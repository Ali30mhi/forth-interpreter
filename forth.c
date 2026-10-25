/* =====================================================================
 * forth.c -- a small stack-based Forth interpreter with a terminal REPL.
 *
 * Supports integer arithmetic, comparisons, bitwise logic, stack words,
 * colon definitions (with recursion), nested IF/ELSE/THEN, DO/LOOP/+LOOP
 * with I and J, BEGIN/UNTIL, BEGIN/AGAIN, BEGIN/WHILE/REPEAT, VARIABLE,
 * CONSTANT, ." strings, ( ) / \ comments -- and Logo-style turtle
 * graphics drawn right in the terminal with Unicode braille characters.
 *
 * Source is compiled to a simple instruction array and executed by a
 * tiny virtual machine with its own return stack, so runaway recursion
 * reports an error instead of crashing.
 * ===================================================================== */

#define _POSIX_C_SOURCE 200809L
#include <ctype.h>
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>   /* strcasecmp, strncasecmp */
#include <time.h>
#include <unistd.h>    /* isatty, write */

/* ----------------------------- Limits -------------------------------- */
#define STACK_MAX    1024   /* data stack cells                    */
#define RSTACK_MAX   1024   /* nested calls (recursion depth)      */
#define LSTACK_MAX   64     /* nested DO loops                     */
#define CFSTACK_MAX  64     /* open IF/DO/BEGIN while compiling    */
#define CODE_MAX     16384  /* instructions for colon definitions  */
#define SCRATCH_MAX  4096   /* instructions for one top-level line */
#define MEM_MAX      4096   /* cells for variables                 */
#define DICT_MAX     512    /* dictionary entries                  */
#define STRPOOL_MAX  16384  /* bytes for ." strings                */
#define NAME_LEN     31
#define INPUT_MAX    1024
#define TOKEN_MAX    128

typedef long cell;
typedef unsigned long ucell;
#define TRUE_F ((cell)-1)

/* ----------------------------- Colors -------------------------------- */
#define COLOR_RESET   "\x1b[0m"
#define COLOR_BOLD    "\x1b[1m"
#define COLOR_DIM     "\x1b[2m"
#define COLOR_RED     "\x1b[31m"
#define COLOR_GREEN   "\x1b[32m"
#define COLOR_YELLOW  "\x1b[33m"
#define COLOR_CYAN    "\x1b[36m"

static int use_color = 0;
static int interactive = 0;
static const char *C(const char *code) { return use_color ? code : ""; }

/* ------------------------------ Output ------------------------------- */
static int at_line_start = 1;

static void out_char(int c) { putchar(c); at_line_start = (c == '\n'); }
static void out_str(const char *s) { while (*s) out_char((unsigned char)*s++); }
static void ensure_newline(void) { if (!at_line_start) out_char('\n'); }

static void outf(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
static void outf(const char *fmt, ...) {
    char buf[512];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    out_str(buf);
}

/* ------------------------------ Errors ------------------------------- */
static int err = 0;          /* set by the first error on a line   */
static int had_error = 0;    /* exit status for scripts            */
static int line_no = 0;

static void forth_error(const char *fmt, ...) __attribute__((format(printf, 1, 2)));
static void forth_error(const char *fmt, ...) {
    if (err) return;         /* report only the first error per line */
    err = 1;
    had_error = 1;
    char msg[256];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    ensure_newline();
    fflush(stdout);
    if (interactive)
        fprintf(stderr, "%s  ! %s%s\n", C(COLOR_RED), msg, C(COLOR_RESET));
    else
        fprintf(stderr, "line %d: error: %s\n", line_no, msg);
}

/* ---------------------------- Interrupts ----------------------------- */
static volatile sig_atomic_t running = 0;
static volatile sig_atomic_t interrupted = 0;
static int want_exit = 0;

static void on_sigint(int sig) {
    (void)sig;
    if (running) { interrupted = 1; return; }      /* stop the program */
    static const char bye_msg[] = "\nGoodbye!\n";   /* at the prompt: quit */
    ssize_t r = write(STDOUT_FILENO, bye_msg, sizeof bye_msg - 1);
    (void)r;
    _exit(0);
}

/* ---------------------------- Data stack ----------------------------- */
static cell ds[STACK_MAX];
static int sp = 0;   /* number of items */

static int need(int n) {
    if (sp < n) { forth_error("stack underflow"); return 0; }
    return 1;
}
static void push(cell v) {
    if (sp >= STACK_MAX) { forth_error("stack overflow"); return; }
    ds[sp++] = v;
}
static cell pop(void) { return ds[--sp]; }   /* callers check need() first */

static void print_stack(void) {
    ensure_newline();
    outf("%s  <%d>%s %s[ ", C(COLOR_DIM), sp, C(COLOR_RESET), C(COLOR_CYAN));
    int from = sp > 16 ? sp - 16 : 0;
    if (from > 0) out_str("... ");
    for (int k = from; k < sp; k++) outf("%ld ", ds[k]);
    outf("]%s\n", C(COLOR_RESET));
}

/* ------------------- Memory, loops, return stack --------------------- */
static cell mem[MEM_MAX];
static int mem_here = 0;

typedef struct { cell index, limit; } loop_frame;
static loop_frame ls[LSTACK_MAX];
static int lp = 0;

static int rs[RSTACK_MAX];
static int rp = 0;

/* --------------------------- Instructions ---------------------------- */
enum { OP_LIT, OP_PRIM, OP_CALL, OP_EXIT, OP_BRANCH, OP_BRANCH0,
       OP_DO, OP_LOOP, OP_PLOOP, OP_I, OP_J, OP_DOTQ };

typedef struct { int op; cell arg; } instr;

/* code[0 .. CODE_MAX) holds colon definitions; the area after it is a
 * scratch buffer for the top-level line being interpreted. */
static instr code[CODE_MAX + SCRATCH_MAX];
static int here = 0;
static int shere = CODE_MAX;

static char strpool[STRPOOL_MAX];
static int str_used = 0;
static int str_mark = 0;   /* strings above this belong to the scratch line */

/* ---------------------------- Dictionary ----------------------------- */
enum { K_PRIM, K_COLON, K_VAR, K_CONST };

typedef struct {
    char name[NAME_LEN + 1];
    int kind;
    cell val;   /* prim index, code address, variable address or value */
} dict_entry;

static dict_entry dict[DICT_MAX];
static int ndict = 0;
static int n_builtin = 0;   /* entries below this were created at startup */

static int dict_find(const char *name) {
    for (int k = ndict - 1; k >= 0; k--)   /* newest first: redefinitions win */
        if (strcasecmp(dict[k].name, name) == 0) return k;
    return -1;
}

static int dict_add(const char *name, int kind, cell val) {
    if (ndict >= DICT_MAX) { forth_error("dictionary full"); return -1; }
    size_t n = strlen(name);
    if (n > NAME_LEN) n = NAME_LEN;
    memcpy(dict[ndict].name, name, n);
    dict[ndict].name[n] = '\0';
    dict[ndict].kind = kind;
    dict[ndict].val = val;
    return ndict++;
}

/* ---------------------------- Primitives ----------------------------- */
#define BINOP(fn, expr) \
    static void fn(void) { if (!need(2)) return; cell b = pop(), a = pop(); push(expr); }
#define UNOP(fn, expr) \
    static void fn(void) { if (!need(1)) return; cell a = pop(); push(expr); }

/* unsigned arithmetic wraps instead of triggering undefined behaviour */
BINOP(p_add, (cell)((ucell)a + (ucell)b))
BINOP(p_sub, (cell)((ucell)a - (ucell)b))
BINOP(p_mul, (cell)((ucell)a * (ucell)b))
BINOP(p_eq,  a == b ? TRUE_F : 0)
BINOP(p_ne,  a != b ? TRUE_F : 0)
BINOP(p_lt,  a <  b ? TRUE_F : 0)
BINOP(p_gt,  a >  b ? TRUE_F : 0)
BINOP(p_and, a & b)
BINOP(p_or,  a | b)
BINOP(p_xor, a ^ b)
BINOP(p_min, a < b ? a : b)
BINOP(p_max, a > b ? a : b)

UNOP(p_invert, ~a)
UNOP(p_negate, (cell)(0 - (ucell)a))
UNOP(p_abs,    a < 0 ? (cell)(0 - (ucell)a) : a)
UNOP(p_zeq,    a == 0 ? TRUE_F : 0)
UNOP(p_zlt,    a <  0 ? TRUE_F : 0)
UNOP(p_inc,    (cell)((ucell)a + 1))
UNOP(p_dec,    (cell)((ucell)a - 1))

/* floored division: the remainder always has the sign of the divisor */
static int floordiv(cell a, cell b, cell *q, cell *r) {
    if (b == 0) { forth_error("division by zero"); return 0; }
    if (a == LONG_MIN && b == -1) { *q = LONG_MIN; *r = 0; return 1; }
    cell qq = a / b, rr = a % b;
    if (rr != 0 && ((rr < 0) != (b < 0))) { qq--; rr += b; }
    *q = qq;
    *r = rr;
    return 1;
}
static void p_div(void)    { if (!need(2)) return; cell b = pop(), a = pop(), q, r; if (floordiv(a, b, &q, &r)) push(q); }
static void p_mod(void)    { if (!need(2)) return; cell b = pop(), a = pop(), q, r; if (floordiv(a, b, &q, &r)) push(r); }
static void p_divmod(void) { if (!need(2)) return; cell b = pop(), a = pop(), q, r; if (floordiv(a, b, &q, &r)) { push(r); push(q); } }

static void p_dup(void)   { if (!need(1)) return; push(ds[sp - 1]); }
static void p_drop(void)  { if (!need(1)) return; sp--; }
static void p_swap(void)  { if (!need(2)) return; cell t = ds[sp - 1]; ds[sp - 1] = ds[sp - 2]; ds[sp - 2] = t; }
static void p_over(void)  { if (!need(2)) return; push(ds[sp - 2]); }
static void p_rot(void)   { if (!need(3)) return; cell a = ds[sp - 3]; ds[sp - 3] = ds[sp - 2]; ds[sp - 2] = ds[sp - 1]; ds[sp - 1] = a; }
static void p_nip(void)   { if (!need(2)) return; ds[sp - 2] = ds[sp - 1]; sp--; }
static void p_tuck(void)  { if (!need(2)) return; cell b = ds[sp - 1], a = ds[sp - 2]; ds[sp - 2] = b; ds[sp - 1] = a; push(b); }
static void p_2dup(void)  { if (!need(2)) return; cell a = ds[sp - 2], b = ds[sp - 1]; push(a); push(b); }
static void p_2drop(void) { if (!need(2)) return; sp -= 2; }
static void p_qdup(void)  { if (!need(1)) return; if (ds[sp - 1]) push(ds[sp - 1]); }
static void p_depth(void) { push(sp); }

static int valid_addr(cell a) {
    if (a < 0 || a >= mem_here) { forth_error("invalid address %ld (not a variable)", a); return 0; }
    return 1;
}
static void p_store(void)     { if (!need(2)) return; cell addr = pop(), v = pop(); if (valid_addr(addr)) mem[addr] = v; }
static void p_fetch(void)     { if (!need(1)) return; cell addr = pop(); if (valid_addr(addr)) push(mem[addr]); }
static void p_plusstore(void) { if (!need(2)) return; cell addr = pop(), v = pop(); if (valid_addr(addr)) mem[addr] = (cell)((ucell)mem[addr] + (ucell)v); }
static void p_question(void)  { if (!need(1)) return; cell addr = pop(); if (valid_addr(addr)) outf("%ld ", mem[addr]); }

static void p_dot(void)    { if (!need(1)) return; outf("%ld ", pop()); }
static void p_dots(void)   { print_stack(); }
static void p_emit(void)   { if (!need(1)) return; out_char((unsigned char)pop()); }
static void p_cr(void)     { out_char('\n'); }
static void p_space(void)  { out_char(' '); }
static void p_spaces(void) { if (!need(1)) return; cell n = pop(); for (cell k = 0; k < n && k < 1000; k++) out_char(' '); }
static void p_empty(void)  { push(sp == 0 ? TRUE_F : 0); }
static void p_reset(void)  { sp = 0; }
static void p_bye(void)    { want_exit = 1; }
static void p_random(void) {
    if (!need(1)) return;
    cell n = pop();
    if (n <= 0) { forth_error("random needs a positive number"); return; }
    push((cell)(rand() % n));
}

/* --------------------------- Turtle graphics --------------------------
 * The canvas is a grid of braille dots: every terminal cell shows a 2x4
 * block of dots, so pictures look sharp with no graphics library. The
 * origin is the centre, y grows upward, heading 0 points up and turning
 * right is clockwise -- the same conventions as Logo. */
#define CANVAS_W  240
#define CANVAS_H  240
#define CELL_COLS (CANVAS_W / 2)
#define CELL_ROWS (CANVAS_H / 4)
#define TURTLE_LIMIT 100000

static unsigned char canvas[CANVAS_H][CANVAS_W];
static unsigned char cell_color[CELL_ROWS][CELL_COLS];
static int ink = 0, ink_x0, ink_y0, ink_x1, ink_y1;   /* bounding box */
static int canvas_dirty = 0;
static double tx = 0.0, ty = 0.0;
static cell theading = 0;
static int pen_down = 1;
static int pen_color = 7;

static int iround(double v) { return v >= 0 ? (int)(v + 0.5) : -(int)(-v + 0.5); }

/* sine of a whole number of degrees, without needing libm */
static double dsin(cell deg) {
    long d = (long)(deg % 360);
    if (d < 0) d += 360;
    if (d > 180) d -= 360;                       /* now in [-180, 180] */
    double x = (double)d * 3.14159265358979323846 / 180.0;
    double term = x, sum = x, x2 = x * x;
    for (int n = 1; n < 12; n++) {
        term *= -x2 / (double)((2 * n) * (2 * n + 1));
        sum += term;
    }
    return sum;
}
static double dcos(cell deg) { return dsin(deg % 360 + 90); }

static void plot(int x, int y) {
    if (x < 0 || y < 0 || x >= CANVAS_W || y >= CANVAS_H) return;   /* clip */
    canvas[y][x] = 1;
    cell_color[y / 4][x / 2] = (unsigned char)pen_color;
    if (!ink) { ink = 1; ink_x0 = ink_x1 = x; ink_y0 = ink_y1 = y; }
    else {
        if (x < ink_x0) ink_x0 = x;
        if (x > ink_x1) ink_x1 = x;
        if (y < ink_y0) ink_y0 = y;
        if (y > ink_y1) ink_y1 = y;
    }
    canvas_dirty = 1;
}

static void draw_line(int x0, int y0, int x1, int y1) {   /* Bresenham */
    int dx = abs(x1 - x0), sx = x0 < x1 ? 1 : -1;
    int dy = -abs(y1 - y0), sy = y0 < y1 ? 1 : -1;
    int e = dx + dy;
    for (;;) {
        plot(x0, y0);
        if (x0 == x1 && y0 == y1) break;
        int e2 = 2 * e;
        if (e2 >= dy) { e += dy; x0 += sx; }
        if (e2 <= dx) { e += dx; y0 += sy; }
    }
}

static void move_to(double nx, double ny) {
    if (nx > TURTLE_LIMIT || nx < -TURTLE_LIMIT || ny > TURTLE_LIMIT || ny < -TURTLE_LIMIT) {
        forth_error("the turtle went too far off the canvas");
        return;
    }
    if (pen_down)
        draw_line(CANVAS_W / 2 + iround(tx), CANVAS_H / 2 - iround(ty),
                  CANVAS_W / 2 + iround(nx), CANVAS_H / 2 - iround(ny));
    tx = nx;
    ty = ny;
}

static void turn(cell deg) { theading = ((theading + deg % 360) % 360 + 360) % 360; }

static void p_forward(void) { if (!need(1)) return; cell n = pop(); move_to(tx + (double)n * dsin(theading), ty + (double)n * dcos(theading)); }
static void p_back(void)    { if (!need(1)) return; cell n = pop(); move_to(tx - (double)n * dsin(theading), ty - (double)n * dcos(theading)); }
static void p_right(void)   { if (!need(1)) return; turn(pop()); }
static void p_left(void)    { if (!need(1)) return; turn(-(pop() % 360)); }
static void p_penup(void)   { pen_down = 0; }
static void p_pendown(void) { pen_down = 1; }
static void p_home(void)    { tx = ty = 0.0; theading = 0; }
static void p_seth(void)    { if (!need(1)) return; theading = 0; turn(pop()); }
static void p_setxy(void)   { if (!need(2)) return; cell y = pop(), x = pop(); move_to((double)x, (double)y); }
static void p_xy(void)      { push(iround(tx)); push(iround(ty)); }
static void p_heading(void) { push(theading); }

static void p_color(void) {
    if (!need(1)) return;
    cell n = pop();
    if (n < 0 || n > 7) { forth_error("color must be 0-7 (try: red color)"); return; }
    pen_color = (int)n;
}

static void p_cs(void) {
    memset(canvas, 0, sizeof canvas);
    memset(cell_color, 0, sizeof cell_color);
    ink = 0;
    canvas_dirty = 0;
    tx = ty = 0.0;
    theading = 0;
    pen_down = 1;
}

static const unsigned char BRAILLE_BIT[4][2] = {
    { 0x01, 0x08 }, { 0x02, 0x10 }, { 0x04, 0x20 }, { 0x40, 0x80 }
};

static void p_show(void) {
    ensure_newline();
    canvas_dirty = 0;
    if (!ink) {
        outf("%s(the canvas is empty -- try: 60 fd 90 rt 60 fd)%s\n", C(COLOR_DIM), C(COLOR_RESET));
        return;
    }
    int c0 = ink_x0 / 2, c1 = ink_x1 / 2, r0 = ink_y0 / 4, r1 = ink_y1 / 4;
    for (int r = r0; r <= r1; r++) {
        char line[CELL_COLS * 16 + 16];
        size_t n = 0;
        int cur = -1;
        for (int c = c0; c <= c1; c++) {
            int bits = 0;
            for (int dy = 0; dy < 4; dy++)
                for (int dx = 0; dx < 2; dx++)
                    if (canvas[r * 4 + dy][c * 2 + dx]) bits |= BRAILLE_BIT[dy][dx];
            if (!bits) { line[n++] = ' '; continue; }
            if (use_color && cell_color[r][c] != cur) {
                cur = cell_color[r][c];
                n += (size_t)snprintf(line + n, sizeof line - n, "\x1b[%dm", 90 + cur);
            }
            unsigned cp = 0x2800u + (unsigned)bits;          /* UTF-8 encode */
            line[n++] = (char)(0xE0 | (cp >> 12));
            line[n++] = (char)(0x80 | ((cp >> 6) & 0x3F));
            line[n++] = (char)(0x80 | (cp & 0x3F));
        }
        if (cur >= 0) n += (size_t)snprintf(line + n, sizeof line - n, "%s", COLOR_RESET);
        line[n] = '\0';
        out_str(line);
        out_char('\n');
    }
}

/* ---------------------------- Word table ----------------------------- */
static void p_words(void);

typedef struct { const char *name; void (*fn)(void); const char *doc; } prim;

static const prim PRIMS[] = {
    { "+",       p_add,       "( a b -- a+b )      add" },
    { "-",       p_sub,       "( a b -- a-b )      subtract" },
    { "*",       p_mul,       "( a b -- a*b )      multiply" },
    { "/",       p_div,       "( a b -- q )        floored division" },
    { "mod",     p_mod,       "( a b -- r )        floored remainder" },
    { "/mod",    p_divmod,    "( a b -- r q )      remainder and quotient" },
    { "negate",  p_negate,    "( a -- -a )         change sign" },
    { "abs",     p_abs,       "( a -- |a| )        absolute value" },
    { "min",     p_min,       "( a b -- min )      smaller of two" },
    { "max",     p_max,       "( a b -- max )      larger of two" },
    { "1+",      p_inc,       "( a -- a+1 )        add one" },
    { "1-",      p_dec,       "( a -- a-1 )        subtract one" },
    { "random",  p_random,    "( n -- r )          random number 0..n-1" },
    { "=",       p_eq,        "( a b -- flag )     equal?" },
    { "<>",      p_ne,        "( a b -- flag )     not equal?" },
    { "<",       p_lt,        "( a b -- flag )     less than?" },
    { ">",       p_gt,        "( a b -- flag )     greater than?" },
    { "0=",      p_zeq,       "( a -- flag )       zero? (logical not)" },
    { "0<",      p_zlt,       "( a -- flag )       negative?" },
    { "and",     p_and,       "( a b -- a&b )      bitwise and" },
    { "or",      p_or,        "( a b -- a|b )      bitwise or" },
    { "xor",     p_xor,       "( a b -- a^b )      bitwise xor" },
    { "invert",  p_invert,    "( a -- ~a )         bitwise not" },
    { "dup",     p_dup,       "( a -- a a )        copy the top item" },
    { "drop",    p_drop,      "( a -- )            discard the top item" },
    { "swap",    p_swap,      "( a b -- b a )      swap the top two" },
    { "over",    p_over,      "( a b -- a b a )    copy the second item" },
    { "rot",     p_rot,       "( a b c -- b c a )  rotate the top three" },
    { "nip",     p_nip,       "( a b -- b )        drop the second item" },
    { "tuck",    p_tuck,      "( a b -- b a b )    copy top below second" },
    { "2dup",    p_2dup,      "( a b -- a b a b )  copy the top two" },
    { "2drop",   p_2drop,     "( a b -- )          drop the top two" },
    { "?dup",    p_qdup,      "( a -- a a | 0 )    dup if non-zero" },
    { "depth",   p_depth,     "( -- n )            items on the stack" },
    { "!",       p_store,     "( v addr -- )       store into variable" },
    { "@",       p_fetch,     "( addr -- v )       fetch from variable" },
    { "+!",      p_plusstore, "( n addr -- )       add to variable" },
    { "?",       p_question,  "( addr -- )         print variable" },
    { ".",       p_dot,       "( a -- )            print number" },
    { ".s",      p_dots,      "( -- )              show the stack" },
    { "emit",    p_emit,      "( c -- )            print character" },
    { "cr",      p_cr,        "( -- )              newline" },
    { "space",   p_space,     "( -- )              print a space" },
    { "spaces",  p_spaces,    "( n -- )            print n spaces" },
    { "forward", p_forward,   "( n -- )            turtle: move forward (draws if pen is down)" },
    { "fd",      p_forward,   "( n -- )            turtle: same as forward" },
    { "back",    p_back,      "( n -- )            turtle: move backward" },
    { "bk",      p_back,      "( n -- )            turtle: same as back" },
    { "right",   p_right,     "( deg -- )          turtle: turn clockwise" },
    { "rt",      p_right,     "( deg -- )          turtle: same as right" },
    { "left",    p_left,      "( deg -- )          turtle: turn counter-clockwise" },
    { "lt",      p_left,      "( deg -- )          turtle: same as left" },
    { "penup",   p_penup,     "( -- )              turtle: stop drawing while moving" },
    { "pu",      p_penup,     "( -- )              turtle: same as penup" },
    { "pendown", p_pendown,   "( -- )              turtle: draw while moving" },
    { "pd",      p_pendown,   "( -- )              turtle: same as pendown" },
    { "home",    p_home,      "( -- )              turtle: jump to centre, face up" },
    { "setxy",   p_setxy,     "( x y -- )          turtle: move to a point" },
    { "seth",    p_seth,      "( deg -- )          turtle: set heading (0 = up)" },
    { "xy",      p_xy,        "( -- x y )          turtle: current position" },
    { "heading", p_heading,   "( -- deg )          turtle: current heading" },
    { "color",   p_color,     "( n -- )            pen colour 0-7, e.g. red color" },
    { "cs",      p_cs,        "( -- )              clear the canvas and reset the turtle" },
    { "show",    p_show,      "( -- )              draw the canvas in the terminal" },
    { "empty?",  p_empty,     "( -- flag )         is the stack empty?" },
    { "reset",   p_reset,     "( ... -- )          clear the stack" },
    { "words",   p_words,     "( -- )              list all words" },
    { "bye",     p_bye,       "( -- )              leave the interpreter" },
};
#define NUM_PRIMS (int)(sizeof(PRIMS) / sizeof(PRIMS[0]))

static const char *COLOR_NAMES[8] = {
    "black", "red", "green", "yellow", "blue", "magenta", "cyan", "white"
};

static int words_col = 0;
static void list_name(const char *name) {
    int len = (int)strlen(name) + 1;
    if (words_col + len > 74) { out_str("\n  "); words_col = 2; }
    outf("%s ", name);
    words_col += len;
}

static void p_words(void) {
    ensure_newline();
    if (ndict > n_builtin) {
        outf("%sYour words:%s\n  ", C(COLOR_BOLD), C(COLOR_RESET));
        words_col = 2;
        for (int k = ndict - 1; k >= n_builtin; k--) list_name(dict[k].name);
        out_char('\n');
    }
    outf("%sBuilt-in words:%s\n  ", C(COLOR_BOLD), C(COLOR_RESET));
    words_col = 2;
    for (int k = 0; k < NUM_PRIMS; k++) list_name(PRIMS[k].name);
    out_char('\n');
    outf("%sCompiler words:%s\n"
         "  : ; if else then do loop +loop i j begin until again while repeat\n"
         "  .\" ( \\ variable constant recurse exit\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("%sColors:%s\n  ", C(COLOR_BOLD), C(COLOR_RESET));
    for (int k = 0; k < 8; k++) outf("%s ", COLOR_NAMES[k]);
    out_char('\n');
    outf("%sType 'help <word>' to see what a built-in word does.%s\n", C(COLOR_DIM), C(COLOR_RESET));
}

/* ------------------------- Virtual machine --------------------------- */
static void run(int ip) {
    int rbase = rp;
    while (!err && !want_exit) {
        if (interrupted) { interrupted = 0; forth_error("interrupted"); break; }
        instr in = code[ip++];
        switch (in.op) {
        case OP_LIT:
            push(in.arg);
            break;
        case OP_PRIM:
            PRIMS[in.arg].fn();
            break;
        case OP_CALL:
            if (rp >= RSTACK_MAX) { forth_error("return stack overflow (recursion too deep?)"); break; }
            rs[rp++] = ip;
            ip = (int)in.arg;
            break;
        case OP_EXIT:
            if (rp == rbase) return;
            ip = rs[--rp];
            break;
        case OP_BRANCH:
            ip = (int)in.arg;
            break;
        case OP_BRANCH0:
            if (!need(1)) break;
            if (pop() == 0) ip = (int)in.arg;
            break;
        case OP_DO: {
            if (!need(2)) break;
            if (lp >= LSTACK_MAX) { forth_error("loops nested too deeply"); break; }
            cell start = pop(), limit = pop();
            ls[lp].index = start;
            ls[lp].limit = limit;
            lp++;
            break;
        }
        case OP_LOOP:
        case OP_PLOOP: {
            if (lp == 0) { forth_error("'loop' outside of a do-loop"); break; }
            cell step = 1;
            if (in.op == OP_PLOOP) { if (!need(1)) break; step = pop(); }
            loop_frame *f = &ls[lp - 1];
            f->index = (cell)((ucell)f->index + (ucell)step);
            int cont = step >= 0 ? f->index < f->limit : f->index >= f->limit;
            if (cont) ip = (int)in.arg;
            else lp--;
            break;
        }
        case OP_I:
            if (lp < 1) forth_error("'i' used outside of a do-loop");
            else push(ls[lp - 1].index);
            break;
        case OP_J:
            if (lp < 2) forth_error("'j' needs two nested do-loops");
            else push(ls[lp - 2].index);
            break;
        case OP_DOTQ:
            out_str(&strpool[in.arg]);
            break;
        default:
            forth_error("internal error: bad opcode %d", in.op);
            break;
        }
    }
}

/* ---------------------------- Compiler ------------------------------- */
static int compiling = 0;        /* inside : ... ; */
static int def_entry = -1;       /* dictionary slot of the word being defined */
static int def_start = 0;        /* its first instruction */
static int *cpos = &shere;       /* where compiled code goes right now */
static int climit = CODE_MAX + SCRATCH_MAX;

static void set_target(void) {
    if (compiling) { cpos = &here;  climit = CODE_MAX; }
    else           { cpos = &shere; climit = CODE_MAX + SCRATCH_MAX; }
}

static int compile_op(int op, cell arg) {
    if (*cpos >= climit) {
        forth_error(compiling ? "out of code space" : "line too long to compile");
        return -1;
    }
    code[*cpos].op = op;
    code[*cpos].arg = arg;
    return (*cpos)++;
}

enum { CF_IF, CF_ELSE, CF_DO, CF_BEGIN, CF_WHILE };
typedef struct { int type; int addr; } cf_entry;
static cf_entry cf[CFSTACK_MAX];
static int cfp = 0;

static void cf_push(int type, int addr) {
    if (cfp >= CFSTACK_MAX) { forth_error("control structures nested too deeply"); return; }
    cf[cfp].type = type;
    cf[cfp].addr = addr;
    cfp++;
}

static cf_entry *cf_expect(int t1, int t2, const char *word, const char *opener) {
    if (cfp > 0 && (cf[cfp - 1].type == t1 || cf[cfp - 1].type == t2)) return &cf[cfp - 1];
    forth_error("'%s' without matching '%s'", word, opener);
    return NULL;
}

/* ----------------------------- Parsing ------------------------------- */
static const char *src = "";

static int next_token(char *buf, size_t n) {
    while (*src && isspace((unsigned char)*src)) src++;
    if (!*src) return 0;
    size_t len = 0;
    while (*src && !isspace((unsigned char)*src)) {
        if (len + 1 < n) buf[len] = *src;
        len++;
        src++;
    }
    if (len >= n) {
        buf[n - 1] = '\0';
        forth_error("token too long: '%.20s...'", buf);
        return 0;
    }
    buf[len] = '\0';
    return 1;
}

/* Reads text up to delim, skipping the single space after the word. */
static int parse_until(char delim, char *buf, size_t n) {
    if (*src && isspace((unsigned char)*src)) src++;
    const char *end = strchr(src, delim);
    if (!end) { forth_error("missing closing '%c'", delim); return 0; }
    size_t len = (size_t)(end - src);
    if (len >= n) { forth_error("string too long"); return 0; }
    memcpy(buf, src, len);
    buf[len] = '\0';
    src = end + 1;
    return 1;
}

/* 1 = number, 0 = not a number, -1 = digits but out of range */
static int parse_number(const char *tok, cell *out) {
    const char *p = tok + (tok[0] == '-');
    if (!*p) return 0;                 /* lone "-" is the subtract word */
    for (const char *q = p; *q; q++)
        if (!isdigit((unsigned char)*q)) return 0;
    errno = 0;
    long v = strtol(tok, NULL, 10);
    if (errno == ERANGE) return -1;
    *out = v;
    return 1;
}

static int store_string(const char *s) {
    size_t n = strlen(s) + 1;
    if ((size_t)str_used + n > STRPOOL_MAX) { forth_error("out of string space"); return -1; }
    memcpy(strpool + str_used, s, n);
    int off = str_used;
    str_used += (int)n;
    return off;
}

static const char *RESERVED[] = {
    ":", ";", "if", "else", "then", "do", "loop", "+loop", "i", "j",
    "begin", "until", "again", "while", "repeat", ".\"", "(", "\\",
    "variable", "constant", "recurse", "exit", NULL
};

static int is(const char *a, const char *b) { return strcasecmp(a, b) == 0; }

static int is_reserved(const char *s) {
    for (int k = 0; RESERVED[k]; k++)
        if (is(s, RESERVED[k])) return 1;
    return 0;
}

static int read_name(char *name, const char *what) {
    char tok[TOKEN_MAX];
    cell dummy;
    if (!next_token(tok, sizeof tok)) {
        if (!err) forth_error("%s needs a name", what);
        return 0;
    }
    if (strlen(tok) > NAME_LEN) { forth_error("name too long (max %d characters)", NAME_LEN); return 0; }
    if (parse_number(tok, &dummy) != 0) { forth_error("'%s' is a number, not a valid name", tok); return 0; }
    if (is_reserved(tok)) { forth_error("'%s' is a reserved word", tok); return 0; }
    strcpy(name, tok);
    return 1;
}

/* Runs whatever has been compiled for the current top-level line. */
static void flush_toplevel(void) {
    if (compiling || err) return;
    if (cfp > 0) { forth_error("finish the open if/do/begin first"); return; }
    if (shere > CODE_MAX && compile_op(OP_EXIT, 0) >= 0) {
        running = 1;
        run(CODE_MAX);
        running = 0;
        rp = 0;
        lp = 0;
    }
    shere = CODE_MAX;
    str_used = str_mark;
}

/* After an error: drop a half-built definition and the pending line. */
static void recover(void) {
    if (compiling) {
        ndict = def_entry;
        here = def_start;
        compiling = 0;
        def_entry = -1;
    }
    cfp = 0;
    shere = CODE_MAX;
    str_used = str_mark;
    rp = 0;
    lp = 0;
    set_target();
}

static void compile_token(const char *tok) {
    char buf[INPUT_MAX];
    char name[NAME_LEN + 1];
    cf_entry *e;
    int a;

    /* comments and strings */
    if (is(tok, "\\")) { src += strlen(src); return; }
    if (is(tok, "(")) {
        const char *end = strchr(src, ')');
        src = end ? end + 1 : src + strlen(src);
        return;
    }
    if (is(tok, ".\"")) {
        if (!parse_until('"', buf, sizeof buf)) return;
        int off = store_string(buf);
        if (off >= 0) compile_op(OP_DOTQ, off);
        return;
    }

    /* definitions */
    if (is(tok, ":")) {
        if (compiling) { forth_error("nested ':' (missing ';' before it?)"); return; }
        flush_toplevel();
        if (err || !read_name(name, "':'")) return;
        def_start = here;
        def_entry = dict_add(name, K_COLON, here);
        if (def_entry < 0) return;
        compiling = 1;
        set_target();
        return;
    }
    if (is(tok, ";")) {
        if (!compiling) { forth_error("';' without matching ':'"); return; }
        if (cfp > 0) { forth_error("unfinished if/do/begin inside definition"); return; }
        if (compile_op(OP_EXIT, 0) < 0) return;
        compiling = 0;
        def_entry = -1;
        str_mark = str_used;   /* keep this definition's strings */
        set_target();
        return;
    }
    if (is(tok, "variable")) {
        if (compiling) { forth_error("'variable' can't be used inside a definition"); return; }
        if (!read_name(name, "'variable'")) return;
        if (mem_here >= MEM_MAX) { forth_error("out of variable space"); return; }
        if (dict_add(name, K_VAR, mem_here) >= 0) mem[mem_here++] = 0;
        return;
    }
    if (is(tok, "constant")) {
        if (compiling) { forth_error("'constant' can't be used inside a definition"); return; }
        flush_toplevel();   /* the value must be on the stack now */
        if (err || !read_name(name, "'constant'")) return;
        if (!need(1)) return;
        dict_add(name, K_CONST, pop());
        return;
    }
    if (is(tok, "recurse")) {
        if (!compiling) { forth_error("'recurse' only works inside a definition"); return; }
        compile_op(OP_CALL, def_start);
        return;
    }
    if (is(tok, "exit")) { compile_op(OP_EXIT, 0); return; }

    /* control flow */
    if (is(tok, "if")) {
        a = compile_op(OP_BRANCH0, 0);
        if (a >= 0) cf_push(CF_IF, a);
        return;
    }
    if (is(tok, "else")) {
        if (!(e = cf_expect(CF_IF, CF_IF, "else", "if"))) return;
        a = compile_op(OP_BRANCH, 0);
        if (a < 0) return;
        code[e->addr].arg = *cpos;
        e->type = CF_ELSE;
        e->addr = a;
        return;
    }
    if (is(tok, "then")) {
        if (!(e = cf_expect(CF_IF, CF_ELSE, "then", "if"))) return;
        code[e->addr].arg = *cpos;
        cfp--;
        return;
    }
    if (is(tok, "do")) {
        if (compile_op(OP_DO, 0) >= 0) cf_push(CF_DO, *cpos);
        return;
    }
    if (is(tok, "loop") || is(tok, "+loop")) {
        if (!(e = cf_expect(CF_DO, CF_DO, tok, "do"))) return;
        if (compile_op(is(tok, "loop") ? OP_LOOP : OP_PLOOP, e->addr) >= 0) cfp--;
        return;
    }
    if (is(tok, "i")) { compile_op(OP_I, 0); return; }
    if (is(tok, "j")) { compile_op(OP_J, 0); return; }
    if (is(tok, "begin")) { cf_push(CF_BEGIN, *cpos); return; }
    if (is(tok, "until") || is(tok, "again")) {
        if (!(e = cf_expect(CF_BEGIN, CF_BEGIN, tok, "begin"))) return;
        if (compile_op(is(tok, "until") ? OP_BRANCH0 : OP_BRANCH, e->addr) >= 0) cfp--;
        return;
    }
    if (is(tok, "while")) {
        if (!cf_expect(CF_BEGIN, CF_BEGIN, "while", "begin")) return;
        a = compile_op(OP_BRANCH0, 0);
        if (a >= 0) cf_push(CF_WHILE, a);
        return;
    }
    if (is(tok, "repeat")) {
        if (!(e = cf_expect(CF_WHILE, CF_WHILE, "repeat", "while"))) return;
        if (cfp < 2 || cf[cfp - 2].type != CF_BEGIN) { forth_error("'repeat' without matching 'begin'"); return; }
        if (compile_op(OP_BRANCH, cf[cfp - 2].addr) < 0) return;
        code[e->addr].arg = *cpos;
        cfp -= 2;
        return;
    }

    /* numbers and dictionary words */
    cell v;
    int r = parse_number(tok, &v);
    if (r < 0) { forth_error("number out of range: %s", tok); return; }
    if (r > 0) { compile_op(OP_LIT, v); return; }

    int d = dict_find(tok);
    if (d < 0) { forth_error("unknown word '%s' (try 'words' or 'help')", tok); return; }
    switch (dict[d].kind) {
    case K_PRIM:  compile_op(OP_PRIM, dict[d].val); break;
    case K_COLON: compile_op(OP_CALL, dict[d].val); break;
    default:      compile_op(OP_LIT, dict[d].val);  break;  /* variable address or constant */
    }
}

static void interpret_line(const char *line) {
    char tok[TOKEN_MAX];
    src = line;
    while (!err && !want_exit && next_token(tok, sizeof tok))
        compile_token(tok);
}

/* ------------------------------ REPL UI ------------------------------ */
static void print_banner(void) {
    printf("%s%s", C(COLOR_BOLD), C(COLOR_CYAN));
    printf("+----------------------------------------+\n");
    printf("|               F O R T H                |\n");
    printf("+----------------------------------------+\n");
    printf("%s", C(COLOR_RESET));
    printf("A tiny stack-based Forth REPL with turtle graphics.\n");
    printf("Type %shelp%s for a tour, %swords%s for the vocabulary, %sexit%s to quit.\n",
           C(COLOR_YELLOW), C(COLOR_RESET), C(COLOR_YELLOW), C(COLOR_RESET),
           C(COLOR_YELLOW), C(COLOR_RESET));
    printf("Try: %scs yellow color 5 0 do 80 fd 144 rt loop%s\n\n",
           C(COLOR_GREEN), C(COLOR_RESET));
}

static void print_help(void) {
    ensure_newline();
    outf("\n%sHow this works:%s\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("  Numbers are pushed onto the stack; words take their inputs from it.\n");
    outf("  3 4 + .                      -> 7\n\n");
    outf("%sDefining words:%s\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("  : square dup * ;   5 square .        -> 25\n");
    outf("  : fact dup 1 > if dup 1 - fact * else drop 1 then ;\n");
    outf("  variable x   10 x !   5 x +!   x @ . -> 15\n");
    outf("  42 constant answer\n\n");
    outf("%sControl flow%s (inside or outside definitions, nesting allowed):\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("  flag if ... then        flag if ... else ... then\n");
    outf("  limit start do ... i ... loop      (also +loop, j)\n");
    outf("  begin ... flag until    begin ... flag while ... repeat    begin ... again\n\n");
    outf("%sTurtle graphics%s (drawn right in the terminal):\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("  cs 4 0 do 60 fd 90 rt loop             a square\n");
    outf("  cs red color 5 0 do 80 fd 144 rt loop  a red star\n");
    outf("  fd bk rt lt pu pd home setxy seth color cs show xy heading\n");
    outf("  In the REPL the canvas is shown automatically; in scripts use 'show'.\n\n");
    outf("%sOutput:%s   .  .s  ?  emit  cr  space  spaces  .\" text\"\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("%sComments:%s \\ rest of line     ( inline comment )\n\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("%sREPL:%s help, help <word>, words, clear, exit/quit/bye or Ctrl-D.\n", C(COLOR_BOLD), C(COLOR_RESET));
    outf("      Ctrl-C stops a running program (e.g. an endless loop).\n\n");
}

static void print_word_help(const char *name) {
    while (*name == ' ' || *name == '\t') name++;
    ensure_newline();
    for (int k = 0; k < NUM_PRIMS; k++) {
        if (is(name, PRIMS[k].name)) {
            outf("  %s%s%s  %s\n", C(COLOR_YELLOW), PRIMS[k].name, C(COLOR_RESET), PRIMS[k].doc);
            return;
        }
    }
    for (int k = 0; k < 8; k++) {
        if (is(name, COLOR_NAMES[k])) {
            outf("  %s  ( -- %d )  colour constant, use with: %s color\n", COLOR_NAMES[k], k, COLOR_NAMES[k]);
            return;
        }
    }
    if (is_reserved(name)) { outf("  '%s' is a compiler word -- type 'help' for examples\n", name); return; }
    if (dict_find(name) >= 0) { outf("  '%s' is a word you defined\n", name); return; }
    outf("  unknown word '%s'\n", name);
}

int main(void) {
    interactive = isatty(STDIN_FILENO);
    use_color = interactive && isatty(STDOUT_FILENO);
    srand((unsigned)time(NULL));

    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_sigint;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;
    sigaction(SIGINT, &sa, NULL);

    for (int k = 0; k < NUM_PRIMS; k++) dict_add(PRIMS[k].name, K_PRIM, k);
    for (int k = 0; k < 8; k++) dict_add(COLOR_NAMES[k], K_CONST, k);
    n_builtin = ndict;
    set_target();
    if (interactive) print_banner();

    char line[INPUT_MAX];
    for (;;) {
        if (interactive) {
            ensure_newline();
            int cont = compiling || cfp > 0;
            printf("%s%s%s%s", C(COLOR_BOLD), C(cont ? COLOR_DIM : COLOR_GREEN),
                   cont ? "   ...> " : "forth> ", C(COLOR_RESET));
            fflush(stdout);
            at_line_start = 0;
        }
        if (!fgets(line, sizeof line, stdin)) break;
        at_line_start = 1;
        line_no++;
        err = 0;

        size_t len = strlen(line);
        if (len > 0 && line[len - 1] != '\n' && !feof(stdin)) {
            int c;
            while ((c = getchar()) != '\n' && c != EOF) { }
            forth_error("line too long (max %d characters)", INPUT_MAX - 2);
            recover();
            continue;
        }
        while (len > 0 && isspace((unsigned char)line[len - 1])) line[--len] = '\0';
        char *t = line;
        while (*t == ' ' || *t == '\t') t++;

        if (!compiling && cfp == 0) {
            if (is(t, "exit") || is(t, "quit")) break;
            if (is(t, "help")) { print_help(); continue; }
            if (strncasecmp(t, "help ", 5) == 0) { print_word_help(t + 5); continue; }
            if (is(t, "clear") || is(t, "cls")) {
                if (interactive) { printf("\x1b[2J\x1b[H"); at_line_start = 1; }
                continue;
            }
        }

        interpret_line(t);
        if (!err && !compiling && cfp == 0) flush_toplevel();
        if (err) recover();
        if (want_exit) break;
        if (interactive && canvas_dirty && !compiling && cfp == 0) p_show();
        if (interactive && *t && !compiling && cfp == 0) print_stack();
    }

    if (!want_exit && (compiling || cfp > 0)) {
        err = 0;
        forth_error("unexpected end of input inside an unfinished definition");
        recover();
    }
    if (canvas_dirty) p_show();
    if (interactive) {
        ensure_newline();
        printf("%sGoodbye!%s\n", C(COLOR_YELLOW), C(COLOR_RESET));
    }
    fflush(stdout);
    return (!interactive && had_error) ? 1 : 0;
}