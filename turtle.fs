\ turtle.fs -- turtle graphics demo.  Run:  ./forth < turtle.fs

: square ( size -- )  4 0 do dup fd 90 rt loop drop ;
: star   ( size -- )  5 0 do dup fd 144 rt loop drop ;
: flower ( -- )       12 0 do i 6 mod 1+ color 40 square 30 rt loop ;
: spiral ( n -- )     0 do i fd 91 rt loop ;

." Flower:" cr
cs flower show

." Star:" cr
cs yellow color 80 star show

." Spiral:" cr
cs cyan color 120 spiral show
