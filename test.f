
lessnat = lambda f:Nat->Nat->Bool.
lambda x:Nat. lambda y:Nat.
if iszero y then false else
(if iszero x then true else
f (pred x) (pred y));
lessnat = fix lessnat;


ff = lambda f:Range->Nat->Range. lambda x:Range. lambda y:Nat.
if iszero y then x else f (mul x 0.1) (pred y);
ff = fix ff;

erfen = lambda f:Range->Range->Range->Nat->Range.
lambda x:Range. lambda l:Range. lambda r:Range. lambda times:Nat. 
(if iszero times then r else
let mid = setprecision (mul (add l r) 0.5) 10 in
let nv = setprecision (mul mid mid) 20  in
if less (up x 20) (down nv 20) then
( f x l mid (pred times) )
else 
if less (up nv 20) (down x 20) then
( f x mid r (pred times) )
else setprecision mid 6);
erfen = fix erfen;

fsqrt = lambda x:Range. setprecision (erfen x 0.0 x 25) 6;

round (setprecision (fsqrt 2.0) 6) 6;
