
erfen = lambda f:Range->Range->Range->Nat->Range.
lambda x:Range. lambda l:Range. lambda r:Range. lambda times:Nat. 
(if iszero times then r else
let mid = setprecision (mul (add l r) 0.5) 10 in
let nv = setprecision (mul mid mid) 20  in
if less (up x) (down nv) then
( f x l mid (pred times) )
else 
if less (up nv) (down x) then
( f x mid r (pred times) )
else setprecision mid 6);
erfen = fix erfen;

fsqrt = lambda x:Range. setprecision (erfen x 0.0 x 25) 6;

up (setprecision (fsqrt 2.0) 6);



sum = lambda f:Range->Range->Nat->Range.
lambda s:Range. lambda now:Range. lambda left:Nat.
if iszero left then s else
f (add s (inv now)) (add now 1.0) (pred left);
sum = fix sum;

ans = sum 0.0 1.0 100;

ans = setprecision ans 100;
down ans;



fib = lambda f:Range->Range->Nat->Range.
lambda a0:Range. lambda a1:Range. lambda n:Nat.
if iszero n then a0
else 
let p0 = torange (down (setprecision a0 1)) in
let p1 = torange (down (setprecision a1 1)) in
f p1 (add p0 p1) (pred n);

fib = fix fib;

ans = fib 0.0 1.0 1000;
ans = setprecision ans 1;
down ans;

