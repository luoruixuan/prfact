/* Examples for testing */

 lambda x:Bot. x;
 lambda x:Bot. x x; 

 
lambda x:<a:Bool,b:Bool>. x;


lambda x:Top. x;
 (lambda x:Top. x) (lambda x:Top. x);
(lambda x:Top->Top. x) (lambda x:Top. x);


(lambda r:{x:Top->Top}. r.x r.x) 
  {x=lambda z:Top.z, y=lambda z:Top.z}; 


"hello";

unit;

lambda x:A. x;

let x=true in x;

{x=true, y=false}; 
{x=true, y=false}.x;
{true, false}; 
{true, false}.1; 


if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

lambda x:Bool. x;
(lambda x:Bool->Bool. if x false then true else false) 
  (lambda x:Bool. if x then false else true); 

lambda x:Nat. succ x;
(lambda x:Nat. succ (succ x)) (succ 0); 

T = Nat->Nat;
lambda f:T. lambda x:Nat. f (f x);

2.0;
3.14159;
100.0;
100.00;
100.000;
10.0;
1.0;
0.1;
0.01;
0.001;
0.0001;
1.0001;
10.0001;
100.0009;
0.0;
0.00000;
00.00000000000000000;
100.000000000;
0100.00000;
00010.000;


setprecision (div 8.0 2.0) 20;
setprecision (div 8.0 0.0) 10;


setprecision (add (div 243.5 293.203) (div 23333333.333 233.33)) 8;
add (div 243.5 293.203) (div 23333333.333 233.33);
t0 = div 243.5 293.203;
t1 = div 23333333.333 233.33;

t2 = sub 66666.6666 554433.2211;
setprecision t2 8;
t3 = add t0 t1;
setprecision t3 8;
t4 = mul t3 t2;
setprecision t4 8;
setprecision t0 15;
setprecision t1 20;
setprecision t2 4;
r3 = setprecision t3 8;
r4 = setprecision t4 10;
add 233.0 23333.0;
round r3 10;
round r4 10;
less (round r3 10) (round r4 10);
