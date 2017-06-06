open Syntax
open Support.Error



(* Tmfrac sgn * frac * len * arr *)
(*
let max v1 v2 = if v1 > v2 then v1 else v2;
let min v1 v2 = if v1 < v2 then v1 else v2;
*)

let fabsbeq t1 t2 =
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->
(
if lena - frca > lenb - frcb then true else
if lena - frca < lenb - frcb then false else (
let tflag = ref false in
let rflag = ref true in
for i = 0 to lena-1 do
if not !tflag then
	if arra.(i) > arrb.(i) then begin tflag := true; rflag := true; end else
	if arra.(i) < arrb.(i) then begin tflag := true; rflag := false; end
done;
!rflag
)
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

let fabsadd t1 t2 = 
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->
(
let lenc = ref (lena + frcb - frca + 1) in
let arrc = Array.make !lenc 0 in
for i = 1 to !lenc-1 do
arrc.(i) <- (arrc.(i) + arra.(i) + arrb.(i));
while arrc.(i) > 9 do
	arrc.(i+1) <- (arrc.(i+1) + 1);
	arrc.(i) <- (arrc.(i) - 10);
done;
done;
while (arrc.(!lenc-1) = 0) && (not (!lenc = 0)) do lenc := !lenc - 1; done;
!lenc, arrc
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

let fabssub t1 t2 = 
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->
(
let lenc = ref (lena + frcb - frca) in
let arrc = Array.make !lenc 0 in
for i = 1 to !lenc-1 do
arrc.(i) <- (arrc.(i) + arra.(i) - arrb.(i));
while arrc.(i) < 0 do
	arrc.(i+1) <- (arrc.(i+1) - 1);
	arrc.(i) <- (arrc.(i) + 10);
done;
done;
while (arrc.(!lenc-1) = 0) && (not (!lenc = 0)) do lenc := !lenc - 1; done;
!lenc, arrc
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")


let bigadd t1 t2 =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->
(
if sgna = sgnb then
	let lenc, arrc = fabsadd t1 t2 in
	TmFrac(fi, sgna, max frca frcb, lenc, arrc)
else
	if fabsbeq t1 t2 then
		let lenc, arrc = fabssub t1 t2 in
		TmFrac(fi, sgna, max frca frcb, lenc, arrc)
	else
		let lenc, arrc = fabssub t1 t2 in
		TmFrac(fi, sgna, max frca frcb, lenc, arrc)
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

let bigsub t1 t2 =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->
      let t2' = TmFrac(fi, 1-sgnb, frcb, lenb, arrb) in
( bigadd t1 t2' )
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

let bigmul t1 t2 = 
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->
(
    let lenc = ref (lena + lenb + 2) in
    let arrc = Array.make !lenc 0 in
for i = 0 to lena-1 do
	for j = 0 to lenb-1 do
		arrc.(i+j) <- (arrc.(i+j) + arra.(i) * arrb.(j))
	done;
done;
for i = 1 to !lenc-1 do
    arrc.(i) <- (arrc.(i) + arrc.(i-1) / 10);
    arrc.(i-1) <- (arrc.(i-1) mod 10);
done;
while arrc.(!lenc-1) = 0 do lenc := (!lenc-1) done;
TmFrac(fi, sgna lxor sgnb, frca + frcb, !lenc, arrc)
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

let bigdiv t1 t2 =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->
(
)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")
