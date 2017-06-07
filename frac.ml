open Syntax
open Support.Error

(* checkarr arr, if arr[i] < 0 || arr[i] > 9, then return true *)
let checkarr arr len = (
let rflag = ref false in
for i = 0 to len-1 do
if arr.(i) < 0 then rflag := true;
if arr.(i) > 9 then rflag := true;
done;
!rflag )

(* frac abs beq, if |t1|>=|t2| then true else false *)
let fabsbeq t1 t2 =
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->(
if lena - frca > lenb - frcb then true else
if lena - frca < lenb - frcb then false else begin
let tflag = ref true in
let rflag = ref true in
let lenc = min lena lenb in
for i = lenc-1 downto 0 do
if !tflag then
	if arra.(i-lenc+lena) > arrb.(i-lenc+lenb) then begin tflag := false; rflag := true; end else
	if arra.(i-lenc+lena) < arrb.(i-lenc+lenb) then begin tflag := false; rflag := false; end
done;
if !tflag then (lena >= lenb) else !rflag end)
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

(* frac abs add, return |t1|+|t2| (|t1| > |t2|) *)
let fabsadd t1 t2 = 
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->(
let frcc = max frca frcb in
let lenc = ref (lena - frca + frcc + 1) in
let arrc = Array.make !lenc 0 in
for i = 0 to lena-1 do
    arrc.(!lenc-2-i) <- (arrc.(!lenc-2-i) + arra.(lena-1-i));
done;
let sti = frcc - frcb in
for i = sti to sti+lenb-1 do
    arrc.(i) <- (arrc.(i) + arrb.(i-sti));
done;
for i = 1 to !lenc-1 do
    arrc.(i) <- (arrc.(i) + arrc.(i-1) / 10);
    arrc.(i-1) <- arrc.(i-1) mod 10;
done;
while (arrc.(!lenc-1) = 0) && (not (!lenc = 1)) do lenc := !lenc - 1; done;
!lenc, arrc )
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

(* frac abs sub, return |t1|-|t2| (>=0) *)
let fabssub t1 t2 = 
match t1 with
  TmFrac(fi, _, frca, lena, arra) ->(
match t2 with
  TmFrac(fi, _, frcb, lenb, arrb) ->(
let frcc = max frca frcb in
let lenc = ref (lena - frca + frcc + 1) in
let arrc = Array.make !lenc 0 in
for i = 0 to lena-1 do
    arrc.(!lenc-2-i) <- (arrc.(!lenc-2-i) + arra.(lena-1-i));
done;
let sti = frcc - frcb in
for i = sti to sti+lenb-1 do
    arrc.(i) <- (arrc.(i) - arrb.(i-sti));
done;
for i = 1 to !lenc-1 do
while arrc.(i-1) < 0 do
	arrc.(i-1) <- (arrc.(i-1) + 10);
	arrc.(i) <- (arrc.(i) - 1);
done;
    arrc.(i) <- (arrc.(i) + arrc.(i-1) / 10);
    arrc.(i-1) <- arrc.(i-1) mod 10;
done;
while (arrc.(!lenc-1) = 0) && (not (!lenc = 1)) do lenc := !lenc - 1; done;
!lenc, arrc )
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

(* frac big add t1 t2, return t1 + t2 *)
let bigadd t1 t2 =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
if lena = 0 then
	raise (Failure "Bad t1(len) accepted") else
if checkarr arra lena then
	raise (Failure "Bad t1(array) accepted") else
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->(
if lenb = 0 then
	raise (Failure "Bad t2(len) accepted") else
if checkarr arrb lenb then
	raise (Failure "Bad t2(array) accepted") else
if sgna = sgnb then
    if fabsbeq t1 t2 then
    	let lenc, arrc = fabsadd t1 t2 in
    	TmFrac(fi, sgna, max frca frcb, lenc, arrc)
    else
        let lenc, arrc = fabsadd t2 t1 in
    	TmFrac(fi, sgna, max frca frcb, lenc, arrc)
else
	if fabsbeq t1 t2 then
		let lenc, arrc = fabssub t1 t2 in
		TmFrac(fi, sgna, max frca frcb, lenc, arrc)
	else
		let lenc, arrc = fabssub t2 t1 in
		TmFrac(fi, sgnb, max frca frcb, lenc, arrc) )
| TmDenormal(fi, deno2) -> t2
| _ -> raise (Failure "TmFrac term t2 expected"))
| TmDenormal(fi, deno1) ->(
match t2 with
  TmFrac(fi, _, _, _, _) -> t1
| TmDenormal(fi, deno2) ->
if (deno1 = 0) || (deno2 = 0) then
	let t' = TmDenormal(fi, 0) in t'
else if deno1 = deno2 then t1 else
	let t' = TmDenormal(fi, 0) in t'
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

(* big frac sub t1 t2, return t1 - t2 *)
let bigsub t1 t2 =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
if lena = 0 then
	raise (Failure "Bad t1(len) accepted") else
if checkarr arra lena then
	raise (Failure "Bad t1(array) accepted") else
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->
if lenb = 0 then
	raise (Failure "Bad t2(len) accepted") else
if checkarr arrb lenb then
	raise (Failure "Bad t2(array) accepted") else
let t2' = TmFrac(fi, 1-sgnb, frcb, lenb, arrb) in ( bigadd t1 t2' )
| TmDenormal(fi, deno2) -> 
	let t2' = TmDenormal(fi, -deno2) in t2'
| _ -> raise (Failure "TmFrac term t2 expected"))
| TmDenormal(fi, deno1) ->(
match t2 with
  TmFrac(fi, _, _, _, _) -> t1
| TmDenormal(fi, deno2) ->
if (deno1 = 0) || (deno2 = 0) then
	let t' = TmDenormal(fi, 0) in t'
else if not (deno1 = deno2) then t1 else 
	let t' = TmDenormal(fi, 0) in t'
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")

(* big frac mul t1 t2, return t1 * t2 *)
let bigmul t1 t2 = 
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
if lena = 0 then
	raise (Failure "Bad t1(len) accepted") else
if checkarr arra lena then
	raise (Failure "Bad t1(array) accepted") else
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->(
if lenb = 0 then
	raise (Failure "Bad t2(len) accepted") else
if checkarr arrb lenb then
	raise (Failure "Bad t2(array) accepted") else
let lenc = ref (lena + lenb) in
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
while (arrc.(!lenc-1) = 0) && (not (!lenc = 1)) do lenc := (!lenc-1) done;
let t' = TmFrac(fi, 1 - (sgna lxor sgnb), frca + frcb, !lenc, arrc) in t' )
| TmDenormal(fi, deno2) ->
if deno2 = 0 then t2 else
if (lena = 1) && (arra.(0) = 0) then
	let t' = TmDenormal(fi, 0) in t'
else t2
| _ -> raise (Failure "TmFrac term t2 expected"))
| TmDenormal(fi, deno1) ->(
match t2 with
  TmFrac(fi, _, _, lenb, arrb) ->
if deno1 = 0 then t1 else
if (lenb = 1) && (arrb.(0) = 0) then
	let t' = TmDenormal(fi, 0) in t'
else t1
| TmDenormal(fi, deno2) ->
if (deno1 = 0) || (deno2 = 0) then
	let t' = TmDenormal(fi, 0) in t'
else
	let t' = TmDenormal(fi, deno1*deno2) in t'
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")


(* big frac div t1 t2 with precision v, return t1/t2(with precision v) *)
let bigdiv t1 t2 v =
match t1 with
  TmFrac(fi, sgna, frca, lena, arra) ->(
if lena = 0 then
	raise (Failure "Bad t1(len) accepted") else
if checkarr arra lena then
	raise (Failure "Bad t1(array) accepted") else
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->(
if lenb = 0 then
	raise (Failure "Bad t2(len) accepted") else
if checkarr arrb lenb then
	raise (Failure "Bad t2(array) accepted") else
if (lenb = 1) && (arrb.(0) = 0) then
	( let t' = TmDenormal(fi, (1-(sgna lxor sgnb))*2-1) in t' )
else begin
let lenc = lena - (frca - frcb) + v in
let lens = ref lenc in
let arrs = Array.make !lens 0 in
let leny = ref 0 in
let arry = Array.make (lenb+1) 0 in
for i = lenc-1 downto 0 do
	for j = !leny downto 1 do
		arry.(j) <- arry.(j-1)
	done;
	leny := !leny + 1;
	if i - lenc + lena >= 0 then
		arry.(0) <- arra.(i-lenc+lena)
	else
		arry.(0) <- 0;
	let dflag = ref true in
	let d = ref 0 in
	for j = 1 to 9 do
		let ys = TmFrac(fi, 1, 0, !leny, arry) in
		let cs = TmFrac(fi, 1, 0, lenb, arrb) in
		let ds = TmFrac(fi, 1, 0, 1, (Array.make 1 (!d+1))) in
		let nv = bigmul cs ds in
        if (!dflag) && (fabsbeq ys nv) then
            d := !d + 1
        else
            dflag := false; 
	done;
    arrs.(i) <- !d;
	let ys = TmFrac(fi, 1, 0, !leny, arry) in
	let cs = TmFrac(fi, 1, 0, lenb, arrb) in
	let ds = TmFrac(fi, 1, 0, 1, (Array.make 1 !d)) in
	let nv = bigmul cs ds in
    let lent, arrt = fabssub ys nv in(
        for j = !leny-1 downto 0 do
            arry.(j) <- arrt.(j)
        done;
        leny := lent;
    )
done; 
while (arrs.(!lens-1) = 0) && (not (!lens = 1)) do lens := !lens - 1 done;
let t' = TmFrac(fi, 1 - (sgna lxor sgnb), v, !lens, arrs) in t' end )
| TmDenormal(fi, deno2) -> (
if deno2 = 0 then t2 else 
	let t' = TmFrac(fi, 1 - (sgna lxor ((deno2+1)/2)), v, 1, Array.make 1 0) in t' )
| _ -> raise (Failure "TmFrac term t2 expected"))
| TmDenormal(fi, deno1) ->(
match t2 with
  TmFrac(fi, sgnb, frcb, lenb, arrb) ->(
if deno1 = 0 then t1 else
	let t' = TmDenormal(fi, deno1 * (sgnb*2-1)) in t' )
| TmDenormal(fi, deno2) -> let t' = TmDenormal(fi, 0) in t'
| _ -> raise (Failure "TmFrac term t2 expected"))
| _ -> raise (Failure "TmFrac term t1 expected")


(* big frac sqrt t v, return sqrt(t) with precision v *)
let bigsqrt t v = 
match t with
  TmFrac(fi, sgn, frc, len, arr) ->(
if sgn = 0 then
	raise (Failure "TmFrac(positive) term t expected")
else
let lenint = len - frc in
let lens = ref (lenint+v) in
let arrs = Array.make !lens 0 in
for i = !lens-1 downto 0 do
	let d = ref 0 in
	let dflag = ref true in
	for j = 1 to 9 do
	if !dflag then (
		let narr = Array.make !lens 0 in
		for k = 0 to !lens-1 do
			narr.(k) <- arrs.(k)
		done;
		narr.(i) <- j;
		let ta = TmFrac(fi, 1, 0, !lens, narr) in
		let nv = bigmul ta ta in
		let bs = TmFrac(fi, 1, 0, len, arr) in
		if fabsbeq bs nv then
			d := j
		else
			dflag := false
	)
	done;
	arrs.(i) <- !d
done;
while (arrs.(!lens-1) = 0) && (not (!lens = 1)) do lens := !lens - 1 done;
let t' = TmFrac(fi, 1, v, !lens, arrs) in t' )
| _ -> raise (Failure "TmFrac(without denormal) term t expected")
