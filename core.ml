open Format
open Syntax
open Support.Error
open Support.Pervasive
open Frac

(* ------------------------   EVALUATION  ------------------------ *)

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmTag(_,l,t1,_) -> isval ctx t1
  | TmString _  -> true
  | TmUnit(_)  -> true
  | TmLoc(_,_) -> true
  | TmFloat _  -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | TmRecord(_,fields) -> List.for_all (fun (l,ti) -> isval ctx ti) fields

  | TmFrac(_,_,_,_,_) -> true
  | TmDenormal(_,_) -> true
  | TmRange(_,_,_,_) -> true

  | _ -> false

let isrange t = match t with
    TmRange(_,_,_,_) -> true
  | _ -> false
let isfrac t = match t with
    TmFrac(_,_,_,_,_) -> true
  | _ -> false

type store = term list  
let emptystore = []
let extendstore store v = (List.length store, List.append store [v])
let lookuploc store l = List.nth store l
let updatestore store n v =
  let rec f s = match s with 
      (0, v'::rest) -> v::rest
    | (n, v'::rest) -> v' :: (f (n-1,rest))
    | _ -> error dummyinfo "updatestore: bad index"
  in
    f (n,store)
let shiftstore i store = List.map (fun t -> termShift i t) store 

exception NoRuleApplies


let k = 1024 

let zero fi fh = 
    let a = Array.make 1 0 in TmFrac(fi, fh, 0, 1, a)
let one fi fh =
    let a = Array.make 1 1 in TmFrac(fi, fh, 0, 1, a)
let biginv f c = 
    match f with
    TmFrac(fi,_,_,_,_) -> bigdiv (one fi 1) f c
    | TmDenormal(fi,_) -> bigdiv (one fi 1) f c
    | _ -> raise (Failure "Not a frac")

let lessthan f1 f2 =
    match f1 with
    TmFrac(_, fh1, fr1, l1, ar1) ->
        (
        match f2 with
        TmFrac(_, fh2, fr2, l2, ar2) ->
            if (fh1=1) && (fh2=0) then false
            else if (fh1=0) && (fh2=1) then true
            else if (fh1=1) then fabsbeq f2 f1
            else fabsbeq f1 f2
        | _ -> false
        )
    | _ -> false
let bigmax f1 f2 = 
    if lessthan f1 f2 then f2 else f1
let bigmin f1 f2 =
    if lessthan f1 f2 then f1 else f2

let checkd f =
    match f with
    TmFrac(fi, fh, fr, l, ar) ->
        if (l-fr)>=k then TmDenormal(fi, fh*2-1)
        else if (fr-l)>=k then zero fi fh
        else f
    | _ -> f
let iszero f = 
    match f with
    TmFrac(fi, fh, fr, l, ar) ->
        if (fr-l)>=k then true
        else false
    | _ -> false
    

let isvalid f1 f2 = 
    match f1 with
    TmFrac(_,_,_,_,_) ->
        (match f2 with
        TmFrac(_,_,_,_,_) -> true
        | _ -> false)
    | TmDenormal(_,d1) ->
        (match f2 with
        TmDenormal(_,d2) -> (d1=d2)
        | _ -> false)
    | _ -> false

let upfrac f c = 
    match f with
    TmDenormal(_,_) -> f
    | TmFrac(fi, fh, fr, l, ar) ->
            if fr<=c then f
            else let newl = l+c-fr in
            let a1 = Array.make 1 1 in let tf = TmFrac(fi, fh, c, 1, a1) in
            if newl<=0 then 
                (
                    if fh=0 then zero fi fh
                    else tf
                )
            else let a = Array.make newl 0 in
            for i = (fr-c) to (l-1) do
                a.(i+c-fr) <- ar.(i);
            done;
            let re=TmFrac(fi, fh, c, newl, a) in
            if fh=0 then re
            else bigadd re tf
    | _ -> raise (Failure "Not a frac")
let downfrac f c = 
    match f with
    TmDenormal(_,_) -> f
    | TmFrac(fi, fh, fr, l, ar) ->
            if fr<=c then f
            else let newl = l+c-fr in
            let a1 = Array.make 1 1 in let tf = TmFrac(fi, fh, c, 1, a1) in
            if newl<=0 then 
                (
                    if fh=1 then zero fi fh
                    else tf
                )
            else let a = Array.make newl 0 in
            for i = (fr-c) to (l-1) do
                a.(i+c-fr) <- ar.(i);
            done;
            let re=TmFrac(fi, fh, c, newl, a) in
            if fh=1 then re
            else bigadd re tf
    | _ -> raise (Failure "Not a frac")
let addrange r1 r2 c = 
    match r1 with
    TmRange(fi, fl1, fr1, ft1) ->
        (match r2 with
        TmRange(fi, fl2, fr2, ft2) ->
            let nl = checkd (bigadd fl1 fl2) in
            let nr = checkd (bigadd fr1 fr2) in
            TmRange(fi, downfrac nl c, upfrac nr c, TmAdd(fi, r1,r2,c))
    | _ -> raise (Failure "Not a range"))
    | _ -> raise (Failure "Not a range")
let subrange r1 r2 c = 
    match r1 with
    TmRange(fi, fl1, fr1, ft1) ->
        (match r2 with
        TmRange(fi, fl2, fr2, ft2) ->
            let nl = checkd (bigsub fl1 fr2) in
            let nr = checkd (bigsub fr1 fl2) in
            TmRange(fi, downfrac nl c, upfrac nr c, TmSub(fi, r1,r2,c))
    | _ -> raise (Failure "Not a range"))
    | _ -> raise (Failure "Not a range")
let mulrange r1 r2 c = 
    match r1 with
    TmRange(fi, fl1, fr1, _) ->
        (
        match r2 with
        TmRange(_, fl2, fr2, _) ->
            let f11 = bigmul fl1 fl2 in
            let f12 = bigmul fl1 fr2 in
            let f21 = bigmul fr1 fl2 in
            let f22 = bigmul fr1 fr2 in
            let ll = checkd (bigmin (bigmin f11 f12) (bigmin f21 f22)) in
            let rr = checkd (bigmax (bigmax f11 f12) (bigmax f21 f22)) in
            TmRange(fi, downfrac ll c, upfrac rr c, TmMul(fi, r1, r2, c))
        | _ -> raise (Failure "Not a range")
        )
    | _ -> raise (Failure "Not a range")

let invrange r c =
    match r with
    TmRange(fi, fl, fr, ft) -> 
        let il = biginv fr (c+1) in
        let ir = biginv fl (c+1) in
        TmRange(fi, downfrac il c, upfrac ir c, TmInv(fi, r, c))
    | _ -> raise (Failure "Not a range")

let todenormal r = 
    match r with
    TmRange(fi, f1, f2, ft) -> 
        (
            match f1 with 
            TmFrac(_,_,_,_,_) -> TmRange(fi, f2, f2, ft)
            | _ -> TmRange(fi, f1, f1, ft)
        )
    | _ -> raise (Failure "Not a range")
let checkinv r = 
    match r with
    TmRange(fi, fl, fr, ft) ->
        let ll = iszero fl in
        let rr = iszero fr in
        (
        match fl with
        TmFrac(_,fh1,_,_,_) ->
            (
            match fr with
            TmFrac(_,fh2,_,_,_) ->
                (not ll) && (not rr) && (fh1=fh2)
            | _ -> raise (Failure "Not a frac")
            )
        | _ -> true
        )
    | _ -> raise (Failure "Not a range")

let fmaxlog f = 
    match f with 
    TmFrac(_,fh,fr,l,ar) -> l-fr+1
    | TmDenormal(_,_) -> 0
    | _ -> raise (Failure "Not a frac")
let maxlog r = 
    match r with
    TmRange(_, f1, f2, _) -> max (fmaxlog f1) (fmaxlog f2)
    | _ -> raise (Failure "Not a range")



let rec eval1 ctx store t = match t with
    TmApp(fi,TmAbs(_,x,tyT11,t12),v2) when isval ctx v2 ->
      termSubstTop v2 t12, store
  | TmApp(fi,v1,t2) when isval ctx v1 ->
      let t2',store' = eval1 ctx store t2 in
      TmApp(fi, v1, t2'), store'
  | TmApp(fi,t1,t2) ->
      let t1',store' = eval1 ctx store t1 in
      TmApp(fi, t1', t2), store'
  | TmIf(_,TmTrue(_),t2,t3) ->
      t2, store
  | TmIf(_,TmFalse(_),t2,t3) ->
      t3, store
  | TmIf(fi,t1,t2,t3) ->
      let t1',store' = eval1 ctx store t1 in
      TmIf(fi, t1', t2, t3), store'
  | TmLet(fi,x,v1,t2) when isval ctx v1 ->
      termSubstTop v1 t2, store 
  | TmLet(fi,x,t1,t2) ->
      let t1',store' = eval1 ctx store t1 in
      TmLet(fi, x, t1', t2), store' 
  | TmFix(fi,v1) as t when isval ctx v1 ->
      (match v1 with
         TmAbs(_,_,_,t12) -> termSubstTop t t12, store
       | _ -> raise NoRuleApplies)
  | TmFix(fi,t1) ->
      let t1',store' = eval1 ctx store t1
      in TmFix(fi,t1'), store'
  | TmRecord(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest',store' = evalafield rest in
          (l,vi)::rest', store'
      | (l,ti)::rest -> 
          let ti',store' = eval1 ctx store ti in
          (l, ti')::rest, store'
      in let fields',store' = evalafield fields in
      TmRecord(fi, fields'), store'
  | TmProj(fi, (TmRecord(_, fields) as v1), l) when isval ctx v1 ->
      (try List.assoc l fields, store
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1',store' = eval1 ctx store t1 in
      TmProj(fi, t1', l), store'
  | TmTag(fi,l,t1,tyT) ->
      let t1',store' = eval1 ctx store t1 in
      TmTag(fi, l, t1',tyT), store'
  | TmCase(fi,TmTag(_,li,v11,_),branches) when isval ctx v11->
      (try 
         let (x,body) = List.assoc li branches in
         termSubstTop v11 body, store
       with Not_found -> raise NoRuleApplies)
  | TmCase(fi,t1,branches) ->
      let t1',store' = eval1 ctx store t1 in
      TmCase(fi, t1', branches), store'
  | TmAscribe(fi,v1,tyT) when isval ctx v1 ->
      v1, store
  | TmAscribe(fi,t1,tyT) ->
      let t1',store' = eval1 ctx store t1 in
      TmAscribe(fi,t1',tyT), store'
  | TmVar(fi,n,_) ->
      (match getbinding fi ctx n with
          TmAbbBind(t,_) -> t,store 
        | _ -> raise NoRuleApplies)
  | TmRef(fi,t1) ->
      if not (isval ctx t1) then
        let (t1',store') = eval1 ctx store t1
        in (TmRef(fi,t1'), store')
      else
        let (l,store') = extendstore store t1 in
        (TmLoc(dummyinfo,l), store')
  | TmDeref(fi,t1) ->
      if not (isval ctx t1) then
        let (t1',store') = eval1 ctx store t1
        in (TmDeref(fi,t1'), store')
      else (match t1 with
            TmLoc(_,l) -> (lookuploc store l, store)
          | _ -> raise NoRuleApplies)
  | TmAssign(fi,t1,t2) ->
      if not (isval ctx t1) then
        let (t1',store') = eval1 ctx store t1
        in (TmAssign(fi,t1',t2), store')
      else if not (isval ctx t2) then
        let (t2',store') = eval1 ctx store t2
        in (TmAssign(fi,t1,t2'), store')
      else (match t1 with
            TmLoc(_,l) -> (TmUnit(dummyinfo), updatestore store l t2)
          | _ -> raise NoRuleApplies)
  | TmTimesfloat(fi,TmFloat(_,f1),TmFloat(_,f2)) ->
      TmFloat(fi, f1 *. f2), store
  | TmTimesfloat(fi,(TmFloat(_,f1) as t1),t2) ->
      let t2',store' = eval1 ctx store t2 in
      TmTimesfloat(fi,t1,t2') , store'
  | TmTimesfloat(fi,t1,t2) ->
      let t1',store' = eval1 ctx store t1 in
      TmTimesfloat(fi,t1',t2) , store'
  | TmSucc(fi,t1) ->
      let t1',store' = eval1 ctx store t1 in
      TmSucc(fi, t1'), store'
  | TmPred(_,TmZero(_)) ->
      TmZero(dummyinfo), store
  | TmPred(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      nv1, store
  | TmPred(fi,t1) ->
      let t1',store' = eval1 ctx store t1 in
      TmPred(fi, t1'), store'
  | TmIsZero(_,TmZero(_)) ->
      TmTrue(dummyinfo), store
  | TmIsZero(_,TmSucc(_,nv1)) when (isnumericval ctx nv1) ->
      TmFalse(dummyinfo), store
  | TmIsZero(fi,t1) ->
      let t1',store' = eval1 ctx store t1 in
      TmIsZero(fi, t1'), store'
  (* New evaluation rules *)
  (* E-Div *)
  | TmDiv(fi, t1, t2, c) -> TmMul(fi, t1, TmInv(fi, t2, c), c), store
  (* E-Add *)
  | TmAdd(fi, t1, t2, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmAdd(fi, t1', t2, c), store'
  | TmAdd(fi, r1, t2, c) when not (isrange t2) ->
      let t2', store' = eval1 ctx store t2 in
      TmAdd(fi, r1, t2', c), store'
  | TmAdd(fi, r1, r2, c) ->
      let r = addrange r1 r2 c in
      (
      match r with
      TmRange(fi, f1, f2, ft) ->
        if isvalid f1 f2 then r, store
        else if (c >= k) then todenormal r, store
        else TmAdd(fi, TmSetprecision(fi, r1, c*2), TmSetprecision(fi, r2, c*2), c*2), store
      | _ -> error fi "addrange error"
      )
  (* E-Sub *)  
  | TmSub(fi, t1, t2, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmSub(fi, t1', t2, c), store'
  | TmSub(fi, r1, t2, c) when not (isrange t2) ->
      let t2', store' = eval1 ctx store t2 in
      TmSub(fi, r1, t2', c), store'
  | TmSub(fi, r1, r2, c) ->
      let r = subrange r1 r2 c in
      (
      match r with
      TmRange(fi, f1, f2, ft) ->
        if isvalid f1 f2 then r, store
        else if (c >= k)then todenormal r, store
        else TmSub(fi, TmSetprecision(fi, r1, c*2), TmSetprecision(fi, r2, c*2), c*2), store
      | _ -> error fi "subrange error"
      )
  (* E-Mul *)
  | TmMul(fi, t1, t2, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmMul(fi, t1', t2, c), store'
  | TmMul(fi, r1, t2, c) when not (isrange t2) ->
      let t2', store' = eval1 ctx store t2 in
      TmMul(fi, r1, t2', c), store'
  | TmMul(fi, r1, r2, c) ->
      let r = mulrange r1 r2 c in
      (
      match r with
      TmRange(fi, f1, f2, ft) ->
        if isvalid f1 f2 then r, store
        else if (c >= k) then todenormal r, store
        else TmMul(fi, TmSetprecision(fi, r1, c*2), TmSetprecision(fi, r2, c*2), c*2), store
      | _ -> error fi "mulrange error"
      )
  (* E-Inv *)  
  | TmInv(fi, t1, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmInv(fi, t1', c), store'
  | TmInv(fi, r1, c) ->
      if checkinv r1 then invrange r1 c, store
      else if (c>=k) then invrange (todenormal r1) c, store
      else TmInv(fi, TmSetprecision(fi, r1, c*2), c*2), store
  (* E-Setprecision *)
  | TmSetprecision(fi, t1, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmSetprecision(fi, t1', c), store'
  | TmSetprecision(fi, r1, c) ->
      (
        match r1 with
        TmRange(fi', f1, f2, ft) ->
            (
                match ft with
                  TmUnit(fi) -> r1, store
                  | TmAdd(fi, r1, r2, cn) -> 
                      let p1 = TmSetprecision(fi, r1, max (c+1) cn) in
                      let r1', store' = eval1 ctx store p1 in
                      let p2 = TmSetprecision(fi, r2, max (c+1) cn) in
                      let r2', store'' = eval1 ctx store' p2 in
                      addrange r1' r2' (c+1), store''
                  | TmSub(fi, r1, r2, cn) -> 
                      let p1 = TmSetprecision(fi, r1, max (c+1) cn) in
                      let r1', store' = eval1 ctx store p1 in
                      let p2 = TmSetprecision(fi, r2, max (c+1) cn) in
                      let r2', store'' = eval1 ctx store' p2 in
                      subrange r1' r2' (c+1), store''
                  | TmMul(fi, r1, r2, cn) -> 
                      let p1 = TmSetprecision(fi, r1, max (c+1+(maxlog r2)) cn) in
                      let r1', store' = eval1 ctx store p1 in
                      let p2 = TmSetprecision(fi, r2, max (c+1+(maxlog r1)) cn) in
                      let r2', store'' = eval1 ctx store' p2 in
                      mulrange r1' r2' (max (c+1) cn), store''
                  | TmInv(fi, r1, cn) ->
                      let p1 = TmSetprecision(fi, r1, max (c+1+2*(maxlog r1)) cn) in  
                      let r1', store' = eval1 ctx store p1 in
                      invrange r1' (max (c+1) cn), store'
                  | _ -> error fi "range from invalid"
            )    
        | _ -> error fi "invalid range"
      )
  (* E-Round/Up/Down/LESS *)
  | TmRound(fi, t1, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmRound(fi, t1', c), store'
  | TmRound(fi, r1, c) -> 
          (match r1 with
          TmRange(fi, f1, f2, _) -> f1, store
          | _ -> error fi "not a range")
  | TmUp(fi, t1, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmUp(fi, t1', c), store'
  | TmUp(fi, r1, c) -> 
          (match r1 with
          TmRange(fi, f1, f2, _) -> upfrac f2 c, store
          | _ -> error fi "not a range")
  | TmDown(fi, t1, c) when not (isrange t1) ->
      let t1', store' = eval1 ctx store t1 in
      TmDown(fi, t1', c), store'
  | TmDown(fi, r1, c) -> 
          (match r1 with
          TmRange(fi, f1, f2, _) -> downfrac f1 c, store
          | _ -> error fi "not a range")
  | TmLess(fi, t1, t2) when not (isfrac t1) ->
          let t1', store' = eval1 ctx store t1 in
          TmLess(fi, t1', t2), store'
  | TmLess(fi, f1, t2) when not (isfrac t2) ->
          let t2', store' = eval1 ctx store t2 in
          TmLess(fi, f1, t2'), store'
  | TmLess(fi, f1, f2) -> 
          let re = if lessthan f1 f2 then TmTrue(fi) else TmFalse(fi) in re, store
  

  | _ -> 
      raise NoRuleApplies

let rec eval ctx store t =
  try let t',store' = eval1 ctx store t
      in eval ctx store' t'
  with NoRuleApplies -> t,store

(* ------------------------   SUBTYPING  ------------------------ *)

let evalbinding ctx store b = match b with
    TmAbbBind(t,tyT) ->
      let t',store' = eval ctx store t in 
      TmAbbBind(t',tyT), store'
  | bind -> bind,store

let istyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> true
  | _ -> false

let gettyabb ctx i = 
  match getbinding dummyinfo ctx i with
    TyAbbBind(tyT) -> tyT
  | _ -> raise NoRuleApplies

let rec computety ctx tyT = match tyT with
    TyVar(i,_) when istyabb ctx i -> gettyabb ctx i
  | _ -> raise NoRuleApplies

let rec simplifyty ctx tyT =
  try
    let tyT' = computety ctx tyT in
    simplifyty ctx tyT' 
  with NoRuleApplies -> tyT

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyTop,TyTop) -> true
  | (TyBot,TyBot) -> true
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyString,TyString) -> true
  | (TyId(b1),TyId(b2)) -> b1=b2
  | (TyFloat,TyFloat) -> true
  | (TyUnit,TyUnit) -> true
  | (TyRef(tyT1),TyRef(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TySource(tyT1),TySource(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TySink(tyT1),TySink(tyT2)) -> tyeqv ctx tyT1 tyT2
  | (TyVar(i,_), _) when istyabb ctx i ->
      tyeqv ctx (gettyabb ctx i) tyT
  | (_, TyVar(i,_)) when istyabb ctx i ->
      tyeqv ctx tyS (gettyabb ctx i)
  | (TyVar(i,_),TyVar(j,_)) -> i=j
  | (TyBool,TyBool) -> true
  | (TyNat,TyNat) -> true

  | (TyRange,TyRange) -> true
  | (TyFrac,TyFrac) -> true

  | (TyRecord(fields1),TyRecord(fields2)) -> 
       List.length fields1 = List.length fields2
       &&                                         
       List.for_all 
         (fun (li2,tyTi2) ->
            try let (tyTi1) = List.assoc li2 fields1 in
                tyeqv ctx tyTi1 tyTi2
            with Not_found -> false)
         fields2
  | (TyVariant(fields1),TyVariant(fields2)) ->
       (List.length fields1 = List.length fields2)
       && List.for_all2
            (fun (li1,tyTi1) (li2,tyTi2) ->
               (li1=li2) && tyeqv ctx tyTi1 tyTi2)
            fields1 fields2
  | _ -> false

let rec subtype ctx tyS tyT =
   tyeqv ctx tyS tyT ||
   let tyS = simplifyty ctx tyS in
   let tyT = simplifyty ctx tyT in
   match (tyS,tyT) with
     (_,TyTop) -> 
       true
   | (TyBot,_) -> 
       true
   | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (subtype ctx tyT1 tyS1) && (subtype ctx tyS2 tyT2)
   | (TyRecord(fS), TyRecord(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fT
   | (TyVariant(fS), TyVariant(fT)) ->
       List.for_all
         (fun (li,tySi) -> 
            try let tyTi = List.assoc li fT in
                subtype ctx tySi tyTi
            with Not_found -> false)
         fS
   | (TyRef(tyT1),TyRef(tyT2)) ->
       subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1
   | (TyRef(tyT1),TySource(tyT2)) ->
       subtype ctx tyT1 tyT2
   | (TySource(tyT1),TySource(tyT2)) ->
       subtype ctx tyT1 tyT2
   | (TyRef(tyT1),TySink(tyT2)) ->
       subtype ctx tyT2 tyT1
   | (TySink(tyT1),TySink(tyT2)) ->
       subtype ctx tyT2 tyT1
   | (_,_) -> 
       false

let rec join ctx tyS tyT =
  if subtype ctx tyS tyT then tyT else 
  if subtype ctx tyT tyS then tyS else
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let commonLabels = 
        List.find_all (fun l -> List.mem l labelsT) labelsS in
      let commonFields = 
        List.map (fun li -> 
                    let tySi = List.assoc li fS in
                    let tyTi = List.assoc li fT in
                    (li, join ctx tySi tyTi))
                 commonLabels in
      TyRecord(commonFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(meet ctx  tyS1 tyT1, join ctx tyS2 tyT2)
  | (TyRef(tyT1),TyRef(tyT2)) ->
      if subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1 
        then TyRef(tyT1)
        else (* Warning: this is incomplete... *)
             TySource(join ctx tyT1 tyT2)
  | (TySource(tyT1),TySource(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TyRef(tyT1),TySource(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TySource(tyT1),TyRef(tyT2)) ->
      TySource(join ctx tyT1 tyT2)
  | (TySink(tyT1),TySink(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | (TyRef(tyT1),TySink(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | (TySink(tyT1),TyRef(tyT2)) ->
      TySink(meet ctx tyT1 tyT2)
  | _ -> 
      TyTop

and meet ctx tyS tyT =
  if subtype ctx tyS tyT then tyS else 
  if subtype ctx tyT tyS then tyT else 
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyRecord(fS), TyRecord(fT)) ->
      let labelsS = List.map (fun (li,_) -> li) fS in
      let labelsT = List.map (fun (li,_) -> li) fT in
      let allLabels = 
        List.append
          labelsS 
          (List.find_all 
            (fun l -> not (List.mem l labelsS)) labelsT) in
      let allFields = 
        List.map (fun li -> 
                    if List.mem li allLabels then
                      let tySi = List.assoc li fS in
                      let tyTi = List.assoc li fT in
                      (li, meet ctx tySi tyTi)
                    else if List.mem li labelsS then
                      (li, List.assoc li fS)
                    else
                      (li, List.assoc li fT))
                 allLabels in
      TyRecord(allFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(join ctx tyS1 tyT1, meet ctx tyS2 tyT2)
  | (TyRef(tyT1),TyRef(tyT2)) ->
      if subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1 
        then TyRef(tyT1)
        else (* Warning: this is incomplete... *)
             TySource(meet ctx tyT1 tyT2)
  | (TySource(tyT1),TySource(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TyRef(tyT1),TySource(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TySource(tyT1),TyRef(tyT2)) ->
      TySource(meet ctx tyT1 tyT2)
  | (TySink(tyT1),TySink(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | (TyRef(tyT1),TySink(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | (TySink(tyT1),TyRef(tyT2)) ->
      TySink(join ctx tyT1 tyT2)
  | _ -> 
      TyBot

(* ------------------------   TYPING  ------------------------ *)

let rec typeof ctx t =
  match t with
    TmInert(fi,tyT) ->
      tyT
  | TmVar(fi,i,_) -> getTypeFromContext fi ctx i
  | TmAbs(fi,x,tyT1,t2) ->
      let ctx' = addbinding ctx x (VarBind(tyT1)) in
      let tyT2 = typeof ctx' t2 in
      TyArr(tyT1, typeShift (-1) tyT2)
  | TmApp(fi,t1,t2) ->
      let tyT1 = typeof ctx t1 in
      let tyT2 = typeof ctx t2 in
      (match simplifyty ctx tyT1 with
          TyArr(tyT11,tyT12) ->
            if subtype ctx tyT2 tyT11 then tyT12
            else error fi "parameter type mismatch" 
        | TyBot -> TyBot
        | _ -> error fi "arrow type expected")
  | TmTrue(fi) -> 
      TyBool
  | TmFalse(fi) -> 
      TyBool
  | TmIf(fi,t1,t2,t3) ->
      if subtype ctx (typeof ctx t1) TyBool then
        join ctx (typeof ctx t2) (typeof ctx t3)
      else error fi "guard of conditional not a boolean"
  | TmLet(fi,x,t1,t2) ->
     let tyT1 = typeof ctx t1 in
     let ctx' = addbinding ctx x (VarBind(tyT1)) in         
     typeShift (-1) (typeof ctx' t2)
  | TmRecord(fi, fields) ->
      let fieldtys = 
        List.map (fun (li,ti) -> (li, typeof ctx ti)) fields in
      TyRecord(fieldtys)
  | TmProj(fi, t1, l) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRecord(fieldtys) ->
            (try List.assoc l fieldtys
             with Not_found -> error fi ("label "^l^" not found"))
        | TyBot -> TyBot
        | _ -> error fi "Expected record type")
  | TmCase(fi, t, cases) ->
      (match simplifyty ctx (typeof ctx t) with
         TyVariant(fieldtys) ->
           List.iter
             (fun (li,(xi,ti)) ->
                try let _ = List.assoc li fieldtys in ()
                with Not_found -> error fi ("label "^li^" not in type"))
             cases;
           let casetypes =
             List.map (fun (li,(xi,ti)) ->
                         let tyTi =
                           try List.assoc li fieldtys
                           with Not_found ->
                             error fi ("label "^li^" not found") in
                         let ctx' = addbinding ctx xi (VarBind(tyTi)) in
                         typeShift (-1) (typeof ctx' ti))
                      cases in
           List.fold_left (join ctx) TyBot casetypes
        | TyBot -> TyBot
        | _ -> error fi "Expected variant type")
  | TmFix(fi, t1) ->
      let tyT1 = typeof ctx t1 in
      (match simplifyty ctx tyT1 with
           TyArr(tyT11,tyT12) ->
             if subtype ctx tyT12 tyT11 then tyT12
             else error fi "result of body not compatible with domain"
         | TyBot -> TyBot
         | _ -> error fi "arrow type expected")
  | TmTag(fi, li, ti, tyT) ->
      (match simplifyty ctx tyT with
          TyVariant(fieldtys) ->
            (try
               let tyTiExpected = List.assoc li fieldtys in
               let tyTi = typeof ctx ti in
               if subtype ctx tyTi tyTiExpected
                 then tyT
                 else error fi "field does not have expected type"
             with Not_found -> error fi ("label "^li^" not found"))
        | _ -> error fi "Annotation is not a variant type")
  | TmAscribe(fi,t1,tyT) ->
     if subtype ctx (typeof ctx t1) tyT then
       tyT
     else
       error fi "body of as-term does not have the expected type"
  | TmString _ -> TyString
  | TmUnit(fi) -> TyUnit
  | TmRef(fi,t1) ->
      TyRef(typeof ctx t1)
  | TmLoc(fi,l) ->
      error fi "locations are not supposed to occur in source programs!"
  | TmDeref(fi,t1) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRef(tyT1) -> tyT1
        | TyBot -> TyBot
        | TySource(tyT1) -> tyT1
        | _ -> error fi "argument of ! is not a Ref or Source")
  | TmAssign(fi,t1,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyRef(tyT1) ->
            if subtype ctx (typeof ctx t2) tyT1 then
              TyUnit
            else
              error fi "arguments of := are incompatible"
        | TyBot -> let _ = typeof ctx t2 in TyBot
        |TySink(tyT1) ->
            if subtype ctx (typeof ctx t2) tyT1 then
              TyUnit
            else
              error fi "arguments of := are incompatible"
        | _ -> error fi "argument of ! is not a Ref or Sink")
  | TmFloat _ -> TyFloat
  | TmTimesfloat(fi,t1,t2) ->
      if subtype ctx (typeof ctx t1) TyFloat
      && subtype ctx (typeof ctx t2) TyFloat then TyFloat
      else error fi "argument of timesfloat is not a number"
  | TmZero(fi) ->
      TyNat
  | TmSucc(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of succ is not a number"
  | TmPred(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyNat
      else error fi "argument of pred is not a number"
  | TmIsZero(fi,t1) ->
      if subtype ctx (typeof ctx t1) TyNat then TyBool
      else error fi "argument of iszero is not a number"

  (* New typing rules *)
  | TmFrac(_,_,_,_,_) -> TyFrac
  | TmDenormal(_,_) -> TyFrac
  | TmAdd(fi,t1,t2,_) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      let isrange ty = (tyeqv ctx ty TyRange) in
      if (isrange ty1) && (isrange ty2) then TyRange
      else error fi "argument of an operator is not a range"
  | TmSub(fi,t1,t2,_) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      let isrange ty = (tyeqv ctx ty TyRange) in
      if (isrange ty1) && (isrange ty2) then TyRange
      else error fi "argument of an operator is not a range"
  | TmMul(fi,t1,t2,_) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      let isrange ty = (tyeqv ctx ty TyRange) in
      if (isrange ty1) && (isrange ty2) then TyRange
      else error fi "argument of an operator is not a range"
  | TmDiv(fi,t1,t2,_) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      let isrange ty = (tyeqv ctx ty TyRange) in
      if (isrange ty1) && (isrange ty2) then TyRange
      else error fi "argument of an operator is not a range"
  | TmInv(fi,t1,_) ->
      let ty1 = typeof ctx t1 in
      let isrange ty = (tyeqv ctx ty TyRange) in
      if (isrange ty1) then TyRange
      else error fi "argument of an operator is not a range"
  | TmRange(fi, t1, t2, t3) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      let ty3 = typeof ctx t3 in 
      let isrange ty = (tyeqv ctx ty TyRange) || (tyeqv ctx ty TyUnit) in
      if (tyeqv ctx ty1 TyFrac) && (tyeqv ctx ty2 TyFrac) && (isrange ty3) then TyRange
      else error fi "argument of range is invalid"
   | TmSetprecision(fi, t1, _) ->
      let ty1 = typeof ctx t1 in
      if (tyeqv ctx ty1 TyRange) then TyRange
      else error fi "argument of setprecision is not a range"
   | TmRound(fi, t1, _) ->
      let ty1 = typeof ctx t1 in 
      if (tyeqv ctx ty1 TyRange) then TyFrac
      else error fi "argument of round is invalid"
   | TmUp(fi, t1, _) ->
      let ty1 = typeof ctx t1 in
      if (tyeqv ctx ty1 TyRange) then TyFrac
      else error fi "argument of up is not a range"
   | TmDown(fi, t1, _) ->
      let ty1 = typeof ctx t1 in
      if (tyeqv ctx ty1 TyRange) then TyFrac
      else error fi "argument of down is not a range"
   | TmLess(fi, t1, t2) ->
      let ty1 = typeof ctx t1 in
      let ty2 = typeof ctx t2 in
      if (tyeqv ctx ty1 TyFrac) && (tyeqv ctx ty2 TyFrac) then TyBool
      else error fi "argument of less is not a frac"


