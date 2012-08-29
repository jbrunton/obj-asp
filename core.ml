open Format
open Syntax
open Support.Error
open Support.Pervasive

exception NoRuleApplies
exception ObjectExpected


(* Helper functions *)

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

let merge_members xs ys =
  let f xs (l_y,t_y) =
    if List.exists (fun (l_x,_) -> l_x = l_y) xs then
      xs
    else
      xs @ [l_y,t_y]
  in List.fold_left f xs ys


(* weaving functions for static aspects *)

exception AspectNotDefined

let rec delta_lookup sigma x = match sigma with
    [] -> raise AspectNotDefined
  | (a,f)::delta ->
      if x = a then f
      else delta_lookup delta x

let delta_upd delta x f =
  let rec g xs ys = match ys with 
      [] -> raise AspectNotDefined
    | (a,f')::ys ->
        if x = a then
          xs @ [(x,f)] @ ys
        else
          g (xs @ [(a,f')]) ys
  in
    g [] delta

let f_compose f1 f2 = fun t -> f1 (f2 t)

let f_id = fun t -> t

let f_X x_M = fun t -> (match t with
    TmObject(fi,y_M) -> TmObject(fi,merge_members x_M y_M)
  | _ -> error (tmInfo t) "Object term expected")

let f_XT x_MT = fun tyT -> (match tyT with
    TyObject(y_MT) -> TyObject(merge_members x_MT y_MT)
  | _ -> error dummyinfo "Object type expected")

let rec weavety ctx delta_ty tyT =
  let w = weavety ctx delta_ty in
  match (simplifyty ctx tyT) with
    StTyJoin(a,tyT1) -> weavety ctx delta_ty ((delta_lookup delta_ty a) tyT1)
  | _ -> tyT

let rec weavetm ctx delta_t delta_ty t =
  let w = weavetm ctx delta_t delta_ty in
  let wty = weavety ctx delta_ty in
  match t with
    StAsp(fi,a,t1) -> weavetm ctx ((a,f_id)::delta_t) delta_ty t1
  | StTyAsp(fi,a,t1) -> weavetm ctx delta_t ((a,f_id)::delta_ty) t1
  | StObjAdv(fi,a,m_X,t1) ->
      let f = delta_lookup delta_t a in
      let delta_t' = delta_upd delta_t a (f_compose (f_X m_X) f) in
      weavetm ctx delta_t' delta_ty t1
  | StObjTyAdv(fi,a,m_XT,t1) ->
      let f = delta_lookup delta_ty a in
      let delta_ty' = delta_upd delta_ty a (f_compose (f_XT m_XT) f) in
      weavetm ctx delta_t delta_ty' t1
  | StJoin(fi,a,t1) -> weavetm ctx delta_t delta_ty ((delta_lookup delta_t a) t1)

  | TmAbs(fi,x,tyT1,t2) -> TmAbs(fi,x,wty tyT1,w t2)
  | TmLet(fi,x,t1,t2) -> TmLet(fi,x,w t1,w t2)
(*  | TmNew(fi,t1) -> TmNew(fi,w t1)*)

  | _ -> t

(* ------------------------   EVALUATION  ------------------------ *)

let ismethod t = match t with
    TmMethod(_,_,_,_) -> true
  | _ -> false

let rec isnumericval ctx t = match t with
    TmZero(_) -> true
  | TmSucc(_,t1) -> isnumericval ctx t1
  | _ -> false

let rec isval ctx t = match t with
    TmTrue(_)  -> true
  | TmFalse(_) -> true
  | TmUnit(_)  -> true
  | TmLoc(_,_) -> true
  | t when isnumericval ctx t  -> true
  | TmAbs(_,_,_,_) -> true
  | TmObject(_,members) -> List.for_all (fun (l,ti) -> isval ctx ti) members
  | TmPair(_,t1,t2) -> isval ctx t1 && isval ctx t2
  | TmMethod(_,_,_,_) -> true
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

let merge_members xs ys =
  let f xs (l_y,t_y) =
    if List.exists (fun (l_x,_) -> l_x = l_y) xs then
      xs
    else
      xs @ [l_y,t_y]
  in List.fold_left f xs ys

let mkid ctx tyT = TmAbs(dummyinfo,"x",tyT,TmVar(dummyinfo,0,ctxlength ctx + 1))

(*let newref ctx x tyT1 t1 t2 = TmAbs(dummyinfo,x,*)

(*let countFields ctx members =
  match members with
      [] -> 0
    | (l,t)::members -> if ismethod t then 0 else 1 + countFields ctx members*)

let rec trty tyT =
  match tyT with
    TyArr(tyT1,tyT2) -> TyArr(trty tyT1,trty tyT2)
  | TyMethod(tyT2) ->
      TyMethod(trty tyT2)
  | TyRef(tyT1) -> TyRef(trty tyT1)
  | TySource(tyT1) -> TySource(trty tyT1)
  | TySink(tyT1) -> TySink(trty tyT1)
  | TyPair(tyT1,tyT2) -> TyPair(trty tyT1, trty tyT2)
  | TyLab(tyT1) -> TyRef(trty(TyArr(tyT1,tyT1)))
  | TyAsp(tyT1) -> TyPair(trty(TyLab(tyT1)),trty(TyArr(tyT1,tyT1)))
  | _ -> tyT

and trtm ctx t = match t with
    TmAbs(fi,x,tyT1,t2) -> TmAbs(fi,x,trty tyT1,trtm (addname ctx x) t2)
  | TmMethod(fi,x,tyT1,t1) -> TmMethod(fi,x,trty tyT1,trtm ctx t1)
  | TmApp(fi,t1,t2) -> TmApp(fi,trtm ctx t1,trtm ctx t2)
  | TmIf(fi,t1,t2,t3) -> TmIf(fi,trtm ctx t1,trtm ctx t2,trtm ctx t3)
  | TmLet(fi,x,t1,t2) -> TmLet(fi,x,trtm ctx t1,trtm ctx t2)
  | TmFix(fi,t1) -> TmFix(fi,trtm ctx t1)
  | TmProj(fi,t1,l) -> TmProj(fi,trtm ctx t1,l)
  | TmAscribe(fi,t1,tyT1) -> TmAscribe(fi,trtm ctx t1,trty tyT1)
  | TmRef(fi,t1) -> TmRef(fi,trtm ctx t1)
  | TmDeref(fi,t1) -> TmDeref(fi,trtm ctx t1) 
  | TmAssign(fi,t1,t2) -> TmAssign(fi,trtm ctx t1,trtm ctx t2)
  | TmSucc(fi,t1) -> TmSucc(fi,trtm ctx t1)
  | TmPred(fi,t1) -> TmPred(fi,trtm ctx t1)
  | TmIsZero(fi,t1) -> TmIsZero(fi,trtm ctx t1)
  | TmInert(fi,tyT1) -> TmInert(fi,trty tyT1)
  | TmPair(fi,t1,t2) -> TmPair(fi,trtm ctx t1,trtm ctx t2)
  | TmFst(fi,t1) -> TmFst(fi,trtm ctx t1)
  | TmSnd(fi,t1) -> TmSnd(fi,trtm ctx t1)
  | TmNewLab(fi,tyT1) ->
      let n = ctxlength ctx in
      let t1 = TmRef(dummyinfo,mkid ctx (trty tyT1)) in
      let t21 = TmAbs(dummyinfo,"y",TyArr(tyT1,tyT1),
                  TmAssign(dummyinfo,TmVar(dummyinfo,1,n+2),
                    TmLet(dummyinfo,"w",TmDeref(dummyinfo,TmVar(dummyinfo,1,n+2)),
                    TmAbs(dummyinfo,"z",tyT1,TmApp(dummyinfo,TmVar(dummyinfo,2,n+4),TmApp(dummyinfo,TmVar(dummyinfo,1,n+4),TmVar(dummyinfo,0,n+4)))))
                  )) in
      let t22 = TmAbs(dummyinfo,"_",TyUnit,TmDeref(dummyinfo,TmVar(dummyinfo,1,n+2))) in
      TmLet(fi,"x",t1,TmPair(dummyinfo,t21,t22))
  | TmInstall(fi,t1,t2) ->
      let n = ctxlength ctx in
      let t22 = TmLet(fi,"a",
               trtm ctx t1,
               TmAssign(dummyinfo,TmFst(dummyinfo,TmVar(dummyinfo,0,n+2)),TmSnd(dummyinfo,TmVar(dummyinfo,0,n+2)))) in
      let t12 = trtm (addname ctx "_") (termShift 1 t2) in
      TmApp(dummyinfo,TmAbs(dummyinfo,"_",TyUnit,t12),t22)
  | TmAsp(fi,t1,x,t2) -> TmPair(fi,trtm ctx t1,TmAbs(dummyinfo,"x",TyTop,trtm (addname ctx "x") t2))
  | TmJoin(fi,t1,t2) -> TmApp(fi,TmDeref(dummyinfo,trtm ctx t1),trtm ctx t2)
  | _ -> t

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
  | TmObject(fi,fields) ->
      let rec evalafield l = match l with 
        [] -> raise NoRuleApplies
      | (l,vi)::rest when isval ctx vi -> 
          let rest',store' = evalafield rest in
          (l,vi)::rest', store'
      | (l,ti)::rest -> 
          let ti',store' = eval1 ctx store ti in
          (l, ti')::rest, store'
      in let fields',store' = evalafield fields in
      TmObject(fi, fields'), store'
  | TmProj(fi, (TmObject(_, members) as o1), l) when isval ctx o1 ->
      (try
        (match List.assoc l members with
            TmMethod(_,_,_,t1) -> termSubstTop o1 t1, store
          | t -> t,store)
       with Not_found -> raise NoRuleApplies)
  | TmProj(fi, t1, l) ->
      let t1',store' = eval1 ctx store t1 in
      TmProj(fi, t1', l), store'
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
          | TmPair(_,v1,v2) -> TmApp(dummyinfo,v2,TmUnit(dummyinfo)),store
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
          | TmPair(_,v1,v2) -> TmApp(dummyinfo, v1, t2),store
          | _ -> raise NoRuleApplies)
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

  | TmObjUpdate(fi,TmObject(_,members),l,x,tyT2,t2) ->
      TmObject(fi,merge_members [l,TmMethod(dummyinfo,x,tyT2,t2)] members),store
  | TmObjUpdate(fi,t1,l,x,tyT2,t2) ->
      let t1',store' = eval1 ctx store t1 in
      TmObjUpdate(fi,t1',l,x,tyT2,t2),store'

  | TmPair(fi,v1,t2) when isval ctx v1 ->
      let t2',store' = eval1 ctx store t2 in
      TmPair(fi,v1,t2'),store'
  | TmPair(fi,t1,t2) ->
      let t1',store' = eval1 ctx store t1 in
      TmPair(fi,t1',t2),store'
  | TmFst(fi,TmPair(_,t11,t12)) ->
      t11,store
  | TmFst(fi,t1) ->
      let t1',store' = eval1 ctx store t1 in
      TmFst(fi,t1'),store'
  | TmSnd(fi,TmPair(_,t11,t12)) ->
      t12,store
  | TmSnd(fi,t1) ->
      let t1',store' = eval1 ctx store t1 in
      TmSnd(fi,t1'),store'
  | TmNewLab(_,_) as t -> trtm ctx t,store
  | TmJoin(_,_,_) as t -> trtm ctx t,store
  | TmInstall(_,_,_) as t -> trtm ctx t,store
  | TmAsp(_,_,_,_) as t -> trtm ctx t,store
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

let rec tyeqv ctx tyS tyT =
  let tyS = simplifyty ctx tyS in
  let tyT = simplifyty ctx tyT in
  match (tyS,tyT) with
    (TyTop,TyTop) -> true
  | (TyBot,TyBot) -> true
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
       (tyeqv ctx tyS1 tyT1) && (tyeqv ctx tyS2 tyT2)
  | (TyId(b1),TyId(b2)) -> b1=b2
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
  | (TyObject(members1),TyObject(members2)) -> 
       List.length members1 = List.length members2
       &&                                         
       List.for_all 
         (fun (li2,tyTi2) ->
            try let (tyTi1) = List.assoc li2 members1 in
                tyeqv ctx tyTi1 tyTi2
            with Not_found -> false)
         members2
  | (TyMethod(tyT1),TyMethod(tyT2)) ->
    tyeqv ctx tyT1 tyT2
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
   | (TyMethod(fS), TyMethod(fT)) ->
       (subtype ctx tyS tyT)
   | (TyObject(fS), TyObject(fT)) ->
       List.for_all
         (fun (li,tyTi) -> 
            try let tySi = List.assoc li fS in
                tyeqv ctx tySi tyTi
            with Not_found -> false)
         fT
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
    (TyObject(fS), TyObject(fT)) ->
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
      TyObject(commonFields)
  | (TyArr(tyS1,tyS2),TyArr(tyT1,tyT2)) ->
      TyArr(meet ctx  tyS1 tyT1, join ctx tyS2 tyT2)
  | (TyRef(tyT1),TyRef(tyT2)) ->
      if subtype ctx tyT1 tyT2 && subtype ctx tyT2 tyT1 
        then TyRef(tyT1)
        else TySource(join ctx tyT1 tyT2)
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
    (TyObject(fS), TyObject(fT)) ->
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
      TyObject(allFields)
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

let rec sigma ctx t = match t with
    TmMethod(_,_,tyT1,_) -> TyMethod(tyT1)
  | _ -> typeof ctx t

and phi ctx selfty t = match t with
    TmMethod(_,x,tyT1,t1) ->
      let ctx = addbinding ctx x (VarBind(selfty)) in
      subtype ctx (typeof ctx t1) tyT1
  | _ -> true

and typeof ctx t =
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
  | TmProj(fi, t1, l) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyObject(membertys) ->
            (try
              (match List.assoc l membertys with
                  TyMethod(tyT1) -> tyT1
                | tyT1 -> tyT1) 
             with Not_found -> error fi ("label "^l^" not found"))
        | TyBot -> TyBot
        | _ -> error fi "Expected object type")
  | TmFix(fi, t1) ->
      let tyT1 = typeof ctx t1 in
      (match simplifyty ctx tyT1 with
           TyArr(tyT11,tyT12) ->
             if subtype ctx tyT12 tyT11 then tyT12
             else error fi "result of body not compatible with domain"
         | TyBot -> TyBot
         | _ -> error fi "arrow type expected")
  | TmAscribe(fi,t1,tyT) ->
     if subtype ctx (typeof ctx t1) tyT then
       tyT
     else
       error fi "body of as-term does not have the expected type"
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

  | TmObject(fi,members) ->
      let x_T = List.map (fun (li,ti) -> (li,sigma ctx ti)) members in
      let selfty = TyObject(x_T) in
      if List.for_all (fun (li,ti) -> phi ctx selfty ti) members then
        selfty
      else
        error fi "ill-formed object"
  | TmObjUpdate(fi,t1,l,x,tyT2,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyObject(membertys) ->
            if (try tyeqv ctx (List.assoc l membertys) (TyMethod(tyT2))
              with Not_found -> error fi ("label "^l^" not found"))
            then TyObject(membertys)
            else error fi "invalid update operation"
        | TyBot -> TyBot
        | _ -> error fi "Expected object type")
  
  | TmPair(fi,t1,t2) ->
      TyPair(typeof ctx t1,typeof ctx t2)
  | TmFst(fi,t1) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyPair(tyT1,tyT2) -> tyT1
        | _ -> error fi "argument of fst must be a Pair")
  | TmSnd(fi,t1) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyPair(tyT1,tyT2) -> tyT2
        | _ -> error fi "argument of fst must be a Pair")

  | TmNewLab(fi,tyT1) ->
      TyLab(tyT1)
  | TmAsp(fi,t1,x,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyLab(tyT1) ->
            let ctx' = addbinding ctx x (VarBind(tyT1)) in
            let tyT2 = simplifyty ctx' (typeof ctx' t2) in
            if subtype ctx tyT2 tyT1 then TyAsp(tyT1)
            else error fi "mismatched types of terms in aspect"
        | _ -> error fi "first term of aspect must be a label")
  | TmJoin(fi,t1,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyLab(tyT1) ->
            if tyeqv ctx (typeof ctx t2) tyT1 then tyT1
            else error fi "mismatched types in aspect invocation"
        | _ -> error fi "first term in aspect invocation must be of type Lab")
  | TmInstall(fi,t1,t2) ->
      (match simplifyty ctx (typeof ctx t1) with
          TyAsp(tyT1) ->
            if tyeqv ctx (typeof ctx t2) tyT1 then tyT1
            else error fi "mismatched types in aspect installation"
        | _ -> error fi "first term in aspect invocation must be of type Asp")
