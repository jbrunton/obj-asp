(* module Syntax: syntax trees and associated support functions *)

open Support.Pervasive
open Support.Error

(* Data type definitions *)
type ty =
    TyVar of int * int
  | TyTop
  | TyBot
  | TyId of string
  | TyArr of ty * ty
  | TyRef of ty
  | TyBool
  | TyUnit
  | TySource of ty
  | TySink of ty
  | TyNat

  | TyObject of (string * ty) list
  | TyMethod of ty
  | TyPair of ty * ty
  | TyAsp of ty
  | TyLab of ty

  | StTyJoin of string * ty

type term =
    TmVar of info * int * int
  | TmAbs of info * string * ty * term
  | TmApp of info * term * term
  | TmTrue of info
  | TmFalse of info
  | TmIf of info * term * term * term
  | TmLet of info * string * term * term
  | TmFix of info * term
  | TmAscribe of info * term * ty
  | TmUnit of info
  | TmLoc of info * int
  | TmRef of info * term
  | TmDeref of info * term 
  | TmAssign of info * term * term
  | TmZero of info
  | TmSucc of info * term
  | TmPred of info * term
  | TmIsZero of info * term
  | TmInert of info * ty

  | TmObject of info * (string * term) list
  | TmProj of info * term * string
  | TmMethod of info * string * ty * term
  | TmObjUpdate of info * term * string * string * ty * term

  | TmPair of info * term * term
  | TmFst of info * term
  | TmSnd of info * term

  | TmNewLab of info * ty
  | TmAsp of info * term * string * term
  | TmJoin of info * term * term
  | TmInstall of info * term * term

  | StAsp of info * string * term
  | StTyAsp of info * string * term
  | StObjAdv of info * string * (string * term) list * term
  | StObjTyAdv of info * string * (string * ty) list * term
  | StJoin of info * string * term

type binding =
    NameBind 
  | TyVarBind
  | VarBind of ty
  | TmAbbBind of term * (ty option)
  | TyAbbBind of ty

type command =
  | Eval of info * term
  | Bind of info * string * binding

(* Contexts *)
type context
val emptycontext : context 
val ctxlength : context -> int
val addbinding : context -> string -> binding -> context
val addname: context -> string -> context
val index2name : info -> context -> int -> string
val getbinding : info -> context -> int -> binding
val name2index : info -> context -> string -> int
val isnamebound : context -> string -> bool
val getTypeFromContext : info -> context -> int -> ty

(* Shifting and substitution *)
val termShift: int -> term -> term
val termSubstTop: term -> term -> term
val typeShift : int -> ty -> ty
val typeSubstTop: ty -> ty -> ty
val tytermSubstTop: ty -> term -> term

(* Printing *)
val printtm: context -> term -> unit
val printtm_ATerm: bool -> context -> term -> unit
val printty : context -> ty -> unit
val prbinding : context -> binding -> unit

(* Misc *)
val tmInfo: term -> info

