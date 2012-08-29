(* module Core

   Core typechecking and evaluation functions
*)

open Syntax
open Support.Error

(* static aspects *)
val weavety : context -> (string * (ty -> ty)) list -> ty -> ty
val weavetm : context -> (string * (term -> term)) list -> (string * (ty -> ty)) list -> term -> term

val typeof : context -> term -> ty
val subtype : context -> ty -> ty -> bool
val tyeqv : context -> ty -> ty -> bool
val simplifyty : context -> ty -> ty
type store
val emptystore : store
val shiftstore : int -> store -> store 
val eval : context -> store -> term -> term * store
val evalbinding : context -> store -> binding -> binding * store
