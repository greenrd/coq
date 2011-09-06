open Names
open Term
open Util

type 'a array' = int * 'a array

(* Zipper à la Elliott *)

type 'constr pexistential' = existential_key * 'constr array'
type ('constr, 'types) prec_declaration' =
  | PrecDec0 of name array * 'types array' * 'constr array
  | PrecDec1 of name array * 'types array * 'constr array'
type ('constr, 'types) pfixpoint =
    (int array * int) * ('constr, 'types) prec_declaration'
type ('constr, 'types) pcofixpoint =
    int * ('constr, 'types) prec_declaration'

type ('constr, 'types) kind_of_term' =
  | Evar0     of 'constr pexistential'
  | Cast0     of cast_kind * 'types
  | Cast1     of 'constr * cast_kind
  | Prod0     of bool * name * 'types
  | Lambda0   of name * 'constr
  | Lambda1   of name * 'types
  | LetIn0    of name * 'types * 'constr
  | LetIn1    of name * 'constr * 'constr
  | LetIn2    of name * 'constr * 'types
  | App0      of 'constr array
  | App1      of 'constr * 'constr array'
  | Case0     of bool * case_info * 'constr * 'constr array
  | Case1     of case_info * 'constr * 'constr * 'constr array'
  | Fix0      of ('constr, 'types) pfixpoint
  | CoFix0    of ('constr, 'types) pcofixpoint

type context = ((constr, types) kind_of_term') list

module type Binder = sig
  type t
  val add_bindings : int -> t -> t
  val remove_bindings : int -> t -> t
end

module EZipper : functor (B : Binder) -> sig
  type t = B.t
  type zipper = t * context * constr

  val up : zipper -> zipper option
  val down : zipper -> (zipper, zipper) kind_of_term
  val leftmost_child : zipper -> zipper option
  val left : zipper -> zipper option
  val left_rec : zipper -> (constr, zipper) union
  val right : zipper -> zipper option
  val right_rec : zipper -> (constr, zipper) union

  (* If first argument is true, tries leftmost_child and then right_rec.
     If it's false, tries rightmost_child and then left_rec.
  *)
  val dfs_step : bool -> zipper -> (constr, zipper) union
end

