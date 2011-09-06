open Names
open Term
open Util

type 'a array' = int * 'a array

let fill_array ia x = match ia, x with
  | (i, a), x ->
    let a = Array.copy a
    in Array.set a i x; a

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

let fill_precdec f t = match f, t with
  | (ln, PrecDec0 (lna,a,bl)), t -> (ln,(lna, fill_array a t, bl))
  | (ln, PrecDec1 (lna,tl,a)), t -> (ln,(lna, tl, fill_array a t))

let fill c t = match c, t with
  | Evar0 (e, a), t -> mkEvar (e, fill_array a t)
  | Cast0 (k, t), c -> mkCast (c,k,t)
  | Cast1 (c, k), t -> mkCast (c,k,t)
  | Prod0 (false, na, c), t -> mkProd (na,t,c)
  | Prod0 (true , na, t), c -> mkProd (na,t,c)
  | Lambda0 (na, c), t -> mkLambda (na,t,c)
  | Lambda1 (na, t), c -> mkLambda (na,t,c)
  | LetIn0 (na, t, c), b -> mkLetIn (na,b,t,c)
  | LetIn1 (na, b, c), t -> mkLetIn (na,b,t,c)
  | LetIn2 (na, b, t), c -> mkLetIn (na,b,t,c)
  | App0 al, c -> mkApp (c, al)
  | App1 (c, a), t -> mkApp (c, fill_array a t)
  | Case0 (false, ci, c, bl), p -> mkCase (ci,p,c,bl)
  | Case0 (true,  ci, p, bl), c -> mkCase (ci,p,c,bl)
  | Case1 (ci, p, c, a), t -> mkCase (ci,p,c,fill_array a t)
  | Fix0 f, t -> mkFix (fill_precdec f t)
  | CoFix0 f, t -> mkCoFix (fill_precdec f t)

let nBindings = function
  | Prod0 (true, _, _)
  | Lambda1 _
  | LetIn2 _ -> 1
  | Fix0 (_, PrecDec1 (ln,_,_))
  | CoFix0 (_, PrecDec1 (ln,_,_)) -> Array.length ln
  | _ -> 0

let array_safe_get a i =
  if i >= Array.length a || i < 0 then None else Some a.(i)

module type Binder = sig
  type t
  val add_bindings : int -> t -> t
  val remove_bindings : int -> t -> t
end

module EZipper (B : Binder) = struct
  type t = B.t
  type zipper = t * context * constr
 
  let up = function
    | (_, [], _) -> None
    | (x, d::ds', t) -> Some (B.remove_bindings (nBindings d) x, ds', fill d t)

  let down = function
    | (x, ds, c) ->
      let g = B.add_bindings in
      let extract_array f a = Array.mapi (fun i y -> (x, f (i, a) :: ds, y)) a in
      let extract_precdec f = function
        | (ln,(lna,tl,bl)) -> (ln, (lna, extract_array (fun a -> f (ln,PrecDec0 (lna,a,bl))) tl,
                                    let l = Array.length lna in
                                    Array.mapi (fun i y -> (g l x, f (ln,PrecDec1 (lna,tl,(i,bl))) :: ds, y)) bl))
      in match kind_of_term c with
        | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
              | Construct _) -> Rel 0 (* dummy value *)
        | Cast (c,k,t) -> Cast ((x, Cast0 (k,t) :: ds, c),k,(x, Cast1 (c,k) :: ds, t))
        | Prod (na,t,c) -> Prod (na, (x, Prod0 (false,na,c) :: ds, t), (g 1 x, Prod0 (true,na,t) :: ds, c))
        | Lambda (na,t,c) -> Lambda (na, (x, Lambda0 (na,c) :: ds, t), (g 1 x, Lambda1 (na,t) :: ds, c))
        | LetIn (na,b,t,c) -> LetIn (na, (x, LetIn0 (na,t,c) :: ds, b), (x, LetIn1 (na,b,c) :: ds, t), (g 1 x, LetIn2 (na,b,t) :: ds, c))
        | App (c,al) -> App ((x, App0 al :: ds, c), extract_array (fun a -> App1 (c,a)) al)
        | Evar (e,al) -> Evar (e, extract_array (fun a -> Evar0 (e,a)) al)
        | Case (ci,p,c,bl) -> Case (ci, (x, Case0 (false,ci,c,bl) :: ds, p), (x, Case0 (true,ci,p,bl) :: ds, c), extract_array (fun a -> Case1 (ci,p,c,a)) bl)
        | Fix f -> Fix (extract_precdec (fun x -> Fix0 x) f)
        | CoFix f -> CoFix (extract_precdec (fun x -> CoFix0 x) f)

  let leftmost_child z = match down z with
    | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
              | Construct _) -> None
    | Cast (c,_,_) -> Some c
    | Prod (_,p,_) -> Some p
    | Lambda (_,t,_) -> Some t
    | LetIn (_,b,_,_) -> Some b
    | App (c,_) -> Some c
    | Case (_,p,_,_) -> Some p
    | Evar (_,al)
    | Fix (_,(_,al,_))
    | CoFix (_,(_,al,_)) -> Some (array_hd al)

  let rightmost_child z = match down z with
    | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
              | Construct _) -> None
    | Cast (_,_,c) -> Some c
    | Prod (_,_,p) -> Some p
    | Lambda (_,_,t) -> Some t
    | LetIn (_,_,_,b) -> Some b
    | Case (_,_,_,al)
    | App (_,al)
    | Evar (_,al)
    | Fix (_,(_,_,al))
    | CoFix (_,(_,_,al)) -> Some (array_last al)

  let xmost_child = function
    | false -> leftmost_child
    | true -> rightmost_child

  (* TODO: Implement! *)
  let left z = None

  let right z =
    let right' u = match z with
      | (_, d :: _, _) -> (match d, down u with
          | Cast0 _, Cast (_,_,t) -> Some t
          | Prod0 (false,_,_), Prod (_,_,c) -> Some c
          | Lambda0 _, Lambda (_,_,c) -> Some c
          | LetIn0 _, LetIn (_,_,t,_) -> Some t
          | LetIn1 _, LetIn (_,_,_,t) -> Some t
          | App0 _, App (_, al) -> Some (array_hd al)
          | App1 (_,(i,_)), App (_,al) -> array_safe_get al (i + 1)
          | Evar0 (_,(i,_)), Evar (_,al) -> array_safe_get al (i + 1)
          | Case0 (false,_,_,_), Case (_,_,c,_) -> Some c
          | Case0 (true,_,_,_), Case (_,_,_,al) -> Some (array_hd al)
          | Case1 (_,_,_,(i,_)), Case (_,_,_,al) -> array_safe_get al (i + 1)
          | Fix0 (_,PrecDec0 (_,(i,_),_)), Fix (_,(_,tl,bl)) -> (match array_safe_get tl (i + 1) with
              | None -> Some (array_hd bl)
              | c -> c)
          | Fix0 (_,PrecDec1 (_,_,(i,_))), Fix (_,(_,_,bl)) -> array_safe_get bl (i + 1)
          | CoFix0 (_,PrecDec0 (_,(i,_),_)), CoFix (_,(_,tl,bl)) -> (match array_safe_get tl (i + 1) with
              | None -> Some (array_hd bl)
              | c -> c)
          | CoFix0 (_,PrecDec1 (_,_,(i,_))), CoFix (_,(_,_,bl)) -> array_safe_get bl (i + 1)
          | _ -> None)
      | _ -> assert false
    in Option.cata right' None (up z)

  let move = function
    | true -> right
    | false -> left

  let move_rec is_right =
    let rec move_rec' z = match move is_right z with
      | Some r -> Inr r
      | None -> match up z with
          | Some u -> move_rec' u
          | None -> match z with
              (_,_,t) -> Inl t
    in move_rec'

  let left_rec = move_rec false
  let right_rec = move_rec true

  let dfs_step is_right z = 
    match xmost_child (not is_right) z with
      | None -> move_rec is_right z
      | Some c -> Inr c

end
