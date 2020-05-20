(*  Title:      nominal_basics.ML
    Author:     Christian Urban
    Author:     Tjark Weber

  Basic functions for nominal.
*)

infix 1 ||>>> |>>>

signature NOMINAL_BASIC =
sig
  val trace: bool Unsynchronized.ref
  val trace_msg: (unit -> string) -> unit

  val |>>> : 'a * ('a -> 'b * 'c) -> 'b list * 'c
  val ||>>> : ('a list * 'b) * ('b -> 'a * 'b) -> 'a list * 'b

  val last2: 'a list -> 'a * 'a
  val split_triples: ('a * 'b * 'c) list -> ('a list * 'b list * 'c list)
  val split_last2: 'a list -> 'a list * 'a * 'a
  val order: ('a * 'a -> bool) -> 'a list -> ('a * 'b) list -> 'b list
  val order_default: ('a * 'a -> bool) -> 'b -> 'a list -> ('a * 'b) list -> 'b list
  val remove_dups: ('a * 'a -> bool) -> 'a list -> 'a list
  val map4: ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val split_filter: ('a -> bool) -> 'a list -> 'a list * 'a list
  val fold_left: ('a * 'a -> 'a) -> 'a list -> 'a -> 'a

  val is_true: term -> bool

  val dest_listT: typ -> typ
  val dest_fsetT: typ -> typ

  val mk_id: term -> term
  val mk_all: (string * typ) -> term -> term
  val mk_All: (string * typ) -> term -> term
  val mk_exists: (string * typ) -> term -> term

  val case_sum_const: typ -> typ -> typ -> term
  val mk_case_sum: term -> term -> term

  val mk_equiv: thm -> thm
  val safe_mk_equiv: thm -> thm

  val mk_minus: term -> term
  val mk_plus: term -> term -> term

  val perm_ty: typ -> typ
  val perm_const: typ -> term
  val mk_perm_ty: typ -> term -> term -> term
  val mk_perm: term -> term -> term
  val dest_perm: term -> term * term

  (* functions to deal with constants in local contexts *)
  val long_name: Proof.context -> string -> string
  val is_fixed: Proof.context -> term -> bool
  val fixed_nonfixed_args: Proof.context -> term -> term * term list
end


structure Nominal_Basic: NOMINAL_BASIC =
struct

val trace = Unsynchronized.ref false
fun trace_msg msg = if ! trace then tracing (msg ()) else ()


infix 1 ||>>> |>>>

fun (x |>>> f) =
  let
    val (x', y') = f x
  in
    ([x'], y')
  end

fun (([], y) ||>>> f) = ([], y)
  | ((xs, y) ||>>> f) =
       let
         val (x', y') = f y
       in
         (xs @ [x'], y')
       end


(* orders an AList according to keys - every key needs to be there *)
fun order eq keys list =
  map (the o AList.lookup eq list) keys

(* orders an AList according to keys - returns default for non-existing keys *)
fun order_default eq default keys list =
  map (the_default default o AList.lookup eq list) keys

(* remove duplicates *)
fun remove_dups eq [] = []
  | remove_dups eq (x :: xs) =
      if member eq xs x
      then remove_dups eq xs
      else x :: remove_dups eq xs

fun split_triples xs =
  fold (fn (a, b, c) => fn (axs, bxs, cxs) => (a :: axs, b :: bxs, c :: cxs)) xs ([], [], [])

fun last2 [] = raise Empty
  | last2 [_] = raise Empty
  | last2 [x, y] = (x, y)
  | last2 (_ :: xs) = last2 xs

fun split_last2 xs =
  let
    val (xs', x) = split_last xs
    val (xs'', y) = split_last xs'
  in
    (xs'', y, x)
  end

fun map4 _ [] [] [] [] = []
  | map4 f (x :: xs) (y :: ys) (z :: zs) (u :: us) = f x y z u :: map4 f xs ys zs us

fun split_filter f [] = ([], [])
  | split_filter f (x :: xs) =
      let
        val (r, l) = split_filter f xs
      in
        if f x
        then (x :: r, l)
        else (r, x :: l)
      end

(* to be used with left-infix binop-operations *)
fun fold_left f [] z = z
  | fold_left f [x] z = x
  | fold_left f (x :: y :: xs) z = fold_left f (f (x, y) :: xs) z

fun is_true @{term "Trueprop True"} = true
  | is_true _ = false

fun dest_listT (Type (@{type_name list}, [T])) = T
  | dest_listT T = raise TYPE ("dest_listT: list type expected", [T], [])

fun dest_fsetT (Type (@{type_name fset}, [T])) = T
  | dest_fsetT T = raise TYPE ("dest_fsetT: fset type expected", [T], [])

fun mk_id trm = HOLogic.id_const (fastype_of trm) $ trm

fun mk_all (a, T) t =  Logic.all_const T $ Abs (a, T, t)

fun mk_All (a, T) t =  HOLogic.all_const T $ Abs (a, T, t)

fun mk_exists (a, T) t =  HOLogic.exists_const T $ Abs (a, T, t)

fun case_sum_const ty1 ty2 ty3 =
  Const (@{const_name case_sum}, [ty1 --> ty3, ty2 --> ty3, Type (@{type_name sum}, [ty1, ty2])] ---> ty3)

fun mk_case_sum trm1 trm2 =
  let
    val ([ty1], ty3) = strip_type (fastype_of trm1)
    val ty2 = domain_type (fastype_of trm2)
  in
    case_sum_const ty1 ty2 ty3 $ trm1 $ trm2
  end

fun mk_equiv r = r RS @{thm eq_reflection}
fun safe_mk_equiv r = mk_equiv r handle Thm.THM _ => r

fun mk_minus p = @{term "uminus::perm => perm"} $ p

fun mk_plus p q = @{term "plus::perm => perm => perm"} $ p $ q

fun perm_ty ty = @{typ "perm"} --> ty --> ty
fun perm_const ty  = Const (@{const_name "permute"}, perm_ty ty)
fun mk_perm_ty ty p trm = perm_const ty $ p $ trm
fun mk_perm p trm = mk_perm_ty (fastype_of trm) p trm

fun dest_perm (Const (@{const_name "permute"}, _) $ p $ t) = (p, t)
  | dest_perm t = raise TERM ("dest_perm", [t])


(** functions to deal with constants in local contexts **)

(* returns the fully qualified name of a constant *)
fun long_name ctxt name =
  case head_of (Syntax.read_term ctxt name) of
    Const (s, _) => s
  | _ => error ("Undeclared constant: " ^ quote name)

(* returns true iff the argument term is a fixed Free *)
fun is_fixed_Free ctxt (Free (s, _)) = Variable.is_fixed ctxt s
  | is_fixed_Free _ _ = false

(* returns true iff c is a constant or fixed Free applied to
   fixed parameters *)
fun is_fixed ctxt c =
  let
    val (c, args) = strip_comb c
  in
    (is_Const c orelse is_fixed_Free ctxt c)
      andalso List.all (is_fixed_Free ctxt) args
  end

(* splits a list into the longest prefix containing only elements
   that satisfy p, and the rest of the list *)
fun chop_while p =
  let
    fun chop_while_aux acc [] =
      (rev acc, [])
      | chop_while_aux acc (x::xs) =
      if p x then chop_while_aux (x::acc) xs else (rev acc, x::xs)
  in
    chop_while_aux []
  end

(* takes a combination "c $ fixed1 $ ... $ fixedN $ not-fixed $ ..."
   to the pair ("c $ fixed1 $ ... $ fixedN", ["not-fixed", ...]). *)
fun fixed_nonfixed_args ctxt c_args =
  let
    val (c, args)     = strip_comb c_args
    val (frees, args) = chop_while (is_fixed_Free ctxt) args
    val c_frees       = list_comb (c, frees)
  in
    (c_frees, args)
  end

end (* structure *)

open Nominal_Basic;
