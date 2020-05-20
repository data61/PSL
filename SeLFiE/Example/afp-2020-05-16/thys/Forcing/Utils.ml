signature Utils =
 sig
    val binop : term -> term -> term -> term
    val add_: term -> term -> term
    val app_: term -> term -> term
    val concat_: term -> term -> term
    val dest_apply: term -> term * term
    val dest_iff_lhs: term -> term
    val dest_iff_rhs: term -> term
    val dest_iff_tms: term -> term * term
    val dest_lhs_def: term -> term
    val dest_rhs_def: term -> term
    val dest_satisfies_tms: term -> term * term
    val dest_satisfies_frm: term -> term
    val dest_eq_tms: term -> term * term
    val dest_sats_frm: term -> (term * term) * term
    val dest_trueprop: term -> term
    val eq_: term -> term -> term
    val fix_vars: thm -> string list -> Proof.context -> thm
    val formula_: term
    val freeName: term -> string
    val inList: ''a -> ''a list -> bool
    val isFree: term -> bool
    val length_: term -> term
    val list_: term -> term
    val lt_: term -> term -> term
    val mem_: term -> term -> term
    val mk_FinSet: term list -> term
    val mk_Pair: term -> term -> term
    val mk_ZFlist: ('a -> term) -> 'a list -> term
    val mk_ZFnat: int -> term
    val nat_: term
    val nth_: term -> term -> term
    val subset_: term -> term -> term
    val thm_concl_tm :  Proof.context -> xstring -> 
        ((indexname * typ) * cterm) list * term * Proof.context
    val to_ML_list: term -> term list
    val tp: term -> term
  end

structure Utils : Utils =
struct 
(* Smart constructors for ZF-terms *)

fun inList a = exists (fn b => a = b)

fun binop h t u = h $ t $ u
val mk_Pair  = binop @{const Pair}

fun mk_FinSet nil = @{const zero}
  | mk_FinSet (e :: es) = @{const cons} $ e $ mk_FinSet es

fun mk_ZFnat 0 = @{const zero}
  | mk_ZFnat n = @{const succ} $ mk_ZFnat (n-1)

fun mk_ZFlist _ nil = @{const "Nil"}
  | mk_ZFlist f (t :: ts) = @{const "Cons"} $ f t $ mk_ZFlist f ts

fun to_ML_list (@{const Nil}) = nil
  | to_ML_list (@{const Cons} $ t $ ts) = t :: to_ML_list ts
|   to_ML_list _ = nil

fun isFree (Free (_,_)) = true
  | isFree _ = false

fun freeName (Free (n,_)) = n
  | freeName _ = error "Not a free variable"

val app_ = binop @{const apply}

fun tp x = @{const Trueprop} $ x
fun length_ env = @{const length} $ env
val nth_ = binop @{const nth}
val add_ = binop @{const add}
val mem_ = binop @{const mem}
val subset_ = binop @{const Subset}
val lt_ = binop @{const lt}
val concat_ = binop @{const app}
val eq_ = binop @{const IFOL.eq(i)}

(* Abbreviation for sets *)
fun list_ set = @{const list} $ set
val nat_ = @{const nat}
val formula_ = @{const formula}

(** Destructors of terms **)
fun dest_eq_tms (Const (@{const_name IFOL.eq},_) $ t $ u) = (t, u)
  | dest_eq_tms t = raise TERM ("dest_eq_tms", [t])

fun dest_lhs_def (Const (@{const_name Pure.eq},_) $ x $ _) = x
  | dest_lhs_def t = raise TERM ("dest_lhs_def", [t])

fun dest_rhs_def (Const (@{const_name Pure.eq},_) $ _ $ y) = y
  | dest_rhs_def t = raise TERM ("dest_rhs_def", [t])


fun dest_apply (@{const apply} $ t $ u) = (t,u)
  | dest_apply t = raise TERM ("dest_applies_op", [t])

fun dest_satisfies_tms (@{const Formula.satisfies} $ A $ f) = (A,f)
  | dest_satisfies_tms t = raise TERM ("dest_satisfies_tms", [t]);

val dest_satisfies_frm = #2 o dest_satisfies_tms

fun dest_sats_frm t = t |> dest_eq_tms |> #1 |> dest_apply |>> dest_satisfies_tms ;

fun dest_trueprop (@{const IFOL.Trueprop} $ t) = t
  | dest_trueprop t = t

fun dest_iff_tms (@{const IFOL.iff} $ t $ u) = (t, u)
  | dest_iff_tms t = raise TERM ("dest_iff_tms", [t])

val dest_iff_lhs = #1 o dest_iff_tms
val dest_iff_rhs = #2 o dest_iff_tms

fun thm_concl_tm ctxt thm_ref =
  let val (((_,vars),thm_tms),ctxt1) = Variable.import true [Proof_Context.get_thm ctxt thm_ref] ctxt
  in (vars, thm_tms |> hd |> Thm.concl_of, ctxt1)
end

fun fix_vars thm vars ctxt = let
  val (_, ctxt1) = Variable.add_fixes vars ctxt
  in singleton (Proof_Context.export ctxt1 ctxt) thm
end

end ;
