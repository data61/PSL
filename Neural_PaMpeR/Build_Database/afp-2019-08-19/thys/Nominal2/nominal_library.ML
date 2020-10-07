(*  Title:      nominal_library.ML
    Author:     Christian Urban

  Library functions for nominal.
*)

signature NOMINAL_LIBRARY =
sig
  val mk_sort_of: term -> term
  val atom_ty: typ -> typ
  val atom_const: typ -> term
  val mk_atom_ty: typ -> term -> term
  val mk_atom: term -> term

  val mk_atom_set_ty: typ -> term -> term
  val mk_atom_set: term -> term
  val mk_atom_fset_ty: typ -> term -> term
  val mk_atom_fset: term -> term
  val mk_atom_list_ty: typ -> term -> term
  val mk_atom_list: term -> term

  val is_atom: Proof.context -> typ -> bool
  val is_atom_set: Proof.context -> typ -> bool
  val is_atom_fset: Proof.context -> typ -> bool
  val is_atom_list: Proof.context -> typ -> bool

  val to_set_ty: typ -> term -> term
  val to_set: term -> term

  val atomify_ty: Proof.context -> typ -> term -> term
  val atomify: Proof.context -> term -> term
  val setify_ty: Proof.context -> typ -> term -> term
  val setify: Proof.context -> term -> term
  val listify_ty: Proof.context -> typ -> term -> term
  val listify: Proof.context -> term -> term

  val fresh_ty: typ -> typ
  val fresh_const: typ -> term
  val mk_fresh_ty: typ -> term -> term -> term
  val mk_fresh: term -> term -> term

  val fresh_star_ty: typ -> typ
  val fresh_star_const: typ -> term
  val mk_fresh_star_ty: typ -> term -> term -> term
  val mk_fresh_star: term -> term -> term

  val supp_ty: typ -> typ
  val supp_const: typ -> term
  val mk_supp_ty: typ -> term -> term
  val mk_supp: term -> term

  val supp_rel_ty: typ -> typ
  val supp_rel_const: typ -> term
  val mk_supp_rel_ty: typ -> term -> term -> term
  val mk_supp_rel: term -> term -> term

  val supports_const: typ -> term
  val mk_supports_ty: typ -> term -> term -> term
  val mk_supports: term -> term -> term

  val finite_const: typ -> term
  val mk_finite_ty: typ -> term -> term
  val mk_finite: term -> term

  val mk_diff: term * term -> term
  val mk_append: term * term -> term
  val mk_union: term * term -> term
  val fold_union: term list -> term
  val fold_append: term list -> term
  val mk_conj: term * term -> term
  val fold_conj: term list -> term
  val fold_conj_balanced: term list -> term

  (* functions for de-Bruijn open terms *)
  val mk_binop_env: typ list -> string -> term * term -> term
  val mk_union_env: typ list -> term * term -> term
  val fold_union_env: typ list -> term list -> term

  (* fresh arguments for a term *)
  val fresh_args: Proof.context -> term -> term list

  (* some logic operations *)
  val strip_full_horn: term -> (string * typ) list * term list * term
  val mk_full_horn: (string * typ) list -> term list -> term -> term

  (* datatype operations *)
  type cns_info = (term * typ * typ list * bool list) list

  val all_dtyp_constrs_types: Old_Datatype_Aux.descr -> cns_info list

  (* tactics for function package *)
  val size_ss: simpset
  val pat_completeness_simp: thm list -> Proof.context -> tactic
  val prove_termination_ind: Proof.context -> int -> tactic
  val prove_termination_fun: thm list -> Proof.context -> Function.info * local_theory

  (* transformations of premises in inductions *)
  val transform_prem1: Proof.context -> string list -> thm -> thm
  val transform_prem2: Proof.context -> string list -> thm -> thm

  (* transformation into the object logic *)
  val atomize: Proof.context -> thm -> thm
  val atomize_rule: Proof.context -> int -> thm -> thm
  val atomize_concl: Proof.context -> thm -> thm

  (* applies a tactic to a formula composed of conjunctions *)
  val conj_tac: Proof.context -> (int -> tactic) -> int -> tactic
end


structure Nominal_Library: NOMINAL_LIBRARY =
struct

fun mk_sort_of t = @{term "sort_of"} $ t;

fun atom_ty ty = ty --> @{typ "atom"};
fun atom_const ty = Const (@{const_name "atom"}, atom_ty ty)
fun mk_atom_ty ty t = atom_const ty $ t;
fun mk_atom t = mk_atom_ty (fastype_of t) t;

fun mk_atom_set_ty ty t =
  let
    val atom_ty = HOLogic.dest_setT ty
    val img_ty = (atom_ty --> @{typ atom}) --> ty --> @{typ "atom set"};
  in
    Const (@{const_name image}, img_ty) $ atom_const atom_ty $ t
  end

fun mk_atom_fset_ty ty t =
  let
    val atom_ty = dest_fsetT ty
    val fmap_ty = (atom_ty --> @{typ atom}) --> ty --> @{typ "atom fset"};
  in
    Const (@{const_name fimage}, fmap_ty) $ atom_const atom_ty $ t
  end

fun mk_atom_list_ty ty t =
  let
    val atom_ty = dest_listT ty
    val map_ty = (atom_ty --> @{typ atom}) --> ty --> @{typ "atom list"}
  in
    Const (@{const_name map}, map_ty) $ atom_const atom_ty $ t
  end

fun mk_atom_set t = mk_atom_set_ty (fastype_of t) t
fun mk_atom_fset t = mk_atom_fset_ty (fastype_of t) t
fun mk_atom_list t = mk_atom_list_ty (fastype_of t) t

(* coerces a list into a set *)

fun to_set_ty ty t =
  case ty of
    @{typ "atom list"} => @{term "set :: atom list => atom set"} $ t
  | @{typ "atom fset"} => @{term "fset :: atom fset => atom set"} $ t
  | _ => t

fun to_set t = to_set_ty (fastype_of t) t


(* testing for concrete atom types *)
fun is_atom ctxt ty =
  Sign.of_sort (Proof_Context.theory_of ctxt) (ty, @{sort at_base})

fun is_atom_set ctxt (Type ("fun", [ty, @{typ bool}])) = is_atom ctxt ty
  | is_atom_set _ _ = false;

fun is_atom_fset ctxt (Type (@{type_name "fset"}, [ty])) = is_atom ctxt ty
  | is_atom_fset _ _ = false;

fun is_atom_list ctxt (Type (@{type_name "list"}, [ty])) = is_atom ctxt ty
  | is_atom_list _ _ = false


(* functions that coerce singletons, sets, fsets and lists of concrete
   atoms into general atoms sets / lists *)
fun atomify_ty ctxt ty t =
  if is_atom ctxt ty
    then  mk_atom_ty ty t
  else if is_atom_set ctxt ty
    then mk_atom_set_ty ty t
  else if is_atom_fset ctxt ty
    then mk_atom_fset_ty ty t
  else if is_atom_list ctxt ty
    then mk_atom_list_ty ty t
  else raise TERM ("atomify: term is not an atom, set or list of atoms", [t])

fun setify_ty ctxt ty t =
  if is_atom ctxt ty
    then HOLogic.mk_set @{typ atom} [mk_atom_ty ty t]
  else if is_atom_set ctxt ty
    then mk_atom_set_ty ty t
  else if is_atom_fset ctxt ty
    then @{term "fset :: atom fset => atom set"} $ mk_atom_fset_ty ty t
  else if is_atom_list ctxt ty
    then @{term "set :: atom list => atom set"} $ mk_atom_list_ty ty t
  else raise TERM ("setify: term is not an atom, set or list of atoms", [t])

fun listify_ty ctxt ty t =
  if is_atom ctxt ty
    then HOLogic.mk_list @{typ atom} [mk_atom_ty ty t]
  else if is_atom_list ctxt ty
    then mk_atom_list_ty ty t
  else raise TERM ("listify: term is not an atom or list of atoms", [t])

fun atomify ctxt t = atomify_ty ctxt (fastype_of t) t
fun setify ctxt t  = setify_ty ctxt (fastype_of t) t
fun listify ctxt t = listify_ty ctxt (fastype_of t) t

fun fresh_ty ty = [@{typ atom}, ty] ---> @{typ bool}
fun fresh_const ty = Const (@{const_name fresh}, fresh_ty ty)
fun mk_fresh_ty ty t1 t2 = fresh_const ty $ t1 $ t2
fun mk_fresh t1 t2 = mk_fresh_ty (fastype_of t2) t1 t2

fun fresh_star_ty ty = [@{typ "atom set"}, ty] ---> @{typ bool}
fun fresh_star_const ty = Const (@{const_name fresh_star}, fresh_star_ty ty)
fun mk_fresh_star_ty ty t1 t2 = fresh_star_const ty $ t1 $ t2
fun mk_fresh_star t1 t2 = mk_fresh_star_ty (fastype_of t2) t1 t2

fun supp_ty ty = ty --> @{typ "atom set"};
fun supp_const ty = Const (@{const_name supp}, supp_ty ty)
fun mk_supp_ty ty t = supp_const ty $ t
fun mk_supp t = mk_supp_ty (fastype_of t) t

fun supp_rel_ty ty = ([ty, ty] ---> @{typ bool}) --> ty --> @{typ "atom set"};
fun supp_rel_const ty = Const (@{const_name supp_rel}, supp_rel_ty ty)
fun mk_supp_rel_ty ty r t = supp_rel_const ty $ r $ t
fun mk_supp_rel r t = mk_supp_rel_ty (fastype_of t) r t

fun supports_const ty = Const (@{const_name supports}, [@{typ "atom set"}, ty] ---> @{typ bool});
fun mk_supports_ty ty t1 t2 = supports_const ty $ t1 $ t2;
fun mk_supports t1 t2 = mk_supports_ty (fastype_of t2) t1 t2;

fun finite_const ty = Const (@{const_name finite}, ty --> @{typ bool})
fun mk_finite_ty ty t = finite_const ty $ t
fun mk_finite t = mk_finite_ty (fastype_of t) t


(* functions that construct differences, appends and unions
   but avoid producing empty atom sets or empty atom lists *)

fun mk_diff (@{term "{}::atom set"}, _) = @{term "{}::atom set"}
  | mk_diff (t1, @{term "{}::atom set"}) = t1
  | mk_diff (@{term "set ([]::atom list)"}, _) = @{term "set ([]::atom list)"}
  | mk_diff (t1, @{term "set ([]::atom list)"}) = t1
  | mk_diff (t1, t2) = HOLogic.mk_binop @{const_name minus} (t1, t2)

fun mk_append (t1, @{term "[]::atom list"}) = t1
  | mk_append (@{term "[]::atom list"}, t2) = t2
  | mk_append (t1, t2) = HOLogic.mk_binop @{const_name "append"} (t1, t2)

fun mk_union (t1, @{term "{}::atom set"}) = t1
  | mk_union (@{term "{}::atom set"}, t2) = t2
  | mk_union (t1, @{term "set ([]::atom list)"}) = t1
  | mk_union (@{term "set ([]::atom list)"}, t2) = t2
  | mk_union (t1, t2) = HOLogic.mk_binop @{const_name "sup"} (t1, t2)

fun fold_union trms = fold_rev (curry mk_union) trms @{term "{}::atom set"}
fun fold_append trms = fold_rev (curry mk_append) trms @{term "[]::atom list"}

fun mk_conj (t1, @{term "True"}) = t1
  | mk_conj (@{term "True"}, t2) = t2
  | mk_conj (t1, t2) = HOLogic.mk_conj (t1, t2)

fun fold_conj trms = fold_rev (curry mk_conj) trms @{term "True"}
fun fold_conj_balanced ts = Balanced_Tree.make HOLogic.mk_conj ts


(* functions for de-Bruijn open terms *)

fun mk_binop_env tys c (t, u) =
  let
    val ty = fastype_of1 (tys, t)
  in
    Const (c, [ty, ty] ---> ty) $ t $ u
  end

fun mk_union_env tys (t1, @{term "{}::atom set"}) = t1
  | mk_union_env tys (@{term "{}::atom set"}, t2) = t2
  | mk_union_env tys (t1, @{term "set ([]::atom list)"}) = t1
  | mk_union_env tys (@{term "set ([]::atom list)"}, t2) = t2
  | mk_union_env tys (t1, t2) = mk_binop_env tys @{const_name "sup"} (t1, t2)

fun fold_union_env tys trms = fold_left (mk_union_env tys) trms @{term "{}::atom set"}


(* produces fresh arguments for a term *)

fun fresh_args ctxt f =
    f |> fastype_of
      |> binder_types
      |> map (pair "z")
      |> Variable.variant_frees ctxt [f]
      |> map Free


(** some logic operations **)

(* decompses a formula into params, premises and a conclusion *)
fun strip_full_horn trm =
  let
    fun strip_outer_params (Const (@{const_name Pure.all}, _) $ Abs (a, T, t)) = strip_outer_params t |>> cons (a, T)
    | strip_outer_params B = ([], B)

    val (params, body) = strip_outer_params trm
    val (prems, concl) = Logic.strip_horn body
  in
    (params, prems, concl)
  end

(* composes a formula out of params, premises and a conclusion *)
fun mk_full_horn params prems concl =
  Logic.list_implies (prems, concl)
  |> fold_rev mk_all params

(** datatypes **)

(* constructor infos *)
type cns_info = (term * typ * typ list * bool list) list

(*  - term for constructor constant
    - type of the constructor
    - types of the arguments
    - flags indicating whether the argument is recursive
*)

(* returns info about constructors in a datatype *)
fun all_dtyp_constrs_info descr =
  map (fn (_, (ty, vs, constrs)) => map (pair (ty, vs)) constrs) descr

(* returns the constants of the constructors plus the
   corresponding type and types of arguments *)
fun all_dtyp_constrs_types descr =
  let
    fun aux ((ty_name, vs), (cname, args)) =
      let
        val vs_tys = map (Old_Datatype_Aux.typ_of_dtyp descr) vs
        val ty = Type (ty_name, vs_tys)
        val arg_tys = map (Old_Datatype_Aux.typ_of_dtyp descr) args
        val is_rec = map Old_Datatype_Aux.is_rec_type args
      in
        (Const (cname, arg_tys ---> ty), ty, arg_tys, is_rec)
      end
  in
    map (map aux) (all_dtyp_constrs_info descr)
  end

(** function package tactics **)

fun pat_completeness_simp simps ctxt =
  let
    val simpset =
      put_simpset HOL_basic_ss ctxt addsimps (@{thms sum.inject sum.distinct} @ simps)
  in
    Pat_Completeness.pat_completeness_tac ctxt 1
      THEN ALLGOALS (asm_full_simp_tac simpset)
  end

(* simpset for size goals *)
val size_ss =
  simpset_of (put_simpset HOL_ss @{context}
   addsimprocs [@{simproc natless_cancel_numerals}]
   addsimps @{thms in_measure wf_measure sum.case add_Suc_right add.right_neutral
     zero_less_Suc prod.size(1) mult_Suc_right})

val natT = @{typ nat}

fun size_prod_const T1 T2 =
  let
    val T1_fun = T1 --> natT
    val T2_fun = T2 --> natT
    val prodT = HOLogic.mk_prodT (T1, T2)
  in
    Const (@{const_name size_prod}, [T1_fun, T2_fun, prodT] ---> natT)
  end

fun snd_const T1 T2 =
  Const (@{const_name Product_Type.snd}, HOLogic.mk_prodT (T1, T2) --> T2)


fun mk_measure_trm f ctxt T =
  HOLogic.dest_setT T
  |> fst o HOLogic.dest_prodT
  |> f
  |> curry (op $) (Const (@{const_name "measure"}, dummyT))
  |> Syntax.check_term ctxt

(* wf-goal arising in induction_schema *)
fun prove_termination_ind ctxt =
  let
    fun mk_size_measure T =
      case T of
        (Type (@{type_name Sum_Type.sum}, [T1, T2])) =>
           Sum_Tree.mk_sumcase T1 T2 natT (mk_size_measure T1) (mk_size_measure T2)
      | (Type (@{type_name Product_Type.prod}, [T1, T2])) =>
           HOLogic.mk_comp (mk_size_measure T2, snd_const T1 T2)
      | _ => HOLogic.size_const T

    val measure_trm = mk_measure_trm (mk_size_measure) ctxt
  in
    Function_Relation.relation_tac ctxt measure_trm
  end

(* wf-goal arising in function definitions *)
fun prove_termination_fun size_simps ctxt =
let
  fun mk_size_measure T =
    case T of
      (Type (@{type_name Sum_Type.sum}, [T1, T2])) =>
         Sum_Tree.mk_sumcase T1 T2 natT (mk_size_measure T1) (mk_size_measure T2)
    | (Type (@{type_name Product_Type.prod}, [T1, T2])) =>
         size_prod_const T1 T2 $ (mk_size_measure T1) $ (mk_size_measure T2)
    | _ => HOLogic.size_const T

  val measure_trm = mk_measure_trm (mk_size_measure) ctxt

  val tac =
    Function_Relation.relation_tac ctxt measure_trm
    THEN_ALL_NEW simp_tac (put_simpset size_ss ctxt addsimps size_simps)
  in
    Function.prove_termination NONE (HEADGOAL tac) ctxt
  end

(** transformations of premises (in inductive proofs) **)

(*
 given the theorem F[t]; proves the theorem F[f t]

  - F needs to be monotone
  - f returns either SOME for a term it fires on
    and NONE elsewhere
*)
fun map_term f t =
  (case f t of
     NONE => map_term' f t
   | x => x)
and map_term' f (t $ u) =
    (case (map_term f t, map_term f u) of
        (NONE, NONE) => NONE
      | (SOME t'', NONE) => SOME (t'' $ u)
      | (NONE, SOME u'') => SOME (t $ u'')
      | (SOME t'', SOME u'') => SOME (t'' $ u''))
  | map_term' f (Abs (s, T, t)) =
      (case map_term f t of
        NONE => NONE
      | SOME t'' => SOME (Abs (s, T, t'')))
  | map_term' _ _  = NONE;

fun map_thm_tac ctxt tac thm =
  let
    val monos = Inductive.get_monos ctxt
    val simpset = put_simpset HOL_basic_ss ctxt addsimps @{thms split_def}
  in
    EVERY [cut_facts_tac [thm] 1, eresolve_tac ctxt [rev_mp] 1,
      REPEAT_DETERM (FIRSTGOAL (simp_tac simpset THEN' resolve_tac ctxt monos)),
      REPEAT_DETERM (resolve_tac ctxt [impI] 1 THEN (assume_tac ctxt 1 ORELSE tac))]
  end

fun map_thm ctxt f tac thm =
  let
    val opt_goal_trm = map_term f (Thm.prop_of thm)
  in
    case opt_goal_trm of
      NONE => thm
    | SOME goal =>
        Goal.prove ctxt [] [] goal (fn _ => map_thm_tac ctxt tac thm)
  end

(*
 inductive premises can be of the form

     R ... /\ P ...;

 split_conj_i picks out the part R or P part
*)
fun split_conj1 names (Const (@{const_name "conj"}, _) $ f1 $ _) =
  (case head_of f1 of
     Const (name, _) => if member (op =) names name then SOME f1 else NONE
   | _ => NONE)
| split_conj1 _ _ = NONE;

fun split_conj2 names (Const (@{const_name "conj"}, _) $ f1 $ f2) =
  (case head_of f1 of
     Const (name, _) => if member (op =) names name then SOME f2 else NONE
   | _ => NONE)
| split_conj2 _ _ = NONE;

fun transform_prem1 ctxt names thm =
  map_thm ctxt (split_conj1 names) (eresolve_tac ctxt [conjunct1] 1) thm

fun transform_prem2 ctxt names thm =
  map_thm ctxt (split_conj2 names) (eresolve_tac ctxt [conjunct2] 1) thm


(* transforms a theorem into one of the object logic *)
fun atomize ctxt = Conv.fconv_rule (Object_Logic.atomize ctxt) o forall_intr_vars;
fun atomize_rule ctxt i thm =
  Conv.fconv_rule (Conv.concl_conv i (Object_Logic.atomize ctxt)) thm
fun atomize_concl ctxt thm = atomize_rule ctxt (length (Thm.prems_of thm)) thm


(* applies a tactic to a formula composed of conjunctions *)
fun conj_tac ctxt tac i =
  let
     fun select (trm, i) =
       case trm of
         @{term "Trueprop"} $ t' => select (t', i)
       | @{term "(&)"} $ _ $ _ =>
          EVERY' [resolve_tac ctxt @{thms conjI}, RANGE [conj_tac ctxt tac, conj_tac ctxt tac]] i
       | _ => tac i
  in
    SUBGOAL select i
  end

end (* structure *)

open Nominal_Library;
