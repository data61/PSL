(* auxiliary functions which might be useful when deriving something for
   datatypes via recursors *)

signature DERIVE_AUX =
sig
  (* split_last [a,...,z] -> ([a,...,y],z) *)
  val split_last : 'a list -> 'a list * 'a

  (* p1 \<longrightarrow> p2 \<longrightarrow> \<dots> \<longrightarrow> p_n \<longrightarrow> r *)
  val HOLogic_list_implies : term list * term -> term

  (* p1 /\ ... /\ pn *)
  val HOLogic_list_conj : term list -> term

  (* \<forall> x1 ... xn . p *)
  val HOLogic_list_all : term list * term -> term

  (* rulifys P1 .. Pn in a thm P1 ==> ... ==> Pn ==> Q *)
  val rulify_only_asm : Proof.context -> thm -> thm

(* takes a list of implications, an induction theorem, and a tactic to handle each case,
   and delivers the major implication.
   Example: if imp_list is [([p1 x y, q1 x y], [x,y]), ([p2 x' y', q2 x' y'], [x',y'])]
            and ind_thm is ... ==> P1 x /\ P2 x'
            then it encodes p1 x y ==> q1 x y &&& p2 x' y' ==> q2 x' y'
            which is converted to HOL (! y. p1 x y --> q1 x y) /\ (! y'. p2 x' y' --> q2 x' y')
            which is proven by the instantiated ind_thm where, e.g. P1 = % x. (! y. p1 x y --> q1 x y)
            and where in the IH all HOL-constructs are rulified again.
            As a result, only the first implication is returned: "p1 x y ==> q1 x y"
   Purpose: encountered problems with induct-tac
     - P1 and P2 are two large for internal unification, so they must be provided
     - if P1 and P2 are provided, then one has to use HOL-constructs (for arbitrary choice of y and y')
     - in induct_tac, then the IH are not converted to nice meta-implications/quantifications
*)
  val inductive_thm : theory -> (term list * term list) list -> thm -> sort ->
      (*                idx    ih_hyps     ih_prems    case_vars    arbi_vars *)
      (Proof.context -> int -> thm list -> thm list -> term list -> term list -> tactic) -> thm

(* delivers a typ substitution which constrains all free type variables in datatype by sort *)
  val typ_subst_for_sort : theory -> Old_Datatype_Aux.info -> sort -> typ -> typ

(* delivers a full type from a type name by instantiating the type-variables of that
   type with different variables of a given sort, also returns the chosen variables
   as second component *)
  val typ_and_vs_of_typname : theory -> string -> sort -> typ * (string * sort) list

(* identity and number recursive occurrences of datatypes *)
  val dt_number_recs : Old_Datatype_Aux.dtyp list -> int * (int * int) list

(* like print_tac, but is turned off by default to not exceed tracing limit *)
  val my_print_tac : Proof.context -> string -> tactic

(* generates a theorem over two variables, where induction over the first one performed,
   and then in every case one performs immediately a case analysis on the second variable.
   It is assumed that if the constructors are different, then the goal is proven by some
   standard tactic, whereas for same constructors, one has to provide a tactic *)
  val mk_binary_thm :
    (theory -> Old_Datatype_Aux.info -> sort -> 'a -> (term list * term list) list) -> (* mk_prop_trm *)
    (theory -> Old_Datatype_Aux.info -> sort -> (int -> term) * ('b * int * int) list) -> (* mk_bin_idx *)
    string -> (* bin_const_name *)
    theory ->
    Old_Datatype_Aux.info ->
    'a -> (* property_generator *)
    sort ->
    (* same_constructor_tac *)
    (Proof.context -> thm list -> thm list -> thm -> (Proof.context -> thm list -> tactic) -> int -> term list ->
     term list -> string * Old_Datatype_Aux.dtyp list -> (Old_Datatype_Aux.dtyp -> term -> term -> term) -> tactic)
    -> thm

  val mk_case_tac : Proof.context ->
    term option list list -> (* usually [[SOME term_to_perform_the_case]] *)
    thm -> (* exhaust theorem *)
    (*               i-th case, prems, newly obtained arguments *)
    (Proof.context * int * thm list * (string * cterm) list -> tactic)
    -> tactic

  val prop_trm_to_major_imp : (term list * 'a) list -> term * 'a

(* delivers "x_i" of corresponding datatype of idx-th type for datatype *)
(*                                                 idx    i *)
  val mk_xs : theory -> Old_Datatype_Aux.info -> sort -> int -> int -> term

(* create Some t *)
  val mk_Some : term -> term

(* my_simp_set should be HOL_ss + the other simplification stuff for orders like simprocs, ... *)
  val my_simp_set : simpset

  val mk_solve_with_tac : Proof.context -> thm list -> tactic -> tactic

  val define_overloaded : (string * term) -> local_theory -> thm * local_theory

  val define_overloaded_generic : (Attrib.binding * term) -> local_theory -> thm * local_theory

  val mk_def : typ -> string -> term -> term

end


structure Derive_Aux : DERIVE_AUX =
struct

val printing = false
fun my_print_tac ctxt = if printing then print_tac ctxt else (fn _ => Seq.single)

fun split_last xs = (take (length xs - 1) xs, List.last xs)

(* FIXME: reconsolidate with similar functions in the Isabelle repository and move to HOLogic *)
fun HOLogic_list_implies (prems,r) = fold_rev (fn r => fn p => HOLogic.mk_imp (r,p)) prems r
fun HOLogic_list_conj [] = @{term true}
  | HOLogic_list_conj [x] = x
  | HOLogic_list_conj (x :: xs) = HOLogic.mk_conj (x, HOLogic_list_conj xs)
fun HOLogic_list_all (xs,p) = fold_rev (fn (x,ty) => fn p => HOLogic.mk_all (x,ty,p)) (map dest_Free xs) p

fun mk_Some t = let
    val ty = fastype_of t
  in
    Const (@{const_name Some}, ty --> Type (@{type_name option}, [ty])) $ t
  end

fun rulify_only_asm ctxt thm =
  (@{thm conjI[OF TrueI]} OF [thm]) (* add conj to prohibit rulify in conclusion *)
  |> Object_Logic.rulify ctxt (* rulify everything, i.e., by preprocessing only the assms *)
  |> (fn conj => (@{thm conjunct2} OF [conj])) (* drop conjunction again *)

fun permute_for_ind_thm ps xs ind_thm =
  let
    val n = length ps
    val vs_p = Thm.prop_of ind_thm |> Term.add_vars |> (fn f => f [] |> rev)
    fun number_ih_vars _ [] = []
      | number_ih_vars i (P :: x :: pxs) = ((P,i) :: (x,i+n) :: number_ih_vars (i+1) pxs)
      | number_ih_vars _ _ = error "odd number of vars in ind-thm"
    val vs_c = Thm.concl_of ind_thm |> Term.add_vars |> (fn f => f [] |> rev) |> number_ih_vars 0
    val permutation = map (AList.lookup (op =) vs_c #> the) vs_p
  in
    map (nth (ps @ xs)) permutation
  end


fun inductive_thm thy (imp_list : (term list * term list) list) ind_thm sort ind_tac =
  let
    val imps = map
      (fn (imps,xs) => HOLogic_list_all (tl xs, HOLogic_list_implies (split_last imps)))
      imp_list
    val ind_term =
      HOLogic_list_conj imps
      |> HOLogic.mk_Trueprop
    val nr_prems = length (hd imp_list |> fst) - 1
    val nr_arbi = length (hd imp_list |> snd) - 1
    val xs = map (snd #> hd) imp_list
    val ps = xs ~~ imps
      |> map (fn (x,imp) => lambda x imp)
    val insts = permute_for_ind_thm ps xs ind_thm
    val xs_strings = map (dest_Free #> fst) xs
    val conjunctive_thm = Goal.prove_global_future thy xs_strings [] ind_term
      (fn {context = ctxt, ...} =>
        let
          val ind_thm_inst = infer_instantiate' ctxt (map (SOME o Thm.cterm_of ctxt) insts) ind_thm
          val ind_thm' = rulify_only_asm (Proof_Context.init_global thy) ind_thm_inst
        in
          (DETERM o Induct.induct_tac ctxt false [] [] [] (SOME [ind_thm']) [])
          THEN_ALL_NEW
          (fn i => Subgoal.SUBPROOF
            (fn {context = ctxt, prems = prems, params = iparams, ...} =>
              let
                val m = length prems - nr_prems
                val ih_prems = drop m prems
                val ih_hyps = take m prems
                val tparams = map (snd #> Thm.term_of) iparams
                val m' = length tparams - nr_arbi
                val arbi_vars = drop m' tparams
                val case_vars = take m' tparams
              in
                ind_tac ctxt (i-1) ih_hyps ih_prems case_vars arbi_vars
              end
            ) ctxt i
          )
        end 1
      )
    (* extract first conjunct *)
    val first_conj = if length imp_list > 1 then @{thm conjunct1} OF [conjunctive_thm] else conjunctive_thm
    (* and replace \<longrightarrow> and \<forall> by meta-logic (for those \<longrightarrow> and \<forall> which have been constructed) *)
    val elim_spec = funpow nr_arbi (fn thm => @{thm spec} OF [thm]) first_conj
    val elim_imp = funpow nr_prems (fn thm => @{thm mp} OF [thm]) elim_spec
  in elim_imp end

fun typ_subst_for_sort thy info sort =
  let
    val spec = BNF_LFP_Compat.the_spec thy (#descr info |> hd |> (fn (_,(dty_name,_,_)) => dty_name))
    val typ_subst = Term.typ_subst_atomic (spec |> fst |> map (fn (n,s) => (TFree (n,s), TFree (n,sort))))
  in typ_subst end

fun typ_and_vs_of_typname thy typ_name sort =
  let
    val ar = Sign.arity_number thy typ_name
    val sorts = map (K sort) (1 upto ar)
    val ty_vars = Name.invent_names (Name.make_context [typ_name]) "a" sorts
    val ty = Type (typ_name,map TFree ty_vars)
  in (ty,ty_vars)
end


fun dt_number_recs dtys =
  let
    fun dtrecs [] j = (j,[])
      | dtrecs (Old_Datatype_Aux.DtTFree _ :: dtys) j = dtrecs dtys j
      | dtrecs (Old_Datatype_Aux.DtRec i :: dtys) j =
          let
            val (j',ijs) = dtrecs dtys (j+1)
          in (j',(i,j) :: ijs) end
      | dtrecs (Old_Datatype_Aux.DtType (_,dtys1) :: dtys2) j =
          let
            val (j',ijs) = dtrecs dtys1 j
            val (j'',ijs') = dtrecs dtys2 j'
          in (j'',ijs @ ijs') end
  in dtrecs dtys 0
end

(* code copied from HOL/SPARK/TOOLS *)
fun define_overloaded_generic (binding,eq) lthy =
  let
    val ((c, _), rhs) = eq |> Syntax.check_term lthy |>
      Logic.dest_equals |>> dest_Free;
    val ((_, (_, thm)), lthy') = Local_Theory.define
      ((Binding.name c, NoSyn), (binding, rhs)) lthy
    val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy');
    val thm' = singleton (Proof_Context.export lthy' ctxt_thy) thm
  in (thm', lthy')
end

fun define_overloaded (name,eq) = define_overloaded_generic ((Binding.name name, @{attributes [code]}),eq)


fun mk_def T c rhs = Logic.mk_equals (Const (c, T), rhs)

(* construct free variable x_i *)
fun mk_free_tysubst_i typ_subst x i ty = Free (x ^ string_of_int i, ty |> typ_subst)


fun mk_xs thy info sort idx i =
  let
    val descr = #descr info
    val typ_subst = typ_subst_for_sort thy info sort
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    val mk_free_i = mk_free_tysubst_i typ_subst
  in
    mk_free_i ("x_" ^ string_of_int idx ^ "_") i (typ_of (Old_Datatype_Aux.DtRec idx))
  end

fun prop_trm_to_major_imp prop =
  hd prop
  |> (fn (p,v) => (
    map (HOLogic.mk_Trueprop) p
    |> split_last
    |> Logic.list_implies,
    v))


fun mk_case_tac (ctxt : Proof.context)
  (insts : term option list list)
  (thm : thm)
  (sub_case_tac : Proof.context * int * thm list * (string * cterm) list -> tactic) =
    (
      DETERM o Induct.cases_tac ctxt false insts (SOME thm) []
      THEN_ALL_NEW (fn i => Subgoal.SUBPROOF (fn {context = ctxt, prems = hyps, params = params, ...}
        => sub_case_tac (ctxt, i-1, hyps, params)) ctxt i)
    )
    1

fun mk_solve_with_tac ctxt thms solver_tac =
  SOLVE (Method.insert_tac ctxt thms 1 THEN solver_tac)

fun simps_of_info info = #case_rewrites info @ #rec_rewrites info @ #inject info @ #distinct info

val my_simp_set =
  simpset_of (@{context}
    delsimps (simpset_of @{context} |> dest_ss |> #simps |> map snd)
    addsimps @{thms HOL.simp_thms})

fun mk_binary_thm mk_prop_trm mk_bin_idx bin_const_name thy (info : Old_Datatype_Aux.info) prop_gen sort same_constructor_tac =
  let
    fun bin_const ty = Const (bin_const_name, ty --> ty --> @{typ bool})
    val prop_props = mk_prop_trm thy info sort prop_gen
    val (mk_rec,nrec_args) = mk_bin_idx thy info sort
    val typ_subst = typ_subst_for_sort thy info sort
    val descr = #descr info
    fun typ_of dty = Old_Datatype_Aux.typ_of_dtyp descr dty |> typ_subst
    fun mk_binary_term (Old_Datatype_Aux.DtRec i) = mk_rec i
      | mk_binary_term dty =
          let
            val ty = typ_of dty
          in bin_const ty end;
    fun mk_binary dty x y = mk_binary_term dty $ x $ y;
    val ind_thm = #induct info
    val prop_thm_of_tac = inductive_thm thy prop_props ind_thm sort
    fun ind_case_tac ctxt i hyps ihprems params_x ys =
      let
        val y = hd ys
        val (j,idx) = nth nrec_args i |> (fn (_,j,idx) => (j,idx))
        val linfo = nth descr idx |> (fn (_,(ty_name,_,_)) => ty_name)
          |> BNF_LFP_Compat.the_info thy []
        fun solve_with_tac ctxt thms =
          let val simp_ctxt =
            (ctxt
              |> Context_Position.set_visible false
              |> put_simpset my_simp_set)
              addsimps (simps_of_info info @ simps_of_info linfo)
          in mk_solve_with_tac ctxt thms (force_tac simp_ctxt 1) end
        fun case_tac ctxt = mk_case_tac ctxt [[SOME y]] (#exhaust linfo)
        fun sub_case_tac (ctxt,k,prems,iparams_y) =
          let
            val case_hyp_y = hd prems
          in
            if not (j = k)
            then my_print_tac ctxt ("different constructors ") THEN solve_with_tac ctxt (case_hyp_y :: ihprems) (* different constructor *)
            else
              let
                val params_y = map (snd #> Thm.term_of) iparams_y
                val c_info = nth descr idx |> snd |> (fn (_,_,info) => nth info j)
              in
                my_print_tac ctxt ("consider constructor " ^ string_of_int k)
                THEN same_constructor_tac ctxt hyps ihprems case_hyp_y solve_with_tac j params_x params_y c_info mk_binary
              end
          end
      in my_print_tac ctxt ("start induct " ^ string_of_int i) THEN case_tac ctxt sub_case_tac end
    val prop_thm = prop_thm_of_tac ind_case_tac
  in prop_thm end

fun mk_case_tac ctxt
  (insts : term option list list)
  (thm : thm)
  (sub_case_tac : Proof.context * int * thm list * (string * cterm) list -> tactic) =
    (
      DETERM o Induct.cases_tac ctxt false insts (SOME thm) []
      THEN_ALL_NEW (fn i => Subgoal.SUBPROOF (fn {context = ctxt, prems = hyps, params = params, ...}
        => sub_case_tac (ctxt, i-1, hyps, params)) ctxt i)
    )
    1

end
