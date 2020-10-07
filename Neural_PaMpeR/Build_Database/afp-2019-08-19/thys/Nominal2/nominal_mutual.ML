(*  Nominal Mutual Functions
    Author:  Christian Urban

    heavily based on the code of Alexander Krauss
    (code forked on 14 January 2011)

    Joachim Breitner helped with the auxiliary graph
    definitions (7 August 2012)

Mutual recursive nominal function definitions.
*)


signature NOMINAL_FUNCTION_MUTUAL =
sig
  val prepare_nominal_function_mutual : Nominal_Function_Common.nominal_function_config
    -> string (* defname *)
    -> ((string * typ) * mixfix) list
    -> term list
    -> local_theory
    -> ((thm (* goalstate *)
        * (Proof.context -> thm -> Nominal_Function_Common.nominal_function_result) (* proof continuation *)
       ) * local_theory)
end

structure Nominal_Function_Mutual: NOMINAL_FUNCTION_MUTUAL =
struct

open Function_Lib
open Function_Common
open Nominal_Function_Common

type qgar = string * (string * typ) list * term list * term list * term

datatype mutual_part = MutualPart of
 {i : int,
  i' : int,
  fvar : string * typ,
  cargTs: typ list,
  f_def: term,
  f: term option,
  f_defthm : thm option}

datatype mutual_info = Mutual of
 {n : int,
  n' : int,
  fsum_var : string * typ,

  ST: typ,
  RST: typ,

  parts: mutual_part list,
  fqgars: qgar list,
  qglrs: ((string * typ) list * term list * term * term) list,

  fsum : term option}

fun mutual_induct_Pnames n =
  if n < 5 then fst (chop n ["P","Q","R","S"])
  else map (fn i => "P" ^ string_of_int i) (1 upto n)

fun get_part fname =
  the o find_first (fn (MutualPart {fvar=(n,_), ...}) => n = fname)

(* FIXME *)
fun mk_prod_abs e (t1, t2) =
  let
    val bTs = rev (map snd e)
    val T1 = fastype_of1 (bTs, t1)
    val T2 = fastype_of1 (bTs, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end

fun analyze_eqs ctxt defname fs eqs =
  let
    val num = length fs
    val fqgars = map (split_def ctxt (K true)) eqs
    val arity_of = map (fn (fname,_,_,args,_) => (fname, length args)) fqgars
      |> AList.lookup (op =) #> the

    fun curried_types (fname, fT) =
      let
        val (caTs, uaTs) = chop (arity_of fname) (binder_types fT)
      in
        (caTs, uaTs ---> body_type fT)
      end

    val (caTss, resultTs) = split_list (map curried_types fs)
    val argTs = map (foldr1 HOLogic.mk_prodT) caTss

    val dresultTs = distinct (op =) resultTs
    val n' = length dresultTs

    val RST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) dresultTs
    val ST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) argTs

    val fsum_type = ST --> RST

    val ([fsum_var_name], _) = Variable.add_fixes [ defname ^ "_sum" ] ctxt
    val fsum_var = (fsum_var_name, fsum_type)

    fun define (fvar as (n, _)) caTs resultT i =
      let
        val vars = map_index (fn (j,T) => Free ("x" ^ string_of_int j, T)) caTs (* FIXME: Bind xs properly *)
        val i' = find_index (fn Ta => Ta = resultT) dresultTs + 1

        val f_exp = Sum_Tree.mk_proj RST n' i' (Free fsum_var $ Sum_Tree.mk_inj ST num i (foldr1 HOLogic.mk_prod vars))
        val def = Term.abstract_over (Free fsum_var, fold_rev lambda vars f_exp)

        val rew = (n, fold_rev lambda vars f_exp)
      in
        (MutualPart {i=i, i'=i', fvar=fvar,cargTs=caTs,f_def=def,f=NONE,f_defthm=NONE}, rew)
      end

    val (parts, rews) = split_list (map4 define fs caTss resultTs (1 upto num))

    fun convert_eqs (f, qs, gs, args, rhs) =
      let
        val MutualPart {i, i', ...} = get_part f parts
        val rhs' = rhs
             |> map_aterms (fn t as Free (n, _) => the_default t (AList.lookup (op =) rews n) | t => t)
      in
        (qs, gs, Sum_Tree.mk_inj ST num i (foldr1 (mk_prod_abs qs) args),
         Envir.beta_norm (Sum_Tree.mk_inj RST n' i' rhs'))
      end

    val qglrs = map convert_eqs fqgars
  in
    Mutual {n=num, n'=n', fsum_var=fsum_var, ST=ST, RST=RST,
      parts=parts, fqgars=fqgars, qglrs=qglrs, fsum=NONE}
  end

fun define_projections fixes mutual fsum lthy =
  let
    fun def ((MutualPart {i=i, i'=i', fvar=(fname, fT), cargTs, f_def, ...}), (_, mixfix)) lthy =
      let
        val ((f, (_, f_defthm)), lthy') =
          Local_Theory.define
            ((Binding.name fname, mixfix),
              ((Binding.concealed (Binding.name (fname ^ "_def")), []),
              Term.subst_bound (fsum, f_def))) lthy
      in
        (MutualPart {i=i, i'=i', fvar=(fname, fT), cargTs=cargTs, f_def=f_def,
           f=SOME f, f_defthm=SOME f_defthm },
         lthy')
      end

    val Mutual { n, n', fsum_var, ST, RST, parts, fqgars, qglrs, ... } = mutual
    val (parts', lthy') = fold_map def (parts ~~ fixes) lthy
  in
    (Mutual { n=n, n'=n', fsum_var=fsum_var, ST=ST, RST=RST, parts=parts',
       fqgars=fqgars, qglrs=qglrs, fsum=SOME fsum },
     lthy')
  end

fun in_context ctxt (f, pre_qs, pre_gs, pre_args, pre_rhs) F =
  let
    val oqnames = map fst pre_qs
    val (qs, _) = Variable.variant_fixes oqnames ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val args = map inst pre_args
    val rhs = inst pre_rhs

    val cqs = map (Thm.cterm_of ctxt) qs
    val (ags, ctxt') = fold_map Thm.assume_hyps (map (Thm.cterm_of ctxt) gs) ctxt

    val import = fold Thm.forall_elim cqs
      #> fold Thm.elim_implies ags

    val export = fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      #> fold_rev forall_intr_rename (oqnames ~~ cqs)
  in
    F ctxt' (f, qs, gs, args, rhs) import export
  end

fun recover_mutual_psimp all_orig_fdefs parts ctxt (fname, _, _, args, rhs)
  import (export : thm -> thm) sum_psimp_eq =
  let
    val (MutualPart {f=SOME f, ...}) = get_part fname parts

    val psimp = import sum_psimp_eq
    val ((simp, restore_cond), ctxt') =
      case cprems_of psimp of
        [] => ((psimp, I), ctxt)
      | [cond] =>
          let val (asm, ctxt') = Thm.assume_hyps cond ctxt
          in ((Thm.implies_elim psimp asm, Thm.implies_intr cond), ctxt') end
      | _ => raise General.Fail "Too many conditions"
  in
    Goal.prove ctxt' [] []
      (HOLogic.Trueprop $ HOLogic.mk_eq (list_comb (f, args), rhs))
      (fn _ => (Local_Defs.unfold_tac ctxt' all_orig_fdefs)
         THEN EqSubst.eqsubst_tac ctxt' [0] [simp] 1
         THEN (simp_tac ctxt') 1)
    |> restore_cond
    |> export
  end

val inl_perm = @{lemma "x = Inl y ==> projl (permute p x) = permute p (projl x)" by simp}
val inr_perm = @{lemma "x = Inr y ==> projr (permute p x) = permute p (projr x)" by simp}

fun recover_mutual_eqvt eqvt_thm all_orig_fdefs parts ctxt (fname, _, _, args, _)
  import (export : thm -> thm) sum_psimp_eq =
  let
    val (MutualPart {f=SOME f, ...}) = get_part fname parts

    val psimp = import sum_psimp_eq
    val ((cond, simp, restore_cond), ctxt') =
      case cprems_of psimp of
        [] => (([], psimp, I), ctxt)
      | [cond] =>
          let val (asm, ctxt') = Thm.assume_hyps cond ctxt
          in (([asm], Thm.implies_elim psimp asm, Thm.implies_intr cond), ctxt') end
      | _ => raise General.Fail "Too many conditions"

    val ([p], ctxt'') = ctxt'
      |> fold Variable.declare_term args
      |> Variable.variant_fixes ["p"]
    val p = Free (p, @{typ perm})

    val simpset =
      put_simpset HOL_basic_ss ctxt'' addsimps
      @{thms permute_sum.simps[symmetric] Pair_eqvt[symmetric] sum.sel} @
      [(cond MRS eqvt_thm) RS @{thm sym}] @
      [inl_perm, inr_perm, simp]
    val goal_lhs = mk_perm p (list_comb (f, args))
    val goal_rhs = list_comb (f, map (mk_perm p) args)
  in
    Goal.prove ctxt'' [] [] (HOLogic.Trueprop $ HOLogic.mk_eq (goal_lhs, goal_rhs))
      (fn _ => Local_Defs.unfold_tac ctxt'' all_orig_fdefs
         THEN (asm_full_simp_tac simpset 1))
    |> singleton (Proof_Context.export ctxt'' ctxt)
    |> restore_cond
    |> export
  end

fun mk_applied_form ctxt caTs thm =
  let
    val xs = map_index (fn (i,T) => Thm.cterm_of ctxt (Free ("x" ^ string_of_int i, T))) caTs (* FIXME: Bind xs properly *)
  in
    fold (fn x => fn thm => Thm.combination thm (Thm.reflexive x)) xs thm
    |> Conv.fconv_rule (Thm.beta_conversion true)
    |> fold_rev Thm.forall_intr xs
    |> Thm.forall_elim_vars 0
  end

fun mutual_induct_rules ctxt induct all_f_defs (Mutual {n, ST, parts, ...}) =
  let
    val cert = Thm.cterm_of ctxt
    val newPs =
      map2 (fn Pname => fn MutualPart {cargTs, ...} =>
          Free (Pname, cargTs ---> HOLogic.boolT))
        (mutual_induct_Pnames (length parts)) parts

    fun mk_P (MutualPart {cargTs, ...}) P =
      let
        val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
        val atup = foldr1 HOLogic.mk_prod avars
      in
        HOLogic.tupled_lambda atup (list_comb (P, avars))
      end

    val Ps = map2 mk_P parts newPs
    val case_exp = Sum_Tree.mk_sumcases HOLogic.boolT Ps

    val induct_inst =
      Thm.forall_elim (cert case_exp) induct
      |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
      |> full_simplify (put_simpset HOL_basic_ss ctxt addsimps all_f_defs)

    fun project rule (MutualPart {cargTs, i, ...}) k =
      let
        val afs = map_index (fn (j,T) => Free ("a" ^ string_of_int (j + k), T)) cargTs (* FIXME! *)
        val inj = Sum_Tree.mk_inj ST n i (foldr1 HOLogic.mk_prod afs)
      in
        (rule
         |> Thm.forall_elim (cert inj)
         |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
         |> fold_rev (Thm.forall_intr o cert) (afs @ newPs),
         k + length cargTs)
      end
  in
    fst (fold_map (project induct_inst) parts 0)
  end


fun forall_elim s (Const (@{const_name Pure.all}, _) $ Abs (_, _, t)) = subst_bound (s, t)
  | forall_elim _ t = t

val forall_elim_list = fold forall_elim

fun split_conj_thm th =
  (split_conj_thm (th RS conjunct1)) @ (split_conj_thm (th RS conjunct2)) handle THM _ => [th];

fun prove_eqvt ctxt fs argTss eqvts_thms induct_thms =
  let
    fun aux argTs s = argTs
      |> map (pair s)
      |> Variable.variant_frees ctxt fs
    val argss' = map2 aux argTss (Name.invent (Variable.names_of ctxt) "" (length fs))
    val argss = (map o map) Free argss'
    val arg_namess = (map o map) fst argss'
    val insts = (map o map) SOME arg_namess

    val ([p_name], ctxt') = Variable.variant_fixes ["p"] ctxt
    val p = Free (p_name, @{typ perm})

    (* extracting the acc-premises from the induction theorems *)
    val acc_prems =
     map Thm.prop_of induct_thms
     |> map2 forall_elim_list argss
     |> map (strip_qnt_body @{const_name Pure.all})
     |> map (curry Logic.nth_prem 1)
     |> map HOLogic.dest_Trueprop

    fun mk_goal acc_prem (f, args) =
      let
        val goal_lhs = mk_perm p (list_comb (f, args))
        val goal_rhs = list_comb (f, map (mk_perm p) args)
      in
        HOLogic.mk_imp (acc_prem, HOLogic.mk_eq (goal_lhs, goal_rhs))
      end

    val goal = fold_conj_balanced (map2 mk_goal acc_prems (fs ~~ argss))
      |> HOLogic.mk_Trueprop

    val induct_thm = case induct_thms of
        [thm] => thm
          |> Variable.gen_all ctxt'
          |> Thm.permute_prems 0 1
          |> (fn thm => atomize_rule ctxt' (length (Thm.prems_of thm) - 1) thm)
      | thms => thms
          |> map (Variable.gen_all ctxt')
          |> map (Rule_Cases.add_consumes 1)
          |> snd o Rule_Cases.strict_mutual_rule ctxt'
          |> atomize_concl ctxt'

    fun tac ctxt thm =
      resolve_tac ctxt [Variable.gen_all ctxt thm]
        THEN_ALL_NEW assume_tac ctxt
  in
    Goal.prove ctxt' (flat arg_namess) [] goal
      (fn {context = ctxt'', ...} =>
        HEADGOAL (DETERM o (resolve_tac ctxt'' [induct_thm]) THEN'
          RANGE (map (tac ctxt'') eqvts_thms)))
    |> singleton (Proof_Context.export ctxt' ctxt)
    |> split_conj_thm
    |> map (fn th => th RS mp)
  end

fun mk_partial_rules_mutual ctxt inner_cont (m as Mutual {parts, fqgars, ...}) proof =
  let
    val result = inner_cont proof

    val NominalFunctionResult {G, R, cases, psimps, simple_pinducts=[simple_pinduct],
      termination, domintros, eqvts=[eqvt],...} = result

    val (all_f_defs, fs) =
      map (fn MutualPart {f_defthm = SOME f_def, f = SOME f, cargTs, ...} =>
          (mk_applied_form ctxt cargTs (Thm.symmetric f_def), f))
      parts
      |> split_list

    val all_orig_fdefs =
      map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts

    val cargTss =
      map (fn MutualPart {f = SOME f, cargTs, ...} => cargTs) parts

    fun mk_mpsimp fqgar sum_psimp =
      in_context ctxt fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp

    fun mk_meqvts fqgar sum_psimp =
      in_context ctxt fqgar (recover_mutual_eqvt eqvt all_orig_fdefs parts) sum_psimp

    val rew_simpset = put_simpset HOL_basic_ss ctxt addsimps all_f_defs
    val mpsimps = map2 mk_mpsimp fqgars psimps
    val minducts = mutual_induct_rules ctxt simple_pinduct all_f_defs m
    val mtermination = full_simplify rew_simpset termination
    val mdomintros = Option.map (map (full_simplify rew_simpset)) domintros
    val meqvts = map2 mk_meqvts fqgars psimps
    val meqvt_funs = prove_eqvt ctxt fs cargTss meqvts minducts
 in
    NominalFunctionResult { fs=fs, G=G, R=R,
      psimps=mpsimps, simple_pinducts=minducts,
      cases=cases, termination=mtermination,
      domintros=mdomintros, eqvts=meqvt_funs }
  end

(* nominal *)
fun subst_all s (Q $ Abs(_, _, t)) =
  let
    val vs = map Free (Term.add_frees s [])
  in
    fold Logic.all vs (subst_bound (s, t))
  end

fun mk_comp_dummy t s = Const (@{const_name comp}, dummyT) $ t $ s

fun all v t =
  let
    val T = Term.fastype_of v
  in
    Logic.all_const T $ absdummy T (abstract_over (v, t))
  end

(* nominal *)
fun prepare_nominal_function_mutual config defname fixes eqss lthy =
  let
    val mutual as Mutual {fsum_var=(n, T), qglrs, ...} =
      analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)

    val ((fsum, G, GIntro_thms, G_induct, goalstate, cont), lthy') =
      Nominal_Function_Core.prepare_nominal_function config defname [((n, T), NoSyn)] qglrs lthy

    val (mutual' as Mutual {n', parts, ST, RST, ...}, lthy'') = define_projections fixes mutual fsum lthy'

    (* defining the auxiliary graph *)
    fun mk_cases (MutualPart {i', fvar as (n, T), ...}) =
      let
        val (tys, ty) = strip_type T
        val fun_var = Free (n ^ "_aux", HOLogic.mk_tupleT tys --> ty)
        val inj_fun = absdummy dummyT (Sum_Tree.mk_inj RST n' i' (Bound 0))
      in
        Syntax.check_term lthy'' (mk_comp_dummy inj_fun fun_var)
      end

    val case_sum_exp = map mk_cases parts
      |> Sum_Tree.mk_sumcases RST

    val (G_name, G_type) = dest_Free G
    val G_name_aux = G_name ^ "_aux"
    val subst = [(G, Free (G_name_aux, G_type))]
    val GIntros_aux = GIntro_thms
      |> map Thm.prop_of
      |> map (Term.subst_free subst)
      |> map (subst_all case_sum_exp)

    val ((G_aux, GIntro_aux_thms, _, G_aux_induct), lthy''') =
      Nominal_Function_Core.inductive_def ((Binding.name G_name_aux, G_type), NoSyn) GIntros_aux lthy''

    fun mutual_cont ctxt = mk_partial_rules_mutual lthy''' (cont ctxt) mutual'

    (* proof of equivalence between graph and auxiliary graph *)
    val x = Var(("x", 0), ST)
    val y = Var(("y", 1), RST)
    val G_aux_prem = HOLogic.mk_Trueprop (G_aux $ x $ y)
    val G_prem = HOLogic.mk_Trueprop (G $ x $ y)

    fun mk_inj_goal  (MutualPart {i', ...}) =
      let
        val injs = Sum_Tree.mk_inj ST n' i' (Bound 0)
        val projs = y
          |> Sum_Tree.mk_proj RST n' i'
          |> Sum_Tree.mk_inj RST n' i'
      in
        Const (@{const_name "All"}, dummyT) $ absdummy dummyT
          (HOLogic.mk_imp (HOLogic.mk_eq(x, injs), HOLogic.mk_eq(projs, y)))
      end

    val goal_inj = Logic.mk_implies (G_aux_prem,
      HOLogic.mk_Trueprop (fold_conj (map mk_inj_goal parts)))
      |> all x |> all y
      |> Syntax.check_term lthy'''
    val goal_iff1 = Logic.mk_implies (G_aux_prem, G_prem)
      |> all x |> all y
    val goal_iff2 = Logic.mk_implies (G_prem, G_aux_prem)
      |> all x |> all y

    val simp_thms = @{thms sum.sel sum.inject sum.case sum.distinct o_apply}
    val simpset0 = put_simpset HOL_basic_ss lthy''' addsimps simp_thms
    val simpset1 = put_simpset HOL_ss lthy''' addsimps simp_thms

    val inj_thm = Goal.prove lthy''' [] [] goal_inj
      (K (HEADGOAL (DETERM o eresolve_tac lthy''' [G_aux_induct]
        THEN_ALL_NEW asm_simp_tac simpset1)))

    fun aux_tac thm =
      resolve_tac lthy''' [Variable.gen_all lthy''' thm] THEN_ALL_NEW
      asm_full_simp_tac (simpset1 addsimps [inj_thm])

    val iff1_thm = Goal.prove lthy''' [] [] goal_iff1
      (K (HEADGOAL (DETERM o eresolve_tac lthy''' [G_aux_induct]
        THEN' RANGE (map aux_tac GIntro_thms))))
      |> Variable.gen_all lthy'''
    val iff2_thm = Goal.prove lthy''' [] [] goal_iff2
      (K (HEADGOAL (DETERM o eresolve_tac lthy''' [G_induct] THEN' RANGE
        (map (aux_tac o simplify simpset0) GIntro_aux_thms))))
      |> Variable.gen_all lthy'''

    val iff_thm = Goal.prove lthy''' [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (G, G_aux)))
      (K (HEADGOAL (EVERY' ((map (resolve_tac lthy''' o single) @{thms ext ext iffI}) @
        [eresolve_tac lthy''' [iff2_thm], eresolve_tac lthy''' [iff1_thm]]))))

    val tac = HEADGOAL (simp_tac (put_simpset HOL_basic_ss lthy''' addsimps [iff_thm]))
    val goalstate' =
      case (SINGLE tac) goalstate of
        NONE => error "auxiliary equivalence proof failed"
      | SOME st => st
  in
    ((goalstate', mutual_cont), lthy''')
  end

end
