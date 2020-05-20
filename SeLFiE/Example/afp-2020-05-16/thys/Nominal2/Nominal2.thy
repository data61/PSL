theory Nominal2
imports
  Nominal2_Base Nominal2_Abs Nominal2_FCB
keywords
  "nominal_datatype" :: thy_defn and
  "nominal_function" "nominal_inductive" "nominal_termination" :: thy_goal_defn and
  "avoids" "binds"
begin

ML_file \<open>nominal_dt_data.ML\<close>
ML \<open>open Nominal_Dt_Data\<close>

ML_file \<open>nominal_dt_rawfuns.ML\<close>
ML \<open>open Nominal_Dt_RawFuns\<close>

ML_file \<open>nominal_dt_alpha.ML\<close>
ML \<open>open Nominal_Dt_Alpha\<close>

ML_file \<open>nominal_dt_quot.ML\<close>
ML \<open>open Nominal_Dt_Quot\<close>

(*****************************************)
(* setup for induction principles method *)
ML_file \<open>nominal_induct.ML\<close>
method_setup nominal_induct =
  \<open>NominalInduct.nominal_induct_method\<close>
  \<open>nominal induction\<close>

(****************************************************)
(* inductive definition involving nominal datatypes *)
ML_file \<open>nominal_inductive.ML\<close>


(***************************************)
(* forked code of the function package *)
(* for defining nominal functions      *)
ML_file \<open>nominal_function_common.ML\<close>
ML_file \<open>nominal_function_core.ML\<close>
ML_file \<open>nominal_mutual.ML\<close>
ML_file \<open>nominal_function.ML\<close>
ML_file \<open>nominal_termination.ML\<close>

ML \<open>
val eqvt_attr = Attrib.internal (K Nominal_ThmDecls.eqvt_add)
val simp_attr = Attrib.internal (K Simplifier.simp_add)
val induct_attr = Attrib.internal (K Induct.induct_simp_add)
\<close>

section\<open>Interface for \<open>nominal_datatype\<close>\<close>

ML \<open>
fun get_cnstrs dts =
  map snd dts

fun get_typed_cnstrs dts =
  flat (map (fn ((bn, _, _), constrs) =>
   (map (fn (bn', _, _) => (Binding.name_of bn, Binding.name_of bn')) constrs)) dts)

fun get_cnstr_strs dts =
  map (fn (bn, _, _) => Binding.name_of bn) (flat (get_cnstrs dts))

fun get_bn_fun_strs bn_funs =
  map (fn (bn_fun, _, _) => Binding.name_of bn_fun) bn_funs
\<close>


text \<open>Infrastructure for adding \<open>_raw\<close> to types and terms\<close>

ML \<open>
fun add_raw s = s ^ "_raw"
fun add_raws ss = map add_raw ss
fun raw_bind bn = Binding.suffix_name "_raw" bn

fun replace_str ss s =
  case (AList.lookup (op =) ss s) of
     SOME s' => s'
   | NONE => s

fun replace_typ ty_ss (Type (a, Ts)) = Type (replace_str ty_ss a, map (replace_typ ty_ss) Ts)
  | replace_typ ty_ss T = T

fun raw_dts ty_ss dts =
let
  fun raw_dts_aux1 (bind, tys, _) =
    (raw_bind bind, map (replace_typ ty_ss) tys, NoSyn)

  fun raw_dts_aux2 ((bind, ty_args, _), constrs) =
    ((raw_bind bind, ty_args, NoSyn), map raw_dts_aux1 constrs)
in
  map raw_dts_aux2 dts
end

fun replace_aterm trm_ss (Const (a, T)) = Const (replace_str trm_ss a, T)
  | replace_aterm trm_ss (Free (a, T)) = Free (replace_str trm_ss a, T)
  | replace_aterm trm_ss trm = trm

fun replace_term trm_ss ty_ss trm =
  trm |> Term.map_aterms (replace_aterm trm_ss) |> map_types (replace_typ ty_ss)
\<close>

ML \<open>
fun rawify_dts dts dts_env = raw_dts dts_env dts
\<close>

ML \<open>
fun rawify_bn_funs dts_env cnstrs_env bn_fun_env bn_funs bn_eqs =
let
  val bn_funs' = map (fn (bn, ty, _) =>
    (raw_bind bn, SOME (replace_typ dts_env ty), NoSyn)) bn_funs

  val bn_eqs' = map (fn (attr, trm) =>
    ((attr, replace_term (cnstrs_env @ bn_fun_env) dts_env trm), [], [])) bn_eqs
in
  (bn_funs', bn_eqs')
end
\<close>

ML \<open>
fun rawify_bclauses dts_env cnstrs_env bn_fun_env bclauses =
let
  fun rawify_bnds bnds =
    map (apfst (Option.map (replace_term (cnstrs_env @ bn_fun_env) dts_env))) bnds

  fun rawify_bclause (BC (mode, bnds, bdys)) = BC (mode, rawify_bnds bnds, bdys)
in
  (map o map o map) rawify_bclause bclauses
end
\<close>


ML \<open>
(* definition of the raw datatype *)

fun define_raw_dts dts cnstr_names cnstr_tys bn_funs bn_eqs bclauses lthy =
let
  val thy = Local_Theory.exit_global lthy
  val thy_name = Context.theory_name thy

  val dt_names = map (fn ((s, _, _), _) => Binding.name_of s) dts
  val dt_full_names = map (Long_Name.qualify thy_name) dt_names
  val dt_full_names' = add_raws dt_full_names
  val dts_env = dt_full_names ~~ dt_full_names'

  val cnstr_full_names = map (Long_Name.qualify thy_name) cnstr_names
  val cnstr_full_names' = map (fn (x, y) => Long_Name.qualify thy_name
    (Long_Name.qualify (add_raw x) (add_raw y))) cnstr_tys
  val cnstrs_env = cnstr_full_names ~~ cnstr_full_names'

  val bn_fun_strs = get_bn_fun_strs bn_funs
  val bn_fun_strs' = add_raws bn_fun_strs
  val bn_fun_env = bn_fun_strs ~~ bn_fun_strs'
  val bn_fun_full_env = map (apply2 (Long_Name.qualify thy_name))
    (bn_fun_strs ~~ bn_fun_strs')

  val raw_dts = rawify_dts dts dts_env
  val (raw_bn_funs, raw_bn_eqs) = rawify_bn_funs dts_env cnstrs_env bn_fun_env bn_funs bn_eqs
  val raw_bclauses = rawify_bclauses dts_env cnstrs_env bn_fun_full_env bclauses

  val (raw_full_dt_names', thy1) =
    BNF_LFP_Compat.add_datatype [BNF_LFP_Compat.Kill_Type_Args] raw_dts thy

  val lthy1 = Named_Target.theory_init thy1

  val dtinfos = map (Old_Datatype_Data.the_info (Proof_Context.theory_of lthy1)) raw_full_dt_names'
  val raw_fp_sugars = map (the o BNF_FP_Def_Sugar.fp_sugar_of lthy1) raw_full_dt_names'
  val {descr, ...} = hd dtinfos

  val raw_ty_args = hd (Old_Datatype_Aux.get_rec_types descr)
    |> snd o dest_Type
    |> map dest_TFree
  val raw_schematic_ty_args = (snd o dest_Type o #T o hd) raw_fp_sugars
  val typ_subst = raw_schematic_ty_args ~~ map TFree raw_ty_args
  val freezeT = Term.typ_subst_atomic typ_subst
  val freeze = Term.subst_atomic_types typ_subst
  val raw_tys = map (freezeT o #T) raw_fp_sugars

  val raw_cns_info = all_dtyp_constrs_types descr
  val raw_all_cns = map (map freeze o #ctrs o #ctr_sugar o #fp_ctr_sugar) raw_fp_sugars

  val raw_inject_thms = flat (map #inject dtinfos)
  val raw_distinct_thms = flat (map #distinct dtinfos)
  val raw_induct_thm = (hd o #common_co_inducts o the o #fp_co_induct_sugar o hd) raw_fp_sugars
  val raw_induct_thms = map (the_single o #co_inducts o the o #fp_co_induct_sugar) raw_fp_sugars
  val raw_exhaust_thms = map #exhaust dtinfos
  val raw_size_trms = map HOLogic.size_const raw_tys
  val raw_size_thms = these (Option.map (#2 o #2)
    (BNF_LFP_Size.size_of lthy1 (hd raw_full_dt_names')))

  val raw_result = RawDtInfo
    {raw_dt_names = raw_full_dt_names',
     raw_fp_sugars = raw_fp_sugars,
     raw_dts = raw_dts,
     raw_tys = raw_tys,
     raw_ty_args = raw_ty_args,
     raw_cns_info = raw_cns_info,
     raw_all_cns = raw_all_cns,
     raw_inject_thms = raw_inject_thms,
     raw_distinct_thms = raw_distinct_thms,
     raw_induct_thm = raw_induct_thm,
     raw_induct_thms = raw_induct_thms,
     raw_exhaust_thms = raw_exhaust_thms,
     raw_size_trms = raw_size_trms,
     raw_size_thms = raw_size_thms}
in
  (raw_bclauses, raw_bn_funs, raw_bn_eqs, raw_result, lthy1)
end
\<close>


ML \<open>
fun nominal_datatype2 opt_thms_name dts bn_funs bn_eqs bclauses lthy =
let
  val cnstr_names = get_cnstr_strs dts
  val cnstr_tys = get_typed_cnstrs dts

  val _ = trace_msg (K "Defining raw datatypes...")
  val (raw_bclauses, raw_bn_funs, raw_bn_eqs, raw_dt_info, lthy0) =
    define_raw_dts dts cnstr_names cnstr_tys bn_funs bn_eqs bclauses lthy

  val RawDtInfo
    {raw_dt_names,
     raw_tys,
     raw_ty_args,
     raw_fp_sugars,
     raw_all_cns,
     raw_inject_thms,
     raw_distinct_thms,
     raw_induct_thm,
     raw_induct_thms,
     raw_exhaust_thms,
     raw_size_trms,
     raw_size_thms, ...} = raw_dt_info

  val _ = trace_msg (K "Defining raw permutations...")
  val ((raw_perm_funs, raw_perm_simps, raw_perm_laws), lthy2a) = define_raw_perms raw_dt_info lthy0

  (* noting the raw permutations as eqvt theorems *)
  val lthy3 = snd (Local_Theory.note ((Binding.empty, [eqvt_attr]), raw_perm_simps) lthy2a)

  val _ = trace_msg (K "Defining raw fv- and bn-functions...")
  val (raw_bns, raw_bn_defs, raw_bn_info, raw_bn_inducts, lthy3a) =
    define_raw_bns raw_dt_info raw_bn_funs raw_bn_eqs lthy3

  (* defining the permute_bn functions *)
  val (raw_perm_bns, raw_perm_bn_simps, lthy3b) =
    define_raw_bn_perms raw_dt_info raw_bn_info lthy3a

  val (raw_fvs, raw_fv_bns, raw_fv_defs, raw_fv_bns_induct, lthy3c) =
    define_raw_fvs raw_dt_info raw_bn_info raw_bclauses lthy3b

  val _ = trace_msg (K "Defining alpha relations...")
  val (alpha_result, lthy4) =
    define_raw_alpha raw_dt_info raw_bn_info raw_bclauses raw_fvs lthy3c

  val _ = trace_msg (K "Proving distinct theorems...")
  val alpha_distincts = raw_prove_alpha_distincts lthy4 alpha_result raw_dt_info

  val _ = trace_msg (K "Proving eq-iff theorems...")
  val alpha_eq_iff = raw_prove_alpha_eq_iff lthy4 alpha_result raw_dt_info

  val _ = trace_msg (K "Proving equivariance of bns, fvs, size and alpha...")
  val raw_bn_eqvt =
    raw_prove_eqvt raw_bns raw_bn_inducts (raw_bn_defs @ raw_perm_simps) lthy4

  (* noting the raw_bn_eqvt lemmas in a temprorary theory *)
  val lthy_tmp = Local_Theory.subtarget
    (Local_Theory.note ((Binding.empty, [eqvt_attr]), raw_bn_eqvt) #> snd) lthy4

  val raw_fv_eqvt =
    raw_prove_eqvt (raw_fvs @ raw_fv_bns) raw_fv_bns_induct (raw_fv_defs @ raw_perm_simps)
      lthy_tmp

  val raw_size_eqvt =
    let
      val RawDtInfo {raw_size_trms, raw_size_thms, raw_induct_thms, ...} = raw_dt_info
    in
      raw_prove_eqvt raw_size_trms raw_induct_thms (raw_size_thms @ raw_perm_simps)
        lthy_tmp
        |> map (rewrite_rule lthy_tmp
            @{thms permute_nat_def[THEN eq_reflection]})
        |> map (fn thm => thm RS @{thm sym})
    end

  val lthy5 = snd (Local_Theory.note ((Binding.empty, [eqvt_attr]), raw_fv_eqvt) lthy_tmp)

  val alpha_eqvt =
    let
      val AlphaResult {alpha_trms, alpha_bn_trms, alpha_raw_induct, alpha_intros, ...} = alpha_result
    in
      Nominal_Eqvt.raw_equivariance lthy5 (alpha_trms @ alpha_bn_trms) alpha_raw_induct alpha_intros
    end

  val alpha_eqvt_norm = map (Nominal_ThmDecls.eqvt_transform lthy5) alpha_eqvt

  val _ = trace_msg (K "Proving equivalence of alpha...")
  val alpha_refl_thms = raw_prove_refl lthy5 alpha_result raw_induct_thm
  val alpha_sym_thms = raw_prove_sym lthy5 alpha_result alpha_eqvt_norm
  val alpha_trans_thms =
    raw_prove_trans lthy5 alpha_result (raw_distinct_thms @ raw_inject_thms) alpha_eqvt_norm

  val (alpha_equivp_thms, alpha_bn_equivp_thms) =
    raw_prove_equivp lthy5 alpha_result alpha_refl_thms alpha_sym_thms alpha_trans_thms

  val _ = trace_msg (K "Proving alpha implies bn...")
  val alpha_bn_imp_thms = raw_prove_bn_imp lthy5 alpha_result

  val _ = trace_msg (K "Proving respectfulness...")
  val raw_funs_rsp_aux =
    raw_fv_bn_rsp_aux lthy5 alpha_result raw_fvs raw_bns raw_fv_bns (raw_bn_defs @ raw_fv_defs)

  val raw_funs_rsp = map (Drule.eta_contraction_rule o mk_funs_rsp lthy5) raw_funs_rsp_aux

  fun match_const cnst th =
    (fst o dest_Const o snd o dest_comb o HOLogic.dest_Trueprop o Thm.prop_of) th =
    fst (dest_Const cnst);
  fun find_matching_rsp cnst =
    hd (filter (fn th => match_const cnst th) raw_funs_rsp);
  val raw_fv_rsp = map find_matching_rsp raw_fvs;
  val raw_bn_rsp = map find_matching_rsp raw_bns;
  val raw_fv_bn_rsp = map find_matching_rsp raw_fv_bns;

  val raw_size_rsp =
    raw_size_rsp_aux lthy5 alpha_result (raw_size_thms @ raw_size_eqvt)
      |> map (mk_funs_rsp lthy5)

  val raw_constrs_rsp =
    raw_constrs_rsp lthy5 alpha_result raw_all_cns (alpha_bn_imp_thms @ raw_funs_rsp_aux)

  val alpha_permute_rsp = map (mk_alpha_permute_rsp lthy5) alpha_eqvt

  val alpha_bn_rsp =
    raw_alpha_bn_rsp alpha_result alpha_bn_equivp_thms alpha_bn_imp_thms

  val raw_perm_bn_rsp = raw_perm_bn_rsp lthy5 alpha_result raw_perm_bns raw_perm_bn_simps

  val _ = trace_msg (K "Defining the quotient types...")
  val qty_descr = map (fn ((bind, vs, mx), _) => (map fst vs, bind, mx)) dts

  val (qty_infos, lthy7) =
    let
      val AlphaResult {alpha_trms, alpha_tys, ...} = alpha_result
    in
      define_qtypes qty_descr alpha_tys alpha_trms alpha_equivp_thms lthy5
    end

  val qtys = map #qtyp qty_infos
  val qty_full_names = map (fst o dest_Type) qtys
  val qty_names = map Long_Name.base_name qty_full_names

  val _ = trace_msg (K "Defining the quotient constants...")
  val qconstrs_descrs =
    (map2 o map2) (fn (b, _, mx) => fn (t, th) => (Variable.check_name b, t, mx, th))
      (get_cnstrs dts) (map (op ~~) (raw_all_cns ~~ raw_constrs_rsp))

  val qbns_descr =
    map2 (fn (b, _, mx) => fn (t, th) => (Variable.check_name b, t, mx, th)) bn_funs (raw_bns ~~ raw_bn_rsp)

  val qfvs_descr =
    map2 (fn n => fn (t, th) => ("fv_" ^ n, t, NoSyn, th)) qty_names (raw_fvs ~~ raw_fv_rsp)

  val qfv_bns_descr =
    map2 (fn (b, _, _) => fn (t, th) => ("fv_" ^ Variable.check_name b, t, NoSyn, th))
      bn_funs (raw_fv_bns ~~ raw_fv_bn_rsp)

  val qalpha_bns_descr =
    let
      val AlphaResult {alpha_bn_trms, ...} = alpha_result
    in
      map2 (fn (b, _, _) => fn (t, th) => ("alpha_" ^ Variable.check_name b, t, NoSyn, th))
        bn_funs (alpha_bn_trms ~~ alpha_bn_rsp)
    end

  val qperm_descr =
    map2 (fn n => fn (t, th) => ("permute_" ^ n, Type.legacy_freeze t, NoSyn, th))
      qty_names (raw_perm_funs ~~ (take (length raw_perm_funs) alpha_permute_rsp))

  val qsize_descr =
    map2 (fn n => fn (t, th) => ("size_" ^ n, t, NoSyn, th)) qty_names
      (raw_size_trms ~~ (take (length raw_size_trms) raw_size_rsp))

  val qperm_bn_descr =
    map2 (fn (b, _, _) => fn (t, th) => ("permute_" ^ Variable.check_name b, t, NoSyn, th))
      bn_funs (raw_perm_bns ~~ raw_perm_bn_rsp)

  val ((((((qconstrs_infos, qbns_info), qfvs_info), qfv_bns_info), qalpha_bns_info), qperm_bns_info),
    lthy8) =
      lthy7
      |> fold_map (define_qconsts qtys) qconstrs_descrs
      ||>> define_qconsts qtys qbns_descr
      ||>> define_qconsts qtys qfvs_descr
      ||>> define_qconsts qtys qfv_bns_descr
      ||>> define_qconsts qtys qalpha_bns_descr
      ||>> define_qconsts qtys qperm_bn_descr

  val lthy9 =
    define_qperms qtys qty_full_names raw_ty_args qperm_descr raw_perm_laws lthy8

  val lthy9a =
    define_qsizes qtys qty_full_names raw_ty_args qsize_descr lthy9

  val qtrms = (map o map) #qconst qconstrs_infos
  val qbns = map #qconst qbns_info
  val qfvs = map #qconst qfvs_info
  val qfv_bns = map #qconst qfv_bns_info
  val qalpha_bns = map #qconst qalpha_bns_info
  val qperm_bns = map #qconst qperm_bns_info

  val _ = trace_msg (K "Lifting of theorems...")
  val eq_iff_simps = @{thms alphas permute_prod.simps prod_fv.simps prod_alpha_def rel_prod_sel
    prod.case}

  val ([ qdistincts, qeq_iffs, qfv_defs, qbn_defs, qperm_simps, qfv_qbn_eqvts,
         qbn_inducts, qsize_eqvt, [qinduct], qexhausts, qsize_simps, qperm_bn_simps,
         qalpha_refl_thms, qalpha_sym_thms, qalpha_trans_thms ], lthyB) =
    lthy9a
    |>>> lift_thms qtys [] alpha_distincts
    ||>>> lift_thms qtys eq_iff_simps alpha_eq_iff
    ||>>> lift_thms qtys [] raw_fv_defs
    ||>>> lift_thms qtys [] raw_bn_defs
    ||>>> lift_thms qtys [] raw_perm_simps
    ||>>> lift_thms qtys [] (raw_fv_eqvt @ raw_bn_eqvt)
    ||>>> lift_thms qtys [] raw_bn_inducts
    ||>>> lift_thms qtys [] raw_size_eqvt
    ||>>> lift_thms qtys [] [raw_induct_thm]
    ||>>> lift_thms qtys [] raw_exhaust_thms
    ||>>> lift_thms qtys [] raw_size_thms
    ||>>> lift_thms qtys [] raw_perm_bn_simps
    ||>>> lift_thms qtys [] alpha_refl_thms
    ||>>> lift_thms qtys [] alpha_sym_thms
    ||>>> lift_thms qtys [] alpha_trans_thms

  val qinducts = Project_Rule.projections lthyB qinduct

  val _ = trace_msg (K "Proving supp lemmas and fs-instances...")
  val qsupports_thms = prove_supports lthyB qperm_simps (flat qtrms)

  (* finite supp lemmas *)
  val qfsupp_thms = prove_fsupp lthyB qtys qinduct qsupports_thms

  (* fs instances *)
  val lthyC = fs_instance qtys qty_full_names raw_ty_args qfsupp_thms lthyB

  val _ = trace_msg (K "Proving equality between fv and supp...")
  val qfv_supp_thms =
    prove_fv_supp qtys (flat qtrms) qfvs qfv_bns qalpha_bns qfv_defs qeq_iffs
      qperm_simps qfv_qbn_eqvts qinduct (flat raw_bclauses) lthyC
    |> map Drule.eta_contraction_rule

  (* postprocessing of eq and fv theorems *)
  val qeq_iffs' = qeq_iffs
    |> map (simplify (put_simpset HOL_basic_ss lthyC addsimps qfv_supp_thms))
    |> map (simplify (put_simpset HOL_basic_ss lthyC
        addsimps @{thms prod_fv_supp prod_alpha_eq Abs_eq_iff[symmetric]}))

  (* filters the theorems that are of the form "qfv = supp" *)
  val qfv_names = map (fst o dest_Const) qfvs
  fun is_qfv_thm (@{term Trueprop} $ (Const (@{const_name HOL.eq}, _) $ Const (lhs, _) $ _)) =
    member (op =) qfv_names lhs
  | is_qfv_thm _ = false

  val qsupp_constrs = qfv_defs
    |> map (simplify (put_simpset HOL_basic_ss lthyC
        addsimps (filter (is_qfv_thm o Thm.prop_of) qfv_supp_thms)))

  val transform_thm = @{lemma "x = y \<Longrightarrow> a \<notin> x \<longleftrightarrow> a \<notin> y" by simp}
  val transform_thms =
    [ @{lemma "a \<notin> (S \<union> T) \<longleftrightarrow> a \<notin> S \<and> a \<notin> T" by simp},
      @{lemma "a \<notin> (S - T) \<longleftrightarrow> a \<notin> S \<or> a \<in> T" by simp},
      @{lemma "(lhs = (a \<notin> {})) \<longleftrightarrow> lhs" by simp},
      @{thm fresh_def[symmetric]}]

  val qfresh_constrs = qsupp_constrs
    |> map (fn thm => thm RS transform_thm)
    |> map (simplify (put_simpset HOL_basic_ss lthyC addsimps transform_thms))

  (* proving that the qbn result is finite *)
  val qbn_finite_thms = prove_bns_finite qtys qbns qinduct qbn_defs lthyC

  (* proving that perm_bns preserve alpha *)
  val qperm_bn_alpha_thms =
    prove_perm_bn_alpha_thms qtys qperm_bns qalpha_bns qinduct qperm_bn_simps qeq_iffs'
      qalpha_refl_thms lthyC

  (* proving the relationship of bn and permute_bn *)
  val qpermute_bn_thms =
    prove_permute_bn_thms qtys qbns qperm_bns qinduct qperm_bn_simps qbn_defs qfv_qbn_eqvts lthyC

  val _ = trace_msg (K "Proving strong exhaust lemmas...")
  val qstrong_exhaust_thms = prove_strong_exhausts lthyC qexhausts bclauses qbn_finite_thms qeq_iffs'
    qfv_qbn_eqvts qpermute_bn_thms qperm_bn_alpha_thms

  val _ = trace_msg (K "Proving strong induct lemmas...")
  val qstrong_induct_thms =  prove_strong_induct lthyC qinduct qstrong_exhaust_thms qsize_simps bclauses

  (* noting the theorems *)

  (* generating the prefix for the theorem names *)
  val thms_name =
    the_default (Binding.name (space_implode "_" qty_names)) opt_thms_name
  fun thms_suffix s = Binding.qualify_name true thms_name s
  val case_names_attr = Attrib.internal (K (Rule_Cases.case_names cnstr_names))

  val infos = mk_infos qty_full_names qeq_iffs' qdistincts qstrong_exhaust_thms qstrong_induct_thms

  val (_, lthy9') = lthyC
     |> Local_Theory.declaration {syntax = false, pervasive = false} (K (fold register_info infos))
     |> Local_Theory.note ((thms_suffix "distinct", [induct_attr, simp_attr]), qdistincts)
     ||>> Local_Theory.note ((thms_suffix "eq_iff", [induct_attr, simp_attr]), qeq_iffs')
     ||>> Local_Theory.note ((thms_suffix "fv_defs", []), qfv_defs)
     ||>> Local_Theory.note ((thms_suffix "bn_defs", []), qbn_defs)
     ||>> Local_Theory.note ((thms_suffix "bn_inducts", []), qbn_inducts)
     ||>> Local_Theory.note ((thms_suffix "perm_simps", [eqvt_attr, simp_attr]), qperm_simps)
     ||>> Local_Theory.note ((thms_suffix "fv_bn_eqvt", [eqvt_attr]), qfv_qbn_eqvts)
     ||>> Local_Theory.note ((thms_suffix "size", [simp_attr]), qsize_simps)
     ||>> Local_Theory.note ((thms_suffix "size_eqvt", []), qsize_eqvt)
     ||>> Local_Theory.note ((thms_suffix "induct", [case_names_attr]), [qinduct])
     ||>> Local_Theory.note ((thms_suffix "inducts", [case_names_attr]), qinducts)
     ||>> Local_Theory.note ((thms_suffix "exhaust", [case_names_attr]), qexhausts)
     ||>> Local_Theory.note ((thms_suffix "strong_exhaust", [case_names_attr]), qstrong_exhaust_thms)
     ||>> Local_Theory.note ((thms_suffix "strong_induct", [case_names_attr]), qstrong_induct_thms)
     ||>> Local_Theory.note ((thms_suffix "supports", []), qsupports_thms)
     ||>> Local_Theory.note ((thms_suffix "fsupp", []), qfsupp_thms)
     ||>> Local_Theory.note ((thms_suffix "supp", []), qsupp_constrs)
     ||>> Local_Theory.note ((thms_suffix "fresh", [simp_attr]), qfresh_constrs)
     ||>> Local_Theory.note ((thms_suffix "perm_bn_simps", []), qperm_bn_simps)
     ||>> Local_Theory.note ((thms_suffix "bn_finite", []), qbn_finite_thms)
     ||>> Local_Theory.note ((thms_suffix "perm_bn_alpha", []), qperm_bn_alpha_thms)
     ||>> Local_Theory.note ((thms_suffix "permute_bn", []), qpermute_bn_thms)
     ||>> Local_Theory.note ((thms_suffix "alpha_refl", []), qalpha_refl_thms)
     ||>> Local_Theory.note ((thms_suffix "alpha_sym", []), qalpha_sym_thms)
     ||>> Local_Theory.note ((thms_suffix "alpha_trans", []), qalpha_trans_thms)

in
  lthy9'
end
\<close>


section \<open>Preparing and parsing of the specification\<close>

ML \<open>
(* adds the default sort @{sort fs} to nominal specifications *)

fun augment_sort thy S = Sign.inter_sort thy (@{sort fs}, S)

fun augment_sort_typ thy =
  map_type_tfree (fn (s, S) => TFree (s, augment_sort thy S))
\<close>

ML \<open>
(* generates the parsed datatypes and declares the constructors *)

fun prepare_dts dt_strs thy =
let
  fun prep_spec ((tname, tvs, mx), constrs) =
    ((tname, tvs, mx), constrs |> map (fn (c, atys, mx', _) => (c, map snd atys, mx')))

  val (dts, spec_ctxt) =
    Old_Datatype.read_specs (map prep_spec dt_strs) thy

  fun augment ((tname, tvs, mx), constrs) =
    ((tname, map (apsnd (augment_sort thy)) tvs, mx),
      constrs |> map (fn (c, tys, mx') => (c, map (augment_sort_typ thy) tys, mx')))

  val dts' = map augment dts

  fun mk_constr_trms ((tname, tvs, _), constrs) =
    let
      val ty = Type (Sign.full_name thy tname, map TFree tvs)
    in
      map (fn (c, tys, mx) => (c, (tys ---> ty), mx)) constrs
    end

  val constr_trms = flat (map mk_constr_trms dts')

  (* FIXME: local version *)
  (* val (_, spec_ctxt') = Proof_Context.add_fixes constr_trms spec_ctxt *)

  val thy' = Sign.add_consts constr_trms (Proof_Context.theory_of spec_ctxt)
in
  (dts', thy')
end
\<close>

ML \<open>
(* parsing the binding function specifications and *)
(* declaring the function constants                *)
fun prepare_bn_funs bn_fun_strs bn_eq_strs thy =
let
  val lthy = Named_Target.theory_init thy

  val ((bn_funs, bn_eqs), lthy') =
    Specification.read_multi_specs bn_fun_strs bn_eq_strs lthy

  fun prep_bn_fun ((bn, T), mx) = (bn, T, mx)

  val bn_funs' = map prep_bn_fun bn_funs

in
  (Local_Theory.exit_global lthy')
  |> Sign.add_consts bn_funs'
  |> pair (bn_funs', bn_eqs)
end
\<close>

text \<open>associates every SOME with the index in the list; drops NONEs\<close>
ML \<open>
fun indexify xs =
let
  fun mapp _ [] = []
    | mapp i (NONE :: xs) = mapp (i + 1) xs
    | mapp i (SOME x :: xs) = (x, i) :: mapp (i + 1) xs
in
  mapp 0 xs
end

fun index_lookup xs x =
  case AList.lookup ((=)) xs x of
    SOME x => x
  | NONE => error ("Cannot find " ^ x ^ " as argument annotation.");
\<close>

ML \<open>
fun prepare_bclauses dt_strs thy =
let
  val annos_bclauses =
    get_cnstrs dt_strs
    |> (map o map) (fn (_, antys, _, bns) => (map fst antys, bns))

  fun prep_binder env bn_str =
    case (Syntax.read_term_global thy bn_str) of
      Free (x, _) => (NONE, index_lookup env x)
    | Const (a, T) $ Free (x, _) => (SOME (Const (a, T)), index_lookup env x)
    | _ => error ("The term " ^ bn_str ^ " is not allowed as binding function.")

  fun prep_body env bn_str = index_lookup env bn_str

  fun prep_bclause env (mode, binders, bodies) =
  let
    val binders' = map (prep_binder env) binders
    val bodies' = map (prep_body env) bodies
  in
    BC (mode, binders', bodies')
  end

  fun prep_bclauses (annos, bclause_strs) =
  let
    val env = indexify annos (* for every label, associate the index *)
  in
    map (prep_bclause env) bclause_strs
  end
in
  ((map o map) prep_bclauses annos_bclauses, thy)
end
\<close>

text \<open>
  adds an empty binding clause for every argument
  that is not already part of a binding clause
\<close>

ML \<open>
fun included i bcs =
let
  fun incl (BC (_, bns, bds)) =
    member (op =) (map snd bns) i orelse member (=) bds i
in
  exists incl bcs
end
\<close>

ML \<open>
fun complete dt_strs bclauses =
let
  val args =
    get_cnstrs dt_strs
    |> (map o map) (fn (_, antys, _, _) => length antys)

  fun complt n bcs =
  let
    fun add bcs i = (if included i bcs then [] else [BC (Lst, [], [i])])
  in
    bcs @ (flat (map_range (add bcs) n))
  end
in
  (map2 o map2) complt args bclauses
end
\<close>

ML \<open>
fun nominal_datatype2_cmd (opt_thms_name, dt_strs, bn_fun_strs, bn_eq_strs) lthy =
let
  (* this theory is used just for parsing *)
  val thy = Proof_Context.theory_of lthy

  val (((dts, (bn_funs, bn_eqs)), bclauses), _) =
    thy
    |> prepare_dts dt_strs
    ||>> prepare_bn_funs bn_fun_strs bn_eq_strs
    ||>> prepare_bclauses dt_strs

  val bclauses' = complete dt_strs bclauses
in
  nominal_datatype2 opt_thms_name dts bn_funs bn_eqs bclauses' lthy
end
\<close>

ML \<open>
(* nominal datatype parser *)
local
  fun triple1 ((x, y), z) = (x, y, z)
  fun triple2 ((x, y), z) = (y, x, z)
  fun tuple2 (((x, y), z), u) = (x, y, u, z)
  fun tuple3 ((x, y), (z, u)) = (x, y, z, u)
in

val opt_name = Scan.option (Parse.binding --| Args.colon)

val anno_typ = Scan.option (Parse.name --| @{keyword "::"}) -- Parse.typ

val bind_mode = @{keyword "binds"} |--
  Scan.optional (Args.parens
    (Args.$$$ "list" >> K Lst || (Args.$$$ "set" -- Args.$$$ "+") >> K Res || Args.$$$ "set" >> K Set)) Lst

val bind_clauses =
  Parse.enum "," (bind_mode -- Scan.repeat1 Parse.term -- (@{keyword "in"} |-- Scan.repeat1 Parse.name) >> triple1)

val cnstr_parser =
  Parse.binding -- Scan.repeat anno_typ -- bind_clauses -- Parse.opt_mixfix >> tuple2

(* datatype parser *)
val dt_parser =
  (Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix >> triple2) --
    (@{keyword "="} |-- Parse.enum1 "|" cnstr_parser)

(* binding function parser *)
val bnfun_parser =
  Scan.optional (@{keyword "binder"} |-- Parse_Spec.specification) ([], [])

(* main parser *)
val main_parser =
  opt_name -- Parse.and_list1 dt_parser -- bnfun_parser >> tuple3

end

(* Command Keyword *)
val _ = Outer_Syntax.local_theory @{command_keyword nominal_datatype}
  "declaration of nominal datatypes"
    (main_parser >> nominal_datatype2_cmd)
\<close>

end
