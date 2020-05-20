section \<open>Actual Implementation of the CAVA Model Checker\<close>
theory CAVA_Impl
imports
  CAVA_Abstract
  CAVA_Automata.Automata_Impl

  LTL.Rewriting

  LTL_to_GBA.LTL_to_GBA_impl (* LTL to BA *)

  Gabow_SCC.Gabow_GBG_Code (* Gabow's Algorithm *)
  "Nested_DFS/NDFS_SI" (* Nested-DFS, standard-invars formalization *)

  "BoolProgs/BoolProgs"                   (* Boolean Programs *)
  "BoolProgs/Programs/BoolProgs_Programs" (* the actual programs *)
  "BoolProgs/BoolProgs_LTL_Conv"          (* LTL parsing setup *)

  Promela.PromelaLTL     (* Promela *)
  Promela.PromelaLTLConv (* LTL parsing setup *)

  "HOL-Library.AList_Mapping"
  CAVA_Base.CAVA_Code_Target
  SM.SM_Wrapup
begin

hide_const (open) SM_Cfg.cfg

subsection \<open>Miscellaneous Lemmata\<close>

(* TODO: Move *)
instantiation uint32 :: hashable begin
  definition "hashcode x = x"
  definition "def_hashmap_size (T::uint32 itself) \<equiv> 8"  
  
  instance
    apply intro_classes
    unfolding def_hashmap_size_uint32_def
    by auto

end

(*<*)
subsection \<open>Exporting Graphs\<close>

(* TODO: frv_export is going to be replaced by more explicit implementation 
  of graphs.
  For the moment, we just keep it here.
*)
definition "frv_edge_set G \<equiv> g_E G \<inter> (g_V G \<times> UNIV)"

definition "frv_edge_set_aimpl G \<equiv> FOREACHi (\<lambda>it r. r = g_E G \<inter> ((g_V G - it) \<times> UNIV))
  (g_V G) 
  (\<lambda>u r. do {
    let E = (\<lambda>v. (u,v))`(succ_of_E (g_E G) u);
    ASSERT (E \<inter> r = {});
    RETURN (E \<union> r)
  }) 
  {}"

lemma frv_edge_set_aimpl_correct: 
  "finite (g_V G) \<Longrightarrow> frv_edge_set_aimpl G \<le> SPEC (\<lambda>r. r = frv_edge_set G)"
  unfolding frv_edge_set_aimpl_def frv_edge_set_def
  apply (refine_rcg refine_vcg)
  apply auto []
  apply auto []
  apply (auto simp: succ_of_E_def) []
  apply auto []
  done

schematic_goal frv_edge_set_impl_aux:
  assumes [autoref_rules]: "(eq,(=))\<in>R \<rightarrow> R \<rightarrow> bool_rel"
  assumes [relator_props]: "single_valued R"
  shows "(?c, frv_edge_set_aimpl) \<in> \<langle>Rx,R\<rangle>frgv_impl_rel_ext \<rightarrow> \<langle>\<langle>R \<times>\<^sub>r R\<rangle>list_set_rel\<rangle>nres_rel"
  unfolding frv_edge_set_aimpl_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition frv_edge_set_impl uses frv_edge_set_impl_aux
lemmas [autoref_rules] = frv_edge_set_impl.refine[OF GEN_OP_D PREFER_sv_D]

schematic_goal frv_edge_set_code_aux: "RETURN ?c \<le> frv_edge_set_impl eq G"
  unfolding frv_edge_set_impl_def by (refine_transfer (post))
concrete_definition frv_edge_set_code for eq G uses frv_edge_set_code_aux
lemmas [refine_transfer] = frv_edge_set_code.refine

lemma frv_edge_set_autoref[autoref_rules]:
  assumes EQ[unfolded autoref_tag_defs]: "GEN_OP eq (=) (R \<rightarrow> R \<rightarrow> bool_rel)"
  assumes SV[unfolded autoref_tag_defs]: "PREFER single_valued R"
  shows "(frv_edge_set_code eq,frv_edge_set) \<in> \<langle>Rx,R\<rangle>frgv_impl_rel_ext \<rightarrow> \<langle>R \<times>\<^sub>r R\<rangle>list_set_rel"
proof (intro fun_relI)
  fix Gi G
  assume Gr: "(Gi, G) \<in> \<langle>Rx, R\<rangle>frgv_impl_rel_ext" 
  hence [simp]: "finite (g_V G)"
    unfolding frgv_impl_rel_ext_def g_impl_rel_ext_def
      gen_g_impl_rel_ext_def
    apply (simp add: list_set_rel_def br_def)
    apply fastforce
    done

  note frv_edge_set_code.refine
  also note frv_edge_set_impl.refine[OF EQ SV, THEN fun_relD, OF Gr, THEN nres_relD]
  also note frv_edge_set_aimpl_correct
  finally show "(frv_edge_set_code eq Gi, frv_edge_set G) \<in> \<langle>R \<times>\<^sub>r R\<rangle>list_set_rel" 
    by (rule RETURN_ref_SPECD) simp_all
qed

definition "frv_export G \<equiv> do {
  nodes \<leftarrow> SPEC (\<lambda>l. set l = g_V G \<and> distinct l);
  V0 \<leftarrow> SPEC (\<lambda>l. set l = g_V0 G \<and> distinct l);
  E \<leftarrow> SPEC (\<lambda>l. set l = frv_edge_set G \<and> distinct l);
  RETURN (nodes,V0,E)
  }"

schematic_goal frv_export_impl_aux:
  fixes R :: "('vi \<times> 'v) set"
  notes [autoref_tyrel] = TYRELI[where R = "\<langle>R \<times>\<^sub>r R\<rangle>list_set_rel"]
  assumes EQ[autoref_rules]: "(eq,(=))\<in>R \<rightarrow> R \<rightarrow> bool_rel"
  assumes SVR[relator_props]: "single_valued R"
  shows "(?c, frv_export) 
  \<in> \<langle>Rx,R\<rangle>frgv_impl_rel_ext 
  \<rightarrow> \<langle>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R \<times>\<^sub>r R\<rangle>list_rel\<rangle>nres_rel"
  unfolding frv_export_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (keep_goal, trace))
  done

concrete_definition frv_export_impl for eq uses frv_export_impl_aux
lemmas [autoref_rules] = frv_export_impl.refine[OF GEN_OP_D PREFER_sv_D]

schematic_goal frv_export_code_aux: "RETURN ?c \<le> frv_export_impl eq G"
  unfolding frv_export_impl_def
  apply (refine_transfer (post))
  done
concrete_definition frv_export_code for eq G uses frv_export_code_aux
lemmas [refine_transfer] = frv_export_code.refine

(*>*)

subsection \<open>Setup\<close>

subsubsection \<open>LTL to GBA conversion\<close>

text \<open>In the following, we set up the algorithms for LTL to GBA conversion.\<close>

definition is_ltl_to_gba_algo 
  :: "('a ltlc \<Rightarrow> (nat, 'a \<Rightarrow> bool, unit) igbav_impl_scheme) \<Rightarrow> bool"
  \<comment> \<open>Predicate that must be satisfied by an LTL to GBA conversion\<close>
  where 
  "is_ltl_to_gba_algo algo \<equiv> (algo, ltl_to_gba_spec) 
    \<in> ltl_rel 
    \<rightarrow> \<langle>igbav_impl_rel_ext unit_rel nat_rel (\<langle>Id\<rangle>fun_set_rel)\<rangle>plain_nres_rel"

definition gerth_ltl_to_gba 
  \<comment> \<open>Conversion based on Gerth's Algorithm\<close>
  where "gerth_ltl_to_gba \<phi> \<equiv> create_name_igba (ltln_to_ltlr (simplify Slow (ltlc_to_ltln \<phi>)))"

lemma gerth_ltl_to_gba_refine:
  "gerth_ltl_to_gba \<phi> \<le> \<Down>Id (ltl_to_gba_spec \<phi>)"
apply simp
unfolding ltl_to_gba_spec_def gerth_ltl_to_gba_def
apply (rule order_trans[OF create_name_igba_correct])
apply (rule SPEC_rule)
proof (safe del: equalityI)
  fix G :: "(nat, 'a set) igba_rec"
  assume "igba G"
  interpret igba G by fact
  assume 1: "finite (g_V G)"
  assume 2: "\<forall> \<xi>. accept \<xi> \<longleftrightarrow> \<xi> \<Turnstile>\<^sub>r ltln_to_ltlr (simplify Slow (ltlc_to_ltln \<phi>))"
  show "lang = language_ltlc \<phi>"
     using 2 unfolding lang_def language_ltlc_def ltln_to_ltlr_semantics simplify_correct ltlc_to_ltln_semantics by auto
  show "finite ((g_E G)\<^sup>* `` g_V0 G)" using 1 reachable_V by auto
qed

definition "gerth_ltl_to_gba_code \<phi> \<equiv> create_name_igba_code (ltln_to_ltlr (simplify Slow (ltlc_to_ltln \<phi>)))"
  
lemma gerth_ltl_to_gba_code_refine: "is_ltl_to_gba_algo gerth_ltl_to_gba_code"
proof -
  have "\<And>\<phi>. RETURN (gerth_ltl_to_gba_code \<phi>) 
    \<le> \<Down>(igbav_impl_rel_ext unit_rel nat_rel (\<langle>Id\<rangle>fun_set_rel)) 
      (gerth_ltl_to_gba \<phi>)"
    unfolding gerth_ltl_to_gba_def[abs_def] gerth_ltl_to_gba_code_def[abs_def]
    apply (rule order_trans[OF create_name_igba_code.refine])
    apply (rule create_name_igba_impl.refine[THEN fun_relD, THEN nres_relD])
    apply simp
    apply simp
    done
  also note gerth_ltl_to_gba_refine
  finally show ?thesis 
    unfolding is_ltl_to_gba_algo_def 
    by (blast intro: plain_nres_relI)
qed


text \<open>We define a function that chooses between the possible conversion 
  algorithms. (Currently there is only one)\<close>
datatype config_l2b = CFG_L2B_GERTHS

definition "ltl_to_gba_code cfg 
  \<equiv> case cfg of CFG_L2B_GERTHS \<Rightarrow> gerth_ltl_to_gba_code"

lemma ltl_to_gba_code_refine:
  "is_ltl_to_gba_algo (ltl_to_gba_code cfg)"
  apply (cases cfg)
  unfolding ltl_to_gba_code_def

  using gerth_ltl_to_gba_code_refine
  apply simp
  done

subsubsection \<open>Counterexample Search\<close>
definition is_find_ce_algo 
  :: "(('a, unit)igbg_impl_scheme \<Rightarrow> 'a lasso option option) \<Rightarrow> bool" 
  \<comment> \<open>Predicate that must be satisfied by counterexample search algorithm\<close>
  where
  "is_find_ce_algo algo \<equiv> (algo, find_ce_spec) 
    \<in> igbg_impl_rel_ext unit_rel Id 
  \<rightarrow> \<langle>\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel\<rangle>plain_nres_rel"

definition gabow_find_ce_code :: "_ \<Rightarrow> 'a::hashable lasso option option"
  \<comment> \<open>Emptiness check based on Gabow's SCC Algorithm\<close>
  where "gabow_find_ce_code
  \<equiv> map_option (Some o lasso_of_prpl) o Gabow_GBG_Code.find_lasso_tr (=) bounded_hashcode_nat (def_hashmap_size TYPE('a))"

lemma gabow_find_ce_code_refine: "is_find_ce_algo 
  (gabow_find_ce_code 
    :: ('a::hashable, unit) igbg_impl_scheme \<Rightarrow> 'a lasso option option)"
proof -
  have AUX_EQ: 
    "\<And>gbgi::('a, unit) igbg_impl_scheme. RETURN (gabow_find_ce_code gbgi)
    = (do {
      l \<leftarrow> RETURN (find_lasso_tr (=) bounded_hashcode_nat (def_hashmap_size TYPE('a)) gbgi);
      RETURN (map_option (Some \<circ> lasso_of_prpl) l)
    })" by (auto simp: gabow_find_ce_code_def)

  show ?thesis
    (* TODO: Clean up this proof! *)
    unfolding is_find_ce_algo_def 
    apply (intro fun_relI plain_nres_relI)
    unfolding find_ce_spec_def AUX_EQ
    apply (refine_rcg)
    apply (rule order_trans[
      OF bind_mono(1)[OF Gabow_GBG_Code.find_lasso_tr_correct order_refl]])
    apply assumption
    apply (simp; fail)
    apply (rule autoref_ga_rules;simp; fail)
    apply (rule autoref_ga_rules;simp; fail)
    apply (rule igb_fr_graphI)
    apply assumption
    apply assumption
    unfolding igb_graph.find_lasso_spec_def
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (clarsimp simp: lasso_run_rel_sv option_rel_sv split: option.split_asm)
    apply (metis igb_graph.is_lasso_prpl_of_lasso igb_graph.accepted_lasso 
      prod.exhaust)
    apply (simp add: option_rel_def lasso_run_rel_def br_def)
    by (metis igb_graph.is_lasso_prpl_conv igb_graph.lasso_accepted)
qed

definition ndfs_find_ce 
  :: "('q::hashable,_) igb_graph_rec_scheme \<Rightarrow> 'q lasso option option nres" 
  \<comment> \<open>Emptiness check based on nested DFS\<close>
  where 
  "ndfs_find_ce G \<equiv> do {
    ASSERT (igb_graph G);
    let G = igb_graph.degeneralize G;
    l \<leftarrow> blue_dfs G;
    case l of
      None \<Rightarrow> RETURN None
    | Some l \<Rightarrow> do { 
        ASSERT (snd l \<noteq> []); 
        RETURN (Some (Some (map_lasso fst (lasso_of_prpl l)))) 
      }
  }"

lemma ndfs_find_ce_refine: "(G',G)\<in>Id \<Longrightarrow> 
  ndfs_find_ce G' \<le> \<Down>(\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>option_rel\<rangle>option_rel) (find_ce_spec G)"
  apply simp
  unfolding find_ce_spec_def
proof (refine_rcg SPEC_refine refine_vcg)
  assume [simp]: "igb_graph G"
  then interpret igb_graph G .

  assume fr: "finite ((g_E G)\<^sup>* `` g_V0 G)"

  have [simp]: "b_graph degeneralize" by (simp add: degen_invar)
  (*then interpret bg: b_graph degeneralize .*)

  show "ndfs_find_ce G
    \<le>
    (SPEC (\<lambda>res. \<exists>res'. 
         (res,res')\<in>(\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel)
       \<and> (case res' of None \<Rightarrow> \<forall>r. \<not> is_acc_run r
         | Some None \<Rightarrow> Ex is_acc_run 
         | Some (Some x) \<Rightarrow> is_acc_run x)))"
    unfolding ndfs_find_ce_def find_lasso_spec_def ce_correct_def
    apply (refine_rcg refine_vcg order_trans[OF blue_dfs_correct])
    apply (clarsimp_all)

    apply (auto intro: degen_finite_reachable fr) []

    apply (auto
      elim!: degen_acc_run_complete[where m="\<lambda>_. ()"]
      dest!: degen.accepted_lasso[OF degen_finite_reachable[OF fr]]
      simp: degen.is_lasso_prpl_of_lasso[symmetric] prpl_of_lasso_def
      simp del: degen.is_lasso_prpl_of_lasso) []

    apply (auto 
      simp: b_graph.is_lasso_prpl_def graph.is_lasso_prpl_pre_def) []

    apply (auto split: option.split
      simp: degen.is_lasso_prpl_conv lasso_run_rel_def br_def
      dest: degen.lasso_accepted degen_acc_run_sound
    ) []
    done
qed


schematic_goal ndfs_find_ce_impl_aux: "(?c, ndfs_find_ce) 
  \<in> igbg_impl_rel_ext Rm Id 
  \<rightarrow> \<langle>
    \<langle>\<langle>\<langle>unit_rel,Id::('a::hashable\<times>_) set\<rangle>lasso_rel_ext\<rangle>option_rel\<rangle>option_rel
  \<rangle> nres_rel"
  unfolding ndfs_find_ce_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (trace, keep_goal))
  done
concrete_definition ndfs_find_ce_impl uses ndfs_find_ce_impl_aux

schematic_goal ndfs_find_ce_code_aux: "RETURN ?c \<le> ndfs_find_ce_impl G"
  unfolding ndfs_find_ce_impl_def
  by (refine_transfer (post))
concrete_definition ndfs_find_ce_code uses ndfs_find_ce_code_aux


lemma ndfs_find_ce_code_refine: "is_find_ce_algo ndfs_find_ce_code"
  unfolding is_find_ce_algo_def
proof (intro fun_relI plain_nres_relI)
  fix gbgi :: "('a,unit) igbg_impl_scheme" and gbg :: "'a igb_graph_rec"
  assume R: "(gbgi, gbg) \<in> igbg_impl_rel_ext unit_rel Id"
  note ndfs_find_ce_code.refine
  also note ndfs_find_ce_impl.refine[param_fo, THEN nres_relD, OF R]
  also note ndfs_find_ce_refine[OF IdI]
  finally show "RETURN (ndfs_find_ce_code gbgi)
    \<le> \<Down> (\<langle>\<langle>\<langle>Id\<rangle>lasso_run_rel\<rangle>Relators.option_rel\<rangle>Relators.option_rel) 
      (find_ce_spec gbg)"
    by (simp add: lasso_rel_ext_id)
qed

text \<open>We define a function that chooses between the emptiness check 
  algorithms\<close>

datatype config_ce = CFG_CE_SCC_GABOW | CFG_CE_NDFS

definition find_ce_code where "find_ce_code cfg \<equiv> case cfg of 
  CFG_CE_SCC_GABOW \<Rightarrow> gabow_find_ce_code
| CFG_CE_NDFS \<Rightarrow> ndfs_find_ce_code"

lemma find_ce_code_refine: "is_find_ce_algo (find_ce_code cfg)"
  apply (cases cfg)
  unfolding find_ce_code_def
  using gabow_find_ce_code_refine ndfs_find_ce_code_refine
  apply (auto split: config_ce.split)
  done
  
subsection \<open>System-Agnostic Model-Checker\<close>
text \<open>
  In this section, we implement the part of the model-checker that does not 
  depend on the language used to describe the system to be checked. 
\<close>

subsubsection \<open>Default Implementation of Lazy Intersection\<close>

locale cava_inter_impl_loc =
  igba_sys_prod_precond G S
  for S :: "('s, 'l set) sa_rec"
  and G :: "('q,'l set) igba_rec" +
  fixes Gi Si Rq Rs Rl eqq
  assumes [autoref_rules]: "(eqq,(=)) \<in> Rq \<rightarrow> Rq \<rightarrow> bool_rel"
  assumes [autoref_rules]: "(Gi,G) \<in> igbav_impl_rel_ext unit_rel Rq Rl"
  assumes [autoref_rules]: "(Si,S) \<in> sa_impl_rel_ext unit_rel Rs Rl"
begin

  lemma cava_inter_impl_loc_this: "cava_inter_impl_loc S G Gi Si Rq Rs Rl eqq"
    by unfold_locales

  (*<*)
  text \<open>TODO/FIXME:
    Some black-magic is going on here: The performance of the mc seems to depend on the ordering of states,
    so we do some adjustments of the ordering here.
\<close>
  lemma prod_impl_aux_alt_cava_reorder:
    "prod = (\<lparr>
      g_V = Collect (\<lambda>(q,s). q \<in> igba.V \<and> s \<in> sa.V),
      g_E = E_of_succ (\<lambda>(q,s). 
        if igba.L q (sa.L s) then     
          (\<lambda>(s,q). (q,s))`(LIST_SET_REV_TAG (succ_of_E (sa.E) s) 
           \<times> (succ_of_E (igba.E) q))
        else
          {}
      ),
      g_V0 = igba.V0 \<times> sa.V0,
      igbg_num_acc = igba.num_acc,
      igbg_acc = \<lambda>(q,s). if s\<in>sa.V then igba.acc q else {}
    \<rparr>)"
    unfolding prod_def
    apply (auto simp: succ_of_E_def E_of_succ_def split: if_split_asm)
    done

  schematic_goal vf_prod_impl_aux_cava_reorder:
    shows "(?c, prod) \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs)"
    unfolding prod_impl_aux_alt_cava_reorder[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (trace, keep_goal))
    done

  lemma (in -) map_concat_map_map_opt: 
    "map f (concat (map (\<lambda>xa. map (f' xa) (l1 xa)) l2)) 
      = List.maps (\<lambda>xa. map (f o f' xa) (l1 xa)) l2"
    "((\<lambda>(xd, xe). (xe, xd)) \<circ> Pair xa) = (\<lambda>x. (x,xa))"
    \<comment> \<open>Very specific optimization used in the next refinement\<close>
    apply -
    apply (induction l2) 
    apply (auto simp: List.maps_def) [2]

    apply auto []
    done

  concrete_definition (in -) gbav_sys_prod_impl_cava_reorder 
    for eqq Gi Si
    uses cava_inter_impl_loc.vf_prod_impl_aux_cava_reorder[
    param_fo, unfolded map_concat_map_map_opt]

  lemmas [autoref_rules] = 
    gbav_sys_prod_impl_cava_reorder.refine[OF cava_inter_impl_loc_this]
  
  context begin interpretation autoref_syn .
    (* HACK: Overwrite pattern that rewrites outer-level prod, such that
      local rules apply here. *)
    lemma [autoref_op_pat]: "prod \<equiv> OP prod" by simp
  end

  (*>*)

  definition dflt_inter :: "('q \<times> 's) igb_graph_rec \<times> ('q \<times> 's \<Rightarrow> 's)" 
    where "dflt_inter \<equiv> (prod, snd)"

  lemma dflt_inter_refine: 
    shows "RETURN dflt_inter \<le> inter_spec S G"
    unfolding inter_spec_def dflt_inter_def
    apply (refine_rcg le_ASSERTI refine_vcg)
  proof clarsimp_all
    show "igb_graph prod" by (rule prod_invar)

    fix r

    assume "finite (igba.E\<^sup>* `` igba.V0)" "finite ((g_E S)\<^sup>* `` g_V0 S)"
    thus "finite ((g_E prod)\<^sup>* `` g_V0 prod)" using prod_finite_reachable by auto

    show "(\<exists>r'. prod.is_acc_run r' \<and> r = snd \<circ> r') \<longleftrightarrow>
          (sa.is_run r \<and> sa.L \<circ> r \<in> igba.lang)"
      using gsp_correct1 gsp_correct2 
      apply (auto simp: comp_assoc)
      done
  qed

  schematic_goal dflt_inter_impl_aux: 
    shows "(?c, dflt_inter) 
    \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs)"
    unfolding dflt_inter_def[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  
  concrete_definition (in -) dflt_inter_impl
    for eqq Si Gi
    uses cava_inter_impl_loc.dflt_inter_impl_aux

  lemmas [autoref_rules] = dflt_inter_impl.refine[OF cava_inter_impl_loc_this]
end

definition [simp]: "op_dflt_inter \<equiv> cava_inter_impl_loc.dflt_inter"
lemma [autoref_op_pat]: "cava_inter_impl_loc.dflt_inter \<equiv> op_dflt_inter"
  by simp

context begin interpretation autoref_syn .
lemma dflt_inter_autoref[autoref_rules]:
  fixes G :: "('q,'l set) igba_rec"
  fixes S :: "('s, 'l set) sa_rec"
  fixes Gi Si Rq Rs Rl eqq
  assumes "SIDE_PRECOND (igba G)"
  assumes "SIDE_PRECOND (sa S)"
  assumes "GEN_OP eqq (=) (Rq \<rightarrow> Rq \<rightarrow> bool_rel)"
  assumes "(Gi,G) \<in> igbav_impl_rel_ext unit_rel Rq Rl"
  assumes "(Si,S) \<in> sa_impl_rel_ext unit_rel Rs Rl"
  shows "(dflt_inter_impl eqq Si Gi,
    (OP op_dflt_inter 
     ::: sa_impl_rel_ext unit_rel Rs Rl
      \<rightarrow> igbav_impl_rel_ext unit_rel Rq Rl 
      \<rightarrow> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs))$S$G
  ) \<in> igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs)"
proof -
  from assms interpret igba: igba G by simp
  from assms interpret sa: sa S by simp
  from assms interpret cava_inter_impl_loc S G Gi Si Rq Rs Rl eqq
    by unfold_locales simp_all

  show ?thesis
    apply simp
    apply (rule dflt_inter_impl.refine)
    apply unfold_locales
    done
qed

end

lemma inter_spec_refineI: 
  assumes "\<lbrakk> sa S; igba G \<rbrakk> \<Longrightarrow> m \<le> \<Down>R (inter_spec S G)"
  shows "m \<le> \<Down>R (inter_spec S G)"
  using assms
  unfolding inter_spec_def
  apply refine_rcg
  apply simp
  done
  
lemma dflt_inter_impl_refine: 
  fixes Rs :: "('si \<times> 's) set"
  fixes Rq :: "('qi \<times> 'q) set"
  fixes Rprop :: "('pi \<times> 'p) set"
  assumes [relator_props]: "single_valued Rs" "Range Rs = UNIV" 
    "single_valued Rq" "Range Rq = UNIV"

  assumes EQ: "(eqq,(=)) \<in> Rq \<rightarrow> Rq \<rightarrow> bool_rel"

  shows "(dflt_inter_impl eqq, inter_spec)
  \<in> sa_impl_rel_ext unit_rel Rs (\<langle>Rprop\<rangle>fun_set_rel) \<rightarrow>
    igbav_impl_rel_ext unit_rel Rq (\<langle>Rprop\<rangle>fun_set_rel) \<rightarrow>
    \<langle>igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r ((Rq \<times>\<^sub>r Rs) \<rightarrow> Rs)\<rangle>plain_nres_rel"
  apply (intro fun_relI plain_nres_relI)
  apply (rule inter_spec_refineI)
proof -
  fix Si S Gi G

  assume R:"(Si,S) \<in> sa_impl_rel_ext unit_rel Rs (\<langle>Rprop\<rangle>fun_set_rel)"
    "(Gi, G) \<in> igbav_impl_rel_ext unit_rel Rq (\<langle>Rprop\<rangle>fun_set_rel)"

  assume "sa S" and "igba G"
  then interpret sa: sa S + igba: igba G .
  interpret cava_inter_impl_loc S G Gi Si Rq Rs "\<langle>Rprop\<rangle>fun_set_rel" eqq
    apply unfold_locales
    using EQ R by simp_all

  note RETURN_refine[OF dflt_inter_impl.refine[OF cava_inter_impl_loc_this]]
  also note dflt_inter_refine
  finally show "RETURN (dflt_inter_impl eqq Si Gi)
  \<le> \<Down> (igbg_impl_rel_ext unit_rel (Rq \<times>\<^sub>r Rs) \<times>\<^sub>r (Rq \<times>\<^sub>r Rs \<rightarrow> Rs))
     (inter_spec S G)" .
qed

subsubsection \<open>Definition of Model-Checker\<close>
text \<open>In this section, we instantiate the parametrized model checker
  with the actual implementations.\<close>

setup Locale_Code.open_block
interpretation cava_sys_agn: impl_model_checker 
  "sa_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)" 
  "igbav_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)"
  "igbg_impl_rel_ext unit_rel (Id \<times>\<^sub>r Id)"
  "\<langle>Id \<times>\<^sub>r Id\<rangle>lasso_run_rel" "\<langle>Id\<rangle>lasso_run_rel"

  "ltl_to_gba_code"
  "\<lambda>_::unit. dflt_inter_impl (=)"
  "find_ce_code"
  "map_lasso"
  apply unfold_locales
  apply tagged_solver

  apply (rule ltl_to_gba_code_refine[unfolded is_ltl_to_gba_algo_def])
  
  using dflt_inter_impl_refine[of Id Id "(=)" Id] apply simp

  using find_ce_code_refine[unfolded is_find_ce_algo_def] 
  apply simp apply assumption

  using map_lasso_run_refine[of Id Id] apply simp
  done
setup Locale_Code.close_block

definition "cava_sys_agn \<equiv> cava_sys_agn.impl_model_check"

text \<open>The correctness theorem states correctness of the model checker wrt.\ 
  a model given as system automata. In the following sections, we will then 
  refine the model description to Boolean programs and Promela.\<close>
theorem cava_sys_agn_correct:
  fixes sysi :: "('s::hashable, 'p::linorder \<Rightarrow> bool, unit) sa_impl_scheme" 
    and sys :: "('s, 'p set) sa_rec" 
    and \<phi> :: "'p ltlc" 
    and cfg :: "config_l2b \<times> unit \<times> config_ce" 
  assumes "(sysi, sys) \<in> sa_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)"
    and "sa sys" "finite ((g_E sys)\<^sup>* `` g_V0 sys)"
  shows "case cava_sys_agn cfg sysi \<phi> of
         None \<Rightarrow> sa.lang sys \<subseteq> language_ltlc \<phi> 
         | Some None \<Rightarrow> \<not> sa.lang sys \<subseteq> language_ltlc \<phi>
         | Some (Some L) \<Rightarrow> 
             graph_defs.is_run sys (run_of_lasso L) 
           \<and> sa_L sys \<circ> (run_of_lasso L) \<notin> language_ltlc \<phi>"
  using cava_sys_agn.impl_model_check_correct[OF assms, of \<phi> cfg]
  unfolding cava_sys_agn_def
  by (auto split: option.splits simp: lasso_run_rel_def br_def)


subsection \<open>Model Checker for Boolean Programs\<close>

definition bpc_to_sa 
  :: "bprog \<times> BoolProgs.config \<Rightarrow> (BoolProgs.config,nat set) sa_rec" 
  \<comment> \<open>Conversion of a Boolean program to a system automata.\<close>
  where 
  "bpc_to_sa bpc \<equiv> let (bp,c0)=bpc in
  \<lparr>
    g_V = UNIV,
    g_E = E_of_succ (set o BoolProgs.nexts bp),
    g_V0 = {c0},
    sa_L = \<lambda>c. bs_\<alpha> (snd c)
  \<rparr>"

definition bpc_to_sa_impl 
  :: "bprog \<times> BoolProgs.config 
  \<Rightarrow> (BoolProgs.config,nat \<Rightarrow> bool,unit) sa_impl_scheme" 
  where 
  "bpc_to_sa_impl bpc \<equiv> let (bp,c0)=bpc in
  \<lparr> gi_V = \<lambda>_. True,
    gi_E = remdups o BoolProgs.nexts bp,
    gi_V0 = [c0],
    sai_L = \<lambda>c i. bs_mem i (snd c)
  \<rparr>"

lemma bpc_to_sa_impl_refine: "(bpc_to_sa_impl bpc, bpc_to_sa bpc) 
  \<in> sa_impl_rel_ext unit_rel Id (\<langle>nat_rel\<rangle>fun_set_rel)"
  unfolding bpc_to_sa_impl_def bpc_to_sa_def 
  unfolding sa_impl_rel_eext_def g_impl_rel_ext_def
  unfolding gen_sa_impl_rel_eext_def gen_g_impl_rel_ext_def
  apply (clarsimp split: prod.split)
  apply (intro conjI)
  apply (auto simp: fun_set_rel_def br_def) []

  apply (rule E_of_succ_refine[param_fo])
  apply (auto simp: list_set_rel_def br_def) []

  apply (auto simp: list_set_rel_def br_def) []

  apply (auto simp: fun_set_rel_def br_def) []
  done


lemma
  shows bpc_to_sa_invar: "sa (bpc_to_sa bpc)"
  and bpc_to_sa_fr: "finite ((g_E (bpc_to_sa bpc))\<^sup>* `` g_V0 (bpc_to_sa bpc))"
proof -
  obtain bp c where [simp]: "bpc = (bp,c)" by (cases bpc)
  show "sa (bpc_to_sa bpc)"
    apply unfold_locales

    apply (simp add: bpc_to_sa_def)
    apply (simp add: bpc_to_sa_def)
    done
  show "finite ((g_E (bpc_to_sa bpc))\<^sup>* `` g_V0 (bpc_to_sa bpc))"
    apply (simp add: bpc_to_sa_def)
    apply (rule finite_subset[OF _ BoolProgs.reachable_configs_finite[of bp c]])
    apply (rule rtrancl_reachable_induct)
    apply (auto 
      intro: BoolProgs.reachable_configs.intros 
      simp: E_of_succ_def)
    done
qed

interpretation bpc_to_sa: sa "bpc_to_sa bpc"
  using bpc_to_sa_invar .

lemma bpc_to_sa_run_conv[simp]: 
  "graph_defs.is_run (bpc_to_sa bpc) = bpc_is_run bpc"
  apply (rule ext)
  unfolding graph_defs.is_run_def
  unfolding bpc_to_sa_def bpc_is_run_def 
    ipath_def E_of_succ_def
  by auto

lemma bpc_to_sa_L_conv[simp]: "sa_L (bpc_to_sa bpc) = bpc_props"
  apply (rule ext)
  unfolding bpc_to_sa_def bpc_props_def
  apply (auto simp: E_of_succ_def split: prod.split)
  done

lemma bpc_to_sa_lang_conv[simp]: "sa.lang (bpc_to_sa bpc) = bpc_lang bpc"
  unfolding bpc_to_sa.lang_def bpc_to_sa.accept_def[abs_def] bpc_lang_def
  by auto

definition "cava_bpc cfg bpc \<phi> \<equiv> cava_sys_agn cfg (bpc_to_sa_impl bpc) \<phi>"

text \<open>
  Correctness theorem for the model checker on boolean programs.
  Note that the semantics of Boolean programs is given 
  by @{const "bpc_lang"}.
\<close>
theorem cava_bpc_correct:
  "case cava_bpc cfg bpc \<phi> of 
    None \<Rightarrow> bpc_lang bpc \<subseteq> language_ltlc \<phi>
  | Some None \<Rightarrow> (\<not>(bpc_lang bpc \<subseteq> language_ltlc \<phi>))
  | Some (Some ce) \<Rightarrow> 
      bpc_is_run bpc (run_of_lasso ce) 
    \<and> bpc_props o run_of_lasso ce \<notin> language_ltlc \<phi>"
  using cava_sys_agn_correct[OF bpc_to_sa_impl_refine bpc_to_sa_invar bpc_to_sa_fr, 
    of bpc \<phi> cfg]
  unfolding cava_bpc_def
  by (auto split: option.split simp: lasso_run_rel_def br_def)

export_code cava_bpc checking SML

subsection \<open>Model Checker for Promela Programs\<close>

definition promela_to_sa 
  :: "PromelaDatastructures.program \<times> APs \<times> gState \<Rightarrow> (gState, nat set) sa_rec" 
  \<comment> \<open>Conversion of a Promela model to a system automata.\<close>
  where "promela_to_sa promg \<equiv> let (prog,APs,g\<^sub>0)=promg in
  \<lparr>
    g_V = UNIV,
    g_E = E_of_succ (ls.\<alpha> o Promela.nexts_code prog),
    g_V0 = {g\<^sub>0},
    sa_L = promela_props_ltl APs
  \<rparr>"

definition promela_to_sa_impl 
  :: "PromelaDatastructures.program \<times> APs \<times> gState
  \<Rightarrow> (gState, nat \<Rightarrow> bool, unit) sa_impl_scheme" where 
  "promela_to_sa_impl promg \<equiv> let (prog,APs,g\<^sub>0)=promg in
  \<lparr> gi_V = \<lambda>_. True,
    gi_E = ls.to_list o Promela.nexts_code prog,
    gi_V0 = [g\<^sub>0],
    sai_L = propValid APs
  \<rparr>"

lemma promela_to_sa_impl_refine:
  shows "(promela_to_sa_impl promg, promela_to_sa promg) 
  \<in> sa_impl_rel_ext unit_rel Id (\<langle>nat_rel\<rangle>fun_set_rel)"
  unfolding promela_to_sa_impl_def promela_to_sa_def 
  unfolding sa_impl_rel_eext_def g_impl_rel_ext_def
  unfolding gen_sa_impl_rel_eext_def gen_g_impl_rel_ext_def

  apply (clarsimp split: prod.split)
  apply (intro conjI)

  apply (auto simp: fun_set_rel_def br_def) []

  apply (rule E_of_succ_refine[param_fo])
  apply (auto simp: list_set_rel_def br_def ls.correct) []

  apply (auto simp: list_set_rel_def br_def) []
  apply (auto simp: fun_set_rel_def br_def in_set_member promela_props_ltl_def) []
  done

definition "cava_promela cfg ast \<phi> \<equiv> 
  let 
      (promg,\<phi>\<^sub>i) = PromelaLTL.prepare cfg ast \<phi>
  in
     cava_sys_agn (fst cfg) (promela_to_sa_impl promg) \<phi>\<^sub>i"

text \<open>
  The next theorem states correctness of the Promela model checker.

  The correctness is specified for some AST.
\<close>
lemma cava_promela_correct:
  shows 
  "case cava_promela cfg ast \<phi> of 
    None \<Rightarrow> promela_language ast \<subseteq> language_ltlc \<phi>
  | Some None \<Rightarrow> (\<not>(promela_language ast \<subseteq> language_ltlc \<phi>))
  | Some (Some ce) \<Rightarrow> promela_is_run ast (run_of_lasso ce) 
    \<and> promela_props o run_of_lasso ce \<notin> language_ltlc \<phi>"
proof -
  obtain APs \<phi>\<^sub>i where conv: "PromelaLTL.ltl_convert \<phi> = (APs,\<phi>\<^sub>i)" 
    by (metis prod.exhaust)
  obtain prog g\<^sub>0 where ast: "Promela.setUp ast = (prog,g\<^sub>0)" 
    by (metis prod.exhaust)

  let ?promg = "(prog,APs,g\<^sub>0)"

  have promela_to_sa_invar: "sa (promela_to_sa ?promg)"
    apply unfold_locales
    apply (simp add: promela_to_sa_def)
    apply (simp add: promela_to_sa_def)
    done

  have promela_to_sa_fr: "finite ((g_E (promela_to_sa ?promg))\<^sup>* `` g_V0 (promela_to_sa ?promg))"
    apply (simp add: promela_to_sa_def)
    apply (rule 
      finite_subset[OF _ Promela.reachable_states_finite[of prog g\<^sub>0]])
    apply (rule rtrancl_reachable_induct)
    apply (auto 
      intro: Promela.reachable_states.intros 
      simp: E_of_succ_def) [2]
    apply (fact setUp_program_inv[OF ast])
    apply (fact setUp_gState_inv[OF ast])
    done

  interpret promela_to_sa: sa "promela_to_sa ?promg"
    using promela_to_sa_invar .

  have promela_to_sa_run_conv[simp]: 
    "graph_defs.is_run (promela_to_sa ?promg) = promela_is_run_ltl ?promg"
    apply (rule ext)
    unfolding graph_defs.is_run_def
    unfolding promela_to_sa_def promela_is_run_ltl_def promela_is_run'_def ipath_def E_of_succ_def
    by auto

  have promela_to_sa_L_conv[simp]: 
    "sa_L (promela_to_sa ?promg) = promela_props_ltl APs"
    apply (rule ext)
    unfolding promela_to_sa_def promela_props_ltl_def[abs_def]
    by (auto simp: E_of_succ_def)

  have promela_to_sa_lang_conv[simp]: 
    "sa.lang (promela_to_sa ?promg) = promela_language_ltl ?promg"
    unfolding promela_to_sa.lang_def promela_to_sa.accept_def[abs_def]
      promela_language_ltl_def
    by auto
  
  show ?thesis
    using cava_sys_agn_correct[OF 
      promela_to_sa_impl_refine promela_to_sa_invar promela_to_sa_fr, of \<phi>\<^sub>i "fst cfg"]
    using promela_language_sub_iff[OF conv ast] promela_run_in_language_iff[OF conv]
    unfolding cava_promela_def PromelaLTL.prepare_def
    by (auto split: option.split prod.splits simp: lasso_run_rel_def br_def conv ast promela_is_run_ltl_def)
qed

export_code cava_promela checking SML

subsection \<open>Model Checker for SM\<close>

definition test_aprop_impl :: "exp \<Rightarrow> valuation_impl \<Rightarrow> bool" where
  "test_aprop_impl e s \<equiv> case eval_exp_impl e (\<lparr> local_state_impl.variables = vi_empty \<rparr>,
    \<lparr> global_state_impl.variables = s \<rparr>) of None \<Rightarrow> False | Some v \<Rightarrow> bool_of_val_impl v"

definition sm_to_sa 
  :: "program \<Rightarrow> (ident \<Rightarrow> bool) \<Rightarrow> (pid_global_config_impl,exp set) sa_rec" 
  \<comment> \<open>Conversion of a Boolean program to a system automata.\<close>
  where 
  "sm_to_sa prog is_vis_var \<equiv> let
    cinf = comp_info_of prog
  in
    \<lparr>
      g_V = UNIV,
      g_E = E_of_succ (set o impl4_succ_impl prog cinf is_vis_var),
      g_V0 = {pid_init_gc_impl_impl prog cinf},
      sa_L = \<lambda>v. {e. test_aprop_impl e (global_state_impl.variables (pid_global_config.state v))}
    \<rparr>"

lemma local_state_rel:
  assumes "(s', s) \<in> vi_rel"
  shows "(\<lparr> local_state_impl.variables = s' \<rparr>, \<lparr> local_state.variables = s \<rparr>) \<in> local_state_rel"
  using assms vi_rel_rew unfolding local_state_rel_def by blast
lemma global_state_rel:
  assumes "(s', s) \<in> vi_rel"
  shows "(\<lparr> global_state_impl.variables = s' \<rparr>, \<lparr> global_state.variables = s \<rparr>) \<in> global_state_rel"
  using assms vi_rel_rew unfolding global_state_rel_def by blast

lemma test_aprop_impl: "(test_aprop_impl, test_aprop) \<in> Id \<rightarrow> vi_rel \<rightarrow> bool_rel"
proof clarsimp
  fix e s' s
  have 0: "(vi_empty, Map.empty) \<in> (vi_rel :: (valuation_impl \<times> valuation) set)"
    using vi_rel_rew vi_empty_correct by blast
  assume 1: "(s', s) \<in> (vi_rel :: (valuation_impl \<times> valuation) set)"
  have 2: "(test_aprop_impl e s', test_aprop e s) \<in> bool_rel"
    unfolding test_aprop_def test_aprop_impl_def
    apply (parametricity add: eval_exp_impl bool_of_val_impl)
    apply (intro IdI)
    apply (intro local_state_rel 0)
    apply (intro global_state_rel 1)
    done
  show "test_aprop_impl e s' \<longleftrightarrow> test_aprop e s" using 2 by simp
qed

lemma restrict_parametric:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> rel_option B) ===> rel_set A ===> (A ===> rel_option B)) (|`) (|`)"
  apply rule
  apply rule
  apply rule
  by (metis (full_types) assms bi_uniqueDl bi_uniqueDr option.rel_intros(1)
    rel_funD rel_setD1 rel_setD2 restrict_map_def)

lift_definition restrict :: "('a, 'b) mapping \<Rightarrow> 'a set \<Rightarrow> ('a, 'b) mapping"
  is "(|`)" parametric restrict_parametric .

lift_definition vi_restrict :: "valuation_impl \<Rightarrow> ident set \<Rightarrow> valuation_impl"
  is "(|`) :: valuation \<Rightarrow> ident set \<Rightarrow> valuation" by this

lemma [code]: "vi_restrict = restrict" by transfer simp
lemma vi_restrict_correct: "vi_\<alpha> (vi_restrict s A) = vi_\<alpha> s |` A"
  unfolding vi_\<alpha>_def by transfer (simp add: Fun.comp_def option.map_ident)


definition (in -) pid_test_gc_impl 
  :: "pid_global_config_impl \<Rightarrow> exp \<Rightarrow> bool"
where
  "pid_test_gc_impl gci ap \<equiv> test_aprop_impl ap
    ((global_state_impl.variables (pid_global_config.state gci)))"

definition sm_to_sa_impl 
  :: "program \<Rightarrow> (ident \<Rightarrow> bool) 
  \<Rightarrow> (pid_global_config_impl,exp \<Rightarrow> bool,unit) sa_impl_scheme" 
  where 
  "sm_to_sa_impl prog is_vis_var \<equiv> let
    cinf = comp_info_of prog
  in  
    \<lparr> gi_V = \<lambda>_. True,
      gi_E = remdups o impl4_succ_impl prog cinf is_vis_var, \<comment> \<open>TODO: This remdups is unnecessary!\<close>
      gi_V0 = [pid_init_gc_impl_impl prog cinf],
      sai_L = pid_test_gc_impl  
    \<rparr>"

lemma sm_to_sa_impl_refine: "(sm_to_sa_impl prog is_vis_var, sm_to_sa prog is_vis_var) 
  \<in> sa_impl_rel_ext unit_rel Id (\<langle>Id\<rangle>fun_set_rel)"
  unfolding sm_to_sa_impl_def sm_to_sa_def 
  unfolding sa_impl_rel_eext_def g_impl_rel_ext_def
  unfolding gen_sa_impl_rel_eext_def gen_g_impl_rel_ext_def
  apply (clarsimp split: prod.split)
  apply (intro conjI)
  apply (auto simp: fun_set_rel_def br_def) []

  apply (rule E_of_succ_refine[param_fo])
  apply (auto simp: list_set_rel_def br_def) []
  apply (auto simp: list_set_rel_def br_def) []
  apply (auto simp: fun_set_rel_def br_def pid_test_gc_impl_def) []
  done

lemma E_of_succ_is_rel_of_succ: "E_of_succ = rel_of_succ"
  by (auto intro!: ext simp: E_of_succ_def rel_of_succ_def)

definition vi_\<gamma> :: "valuation \<Rightarrow> valuation_impl" where
  "vi_\<gamma> v = (Mapping.Mapping (map_option Abs_uint32 \<circ> v))"

lemma [simp]: "vi_\<alpha> (vi_\<gamma> v) = v"
  unfolding vi_\<alpha>_def vi_\<gamma>_def
  apply (rule ext)
  apply (auto simp: Mapping_inverse option.map_comp option.map_ident Abs_uint32_inverse o_def)
  done

lemma [simp]: "vi_\<gamma> (vi_\<alpha> v) = v"
  unfolding vi_\<alpha>_def vi_\<gamma>_def
  apply (auto simp: Mapping.rep_inverse option.map_comp option.map_ident Rep_uint32_inverse o_def)
  done

definition lsi_\<alpha> :: "local_state_impl \<Rightarrow> local_state"  where
  "lsi_\<alpha> lsi \<equiv> \<lparr> local_state.variables = vi_\<alpha> (local_state_impl.variables lsi) \<rparr>"
definition lsi_\<gamma> :: "local_state \<Rightarrow> local_state_impl"  where
  "lsi_\<gamma> lsi \<equiv> \<lparr> local_state_impl.variables = vi_\<gamma> (local_state.variables lsi) \<rparr>"

lemma [simp]: 
  "lsi_\<alpha> (lsi_\<gamma> ls) = ls"
  "lsi_\<gamma> (lsi_\<alpha> lsi) = lsi"
  unfolding lsi_\<alpha>_def lsi_\<gamma>_def
  by auto

lemma local_state_rel_as_br: "local_state_rel = br lsi_\<alpha> (\<lambda>_. True)"
  by (force simp: local_state_rel_def br_def lsi_\<alpha>_def)


definition gsi_\<alpha> :: "global_state_impl \<Rightarrow> global_state"  where
  "gsi_\<alpha> gsi \<equiv> \<lparr> global_state.variables = vi_\<alpha> (global_state_impl.variables gsi) \<rparr>"
definition gsi_\<gamma> :: "global_state \<Rightarrow> global_state_impl"  where
  "gsi_\<gamma> gs \<equiv> \<lparr> global_state_impl.variables = vi_\<gamma> (global_state.variables gs) \<rparr>"

lemma [simp]: 
  "gsi_\<alpha> (gsi_\<gamma> gs) = gs"
  "gsi_\<gamma> (gsi_\<alpha> gsi) = gsi"
  unfolding gsi_\<alpha>_def gsi_\<gamma>_def
  by auto

lemma global_state_rel_as_br: "global_state_rel = br gsi_\<alpha> (\<lambda>_. True)"
  by (force simp: global_state_rel_def br_def gsi_\<alpha>_def)

definition map_local_config 
  :: "('a\<Rightarrow>'c) \<Rightarrow> ('b\<Rightarrow>'d) \<Rightarrow> ('a,'b) Gen_Scheduler.local_config \<Rightarrow> ('c,'d) Gen_Scheduler.local_config"
where
  "map_local_config mc ms ls \<equiv> \<lparr> 
    local_config.command = mc (local_config.command ls),
    local_config.state = ms (local_config.state ls)
    \<rparr>"

lemma [simp]:
  "map_local_config (\<lambda>x. x) (\<lambda>x. x) = (\<lambda>x. x)"
  "map_local_config f g (map_local_config f' g' lc) = map_local_config (f o f') (g o g') lc"
  by (auto simp: map_local_config_def)

definition map_pid_global_config 
  :: "('a\<Rightarrow>'d) \<Rightarrow> ('b\<Rightarrow>'e) \<Rightarrow> ('c\<Rightarrow>'f) \<Rightarrow> ('a,'b,'c) Pid_Scheduler.pid_global_config \<Rightarrow> ('d,'e,'f) Pid_Scheduler.pid_global_config"
where
  "map_pid_global_config mp ml mg gc \<equiv> \<lparr> 
    pid_global_config.processes = map (map_local_config mp ml) (pid_global_config.processes gc),
    pid_global_config.state = mg (pid_global_config.state gc)
    \<rparr>"

lemma [simp]:
  "map_pid_global_config (\<lambda>x. x) (\<lambda>x. x) (\<lambda>x. x) = (\<lambda>x. x)"
  "map_pid_global_config f g h (map_pid_global_config f' g' h' gc) 
  = map_pid_global_config (f o f') (g o g') (h o h') gc"
  by (auto simp: map_pid_global_config_def)

abbreviation lci_\<alpha> :: "local_config_impl \<Rightarrow> local_config" 
  where "lci_\<alpha> \<equiv> map_local_config (\<lambda>x. x) lsi_\<alpha>"

abbreviation lci_\<gamma> :: "local_config \<Rightarrow> local_config_impl" 
  where "lci_\<gamma> \<equiv> map_local_config (\<lambda>x. x) lsi_\<gamma>"

abbreviation gci_\<alpha> :: "pid_global_config_impl \<Rightarrow> pid_global_config" 
  where "gci_\<alpha> \<equiv> map_pid_global_config (\<lambda>x. x) lsi_\<alpha> gsi_\<alpha>"

abbreviation gci_\<gamma> :: "pid_global_config \<Rightarrow> pid_global_config_impl" 
  where "gci_\<gamma> \<equiv> map_pid_global_config (\<lambda>x. x) lsi_\<gamma> gsi_\<gamma>"


lemma local_config_rel_as_br: "local_config_rel = br lci_\<alpha> (\<lambda>_. True)"
  by (force simp: local_config_rel_def br_def map_local_config_def local_state_rel_as_br)
  
thm list_all2_induct
(* TODO: Move *)
lemma list_all2_map_conv[simp]: 
  "list_all2 (\<lambda>x y. x=f y) xs ys \<longleftrightarrow> xs = map f ys"
  "list_all2 (\<lambda>x y. y=f x) ys xs \<longleftrightarrow> xs = map f ys"
  apply (rule iffI)
  apply (induction rule: list_all2_induct, auto) []
  apply (induction ys arbitrary: xs, auto) []
  apply (rule iffI)
  apply (induction rule: list_all2_induct, auto) []
  apply (induction ys arbitrary: xs, auto) []
  done

lemma pid_global_config_rel_as_br: "global_config_rel = br gci_\<alpha> (\<lambda>_. True)"
  by (force 
    simp: global_config_rel_def br_def map_pid_global_config_def 
    simp: global_state_rel_as_br local_config_rel_as_br
    simp: list_rel_def)

lemma global_config_rel_inv_sv: "single_valued (global_config_rel\<inverse>)"
  apply (rule single_valuedI)
  apply (clarsimp simp: pid_global_config_rel_as_br br_def)
proof -
  fix x y
  assume "gci_\<alpha> x = gci_\<alpha> y"  
  hence "gci_\<gamma> (gci_\<alpha> x) = gci_\<gamma> (gci_\<alpha> y)" by simp
  thus "x=y" by (simp add: o_def)
qed  

(* TODO: Move *)
lemma pred_of_enex_mono: 
  assumes "en c \<subseteq> en' c"
  assumes "pred_of_enex (en,ex) c c'"
  shows "pred_of_enex (en',ex) c c'"
  using assms
  by (auto)

lemma finite_ample_reachable[simp, intro!]: 
  assumes "ty_program prog"
  shows "finite
     ((E_of_succ ((set \<circ>\<circ> impl4_succ_impl prog (comp_info_of prog)) is_vis_var))\<^sup>* ``
      {pid_init_gc_impl_impl prog (comp_info_of prog)})" (is "finite ?S")
proof -
  interpret visible_prog prog is_vis_var using assms by unfold_locales
  have "E_of_succ ((set \<circ>\<circ> impl4_succ_impl prog (comp_info_of prog)) is_vis_var) 
    = ample_step_impl4 is_vis_var"
    by (simp 
          add: impl4_succ_pred[symmetric] E_of_succ_is_rel_of_succ
          add: impl4_succ_impl)
  also note ample_step_impl4[simplified]
  finally have "E_of_succ ((set \<circ>\<circ> impl4_succ_impl prog (comp_info_of prog)) is_vis_var) 
    = ample_step_impl3" .
  hence S_eq: "?S = ample_step_impl3\<^sup>* `` {pid_init_gc_impl}"
    by (simp add: pid_init_gc_impl_impl)

  (* TODO: Move as sublocale to SM_Ample_Impl in visible_prog-context,
    before interpretation as impl3_sim.b ! *)  
  interpret impl2: sa "\<lparr> g_V = UNIV, g_E = ample_step_impl2,
    g_V0 = {pid_init_gc}, sa_L = pid_interp_gc \<rparr>" by unfold_locales auto

  (* TODO: Duplicated from prf of cr_ample_impl2_reduction *)
  have 1: "ample_step_impl2 = rel_of_enex (cr_ample_impl1, ga_ex)"
    unfolding ample_step_impl2_def cr_ample_impl1_def cr_ample_impl2_def
    unfolding ga_gample_mi2_impl[abs_def]
    by simp

  {
    fix gc :: pid_global_config
    have "cr_ample \<le> SPEC (\<lambda>r. r gc \<subseteq> ga_en gc)"
      unfolding cr_ample_def
      apply (refine_vcg order_trans[OF find_fas_init_correct])
      apply unfold_locales[]
      apply simp
    proof -
      fix sticky_E
      show "ga_ample sticky_E gc \<subseteq> ga_en gc"
        apply (cases "ga_ample sticky_E gc = ga_en gc")
        apply simp
        apply (drule ga_ample_neq_en_eq[of sticky_E gc])
        using ga_gample_subset[of sticky_E gc]
        apply auto
        done
    qed    
    from order_trans[OF cr_ample_impl1.refine[THEN nres_relD, simplified] this]
    have "cr_ample_impl1 gc \<subseteq> ga_en gc" by simp
  } note aux1=this

  interpret simulation Id
    "\<lparr> g_V = UNIV, g_E = rel_of_enex (cr_ample_impl1,ga_ex), g_V0 = {pid_init_gc} \<rparr>"
    "\<lparr> g_V = UNIV, g_E = ga_step, g_V0 = {pid_init_gc} \<rparr>"
    unfolding ga_step_alt
    apply unfold_locales
    using pred_of_enex_mono[of cr_ample_impl1 _ ga_en ga_ex,OF aux1]
    apply auto
    done


  have FIN2: "finite (ample_step_impl2\<^sup>* `` {pid_init_gc})"
    unfolding 1
    unfolding graph_rec.simps
    apply (rule reachable_finite_sim[unfolded graph_rec.simps])
    using jsys.reachable_finite
    using reachable_alt
    apply simp
    apply simp
    done    

  show "finite ?S"
    unfolding S_eq
    using impl3_sim.s1.reachable_finite_sim FIN2 finite_Image_sv[OF global_config_rel_inv_sv]
    by simp
qed
 

lemma
  assumes "ty_program prog"
  shows sm_to_sa_invar: "sa (sm_to_sa prog is_vis_var)"
  and sm_to_sa_fr: "finite ((g_E (sm_to_sa prog is_vis_var))\<^sup>* `` g_V0 (sm_to_sa prog is_vis_var))"
  unfolding sm_to_sa_def by (unfold_locales, auto intro: assms)

definition "mapping_val_hashcode m \<equiv> \<Sum>((hashcode o Mapping.lookup m)`Mapping.keys m)"

instantiation local_config_ext :: (hashable,hashable,hashable)hashable begin
  definition "hashcode lc \<equiv> 
      hashcode (local_config.command lc) 
    + hashcode (local_config.state lc)
    + hashcode (local_config.more lc)"

  definition "def_hashmap_size (T::('a,'b,'c) local_config_ext itself) \<equiv> 8"  

  instance 
    apply intro_classes
    unfolding def_hashmap_size_local_config_ext_def
    by auto

end

instantiation Pid_Scheduler.pid_global_config_ext :: (hashable,hashable,hashable,hashable) hashable begin
  definition "hashcode gc \<equiv> 
      hashcode (pid_global_config.processes gc)
    + hashcode (pid_global_config.state gc)
    + hashcode (pid_global_config.more gc)"

  definition "def_hashmap_size (T::('a,'b,'c,'d) pid_global_config_ext itself) \<equiv> 8"

  instance 
    apply intro_classes
    unfolding def_hashmap_size_pid_global_config_ext_def
    by auto

end

instantiation local_state_impl_ext :: (hashable)hashable begin
  term "rm.iterate r (\<lambda>(k,v) s. hashcode k + hashcode v + s) 0"

  (* TODO: Derive sensible hashcode! *)
  definition "hashcode ls 
    \<equiv> mapping_val_hashcode (local_state_impl.variables ls) 
     + hashcode (local_state_impl.more ls)"

  definition "def_hashmap_size (T::('a) local_state_impl_ext itself) \<equiv> 8"

  instance 
    apply intro_classes
    unfolding def_hashmap_size_local_state_impl_ext_def
    by auto

end

instantiation global_state_impl_ext :: (hashable)hashable begin
  term "rm.iterate r (\<lambda>(k,v) s. hashcode k + hashcode v + s) 0"

  (* TODO: Derive sensible hashcode! *)
  definition "hashcode gs 
    \<equiv> mapping_val_hashcode (global_state_impl.variables gs)
    + hashcode (global_state_impl.more gs)"

  definition "def_hashmap_size (T::('a) global_state_impl_ext itself) \<equiv> 8"

  instance 
    apply intro_classes
    unfolding def_hashmap_size_global_state_impl_ext_def
    by auto

end

(* TODO: Move. TODO: Can we generate a more efficient comparator. 
  Perhaps using code_printing? *)
local_setup \<open>
  Comparator_Generator.register_foreign_comparator @{typ String.literal}
    @{term "comparator_of :: String.literal \<Rightarrow> _"}
    @{thm comparator_of[where 'a=String.literal]}
\<close>

derive linorder un_op
derive linorder bin_op
derive linorder exp

datatype sm_result = TY_ERR | SAT | UNSAT | UNSAT_CE "pid_global_config_impl lasso"

definition "cava_sm cfg prog \<phi> \<equiv> 
  let prog = dloc prog in (
  if ty_program prog \<and> ltlc_next_free \<phi> then
    case cava_sys_agn cfg (sm_to_sa_impl prog (\<lambda>x. x\<in>vars_of_ltlc \<phi>)) \<phi> of
      None \<Rightarrow> SAT
    | Some None \<Rightarrow> UNSAT
    | Some (Some ce) \<Rightarrow> UNSAT_CE ce
  else TY_ERR)"

text \<open> Relation that relates states of computed counterexample with
  states of actual run in reference point semantics. Unfortunately,
  we cannot exactly recompute the reference point run b/c we cannot undo
  the effect of the locality decider. \<close>
definition "sm_gc_rel prog \<equiv> {(gci, gc). map_option dloc_gc gc = Some (cprog.gc_\<alpha> prog (pidgc_\<alpha> (gci_\<alpha> gci)))}"

definition "sm_props_of_gc gc \<equiv> sm_props (global_state.variables (global_config.state (the gc)))"

lemma lang_eq_on_ss_ltlc:
  fixes interp interp' P
  defines "L \<equiv> {w. \<exists>r. P r \<and> w = interp o r }"
  defines "L' \<equiv> {w. \<exists>r. P r \<and> w = interp' o r }"
  assumes 1: "\<And>r. P r \<Longrightarrow> pw_eq_on (atoms_ltlc \<phi>) (interp o r) (interp' o r)"
  shows "L \<subseteq> language_ltlc \<phi> \<longleftrightarrow> L' \<subseteq> language_ltlc \<phi>"
proof -
  from 1 have 2: "\<And>r. P r \<Longrightarrow> pw_eq_on (atoms_ltlc \<phi>) (interp' o r) (interp o r)"
    by (simp add: pw_eq_on_sym)

  thus ?thesis
    unfolding L_def L'_def language_ltlc_def
    apply (auto simp: ltlc_eq_on)
    apply (subst ltlc_eq_on)
    apply (erule 2) apply auto

    apply (subst ltlc_eq_on)
    apply (erule 1) apply auto
    done
qed


text \<open>Correctness theorem for the model checker on SM programs.\<close>
(* TODO: variables occurring in the formula but not as global variables in the
  program should also be a type error *)
theorem cava_sm_correct:
  "case cava_sm config prog \<phi> of 
    TY_ERR \<Rightarrow> \<not>ty_program (dloc prog) \<or> \<not>ltlc_next_free \<phi>
  | SAT \<Rightarrow> Collect (ap_accept prog) \<subseteq> language_ltlc \<phi>
  | UNSAT \<Rightarrow> (\<not>(Collect (ap_accept prog) \<subseteq> language_ltlc \<phi>))
  | UNSAT_CE ce \<Rightarrow> \<not>(Collect (ap_accept prog) \<subseteq> language_ltlc \<phi>) 
    \<and> (\<exists>r. (run_of_lasso ce, r) \<in> run_rel (sm_gc_rel (dloc prog)) \<and> ref_is_run prog r
        \<and> sm_props_of_gc o r \<notin> language_ltlc \<phi>)"
  unfolding cava_sm_def
  apply (clarsimp split: option.splits)
  apply safe
proof -
  let ?is_vis_var = "(\<lambda>x. x \<in> vars_of_ltlc \<phi>)"
  let ?csa = "cava_sys_agn config (sm_to_sa_impl (dloc prog) ?is_vis_var) \<phi>"
  assume TY: "ty_program (dloc prog)"
  then interpret visible_prog "(dloc prog)" "(\<lambda>x. x\<in>vars_of_ltlc \<phi>)" by unfold_locales
    
  interpret sm_to_sa: sa "(sm_to_sa (dloc prog) ?is_vis_var)"
    using sm_to_sa_invar[OF TY] .

  assume NF: "ltlc_next_free \<phi>"

  note csa_correct = cava_sys_agn_correct[OF sm_to_sa_impl_refine sm_to_sa_invar sm_to_sa_fr,
      of "(dloc prog)" ?is_vis_var \<phi> config]
    
  have aprop_impl_conv: "\<And>e v. test_aprop_impl e v = test_aprop e (vi_\<alpha> v)"  
    apply (rule IdD)
    apply (parametricity add: test_aprop_impl)
    apply (auto simp: br_def)
    done

  have lang_ss_conv: "sa.lang (sm_to_sa (dloc prog) ?is_vis_var) \<subseteq> language_ltlc \<phi>
    \<longleftrightarrow> Collect (ample_impl.accept ?is_vis_var) \<subseteq> language_ltlc \<phi>"
    unfolding sm_to_sa.lang_def sm_to_sa.accept_def[abs_def] graph_defs.is_run_def
    unfolding sm_to_sa_def
    apply simp
    unfolding ample_impl.accept_def[abs_def] graph_defs.is_run_def
    unfolding impl4_succ_impl ample_step_impl4_impl
    unfolding impl4_succ_pred[symmetric] E_of_succ_is_rel_of_succ
    apply (simp add: eq_commute[of "pid_init_gc_impl_impl (dloc prog) (comp_info_of (dloc prog))"])
    unfolding conj_assoc[symmetric] (* TODO: Hack *)
    apply (rule lang_eq_on_ss_ltlc)
    apply (auto simp: pw_eq_on_def pid_interp_gc_impl_def aprop_impl_conv sm_props_def test_aprop_vars_cong)
    done

  {
    fix w
    assume N: "?csa=None" 
    assume "ap_accept prog w"
    with dloc_sim.accept_bisim[of prog] have ACC: "ap_accept (dloc prog) w" 
      unfolding ap_accept_def by simp

    from csa_correct N TY have "sa.lang (sm_to_sa (dloc prog) ?is_vis_var) \<subseteq> language_ltlc \<phi>"
      by simp
    hence "Collect (ample_impl.accept ?is_vis_var) \<subseteq> language_ltlc \<phi>"
      by (simp add: lang_ss_conv)
    with ample_reduction_correct[OF TY NF] have "Collect (ap_accept (dloc prog)) \<subseteq> language_ltlc \<phi>" 
      by simp

    thus "w\<in>language_ltlc \<phi>" using ACC by blast
  }

  {
    fix w
    assume N: "?csa=Some None" 
    
    from csa_correct N TY have "\<not>sa.lang (sm_to_sa (dloc prog) ?is_vis_var) \<subseteq> language_ltlc \<phi>"
      by simp
    hence "\<not>Collect (ample_impl.accept ?is_vis_var) \<subseteq> language_ltlc \<phi>"
      by (simp add: lang_ss_conv)

    with ample_reduction_correct[OF TY NF] have "\<not>Collect (ap_accept (dloc prog)) \<subseteq> language_ltlc \<phi>" 
      by simp
    moreover assume "Collect (ap_accept prog) \<subseteq> language_ltlc \<phi>"
    hence "Collect (ap_accept (dloc prog)) \<subseteq> language_ltlc \<phi>"
      using dloc_sim.accept_bisim[of prog] unfolding ap_accept_def[abs_def] 
      by auto
    ultimately show False ..
  }

  
  {
    fix w ce
    assume N: "?csa=Some (Some ce)" 

    from csa_correct N TY have R:
      "graph_defs.is_run (sm_to_sa (dloc prog) (\<lambda>x. x \<in> vars_of_ltlc \<phi>)) (run_of_lasso ce)"
      and NL:  
      "(sa_L (sm_to_sa (dloc prog) (\<lambda>x. x \<in> vars_of_ltlc \<phi>)) \<circ> (run_of_lasso ce)) 
        \<notin> language_ltlc \<phi>"
      by auto  

    from R have "graph_defs.is_run \<lparr> g_V = UNIV, g_E = ample_step_impl4_impl (dloc prog)
      (comp_info_of (dloc prog)) ?is_vis_var, g_V0 = {pid_init_gc_impl_impl (dloc prog)
      (comp_info_of (dloc prog))}, sa_L = pid_interp_gc_impl ?is_vis_var \<rparr> (run_of_lasso ce)"
      unfolding graph_defs.is_run_def
      by (auto simp: ipath_def impl4_succ_pred[symmetric]
        sm_to_sa_def E_of_succ_def  pid_init_gc_impl_impl ample_step_impl4_impl impl4_succ_impl)

    with ample_step_impl4 have R3: "graph_defs.is_run \<lparr> g_V = UNIV,
      g_E = visible_prog.ample_step_impl3 (dloc prog) (\<lambda> x. x \<in> vars_of_ltlc \<phi>),
      g_V0 = {cprog.pid_init_gc_impl (dloc prog)},
      sa_L = pid_interp_gc_impl (\<lambda> x. x \<in> vars_of_ltlc \<phi>) \<rparr> (run_of_lasso ce)"  
      by (auto simp: pid_init_gc_impl_impl ample_step_impl4_impl)

    from impl3_sim.br_run_conv[OF pid_global_config_rel_as_br] R3 
    have R2: "graph_defs.is_run \<lparr> g_V = UNIV, g_E = visible_prog.ample_step_impl2 (dloc prog)
      (\<lambda> x. x \<in> vars_of_ltlc \<phi>), g_V0 = {cprog.pid_init_gc (dloc prog)},
      sa_L = visible_prog.pid_interp_gc (\<lambda> x. x \<in> vars_of_ltlc \<phi>) \<rparr> (gci_\<alpha> o run_of_lasso ce)"
      by auto

    (* TODO: The whole next 100 lines duplicated from finiteness proof *)  
    (* TODO: Duplicated from prf of cr_ample_impl2_reduction *)
    have 1: "ample_step_impl2 = rel_of_enex (cr_ample_impl1, ga_ex)"
      unfolding ample_step_impl2_def cr_ample_impl1_def cr_ample_impl2_def
      unfolding ga_gample_mi2_impl[abs_def]
      by simp
  
    {
      fix gc :: pid_global_config
      have "cr_ample \<le> SPEC (\<lambda>r. r gc \<subseteq> ga_en gc)"
        unfolding cr_ample_def
        apply (refine_vcg order_trans[OF find_fas_init_correct])
        apply unfold_locales[]
        apply simp
      proof -
        fix sticky_E
        show "ga_ample sticky_E gc \<subseteq> ga_en gc"
          apply (cases "ga_ample sticky_E gc = ga_en gc")
          apply simp
          apply (drule ga_ample_neq_en_eq[of sticky_E gc])
          using ga_gample_subset[of sticky_E gc]
          apply auto
          done
      qed    
      from order_trans[OF cr_ample_impl1.refine[THEN nres_relD, simplified] this]
      have "cr_ample_impl1 gc \<subseteq> ga_en gc" by simp
    } note aux1=this

    interpret simulation Id
      "\<lparr> g_V = UNIV, g_E = ample_step_impl2, g_V0 = {pid_init_gc} \<rparr>"
      "\<lparr> g_V = UNIV, g_E = ga_step, g_V0 = {pid_init_gc} \<rparr>"
      unfolding ga_step_alt 1
      apply unfold_locales
      apply simp
      using pred_of_enex_mono[of cr_ample_impl1 _ ga_en ga_ex,OF aux1]
      apply auto
      done

    have run_rel_eq_simp[simp]: "\<And> a b. (a, b) \<in> run_rel Id \<longleftrightarrow> a = b"
      by (auto simp: run_rel_def)

    have 1: "graph_defs.is_run \<lparr> g_V = UNIV, g_E = ample_step_impl2,
      g_V0 = {pid_init_gc} \<rparr> (gci_\<alpha> o run_of_lasso ce)"
      using R2 unfolding graph_defs.is_run_def by simp

    have "graph_defs.is_run (Pid_Gen_Scheduler_linit.ga_automaton (sl_graph.astep_impl
      (approx_reachable_list (dloc prog)) cfg'_succ_list) la_en' la_ex'
      (cprog.pid_init_gc (dloc prog)) (visible_prog.pid_interp_gc (\<lambda> x. x \<in> vars_of_ltlc \<phi>)))
      (gci_\<alpha> o run_of_lasso ce)"
      unfolding ga_automaton_def
      apply (rule run_sim)
      apply (rule 1)
      unfolding ga_automaton_def[symmetric]
      unfolding graph_defs.is_run_def
      by simp

    from ga_run_sim'[OF this]  
    have "ref_is_run (dloc prog) (Some \<circ> gc_\<alpha> \<circ> pidgc_\<alpha> \<circ> gci_\<alpha> o (run_of_lasso ce))"
      by (simp add: o_def)

    from dloc_sim.br_run_conv[OF refl, THEN iffD1, OF this]
    obtain r where RUN: "ref_is_run prog r"
      and RR: "(run_of_lasso ce, r) \<in> run_rel (sm_gc_rel (dloc prog))"
      and NL': "pid_interp_gc_impl ?is_vis_var \<circ> (run_of_lasso ce) \<notin> language_ltlc \<phi>"
      apply clarsimp
      apply (rule that)
      apply assumption
      unfolding run_rel_def sm_gc_rel_def fun_eq_iff
      apply (simp add: o_def map_option_def)

      apply (thin_tac "\<And>r. a r \<Longrightarrow> b r \<Longrightarrow> c r \<Longrightarrow> thesis" for a b c)
      apply (thin_tac a for a)
        
      using NL
      unfolding language_ltlc_def
      apply simp
      apply (subst ltlc_eq_on) prefer 2 apply assumption
      apply (thin_tac "\<not>a" for a)
      apply (auto simp: pw_eq_on_def sm_to_sa_def pid_interp_gc_impl_def 
        aprop_impl_conv sm_props_def test_aprop_vars_cong)
      done

    have "pw_eq_on (atoms_ltlc \<phi>) 
      (sm_props_of_gc o r) (pid_interp_gc_impl ?is_vis_var o run_of_lasso ce)"
      using RR
      apply (auto 
        simp: pw_eq_on_def run_rel_def sm_gc_rel_def sm_props_of_gc_def
        simp: pid_interp_gc_impl_def)
      apply (drule_tac x=i in spec, clarsimp)
      apply (auto simp: sm_props_def)
      apply (case_tac z, clarsimp)
      apply (auto
        simp: dloc_gc_def gc_\<alpha>_def pidgc_\<alpha>_def map_pid_global_config_def gsi_\<alpha>_def
        dest: test_aprop_vars_cong
        ) []

      apply (drule_tac x=i in spec, clarsimp)
      apply (case_tac z, clarsimp)
      apply (auto
        simp: dloc_gc_def gc_\<alpha>_def pidgc_\<alpha>_def map_pid_global_config_def gsi_\<alpha>_def
        dest: test_aprop_vars_cong
        ) []
      done
    from NL' ltlc_eq_on[of \<phi>, OF this] have "sm_props_of_gc \<circ> r \<notin> language_ltlc \<phi>"
      by (auto simp: language_ltlc_def)
    with RUN RR show "\<exists>r. (run_of_lasso ce, r) \<in> run_rel (sm_gc_rel (dloc prog)) \<and>
               ref_is_run prog r \<and>
               sm_props_of_gc \<circ> r \<notin> language_ltlc \<phi>"  
      by auto

    {  
      from R NL have "\<not>sa.lang (sm_to_sa (dloc prog) ?is_vis_var) \<subseteq> language_ltlc \<phi>" 
        by (auto simp: sm_to_sa.lang_def sm_to_sa.accept_def[abs_def])
      from csa_correct N TY have "\<not>sa.lang (sm_to_sa (dloc prog) ?is_vis_var) \<subseteq> language_ltlc \<phi>"
        apply simp
        apply (auto simp: sm_to_sa.lang_def sm_to_sa.accept_def[abs_def])
        done
      hence "\<not>Collect (ample_impl.accept ?is_vis_var) \<subseteq> language_ltlc \<phi>"
        by (simp add: lang_ss_conv)
      with ample_reduction_correct[OF TY NF] have "\<not>Collect (ap_accept (dloc prog)) \<subseteq> language_ltlc \<phi>" 
        by simp
      moreover assume "Collect (ap_accept prog) \<subseteq> language_ltlc \<phi>"
      hence "Collect (ap_accept (dloc prog)) \<subseteq> language_ltlc \<phi>"
        using dloc_sim.accept_bisim[of prog] unfolding ap_accept_def[abs_def] 
        by auto
      ultimately show False ..
    }
  }
qed

export_code cava_sm checking SML

subsection \<open>Extraction of SML Code\<close>

definition "dflt_cfg \<equiv> (CFG_L2B_GERTHS,(),CFG_CE_SCC_GABOW)"

export_code (* Cava MC *)
            cava_bpc cava_promela dflt_cfg CAVA_Impl.CFG_CE_NDFS
            
            (* BP *)
            BoolProgs.print_config chose_prog list_progs
            BoolProgs_LTL_Conv.ltl_conv BoolProgs_LTL_Conv.CProp 
            BoolProgs_Programs.default_prog 
            BoolProgs_Programs.keys_of_map
            BoolProgs_Programs.default_prog BoolProgs_Programs.keys_of_map
            
            (* Promela *)
            printProcesses Promela.printConfigFromAST lookupLTL
            PromelaLTLConv.ltl_conv

            (* stat printing *)
            frv_export_code LTL_to_GBA_impl.create_name_gba_code

            (* Lasso *)
            lasso_v0 lasso_va lasso_reach lasso_cycle
            
            (* Arith *)
            nat_of_integer int_of_integer
            integer_of_nat integer_of_int
  checking SML 

code_identifier
  code_module String \<rightharpoonup> (SML) HOLString |
  code_module Code_Target_Int \<rightharpoonup> (SML) Code_Target_Int

export_code (* Cava MC *)
            cava_bpc cava_promela dflt_cfg CAVA_Impl.CFG_CE_NDFS
            
            (* BP *)
            BoolProgs.print_config chose_prog list_progs
            BoolProgs_LTL_Conv.ltl_conv BoolProgs_LTL_Conv.CProp 
            BoolProgs_Programs.default_prog 
            BoolProgs_Programs.keys_of_map
            BoolProgs_Programs.default_prog BoolProgs_Programs.keys_of_map
            
            (* Promela *)
            printProcesses Promela.printConfigFromAST lookupLTL
            PromelaLTLConv.ltl_conv PromelaLTLConv.CProp PromelaLTLConv.Eq PromelaLTLConv.Ident

            (* stat printing *)
            frv_export_code LTL_to_GBA_impl.create_name_gba_code

            (* Lasso *)
            lasso_v0 lasso_va lasso_reach lasso_cycle
            
            (* Arith *)
            nat_of_integer int_of_integer
            integer_of_nat integer_of_int

            (* String *)
            String.explode String.implode
  in SML
  file \<open>code/CAVA_Export.sml\<close>

end
