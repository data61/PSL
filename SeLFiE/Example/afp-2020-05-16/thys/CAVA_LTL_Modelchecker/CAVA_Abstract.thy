section \<open>Abstract Model-Checker\<close>
theory CAVA_Abstract
imports 
  CAVA_Base.CAVA_Base
  CAVA_Automata.Automata
  LTL.LTL
begin
text \<open>
  This theory defines the abstract version of the cava model checker, 
  as well as a generic implementation.
\<close>

subsection \<open>Specification of an LTL Model-Checker\<close>
text \<open>
  Abstractly, an LTL model-checker consists of three components:
  \begin{enumerate}
    \item A conversion of LTL-formula to Indexed Generalized Buchi Automata 
      (IGBA) over sets of atomic propositions.       
    \item An intersection construction, which takes a system and an IGBA, and 
      creates an Indexed Generalized Buchi Graph (IGBG) and a projection 
      function to project runs of the IGBG back to runs of the system.
    \item An emptiness check for IGBGs.
  \end{enumerate}
\<close>

text \<open>Given an LTL formula, the LTL to Buchi conversion
  returns a Generalized Buchi Automaton that accepts the same language.\<close>
definition ltl_to_gba_spec 
  :: "'prop ltlc \<Rightarrow> ('q, 'prop set, _) igba_rec_scheme nres"
  \<comment> \<open>Conversion of LTL formula to generalized buchi automaton\<close>  
  where "ltl_to_gba_spec \<phi> \<equiv> SPEC (\<lambda>gba. 
    igba.lang gba = language_ltlc \<phi> \<and> igba gba \<and> finite ((g_E gba)\<^sup>* `` g_V0 gba))"

definition inter_spec 
  :: "('s,'prop set,_) sa_rec_scheme 
  \<Rightarrow> ('q,'prop set,_) igba_rec_scheme
  \<Rightarrow> (('prod_state,_) igb_graph_rec_scheme \<times> ('prod_state \<Rightarrow> 's)) nres"
  \<comment> \<open>Intersection of system and IGBA\<close>
  where "\<And>sys ba. inter_spec sys ba \<equiv> do {
    ASSERT (sa sys);
    ASSERT (finite ((g_E sys)\<^sup>* `` g_V0 sys));
    ASSERT (igba ba);
    ASSERT (finite ((g_E ba)\<^sup>* `` g_V0 ba));
    SPEC (\<lambda>(G,project). igb_graph G \<and> finite ((g_E G)\<^sup>* `` g_V0 G) \<and> (\<forall>r. 
      (\<exists>r'. igb_graph.is_acc_run G r' \<and> r = project o r')
        \<longleftrightarrow> (graph_defs.is_run sys r \<and> sa_L sys o r \<in> igba.lang ba)))
  }"


definition find_ce_spec 
  :: "('q,_) igb_graph_rec_scheme \<Rightarrow> 'q word option option nres"
  \<comment> \<open>Check Generalized Buchi graph for emptiness, with optional counterexample\<close>
  where "find_ce_spec G \<equiv> do {
    ASSERT (igb_graph G);
    ASSERT (finite ((g_E G)\<^sup>* `` g_V0 G));
    SPEC (\<lambda>res. case res of 
      None \<Rightarrow> (\<forall>r. \<not>igb_graph.is_acc_run G r)
    | Some None \<Rightarrow> (\<exists>r. igb_graph.is_acc_run G r)
    | Some (Some r) \<Rightarrow> igb_graph.is_acc_run G r
    )}"

text \<open>
  Using the specifications from above, we can specify the essence
  of the model-checking algorithm: Convert the LTL-formula to a GBA,
  make an intersection with the system and check the result for emptiness.
\<close>

definition abs_model_check 
  :: "'ba_state itself \<Rightarrow> 'ba_more itself 
  \<Rightarrow> 'prod_state itself \<Rightarrow> 'prod_more itself
  \<Rightarrow> ('s,'prop set,_) sa_rec_scheme \<Rightarrow> 'prop ltlc 
  \<Rightarrow> 's word option option nres"
  where
  "abs_model_check _ _ _ _ sys \<phi> \<equiv> do {
    gba :: ('ba_state,_,'ba_more) igba_rec_scheme 
      \<leftarrow> ltl_to_gba_spec (Not_ltlc \<phi>);
    ASSERT (igba gba);
    ASSERT (sa sys);
    (Gprod::('prod_state,'prod_more)igb_graph_rec_scheme, map_state) 
      \<leftarrow> inter_spec sys gba;
    ASSERT (igb_graph Gprod);
    ce \<leftarrow> find_ce_spec Gprod;

    case ce of
      None \<Rightarrow> RETURN None
    | Some None \<Rightarrow> RETURN (Some None)
    | Some (Some r) \<Rightarrow> RETURN (Some (Some (map_state o r)))
  }"

text \<open>
  The main correctness theorem states that our abstract model checker
  really checks whether the system satisfies the formula, and a
  correct counterexample is returned (if any). 
  Note that, if the model does not satisfy the formula, 
  returning a counterexample is optional.
\<close>
theorem abs_model_check_correct:
  "abs_model_check T1 T2 T3 T4 sys \<phi> \<le> do {
    ASSERT (sa sys);
    ASSERT (finite ((g_E sys)\<^sup>* `` g_V0 sys));
    SPEC (\<lambda>res. case res of
      None \<Rightarrow> sa.lang sys \<subseteq> language_ltlc \<phi>
    | Some None \<Rightarrow> \<not> sa.lang sys \<subseteq> language_ltlc \<phi>
    | Some (Some r) \<Rightarrow> graph_defs.is_run sys r \<and> sa_L sys \<circ> r \<notin> language_ltlc \<phi>)
  }"
  unfolding abs_model_check_def ltl_to_gba_spec_def inter_spec_def 
    find_ce_spec_def
  apply (refine_rcg refine_vcg ASSERT_leI le_ASSERTI)
  apply (auto simp: sa.lang_def
    sa.accept_def[THEN meta_eq_to_obj_eq, THEN ext[of "sa.accept sys"] ]) 
    (* TODO: We really need an extended abs_def attribute, that digests 
      conditional definitions! *)
  done

subsection \<open>Generic Implementation\<close>
text \<open>
  In this section, we define a generic implementation of an LTL model checker,
  that is parameterized with implementations of its components.
\<close>

abbreviation "ltl_rel \<equiv> Id :: ('a ltlc \<times> _) set"

locale impl_model_checker =
  \<comment> \<open>Assembly of a generic model-checker\<close>
  fixes sa_rel :: "('sai \<times> ('s,'prop set,'sa_more) sa_rec_scheme) set"
  fixes igba_rel :: "('igbai \<times> ('q, 'prop set, 'igba_more) igba_rec_scheme) set"
  fixes igbg_rel :: "('igbgi \<times> ('sq, 'igbg_more) igb_graph_rec_scheme) set"
  fixes ce_rel :: "('cei \<times> 'sq word) set"
  fixes mce_rel :: "('mcei \<times> 's word) set"
  
  fixes ltl_to_gba_impl :: "'cfg_l2b \<Rightarrow> 'prop ltlc \<Rightarrow> 'igbai"
  fixes inter_impl :: "'cfg_int \<Rightarrow> 'sai \<Rightarrow> 'igbai \<Rightarrow> 'igbgi \<times> ('sq \<Rightarrow> 's)"
  fixes find_ce_impl :: "'cfg_ce \<Rightarrow> 'igbgi \<Rightarrow> 'cei option option"
  fixes map_run_impl :: "('sq \<Rightarrow> 's) \<Rightarrow> 'cei \<Rightarrow> 'mcei"

  assumes [relator_props, simp, intro!]: "single_valued mce_rel"

  assumes ltl_to_gba_refine: 
    "\<And>cfg. (ltl_to_gba_impl cfg,ltl_to_gba_spec) 
      \<in> ltl_rel \<rightarrow> \<langle>igba_rel\<rangle>plain_nres_rel"
  assumes inter_refine: 
    "\<And>cfg. (inter_impl cfg,inter_spec) 
      \<in> sa_rel \<rightarrow> igba_rel \<rightarrow> \<langle>igbg_rel \<times>\<^sub>r (Id \<rightarrow> Id)\<rangle>plain_nres_rel"
  assumes find_ce_refine: 
    "\<And>cfg. (find_ce_impl cfg,find_ce_spec)
      \<in> igbg_rel \<rightarrow> \<langle>\<langle>\<langle>ce_rel\<rangle>option_rel\<rangle>option_rel\<rangle>plain_nres_rel"

  assumes map_run_refine: "(map_run_impl,(o)) \<in> (Id \<rightarrow> Id) \<rightarrow> ce_rel \<rightarrow> mce_rel"


begin


  fun cfg_l2b where "cfg_l2b (c1,c2,c3) = c1"
  fun cfg_int where "cfg_int (c1,c2,c3) = c2"
  fun cfg_ce where "cfg_ce (c1,c2,c3) = c3"

  definition impl_model_check 
    :: "('cfg_l2b\<times>'cfg_int\<times>'cfg_ce) 
      \<Rightarrow> 'sai \<Rightarrow> 'prop ltlc \<Rightarrow> 'mcei option option"
    where
    "impl_model_check cfg sys \<phi> \<equiv> let
      ba = ltl_to_gba_impl (cfg_l2b cfg) (Not_ltlc \<phi>);
      (G,map_q) = inter_impl (cfg_int cfg) sys ba;
      ce = find_ce_impl (cfg_ce cfg) G
    in
      case ce of
        None \<Rightarrow> None
      | Some None \<Rightarrow> Some None
      | Some (Some ce) \<Rightarrow> Some (Some (map_run_impl map_q ce))"
  
  lemma impl_model_check_refine:
    "(impl_model_check cfg,abs_model_check 
        TYPE('q) TYPE('igba_more) TYPE('sq) TYPE('igbg_more)) 
      \<in> sa_rel \<rightarrow> ltl_rel \<rightarrow> \<langle>\<langle>\<langle>mce_rel\<rangle>option_rel\<rangle>option_rel\<rangle>plain_nres_rel"
    apply (intro fun_relI plain_nres_relI)
    unfolding abs_model_check_def impl_model_check_def

    apply (simp only: let_to_bind_conv pull_out_let_conv 
      pull_out_RETURN_case_option)

    apply (refine_rcg
      ltl_to_gba_refine[param_fo, THEN plain_nres_relD]
      rel_arg_cong[where f="Not_ltlc"]
      inter_refine[param_fo, THEN plain_nres_relD]
      find_ce_refine[param_fo, THEN plain_nres_relD]
    )

    apply (simp_all split: option.split)
    apply (auto elim: option_relE)
    apply (parametricity add: map_run_refine)
    apply simp
    done

  theorem impl_model_check_correct:
    assumes R: "(sysi,sys)\<in>sa_rel"
    assumes [simp]: "sa sys" "finite ((g_E sys)\<^sup>* `` g_V0 sys)"
    shows "case impl_model_check cfg sysi \<phi> of
      None 
        \<Rightarrow> sa.lang sys \<subseteq> language_ltlc \<phi>
    | Some None 
        \<Rightarrow> \<not> sa.lang sys \<subseteq> language_ltlc \<phi>
    | Some (Some ri) 
        \<Rightarrow> (\<exists>r. (ri,r)\<in>mce_rel 
           \<and> graph_defs.is_run sys r \<and> sa_L sys o r \<notin> language_ltlc \<phi>)"
  proof -
    note impl_model_check_refine[
      where cfg=cfg,
      param_fo, 
      THEN plain_nres_relD, 
      OF R IdI[of \<phi>]]
    also note abs_model_check_correct
    finally show ?thesis 
      apply (simp split: option.split)
      apply (simp add: refine_pw_simps pw_le_iff)
      apply (auto elim!: option_relE) []
      done
  qed

  theorem impl_model_check_correct_no_ce:
    assumes "(sysi,sys)\<in>sa_rel"
    assumes SA: "sa sys" "finite ((g_E sys)\<^sup>* `` g_V0 sys)"
    shows "impl_model_check cfg sysi \<phi> = None 
    \<longleftrightarrow> sa.lang sys \<subseteq> language_ltlc \<phi>"
    using impl_model_check_correct[where cfg=cfg, OF assms, of \<phi>]
    by (auto 
      split: option.splits 
      simp: sa.lang_def[OF SA(1)] sa.accept_def[OF SA(1), abs_def])

end


end
