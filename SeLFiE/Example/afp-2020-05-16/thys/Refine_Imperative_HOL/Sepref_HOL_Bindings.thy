section \<open>HOL Setup\<close>
theory Sepref_HOL_Bindings
imports Sepref_Tool
begin

subsection \<open>Assertion Annotation\<close>
text \<open>Annotate an assertion to a term. The term must then be refined with this assertion.\<close>
(* TODO: Version for monadic expressions.*)
definition ASSN_ANNOT :: "('a \<Rightarrow> 'ai \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> 'a" where [simp]: "ASSN_ANNOT A x \<equiv> x"
context fixes A :: "'a \<Rightarrow> 'ai \<Rightarrow> assn" begin
  sepref_register "PR_CONST (ASSN_ANNOT A)"
  lemma [def_pat_rules]: "ASSN_ANNOT$A \<equiv> UNPROTECT (ASSN_ANNOT A)" by simp
  lemma [sepref_fr_rules]: "(return o (\<lambda>x. x), RETURN o PR_CONST (ASSN_ANNOT A)) \<in> A\<^sup>d\<rightarrow>\<^sub>aA"
    by sepref_to_hoare sep_auto
end  

lemma annotate_assn: "x \<equiv> ASSN_ANNOT A x" by simp

subsection \<open>Shortcuts\<close>
abbreviation "nat_assn \<equiv> (id_assn::nat \<Rightarrow> _)"
abbreviation "int_assn \<equiv> (id_assn::int \<Rightarrow> _)"
abbreviation "bool_assn \<equiv> (id_assn::bool \<Rightarrow> _)"

subsection \<open>Identity Relations\<close>
definition "IS_ID R \<equiv> R=Id"
definition "IS_BELOW_ID R \<equiv> R\<subseteq>Id"

lemma [safe_constraint_rules]: 
  "IS_ID Id"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<rightarrow> R2)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>option_rel)"
  "IS_ID R \<Longrightarrow> IS_ID (\<langle>R\<rangle>list_rel)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (R1 \<times>\<^sub>r R2)"
  "IS_ID R1 \<Longrightarrow> IS_ID R2 \<Longrightarrow> IS_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def)

lemma [safe_constraint_rules]: 
  "IS_BELOW_ID Id"
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>option_rel)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<times>\<^sub>r R2)"
  "IS_BELOW_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (\<langle>R1,R2\<rangle>sum_rel)"
  by (auto simp: IS_ID_def IS_BELOW_ID_def option_rel_def sum_rel_def list_rel_def)

lemma IS_BELOW_ID_fun_rel_aux: "R1\<supseteq>Id \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  by (auto simp: IS_BELOW_ID_def dest: fun_relD)

corollary IS_BELOW_ID_fun_rel[safe_constraint_rules]: 
  "IS_ID R1 \<Longrightarrow> IS_BELOW_ID R2 \<Longrightarrow> IS_BELOW_ID (R1 \<rightarrow> R2)"
  using IS_BELOW_ID_fun_rel_aux[of Id R2]
  by (auto simp: IS_ID_def)


lemma IS_BELOW_ID_list_rel[safe_constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>list_rel)"
  unfolding IS_BELOW_ID_def
proof safe
  fix l l'
  assume A: "R\<subseteq>Id" 
  assume "(l,l')\<in>\<langle>R\<rangle>list_rel"
  thus "l=l'"
    apply induction
    using A by auto
qed

lemma IS_ID_imp_BELOW_ID[constraint_rules]: 
  "IS_ID R \<Longrightarrow> IS_BELOW_ID R"
  by (auto simp: IS_ID_def IS_BELOW_ID_def )



subsection \<open>Inverse Relation\<close>

lemma inv_fun_rel_eq[simp]: "(A\<rightarrow>B)\<inverse> = A\<inverse>\<rightarrow>B\<inverse>"
  by (auto dest: fun_relD)

lemma inv_option_rel_eq[simp]: "(\<langle>K\<rangle>option_rel)\<inverse> = \<langle>K\<inverse>\<rangle>option_rel"
  by (auto simp: option_rel_def)

lemma inv_prod_rel_eq[simp]: "(P \<times>\<^sub>r Q)\<inverse> = P\<inverse> \<times>\<^sub>r Q\<inverse>"
  by (auto)

lemma inv_sum_rel_eq[simp]: "(\<langle>P,Q\<rangle>sum_rel)\<inverse> = \<langle>P\<inverse>,Q\<inverse>\<rangle>sum_rel"
  by (auto simp: sum_rel_def)

lemma inv_list_rel_eq[simp]: "(\<langle>R\<rangle>list_rel)\<inverse> = \<langle>R\<inverse>\<rangle>list_rel"
  unfolding list_rel_def
  apply safe
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  apply (subst list.rel_flip[symmetric])
  apply (simp add: conversep_iff[abs_def])
  done

lemmas [constraint_simps] =
  Relation.converse_Id
  inv_fun_rel_eq
  inv_option_rel_eq
  inv_prod_rel_eq
  inv_sum_rel_eq
  inv_list_rel_eq


subsection \<open>Single Valued and Total Relations\<close>

(* TODO: Link to other such theories: Transfer, Autoref *)
definition "IS_LEFT_UNIQUE R \<equiv> single_valued (R\<inverse>)"
definition "IS_LEFT_TOTAL R \<equiv> Domain R = UNIV"
definition "IS_RIGHT_TOTAL R \<equiv> Range R = UNIV"
abbreviation (input) "IS_RIGHT_UNIQUE \<equiv> single_valued"

lemmas IS_RIGHT_UNIQUED = single_valuedD
lemma IS_LEFT_UNIQUED: "\<lbrakk>IS_LEFT_UNIQUE r; (y, x) \<in> r; (z, x) \<in> r\<rbrakk> \<Longrightarrow> y = z"
  by (auto simp: IS_LEFT_UNIQUE_def dest: single_valuedD)

lemma prop2p:
  "IS_LEFT_UNIQUE R = left_unique (rel2p R)"
  "IS_RIGHT_UNIQUE R = right_unique (rel2p R)"
  "right_unique (rel2p (R\<inverse>)) = left_unique (rel2p R)"
  "IS_LEFT_TOTAL R = left_total (rel2p R)"
  "IS_RIGHT_TOTAL R = right_total (rel2p R)"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: rel2p_def
    )

lemma p2prop:
  "left_unique P = IS_LEFT_UNIQUE (p2rel P)"
  "right_unique P = IS_RIGHT_UNIQUE (p2rel P)"
  "left_total P = IS_LEFT_TOTAL (p2rel P)"
  "right_total P = IS_RIGHT_TOTAL (p2rel P)"
  "bi_unique P \<longleftrightarrow> left_unique P \<and> right_unique P"
  by (auto 
    simp: IS_LEFT_UNIQUE_def left_unique_def single_valued_def
    simp: right_unique_def bi_unique_alt_def
    simp: IS_LEFT_TOTAL_def left_total_def
    simp: IS_RIGHT_TOTAL_def right_total_def
    simp: p2rel_def
    )

lemmas [safe_constraint_rules] = 
  single_valued_Id  
  prod_rel_sv 
  list_rel_sv 
  option_rel_sv 
  sum_rel_sv

lemma [safe_constraint_rules]:
  "IS_LEFT_UNIQUE Id"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (R1\<times>\<^sub>rR2)"
  "IS_LEFT_UNIQUE R1 \<Longrightarrow> IS_LEFT_UNIQUE R2 \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>option_rel)"
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (\<langle>R\<rangle>list_rel)"
  by (auto simp: IS_LEFT_UNIQUE_def prod_rel_sv sum_rel_sv option_rel_sv list_rel_sv)

lemma IS_LEFT_TOTAL_alt: "IS_LEFT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (x,y)\<in>R)"
  by (auto simp: IS_LEFT_TOTAL_def)

lemma IS_RIGHT_TOTAL_alt: "IS_RIGHT_TOTAL R \<longleftrightarrow> (\<forall>x. \<exists>y. (y,x)\<in>R)"
  by (auto simp: IS_RIGHT_TOTAL_def)

lemma [safe_constraint_rules]:
  "IS_LEFT_TOTAL Id"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_LEFT_TOTAL R1 \<Longrightarrow> IS_LEFT_TOTAL R2 \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_LEFT_TOTAL_alt sum_rel_def option_rel_def list_rel_def)
  apply (rename_tac x; case_tac x; auto)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_LEFT_TOTAL R \<Longrightarrow> IS_LEFT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_LEFT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (x,y)\<in>R"
  fix l
  show "\<exists>l'. (l,l')\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_right_iff)
qed

lemma [safe_constraint_rules]:
  "IS_RIGHT_TOTAL Id"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (R1\<times>\<^sub>rR2)"
  "IS_RIGHT_TOTAL R1 \<Longrightarrow> IS_RIGHT_TOTAL R2 \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R1,R2\<rangle>sum_rel)"
  "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>option_rel)"
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (auto simp: IS_RIGHT_TOTAL_alt sum_rel_def option_rel_def) []
  apply (rename_tac x; case_tac x; auto)
  apply (clarsimp simp: IS_RIGHT_TOTAL_alt option_rel_def)
  apply (rename_tac x; case_tac x; auto)
  done

lemma [safe_constraint_rules]: "IS_RIGHT_TOTAL R \<Longrightarrow> IS_RIGHT_TOTAL (\<langle>R\<rangle>list_rel)"
  unfolding IS_RIGHT_TOTAL_alt
proof safe
  assume A: "\<forall>x.\<exists>y. (y,x)\<in>R"
  fix l
  show "\<exists>l'. (l',l)\<in>\<langle>R\<rangle>list_rel"
    apply (induction l)
    using A
    by (auto simp: list_rel_split_left_iff)
qed
  
lemma [constraint_simps]:
  "IS_LEFT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_RIGHT_TOTAL R "
  "IS_RIGHT_TOTAL (R\<inverse>) \<longleftrightarrow> IS_LEFT_TOTAL R  "
  "IS_LEFT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_RIGHT_UNIQUE R"
  "IS_RIGHT_UNIQUE (R\<inverse>) \<longleftrightarrow> IS_LEFT_UNIQUE R "
  by (auto simp: IS_RIGHT_TOTAL_alt IS_LEFT_TOTAL_alt IS_LEFT_UNIQUE_def)

lemma [safe_constraint_rules]:
  "IS_RIGHT_UNIQUE A \<Longrightarrow> IS_RIGHT_TOTAL B \<Longrightarrow> IS_RIGHT_TOTAL (A\<rightarrow>B)"
  "IS_RIGHT_TOTAL A \<Longrightarrow> IS_RIGHT_UNIQUE B \<Longrightarrow> IS_RIGHT_UNIQUE (A\<rightarrow>B)"
  "IS_LEFT_UNIQUE A \<Longrightarrow> IS_LEFT_TOTAL B \<Longrightarrow> IS_LEFT_TOTAL (A\<rightarrow>B)"
  "IS_LEFT_TOTAL A \<Longrightarrow> IS_LEFT_UNIQUE B \<Longrightarrow> IS_LEFT_UNIQUE (A\<rightarrow>B)"
  apply (simp_all add: prop2p rel2p)
  (*apply transfer_step TODO: Isabelle 2016 *)
  apply (blast intro!: transfer_raw)+
  done

lemma [constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_RIGHT_UNIQUE R"
  "IS_BELOW_ID R \<Longrightarrow> IS_LEFT_UNIQUE R"
  "IS_ID R \<Longrightarrow> IS_RIGHT_TOTAL R"
  "IS_ID R \<Longrightarrow> IS_LEFT_TOTAL R"
  by (auto simp: IS_BELOW_ID_def IS_ID_def IS_LEFT_UNIQUE_def IS_RIGHT_TOTAL_def IS_LEFT_TOTAL_def
    intro: single_valuedI)

thm constraint_rules

subsubsection \<open>Additional Parametricity Lemmas\<close>
(* TODO: Move. Problem: Depend on IS_LEFT_UNIQUE, which has to be moved to!*)

lemma param_distinct[param]: "\<lbrakk>IS_LEFT_UNIQUE A; IS_RIGHT_UNIQUE A\<rbrakk> \<Longrightarrow> (distinct, distinct) \<in> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"  
  apply (fold rel2p_def)
  apply (simp add: rel2p)
  apply (rule distinct_transfer)
  apply (simp add: p2prop)
  done

lemma param_Image[param]: 
  assumes "IS_LEFT_UNIQUE A" "IS_RIGHT_UNIQUE A"
  shows "((``), (``)) \<in> \<langle>A\<times>\<^sub>rB\<rangle>set_rel \<rightarrow> \<langle>A\<rangle>set_rel \<rightarrow> \<langle>B\<rangle>set_rel"
  apply (clarsimp simp: set_rel_def; intro conjI)  
  apply (fastforce dest: IS_RIGHT_UNIQUED[OF assms(2)])
  apply (fastforce dest: IS_LEFT_UNIQUED[OF assms(1)])
  done

lemma pres_eq_iff_svb: "((=),(=))\<in>K\<rightarrow>K\<rightarrow>bool_rel \<longleftrightarrow> (single_valued K \<and> single_valued (K\<inverse>))"
  apply (safe intro!: single_valuedI)
  apply (metis (full_types) IdD fun_relD1)
  apply (metis (full_types) IdD fun_relD1)
  by (auto dest: single_valuedD)

definition "IS_PRES_EQ R \<equiv> ((=), (=))\<in>R\<rightarrow>R\<rightarrow>bool_rel"
lemma [constraint_rules]: "\<lbrakk>single_valued R; single_valued (R\<inverse>)\<rbrakk> \<Longrightarrow> IS_PRES_EQ R"
  by (simp add: pres_eq_iff_svb IS_PRES_EQ_def)


subsection \<open>Bounded Assertions\<close>
definition "b_rel R P \<equiv> R \<inter> UNIV\<times>Collect P"
definition "b_assn A P \<equiv> \<lambda>x y. A x y * \<up>(P x)"

lemma b_assn_pure_conv[constraint_simps]: "b_assn (pure R) P = pure (b_rel R P)"
  by (auto intro!: ext simp: b_rel_def b_assn_def pure_def)
lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] 
  = b_assn_pure_conv[symmetric]

lemma b_rel_nesting[simp]: 
  "b_rel (b_rel R P1) P2 = b_rel R (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_rel_def)
lemma b_rel_triv[simp]: 
  "b_rel R (\<lambda>_. True) = R"
  by (auto simp: b_rel_def)
lemma b_assn_nesting[simp]: 
  "b_assn (b_assn A P1) P2 = b_assn A (\<lambda>x. P1 x \<and> P2 x)"
  by (auto simp: b_assn_def pure_def intro!: ext)
lemma b_assn_triv[simp]: 
  "b_assn A (\<lambda>_. True) = A"
  by (auto simp: b_assn_def pure_def intro!: ext)

lemmas [simp,constraint_simps,sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold]
  = b_rel_nesting b_assn_nesting

lemma b_rel_simp[simp]: "(x,y)\<in>b_rel R P \<longleftrightarrow> (x,y)\<in>R \<and> P y"
  by (auto simp: b_rel_def)

lemma b_assn_simp[simp]: "b_assn A P x y = A x y * \<up>(P x)"
  by (auto simp: b_assn_def)

lemma b_rel_Range[simp]: "Range (b_rel R P) = Range R \<inter> Collect P" by auto
lemma b_assn_rdom[simp]: "rdomp (b_assn R P) x \<longleftrightarrow> rdomp R x \<and> P x"
  by (auto simp: rdomp_def)


lemma b_rel_below_id[constraint_rules]: 
  "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (b_rel R P)"
  by (auto simp: IS_BELOW_ID_def)

lemma b_rel_left_unique[constraint_rules]: 
  "IS_LEFT_UNIQUE R \<Longrightarrow> IS_LEFT_UNIQUE (b_rel R P)"
  by (auto simp: IS_LEFT_UNIQUE_def single_valued_def)
  
lemma b_rel_right_unique[constraint_rules]: 
  "IS_RIGHT_UNIQUE R \<Longrightarrow> IS_RIGHT_UNIQUE (b_rel R P)"
  by (auto simp: single_valued_def)

\<comment> \<open>Registered as safe rule, although may loose information in the 
    odd case that purity depends condition.\<close>
lemma b_assn_is_pure[safe_constraint_rules]:
  "is_pure A \<Longrightarrow> is_pure (b_assn A P)"
  by (auto simp: is_pure_conv b_assn_pure_conv)

\<comment> \<open>Most general form\<close>
lemma b_assn_subtyping_match[sepref_frame_match_rules]:
  assumes "hn_ctxt (b_assn A P) x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); vassn_tag (hn_ctxt A' x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def mod_star_conv)
  
\<comment> \<open>Simplified forms:\<close>
lemma b_assn_subtyping_match_eqA[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y); P x\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt (b_assn A P) x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A P') x y"
  apply (rule b_assn_subtyping_match)
  subgoal 
    unfolding hn_ctxt_def b_assn_def entailst_def entails_def
    by (fastforce simp: vassn_tag_def mod_star_conv)
  subgoal
    using assms .
  done  

lemma b_assn_subtyping_match_tR[sepref_frame_match_rules]:
  assumes "\<lbrakk>P x\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y"
  shows "hn_ctxt (b_assn A P) x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def mod_star_conv)

lemma b_assn_subtyping_match_tL[sepref_frame_match_rules]:
  assumes "hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y"
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A' P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def mod_star_conv)


lemma b_assn_subtyping_match_eqA_tR[sepref_frame_match_rules]: 
  "hn_ctxt (b_assn A P) x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  unfolding hn_ctxt_def b_assn_def
  by (sep_auto intro!: enttI)

lemma b_assn_subtyping_match_eqA_tL[sepref_frame_match_rules]:
  assumes "\<lbrakk>vassn_tag (hn_ctxt A x y)\<rbrakk> \<Longrightarrow> P' x"
  shows "hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A P') x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def mod_star_conv)

\<comment> \<open>General form\<close>
lemma b_rel_subtyping_merge[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn Am (\<lambda>x. P x \<or> P' x)) x y"
  using assms
  unfolding hn_ctxt_def b_assn_def entailst_def entails_def
  by (fastforce simp: vassn_tag_def)
  
\<comment> \<open>Simplified forms\<close>
lemma b_rel_subtyping_merge_eqA[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  apply (rule b_rel_subtyping_merge)
  by simp

lemma b_rel_subtyping_merge_tL[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A' P') x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am "\<lambda>_. True" P', simplified] assms .

lemma b_rel_subtyping_merge_tR[sepref_frame_merge_rules]:
  assumes "hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  using b_rel_subtyping_merge[of A x y A' Am P "\<lambda>_. True", simplified] assms .

lemma b_rel_subtyping_merge_eqA_tL[sepref_frame_merge_rules]:
  shows "hn_ctxt A x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A "\<lambda>_. True" x y P', simplified] .

lemma b_rel_subtyping_merge_eqA_tR[sepref_frame_merge_rules]:
  shows "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A x y"
  using b_rel_subtyping_merge_eqA[of A P x y "\<lambda>_. True", simplified] .

(* TODO: Combinatorial explosion :( *)
lemma b_assn_invalid_merge1: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge2: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge3: "hn_invalid A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge4: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt (b_assn A P') x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge5: "hn_ctxt (b_assn A P') x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid (b_assn A (\<lambda>x. P x \<or> P' x)) x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge6: "hn_invalid (b_assn A P) x y \<or>\<^sub>A hn_ctxt A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge7: "hn_ctxt A x y \<or>\<^sub>A hn_invalid (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemma b_assn_invalid_merge8: "hn_ctxt (b_assn A P) x y \<or>\<^sub>A hn_invalid A x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)
lemma b_assn_invalid_merge9: "hn_invalid A x y \<or>\<^sub>A hn_ctxt (b_assn A P) x y
  \<Longrightarrow>\<^sub>t hn_invalid A x y"
  by (sep_auto simp: hn_ctxt_def invalid_assn_def entailst_def)

lemmas b_assn_invalid_merge[sepref_frame_merge_rules] = 
  b_assn_invalid_merge1
  b_assn_invalid_merge2
  b_assn_invalid_merge3
  b_assn_invalid_merge4
  b_assn_invalid_merge5
  b_assn_invalid_merge6
  b_assn_invalid_merge7
  b_assn_invalid_merge8
  b_assn_invalid_merge9




(*
lemma list_rel_b_id: "\<forall>x\<in>set l. B x \<Longrightarrow> (l,l)\<in>\<langle>b_rel B\<rangle>list_rel"
  by (induction l) auto
*)


abbreviation nbn_rel :: "nat \<Rightarrow> (nat \<times> nat) set" 
  \<comment> \<open>Natural numbers with upper bound.\<close>
  where "nbn_rel n \<equiv> b_rel nat_rel (\<lambda>x::nat. x<n)"  

abbreviation nbn_assn :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> assn" 
  \<comment> \<open>Natural numbers with upper bound.\<close>
  where "nbn_assn n \<equiv> b_assn nat_assn (\<lambda>x::nat. x<n)"  

(*
subsection \<open>Bounded Identity Relations\<close>
definition "b_rel B \<equiv> {(x,x) | x. B x}"

lemma b_rel_simp[simp]: "(x,y)\<in>b_rel B \<longleftrightarrow> x=y \<and> B y"
  by (auto simp: b_rel_def)

lemma b_rel_Range[simp]: "Range (b_rel B) = Collect B" by auto

lemma b_rel_below_id[safe_constraint_rules]: "IS_BELOW_ID (b_rel B)"
  by (auto simp: IS_BELOW_ID_def)

lemma list_rel_b_id: "\<forall>x\<in>set l. B x \<Longrightarrow> (l,l)\<in>\<langle>b_rel B\<rangle>list_rel"
  by (induction l) auto

lemma b_rel_subtyping_match[sepref_frame_match_rules]:
  "P x \<Longrightarrow> hn_val Id x y \<Longrightarrow>\<^sub>t hn_val (b_rel P) x y"
  "\<lbrakk>P1 x \<Longrightarrow> P2 x\<rbrakk> \<Longrightarrow> hn_val (b_rel P1) x y \<Longrightarrow>\<^sub>t hn_val (b_rel P2) x y"
  "hn_val (b_rel P) x y \<Longrightarrow>\<^sub>t hn_val Id x y"
  by (auto simp: hn_ctxt_def pure_def intro: enttI)

lemma b_rel_subtyping_merge[sepref_frame_merge_rules]:
  "hn_val Id x y \<or>\<^sub>A hn_val (b_rel P) x y \<Longrightarrow>\<^sub>t hn_val Id x y"
  "hn_val (b_rel P) x y \<or>\<^sub>A hn_val Id x y \<Longrightarrow>\<^sub>t hn_val Id x y"
  "hn_val (b_rel P1) x y \<or>\<^sub>A hn_val (b_rel P2) x y \<Longrightarrow>\<^sub>t hn_val (b_rel (\<lambda>x. P1 x \<or> P2 x)) x y"
  by (auto simp: hn_ctxt_def pure_def intro: enttI)


abbreviation nbn_rel :: "nat \<Rightarrow> (nat \<times> nat) set" 
  -- \<open>Natural numbers with upper bound.\<close>
  where "nbn_rel n \<equiv> b_rel (\<lambda>x::nat. x<n)"  


*)


subsection \<open>Tool Setup\<close>
lemmas [sepref_relprops] = 
  sepref_relpropI[of IS_LEFT_UNIQUE]
  sepref_relpropI[of IS_RIGHT_UNIQUE]
  sepref_relpropI[of IS_LEFT_TOTAL]
  sepref_relpropI[of IS_RIGHT_TOTAL]
  sepref_relpropI[of is_pure]
  sepref_relpropI[of "IS_PURE \<Phi>" for \<Phi>]
  sepref_relpropI[of IS_ID]
  sepref_relpropI[of IS_BELOW_ID]
 


lemma [sepref_relprops_simps]:
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_BELOW_ID) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_TOTAL) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) A"
  "CONSTRAINT (IS_PURE IS_BELOW_ID) A \<Longrightarrow> CONSTRAINT (IS_PURE IS_RIGHT_UNIQUE) A"
  by (auto 
    simp: IS_ID_def IS_BELOW_ID_def IS_PURE_def IS_LEFT_UNIQUE_def
    simp: IS_LEFT_TOTAL_def IS_RIGHT_TOTAL_def
    simp: single_valued_below_Id)

declare True_implies_equals[sepref_relprops_simps]

lemma [sepref_relprops_transform]: "single_valued (R\<inverse>) = IS_LEFT_UNIQUE R"
  by (auto simp: IS_LEFT_UNIQUE_def)


subsection \<open>HOL Combinators\<close>
lemma hn_if[sepref_comb_rules]:
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>1 * hn_val bool_rel a a'"
  assumes RT: "a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') c' \<Gamma>2c R c"
  assumes IMP: "TERM If \<Longrightarrow> \<Gamma>2b \<or>\<^sub>A \<Gamma>2c \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (if a' then b' else c') \<Gamma>' R (If$a$b$c)"
  using P RT RE IMP[OF TERMI]
  unfolding APP_def PROTECT2_def 
  by (rule hnr_If)

lemmas [sepref_opt_simps] = if_True if_False

lemma hn_let[sepref_comb_rules]:
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>1 * hn_ctxt R v v'"
  assumes R: "\<And>x x'. x=v \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt R x x') (f' x') 
    (\<Gamma>' x x') R2 (f x)"
  assumes F: "\<And>x x'. \<Gamma>' x x' \<Longrightarrow>\<^sub>t \<Gamma>2 * hn_ctxt R' x x'"
  shows 
    "hn_refine \<Gamma> (Let v' f') (\<Gamma>2 * hn_ctxt R' v v') R2 (Let$v$(\<lambda>\<^sub>2x. f x))"
  apply (rule hn_refine_cons[OF P _ F entt_refl])
  apply (simp)
  apply (rule R)
  by simp

subsection \<open>Basic HOL types\<close>

lemma hnr_default[sepref_import_param]: "(default,default)\<in>Id" by simp

lemma unit_hnr[sepref_import_param]: "((),())\<in>unit_rel" by auto
    
lemmas [sepref_import_param] = 
  param_bool
  param_nat1
  param_int

lemmas [id_rules] = 
  itypeI[Pure.of 0 "TYPE (nat)"]
  itypeI[Pure.of 0 "TYPE (int)"]
  itypeI[Pure.of 1 "TYPE (nat)"]
  itypeI[Pure.of 1 "TYPE (int)"]
  itypeI[Pure.of numeral "TYPE (num \<Rightarrow> nat)"]
  itypeI[Pure.of numeral "TYPE (num \<Rightarrow> int)"]
  itype_self[of num.One]
  itype_self[of num.Bit0]
  itype_self[of num.Bit1]

lemma param_min_nat[param,sepref_import_param]: "(min,min)\<in>nat_rel \<rightarrow> nat_rel \<rightarrow> nat_rel" by auto
lemma param_max_nat[param,sepref_import_param]: "(max,max)\<in>nat_rel \<rightarrow> nat_rel \<rightarrow> nat_rel" by auto

lemma param_min_int[param,sepref_import_param]: "(min,min)\<in>int_rel \<rightarrow> int_rel \<rightarrow> int_rel" by auto
lemma param_max_int[param,sepref_import_param]: "(max,max)\<in>int_rel \<rightarrow> int_rel \<rightarrow> int_rel" by auto

lemma uminus_hnr[sepref_import_param]: "(uminus,uminus)\<in>int_rel \<rightarrow> int_rel" by auto
    
lemma nat_param[param,sepref_import_param]: "(nat,nat) \<in> int_rel \<rightarrow> nat_rel" by auto
lemma int_param[param,sepref_import_param]: "(int,int) \<in> nat_rel \<rightarrow> int_rel" by auto
      
      
      
subsection "Product"


lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] = prod_assn_pure_conv[symmetric]

lemma prod_assn_precise[constraint_rules]: 
  "precise P1 \<Longrightarrow> precise P2 \<Longrightarrow> precise (prod_assn P1 P2)"
  apply rule
  apply (clarsimp simp: prod_assn_def star_assoc)
  apply safe
  apply (erule (1) prec_frame) apply frame_inference+
  apply (erule (1) prec_frame) apply frame_inference+
  done

lemma  
  "precise P1 \<Longrightarrow> precise P2 \<Longrightarrow> precise (prod_assn P1 P2)" \<comment> \<open>Original proof\<close>
  apply rule
  apply (clarsimp simp: prod_assn_def)
proof (rule conjI)
  fix F F' h as a b a' b' ap bp
  assume P1: "precise P1" and P2: "precise P2"
  assume F: "(h, as) \<Turnstile> P1 a ap * P2 b bp * F \<and>\<^sub>A P1 a' ap * P2 b' bp * F'"

  from F have "(h, as) \<Turnstile> P1 a ap * (P2 b bp * F) \<and>\<^sub>A P1 a' ap * (P2 b' bp * F')"
    by (simp only: mult.assoc)
  with preciseD[OF P1] show "a=a'" .
  from F have "(h, as) \<Turnstile> P2 b bp * (P1 a ap * F) \<and>\<^sub>A P2 b' bp * (P1 a' ap * F')"
    by (simp only: mult.assoc[where 'a=assn] mult.commute[where 'a=assn] mult.left_commute[where 'a=assn])
  with preciseD[OF P2] show "b=b'" .
qed

(* TODO Add corresponding rules for other types and add to datatype snippet *)
lemma intf_of_prod_assn[intf_of_assn]:
  assumes "intf_of_assn A TYPE('a)" "intf_of_assn B TYPE('b)"
  shows "intf_of_assn (prod_assn A B) TYPE('a * 'b)"
by simp

lemma pure_prod[constraint_rules]: 
  assumes P1: "is_pure P1" and P2: "is_pure P2"
  shows "is_pure (prod_assn P1 P2)"
proof -
  from P1 obtain P1' where P1': "\<And>x x'. P1 x x' = \<up>(P1' x x')"
    using is_pureE by blast
  from P2 obtain P2' where P2': "\<And>x x'. P2 x x' = \<up>(P2' x x')"
    using is_pureE by blast

  show ?thesis proof
    fix x x'
    show "prod_assn P1 P2 x x' =
         \<up> (case (x, x') of ((a1, a2), c1, c2) \<Rightarrow> P1' a1 c1 \<and> P2' a2 c2)"
      unfolding prod_assn_def
      apply (simp add: P1' P2' split: prod.split)
      done
  qed
qed

lemma prod_frame_match[sepref_frame_match_rules]:
  assumes "hn_ctxt A (fst x) (fst y) \<Longrightarrow>\<^sub>t hn_ctxt A' (fst x) (fst y)"
  assumes "hn_ctxt B (snd x) (snd y) \<Longrightarrow>\<^sub>t hn_ctxt B' (snd x) (snd y)"
  shows "hn_ctxt (prod_assn A B) x y \<Longrightarrow>\<^sub>t hn_ctxt (prod_assn A' B') x y"
  apply (cases x; cases y; simp)
  apply (simp add: hn_ctxt_def)
  apply (rule entt_star_mono)
  using assms apply (auto simp: hn_ctxt_def)
  done

lemma prod_frame_merge[sepref_frame_merge_rules]:   
  assumes "hn_ctxt A (fst x) (fst y) \<or>\<^sub>A hn_ctxt A' (fst x) (fst y) \<Longrightarrow>\<^sub>t hn_ctxt Am (fst x) (fst y)"
  assumes "hn_ctxt B (snd x) (snd y) \<or>\<^sub>A hn_ctxt B' (snd x) (snd y) \<Longrightarrow>\<^sub>t hn_ctxt Bm (snd x) (snd y)"
  shows "hn_ctxt (prod_assn A B) x y \<or>\<^sub>A hn_ctxt (prod_assn A' B') x y \<Longrightarrow>\<^sub>t hn_ctxt (prod_assn Am Bm) x y"
  by (blast intro: entt_disjE prod_frame_match 
    entt_disjD1[OF assms(1)] entt_disjD2[OF assms(1)]
    entt_disjD1[OF assms(2)] entt_disjD2[OF assms(2)])
  
lemma entt_invalid_prod: "hn_invalid (prod_assn A B) p p' \<Longrightarrow>\<^sub>t hn_ctxt (prod_assn (invalid_assn A) (invalid_assn B)) p p'"
    apply (simp add: hn_ctxt_def invalid_assn_def[abs_def])
    apply (rule enttI)
    apply clarsimp
    apply (cases p; cases p'; auto simp: mod_star_conv pure_def) 
    done

lemmas invalid_prod_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_prod]

lemma prod_assn_ctxt: "prod_assn A1 A2 x y = z \<Longrightarrow> hn_ctxt (prod_assn A1 A2) x y = z"
  by (simp add: hn_ctxt_def)

lemma hn_case_prod'[sepref_prep_comb_rule,sepref_comb_rules]:
  assumes FR: "\<Gamma>\<Longrightarrow>\<^sub>thn_ctxt (prod_assn P1 P2) p' p * \<Gamma>1"
  assumes Pair: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 * hn_ctxt P2 a2' a2 * \<Gamma>1 * hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (hn_ctxt P1' a1' a1 * hn_ctxt P2' a2' a2 * hn_ctxt XX1 p' p * \<Gamma>1') R (f' a1' a2')"
  shows "hn_refine \<Gamma> (case_prod f p) (hn_ctxt (prod_assn P1' P2') p' p * \<Gamma>1')
    R (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')" (is "?G \<Gamma>")
    apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply1 (cases p; cases p'; simp add: prod_assn_pair_conv[THEN prod_assn_ctxt])
    apply (rule hn_refine_cons[OF _ Pair _ entt_refl])
    applyS (simp add: hn_ctxt_def)
    applyS simp
    applyS (simp add: hn_ctxt_def entt_fr_refl entt_fr_drop)
    done

lemma hn_case_prod_old:
  assumes P: "\<Gamma>\<Longrightarrow>\<^sub>t\<Gamma>1 * hn_ctxt (prod_assn P1 P2) p' p"
  assumes R: "\<And>a1 a2 a1' a2'. \<lbrakk>p'=(a1',a2')\<rbrakk> 
    \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt P1 a1' a1 * hn_ctxt P2 a2' a2 * hn_invalid (prod_assn P1 P2) p' p) (f a1 a2) 
          (\<Gamma>h a1 a1' a2 a2') R (f' a1' a2')"
  assumes M: "\<And>a1 a1' a2 a2'. \<Gamma>h a1 a1' a2 a2' 
    \<Longrightarrow>\<^sub>t \<Gamma>' * hn_ctxt P1' a1' a1 * hn_ctxt P2' a2' a2 * hn_ctxt Pxx p' p"
  shows "hn_refine \<Gamma> (case_prod f p) (\<Gamma>' * hn_ctxt (prod_assn P1' P2') p' p)
    R (case_prod$(\<lambda>\<^sub>2a b. f' a b)$p')"
  apply1 (cases p; cases p'; simp)  
  apply1 (rule hn_refine_cons_pre[OF P])
  apply (rule hn_refine_preI)
  apply (simp add: hn_ctxt_def assn_aci)
  apply (rule hn_refine_cons[OF _ R])
  apply1 (rule enttI)
  applyS (sep_auto simp add: hn_ctxt_def invalid_assn_def mod_star_conv)

  applyS simp
  apply1 (rule entt_trans[OF M])
  applyS (sep_auto intro!: enttI simp: hn_ctxt_def)

  applyS simp
  done

lemma hn_Pair[sepref_fr_rules]: "hn_refine 
  (hn_ctxt P1 x1 x1' * hn_ctxt P2 x2 x2')
  (return (x1',x2'))
  (hn_invalid P1 x1 x1' * hn_invalid P2 x2 x2')
  (prod_assn P1 P2)
  (RETURN$(Pair$x1$x2))"
  unfolding hn_refine_def
  apply (sep_auto simp: hn_ctxt_def prod_assn_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P1]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P2]], frame_inference)
  apply sep_auto
  done

lemma fst_hnr[sepref_fr_rules]: "(return o fst,RETURN o fst) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a A"
  by sepref_to_hoare sep_auto
lemma snd_hnr[sepref_fr_rules]: "(return o snd,RETURN o snd) \<in> (prod_assn A B)\<^sup>d \<rightarrow>\<^sub>a B"
  by sepref_to_hoare sep_auto


lemmas [constraint_simps] = prod_assn_pure_conv
lemmas [sepref_import_param] = param_prod_swap

lemma rdomp_prodD[dest!]: "rdomp (prod_assn A B) (a,b) \<Longrightarrow> rdomp A a \<and> rdomp B b"
  unfolding rdomp_def prod_assn_def
  by (sep_auto simp: mod_star_conv)


subsection "Option"
fun option_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a option \<Rightarrow> 'c option \<Rightarrow> assn" where
  "option_assn P None None = emp"
| "option_assn P (Some a) (Some c) = P a c"
| "option_assn _ _ _ = false"

lemma option_assn_simps[simp]:
  "option_assn P None v' = \<up>(v'=None)"
  "option_assn P v None = \<up>(v=None)"
  apply (cases v', simp_all)
  apply (cases v, simp_all)
  done

lemma option_assn_alt_def: "option_assn R a b = 
  (case (a,b) of (Some x, Some y) \<Rightarrow> R x y
  | (None,None) \<Rightarrow> emp
  | _ \<Rightarrow> false)"
  by (auto split: option.split)


lemma option_assn_pure_conv[constraint_simps]: "option_assn (pure R) = pure (\<langle>R\<rangle>option_rel)"
  apply (intro ext)      
  apply (rename_tac a c)
  apply (case_tac "(pure R,a,c)" rule: option_assn.cases)  
  by (auto simp: pure_def)
                                                
lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] = option_assn_pure_conv[symmetric]

lemma hr_comp_option_conv[simp, fcomp_norm_unfold]: "
  hr_comp (option_assn R) (\<langle>R'\<rangle>option_rel) 
  = option_assn (hr_comp R R')"
  unfolding hr_comp_def[abs_def]
  apply (intro ext ent_iffI)
  apply solve_entails
  apply (case_tac "(R,b,c)" rule: option_assn.cases)
  apply clarsimp_all
  
  apply (sep_auto simp: option_assn_alt_def split: option.splits)
  apply (clarsimp simp: option_assn_alt_def split: option.splits; safe)
  apply (sep_auto split: option.splits)
  apply (intro ent_ex_preI) 
  apply (rule ent_ex_postI)
  apply (sep_auto split: option.splits)
  done
      

lemma option_assn_precise[safe_constraint_rules]: 
  assumes "precise P"  
  shows "precise (option_assn P)"
proof
  fix a a' p h F F'
  assume A: "h \<Turnstile> option_assn P a p * F \<and>\<^sub>A option_assn P a' p * F'"
  thus "a=a'" proof (cases "(P,a,p)" rule: option_assn.cases)
    case (2 _ av pv) hence [simp]: "a=Some av" "p=Some pv" by simp_all

    from A obtain av' where [simp]: "a'=Some av'" by (cases a', simp_all)

    from A have "h \<Turnstile> P av pv * F \<and>\<^sub>A P av' pv * F'" by simp
    with \<open>precise P\<close> have "av=av'" by (rule preciseD)
    thus ?thesis by simp
  qed simp_all
qed

lemma pure_option[safe_constraint_rules]: 
  assumes P: "is_pure P"
  shows "is_pure (option_assn P)"
proof -
  from P obtain P' where P': "\<And>x x'. P x x' = \<up>(P' x x')"
    using is_pureE by blast

  show ?thesis proof
    fix x x'
    show "option_assn P x x' =
         \<up> (case (x, x') of 
             (None,None) \<Rightarrow> True | (Some v, Some v') \<Rightarrow> P' v v' | _ \<Rightarrow> False
           )"
      apply (simp add: P' split: prod.split option.split)
      done
  qed
qed

lemma hn_ctxt_option: "option_assn A x y = z \<Longrightarrow> hn_ctxt (option_assn A) x y = z"
  by (simp add: hn_ctxt_def)

lemma hn_case_option[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (option_assn P) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (option_assn P) p p' * F"
  assumes Rn: "p=None \<Longrightarrow> hn_refine (hn_ctxt (option_assn P) p p' * F) f1' (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
  assumes Rs: "\<And>x x'. \<lbrakk> p=Some x; p'=Some x' \<rbrakk> \<Longrightarrow> 
    hn_refine (hn_ctxt P x x' * INVE * F) (f2' x') (hn_ctxt P' x x' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 x)"
  assumes MERGE1: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"  
  shows "hn_refine \<Gamma> (case_option f1' f2' p') (hn_ctxt (option_assn P') p p' * \<Gamma>') R (case_option$f1$(\<lambda>\<^sub>2x. f2 x)$p)"
    apply (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply (cases p; cases p'; simp add: option_assn.simps[THEN hn_ctxt_option])
    subgoal 
      apply (rule hn_refine_cons[OF _ Rn _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)

      apply (subst mult.commute, rule entt_fr_drop)
      apply (rule entt_trans[OF _ MERGE1])
      apply (simp add: ent_disjI1' ent_disjI2')
    done  

    subgoal
      apply (rule hn_refine_cons[OF _ Rs _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      applyS (simp add: hn_ctxt_def)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def)
    done
    done

lemma hn_None[sepref_fr_rules]:
  "hn_refine emp (return None) emp (option_assn P) (RETURN$None)"
  by rule sep_auto

lemma hn_Some[sepref_fr_rules]: "hn_refine 
  (hn_ctxt P v v')
  (return (Some v'))
  (hn_invalid P v v')
  (option_assn P)
  (RETURN$(Some$v))"
  by rule (sep_auto simp: hn_ctxt_def invalidate_clone')

definition "imp_option_eq eq a b \<equiv> case (a,b) of 
  (None,None) \<Rightarrow> return True
| (Some a, Some b) \<Rightarrow> eq a b
| _ \<Rightarrow> return False"

(* TODO: This is some kind of generic algorithm! Use GEN_ALGO here, and 
  let GEN_ALGO re-use the registered operator rules *)
lemma option_assn_eq[sepref_comb_rules]:
  fixes a b :: "'a option"
  assumes F1: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (option_assn P) a a' * hn_ctxt (option_assn P) b b' * \<Gamma>1"
  assumes EQ: "\<And>va va' vb vb'. hn_refine 
    (hn_ctxt P va va' * hn_ctxt P vb vb' * \<Gamma>1)
    (eq' va' vb') 
    (\<Gamma>' va va' vb vb') 
    bool_assn
    (RETURN$((=) $va$vb))"
  assumes F2: 
    "\<And>va va' vb vb'. 
      \<Gamma>' va va' vb vb' \<Longrightarrow>\<^sub>t hn_ctxt P va va' * hn_ctxt P vb vb' * \<Gamma>1"
  shows "hn_refine 
    \<Gamma> 
    (imp_option_eq eq' a' b') 
    (hn_ctxt (option_assn P) a a' * hn_ctxt (option_assn P) b b' * \<Gamma>1)
    bool_assn 
    (RETURN$((=) $a$b))"
  apply (rule hn_refine_cons_pre[OF F1])
  unfolding imp_option_eq_def
  apply rule
  apply (simp split: option.split add: hn_ctxt_def, intro impI conjI)

  apply (sep_auto split: option.split simp: hn_ctxt_def pure_def)
  apply (cases a, (sep_auto split: option.split simp: hn_ctxt_def pure_def)+)[]
  apply (cases a, (sep_auto split: option.split simp: hn_ctxt_def pure_def)+)[]
  apply (cases b, (sep_auto split: option.split simp: hn_ctxt_def pure_def)+)[]
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF EQ[unfolded hn_ctxt_def]])
  apply simp
  apply (rule ent_frame_fwd[OF F2[THEN enttD,unfolded hn_ctxt_def]])
  apply (fr_rot 2)
  apply (fr_rot_rhs 1)
  apply (rule fr_refl)
  apply (rule ent_refl)
  apply (sep_auto simp: pure_def)
  done

lemma [pat_rules]: 
  "(=) $a$None \<equiv> is_None$a"
  "(=) $None$a \<equiv> is_None$a"
  apply (rule eq_reflection, simp split: option.split)+
  done

lemma hn_is_None[sepref_fr_rules]: "hn_refine 
  (hn_ctxt (option_assn P) a a')
  (return (is_None a'))
  (hn_ctxt (option_assn P) a a')
  bool_assn
  (RETURN$(is_None$a))"
  apply rule
  apply (sep_auto split: option.split simp: hn_ctxt_def pure_def)
  done

lemma (in -) sepref_the_complete[sepref_fr_rules]:
  assumes "x\<noteq>None"
  shows "hn_refine 
    (hn_ctxt (option_assn R) x xi) 
    (return (the xi)) 
    (hn_invalid (option_assn R) x xi)
    (R)
    (RETURN$(the$x))"
    using assms
    apply (cases x)
    apply simp
    apply (cases xi)
    apply (simp add: hn_ctxt_def)
    apply rule
    apply (sep_auto simp: hn_ctxt_def invalidate_clone' vassn_tagI invalid_assn_const)
    done

(* As the sepref_the_complete rule does not work for us 
  --- the assertion ensuring the side-condition gets decoupled from its variable by a copy-operation ---
  we use the following rule that only works for the identity relation *)
lemma (in -) sepref_the_id:
  assumes "CONSTRAINT (IS_PURE IS_ID) R"
  shows "hn_refine 
    (hn_ctxt (option_assn R) x xi) 
    (return (the xi)) 
    (hn_ctxt (option_assn R) x xi)
    (R)
    (RETURN$(the$x))"
    using assms 
    apply (clarsimp simp: IS_PURE_def IS_ID_def hn_ctxt_def is_pure_conv)
    apply (cases x)
    apply simp
    apply (cases xi)
    apply (simp add: hn_ctxt_def invalid_assn_def)
    apply rule apply (sep_auto simp: pure_def)
    apply rule apply (sep_auto)
    apply (simp add: option_assn_pure_conv)
    apply rule apply (sep_auto simp: pure_def invalid_assn_def)
    done


subsection "Lists"

fun list_assn :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a list \<Rightarrow> 'c list \<Rightarrow> assn" where
  "list_assn P [] [] = emp"
| "list_assn P (a#as) (c#cs) = P a c * list_assn P as cs"
| "list_assn _ _ _ = false"

lemma list_assn_aux_simps[simp]:
  "list_assn P [] l' = (\<up>(l'=[]))"
  "list_assn P l [] = (\<up>(l=[]))"
  unfolding hn_ctxt_def
  apply (cases l')
  apply simp
  apply simp
  apply (cases l)
  apply simp
  apply simp
  done

lemma list_assn_aux_append[simp]:
  "length l1=length l1' \<Longrightarrow> 
    list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (induct rule: list_induct2)
  apply simp
  apply (simp add: star_assoc)
  done

lemma list_assn_aux_ineq_len: "length l \<noteq> length li \<Longrightarrow> list_assn A l li = false"
proof (induction l arbitrary: li)
  case (Cons x l li) thus ?case by (cases li; auto)
qed simp

lemma list_assn_aux_append2[simp]:
  assumes "length l2=length l2'"  
  shows "list_assn P (l1@l2) (l1'@l2') 
    = list_assn P l1 l1' * list_assn P l2 l2'"
  apply (cases "length l1 = length l1'")
  apply (erule list_assn_aux_append)
  apply (simp add: list_assn_aux_ineq_len assms)
  done

lemma list_assn_pure_conv[constraint_simps]: "list_assn (pure R) = pure (\<langle>R\<rangle>list_rel)"
proof (intro ext)
  fix l li
  show "list_assn (pure R) l li = pure (\<langle>R\<rangle>list_rel) l li"
    apply (induction "pure R" l li rule: list_assn.induct)
    by (auto simp: pure_def)
qed

lemmas [sepref_import_rewrite, sepref_frame_normrel_eqs, fcomp_norm_unfold] = list_assn_pure_conv[symmetric]


lemma list_assn_simps[simp]:
  "hn_ctxt (list_assn P) [] l' = (\<up>(l'=[]))"
  "hn_ctxt (list_assn P) l [] = (\<up>(l=[]))"
  "hn_ctxt (list_assn P) [] [] = emp"
  "hn_ctxt (list_assn P) (a#as) (c#cs) = hn_ctxt P a c * hn_ctxt (list_assn P) as cs"
  "hn_ctxt (list_assn P) (a#as) [] = false"
  "hn_ctxt (list_assn P) [] (c#cs) = false"
  unfolding hn_ctxt_def
  apply (cases l')
  apply simp
  apply simp
  apply (cases l)
  apply simp
  apply simp
  apply simp_all
  done

lemma list_assn_precise[constraint_rules]: "precise P \<Longrightarrow> precise (list_assn P)"
proof
  fix l1 l2 l h F1 F2
  assume P: "precise P"
  assume "h\<Turnstile>list_assn P l1 l * F1 \<and>\<^sub>A list_assn P l2 l * F2"
  thus "l1=l2"
  proof (induct l arbitrary: l1 l2 F1 F2)
    case Nil thus ?case by simp
  next
    case (Cons a ls)
    from Cons obtain a1 ls1 where [simp]: "l1=a1#ls1"
      by (cases l1, simp)
    from Cons obtain a2 ls2 where [simp]: "l2=a2#ls2"
      by (cases l2, simp)
    
    from Cons.prems have M:
      "h \<Turnstile> P a1 a * list_assn P ls1 ls * F1 
        \<and>\<^sub>A P a2 a * list_assn P ls2 ls * F2" by simp
    have "a1=a2"
      apply (rule preciseD[OF P, where a=a1 and a'=a2 and p=a
        and F= "list_assn P ls1 ls * F1" 
        and F'="list_assn P ls2 ls * F2"
        ])
      using M
      by (simp add: star_assoc)
    
    moreover have "ls1=ls2"
      apply (rule Cons.hyps[where ?F1.0="P a1 a * F1" and ?F2.0="P a2 a * F2"])
      using M
      by (simp only: star_aci)
    ultimately show ?case by simp
  qed
qed
lemma list_assn_pure[constraint_rules]: 
  assumes P: "is_pure P" 
  shows "is_pure (list_assn P)"
proof -
  from P obtain P' where P_eq: "\<And>x x'. P x x' = \<up>(P' x x')" 
    by (rule is_pureE) blast

  {
    fix l l'
    have "list_assn P l l' = \<up>(list_all2 P' l l')"
      by (induct P\<equiv>P l l' rule: list_assn.induct)
         (simp_all add: P_eq)
  } thus ?thesis by rule
qed

lemma list_assn_mono: 
  "\<lbrakk>\<And>x x'. P x x'\<Longrightarrow>\<^sub>AP' x x'\<rbrakk> \<Longrightarrow> list_assn P l l' \<Longrightarrow>\<^sub>A list_assn P' l l'"
  unfolding hn_ctxt_def
  apply (induct P l l' rule: list_assn.induct)
  by (auto intro: ent_star_mono)

lemma list_assn_monot: 
  "\<lbrakk>\<And>x x'. P x x'\<Longrightarrow>\<^sub>tP' x x'\<rbrakk> \<Longrightarrow> list_assn P l l' \<Longrightarrow>\<^sub>t list_assn P' l l'"
  unfolding hn_ctxt_def
  apply (induct P l l' rule: list_assn.induct)
  by (auto intro: entt_star_mono)

lemma list_match_cong[sepref_frame_match_rules]: 
  "\<lbrakk>\<And>x x'. \<lbrakk>x\<in>set l; x'\<in>set l'\<rbrakk> \<Longrightarrow> hn_ctxt A x x' \<Longrightarrow>\<^sub>t hn_ctxt A' x x' \<rbrakk> \<Longrightarrow> hn_ctxt (list_assn A) l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn A') l l'"
  unfolding hn_ctxt_def
  by (induct A l l' rule: list_assn.induct) (simp_all add: entt_star_mono)

lemma list_merge_cong[sepref_frame_merge_rules]:
  assumes "\<And>x x'. \<lbrakk>x\<in>set l; x'\<in>set l'\<rbrakk> \<Longrightarrow> hn_ctxt A x x' \<or>\<^sub>A hn_ctxt A' x x' \<Longrightarrow>\<^sub>t hn_ctxt Am x x'"
  shows "hn_ctxt (list_assn A) l l' \<or>\<^sub>A hn_ctxt (list_assn A') l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn Am) l l'"
  apply (blast intro: entt_disjE list_match_cong entt_disjD1[OF assms] entt_disjD2[OF assms])
  done
  
lemma invalid_list_split: 
  "invalid_assn (list_assn A) (x#xs) (y#ys) \<Longrightarrow>\<^sub>t invalid_assn A x y * invalid_assn (list_assn A) xs ys"
  by (fastforce simp: invalid_assn_def intro!: enttI simp: mod_star_conv)

lemma entt_invalid_list: "hn_invalid (list_assn A) l l' \<Longrightarrow>\<^sub>t hn_ctxt (list_assn (invalid_assn A)) l l'"
  apply (induct A l l' rule: list_assn.induct)
  applyS simp

  subgoal
    apply1 (simp add: hn_ctxt_def cong del: invalid_assn_cong)
    apply1 (rule entt_trans[OF invalid_list_split])
    apply (rule entt_star_mono)
      applyS simp

      apply (rule entt_trans)
        applyS assumption
        applyS simp
    done
    
  applyS (simp add: hn_ctxt_def invalid_assn_def) 
  applyS (simp add: hn_ctxt_def invalid_assn_def) 
  done

lemmas invalid_list_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_list]


lemma list_assn_comp[fcomp_norm_unfold]: "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) = list_assn (hr_comp A B)"
proof (intro ext)  
  { fix x l y m
    have "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) (x # l) (y # m) = 
      hr_comp A B x y * hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) l m"
      by (sep_auto 
        simp: hr_comp_def list_rel_split_left_iff
        intro!: ent_ex_preI ent_iffI) (* TODO: ent_ex_preI should be applied by default, before ent_ex_postI!*)
  } note aux = this

  fix l li
  show "hr_comp (list_assn A) (\<langle>B\<rangle>list_rel) l li = list_assn (hr_comp A B) l li"
    apply (induction l arbitrary: li; case_tac li; intro ent_iffI)
    apply (sep_auto simp: hr_comp_def; fail)+
    by (simp_all add: aux)
qed  

lemma hn_ctxt_eq: "A x y = z \<Longrightarrow> hn_ctxt A x y = z" by (simp add: hn_ctxt_def)

lemmas hn_ctxt_list = hn_ctxt_eq[of "list_assn A" for A]

lemma hn_case_list[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (list_assn P) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (list_assn P) p p' * F"
  assumes Rn: "p=[] \<Longrightarrow> hn_refine (hn_ctxt (list_assn P) p p' * F) f1' (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
  assumes Rs: "\<And>x l x' l'. \<lbrakk> p=x#l; p'=x'#l' \<rbrakk> \<Longrightarrow> 
    hn_refine (hn_ctxt P x x' * hn_ctxt (list_assn P) l l' * INVE * F) (f2' x' l') (hn_ctxt P1' x x' * hn_ctxt (list_assn P2') l l' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 x l)"
  assumes MERGE1[unfolded hn_ctxt_def]: "\<And>x x'. hn_ctxt P1' x x' \<or>\<^sub>A hn_ctxt P2' x x' \<Longrightarrow>\<^sub>t hn_ctxt P' x x'"  
  assumes MERGE2: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"  
  shows "hn_refine \<Gamma> (case_list f1' f2' p') (hn_ctxt (list_assn P') p p' * \<Gamma>') R (case_list$f1$(\<lambda>\<^sub>2x l. f2 x l)$p)"
    apply (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply (cases p; cases p'; simp add: list_assn.simps[THEN hn_ctxt_list])
    subgoal 
      apply (rule hn_refine_cons[OF _ Rn _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)

      apply (subst mult.commute, rule entt_fr_drop)
      apply (rule entt_trans[OF _ MERGE2])
      apply (simp add: ent_disjI1' ent_disjI2')
    done  

    subgoal
      apply (rule hn_refine_cons[OF _ Rs _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (simp add: hn_ctxt_def)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp)

      apply1 (simp add: hn_ctxt_def)
      apply (rule list_assn_monot)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp)

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp)
    done
    done

lemma hn_Nil[sepref_fr_rules]: 
  "hn_refine emp (return []) emp (list_assn P) (RETURN$[])"
  unfolding hn_refine_def
  by sep_auto

lemma hn_Cons[sepref_fr_rules]: "hn_refine (hn_ctxt P x x' * hn_ctxt (list_assn P) xs xs') 
  (return (x'#xs')) (hn_invalid P x x' * hn_invalid (list_assn P) xs xs') (list_assn P)
  (RETURN$((#) $x$xs))"
  unfolding hn_refine_def
  apply (sep_auto simp: hn_ctxt_def)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of P]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply solve_entails
  done

lemma list_assn_aux_len: 
  "list_assn P l l' = list_assn P l l' * \<up>(length l = length l')"
  apply (induct P\<equiv>P l l' rule: list_assn.induct)
  apply simp_all
  subgoal for a as c cs
    by (erule_tac t="list_assn P as cs" in subst[OF sym]) simp
  done

lemma list_assn_aux_eqlen_simp: 
  "vassn_tag (list_assn P l l') \<Longrightarrow> length l' = length l"
  "h \<Turnstile> (list_assn P l l') \<Longrightarrow> length l' = length l"
  apply (subst (asm) list_assn_aux_len; auto simp: vassn_tag_def)+
  done

lemma hn_append[sepref_fr_rules]: "hn_refine (hn_ctxt (list_assn P) l1 l1' * hn_ctxt (list_assn P) l2 l2')
  (return (l1'@l2')) (hn_invalid (list_assn P) l1 l1' * hn_invalid (list_assn P) l2 l2') (list_assn P)
  (RETURN$((@) $l1$l2))"
  apply rule
  apply (sep_auto simp: hn_ctxt_def)
  apply (subst list_assn_aux_len)
  apply (sep_auto)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply (rule ent_frame_fwd[OF invalidate_clone'[of "list_assn P"]], frame_inference)
  apply solve_entails
  done

lemma list_assn_aux_cons_conv1:
  "list_assn R (a#l) m = (\<exists>\<^sub>Ab m'. R a b * list_assn R l m' * \<up>(m=b#m'))"
  apply (cases m)
  apply sep_auto
  apply (sep_auto intro!: ent_iffI)
  done
lemma list_assn_aux_cons_conv2:
  "list_assn R l (b#m) = (\<exists>\<^sub>Aa l'. R a b * list_assn R l' m * \<up>(l=a#l'))"
  apply (cases l)
  apply sep_auto
  apply (sep_auto intro!: ent_iffI)
  done
lemmas list_assn_aux_cons_conv = list_assn_aux_cons_conv1 list_assn_aux_cons_conv2

lemma list_assn_aux_append_conv1:
  "list_assn R (l1@l2) m = (\<exists>\<^sub>Am1 m2. list_assn R l1 m1 * list_assn R l2 m2 * \<up>(m=m1@m2))"
  apply (induction l1 arbitrary: m)
  apply (sep_auto intro!: ent_iffI)
  apply (sep_auto intro!: ent_iffI simp: list_assn_aux_cons_conv)
  done
lemma list_assn_aux_append_conv2:
  "list_assn R l (m1@m2) = (\<exists>\<^sub>Al1 l2. list_assn R l1 m1 * list_assn R l2 m2 * \<up>(l=l1@l2))"
  apply (induction m1 arbitrary: l)
  apply (sep_auto intro!: ent_iffI)
  apply (sep_auto intro!: ent_iffI simp: list_assn_aux_cons_conv)
  done
lemmas list_assn_aux_append_conv = list_assn_aux_append_conv1 list_assn_aux_append_conv2  

declare param_upt[sepref_import_param]
  
  
subsection \<open>Sum-Type\<close>    

fun sum_assn :: "('ai \<Rightarrow> 'a \<Rightarrow> assn) \<Rightarrow> ('bi \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> ('ai+'bi) \<Rightarrow> ('a+'b) \<Rightarrow> assn" where
  "sum_assn A B (Inl ai) (Inl a) = A ai a"
| "sum_assn A B (Inr bi) (Inr b) = B bi b"
| "sum_assn A B _ _ = false"  

notation sum_assn (infixr "+\<^sub>a" 67)
  
lemma sum_assn_pure[safe_constraint_rules]: "\<lbrakk>is_pure A; is_pure B\<rbrakk> \<Longrightarrow> is_pure (sum_assn A B)"
  apply (auto simp: is_pure_iff_pure_assn)
  apply (rename_tac x x')
  apply (case_tac x; case_tac x'; simp add: pure_def)
  done
  
lemma sum_assn_id[simp]: "sum_assn id_assn id_assn = id_assn"
  apply (intro ext)
  subgoal for x y by (cases x; cases y; simp add: pure_def)
  done

lemma sum_assn_pure_conv[simp]: "sum_assn (pure A) (pure B) = pure (\<langle>A,B\<rangle>sum_rel)"
  apply (intro ext)
  subgoal for a b by (cases a; cases b; auto simp: pure_def)
  done
    
    
lemma sum_match_cong[sepref_frame_match_rules]: 
  "\<lbrakk>
    \<And>x y. \<lbrakk>e = Inl x; e'=Inl y\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y;
    \<And>x y. \<lbrakk>e = Inr x; e'=Inr y\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<Longrightarrow>\<^sub>t hn_ctxt B' x y
  \<rbrakk> \<Longrightarrow> hn_ctxt (sum_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn A' B') e e'"
  by (cases e; cases e'; simp add: hn_ctxt_def entt_star_mono)

lemma enum_merge_cong[sepref_frame_merge_rules]:
  assumes "\<And>x y. \<lbrakk>e=Inl x; e'=Inl y\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
  assumes "\<And>x y. \<lbrakk>e=Inr x; e'=Inr y\<rbrakk> \<Longrightarrow> hn_ctxt B x y \<or>\<^sub>A hn_ctxt B' x y \<Longrightarrow>\<^sub>t hn_ctxt Bm x y"
  shows "hn_ctxt (sum_assn A B) e e' \<or>\<^sub>A hn_ctxt (sum_assn A' B') e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn Am Bm) e e'"
  apply (rule entt_disjE)
  apply (rule sum_match_cong)
  apply (rule entt_disjD1[OF assms(1)]; simp)
  apply (rule entt_disjD1[OF assms(2)]; simp)

  apply (rule sum_match_cong)
  apply (rule entt_disjD2[OF assms(1)]; simp)
  apply (rule entt_disjD2[OF assms(2)]; simp)
  done

lemma entt_invalid_sum: "hn_invalid (sum_assn A B) e e' \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn (invalid_assn A) (invalid_assn B)) e e'"
  apply (simp add: hn_ctxt_def invalid_assn_def[abs_def])
  apply (rule enttI)
  apply clarsimp
  apply (cases e; cases e'; auto simp: mod_star_conv pure_def) 
  done

lemmas invalid_sum_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_sum]

sepref_register Inr Inl  

lemma [sepref_fr_rules]: "(return o Inl,RETURN o Inl) \<in> A\<^sup>d \<rightarrow>\<^sub>a sum_assn A B"
  by sepref_to_hoare sep_auto
lemma [sepref_fr_rules]: "(return o Inr,RETURN o Inr) \<in> B\<^sup>d \<rightarrow>\<^sub>a sum_assn A B"
  by sepref_to_hoare sep_auto

sepref_register case_sum

text \<open>In the monadify phase, this eta-expands to make visible all required arguments\<close>
lemma [sepref_monadify_arity]: "case_sum \<equiv> \<lambda>\<^sub>2f1 f2 x. SP case_sum$(\<lambda>\<^sub>2x. f1$x)$(\<lambda>\<^sub>2x. f2$x)$x"
  by simp

text \<open>This determines an evaluation order for the first-order operands\<close>  
lemma [sepref_monadify_comb]: "case_sum$f1$f2$x \<equiv> (\<bind>) $(EVAL$x)$(\<lambda>\<^sub>2x. SP case_sum$f1$f2$x)" by simp

text \<open>This enables translation of the case-distinction in a non-monadic context.\<close>  
lemma [sepref_monadify_comb]: "EVAL$(case_sum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$x) 
  \<equiv> (\<bind>) $(EVAL$x)$(\<lambda>\<^sub>2x. SP case_sum$(\<lambda>\<^sub>2x. EVAL $ f1 x)$(\<lambda>\<^sub>2x. EVAL $ f2 x)$x)"
  apply (rule eq_reflection)
  by (simp split: sum.splits)

text \<open>Auxiliary lemma, to lift simp-rule over \<open>hn_ctxt\<close>\<close>  
lemma sum_assn_ctxt: "sum_assn A B x y = z \<Longrightarrow> hn_ctxt (sum_assn A B) x y = z"
  by (simp add: hn_ctxt_def)

text \<open>The cases lemma first extracts the refinement for the datatype from the precondition.
  Next, it generate proof obligations to refine the functions for every case. 
  Finally the postconditions of the refinement are merged. 

  Note that we handle the
  destructed values separately, to allow reconstruction of the original datatype after the case-expression.

  Moreover, we provide (invalidated) versions of the original compound value to the cases,
  which allows access to pure compound values from inside the case.
  \<close>  
lemma sum_cases_hnr:
  fixes A B e e'
  defines [simp]: "INVe \<equiv> hn_invalid (sum_assn A B) e e'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (sum_assn A B) e e' * F"
  assumes E1: "\<And>x1 x1a. \<lbrakk>e = Inl x1; e' = Inl x1a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x1 x1a * INVe * F) (f1' x1a) (hn_ctxt A' x1 x1a * hn_ctxt XX1 e e' * \<Gamma>1') R (f1 x1)"
  assumes E2: "\<And>x2 x2a. \<lbrakk>e = Inr x2; e' = Inr x2a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt B x2 x2a * INVe * F) (f2' x2a) (hn_ctxt B' x2 x2a * hn_ctxt XX2 e e' * \<Gamma>2') R (f2 x2)"
  assumes MERGE[unfolded hn_ctxt_def]: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (case_sum f1' f2' e') (hn_ctxt (sum_assn A' B') e e' * \<Gamma>') R (case_sum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$e)"
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (cases e; cases e'; simp add: sum_assn.simps[THEN sum_assn_ctxt])
  subgoal
    apply (rule hn_refine_cons[OF _ E1 _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def) \<comment> \<open>Match precondition for case, get \<open>enum_assn\<close> from assumption generated by \<open>extract_hnr_invalids\<close>\<close>
    apply (rule entt_star_mono) \<comment> \<open>Split postcondition into pairs for compounds and frame, drop \<open>hn_ctxt XX\<close>\<close>
    apply1 (rule entt_fr_drop)
    applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
    apply1 (rule entt_trans[OF _ MERGE])
    applyS (simp add: entt_disjI1' entt_disjI2')
  done
  subgoal 
    apply (rule hn_refine_cons[OF _ E2 _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def)
    apply (rule entt_star_mono)
    apply1 (rule entt_fr_drop)
    applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
    apply1 (rule entt_trans[OF _ MERGE])
    applyS (simp add: entt_disjI1' entt_disjI2')
  done    
done  

text \<open>After some more preprocessing (adding extra frame-rules for non-atomic postconditions, 
  and splitting the merge-terms into binary merges), this rule can be registered\<close>
lemmas [sepref_comb_rules] = sum_cases_hnr[sepref_prep_comb_rule]

sepref_register isl projl projr
lemma isl_hnr[sepref_fr_rules]: "(return o isl,RETURN o isl) \<in> (sum_assn A B)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done

lemma projl_hnr[sepref_fr_rules]: "(return o projl,RETURN o projl) \<in> [isl]\<^sub>a (sum_assn A B)\<^sup>d \<rightarrow> A"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done

lemma projr_hnr[sepref_fr_rules]: "(return o projr,RETURN o projr) \<in> [Not o isl]\<^sub>a (sum_assn A B)\<^sup>d \<rightarrow> B"
  apply sepref_to_hoare
  subgoal for a b by (cases a; cases b; sep_auto)
  done
  
subsection \<open>String Literals\<close>  

sepref_register "PR_CONST String.empty_literal"

lemma empty_literal_hnr [sepref_import_param]:
  "(String.empty_literal, PR_CONST String.empty_literal) \<in> Id"
  by simp

lemma empty_literal_pat [def_pat_rules]:
  "String.empty_literal \<equiv> UNPROTECT String.empty_literal"
  by simp

context
  fixes b0 b1 b2 b3 b4 b5 b6 :: bool
  and s :: String.literal
begin

sepref_register "PR_CONST (String.Literal b0 b1 b2 b3 b4 b5 b6 s)"

lemma Literal_hnr [sepref_import_param]:
  "(String.Literal b0 b1 b2 b3 b4 b5 b6 s,
    PR_CONST (String.Literal b0 b1 b2 b3 b4 b5 b6 s)) \<in> Id"
  by simp

end

lemma Literal_pat [def_pat_rules]:
  "String.Literal $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ s \<equiv>
    UNPROTECT (String.Literal $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ s)"
  by simp
  
end
