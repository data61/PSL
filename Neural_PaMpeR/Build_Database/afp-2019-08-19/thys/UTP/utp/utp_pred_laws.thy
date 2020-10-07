section \<open> Predicate Calculus Laws \<close>

theory utp_pred_laws
  imports utp_pred
begin
  
subsection \<open> Propositional Logic \<close>
  
text \<open> Showing that predicates form a Boolean Algebra (under the predicate operators as opposed to
  the lattice operators) gives us many useful laws. \<close>

interpretation boolean_algebra diff_upred not_upred conj_upred "(\<le>)" "(<)"
  disj_upred false_upred true_upred
  by (unfold_locales; pred_auto)

lemma taut_true [simp]: "`true`"
  by (pred_auto)

lemma taut_false [simp]: "`false` = False"
  by (pred_auto)

lemma taut_conj: "`A \<and> B` = (`A` \<and> `B`)"
  by (rel_auto)

lemma taut_conj_elim [elim!]:
  "\<lbrakk> `A \<and> B`; \<lbrakk> `A`; `B` \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (rel_auto)

lemma taut_refine_impl: "\<lbrakk> Q \<sqsubseteq> P; `P` \<rbrakk> \<Longrightarrow> `Q`"
  by (rel_auto)

lemma taut_shEx_elim: 
  "\<lbrakk> `(\<^bold>\<exists> x \<bullet> P x)`; \<And> x. \<Sigma> \<sharp> P x; \<And> x. `P x` \<Longrightarrow> Q  \<rbrakk> \<Longrightarrow> Q"
  by (rel_blast)

text \<open> Linking refinement and HOL implication \<close>

lemma refine_prop_intro:
  assumes "\<Sigma> \<sharp> P" "\<Sigma> \<sharp> Q" "`Q` \<Longrightarrow> `P`"
  shows "P \<sqsubseteq> Q"
  using assms
  by (pred_auto)

lemma taut_not: "\<Sigma> \<sharp> P \<Longrightarrow> (\<not> `P`) = `\<not> P`"
  by (rel_auto)

lemma taut_shAll_intro:
  "\<forall> x. `P x` \<Longrightarrow> `\<^bold>\<forall> x \<bullet> P x`"
  by (rel_auto)

lemma taut_shAll_intro_2:
  "\<forall> x y. `P x y` \<Longrightarrow> `\<^bold>\<forall> (x, y) \<bullet> P x y`"
  by (rel_auto)

lemma taut_impl_intro:
  "\<lbrakk> \<Sigma> \<sharp> P; `P` \<Longrightarrow> `Q` \<rbrakk> \<Longrightarrow> `P \<Rightarrow> Q`"
  by (rel_auto)

lemma upred_eval_taut:
  "`P\<lbrakk>\<guillemotleft>b\<guillemotright>/&\<^bold>v\<rbrakk>` = \<lbrakk>P\<rbrakk>\<^sub>eb"
  by (pred_auto)
    
lemma refBy_order: "P \<sqsubseteq> Q = `Q \<Rightarrow> P`"
  by (pred_auto)

lemma conj_idem [simp]: "((P::'\<alpha> upred) \<and> P) = P"
  by (pred_auto)

lemma disj_idem [simp]: "((P::'\<alpha> upred) \<or> P) = P"
  by (pred_auto)

lemma conj_comm: "((P::'\<alpha> upred) \<and> Q) = (Q \<and> P)"
  by (pred_auto)

lemma disj_comm: "((P::'\<alpha> upred) \<or> Q) = (Q \<or> P)"
  by (pred_auto)

lemma conj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<and> Q) = (R \<and> Q)"
  by (pred_auto)

lemma disj_subst: "P = R \<Longrightarrow> ((P::'\<alpha> upred) \<or> Q) = (R \<or> Q)"
  by (pred_auto)

lemma conj_assoc:"(((P::'\<alpha> upred) \<and> Q) \<and> S) = (P \<and> (Q \<and> S))"
  by (pred_auto)

lemma disj_assoc:"(((P::'\<alpha> upred) \<or> Q) \<or> S) = (P \<or> (Q \<or> S))"
  by (pred_auto)

lemma conj_disj_abs:"((P::'\<alpha> upred) \<and> (P \<or> Q)) = P"
  by (pred_auto)

lemma disj_conj_abs:"((P::'\<alpha> upred) \<or> (P \<and> Q)) = P"
  by (pred_auto)

lemma conj_disj_distr:"((P::'\<alpha> upred) \<and> (Q \<or> R)) = ((P \<and> Q) \<or> (P \<and> R))"
  by (pred_auto)

lemma disj_conj_distr:"((P::'\<alpha> upred) \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
  by (pred_auto)

lemma true_disj_zero [simp]:
  "(P \<or> true) = true" "(true \<or> P) = true"
  by (pred_auto)+

lemma true_conj_zero [simp]:
  "(P \<and> false) = false" "(false \<and> P) = false"
  by (pred_auto)+

lemma false_sup [simp]: "false \<sqinter> P = P" "P \<sqinter> false = P"
  by (pred_auto)+

lemma true_inf [simp]: "true \<squnion> P = P" "P \<squnion> true = P"
  by (pred_auto)+

lemma imp_vacuous [simp]: "(false \<Rightarrow> u) = true"
  by (pred_auto)

lemma imp_true [simp]: "(p \<Rightarrow> true) = true"
  by (pred_auto)

lemma true_imp [simp]: "(true \<Rightarrow> p) = p"
  by (pred_auto)

lemma impl_mp1 [simp]: "(P \<and> (P \<Rightarrow> Q)) = (P \<and> Q)"
  by (pred_auto)

lemma impl_mp2 [simp]: "((P \<Rightarrow> Q) \<and> P) = (Q \<and> P)"
  by (pred_auto)

lemma impl_adjoin: "((P \<Rightarrow> Q) \<and> R) = ((P \<and> R \<Rightarrow> Q \<and> R) \<and> R)"
  by (pred_auto)

lemma impl_refine_intro:
  "\<lbrakk> Q\<^sub>1 \<sqsubseteq> P\<^sub>1; P\<^sub>2 \<sqsubseteq> (P\<^sub>1 \<and> Q\<^sub>2) \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<Rightarrow> P\<^sub>2) \<sqsubseteq> (Q\<^sub>1 \<Rightarrow> Q\<^sub>2)"
  by (pred_auto)

lemma spec_refine:
  "Q \<sqsubseteq> (P \<and> R) \<Longrightarrow> (P \<Rightarrow> Q) \<sqsubseteq> R"
  by (rel_auto)
    
lemma impl_disjI: "\<lbrakk> `P \<Rightarrow> R`; `Q \<Rightarrow> R` \<rbrakk> \<Longrightarrow> `(P \<or> Q) \<Rightarrow> R`"
  by (rel_auto)

lemma conditional_iff:
  "(P \<Rightarrow> Q) = (P \<Rightarrow> R) \<longleftrightarrow> `P \<Rightarrow> (Q \<Leftrightarrow> R)`"
  by (pred_auto)

lemma p_and_not_p [simp]: "(P \<and> \<not> P) = false"
  by (pred_auto)

lemma p_or_not_p [simp]: "(P \<or> \<not> P) = true"
  by (pred_auto)

lemma p_imp_p [simp]: "(P \<Rightarrow> P) = true"
  by (pred_auto)

lemma p_iff_p [simp]: "(P \<Leftrightarrow> P) = true"
  by (pred_auto)

lemma p_imp_false [simp]: "(P \<Rightarrow> false) = (\<not> P)"
  by (pred_auto)

lemma not_conj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<and> Q)) = ((\<not> P) \<or> (\<not> Q))"
  by (pred_auto)

lemma not_disj_deMorgans [simp]: "(\<not> ((P::'\<alpha> upred) \<or> Q)) = ((\<not> P) \<and> (\<not> Q))"
  by (pred_auto)

lemma conj_disj_not_abs [simp]: "((P::'\<alpha> upred) \<and> ((\<not>P) \<or> Q)) = (P \<and> Q)"
  by (pred_auto)

lemma subsumption1:
  "`P \<Rightarrow> Q` \<Longrightarrow> (P \<or> Q) = Q"
  by (pred_auto)

lemma subsumption2:
  "`Q \<Rightarrow> P` \<Longrightarrow> (P \<or> Q) = P"
  by (pred_auto)

lemma neg_conj_cancel1: "(\<not> P \<and> (P \<or> Q)) = (\<not> P \<and> Q :: '\<alpha> upred)"
  by (pred_auto)

lemma neg_conj_cancel2: "(\<not> Q \<and> (P \<or> Q)) = (\<not> Q \<and> P :: '\<alpha> upred)"
  by (pred_auto)

lemma double_negation [simp]: "(\<not> \<not> (P::'\<alpha> upred)) = P"
  by (pred_auto)

lemma true_not_false [simp]: "true \<noteq> false" "false \<noteq> true"
  by (pred_auto)+

lemma closure_conj_distr: "([P]\<^sub>u \<and> [Q]\<^sub>u) = [P \<and> Q]\<^sub>u"
  by (pred_auto)

lemma closure_imp_distr: "`[P \<Rightarrow> Q]\<^sub>u \<Rightarrow> [P]\<^sub>u \<Rightarrow> [Q]\<^sub>u`"
  by (pred_auto)

lemma true_iff [simp]: "(P \<Leftrightarrow> true) = P"
  by (pred_auto)

lemma taut_iff_eq:
  "`P \<Leftrightarrow> Q` \<longleftrightarrow> (P = Q)"
  by (pred_auto)
    
lemma impl_alt_def: "(P \<Rightarrow> Q) = (\<not> P \<or> Q)"
  by (pred_auto)
    
subsection \<open> Lattice laws \<close>
    
lemma uinf_or:
  fixes P Q :: "'\<alpha> upred"
  shows "(P \<sqinter> Q) = (P \<or> Q)"
  by (pred_auto)

lemma usup_and:
  fixes P Q :: "'\<alpha> upred"
  shows "(P \<squnion> Q) = (P \<and> Q)"
  by (pred_auto)

lemma UINF_alt_def:
  "(\<Sqinter> i | A(i) \<bullet> P(i)) = (\<Sqinter> i \<bullet> A(i) \<and> P(i))"
  by (rel_auto)
    
lemma USUP_true [simp]: "(\<Squnion> P | F(P) \<bullet> true) = true"
  by (pred_auto)

lemma UINF_mem_UNIV [simp]: "(\<Sqinter> x\<in>UNIV \<bullet> P(x)) = (\<Sqinter> x \<bullet> P(x))"
  by (pred_auto)

lemma USUP_mem_UNIV [simp]: "(\<Squnion> x\<in>UNIV \<bullet> P(x)) = (\<Squnion> x \<bullet> P(x))"
  by (pred_auto)

lemma USUP_false [simp]: "(\<Squnion> i \<bullet> false) = false"
  by (pred_simp)

lemma USUP_mem_false [simp]: "I \<noteq> {} \<Longrightarrow> (\<Squnion> i\<in>I \<bullet> false) = false"
  by (rel_simp)

lemma USUP_where_false [simp]: "(\<Squnion> i | false \<bullet> P(i)) = true"
  by (rel_auto)

lemma UINF_true [simp]: "(\<Sqinter> i \<bullet> true) = true"
  by (pred_simp)

lemma UINF_ind_const [simp]: 
  "(\<Sqinter> i \<bullet> P) = P"
  by (rel_auto)
    
lemma UINF_mem_true [simp]: "A \<noteq> {} \<Longrightarrow> (\<Sqinter> i\<in>A \<bullet> true) = true"
  by (pred_auto)

lemma UINF_false [simp]: "(\<Sqinter> i | P(i) \<bullet> false) = false"
  by (pred_auto)

lemma UINF_where_false [simp]: "(\<Sqinter> i | false \<bullet> P(i)) = false"
  by (rel_auto)

lemma UINF_cong_eq:
  "\<lbrakk> \<And> x. P\<^sub>1(x) = P\<^sub>2(x); \<And> x. `P\<^sub>1(x) \<Rightarrow> Q\<^sub>1(x) =\<^sub>u Q\<^sub>2(x)` \<rbrakk> \<Longrightarrow>
        (\<Sqinter> x | P\<^sub>1(x) \<bullet> Q\<^sub>1(x)) = (\<Sqinter> x | P\<^sub>2(x) \<bullet> Q\<^sub>2(x))"
 by (unfold UINF_def, pred_simp, metis)

lemma UINF_as_Sup: "(\<Sqinter> P \<in> \<P> \<bullet> P) = \<Sqinter> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Sup"])
   apply (auto)
  done

lemma UINF_as_Sup_collect: "(\<Sqinter>P\<in>A \<bullet> f(P)) = (\<Sqinter>P\<in>A. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: Setcompr_eq_image)
  done

lemma UINF_as_Sup_collect': "(\<Sqinter>P \<bullet> f(P)) = (\<Sqinter>P. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: full_SetCompr_eq)
  done

lemma UINF_as_Sup_image: "(\<Sqinter> P | \<guillemotleft>P\<guillemotright> \<in>\<^sub>u \<guillemotleft>A\<guillemotright> \<bullet> f(P)) = \<Sqinter> (f ` A)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Sup"])
   apply (auto)
  done

lemma USUP_as_Inf: "(\<Squnion> P \<in> \<P> \<bullet> P) = \<Squnion> \<P>"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Inf"])
   apply (auto)
  done

lemma USUP_as_Inf_collect: "(\<Squnion>P\<in>A \<bullet> f(P)) = (\<Squnion>P\<in>A. f(P))"
  apply (pred_simp)
  apply (simp add: Setcompr_eq_image)
  done

lemma USUP_as_Inf_collect': "(\<Squnion>P \<bullet> f(P)) = (\<Squnion>P. f(P))"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Sup_uexpr_def)
  apply (pred_simp)
  apply (simp add: full_SetCompr_eq)
  done

lemma USUP_as_Inf_image: "(\<Squnion> P \<in> \<P> \<bullet> f(P)) = \<Squnion> (f ` \<P>)"
  apply (simp add: upred_defs bop.rep_eq lit.rep_eq Inf_uexpr_def)
  apply (pred_simp)
  apply (rule cong[of "Inf"])
   apply (auto)
  done

lemma USUP_image_eq [simp]: "USUP (\<lambda>i. \<guillemotleft>i\<guillemotright> \<in>\<^sub>u \<guillemotleft>f ` A\<guillemotright>) g = (\<Squnion> i\<in>A \<bullet> g(f(i)))"
  by (pred_simp, rule_tac cong[of Inf Inf], auto)

lemma UINF_image_eq [simp]: "UINF (\<lambda>i. \<guillemotleft>i\<guillemotright> \<in>\<^sub>u \<guillemotleft>f ` A\<guillemotright>) g = (\<Sqinter> i\<in>A \<bullet> g(f(i)))"
  by (pred_simp, rule_tac cong[of Sup Sup], auto)

lemma subst_continuous [usubst]: "\<sigma> \<dagger> (\<Sqinter> A) = (\<Sqinter> {\<sigma> \<dagger> P | P. P \<in> A})"
  by (simp add: UINF_as_Sup[THEN sym] usubst setcompr_eq_image)

lemma not_UINF: "(\<not> (\<Sqinter> i\<in>A\<bullet> P(i))) = (\<Squnion> i\<in>A\<bullet> \<not> P(i))"
  by (pred_auto)

lemma not_USUP: "(\<not> (\<Squnion> i\<in>A\<bullet> P(i))) = (\<Sqinter> i\<in>A\<bullet> \<not> P(i))"
  by (pred_auto)

lemma not_UINF_ind: "(\<not> (\<Sqinter> i \<bullet> P(i))) = (\<Squnion> i \<bullet> \<not> P(i))"
  by (pred_auto)

lemma not_USUP_ind: "(\<not> (\<Squnion> i \<bullet> P(i))) = (\<Sqinter> i \<bullet> \<not> P(i))"
  by (pred_auto)

lemma UINF_empty [simp]: "(\<Sqinter> i \<in> {} \<bullet> P(i)) = false"
  by (pred_auto)

lemma UINF_insert [simp]: "(\<Sqinter> i\<in>insert x xs \<bullet> P(i)) = (P(x) \<sqinter> (\<Sqinter> i\<in>xs \<bullet> P(i)))"
  apply (pred_simp)
  apply (subst Sup_insert[THEN sym])
  apply (rule_tac cong[of Sup Sup])
   apply (auto)
  done
    
lemma UINF_atLeast_first:
  "P(n) \<sqinter> (\<Sqinter> i \<in> {Suc n..} \<bullet> P(i)) = (\<Sqinter> i \<in> {n..} \<bullet> P(i))"
proof -
  have "insert n {Suc n..} = {n..}"
    by (auto)
  thus ?thesis
    by (metis UINF_insert)
qed  

lemma UINF_atLeast_Suc:
  "(\<Sqinter> i \<in> {Suc m..} \<bullet> P(i)) = (\<Sqinter> i \<in> {m..} \<bullet> P(Suc i))"
  by (rel_simp, metis (full_types) Suc_le_D not_less_eq_eq)

lemma USUP_empty [simp]: "(\<Squnion> i \<in> {} \<bullet> P(i)) = true"
  by (pred_auto)

lemma USUP_insert [simp]: "(\<Squnion> i\<in>insert x xs \<bullet> P(i)) = (P(x) \<squnion> (\<Squnion> i\<in>xs \<bullet> P(i)))"
  apply (pred_simp)
  apply (subst Inf_insert[THEN sym])
  apply (rule_tac cong[of Inf Inf])
   apply (auto)
  done

lemma USUP_atLeast_first:
  "(P(n) \<and> (\<Squnion> i \<in> {Suc n..} \<bullet> P(i))) = (\<Squnion> i \<in> {n..} \<bullet> P(i))"
proof -
  have "insert n {Suc n..} = {n..}"
    by (auto)
  thus ?thesis
    by (metis USUP_insert conj_upred_def)
qed

lemma USUP_atLeast_Suc:
  "(\<Squnion> i \<in> {Suc m..} \<bullet> P(i)) = (\<Squnion> i \<in> {m..} \<bullet> P(Suc i))"
  by (rel_simp, metis (full_types) Suc_le_D not_less_eq_eq)

lemma conj_UINF_dist:
  "(P \<and> (\<Sqinter> Q\<in>S \<bullet> F(Q))) = (\<Sqinter> Q\<in>S \<bullet> P \<and> F(Q))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma conj_UINF_ind_dist:
  "(P \<and> (\<Sqinter> Q \<bullet> F(Q))) = (\<Sqinter> Q \<bullet> P \<and> F(Q))"
  by pred_auto

lemma disj_UINF_dist:
  "S \<noteq> {} \<Longrightarrow> (P \<or> (\<Sqinter> Q\<in>S \<bullet> F(Q))) = (\<Sqinter> Q\<in>S \<bullet> P \<or> F(Q))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma UINF_conj_UINF [simp]: 
  "((\<Sqinter> i\<in>I \<bullet> P(i)) \<or> (\<Sqinter> i\<in>I \<bullet> Q(i))) = (\<Sqinter> i\<in>I \<bullet> P(i) \<or> Q(i))"
  by (rel_auto)

lemma conj_USUP_dist:
  "S \<noteq> {} \<Longrightarrow> (P \<and> (\<Squnion> Q\<in>S \<bullet> F(Q))) = (\<Squnion> Q\<in>S \<bullet> P \<and> F(Q))"
  by (subst uexpr_eq_iff, auto simp add: conj_upred_def USUP.rep_eq inf_uexpr.rep_eq bop.rep_eq lit.rep_eq)

lemma USUP_conj_USUP [simp]: "((\<Squnion> P \<in> A \<bullet> F(P)) \<and> (\<Squnion> P \<in> A \<bullet> G(P))) = (\<Squnion> P \<in> A \<bullet> F(P) \<and> G(P))"
  by (simp add: upred_defs bop.rep_eq lit.rep_eq, pred_auto)

lemma UINF_all_cong [cong]:
  assumes "\<And> P. F(P) = G(P)"
  shows "(\<Sqinter> P \<bullet> F(P)) = (\<Sqinter> P \<bullet> G(P))"
  by (simp add: UINF_as_Sup_collect assms)

lemma UINF_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<Sqinter> P\<in>A \<bullet> F(P)) = (\<Sqinter> P\<in>A \<bullet> G(P))"
  by (simp add: UINF_as_Sup_collect assms)

lemma USUP_all_cong:
  assumes "\<And> P. F(P) = G(P)"
  shows "(\<Squnion> P \<bullet> F(P)) = (\<Squnion> P \<bullet> G(P))"
  by (simp add: assms)
    
lemma USUP_cong:
  assumes "\<And> P. P \<in> A \<Longrightarrow> F(P) = G(P)"
  shows "(\<Squnion> P\<in>A \<bullet> F(P)) = (\<Squnion> P\<in>A \<bullet> G(P))"
  by (simp add: USUP_as_Inf_collect assms)

lemma UINF_subset_mono: "A \<subseteq> B \<Longrightarrow> (\<Sqinter> P\<in>B \<bullet> F(P)) \<sqsubseteq> (\<Sqinter> P\<in>A \<bullet> F(P))"
  by (simp add: SUP_subset_mono UINF_as_Sup_collect)

lemma USUP_subset_mono: "A \<subseteq> B \<Longrightarrow> (\<Squnion> P\<in>A \<bullet> F(P)) \<sqsubseteq> (\<Squnion> P\<in>B \<bullet> F(P))"
  by (simp add: INF_superset_mono USUP_as_Inf_collect)

lemma UINF_impl: "(\<Sqinter> P\<in>A \<bullet> F(P) \<Rightarrow> G(P)) = ((\<Squnion> P\<in>A \<bullet> F(P)) \<Rightarrow> (\<Sqinter> P\<in>A \<bullet> G(P)))"
  by (pred_auto)

lemma USUP_is_forall: "(\<Squnion> x \<bullet> P(x)) = (\<^bold>\<forall> x \<bullet> P(x))"
  by (pred_simp)

lemma USUP_ind_is_forall: "(\<Squnion> x\<in>A \<bullet> P(x)) = (\<^bold>\<forall> x\<in>\<guillemotleft>A\<guillemotright> \<bullet> P(x))"
  by (pred_auto)

lemma UINF_is_exists: "(\<Sqinter> x \<bullet> P(x)) = (\<^bold>\<exists> x \<bullet> P(x))"
  by (pred_simp)

lemma UINF_all_nats [simp]:
  fixes P :: "nat \<Rightarrow> '\<alpha> upred"
  shows "(\<Sqinter> n \<bullet> \<Sqinter> i\<in>{0..n} \<bullet> P(i)) = (\<Sqinter> n \<bullet> P(n))"
  by (pred_auto)

lemma USUP_all_nats [simp]:
  fixes P :: "nat \<Rightarrow> '\<alpha> upred"
  shows "(\<Squnion> n \<bullet> \<Squnion> i\<in>{0..n} \<bullet> P(i)) = (\<Squnion> n \<bullet> P(n))"
  by (pred_auto)

lemma UINF_upto_expand_first:
  "m < n \<Longrightarrow> (\<Sqinter> i \<in> {m..<n} \<bullet> P(i)) = ((P(m) :: '\<alpha> upred) \<or> (\<Sqinter> i \<in> {Suc m..<n} \<bullet> P(i)))"
  apply (rel_auto) using Suc_leI le_eq_less_or_eq by auto

lemma UINF_upto_expand_last:
  "(\<Sqinter> i \<in> {0..<Suc(n)} \<bullet> P(i)) = ((\<Sqinter> i \<in> {0..<n} \<bullet> P(i)) \<or> P(n))"
  apply (rel_auto)
  using less_SucE by blast
    
lemma UINF_Suc_shift: "(\<Sqinter> i \<in> {Suc 0..<Suc n} \<bullet> P(i)) = (\<Sqinter> i \<in> {0..<n} \<bullet> P(Suc i))"
  apply (rel_simp)
  apply (rule cong[of Sup], auto)
  using less_Suc_eq_0_disj by auto

lemma USUP_upto_expand_first:
  "(\<Squnion> i \<in> {0..<Suc(n)} \<bullet> P(i)) = (P(0) \<and> (\<Squnion> i \<in> {1..<Suc(n)} \<bullet> P(i)))"
  apply (rel_auto)
  using not_less by auto

lemma USUP_Suc_shift: "(\<Squnion> i \<in> {Suc 0..<Suc n} \<bullet> P(i)) = (\<Squnion> i \<in> {0..<n} \<bullet> P(Suc i))"
  apply (rel_simp)
  apply (rule cong[of Inf], auto)
  using less_Suc_eq_0_disj by auto
    
lemma UINF_list_conv:
  "(\<Sqinter> i \<in> {0..<length(xs)} \<bullet> f (xs ! i)) = foldr (\<or>) (map f xs) false"    
  apply (induct xs)
   apply (rel_auto)
  apply (simp add: UINF_upto_expand_first UINF_Suc_shift)
  done

lemma USUP_list_conv:
  "(\<Squnion> i \<in> {0..<length(xs)} \<bullet> f (xs ! i)) = foldr (\<and>) (map f xs) true"    
  apply (induct xs)
   apply (rel_auto)
  apply (simp_all add: USUP_upto_expand_first USUP_Suc_shift)
  done

lemma UINF_refines:
  "\<lbrakk> \<And> i. i\<in>I \<Longrightarrow> P \<sqsubseteq> Q i \<rbrakk> \<Longrightarrow> P \<sqsubseteq> (\<Sqinter> i\<in>I \<bullet> Q i)"
  by (simp add: UINF_as_Sup_collect, metis SUP_least)

lemma UINF_refines':
  assumes "\<And> i. P \<sqsubseteq> Q(i)" 
  shows "P \<sqsubseteq> (\<Sqinter> i \<bullet> Q(i))"
  using assms
  apply (rel_auto) using Sup_le_iff by fastforce

lemma UINF_pred_ueq [simp]: 
  "(\<Sqinter> x | \<guillemotleft>x\<guillemotright> =\<^sub>u v \<bullet> P(x)) = (P x)\<lbrakk>x\<rightarrow>v\<rbrakk>"
  by (pred_auto)

lemma UINF_pred_lit_eq [simp]: 
  "(\<Sqinter> x | \<guillemotleft>x = v\<guillemotright> \<bullet> P(x)) = (P v)"
  by (pred_auto)

subsection \<open> Equality laws \<close>

lemma eq_upred_refl [simp]: "(x =\<^sub>u x) = true"
  by (pred_auto)

lemma eq_upred_sym: "(x =\<^sub>u y) = (y =\<^sub>u x)"
  by (pred_auto)

lemma eq_cong_left:
  assumes "vwb_lens x" "$x \<sharp> Q" "$x\<acute> \<sharp> Q" "$x \<sharp> R" "$x\<acute> \<sharp> R"
  shows "(($x\<acute> =\<^sub>u $x \<and> Q) = ($x\<acute> =\<^sub>u $x \<and> R)) \<longleftrightarrow> (Q = R)"
  using assms
  by (pred_simp, (meson mwb_lens_def vwb_lens_mwb weak_lens_def)+)

lemma conj_eq_in_var_subst:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "vwb_lens x"
  shows "(P \<and> $x =\<^sub>u v) = (P\<lbrakk>v/$x\<rbrakk> \<and> $x =\<^sub>u v)"
  using assms
  by (pred_simp, (metis vwb_lens_wb wb_lens.get_put)+)

lemma conj_eq_out_var_subst:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  assumes "vwb_lens x"
  shows "(P \<and> $x\<acute> =\<^sub>u v) = (P\<lbrakk>v/$x\<acute>\<rbrakk> \<and> $x\<acute> =\<^sub>u v)"
  using assms
  by (pred_simp, (metis vwb_lens_wb wb_lens.get_put)+)

lemma conj_pos_var_subst:
  assumes "vwb_lens x"
  shows "($x \<and> Q) = ($x \<and> Q\<lbrakk>true/$x\<rbrakk>)"
  using assms
  by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma conj_neg_var_subst:
  assumes "vwb_lens x"
  shows "(\<not> $x \<and> Q) = (\<not> $x \<and> Q\<lbrakk>false/$x\<rbrakk>)"
  using assms
  by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma upred_eq_true [simp]: "(p =\<^sub>u true) = p"
  by (pred_auto)

lemma upred_eq_false [simp]: "(p =\<^sub>u false) = (\<not> p)"
  by (pred_auto)

lemma upred_true_eq [simp]: "(true =\<^sub>u p) = p"
  by (pred_auto)

lemma upred_false_eq [simp]: "(false =\<^sub>u p) = (\<not> p)"
  by (pred_auto)

lemma conj_var_subst:
  assumes "vwb_lens x"
  shows "(P \<and> var x =\<^sub>u v) = (P\<lbrakk>v/x\<rbrakk> \<and> var x =\<^sub>u v)"
  using assms
  by (pred_simp, (metis (full_types) vwb_lens_def wb_lens.get_put)+)

subsection \<open> HOL Variable Quantifiers \<close>
    
lemma shEx_unbound [simp]: "(\<^bold>\<exists> x \<bullet> P) = P"
  by (pred_auto)

lemma shEx_bool [simp]: "shEx P = (P True \<or> P False)"
  by (pred_simp, metis (full_types))

lemma shEx_commute: "(\<^bold>\<exists> x \<bullet> \<^bold>\<exists> y \<bullet> P x y) = (\<^bold>\<exists> y \<bullet> \<^bold>\<exists> x \<bullet> P x y)"
  by (pred_auto)

lemma shEx_cong: "\<lbrakk> \<And> x. P x = Q x \<rbrakk> \<Longrightarrow> shEx P = shEx Q"
  by (pred_auto)

lemma shEx_insert: "(\<^bold>\<exists> x \<in> insert\<^sub>u y A \<bullet> P(x)) = (P(x)\<lbrakk>x\<rightarrow>y\<rbrakk> \<or> (\<^bold>\<exists> x \<in> A \<bullet> P(x)))"
  by (pred_auto)

lemma shEx_one_point: "(\<^bold>\<exists> x \<bullet> \<guillemotleft>x\<guillemotright> =\<^sub>u v \<and> P(x)) = P(x)\<lbrakk>x\<rightarrow>v\<rbrakk>"
  by (rel_auto)

lemma shAll_unbound [simp]: "(\<^bold>\<forall> x \<bullet> P) = P"
  by (pred_auto)

lemma shAll_bool [simp]: "shAll P = (P True \<and> P False)"
  by (pred_simp, metis (full_types))

lemma shAll_cong: "\<lbrakk> \<And> x. P x = Q x \<rbrakk> \<Longrightarrow> shAll P = shAll Q"
  by (pred_auto)
    
text \<open> Quantifier lifting \<close>

named_theorems uquant_lift

lemma shEx_lift_conj_1 [uquant_lift]:
  "((\<^bold>\<exists> x \<bullet> P(x)) \<and> Q) = (\<^bold>\<exists> x \<bullet> P(x) \<and> Q)"
  by (pred_auto)

lemma shEx_lift_conj_2 [uquant_lift]:
  "(P \<and> (\<^bold>\<exists> x \<bullet> Q(x))) = (\<^bold>\<exists> x \<bullet> P \<and> Q(x))"
  by (pred_auto)

subsection \<open> Case Splitting \<close>
  
lemma eq_split_subst:
  assumes "vwb_lens x"
  shows "(P = Q) \<longleftrightarrow> (\<forall> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)"
  using assms
  by (pred_auto, metis vwb_lens_wb wb_lens.source_stability)

lemma eq_split_substI:
  assumes "vwb_lens x" "\<And> v. P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk> = Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>"
  shows "P = Q"
  using assms(1) assms(2) eq_split_subst by blast

lemma taut_split_subst:
  assumes "vwb_lens x"
  shows "`P` \<longleftrightarrow> (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
  using assms
  by (pred_auto, metis vwb_lens_wb wb_lens.source_stability)

lemma eq_split:
  assumes "`P \<Rightarrow> Q`" "`Q \<Rightarrow> P`"
  shows "P = Q"
  using assms
  by (pred_auto)

lemma bool_eq_splitI:
  assumes "vwb_lens x" "P\<lbrakk>true/x\<rbrakk> = Q\<lbrakk>true/x\<rbrakk>" "P\<lbrakk>false/x\<rbrakk> = Q\<lbrakk>false/x\<rbrakk>"
  shows "P = Q"
  by (metis (full_types) assms eq_split_subst false_alt_def true_alt_def)

lemma subst_bool_split:
  assumes "vwb_lens x"
  shows "`P` = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
proof -
  from assms have "`P` = (\<forall> v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`)"
    by (subst taut_split_subst[of x], auto)
  also have "... = (`P\<lbrakk>\<guillemotleft>True\<guillemotright>/x\<rbrakk>` \<and> `P\<lbrakk>\<guillemotleft>False\<guillemotright>/x\<rbrakk>`)"
    by (metis (mono_tags, lifting))
  also have "... = `(P\<lbrakk>false/x\<rbrakk> \<and> P\<lbrakk>true/x\<rbrakk>)`"
    by (pred_auto)
  finally show ?thesis .
qed

lemma subst_eq_replace:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(p\<lbrakk>u/x\<rbrakk> \<and> u =\<^sub>u v) = (p\<lbrakk>v/x\<rbrakk> \<and> u =\<^sub>u v)"
  by (pred_auto)

subsection \<open> UTP Quantifiers \<close>
    
lemma one_point:
  assumes "mwb_lens x" "x \<sharp> v"
  shows "(\<exists> x \<bullet> P \<and> var x =\<^sub>u v) = P\<lbrakk>v/x\<rbrakk>"
  using assms
  by (pred_auto)

lemma exists_twice: "mwb_lens x \<Longrightarrow> (\<exists> x \<bullet> \<exists> x \<bullet> P) = (\<exists> x \<bullet> P)"
  by (pred_auto)

lemma all_twice: "mwb_lens x \<Longrightarrow> (\<forall> x \<bullet> \<forall> x \<bullet> P) = (\<forall> x \<bullet> P)"
  by (pred_auto)

lemma exists_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> P)"
  by (pred_auto)

lemma all_sub: "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> (\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> P)"
  by (pred_auto)

lemma ex_commute:
  assumes "x \<bowtie> y"
  shows "(\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
  done

lemma all_commute:
  assumes "x \<bowtie> y"
  shows "(\<forall> x \<bullet> \<forall> y \<bullet> P) = (\<forall> y \<bullet> \<forall> x \<bullet> P)"
  using assms
  apply (pred_auto)
  using lens_indep_comm apply fastforce+
  done

lemma ex_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<exists> x \<bullet> P) = (\<exists> y \<bullet> P)"
  using assms
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))

lemma all_equiv:
  assumes "x \<approx>\<^sub>L y"
  shows "(\<forall> x \<bullet> P) = (\<forall> y \<bullet> P)"
  using assms
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))

lemma ex_zero:
  "(\<exists> \<emptyset> \<bullet> P) = P"
  by (pred_auto)

lemma all_zero:
  "(\<forall> \<emptyset> \<bullet> P) = P"
  by (pred_auto)

lemma ex_plus:
  "(\<exists> y;x \<bullet> P) = (\<exists> x \<bullet> \<exists> y \<bullet> P)"
  by (pred_auto)

lemma all_plus:
  "(\<forall> y;x \<bullet> P) = (\<forall> x \<bullet> \<forall> y \<bullet> P)"
  by (pred_auto)

lemma closure_all:
  "[P]\<^sub>u = (\<forall> \<Sigma> \<bullet> P)"
  by (pred_auto)

lemma unrest_as_exists:
  "vwb_lens x \<Longrightarrow> (x \<sharp> P) \<longleftrightarrow> ((\<exists> x \<bullet> P) = P)"
  by (pred_simp, metis vwb_lens.put_eq)

lemma ex_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<exists> x \<bullet> P) \<sqsubseteq> (\<exists> x \<bullet> Q)"
  by (pred_auto)

lemma ex_weakens: "wb_lens x \<Longrightarrow> (\<exists> x \<bullet> P) \<sqsubseteq> P"
  by (pred_simp, metis wb_lens.get_put)

lemma all_mono: "P \<sqsubseteq> Q \<Longrightarrow> (\<forall> x \<bullet> P) \<sqsubseteq> (\<forall> x \<bullet> Q)"
  by (pred_auto)

lemma all_strengthens: "wb_lens x \<Longrightarrow> P \<sqsubseteq> (\<forall> x \<bullet> P)"
  by (pred_simp, metis wb_lens.get_put)

lemma ex_unrest: "x \<sharp> P \<Longrightarrow> (\<exists> x \<bullet> P) = P"
  by (pred_auto)

lemma all_unrest: "x \<sharp> P \<Longrightarrow> (\<forall> x \<bullet> P) = P"
  by (pred_auto)

lemma not_ex_not: "\<not> (\<exists> x \<bullet> \<not> P) = (\<forall> x \<bullet> P)"
  by (pred_auto)

lemma not_all_not: "\<not> (\<forall> x \<bullet> \<not> P) = (\<exists> x \<bullet> P)"
  by (pred_auto)

lemma ex_conj_contr_left: "x \<sharp> P \<Longrightarrow> (\<exists> x \<bullet> P \<and> Q) = (P \<and> (\<exists> x \<bullet> Q))"
  by (pred_auto)

lemma ex_conj_contr_right: "x \<sharp> Q \<Longrightarrow> (\<exists> x \<bullet> P \<and> Q) = ((\<exists> x \<bullet> P) \<and> Q)"
  by (pred_auto)

subsection \<open> Variable Restriction \<close>    
  
lemma var_res_all: 
  "P \<restriction>\<^sub>v \<Sigma> = P"
  by (rel_auto)
  
lemma var_res_twice: 
  "mwb_lens x \<Longrightarrow> P \<restriction>\<^sub>v x \<restriction>\<^sub>v x = P \<restriction>\<^sub>v x"
  by (pred_auto)
    
subsection \<open> Conditional laws \<close>

lemma cond_def:
  "(P \<triangleleft> b \<triangleright> Q) = ((b \<and> P) \<or> ((\<not> b) \<and> Q))"
  by (pred_auto)
    
lemma cond_idem [simp]:"(P \<triangleleft> b \<triangleright> P) = P" by (pred_auto)

lemma cond_true_false [simp]: "true \<triangleleft> b \<triangleright> false = b" by (pred_auto)
    
lemma cond_symm:"(P \<triangleleft> b \<triangleright> Q) = (Q \<triangleleft> \<not> b \<triangleright> P)" by (pred_auto)

lemma cond_assoc: "((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> R) = (P \<triangleleft> b \<and> c \<triangleright> (Q \<triangleleft> c \<triangleright> R))" by (pred_auto)

lemma cond_distr: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> c \<triangleright> R)) = ((P \<triangleleft> b \<triangleright> Q) \<triangleleft> c \<triangleright> (P \<triangleleft> b \<triangleright> R))" by (pred_auto)

lemma cond_unit_T [simp]:"(P \<triangleleft> true \<triangleright> Q) = P" by (pred_auto)

lemma cond_unit_F [simp]:"(P \<triangleleft> false \<triangleright> Q) = Q" by (pred_auto)

lemma cond_conj_not: "((P \<triangleleft> b \<triangleright> Q) \<and> (\<not> b)) = (Q \<and> (\<not> b))"
  by (rel_auto)
    
lemma cond_and_T_integrate:
  "((P \<and> b) \<or> (Q \<triangleleft> b \<triangleright> R)) = ((P \<or> Q) \<triangleleft> b \<triangleright> R)"
  by (pred_auto)

lemma cond_L6: "(P \<triangleleft> b \<triangleright> (Q \<triangleleft> b \<triangleright> R)) = (P \<triangleleft> b \<triangleright> R)" by (pred_auto)

lemma cond_L7: "(P \<triangleleft> b \<triangleright> (P \<triangleleft> c \<triangleright> Q)) = (P \<triangleleft> b \<or> c \<triangleright> Q)" by (pred_auto)

lemma cond_and_distr: "((P \<and> Q) \<triangleleft> b \<triangleright> (R \<and> S)) = ((P \<triangleleft> b \<triangleright> R) \<and> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_or_distr: "((P \<or> Q) \<triangleleft> b \<triangleright> (R \<or> S)) = ((P \<triangleleft> b \<triangleright> R) \<or> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_imp_distr:
"((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (R \<Rightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Rightarrow> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_eq_distr:
"((P \<Leftrightarrow> Q) \<triangleleft> b \<triangleright> (R \<Leftrightarrow> S)) = ((P \<triangleleft> b \<triangleright> R) \<Leftrightarrow> (Q \<triangleleft> b \<triangleright> S))" by (pred_auto)

lemma cond_conj_distr:"(P \<and> (Q \<triangleleft> b \<triangleright> S)) = ((P \<and> Q) \<triangleleft> b \<triangleright> (P \<and> S))" by (pred_auto)

lemma cond_disj_distr:"(P \<or> (Q \<triangleleft> b \<triangleright> S)) = ((P \<or> Q) \<triangleleft> b \<triangleright> (P \<or> S))" by (pred_auto)

lemma cond_neg: "\<not> (P \<triangleleft> b \<triangleright> Q) = ((\<not> P) \<triangleleft> b \<triangleright> (\<not> Q))" by (pred_auto)

lemma cond_conj: "P \<triangleleft> b \<and> c \<triangleright> Q = (P \<triangleleft> c \<triangleright> Q) \<triangleleft> b \<triangleright> Q"
  by (pred_auto)

lemma spec_cond_dist: "(P \<Rightarrow> (Q \<triangleleft> b \<triangleright> R)) = ((P \<Rightarrow> Q) \<triangleleft> b \<triangleright> (P \<Rightarrow> R))"
  by (pred_auto)

lemma cond_USUP_dist: "(\<Squnion> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Squnion> P\<in>S \<bullet> G(P)) = (\<Squnion> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (pred_auto)

lemma cond_UINF_dist: "(\<Sqinter> P\<in>S \<bullet> F(P)) \<triangleleft> b \<triangleright> (\<Sqinter> P\<in>S \<bullet> G(P)) = (\<Sqinter> P\<in>S \<bullet> F(P) \<triangleleft> b \<triangleright> G(P))"
  by (pred_auto)

lemma cond_var_subst_left:
  assumes "vwb_lens x"
  shows "(P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> Q) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (pred_auto, metis (full_types) vwb_lens_wb wb_lens.get_put)

lemma cond_var_subst_right:
  assumes "vwb_lens x"
  shows "(P \<triangleleft> var x \<triangleright> Q\<lbrakk>false/x\<rbrakk>) = (P \<triangleleft> var x \<triangleright> Q)"
  using assms by (pred_auto, metis (full_types) vwb_lens.put_eq)

lemma cond_var_split:
  "vwb_lens x \<Longrightarrow> (P\<lbrakk>true/x\<rbrakk> \<triangleleft> var x \<triangleright> P\<lbrakk>false/x\<rbrakk>) = P"
  by (rel_simp, (metis (full_types) vwb_lens.put_eq)+)

lemma cond_assign_subst:
  "vwb_lens x \<Longrightarrow> (P \<triangleleft> utp_expr.var x =\<^sub>u v \<triangleright> Q) = (P\<lbrakk>v/x\<rbrakk> \<triangleleft> utp_expr.var x =\<^sub>u v \<triangleright> Q)"
  apply (rel_simp) using vwb_lens.put_eq by force
    
lemma conj_conds: 
  "(P1 \<triangleleft> b \<triangleright> Q1 \<and> P2 \<triangleleft> b \<triangleright> Q2) = (P1 \<and> P2) \<triangleleft> b \<triangleright> (Q1 \<and> Q2)"
  by pred_auto

lemma disj_conds:
  "(P1 \<triangleleft> b \<triangleright> Q1 \<or> P2 \<triangleleft> b \<triangleright> Q2) = (P1 \<or> P2) \<triangleleft> b \<triangleright> (Q1 \<or> Q2)"
  by pred_auto

lemma cond_mono:
  "\<lbrakk> P\<^sub>1 \<sqsubseteq> P\<^sub>2; Q\<^sub>1 \<sqsubseteq> Q\<^sub>2 \<rbrakk> \<Longrightarrow> (P\<^sub>1 \<triangleleft> b \<triangleright> Q\<^sub>1) \<sqsubseteq> (P\<^sub>2 \<triangleleft> b \<triangleright> Q\<^sub>2)"
  by (rel_auto)

lemma cond_monotonic:
  "\<lbrakk> mono P; mono Q \<rbrakk> \<Longrightarrow> mono (\<lambda> X. P X \<triangleleft> b \<triangleright> Q X)"
  by (simp add: mono_def, rel_blast)

subsection \<open> Additional Expression Laws \<close>

lemma le_pred_refl [simp]:
  fixes x :: "('a::preorder, '\<alpha>) uexpr"
  shows "(x \<le>\<^sub>u x) = true"
  by (pred_auto)

lemma uzero_le_laws [simp]:
  "(0 :: ('a::{linordered_semidom}, '\<alpha>) uexpr) \<le>\<^sub>u numeral x = true"
  "(1 :: ('a::{linordered_semidom}, '\<alpha>) uexpr) \<le>\<^sub>u numeral x = true"
  "(0 :: ('a::{linordered_semidom}, '\<alpha>) uexpr) \<le>\<^sub>u 1 = true"
  by (pred_simp)+
  
lemma unumeral_le_1 [simp]:
  assumes "(numeral i :: 'a::{numeral,ord}) \<le> numeral j"
  shows "(numeral i :: ('a, '\<alpha>) uexpr) \<le>\<^sub>u numeral j = true"
  using assms by (pred_auto)

lemma unumeral_le_2 [simp]:
  assumes "(numeral i :: 'a::{numeral,linorder}) > numeral j"
  shows "(numeral i :: ('a, '\<alpha>) uexpr) \<le>\<^sub>u numeral j = false"
  using assms by (pred_auto)
    
lemma uset_laws [simp]:
  "x \<in>\<^sub>u {}\<^sub>u = false"
  "x \<in>\<^sub>u {m..n}\<^sub>u = (m \<le>\<^sub>u x \<and> x \<le>\<^sub>u n)"
  by (pred_auto)+
  
lemma ulit_eq [simp]: "x = y \<Longrightarrow> (\<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>y\<guillemotright>) = true"
  by (rel_auto)
    
lemma ulit_neq [simp]: "x \<noteq> y \<Longrightarrow> (\<guillemotleft>x\<guillemotright> =\<^sub>u \<guillemotleft>y\<guillemotright>) = false"
  by (rel_auto)
    
lemma uset_mems [simp]:
  "x \<in>\<^sub>u {y}\<^sub>u = (x =\<^sub>u y)"
  "x \<in>\<^sub>u A \<union>\<^sub>u B = (x \<in>\<^sub>u A \<or> x \<in>\<^sub>u B)"
  "x \<in>\<^sub>u A \<inter>\<^sub>u B = (x \<in>\<^sub>u A \<and> x \<in>\<^sub>u B)"
  by (rel_auto)+
    
subsection \<open> Refinement By Observation \<close>
    
text \<open> Function to obtain the set of observations of a predicate \<close>
    
definition obs_upred :: "'\<alpha> upred \<Rightarrow> '\<alpha> set" ("\<lbrakk>_\<rbrakk>\<^sub>o")
where [upred_defs]: "\<lbrakk>P\<rbrakk>\<^sub>o = {b. \<lbrakk>P\<rbrakk>\<^sub>eb}"
    
lemma obs_upred_refine_iff: 
  "P \<sqsubseteq> Q \<longleftrightarrow> \<lbrakk>Q\<rbrakk>\<^sub>o \<subseteq> \<lbrakk>P\<rbrakk>\<^sub>o"
  by (pred_auto)
    
text \<open> A refinement can be demonstrated by considering only the observations of the predicates
  which are relevant, i.e. not unrestricted, for them. In other words, if the alphabet can
  be split into two disjoint segments, $x$ and $y$, and neither predicate refers to $y$ then
  only $x$ need be considered when checking for observations. \<close>
    
lemma refine_by_obs:
  assumes "x \<bowtie> y" "bij_lens (x +\<^sub>L y)" "y \<sharp> P" "y \<sharp> Q" "{v. `P\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`} \<subseteq> {v. `Q\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>`}"
  shows "Q \<sqsubseteq> P"
  using assms(3-5)
  apply (simp add: obs_upred_refine_iff subset_eq)
  apply (pred_simp)
  apply (rename_tac b)
  apply (drule_tac x="get\<^bsub>x\<^esub>b" in spec)
  apply (auto simp add: assms)
   apply (metis assms(1) assms(2) bij_lens.axioms(2) bij_lens_axioms_def lens_override_def lens_override_plus)+
  done
    
subsection \<open> Cylindric Algebra \<close>

lemma C1: "(\<exists> x \<bullet> false) = false"
  by (pred_auto)

lemma C2: "wb_lens x \<Longrightarrow> `P \<Rightarrow> (\<exists> x \<bullet> P)`"
  by (pred_simp, metis wb_lens.get_put)

lemma C3: "mwb_lens x \<Longrightarrow> (\<exists> x \<bullet> (P \<and> (\<exists> x \<bullet> Q))) = ((\<exists> x \<bullet> P) \<and> (\<exists> x \<bullet> Q))"
  by (pred_auto)

lemma C4a: "x \<approx>\<^sub>L y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  by (pred_simp, metis (no_types, lifting) lens.select_convs(2))+

lemma C4b: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<bullet> \<exists> y \<bullet> P) = (\<exists> y \<bullet> \<exists> x \<bullet> P)"
  using ex_commute by blast

lemma C5:
  fixes x :: "('a \<Longrightarrow> '\<alpha>)"
  shows "(&x =\<^sub>u &x) = true"
  by (pred_auto)

lemma C6:
  assumes "wb_lens x" "x \<bowtie> y" "x \<bowtie> z"
  shows "(&y =\<^sub>u &z) = (\<exists> x \<bullet> &y =\<^sub>u &x \<and> &x =\<^sub>u &z)"
  using assms
  by (pred_simp, (metis lens_indep_def)+)

lemma C7:
  assumes "weak_lens x" "x \<bowtie> y"
  shows "((\<exists> x \<bullet> &x =\<^sub>u &y \<and> P) \<and> (\<exists> x \<bullet> &x =\<^sub>u &y \<and> \<not> P)) = false"
  using assms
  by (pred_simp, simp add: lens_indep_sym)

end