section\<open>Separative notions and proper extensions\<close>
theory Proper_Extension
  imports
    Names

begin

text\<open>The key ingredient to obtain a proper extension is to have
a \<^emph>\<open>separative preorder\<close>:\<close>

locale separative_notion = forcing_notion +
  assumes separative: "p\<in>P \<Longrightarrow> \<exists>q\<in>P. \<exists>r\<in>P. q \<preceq> p \<and> r \<preceq> p \<and> q \<bottom> r"
begin

text\<open>For separative preorders, the complement of every filter is
dense. Hence an $M$-generic filter can't belong to the ground model.\<close>

lemma filter_complement_dense:
  assumes "filter(G)" shows "dense(P - G)"
proof
  fix p
  assume "p\<in>P"
  show "\<exists>d\<in>P - G. d \<preceq> p"
  proof (cases "p\<in>G")
    case True
    note \<open>p\<in>P\<close> assms
    moreover
    obtain q r where "q \<preceq> p" "r \<preceq> p" "q \<bottom> r" "q\<in>P" "r\<in>P" 
      using separative[OF \<open>p\<in>P\<close>]
      by force
    with \<open>filter(G)\<close>
    obtain s where "s \<preceq> p" "s \<notin> G" "s \<in> P"
      using filter_imp_compat[of G q r]
      by auto
    then
    show ?thesis by blast
  next
    case False
    with \<open>p\<in>P\<close> 
    show ?thesis using leq_reflI unfolding Diff_def by auto
  qed
qed

end (* separative_notion *)

locale ctm_separative = forcing_data + separative_notion
begin

lemma generic_not_in_M: assumes "M_generic(G)"  shows "G \<notin> M"
proof
  assume "G\<in>M"
  then
  have "P - G \<in> M" 
    using P_in_M Diff_closed by simp
  moreover
  have "\<not>(\<exists>q\<in>G. q \<in> P - G)" "(P - G) \<subseteq> P"
    unfolding Diff_def by auto
  moreover
  note assms
  ultimately
  show "False"
    using filter_complement_dense[of G] M_generic_denseD[of G "P-G"] 
      M_generic_def by simp \<comment> \<open>need to put generic ==> filter in claset\<close>
qed

theorem proper_extension: assumes "M_generic(G)" shows "M \<noteq> M[G]"
  using assms G_in_Gen_Ext[of G] one_in_G[of G] generic_not_in_M
  by force

end (* ctm_separative *)

end