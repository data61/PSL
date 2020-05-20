section\<open>The general Rasiowa-Sikorski lemma\<close>
theory Rasiowa_Sikorski imports Forcing_Notions Pointed_DC begin

context countable_generic
begin

lemma RS_relation:
  assumes "p\<in>P" "n\<in>nat"
  shows "\<exists>y\<in>P. \<langle>p,y\<rangle> \<in> (\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P\<times>P. y\<preceq>x \<and> y\<in>\<D>`(pred(m))})`n"
proof -
  from seq_of_denses \<open>n\<in>nat\<close>
  have "dense(\<D> ` pred(n))" by simp
  with \<open>p\<in>P\<close>
  have "\<exists>d\<in>\<D> ` Arith.pred(n). d\<preceq> p"
    unfolding dense_def by simp
  then obtain d where 3: "d \<in> \<D> ` Arith.pred(n) \<and> d\<preceq> p"
    by blast
  from countable_subs_of_P \<open>n\<in>nat\<close>
  have "\<D> ` Arith.pred(n) \<in> Pow(P)"
    by (blast dest:apply_funtype intro:pred_type)
  then 
  have "\<D> ` Arith.pred(n) \<subseteq> P" 
    by (rule PowD)
  with 3
  have "d \<in> P \<and> d\<preceq> p \<and> d \<in> \<D> ` Arith.pred(n)"
    by auto
  with \<open>p\<in>P\<close> \<open>n\<in>nat\<close> 
  show ?thesis by auto
qed

lemma DC_imp_RS_sequence:
  assumes "p\<in>P"
  shows "\<exists>f. f: nat\<rightarrow>P \<and> f ` 0 = p \<and> 
     (\<forall>n\<in>nat. f ` succ(n)\<preceq> f ` n \<and> f ` succ(n) \<in> \<D> ` n)"
proof -
  let ?S="(\<lambda>m\<in>nat. {\<langle>x,y\<rangle>\<in>P\<times>P. y\<preceq>x \<and> y\<in>\<D>`(pred(m))})"
  have "\<forall>x\<in>P. \<forall>n\<in>nat. \<exists>y\<in>P. \<langle>x,y\<rangle> \<in> ?S`n" 
    using RS_relation by (auto)
  then
  have "\<forall>a\<in>P. (\<exists>f \<in> nat\<rightarrow>P. f`0 = a \<and> (\<forall>n \<in> nat. \<langle>f`n,f`succ(n)\<rangle>\<in>?S`succ(n)))"
    using sequence_DC by (blast)
  with \<open>p\<in>P\<close>
  show ?thesis by auto
qed
  
theorem rasiowa_sikorski:
  "p\<in>P \<Longrightarrow> \<exists>G. p\<in>G \<and> D_generic(G)"
  using RS_sequence_imp_rasiowa_sikorski by (auto dest:DC_imp_RS_sequence)

end (* countable_generic *)

end