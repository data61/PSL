(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Results on Infinite Sequences\<close>

(* TODO: Move to Abstract-Rewriting.Seq -- maybe this is of very general interest... *)
theory Seq_More
  imports
    "Abstract-Rewriting.Seq"
    Transitive_Closure_More
begin

lemma down_chain_imp_eq:
  fixes f :: "nat seq"
  assumes "\<forall>i. f i \<ge> f (Suc i)"
  shows "\<exists>N. \<forall>i > N. f i = f (Suc i)"
proof -
  let ?F = "{f i | i. True}"
  from wf_less [unfolded wf_eq_minimal, THEN spec, of ?F]
    obtain x where "x \<in> ?F" and *: "\<forall>y. y < x \<longrightarrow> y \<notin> ?F" by auto
  obtain N where "f N = x" using \<open>x \<in> ?F\<close> by auto
  moreover have "\<forall>i > N. f i \<in> ?F" by auto
  ultimately have "\<forall>i > N. \<not> f i < x" using * by auto
  moreover have "\<forall>i > N. f N \<ge> f i"
    using chainp_imp_rtranclp [of "(\<ge>)" f, OF assms] by simp
  ultimately have "\<forall>i > N. f i = f (Suc i)"
    using \<open>f N = x\<close> by (auto) (metis less_SucI order.not_eq_order_implies_strict)
  then show ?thesis ..
qed

lemma inc_seq_greater:
  fixes f :: "nat seq"
  assumes "\<forall>i. f i < f (Suc i)"
  shows "\<exists>i. f i > N"
  using assms
  apply (induct N)
   apply (auto)
   apply (metis neq0_conv)
  by (metis Suc_lessI)

end
