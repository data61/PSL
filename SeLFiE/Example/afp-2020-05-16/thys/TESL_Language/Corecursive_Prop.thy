(*chapter\<open>Equivalence of Operational and Denotational Semantics\<close>*)
text\<open>\chapter[Semantics Equivalence]{Equivalence of the Operational and Denotational Semantics}\<close>

theory Corecursive_Prop
  imports
    SymbolicPrimitive
    Operational
    Denotational

begin

section \<open>Stepwise denotational interpretation of TESL atoms\<close>

text \<open>
  In order to prove the equivalence of the denotational and operational semantics, 
  we need to be able to ignore the past (for which the constraints are encoded 
  in the context) and consider only the satisfaction of the constraints from
  a given instant index.
  For this purpose, we define an interpretation of TESL formulae for a suffix of a run.
  That interpretation is closely related to the denotational semantics as
  defined in the preceding chapters.
\<close>
fun TESL_interpretation_atomic_stepwise
    :: \<open>('\<tau>::linordered_field) TESL_atomic \<Rightarrow> nat \<Rightarrow> '\<tau> run set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>\<close>)
where
  \<open>\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<exists>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>}\<close>
| \<open>\<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2))}\<close>
| \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave)}\<close>
| \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave)}\<close>
| \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
               (let measured_time = time ((Rep_run \<rho>) n measuring) in
                \<forall>m \<ge> n. first_time \<rho> measuring m (measured_time + \<delta>\<tau>)
                         \<longrightarrow> hamlet ((Rep_run \<rho>) m slave)
               )
      }\<close>
| \<open>\<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count \<rho> K\<^sub>1 n)}\<close>
| \<open>\<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n)}\<close>
| \<open>\<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> i\<^esup> =
      {\<rho>. \<forall>n\<ge>i. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet ((Rep_run \<rho>) m K\<^sub>2))}\<close>

text \<open>
  The denotational interpretation of TESL formulae can be unfolded into the 
  stepwise interpretation.
\<close>
lemma TESL_interp_unfold_stepwise_sporadicon:
  \<open>\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_tagrelgen:
  \<open>\<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_implies:
  \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_implies_not:
  \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_timedelayed:
  \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat.
          Y = \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_weakly_precedes:
  \<open>\<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_strictly_precedes:
  \<open>\<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
    = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

lemma TESL_interp_unfold_stepwise_kills:
  \<open>\<lbrakk> master kills slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> master kills slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
by auto

text \<open>
  Positive atomic formulae (the ones that create ticks from nothing) are unfolded
  as the union of the stepwise interpretations.
\<close>
theorem TESL_interp_unfold_stepwise_positive_atoms:
  assumes \<open>positive_atom \<phi>\<close>
    shows \<open>\<lbrakk> \<phi>::'\<tau>::linordered_field TESL_atomic \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L
            = \<Union> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
proof -
  from positive_atom.elims(2)[OF assms]
    obtain u v w where \<open>\<phi> = (u sporadic v on w)\<close> by blast
  with TESL_interp_unfold_stepwise_sporadicon show ?thesis by simp
qed

text \<open>
  Negative atomic formulae are unfolded
  as the intersection of the stepwise interpretations.
\<close>
theorem TESL_interp_unfold_stepwise_negative_atoms:
  assumes \<open>\<not> positive_atom \<phi>\<close>
    shows \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> {Y. \<exists>n::nat. Y = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>}\<close>
proof (cases \<phi>)
  case SporadicOn thus ?thesis using assms by simp
next
  case TagRelation
    thus ?thesis using TESL_interp_unfold_stepwise_tagrelgen by simp
next
  case Implies
    thus ?thesis using TESL_interp_unfold_stepwise_implies by simp
next
  case ImpliesNot
    thus ?thesis using TESL_interp_unfold_stepwise_implies_not by simp
next
  case TimeDelayedBy
    thus ?thesis using TESL_interp_unfold_stepwise_timedelayed by simp
next
  case WeaklyPrecedes
    thus ?thesis
      using TESL_interp_unfold_stepwise_weakly_precedes by simp
next
  case StrictlyPrecedes
    thus ?thesis
      using TESL_interp_unfold_stepwise_strictly_precedes by simp
next
  case Kills
    thus ?thesis
      using TESL_interp_unfold_stepwise_kills by simp
qed

text \<open>
  Some useful lemmas for reasoning on properties of sequences.
\<close>
lemma forall_nat_expansion:
  \<open>(\<forall>n \<ge> (n\<^sub>0::nat). P n) = (P n\<^sub>0 \<and> (\<forall>n \<ge> Suc n\<^sub>0. P n))\<close>
proof -
  have \<open>(\<forall>n \<ge> (n\<^sub>0::nat). P n) = (\<forall>n. (n = n\<^sub>0 \<or> n > n\<^sub>0) \<longrightarrow> P n)\<close>
    using le_less by blast
  also have \<open>... = (P n\<^sub>0 \<and> (\<forall>n > n\<^sub>0. P n))\<close> by blast
  finally show ?thesis using Suc_le_eq by simp
qed

lemma exists_nat_expansion:
  \<open>(\<exists>n \<ge> (n\<^sub>0::nat). P n) = (P n\<^sub>0 \<or> (\<exists>n \<ge> Suc n\<^sub>0. P n))\<close>
proof -
  have \<open>(\<exists>n \<ge> (n\<^sub>0::nat). P n) = (\<exists>n. (n = n\<^sub>0 \<or> n > n\<^sub>0) \<and> P n)\<close>
    using le_less by blast
  also have \<open>... = (\<exists>n. (P n\<^sub>0) \<or> (n > n\<^sub>0 \<and> P n))\<close> by blast
  finally show ?thesis using Suc_le_eq by simp
qed

lemma forall_nat_set_suc:\<open>{x. \<forall>m \<ge> n. P x m} = {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
proof
  { fix x assume h:\<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>x \<in> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
    ultimately have \<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> by simp
  } thus \<open>{x. \<forall>m \<ge> n. P x m} \<subseteq> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close> ..
next
  { fix x  assume h:\<open>x \<in> {x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m}\<close>
    hence \<open>P x n\<close> by simp
    moreover from h have \<open>\<forall>m \<ge> Suc n. P x m\<close> by simp
    ultimately have \<open>\<forall>m \<ge> n. P x m\<close> using forall_nat_expansion by blast
    hence \<open>x \<in> {x. \<forall>m \<ge> n. P x m}\<close> by simp
  } thus \<open>{x. P x n} \<inter> {x. \<forall>m \<ge> Suc n. P x m} \<subseteq> {x. \<forall>m \<ge> n. P x m}\<close> ..
qed

lemma exists_nat_set_suc:\<open>{x. \<exists>m \<ge> n. P x m} = {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close>
proof
  { fix x assume h:\<open>x \<in> {x. \<exists>m \<ge> n. P x m}\<close>
    hence \<open>x \<in> {x. \<exists>m. (m = n \<or> m \<ge> Suc n) \<and> P x m}\<close>
      using Suc_le_eq antisym_conv2 by fastforce
    hence \<open>x \<in> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close> by blast
  } thus \<open>{x. \<exists>m \<ge> n. P x m} \<subseteq> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close> ..
next
  { fix x  assume h:\<open>x \<in> {x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m}\<close>
    hence \<open>x \<in> {x. \<exists>m \<ge> n. P x m}\<close> using Suc_leD by blast
  } thus \<open>{x. P x n} \<union> {x. \<exists>m \<ge> Suc n. P x m} \<subseteq> {x. \<exists>m \<ge> n. P x m}\<close> ..
qed

section \<open>Coinduction Unfolding Properties\<close>

text \<open>
  The following lemmas show how  to shorten a suffix, i.e. to unfold one instant 
  in the construction of a run. They correspond to the rules of the operational 
  semantics.
\<close>
lemma TESL_interp_stepwise_sporadicon_coind_unfold:
  \<open>\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
    \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m        \<comment> \<open>rule @{term sporadic_on_e2}\<close>
    \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>   \<comment> \<open>rule @{term sporadic_on_e1}\<close>
unfolding TESL_interpretation_atomic_stepwise.simps(1)
          symbolic_run_interpretation_primitive.simps(1,6)
using exists_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. hamlet (Rep_run \<rho> n K\<^sub>1)
                                     \<and> time (Rep_run \<rho> n K\<^sub>2) = \<tau>\<close>]
by (simp add: Collect_conj_eq)


lemma TESL_interp_stepwise_tagrel_coind_unfold:
  \<open>\<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =        \<comment> \<open>rule @{term tagrel_e}\<close>
     \<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
     \<inter> \<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. R (time ((Rep_run \<rho>) m K\<^sub>1), time ((Rep_run \<rho>) m K\<^sub>2))}
       = {\<rho>. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2))}
       \<inter> {\<rho>. \<forall>m\<ge>Suc n. R (time ((Rep_run \<rho>) m K\<^sub>1), time ((Rep_run \<rho>) m K\<^sub>2))}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. R (time ((Rep_run x) y K\<^sub>1),
                                       time ((Rep_run x) y K\<^sub>2))\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_implies_coind_unfold:
  \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (   \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                     \<comment> \<open>rule @{term implies_e1}\<close>
       \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)  \<comment> \<open>rule @{term implies_e2}\<close>
     \<inter> \<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> hamlet ((Rep_run \<rho>) m slave)}
        = {\<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave)}
        \<inter> {\<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master)
                     \<longrightarrow> hamlet ((Rep_run \<rho>) m slave)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. hamlet ((Rep_run x) y master)
                                \<longrightarrow> hamlet ((Rep_run x) y slave)\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_implies_not_coind_unfold:
  \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (    \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                       \<comment> \<open>rule @{term implies_not_e1}\<close>
        \<union> \<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> slave \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)  \<comment> \<open>rule @{term implies_not_e2}\<close>
     \<inter> \<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>m\<ge>n. hamlet ((Rep_run \<rho>) m master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) m slave)}
       = {\<rho>. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) n slave)}
          \<inter> {\<rho>. \<forall>m\<ge>Suc n. hamlet ((Rep_run \<rho>) m master)
                     \<longrightarrow> \<not> hamlet ((Rep_run \<rho>) m slave)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>x y. hamlet ((Rep_run x) y master)
                               \<longrightarrow> \<not>hamlet ((Rep_run x) y slave)\<close>] by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_timedelayed_coind_unfold:
  \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
     (     \<lbrakk> master \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m               \<comment> \<open>rule @{term timedelayed_e1}\<close>
        \<union> (\<lbrakk> master \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> measuring @ n \<oplus> \<delta>\<tau> \<Rightarrow> slave \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m))
                                             \<comment> \<open>rule @{term timedelayed_e2}\<close>
     \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?prop = \<open>\<lambda>\<rho> m. hamlet ((Rep_run \<rho>) m master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) m measuring) in
                  \<forall>p \<ge> m. first_time \<rho> measuring p (measured_time + \<delta>\<tau>)
                           \<longrightarrow> hamlet ((Rep_run \<rho>) p slave))\<close>
  have \<open>{\<rho>. \<forall>m \<ge> n. ?prop \<rho> m} = {\<rho>. ?prop \<rho> n} \<inter> {\<rho>. \<forall>m \<ge> Suc n. ?prop \<rho> m}\<close>
    using forall_nat_set_suc[of \<open>n\<close> ?prop] by blast
  also have \<open>... = {\<rho>. ?prop \<rho> n}
              \<inter> \<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  finally show ?thesis by auto
qed

lemma TESL_interp_stepwise_weakly_precedes_coind_unfold:
   \<open>\<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =                 \<comment> \<open>rule @{term weakly_precedes_e}\<close>
      \<lbrakk> (\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m 
      \<inter> \<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>p\<ge>n. (run_tick_count \<rho> K\<^sub>2 p) \<le> (run_tick_count \<rho> K\<^sub>1 p)}
         = {\<rho>. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count \<rho> K\<^sub>1 n)}
         \<inter> {\<rho>. \<forall>p\<ge>Suc n. (run_tick_count \<rho> K\<^sub>2 p) \<le> (run_tick_count \<rho> K\<^sub>1 p)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. (run_tick_count \<rho> K\<^sub>2 n)
                                  \<le> (run_tick_count \<rho> K\<^sub>1 n)\<close>]
    by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_strictly_precedes_coind_unfold:
   \<open>\<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =               \<comment> \<open>rule @{term strictly_precedes_e}\<close>
      \<lbrakk> (\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
      \<inter> \<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  have \<open>{\<rho>. \<forall>p\<ge>n. (run_tick_count \<rho> K\<^sub>2 p) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 p)}
         = {\<rho>. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n)}
         \<inter> {\<rho>. \<forall>p\<ge>Suc n. (run_tick_count \<rho> K\<^sub>2 p) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 p)}\<close>
    using forall_nat_set_suc[of \<open>n\<close> \<open>\<lambda>\<rho> n. (run_tick_count \<rho> K\<^sub>2 n)
                                  \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n)\<close>]
    by simp
  thus ?thesis by auto
qed

lemma TESL_interp_stepwise_kills_coind_unfold:
   \<open>\<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> =
      (   \<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m                        \<comment> \<open>rule @{term kills_e1}\<close>
        \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)    \<comment> \<open>rule @{term kills_e2}\<close>
      \<inter> \<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
proof -
  let ?kills = \<open>\<lambda>n \<rho>. \<forall>p\<ge>n. hamlet ((Rep_run \<rho>) p K\<^sub>1)
                             \<longrightarrow> (\<forall>m\<ge>p. \<not> hamlet ((Rep_run \<rho>) m K\<^sub>2))\<close>
  let ?ticks = \<open>\<lambda>n \<rho> c. hamlet ((Rep_run \<rho>) n c)\<close>
  let ?dead = \<open>\<lambda>n \<rho> c. \<forall>m \<ge> n. \<not>hamlet ((Rep_run \<rho>) m c)\<close>
  have \<open>\<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = {\<rho>. ?kills n \<rho>}\<close> by simp
  also have \<open>... = ({\<rho>. \<not> ?ticks n \<rho> K\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2})\<close>
  proof
    { fix \<rho>::\<open>'\<tau>::linordered_field run\<close>
      assume \<open>\<rho> \<in> {\<rho>. ?kills n \<rho>}\<close>
      hence \<open>?kills n \<rho>\<close> by simp
      hence \<open>(?ticks n \<rho> K\<^sub>1 \<and> ?dead n \<rho> K\<^sub>2) \<or> (\<not>?ticks n \<rho> K\<^sub>1 \<and> ?kills (Suc n) \<rho>)\<close>
        using Suc_leD by blast
      hence \<open>\<rho> \<in> ({\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2})
               \<union> ({\<rho>. \<not> ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>})\<close>
        by blast
    } thus \<open>{\<rho>. ?kills n \<rho>}
           \<subseteq> {\<rho>. \<not> ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>} 
            \<union> {\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2}\<close> by blast
  next
    { fix \<rho>::\<open>'\<tau>::linordered_field run\<close>
      assume \<open>\<rho> \<in> ({\<rho>. \<not> ?ticks n \<rho> K\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2})\<close>
      hence \<open>\<not> ?ticks n \<rho> K\<^sub>1 \<and> ?kills (Suc n) \<rho>
             \<or> ?ticks n \<rho> K\<^sub>1 \<and> ?dead n \<rho> K\<^sub>2\<close> by blast
      moreover have \<open>((\<not> ?ticks n \<rho> K\<^sub>1) \<and> (?kills (Suc n) \<rho>)) \<longrightarrow> ?kills n \<rho>\<close>
        using dual_order.antisym not_less_eq_eq by blast
      ultimately have \<open>?kills n \<rho> \<or> ?ticks n \<rho> K\<^sub>1 \<and> ?dead n \<rho> K\<^sub>2\<close> by blast
      hence \<open>?kills n \<rho>\<close> using le_trans by blast
    } thus \<open>({\<rho>. \<not> ?ticks n \<rho> K\<^sub>1}  \<inter> {\<rho>. ?kills (Suc n) \<rho>})
                 \<union> ({\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2})
          \<subseteq> {\<rho>. ?kills n \<rho>}\<close> by blast
  qed
  also have \<open>... = {\<rho>. \<not> ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?kills (Suc n) \<rho>}
                 \<union> {\<rho>. ?ticks n \<rho> K\<^sub>1} \<inter> {\<rho>. ?dead n \<rho> K\<^sub>2} \<inter> {\<rho>. ?kills (Suc n) \<rho>}\<close>
    using Collect_cong Collect_disj_eq by auto
  also have \<open>... = \<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                 \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                 \<inter> \<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  finally show ?thesis by blast
qed

text \<open>
  The stepwise interpretation of a TESL formula is the intersection of the
  interpretation of its atomic components.
\<close>
fun TESL_interpretation_stepwise
  ::\<open>'\<tau>::linordered_field TESL_formula \<Rightarrow> nat \<Rightarrow> '\<tau> run set\<close>
  (\<open>\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> _\<^esup>\<close>)
where
  \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = {\<rho>. True}\<close>
| \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>

lemma TESL_interpretation_stepwise_fixpoint:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>) ` set \<Phi>)\<close>
by (induction \<Phi>, simp, auto)

text \<open>
  The global interpretation of a TESL formula is its interpretation starting
  at the first instant.
\<close>
lemma TESL_interpretation_stepwise_zero:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>\<close>
by (induction \<phi>, simp+)

lemma TESL_interpretation_stepwise_zero':
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> 0\<^esup>\<close>
by (induction \<Phi>, simp, simp add: TESL_interpretation_stepwise_zero)

lemma TESL_interpretation_stepwise_cons_morph:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
by auto

theorem TESL_interp_stepwise_composition:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
by (induction \<Phi>\<^sub>1, simp, auto)

section \<open>Interpretation of configurations\<close>

text \<open>
  The interpretation of a configuration of the operational semantics abstract 
  machine is the intersection of:
  \<^item> the interpretation of its context (the past),
  \<^item> the interpretation of its present from the current instant,
  \<^item> the interpretation of its future from the next instant.
\<close>
fun HeronConf_interpretation
  ::\<open>'\<tau>::linordered_field config \<Rightarrow> '\<tau> run set\<close>          (\<open>\<lbrakk> _ \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close> 71)
where
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>

lemma HeronConf_interp_composition:
   \<open>\<lbrakk> \<Gamma>\<^sub>1, n \<turnstile> \<Psi>\<^sub>1 \<triangleright> \<Phi>\<^sub>1 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g \<inter> \<lbrakk> \<Gamma>\<^sub>2, n \<turnstile> \<Psi>\<^sub>2 \<triangleright> \<Phi>\<^sub>2 \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
     = \<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2), n \<turnstile> (\<Psi>\<^sub>1 @ \<Psi>\<^sub>2) \<triangleright> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
  using TESL_interp_stepwise_composition symrun_interp_expansion
by (simp add: TESL_interp_stepwise_composition
              symrun_interp_expansion inf_assoc inf_left_commute)

text \<open>
  When there are no remaining constraints on the present, the interpretation of
  a configuration is the same as the configuration at the next instant of its future.
  This corresponds to the introduction rule of the operational semantics.
\<close>
lemma HeronConf_interp_stepwise_instant_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> [] \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> \<Gamma>, Suc n \<turnstile> \<Phi> \<triangleright> [] \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
                 = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis by blast
qed

text \<open>
  The following lemmas use the unfolding properties of the stepwise denotational 
  semantics to give rewriting rules for the interpretation of configurations that
  match the elimination rules of the operational semantics.
\<close>
lemma HeronConf_interp_stepwise_sporadicon_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> \<Gamma>, n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 =  \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 =  \<lbrakk>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                  \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>(\<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
            \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>)
          = \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)\<close>
      using TESL_interp_stepwise_sporadicon_coind_unfold by blast
    hence \<open>\<lbrakk>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Down> n @ \<tau>) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            \<union> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
           = \<lbrakk>\<lbrakk> (K\<^sub>1 sporadic \<tau> on K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> by auto
    thus ?thesis by auto
  qed
qed

lemma HeronConf_interp_stepwise_tagrel_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
        \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
        \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (\<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                 \<inter> \<lbrakk>\<lbrakk> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
          \<inter> \<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> = \<lbrakk>\<lbrakk> (time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_tagrel_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma HeronConf_interp_stepwise_implies_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                =  \<lbrakk>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<Up> n) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                 \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have f1: \<open>(\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
                \<inter> \<lbrakk> K\<^sub>1 implies K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
              = \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      using TESL_interp_stepwise_implies_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    have \<open>\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>2 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
         = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by force
    hence \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>2 \<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
        \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using f1 by (simp add: inf_left_commute inf_assoc)
    thus ?thesis by (simp add: Int_Un_distrib2 inf_assoc)
  qed
qed

lemma HeronConf_interp_stepwise_implies_not_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies not K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 implies not K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                  = \<lbrakk>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> n) # \<Gamma>) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies not K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have f1: \<open>(\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
              \<inter> \<lbrakk> K\<^sub>1 implies not K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>
              \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)
              = \<lbrakk>\<lbrakk> (K\<^sub>1 implies not K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
      using TESL_interp_stepwise_implies_not_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    have \<open>\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>2 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
           = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
      by force
    then have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 implies not K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                    \<inter> \<lbrakk>\<lbrakk> (K\<^sub>2 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                    \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 implies not K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using f1 by (simp add: inf_left_commute inf_assoc)
    thus ?thesis by (simp add: Int_Un_distrib2 inf_assoc)
  qed
qed

lemma HeronConf_interp_stepwise_timedelayed_cases:
  \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
        \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have 1:\<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
         = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                 = \<lbrakk>\<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
      = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
        \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>)\<close>
      using 1 by blast
    hence \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
          = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
            \<inter> (\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> (\<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>))\<close>
      using TESL_interpretation_stepwise_cons_morph
            TESL_interp_stepwise_timedelayed_coind_unfold
    proof -
      have \<open>\<lbrakk>\<lbrakk> (K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            = (\<lbrakk> K\<^sub>1 \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> K\<^sub>1 \<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> K\<^sub>2 @ n \<oplus> \<delta>\<tau> \<Rightarrow> K\<^sub>3 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
            \<inter> \<lbrakk> K\<^sub>1 time-delayed by \<delta>\<tau> on K\<^sub>2 implies K\<^sub>3 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
        using TESL_interp_stepwise_timedelayed_coind_unfold
              TESL_interpretation_stepwise_cons_morph by blast
      then show ?thesis
        by (simp add: Int_assoc Int_left_commute)
    qed
    then show ?thesis by (simp add: inf_assoc inf_sup_distrib2)
  qed
qed

lemma HeronConf_interp_stepwise_weakly_precedes_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
      \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 weakly precedes K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>\<le> K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
            \<inter> \<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          = \<lbrakk>\<lbrakk> (K\<^sub>1 weakly precedes K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_weakly_precedes_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma HeronConf_interp_stepwise_strictly_precedes_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
      \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> (K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi> \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma>), n
                  \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (\<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y)) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
                \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 strictly precedes K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
  proof -
    have \<open>\<lbrakk> \<lceil>#\<^sup>\<le> K\<^sub>2 n, #\<^sup>< K\<^sub>1 n\<rceil> \<in> (\<lambda>(x,y). x\<le>y) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m
            \<inter> \<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
          = \<lbrakk>\<lbrakk> (K\<^sub>1 strictly precedes K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
      using TESL_interp_stepwise_strictly_precedes_coind_unfold
            TESL_interpretation_stepwise_cons_morph by blast
    thus ?thesis by auto
  qed
qed

lemma HeronConf_interp_stepwise_kills_cases:
   \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    = \<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
    \<union> \<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g\<close>
proof -
  have \<open>\<lbrakk> \<Gamma>, n \<turnstile> ((K\<^sub>1 kills K\<^sub>2) # \<Psi>) \<triangleright> \<Phi> \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
        = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 kills K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close>
    by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<not>\<Up> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (K\<^sub>1 \<not>\<Up> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 kills K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  moreover have \<open>\<lbrakk> ((K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma>), n \<turnstile> \<Psi> \<triangleright> ((K\<^sub>1 kills K\<^sub>2) # \<Phi>) \<rbrakk>\<^sub>c\<^sub>o\<^sub>n\<^sub>f\<^sub>i\<^sub>g
                = \<lbrakk>\<lbrakk> (K\<^sub>1 \<Up> n) # (K\<^sub>2 \<not>\<Up> \<ge> n) # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
                  \<inter> \<lbrakk>\<lbrakk> (K\<^sub>1 kills K\<^sub>2) # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup>\<close> by simp
  ultimately show ?thesis
    proof -
      have \<open>\<lbrakk>\<lbrakk> (K\<^sub>1 kills K\<^sub>2) # \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>
            = (\<lbrakk> (K\<^sub>1 \<not>\<Up> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<union> \<lbrakk> (K\<^sub>1 \<Up> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk> (K\<^sub>2 \<not>\<Up> \<ge> n) \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m)
              \<inter> \<lbrakk> (K\<^sub>1 kills K\<^sub>2) \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> Suc n\<^esup> \<inter> \<lbrakk>\<lbrakk> \<Psi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<^bsup>\<ge> n\<^esup>\<close>
        using TESL_interp_stepwise_kills_coind_unfold
              TESL_interpretation_stepwise_cons_morph by blast
      thus ?thesis by auto
    qed
qed

end
