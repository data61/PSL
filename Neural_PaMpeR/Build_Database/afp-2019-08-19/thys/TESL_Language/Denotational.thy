chapter \<open>Denotational Semantics\<close>

theory Denotational
imports
    TESL
    Run

begin
text\<open>
  The denotational semantics maps TESL formulae to sets of satisfying runs.
  Firstly, we define the semantics of atomic formulae (basic constructs of the 
  TESL language), then we define the semantics of compound formulae as the
  intersection of the semantics of their components: a run must satisfy all
  the individual formulae of a compound formula.
\<close>
section \<open>Denotational interpretation for atomic TESL formulae\<close>
(*<*)
consts dummyT0 ::\<open>'\<tau> tag_const\<close>
consts dummyDeltaT ::\<open>'\<tau> tag_const\<close>

notation dummyT0     (\<open>t\<^sub>0\<close>)
notation dummyDeltaT (\<open>\<delta>t\<close>)
(*>*)

fun TESL_interpretation_atomic
    :: \<open>('\<tau>::linordered_field) TESL_atomic \<Rightarrow> '\<tau> run set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>)
where
  \<comment> \<open>@{term \<open>K\<^sub>1 sporadic \<tau> on K\<^sub>2\<close>} means that @{term \<open>K\<^sub>1\<close>} should tick at an 
      instant where the time on @{term \<open>K\<^sub>2\<close>} is @{term \<open>\<tau>\<close>}.\<close>
    \<open>\<lbrakk> K\<^sub>1 sporadic \<tau> on K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<exists>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1) \<and> time ((Rep_run \<rho>) n K\<^sub>2) = \<tau>}\<close>
  \<comment> \<open>@{term \<open>time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R\<close>} means that at each instant, the time 
      on @{term \<open>K\<^sub>1\<close>} and the time on @{term \<open>K\<^sub>2\<close>} are in relation~@{term \<open>R\<close>}.\<close>
  | \<open>\<lbrakk> time-relation \<lfloor>K\<^sub>1, K\<^sub>2\<rfloor> \<in> R \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. R (time ((Rep_run \<rho>) n K\<^sub>1), time ((Rep_run \<rho>) n K\<^sub>2))}\<close>
  \<comment> \<open>@{term \<open>master implies slave\<close>} means that at each instant at which 
      @{term \<open>master\<close>} ticks, @{term \<open>slave\<close>} also ticks.\<close>
  | \<open>\<lbrakk> master implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> hamlet ((Rep_run \<rho>) n slave)}\<close>
  \<comment> \<open>@{term \<open>master implies not slave\<close>} means that at each instant at which 
      @{term \<open>master\<close>} ticks, @{term \<open>slave\<close>} does not tick.\<close>
  | \<open>\<lbrakk> master implies not slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n master) \<longrightarrow> \<not>hamlet ((Rep_run \<rho>) n slave)}\<close>
  \<comment> \<open>@{term \<open>master time-delayed by \<delta>\<tau> on measuring implies slave\<close>} means that 
      at each instant at which  @{term \<open>master\<close>} ticks, @{term \<open>slave\<close>} will
      tick after a delay @{term \<open>\<delta>\<tau>\<close>} measured on the time scale 
      of @{term \<open>measuring\<close>}.\<close>
  | \<open>\<lbrakk> master time-delayed by \<delta>\<tau> on measuring implies slave \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
    \<comment> \<open>
      When master ticks, let's call @{term \<open>t\<^sub>0\<close>} the current date on measuring. Then, 
      at the first instant when the date on measuring is @{term \<open>t\<^sub>0+\<delta>t\<close>}, 
      slave has to tick.
    \<close>
        {\<rho>. \<forall>n. hamlet ((Rep_run \<rho>) n master) \<longrightarrow>
                 (let measured_time = time ((Rep_run \<rho>) n measuring) in
                  \<forall>m \<ge> n.  first_time \<rho> measuring m (measured_time + \<delta>\<tau>)
                            \<longrightarrow> hamlet ((Rep_run \<rho>) m slave)
                 )
        }\<close>
  \<comment> \<open>@{term \<open>K\<^sub>1 weakly precedes K\<^sub>2\<close>} means that each tick on @{term \<open>K\<^sub>2\<close>}
        must be preceded by or coincide with at least one tick on @{term \<open>K\<^sub>1\<close>}.
        Therefore, at each instant @{term \<open>n\<close>}, the number of ticks on @{term \<open>K\<^sub>2\<close>} 
        must be less or equal to the number of ticks on @{term \<open>K\<^sub>1\<close>}.\<close>
  | \<open>\<lbrakk> K\<^sub>1 weakly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count \<rho> K\<^sub>1 n)}\<close>
  \<comment> \<open>@{term \<open>K\<^sub>1 strictly precedes K\<^sub>2\<close>} means that each tick on @{term \<open>K\<^sub>2\<close>}
        must be preceded by at least one tick on @{term \<open>K\<^sub>1\<close>} at a previous instant.
        Therefore, at each instant n, the number of ticks on @{term \<open>K\<^sub>2\<close>}
        must be less or equal to the number of ticks on @{term \<open>K\<^sub>1\<close>} 
        at instant n - 1.\<close>
  | \<open>\<lbrakk> K\<^sub>1 strictly precedes K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. (run_tick_count \<rho> K\<^sub>2 n) \<le> (run_tick_count_strictly \<rho> K\<^sub>1 n)}\<close>
  \<comment> \<open>@{term \<open>K\<^sub>1 kills K\<^sub>2\<close>} means that when @{term \<open>K\<^sub>1\<close>} ticks, @{term \<open>K\<^sub>2\<close>}
        cannot tick and is not allowed to tick at any further instant.\<close>
  | \<open>\<lbrakk> K\<^sub>1 kills K\<^sub>2 \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L =
        {\<rho>. \<forall>n::nat. hamlet ((Rep_run \<rho>) n K\<^sub>1)
                        \<longrightarrow> (\<forall>m\<ge>n. \<not> hamlet ((Rep_run \<rho>) m K\<^sub>2))}\<close>

section \<open>Denotational interpretation for TESL formulae\<close>

text\<open>
  To satisfy a formula, a run has to satisfy the conjunction of its atomic 
  formulae. Therefore, the interpretation of a formula is the intersection
  of the interpretations of its components.
\<close>
fun TESL_interpretation :: \<open>('\<tau>::linordered_field) TESL_formula \<Rightarrow> '\<tau> run set\<close>
  (\<open>\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>)
where
  \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = {_. True}\<close>
| \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>

lemma TESL_interpretation_homo:
  \<open>\<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by simp

subsection \<open>Image interpretation lemma\<close>

theorem TESL_interpretation_image:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>)\<close>
by (induction \<Phi>, simp+)

subsection \<open>Expansion law\<close>
text \<open>Similar to the expansion laws of lattices.\<close>

theorem TESL_interp_homo_append:
  \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by (induction \<Phi>\<^sub>1, simp, auto)

section \<open>Equational laws for the denotation of TESL formulae\<close>

lemma TESL_interp_assoc:
  \<open>\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by auto

lemma TESL_interp_commute:
  shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by (simp add: TESL_interp_homo_append inf_sup_aci(1))

lemma TESL_interp_left_commute:
  \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>2 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
unfolding TESL_interp_homo_append by auto

lemma TESL_interp_idem:
  \<open>\<lbrakk>\<lbrakk> \<Phi> @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using TESL_interp_homo_append by auto

lemma TESL_interp_left_idem:
  \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using TESL_interp_homo_append by auto

lemma TESL_interp_right_idem:
  \<open>\<lbrakk>\<lbrakk> (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
unfolding TESL_interp_homo_append by auto

lemmas TESL_interp_aci = TESL_interp_commute
                         TESL_interp_assoc
                         TESL_interp_left_commute
                         TESL_interp_left_idem

text \<open>The empty formula is the identity element.\<close>
lemma TESL_interp_neutral1:
  \<open>\<lbrakk>\<lbrakk> [] @ \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by simp

lemma TESL_interp_neutral2:
  \<open>\<lbrakk>\<lbrakk> \<Phi> @ [] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by simp

section \<open>Decreasing interpretation of TESL formulae\<close>
text\<open>
  Adding constraints to a TESL formula reduces the number of satisfying runs.
\<close>
lemma TESL_sem_decreases_head:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by simp

lemma TESL_sem_decreases_tail:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by (simp add: TESL_interp_homo_append)

text \<open>
  Repeating a formula in a specification does not change the specification.
\<close>
lemma TESL_interp_formula_stuttering:
  assumes \<open>\<phi> \<in> set \<Phi>\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  have \<open>\<phi> # \<Phi> = [\<phi>] @ \<Phi>\<close> by simp
  hence \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    using TESL_interp_homo_append by simp
  thus ?thesis using assms TESL_interpretation_image by fastforce
qed

text \<open>
  Removing duplicate formulae in a specification does not change the specification.
\<close>
lemma TESL_interp_remdups_absorb:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> remdups \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof (induction \<Phi>)
  case Cons
    thus ?case using TESL_interp_formula_stuttering by auto
qed simp

text \<open>
  Specifications that contain the same formulae have the same semantics.
\<close>
lemma TESL_interp_set_lifting:
  assumes \<open>set \<Phi> = set \<Phi>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -     
  have \<open>set (remdups \<Phi>) = set (remdups \<Phi>')\<close>
    by (simp add: assms)
  moreover have fxpnt\<Phi>: \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    by (simp add: TESL_interpretation_image)
  moreover have fxpnt\<Phi>': \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>') = \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    by (simp add: TESL_interpretation_image)
  moreover have \<open>\<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>) = \<Inter> ((\<lambda>\<phi>. \<lbrakk> \<phi> \<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L) ` set \<Phi>')\<close>
    by (simp add: assms)
  ultimately show ?thesis using TESL_interp_remdups_absorb by auto
qed

text \<open>
  The semantics of specifications is contravariant with respect to their inclusion.
\<close>
theorem TESL_interp_decreases_setinc:
  assumes \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  obtain \<Phi>\<^sub>r where decompose: \<open>set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'\<close> using assms by auto
  hence \<open>set (\<Phi> @ \<Phi>\<^sub>r) = set \<Phi>'\<close> using assms by blast
  moreover have \<open>(set \<Phi>) \<union> (set \<Phi>\<^sub>r) = set \<Phi>'\<close>
    using assms decompose by auto
  moreover have \<open>\<lbrakk>\<lbrakk> \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    using TESL_interp_set_lifting decompose by blast
  moreover have \<open>\<lbrakk>\<lbrakk> \<Phi> @ \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
    by (simp add: TESL_interp_homo_append)
  moreover have \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> \<Phi>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close> by simp
  ultimately show ?thesis by simp
qed

lemma TESL_interp_decreases_add_head:
  assumes \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<phi> # \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<phi> # \<Phi>' \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using assms TESL_interp_decreases_setinc by auto

lemma TESL_interp_decreases_add_tail:
  assumes \<open>set \<Phi> \<subseteq> set \<Phi>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Phi> @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<supseteq> \<lbrakk>\<lbrakk> \<Phi>' @ [\<phi>] \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using TESL_interp_decreases_setinc[OF assms] 
  by (simp add: TESL_interpretation_image dual_order.trans)

lemma TESL_interp_absorb1:
  assumes \<open>set \<Phi>\<^sub>1 \<subseteq> set \<Phi>\<^sub>2\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
by (simp add: Int_absorb1 TESL_interp_decreases_setinc
                          TESL_interp_homo_append assms)

lemma TESL_interp_absorb2:
  assumes \<open>set \<Phi>\<^sub>2 \<subseteq> set \<Phi>\<^sub>1\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Phi>\<^sub>1 @ \<Phi>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using TESL_interp_absorb1 TESL_interp_commute assms by blast

section \<open>Some special cases\<close>

lemma NoSporadic_stable [simp]:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<subseteq> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
proof -
  from filter_is_subset have \<open>set (NoSporadic \<Phi>) \<subseteq> set \<Phi>\<close> .
  from TESL_interp_decreases_setinc[OF this] show ?thesis .
qed

lemma NoSporadic_idem [simp]:
  \<open>\<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L \<inter> \<lbrakk>\<lbrakk> NoSporadic \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L = \<lbrakk>\<lbrakk> \<Phi> \<rbrakk>\<rbrakk>\<^sub>T\<^sub>E\<^sub>S\<^sub>L\<close>
using NoSporadic_stable by blast

lemma NoSporadic_setinc:
  \<open>set (NoSporadic \<Phi>) \<subseteq> set \<Phi>\<close>
by (rule filter_is_subset)

(*<*)
no_notation dummyT0    (\<open>t\<^sub>0\<close>)
no_notation dummyDeltaT (\<open>\<delta>t\<close>)
(*>*)

end
