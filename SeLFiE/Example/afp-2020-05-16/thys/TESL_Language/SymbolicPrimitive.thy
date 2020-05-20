chapter \<open>Symbolic Primitives for Building Runs\<close>

theory SymbolicPrimitive
  imports Run

begin

text\<open>
  We define here the primitive constraints on runs, towards which we translate
  TESL specifications in the operational semantics.
  These constraints refer to a specific symbolic run and can therefore access
  properties of the run at particular instants (for instance, the fact that a clock
  ticks at instant @{term \<open>n\<close>} of the run, or the time on a given clock at 
  that instant).

  In the previous chapters, we had no reference to particular instants of a run 
  because the TESL language should be invariant by stuttering in order to allow 
  the composition of specifications: adding an instant where no clock ticks to 
  a run that satisfies a formula should yield another run that satisfies the 
  same formula. However, when constructing runs that satisfy a formula, we
  need to be able to refer to the time or hamlet of a clock at a given instant.
\<close>

text\<open>
  Counter expressions are used to get the number of ticks of a clock up to 
  (strictly or not) a given instant index.
\<close>
datatype cnt_expr =
  TickCountLess \<open>clock\<close> \<open>instant_index\<close> (\<open>#\<^sup><\<close>)
| TickCountLeq \<open>clock\<close> \<open>instant_index\<close>  (\<open>#\<^sup>\<le>\<close>)

subsection\<open> Symbolic Primitives for Runs \<close>

text\<open>
  Tag values are used to refer to the time on a clock at a given instant index.
\<close>
datatype tag_val =
  TSchematic \<open>clock * instant_index\<close> (\<open>\<tau>\<^sub>v\<^sub>a\<^sub>r\<close>)

datatype '\<tau> constr =
\<comment> \<open>@{term \<open>c \<Down> n @ \<tau>\<close>} constrains clock @{term \<open>c\<close>} to have time @{term \<open>\<tau>\<close>}
    at instant @{term \<open>n\<close>} of the run.\<close>
  Timestamp     \<open>clock\<close>   \<open>instant_index\<close> \<open>'\<tau> tag_const\<close>         (\<open>_ \<Down> _ @ _\<close>)
\<comment> \<open>@{term \<open>m @ n \<oplus> \<delta>t \<Rightarrow> s\<close>} constrains clock @{term \<open>s\<close>} to tick at the
    first instant at which the time on @{term \<open>m\<close>} has increased by @{term \<open>\<delta>t\<close>}
    from the value it had at instant @{term \<open>n\<close>} of the run.\<close>
| TimeDelay     \<open>clock\<close>   \<open>instant_index\<close> \<open>'\<tau> tag_const\<close> \<open>clock\<close> (\<open>_ @ _ \<oplus> _ \<Rightarrow> _\<close>)
\<comment> \<open>@{term \<open>c \<Up> n\<close>} constrains clock @{term \<open>c\<close>} to tick
    at instant @{term \<open>n\<close>} of the run.\<close>
| Ticks         \<open>clock\<close>   \<open>instant_index\<close>                        (\<open>_ \<Up> _\<close>)
\<comment> \<open>@{term \<open>c \<not>\<Up> n\<close>} constrains clock @{term \<open>c\<close>} not to tick
    at instant @{term \<open>n\<close>} of the run.\<close>
| NotTicks      \<open>clock\<close>   \<open>instant_index\<close>                        (\<open>_ \<not>\<Up> _\<close>)
\<comment> \<open>@{term \<open>c \<not>\<Up> < n\<close>} constrains clock @{term \<open>c\<close>} not to tick
    before instant @{term \<open>n\<close>} of the run.\<close>
| NotTicksUntil \<open>clock\<close>   \<open>instant_index\<close>                        (\<open>_ \<not>\<Up> < _\<close>)
\<comment> \<open>@{term \<open>c \<not>\<Up> \<ge> n\<close>} constrains clock @{term \<open>c\<close>} not to tick
    at and after instant @{term \<open>n\<close>} of the run.\<close>
| NotTicksFrom  \<open>clock\<close>   \<open>instant_index\<close>                        (\<open>_ \<not>\<Up> \<ge> _\<close>)
\<comment> \<open>@{term \<open>\<lfloor>\<tau>\<^sub>1, \<tau>\<^sub>2\<rfloor> \<in> R\<close>} constrains tag variables @{term \<open>\<tau>\<^sub>1\<close>} and  @{term \<open>\<tau>\<^sub>2\<close>} 
    to be in relation @{term \<open>R\<close>}.\<close>
| TagArith      \<open>tag_val\<close> \<open>tag_val\<close> \<open>('\<tau> tag_const \<times> '\<tau> tag_const) \<Rightarrow> bool\<close> (\<open>\<lfloor>_, _\<rfloor> \<in> _\<close>)
\<comment> \<open>@{term \<open>\<lceil>k\<^sub>1, k\<^sub>2\<rceil> \<in> R\<close>} constrains counter expressions @{term \<open>k\<^sub>1\<close>} and  @{term \<open>k\<^sub>2\<close>} 
    to be in relation @{term \<open>R\<close>}.\<close>
| TickCntArith  \<open>cnt_expr\<close> \<open>cnt_expr\<close> \<open>(nat \<times> nat) \<Rightarrow> bool\<close>      (\<open>\<lceil>_, _\<rceil> \<in> _\<close>)
\<comment> \<open>@{term \<open>k\<^sub>1 \<preceq> k\<^sub>2\<close>} constrains counter expression @{term \<open>k\<^sub>1\<close>} to be less or equal 
    to counter expression @{term \<open>k\<^sub>2\<close>}.\<close>
| TickCntLeq    \<open>cnt_expr\<close> \<open>cnt_expr\<close>                            (\<open>_ \<preceq> _\<close>)

type_synonym '\<tau> system = \<open>'\<tau> constr list\<close>


text \<open>
  The abstract machine has configurations composed of:
  \<^item> the past @{term\<open>\<Gamma>\<close>}, which captures choices that have already be made as a 
    list of symbolic primitive constraints on the run;
  \<^item> the current index @{term \<open>n\<close>}, which is the index of the present instant;
  \<^item> the present @{term\<open>\<Psi>\<close>}, which captures the formulae that must be satisfied
    in the current instant;
  \<^item> the future @{term\<open>\<Phi>\<close>}, which captures the constraints on the future of the run.
\<close>
type_synonym '\<tau> config =
                \<open>'\<tau> system * instant_index * '\<tau> TESL_formula * '\<tau> TESL_formula\<close>


section \<open>Semantics of Primitive Constraints \<close>

text\<open>
  The semantics of the primitive constraints is defined in a way similar to
  the semantics of TESL formulae.
\<close>
fun counter_expr_eval :: \<open>('\<tau>::linordered_field) run \<Rightarrow> cnt_expr \<Rightarrow> nat\<close>
  (\<open>\<lbrakk> _ \<turnstile> _ \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r\<close>)
where
  \<open>\<lbrakk> \<rho> \<turnstile> #\<^sup>< clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count_strictly \<rho> clk indx\<close>
| \<open>\<lbrakk> \<rho> \<turnstile> #\<^sup>\<le> clk indx \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r = run_tick_count \<rho> clk indx\<close>


fun symbolic_run_interpretation_primitive
  ::\<open>('\<tau>::linordered_field) constr \<Rightarrow> '\<tau> run set\<close> (\<open>\<lbrakk> _ \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>)
where
  \<open>\<lbrakk> K \<Up> n  \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m     = {\<rho>. hamlet ((Rep_run \<rho>) n K) }\<close>
| \<open>\<lbrakk> K @ n\<^sub>0 \<oplus> \<delta>t \<Rightarrow> K' \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m =
                  {\<rho>. \<forall>n \<ge> n\<^sub>0. first_time \<rho> K n (time ((Rep_run \<rho>) n\<^sub>0 K) + \<delta>t)
                               \<longrightarrow> hamlet ((Rep_run \<rho>) n K')}\<close>
| \<open>\<lbrakk> K \<not>\<Up> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m     = {\<rho>. \<not>hamlet ((Rep_run \<rho>) n K) }\<close>
| \<open>\<lbrakk> K \<not>\<Up> < n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m   = {\<rho>. \<forall>i < n. \<not> hamlet ((Rep_run \<rho>) i K)}\<close>
| \<open>\<lbrakk> K \<not>\<Up> \<ge> n \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m   = {\<rho>. \<forall>i \<ge> n. \<not> hamlet ((Rep_run \<rho>) i K) }\<close>
| \<open>\<lbrakk> K \<Down> n @ \<tau> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = {\<rho>. time ((Rep_run \<rho>) n K) = \<tau> }\<close>
| \<open>\<lbrakk> \<lfloor>\<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>1, n\<^sub>1), \<tau>\<^sub>v\<^sub>a\<^sub>r(K\<^sub>2, n\<^sub>2)\<rfloor> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m =
    { \<rho>. R (time ((Rep_run \<rho>) n\<^sub>1 K\<^sub>1), time ((Rep_run \<rho>) n\<^sub>2 K\<^sub>2)) }\<close>
| \<open>\<lbrakk> \<lceil>e\<^sub>1, e\<^sub>2\<rceil> \<in> R \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. R (\<lbrakk> \<rho> \<turnstile> e\<^sub>1 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r, \<lbrakk> \<rho> \<turnstile> e\<^sub>2 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r) }\<close>
| \<open>\<lbrakk> cnt_e\<^sub>1 \<preceq> cnt_e\<^sub>2 \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = { \<rho>. \<lbrakk> \<rho> \<turnstile> cnt_e\<^sub>1 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r \<le> \<lbrakk> \<rho> \<turnstile> cnt_e\<^sub>2 \<rbrakk>\<^sub>c\<^sub>n\<^sub>t\<^sub>e\<^sub>x\<^sub>p\<^sub>r }\<close>

text\<open>
  The composition of primitive constraints is their conjunction, and we get the
  set of satisfying runs by intersection.
\<close>
fun symbolic_run_interpretation
  ::\<open>('\<tau>::linordered_field) constr list \<Rightarrow> ('\<tau>::linordered_field) run set\<close>
  (\<open>\<lbrakk>\<lbrakk> _ \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>)
where
  \<open>\<lbrakk>\<lbrakk> [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = {\<rho>. True }\<close>
| \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>

lemma symbolic_run_interp_cons_morph:
  \<open>\<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by auto

definition consistent_context :: \<open>('\<tau>::linordered_field) constr list \<Rightarrow> bool\<close>
where 
  \<open>consistent_context \<Gamma> \<equiv> ( \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<noteq> {}) \<close>

subsection \<open>Defining a method for witness construction\<close>

text\<open>
  In order to build a run, we can start from an initial run in which no clock 
  ticks and the time is always 0 on any clock.
\<close>
abbreviation initial_run :: \<open>('\<tau>::linordered_field) run\<close> (\<open>\<rho>\<^sub>\<odot>\<close>) where
  \<open>\<rho>\<^sub>\<odot> \<equiv> Abs_run ((\<lambda>_ _. (False, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)) ::nat \<Rightarrow> clock \<Rightarrow> (bool \<times> '\<tau> tag_const))\<close>

text\<open>
  To help avoiding that time flows backward, setting the time on a clock at a given 
  instant sets it for the future instants too.
\<close>
fun time_update
  :: \<open>nat \<Rightarrow> clock \<Rightarrow> ('\<tau>::linordered_field) tag_const \<Rightarrow> (nat \<Rightarrow> '\<tau> instant)
      \<Rightarrow> (nat \<Rightarrow> '\<tau> instant)\<close>
where
  \<open>time_update n K \<tau> \<rho> = (\<lambda>n' K'. if K = K' \<and> n \<le> n'
                                  then (hamlet (\<rho> n K), \<tau>)
                                  else \<rho> n' K')\<close>


section \<open>Rules and properties of consistence\<close>

lemma context_consistency_preservationI:
  \<open>consistent_context ((\<gamma>::('\<tau>::linordered_field) constr)#\<Gamma>) \<Longrightarrow> consistent_context \<Gamma>\<close>
unfolding consistent_context_def by auto

\<comment> \<open>This is very restrictive\<close>
inductive context_independency
  ::\<open>('\<tau>::linordered_field) constr \<Rightarrow> '\<tau> constr list \<Rightarrow> bool\<close> (\<open>_ \<bowtie> _\<close>)
where
  NotTicks_independency:
  \<open>(K \<Up> n) \<notin> set \<Gamma> \<Longrightarrow> (K \<not>\<Up> n) \<bowtie> \<Gamma>\<close>
| Ticks_independency:
  \<open>(K \<not>\<Up> n) \<notin> set \<Gamma> \<Longrightarrow> (K \<Up> n) \<bowtie> \<Gamma>\<close>
| Timestamp_independency:
  \<open>(\<nexists>\<tau>'. \<tau>' = \<tau> \<and> (K \<Down> n @ \<tau>) \<in> set \<Gamma>) \<Longrightarrow> (K \<Down> n @ \<tau>) \<bowtie> \<Gamma>\<close>


section\<open>Major Theorems\<close>
subsection \<open>Interpretation of a context\<close>

text\<open>
  The interpretation of a context is the intersection of the interpretation 
  of its components.
\<close>
theorem symrun_interp_fixpoint:
  \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (induction \<Gamma>, simp+)

subsection \<open>Expansion law\<close>
text \<open>Similar to the expansion laws of lattices\<close>

theorem symrun_interp_expansion:
  \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (induction \<Gamma>\<^sub>1, simp, auto)

section \<open>Equations for the interpretation of symbolic primitives\<close> 
subsection \<open>General laws\<close>

lemma symrun_interp_assoc:
  \<open>\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>3 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by auto

lemma symrun_interp_commute:
  \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (simp add: symrun_interp_expansion inf_sup_aci(1))

lemma symrun_interp_left_commute:
  \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>2 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>3) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
unfolding symrun_interp_expansion by auto

lemma symrun_interp_idem:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
using symrun_interp_expansion by auto

lemma symrun_interp_left_idem:
  \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
using symrun_interp_expansion by auto

lemma symrun_interp_right_idem:
  \<open>\<lbrakk>\<lbrakk> (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
unfolding symrun_interp_expansion by auto

lemmas symrun_interp_aci =  symrun_interp_commute
                            symrun_interp_assoc
                            symrun_interp_left_commute
                            symrun_interp_left_idem

\<comment> \<open>Identity element\<close>
lemma symrun_interp_neutral1:
  \<open>\<lbrakk>\<lbrakk> [] @ \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by simp

lemma symrun_interp_neutral2:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> @ [] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by simp

subsection \<open>Decreasing interpretation of symbolic primitives\<close>

text\<open>
  Adding constraints to a context reduces the number of satisfying runs.
\<close>
lemma TESL_sem_decreases_head:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by simp

lemma TESL_sem_decreases_tail:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma> @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (simp add: symrun_interp_expansion)

text\<open>
  Adding a constraint that is already in the context does not change the
  interpretation of the context.
\<close>
lemma symrun_interp_formula_stuttering:
  assumes \<open>\<gamma> \<in> set \<Gamma>\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
proof -
  have \<open>\<gamma> # \<Gamma> = [\<gamma>] @ \<Gamma>\<close> by simp
  hence \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
    using symrun_interp_expansion by simp
  thus ?thesis using assms symrun_interp_fixpoint by fastforce
qed


text\<open>
  Removing duplicate constraints from a context does not change the
  interpretation of the context.
\<close>
lemma symrun_interp_remdups_absorb:
  \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> remdups \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
proof (induction \<Gamma>)
  case Cons
    thus ?case using symrun_interp_formula_stuttering by auto
qed simp

text\<open>
  Two identical sets of constraints have the same interpretation,
  the order in the context does not matter.
\<close>
lemma symrun_interp_set_lifting:
  assumes \<open>set \<Gamma> = set \<Gamma>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
proof -     
  have \<open>set (remdups \<Gamma>) = set (remdups \<Gamma>')\<close>
    by (simp add: assms)
  moreover have fxpnt\<Gamma>: \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
    by (simp add: symrun_interp_fixpoint)
  moreover have fxpnt\<Gamma>': \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>') = \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
    by (simp add: symrun_interp_fixpoint)
  moreover have \<open>\<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>) = \<Inter> ((\<lambda>\<gamma>. \<lbrakk> \<gamma> \<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m) ` set \<Gamma>')\<close>
    by (simp add: assms)
  ultimately show ?thesis using symrun_interp_remdups_absorb by auto
qed

text\<open>
  The interpretation of contexts is contravariant with regard to set inclusion.
\<close>
theorem symrun_interp_decreases_setinc:
  assumes \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
proof -
  obtain \<Gamma>\<^sub>r where decompose: \<open>set (\<Gamma> @ \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using assms by auto
  hence \<open>set (\<Gamma> @ \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using assms by blast
  moreover have \<open>(set \<Gamma>) \<union> (set \<Gamma>\<^sub>r) = set \<Gamma>'\<close> using assms decompose by auto
  moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
    using symrun_interp_set_lifting decompose by blast
  moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> @ \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
    by (simp add: symrun_interp_expansion)
  moreover have \<open>\<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<inter> \<lbrakk>\<lbrakk> \<Gamma>\<^sub>r \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> by simp
  ultimately show ?thesis by simp
qed

lemma symrun_interp_decreases_add_head:
  assumes \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<gamma> # \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<gamma> # \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
using symrun_interp_decreases_setinc assms by auto

lemma symrun_interp_decreases_add_tail:
  assumes \<open>set \<Gamma> \<subseteq> set \<Gamma>'\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Gamma> @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<supseteq> \<lbrakk>\<lbrakk> \<Gamma>' @ [\<gamma>] \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
proof -
  from symrun_interp_decreases_setinc[OF assms] have \<open>\<lbrakk>\<lbrakk> \<Gamma>' \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m \<subseteq> \<lbrakk>\<lbrakk> \<Gamma> \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close> .
  thus ?thesis by (simp add: symrun_interp_expansion dual_order.trans)
qed

lemma symrun_interp_absorb1:
  assumes \<open>set \<Gamma>\<^sub>1 \<subseteq> set \<Gamma>\<^sub>2\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
by (simp add: Int_absorb1 symrun_interp_decreases_setinc
                          symrun_interp_expansion assms)

lemma symrun_interp_absorb2:
  assumes \<open>set \<Gamma>\<^sub>2 \<subseteq> set \<Gamma>\<^sub>1\<close>
    shows \<open>\<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m = \<lbrakk>\<lbrakk> \<Gamma>\<^sub>1 \<rbrakk>\<rbrakk>\<^sub>p\<^sub>r\<^sub>i\<^sub>m\<close>
using symrun_interp_absorb1 symrun_interp_commute assms by blast

end
