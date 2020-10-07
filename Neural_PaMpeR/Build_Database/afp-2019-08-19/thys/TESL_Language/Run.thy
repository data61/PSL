section \<open> Defining Runs \<close>

theory Run
imports TESL
      
begin
text \<open>
  Runs are sequences of instants, and each instant maps a clock to a pair 
  @{term \<open>(h, t)\<close>} where @{term \<open>h\<close>} indicates whether the clock ticks or not, 
  and @{term \<open>t\<close>} is the current time on this clock.
  The first element of the pair is called the \<^emph>\<open>hamlet\<close> of the clock (to tick or 
  not to tick), the second element is called the \<^emph>\<open>time\<close>.
\<close>

abbreviation hamlet where \<open>hamlet \<equiv> fst\<close>
abbreviation time   where \<open>time \<equiv> snd\<close>

type_synonym '\<tau> instant = \<open>clock \<Rightarrow> (bool \<times> '\<tau> tag_const)\<close>

text\<open>
  Runs have the additional constraint that time cannot go backwards on any clock
  in the sequence of instants.
  Therefore, for any clock, the time projection of a run is monotonous.
\<close>
typedef (overloaded) '\<tau>::linordered_field run =
  \<open>{ \<rho>::nat \<Rightarrow> '\<tau> instant. \<forall>c. mono (\<lambda>n. time (\<rho> n c)) }\<close>
proof
  show \<open>(\<lambda>_ _. (True, \<tau>\<^sub>c\<^sub>s\<^sub>t 0)) \<in> {\<rho>. \<forall>c. mono (\<lambda>n. time (\<rho> n c))}\<close> 
    unfolding mono_def by blast
qed

lemma Abs_run_inverse_rewrite:
  \<open>\<forall>c. mono (\<lambda>n. time (\<rho> n c)) \<Longrightarrow> Rep_run (Abs_run \<rho>) = \<rho>\<close>
by (simp add: Abs_run_inverse)

text \<open>
  A \<^emph>\<open>dense\<close> run is a run in which something happens (at least one clock ticks) 
  at every instant.
\<close>
definition \<open>dense_run \<rho> \<equiv> (\<forall>n. \<exists>c. hamlet ((Rep_run \<rho>) n c))\<close>

text\<open>
  @{term \<open>run_tick_count \<rho> K n\<close>} counts the number of ticks on clock @{term \<open>K\<close>} 
  in the interval \<^verbatim>\<open>[0, n]\<close> of run @{term \<open>\<rho>\<close>}.
\<close>
fun run_tick_count :: \<open>('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
  (\<open>#\<^sub>\<le> _ _ _\<close>)
where
  \<open>(#\<^sub>\<le> \<rho> K 0)       = (if hamlet ((Rep_run \<rho>) 0 K)
                       then 1
                       else 0)\<close>
| \<open>(#\<^sub>\<le> \<rho> K (Suc n)) = (if hamlet ((Rep_run \<rho>) (Suc n) K)
                       then 1 + (#\<^sub>\<le> \<rho> K n)
                       else (#\<^sub>\<le> \<rho> K n))\<close>

text\<open>
  @{term \<open>run_tick_count_strictly \<rho> K n\<close>} counts the number of ticks on
  clock @{term \<open>K\<close>} in the interval \<^verbatim>\<open>[0, n[\<close> of run @{term \<open>\<rho>\<close>}.
\<close>
fun run_tick_count_strictly :: \<open>('\<tau>::linordered_field) run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> nat\<close>
  (\<open>#\<^sub>< _ _ _\<close>)
where
  \<open>(#\<^sub>< \<rho> K 0)       = 0\<close>
| \<open>(#\<^sub>< \<rho> K (Suc n)) = #\<^sub>\<le> \<rho> K n\<close>

text\<open>
  @{term \<open>first_time \<rho> K n \<tau>\<close>} tells whether instant @{term \<open>n\<close>} in run @{term\<open>\<rho>\<close>}
  is the first one where the time on clock @{term \<open>K\<close>} reaches @{term \<open>\<tau>\<close>}.
\<close>
definition first_time :: \<open>'a::linordered_field run \<Rightarrow> clock \<Rightarrow> nat \<Rightarrow> 'a tag_const
                          \<Rightarrow> bool\<close>
where
  \<open>first_time \<rho> K n \<tau> \<equiv> (time ((Rep_run \<rho>) n K) = \<tau>)
                      \<and> (\<nexists>n'. n' < n \<and> time ((Rep_run \<rho>) n' K) = \<tau>)\<close>

text\<open>
  The time on a clock is necessarily less than @{term \<open>\<tau>\<close>} before the first instant
  at which it reaches @{term \<open>\<tau>\<close>}.
\<close>
lemma before_first_time:
  assumes \<open>first_time \<rho> K n \<tau>\<close>
      and \<open>m < n\<close>
    shows \<open>time ((Rep_run \<rho>) m K) < \<tau>\<close>
proof -
  have \<open>mono (\<lambda>n. time (Rep_run \<rho> n K))\<close> using Rep_run by blast
  moreover from assms(2) have \<open>m \<le> n\<close> using less_imp_le by simp
  moreover have \<open>mono (\<lambda>n. time (Rep_run \<rho> n K))\<close> using Rep_run by blast
  ultimately have  \<open>time ((Rep_run \<rho>) m K) \<le> time ((Rep_run \<rho>) n K)\<close>
    by (simp add:mono_def)
  moreover from assms(1) have \<open>time ((Rep_run \<rho>) n K) = \<tau>\<close>
    using first_time_def by blast
  moreover from assms have \<open>time ((Rep_run \<rho>) m K) \<noteq> \<tau>\<close>
    using first_time_def by blast
  ultimately show ?thesis by simp
qed

text\<open>
  This leads to an alternate definition of @{term \<open>first_time\<close>}:
\<close>
lemma alt_first_time_def:
  assumes \<open>\<forall>m < n. time ((Rep_run \<rho>) m K) < \<tau>\<close>
      and \<open>time ((Rep_run \<rho>) n K) = \<tau>\<close>
    shows \<open>first_time \<rho> K n \<tau>\<close>
proof -
  from assms(1) have \<open>\<forall>m < n. time ((Rep_run \<rho>) m K) \<noteq> \<tau>\<close>
    by (simp add: less_le)
  with assms(2) show ?thesis by (simp add: first_time_def)
qed

end
