(*
  File:   Banach_Steinhaus_Missing.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Missing results for the proof of Banach-Steinhaus theorem\<close>

theory Banach_Steinhaus_Missing
  imports
    "HOL-Analysis.Infinite_Set_Sum"

begin
subsection \<open>Results missing for the proof of Banach-Steinhaus theorem\<close>
text \<open>
  The results proved here are preliminaries for the proof of Banach-Steinhaus theorem using Sokal's 
  approach, but they do not explicitly appear in Sokal's paper ~\cite{sokal2011reall}.
\<close>

text\<open>Notation for the norm\<close>
bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

bundle no_notation_norm begin
no_notation norm ("\<parallel>_\<parallel>")
end

unbundle notation_norm

text\<open>Notation for apply bilinear function\<close>
bundle notation_blinfun_apply begin
notation blinfun_apply (infixr "*\<^sub>v" 70)
end

bundle no_notation_blinfun_apply begin
no_notation blinfun_apply (infixr "*\<^sub>v" 70)
end

unbundle notation_blinfun_apply

lemma bdd_above_plus:
  fixes f::\<open>'a \<Rightarrow> real\<close>
  assumes \<open>bdd_above (f ` S)\<close> and \<open>bdd_above (g ` S)\<close> 
  shows \<open>bdd_above ((\<lambda> x. f x + g x) ` S)\<close>
  text \<open>
  Explanation: If the images of two real-valued functions \<^term>\<open>f\<close>,\<^term>\<open>g\<close> are bounded above on a 
  set \<^term>\<open>S\<close>, then the image of their sum is bounded on \<^term>\<open>S\<close>.
\<close>
proof-
  obtain M where \<open>\<And> x. x\<in>S \<Longrightarrow> f x \<le> M\<close>
    using \<open>bdd_above (f ` S)\<close> unfolding bdd_above_def by blast
  obtain N where \<open>\<And> x. x\<in>S \<Longrightarrow> g x \<le> N\<close>
    using \<open>bdd_above (g ` S)\<close> unfolding bdd_above_def by blast
  have \<open>\<And> x. x\<in>S \<Longrightarrow> f x + g x \<le> M + N\<close>
    using \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> M\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> g x \<le> N\<close> by fastforce
  thus ?thesis unfolding bdd_above_def by blast
qed

text\<open>The maximum of two functions\<close>
definition pointwise_max:: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  \<open>pointwise_max f g = (\<lambda>x. max (f x) (g x))\<close>

lemma max_Sup_absorb_left:
  fixes f g::\<open>'a \<Rightarrow> real\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>
  shows \<open>Sup ((pointwise_max f g) ` X) = Sup (f ` X)\<close>

  text \<open>Explanation: For real-valued functions \<^term>\<open>f\<close> and \<^term>\<open>g\<close>, if the supremum of \<^term>\<open>f\<close> is 
    greater-equal the supremum of \<^term>\<open>g\<close>, then the supremum of \<^term>\<open>max f g\<close> equals the supremum of
    \<^term>\<open>f\<close>. (Under some technical conditions.)\<close>

proof-
  have y_Sup: \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X) \<Longrightarrow> y \<le> Sup (f ` X)\<close> for y
  proof-
    assume \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X)\<close>
    then obtain x where \<open>y = max (f x) (g x)\<close> and \<open>x \<in> X\<close>
      by blast
    have \<open>f x \<le> Sup (f ` X)\<close>
      by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (f ` X)\<close> cSUP_upper) 
    moreover have  \<open>g x \<le> Sup (g ` X)\<close>
      by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (g ` X)\<close> cSUP_upper) 
    ultimately have \<open>max (f x) (g x) \<le> Sup (f ` X)\<close>
      using  \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close> by auto
    thus ?thesis by (simp add: \<open>y = max (f x) (g x)\<close>) 
  qed
  have y_f_X: \<open>y \<in> f ` X \<Longrightarrow> y \<le> Sup ((\<lambda> x. max (f x) (g x)) ` X)\<close> for y
  proof-
    assume \<open>y \<in> f ` X\<close>
    then obtain x where \<open>x \<in> X\<close> and \<open>y = f x\<close>
      by blast
    have  \<open>bdd_above ((\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X)\<close>
      by (metis (no_types) \<open>bdd_above (f ` X)\<close> \<open>bdd_above (g ` X)\<close> bdd_above_image_sup sup_max)
    moreover have \<open>e > 0 \<Longrightarrow> \<exists> k \<in> (\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X. y \<le> k + e\<close>
      for e::real
      using \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close> by (smt \<open>x \<in> X\<close> \<open>y = f x\<close> image_eqI)        
    ultimately show ?thesis
      using \<open>x \<in> X\<close> \<open>y = f x\<close> cSUP_upper by fastforce
  qed
  have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<le> Sup (f ` X)\<close>
    using y_Sup by (simp add: \<open>X \<noteq> {}\<close> cSup_least) 
  moreover have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<ge> Sup (f ` X)\<close>
    using y_f_X by (metis (mono_tags) cSup_least calculation empty_is_image)  
  ultimately show ?thesis unfolding pointwise_max_def by simp
qed

lemma max_Sup_absorb_right:
  fixes f g::\<open>'a \<Rightarrow> real\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<le> Sup (g ` X)\<close>
  shows \<open>Sup ((pointwise_max f g) ` X) = Sup (g ` X)\<close>
  text \<open>
  Explanation: For real-valued functions \<^term>\<open>f\<close> and \<^term>\<open>g\<close> and a nonempty set \<^term>\<open>X\<close>, such that 
  the \<^term>\<open>f\<close> and \<^term>\<open>g\<close> are bounded above on \<^term>\<open>X\<close>, if the supremum of \<^term>\<open>f\<close> on \<^term>\<open>X\<close> is 
  lower-equal the supremum of \<^term>\<open>g\<close> on \<^term>\<open>X\<close>, then the supremum of \<^term>\<open>pointwise_max f g\<close> on \<^term>\<open>X\<close>
  equals the supremum of \<^term>\<open>g\<close>. This is the right analog of @{text max_Sup_absorb_left}.
\<close>
proof-
  have \<open>Sup ((pointwise_max g f) ` X) = Sup (g ` X)\<close>
    using  assms by (simp add: max_Sup_absorb_left)     
  moreover have \<open>pointwise_max g f = pointwise_max f g\<close>
    unfolding pointwise_max_def  by auto
  ultimately show ?thesis by simp
qed

lemma max_Sup:
  fixes f g::\<open>'a \<Rightarrow> real\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close>
  shows \<open>Sup ((pointwise_max f g) ` X) = max (Sup (f ` X)) (Sup (g ` X))\<close>
  text \<open>
  Explanation: Let \<^term>\<open>X\<close> be a nonempty set. Two supremum over \<^term>\<open>X\<close> of the maximum of two 
  real-value functions is equal to the maximum of their suprema over \<^term>\<open>X\<close>, provided that the
  functions are bounded above on \<^term>\<open>X\<close>.
\<close>
proof(cases \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>)
  case True thus ?thesis by (simp add: assms(1) assms(2) assms(3) max_Sup_absorb_left)
next
  case False 
  have f1: "\<not> 0 \<le> Sup (f ` X) + - 1 * Sup (g ` X)"
    using False by linarith
  hence "Sup (Banach_Steinhaus_Missing.pointwise_max f g ` X) = Sup (g ` X)"
    by (simp add: assms(1) assms(2) assms(3) max_Sup_absorb_right)
  thus ?thesis
    using f1 by linarith
qed


lemma identity_telescopic:
  fixes x :: \<open>_ \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>x \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
  text\<open>
  Expression of a limit as a telescopic series.
  Explanation: If \<^term>\<open>x\<close> converges to \<^term>\<open>l\<close> then the sum \<^term>\<open>sum (\<lambda> k. x (Suc k) - x k) {n..N}\<close>
  converges to \<^term>\<open>l - x n\<close> as \<^term>\<open>N\<close> goes to infinity.
\<close>
proof-
  have \<open>(\<lambda> p. x (p + Suc n)) \<longlonglongrightarrow> l\<close>
    using \<open>x \<longlonglongrightarrow> l\<close> by (rule LIMSEQ_ignore_initial_segment)
  hence \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close>   
    by (simp add: add.commute)
  hence \<open>(\<lambda> p. x (Suc (n + p))) \<longlonglongrightarrow> l\<close>
    by simp 
  hence \<open>(\<lambda> t. (- (x n)) + (\<lambda> p.  x (Suc (n + p))) t ) \<longlonglongrightarrow> (- (x n))  + l\<close>
    using tendsto_add_const_iff by metis 
  hence f1: \<open>(\<lambda> p. x (Suc (n + p)) - x n)\<longlonglongrightarrow> l - x n\<close>
    by simp
  have \<open>sum (\<lambda> k. x (Suc k) - x k) {n..n+p} = x (Suc (n+p)) - x n\<close> for p
    by (simp add: sum_Suc_diff)
  moreover have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + t) 
               = (\<lambda> p. sum (\<lambda> k. x (Suc k) - x k) {n..n+p}) t\<close> for t
    by blast
  ultimately have  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + p)) \<longlonglongrightarrow> l - x n\<close>
    using f1 by simp
  hence \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (p + n)) \<longlonglongrightarrow> l - x n\<close>
    by (simp add: add.commute)
  hence  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) p) \<longlonglongrightarrow> l - x n\<close>
    using Topological_Spaces.LIMSEQ_offset[where f = "(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N})" 
        and a = "l - x n" and k = n] by blast
  hence  \<open>(\<lambda> M. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) M) \<longlonglongrightarrow> l - x n\<close>
    by simp
  thus ?thesis by blast
qed

lemma bound_Cauchy_to_lim:
  assumes \<open>y \<longlonglongrightarrow> x\<close> and \<open>\<And>n. \<parallel>y (Suc n) - y n\<parallel> \<le> c^n\<close> and \<open>y 0 = 0\<close> and \<open>c < 1\<close>
  shows \<open>\<parallel>x - y (Suc n)\<parallel> \<le> (c / (1 - c)) * c ^ n\<close>
  text\<open>
  Inequality about a sequence of approximations assuming that the sequence of differences is bounded
  by a geometric progression.
  Explanation: Let \<^term>\<open>y\<close> be a sequence converging to \<^term>\<open>x\<close>.
  If \<^term>\<open>y\<close> satisfies the inequality \<open>\<parallel>y (Suc n) - y n\<parallel> \<le> c ^ n\<close> for some \<^term>\<open>c < 1\<close> and 
  assuming \<^term>\<open>y 0 = 0\<close> then the inequality \<open>\<parallel>x - y (Suc n)\<parallel> \<le> (c / (1 - c)) * c ^ n\<close> holds.
\<close>
proof-
  have \<open>c \<ge> 0\<close>
    using \<open>\<And> n. \<parallel>y (Suc n) - y n\<parallel> \<le> c^n\<close> by (smt norm_imp_pos_and_ge power_Suc0_right)
  have norm_1: \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (c ^ Suc n)/(1 - c)\<close> for N
  proof(cases \<open>N < Suc n\<close>)
    case True
    hence \<open>\<parallel>sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}\<parallel> = 0\<close>
      by auto
    thus ?thesis  using  \<open>c \<ge> 0\<close> \<open>c < 1\<close> by auto       
  next
    case False
    hence \<open>N \<ge> Suc n\<close>
      by auto
    have \<open>c^(Suc N) \<ge> 0\<close>
      using \<open>c \<ge> 0\<close> by auto
    have \<open>1 - c > 0\<close>
      by (simp add: \<open>c < 1\<close>)
    hence \<open>(1 - c)/(1 - c) = 1\<close>
      by auto
    have \<open>\<parallel>sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}\<parallel> \<le> (sum (\<lambda>k. \<parallel>y (Suc k) - y k\<parallel>) {Suc n .. N})\<close>
      by (simp add: sum_norm_le)
    hence \<open>\<parallel>sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}\<parallel> \<le> (sum (power c) {Suc n .. N})\<close>
      by (simp add: assms(2) sum_norm_le)
    hence \<open>(1 - c) * \<parallel>sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}\<parallel>
                   \<le> (1 - c) * (sum (power c) {Suc n .. N})\<close>
      using \<open>0 < 1 - c\<close> real_mult_le_cancel_iff2 by blast      
    also have \<open>\<dots> = c^(Suc n) - c^(Suc N)\<close>
      using Set_Interval.sum_gp_multiplied \<open>Suc n \<le> N\<close> by blast
    also have \<open>\<dots> \<le> c^(Suc n)\<close>
      using \<open>c^(Suc N) \<ge> 0\<close> by auto
    finally have \<open>(1 - c) * \<parallel>\<Sum>k = Suc n..N. y (Suc k) - y k\<parallel> \<le> c ^ Suc n\<close>
      by blast
    hence \<open>((1 - c) * \<parallel>\<Sum>k = Suc n..N. y (Suc k) - y k\<parallel>)/(1 - c)
                   \<le> (c ^ Suc n)/(1 - c)\<close>
      using \<open>0 < 1 - c\<close> by (smt divide_right_mono)      
    thus \<open>\<parallel>\<Sum>k = Suc n..N. y (Suc k) - y k\<parallel> \<le> (c ^ Suc n)/(1 - c)\<close>
      using \<open>0 < 1 - c\<close> by auto 
  qed
  have \<open>(\<lambda> N. (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> x - y (Suc n)\<close>
    by (metis (no_types) \<open>y \<longlonglongrightarrow> x\<close> identity_telescopic)     
  hence \<open>(\<lambda> N. \<parallel>sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}\<parallel>) \<longlonglongrightarrow> \<parallel>x - y (Suc n)\<parallel>\<close>
    using tendsto_norm by blast
  hence \<open>\<parallel>x - y (Suc n)\<parallel> \<le> (c ^ Suc n)/(1 - c)\<close>
    using norm_1 Lim_bounded by blast
  hence  \<open>\<parallel>x - y (Suc n)\<parallel> \<le> (c ^ Suc n)/(1 - c)\<close>
    by auto
  moreover have \<open>(c ^ Suc n)/(1 - c) = (c / (1 - c)) * (c ^ n)\<close>
    by (simp add: divide_inverse_commute)    
  ultimately show \<open>\<parallel>x - y (Suc n)\<parallel> \<le> (c / (1 - c)) * (c ^ n)\<close> by linarith
qed

lemma onorm_open_ball:
  includes notation_norm
  shows \<open>\<parallel>f\<parallel> = Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 }\<close>
  text \<open>
  Explanation: Let \<^term>\<open>f\<close> be a bounded linear operator. The operator norm of \<^term>\<open>f\<close> is the
  supremum of \<^term>\<open>norm (f x)\<close> for \<^term>\<open>x\<close> such that \<^term>\<open>norm x < 1\<close>.
\<close>
proof(cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  hence \<open>x = 0\<close> for x::'a
    by auto
  hence \<open>f *\<^sub>v x = 0\<close> for x
    by (metis (full_types) blinfun.zero_right)
  hence \<open>\<parallel>f\<parallel> = 0\<close>
    by (simp add: blinfun_eqI zero_blinfun.rep_eq)      
  have \<open>{ \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} = {0}\<close>
    by (smt Collect_cong \<open>\<And>x. f *\<^sub>v x = 0\<close> norm_zero singleton_conv)      
  hence \<open>Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} = 0\<close>
    by simp    
  thus ?thesis using \<open>\<parallel>f\<parallel> = 0\<close> by auto      
next
  case False
  hence \<open>(UNIV::'a set) \<noteq> 0\<close>
    by simp
  have nonnegative: \<open>\<parallel>f *\<^sub>v x\<parallel> \<ge> 0\<close> for x
    by simp
  have \<open>\<exists> x::'a. x \<noteq> 0\<close>
    using \<open>UNIV \<noteq> 0\<close> by auto
  then obtain x::'a where \<open>x \<noteq> 0\<close>
    by blast
  hence \<open>\<parallel>x\<parallel> \<noteq> 0\<close>
    by auto
  define y where \<open>y = x /\<^sub>R \<parallel>x\<parallel>\<close>
  have \<open>norm y = \<parallel> x /\<^sub>R \<parallel>x\<parallel> \<parallel>\<close>
    unfolding y_def by auto
  also have \<open>\<dots> = \<parallel>x\<parallel> /\<^sub>R \<parallel>x\<parallel>\<close>
    by auto
  also have \<open>\<dots> = 1\<close>
    using \<open>\<parallel>x\<parallel> \<noteq> 0\<close> by auto
  finally have \<open>\<parallel>y\<parallel> = 1\<close>
    by blast
  hence norm_1_non_empty: \<open>{ \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<noteq> {}\<close>
    by blast
  have norm_1_bounded: \<open>bdd_above { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
    unfolding bdd_above_def apply auto
    by (metis norm_blinfun)
  have norm_less_1_non_empty: \<open>{\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} \<noteq> {}\<close>
    by (metis (mono_tags, lifting) Collect_empty_eq_bot bot_empty_eq empty_iff norm_zero 
        zero_less_one)   
  have norm_less_1_bounded: \<open>bdd_above {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
  proof-
    have \<open>\<exists>r. \<parallel>a r\<parallel> < 1 \<longrightarrow> \<parallel>f *\<^sub>v (a r)\<parallel> \<le> r\<close> for a :: "real \<Rightarrow> 'a"
    proof-
      obtain r :: "('a \<Rightarrow>\<^sub>L 'b) \<Rightarrow> real" where
        "\<And>f x. 0 \<le> r f \<and> (bounded_linear f \<longrightarrow> \<parallel>f *\<^sub>v x\<parallel> \<le> \<parallel>x\<parallel> * r f)"
        using bounded_linear.nonneg_bounded by moura
      have \<open>\<not> \<parallel>f\<parallel> < 0\<close>
        by simp          
      hence "(\<exists>r. \<parallel>f\<parallel> * \<parallel>a r\<parallel> \<le> r) \<or> (\<exists>r. \<parallel>a r\<parallel> < 1 \<longrightarrow> \<parallel>f *\<^sub>v a r\<parallel> \<le> r)"
        by (meson less_eq_real_def mult_le_cancel_left2) 
      thus ?thesis using dual_order.trans norm_blinfun by blast
    qed
    hence \<open>\<exists> M. \<forall> x. \<parallel>x\<parallel> < 1 \<longrightarrow> \<parallel>f *\<^sub>v x\<parallel> \<le> M\<close>
      by metis
    thus ?thesis by auto 
  qed
  have Sup_non_neg: \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<ge> 0\<close>
    by (smt Collect_empty_eq cSup_upper mem_Collect_eq nonnegative norm_1_bounded norm_1_non_empty)      
  have \<open>{0::real} \<noteq> {}\<close>
    by simp
  have \<open>bdd_above {0::real}\<close>
    by simp
  show \<open>\<parallel>f\<parallel> = Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
  proof(cases \<open>\<forall>x. f *\<^sub>v x = 0\<close>)
    case True
    have \<open>\<parallel>f *\<^sub>v x\<parallel> = 0\<close> for x
      by (simp add: True)
    hence \<open>{\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 } \<subseteq> {0}\<close>
      by blast        
    moreover have \<open>{\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 } \<supseteq> {0}\<close>
      using calculation norm_less_1_non_empty by fastforce                        
    ultimately have \<open>{\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 } = {0}\<close>  
      by blast
    hence Sup1: \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 } = 0\<close> 
      by simp
    have \<open>\<parallel>f\<parallel> = 0\<close>
      by (simp add: True blinfun_eqI)        
    moreover have \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} = 0\<close>
      using Sup1 by blast
    ultimately show ?thesis by simp
  next
    case False
    have norm_f_eq_leq: \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<Longrightarrow> 
                         y \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close> for y
    proof-
      assume \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
      hence \<open>\<exists> x. y = \<parallel>f *\<^sub>v x\<parallel> \<and> \<parallel>x\<parallel> = 1\<close>
        by blast
      then obtain x where \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> and \<open>\<parallel>x\<parallel> = 1\<close>
        by auto
      define y' where \<open>y' n = (1 - (inverse (real (Suc n)))) *\<^sub>R y\<close> for n
      have \<open>y' n \<in> {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close> for n
      proof-
        have \<open>y' n = (1 - (inverse (real (Suc n)))) *\<^sub>R \<parallel>f *\<^sub>v x\<parallel>\<close>
          using y'_def \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> by blast
        also have \<open>... = \<bar>(1 - (inverse (real (Suc n))))\<bar> *\<^sub>R \<parallel>f *\<^sub>v x\<parallel>\<close>
          by (metis (mono_tags, hide_lams) \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> abs_1 abs_le_self_iff abs_of_nat 
              abs_of_nonneg add_diff_cancel_left' add_eq_if cancel_comm_monoid_add_class.diff_cancel
              diff_ge_0_iff_ge eq_iff_diff_eq_0 inverse_1 inverse_le_iff_le nat.distinct(1) of_nat_0
              of_nat_Suc of_nat_le_0_iff zero_less_abs_iff zero_neq_one)
        also have \<open>... = \<parallel>f *\<^sub>v ((1 - (inverse (real (Suc n)))) *\<^sub>R  x)\<parallel>\<close>
          by (simp add: blinfun.scaleR_right)            
        finally have y'_1: \<open>y' n = \<parallel>f *\<^sub>v ( (1 - (inverse (real (Suc n)))) *\<^sub>R x)\<parallel>\<close> 
          by blast
        have \<open>\<parallel>(1 - (inverse (Suc n))) *\<^sub>R x\<parallel> = (1 - (inverse (real (Suc n)))) * \<parallel>x\<parallel>\<close>
          by (simp add: linordered_field_class.inverse_le_1_iff)                
        hence \<open>\<parallel>(1 - (inverse (Suc n))) *\<^sub>R x\<parallel> < 1\<close>
          by (simp add: \<open>\<parallel>x\<parallel> = 1\<close>) 
        thus ?thesis using y'_1 by blast 
      qed
      have \<open>(\<lambda>n. (1 - (inverse (real (Suc n)))) ) \<longlonglongrightarrow> 1\<close>
        using Limits.LIMSEQ_inverse_real_of_nat_add_minus by simp
      hence \<open>(\<lambda>n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> 1 *\<^sub>R y\<close>
        using Limits.tendsto_scaleR by blast
      hence \<open>(\<lambda>n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> y\<close>
        by simp
      hence \<open>(\<lambda>n. y' n) \<longlonglongrightarrow> y\<close>
        using y'_def by simp
      hence \<open>y' \<longlonglongrightarrow> y\<close> 
        by simp
      have \<open>y' n \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close> for n
        using cSup_upper \<open>\<And>n. y' n \<in> {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> < 1}\<close> norm_less_1_bounded by blast
      hence \<open>y \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
        using \<open>y' \<longlonglongrightarrow> y\<close> Topological_Spaces.Sup_lim by (meson LIMSEQ_le_const2)
      thus ?thesis by blast
    qed
    hence \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1} \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
      by (metis (lifting) cSup_least norm_1_non_empty)
    have \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} \<Longrightarrow> y \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close> for y
    proof(cases \<open>y = 0\<close>)
      case True thus ?thesis by (simp add: Sup_non_neg) 
    next
      case False
      hence \<open>y \<noteq> 0\<close> by blast
      assume \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
      hence \<open>\<exists> x. y = \<parallel>f *\<^sub>v x\<parallel> \<and> \<parallel>x\<parallel> < 1\<close>
        by blast
      then obtain x where \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> and \<open>\<parallel>x\<parallel> < 1\<close>
        by blast
      have \<open>(1/\<parallel>x\<parallel>) * y = (1/\<parallel>x\<parallel>) * \<parallel>f x\<parallel>\<close>
        by (simp add: \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close>)
      also have \<open>... = \<bar>1/\<parallel>x\<parallel>\<bar> * \<parallel>f *\<^sub>v x\<parallel>\<close>
        by simp
      also have \<open>... = \<parallel>(1/\<parallel>x\<parallel>) *\<^sub>R (f *\<^sub>v x)\<parallel>\<close>
        by simp
      also have \<open>... = \<parallel>f *\<^sub>v ((1/\<parallel>x\<parallel>) *\<^sub>R x)\<parallel>\<close>
        by (simp add: blinfun.scaleR_right)          
      finally have \<open>(1/\<parallel>x\<parallel>) * y  = \<parallel>f *\<^sub>v ((1/\<parallel>x\<parallel>) *\<^sub>R x)\<parallel>\<close>
        by blast
      have \<open>x \<noteq> 0\<close>
        using  \<open>y \<noteq> 0\<close> \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> blinfun.zero_right by auto 
      have \<open>\<parallel> (1/\<parallel>x\<parallel>) *\<^sub>R x \<parallel> = \<bar> (1/\<parallel>x\<parallel>) \<bar> * \<parallel>x\<parallel>\<close>
        by simp
      also have \<open>... = (1/\<parallel>x\<parallel>) * \<parallel>x\<parallel>\<close>
        by simp
      finally have  \<open>\<parallel>(1/\<parallel>x\<parallel>) *\<^sub>R x\<parallel> = 1\<close>
        using \<open>x \<noteq> 0\<close> by simp
      hence \<open>(1/\<parallel>x\<parallel>) * y \<in> { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
        using \<open>1 / \<parallel>x\<parallel> * y = \<parallel>f *\<^sub>v (1 / \<parallel>x\<parallel>) *\<^sub>R x\<parallel>\<close> by blast
      hence \<open>(1/\<parallel>x\<parallel>) * y \<le> Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
        by (simp add: cSup_upper norm_1_bounded)
      moreover have \<open>y \<le> (1/\<parallel>x\<parallel>) * y\<close>
        by (metis \<open>\<parallel>x\<parallel> < 1\<close> \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close> mult_le_cancel_right1 norm_not_less_zero 
            order.strict_implies_order \<open>x \<noteq> 0\<close> less_divide_eq_1_pos zero_less_norm_iff)
      ultimately show ?thesis by linarith 
    qed
    hence \<open>Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1} \<le> Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
      by (smt cSup_least norm_less_1_non_empty) 
    hence \<open>Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1} = Sup { \<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1}\<close>
      using \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> |x. norm x = 1} \<le> Sup { \<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> < 1}\<close> by linarith
    have f1: \<open>(SUP x. \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>) = Sup { \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> | x. True}\<close>
      by (simp add: full_SetCompr_eq)
    have \<open>y \<in> { \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True} \<Longrightarrow> y \<in> { \<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}\<close>
      for y
    proof-
      assume \<open>y \<in> { \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True}\<close> show ?thesis
      proof(cases \<open>y = 0\<close>)
        case True  thus ?thesis by simp 
      next
        case False
        have \<open>\<exists> x. y = \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>\<close>
          using \<open>y \<in> { \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True}\<close> by auto
        then obtain x where \<open>y = \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>\<close>
          by blast
        hence \<open>y = \<bar>(1/\<parallel>x\<parallel>)\<bar> * \<parallel> f *\<^sub>v x \<parallel>\<close>
          by simp
        hence \<open>y = \<parallel>(1/\<parallel>x\<parallel>) *\<^sub>R (f *\<^sub>v x)\<parallel>\<close>
          by simp
        hence \<open>y = \<parallel>f ((1/\<parallel>x\<parallel>) *\<^sub>R x)\<parallel>\<close>
          by (simp add: blinfun.scaleR_right)            
        moreover have \<open>\<parallel> (1/\<parallel>x\<parallel>) *\<^sub>R x \<parallel> = 1\<close>
          using False \<open>y = \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>\<close> by auto
        ultimately have \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}\<close>
          by blast
        thus ?thesis by blast
      qed
    qed
    moreover have \<open>y \<in> {\<parallel>f x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0} \<Longrightarrow> y \<in> {\<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True}\<close>
      for y
    proof(cases \<open>y = 0\<close>)
      case True thus ?thesis by auto 
    next
      case False
      hence \<open>y \<notin> {0}\<close>
        by simp
      moreover assume \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}\<close>
      ultimately have \<open>y \<in> {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}\<close>
        by simp
      then obtain x where \<open>\<parallel>x\<parallel> = 1\<close> and \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close>
        by auto
      have \<open>y = \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>\<close> using  \<open>\<parallel>x\<parallel> = 1\<close>  \<open>y = \<parallel>f *\<^sub>v x\<parallel>\<close>
        by simp 
      thus ?thesis by auto 
    qed
    ultimately have \<open>{\<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True} = {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}\<close>
      by blast
    hence \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True} = Sup ({\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0})\<close>
      by simp
    have "\<And>r s. \<not> (r::real) \<le> s \<or> sup r s = s"
      by (metis (lifting) sup.absorb_iff1 sup_commute)
    hence \<open>Sup ({\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {(0::real)})
             = max (Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}) (Sup {0::real})\<close>
      using \<open>0 \<le> Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}\<close> \<open>bdd_above {0}\<close> \<open>{0} \<noteq> {}\<close> cSup_singleton 
        cSup_union_distrib max.absorb_iff1 sup_commute norm_1_bounded norm_1_non_empty
      by (metis (no_types, lifting) )
    moreover have \<open>Sup {(0::real)} = (0::real)\<close>
      by simp          
    ultimately have \<open>Sup ({\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}) = Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}\<close>
      using Sup_non_neg by linarith
    moreover have \<open>Sup ( {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}) 
                    = max (Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}) (Sup {0}) \<close>
      using Sup_non_neg  \<open>Sup ({\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0}) 
        = max (Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1}) (Sup {0})\<close> 
      by auto           
    ultimately have f2: \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> | x. True} = Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
      using \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel> |x. True} = Sup ({\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} \<union> {0})\<close> by linarith
    have \<open>(SUP x. \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>) = Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> = 1}\<close>
      using f1 f2 by linarith
    hence \<open>(SUP x. \<parallel>f *\<^sub>v x\<parallel> / \<parallel>x\<parallel>) = Sup {\<parallel>f *\<^sub>v x\<parallel> | x. \<parallel>x\<parallel> < 1 }\<close>
      by (simp add: \<open>Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> = 1} = Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> < 1}\<close>)        
    thus ?thesis apply transfer by (simp add: onorm_def) 
  qed      
qed

lemma onorm_r:
  includes notation_norm
  assumes \<open>r > 0\<close>
  shows \<open>\<parallel>f\<parallel> = Sup ((\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 r)) / r\<close>
  text \<open>
  Explanation: The norm of \<^term>\<open>f\<close> is \<^term>\<open>1/r\<close> of the supremum of the norm of \<^term>\<open>f *\<^sub>v x\<close> for
  \<^term>\<open>x\<close> in the ball of radius \<^term>\<open>r\<close> centered at the origin.
\<close>
proof-
  have \<open>\<parallel>f\<parallel> = Sup {\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> < 1}\<close>
    using onorm_open_ball by blast
  moreover have \<open>{\<parallel>f *\<^sub>v x\<parallel> |x. \<parallel>x\<parallel> < 1} = (\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 1)\<close>
    unfolding ball_def by auto
  ultimately have onorm_f: \<open>\<parallel>f\<parallel> = Sup ((\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 1))\<close>
    by simp
  have s2: \<open>x \<in> (\<lambda>t. r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<Longrightarrow> x \<le> r * Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1)\<close> for x
  proof-
    assume \<open>x \<in> (\<lambda>t. r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1\<close>
    hence \<open>\<exists> t. x = r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel> \<and> \<parallel>t\<parallel> < 1\<close>
      by auto
    then obtain t where \<open>x = r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>\<close> and \<open>\<parallel>t\<parallel> < 1\<close>
      by blast
    define y where \<open>y = x /\<^sub>R r\<close>
    have \<open>x = r * (inverse r * x)\<close>
      using \<open>x = r *\<^sub>R norm (f t)\<close> by auto
    hence \<open>x - (r * (inverse r * x)) \<le> 0\<close>
      by linarith
    hence \<open>x \<le> r * (x /\<^sub>R r)\<close>
      by auto
    have \<open>y \<in> (\<lambda>k. \<parallel>f *\<^sub>v k\<parallel>) ` ball 0 1\<close>
      unfolding y_def by (smt \<open>x \<in> (\<lambda>t. r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1\<close> assms image_iff 
          inverse_inverse_eq pos_le_divideR_eq positive_imp_inverse_positive) 
    moreover have \<open>x \<le> r * y\<close>          
      using \<open>x \<le> r * (x /\<^sub>R r)\<close> y_def by blast
    ultimately have y_norm_f: \<open>y \<in> (\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<and> x \<le> r * y\<close>
      by blast
    have \<open>(\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<noteq> {}\<close>
      by simp        
    moreover have \<open>bdd_above ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1)\<close>
      by (simp add: bounded_linear_image blinfun.bounded_linear_right bounded_imp_bdd_above 
          bounded_norm_comp) 
    moreover have \<open>\<exists> y. y \<in> (\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<and> x \<le> r * y\<close>
      using y_norm_f by blast
    ultimately show ?thesis
      by (smt \<open>0 < r\<close> cSup_upper ordered_comm_semiring_class.comm_mult_left_mono) 
  qed
  have s3: \<open>(\<And>x. x \<in> (\<lambda>t. r * \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<Longrightarrow> x \<le> y) \<Longrightarrow>
         r * Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1) \<le> y\<close> for y
  proof-
    assume \<open>\<And>x. x \<in> (\<lambda>t. r * \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<Longrightarrow> x \<le> y\<close> 
    have x_leq: \<open>x \<in> (\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<Longrightarrow> x \<le> y / r\<close> for x
    proof-
      assume \<open>x \<in> (\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1\<close>
      then obtain t where \<open>t \<in> ball (0::'a) 1\<close> and \<open>x = \<parallel>f *\<^sub>v t\<parallel>\<close>
        by auto
      define x' where \<open>x' = r *\<^sub>R x\<close>
      have \<open>x' = r * \<parallel>f *\<^sub>v t\<parallel>\<close>
        by (simp add: \<open>x = \<parallel>f *\<^sub>v t\<parallel>\<close> x'_def)
      hence \<open>x' \<in> (\<lambda>t. r * \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1\<close>
        using \<open>t \<in> ball (0::'a) 1\<close> by auto
      hence \<open>x' \<le> y\<close>
        using \<open>\<And>x. x \<in> (\<lambda>t. r * \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<Longrightarrow> x \<le> y\<close> by blast        
      thus \<open>x \<le> y / r\<close>
        unfolding x'_def using \<open>r > 0\<close> by (simp add: mult.commute pos_le_divide_eq) 
    qed
    have \<open>(\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1 \<noteq> {}\<close>
      by simp        
    moreover have \<open>bdd_above ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1)\<close>
      by (simp add: bounded_linear_image blinfun.bounded_linear_right bounded_imp_bdd_above 
          bounded_norm_comp) 
    ultimately have \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1) \<le> y/r\<close>
      using x_leq by (simp add: \<open>bdd_above ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 1)\<close> cSup_least) 
    thus ?thesis using \<open>r > 0\<close>
      by (smt divide_strict_right_mono nonzero_mult_div_cancel_left)  
  qed
  have norm_scaleR: \<open>norm \<circ> ((*\<^sub>R) r) = ((*\<^sub>R) \<bar>r\<bar>) \<circ> (norm::'a \<Rightarrow> real)\<close>
    by auto
  have f_x1: \<open>f (r *\<^sub>R x) = r *\<^sub>R f x\<close> for x
    by (simp add: blinfun.scaleR_right)    
  have \<open>ball (0::'a) r = ((*\<^sub>R) r) ` (ball 0 1)\<close>
    by (smt assms ball_scale nonzero_mult_div_cancel_left right_inverse_eq scale_zero_right)
  hence \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 r)) = Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (((*\<^sub>R) r) ` (ball 0 1)))\<close>
    by simp
  also have \<open>\<dots> = Sup (((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) \<circ> ((*\<^sub>R) r)) ` (ball 0 1))\<close>
    using Sup.SUP_image by auto
  also have \<open>\<dots> = Sup ((\<lambda>t. \<parallel>f *\<^sub>v (r *\<^sub>R t)\<parallel>) ` (ball 0 1))\<close>
    using f_x1 by (simp add: comp_assoc) 
  also have \<open>\<dots> = Sup ((\<lambda>t. \<bar>r\<bar> *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 1))\<close>
    using norm_scaleR f_x1 by auto 
  also have \<open>\<dots> = Sup ((\<lambda>t. r *\<^sub>R \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 1))\<close>
    using \<open>r > 0\<close> by auto
  also have \<open>\<dots> = r * Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 1))\<close>
    apply (rule cSup_eq_non_empty) apply simp using s2 apply auto using s3 by auto
  also have \<open>\<dots> = r * \<parallel>f\<parallel>\<close>
    using onorm_f by auto
  finally have \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball 0 r) = r * \<parallel>f\<parallel>\<close>
    by blast    
  thus \<open>\<parallel>f\<parallel> = Sup ((\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 r)) / r\<close> using \<open>r > 0\<close> by simp
qed

text\<open>Pointwise convergence\<close>
definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  (\<open>((_)/ \<midarrow>pointwise\<rightarrow> (_))\<close> [60, 60] 60) where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t) \<longlonglongrightarrow> l t)\<close>

lemma linear_limit_linear:
  fixes f :: \<open>_ \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes  \<open>\<And>n. linear (f n)\<close> and \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
  shows \<open>linear F\<close>
  text\<open>
  Explanation: If a family of linear operators converges pointwise, then the limit is also a linear
  operator.
\<close>
proof
  show "F (x + y) = F x + F y" for x y
  proof-
    have "\<forall>a. F a = lim (\<lambda>n. f n a)"
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by (metis (full_types) limI)
    moreover have "\<forall>f b c g. (lim (\<lambda>n. g n + f n) = (b::'b) + c \<or> \<not> f \<longlonglongrightarrow> c) \<or> \<not> g \<longlonglongrightarrow> b"
      by (metis (no_types) limI tendsto_add)
    moreover have "\<And>a. (\<lambda>n. f n a) \<longlonglongrightarrow> F a"
      using assms(2) pointwise_convergent_to_def by force
    ultimately have 
      lim_sum: \<open>lim (\<lambda> n. (f n) x + (f n) y) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      by metis
    have \<open>(f n) (x + y) = (f n) x + (f n) y\<close> for n
      using \<open>\<And> n.  linear (f n)\<close> unfolding linear_def using Real_Vector_Spaces.linear_iff assms(1) 
      by auto
    hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x + (f n) y)\<close>
      by simp
    hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      using lim_sum by simp
    moreover have \<open>(\<lambda> n. (f n) (x + y)) \<longlonglongrightarrow> F (x + y)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    ultimately show ?thesis
      by (metis limI) 
  qed
  show "F (r *\<^sub>R x) = r *\<^sub>R F x" for r and x
  proof-
    have \<open>(f n) (r *\<^sub>R x) = r *\<^sub>R (f n) x\<close> for n
      using  \<open>\<And> n.  linear (f n)\<close> 
      by (simp add: Real_Vector_Spaces.linear_def real_vector.linear_scale)
    hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
      by simp
    have \<open>convergent (\<lambda> n. (f n) x)\<close>
      by (metis assms(2) convergentI pointwise_convergent_to_def)
    moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>R t) tt\<close> for tt
      by (simp add: bounded_linear_scaleR_right)
    ultimately have \<open>lim (\<lambda> n. r *\<^sub>R ((f n) x)) =  r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def 
      by (metis (mono_tags) isCont_tendsto_compose limI)
    hence \<open>lim (\<lambda> n.  (f n) (r *\<^sub>R x)) = r *\<^sub>R lim (\<lambda> n. (f n) x)\<close> 
      using \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close> by simp
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>R x)) \<longlonglongrightarrow> F (r *\<^sub>R x)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    ultimately show ?thesis
      by (metis limI) 
  qed
qed


lemma non_Cauchy_unbounded:
  fixes a ::\<open>_ \<Rightarrow> real\<close> 
  assumes \<open>\<And>n. a n \<ge> 0\<close> and \<open>e > 0\<close> 
    and \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
  shows \<open>(\<lambda>n. (sum a  {0..n})) \<longlonglongrightarrow> \<infinity>\<close>
  text\<open>
  Explanation: If the sequence of partial sums of nonnegative terms is not Cauchy, then it converges
  to infinite.
\<close>
proof-
  define S::"ereal set" where \<open>S = range (\<lambda>n. sum a  {0..n})\<close>
  have \<open>\<exists>s\<in>S.  k*e \<le> s\<close> for k::nat
  proof(induction k)
    case 0
    from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
    obtain m n where \<open>m \<ge> 0\<close> and \<open>n \<ge> 0\<close> and \<open>m > n\<close> and \<open>sum a {Suc n..m} \<ge> e\<close> by blast
    have \<open>n < Suc n\<close>
      by simp
    hence \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
      using Set_Interval.ivl_disj_un(7) \<open>n < m\<close> by auto
    moreover have \<open>finite {0..n}\<close>
      by simp
    moreover have \<open>finite {Suc n..m}\<close>
      by simp
    moreover have \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
      by simp
    ultimately have \<open>sum a {0..n} + sum a {Suc n..m} = sum a {0..m}\<close>
      by (metis sum.union_disjoint) 
    moreover have \<open>sum a {Suc n..m} > 0\<close>
      using \<open>e > 0\<close> \<open>sum a {Suc n..m} \<ge> e\<close> by linarith
    moreover have \<open>sum a {0..n} \<ge> 0\<close>
      by (simp add: assms(1) sum_nonneg)
    ultimately have \<open>sum a {0..m} > 0\<close>
      by linarith      
    moreover have \<open>sum a {0..m} \<in> S\<close>
      unfolding S_def by blast
    ultimately have \<open>\<exists>s\<in>S. 0 \<le> s\<close>
      using ereal_less_eq(5) by fastforce    
    thus ?case
      by (simp add: zero_ereal_def)  
  next
    case (Suc k)
    assume \<open>\<exists>s\<in>S. k*e \<le> s\<close>
    then obtain s where \<open>s\<in>S\<close> and \<open>ereal (k * e) \<le> s\<close>
      by blast
    have \<open>\<exists>N. s = sum a {0..N}\<close>
      using \<open>s\<in>S\<close> unfolding S_def by blast
    then obtain N where \<open>s = sum a {0..N}\<close>
      by blast
    from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
    obtain m n where \<open>m \<ge> Suc N\<close> and \<open>n \<ge> Suc N\<close> and \<open>m > n\<close> and \<open>sum a {Suc n..m} \<ge> e\<close>
      by blast
    have \<open>finite {Suc N..n}\<close>
      by simp
    moreover have \<open>finite {Suc n..m}\<close>
      by simp
    moreover have \<open>{Suc N..n} \<union> {Suc n..m} = {Suc N..m}\<close>
      using Set_Interval.ivl_disj_un
      by (smt \<open>Suc N \<le> n\<close> \<open>n < m\<close> atLeastSucAtMost_greaterThanAtMost less_imp_le_nat)
    moreover have \<open>{} = {Suc N..n} \<inter> {Suc n..m}\<close>
      by simp
    ultimately have \<open>sum a {Suc N..m} = sum a {Suc N..n} + sum a {Suc n..m}\<close>
      by (metis sum.union_disjoint)
    moreover have \<open>sum a {Suc N..n} \<ge> 0\<close>
      using  \<open>\<And>n. a n \<ge> 0\<close> by (simp add: sum_nonneg) 
    ultimately have \<open>sum a {Suc N..m} \<ge> e\<close>
      using \<open>e \<le> sum a {Suc n..m}\<close> by linarith
    have \<open>finite {0..N}\<close>
      by simp
    have \<open>finite {Suc N..m}\<close>
      by simp
    moreover have \<open>{0..N} \<union> {Suc N..m} = {0..m}\<close>
      using Set_Interval.ivl_disj_un(7) \<open>Suc N \<le> m\<close> by auto          
    moreover have \<open>{0..N} \<inter> {Suc N..m} = {}\<close>
      by simp
    ultimately have \<open>sum a {0..N} + sum a {Suc N..m} =  sum a {0..m}\<close> 
      by (metis \<open>finite {0..N}\<close> sum.union_disjoint)    
    hence \<open>e + k * e \<le> sum a {0..m}\<close>
      using \<open>ereal (real k * e) \<le> s\<close> \<open>s = ereal (sum a {0..N})\<close> \<open>e \<le> sum a {Suc N..m}\<close> by auto 
    moreover have \<open>e + k * e = (Suc k) * e\<close>
      by (simp add: semiring_normalization_rules(3))
    ultimately have \<open>(Suc k) * e \<le> sum a {0..m}\<close>
      by linarith
    hence \<open>ereal ((Suc k) * e) \<le> sum a {0..m}\<close>
      by auto
    moreover have \<open>sum a {0..m}\<in>S\<close>
      unfolding S_def by blast
    ultimately show ?case by blast
  qed
  hence \<open>\<exists>s\<in>S. (real n) \<le> s\<close> for n
    by (meson assms(2) ereal_le_le ex_less_of_nat_mult less_le_not_le)
  hence  \<open>Sup S = \<infinity>\<close>
    using Sup_le_iff Sup_subset_mono dual_order.strict_trans1 leD less_PInf_Ex_of_nat subsetI 
    by metis
  hence Sup: \<open>Sup ((range (\<lambda> n. (sum a  {0..n})))::ereal set) = \<infinity>\<close> using S_def 
    by blast
  have \<open>incseq (\<lambda>n. (sum a  {..<n}))\<close>
    using \<open>\<And>n. a n \<ge> 0\<close> using Extended_Real.incseq_sumI by auto
  hence \<open>incseq (\<lambda>n. (sum a  {..< Suc n}))\<close>
    by (meson incseq_Suc_iff)
  hence \<open>incseq (\<lambda>n. (sum a  {0..n})::ereal)\<close>
    using incseq_ereal by (simp add: atLeast0AtMost lessThan_Suc_atMost) 
  hence \<open>(\<lambda>n. sum a  {0..n}) \<longlonglongrightarrow> Sup (range (\<lambda>n. (sum a  {0..n})::ereal))\<close>
    using LIMSEQ_SUP by auto
  thus ?thesis using Sup PInfty_neq_ereal by auto 
qed

lemma sum_Cauchy_positive:
  fixes a ::\<open>_ \<Rightarrow> real\<close>
  assumes \<open>\<And>n. a n \<ge> 0\<close> and \<open>\<exists>K. \<forall>n. (sum a  {0..n}) \<le> K\<close>
  shows \<open>Cauchy (\<lambda>n. sum a {0..n})\<close>
  text\<open>
  Explanation: If a series of nonnegative reals is bounded, then the series is 
  Cauchy.
\<close>
proof (unfold Cauchy_altdef2, rule, rule)
  fix e::real
  assume \<open>e>0\<close>       
  have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
  proof(rule classical)
    assume \<open>\<not>(\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e)\<close>
    hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> \<not>(sum a {Suc n..m} < e)\<close>
      by blast
    hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      by fastforce
    hence \<open>(\<lambda>n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
      using non_Cauchy_unbounded \<open>0 < e\<close> assms(1) by blast
    from  \<open>\<exists>K. \<forall>n. sum a  {0..n} \<le> K\<close>
    obtain K where  \<open>\<forall>n. sum a {0..n} \<le> K\<close>
      by blast
    from  \<open>(\<lambda>n. sum a {0..n})  \<longlonglongrightarrow> \<infinity>\<close>
    have \<open>\<forall>B. \<exists>N. \<forall>n\<ge>N. (\<lambda> n. (sum a  {0..n}) ) n \<ge> B\<close>
      using Lim_PInfty by simp
    hence  \<open>\<exists>n. (sum a {0..n}) \<ge> K+1\<close>
      using ereal_less_eq(3) by blast        
    thus ?thesis using  \<open>\<forall>n. (sum a  {0..n}) \<le> K\<close> by smt       
  qed
  have \<open>sum a {Suc n..m} = sum a {0..m} - sum a {0..n}\<close>
    if "m > n" for m n
    apply (simp add: that atLeast0AtMost) using sum_up_index_split 
    by (smt less_imp_add_positive that)
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close> by smt     
  from \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
  obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    by blast
  moreover have \<open>m > n \<Longrightarrow> sum a {0..m} \<ge> sum a {0..n}\<close> for m n
    using \<open>\<And> n. a n \<ge> 0\<close> by (simp add: sum_mono2)
  ultimately have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    by auto
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m \<ge> n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    by (metis \<open>0 < e\<close> abs_zero cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' 
        less_irrefl_nat linorder_neqE_nat zero_less_diff)      
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    by (metis abs_minus_commute nat_le_linear)
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    by (simp add: dist_real_def)      
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close> by blast
  thus \<open>\<exists>N. \<forall>n\<ge>N. dist (sum a {0..n}) (sum a {0..N}) < e\<close> by auto
qed

lemma convergent_series_Cauchy:
  fixes a::\<open>nat \<Rightarrow> real\<close> and \<phi>::\<open>nat \<Rightarrow> 'a::metric_space\<close>
  assumes \<open>\<exists>M. \<forall>n. sum a {0..n} \<le> M\<close> and \<open>\<And>n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
  shows \<open>Cauchy \<phi>\<close>
  text\<open>
  Explanation: Let \<^term>\<open>a\<close> be a real-valued sequence and let \<^term>\<open>\<phi>\<close> be sequence in a metric space.
  If the partial sums of \<^term>\<open>a\<close> are uniformly bounded and the distance between consecutive terms of \<^term>\<open>\<phi>\<close>
  are bounded by the sequence \<^term>\<open>a\<close>, then \<^term>\<open>\<phi>\<close> is Cauchy.\<close>
proof (unfold Cauchy_altdef2, rule, rule)
  fix e::real
  assume \<open>e > 0\<close>
  have \<open>\<And>k. a k \<ge> 0\<close>
    using \<open>\<And>n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close> dual_order.trans zero_le_dist by blast
  hence \<open>Cauchy (\<lambda>k. sum a {0..k})\<close>
    using  \<open>\<exists>M. \<forall>n. sum a {0..n} \<le> M\<close> sum_Cauchy_positive by blast
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    unfolding Cauchy_def using \<open>e > 0\<close> by blast
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    by blast
  have \<open>dist (sum a {0..m}) (sum a {0..n}) = sum a {Suc n..m}\<close> if \<open>n<m\<close> for m n
  proof -
    have \<open>n < Suc n\<close>
      by simp
    have \<open>finite {0..n}\<close>
      by simp
    moreover have \<open>finite {Suc n..m}\<close>
      by simp
    moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
      using \<open>n < Suc n\<close> \<open>n < m\<close> by auto
    moreover have  \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
      by simp
    ultimately have sum_plus: \<open>(sum a {0..n}) + sum a {Suc n..m} = (sum a {0..m})\<close>
      by (metis sum.union_disjoint)
    have \<open>dist (sum a {0..m}) (sum a {0..n}) = \<bar>(sum a {0..m}) - (sum a {0..n})\<bar>\<close>
      using dist_real_def by blast
    moreover have \<open>(sum a {0..m}) - (sum a {0..n}) = sum a {Suc n..m}\<close>
      using sum_plus by linarith 
    ultimately show ?thesis
      by (simp add: \<open>\<And>k. 0 \<le> a k\<close> sum_nonneg)
  qed
  hence sum_a: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
    by (metis \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>) 
  obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
    using sum_a \<open>e > 0\<close> by blast
  hence  \<open>\<forall>m. \<forall>n. Suc m \<ge> Suc M \<and> Suc n \<ge> Suc M \<and> Suc m > Suc n \<longrightarrow> sum a {Suc n..Suc m - 1} < e\<close>
    by simp
  hence  \<open>\<forall>m\<ge>1. \<forall>n\<ge>1. m \<ge> Suc M \<and> n \<ge> Suc M \<and> m > n \<longrightarrow> sum a {n..m - 1} < e\<close>
    by (metis Suc_le_D)
  hence sum_a2: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {n..m-1} < e\<close>
    by (meson add_leE)
  have \<open>dist (\<phi> (n+p+1)) (\<phi> n) \<le> sum a {n..n+p}\<close> for p n :: nat
  proof(induction p)
    case 0 thus ?case  by (simp add: assms(2))
  next
    case (Suc p) thus ?case
      by (smt Suc_eq_plus1 add_Suc_right add_less_same_cancel1 assms(2) dist_self dist_triangle2 
          gr_implies_not0 sum.cl_ivl_Suc)  
  qed
  hence \<open>m > n \<Longrightarrow> dist (\<phi> m) (\<phi> n) \<le> sum a {n..m-1}\<close> for m n :: nat
    by (metis Suc_eq_plus1 Suc_le_D diff_Suc_1  gr0_implies_Suc less_eq_Suc_le less_imp_Suc_add 
        zero_less_Suc)
  hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (\<phi> m) (\<phi> n) < e\<close> 
    using sum_a2 \<open>e > 0\<close> by smt
  thus "\<exists>N. \<forall>n\<ge>N. dist (\<phi> n) (\<phi> N) < e"
    using \<open>0 < e\<close> by fastforce
qed

unbundle notation_blinfun_apply

unbundle no_notation_norm

end
