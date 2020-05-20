(*
  File:   Banach_Steinhaus.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Banach-Steinhaus theorem\<close>

theory Banach_Steinhaus
  imports Banach_Steinhaus_Missing
begin

text \<open>
  We formalize Banach-Steinhaus theorem as theorem @{text banach_steinhaus}. This theorem was 
  originally proved in Banach-Steinhaus's paper~\cite{banach1927principe}. For the proof, we follow
  Sokal's approach~\cite{sokal2011really}. Furthermore, we prove as a corollary a result about
  pointwise convergent sequences of bounded operators whose domain is a Banach space.
\<close>

subsection \<open>Preliminaries for Sokal's proof of Banach-Steinhaus theorem\<close>

lemma linear_plus_norm:
  includes notation_norm
  assumes \<open>linear f\<close>
  shows \<open>\<parallel>f \<xi>\<parallel> \<le> max \<parallel>f (x + \<xi>)\<parallel> \<parallel>f (x - \<xi>)\<parallel>\<close>
  text \<open>
  Explanation: For arbitrary \<^term>\<open>x\<close> and a linear operator \<^term>\<open>f\<close>,
  \<^term>\<open>norm (f \<xi>)\<close> is upper bounded by the maximum of the norms
  of the shifts of \<^term>\<open>f\<close> (i.e., \<^term>\<open>f (x + \<xi>)\<close> and \<^term>\<open>f (x - \<xi>)\<close>).
\<close>
proof-
  have \<open>norm (f \<xi>) = norm ( (inverse (of_nat 2)) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>)) )\<close>
    by (smt add_diff_cancel_left' assms diff_add_cancel diff_diff_add linear_diff midpoint_def 
        midpoint_plus_self of_nat_1 of_nat_add one_add_one scaleR_half_double)
  also have \<open>\<dots> = inverse (of_nat 2) * norm (f (x + \<xi>) - f (x - \<xi>))\<close>
    using Real_Vector_Spaces.real_normed_vector_class.norm_scaleR by simp
  also have \<open>\<dots> \<le> inverse (of_nat 2) * (norm (f (x + \<xi>)) + norm (f (x - \<xi>)))\<close>
    by (simp add: norm_triangle_ineq4)
  also have \<open>\<dots> \<le>  max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    by auto
  finally show ?thesis by blast
qed

lemma onorm_Sup_on_ball:
  includes notation_norm
  assumes \<open>r > 0\<close>
  shows "\<parallel>f\<parallel> \<le> Sup ( (\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball x r) ) / r"
  text \<open>
  Explanation: Let \<^term>\<open>f\<close> be a bounded operator and let \<^term>\<open>x\<close> be a point. For any \<^term>\<open>r > 0\<close>, 
  the operator norm of \<^term>\<open>f\<close> is bounded above by the supremum of $f$ applied to the open ball of 
  radius \<^term>\<open>r\<close> around \<^term>\<open>x\<close>, divided by \<^term>\<open>r\<close>.
\<close>
proof-
  have bdd_above_3: \<open>bdd_above ((\<lambda>x. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 r))\<close>
  proof -
    obtain M where \<open>\<And> \<xi>.  \<parallel>f *\<^sub>v \<xi>\<parallel> \<le> M * norm \<xi>\<close> and \<open>M \<ge> 0\<close>
      using norm_blinfun norm_ge_zero by blast      
    hence \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> \<parallel>f *\<^sub>v \<xi>\<parallel> \<le> M * r\<close>
      using \<open>r > 0\<close> by (smt mem_ball_0 mult_left_mono) 
    thus ?thesis by (meson bdd_aboveI2)     
  qed
  have bdd_above_2: \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r))\<close>
  proof-
    have \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v x\<parallel>) ` (ball 0 r))\<close>
      by auto          
    moreover have \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v \<xi>\<parallel>) ` (ball 0 r))\<close>
      using bdd_above_3 by blast
    ultimately have \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v x\<parallel> + \<parallel>f *\<^sub>v \<xi>\<parallel>) ` (ball 0 r))\<close>
      by (rule bdd_above_plus)
    then obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> \<parallel>f *\<^sub>v x\<parallel> + \<parallel>f *\<^sub>v \<xi>\<parallel> \<le> M\<close>
      unfolding bdd_above_def by (meson image_eqI)
    moreover have \<open>\<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<le> \<parallel>f *\<^sub>v x\<parallel> + \<parallel>f *\<^sub>v \<xi>\<parallel>\<close> for \<xi>
      by (simp add: blinfun.add_right norm_triangle_ineq)                
    ultimately have \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<le> M\<close>
      by (simp add: blinfun.add_right norm_triangle_le)
    thus ?thesis by (meson bdd_aboveI2)                          
  qed 
  have bdd_above_4: \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close>
  proof-
    obtain K where K_def: \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<le> K\<close>
      using  \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close> unfolding bdd_above_def 
      by (meson image_eqI)
    have \<open>\<xi> \<in> ball (0::'a) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close> for \<xi>
      by auto
    thus ?thesis by (metis K_def ab_group_add_class.ab_diff_conv_add_uminus bdd_aboveI2)
  qed
  have bdd_above_1: \<open>bdd_above ((\<lambda> \<xi>. max \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>  \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close>
  proof-
    have \<open>bdd_above ((\<lambda> \<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r))\<close>
      using bdd_above_2 by blast
    moreover have \<open>bdd_above ((\<lambda> \<xi>.  \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close>
      using bdd_above_4 by blast
    ultimately show ?thesis
      unfolding max_def apply auto apply (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
      by (meson bdd_above_Int1 bdd_above_mono image_Int_subset)   
  qed 
  have bdd_above_6: \<open>bdd_above ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball x r)\<close>
  proof-
    have \<open>bounded (ball x r)\<close>
      by simp            
    hence \<open>bounded ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball x r)\<close>
      by (metis (no_types) add.left_neutral bdd_above_2 bdd_above_norm bounded_norm_comp 
          image_add_ball image_image)
    thus ?thesis
      by (simp add: bounded_imp_bdd_above)
  qed
  have norm_1: \<open>(\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` ball 0 r = (\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball x r\<close>
    by (metis add.right_neutral ball_translation image_image)   
  have bdd_above_5: \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
    by (simp add: bdd_above_2)   
  have norm_2: \<open>\<parallel>\<xi>\<parallel> < r \<Longrightarrow> \<parallel>f *\<^sub>v (x - \<xi>)\<parallel> \<in> (\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` ball 0 r\<close> for \<xi>
  proof-
    assume \<open>\<parallel>\<xi>\<parallel> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    thus ?thesis 
      by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus image_iff) 
  qed
  have norm_2': \<open>\<parallel>\<xi>\<parallel> < r \<Longrightarrow> \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<in> (\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` ball 0 r\<close> for \<xi>
  proof-
    assume \<open>norm \<xi> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    thus ?thesis 
      by (metis (no_types, lifting) diff_minus_eq_add image_iff)          
  qed
  have bdd_above_6: \<open>bdd_above ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` ball 0 r)\<close>
    by (simp add: bdd_above_4)   
  have Sup_2: \<open>(SUP \<xi>\<in>ball 0 r. max \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) =
                 max (SUP \<xi>\<in>ball 0 r. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) (SUP \<xi>\<in>ball 0 r. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>)\<close>
  proof-
    have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto
    moreover have \<open>bdd_above ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` ball 0 r)\<close>
      using bdd_above_5 by blast
    moreover have \<open>bdd_above ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` ball 0 r)\<close>
      using bdd_above_6 by blast
    ultimately show ?thesis
      using max_Sup
      by (metis (mono_tags, lifting) Banach_Steinhaus_Missing.pointwise_max_def image_cong) 
  qed 
  have Sup_3': \<open>\<parallel>\<xi>\<parallel> < r \<Longrightarrow> \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<in> (\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` ball 0 r\<close> for \<xi>::'a
    by (simp add: norm_2')
  have Sup_3'': \<open>\<parallel>\<xi>\<parallel> < r \<Longrightarrow> \<parallel>f *\<^sub>v (x - \<xi>)\<parallel> \<in> (\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` ball 0 r\<close> for \<xi>::'a
    by (simp add: norm_2)  
  have Sup_3: \<open>max (SUP \<xi>\<in>ball 0 r. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) (SUP \<xi>\<in>ball 0 r.  \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) =
        (SUP \<xi>\<in>ball 0 r. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>)\<close>
  proof-
    have \<open>(\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r) = (\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r)\<close>
      apply auto using Sup_3' apply auto using Sup_3'' by blast
    hence \<open>Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r))=Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close>
      by simp
    thus ?thesis by simp
  qed
  have Sup_1: \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 r)) \<le> Sup ( (\<lambda>\<xi>. \<parallel>f *\<^sub>v \<xi>\<parallel>) ` (ball x r) )\<close> 
  proof-
    have \<open>(\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) \<xi> \<le> max \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>\<close> for \<xi>
      apply(rule linear_plus_norm) apply (rule bounded_linear.linear)
      by (simp add: blinfun.bounded_linear_right)
    moreover have \<open>bdd_above ((\<lambda> \<xi>. max \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>  \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close> 
      using bdd_above_1 by blast
    moreover have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto      
    ultimately have \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 r)) \<le>
                     Sup ((\<lambda>\<xi>. max \<parallel>f *\<^sub>v (x + \<xi>)\<parallel> \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r))\<close>
      using cSUP_mono by smt 
    also have \<open>\<dots> = max (Sup ((\<lambda>\<xi>.  \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r)))
                        (Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x - \<xi>)\<parallel>) ` (ball 0 r)))\<close> 
      using Sup_2 by blast
    also have \<open>\<dots> = Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v (x + \<xi>)\<parallel>) ` (ball 0 r))\<close>
      using Sup_3 by blast
    also have \<open>\<dots> = Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v \<xi>\<parallel>) ` (ball x r))\<close>
      by (metis  add.right_neutral ball_translation image_image)      
    finally show ?thesis by blast
  qed
  have \<open>\<parallel>f\<parallel> = (SUP x\<in>ball 0 r. \<parallel>f *\<^sub>v x\<parallel>) / r\<close>
    using \<open>0 < r\<close> onorm_r by blast
  moreover have \<open>Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` (ball 0 r)) / r \<le> Sup ((\<lambda>\<xi>. \<parallel>f *\<^sub>v \<xi>\<parallel>) ` (ball x r)) / r\<close>
    using Sup_1 \<open>0 < r\<close> divide_right_mono by fastforce 
  ultimately have \<open>\<parallel>f\<parallel> \<le> Sup ((\<lambda>t. \<parallel>f *\<^sub>v t\<parallel>) ` ball x r) / r\<close>
    by simp
  thus ?thesis by simp    
qed

lemma onorm_Sup_on_ball':
  includes notation_norm
  assumes \<open>r > 0\<close> and \<open>\<tau> < 1\<close>
  shows \<open>\<exists>\<xi>\<in>ball x r.  \<tau> * r * \<parallel>f\<parallel> \<le> \<parallel>f *\<^sub>v \<xi>\<parallel>\<close>
  text \<open>                 
  In the proof of Banach-Steinhaus theorem, we will use this variation of the 
  lemma @{text onorm_Sup_on_ball}.

  Explanation: Let \<^term>\<open>f\<close> be a bounded operator, let \<^term>\<open>x\<close> be a point and let \<^term>\<open>r\<close> be a 
  positive real number. For any real number \<^term>\<open>\<tau> < 1\<close>, there is a point \<^term>\<open>\<xi>\<close> in the open ball 
  of radius \<^term>\<open>r\<close> around \<^term>\<open>x\<close> such that \<^term>\<open>\<tau> * r * \<parallel>f\<parallel> \<le> \<parallel>f *\<^sub>v \<xi>\<parallel>\<close>.
\<close>
proof(cases  \<open>f = 0\<close>)
  case True
  thus ?thesis by (metis assms(1) centre_in_ball mult_zero_right norm_zero order_refl 
        zero_blinfun.rep_eq) 
next
  case False
  have bdd_above_1: \<open>bdd_above ((\<lambda>t. \<parallel>(*\<^sub>v) f t\<parallel>) ` ball x r)\<close> for f::\<open>'a \<Rightarrow>\<^sub>L 'b\<close>
    using assms(1) bounded_linear_image by (simp add: bounded_linear_image 
        blinfun.bounded_linear_right bounded_imp_bdd_above bounded_norm_comp) 
  have  \<open>norm f > 0\<close>
    using \<open>f \<noteq> 0\<close> by auto
  have \<open>norm f \<le>  Sup ( (\<lambda>\<xi>.  \<parallel>(*\<^sub>v) f \<xi>\<parallel>) ` (ball x r) ) / r\<close>
    using \<open>r > 0\<close> by (simp add: onorm_Sup_on_ball)  
  hence \<open>r * norm f \<le>  Sup ( (\<lambda>\<xi>.  \<parallel>(*\<^sub>v) f \<xi>\<parallel>) ` (ball x r) )\<close>
    using \<open>0 < r\<close> by (smt divide_strict_right_mono nonzero_mult_div_cancel_left) 
  moreover have \<open>\<tau> * r * norm f < r * norm f\<close>
    using  \<open>\<tau> < 1\<close> using \<open>0 < norm f\<close> \<open>0 < r\<close> by auto
  ultimately have \<open>\<tau> * r * norm f < Sup ( (norm \<circ> ((*\<^sub>v) f)) ` (ball x r) )\<close>
    by simp
  moreover have \<open>(norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) \<noteq> {}\<close>
    using \<open>0 < r\<close> by auto    
  moreover have \<open>bdd_above ((norm \<circ> ( (*\<^sub>v) f)) ` (ball x r))\<close>
    using bdd_above_1 apply transfer by simp
  ultimately have \<open>\<exists>t \<in> (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r). \<tau> * r * norm f < t\<close> 
    by (simp add: less_cSup_iff)    
  thus ?thesis by (smt comp_def image_iff) 
qed

subsection \<open>Banach-Steinhaus theorem\<close>

theorem banach_steinhaus:
  fixes f::\<open>'c \<Rightarrow> ('a::banach \<Rightarrow>\<^sub>L 'b::real_normed_vector)\<close>
  assumes \<open>\<And>x. bounded (range (\<lambda>n. (f n) *\<^sub>v x))\<close>
  shows  \<open>bounded (range f)\<close>
  text\<open>
  This is Banach-Steinhaus Theorem.

  Explanation: If a family of bounded operators on a Banach space
  is pointwise bounded, then it is uniformly bounded.
\<close>
proof(rule classical)
  assume \<open>\<not>(bounded (range f))\<close>
  have sum_1: \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
  proof-
    have \<open>summable (\<lambda>n. (inverse (real_of_nat 3))^n)\<close>
      using Series.summable_geometric_iff [where c = "inverse (real_of_nat 3)"] by auto
    moreover have \<open>(inverse (real_of_nat 3))^n = inverse (real_of_nat 3^n)\<close> for n::nat
      using power_inverse by blast        
    ultimately have \<open>summable (\<lambda>n. inverse (real_of_nat 3^n))\<close>
      by auto
    hence \<open>bounded (range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}))\<close>
      using summable_imp_sums_bounded[where f = "(\<lambda>n. inverse (real_of_nat 3^n))"]
        lessThan_atLeast0 by auto
    hence \<open>\<exists>M. \<forall>h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})). norm h \<le> M\<close>
      using bounded_iff by blast
    then obtain M where \<open>h\<in>range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}) \<Longrightarrow> norm h \<le> M\<close> 
      for h
      by blast      
    have sum_2: \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n
    proof-
      have  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..< Suc n}) \<le> M\<close>
        using \<open>\<And>h. h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})) \<Longrightarrow> norm h \<le> M\<close> 
        by blast
      hence  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
        by (simp add: atLeastLessThanSuc_atLeastAtMost)        
      hence  \<open>(sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
        by auto
      thus ?thesis  by blast
    qed
    have \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n 
      using sum_2 by blast
    thus ?thesis  by blast
  qed
  have \<open>of_rat 2/3 < (1::real)\<close>
    by auto
  hence \<open>\<forall>g::'a \<Rightarrow>\<^sub>L 'b. \<forall>x. \<forall>r. \<exists>\<xi>. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> (\<xi>\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm ((*\<^sub>v) g \<xi>))\<close> 
    using onorm_Sup_on_ball' by blast
  hence \<open>\<exists>\<xi>. \<forall>g::'a \<Rightarrow>\<^sub>L 'b. \<forall>x. \<forall>r. g \<noteq> 0 \<and> r > 0
           \<longrightarrow> ((\<xi> g x r)\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm ((*\<^sub>v) g (\<xi> g x r)))\<close> 
    by metis
  then obtain \<xi> where f1: \<open>\<lbrakk>g \<noteq> 0; r > 0\<rbrakk> \<Longrightarrow> 
        \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm ((*\<^sub>v) g (\<xi> g x r))\<close>
    for g::\<open>'a \<Rightarrow>\<^sub>L 'b\<close> and x and r
    by blast
  have \<open>\<forall>n. \<exists>k. norm (f k) \<ge> 4^n\<close>
    using \<open>\<not>(bounded (range f))\<close> by (metis (mono_tags, hide_lams) boundedI image_iff linear)
  hence  \<open>\<exists>k. \<forall>n. norm (f (k n)) \<ge> 4^n\<close>
    by metis
  hence  \<open>\<exists>k. \<forall>n. norm ((f \<circ> k) n) \<ge> 4^n\<close>
    by simp
  then obtain k where \<open>norm ((f \<circ> k) n) \<ge> 4^n\<close> for n
    by blast
  define T where \<open>T = f \<circ> k\<close>
  have \<open>T n \<in> range f\<close> for n
    unfolding T_def by simp        
  have \<open>norm (T n) \<ge> of_nat (4^n)\<close> for n
    unfolding T_def using \<open>\<And> n. norm ((f \<circ> k) n) \<ge> 4^n\<close> by auto
  hence \<open>T n \<noteq> 0\<close> for n
    by (smt T_def \<open>\<And>n. 4 ^ n \<le> norm ((f \<circ> k) n)\<close> norm_zero power_not_zero zero_le_power)
  have \<open>inverse (of_nat 3^n) > (0::real)\<close> for n
    by auto
  define y::\<open>nat \<Rightarrow> 'a\<close> where \<open>y = rec_nat 0 (\<lambda>n x. \<xi> (T n) x (inverse (of_nat 3^n)))\<close>
  have \<open>y (Suc n) \<in> ball (y n) (inverse (of_nat 3^n))\<close> for n
    using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
  hence \<open>norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> for n
    unfolding ball_def apply auto using dist_norm by (smt norm_minus_commute) 
  moreover have \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
    using sum_1 by blast
  moreover have \<open>Cauchy y\<close>
    using convergent_series_Cauchy[where a = "\<lambda>n. inverse (of_nat 3^n)" and \<phi> = y] dist_norm
    by (metis calculation(1) calculation(2))
  hence \<open>\<exists> x. y \<longlonglongrightarrow> x\<close>
    by (simp add: convergent_eq_Cauchy)
  then obtain x where \<open>y \<longlonglongrightarrow> x\<close>
    by blast
  have norm_2: \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
  proof-
    have \<open>inverse (real_of_nat 3) < 1\<close>
      by simp        
    moreover have \<open>y 0 = 0\<close>
      using y_def by auto
    ultimately have \<open>norm (x - y (Suc n)) 
    \<le> (inverse (of_nat 3)) * inverse (1 - (inverse (of_nat 3))) * ((inverse (of_nat 3)) ^ n)\<close>
      using bound_Cauchy_to_lim[where c = "inverse (of_nat 3)" and y = y and x = x]
        power_inverse semiring_norm(77)  \<open>y \<longlonglongrightarrow> x\<close>
        \<open>\<And> n. norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> by (metis divide_inverse)
    moreover have \<open>inverse (real_of_nat 3) * inverse (1 - (inverse (of_nat 3)))
                   = inverse (of_nat 2)\<close>
      by auto
    ultimately show ?thesis 
      by (metis power_inverse) 
  qed
  have \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
    using norm_2 by blast
  have \<open>\<exists> M. \<forall> n. norm ((*\<^sub>v) (T n) x) \<le> M\<close>
    unfolding T_def apply auto
    by (metis \<open>\<And>x. bounded (range (\<lambda>n. (*\<^sub>v) (f n) x))\<close> bounded_iff rangeI)
  then obtain M where \<open>norm ((*\<^sub>v) (T n) x) \<le> M\<close> for n
    by blast
  have norm_1: \<open>norm (T n) * norm (y (Suc n) - x) + norm ((*\<^sub>v) (T n) x)
       \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) + norm ((*\<^sub>v) (T n) x)\<close> for n
  proof-   
    have \<open>norm (y (Suc n) - x) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
      using \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> 
      by (simp add: norm_minus_commute)
    moreover have \<open>norm (T n) \<ge> 0\<close>
      by auto
    ultimately have \<open>norm (T n) * norm (y (Suc n) - x) 
                     \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n)\<close>
      by (simp add: \<open>\<And>n. T n \<noteq> 0\<close>)
    thus ?thesis by simp      
  qed 
  have inverse_2: \<open>(inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n) 
                  \<le> norm ((*\<^sub>v) (T n) x)\<close> for n
  proof-
    have \<open>(of_rat 2/3)*(inverse (of_nat 3^n))*norm (T n) \<le> norm ((*\<^sub>v) (T n) (y (Suc n)))\<close> 
      using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
    also have \<open>\<dots> = norm ((*\<^sub>v) (T n) ((y (Suc n) - x) + x))\<close>
      by auto
    also have \<open>\<dots> = norm ((*\<^sub>v) (T n) (y (Suc n) - x) + (*\<^sub>v) (T n) x)\<close>
      apply transfer apply auto by (metis diff_add_cancel linear_simps(1))
    also have \<open>\<dots> \<le> norm ((*\<^sub>v) (T n) (y (Suc n) - x)) + norm ((*\<^sub>v) (T n) x)\<close>
      by (simp add: norm_triangle_ineq)
    also have \<open>\<dots> \<le> norm (T n) * norm (y (Suc n) - x) + norm ((*\<^sub>v) (T n) x)\<close>
      apply transfer apply auto using onorm by auto 
    also have \<open>\<dots> \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n) 
                + norm ((*\<^sub>v) (T n) x)\<close>
      using norm_1 by blast
    finally have \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n)
                \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) 
                + norm ((*\<^sub>v) (T n) x)\<close>
      by blast
    hence \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n) 
             - inverse (real 2) * inverse (real 3 ^ n) * norm (T n) \<le> norm ((*\<^sub>v) (T n) x)\<close>
      by linarith
    moreover have \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n) 
             - inverse (real 2) * inverse (real 3 ^ n) * norm (T n)
             = (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close>
      by fastforce
    ultimately show \<open>(inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n) \<le> norm ((*\<^sub>v) (T n) x)\<close>
      by linarith      
  qed
  have inverse_3: \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
                    \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> for n
  proof-
    have \<open>of_rat (4/3)^n = inverse (real 3 ^ n) * (of_nat 4^n)\<close>
      apply auto by (metis divide_inverse_commute of_rat_divide power_divide of_rat_numeral_eq) 
    also have \<open>\<dots> \<le>  inverse (real 3 ^ n) * norm (T n)\<close>
      using \<open>\<And>n. norm (T n) \<ge> of_nat (4^n)\<close> by simp
    finally have \<open>of_rat (4/3)^n \<le> inverse (real 3 ^ n) * norm (T n)\<close>
      by blast
    moreover have \<open>inverse (of_nat 6) > (0::real)\<close>
      by auto
    ultimately show ?thesis by auto
  qed
  have inverse_1: \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
  proof-
    have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
          \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> 
      using inverse_3 by blast
    also have \<open>\<dots> \<le> norm ((*\<^sub>v) (T n) x)\<close> 
      using inverse_2 by blast
    finally have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> norm ((*\<^sub>v) (T n) x)\<close>
      by auto
    thus ?thesis using \<open>\<And> n. norm ((*\<^sub>v) (T n) x) \<le> M\<close> by smt
  qed
  have \<open>\<exists>n. M < (inverse (of_nat 6)) * (of_rat (4/3)^n)\<close>
    using Real.real_arch_pow by auto
  moreover have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
    using inverse_1 by blast                      
  ultimately show ?thesis by smt
qed

subsection \<open>A consequence of Banach-Steinhaus theorem\<close>

corollary bounded_linear_limit_bounded_linear:
  fixes f::\<open>nat \<Rightarrow> ('a::banach \<Rightarrow>\<^sub>L 'b::real_normed_vector)\<close>
  assumes \<open>\<And>x. convergent (\<lambda>n. (f n) *\<^sub>v x)\<close>
  shows  \<open>\<exists>g. (\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> (*\<^sub>v) g\<close>
  text\<open>
  Explanation: If a sequence of bounded operators on a Banach space converges
  pointwise, then the limit is also a bounded operator.
\<close>
proof-
  have \<open>\<exists>l. (\<lambda>n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> l\<close> for x
    by (simp add:  \<open>\<And>x. convergent (\<lambda>n. (*\<^sub>v) (f n) x)\<close> convergentD)
  hence \<open>\<exists>F. (\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    unfolding pointwise_convergent_to_def by metis
  obtain F where \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    using \<open>\<exists>F. (\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> by auto
  have \<open>\<And>x. (\<lambda> n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer
    by (simp add: pointwise_convergent_to_def)
  have \<open>bounded (range f)\<close>
    using \<open>\<And>x. convergent (\<lambda>n. (*\<^sub>v) (f n) x)\<close> banach_steinhaus
      \<open>\<And>x. \<exists>l. (\<lambda>n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> l\<close> convergent_imp_bounded by blast
  have norm_f_n: \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
    unfolding bounded_def
    by (meson UNIV_I \<open>bounded (range f)\<close> bounded_iff image_eqI)
  have \<open>isCont (\<lambda> t::'b. norm t) y\<close> for y::'b
    using Limits.isCont_norm by simp
  hence \<open>(\<lambda> n. norm ((*\<^sub>v) (f n) x)) \<longlonglongrightarrow> (norm (F x))\<close> for x
    using \<open>\<And> x::'a. (\<lambda> n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close> by (simp add: tendsto_norm)
  hence norm_f_n_x: \<open>\<exists> M. \<forall> n. norm ((*\<^sub>v) (f n) x) \<le> M\<close> for x
    using Elementary_Metric_Spaces.convergent_imp_bounded
    by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
  have norm_f: \<open>\<exists>K. \<forall>n. \<forall>x. norm ((*\<^sub>v) (f n) x) \<le> norm x * K\<close>
  proof-
    have \<open>\<exists> M. \<forall> n. norm ((*\<^sub>v) (f n) x) \<le> M\<close> for x
      using norm_f_n_x  \<open>\<And>x. (\<lambda>n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close> by blast
    hence \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      using norm_f_n by simp 
    then obtain M::real where \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by blast
    have \<open>\<forall> n. \<forall>x. norm ((*\<^sub>v) (f n) x) \<le> norm x * norm (f n)\<close>
      apply transfer apply auto by (metis mult.commute onorm) 
    thus  ?thesis using \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl 
          real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)
  qed 
  have norm_F_x: \<open>\<exists>K. \<forall>x. norm (F x) \<le> norm x * K\<close>
  proof-
    have "\<exists>K. \<forall>n. \<forall>x. norm ((*\<^sub>v) (f n) x) \<le> norm x * K"
      using norm_f \<open>\<And>x. (\<lambda>n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close> by auto
    thus ?thesis
      using  \<open>\<And> x::'a. (\<lambda> n. (*\<^sub>v) (f n)  x) \<longlonglongrightarrow> F x\<close> apply transfer 
      by (metis Lim_bounded tendsto_norm)   
  qed
  have \<open>linear F\<close>
  proof(rule linear_limit_linear)
    show \<open>linear ((*\<^sub>v) (f n))\<close> for n
      apply transfer apply auto by (simp add: bounded_linear.linear) 
    show \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
      using \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> by auto
  qed
  moreover have \<open>bounded_linear_axioms F\<close>
    using norm_F_x by (simp add: \<open>\<And>x. (\<lambda>n. (*\<^sub>v) (f n) x) \<longlonglongrightarrow> F x\<close> bounded_linear_axioms_def) 
  ultimately have \<open>bounded_linear F\<close> 
    unfolding bounded_linear_def by blast
  hence \<open>\<exists>g. (*\<^sub>v) g = F\<close>
    using bounded_linear_Blinfun_apply by auto
  thus ?thesis using \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer by auto
qed

end
