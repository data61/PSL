(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in analysis\<close>

theory Missing_Analysis
  imports "HOL-Complex_Analysis.Complex_Analysis"
begin  

subsection \<open>More about paths\<close>
   
lemma pathfinish_offset[simp]:
  "pathfinish (\<lambda>t. g t - z) = pathfinish g - z"
  unfolding pathfinish_def by simp 
    
lemma pathstart_offset[simp]:
  "pathstart (\<lambda>t. g t - z) = pathstart g - z"
  unfolding pathstart_def by simp
    
lemma pathimage_offset[simp]:
  fixes g :: "_ \<Rightarrow> 'b::topological_group_add"
  shows "p \<in> path_image (\<lambda>t. g t - z) \<longleftrightarrow> p+z \<in> path_image g " 
unfolding path_image_def by (auto simp:algebra_simps)
  
lemma path_offset[simp]:
 fixes g :: "_ \<Rightarrow> 'b::topological_group_add"
 shows "path (\<lambda>t. g t - z) \<longleftrightarrow> path g"
unfolding path_def
proof 
  assume "continuous_on {0..1} (\<lambda>t. g t - z)" 
  hence "continuous_on {0..1} (\<lambda>t. (g t - z) + z)" 
    apply (rule continuous_intros)
    by (intro continuous_intros)
  then show "continuous_on {0..1} g" by auto
qed (auto intro:continuous_intros)   
  
lemma not_on_circlepathI:
  assumes "cmod (z-z0) \<noteq> \<bar>r\<bar>"
  shows "z \<notin> path_image (part_circlepath z0 r st tt)"
proof (rule ccontr)
  assume "\<not> z \<notin> path_image (part_circlepath z0 r st tt)"
  then have "z\<in>path_image (part_circlepath z0 r st tt)" by simp
  then obtain t where "t\<in>{0..1}" and *:"z = z0 + r * exp (\<i> * (linepath st tt t))"
    unfolding path_image_def image_def part_circlepath_def by blast
  define \<theta> where "\<theta> = linepath st tt t"
  then have "z-z0 = r * exp (\<i> * \<theta>)" using * by auto
  then have "cmod (z-z0) = cmod (r * exp (\<i> * \<theta>))" by auto
  also have "\<dots> = \<bar>r\<bar> * cmod (exp (\<i> * \<theta>))" by (simp add: norm_mult)
  also have "\<dots> = \<bar>r\<bar>" by auto
  finally have "cmod (z-z0) = \<bar>r\<bar>" .
  then show False using assms by auto
qed    

lemma circlepath_inj_on: 
  assumes "r>0"
  shows "inj_on (circlepath z r) {0..<1}"
proof (rule inj_onI)
  fix x y assume asm: "x \<in> {0..<1}" "y \<in> {0..<1}" "circlepath z r x = circlepath z r y"
  define c where "c=2 * pi * \<i>"
  have "c\<noteq>0" unfolding c_def by auto 
  from asm(3) have "exp (c * x) =exp (c * y)"
    unfolding circlepath c_def using \<open>r>0\<close> by auto
  then obtain n where "c * x =c * (y + of_int n)"
    by (auto simp add:exp_eq c_def algebra_simps)
  then have "x=y+n" using \<open>c\<noteq>0\<close>
    by (meson mult_cancel_left of_real_eq_iff)
  then show "x=y" using asm(1,2) by auto
qed

subsection \<open>More lemmas related to @{term winding_number}\<close>  
  
lemma winding_number_comp:
  assumes "open s" "f holomorphic_on s" "path_image \<gamma> \<subseteq> s"  
    "valid_path \<gamma>" "z \<notin> path_image (f \<circ> \<gamma>)" 
  shows "winding_number (f \<circ> \<gamma>) z = 1/(2*pi*\<i>)* contour_integral \<gamma> (\<lambda>w. deriv f w / (f w - z))"
proof -
  obtain spikes where "finite spikes" and \<gamma>_diff: "\<gamma> C1_differentiable_on {0..1} - spikes"
    using \<open>valid_path \<gamma>\<close> unfolding valid_path_def piecewise_C1_differentiable_on_def by auto  
  have "valid_path (f \<circ> \<gamma>)" 
    using valid_path_compose_holomorphic assms by blast
  moreover have "contour_integral (f \<circ> \<gamma>) (\<lambda>w. 1 / (w - z)) 
      = contour_integral \<gamma> (\<lambda>w. deriv f w / (f w - z))"
    unfolding contour_integral_integral
  proof (rule integral_spike[rule_format,OF negligible_finite[OF \<open>finite spikes\<close>]])
    fix t::real assume t:"t \<in> {0..1} - spikes"
    then have "\<gamma> differentiable at t" 
      using \<gamma>_diff unfolding C1_differentiable_on_eq by auto
    moreover have "f field_differentiable at (\<gamma> t)" 
    proof -
      have "\<gamma> t \<in> s" using \<open>path_image \<gamma> \<subseteq> s\<close> t unfolding path_image_def by auto 
      thus ?thesis 
        using \<open>open s\<close> \<open>f holomorphic_on s\<close>  holomorphic_on_imp_differentiable_at by blast
    qed
    ultimately show " deriv f (\<gamma> t) / (f (\<gamma> t) - z) * vector_derivative \<gamma> (at t) =
         1 / ((f \<circ> \<gamma>) t - z) * vector_derivative (f \<circ> \<gamma>) (at t)"
      apply (subst vector_derivative_chain_at_general)
      by (simp_all add:field_simps)
  qed
  moreover note \<open>z \<notin> path_image (f \<circ> \<gamma>)\<close> 
  ultimately show ?thesis
    apply (subst winding_number_valid_path)
    by simp_all
qed  
  
lemma winding_number_uminus_comp:
  assumes "valid_path \<gamma>" "- z \<notin> path_image \<gamma>" 
  shows "winding_number (uminus \<circ> \<gamma>) z = winding_number \<gamma> (-z)"
proof -
  define c where "c= 2 * pi * \<i>"
  have "winding_number (uminus \<circ> \<gamma>) z = 1/c * contour_integral \<gamma> (\<lambda>w. deriv uminus w / (-w-z)) "
  proof (rule winding_number_comp[of UNIV, folded c_def])
    show "open UNIV" "uminus holomorphic_on UNIV" "path_image \<gamma> \<subseteq> UNIV" "valid_path \<gamma>"
      using \<open>valid_path \<gamma>\<close> by (auto intro:holomorphic_intros)
    show "z \<notin> path_image (uminus \<circ> \<gamma>)" 
      unfolding path_image_compose using \<open>- z \<notin> path_image \<gamma>\<close> by auto
  qed
  also have "\<dots> = 1/c * contour_integral \<gamma> (\<lambda>w. 1 / (w- (-z)))"
    by (auto intro!:contour_integral_eq simp add:field_simps minus_divide_right)
  also have "\<dots> = winding_number \<gamma> (-z)"
    using winding_number_valid_path[OF \<open>valid_path \<gamma>\<close> \<open>- z \<notin> path_image \<gamma>\<close>,folded c_def]
    by simp
  finally show ?thesis by auto
qed  
  
lemma winding_number_comp_linear:
  assumes "c\<noteq>0" "valid_path \<gamma>" and not_image: "(z-b)/c \<notin> path_image \<gamma>"
  shows "winding_number ((\<lambda>x. c*x+b) \<circ> \<gamma>) z = winding_number \<gamma> ((z-b)/c)" (is "?L = ?R")
proof -
  define cc where "cc=1 / (complex_of_real (2 * pi) * \<i>)"
  define zz where "zz=(z-b)/c"
  have "?L = cc * contour_integral \<gamma> (\<lambda>w. deriv (\<lambda>x. c * x + b) w / (c * w + b - z))"
    apply (subst winding_number_comp[of UNIV,simplified])
    subgoal by (auto intro:holomorphic_intros)
    subgoal using \<open>valid_path \<gamma>\<close> .
    subgoal using not_image \<open>c\<noteq>0\<close> unfolding path_image_compose by auto
    subgoal unfolding cc_def by auto
    done
  also have "\<dots> = cc * contour_integral \<gamma> (\<lambda>w.1 / (w - zz))"
  proof -
    have "deriv (\<lambda>x. c * x + b) = (\<lambda>x. c)"
      by (auto intro:derivative_intros) 
    then show ?thesis
      unfolding zz_def cc_def using \<open>c\<noteq>0\<close>
      by (auto simp:field_simps)
  qed
  also have "\<dots> = winding_number \<gamma> zz"
    using winding_number_valid_path[OF \<open>valid_path \<gamma>\<close> not_image,folded zz_def cc_def]
    by simp
  finally show "winding_number ((\<lambda>x. c * x + b) \<circ> \<gamma>) z = winding_number \<gamma> zz" .
qed  
 
end
