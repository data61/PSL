(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Cauchy's index theorem\<close>

theory Cauchy_Index_Theorem imports 
  "HOL-Complex_Analysis.Complex_Analysis"
  "Sturm_Tarski.Sturm_Tarski"
  "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
  Missing_Transcendental
  Missing_Algebraic
  Missing_Analysis
begin

text \<open>This theory formalises Cauchy indices on the complex plane and relate them to winding numbers\<close>

subsection \<open>Misc\<close>
  
(*refined version of the library one with the same name by dropping unnecessary assumptions*) 
lemma atMostAtLeast_subset_convex:
  fixes C :: "real set"
  assumes "convex C"
    and "x \<in> C" "y \<in> C" 
  shows "{x .. y} \<subseteq> C"
proof safe
  fix z assume z: "z \<in> {x .. y}"
  have "z \<in> C" if *: "x < z" "z < y"
  proof -
    let ?\<mu> = "(y - z) / (y - x)"
    have "0 \<le> ?\<mu>" "?\<mu> \<le> 1"
      using assms * by (auto simp: field_simps)
    then have comb: "?\<mu> * x + (1 - ?\<mu>) * y \<in> C"
      using assms iffD1[OF convex_alt, rule_format, of C y x ?\<mu>]
      by (simp add: algebra_simps)
    have "?\<mu> * x + (1 - ?\<mu>) * y = (y - z) * x / (y - x) + (1 - (y - z) / (y - x)) * y"
      by (auto simp: field_simps)
    also have "\<dots> = ((y - z) * x + (y - x - (y - z)) * y) / (y - x)"
      using * by (simp only: add_divide_distrib) (auto simp: field_simps)
    also have "\<dots> = z"
      using assms * by (auto simp: field_simps)
    finally show ?thesis
      using comb by auto
  qed
  then show "z \<in> C"
    using z assms by (auto simp: le_less)
qed
  
lemma arg_elim:
  "f x \<Longrightarrow> x= y \<Longrightarrow> f y"
  by auto
 
lemma arg_elim2:
  "f x1 x2 \<Longrightarrow> x1= y1 \<Longrightarrow>x2=y2 \<Longrightarrow> f y1 y2"
  by auto
 
lemma arg_elim3:
  "\<lbrakk>f x1 x2 x3;x1= y1;x2=y2;x3=y3 \<rbrakk> \<Longrightarrow> f y1 y2 y3"
  by auto  
    
lemma IVT_strict:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "(f a > y \<and> y > f b) \<or> (f a < y \<and> y < f b)" "a<b" "continuous_on {a .. b} f"
  shows "\<exists>x. a < x \<and> x < b \<and> f x = y"
by (metis IVT' IVT2' assms(1) assms(2) assms(3) linorder_neq_iff order_le_less order_less_imp_le)    
  
lemma (in dense_linorder) atLeastAtMost_subseteq_greaterThanLessThan_iff:
  "{a .. b} \<subseteq> { c <..< d } \<longleftrightarrow> (a \<le> b \<longrightarrow> c < a \<and> b < d)"
  using dense[of "a" "min c b"] dense[of "max a d" "b"]
  by (force simp: subset_eq Ball_def not_less[symmetric])    

lemma Re_winding_number_half_right:
  assumes "\<forall>p\<in>path_image \<gamma>. Re p \<ge> Re z" and "valid_path \<gamma>" and  "z\<notin>path_image \<gamma>"
  shows "Re(winding_number \<gamma> z) = (Im (Ln (pathfinish \<gamma> - z)) - Im (Ln (pathstart \<gamma> - z)))/(2*pi)"
proof -
  define g where "g=(\<lambda>t. \<gamma> t - z)"
  define st fi where "st\<equiv>pathstart g" and "fi\<equiv>pathfinish g"
  have "valid_path g" "0\<notin>path_image g" and pos_img:"\<forall>p\<in>path_image g. Re p \<ge> 0" unfolding g_def 
    subgoal using assms(2) by auto
    subgoal using assms(3) by auto
    subgoal using assms(1) by fastforce
    done
  have "(inverse has_contour_integral Ln fi - Ln st) g"
    unfolding fi_def st_def
  proof (rule contour_integral_primitive[OF _ \<open>valid_path g\<close>,of " - \<real>\<^sub>\<le>\<^sub>0"])
    fix x::complex assume "x \<in> - \<real>\<^sub>\<le>\<^sub>0"
    then have "(Ln has_field_derivative inverse x) (at x)" using has_field_derivative_Ln
      by auto
    then show "(Ln has_field_derivative inverse x) (at x within - \<real>\<^sub>\<le>\<^sub>0)"
      using has_field_derivative_at_within by auto
  next
    show "path_image g \<subseteq> - \<real>\<^sub>\<le>\<^sub>0" using pos_img \<open>0\<notin>path_image g\<close>
      by (metis ComplI antisym assms(3) complex_nonpos_Reals_iff complex_surj
          subsetI zero_complex.code)
  qed
  then have winding_eq:"2*pi*\<i>*winding_number g 0 = (Ln fi - Ln st)"
    using has_contour_integral_winding_number[OF \<open>valid_path g\<close> \<open>0\<notin>path_image g\<close>
        ,simplified,folded inverse_eq_divide] has_contour_integral_unique 
    by auto
  have "Re(winding_number g 0) 
      = (Im (Ln fi) - Im (Ln st))/(2*pi)"
    (is "?L=?R")
  proof -
    have "?L = Re((Ln fi - Ln st)/(2*pi*\<i>))"
      using winding_eq[symmetric] by auto
    also have "... = ?R"
      by (metis Im_divide_of_real Im_i_times complex_i_not_zero minus_complex.simps(2) 
          mult.commute mult_divide_mult_cancel_left_if times_divide_eq_right)
    finally show ?thesis .
  qed
  then show ?thesis unfolding g_def fi_def st_def using winding_number_offset by simp
qed      
  
lemma Re_winding_number_half_upper:
  assumes pimage:"\<forall>p\<in>path_image \<gamma>. Im p \<ge> Im z" and "valid_path \<gamma>" and "z\<notin>path_image \<gamma>"
  shows "Re(winding_number \<gamma> z) = 
            (Im (Ln (\<i>*z - \<i>*pathfinish \<gamma>)) - Im (Ln (\<i>*z - \<i>*pathstart \<gamma> )))/(2*pi)"
proof -
  define \<gamma>' where "\<gamma>'=(\<lambda>t. - \<i> * (\<gamma> t - z) + z)"
  have "Re (winding_number \<gamma>' z) = (Im (Ln (pathfinish \<gamma>' - z)) - Im (Ln (pathstart \<gamma>' - z))) / (2 * pi)"
    unfolding \<gamma>'_def
    apply (rule Re_winding_number_half_right)
    subgoal using pimage unfolding path_image_def by auto
    subgoal 
      apply (rule valid_path_compose_holomorphic[OF \<open>valid_path \<gamma>\<close>,of "\<lambda>x. -\<i> * (x-z) + z" UNIV
            , unfolded comp_def])
      by (auto intro!:holomorphic_intros)
    subgoal using \<open>z\<notin>path_image \<gamma>\<close> unfolding path_image_def by auto
    done
  moreover have "winding_number \<gamma>' z = winding_number \<gamma> z"
  proof -
    define f where "f=(\<lambda>x. -\<i> * (x-z) + z)"
    define c where "c= 1 / (complex_of_real (2 * pi) * \<i>)"
    have "winding_number \<gamma>' z = winding_number (f o \<gamma>) z" 
      unfolding \<gamma>'_def comp_def f_def by auto
    also have "... = c * contour_integral \<gamma> (\<lambda>w. deriv f w / (f w - z))" unfolding c_def
    proof (rule winding_number_comp[of UNIV])
      show "z \<notin> path_image (f \<circ> \<gamma>)" using \<open>z\<notin>path_image \<gamma>\<close> unfolding f_def path_image_def by auto
    qed (auto simp add:f_def \<open>valid_path \<gamma>\<close> intro!:holomorphic_intros)
    also have "... = c * contour_integral \<gamma> (\<lambda>w.  1 / (w - z))"
    proof -
      have "deriv f x = -\<i>" for x
        unfolding f_def
        by (auto intro!:derivative_eq_intros DERIV_imp_deriv)
      then show ?thesis    
        unfolding f_def c_def 
        by (auto simp add:field_simps divide_simps intro!:arg_cong2[where f=contour_integral])
    qed
    also have "... = winding_number \<gamma> z"
      using winding_number_valid_path[OF \<open>valid_path \<gamma>\<close> \<open>z\<notin>path_image \<gamma>\<close>,folded c_def] by simp
    finally show ?thesis .
  qed    
  moreover have "pathfinish \<gamma>' = z+ \<i>*z -\<i>* pathfinish \<gamma>" "pathstart \<gamma>' = z+ \<i>*z -\<i>*pathstart \<gamma>"  
    unfolding \<gamma>'_def path_defs by (auto simp add:algebra_simps)
  ultimately show ?thesis by auto
qed
    
lemma Re_winding_number_half_lower:
  assumes pimage:"\<forall>p\<in>path_image \<gamma>. Im p \<le> Im z" and "valid_path \<gamma>" and "z\<notin>path_image \<gamma>"
  shows "Re(winding_number \<gamma> z) = 
             (Im (Ln ( \<i>*pathfinish \<gamma> - \<i>*z)) - Im (Ln (\<i>*pathstart \<gamma> - \<i>*z)))/(2*pi)"
proof -
  define \<gamma>' where "\<gamma>'=(\<lambda>t. \<i> * (\<gamma> t - z) + z)"
  have "Re (winding_number \<gamma>' z) = (Im (Ln (pathfinish \<gamma>' - z)) - Im (Ln (pathstart \<gamma>' - z))) / (2 * pi)"
    unfolding \<gamma>'_def
    apply (rule Re_winding_number_half_right)
    subgoal using pimage unfolding path_image_def by auto
    subgoal 
      apply (rule valid_path_compose_holomorphic[OF \<open>valid_path \<gamma>\<close>,of "\<lambda>x. \<i> * (x-z) + z" UNIV
            , unfolded comp_def])
      by (auto intro!:holomorphic_intros)
    subgoal using \<open>z\<notin>path_image \<gamma>\<close> unfolding path_image_def by auto
    done
  moreover have "winding_number \<gamma>' z = winding_number \<gamma> z"
  proof -
    define f where "f=(\<lambda>x. \<i> * (x-z) + z)"
    define c where "c= 1 / (complex_of_real (2 * pi) * \<i>)"
    have "winding_number \<gamma>' z = winding_number (f o \<gamma>) z" 
      unfolding \<gamma>'_def comp_def f_def by auto
    also have "... = c * contour_integral \<gamma> (\<lambda>w. deriv f w / (f w - z))" unfolding c_def
    proof (rule winding_number_comp[of UNIV])
      show "z \<notin> path_image (f \<circ> \<gamma>)" using \<open>z\<notin>path_image \<gamma>\<close> unfolding f_def path_image_def by auto
    qed (auto simp add:f_def \<open>valid_path \<gamma>\<close> intro!:holomorphic_intros)
    also have "... = c * contour_integral \<gamma> (\<lambda>w.  1 / (w - z))"
    proof -
      have "deriv f x = \<i>" for x
        unfolding f_def
        by (auto intro!:derivative_eq_intros DERIV_imp_deriv)
      then show ?thesis    
        unfolding f_def c_def 
        by (auto simp add:field_simps divide_simps intro!:arg_cong2[where f=contour_integral])
    qed
    also have "... = winding_number \<gamma> z"
      using winding_number_valid_path[OF \<open>valid_path \<gamma>\<close> \<open>z\<notin>path_image \<gamma>\<close>,folded c_def] by simp
    finally show ?thesis .
  qed    
  moreover have "pathfinish \<gamma>' = z+ \<i>* pathfinish \<gamma> - \<i>*z" "pathstart \<gamma>' = z+ \<i>*pathstart \<gamma> - \<i>*z"  
    unfolding \<gamma>'_def path_defs by (auto simp add:algebra_simps)
  ultimately show ?thesis by auto
qed    
    
      
lemma Re_winding_number_half_left:
  assumes neg_img:"\<forall>p\<in>path_image \<gamma>. Re p \<le> Re z" and "valid_path \<gamma>" and "z\<notin>path_image \<gamma>"
  shows "Re(winding_number \<gamma> z) = (Im (Ln (z - pathfinish \<gamma>)) - Im (Ln (z - pathstart \<gamma> )))/(2*pi)"
proof -
  define \<gamma>' where "\<gamma>'\<equiv>(\<lambda>t. 2*z - \<gamma> t)"
  have "Re (winding_number \<gamma>' z) = (Im (Ln (pathfinish \<gamma>' - z)) - Im (Ln (pathstart \<gamma>' - z))) / (2 * pi)"
    unfolding \<gamma>'_def
    apply (rule Re_winding_number_half_right)
    subgoal using neg_img unfolding path_image_def by auto
    subgoal 
      apply (rule valid_path_compose_holomorphic[OF \<open>valid_path \<gamma>\<close>,of "\<lambda>t. 2*z-t" UNIV,
            unfolded comp_def])
      by (auto intro:holomorphic_intros)
    subgoal using \<open>z\<notin>path_image \<gamma>\<close> unfolding path_image_def by auto
    done
  moreover have "winding_number \<gamma>' z = winding_number \<gamma> z"
  proof -
    define f where "f=(\<lambda>t. 2*z-t)"
    define c where "c= 1 / (complex_of_real (2 * pi) * \<i>)"
    have "winding_number \<gamma>' z = winding_number (f o \<gamma>) z" 
      unfolding \<gamma>'_def comp_def f_def by auto
    also have "... = c * contour_integral \<gamma> (\<lambda>w. deriv f w / (f w - z))" unfolding c_def
    proof (rule winding_number_comp[of UNIV])
      show "z \<notin> path_image (f \<circ> \<gamma>)" using \<open>z\<notin>path_image \<gamma>\<close> unfolding f_def path_image_def by auto
    qed (auto simp add:f_def \<open>valid_path \<gamma>\<close> intro:holomorphic_intros)
    also have "... = c * contour_integral \<gamma> (\<lambda>w.  1 / (w - z))" 
      unfolding f_def c_def 
      by (auto simp add:field_simps divide_simps intro!:arg_cong2[where f=contour_integral])
    also have "... = winding_number \<gamma> z"
      using winding_number_valid_path[OF \<open>valid_path \<gamma>\<close> \<open>z\<notin>path_image \<gamma>\<close>,folded c_def] by simp
    finally show ?thesis .
  qed
  moreover have "pathfinish \<gamma>' = 2*z - pathfinish \<gamma>" "pathstart \<gamma>' = 2*z - pathstart \<gamma>"  
    unfolding \<gamma>'_def path_defs by auto 
  ultimately show ?thesis by auto    
qed 
  
lemma continuous_on_open_Collect_neq:
  fixes f g :: "'a::topological_space \<Rightarrow> 'b::t2_space"
  assumes f: "continuous_on S f" and g: "continuous_on S g" and "open S"
  shows "open {x\<in>S. f x \<noteq> g x}"
proof (rule topological_space_class.openI)
  fix t
  assume "t \<in> {x\<in>S. f x \<noteq> g x}"
  then obtain U0 V0 where "open U0" "open V0" "f t \<in> U0" "g t \<in> V0" "U0 \<inter> V0 = {}" "t\<in>S"
    by (auto simp add: separation_t2)
  obtain U1 where "open U1" "t \<in> U1" "\<forall>y\<in>(S \<inter> U1). f y \<in> U0"
    using f[unfolded continuous_on_topological,rule_format,OF \<open>t\<in>S\<close> \<open>open U0\<close> \<open>f t \<in>U0\<close>] by auto
  obtain V1 where "open V1" "t \<in> V1" "\<forall>y\<in>(S \<inter> V1). g y \<in> V0"
    using g[unfolded continuous_on_topological,rule_format,OF \<open>t\<in>S\<close> \<open>open V0\<close> \<open>g t \<in>V0\<close>] by auto 
  define T where "T=V1 \<inter> U1 \<inter> S"
  have "open T" unfolding T_def using \<open>open U1\<close> \<open>open V1\<close> \<open>open S\<close> by auto
  moreover have "t \<in> T" unfolding T_def using \<open>t\<in>U1\<close> \<open>t\<in>V1\<close> \<open>t\<in>S\<close> by auto
  moreover have "T \<subseteq> {x \<in> S. f x \<noteq> g x}" unfolding T_def
    using \<open>U0 \<inter> V0 = {}\<close> \<open>\<forall>y\<in>S \<inter> U1. f y \<in> U0\<close> \<open>\<forall>y\<in>S \<inter> V1. g y \<in> V0\<close> by auto
  ultimately show "\<exists>T. open T \<and> t \<in> T \<and> T \<subseteq> {x \<in> S. f x \<noteq> g x}" by auto
qed  
    
subsection \<open>Sign at a filter\<close>    
 
(*Relaxation in types could be done in the future.*)
definition has_sgnx::"(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real filter \<Rightarrow> bool" 
    (infixr "has'_sgnx" 55) where
  "(f has_sgnx c) F= (eventually (\<lambda>x. sgn(f x) = c) F)"    
  
definition sgnx_able (infixr "sgnx'_able" 55) where
  "(f sgnx_able F) = (\<exists>c. (f has_sgnx c) F)"
  
definition sgnx where
  "sgnx f F = (SOME c. (f has_sgnx c) F)"
  
lemma has_sgnx_eq_rhs: "(f has_sgnx x) F \<Longrightarrow> x = y \<Longrightarrow> (f has_sgnx y) F"
  by simp

named_theorems sgnx_intros "introduction rules for has_sgnx"
setup \<open>
  Global_Theory.add_thms_dynamic (@{binding sgnx_eq_intros},
    fn context =>
      Named_Theorems.get (Context.proof_of context) @{named_theorems sgnx_intros}
      |> map_filter (try (fn thm => @{thm has_sgnx_eq_rhs} OF [thm])))
\<close>  

lemma sgnx_able_sgnx:"f sgnx_able F \<Longrightarrow> (f has_sgnx (sgnx f F)) F"
  unfolding sgnx_able_def sgnx_def using someI_ex by metis    

lemma has_sgnx_imp_sgnx_able[elim]:
  "(f has_sgnx c) F \<Longrightarrow> f sgnx_able F"
unfolding sgnx_able_def by auto

lemma has_sgnx_unique:
  assumes "F\<noteq>bot" "(f has_sgnx c1) F" "(f has_sgnx c2) F" 
  shows "c1=c2"
proof (rule ccontr)
  assume "c1 \<noteq> c2 "
  have "eventually (\<lambda>x. sgn(f x) = c1 \<and> sgn(f x) = c2) F" 
    using assms  unfolding has_sgnx_def eventually_conj_iff by simp
  then have "eventually (\<lambda>_. c1 = c2) F" by (elim eventually_mono,auto)
  then have "eventually (\<lambda>_. False) F" using \<open>c1 \<noteq> c2\<close> by auto
  then show False using \<open>F \<noteq> bot\<close> eventually_False by auto
qed

lemma has_sgnx_imp_sgnx[elim]:
  "(f has_sgnx c) F \<Longrightarrow>F\<noteq>bot \<Longrightarrow> sgnx f F = c"
  using has_sgnx_unique sgnx_def by auto

lemma has_sgnx_const[simp,sgnx_intros]:
  "((\<lambda>_. c) has_sgnx sgn c) F"
by (simp add: has_sgnx_def)

lemma finite_sgnx_at_left_at_right:
  assumes "finite {t. f t=0 \<and> a<t \<and> t<b}" "continuous_on ({a<..<b} - s) f" "finite s" 
      and x:"x\<in>{a<..<b}"
  shows "f sgnx_able (at_left x)" "sgnx f (at_left x)\<noteq>0"
        "f sgnx_able (at_right x)" "sgnx f (at_right x)\<noteq>0"
proof -
  define ls where "ls \<equiv> {t. (f t=0 \<or> t\<in>s) \<and> a<t \<and>t<x }"
  define l where "l\<equiv>(if ls = {} then (a+x)/2 else (Max ls + x)/2)" 
  have "finite ls"
  proof -
    have "{t. f t=0 \<and> a<t \<and> t<x} \<subseteq> {t. f t=0 \<and> a<t \<and> t<b}" using x by auto
    then have "finite {t. f t=0 \<and> a<t \<and> t<x}" using assms(1) 
      using finite_subset by blast
    moreover have "finite {t. t\<in>s \<and> a<t \<and> t<x}" using assms(3) by auto
    moreover have "ls = {t. f t=0 \<and> a<t \<and> t<x} \<union> {t. t\<in>s \<and> a<t \<and> t<x}"
      unfolding ls_def by auto
    ultimately show ?thesis by auto
  qed
  have [simp]: "l<x" "a<l" "l<b"
  proof -
    have "l<x \<and> a<l \<and> l<b" when "ls = {}" 
      using that x unfolding l_def by auto
    moreover have "l<x \<and> a<l \<and> l<b" when "ls \<noteq>{}"
    proof -
      have "Max ls \<in> ls" using assms(1,3) that \<open>finite ls\<close>
        apply (intro linorder_class.Max_in)
        by auto
      then have "a<Max ls \<and> Max ls < x" unfolding ls_def by auto
      then show ?thesis unfolding l_def using that x by auto
    qed
    ultimately show "l<x" "a<l" "l<b" by auto
  qed  
  have noroot:"f t\<noteq>0" when t:"t\<in>{l..<x}" for t
  proof (cases "ls = {}")
    case True
    have False when "f t=0"
    proof -
      have "t>a" using t \<open>l>a\<close> by (meson atLeastLessThan_iff less_le_trans)
      then have "t\<in>ls" using that t unfolding ls_def by auto
      then show False using True by auto
    qed
    then show ?thesis by auto 
  next
    case False
    have "t>Max ls" using that False \<open>l<x\<close> unfolding l_def by auto
    have False when "f t=0" 
    proof -
      have "t>a" using t \<open>l>a\<close> by (meson atLeastLessThan_iff less_le_trans)
      then have "t\<in>ls" using that t unfolding ls_def by auto
      then have "t\<le>Max ls" using \<open>finite ls\<close> by auto
      then show False using \<open>t>Max ls\<close> by auto
    qed
    then show ?thesis by auto
  qed
  have "(f has_sgnx sgn (f l)) (at_left x)" unfolding has_sgnx_def
  proof (rule eventually_at_leftI[OF _ \<open>l<x\<close>])
    fix t assume t:"t\<in>{l<..<x}"
    then have [simp]:"t>a" "t<b" using \<open>l>a\<close> x 
      by (meson greaterThanLessThan_iff less_trans)+
    have False when "f t = 0" 
      using noroot t that by auto
    moreover have False when "f l=0" 
      using noroot t that by auto
    moreover have False when "f l>0 \<and> f t<0 \<or> f l <0 \<and> f t >0" 
    proof -
      have False when "{l..t} \<inter> s \<noteq>{}" 
      proof -
        obtain t' where t':"t'\<in>{l..t}" "t'\<in>s" 
          using \<open>{l..t} \<inter> s \<noteq> {}\<close> by blast
        then have "a<t' \<and> t'<x" 
          by (metis \<open>a < l\<close> atLeastAtMost_iff greaterThanLessThan_iff le_less less_trans t)
        then have "t'\<in>ls" unfolding ls_def using \<open>t'\<in>s\<close> by auto
        then have "t'\<le>Max ls" using \<open>finite ls\<close> by auto
        moreover have "Max ls<l" 
          using \<open>l<x\<close> \<open>t'\<in>ls\<close> \<open>finite ls\<close> unfolding l_def by (auto simp add:ls_def )
        ultimately show False using t'(1) by auto
      qed
      moreover have "{l..t} \<subseteq> {a<..<b}" 
        by (intro atMostAtLeast_subset_convex,auto)
      ultimately have "continuous_on {l..t} f" using assms(2) 
        by (elim continuous_on_subset,auto) 
      then have "\<exists>x>l. x < t \<and> f x = 0"
        apply (intro IVT_strict)
        using that t assms(2) by auto 
      then obtain t' where "l<t'" "t'<t" "f t'=0" by auto
      then have "t'\<in>{l..<x}" unfolding ls_def using t by auto
      then show False using noroot \<open>f t'=0\<close> by auto
    qed
    ultimately show "sgn (f t) = sgn (f l)" 
      by (metis le_less not_less sgn_if)
  qed
  then show "f sgnx_able (at_left x)" by auto   
  show "sgnx f (at_left x)\<noteq>0" 
    using noroot[of l,simplified] \<open>(f has_sgnx sgn (f l)) (at_left x)\<close>
    by (simp add: has_sgnx_imp_sgnx sgn_if)
next
  define rs where "rs \<equiv> {t. (f t=0 \<or> t\<in>s) \<and> x<t \<and> t<b}"
  define r where "r\<equiv>(if rs = {} then (x+b)/2 else (Min rs + x)/2)" 
  have "finite rs" 
  proof -
    have "{t. f t=0 \<and> x<t \<and> t<b} \<subseteq> {t. f t=0 \<and> a<t \<and> t<b}" using x by auto
    then have "finite {t. f t=0 \<and> x<t \<and> t<b}" using assms(1) 
      using finite_subset by blast
    moreover have "finite {t. t\<in>s \<and> x<t \<and> t<b}" using assms(3) by auto
    moreover have "rs = {t. f t=0 \<and> x<t \<and> t<b} \<union> {t. t\<in>s \<and> x<t \<and> t<b}"
      unfolding rs_def by auto
    ultimately show ?thesis by auto
  qed  
  
  have [simp]: "r>x" "a<r" "r<b"
  proof -
    have "r>x \<and> a<r \<and> r<b" when "rs = {}" 
      using that x unfolding r_def by auto
    moreover have "r>x \<and> a<r \<and> r<b" when "rs \<noteq>{}"
    proof -
      have "Min rs \<in> rs" using assms(1,3) that \<open>finite rs\<close>
        apply (intro linorder_class.Min_in)
        by auto
      then have "x<Min rs \<and> Min rs < b" unfolding rs_def by auto
      then show ?thesis unfolding r_def using that x by auto
    qed
    ultimately show "r>x" "a<r" "r<b" by auto
  qed   
  have noroot:"f t\<noteq>0" when t:"t\<in>{x<..r}" for t
  proof (cases "rs = {}")
    case True
    have False when "f t=0"
    proof -
      have "t<b" using t \<open>r<b\<close> 
        using greaterThanAtMost_iff by fastforce 
      then have "t\<in>rs" using that t unfolding rs_def by auto
      then show False using True by auto
    qed
    then show ?thesis by auto
  next
    case False
    have "t<Min rs" using that False \<open>r>x\<close> unfolding r_def by auto
    have False when "f t=0" 
    proof -
      have "t<b" using t \<open>r<b\<close> by (metis greaterThanAtMost_iff le_less less_trans)
      then have "t\<in>rs" using that t unfolding rs_def by auto
      then have "t\<ge>Min rs" using \<open>finite rs\<close> by auto
      then show False using \<open>t<Min rs\<close> by auto
    qed
    then show ?thesis by auto
  qed
  have "(f has_sgnx sgn (f r)) (at_right x)" unfolding has_sgnx_def
  proof (rule eventually_at_rightI[OF _ \<open>r>x\<close>])
    fix t assume t:"t\<in>{x<..<r}"
    then have [simp]:"t>a" "t<b" using \<open>r<b\<close> x 
      by (meson greaterThanLessThan_iff less_trans)+
    have False when "f t = 0" 
      using noroot t that by auto
    moreover have False when "f r=0" 
      using noroot t that by auto
    moreover have False when "f r>0 \<and> f t<0 \<or> f r <0 \<and> f t >0" 
    proof -
      have False when "{t..r} \<inter> s \<noteq>{}" 
      proof -
        obtain t' where t':"t'\<in>{t..r}" "t'\<in>s" 
          using \<open>{t..r} \<inter> s \<noteq> {}\<close> by blast
        then have "x<t' \<and> t'<b" 
          by (meson \<open>r < b\<close> atLeastAtMost_iff greaterThanLessThan_iff less_le_trans not_le t)
        then have "t'\<in>rs" unfolding rs_def using t \<open>t'\<in>s\<close> by auto
        then have "t'\<ge>Min rs" using \<open>finite rs\<close> by auto
        moreover have "Min rs>r" 
          using \<open>r>x\<close> \<open>t'\<in>rs\<close> \<open>finite rs\<close> unfolding r_def by (auto simp add:rs_def )
        ultimately show False using t'(1) by auto
      qed
      moreover have "{t..r} \<subseteq> {a<..<b}"
        by (intro atMostAtLeast_subset_convex,auto)
      ultimately have "continuous_on {t..r} f" using assms(2) by (elim continuous_on_subset,auto) 
      then have "\<exists>x>t. x < r \<and> f x = 0"
        apply (intro IVT_strict)
        using that t assms(2) by auto
      then obtain t' where "t<t'" "t'<r" "f t'=0" by auto
      then have "t'\<in>{x<..r}" unfolding rs_def using t by auto
      then show False using noroot \<open>f t'=0\<close> by auto
    qed
    ultimately show "sgn (f t) = sgn (f r)" 
      by (metis le_less not_less sgn_if)
  qed
  then show "f sgnx_able (at_right x)" by auto   
  show "sgnx f (at_right x)\<noteq>0" 
    using noroot[of r,simplified] \<open>(f has_sgnx sgn (f r)) (at_right x)\<close>
    by (simp add: has_sgnx_imp_sgnx sgn_if)    
qed

lemma sgnx_able_poly[simp]:
  "(poly p) sgnx_able (at_right a)"
  "(poly p) sgnx_able (at_left a)"
  "(poly p) sgnx_able at_top"
  "(poly p) sgnx_able at_bot"
proof -
  show "(poly p) sgnx_able at_top"
    using has_sgnx_def poly_sgn_eventually_at_top sgnx_able_def by blast
  show "(poly p) sgnx_able at_bot"
    using has_sgnx_def poly_sgn_eventually_at_bot sgnx_able_def by blast
  show "(poly p) sgnx_able (at_right a)"
  proof (cases "p=0")
    case True
    then show ?thesis unfolding sgnx_able_def has_sgnx_def eventually_at_right
      using linordered_field_no_ub by force
  next
    case False
    obtain ub where "ub>a" and ub:"\<forall>z. a<z\<and>z\<le>ub\<longrightarrow>poly p z\<noteq>0" 
      using next_non_root_interval[OF False] by auto 
    have "\<forall>z. a<z\<and>z\<le>ub\<longrightarrow>sgn(poly p z) = sgn (poly p ub)"
    proof (rule ccontr)
      assume "\<not> (\<forall>z. a < z \<and> z \<le> ub \<longrightarrow> sgn (poly p z) = sgn (poly p ub))"
      then obtain z where "a<z" "z\<le>ub" "sgn(poly p z) \<noteq> sgn (poly p ub)" by auto
      moreover then have "poly p z\<noteq>0" "poly p ub\<noteq>0" "z\<noteq>ub" using ub \<open>ub>a\<close> by blast+
      ultimately have "(poly p z>0 \<and> poly p ub<0) \<or> (poly p z<0 \<and> poly p ub>0)"
        by (metis linorder_neqE_linordered_idom sgn_neg sgn_pos)
      then have "\<exists>x>z. x < ub \<and> poly p x = 0" 
        using poly_IVT_neg[of z ub p] poly_IVT_pos[of z ub p] \<open>z\<le>ub\<close> \<open>z\<noteq>ub\<close> by argo  
      then show False using ub \<open>a < z\<close> by auto  
    qed
    then show ?thesis unfolding sgnx_able_def has_sgnx_def eventually_at_right
      apply (rule_tac exI[where x="sgn(poly p ub)"])
      apply (rule_tac exI[where x="ub"])
      using less_eq_real_def \<open>ub>a\<close> by blast
  qed
  show "(poly p) sgnx_able (at_left a)"
  proof (cases "p=0")
    case True
    then show ?thesis unfolding sgnx_able_def has_sgnx_def eventually_at_right
      using linordered_field_no_ub by force
  next
    case False
    obtain lb where "lb<a" and ub:"\<forall>z. lb\<le>z\<and>z<a\<longrightarrow>poly p z\<noteq>0" 
      using last_non_root_interval[OF False] by auto 
    have "\<forall>z. lb\<le>z\<and>z<a\<longrightarrow>sgn(poly p z) = sgn (poly p lb)"
    proof (rule ccontr)
      assume "\<not> (\<forall>z. lb\<le>z\<and>z<a \<longrightarrow> sgn (poly p z) = sgn (poly p lb))"
      then obtain z where "lb\<le>z" "z<a" "sgn(poly p z) \<noteq> sgn (poly p lb)" by auto
      moreover then have "poly p z\<noteq>0" "poly p lb\<noteq>0" "z\<noteq>lb" using ub \<open>lb<a\<close> by blast+
      ultimately have "(poly p z>0 \<and> poly p lb<0) \<or> (poly p z<0 \<and> poly p lb>0)"
        by (metis linorder_neqE_linordered_idom sgn_neg sgn_pos)
      then have "\<exists>x>lb. x < z \<and> poly p x = 0" 
        using poly_IVT_neg[of lb z p] poly_IVT_pos[of lb z p] \<open>lb\<le>z\<close> \<open>z\<noteq>lb\<close> by argo  
      then show False using ub \<open>z < a\<close> by auto  
    qed
    then show ?thesis unfolding sgnx_able_def has_sgnx_def eventually_at_left
      apply (rule_tac exI[where x="sgn(poly p lb)"])
      apply (rule_tac exI[where x="lb"])
      using less_eq_real_def \<open>lb<a\<close> by blast
  qed
qed

lemma has_sgnx_identity[intro,sgnx_intros]:
  shows "x\<ge>0 \<Longrightarrow>((\<lambda>x. x) has_sgnx 1) (at_right x)" 
        "x\<le>0 \<Longrightarrow> ((\<lambda>x. x) has_sgnx -1) (at_left x)"  
proof -
  show "x\<ge>0 \<Longrightarrow> ((\<lambda>x. x) has_sgnx 1) (at_right x)"
    unfolding has_sgnx_def eventually_at_right
    apply (intro exI[where x="x+1"])
    by auto
  show "x\<le>0 \<Longrightarrow> ((\<lambda>x. x) has_sgnx -1) (at_left x)"
    unfolding has_sgnx_def eventually_at_left
    apply (intro exI[where x="x-1"])
    by auto
qed
    
lemma has_sgnx_divide[sgnx_intros]:
  assumes "(f has_sgnx c1) F" "(g has_sgnx c2) F"
  shows "((\<lambda>x. f x / g x) has_sgnx c1 / c2) F"
proof -
  have "\<forall>\<^sub>F x in F. sgn (f x) = c1 \<and> sgn (g x) = c2" 
    using assms unfolding has_sgnx_def by (intro eventually_conj,auto)
  then have "\<forall>\<^sub>F x in F. sgn (f x / g x) = c1 / c2" 
    apply (elim eventually_mono)
    by (simp add: sgn_mult sgn_divide)
  then show "((\<lambda>x. f x / g x) has_sgnx c1 / c2) F" unfolding has_sgnx_def by auto
qed

lemma sgnx_able_divide[sgnx_intros]:
  assumes "f sgnx_able F" "g sgnx_able F"
  shows "(\<lambda>x. f x / g x) sgnx_able F"  
using has_sgnx_divide by (meson assms(1) assms(2) sgnx_able_def)   

lemma sgnx_divide:
  assumes "F\<noteq>bot" "f sgnx_able F" "g sgnx_able F"
  shows "sgnx (\<lambda>x. f x / g x) F =sgnx f F / sgnx g F"
proof -
  obtain c1 c2 where c1:"(f has_sgnx c1) F" and c2:"(g has_sgnx c2) F"
    using assms unfolding sgnx_able_def by auto
  have "sgnx f F=c1" "sgnx g F=c2" using c1 c2 \<open>F\<noteq>bot\<close> by auto
  moreover have "((\<lambda>x. f x / g x) has_sgnx c1 / c2) F" 
    using has_sgnx_divide[OF c1 c2] .
  ultimately show ?thesis using assms(1) has_sgnx_imp_sgnx by blast
qed
  
lemma has_sgnx_times[sgnx_intros]:
  assumes "(f has_sgnx c1) F" "(g has_sgnx c2) F"
  shows "((\<lambda>x. f x* g x) has_sgnx c1 * c2) F"
proof -
  have "\<forall>\<^sub>F x in F. sgn (f x) = c1 \<and> sgn (g x) = c2" 
    using assms unfolding has_sgnx_def by (intro eventually_conj,auto)
  then have "\<forall>\<^sub>F x in F. sgn (f x * g x) = c1 * c2" 
    apply (elim eventually_mono)
    by (simp add: sgn_mult)
  then show "((\<lambda>x. f x* g x) has_sgnx c1 * c2) F" unfolding has_sgnx_def by auto
qed

lemma sgnx_able_times[sgnx_intros]:
  assumes "f sgnx_able F" "g sgnx_able F"
  shows "(\<lambda>x. f x * g x) sgnx_able F"  
using has_sgnx_times by (meson assms(1) assms(2) sgnx_able_def)   

lemma sgnx_times:
  assumes "F\<noteq>bot" "f sgnx_able F" "g sgnx_able F"
  shows "sgnx (\<lambda>x. f x * g x) F =sgnx f F * sgnx g F"
proof -
  obtain c1 c2 where c1:"(f has_sgnx c1) F" and c2:"(g has_sgnx c2) F"
    using assms unfolding sgnx_able_def by auto
  have "sgnx f F=c1" "sgnx g F=c2" using c1 c2 \<open>F\<noteq>bot\<close> by auto
  moreover have "((\<lambda>x. f x* g x) has_sgnx c1 * c2) F" 
    using has_sgnx_times[OF c1 c2] .
  ultimately show ?thesis using assms(1) has_sgnx_imp_sgnx by blast
qed

lemma tendsto_nonzero_has_sgnx:
  assumes "(f \<longlongrightarrow> c) F" "c\<noteq>0"
  shows "(f has_sgnx sgn c) F"
proof (cases rule:linorder_cases[of c 0])
  case less
  then have "\<forall>\<^sub>F x in F. f x<0"
    using order_topology_class.order_tendstoD[OF assms(1),of 0] by auto
  then show ?thesis 
    unfolding has_sgnx_def 
    apply (elim eventually_mono)
    using less by auto
next
  case equal
  then show ?thesis using \<open>c\<noteq>0\<close> by auto
next
  case greater
  then have "\<forall>\<^sub>F x in F. f x>0"
    using order_topology_class.order_tendstoD[OF assms(1),of 0] by auto
  then show ?thesis 
    unfolding has_sgnx_def 
    apply (elim eventually_mono)
    using greater by auto
qed

lemma tendsto_nonzero_sgnx:
  assumes "(f \<longlongrightarrow> c) F" "F\<noteq>bot" "c\<noteq>0"
  shows "sgnx f F = sgn c"
  using tendsto_nonzero_has_sgnx
by (simp add: assms has_sgnx_imp_sgnx)


lemma filterlim_divide_at_bot_at_top_iff:
  assumes "(f \<longlongrightarrow> c) F" "c\<noteq>0" 
  shows 
    "(LIM x F. f x / g x :> at_bot) \<longleftrightarrow> (g \<longlongrightarrow> 0) F 
      \<and> ((\<lambda>x. g x) has_sgnx - sgn c) F"
    "(LIM x F. f x / g x :> at_top) \<longleftrightarrow> (g \<longlongrightarrow> 0) F 
      \<and> ((\<lambda>x. g x) has_sgnx sgn c) F"
proof -
  show "(LIM x F. f x / g x :> at_bot) \<longleftrightarrow> ((g \<longlongrightarrow> 0) F )  
    \<and> ((\<lambda>x. g x) has_sgnx - sgn c) F"
  proof 
    assume asm:"LIM x F. f x / g x :> at_bot"
    then have "filterlim g (at 0) F" 
      using filterlim_at_infinity_divide_iff[OF assms(1,2),of g] 
      at_bot_le_at_infinity filterlim_mono by blast
    then have "(g \<longlongrightarrow> 0) F" using filterlim_at by blast
    moreover have "(g has_sgnx - sgn c) F"
    proof -
      have "((\<lambda>x. sgn c * inverse (f x)) \<longlongrightarrow> sgn c * inverse c) F"
        using assms(1,2) by (auto intro:tendsto_intros)
      then have "LIM x F. sgn c * inverse (f x) * (f x / g x) :> at_bot"
        apply (elim filterlim_tendsto_pos_mult_at_bot[OF _ _ asm])
        using \<open>c\<noteq>0\<close> sgn_real_def by auto
      then have "LIM x F. sgn c / g x :> at_bot"
        apply (elim filterlim_mono_eventually)
        using eventually_times_inverse_1[OF assms] by (auto elim:eventually_mono)
      then have "\<forall>\<^sub>F x in F. sgn c / g x < 0" 
        using filterlim_at_bot_dense[of "\<lambda>x. sgn c/g x" F] by auto
      then show ?thesis unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (metis add.inverse_inverse divide_less_0_iff sgn_neg sgn_pos sgn_sgn)
    qed  
    ultimately show "(g \<longlongrightarrow> 0) F \<and> (g has_sgnx - sgn c) F" by auto
  next
    assume "(g \<longlongrightarrow> 0) F \<and> (g has_sgnx - sgn c) F"
    then have asm:"(g \<longlongrightarrow> 0) F" "(g has_sgnx - sgn c) F" by auto
    have "LIM x F. inverse (g x * sgn c) :> at_bot"
    proof (rule filterlim_inverse_at_bot)
      show "((\<lambda>x. g x * sgn c) \<longlongrightarrow> 0) F"  
        apply (rule tendsto_mult_left_zero)
        using asm(1) by blast
    next
      show "\<forall>\<^sub>F x in F. g x * sgn c < 0" using asm(2) unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (metis add.inverse_inverse assms(2) linorder_neqE_linordered_idom mult_less_0_iff 
            neg_0_less_iff_less sgn_greater sgn_zero_iff)
    qed
    moreover have "((\<lambda>x. f x * sgn c) \<longlongrightarrow> c * sgn c) F"
      using \<open>(f \<longlongrightarrow> c) F\<close> \<open>c\<noteq>0\<close>
      apply (intro tendsto_intros)
      by (auto simp add:sgn_zero_iff)
    moreover have "c * sgn c >0" using \<open>c\<noteq>0\<close> by (simp add: sgn_real_def)    
    ultimately have "LIM x F. (f x * sgn c) *inverse (g x * sgn c) :> at_bot"
      using filterlim_tendsto_pos_mult_at_bot by blast
    then show "LIM x F. f x / g x :> at_bot" 
      using \<open>c\<noteq>0\<close> by (auto simp add:field_simps sgn_zero_iff)
  qed
  show "(LIM x F. f x / g x :> at_top) \<longleftrightarrow> ((g \<longlongrightarrow> 0) F )  
    \<and> ((\<lambda>x. g x) has_sgnx sgn c) F"
  proof 
    assume asm:"LIM x F. f x / g x :> at_top"
    then have "filterlim g (at 0) F" 
      using filterlim_at_infinity_divide_iff[OF assms(1,2),of g] 
      at_top_le_at_infinity filterlim_mono by blast
    then have "(g \<longlongrightarrow> 0) F" using filterlim_at by blast
    moreover have "(g has_sgnx sgn c) F"
    proof -
      have "((\<lambda>x. sgn c * inverse (f x)) \<longlongrightarrow> sgn c * inverse c) F"
        using assms(1,2) by (auto intro:tendsto_intros)
      then have "LIM x F. sgn c * inverse (f x) * (f x / g x) :> at_top"
        apply (elim filterlim_tendsto_pos_mult_at_top[OF _ _ asm])
        using \<open>c\<noteq>0\<close> sgn_real_def by auto
      then have "LIM x F. sgn c / g x :> at_top"
        apply (elim filterlim_mono_eventually)
        using eventually_times_inverse_1[OF assms] by (auto elim:eventually_mono)
      then have "\<forall>\<^sub>F x in F. sgn c / g x > 0" 
        using filterlim_at_top_dense[of "\<lambda>x. sgn c/g x" F] by auto
      then show ?thesis unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (metis sgn_greater sgn_less sgn_neg sgn_pos zero_less_divide_iff)
    qed  
    ultimately show "(g \<longlongrightarrow> 0) F \<and> (g has_sgnx sgn c) F" by auto
  next
    assume "(g \<longlongrightarrow> 0) F \<and> (g has_sgnx sgn c) F"
    then have asm:"(g \<longlongrightarrow> 0) F" "(g has_sgnx sgn c) F" by auto
    have "LIM x F. inverse (g x * sgn c) :> at_top"
    proof (rule filterlim_inverse_at_top)
      show "((\<lambda>x. g x * sgn c) \<longlongrightarrow> 0) F"  
        apply (rule tendsto_mult_left_zero)
        using asm(1) by blast
    next
      show "\<forall>\<^sub>F x in F. g x * sgn c > 0" using asm(2) unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (metis assms(2) sgn_1_neg sgn_greater sgn_if zero_less_mult_iff)
    qed
    moreover have "((\<lambda>x. f x * sgn c) \<longlongrightarrow> c * sgn c) F"
      using \<open>(f \<longlongrightarrow> c) F\<close> \<open>c\<noteq>0\<close>
      apply (intro tendsto_intros)
      by (auto simp add:sgn_zero_iff)
    moreover have "c * sgn c >0" using \<open>c\<noteq>0\<close> by (simp add: sgn_real_def)    
    ultimately have "LIM x F. (f x * sgn c) *inverse (g x * sgn c) :> at_top"
      using filterlim_tendsto_pos_mult_at_top by blast
    then show "LIM x F. f x / g x :> at_top" 
      using \<open>c\<noteq>0\<close> by (auto simp add:field_simps sgn_zero_iff)
  qed    
qed 


lemma poly_sgnx_left_right:
  fixes c a::real and p::"real poly"
  assumes "p\<noteq>0"
  shows "sgnx (poly p) (at_left a) = (if even (order a p) 
            then sgnx (poly p) (at_right a)
            else -sgnx (poly p) (at_right a))"
  using assms
proof (induction "degree p" arbitrary: p rule: less_induct)
  case less
  have ?case when "poly p a\<noteq>0" 
  proof -
    have "sgnx (poly p) (at_left a) = sgn (poly p a)" 
      by (simp add: has_sgnx_imp_sgnx tendsto_nonzero_has_sgnx that)
    moreover have "sgnx (poly p) (at_right a) = sgn (poly p a)"
      by (simp add: has_sgnx_imp_sgnx tendsto_nonzero_has_sgnx that)
    moreover have "order a p = 0" using that by (simp add: order_0I)
    ultimately show ?thesis by auto
  qed
  moreover have ?case when "poly p a=0"
  proof -
    obtain q where pq:"p= [:-a,1:] * q" 
      using \<open>poly p a=0\<close> by (meson dvdE poly_eq_0_iff_dvd)
    then have "q\<noteq>0" using \<open>p\<noteq>0\<close> by auto
    then have "degree q < degree p" unfolding pq by (subst degree_mult_eq,auto)
    have "sgnx (poly p) (at_left a) = - sgnx (poly q) (at_left a)" 
    proof -
      have "sgnx (\<lambda>x. poly p x) (at_left a) 
          = sgnx (poly q) (at_left a) * sgnx (poly [:-a,1:]) (at_left a)"
        unfolding pq
        apply (subst poly_mult)
        apply (subst sgnx_times)
        by auto
      moreover have "sgnx (\<lambda>x. poly [:-a,1:] x) (at_left a) = -1"
        apply (intro has_sgnx_imp_sgnx)
        unfolding has_sgnx_def eventually_at_left
        by (auto simp add: linordered_field_no_lb)
      ultimately show ?thesis by auto
    qed
    moreover have "sgnx (poly p) (at_right a) = sgnx (poly q) (at_right a)" 
    proof -
      have "sgnx (\<lambda>x. poly p x) (at_right a) 
          = sgnx (poly q) (at_right a) * sgnx (poly [:-a,1:]) (at_right a)"
        unfolding pq
        apply (subst poly_mult)
        apply (subst sgnx_times)
        by auto
      moreover have "sgnx (\<lambda>x. poly [:-a,1:] x) (at_right a) = 1"
        apply (intro has_sgnx_imp_sgnx)
        unfolding has_sgnx_def eventually_at_right
        by (auto simp add: linordered_field_no_ub)
      ultimately show ?thesis by auto
    qed
    moreover have "even (order a p) \<longleftrightarrow> odd (order a q)"
      unfolding pq 
      apply (subst order_mult[OF \<open>p \<noteq> 0\<close>[unfolded pq]])
      using  \<open>q\<noteq>0\<close> by (auto simp add:order_power_n_n[of _ 1, simplified])
    moreover note less.hyps[OF \<open>degree q < degree p\<close> \<open>q\<noteq>0\<close>]
    ultimately show ?thesis by auto
  qed
  ultimately show ?case by blast
qed

lemma poly_has_sgnx_left_right:
  fixes c a::real and p::"real poly"
  assumes "p\<noteq>0"
  shows "(poly p has_sgnx c) (at_left a) \<longleftrightarrow> (if even (order a p) 
            then (poly p has_sgnx c) (at_right a)
            else (poly p has_sgnx -c) (at_right a))"
using poly_sgnx_left_right 
by (metis (no_types, hide_lams) add.inverse_inverse assms has_sgnx_unique 
     sgnx_able_poly sgnx_able_sgnx trivial_limit_at_left_real trivial_limit_at_right_real)    
    
    
lemma sign_r_pos_sgnx_iff:
  "sign_r_pos p a \<longleftrightarrow> sgnx (poly p) (at_right a) > 0"
proof 
  assume asm:"0 < sgnx (poly p) (at_right a)"
  obtain c where c_def:"(poly p has_sgnx c) (at_right a)"
    using sgnx_able_poly(1) sgnx_able_sgnx by blast
  then have "c>0" using asm 
    using has_sgnx_imp_sgnx trivial_limit_at_right_real by blast
  then show "sign_r_pos p a" using c_def unfolding sign_r_pos_def has_sgnx_def
    apply (elim eventually_mono)
    by force
next
  assume asm:"sign_r_pos p a"
  define c where "c = sgnx (poly p) (at_right a)"
  then have "(poly p has_sgnx c) (at_right a)" 
    by (simp add: sgnx_able_sgnx)
  then have "(\<forall>\<^sub>F x in (at_right a). poly p x>0 \<and> sgn (poly p x) = c)"
    using asm unfolding has_sgnx_def sign_r_pos_def
    by (simp add:eventually_conj_iff)
  then have "\<forall>\<^sub>F x in (at_right a). c > 0"
    apply (elim eventually_mono)
    by fastforce
  then show "c>0" by auto
qed

lemma sgnx_values:
  assumes "f sgnx_able F" "F \<noteq> bot"
  shows "sgnx f F = -1 \<or> sgnx f F = 0 \<or> sgnx f F = 1"
proof -
  obtain c where c_def:"(f has_sgnx c) F" 
    using assms(1) unfolding sgnx_able_def by auto
  then obtain x where "sgn(f x) = c" 
    unfolding has_sgnx_def using assms(2) eventually_happens 
    by blast
  then have "c=-1 \<or> c=0 \<or> c=1" using sgn_if by metis
  moreover have "sgnx f F = c" using c_def by (simp add: assms(2) has_sgnx_imp_sgnx)
  ultimately show ?thesis by auto
qed
  
lemma has_sgnx_poly_at_top:
    "(poly p has_sgnx  sgn_pos_inf p) at_top"
  using has_sgnx_def poly_sgn_eventually_at_top by blast

lemma has_sgnx_poly_at_bot:
    "(poly p has_sgnx  sgn_neg_inf p) at_bot"
  using has_sgnx_def poly_sgn_eventually_at_bot by blast
    
lemma sgnx_poly_at_top:
  "sgnx (poly p) at_top = sgn_pos_inf p"
by (simp add: has_sgnx_def has_sgnx_imp_sgnx poly_sgn_eventually_at_top)
    
lemma sgnx_poly_at_bot:
  "sgnx (poly p) at_bot = sgn_neg_inf p"
by (simp add: has_sgnx_def has_sgnx_imp_sgnx poly_sgn_eventually_at_bot)  
  
lemma poly_has_sgnx_values:
  assumes "p\<noteq>0"
  shows 
    "(poly p has_sgnx 1) (at_left a) \<or> (poly p has_sgnx - 1) (at_left a)"
    "(poly p has_sgnx 1) (at_right a) \<or> (poly p has_sgnx - 1) (at_right a)"
    "(poly p has_sgnx 1) at_top \<or> (poly p has_sgnx - 1) at_top"
    "(poly p has_sgnx 1) at_bot \<or> (poly p has_sgnx - 1) at_bot"
proof -
  have "sgn_pos_inf p = 1 \<or> sgn_pos_inf p = -1"
    unfolding sgn_pos_inf_def by (simp add: assms sgn_if)
  then show "(poly p has_sgnx 1) at_top \<or> (poly p has_sgnx - 1) at_top"
    using has_sgnx_poly_at_top by metis
next
  have "sgn_neg_inf p = 1 \<or> sgn_neg_inf p = -1"
    unfolding sgn_neg_inf_def by (simp add: assms sgn_if)
  then show "(poly p has_sgnx 1) at_bot \<or> (poly p has_sgnx - 1) at_bot"
    using has_sgnx_poly_at_bot by metis
next
  obtain c where c_def:"(poly p has_sgnx c) (at_left a)" 
    using sgnx_able_poly(2) sgnx_able_sgnx by blast
  then have "sgnx (poly p) (at_left a) = c" using assms by auto
  then have "c=-1 \<or> c=0 \<or> c=1"
    using sgnx_values sgnx_able_poly(2) trivial_limit_at_left_real by blast
  moreover have False when "c=0" 
  proof -
    have "(poly p has_sgnx 0) (at_left a)" using c_def that by auto
    then obtain lb where "lb<a" "\<forall>y. (lb<y \<and> y < a) \<longrightarrow> poly p y = 0"
      unfolding has_sgnx_def eventually_at_left sgn_if
      by (metis one_neq_zero zero_neq_neg_one)
    then have "{lb<..<a} \<subseteq> proots p" unfolding proots_within_def by auto
    then have "infinite (proots p)"
      apply (elim infinite_super)
      using \<open>lb<a\<close> by auto
    moreover have "finite (proots p)" using finite_proots[OF \<open>p\<noteq>0\<close>] by auto
    ultimately show False by auto
  qed
  ultimately have "c=-1 \<or> c=1" by auto
  then show "(poly p has_sgnx 1) (at_left a) \<or> (poly p has_sgnx - 1) (at_left a)"
    using c_def by auto
next
  obtain c where c_def:"(poly p has_sgnx c) (at_right a)" 
    using sgnx_able_poly(1) sgnx_able_sgnx by blast
  then have "sgnx (poly p) (at_right a) = c" using assms by auto
  then have "c=-1 \<or> c=0 \<or> c=1"
    using sgnx_values sgnx_able_poly(1) trivial_limit_at_right_real by blast
  moreover have False when "c=0" 
  proof -
    have "(poly p has_sgnx 0) (at_right a)" using c_def that by auto
    then obtain ub where "ub>a" "\<forall>y. (a<y \<and> y < ub) \<longrightarrow> poly p y = 0"
      unfolding has_sgnx_def eventually_at_right sgn_if
      by (metis one_neq_zero zero_neq_neg_one)
    then have "{a<..<ub} \<subseteq> proots p" unfolding proots_within_def by auto
    then have "infinite (proots p)"
      apply (elim infinite_super)
      using \<open>ub>a\<close> by auto
    moreover have "finite (proots p)" using finite_proots[OF \<open>p\<noteq>0\<close>] by auto
    ultimately show False by auto
  qed
  ultimately have "c=-1 \<or> c=1" by auto
  then show "(poly p has_sgnx 1) (at_right a) \<or> (poly p has_sgnx - 1) (at_right a)"
    using c_def by auto
qed

lemma poly_sgnx_values:
  assumes "p\<noteq>0"
  shows "sgnx (poly p) (at_left a) = 1 \<or> sgnx (poly p) (at_left a) = -1"
        "sgnx (poly p) (at_right a) = 1 \<or> sgnx (poly p) (at_right a) = -1" 
  using poly_has_sgnx_values[OF \<open>p\<noteq>0\<close>] has_sgnx_imp_sgnx trivial_limit_at_left_real 
    trivial_limit_at_right_real by blast+
 
lemma has_sgnx_inverse: "(f has_sgnx c) F \<longleftrightarrow> ((inverse o f) has_sgnx (inverse c)) F"
  unfolding has_sgnx_def comp_def
  apply (rule eventually_subst)  
  apply (rule always_eventually)
  by (metis inverse_inverse_eq sgn_inverse)


lemma has_sgnx_derivative_at_left:
  assumes g_deriv:"(g has_field_derivative c) (at x)" and "g x=0" and "c\<noteq>0" 
  shows "(g has_sgnx - sgn c) (at_left x)" 
proof -
  have "(g has_sgnx -1) (at_left x)" when "c>0"
  proof -
    obtain d1 where "d1>0" and d1_def:"\<forall>h>0. h < d1 \<longrightarrow> g (x - h) < g x"
      using DERIV_pos_inc_left[OF g_deriv \<open>c>0\<close>] \<open>g x=0\<close> by auto
    have "(g has_sgnx -1) (at_left x)" 
      unfolding has_sgnx_def eventually_at_left
      apply (intro exI[where x="x-d1"])
      using \<open>d1>0\<close> d1_def 
      by (metis (no_types, hide_lams) add.commute add_uminus_conv_diff assms(2) diff_add_cancel 
          diff_strict_left_mono diff_zero minus_diff_eq sgn_neg)  
    thus ?thesis by auto 
  qed
  moreover have "(g has_sgnx 1) (at_left x)" when "c<0"
  proof -
    obtain d1 where "d1>0" and d1_def:"\<forall>h>0. h < d1 \<longrightarrow> g (x - h) > g x"
        using DERIV_neg_dec_left[OF g_deriv \<open>c<0\<close>] \<open>g x=0\<close> by auto
    have "(g has_sgnx 1) (at_left x)" 
        unfolding has_sgnx_def eventually_at_left
        apply (intro exI[where x="x-d1"])
        using \<open>d1>0\<close> d1_def 
        by (metis (no_types, hide_lams) add.commute add_uminus_conv_diff assms(2) diff_add_cancel
            diff_zero less_diff_eq minus_diff_eq sgn_pos)
    thus ?thesis using \<open>c<0\<close>  by auto
  qed
  ultimately show ?thesis using \<open>c\<noteq>0\<close> using sgn_real_def by auto
qed

lemma has_sgnx_derivative_at_right:
  assumes g_deriv:"(g has_field_derivative c) (at x)" and "g x=0" and "c\<noteq>0"
  shows "(g has_sgnx sgn c) (at_right x)"  
proof -
  have "(g has_sgnx 1) (at_right x)" when "c>0"
  proof -
    obtain d2 where "d2>0" and d2_def:"\<forall>h>0. h < d2 \<longrightarrow> g x < g (x + h)"
        using DERIV_pos_inc_right[OF g_deriv \<open>c>0\<close>] \<open>g x=0\<close> by auto 
    have "(g has_sgnx 1) (at_right x)" 
      unfolding has_sgnx_def eventually_at_right
      apply (intro exI[where x="x+d2"])
      using \<open>d2>0\<close> d2_def 
      by (metis add.commute assms(2) diff_add_cancel diff_less_eq less_add_same_cancel1 sgn_pos)
    thus ?thesis using \<open>c>0\<close> by auto
  qed
  moreover have "(g has_sgnx -1) (at_right x)" when "c<0"
  proof -
    obtain d2 where "d2>0" and d2_def:"\<forall>h>0. h < d2 \<longrightarrow> g x > g (x + h)"
      using DERIV_neg_dec_right[OF g_deriv \<open>c<0\<close>] \<open>g x=0\<close> by auto 
    have "(g has_sgnx -1) (at_right x)" 
      unfolding has_sgnx_def eventually_at_right
      apply (intro exI[where x="x+d2"])
      using \<open>d2>0\<close> d2_def 
      by (metis (no_types, hide_lams) add.commute add.right_inverse add_uminus_conv_diff assms(2) 
          diff_add_cancel diff_less_eq sgn_neg)
    thus ?thesis using \<open>c<0\<close> by auto
  qed
  ultimately show ?thesis using \<open>c\<noteq>0\<close> using sgn_real_def by auto
qed  

lemma has_sgnx_split:
  "(f has_sgnx c) (at x) \<longleftrightarrow> (f has_sgnx c) (at_left x) \<and> (f has_sgnx c) (at_right x)"
unfolding has_sgnx_def using eventually_at_split by auto    
        
lemma sgnx_at_top_IVT:
  assumes "sgnx (poly p) (at_right a) \<noteq> sgnx (poly p) at_top"
  shows "\<exists>x>a. poly p x=0"
proof (cases "p=0")
  case True
  then show ?thesis using gt_ex[of a] by simp
next
  case False
  from poly_has_sgnx_values[OF this] 
  have "(poly p has_sgnx 1) (at_right a) \<or> (poly p has_sgnx - 1) (at_right a)"
    "(poly p has_sgnx 1) at_top \<or> (poly p has_sgnx - 1) at_top"
    by auto
  moreover have ?thesis when has_r:"(poly p has_sgnx 1) (at_right a)" 
      and has_top:"(poly p has_sgnx -1) at_top"
  proof -
    obtain b where "b>a" "poly p b>0"
    proof -
      obtain a' where "a'>a" and a'_def:"\<forall>y>a. y < a' \<longrightarrow> sgn (poly p y) = 1"
        using has_r[unfolded has_sgnx_def eventually_at_right] by auto
      define b where "b=(a+a')/2"
      have "a<b" "b<a'" unfolding b_def using \<open>a'>a\<close> by auto
      moreover have "poly p b>0"
        using a'_def[rule_format,OF \<open>b>a\<close> \<open>b<a'\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain c where "c>b" "poly p c<0"
    proof -
      obtain b' where b'_def:"\<forall>n\<ge>b'. sgn (poly p n) = - 1"
        using has_top[unfolded has_sgnx_def eventually_at_top_linorder] by auto
      define c where "c=1+max b b'"
      have "c>b" "c\<ge>b'" unfolding c_def using \<open>b>a\<close> by auto
      moreover have "poly p c<0"
        using b'_def[rule_format,OF \<open>b'\<le>c\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately show ?thesis using poly_IVT_neg[of b c p] not_less by fastforce
  qed
  moreover have ?thesis when has_r:"(poly p has_sgnx -1) (at_right a)" 
      and has_top:"(poly p has_sgnx 1) at_top"
  proof -
    obtain b where "b>a" "poly p b<0"
    proof -
      obtain a' where "a'>a" and a'_def:"\<forall>y>a. y < a' \<longrightarrow> sgn (poly p y) = -1"
        using has_r[unfolded has_sgnx_def eventually_at_right] by auto
      define b where "b=(a+a')/2"
      have "a<b" "b<a'" unfolding b_def using \<open>a'>a\<close> by auto
      moreover have "poly p b<0"
        using a'_def[rule_format,OF \<open>b>a\<close> \<open>b<a'\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain c where "c>b" "poly p c>0"
    proof -
      obtain b' where b'_def:"\<forall>n\<ge>b'. sgn (poly p n) = 1"
        using has_top[unfolded has_sgnx_def eventually_at_top_linorder] by auto
      define c where "c=1+max b b'"
      have "c>b" "c\<ge>b'" unfolding c_def using \<open>b>a\<close> by auto
      moreover have "poly p c>0"
        using b'_def[rule_format,OF \<open>b'\<le>c\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately show ?thesis using poly_IVT_pos[of b c p] not_less by fastforce
  qed
  moreover have ?thesis when 
    "(poly p has_sgnx 1) (at_right a) \<and> (poly p has_sgnx 1) at_top
     \<or> (poly p has_sgnx - 1) (at_right a) \<and> (poly p has_sgnx -1) at_top" 
  proof -
    have "sgnx (poly p) (at_right a) = sgnx (poly p) at_top"
      using that has_sgnx_imp_sgnx by auto
    then have False using assms by simp
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed
  
lemma sgnx_at_left_at_right_IVT:
  assumes "sgnx (poly p) (at_right a) \<noteq> sgnx (poly p) (at_left b)" "a<b"
  shows "\<exists>x. a<x \<and> x<b \<and> poly p x=0"
proof (cases "p=0")
  case True
  then show ?thesis using \<open>a<b\<close> by (auto intro:exI[where x="(a+b)/2"])
next
  case False
  from poly_has_sgnx_values[OF this]
  have "(poly p has_sgnx 1) (at_right a) \<or> (poly p has_sgnx - 1) (at_right a)"
    "(poly p has_sgnx 1) (at_left b) \<or> (poly p has_sgnx - 1) (at_left b)"
    by auto
  moreover have ?thesis when has_r:"(poly p has_sgnx 1) (at_right a)" 
      and has_l:"(poly p has_sgnx -1) (at_left b)"
  proof -
    obtain c where "a<c" "c<b" "poly p c>0"
    proof -
      obtain a' where "a'>a" and a'_def:"\<forall>y>a. y < a' \<longrightarrow> sgn (poly p y) = 1"
        using has_r[unfolded has_sgnx_def eventually_at_right] by auto
      define c where "c=(a+min a' b)/2"
      have "a<c" "c<a'" "c<b" unfolding c_def using \<open>a'>a\<close> \<open>b>a\<close> by auto
      moreover have "poly p c>0"
        using a'_def[rule_format,OF \<open>c>a\<close> \<open>c<a'\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain d where "c<d""d<b" "poly p d<0"
    proof -
      obtain b' where "b'<b" and b'_def:"\<forall>y>b'. y < b \<longrightarrow> sgn (poly p y) = - 1"
        using has_l[unfolded has_sgnx_def eventually_at_left] by auto
      define d where "d=(b+max b' c)/2"
      have "b'<d" "d<b" "d>c" 
        unfolding d_def using \<open>b>b'\<close> \<open>b>c\<close> by auto
      moreover have "poly p d<0"
        using b'_def[rule_format, OF \<open>b'<d\<close> \<open>d<b\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately obtain x where "c<x" "x<d" "poly p x=0"
      using poly_IVT_neg[of c d p] by auto
    then show ?thesis using \<open>c>a\<close> \<open>d<b\<close> by (auto intro: exI[where x=x])
  qed
  moreover have ?thesis when has_r:"(poly p has_sgnx -1) (at_right a)" 
      and has_l:"(poly p has_sgnx 1) (at_left b)"
  proof -
    obtain c where "a<c" "c<b" "poly p c<0"
    proof -
      obtain a' where "a'>a" and a'_def:"\<forall>y>a. y < a' \<longrightarrow> sgn (poly p y) = -1"
        using has_r[unfolded has_sgnx_def eventually_at_right] by auto
      define c where "c=(a+min a' b)/2"
      have "a<c" "c<a'" "c<b" unfolding c_def using \<open>a'>a\<close> \<open>b>a\<close> by auto
      moreover have "poly p c<0"
        using a'_def[rule_format,OF \<open>c>a\<close> \<open>c<a'\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain d where "c<d""d<b" "poly p d>0"
    proof -
      obtain b' where "b'<b" and b'_def:"\<forall>y>b'. y < b \<longrightarrow> sgn (poly p y) = 1"
        using has_l[unfolded has_sgnx_def eventually_at_left] by auto
      define d where "d=(b+max b' c)/2"
      have "b'<d" "d<b" "d>c" 
        unfolding d_def using \<open>b>b'\<close> \<open>b>c\<close> by auto
      moreover have "poly p d>0"
        using b'_def[rule_format, OF \<open>b'<d\<close> \<open>d<b\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately obtain x where "c<x" "x<d" "poly p x=0"
      using poly_IVT_pos[of c d p] by auto
    then show ?thesis using \<open>c>a\<close> \<open>d<b\<close> by (auto intro: exI[where x=x])
  qed
  moreover have ?thesis when 
    "(poly p has_sgnx 1) (at_right a) \<and> (poly p has_sgnx 1) (at_left b)
     \<or> (poly p has_sgnx - 1) (at_right a) \<and> (poly p has_sgnx -1) (at_left b)" 
  proof -
    have "sgnx (poly p) (at_right a) = sgnx (poly p) (at_left b)"
      using that has_sgnx_imp_sgnx by auto
    then have False using assms by simp
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed
   
lemma sgnx_at_bot_IVT:
  assumes "sgnx (poly p) (at_left a) \<noteq> sgnx (poly p) at_bot"
  shows "\<exists>x<a. poly p x=0"
proof (cases "p=0")
  case True
  then show ?thesis using lt_ex[of a] by simp
next
  case False
  from poly_has_sgnx_values[OF this] 
  have "(poly p has_sgnx 1) (at_left a) \<or> (poly p has_sgnx - 1) (at_left a)"
    "(poly p has_sgnx 1) at_bot \<or> (poly p has_sgnx - 1) at_bot"
    by auto
  moreover have ?thesis when has_l:"(poly p has_sgnx 1) (at_left a)" 
      and has_bot:"(poly p has_sgnx -1) at_bot"
  proof -
    obtain b where "b<a" "poly p b>0"
    proof -
      obtain a' where "a'<a" and a'_def:"\<forall>y>a'. y < a \<longrightarrow> sgn (poly p y) = 1"
        using has_l[unfolded has_sgnx_def eventually_at_left] by auto
      define b where "b=(a+a')/2"
      have "a>b" "b>a'" unfolding b_def using \<open>a'<a\<close> by auto
      moreover have "poly p b>0"
        using a'_def[rule_format,OF \<open>b>a'\<close> \<open>b<a\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain c where "c<b" "poly p c<0"
    proof -
      obtain b' where b'_def:"\<forall>n\<le>b'. sgn (poly p n) = - 1"
        using has_bot[unfolded has_sgnx_def eventually_at_bot_linorder] by auto
      define c where "c=min b b'- 1"
      have "c<b" "c\<le>b'" unfolding c_def using \<open>b<a\<close> by auto
      moreover have "poly p c<0"
        using b'_def[rule_format,OF \<open>b'\<ge>c\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately show ?thesis using poly_IVT_pos[of c b p] using not_less by fastforce
  qed
  moreover have ?thesis when has_l:"(poly p has_sgnx -1) (at_left a)" 
      and has_bot:"(poly p has_sgnx 1) at_bot"
  proof -
    obtain b where "b<a" "poly p b<0"
    proof -
      obtain a' where "a'<a" and a'_def:"\<forall>y>a'. y < a \<longrightarrow> sgn (poly p y) = -1"
        using has_l[unfolded has_sgnx_def eventually_at_left] by auto
      define b where "b=(a+a')/2"
      have "a>b" "b>a'" unfolding b_def using \<open>a'<a\<close> by auto
      moreover have "poly p b<0"
        using a'_def[rule_format,OF \<open>b>a'\<close> \<open>b<a\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    moreover obtain c where "c<b" "poly p c>0"
    proof -
      obtain b' where b'_def:"\<forall>n\<le>b'. sgn (poly p n) = 1"
        using has_bot[unfolded has_sgnx_def eventually_at_bot_linorder] by auto
      define c where "c=min b b'- 1"
      have "c<b" "c\<le>b'" unfolding c_def using \<open>b<a\<close> by auto
      moreover have "poly p c>0"
        using b'_def[rule_format,OF \<open>b'\<ge>c\<close>] unfolding sgn_if by argo
      ultimately show ?thesis using that by auto
    qed
    ultimately show ?thesis using poly_IVT_neg[of c b p] using not_less by fastforce
  qed
  moreover have ?thesis when 
    "(poly p has_sgnx 1) (at_left a) \<and> (poly p has_sgnx 1) at_bot
     \<or> (poly p has_sgnx - 1) (at_left a) \<and> (poly p has_sgnx -1) at_bot" 
  proof -
    have "sgnx (poly p) (at_left a) = sgnx (poly p) at_bot"
      using that has_sgnx_imp_sgnx by auto
    then have False using assms by simp
    then show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed    

lemma sgnx_poly_nz:
  assumes "poly p x\<noteq>0"
  shows "sgnx (poly p) (at_left x) = sgn (poly p x)"
        "sgnx (poly p) (at_right x) = sgn (poly p x)"
proof -
  have "(poly p has_sgnx sgn(poly p x)) (at x)"
    apply (rule tendsto_nonzero_has_sgnx)
    using assms by auto
  then show "sgnx (poly p) (at_left x) = sgn (poly p x)"
        "sgnx (poly p) (at_right x) = sgn (poly p x)"
    unfolding has_sgnx_split by auto
qed
  
subsection \<open>Finite predicate segments over an interval\<close>

inductive finite_Psegments::"(real \<Rightarrow> bool) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" for P where
  emptyI: "a\<ge>b \<Longrightarrow> finite_Psegments P a b"|
  insertI_1: "\<lbrakk>s\<in>{a..<b};s=a\<or>P s;\<forall>t\<in>{s<..<b}. P t; finite_Psegments P a s\<rbrakk> 
        \<Longrightarrow> finite_Psegments P a b"|
  insertI_2: "\<lbrakk>s\<in>{a..<b};s=a\<or>P s;(\<forall>t\<in>{s<..<b}. \<not>P t);finite_Psegments P a s\<rbrakk> 
        \<Longrightarrow> finite_Psegments P a b" 

lemma finite_Psegments_pos_linear:
  assumes "finite_Psegments P (b*lb+c) (b*ub+c) " and "b>0"
  shows "finite_Psegments (P o (\<lambda>t. b*t+c)) lb ub" 
proof -    
  have [simp]:"b\<noteq>0" using \<open>b>0\<close> by auto
  show ?thesis 
  proof (rule finite_Psegments.induct[OF assms(1),
        of "\<lambda>lb' ub'. finite_Psegments (P o (\<lambda>t. b*t+c)) ((lb'-c)/b) ((ub'-c)/b)",simplified])
    (*really weird application of the induction rule, is there an alternative?*)
    fix lb ub f assume "(lb::real)\<le>ub"  
    then have "(lb - c) / b \<le> (ub - c) / b" 
      using \<open>b>0\<close> by (auto simp add:field_simps)
    then show "finite_Psegments (f \<circ> (\<lambda>t. b * t + c)) ((ub - c) / b) ((lb - c) / b)"
      by (rule finite_Psegments.emptyI)
  next
    fix s lb ub P
    assume asm: "lb \<le> s \<and> s < ub" 
       "\<forall>t\<in>{s<..<ub}. P t" 
       "finite_Psegments (P \<circ> (\<lambda>t. b * t + c)) ((lb - c) / b) ((s - c) / b)"
       "s = lb \<or> P s"
    show "finite_Psegments (P \<circ> (\<lambda>t. b * t + c)) ((lb - c) / b) ((ub - c) / b)"
      apply (rule finite_Psegments.insertI_1[of "(s-c)/b"])
      using asm \<open>b>0\<close>  by (auto simp add:field_simps)
  next
    fix s lb ub P
    assume asm: "lb \<le> s \<and> s < ub" 
       "\<forall>t\<in>{s<..<ub}. \<not> P t" 
       "finite_Psegments (P \<circ> (\<lambda>t. b * t + c)) ((lb - c) / b) ((s - c) / b)" 
       "s=lb \<or> P s"
    show "finite_Psegments (P \<circ> (\<lambda>t. b * t + c)) ((lb - c) / b) ((ub - c) / b)"
      apply (rule finite_Psegments.insertI_2[of "(s-c)/b"])
      using asm \<open>b>0\<close>  by (auto simp add:field_simps)
  qed
qed  

lemma finite_Psegments_congE:
  assumes "finite_Psegments Q lb ub" 
    "\<And>t. \<lbrakk>lb<t;t<ub\<rbrakk> \<Longrightarrow> Q t \<longleftrightarrow> P t "
  shows "finite_Psegments P lb ub" using assms
proof (induct rule:finite_Psegments.induct)
  case (emptyI a b)
  then show ?case using finite_Psegments.emptyI by auto
next
  case (insertI_1 s a b)
  show ?case 
  proof (rule finite_Psegments.insertI_1[of s])
    have "P s" when "s\<noteq>a"
    proof -
      have "s\<in>{a<..<b}" using \<open>s \<in> {a..<b}\<close> that by auto 
      then show ?thesis using insertI_1 by auto
    qed
    then show "s = a \<or> P s" by auto
  next
    show "s \<in> {a..<b}" " \<forall>t\<in>{s<..<b}. P t" "finite_Psegments P a s" using insertI_1 by auto
  qed  
next
  case (insertI_2 s a b)
  show ?case 
  proof (rule finite_Psegments.insertI_2[of s]) 
    have "P s" when "s\<noteq>a"
    proof -
      have "s\<in>{a<..<b}" using \<open>s \<in> {a..<b}\<close> that by auto 
      then show ?thesis using insertI_2 by auto
    qed
    then show "s = a \<or> P s" by auto
  next
    show "s \<in> {a..<b}" " \<forall>t\<in>{s<..<b}. \<not> P t" "finite_Psegments P a s" using insertI_2 by auto
  qed   
qed
  
lemma finite_Psegments_constI:
  assumes "\<And>t. \<lbrakk>a<t;t<b\<rbrakk> \<Longrightarrow> P t = c"
  shows "finite_Psegments P a b"
proof -
  have "finite_Psegments (\<lambda>_. c) a b"
  proof -
    have ?thesis when "a\<ge>b"
      using that finite_Psegments.emptyI by auto
    moreover have ?thesis when "a<b" "c"
      apply (rule finite_Psegments.insertI_1[of a])
      using that by (auto intro: finite_Psegments.emptyI)
    moreover have ?thesis when "a<b" "\<not>c"
      apply (rule finite_Psegments.insertI_2[of a])
      using that by (auto intro: finite_Psegments.emptyI)
    ultimately show ?thesis by argo
  qed
  then show ?thesis
    apply (elim finite_Psegments_congE)
    using assms by auto
qed    

context 
begin  

private lemma finite_Psegments_less_eq1:
  assumes "finite_Psegments P a c" "b\<le>c"
  shows "finite_Psegments P a b" using assms
proof (induct arbitrary: b rule:finite_Psegments.induct)
  case (emptyI a c)
  then show ?case using finite_Psegments.emptyI by auto
next
  case (insertI_1 s a c)  
  have ?case when "b\<le>s" using insertI_1 that by auto
  moreover have ?case when "b>s" 
  proof -
    have "s \<in> {a..<b}" using that \<open>s \<in> {a..<c}\<close> \<open>b \<le> c\<close> by auto 
    moreover have "\<forall>t\<in>{s<..<b}. P t" using \<open>\<forall>t\<in>{s<..<c}. P t\<close> that \<open>b \<le> c\<close> by auto
    ultimately show ?case 
      using finite_Psegments.insertI_1[OF _ _ _ \<open>finite_Psegments P a s\<close>] \<open> s = a \<or> P s\<close> by auto
  qed
  ultimately show ?case by fastforce
next
  case (insertI_2 s a c)
  have ?case when "b\<le>s" using insertI_2 that by auto
  moreover have ?case when "b>s" 
  proof -
    have "s \<in> {a..<b}" using that \<open>s \<in> {a..<c}\<close> \<open>b \<le> c\<close> by auto 
    moreover have "\<forall>t\<in>{s<..<b}. \<not> P t" using \<open>\<forall>t\<in>{s<..<c}. \<not> P t\<close> that \<open>b \<le> c\<close> by auto
    ultimately show ?case 
      using finite_Psegments.insertI_2[OF _ _ _ \<open>finite_Psegments P a s\<close>] \<open> s = a \<or> P s\<close> by auto
  qed
  ultimately show ?case by fastforce
qed  
 
  
private lemma finite_Psegments_less_eq2:
  assumes "finite_Psegments P a c" "a\<le>b"
  shows "finite_Psegments P b c" using assms  
proof (induct arbitrary:  rule:finite_Psegments.induct)
  case (emptyI a c)
  then show ?case using finite_Psegments.emptyI by auto 
next
  case (insertI_1 s a c)
  have ?case when "s\<le>b"
  proof -
    have "\<forall>t\<in>{b<..<c}. P t" using insertI_1 that by auto
    then show ?thesis by (simp add: finite_Psegments_constI)
  qed
  moreover have ?case when "s>b"
    apply (rule finite_Psegments.insertI_1[where s=s])
    using insertI_1 that by auto
  ultimately show ?case by linarith
next
  case (insertI_2 s a c)
  have ?case when "s\<le>b"
  proof -
    have "\<forall>t\<in>{b<..<c}. \<not> P t" using insertI_2 that by auto
    then show ?thesis by (metis finite_Psegments_constI greaterThanLessThan_iff)
  qed
  moreover have ?case when "s>b"
    apply (rule finite_Psegments.insertI_2[where s=s])
    using insertI_2 that by auto
  ultimately show ?case by linarith
qed  


lemma finite_Psegments_included:
  assumes "finite_Psegments P a d" "a\<le>b" "c\<le>d"
  shows "finite_Psegments P b c"  
  using finite_Psegments_less_eq2 finite_Psegments_less_eq1 assms by blast      
end      

lemma finite_Psegments_combine:
  assumes "finite_Psegments P a b" "finite_Psegments P b c" "b\<in>{a..c}" "closed ({x. P x} \<inter> {a..c})" 
  shows "finite_Psegments P a c"  using assms(2,1,3,4)
proof (induct rule:finite_Psegments.induct)
  case (emptyI b c)
  then show ?case using finite_Psegments_included by auto
next
  case (insertI_1 s b c)
  have "P s" 
  proof -
    have "s<c" using insertI_1 by auto
    define S where "S = {x. P x} \<inter> {s..(s+c)/2}"
    have "closed S"
    proof -
      have "closed ({a. P a} \<inter> {a..c})" using insertI_1(8) .
      moreover have "S = ({a. P a} \<inter> {a..c}) \<inter> {s..(s+c)/2}"
        using insertI_1(1,7) unfolding S_def by (auto simp add:field_simps)
      ultimately show ?thesis
        using closed_Int[of "{a. P a} \<inter> {a..c}" "{s..(s+c)/2}"] by blast
    qed
    moreover have "\<exists>y\<in>S. dist y s < e" when "e>0" for e 
    proof -
      define y where "y = min ((s+c)/2) (e/2+s)"
      have "y\<in>S"
      proof -
        have "y\<in>{s..(s+c)/2}" unfolding y_def
          using \<open>e>0\<close> \<open>s<c\<close> by (auto simp add:min_mult_distrib_left algebra_simps)
        moreover have "P y" 
          apply (rule insertI_1(3)[rule_format])
          unfolding y_def
          using \<open>e>0\<close> \<open>s<c\<close> 
          by (auto simp add:algebra_simps min_mult_distrib_left min_less_iff_disj)
        ultimately show ?thesis unfolding S_def by auto   
      qed
      moreover have "dist y s <e"
        unfolding y_def using \<open>e>0\<close> \<open>s<c\<close> 
        by (auto simp add:algebra_simps min_mult_distrib_left min_less_iff_disj dist_real_def)
      ultimately show ?thesis by auto
    qed
    ultimately have "s\<in>S" using closed_approachable by auto
    then show ?thesis unfolding S_def by auto
  qed
  show ?case 
  proof (rule finite_Psegments.insertI_1[of s])
    show " s \<in> {a..<c}" "s = a \<or> P s" "\<forall>t\<in>{s<..<c}. P t"
      using insertI_1 \<open>P s\<close> by auto
  next
    have "closed ({a. P a} \<inter> {a..s})" 
      using closed_Int[OF \<open>closed ({a. P a} \<inter> {a..c})\<close>,of "{a..s}",simplified]
      apply (elim arg_elim[of closed])
      using \<open>s \<in> {b..<c}\<close> \<open>b \<in> {a..c}\<close> by auto
    then show "finite_Psegments P a s" using insertI_1 by auto
  qed
next
  case (insertI_2 s b c)
  have ?case when "P s"
  proof (rule finite_Psegments.insertI_2[of s])
    show "s \<in> {a..<c}" "s = a \<or> P s" "\<forall>t\<in>{s<..<c}. \<not> P t" using that insertI_2 by auto
  next
    have "closed ({a. P a} \<inter> {a..s})" 
      using closed_Int[OF \<open>closed ({a. P a} \<inter> {a..c})\<close>,of "{a..s}",simplified]
      apply (elim arg_elim[of closed])
      using  \<open>s \<in> {b..<c}\<close> \<open>b \<in> {a..c}\<close> by auto
    then show "finite_Psegments P a s" using insertI_2 by auto
  qed  
  moreover have ?case when "\<not> P s" "s=b" using \<open>finite_Psegments P a b\<close>  
  proof (cases rule:finite_Psegments.cases)
    case emptyI
    then show ?thesis using insertI_2 that 
      by (metis antisym_conv atLeastAtMost_iff finite_Psegments.insertI_2)
  next
    case (insertI_1 s0)
    have "P s" 
    proof -
      have "s0<s" using insertI_1 atLeastLessThan_iff that(2) by blast    
      define S where "S = {x. P x} \<inter> {(s0+s)/2..s}"
      have "closed S"
        using closed_Int[OF \<open>closed ({a. P a} \<inter> {a..c})\<close>,of "{(s0+s)/2..s}",simplified]  
        apply (elim arg_elim[of closed])
        unfolding S_def using \<open>s0 \<in> {a..<b}\<close> \<open> s \<in> {b..<c}\<close> \<open>b \<in> {a..c}\<close> by auto    
      moreover have "\<exists>y\<in>S. dist y s < e" when "e>0" for e 
      proof -
        define y where "y = max ((s+s0)/2) (s-e/2)"
        have "y\<in>S"
        proof -
          have "y\<in>{(s0+s)/2..s}" unfolding y_def
            using \<open>e>0\<close> \<open>s0<s\<close> by (auto simp add:field_simps min_mult_distrib_left)
          moreover have "P y" 
            apply (rule insertI_1(3)[rule_format])
            unfolding y_def
            using \<open>e>0\<close> \<open>s0<s\<close> \<open>s=b\<close>
            by (auto simp add:field_simps max_mult_distrib_left less_max_iff_disj)
          ultimately show ?thesis unfolding S_def by auto   
        qed
        moreover have "dist y s <e"
          unfolding y_def using \<open>e>0\<close> \<open>s0<s\<close> 
          by (auto simp add:algebra_simps max_mult_distrib_left less_max_iff_disj dist_real_def 
              max_add_distrib_right)
        ultimately show ?thesis by auto
      qed
      ultimately have "s\<in>S" using closed_approachable by auto
      then show ?thesis unfolding S_def by auto
    qed  
    then have False using \<open>\<not> P s\<close> by auto
    then show ?thesis by simp
  next
    case (insertI_2 s0)
    have *: "\<forall>t\<in>{s0<..<c}. \<not> P t" 
      using \<open> \<forall>t\<in>{s<..<c}. \<not> P t\<close> that \<open>\<forall>t\<in>{s0<..<b}. \<not> P t\<close> 
      by force
    show ?thesis 
      apply (rule finite_Psegments.insertI_2[of s0])
      subgoal using insertI_2.prems(2) local.insertI_2(1) by auto   
      subgoal using \<open>s0 = a \<or> P s0\<close> .
      subgoal using * .
      subgoal using \<open>finite_Psegments P a s0\<close> .
      done
  qed
  moreover note \<open>s = b \<or> P s\<close>  
  ultimately show ?case by auto
qed
 
subsection \<open>Finite segment intersection of a path with the imaginary axis\<close>

definition finite_ReZ_segments::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> bool" where
  "finite_ReZ_segments g z = finite_Psegments (\<lambda>t. Re (g t - z) = 0) 0 1"    

lemma finite_ReZ_segments_joinpaths:
  assumes g1:"finite_ReZ_segments g1 z" and g2: "finite_ReZ_segments g2 z" and
    "path g1" "path g2" "pathfinish g1=pathstart g2"
  shows "finite_ReZ_segments (g1+++g2) z" 
proof -
  define P where "P = (\<lambda>t. (Re ((g1 +++ g2) t - z) = 0 \<and> 0<t \<and> t<1) \<or> t=0 \<or> t=1)"
  have "finite_Psegments P 0 (1/2)" 
  proof -
    have "finite_Psegments (\<lambda>t. Re (g1 t - z) = 0) 0 1" 
      using g1 unfolding finite_ReZ_segments_def .
    then have "finite_Psegments (\<lambda>t. Re (g1 (2 * t) - z) = 0) 0 (1/2)" 
      apply (drule_tac finite_Psegments_pos_linear[of _ 2 0 0 "1/2",simplified])
      by (auto simp add:comp_def)
    then show ?thesis
      unfolding P_def joinpaths_def
      by (elim finite_Psegments_congE,auto)
  qed
  moreover have "finite_Psegments P (1/2) 1" 
  proof -
    have "finite_Psegments (\<lambda>t. Re (g2 t - z) = 0) 0 1" 
      using g2 unfolding finite_ReZ_segments_def .
    then have "finite_Psegments (\<lambda>t. Re (g2 (2 * t-1) - z) = 0) (1/2) 1"  
      apply (drule_tac finite_Psegments_pos_linear[of _ 2 "1/2" "-1" 1,simplified])
      by (auto simp add:comp_def)
    then show ?thesis
      unfolding P_def joinpaths_def
      apply (elim finite_Psegments_congE)
      by auto
  qed  
  moreover have "closed {x. P x}"
  proof -
    define Q where "Q=(\<lambda>t. Re ((g1 +++ g2) t - z) = 0)"
    have "continuous_on {0<..<1} (g1+++g2)"
      using path_join_imp[OF \<open>path g1\<close> \<open>path g2\<close> \<open>pathfinish g1=pathstart g2\<close>] 
      unfolding path_def by (auto elim:continuous_on_subset)
    from continuous_on_Re[OF this] have "continuous_on {0<..<1} (\<lambda>x. Re ((g1 +++ g2) x))" .
    from continuous_on_open_Collect_neq[OF this,of "\<lambda>_. Re z",OF continuous_on_const,simplified]
    have "open {t. Re ((g1 +++ g2) t - z) \<noteq> 0 \<and> 0<t \<and> t<1}" 
       by (elim arg_elim[where f="open"],auto)
    from closed_Diff[of "{0::real..1}",OF _ this,simplified]
    show "closed {x. P x}" 
      apply (elim arg_elim[where f=closed])
      by (auto simp add:P_def)
  qed
  ultimately have "finite_Psegments P 0 1"
    using finite_Psegments_combine[of _ 0 "1/2" 1] by auto
  then show ?thesis 
    unfolding finite_ReZ_segments_def P_def
    by (elim finite_Psegments_congE,auto)
qed
      
lemma finite_ReZ_segments_congE:
  assumes "finite_ReZ_segments p1 z1" 
    "\<And>t. \<lbrakk>0<t;t<1\<rbrakk> \<Longrightarrow>  Re(p1 t- z1) = Re(p2 t - z2)"
  shows "finite_ReZ_segments p2 z2"      
  using assms unfolding finite_ReZ_segments_def
  apply (elim finite_Psegments_congE)
  by auto 
       
lemma finite_ReZ_segments_constI:
  assumes "\<forall>t. 0<t\<and>t<1 \<longrightarrow> g t = c"
  shows "finite_ReZ_segments g z" 
proof -
  have "finite_ReZ_segments (\<lambda>_. c) z" 
    unfolding finite_ReZ_segments_def 
    by (rule finite_Psegments_constI,auto)
  then show ?thesis using assms
    by (elim finite_ReZ_segments_congE,auto)
qed 

lemma finite_ReZ_segment_cases [consumes 1, case_names subEq subNEq,cases pred:finite_ReZ_segments]:
  assumes "finite_ReZ_segments g z"
    and subEq:"(\<And>s. \<lbrakk>s \<in> {0..<1};s=0\<or>Re (g s) = Re z;
          \<forall>t\<in>{s<..<1}. Re (g t) = Re z;finite_ReZ_segments (subpath 0 s g) z\<rbrakk> \<Longrightarrow> P)" 
    and subNEq:"(\<And>s. \<lbrakk>s \<in> {0..<1};s=0\<or>Re (g s) = Re z;
          \<forall>t\<in>{s<..<1}. Re (g t) \<noteq> Re z;finite_ReZ_segments (subpath 0 s g) z\<rbrakk> \<Longrightarrow> P)"
  shows "P"  
using assms(1) unfolding finite_ReZ_segments_def
proof (cases rule:finite_Psegments.cases)
  case emptyI
  then show ?thesis by auto
next
  case (insertI_1 s)
  have "finite_ReZ_segments (subpath 0 s g) z" 
  proof (cases "s=0")
    case True
    show ?thesis
      apply (rule finite_ReZ_segments_constI)
      using True unfolding subpath_def by auto
  next
    case False
    then have "s>0" using \<open>s\<in>{0..<1}\<close> by auto
    from finite_Psegments_pos_linear[OF _ this,of _ 0 0 1] insertI_1(4)
    show "finite_ReZ_segments (subpath 0 s g) z"
      unfolding finite_ReZ_segments_def comp_def subpath_def by auto
  qed  
  then show ?thesis using subEq insertI_1 by force
next
  case (insertI_2 s)
  have "finite_ReZ_segments (subpath 0 s g) z" 
  proof (cases "s=0")
    case True
    show ?thesis
      apply (rule finite_ReZ_segments_constI)
      using True unfolding subpath_def by auto
  next
    case False
    then have "s>0" using \<open>s\<in>{0..<1}\<close> by auto
    from finite_Psegments_pos_linear[OF _ this,of _ 0 0 1] insertI_2(4)
    show "finite_ReZ_segments (subpath 0 s g) z"
      unfolding finite_ReZ_segments_def comp_def subpath_def by auto
  qed
  then show ?thesis using subNEq insertI_2 by force
qed         
  
lemma finite_ReZ_segments_induct [case_names sub0 subEq subNEq, induct pred:finite_ReZ_segments]:
  assumes "finite_ReZ_segments g z"
  assumes  sub0:"\<And>g z. (P (subpath 0 0 g) z)" 
    and subEq:"(\<And>s g z. \<lbrakk>s \<in> {0..<1};s=0\<or>Re (g s) = Re z;
          \<forall>t\<in>{s<..<1}. Re (g t) = Re z;finite_ReZ_segments (subpath 0 s g) z; 
          P (subpath 0 s g) z\<rbrakk> \<Longrightarrow> P g z)" 
    and subNEq:"(\<And>s g z. \<lbrakk>s \<in> {0..<1};s=0\<or>Re (g s) = Re z;
          \<forall>t\<in>{s<..<1}. Re (g t) \<noteq> Re z;finite_ReZ_segments (subpath 0 s g) z;
          P (subpath 0 s g) z\<rbrakk> \<Longrightarrow> P g z)"
  shows "P g z" 
proof -
  have "finite_Psegments (\<lambda>t. Re (g t - z) = 0) 0 1" 
    using assms(1) unfolding finite_ReZ_segments_def by auto
  then have "(0::real)\<le>1 \<longrightarrow> P (subpath 0 1 g) z"
  proof (induct rule: finite_Psegments.induct[of _ 0 1 "\<lambda>a b. b\<ge>a \<longrightarrow> P (subpath a b g) z"] )
    case (emptyI a b)
    then show ?case using sub0[of "subpath a b g"] unfolding subpath_def by auto 
  next
    case (insertI_1 s a b)
    have ?case when "a=b"
      using sub0[of "subpath a b g"] that unfolding subpath_def by auto        
    moreover have ?case when "a\<noteq>b"
    proof -
      have "b>a" using that \<open>s \<in> {a..<b}\<close> by auto
      define s'::real where "s'=(s-a)/(b-a)"  
      have "P (subpath a b g) z" 
      proof (rule subEq[of s' "subpath a b g"])
        show "\<forall>t\<in>{s'<..<1}. Re (subpath a b g t) = Re z" 
        proof 
          fix t assume "t \<in> {s'<..<1}"
          then have "(b - a) * t + a\<in>{s<..<b}" 
            unfolding s'_def using \<open>b>a\<close> \<open>s \<in> {a..<b}\<close>
            apply (auto simp add:field_simps)
            by (sos "((((A<0 * (A<1 * A<2)) * R<1) + (((A<=1 * (A<0 * R<1)) * (R<1 * [1]^2))
               + ((A<=0 * (A<0 * (A<1 * R<1))) * (R<1 * [1]^2)))))")  
          then have "Re (g ((b - a) * t + a) - z) = 0"
            using insertI_1(3)[rule_format,of "(b - a) * t + a"] by auto
          then show "Re (subpath a b g t) = Re z" 
            unfolding subpath_def by auto
        qed
        show "finite_ReZ_segments (subpath 0 s' (subpath a b g)) z"
        proof (cases "s=a")
          case True
          then show ?thesis unfolding s'_def subpath_def 
            by (auto intro:finite_ReZ_segments_constI)
        next
          case False
          have "finite_Psegments (\<lambda>t. Re (g t - z) = 0) a s"
            using insertI_1(4) unfolding finite_ReZ_segments_def by auto
          then have "finite_Psegments ((\<lambda>t. Re (g t - z) = 0) \<circ> (\<lambda>t. (s - a) * t + a)) 0 1" 
            apply (elim finite_Psegments_pos_linear[of _ "s-a" 0 a 1,simplified])
            using False \<open>s\<in>{a..<b}\<close> by auto
          then show ?thesis 
            using \<open>b>a\<close> unfolding finite_ReZ_segments_def subpath_def s'_def comp_def
            by auto
        qed
        show "s' \<in> {0..<1}"
          using \<open>b>a\<close> \<open>s\<in>{a..<b}\<close> unfolding s'_def 
          by (auto simp add:field_simps)
        show "P (subpath 0 s' (subpath a b g)) z"
        proof -
          have "P (subpath a s g) z" using insertI_1(1,5) by auto
          then show ?thesis 
            using \<open>b>a\<close> unfolding s'_def subpath_def  by simp  
        qed
        show "s' = 0 \<or> Re (subpath a b g s') = Re z"
        proof -
          have ?thesis when "s=a"
            using that unfolding s'_def by auto
          moreover have ?thesis when "Re (g s - z) = 0"
            using that unfolding s'_def subpath_def by auto
          ultimately show ?thesis using \<open>s = a \<or> Re (g s - z) = 0\<close> by auto
        qed
      qed
      then show ?thesis using \<open>b>a\<close> by auto
    qed
    ultimately show ?case by auto
  next
    case (insertI_2 s a b)
    have ?case when "a=b"
      using sub0[of "subpath a b g"] that unfolding subpath_def by auto        
    moreover have ?case when "a\<noteq>b"
    proof -
      have "b>a" using that \<open>s \<in> {a..<b}\<close> by auto
      define s'::real where "s'=(s-a)/(b-a)"  
      have "P (subpath a b g) z" 
      proof (rule subNEq[of s' "subpath a b g"])
        show "\<forall>t\<in>{s'<..<1}. Re (subpath a b g t) \<noteq> Re z" 
        proof 
          fix t assume "t \<in> {s'<..<1}"
          then have "(b - a) * t + a\<in>{s<..<b}" 
            unfolding s'_def using \<open>b>a\<close> \<open>s \<in> {a..<b}\<close>
            apply (auto simp add:field_simps)
            by (sos "((((A<0 * (A<1 * A<2)) * R<1) + (((A<=1 * (A<0 * R<1)) * (R<1 * [1]^2)) + 
              ((A<=0 * (A<0 * (A<1 * R<1))) * (R<1 * [1]^2)))))")  
          then have "Re (g ((b - a) * t + a) - z) \<noteq> 0"
            using insertI_2(3)[rule_format,of "(b - a) * t + a"] by auto
          then show "Re (subpath a b g t) \<noteq> Re z" 
            unfolding subpath_def by auto
        qed
        show "finite_ReZ_segments (subpath 0 s' (subpath a b g)) z"
        proof (cases "s=a")
          case True
          then show ?thesis unfolding s'_def subpath_def 
            by (auto intro:finite_ReZ_segments_constI)
        next
          case False
          have "finite_Psegments (\<lambda>t. Re (g t - z) = 0) a s"
            using insertI_2(4) unfolding finite_ReZ_segments_def by auto
          then have "finite_Psegments ((\<lambda>t. Re (g t - z) = 0) \<circ> (\<lambda>t. (s - a) * t + a)) 0 1" 
            apply (elim finite_Psegments_pos_linear[of _ "s-a" 0 a 1,simplified])
            using False \<open>s\<in>{a..<b}\<close> by auto
          then show ?thesis 
            using \<open>b>a\<close> unfolding finite_ReZ_segments_def subpath_def s'_def comp_def
            by auto
        qed
        show "s' \<in> {0..<1}"
          using \<open>b>a\<close> \<open>s\<in>{a..<b}\<close> unfolding s'_def 
          by (auto simp add:field_simps)
        show "P (subpath 0 s' (subpath a b g)) z"
        proof -
          have "P (subpath a s g) z" using insertI_2(1,5) by auto
          then show ?thesis 
            using \<open>b>a\<close> unfolding s'_def subpath_def  by simp  
        qed
        show "s' = 0 \<or> Re (subpath a b g s') = Re z"
        proof -
          have ?thesis when "s=a"
            using that unfolding s'_def by auto
          moreover have ?thesis when "Re (g s - z) = 0"
            using that unfolding s'_def subpath_def by auto
          ultimately show ?thesis using \<open>s = a \<or> Re (g s - z) = 0\<close> by auto
        qed
      qed
      then show ?thesis using \<open>b>a\<close> by auto
    qed
    ultimately show ?case by auto
  qed
  then show ?thesis by auto
qed

lemma finite_ReZ_segments_shiftpah:
  assumes "finite_ReZ_segments g z" "s\<in>{0..1}" "path g" and loop:"pathfinish g = pathstart g" 
  shows "finite_ReZ_segments (shiftpath s g) z"
proof -
  have "finite_Psegments (\<lambda>t. Re (shiftpath s g t - z) = 0) 0 (1-s)"
  proof -
    have "finite_Psegments (\<lambda>t. Re (g t) = Re z) s 1" 
      using assms finite_Psegments_included[of _ 0 1 s] unfolding finite_ReZ_segments_def  
      by force   
    then have "finite_Psegments (\<lambda>t. Re (g (s + t) - z) = 0) 0 (1-s)" 
      using finite_Psegments_pos_linear[of "\<lambda>t. Re (g t - z) =0" 1 0 s "1-s",simplified]
      unfolding comp_def by (auto simp add:algebra_simps)
    then show ?thesis unfolding shiftpath_def
      apply (elim finite_Psegments_congE)
      using \<open>s\<in>{0..1}\<close> by auto  
  qed
  moreover have "finite_Psegments (\<lambda>t. Re (shiftpath s g t - z) = 0) (1-s) 1"  
  proof -
    have "finite_Psegments (\<lambda>t. Re (g t) = Re z) 0 s " 
      using assms finite_Psegments_included unfolding finite_ReZ_segments_def  
      by force   
    then have "finite_Psegments (\<lambda>t. Re (g (s + t - 1) - z) = 0) (1-s) 1" 
      using finite_Psegments_pos_linear[of "\<lambda>t. Re (g t - z) =0" 1 "1-s" "s-1" 1,simplified]
      unfolding comp_def by (auto simp add:algebra_simps)
    then show ?thesis unfolding shiftpath_def
      apply (elim finite_Psegments_congE)
      using \<open>s\<in>{0..1}\<close> by auto  
  qed
  moreover have "1 - s \<in> {0..1}" using \<open>s\<in>{0..1}\<close> by auto
  moreover have "closed ({x. Re (shiftpath s g x - z) = 0} \<inter> {0..1})"
  proof -
    let ?f = "\<lambda>x. Re (shiftpath s g x - z)"  
    have "continuous_on {0..1} ?f"
      using path_shiftpath[OF \<open>path g\<close> loop \<open>s\<in>{0..1}\<close>] unfolding path_def
      by (auto intro: continuous_intros)
    from continuous_closed_preimage_constant[OF this,of 0,simplified] 
    show ?thesis 
      apply (elim arg_elim[of closed])
      by force
  qed
  ultimately show ?thesis unfolding finite_ReZ_segments_def 
    by (rule finite_Psegments_combine[where b="1-s"])  
qed
     
lemma finite_imp_finite_ReZ_segments:
  assumes "finite {t. Re (g t - z) = 0 \<and> 0 \<le> t \<and> t\<le>1}"
  shows "finite_ReZ_segments g z"
proof -
  define P where "P = (\<lambda>t. Re (g t - z) = 0)"
  define rs where "rs=(\<lambda>b. {t. P t \<and> 0 < t \<and> t<b})"
  have "finite_Psegments P 0 b" when "finite (rs b)" "b>0" for b
  using that
  proof (induct "card (rs b)" arbitrary:b rule:nat_less_induct)
    case ind:1
    have ?case when "rs b= {}"
      apply (rule finite_Psegments.intros(3)[of 0])
      using that \<open>0 < b\<close> unfolding rs_def by (auto intro:finite_Psegments.intros)  
    moreover have ?case when "rs b\<noteq>{}"
    proof -
      define lj where "lj = Max (rs b)" 
      have "0<lj" "lj<b" "P lj"
        using Max_in[OF \<open>finite (rs b)\<close> \<open>rs b\<noteq>{}\<close>,folded lj_def]
        unfolding rs_def by auto
      show ?thesis 
      proof (rule finite_Psegments.intros(3)[of lj])
        show "lj \<in> {0..<b}" " lj = 0 \<or> P lj" 
          using \<open>0<lj\<close> \<open>lj<b\<close> \<open>P lj\<close> by auto
        show "\<forall>t\<in>{lj<..<b}. \<not> P t"
        proof (rule ccontr)
          assume " \<not> (\<forall>t\<in>{lj<..<b}. \<not> P t) "
          then obtain t where t:"P t" "lj < t" "t < b" by auto
          then have "t\<in>rs b" unfolding rs_def using \<open>lj>0\<close> by auto
          then have "t\<le>lj" using Max_ge[OF \<open>finite (rs b)\<close>,of t] unfolding lj_def by auto
          then show False using \<open>t>lj\<close> by auto
        qed
        show "finite_Psegments P 0 lj"
        proof (rule ind.hyps[rule_format,of "card (rs lj)" lj,simplified])
          show "finite (rs lj)"
            using \<open>finite (rs b)\<close> unfolding rs_def using \<open>lj<b\<close> 
            by (auto elim!:rev_finite_subset )
          show "card (rs lj) < card (rs b)"
            apply (rule psubset_card_mono[OF \<open>finite (rs b)\<close>])
            using Max_in \<open>finite (rs lj)\<close> \<open>lj < b\<close> lj_def rs_def that by fastforce
          show "0 < lj" using \<open>0<lj\<close> .
        qed
      qed
    qed
    ultimately show ?case by auto 
  qed
  moreover have "finite (rs 1)"
    using assms unfolding rs_def P_def
    by (auto elim:rev_finite_subset)
  ultimately have "finite_Psegments P 0 1" by auto
  then show ?thesis unfolding P_def finite_ReZ_segments_def .
qed
  
lemma finite_ReZ_segments_poly_linepath:
  shows "finite_ReZ_segments (poly p o linepath a b) z" 
proof -
  define P where "P=map_poly Re (pcompose (p-[:z:]) [:a,b-a:])"
  have *:"Re ((poly p \<circ> linepath a b) t - z) = 0 \<longleftrightarrow> poly P t=0" for t
    unfolding inner_complex_def P_def linepath_def comp_def
    apply (subst Re_poly_of_real[symmetric])
    by (auto simp add: algebra_simps poly_pcompose scaleR_conv_of_real)
  have ?thesis when "P\<noteq>0"
  proof -
    have "finite {t. poly P t=0}" using that poly_roots_finite by auto
    then have "finite {t. Re ((poly p \<circ> linepath a b) t - z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
      using *
      by auto
    then show ?thesis   
      using finite_imp_finite_ReZ_segments[of "poly p o linepath a b" z] by auto
  qed
  moreover have ?thesis when "P=0"
    unfolding finite_ReZ_segments_def
    apply (rule finite_Psegments_constI[where c=True])  
    apply (subst *)
    using that by auto 
  ultimately show ?thesis by auto
qed  
  
lemma part_circlepath_half_finite_inter:
  assumes "st\<noteq>tt" "r\<noteq>0" "c\<noteq>0"
  shows "finite {t. part_circlepath z0 r st tt t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}" (is "finite ?T")
proof -
  let ?S = "{\<theta>. (z0+r*exp (\<i> * \<theta> )) \<bullet> c = d \<and> \<theta> \<in> closed_segment st tt}"
  define S where "S \<equiv> {\<theta>. (z0+r*exp (\<i> * \<theta> )) \<bullet> c = d \<and> \<theta> \<in> closed_segment st tt}"
  have "S = linepath st tt ` ?T"
  proof   
    define g where "g\<equiv>(\<lambda>t. (t-st)/(tt -st))"
    have "0\<le>g t" "g t\<le>1" when "t \<in> closed_segment st tt " for t
      using that \<open>st\<noteq>tt\<close> closed_segment_eq_real_ivl unfolding  g_def real_scaleR_def
      by (auto simp add:divide_simps)
    moreover have "linepath st tt (g t) =t" "g (linepath st tt t) = t" for t
      unfolding linepath_def g_def real_scaleR_def using \<open>st\<noteq>tt\<close>
      apply (simp_all add:divide_simps)
      by (auto simp add:algebra_simps )
    ultimately have "x\<in>linepath st tt ` ?T" when "x\<in>S" for x
      using that unfolding S_def 
      by (auto intro!:image_eqI[where x="g x"] simp add:part_circlepath_def)
    then show "S \<subseteq> linepath st tt ` ?T" by auto
  next
    have "x\<in>S" when "x\<in>linepath st tt ` ?T" for x
      using that unfolding part_circlepath_def S_def
      by (auto simp add: linepath_in_path)
    then show "linepath st tt ` ?T \<subseteq> S" by auto
  qed
  moreover have "finite S" 
  proof -
    define a' b' c' where "a'=r * Re c" and "b' = r* Im c" and "c'=Im c * Im z0 + Re z0 * Re c - d"
    define f where "f \<theta>= a' * cos \<theta> + b' * sin \<theta> + c'" for \<theta>
    have "(z0+r*exp (\<i> * \<theta> )) \<bullet> c = d \<longleftrightarrow> f \<theta> = 0" for \<theta>
      unfolding exp_Euler inner_complex_def f_def a'_def b'_def c'_def
      by (auto simp add:algebra_simps cos_of_real sin_of_real)
    then have *:"S = roots f \<inter> closed_segment st tt"
      unfolding S_def roots_within_def by auto
    have "uniform_discrete S"
    proof -
      have "a' \<noteq> 0 \<or> b' \<noteq> 0 \<or> c' \<noteq> 0" 
        using assms complex_eq_iff unfolding a'_def b'_def c'_def 
        by auto
      then have "periodic_set (roots f) (4 * pi)"
        using periodic_set_sin_cos_linear[of a' b' c',folded f_def] by auto
      then have "uniform_discrete (roots f)" using periodic_imp_uniform_discrete by auto
      then show ?thesis unfolding * by auto
    qed
    moreover have "bounded S" unfolding * 
      by (simp add: bounded_Int bounded_closed_segment)
    ultimately show ?thesis using uniform_discrete_finite_iff by auto
  qed
  moreover have "inj_on (linepath st tt) ?T" 
  proof -
    have "inj (linepath st tt)"
      unfolding linepath_def using assms inj_segment by blast
    then show ?thesis by (auto elim:subset_inj_on)
  qed
  ultimately show ?thesis by (auto elim!: finite_imageD)
qed

lemma linepath_half_finite_inter:
  assumes "a \<bullet> c \<noteq> d \<or> b \<bullet> c \<noteq> d"
  shows "finite {t. linepath a b t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}" (is "finite ?S")
proof (rule ccontr)
  assume asm:"infinite ?S"
  obtain t1 t2 where u1u2:"t1\<noteq>t2" "t1\<in>?S" "t2\<in>?S"
  proof -
    obtain t1 where "t1\<in>?S" using not_finite_existsD asm by blast
    moreover have "\<exists>u2. u2\<in>?S-{t1}" 
      using infinite_remove[OF asm,of t1] 
      by (meson finite.emptyI rev_finite_subset subsetI)
    ultimately show ?thesis using that by auto
  qed
  have t1:"(1-t1)*(a \<bullet> c) + t1 * (b \<bullet> c) = d"
    using \<open>t1\<in>?S\<close> unfolding linepath_def by (simp add: inner_left_distrib)
  have t2:"(1-t2)*(a \<bullet> c) + t2 * (b \<bullet> c) = d"
    using \<open>t2\<in>?S\<close> unfolding linepath_def by (simp add: inner_left_distrib)
  have "a \<bullet> c = d"
  proof -
    have "t2*((1-t1)*(a \<bullet> c) + t1 * (b \<bullet> c)) = t2*d" using t1 by auto
    then have *:"(t2-t1*t2)*(a \<bullet> c) + t1*t2 * (b \<bullet> c) = t2*d" by (auto simp add:algebra_simps)
    have "t1*((1-t2)*(a \<bullet> c) + t2 * (b \<bullet> c)) = t1*d" using t2 by auto
    then have **:"(t1-t1*t2)*(a \<bullet> c) + t1*t2 * (b \<bullet> c) = t1*d" by (auto simp add:algebra_simps)
    have "(t2-t1)*(a \<bullet> c) = (t2-t1)*d" using arg_cong2[OF * **,of minus]
      by (auto simp add:algebra_simps)
    then show ?thesis using \<open>t1\<noteq>t2\<close> by auto
  qed
  moreover have "b \<bullet> c = d"
  proof -
    have "(1-t2)*((1-t1)*(a \<bullet> c) + t1 * (b \<bullet> c)) = (1-t2)*d" using t1 by auto
    then have *:"(1-t1)*(1-t2)*(a \<bullet> c) + (t1-t1*t2) * (b \<bullet> c) = (1-t2)*d" by (auto simp add:algebra_simps)
    have "(1-t1)*((1-t2)*(a \<bullet> c) + t2 * (b \<bullet> c)) = (1-t1)*d" using t2 by auto
    then have **:"(1-t1)*(1-t2)*(a \<bullet> c) + (t2-t1*t2) * (b \<bullet> c) = (1-t1)*d" by (auto simp add:algebra_simps)
    have "(t2-t1)*(b \<bullet> c) = (t2-t1)*d" using arg_cong2[OF ** *,of minus]
      by (auto simp add:algebra_simps)
    then show ?thesis using \<open>t1\<noteq>t2\<close> by auto
  qed
  ultimately show False using assms by auto  
qed
  
lemma finite_half_joinpaths_inter:
  assumes "finite {t. l1 t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}" "finite {t. l2 t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}"
  shows "finite {t. (l1+++l2) t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}"
proof -
  let ?l1s = "{t. l1 (2*t) \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1/2}"
  let ?l2s = "{t. l2 (2 * t - 1) \<bullet> c = d \<and> 1/2< t \<and> t\<le>1}"
  let ?ls = "\<lambda>l. {t. l t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1}"
  have "{t. (l1+++l2) t \<bullet> c = d \<and> 0\<le> t \<and> t\<le>1} = ?l1s \<union> ?l2s"
    unfolding joinpaths_def by auto
  moreover have "finite ?l1s"
  proof -
    have "?l1s = ((*) (1/2)) ` ?ls l1" by (auto intro:rev_image_eqI)
    thus ?thesis using assms by simp 
  qed
  moreover have "finite ?l2s"
  proof -
    have "?l2s \<subseteq> (\<lambda>x. x/2 + 1/2) ` ?ls l2" by (auto intro:rev_image_eqI simp add:field_simps)
    thus ?thesis using assms 
      by (auto elim:finite_subset)
  qed
  ultimately show ?thesis by simp
qed  
  
lemma finite_ReZ_segments_linepath:
  "finite_ReZ_segments (linepath a b) z"
proof -
  have ?thesis when "Re a\<noteq>Re z \<or> Re b \<noteq>Re z"
  proof -
    let ?S1="{t. Re (linepath a b t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
    have "finite ?S1" 
      using linepath_half_finite_inter[of a "Complex 1 0" "Re z" b] that 
      using one_complex.code by auto
    from finite_imp_finite_ReZ_segments[OF this] show ?thesis .
  qed
  moreover have ?thesis when "Re a=Re z" "Re b=Re z"
    unfolding finite_ReZ_segments_def
    apply (rule finite_Psegments.intros(2)[of 0])
    using that unfolding linepath_def by (auto simp add:algebra_simps intro:finite_Psegments.intros)
  ultimately show ?thesis by blast
qed
  
lemma finite_ReZ_segments_part_circlepath:
  "finite_ReZ_segments (part_circlepath z0 r st tt) z"
proof -
  have ?thesis when "st \<noteq> tt" "r \<noteq> 0"
  proof -
    let ?S1="{t. Re (part_circlepath z0 r st tt t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"  
    have "finite ?S1"
      using part_circlepath_half_finite_inter[of st tt r "Complex 1 0" z0 "Re z"] that one_complex.code
      by (auto simp add:inner_complex_def )
    from finite_imp_finite_ReZ_segments[OF this] show ?thesis .
  qed
  moreover have ?thesis when "st =tt \<or> r=0"
  proof -
    define c where "c = z0 + r * exp (\<i> *  tt)"
    have "part_circlepath z0 r st tt = (\<lambda>t. c)"
      unfolding part_circlepath_def c_def using that linepath_refl by auto
    then show ?thesis 
      using finite_ReZ_segments_linepath[of c c z] linepath_refl[of c]
      by auto
  qed
  ultimately show ?thesis by blast
qed
   
lemma finite_ReZ_segments_poly_of_real:
  shows "finite_ReZ_segments (poly p o of_real) z" 
  using finite_ReZ_segments_poly_linepath[of p 0 1 z] unfolding linepath_def
  by (auto simp add:scaleR_conv_of_real)
 
lemma finite_ReZ_segments_subpath:
  assumes "finite_ReZ_segments g z"
    "0\<le>u" "u\<le>v" "v\<le>1"
  shows "finite_ReZ_segments (subpath u v g) z" 
proof (cases "u=v")
  case True  
  then show ?thesis 
    unfolding subpath_def by (auto intro:finite_ReZ_segments_constI)
next
  case False
  then have "u<v" using \<open>u\<le>v\<close> by auto
  define P where "P=(\<lambda>t. Re (g t - z) = 0)"
  have "finite_ReZ_segments (subpath u v g) z 
      = finite_Psegments (P o (\<lambda>t. (v - u) * t + u)) 0 1"
    unfolding finite_ReZ_segments_def subpath_def P_def comp_def by auto
  also have "..."
    apply (rule finite_Psegments_pos_linear)
    using assms False unfolding finite_ReZ_segments_def
    by (fold P_def,auto elim:finite_Psegments_included)        
  finally show ?thesis .
qed   
  
subsection \<open>jump and jumpF\<close> 
  
definition jump::"(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> int" where
  "jump f a = (if 
        (LIM x (at_left a). f x :> at_bot) \<and> (LIM x (at_right a). f x :> at_top) 
      then 1 else if 
        (LIM x (at_left a). f x :> at_top) \<and> (LIM x (at_right a). f x :> at_bot) 
      then -1 else 0)"
  
definition jumpF::"(real \<Rightarrow> real) \<Rightarrow> real filter \<Rightarrow> real" where 
  "jumpF f F \<equiv> (if filterlim f at_top F then 1/2 else 
    if filterlim f at_bot F then -1/2 else (0::real))"
   
lemma jumpF_const[simp]:
  assumes "F\<noteq>bot"
  shows "jumpF (\<lambda>_. c) F = 0" 
proof -
  have False when "LIM x F. c :> at_bot"
    using filterlim_at_bot_nhds[OF that _ \<open>F\<noteq>bot\<close>] by auto
  moreover have False when "LIM x F. c :> at_top"
    using filterlim_at_top_nhds[OF that _ \<open>F\<noteq>bot\<close>] by auto
  ultimately show ?thesis unfolding jumpF_def by auto
qed

lemma jumpF_not_infinity:
  assumes "continuous F g" "F\<noteq>bot"
  shows "jumpF g F = 0"  
proof -
  have "\<not> filterlim g at_infinity F"
    using not_tendsto_and_filterlim_at_infinity[OF \<open>F \<noteq>bot\<close> assms(1)[unfolded continuous_def]] 
    by auto
  then have "\<not> filterlim g at_bot F" "\<not> filterlim g at_top F"
    using at_bot_le_at_infinity at_top_le_at_infinity filterlim_mono by blast+
  then show ?thesis unfolding jumpF_def by auto
qed
  
lemma jumpF_linear_comp:
  assumes "c\<noteq>0"
  shows 
    "jumpF (f o (\<lambda>x. c*x+b)) (at_left x) = 
            (if c>0 then jumpF f (at_left (c*x+b)) else jumpF f (at_right (c*x+b)))"
    (is ?case1)
    "jumpF (f o (\<lambda>x. c*x+b)) (at_right x) = 
            (if c>0 then jumpF f (at_right (c*x+b)) else jumpF f (at_left (c*x+b)))"
    (is ?case2)
proof -
  let ?g = "\<lambda>x. c*x+b"  
  have ?case1 ?case2 when "\<not> c>0"
  proof -
    have "c<0" using \<open>c\<noteq>0\<close> that by auto
    have "filtermap ?g (at_left x) = at_right (?g x)"
         "filtermap ?g (at_right x) = at_left (?g x)"
      using \<open>c<0\<close> 
      filtermap_linear_at_left[OF \<open>c\<noteq>0\<close>, of b x] 
      filtermap_linear_at_right[OF \<open>c\<noteq>0\<close>, of b x] by auto
    then have 
        "jumpF (f \<circ> ?g) (at_left x) = jumpF f (at_right (?g x))"
        "jumpF (f \<circ> ?g) (at_right x) = jumpF f (at_left (?g x))"
      unfolding jumpF_def filterlim_def comp_def
      by (auto simp add: filtermap_filtermap[of f ?g,symmetric])
    then show ?case1 ?case2 using \<open>c<0\<close> by auto
  qed
  moreover have ?case1 ?case2 when "c>0"
  proof -
    have "filtermap ?g (at_left x) = at_left (?g x)"
         "filtermap ?g (at_right x) = at_right (?g x)"
      using that 
      filtermap_linear_at_left[OF \<open>c\<noteq>0\<close>, of b x] 
      filtermap_linear_at_right[OF \<open>c\<noteq>0\<close>, of b x] by auto
    then have 
        "jumpF (f \<circ> ?g) (at_left x) = jumpF f (at_left (?g x))"
        "jumpF (f \<circ> ?g) (at_right x) = jumpF f (at_right (?g x))"
      unfolding jumpF_def filterlim_def comp_def
      by (auto simp add: filtermap_filtermap[of f ?g,symmetric])
    then show ?case1 ?case2 using that by auto
  qed
  ultimately show ?case1 ?case2 by auto
qed  
  
lemma jump_const[simp]:"jump (\<lambda>_. c) a = 0"
proof -
  have False when "LIM x (at_left a). c :> at_bot"
    apply (rule not_tendsto_and_filterlim_at_infinity[of "at_left a" "\<lambda>_. c" c])
      apply auto
    using at_bot_le_at_infinity filterlim_mono that by blast
  moreover have False when "LIM x (at_left a). c :> at_top"
    apply (rule not_tendsto_and_filterlim_at_infinity[of "at_left a" "\<lambda>_. c" c])
      apply auto
    using at_top_le_at_infinity filterlim_mono that by blast  
  ultimately show ?thesis unfolding jump_def by auto
qed  

lemma jump_not_infinity:
  "isCont f a \<Longrightarrow> jump f a =0"
  by (meson at_bot_le_at_infinity at_top_le_at_infinity filterlim_at_split 
      filterlim_def isCont_def jump_def not_tendsto_and_filterlim_at_infinity 
      order_trans trivial_limit_at_left_real) 
  
lemma jump_jump_poly_aux:
  assumes "p\<noteq>0" "coprime p q"
  shows "jump (\<lambda>x. poly q x / poly p x) a = jump_poly q p a"
proof (cases "q=0")
  case True
  then show ?thesis by auto
next
  case False
  define f where "f \<equiv> (\<lambda>x. poly q x / poly p x)"
  have ?thesis when "poly q a = 0"
  proof -
    have "poly p a\<noteq>0" using coprime_poly_0[OF \<open>coprime p q\<close>] that by blast
    then have "isCont f a" unfolding f_def by simp
    then have "jump f a=0" using jump_not_infinity by auto
    moreover have "jump_poly q p a=0"
      using jump_poly_not_root[OF \<open>poly p a\<noteq>0\<close>] by auto
    ultimately show ?thesis unfolding f_def by auto
  qed
  moreover have ?thesis when "poly q a\<noteq>0"
  proof (cases "even(order a p)")
    case True
    define c where "c\<equiv>sgn (poly q a)"
    note 
      filterlim_divide_at_bot_at_top_iff
        [OF _ that,of "poly q"  "at_left a" "poly p",folded f_def c_def,simplified]
      filterlim_divide_at_bot_at_top_iff
        [OF _ that,of "poly q"  "at_right a" "poly p",folded f_def c_def,simplified]
    moreover have "(poly p has_sgnx - c) (at_left a) = (poly p has_sgnx - c) (at_right a)"
         "(poly p has_sgnx c) (at_left a) = (poly p has_sgnx c) (at_right a)"
      using poly_has_sgnx_left_right[OF \<open>p\<noteq>0\<close>] True by auto
    moreover have "c\<noteq>0" by (simp add: c_def sgn_if that)
    then have False when 
        "(poly p has_sgnx - c) (at_right a)" 
        "(poly p has_sgnx c) (at_right a)"
      using has_sgnx_unique[OF _ that] by auto
    ultimately have "jump f a = 0"
      unfolding jump_def by auto
    moreover have "jump_poly q p a = 0" unfolding jump_poly_def
      using True by (simp add: order_0I that)
    ultimately show ?thesis unfolding f_def by auto
  next
    case False
    define c where "c\<equiv>sgn (poly q a)"
    have "(poly p \<longlongrightarrow> 0) (at a)" using False 
      by (metis even_zero order_0I poly_tendsto(1))
    then have "(poly p \<longlongrightarrow> 0) (at_left a)" and "(poly p \<longlongrightarrow> 0) (at_right a)"
      by (auto simp add: filterlim_at_split)
    moreover note 
      filterlim_divide_at_bot_at_top_iff
        [OF _ that,of "poly q" _ "poly p",folded f_def c_def]
    moreover have "(poly p has_sgnx c) (at_left a) = (poly p has_sgnx - c) (at_right a)"
         "(poly p has_sgnx - c) (at_left a) = (poly p has_sgnx c) (at_right a)"
      using poly_has_sgnx_left_right[OF \<open>p\<noteq>0\<close>] False by auto
    ultimately have "jump f a = (if (poly p has_sgnx c) (at_right a) then 1
        else if (poly p has_sgnx - c) (at_right a) then -1 else 0)"
      unfolding jump_def by auto
    also have "... = (if sign_r_pos (q * p) a then 1 else - 1)"
    proof -
      have "(poly p has_sgnx c) (at_right a) \<longleftrightarrow>  sign_r_pos (q * p) a " 
      proof 
        assume "(poly p has_sgnx c) (at_right a)"
        then have "sgnx (poly p) (at_right a) = c" by auto
        moreover have "sgnx (poly q) (at_right a) = c"
          unfolding c_def using that by (auto intro!: tendsto_nonzero_sgnx)
        ultimately have "sgnx (\<lambda>x. poly (q*p) x) (at_right a) = c * c"
          by (simp add:sgnx_times)
        moreover have "c\<noteq>0" by (simp add: c_def sgn_if that) 
        ultimately have "sgnx (\<lambda>x. poly (q*p) x) (at_right a) > 0"
          using not_real_square_gt_zero by fastforce
        then show "sign_r_pos (q * p) a" using sign_r_pos_sgnx_iff 
          by blast
      next
        assume asm:"sign_r_pos (q * p) a"
        let ?c1 = "sgnx (poly p) (at_right a)"
        let ?c2 = "sgnx (poly q) (at_right a)"
        have "0 < sgnx (\<lambda>x. poly (q * p) x) (at_right a)"
          using asm sign_r_pos_sgnx_iff by blast
        then have "?c2 * ?c1 >0" 
          apply (subst (asm) poly_mult)
          apply (subst (asm) sgnx_times)
          by auto
        then have "?c2>0 \<and> ?c1>0 \<or> ?c2<0 \<and> ?c1<0"
          by (simp add: zero_less_mult_iff)
        then have "?c1=?c2"
          using sgnx_values[OF sgnx_able_poly(1), of a,simplified]
          by (metis add.inverse_neutral less_minus_iff less_not_sym)    
        moreover have "sgnx (poly q) (at_right a) = c"
          unfolding c_def using that by (auto intro!: tendsto_nonzero_sgnx)
        ultimately have "?c1 = c" by auto
        then show "(poly p has_sgnx c) (at_right a)"
          using sgnx_able_poly(1) sgnx_able_sgnx by blast
      qed  
      then show ?thesis 
        unfolding jump_poly_def using poly_has_sgnx_values[OF \<open>p\<noteq>0\<close>]
        by (metis add.inverse_inverse c_def sgn_if that)
    qed
    also have "... = jump_poly q p a"
      unfolding jump_poly_def using False order_root that by (simp add: order_root assms(1))
    finally show ?thesis unfolding f_def by auto
  qed
  ultimately show ?thesis by auto
qed
 
lemma jump_jumpF:
  assumes cont:"isCont (inverse o f) a" and 
      sgnxl:"(f has_sgnx l) (at_left a)" and sgnxr:"(f has_sgnx r) (at_right a)" and
      "l\<noteq>0 " "r\<noteq>0"
  shows "jump f a = jumpF f (at_right a) - jumpF f (at_left a)"
proof -
  have ?thesis when "filterlim f at_bot (at_left a)" "filterlim f at_top (at_right a)"
    unfolding jump_def jumpF_def 
    using that filterlim_at_top_at_bot[OF _ _ trivial_limit_at_left_real]
    by auto
  moreover have ?thesis when "filterlim f at_top (at_left a)" "filterlim f at_bot (at_right a)"
    unfolding jump_def jumpF_def 
    using that filterlim_at_top_at_bot[OF _ _ trivial_limit_at_right_real]
    by auto
  moreover have ?thesis when 
          "\<not> filterlim f at_bot (at_left a) \<or> \<not> filterlim f at_top (at_right a)"
          "\<not> filterlim f at_top (at_left a) \<or> \<not> filterlim f at_bot (at_right a)"
  proof (cases "f a=0")
    case False
    have "jumpF f (at_right a) = 0" "jumpF f (at_left a) = 0"
    proof -
      have "isCont (inverse o inverse o f) a" using cont False unfolding comp_def
        by (rule_tac continuous_at_within_inverse, auto)
      then have "isCont f a" unfolding comp_def by auto
      then have "(f \<longlongrightarrow> f a) (at_right a)" "(f \<longlongrightarrow> f a) (at_left a)"
        unfolding continuous_at_split by (auto simp add:continuous_within)
      moreover note trivial_limit_at_left_real trivial_limit_at_right_real
      ultimately show "jumpF f (at_right a) = 0" "jumpF f (at_left a) = 0"
        unfolding jumpF_def using filterlim_at_bot_nhds filterlim_at_top_nhds
        by metis+
    qed
    then show ?thesis unfolding jump_def using that by auto
  next
    case True
    then have tends0:"((\<lambda>x. inverse (f x)) \<longlongrightarrow> 0) (at a)" 
      using cont unfolding isCont_def comp_def by auto
    have "jump f a = 0" using that unfolding jump_def by auto
    have r_lim:"if r>0 then filterlim f at_top (at_right a) else filterlim f at_bot (at_right a)"
    proof (cases "r>0")
      case True 
      then have "\<forall>\<^sub>F x in (at_right a). 0 < f x" 
          using sgnxr unfolding has_sgnx_def
          by (auto elim:eventually_mono)
      then have "filterlim f at_top (at_right a)" 
        using filterlim_inverse_at_top[of "\<lambda>x. inverse (f x)", simplified] tends0
        unfolding filterlim_at_split by auto
      then show ?thesis using True by presburger
    next
      case False
      then have "\<forall>\<^sub>F x in (at_right a). 0 > f x" 
        using sgnxr \<open>r\<noteq>0\<close> False unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (meson linorder_neqE_linordered_idom sgn_less)
      then have "filterlim f at_bot (at_right a)" 
        using filterlim_inverse_at_bot[of "\<lambda>x. inverse (f x)", simplified] tends0
        unfolding filterlim_at_split by auto
      then show ?thesis using False by simp
    qed
    have l_lim:"if l>0 then filterlim f at_top (at_left a) else filterlim f at_bot (at_left a)"
    proof (cases "l>0")
      case True 
      then have "\<forall>\<^sub>F x in (at_left a). 0 < f x" 
          using sgnxl unfolding has_sgnx_def
          by (auto elim:eventually_mono)
      then have "filterlim f at_top (at_left a)" 
        using filterlim_inverse_at_top[of "\<lambda>x. inverse (f x)", simplified] tends0
        unfolding filterlim_at_split by auto
      then show ?thesis using True by presburger
    next
      case False
      then have "\<forall>\<^sub>F x in (at_left a). 0 > f x" 
        using sgnxl \<open>l\<noteq>0\<close> False unfolding has_sgnx_def
        apply (elim eventually_mono)
        by (meson linorder_neqE_linordered_idom sgn_less)
      then have "filterlim f at_bot (at_left a)" 
        using filterlim_inverse_at_bot[of "\<lambda>x. inverse (f x)", simplified] tends0
        unfolding filterlim_at_split by auto
      then show ?thesis using False by simp
    qed
      
    have ?thesis when "l>0" "r>0"
      using that l_lim r_lim \<open>jump f a=0\<close> unfolding jumpF_def by auto
    moreover have ?thesis when "\<not> l>0" "\<not> r>0"
    proof -
      have "filterlim f at_bot (at_right a)" "filterlim f at_bot (at_left a)" 
        using r_lim l_lim that by auto
      moreover then have "\<not> filterlim f at_top (at_right a)" "\<not> filterlim f at_top (at_left a)"
        by (auto elim: filterlim_at_top_at_bot)
      ultimately have "jumpF f (at_right a) = -1/2 "  "jumpF f (at_left a) = -1/2"
        unfolding jumpF_def by auto
      then show ?thesis using \<open>jump f a=0\<close> by auto
    qed
    moreover have ?thesis when "l>0" "\<not> r>0"
    proof -
      note \<open>\<not> filterlim f at_top (at_left a) \<or> \<not> filterlim f at_bot (at_right a)\<close>
      moreover have "filterlim f at_bot (at_right a)" "filterlim f at_top (at_left a)" 
        using r_lim l_lim that by auto
      ultimately have False by auto
      then show ?thesis by auto
    qed
    moreover have ?thesis when "\<not> l>0" "r>0"
    proof -
      note \<open>\<not> filterlim f at_bot (at_left a) \<or> \<not> filterlim f at_top (at_right a)\<close>
      moreover have "filterlim f at_bot (at_left a)" "filterlim f at_top (at_right a)" 
        using r_lim l_lim that by auto
      ultimately have False by auto
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed
  
lemma jump_linear_comp:
  assumes "c\<noteq>0"
  shows "jump (f o (\<lambda>x. c*x+b)) x = (if c>0 then jump f (c*x+b) else -jump f (c*x+b))"
proof (cases "c>0")
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  let ?g = "\<lambda>x. c*x+b"  
  have "filtermap ?g (at_left x) = at_right (?g x)"
       "filtermap ?g (at_right x) = at_left (?g x)"
    using \<open>c<0\<close> 
      filtermap_linear_at_left[OF \<open>c\<noteq>0\<close>, of b x] 
      filtermap_linear_at_right[OF \<open>c\<noteq>0\<close>, of b x] by auto
  then have "jump (f \<circ> ?g) x = - jump f (c * x + b)"
    unfolding jump_def filterlim_def comp_def
    apply (auto simp add: filtermap_filtermap[of f ?g,symmetric])
    apply (fold filterlim_def)
    by (auto elim:filterlim_at_top_at_bot)
  then show ?thesis using \<open>c<0\<close> by auto
next
  case True
  let ?g = "\<lambda>x. c*x+b"  
  have "filtermap ?g (at_left x) = at_left (?g x)"
       "filtermap ?g (at_right x) = at_right (?g x)"
    using True 
      filtermap_linear_at_left[OF \<open>c\<noteq>0\<close>, of b x] 
      filtermap_linear_at_right[OF \<open>c\<noteq>0\<close>, of b x] by auto
  then have "jump (f \<circ> ?g) x = jump f (c * x + b)"
    unfolding jump_def filterlim_def comp_def
    by (auto simp add: filtermap_filtermap[of f ?g,symmetric])
  then show ?thesis using True by auto
qed 
  
lemma jump_divide_derivative:
  assumes "isCont f x" "g x = 0" "f x\<noteq>0" 
    and g_deriv:"(g has_field_derivative c) (at x)" and "c\<noteq>0"
  shows "jump (\<lambda>t. f t/g t) x = (if sgn c = sgn ( f x) then 1 else -1)"  
proof -
  have g_tendsto:"(g \<longlongrightarrow> 0) (at_left x)" "(g \<longlongrightarrow> 0) (at_right x)"
    by (metis DERIV_isCont Lim_at_imp_Lim_at_within assms(2) assms(4) continuous_at)+
  have f_tendsto:"(f \<longlongrightarrow> f x) (at_left x)" "(f \<longlongrightarrow> f x) (at_right x)"
    using Lim_at_imp_Lim_at_within assms(1) continuous_at by blast+
  
  have ?thesis when "c>0" "f x>0"  
  proof -    
    have "(g has_sgnx - sgn (f x)) (at_left x)" 
      using has_sgnx_derivative_at_left[OF g_deriv \<open>g x=0\<close>] that by auto
    moreover have "(g has_sgnx sgn (f x)) (at_right x)" 
      using has_sgnx_derivative_at_right[OF g_deriv \<open>g x=0\<close>] that by auto
    ultimately have "(LIM t at_left x. f t / g t :> at_bot) \<and> (LIM t at_right x. f t / g t :> at_top)"
      using filterlim_divide_at_bot_at_top_iff[OF _ \<open>f x\<noteq>0\<close>, of f] 
      using f_tendsto(1) f_tendsto(2) g_tendsto(1) g_tendsto(2) by blast
    moreover have "sgn c = sgn (f x)" using that by auto
    ultimately show ?thesis unfolding jump_def by auto
  qed
  moreover have ?thesis when "c>0" "f x<0"  
  proof -    
    have "(g has_sgnx sgn (f x)) (at_left x)" 
      using has_sgnx_derivative_at_left[OF g_deriv \<open>g x=0\<close>] that by auto
    moreover have "(g has_sgnx - sgn (f x)) (at_right x)" 
      using has_sgnx_derivative_at_right[OF g_deriv \<open>g x=0\<close>] that by auto
    ultimately have "(LIM t at_left x. f t / g t :> at_top) \<and> (LIM t at_right x. f t / g t :> at_bot)"
      using filterlim_divide_at_bot_at_top_iff[OF _ \<open>f x\<noteq>0\<close>, of f] 
      using f_tendsto(1) f_tendsto(2) g_tendsto(1) g_tendsto(2) by blast
    moreover from this have "\<not> (LIM t at_left x. f t / g t :> at_bot)"
      using filterlim_at_top_at_bot by fastforce
    moreover have "sgn c \<noteq> sgn (f x)" using that by auto
    ultimately show ?thesis unfolding jump_def by auto
  qed
  moreover have ?thesis when "c<0" "f x>0"  
  proof -    
    have "(g has_sgnx sgn (f x)) (at_left x)" 
      using has_sgnx_derivative_at_left[OF g_deriv \<open>g x=0\<close>] that by auto
    moreover have "(g has_sgnx - sgn (f x)) (at_right x)" 
      using has_sgnx_derivative_at_right[OF g_deriv \<open>g x=0\<close>] that by auto
    ultimately have "(LIM t at_left x. f t / g t :> at_top) \<and> (LIM t at_right x. f t / g t :> at_bot)"
      using filterlim_divide_at_bot_at_top_iff[OF _ \<open>f x\<noteq>0\<close>, of f] 
      using f_tendsto(1) f_tendsto(2) g_tendsto(1) g_tendsto(2) by blast
    moreover from this have "\<not> (LIM t at_left x. f t / g t :> at_bot)"
      using filterlim_at_top_at_bot by fastforce
    moreover have "sgn c \<noteq> sgn (f x)" using that by auto
    ultimately show ?thesis unfolding jump_def by auto
  qed
  moreover have ?thesis when "c<0" "f x<0"  
  proof -    
    have "(g has_sgnx - sgn (f x)) (at_left x)" 
      using has_sgnx_derivative_at_left[OF g_deriv \<open>g x=0\<close>] that by auto
    moreover have "(g has_sgnx sgn (f x)) (at_right x)" 
      using has_sgnx_derivative_at_right[OF g_deriv \<open>g x=0\<close>] that by auto
    ultimately have "(LIM t at_left x. f t / g t :> at_bot) \<and> (LIM t at_right x. f t / g t :> at_top)"
      using filterlim_divide_at_bot_at_top_iff[OF _ \<open>f x\<noteq>0\<close>, of f] 
      using f_tendsto(1) f_tendsto(2) g_tendsto(1) g_tendsto(2) by blast
    moreover have "sgn c =sgn (f x)" using that by auto
    ultimately show ?thesis unfolding jump_def by auto
  qed
  ultimately show ?thesis using \<open>c\<noteq>0\<close> \<open>f x\<noteq>0\<close> by argo   
qed
    
lemma jump_jump_poly: "jump (\<lambda>x. poly q x / poly p x) a = jump_poly q p a"
proof (cases "p=0")
  case True
  then show ?thesis by auto
next
  case False
  obtain p' q' where p':"p= p'*gcd p q" and q':"q=q'*gcd p q" 
    using gcd_dvd1 gcd_dvd2 dvd_def[of "gcd p q", simplified mult.commute]  by metis
  then have "coprime p' q'" "p'\<noteq>0" "gcd p q\<noteq>0" using gcd_coprime \<open>p\<noteq>0\<close>  by auto
  
  define f where "f \<equiv> (\<lambda>x. poly q' x / poly p' x)"
  define g where "g \<equiv> (\<lambda>x. if poly (gcd p q) x = 0 then 0::real else 1)"
  
  have g_tendsto:"(g \<longlongrightarrow> 1) (at_left a)" "(g \<longlongrightarrow> 1) (at_right a)"
  proof -
    have
      "(poly (gcd p q) has_sgnx 1) (at_left a) 
          \<or> (poly (gcd p q) has_sgnx - 1) (at_left a)"
      "(poly (gcd p q) has_sgnx 1) (at_right a) 
          \<or> (poly (gcd p q) has_sgnx - 1) (at_right a)"
      using \<open>p\<noteq>0\<close> poly_has_sgnx_values by auto
    then have " \<forall>\<^sub>F x in at_left a. g x = 1" " \<forall>\<^sub>F x in at_right a. g x = 1"
      unfolding has_sgnx_def g_def by (auto elim:eventually_mono)
    then show "(g \<longlongrightarrow> 1) (at_left a)" "(g \<longlongrightarrow> 1) (at_right a)"
      using tendsto_eventually by auto
  qed
    
  have "poly q x / poly p x = g x * f x" for x
    unfolding f_def g_def by (subst p',subst q',auto)
  then have "jump (\<lambda>x. poly q x / poly p x) a = jump (\<lambda>x. g x * f x) a"
    by auto
  also have "... = jump f a"
    unfolding jump_def
    apply (subst (1 2) filterlim_tendsto_pos_mult_at_top_iff)
        prefer 5
        apply (subst (1 2) filterlim_tendsto_pos_mult_at_bot_iff)
    using g_tendsto by auto
  also have "... = jump_poly q' p' a"
    using jump_jump_poly_aux[OF \<open>p'\<noteq>0\<close> \<open>coprime p' q'\<close>] unfolding f_def by auto
  also have "... = jump_poly q p a"
    using jump_poly_mult[OF \<open>gcd p q \<noteq> 0\<close>, of q'] p' q'
    by (metis mult.commute)
  finally show ?thesis .
qed  
  
 
lemma jump_Im_divide_Re_0:
  assumes "path g" "Re (g x)\<noteq>0" "0<x" "x<1"
  shows "jump (\<lambda>t. Im (g t) / Re (g t)) x = 0"  
proof -
  have "isCont g x"
    using \<open>path g\<close>[unfolded path_def] \<open>0<x\<close> \<open>x<1\<close>
    apply (elim continuous_on_interior)
    by auto
  then have "isCont (\<lambda>t. Im(g t)/Re(g t)) x" using \<open>Re (g x)\<noteq>0\<close>  
    by (auto intro:continuous_intros isCont_Re isCont_Im)
  then show "jump (\<lambda>t. Im(g t)/Re(g t)) x=0"
    using jump_not_infinity by auto 
qed 
  
lemma jumpF_im_divide_Re_0:
  assumes "path g" "Re (g x)\<noteq>0" 
  shows "\<lbrakk>0\<le>x;x<1\<rbrakk> \<Longrightarrow> jumpF (\<lambda>t. Im (g t) / Re (g t)) (at_right x) = 0"
        "\<lbrakk>0<x;x\<le>1\<rbrakk> \<Longrightarrow> jumpF (\<lambda>t. Im (g t) / Re (g t)) (at_left x) = 0"
proof -
  define g' where "g' = (\<lambda>t. Im (g t) / Re (g t))"

  show "jumpF g' (at_right x) = 0" when "0\<le>x" "x<1"
  proof -
    have "(g' \<longlongrightarrow> g' x) (at_right x)"
    proof (cases "x=0")
      case True
      have "continuous (at_right 0) g" 
        using \<open>path g\<close> unfolding path_def 
        by (auto elim:continuous_on_at_right)
      then have "continuous (at_right x) (\<lambda>t. Im(g t))" "continuous (at_right x) (\<lambda>t. Re(g t))"
        using continuous_Im continuous_Re True by auto
      moreover have "Re (g (netlimit (at_right x))) \<noteq> 0" 
        using assms(2) by (simp add: Lim_ident_at)
      ultimately have "continuous (at_right x) (\<lambda>t. Im (g t)/Re(g t))"  
        by (auto intro:continuous_divide)
      then show ?thesis unfolding g'_def continuous_def 
        by (simp add: Lim_ident_at)
    next
      case False
      have "isCont (\<lambda>x. Im (g x)) x" "isCont (\<lambda>x. Re (g x)) x" 
        using \<open>path g\<close> unfolding path_def
        by (metis False atLeastAtMost_iff at_within_Icc_at continuous_Im continuous_Re
          continuous_on_eq_continuous_within less_le that)+      
      then have "isCont g' x" 
        using assms(2) unfolding g'_def
        by (auto intro:continuous_intros)
      then show ?thesis unfolding isCont_def using filterlim_at_split by blast
    qed
    then have "\<not> filterlim g' at_top (at_right x)" "\<not> filterlim g' at_bot (at_right x)"
      using filterlim_at_top_nhds[of g' "at_right x"] filterlim_at_bot_nhds[of g' "at_right x"]
      by auto
    then show ?thesis unfolding jumpF_def by auto
  qed
    
  show "jumpF g' (at_left x) = 0" when "0<x" "x\<le>1"
  proof -
    have "(g' \<longlongrightarrow> g' x) (at_left x)"
    proof (cases "x=1")
      case True
      have "continuous (at_left 1) g" 
        using \<open>path g\<close> unfolding path_def 
        by (auto elim:continuous_on_at_left)
      then have "continuous (at_left x) (\<lambda>t. Im(g t))" "continuous (at_left x) (\<lambda>t. Re(g t))"
        using continuous_Im continuous_Re True by auto
      moreover have "Re (g (netlimit (at_left x))) \<noteq> 0" 
        using assms(2) by (simp add: Lim_ident_at)
      ultimately have "continuous (at_left x) (\<lambda>t. Im (g t)/Re(g t))"  
        by (auto intro:continuous_divide)
      then show ?thesis unfolding g'_def continuous_def 
        by (simp add: Lim_ident_at)
    next
      case False
      have "isCont (\<lambda>x. Im (g x)) x" "isCont (\<lambda>x. Re (g x)) x" 
        using \<open>path g\<close> unfolding path_def
        by (metis False atLeastAtMost_iff at_within_Icc_at continuous_Im continuous_Re
          continuous_on_eq_continuous_within less_le that)+      
      then have "isCont g' x" 
        using assms(2) unfolding g'_def
        by (auto)
      then show ?thesis unfolding isCont_def using filterlim_at_split by blast
    qed
    then have "\<not> filterlim g' at_top (at_left x)" "\<not> filterlim g' at_bot (at_left x)"
      using filterlim_at_top_nhds[of g' "at_left x"] filterlim_at_bot_nhds[of g' "at_left x"]
      by auto
    then show ?thesis unfolding jumpF_def by auto
  qed 
qed
  
lemma jump_cong:
  assumes "x=y" and "eventually (\<lambda>x. f x=g x) (at x)"
  shows "jump f x = jump g y"
proof -
  have left:"eventually (\<lambda>x. f x=g x) (at_left x)" 
    and right:"eventually (\<lambda>x. f x=g x) (at_right x)"
    using assms(2) eventually_at_split by blast+
  from filterlim_cong[OF _ _ this(1)] filterlim_cong[OF _ _ this(2)] 
  show ?thesis unfolding jump_def using assms(1) by fastforce
qed 
    
lemma jumpF_cong:
  assumes "F=G" and "eventually (\<lambda>x. f x=g x) F"
  shows "jumpF f F = jumpF g G"
proof -
  have "\<forall>\<^sub>F r in G. f r = g r"
    using assms(1) assms(2) by force
  then show ?thesis
    by (simp add: assms(1) filterlim_cong jumpF_def)
qed
  
lemma jump_at_left_at_right_eq:
  assumes "isCont f x" and "f x \<noteq> 0" and sgnx_eq:"sgnx g (at_left x) = sgnx g (at_right x)"
  shows "jump (\<lambda>t. f t/g t) x = 0"  
proof -
  define c where "c = sgn (f x)"
  then have "c\<noteq>0" using \<open>f x\<noteq>0\<close> by (simp add: sgn_zero_iff)
  have f_tendsto:"(f \<longlongrightarrow> f x) (at_left x)" " (f \<longlongrightarrow> f x) (at_right x)"
    using \<open>isCont f x\<close> Lim_at_imp_Lim_at_within isCont_def by blast+
  have False when "(g has_sgnx - c) (at_left x)" "(g has_sgnx c) (at_right x)" 
  proof -
    have "sgnx g (at_left x) = -c" using that(1) by auto
    moreover have "sgnx g (at_right x) = c" using that(2) by auto
    ultimately show False using sgnx_eq \<open>c\<noteq>0\<close> by force
  qed
  moreover have False when "(g has_sgnx c) (at_left x)" "(g has_sgnx - c) (at_right x)" 
  proof -
    have "sgnx g (at_left x) = c" using that(1) by auto
    moreover have "sgnx g (at_right x) = - c" using that(2) by auto
    ultimately show False using sgnx_eq \<open>c\<noteq>0\<close> by force
  qed  
  ultimately show ?thesis
    unfolding jump_def
    by (auto simp add:f_tendsto filterlim_divide_at_bot_at_top_iff[OF _ \<open>f x \<noteq> 0\<close>] c_def)  
qed  
  
lemma jumpF_pos_has_sgnx:
  assumes "jumpF f F > 0"
  shows "(f has_sgnx 1) F"
proof -
  have "filterlim f at_top F" using assms unfolding jumpF_def by argo
  then have "eventually (\<lambda>x. f x>0) F" using filterlim_at_top_dense[of f F] by blast
  then show ?thesis unfolding has_sgnx_def 
    apply (elim eventually_mono)
    by auto
qed  

lemma jumpF_neg_has_sgnx:
  assumes "jumpF f F < 0"
  shows "(f has_sgnx -1) F"
proof -
  have "filterlim f at_bot F" using assms unfolding jumpF_def by argo
  then have "eventually (\<lambda>x. f x<0) F" using filterlim_at_bot_dense[of f F] by blast
  then show ?thesis unfolding has_sgnx_def 
    apply (elim eventually_mono)
    by auto
qed

  
lemma jumpF_IVT:
  fixes f::"real \<Rightarrow> real" and a b::real
  defines "right\<equiv>(\<lambda>(R::real \<Rightarrow> real \<Rightarrow> bool). R (jumpF f (at_right a)) 0 
                      \<or> (continuous (at_right a) f \<and> R (f a) 0))"
    and
          "left\<equiv>(\<lambda>(R::real \<Rightarrow> real \<Rightarrow> bool). R (jumpF f (at_left b)) 0 
                      \<or> (continuous (at_left b) f \<and> R (f b) 0))"
  assumes "a<b" and cont:"continuous_on {a<..<b} f" and
    right_left:"right greater \<and> left less \<or> right less \<and> left greater" 
  shows "\<exists>x. a<x \<and> x<b \<and> f x =0"
proof -
  have ?thesis when "right greater" "left less" 
  proof -
    have "(f has_sgnx 1) (at_right a)"
    proof -
      have ?thesis when "jumpF f (at_right a)>0" using jumpF_pos_has_sgnx[OF that] .
      moreover have ?thesis when "f a > 0" "continuous (at_right a) f"
      proof -
        have "(f \<longlongrightarrow> f a) (at_right a)" using that(2) by (simp add: continuous_within)
        then show ?thesis
          using tendsto_nonzero_has_sgnx[of f "f a" "at_right a"] that by auto
      qed
      ultimately show ?thesis using that(1) unfolding right_def by auto
    qed
    then obtain a' where "a<a'" and a'_def:"\<forall>y. a<y \<and> y < a' \<longrightarrow> f y > 0" 
      unfolding has_sgnx_def eventually_at_right using sgn_1_pos by auto
    have "(f has_sgnx - 1) (at_left b)" 
    proof -
      have ?thesis when "jumpF f (at_left b)<0" using jumpF_neg_has_sgnx[OF that] .
      moreover have ?thesis when "f b < 0" "continuous (at_left b) f" 
      proof -
        have "(f \<longlongrightarrow> f b) (at_left b)" 
          using that(2) by (simp add: continuous_within)
        then show ?thesis
          using tendsto_nonzero_has_sgnx[of f "f b" "at_left b"] that by auto
      qed
      ultimately show ?thesis using that(2) unfolding left_def by auto
    qed
    then obtain b' where "b'<b" and b'_def:"\<forall>y. b'<y \<and> y < b \<longrightarrow> f y < 0" 
      unfolding has_sgnx_def eventually_at_left using sgn_1_neg by auto  
    have "a' \<le> b'"
    proof (rule ccontr)
      assume "\<not> a' \<le> b'"
      then have "{a<..<a'} \<inter> {b'<..<b} \<noteq> {}"
        using \<open>a<a'\<close> \<open>b'<b\<close> \<open>a<b\<close> by auto
      then obtain c where "c\<in>{a<..<a'}" "c\<in>{b'<..<b}" by blast
      then have "f c>0" "f c<0"
        using a'_def b'_def by auto
      then show False by auto
    qed
    define a0 where "a0=(a+a')/2"
    define b0 where "b0=(b+b')/2"
    have [simp]:"a<a0" "a0<a'" "a0<b0" "b'<b0" "b0<b" 
      unfolding a0_def b0_def using \<open>a<a'\<close> \<open>b'<b\<close> \<open>a'\<le>b'\<close> by auto   
    have "f a0>0" "f b0<0" using a'_def[rule_format,of a0] b'_def[rule_format,of b0] by auto
    moreover have "continuous_on {a0..b0} f"
      using cont \<open>a < a0\<close> \<open>b0 < b\<close>
      by (meson atLeastAtMost_subseteq_greaterThanLessThan_iff continuous_on_subset)
    ultimately have "\<exists>x>a0. x < b0 \<and> f x = 0"
      using IVT_strict[of 0 f a0 b0] by auto
    then show ?thesis using \<open>a < a0\<close> \<open>b0 < b\<close> 
      by (meson lessThan_strict_subset_iff psubsetE subset_psubset_trans)
  qed
  moreover have ?thesis when "right less" "left greater" 
  proof -
    have "(f has_sgnx -1) (at_right a)"
    proof -
      have ?thesis when "jumpF f (at_right a)<0" using jumpF_neg_has_sgnx[OF that] .
      moreover have ?thesis when "f a < 0" "continuous (at_right a) f"
      proof -
        have "(f \<longlongrightarrow> f a) (at_right a)" 
          using that(2) by (simp add: continuous_within)
        then show ?thesis
          using tendsto_nonzero_has_sgnx[of f "f a" "at_right a"] that by auto
      qed
      ultimately show ?thesis using that(1) unfolding right_def by auto
    qed
    then obtain a' where "a<a'" and a'_def:"\<forall>y. a<y \<and> y < a' \<longrightarrow> f y < 0" 
      unfolding has_sgnx_def eventually_at_right using sgn_1_neg by auto
    have "(f has_sgnx  1) (at_left b)" 
    proof -
      have ?thesis when "jumpF f (at_left b)>0" using jumpF_pos_has_sgnx[OF that] .
      moreover have ?thesis when "f b > 0" "continuous (at_left b) f"
      proof -
        have "(f \<longlongrightarrow> f b) (at_left b)" 
          using that(2) by (simp add: continuous_within)
        then show ?thesis
          using tendsto_nonzero_has_sgnx[of f "f b" "at_left b"] that by auto
      qed
      ultimately show ?thesis using that(2) unfolding left_def by auto
    qed
    then obtain b' where "b'<b" and b'_def:"\<forall>y. b'<y \<and> y < b \<longrightarrow> f y > 0" 
      unfolding has_sgnx_def eventually_at_left using sgn_1_pos by auto  
    have "a' \<le> b'"
    proof (rule ccontr)
      assume "\<not> a' \<le> b'"
      then have "{a<..<a'} \<inter> {b'<..<b} \<noteq> {}"
        using \<open>a<a'\<close> \<open>b'<b\<close> \<open>a<b\<close> by auto
      then obtain c where "c\<in>{a<..<a'}" "c\<in>{b'<..<b}" by blast
      then have "f c>0" "f c<0"
        using a'_def b'_def by auto
      then show False by auto
    qed
    define a0 where "a0=(a+a')/2"
    define b0 where "b0=(b+b')/2"
    have [simp]:"a<a0" "a0<a'" "a0<b0" "b'<b0" "b0<b" 
      unfolding a0_def b0_def using \<open>a<a'\<close> \<open>b'<b\<close> \<open>a'\<le>b'\<close> by auto   
    have "f a0<0" "f b0>0" using a'_def[rule_format,of a0] b'_def[rule_format,of b0] by auto
    moreover have "continuous_on {a0..b0} f"
      using cont  \<open>a < a0\<close> \<open>b0 < b\<close> 
      by (meson atLeastAtMost_subseteq_greaterThanLessThan_iff continuous_on_subset)  
    ultimately have "\<exists>x>a0. x < b0 \<and> f x = 0"
      using IVT_strict[of 0 f a0 b0] by auto
    then show ?thesis using \<open>a < a0\<close> \<open>b0 < b\<close> 
      by (meson lessThan_strict_subset_iff psubsetE subset_psubset_trans)
  qed  
  ultimately show ?thesis using right_left by auto
qed
   
lemma jumpF_eventually_const:
  assumes "eventually (\<lambda>x. f x=c) F" "F\<noteq>bot"
  shows "jumpF f F = 0"
proof -
  have "jumpF f F = jumpF (\<lambda>_. c) F"
    apply (rule jumpF_cong)
    using assms(1) by auto
  also have "... = 0" using jumpF_const[OF \<open>F\<noteq>bot\<close>] by simp
  finally show ?thesis .
qed

lemma jumpF_tan_comp:
  "jumpF (f o tan) (at_right x) = (if cos x = 0 
      then jumpF f at_bot else jumpF f (at_right (tan x)))"
  "jumpF (f o tan) (at_left x) = (if cos x =0 
      then jumpF f at_top else jumpF f (at_left (tan x)))"
proof -
  have "filtermap (f \<circ> tan) (at_right x) = 
      (if cos x = 0 then filtermap f at_bot else filtermap f (at_right (tan x)))"
    unfolding comp_def
    apply (subst filtermap_filtermap[of f tan,symmetric])
    using filtermap_tan_at_right_inf filtermap_tan_at_right by auto
  then show "jumpF (f o tan) (at_right x) = (if cos x = 0 
          then jumpF f at_bot else jumpF f (at_right (tan x)))"
    unfolding jumpF_def filterlim_def by auto
next
  have "filtermap (f \<circ> tan) (at_left x) = 
      (if cos x = 0 then filtermap f at_top else filtermap f (at_left (tan x)))"
    unfolding comp_def
    apply (subst filtermap_filtermap[of f tan,symmetric])
    using filtermap_tan_at_left_inf filtermap_tan_at_left by auto
  then show "jumpF (f o tan) (at_left x) = (if cos x = 0 
          then jumpF f at_top else jumpF f (at_left (tan x)))"
    unfolding jumpF_def filterlim_def by auto
qed

subsection \<open>Finite jumpFs over an interval\<close>

definition finite_jumpFs::"(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow>  bool" where
  "finite_jumpFs f a b = finite {x. (jumpF f (at_left x) \<noteq>0 \<or> jumpF f (at_right x) \<noteq>0) \<and> a\<le>x \<and> x\<le>b}" 
  
lemma finite_jumpFs_linear_pos:
  assumes "c>0"
  shows "finite_jumpFs (f o (\<lambda>x. c * x + b)) lb ub \<longleftrightarrow> finite_jumpFs f (c * lb +b) (c * ub + b)" 
proof -
  define left where "left = (\<lambda>f lb ub. {x. jumpF f (at_left x) \<noteq> 0 \<and> lb \<le> x \<and> x \<le> ub})"
  define right where "right = (\<lambda>f lb ub. {x. jumpF f (at_right x) \<noteq> 0 \<and> lb \<le> x \<and> x \<le> ub})"
  define g where "g=(\<lambda>x. c*x+b)"
  define gi where "gi = (\<lambda>x. (x-b)/c)"
  have "finite_jumpFs (f o (\<lambda>x. c * x + b)) lb ub 
      = finite (left (f o g) lb ub \<union> right (f o g) lb ub)"
    unfolding finite_jumpFs_def  
    apply (rule arg_cong[where f=finite]) 
    by (auto simp add:left_def right_def g_def)
  also have "... = finite (gi ` (left f (g lb) (g ub) \<union> right f (g lb) (g ub)))"
  proof -
    have j_rw:
      "jumpF (f o g) (at_left x) = jumpF f (at_left (g x))" 
      "jumpF (f o g) (at_right x) = jumpF f (at_right (g x))"
        for x 
      using jumpF_linear_comp[of c f b x] \<open>c>0\<close> unfolding g_def by auto
    then have 
        "left (f o g) lb ub = gi ` left f (g lb) (g ub)"
        "right (f o g) lb ub = gi ` right f (g lb) (g ub)"
      unfolding left_def right_def gi_def
      using \<open>c>0\<close> by (auto simp add:g_def field_simps) 
    then have "left (f o g) lb ub \<union> right (f o g) lb ub 
        = gi ` (left f (g lb) (g ub) \<union> right f (g lb) (g ub))"
      by auto
    then show ?thesis by auto
  qed
  also have "... = finite (left f (g lb) (g ub) \<union> right f (g lb) (g ub))"
    apply (rule finite_image_iff)
    unfolding gi_def using \<open>c >0\<close>  inj_on_def by fastforce
  also have "... =  finite_jumpFs f (c * lb +b) (c * ub + b)"   
    unfolding finite_jumpFs_def
    apply (rule arg_cong[where f=finite]) 
    by (auto simp add:left_def right_def g_def)
  finally show ?thesis .
qed
  
lemma finite_jumpFs_consts:
  "finite_jumpFs (\<lambda>_ . c) lb ub"
  unfolding finite_jumpFs_def using jumpF_const by auto
    
lemma finite_jumpFs_combine:
  assumes "finite_jumpFs f a b" "finite_jumpFs f b c" 
  shows "finite_jumpFs f a c"
proof -
  define P where "P=(\<lambda>x. jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0)"
  have "{x. P x \<and> a \<le> x \<and> x \<le> c} \<subseteq> {x. P x \<and> a \<le> x \<and> x\<le>b} \<union> {x. P x \<and> b \<le>x \<and> x\<le>c}"
    by auto
  moreover have "finite ({x. P x \<and> a \<le> x \<and> x\<le>b} \<union> {x. P x \<and> b \<le>x \<and> x\<le>c})"
    using assms unfolding finite_jumpFs_def P_def by auto
  ultimately have "finite {x. P x \<and> a \<le> x \<and> x \<le> c}" 
    using finite_subset by auto    
  then show ?thesis unfolding finite_jumpFs_def P_def by auto
qed
    
lemma finite_jumpFs_subE:
  assumes "finite_jumpFs f a b" "a\<le>a'" "b'\<le>b" 
  shows "finite_jumpFs f a' b'"  
using assms unfolding finite_jumpFs_def
  apply (elim rev_finite_subset)
  by auto
   
lemma finite_Psegments_Re_imp_jumpFs:
  assumes "finite_Psegments (\<lambda>t. Re (g t - z) = 0) a b" "continuous_on {a..b} g" 
  shows "finite_jumpFs (\<lambda>t. Im (g t - z)/Re (g t - z)) a b"
    using assms
proof (induct rule:finite_Psegments.induct)
  case (emptyI a b) 
  then show ?case unfolding finite_jumpFs_def 
    by (auto intro:rev_finite_subset[of "{a}"])    
next
  case (insertI_1 s a b)
  define f where "f=(\<lambda>t. Im (g t - z) / Re (g t - z))"
  have "finite_jumpFs f a s" 
  proof -
    have "continuous_on {a..s} g" using \<open>continuous_on {a..b} g\<close> \<open>s \<in> {a..<b}\<close> 
      by (auto elim:continuous_on_subset)
    then show ?thesis using insertI_1 unfolding f_def by auto
  qed
  moreover have "finite_jumpFs f s b" 
  proof -
    have "jumpF f (at_left x) =0" "jumpF f (at_right x) = 0" when "x\<in>{s<..<b}" for x
    proof - 
      show "jumpF f (at_left x) =0"
        apply (rule jumpF_eventually_const[of _ 0])
        unfolding eventually_at_left
         apply (rule exI[where x=s])
        using that insertI_1 unfolding f_def by auto
      show "jumpF f (at_right x) = 0"
        apply (rule jumpF_eventually_const[of _ 0])
        unfolding eventually_at_right
         apply (rule exI[where x=b])
        using that insertI_1 unfolding f_def by auto 
    qed
    then have "{x. (jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0) \<and> s \<le> x \<and> x \<le> b}
          = {x. (jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0) \<and> (x=s \<or> x = b)}"
      using  \<open>s\<in>{a..<b}\<close> by force
    then show ?thesis unfolding finite_jumpFs_def by auto
  qed
  ultimately show ?case using finite_jumpFs_combine[of _ a s b] unfolding f_def by auto
next
  case (insertI_2 s a b)
  define f where "f=(\<lambda>t. Im (g t - z) / Re (g t - z))"
  have "finite_jumpFs f a s" 
  proof -
    have "continuous_on {a..s} g" using \<open>continuous_on {a..b} g\<close> \<open>s \<in> {a..<b}\<close> 
      by (auto elim:continuous_on_subset)
    then show ?thesis using insertI_2 unfolding f_def by auto
  qed
  moreover have "finite_jumpFs f s b" 
  proof -
    have "jumpF f (at_left x) =0" "jumpF f (at_right x) = 0" when "x\<in>{s<..<b}" for x
    proof - 
      have "isCont f x" 
        unfolding f_def
        apply (intro continuous_intros isCont_Im isCont_Re 
            continuous_on_interior[OF \<open>continuous_on {a..b} g\<close>])
        using insertI_2.hyps(1) that 
          apply auto[2]
        using insertI_2.hyps(3) that by blast
      then show "jumpF f (at_left x) =0" "jumpF f (at_right x) = 0"
        by (simp_all add: continuous_at_split jumpF_not_infinity)
    qed
    then have "{x. (jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0) \<and> s \<le> x \<and> x \<le> b}
          = {x. (jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0) \<and> (x=s \<or> x = b)}"
      using  \<open>s\<in>{a..<b}\<close> by force
    then show ?thesis unfolding finite_jumpFs_def by auto
  qed
  ultimately show ?case using finite_jumpFs_combine[of _ a s b] unfolding f_def by auto
qed
  
lemma finite_ReZ_segments_imp_jumpFs:
  assumes "finite_ReZ_segments g z" "path g" 
  shows "finite_jumpFs (\<lambda>t. Im (g t - z)/Re (g t - z)) 0 1"
  using assms unfolding finite_ReZ_segments_def path_def
  by (rule finite_Psegments_Re_imp_jumpFs)      
    
subsection \<open>@{term jumpF} at path ends\<close>  

definition jumpF_pathstart::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> real" where
  "jumpF_pathstart g z= jumpF (\<lambda>t. Im(g t- z)/Re(g t - z)) (at_right 0)"
 
definition jumpF_pathfinish::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> real" where
  "jumpF_pathfinish g z= jumpF (\<lambda>t. Im(g t - z)/Re(g t -z)) (at_left 1)"
  
lemma jumpF_pathstart_eq_0:
  assumes "path g" "Re(pathstart g)\<noteq>Re z"
  shows "jumpF_pathstart g z = 0"
unfolding jumpF_pathstart_def 
  apply (rule jumpF_im_divide_Re_0)
  using assms[unfolded pathstart_def] by auto

lemma jumpF_pathfinish_eq_0:
  assumes "path g" "Re(pathfinish g)\<noteq>Re z"
  shows "jumpF_pathfinish g z = 0"
unfolding jumpF_pathfinish_def 
  apply (rule jumpF_im_divide_Re_0)
  using assms[unfolded pathfinish_def] by auto  
   
lemma 
  shows jumpF_pathfinish_reversepath: "jumpF_pathfinish (reversepath g) z = jumpF_pathstart g z"
    and jumpF_pathstart_reversepath: "jumpF_pathstart (reversepath g) z = jumpF_pathfinish g z"
proof -
  define f where "f=(\<lambda>t. Im (g t - z) / Re (g t - z))"
  define f' where "f'=(\<lambda>t. Im (reversepath g t - z) / Re (reversepath g t - z))"
  have "f o (\<lambda>t. 1 - t) = f'"
    unfolding f_def f'_def comp_def reversepath_def by auto
  then show "jumpF_pathfinish (reversepath g) z = jumpF_pathstart g z" 
        "jumpF_pathstart (reversepath g) z = jumpF_pathfinish g z" 
    unfolding jumpF_pathstart_def jumpF_pathfinish_def
    using jumpF_linear_comp(2)[of "-1" f 1 0,simplified] jumpF_linear_comp(1)[of "-1" f 1 1,simplified]
    apply (fold f_def f'_def)    
    by auto
qed
     
lemma jumpF_pathstart_joinpaths[simp]:
  "jumpF_pathstart (g1+++g2) z = jumpF_pathstart g1 z"
proof -
  let ?h="(\<lambda>t. Im (g1 t - z) / Re (g1 t - z))"
  let ?f="\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)"
  have "jumpF_pathstart g1 z = jumpF ?h (at_right 0)"
    unfolding jumpF_pathstart_def by simp
  also have "... = jumpF (?h o (\<lambda>t. 2*t)) (at_right 0)"
    using jumpF_linear_comp[of 2 ?h 0 0,simplified] by auto
  also have "... = jumpF ?f (at_right 0)"
  proof (rule jumpF_cong)
    show " \<forall>\<^sub>F x in at_right 0. (?h \<circ> (*) 2) x =?f x"
      unfolding eventually_at_right
      apply (intro exI[where x="1/2"])
      by (auto simp add:joinpaths_def)
  qed simp
  also have "... =jumpF_pathstart (g1+++g2) z"
    unfolding jumpF_pathstart_def by simp
  finally show ?thesis by simp
qed
  
lemma jumpF_pathfinish_joinpaths[simp]:
  "jumpF_pathfinish (g1+++g2) z = jumpF_pathfinish g2 z"
proof -
  let ?h="(\<lambda>t. Im (g2 t - z) / Re (g2 t - z))"
  let ?f="\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)"
  have "jumpF_pathfinish g2 z = jumpF ?h (at_left 1)"
    unfolding jumpF_pathfinish_def by simp
  also have "... = jumpF (?h o (\<lambda>t. 2*t-1)) (at_left 1)"
    using jumpF_linear_comp[of 2 _ "-1" 1,simplified] by auto
  also have "... = jumpF ?f (at_left 1)"
  proof (rule jumpF_cong)
    show " \<forall>\<^sub>F x in at_left 1. (?h \<circ> (\<lambda>t. 2 * t - 1)) x =?f x"
      unfolding eventually_at_left
      apply (intro exI[where x="1/2"])
      by (auto simp add:joinpaths_def)
  qed simp
  also have "... =jumpF_pathfinish (g1+++g2) z"
    unfolding jumpF_pathfinish_def by simp
  finally show ?thesis by simp
qed  
  
subsection \<open>Cauchy index\<close>  

\<comment>\<open>Deprecated, use "cindexE" if possible\<close>
definition cindex::"real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> int" where
  "cindex a b f = (\<Sum>x\<in>{x. jump f x\<noteq>0 \<and> a<x \<and> x<b}. jump f x )"

definition cindexE::"real \<Rightarrow> real \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real" where
  "cindexE a b f = (\<Sum>x\<in>{x. jumpF f (at_right x) \<noteq>0 \<and> a\<le>x \<and> x<b}. jumpF f (at_right x)) 
                    - (\<Sum>x\<in>{x. jumpF f (at_left x) \<noteq>0 \<and> a<x \<and> x\<le>b}. jumpF f (at_left x))"     

definition cindexE_ubd::"(real \<Rightarrow> real) \<Rightarrow> real" where
  "cindexE_ubd f = (\<Sum>x\<in>{x. jumpF f (at_right x) \<noteq>0 }. jumpF f (at_right x)) 
                      - (\<Sum>x\<in>{x. jumpF f (at_left x) \<noteq>0}. jumpF f (at_left x))"

  
lemma cindexE_empty:
  "cindexE a a f = 0"
  unfolding cindexE_def by (simp add: sum.neutral)     
  
lemma cindex_const: "cindex a b (\<lambda>_. c) = 0"
  unfolding cindex_def
  apply (rule sum.neutral)
  by auto
      
lemma cindex_eq_cindex_poly: "cindex a b (\<lambda>x. poly q x/poly p x) = cindex_poly a b q p"  
proof (cases "p=0")
  case True
  then show ?thesis using cindex_const by auto
next
  case False
  have "cindex_poly a b q p = 
      (\<Sum>x |jump_poly q p x \<noteq>0 \<and> a < x \<and> x < b. jump_poly q p x)"
    unfolding cindex_poly_def 
    apply (rule sum.mono_neutral_cong_right)
    using jump_poly_not_root by (auto simp add: \<open>p\<noteq>0\<close> poly_roots_finite)
  also have "... = cindex a b (\<lambda>x. poly q x/poly p x)"
    unfolding cindex_def
    apply (rule sum.cong)
    using jump_jump_poly[of q] by auto
  finally show ?thesis by auto
qed
  
lemma cindex_combine:
  assumes finite:"finite {x. jump f x\<noteq>0 \<and> a<x \<and> x<c}" and "a<b" "b<c"
  shows "cindex a c f = cindex a b f  + jump f b + cindex b c f"
proof -
  define ssum where "ssum = (\<lambda>s. sum (jump f) ({x. jump f x\<noteq>0 \<and> a<x \<and> x<c} \<inter> s))"  
  have ssum_union:"ssum (A \<union> B) = ssum A + ssum B" when "A \<inter> B ={}" for A B
  proof -
    define C where "C={x. jump f x \<noteq> 0 \<and> a<x \<and> x<c}"
    have "finite C" using finite unfolding C_def .
    then show ?thesis
      unfolding ssum_def
      apply (fold C_def)
      using sum_Un[of "C \<inter> A" "C \<inter> B"] that
      by (simp add: inf_assoc inf_sup_aci(3) inf_sup_distrib1 sum.union_disjoint)
  qed
  have "cindex a c f = ssum ({a<..<b} \<union> {b} \<union> {b<..<c})"
    unfolding ssum_def cindex_def 
    apply (rule sum.cong[of _ _ "jump f" "jump f",simplified])
    using \<open>a<b\<close> \<open>b<c\<close> by fastforce
  moreover have "cindex a b f = ssum {a<..<b}" 
    unfolding cindex_def ssum_def using \<open>a<b\<close> \<open>b<c\<close> 
    by (intro sum.cong,auto)
  moreover have "jump f b = ssum {b}" 
    unfolding ssum_def using \<open>a<b\<close> \<open>b<c\<close>  by (cases "jump f b=0",auto)
  moreover have "cindex b c f = ssum {b<..<c}" 
    unfolding cindex_def ssum_def using \<open>a<b\<close> \<open>b<c\<close>  by (intro sum.cong,auto)
  ultimately show ?thesis 
    apply (subst (asm) ssum_union,simp)
    by (subst (asm) ssum_union,auto)
qed
 
lemma cindexE_combine:
  assumes finite:"finite_jumpFs f a c" and "a\<le>b" "b\<le>c"
  shows "cindexE a c f = cindexE a b f + cindexE b c f" 
proof -
  define S where "S={x. (jumpF f (at_left x) \<noteq> 0 \<or> jumpF f (at_right x) \<noteq> 0) \<and> a \<le> x \<and> x \<le> c}"
  define A0 where "A0={x. jumpF f (at_right x) \<noteq> 0 \<and> a \<le> x \<and> x < c}"
  define A1 where "A1={x. jumpF f (at_right x) \<noteq> 0 \<and> a \<le> x \<and> x < b}" 
  define A2 where "A2={x. jumpF f (at_right x) \<noteq> 0 \<and> b \<le> x \<and> x < c}"
  define B0 where "B0={x. jumpF f (at_left x) \<noteq> 0 \<and> a < x \<and> x \<le> c}"
  define B1 where "B1={x. jumpF f (at_left x) \<noteq> 0 \<and> a < x \<and> x \<le> b}" 
  define B2 where "B2={x. jumpF f (at_left x) \<noteq> 0 \<and> b < x \<and> x \<le> c}"
  have [simp]:"finite A1" "finite A2" "finite B1" "finite B2" 
  proof -
    have "finite S" using finite unfolding finite_jumpFs_def S_def by auto
    moreover have "A1 \<subseteq> S" "A2 \<subseteq> S" "B1 \<subseteq> S" "B2 \<subseteq> S"
      unfolding A1_def A2_def B1_def B2_def S_def using \<open>a\<le>b\<close> \<open>b\<le>c\<close> by auto
    ultimately show "finite A1" "finite A2" "finite B1" "finite B2" by (auto elim:finite_subset)
  qed 
  have "cindexE a c f = sum (\<lambda>x. jumpF f (at_right x)) A0 
        - sum (\<lambda>x. jumpF f (at_left x)) B0"
    unfolding cindexE_def A0_def B0_def by auto
  also have "... = sum (\<lambda>x. jumpF f (at_right x)) (A1 \<union> A2) 
        - sum (\<lambda>x. jumpF f (at_left x)) (B1 \<union> B2)"
  proof -
    have "A0=A1\<union>A2" unfolding A0_def A1_def A2_def using assms by auto
    moreover have "B0=B1\<union>B2" unfolding B0_def B1_def B2_def using assms by auto
    ultimately show ?thesis by auto
  qed
  also have "... = cindexE a b f + cindexE b c f"
  proof -
    have "A1 \<inter> A2 = {}" unfolding A1_def A2_def by auto
    moreover have "B1 \<inter> B2 = {}" unfolding B1_def B2_def by auto
    ultimately show ?thesis
      unfolding cindexE_def  
      apply (fold A1_def A2_def B1_def B2_def)
      by (auto simp add:sum.union_disjoint) 
  qed
  finally show ?thesis .
qed

lemma cindex_linear_comp:
  assumes "c\<noteq>0"
  shows "cindex lb ub (f o (\<lambda>x. c*x+b)) = (if c>0 
    then cindex (c*lb+b) (c*ub+b) f 
    else - cindex (c*ub+b) (c*lb+b) f)"
proof (cases "c>0")
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  have "cindex lb ub (f o (\<lambda>x. c*x+b)) = - cindex (c*ub+b) (c*lb+b) f"
    unfolding cindex_def
    apply (subst sum_negf[symmetric])
    apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
    subgoal by (simp add: inj_on_def)
    subgoal using False
      apply (subst jump_linear_comp[OF \<open>c\<noteq>0\<close>])
      by (auto simp add:\<open>c<0\<close> \<open>c\<noteq>0\<close> field_simps)
    subgoal for x
      apply (subst jump_linear_comp[OF \<open>c\<noteq>0\<close>])
      by (auto simp add:\<open>c<0\<close> \<open>c\<noteq>0\<close> False field_simps)
    done 
  then show ?thesis using False by auto
next
  case True
  have "cindex lb ub (f o (\<lambda>x. c*x+b)) = cindex (c*lb+b) (c*ub+b) f"
    unfolding cindex_def
    apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
    subgoal by (simp add: inj_on_def)
    subgoal 
      apply (subst jump_linear_comp[OF \<open>c\<noteq>0\<close>])
      by (auto simp add: True \<open>c\<noteq>0\<close> field_simps)
    subgoal for x
      apply (subst jump_linear_comp[OF \<open>c\<noteq>0\<close>])
      by (auto simp add: \<open>c\<noteq>0\<close> True field_simps)
    done 
  then show ?thesis using True by auto
qed     

lemma cindexE_linear_comp: 
  assumes "c\<noteq>0"
  shows "cindexE lb ub (f o (\<lambda>x. c*x+b)) = (if c>0 
    then cindexE (c*lb+b) (c*ub+b) f 
    else - cindexE (c*ub+b) (c*lb+b) f)"  
proof -
  define cright where "cright = (\<lambda>lb ub f. (\<Sum>x | jumpF f (at_right x) \<noteq> 0 \<and> lb \<le> x \<and> x < ub. 
                        jumpF f (at_right x)))"
  define cleft where "cleft = (\<lambda>lb ub f. (\<Sum>x | jumpF f (at_left x) \<noteq> 0 \<and> lb < x \<and> x \<le> ub. 
                        jumpF f (at_left x)))"
  have cindexE_unfold:"cindexE lb ub f = cright lb ub f - cleft lb ub f"
    for lb ub f unfolding cindexE_def cright_def cleft_def by auto
  have ?thesis when "c<0"
  proof -
    have "cright lb ub (f \<circ> (\<lambda>x. c * x + b)) = cleft (c * ub + b) (c * lb + b) f" 
      unfolding cright_def cleft_def
      apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
      subgoal by (simp add: inj_on_def)
      subgoal using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add:field_simps)
      subgoal for x using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add: field_simps)
      done  
    moreover have "cleft lb ub (f \<circ> (\<lambda>x. c * x + b)) = cright (c*ub+b) (c*lb + b) f" 
      unfolding cright_def cleft_def
      apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
      subgoal by (simp add: inj_on_def)
      subgoal using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add:field_simps)
      subgoal for x using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add: field_simps)
      done 
    ultimately show ?thesis unfolding cindexE_unfold using that by auto 
  qed
  moreover have ?thesis when "c>0"
  proof -
    have "cright lb ub (f \<circ> (\<lambda>x. c * x + b)) = cright (c * lb + b) (c * ub + b) f" 
      unfolding cright_def cleft_def
      apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
      subgoal by (simp add: inj_on_def)
      subgoal using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add:field_simps)
      subgoal for x using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add: field_simps)
      done   
    moreover have "cleft lb ub (f \<circ> (\<lambda>x. c * x + b)) = cleft (c*lb+b) (c*ub + b) f" 
      unfolding cright_def cleft_def
      apply (intro sum.reindex_cong[of "\<lambda>x. (x-b)/c"])
      subgoal by (simp add: inj_on_def)
      subgoal using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add:field_simps)
      subgoal for x using that
        by (subst jumpF_linear_comp[OF \<open>c\<noteq>0\<close>],auto simp add: field_simps)
      done 
    ultimately show ?thesis unfolding cindexE_unfold using that by auto
  qed
  ultimately show ?thesis using \<open>c\<noteq>0\<close> by auto
qed

lemma cindexE_cong:
  assumes "finite s" and fg_eq:"\<And>x. \<lbrakk>a<x;x<b;x\<notin>s\<rbrakk> \<Longrightarrow> f x = g x"
  shows "cindexE a b f = cindexE a b g"
proof -
  define left where 
      "left=(\<lambda>f. (\<Sum>x | jumpF f (at_left x) \<noteq> 0 \<and> a < x \<and> x \<le> b. jumpF f (at_left x)))"
  define right where 
      "right=(\<lambda>f. (\<Sum>x | jumpF f (at_right x) \<noteq> 0 \<and> a \<le> x \<and> x < b. jumpF f (at_right x)))"
  have "left f = left g"
  proof -
    have "jumpF f (at_left x) = jumpF g (at_left x)" when "a<x" "x\<le>b" for x 
    proof (rule jumpF_cong)
      define cs where "cs \<equiv> {y\<in>s. a<y \<and> y<x}"
      define c where "c\<equiv> (if cs = {} then (x+a)/2 else Max cs)"
      have "finite cs" unfolding cs_def using assms(1) by auto
      have "c<x \<and> (\<forall>y. c<y \<and> y<x \<longrightarrow> f y=g y)" 
      proof (cases "cs={}")
        case True
        then have "\<forall>y. c<y \<and> y<x \<longrightarrow> y \<notin> s" unfolding cs_def c_def by force
        moreover have "c=(x+a)/2" using True unfolding c_def by auto
        ultimately show ?thesis using fg_eq using that by auto
      next
        case False
        then have "c\<in>cs" unfolding c_def using False \<open>finite cs\<close> by auto
        moreover have "\<forall>y. c<y \<and> y<x \<longrightarrow> y \<notin> s" 
        proof (rule ccontr)
          assume "\<not> (\<forall>y. c < y \<and> y < x \<longrightarrow> y \<notin> s) "
          then obtain y' where "c<y'" "y'<x" "y'\<in>s" by auto
          then have "y'\<in>cs" using \<open>c\<in>cs\<close> unfolding cs_def by auto
          then have "y'\<le>c" unfolding c_def using False \<open>finite cs\<close> by auto
          then show False using \<open>c<y'\<close> by auto
        qed
        ultimately show ?thesis unfolding cs_def using that by (auto intro!:fg_eq)
      qed  
      then show "\<forall>\<^sub>F x in at_left x. f x = g x"
        unfolding eventually_at_left by auto
    qed simp
    then show ?thesis
      unfolding left_def
      by (auto intro: sum.cong)
  qed
  moreover have "right f = right g"
  proof -
    have "jumpF f (at_right x) = jumpF g (at_right x)" when "a\<le>x" "x<b" for x 
    proof (rule jumpF_cong)
      define cs where "cs \<equiv> {y\<in>s. x<y \<and> y<b}"
      define c where "c\<equiv> (if cs = {} then (x+b)/2 else Min cs)"
      have "finite cs" unfolding cs_def using assms(1) by auto
      have "x<c \<and> (\<forall>y. x<y \<and> y<c \<longrightarrow> f y=g y)" 
      proof (cases "cs={}")
        case True
        then have "\<forall>y. x<y \<and> y<c \<longrightarrow> y \<notin> s" unfolding cs_def c_def by force
        moreover have "c=(x+b)/2" using True unfolding c_def by auto
        ultimately show ?thesis using fg_eq using that by auto
      next
        case False
        then have "c\<in>cs" unfolding c_def using False \<open>finite cs\<close> by auto
        moreover have "\<forall>y. x<y \<and> y<c \<longrightarrow> y \<notin> s" 
        proof (rule ccontr)
          assume "\<not> (\<forall>y. x < y \<and> y < c \<longrightarrow> y \<notin> s) "
          then obtain y' where "x<y'" "y'<c" "y'\<in>s" by auto
          then have "y'\<in>cs" using \<open>c\<in>cs\<close> unfolding cs_def by auto
          then have "y'\<ge>c" unfolding c_def using False \<open>finite cs\<close> by auto
          then show False using \<open>c>y'\<close> by auto
        qed
        ultimately show ?thesis unfolding cs_def using that by (auto intro!:fg_eq)
      qed  
      then show "\<forall>\<^sub>F x in at_right x. f x = g x"
        unfolding eventually_at_right by auto
    qed simp
    then show ?thesis
      unfolding right_def
      by (auto intro: sum.cong)
  qed
  ultimately show ?thesis unfolding cindexE_def left_def right_def by presburger
qed
      
lemma cindexE_constI:
  assumes "\<And>t. \<lbrakk>a<t;t<b\<rbrakk> \<Longrightarrow> f t=c"
  shows "cindexE a b f = 0"
proof -
  define left where 
      "left=(\<lambda>f. (\<Sum>x | jumpF f (at_left x) \<noteq> 0 \<and> a < x \<and> x \<le> b. jumpF f (at_left x)))"
  define right where 
      "right=(\<lambda>f. (\<Sum>x | jumpF f (at_right x) \<noteq> 0 \<and> a \<le> x \<and> x < b. jumpF f (at_right x)))"
  have "left f = 0"  
  proof -
    have "jumpF f (at_left x) = 0" when "a<x" "x\<le>b" for x 
      apply (rule jumpF_eventually_const[of _ c])
      unfolding eventually_at_left using assms that by auto
    then show ?thesis unfolding left_def by auto
  qed
  moreover have "right f = 0"  
  proof -
    have "jumpF f (at_right x) = 0" when "a\<le>x" "x<b" for x 
      apply (rule jumpF_eventually_const[of _ c])
      unfolding eventually_at_right using assms that by auto
    then show ?thesis unfolding right_def by auto
  qed
  ultimately show ?thesis unfolding cindexE_def left_def right_def by auto
qed

lemma cindex_eq_cindexE_divide:
  fixes f g::"real \<Rightarrow> real"
  defines "h \<equiv> (\<lambda>x. f x/g x)"
  assumes "a<b" and
    finite_fg: "finite {x. (f x=0\<or>g x=0) \<and> a\<le>x\<and>x\<le>b}" and 
    g_imp_f:"\<forall>x\<in>{a..b}. g x=0 \<longrightarrow> f x\<noteq>0" and
    f_cont:"continuous_on {a..b} f" and
    g_cont:"continuous_on {a..b} g"
  shows "cindexE a b h = jumpF h (at_right a) + cindex a b h - jumpF h (at_left b)"  
proof -
  define R where "R=(\<lambda>S.{x. jumpF h (at_right x) \<noteq> 0 \<and> x\<in>S})"
  define L where "L=(\<lambda>S.{x. jumpF h (at_left x) \<noteq> 0 \<and> x\<in>S})"
  define right where "right = (\<lambda>S. (\<Sum>x\<in>R S. jumpF h (at_right x)))"
  define left where "left = (\<lambda>S. (\<Sum>x\<in>L S. jumpF h (at_left x)))"
  have jump_gnz:"jumpF h (at_left x) = 0" "jumpF h (at_right x) = 0" "jump h x=0" 
      when "a<x" "x<b" "g x\<noteq>0" for x
    proof -
      have "isCont h x" unfolding h_def using f_cont g_cont that
        by (auto intro!:continuous_intros elim:continuous_on_interior)
      then show "jumpF h (at_left x) = 0" "jumpF h (at_right x) = 0" "jump h x=0" 
        using jumpF_not_infinity jump_not_infinity unfolding continuous_at_split by auto
    qed  
    
  have finite_jFs:"finite_jumpFs h a b" 
  proof -
    define S where "S=(\<lambda>s. {x. (jumpF h (at_left x) \<noteq> 0 \<or> jumpF h (at_right x) \<noteq> 0) \<and> x\<in>s})"
    note jump_gnz
    then have "S {a<..<b} \<subseteq> {x. (f x=0\<or>g x=0) \<and> a\<le>x\<and>x\<le>b}"
      unfolding S_def by auto
    then have "finite (S {a<..<b})" 
      using rev_finite_subset[OF finite_fg] by auto
    moreover have "finite (S {a,b})" unfolding S_def by auto
    moreover have "S {a..b} = S {a<..<b} \<union> S {a,b}" 
      unfolding S_def using \<open>a<b\<close> by auto
    ultimately have "finite (S {a..b})" by auto
    then show ?thesis unfolding S_def finite_jumpFs_def by auto
  qed
  have "cindexE a b h = right {a..<b} - left {a<..b}"
    unfolding cindexE_def right_def left_def R_def L_def by auto
  also have "... = jumpF h (at_right a) +  right {a<..<b} - left {a<..<b} - jumpF h (at_left b)"
  proof -
    have "right {a..<b} = jumpF h (at_right a) +  right {a<..<b}"
    proof (cases "jumpF h (at_right a) =0")
      case True
      then have "R {a..<b} = R {a<..<b}"
        unfolding R_def using less_eq_real_def by auto
      then have "right {a..<b} = right {a<..<b}"
        unfolding right_def by auto
      then show ?thesis using True by auto
    next
      case False
      have "finite (R {a..<b})"
        using finite_jFs unfolding R_def finite_jumpFs_def 
        by (auto elim:rev_finite_subset)
      moreover have "a \<in> R {a..<b}" using False \<open>a<b\<close> unfolding R_def by auto
      moreover have "R {a..<b} - {a} = R {a<..<b}" unfolding R_def by auto
      ultimately show "right {a..<b}= jumpF h (at_right a) 
            + right {a<..<b}"
        using sum.remove[of "R {a..<b}" a "\<lambda>x. jumpF h (at_right x)"]
        unfolding right_def by simp
    qed
    moreover have "left {a<..b} = jumpF h (at_left b) +  left {a<..<b}"
    proof (cases "jumpF h (at_left b) =0")
      case True
      then have "L {a<..b} = L {a<..<b}"
        unfolding L_def using less_eq_real_def by auto
      then have "left {a<..b} = left {a<..<b}"
        unfolding left_def by auto
      then show ?thesis using True by auto
    next
      case False
      have "finite (L {a<..b})"
        using finite_jFs unfolding L_def finite_jumpFs_def 
        by (auto elim:rev_finite_subset)
      moreover have "b \<in> L {a<..b}" using False \<open>a<b\<close> unfolding L_def by auto
      moreover have "L {a<..b} - {b} = L {a<..<b}" unfolding L_def by auto
      ultimately show "left {a<..b}= jumpF h (at_left b) + left {a<..<b}"
        using sum.remove[of "L {a<..b}" b "\<lambda>x. jumpF h (at_left x)"]
        unfolding left_def by simp
    qed  
    ultimately show ?thesis by simp
  qed
  also have "... = jumpF h (at_right a) + cindex a b h - jumpF h (at_left b)"
  proof -
    define S where "S={x. g x=0 \<and> a < x \<and> x < b}"
    have "right {a<..<b} = sum (\<lambda>x. jumpF h (at_right x)) S"
      unfolding right_def S_def R_def
      apply (rule sum.mono_neutral_left)
      subgoal using finite_fg by (auto elim:rev_finite_subset)
      subgoal using jump_gnz by auto
      subgoal by auto
      done
    moreover have "left {a<..<b} = sum (\<lambda>x. jumpF h (at_left x)) S"
      unfolding left_def S_def L_def
      apply (rule sum.mono_neutral_left)
      subgoal using finite_fg by (auto elim:rev_finite_subset)
      subgoal using jump_gnz by auto
      subgoal by auto
      done   
    ultimately have "right {a<..<b} - left {a<..<b} 
        = sum (\<lambda>x. jumpF h (at_right x) - jumpF h (at_left x)) S"
      by (simp add: sum_subtractf)
    also have "... = sum (\<lambda>x. of_int(jump h x)) S"
    proof (rule sum.cong)
      fix x assume "x\<in>S"
      define hr where "hr = sgnx h (at_right x)"
      define hl where "hl = sgnx h (at_left x)"
      have "h sgnx_able (at_left x)" "hr\<noteq>0" "h sgnx_able (at_right x)" "hl\<noteq>0" 
      proof -
        have "finite {t. h t = 0 \<and> a < t \<and> t < b}" 
          using finite_fg unfolding h_def by (auto elim!:rev_finite_subset)
        moreover have "continuous_on ({a<..<b} - {x. g x = 0 \<and> a < x \<and> x < b}) h" 
          unfolding h_def using f_cont g_cont
          by (auto intro!: continuous_intros elim:continuous_on_subset) 
        moreover have "finite {x. g x = 0 \<and> a < x \<and> x < b}" 
          using finite_fg by (auto elim!:rev_finite_subset)
        moreover have  " x \<in> {a<..<b}" 
          using \<open>x\<in>S\<close> unfolding S_def by auto
        ultimately show "h sgnx_able (at_left x)"  "hl\<noteq>0" "h sgnx_able (at_right x)"  "hr\<noteq>0" 
          using  finite_sgnx_at_left_at_right[of h a b "{x. g x=0 \<and> a<x\<and>x<b}" x] 
          unfolding hl_def hr_def by blast+
      qed
      then have "(h has_sgnx hl) (at_left x)" "(h has_sgnx hr) (at_right x)"
        unfolding hl_def hr_def using sgnx_able_sgnx by blast+
      moreover have "isCont (inverse \<circ> h) x" 
      proof -
        have "f x\<noteq>0" using \<open>x\<in>S\<close> g_imp_f unfolding S_def by auto
        then show ?thesis using f_cont g_cont \<open>x\<in>S\<close> unfolding h_def S_def
          by (auto simp add:comp_def intro!:continuous_intros elim:continuous_on_interior)
      qed
      ultimately show "jumpF h (at_right x) - jumpF h (at_left x) = real_of_int (jump h x)" 
        using jump_jumpF[of x h] \<open>hr\<noteq>0\<close> \<open>hl\<noteq>0\<close> by auto
    qed auto
    also have "... = cindex a b h"
      unfolding cindex_def of_int_sum S_def
      apply (rule sum.mono_neutral_cong_right)
      using jump_gnz finite_fg by (auto elim:rev_finite_subset)  
    finally show ?thesis by simp
  qed
  finally show ?thesis .
qed  

subsection \<open>Cauchy index along a path\<close>

\<comment>\<open>Deprecated, use "cindex\_pathE" if possible\<close>
definition cindex_path::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> int" where
  "cindex_path g z = cindex 0 1 (\<lambda>t. Im (g t - z) / Re (g t - z))" 
   
definition cindex_pathE::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> real" where
  "cindex_pathE g z = cindexE 0 1 (\<lambda>t. Im (g t - z) / Re (g t - z))"

lemma cindex_pathE_point: "cindex_pathE (linepath a a) b = 0"
  unfolding cindex_pathE_def by (simp add:cindexE_constI)

lemma cindex_path_reversepath:
  "cindex_path (reversepath g) z = - cindex_path g z"
proof -
  define f where "f=(\<lambda>t. Im (g t - z) / Re (g t - z))"
  define f' where "f'=(\<lambda>t. Im (reversepath g t - z) / Re (reversepath g t - z))"
  have "f o (\<lambda>t. 1 - t) = f'"
    unfolding f_def f'_def comp_def reversepath_def by auto
  then have "cindex 0 1 f' = - cindex 0 1 f"   
    using cindex_linear_comp[of "-1" 0 1 f 1,simplified] by simp
  then show ?thesis 
    unfolding cindex_path_def 
    apply (fold f_def f'_def)
    by simp
qed 

lemma cindex_pathE_reversepath: "cindex_pathE (reversepath g) z = -cindex_pathE g z"
  using cindexE_linear_comp[of "-1" 0 1 "\<lambda>t. (Im (g t) - Im z) / (Re (g t) - Re z)" 1]  
  by (simp add: cindex_pathE_def reversepath_def o_def)

lemma cindex_pathE_reversepath': "cindex_pathE g z = -cindex_pathE (reversepath g) z"
  using cindexE_linear_comp[of "-1" 0 1 "\<lambda>t. (Im (g t) - Im z) / (Re (g t) - Re z)" 1]  
  by (simp add: cindex_pathE_def reversepath_def o_def)

lemma cindex_pathE_joinpaths:
  assumes g1:"finite_ReZ_segments g1 z" and g2: "finite_ReZ_segments g2 z" and
    "path g1" "path g2" "pathfinish g1 = pathstart g2"
  shows "cindex_pathE (g1+++g2) z = cindex_pathE g1 z + cindex_pathE g2 z"
proof -
  define f where "f = (\<lambda>g (t::real). Im (g t - z) / Re (g t - z))"
  have "cindex_pathE (g1 +++ g2) z =  cindexE 0 1 (f (g1+++g2))"
    unfolding cindex_pathE_def f_def by auto
  also have "... = cindexE 0 (1/2) (f (g1+++g2)) + cindexE (1/2) 1 (f (g1+++g2))"
  proof (rule cindexE_combine)
    show "finite_jumpFs (f (g1 +++ g2)) 0 1" 
      unfolding f_def
      apply (rule finite_ReZ_segments_imp_jumpFs)
      subgoal using finite_ReZ_segments_joinpaths[OF g1 g2] assms(3-5) .
      subgoal using path_join_imp[OF \<open>path g1\<close> \<open>path g2\<close> \<open>pathfinish g1=pathstart g2\<close>] .
      done
  qed auto
  also have "... = cindex_pathE g1 z + cindex_pathE g2 z"
  proof -
    have "cindexE 0 (1/2) (f (g1+++g2)) = cindex_pathE g1 z"
    proof -
      have "cindexE 0 (1/2) (f (g1+++g2)) = cindexE 0 (1/2) (f g1 o ((*) 2))"
        apply (rule cindexE_cong)
        unfolding comp_def joinpaths_def f_def by auto
      also have "... = cindexE 0 1 (f g1)"
        using cindexE_linear_comp[of 2 0 "1/2" _ 0,simplified] by simp
      also have "... = cindex_pathE g1 z"
        unfolding cindex_pathE_def f_def by auto
      finally show ?thesis .
    qed
    moreover have "cindexE (1/2) 1 (f (g1+++g2)) = cindex_pathE g2 z"
    proof -
      have "cindexE (1/2) 1 (f (g1+++g2)) = cindexE (1/2) 1 (f g2 o (\<lambda>x. 2*x  - 1))"
        apply (rule cindexE_cong)
        unfolding comp_def joinpaths_def f_def by auto
      also have "... = cindexE 0 1 (f g2)"
        using cindexE_linear_comp[of 2 "1/2" 1 _ "-1",simplified] by simp
      also have "... = cindex_pathE g2 z"
        unfolding cindex_pathE_def f_def by auto
      finally show ?thesis .
    qed  
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma cindex_pathE_constI:
  assumes "\<And>t. \<lbrakk>0<t;t<1\<rbrakk> \<Longrightarrow> g t=c"
  shows "cindex_pathE g z = 0"
  unfolding cindex_pathE_def
  apply (rule cindexE_constI)
  using assms by auto
  
lemma cindex_pathE_subpath_combine:
  assumes g:"finite_ReZ_segments g z"and "path g" and
     "0\<le>a" "a\<le>b" "b\<le>c" "c\<le>1"
  shows "cindex_pathE (subpath a b g) z + cindex_pathE (subpath b c g) z 
          = cindex_pathE (subpath a c g) z"
proof -
  define f where "f = (\<lambda>t. Im (g t - z) / Re (g t - z))"
  have ?thesis when "a=b"
  proof -
    have "cindex_pathE (subpath a b g) z = 0"
      apply (rule cindex_pathE_constI)
      using that unfolding subpath_def by auto
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "b=c" 
  proof -
    have "cindex_pathE (subpath b c g) z = 0"
      apply (rule cindex_pathE_constI)
      using that unfolding subpath_def by auto
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "a\<noteq>b" "b\<noteq>c"
  proof -
    have  [simp]:"a<b" "b<c" "a<c" 
      using that \<open>a\<le>b\<close> \<open>b\<le>c\<close> by auto
    have "cindex_pathE (subpath a b g) z = cindexE a b f"
    proof -
      have "cindex_pathE (subpath a b g) z = cindexE 0 1 (f \<circ> (\<lambda>x. (b - a) * x + a))"
        unfolding cindex_pathE_def f_def comp_def subpath_def by auto
      also have "... =  cindexE a b f"
        using cindexE_linear_comp[of "b-a" 0 1 f a,simplified] that(1) by auto
      finally show ?thesis .
    qed
    moreover have "cindex_pathE (subpath b c g) z = cindexE b c f"
    proof -
      have "cindex_pathE (subpath b c g) z = cindexE 0 1 (f \<circ> (\<lambda>x. (c - b) * x + b))"
        unfolding cindex_pathE_def f_def comp_def subpath_def by auto
      also have "... =  cindexE b c f"
        using cindexE_linear_comp[of "c-b" 0 1 f b,simplified] that(2) by auto
      finally show ?thesis .
    qed
    moreover have "cindex_pathE (subpath a c g) z = cindexE a c f" 
    proof -
      have "cindex_pathE (subpath a c g) z = cindexE 0 1 (f \<circ> (\<lambda>x. (c - a) * x + a))"
        unfolding cindex_pathE_def f_def comp_def subpath_def by auto
      also have "... =  cindexE a c f"
        using cindexE_linear_comp[of "c-a" 0 1 f a,simplified] \<open>a<c\<close> by auto
      finally show ?thesis .
    qed
    moreover have "cindexE a b f + cindexE b c f = cindexE a c f "
    proof -
      have "finite_jumpFs f a c" 
        using finite_ReZ_segments_imp_jumpFs[OF g \<open>path g\<close>] \<open>0\<le>a\<close> \<open>c\<le>1\<close> unfolding f_def
        by (elim finite_jumpFs_subE,auto)
      then show ?thesis using cindexE_linear_comp cindexE_combine[OF _ \<open>a\<le>b\<close> \<open>b\<le>c\<close>] by auto
    qed
    ultimately show ?thesis by auto  
  qed
  ultimately show ?thesis by blast 
qed
  
lemma cindex_pathE_shiftpath:
  assumes "finite_ReZ_segments g z" "s\<in>{0..1}" "path g" and loop:"pathfinish g = pathstart g"
  shows "cindex_pathE (shiftpath s g) z = cindex_pathE g z" 
proof -
  define f where "f=(\<lambda>g t. Im (g (t::real) - z) / Re (g t - z))"
  have "cindex_pathE (shiftpath s g) z = cindexE 0 1 (f (shiftpath s g))"
    unfolding cindex_pathE_def f_def by simp
  also have "... = cindexE 0 (1-s) (f (shiftpath s g)) + cindexE (1-s) 1 (f (shiftpath s g))"
  proof (rule cindexE_combine)
    have "finite_ReZ_segments (shiftpath s g) z"
      using finite_ReZ_segments_shiftpah[OF assms] .
    from finite_ReZ_segments_imp_jumpFs[OF this] path_shiftpath[OF \<open>path g\<close> loop \<open>s\<in>{0..1}\<close>]    
    show "finite_jumpFs (f (shiftpath s g)) 0 1" unfolding f_def by simp
    show "0 \<le> 1 - s" "1 - s \<le> 1" using \<open>s\<in>{0..1}\<close> by auto
  qed 
  also have "... = cindexE 0 s (f g) + cindexE s 1 (f g)"
  proof -
    have "cindexE 0 (1-s) (f (shiftpath s g)) = cindexE s 1 (f g)"
    proof -
      have "cindexE 0 (1-s) (f (shiftpath s g)) = cindexE 0 (1-s) ((f g) o (\<lambda>t. t+s))"
        apply (rule cindexE_cong)
        unfolding shiftpath_def f_def using \<open>s\<in>{0..1}\<close> by (auto simp add:algebra_simps)
      also have "...= cindexE s 1 (f g)"
        using cindexE_linear_comp[of 1 0 "1-s" "f g" s,simplified] .
      finally show ?thesis .
    qed
    moreover have "cindexE (1 - s) 1 (f (shiftpath s g)) = cindexE 0 s (f g)"  
    proof -
      have "cindexE (1 - s) 1 (f (shiftpath s g)) = cindexE (1-s) 1 ((f g) o (\<lambda>t. t+s-1))"
        apply (rule cindexE_cong)
        unfolding shiftpath_def f_def using \<open>s\<in>{0..1}\<close> by (auto simp add:algebra_simps)
      also have "... = cindexE 0 s (f g)"
        using cindexE_linear_comp[of 1 "1-s" 1 "f g" "s-1",simplified] 
        by (simp add:algebra_simps)
      finally show ?thesis .
    qed
    ultimately show ?thesis by auto
  qed
  also have "... = cindexE 0 1 (f g)"
  proof (rule cindexE_combine[symmetric])
    show "finite_jumpFs (f g) 0 1"  
      using finite_ReZ_segments_imp_jumpFs[OF assms(1,3)] unfolding f_def by simp
    show "0 \<le> s" "s\<le>1" using \<open>s\<in>{0..1}\<close> by auto
  qed
  also have "... = cindex_pathE g z"
    unfolding cindex_pathE_def f_def by simp
  finally show ?thesis .
qed 

subsection \<open>Cauchy's Index Theorem\<close>  
    
theorem winding_number_cindex_pathE_aux:
  fixes g::"real \<Rightarrow> complex"
  assumes "finite_ReZ_segments g z" and "valid_path g" "z \<notin> path_image g" and
    Re_ends:"Re (g 1) = Re z" "Re (g 0) = Re z"
  shows "2 * Re(winding_number g z) = - cindex_pathE g z" 
  using assms  
proof (induct rule:finite_ReZ_segments_induct)
  case (sub0 g z)
  have "winding_number (subpath 0 0 g) z = 0" 
    using \<open>z \<notin> path_image (subpath 0 0 g)\<close> unfolding subpath_refl
    by (auto intro!: winding_number_trivial)
  moreover have "cindex_pathE (subpath 0 0 g) z = 0"
    unfolding subpath_def by (auto intro:cindex_pathE_constI)
  ultimately show ?case by auto
next
  case (subEq s g z)
  have Re_winding_0:"Re(winding_number h z) = 0" 
    when Re_const:"\<forall>t\<in>{0..1}. Re (h t) = Re z" and "valid_path h" "z\<notin>path_image h" for h
  proof -
    have "Re (winding_number (\<lambda>t. h t - z) 0) = (Im (Ln (pathfinish (\<lambda>t. h t - z))) 
              - Im (Ln (pathstart (\<lambda>t. h t - z)))) / (2 * pi)"
      apply (rule Re_winding_number_half_right[of _ 0,simplified])
      using Re_const \<open>valid_path h\<close> \<open>z \<notin> path_image h\<close> 
        apply auto
      by (metis (no_types, hide_lams) add.commute imageE le_add_same_cancel1 order_refl 
            path_image_def plus_complex.simps(1))
    moreover have "Im (Ln (h 1 - z)) = Im (Ln (h 0 - z))"
    proof -
      define z0 where "z0 = h 0 - z"
      define z1 where "z1 = h 1 - z"
      have [simp]: "z0\<noteq>0" "z1\<noteq>0" "Re z0=0" "Re z1=0"
        using \<open>z \<notin> path_image h\<close> that(1) unfolding z1_def z0_def path_image_def by auto
      have ?thesis when [simp]: "Im z0>0" "Im z1>0"
        apply (fold z1_def z0_def)
        using Im_Ln_eq_pi_half[of z1] Im_Ln_eq_pi_half[of z0] by auto
      moreover have ?thesis when [simp]: "Im z0<0" "Im z1<0"
        apply (fold z1_def z0_def)
        using Im_Ln_eq_pi_half[of z1] Im_Ln_eq_pi_half[of z0] by auto
      moreover have False when "Im z0\<ge>0" "Im z1\<le>0" 
      proof -
        define f where "f=(\<lambda>t. Im (h t - z))"
        have "\<exists>x\<ge>0. x \<le> 1 \<and> f x = 0"
          apply (rule IVT2'[of f 1 0 0])
          using that valid_path_imp_path[OF \<open>valid_path h\<close>] 
          unfolding f_def z0_def z1_def path_def 
          by (auto intro:continuous_intros)
        then show False using Re_const  \<open>z \<notin> path_image h\<close> unfolding f_def  
          by (metis atLeastAtMost_iff complex_surj image_eqI minus_complex.simps(2) 
                path_defs(4) right_minus_eq)
      qed
      moreover have False when "Im z0\<le>0" "Im z1\<ge>0" 
      proof -
        define f where "f=(\<lambda>t. Im (h t - z))"
        have "\<exists>x\<ge>0. x \<le> 1 \<and> f x = 0"
          apply (rule IVT')
          using that valid_path_imp_path[OF \<open>valid_path h\<close>] 
          unfolding f_def z0_def z1_def path_def 
          by (auto intro:continuous_intros)
        then show False using Re_const \<open>z \<notin> path_image h\<close> unfolding f_def  
          by (metis atLeastAtMost_iff complex_surj image_eqI minus_complex.simps(2) 
                path_defs(4) right_minus_eq)
      qed
      ultimately show ?thesis by argo
    qed
    ultimately have "Re (winding_number (\<lambda>t. h t - z) 0) = 0"
      unfolding pathfinish_def pathstart_def by auto
    then show ?thesis using winding_number_offset by auto
  qed
  have ?case when "s = 0"
  proof -
    have *: "\<forall>t\<in>{0..1}. Re (g t) = Re z" 
      using \<open>\<forall>t\<in>{s<..<1}. Re (g t) = Re z\<close> \<open>Re (g 1) = Re z\<close> \<open>Re (g 0) = Re z\<close> \<open>s=0\<close>
      by force
    have "Re(winding_number g z) = 0"
      by (rule Re_winding_0[OF * \<open>valid_path g\<close> \<open>z \<notin> path_image g\<close>])
    moreover have "cindex_pathE g z = 0"
      unfolding cindex_pathE_def
      apply (rule cindexE_constI)
      using * by auto
    ultimately show ?thesis by auto
  qed
  moreover have ?case when "s\<noteq>0"
  proof -
    define g1 where "g1 = subpath 0 s g"
    define g2 where "g2 = subpath s 1 g"
    have "path g" "s>0" 
      using valid_path_imp_path[OF \<open>valid_path g\<close>] that \<open>s\<in>{0..<1}\<close> by auto
    have "2 * Re (winding_number g z) = 2*Re (winding_number g1 z) + 2*Re (winding_number g2 z)"
      apply (subst winding_number_subpath_combine[OF \<open>path g\<close> \<open>z\<notin>path_image g\<close>,of 0 s 1
            ,simplified,symmetric])
      using \<open>s\<in>{0..<1}\<close> unfolding g1_def g2_def by auto
    also have "... = - cindex_pathE g1 z - cindex_pathE g2 z"
    proof -
      have "2*Re (winding_number g1 z) = - cindex_pathE g1 z" 
        unfolding g1_def
        apply (rule subEq.hyps(5))
        subgoal using subEq.hyps(1) subEq.prems(1) valid_path_subpath by fastforce  
        subgoal by (meson Path_Connected.path_image_subpath_subset atLeastAtMost_iff 
            atLeastLessThan_iff less_eq_real_def subEq(7) subEq.hyps(1) subEq.prems(1) 
            subsetCE valid_path_imp_path zero_le_one) 
        subgoal by (metis Groups.add_ac(2) add_0_left diff_zero mult.right_neutral subEq(2) 
            subEq(9) subpath_def) 
        subgoal by (simp add: subEq.prems(4) subpath_def)
        done
      moreover have "2*Re (winding_number g2 z) = - cindex_pathE g2 z"  
      proof -
        have *: "\<forall>t\<in>{0..1}. Re (g2 t) = Re z"
        proof 
          fix t::real assume "t\<in>{0..1}"
          have "Re (g2 t) = Re z" when "t=0 \<or> t=1"
            using that unfolding g2_def 
            by (metis \<open>s \<noteq> 0\<close> add.left_neutral diff_add_cancel mult.commute mult.left_neutral 
                mult_zero_left subEq.hyps(2) subEq.prems(3) subpath_def)
          moreover have "Re (g2 t) = Re z" when "t\<in>{0<..<1}"
          proof -
            define t' where "t'=(1 - s) * t + s"
            then have "t'\<in>{s<..<1}" 
              using that \<open>s\<in>{0..<1}\<close> unfolding t'_def 
              apply auto
              by (sos "((((A<0 * (A<1 * A<2)) * R<1) + ((A<=1 * (A<0 * R<1)) * (R<1 * [1]^2))))")
            then have "Re (g t') = Re z" 
              using \<open>\<forall>t\<in>{s<..<1}. Re (g t) = Re z\<close> by auto
            then show ?thesis
              unfolding g2_def subpath_def t'_def .
          qed
          ultimately show "Re (g2 t) = Re z" using \<open>t\<in>{0..1}\<close> by fastforce
        qed
        have "Re(winding_number g2 z) = 0"
          apply (rule Re_winding_0[OF *]) 
          subgoal using g2_def subEq.hyps(1) subEq.prems(1) valid_path_subpath by fastforce
          subgoal by (metis (no_types, hide_lams) Path_Connected.path_image_subpath_subset 
                atLeastAtMost_iff atLeastLessThan_iff g2_def less_eq_real_def subEq.hyps(1) 
                subEq.prems(1) subEq.prems(2) subsetCE valid_path_imp_path zero_le_one)  
          done
        moreover have "cindex_pathE g2 z = 0"
          unfolding cindex_pathE_def
          apply (rule cindexE_constI)
          using * by auto
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed
    also have "... = - cindex_pathE g z"
    proof -
      have "finite_ReZ_segments g z"
        unfolding finite_ReZ_segments_def
        apply (rule finite_Psegments.insertI_1[of s])
        subgoal using \<open>s \<in> {0..<1}\<close> by auto
        subgoal using \<open>s = 0 \<or> Re (g s) = Re z\<close> by auto
        subgoal using \<open>\<forall>t\<in>{s<..<1}. Re (g t) = Re z\<close> by auto
        subgoal 
        proof -
          have "finite_Psegments (\<lambda>t. Re (g (s * t)) = Re z) 0 1"
            using \<open>finite_ReZ_segments (subpath 0 s g) z\<close>
            unfolding subpath_def finite_ReZ_segments_def by auto
          from finite_Psegments_pos_linear[of _ "1/s" 0 0 s,simplified,OF this] 
          show "finite_Psegments (\<lambda>t. Re (g t - z) = 0) 0 s" 
            using \<open>s>0\<close> unfolding comp_def by auto
        qed
        done
      then show ?thesis    
        using cindex_pathE_subpath_combine[OF _ \<open>path g\<close>,of z 0 s 1,folded g1_def g2_def,simplified]
          \<open>s\<in>{0..<1}\<close> by auto
    qed
    finally show ?thesis .  
  qed
  ultimately show ?case by auto
next
  case (subNEq s g z)
  have Re_winding:"2*Re(winding_number h z) = jumpF_pathfinish h z - jumpF_pathstart h z" 
    when Re_neq:"\<forall>t\<in>{0<..<1}. Re (h t) \<noteq> Re z" and "Re (h 0) = Re z" "Re (h 1) = Re z"
          and "valid_path h" "z\<notin>path_image h" for h
  proof -
    have Re_winding_pos:
        "2*Re(winding_number h0 0) = jumpF_pathfinish h0 0 - jumpF_pathstart h0 0" 
      when Re_gt:"\<forall>t\<in>{0<..<1}. Re (h0 t) > 0" and "Re (h0 0) = 0" "Re (h0 1) = 0"
          and "valid_path h0" "0\<notin>path_image h0" for h0
    proof -
      define f where "f \<equiv> (\<lambda>(t::real). Im(h0 t) / Re (h0 t))"
      define ln0 where "ln0 = Im (Ln (h0 0)) / pi"
      define ln1 where "ln1 = Im (Ln (h0 1)) / pi"
      have "path h0" using \<open>valid_path h0\<close> valid_path_imp_path by auto
      have "h0 0\<noteq>0" "h0 1\<noteq>0"
        using path_defs(4) that(5) by fastforce+ 
      have "ln1 = jumpF_pathfinish h0 0"  
      proof -
        have sgnx_at_left:"((\<lambda>x. Re (h0 x)) has_sgnx 1) (at_left 1)"
          unfolding has_sgnx_def eventually_at_left using \<open>\<forall>p\<in>{0<..<1}. Re (h0 p) > 0\<close>
          by (intro exI[where x=0],auto)
        have cont:"continuous (at_left 1) (\<lambda>t. Im (h0 t))" 
                "continuous (at_left 1) (\<lambda>t. Re (h0 t))"
          using \<open>path h0\<close> unfolding path_def
          by (auto intro:continuous_on_at_left[of 0 1] continuous_intros)
        have ?thesis when "Im (h0 1) > 0"
        proof -
          have "ln1 = 1/2"
            using Im_Ln_eq_pi_half[OF \<open>h0 1\<noteq>0\<close>] that \<open>Re (h0 1) = 0\<close> unfolding ln1_def by auto 
          moreover have "jumpF_pathfinish h0 0 = 1/2"
          proof -
            have "filterlim f at_top (at_left 1)" unfolding f_def
              apply (subst filterlim_divide_at_bot_at_top_iff[of _ " Im (h0 1)"])  
              using \<open>Re(h0 1) = 0\<close> sgnx_at_left cont that unfolding continuous_within by auto
            then show ?thesis unfolding jumpF_pathfinish_def jumpF_def f_def by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover have ?thesis when "Im (h0 1) < 0"
        proof -
          have "ln1 = - 1/2"
            using Im_Ln_eq_pi_half[OF \<open>h0 1\<noteq>0\<close>] that \<open>Re (h0 1) = 0\<close> unfolding ln1_def by auto
          moreover have "jumpF_pathfinish h0 0 = - 1/2"
          proof -
            have "((\<lambda>x. Re (h0 x)) has_sgnx - sgn (Im (h0 1))) (at_left 1)" 
              using sgnx_at_left that by auto
            then have "filterlim f at_bot (at_left 1)" 
              unfolding f_def using cont that
              apply (subst filterlim_divide_at_bot_at_top_iff[of _ " Im (h0 1)"])
              unfolding continuous_within using \<open>Re(h0 1) = 0\<close> by auto
            then show ?thesis unfolding jumpF_pathfinish_def jumpF_def f_def by auto 
          qed
          ultimately show ?thesis by auto
        qed
        moreover have "Im (h0 1)\<noteq>0" using \<open>h0 1\<noteq>0\<close> \<open>Re (h0 1) = 0\<close> 
          using complex.expand by auto   
        ultimately show ?thesis by linarith
      qed
      moreover have "ln0 = jumpF_pathstart h0 0" 
      proof -
        have sgnx_at_right:"((\<lambda>x. Re (h0 x)) has_sgnx 1) (at_right 0)"
          unfolding has_sgnx_def eventually_at_right using \<open>\<forall>p\<in>{0<..<1}. Re (h0 p) > 0\<close>
          by (intro exI[where x=1],auto)
        have cont:"continuous (at_right 0) (\<lambda>t. Im (h0 t))" 
          "continuous (at_right 0) (\<lambda>t. Re (h0 t))"
          using \<open>path h0\<close> unfolding path_def      
          by (auto intro:continuous_on_at_right[of 0 1] continuous_intros)
        have ?thesis when "Im (h0 0) > 0"   
        proof -
          have "ln0 = 1/2" 
            using Im_Ln_eq_pi_half[OF \<open>h0 0\<noteq>0\<close>] that \<open>Re (h0 0) = 0\<close> unfolding ln0_def by auto 
          moreover have "jumpF_pathstart h0 0 = 1/2"
          proof -
            have "filterlim f at_top (at_right 0)" unfolding f_def
              apply (subst filterlim_divide_at_bot_at_top_iff[of _ " Im (h0 0)"])  
              using \<open>Re(h0 0) = 0\<close> sgnx_at_right cont that unfolding continuous_within by auto
            then show ?thesis unfolding jumpF_pathstart_def jumpF_def f_def by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover have ?thesis when "Im (h0 0) < 0"   
        proof -
          have "ln0 = - 1/2" 
            using Im_Ln_eq_pi_half[OF \<open>h0 0\<noteq>0\<close>] that \<open>Re (h0 0) = 0\<close> unfolding ln0_def by auto 
          moreover have "jumpF_pathstart h0 0 = - 1/2"
          proof -
            have "filterlim f at_bot (at_right 0)" unfolding f_def
              apply (subst filterlim_divide_at_bot_at_top_iff[of _ " Im (h0 0)"])  
              using \<open>Re(h0 0) = 0\<close> sgnx_at_right cont that unfolding continuous_within by auto
            then show ?thesis unfolding jumpF_pathstart_def jumpF_def f_def by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover have "Im (h0 0)\<noteq>0" using \<open>h0 0\<noteq>0\<close> \<open>Re (h0 0) = 0\<close> 
          using complex.expand by auto   
        ultimately show ?thesis by linarith
      qed
      moreover have "2*Re(winding_number h0 0) = ln1 - ln0"
      proof -
        have "\<forall>p\<in>path_image h0. 0 \<le> Re p" 
        proof 
          fix p assume "p \<in> path_image h0"
          then obtain t where t:"t\<in>{0..1}" "p = h0 t" unfolding path_image_def by auto
          have "0 \<le> Re p" when "t=0 \<or> t=1"  
            using that t \<open>Re (h0 0) = 0\<close> \<open>Re (h0 1) = 0\<close> by auto
          moreover have "0 \<le> Re p" when "t\<in>{0<..<1}"
            using that t Re_gt[rule_format, of t] by fastforce 
          ultimately show "0 \<le> Re p" using t(1) by fastforce    
        qed
        from Re_winding_number_half_right[of _ 0,simplified,OF this \<open>valid_path h0\<close> \<open>0 \<notin> path_image h0\<close>]
        show ?thesis unfolding ln1_def ln0_def pathfinish_def pathstart_def 
          by (auto simp add:field_simps)
      qed
      ultimately show ?thesis by auto
    qed
   
    have ?thesis when "\<forall>t\<in>{0<..<1}. Re (h t) < Re z"
    proof -
      let ?hu= "\<lambda>t. z - h t"
      have "2*Re(winding_number ?hu 0) = jumpF_pathfinish ?hu 0 - jumpF_pathstart ?hu 0"
        apply(rule Re_winding_pos)
        subgoal using that by auto
        subgoal using \<open>Re (h 0) = Re z\<close> by auto
        subgoal using \<open>Re (h 1) = Re z\<close> by auto
        subgoal using \<open>valid_path h\<close> valid_path_offset valid_path_uminus_comp 
            unfolding comp_def by fastforce
        subgoal using \<open>z\<notin>path_image h\<close> by (simp add: image_iff path_defs(4)) 
        done
      moreover have "winding_number ?hu 0 = winding_number h z"
        using winding_number_offset[of h z] 
              winding_number_uminus_comp[of "\<lambda>t. h t- z" 0,unfolded comp_def,simplified] 
              \<open>valid_path h\<close> \<open>z\<notin>path_image h\<close> by auto
      moreover have "jumpF_pathfinish ?hu 0 =  jumpF_pathfinish h z"
        unfolding jumpF_pathfinish_def
        apply (auto intro!:jumpF_cong eventuallyI)
        by (auto simp add:divide_simps algebra_simps)
      moreover have "jumpF_pathstart ?hu 0 =  jumpF_pathstart h z"
        unfolding jumpF_pathstart_def
        apply (auto intro!:jumpF_cong eventuallyI)
        by (auto simp add:divide_simps algebra_simps)
      ultimately show ?thesis by auto
    qed
    moreover have ?thesis when "\<forall>t\<in>{0<..<1}. Re (h t) > Re z"
    proof -
      let ?hu= "\<lambda>t. h t - z"
      have "2*Re(winding_number ?hu 0) = jumpF_pathfinish ?hu 0 - jumpF_pathstart ?hu 0"
        apply(rule Re_winding_pos)
        subgoal using that by auto
        subgoal using \<open>Re (h 0) = Re z\<close> by auto
        subgoal using \<open>Re (h 1) = Re z\<close> by auto
        subgoal using \<open>valid_path h\<close> valid_path_offset valid_path_uminus_comp 
            unfolding comp_def by fastforce
        subgoal using \<open>z\<notin>path_image h\<close> by simp 
        done
      moreover have "winding_number ?hu 0 = winding_number h z"
        using winding_number_offset[of h z] \<open>valid_path h\<close> \<open>z\<notin>path_image h\<close> by auto
      moreover have "jumpF_pathfinish ?hu 0 =  jumpF_pathfinish h z"
        unfolding jumpF_pathfinish_def by auto
      moreover have "jumpF_pathstart ?hu 0 =  jumpF_pathstart h z"
        unfolding jumpF_pathstart_def by auto
      ultimately show ?thesis by auto
    qed  
    moreover have "(\<forall>t\<in>{0<..<1}. Re (h t) > Re z) \<or> (\<forall>t\<in>{0<..<1}. Re (h t) < Re z)" 
    proof (rule ccontr)
      assume " \<not> ((\<forall>t\<in>{0<..<1}. Re z < Re (h t)) \<or> (\<forall>t\<in>{0<..<1}. Re (h t) < Re z))"
      then obtain t1 t2 where t:"t1\<in>{0<..<1}" "t2\<in>{0<..<1}" "Re (h t1)\<le>Re z" "Re (h t2)\<ge>Re z"
        unfolding path_image_def by auto 
      have False when "t1\<le>t2"
      proof -
        have "continuous_on {t1..t2} (\<lambda>t. Re (h t))" 
          using valid_path_imp_path[OF \<open>valid_path h\<close>] t unfolding path_def 
          by (metis (full_types) atLeastatMost_subset_iff continuous_on_Re continuous_on_subset 
            eucl_less_le_not_le greaterThanLessThan_iff)
        then obtain t' where t':"t'\<ge>t1" "t'\<le>t2" "Re (h t') = Re z"
          using  IVT'[of "\<lambda>t. Re (h t)" t1 _ t2] t \<open>t1\<le>t2\<close> by auto
        then have "t'\<in>{0<..<1}" using t by auto
        then have "Re (h t') \<noteq> Re z" using Re_neq by auto
        then show False using \<open>Re (h t') = Re z\<close> by simp 
      qed
      moreover have False when "t1\<ge>t2"
      proof -
        have "continuous_on {t2..t1} (\<lambda>t. Re (h t))" 
          using valid_path_imp_path[OF \<open>valid_path h\<close>] t unfolding path_def 
          by (metis (full_types) atLeastatMost_subset_iff continuous_on_Re continuous_on_subset 
            eucl_less_le_not_le greaterThanLessThan_iff)
        then obtain t' where t':"t'\<le>t1" "t'\<ge>t2" "Re (h t') = Re z"
          using  IVT2'[of "\<lambda>t. Re (h t)" t1 _ t2] t \<open>t1\<ge>t2\<close> by auto
        then have "t'\<in>{0<..<1}" using t by auto
        then have "Re (h t') \<noteq> Re z" using Re_neq by auto
        then show False using \<open>Re (h t') = Re z\<close> by simp 
      qed
      ultimately show False by linarith
    qed
    ultimately show ?thesis by blast
  qed
  
  have index_ends:"cindex_pathE h z = jumpF_pathstart h z - jumpF_pathfinish h z"
    when Re_neq:"\<forall>t\<in>{0<..<1}. Re (h t) \<noteq> Re z" and "valid_path h" for h
  proof -
    define f where "f = (\<lambda>t. Im (h t - z) / Re (h t - z))"
    define Ri where "Ri = {x. jumpF f (at_right x) \<noteq> 0 \<and> 0 \<le> x \<and> x < 1}"
    define Le where "Le = {x. jumpF f (at_left x) \<noteq> 0 \<and> 0 < x \<and> x \<le> 1}"
    have "path h" using \<open>valid_path h\<close> valid_path_imp_path by auto
    have jumpF_eq0: "jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0" when "x\<in>{0<..<1}" for x
    proof -
      have "Re (h x) \<noteq> Re z"
        using  \<open>\<forall>t\<in>{0<..<1}. Re (h t) \<noteq> Re z\<close> that by blast
      then have "isCont f x"
        unfolding f_def using continuous_on_interior[OF \<open>path h\<close>[unfolded path_def]] that
        by (auto intro!: continuous_intros isCont_Im isCont_Re)
      then show "jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0"
        unfolding continuous_at_split by (auto intro: jumpF_not_infinity)
    qed
    have "cindex_pathE h z  = cindexE 0 1 f" 
      unfolding cindex_pathE_def f_def by simp
    also have "... = sum (\<lambda>x. jumpF f (at_right x)) Ri - sum (\<lambda>x. jumpF f (at_left x)) Le"
      unfolding cindexE_def Ri_def Le_def by auto
    also have "... = jumpF f (at_right 0) -  jumpF f (at_left 1)"
    proof -
      have "sum (\<lambda>x. jumpF f (at_right x)) Ri = jumpF f (at_right 0)"
      proof (cases "jumpF f (at_right 0) = 0")
        case True
        hence False if "x \<in> Ri" for x using that
          by (cases "x = 0") (auto simp: jumpF_eq0 Ri_def)
        hence "Ri = {}" by blast
        then show ?thesis using True by auto
      next
        case False
        hence "x \<in> Ri \<longleftrightarrow> x = 0" for x using that
          by (cases "x = 0") (auto simp: jumpF_eq0 Ri_def)
        hence "Ri = {0}" by blast
        then show ?thesis by auto
      qed
      moreover have "sum (\<lambda>x. jumpF f (at_left x)) Le = jumpF f (at_left 1)"
      proof (cases "jumpF f (at_left 1) = 0")
        case True
        then have "Le = {}"
          unfolding Le_def using jumpF_eq0(1) greaterThanLessThan_iff by fastforce
        then show ?thesis using True by auto
      next
        case False
        then have "Le = {1}"
          unfolding Le_def using jumpF_eq0(1) greaterThanLessThan_iff by fastforce
        then show ?thesis by auto
      qed  
      ultimately show ?thesis by auto
    qed
    also have "... = jumpF_pathstart h z - jumpF_pathfinish h z"
      unfolding jumpF_pathstart_def jumpF_pathfinish_def f_def by simp
    finally show ?thesis .
  qed

  have ?case when "s=0"
  proof -
    have "2 * Re (winding_number g z) = jumpF_pathfinish g z - jumpF_pathstart g z"
      apply (rule Re_winding)
      using subNEq that by auto
    moreover have "cindex_pathE g z = jumpF_pathstart g z - jumpF_pathfinish g z"
      apply (rule index_ends)
      using subNEq that by auto
    ultimately show ?thesis by auto
  qed
  moreover have ?case when "s\<noteq>0"
  proof -
    define g1 where "g1 = subpath 0 s g"
    define g2 where "g2 = subpath s 1 g"
    have "path g" "s>0" 
      using valid_path_imp_path[OF \<open>valid_path g\<close>] that \<open>s\<in>{0..<1}\<close> by auto
    have "2 * Re (winding_number g z) = 2*Re (winding_number g1 z) + 2*Re (winding_number g2 z)"
      apply (subst winding_number_subpath_combine[OF \<open>path g\<close> \<open>z\<notin>path_image g\<close>,of 0 s 1
            ,simplified,symmetric])
      using \<open>s\<in>{0..<1}\<close> unfolding g1_def g2_def by auto  
    also have "... = - cindex_pathE g1 z - cindex_pathE g2 z"
    proof -
      have "2*Re (winding_number g1 z) = - cindex_pathE g1 z" 
        unfolding g1_def
        apply (rule subNEq.hyps(5))
        subgoal using subNEq.hyps(1) subNEq.prems(1) valid_path_subpath by fastforce  
        subgoal by (meson Path_Connected.path_image_subpath_subset atLeastAtMost_iff 
            atLeastLessThan_iff less_eq_real_def subNEq(7) subNEq.hyps(1) subNEq.prems(1) 
            subsetCE valid_path_imp_path zero_le_one) 
        subgoal by (metis Groups.add_ac(2) add_0_left diff_zero mult.right_neutral subNEq(2) 
            subNEq(9) subpath_def) 
        subgoal by (simp add: subNEq.prems(4) subpath_def)
        done
      moreover have "2*Re (winding_number g2 z) = - cindex_pathE g2 z"  
      proof -
        have *:"\<forall>t\<in>{0<..<1}. Re (g2 t) \<noteq> Re z"
        proof 
          fix t::real assume "t \<in> {0<..<1}"
          define t' where "t'=(1 - s) * t + s"
          have "t'\<in>{s<..<1}" unfolding t'_def using \<open>s\<in>{0..<1}\<close> \<open>t \<in> {0<..<1}\<close> 
            apply (auto simp add:algebra_simps)
            by (sos "((((A<0 * (A<1 * A<2)) * R<1) + ((A<=1 * (A<1 * R<1)) * (R<1 * [1]^2))))")
          then have "Re (g t') \<noteq> Re z" using \<open>\<forall>t\<in>{s<..<1}. Re (g t) \<noteq> Re z\<close> by auto
          then show "Re (g2 t) \<noteq> Re z" unfolding g2_def subpath_def t'_def by auto
        qed
        have "2*Re (winding_number g2 z) = jumpF_pathfinish g2 z - jumpF_pathstart g2 z"
          apply (rule Re_winding[OF *])
          subgoal by (metis add.commute add.right_neutral g2_def mult_zero_right subNEq.hyps(2) 
                subpath_def that)
          subgoal by (simp add: \<open>g2 \<equiv> subpath s 1 g\<close> subNEq.prems(3) subpath_def)
          subgoal using g2_def subNEq.hyps(1) subNEq.prems(1) valid_path_subpath by fastforce
          subgoal by (metis (no_types, hide_lams) Path_Connected.path_image_subpath_subset 
                \<open>path g\<close> atLeastAtMost_iff atLeastLessThan_iff g2_def less_eq_real_def subNEq.hyps(1) 
                subNEq.prems(2) subsetCE zero_le_one)
          done
        moreover have "cindex_pathE g2 z = jumpF_pathstart g2 z - jumpF_pathfinish g2 z" 
          apply (rule index_ends[OF *])
          using g2_def subNEq.hyps(1) subNEq.prems(1) valid_path_subpath by fastforce
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed 
    also have "... = - cindex_pathE g z"
    proof -
      have "finite_ReZ_segments g z"
        unfolding finite_ReZ_segments_def
        apply (rule finite_Psegments.insertI_2[of s])
        subgoal using \<open>s \<in> {0..<1}\<close> by auto
        subgoal using \<open>s = 0 \<or> Re (g s) = Re z\<close> by auto
        subgoal using \<open>\<forall>t\<in>{s<..<1}. Re (g t) \<noteq> Re z\<close> by auto
        subgoal 
        proof -
          have "finite_Psegments (\<lambda>t. Re (g (s * t)) = Re z) 0 1"
            using \<open>finite_ReZ_segments (subpath 0 s g) z\<close>
            unfolding subpath_def finite_ReZ_segments_def by auto
          from finite_Psegments_pos_linear[of _ "1/s" 0 0 s,simplified,OF this] 
          show "finite_Psegments (\<lambda>t. Re (g t - z) = 0) 0 s" 
            using \<open>s>0\<close> unfolding comp_def by auto
        qed
        done
      then show ?thesis    
        using cindex_pathE_subpath_combine[OF _ \<open>path g\<close>,of z 0 s 1,folded g1_def g2_def,simplified]
          \<open>s\<in>{0..<1}\<close> by auto
    qed
    finally show ?thesis .
  qed
  ultimately show ?case by auto
qed

theorem winding_number_cindex_pathE:
  fixes g::"real \<Rightarrow> complex"
  assumes "finite_ReZ_segments g z" and "valid_path g" "z \<notin> path_image g" and
    loop: "pathfinish g = pathstart g"
  shows "winding_number g z = - cindex_pathE g z / 2" 
proof (rule finite_ReZ_segment_cases[OF assms(1)])    
  fix s assume "s \<in> {0..<1}" "s = 0 \<or> Re (g s) = Re z" 
          and const:"\<forall>t\<in>{s<..<1}. Re (g t) = Re z" 
          and finite:"finite_ReZ_segments (subpath 0 s g) z" 
  have "Re (g 1) = Re z"
    apply(rule continuous_constant_on_closure[of "{s<..<1}" "\<lambda>t. Re(g t)"])
    subgoal using valid_path_imp_path[OF \<open>valid_path g\<close>,unfolded path_def] \<open>s\<in>{0..<1}\<close>
      by (auto intro!:continuous_intros continuous_Re elim:continuous_on_subset)
    subgoal using const by auto
    subgoal using \<open>s\<in>{0..<1}\<close> by auto
    done
  moreover then have "Re (g 0) = Re z" using loop unfolding path_defs by auto
  ultimately have "2 * Re (winding_number g z) = - cindex_pathE g z"
    using winding_number_cindex_pathE_aux[of g z] assms(1-3) by auto
  moreover have "winding_number g z \<in> \<int>" 
    using integer_winding_number[OF _ loop \<open>z\<notin>path_image g\<close>] valid_path_imp_path[OF \<open>valid_path g\<close>]
    by auto
  ultimately show "winding_number g z = - cindex_pathE g z / 2"  
    by (metis add.right_neutral complex_eq complex_is_Int_iff mult_zero_right 
        nonzero_mult_div_cancel_left of_real_0 zero_neq_numeral)
next
  fix s assume "s \<in> {0..<1}" "s = 0 \<or> Re (g s) = Re z"
          and Re_neq:"\<forall>t\<in>{s<..<1}. Re (g t) \<noteq> Re z" 
          and finite:"finite_ReZ_segments (subpath 0 s g) z"  
  have "path g" using \<open>valid_path g\<close> valid_path_imp_path by auto
  let ?goal = "2 * Re (winding_number g z) = - cindex_pathE g z"       
  have ?goal when "s=0"
  proof -
    have index_ends:"cindex_pathE h z = jumpF_pathstart h z - jumpF_pathfinish h z"
      when Re_neq:"\<forall>t\<in>{0<..<1}. Re (h t) \<noteq> Re z" and "valid_path h" for h
    proof -
      define f where "f = (\<lambda>t. Im (h t - z) / Re (h t - z))"
      define Ri where "Ri = {x. jumpF f (at_right x) \<noteq> 0 \<and> 0 \<le> x \<and> x < 1}"
      define Le where "Le = {x. jumpF f (at_left x) \<noteq> 0 \<and> 0 < x \<and> x \<le> 1}"
      have "path h" using \<open>valid_path h\<close> valid_path_imp_path by auto
      have jumpF_eq0: "jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0" when "x\<in>{0<..<1}" for x
      proof -
        have "Re (h x) \<noteq> Re z"
          using  \<open>\<forall>t\<in>{0<..<1}. Re (h t) \<noteq> Re z\<close> that by blast
        then have "isCont f x"
          unfolding f_def using continuous_on_interior[OF \<open>path h\<close>[unfolded path_def]] that
          by (auto intro!: continuous_intros isCont_Im isCont_Re)
        then show "jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0"
          unfolding continuous_at_split by (auto intro: jumpF_not_infinity)
      qed
      have "cindex_pathE h z  = cindexE 0 1 f" 
        unfolding cindex_pathE_def f_def by simp
      also have "... = sum (\<lambda>x. jumpF f (at_right x)) Ri - sum (\<lambda>x. jumpF f (at_left x)) Le"
        unfolding cindexE_def Ri_def Le_def by auto
      also have "... = jumpF f (at_right 0) -  jumpF f (at_left 1)"
      proof -
        have "sum (\<lambda>x. jumpF f (at_right x)) Ri = jumpF f (at_right 0)"
        proof (cases "jumpF f (at_right 0) = 0")
          case True
          hence False if "x \<in> Ri" for x using that
            by (cases "x = 0") (auto simp: jumpF_eq0 Ri_def)
          hence "Ri = {}" by blast
          then show ?thesis using True by auto
        next
          case False
          hence "x \<in> Ri \<longleftrightarrow> x = 0" for x using that
            by (cases "x = 0") (auto simp: jumpF_eq0 Ri_def)
          then have "Ri = {0}" by blast
          then show ?thesis by auto
        qed
        moreover have "sum (\<lambda>x. jumpF f (at_left x)) Le = jumpF f (at_left 1)"
        proof (cases "jumpF f (at_left 1) = 0")
          case True
          then have "Le = {}"
            unfolding Le_def using jumpF_eq0(1) greaterThanLessThan_iff by fastforce
          then show ?thesis using True by auto
        next
          case False
          then have "Le = {1}"
            unfolding Le_def using jumpF_eq0(1) greaterThanLessThan_iff by fastforce
          then show ?thesis by auto
        qed  
        ultimately show ?thesis by auto
      qed
      also have "... = jumpF_pathstart h z - jumpF_pathfinish h z"
        unfolding jumpF_pathstart_def jumpF_pathfinish_def f_def by simp
      finally show ?thesis .
    qed
    define fI where "fI=(\<lambda>t. Im (g t - z))"
    define fR where "fR=(\<lambda>t. Re (g t - z))"
    have fI: "(fI \<longlongrightarrow> fI 0) (at_right 0)" "(fI \<longlongrightarrow> fI 1) (at_left 1)" 
    proof -
      have "continuous (at_right 0) fI"
        apply (rule continuous_on_at_right[of _ 1])
        using \<open>path g\<close> unfolding fI_def path_def by (auto intro:continuous_intros) 
      then show "(fI \<longlongrightarrow> fI 0) (at_right 0)" by (simp add: continuous_within)
    next
      have "continuous (at_left 1) fI"
        apply (rule continuous_on_at_left[of 0])
        using \<open>path g\<close> unfolding fI_def path_def by (auto intro:continuous_intros) 
      then show "(fI \<longlongrightarrow> fI 1) (at_left 1)" by (simp add: continuous_within)
    qed  
    have fR: "(fR \<longlongrightarrow> 0) (at_right 0)" "(fR \<longlongrightarrow> 0) (at_left 1)" when "Re (g 0) = Re z" 
    proof -
      have "continuous (at_right 0) fR"
        apply (rule continuous_on_at_right[of _ 1])
        using \<open>path g\<close> unfolding fR_def path_def by (auto intro:continuous_intros) 
      then show "(fR \<longlongrightarrow> 0) (at_right 0)" using that unfolding fR_def by (simp add: continuous_within)
    next
      have "continuous (at_left 1) fR"
        apply (rule continuous_on_at_left[of 0])
        using \<open>path g\<close> unfolding fR_def path_def by (auto intro:continuous_intros) 
      then show "(fR \<longlongrightarrow> 0) (at_left 1)" 
        using that loop unfolding fR_def path_defs by (simp add: continuous_within)
    qed
    have "(\<forall>t\<in>{0<..<1}. Re (g t) > Re z) \<or> (\<forall>t\<in>{0<..<1}. Re (g t) < Re z)" 
    proof (rule ccontr)
      assume " \<not> ((\<forall>t\<in>{0<..<1}. Re z < Re (g t)) \<or> (\<forall>t\<in>{0<..<1}. Re (g t) < Re z))"
      then obtain t1 t2 where t:"t1\<in>{0<..<1}" "t2\<in>{0<..<1}" "Re (g t1)\<le>Re z" "Re (g t2)\<ge>Re z"
        unfolding path_image_def by auto 
      have False when "t1\<le>t2"
      proof -
        have "continuous_on {t1..t2} (\<lambda>t. Re (g t))" 
          using valid_path_imp_path[OF \<open>valid_path g\<close>] t unfolding path_def 
          by (metis (full_types) atLeastatMost_subset_iff continuous_on_Re continuous_on_subset 
            eucl_less_le_not_le greaterThanLessThan_iff)
        then obtain t' where t':"t'\<ge>t1" "t'\<le>t2" "Re (g t') = Re z"
          using  IVT'[of "\<lambda>t. Re (g t)" t1 _ t2] t \<open>t1\<le>t2\<close> by auto
        then have "t'\<in>{0<..<1}" using t by auto
        then have "Re (g t') \<noteq> Re z" using Re_neq \<open>s=0\<close> by auto
        then show False using \<open>Re (g t') = Re z\<close> by simp 
      qed
      moreover have False when "t1\<ge>t2"
      proof -
        have "continuous_on {t2..t1} (\<lambda>t. Re (g t))" 
          using valid_path_imp_path[OF \<open>valid_path g\<close>] t unfolding path_def 
          by (metis (full_types) atLeastatMost_subset_iff continuous_on_Re continuous_on_subset 
            eucl_less_le_not_le greaterThanLessThan_iff)
        then obtain t' where t':"t'\<le>t1" "t'\<ge>t2" "Re (g t') = Re z"
          using  IVT2'[of "\<lambda>t. Re (g t)" t1 _ t2] t \<open>t1\<ge>t2\<close> by auto
        then have "t'\<in>{0<..<1}" using t by auto
        then have "Re (g t') \<noteq> Re z" using Re_neq \<open>s=0\<close> by auto
        then show False using \<open>Re (g t') = Re z\<close> by simp 
      qed
      ultimately show False by linarith
    qed
    moreover have ?thesis when Re_pos:"\<forall>t\<in>{0<..<1}. Re (g t) > Re z"
    proof -
      have "Re (winding_number g z) = 0"
      proof -
        have "\<forall>p\<in>path_image g. Re z \<le> Re p"
        proof 
          fix p assume "p \<in> path_image g"
          then obtain t where "0\<le>t" "t\<le>1" "p = g t" unfolding path_image_def by auto
          have "Re z \<le> Re (g t)"
            apply (rule continuous_ge_on_closure[of "{0<..<1}" "\<lambda>t. Re (g t)" t "Re z",simplified])
            subgoal using valid_path_imp_path[OF \<open>valid_path g\<close>,unfolded path_def] 
              by (auto intro:continuous_intros)
            subgoal using \<open>0\<le>t\<close> \<open>t\<le>1\<close> by auto
            subgoal for x using that[rule_format,of x] by auto
            done
          then show "Re z \<le> Re p" using \<open>p = g t\<close> by auto
        qed
        from Re_winding_number_half_right[OF this \<open>valid_path g\<close> \<open>z\<notin>path_image g\<close>] loop
        show ?thesis by auto
      qed
      moreover have "cindex_pathE g z = 0"
      proof -
        have "cindex_pathE g z = jumpF_pathstart g z - jumpF_pathfinish g z"
          using index_ends[OF _ \<open>valid_path g\<close>] Re_neq \<open>s=0\<close> by auto
        moreover have "jumpF_pathstart g z = jumpF_pathfinish g z" when "Re (g 0) \<noteq> Re z"
        proof -
          have "jumpF_pathstart g z = 0" 
            using jumpF_pathstart_eq_0[OF \<open>path g\<close>] that unfolding path_defs by auto
          moreover have "jumpF_pathfinish g z=0"
            using jumpF_pathfinish_eq_0[OF \<open>path g\<close>] that loop unfolding path_defs by auto 
          ultimately show ?thesis by auto
        qed
        moreover have "jumpF_pathstart g z = jumpF_pathfinish g z" when "Re (g 0) = Re z"  
        proof -
          have [simp]:"(fR has_sgnx 1) (at_right 0)" 
            unfolding fR_def has_sgnx_def eventually_at_right
            apply (rule exI[where x=1])
            using Re_pos by auto
          have [simp]:"(fR has_sgnx 1) (at_left 1)" 
            unfolding fR_def has_sgnx_def eventually_at_left
            apply (rule exI[where x=0])
            using Re_pos by auto
          have "fI 0\<noteq>0" 
          proof (rule ccontr)
            assume "\<not> fI 0 \<noteq> 0"
            then have "g 0 =z" using \<open>Re (g 0) = Re z\<close> 
              unfolding fI_def by (simp add: complex.expand)
            then show False using \<open>z \<notin> path_image g\<close> unfolding path_image_def by auto
          qed
          moreover have ?thesis when "fI 0>0"
          proof -
            have "jumpF_pathstart g z = 1/2"
            proof -
              have "(LIM x at_right 0. fI x / fR x :> at_top)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 0"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathstart_def fI_def fR_def jumpF_def by auto
            qed
            moreover have "jumpF_pathfinish g z = 1/2"
            proof -
              have "fI 1>0" using loop that unfolding path_defs fI_def by auto
              then have "(LIM x at_left 1. fI x / fR x :> at_top)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 1"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathfinish_def fI_def fR_def jumpF_def by auto
            qed  
            ultimately show ?thesis by simp
          qed
          moreover have ?thesis when "fI 0<0" 
          proof -
            have "jumpF_pathstart g z = - 1/2"
            proof -
              have "(LIM x at_right 0. fI x / fR x :> at_bot)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 0"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathstart_def fI_def fR_def jumpF_def by auto
            qed
            moreover have "jumpF_pathfinish g z = - 1/2"
            proof -
              have "fI 1<0" using loop that unfolding path_defs fI_def by auto
              then have "(LIM x at_left 1. fI x / fR x :> at_bot)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 1"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathfinish_def fI_def fR_def jumpF_def by auto
            qed  
            ultimately show ?thesis by simp
          qed  
          ultimately show ?thesis by linarith
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed
    moreover have ?thesis when Re_neg:"\<forall>t\<in>{0<..<1}. Re (g t) < Re z"
    proof -
      have "Re (winding_number g z) = 0"
      proof -
        have "\<forall>p\<in>path_image g. Re z \<ge> Re p"
        proof 
          fix p assume "p \<in> path_image g"
          then obtain t where "0\<le>t" "t\<le>1" "p = g t" unfolding path_image_def by auto
          have "Re z \<ge> Re (g t)"
            apply (rule continuous_le_on_closure[of "{0<..<1}" "\<lambda>t. Re (g t)" t "Re z",simplified])
            subgoal using valid_path_imp_path[OF \<open>valid_path g\<close>,unfolded path_def] 
              by (auto intro:continuous_intros)
            subgoal using \<open>0\<le>t\<close> \<open>t\<le>1\<close> by auto
            subgoal for x using that[rule_format,of x] by auto
            done
          then show "Re z \<ge> Re p" using \<open>p = g t\<close> by auto
        qed
        from Re_winding_number_half_left[OF this \<open>valid_path g\<close> \<open>z\<notin>path_image g\<close>] loop
        show ?thesis by auto
      qed
      moreover have "cindex_pathE g z = 0"
      proof -
        have "cindex_pathE g z = jumpF_pathstart g z - jumpF_pathfinish g z"
          using index_ends[OF _ \<open>valid_path g\<close>] Re_neq \<open>s=0\<close> by auto
        moreover have "jumpF_pathstart g z = jumpF_pathfinish g z" when "Re (g 0) \<noteq> Re z"
        proof -
          have "jumpF_pathstart g z = 0" 
            using jumpF_pathstart_eq_0[OF \<open>path g\<close>] that unfolding path_defs by auto
          moreover have "jumpF_pathfinish g z=0"
            using jumpF_pathfinish_eq_0[OF \<open>path g\<close>] that loop unfolding path_defs by auto 
          ultimately show ?thesis by auto
        qed
        moreover have "jumpF_pathstart g z = jumpF_pathfinish g z" when "Re (g 0) = Re z"  
        proof -
          have [simp]:"(fR has_sgnx - 1) (at_right 0)" 
            unfolding fR_def has_sgnx_def eventually_at_right
            apply (rule exI[where x=1])
            using Re_neg by auto
          have [simp]:"(fR has_sgnx - 1) (at_left 1)" 
            unfolding fR_def has_sgnx_def eventually_at_left
            apply (rule exI[where x=0])
            using Re_neg by auto
          have "fI 0\<noteq>0" 
          proof (rule ccontr)
            assume "\<not> fI 0 \<noteq> 0"
            then have "g 0 =z" using \<open>Re (g 0) = Re z\<close> 
              unfolding fI_def by (simp add: complex.expand)
            then show False using \<open>z \<notin> path_image g\<close> unfolding path_image_def by auto
          qed
          moreover have ?thesis when "fI 0>0"
          proof -
            have "jumpF_pathstart g z = - 1/2"
            proof -
              have "(LIM x at_right 0. fI x / fR x :> at_bot)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 0"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathstart_def fI_def fR_def jumpF_def by auto
            qed
            moreover have "jumpF_pathfinish g z = - 1/2"
            proof -
              have "fI 1>0" using loop that unfolding path_defs fI_def by auto
              then have "(LIM x at_left 1. fI x / fR x :> at_bot)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 1"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathfinish_def fI_def fR_def jumpF_def by auto
            qed  
            ultimately show ?thesis by simp
          qed
          moreover have ?thesis when "fI 0<0" 
          proof -
            have "jumpF_pathstart g z = 1/2"
            proof -
              have "(LIM x at_right 0. fI x / fR x :> at_top)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 0"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathstart_def fI_def fR_def jumpF_def by auto
            qed
            moreover have "jumpF_pathfinish g z = 1/2"
            proof -
              have "fI 1<0" using loop that unfolding path_defs fI_def by auto
              then have "(LIM x at_left 1. fI x / fR x :> at_top)"
                apply (subst filterlim_divide_at_bot_at_top_iff[of _ "fI 1"])
                using that fI fR[OF \<open>Re (g 0) = Re z\<close>] by simp_all
              then show ?thesis unfolding jumpF_pathfinish_def fI_def fR_def jumpF_def by auto
            qed  
            ultimately show ?thesis by simp
          qed  
          ultimately show ?thesis by linarith
        qed
        ultimately show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed  
    ultimately show ?thesis by auto
  qed
  moreover have ?goal when "s\<noteq>0"
  proof -
    have "Re (g s) = Re z" using \<open>s = 0 \<or> Re (g s) = Re z\<close> that by auto 
    define g' where "g' = shiftpath s g"
    have "2 * Re (winding_number g' z) = - cindex_pathE g' z"
    proof (rule winding_number_cindex_pathE_aux)
      show "Re (g' 1) = Re z" "Re (g' 0) = Re z"
        using \<open>Re (g s) = Re z\<close> \<open>s\<in>{0..<1}\<close> \<open>s\<noteq>0\<close> 
        unfolding g'_def shiftpath_def by simp_all
      show "valid_path g'" 
        using valid_path_shiftpath[OF \<open>valid_path g\<close> loop,of s,folded g'_def] \<open>s\<in>{0..<1}\<close>
        by auto
      show "z \<notin> path_image g'"
        using \<open>s \<in> {0..<1}\<close> assms(3) g'_def loop path_image_shiftpath by fastforce
      show "finite_ReZ_segments g' z"
        using finite_ReZ_segments_shiftpah[OF \<open>finite_ReZ_segments g z\<close> _ \<open>path g\<close> loop] \<open>s\<in>{0..<1}\<close>
        unfolding g'_def by auto
    qed
    moreover have "winding_number g' z = winding_number g z"
      unfolding g'_def
      apply (rule winding_number_shiftpath[OF \<open>path g\<close> \<open>z \<notin> path_image g\<close> loop])
      using \<open>s\<in>{0..<1}\<close> by auto
    moreover have "cindex_pathE g' z = cindex_pathE g z"
      unfolding g'_def
      apply (rule cindex_pathE_shiftpath[OF \<open>finite_ReZ_segments g z\<close> _ \<open>path g\<close> loop])
      using \<open>s\<in>{0..<1}\<close> by auto
    ultimately show ?thesis by auto
  qed
  ultimately have ?goal by auto
  moreover have "winding_number g z \<in> \<int>" 
    using integer_winding_number[OF _ loop \<open>z\<notin>path_image g\<close>] valid_path_imp_path[OF \<open>valid_path g\<close>]
    by auto
  ultimately show "winding_number g z = - cindex_pathE g z / 2"  
    by (metis add.right_neutral complex_eq complex_is_Int_iff mult_zero_right 
        nonzero_mult_div_cancel_left of_real_0 zero_neq_numeral)
qed
 
text \<open>REMARK: The usual statement of Cauchy's Index theorem (i.e. Analytic Theory of Polynomials 
  (2002): Theorem 11.1.3) is about the equality between the number of polynomial roots and
  the Cauchy index, which is the joint application of @{thm winding_number_cindex_pathE} and
  @{thm argument_principle}.\<close>  
  
end
  
  
