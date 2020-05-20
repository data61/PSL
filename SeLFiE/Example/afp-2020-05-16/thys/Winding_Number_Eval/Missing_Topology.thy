(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some useful lemmas in topology\<close>

theory Missing_Topology imports "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>Misc\<close>    
 
lemma open_times_image:
  fixes S::"'a::real_normed_field set"
  assumes "open S" "c\<noteq>0"
  shows "open (((*) c) ` S)" 
proof -
  let ?f = "\<lambda>x. x/c" and ?g="((*) c)"
  have "continuous_on UNIV ?f" using \<open>c\<noteq>0\<close> by (auto intro:continuous_intros)
  then have "open (?f -` S)" using \<open>open S\<close> by (auto elim:open_vimage)
  moreover have "?g ` S = ?f -` S" using \<open>c\<noteq>0\<close>
    apply auto
    using image_iff by fastforce
  ultimately show ?thesis by auto
qed   
 
lemma image_linear_greaterThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {x<..}) = (if c>0 then {c*x+b <..} else {..< c*x+b})"
using \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done

lemma image_linear_lessThan:
  fixes x::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "((\<lambda>x. c*x+b) ` {..<x}) = (if c>0 then {..<c*x+b} else {c*x+b<..})"
using \<open>c\<noteq>0\<close>
  apply (auto simp add:image_iff field_simps)    
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
  subgoal for y by (rule bexI[where x="(y-b)/c"],auto simp add:field_simps)
done    
 
lemma continuous_on_neq_split:
  fixes f :: "'a::linear_continuum_topology \<Rightarrow> 'b::linorder_topology"
  assumes "\<forall>x\<in>s. f x\<noteq>y" "continuous_on s f" "connected s"
  shows "(\<forall>x\<in>s. f x>y) \<or> (\<forall>x\<in>s. f x<y)" 
proof -
  { fix aa :: 'a and aaa :: 'a
    have "y \<notin> f ` s"
      using assms(1) by blast
    then have "(aa \<notin> s \<or> y < f aa) \<or> aaa \<notin> s \<or> f aaa < y"
      by (meson Topological_Spaces.connected_continuous_image assms(2) assms(3) 
          connectedD_interval image_eqI linorder_not_le) }
  then show ?thesis
    by blast
qed

lemma
  fixes f::"'a::linorder_topology \<Rightarrow> 'b::topological_space"
  assumes "continuous_on {a..b} f" "a<b"
  shows continuous_on_at_left:"continuous (at_left b) f" 
    and continuous_on_at_right:"continuous (at_right a) f"
proof -
  have "at b within {..a} = bot" 
  proof -
    have "closed {..a}" by auto
    then have "closure ({..a} - {b}) = {..a}" by (simp add: assms(2) not_le)
    then have "b\<notin>closure ({..a} - {b})" using \<open>a<b\<close> by auto
    then show ?thesis using at_within_eq_bot_iff by auto
  qed
  then have "(f \<longlongrightarrow> f b) (at b within {..a})" by auto
  moreover have "(f \<longlongrightarrow> f b) (at b within {a..b})"
    using assms unfolding continuous_on by auto
  moreover have "{..a} \<union> {a..b} = {..b}"
    using \<open>a<b\<close> by auto
  ultimately have "(f \<longlongrightarrow> f b) (at b within {..b})" 
    using Lim_Un[of f "f b" b "{..a}" "{a..b}"] by presburger
  then have "(f \<longlongrightarrow> f b) (at b within {..<b})"
    apply (elim tendsto_within_subset)
    by auto
  then show "continuous (at_left b) f" using continuous_within by auto
next
  have "at a within {b..} = bot" 
  proof -
    have "closed {b..}" by auto
    then have "closure ({b..} - {a}) = {b..}" by (simp add: assms(2) not_le)
    then have "a\<notin>closure ({b..} - {a})" using \<open>a<b\<close> by auto
    then show ?thesis using at_within_eq_bot_iff by auto
  qed
  then have "(f \<longlongrightarrow> f a) (at a within {b..})" by auto
  moreover have "(f \<longlongrightarrow> f a) (at a within {a..b})"
    using assms unfolding continuous_on by auto
  moreover have "{b..} \<union> {a..b} = {a..}"
    using \<open>a<b\<close> by auto
  ultimately have "(f \<longlongrightarrow> f a) (at a within {a..})" 
    using Lim_Un[of f "f a" a "{b..}" "{a..b}"] by presburger
  then have "(f \<longlongrightarrow> f a) (at a within {a<..})"
    apply (elim tendsto_within_subset)
    by auto
  then show "continuous (at_right a) f" using continuous_within by auto
qed 
  
subsection \<open>More about @{term eventually}\<close>    
    
lemma eventually_comp_filtermap:
    "eventually (P o f) F \<longleftrightarrow> eventually P (filtermap f F)"
  unfolding comp_def using eventually_filtermap by auto
 
lemma eventually_uminus_at_top_at_bot:
  fixes P::"'a::{ordered_ab_group_add,linorder} \<Rightarrow> bool"
  shows "eventually (P o uminus) at_bot \<longleftrightarrow> eventually P at_top"
    "eventually (P o uminus) at_top \<longleftrightarrow> eventually P at_bot"
  unfolding eventually_comp_filtermap
  by (fold at_top_mirror at_bot_mirror,auto)
    
lemma eventually_at_infinityI:
  fixes P::"'a::real_normed_vector \<Rightarrow> bool"
  assumes "\<And>x. c \<le> norm x \<Longrightarrow> P x"
  shows "eventually P at_infinity"  
unfolding eventually_at_infinity using assms by auto
   
lemma eventually_at_bot_linorderI:
  fixes c::"'a::linorder"
  assumes "\<And>x. x \<le> c \<Longrightarrow> P x"
  shows "eventually P at_bot"
  using assms by (auto simp: eventually_at_bot_linorder)     

lemma eventually_times_inverse_1:
  fixes f::"'a \<Rightarrow> 'b::{field,t2_space}"
  assumes "(f \<longlongrightarrow> c) F" "c\<noteq>0"
  shows "\<forall>\<^sub>F x in F. inverse (f x) * f x = 1"
proof -
  have "\<forall>\<^sub>F x in F. f x\<noteq>0" 
    using assms tendsto_imp_eventually_ne by blast
  then show ?thesis
    apply (elim eventually_mono)
    by auto
qed  
  
subsection \<open>More about @{term filtermap}\<close> 

lemma filtermap_linear_at_within:
  assumes "bij f" and cont: "isCont f a" and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (at a within S) = at (f a) within f`S"
  unfolding filter_eq_iff
proof safe
  fix P
  assume "eventually P (filtermap f (at a within S))"
  then obtain T where "open T" "a \<in> T" and impP:"\<forall>x\<in>T. x\<noteq>a \<longrightarrow> x\<in>S\<longrightarrow> P (f x)"
    by (auto simp: eventually_filtermap eventually_at_topological)
  then show "eventually P (at (f a) within f ` S)"
    unfolding eventually_at_topological
    apply (intro exI[of _ "f`T"])
    using \<open>bij f\<close> open_map by (metis bij_pointE imageE imageI)  
next
  fix P
  assume "eventually P (at (f a) within f ` S)"
  then obtain T1 where "open T1" "f a \<in> T1" and impP:"\<forall>x\<in>T1. x\<noteq>f a \<longrightarrow> x\<in>f`S\<longrightarrow> P (x)"
    unfolding eventually_at_topological by auto
  then obtain T2 where "open T2" "a \<in> T2" "(\<forall>x'\<in>T2. f x' \<in> T1)" 
    using cont[unfolded continuous_at_open,rule_format,of T1] by blast 
  then have "\<forall>x\<in>T2. x\<noteq>a \<longrightarrow> x\<in>S\<longrightarrow> P (f x)"
    using impP by (metis assms(1) bij_pointE imageI)
  then show "eventually P (filtermap f (at a within S))" 
    unfolding eventually_filtermap eventually_at_topological 
    apply (intro exI[of _ T2])
    using \<open>open T2\<close> \<open>a \<in> T2\<close> by auto
qed
  
lemma filtermap_at_bot_linear_eq:
  fixes c::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. x * c + b) at_bot = (if c>0 then at_bot else at_top)"
proof (cases "c>0")
  case True
  then have "filtermap (\<lambda>x. x * c + b) at_bot = at_bot" 
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_bot_linorder filterlim_at_bot
      by (auto simp add: field_simps)
    subgoal unfolding eventually_at_bot_linorder filterlim_at_bot
      by (metis mult.commute real_affinity_le)
    by auto
  then show ?thesis using \<open>c>0\<close> by auto
next
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  then have "filtermap (\<lambda>x. x * c + b) at_bot = at_top"
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_top_linorder filterlim_at_bot
      by (meson le_diff_eq neg_divide_le_eq)
    subgoal unfolding eventually_at_bot_linorder filterlim_at_top
      using \<open>c < 0\<close> by (meson False diff_le_eq le_divide_eq)
    by auto
  then show ?thesis using \<open>c<0\<close> by auto
qed  
  
lemma filtermap_linear_at_left:
  fixes c::"'a::{linordered_field,linorder_topology,real_normed_field}"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. c*x+b) (at_left x) = (if c>0 then at_left (c*x+b) else at_right (c*x+b))"
proof -
  let ?f = "\<lambda>x. c*x+b"
  have "filtermap (\<lambda>x. c*x+b) (at_left x) = (at (?f x) within ?f ` {..<x})"
  proof (subst filtermap_linear_at_within)
    show "bij ?f" using \<open>c\<noteq>0\<close> 
      by (auto intro!: o_bij[of "\<lambda>x. (x-b)/c"])
    show "isCont ?f x" by auto
    show "\<And>S. open S \<Longrightarrow> open (?f ` S)" 
      using open_times_image[OF _ \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
      by (simp add:image_image add.commute)
    show "at (?f x) within ?f ` {..<x} = at (?f x) within ?f ` {..<x}" by simp
  qed
  moreover have "?f ` {..<x} =  {..<?f x}" when "c>0" 
    using image_linear_lessThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  moreover have "?f ` {..<x} =  {?f x<..}" when "\<not> c>0" 
    using image_linear_lessThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  ultimately show ?thesis by auto
qed
    
lemma filtermap_linear_at_right:
  fixes c::"'a::{linordered_field,linorder_topology,real_normed_field}"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. c*x+b) (at_right x) = (if c>0 then at_right (c*x+b) else at_left (c*x+b))" 
proof -
  let ?f = "\<lambda>x. c*x+b"
  have "filtermap ?f (at_right x) = (at (?f x) within ?f ` {x<..})"
  proof (subst filtermap_linear_at_within)
    show "bij ?f" using \<open>c\<noteq>0\<close> 
      by (auto intro!: o_bij[of "\<lambda>x. (x-b)/c"])
    show "isCont ?f x" by auto
    show "\<And>S. open S \<Longrightarrow> open (?f ` S)" 
      using open_times_image[OF _ \<open>c\<noteq>0\<close>,THEN open_translation,of _ b]  
      by (simp add:image_image add.commute)
    show "at (?f x) within ?f ` {x<..} = at (?f x) within ?f ` {x<..}" by simp
  qed
  moreover have "?f ` {x<..} =  {?f x<..}" when "c>0" 
    using image_linear_greaterThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  moreover have "?f ` {x<..} =  {..<?f x}" when "\<not> c>0" 
    using image_linear_greaterThan[OF \<open>c\<noteq>0\<close>,of b x] that by auto
  ultimately show ?thesis by auto
qed
 
lemma filtermap_at_top_linear_eq:
  fixes c::"'a::linordered_field"
  assumes "c\<noteq>0"
  shows "filtermap (\<lambda>x. x * c + b) at_top = (if c>0 then at_top else at_bot)"
proof (cases "c>0")
  case True
  then have "filtermap (\<lambda>x. x * c + b) at_top = at_top" 
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_top_linorder filterlim_at_top 
      by (meson le_diff_eq pos_le_divide_eq)
    subgoal unfolding eventually_at_top_linorder filterlim_at_top
      apply auto
      by (metis mult.commute real_le_affinity) 
    by auto
  then show ?thesis using \<open>c>0\<close> by auto
next
  case False
  then have "c<0" using \<open>c\<noteq>0\<close> by auto
  then have "filtermap (\<lambda>x. x * c + b) at_top = at_bot"
    apply (intro filtermap_fun_inverse[of "\<lambda>x. (x-b) / c"])
    subgoal unfolding eventually_at_bot_linorder filterlim_at_top
      by (auto simp add: field_simps)
    subgoal unfolding eventually_at_top_linorder filterlim_at_bot
      by (meson le_diff_eq neg_divide_le_eq)
    by auto
  then show ?thesis using \<open>c<0\<close> by auto
qed

  
lemma filtermap_nhds_open_map:
  assumes cont: "isCont f a"
    and open_map: "\<And>S. open S \<Longrightarrow> open (f`S)"
  shows "filtermap f (nhds a) = nhds (f a)"
  unfolding filter_eq_iff
proof safe
  fix P
  assume "eventually P (filtermap f (nhds a))"
  then obtain S where "open S" "a \<in> S" "\<forall>x\<in>S. P (f x)"
    by (auto simp: eventually_filtermap eventually_nhds)
  then show "eventually P (nhds (f a))"
    unfolding eventually_nhds 
    apply (intro exI[of _ "f`S"]) 
    by (auto intro!: open_map)
qed (metis filterlim_iff tendsto_at_iff_tendsto_nhds isCont_def eventually_filtermap cont)
  
subsection \<open>More about @{term filterlim}\<close>
  
lemma filterlim_at_infinity_times:
  fixes f :: "'a \<Rightarrow> 'b::real_normed_field"
  assumes "filterlim f at_infinity F" "filterlim g at_infinity F"
  shows "filterlim (\<lambda>x. f x * g x) at_infinity F"  
proof -
  have "((\<lambda>x. inverse (f x) * inverse (g x)) \<longlongrightarrow> 0 * 0) F"
    by (intro tendsto_mult tendsto_inverse assms filterlim_compose[OF tendsto_inverse_0])
  then have "filterlim (\<lambda>x. inverse (f x) * inverse (g x)) (at 0) F"
    unfolding filterlim_at using assms
    by (auto intro: filterlim_at_infinity_imp_eventually_ne tendsto_imp_eventually_ne eventually_conj)
  then show ?thesis
    by (subst filterlim_inverse_at_iff[symmetric]) simp_all
qed   
  
lemma filterlim_at_top_at_bot[elim]:
  fixes f::"'a \<Rightarrow> 'b::unbounded_dense_linorder" and F::"'a filter"
  assumes top:"filterlim f at_top F" and bot: "filterlim f at_bot F" and "F\<noteq>bot"
  shows False
proof -
  obtain c::'b where True by auto
  have "\<forall>\<^sub>F x in F. c < f x" 
    using top unfolding filterlim_at_top_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x < c" 
    using bot unfolding filterlim_at_bot_dense by auto
  ultimately have "\<forall>\<^sub>F x in F. c < f x \<and> f x < c" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed  

lemma filterlim_at_top_nhds[elim]:      
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_top F" and tendsto: "(f \<longlongrightarrow> c) F" and "F\<noteq>bot"
  shows False
proof -
  obtain c'::'b where "c'>c" using gt_ex by blast
  have "\<forall>\<^sub>F x in F. c' < f x" 
    using top unfolding filterlim_at_top_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x < c'" 
    using order_tendstoD[OF tendsto,of c'] \<open>c'>c\<close> by auto
  ultimately have "\<forall>\<^sub>F x in F. c' < f x \<and> f x < c'" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed

lemma filterlim_at_bot_nhds[elim]:      
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_bot F" and tendsto: "(f \<longlongrightarrow> c) F" and "F\<noteq>bot"
  shows False
proof -
  obtain c'::'b where "c'<c" using lt_ex by blast
  have "\<forall>\<^sub>F x in F. c' > f x" 
    using top unfolding filterlim_at_bot_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x > c'" 
    using order_tendstoD[OF tendsto,of c'] \<open>c'<c\<close> by auto
  ultimately have "\<forall>\<^sub>F x in F. c' < f x \<and> f x < c'" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed  
  
lemma filterlim_at_top_linear_iff:
  fixes f::"'a::linordered_field \<Rightarrow> 'b"
  assumes "c\<noteq>0"
  shows "(LIM x at_top. f (x * c + b) :> F2) \<longleftrightarrow> (if c>0 then (LIM x at_top. f x :> F2) 
            else (LIM x at_bot. f x :> F2))"
  unfolding filterlim_def
  apply (subst filtermap_filtermap[of f "\<lambda>x. x * c + b",symmetric])
  using assms by (auto simp add:filtermap_at_top_linear_eq)
    
lemma filterlim_at_bot_linear_iff:
  fixes f::"'a::linordered_field \<Rightarrow> 'b"
  assumes "c\<noteq>0"
  shows "(LIM x at_bot. f (x * c + b) :> F2) \<longleftrightarrow> (if c>0 then (LIM x at_bot. f x :> F2) 
            else (LIM x at_top. f x :> F2)) "
  unfolding filterlim_def 
  apply (subst filtermap_filtermap[of f "\<lambda>x. x * c + b",symmetric])
  using assms by (auto simp add:filtermap_at_bot_linear_eq)      
  
  
lemma filterlim_tendsto_add_at_top_iff:
  assumes f: "(f \<longlongrightarrow> c) F"
  shows "(LIM x F. (f x + g x :: real) :> at_top) \<longleftrightarrow> (LIM x F. g x :> at_top)"
proof     
  assume "LIM x F. f x + g x :> at_top" 
  moreover have "((\<lambda>x. - f x) \<longlongrightarrow> - c) F"
    using f by (intro tendsto_intros,simp)
  ultimately show "filterlim g at_top F" using filterlim_tendsto_add_at_top 
    by fastforce
qed (auto simp add:filterlim_tendsto_add_at_top[OF f])    
    
  
lemma filterlim_tendsto_add_at_bot_iff:
  fixes c::real
  assumes f: "(f \<longlongrightarrow> c) F"
  shows "(LIM x F. f x + g x :> at_bot) \<longleftrightarrow> (LIM x F. g x :> at_bot)" 
proof -
  have "(LIM x F. f x + g x :> at_bot) 
        \<longleftrightarrow>  (LIM x F. - f x + (- g x)  :> at_top)"
    apply (subst filterlim_uminus_at_top)
    by (rule filterlim_cong,auto)
  also have "... = (LIM x F. - g x  :> at_top)"
    apply (subst filterlim_tendsto_add_at_top_iff[of _ "-c"])
    by (auto intro:tendsto_intros simp add:f)
  also have "... = (LIM x F. g x  :> at_bot)"
    apply (subst filterlim_uminus_at_top)
    by (rule filterlim_cong,auto)
  finally show ?thesis .
qed
  
lemma tendsto_inverse_0_at_infinity: 
    "LIM x F. f x :> at_infinity \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) \<longlongrightarrow> 0) F"
  by (metis filterlim_at filterlim_inverse_at_iff)

lemma filterlim_at_infinity_divide_iff:
  fixes f::"'a \<Rightarrow> 'b::real_normed_field"
  assumes "(f \<longlongrightarrow> c) F" "c\<noteq>0"
  shows "(LIM x F. f x / g x :> at_infinity) \<longleftrightarrow> (LIM x F. g x :> at 0)"
proof 
  assume asm:"LIM x F. f x / g x :> at_infinity"
  have "LIM x F. inverse (f x) * (f x / g x) :> at_infinity"
    apply (rule tendsto_mult_filterlim_at_infinity[of _ "inverse c", OF _ _ asm])
    by (auto simp add: assms(1) assms(2) tendsto_inverse)
  then have "LIM x F. inverse (g x) :> at_infinity"
    apply (elim filterlim_mono_eventually)
    using eventually_times_inverse_1[OF assms] 
    by (auto elim:eventually_mono simp add:field_simps)
  then show "filterlim g (at 0) F" using filterlim_inverse_at_iff[symmetric] by force 
next
  assume "filterlim g (at 0) F" 
  then have "filterlim (\<lambda>x. inverse (g x)) at_infinity F"
    using filterlim_compose filterlim_inverse_at_infinity by blast
  then have "LIM x F. f x * inverse (g x) :> at_infinity"
    using tendsto_mult_filterlim_at_infinity[OF assms, of "\<lambda>x. inverse(g x)"] 
    by simp
  then show "LIM x F. f x / g x :> at_infinity" by (simp add: divide_inverse)
qed  
  
lemma filterlim_tendsto_pos_mult_at_top_iff:
  fixes f::"'a \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> c) F" and "0 < c"
  shows "(LIM x F. (f x * g x) :> at_top) \<longleftrightarrow> (LIM x F. g x :> at_top)"
proof 
  assume "filterlim g at_top F"
  then show "LIM x F. f x * g x :> at_top" 
    using filterlim_tendsto_pos_mult_at_top[OF assms] by auto
next
  assume asm:"LIM x F. f x * g x :> at_top"
  have "((\<lambda>x. inverse (f x)) \<longlongrightarrow> inverse c) F" 
    using tendsto_inverse[OF assms(1)] \<open>0<c\<close> by auto
  moreover have "inverse c >0" using assms(2) by auto
  ultimately have "LIM x F. inverse (f x) * (f x * g x) :> at_top"
    using filterlim_tendsto_pos_mult_at_top[OF _ _ asm,of "\<lambda>x. inverse (f x)" "inverse c"] by auto
  then show "LIM x F. g x :> at_top"
    apply (elim filterlim_mono_eventually)
      apply simp_all[2]
    using eventually_times_inverse_1[OF assms(1)] \<open>c>0\<close> eventually_mono by fastforce
qed  

lemma filterlim_tendsto_pos_mult_at_bot_iff:
  fixes c :: real
  assumes "(f \<longlongrightarrow> c) F" "0 < c" 
  shows "(LIM x F. f x * g x :> at_bot) \<longleftrightarrow> filterlim g at_bot F"
  using filterlim_tendsto_pos_mult_at_top_iff[OF assms(1,2), of "\<lambda>x. - g x"] 
  unfolding filterlim_uminus_at_bot by simp    

lemma filterlim_tendsto_neg_mult_at_top_iff:
  fixes f::"'a \<Rightarrow> real"
  assumes "(f \<longlongrightarrow> c) F" and "c < 0"
  shows "(LIM x F. (f x * g x) :> at_top) \<longleftrightarrow> (LIM x F. g x :> at_bot)"  
proof -
  have "(LIM x F. f x * g x :> at_top) = (LIM x F. - g x :> at_top)"
    apply (rule filterlim_tendsto_pos_mult_at_top_iff[of "\<lambda>x. - f x" "-c" F "\<lambda>x. - g x", simplified])
    using assms by (auto intro: tendsto_intros )
  also have "... = (LIM x F. g x :> at_bot)" 
    using filterlim_uminus_at_bot[symmetric] by auto
  finally show ?thesis .
qed

lemma filterlim_tendsto_neg_mult_at_bot_iff:
  fixes c :: real
  assumes "(f \<longlongrightarrow> c) F" "0 > c" 
  shows "(LIM x F. f x * g x :> at_bot) \<longleftrightarrow> filterlim g at_top F"
  using filterlim_tendsto_neg_mult_at_top_iff[OF assms(1,2), of "\<lambda>x. - g x"] 
  unfolding filterlim_uminus_at_top by simp    

lemma Lim_add:
  fixes f g::"_ \<Rightarrow> 'a::{t2_space,topological_monoid_add}"
  assumes "\<exists>y. (f \<longlongrightarrow> y) F" and "\<exists>y. (g \<longlongrightarrow> y) F" and "F\<noteq>bot"
  shows "Lim F f + Lim F g = Lim F (\<lambda>x. f x+g x)"
  apply (rule tendsto_Lim[OF \<open>F\<noteq>bot\<close>, symmetric])
  apply (auto intro!:tendsto_eq_intros)
  using assms tendsto_Lim by blast+

(*
lemma filterlim_at_top_tendsto[elim]:
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_top F" and tendsto: "(f \<longlongrightarrow> c) F" 
          and "F\<noteq>bot"
  shows False
proof -
  obtain cc where "cc>c" using gt_ex by blast
  have "\<forall>\<^sub>F x in F. cc < f x" 
    using top unfolding filterlim_at_top_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x < cc" 
    using tendsto order_tendstoD(2)[OF _ \<open>cc>c\<close>] by auto
  ultimately have "\<forall>\<^sub>F x in F. cc < f x \<and> f x < cc" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed

lemma filterlim_at_bot_tendsto[elim]:
  fixes f::"'a \<Rightarrow> 'b::{unbounded_dense_linorder,order_topology}" and F::"'a filter"
  assumes top:"filterlim f at_bot F" and tendsto: "(f \<longlongrightarrow> c) F" 
          and "F\<noteq>bot"
  shows False
proof -
  obtain cc where "cc<c" using lt_ex by blast
  have "\<forall>\<^sub>F x in F. cc > f x" 
    using top unfolding filterlim_at_bot_dense by auto
  moreover have "\<forall>\<^sub>F x in F. f x > cc" 
    using tendsto order_tendstoD(1)[OF _ \<open>cc<c\<close>] by auto
  ultimately have "\<forall>\<^sub>F x in F. cc < f x \<and> f x < cc" 
    using eventually_conj by auto
  then have "\<forall>\<^sub>F x in F. False" by (auto elim:eventually_mono)
  then show False using \<open>F\<noteq>bot\<close> by auto
qed
*)
  
subsection \<open>Isolate and discrete\<close>  
  
definition (in topological_space) isolate:: "'a \<Rightarrow> 'a set \<Rightarrow> bool"  (infixr "isolate" 60)
  where "x isolate S \<longleftrightarrow> (x\<in>S \<and> (\<exists>T. open T \<and> T \<inter> S = {x}))"  
    
definition (in topological_space) discrete:: "'a set \<Rightarrow> bool" 
  where "discrete S \<longleftrightarrow> (\<forall>x\<in>S. x isolate S)"  
    
definition (in metric_space) uniform_discrete :: "'a set \<Rightarrow> bool" where
  "uniform_discrete S \<longleftrightarrow> (\<exists>e>0. \<forall>x\<in>S. \<forall>y\<in>S. dist x y < e \<longrightarrow> x = y)"
  
lemma uniformI1:
  assumes "e>0" "\<And>x y. \<lbrakk>x\<in>S;y\<in>S;dist x y<e\<rbrakk> \<Longrightarrow> x =y "
  shows "uniform_discrete S"  
unfolding uniform_discrete_def using assms by auto

lemma uniformI2:
  assumes "e>0" "\<And>x y. \<lbrakk>x\<in>S;y\<in>S;x\<noteq>y\<rbrakk> \<Longrightarrow> dist x y\<ge>e "
  shows "uniform_discrete S"  
unfolding uniform_discrete_def using assms not_less by blast
  
lemma isolate_islimpt_iff:"(x isolate S) \<longleftrightarrow> (\<not> (x islimpt S) \<and> x\<in>S)"
  unfolding isolate_def islimpt_def by auto
  
lemma isolate_dist_Ex_iff:
  fixes x::"'a::metric_space"
  shows "x isolate S \<longleftrightarrow> (x\<in>S \<and> (\<exists>e>0. \<forall>y\<in>S. dist x y < e \<longrightarrow> y=x))"
unfolding isolate_islimpt_iff islimpt_approachable by (metis dist_commute)
  
lemma discrete_empty[simp]: "discrete {}"
  unfolding discrete_def by auto

lemma uniform_discrete_empty[simp]: "uniform_discrete {}"
  unfolding uniform_discrete_def by (simp add: gt_ex)
  
lemma isolate_insert: 
  fixes x :: "'a::t1_space"
  shows "x isolate (insert a S) \<longleftrightarrow> x isolate S \<or> (x=a \<and> \<not> (x islimpt S))"
by (meson insert_iff islimpt_insert isolate_islimpt_iff)
    
(*
TODO. 
Other than 

  uniform_discrete S \<longrightarrow> discrete S
  uniform_discrete S \<longrightarrow> closed S

, we should be able to prove

  discrete S \<and> closed S \<longrightarrow> uniform_discrete S

but the proof (based on Tietze Extension Theorem) seems not very trivial to me. Informal proofs can be found in

http://topology.auburn.edu/tp/reprints/v30/tp30120.pdf
http://msp.org/pjm/1959/9-2/pjm-v9-n2-p19-s.pdf
*)  
  
lemma uniform_discrete_imp_closed:
  "uniform_discrete S \<Longrightarrow> closed S" 
  by (meson discrete_imp_closed uniform_discrete_def) 
    
lemma uniform_discrete_imp_discrete:
  "uniform_discrete S \<Longrightarrow> discrete S"
  by (metis discrete_def isolate_dist_Ex_iff uniform_discrete_def)
  
lemma isolate_subset:"x isolate S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> x\<in>T \<Longrightarrow> x isolate T"
  unfolding isolate_def by fastforce

lemma discrete_subset[elim]: "discrete S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> discrete T"
  unfolding discrete_def using islimpt_subset isolate_islimpt_iff by blast
    
lemma uniform_discrete_subset[elim]: "uniform_discrete S \<Longrightarrow> T \<subseteq> S \<Longrightarrow> uniform_discrete T"
  by (meson subsetD uniform_discrete_def)
        
lemma continuous_on_discrete: "discrete S \<Longrightarrow> continuous_on S f" 
  unfolding continuous_on_topological by (metis discrete_def islimptI isolate_islimpt_iff)
   
(* Is euclidean_space really necessary?*)    
lemma uniform_discrete_insert:
  fixes S :: "'a::euclidean_space set"
  shows "uniform_discrete (insert a S) \<longleftrightarrow> uniform_discrete S"
proof 
  assume asm:"uniform_discrete S" 
  let ?thesis = "uniform_discrete (insert a S)"
  have ?thesis when "a\<in>S" using that asm by (simp add: insert_absorb)
  moreover have ?thesis when "S={}" using that asm by (simp add: uniform_discrete_def)
  moreover have ?thesis when "a\<notin>S" "S\<noteq>{}"
  proof -
    obtain e1 where "e1>0" and e1_dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist y x < e1 \<longrightarrow> y = x"
      using asm unfolding uniform_discrete_def by auto
    define e2 where "e2 \<equiv> min (setdist {a} S) e1"
    have "closed S" using asm uniform_discrete_imp_closed by auto
    then have "e2>0" by (simp add: \<open>0 < e1\<close> e2_def setdist_gt_0_compact_closed that(1) that(2))
    moreover have "x = y" when "x\<in>insert a S" "y\<in>insert a S" "dist x y < e2 " for x y
    proof -
      have ?thesis when "x=a" "y=a" using that by auto
      moreover have ?thesis when "x=a" "y\<in>S"
        using that setdist_le_dist[of x "{a}" y S] \<open>dist x y < e2\<close> unfolding e2_def
        by fastforce
      moreover have ?thesis when "y=a" "x\<in>S"
        using that setdist_le_dist[of y "{a}" x S] \<open>dist x y < e2\<close> unfolding e2_def
        by (simp add: dist_commute)
      moreover have ?thesis when "x\<in>S" "y\<in>S"
        using e1_dist[rule_format, OF that] \<open>dist x y < e2\<close> unfolding e2_def
        by (simp add: dist_commute)
      ultimately show ?thesis using that by auto
    qed
    ultimately show ?thesis unfolding uniform_discrete_def by meson
  qed
  ultimately show ?thesis by auto
qed (simp add: subset_insertI uniform_discrete_subset)
    
lemma discrete_compact_finite_iff:
  fixes S :: "'a::t1_space set"
  shows "discrete S \<and> compact S \<longleftrightarrow> finite S"
proof 
  assume "finite S"
  then have "compact S" using finite_imp_compact by auto
  moreover have "discrete S"
    unfolding discrete_def using isolate_islimpt_iff islimpt_finite[OF \<open>finite S\<close>] by auto 
  ultimately show "discrete S \<and> compact S" by auto
next
  assume "discrete S \<and> compact S"
  then show "finite S" 
    by (meson discrete_def Heine_Borel_imp_Bolzano_Weierstrass isolate_islimpt_iff order_refl)
qed
  
lemma uniform_discrete_finite_iff:
  fixes S :: "'a::heine_borel set"
  shows "uniform_discrete S \<and> bounded S \<longleftrightarrow> finite S"
proof 
  assume "uniform_discrete S \<and> bounded S"
  then have "discrete S" "compact S"
    using uniform_discrete_imp_discrete uniform_discrete_imp_closed compact_eq_bounded_closed
    by auto
  then show "finite S" using discrete_compact_finite_iff by auto
next
  assume asm:"finite S"
  let ?thesis = "uniform_discrete S \<and> bounded S"
  have ?thesis when "S={}" using that by auto
  moreover have ?thesis when "S\<noteq>{}"
  proof -
    have "\<forall>x. \<exists>d>0. \<forall>y\<in>S. y \<noteq> x \<longrightarrow> d \<le> dist x y"
      using finite_set_avoid[OF \<open>finite S\<close>] by auto
    then obtain f where f_pos:"f x>0" 
        and f_dist: "\<forall>y\<in>S. y \<noteq> x \<longrightarrow> f x \<le> dist x y"
        if "x\<in>S" for x 
      by metis
    define f_min where "f_min \<equiv> Min (f ` S)" 
    have "f_min > 0"
      unfolding f_min_def 
      by (simp add: asm f_pos that)
    moreover have "\<forall>x\<in>S. \<forall>y\<in>S. f_min > dist x y \<longrightarrow> x=y"
      using f_dist unfolding f_min_def 
      by (metis Min_gr_iff all_not_in_conv asm dual_order.irrefl eq_iff finite_imageI imageI 
          less_eq_real_def)
    ultimately have "uniform_discrete S" 
      unfolding uniform_discrete_def by auto
    moreover have "bounded S" using \<open>finite S\<close> by auto
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis by blast
qed
  
lemma uniform_discrete_image_scale:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
  assumes "uniform_discrete S" and dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist x y = c * dist (f x) (f y)"
  shows "uniform_discrete (f ` S)"  
proof -
  have ?thesis when "S={}" using that by auto
  moreover have ?thesis when "S\<noteq>{}" "c\<le>0"
  proof -
    obtain x1 where "x1\<in>S" using \<open>S\<noteq>{}\<close> by auto
    have ?thesis when "S-{x1} = {}"
    proof -
      have "S={x1}" using that \<open>S\<noteq>{}\<close> by auto
      then show ?thesis using uniform_discrete_insert[of "f x1"] by auto
    qed
    moreover have ?thesis when "S-{x1} \<noteq> {}"
    proof -
      obtain x2 where "x2\<in>S-{x1}" using \<open>S-{x1} \<noteq> {}\<close> by auto
      then have "x2\<in>S" "x1\<noteq>x2" by auto
      then have "dist x1 x2 > 0" by auto
      moreover have "dist x1 x2 = c * dist (f x1) (f x2)"
        using dist[rule_format, OF \<open>x1\<in>S\<close> \<open>x2\<in>S\<close>] .
      moreover have "dist (f x2) (f x2) \<ge> 0" by auto
      ultimately have False using \<open>c\<le>0\<close> by (simp add: zero_less_mult_iff)
      then show ?thesis by auto
    qed
    ultimately show ?thesis by auto
  qed
  moreover have ?thesis when "S\<noteq>{}" "c>0"
  proof -
    obtain e1 where "e1>0" and e1_dist:"\<forall>x\<in>S. \<forall>y\<in>S. dist y x < e1 \<longrightarrow> y = x"
      using \<open>uniform_discrete S\<close> unfolding uniform_discrete_def by auto
    define e where "e= e1/c"
    have "x1 = x2" when "x1\<in> f ` S" "x2\<in> f ` S" "dist x1 x2 < e " for x1 x2 
    proof -
      obtain y1 where y1:"y1\<in>S" "x1=f y1" using \<open>x1\<in> f ` S\<close> by auto
      obtain y2 where y2:"y2\<in>S" "x2=f y2" using \<open>x2\<in> f ` S\<close> by auto    
      have "dist y1 y2 < e1"
        using dist[rule_format, OF y1(1) y2(1)] \<open>c>0\<close> \<open>dist x1 x2 < e\<close> unfolding e_def
        apply (fold y1(2) y2(2))
        by (auto simp add:divide_simps mult.commute) 
      then have "y1=y2"    
        using e1_dist[rule_format, OF y2(1) y1(1)] by simp
      then show "x1=x2" using y1(2) y2(2) by auto
    qed
    moreover have "e>0" using \<open>e1>0\<close> \<open>c>0\<close> unfolding e_def by auto
    ultimately show ?thesis unfolding uniform_discrete_def by meson
  qed
  ultimately show ?thesis by fastforce
qed
 

  
end
