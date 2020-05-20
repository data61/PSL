(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Evaluate winding numbers by calculating Cauchy indices\<close>

theory Winding_Number_Eval imports 
  Cauchy_Index_Theorem 
  "HOL-Eisbach.Eisbach_Tools"
begin
  
subsection \<open>Misc\<close>

lemma not_on_closed_segmentI:
  fixes z::"'a::euclidean_space"
  assumes "norm (z - a) *\<^sub>R (b - z) \<noteq> norm (b - z) *\<^sub>R (z - a)"
  shows "z \<notin> closed_segment a b"
  using assms by (auto simp add:between_mem_segment[symmetric] between_norm)

lemma not_on_closed_segmentI_complex:    
  fixes z::"complex"
  assumes "(Re b - Re z) * (Im z - Im a) \<noteq> (Im b - Im z) * (Re z - Re a)"
  shows "z \<notin> closed_segment a b"
proof (cases "z\<noteq>a \<and> z\<noteq>b")
  case True
  then have "cmod (z - a)\<noteq>0" "cmod (b - z)\<noteq>0" by auto
  then have "(Re b - Re z) * (Im z - Im a) = (Im b - Im z) * (Re z - Re a)" when 
    "cmod (z - a) * (Re b - Re z) = cmod (b - z) * (Re z - Re a)"
    "cmod (z - a) * (Im b - Im z) = cmod (b - z) * (Im z - Im a)"
    using that by algebra
  then show ?thesis using assms
    apply (intro not_on_closed_segmentI)
    by (auto simp add:scaleR_complex.ctr simp del:Complex_eq)
next
  case False
  then have "(Re b - Re z) * (Im z - Im a) = (Im b - Im z) * (Re z - Re a)" by auto
  then have False using assms by auto
  then show ?thesis by auto
qed

subsection \<open>finite intersection with the two axes\<close>

definition finite_axes_cross::"(real \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> bool" where
  "finite_axes_cross g z = finite {t. (Re (g t-z) = 0 \<or> Im (g t-z) = 0) \<and> 0 \<le> t \<and> t \<le> 1}"

lemma finite_cross_intros:
  "\<lbrakk>Re a\<noteq>Re z \<or> Re b \<noteq>Re z; Im a\<noteq>Im z \<or> Im b\<noteq>Im z\<rbrakk>\<Longrightarrow>finite_axes_cross (linepath a b) z"
  "\<lbrakk>st \<noteq> tt; r \<noteq> 0\<rbrakk> \<Longrightarrow> finite_axes_cross (part_circlepath z0 r st tt) z"
  "\<lbrakk>finite_axes_cross g1 z;finite_axes_cross g2 z\<rbrakk> \<Longrightarrow> finite_axes_cross (g1+++g2) z"
proof -
  assume asm:"Re a\<noteq>Re z \<or> Re b \<noteq>Re z" "Im a\<noteq>Im z \<or> Im b\<noteq>Im z"
  let ?S1="{t. Re (linepath a b t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?S2="{t. Im (linepath a b t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  have "finite ?S1" 
    using linepath_half_finite_inter[of a "Complex 1 0" "Re z" b] asm(1) 
    by (auto simp add:inner_complex_def)
  moreover have "finite ?S2"
    using linepath_half_finite_inter[of a "Complex 0 1" "Im z" b] asm(2) 
    by (auto simp add:inner_complex_def)
  moreover have "{t. (Re (linepath a b t-z) = 0 \<or> Im (linepath a b t-z) = 0) \<and> 0 \<le> t \<and> t \<le> 1} 
      = ?S1 \<union> ?S2"
    by fast
  ultimately show "finite_axes_cross (linepath a b) z"
    unfolding finite_axes_cross_def by force
next
  assume asm: "st \<noteq>tt" "r\<noteq>0"
  let ?S1="{t. Re (part_circlepath z0 r st tt t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?S2="{t. Im (part_circlepath z0 r st tt t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  have "finite ?S1"
    using part_circlepath_half_finite_inter[of st tt r "Complex 1 0" z0 "Re z"] asm 
    by (auto simp add:inner_complex_def Complex_eq_0)
  moreover have "finite ?S2"
    using part_circlepath_half_finite_inter[of st tt r "Complex 0 1" z0 "Im z"] asm 
    by (auto simp add:inner_complex_def Complex_eq_0)
  moreover have "{t. (Re (part_circlepath z0 r st tt t-z) = 0 
      \<or> Im (part_circlepath z0 r st tt t-z) = 0) \<and> 0 \<le> t \<and> t \<le> 1} = ?S1 \<union> ?S2"
    by fast
  ultimately show "finite_axes_cross (part_circlepath z0 r st tt) z" 
    unfolding finite_axes_cross_def by auto
next
  assume asm:"finite_axes_cross g1 z" "finite_axes_cross g2 z"
  let ?g1R="{t. Re (g1 t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?g1I="{t. Im (g1 t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?g2R="{t. Re (g2 t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?g2I="{t. Im (g2 t-z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  have "finite ?g1R" "finite ?g1I"
  proof -
    have "{t. (Re (g1 t - z) = 0 \<or> Im (g1 t - z) = 0) \<and> 0 \<le> t \<and> t \<le> 1} = ?g1R \<union> ?g1I"
      by force
    then have "finite (?g1R \<union> ?g1I)"
      using asm(1) unfolding finite_axes_cross_def by auto
    then show "finite ?g1R" "finite ?g1I" by blast+
  qed
  have "finite ?g2R" "finite ?g2I" 
  proof -
    have "{t. (Re (g2 t - z) = 0 \<or> Im (g2 t - z) = 0) \<and> 0 \<le> t \<and> t \<le> 1} = ?g2R \<union> ?g2I"
      by force
    then have "finite (?g2R \<union> ?g2I)"
      using asm(2) unfolding finite_axes_cross_def by auto
    then show "finite ?g2R" "finite ?g2I" by blast+
  qed
  let ?S1 = "{t. Re ((g1 +++ g2) t - z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  and ?S2 = "{t. Im ((g1 +++ g2) t - z) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
  have "finite ?S1"  
    using finite_half_joinpaths_inter[of g1 "Complex 1 0" "Re z" g2,simplified] 
      \<open>finite ?g1R\<close> \<open>finite ?g2R\<close>
    by (auto simp add:inner_complex_def)
  moreover have "finite ?S2"  
    using finite_half_joinpaths_inter[of g1 "Complex 0 1" "Im z" g2,simplified] 
      \<open>finite ?g1I\<close> \<open>finite ?g2I\<close>
    by (auto simp add:inner_complex_def)
  moreover have "{t. (Re ((g1 +++ g2) t - z) = 0 \<or> Im ((g1 +++ g2) t - z) = 0) \<and> 0 \<le> t \<and> t \<le> 1}
        = ?S1 \<union> ?S2" 
    by force
  ultimately show "finite_axes_cross (g1 +++ g2) z"
    unfolding finite_axes_cross_def 
    by auto
qed

lemma cindex_path_joinpaths:
  assumes "finite_axes_cross g1 z" "finite_axes_cross g2 z"
    and "path g1" "path g2" "pathfinish g1 = pathstart g2" "pathfinish g1\<noteq>z" 
  shows "cindex_path (g1+++g2) z = cindex_path g1 z + jumpF_pathstart g2 z 
            - jumpF_pathfinish g1 z  + cindex_path g2 z"
proof -
  define h12 where "h12 = (\<lambda>t. Im ((g1+++g2) t - z) / Re ((g1+++g2) t - z))"
  let ?h = "\<lambda>g. \<lambda>t. Im (g t - z) / Re (g t - z)"
  have "cindex_path (g1+++g2) z = cindex 0 1 h12"
    unfolding cindex_path_def h12_def by simp
  also have "... = cindex 0 (1/2) h12 + jump h12 (1/2) + cindex (1/2) 1 h12"
  proof (rule cindex_combine)
    have "finite_axes_cross (g1+++g2) z" using assms by (auto intro:finite_cross_intros)
    then have "finite {t. Re ((g1+++g2) t - z) = 0 \<and> 0\<le>t \<and> t\<le>1}" 
      unfolding finite_axes_cross_def by (auto elim:rev_finite_subset)
    moreover have " jump h12 t = 0" when "Re ((g1 +++ g2) t - z) \<noteq> 0" "0 < t" "t < 1" for t 
      apply (rule jump_Im_divide_Re_0[of "\<lambda>t. (g1+++g2) t- z",folded h12_def,OF _ that])
      using assms by (auto intro:path_offset)
    ultimately show "finite {x. jump h12 x \<noteq> 0 \<and> 0 < x \<and> x < 1}" 
      apply (elim rev_finite_subset)
      by auto
  qed auto
  also have "... = cindex_path g1 z + jumpF_pathstart g2 z  
      - jumpF_pathfinish g1 z  + cindex_path g2 z"
  proof -
    have "jump h12 (1/2) =  jumpF_pathstart g2 z -  jumpF_pathfinish g1 z  "
    proof -
      have "jump h12 (1 / 2) = jumpF h12 (at_right (1 / 2)) - jumpF h12 (at_left (1 / 2))"
      proof (cases "Re ((g1+++g2) (1/2) - z) = 0")
        case False
        have "jump h12 (1 / 2) = 0"
          unfolding h12_def
          apply (rule jump_Im_divide_Re_0)
          using assms False by (auto intro:path_offset)
        moreover have "jumpF h12 (at_right (1/2)) = 0"
          unfolding h12_def 
          apply (intro jumpF_im_divide_Re_0)
          subgoal using assms by (auto intro:path_offset)
          subgoal using assms(5-6) False unfolding joinpaths_def pathfinish_def pathstart_def by auto
          by auto
        moreover have "jumpF h12 (at_left (1/2)) = 0"
          unfolding h12_def 
          apply (intro jumpF_im_divide_Re_0)
          subgoal using assms by (auto intro:path_offset)
          subgoal using assms(5-6) False unfolding joinpaths_def pathfinish_def pathstart_def by auto
          by auto    
        ultimately show ?thesis by auto
      next
        case True
        then have "Im ((g1 +++ g2) (1 / 2) - z) \<noteq> 0"
          using assms(5,6)
          by (metis (no_types, hide_lams) Re_divide_numeral complex_Re_numeral complex_eq 
              divide_self_if joinpaths_def  minus_complex.simps mult.commute mult.left_neutral
              numeral_One pathfinish_def pathstart_def right_minus_eq times_divide_eq_left zero_neq_numeral)
        show ?thesis
        proof (rule jump_jumpF[of _ h12 "sgnx h12 (at_left (1/2))" "sgnx h12 (at_right (1/2))"])
          define g where "g=(\<lambda>t. (g1 +++ g2) t - z)"
          have h12_def:"h12 = (\<lambda>t. Im(g t)/Re(g t))" unfolding h12_def g_def by simp  
          have "path g" using assms unfolding g_def by (auto intro!:path_offset)
          then have "isCont (\<lambda>t. Im (g t)) (1 / 2)" "isCont (\<lambda>t. Re (g t)) (1 / 2)" 
            unfolding path_def by (auto intro!:continuous_intros continuous_on_interior)
          moreover have "Im (g (1/2)) \<noteq>0"
            using \<open>Im ((g1 +++ g2) (1 / 2) - z) \<noteq> 0\<close> unfolding g_def .
          ultimately show "isCont (inverse \<circ> h12) (1 / 2)" 
            unfolding h12_def comp_def 
            by (auto intro!: continuous_intros)
              
          define l where "l \<equiv> sgnx h12 (at_left (1/2))"
          define r where "r \<equiv> sgnx h12 (at_right (1/2))"
          have *:"continuous_on ({0<..<1}- {t. h12 t = 0 \<and> 0 < t \<and> t < 1}) h12"
            using \<open>path g\<close>[unfolded path_def] unfolding h12_def
            apply (auto intro!: continuous_intros)
            by (auto elim:continuous_on_subset)   
          have **:"finite {t. h12 t = 0 \<and> 0 < t \<and> t < 1}" 
          proof -
            have "finite_axes_cross (g1 +++ g2) z" 
              using assms(1,2) finite_cross_intros(3)[of g1 z g2] by auto
            then have "finite {t. (Re (g t) = 0 \<or> Im (g t) = 0) \<and> 0 < t \<and> t < 1}" 
              unfolding finite_axes_cross_def g_def 
              apply (elim rev_finite_subset)
              by auto
            then show ?thesis unfolding h12_def 
              by (simp add:disj_commute)
          qed 
          have "h12 sgnx_able at_left (1/2)" "l \<noteq> 0" "h12 sgnx_able at_right (1/2)" "r \<noteq> 0"
            unfolding l_def r_def using finite_sgnx_at_left_at_right[OF ** * **] 
            by auto
          then show "(h12 has_sgnx l) (at_left (1/2))" "(h12 has_sgnx r) (at_right (1/2))" "l\<noteq>0" "r\<noteq>0"
            unfolding l_def r_def by (auto elim:sgnx_able_sgnx)
        qed 
      qed
      moreover have "jumpF h12 (at_right (1/2)) = jumpF_pathstart g2 z"
      proof -
        have " jumpF h12 (at_right (1 / 2)) = jumpF (h12 \<circ> (\<lambda>x. x / 2 + 1 / 2)) (at_right 0)"
          using jumpF_linear_comp[of "1/2" h12 "1/2" 0,simplified] by simp
        also have "jumpF (h12 \<circ> (\<lambda>x. x / 2 + 1 / 2)) (at_right 0) = jumpF_pathstart g2 z"
          unfolding h12_def jumpF_pathstart_def
        proof (rule jumpF_cong)
          show "\<forall>\<^sub>F x in at_right 0. ((\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)) 
                  \<circ> (\<lambda>x. x / 2 + 1 / 2)) x = Im (g2 x - z) / Re (g2 x - z)"
            unfolding eventually_at_right
            apply (intro exI[where x="1/2"])
            unfolding joinpaths_def by auto
        qed simp
        finally show ?thesis .
      qed
      moreover have "jumpF h12 (at_left (1 / 2)) = jumpF_pathfinish g1 z" 
      proof -
        have "jumpF h12 (at_left (1 / 2)) = jumpF (h12 \<circ> (\<lambda>x. x / 2)) (at_left 1)"
          using jumpF_linear_comp[of "1/2" h12 0 1,simplified] by simp
        also have "jumpF (h12 \<circ> (\<lambda>x. x / 2 )) (at_left 1) = jumpF_pathfinish g1 z"
          unfolding h12_def jumpF_pathfinish_def
        proof (rule jumpF_cong)
          show " \<forall>\<^sub>F x in at_left 1. ((\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)) 
              \<circ> (\<lambda>x. x / 2)) x = Im (g1 x - z) / Re (g1 x - z)"
            unfolding eventually_at_left
            apply (intro exI[where x="1/2"])
            unfolding joinpaths_def by auto
        qed simp
        finally show ?thesis .
      qed
      ultimately show ?thesis by auto
    qed
    moreover have "cindex 0 (1 / 2) h12 = cindex_path g1 z"
    proof -
      have "cindex 0 (1 / 2) h12 = cindex 0 1 (h12 \<circ> (\<lambda>x. x / 2))"
        using cindex_linear_comp[of "1/2" 0 1 h12 0,simplified,symmetric] .
      also have "... = cindex_path g1 z"
      proof -
        let ?g = " (\<lambda>t. Im (g1 t - z) / Re (g1 t - z))"
        have *:"jump (h12 \<circ> (\<lambda>x. x / 2)) x = jump ?g x" when "0<x" "x<1" for x 
          unfolding h12_def   
        proof (rule jump_cong)
          show "\<forall>\<^sub>F x in at x. ((\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)) 
              \<circ> (\<lambda>x. x / 2)) x = Im (g1 x - z) / Re (g1 x - z)"
            unfolding eventually_at joinpaths_def comp_def using that
            apply (intro exI[where x="(1-x)/2"])
            by (auto simp add: dist_norm)
        qed simp
        then have "{x. jump (h12 \<circ> (\<lambda>x. x / 2)) x \<noteq> 0 \<and> 0 < x \<and> x < 1} 
            = {x. jump ?g x \<noteq> 0 \<and> 0 < x \<and> x < 1}"
          by auto
        then show ?thesis
          unfolding cindex_def cindex_path_def 
          apply (elim sum.cong)
          by (auto simp add:*)
      qed
      finally show ?thesis .
    qed
    moreover have "cindex (1 / 2) 1 h12 = cindex_path g2 z"
    proof -
      have "cindex (1 / 2) 1 h12 = cindex 0 1 (h12 \<circ> (\<lambda>x. x / 2 + 1 / 2))"
        using cindex_linear_comp[of "1/2" 0 1 h12 "1/2",simplified,symmetric] . 
      also have "... = cindex_path g2 z"
      proof -
        let ?g = " (\<lambda>t. Im (g2 t - z) / Re (g2 t - z))"
        have *:"jump (h12 \<circ> (\<lambda>x. x / 2+1/2)) x = jump ?g x" when "0<x" "x<1" for x 
          unfolding h12_def   
        proof (rule jump_cong)
          show "\<forall>\<^sub>F x in at x. ((\<lambda>t. Im ((g1 +++ g2) t - z) / Re ((g1 +++ g2) t - z)) 
              \<circ> (\<lambda>x. x / 2+1/2)) x = Im (g2 x - z) / Re (g2 x - z)"
            unfolding eventually_at joinpaths_def comp_def using that
            apply (intro exI[where x="x/2"])
            by (auto simp add: dist_norm)
        qed simp
        then have "{x. jump (h12 \<circ> (\<lambda>x. x / 2+1/2)) x \<noteq> 0 \<and> 0 < x \<and> x < 1} 
            = {x. jump ?g x \<noteq> 0 \<and> 0 < x \<and> x < 1}"
          by auto
        then show ?thesis
          unfolding cindex_def cindex_path_def 
          apply (elim sum.cong)
          by (auto simp add:*)
      qed
      finally show ?thesis .
    qed     
    ultimately show ?thesis by simp
  qed
  finally show ?thesis .
qed  
    
subsection \<open>More lemmas related @{term cindex_pathE} / @{term jumpF_pathstart} / @{term jumpF_pathfinish}\<close>
    
lemma cindex_pathE_linepath:
  assumes "z\<notin>closed_segment a b"
  shows "cindex_pathE (linepath a b) z = (
    let c1 = Re a - Re z; 
        c2 = Re b - Re z; 
        c3 = Im a * Re b + Re z * Im b + Im z * Re a - Im z * Re b - Im b * Re a - Re z * Im a;
        d1 = Im a - Im z;
        d2 = Im b - Im z
    in if (c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0) then 
          (if c3>0 then 1 else -1) 
       else 
          (if (c1=0 \<longleftrightarrow> c2\<noteq>0) \<and> (c1=0 \<longrightarrow>d1\<noteq>0) \<and> (c2=0 \<longrightarrow> d2\<noteq>0) then 
            if (c1=0 \<and> (c2 >0 \<longleftrightarrow> d1>0)) \<or> (c2=0 \<and> (c1 >0 \<longleftrightarrow> d2<0))  then 1/2 else -1/2
          else 0))"
proof -
  define c1 c2 where "c1=Re a - Re z" and "c2=Re b - Re z"
  define d1 d2 where "d1=Im a - Im z" and "d2=Im b - Im z"
  let ?g = "linepath a b"
  have ?thesis when "\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))"   
  proof -
    have "Re a= Re z \<and> Re b=Re z"
      when "0<t" "t<1" and asm:"(1-t)*Re a + t * Re b = Re z" for t
      unfolding c1_def c2_def using that  
    proof -
      have ?thesis when "c1\<le>0" "c1\<ge>0"
      proof -
        have "Re a=Re z" using that unfolding c1_def by auto
        then show ?thesis using \<open>0<t\<close> \<open>t<1\<close> asm
          apply (cases "Re b" "Re z" rule:linorder_cases)
            apply (auto simp add:field_simps)
          done
      qed
      moreover have ?thesis when "c1\<le>0" "c2\<le>0"
      proof -  
        have False when "c1<0"
        proof -
          have "(1 - t) * Re a < (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1<0\<close> unfolding c1_def by auto
          moreover have "t * Re b \<le> t* Re z" using \<open>t>0\<close> \<open>c2\<le>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b < (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        moreover have False when "c2<0"
        proof -
          have "(1 - t) * Re a \<le> (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1\<le>0\<close> unfolding c1_def by auto
          moreover have "t * Re b < t* Re z" using \<open>t>0\<close> \<open>c2<0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b < (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        ultimately show ?thesis using that unfolding c1_def c2_def by argo
      qed
      moreover have ?thesis when "c2\<le>0" "c2\<ge>0"
      proof -
        have "Re b=Re z" using that unfolding c2_def by auto
        then have "(1 - t) * Re a = (1-t)*Re z" using asm by (auto simp add:field_simps)
        then have "Re a= Re z" using \<open>t<1\<close> by auto
        then show ?thesis using \<open>Re b=Re z\<close> by auto
      qed
      moreover have ?thesis when "c1\<ge>0" "c2\<ge>0"
      proof -  
        have False when "c1>0"
        proof -
          have "(1 - t) * Re a > (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1>0\<close> unfolding c1_def by auto
          moreover have "t * Re b \<ge> t* Re z" using \<open>t>0\<close> \<open>c2\<ge>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b > (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        moreover have False when "c2>0"
        proof -
          have "(1 - t) * Re a \<ge> (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1\<ge>0\<close> unfolding c1_def by auto
          moreover have "t * Re b > t* Re z" using \<open>t>0\<close> \<open>c2>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b > (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        ultimately show ?thesis using that unfolding c1_def c2_def by argo
      qed
      moreover have "c1\<le>0 \<or> c2\<ge>0" "c1\<ge>0 \<or> c2\<le>0" using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close> by auto
      ultimately show ?thesis by fast
    qed
    then have "(\<forall>t. 0<t \<and> t<1 \<longrightarrow> Re(linepath a b t - z) \<noteq> 0) \<or> (c1=0 \<and> c2=0)" 
      using that unfolding linepath_def c1_def c2_def by auto
    moreover have ?thesis when asm:"\<forall>t. 0<t \<and> t<1 \<longrightarrow> Re(linepath a b t - z) \<noteq> 0"
      and "\<not> (c1=0 \<and> c2=0)"
    proof -
      have cindex_ends:"cindex_pathE ?g z = jumpF_pathstart ?g z - jumpF_pathfinish ?g z"
      proof -
        define f where "f=(\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z))"
        define left where "left = {x. jumpF f (at_left x) \<noteq> 0 \<and> 0 < x \<and> x \<le> 1}"
        define right where "right = {x. jumpF f (at_right x) \<noteq> 0 \<and> 0 \<le> x \<and> x < 1}"
        have jumpF_nz:"jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0"
          when "0<x" "x<1" for x
        proof -
          have "isCont f x" unfolding f_def 
            using asm[rule_format,of x] that
            by (auto intro!:continuous_intros isCont_Im isCont_Re)
          then have "continuous (at_left x) f" "continuous (at_right x) f"
            using continuous_at_split by blast+
          then show "jumpF f (at_left x) = 0" "jumpF f (at_right x) = 0"
            using jumpF_not_infinity by auto
        qed
        have "cindex_pathE ?g z = sum (\<lambda>x. jumpF f (at_right x)) right 
            - sum (\<lambda>x. jumpF f (at_left x)) left"
          unfolding cindex_pathE_def cindexE_def right_def left_def 
          by (fold f_def,simp)
        moreover have "sum (\<lambda>x. jumpF f (at_right x)) right = jumpF_pathstart ?g z"
        proof (cases " jumpF f (at_right 0) = 0")
          case True
          hence False if "x \<in> right" for x using that
            by (cases "x = 0") (auto simp: jumpF_nz right_def)
          then have "right = {}" by blast
          then show ?thesis 
            unfolding jumpF_pathstart_def using True
            apply (fold f_def)
            by auto  
        next
          case False
          hence "x \<in> right \<longleftrightarrow> x = 0" for x using that
            by (cases "x = 0") (auto simp: jumpF_nz right_def)
          then have "right = {0}" by blast
          then show ?thesis 
            unfolding jumpF_pathstart_def using False
            apply (fold f_def)
            by auto
        qed
        moreover have "sum (\<lambda>x. jumpF f (at_left x)) left = jumpF_pathfinish ?g z"
        proof (cases " jumpF f (at_left 1) = 0")
          case True
          then have "left = {}"
            unfolding left_def using jumpF_nz by force
          then show ?thesis 
            unfolding jumpF_pathfinish_def using True
            apply (fold f_def)
            by auto  
        next
          case False
          then have "left = {1}"
            unfolding left_def using jumpF_nz by force
          then show ?thesis 
            unfolding jumpF_pathfinish_def using False
            apply (fold f_def)
            by auto
        qed
        ultimately show ?thesis by auto
      qed
      moreover have jF_start:"jumpF_pathstart ?g z = 
          (if c1=0 \<and> c2 \<noteq>0 \<and> d1 \<noteq>0 then 
            if c2 >0 \<longleftrightarrow> d1 > 0 then 1/2 else -1/2
          else 
            0)"
      proof -
        define f where "f=(\<lambda>t. (Im b - Im a )* t + d1)"
        define g where "g=(\<lambda>t. (Re b - Re a )* t + c1)"
        have jump_eq:"jumpF_pathstart (linepath a b) z = jumpF (\<lambda>t. f t/g t) (at_right 0)"
          unfolding jumpF_pathstart_def f_def linepath_def g_def d1_def c1_def
          by (auto simp add:algebra_simps)
        have ?thesis when "\<not> (c1 =0 \<and> c2 \<noteq>0 \<and> d1 \<noteq>0)"
        proof -
          have "c2=0 \<longrightarrow> c1\<noteq>0" using \<open>\<not> (c1=0 \<and> c2=0)\<close> by auto
          moreover have "d1 =0 \<longrightarrow> c1\<noteq>0" 
          proof (rule ccontr)
            assume "\<not> (d1 = 0 \<longrightarrow> c1 \<noteq> 0)"
            then have "a=z" unfolding d1_def c1_def by (simp add: complex_eqI)  
            then have "z\<in>path_image (linepath a b)" by auto
            then show False using \<open>z\<notin>closed_segment a b\<close> by auto
          qed    
          moreover have ?thesis when "c1\<noteq>0" 
          proof -
            have "jumpF (\<lambda>t. f t/g t) (at_right 0) = 0" 
              apply (rule jumpF_not_infinity)
               apply (unfold f_def g_def)
              using that by (auto intro!: continuous_intros) 
            then show ?thesis using jump_eq using that by auto
          qed
          ultimately show ?thesis using that by blast
        qed
        moreover have ?thesis when "c1=0" "c2 \<noteq>0" "d1 \<noteq>0" "c2 >0 \<longleftrightarrow> d1 > 0"  
        proof -
          have "(LIM x at_right 0. f x / g x :> at_top)"
          proof -
            have "(f \<longlongrightarrow> d1) (at_right 0)"
              unfolding f_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g \<longlongrightarrow> 0) (at_right 0)" 
              unfolding g_def using \<open>c1=0\<close> by (auto intro!: tendsto_eq_intros)
            moreover have "(g has_sgnx sgn d1) (at_right 0)"
            proof -  
              have "(g has_sgnx sgn (c2-c1)) (at_right 0)"
                unfolding g_def 
                apply (rule has_sgnx_derivative_at_right)
                subgoal unfolding c2_def c1_def d1_def by (auto intro!: derivative_eq_intros)
                subgoal using \<open>c1=0\<close> by auto
                subgoal using \<open>c1=0\<close> \<open>c2\<noteq>0\<close> by auto
                done    
              moreover have "sgn (c2-c1) = sgn d1" using that by fastforce
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis   
              using filterlim_divide_at_bot_at_top_iff[of f d1 "at_right 0" g] \<open>d1\<noteq>0\<close> by auto
          qed
          then have "jumpF (\<lambda>t. f t/g t) (at_right 0) = 1/2" unfolding jumpF_def by auto
          then show ?thesis using that jump_eq by auto
        qed
        moreover have ?thesis when "c1=0" "c2 \<noteq>0" "d1 \<noteq>0" "\<not> c2 >0 \<longleftrightarrow> d1 > 0"  
        proof -
          have "(LIM x at_right 0. f x / g x :> at_bot)"
          proof -
            have "(f \<longlongrightarrow> d1) (at_right 0)"
              unfolding f_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g \<longlongrightarrow> 0) (at_right 0)" 
              unfolding g_def using \<open>c1=0\<close> by (auto intro!: tendsto_eq_intros)
            moreover have "(g has_sgnx - sgn d1) (at_right 0)"
            proof -  
              have "(g has_sgnx sgn (c2-c1)) (at_right 0)"
                unfolding g_def 
                apply (rule has_sgnx_derivative_at_right)
                subgoal unfolding c2_def c1_def d1_def by (auto intro!: derivative_eq_intros)
                subgoal using \<open>c1=0\<close> by auto
                subgoal using \<open>c1=0\<close> \<open>c2\<noteq>0\<close> by auto
                done    
              moreover have "sgn (c2-c1) = - sgn d1" using that by fastforce
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis   
              using filterlim_divide_at_bot_at_top_iff[of f d1 "at_right 0" g] \<open>d1\<noteq>0\<close> by auto
          qed
          then have "jumpF (\<lambda>t. f t/g t) (at_right 0) = - 1/2" unfolding jumpF_def by auto
          then show ?thesis using that jump_eq by auto
        qed  
        ultimately show ?thesis by fast        
      qed
      moreover have jF_finish:"jumpF_pathfinish ?g z = 
          (if c2=0 \<and> c1 \<noteq>0 \<and> d2 \<noteq>0 then 
            if c1 >0 \<longleftrightarrow> d2 > 0 then 1/2 else -1/2
          else 
            0)"
      proof -
        define f where "f=(\<lambda>t. (Im b - Im a )* t + (Im a - Im z))"
        define g where "g=(\<lambda>t. (Re b - Re a )* t + (Re a - Re z))"
        have jump_eq:"jumpF_pathfinish (linepath a b) z = jumpF (\<lambda>t. f t/g t) (at_left 1)"
          unfolding jumpF_pathfinish_def f_def linepath_def g_def d1_def c1_def
          by (auto simp add:algebra_simps)
        have ?thesis when "\<not> (c2 =0 \<and> c1 \<noteq>0 \<and> d2 \<noteq>0)"
        proof -
          have "c1=0 \<longrightarrow> c2\<noteq>0" using \<open>\<not> (c1=0 \<and> c2=0)\<close> by auto
          moreover have "d2 =0 \<longrightarrow> c2\<noteq>0" 
          proof (rule ccontr)
            assume "\<not> (d2 = 0 \<longrightarrow> c2 \<noteq> 0)"
            then have "b=z" unfolding d2_def c2_def by (simp add: complex_eqI)  
            then have "z\<in>path_image (linepath a b)" by auto
            then show False using \<open>z\<notin>closed_segment a b\<close> by auto
          qed    
          moreover have ?thesis when "c2\<noteq>0" 
          proof -
            have "jumpF (\<lambda>t. f t/g t) (at_left 1) = 0" 
              apply (rule jumpF_not_infinity)
               apply (unfold f_def g_def)
              using that unfolding c2_def by (auto intro!: continuous_intros) 
            then show ?thesis using jump_eq using that by auto
          qed
          ultimately show ?thesis using that by blast
        qed
        moreover have ?thesis when "c2=0" "c1 \<noteq>0" "d2 \<noteq>0" "c1 >0 \<longleftrightarrow> d2 > 0"  
        proof -
          have "(LIM x at_left 1. f x / g x :> at_top)"
          proof -
            have "(f \<longlongrightarrow> d2) (at_left 1)"
              unfolding f_def d2_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g \<longlongrightarrow> 0) (at_left 1)" 
              using \<open>c2=0\<close> unfolding g_def c2_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g has_sgnx sgn d2) (at_left 1)"
            proof -  
              have "(g has_sgnx - sgn (c2-c1)) (at_left 1)"
                unfolding g_def 
                apply (rule has_sgnx_derivative_at_left)
                subgoal unfolding c2_def c1_def d1_def by (auto intro!: derivative_eq_intros)
                subgoal using \<open>c2=0\<close> unfolding c2_def by auto
                subgoal using \<open>c2=0\<close> \<open>c1\<noteq>0\<close> by auto
                done    
              moreover have "- sgn (c2-c1) = sgn d2" using that by fastforce
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis   
              using filterlim_divide_at_bot_at_top_iff[of f d2 "at_left 1" g] \<open>d2\<noteq>0\<close> by auto
          qed
          then have "jumpF (\<lambda>t. f t/g t) (at_left 1) = 1/2" unfolding jumpF_def by auto
          then show ?thesis using that jump_eq by auto
        qed
        moreover have ?thesis when "c2=0" "c1 \<noteq>0" "d2 \<noteq>0" "\<not> c1 >0 \<longleftrightarrow> d2 > 0"  
        proof -
          have "(LIM x at_left 1. f x / g x :> at_bot)"
          proof -
            have "(f \<longlongrightarrow> d2) (at_left 1)"
              unfolding f_def d2_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g \<longlongrightarrow> 0) (at_left 1)" 
              using \<open>c2=0\<close> unfolding g_def c2_def by (auto intro!: tendsto_eq_intros)
            moreover have "(g has_sgnx - sgn d2) (at_left 1)"
            proof -  
              have "(g has_sgnx - sgn (c2-c1)) (at_left 1)"
                unfolding g_def 
                apply (rule has_sgnx_derivative_at_left)
                subgoal unfolding c2_def c1_def d1_def by (auto intro!: derivative_eq_intros)
                subgoal using \<open>c2=0\<close> unfolding c2_def by auto
                subgoal using \<open>c2=0\<close> \<open>c1\<noteq>0\<close> by auto
                done    
              moreover have "sgn (c2-c1) = sgn d2" using that by fastforce
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis   
              using filterlim_divide_at_bot_at_top_iff[of f d2 "at_left 1" g] \<open>d2\<noteq>0\<close> by auto
          qed
          then have "jumpF (\<lambda>t. f t/g t) (at_left 1) = - 1/2" unfolding jumpF_def by auto
          then show ?thesis using that jump_eq by auto
        qed
        ultimately show ?thesis by fast  
      qed
      ultimately show ?thesis using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close>
        apply (fold c1_def c2_def d1_def d2_def)
        by auto
    qed
    moreover have ?thesis when "c1=0" "c2=0"
    proof -
      have "(\<lambda>t. Re (linepath a b t - z)) = (\<lambda>_. 0)"
        using that unfolding linepath_def c1_def c2_def  
        by (auto simp add:algebra_simps)
      then have "(\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z)) = (\<lambda>_. 0)"
        by (metis div_by_0)
      then have "cindex_pathE (linepath a b) z = 0" 
        unfolding cindex_pathE_def
        by (auto intro: cindexE_constI)
      thus ?thesis using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close> that 
        apply (fold c1_def c2_def d1_def d2_def)
        by auto
    qed    
    ultimately show ?thesis by fast
  qed
  moreover have ?thesis when c1c2_diff_sgn:"(c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0)"
  proof -
    define f where "f=(\<lambda>t. (Im b - Im a )* t + (Im a - Im z))"
    define g where "g=(\<lambda>t. (Re b - Re a )* t + (Re a - Re z))"
    define h where "h=(\<lambda>t. f t/ g t)"
    define c3 where "c3=Im(a)*Re(b)+Re(z)*Im(b)+Im(z)*Re(a) -Im(z)*Re(b) - Im(b)*Re(a) - Re(z)*Im(a)"
    define u where "u = (Re z - Re a) / (Re b - Re a)"
    let ?g = "\<lambda>t. linepath a b t - z"
    have "0<u" "u<1" "Re b - Re a\<noteq>0" using that unfolding u_def c1_def c2_def by (auto simp add:field_simps)
    have "Re(?g u) = 0" "g u=0" unfolding linepath_def u_def g_def  
      apply (auto simp add:field_simps)
      using \<open>Re b - Re a\<noteq>0\<close> by (auto simp add:field_simps)
    moreover have "u1 = u2" when "Re(?g u1) = 0" "Re(?g u2) = 0" for u1 u2
    proof -
      have " (u1 - u2) * (Re b - Re a) = Re(?g u1) - Re(?g u2)" 
        unfolding linepath_def by (auto simp add:algebra_simps)
      also have "... = 0" using that by auto
      finally have "(u1 - u2) * (Re b - Re a) = 0" .
      thus ?thesis using \<open>Re b - Re a\<noteq>0\<close> by auto
    qed
    ultimately have re_g_iff:"Re(?g t) = 0 \<longleftrightarrow> t=u" for t by blast
     
    have "cindex_pathE (linepath a b) z = jumpF h (at_right u) - jumpF h (at_left u)"
    proof -
      define left where "left = {x. jumpF h (at_left x) \<noteq> 0 \<and> 0 < x \<and> x \<le> 1}"
      define right where "right = {x. jumpF h (at_right x) \<noteq> 0 \<and> 0 \<le> x \<and> x < 1}"
      have jumpF_nz:"jumpF h (at_left x) = 0" "jumpF h (at_right x) = 0"
        when "0\<le>x" "x\<le>1" "x\<noteq>u" for x
      proof -
        have "g x\<noteq>0" 
          using re_g_iff \<open>x\<noteq>u\<close> unfolding g_def linepath_def
          by (metis \<open>Re b - Re a \<noteq> 0\<close> add_diff_cancel_left' diff_diff_eq2 diff_zero 
              nonzero_mult_div_cancel_left u_def)
        then have "isCont h x" 
          unfolding h_def f_def g_def
          by (auto intro!:continuous_intros)
        then have "continuous (at_left x) h" "continuous (at_right x) h"
          using continuous_at_split by blast+
        then show "jumpF h (at_left x) = 0" "jumpF h(at_right x) = 0"
          using jumpF_not_infinity by auto
      qed
      have "cindex_pathE (linepath a b) z = sum (\<lambda>x. jumpF h (at_right x)) right 
            - sum (\<lambda>x. jumpF h (at_left x)) left"
      proof -
        have "cindex_pathE (linepath a b) z = cindexE 0 1 (\<lambda>t. Im (?g t) / Re (?g t))"
          unfolding cindex_pathE_def by auto
        also have "... = cindexE 0 1 h"
        proof -
          have "(\<lambda>t. Im (?g t) / Re (?g t)) = h"
            unfolding h_def f_def g_def linepath_def 
            by (auto simp add:algebra_simps)
          then show ?thesis by auto
        qed
        also have "... = sum (\<lambda>x. jumpF h (at_right x)) right - sum (\<lambda>x. jumpF h (at_left x)) left"
          unfolding cindexE_def left_def right_def by auto
        finally show ?thesis .
      qed
      moreover have "sum (\<lambda>x. jumpF h (at_right x)) right = jumpF h (at_right u)"
      proof (cases " jumpF h (at_right u) = 0")
        case True
        then have "right = {}"
          unfolding right_def using jumpF_nz by force
        then show ?thesis using True by auto 
      next
        case False
        then have "right = {u}"
          unfolding right_def using jumpF_nz \<open>0<u\<close> \<open>u<1\<close> by fastforce 
        then show ?thesis by auto
      qed
      moreover have "sum (\<lambda>x. jumpF h (at_left x)) left = jumpF h (at_left u)"
      proof (cases " jumpF h (at_left u) = 0")
        case True
        then have "left = {}"
          unfolding left_def 
          apply safe
          apply (case_tac "x=u")
          using jumpF_nz \<open>0<u\<close> \<open>u<1\<close> by auto
        then show ?thesis using True by auto
      next
        case False
        then have "left = {u}"
          unfolding left_def 
          apply safe
            apply (case_tac "x=u")
          using jumpF_nz \<open>0<u\<close> \<open>u<1\<close> by auto
        then show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed
    moreover have "jump h u = (if c3>0 then 1 else -1)" 
    proof -
      have "Re b-Re a\<noteq>0" using c1c2_diff_sgn unfolding c1_def c2_def by auto 
      have "jump (\<lambda>t. Im(?g t) / Re(?g t)) u = jump h u"
        apply (rule arg_cong2[where f=jump])
        unfolding linepath_def h_def f_def g_def by (auto simp add:algebra_simps)
      moreover have "jump (\<lambda>t. Im(?g t) / Re(?g t)) u 
          = (if sgn (Re b -Re a) = sgn (Im(?g u)) then 1 else - 1)" 
      proof (rule jump_divide_derivative)
        have "path ?g" using path_offset by auto
        then have "continuous_on {0..1} (\<lambda>t. Im(?g t))" 
          using continuous_on_Im path_def by blast
        then show "isCont (\<lambda>t. Im (?g t)) u"
          unfolding path_def
          apply (elim continuous_on_interior)
          using \<open>0<u\<close> \<open>u<1\<close> by auto
      next
        show "Re(?g u) = 0" "Re b - Re a \<noteq> 0" using \<open>Re(?g u) = 0\<close> \<open>Re b - Re a \<noteq> 0\<close>
          by auto
        show "Im(?g u) \<noteq> 0" 
        proof (rule ccontr)
          assume "\<not> Im (linepath a b u - z) \<noteq> 0 "
          then have "?g u = 0" using \<open>Re(?g u) = 0\<close> 
            by (simp add: complex_eq_iff)
          then have "z \<in> closed_segment a b" using \<open>0<u\<close> \<open>u<1\<close>
            by (auto intro:linepath_in_path)
          thus False using \<open>z \<notin> closed_segment a b\<close> by simp   
        qed
        show "((\<lambda>t. Re (linepath a b t - z)) has_real_derivative Re b - Re a) (at u)"
          unfolding linepath_def by (auto intro!:derivative_eq_intros)
      qed
      moreover have "sgn (Re b - Re a) = sgn (Im(?g u)) \<longleftrightarrow> c3 > 0"   
      proof -
        have "Im(?g u) = c3/(Re b-Re a)"
        proof -
          define ba where "ba = Re b-Re a"
          have "ba\<noteq>0"  using \<open>Re b - Re a \<noteq> 0\<close> unfolding ba_def by auto
          then show ?thesis
            unfolding linepath_def u_def c3_def
            apply (fold ba_def)
            apply (auto simp add:field_simps)  
            by (auto simp add:algebra_simps ba_def)
        qed
        then have "sgn (Re b - Re a) = sgn (Im(?g u)) \<longleftrightarrow> sgn (Re b - Re a) = sgn (c3/(Re b-Re a))"
          by auto
        also have "... \<longleftrightarrow> c3>0"
          using \<open>Re b-Re a\<noteq>0\<close>
          apply (cases "0::real" c3 rule:linorder_cases)
          by (auto simp add:sgn_zero_iff)
        finally show ?thesis .
      qed 
      ultimately show ?thesis by auto
    qed
    moreover have "jump h u = jumpF h (at_right u) - jumpF h (at_left u)"
    proof (rule jump_jumpF)
      have "f u\<noteq>0" 
      proof (rule ccontr)
        assume "\<not> f u \<noteq> 0"
        then have "z\<in>path_image (linepath a b)" 
          unfolding path_image_def
          apply (rule_tac rev_image_eqI[of u])
          using re_g_iff[of u,simplified] \<open>0<u\<close> \<open>u<1\<close> 
          unfolding f_def linepath_def 
          by (auto simp add:algebra_simps complex.expand)  
        then show False using \<open>z\<notin>closed_segment a b\<close> by simp
      qed
      then show "isCont (inverse \<circ> h) u"
        unfolding h_def comp_def f_def g_def
        by (auto intro!: continuous_intros)
      define hs where "hs = sgn ((f u) / (c2 -c1))"     
      show "(h has_sgnx -hs) (at_left u)" "(h has_sgnx hs) (at_right u)"    
      proof -
        have ff:"(f has_sgnx sgn (f u)) (at_left u)" "(f has_sgnx sgn (f u)) (at_right u)" 
        proof -
          have "(f \<longlongrightarrow> f u) (at u)"
            unfolding f_def by (auto intro!:tendsto_intros)
          then have " (f has_sgnx sgn (f u)) (at u)"  
            using tendsto_nonzero_has_sgnx[of f, OF _ \<open>f u\<noteq>0\<close>] by auto
          then show "(f has_sgnx sgn (f u)) (at_left u)" "(f has_sgnx sgn (f u)) (at_right u)" 
            using has_sgnx_split by blast+
        qed
        have gg:"(g has_sgnx - sgn (c2 - c1)) (at_left u)" "(g has_sgnx sgn (c2 - c1)) (at_right u)" 
        proof -
          have "(g has_real_derivative c2 - c1) (at u)" unfolding g_def c1_def c2_def
            by (auto intro!:derivative_eq_intros)
          moreover have "c2 - c1 \<noteq> 0" using that by auto
          ultimately show "(g has_sgnx sgn (c2 - c1)) (at_right u)" 
              "(g has_sgnx - sgn (c2 - c1)) (at_left u)"
            using has_sgnx_derivative_at_right[of g "c2-c1" u] 
                has_sgnx_derivative_at_left[of g "c2-c1" u] \<open>g u=0\<close>
            by auto
        qed
        show "(h has_sgnx - hs) (at_left u)"
          using has_sgnx_divide[OF ff(1) gg(1)] unfolding h_def hs_def 
          by auto  
        show "(h has_sgnx hs) (at_right u)"    
          using has_sgnx_divide[OF ff(2) gg(2)] unfolding h_def hs_def 
          by auto 
      qed
      show "hs\<noteq>0" "-hs\<noteq>0"
        unfolding hs_def using \<open>f u\<noteq>0\<close> that by (auto simp add:sgn_if)
    qed
    ultimately show ?thesis using that 
      apply (fold c1_def c2_def c3_def)
      by auto
  qed
  ultimately show ?thesis by fast
qed
  
lemma cindex_path_linepath:
  assumes "z\<notin>path_image (linepath a b)"
  shows "cindex_path (linepath a b) z = (
    let c1=Re(a)-Re(z) ; c2=Re(b)-Re(z) ; 
        c3 = Im(a)*Re(b)+Re(z)*Im(b)+Im(z)*Re(a) -Im(z)*Re(b) - Im(b)*Re(a) - Re(z)*Im(a)
    in if (c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0) then (if c3>0 then 1 else -1) else 0)"  
proof -
  define c1 c2 where "c1=Re(a)-Re(z)" and "c2=Re(b)-Re(z)"
  let ?g = "linepath a b"
  have ?thesis when "\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))"   
  proof -
    have "Re a= Re z \<and> Re b=Re z"
      when "0<t" "t<1" and asm:"(1-t)*Re a + t * Re b = Re z" for t
      unfolding c1_def c2_def using that  
    proof -
      have ?thesis when "c1\<le>0" "c1\<ge>0"
      proof -
        have "Re a=Re z" using that unfolding c1_def by auto
        then show ?thesis using \<open>0<t\<close> \<open>t<1\<close> asm
          apply (cases "Re b" "Re z" rule:linorder_cases)
            apply (auto simp add:field_simps)
          done
      qed
      moreover have ?thesis when "c1\<le>0" "c2\<le>0"
      proof -  
        have False when "c1<0"
        proof -
          have "(1 - t) * Re a < (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1<0\<close> unfolding c1_def by auto
          moreover have "t * Re b \<le> t* Re z" using \<open>t>0\<close> \<open>c2\<le>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b < (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        moreover have False when "c2<0"
        proof -
          have "(1 - t) * Re a \<le> (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1\<le>0\<close> unfolding c1_def by auto
          moreover have "t * Re b < t* Re z" using \<open>t>0\<close> \<open>c2<0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b < (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        ultimately show ?thesis using that unfolding c1_def c2_def by argo
      qed
      moreover have ?thesis when "c2\<le>0" "c2\<ge>0"
      proof -
        have "Re b=Re z" using that unfolding c2_def by auto
        then have "(1 - t) * Re a = (1-t)*Re z" using asm by (auto simp add:field_simps)
        then have "Re a= Re z" using \<open>t<1\<close> by auto
        then show ?thesis using \<open>Re b=Re z\<close> by auto
      qed
      moreover have ?thesis when "c1\<ge>0" "c2\<ge>0"
      proof -  
        have False when "c1>0"
        proof -
          have "(1 - t) * Re a > (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1>0\<close> unfolding c1_def by auto
          moreover have "t * Re b \<ge> t* Re z" using \<open>t>0\<close> \<open>c2\<ge>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b > (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        moreover have False when "c2>0"
        proof -
          have "(1 - t) * Re a \<ge> (1 - t) * Re z"
            using \<open>t<1\<close> \<open>c1\<ge>0\<close> unfolding c1_def by auto
          moreover have "t * Re b > t* Re z" using \<open>t>0\<close> \<open>c2>0\<close> unfolding c2_def by auto
          ultimately have "(1 - t) * Re a + t * Re b > (1 - t) * Re z + t * Re z"
            by auto
          thus False using asm by (auto simp add:algebra_simps)
        qed
        ultimately show ?thesis using that unfolding c1_def c2_def by argo
      qed
      moreover have "c1\<le>0 \<or> c2\<ge>0" "c1\<ge>0 \<or> c2\<le>0" using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close> by auto
      ultimately show ?thesis by fast
    qed
    then have "(\<forall>t. 0<t \<and> t<1 \<longrightarrow> Re(linepath a b t - z) \<noteq> 0) \<or> (Re a= Re z \<and> Re b=Re z)" 
      using that unfolding linepath_def by auto
    moreover have ?thesis when asm:"\<forall>t. 0<t \<and> t<1 \<longrightarrow> Re(linepath a b t - z) \<noteq> 0"
    proof -
      have "jump (\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z)) t = 0" 
        when "0<t" "t<1" for t
        apply (rule jump_Im_divide_Re_0[of "\<lambda>t. linepath a b t - z", 
              OF _ asm[rule_format]])
        by (auto simp add:path_offset that)
      then have "cindex_path (linepath a b) z = 0"
        unfolding cindex_path_def cindex_def by auto
      thus ?thesis using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close> 
        apply (fold c1_def c2_def)
        by auto
    qed
    moreover have ?thesis when "Re a= Re z" "Re b=Re z"
    proof -
      have "(\<lambda>t. Re (linepath a b t - z)) = (\<lambda>_. 0)"
        unfolding linepath_def using \<open>Re a= Re z\<close> \<open>Re b=Re z\<close> 
        by (auto simp add:algebra_simps)
      then have "(\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z)) = (\<lambda>_. 0)"
        by (metis div_by_0)
      then have "jump (\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z)) t = 0" for t
        using jump_const by auto
      then have "cindex_path (linepath a b) z = 0"
        unfolding cindex_path_def cindex_def by auto
      thus ?thesis using \<open>\<not> ((c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0))\<close> 
        apply (fold c1_def c2_def)
        by auto
    qed    
    ultimately show ?thesis by auto
  qed
  moreover have ?thesis when c1c2_diff_sgn:"(c1>0 \<and> c2<0) \<or> (c1<0 \<and> c2>0)"
  proof -
    define c3 where "c3=Im(a)*Re(b)+Re(z)*Im(b)+Im(z)*Re(a) -Im(z)*Re(b) - Im(b)*Re(a) - Re(z)*Im(a)"
    define u where "u = (Re z - Re a) / (Re b - Re a)"
    let ?g = "\<lambda>t. linepath a b t - z"
    have "0<u" "u<1" "Re b - Re a\<noteq>0" using that unfolding u_def c1_def c2_def by (auto simp add:field_simps)
    have "Re(?g u) = 0" unfolding linepath_def u_def  
      apply (auto simp add:field_simps)
      using \<open>Re b - Re a\<noteq>0\<close> by (auto simp add:field_simps)
    moreover have "u1 = u2" when "Re(?g u1) = 0" "Re(?g u2) = 0" for u1 u2
    proof -
      have " (u1 - u2) * (Re b - Re a) = Re(?g u1) - Re(?g u2)" 
        unfolding linepath_def by (auto simp add:algebra_simps)
      also have "... = 0" using that by auto
      finally have "(u1 - u2) * (Re b - Re a) = 0" .
      thus ?thesis using \<open>Re b - Re a\<noteq>0\<close> by auto
    qed
    ultimately have re_g_iff:"Re(?g t) = 0 \<longleftrightarrow> t=u" for t by blast
    have "cindex_path (linepath a b) z = jump (\<lambda>t. Im (?g t)/Re(?g t)) u" 
    proof -  
      define f where "f=(\<lambda>t. Im (linepath a b t - z) / Re (linepath a b t - z))"
      have "jump f t =0" when "t\<noteq>u" "0<t" "t<1" for t
        unfolding f_def 
        apply (rule jump_Im_divide_Re_0)
        using that re_g_iff by (auto simp add: path_offset)
      then have "{x. jump f x \<noteq> 0 \<and> 0 < x \<and> x < 1} = (if jump f u=0 then {} else {u})"
        using \<open>0<u\<close> \<open>u<1\<close> 
        apply auto
        by fastforce
      then show ?thesis
        unfolding cindex_path_def cindex_def 
        apply (fold f_def)
        by auto
    qed  
    moreover have "jump (\<lambda>t. Im (?g t)/Re(?g t)) u = (if c3>0 then 1 else -1)" 
    proof -
      have "Re b-Re a\<noteq>0" using c1c2_diff_sgn unfolding c1_def c2_def by auto  
      have "jump (\<lambda>t. Im(?g t) / Re(?g t)) u 
          = (if sgn (Re b -Re a) = sgn (Im(?g u)) then 1 else - 1)" 
      proof (rule jump_divide_derivative)
        have "path ?g" using path_offset by auto
        then have "continuous_on {0..1} (\<lambda>t. Im(?g t))" 
          using continuous_on_Im path_def by blast
        then show "isCont (\<lambda>t. Im (?g t)) u"
          unfolding path_def
          apply (elim continuous_on_interior)
          using \<open>0<u\<close> \<open>u<1\<close> by auto
      next
        show "Re(?g u) = 0" "Re b - Re a \<noteq> 0" using \<open>Re(?g u) = 0\<close> \<open>Re b - Re a \<noteq> 0\<close>
          by auto
        show "Im(?g u) \<noteq> 0" 
        proof (rule ccontr)
          assume "\<not> Im (linepath a b u - z) \<noteq> 0 "
          then have "?g u = 0" using \<open>Re(?g u) = 0\<close> 
            by (simp add: complex_eq_iff)
          thus False using assms \<open>0<u\<close> \<open>u<1\<close> unfolding path_image_def by fastforce
        qed
        show "((\<lambda>t. Re (linepath a b t - z)) has_real_derivative Re b - Re a) (at u)"
          unfolding linepath_def by (auto intro!:derivative_eq_intros)
      qed
      moreover have "sgn (Re b - Re a) = sgn (Im(?g u)) \<longleftrightarrow> c3 > 0"   
      proof -
        have "Im(?g u) = c3/(Re b-Re a)"
        proof -
          define ba where "ba = Re b-Re a"
          have "ba\<noteq>0"  using \<open>Re b - Re a \<noteq> 0\<close> unfolding ba_def by auto
          then show ?thesis
            unfolding linepath_def u_def c3_def
            apply (fold ba_def)
            apply (auto simp add:field_simps)  
            by (auto simp add:algebra_simps ba_def)
        qed
        then have "sgn (Re b - Re a) = sgn (Im(?g u)) \<longleftrightarrow> sgn (Re b - Re a) = sgn (c3/(Re b-Re a))"
          by auto
        also have "... \<longleftrightarrow> c3>0"
          using \<open>Re b-Re a\<noteq>0\<close>
          apply (cases "0::real" c3 rule:linorder_cases)
          by (auto simp add:sgn_zero_iff)
        finally show ?thesis .
      qed 
      ultimately show ?thesis by auto
    qed
    ultimately show ?thesis using c1c2_diff_sgn
      apply (fold c1_def c2_def c3_def)
      by auto
  qed
  ultimately show ?thesis by blast  
qed

lemma cindex_pathE_part_circlepath:
  assumes "cmod (z-z0) \<noteq>r" and "r>0" "0\<le>st" "st<tt" "tt\<le>2*pi"
  shows "cindex_pathE (part_circlepath z r st tt) z0 = (
    if \<bar>Re z - Re z0\<bar> < r then 
      (let
          \<theta> = arccos ((Re z0 - Re z)/r);
          \<beta> = 2*pi - \<theta>
        in
          jumpF_pathstart (part_circlepath z r st tt) z0
          +
          (if st<\<theta> \<and> \<theta><tt then if r * sin \<theta> + Im z > Im z0 then -1 else 1 else 0)
          +
          (if st<\<beta> \<and> \<beta> < tt then if r * sin \<beta> + Im z > Im z0 then 1 else -1 else 0)
          - 
          jumpF_pathfinish (part_circlepath z r st tt) z0
      )
    else 
      if \<bar>Re z - Re z0\<bar> = r then 
        jumpF_pathstart (part_circlepath z r st tt) z0 
        - jumpF_pathfinish (part_circlepath z r st tt) z0 
      else 0
    )" 
proof -
  define f where "f=(\<lambda>i. r * sin i + Im z - Im z0)"
  define g where "g=(\<lambda>i. r * cos i + Re z - Re z0)"
  define h where "h=(\<lambda>t. f t / g t)"
  have index_eq:"cindex_pathE (part_circlepath z r st tt) z0 = cindexE st tt h"
  proof -
    have "cindex_pathE (part_circlepath z r st tt) z0 
      = cindexE 0 1 ((\<lambda>i. f i/g i) o (linepath st tt))"
      unfolding cindex_pathE_def part_circlepath_def exp_Euler f_def g_def comp_def
      by (simp add:cos_of_real sin_of_real algebra_simps)
    also have "... = cindexE st tt (\<lambda>i. f i/g i)"   
      unfolding linepath_def using cindexE_linear_comp[of "tt-st" 0 1 _ st] \<open>st<tt\<close>
      by (simp add:algebra_simps)
    also have "... = cindexE st tt h" unfolding h_def by simp
    finally show ?thesis .
  qed
  have jstart_eq:"jumpF_pathstart (part_circlepath z r st tt) z0 = jumpF h (at_right st)"
  proof -
    have "jumpF_pathstart (part_circlepath z r st tt) z0 
            = jumpF ((\<lambda>i. f i/g i) o (linepath st tt)) (at_right 0) "
      unfolding jumpF_pathstart_def part_circlepath_def exp_Euler f_def g_def comp_def 
      by (simp add:cos_of_real sin_of_real algebra_simps)
    also have "... = jumpF (\<lambda>i. f i/g i) (at_right st)"
      unfolding linepath_def using jumpF_linear_comp(2)[of "tt-st" _ st 0] \<open>st<tt\<close>
      by (simp add:algebra_simps)
    also have "... = jumpF h (at_right st)" unfolding h_def by simp
    finally show ?thesis .
  qed
  have jfinish_eq:"jumpF_pathfinish (part_circlepath z r st tt) z0 = jumpF h (at_left tt)"
  proof -
    have "jumpF_pathfinish (part_circlepath z r st tt) z0 
            = jumpF ((\<lambda>i. f i/g i) o (linepath st tt)) (at_left 1) "
      unfolding jumpF_pathfinish_def part_circlepath_def exp_Euler f_def g_def comp_def 
      by (simp add:cos_of_real sin_of_real algebra_simps)
    also have "... = jumpF (\<lambda>i. f i/g i) (at_left tt)"
      unfolding linepath_def using jumpF_linear_comp(1)[of "tt-st" _ st 1] \<open>st<tt\<close>
      by (simp add:algebra_simps)
    also have "... = jumpF h (at_left tt)" unfolding h_def by simp
    finally show ?thesis .
  qed  
  have finite_jFs:"finite_jumpFs h st tt"
  proof -
    note finite_ReZ_segments_imp_jumpFs[OF finite_ReZ_segments_part_circlepath
          ,of  z r st tt z0,simplified]
    then have "finite_jumpFs ((\<lambda>i. f i/g i) o (linepath st tt)) 0 1"
      unfolding h_def f_def g_def part_circlepath_def exp_Euler comp_def
      by (simp add:cos_of_real sin_of_real algebra_simps)
    then have "finite_jumpFs (\<lambda>i. f i/g i) st tt"
      unfolding linepath_def using finite_jumpFs_linear_pos[of "tt-st" _ st 0 1] \<open>st<tt\<close> 
      by (simp add:algebra_simps)
    then show ?thesis unfolding h_def by auto
  qed
  have g_imp_f:"g i = 0 \<Longrightarrow> f i\<noteq>0" for i 
  proof (rule ccontr)
    assume "g i = 0" "\<not> f i \<noteq> 0 "
    then have "r * sin i = Im (z0 - z)" "r * cos i = Re (z0 - z)" 
      unfolding f_def g_def by auto
    then have "(r * sin i) ^2 + (r * cos i)^2 = Im (z0 - z) ^ 2 +  Re (z0 - z) ^2" 
      by auto
    then have "r^2 * (sin i ^2  + cos i^2) = Im (z0 - z) ^ 2 +  Re (z0 - z) ^2" 
      by (auto simp only:algebra_simps power_mult_distrib)    
    then have "r^2 = cmod (z0-z) ^ 2"   
      unfolding cmod_def by auto
    then have "r = cmod (z0-z)"
      using \<open>r>0\<close> power2_eq_imp_eq by fastforce
    then show False using \<open>cmod (z-z0) \<noteq>r\<close> using norm_minus_commute by blast
  qed  
  have ?thesis when "\<bar>Re z - Re z0\<bar> > r"
  proof -      
    have "jumpF h (at_right x) = 0" "jumpF h (at_left x) = 0" for x
    proof -
      have "g x \<noteq>0" 
      proof (rule ccontr)
        assume "\<not> g x \<noteq> 0"
        then have "cos x = (Re z0 - Re z) / r" unfolding g_def using \<open>r>0\<close>  
          by (auto simp add:field_simps)
        then have "\<bar>(Re z0 - Re z)/r\<bar> \<le> 1"
          by (metis abs_cos_le_one)
        then have "\<bar>Re z0 - Re z\<bar> \<le> r"
          using \<open>r>0\<close> by (auto simp add:field_simps)
        then show False using that by auto
      qed    
      then have "isCont h x" 
        unfolding h_def f_def g_def by (auto intro:continuous_intros)
      then show "jumpF h (at_right x) = 0" "jumpF h (at_left x) = 0"
        using jumpF_not_infinity unfolding continuous_at_split by auto
    qed
    then have "cindexE st tt h = 0" unfolding cindexE_def by auto  
    then show ?thesis using index_eq that by auto 
  qed
  moreover have ?thesis when "\<bar>Re z - Re z0\<bar> = r" 
  proof -
    define R where "R=(\<lambda>S.{x. jumpF h (at_right x) \<noteq> 0 \<and> x\<in>S})"
    define L where "L=(\<lambda>S.{x. jumpF h (at_left x) \<noteq> 0 \<and> x\<in>S})"
    define right where 
      "right = (\<lambda>S. (\<Sum>x\<in>R S. jumpF h (at_right x)))"
    define left where 
      "left = (\<lambda>S. (\<Sum>x\<in>L S. jumpF h (at_left x)))"
    have "cindex_pathE (part_circlepath z r st tt) z0 = cindexE st tt h"
      using index_eq by simp
    also have "... = right {st..<tt} - left {st<..tt}"
      unfolding cindexE_def right_def left_def R_def L_def by auto
    also have "... = jumpF h (at_right st) +  right {st<..<tt} - left {st<..<tt} - jumpF h (at_left tt)"
    proof -
      have "right {st..<tt} = jumpF h (at_right st) +  right {st<..<tt}"
      proof (cases "jumpF h (at_right st) =0")
        case True
        then have "R {st..<tt} = R {st<..<tt}"
          unfolding R_def using less_eq_real_def by auto
        then have "right {st..<tt} = right {st<..<tt}"
          unfolding right_def by auto
        then show ?thesis using True by auto
      next
        case False
        have "finite (R {st..<tt})"
          using finite_jFs unfolding R_def finite_jumpFs_def 
          by (auto elim:rev_finite_subset)
        moreover have "st \<in> R {st..<tt}" using False \<open>st<tt\<close> unfolding R_def by auto
        moreover have "R {st..<tt} - {st} = R {st<..<tt}" unfolding R_def by auto
        ultimately show "right {st..<tt}= jumpF h (at_right st) 
            + right {st<..<tt}"
          using sum.remove[of "R {st..<tt}" st "\<lambda>x. jumpF h (at_right x)"]
          unfolding right_def by simp
      qed
      moreover have "left {st<..tt} = jumpF h (at_left tt) +  left {st<..<tt}"
      proof (cases "jumpF h (at_left tt) =0")
        case True
        then have "L {st<..tt} = L {st<..<tt}"
          unfolding L_def using less_eq_real_def by auto
        then have "left {st<..tt} = left {st<..<tt}"
          unfolding left_def by auto
        then show ?thesis using True by auto
      next
        case False
        have "finite (L {st<..tt})"
          using finite_jFs unfolding L_def finite_jumpFs_def 
          by (auto elim:rev_finite_subset)
        moreover have "tt \<in> L {st<..tt}" using False \<open>st<tt\<close> unfolding L_def by auto
        moreover have "L {st<..tt} - {tt} = L {st<..<tt}" unfolding L_def by auto
        ultimately show "left {st<..tt}= jumpF h (at_left tt) + left {st<..<tt}"
          using sum.remove[of "L {st<..tt}" tt "\<lambda>x. jumpF h (at_left x)"]
          unfolding left_def by simp
      qed  
      ultimately show ?thesis by simp
    qed
    also have "... =  jumpF h (at_right st) - jumpF h (at_left tt)"  
    proof -
      define S where "S={x. (jumpF h (at_left x) \<noteq> 0 \<or> jumpF h (at_right x) \<noteq> 0) \<and> st < x \<and> x < tt}"
      have "right {st<..<tt} = sum (\<lambda>x. jumpF h (at_right x)) S"
        unfolding right_def S_def R_def
        apply (rule sum.mono_neutral_left)
        subgoal using finite_jFs unfolding finite_jumpFs_def by (auto elim:rev_finite_subset)
        subgoal by auto
        subgoal by auto
        done
      moreover have "left {st<..<tt} = sum (\<lambda>x. jumpF h (at_left x)) S"
        unfolding left_def S_def L_def
        apply (rule sum.mono_neutral_left)
        subgoal using finite_jFs unfolding finite_jumpFs_def by (auto elim:rev_finite_subset)
        subgoal by auto
        subgoal by auto
        done   
      ultimately have "right {st<..<tt} - left {st<..<tt} 
          = sum (\<lambda>x. jumpF h (at_right x) - jumpF h (at_left x)) S"
        by (simp add: sum_subtractf)
      also have "... = 0"
      proof -
        have "jumpF h (at_right i) - jumpF h (at_left i) = 0" when "g i=0" for i
        proof -
          have "(LIM x at i. f x / g x :> at_bot) \<or> (LIM x at i. f x / g x :> at_top)"
          proof -
            have *: "f \<midarrow>i\<rightarrow> f i" "g \<midarrow>i\<rightarrow> 0" "f i \<noteq> 0" 
              using g_imp_f[OF \<open>g i=0\<close>] \<open>g i=0\<close> unfolding f_def g_def 
              by (auto intro!:tendsto_eq_intros)
            have ?thesis when "Re z > Re z0"
            proof -
              have g_alt:"g = (\<lambda>t. r * cos t + r)" unfolding g_def using \<open>\<bar>Re z - Re z0\<bar> = r\<close> that by auto
              have "(g has_sgnx 1) (at i)" 
              proof -
                have "sgn (g t) = 1" when "t \<noteq> i " "dist t i < pi" for t
                proof -
                  have "cos i = - 1" using \<open>g i =0\<close> \<open>r>0\<close> unfolding g_alt 
                    by (metis add.inverse_inverse less_numeral_extra(3) mult_cancel_left 
                        mult_minus1_right real_add_minus_iff)
                  then obtain k::int where k_def:"i = (2 * k + 1) * pi"
                    using cos_eq_minus1[of i] by auto
                  show ?thesis
                  proof (rule ccontr)
                    assume "sgn (g t) \<noteq> 1"
                    then have "cos t + 1\<le>0" using \<open>r>0\<close> unfolding g_alt 
                      by (metis (no_types, hide_lams) add_le_same_cancel1 add_minus_cancel 
                          mult_le_cancel_left1 mult_le_cancel_right1 mult_minus_right mult_zero_left 
                          sgn_pos zero_le_one)
                    then have "cos t = -1" 
                      by (metis add.commute cos_ge_minus_one le_less not_less real_add_le_0_iff)
                    then obtain k'::int where k'_def:"t = (2 * k' + 1) * pi"
                      using cos_eq_minus1[of t] by auto  
                    then have "t - i = 2 * pi*(k' - k)"
                      using k_def by (auto simp add:algebra_simps)
                    then have "2  * pi * \<bar>  (k' - k)\<bar> < pi" 
                      using \<open>dist t i < pi\<close> by (simp add:dist_norm abs_mult)
                    from divide_strict_right_mono[OF this, of "2*pi",simplified] have "\<bar>k' - k \<bar> < 1/2"
                      by auto
                    then have "k=k'" by linarith
                    then have "t=i" using k_def k'_def by auto
                    then show False using \<open>t\<noteq>i\<close> by auto
                  qed
                qed
                then show ?thesis unfolding has_sgnx_def eventually_at
                  apply(intro exI[where x="pi"])
                  by auto
              qed
              then show ?thesis using * filterlim_divide_at_bot_at_top_iff[of f "f i" "at i" g]
                by (simp add: sgn_if)
            qed
            moreover have ?thesis when "Re z < Re z0"
            proof -
                have g_alt:"g = (\<lambda>t. r * cos t - r)" unfolding g_def using \<open>\<bar>Re z - Re z0\<bar> = r\<close> that by auto
                have "(g has_sgnx - 1) (at i)" 
                proof -
                  have "sgn (g t) = - 1" when "t \<noteq> i " "dist t i < pi" for t
                  proof -
                    have "cos i = 1" using \<open>g i =0\<close> \<open>r>0\<close> unfolding g_alt by simp
                    then obtain k::int where k_def:"i = (2 * k  * pi)"
                      using cos_one_2pi_int[of i] by auto
                    show ?thesis
                    proof (rule ccontr)
                      assume "sgn (g t) \<noteq> - 1"
                      then have "cos t - 1\<ge>0" using \<open>r>0\<close> unfolding g_alt 
                        using mult_le_cancel_left1 by fastforce
                      then have "cos t = 1" 
                        by (meson cos_le_one diff_ge_0_iff_ge le_less not_less)
                      then obtain k'::int where k'_def:"t = 2 * k'* pi"
                        using cos_one_2pi_int[of t] by auto  
                      then have "t - i = 2 * pi*(k' - k)"
                        using k_def by (auto simp add:algebra_simps)
                      then have "2  * pi * \<bar>  (k' - k)\<bar> < pi" 
                        using \<open>dist t i < pi\<close> by (simp add:dist_norm abs_mult)
                      from divide_strict_right_mono[OF this, of "2*pi",simplified] have "\<bar>k' - k \<bar> < 1/2"
                        by auto
                      then have "k=k'" by linarith
                      then have "t=i" using k_def k'_def by auto
                      then show False using \<open>t\<noteq>i\<close> by auto
                    qed
                  qed
                  then show ?thesis unfolding has_sgnx_def eventually_at
                    apply(intro exI[where x="pi"])
                    by auto
                qed
                then show ?thesis using * filterlim_divide_at_bot_at_top_iff[of f "f i" "at i" g]
                  by (simp add: sgn_if)
            qed
            moreover have "Re z\<noteq> Re z0" using \<open>\<bar>Re z - Re z0\<bar> = r\<close> \<open>r>0\<close> by fastforce 
            ultimately show ?thesis by fastforce
          qed
          moreover have ?thesis when "(LIM x at i. f x / g x :> at_bot)"
          proof -
            have "jumpF h (at_right i) = - 1/2" "jumpF h (at_left i) = -1/2"
              using that unfolding jumpF_def h_def filterlim_at_split by auto
            then show ?thesis by auto
          qed
          moreover have ?thesis when "(LIM x at i. f x / g x :> at_top)"
          proof -
            have "jumpF h (at_right i) =  1/2" "jumpF h (at_left i) = 1/2"
              using that unfolding jumpF_def h_def filterlim_at_split by auto
            then show ?thesis by auto
          qed  
          ultimately show ?thesis by auto
        qed
        moreover have "jumpF h (at_right i) - jumpF h (at_left i) = 0" when "g i\<noteq>0" for i 
        proof -
          have "isCont h i" using that unfolding h_def f_def g_def
            by (auto intro!:continuous_intros)
          then have "jumpF h (at_right i) = 0" "jumpF h (at_left i) = 0"  
            using jumpF_not_infinity unfolding continuous_at_split by auto
          then show ?thesis by auto
        qed
        ultimately show ?thesis by (intro sum.neutral,auto)
      qed
      finally show ?thesis by simp
    qed
    also have "... = jumpF_pathstart (part_circlepath z r st tt) z0 
        - jumpF_pathfinish (part_circlepath z r st tt) z0" 
      using jstart_eq jfinish_eq by auto
    finally have "cindex_pathE (part_circlepath z r st tt) z0 = 
        jumpF_pathstart (part_circlepath z r st tt) z0 
        - jumpF_pathfinish (part_circlepath z r st tt) z0"
      .
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "\<bar>Re z - Re z0\<bar> < r"
  proof -
    define zr where "zr= (Re z0 - Re z)/r"
    define \<theta> where "\<theta> = arccos zr"
    define \<beta> where "\<beta> = 2*pi - \<theta>" 
    have "0<\<theta>" "\<theta><pi"
    proof -
      have "- 1 < zr" "zr < 1"  
        using that \<open>r>0\<close> unfolding zr_def by (auto simp add:field_simps)
      from arccos_lt_bounded[OF this] show "0<\<theta>" "\<theta><pi"
        unfolding \<theta>_def by auto
    qed
    have "g \<theta> = 0" "g \<beta> = 0" 
    proof -
      have "\<bar>zr\<bar>\<le>1" using that unfolding zr_def by auto
      then have "cos \<theta> = zr" "cos \<beta> = cos \<theta>"
        unfolding \<theta>_def[folded zr_def] \<beta>_def by auto
      then show "g \<theta> = 0" "g \<beta> = 0" unfolding zr_def g_def using \<open>r>0\<close> by auto
    qed
    have g_sgnx_\<theta>:"(g has_sgnx 1) (at_left \<theta>)" "(g has_sgnx -1) (at_right \<theta>)"
    proof -
      have "(g has_real_derivative - r * sin \<theta>) (at \<theta>)"
        unfolding g_def by (auto intro!:derivative_eq_intros)
      moreover have "- r * sin \<theta> <0"
        using sin_gt_zero[OF \<open>0<\<theta>\<close> \<open>\<theta><pi\<close>] \<open>r>0\<close> by auto
      ultimately show "(g has_sgnx 1) (at_left \<theta>)" "(g has_sgnx -1) (at_right \<theta>)"
        using has_sgnx_derivative_at_left[of g "- r * sin \<theta>", OF _ \<open>g \<theta>=0\<close>] 
              has_sgnx_derivative_at_right[of g "- r * sin \<theta>", OF _ \<open>g \<theta>=0\<close>]
        by force+
    qed
    have g_sgnx_\<beta>:"(g has_sgnx -1) (at_left \<beta>)" "(g has_sgnx 1) (at_right \<beta>)"
    proof -
      have "(g has_real_derivative - r * sin \<beta>) (at \<beta>)"
        unfolding g_def by (auto intro!:derivative_eq_intros)
      moreover have "pi<\<beta>" "\<beta><2*pi" unfolding \<beta>_def using \<open>0<\<theta>\<close> \<open>\<theta><pi\<close> by auto
      from sin_lt_zero[OF this] \<open>r>0\<close> have "- r * sin \<beta> >0" by (simp add: mult_pos_neg)
      ultimately show "(g has_sgnx -1) (at_left \<beta>)" "(g has_sgnx 1) (at_right \<beta>)"
        using has_sgnx_derivative_at_left[of g "- r * sin \<beta>", OF _ \<open>g \<beta>=0\<close>] 
              has_sgnx_derivative_at_right[of g "- r * sin \<beta>", OF _ \<open>g \<beta>=0\<close>]
        by force+
    qed
    have f_tendsto: "(f \<longlongrightarrow> f i) (at_left i)" "(f \<longlongrightarrow> f i) (at_right i)" 
     and g_tendsto: "(g \<longlongrightarrow> g i) (at_left i)" "(g \<longlongrightarrow> g i) (at_right i)" for i
    proof -
      have "(f \<longlongrightarrow> f i) (at i)"
        unfolding f_def by (auto intro!:tendsto_eq_intros)
      then show "(f \<longlongrightarrow> f i) (at_left i)" "(f \<longlongrightarrow> f i) (at_right i)"
        by (auto simp add: filterlim_at_split)
    next
      have "(g \<longlongrightarrow> g i) (at i)"
        unfolding g_def by (auto intro!:tendsto_eq_intros)
      then show "(g \<longlongrightarrow> g i) (at_left i)" "(g \<longlongrightarrow> g i) (at_right i)"
        by (auto simp add: filterlim_at_split)
    qed
      
    define \<theta>_if::real where "\<theta>_if = (if r * sin \<theta> + Im z > Im z0 then -1 else 1)" 
    define \<beta>_if::real where "\<beta>_if = (if r * sin \<beta> + Im z > Im z0 then 1 else -1)" 
    have "jump (\<lambda>i. f i/g i) \<theta> = \<theta>_if" 
    proof -
      have ?thesis when "r * sin \<theta> + Im z > Im z0"
      proof -
        have "f \<theta> > 0" using that unfolding f_def by auto
        have "(LIM x (at_left \<theta>). f x / g x :> at_top)" 
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<theta>" _ g])
          using \<open>f \<theta> > 0\<close> \<open>g \<theta> =0\<close> f_tendsto g_tendsto[of \<theta>] g_sgnx_\<theta> by auto
        moreover then have "\<not> (LIM x (at_left \<theta>). f x / g x :> at_bot)" by auto 
        moreover have "(LIM x (at_right \<theta>). f x / g x :> at_bot)"    
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<theta>" _ g])
          using \<open>f \<theta> > 0\<close> \<open>g \<theta> =0\<close> f_tendsto g_tendsto[of \<theta>] g_sgnx_\<theta> by auto
        ultimately show ?thesis using that unfolding jump_def \<theta>_if_def by auto
      qed
      moreover have ?thesis when "r * sin \<theta> + Im z < Im z0"
      proof -
        have "f \<theta> < 0" using that unfolding f_def by auto
        have "(LIM x (at_left \<theta>). f x / g x :> at_bot)" 
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<theta>" _ g])
          using \<open>f \<theta> < 0\<close> \<open>g \<theta> =0\<close> f_tendsto g_tendsto[of \<theta>] g_sgnx_\<theta> by auto
        moreover have "(LIM x (at_right \<theta>). f x / g x :> at_top)"    
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<theta>" _ g])
          using \<open>f \<theta> < 0\<close> \<open>g \<theta> =0\<close> f_tendsto g_tendsto[of \<theta>] g_sgnx_\<theta> by auto
        ultimately show ?thesis using that unfolding jump_def \<theta>_if_def by auto
      qed  
      moreover have "r * sin \<theta> + Im z \<noteq> Im z0"
        using g_imp_f[OF \<open>g \<theta>=0\<close>] unfolding f_def by auto
      ultimately show ?thesis by fastforce
    qed
    moreover have "jump (\<lambda>i. f i/g i) \<beta> = \<beta>_if" 
    proof -
      have ?thesis when "r * sin \<beta> + Im z > Im z0"
      proof -
        have "f \<beta> > 0" using that unfolding f_def by auto
        have "(LIM x (at_left \<beta>). f x / g x :> at_bot)" 
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<beta>" _ g])
          using \<open>f \<beta> > 0\<close> \<open>g \<beta> =0\<close> f_tendsto g_tendsto[of \<beta>] g_sgnx_\<beta> by auto
        moreover have "(LIM x (at_right \<beta>). f x / g x :> at_top)"    
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<beta>" _ g])
          using \<open>f \<beta> > 0\<close> \<open>g \<beta> =0\<close> f_tendsto g_tendsto[of \<beta>] g_sgnx_\<beta> by auto
        ultimately show ?thesis using that unfolding jump_def \<beta>_if_def by auto
      qed
      moreover have ?thesis when "r * sin \<beta> + Im z < Im z0"
      proof -
        have "f \<beta> < 0" using that unfolding f_def by auto
        have "(LIM x (at_left \<beta>). f x / g x :> at_top)" 
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<beta>" _ g])
          using \<open>f \<beta> < 0\<close> \<open>g \<beta> =0\<close> f_tendsto g_tendsto[of \<beta>] g_sgnx_\<beta> by auto
        moreover have "(LIM x (at_right \<beta>). f x / g x :> at_bot)"    
          apply (subst filterlim_divide_at_bot_at_top_iff[of f "f \<beta>" _ g])
          using \<open>f \<beta> < 0\<close> \<open>g \<beta> =0\<close> f_tendsto g_tendsto[of \<beta>] g_sgnx_\<beta> by auto
        ultimately show ?thesis using that unfolding jump_def \<beta>_if_def by auto
      qed  
      moreover have "r * sin \<beta> + Im z \<noteq> Im z0"
        using g_imp_f[OF \<open>g \<beta>=0\<close>] unfolding f_def by auto
      ultimately show ?thesis by fastforce
    qed
    moreover have "jump (\<lambda>i. f i / g i) x \<noteq> 0 \<longleftrightarrow> x=\<theta> \<or> x=\<beta>" when "st<x" "x<tt" for x 
    proof 
      assume "x = \<theta> \<or> x = \<beta>"
      then show "jump (\<lambda>i. f i / g i) x \<noteq> 0"
        using \<open>jump (\<lambda>i. f i/g i) \<theta> = \<theta>_if\<close> \<open>jump (\<lambda>i. f i/g i) \<beta> = \<beta>_if\<close>
        unfolding \<theta>_if_def \<beta>_if_def 
        by (metis add.inverse_inverse add.inverse_neutral of_int_0 one_neq_zero)
    next
      assume asm:"jump (\<lambda>i. f i / g i) x \<noteq> 0"
      let ?thesis = "x = \<theta> \<or> x = \<beta>"
      have "g x=0"
      proof (rule ccontr)
        assume "g x \<noteq> 0"
        then have "isCont (\<lambda>i. f i / g i) x"  
          unfolding f_def g_def by (auto intro:continuous_intros)
        then have "jump (\<lambda>i. f i / g i) x = 0" using jump_not_infinity by simp
        then show False using asm by auto
      qed
      then have "cos x = zr" unfolding g_def zr_def using \<open>r>0\<close> by (auto simp add:field_simps)
      have ?thesis when "x\<le>pi"
      proof-
        have "x\<ge>0" using \<open>st<x\<close> \<open>st\<ge>0\<close> by auto
        then have "arccos (cos x) = x" using arccos_cos[of x] that by auto
        then have "x=\<theta>" unfolding \<theta>_def \<open>cos x=zr\<close> by auto
        then show ?thesis by auto
      qed
      moreover have ?thesis when "\<not> x\<le>pi"
      proof -
        have "x-2*pi\<le>0" "-pi\<le>x-2*pi" using that \<open>x<tt\<close> \<open>tt\<le>2*pi\<close> by auto
        from arccos_cos2[OF this] have "arccos (cos (x - 2 * pi)) = 2*pi-x" by auto
        then have "arccos (cos x) = 2*pi-x" 
          by (metis arccos cos_2pi_minus cos_ge_minus_one cos_le_one)
        then have "x=\<beta>" unfolding \<beta>_def \<theta>_def using \<open>cos x =zr\<close> by auto
        then show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    qed
    then have "{x. jump (\<lambda>i. f i / g i) x \<noteq> 0 \<and> st < x \<and> x < tt} = {\<theta>,\<beta>} \<inter> {st<..<tt}"
      by force
    moreover have "\<theta>\<noteq>\<beta>" using \<beta>_def \<open>\<theta> < pi\<close> by auto
    ultimately have "cindex st tt h = 
          (if st<\<theta> \<and> \<theta><tt then \<theta>_if else 0)
          +
          (if st<\<beta> \<and> \<beta> < tt then \<beta>_if else 0)"
      unfolding cindex_def h_def by fastforce
    moreover have "cindexE st tt h = jumpF h (at_right st) + cindex st tt h - jumpF h (at_left tt)"
    proof (rule cindex_eq_cindexE_divide[of st tt f g,folded h_def])
      show "st < tt" using \<open>st < tt\<close> .
      show "\<forall>x\<in>{st..tt}. g x = 0 \<longrightarrow> f x \<noteq> 0" using g_imp_f by auto
      show "continuous_on {st..tt} f" "continuous_on {st..tt} g"
        unfolding f_def g_def by (auto intro!:continuous_intros)
    next
      let ?S1="{t. Re (part_circlepath z r st tt t-z0) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"  
      let ?S2="{t. Im (part_circlepath z r st tt t-z0) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
      define G where "G={t.  g (linepath st tt t) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
      define F where "F={t.  f (linepath st tt t) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
      define vl where "vl=(\<lambda>x. (x-st)/(tt-st))"
      have "finite G" "finite F"
      proof -
        have "finite {t. Re (part_circlepath z r st tt t-z0) = 0 \<and> 0 \<le> t \<and> t \<le> 1}" 
             "finite {t. Im (part_circlepath z r st tt t-z0) = 0 \<and> 0 \<le> t \<and> t \<le> 1}"
          using part_circlepath_half_finite_inter[of st tt r "Complex 1 0" z "Re z0"]
              part_circlepath_half_finite_inter[of st tt r "Complex 0 1" z "Im z0"] \<open>st<tt\<close> \<open>r>0\<close> 
          by (auto simp add:inner_complex_def Complex_eq_0)  
        moreover have 
            "Re (part_circlepath z r st tt t-z0) = 0 \<longleftrightarrow> g (linepath st tt t) = 0"
            "Im (part_circlepath z r st tt t-z0) = 0 \<longleftrightarrow> f (linepath st tt t) = 0"
            for t
          unfolding cindex_pathE_def part_circlepath_def exp_Euler f_def g_def comp_def
          by (auto simp add:cos_of_real sin_of_real algebra_simps)
        ultimately show "finite G" "finite F" unfolding G_def F_def
          by auto
      qed
      then have "finite (linepath st tt ` F)" "finite (linepath st tt ` G)"
        by auto
      moreover have 
          "{x. f x = 0 \<and> st \<le> x \<and> x \<le> tt} \<subseteq> linepath st tt ` F"
          "{x. g x = 0 \<and> st \<le> x \<and> x \<le> tt} \<subseteq> linepath st tt ` G"
      proof -
        have *: "linepath st tt (vl t) = t" "vl t\<ge>0 \<longleftrightarrow> t\<ge>st" "vl t\<le>1 \<longleftrightarrow>t\<le>tt" for t 
          unfolding linepath_def vl_def using \<open>tt>st\<close>
            apply (auto simp add:divide_simps)  
          by (simp add:algebra_simps)   
        then show 
            "{x. f x = 0 \<and> st \<le> x \<and> x \<le> tt} \<subseteq> linepath st tt `F"
            "{x. g x = 0 \<and> st \<le> x \<and> x \<le> tt} \<subseteq> linepath st tt `G"
          unfolding F_def G_def 
          by (clarify|rule_tac x="vl x" in rev_image_eqI,auto)+
      qed
      ultimately have 
          "finite {x. f x = 0 \<and> st \<le> x \<and> x \<le> tt}" 
          "finite {x. g x = 0 \<and> st \<le> x \<and> x \<le> tt}"
        by (auto elim:rev_finite_subset)
      from finite_UnI[OF this] show "finite {x. (f x = 0 \<or> g x = 0) \<and> st \<le> x \<and> x \<le> tt}" 
        by (elim rev_finite_subset,auto)
    qed
    ultimately show ?thesis
      unfolding Let_def
      apply (fold zr_def \<theta>_def \<beta>_def \<theta>_if_def \<beta>_if_def)+
      using jstart_eq jfinish_eq index_eq that by auto
  qed
  ultimately show ?thesis by fastforce  
qed 

lemma jumpF_pathstart_part_circlepath: 
  assumes "st<tt" "r>0" "cmod (z-z0) \<noteq>r"
  shows "jumpF_pathstart (part_circlepath z r st tt) z0 = (
            if r * cos st + Re z - Re z0 = 0 then 
              (let 
                \<Delta> = r* sin st + Im z - Im z0
              in
                if (sin st > 0 \<or> cos st=1 ) \<and> \<Delta> < 0 
                    \<or> (sin st < 0 \<or>  cos st=-1 ) \<and> \<Delta> > 0  then 
                  1/2
                else 
                  - 1/2)
            else 0)"  
proof -
  define f where "f=(\<lambda>i. r * sin i + Im z - Im z0)"
  define g where "g=(\<lambda>i. r * cos i + Re z - Re z0)"
  have jumpF_eq:"jumpF_pathstart (part_circlepath z r st tt) z0 = jumpF (\<lambda>i. f i/g i) (at_right st)"
  proof -
    have "jumpF_pathstart (part_circlepath z r st tt) z0 
        = jumpF ((\<lambda>i. f i/g i) o linepath st tt) (at_right 0)" 
      unfolding jumpF_pathstart_def part_circlepath_def exp_Euler f_def g_def comp_def
      by (simp add:cos_of_real sin_of_real algebra_simps)
    also have "... = jumpF (\<lambda>i. f i/g i) (at_right st)"
      using jumpF_linear_comp(2)[of "tt-st" "(\<lambda>i. f i/g i)" st 0,symmetric] \<open>st<tt\<close>
      unfolding linepath_def by (auto simp add:algebra_simps)
    finally show ?thesis .
  qed
  have g_has_sgnx1:"(g has_sgnx 1) (at_right st)" when "g st=0" "sin st < 0 \<or> cos st=-1"  
  proof -
    have ?thesis when "sin st<0" 
    proof -
      have "(g has_sgnx sgn (- r * sin st)) (at_right st)"
        apply (rule has_sgnx_derivative_at_right[of g "- r * sin st" st])
        subgoal unfolding g_def by (auto intro!:derivative_eq_intros)
        subgoal using \<open>g st=0\<close> .
        subgoal using \<open>r>0\<close> \<open>sin st<0\<close> by (simp add: mult_pos_neg)
        done
      then show ?thesis using \<open>r>0\<close> that by (simp add: sgn_mult)
    qed
    moreover have ?thesis when "cos st = -1"
    proof -
      have "g i > 0" when "st<i" "i<st+pi" for i
      proof -
        obtain k where k_def:"st = 2 * of_int k * pi+ pi" 
          using \<open>cos st = -1\<close> by (metis cos_eq_minus1 distrib_left mult.commute mult.right_neutral)
        have "cos (i-st) < 1" using cos_monotone_0_pi[of 0 "i-st" ] that by auto
        moreover have "cos (i-st) = - cos i" 
          apply (rule cos_eq_neg_periodic_intro[of _ _ "-k-1"])
          unfolding k_def by (auto simp add:algebra_simps)
        ultimately have "cos i>-1" by auto
        then have "cos st<cos i" using \<open>cos st=-1\<close> by auto
        have "0 = r * cos st + Re z - Re z0"
          using \<open>g st = 0\<close> unfolding g_def by auto
        also have "... < r * cos i + Re z - Re z0"
          using \<open>cos st < cos i\<close> \<open>r>0\<close> by auto
        finally show ?thesis unfolding g_def by auto
      qed
      then show ?thesis
        unfolding has_sgnx_def eventually_at_right 
        apply (intro exI[where x="st+pi"])
        by auto
    qed
    ultimately show ?thesis using that(2) by auto
  qed
  have g_has_sgnx2:"(g has_sgnx -1) (at_right st)" when "g st=0" "sin st > 0 \<or> cos st=1" 
  proof -
    have ?thesis when "sin st>0"
    proof -
      have "(g has_sgnx sgn (- r * sin st)) (at_right st)"
        apply (rule has_sgnx_derivative_at_right[of _ "- r * sin st"])
        subgoal unfolding g_def by (auto intro!:derivative_eq_intros)
        subgoal using \<open>g st=0\<close> .
        subgoal using \<open>r>0\<close> \<open>sin st>0\<close> by (simp add: mult_pos_neg)
        done
      then show ?thesis using \<open>r>0\<close> that by (simp add: sgn_mult)
    qed    
    moreover have ?thesis when "cos st=1"
    proof -
      have "g i < 0" when "st<i" "i<st+pi" for i
      proof -
        obtain k where k_def:"st = 2 * of_int k * pi" 
          using \<open>cos st=1\<close> cos_one_2pi_int by auto
        have "cos (i-st) < 1" using cos_monotone_0_pi[of 0 "i-st" ] that by auto
        moreover have "cos (i-st) = cos i" 
          apply (rule cos_eq_periodic_intro[of _ _ "-k"])
          unfolding k_def by (auto simp add:algebra_simps)
        ultimately have "cos i<1" by auto
        then have "cos st>cos i" using \<open>cos st=1\<close> by auto
        have "0 = r * cos st + Re z - Re z0"
          using \<open>g st = 0\<close> unfolding g_def by auto
        also have "... > r * cos i + Re z - Re z0"
          using \<open>cos st > cos i\<close> \<open>r>0\<close> by auto
        finally show ?thesis unfolding g_def by auto
      qed
      then show ?thesis
        unfolding has_sgnx_def eventually_at_right
        apply (intro exI[where x="st+pi"])
        by auto
    qed
    ultimately show ?thesis using that(2) by auto
  qed
    
  have ?thesis when "r * cos st + Re z - Re z0 \<noteq> 0"
  proof -
    have "g st \<noteq>0" using that unfolding g_def by auto
    then have "continuous (at_right st) (\<lambda>i. f i / g i)"
      unfolding f_def g_def by (auto intro!:continuous_intros)
    then have "jumpF (\<lambda>i. f i/g i) (at_right st) = 0"
      using jumpF_not_infinity[of "at_right st" "(\<lambda>i. f i/g i)"] by auto
    then show ?thesis using jumpF_eq that by auto
  qed
  moreover have ?thesis when "r * cos st + Re z - Re z0 = 0" 
    "(sin st > 0 \<or> (cos st=1) ) \<and> f st < 0 
                    \<or> (sin st < 0 \<or>  (cos st=-1) ) \<and> f st > 0"
  proof -
    have "g st = 0" "f st\<noteq>0" and g_cont: "continuous (at_right st) g" and f_cont:"continuous (at_right st) f" 
      using that unfolding g_def f_def by (auto intro!:continuous_intros)
    have "(g has_sgnx sgn (f st)) (at_right st)"
      using g_has_sgnx1[OF \<open>g st=0\<close>] g_has_sgnx2[OF \<open>g st=0\<close>] that(2) by auto
    then have "LIM x at_right st. f x / g x :> at_top"
      apply (subst filterlim_divide_at_bot_at_top_iff[of f "f st" "at_right st" g])
      using \<open>f st\<noteq>0\<close> \<open>g st = 0\<close> g_cont f_cont by (auto simp add: continuous_within)
    then have "jumpF (\<lambda>i. f i/g i) (at_right st) = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis using jumpF_eq that unfolding f_def by auto
  qed
  moreover have ?thesis when "r * cos st + Re z - Re z0 = 0" 
    "\<not> ((sin st > 0 \<or> cos st=1 ) \<and> f st < 0 
                    \<or> (sin st < 0 \<or>  cos st=-1 ) \<and> f st > 0)"
  proof -
    define neq1 where "neq1 = (\<forall>k::int. st \<noteq> 2*k*pi)"
    define neq2 where "neq2 = (\<forall>k::int. st \<noteq> 2*k*pi+pi)"
    have "g st = 0" and g_cont: "continuous (at_right st) g" and f_cont:"continuous (at_right st) f" 
      using that unfolding g_def f_def by (auto intro!:continuous_intros)
    have "f st\<noteq>0"
    proof (rule ccontr)
      assume "\<not> f st \<noteq> 0"
      then have "f st = 0" by auto
      then have "Im (z0 - z) =r * sin st " "Re (z0 - z) = r * cos st" using \<open>g st=0\<close>
        unfolding f_def g_def by (auto simp add:algebra_simps)
      then have "cmod (z0 - z) = sqrt((r * sin st)^2 + (r * cos st)^2)" 
        unfolding cmod_def by auto
      also have "... = sqrt (r^2 * ((sin st)^2 + (cos st)^2))"
        by (auto simp only:algebra_simps power_mult_distrib)
      also have "... = r"
        using \<open>r>0\<close> by simp
      finally have "cmod (z0 - z) = r" .
      then show False using \<open>cmod (z-z0) \<noteq>r\<close> by (simp add: norm_minus_commute)
    qed
    have "(sin st > 0 \<or> (cos st=1) ) \<and> f st > 0 \<or> (sin st < 0 \<or>  (cos st=-1) ) \<and> f st < 0"  
    proof -
      have "sin st = 0 \<longleftrightarrow> cos st=-1 \<or> cos st=1"  
        by (metis (no_types, hide_lams) add.right_neutral cancel_comm_monoid_add_class.diff_cancel 
            cos_diff cos_zero mult_eq_0_iff power2_eq_1_iff power2_eq_square sin_squared_eq)
      moreover have "((sin st \<le> 0 \<and> cos st \<noteq>1 ) \<or> f st > 0) \<and> ((sin st \<ge> 0 \<and>  cos st\<noteq>-1) \<or> f st < 0)"
        using that(2) \<open>f st\<noteq>0\<close> by argo  
      ultimately show ?thesis by (meson linorder_neqE_linordered_idom not_le)   
    qed   
    then have "(g has_sgnx - sgn (f st)) (at_right st)"  
      using g_has_sgnx1[OF \<open>g st=0\<close>] g_has_sgnx2[OF \<open>g st=0\<close>] by auto
    then have "LIM x at_right st. f x / g x :> at_bot"
      apply (subst filterlim_divide_at_bot_at_top_iff[of f "f st" "at_right st" g])
      using \<open>f st\<noteq>0\<close> \<open>g st = 0\<close> g_cont f_cont by (auto simp add: continuous_within)
    then have "jumpF (\<lambda>i. f i/g i) (at_right st) = -1/2"
      unfolding jumpF_def by auto
    then show ?thesis using jumpF_eq that unfolding f_def by auto
  qed    
  ultimately show ?thesis by fast
qed  
  
lemma jumpF_pathfinish_part_circlepath: 
  assumes "st<tt" "r>0" "cmod (z-z0) \<noteq>r"
  shows "jumpF_pathfinish (part_circlepath z r st tt) z0 = (
            if r * cos tt + Re z - Re z0 = 0 then 
              (let 
                \<Delta> = r* sin tt + Im z - Im z0
              in
                if (sin tt > 0 \<or> cos tt=-1 ) \<and> \<Delta> < 0 
                    \<or> (sin tt < 0 \<or>  cos tt=1 ) \<and> \<Delta> > 0  then 
                  - 1/2
                else 
                  1/2)
            else 0)"  
proof -
  define f where "f=(\<lambda>i. r * sin i + Im z - Im z0)"
  define g where "g=(\<lambda>i. r * cos i + Re z - Re z0)"
  have jumpF_eq:"jumpF_pathfinish (part_circlepath z r st tt) z0 = jumpF (\<lambda>i. f i/g i) (at_left tt)"
  proof -
    have "jumpF_pathfinish (part_circlepath z r st tt) z0 
        = jumpF ((\<lambda>i. f i/g i) o linepath st tt) (at_left 1)" 
      unfolding jumpF_pathfinish_def part_circlepath_def exp_Euler f_def g_def comp_def
      by (simp add:cos_of_real sin_of_real algebra_simps)
    also have "... = jumpF (\<lambda>i. f i/g i) (at_left tt)"
      using jumpF_linear_comp(1)[of "tt-st" "(\<lambda>i. f i/g i)" st 1,symmetric]  \<open>st<tt\<close>
      unfolding linepath_def by (auto simp add:algebra_simps)
    finally show ?thesis .
  qed
  have g_has_sgnx1:"(g has_sgnx -1) (at_left tt)" when "g tt=0" "sin tt < 0 \<or> cos tt=1"  
  proof -
    have ?thesis when "sin tt<0"
    proof -
      have "(g has_sgnx - sgn (- r * sin tt)) (at_left tt)"
        apply (rule has_sgnx_derivative_at_left[of _ "- r * sin tt"])
        subgoal unfolding g_def by (auto intro!:derivative_eq_intros)
        subgoal using \<open>g tt=0\<close> .
        subgoal using \<open>r>0\<close> \<open>sin tt<0\<close> by (simp add: mult_pos_neg)
        done
      then show ?thesis using \<open>r>0\<close> that by (simp add: sgn_mult)
    qed
    moreover have ?thesis when "cos tt=1"
    proof -
      have "g i < 0" when "tt-pi<i" "i<tt" for i
      proof -
        obtain k where k_def:"tt = 2 * of_int k * pi" 
          using \<open>cos tt=1\<close> cos_one_2pi_int by auto
        have "cos (i-tt) < 1" 
          using cos_monotone_0_pi[of 0 "tt-i" ] that cos_minus[of "tt-i",simplified] by auto
        moreover have "cos (i-tt) = cos i" 
          apply (rule cos_eq_periodic_intro[of _ _ "-k"])
          unfolding k_def by (auto simp add:algebra_simps)
        ultimately have "cos i<1" by auto
        then have "cos tt>cos i" using \<open>cos tt=1\<close> by auto
        have "0 = r * cos tt + Re z - Re z0"
          using \<open>g tt = 0\<close> unfolding g_def by auto
        also have "... > r * cos i + Re z - Re z0"
          using \<open>cos tt > cos i\<close> \<open>r>0\<close> by auto
        finally show ?thesis unfolding g_def by auto
      qed
      then show ?thesis
        unfolding has_sgnx_def eventually_at_left
        apply (intro exI[where x="tt-pi"])
        by auto
    qed
    ultimately show ?thesis using that(2) by auto
  qed
  have g_has_sgnx2:"(g has_sgnx 1) (at_left tt)" when "g tt=0" "sin tt > 0 \<or> cos tt=-1" 
  proof -
    have ?thesis when "sin tt>0"
    proof -
      have "(g has_sgnx - sgn (- r * sin tt)) (at_left tt)"
        apply (rule has_sgnx_derivative_at_left[of _ "- r * sin tt"])
        subgoal unfolding g_def by (auto intro!:derivative_eq_intros)
        subgoal using \<open>g tt=0\<close> .
        subgoal using \<open>r>0\<close> \<open>sin tt>0\<close> by (simp add: mult_pos_neg)
        done
      then show ?thesis using \<open>r>0\<close> that by (simp add: sgn_mult)
    qed
    moreover have ?thesis when "cos tt = -1"
    proof -
      have "g i > 0" when "tt-pi<i" "i<tt" for i
      proof -
        obtain k where k_def:"tt = 2 * of_int k * pi+ pi" 
          using \<open>cos tt = -1\<close> by (metis cos_eq_minus1 distrib_left mult.commute mult.right_neutral)
        have "cos (i-tt) < 1" 
            using cos_monotone_0_pi[of 0 "tt-i" ] that cos_minus[of "tt-i",simplified]
            by auto
        moreover have "cos (i-tt) = - cos i" 
          apply (rule cos_eq_neg_periodic_intro[of _ _ "-k-1"])
          unfolding k_def by (auto simp add:algebra_simps)
        ultimately have "cos i>-1" by auto
        then have "cos tt<cos i" using \<open>cos tt=-1\<close> by auto
        have "0 = r * cos tt + Re z - Re z0"
          using \<open>g tt = 0\<close> unfolding g_def by auto
        also have "... < r * cos i + Re z - Re z0"
          using \<open>cos tt < cos i\<close> \<open>r>0\<close> by auto
        finally show ?thesis unfolding g_def by auto
      qed
      then show ?thesis
        unfolding has_sgnx_def eventually_at_left 
        apply (intro exI[where x="tt-pi"])
        by auto
    qed
    ultimately show ?thesis using that(2) by auto
  qed
    
  have ?thesis when "r * cos tt + Re z - Re z0 \<noteq> 0"
  proof -
    have "g tt \<noteq>0" using that unfolding g_def by auto
    then have "continuous (at_left tt) (\<lambda>i. f i / g i)"
      unfolding f_def g_def by (auto intro!:continuous_intros)
    then have "jumpF (\<lambda>i. f i/g i) (at_left tt) = 0"
      using jumpF_not_infinity[of "at_left tt" "(\<lambda>i. f i/g i)"] by auto
    then show ?thesis using jumpF_eq that by auto
  qed
  moreover have ?thesis when "r * cos tt + Re z - Re z0 = 0" 
    "(sin tt > 0 \<or> cos tt=-1 ) \<and> f tt < 0 
                    \<or> (sin tt < 0 \<or> cos tt=1 ) \<and> f tt > 0"
  proof -
    have "g tt = 0" "f tt\<noteq>0" and g_cont: "continuous (at_left tt) g" and f_cont:"continuous (at_left tt) f" 
      using that unfolding g_def f_def by (auto intro!:continuous_intros)
    have "(g has_sgnx - sgn (f tt)) (at_left tt)"
      using g_has_sgnx1[OF \<open>g tt=0\<close>] g_has_sgnx2[OF \<open>g tt=0\<close>] that(2) by auto
    then have "LIM x at_left tt. f x / g x :> at_bot"
      apply (subst filterlim_divide_at_bot_at_top_iff[of f "f tt" "at_left tt" g])
      using \<open>f tt\<noteq>0\<close> \<open>g tt = 0\<close> g_cont f_cont by (auto simp add: continuous_within)
    then have "jumpF (\<lambda>i. f i/g i) (at_left tt) = - 1/2"
      unfolding jumpF_def by auto
    then show ?thesis using jumpF_eq that unfolding f_def by auto
  qed
  moreover have ?thesis when "r * cos tt + Re z - Re z0 = 0" 
    "\<not> ((sin tt > 0 \<or> cos tt=-1 ) \<and> f tt < 0 
                    \<or> (sin tt < 0 \<or>  cos tt=1 ) \<and> f tt > 0)"
  proof -
    have "g tt = 0" and g_cont: "continuous (at_left tt) g" and f_cont:"continuous (at_left tt) f" 
      using that unfolding g_def f_def by (auto intro!:continuous_intros)
    have "f tt\<noteq>0"
    proof (rule ccontr)
      assume "\<not> f tt \<noteq> 0"
      then have "f tt = 0" by auto
      then have "Im (z0 - z) =r * sin tt " "Re (z0 - z) = r * cos tt" using \<open>g tt=0\<close>
        unfolding f_def g_def by (auto simp add:algebra_simps)
      then have "cmod (z0 - z) = sqrt((r * sin tt)^2 + (r * cos tt)^2)" 
        unfolding cmod_def by auto
      also have "... = sqrt (r^2 * ((sin tt)^2 + (cos tt)^2))"
        by (auto simp only:algebra_simps power_mult_distrib)
      also have "... = r"
        using \<open>r>0\<close> by simp
      finally have "cmod (z0 - z) = r" .
      then show False using \<open>cmod (z-z0) \<noteq>r\<close> by (simp add: norm_minus_commute)
    qed
    have "(sin tt > 0 \<or> cos tt=-1 ) \<and> f tt > 0 \<or> (sin tt < 0 \<or>  cos tt=1 ) \<and> f tt < 0"  
    proof -
      have "sin tt = 0 \<longleftrightarrow> cos tt=-1 \<or> cos tt=1"  
        by (metis (no_types, hide_lams) add.right_neutral cancel_comm_monoid_add_class.diff_cancel 
            cos_diff cos_zero mult_eq_0_iff power2_eq_1_iff power2_eq_square sin_squared_eq)
      moreover have "((sin tt \<le> 0 \<and> cos tt \<noteq>-1 ) \<or> f tt > 0) \<and> ((sin tt \<ge> 0 \<and>  cos tt\<noteq>1) \<or> f tt < 0)"
        using that(2) \<open>f tt\<noteq>0\<close> by argo  
      ultimately show ?thesis by (meson linorder_neqE_linordered_idom not_le)   
    qed   
    then have "(g has_sgnx sgn (f tt)) (at_left tt)"  
      using g_has_sgnx1[OF \<open>g tt=0\<close>] g_has_sgnx2[OF \<open>g tt=0\<close>] by auto
    then have "LIM x at_left tt. f x / g x :> at_top"
      apply (subst filterlim_divide_at_bot_at_top_iff[of f "f tt" "at_left tt" g])
      using \<open>f tt\<noteq>0\<close> \<open>g tt = 0\<close> g_cont f_cont by (auto simp add: continuous_within)
    then have "jumpF (\<lambda>i. f i/g i) (at_left tt) = 1/2"
      unfolding jumpF_def by auto
    then show ?thesis using jumpF_eq that unfolding f_def by auto
  qed    
  ultimately show ?thesis by fast
qed

lemma 
  fixes z0 z::complex and r::real
  defines "upper \<equiv> cindex_pathE (part_circlepath z r 0 pi) z0"
      and "lower \<equiv> cindex_pathE (part_circlepath z r pi (2*pi)) z0"
  shows cindex_pathE_circlepath_upper:
      "\<lbrakk>cmod (z0-z) < r\<rbrakk>  \<Longrightarrow> upper = -1" 
      "\<lbrakk>Im (z0-z) > r; \<bar>Re (z0 - z)\<bar> < r\<rbrakk> \<Longrightarrow> upper = 1"
      "\<lbrakk>Im (z0-z) < -r; \<bar>Re (z0 - z)\<bar> < r\<rbrakk> \<Longrightarrow> upper = -1" 
      "\<lbrakk>\<bar>Re (z0 - z)\<bar> > r; r>0\<rbrakk> \<Longrightarrow> upper = 0"
  and cindex_pathE_circlepath_lower: 
      "\<lbrakk>cmod (z0-z) < r\<rbrakk> \<Longrightarrow> lower = -1" 
      "\<lbrakk>Im (z0-z) > r; \<bar>Re (z0 - z)\<bar> < r\<rbrakk> \<Longrightarrow> lower = -1"
      "\<lbrakk>Im (z0-z) < -r; \<bar>Re (z0 - z)\<bar> < r\<rbrakk> \<Longrightarrow> lower = 1"
      "\<lbrakk>\<bar>Re (z0 - z)\<bar> > r; r>0\<rbrakk> \<Longrightarrow> lower = 0"
proof -
  assume assms:"cmod (z0-z) < r"
  have zz_facts:"-r<Re z - Re z0" "Re z - Re z0<r" "r>0"
    subgoal using assms complex_Re_le_cmod le_less_trans by fastforce
    subgoal by (metis assms complex_Re_le_cmod le_less_trans minus_complex.simps(1) norm_minus_commute)
    subgoal using assms le_less_trans norm_ge_zero by blast
    done
  define \<theta> where "\<theta> = arccos ((Re z0 - Re z) / r)"    
  have \<theta>_bound:"0 < \<theta> \<and> \<theta> < pi" 
    unfolding \<theta>_def
    apply (rule arccos_lt_bounded)
    using zz_facts by (auto simp add:field_simps)
  have Im_sin:"abs (Im z0 - Im z) < r * sin \<theta>"
  proof -
    define zz where "zz=z0-z"
    have "sqrt ((Re zz)\<^sup>2 + (Im zz)\<^sup>2) < r"
      using assms unfolding zz_def cmod_def .
    then have "(Re zz)\<^sup>2 + (Im zz)\<^sup>2 < r^2"
      by (metis cmod_power2 dvd_refl linorder_not_le norm_complex_def power2_le_imp_le
            real_sqrt_power zero_le_power_eq_numeral)
    then have "(Im zz)\<^sup>2 < r^2 - (Re zz)^2" by auto
    then have "abs (Im zz) < sqrt (r^2 - (Re zz)^2)"
      by (simp add: real_less_rsqrt)
    then show ?thesis
      unfolding \<theta>_def zz_def
      apply (subst sin_arccos_abs)
      subgoal using zz_facts by auto
      subgoal using \<open>r>0\<close> by (auto simp add:field_simps divide_simps real_sqrt_divide)
      done
  qed
  show "upper = - 1"
  proof -
    have "jumpF_pathstart (part_circlepath z r 0 pi) z0 = 0"
      apply (subst jumpF_pathstart_part_circlepath)
      using zz_facts assms by (auto simp add: norm_minus_commute)
    moreover have "jumpF_pathfinish (part_circlepath z r 0 pi) z0 = 0"
      apply (subst jumpF_pathfinish_part_circlepath)
      using zz_facts assms by (auto simp add: norm_minus_commute)
    ultimately show ?thesis using assms zz_facts \<theta>_bound Im_sin unfolding upper_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto simp add: norm_minus_commute)
  qed
  show "lower = - 1"
  proof -    
    have "jumpF_pathstart (part_circlepath z r pi (2*pi)) z0 = 0"
      apply (subst jumpF_pathstart_part_circlepath)
      using zz_facts assms by (auto simp add: norm_minus_commute)
    moreover have "jumpF_pathfinish (part_circlepath z r pi (2*pi)) z0 = 0"
      apply (subst jumpF_pathfinish_part_circlepath)
      using zz_facts assms by (auto simp add: norm_minus_commute)
    ultimately show ?thesis using assms zz_facts \<theta>_bound Im_sin unfolding lower_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto simp add: norm_minus_commute)
  qed 
next
  assume assms:"\<bar>Re (z0 - z)\<bar> > r" "r>0"
  show "upper = 0" using assms unfolding upper_def 
    apply (subst cindex_pathE_part_circlepath)
    apply auto
    by (metis abs_Re_le_cmod abs_minus_commute eucl_less_le_not_le minus_complex.simps(1))
  show "lower = 0"
    using assms unfolding lower_def 
    apply (subst cindex_pathE_part_circlepath)
    apply auto
    by (metis abs_Re_le_cmod abs_minus_commute eucl_less_le_not_le minus_complex.simps(1))
next
  assume assms:"\<bar>Re (z0 - z)\<bar> < r"
  then have "r>0" by auto

  define \<theta> where "\<theta> = arccos ((Re z0 - Re z) / r)"   
  have \<theta>_bound:"0 < \<theta> \<and> \<theta> < pi" 
    unfolding \<theta>_def
    apply (rule arccos_lt_bounded)
    using assms by (auto simp add:field_simps)
  note norm_minus_commute[simp]
  have jumpFs:
      "jumpF_pathstart (part_circlepath z r 0 pi) z0 = 0"
      "jumpF_pathfinish (part_circlepath z r 0 pi) z0 = 0"
      "jumpF_pathstart (part_circlepath z r pi (2*pi)) z0 = 0"
      "jumpF_pathfinish (part_circlepath z r pi (2*pi)) z0 = 0"
      when "cmod (z0 - z) \<noteq> r"
    subgoal by (subst jumpF_pathstart_part_circlepath,use assms that in auto)
    subgoal by (subst jumpF_pathfinish_part_circlepath,use assms that in auto)
    subgoal by (subst jumpF_pathstart_part_circlepath,use assms that in auto)
    subgoal by (subst jumpF_pathfinish_part_circlepath,use assms that in auto)
    done
  show "upper = 1" "lower = -1" when "Im (z0-z) > r"
  proof -
    have "cmod (z0 - z) \<noteq> r" 
      using that assms abs_Im_le_cmod abs_le_D1 not_le by blast
    moreover have "Im z0 - Im z > r * sin \<theta>" 
    proof -
      have "r * sin \<theta> \<le> r" 
        using \<open>r>0\<close> by auto
      also have "... < Im z0 - Im z" using that by auto
      finally show ?thesis .
    qed
    ultimately show "upper = 1"  using assms jumpFs \<theta>_bound that unfolding upper_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto)
    have "Im z - Im z0 < r * sin \<theta>" 
    proof -
      have "Im z - Im z0  <0" using that \<open>r>0\<close> by auto
      moreover have "r * sin \<theta>>0" using \<open>r>0\<close> \<theta>_bound by (simp add: sin_gt_zero)
      ultimately show ?thesis by auto
    qed
    then show "lower = -1" using \<open>cmod (z0 - z) \<noteq> r\<close> \<open>Im z0 - Im z > r * sin \<theta>\<close> 
        assms jumpFs \<theta>_bound that unfolding lower_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto)
  qed
  show "upper = - 1" "lower = 1" when "Im (z0-z) < -r"
  proof -
    have "cmod (z0 - z) \<noteq> r" 
      using that assms 
      by (metis abs_Im_le_cmod abs_le_D1 minus_complex.simps(2) minus_diff_eq neg_less_iff_less 
          norm_minus_cancel not_le)
    moreover have "Im z - Im z0 > r * sin \<theta>" 
    proof -
      have "r * sin \<theta> \<le> r" 
        using \<open>r>0\<close> by auto
      also have "... < Im z - Im z0" using that by auto
      finally show ?thesis .
    qed
    moreover have "Im z0 - Im z < r * sin \<theta>"
    proof -
      have "Im z0 - Im z<0" using that \<open>r>0\<close> by auto
      moreover have "r * sin \<theta>>0" using \<open>r>0\<close> \<theta>_bound by (simp add: sin_gt_zero)
      ultimately show ?thesis by auto
    qed
    ultimately show "upper = - 1" using assms jumpFs \<theta>_bound that unfolding upper_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto)
    show "lower = 1"
      using \<open>Im z0 - Im z < r * sin \<theta>\<close> \<open>Im z - Im z0 > r * sin \<theta>\<close> \<open>cmod (z0 - z) \<noteq> r\<close>
        assms jumpFs \<theta>_bound that unfolding lower_def
      apply (subst cindex_pathE_part_circlepath)
      by (fold \<theta>_def,auto)
  qed
qed
  
lemma jumpF_pathstart_linepath:
  "jumpF_pathstart (linepath a b) z = 
    (if Re a = Re z \<and> Im a\<noteq>Im z \<and> Re b \<noteq> Re a then 
        if (Im a>Im z \<and> Re b > Re a) \<or> (Im a<Im z \<and> Re b < Re a) then 1/2 else -1/2 
     else 0)"
proof -
  define f where "f=(\<lambda>t. (Im b - Im a )* t + (Im a - Im z))"
  define g where "g=(\<lambda>t. (Re b - Re a )* t + (Re a - Re z))"
  have jump_eq:"jumpF_pathstart (linepath a b) z = jumpF (\<lambda>t. f t/g t) (at_right 0)"
    unfolding jumpF_pathstart_def f_def linepath_def g_def 
    by (auto simp add:algebra_simps)
  have ?thesis when "Re a\<noteq>Re z"
  proof -
    have "jumpF_pathstart (linepath a b) z = 0"
      unfolding jumpF_pathstart_def
      apply (rule jumpF_im_divide_Re_0)
         apply auto
      by (auto simp add:linepath_def that)
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "Re a=Re z" "Im a = Im z" 
  proof -
    define c where "c=(Im b - Im a) / (Re b - Re a)"
    have "jumpF (\<lambda>t. f t/g t) (at_right 0) = jumpF (\<lambda>_. c) (at_right 0)"
    proof (rule jumpF_cong)
      show "\<forall>\<^sub>F x in at_right 0. f x / g x = c"
        unfolding eventually_at_right f_def g_def c_def using that
        apply (intro exI[where x=1])
        by auto
    qed simp
    then show ?thesis using jump_eq that by auto 
  qed
  moreover have ?thesis when "Re a=Re z" "Re b = Re a" 
  proof -
    have "(\<lambda>t. f t/g t) = (\<lambda>_. 0)" unfolding f_def g_def using that by auto
    then have "jumpF (\<lambda>t. f t/g t) (at_right 0) = jumpF (\<lambda>_. 0) (at_right 0)" by auto
    then show ?thesis using jump_eq that by auto
  qed
  moreover have ?thesis when "Re a = Re z" "(Im a>Im z \<and> Re b > Re a) \<or> (Im a<Im z \<and> Re b < Re a)"
  proof -
    have "LIM x at_right 0. f x / g x :> at_top"
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "Im a - Im z"])
      unfolding f_def g_def using that
      by (auto intro!:tendsto_eq_intros sgnx_eq_intros)  
    then have "jumpF (\<lambda>t. f t/g t) (at_right 0) = 1/2"
      unfolding jumpF_def by simp
    then show ?thesis using jump_eq that by auto
  qed
  moreover have ?thesis when "Re a = Re z" "Im a\<noteq>Im z" "Re b \<noteq> Re a" 
      "\<not> ((Im a>Im z \<and> Re b > Re a) \<or> (Im a<Im z \<and> Re b < Re a))"
  proof -
    have "(Im a>Im z \<and> Re b < Re a) \<or> (Im a<Im z \<and> Re b > Re a)"
      using that by argo
    then have "LIM x at_right 0. f x / g x :> at_bot"
      apply (subst filterlim_divide_at_bot_at_top_iff[of _ "Im a - Im z"])
      unfolding f_def g_def using that
      by (auto intro!:tendsto_eq_intros sgnx_eq_intros) 
    moreover then have "\<not> (LIM x at_right 0. f x / g x :> at_top)"
      using filterlim_at_top_at_bot by fastforce
    ultimately have "jumpF (\<lambda>t. f t/g t) (at_right 0) = - 1/2"
      unfolding jumpF_def by simp
    then show ?thesis using jump_eq that by auto
  qed  
  ultimately show ?thesis by fast
qed
  
lemma jumpF_pathfinish_linepath:
  "jumpF_pathfinish (linepath a b) z = 
    (if Re b = Re z \<and> Im b \<noteq>Im z \<and> Re b \<noteq> Re a then 
        if (Im b>Im z \<and> Re a > Re b) \<or> (Im b<Im z \<and> Re a < Re b) then 1/2 else -1/2 
     else 0)"
proof -
  define f where "f=(\<lambda>t. (Im b - Im a )* t + (Im a - Im z))"
  define g where "g=(\<lambda>t. (Re b - Re a )* t + (Re a - Re z))"
  have jump_eq:"jumpF_pathfinish (linepath a b) z = jumpF (\<lambda>t. f t/g t) (at_left 1)"
    unfolding jumpF_pathfinish_def f_def linepath_def g_def 
    by (auto simp add:algebra_simps)
  have ?thesis when "Re b\<noteq>Re z"
  proof -
    have "jumpF_pathfinish (linepath a b) z = 0"
      unfolding jumpF_pathfinish_def
      apply (rule jumpF_im_divide_Re_0)
         apply auto
      by (auto simp add:linepath_def that)
    then show ?thesis using that by auto
  qed
  moreover have ?thesis when "Re z=Re b" "Im z = Im b" 
  proof -
    define c where "c=(Im a - Im b) / (Re a - Re b)"
    have "jumpF (\<lambda>t. f t/g t) (at_left 1) = jumpF (\<lambda>_. c) (at_left 1)"
    proof (rule jumpF_cong)
      have "f x / g x = c" when "x<1" for x
      proof -
        have "f x / g x = ((Im a - Im b)*(1-x))/((Re a - Re b)*(1-x))"
          unfolding f_def g_def 
          by (auto simp add:algebra_simps \<open>Re z=Re b\<close> \<open>Im z = Im b\<close>)
        also have "... = c"
          using that unfolding c_def by auto
        finally show ?thesis .
      qed
      then show "\<forall>\<^sub>F x in at_left 1. f x / g x = c"
        unfolding eventually_at_left using that
        apply (intro exI[where x=0])
        by auto
    qed simp
    then show ?thesis using jump_eq that by auto 
  qed
  moreover have ?thesis when "Re a=Re z" "Re b = Re a" 
  proof -
    have "(\<lambda>t. f t/g t) = (\<lambda>_. 0)" unfolding f_def g_def using that by auto
    then have "jumpF (\<lambda>t. f t/g t) (at_left 1) = jumpF (\<lambda>_. 0) (at_left 1)" by auto
    then show ?thesis using jump_eq that by auto
  qed
  moreover have ?thesis when "Re b = Re z" "(Im b>Im z \<and> Re a > Re b) \<or> (Im b<Im z \<and> Re a < Re b)"
  proof -
    have "LIM x at_left 1. f x / g x :> at_top"
    proof -
      have "(g has_real_derivative Re b - Re a) (at 1)"
        unfolding g_def by (auto intro!:derivative_eq_intros) 
      from has_sgnx_derivative_at_left[OF this] 
      have "(g has_sgnx sgn (Im b - Im z)) (at_left 1)"
        using that unfolding g_def by auto
      then show ?thesis 
        apply (subst filterlim_divide_at_bot_at_top_iff[of _ "Im b - Im z"])
        unfolding f_def g_def using that by (auto intro!:tendsto_eq_intros)
    qed
    then have "jumpF (\<lambda>t. f t/g t) (at_left 1) = 1/2"
      unfolding jumpF_def by simp
    then show ?thesis using jump_eq that by auto
  qed
  moreover have ?thesis when "Re b = Re z" "Im b\<noteq>Im z" "Re b \<noteq> Re a" 
      "\<not> ((Im b>Im z \<and> Re a > Re b) \<or> (Im b<Im z \<and> Re a < Re b))"
  proof -
    have "(Im b>Im z \<and> Re a < Re b) \<or> (Im b<Im z \<and> Re a > Re b)"
      using that by argo
    have "LIM x at_left 1. f x / g x :> at_bot"
    proof -
      have "(g has_real_derivative Re b - Re a) (at 1)"
        unfolding g_def by (auto intro!:derivative_eq_intros) 
      from has_sgnx_derivative_at_left[OF this]
      have "(g has_sgnx - sgn (Im b - Im z)) (at_left 1)" 
        using that unfolding g_def by auto
      then show ?thesis
        apply (subst filterlim_divide_at_bot_at_top_iff[of _ "Im b - Im z"])
        unfolding f_def g_def using that by (auto intro!:tendsto_eq_intros ) 
    qed
    moreover then have "\<not> (LIM x at_left 1. f x / g x :> at_top)"
      using filterlim_at_top_at_bot by fastforce
    ultimately have "jumpF (\<lambda>t. f t/g t) (at_left 1) = - 1/2"
      unfolding jumpF_def by simp
    then show ?thesis using jump_eq that by auto
  qed  
  ultimately show ?thesis by argo
qed    
    
subsection \<open>Setting up the method for evaluating winding numbers\<close>  
  
lemma pathfinish_pathstart_partcirclepath_simps:
  "pathstart (part_circlepath z0 r (3*pi/2) tt) = z0 - Complex 0 r"
  "pathstart (part_circlepath z0 r (2*pi) tt) = z0 + r"
  "pathfinish (part_circlepath z0 r st (3*pi/2)) = z0 - Complex 0 r"
  "pathfinish (part_circlepath z0 r st (2*pi)) = z0 + r"
  "pathstart (part_circlepath z0 r 0 tt) = z0 + r"
  "pathstart (part_circlepath z0 r (pi/2) tt) = z0 + Complex 0 r"
  "pathstart (part_circlepath z0 r (pi) tt) = z0 - r"
  "pathfinish (part_circlepath z0 r st 0) = z0+r"
  "pathfinish (part_circlepath z0 r st (pi/2)) = z0 + Complex 0 r"
  "pathfinish (part_circlepath z0 r st (pi)) = z0 - r"
  unfolding part_circlepath_def linepath_def pathstart_def pathfinish_def exp_Euler
  subgoal 
    apply(simp, subst sin.minus_1[symmetric],subst cos.minus_1[symmetric])
    by (simp add: complex_of_real_i)
  subgoal by (simp, subst sin.minus_1[symmetric],subst cos.minus_1[symmetric],auto)
  subgoal 
    apply (simp, subst sin.minus_1[symmetric],subst cos.minus_1[symmetric])
    by (simp add: complex_of_real_i)
  subgoal by (simp, subst sin.minus_1[symmetric],subst cos.minus_1[symmetric],auto)
  by (simp_all add: complex_of_real_i)
    
lemma winding_eq_intro:
  "finite_ReZ_segments g z \<Longrightarrow>
  valid_path g \<Longrightarrow>
  z \<notin> path_image g \<Longrightarrow>
  pathfinish g = pathstart g \<Longrightarrow>  
  - of_real(cindex_pathE g z) =2*n \<Longrightarrow>
  winding_number g z = (n::complex)"
apply (subst winding_number_cindex_pathE[of g z])
by (auto simp add:field_simps)
    
named_theorems winding_intros and winding_simps
   
lemmas [winding_intros] = 
  finite_ReZ_segments_joinpaths
  valid_path_join
  path_join_imp
  not_in_path_image_join

lemmas [winding_simps] =
  finite_ReZ_segments_linepath
  finite_ReZ_segments_part_circlepath
  jumpF_pathfinish_joinpaths
  jumpF_pathstart_joinpaths
  pathfinish_linepath
  pathstart_linepath
  pathfinish_join
  pathstart_join
  valid_path_linepath
  valid_path_part_circlepath
  path_part_circlepath
  Re_complex_of_real
  Im_complex_of_real
  of_real_linepath
  pathfinish_pathstart_partcirclepath_simps
    
method rep_subst  =
  (subst cindex_pathE_joinpaths; rep_subst)?
 
  
text \<open>
The method "eval\_winding" @{term 1} will try to simplify of the form @{term "winding_number g z = n"} where 
@{term n} is an integer and @{term g} is a closed path comprised of @{term linepath}, 
@{term part_circlepath} and @{term joinpaths}.

Suppose @{term "g=l1+++l2"}, usually, the key behind the success of this framework is whether we can prove 
@{term "z \<notin> path_image l1"}, @{term "z \<notin> path_image l2"} and calculate @{term "cindex_pathE l1 z"} 
and @{term "cindex_pathE l2 z"}.
\<close>
  
method eval_winding = 
  ((rule_tac winding_eq_intro;
    rep_subst
    )
  , auto simp only:winding_simps del:notI intro!:winding_intros
  , tactic \<open>distinct_subgoals_tac\<close>)
  
end
