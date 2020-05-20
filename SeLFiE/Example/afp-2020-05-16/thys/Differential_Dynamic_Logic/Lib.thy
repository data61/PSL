theory Lib
imports
  Ordinary_Differential_Equations.ODE_Analysis
begin
section \<open>Generic Mathematical Lemmas\<close>
text\<open>General lemmas that don't have anything to do with dL specifically and could be fit for 
  general-purpose libraries, mostly dealing with derivatives, ODEs and vectors.\<close>

lemma vec_extensionality:"(\<And>i. v$i = w$i) \<Longrightarrow> (v = w)"
  by (simp add: vec_eq_iff)

lemma norm_axis: "norm (axis i x) = norm x"
  unfolding axis_def norm_vec_def
  unfolding L2_set_def
  by(clarsimp simp add: if_distrib[where f=norm] if_distrib[where f="\<lambda>x. x\<^sup>2"] sum.If_cases)

lemma bounded_linear_axis: "bounded_linear (axis i)"
proof
  show "axis i (x + y) = axis i x + axis i y" "axis i (r *\<^sub>R x) = r *\<^sub>R axis i x" for x y :: "'a" and r
    by (auto simp: vec_eq_iff axis_def)
  show "\<exists>K. \<forall>x::'a. norm (axis i x) \<le> norm x * K"
    by (auto simp add: norm_axis intro!: exI[of _ 1])
qed

lemma bounded_linear_vec:
  fixes f::"('a::finite) \<Rightarrow> 'b::real_normed_vector \<Rightarrow> 'c::real_normed_vector"
  assumes bounds:"\<And>i. bounded_linear (f i)"
  shows "bounded_linear (\<lambda>x. \<chi> i. f i x)"
proof unfold_locales
  fix r x y
  interpret bounded_linear "f i" for i by fact
  show "(\<chi> i. f i (x + y)) = (\<chi> i. f i x) + (\<chi> i. f i y)"
    by (vector add)
  show "(\<chi> i. f i (r *\<^sub>R x)) = r *\<^sub>R (\<chi> i. f i x)"
    by (vector scaleR)
  obtain K where "norm (f i x) \<le> norm x * K i" for x i
    using bounded by metis
  then have "norm (\<chi> i. f i x) \<le> norm x * (\<Sum>i\<in>UNIV. K i)" (is "?lhs \<le> ?rhs") for x
    unfolding sum_distrib_left
    unfolding norm_vec_def
    by (auto intro!: L2_set_le_sum_abs[THEN order_trans] sum_mono simp: abs_mult)
  then show "\<exists>K. \<forall>x. norm (\<chi> i. f i x) \<le> norm x * K"
    by blast
qed

lift_definition blinfun_vec::"('a::finite \<Rightarrow> 'b::real_normed_vector \<Rightarrow>\<^sub>L real) \<Rightarrow> 'b \<Rightarrow>\<^sub>L (real ^ 'a)" is "(\<lambda>(f::('a \<Rightarrow> 'b \<Rightarrow> real)) (x::'b). \<chi> (i::'a). f i x)"
  by(rule bounded_linear_vec, simp)  

lemmas blinfun_vec_simps[simp] = blinfun_vec.rep_eq

lemma continuous_blinfun_vec:"(\<And>i. continuous_on UNIV (blinfun_apply (g i))) \<Longrightarrow> continuous_on UNIV (blinfun_vec g)"
  by (simp add: continuous_on_vec_lambda)  

lemma blinfun_elim:"\<And>g. (blinfun_apply (blinfun_vec g)) = (\<lambda>x. \<chi> i. g i x)"
  using blinfun_vec.rep_eq by auto

lemma sup_plus:
  fixes f g::"('b::metric_space) \<Rightarrow> real"
  assumes nonempty:"R \<noteq> {}"
  assumes bddf:"bdd_above (f ` R)"
  assumes bddg:"bdd_above (g ` R)"
  shows "(SUP x\<in>R. f x  + g x) \<le> (SUP x\<in>R. f x) + (SUP x\<in>R. g x)"
proof -
  have bddfg:"bdd_above((\<lambda>x. f x + g x ) ` R)" 
    using bddf bddg apply (auto simp add: bdd_above_def)
    using add_mono_thms_linordered_semiring(1) by blast
  have eq:"(SUP x\<in>R. f x + g x) \<le> (SUP x\<in>R. f x) + (SUP x\<in>R. g x)
    \<longleftrightarrow> (\<forall>x\<in>R. (f x + g x) \<le> (SUP x\<in>R. f x) + (SUP x\<in>R. g x))"
    apply(rule cSUP_le_iff)
     subgoal by (rule nonempty)
    subgoal by (rule bddfg)
    done
  have fs:"\<And>x. x \<in> R \<Longrightarrow> f x \<le> (SUP x\<in>R. f x)"
    using bddf 
    by (simp add: cSUP_upper)
  have gs:"\<And>x. x \<in> R \<Longrightarrow> g x \<le> (SUP x\<in>R. g x)"
    using bddg
    by (simp add: cSUP_upper)
  have "(\<forall>x\<in>R. (f x + g x) \<le> (SUP x\<in>R. f x) + (SUP x\<in>R. g x))"
    apply auto                    
    subgoal for x using fs[of x] gs[of x] by auto
    done
  then show ?thesis by (auto simp add: eq)
qed
     
lemma continuous_blinfun_vec':
  fixes f::"'a::{finite,linorder} \<Rightarrow> 'b::{metric_space, real_normed_vector,abs} \<Rightarrow> 'b \<Rightarrow>\<^sub>L real"
  fixes S::"'b set"
  assumes conts:"\<And>i. continuous_on UNIV (f i)"
  shows "continuous_on UNIV (\<lambda>x. blinfun_vec (\<lambda> i. f i x))"
proof (auto simp add:  LIM_def continuous_on_def)
  fix x1 and \<epsilon>::real
  assume \<epsilon>:"0 < \<epsilon>"
  let ?n = "card (UNIV::'a set)"
  have conts':" \<And>i x1 \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>\<delta>>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < \<epsilon>"  
    using conts by(auto simp add: LIM_def continuous_on_def)
  have conts'':"\<And>i. \<exists>\<delta>>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n)"
    subgoal for i using conts'[of "\<epsilon> / ?n"  x1 i] \<epsilon> by auto done
  let ?f = "(\<lambda>x. blinfun_vec (\<lambda> i. f i x))"
  let ?P\<delta> = "(\<lambda> i \<delta>. (\<delta>>0 \<and> (\<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < \<delta> \<longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n))))"
  let ?\<delta>i = "(\<lambda>i. SOME \<delta>. ?P\<delta> i \<delta>)"
  have Ps:"\<And>i. \<exists>\<delta>. ?P\<delta> i \<delta>" using conts'' by auto
  have P\<delta>i:"\<And>i. ?P\<delta> i (?\<delta>i i)"
    subgoal for i using someI[of "?P\<delta> i" ] Ps[of i] by auto done
  have finU:"finite (UNIV::'a set)" by auto
  let ?\<delta> = "linorder_class.Min  (?\<delta>i ` UNIV)"
  have \<delta>0s:"\<And>i. ?\<delta>i i > 0" using P\<delta>i by blast
  then have \<delta>0s':"\<And>i. 0 < ?\<delta>i i" by auto
  have bounds:"bdd_below (?\<delta>i ` UNIV)" 
    unfolding bdd_below_def 
    using \<delta>0s less_eq_real_def by blast
  have \<delta>s:"\<And>i. ?\<delta> \<le> ?\<delta>i i"
    using bounds cINF_lower[of ?\<delta>i] by auto
  have finite:"finite ((?\<delta>i ` UNIV))" by auto
  have nonempty:"((?\<delta>i ` UNIV)) \<noteq> {}" by auto
  have \<delta>:"?\<delta> > 0 " using Min_gr_iff[OF finite nonempty] \<delta>0s' 
    by blast
  have conts''':"\<And>i x2. x2 \<noteq> x1 \<Longrightarrow> dist x2 x1 < ?\<delta>i i \<Longrightarrow> dist (f i  x2) (f i x1) < (\<epsilon>/?n)"
    subgoal for i x2 
      using conts''[of i] apply auto
      subgoal for \<delta>
        apply(erule allE[where x=x2])
        using P\<delta>i  \<delta>s[of i] apply (auto simp add: \<delta>s[of i])
        done
      done
    done
  have "\<And>x2. x2 \<noteq> x1 \<and> dist x2 x1 < ?\<delta> \<Longrightarrow> dist (blinfun_vec (\<lambda>i. f i x2)) (blinfun_vec (\<lambda>i. f i x1)) < \<epsilon>"
  proof (auto)
    fix x2
    assume ne:"x2 \<noteq> x1"
    assume dist:"\<forall>i. dist x2 x1 < ?\<delta>i i"
    have dists:"\<And>i. dist x2 x1 < ?\<delta>i i"
      subgoal for i using dist \<delta>s[of i] by auto done
    have euclid:"\<And>y. norm(?f x1 y - ?f x2 y) = (L2_set (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)"
      by (simp add: norm_vec_def)
    have finite:"finite (UNIV::'a set)" by auto
    have nonempty: "(UNIV::'a set) \<noteq> {}" by auto
    have nonemptyB: "(UNIV::'b set) \<noteq> {}" by auto
    have nonemptyR: "(UNIV::real set) \<noteq> {}" by auto
    have SUP_leq:"\<And>f::('b \<Rightarrow> real). \<And> g::('b \<Rightarrow> real). \<And> S::'b set. S \<noteq> {} \<Longrightarrow> bdd_above (g ` S) \<Longrightarrow> (\<And>x. x \<in> (S::'b set) \<Longrightarrow> ((f x)::real) \<le> ((g x)::real)) \<Longrightarrow> (SUP x\<in>S. f x) \<le> (SUP x\<in>S. g x)"
      by(rule cSup_mono, auto)
    have SUP_sum_comm':"\<And>R S f . finite (S::'a set) \<Longrightarrow> (R::'d::metric_space set) \<noteq> {} \<Longrightarrow>
      (\<And>i x. ((f i x)::real) \<ge> 0) \<Longrightarrow>
      (\<And>i. bdd_above (f i ` R)) \<Longrightarrow>
      (SUP x\<in>R . (\<Sum>i \<in> S. f i x)) \<le> (\<Sum>i \<in> S. (SUP x\<in>R. f i x))"
    proof -
      fix  R::"'d set" and S ::"('a)set"  and f  ::"'a \<Rightarrow> 'd \<Rightarrow> real"
      assume non:"R \<noteq> {} "
      assume fin:"finite S"
      assume every:"(\<And>i x. 0 \<le> f i x)"
      assume bddF:"\<And>i. bdd_above (f i ` R)"
      then have bddF':"\<And>i. \<exists>M. \<forall>x \<in>R. f i x \<le> M "
        unfolding bdd_above_def by auto
      let ?boundP = "(\<lambda>i M. \<forall>x \<in>R. f i x \<le> M)"
      let ?bound = "(\<lambda>i::'a. SOME M. \<forall>x \<in>R. f i x \<le> M)"
      have "\<And>i. \<exists>M. ?boundP i M" using bddF' by auto
      then have each_bound:"\<And>i. ?boundP i (?bound i)" 
        subgoal for i using someI[of "?boundP i"] by blast done
      let ?bigBound = "(\<lambda>F. \<Sum>i\<in>F. (?bound i))"
      have bddG:"\<And>i::'a. \<And>F. bdd_above ((\<lambda>x. \<Sum>i\<in>F. f i x) ` R)" 
        subgoal for i F
          using bddF[of i] unfolding bdd_above_def apply auto
          apply(rule exI[where x="?bigBound F"])
          subgoal for M
            apply auto
            subgoal for x
              using each_bound by (simp add: sum_mono)
            done
          done
        done
      show "?thesis R S f" using fin assms
      proof (induct)
        case empty
        have "((SUP x\<in>R. \<Sum>i\<in>{}. f i x)::real) \<le> (\<Sum>i\<in>{}. SUP a\<in>R. f i a)"   by (simp add: non)
        then show ?case by auto
      next
        case (insert x F)
        have "((SUP xa\<in>R. \<Sum>i\<in>insert x F. f i xa)::real) \<le> (SUP xa\<in>R. f x xa +  (\<Sum>i\<in>F. f i xa))"
          using insert.hyps(2) by auto
        moreover have "...  \<le> (SUP xa\<in> R. f x xa) + (SUP xa\<in>R. (\<Sum>i\<in>F. f i xa))"
          by(rule sup_plus, rule non, rule bddF, rule bddG)
        moreover have "... \<le> (SUP xa\<in> R. f x xa) + (\<Sum>i\<in>F. SUP a\<in>R. f i a)"
          using add_le_cancel_left conts insert.hyps(3) by blast
        moreover have "... \<le> (\<Sum>i\<in>(insert x F). SUP a\<in>R. f i a)"
          by (simp add: insert.hyps(2))
        ultimately have "((SUP xa\<in>R. \<Sum>i\<in>insert x F. f i xa)::real) \<le> (\<Sum>i\<in>(insert x F). SUP a\<in>R. f i a)"
          by linarith
        then show ?case by auto
      qed
    qed
    have SUP_sum_comm:"\<And>R S y1 y2 . finite (S::'a set) \<Longrightarrow> (R::'b set) \<noteq> {} \<Longrightarrow> (SUP x\<in>R . (\<Sum>i \<in> S. norm(f i y1 x - f i y2 x)/norm(x))) \<le> (\<Sum>i \<in> S. (SUP x\<in>R. norm(f i y1 x - f i y2 x)/norm(x)))"
      apply(rule SUP_sum_comm')
         apply(auto)[3]
      proof (unfold bdd_above_def)
        fix R S y1 y2 i
          { fix rr :: "real \<Rightarrow> real"
            obtain bb :: "real \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> 'b set \<Rightarrow> 'b" where
              ff1: "\<And>r f B. r \<notin> f ` B \<or> f (bb r f B) = r"
              by moura
            { assume "\<exists>r. \<not> rr r \<le> norm (f i y1 - f i y2)"
              then have "\<exists>r. norm (blinfun_apply (f i y1) (bb (rr r) (\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) R) - blinfun_apply (f i y2) (bb (rr r) (\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) R)) / norm (bb (rr r) (\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) R) \<noteq> rr r"
                by (metis (no_types) le_norm_blinfun minus_blinfun.rep_eq)
              then have "\<exists>r. rr r \<le> r \<or> rr r \<notin> (\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) ` R"
                using ff1 by meson }
              then have "\<exists>r. rr r \<le> r \<or> rr r \<notin> (\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) ` R"
                by blast }
        then show "\<exists>r. \<forall>ra\<in>(\<lambda>b. norm (blinfun_apply (f i y1) b - blinfun_apply (f i y2) b) / norm b) ` R. ra \<le> r"
          by meson
      qed
    have SUM_leq:"\<And>S::('a) set. \<And> f g ::('a \<Rightarrow> real). S \<noteq> {} \<Longrightarrow> finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> f x < g x) \<Longrightarrow> (\<Sum>x\<in>S. f x) < (\<Sum>x\<in>S. g x)"
      by(rule sum_strict_mono, auto)
    have L2:"\<And>f S. L2_set (\<lambda>x. norm(f x)) S \<le> (\<Sum>x \<in> S. norm(f x))"
      using L2_set_le_sum norm_ge_zero by metis
    have L2':"\<And>y. (L2_set (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)/norm(y) \<le> (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y)"
      subgoal for y
        using L2[of "(\<lambda> x. f x x1 y - f x x2 y)" UNIV]
        by (auto simp add: divide_right_mono)
      done
    have "\<And>i. (SUP y\<in>UNIV.  norm((f i x1 - f i x2) y)/norm(y)) = norm(f i x1 - f i x2)"
      by (simp add: onorm_def norm_blinfun.rep_eq)
    then have each_norm:"\<And>i. (SUP y\<in>UNIV.  norm(f i x1 y - f i x2 y)/norm(y)) = norm(f i x1 - f i x2)"
      by (metis (no_types, lifting) SUP_cong blinfun.diff_left)
    have bounded_linear:"\<And>i. bounded_linear (\<lambda>y. f i x1 y - f i x2 y)" 
      by (simp add: blinfun.bounded_linear_right bounded_linear_sub)
    have each_bound:"\<And>i. bdd_above ((\<lambda>y. norm(f i x1 y - f i x2 y)/norm(y)) ` UNIV)"
      using bounded_linear unfolding bdd_above_def
    proof -
      fix i :: 'a
      { fix rr :: "real \<Rightarrow> real"
        have "\<And>a r. norm (blinfun_apply (f a x1) r - blinfun_apply (f a x2) r) / norm r \<le> norm (f a x1 - f a x2)"
          by (metis le_norm_blinfun minus_blinfun.rep_eq)
        then have "\<And>r R. r \<notin> (\<lambda>r. norm (blinfun_apply (f i x1) r - blinfun_apply (f i x2) r) / norm r) ` R \<or> r \<le> norm (f i x1 - f i x2)"
          by blast
        then have "\<exists>r. rr r \<le> r \<or> rr r \<notin> range (\<lambda>r. norm (blinfun_apply (f i x1) r - blinfun_apply (f i x2) r) / norm r)"
          by blast }
      then show "\<exists>r. \<forall>ra\<in>range (\<lambda>r. norm (blinfun_apply (f i x1) r - blinfun_apply (f i x2) r) / norm r). ra \<le> r"
        by meson
    qed
    have bdd_above:"(bdd_above ((\<lambda>y. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y)/norm(y))) ` UNIV))"
      using each_bound unfolding bdd_above_def apply auto
    proof -
      assume each:"(\<And>i. \<exists>M. \<forall>x. \<bar>blinfun_apply (f i x1) x - blinfun_apply (f i x2) x\<bar> / norm x \<le> M)"
      let ?boundP = "(\<lambda>i M. \<forall>x. \<bar>blinfun_apply (f i x1) x - blinfun_apply (f i x2) x\<bar> / norm x \<le> M)"
      let ?bound = "(\<lambda>i. SOME x. ?boundP i x)"
      have bounds:"\<And>i. ?boundP i (?bound i)"
        subgoal for i using each someI[of "?boundP i"] by blast done
      let ?bigBound = "\<Sum>i\<in>(UNIV::'a set). ?bound i"
      show "\<exists>M. \<forall>x. (\<Sum>i\<in>UNIV. \<bar>blinfun_apply (f i x1) x - blinfun_apply (f i x2) x\<bar> / norm x) \<le> M"
        apply(rule exI[where x= ?bigBound])
        by(auto simp add: bounds sum_mono) 
    qed
    have bdd_above:"(bdd_above ((\<lambda>y. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y)) ` UNIV))"
      using bdd_above unfolding bdd_above_def apply auto
    proof -
      fix M :: real
      assume a1: "\<forall>x. (\<Sum>i\<in>UNIV. \<bar>blinfun_apply (f i x1) x - blinfun_apply (f i x2) x\<bar> / norm x) \<le> M"
      { fix bb :: "real \<Rightarrow> 'b"
        have "\<And>b. (\<Sum>a\<in>UNIV. \<bar>blinfun_apply (f a x1) b - blinfun_apply (f a x2) b\<bar>) / norm b \<le> M"
          using a1 by (simp add: sum_divide_distrib)
        then have "\<exists>r. (\<Sum>a\<in>UNIV. \<bar>blinfun_apply (f a x1) (bb r) - blinfun_apply (f a x2) (bb r)\<bar>) / norm (bb r) \<le> r"
          by blast }
      then show "\<exists>r. \<forall>b. (\<Sum>a\<in>UNIV. \<bar>blinfun_apply (f a x1) b - blinfun_apply (f a x2) b\<bar>) / norm b \<le> r"
        by meson
    qed 
    have "dist (?f x2) (?f x1) = norm((?f x2) - (?f x1))"
      by (simp add: dist_blinfun_def)
    moreover have "... = (SUP y\<in>UNIV. norm(?f x1 y - ?f x2 y)/norm(y))"
      by (metis (no_types, lifting) SUP_cong blinfun.diff_left norm_blinfun.rep_eq norm_minus_commute onorm_def)
    moreover have "... = (SUP y\<in>UNIV. (L2_set (\<lambda>i. norm(f i x1 y - f i x2 y)) UNIV)/norm(y))"
      using  euclid by auto
    moreover have "... \<le> (SUP y\<in>UNIV. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y))/norm(y))"
      using L2' SUP_cong SUP_leq bdd_above by auto
    moreover have "... = (SUP y\<in>UNIV. (\<Sum>i\<in>UNIV. norm(f i x1 y - f i x2 y)/norm(y)))"
      by (simp add: sum_divide_distrib)
    moreover have "... \<le> (\<Sum>i\<in>UNIV. (SUP y\<in>UNIV.  norm(f i x1 y - f i x2 y)/norm(y)))"
      by(rule SUP_sum_comm[OF finite  nonemptyB, of x1 x2]) 
    moreover have "... = (\<Sum>i\<in>UNIV. norm(f i x1 - f i x2))"
      using each_norm by simp
    moreover have "... = (\<Sum>i\<in>UNIV. dist(f i x1) (f i x2))"
      by (simp add: dist_blinfun_def)
    moreover have "... < (\<Sum>i\<in>(UNIV::'a set). \<epsilon> / ?n)"
      using conts'''[OF ne dists] using SUM_leq[OF nonempty, of "(\<lambda>i.  dist (f i x1) (f i x2))" "(\<lambda>i.  \<epsilon> / ?n)"]
      by (simp add: dist_commute)
    moreover have "... = \<epsilon>"
      by(auto)
    ultimately show "dist (?f x2) (?f x1) < \<epsilon>"
      by linarith
  qed
  then show "\<exists>s>0. \<forall>x2. x2 \<noteq> x1 \<and> dist x2 x1 < s \<longrightarrow> dist (blinfun_vec (\<lambda>i. f i x2)) (blinfun_vec (\<lambda>i. f i x1)) < \<epsilon>"
    using \<delta> by blast
qed

lemma has_derivative_vec[derivative_intros]:
  assumes "\<And>i. ((\<lambda>x. f i x) has_derivative (\<lambda>h. f' i h)) F"
  shows "((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
proof -
  have *: "(\<chi> i. f i x) = (\<Sum>i\<in>UNIV. axis i (f i x))" "(\<chi> i. f' i x) = (\<Sum>i\<in>UNIV. axis i (f' i x))" for x
    by (simp_all add: axis_def sum.If_cases vec_eq_iff)
  show ?thesis
    unfolding *
    by (intro has_derivative_sum bounded_linear.has_derivative[OF bounded_linear_axis] assms)
qed

lemma has_derivative_proj:
  fixes j::"('a::finite)" 
  fixes f::"'a \<Rightarrow> real \<Rightarrow> real"
  assumes assm:"((\<lambda>x. \<chi> i. f i x) has_derivative (\<lambda>h. \<chi> i. f' i h)) F"
  shows "((\<lambda>x. f j x) has_derivative (\<lambda>h. f' j h)) F"
proof -
  have bounded_proj:"bounded_linear (\<lambda> x::(real^'a). x $ j)"
    by (simp add: bounded_linear_vec_nth)
  show "?thesis"
    using bounded_linear.has_derivative[OF bounded_proj, of "(\<lambda>x. \<chi> i. f i x)" "(\<lambda>h. \<chi> i. f' i h)", OF assm]
    by auto
qed

lemma has_derivative_proj':
  fixes i::"'a::finite"
  shows "\<forall>x. ((\<lambda> x. x $ i) has_derivative (\<lambda>x::(real^'a). x $ i)) (at x)"
proof -
  have bounded_proj:"bounded_linear (\<lambda> x::(real^'a). x $ i)"
    by (simp add: bounded_linear_vec_nth)
  show "?thesis"
    using bounded_proj unfolding has_derivative_def by auto
qed

lemma constant_when_zero:
  fixes v::"real \<Rightarrow> (real, 'i::finite) vec"
  assumes x0: "(v t0) $ i = x0"
  assumes sol: "(v solves_ode f) T S"
  assumes f0: "\<And>s x. s \<in> T \<Longrightarrow> f s x $ i = 0"
  assumes t0:"t0 \<in> T"
  assumes t:"t \<in> T"
  assumes convex:"convex T"
  shows "v t $ i = x0"
proof -
  from solves_odeD[OF sol]
  have deriv: "(v has_vderiv_on (\<lambda>t. f t (v t))) T" by simp
  then have "((\<lambda>t. v t $ i) has_vderiv_on (\<lambda>t. 0)) T"
    using f0
    by (auto simp: has_vderiv_on_def has_vector_derivative_def cart_eq_inner_axis
      intro!: derivative_eq_intros)
  from has_vderiv_on_zero_constant[OF convex this]
  obtain c where c:"\<And>x. x \<in> T \<Longrightarrow> v x $ i = c" by blast
  with x0 have "c = x0" "v t $ i = c"
    using t t0 c x0 by blast+
  then show ?thesis by simp
qed

lemma
  solves_ode_subset:
  assumes x: "(x solves_ode f) T X"
  assumes s: "S \<subseteq> T"
  shows "(x solves_ode f) S X"
  apply(rule solves_odeI)
   using has_vderiv_on_subset s solves_ode_vderivD x apply force
  using assms by (auto intro!: solves_odeI dest!: solves_ode_domainD)

lemma
  solves_ode_supset_range:
  assumes x: "(x solves_ode f) T X"
  assumes y: "X \<subseteq> Y"
  shows "(x solves_ode f) T Y"
  apply(rule solves_odeI)
   using has_vderiv_on_subset y solves_ode_vderivD x apply force
  using assms by (auto intro!: solves_odeI dest!: solves_ode_domainD)

lemma
  usolves_ode_subset:
  assumes x: "(x usolves_ode f from t0) T X"
  assumes s: "S \<subseteq> T"
  assumes t0: "t0 \<in> S"
  assumes S: "is_interval S"
  shows "(x usolves_ode f from t0) S X"
proof (rule usolves_odeI)
  note usolves_odeD[OF x]
  show "(x solves_ode f) S X" by (rule solves_ode_subset; fact)
  show "t0 \<in> S" "is_interval S" by(fact+)
  fix z t
  assume s: "{t0 -- t} \<subseteq> S" and z: "(z solves_ode f) {t0 -- t} X" and z0: "z t0 = x t0"
  then have "t0 \<in> {t0 -- t}" "is_interval {t0 -- t}"
    by auto
  moreover note s
  moreover have "(z solves_ode f) {t0--t} X"
    using solves_odeD[OF z] \<open>S \<subseteq> T\<close>
    by (intro solves_ode_subset_range[OF z]) force
  moreover note z0
  moreover have "t \<in> {t0 -- t}" by simp
  ultimately show "z t = x t"
    by (meson \<open>\<And>z ta T'. \<lbrakk>t0 \<in> T'; is_interval T'; T' \<subseteq> T; (z solves_ode f) T' X; z t0 = x t0; ta \<in> T'\<rbrakk> \<Longrightarrow> z ta = x ta\<close> assms(2) dual_order.trans)
qed

\<comment> \<open>Example of using lemmas above to show a lemma that could be useful for dL: The constant ODE\<close>
\<comment> \<open>0 does not change the state.\<close>
lemma example:
  fixes x t::real and i::"('sz::finite)"
  assumes "t > 0"
  shows "x = (ll_on_open.flow UNIV (\<lambda>t. \<lambda>x. \<chi> (i::('sz::finite)). 0) UNIV 0 (\<chi> i. x) t) $ i"
proof -
  let ?T = UNIV
  let ?f = "(\<lambda>t. \<lambda>x. \<chi> i::('sz::finite). 0)"
  let ?X = UNIV
  let ?t0.0 = 0
  let ?x0.0 = "\<chi> i::('sz::finite). x"
  interpret ll: ll_on_open "UNIV" "(\<lambda>t x. \<chi> i::('sz::finite). 0)" UNIV
    using gt_ex
    by unfold_locales
      (auto simp: interval_def continuous_on_def local_lipschitz_def intro!: lipschitz_intros)
  have foo1:"?t0.0 \<in> ?T" by auto
  have foo2:"?x0.0 \<in> ?X" by auto
  let ?v = "ll.flow  ?t0.0 ?x0.0"
  from ll.flow_solves_ode[OF foo1 foo2]
  have solves:"(ll.flow  ?t0.0 ?x0.0 solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X"  by (auto)
  then have solves:"(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" by auto
  have thex0: "(?v ?t0.0) $ (i::('sz::finite)) = x" by auto
  have sol_help: "(?v solves_ode ?f) (ll.existence_ivl  ?t0.0 ?x0.0) ?X" using solves by auto
  have ivl:"ll.existence_ivl ?t0.0 ?x0.0 = UNIV"
    by (rule ll.existence_ivl_eq_domain)
       (auto intro!: exI[where x=0] simp: vec_eq_iff)
  have sol: "(?v solves_ode ?f) UNIV ?X" using solves ivl by auto
  have thef0: "\<And>t x. ?f t x $ i = 0" by auto
  from constant_when_zero [OF thex0 sol thef0]
  have "?v t $ i = x"
    by auto
  thus ?thesis by auto
 qed
 
lemma MVT_ivl:
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D)"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x u \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> a + x *\<^sub>R u \<in> D"
  shows "f (a + u) - f a \<ge> J0"
proof -
  from MVT_corrected[OF fderiv line_in] obtain t where
    t: "t\<in>Basis \<rightarrow> {0<..<1}" and
    mvt: "f (a + u) - f a = (\<Sum>i\<in>Basis. (J (a + t i *\<^sub>R u) u \<bullet> i) *\<^sub>R i)"
    by auto
  note mvt
  also have "\<dots> \<ge> J0"
  proof -
    have J: "\<And>i. i \<in> Basis \<Longrightarrow> J0 \<le> J (a + t i *\<^sub>R u) u"
      using J_ivl t line_in by (auto simp: Pi_iff)
    show ?thesis
      using J
      unfolding atLeastAtMost_iff eucl_le[where 'a='b]
      by auto
  qed
  finally show ?thesis .
qed

lemma MVT_ivl':
  fixes f::"'a::ordered_euclidean_space\<Rightarrow>'b::ordered_euclidean_space"
  assumes fderiv: "(\<And>x. x \<in> D \<Longrightarrow> (f has_derivative J x) (at x within D))"
  assumes J_ivl: "\<And>x. x \<in> D \<Longrightarrow> J x (a - b) \<ge> J0"
  assumes line_in: "\<And>x. x \<in> {0..1} \<Longrightarrow> b + x *\<^sub>R (a - b) \<in> D"
  shows "f a \<ge> f b + J0"
proof -
  have "f (b + (a - b)) - f b \<ge> J0"
    apply (rule MVT_ivl[OF fderiv ])
      apply assumption
     apply (rule J_ivl) apply assumption
    using line_in
    apply (auto simp: diff_le_eq le_diff_eq ac_simps)
    done
  thus ?thesis
    by (auto simp: diff_le_eq le_diff_eq ac_simps)
qed
end
