theory PTA
  imports "library/Lib"
begin

section \<open>Bisimulation on a Relation\<close> text_raw \<open>\label{thm:bisim}\<close>

definition rel_set_strong :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "rel_set_strong R A B \<longleftrightarrow> (\<forall>x y. R x y \<longrightarrow> (x \<in> A \<longleftrightarrow> y \<in> B))"

lemma T_eq_rel_half[consumes 4, case_names prob sets cont]:
  fixes R :: "'s \<Rightarrow> 't \<Rightarrow> bool" and f :: "'s \<Rightarrow> 't" and S :: "'s set"
  assumes R_def: "\<And>s t. R s t \<longleftrightarrow> (s \<in> S \<and> f s = t)"
  assumes A[measurable]: "A \<in> sets (stream_space (count_space UNIV))"
    and B[measurable]: "B \<in> sets (stream_space (count_space UNIV))"
    and AB: "rel_set_strong (stream_all2 R) A B" and KL: "rel_fun R (rel_pmf R) K L" and xy: "R x y"
  shows "MC_syntax.T K x A = MC_syntax.T L y B"
proof -
  interpret K: MC_syntax K by unfold_locales
  interpret L: MC_syntax L by unfold_locales

  have "x \<in> S" using \<open>R x y\<close> by (auto simp: R_def)

  define g where "g t = (SOME s. R s t)" for t
  have measurable_g: "g \<in> count_space UNIV \<rightarrow>\<^sub>M count_space UNIV" by auto
  have g: "R i j \<Longrightarrow> R (g j) j" for i j
    unfolding g_def by (rule someI)
  
  have K_subset: "x \<in> S \<Longrightarrow> K x \<subseteq> S" for x
    using KL[THEN rel_funD, of x "f x", THEN rel_pmf_imp_rel_set] by (auto simp: rel_set_def R_def)

  have in_S: "AE \<omega> in K.T x. \<omega> \<in> streams S"
    using K.AE_T_enabled
  proof eventually_elim 
    case (elim \<omega>) with \<open>x \<in> S\<close> show ?case
      apply (coinduction arbitrary: x \<omega>)
      subgoal for x \<omega> using K_subset by (cases \<omega>) (auto simp: K.enabled_Stream)
      done
  qed

  have L_eq: "L y = map_pmf f (K x)" if xy: "R x y" for x y
  proof -
    have "rel_pmf (\<lambda>x y. x = y) (map_pmf f (K x)) (L y)"
      using KL[THEN rel_funD, OF xy] by (auto intro: pmf.rel_mono_strong simp: R_def pmf.rel_map)
    then show ?thesis unfolding pmf.rel_eq by simp
  qed

  let ?D = "\<lambda>x. distr (K.T x) K.S (smap f)"
  have prob_space_D: "?D x \<in> space (prob_algebra K.S)" for x 
    by (auto simp: space_prob_algebra K.T.prob_space_distr)

  have D_eq_D: "?D x = ?D x'" if "R x y" "R x' y" for x x' y
  proof (rule stream_space_eq_sstart)
    define A where "A = K.acc `` {x, x'}"
    have x_A: "x \<in> A" "x' \<in> A" by (auto simp: A_def)
    let ?\<Omega> = "f ` A"
    show "countable ?\<Omega>"
      unfolding A_def by (intro countable_image K.countable_acc) auto
    show "prob_space (?D x)" "prob_space (?D x')" by (auto intro!: K.T.prob_space_distr)
    show "sets (?D x) = sets L.S" "sets (?D x') = sets L.S" by auto
    have AE_streams: "AE x in ?D x''. x \<in> streams ?\<Omega>" if "x'' \<in> A" for x''
      apply (simp add: space_stream_space streams_sets AE_distr_iff)
      using K.AE_T_reachable[of x''] unfolding alw_HLD_iff_streams
    proof eventually_elim
      fix s assume "s \<in> streams (K.acc `` {x''})"
      moreover have "K.acc `` {x''} \<subseteq> A"
        using \<open>x'' \<in> A\<close> by (auto simp: A_def Image_def intro: rtrancl_trans)
      ultimately show "smap f s \<in> streams (f ` A)"
        by (auto intro: smap_streams)
    qed
    with x_A show "AE x in ?D x'. x \<in> streams ?\<Omega>" "AE x in ?D x. x \<in> streams ?\<Omega>"
      by auto
    from \<open>x \<in> A\<close> \<open>x' \<in> A\<close> that show "?D x (sstart (f ` A) xs) = ?D x' (sstart (f ` A) xs)" for xs
    proof (induction xs arbitrary: x x' y)
      case Nil
      moreover have "?D x (streams (f ` A)) = 1" if "x \<in> A" for x
        using AE_streams[of x] that
        by (intro prob_space.emeasure_eq_1_AE[OF K.T.prob_space_distr]) (auto simp: streams_sets)
      ultimately show ?case by simp
    next
      case (Cons z zs x x' y)
      have "rel_pmf (R OO R\<inverse>\<inverse>) (K x) (K x')"
        using KL[THEN rel_funD, OF Cons(4)] KL[THEN rel_funD, OF Cons(5)]
        unfolding pmf.rel_compp pmf.rel_flip by auto
      then obtain p :: "('s \<times> 's) pmf" where p: "\<And>a b. (a, b) \<in> p \<Longrightarrow> (R OO R\<inverse>\<inverse>) a b" and
        eq: "map_pmf fst p = K x" "map_pmf snd p = K x'"
        by (auto simp: pmf.in_rel)
      let ?S = "stream_space (count_space UNIV)"
      have *: "(##) y -` smap f -` sstart (f ` A) (z # zs) = (if f y = z then smap f -` sstart (f ` A) zs else {})" for y z zs
        by auto
      have **: "?D x (sstart (f ` A) (z # zs)) = (\<integral>\<^sup>+ y'. (if f y' = z then ?D y' (sstart (f ` A) zs) else 0) \<partial>K x)" for x
        apply (simp add: emeasure_distr)
        apply (subst K.T_eq_bind)
        apply (subst emeasure_bind[where N="?S"])
           apply simp
          apply (rule measurable_distr2[where M="?S"])
           apply measurable
        apply (intro nn_integral_cong_AE AE_pmfI)
        apply (auto simp add: emeasure_distr)
        apply (simp_all add: * space_stream_space)
        done
      have fst_A: "fst ab \<in> A" if "ab \<in> p" for ab
      proof -
        have "fst ab \<in> K x" using \<open>ab \<in> p\<close> set_map_pmf [of fst p] by (auto simp: eq)
        with \<open>x \<in> A\<close> show "fst ab \<in> A"
          by (auto simp: A_def intro: rtrancl.rtrancl_into_rtrancl)
      qed
      have snd_A: "snd ab \<in> A" if "ab \<in> p" for ab
      proof -
        have "snd ab \<in> K x'" using \<open>ab \<in> p\<close> set_map_pmf [of snd p] by (auto simp: eq)
        with \<open>x' \<in> A\<close> show "snd ab \<in> A"
          by (auto simp: A_def intro: rtrancl.rtrancl_into_rtrancl)
      qed
      show ?case
        unfolding ** eq[symmetric] nn_integral_map_pmf
        apply (intro nn_integral_cong_AE AE_pmfI)
        subgoal for ab using p[of "fst ab" "snd ab"] by (auto simp: R_def intro!: Cons(1) fst_A snd_A)
        done
    qed
  qed

  have L_eq_D: "L.T y = ?D x"
    using \<open>R x y\<close>
  proof (coinduction arbitrary: x y rule: L.T_coinduct)
    case (cont x y)
    then have Kx_Ly: "rel_pmf R (K x) (L y)"
      by (rule KL[THEN rel_funD])
    then have *: "y' \<in> L y \<Longrightarrow> \<exists>x'\<in>K x. R x' y'" for y'
      by (auto dest!: rel_pmf_imp_rel_set simp: rel_set_def)
    have **: "y' \<in> L y \<Longrightarrow> R (g y') y'" for y'
      using *[of y'] unfolding g_def by (auto intro: someI)

    have D_SCons_eq_D_D: "distr (K.T i) K.S (\<lambda>x. z ## smap f x) = distr (?D i) K.S (\<lambda>x. z ## x)" for i z
      by (subst distr_distr) (auto simp: comp_def)
    have D_eq_D_gi: "?D i = ?D (g (f i))" if i: "i \<in> K x" for i
    proof -
      obtain j where "j \<in> L y" "R i j" "f i = j"
        using Kx_Ly i by (force dest!: rel_pmf_imp_rel_set simp: rel_set_def R_def)
      then show ?thesis
        by (auto intro!: D_eq_D[OF \<open>R i j\<close>] g)
    qed

    have ***: "?D x = measure_pmf (L y) \<bind> (\<lambda>y. distr (?D (g y)) K.S ((##) y))"
      apply (subst K.T_eq_bind)
      apply (subst distr_bind[of _ _ K.S])
         apply (rule measurable_distr2[of _  _ "K.S"])
          apply (simp_all add: Pi_iff)
      apply (simp add: distr_distr comp_def L_eq[OF cont] map_pmf_rep_eq)
      apply (subst bind_distr[where K=K.S])
         apply measurable []
        apply (rule measurable_distr2[of _  _ "K.S"])
        apply measurable []
        apply (rule measurable_compose[OF measurable_g])
        apply measurable []
       apply simp
      apply (rule bind_measure_pmf_cong[where N="K.S"])
        apply (auto simp: space_subprob_algebra space_stream_space intro!: K.T.subprob_space_distr)
        unfolding D_SCons_eq_D_D D_eq_D_gi ..
    show ?case
      by (intro exI[of _ "\<lambda>t. distr (K.T (g t)) (stream_space (count_space UNIV)) (smap f)"])
         (auto simp add: K.T.prob_space_distr *** dest: **)
  qed (auto intro: K.T.prob_space_distr)

  have "stream_all2 R s t \<longleftrightarrow> (s \<in> streams S \<and> smap f s = t)" for s t 
  proof safe
    show "stream_all2 R s t \<Longrightarrow> s \<in> streams S"
      apply (coinduction arbitrary: s t)
      subgoal for s t by (cases s; cases t) (auto simp: R_def)
      done
    show "stream_all2 R s t \<Longrightarrow> smap f s = t"
      apply (coinduction arbitrary: s t rule: stream.coinduct)
      subgoal for s t by (cases s; cases t) (auto simp: R_def)
      done
  qed (auto intro!: stream.rel_refl_strong simp: stream.rel_map R_def streams_iff_sset)
  then have "\<omega> \<in> streams S \<Longrightarrow> \<omega> \<in> A \<longleftrightarrow> smap f \<omega> \<in> B" for \<omega>
    using AB by (auto simp: rel_set_strong_def)
  with in_S have "K.T x A = K.T x (smap f -` B \<inter> space (K.T x))"
    by (auto intro!: emeasure_eq_AE streams_sets)
  also have "\<dots> = (distr (K.T x) K.S (smap f)) B"
    by (intro emeasure_distr[symmetric]) auto
  also have "\<dots> = (L.T y) B" unfolding L_eq_D ..
  finally show ?thesis .
qed

no_notation ccval ("\<lbrace>_\<rbrace>" [100])

hide_const succ


section \<open>Additional Facts on Regions\<close>

(* XXX Move this to a theory on Timed Automata *)
declare reset_set11[simp] reset_set1[simp]

text \<open>
  Defining the closest successor of a region. Only exists if at least one interval is upper-bounded.
\<close>

abbreviation is_upper_right where
  "is_upper_right R \<equiv> (\<forall> t \<ge> 0. \<forall> u \<in> R. u \<oplus> t \<in> R)"

(* XXX Remove old successor definition *)
definition
  "succ \<R> R \<equiv>
  if is_upper_right R then R else
  (THE R'. R' \<noteq> R \<and> R' \<in> Succ \<R> R \<and> (\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> R' \<and> 0 \<le> t')))"

lemma region_continuous:
  assumes "valid_region X k I r"
  defines R: "R \<equiv> region X I r"
  assumes between: "0 \<le> t1" "t1 \<le> t2"
  assumes elem: "u \<in> R" "u \<oplus> t2 \<in> R"
  shows "u \<oplus> t1 \<in> R"
unfolding R
proof
  from \<open>0 \<le> t1\<close> \<open>u \<in> R\<close> show "\<forall>x\<in>X. 0 \<le> (u \<oplus> t1) x" by (auto simp: R cval_add_def)

  have "intv_elem x (u \<oplus> t1) (I x)" if "x \<in> X" for x
  proof -
    from elem that have "intv_elem x u (I x)" "intv_elem x (u \<oplus> t2) (I x)" by (auto simp: R)
    with between show ?thesis by (cases "I x", auto simp: cval_add_def)
  qed
  then show "\<forall> x \<in> X. intv_elem x (u \<oplus> t1) (I x)" by blast

  let ?X\<^sub>0 = "{x \<in> X. \<exists>d. I x = Intv d}"
  show "?X\<^sub>0 = ?X\<^sub>0" ..

  from elem have "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac (u x) \<le> frac (u y)" by (auto simp: R)
  moreover
  { fix x y c d assume A: "x \<in> X" "y \<in> X" "I x = Intv c" "I y = Intv d"
    from A elem between have *:
      "c < u x" "u x < c + 1" "c < u x + t1" "u x + t1 < c + 1"
    by (fastforce simp: cval_add_def R)+
    moreover from A(2,4) elem between have **:
      "d < u y" "u y < d + 1" "d < u y + t1" "u y + t1 < d + 1"
    by (fastforce simp: cval_add_def R)+
    ultimately have "u x = c + frac (u x)" "u y = d + frac (u y)" using nat_intv_frac_decomp by auto
    then have
      "frac (u x + t1) = frac (u x) + t1" "frac (u y + t1) = frac (u y) + t1"
    using *(3,4) **(3,4) nat_intv_frac_decomp by force+
    then have
      "frac (u x) \<le> frac (u y) \<longleftrightarrow> frac ((u \<oplus> t1) x) \<le> frac ((u \<oplus> t1) y)"
    by (auto simp: cval_add_def)
  }
  ultimately show
    "\<forall> x \<in> ?X\<^sub>0. \<forall> y \<in> ?X\<^sub>0. (x, y) \<in> r \<longleftrightarrow> frac ((u \<oplus> t1) x) \<le> frac ((u \<oplus> t1) y)"
  by (auto simp: cval_add_def)
qed

lemma upper_right_eq:
  assumes "finite X" "valid_region X k I r"
  shows "(\<forall> x \<in> X. isGreater (I x)) \<longleftrightarrow> is_upper_right (region X I r)"
using assms
proof (safe, goal_cases)
  case (1 t u)
  then show ?case
    by - (standard, force simp: cval_add_def)+
next
  case (2 x)
  (* XXX Does this lemma actually need the finiteness assumption? *)
  from region_not_empty[OF assms] obtain u where u: "u \<in> region X I r" ..
  moreover have "(1 :: real) \<ge> 0" by auto
  ultimately have "(u \<oplus> 1) \<in> region X I r" using 2 by auto
  with \<open>x \<in> X\<close> u have "intv_elem x u (I x)" "intv_elem x (u \<oplus> 1) (I x)" by auto
  then show ?case by (cases "I x", auto simp: cval_add_def)
qed

lemma bounded_region:
  assumes "finite X" "valid_region X k I r"
  defines R: "R \<equiv> region X I r"
  assumes "\<not> is_upper_right R" "u \<in> R"
  shows "u \<oplus> 1 \<notin> R"
proof -
  from upper_right_eq[OF assms(1,2)] assms(4) obtain x where x:
    "x \<in> X" "\<not> isGreater (I x)"
  by (auto simp: R)
  with assms have "intv_elem x u (I x)" by auto
  with x(2) have "\<not> intv_elem x (u \<oplus> 1) (I x)" by (cases "I x", auto simp: cval_add_def)
  with x(1) assms show ?thesis by auto
qed

(* XXX Remove Caml case *)
context AlphaClosure
begin

(* XXX Clean *)
no_notation Regions_Beta.part ("[_]\<^sub>_" [61,61] 61)

lemma succ_ex:
  assumes "R \<in> \<R>"
  shows "succ \<R> R \<in> \<R>" (is "?G1") and "succ \<R> R \<in> Succ \<R> R" (is "?G2")
  and "\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> succ \<R> R \<and> 0 \<le> t')" (is "?G3")
proof -
  from \<open>R \<in> \<R>\<close> obtain I r where R: "R = region X I r" "valid_region X k I r"
    unfolding \<R>_def by auto
  from region_not_empty[OF finite] R obtain u where u: "u \<in> R"
    by blast
  let ?Z = "{x \<in> X . \<exists> c. I x = Const c}"
  let ?succ =
    "\<lambda> R'. R' \<noteq> R \<and> R' \<in> Succ \<R> R
     \<and> (\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> R' \<and> 0 \<le> t'))"
  consider (upper_right) "\<forall> x \<in> X. isGreater (I x)" | (intv) "\<exists> x \<in> X. \<exists> d. I x = Intv d \<and> ?Z = {}"
         | (const) "?Z \<noteq> {}"
  apply (cases "\<forall> x \<in> X. isGreater (I x)")
   apply fast
  apply (cases "?Z = {}")
   apply safe
   apply (rename_tac x)
   apply (case_tac "I x")
  by auto
  then have "?G1 \<and> ?G2 \<and> ?G3"
  proof cases
    case const
    with upper_right_eq[OF finite R(2)] have "\<not> is_upper_right R" by (auto simp: R(1))
    from closest_prestable_1(1,2)[OF const finite R(2)] closest_valid_1[OF const finite R(2)] R(1)
    obtain R' where R':
      "\<forall> u \<in> R. \<forall> t>0. \<exists>t'\<le>t. (u \<oplus> t') \<in> R' \<and> t' \<ge> 0" "R' \<in> \<R>" "\<forall> u \<in> R'. \<forall> t\<ge>0. (u \<oplus> t) \<notin> R"
    unfolding \<R>_def by auto
    with region_not_empty[OF finite] obtain u' where "u' \<in> R'" unfolding \<R>_def by blast
    with R'(3) have neq: "R' \<noteq> R" by (fastforce simp: cval_add_def)
    obtain t:: real where "t > 0" by (auto intro: that[of 1])
    with R'(1,2) \<open>u \<in> R\<close> obtain t where "t \<ge> 0" "u \<oplus> t \<in> R'" by auto
    with \<open>R \<in> \<R>\<close> \<open>R' \<in> \<R>\<close> \<open>u \<in> R\<close> have "R' \<in> Succ \<R> R" by (intro SuccI3)
    moreover have "(\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> R' \<and> 0 \<le> t'))"
      using R'(1) unfolding cval_add_def
      apply clarsimp
      subgoal for u t
        by (cases "t = 0") auto
      done
    ultimately have *: "?succ R'" using neq by auto
    have "succ \<R> R = R'" unfolding succ_def
    proof (simp add: \<open>\<not> is_upper_right R\<close>, intro the_equality, rule *, goal_cases)
      case prems: (1 R'')
      from prems obtain t' u' where R'':
        "R'' \<in> \<R>" "R'' \<noteq> R" "t' \<ge> 0" "R'' = [u' \<oplus> t']\<^sub>\<R>" "u' \<in> R"
      using R'(1) by fastforce
      from this(1) obtain I r where R''2:
        "R'' = region X I r" "valid_region X k I r"
        by (auto simp: \<R>_def)
      from R'' have "u' \<oplus> t' \<notin> R" using assms region_unique_spec by blast
      with * \<open>t' \<ge> 0\<close> \<open>u' \<in> R\<close> obtain t'' where t'': "t'' \<le> t'" "u' \<oplus> t'' \<in> R'" "t'' \<ge> 0" by auto
      from this(2) neq have "u' \<oplus> t'' \<notin> R" using R'(2) assms region_unique_spec by auto
      with t'' prems \<open>u' \<in> R\<close> obtain t''' where t''':
        "t''' \<le> t''" "u' \<oplus> t''' \<in> R''" "t''' \<ge> 0"
      by auto
      with region_continuous[OF R''2(2) _ _ t'''(2)[unfolded R''2(1)], of "t'' - t'''" "t' - t'''"]
           t'' R'' regions_closed'_spec[OF \<open>R \<in> \<R>\<close> R''(5,3)]
      have "u' \<oplus> t'' \<in> R''" by (auto simp: R''2 cval_add_def)
      with t''(2) show ?case using R''(1) R'(2) region_unique_spec by blast
    qed
    with R' * show ?thesis by auto
  next
    case intv
    then have *: "\<forall>x\<in>X. \<not> Regions.isConst (I x)" by auto
    let ?X\<^sub>0 = "{x \<in> X. isIntv (I x)}"
    let ?M = "{x \<in> ?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r}"
    from intv obtain x c where x: "x \<in> X" "\<not> isGreater (I x)" and c: "I x = Intv c" by auto
    with \<open>x \<in> X\<close> have "?X\<^sub>0 \<noteq> {}" by auto
    have "?X\<^sub>0 = {x \<in> X. \<exists>d. I x = Intv d}" by auto
    with R(2) have r: "total_on ?X\<^sub>0 r" "trans r" by auto
    from total_finite_trans_max[OF \<open>?X\<^sub>0 \<noteq> {}\<close> _ this] finite
    obtain x' where x': "x' \<in> ?X\<^sub>0" "\<forall> y \<in> ?X\<^sub>0. x' \<noteq> y \<longrightarrow> (y, x') \<in> r" by fastforce
    from this(2) have "\<forall>y\<in>?X\<^sub>0. (x', y) \<in> r \<longrightarrow> (y, x') \<in> r" by auto
    with x'(1) have **: "?M \<noteq> {}" by fastforce
    with upper_right_eq[OF finite R(2)] have "\<not> is_upper_right R" by (auto simp: R(1))
    from closest_prestable_2(1,2)[OF * finite R(2) **] closest_valid_2[OF * finite R(2) **] R(1)
    obtain R' where R':
      "(\<forall> u \<in> R. \<forall> t \<ge> 0. (u \<oplus> t) \<notin> R \<longrightarrow> (\<exists> t' \<le> t. (u \<oplus> t') \<in> R' \<and> 0 \<le> t'))" "R' \<in> \<R>"
      "\<forall> u \<in> R'. \<forall> t\<ge>0. (u \<oplus> t) \<notin> R"
    unfolding \<R>_def by auto
    with region_not_empty[OF finite] obtain u' where "u' \<in> R'" unfolding \<R>_def by blast
    with R'(3) have neq: "R' \<noteq> R" by (fastforce simp: cval_add_def)
    from bounded_region[OF finite R(2), folded R(1), OF \<open>\<not> is_upper_right R\<close> u] have
      "u \<oplus> (1 :: t) \<notin> R" "(1 :: t) \<ge> 0"
    by auto
    with R'(1) u obtain t' where "t' \<le> (1 :: t)" "(u \<oplus> t') \<in> R'" "0 \<le> t'" by fastforce
    with \<open>R \<in> \<R>\<close> \<open>R' \<in> \<R>\<close> \<open>u \<in> R\<close> have "R' \<in> Succ \<R> R" by (intro SuccI3)
    with R'(1) neq have *: "?succ R'" by auto
    have "succ \<R> R = R'" unfolding succ_def
    proof (simp add: \<open>\<not> is_upper_right R\<close>, intro the_equality, rule *, goal_cases)
      case prems: (1 R'')
      from prems obtain t' u' where R'':
        "R'' \<in> \<R>" "R'' \<noteq> R" "t' \<ge> 0" "R'' = [u' \<oplus> t']\<^sub>\<R>" "u' \<in> R"
      using R'(1) by fastforce
      from this(1) obtain I r where R''2:
        "R'' = region X I r" "valid_region X k I r"
      by (auto simp: \<R>_def)
      from R'' have "u' \<oplus> t' \<notin> R" using assms region_unique_spec by blast
      with * \<open>t' \<ge> 0\<close> \<open>u' \<in> R\<close> obtain t'' where t'': "t'' \<le> t'" "u' \<oplus> t'' \<in> R'" "t'' \<ge> 0" by auto
      from this(2) neq have "u' \<oplus> t'' \<notin> R" using R'(2) assms region_unique_spec by auto
      with t'' prems \<open>u' \<in> R\<close> obtain t''' where t''':
        "t''' \<le> t''" "u' \<oplus> t''' \<in> R''" "t''' \<ge> 0"
      by auto
      with region_continuous[OF R''2(2) _ _ t'''(2)[unfolded R''2(1)], of "t'' - t'''" "t' - t'''"]
           t'' R'' regions_closed'_spec[OF \<open>R \<in> \<R>\<close> R''(5,3)]
      have "u' \<oplus> t'' \<in> R''" by (auto simp: cval_add_def R''2)
      with t''(2) show ?case using R''(1) R'(2) region_unique_spec by blast
    qed
    with R' * show ?thesis by auto
  next
    case upper_right
    with upper_right_eq[OF finite R(2)] have "succ \<R> R = R" by (auto simp: R succ_def)
    with \<open>R \<in> \<R>\<close> u show ?thesis by (fastforce simp: cval_add_def intro: SuccI3)
  qed
  then show ?G1 ?G2 ?G3 by auto
qed
      
lemma region_set'_closed:
  fixes d :: nat
  assumes "R \<in> \<R>" "d \<ge> 0" "\<forall>x\<in>set r. d \<le> k x" "set r \<subseteq> X"
  shows "region_set' R r d \<in> \<R>"
proof -
  from region_not_empty[OF finite] assms(1) obtain u where "u \<in> R" using \<R>_def by blast
  from region_set'_id[OF _ _  finite, of _ k, folded \<R>_def] assms this show ?thesis by fastforce
qed

(* XXX Move *)
lemma clock_set_cong[simp]:
  assumes "\<forall> c \<in> set r. u c = d"
  shows "[r \<rightarrow> d]u = u"
proof standard
  fix c
  from assms show "([r \<rightarrow> d]u) c = u c" by (cases "c \<in> set r"; auto)
qed

lemma region_reset_not_Succ:
  (* XXX Declare globally? *)
  notes regions_closed'_spec[intro]
  assumes "R \<in> \<R>" "set r \<subseteq> X"
  shows "region_set' R r 0 = R \<or> region_set' R r 0 \<notin> Succ \<R> R" (is "?R = R \<or> _")
proof -
  from assms finite obtain u where "u \<in> R" by (meson Succ.cases succ_ex(2))
  with \<open>R \<in> \<R>\<close> have "u \<in> V" "[u]\<^sub>\<R> = R" by (auto simp: region_unique_spec dest: region_V) 
  with region_set'_id[OF \<open>R \<in> \<R>\<close>[unfolded \<R>_def] \<open>u \<in> R\<close> finite] assms(2) have
    "?R = [[r\<rightarrow>0]u]\<^sub>\<R>"
  by (force simp: \<R>_def)
  show ?thesis
  proof (cases "\<forall> x \<in> set r. u x = 0")
    case True
    then have "[r\<rightarrow>0]u = u" by simp
    with \<open>?R = _\<close> \<open>_ = R\<close> have "?R = R" by (force simp: \<R>_def)
    then show ?thesis ..
  next
    case False
    then obtain x where x: "x \<in> set r" "u x \<noteq> 0" by auto
    { assume "?R \<in> Succ \<R> R"
      with \<open>u \<in> R\<close> \<open>R \<in> \<R>\<close> obtain t where
        "t \<ge> 0" "[u \<oplus> t]\<^sub>\<R> = ?R" "?R \<in> \<R>"
      by (meson Succ.cases set_of_regions_spec)
      with \<open>u \<in> R\<close> assms(1) have "u \<oplus> t \<in> ?R" by blast
      moreover from \<open>?R = _\<close> \<open>u \<in> R\<close> have "[r\<rightarrow>0]u \<in> ?R" by (fastforce simp: region_set'_def)
      moreover from x \<open>t \<ge> 0\<close> \<open>u \<in> V\<close> assms have "(u \<oplus> t) x > 0" by (force simp: cval_add_def V_def)
      moreover from x have "([r\<rightarrow>0]u) x = 0" by auto
      ultimately have False using \<open>?R \<in> \<R>\<close> x(1) by (fastforce simp: region_set'_def)
    }
    then show ?thesis by auto
  qed
qed

end (* Alpha Closure global *)

subsection \<open>Justifying Timed Until vs \<^emph>\<open>suntil\<close>\<close>

(* XXX Move *)
lemma guard_continuous:
  assumes "u \<turnstile> g" "u \<oplus> t \<turnstile> g" "0 \<le> (t'::'t::time)" "t' \<le> t"
  shows "u \<oplus> t' \<turnstile> g"
  using assms
  by (induction g;
      auto 4 3
        simp: cval_add_def order_le_less_subst2 order_subst2 add_increasing2
        intro: less_le_trans
     )

(* XXX Move *)
(*
lemma guard_continuous:
  assumes "u \<turnstile> g" "u \<oplus> t \<turnstile> g" "0 \<le> t'" "t' \<le> t"
  shows "u \<oplus> t' \<turnstile> g"
  using assms by (auto 4 4 intro: atomic_guard_continuous simp: list_all_iff)
*)

section \<open>Definition and Semantics\<close>

subsection \<open>Syntactic Definition\<close>

text \<open>
  We do not include:
  \<^item> a labelling function, as we will assume that atomic propositions are simply sets of states
  \<^item> a fixed set of locations or clocks, as we will implicitly derive it from the set of transitions
  \<^item> start or end locations, as we will primarily study reachability
\<close>

type_synonym
  ('c, 't, 's) transition = "'s * ('c, 't) cconstraint * ('c set * 's) pmf"

type_synonym
  ('c, 't, 's) pta = "('c, 't, 's) transition set * ('c, 't, 's) invassn"

definition
  edges :: "('c, 't, 's) transition \<Rightarrow> ('s * ('c, 't) cconstraint * ('c set * 's) pmf * 'c set * 's) set"
where
  "edges \<equiv> \<lambda> (l, g, p). {(l, g, p, X, l') | X l'. (X, l') \<in> set_pmf p}"

definition
  "Edges A \<equiv> \<Union> {edges t | t. t \<in> fst A}"

definition
  trans_of :: "('c, 't, 's) pta \<Rightarrow> ('c, 't, 's) transition set"
where
  "trans_of \<equiv> fst"

definition
  inv_of  :: "('c, 'time, 's) pta \<Rightarrow> ('c, 'time, 's) invassn"
where
  "inv_of \<equiv> snd"

no_notation transition ("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61)

abbreviation transition ::
  "('c, 'time, 's) pta \<Rightarrow> 's \<Rightarrow> ('c, 'time) cconstraint \<Rightarrow> ('c set * 's) pmf \<Rightarrow> 'c set \<Rightarrow> 's \<Rightarrow> bool"
("_ \<turnstile> _ \<longrightarrow>\<^bsup>_,_,_\<^esup> _" [61,61,61,61,61,61] 61) where
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,p,X\<^esup> l') \<equiv> (l, g, p, X, l') \<in> Edges A"

definition
  locations  :: "('c, 't, 's) pta \<Rightarrow> 's set"
where
  "locations A \<equiv> (fst ` Edges A) \<union> ((snd o snd o snd o snd) ` Edges A)"


subsubsection \<open>Collecting Information About Clocks\<close>

(* XXX Remove sort constraints *)

definition collect_clkt :: "('c, 't::time, 's) transition set \<Rightarrow> ('c *'t) set"
where
  "collect_clkt S = \<Union> {collect_clock_pairs (fst (snd t)) | t . t \<in> S}"

definition collect_clki :: "('c, 't :: time, 's) invassn \<Rightarrow> ('c *'t) set"
where
  "collect_clki I = \<Union> {collect_clock_pairs (I x) | x. True}"

definition clkp_set :: "('c, 't :: time, 's) pta \<Rightarrow> ('c * 't) set"
where
  "clkp_set A = collect_clki (inv_of A) \<union> collect_clkt (trans_of A)"

definition collect_clkvt :: "('c, 't :: time, 's) pta \<Rightarrow> 'c set"
where
  "collect_clkvt A = \<Union> ((fst o snd o snd o snd) ` Edges A)"

abbreviation clocks where "clocks A \<equiv> fst ` clkp_set A \<union> collect_clkvt A"

definition valid_abstraction
where
  "valid_abstraction A X k \<equiv>
  (\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>) \<and> collect_clkvt A \<subseteq> X \<and> finite X"

lemma valid_abstractionD[dest]:
  assumes "valid_abstraction A X k"
  shows "(\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>)" "collect_clkvt A \<subseteq> X" "finite X"
using assms unfolding valid_abstraction_def by auto

lemma valid_abstractionI[intro]:
  assumes "(\<forall>(x,m) \<in> clkp_set A. m \<le> k x \<and> x \<in> X \<and> m \<in> \<nat>)" "collect_clkvt A \<subseteq> X" "finite X"
  shows "valid_abstraction A X k"
using assms unfolding valid_abstraction_def by auto

subsection \<open>Operational Semantics as an MDP\<close>

abbreviation (input) clock_set_set :: "'c set \<Rightarrow> 't::time \<Rightarrow> ('c,'t) cval \<Rightarrow> ('c,'t) cval"
("[_:=_]_" [65,65,65] 65)
where
  "[X:=t]u \<equiv> clock_set (SOME r. set r = X) t u"

term region_set'

abbreviation region_set_set :: "'c set \<Rightarrow> 't::time \<Rightarrow> ('c,'t) zone \<Rightarrow> ('c,'t) zone"
("[_::=_]_" [65,65,65] 65)
where
  "[X::=t]R \<equiv> region_set' R (SOME r. set r = X) t"

no_notation zone_set ("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)

abbreviation zone_set_set :: "('c, 't::time) zone \<Rightarrow> 'c set \<Rightarrow> ('c, 't) zone"
("_\<^bsub>_ \<rightarrow> 0\<^esub>" [71] 71)
where
  "Z\<^bsub>X \<rightarrow> 0\<^esub> \<equiv> zone_set Z (SOME r. set r = X)"

abbreviation (input) ccval ("\<lbrace>_\<rbrace>" [100]) where "ccval cc \<equiv> {v. v \<turnstile> cc}"

locale Probabilistic_Timed_Automaton =
  fixes A :: "('c, 't :: time, 's) pta"
  assumes admissible_targets:
    "(l, g, \<mu>) \<in> trans_of A \<Longrightarrow> (X, l') \<in> \<mu> \<Longrightarrow> \<lbrace>g\<rbrace>\<^bsub>X \<rightarrow> 0\<^esub> \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
    "(l, g, \<mu>) \<in> trans_of A \<Longrightarrow> (X, l') \<in> \<mu> \<Longrightarrow> X \<subseteq> clocks A"
  \<comment> \<open>Not necessarily what we want to have\<close>
begin

subsection \<open>Syntactic Definition\<close> text_raw \<open> \label{sem:mdp} \<close>

definition "L = locations A"

definition "\<X> = clocks A"

definition "S \<equiv> {(l, u) . l \<in> L \<and> (\<forall> x \<in> \<X>. u x \<ge> 0) \<and> u \<turnstile> inv_of A l}"

inductive_set
  K :: "('s * ('c, 't) cval) \<Rightarrow> ('s * ('c, 't) cval) pmf set" for st :: "('s * ('c, 't) cval)"
where
  \<comment> \<open>Passage of time\<close> delay:
  "st \<in> S \<Longrightarrow> st = (l, u) \<Longrightarrow> t \<ge> 0 \<Longrightarrow> u \<oplus> t \<turnstile> inv_of A l \<Longrightarrow> return_pmf (l, u \<oplus> t) \<in> K st" |
  \<comment> \<open>Discrete transitions\<close> action:
  "st \<in> S \<Longrightarrow> st = (l, u) \<Longrightarrow> (l, g, \<mu>) \<in> trans_of A \<Longrightarrow> u \<turnstile> g
  \<Longrightarrow> map_pmf (\<lambda> (X, l). (l, ([X := 0]u))) \<mu> \<in> K st" |
  \<comment> \<open>Self loops -- Note that this does not assume \<open>st \<in> S\<close>\<close> loop:
  "return_pmf st \<in> K st"

declare K.intros[intro]

sublocale MDP: Markov_Decision_Process K by (standard, auto)

end (* Probabilistic Timed Automaton *)

section \<open>Constructing the Corresponding Finite MDP on Regions\<close>

locale Probabilistic_Timed_Automaton_Regions =
  Probabilistic_Timed_Automaton A + Regions \<X>
  for A :: "('c, t, 's) pta" +
  \<comment> \<open>The following are necessary to obtain a \<open>finite\<close> MDP\<close>
  assumes finite: "finite \<X>" "finite L" "finite (trans_of A)"
  assumes not_trivial: "\<exists> l \<in> L. \<exists> u \<in> V. u \<turnstile> inv_of A l"
  assumes valid: "valid_abstraction A \<X> k"
begin

lemmas finite_\<R> = finite_\<R>[OF finite(1), of k, folded \<R>_def]


subsection \<open>Syntactic Definition\<close> text_raw \<open> \label{sem:mdprg} \<close>

definition "\<S> \<equiv> {(l, R) . l \<in> L \<and> R \<in> \<R> \<and> R \<subseteq> {u. u \<turnstile> inv_of A l}}"

(* XXX Move definition of V somewhere else *)
lemma S_alt_def: "S = {(l, u) . l \<in> L \<and> u \<in> V \<and> u \<turnstile> inv_of A l}" unfolding V_def S_def by auto

text \<open>
  Note how we relax the definition to allow more transitions in the first case.
  To obtain a more compact MDP the commented out version can be used an proved equivalent.
\<close>

inductive_set
 \<K> :: "('s * ('c, t) cval set) \<Rightarrow> ('s * ('c, t) cval set) pmf set" for st :: "('s * ('c, t) cval set)"
where
  (* 
  -- "Passage of time" delay:
  "st \<in> \<S> \<Longrightarrow> st = (l,R) \<Longrightarrow> succ \<R> R \<subseteq> \<lbrace>inv_of A l\<rbrace> \<Longrightarrow> return_pmf (l, succ \<R> R) \<in> \<K> st" |
  *)
   \<comment> \<open>Passage of time\<close> delay:
  "st \<in> \<S> \<Longrightarrow> st = (l,R) \<Longrightarrow> R' \<in> Succ \<R> R \<Longrightarrow> R' \<subseteq> \<lbrace>inv_of A l\<rbrace> \<Longrightarrow> return_pmf (l, R') \<in> \<K> st" |
  \<comment> \<open>Discrete transitions\<close> action:
  "st \<in> \<S> \<Longrightarrow> st = (l, R ) \<Longrightarrow> (l, g, \<mu>) \<in> trans_of A \<Longrightarrow> R \<subseteq> \<lbrace>g\<rbrace>
  \<Longrightarrow> map_pmf (\<lambda> (X, l). (l, region_set' R (SOME r. set r = X) 0)) \<mu> \<in> \<K> st" |
  \<comment> \<open>Self loops -- Note that this does not assume \<open>st \<in> \<S>\<close>\<close> loop:
  "return_pmf st \<in> \<K> st"

lemmas [intro] = \<K>.intros


subsection \<open>Many Closure Properties\<close>

lemma transition_def:
  "(A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l') = ((l, g, \<mu>) \<in> trans_of A \<and> (X, l') \<in> \<mu>)"
  unfolding Edges_def edges_def trans_of_def by auto

lemma transitionI[intro]:
  "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'" if "(l, g, \<mu>) \<in> trans_of A" "(X, l') \<in> \<mu>"
  using that unfolding transition_def ..

lemma transitionD[dest]:
  "(l, g, \<mu>) \<in> trans_of A" "(X, l') \<in> \<mu>" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'"
  using that unfolding transition_def by auto

lemma bex_Edges:
  "(\<exists> x \<in> Edges A. P x) = (\<exists> l g \<mu> X l'. A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l' \<and> P (l, g, \<mu>, X, l'))"
  by fastforce

(* XXX Move *)
lemma L_trans[intro]:
  assumes "(l, g, \<mu>) \<in> trans_of A" "(X, l') \<in> \<mu>"
  shows "l \<in> L" "l' \<in> L"
  using assms unfolding L_def locations_def by (auto simp: image_iff bex_Edges transition_def)

lemma transition_\<X>:
  "X \<subseteq> \<X>" if "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'"
  using that unfolding \<X>_def collect_clkvt_def clkp_set_def by auto

lemma admissible_targets_alt:
  "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l' \<Longrightarrow> \<lbrace>g\<rbrace>\<^bsub>X \<rightarrow> 0\<^esub> \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
  "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l' \<Longrightarrow> X \<subseteq> clocks A"
  by (intro admissible_targets; blast)+

lemma V_reset_closed[intro]:
  assumes "u \<in> V"
  shows "[r \<rightarrow> (d::nat)]u \<in> V"
using assms unfolding V_def
  apply safe
  subgoal for x
    by (cases "x \<in> set r"; auto)
  done

lemmas V_reset_closed'[intro] = V_reset_closed[of _ _ 0, simplified]

lemma regions_part_ex[intro]:
  assumes "u \<in> V"
  shows "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>"
proof -
  from assms regions_partition[OF meta_eq_to_obj_eq[OF \<R>_def]] have
    "\<exists>!R. R \<in> \<R> \<and> u \<in> R"
    unfolding V_def by auto
  then show "[u]\<^sub>\<R> \<in> \<R>" "u \<in> [u]\<^sub>\<R>"
    using alpha_interp.region_unique_spec by auto
qed

lemma rep_\<R>_ex[intro]:
  assumes "R \<in> \<R>"
  shows "(SOME u. u \<in> R) \<in> R"
proof -
  from assms region_not_empty[OF finite(1)] have "\<exists> u. u \<in> R" unfolding \<R>_def by auto
  then show ?thesis ..
qed

lemma V_nn_closed[intro]:
  "u \<in> V \<Longrightarrow> t \<ge> 0 \<Longrightarrow> u \<oplus> t \<in> V"
unfolding V_def cval_add_def by auto

lemma K_S_closed[intro]:
  assumes "\<mu> \<in> K s" "s' \<in> \<mu>" "s \<in> S"
  shows "s' \<in> S"
  using assms
  by (cases rule: K.cases, auto simp: S_alt_def dest: admissible_targets[unfolded zone_set_def])

lemma S_V[intro]:
  "(l, u) \<in> S \<Longrightarrow> u \<in> V"
unfolding S_alt_def by auto

lemma L_V[intro]:
  "(l, u) \<in> S \<Longrightarrow> l \<in> L"
unfolding S_def by auto

lemma \<S>_V[intro]:
  "(l, R) \<in> \<S> \<Longrightarrow> R \<in> \<R>"
unfolding \<S>_def by auto

lemma admissible_targets':
  assumes "(l, g, \<mu>) \<in> trans_of A" "(X, l') \<in> \<mu>" "R \<subseteq> \<lbrace>g\<rbrace>"
  shows "region_set' R (SOME r. set r = X) 0 \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
using admissible_targets(1)[OF assms(1,2)] assms(3) unfolding region_set'_def zone_set_def by auto


subsection \<open>The Region Graph is a Finite MDP\<close>

lemma \<S>_finite:
  "finite \<S>"
using finite finite_\<R> unfolding \<S>_def by auto

lemma \<K>_finite:
  "finite (\<K> st)"
proof -
  let ?B1 = "{(R', l, R). st \<in> \<S> \<and> st = (l, R) \<and> R' \<in> Succ \<R> R \<and> R' \<subseteq> \<lbrace>inv_of A l\<rbrace>}"
  let ?S1 = "(\<lambda>(R', l, R). return_pmf (l, R')) ` ?B1"
  let ?S1 = "{return_pmf (l, R') | R' l R. st \<in> \<S> \<and> st = (l, R) \<and> R' \<in> Succ \<R> R \<and> R' \<subseteq> \<lbrace>inv_of A l\<rbrace>}"
  let ?S2 = "{map_pmf (\<lambda> (X, l). (l, region_set' R (SOME r. set r = X) 0)) \<mu>
             | R \<mu>. \<exists> l g. st \<in> \<S> \<and> st = (l, R ) \<and> (l, g, \<mu>) \<in> trans_of A \<and> R \<subseteq> \<lbrace>g\<rbrace>}"
  have "?B1 \<subseteq> {(R', l, R). R' \<in> \<R> \<and> (l, R) \<in> \<S> }" unfolding \<S>_def by auto
  with \<S>_finite finite_\<R> have "finite ?B1" by - (rule finite_subset, auto)
  moreover have "?S1 = (\<lambda>(R', l, R). return_pmf (l, R')) ` ?B1" by (auto simp: image_def)
  ultimately have *: "finite ?S1" by auto
  have "{\<mu>. \<exists>l g. (l, g, \<mu>) \<in> PTA.trans_of A} = ((\<lambda> (l, g, \<mu>). \<mu>) ` PTA.trans_of A)" by force
  with finite(3) finite_\<R> have "finite {(R, \<mu>). \<exists> l g. R \<in> \<R> \<and> (l, g, \<mu>) \<in> trans_of A}" by auto
  moreover have
    "{(R, \<mu>). \<exists> l g. st \<in> \<S> \<and> st = (l, R ) \<and> (l, g, \<mu>) \<in> trans_of A \<and> R \<subseteq> \<lbrace>g\<rbrace>} \<subseteq> \<dots>"
  unfolding \<S>_def by fastforce
  ultimately have **:
    "finite {(R, \<mu>). \<exists> l g. st \<in> \<S> \<and> st = (l, R ) \<and> (l, g, \<mu>) \<in> trans_of A \<and> R \<subseteq> \<lbrace>g\<rbrace>}"
  unfolding \<S>_def by (blast intro: finite_subset)
  then have "finite ?S2" unfolding \<S>_def by auto
  have "\<K> st = ?S1 \<union> ?S2 \<union> {return_pmf st}" by (safe, cases rule: \<K>.cases, auto)
  with * ** show ?thesis by auto
qed

(* XXX Obsolete in here, move to Regions *)
lemma \<R>_not_empty:
  "\<R> \<noteq> {}"
proof -
  let ?r = "{}"
  let ?I = "\<lambda> c. Const 0"
  let ?R = "region \<X> ?I ?r"
  have "valid_region \<X> k ?I ?r"
  proof
    show "{} = {x \<in> \<X>. \<exists>d. Const 0 = Intv d}" by auto
    show "refl_on {} {}" and "trans {}" and "total_on {} {}" unfolding trans_def by auto
    show "\<forall>x \<in> \<X>. Regions.valid_intv (k x) (Const 0)" by auto
  qed
  then have "?R \<in> \<R>" unfolding \<R>_def by auto
  then show "\<R> \<noteq> {}" by blast
qed

lemma \<S>_not_empty:
  "\<S> \<noteq> {}"
proof -
  from not_trivial obtain l u where st: "l \<in> L" "u \<in> V" "u \<turnstile> inv_of A l" by blast
  then obtain R where R: "R \<in> \<R>" "u \<in> R" using \<R>_V by auto
  from valid have
    "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> \<X> \<and> m \<in> \<nat>"
  by (fastforce simp: clkp_set_def collect_clki_def)
  from ccompatible[OF this, folded \<R>_def] R st(3) have
    "R \<subseteq> \<lbrace>inv_of A l\<rbrace>"
  unfolding ccompatible_def ccval_def by auto
  with st(1) R(1) show ?thesis unfolding \<S>_def by auto
qed

lemma \<K>_\<S>_closed:
  assumes "s \<in> \<S>"
  shows "(\<Union>D\<in>\<K> s. set_pmf D) \<subseteq> \<S>"
proof (safe, cases rule: \<K>.cases, blast, goal_cases)
  case (1 x a b l R)
  then show ?case unfolding \<S>_def by (auto intro: alpha_interp.succ_ex(1))
next
  case (3 a b x)
  with \<open>s \<in> \<S>\<close> show ?case by auto
next
  case prems: (2 l' R' p l R g \<mu>)
  then obtain X where *: "(X, l') \<in> set_pmf \<mu>" "R' = region_set' R (SOME r. set r = X) 0" by auto
  
  show ?case unfolding \<S>_def
  proof safe
    from *(1) have "(l, g, \<mu>, X, l') \<in> edges (l,g, \<mu>)" unfolding edges_def by auto
    with prems(6) have "(l, g, \<mu>, X, l') \<in> Edges A" unfolding Edges_def trans_of_def by auto
    then show "l' \<in> L" unfolding L_def locations_def by force

    show "u \<turnstile> inv_of A l'" if "u \<in> R'" for u
    using admissible_targets'[OF prems(6) *(1) prems(7)] *(2) that by auto    
    
    from admissible_targets(2)[OF prems(6) *(1)] have "X \<subseteq> \<X>" unfolding \<X>_def by auto
    with finite(1) have "finite X" by (blast intro: finite_subset)
    then obtain r where "set r = X" using finite_list by auto
    then have "set (SOME r. set r = X) = X" by (rule someI)
    with \<open>X \<subseteq> \<X>\<close> have "set (SOME r. set r = X) \<subseteq> \<X>" by auto
    with alpha_interp.region_set'_closed[of R 0 "SOME r. set r = X"] prems(4,5) *(2)
    show "R' \<in> \<R>" unfolding \<S>_def \<X>_def by auto
  qed
qed

sublocale R_G: Finite_Markov_Decision_Process \<K> \<S>
by (standard, auto simp: \<S>_finite \<S>_not_empty \<K>_finite \<K>_\<S>_closed)

lemmas \<K>_\<S>_closed'[intro] = R_G.set_pmf_closed


section \<open>Relating the MDPs\<close>

subsection \<open>Translating From K to \<open>\<K>\<close>\<close>

(* XXX Clean this for regular automata too *)
(* Assumption of valid too strong? i.e. do not need l \<in> L here *)
lemma ccompatible_inv:
  shows "ccompatible \<R> (inv_of A l)"
proof -
  from valid have
    "\<forall>(x, m)\<in>collect_clock_pairs (inv_of A l). m \<le> real (k x) \<and> x \<in> \<X> \<and> m \<in> \<nat>"
  unfolding valid_abstraction_def clkp_set_def collect_clki_def by auto
  with ccompatible[of _ k \<X>, folded \<R>_def] show ?thesis by auto
qed

lemma ccompatible_guard:
  assumes "(l, g, \<mu>) \<in> trans_of A"
  shows "ccompatible \<R> g"
proof -
  from assms valid have
    "\<forall>(x, m)\<in>collect_clock_pairs g. m \<le> real (k x) \<and> x \<in> \<X> \<and> m \<in> \<nat>"
  unfolding valid_abstraction_def clkp_set_def collect_clkt_def trans_of_def by fastforce
  with assms ccompatible[of _ k \<X>, folded \<R>_def] show ?thesis by auto
qed

lemmas ccompatible_def = ccompatible_def[unfolded ccval_def]

lemma region_set'_eq:
  fixes X :: "'c set"
  assumes "R \<in> \<R>" "u \<in> R"
      and "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'"
  shows
    "[[X:=0]u]\<^sub>\<R> = region_set' R (SOME r. set r = X) 0" "[[X:=0]u]\<^sub>\<R> \<in> \<R>" "[X:=0]u \<in> [[X:=0]u]\<^sub>\<R>"
proof -
  let ?r = "(SOME r. set r = X)"
  from admissible_targets_alt[OF assms(3)] \<X>_def finite have "finite X"
    by (auto intro: finite_subset)
  then obtain r where "set r = X" using finite_list by blast
  then have "set ?r = X" by (intro someI)
  with valid assms(3) have "set ?r \<subseteq> \<X>"
    by (simp add: transition_\<X>)
  from region_set'_id[of _ \<X> k, folded \<R>_def, OF assms(1,2) finite(1) _ _ this]
  show
    "[[X:=0]u]\<^sub>\<R> = region_set' R (SOME r. set r = X) 0" "[[X:=0]u]\<^sub>\<R> \<in> \<R>" "[X:=0]u \<in> [[X:=0]u]\<^sub>\<R>"
  by force+
qed

lemma regions_part_ex_reset:
  assumes "u \<in> V"
  shows  "[r \<rightarrow> (d::nat)]u \<in> [[r \<rightarrow> d]u]\<^sub>\<R>" "[[r \<rightarrow> d]u]\<^sub>\<R> \<in> \<R>"
using assms by auto

lemma reset_sets_all_equiv:
  assumes "u \<in> V" "u' \<in> [[r \<rightarrow> (d :: nat)]u]\<^sub>\<R>" "x \<in> set r" "set r \<subseteq> \<X>" "d \<le> k x"
  shows "u' x = d"
proof -
  from assms(1) have u: "[r \<rightarrow> d]u \<in> [[r \<rightarrow> d]u]\<^sub>\<R>" "[[r \<rightarrow> d]u]\<^sub>\<R> \<in> \<R>" by auto
  then obtain I \<rho> where I: "[[r \<rightarrow> d]u]\<^sub>\<R> = region \<X> I \<rho>" "valid_region \<X> k I \<rho>"
    by (auto simp: \<R>_def)
  with u(1) assms(3-) have "intv_elem x ([r \<rightarrow> d]u) (I x)" "valid_intv (k x) (I x)" by fastforce+
  moreover from assms have "([r \<rightarrow> d]u) x = d" by simp
  ultimately have "I x = Const d" using assms(5) by (cases "I x") auto
  moreover from I assms(2-) have "intv_elem x u' (I x)" by fastforce
  ultimately show "u' x = d" by auto
qed

lemma reset_eq:
  assumes "u \<in> V" "([[r \<rightarrow> 0]u]\<^sub>\<R>) = ([[r' \<rightarrow> 0]u]\<^sub>\<R>)" "set r \<subseteq> \<X>" "set r' \<subseteq> \<X>"
  shows "[r \<rightarrow> 0]u = [r' \<rightarrow> 0]u" using assms 
proof -
  have *: "u' x = 0" if "u' \<in> [[r \<rightarrow> 0]u]\<^sub>\<R>" "x \<in> set r" for u' x
  using reset_sets_all_equiv[of u u' r 0 x] that assms by auto
  have "u' x = 0" if "u' \<in> [[r' \<rightarrow> 0]u]\<^sub>\<R>" "x \<in> set r'" for u' x 
  using reset_sets_all_equiv[of u u' r' 0 x] that assms by auto
  from regions_part_ex_reset[OF assms(1), of _ 0] assms(2) have **:
    "([r' \<rightarrow> 0]u) \<in> [[r \<rightarrow> 0]u]\<^sub>\<R>" "([r \<rightarrow> 0]u) \<in> [[r \<rightarrow> 0]u]\<^sub>\<R>" "[[r \<rightarrow> 0]u]\<^sub>\<R> \<in> \<R>"
  by auto
  have "(([r \<rightarrow> 0]u) x) = (([r' \<rightarrow> 0]u) x)" for x
  proof (cases "x \<in> set r")
    case True
    then have "([r \<rightarrow> 0]u) x = 0" by simp
    moreover from * ** True have "([r' \<rightarrow> 0]u) x = 0" by auto
    ultimately show ?thesis ..
  next
    case False
    then have id: "([r\<rightarrow>0]u) x = u x" by simp
    show ?thesis
    proof (cases "x \<in> set r'")
      case True
      then have reset: "([r' \<rightarrow> 0]u) x = 0" by simp
      show ?thesis
      proof (cases "x \<in> \<X>")
        case True
        from **(3) obtain I \<rho> where
          "([([r \<rightarrow> 0]u)]\<^sub>\<R>) = Regions.region \<X> I \<rho>" "Regions.valid_region \<X> k I \<rho>"
        by (auto simp: \<R>_def)
        with ** \<open>x \<in> \<X>\<close> have ***:
          "intv_elem x ([r' \<rightarrow> 0]u) (I x)" "intv_elem x ([r \<rightarrow> 0]u) (I x)"
        by auto
        with reset have "I x = Const 0" by (cases "I x", auto)
        with ***(2) have "([r \<rightarrow> 0]u) x = 0" by auto
        with reset show ?thesis by auto
      next
        case False
        with assms(3-) have "x \<notin> set r" "x \<notin> set r'" by auto
        then show ?thesis by simp
      qed
    next
      case False
      then have reset: "([r' \<rightarrow> 0]u) x = u x" by simp
      with id show ?thesis by simp
    qed
  qed
  then show ?thesis ..
qed

lemma admissible_targets_clocks:
  assumes "(l, g, \<mu>) \<in> trans_of A" "(X, l') \<in> \<mu>"
  shows "X \<subseteq> \<X>" "set (SOME r. set r = X) \<subseteq> \<X>"
proof -
  from admissible_targets(2)[OF assms] finite have
    "finite X" "X \<subseteq> \<X>"
  by (auto intro: finite_subset simp: \<X>_def)
  then obtain r where "set r = X" using finite_list by blast
  with \<open>X \<subseteq> \<X>\<close> show "X \<subseteq> \<X>" "set (SOME r. set r = X) \<subseteq> \<X>"
    by (metis (mono_tags, lifting) someI_ex)+
qed

lemma
  "rel_pmf (\<lambda> a b. f a = b) \<mu> (map_pmf f \<mu>)"
by (subst pmf.rel_map(2)) (rule rel_pmf_reflI, auto)

lemma K_pmf_rel:
  defines "f \<equiv> \<lambda> (l, u). (l, [u]\<^sub>\<R>)"
  shows "rel_pmf (\<lambda> (l, u) st. (l, [u]\<^sub>\<R>) = st) \<mu> (map_pmf f \<mu>)" unfolding f_def
by (subst pmf.rel_map(2)) (rule rel_pmf_reflI, auto)

lemma \<K>_pmf_rel:
  assumes A: "\<mu> \<in> \<K> (l, R)"
  defines "f \<equiv> \<lambda> (l, u). (l, SOME u. u \<in> R)"
  shows "rel_pmf (\<lambda> (l, u) st. (l, SOME u. u \<in> R) = st) \<mu> (map_pmf f \<mu>)" unfolding f_def
by (subst pmf.rel_map(2)) (rule rel_pmf_reflI, auto)

lemma K_elem_abs_inj:
  assumes A: "\<mu> \<in> K (l, u)"
  defines "f \<equiv> \<lambda> (l, u). (l, [u]\<^sub>\<R>)"
  shows "inj_on f \<mu>"
proof -
  have "(l1, u1) = (l2, u2)"
    if id: "(l1, [u1]\<^sub>\<R>) = (l2, [u2]\<^sub>\<R>)" and elem: "(l1, u1) \<in> \<mu>" "(l2, u2) \<in> \<mu>" for l1 l2 u1 u2
  proof -
    from id have [simp]: "l2 = l1" by auto
    from A
    show ?thesis
    proof (cases, safe, goal_cases)
      case (4 _ _ \<tau> \<mu>')
      from \<open>\<mu> = _\<close> elem obtain X1 X2 where
        "u1 = [(SOME r. set r = X1)\<rightarrow>0]u" "(X1, l1) \<in> \<mu>'"
        "u2 = [(SOME r. set r = X2)\<rightarrow>0]u" "(X2, l1) \<in> \<mu>'"
      by auto
      with \<open>_ \<in> trans_of _\<close> admissible_targets_clocks have
        "set (SOME r. set r = X1) \<subseteq> \<X>" "set (SOME r. set r = X2) \<subseteq> \<X>"
      by auto
      with id \<open>u1 = _\<close> \<open>u2 = _\<close> reset_eq[of u] \<open>_ \<in> S\<close> show ?case by (auto simp: S_def V_def)
    qed (-, insert elem, simp)+
  qed
  then show ?thesis unfolding f_def inj_on_def by auto
qed

lemma K_elem_repr_inj:
  notes alpha_interp.valid_regions_distinct_spec[intro] (* XXX Declare somewhere else *)
  assumes A: "\<mu> \<in> \<K> (l, R)"
  defines "f \<equiv> \<lambda> (l, R). (l, SOME u. u \<in> R)"
  shows "inj_on f \<mu>"
proof -
  have "(l1, R1) = (l2, R2)"
    if id: "(l1, SOME u. u \<in> R1) = (l2, SOME u. u \<in> R2)" and elem: "(l1, R1) \<in> \<mu>" "(l2, R2) \<in> \<mu>"
    for l1 l2 R1 R2
  proof -
    let ?r1 = "SOME u. u \<in> R1" and ?r2 = "SOME u. u \<in> R2"
    from id have [simp]: "l2 = l1" "?r2 = ?r1" by auto
    { fix g \<mu>' x
      assume "(l, R) \<in> \<S>" "(l, g, \<mu>') \<in> PTA.trans_of A" "R \<subseteq> {v. v \<turnstile> g}"
         and "\<mu> = map_pmf (\<lambda>(X, l). (l, region_set' R (SOME r. set r = X) 0)) \<mu>'"
      from \<open>\<mu> = _\<close> elem obtain X1 X2 where
        "R1 = region_set' R (SOME r. set r = X1) 0" "(X1, l1) \<in> \<mu>'"
        "R2 = region_set' R (SOME r. set r = X2) 0" "(X2, l1) \<in> \<mu>'"
      by auto
      with \<open>_ \<in> trans_of _\<close> admissible_targets_clocks have
        "set (SOME r. set r = X1) \<subseteq> \<X>" "set (SOME r. set r = X2) \<subseteq> \<X>"
      by auto
      with alpha_interp.region_set'_closed[of _ 0] \<open>R1 = _\<close> \<open>R2 = _\<close> \<open>_ \<in> \<S>\<close> have
        "R1 \<in> \<R>" "R2 \<in> \<R>"
      unfolding \<S>_def by auto
      with region_not_empty[OF finite(1)] have
        "R1 \<noteq> {}" "R2 \<noteq> {}" "\<exists>u. u \<in> R1" "\<exists>u. u \<in> R2"
      by (auto simp: \<R>_def)
      from someI_ex[OF this(3)] someI_ex[OF this(4)] have "?r1 \<in> R1" "?r1 \<in> R2" by simp+
      with \<open>R1 \<in> \<R>\<close> \<open>R2 \<in> \<R>\<close> have "R1 = R2" ..
    }
    from A elem this show ?thesis by (cases, auto)
  qed
  then show ?thesis unfolding f_def inj_on_def by auto
qed

lemma K_elem_pmf_map_abs:
  assumes A: "\<mu> \<in> K (l, u)" "(l', u') \<in> \<mu>"
  defines "f \<equiv> \<lambda> (l, u). (l, [u]\<^sub>\<R>)"
  shows "pmf (map_pmf f \<mu>) (f (l', u')) = pmf \<mu> (l', u')"
using A unfolding f_def by (blast intro: pmf_map_inj K_elem_abs_inj)

lemma K_elem_pmf_map_repr:
  assumes A: "\<mu> \<in> \<K> (l, R)" "(l', R') \<in> \<mu>"
  defines "f \<equiv> \<lambda> (l, R). (l, SOME u. u \<in> R)"
  shows "pmf (map_pmf f \<mu>) (f (l', R')) = pmf \<mu> (l', R')"
using A unfolding f_def by (blast intro: pmf_map_inj K_elem_repr_inj)



definition transp :: "('s * ('c, t) cval \<Rightarrow> bool) \<Rightarrow> 's * ('c, t) cval set \<Rightarrow> bool" where
  "transp \<phi> \<equiv> \<lambda> (l, R). \<forall> u \<in> R. \<phi> (l, u)"

subsection \<open>Translating Configurations\<close>

subsubsection \<open>States\<close>

definition
  abss :: "'s * ('c, t) cval \<Rightarrow> 's * ('c, t) cval set"
where
  "abss \<equiv> \<lambda> (l, u). if u \<in> V then (l, [u]\<^sub>\<R>) else (l, -V)"

definition
  reps :: "'s * ('c, t) cval set \<Rightarrow> 's * ('c, t) cval"
where
  "reps \<equiv> \<lambda> (l, R). if R \<in> \<R> then (l, SOME u. u \<in> R) else (l, \<lambda>_. -1)"

lemma \<S>_reps_S[intro]:
  assumes "s \<in> \<S>"
  shows "reps s \<in> S"
using assms \<R>_V unfolding S_def \<S>_def reps_def V_def by force

lemma S_abss_\<S>[intro]:
  assumes "s \<in> S"
  shows "abss s \<in> \<S>"
using assms ccompatible_inv unfolding \<S>_def S_alt_def abss_def ccompatible_def by force

lemma \<S>_abss_reps[simp]:
  "s \<in> \<S> \<Longrightarrow> abss (reps s) = s"
using \<R>_V alpha_interp.region_unique_spec by (auto simp: S_def \<S>_def reps_def abss_def; blast)

lemma map_pmf_abs_reps:
  assumes "s \<in> \<S>" "\<mu> \<in> \<K> s"
  shows "map_pmf abss (map_pmf reps \<mu>) = \<mu>"
proof -
  have "map_pmf abss (map_pmf reps \<mu>) = map_pmf (abss o reps) \<mu>" by (simp add: pmf.map_comp)
  also have "\<dots> = \<mu>"
  proof (rule map_pmf_idI, safe, goal_cases)
    case prems: (1 l' R')
    with assms have "(l', R') \<in> \<S>" "reps (l', R') \<in> S" by auto
    then show ?case by auto
  qed
  finally show ?thesis by auto
qed

lemma abss_reps_id:
  notes R_G.cfg_onD_state[simp del]
  assumes "s' \<in> \<S>" "s \<in> set_pmf (action cfg)" "cfg \<in> R_G.cfg_on s'"
  shows "abss (reps s) = s"
proof -
  from assms have "s \<in> \<S>" by auto
  then show ?thesis by auto
qed

lemma abss_S[intro]:
  assumes "(l, u) \<in> S"
  shows "abss (l, u) = (l, [u]\<^sub>\<R>)"
using assms unfolding abss_def by auto

lemma reps_\<S>[intro]:
  assumes "(l, R) \<in> \<S>"
  shows "reps (l, R) = (l, SOME u. u \<in> R)"
using assms unfolding reps_def by auto

lemma fst_abss:
  "fst (abss st) = fst st" for st
  by (cases st) (auto simp: abss_def)

lemma K_elem_abss_inj:
  assumes A: "\<mu> \<in> K (l, u)" "(l, u) \<in> S"
  shows "inj_on abss \<mu>"
proof -
  from assms have "abss s' = (\<lambda> (l, u). (l, [u]\<^sub>\<R>)) s'" if "s' \<in> \<mu>" for s'
  using that by (auto split: prod.split)
  from inj_on_cong[OF this] K_elem_abs_inj[OF A(1)] show ?thesis by force
qed

lemma \<K>_elem_reps_inj:
  assumes A: "\<mu> \<in> \<K> (l, R)" "(l, R) \<in> \<S>"
  shows "inj_on reps \<mu>"
proof -
  from assms have "reps s' = (\<lambda> (l, R). (l, SOME u. u \<in> R)) s'" if "s' \<in> \<mu>" for s'
  using that by (auto split: prod.split)
  from inj_on_cong[OF this] K_elem_repr_inj[OF A(1)] show ?thesis by force
qed

lemma P_elem_pmf_map_abss:
  assumes A: "\<mu> \<in> K (l, u)" "(l, u) \<in> S" "s' \<in> \<mu>"
  shows "pmf (map_pmf abss \<mu>) (abss s') = pmf \<mu> s'"
using A by (blast intro: pmf_map_inj K_elem_abss_inj)

lemma \<K>_elem_pmf_map_reps:
  assumes A: "\<mu> \<in> \<K> (l, R)" "(l, R) \<in> \<S>" "(l', R') \<in> \<mu>"
  shows "pmf (map_pmf reps \<mu>) (reps (l', R')) = pmf \<mu> (l', R')"
using A by (blast intro: pmf_map_inj \<K>_elem_reps_inj)

text \<open>We need that \<open>\<X>\<close> is non-trivial here\<close>
lemma not_\<S>_reps:
  "(l, R) \<notin> \<S> \<Longrightarrow> reps (l, R) \<notin> S"
proof -
  assume "(l, R) \<notin> \<S>"
  let ?u = "SOME u. u \<in> R"
  have "\<not> ?u \<turnstile> inv_of A l" if "R \<in> \<R>" "l \<in> L"
  proof -
    (* XXX Refactor -- doing that kind of proof at other places too *)
    from region_not_empty[OF finite(1)] \<open>R \<in> \<R>\<close> have "\<exists>u. u \<in> R" by (auto simp: \<R>_def)
    from someI_ex[OF this] have "?u \<in> R" .
    moreover from \<open>(l, R) \<notin> \<S>\<close> that have "\<not> R \<subseteq> \<lbrace>inv_of A l\<rbrace>" by (auto simp: \<S>_def)
    ultimately show ?thesis
      using ccompatible_inv[of l] \<open>R \<in> \<R>\<close> unfolding ccompatible_def by fastforce
  qed
  with non_empty \<open>(l, R) \<notin> \<S>\<close> show ?thesis unfolding \<S>_def S_def reps_def by auto
qed

(* XXX Move up *)
lemma neq_V_not_region:
  "-V \<notin> \<R>"
using \<R>_V rep_\<R>_ex by auto

lemma \<S>_abss_S:
  "abss s \<in> \<S> \<Longrightarrow> s \<in> S"
  unfolding abss_def \<S>_def S_def
  apply safe
  subgoal for _ _ _ u
    by (cases "u \<in> V") auto
  subgoal for _ _ _ u
    using neq_V_not_region by (cases "u \<in> V", (auto simp: V_def; fail), auto)
  subgoal for l' y l u
    using neq_V_not_region by (cases "u \<in> V"; auto dest: regions_part_ex)
  done

lemma S_pred_stream_abss_\<S>:
  "pred_stream (\<lambda> s. s \<in> S) xs \<longleftrightarrow> pred_stream (\<lambda> s. s \<in> \<S>) (smap abss xs)"
using S_abss_\<S> \<S>_abss_S by (auto simp: stream.pred_set)


sublocale MDP: Markov_Decision_Process_Invariant K S by (standard, auto)

abbreviation (input) "valid_cfg \<equiv> MDP.valid_cfg"

lemma K_closed:
  "s \<in> S \<Longrightarrow> (\<Union>D\<in>K s. set_pmf D) \<subseteq> S" 
  by auto


subsubsection \<open>Intermezzo\<close>

(* XXX Correct binding strength *)
abbreviation timed_bisim (infixr "~" 60) where
  "s ~ s' \<equiv> abss s = abss s'"

lemma bisim_loc_id[intro]:
  "(l, u) ~ (l', u') \<Longrightarrow> l = l'"
unfolding abss_def by (cases "u \<in> V"; cases "u' \<in> V"; simp)

lemma bisim_val_id[intro]:
  "[u]\<^sub>\<R> = [u']\<^sub>\<R>" if "u \<in> V" "(l, u) ~ (l', u')"
proof -
  have "(l', - V) \<noteq> (l, [u]\<^sub>\<R>)"
    using that by blast
  with that have "u' \<in> V"
    by (force simp: abss_def)
  with that show ?thesis
    by (simp add: abss_def)
qed

lemma bisim_symmetric:
  "(l, u) ~ (l', u') = (l', u') ~ (l, u)"
by (rule eq_commute)

lemma bisim_val_id2[intro]:
  "u' \<in> V \<Longrightarrow> (l, u) ~ (l', u') \<Longrightarrow> [u]\<^sub>\<R> = [u']\<^sub>\<R>"
 apply (subst (asm) eq_commute)
 apply (subst eq_commute)
 apply (rule bisim_val_id)
by auto

lemma K_bisim_unique:
  assumes "s \<in> S" "\<mu> \<in> K s" "x \<in> \<mu>" "x' \<in> \<mu>" "x ~ x'"
  shows "x = x'"
using assms(2,1,3-)
proof (cases rule: K.cases)
  case prems: (action l u \<tau> \<mu>')
  with assms obtain l1 l2 X1 X2 where A:
    "(X1, l1) \<in> set_pmf \<mu>'" "(X2, l2) \<in> set_pmf \<mu>'"
    "x = (l1, [X1:=0]u)" "x' = (l2, [X2:=0]u)"
  by auto
  from \<open>x ~ x'\<close> A \<open>s \<in> S\<close> \<open>s = (l, u)\<close> have "[[X1:=0]u]\<^sub>\<R> = [[X2:=0]u]\<^sub>\<R>"
    using bisim_val_id[OF S_V] K_S_closed assms(2-4) by (auto intro!: bisim_val_id[OF S_V])
  then have "[X1:=0]u = [X2:=0]u"
    using A admissible_targets_clocks(2)[OF prems(4)] prems(2,3) by - (rule reset_eq, force)
  with A \<open>x ~ x'\<close> show ?thesis by auto
next
  case delay
  with assms(3-) show ?thesis by auto
next
  case loop
  with assms(3-) show ?thesis by auto
qed

subsubsection \<open>Predicates\<close>

definition absp where
  "absp \<phi> \<equiv> \<phi> o reps"

definition repp where
  "repp \<phi> \<equiv> \<phi> o absp"


subsubsection \<open>Distributions\<close>

definition
  abst :: "('s * ('c, t) cval) pmf \<Rightarrow> ('s * ('c, t) cval set) pmf"
where
  "abst = map_pmf abss"

lemma abss_\<S>D:
  assumes "abss s \<in> \<S>"
  obtains l u where "s = (l, u)" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>"
proof -
  obtain l u where "s = (l, u)" by force
  moreover from \<S>_abss_S[OF assms] have "s \<in> S" .
  ultimately have "abss s = (l, [u]\<^sub>\<R>)" "u \<in> V" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" by auto
  with \<open>s = _\<close> show ?thesis by (auto intro: that)
qed

lemma abss_\<S>D':
  assumes "abss s \<in> \<S>" "abss s = (l, R)"
  obtains u where "s = (l, u)" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" "R = [u]\<^sub>\<R>"
proof -
  from abss_\<S>D[OF assms(1)] obtain l' u where u:
    "s = (l', u)" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>"
  by blast+
  with \<R>_V have "u \<in> V" by auto
  with \<open>s = _\<close> assms(2) have "l' = l" "R = [u]\<^sub>\<R>" unfolding abss_def by auto
  with u show ?thesis by (auto intro: that)
qed

(*
definition
  rept :: "'s * ('c, t) cval \<Rightarrow> ('s * ('c, t) cval set) pmf \<Rightarrow> ('s * ('c, t) cval) pmf"
where
  "rept s \<mu>_abs \<equiv> let (l, u) = s in
    if \<mu>_abs = return_pmf (abss s)
    then if (\<exists> c \<in> \<X>. \<exists> d. u c = real d)
         then return_pmf s
         else return_pmf (l, u \<oplus> 0.5)
    else SOME \<mu>. \<mu> \<in> K s \<and> abst \<mu> = \<mu>_abs"
*)

definition "infR R \<equiv> \<lambda> c. of_int \<lfloor>(SOME u. u \<in> R) c\<rfloor>"

term "let a = 3 in b"

(* definition "shiftedR R \<equiv> let u = (SOME u. u \<in> R) in (u \<oplus> max 0 (0.1 - Max {frac (u c) | c. c \<in> \<X>}))" *)
(*
definition "delayedR R u \<equiv>
  u \<oplus> (
    let (I, r) = (SOME x. \<exists> I r. x = (I, r) \<and> valid_region \<X> k I r \<and> R = region \<X> I r);
        m = Min {of_nat (intv_const (I c)) + 1 - u c | c. c \<in> \<X> \<and> isConst (I c)}
    in if m \<ge> 1 then SOME t. u \<oplus> t \<in> R else m / 2
  )"
*)

(*
definition "delayedR R u \<equiv>
  u \<oplus> (
    let (I, r) = (SOME x. \<exists> I r. x = (I, r) \<and> valid_region \<X> k I r \<and> R = region \<X> I r);
        m = 1 - Max ({frac (u c) | c. c \<in> \<X> \<and> isIntv (I c) \<and> intv_const (I c) = 0} \<union> {0})
    in if m \<ge> 1 then SOME t. u \<oplus> t \<in> R else m / 2
  )"
*)

definition "delayedR R u \<equiv>
  u \<oplus> (
    let I = (SOME I. \<exists> r. valid_region \<X> k I r \<and> R = region \<X> I r);
        m = 1 - Max ({frac (u c) | c. c \<in> \<X> \<and> isIntv (I c)} \<union> {0})
    in SOME t. u \<oplus> t \<in> R \<and> t \<ge> m / 2
  )"


(* XXX Move, generated by sledgehammer *)
lemma delayedR_correct_aux_aux:
  fixes c :: nat
  fixes a b :: real
  assumes "c < a" "a < Suc c" "b \<ge> 0" "a + b < Suc c"
  shows "frac (a + b) = frac a + b"
(* Working alternative:
by (smt One_nat_def add.right_neutral add_Suc_right assms nat_intv_frac_decomp)
*)
proof -
  have f1: "a + b < real (c + 1)"
    using assms(4) by auto
  have f2: "\<And>r ra. (r::real) + (- r + ra) = ra"
    by linarith
  have f3: "\<And>r. (r::real) = - (- r)"
    by linarith
  have f4: "\<And>r ra. - (r::real) + (ra + r) = ra"
    by linarith
  then have f5: "\<And>r n. r + - frac r = real n \<or> \<not> r < real (n + 1) \<or> \<not> real n < r"
    using f2 by (metis nat_intv_frac_decomp)
  then have "frac a + real c = a"
    using f4 f3 by (metis One_nat_def add.right_neutral add_Suc_right assms(1) assms(2))
  then show ?thesis
    using f5 f1 assms(1) assms(3) by fastforce
qed

lemma delayedR_correct_aux:
  fixes I r
  defines "R \<equiv> region \<X> I r"
  assumes "u \<in> R" "valid_region \<X> k I r" "\<forall> c \<in> \<X>. \<not> isConst (I c)"
          "\<forall> c \<in> \<X>. isIntv (I c) \<longrightarrow> (u \<oplus> t) c < intv_const (I c) + 1"
          "t \<ge> 0"
  shows "u \<oplus> t \<in> R" unfolding R_def
proof
  from assms have "R \<in> \<R>" unfolding \<R>_def by auto
  with \<open>u \<in> R\<close> \<R>_V have "u \<in> V" by auto
  with \<open>t \<ge> 0\<close> show "\<forall>x\<in>\<X>. 0 \<le> (u \<oplus> t) x" unfolding V_def by (auto simp: cval_add_def)
  have "intv_elem x (u \<oplus> t) (I x)" if "x \<in> \<X>" for x
  proof (cases "I x")
    case Const
    with assms \<open>x \<in> \<X>\<close> show ?thesis by auto
  next
    case (Intv c)
    with assms \<open>x \<in> \<X>\<close> show ?thesis by (simp add: cval_add_def) (rule; force)
  next
    case (Greater c)
    with assms \<open>x \<in> \<X>\<close> show ?thesis by (fastforce simp add: cval_add_def)
  qed
  then show "\<forall>x\<in>\<X>. intv_elem x (u \<oplus> t) (I x)" ..

  let ?X\<^sub>0 = "{x \<in> \<X>. \<exists>d. I x = Intv d}"
  show "?X\<^sub>0 = ?X\<^sub>0" by auto

  have "frac (u x + t) = frac (u x) + t" if "x \<in> ?X\<^sub>0" for x
  proof -
    show ?thesis
      apply (rule delayedR_correct_aux_aux[where c = "intv_const (I x)"])
    using assms \<open>x \<in> ?X\<^sub>0\<close> by (force simp add: cval_add_def)+
  qed
  then have "frac (u x) \<le> frac (u y) \<longleftrightarrow> frac (u x + t) \<le> frac (u y + t)" if "x \<in> ?X\<^sub>0" "y \<in> ?X\<^sub>0" for x y
  using that by auto
  with assms show
    "\<forall>x\<in>?X\<^sub>0. \<forall>y\<in>?X\<^sub>0. ((x, y) \<in> r) = (frac ((u \<oplus> t) x) \<le> frac ((u \<oplus> t) y))"
  unfolding cval_add_def by auto
qed

lemma delayedR_correct_aux':
  fixes I r
  defines "R \<equiv> region \<X> I r"
  assumes "u \<oplus> t1 \<in> R" "valid_region \<X> k I r" "\<forall> c \<in> \<X>. \<not> isConst (I c)"
          "\<forall> c \<in> \<X>. isIntv (I c) \<longrightarrow> (u \<oplus> t2) c < intv_const (I c) + 1"
          "t1 \<le> t2"
  shows "u \<oplus> t2 \<in> R"
proof -
  have "(u \<oplus> t1) \<oplus> (t2 - t1) \<in> R" unfolding R_def
    using assms by - (rule delayedR_correct_aux, auto simp: cval_add_def)
  then show "u \<oplus> t2 \<in> R" by (simp add: cval_add_def)
qed


(* XXX Move to valid_regions_distinct *)
lemma valid_regions_intv_distinct:
  "valid_region X k I r \<Longrightarrow> valid_region X k I' r' \<Longrightarrow> u \<in> region X I r \<Longrightarrow> u \<in> region X I' r'
  \<Longrightarrow> x \<in> X \<Longrightarrow> I x = I' x"
proof goal_cases
  case A: 1
  note x = \<open>x \<in> X\<close>
  with A have "valid_intv (k x) (I x)" by auto
  moreover from A(2) x have "valid_intv (k x) (I' x)" by auto
  moreover from A(3) x have "intv_elem x u (I x)" by auto
  moreover from A(4) x have "intv_elem x u (I' x)" by auto
  ultimately show "I x = I' x" using valid_intv_distinct by fastforce
qed

(* XXX Move *)
lemma delayedR_correct:
  fixes I r
  defines "R' \<equiv> region \<X> I r"
  assumes "u \<in> R" "R \<in> \<R>" "valid_region \<X> k I r" "\<forall> c \<in> \<X>. \<not> isConst (I c)" "R' \<in> Succ \<R> R"
  shows
    "delayedR R' u \<in> R'"
    "\<exists> t \<ge> 0. delayedR R' u = u \<oplus> t
            \<and> t \<ge> (1 - Max ({frac (u c) | c. c \<in> \<X> \<and> isIntv (I c)} \<union> {0})) / 2"
proof -
  let ?u = "SOME u. u \<in> R"
  let ?I = "SOME I. \<exists> r. valid_region \<X> k I r \<and> R' = region \<X> I r"
  let ?S = "{frac (u c) | c. c \<in> \<X> \<and> isIntv (I c)}"
  let ?m = "1 - Max (?S \<union> {0})"
  let ?t = "SOME t. u \<oplus> t \<in> R' \<and> t \<ge> ?m / 2"
  have "Max (?S \<union> {0}) \<ge> 0" "?m \<le> 1" using finite(1) by auto
  have "Max (?S \<union> {0}) \<in> ?S \<union> {0}" using finite(1) by - (rule Max_in; auto)
  with frac_lt_1 have "Max (?S \<union> {0}) \<le> 1" "?m \<ge> 0" by auto
  from assms(3, 6) \<open>u \<in> R\<close> obtain t where t:
    "u \<oplus> t \<in> R'" "t \<ge> 0"
  by (metis alpha_interp.regions_closed'_spec alpha_interp.set_of_regions_spec)
  have I_cong: "\<forall> c \<in> \<X>. I' c = I c" if "valid_region \<X> k I' r'" "R' = region \<X> I' r'" for I' r'
  using valid_regions_intv_distinct assms(4) t(1) that unfolding R'_def by auto
  have I_cong: "?I c = I c" if "c \<in> \<X>" for c
  proof -
    from assms have
      "\<exists> r. valid_region \<X> k ?I r \<and> R' = region \<X> ?I r"
    by - (rule someI[where P = "\<lambda> I. \<exists> r. valid_region \<X> k I r \<and> R' = region \<X> I r"]; auto)
    with I_cong that show ?thesis by auto
  qed
  then have "?S = {frac (u c) | c. c \<in> \<X> \<and> isIntv (?I c)}" by auto
  have upper_bound: "(u \<oplus> ?m / 2) c < intv_const (I c) + 1" if "c \<in> \<X>" "isIntv (I c)" for c
  proof (cases "u c > intv_const (I c)")
    case True
    from t that assms have "u c + t < intv_const (I c) + 1" unfolding cval_add_def by fastforce
    with \<open>t \<ge> 0\<close> True have *: "intv_const (I c) < u c" "u c < intv_const (I c) + 1" by auto
    have "frac (u c) \<le> Max (?S \<union> {0})" using finite(1) that by - (rule Max_ge; auto)
    then have "?m \<le> 1 - frac (u c)" by auto
    then have "?m / 2 < 1 - frac (u c)" using * nat_intv_frac_decomp by fastforce 
    then have "(u \<oplus> ?m / 2) c < u c + 1 - frac (u c)" unfolding cval_add_def by auto
    also from * have
      "\<dots> = intv_const (I c) + 1"
    using nat_intv_frac_decomp of_nat_1 of_nat_add by fastforce
    finally show ?thesis .
  next
    case False
    then have "u c \<le> intv_const (I c)" by auto
    moreover from \<open>0 \<le> ?m\<close> \<open>?m \<le> 1\<close> have "?m / 2 < 1" by auto
    ultimately have "u c + ?m / 2 < intv_const (I c) + 1" by linarith
    then show ?thesis by (simp add: cval_add_def)
  qed
  have "?t \<ge> 0 \<and> u \<oplus> ?t \<in> R' \<and> ?t \<ge> ?m / 2"
  proof (cases "t \<ge> ?m / 2")
    case True
    from \<open>t \<ge> ?m / 2\<close> t \<open>Max (?S \<union> {0}) \<le> 1\<close> have "u \<oplus> ?t \<in> R' \<and> ?t \<ge> ?m / 2"
      by - (rule someI; auto)
    with \<open>?m \<ge> 0\<close> show ?thesis by auto
  next
    case False
    have "u \<oplus> ?m / 2 \<in> R'" unfolding R'_def
     apply (rule delayedR_correct_aux')
         apply (rule t[unfolded R'_def])
        apply (rule assms)+
    using upper_bound False by auto
    with \<open>?m \<ge> 0\<close> show ?thesis by - (rule someI2; fastforce)
  qed
  then show "delayedR R' u \<in> R'" "\<exists>t\<ge>0. delayedR R' u = u \<oplus> t \<and> t \<ge> ?m / 2"
    by (auto simp: delayedR_def \<open>?S = _\<close>)
qed

definition
  rept :: "'s * ('c, t) cval \<Rightarrow> ('s * ('c, t) cval set) pmf \<Rightarrow> ('s * ('c, t) cval) pmf"
where
  "rept s \<mu>_abs \<equiv> let (l, u) = s in
    if (\<exists> R'. (l, u) \<in> S \<and> \<mu>_abs = return_pmf (l, R') \<and>
        (([u]\<^sub>\<R> = R' \<and> (\<forall> c \<in> \<X>. u c > k c))))
    then return_pmf (l, u \<oplus> 0.5)
    else if
      (\<exists> R'. (l, u) \<in> S \<and> \<mu>_abs = return_pmf (l, R') \<and> R' \<in> Succ \<R> ([u]\<^sub>\<R>) \<and> [u]\<^sub>\<R> \<noteq> R'
           \<and> (\<forall> u \<in> R'. \<forall> c \<in> \<X>. \<nexists> d. d \<le> k c \<and>  u c = real d))
    then return_pmf (l, delayedR (SOME R'. \<mu>_abs = return_pmf (l, R')) u)
    else SOME \<mu>. \<mu> \<in> K s \<and> abst \<mu> = \<mu>_abs"

(* XXX Move *)
lemma \<S>_L:
  "l \<in> L" if "(l, R) \<in> \<S>"
  using that unfolding \<S>_def by auto

lemma \<S>_inv:
  "(l, R) \<in> \<S> \<Longrightarrow> R \<subseteq> \<lbrace>inv_of A l\<rbrace>"
  unfolding \<S>_def by auto

lemma upper_right_closed:
  assumes "\<forall>c\<in>\<X>. real (k c) < u c" "u \<in> R" "R \<in> \<R>" "t \<ge> 0"
  shows "u \<oplus> t \<in> R"
proof -
  from \<open>R \<in> \<R>\<close> obtain I r where R:
    "R = region \<X> I r" "valid_region \<X> k I r"
  unfolding \<R>_def by auto
  from assms \<R>_V have "u \<in> V" by auto
  from assms R have "\<forall> c \<in> \<X>. I c = Greater (k c)" by safe (case_tac "I c"; fastforce)
  with R \<open>u \<in> V\<close> assms show
    "u \<oplus> t \<in> R"
  unfolding V_def by safe (rule; force simp: cval_add_def)
qed

lemma S_I[intro]:
  "(l, u) \<in> S" if "l \<in> L" "u \<in> V" "u \<turnstile> inv_of A l"
  using that by (auto simp: S_def V_def)

lemma rept_ex:
  assumes "\<mu> \<in> \<K> (abss s)"
  shows "rept s \<mu> \<in> K s \<and> abst (rept s \<mu>) = \<mu>" using assms
proof cases
  case prems: (delay l R R')
  then have "R \<in> \<R>" by auto
  from prems(2) have "s \<in> S" by (auto intro: \<S>_abss_S)
  from abss_\<S>D[OF prems(2)] obtain l' u' where "s = (l', u')" "u' \<in> [u']\<^sub>\<R>"
    by metis
  with prems(3) have *: "s = (l, u') \<and> u' \<in> R"
   apply simp
   apply (subst (asm) abss_S[OF \<S>_abss_S])
  using prems(2) by auto
  with prems(4) alpha_interp.set_of_regions_spec[OF \<open>R \<in> \<R>\<close>] obtain t where R':
    "t \<ge> 0" "R' = [u' \<oplus> t]\<^sub>\<R>"
  by auto
  with \<open>s \<in> S\<close> * have "u' \<oplus> t \<in> R'" "u' \<oplus> t \<in> V" "l \<in> L" by auto
  with prems(5) have "(l, u' \<oplus> t) \<in> S" unfolding S_def V_def by auto
  with \<open>R' = [u' \<oplus> t]\<^sub>\<R>\<close> have **: "abss (l, u' \<oplus> t) = (l, R')" by (auto simp: abss_S)
  let ?\<mu> = "return_pmf (l, u' \<oplus> t)"
  have "?\<mu> \<in> K s" using * \<open>s \<in> S\<close> \<open>t \<ge> 0\<close> \<open>u' \<oplus> t \<in> R'\<close> prems by blast
  moreover have "abst ?\<mu> = \<mu>" by (simp add: ** abst_def prems(1))
  moreover note default = calculation
  have "R' \<in> \<R>" using prems(4) by auto
  have R: "[u']\<^sub>\<R> = R" by (simp add: * \<open>R \<in> \<R>\<close> alpha_interp.region_unique_spec) 
  from \<open>R' \<in> \<R>\<close> obtain I r where R':
    "R' = region \<X> I r" "valid_region \<X> k I r"
  unfolding \<R>_def by auto
  have "u' \<in> V" using * prems \<R>_V by force
  let ?\<mu>' = "return_pmf (l, u' \<oplus> 0.5)"
  have elapsed: "abst (return_pmf (l, u' \<oplus> t)) = \<mu>" "return_pmf (l, u' \<oplus> t) \<in> K s"
    if "u' \<oplus> t \<in> R'" "t \<ge> 0" for t
  proof -
    let ?u = "u' \<oplus> t" let ?\<mu>' = "return_pmf (l, u' \<oplus> t)"
    from \<open>?u \<in> R'\<close> \<open>R' \<in> \<R>\<close> \<R>_V have "?u \<in> V" by auto
    with \<open>?u \<in> R'\<close> \<open>R' \<in> \<R>\<close> have "[?u]\<^sub>\<R> = R'" using alpha_interp.region_unique_spec by auto
    with \<open>?u \<in> V\<close> \<open>?u \<in> R'\<close> \<open>l \<in> L\<close> prems(4,5) have "abss (l, ?u) = (l, R')"
      by (subst abss_S) auto
    with prems(1) have "abst ?\<mu>' = \<mu>" by (auto simp: abst_def)
    moreover from * \<open>?u \<in> R'\<close> \<open>s \<in> S\<close> prems \<open>t \<ge> 0\<close> have "?\<mu>' \<in> K s" by auto
    ultimately show "abst ?\<mu>' = \<mu>" "?\<mu>' \<in> K s" by auto
  qed
  show ?thesis
  proof (cases "R = R'")
    case T: True
    show ?thesis
    proof (cases "\<forall> c \<in> \<X>. u' c > k c")
      case True
      with T * R prems(1,4) \<open>s \<in> S\<close> have
        "rept s \<mu> = return_pmf (l, u' \<oplus> 0.5)" (is "_ = ?\<mu>")
      unfolding rept_def by auto
      from upper_right_closed[OF True] * \<open>R' \<in> \<R>\<close> T have "u' \<oplus> 0.5 \<in> R'" by auto
      with elapsed \<open>rept _ _ = _\<close> show ?thesis by auto
    next
      case False
      with T * R prems(1) have
        "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
      unfolding rept_def by auto
      with default show ?thesis by simp (rule someI; auto)
    qed
  next
    case F: False
    show ?thesis
    proof (cases "\<forall> u \<in> R'. \<forall> c \<in> \<X>. \<nexists> d. d \<le> k c \<and> u c = real d")
      case False
      with F * R prems(1) have
        "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
      unfolding rept_def by auto
      with default show ?thesis by simp (rule someI; auto)
    next
      case True
      from True F * R prems(1,4) \<open>s \<in> S\<close> have
        "rept s \<mu> = return_pmf (l, delayedR (SOME R'. \<mu> = return_pmf (l, R')) u')"
        (is "_ = return_pmf (l, delayedR ?R u')")
      unfolding rept_def by auto
      let ?u = "delayedR ?R u'"
      from prems(1) have "\<mu> = return_pmf (l, ?R)" by auto
      with prems(1) have "?R = R'" by auto
      moreover from R' True \<open>_ \<in> R'\<close> have "\<forall>c\<in>\<X>. \<not> Regions.isConst (I c)" by fastforce
      moreover note delayedR_correct[of u' R I r] * \<open>R \<in> \<R>\<close> R' True \<open>R' \<in> Succ \<R> R\<close>
      ultimately obtain t where **: "delayedR R' u' \<in> R'" "t \<ge> 0" "delayedR R' u' = u' \<oplus> t" by auto
      moreover from \<open>?R =_ \<close>\<open>rept _ _ = _\<close> have "rept s \<mu> = return_pmf (l, delayedR R' u')" by auto
      ultimately show ?thesis using elapsed by auto
    qed
  qed
next
  case prems: (action l R \<tau> \<mu>')
  from abss_\<S>D'[OF prems(2,3)] obtain u where u:
    "s = (l, u)" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" "R = [u]\<^sub>\<R>"
  by auto
  with \<open>_ \<in> \<S>\<close> have "(l, u) \<in> S" by (auto intro: \<S>_abss_S)
  let ?\<mu> = "map_pmf (\<lambda>(X, l). (l, [X:=0]u)) \<mu>'"
  from u prems have "?\<mu> \<in> K s" by (fastforce intro: \<S>_abss_S)
  moreover have "abst ?\<mu> = \<mu>" unfolding prems(1) abst_def
   proof (subst map_pmf_comp, rule pmf.map_cong, safe, goal_cases)
     case A: (1 X l')
     from u have "u \<in> V" using \<R>_V by auto
     then have "[X:=0]u \<in> V" by auto
     from prems(1) A
     have "(l', region_set' R (SOME r. set r = X) 0) \<in> \<mu>" by auto
     from A prems R_G.K_closed \<open>\<mu> \<in> _\<close> have
        "l' \<in> L" "region_set' R (SOME r. set r = X) 0 \<subseteq> \<lbrace>inv_of A l'\<rbrace>"
     by (force dest: \<S>_L \<S>_inv)+
     with u have "[X:=0]u \<turnstile> inv_of A l'" unfolding region_set'_def by auto
     with \<open>l' \<in> L\<close> \<open>[X:=0]u \<in> V\<close> have "(l', [X:=0]u) \<in> S" unfolding S_def V_def by auto
     then have "abss (l', [X:=0]u) = (l', [[X:=0]u]\<^sub>\<R>)" by auto
     also have
       "\<dots> = (l', region_set' R (SOME r. set r = X) 0)"
     using region_set'_eq(1)[unfolded transition_def] prems A u by force
    finally show ?case .
  qed
  ultimately have default: ?thesis if "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)" using that
  by simp (rule someI; auto)
  show ?thesis
  proof (cases "\<exists> R. \<mu> = return_pmf (l, R)")
    case False
    with \<open>s = (l, u)\<close> have "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)" unfolding rept_def by auto
    with default show ?thesis by auto
  next
    case True
    then obtain R' where R': "\<mu> = return_pmf (l, R')" by auto
    show ?thesis
    proof (cases "R = R'")
      case False
      from R' prems(1) have
        "\<forall> (X, l') \<in> \<mu>'. (l', region_set' R (SOME r. set r = X) 0) = (l, R')"
      by (auto simp: map_pmf_eq_return_pmf_iff[of _ \<mu>' "(l, R')"])
      then obtain X where
        "region_set' R (SOME r. set r = X) 0 = R'" "(X, l) \<in> \<mu>'"
      using set_pmf_not_empty by force
      with prems(4) have "X \<subseteq> \<X>" by (simp add: admissible_targets_clocks(1))
      moreover then have
        "set (SOME r. set r = X) = X"
      by - (rule someI_ex, metis finite_list finite(1) finite_subset)
      ultimately have "set (SOME r. set r = X) \<subseteq> \<X>" by auto
      with alpha_interp.region_reset_not_Succ False \<open>_ = R'\<close> u(3,4) have "R' \<notin> Succ \<R> R" by auto
      with \<open>s = (l, u)\<close> R' u(4) False have
        "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
      unfolding rept_def by auto
      with default show ?thesis by auto
    next
      case T: True
      show ?thesis
      proof (cases "\<forall>c\<in>\<X>. real (k c) < u c")
        case False
        with T \<open>s = (l, u)\<close> R' u(4) have
          "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
        unfolding rept_def by auto
        with default show ?thesis by auto
      next
        case True
        with T \<open>s = (l, u)\<close> R' u(4) \<open>(l, u) \<in> S\<close> have
          "rept s \<mu> = return_pmf (l, u \<oplus> 0.5)"
        unfolding rept_def by auto
        from upper_right_closed[OF True] T u \<R>_V have "u \<oplus> 0.5 \<in> R'" "u \<oplus> 0.5 \<in> V" by force+
        moreover then have "[u \<oplus> 0.5]\<^sub>\<R> = R'"
          using T alpha_interp.region_unique_spec u(3,4) by blast 
        moreover note * = \<open>rept _ _ = _\<close> R' \<open>abss s \<in> \<S>\<close> \<open>abss s = _\<close> prems(5)
        ultimately have "abst (rept s \<mu>) = \<mu>"
         apply (simp add: abst_def)
         apply (subst abss_S)
        by (auto simp: \<S>_L S_def V_def T dest: \<S>_inv)
        moreover from * \<open>s = _\<close> \<open>(l, u) \<in> S\<close> \<open>_ \<in> R'\<close> have
          "rept s \<mu> \<in> K s"
         apply simp
         apply (rule K.delay)
        by (auto simp: T dest: \<S>_inv)
        ultimately show ?thesis by auto
      qed
    qed
  qed
next
  case loop
  obtain l u where "s = (l, u)" by force
  show ?thesis
  proof (cases "s \<in> S")
    case T: True
    with \<open>s = _\<close> have *: "l \<in> L" "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" "abss s = (l, [u]\<^sub>\<R>)" by auto
    then have "abss s = (l, [u]\<^sub>\<R>)" by auto
    with \<open>s \<in> S\<close> S_abss_\<S> have "(l, [u]\<^sub>\<R>) \<in> \<S>" by auto
    with \<S>_inv have "[u]\<^sub>\<R> \<subseteq> {u. u \<turnstile> inv_of A l}" by auto
    show ?thesis
    proof (cases "\<forall>c\<in>\<X>. real (k c) < u c")
      case True
      with * \<open>\<mu> = _\<close> \<open>s = _\<close> \<open>s \<in> S\<close> have
        "rept s \<mu> = return_pmf (l, u \<oplus> 0.5)"
      unfolding rept_def by auto
      from upper_right_closed[OF True] * have "u \<oplus> 0.5 \<in> [u]\<^sub>\<R>" by auto
      moreover with * \<R>_V have "u \<oplus> 0.5 \<in> V" by auto
      moreover with calculation * alpha_interp.region_unique_spec have "[u \<oplus> 0.5]\<^sub>\<R> = [u]\<^sub>\<R>" by blast
      moreover note * \<open>rept _ _ = _\<close> \<open>s = _\<close> T \<open>\<mu> = _\<close> \<open>(l, _) \<in> \<S>\<close> \<S>_inv
      ultimately show ?thesis unfolding rept_def
       apply simp
       apply safe
        apply fastforce
       apply (simp add: abst_def)
       apply (subst abst_def abss_S)
      by fastforce+
    next
      case False
      with * \<open>s = _\<close> \<open>\<mu> = _\<close> have
        "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
      unfolding rept_def by auto
      with \<open>\<mu> = _\<close> show ?thesis by simp (rule someI[where x = "return_pmf s"], auto simp: abst_def)
    qed
  next
    case False
    with \<open>s = _\<close> \<open>\<mu> = _\<close> have
        "rept s \<mu> = (SOME \<mu>'. \<mu>' \<in> K s \<and> abst \<mu>' = \<mu>)"
    unfolding rept_def by auto
    with \<open>\<mu> = _\<close> show ?thesis by simp (rule someI[where x = "return_pmf s"], auto simp: abst_def)
  qed
qed

lemmas rept_K[intro]       = rept_ex[THEN conjunct1]
lemmas abst_rept_id[simp]  = rept_ex[THEN conjunct2]

lemma abst_rept2:
  assumes "\<mu> \<in> \<K> s" "s \<in> \<S>"
  shows "abst (rept (reps s) \<mu>) = \<mu>"
using assms by auto

lemma rept_K2:
  assumes "\<mu> \<in> \<K> s" "s \<in> \<S>"
  shows "rept (reps s) \<mu> \<in> K (reps s)"
using assms by auto

(* XXX Move this. Does this exist anywhere? More elegant pattern? *)
lemma theI':
  assumes "P a"
    and "\<And>x. P x \<Longrightarrow> x = a"
  shows "P (THE x. P x) \<and> (\<forall> y. P y \<longrightarrow> y = (THE x. P x))"
using theI assms by metis

lemma cont_cfg_defined:
  fixes cfg s
  assumes "cfg \<in> valid_cfg" "s \<in> abst (action cfg)"
  defines "x \<equiv> THE x. abss x = s \<and> x \<in> action cfg"
  shows "(abss x = s \<and> x \<in> action cfg) \<and> (\<forall> y. abss y = s \<and> y \<in> action cfg \<longrightarrow> y = x)"
proof -
  from assms(2) obtain s' where "s' \<in> action cfg" "s = abss s'" unfolding abst_def by auto
  with assms show ?thesis unfolding x_def
  by -(rule theI'[of _ s'],auto intro: K_bisim_unique MDP.valid_cfg_state_in_S dest: MDP.valid_cfgD)
qed

definition
  absc' :: "('s * ('c, t) cval) cfg \<Rightarrow> ('s * ('c, t) cval set) cfg"
where
  "absc' cfg = cfg_corec
    (abss (state cfg))
    (abst o action)
    (\<lambda> cfg s. cont cfg (THE x. abss x = s \<and> x \<in> action cfg)) cfg"

subsubsection \<open>Configuration\<close>

definition
  absc :: "('s * ('c, t) cval) cfg \<Rightarrow> ('s * ('c, t) cval set) cfg"
where
  "absc cfg = cfg_corec
    (abss (state cfg))
    (abst o action)
    (\<lambda> cfg s. cont cfg (THE x. abss x = s \<and> x \<in> action cfg)) cfg"

definition
  repcs :: "'s * ('c, t) cval \<Rightarrow> ('s * ('c, t) cval set) cfg \<Rightarrow> ('s * ('c, t) cval) cfg"
where
  "repcs s cfg = cfg_corec
    s
    (\<lambda> (s, cfg). rept s (action cfg))
    (\<lambda> (s, cfg) s'. (s', cont cfg (abss s'))) (s, cfg)"

definition
  "repc cfg = repcs (reps (state cfg)) cfg"

lemma \<S>_state_absc_repc[simp]:
  "state cfg \<in> \<S> \<Longrightarrow> state (absc (repc cfg)) = state cfg"
by (simp add: absc_def repc_def repcs_def)

lemma action_repc:
  "action (repc cfg) = rept (reps (state cfg)) (action cfg)"
unfolding repc_def repcs_def by simp

(* XXX Declare simp? *)
lemma action_absc:
  "action (absc cfg) = abst (action cfg)"
unfolding absc_def by simp

lemma action_absc':
  "action (absc cfg) = map_pmf abss (action cfg)"
unfolding absc_def unfolding abst_def by simp

lemma
  notes R_G.cfg_onD_state[simp del]
  assumes "state cfg \<in> \<S>" "s' \<in> set_pmf (action (repc cfg))" "cfg \<in> R_G.cfg_on (state cfg)"
  shows "cont (repc cfg) s' = repcs s' (cont cfg (abss s'))"
using assms by (auto simp: repc_def repcs_def abss_reps_id)

lemma cont_repcs1:
  notes R_G.cfg_onD_state[simp del]
  assumes "abss s \<in> \<S>" "s' \<in> set_pmf (action (repcs s cfg))" "cfg \<in> R_G.cfg_on (abss s)"
  shows "cont (repcs s cfg) s' = repcs s' (cont cfg (abss s'))"
using assms by (auto simp: repc_def repcs_def abss_reps_id)

lemma cont_absc_1:
  notes MDP.cfg_onD_state[simp del]
  assumes "cfg \<in> valid_cfg" "s' \<in> set_pmf (action cfg)"
  shows "cont (absc cfg) (abss s') = absc (cont cfg s')"
proof -
  define x where "x \<equiv> THE x. x ~ s' \<and> x \<in> set_pmf (action cfg)"
  from assms(2) have "abss s' \<in> set_pmf (abst (action cfg))" unfolding abst_def by auto
  from cont_cfg_defined[OF assms(1) this] have
    "(x ~ s' \<and> x \<in> set_pmf (action cfg)) \<and> (\<forall>y. y ~ s' \<and> y \<in> set_pmf (action cfg) \<longrightarrow> y = x)"
  unfolding x_def .
  with assms have "s' = x" by fastforce
  then show ?thesis
  unfolding absc_def abst_def repc_def x_def using assms(2) by auto
qed

lemma state_repc:
  "state (repc cfg) = reps (state cfg)"
unfolding repc_def repcs_def by simp

lemma abss_reps_id':
  notes R_G.cfg_onD_state[simp del]
  assumes "cfg \<in> R_G.valid_cfg" "s \<in> set_pmf (action cfg)"
  shows "abss (reps s) = s"
using assms by (auto intro: abss_reps_id R_G.valid_cfg_state_in_S R_G.valid_cfgD)

(* XXX Move to different locale *)
lemma valid_cfg_coinduct[coinduct set: valid_cfg]:
  assumes "P cfg"
  assumes "\<And>cfg. P cfg \<Longrightarrow> state cfg \<in> S"
  assumes "\<And>cfg. P cfg \<Longrightarrow> action cfg \<in> K (state cfg)"
  assumes "\<And>cfg t. P cfg \<Longrightarrow> t \<in> action cfg \<Longrightarrow> P (cont cfg t)"
  shows "cfg \<in> valid_cfg"
proof -
  from assms have "cfg \<in> MDP.cfg_on (state cfg)" by (coinduction arbitrary: cfg) auto
  moreover from assms have "state cfg \<in> S" by auto
  ultimately show ?thesis by (intro MDP.valid_cfgI)
qed

lemma state_repcD[simp]:
  assumes "cfg \<in> R_G.cfg_on s"
  shows "state (repc cfg) = reps s"
using assms unfolding repc_def repcs_def by auto

(* XXX Move *)
lemma ccompatible_subs[intro]:
  assumes "ccompatible \<R> g" "R \<in> \<R>" "u \<in> R" "u \<turnstile> g"
  shows "R \<subseteq> {u. u \<turnstile> g}"
using assms unfolding ccompatible_def by auto

lemma action_abscD[dest]:
  "cfg \<in> MDP.cfg_on s \<Longrightarrow> action (absc cfg) \<in> \<K> (abss s)"
unfolding absc_def abst_def
proof simp
  assume cfg: "cfg \<in> MDP.cfg_on s"
  then have "action cfg \<in> K s" by auto
  then show "map_pmf abss (action cfg) \<in> \<K> (abss s)"
  proof cases
    case prems: (delay l u t)
    then have "[u \<oplus> t]\<^sub>\<R> \<in> \<R>" by auto
    moreover with prems ccompatible_inv[of l] have
      "[u \<oplus> t]\<^sub>\<R> \<subseteq> {v. v \<turnstile> PTA.inv_of A l}"
    unfolding ccompatible_def by force
    moreover from prems have "abss (l, u \<oplus> t) = (l, [u \<oplus> t]\<^sub>\<R>)" by (subst abss_S) auto
    ultimately show ?thesis using prems by auto
  next
    case prems: (action l u g \<mu>)
    then have "[u]\<^sub>\<R> \<in> \<R>" by auto
    moreover with prems ccompatible_guard have "[u]\<^sub>\<R> \<subseteq> {u. u \<turnstile> g}"
      by (intro ccompatible_subs) auto
    moreover have
      "map_pmf abss (action cfg)
      = map_pmf (\<lambda>(X, l). (l, region_set' ([u]\<^sub>\<R>) (SOME r. set r = X) 0)) \<mu>"
    proof -
      have "abss (l', [X:=0]u) = (l', region_set' ([u]\<^sub>\<R>) (SOME r. set r = X) 0)"
        if "(X, l') \<in> \<mu>" for X l'
      proof -
        from that prems have "A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'"
          by auto
        from that prems MDP.action_closed[OF _ cfg] have "(l', [X:=0]u) \<in> S" by force
        then have "abss (l', [X:=0]u) = (l', [[X:=0]u]\<^sub>\<R>)" by auto
        also have
          "\<dots> = (l', region_set' ([u]\<^sub>\<R>) (SOME r. set r = X) 0)"
          using region_set'_eq(1)[OF _ _ \<open>A \<turnstile> l \<longrightarrow>\<^bsup>g,\<mu>,X\<^esup> l'\<close>] prems by auto
        finally show ?thesis .
      qed
      then show ?thesis
        unfolding prems(1)
        by (auto intro: pmf.map_cong simp: map_pmf_comp)
    qed
    ultimately show ?thesis using prems by auto
  next
    case prems: loop
    then show ?thesis by auto
  qed
qed

lemma repcs_valid[intro]:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  shows "repcs s cfg \<in> valid_cfg"
using assms
proof (coinduction arbitrary: cfg s)
  case 1
  then show ?case
  by (auto simp: repcs_def \<S>_abss_S dest: R_G.valid_cfg_state_in_S)
next
  case (2 cfg' s)
  then show ?case
   by (simp add: repcs_def) (rule rept_K, auto dest: R_G.valid_cfgD)
next
  case prems: (3 s' cfg)
  let ?cfg = "cont cfg (abss s')"
  from prems have "abss s' \<in> abst (rept s (action cfg))" unfolding repcs_def abst_def by auto
  with prems have
    "abss s' \<in> action cfg"
  by (subst (asm) abst_rept_id) (auto dest: R_G.valid_cfgD)
  with prems show ?case
    by (inst_existentials ?cfg s', subst cont_repcs1)
       (auto dest: R_G.valid_cfg_state_in_S intro: R_G.valid_cfgD R_G.valid_cfg_cont)
qed

lemma repc_valid[intro]:
  assumes "cfg \<in> R_G.valid_cfg"
  shows "repc cfg \<in> valid_cfg"
using assms unfolding repc_def by (force dest: R_G.valid_cfg_state_in_S)

lemma action_abst_repcs:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  shows "abst (action (repcs s cfg)) = action cfg"
proof -
  from assms show ?thesis
  unfolding repc_def repcs_def
   apply simp
   apply (subst abst_rept_id)
  by (auto dest: R_G.cfg_onD_action R_G.valid_cfgD)
qed

lemma action_abst_repc:
  assumes "cfg \<in> R_G.valid_cfg"
  shows "abst (action (repc cfg)) = action cfg"
proof -
  from assms have "abss (reps (state cfg)) = state cfg" by (auto dest: R_G.valid_cfg_state_in_S)
  with action_abst_repcs[OF assms] show ?thesis unfolding repc_def by auto
qed

(* XXX Move *)
lemma state_absc:
  "state (absc cfg) = abss (state cfg)"
unfolding absc_def by auto

lemma state_repcs[simp]:
  "state (repcs s cfg) = s"
unfolding repcs_def by auto

lemma repcs_bisim:
  notes R_G.cfg_onD_state[simp del]
  assumes "cfg \<in> R_G.valid_cfg" "x \<in> S" "x ~ x'" "abss x = state cfg"
  shows "absc (repcs x cfg) = absc (repcs x' cfg)"
using assms
proof -
  from assms have "abss x' = state cfg" by auto
  from assms have "abss x' \<in> \<S>" by auto
  then have "x' \<in> S" by (auto intro: \<S>_abss_S)
  with assms show ?thesis  
  proof (coinduction arbitrary: cfg x x')
    case state
    then show ?case by (simp add: state_absc)
  next
    case action
    then show ?case unfolding absc_def repcs_def by (auto dest: R_G.valid_cfgD)
  next
    case prems: (cont s cfg x x')
    define cfg' where "cfg' = cont cfg s"
    define t    where "t \<equiv> THE y. abss y = s \<and> y \<in> action (repcs x cfg)"
    define t'   where "t' \<equiv>THE y. abss y = s \<and> y \<in> action (repcs x' cfg)"
    from prems have valid: "repcs x cfg \<in> valid_cfg" by (intro repcs_valid)
    from prems have *: "s \<in> abst (action (repcs x cfg))"
      unfolding cfg'_def by (simp add: action_absc)
    with prems have "s \<in> action cfg" by (auto dest: R_G.valid_cfgD simp: repcs_def)
    with prems have "s \<in> \<S>" by (auto intro: R_G.valid_cfg_action)
    from cont_cfg_defined[OF valid *] have t:
      "abss t = s" "t \<in> action (repcs x cfg)"
      unfolding t_def by auto
    have "cont (absc (repcs x cfg)) s = cont (absc (repcs x cfg)) (abss t)" using t by auto
    have "cont (absc (repcs x cfg)) s = absc (cont (repcs x cfg) t)"
      using t valid by (auto simp: cont_absc_1)
    also have "\<dots> = absc (repcs t (cont cfg s))"
      using prems t by (subst cont_repcs1) (auto dest: R_G.valid_cfgD)
    finally have cont_x: "cont (absc (repcs x cfg)) s = absc (repcs t (cont cfg s))" .
    from prems have valid: "repcs x' cfg \<in> valid_cfg" by auto
    from \<open>s \<in> action cfg\<close> prems have "s \<in> abst (action (repcs x' cfg))"
      by (auto dest: R_G.valid_cfgD simp: repcs_def)
    from cont_cfg_defined[OF valid this] have t':
      "abss t' = s" "t' \<in> action (repcs x' cfg)"
    unfolding t'_def by auto
    have "cont (absc (repcs x' cfg)) s = cont (absc (repcs x' cfg)) (abss t')" using t' by auto
    have "cont (absc (repcs x' cfg)) s = absc (cont (repcs x' cfg) t')"
      using t' valid by (auto simp: cont_absc_1)
    also have "\<dots> = absc (repcs t' (cont cfg s))"
      using prems t' by (subst cont_repcs1) (auto dest: R_G.valid_cfgD)
    finally have "cont (absc (repcs x' cfg)) s = absc (repcs t' (cont cfg s))" .
    with cont_x \<open>s \<in> action cfg\<close> prems(1) t t' \<open>s \<in> \<S>\<close>
    show ?case
      by (inst_existentials "cont cfg s" t t')
         (auto intro: \<S>_abss_S R_G.valid_cfg_action R_G.valid_cfg_cont)
  qed
qed

named_theorems R_G_I

lemmas R_G.valid_cfg_state_in_S[R_G_I] R_G.valid_cfgD[R_G_I] R_G.valid_cfg_action

(* XXX Simplifier looping problems on cfg_on
   If R_G.cfg_onD_state is not removed from simpset, the simplifier rewrites state cfg = state cfg.
*)
lemma absc_repcs_id:
  notes R_G.cfg_onD_state[simp del]
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  shows "absc (repcs s cfg) = cfg" using assms
proof (subst eq_commute, coinduction arbitrary: cfg s)
  case state
  then show ?case by (simp add: absc_def repc_def repcs_def)
next
  case prems: (action cfg)
  then show ?case by (auto simp: action_abst_repcs action_absc)
next
  case prems: (cont s')
  define cfg' where "cfg' \<equiv> repcs s cfg"
  define t    where "t    \<equiv> THE x. abss x = s' \<and> x \<in> set_pmf (action cfg')"
  from prems have "cfg \<in> R_G.cfg_on (state cfg)" "state cfg \<in> \<S>" by (auto dest: R_G_I)
  then have *: "cfg \<in> R_G.cfg_on (abss (reps (state cfg)))" "abss (reps (state cfg)) \<in> \<S>" by auto
  from prems have "s' \<in> \<S>" by (auto intro: R_G.valid_cfg_action)
  from prems have valid: "cfg' \<in> valid_cfg" unfolding cfg'_def by (intro repcs_valid)
  from prems have "s' \<in> abst (action cfg')" unfolding cfg'_def by (subst action_abst_repcs)
  from cont_cfg_defined[OF valid this] have t:
    "abss t = s'" "t \<in> action cfg'"
  unfolding t_def cfg'_def by auto
  with prems have "t ~ reps (abss t)"
   apply -
   apply (subst \<S>_abss_reps)
  by (auto intro: R_G.valid_cfg_action)
  have "cont (absc cfg') s' = cont (absc cfg') (abss t)" using t by auto
  have "cont (absc cfg') s' = absc (cont cfg' t)" using t valid by (auto simp: cont_absc_1)
  also have "\<dots> = absc (repcs t (cont cfg s'))" using prems t * \<open>t ~ _\<close> valid
  by (fastforce dest: R_G_I intro: repcs_bisim simp: cont_repcs1 cfg'_def)
  finally show ?case
   apply -
   apply (rule exI[where x = "cont cfg s'"], rule exI[where x = t])
  unfolding cfg'_def using prems t by (auto intro: R_G.valid_cfg_cont)
qed

(* XXX Simplifier looping problems on cfg_on
   If R_G.cfg_onD_state is not removed from simpset, the simplifier rewrites state cfg = state cfg.
*)
lemma absc_repc_id:
  notes R_G.cfg_onD_state[simp del]
  assumes "cfg \<in> R_G.valid_cfg"
  shows "absc (repc cfg) = cfg" using assms
unfolding repc_def using assms by (subst absc_repcs_id) (auto dest: R_G_I)

lemma K_cfg_map_absc:
  "cfg \<in> valid_cfg \<Longrightarrow> K_cfg (absc cfg) = map_pmf absc (K_cfg cfg)"
by (auto simp: K_cfg_def map_pmf_comp action_absc abst_def cont_absc_1 intro: map_pmf_cong)

(* XXX Move *)
lemma smap_comp:
  "(smap f o smap g) = smap (f o g)"
by (auto simp: stream.map_comp)

lemma state_abscD[simp]:
  assumes "cfg \<in> MDP.cfg_on s"
  shows "state (absc cfg) = abss s"
using assms unfolding absc_def by auto

(* XXX Move to different locale *)
lemma R_G_valid_cfg_coinduct[coinduct set: valid_cfg]:
  assumes "P cfg"
  assumes "\<And>cfg. P cfg \<Longrightarrow> state cfg \<in> \<S>"
  assumes "\<And>cfg. P cfg \<Longrightarrow> action cfg \<in> \<K> (state cfg)"
  assumes "\<And>cfg t. P cfg \<Longrightarrow> t \<in> action cfg \<Longrightarrow> P (cont cfg t)"
  shows "cfg \<in> R_G.valid_cfg"
proof -
  from assms have "cfg \<in> R_G.cfg_on (state cfg)" by (coinduction arbitrary: cfg) auto
  moreover from assms have "state cfg \<in> \<S>" by auto
  ultimately show ?thesis by (intro R_G.valid_cfgI)
qed

lemma absc_valid[intro]:
  assumes "cfg \<in> valid_cfg"
  shows "absc cfg \<in> R_G.valid_cfg"
using assms
proof (coinduction arbitrary: cfg)
  case 1
  then show ?case by (auto simp: absc_def dest: MDP.valid_cfg_state_in_S)
next
  case (2 cfg')
  then show ?case by (subst state_abscD) (auto intro: MDP.valid_cfgD action_abscD)
next
  case prems: (3 s' cfg)
  define t where "t \<equiv> THE x. abss x = s' \<and> x \<in> set_pmf (action cfg)"
  let ?cfg = "cont cfg t"
  from prems obtain s where "s' = abss s" "s \<in> action cfg" by (auto simp: action_absc')
  with cont_cfg_defined[OF prems(1), of s'] have
    "abss t = s'" "t \<in> set_pmf (action cfg)"
    "\<forall>y. abss y = s' \<and> y \<in> set_pmf (action cfg) \<longrightarrow> y = t"
  unfolding t_def abst_def by auto
  with prems show ?case
    by (inst_existentials ?cfg)
       (auto intro: MDP.valid_cfg_cont simp: abst_def action_absc absc_def t_def)
qed

lemma K_cfg_set_absc:
  assumes "cfg \<in> valid_cfg" "cfg' \<in> K_cfg cfg"
  shows "absc cfg' \<in> K_cfg (absc cfg)"
using assms by (auto simp: K_cfg_map_absc)

lemma abst_action_repcs:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  shows "abst (action (repcs s cfg)) = action cfg"
unfolding repc_def repcs_def using assms by (simp, subst abst_rept_id) (auto intro: R_G_I)

lemma abst_action_repc:
  assumes "cfg \<in> R_G.valid_cfg"
  shows "abst (action (repc cfg)) = action cfg"
using assms unfolding repc_def by (auto intro: abst_action_repcs simp: R_G_I)

lemma K_elem_abss_inj':
  assumes "\<mu> \<in> K s"
    and "s \<in> S"
  shows "inj_on abss (set_pmf \<mu>)"
using assms K_elem_abss_inj by (simp add: K_bisim_unique inj_onI)

lemma K_cfg_rept_aux:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg" "x \<in> rept s (action cfg)"
  defines "t \<equiv> \<lambda> cfg'. THE s'. s' \<in> rept s (action cfg) \<and> s' ~ x"
  shows "t cfg' = x"
proof -
  from assms have "rept s (action cfg) \<in> K s" "s \<in> S" by (auto simp: R_G_I \<S>_abss_S)
  from K_bisim_unique[OF this(2,1) _ assms(3)] assms(3) show ?thesis unfolding t_def by blast
qed

lemma K_cfg_rept_action:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg" "cfg' \<in> set_pmf (K_cfg cfg)"
  shows "abss (THE s'. s' \<in> rept s (action cfg) \<and> abss s' = state cfg') = state cfg'"
proof -
  let ?\<mu> = "rept s (action cfg)"
  from abst_rept_id assms have "action cfg = abst ?\<mu>" by (auto simp: R_G_I)
  moreover from assms have "state cfg' \<in> action cfg" by (auto simp: set_K_cfg)
  ultimately have "state cfg' \<in> abst ?\<mu>" by simp
  then obtain s' where "s' \<in> ?\<mu>" "abss s' = state cfg'" by (auto simp: abst_def pmf.set_map)
  with K_cfg_rept_aux[OF assms(1,2) this(1)] show ?thesis by auto
qed

lemma K_cfg_map_repcs:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  defines "repc' \<equiv> (\<lambda> cfg'. repcs (THE s'. s' \<in> rept s (action cfg) \<and> abss s' = state cfg') cfg')"
  shows "K_cfg (repcs s cfg) = map_pmf repc' (K_cfg cfg)"
proof -
  let ?\<mu> = "rept s (action cfg)"
  define t where "t \<equiv> \<lambda> cfg'. THE s. s \<in> ?\<mu> \<and> abss s = state cfg'"
  have t: "t (cont cfg (abss s')) = s'" if "s' \<in> ?\<mu>" for s'
    using K_cfg_rept_aux[OF assms(1,2) that] unfolding t_def by auto
  show ?thesis
    unfolding K_cfg_def using t
    by (subst abst_action_repcs[symmetric])
       (auto simp: repc_def repcs_def t_def map_pmf_comp abst_def assms intro: map_pmf_cong)
qed

lemma K_cfg_map_repc:
  assumes "cfg \<in> R_G.valid_cfg"
  defines
    "repc' cfg' \<equiv> repcs (THE s. s \<in> rept (reps (state cfg)) (action cfg) \<and> abss s = state cfg') cfg'"
  shows 
    "K_cfg (repc cfg) = map_pmf repc' (K_cfg cfg)"
using assms unfolding repc'_def repc_def by (auto simp: R_G_I K_cfg_map_repcs)

lemma R_G_K_cfg_valid_cfgD:
  assumes "cfg \<in> R_G.valid_cfg" "cfg' \<in> K_cfg cfg"
  shows "cfg' = cont cfg (state cfg')" "state cfg' \<in> action cfg"
proof -
  from assms(2) obtain s where "s \<in> action cfg" "cfg' = cont cfg s" by (auto simp: set_K_cfg)
  with assms show
    "cfg' = cont cfg (state cfg')" "state cfg' \<in> action cfg"
  by (auto intro: R_G.valid_cfg_state_in_S R_G.valid_cfgD)
qed

lemma K_cfg_valid_cfgD:
  assumes "cfg \<in> valid_cfg" "cfg' \<in> K_cfg cfg"
  shows "cfg' = cont cfg (state cfg')" "state cfg' \<in> action cfg"
proof -
  from assms(2) obtain s where "s \<in> action cfg" "cfg' = cont cfg s" by (auto simp: set_K_cfg)
  with assms show
    "cfg' = cont cfg (state cfg')" "state cfg' \<in> action cfg"
  by auto
qed

(* XXX Move *)
lemma absc_bisim_abss:
  assumes "absc x = absc x'"
  shows "state x ~ state x'"
proof -
  from assms have "state (absc x) = state (absc x')" by simp
  then show ?thesis by (simp add: state_absc)
qed

(* XXX Move *)
lemma K_cfg_bisim_unique:
  assumes "cfg \<in> valid_cfg" and "x \<in> K_cfg cfg" "x' \<in> K_cfg cfg" and "state x ~ state x'"
  shows "x = x'"
proof -
  define t where "t \<equiv> THE x'. x' ~ state x \<and> x' \<in> set_pmf (action cfg)"
  from K_cfg_valid_cfgD assms have *:
    "x  = cont cfg (state x)"  "state x \<in> action cfg"
    "x' = cont cfg (state x')" "state x' \<in> action cfg"
    by auto
  with assms have
    "cfg \<in> valid_cfg" "abss (state x) \<in> set_pmf (abst (action cfg))"
    unfolding abst_def by auto
  with cont_cfg_defined[of cfg "abss (state x)"] have
    "\<forall>y. y ~ state x \<and> y \<in> set_pmf (action cfg) \<longrightarrow> y = t"
    unfolding t_def by auto
  with * assms(4) have "state x' = t" "state x = t" by fastforce+
  with * show ?thesis by simp
qed

lemma absc_distr_self:
  "MDP.MC.T (absc cfg) = distr (MDP.MC.T cfg) MDP.MC.S (smap absc)" if "cfg \<in> valid_cfg"
  using \<open>cfg \<in> _\<close>
proof (coinduction arbitrary: cfg rule: MDP.MC.T_coinduct)
  case prob
  show ?case by (rule MDP.MC.T.prob_space_distr, simp)
next
  case sets
  show ?case by auto
next
  case prems: (cont cfg)
  define t  where "t  \<equiv> \<lambda> y. THE x. y = absc x \<and> x \<in> K_cfg cfg"
  define M' where "M' \<equiv> \<lambda> cfg. distr (MDP.MC.T (t cfg)) MDP.MC.S (smap absc)"
  show ?case
  proof (rule exI[where x = M'], safe, goal_cases)
    case A: (1 y)
    from A prems obtain x' where "y = absc x'" "x' \<in> K_cfg cfg" by (auto simp: K_cfg_map_absc)
    with K_cfg_bisim_unique[OF prems _ _ absc_bisim_abss] have
      "y = absc (t y)" "x' = t y"
      unfolding t_def by (auto intro: theI2)
    moreover have "x' \<in> valid_cfg" using \<open>x' \<in> _\<close> prems by auto
    ultimately show ?case unfolding M'_def by auto
  next
    case 5
    show ?case unfolding M'_def
      apply (subst distr_distr)
        prefer 3
        apply (subst MDP.MC.T_eq_bind)
        apply (subst distr_bind)
           prefer 4
           apply (subst distr_distr)
             prefer 3
             apply (subst K_cfg_map_absc)
              apply (rule prems)
             apply (subst map_pmf_rep_eq)
             apply (subst bind_distr)
               prefer 4
               apply (rule bind_measure_pmf_cong)
                 prefer 3
      subgoal premises A for x
      proof -
        have "t (absc x) = x" unfolding t_def
        proof (rule the_equality, goal_cases)
          case 1 with A show ?case by simp
        next
          case (2 x')
          with K_cfg_bisim_unique[OF prems _ A absc_bisim_abss] show ?case by simp
        qed
        then show ?thesis by (auto simp: comp_def)
      qed
      by (fastforce
          simp:  space_subprob_algebra MC_syntax.in_S
          intro: bind_measure_pmf_cong MDP.MC.T.subprob_space_distr MDP.MC.T.prob_space_distr
          )+
  qed (auto simp: M'_def intro: MDP.MC.T.prob_space_distr)
qed

lemma R_G_trace_space_distr_eq:
  assumes "cfg \<in> R_G.valid_cfg" "abss s = state cfg"
  shows "MDP.MC.T cfg = distr (MDP.MC.T (repcs s cfg)) MDP.MC.S (smap absc)"
using assms
proof (coinduction arbitrary: cfg s rule: MDP.MC.T_coinduct)
  case prob
  show ?case by (rule MDP.MC.T.prob_space_distr, simp) 
next
  case sets
  show ?case by auto
next
  case prems: (cont cfg s)
  let ?\<mu> = "rept s (action cfg)"
  define repc' where "repc' \<equiv> \<lambda> cfg'. repcs (THE s. s \<in> ?\<mu> \<and> abss s = state cfg') cfg'"
  define M' where "M' \<equiv> \<lambda> cfg. distr (MDP.MC.T (repc' cfg)) MDP.MC.S (smap absc)"
  show ?case
  proof (intro exI[where x = M'], safe, goal_cases)
    case A: (1 cfg')
    with K_cfg_rept_action[OF prems] have
      "abss (THE s. s \<in> ?\<mu> \<and> abss s = state cfg') = state cfg'"
    by auto
    moreover from A prems have "cfg' \<in> R_G.valid_cfg" by auto
    ultimately show ?case unfolding M'_def repc'_def by best
  next
    case 4
    show ?case unfolding M'_def by (rule MDP.MC.T.prob_space_distr, simp)
  next
    case 5
    have *: "smap absc \<circ> (##) (repc' cfg') = (##) cfg' \<circ> smap absc"
    if "cfg' \<in> set_pmf (K_cfg cfg)" for cfg'
    proof -
      from K_cfg_rept_action[OF prems that] have
        "abss (THE s. s \<in> ?\<mu> \<and> abss s = state cfg') = state cfg'"
      .
      with prems that have *:
        "absc (repc' cfg') = cfg'"
      unfolding repc'_def by (subst absc_repcs_id, auto)
      then show "(smap absc \<circ> (##) (repc' cfg')) = ((##) cfg' \<circ> smap absc)" by auto
    qed
    from prems show ?case unfolding M'_def
      apply (subst distr_distr)
        apply simp+
      apply (subst MDP.MC.T_eq_bind)
      apply (subst distr_bind)
         prefer 2
         apply simp
        apply (rule MDP.MC.distr_Stream_subprob)
       apply simp
      apply (subst distr_distr)
        apply simp+
      apply (subst K_cfg_map_repcs[OF prems])
      apply (subst map_pmf_rep_eq)
      apply (subst bind_distr)
    by (fastforce simp: *[unfolded repc'_def] repc'_def space_subprob_algebra MC_syntax.in_S
                  intro: bind_measure_pmf_cong MDP.MC.T.subprob_space_distr)+
  qed (simp add: M'_def)+
qed

lemma repc_inj_on_K_cfg:
  assumes "cfg \<in> R_G.cfg_on s" "s \<in> \<S>"
  shows "inj_on repc (set_pmf (K_cfg cfg))"
  using assms
  by (intro inj_on_inverseI[where g = absc], subst absc_repc_id)
     (auto intro: R_G.valid_cfgD R_G.valid_cfgI R_G.valid_cfg_state_in_S)

lemma smap_absc_iff:
  assumes "\<And> x y. x \<in> X \<Longrightarrow> smap abss x = smap abss y \<Longrightarrow> y \<in> X"
  shows "(smap state xs \<in> X) = (smap (\<lambda>z. abss (state z)) xs \<in> smap abss ` X)"
proof (safe, goal_cases)
  case 1
  then show ?case unfolding image_def
    by clarify (inst_existentials "smap state xs", auto simp: stream.map_comp)
next
  case prems: (2 xs')
  have
    "smap (\<lambda>z. abss (state z)) xs = smap abss (smap state xs)"
  by (auto simp: comp_def stream.map_comp)
  with prems have "smap abss (smap state xs) = smap abss xs'" by simp
  with prems(2) assms show ?case by auto
qed

lemma valid_abss_reps[simp]:
  assumes "cfg \<in> R_G.valid_cfg"
  shows "abss (reps (state cfg)) = state cfg"
using assms by (subst \<S>_abss_reps) (auto intro: R_G.valid_cfg_state_in_S)

lemma in_space_UNIV: "x \<in> space (count_space UNIV)"
  by simp

lemma S_reps_\<S>_aux:
  "reps (l, R) \<in> S \<Longrightarrow> (l, R) \<in> \<S>"
  using ccompatible_inv unfolding reps_def ccompatible_def \<S>_def S_def
  by (cases "R \<in> \<R>"; auto simp: non_empty)

(* XXX Move *)
lemma S_reps_\<S>[intro]:
  "reps s \<in> S \<Longrightarrow> s \<in> \<S>"
  using S_reps_\<S>_aux by (metis surj_pair)

lemma absc_valid_cfg_eq:
  "absc ` valid_cfg = R_G.valid_cfg"
  apply safe
  subgoal
    by auto
  subgoal for cfg
    using absc_repcs_id[where s = "reps (state cfg)"]
    by - (frule repcs_valid[where s = "reps (state cfg)"]; force intro: imageI)
  done

lemma action_repcs:
  "action (repcs (l, u) cfg) = rept (l, u) (action cfg)"
  by (simp add: repcs_def)

subsection \<open>Equalities Between Measures of Trace Spaces\<close>

(* TODO: Clean *)
lemma path_measure_eq_absc1_new:
  fixes cfg s
  defines "cfg' \<equiv> absc cfg"
  assumes valid: "cfg \<in> valid_cfg"
  assumes X[measurable]: "X \<in> R_G.St" and Y[measurable]: "Y \<in> MDP.St"
  assumes P: "AE x in (R_G.T cfg'). P x" and Q: "AE x in (MDP.T cfg). Q x"
  assumes P'[measurable]: "Measurable.pred R_G.St P"
      and Q'[measurable]: "Measurable.pred MDP.St Q"
  assumes X_Y_closed: "\<And> x y. P x \<Longrightarrow> smap abss y = x \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<and> Q y"
  assumes Y_X_closed: "\<And> x y. Q y \<Longrightarrow> smap abss y = x \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<in> X \<and> P x"
  shows
    "emeasure (R_G.T cfg') X = emeasure (MDP.T cfg) Y"
proof -
  have *: "stream_all2 (\<lambda>s. (=) (absc s)) x y = stream_all2 (=) (smap absc x) y" for x y
    by simp
  have *: "stream_all2 (\<lambda>s t. t = absc s) x y = stream_all2 (=) y (smap absc x)" for x y
    using stream.rel_conversep[of "\<lambda>s t. t = absc s"]
    by (simp add: conversep_iff[abs_def])

  from P have "emeasure (R_G.T cfg') X = emeasure (R_G.T cfg') {x \<in> X. P x}"
    by (auto intro: emeasure_eq_AE)
  moreover from Q have "emeasure (MDP.T cfg) Y = emeasure (MDP.T cfg) {y \<in> Y. Q y}"
    by (auto intro: emeasure_eq_AE)
  moreover show ?thesis
   apply (simp only: calculation)
    unfolding R_G.T_def MDP.T_def
    apply (simp add: emeasure_distr)
    apply (rule sym)
    apply (rule T_eq_rel_half[where f = absc and S = valid_cfg])
         apply (rule HOL.refl)
    apply measurable
      apply (simp add: space_stream_space)
    subgoal
      unfolding rel_set_strong_def stream.rel_eq
      apply (intro allI impI)
      apply (drule stream.rel_mono_strong[where Ra = "\<lambda>s t. t = absc s"])
       apply (simp; fail)
      subgoal for x y
      using Y_X_closed[of "smap state x" "smap state (smap absc x)" for x y]
      using X_Y_closed[of "smap state (smap absc x)" "smap state x" for x y]
      by (auto simp: * stream.rel_eq stream.map_comp state_absc)+
    done
    subgoal
      apply (auto intro!: rel_funI)
      apply (subst K_cfg_map_absc)
       defer
       apply (subst pmf.rel_map(2))
       apply (rule rel_pmf_reflI)
      by auto
    subgoal
      using valid unfolding cfg'_def by simp
    done
qed

(* TODO: Clean duplication *)
lemma path_measure_eq_repcs1_new:
  fixes cfg s
  defines "cfg' \<equiv> repcs s cfg"
  assumes s: "abss s = state cfg"
  assumes valid: "cfg \<in> R_G.valid_cfg"
  assumes X[measurable]: "X \<in> R_G.St" and Y[measurable]: "Y \<in> MDP.St"
  assumes P: "AE x in (R_G.T cfg). P x" and Q: "AE x in (MDP.T cfg'). Q x"
  assumes P'[measurable]: "Measurable.pred R_G.St P"
      and Q'[measurable]: "Measurable.pred MDP.St Q"
  assumes X_Y_closed: "\<And> x y. P x \<Longrightarrow> smap abss y = x \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> Y \<and> Q y"
  assumes Y_X_closed: "\<And> x y. Q y \<Longrightarrow> smap abss y = x \<Longrightarrow> y \<in> Y \<Longrightarrow> x \<in> X \<and> P x"
  shows
    "emeasure (R_G.T cfg) X = emeasure (MDP.T cfg') Y"
proof -
  have *: "stream_all2 (\<lambda>s t. t = absc s) x y = stream_all2 (=) y (smap absc x)" for x y
    using stream.rel_conversep[of "\<lambda>s t. t = absc s"]
    by (simp add: conversep_iff[abs_def])
  from P X have
    "emeasure (R_G.T cfg) X = emeasure (R_G.T cfg) {x \<in> X. P x}"
    by (auto intro: emeasure_eq_AE)
  moreover from Q Y have
    "emeasure (MDP.T cfg') Y = emeasure (MDP.T cfg') {y \<in> Y. Q y}"
    by (auto intro: emeasure_eq_AE)
  moreover show ?thesis
    apply (simp only: calculation)
    unfolding R_G.T_def MDP.T_def
    apply (simp add: emeasure_distr)
    apply (rule sym)
    apply (rule T_eq_rel_half[where f = absc and S = valid_cfg])
         apply (rule HOL.refl)
        apply measurable
      apply (simp add: space_stream_space)
    subgoal
      unfolding rel_set_strong_def stream.rel_eq
      apply (intro allI impI)
      apply (drule stream.rel_mono_strong[where Ra = "\<lambda>s t. t = absc s"])
       apply (simp; fail)
      subgoal for x y
        using Y_X_closed[of "smap state x" "smap state (smap absc x)" for x y]
        using X_Y_closed[of "smap state (smap absc x)" "smap state x" for x y]
        by (auto simp: * stream.rel_eq stream.map_comp state_absc)+
      done
    subgoal
      apply (auto intro!: rel_funI)
      apply (subst K_cfg_map_absc)
       defer
       apply (subst pmf.rel_map(2))
       apply (rule rel_pmf_reflI)
      by auto
    subgoal
      using valid unfolding cfg'_def by (auto simp: s absc_repcs_id)
    done
qed

lemma region_compatible_suntil1:
  assumes "(holds (\<lambda>x. \<phi> (reps x)) suntil holds (\<lambda>x. \<psi> (reps x))) (smap abss x)"
      and "pred_stream (\<lambda> s. \<phi> (reps (abss s)) \<longrightarrow> \<phi> s) x"
      and "pred_stream (\<lambda> s. \<psi> (reps (abss s)) \<longrightarrow> \<psi> s) x"
  shows "(holds \<phi> suntil holds \<psi>) x" using assms
proof (induction "smap abss x" arbitrary: x rule: suntil.induct)
  case base
  then show ?case by (auto intro: suntil.base simp: stream.pred_set)
next
  case step
  have
    "pred_stream (\<lambda>s. \<phi> (reps (abss s)) \<longrightarrow> \<phi> s) (stl x)"
    "pred_stream (\<lambda>s. \<psi> (reps (abss s)) \<longrightarrow> \<psi> s) (stl x)"
    using step.prems apply (cases x; auto)
    using step.prems apply (cases x; auto)
    done
  with step.hyps(3)[of "stl x"] have "(holds \<phi> suntil holds \<psi>) (stl x)" by auto
  with step.prems step.hyps(1-2) show ?case by (auto intro: suntil.step simp: stream.pred_set)
qed

lemma region_compatible_suntil2:
  assumes "(holds \<phi> suntil holds \<psi>) x"
      and "pred_stream (\<lambda> s. \<phi> s \<longrightarrow> \<phi> (reps (abss s))) x"
      and "pred_stream (\<lambda> s. \<psi> s \<longrightarrow> \<psi> (reps (abss s))) x"
  shows "(holds (\<lambda>x. \<phi> (reps x)) suntil holds (\<lambda>x. \<psi> (reps x))) (smap abss x)" using assms
proof (induction x rule: suntil.induct)
  case (base x)
  then show ?case by (auto intro: suntil.base simp: stream.pred_set)
next
  case (step x)
  have
    "pred_stream (\<lambda>s. \<phi> s \<longrightarrow> \<phi> (reps (abss s))) (stl x)"
    "pred_stream (\<lambda>s. \<psi> s \<longrightarrow> \<psi> (reps (abss s))) (stl x)"
    using step.prems apply (cases x; auto)
    using step.prems apply (cases x; auto)
    done
  with step show ?case by (auto intro: suntil.step simp: stream.pred_set)
qed

lemma region_compatible_suntil:
  assumes "pred_stream (\<lambda> s. \<phi> (reps (abss s)) \<longleftrightarrow> \<phi> s) x"
      and "pred_stream (\<lambda> s. \<psi> (reps (abss s)) \<longleftrightarrow> \<psi> s) x"
  shows "(holds (\<lambda>x. \<phi> (reps x)) suntil holds (\<lambda>x. \<psi> (reps x))) (smap abss x)
     \<longleftrightarrow> (holds \<phi> suntil holds \<psi>) x" using assms
using assms region_compatible_suntil1 region_compatible_suntil2 unfolding stream.pred_set by blast

lemma reps_abss_S:
  assumes "reps (abss s) \<in> S"
  shows "s \<in> S"
by (simp add: S_reps_\<S> \<S>_abss_S assms)

lemma measurable_sset[measurable (raw)]:
  assumes f[measurable]: "f \<in> N \<rightarrow>\<^sub>M stream_space M" and P[measurable]: "Measurable.pred M P"
  shows "Measurable.pred N (\<lambda>x. \<forall>s\<in>sset (f x). P s)"
proof -
  have *: "(\<lambda>x. \<forall>s\<in>sset (f x). P s) = (\<lambda>x. \<forall>i. P (f x !! i))"
    by (simp add: sset_range)
  show ?thesis
    unfolding * by measurable
qed

lemma path_measure_eq_repcs''_new:
  notes in_space_UNIV[measurable]
  fixes cfg \<phi> \<psi> s
  defines "cfg' \<equiv> repcs s cfg"
  defines "\<phi>' \<equiv> absp \<phi>" and "\<psi>' \<equiv> absp \<psi>"
  assumes s: "abss s = state cfg"
  assumes valid: "cfg \<in> R_G.valid_cfg"
  assumes valid': "cfg' \<in> valid_cfg"
  assumes equiv_\<phi>: "\<And> x. pred_stream (\<lambda> s. s \<in> S) x
                    \<Longrightarrow> pred_stream (\<lambda> s. \<phi> (reps (abss s)) \<longleftrightarrow> \<phi> s) (state cfg' ## x)"
    and equiv_\<psi>: "\<And> x. pred_stream (\<lambda> s. s \<in> S) x
                    \<Longrightarrow> pred_stream (\<lambda> s. \<psi> (reps (abss s)) \<longleftrightarrow> \<psi> s) (state cfg' ## x)"
  shows
    "emeasure (R_G.T cfg)  {x\<in>space R_G.St. (holds \<phi>' suntil holds \<psi>') (state cfg  ## x)} =
     emeasure (MDP.T cfg') {x\<in>space MDP.St. (holds \<phi>  suntil holds \<psi>)  (state cfg' ## x)}"
  unfolding cfg'_def
  apply (rule path_measure_eq_repcs1_new[where P = "pred_stream (\<lambda> s. s \<in> \<S>)" and Q = "pred_stream (\<lambda> s. s \<in> S)"])
           apply fact
          apply fact
         apply measurable
  subgoal
    unfolding R_G.T_def
    apply (subst AE_distr_iff)
      apply (auto; fail)
     apply (auto simp: stream.pred_set; fail)
    apply (rule AE_mp[OF MDP.MC.AE_T_enabled AE_I2])
    using R_G.pred_stream_cfg_on[OF valid] by (auto simp: stream.pred_set)
  subgoal
    unfolding MDP.T_def
    apply (subst AE_distr_iff)
      apply (auto; fail)
     apply (auto simp: stream.pred_set; fail)
    apply (rule AE_mp[OF MDP.MC.AE_T_enabled AE_I2])
    using MDP.pred_stream_cfg_on[OF valid', unfolded cfg'_def] by (auto simp: stream.pred_set)
     apply measurable
  subgoal premises prems for ys xs
    apply safe
      apply measurable
    unfolding \<phi>'_def \<psi>'_def absp_def
     apply (subst region_compatible_suntil[symmetric])
    subgoal
    proof -
      from prems have "pred_stream (\<lambda>s. s \<in> S) xs" using \<S>_abss_S by (auto simp: stream.pred_set)
      with equiv_\<phi> show ?thesis by (simp add: cfg'_def)
    qed
    subgoal
    proof -
      from prems have "pred_stream (\<lambda>s. s \<in> S) xs" using \<S>_abss_S by (auto simp: stream.pred_set)
      with equiv_\<psi> show ?thesis by (simp add: cfg'_def)
    qed
    using valid prems
     apply (auto simp: s comp_def \<phi>'_def \<psi>'_def absp_def dest: R_G.valid_cfg_state_in_S)
    apply (auto simp: stream.pred_set intro: \<S>_abss_S dest: R_G.valid_cfg_state_in_S)
    done
  subgoal premises prems for ys xs
    apply safe
      using prems apply (auto simp: stream.pred_set \<S>_abss_S; measurable; fail)
    using prems unfolding \<phi>'_def \<psi>'_def absp_def comp_def apply (simp add: stream.map_comp)
     apply (subst (asm) region_compatible_suntil[symmetric])
    subgoal
    proof -
      from prems have "pred_stream (\<lambda>s. s \<in> S) xs" using \<S>_abss_S by auto
      with equiv_\<phi> show ?thesis using valid by (simp add: cfg'_def repc_def)
    qed
    subgoal
    proof -
      from prems have "pred_stream (\<lambda>s. s \<in> S) xs" using \<S>_abss_S by auto
      with equiv_\<psi> show ?thesis using valid  by (simp add: cfg'_def)
    qed
    using valid prems by (auto simp: s S_abss_\<S> stream.pred_set dest: R_G.valid_cfg_state_in_S)
  done

end (* Probabilistic Timed Automaton Regions *)

end (* Theory *)
