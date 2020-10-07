(* Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Matrices for given marginals\<close>

text \<open>This theory derives from the finite max-flow min-cut theorem the existence of
matrices with given marginals based on a proof by Georg Kellerer
(Funktionen auf Produkträumen mit vorgegebenen Marginal-Funktionen).\<close>

theory Matrix_For_Marginals
  imports MFMC_Misc "HOL-Library.Diagonal_Subsequence" MFMC_Finite
begin

lemma bounded_matrix_for_marginals_finite:
  fixes f g :: "nat \<Rightarrow> real"
    and n :: nat
    and R :: "(nat \<times> nat) set"
  assumes eq_sum: "sum f {..n} = sum g {..n}"
    and le: "\<And>X. X \<subseteq> {..n} \<Longrightarrow> sum f X \<le> sum g (R `` X)"
    and f_nonneg: "\<And>x. 0 \<le> f x"
    and g_nonneg: "\<And>y. 0 \<le> g y"
    and R: "R \<subseteq> {..n} \<times> {..n}"
  obtains h :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "\<And>x y. \<lbrakk> x \<le> n; y \<le> n \<rbrakk> \<Longrightarrow> 0 \<le> h x y"
    and "\<And>x y. \<lbrakk> 0 < h x y; x \<le> n; y \<le> n \<rbrakk> \<Longrightarrow> (x, y) \<in> R"
    and "\<And>x. x \<le> n \<Longrightarrow> f x = sum (h x) {..n}"
    and "\<And>y. y \<le> n \<Longrightarrow> g y = sum (\<lambda>x. h x y) {..n}"
proof(cases "\<exists>x\<le>n. f x > 0")
  case False
  hence f: "f x = 0" if "x \<le> n" for x using f_nonneg[of x] that by(auto simp add: not_less)
  hence "sum g {..n} = 0" using eq_sum by simp
  hence "g y = 0" if "y \<le> n" for y using g_nonneg that by(simp add: sum_nonneg_eq_0_iff)
  with f show thesis by(auto intro!: that[of "\<lambda>_ _. 0"])
next
  case True
  then obtain x0 where x0: "x0 \<le> n" "f x0 > 0" by blast

  define R' where "R' = R \<inter> {x. f x > 0} \<times> {y. g y > 0}"

  have [simp]: "finite (R `` A)" for A
  proof -
    have "R `` A \<subseteq> {..n}" using R by auto
    thus ?thesis by(rule finite_subset) auto
  qed

  have R': "R' \<subseteq> {..n} \<times> {..n}" using R by(auto simp add: R'_def)
  have R'': "R' `` A \<subseteq> {..n}" for A using R by(auto simp add: R'_def)
  have [simp]: "finite (R' `` A)" for A using R''[of A]
    by(rule finite_subset) auto

  have hop: "\<exists>y0\<le>n. (x0, y0) \<in> R \<and> g y0 > 0" if x0: "x0 \<le> n" "f x0 > 0" for x0
  proof(rule ccontr)
    assume "\<not> ?thesis"
    then have "g y0 = 0" if "(x0, y0) \<in> R" "y0 \<le> n" for y0 using g_nonneg[of y0] that by auto
    moreover from R have "R `` {x0} \<subseteq> {..n}" by auto
    ultimately have "sum g (R `` {x0}) = 0" 
      using g_nonneg by(auto intro!: sum_nonneg_eq_0_iff[THEN iffD2])
    moreover have "{x0} \<subseteq> {..n}" using x0 by auto
    from le[OF this] x0 have "R `` {x0} \<noteq> {}" "sum g (R `` {x0}) > 0" by auto
    ultimately show False by simp
  qed
  then obtain y0 where y0: "y0 \<le> n" "(x0, y0) \<in> R'" "g y0 > 0" using x0 by(auto simp add: R'_def)

  define LARGE where "LARGE = sum f {..n} + 1"
  have "1 \<le> LARGE" using f_nonneg by(simp add: LARGE_def sum_nonneg)
  hence [simp]: "LARGE \<noteq> 0" "0 \<noteq> LARGE" "0 < LARGE" "0 \<le> LARGE" by simp_all

  define s where "s = 2 * n + 2"
  define t where "t = 2 * n + 3"
  define c where "c = (\<lambda>(x, y).
     if x = s \<and> y \<le> n then f y
     else if x \<le> n \<and> n < y \<and> y \<le> 2 * n + 1 \<and> (x, y - n - 1) \<in> R' then LARGE
     else if n < x \<and> x \<le> 2 * n + 1 \<and> y = t then g (x - n - 1)
     else 0)"

  have st [simp]: "\<not> s \<le> n" "\<not> s \<le> Suc (2 * n)" "s \<noteq> t" "t \<noteq> s" "\<not> t \<le> n" "\<not> t \<le> Suc (2 * n)"
    by(simp_all add: s_def t_def)

  have c_simps: "c (x, y) = 
    (if x = s \<and> y \<le> n then f y
     else if x \<le> n \<and> n < y \<and> y \<le> 2 * n + 1 \<and> (x, y - n - 1) \<in> R' then LARGE
     else if n < x \<and> x \<le> 2 * n + 1 \<and> y = t then g (x - n - 1)
     else 0)"
    for x y by(simp add: c_def)
  have cs [simp]: "c (s, y) = (if y \<le> n then f y else 0)"
    and ct [simp]: "c (x, t) = (if n < x \<and> x \<le> 2 * n + 1 then g (x - n - 1) else 0)"
    for x y by(auto simp add: c_simps)

  interpret Graph c .
  note [simp del] = zero_cap_simp

  interpret Network c s t
  proof
    have "(s, x0) \<in> E" using x0 by(simp add: E_def)
    thus "s \<in> V" by(auto simp add: V_def)
    
    have "(y0 + n + 1, t) \<in> E" using y0 by(simp add: E_def)
    thus "t \<in> V" by(auto simp add: V_def)

    show "s \<noteq> t" by simp
    show "\<forall>u v. 0 \<le> c (u, v)" by(simp add: c_simps f_nonneg g_nonneg max_def)
    show "\<forall>u. (u, s) \<notin> E" by(simp add: E_def c_simps)
    show "\<forall>u. (t, u) \<notin> E" by(simp add: E_def c_simps)
    show "\<forall>u v. (u, v) \<in> E \<longrightarrow> (v, u) \<notin> E" by(simp add: E_def c_simps)

    have "isPath s [(s, x0), (x0, y0 + n + 1), (y0 + n + 1, t)] t" 
      using x0 y0 by(auto simp add: E_def c_simps)
    hence st: "connected s t" by(auto simp add: connected_def simp del: isPath.simps)

    show "\<forall>v\<in>V. connected s v \<and> connected v t"
    proof(intro strip)
      fix v
      assume v: "v \<in> V"
      hence "v \<le> 2 * n + 3" by(auto simp add: V_def E_def c_simps t_def s_def split: if_split_asm)
      then consider (left) "v \<le> n" | (right) "n < v" "v \<le> 2 * n + 1" | (s) "v = s" | (t) "v = t"
        by(fastforce simp add: s_def t_def)
      then show "connected s v \<and> connected v t"
      proof cases
        case left
        have sv: "(s, v) \<in> E" using v left
          by(fastforce simp add: E_def V_def c_simps max_def R'_def split: if_split_asm)
        hence "connected s v" by(auto simp add: connected_def intro!: exI[where x="[(s, v)]"])
        moreover from sv left f_nonneg[of v] have "f v > 0" by(simp add: E_def)
        from hop[OF left this] obtain v' where "(v, v') \<in> R" "v' \<le> n" "g v' > 0" by auto
        hence "isPath v [(v, v' + n + 1), (v' + n + 1, t)] t" using left \<open>f v > 0\<close>
          by(auto simp add: E_def c_simps R'_def)
        hence "connected v t" by(auto simp add: connected_def simp del: isPath.simps)
        ultimately show ?thesis ..
      next
        case right
        hence vt: "(v, t) \<in> E" using v by(auto simp add: V_def E_def c_simps max_def R'_def split: if_split_asm)
        hence "connected v t" by(auto simp add: connected_def intro!: exI[where x="[(v, t)]"])
        moreover
        have *: "g (v - n - 1) > 0" using vt g_nonneg[of "v - n - 1"] right by(simp add: E_def )
        have "\<exists>v'\<le>n. (v', v - n - 1) \<in> R \<and> f v' > 0"
        proof(rule ccontr)
          assume "\<not> ?thesis"
          hence zero: "\<lbrakk> v' \<le> n; (v', v - n - 1) \<in> R \<rbrakk> \<Longrightarrow> f v' = 0" for v' using f_nonneg[of v'] by auto
          have "sum f {..n} = sum f {x. x \<le> n \<and> x \<notin> R^-1 `` {v - n - 1}}"
            by(rule sum.mono_neutral_cong_right)(auto dest: zero)
          also have "\<dots> \<le> sum g (R `` {x. x \<le> n \<and> x \<notin> R^-1 `` {v - n - 1}})" by(rule le) auto
          also have "\<dots> \<le> sum g ({..n} - {v - n - 1})"
            by(rule sum_mono2)(use R in \<open>auto simp add: g_nonneg\<close>)
          also have "\<dots> = sum g {..n} - g (v - n - 1)" using right by(subst sum_diff) auto
          also have "\<dots> < sum g {..n}" using * by simp
          also have "\<dots> = sum f {..n}" by(simp add: eq_sum)
          finally show False by simp
        qed
        then obtain v' where "v' \<le> n" "(v', v - n - 1) \<in> R" "f v' > 0" by auto
        with right * have "isPath s [(s, v'), (v', v)] v" by(auto simp add: E_def c_simps R'_def)
        hence "connected s v" by(auto simp add: connected_def simp del: isPath.simps)
        ultimately show ?thesis by blast
      qed(simp_all add: st)
    qed

    have "reachableNodes s \<subseteq> V" using \<open>s \<in> V\<close> by(rule reachable_ss_V)
    also have "V \<subseteq> {..2 * n + 3}"
      by(clarsimp simp add: V_def E_def)(simp_all add: c_simps s_def t_def split: if_split_asm)
    finally show "finite (reachableNodes s)" by(rule finite_subset) simp
  qed

  interpret h: NFlow c s t max_flow by(rule max_flow)
  let ?h = "\<lambda>x y. max_flow (x, y + n + 1)"
  from max_flow(2)[THEN h.fofu_II_III] obtain C where C: "NCut c s t C" 
    and eq: "h.val = NCut.cap c C" by blast
  interpret C: NCut c s t C using C .

  have "sum c (outgoing s) = sum (\<lambda>(_, x). f x) (Pair s ` {..n})"
    by(rule sum.mono_neutral_cong_left)(auto simp add: outgoing_def E_def)
  also have "\<dots> = sum f {..n}" by(subst sum.reindex)(auto simp add: inj_on_def)
  finally have out: "sum c (outgoing s) = sum f {..n}" .

  have no_leaving: "(\<lambda>y. y + n + 1) ` (R' `` (C \<inter> {..n})) \<subseteq> C"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    then obtain x y where *: "(x, y) \<in> R'" "x \<le> n" "x \<in> C" "y + n + 1 \<notin> C" by auto
    then have xy: "(x, y + n + 1) \<in> E" "y \<le> n" "c (x, y + n + 1) = LARGE"
      using R by(auto simp add: E_def c_simps R'_def)

    have "h.val \<le> sum f {..n}" using h.val_bounded(2) out by simp
    also have "\<dots> < sum c {(x, y + n + 1)}" using xy * by(simp add: LARGE_def)
    also have "\<dots> \<le> C.cap" using * xy unfolding C.cap_def
      by(intro sum_mono2[OF finite_outgoing'])(auto simp add: outgoing'_def cap_non_negative)
    also have "\<dots> = h.val" by(simp add: eq)
    finally show False by simp
  qed

  have "C.cap \<le> sum f {..n}" using out h.val_bounded(2) eq by simp
  then have cap: "C.cap = sum f {..n}"
  proof(rule antisym)
    let ?L = "{x. x \<le> n \<and> x \<in> C \<and> f x > 0}"
    let ?R = "(\<lambda>y. y + n + 1) ` (R' `` ?L)"
    have "sum f {..n} = sum f ?L + sum f ({..n} - ?L)" by(subst sum_diff) auto
    also have "sum f ?L \<le> sum g (R `` ?L)" by(rule le) auto
    also have "\<dots> = sum g (R' `` ?L)" using g_nonneg
      by(intro sum.mono_neutral_cong_right)(auto 4 3 simp add: R'_def Image_iff intro: antisym)
    also have "\<dots> = sum c ((\<lambda>y. (y + n + 1, t)) ` (R' `` ?L))" using R
      by(subst sum.reindex)(auto intro!: sum.cong simp add: inj_on_def R'_def)
    also have "sum f ({..n} - ?L) = sum c (Pair s ` ({..n} - ?L))" by(simp add: sum.reindex inj_on_def)
    also have "sum c ((\<lambda>y. (y + n + 1, t)) ` (R' `` ?L)) + \<dots> = 
      sum c (((\<lambda>y. (y + n + 1, t)) ` (R' `` ?L)) \<union> (Pair s ` ({..n} - ?L)))"
      by(subst sum.union_disjoint) auto
    also have "\<dots> \<le> sum c (((\<lambda>y. (y + n + 1, t)) ` (R' `` ?L)) \<union> (Pair s ` ({..n} - ?L)) \<union> {(x, t) | x. x \<in> C \<and> n < x \<and> x \<le> 2 * n + 1})"
      by(rule sum_mono2)(auto simp add: g_nonneg)
    also have "(((\<lambda>y. (y + n + 1, t)) ` (R' `` ?L)) \<union> (Pair s ` ({..n} - ?L)) \<union> {(x, t) | x. x \<in> C \<and> n < x \<and> x \<le> 2 * n + 1}) = (Pair s ` ({..n} - ?L)) \<union>  {(x, t) | x. x \<in> C \<and> n < x \<and> x \<le> 2 * n + 1}"
      using no_leaving R' by(fastforce simp add: Image_iff intro: rev_image_eqI)
    also have "sum c \<dots> = sum c (outgoing' C)" using C.s_in_cut C.t_ni_cut f_nonneg no_leaving
      apply(intro sum.mono_neutral_cong_right)
      apply(auto simp add: outgoing'_def E_def intro: le_neq_trans)
      apply(fastforce simp add: c_simps Image_iff intro: rev_image_eqI split: if_split_asm)+
      done
    also have "\<dots> = C.cap" by(simp add: C.cap_def)
    finally show "sum f {..n} \<le> \<dots>" by simp
  qed

  show thesis
  proof
    show "0 \<le> ?h x y" for x y by(rule h.f_non_negative)
    show "(x, y) \<in> R" if "0 < ?h x y" "x \<le> n" "y \<le> n" for x y
      using h.capacity_const[rule_format, of "(x, y + n + 1)"] that
      by(simp add: c_simps R'_def split: if_split_asm)

    have sum_h: "sum (?h x) {..n} = max_flow (s, x)" if "x \<le> n" for x
    proof -
      have "sum (?h x) {..n} = sum max_flow (Pair x ` ((+) (n + 1)) ` {..n})"
        by(simp add: sum.reindex add.commute inj_on_def)
      also have "\<dots> = sum max_flow (outgoing x)" using that
        apply(intro sum.mono_neutral_cong_right)
        apply(auto simp add: outgoing_def E_def)
        subgoal for y by(auto 4 3 simp add: c_simps max_def split: if_split_asm intro: rev_image_eqI[where x="y - n - 1"])
        done
      also have "\<dots> = sum max_flow (incoming x)" using that by(subst h.conservation) auto
      also have "\<dots> = sum max_flow {(s, x)}" using that
        by(intro sum.mono_neutral_cong_left; auto simp add: incoming_def E_def; simp add: c_simps split: if_split_asm)
      finally show ?thesis by simp
    qed
    hence le: "sum (?h x) {..n} \<le> f x" if "x \<le> n" for x
      using sum_h[OF that] h.capacity_const[rule_format, of "(s, x)"] that by simp
    moreover have "f x \<le> sum (?h x) {..n}" if "x \<le> n" for x
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "sum (?h x) {..n} < f x" by simp
      hence "sum (\<lambda>x. (sum (?h x) {..n})) {..n} < sum f {..n}"
        using le that by(intro sum_strict_mono_ex1) auto
      also have "sum (\<lambda>x. (sum (?h x) {..n})) {..n} = sum max_flow (Pair s ` {..n})"
        using sum_h by(simp add: sum.reindex inj_on_def)
      also have "\<dots> = sum max_flow (outgoing s)"
        by(rule sum.mono_neutral_right)(auto simp add: outgoing_def E_def)
      also have "\<dots> = sum f {..n}" using eq cap by(simp add: h.val_alt)
      finally show False by simp
    qed
    ultimately show "f x = sum (?h x) {..n}" if "x \<le> n" for x using that by(auto intro: antisym)

    have sum_h': "sum (\<lambda>x. ?h x y) {..n} = max_flow (y + n + 1, t)" if "y \<le> n" for y
    proof -
      have "sum (\<lambda>x. ?h x y) {..n} = sum max_flow ((\<lambda>x. (x, y + n + 1)) ` {..n})" 
        by(simp add: sum.reindex inj_on_def)
      also have "\<dots> = sum max_flow (incoming (y + n + 1))" using that
        apply(intro sum.mono_neutral_cong_right)
        apply(auto simp add: incoming_def E_def)
        apply(auto simp add: c_simps t_def split: if_split_asm)
        done
      also have "\<dots> = sum max_flow (outgoing (y + n + 1))"
        using that by(subst h.conservation)(auto simp add: s_def t_def)
      also have "\<dots> = sum max_flow {(y + n + 1, t)}" using that
        by(intro sum.mono_neutral_cong_left; auto simp add: outgoing_def E_def; simp add: s_def c_simps split: if_split_asm)
      finally show ?thesis by simp
    qed
    hence le': "sum (\<lambda>x. ?h x y) {..n} \<le> g y" if "y \<le> n" for y
      using sum_h'[OF that] h.capacity_const[rule_format, of "(y + n + 1, t)"] that by simp
    moreover have "g y \<le> sum (\<lambda>x. ?h x y) {..n}" if "y \<le> n" for y
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "sum (\<lambda>x. ?h x y) {..n} < g y" by simp
      hence "sum (\<lambda>y. (sum (\<lambda>x. ?h x y) {..n})) {..n} < sum g {..n}"
        using le' that by(intro sum_strict_mono_ex1) auto
      also have "sum (\<lambda>y. (sum (\<lambda>x. ?h x y) {..n})) {..n} = sum max_flow ((\<lambda>y. (y + n + 1, t)) ` {..n})"
        using sum_h' by(simp add: sum.reindex inj_on_def)
      also have "\<dots> = sum max_flow (incoming t)"
        apply(rule sum.mono_neutral_right)
        apply simp
        apply(auto simp add: incoming_def E_def cong: rev_conj_cong)
        subgoal for u by(auto intro: rev_image_eqI[where x="u - n - 1"])
        done
      also have "\<dots> = sum max_flow (outgoing s)" by(rule h.inflow_t_outflow_s)
      also have "\<dots> = sum f {..n}" using eq cap by(simp add: h.val_alt)
      finally show False using eq_sum by simp
    qed
    ultimately show "g y = sum (\<lambda>x. ?h x y) {..n}" if "y \<le> n" for y using that by(auto intro: antisym)
  qed
qed

lemma convergent_bounded_family_nat:
  fixes f :: "nat \<Rightarrow> nat \<Rightarrow> real"
  assumes bounded: "\<And>x. bounded (range (\<lambda>n. f n x))"
  obtains k where "strict_mono k" "\<And>x. convergent (\<lambda>n. f (k n) x)"
proof -
  interpret subseqs "\<lambda>x k. convergent (\<lambda>n. f (k n) x)"
  proof(unfold_locales)
    fix x and s :: "nat \<Rightarrow> nat"
    have "bounded (range (\<lambda>n. f (s n) x))" using bounded by(rule bounded_subset) auto
    from bounded_imp_convergent_subsequence[OF this]
    show "\<exists>r. strict_mono r \<and> convergent (\<lambda>n. f ((s \<circ> r) n) x)"
      by(auto simp add: o_def convergent_def)
  qed
  { fix k
    have "convergent (\<lambda>n. f ((diagseq \<circ> (+) (Suc k)) n) k)"
      by(rule diagseq_holds)(auto dest: convergent_subseq_convergent simp add: o_def)
    hence "convergent (\<lambda>n. f (diagseq n) k)" unfolding o_def
      by(subst (asm) add.commute)(simp only: convergent_ignore_initial_segment[where f="\<lambda>x. f (diagseq x) k"])
  } with subseq_diagseq show ?thesis ..
qed

lemma convergent_bounded_family:
  fixes f :: "nat \<Rightarrow> 'a \<Rightarrow> real"
  assumes bounded: "\<And>x. x \<in> A \<Longrightarrow> bounded (range (\<lambda>n. f n x))"
  and A: "countable A"
  obtains k where "strict_mono k" "\<And>x. x \<in> A \<Longrightarrow> convergent (\<lambda>n. f (k n) x)"
proof(cases "A = {}")
  case False
  define f' where "f' n x = f n (from_nat_into A x)" for n x
  have "bounded (range (\<lambda>n. f' n x))" for x
    unfolding f'_def using from_nat_into[OF False] by(rule bounded)
  then obtain k where k: "strict_mono k" 
    and conv: "convergent (\<lambda>n. f' (k n) x)" for x
    by(rule convergent_bounded_family_nat) iprover
  have "convergent (\<lambda>n. f (k n) x)" if "x \<in> A" for x
    using conv[of "to_nat_on A x"] A that by(simp add: f'_def)
  with k show thesis ..
next
  case True
  with strict_mono_id show thesis by(blast intro!: that)
qed

abbreviation zero_on :: "('a \<Rightarrow> 'b :: zero) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
where "zero_on f \<equiv> override_on f (\<lambda>_. 0)"

lemma zero_on_le [simp]: fixes f :: "'a \<Rightarrow> 'b :: {preorder, zero}" shows
  "zero_on f X x \<le> f x \<longleftrightarrow> (x \<in> X \<longrightarrow> 0 \<le> f x)"
by(auto simp add: override_on_def)

lemma zero_on_nonneg: fixes f :: "'a \<Rightarrow> 'b :: {preorder, zero}" shows
  "0 \<le> zero_on f X x \<longleftrightarrow> (x \<notin> X \<longrightarrow> 0 \<le> f x)"
by(auto simp add: override_on_def)

lemma sums_zero_on:
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes f: "f sums s"
    and X: "finite X"
  shows "zero_on f X sums (s - sum f X)"
proof -
  have "(\<lambda>x. if x \<in> X then f x else 0) sums sum (\<lambda>x. f x) X" using X by(rule sums_If_finite_set)
  from sums_diff[OF f this] show ?thesis
    by(simp add: sum_negf override_on_def if_distrib cong del: if_weak_cong)
qed

lemma 
  fixes f :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes f: "summable f"
  and X: "finite X"
  shows summable_zero_on [simp]: "summable (zero_on f X)" (is ?thesis1)
  and suminf_zero_on: "suminf (zero_on f X) = suminf f - sum f X" (is ?thesis2)
proof -
  from f obtain s where "f sums s" unfolding summable_def ..
  with sums_zero_on[OF this X] show ?thesis1 ?thesis2 
    by(auto simp add: summable_def sums_unique[symmetric])
qed

lemma summable_zero_on_nonneg:
  fixes f :: "nat \<Rightarrow> 'a :: {ordered_comm_monoid_add,linorder_topology,conditionally_complete_linorder}"
  assumes f: "summable f"
  and nonneg: "\<And>x. 0 \<le> f x"
  shows "summable (zero_on f X)"
proof(rule summableI_nonneg_bounded)
  fix n
  have "sum (zero_on f X) {..<n} \<le> sum f {..<n}" by(rule sum_mono)(simp add: nonneg)
  also have "\<dots> \<le> suminf f" using f by(rule sum_le_suminf)(auto simp add: nonneg)
  finally show "sum (zero_on f X) {..<n} \<le> suminf f" .
qed(simp add: zero_on_nonneg nonneg)

lemma zero_on_ennreal [simp]: "zero_on (\<lambda>x. ennreal (f x)) A = (\<lambda>x. ennreal (zero_on f A x))"
by(simp add: override_on_def fun_eq_iff)
 
lemma sum_lessThan_conv_atMost_nat:
  fixes f :: "nat \<Rightarrow> 'b :: ab_group_add"
  shows "sum f {..<n} = sum f {..n} - f n"
by (metis Groups.add_ac(2) add_diff_cancel_left' lessThan_Suc_atMost sum.lessThan_Suc)

lemma Collect_disjoint_atLeast:
  "Collect P \<inter> {x..} = {} \<longleftrightarrow> (\<forall>y\<ge>x. \<not> P y)"
by(auto simp add: atLeast_def)

lemma bounded_matrix_for_marginals_nat:
  fixes f g :: "nat \<Rightarrow> real"
    and R :: "(nat \<times> nat) set"
    and s :: real
  assumes sum_f: "f sums s" and sum_g: "g sums s"
    and f_nonneg: "\<And>x. 0 \<le> f x" and g_nonneg: "\<And>y. 0 \<le> g y"
    and f_le_g: "\<And>X. suminf (zero_on f (- X)) \<le> suminf (zero_on g (- R `` X))"
  obtains h :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "\<And>x y. 0 \<le> h x y"
    and "\<And>x y. 0 < h x y \<Longrightarrow> (x, y) \<in> R"
    and "\<And>x. h x sums f x"
    and "\<And>y. (\<lambda>x. h x y) sums g y"
proof -
  have summ_f: "summable f" and summ_g: "summable g" and sum_fg: "suminf f = suminf g"
    using sum_f sum_g by(auto simp add: summable_def sums_unique[symmetric])

  have summ_zf: "summable (zero_on f A)" for A
    using summ_f f_nonneg by(rule summable_zero_on_nonneg)
  have summ_zg: "summable (zero_on g A)" for A
    using summ_g g_nonneg by(rule summable_zero_on_nonneg)

  define f' :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "f' n x = (if x \<le> n then f x else if x = Suc n then \<Sum> k. f (k + (n + 1)) else 0)" for n x
  define g' :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "g' n y = (if y \<le> n then g y else if y = Suc n then \<Sum> k. g (k + (n + 1)) else 0)" for n y
  define R' :: "nat \<Rightarrow> (nat \<times> nat) set"
    where "R' n = 
      R \<inter> {..n} \<times> {..n} \<union> 
      {(n + 1, y) | y. \<exists>x'>n. (x', y) \<in> R \<and> y \<le> n} \<union>
      {(x, n + 1) | x. \<exists>y'>n. (x, y') \<in> R \<and> x \<le> n} \<union>
      (if \<exists>x>n. \<exists>y>n. (x, y) \<in> R then {(n + 1, n + 1)} else {})"
    for n
  have R'_simps [simplified, simp]:
    "\<lbrakk> x \<le> n; y \<le> n \<rbrakk> \<Longrightarrow> (x, y) \<in> R' n \<longleftrightarrow> (x, y) \<in> R"
    "y \<le> n \<Longrightarrow> (n + 1, y) \<in> R' n \<longleftrightarrow> (\<exists>x'>n. (x', y) \<in> R)"
    "x \<le> n \<Longrightarrow> (x, n + 1) \<in> R' n \<longleftrightarrow> (\<exists>y'>n. (x, y') \<in> R)"
    "(n + 1, n + 1) \<in> R' n \<longleftrightarrow> (\<exists>x'>n. \<exists>y'>n. (x', y') \<in> R)"
    "x > n + 1 \<or> y > n + 1 \<Longrightarrow> (x, y) \<notin> R' n"
    for x y n by(auto simp add: R'_def)

  have R'_cases: thesis if "(x, y) \<in> R' n"
    and "\<lbrakk> x \<le> n; y \<le> n; (x, y) \<in> R \<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x'. \<lbrakk> x = n + 1; y \<le> n; n < x'; (x', y) \<in> R \<rbrakk> \<Longrightarrow> thesis"
    and "\<And>y'. \<lbrakk> x \<le> n; y = n + 1; n < y'; (x, y') \<in> R \<rbrakk> \<Longrightarrow> thesis"
    and "\<And>x' y'. \<lbrakk> x = n + 1; y = n + 1; n < x'; n < y'; (x', y') \<in> R \<rbrakk> \<Longrightarrow> thesis"
    for thesis x y n using that by(auto simp add: R'_def split: if_split_asm)

  have R'_intros:
    "\<lbrakk> (x, y) \<in> R; x \<le> n; y \<le> n \<rbrakk> \<Longrightarrow> (x, y) \<in> R' n"
    "\<lbrakk> (x', y) \<in> R; n < x'; y \<le> n \<rbrakk> \<Longrightarrow> (n + 1, y) \<in> R' n"
    "\<lbrakk> (x, y') \<in> R; x \<le> n; n < y' \<rbrakk> \<Longrightarrow> (x, n + 1) \<in> R' n"
    "\<lbrakk> (x', y') \<in> R; n < x'; n < y' \<rbrakk> \<Longrightarrow> (n + 1, n + 1) \<in> R' n"
    for n x y x' y' by(auto)

  have Image_R':
    "R' n `` X = (R `` (X \<inter> {..n})) \<inter> {..n} \<union> 
    (if n + 1 \<in> X then (R `` {n+1..}) \<inter> {..n} else {}) \<union>
    (if (R `` (X \<inter> {..n})) \<inter> {n+1..} = {} then {} else {n + 1}) \<union>
    (if n + 1 \<in> X \<and> (R `` {n+1..}) \<inter> {n+1..} \<noteq> {} then {n + 1} else {})" for n X
    apply(simp add: Image_def)
    apply(safe elim!: R'_cases; auto simp add: Collect_disjoint_atLeast intro: R'_intros simp add: Suc_le_eq dest: Suc_le_lessD)
    apply(metis R'_simps(4) R'_intros(3) Suc_eq_plus1)+
    done

  { fix n
    have "sum (f' n) {..n + 1} = sum (g' n) {..n + 1}" using sum_fg
      unfolding f'_def g'_def suminf_minus_initial_segment[OF summ_f] suminf_minus_initial_segment[OF summ_g]
      by(simp)(metis (no_types, hide_lams) add.commute add.left_inverse atLeast0AtMost atLeast0LessThan atLeastLessThanSuc_atLeastAtMost minus_add_distrib sum.lessThan_Suc uminus_add_conv_diff)
    moreover have "sum (f' n) X \<le> sum (g' n) (R' n `` X)" if "X \<subseteq> {..n + 1}" for X
    proof -
      from that have [simp]: "finite X" by(rule finite_subset) simp
      define X' where "X' \<equiv> if n + 1 \<in> X then X \<union> {n+1..} else X"

      define Y' where "Y' \<equiv> if R `` X' \<inter> {n+1..} = {} then R `` X' else R `` X' \<union> {n+1..}"
        
      have "sum (f' n) X = sum (f' n) (X - {n + 1}) + (if n + 1 \<in> X then f' n (n + 1) else 0)"
        by(simp add: sum.remove)
      also have "sum (f' n) (X - {n + 1}) = sum f (X - {n + 1})" using that
        by(intro sum.cong)(auto simp add: f'_def)
      also have "\<dots> + (if n + 1 \<in> X then f' n (n + 1) else 0) = suminf (zero_on f (- X'))"
      proof(cases "n + 1 \<in> X")
        case True
        with sum_f that show ?thesis
          apply(simp add: summable_def X'_def f'_def suminf_zero_on[OF sums_summable] del: One_nat_def)
          apply(subst suminf_minus_initial_segment[OF summ_f])
          apply(simp add: algebra_simps)
          apply(subst sum.union_disjoint[symmetric])
          apply(auto simp add: sum_lessThan_conv_atMost_nat intro!: sum.cong)
          done
      next
        case False
        with sum_f show ?thesis
          by(simp add: X'_def suminf_finite[where N=X])
      qed
      also have "\<dots> \<le> suminf (zero_on g (- R `` X'))" by(rule f_le_g)
      also have "\<dots> \<le> suminf (zero_on g (- Y'))"
        by(rule suminf_le[OF _ summ_zg summ_zg])(clarsimp simp add: override_on_def g_nonneg Y'_def summ_zg)
      also have "\<dots> = suminf (\<lambda>k. zero_on g (- Y') (k + (n + 1))) + sum (zero_on g (- Y')) {..n}"
        by(subst suminf_split_initial_segment[OF summ_zg, of _ "n + 1"])(simp add: sum_lessThan_conv_atMost_nat)
      also have "sum (zero_on g (- Y')) {..n} = sum g (Y' \<inter> {..n})"
        by(rule sum.mono_neutral_cong_right)(auto simp add: override_on_def)
      also have "\<dots> = sum (g' n) (Y' \<inter> {..n})"
        by(rule sum.cong)(auto simp add: g'_def)
      also have "suminf (\<lambda>k. zero_on g (- Y') (k + (n + 1))) \<le> (if R `` X' \<inter> {n+1..} = {} then 0 else g' n (n + 1))"
        apply(clarsimp simp add: Y'_def g'_def simp del: One_nat_def)
        apply(subst suminf_eq_zero_iff[THEN iffD2])
        apply(auto simp del: One_nat_def simp add: summable_iff_shift summ_zg zero_on_nonneg g_nonneg)
        apply(auto simp add: override_on_def)
        done
      also have "\<dots> + sum (g' n) (Y' \<inter> {..n}) = sum (g' n) (R' n `` X)"
        using that by(fastforce simp add: Image_R' Y'_def X'_def atMost_Suc intro: sum.cong[OF _ refl])
      finally show ?thesis by simp
    qed
    moreover have "\<And>x. 0 \<le> f' n x" "\<And>y. 0 \<le> g' n y"
      by(auto simp add: f'_def g'_def f_nonneg g_nonneg summable_iff_shift summ_f summ_g intro!: suminf_nonneg simp del: One_nat_def)
    moreover have "R' n \<subseteq> {..n+1} \<times> {..n+1}"
      by(auto elim!: R'_cases)
    ultimately obtain h 
      where "\<And>x y. \<lbrakk> x \<le> n + 1; y \<le> n + 1\<rbrakk> \<Longrightarrow> 0 \<le> h x y"
      and "\<And>x y. \<lbrakk> 0 < h x y; x \<le> n + 1; y \<le> n + 1\<rbrakk> \<Longrightarrow> (x, y) \<in> R' n"
      and "\<And>x. x \<le> n + 1 \<Longrightarrow> f' n x = sum (h x) {..n + 1}"
      and "\<And>y. y \<le> n + 1 \<Longrightarrow> g' n y = sum (\<lambda>x. h x y) {..n + 1}"
      by(rule bounded_matrix_for_marginals_finite) blast+
    hence "\<exists>h. (\<forall>x y. x \<le> n + 1 \<longrightarrow> y \<le> n + 1 \<longrightarrow> 0 \<le> h x y) \<and>
       (\<forall>x y. 0 < h x y \<longrightarrow> x \<le> n + 1 \<longrightarrow> y \<le> n + 1 \<longrightarrow> (x, y) \<in> R' n) \<and>
       (\<forall>x. x \<le> n + 1 \<longrightarrow> f' n x = sum (h x) {..n + 1}) \<and>
       (\<forall>y. y \<le> n + 1 \<longrightarrow> g' n y = sum (\<lambda>x. h x y) {..n + 1})" by blast }
  hence "\<exists>h. \<forall>n. (\<forall>x y. x \<le> n + 1 \<longrightarrow> y \<le> n + 1 \<longrightarrow> 0 \<le> h n x y) \<and>
       (\<forall>x y. 0 < h n x y \<longrightarrow> x \<le> n + 1 \<longrightarrow> y \<le> n + 1 \<longrightarrow> (x, y) \<in> R' n) \<and>
       (\<forall>x. x \<le> n + 1 \<longrightarrow> f' n x = sum (h n x) {..n + 1}) \<and>
       (\<forall>y. y \<le> n + 1 \<longrightarrow> g' n y = sum (\<lambda>x. h n x y) {..n + 1})"
    by(subst choice_iff[symmetric]) blast
  then obtain h where h_nonneg: "\<And>n x y. \<lbrakk> x \<le> n + 1; y \<le> n + 1\<rbrakk> \<Longrightarrow> 0 \<le> h n x y"
    and h_R: "\<And>n x y. \<lbrakk> 0 < h n x y; x \<le> n + 1; y \<le> n + 1\<rbrakk> \<Longrightarrow> (x, y) \<in> R' n"
    and h_f: "\<And>n x. x \<le> n + 1 \<Longrightarrow> f' n x = sum (h n x) {..n + 1}"
    and h_g: "\<And>n y. y \<le> n + 1 \<Longrightarrow> g' n y = sum (\<lambda>x. h n x y) {..n + 1}"
    apply(rule exE)
    subgoal for h by(erule meta_allE[of _ h]) blast
    done
  
  define h' :: "nat \<Rightarrow> nat \<times> nat \<Rightarrow> real"
    where "h' n = (\<lambda>(x, y). if x \<le> n \<and> y \<le> n then h n x y else 0)" for n
  have h'_nonneg: "h' n xy \<ge> 0" for n xy by(simp add: h'_def h_nonneg split: prod.split)
  
  have "h' n xy \<le> s" for n xy
  proof(cases xy)
    case [simp]: (Pair x y)
    consider (le) "x \<le> n" "y \<le> n" | (beyond) "x > n \<or> y > n" by fastforce
    then show ?thesis
    proof cases
      case le
      have "h' n xy = h n x y" by(simp add: h'_def le)
      also have "\<dots> \<le> h n x y + sum (h n x) {..<y} + sum (h n x) {y<..n + 1}"
        using h_nonneg le by(auto intro!: sum_nonneg add_nonneg_nonneg)
      also have "\<dots> = sum (h n x) {..y} +  sum (h n x) {y<..n + 1}"
        by(simp add: sum_lessThan_conv_atMost_nat)
      also have "\<dots> = sum (h n x) {..n+1}" using le
        by(subst sum.union_disjoint[symmetric])(auto simp del: One_nat_def intro!: sum.cong)
      also have "\<dots> = f' n x" using le by(simp add: h_f)
      also have "\<dots> = f x" using le by(simp add: f'_def)
      also have "\<dots> = suminf (zero_on f (- {x}))"
        by(subst suminf_finite[where N="{x}"]) simp_all
      also have "\<dots> \<le> suminf f"
        by(rule suminf_le)(auto simp add: f_nonneg summ_zf summ_f)
      also have "\<dots> = s" using sum_f by(simp add: sums_unique[symmetric])
      finally show ?thesis .
    next
      case beyond
      then have "h' n xy = 0" by(auto simp add: h'_def)
      also have "0 \<le> s" using summ_f by(simp add: sums_unique[OF sum_f] suminf_nonneg f_nonneg)
      finally show ?thesis .
    qed
  qed
  then have "bounded (range (\<lambda>n. h' n x))" for x unfolding bounded_def
    by(intro exI[of _ 0] exI[of _ s]; simp add: h'_nonneg)
  from convergent_bounded_family[OF this, of UNIV "%x. x"] obtain k 
    where k: "strict_mono k" and conv: "\<And>xy. convergent (\<lambda>n. h' (k n) xy)" by auto

  define H :: "nat \<Rightarrow> nat \<Rightarrow> real"
    where "H x y = lim (\<lambda>n. h' (k n) (x, y))" for x y

  have H: "(\<lambda>n. h' (k n) (x, y)) \<longlonglongrightarrow> H x y" for x y
    unfolding H_def using conv[of "(x, y)"] by(simp add: convergent_LIMSEQ_iff)

  show thesis
  proof(rule that)
    show H_nonneg: "0 \<le> H x y" for x y using H[of x y] by(rule LIMSEQ_le_const)(simp add: h'_nonneg)
    show "(x, y) \<in> R" if "0 < H x y" for x y 
    proof(rule ccontr)
      assume "(x, y) \<notin> R"
      hence "h' n (x, y) = 0" for n using h_nonneg[of x n y] h_R[of n x y]
        by(fastforce simp add: h'_def)
      hence "H x y = 0" using H[of x y] by(simp add: LIMSEQ_const_iff)
      with that show False by simp
   qed
   show "H x sums f x" for x unfolding sums_iff
   proof
     have sum_H: "sum (H x) {..<m} \<le> f x" for m
     proof -
       have "sum (\<lambda>y. h' (k n) (x, y)) {..<m} \<le> f x" for n
       proof(cases "x \<le> k n")
         case True
         from k have "n \<le> k n" by(rule seq_suble)
         have "sum (\<lambda>y. h' (k n) (x, y)) {..<m} = sum (\<lambda>y. h' (k n) (x, y)) {..<min m (k n + 1)}"
           by(rule sum.mono_neutral_right)(auto simp add: h'_def min_def)
         also have "\<dots> \<le> sum (\<lambda>y. h (k n) x y) {..k n + 1}" using True
           by(intro sum_le_included[where i="id"])(auto simp add: h'_def h_nonneg)
         also have "\<dots> = f' (k n) x" using h_f True by simp
         also have "\<dots> = f x" using True by(simp add: f'_def)
         finally show ?thesis .
       qed(simp add: f_nonneg h'_def)
       then show ?thesis by -((rule LIMSEQ_le_const2 tendsto_sum H)+, simp)
     qed
     with H_nonneg show summ_H: "summable (H x)" by(rule summableI_nonneg_bounded)
     hence "suminf (H x) \<le> f x" using sum_H by(rule suminf_le_const)
     moreover
     have "(\<lambda>m. sum (H x) {..<m} + suminf (\<lambda>n. g (n + m))) \<longlonglongrightarrow> suminf (H x) + 0"
       by(rule tendsto_intros summable_LIMSEQ summ_H suminf_exist_split2 summ_g)+
     hence "f x \<le> suminf (H x) + 0"
     proof(rule LIMSEQ_le_const)
       have "f x \<le> sum (H x) {..<m} + suminf (\<lambda>n. g (n + m))" for m
       proof -
         have "(\<lambda>n. sum (\<lambda>y. h' (k n) (x, y)) {..<m} + suminf (\<lambda>i. g (i + m))) \<longlonglongrightarrow> sum (H x) {..<m} + suminf (\<lambda>i. g (i + m))"
           by(rule tendsto_intros H)+
         moreover have "\<exists>N. \<forall>n\<ge>N. f x \<le> sum (\<lambda>y. h' (k n) (x, y)) {..<m} + suminf (\<lambda>i. g (i + m))"
         proof(intro exI strip)
           fix n
           assume "max x m \<le> n"
           with seq_suble[OF k, of n] have x: "x \<le> k n" and m: "m \<le> k n" by auto
           have "f x = f' (k n) x" using x by(simp add: f'_def)
           also have "\<dots> = sum (h (k n) x) {..k n + 1}" using x by(simp add: h_f)
           also have "\<dots> = sum (h (k n) x) {..<m} + sum (h (k n) x) {m..k n + 1}"
             using x m by(subst sum.union_disjoint[symmetric])(auto intro!: sum.cong simp del: One_nat_def)
           also have "sum (h (k n) x) {..<m} = sum (\<lambda>y. h' (k n) (x, y)) {..<m}"
             using x m by(auto simp add: h'_def)
           also have "sum (h (k n) x) {m..k n + 1} = sum (\<lambda>y. sum (\<lambda>x. h (k n) x y) {x}) {m..k n + 1}" by simp
           also have "\<dots> \<le> sum (\<lambda>y. sum (\<lambda>x. h (k n) x y) {..k n + 1}) {m..k n + 1}" using x
             by(intro sum_mono sum_mono2)(auto simp add: h_nonneg)
           also have "\<dots> = sum (g' (k n)) {m..k n + 1}" by(simp add: h_g del: One_nat_def)
           also have "\<dots> = sum g {m..k n} + suminf (\<lambda>i. g (i + (k n + 1)))" using m by(simp add: g'_def)
           also have "\<dots> = suminf (\<lambda>i. g (i + m))" using m
             apply(subst (2) suminf_split_initial_segment[where k="k n + 1 - m"])
             apply(simp_all add: summable_iff_shift summ_g)
             apply(rule sum.reindex_cong[OF _ _ refl])
             apply(simp_all add: Suc_diff_le lessThan_Suc_atMost)
             apply(safe; clarsimp)
             subgoal for x by(rule image_eqI[where x="x - m"]) auto
             subgoal by auto 
             done
           finally show "f x \<le> sum (\<lambda>y. h' (k n) (x, y)) {..<m} + \<dots>" by simp
         qed
         ultimately show ?thesis by(rule LIMSEQ_le_const)
       qed
       thus "\<exists>N. \<forall>n\<ge>N. f x \<le> sum (H x) {..<n} + (\<Sum>i. g (i + n))" by auto
     qed
     ultimately show "suminf (H x) = f x" by simp
   qed
   show "(\<lambda>x. H x y) sums g y" for y unfolding sums_iff
   proof
     have sum_H: "sum (\<lambda>x. H x y) {..<m} \<le> g y" for m
     proof -
       have "sum (\<lambda>x. h' (k n) (x, y)) {..<m} \<le> g y" for n
       proof(cases "y \<le> k n")
         case True
         from k have "n \<le> k n" by(rule seq_suble)
         have "sum (\<lambda>x. h' (k n) (x, y)) {..<m} = sum (\<lambda>x. h' (k n) (x, y)) {..<min m (k n + 1)}"
           by(rule sum.mono_neutral_right)(auto simp add: h'_def min_def)
         also have "\<dots> \<le> sum (\<lambda>x. h (k n) x y) {..k n + 1}" using True
           by(intro sum_le_included[where i="id"])(auto simp add: h'_def h_nonneg)
         also have "\<dots> = g' (k n) y" using h_g True by simp
         also have "\<dots> = g y" using True by(simp add: g'_def)
         finally show ?thesis .
       qed(simp add: g_nonneg h'_def)
       then show ?thesis by -((rule LIMSEQ_le_const2 tendsto_sum H)+, simp)
     qed
     with H_nonneg show summ_H: "summable (\<lambda>x. H x  y)" by(rule summableI_nonneg_bounded)
     hence "suminf (\<lambda>x. H x y) \<le> g y" using sum_H by(rule suminf_le_const)
     moreover
     have "(\<lambda>m. sum (\<lambda>x. H x y) {..<m} + suminf (\<lambda>n. f (n + m))) \<longlonglongrightarrow> suminf (\<lambda>x. H x y) + 0"
       by(rule tendsto_intros summable_LIMSEQ summ_H suminf_exist_split2 summ_f)+
     hence "g y \<le> suminf (\<lambda>x. H x y) + 0"
     proof(rule LIMSEQ_le_const)
       have "g y \<le> sum (\<lambda>x. H x y) {..<m} + suminf (\<lambda>n. f (n + m))" for m
       proof -
         have "(\<lambda>n. sum (\<lambda>x. h' (k n) (x, y)) {..<m} + suminf (\<lambda>i. f (i + m))) \<longlonglongrightarrow> sum (\<lambda>x. H x y) {..<m} + suminf (\<lambda>i. f (i + m))"
           by(rule tendsto_intros H)+
         moreover have "\<exists>N. \<forall>n\<ge>N. g y \<le> sum (\<lambda>x. h' (k n) (x, y)) {..<m} + suminf (\<lambda>i. f (i + m))"
         proof(intro exI strip)
           fix n
           assume "max y m \<le> n"
           with seq_suble[OF k, of n] have y: "y \<le> k n" and m: "m \<le> k n" by auto
           have "g y = g' (k n) y" using y by(simp add: g'_def)
           also have "\<dots> = sum (\<lambda>x. h (k n) x y) {..k n + 1}" using y by(simp add: h_g)
           also have "\<dots> = sum (\<lambda>x. h (k n) x y) {..<m} + sum (\<lambda>x. h (k n) x y) {m..k n + 1}"
             using y m by(subst sum.union_disjoint[symmetric])(auto intro!: sum.cong simp del: One_nat_def)
           also have "sum (\<lambda>x. h (k n) x y) {..<m} = sum (\<lambda>x. h' (k n) (x, y)) {..<m}"
             using y m by(auto simp add: h'_def)
           also have "sum (\<lambda>x. h (k n) x y) {m..k n + 1} = sum (\<lambda>x. sum (\<lambda>y. h (k n) x y) {y}) {m..k n + 1}" by simp
           also have "\<dots> \<le> sum (\<lambda>x. sum (\<lambda>y. h (k n) x y) {..k n + 1}) {m..k n + 1}" using y
             by(intro sum_mono sum_mono2)(auto simp add: h_nonneg)
           also have "\<dots> = sum (f' (k n)) {m..k n + 1}" by(simp add: h_f del: One_nat_def)
           also have "\<dots> = sum f {m..k n} + suminf (\<lambda>i. f (i + (k n + 1)))" using m by(simp add: f'_def)
           also have "\<dots> = suminf (\<lambda>i. f (i + m))" using m
             apply(subst (2) suminf_split_initial_segment[where k="k n + 1 - m"])
             apply(simp_all add: summable_iff_shift summ_f)
             apply(rule sum.reindex_cong[OF _ _ refl])
             apply(simp_all add: Suc_diff_le lessThan_Suc_atMost)
             apply(safe; clarsimp)
             subgoal for x by(rule image_eqI[where x="x - m"]) auto
             subgoal by auto 
             done
           finally show "g y \<le> sum (\<lambda>x. h' (k n) (x, y)) {..<m} + \<dots>" by simp
         qed
         ultimately show ?thesis by(rule LIMSEQ_le_const)
       qed
       thus "\<exists>N. \<forall>n\<ge>N. g y \<le> sum (\<lambda>x. H x y) {..<n} + (\<Sum>i. f (i + n))" by auto
     qed
     ultimately show "suminf (\<lambda>x. H x y) = g y" by simp
   qed
  qed
qed

lemma bounded_matrix_for_marginals_ennreal:
  assumes sum_eq: "(\<Sum>\<^sup>+ x\<in>A. f x) = (\<Sum>\<^sup>+ y\<in>B. g y)"
    and finite: "(\<Sum>\<^sup>+ x\<in>B. g x) \<noteq> \<top>"
    and le: "\<And>X. X \<subseteq> A \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>X. f x) \<le> (\<Sum>\<^sup>+ y\<in>R `` X. g y)"
    and countable [simp]: "countable A" "countable B"
    and R: "R \<subseteq> A \<times> B"
  obtains h where "\<And>x y. 0 < h x y \<Longrightarrow> (x, y) \<in> R"
    and "\<And>x y. h x y \<noteq> \<top>"
    and "\<And>x. x \<in> A \<Longrightarrow> (\<Sum>\<^sup>+ y\<in>B. h x y) = f x"
    and "\<And>y. y \<in> B \<Longrightarrow> (\<Sum>\<^sup>+ x\<in>A. h x y) = g y"
proof -
  have fin_g [simp]: "g y \<noteq> \<top>" if "y \<in> B" for y using finite
    by(rule neq_top_trans)(rule nn_integral_ge_point[OF that])
  have fin_f [simp]: "f x \<noteq> \<top>" if "x \<in> A" for x using finite unfolding sum_eq[symmetric]
    by(rule neq_top_trans)(rule nn_integral_ge_point[OF that])

  define f' where "f' x = (if x \<in> to_nat_on A ` A then enn2real (f (from_nat_into A x)) else 0)" for x
  define g' where "g' y = (if y \<in> to_nat_on B ` B then enn2real (g (from_nat_into B y)) else 0)" for y
  define s where "s = enn2real (\<Sum>\<^sup>+ x\<in>B. g x)"
  define R' where "R' = map_prod (to_nat_on A) (to_nat_on B) ` R" 

  have f'_nonneg: "f' x \<ge> 0" for x by(simp add: f'_def)
  have g'_nonneg: "g' y \<ge> 0" for y by(simp add: g'_def)

  have "(\<Sum>\<^sup>+ x. f' x) = (\<Sum>\<^sup>+ x\<in>to_nat_on A ` A. f' x)"
    by(auto simp add: nn_integral_count_space_indicator f'_def intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>A. f x)"
    by(subst nn_integral_count_space_reindex)(auto simp add: inj_on_to_nat_on f'_def ennreal_enn2real_if intro!: nn_integral_cong)
  finally have sum_f': "(\<Sum>\<^sup>+ x. f' x) = (\<Sum>\<^sup>+ x\<in>A. f x)" .

  have "(\<Sum>\<^sup>+ y. g' y) = (\<Sum>\<^sup>+ y\<in>to_nat_on B ` B. g' y)"
    by(auto simp add: nn_integral_count_space_indicator g'_def intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>B. g y)"
    by(subst nn_integral_count_space_reindex)(auto simp add: inj_on_to_nat_on g'_def ennreal_enn2real_if intro!: nn_integral_cong)
  finally have sum_g': "(\<Sum>\<^sup>+ y. g' y) = (\<Sum>\<^sup>+ y\<in>B. g y)" .

  have summ_f': "summable f'"
  proof(rule summableI_nonneg_bounded)
    show "sum f' {..<n} \<le> enn2real (\<Sum>\<^sup>+ x. f' x)" for n
    proof -
      have "sum f' {..<n} = enn2real (\<Sum>\<^sup>+ x\<in>{..<n}. f' x)" 
        by(simp add: nn_integral_count_space_finite f'_nonneg sum_nonneg)
      also have "enn2real (\<Sum>\<^sup>+ x\<in>{..<n}. f' x) \<le> enn2real (\<Sum>\<^sup>+ x. f' x)" using finite sum_eq[symmetric]
        by(auto simp add: nn_integral_count_space_indicator sum_f'[symmetric] less_top intro!: nn_integral_mono enn2real_mono split: split_indicator)
      finally show ?thesis .
    qed
  qed(rule f'_nonneg)
  have suminf_f': "suminf f' = enn2real (\<Sum>\<^sup>+ y. f' y)"
    by(simp add: nn_integral_count_space_nat suminf_ennreal2[OF f'_nonneg summ_f'] suminf_nonneg[OF summ_f'] f'_nonneg)
  with summ_f' sum_f' sum_eq have sums_f: "f' sums s" by(simp add: s_def sums_iff)
  moreover
  have summ_g': "summable g'"
  proof(rule summableI_nonneg_bounded)
    show "sum g' {..<n} \<le> enn2real (\<Sum>\<^sup>+ y. g' y)" for n
    proof -
      have "sum g' {..<n} = enn2real (\<Sum>\<^sup>+ y\<in>{..<n}. g' y)" 
        by(simp add: nn_integral_count_space_finite g'_nonneg sum_nonneg)
      also have "enn2real (\<Sum>\<^sup>+ y\<in>{..<n}. g' y) \<le> enn2real (\<Sum>\<^sup>+ y. g' y)" using finite
        by(auto simp add: nn_integral_count_space_indicator sum_g'[symmetric] less_top intro!: nn_integral_mono enn2real_mono split: split_indicator)
      finally show ?thesis .
    qed
  qed(rule g'_nonneg)
  have suminf_g': "suminf g' = enn2real (\<Sum>\<^sup>+ y. g' y)"
    by(simp add: nn_integral_count_space_nat suminf_ennreal2[OF g'_nonneg summ_g'] suminf_nonneg[OF summ_g'] g'_nonneg)
  with summ_g' sum_g' have sums_g: "g' sums s" by(simp add: s_def sums_iff)
  moreover note f'_nonneg g'_nonneg
  moreover have "suminf (zero_on f' (- X)) \<le> suminf (zero_on g' (- R' `` X))" for X
  proof -
    define X' where "X' = from_nat_into A ` (X \<inter> to_nat_on A ` A)"
    have X': "to_nat_on A ` X' = X \<inter> (to_nat_on A ` A)"
      by(auto 4 3 simp add: X'_def intro: rev_image_eqI)

    have "ennreal (suminf (zero_on f' (- X))) = suminf (zero_on (\<lambda>x. ennreal (f' x)) (- X))"
      by(simp add: suminf_ennreal2 zero_on_nonneg f'_nonneg summable_zero_on_nonneg summ_f')
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>X. f' x)"
      by(auto simp add: nn_integral_count_space_nat[symmetric] nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x\<in>to_nat_on A ` X'. f' x)" using X'
      by(auto simp add: nn_integral_count_space_indicator f'_def intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ x \<in> X'. f x)"
      by(subst nn_integral_count_space_reindex)(auto simp add: X'_def inj_on_def f'_def ennreal_enn2real_if intro!: nn_integral_cong)
    also have "\<dots> \<le> (\<Sum>\<^sup>+ y \<in> R `` X'. g y)" by(rule le)(auto simp add: X'_def)
    also have "\<dots> = (\<Sum>\<^sup>+ y \<in> to_nat_on B ` (R `` X'). g' y)" using R fin_g
      by(subst nn_integral_count_space_reindex)(auto 4 3 simp add: X'_def inj_on_def g'_def ennreal_enn2real_if simp del: fin_g intro!: nn_integral_cong from_nat_into dest: to_nat_on_inj[THEN iffD1, rotated -1])
    also have "to_nat_on B ` (R `` X') = R' `` X" using R 
      by(auto 4 4 simp add: X'_def R'_def Image_iff intro: rev_image_eqI rev_bexI intro!: imageI)
    also have "(\<Sum>\<^sup>+ y\<in>\<dots>. g' y) = suminf (zero_on (\<lambda>y. ennreal (g' y)) (- \<dots>))"
      by(auto simp add: nn_integral_count_space_nat[symmetric] nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
    also have "\<dots> = ennreal (suminf (zero_on g' (- R' `` X)))"
      by(simp add: suminf_ennreal2 zero_on_nonneg g'_nonneg summable_zero_on_nonneg summ_g')
    finally show ?thesis 
      by(simp add: suminf_nonneg summable_zero_on_nonneg[OF summ_g' g'_nonneg] zero_on_nonneg g'_nonneg)
  qed
  ultimately obtain h' where h'_nonneg: "\<And>x y. 0 \<le> h' x y"
    and dom_h': "\<And>x y. 0 < h' x y \<Longrightarrow> (x, y) \<in> R'"
    and h'_f: "\<And>x. h' x sums f' x"
    and h'_g: "\<And>y. (\<lambda>x. h' x y) sums g' y"
    by(rule bounded_matrix_for_marginals_nat) blast

  define h where "h x y = ennreal (if x \<in> A \<and> y \<in> B then h' (to_nat_on A x) (to_nat_on B y) else 0)" for x y
  show ?thesis
  proof
    show "(x, y) \<in> R" if "0 < h x y" for x y
      using that dom_h'[of "to_nat_on A x" "to_nat_on B y"] R 
      by(auto simp add: h_def R'_def dest: to_nat_on_inj[THEN iffD1, rotated -1] split: if_split_asm)
    show "h x y \<noteq> \<top>" for x y by(simp add: h_def)

    fix x
    assume x: "x \<in> A"
    have "(\<Sum>\<^sup>+ y\<in>B. h x y) = (\<Sum>\<^sup>+ y\<in>to_nat_on B ` B. h' (to_nat_on A x) y)"
      by(subst nn_integral_count_space_reindex)(auto simp add: inj_on_to_nat_on h_def x intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ y. h' (to_nat_on A x) y)" using dom_h'[of "to_nat_on A x"] h'_nonneg R
      by(fastforce intro!: nn_integral_cong intro: rev_image_eqI simp add: nn_integral_count_space_indicator R'_def less_le split: split_indicator)
    also have "\<dots> = ennreal (suminf (h' (to_nat_on A x)))" 
      by(simp add: nn_integral_count_space_nat suminf_ennreal_eq[OF _ h'_f] h'_nonneg) 
    also have "\<dots> = ennreal (f' (to_nat_on A x))" using h'_f[of "to_nat_on A x"] by(simp add: sums_iff)
    also have "\<dots> = f x" using x by(simp add: f'_def ennreal_enn2real_if)
    finally show "(\<Sum>\<^sup>+ y\<in>B. h x y) = f x" .
  next
    fix y
    assume y: "y \<in> B"
    have "(\<Sum>\<^sup>+ x\<in>A. h x y) = (\<Sum>\<^sup>+ x\<in>to_nat_on A ` A. h' x (to_nat_on B y))"
      by(subst nn_integral_count_space_reindex)(auto simp add: inj_on_to_nat_on h_def y intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ x. h' x (to_nat_on B y))" using dom_h'[of _ "to_nat_on B y"] h'_nonneg R
      by(fastforce intro!: nn_integral_cong intro: rev_image_eqI simp add: nn_integral_count_space_indicator R'_def less_le split: split_indicator)
    also have "\<dots> = ennreal (suminf (\<lambda>x. h' x (to_nat_on B y)))" 
      by(simp add: nn_integral_count_space_nat suminf_ennreal_eq[OF _ h'_g] h'_nonneg) 
    also have "\<dots> = ennreal (g' (to_nat_on B y))" using h'_g[of "to_nat_on B y"] by(simp add: sums_iff)
    also have "\<dots> = g y" using y by(simp add: g'_def ennreal_enn2real_if)
    finally show "(\<Sum>\<^sup>+ x\<in>A. h x y) = g y" .
  qed
qed

end
