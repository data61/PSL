(* Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Derangements\<close>

theory Derangements
imports
  Complex_Main
  "HOL-Library.Permutations"
begin

subsection \<open>Preliminaries\<close>

subsubsection \<open>Additions to @{theory HOL.Finite_Set} Theory\<close>

lemma card_product_dependent:
  assumes "finite S" "\<forall>x \<in> S. finite (T x)"
  shows "card {(x, y). x \<in> S \<and> y \<in> T x} = (\<Sum>x \<in> S. card (T x))"
using card_SigmaI[OF assms, symmetric] by (auto intro!: arg_cong[where f=card] simp add: Sigma_def)

subsubsection \<open>Additions to @{theory "HOL-Library.Permutations"} Theory\<close>

lemma permutes_imp_bij':
  assumes "p permutes S"
  shows "bij p"
using assms by (meson bij_def permutes_inj permutes_surj)

lemma permutesE:
  assumes "p permutes S"
  obtains "bij p" "\<forall>x. x \<notin> S \<longrightarrow> p x = x"
using assms by (simp add: permutes_def permutes_imp_bij')

lemma bij_imp_permutes':
  assumes "bij p" "\<forall>x. x \<notin> A \<longrightarrow> p x = x"
  shows  "p permutes A"
using assms bij_imp_permutes permutes_superset by force

lemma permutes_swap:
  assumes "p permutes S"
  shows "Fun.swap x y p permutes (insert x (insert y S))"
proof -
  from assms have "p permutes (insert x (insert y S))" by (meson permutes_subset subset_insertI)
  moreover have "Fun.swap x y id permutes (insert x (insert y S))" by (simp add: permutes_swap_id)
  ultimately show "Fun.swap x y p permutes (insert x (insert y S))"
    by (metis comp_id comp_swap permutes_compose)
qed

lemma bij_extends:
  "bij p \<Longrightarrow> p x = x \<Longrightarrow> bij (p(x := y, inv p y := x))"
unfolding bij_def
proof (rule conjI; erule conjE)
  assume a: "inj p" "p x = x"
  show "inj (p(x := y, inv p y := x))"
  proof (intro injI)
    fix z z'
    assume "(p(x := y, inv p y := x)) z = (p(x := y, inv p y := x)) z'"
    from this a show "z = z'"
      by (auto split: if_split_asm simp add: inv_f_eq inj_eq)
  qed
next
  assume a: "inj p" "surj p" "p x = x"
  {
    fix x'
    from a have "(p(x := y, inv p y := x)) (((inv p)(y := x, x := inv p y)) x') = x'"
      by (auto split: if_split_asm) (metis surj_f_inv_f)+
  }
  from this show "surj (p(x := y, inv p y := x))" by (metis surjI)
qed

lemma permutes_add_one:
  assumes "p permutes S" "x \<notin> S" "y \<in> S"
  shows "p(x := y, inv p y := x) permutes (insert x S)"
proof (rule bij_imp_permutes')
  from assms show "bij (p(x := y, inv p y := x))"
    by (meson bij_extends permutes_def permutes_imp_bij')
  from assms show "\<forall>z. z \<notin> insert x S \<longrightarrow> (p(x := y, inv p y := x)) z = z"
    by (metis fun_upd_apply insertCI permutes_def permutes_inverses(1))
qed

lemma permutations_skip_one:
  assumes "p permutes S" "x : S"
  shows "p(x := x, inv p x := p x) permutes (S - {x})"
proof (rule bij_imp_permutes')
  from assms show "\<forall>z. z \<notin> S - {x} \<longrightarrow> (p(x := x, inv p x := p x)) z = z"
    by (auto elim: permutesE simp add: bij_inv_eq_iff)
      (simp add: assms(1) permutes_in_image permutes_inv)
  from assms have "inj (p(x := x, inv p x := p x))"
    by (intro injI) (auto split: if_split_asm; metis permutes_inverses(2))+
  from assms this show "bij (p(x := x, inv p x := p x))"
    by (metis UNIV_I bij_betw_imageI bij_betw_swap_iff permutes_inj permutes_surj surj_f_inv_f swap_def)
qed

lemma permutes_drop_cycle_size_two:
  assumes "p permutes S" "p (p x) = x"
  shows "Fun.swap x (p x) p permutes (S - {x, p x})"
using assms by (auto intro!: bij_imp_permutes' elim!: permutesE) (metis swap_apply(1,3))

subsection \<open>Fixpoint-Free Permutations\<close>

definition derangements :: "nat set \<Rightarrow> (nat \<Rightarrow> nat) set"
where
  "derangements S = {p. p permutes S \<and> (\<forall>x \<in> S. p x \<noteq> x)}"

lemma derangementsI:
  assumes "p permutes S" "\<And>x. x \<in> S \<Longrightarrow> p x \<noteq> x"
  shows "p \<in> derangements S"
using assms unfolding derangements_def by auto

lemma derangementsE:
  assumes "d : derangements S"
  obtains "d permutes S" "\<forall>x\<in>S. d x \<noteq> x"
using assms unfolding derangements_def by auto

subsection \<open>Properties of Derangements\<close>

lemma derangements_inv:
  assumes d: "d \<in> derangements S"
  shows "inv d \<in> derangements S"
using assms
by (auto intro!: derangementsI elim!: derangementsE simp add: permutes_inv permutes_inv_eq)

lemma derangements_in_image:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<in> A"
using assms by (auto elim: derangementsE simp add: permutes_in_image)

lemma derangements_in_image_strong:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<in> A - {x}"
using assms by (auto elim: derangementsE simp add: permutes_in_image)

lemma derangements_inverse_in_image:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "inv d x \<in> A"
using assms by (auto intro: derangements_in_image derangements_inv)

lemma derangements_fixpoint:
  assumes "d \<in> derangements A" "x \<notin> A"
  shows "d x = x"
using assms by (auto elim!: derangementsE simp add: permutes_def)

lemma derangements_no_fixpoint:
  assumes "d \<in> derangements A" "x \<in> A"
  shows "d x \<noteq> x"
using assms by (auto elim: derangementsE)

lemma finite_derangements:
  assumes "finite A"
  shows "finite (derangements A)"
using assms unfolding derangements_def
by (auto simp add: finite_permutations)

subsection \<open>Construction of Derangements\<close>

lemma derangements_empty[simp]:
  "derangements {} = {id}"
unfolding derangements_def by auto

lemma derangements_singleton[simp]:
  "derangements {x} = {}"
unfolding derangements_def by auto

lemma derangements_swap:
  assumes "d \<in> derangements S" "x \<notin> S" "y \<notin> S" "x \<noteq> y"
  shows "Fun.swap x y d \<in> derangements (insert x (insert y S))"
proof (rule derangementsI)
  from assms show "Fun.swap x y d permutes (insert x (insert y S))"
    by (auto intro: permutes_swap elim: derangementsE)
  from assms have s: "d x = x" "d y = y"
    by (auto intro: derangements_fixpoint)
  {
    fix x'
    assume "x' : insert x (insert y S)"
    from s assms \<open>x \<noteq> y\<close> this show "Fun.swap x y d x' \<noteq> x'"
      by (cases "x' = x"; cases "x' = y") (auto dest: derangements_no_fixpoint)
  }
qed

lemma derangements_skip_one:
  assumes d: "d \<in> derangements S" and "x \<in> S" "d (d x) \<noteq> x"
  shows "d(x := x, inv d x := d x) \<in> derangements (S - {x})"
proof -
  from d have bij: "bij d"
    by (auto elim: derangementsE simp add: permutes_imp_bij')
  from d \<open>x : S\<close> have that: "d x : S - {x}"
    by (auto dest: derangements_in_image derangements_no_fixpoint)
  from d \<open>d (d x) \<noteq> x\<close> bij have "\<forall>x'\<in>S - {x}. (d(x := x, inv d x := d x)) x' \<noteq> x'"
    by (auto elim!: derangementsE simp add: bij_inv_eq_iff)
  from d \<open>x : S\<close> this show derangements: "d(x:=x, inv d x:= d x) : derangements (S - {x})"
    by (meson derangementsE derangementsI permutations_skip_one)
qed

lemma derangements_add_one:
  assumes "d \<in> derangements S" "x \<notin> S" "y \<in> S"
  shows "d(x := y, inv d y := x) \<in> derangements (insert x S)"
proof (rule derangementsI)
  from assms show "d(x := y, inv d y := x) permutes (insert x S)"
   by (auto intro: permutes_add_one elim: derangementsE)
next
  fix z
  assume "z : insert x S"
  from assms this derangements_inverse_in_image[OF assms(1), of y]
  show "(d(x := y, inv d y := x)) z \<noteq> z" by (auto elim: derangementsE)
qed

lemma derangements_drop_minimal_cycle:
  assumes "d \<in> derangements S" "d (d x) = x"
  shows "Fun.swap x (d x) d \<in> derangements (S - {x, d x})"
proof (rule derangementsI)
  from assms show "Fun.swap x (d x) d permutes (S - {x, d x})"
    by (meson derangementsE permutes_drop_cycle_size_two)
next
  fix y
  assume "y \<in> S - {x, d x}"
  from assms this show "Fun.swap x (d x) d y \<noteq> y"
    by (auto elim: derangementsE)
qed

subsection \<open>Cardinality of Derangements\<close>

subsubsection \<open>Recursive Characterization\<close>

fun count_derangements :: "nat \<Rightarrow> nat"
where
  "count_derangements 0 = 1"
| "count_derangements (Suc 0) = 0"
| "count_derangements (Suc (Suc n)) = (n + 1) * (count_derangements (Suc n) + count_derangements n)"

lemma card_derangements:
  assumes "finite S" "card S = n"
  shows "card (derangements S) = count_derangements n"
using assms
proof (induct n arbitrary: S rule: count_derangements.induct)
  case 1
  from this show ?case by auto
next
  case 2
  from this derangements_singleton finite_derangements show ?case
    using Finite_Set.card_0_eq card_eq_SucD count_derangements.simps(2) by fastforce
next
  case (3 n)
  from 3(4) obtain x where "x \<in> S" using card_eq_SucD insertI1 by auto
  let ?D1 = "(\<lambda>(y, d). Fun.swap x y d) ` {(y, d). y \<in> S & y \<noteq> x & d : derangements (S - {x, y})}"
  let ?D2 = "(\<lambda>(y, f). f(x:=y, inv f y := x)) ` ((S - {x}) \<times> derangements (S - {x}))"
  from \<open>x \<in> S\<close> have subset1: "?D1 \<subseteq> derangements S"
  proof (auto)
    fix y d
    assume "y \<in> S" "y \<noteq> x"
    assume d: "d \<in> derangements (S - {x, y})"
    from \<open>x : S\<close> \<open>y : S\<close> have S: "S = insert x (insert y (S - {x, y}))" by auto
    from d \<open>x : S\<close> \<open>y : S\<close> \<open>y \<noteq> x\<close> show "Fun.swap x y d \<in> derangements S"
      by (subst S) (auto intro!: derangements_swap)
  qed
  have subset2: "?D2 \<subseteq> derangements S"
  proof (rule subsetI, erule imageE, simp split: prod.split_asm, (erule conjE)+)
    fix d y
    assume "d : derangements (S - {x})" "y : S" "y \<noteq> x"
    from this have "d(x := y, inv d y := x) \<in> derangements (insert x (S - {x}))"
      by (intro derangements_add_one) auto
    from this \<open>x : S\<close> show "d(x := y, inv d y := x) \<in> derangements S"
      using insert_Diff by fastforce
  qed
  have split: "derangements S = ?D1 \<union> ?D2"
  proof
    from subset1 subset2 show "?D1 \<union> ?D2 \<subseteq> derangements S" by simp
  next
    show "derangements S \<subseteq> ?D1 \<union> ?D2"
    proof
      fix d
      assume d: "d : derangements S"
      show "d : ?D1 \<union> ?D2"
      proof (cases "d (d x) = x")
        case True
        from \<open>x : S\<close> d have "d x \<in> S" "d x \<noteq> x"
          by (auto simp add: derangements_in_image derangements_no_fixpoint)
        from d True have "Fun.swap x (d x) d \<in> derangements (S - {x, d x})"
          by (rule derangements_drop_minimal_cycle)
        from \<open>d x \<in> S\<close> \<open>d x \<noteq> x\<close> this have "d : ?D1"
          by (auto intro: image_eqI[where x = "(d x, Fun.swap x (d x) d)"])
        from this show ?thesis by auto
      next
        case False
        from d have bij: "bij d"
          by (auto elim: derangementsE simp add: permutes_imp_bij')
        from d \<open>x : S\<close> have that: "d x : S - {x}"
          by (intro derangements_in_image_strong)
        from d \<open>x : S\<close> False have derangements: "d(x:=x, inv d x:= d x) : derangements (S - {x})"
          by (auto intro: derangements_skip_one)
        from this have "bij (d(x := x, inv d x:= d x))"
          by (metis derangementsE permutes_imp_bij')+
        from this have a: "inv (d(x := x, inv d x := d x)) (d x) = inv d x"
          by (metis bij_inv_eq_iff fun_upd_same)
        from bij have x: "d (inv d x) = x" by (meson bij_inv_eq_iff)
        from d derangements_inv[of d] \<open>x : S\<close> have "inv d x \<noteq> x" "d x \<noteq> x"
          by (auto dest: derangements_no_fixpoint)
        from this a x have d_eq: "d = d(inv d x := d x, x := d x, inv (d(x := x, inv d x := d x)) (d x) := x)"
          by auto
        from derangements that have "(d x, d(x:=x, inv d x:=d x)) : ((S - {x}) \<times> derangements (S - {x}))" by auto
        from d_eq this have "d : ?D2"
          by (auto intro: image_eqI[where x = "(d x, d(x:=x, inv d x:=d x))"])
        from this show ?thesis by auto
      qed
    qed
  qed
  have no_intersect: "?D1 \<inter> ?D2 = {}"
  proof -
    have that: "\<And>d. d \<in> ?D1 \<Longrightarrow> d (d x) = x"
      using Diff_iff Diff_insert2 derangements_fixpoint insertI1 swap_apply(2) by fastforce
    have "\<And>d. d \<in> ?D2 \<Longrightarrow> d (d x) \<noteq> x"
    proof -
      fix d
      assume a: "d \<in> ?D2"
      from a obtain y d' where d: "d = d'(x := y, inv d' y := x)"
        "d' \<in> derangements (S - {x})" "y \<in> S - {x}"
        by auto
      from d(2) have inv: "inv d' \<in> derangements (S - {x})"
        by (rule derangements_inv)
      from d have inv_x: "inv d' y \<noteq> x"
        by (auto dest: derangements_inverse_in_image)
      from inv have inv_y: "inv d' y \<noteq> y"
        using d(3) derangements_no_fixpoint by blast
      from d inv_x have 1: "d x = y" by auto
      from d inv_y have 2: "d y = d' y" by auto
      from d(2, 3) have 3: "d' y \<in> S - {x}"
        by (auto dest: derangements_in_image)
      from 1 2 3 show "d (d x) \<noteq> x" by auto
    qed
    from this that show ?thesis by blast
  qed
  have inj: "inj_on (\<lambda>(y, f). Fun.swap x y f) {(y, f). y \<in> S & y \<noteq> x & f : derangements (S - {x, y})}"
    unfolding inj_on_def
    by (clarify; metis DiffD2 derangements_fixpoint insertI1 insert_commute swap_apply(1) swap_nilpotent)
  have eq: "{(y, f). y \<in> S & y \<noteq> x & f : derangements (S - {x, y})} = {(y, f). y \<in> S - {x} & f : derangements (S - {x, y})}"
    by simp
  have eq': "{(y, f). y \<in> S & y \<noteq> x & f : derangements (S - {x, y})} = Sigma (S - {x}) (%y. derangements (S - {x, y}))"
    unfolding Sigma_def by auto
  have card: "\<And> y. y \<in> S - {x} \<Longrightarrow> card (derangements (S - {x, y})) = count_derangements n"
  proof -
    fix y
    assume "y \<in> S - {x}"
    from 3(3, 4) \<open>x \<in> S\<close> this have "card (S - {x, y}) = n"
      by (metis Diff_insert2 card_Diff_singleton diff_Suc_1 finite_Diff)
    from 3(3) 3(2)[OF _ this] show "card (derangements (S - {x, y})) = count_derangements n" by auto
  qed
  from 3(3, 4) \<open>x : S\<close> have card2: "card (S - {x}) = Suc n" by (simp add: card.insert_remove insert_absorb)
  from inj have "card ?D1 = card {(y, f). y \<in> S - {x} \<and> f \<in> derangements (S - {x, y})}"
    by (simp add: card_image)
  also from 3(3) have "... = (\<Sum>y\<in>S - {x}. card (derangements (S - {x, y})))"
    by (subst card_product_dependent) (simp add: finite_derangements)+
  finally have card_1: "card ?D1 =(Suc n) * count_derangements n"
    using card card2 by auto
  have inj_2: "inj_on (\<lambda>(y, f). f(x := y, inv f y := x)) ((S - {x}) \<times> derangements (S - {x}))"
  proof -
    {
      fix d d' y y'
      assume 1: "d \<in> derangements (S - {x})" "d' \<in> derangements (S - {x})"
      assume 2: "y \<in> S" "y \<noteq> x" "y' \<in> S" "y' \<noteq> x"
      assume eq: "d(x := y, inv d y := x) = d'(x := y', inv d' y' := x)"
      from 1 2 eq \<open>x \<in> S\<close> have y: "y = y'"
        by (metis Diff_insert_absorb derangements_in_image derangements_inv
          fun_upd_same fun_upd_twist insert_iff mk_disjoint_insert)
      have "d = d'"
      proof
        fix z
        from 1 have d_x: "d x = d' x"
          by (auto dest!: derangements_fixpoint)
        from 1 have bij: "bij d" "bij d'"
          by (metis derangementsE permutes_imp_bij')+
        from this have d_d: "d (inv d y) = y" "d' (inv d' y') = y'"
          by (simp add: bij_is_surj surj_f_inv_f)+
        from 1 2 bij have neq: "d (inv d' y') \<noteq> x \<and> d' (inv d y) \<noteq> x"
          by (metis Diff_iff bij_inv_eq_iff derangements_fixpoint singletonI)
        from eq have "(d(x := y, inv d y := x)) z = (d'(x := y', inv d' y' := x)) z" by auto
        from y d_x d_d neq this show "d z = d' z" by (auto split: if_split_asm)
      qed
      from y this have "y = y' & d = d'" by auto
    }
    from this show ?thesis
      unfolding inj_on_def by auto
  qed
  from 3(3) 3(1)[OF _ card2] have card3: "card (derangements (S - {x})) = count_derangements (Suc n)"
    by auto
  from 3(3) inj_2 have card_2: "card ?D2 = (Suc n) * count_derangements (Suc n)"
    by (simp only: card_image) (auto simp add: card_cartesian_product card3 card2)
  from \<open>finite S\<close>have finite1: "finite ?D1"
    unfolding eq' by (auto intro: finite_derangements)
  from \<open>finite S\<close> have finite2: "finite ?D2"
    by (auto intro: finite_cartesian_product finite_derangements)
  show ?case
    by (simp add: split card_Un_disjoint finite1 finite2 no_intersect card_1 card_2 field_simps)
qed

subsubsection \<open>Closed-Form Characterization\<close>

lemma count_derangements:
  "real (count_derangements n) = fact n * (\<Sum>k \<in> {0..n}. (-1) ^ k / fact k)"
proof (induct n rule: count_derangements.induct)
  case (3 n)
  let ?f = "\<lambda>n. fact n * (\<Sum>k = 0..n. (- 1) ^ k / fact k)"
  have "real (count_derangements (Suc (Suc n))) = (n + 1) * (count_derangements (n + 1) + count_derangements n)"
    unfolding count_derangements.simps by simp
  also have "... = real (n + 1) * (real (count_derangements (n + 1)) + real (count_derangements n))"
    by (simp only: of_nat_mult of_nat_add)
  also have "... = (n + 1) * (?f (n + 1) + ?f n)"
    unfolding 3(2) 3(1)[unfolded Suc_eq_plus1] ..
  also have "(n + 1) * (?f (n + 1) + ?f n) = ?f (n + 2)"
  proof -
    define f where "f n = ((fact n) :: real) * (\<Sum>k = 0..n. (- 1) ^ k / fact k)" for n
    have f_eq: "\<And>n. f (n + 1) = (n + 1) * f n + (- 1) ^ (n + 1)"
    proof -
      fix n
      have "?f (n + 1) = (n + 1) * fact n * (\<Sum>k = 0..n. (- 1) ^ k / fact k) + fact (n + 1) * ((- 1) ^ (n + 1) / fact (n + 1))"
        by (simp add: field_simps)
      also have "... = (n + 1) * ?f n + (- 1) ^ (n + 1)" by (simp del: One_nat_def)
      finally show "?thesis n" unfolding f_def by simp
    qed
    from this have f_eq': "\<And> n. (n + 1) * f n = f (n + 1) + (- 1) ^ n" by auto
    from f_eq'[of n] have "(n + 1) * (f (n + 1) + f n) = ((n + 1) * f (n + 1)) + f (n + 1) + (- 1) ^ n"
      by (simp only: distrib_left of_nat_add of_nat_1)
    also have "... = (n + 2) * f (n + 1) + (- 1) ^ (n + 2)"
      by (simp del: One_nat_def add_2_eq_Suc' add: algebra_simps) simp
    also from f_eq[of "n + 1"] have "... = f (n + 2)" by simp
    finally show ?thesis unfolding f_def by simp
  qed
  finally show ?case by simp
qed (auto)

subsubsection \<open>Approximation of Cardinality\<close>

lemma two_power_fact_le_fact:
  assumes "n \<ge> 1"
  shows   "2^k * fact n \<le> (fact (n + k) :: 'a :: {semiring_char_0,linordered_semidom})"
proof (induction k)
  case (Suc k)
  have "2 ^ Suc k * fact n = 2 * (2 ^ k * fact n)" by (simp add: algebra_simps)
  also note Suc.IH
  also from assms have "of_nat 1 + of_nat 1 \<le> of_nat n + (of_nat (Suc k) :: 'a)"
    by (intro add_mono) (unfold of_nat_le_iff, simp_all)
  hence "2 * (fact (n + k) :: 'a) \<le> of_nat (n + Suc k) * fact (n + k)"
    by (intro mult_right_mono) (simp_all add: add_ac)
  also have "\<dots> = fact (n + Suc k)" by simp
  finally show ?case by - (simp add: mult_left_mono)
qed simp_all

lemma exp1_approx:
  assumes "n > 0"
  shows   "exp (1::real) - (\<Sum>k<n. 1 / fact k) \<in> {0..2 / fact n}"
proof (unfold atLeastAtMost_iff, safe)
  have "(\<lambda>k. 1^k / fact k) sums exp (1::real)"
    using exp_converges[of "1::real"] by (simp add: field_simps)
  from sums_split_initial_segment[OF this, of n]
    have sums: "(\<lambda>k. 1 / fact (n+k)) sums (exp 1 - (\<Sum>k<n. 1 / fact k :: real))"
    by (simp add:  algebra_simps power_add)
  from assms show "(exp 1 - (\<Sum>k<n. 1 / fact k :: real)) \<ge> 0"
    by (intro sums_le[OF _ sums_zero sums]) auto
  show "(exp 1 - (\<Sum>k<n. 1 / fact k :: real)) \<le> 2 / fact n"
  proof (rule sums_le[OF allI])
    from assms have "(\<lambda>k. (1 / fact n) * (1 / 2)^k :: real) sums ((1 / fact n) * (1 / (1 - 1 / 2)))"
      by (intro sums_mult geometric_sums) simp_all
    also have "\<dots> = 2 / fact n" by simp
    finally show "(\<lambda>k. 1 / fact n * (1 / 2) ^ k) sums (2 / fact n :: real)" .
  next
    fix k show "(1 / fact (n+k)) \<le> (1 / fact n) * (1 / 2 :: real)^k" for k
      using two_power_fact_le_fact[of n k] assms by (auto simp: field_simps)
  qed fact+
qed

lemma exp1_bounds: "exp 1 \<in> {8 / 3..11 / 4 :: real}"
  using exp1_approx[of 4] by (simp add: eval_nat_numeral)

lemma count_derangements_approximation:
  assumes "n \<noteq> 0"
  shows "abs(real (count_derangements n) - fact n / exp 1) < 1 / 2"
proof (cases "n \<ge> 5")
  case False
  from assms this have n: "n = 1 \<or> n = 2 \<or> n = 3 \<or> n = 4" by auto
  from exp1_bounds have 1: "abs(real (count_derangements 1) - fact 1 / exp 1) < 1 / 2"
    by simp
  from exp1_bounds have 2: "abs(real (count_derangements 2) - fact 2 / exp 1) < 1 / 2"
    by (auto simp add: eval_nat_numeral abs_real_def)
  from exp1_bounds have 3: "abs(real (count_derangements 3) - fact 3 / exp 1) < 1 / 2"
    by (auto simp add: eval_nat_numeral abs_if field_simps)
  from exp1_bounds have 4: "abs(real (count_derangements 4) - fact 4 / exp 1) < 1 / 2"
    by (auto simp: abs_if field_simps eval_nat_numeral)
  from 1 2 3 4 n show ?thesis by auto
next
  case True
  from Maclaurin_exp_le[of "- 1" "n + 1"]
  obtain t where t: "abs (t :: real) \<le> abs (- 1)"
    and exp: "exp (- 1) = (\<Sum>m<n + 1. (- 1) ^ m / fact m) + exp t / fact (n + 1) * (- 1) ^ (n + 1)"
    by blast
  from exp have sum_eq_exp: 
    "(\<Sum>k = 0..n. (- 1) ^ k / fact k) = exp (- 1) - exp t / fact (n + 1) * (- 1) ^ (n + 1)"
    by (simp add: atLeast0AtMost ivl_disj_un(2)[symmetric])
  have fact_plus1: "fact (n + 1) = (n + 1) * fact n" by simp
  have eq: "\<bar>real (count_derangements n) - fact n / exp 1\<bar> = exp t / (n + 1)"
    by (simp del: One_nat_def 
             add: count_derangements sum_eq_exp exp_minus inverse_eq_divide algebra_simps abs_mult)
       (simp add: fact_plus1)
  from t have "exp t \<le> exp 1" by simp
  also from exp1_bounds have "\<dots> < 3" by simp
  finally show ?thesis using \<open>n \<ge> 5\<close> by (simp add: eq)
qed

theorem derangements_formula:
  assumes "n \<noteq> 0" "finite S" "card S = n"
  shows "int (card (derangements S)) = round (fact n / exp 1 :: real)"
  using count_derangements_approximation[of n] assms
  by (intro round_unique' [symmetric]) (auto simp: card_derangements abs_minus_commute)

theorem derangements_formula':
  assumes "n \<noteq> 0" "finite S" "card S = n"
  shows "card (derangements S) = nat (round (fact n / exp 1 :: real))"
  using derangements_formula[OF assms] by simp

end
