section \<open>Intersection\<close>
theory Intersection
imports
  "HOL-Library.Monad_Syntax"
  Polygon
  Counterclockwise_2D_Arbitrary
  Affine_Form
begin
text \<open>\label{sec:intersection}\<close>

subsection \<open>Polygons and @{term ccw}, @{term lex}, @{term psi}, @{term coll}\<close>

lemma polychain_of_ccw_conjunction:
  assumes sorted: "ccw'.sortedP 0 Ps"
  assumes z: "z \<in> set (polychain_of Pc Ps)"
  shows "list_all (\<lambda>(xi, xj). ccw xi xj (fst z) \<and> ccw xi xj (snd z)) (polychain_of Pc Ps)"
  using assms
proof (induction Ps arbitrary: Pc z rule: list.induct)
  case (Cons P Ps)
  {
    assume "set Ps = {}"
    hence ?case using Cons by simp
  } moreover {
    assume "set Ps \<noteq> {}"
    hence "Ps \<noteq> []" by simp
    {
      fix a assume "a \<in> set Ps"
      hence "ccw' 0 P a"
        using Cons.prems
        by (auto elim!: linorder_list0.sortedP_Cons)
    } note ccw' = this
    have sorted': "linorder_list0.sortedP (ccw' 0) Ps"
      using Cons.prems
      by (auto elim!: linorder_list0.sortedP_Cons)
    from in_set_polychain_of_imp_sum_list[OF Cons(3)]
    obtain d
    where d: "z = (Pc + sum_list (take d (P # Ps)), Pc + sum_list (take (Suc d) (P # Ps)))" .

    from Cons(3)
    have disj: "z = (Pc, Pc + P) \<or> z \<in> set (polychain_of (Pc + P) Ps)"
      by auto

    let ?th = "\<lambda>(xi, xj). ccw xi xj Pc \<and> ccw xi xj (Pc + P)"
    have la: "list_all ?th (polychain_of (Pc + P) Ps)"
    proof (rule list_allI)
      fix x assume x: "x \<in> set (polychain_of (Pc + P) Ps)"
      from in_set_polychain_of_imp_sum_list[OF this]
      obtain e where e: "x = (Pc + P + sum_list (take e Ps), Pc + P + sum_list (take (Suc e) Ps))"
        by auto
      {
        assume "e \<ge> length Ps"
        hence "?th x" by (auto simp: e)
      } moreover {
        assume "e < length Ps"
        have 0: "\<And>e. e < length Ps \<Longrightarrow> ccw' 0 P (Ps ! e)"
          by (rule ccw') (simp add: )
        have 2: "0 < e \<Longrightarrow> ccw' 0 (P + sum_list (take e Ps)) (Ps ! e)"
          using \<open>e < length Ps\<close>
          by (auto intro!: ccw'.add1 0 ccw'.sum2 sorted' ccw'.sorted_nth_less
            simp: sum_list_sum_nth)
        have "ccw Pc (Pc + P + sum_list (take e Ps)) (Pc + P + sum_list (take (Suc e) Ps))"
          by (cases "e = 0")
            (auto simp add: ccw_translate_origin take_Suc_eq add.assoc[symmetric] 0 2
              intro!: ccw'_imp_ccw intro: cyclic)
        hence "ccw (Pc + P + sum_list (take e Ps)) (Pc + P + sum_list (take (Suc e) Ps)) Pc"
          by (rule cyclic)
        moreover
        have "0 < e \<Longrightarrow> ccw 0 (Ps ! e) (- sum_list (take e Ps))"
          using \<open>e < length Ps\<close>
          by (auto simp add: take_Suc_eq add.assoc[symmetric]
              sum_list_sum_nth
            intro!: ccw'_imp_ccw ccw'.sum2 sorted' ccw'.sorted_nth_less)
        hence "ccw (Pc + P + sum_list (take e Ps)) (Pc + P + sum_list (take (Suc e) Ps)) (Pc + P)"
          by (cases "e = 0") (simp_all add: ccw_translate_origin take_Suc_eq)
        ultimately have "?th x"
          by (auto simp add: e)
      } ultimately show "?th x" by arith
    qed
    from disj have ?case
    proof
      assume z: "z \<in> set (polychain_of (Pc + P) Ps)"
      have "ccw 0 P (sum_list (take d (P # Ps)))"
      proof (cases d)
        case (Suc e) note e = this
        show ?thesis
        proof (cases e)
          case (Suc f)
          have "ccw 0 P (P + sum_list (take (Suc f) Ps))"
            using z
            by (force simp add: sum_list_sum_nth intro!: ccw'.sum intro: ccw' ccw'_imp_ccw)
          thus ?thesis
            by (simp add: e Suc)
        qed (simp add: e)
      qed simp
      hence "ccw Pc (Pc + P) (fst z)"
        by (simp add: d ccw_translate_origin)
      moreover
      from z have "ccw 0 P (P + sum_list (take d Ps))"
        by (cases d, force)
          (force simp add: sum_list_sum_nth intro!: ccw'_imp_ccw ccw'.sum intro: ccw')+
      hence "ccw Pc (Pc + P) (snd z)"
        by (simp add: d ccw_translate_origin)
      moreover
      from z Cons.prems have "list_all (\<lambda>(xi, xj). ccw xi xj (fst z) \<and> ccw xi xj (snd z))
        (polychain_of (Pc + P) Ps)"
        by (intro Cons.IH) (auto elim!: linorder_list0.sortedP_Cons)
      ultimately show ?thesis by simp
    qed (simp add: la)
  } ultimately show ?case by blast
qed simp

lemma lex_polychain_of_center:
  "d \<in> set (polychain_of x0 xs) \<Longrightarrow> list_all (\<lambda>x. lex x 0) xs \<Longrightarrow> lex (snd d) x0"
proof (induction xs arbitrary: x0)
  case (Cons x xs) thus ?case
    by (auto simp add: lex_def lex_translate_origin dest!: Cons.IH)
qed (auto simp: lex_translate_origin)

lemma lex_polychain_of_last:
  "(c, d) \<in> set (polychain_of x0 xs) \<Longrightarrow> list_all (\<lambda>x. lex x 0) xs \<Longrightarrow>
    lex (snd (last (polychain_of x0 xs))) d"
proof (induction xs arbitrary: x0 c d)
  case (Cons x xs)
  let ?c1 = "c = x0 \<and> d = x0 + x"
  let ?c2 = "(c, d) \<in> set (polychain_of (x0 + x) xs)"
  from Cons(2) have "?c1 \<or> ?c2" by auto
  thus ?case
  proof
    assume ?c1
    with Cons.prems show ?thesis
      by (auto intro!: lex_polychain_of_center)
  next
    assume ?c2
    from Cons.IH[OF this] Cons.prems
    show ?thesis
      by auto
  qed
qed (auto simp: lex_translate_origin)

lemma distinct_fst_polychain_of:
  assumes "list_all (\<lambda>x. x \<noteq> 0) xs"
  assumes "list_all (\<lambda>x. lex x 0) xs"
  shows "distinct (map fst (polychain_of x0 xs))"
  using assms
proof (induction xs arbitrary: x0)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  hence "\<And>d. list_all (\<lambda>x. lex x 0) (x # take d xs)"
    by (auto simp: list_all_iff dest!: in_set_takeD)
  from sum_list_nlex_eq_zero_iff[OF this] Cons.prems
  show ?case
    by (cases "xs = []") (auto intro!: Cons.IH elim!: in_set_polychain_of_imp_sum_list)
qed

lemma distinct_snd_polychain_of:
  assumes "list_all (\<lambda>x. x \<noteq> 0) xs"
  assumes "list_all (\<lambda>x. lex x 0) xs"
  shows "distinct (map snd (polychain_of x0 xs))"
  using assms
proof (induction xs arbitrary: x0)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  have contra:
    "\<And>d. xs \<noteq> [] \<Longrightarrow> list_all (\<lambda>x. x \<noteq> 0) xs \<Longrightarrow> list_all ((=) 0) (take (Suc d) xs) \<Longrightarrow> False"
    by (auto simp: neq_Nil_conv)
  from Cons have "\<And>d. list_all (\<lambda>x. lex x 0) (take (Suc d) xs)"
    by (auto simp: list_all_iff dest!: in_set_takeD)
  from sum_list_nlex_eq_zero_iff[OF this] Cons.prems contra
  show ?case
    by (cases "xs = []") (auto intro!: Cons.IH elim!: in_set_polychain_of_imp_sum_list dest!: contra)
qed


subsection \<open>Orient all entries\<close>

lift_definition nlex_pdevs::"point pdevs \<Rightarrow> point pdevs"
  is "\<lambda>x n. if lex 0 (x n) then - x n else x n" by simp

lemma pdevs_apply_nlex_pdevs[simp]: "pdevs_apply (nlex_pdevs x) n =
  (if lex 0 (pdevs_apply x n) then - pdevs_apply x n else pdevs_apply x n)"
  by transfer simp

lemma nlex_pdevs_zero_pdevs[simp]: "nlex_pdevs zero_pdevs = zero_pdevs"
  by (auto intro!: pdevs_eqI)

lemma pdevs_domain_nlex_pdevs[simp]: "pdevs_domain (nlex_pdevs x) = pdevs_domain x"
  by (auto simp: pdevs_domain_def)

lemma degree_nlex_pdevs[simp]: "degree (nlex_pdevs x) = degree x"
  by (rule degree_cong) auto

lemma
  pdevs_val_nlex_pdevs:
  assumes "e \<in> UNIV \<rightarrow> I" "uminus ` I = I"
  obtains e' where "e' \<in> UNIV \<rightarrow> I" "pdevs_val e x = pdevs_val e' (nlex_pdevs x)"
  using assms
  by (atomize_elim, intro exI[where x="\<lambda>n. if lex 0 (pdevs_apply x n) then - e n else e n"])
    (force simp: pdevs_val_pdevs_domain intro!: sum.cong)

lemma
  pdevs_val_nlex_pdevs2:
  assumes "e \<in> UNIV \<rightarrow> I" "uminus ` I = I"
  obtains e' where "e' \<in> UNIV \<rightarrow> I" "pdevs_val e (nlex_pdevs x) = pdevs_val e' x"
  using assms
  by (atomize_elim, intro exI[where x="\<lambda>n. (if lex 0 (pdevs_apply x n) then - e n else e n)"])
    (force simp: pdevs_val_pdevs_domain intro!: sum.cong)

lemma
  pdevs_val_selsort_ccw:
  assumes "distinct xs"
  assumes "e \<in> UNIV \<rightarrow> I"
  obtains e' where "e' \<in> UNIV \<rightarrow> I"
    "pdevs_val e (pdevs_of_list xs) = pdevs_val e' (pdevs_of_list (ccw.selsort 0 xs))"
proof -
  have "set xs = set (ccw.selsort 0 xs)" "distinct xs" "distinct (ccw.selsort 0 xs)"
    by (simp_all add: assms)
  from this assms(2) obtain e'
  where "e' \<in> UNIV \<rightarrow> I"
    "pdevs_val e (pdevs_of_list xs) = pdevs_val e' (pdevs_of_list (ccw.selsort 0 xs))"
    by (rule pdevs_val_permute)
  thus thesis ..
qed

lemma
  pdevs_val_selsort_ccw2:
  assumes "distinct xs"
  assumes "e \<in> UNIV \<rightarrow> I"
  obtains e' where "e' \<in> UNIV \<rightarrow> I"
    "pdevs_val e (pdevs_of_list (ccw.selsort 0 xs)) = pdevs_val e' (pdevs_of_list xs)"
proof -
  have "set (ccw.selsort 0 xs) = set xs" "distinct (ccw.selsort 0 xs)" "distinct xs"
    by (simp_all add: assms)
  from this assms(2) obtain e'
  where "e' \<in> UNIV \<rightarrow> I"
    "pdevs_val e (pdevs_of_list (ccw.selsort 0 xs)) = pdevs_val e' (pdevs_of_list xs)"
    by (rule pdevs_val_permute)
  thus thesis ..
qed

lemma lex_nlex_pdevs: "lex (pdevs_apply (nlex_pdevs x) i) 0"
  by (auto simp: lex_def algebra_simps prod_eq_iff)


subsection \<open>Lowest Vertex\<close>

definition lowest_vertex::"'a::ordered_euclidean_space aform \<Rightarrow> 'a" where
  "lowest_vertex X = fst X - sum_list (map snd (list_of_pdevs (snd X)))"

lemma snd_abs: "snd (abs x) = abs (snd x)"
  by (metis abs_prod_def snd_conv)

lemma lowest_vertex:
  fixes X Y::"(real*real) aform"
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "\<And>i. snd (pdevs_apply (snd X) i) \<ge> 0"
  assumes "\<And>i. abs (snd (pdevs_apply (snd Y) i)) = abs (snd (pdevs_apply (snd X) i))"
  assumes "degree_aform Y = degree_aform X"
  assumes "fst Y = fst X"
  shows "snd (lowest_vertex X) \<le> snd (aform_val e Y)"
proof -
  from abs_pdevs_val_le_tdev[OF assms(1), of "snd Y"]
  have "snd \<bar>pdevs_val e (snd Y)\<bar> \<le> (\<Sum>i<degree_aform Y. \<bar>snd (pdevs_apply (snd X) i)\<bar>)"
    unfolding lowest_vertex_def
    by (auto simp: aform_val_def tdev_def less_eq_prod_def snd_sum snd_abs assms)
  also have "\<dots> = (\<Sum>i<degree_aform X. snd (pdevs_apply (snd X) i))"
    by (simp add: assms)
  also have "\<dots> \<le> snd (sum_list (map snd (list_of_pdevs (snd X))))"
    by (simp add: sum_list_list_of_pdevs dense_list_of_pdevs_def sum_list_distinct_conv_sum_set
      snd_sum atLeast0LessThan)
  finally show ?thesis
    by (auto simp: aform_val_def lowest_vertex_def minus_le_iff snd_abs abs_real_def assms
      split: if_split_asm)
qed

lemma sum_list_nonposI:
  fixes xs::"'a::ordered_comm_monoid_add list"
  shows "list_all (\<lambda>x. x \<le> 0) xs \<Longrightarrow> sum_list xs \<le> 0"
  by (induct xs) (auto simp: intro!: add_nonpos_nonpos)

lemma center_le_lowest:
  "fst (fst X) \<le> fst (lowest_vertex (fst X, nlex_pdevs (snd X)))"
  by (auto simp: lowest_vertex_def fst_sum_list intro!: sum_list_nonposI)
    (auto simp: lex_def list_all_iff list_of_pdevs_def dest!: in_set_butlastD split: if_split_asm)

lemma lowest_vertex_eq_center_iff:
  "lowest_vertex (x0, nlex_pdevs (snd X)) = x0 \<longleftrightarrow> snd X = zero_pdevs"
proof
  assume "lowest_vertex (x0, nlex_pdevs (snd X)) = x0"
  then have "sum_list (map snd (list_of_pdevs (nlex_pdevs (snd X)))) = 0"
    by (simp add: lowest_vertex_def)
  moreover have "list_all (\<lambda>x. Counterclockwise_2D_Arbitrary.lex x 0)
    (map snd (list_of_pdevs (nlex_pdevs (snd X))))"
    by (auto simp add: list_all_iff list_of_pdevs_def)
  ultimately have "\<forall>x\<in>set (list_of_pdevs (nlex_pdevs (snd X))). snd x = 0"
    by (simp add: sum_list_nlex_eq_zero_iff list_all_iff)
  then have "pdevs_apply (snd X) i = pdevs_apply zero_pdevs i" for i
    by (simp add: list_of_pdevs_def split: if_splits)
  then show "snd X = zero_pdevs"
    by (rule pdevs_eqI)
qed (simp add: lowest_vertex_def)


subsection \<open>Collinear Generators\<close>

lemma scaleR_le_self_cancel:
  fixes c::"'a::ordered_real_vector"
  shows "a *\<^sub>R c \<le> c \<longleftrightarrow> (1 < a \<and> c \<le> 0 \<or> a < 1 \<and> 0 \<le> c \<or> a = 1)"
  using scaleR_le_0_iff[of "a - 1" c]
  by (simp add: algebra_simps)

lemma pdevs_val_coll:
  assumes coll: "list_all (coll 0 x) xs"
  assumes nlex: "list_all (\<lambda>x. lex x 0) xs"
  assumes "x \<noteq> 0"
  assumes "f \<in> UNIV \<rightarrow> {-1 .. 1}"
  obtains e where "e \<in> {-1 .. 1}" "pdevs_val f (pdevs_of_list xs) = e *\<^sub>R (sum_list xs)"
proof cases
  assume "sum_list xs = 0"
  have "pdevs_of_list xs = zero_pdevs"
    by (auto intro!: pdevs_eqI sum_list_nlex_eq_zeroI[OF nlex \<open>sum_list xs = 0\<close>]
      simp: pdevs_apply_pdevs_of_list list_all_iff dest!: nth_mem)
  hence "0 \<in> {-1 .. 1::real}" "pdevs_val f (pdevs_of_list xs) = 0 *\<^sub>R sum_list xs"
    by simp_all
  thus ?thesis ..
next
  assume "sum_list xs \<noteq> 0"
  have "sum_list (map abs xs) \<ge> 0"
    by (auto intro!: sum_list_nonneg)
  hence [simp]: "\<not>sum_list (map abs xs) \<le> 0"
    by (metis \<open>sum_list xs \<noteq> 0\<close> abs_le_zero_iff antisym_conv sum_list_abs)

  have collist: "list_all (coll 0 (sum_list xs)) xs"
  proof (rule list_allI)
    fix y assume "y \<in> set xs"
    hence "coll 0 x y"
      using coll by (auto simp: list_all_iff)
    also have "coll 0 x (sum_list xs)"
      using coll by (auto simp: list_all_iff intro!: coll_sum_list)
    finally (coll_trans)
    show "coll 0 (sum_list xs) y"
      by (simp add: coll_commute \<open>x \<noteq> 0\<close>)
  qed

  {
    fix i assume "i < length xs"
    hence "\<exists>r. xs ! i = r *\<^sub>R (sum_list xs)"
      by (metis (mono_tags) coll_scale nth_mem \<open>sum_list xs \<noteq> 0\<close> list_all_iff collist)
  } then obtain r where r: "\<And>i. i < length xs \<Longrightarrow> (xs ! i) = r i *\<^sub>R (sum_list xs)"
    by metis
  let ?coll = "pdevs_of_list xs"
  have "pdevs_val f (pdevs_of_list xs) =
      (\<Sum>i<degree (pdevs_of_list xs). f i *\<^sub>R xs ! i)"
    unfolding pdevs_val_sum
    by (simp add: pdevs_apply_pdevs_of_list less_degree_pdevs_of_list_imp_less_length)
  also have "\<dots> = (\<Sum>i<degree ?coll. (f i * r i) *\<^sub>R (sum_list xs))"
    by (simp add: r less_degree_pdevs_of_list_imp_less_length)
  also have "\<dots> = (\<Sum>i<degree ?coll. f i * r i) *\<^sub>R (sum_list xs)"
    by (simp add: algebra_simps scaleR_sum_left)
  finally have eq: "pdevs_val f ?coll = (\<Sum>i<degree ?coll. f i * r i) *\<^sub>R (sum_list xs)"
    (is "_ = ?e *\<^sub>R _")
    .

  have "abs (pdevs_val f ?coll) \<le> tdev ?coll"
    using assms(4)
    by (intro abs_pdevs_val_le_tdev) (auto simp: Pi_iff less_imp_le)
  also have "\<dots> = sum_list (map abs xs)" using assms by simp
  also note eq
  finally have less: "\<bar>?e\<bar> *\<^sub>R abs (sum_list xs) \<le> sum_list (map abs xs)" by (simp add: abs_scaleR)
  also have "\<bar>sum_list xs\<bar> = sum_list (map abs xs)"
    using coll \<open>x \<noteq> 0\<close> nlex
    by (rule abs_sum_list_coll)
  finally have "?e \<in> {-1 .. 1}"
    by (auto simp add: less_le scaleR_le_self_cancel)
  thus ?thesis using eq ..
qed

lemma scaleR_eq_self_cancel:
  fixes x::"'a::real_vector"
  shows "a *\<^sub>R x = x \<longleftrightarrow> a = 1 \<or> x = 0"
  using scaleR_cancel_right[of a x 1]
  by simp

lemma abs_pdevs_val_less_tdev:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}" "degree x > 0"
  shows "\<bar>pdevs_val e x\<bar> < tdev x"
proof -
  have bnds: "\<And>i. \<bar>e i\<bar> < 1" "\<And>i. \<bar>e i\<bar> \<le> 1"
    using assms
    by (auto simp: Pi_iff abs_less_iff order.strict_implies_order)
  moreover
  let ?w = "degree x - 1"
  have witness: "\<bar>e ?w\<bar> *\<^sub>R \<bar>pdevs_apply x ?w\<bar> < \<bar>pdevs_apply x ?w\<bar>"
    using degree_least_nonzero[of x] assms bnds
    by (intro neq_le_trans) (auto simp: scaleR_eq_self_cancel Pi_iff
      intro!: scaleR_left_le_one_le neq_le_trans
      intro: abs_leI less_imp_le dest!: order.strict_implies_not_eq)
  ultimately
  show ?thesis
    using assms witness bnds
    by (auto simp: pdevs_val_sum tdev_def abs_scaleR
      intro!: le_less_trans[OF sum_abs] sum_strict_mono_ex1 scaleR_left_le_one_le)
qed

lemma pdevs_val_coll_strict:
  assumes coll: "list_all (coll 0 x) xs"
  assumes nlex: "list_all (\<lambda>x. lex x 0) xs"
  assumes "x \<noteq> 0"
  assumes "f \<in> UNIV \<rightarrow> {-1 <..< 1}"
  obtains e where "e \<in> {-1 <..< 1}" "pdevs_val f (pdevs_of_list xs) = e *\<^sub>R (sum_list xs)"
proof cases
  assume "sum_list xs = 0"
  have "pdevs_of_list xs = zero_pdevs"
    by (auto intro!: pdevs_eqI sum_list_nlex_eq_zeroI[OF nlex \<open>sum_list xs = 0\<close>]
      simp: pdevs_apply_pdevs_of_list list_all_iff dest!: nth_mem)
  hence "0 \<in> {-1 <..< 1::real}" "pdevs_val f (pdevs_of_list xs) = 0 *\<^sub>R sum_list xs"
    by simp_all
  thus ?thesis ..
next
  assume "sum_list xs \<noteq> 0"
  have "sum_list (map abs xs) \<ge> 0"
    by (auto intro!: sum_list_nonneg)
  hence [simp]: "\<not>sum_list (map abs xs) \<le> 0"
    by (metis \<open>sum_list xs \<noteq> 0\<close> abs_le_zero_iff antisym_conv sum_list_abs)

  have "\<exists>x \<in> set xs. x \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>x\<in>set xs. x \<noteq> 0)"
    hence "\<And>x. x \<in> set xs \<Longrightarrow> x = 0" by auto
    hence "sum_list xs = 0"
      by (auto simp: sum_list_eq_0_iff_nonpos list_all_iff less_eq_prod_def prod_eq_iff fst_sum_list
        snd_sum_list)
    thus False using \<open>sum_list xs \<noteq> 0\<close> by simp
  qed
  then obtain i where i: "i < length xs" "xs ! i \<noteq> 0"
    by (metis in_set_conv_nth)
  hence "i < degree (pdevs_of_list xs)"
    by (auto intro!: degree_gt simp: pdevs_apply_pdevs_of_list)
  hence deg_pos: "0 < degree (pdevs_of_list xs)" by simp

  have collist: "list_all (coll 0 (sum_list xs)) xs"
  proof (rule list_allI)
    fix y assume "y \<in> set xs"
    hence "coll 0 x y"
      using coll by (auto simp: list_all_iff)
    also have "coll 0 x (sum_list xs)"
      using coll by (auto simp: list_all_iff intro!: coll_sum_list)
    finally (coll_trans)
    show "coll 0 (sum_list xs) y"
      by (simp add: coll_commute \<open>x \<noteq> 0\<close>)
  qed

  {
    fix i assume "i < length xs"
    hence "\<exists>r. xs ! i = r *\<^sub>R (sum_list xs)"
      by (metis (mono_tags, lifting) \<open>sum_list xs \<noteq> 0\<close> coll_scale collist list_all_iff nth_mem)
  } then obtain r where r: "\<And>i. i < length xs \<Longrightarrow> (xs ! i) = r i *\<^sub>R (sum_list xs)"
    by metis
  let ?coll = "pdevs_of_list xs"
  have "pdevs_val f (pdevs_of_list xs) =
      (\<Sum>i<degree (pdevs_of_list xs). f i *\<^sub>R xs ! i)"
    unfolding pdevs_val_sum
    by (simp add: less_degree_pdevs_of_list_imp_less_length pdevs_apply_pdevs_of_list)
  also have "\<dots> = (\<Sum>i<degree ?coll. (f i * r i) *\<^sub>R (sum_list xs))"
    by (simp add: r less_degree_pdevs_of_list_imp_less_length)
  also have "\<dots> = (\<Sum>i<degree ?coll. f i * r i) *\<^sub>R (sum_list xs)"
    by (simp add: algebra_simps scaleR_sum_left)
  finally have eq: "pdevs_val f ?coll = (\<Sum>i<degree ?coll. f i * r i) *\<^sub>R (sum_list xs)"
    (is "_ = ?e *\<^sub>R _")
    .

  have "abs (pdevs_val f ?coll) < tdev ?coll"
    using assms(4)
    by (intro abs_pdevs_val_less_tdev) (auto simp: Pi_iff less_imp_le deg_pos)
  also have "\<dots> = sum_list (map abs xs)" using assms by simp
  also note eq
  finally have less: "\<bar>?e\<bar> *\<^sub>R abs (sum_list xs) < sum_list (map abs xs)" by (simp add: abs_scaleR)
  also have "\<bar>sum_list xs\<bar> = sum_list (map abs xs)"
    using coll \<open>x \<noteq> 0\<close> nlex
    by (rule abs_sum_list_coll)
  finally have "?e \<in> {-1 <..< 1}"
    by (auto simp add: less_le scaleR_le_self_cancel)
  thus ?thesis using eq ..
qed


subsection \<open>Independent Generators\<close>

fun independent_pdevs::"point list \<Rightarrow> point list"
  where
  "independent_pdevs [] = []"
| "independent_pdevs (x#xs) =
    (let
      (cs, is) = List.partition (coll 0 x) xs;
      s = x + sum_list cs
    in (if s = 0 then [] else [s]) @ independent_pdevs is)"

lemma in_set_independent_pdevsE:
  assumes "y \<in> set (independent_pdevs xs)"
  obtains x where "x\<in>set xs" "coll 0 x y"
proof atomize_elim
  show "\<exists>x. x \<in> set xs \<and> coll 0 x y"
    using assms
  proof (induct xs rule: independent_pdevs.induct)
    case 1 thus ?case by simp
  next
    case (2 z zs)
    let ?c1 = "y = z + sum_list (filter (coll 0 z) zs)"
    let ?c2 = "y \<in> set (independent_pdevs (filter (Not \<circ> coll 0 z) zs))"
    from 2
    have "?c1 \<or> ?c2"
      by (auto simp: Let_def split: if_split_asm)
    thus ?case
    proof
      assume ?c2
      hence "y \<in> set (independent_pdevs (snd (partition (coll 0 z) zs)))"
        by simp
      from 2(1)[OF refl prod.collapse refl this]
      show ?case
        by auto
    next
      assume y: ?c1
      show ?case
        unfolding y
        by (rule exI[where x="z"]) (auto intro!: coll_add coll_sum_list )
    qed
  qed
qed

lemma in_set_independent_pdevs_nonzero: "x \<in> set (independent_pdevs xs) \<Longrightarrow> x \<noteq> 0"
proof (induct xs rule: independent_pdevs.induct)
  case (2 y ys)
  from 2(1)[OF refl prod.collapse refl] 2(2)
  show ?case
    by (auto simp: Let_def split: if_split_asm)
qed simp

lemma independent_pdevs_pairwise_non_coll:
  assumes "x \<in> set (independent_pdevs xs)"
  assumes "y \<in> set (independent_pdevs xs)"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0"
  assumes "x \<noteq> y"
  shows "\<not> coll 0 x y"
using assms
proof (induct xs rule: independent_pdevs.induct)
  case 1 thus ?case by simp
next
  case (2 z zs)
  from 2 have "z \<noteq> 0" by simp
  from 2(2) have "x \<noteq> 0" by (rule in_set_independent_pdevs_nonzero)
  from 2(3) have "y \<noteq> 0" by (rule in_set_independent_pdevs_nonzero)
  let ?c = "filter (coll 0 z) zs"
  let ?nc = "filter (Not \<circ> coll 0 z) zs"
  {
    assume "x \<in> set (independent_pdevs ?nc)" "y \<in> set (independent_pdevs ?nc)"
    hence "\<not>coll 0 x y"
      by (intro 2(1)[OF refl prod.collapse refl _ _ 2(4) 2(5)]) auto
  } note IH = this
  {
    fix x assume "x \<noteq> 0" "z + sum_list ?c \<noteq> 0"
      "coll 0 x (z + sum_list ?c)"
    hence "x \<notin> set (independent_pdevs ?nc)"
      using sum_list_filter_coll_ex_scale[OF \<open>z \<noteq> 0\<close>, of "z#zs"]
      by (auto elim!: in_set_independent_pdevsE  simp: coll_commute)
        (metis (no_types) \<open>x \<noteq> 0\<close> coll_scale coll_scaleR)
  } note nc = this
  from 2(2,3,4,5) nc[OF \<open>x \<noteq> 0\<close>] nc[OF \<open>y \<noteq> 0\<close>]
  show ?case
    by (auto simp: Let_def IH coll_commute split: if_split_asm)
qed

lemma distinct_independent_pdevs[simp]:
  shows "distinct (independent_pdevs xs)"
proof (induct xs rule: independent_pdevs.induct)
  case 1 thus ?case by simp
next
  case (2 x xs)
  let ?is = "independent_pdevs (filter (Not \<circ> coll 0 x) xs)"
  have "distinct ?is"
    by (rule 2) (auto intro!: 2)
  thus ?case
  proof (clarsimp simp add: Let_def)
    let ?s = "x + sum_list (filter (coll 0 x) xs)"
    assume s: "?s \<noteq> 0" "?s \<in> set ?is"
    from in_set_independent_pdevsE[OF s(2)]
    obtain y where y:
      "y \<in> set (filter (Not \<circ> coll 0 x) xs)"
      "coll 0 y (x + sum_list (filter (coll 0 x) xs))"
      by auto
    {
      assume "y = 0 \<or> x = 0 \<or> sum_list (filter (coll 0 x) xs) = 0"
      hence False using s y by (auto simp: coll_commute)
    } moreover {
      assume "y \<noteq> 0" "x \<noteq> 0" "sum_list (filter (coll 0 x) xs) \<noteq> 0"
        "sum_list (filter (coll 0 x) xs) + x \<noteq> 0"
      have *: "coll 0 (sum_list (filter (coll 0 x) xs)) x"
        by (auto intro!: coll_sum_list simp: coll_commute)
      have "coll 0 y (sum_list (filter (coll 0 x) xs) + x)"
        using s y by (simp add: add.commute)
      hence "coll 0 y x" using *
        by (rule coll_add_trans) fact+
      hence False using s y by (simp add: coll_commute)
    } ultimately show False using s y by (auto simp: add.commute)
  qed
qed

lemma in_set_independent_pdevs_invariant_nlex:
  "x \<in> set (independent_pdevs xs) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> lex x 0) \<Longrightarrow>
  (\<And>x. x \<in> set xs \<Longrightarrow> x \<noteq> 0) \<Longrightarrow> Counterclockwise_2D_Arbitrary.lex x 0"
proof (induction xs arbitrary: x rule: independent_pdevs.induct )
  case 1 thus ?case by simp
next
  case (2 y ys)
  from 2 have "y \<noteq> 0" by auto
  from 2(2)
  have "x \<in> set (independent_pdevs (filter (Not \<circ> coll 0 y) ys)) \<or>
    x = y + sum_list (filter (coll 0 y) ys)"
    by (auto simp: Let_def split: if_split_asm)
  thus ?case
  proof
    assume "x \<in> set (independent_pdevs (filter (Not \<circ> coll 0 y) ys))"
    from 2(1)[OF refl prod.collapse refl, simplified, OF this 2(3,4)]
    show ?case by simp
  next
    assume "x = y + sum_list (filter (coll 0 y) ys)"
    also have "lex \<dots> 0"
      by (force intro: nlex_add nlex_sum simp: sum_list_sum_nth
        dest: nth_mem intro: 2(3))
    finally show ?case .
  qed
qed

lemma
  pdevs_val_independent_pdevs2:
  assumes "e \<in> UNIV \<rightarrow> I"
  shows "\<exists>e'. e' \<in> UNIV \<rightarrow> I \<and>
    pdevs_val e (pdevs_of_list (independent_pdevs xs)) = pdevs_val e' (pdevs_of_list xs)"
  using assms
proof (induct xs arbitrary: e rule: independent_pdevs.induct)
  case 1 thus ?case by force
next
  case (2 x xs)
  let ?coll = "(filter (coll 0 x) (x#xs))"
  let ?ncoll = "(filter (Not o coll 0 x) (x#xs))"
  let ?e0 = "if sum_list ?coll = 0 then e else e \<circ> (+) (Suc 0)"
  have "pdevs_val e (pdevs_of_list (independent_pdevs (x#xs))) =
    e 0 *\<^sub>R (sum_list ?coll) + pdevs_val ?e0 (pdevs_of_list (independent_pdevs ?ncoll))"
    (is "_ = ?vc + ?vnc")
    by (simp add: Let_def)
  also
  have e_split: "(\<lambda>_. e 0) \<in> UNIV \<rightarrow> I" "?e0 \<in> UNIV \<rightarrow> I"
    using 2(2) by auto
  from 2(1)[OF refl prod.collapse refl e_split(2)]
  obtain e' where e': "e' \<in> UNIV \<rightarrow> I" and "?vnc = pdevs_val e' (pdevs_of_list ?ncoll)"
    by (auto simp add: o_def)
  note this(2)
  also
  have "?vc = pdevs_val (\<lambda>_. e 0) (pdevs_of_list ?coll)"
    by (simp add: pdevs_val_const_pdevs_of_list)
  also
  from pdevs_val_pdevs_of_list_append[OF e_split(1) e'] obtain e'' where
    e'': "e'' \<in> UNIV \<rightarrow> I"
    and "pdevs_val (\<lambda>_. e 0) (pdevs_of_list ?coll) + pdevs_val e' (pdevs_of_list ?ncoll) =
      pdevs_val e'' (pdevs_of_list (?coll @ ?ncoll))"
    by metis
  note this(2)
  also
  from pdevs_val_perm[OF partition_permI e'', of "coll 0 x" "x#xs"]
  obtain e''' where e''': "e''' \<in> UNIV \<rightarrow> I"
    and "\<dots> = pdevs_val e''' (pdevs_of_list (x # xs))"
    by metis
  note this(2)
  finally show ?case using e''' by auto
qed

lemma list_all_filter: "list_all p (filter p xs)"
  by (induct xs) auto

lemma pdevs_val_independent_pdevs:
  assumes "list_all (\<lambda>x. lex x 0) xs"
  assumes "list_all (\<lambda>x. x \<noteq> 0) xs"
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "\<exists>e'. e' \<in> UNIV \<rightarrow> {-1 .. 1} \<and> pdevs_val e (pdevs_of_list xs) =
    pdevs_val e' (pdevs_of_list (independent_pdevs xs))"
  using assms(1,2,3)
proof (induct xs arbitrary: e rule: independent_pdevs.induct)
  case 1 thus ?case by force
next
  case (2 x xs)

  let ?coll = "(filter (coll 0 x) (x#xs))"
  let ?ncoll = "(filter (Not o coll 0 x) xs)"

  from 2 have "x \<noteq> 0" by simp

  from pdevs_val_partition[OF 2(4), of "x#xs" "coll 0 x"]
  obtain f g where part: "pdevs_val e (pdevs_of_list (x # xs)) =
      pdevs_val f (pdevs_of_list ?coll) +
      pdevs_val g (pdevs_of_list (filter (Not o coll 0 x) (x#xs)))"
    and f: "f \<in> UNIV \<rightarrow> {-1 .. 1}" and g: "g \<in> UNIV \<rightarrow> {-1 .. 1}"
    by blast
  note part
  also

  have "list_all (\<lambda>x. lex x 0) (filter (coll 0 x) (x#xs))"
    using 2(2) by (auto simp: inner_prod_def list_all_iff)
  from pdevs_val_coll[OF list_all_filter this \<open>x \<noteq> 0\<close> f]
  obtain f' where "pdevs_val f (pdevs_of_list ?coll) = f' *\<^sub>R sum_list (filter (coll 0 x) (x#xs))"
    and f': "f' \<in> {-1 .. 1}"
    by blast
  note this(1)
  also

  have "filter (Not o coll 0 x) (x#xs) = ?ncoll"
    by simp
  also

  from 2(2) have "list_all (\<lambda>x. lex x 0) ?ncoll" "list_all (\<lambda>x. x \<noteq> 0) ?ncoll"
    by (auto simp: list_all_iff)
  from 2(1)[OF refl partition_filter_conv[symmetric] refl this g]
  obtain g'
  where "pdevs_val g (pdevs_of_list ?ncoll) =
      pdevs_val g' (pdevs_of_list (independent_pdevs ?ncoll))"
    and g': "g' \<in> UNIV \<rightarrow> {-1 .. 1}"
    by metis
  note this(1)
  also

  define h where "h = (if sum_list ?coll \<noteq> 0 then rec_nat f' (\<lambda>i _. g' i) else g')"
  have "f' *\<^sub>R sum_list ?coll + pdevs_val g' (pdevs_of_list (independent_pdevs ?ncoll))
      = pdevs_val h (pdevs_of_list (independent_pdevs (x#xs)))"
    by (simp add: h_def o_def Let_def)

  finally
  have "pdevs_val e (pdevs_of_list (x # xs)) =
      pdevs_val h (pdevs_of_list (independent_pdevs (x # xs)))" .

  moreover have "h \<in> UNIV \<rightarrow> {-1 .. 1}"
  proof
    fix i show "h i \<in> {-1 .. 1}"
      using f' g'
      by (cases i) (auto simp: h_def)
  qed

  ultimately show ?case by blast
qed

lemma
  pdevs_val_independent_pdevs_strict:
  assumes "list_all (\<lambda>x. lex x 0) xs"
  assumes "list_all (\<lambda>x. x \<noteq> 0) xs"
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  shows "\<exists>e'. e' \<in> UNIV \<rightarrow> {-1 <..< 1} \<and> pdevs_val e (pdevs_of_list xs) =
    pdevs_val e' (pdevs_of_list (independent_pdevs xs))"
  using assms(1,2,3)
proof (induct xs arbitrary: e rule: independent_pdevs.induct)
  case 1 thus ?case by force
next
  case (2 x xs)

  let ?coll = "(filter (coll 0 x) (x#xs))"
  let ?ncoll = "(filter (Not o coll 0 x) xs)"

  from 2 have "x \<noteq> 0" by simp

  from pdevs_val_partition[OF 2(4), of "x#xs" "coll 0 x"]
  obtain f g
  where part: "pdevs_val e (pdevs_of_list (x # xs)) =
      pdevs_val f (pdevs_of_list ?coll) +
      pdevs_val g (pdevs_of_list (filter (Not o coll 0 x) (x#xs)))"
    and f: "f \<in> UNIV \<rightarrow> {-1 <..< 1}" and g: "g \<in> UNIV \<rightarrow> {-1 <..< 1}"
    by blast
  note part
  also

  have "list_all (\<lambda>x. lex x 0) (filter (coll 0 x) (x#xs))"
    using 2(2) by (auto simp: inner_prod_def list_all_iff)
  from pdevs_val_coll_strict[OF list_all_filter this \<open>x \<noteq> 0\<close> f]
  obtain f' where "pdevs_val f (pdevs_of_list ?coll) = f' *\<^sub>R sum_list (filter (coll 0 x) (x#xs))"
    and f': "f' \<in> {-1 <..< 1}"
    by blast
  note this(1)
  also

  have "filter (Not o coll 0 x) (x#xs) = ?ncoll"
    by simp
  also

  from 2(2) have "list_all (\<lambda>x. lex x 0) ?ncoll" "list_all (\<lambda>x. x \<noteq> 0) ?ncoll"
    by (auto simp: list_all_iff)
  from 2(1)[OF refl partition_filter_conv[symmetric] refl this g]
  obtain g'
  where "pdevs_val g (pdevs_of_list ?ncoll) =
      pdevs_val g' (pdevs_of_list (independent_pdevs ?ncoll))"
    and g': "g' \<in> UNIV \<rightarrow> {-1 <..< 1}"
    by metis
  note this(1)
  also

  define h where "h = (if sum_list ?coll \<noteq> 0 then rec_nat f' (\<lambda>i _. g' i) else g')"
  have "f' *\<^sub>R sum_list ?coll + pdevs_val g' (pdevs_of_list (independent_pdevs ?ncoll))
      = pdevs_val h (pdevs_of_list (independent_pdevs (x#xs)))"
    by (simp add: h_def o_def Let_def)

  finally
  have "pdevs_val e (pdevs_of_list (x # xs)) =
      pdevs_val h (pdevs_of_list (independent_pdevs (x # xs)))" .

  moreover have "h \<in> UNIV \<rightarrow> {-1 <..< 1}"
  proof
    fix i show "h i \<in> {-1 <..< 1}"
      using f' g'
      by (cases i) (auto simp: h_def)
  qed

  ultimately show ?case by blast
qed

lemma sum_list_independent_pdevs: "sum_list (independent_pdevs xs) = sum_list xs"
proof (induct xs rule: independent_pdevs.induct)
  case (2 y ys)
  from 2[OF refl prod.collapse refl]
  show ?case
    using sum_list_partition[of "coll 0 y" ys, symmetric]
    by (auto simp: Let_def)
qed simp

lemma independent_pdevs_eq_Nil_iff:
  "list_all (\<lambda>x. lex x 0) xs \<Longrightarrow> list_all (\<lambda>x. x \<noteq> 0) xs \<Longrightarrow> independent_pdevs xs = [] \<longleftrightarrow> xs = []"
proof (induct xs)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  from Cons(2) have "list_all (\<lambda>x. lex x 0) (x # filter (coll 0 x) xs)"
    by (auto simp: list_all_iff)
  from sum_list_nlex_eq_zero_iff[OF this] Cons(3)
  show ?case
    by (auto simp: list_all_iff)
qed


subsection \<open>Independent Oriented Generators\<close>

definition "inl p = independent_pdevs (map snd (list_of_pdevs (nlex_pdevs p)))"

lemma distinct_inl[simp]: "distinct (inl (snd X))"
  by (auto simp: inl_def)

lemma in_set_inl_nonzero: "x \<in> set (inl xs) \<Longrightarrow> x \<noteq> 0"
  by (auto simp: inl_def in_set_independent_pdevs_nonzero)

lemma
  inl_ncoll: "y \<in> set (inl (snd X)) \<Longrightarrow> z \<in> set (inl (snd X)) \<Longrightarrow> y \<noteq> z \<Longrightarrow> \<not>coll 0 y z"
  unfolding inl_def
  by (rule independent_pdevs_pairwise_non_coll, assumption+)
    (auto simp: inl_def list_of_pdevs_nonzero)

lemma in_set_inl_lex: "x \<in> set (inl xs) \<Longrightarrow> lex x 0"
  by (auto simp: inl_def list_of_pdevs_def dest!: in_set_independent_pdevs_invariant_nlex
    split: if_split_asm)

interpretation ccw0: linorder_list "ccw 0" "set (inl (snd X))"
proof unfold_locales
  fix a b c
  show "a \<noteq> b \<Longrightarrow> ccw 0 a b \<or> ccw 0 b a"
    by (metis UNIV_I ccw_self(1) nondegenerate)
  assume a: "a \<in> set (inl (snd X))"
  show "ccw 0 a a"
    by simp
  assume b: "b \<in> set (inl (snd X))"
  show "ccw 0 a b \<Longrightarrow> ccw 0 b a \<Longrightarrow> a = b"
    by (metis ccw_self(1) in_set_inl_nonzero mem_Collect_eq not_ccw_eq a b)
  assume c: "c \<in> set (inl (snd X))"
  assume distinct: "a \<noteq> b" "b \<noteq> c" "a \<noteq> c"
  assume ab: "ccw 0 a b" and bc: "ccw 0 b c"
  show "ccw 0 a c"
    using a b c ab bc
  proof (cases "a = (0, 1)" "b = (0, 1)" "c = (0, 1)"
      rule: case_split[case_product case_split[case_product case_split]])
    assume nu: "a \<noteq> (0, 1)" "b \<noteq> (0, 1)" "c \<noteq> (0, 1)"
    have "distinct5 a b c (0, 1) 0" "in5 UNIV a b c (0, 1) 0"
      using a b c distinct nu by (simp_all add: in_set_inl_nonzero)
    moreover have "ccw 0 (0, 1) a" "ccw 0 (0, 1) b" "ccw 0 (0, 1) c"
      by (auto intro!: nlex_ccw_left in_set_inl_lex a b c)
    ultimately show ?thesis using ab bc
      by (rule ccw.transitive[where S=UNIV and s="(0, 1)"])
  next
    assume "a \<noteq> (0, 1)" "b = (0, 1)" "c \<noteq> (0, 1)"
    thus ?thesis
      using ccw_switch23 in_set_inl_lex inl_ncoll nlex_ccw_left a b ab
      by blast
  next
    assume "a \<noteq> (0, 1)" "b \<noteq> (0, 1)" "c = (0, 1)"
    thus ?thesis
      using ccw_switch23 in_set_inl_lex inl_ncoll nlex_ccw_left b c bc
      by blast
  qed (auto simp add: nlex_ccw_left in_set_inl_lex)
qed

lemma sorted_inl: "ccw.sortedP 0 (ccw.selsort 0 (inl (snd X)))"
  by (rule ccw0.sortedP_selsort) auto

lemma sorted_scaled_inl: "ccw.sortedP 0 (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X))))"
  using sorted_inl
  by (rule ccw_sorted_scaleR) simp

lemma distinct_selsort_inl: "distinct (ccw.selsort 0 (inl (snd X)))"
  by simp

lemma distinct_map_scaleRI:
  fixes xs::"'a::real_vector list"
  shows "distinct xs \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> distinct (map ((*\<^sub>R) c) xs)"
  by (induct xs) auto

lemma distinct_scaled_inl: "distinct (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X))))"
  using distinct_selsort_inl
  by (rule distinct_map_scaleRI) simp

lemma ccw'_sortedP_scaled_inl:
  "ccw'.sortedP 0 (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X))))"
  using ccw_sorted_implies_ccw'_sortedP
  by (rule ccw'_sorted_scaleR) (auto simp: sorted_inl inl_ncoll)

lemma pdevs_val_pdevs_of_list_inl2E:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  obtains e' where "pdevs_val e X = pdevs_val e' (pdevs_of_list (inl X))" "e' \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  let ?l = "map snd (list_of_pdevs (nlex_pdevs X))"
  have l: "list_all (\<lambda>x. Counterclockwise_2D_Arbitrary.lex x 0) ?l"
    "list_all (\<lambda>x. x \<noteq> 0) (map snd (list_of_pdevs (nlex_pdevs X)))"
    by (auto simp: list_all_iff list_of_pdevs_def)

  from pdevs_val_nlex_pdevs[OF assms(1)]
  obtain e' where "e' \<in> UNIV \<rightarrow> {-1 .. 1}" "pdevs_val e X = pdevs_val e' (nlex_pdevs X)"
    by auto
  note this(2)
  also from pdevs_val_of_list_of_pdevs2[OF \<open>e' \<in> _\<close>]
  obtain e'' where "e'' \<in> UNIV \<rightarrow> {-1 .. 1}" "\<dots> = pdevs_val e'' (pdevs_of_list ?l)"
    by metis
  note this(2)
  also from pdevs_val_independent_pdevs[OF l \<open>e'' \<in> _\<close>]
  obtain e'''
  where "e''' \<in> UNIV \<rightarrow> {-1 .. 1}"
    and "\<dots> = pdevs_val e''' (pdevs_of_list (independent_pdevs ?l))"
    by metis
  note this(2)
  also have "\<dots> = pdevs_val e''' (pdevs_of_list (inl X))"
    by (simp add: inl_def)
  finally have "pdevs_val e X = pdevs_val e''' (pdevs_of_list (inl X))" .
  thus thesis using \<open>e''' \<in> _\<close> ..
qed

lemma pdevs_val_pdevs_of_list_inlE:
  assumes "e \<in> UNIV \<rightarrow> I" "uminus ` I = I" "0 \<in> I"
  obtains e' where "pdevs_val e (pdevs_of_list (inl X)) = pdevs_val e' X" "e' \<in> UNIV \<rightarrow> I"
proof -
  let ?l = "map snd (list_of_pdevs (nlex_pdevs X))"
  have "pdevs_val e (pdevs_of_list (inl X)) = pdevs_val e (pdevs_of_list (independent_pdevs ?l))"
    by (simp add: inl_def)
  also
  from pdevs_val_independent_pdevs2[OF \<open>e \<in> _\<close>]
  obtain e'
  where "pdevs_val e (pdevs_of_list (independent_pdevs ?l)) = pdevs_val e' (pdevs_of_list ?l)"
    and "e' \<in> UNIV \<rightarrow> I"
    by auto
  note this(1)
  also
  from pdevs_val_of_list_of_pdevs[OF \<open>e' \<in> _\<close> \<open>0 \<in> I\<close>, of "nlex_pdevs X"]
  obtain e'' where "pdevs_val e' (pdevs_of_list ?l) = pdevs_val e'' (nlex_pdevs X)"
    and "e'' \<in> UNIV \<rightarrow> I"
    by metis
  note this(1)
  also
  from pdevs_val_nlex_pdevs2[OF \<open>e'' \<in> _\<close> \<open>_ = I\<close>]
  obtain e''' where "pdevs_val e'' (nlex_pdevs X) = pdevs_val e''' X" "e''' \<in> UNIV \<rightarrow> I"
    by metis
  note this(1)
  finally have "pdevs_val e (pdevs_of_list (inl X)) = pdevs_val e''' X" .
  thus ?thesis using \<open>e''' \<in> UNIV \<rightarrow> I\<close> ..
qed

lemma sum_list_nlex_eq_sum_list_inl:
  "sum_list (map snd (list_of_pdevs (nlex_pdevs X))) = sum_list (inl X)"
  by (auto simp: inl_def sum_list_list_of_pdevs sum_list_independent_pdevs)

lemma Affine_inl: "Affine (fst X, pdevs_of_list (inl (snd X))) = Affine X"
  by (auto simp: Affine_def valuate_def aform_val_def
    elim: pdevs_val_pdevs_of_list_inlE[of _ _ "snd X"] pdevs_val_pdevs_of_list_inl2E[of _ "snd X"])


subsection \<open>Half Segments\<close>

definition half_segments_of_aform::"point aform \<Rightarrow> (point*point) list"
  where "half_segments_of_aform X =
    (let
      x0 = lowest_vertex (fst X, nlex_pdevs (snd X))
    in
      polychain_of x0 (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X)))))"

lemma subsequent_half_segments:
  fixes X
  assumes "Suc i < length (half_segments_of_aform X)"
  shows "snd (half_segments_of_aform X ! i) = fst (half_segments_of_aform X ! Suc i)"
  using assms
  by (cases i) (auto simp: half_segments_of_aform_def Let_def polychain_of_subsequent_eq)

lemma polychain_half_segments_of_aform: "polychain (half_segments_of_aform X)"
  by (auto simp: subsequent_half_segments intro!: polychainI)

lemma fst_half_segments:
  "half_segments_of_aform X \<noteq> [] \<Longrightarrow>
    fst (half_segments_of_aform X ! 0) = lowest_vertex (fst X, nlex_pdevs (snd X))"
  by (auto simp: half_segments_of_aform_def Let_def o_def split_beta')

lemma nlex_half_segments_of_aform: "(a, b) \<in> set (half_segments_of_aform X) \<Longrightarrow> lex b a"
  by (auto simp: half_segments_of_aform_def prod_eq_iff lex_def
    dest!: in_set_polychain_ofD in_set_inl_lex)

lemma ccw_half_segments_of_aform_all:
  assumes cd: "(c, d) \<in> set (half_segments_of_aform X)"
  shows "list_all (\<lambda>(xi, xj). ccw xi xj c \<and> ccw xi xj d) (half_segments_of_aform X)"
proof -
  have
    "list_all (\<lambda>(xi, xj). ccw xi xj (fst (c, d)) \<and> ccw xi xj (snd (c, d)))
      (polychain_of (lowest_vertex (fst X, nlex_pdevs (snd X)))
        ((map ((*\<^sub>R) 2) (linorder_list0.selsort (ccw 0) (inl (snd X))))))"
    using ccw'_sortedP_scaled_inl cd[unfolded half_segments_of_aform_def Let_def]
    by (rule polychain_of_ccw_conjunction)
  thus ?thesis
    unfolding half_segments_of_aform_def[unfolded Let_def, symmetric] fst_conv snd_conv .
qed

lemma ccw_half_segments_of_aform:
  assumes ij: "(xi, xj) \<in> set (half_segments_of_aform X)"
  assumes c: "(c, d) \<in> set (half_segments_of_aform X)"
  shows "ccw xi xj c" "ccw xi xj d"
  using ccw_half_segments_of_aform_all[OF c] ij
  by (auto simp add: list_all_iff)

lemma half_segments_of_aform1:
  assumes ch: "x \<in> convex hull set (map fst (half_segments_of_aform X))"
  assumes ab: "(a, b) \<in> set (half_segments_of_aform X)"
  shows "ccw a b x"
  using finite_set _ ch
proof (rule ccw.convex_hull)
  fix c assume "c \<in> set (map fst (half_segments_of_aform X))"
  then obtain d where "(c, d) \<in> set (half_segments_of_aform X)" by auto
  with ab show "ccw a b c"
    by (rule ccw_half_segments_of_aform(1))
qed (insert ab, simp add: nlex_half_segments_of_aform)

lemma half_segments_of_aform2:
  assumes ch: "x \<in> convex hull set (map snd (half_segments_of_aform X))"
  assumes ab: "(a, b) \<in> set (half_segments_of_aform X)"
  shows "ccw a b x"
  using finite_set _ ch
proof (rule ccw.convex_hull)
  fix d assume "d \<in> set (map snd (half_segments_of_aform X))"
  then obtain c where "(c, d) \<in> set (half_segments_of_aform X)" by auto
  with ab show "ccw a b d"
    by (rule ccw_half_segments_of_aform(2))
qed (insert ab, simp add: nlex_half_segments_of_aform)

lemma
  in_set_half_segments_of_aform_aform_valE:
  assumes "(x2, y2) \<in> set (half_segments_of_aform X)"
  obtains e where "y2 = aform_val e X" "e \<in> UNIV \<rightarrow> {-1 .. 1}"
proof -
  from assms obtain d where
    "y2 = lowest_vertex (fst X, nlex_pdevs (snd X)) +
      sum_list (take (Suc d) (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X)))))"
    by (auto simp: half_segments_of_aform_def elim!: in_set_polychain_of_imp_sum_list)
  also have "lowest_vertex (fst X, nlex_pdevs (snd X)) =
      fst X - sum_list (map snd (list_of_pdevs (nlex_pdevs (snd X))))"
    by (simp add: lowest_vertex_def)
  also have "sum_list (map snd (list_of_pdevs (nlex_pdevs (snd X)))) =
      pdevs_val (\<lambda>_. 1) (nlex_pdevs (snd X))"
    by (auto simp: pdevs_val_sum_list)
  also

  have "sum_list (take (Suc d) (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X))))) =
      pdevs_val (\<lambda>i. if i \<le> d then 2 else 0) (pdevs_of_list (ccw.selsort 0 (inl (snd X))))"
    (is "_ = pdevs_val ?e _")
    by (subst sum_list_take_pdevs_val_eq)
      (auto simp: pdevs_val_sum if_distrib pdevs_apply_pdevs_of_list
        degree_pdevs_of_list_scaleR intro!: sum.cong )
  also
  obtain e'' where "\<dots> = pdevs_val e'' (pdevs_of_list (inl (snd X)))" "e'' \<in> UNIV \<rightarrow> {0..2}"
    by (auto intro: pdevs_val_selsort_ccw2[of "inl (snd X)" ?e "{0 .. 2}"])
  note this(1)
  also note inl_def
  also
  let ?l = "map snd (list_of_pdevs (nlex_pdevs (snd X)))"
  from pdevs_val_independent_pdevs2[OF \<open>e'' \<in> _\<close>]
  obtain e'''
  where "pdevs_val e'' (pdevs_of_list (independent_pdevs ?l)) = pdevs_val e''' (pdevs_of_list ?l)"
    and "e''' \<in> UNIV \<rightarrow> {0..2}"
    by auto
  note this(1)
  also
  have "0 \<in> {0 .. 2::real}" by simp
  from pdevs_val_of_list_of_pdevs[OF \<open>e''' \<in> _\<close> this, of "nlex_pdevs (snd X)"]
  obtain e'''' where "pdevs_val e''' (pdevs_of_list ?l) = pdevs_val e'''' (nlex_pdevs (snd X))"
    and "e'''' \<in> UNIV \<rightarrow> {0 .. 2}"
    by metis
  note this(1)
  finally have
    "y2 = fst X + (pdevs_val e'''' (nlex_pdevs (snd X)) - pdevs_val (\<lambda>_. 1) (nlex_pdevs (snd X)))"
    by simp
  also have "pdevs_val e'''' (nlex_pdevs (snd X)) - pdevs_val (\<lambda>_. 1) (nlex_pdevs (snd X)) =
      pdevs_val (\<lambda>i. e'''' i - 1) (nlex_pdevs (snd X))"
    by (simp add: pdevs_val_minus)
  also
  have "(\<lambda>i. e'''' i - 1) \<in> UNIV \<rightarrow> {-1 .. 1}" using \<open>e'''' \<in> _\<close> by auto
  from pdevs_val_nlex_pdevs2[OF this]
  obtain f where "f \<in> UNIV \<rightarrow>  {-1 .. 1}"
    and "pdevs_val (\<lambda>i. e'''' i - 1) (nlex_pdevs (snd X)) = pdevs_val f (snd X)"
    by auto
  note this(2)
  finally have "y2 = aform_val f X" by (simp add: aform_val_def)
  thus ?thesis using \<open>f \<in> _\<close> ..
qed

lemma fst_hd_half_segments_of_aform:
  assumes "half_segments_of_aform X \<noteq> []"
  shows "fst (hd (half_segments_of_aform X)) = lowest_vertex (fst X, (nlex_pdevs (snd X)))"
  using assms
  by (auto simp: half_segments_of_aform_def Let_def fst_hd_polychain_of)

lemma
  "linorder_list0.sortedP (ccw' (lowest_vertex (fst X, nlex_pdevs (snd X))))
    (map snd (half_segments_of_aform X))"
  (is "linorder_list0.sortedP (ccw' ?x0) ?ms")
  unfolding half_segments_of_aform_def Let_def
  by (rule ccw'_sortedP_polychain_of_snd) (rule ccw'_sortedP_scaled_inl)

lemma rev_zip: "length xs = length ys \<Longrightarrow> rev (zip xs ys) = zip (rev xs) (rev ys)"
  by (induct xs ys rule: list_induct2) auto

lemma zip_upt_self_aux: "zip [0..<length xs] xs = map (\<lambda>i. (i, xs ! i)) [0..<length xs]"
  by (auto intro!: nth_equalityI)

lemma half_segments_of_aform_strict:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  assumes "seg \<in> set (half_segments_of_aform X)"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  shows "ccw' (fst seg) (snd seg) (aform_val e X)"
  using assms unfolding half_segments_of_aform_def Let_def
proof -
  have len: "length (map ((*\<^sub>R) 2) (linorder_list0.selsort (ccw 0) (inl (snd X)))) \<noteq> 1"
    using assms by (auto simp: half_segments_of_aform_def)

  have "aform_val e X = fst X + pdevs_val e (snd X)"
    by (simp add: aform_val_def)
  also
  obtain e' where "e' \<in> UNIV \<rightarrow> {-1 <..< 1}"
    "pdevs_val e (snd X) = pdevs_val e' (nlex_pdevs (snd X))"
    using pdevs_val_nlex_pdevs[OF \<open>e \<in> _\<close>]
    by auto
  note this(2)
  also obtain e'' where "e'' \<in> UNIV \<rightarrow> {-1 <..< 1}"
    "\<dots> = pdevs_val e'' (pdevs_of_list (map snd (list_of_pdevs (nlex_pdevs (snd X)))))"
    by (metis pdevs_val_of_list_of_pdevs2[OF \<open>e' \<in> _\<close>])
  note this(2)
  also
  obtain e''' where "e''' \<in> UNIV \<rightarrow> {-1 <..< 1}" "\<dots> = pdevs_val e''' (pdevs_of_list (inl (snd X)))"
    unfolding inl_def
    using
      pdevs_val_independent_pdevs_strict[OF list_all_list_of_pdevsI,
        OF lex_nlex_pdevs list_of_pdevs_all_nonzero \<open>e'' \<in> _\<close>]
    by metis
  note this(2)
  also
  from pdevs_val_selsort_ccw[OF distinct_inl \<open>e''' \<in> _\<close>]
  obtain f where "f \<in> UNIV \<rightarrow> {-1 <..< 1}"
    "\<dots> = pdevs_val f (pdevs_of_list (linorder_list0.selsort (ccw 0) (inl (snd X))))"
    (is "_ = pdevs_val _ (pdevs_of_list ?sl)")
    by metis
  note this(2)
  also have "\<dots> = pdevs_val (\<lambda>i. f i + 1) (pdevs_of_list ?sl) +
      lowest_vertex (fst X, nlex_pdevs (snd X)) - fst X"
  proof -
    have "sum_list (dense_list_of_pdevs (nlex_pdevs (snd X))) =
        sum_list (dense_list_of_pdevs (pdevs_of_list (ccw.selsort 0 (inl (snd X)))))"
      by (subst dense_list_of_pdevs_pdevs_of_list)
        (auto simp: in_set_independent_pdevs_nonzero dense_list_of_pdevs_pdevs_of_list inl_def
          sum_list_distinct_selsort sum_list_independent_pdevs sum_list_list_of_pdevs)
    thus ?thesis
      by (auto simp add: pdevs_val_add lowest_vertex_def algebra_simps pdevs_val_sum_list
        sum_list_list_of_pdevs in_set_inl_nonzero dense_list_of_pdevs_pdevs_of_list)
  qed
  also have "pdevs_val (\<lambda>i. f i + 1) (pdevs_of_list ?sl) =
      pdevs_val (\<lambda>i. 1/2 * (f i + 1)) (pdevs_of_list (map ((*\<^sub>R) 2) ?sl))"
    (is "_ = pdevs_val ?f' (pdevs_of_list ?ssl)")
    by (subst pdevs_val_cmul) (simp add: pdevs_of_list_map_scaleR)
  also
  have "distinct ?ssl" "?f' \<in> UNIV \<rightarrow> {0<..<1}" using \<open>f \<in> _\<close>
    by (auto simp: distinct_map_scaleRI Pi_iff algebra_simps real_0_less_add_iff)
  from pdevs_of_list_sum[OF this]
  obtain g where "g \<in> UNIV \<rightarrow> {0<..<1}"
    "pdevs_val ?f' (pdevs_of_list ?ssl) = (\<Sum>P\<in>set ?ssl. g P *\<^sub>R P)"
    by blast
  note this(2)
  finally
  have "aform_val e X = lowest_vertex (fst X, nlex_pdevs (snd X)) + (\<Sum>P\<in>set ?ssl. g P *\<^sub>R P)"
    by simp
  also
  have "ccw' (fst seg) (snd seg) \<dots>"
    using \<open>g \<in> _\<close> _ len \<open>seg \<in> _\<close>[unfolded half_segments_of_aform_def Let_def]
    by (rule in_polychain_of_ccw) (simp add: ccw'_sortedP_scaled_inl)
  finally show ?thesis .
qed

lemma half_segments_of_aform_strict_all:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  shows "list_all (\<lambda>seg. ccw' (fst seg) (snd seg) (aform_val e X)) (half_segments_of_aform X)"
  using assms
  by (auto intro!: half_segments_of_aform_strict simp: list_all_iff)

lemma list_allD: "list_all P xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x"
  by (auto simp: list_all_iff)

lemma minus_one_less_multI:
  fixes e x::real
  shows "- 1 \<le> e \<Longrightarrow> 0 < x \<Longrightarrow> x < 1 \<Longrightarrow> - 1 < e * x"
  by (metis abs_add_one_gt_zero abs_real_def le_less_trans less_not_sym mult_less_0_iff
    mult_less_cancel_left1 real_0_less_add_iff)

lemma less_one_multI:
  fixes e x::real
  shows "e \<le> 1 \<Longrightarrow> 0 < x \<Longrightarrow> x < 1 \<Longrightarrow> e * x < 1"
  by (metis (erased, hide_lams) less_eq_real_def monoid_mult_class.mult.left_neutral
    mult_strict_mono zero_less_one)

lemma ccw_half_segments_of_aform_strictI:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  assumes "(s1, s2) \<in> set (half_segments_of_aform X)"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  assumes "x = (aform_val e X)"
  shows "ccw' s1 s2 x"
  using half_segments_of_aform_strict[OF assms(1-3)] assms(4) by simp

lemma
  ccw'_sortedP_subsequent:
  assumes "Suc i < length xs" "ccw'.sortedP 0 (map dirvec xs)" "fst (xs ! Suc i) = snd (xs ! i)"
  shows "ccw' (fst (xs ! i)) (snd (xs ! i)) (snd (xs ! Suc i))"
  using assms
proof (induct xs arbitrary: i)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  thus ?case
    by (auto simp: nth_Cons dirvec_minus split: nat.split elim!: ccw'.sortedP_Cons)
      (metis (no_types, lifting) ccw'.renormalize length_greater_0_conv nth_mem prod.case_eq_if)
qed

lemma ccw'_sortedP_uminus: "ccw'.sortedP 0 xs \<Longrightarrow> ccw'.sortedP 0 (map uminus xs)"
  by (induct xs) (auto intro!: ccw'.sortedP.Cons elim!: ccw'.sortedP_Cons simp del: uminus_Pair)

lemma subsequent_half_segments_ccw:
  fixes X
  assumes "Suc i < length (half_segments_of_aform X)"
  shows "ccw' (fst (half_segments_of_aform X ! i)) (snd (half_segments_of_aform X ! i))
    (snd (half_segments_of_aform X ! Suc i))"
  using assms
  by (intro ccw'_sortedP_subsequent )
    (auto simp: subsequent_half_segments half_segments_of_aform_def
      sorted_inl polychain_of_subsequent_eq intro!: ccw_sorted_implies_ccw'_sortedP[OF inl_ncoll]
      ccw'_sorted_scaleR)

lemma convex_polychain_half_segments_of_aform: "convex_polychain (half_segments_of_aform X)"
proof cases
  assume "length (half_segments_of_aform X) = 1"
  thus ?thesis
    by (auto simp: length_Suc_conv convex_polychain_def polychain_def)
next
  assume len: "length (half_segments_of_aform X) \<noteq> 1"
  show ?thesis
    by (rule convex_polychainI)
      (simp_all add: polychain_half_segments_of_aform subsequent_half_segments_ccw
        ccw'_def[symmetric])
qed

lemma hd_distinct_neq_last: "distinct xs \<Longrightarrow> length xs > 1 \<Longrightarrow> hd xs \<noteq> last xs"
  by (metis One_nat_def add_Suc_right distinct.simps(2) last.simps last_in_set less_irrefl
    list.exhaust list.sel(1) list.size(3) list.size(4) add.right_neutral nat_neq_iff not_less0)

lemma ccw_hd_last_half_segments_dirvec:
  assumes "length (half_segments_of_aform X) > 1"
  shows "ccw' 0 (dirvec (hd (half_segments_of_aform X))) (dirvec (last (half_segments_of_aform X)))"
proof -
  let ?i = "ccw.selsort 0 (inl (snd X))"
  let ?s = "map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X)))"
  from assms have l: "1 < length (inl (snd X))" "inl (snd X) \<noteq> []"
    using assms by (auto simp add: half_segments_of_aform_def)
  hence "hd ?i \<in> set ?i" "last ?i \<in> set ?i"
    by (auto intro!: hd_in_set last_in_set simp del: ccw.set_selsort)
  hence "\<not>coll 0 (hd ?i) (last ?i)" using l
    by (intro inl_ncoll[of _ X]) (auto simp: hd_distinct_neq_last)
  hence "\<not>coll 0 (hd ?s) (last ?s)" using l
    by (auto simp: hd_map last_map)
  hence "ccw' 0 (hd (map ((*\<^sub>R) 2) (linorder_list0.selsort (ccw 0) (inl (snd X)))))
     (last (map ((*\<^sub>R) 2) (linorder_list0.selsort (ccw 0) (inl (snd X)))))"
    using assms
    by (auto simp add: half_segments_of_aform_def
      intro!: sorted_inl ccw_sorted_scaleR ccw.hd_last_sorted ccw_ncoll_imp_ccw)
  with assms show ?thesis
    by (auto simp add: half_segments_of_aform_def Let_def
        dirvec_hd_polychain_of dirvec_last_polychain_of length_greater_0_conv[symmetric]
      simp del: polychain_of.simps length_greater_0_conv
      split: if_split_asm)
qed

lemma map_fst_half_segments_aux_eq: "[] \<noteq> half_segments_of_aform X \<Longrightarrow>
    map fst (half_segments_of_aform X) =
      fst (hd (half_segments_of_aform X))#butlast (map snd (half_segments_of_aform X))"
  by (rule nth_equalityI)
    (auto simp: nth_Cons hd_conv_nth nth_butlast subsequent_half_segments split: nat.split)

lemma le_less_Suc_eq: "x - Suc 0 \<le> (i::nat) \<Longrightarrow> i < x \<Longrightarrow> x - Suc 0 = i"
  by simp

lemma map_snd_half_segments_aux_eq: "half_segments_of_aform X \<noteq> [] \<Longrightarrow>
    map snd (half_segments_of_aform X) =
      tl (map fst (half_segments_of_aform X)) @ [snd (last (half_segments_of_aform X))]"
  by (rule nth_equalityI)
    (auto simp: nth_Cons hd_conv_nth nth_append nth_tl subsequent_half_segments
      not_less last_conv_nth algebra_simps dest!: le_less_Suc_eq
    split: nat.split)

lemma ccw'_sortedP_snd_half_segments_of_aform:
  "ccw'.sortedP (lowest_vertex (fst X, nlex_pdevs (snd X))) (map snd (half_segments_of_aform X))"
  by (auto simp: half_segments_of_aform_def Let_def
    intro!: ccw'.sortedP.Cons ccw'_sortedP_polychain_of_snd ccw'_sortedP_scaled_inl)

lemma
  lex_half_segments_lowest_vertex:
  assumes "(c, d) \<in> set (half_segments_of_aform X)"
  shows "lex d (lowest_vertex (fst X, nlex_pdevs (snd X)))"
  unfolding half_segments_of_aform_def Let_def
  by (rule lex_polychain_of_center[OF assms[unfolded half_segments_of_aform_def Let_def],
      unfolded snd_conv])
    (auto simp: list_all_iff lex_def dest!: in_set_inl_lex)

lemma
  lex_half_segments_lowest_vertex':
  assumes "d \<in> set (map snd (half_segments_of_aform X))"
  shows "lex d (lowest_vertex (fst X, nlex_pdevs (snd X)))"
  using assms
  by (auto intro: lex_half_segments_lowest_vertex)

lemma
  lex_half_segments_last:
  assumes "(c, d) \<in> set (half_segments_of_aform X)"
  shows "lex (snd (last (half_segments_of_aform X))) d"
  using assms
  unfolding half_segments_of_aform_def Let_def
  by (rule lex_polychain_of_last) (auto simp: list_all_iff lex_def dest!: in_set_inl_lex)

lemma
  lex_half_segments_last':
  assumes "d \<in> set (map snd (half_segments_of_aform X))"
  shows "lex (snd (last (half_segments_of_aform X))) d"
  using assms
  by (auto intro: lex_half_segments_last)

lemma
  ccw'_half_segments_lowest_last:
  assumes set_butlast: "(c, d) \<in> set (butlast (half_segments_of_aform X))"
  assumes ne: "inl (snd X) \<noteq> []"
  shows "ccw' (lowest_vertex (fst X, nlex_pdevs (snd X))) d (snd (last (half_segments_of_aform X)))"
  using set_butlast
  unfolding half_segments_of_aform_def Let_def
  by (rule ccw'_polychain_of_sorted_center_last) (auto simp: ne ccw'_sortedP_scaled_inl)

lemma distinct_fst_half_segments:
  "distinct (map fst (half_segments_of_aform X))"
  by (auto simp: half_segments_of_aform_def list_all_iff lex_scale1_zero
    simp del: scaleR_Pair
    intro!: distinct_fst_polychain_of
    dest: in_set_inl_nonzero in_set_inl_lex)

lemma distinct_snd_half_segments:
  "distinct (map snd (half_segments_of_aform X))"
  by (auto simp: half_segments_of_aform_def list_all_iff lex_scale1_zero
    simp del: scaleR_Pair
    intro!: distinct_snd_polychain_of
    dest: in_set_inl_nonzero in_set_inl_lex)


subsection \<open>Mirror\<close>

definition "mirror_point x y = 2 *\<^sub>R x - y"

lemma ccw'_mirror_point3[simp]:
  "ccw' (mirror_point x y) (mirror_point x z) (mirror_point x w) \<longleftrightarrow> ccw' y z w "
  by (auto simp: mirror_point_def det3_def' ccw'_def algebra_simps)

lemma mirror_point_self_inverse[simp]:
  fixes x::"'a::real_vector"
  shows "mirror_point p (mirror_point p x) = x"
  by (auto simp: mirror_point_def scaleR_2)

lemma mirror_half_segments_of_aform:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  shows "list_all (\<lambda>seg. ccw' (fst seg) (snd seg) (aform_val e X))
      (map (pairself (mirror_point (fst X))) (half_segments_of_aform X))"
  unfolding list_all_length
proof safe
  let ?m = "map (pairself (mirror_point (fst X))) (half_segments_of_aform X)"
  fix n assume "n < length ?m"
  hence "ccw' (fst (half_segments_of_aform X ! n)) (snd (half_segments_of_aform X ! n))
      (aform_val (- e) X)"
    using assms
    by (auto dest!: nth_mem intro!: half_segments_of_aform_strict)
  also have "aform_val (-e) X = 2 *\<^sub>R fst X - aform_val e X"
    by (auto simp: aform_val_def pdevs_val_sum algebra_simps scaleR_2 sum_negf)
  finally have le:
    "ccw' (fst (half_segments_of_aform X ! n)) (snd (half_segments_of_aform X ! n))
      (2 *\<^sub>R fst X - aform_val e X)"
    .

  have eq: "(map (pairself (mirror_point (fst X))) (half_segments_of_aform X) ! n) =
    (2 *\<^sub>R fst X - fst ((half_segments_of_aform X) ! n),
     2 *\<^sub>R fst X - snd ((half_segments_of_aform X) ! n))"
    using \<open>n < length ?m\<close>
    by (cases "half_segments_of_aform X ! n") (auto simp add: mirror_point_def)
  show "ccw' (fst (?m ! n)) (snd (?m ! n)) (aform_val e X)"
    using le
    unfolding eq
    by (auto simp: algebra_simps ccw'_def det3_def')
qed

lemma last_half_segments:
  assumes "half_segments_of_aform X \<noteq> []"
  shows "snd (last (half_segments_of_aform X)) =
    mirror_point (fst X) (lowest_vertex (fst X, nlex_pdevs (snd X)))"
  using assms
  by (auto simp add: half_segments_of_aform_def Let_def lowest_vertex_def mirror_point_def scaleR_2
    scaleR_sum_list[symmetric] last_polychain_of sum_list_distinct_selsort inl_def
    sum_list_independent_pdevs sum_list_list_of_pdevs)

lemma convex_polychain_map_mirror:
  assumes "convex_polychain hs"
  shows "convex_polychain (map (pairself (mirror_point x)) hs)"
proof (rule convex_polychainI)
qed (insert assms, auto simp: convex_polychain_def polychain_map_pairself pairself_apply
  mirror_point_def det3_def' algebra_simps)

lemma ccw'_mirror_point0:
  "ccw' (mirror_point x y) z w \<longleftrightarrow> ccw' y (mirror_point x z) (mirror_point x w)"
  by (metis ccw'_mirror_point3 mirror_point_self_inverse)

lemma ccw'_sortedP_mirror:
  "ccw'.sortedP x0 (map (mirror_point p0) xs) \<longleftrightarrow> ccw'.sortedP (mirror_point p0 x0) xs"
  by (induct xs)
    (simp_all add: linorder_list0.sortedP.Nil linorder_list0.sortedP_Cons_iff ccw'_mirror_point0)

lemma ccw'_sortedP_mirror2:
  "ccw'.sortedP (mirror_point p0 x0) (map (mirror_point p0) xs) \<longleftrightarrow> ccw'.sortedP x0 xs"
  using ccw'_sortedP_mirror[of "mirror_point p0 x0" p0 xs]
  by simp

lemma map_mirror_o_snd_polychain_of_eq: "map (mirror_point x0 \<circ> snd) (polychain_of y xs) =
  map snd (polychain_of (mirror_point x0 y) (map uminus xs))"
  by (induct xs arbitrary: x0 y) (auto simp: mirror_point_def o_def algebra_simps)

lemma lowest_vertex_eq_mirror_last:
  "half_segments_of_aform X \<noteq> [] \<Longrightarrow>
    (lowest_vertex (fst X, nlex_pdevs (snd X))) =
    mirror_point (fst X) (snd (last (half_segments_of_aform X)))"
  using last_half_segments[of X] by simp

lemma snd_last: "xs \<noteq> [] \<Longrightarrow> snd (last xs) = last (map snd xs)"
  by (induct xs) auto

lemma mirror_point_snd_last_eq_lowest:
  "half_segments_of_aform X \<noteq> [] \<Longrightarrow>
    mirror_point (fst X) (last (map snd (half_segments_of_aform X))) =
      lowest_vertex (fst X, nlex_pdevs (snd X))"
  by (simp add: lowest_vertex_eq_mirror_last snd_last)

lemma lex_mirror_point: "lex (mirror_point x0 a) (mirror_point x0 b) \<Longrightarrow> lex b a"
  by (auto simp: mirror_point_def lex_def)

lemma ccw'_mirror_point:
  "ccw' (mirror_point x0 a) (mirror_point x0 b)  (mirror_point x0 c) \<Longrightarrow> ccw' a b c"
  by (auto simp: mirror_point_def)

lemma inj_mirror_point: "inj (mirror_point (x::'a::real_vector))"
  by (auto simp: mirror_point_def inj_on_def algebra_simps)

lemma
  distinct_map_mirror_point_eq:
  "distinct (map (mirror_point (x::'a::real_vector)) xs) = distinct xs"
  by (auto simp: distinct_map intro!: subset_inj_on[OF inj_mirror_point])

lemma eq_self_mirror_iff: fixes x::"'a::real_vector" shows "x = mirror_point y x \<longleftrightarrow> x = y"
  by (auto simp: mirror_point_def algebra_simps scaleR_2[symmetric])


subsection \<open>Full Segments\<close>

definition segments_of_aform::"point aform \<Rightarrow> (point * point) list"
  where "segments_of_aform X =
    (let hs = half_segments_of_aform X in hs @ map (pairself (mirror_point (fst X))) hs)"

lemma segments_of_aform_strict:
  assumes "e \<in> UNIV \<rightarrow> {-1 <..< 1}"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  shows "list_all (\<lambda>seg. ccw' (fst seg) (snd seg) (aform_val e X)) (segments_of_aform X)"
  using assms
  by (auto simp: segments_of_aform_def Let_def mirror_half_segments_of_aform
    half_segments_of_aform_strict_all)
  

lemma mirror_point_aform_val[simp]: "mirror_point (fst X) (aform_val e X) = aform_val (- e) X"
  by (auto simp: mirror_point_def aform_val_def pdevs_val_sum algebra_simps scaleR_2 sum_negf)

lemma
  in_set_segments_of_aform_aform_valE:
  assumes "(x2, y2) \<in> set (segments_of_aform X)"
  obtains e where "y2 = aform_val e X" "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  using assms
proof (auto simp: segments_of_aform_def Let_def)
  assume "(x2, y2) \<in> set (half_segments_of_aform X)"
  from in_set_half_segments_of_aform_aform_valE[OF this]
  obtain e where "y2 = aform_val e X" "e \<in> UNIV \<rightarrow> {- 1..1}" by auto
  thus ?thesis ..
next
  fix a b aa ba
  assume "((a, b), aa, ba) \<in> set (half_segments_of_aform X)"
  from in_set_half_segments_of_aform_aform_valE[OF this]
  obtain e where e: "(aa, ba) = aform_val e X" "e \<in> UNIV \<rightarrow> {- 1..1}" by auto
  assume "y2 = mirror_point (fst X) (aa, ba)"
  hence "y2 = aform_val (-e) X" "(-e) \<in> UNIV \<rightarrow> {-1 .. 1}" using e by auto
  thus ?thesis ..
qed

lemma
  last_half_segments_eq_mirror_hd:
  assumes "half_segments_of_aform X \<noteq> []"
  shows "snd (last (half_segments_of_aform X)) = mirror_point (fst X) (fst (hd (half_segments_of_aform X)))"
  by (simp add: last_half_segments assms fst_hd_half_segments_of_aform)

lemma polychain_segments_of_aform: "polychain (segments_of_aform X)"
  by (auto simp: segments_of_aform_def Let_def polychain_half_segments_of_aform
    polychain_map_pairself last_half_segments_eq_mirror_hd hd_map pairself_apply
    intro!: polychain_appendI)

lemma segments_of_aform_closed:
  assumes "segments_of_aform X \<noteq> []"
  shows "fst (hd (segments_of_aform X)) = snd (last (segments_of_aform X))"
  using assms
  by (auto simp: segments_of_aform_def Let_def fst_hd_half_segments_of_aform last_map
    pairself_apply last_half_segments mirror_point_def)

lemma convex_polychain_segments_of_aform:
  assumes "1 < length (half_segments_of_aform X)"
  shows "convex_polychain (segments_of_aform X)"
  unfolding segments_of_aform_def Let_def
    using ccw_hd_last_half_segments_dirvec[OF assms]
  by (intro convex_polychain_appendI)
    (auto
      simp: convex_polychain_half_segments_of_aform convex_polychain_map_mirror dirvec_minus hd_map
        pairself_apply last_half_segments mirror_point_def fst_hd_half_segments_of_aform det3_def'
        algebra_simps ccw'_def
      intro!: polychain_appendI polychain_half_segments_of_aform polychain_map_pairself)

lemma convex_polygon_segments_of_aform:
  assumes "1 < length (half_segments_of_aform X)"
  shows "convex_polygon (segments_of_aform X)"
proof -
  from assms have hne: "half_segments_of_aform X \<noteq> []"
    by auto
  from convex_polychain_segments_of_aform[OF assms]
  have "convex_polychain (segments_of_aform X)" .
  thus ?thesis
    by (auto simp: convex_polygon_def segments_of_aform_closed)
qed

lemma
  previous_segments_of_aformE:
  assumes "(y, z) \<in> set (segments_of_aform X)"
  obtains x where "(x, y) \<in> set (segments_of_aform X)"
proof -
  from assms have ne[simp]: "segments_of_aform X \<noteq> []"
    by auto
  from assms
  obtain i where i: "i<length (segments_of_aform X)" "(segments_of_aform X) ! i = (y, z)"
    by (auto simp: in_set_conv_nth)
  show ?thesis
  proof (cases i)
    case 0
    with segments_of_aform_closed[of X] assms
    have "(fst (last (segments_of_aform X)), y) \<in> set (segments_of_aform X)"
      by (metis fst_conv hd_conv_nth i(2) last_in_set ne snd_conv surj_pair)
    thus ?thesis ..
  next
    case (Suc j)
    have "(fst (segments_of_aform X ! j), snd (segments_of_aform X ! j)) \<in>
        set (segments_of_aform X)"
      using Suc i(1) by auto
    also
    from i have "y = fst (segments_of_aform X ! i)"
      by auto
    hence "snd (segments_of_aform X ! j) = y"
      using polychain_segments_of_aform[of X] i(1) Suc
      by (auto simp: polychain_def Suc)
    finally have "(fst (segments_of_aform X ! j), y) \<in> set (segments_of_aform X)" .
    thus ?thesis ..
  qed
qed

lemma fst_compose_pairself: "fst o pairself f = f o fst"
  and snd_compose_pairself: "snd o pairself f = f o snd"
  by (auto simp: pairself_apply)

lemma in_set_butlastI: "xs \<noteq> [] \<Longrightarrow> x \<in> set xs \<Longrightarrow> x \<noteq> last xs \<Longrightarrow> x \<in> set (butlast xs)"
  by (induct xs) (auto split: if_splits)

lemma distinct_in_set_butlastD:
  "x \<in> set (butlast xs) \<Longrightarrow> distinct xs \<Longrightarrow> x \<noteq> last xs"
  by (induct xs) auto

lemma distinct_in_set_tlD:
  "x \<in> set (tl xs) \<Longrightarrow> distinct xs \<Longrightarrow> x \<noteq> hd xs"
  by (induct xs) auto

lemma ccw'_sortedP_snd_segments_of_aform:
  assumes "length (inl (snd X)) > 1"
  shows
    "ccw'.sortedP (lowest_vertex (fst X, nlex_pdevs (snd X)))
      (butlast (map snd (segments_of_aform X)))"
proof cases
  assume "[] = half_segments_of_aform X"
  from this show ?thesis
    by (simp add: segments_of_aform_def Let_def ccw'.sortedP.Nil)
next
  assume H: "[] \<noteq> half_segments_of_aform X"
  let ?m = "mirror_point (fst X)"
  have ne: "inl (snd X) \<noteq> []" using assms by auto
  have "ccw'.sortedP (lowest_vertex (fst X, nlex_pdevs (snd X)))
     (map snd (half_segments_of_aform X) @ butlast (map (?m \<circ> snd)
    (half_segments_of_aform X)))"
  proof (rule ccw'.sortedP_appendI)
    show "ccw'.sortedP (lowest_vertex (fst X, nlex_pdevs (snd X))) (map snd (half_segments_of_aform X))"
      by (rule ccw'_sortedP_snd_half_segments_of_aform)
    have "butlast (map (?m \<circ> snd) (half_segments_of_aform X)) =
      butlast
       (map (?m \<circ> snd) (polychain_of (lowest_vertex (fst X, nlex_pdevs (snd X)))
         (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X))))))"
      by (simp add: half_segments_of_aform_def)
    also have "\<dots> =
       map snd
        (butlast
          (polychain_of (?m (lowest_vertex (fst X, nlex_pdevs (snd X))))
            (map uminus (map ((*\<^sub>R) 2) (ccw.selsort 0 (inl (snd X)))))))"
      (is "_ = map snd (butlast (polychain_of ?x ?xs))")
      by (simp add: map_mirror_o_snd_polychain_of_eq map_butlast)
    also
    {
      have "ccw'.sortedP 0 ?xs"
        by (intro ccw'_sortedP_uminus ccw'_sortedP_scaled_inl)
      moreover
      have "ccw'.sortedP ?x (map snd (polychain_of ?x ?xs))"
        unfolding ccw'_sortedP_mirror[symmetric] map_map map_mirror_o_snd_polychain_of_eq
        by (auto simp add: o_def intro!: ccw'_sortedP_polychain_of_snd ccw'_sortedP_scaled_inl)
      ultimately
      have "ccw'.sortedP (snd (last (polychain_of ?x ?xs)))
          (map snd (butlast (polychain_of ?x ?xs)))"
        by (rule ccw'_sortedP_convex_rotate_aux)
    }
    also have "(snd (last (polychain_of ?x ?xs))) =
        ?m (last (map snd (half_segments_of_aform X)))"
      by (simp add: half_segments_of_aform_def ne map_mirror_o_snd_polychain_of_eq
         last_map[symmetric, where f="?m"]
         last_map[symmetric, where f="snd"])
    also have "\<dots> = lowest_vertex (fst X, nlex_pdevs (snd X))"
      using ne H
      by (auto simp: lowest_vertex_eq_mirror_last snd_last)
    finally show "ccw'.sortedP (lowest_vertex (fst X, nlex_pdevs (snd X)))
       (butlast (map (?m \<circ> snd) (half_segments_of_aform X)))" .
  next
    fix x y
    assume seg: "x \<in> set (map snd (half_segments_of_aform X))"
      and mseg: "y \<in> set (butlast (map (?m \<circ> snd) (half_segments_of_aform X)))"
    from seg assms have neq_Nil: "inl (snd X) \<noteq> []" "half_segments_of_aform X \<noteq> []"
      by auto

    from seg obtain a where a: "(a, x) \<in> set (half_segments_of_aform X)"
      by auto
    from mseg obtain b
    where mirror_y: "(b, ?m y) \<in> set (butlast (half_segments_of_aform X))"
      by (auto simp: map_butlast[symmetric])

    let ?l = "lowest_vertex (fst X, nlex_pdevs (snd X))"
    let ?ml = "?m ?l"

    have mirror_eq_last: "?ml = snd (last (half_segments_of_aform X))"
      using seg H
      by (intro last_half_segments[symmetric]) simp

    define r
      where "r = ?l + (0, abs (snd x - snd ?l) + abs (snd y - snd ?l) + abs (snd ?ml - snd ?l) + 1)"

    have d1: "x \<noteq> r" "y \<noteq> r" "?l \<noteq> r" "?ml \<noteq> r"
      by (auto simp: r_def plus_prod_def prod_eq_iff)
    have "distinct (map (?m \<circ> snd) (half_segments_of_aform X))"
      unfolding map_comp_map[symmetric]
      unfolding o_def distinct_map_mirror_point_eq
      by (rule distinct_snd_half_segments)
    from distinct_in_set_butlastD[OF \<open>y \<in> _\<close> this]
    have "?l \<noteq> y"
      by (simp add: neq_Nil lowest_vertex_eq_mirror_last last_map)
    moreover have "?l \<noteq> ?ml"
      using neq_Nil by (auto simp add: eq_self_mirror_iff lowest_vertex_eq_center_iff inl_def)
    ultimately
    have d2: "?l \<noteq> y" "?l \<noteq> ?ml"
      by auto

    have *: "ccw' ?l (?m y) ?ml"
      by (metis mirror_eq_last ccw'_half_segments_lowest_last mirror_y neq_Nil(1))
    have "ccw' ?ml y ?l"
      by (rule ccw'_mirror_point[of "fst X"]) (simp add: *)
    hence lmy: "ccw' ?l ?ml y"
      by (simp add: ccw'_def det3_def' algebra_simps)
    let ?ccw = "ccw' (lowest_vertex (fst X, nlex_pdevs (snd X))) x y"
    {
      assume "x \<noteq> ?ml"
      hence x_butlast: "(a, x) \<in> set (butlast (half_segments_of_aform X))"
        unfolding mirror_eq_last
        using a
        by (auto intro!: in_set_butlastI simp: prod_eq_iff)
      have "ccw' ?l x ?ml"
        by (metis mirror_eq_last ccw'_half_segments_lowest_last x_butlast neq_Nil(1))
    } note lxml = this
    {
      assume "x = ?ml"
      hence ?ccw
        by (simp add: lmy)
    } moreover {
      assume "x \<noteq> ?ml" "y = ?ml"
      hence ?ccw
        by (simp add: lxml)
    } moreover {
      assume d3: "x \<noteq> ?ml" "y \<noteq> ?ml"

      from \<open>x \<in> set _\<close>
      have "x \<in> set (map snd (half_segments_of_aform X))" by force
      hence "x \<in> set (tl (map fst (half_segments_of_aform X)))"
        using d3
        unfolding map_snd_half_segments_aux_eq[OF neq_Nil(2)]
        by (auto simp: mirror_eq_last)
      from distinct_in_set_tlD[OF this distinct_fst_half_segments]
      have "?l \<noteq> x"
        by (simp add: fst_hd_half_segments_of_aform neq_Nil hd_map)

      from lxml[OF \<open>x \<noteq> ?ml\<close>] \<open>ccw' ?l ?ml y\<close>
      have d4: "x \<noteq> y"
        by (rule neq_left_right_of lxml)

      have "distinct5 x ?ml y r ?l"
        using d1 d2 \<open>?l \<noteq> x\<close> d3 d4
        by simp_all
      moreover
      note _
      moreover
      have "lex x ?l"
        by (rule lex_half_segments_lowest_vertex) fact
      hence "ccw ?l r x"
        unfolding r_def by (rule lex_ccw_left) simp
      moreover
      have "lex ?ml ?l"
        using last_in_set[OF H[symmetric]]
        by (auto simp: mirror_eq_last intro: lex_half_segments_lowest_vertex')
      hence "ccw ?l r ?ml"
        unfolding r_def by (rule lex_ccw_left) simp
      moreover
      have "lex (?m (lowest_vertex (fst X, nlex_pdevs (snd X)))) (?m y)"
        using mirror_y
        by (force dest!: in_set_butlastD intro: lex_half_segments_last' simp: mirror_eq_last )
      hence "lex y ?l"
        by (rule lex_mirror_point)
      hence "ccw ?l r y"
        unfolding r_def by (rule lex_ccw_left) simp
      moreover
      from \<open>x \<noteq> ?ml\<close> have "ccw ?l x ?ml"
        by (simp add: ccw_def lxml)
      moreover
      from lmy have "ccw ?l ?ml y"
        by (simp add: ccw_def)
      ultimately
      have "ccw ?l x y"
        by (rule ccw.transitive[where S=UNIV]) simp

      moreover
      {
        have "x \<noteq> ?l" using \<open>?l \<noteq> x\<close> by simp
        moreover
        have "lex (?m y) (?m ?ml)"
          using mirror_y
          by (force intro: lex_half_segments_lowest_vertex in_set_butlastD)
        hence "lex ?ml y"
          by (rule lex_mirror_point)
        moreover
        from a have "lex ?ml x"
          unfolding mirror_eq_last
          by (rule lex_half_segments_last)
        moreover note \<open>lex y ?l\<close> \<open>lex x ?l\<close> \<open>ccw' ?l x ?ml\<close> \<open>ccw' ?l ?ml y\<close>
        ultimately
        have ncoll: "\<not> coll ?l x y"
          by (rule not_coll_ordered_lexI)
      }
      ultimately have ?ccw
        by (simp add: ccw_def)
    } ultimately show ?ccw
      by blast
  qed
  thus ?thesis using H
    by (simp add: segments_of_aform_def Let_def butlast_append snd_compose_pairself)
qed

lemma polychain_of_segments_of_aform1:
  assumes "length (segments_of_aform X) = 1"
  shows "False"
  using assms
  by (auto simp: segments_of_aform_def Let_def half_segments_of_aform_def add_is_1
    split: if_split_asm)

lemma polychain_of_segments_of_aform2:
  assumes "segments_of_aform X = [x, y]"
  assumes "between (fst x, snd x) p"
  shows "p \<in> convex hull set (map fst (segments_of_aform X))"
proof -
  from polychain_segments_of_aform[of X] segments_of_aform_closed[of X] assms
  have "fst y = snd x" "snd y = fst x" by (simp_all add: polychain_def)
  thus ?thesis
    using assms
    by (cases x) (auto simp: between_mem_convex_hull)
qed

lemma append_eq_2:
  assumes "length xs = length ys"
  shows "xs @ ys = [x, y] \<longleftrightarrow> xs = [x] \<and> ys = [y]"
  using assms
proof (cases xs)
  case (Cons z zs)
  thus ?thesis using assms by (cases zs) auto
qed simp

lemma segments_of_aform_line_segment:
  assumes "segments_of_aform X = [x, y]"
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "aform_val e X \<in> closed_segment (fst x) (snd x)"
proof -
  from pdevs_val_pdevs_of_list_inl2E[OF \<open>e \<in> _\<close>, of "snd X"]
  obtain e' where e': "pdevs_val e (snd X) = pdevs_val e' (pdevs_of_list (inl (snd X)))"
    "e' \<in> UNIV \<rightarrow> {- 1..1}" .
  from e' have "0 \<le> 1 + e' 0" by (auto simp: Pi_iff dest!: spec[where x=0])
  with assms e' show ?thesis
    by (auto simp: segments_of_aform_def Let_def append_eq_2 half_segments_of_aform_def
        polychain_of_singleton_iff mirror_point_def ccw.selsort_singleton_iff lowest_vertex_def
        aform_val_def sum_list_nlex_eq_sum_list_inl closed_segment_def Pi_iff
      intro!: exI[where x="(1 + e' 0) / 2"])
      (auto simp: algebra_simps)
qed


subsection \<open>Continuous Generalization\<close>

lemma LIMSEQ_minus_fract_mult:
  "(\<lambda>n. r * (1 - 1 / real (Suc (Suc n)))) \<longlonglongrightarrow> r"
  by (rule tendsto_eq_rhs[OF tendsto_mult[where a=r and b = 1]])
    (auto simp: inverse_eq_divide[symmetric] simp del: of_nat_Suc
      intro: filterlim_compose[OF LIMSEQ_inverse_real_of_nat filterlim_Suc] tendsto_eq_intros)

lemma det3_nonneg_segments_of_aform:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  shows "list_all (\<lambda>seg. det3 (fst seg) (snd seg) (aform_val e X) \<ge> 0) (segments_of_aform X)"
  unfolding list_all_iff
proof safe
  fix a b c d
  assume seg: "((a, b), c, d) \<in> set (segments_of_aform X)" (is "?seg \<in> _")
  define normal_of_segment
    where "normal_of_segment = (\<lambda>((a0, a1), b0, b1). (b1 - a1, a0 - b0)::real*real)"
  define support_of_segment
    where "support_of_segment = (\<lambda>(a, b). normal_of_segment (a, b) \<bullet> a)"
  have "closed ((\<lambda>x. x \<bullet> normal_of_segment ?seg) -` {..support_of_segment ?seg})" (is "closed ?cl")
    by (auto intro!: continuous_intros closed_vimage)
  moreover
  define f where "f n i = e i * ( 1 - 1 / (Suc (Suc n)))" for n i
  have "\<forall>n. aform_val (f n) X \<in> ?cl"
  proof
    fix n
    have "f n \<in> UNIV \<rightarrow> {-1 <..< 1}"
      using assms
      by (auto simp: f_def Pi_iff intro!: less_one_multI minus_one_less_multI)
    from list_allD[OF segments_of_aform_strict[OF this assms(2)] seg]
    show "aform_val (f n) X \<in> (\<lambda>x. x \<bullet> normal_of_segment ((a, b), c, d)) -`
        {..support_of_segment ((a, b), c, d)}"
      by (auto simp: list_all_iff normal_of_segment_def support_of_segment_def
        det3_def' field_simps inner_prod_def ccw'_def)
  qed
  moreover
  have "\<And>i. (\<lambda>n. f n i) \<longlonglongrightarrow> e i"
    unfolding f_def
    by (rule LIMSEQ_minus_fract_mult)
  hence "(\<lambda>n. aform_val (f n) X) \<longlonglongrightarrow> aform_val e X"
    by (auto simp: aform_val_def pdevs_val_sum intro!: tendsto_intros)
  ultimately have "aform_val e X \<in> ?cl"
    by (rule closed_sequentially)
  thus "det3 (fst ?seg) (snd ?seg) (aform_val e X) \<ge> 0"
    by (auto simp: list_all_iff normal_of_segment_def support_of_segment_def det3_def' field_simps
      inner_prod_def)
qed

lemma det3_nonneg_segments_of_aformI:
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  assumes "length (half_segments_of_aform X) \<noteq> 1"
  assumes "seg \<in> set (segments_of_aform X)"
  shows "det3 (fst seg) (snd seg) (aform_val e X) \<ge> 0"
  using assms det3_nonneg_segments_of_aform by (auto simp: list_all_iff)


subsection \<open>Intersection of Vertical Line with Segment\<close>

fun intersect_segment_xline'::"nat \<Rightarrow> point * point \<Rightarrow> real \<Rightarrow> point option"
  where "intersect_segment_xline' p ((x0, y0), (x1, y1)) xl =
    (if x0 \<le> xl \<and> xl \<le> x1 then
      if x0 = x1 then Some ((min y0 y1), (max y0 y1))
      else
        let
          yl = truncate_down p (truncate_down p (real_divl p (y1 - y0) (x1 - x0) * (xl - x0)) + y0);
          yr = truncate_up p (truncate_up p (real_divr p (y1 - y0) (x1 - x0) * (xl - x0)) + y0)
        in Some (yl, yr)
    else None)"

lemma norm_pair_fst0[simp]: "norm (0, x) = norm x"
  by (auto simp: norm_prod_def)

lemmas add_right_mono_le = order_trans[OF add_right_mono]
lemmas mult_right_mono_le = order_trans[OF mult_right_mono]

lemmas add_right_mono_ge = order_trans[OF _ add_right_mono]
lemmas mult_right_mono_ge = order_trans[OF _ mult_right_mono]

lemma dest_segment:
  fixes x b::real
  assumes "(x, b) \<in> closed_segment (x0, y0) (x1, y1)"
  assumes "x0 \<noteq> x1"
  shows "b = (y1 - y0) * (x - x0) / (x1 - x0) + y0"
proof -
  from assms obtain u where u: "x = x0 *\<^sub>R (1 - u) + u * x1" "b = y0 *\<^sub>R (1 - u) + u * y1" "0 \<le> u" "u \<le> 1"
    by (auto simp: closed_segment_def algebra_simps)
  show "b = (y1 - y0) * (x - x0) / (x1 - x0) + y0 "
    using assms by (auto simp: closed_segment_def field_simps u)
qed

lemma intersect_segment_xline':
  assumes "intersect_segment_xline' prec (p0, p1) x = Some (m, M)"
  shows "closed_segment p0 p1 \<inter> {p. fst p = x} \<subseteq> {(x, m) .. (x, M)}"
  using assms
proof (cases p0)
  case (Pair x0 y0) note p0 = this
  show ?thesis
  proof (cases p1)
    case (Pair x1 y1) note p1 = this
    {
      assume "x0 = x1" "x = x1" "m = min y0 y1" "M = max y0 y1"
      hence ?thesis
        by (force simp: abs_le_iff p0 p1 min_def max_def algebra_simps dest: segment_bound
          split: if_split_asm)
    } thus ?thesis
      using assms
      by (auto simp: abs_le_iff p0 p1 split: if_split_asm
        intro!: truncate_up_le truncate_down_le
        add_right_mono_le[OF truncate_down]
        add_right_mono_le[OF real_divl]
        add_right_mono_le[OF mult_right_mono_le[OF real_divl]]
        add_right_mono_ge[OF _ truncate_up]
        add_right_mono_ge[OF _ mult_right_mono_ge[OF _ real_divr]]
        dest!: dest_segment)
  qed
qed

lemma
  in_segment_fst_le:
  fixes x0 x1 b::real
  assumes "x0 \<le> x1" "(x, b) \<in> closed_segment (x0, y0) (x1, y1)"
  shows "x \<le> x1"
  using assms using mult_left_mono[OF \<open>x0 \<le> x1\<close>, where c="1 - u" for u]
  by (force simp add: min_def max_def split: if_split_asm
    simp add: algebra_simps not_le closed_segment_def)

lemma
  in_segment_fst_ge:
  fixes x0 x1 b::real
  assumes "x0 \<le> x1" "(x, b) \<in> closed_segment (x0, y0) (x1, y1)"
  shows "x0 \<le> x"
  using assms using mult_left_mono[OF \<open>x0 \<le> x1\<close>]
  by (force simp add: min_def max_def split: if_split_asm
    simp add: algebra_simps not_le closed_segment_def)

lemma intersect_segment_xline'_eq_None:
  assumes "intersect_segment_xline' prec (p0, p1) x = None"
  assumes "fst p0 \<le> fst p1"
  shows "closed_segment p0 p1 \<inter> {p. fst p = x} = {}"
  using assms
  by (cases p0, cases p1)
    (auto simp: abs_le_iff split: if_split_asm dest: in_segment_fst_le in_segment_fst_ge)

fun intersect_segment_xline
  where "intersect_segment_xline prec ((a, b), (c, d)) x =
  (if a \<le> c then intersect_segment_xline' prec ((a, b), (c, d)) x
  else intersect_segment_xline' prec ((c, d), (a, b)) x)"

lemma closed_segment_commute: "closed_segment a b = closed_segment b a"
  by (meson convex_contains_segment convex_closed_segment dual_order.antisym ends_in_segment)

lemma intersect_segment_xline:
  assumes "intersect_segment_xline prec (p0, p1) x = Some (m, M)"
  shows "closed_segment p0 p1 \<inter> {p. fst p = x} \<subseteq> {(x, m) .. (x, M)}"
  using assms
  by (cases p0, cases p1)
    (auto simp: closed_segment_commute split: if_split_asm simp del: intersect_segment_xline'.simps
      dest!: intersect_segment_xline')

lemma intersect_segment_xline_fst_snd:
  assumes "intersect_segment_xline prec seg x = Some (m, M)"
  shows "closed_segment (fst seg) (snd seg) \<inter> {p. fst p = x} \<subseteq> {(x, m) .. (x, M)}"
  using intersect_segment_xline[of prec "fst seg" "snd seg" x m M] assms
  by simp

lemma intersect_segment_xline_eq_None:
  assumes "intersect_segment_xline prec (p0, p1) x = None"
  shows "closed_segment p0 p1 \<inter> {p. fst p = x} = {}"
  using assms
  by (cases p0, cases p1)
     (auto simp: closed_segment_commute split: if_split_asm simp del: intersect_segment_xline'.simps
      dest!: intersect_segment_xline'_eq_None)

lemma inter_image_empty_iff: "(X \<inter> {p. f p = x} = {}) \<longleftrightarrow> (x \<notin> f ` X)"
  by auto

lemma fst_closed_segment[simp]: "fst ` closed_segment a b = closed_segment (fst a) (fst b)"
  by (force simp: closed_segment_def)

lemma intersect_segment_xline_eq_empty:
  fixes p0 p1::"real * real"
  assumes "closed_segment p0 p1 \<inter> {p. fst p = x} = {}"
  shows "intersect_segment_xline prec (p0, p1) x = None"
  using assms
  by (cases p0, cases p1)
    (auto simp: inter_image_empty_iff closed_segment_eq_real_ivl split: if_split_asm)

lemma intersect_segment_xline_le:
  assumes "intersect_segment_xline prec y xl = Some (m0, M0)"
  shows "m0 \<le> M0"
  using assms
  by (cases y) (auto simp: min_def split: if_split_asm intro!: truncate_up_le truncate_down_le
    order_trans[OF real_divl] order_trans[OF _ real_divr] mult_right_mono)

lemma intersect_segment_xline_None_iff:
  fixes p0 p1::"real * real"
  shows "intersect_segment_xline prec (p0, p1) x = None \<longleftrightarrow> closed_segment p0 p1 \<inter> {p. fst p = x} = {}"
  by (auto intro!: intersect_segment_xline_eq_empty dest!: intersect_segment_xline_eq_None)


subsection \<open>Bounds on Vertical Intersection with Oriented List of Segments\<close>

primrec bound_intersect_2d where
  "bound_intersect_2d prec [] x = None"
| "bound_intersect_2d prec (X # Xs) xl =
    (case bound_intersect_2d prec Xs xl of
      None \<Rightarrow> intersect_segment_xline prec X xl
    | Some (m, M) \<Rightarrow>
      (case intersect_segment_xline prec X xl of
        None \<Rightarrow> Some (m, M)
      | Some (m', M') \<Rightarrow> Some (min m' m, max M' M)))"

lemma
  bound_intersect_2d_eq_None:
  assumes "bound_intersect_2d prec Xs x = None"
  assumes "X \<in> set Xs"
  shows "intersect_segment_xline prec X x = None"
  using assms by (induct Xs) (auto split: option.split_asm)

lemma bound_intersect_2d_upper:
  assumes "bound_intersect_2d prec Xs x = Some (m, M)"
  obtains X m' where "X \<in> set Xs" "intersect_segment_xline prec X x = Some (m', M)"
    "\<And>X m' M' . X \<in> set Xs \<Longrightarrow> intersect_segment_xline prec X x = Some (m', M') \<Longrightarrow> M' \<le> M"
proof atomize_elim
  show "\<exists>X m'. X \<in> set Xs \<and> intersect_segment_xline prec X x = Some (m', M) \<and>
    (\<forall>X m' M'. X \<in> set Xs \<longrightarrow> intersect_segment_xline prec X x = Some (m', M') \<longrightarrow> M' \<le> M)"
    using assms
  proof (induct Xs arbitrary: m M)
    case Nil thus ?case by (simp add: bound_intersect_2d_def)
  next
    case (Cons X Xs)
    show ?case
    proof (cases "bound_intersect_2d prec Xs x")
      case None
      thus ?thesis using Cons
        by (intro exI[where x=X] exI[where x=m])
          (simp del: intersect_segment_xline.simps add: bound_intersect_2d_eq_None)
    next
      case (Some mM)
      note Some1=this
      then obtain m' M' where mM: "mM = (m', M')" by (cases mM)
      from Cons(1)[OF Some[unfolded mM]]
      obtain X' m'' where X': "X' \<in> set Xs"
        and m'': "intersect_segment_xline prec X' x = Some (m'', M')"
        and max: "\<And>X m' M'a. X \<in> set Xs \<Longrightarrow> intersect_segment_xline prec X x = Some (m', M'a) \<Longrightarrow>
          M'a \<le> M'"
        by auto
      show ?thesis
      proof (cases "intersect_segment_xline prec X x")
        case None thus ?thesis using Some1 mM Cons(2) X' m'' max
          by (intro exI[where x= X'] exI[where x= m''])
            (auto simp del: intersect_segment_xline.simps split: option.split_asm)
      next
        case (Some mM''')
        thus ?thesis using Some1 mM Cons(2) X' m''
          by (cases mM''')
            (force simp: max_def min_def simp del: intersect_segment_xline.simps
              split: option.split_asm if_split_asm dest!: max
              intro!: exI[where x= "if M' \<ge> snd mM''' then X' else X"]
              exI[where x= "if M' \<ge> snd mM''' then m'' else fst mM'''"])
      qed
    qed
  qed
qed

lemma bound_intersect_2d_lower:
  assumes "bound_intersect_2d prec Xs x = Some (m, M)"
  obtains X M' where "X \<in> set Xs" "intersect_segment_xline prec X x = Some (m, M')"
    "\<And>X m' M' . X \<in> set Xs \<Longrightarrow> intersect_segment_xline prec X x = Some (m', M') \<Longrightarrow> m \<le> m'"
proof atomize_elim
  show "\<exists>X M'. X \<in> set Xs \<and> intersect_segment_xline prec X x = Some (m, M') \<and>
    (\<forall>X m' M'. X \<in> set Xs \<longrightarrow> intersect_segment_xline prec X x = Some (m', M') \<longrightarrow> m \<le> m')"
    using assms
  proof (induct Xs arbitrary: m M)
    case Nil thus ?case by (simp add: bound_intersect_2d_def)
  next
    case (Cons X Xs)
    show ?case
    proof (cases "bound_intersect_2d prec Xs x")
      case None
      thus ?thesis using Cons
        by (intro exI[where x= X])
          (simp del: intersect_segment_xline.simps add: bound_intersect_2d_eq_None)
    next
      case (Some mM)
      note Some1=this
      then obtain m' M' where mM: "mM = (m', M')" by (cases mM)
      from Cons(1)[OF Some[unfolded mM]]
      obtain X' M'' where X': "X' \<in> set Xs"
        and M'': "intersect_segment_xline prec X' x = Some (m', M'')"
        and min: "\<And>X m'a M'. X \<in> set Xs \<Longrightarrow> intersect_segment_xline prec X x = Some (m'a, M') \<Longrightarrow>
          m' \<le> m'a"
        by auto
      show ?thesis
      proof (cases "intersect_segment_xline prec X x")
        case None thus ?thesis using Some1 mM Cons(2) X' M'' min
          by (intro exI[where x= X'] exI[where x= M''])
            (auto simp del: intersect_segment_xline.simps split: option.split_asm)
      next
        case (Some mM''')
        thus ?thesis using Some1 mM Cons(2) X' M'' min
          by (cases mM''')
            (force simp: max_def min_def
              simp del: intersect_segment_xline.simps
              split: option.split_asm if_split_asm
              dest!: min
              intro!: exI[where x= "if m' \<le> fst mM''' then X' else X"]
                exI[where x= "if m' \<le> fst mM''' then M'' else snd mM'''"])
      qed
    qed
  qed
qed

lemma bound_intersect_2d:
  assumes "bound_intersect_2d prec Xs x = Some (m, M)"
  shows "(\<Union>(p1, p2) \<in> set Xs. closed_segment p1 p2) \<inter> {p. fst p = x} \<subseteq> {(x, m) .. (x, M)}"
proof (clarsimp, safe)
  fix b x0 y0 x1 y1
  assume H: "((x0, y0), x1, y1) \<in> set Xs" "(x, b) \<in> closed_segment (x0, y0) (x1, y1)"
  hence "intersect_segment_xline prec ((x0, y0), x1, y1) x \<noteq> None"
    by (intro notI)
      (auto dest!: intersect_segment_xline_eq_None simp del: intersect_segment_xline.simps)
  then obtain e f where ef: "intersect_segment_xline prec ((x0, y0), x1, y1) x = Some (e, f)"
    by auto
  with H have "m \<le> e"
    by (auto intro: bound_intersect_2d_lower[OF assms])
  also have "\<dots> \<le> b"
    using intersect_segment_xline[OF ef] H
    by force
  finally show "m \<le> b" .
  have "b \<le> f"
    using intersect_segment_xline[OF ef] H
    by force
  also have "\<dots> \<le> M"
    using H ef by (auto intro: bound_intersect_2d_upper[OF assms])
  finally show "b \<le> M" .
qed

lemma bound_intersect_2d_eq_None_iff:
  "bound_intersect_2d prec Xs x = None \<longleftrightarrow> (\<forall>X\<in>set Xs. intersect_segment_xline prec X x = None)"
  by (induct Xs) (auto simp: split: option.split_asm)

lemma bound_intersect_2d_nonempty:
  assumes "bound_intersect_2d prec Xs x = Some (m, M)"
  shows "(\<Union>(p1, p2) \<in> set Xs. closed_segment p1 p2) \<inter> {p. fst p = x} \<noteq> {}"
proof -
  from assms have "bound_intersect_2d prec Xs x \<noteq> None" by simp
  then obtain p1 p2 where "(p1, p2) \<in> set Xs" "intersect_segment_xline prec (p1, p2) x \<noteq> None"
    unfolding bound_intersect_2d_eq_None_iff by auto
  hence "closed_segment p1 p2 \<inter> {p. fst p = x} \<noteq> {}"
    by (simp add: intersect_segment_xline_None_iff)
  thus ?thesis using \<open>(p1, p2) \<in> set Xs\<close> by auto
qed

lemma bound_intersect_2d_le:
  assumes "bound_intersect_2d prec Xs x = Some (m, M)" shows "m \<le> M"
proof -
  from bound_intersect_2d_nonempty[OF assms] bound_intersect_2d[OF assms]
  show "m \<le> M" by auto
qed


subsection \<open>Bounds on Vertical Intersection with General List of Segments\<close>

definition "bound_intersect_2d_ud prec X xl =
  (case segments_of_aform X of
    [] \<Rightarrow> if fst (fst X) = xl then let m = snd (fst X) in Some (m, m) else None
  | [x, y] \<Rightarrow> intersect_segment_xline prec x xl
  | xs \<Rightarrow>
    (case bound_intersect_2d prec (filter (\<lambda>((x1, y1), x2, y2). x1 < x2) xs) xl of
      Some (m, M') \<Rightarrow>
      (case bound_intersect_2d prec (filter (\<lambda>((x1, y1), x2, y2). x1 > x2) xs) xl of
        Some (m', M) \<Rightarrow> Some (min m m', max M M')
      | None \<Rightarrow> None)
    | None \<Rightarrow> None))"

lemma list_cases4:
  "\<And>x P. (x = [] \<Longrightarrow> P) \<Longrightarrow> (\<And>y. x = [y] \<Longrightarrow> P) \<Longrightarrow>
    (\<And>y z. x = [y, z] \<Longrightarrow> P) \<Longrightarrow>
    (\<And>w y z zs. x = w # y # z # zs \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis list.exhaust)

lemma bound_intersect_2d_ud_segments_of_aform_le:
  "bound_intersect_2d_ud prec X xl = Some (m0, M0) \<Longrightarrow> m0 \<le> M0"
  by (cases "segments_of_aform X" rule: list_cases4)
    (auto simp: Let_def bound_intersect_2d_ud_def min_def max_def intersect_segment_xline_le
      if_split_eq1 split: option.split_asm prod.split_asm list.split_asm
      dest!: bound_intersect_2d_le)

lemma pdevs_domain_eq_empty_iff[simp]: "pdevs_domain (snd X) = {} \<longleftrightarrow> snd X = zero_pdevs"
  by (auto simp: intro!: pdevs_eqI)

lemma ccw_contr_on_line_left:
  assumes "det3 (a, b) (x, c) (x, d) \<ge> 0" "a > x"
  shows "d \<le> c"
proof -
  from assms have "d * (a - x) \<le> c * (a - x)"
    by (auto simp: det3_def' algebra_simps)
  with assms show "c \<ge> d" by auto
qed

lemma ccw_contr_on_line_right:
  assumes "det3 (a, b) (x, c) (x, d) \<ge> 0" "a < x"
  shows "d \<ge> c"
proof -
  from assms have "c * (x - a) \<le> d * (x - a)"
    by (auto simp: det3_def' algebra_simps)
  with assms show "d \<ge> c" by auto
qed

lemma singleton_contrE:
  assumes "\<And>x y. x \<noteq> y \<Longrightarrow> x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> False"
  assumes "X \<noteq> {}"
  obtains x where "X = {x}"
  using assms by blast

lemma segment_intersection_singleton:
  fixes xl and a b::"real * real"
  defines "i \<equiv> closed_segment a b \<inter> {p. fst p = xl}"
  assumes ne1: "fst a \<noteq> fst b"
  assumes upper: "i \<noteq> {}"
  obtains p1 where "i = {p1}"
proof (rule singleton_contrE[OF _ upper])
  fix x y assume H: "x \<noteq> y" "x \<in> i" "y \<in> i"
  then obtain u v where uv: "x = u *\<^sub>R b + (1 - u) *\<^sub>R a" "y = v *\<^sub>R b + (1 - v) *\<^sub>R a"
    "0 \<le> u" "u \<le> 1" "0 \<le> v" "v \<le> 1"
    by (auto simp add: closed_segment_def i_def field_simps)
  then have "x + u *\<^sub>R a = a + u *\<^sub>R b" "y + v *\<^sub>R a = a + v *\<^sub>R b"
    by simp_all
  then have "fst (x + u *\<^sub>R a) = fst (a + u *\<^sub>R b)" "fst (y + v *\<^sub>R a) = fst (a + v *\<^sub>R b)"
    by simp_all
  then have "u = v * (fst a - fst b) / (fst a - fst b)"
    using ne1 H(2,3) \<open>0 \<le> u\<close> \<open>u \<le> 1\<close> \<open>0 \<le> v\<close> \<open>v \<le> 1\<close>
    by (simp add: closed_segment_def i_def field_simps)
  then have "u = v"
    by (simp add: ne1)
  then show False using H uv
    by simp
qed

lemma bound_intersect_2d_ud_segments_of_aform:
  assumes "bound_intersect_2d_ud prec X xl = Some (m0, M0)"
  assumes "e \<in> UNIV \<rightarrow> {-1 .. 1}"
  shows "{aform_val e X} \<inter> {x. fst x = xl} \<subseteq> {(xl, m0) .. (xl, M0)}"
proof safe
  fix a b
  assume safeassms: "(a, b) = aform_val e X" "xl = fst (a, b)"
  hence fst_aform_val: "fst (aform_val e X) = xl"
    by simp
  {
    assume len: "length (segments_of_aform X) > 2"
    with assms obtain m M m' M'
    where lb: "bound_intersect_2d prec
        [((x1, y1), x2, y2)\<leftarrow>segments_of_aform X . x1 < x2] xl = Some (m, M')"
      and ub: "bound_intersect_2d prec
        [((x1, y1), x2, y2)\<leftarrow>segments_of_aform X . x2 < x1] xl = Some (m', M)"
      and minmax: "m0 = min m m'" "M0 = max M M'"
      by (auto simp: bound_intersect_2d_ud_def split: option.split_asm list.split_asm )
    from bound_intersect_2d_upper[OF ub] obtain X1 m1
    where upper:
      "X1 \<in> set [((x1, y1), x2, y2)\<leftarrow>segments_of_aform X . x2 < x1]"
      "intersect_segment_xline prec X1 xl = Some (m1, M)"
      by metis
    from bound_intersect_2d_lower[OF lb] obtain X2 M2
    where lower:
      "X2 \<in> set [((x1, y1), x2, y2)\<leftarrow>segments_of_aform X . x1 < x2]"
      "intersect_segment_xline prec X2 xl = Some (m, M2)"
      by metis
    from upper(1) lower(1)
    have X1: "X1 \<in> set (segments_of_aform X)" "fst (fst X1) > fst (snd X1)"
      and X2: "X2 \<in> set (segments_of_aform X)" "fst (fst X2) < fst (snd X2)"
      by auto
    note upper_seg = intersect_segment_xline_fst_snd[OF upper(2)]
    note lower_seg = intersect_segment_xline_fst_snd[OF lower(2)]
    from len have lh: "length (half_segments_of_aform X) \<noteq> 1"
      by (auto simp: segments_of_aform_def Let_def)
    from X1 have ne1: "fst (fst X1) \<noteq> fst (snd X1)"
      by simp
    moreover have "closed_segment (fst X1) (snd X1) \<inter> {p. fst p = xl} \<noteq> {}"
      using upper(2)
      by (simp add: intersect_segment_xline_None_iff[of prec, symmetric])
    ultimately obtain p1 where p1: "closed_segment (fst X1) (snd X1) \<inter> {p. fst p = xl} = {p1}"
      by (rule segment_intersection_singleton)
    then obtain u where u: "p1 = (1 - u) *\<^sub>R fst X1 + u *\<^sub>R (snd X1)" "0 \<le> u" "u \<le> 1"
      by (auto simp: closed_segment_def algebra_simps)
    have coll1: "det3 (fst X1) p1 (aform_val e X) \<ge> 0"
      and coll1': "det3 p1 (snd X1) (aform_val e X) \<ge> 0"
      unfolding atomize_conj
      using u
      by (cases "u = 0 \<or> u = 1")
        (auto simp: u(1) intro: det3_nonneg_scaleR_segment1 det3_nonneg_scaleR_segment2
          det3_nonneg_segments_of_aformI[OF \<open>e \<in> _\<close> lh X1(1)])

    from X2 have ne2: "fst (fst X2) \<noteq> fst (snd X2)" by simp
    moreover
    have "closed_segment (fst X2) (snd X2) \<inter> {p. fst p = xl} \<noteq> {}"
      using lower(2)
      by (simp add: intersect_segment_xline_None_iff[of prec, symmetric])
    ultimately
    obtain p2 where p2: "closed_segment (fst X2) (snd X2) \<inter> {p. fst p = xl} = {p2}"
      by (rule segment_intersection_singleton)
    then obtain v where v: "p2 = (1 - v) *\<^sub>R fst X2 + v *\<^sub>R (snd X2)" "0 \<le> v" "v \<le> 1"
      by (auto simp: closed_segment_def algebra_simps)
    have coll2: "det3 (fst X2) p2 (aform_val e X) \<ge> 0"
      and coll2': "det3 p2 (snd X2) (aform_val e X) \<ge> 0"
      unfolding atomize_conj
      using v
      by (cases "v = 0 \<or> v = 1")
        (auto simp: v(1) intro: det3_nonneg_scaleR_segment1 det3_nonneg_scaleR_segment2
          det3_nonneg_segments_of_aformI[OF \<open>e \<in> _\<close> lh X2(1)])

    from in_set_segments_of_aform_aform_valE
        [of "fst X1" "snd X1" X, unfolded prod.collapse, OF X1(1)]
    obtain e1s where e1s: "snd X1 = aform_val e1s X" "e1s \<in> UNIV \<rightarrow> {- 1..1}" .
    from previous_segments_of_aformE
        [of "fst X1" "snd X1" X, unfolded prod.collapse, OF X1(1)]
    obtain fX0 where "(fX0, fst X1) \<in> set (segments_of_aform X)" .
    from in_set_segments_of_aform_aform_valE[OF this]
    obtain e1f where e1f: "fst X1 = aform_val e1f X" "e1f \<in> UNIV \<rightarrow> {- 1..1}" .
    have "p1 \<in> closed_segment (aform_val e1f X) (aform_val e1s X)"
      using p1 by (auto simp: e1s e1f)
    with segment_in_aform_val[OF e1s(2) e1f(2), of X]
    obtain ep1 where ep1: "ep1 \<in> UNIV \<rightarrow> {-1 .. 1}" "p1 = aform_val ep1 X"
      by (auto simp: Affine_def valuate_def closed_segment_commute)

    from in_set_segments_of_aform_aform_valE
        [of "fst X2" "snd X2" X, unfolded prod.collapse, OF X2(1)]
    obtain e2s where e2s: "snd X2 = aform_val e2s X" "e2s \<in> UNIV \<rightarrow> {- 1..1}" .
    from previous_segments_of_aformE
        [of "fst X2" "snd X2" X, unfolded prod.collapse, OF X2(1)]
    obtain fX02 where "(fX02, fst X2) \<in> set (segments_of_aform X)" .
    from in_set_segments_of_aform_aform_valE[OF this]
    obtain e2f where e2f: "fst X2 = aform_val e2f X" "e2f \<in> UNIV \<rightarrow> {- 1..1}" .
    have "p2 \<in> closed_segment (aform_val e2f X) (aform_val e2s X)"
      using p2 by (auto simp: e2s e2f)
    with segment_in_aform_val[OF e2f(2) e2s(2), of X]
    obtain ep2 where ep2: "ep2 \<in> UNIV \<rightarrow> {-1 .. 1}" "p2 = aform_val ep2 X"
      by (auto simp: Affine_def valuate_def)

    from det3_nonneg_segments_of_aformI[OF ep2(1), of X "(fst X1, snd X1)", unfolded prod.collapse,
        OF lh X1(1), unfolded ep2(2)[symmetric]]
    have c2: "det3 (fst X1) (snd X1) p2 \<ge> 0" .
    hence c12: "det3 (fst X1) p1 p2 \<ge> 0"
      using u by (cases "u = 0") (auto simp: u(1) det3_nonneg_scaleR_segment2)
    from det3_nonneg_segments_of_aformI[OF ep1(1), of X "(fst X2, snd X2)", unfolded prod.collapse,
        OF lh X2(1), unfolded ep1(2)[symmetric]]
    have c1: "det3 (fst X2) (snd X2) p1 \<ge> 0" .
    hence c21: "det3 (fst X2) p2 p1 \<ge> 0"
      using v by (cases "v = 0") (auto simp: v(1) det3_nonneg_scaleR_segment2)
    from p1 p2 have p1p2xl: "fst p1 = xl" "fst p2 = xl"
      by (auto simp: det3_def')
    from upper_seg p1 have "snd p1 \<le> M" by (auto simp: less_eq_prod_def)
    from lower_seg p2 have "m \<le> snd p2" by (auto simp: less_eq_prod_def)

    {
      have *: "(fst p1, snd (aform_val e X)) = aform_val e X"
        by (simp add: prod_eq_iff p1p2xl fst_aform_val)
      hence coll:
        "det3 (fst (fst X1), snd (fst X1)) (fst p1, snd p1) (fst p1, snd (aform_val e X)) \<ge> 0"
        and coll':
        "det3 (fst (snd X1), snd (snd X1)) (fst p1, snd (aform_val e X)) (fst p1, snd p1) \<ge> 0"
        using coll1 coll1'
        by (auto simp: det3_rotate)
      have "snd (aform_val e X) \<le> M"
      proof (cases "fst (fst X1) = xl")
        case False
        have "fst (fst X1) \<ge> fst p1"
          unfolding u using X1
          by (auto simp: algebra_simps intro!: mult_left_mono u)
        moreover
        have "fst (fst X1) \<noteq> fst p1"
          using False
          by (simp add: p1p2xl)
        ultimately
        have "fst (fst X1) > fst p1" by simp
        from ccw_contr_on_line_left[OF coll this]
        show ?thesis using \<open>snd p1 \<le> M\<close> by simp
      next
        case True
        have "fst (snd X1) * (1 - u) \<le> fst (fst X1) * (1 - u)"
          using X1 u
          by (auto simp: intro!: mult_right_mono)
        hence "fst (snd X1) \<le> fst p1"
          unfolding u by (auto simp: algebra_simps)
        moreover
        have "fst (snd X1) \<noteq> fst p1"
          using True ne1
          by (simp add: p1p2xl)
        ultimately
        have "fst (snd X1) < fst p1" by simp
        from ccw_contr_on_line_right[OF coll' this]
        show ?thesis using \<open>snd p1 \<le> M\<close> by simp
      qed
    } moreover {
      have "(fst p2, snd (aform_val e X)) = aform_val e X"
        by (simp add: prod_eq_iff p1p2xl fst_aform_val)
      hence coll:
        "det3 (fst (fst X2), snd (fst X2)) (fst p2, snd p2) (fst p2, snd (aform_val e X)) \<ge> 0"
        and coll':
        "det3 (fst (snd X2), snd (snd X2)) (fst p2, snd (aform_val e X)) (fst p2, snd p2) \<ge> 0"
        using coll2 coll2'
        by (auto simp: det3_rotate)
      have "m \<le> snd (aform_val e X)"
      proof (cases "fst (fst X2) = xl")
        case False
        have "fst (fst X2) \<le> fst p2"
          unfolding v using X2
          by (auto simp: algebra_simps intro!: mult_left_mono v)
        moreover
        have "fst (fst X2) \<noteq> fst p2"
          using False
          by (simp add: p1p2xl)
        ultimately
        have "fst (fst X2) < fst p2" by simp
        from ccw_contr_on_line_right[OF coll this]
        show ?thesis using \<open>m \<le> snd p2\<close> by simp
      next
        case True
        have "(1 - v) * fst (snd X2) \<ge> (1 - v) * fst (fst X2)"
          using X2 v
          by (auto simp: intro!: mult_left_mono)
        hence "fst (snd X2) \<ge> fst p2"
          unfolding v by (auto simp: algebra_simps)
        moreover
        have "fst (snd X2) \<noteq> fst p2"
          using True ne2
          by (simp add: p1p2xl)
        ultimately
        have "fst (snd X2) > fst p2" by simp
        from ccw_contr_on_line_left[OF coll' this]
        show ?thesis using \<open>m \<le> snd p2\<close> by simp
      qed
    } ultimately have "aform_val e X \<in> {(xl, m) .. (xl, M)}"
      by (auto simp: less_eq_prod_def fst_aform_val)
    hence "aform_val e X \<in> {(xl, m0) .. (xl, M0)}"
      by (auto simp: minmax less_eq_prod_def)
  } moreover {
    assume "length (segments_of_aform X) = 2"
    then obtain a b where s: "segments_of_aform X = [a, b]"
      by (auto simp: numeral_2_eq_2 length_Suc_conv)
    from segments_of_aform_line_segment[OF this assms(2)]
    have "aform_val e X \<in> closed_segment (fst a) (snd a)" .
    moreover
    from assms
    have "intersect_segment_xline prec a xl = Some (m0, M0)"
      by (auto simp: bound_intersect_2d_ud_def s)
    note intersect_segment_xline_fst_snd[OF this]
    ultimately
    have "aform_val e X \<in> {(xl, m0) .. (xl, M0)}"
      by (auto simp: less_eq_prod_def fst_aform_val)
  } moreover {
    assume "length (segments_of_aform X) = 1"
    from polychain_of_segments_of_aform1[OF this]
    have "aform_val e X \<in> {(xl, m0) .. (xl, M0)}" by auto
  } moreover {
    assume len: "length (segments_of_aform X) = 0"
    hence "independent_pdevs (map snd (list_of_pdevs (nlex_pdevs (snd X)))) = []"
      by (simp add: segments_of_aform_def Let_def half_segments_of_aform_def inl_def)
    hence "snd X = zero_pdevs"
      by (subst (asm) independent_pdevs_eq_Nil_iff) (auto simp: list_all_iff list_of_pdevs_def)
    hence "aform_val e X = fst X"
      by (simp add: aform_val_def)
    with len assms have "aform_val e X \<in> {(xl, m0) .. (xl, M0)}"
      by (auto simp: bound_intersect_2d_ud_def Let_def split: if_split_asm)
  } ultimately have "aform_val e X \<in> {(xl, m0)..(xl, M0)}"
    by arith
  thus "(a, b) \<in> {(fst (a, b), m0)..(fst (a, b), M0)}"
    using safeassms
    by simp
qed


subsection \<open>Approximation from Orthogonal Directions\<close>

definition inter_aform_plane_ortho::
  "nat \<Rightarrow> 'a::executable_euclidean_space aform \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a aform option"
  where
  "inter_aform_plane_ortho p Z n g = do {
    mMs \<leftarrow> those (map (\<lambda>b. bound_intersect_2d_ud p (inner2_aform Z n b) g) Basis_list);
    let l = (\<Sum>(b, m)\<leftarrow>zip Basis_list (map fst mMs). m *\<^sub>R b);
    let u = (\<Sum>(b, M)\<leftarrow>zip Basis_list (map snd mMs). M *\<^sub>R b);
    Some (aform_of_ivl l u)
  }"

lemma
  those_eq_SomeD:
  assumes "those (map f xs) = Some ys"
  shows "ys = map (the o f) xs \<and> (\<forall>i.\<exists>y. i < length xs \<longrightarrow> f (xs ! i) = Some y)"
  using assms
  by (induct xs arbitrary: ys) (auto split: option.split_asm simp: o_def nth_Cons split: nat.split)

lemma
  sum_list_zip_map:
  assumes "distinct xs"
  shows "(\<Sum>(x, y)\<leftarrow>zip xs (map g xs). f x y) = (\<Sum>x\<in>set xs. f x (g x))"
  by (force simp add: sum_list_distinct_conv_sum_set assms distinct_zipI1 split_beta'
    in_set_zip in_set_conv_nth inj_on_convol_ident
    intro!: sum.reindex_cong[where l="\<lambda>x. (x, g x)"])

lemma
  inter_aform_plane_ortho_overappr:
  assumes "inter_aform_plane_ortho p Z n g = Some X"
  shows "{x. \<forall>i \<in> Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z}} \<subseteq> Affine X"
proof -
  let ?inter = "(\<lambda>b. bound_intersect_2d_ud p (inner2_aform Z n b) g)"
  obtain xs
  where xs: "those (map ?inter Basis_list) = Some xs"
    using assms by (cases "those (map ?inter Basis_list)") (auto simp: inter_aform_plane_ortho_def)

  from those_eq_SomeD[OF this]
  obtain y' where xs_eq: "xs = map (the \<circ> ?inter) Basis_list"
    and y': "\<And>i. i < length (Basis_list::'a list) \<Longrightarrow> ?inter (Basis_list ! i) = Some (y' i)"
    by metis
  have "\<forall>(i::'a) \<in> Basis. \<exists>j<length (Basis_list::'a list). i = Basis_list ! j"
    by (metis Basis_list in_set_conv_nth)
  then obtain j where j:
    "\<And>i::'a. i\<in>Basis \<Longrightarrow> j i < length (Basis_list::'a list)"
    "\<And>i::'a. i\<in>Basis \<Longrightarrow> i = Basis_list ! j i"
    by metis
  define y where "y = y' o j"
  with y' j have y: "\<And>i. i \<in> Basis \<Longrightarrow> ?inter i = Some (y i)"
    by (metis comp_def)
  hence y_le: "\<And>i. i \<in> Basis \<Longrightarrow> fst (y i) \<le> snd (y i)"
    by (auto intro!: bound_intersect_2d_ud_segments_of_aform_le)
  hence "(\<Sum>b\<in>Basis. fst (y b) *\<^sub>R b) \<le> (\<Sum>b\<in>Basis. snd (y b) *\<^sub>R b)"
    by (auto simp: eucl_le[where 'a='a])
  with assms have X: "Affine X = {\<Sum>b\<in>Basis. fst (y b) *\<^sub>R b..\<Sum>b\<in>Basis. snd (y b) *\<^sub>R b}"
    by (auto simp: inter_aform_plane_ortho_def sum_list_zip_map xs xs_eq y Affine_aform_of_ivl)

  show ?thesis
  proof safe
    fix x assume x: "\<forall>i\<in>Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z}"
    {
      fix i::'a assume i: "i \<in> Basis"
      from x i have x_in2: "(g, x \<bullet> i) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Affine Z"
        by auto
      from x_in2 obtain e
      where e: "e \<in> UNIV \<rightarrow> {- 1..1}"
        and g: "g = aform_val e Z \<bullet> n"
        and x: "x \<bullet> i = aform_val e Z \<bullet> i"
        by (auto simp: Affine_def valuate_def)
      have "{aform_val e (inner2_aform Z n i)} = {aform_val e (inner2_aform Z n i)} \<inter> {x. fst x = g}"
        by (auto simp: g inner2_def)
      also
      from y[OF \<open>i \<in> Basis\<close>]
      have "?inter i = Some (fst (y i), snd (y i))" by simp
      note bound_intersect_2d_ud_segments_of_aform[OF this e]
      finally have "x \<bullet> i \<in> {fst (y i) .. snd (y i)}"
        by (auto simp: x inner2_def)
    } thus "x \<in> Affine X"
      unfolding X
      by (auto simp: eucl_le[where 'a='a])
  qed
qed

lemma inter_proj_eq:
  fixes n g l
  defines "G \<equiv> {x. x \<bullet> n = g}"
  shows "(\<lambda>x. x \<bullet> l) ` (Z \<inter> G) =
    {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> l)) ` Z}"
  by (auto simp: G_def)

lemma
  inter_overappr:
  fixes n \<gamma> l
  shows "Z \<inter> {x. x \<bullet> n = g} \<subseteq> {x. \<forall>i \<in> Basis. x \<bullet> i \<in> {y. (g, y) \<in> (\<lambda>x. (x \<bullet> n, x \<bullet> i)) ` Z}}"
  by auto

lemma inter_inter_aform_plane_ortho:
  assumes "inter_aform_plane_ortho p Z n g = Some X"
  shows "Affine Z \<inter> {x. x \<bullet> n = g} \<subseteq> Affine X"
proof -
  note inter_overappr[of "Affine Z" n g]
  also note inter_aform_plane_ortho_overappr[OF assms]
  finally show ?thesis .
qed

subsection \<open>``Completeness'' of Intersection\<close>

abbreviation "encompasses x seg \<equiv> det3 (fst seg) (snd seg) x \<ge> 0"

lemma encompasses_cases:
  "encompasses x seg \<or> encompasses x (snd seg, fst seg)"
  by (auto simp: det3_def' algebra_simps)

lemma list_all_encompasses_cases:
  assumes "list_all (encompasses p) (x # y # zs)"
  obtains "list_all (encompasses p) [x, y, (snd y, fst x)]"
    | "list_all (encompasses p) ((fst x, snd y)#zs)"
  using encompasses_cases
proof
  assume "encompasses p (snd y, fst x)"
  hence "list_all (encompasses p) [x, y, (snd y, fst x)]"
    using assms by (auto simp: list_all_iff)
  thus ?thesis ..
next
  assume "encompasses p (snd (snd y, fst x), fst (snd y, fst x))"
  hence "list_all (encompasses p) ((fst x, snd y)#zs)"
    using assms by (auto simp: list_all_iff)
  thus ?thesis ..
qed

lemma triangle_encompassing_polychain_of:
  assumes "det3 p a b \<ge> 0" "det3 p b c \<ge> 0" "det3 p c a \<ge> 0"
  assumes "ccw' a b c"
  shows "p \<in> convex hull {a, b, c}"
proof -
  from assms have nn: "det3 b c p \<ge> 0" "det3 c a p \<ge> 0" "det3 a b p \<ge> 0" "det3 a b c \<ge> 0"
    by (auto simp: det3_def' algebra_simps)
  have "det3 a b c *\<^sub>R p = det3 b c p *\<^sub>R a + det3 c a p *\<^sub>R b + det3 a b p *\<^sub>R c"
    by (auto simp: det3_def' algebra_simps prod_eq_iff)
  hence "inverse (det3 a b c) *\<^sub>R (det3 a b c *\<^sub>R p) =
      inverse (det3 a b c) *\<^sub>R (det3 b c p *\<^sub>R a + det3 c a p *\<^sub>R b + det3 a b p *\<^sub>R c)"
    by simp
  with assms have p_eq: "p =
    (det3 b c p / det3 a b c) *\<^sub>R a + (det3 c a p / det3 a b c) *\<^sub>R b + (det3 a b p / det3 a b c) *\<^sub>R c"
    (is "_ = scaleR ?u _ + scaleR ?v _ + scaleR ?w _")
    by (simp add: inverse_eq_divide algebra_simps ccw'_def)
  have det_eq: "det3 b c p / det3 a b c + det3 c a p / det3 a b c + det3 a b p / det3 a b c = 1"
    using assms(4)
    by (simp add: add_divide_distrib[symmetric] det3_def' algebra_simps ccw'_def)
  show ?thesis
    unfolding convex_hull_3
    using assms(4)
    by (blast intro: exI[where x="?u"] exI[where x="?v"] exI[where x="?w"]
      intro!: p_eq divide_nonneg_nonneg nn det_eq)
qed

lemma encompasses_convex_polygon3:
  assumes "list_all (encompasses p) (x#y#z#zs)"
  assumes "convex_polygon (x#y#z#zs)"
  assumes "ccw'.sortedP (fst x) (map snd (butlast (x#y#z#zs)))"
  shows "p \<in> convex hull (set (map fst (x#y#z#zs)))"
  using assms
proof (induct zs arbitrary: x y z p)
  case Nil
  thus ?case
    by (auto simp: det3_def' algebra_simps
      elim!: ccw'.sortedP_Cons ccw'.sortedP_Nil
      intro!: triangle_encompassing_polychain_of)
next
  case (Cons w ws)
  from Cons.prems(2) have "snd y = fst z" by auto
  from Cons.prems(1)
  show ?case
  proof (rule list_all_encompasses_cases)
    assume "list_all (encompasses p) [x, y, (snd y, fst x)]"
    hence "p \<in> convex hull {fst x, fst y, snd y}"
      using Cons.prems
      by (auto simp: det3_def' algebra_simps
        elim!: ccw'.sortedP_Cons ccw'.sortedP_Nil
        intro!: triangle_encompassing_polychain_of)
    thus ?case
      by (rule rev_subsetD[OF _ hull_mono]) (auto simp: \<open>snd y = fst z\<close>)
  next
    assume *: "list_all (encompasses p) ((fst x, snd y) # z # w # ws)"
    from Cons.prems
    have enc: "ws \<noteq> [] \<Longrightarrow> encompasses p (last ws)"
      by (auto simp: list_all_iff)
    have "set (map fst ((fst x, snd y)#z#w#ws)) \<subseteq> set (map fst (x # y # z # w # ws))"
      by auto
    moreover
    {
      note *
      moreover
      have "convex_polygon ((fst x, snd y) # z # w # ws)"
        by (metis convex_polygon_skip Cons.prems(2,3))
      moreover
      have "ccw'.sortedP (fst (fst x, snd y)) (map snd (butlast ((fst x, snd y) # z # w # ws)))"
        using Cons.prems(3)
        by (auto elim!: ccw'.sortedP_Cons intro!: ccw'.sortedP.Cons ccw'.sortedP.Nil
          split: if_split_asm)
      ultimately have "p \<in> convex hull set (map fst ((fst x, snd y)#z#w#ws))"
        by (rule Cons.hyps)
    }
    ultimately
    show "p \<in> convex hull set (map fst (x # y # z # w # ws))"
      by (rule subsetD[OF hull_mono])
  qed
qed

lemma segments_of_aform_empty_Affine_eq:
  assumes "segments_of_aform X = []"
  shows "Affine X = {fst X}"
proof -
  have "independent_pdevs (map snd (list_of_pdevs (nlex_pdevs (snd X)))) = [] \<longleftrightarrow>
    (list_of_pdevs (nlex_pdevs (snd X))) = []"
    by (subst independent_pdevs_eq_Nil_iff) (auto simp: list_all_iff list_of_pdevs_def )
  with assms show ?thesis
    by (force simp: aform_val_def list_of_pdevs_def Affine_def valuate_def segments_of_aform_def
      Let_def half_segments_of_aform_def inl_def)
qed

lemma not_segments_of_aform_singleton: "segments_of_aform X \<noteq> [x]"
  by (auto simp: segments_of_aform_def Let_def add_is_1 dest!: arg_cong[where f=length])

lemma encompasses_segments_of_aform_in_AffineI:
  assumes "length (segments_of_aform X) > 2"
  assumes "list_all (encompasses p) (segments_of_aform X)"
  shows "p \<in> Affine X"
proof -
  from assms(1) obtain x y z zs where eq: "segments_of_aform X = x#y#z#zs"
    by (cases "segments_of_aform X" rule: list_cases4) auto
  hence "fst x = fst (hd (half_segments_of_aform X))"
    by (metis segments_of_aform_def hd_append list.map_disc_iff list.sel(1))
  also have "\<dots> = lowest_vertex (fst X, nlex_pdevs (snd X))"
    using assms
    by (intro fst_hd_half_segments_of_aform) (auto simp: segments_of_aform_def)
  finally have fstx: "fst x = lowest_vertex (fst X, nlex_pdevs (snd X))" .
  have "p \<in> convex hull (set (map fst (segments_of_aform X)))"
    using assms(2)
    unfolding eq
  proof (rule encompasses_convex_polygon3)
    show "convex_polygon (x # y # z # zs)"
      using assms(1) unfolding eq[symmetric]
      by (intro convex_polygon_segments_of_aform) (simp add: segments_of_aform_def Let_def)
    show "ccw'.sortedP (fst x) (map snd (butlast (x # y # z # zs)))"
      using assms(1)
      unfolding fstx map_butlast eq[symmetric]
      by (intro ccw'_sortedP_snd_segments_of_aform)
        (simp add: segments_of_aform_def Let_def half_segments_of_aform_def)
  qed
  also have "\<dots> \<subseteq> convex hull (Affine X)"
  proof (rule hull_mono, safe)
    fix a b assume "(a, b) \<in> set (map fst (segments_of_aform X))"
    then obtain c d where "((a, b), c, d) \<in> set (segments_of_aform X)" by auto
    from previous_segments_of_aformE[OF this]
    obtain x where "(x, a, b) \<in> set (segments_of_aform X)" by auto
    from in_set_segments_of_aform_aform_valE[OF this]
    obtain e where "(a, b) = aform_val e X" "e \<in> UNIV \<rightarrow> {- 1..1}" by auto
    thus "(a, b) \<in> Affine X"
      by (auto simp: Affine_def valuate_def image_iff)
  qed
  also have "\<dots> = Affine X"
    by (simp add: convex_Affine convex_hull_eq)
  finally show ?thesis .
qed

end
