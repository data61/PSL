(* Author: Alexander Maletzky *)

section \<open>Dub\'{e}'s Degree-Bound for Homogeneous Gr\"obner Bases\<close>

theory Dube_Bound
  imports Poly_Fun Cone_Decomposition Degree_Bound_Utils
begin

context fixes n d :: nat
begin

function Dube_aux :: "nat \<Rightarrow> nat" where
  "Dube_aux j = (if j + 2 < n then
                  2 + ((Dube_aux (j + 1)) choose 2) + (\<Sum>i=j+3..n-1. (Dube_aux i) choose (Suc (i - j)))
                else if j + 2 = n then d\<^sup>2 + 2 * d else 2 * d)"
  by pat_completeness auto
termination proof
  show "wf (measure ((-) n))" by (fact wf_measure)
qed auto

definition Dube :: nat where "Dube = (if n \<le> 1 \<or> d = 0 then d else Dube_aux 1)"

lemma Dube_aux_ge_d: "d \<le> Dube_aux j"
proof (induct j rule: Dube_aux.induct)
  case step: (1 j)
  have "j + 2 < n \<or> j + 2 = n \<or> n < j + 2" by auto
  show ?case
  proof (rule linorder_cases)
    assume *: "j + 2 < n"
    hence 1: "d \<le> Dube_aux (j + 1)"
      by (rule step.hyps)+
    show ?thesis
    proof (cases "d \<le> 2")
      case True
      also from * have "2 \<le> Dube_aux j" by simp
      finally show ?thesis .
    next
      case False
      hence "2 < d" by simp
      hence "2 < Dube_aux (j + 1)" using 1 by (rule less_le_trans)
      with _ have "Dube_aux (j + 1) \<le> Dube_aux (j + 1) choose 2" by (rule upper_le_binomial) simp
      also from * have "\<dots> \<le> Dube_aux j" by simp
      finally have "Dube_aux (j + 1) \<le> Dube_aux j" .
      with 1 show ?thesis by (rule le_trans)
    qed
  next
    assume "j + 2 = n"
    thus ?thesis by simp
  next
    assume "n < j + 2"
    thus ?thesis by simp
  qed
qed

corollary Dube_ge_d: "d \<le> Dube"
  by (simp add: Dube_def Dube_aux_ge_d del: Dube_aux.simps)

text \<open>Dub\'{e} in @{cite Dube1990} proves the following theorem, to obtain a short closed form for
  the degree bound. However, the proof he gives is wrong: In the last-but-one proof step of Lemma 8.1
  the sum on the right-hand-side of the inequality can be greater than 1/2 (e.g. for @{prop "n = 7"},
  @{prop "d = 2"} and @{prop "j = 1"}), rendering the value inside the big brackets negative. This is
  also true without the additional summand \<open>2\<close> we had to introduce in function @{const Dube_aux} to
  correct another mistake found in @{cite Dube1990}.
  Nonetheless, experiments carried out in Mathematica still suggest that the short closed form is a
  valid upper bound for @{const Dube}, even with the additional summand \<open>2\<close>. So, with some effort it
  might be possible to prove the theorem below; but in fact function @{const Dube} gives typically
  much better (i.e. smaller) values for concrete values of \<open>n\<close> and \<open>d\<close>, so it is better to stick to
  @{const Dube} instead of the closed form anyway. Asymptotically, as \<open>n\<close> tends to infinity,
  @{const Dube} grows double exponentially, too.\<close>

theorem "rat_of_nat Dube \<le> 2 * ((rat_of_nat d)\<^sup>2 / 2 + (rat_of_nat d)) ^ (2 ^ (n - 2))"
  oops

end

subsection \<open>Hilbert Function and Hilbert Polynomial\<close>

context pm_powerprod
begin

context
  fixes X :: "'x set"
  assumes fin_X: "finite X"
begin

lemma Hilbert_fun_cone_aux:
  assumes "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" and "homogeneous (h::_ \<Rightarrow>\<^sub>0 'a::field)"
  shows "Hilbert_fun (cone (h, U)) z = card {t \<in> .[U]. deg_pm t + poly_deg h = z}"
proof -
  from assms(2) have "lpp h \<in> keys h" by (rule punit.lt_in_keys)
  with assms(4) have deg_h[symmetric]: "deg_pm (lpp h) = poly_deg h"
    by (rule homogeneousD_poly_deg)
  from assms(1, 3) have "cone (h, U) \<subseteq> P[X]" by (rule cone_subset_PolysI)
  with fin_X have "Hilbert_fun (cone (h, U)) z = card (lpp ` (hom_deg_set z (cone (h, U)) - {0}))"
    using subspace_cone[of "(h, U)"] by (simp only: Hilbert_fun_alt)
  also from assms(4) have "lpp ` (hom_deg_set z (cone (h, U)) - {0}) =
                            {t \<in> lpp ` (cone (h, U) - {0}). deg_pm t = z}"
    by (intro image_lt_hom_deg_set homogeneous_set_coneI)
  also have "{t \<in> lpp ` (cone (h, U) - {0}). deg_pm t = z} =
              (\<lambda>t. t + lpp h) ` {t \<in> .[U]. deg_pm t + poly_deg h = z}"  (is "?A = ?B")
  proof
    show "?A \<subseteq> ?B"
    proof
      fix t
      assume "t \<in> ?A"
      hence "t \<in> lpp ` (cone (h, U) - {0})" and "deg_pm t = z" by simp_all
      from this(1) obtain a where "a \<in> cone (h, U) - {0}" and 2: "t = lpp a" ..
      from this(1) have "a \<in> cone (h, U)" and "a \<noteq> 0" by simp_all
      from this(1) obtain q where "q \<in> P[U]" and a: "a = q * h" by (rule coneE)
      from \<open>a \<noteq> 0\<close> have "q \<noteq> 0" by (auto simp: a)
      hence t: "t = lpp q + lpp h" using assms(2) unfolding 2 a by (rule lp_times)
      hence "deg_pm (lpp q) + poly_deg h = deg_pm t" by (simp add: deg_pm_plus deg_h)
      also have "\<dots> = z" by fact
      finally have "deg_pm (lpp q) + poly_deg h = z" .
      moreover from \<open>q \<in> P[U]\<close> have "lpp q \<in> .[U]" by (rule PPs_closed_lpp)
      ultimately have "lpp q \<in> {t \<in> .[U]. deg_pm t + poly_deg h = z}" by simp
      moreover have "t = lpp q + lpp h" by (simp only: t)
      ultimately show "t \<in> ?B" by (rule rev_image_eqI)
    qed
  next
    show "?B \<subseteq> ?A"
    proof
      fix t
      assume "t \<in> ?B"
      then obtain s where "s \<in> {t \<in> .[U]. deg_pm t + poly_deg h = z}"
        and t1: "t = s + lpp h" ..
      from this(1) have "s \<in> .[U]" and 1: "deg_pm s + poly_deg h = z" by simp_all
      let ?q = "monomial (1::'a) s"
      have "?q \<noteq> 0" by (simp add: monomial_0_iff)
      hence "?q * h \<noteq> 0" and "lpp (?q * h) = lpp ?q + lpp h" using \<open>h \<noteq> 0\<close>
        by (rule times_not_zero, rule lp_times)
      hence t: "t = lpp (?q * h)" by (simp add: t1 punit.lt_monomial)
      from \<open>s \<in> .[U]\<close> have "?q \<in> P[U]" by (rule Polys_closed_monomial)
      with refl have "?q * h \<in> cone (h, U)" by (rule coneI)
      moreover from _ assms(2) have "?q * h \<noteq> 0" by (rule times_not_zero) (simp add: monomial_0_iff)
      ultimately have "?q * h \<in> cone (h, U) - {0}" by simp
      hence "t \<in> lpp ` (cone (h, U) - {0})" unfolding t by (rule imageI)
      moreover have "deg_pm t = int z" by (simp add: t1) (simp add: deg_pm_plus deg_h flip: 1)
      ultimately show "t \<in> ?A" by simp
    qed
  qed
  also have "card \<dots> = card {t \<in> .[U]. deg_pm t + poly_deg h = z}" by (simp add: card_image)
  finally show ?thesis .
qed

lemma Hilbert_fun_cone_empty:
  assumes "h \<in> P[X]" and "h \<noteq> 0" and "homogeneous (h::_ \<Rightarrow>\<^sub>0 'a::field)"
  shows "Hilbert_fun (cone (h, {})) z = (if poly_deg h = z then 1 else 0)"
proof -
  have "Hilbert_fun (cone (h, {})) z = card {t \<in> .[{}::'x set]. deg_pm t + poly_deg h = z}"
    using assms(1, 2) empty_subsetI assms(3) by (rule Hilbert_fun_cone_aux)
  also have "\<dots> = (if poly_deg h = z then 1 else 0)" by simp
  finally show ?thesis .
qed

lemma Hilbert_fun_cone_nonempty:
  assumes "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" and "homogeneous (h::_ \<Rightarrow>\<^sub>0 'a::field)" and "U \<noteq> {}"
  shows "Hilbert_fun (cone (h, U)) z =
          (if poly_deg h \<le> z then ((z - poly_deg h) + (card U - 1)) choose (card U - 1) else 0)"
proof (cases "poly_deg h \<le> z")
  case True
  from assms(3) fin_X have "finite U" by (rule finite_subset)
  from assms(1-4) have "Hilbert_fun (cone (h, U)) z = card {t \<in> .[U]. deg_pm t + poly_deg h = z}"
    by (rule Hilbert_fun_cone_aux)
  also from True have "{t \<in> .[U]. deg_pm t + poly_deg h = z} = deg_sect U (z - poly_deg h)"
    by (auto simp: deg_sect_def)
  also from \<open>finite U\<close> assms(5) have "card \<dots> = (z - poly_deg h) + (card U - 1) choose (card U - 1)"
    by (rule card_deg_sect)
  finally show ?thesis by (simp add: True)
next
  case False
  from assms(1-4) have "Hilbert_fun (cone (h, U)) z = card {t \<in> .[U]. deg_pm t + poly_deg h = z}"
    by (rule Hilbert_fun_cone_aux)
  also from False have "{t \<in> .[U]. deg_pm t + poly_deg h = z} = {}" by auto
  hence "card {t \<in> .[U]. deg_pm t + poly_deg h = z} = card ({}::('x \<Rightarrow>\<^sub>0 nat) set)" by (rule arg_cong)
  also have "\<dots> = 0" by simp
  finally show ?thesis by (simp add: False)
qed

corollary Hilbert_fun_Polys:
  assumes "X \<noteq> {}"
  shows "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a::field) set) z = (z + (card X - 1)) choose (card X - 1)"
proof -
  let ?one = "1::('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a"
  have "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) z = Hilbert_fun (cone (?one, X)) z" by simp
  also have "\<dots> = (if poly_deg ?one \<le> z then ((z - poly_deg ?one) + (card X - 1)) choose (card X - 1) else 0)"
    using one_in_Polys _ subset_refl _ assms by (rule Hilbert_fun_cone_nonempty) simp_all
  also have "\<dots> = (z + (card X - 1)) choose (card X - 1)" by simp
  finally show ?thesis .
qed

lemma Hilbert_fun_cone_decomp:
  assumes "cone_decomp T ps" and "valid_decomp X ps" and "hom_decomp ps"
  shows "Hilbert_fun T z = (\<Sum>hU\<in>set ps. Hilbert_fun (cone hU) z)"
proof -
  note fin_X
  moreover from assms(2, 1) have "T \<subseteq> P[X]" by (rule valid_cone_decomp_subset_Polys)
  moreover from assms(1) have dd: "direct_decomp T (map cone ps)" by (rule cone_decompD)
  ultimately have "Hilbert_fun T z = (\<Sum>s\<in>set (map cone ps). Hilbert_fun s z)"
  proof (rule Hilbert_fun_direct_decomp)
    fix cn
    assume "cn \<in> set (map cone ps)"
    then obtain hU where "hU \<in> set ps" and cn: "cn = cone hU" unfolding set_map ..
    note this(1)
    moreover obtain h U where hU: "hU = (h, U)" using prod.exhaust by blast
    ultimately have "(h, U) \<in> set ps" by simp
    with assms(3) have "homogeneous h" by (rule hom_decompD)
    thus "homogeneous_set cn" unfolding cn hU by (rule homogeneous_set_coneI)
    show "phull.subspace cn" unfolding cn by (fact subspace_cone)
  qed
  also have "\<dots> = (\<Sum>hU\<in>set ps. ((\<lambda>s. Hilbert_fun s z) \<circ> cone) hU)" unfolding set_map using finite_set
  proof (rule sum.reindex_nontrivial)
    fix hU1 hU2
    assume "hU1 \<in> set ps" and "hU2 \<in> set ps" and "hU1 \<noteq> hU2"
    with dd have "cone hU1 \<inter> cone hU2 = {0}" using zero_in_cone by (rule direct_decomp_map_Int_zero)
    moreover assume "cone hU1 = cone hU2"
    ultimately show "Hilbert_fun (cone hU1) z = 0" by simp
  qed
  finally show ?thesis by simp
qed

definition Hilbert_poly :: "(nat \<Rightarrow> nat) \<Rightarrow> int \<Rightarrow> int"
  where "Hilbert_poly b =
                (\<lambda>z::int. let n = card X in
                  ((z - b (Suc n) + n) gchoose n) - 1 - (\<Sum>i=1..n. (z - b i + i - 1) gchoose i))"

lemma poly_fun_Hilbert_poly: "poly_fun (Hilbert_poly b)"
  by (simp add: Hilbert_poly_def Let_def)

lemma Hilbert_fun_eq_Hilbert_poly_plus_card:
  assumes "X \<noteq> {}" and "valid_decomp X ps" and "hom_decomp ps" and "cone_decomp T ps"
    and "standard_decomp k ps" and "exact_decomp X 0 ps" and "\<b> ps (Suc 0) \<le> d"
  shows "int (Hilbert_fun T d) = card {h::_ \<Rightarrow>\<^sub>0 'a::field. (h, {}) \<in> set ps \<and> poly_deg h = d} + Hilbert_poly (\<b> ps) d"
proof -
  define n where "n = card X"
  with assms(1) have "0 < n" using fin_X by (simp add: card_gt_0_iff)
  hence "1 \<le> n" and "Suc 0 \<le> n" by simp_all
  from pos_decomp_subset have eq0: "(set ps - set (ps\<^sub>+)) \<union> set (ps\<^sub>+) = set ps" by blast
  have "set ps - set (ps\<^sub>+) \<subseteq> set ps" by blast
  hence fin2: "finite (set ps - set (ps\<^sub>+))" using finite_set by (rule finite_subset)

  have "(\<Sum>hU\<in>set ps - set (ps\<^sub>+). Hilbert_fun (cone hU) d) =
        (\<Sum>(h, U)\<in>set ps - set (ps\<^sub>+). if poly_deg h = d then 1 else 0)"
    using refl
  proof (rule sum.cong)
    fix x
    assume "x \<in> set ps - set (ps\<^sub>+)"
    moreover obtain h U where x: "x = (h, U)" using prod.exhaust by blast
    ultimately have "U = {}" and "(h, U) \<in> set ps" by (simp_all add: pos_decomp_def)
    from assms(2) this(2) have "h \<in> P[X]" and "h \<noteq> 0" by (rule valid_decompD)+
    moreover from assms(3) \<open>(h, U) \<in> set ps\<close> have "homogeneous h" by (rule hom_decompD)
    ultimately show "Hilbert_fun (cone x) d = (case x of (h, U) \<Rightarrow> if poly_deg h = d then 1 else 0)"
      by (simp add: x \<open>U = {}\<close> Hilbert_fun_cone_empty split del: if_split)
  qed
  also from fin2 have "\<dots> = (\<Sum>(h, U)\<in>{(h', U') \<in> set ps - set (ps\<^sub>+). poly_deg h' = d}. 1)"
    by (rule sum.mono_neutral_cong_right) (auto split: if_splits)
  also have "\<dots> = card {(h, U) \<in> set ps - set (ps\<^sub>+). poly_deg h = d}" by auto
  also have "\<dots> = card {h. (h, {}) \<in> set ps \<and> poly_deg h = d}" by (fact card_Diff_pos_decomp)
  finally have eq1: "(\<Sum>hU\<in>set ps - set (ps\<^sub>+). Hilbert_fun (cone hU) d) =
                      card {h. (h, {}) \<in> set ps \<and> poly_deg h = d}" .

  let ?f = "\<lambda>a b. (int d) - a + b gchoose b"
  have "int (\<Sum>hU\<in>set (ps\<^sub>+). Hilbert_fun (cone hU) d) = (\<Sum>hU\<in>set (ps\<^sub>+). int (Hilbert_fun (cone hU) d))"
    by (simp add: int_sum prod.case_distrib)
  also have "\<dots> = (\<Sum>(h, U)\<in>(\<Union>i\<in>{1..n}. {(h, U) \<in> set (ps\<^sub>+). card U = i}). ?f (poly_deg h) (card U - 1))"
  proof (rule sum.cong)
    show "set (ps\<^sub>+) = (\<Union>i\<in>{1..n}. {(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = i})"
    proof (rule Set.set_eqI, rule)
      fix x
      assume "x \<in> set (ps\<^sub>+)"
      moreover obtain h U where x: "x = (h, U)" using prod.exhaust by blast
      ultimately have "(h, U) \<in> set (ps\<^sub>+)" by simp
      hence "(h, U) \<in> set ps" and "U \<noteq> {}" by (simp_all add: pos_decomp_def)
      from fin_X assms(6) this(1) have "U \<subseteq> X" by (rule exact_decompD)
      hence "finite U" using fin_X by (rule finite_subset)
      with \<open>U \<noteq> {}\<close> have "0 < card U" by (simp add: card_gt_0_iff)
      moreover from fin_X \<open>U \<subseteq> X\<close> have "card U \<le> n" unfolding n_def by (rule card_mono)
      ultimately have "card U \<in> {1..n}" by simp
      moreover from \<open>(h, U) \<in> set (ps\<^sub>+)\<close> have "(h, U) \<in> {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> card U' = card U}"
        by simp
      ultimately show "x \<in> (\<Union>i\<in>{1..n}. {(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = i})" by (simp add: x)
    qed blast
  next
    fix x
    assume "x \<in> (\<Union>i\<in>{1..n}. {(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = i})"
    then obtain j where "j \<in> {1..n}" and "x \<in> {(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = j}" ..
    from this(2) obtain h U where "(h, U) \<in> set (ps\<^sub>+)" and "card U = j" and x: "x = (h, U)" by blast
    from fin_X assms(2, 5) this(1) have "poly_deg h < \<b> ps (Suc 0)" by (rule \<b>_one_gr)
    also have "\<dots> \<le> d" by fact
    finally have "poly_deg h < d" .
    hence int1: "int (d - poly_deg h) = int d - int (poly_deg h)" by simp
    from \<open>card U = j\<close> \<open>j \<in> {1..n}\<close> have "0 < card U" by simp
    hence int2: "int (card U - Suc 0) = int (card U) - 1" by simp
    from \<open>(h, U) \<in> set (ps\<^sub>+)\<close> have "(h, U) \<in> set ps" using pos_decomp_subset ..
    with assms(2) have "h \<in> P[X]" and "h \<noteq> 0" and "U \<subseteq> X" by (rule valid_decompD)+
    moreover from assms(3) \<open>(h, U) \<in> set ps\<close> have "homogeneous h" by (rule hom_decompD)
    moreover from \<open>0 < card U\<close> have "U \<noteq> {}" by auto
    ultimately have "Hilbert_fun (cone (h, U)) d =
                (if poly_deg h \<le> d then (d - poly_deg h + (card U - 1)) choose (card U - 1) else 0)"
      by (rule Hilbert_fun_cone_nonempty)
    also from \<open>poly_deg h < d\<close> have "\<dots> = (d - poly_deg h + (card U - 1)) choose (card U - 1)" by simp
    finally
    have "int (Hilbert_fun (cone (h, U)) d) = (int d - int (poly_deg h) + (int (card U - 1))) gchoose (card U - 1)"
      by (simp add: int_binomial int1 int2)
    thus "int (Hilbert_fun (cone x) d) =
          (case x of (h, U) \<Rightarrow> int d - int (poly_deg h) + (int (card U - 1)) gchoose (card U - 1))"
      by (simp add: x)
  qed
  also have "\<dots> = (\<Sum>j=1..n. \<Sum>(h, U)\<in>{(h', U') \<in> set (ps\<^sub>+). card U' = j}. ?f (poly_deg h) (card U - 1))"
  proof (intro sum.UNION_disjoint ballI)
    fix j
    have "{(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = j} \<subseteq> set (ps\<^sub>+)" by blast
    thus "finite {(h, U). (h, U) \<in> set (ps\<^sub>+) \<and> card U = j}" using finite_set by (rule finite_subset)
  qed blast+
  also from refl have "\<dots> = (\<Sum>j=1..n. ?f (\<b> ps (Suc j)) j - ?f (\<b> ps j) j)"
  proof (rule sum.cong)
    fix j
    assume "j \<in> {1..n}"
    hence "Suc 0 \<le> j" and "0 < j" and "j \<le> n" by simp_all
    from fin_X this(1) have "\<b> ps j \<le> \<b> ps (Suc 0)" by (rule \<b>_decreasing)
    also have "\<dots> \<le> d" by fact
    finally have "\<b> ps j \<le> d" .
    from fin_X have "\<b> ps (Suc j) \<le> \<b> ps j" by (rule \<b>_decreasing) simp
    hence "\<b> ps (Suc j) \<le> d" using \<open>\<b> ps j \<le> d\<close> by (rule le_trans)
    from \<open>0 < j\<close> have int_j: "int (j - Suc 0) = int j - 1" by simp
    have "(\<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> card U' = j}. ?f (poly_deg h) (card U - 1)) =
         (\<Sum>(h, U)\<in>(\<Union>d0\<in>{\<b> ps (Suc j)..int (\<b> ps j) - 1}. {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> int (poly_deg h') = d0 \<and> card U' = j}).
            ?f (poly_deg h) (card U - 1))"
      using _ refl
    proof (rule sum.cong)
      show "{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> card U' = j} =
            (\<Union>d0\<in>{\<b> ps (Suc j)..int (\<b> ps j) - 1}. {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> int (poly_deg h') = d0 \<and> card U' = j})"
      proof (rule Set.set_eqI, rule)
        fix x
        assume "x \<in> {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> card U' = j}"
        moreover obtain h U where x: "x = (h, U)" using prod.exhaust by blast
        ultimately have "(h, U) \<in> set (ps\<^sub>+)" and "card U = j" by simp_all
        with fin_X assms(5, 6) \<open>Suc 0 \<le> j\<close> \<open>j \<le> n\<close> have "\<b> ps (Suc j) \<le> poly_deg h"
          unfolding n_def by (rule lem_6_1_3)
        moreover from fin_X have "poly_deg h < \<b> ps j"
        proof (rule \<b>)
          from \<open>(h, U) \<in> set (ps\<^sub>+)\<close> show "(h, U) \<in> set ps" using pos_decomp_subset ..
        next
          show "j \<le> card U" by (simp add: \<open>card U = j\<close>)
        qed
        ultimately have "poly_deg h \<in> {\<b> ps (Suc j)..int (\<b> ps j) - 1}" by simp
        moreover have "(h, U) \<in> {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = poly_deg h \<and> card U' = card U}"
          using \<open>(h, U) \<in> set (ps\<^sub>+)\<close> by simp
        ultimately show "x \<in> (\<Union>d0\<in>{\<b> ps (Suc j)..int (\<b> ps j) - 1}.
                                {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> int (poly_deg h') = d0 \<and> card U' = j})"
          by (simp add: x \<open>card U = j\<close>)
      qed blast
    qed
    also have "\<dots> = (\<Sum>d0=\<b> ps (Suc j)..int (\<b> ps j) - 1.
                        \<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j}.
                            ?f (poly_deg h) (card U - 1))"
    proof (intro sum.UNION_disjoint ballI)
      fix d0::int
      have "{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j} \<subseteq> set (ps\<^sub>+)" by blast
      thus "finite {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j}"
        using finite_set by (rule finite_subset)
    qed blast+
    also from refl have "\<dots> = (\<Sum>d0=\<b> ps (Suc j)..int (\<b> ps j) - 1. ?f d0 (j - 1))"
    proof (rule sum.cong)
      fix d0
      assume "d0 \<in> {\<b> ps (Suc j)..int (\<b> ps j) - 1}"
      hence "\<b> ps (Suc j) \<le> d0" and "d0 < int (\<b> ps j)" by simp_all
      hence "\<b> ps (Suc j) \<le> nat d0" and "nat d0 < \<b> ps j" by simp_all
      have "(\<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j}. ?f (poly_deg h) (card U - 1)) =
            (\<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j}. ?f d0 (j - 1))"
        using refl by (rule sum.cong) auto
      also have "\<dots> = card {(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = nat d0 \<and> card U' = j} * ?f d0 (j - 1)"
        using \<open>\<b> ps (Suc j) \<le> d0\<close> by (simp add: int_eq_iff)
      also have "\<dots> = ?f d0 (j - 1)"
        using fin_X assms(5, 6) \<open>Suc 0 \<le> j\<close> \<open>j \<le> n\<close> \<open>\<b> ps (Suc j) \<le> nat d0\<close> \<open>nat d0 < \<b> ps j\<close>
        by (simp only: n_def lem_6_1_2'(3))
      finally show "(\<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> poly_deg h' = d0 \<and> card U' = j}.
                      ?f (poly_deg h) (card U - 1)) = ?f d0 (j - 1)" .
    qed
    also have "\<dots> = (\<Sum>d0\<in>(-) (int d) ` {\<b> ps (Suc j)..int (\<b> ps j) - 1}. d0 + int (j - 1) gchoose (j - 1))"
    proof -
      have "inj_on ((-) (int d)) {\<b> ps (Suc j)..int (\<b> ps j) - 1}" by (auto simp: inj_on_def)
      thus ?thesis by (simp only: sum.reindex o_def)
    qed
    also have "\<dots> = (\<Sum>d0\<in>{0..int d - (\<b> ps (Suc j))}-{0..int d - \<b> ps j}. d0 + int (j - 1) gchoose (j - 1))"
      using _ refl
    proof (rule sum.cong)
      have "(-) (int d) ` {\<b> ps (Suc j)..int (\<b> ps j) - 1} = {int d - (int (\<b> ps j) - 1)..int d - int (\<b> ps (Suc j))}"
        by (simp only: image_diff_atLeastAtMost)
      also have "\<dots> = {0..int d - int (\<b> ps (Suc j))} - {0..int d - int (\<b> ps j)}"
      proof -
        from \<open>\<b> ps j \<le> d\<close> have "int (\<b> ps j) - 1 \<le> int d" by simp
        thus ?thesis by auto
      qed
      finally show "(-) (int d) ` {\<b> ps (Suc j)..int (\<b> ps j) - 1} =
                    {0..int d - int (\<b> ps (Suc j))} - {0..int d - int (\<b> ps j)}" .
    qed
    also have "\<dots> = (\<Sum>d0=0..int d - (\<b> ps (Suc j)). d0 + int (j - 1) gchoose (j - 1)) -
                    (\<Sum>d0=0..int d - \<b> ps j. d0 + int (j - 1) gchoose (j - 1))"
      by (rule sum_diff) (auto simp: \<open>\<b> ps (Suc j) \<le> \<b> ps j\<close>)
    also from \<open>\<b> ps (Suc j) \<le> d\<close> \<open>\<b> ps j \<le> d\<close> have "\<dots> = ?f (\<b> ps (Suc j)) j - ?f (\<b> ps j) j"
      by (simp add: gchoose_rising_sum, simp add: int_j ac_simps \<open>0 < j\<close>)
    finally show "(\<Sum>(h, U)\<in>{(h', U'). (h', U') \<in> set (ps\<^sub>+) \<and> card U' = j}. ?f (poly_deg h) (card U - 1)) =
                    ?f (\<b> ps (Suc j)) j - ?f (\<b> ps j) j" .
  qed
  also have "\<dots> = (\<Sum>j=1..n. ?f (\<b> ps (Suc j)) j) - (\<Sum>j=1..n. ?f (\<b> ps j) j)"
    by (fact sum_subtractf)
  also have "\<dots> = ?f (\<b> ps (Suc n)) n + (\<Sum>j=1..n-1. ?f (\<b> ps (Suc j)) j) - (\<Sum>j=1..n. ?f (\<b> ps j) j)"
    by (simp only: sum_tail_nat[OF \<open>0 < n\<close> \<open>1 \<le> n\<close>])
  also have "\<dots> = ?f (\<b> ps (Suc n)) n - ?f (\<b> ps 1) 1 +
                  ((\<Sum>j=1..n-1. ?f (\<b> ps (Suc j)) j) - (\<Sum>j=1..n-1. ?f (\<b> ps (Suc j)) (Suc j)))"
    by (simp only: sum.atLeast_Suc_atMost[OF \<open>1 \<le> n\<close>] sum_atLeast_Suc_shift[OF \<open>0 < n\<close> \<open>1 \<le> n\<close>])
  also have "\<dots> = ?f (\<b> ps (Suc n)) n - ?f (\<b> ps 1) 1 -
                  (\<Sum>j=1..n-1. ?f (\<b> ps (Suc j)) (Suc j) - ?f (\<b> ps (Suc j)) j)"
    by (simp only: sum_subtractf)
  also have "\<dots> = ?f (\<b> ps (Suc n)) n - 1 - ((int d - \<b> ps (Suc 0)) gchoose (Suc 0)) -
                  (\<Sum>j=1..n-1. (int d - \<b> ps (Suc j) + j) gchoose (Suc j))"
  proof -
    have "?f (\<b> ps 1) 1 = 1 + ((int d - \<b> ps (Suc 0)) gchoose (Suc 0))"
      by (simp add: plus_Suc_gbinomial)
    moreover from refl have "(\<Sum>j=1..n-1. ?f (\<b> ps (Suc j)) (Suc j) - ?f (\<b> ps (Suc j)) j) =
                              (\<Sum>j=1..n-1. (int d - \<b> ps (Suc j) + j) gchoose (Suc j))"
      by (rule sum.cong) (simp add: plus_Suc_gbinomial)
    ultimately show ?thesis by (simp only:)
  qed
  also have "\<dots> = ?f (\<b> ps (Suc n)) n - 1 - (\<Sum>j=0..n-1. (int d - \<b> ps (Suc j) + j) gchoose (Suc j))"
    by (simp only: sum.atLeast_Suc_atMost[OF le0], simp)
  also have "\<dots> = ?f (\<b> ps (Suc n)) n - 1 - (\<Sum>j=Suc 0..Suc (n-1). (int d - \<b> ps j + j - 1) gchoose j)"
    by (simp only: sum.shift_bounds_cl_Suc_ivl, simp add: ac_simps)
  also have "\<dots> = Hilbert_poly (\<b> ps) d" using \<open>0 < n\<close> by (simp add: Hilbert_poly_def Let_def n_def)
  finally have eq2: "int (\<Sum>hU\<in>set (ps\<^sub>+). Hilbert_fun (cone hU) d) = Hilbert_poly (\<b> ps) (int d)" .

  from assms(4, 2, 3) have "Hilbert_fun T d = (\<Sum>hU\<in>set ps. Hilbert_fun (cone hU) d)"
    by (rule Hilbert_fun_cone_decomp)
  also have "\<dots> = (\<Sum>hU\<in>(set ps - set (ps\<^sub>+)) \<union> set (ps\<^sub>+). Hilbert_fun (cone hU) d)" by (simp only: eq0)
  also have "\<dots> = (\<Sum>hU\<in>set ps - set (ps\<^sub>+). Hilbert_fun (cone hU) d) + (\<Sum>hU\<in>set (ps\<^sub>+). Hilbert_fun (cone hU) d)"
    using fin2 finite_set by (rule sum.union_disjoint) blast
  also have "\<dots> = card {h. (h, {}) \<in> set ps \<and> poly_deg h = d} + (\<Sum>hU\<in>set (ps\<^sub>+). Hilbert_fun (cone hU) d)"
    by (simp only: eq1)
  also have "int \<dots> = card {h. (h, {}) \<in> set ps \<and> poly_deg h = d} + Hilbert_poly (\<b> ps) d"
    by (simp only: eq2 int_plus)
  finally show ?thesis .
qed

corollary Hilbert_fun_eq_Hilbert_poly:
  assumes "X \<noteq> {}" and "valid_decomp X ps" and "hom_decomp ps" and "cone_decomp T ps"
    and "standard_decomp k ps" and "exact_decomp X 0 ps" and "\<b> ps 0 \<le> d"
  shows "int (Hilbert_fun (T::(_ \<Rightarrow>\<^sub>0 'a::field) set) d) = Hilbert_poly (\<b> ps) d"
proof -
  from fin_X have "\<b> ps (Suc 0) \<le> \<b> ps 0" using le0 by (rule \<b>_decreasing)
  also have "\<dots> \<le> d" by fact
  finally have "\<b> ps (Suc 0) \<le> d" .
  with assms(1-6) have "int (Hilbert_fun T d) =
                int (card {h. (h, {}) \<in> set ps \<and> poly_deg h = d}) + Hilbert_poly (\<b> ps) (int d)"
    by (rule Hilbert_fun_eq_Hilbert_poly_plus_card)
  also have "\<dots> = Hilbert_poly (\<b> ps) (int d)"
  proof -
    have eq: "{h. (h, {}) \<in> set ps \<and> poly_deg h = d} = {}"
    proof -
      {
        fix h
        assume "(h, {}) \<in> set ps" and "poly_deg h = d"
        from fin_X this(1) le0 have "poly_deg h < \<b> ps 0" by (rule \<b>)
        with assms(7) have False by (simp add: \<open>poly_deg h = d\<close>)
      }
      thus ?thesis by blast
    qed
    show ?thesis by (simp add: eq)
  qed
  finally show ?thesis .
qed

subsection \<open>Dub\'{e}'s Bound\<close>

context
  fixes f :: "('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field"
  fixes F
  assumes n_gr_1: "1 < card X" and fin_F: "finite F" and F_sub: "F \<subseteq> P[X]" and f_in: "f \<in> F"
    and hom_F: "\<And>f'. f' \<in> F \<Longrightarrow> homogeneous f'" and f_max: "\<And>f'. f' \<in> F \<Longrightarrow> poly_deg f' \<le> poly_deg f"
    and d_gr_0: "0 < poly_deg f" and ideal_f_neq: "ideal {f} \<noteq> ideal F"
begin

private abbreviation (input) "n \<equiv> card X"
private abbreviation (input) "d \<equiv> poly_deg f"

lemma f_in_Polys: "f \<in> P[X]"
  using f_in F_sub ..

lemma hom_f: "homogeneous f"
  using f_in by (rule hom_F)

lemma f_not_0: "f \<noteq> 0"
  using d_gr_0 by auto

lemma X_not_empty: "X \<noteq> {}"
  using n_gr_1 by auto

lemma n_gr_0: "0 < n"
  using \<open>1 < n\<close> by simp

corollary int_n_minus_1 [simp]: "int (n - Suc 0) = int n - 1"
  using n_gr_0 by simp

lemma int_n_minus_2 [simp]: "int (n - Suc (Suc 0)) = int n - 2"
  using n_gr_1 by simp

lemma cone_f_X_sub: "cone (f, X) \<subseteq> P[X]"
proof -
  have "cone (f, X) = cone (f * 1, X)" by simp
  also from f_in_Polys have "\<dots> \<subseteq> cone (1, X)" by (rule cone_mono_1)
  finally show ?thesis by simp
qed

lemma ideal_Int_Polys_eq_cone: "ideal {f} \<inter> P[X] = cone (f, X)"
proof (intro subset_antisym subsetI)
  fix p
  assume "p \<in> ideal {f} \<inter> P[X]"
  hence "p \<in> ideal {f}" and "p \<in> P[X]" by simp_all
  have "finite {f}" by simp
  then obtain q where "p = (\<Sum>f'\<in>{f}. q f' * f')" using \<open>p \<in> ideal {f}\<close>
    by (rule ideal.span_finiteE)
  hence p: "p = q f * f" by simp
  with \<open>p \<in> P[X]\<close> have "f * q f \<in> P[X]" by (simp only: mult.commute)
  hence "q f \<in> P[X]" using f_in_Polys f_not_0 by (rule times_in_PolysD)
  with p show "p \<in> cone (f, X)" by (rule coneI)
next
  fix p
  assume "p \<in> cone (f, X)"
  then obtain q where "q \<in> P[X]" and p: "p = q * f" by (rule coneE)
  have "f \<in> ideal {f}" by (rule ideal.span_base) simp
  with \<open>q \<in> P[X]\<close> f_in_Polys show "p \<in> ideal {f} \<inter> P[X]"
    unfolding p by (intro IntI ideal.span_scale Polys_closed_times)
qed

private definition P_ps where
  "P_ps = (SOME x. valid_decomp X (snd x) \<and> standard_decomp d (snd x) \<and>
                        exact_decomp X 0 (snd x) \<and> cone_decomp (fst x) (snd x) \<and> hom_decomp (snd x) \<and>
                        direct_decomp (ideal F \<inter> P[X]) [ideal {f} \<inter> P[X], fst x])"

private definition P where "P = fst P_ps"

private definition ps where "ps = snd P_ps"

lemma
  shows valid_ps: "valid_decomp X ps" (is ?thesis1)
    and std_ps: "standard_decomp d ps" (is ?thesis2)
    and ext_ps: "exact_decomp X 0 ps" (is ?thesis3)
    and cn_ps: "cone_decomp P ps" (is ?thesis4)
    and hom_ps: "hom_decomp ps" (is ?thesis5)
    and decomp_F: "direct_decomp (ideal F \<inter> P[X]) [ideal {f} \<inter> P[X], P]" (is ?thesis6)
proof -
  note fin_X
  moreover from fin_F have "finite (F - {f})" by simp
  moreover from F_sub have "F - {f} \<subseteq> P[X]" by blast
  ultimately obtain P' ps' where 1: "valid_decomp X ps'" and 2: "standard_decomp d ps'"
    and 3: "cone_decomp P' ps'" and 40: "(\<And>f'. f' \<in> F - {f} \<Longrightarrow> homogeneous f') \<Longrightarrow> hom_decomp ps'"
    and 50: "direct_decomp (ideal (insert f (F - {f})) \<inter> P[X]) [ideal {f} \<inter> P[X], P']"
    using f_in_Polys f_max by (rule ideal_decompE) blast+
  have 4: "hom_decomp ps'" by (intro 40 hom_F) simp
  from 50 f_in have 5: "direct_decomp (ideal F \<inter> P[X]) [ideal {f} \<inter> P[X], P']"
    by (simp add: insert_absorb)
  let ?ps = "exact X (poly_deg f) ps'"
  from fin_X 1 2 have "valid_decomp X ?ps" and "standard_decomp d ?ps" and "exact_decomp X 0 ?ps"
    by (rule exact)+
  moreover from fin_X 1 2 3 have "cone_decomp P' ?ps" by (rule cone_decomp_exact)
  moreover from fin_X 1 2 4 have "hom_decomp ?ps" by (rule hom_decomp_exact)
  ultimately have "valid_decomp X (snd (P', ?ps)) \<and> standard_decomp d (snd (P', ?ps)) \<and>
                    exact_decomp X 0 (snd (P', ?ps)) \<and> cone_decomp (fst (P', ?ps)) (snd (P', ?ps)) \<and>
                    hom_decomp (snd (P', ?ps)) \<and>
                    direct_decomp (ideal F \<inter> P[X]) [ideal {f} \<inter> P[X], fst (P', ?ps)]"
    using 5 by simp
  hence "?thesis1 \<and> ?thesis2 \<and> ?thesis3 \<and> ?thesis4 \<and> ?thesis5 \<and> ?thesis6"
    unfolding P_def ps_def P_ps_def by (rule someI)
  thus ?thesis1 and ?thesis2 and ?thesis3 and ?thesis4 and ?thesis5 and ?thesis6 by simp_all
qed

lemma P_sub: "P \<subseteq> P[X]"
  using valid_ps cn_ps by (rule valid_cone_decomp_subset_Polys)

lemma ps_not_Nil: "ps\<^sub>+ \<noteq> []"
proof
  assume "ps\<^sub>+ = []"
  have "Keys P \<subseteq> (\<Union>hU\<in>set ps. keys (fst hU))" (is "_ \<subseteq> ?A")
  proof
    fix t
    assume "t \<in> Keys P"
    then obtain p where "p \<in> P" and "t \<in> keys p" by (rule in_KeysE)
    from cn_ps have "direct_decomp P (map cone ps)" by (rule cone_decompD)
    then obtain qs where qs: "qs \<in> listset (map cone ps)" and p: "p = sum_list qs" using \<open>p \<in> P\<close>
      by (rule direct_decompE)
    from \<open>t \<in> keys p\<close> keys_sum_list_subset have "t \<in> Keys (set qs)" unfolding p ..
    then obtain q where "q \<in> set qs" and "t \<in> keys q" by (rule in_KeysE)
    from this(1) obtain i where "i < length qs" and "q = qs ! i" by (metis in_set_conv_nth)
    with qs have "i < length ps" and "q \<in> (map cone ps) ! i" by (simp_all add: listsetD del: nth_map)
    hence "q \<in> cone (ps ! i)" by simp
    obtain h U where eq: "ps ! i = (h, U)" using prod.exhaust by blast
    from \<open>i < length ps\<close> this[symmetric] have "(h, U) \<in> set ps" by simp
    have "U = {}"
    proof (rule ccontr)
      assume "U \<noteq> {}"
      with \<open>(h, U) \<in> set ps\<close> have "(h, U) \<in> set (ps\<^sub>+)" by (simp add: pos_decomp_def)
      with \<open>ps\<^sub>+ = []\<close> show False by simp
    qed
    with \<open>q \<in> cone (ps ! i)\<close> have "q \<in> range (\<lambda>c. c \<cdot> h)" by (simp only: eq cone_empty)
    then obtain c where "q = c \<cdot> h" ..
    also have "keys \<dots> \<subseteq> keys h" by (fact keys_map_scale_subset)
    finally have "t \<in> keys h" using \<open>t \<in> keys q\<close> ..
    hence "t \<in> keys (fst (h, U))" by simp
    with \<open>(h, U) \<in> set ps\<close> show "t \<in> ?A" ..
  qed
  moreover from finite_set finite_keys have "finite ?A" by (rule finite_UN_I)
  ultimately have "finite (Keys P)" by (rule finite_subset)

  have "\<exists>q\<in>ideal F. q \<in> P[X] \<and> q \<noteq> 0 \<and> \<not> lpp f adds lpp q"
  proof (rule ccontr)
    assume "\<not> (\<exists>q\<in>ideal F. q \<in> P[X] \<and> q \<noteq> 0 \<and> \<not> lpp f adds lpp q)"
    hence adds: "lpp f adds lpp q" if "q \<in> ideal F" and "q \<in> P[X]" and "q \<noteq> 0" for q
      using that by blast
    from fin_X _ F_sub have "ideal {f} = ideal F"
    proof (rule punit.pmdl_eqI_adds_lt_dgrad_p_set[simplified, OF dickson_grading_varnum,
          where m=0, simplified dgrad_p_set_varnum])
      from f_in_Polys show "{f} \<subseteq> P[X]" by simp
    next
      from f_in have "{f} \<subseteq> F" by simp
      thus "ideal {f} \<subseteq> ideal F" by (rule ideal.span_mono)
    next
      fix q
      assume "q \<in> ideal F" and "q \<in> P[X]" and "q \<noteq> 0"
      hence "lpp f adds lpp q" by (rule adds)
      with f_not_0 show "\<exists>g\<in>{f}. g \<noteq> 0 \<and> lpp g adds lpp q" by blast
    qed
    with ideal_f_neq show False ..
  qed
  then obtain q0 where "q0 \<in> ideal F" and "q0 \<in> P[X]" and "q0 \<noteq> 0"
    and nadds_q0: "\<not> lpp f adds lpp q0" by blast
  define q where "q = hom_component q0 (deg_pm (lpp q0))"
  from hom_F \<open>q0 \<in> ideal F\<close> have "q \<in> ideal F" unfolding q_def by (rule homogeneous_ideal)
  from homogeneous_set_Polys \<open>q0 \<in> P[X]\<close> have "q \<in> P[X]" unfolding q_def by (rule homogeneous_setD)
  from \<open>q0 \<noteq> 0\<close> have "q \<noteq> 0" and "lpp q = lpp q0" unfolding q_def by (rule hom_component_lpp)+
  from nadds_q0 this(2) have nadds_q: "\<not> lpp f adds lpp q" by simp
  have hom_q: "homogeneous q" by (simp only: q_def homogeneous_hom_component)
  from nadds_q obtain x where x: "\<not> lookup (lpp f) x \<le> lookup (lpp q) x"
    by (auto simp add: adds_poly_mapping le_fun_def)
  obtain y where "y \<in> X" and "y \<noteq> x"
  proof -
    from n_gr_1 have "2 \<le> n" by simp
    then obtain Y where "Y \<subseteq> X" and "card Y = 2" by (rule card_geq_ex_subset)
    from this(2) obtain u v where "u \<noteq> v" and "Y = {u, v}" by (rule card_2_E)
    from this obtain y where "y \<in> Y" and "y \<noteq> x" by blast
    from this(1) \<open>Y \<subseteq> X\<close> have "y \<in> X" ..
    thus ?thesis using \<open>y \<noteq> x\<close> ..
  qed
  define q' where "q' = (\<lambda>k. punit.monom_mult 1 (Poly_Mapping.single y k) q)"
  have inj1: "inj q'" by (auto intro!: injI simp: q'_def \<open>q \<noteq> 0\<close> dest: punit.monom_mult_inj_2 monomial_inj)
  have q'_in: "q' k \<in> ideal F \<inter> P[X]" for k unfolding q'_def using \<open>q \<in> ideal F\<close> \<open>q \<in> P[X]\<close> \<open>y \<in> X\<close>
    by (intro IntI punit.pmdl_closed_monom_mult[simplified] Polys_closed_monom_mult PPs_closed_single)
  have lpp_q': "lpp (q' k) = Poly_Mapping.single y k + lpp q" for k
    using \<open>q \<noteq> 0\<close> by (simp add: q'_def punit.lt_monom_mult)
  have inj2: "inj_on (deg_pm \<circ> lpp) (range q')"
    by (auto intro!: inj_onI simp: lpp_q' deg_pm_plus deg_pm_single dest: monomial_inj)
  have "(deg_pm \<circ> lpp) ` range q' \<subseteq> deg_pm ` Keys P"
  proof
    fix d
    assume "d \<in> (deg_pm \<circ> lpp) ` range q'"
    then obtain k where d: "d = deg_pm (lpp (q' k))" (is "_ = deg_pm ?t") by auto
    from hom_q have hom_q': "homogeneous (q' k)" by (simp add: q'_def homogeneous_monom_mult)
    from \<open>q \<noteq> 0\<close> have "q' k \<noteq> 0" by (simp add: q'_def punit.monom_mult_eq_zero_iff)
    hence "?t \<in> keys (q' k)" by (rule punit.lt_in_keys)
    with hom_q' have deg_q': "d = poly_deg (q' k)" unfolding d by (rule homogeneousD_poly_deg)
    from decomp_F q'_in obtain qs where "qs \<in> listset [ideal {f} \<inter> P[X], P]" and "q' k = sum_list qs"
      by (rule direct_decompE)
    moreover from this(1) obtain f0 p0 where f0: "f0 \<in> ideal {f} \<inter> P[X]" and p0: "p0 \<in> P"
      and "qs = [f0, p0]" by (rule listset_doubletonE)
    ultimately have q': "q' k = f0 + p0" by simp
    define f1 where "f1 = hom_component f0 d"
    define p1 where "p1 = hom_component p0 d"
    from hom_q have "homogeneous (q' k)" by (simp add: q'_def homogeneous_monom_mult)
    hence "q' k = hom_component (q' k) d" by (simp add: hom_component_of_homogeneous deg_q')
    also have "\<dots> = f1 + p1" by (simp only: q' hom_component_plus f1_def p1_def)
    finally have "q' k = f1 + p1" .
    have "keys p1 \<noteq> {}"
    proof
      assume "keys p1 = {}"
      with \<open>q' k = f1 + p1\<close> \<open>q' k \<noteq> 0\<close> have t: "?t = lpp f1" and "f1 \<noteq> 0" by simp_all
      from f0 have "f0 \<in> ideal {f}" by simp
      with _ have "f1 \<in> ideal {f}" unfolding f1_def by (rule homogeneous_ideal) (simp add: hom_f)
      with punit.is_Groebner_basis_singleton obtain g where "g \<in> {f}" and "lpp g adds lpp f1"
        using \<open>f1 \<noteq> 0\<close> by (rule punit.GB_adds_lt[simplified])
      hence "lpp f adds ?t" by (simp add: t)
      hence "lookup (lpp f) x \<le> lookup ?t x" by (simp add: adds_poly_mapping le_fun_def)
      also have "\<dots> = lookup (lpp q) x" by (simp add: lpp_q' lookup_add lookup_single \<open>y \<noteq> x\<close>)
      finally have "lookup (lpp f) x \<le> lookup (lpp q) x" .
      with x show False ..
    qed
    then obtain t where "t \<in> keys p1" by blast
    hence "d = deg_pm t" by (simp add: p1_def keys_hom_component)
    from cn_ps hom_ps have "homogeneous_set P" by (intro homogeneous_set_cone_decomp)
    hence "p1 \<in> P" using \<open>p0 \<in> P\<close> unfolding p1_def by (rule homogeneous_setD)
    with \<open>t \<in> keys p1\<close> have "t \<in> Keys P" by (rule in_KeysI)
    with \<open>d = deg_pm t\<close> show "d \<in> deg_pm ` Keys P" by (rule image_eqI)
  qed
  moreover from inj1 inj2 have "infinite ((deg_pm \<circ> lpp) ` range q')"
    by (simp add: finite_image_iff o_def)
  ultimately have "infinite (deg_pm ` Keys P)" by (rule infinite_super)
  hence "infinite (Keys P)" by blast
  thus False using \<open>finite (Keys P)\<close> ..
qed

private definition N where "N = normal_form F ` P[X]"

private definition qs where "qs = (SOME qs'. valid_decomp X qs' \<and> standard_decomp 0 qs' \<and>
                                    monomial_decomp qs' \<and> cone_decomp N qs' \<and> exact_decomp X 0 qs' \<and>
                                    (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> \<b> qs' 0))"

private definition "aa \<equiv> \<b> ps"
private definition "bb \<equiv> \<b> qs"
private abbreviation (input) "cc \<equiv> (\<lambda>i. aa i + bb i)"

lemma
  shows valid_qs: "valid_decomp X qs" (is ?thesis1)
    and std_qs: "standard_decomp 0 qs" (is ?thesis2)
    and mon_qs: "monomial_decomp qs" (is ?thesis3)
    and hom_qs: "hom_decomp qs" (is ?thesis6)
    and cn_qs: "cone_decomp N qs" (is ?thesis4)
    and ext_qs: "exact_decomp X 0 qs" (is ?thesis5)
    and deg_RGB: "g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> bb 0"
proof -
  from fin_X F_sub obtain qs' where 1: "valid_decomp X qs'" and 2: "standard_decomp 0 qs'"
    and 3: "monomial_decomp qs'" and 4: "cone_decomp (normal_form F ` P[X]) qs'"
    and 5: "exact_decomp X 0 qs'"
    and 60: "\<And>g. (\<And>f. f \<in> F \<Longrightarrow> homogeneous f) \<Longrightarrow> g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> \<b> qs' 0"
    by (rule normal_form_exact_decompE) blast
  from hom_F have "\<And>g. g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> \<b> qs' 0" by (rule 60)
  with 1 2 3 4 5 have "valid_decomp X qs' \<and> standard_decomp 0 qs' \<and>
                        monomial_decomp qs' \<and> cone_decomp N qs' \<and> exact_decomp X 0 qs' \<and>
                        (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> \<b> qs' 0)" by (simp add: N_def)
  hence "?thesis1 \<and> ?thesis2 \<and> ?thesis3 \<and> ?thesis4 \<and> ?thesis5 \<and> (\<forall>g\<in>punit.reduced_GB F. poly_deg g \<le> bb 0)"
    unfolding qs_def bb_def by (rule someI)
  thus ?thesis1 and ?thesis2 and ?thesis3 and ?thesis4 and ?thesis5
    and "g \<in> punit.reduced_GB F \<Longrightarrow> poly_deg g \<le> bb 0" by simp_all
  from \<open>?thesis3\<close> show ?thesis6 by (rule monomial_decomp_imp_hom_decomp)
qed

lemma N_sub: "N \<subseteq> P[X]"
  using valid_qs cn_qs by (rule valid_cone_decomp_subset_Polys)

lemma decomp_Polys: "direct_decomp P[X] [ideal {f} \<inter> P[X], P, N]"
proof -
  from fin_X F_sub have "direct_decomp P[X] [ideal F \<inter> P[X], N]" unfolding N_def
    by (rule direct_decomp_ideal_normal_form)
  hence "direct_decomp P[X] ([N] @ [ideal {f} \<inter> P[X], P])" using decomp_F
    by (rule direct_decomp_direct_decomp)
  hence "direct_decomp P[X] ([ideal {f} \<inter> P[X], P] @ [N])" using perm_append_swap
    by (rule direct_decomp_perm)
  thus ?thesis by simp
qed

lemma aa_Suc_n [simp]: "aa (Suc n) = d"
proof -
  from fin_X ext_ps le_refl have "aa (Suc n) = \<a> ps" unfolding aa_def by (rule \<b>_card_X)
  also from fin_X valid_ps std_ps ps_not_Nil have "\<dots> = d" by (rule \<a>_nonempty_unique)
  finally show ?thesis .
qed

lemma bb_Suc_n [simp]: "bb (Suc n) = 0"
proof -
  from fin_X ext_qs le_refl have "bb (Suc n) = \<a> qs" unfolding bb_def by (rule \<b>_card_X)
  also from std_qs have "\<dots> = 0" unfolding \<a>_def[OF fin_X] by (rule Least_eq_0)
  finally show ?thesis .
qed

lemma Hilbert_fun_X:
  assumes "d \<le> z"
  shows "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) z =
            ((z - d) + (n - 1)) choose (n - 1) + Hilbert_fun P z + Hilbert_fun N z"
proof -
  define ss where "ss = [ideal {f} \<inter> P[X], P, N]"
  have "homogeneous_set A \<and> phull.subspace A" if "A \<in> set ss" for A
  proof -
    from that have "A = ideal {f} \<inter> P[X] \<or> A = P \<or> A = N" by (simp add: ss_def)
    thus ?thesis
    proof (elim disjE)
      assume A: "A = ideal {f} \<inter> P[X]"
      show ?thesis unfolding A
        by (intro conjI homogeneous_set_IntI phull.subspace_inter homogeneous_set_homogeneous_ideal
            homogeneous_set_Polys subspace_ideal subspace_Polys) (simp add: hom_f)
    next
      assume A: "A = P"
      from cn_ps hom_ps show ?thesis unfolding A
        by (intro conjI homogeneous_set_cone_decomp subspace_cone_decomp)
    next
      assume A: "A = N"
      from cn_qs hom_qs show ?thesis unfolding A
        by (intro conjI homogeneous_set_cone_decomp subspace_cone_decomp)
    qed
  qed
  hence 1: "\<And>A. A \<in> set ss \<Longrightarrow> homogeneous_set A" and 2: "\<And>A. A \<in> set ss \<Longrightarrow> phull.subspace A"
    by simp_all
  have "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) z = (\<Sum>p\<in>set ss. Hilbert_fun p z)"
    using fin_X subset_refl decomp_Polys unfolding ss_def
  proof (rule Hilbert_fun_direct_decomp)
    fix A
    assume "A \<in> set [ideal {f} \<inter> P[X], P, N]"
    hence "A \<in> set ss" by (simp only: ss_def)
    thus "homogeneous_set A" and "phull.subspace A" by (rule 1, rule 2)
  qed
  also have "\<dots> = (\<Sum>p\<in>set ss. count_list ss p * Hilbert_fun p z)"
    using refl
  proof (rule sum.cong)
    fix p
    assume "p \<in> set ss"
    hence "count_list ss p \<noteq> 0" by (simp only: count_list_eq_0_iff not_not)
    hence "count_list ss p = 1 \<or> 1 < count_list ss p" by auto
    thus "Hilbert_fun p z = count_list ss p * Hilbert_fun p z"
    proof
      assume "1 < count_list ss p"
      with decomp_Polys have "p = {0}" unfolding ss_def[symmetric] using phull.subspace_0
        by (rule direct_decomp_repeated_eq_zero) (rule 2)
      thus ?thesis by simp
    qed simp
  qed
  also have "\<dots> = sum_list (map (\<lambda>p. Hilbert_fun p z) ss)"
    by (rule sym) (rule sum_list_map_eq_sum_count)
  also have "\<dots> = Hilbert_fun (cone (f, X)) z + Hilbert_fun P z + Hilbert_fun N z"
    by (simp add: ss_def ideal_Int_Polys_eq_cone)
  also have "Hilbert_fun (cone (f, X)) z = (z - d + (n - 1)) choose (n - 1)"
    using f_not_0 f_in_Polys fin_X hom_f X_not_empty by (simp add: Hilbert_fun_cone_nonempty assms)
  finally show ?thesis .
qed

lemma dube_eq_0:
  "(\<lambda>z::int. (z + int n - 1) gchoose (n - 1)) =
    (\<lambda>z::int. ((z - d + n - 1) gchoose (n - 1)) + Hilbert_poly aa z + Hilbert_poly bb z)"
    (is "?f = ?g")
proof (rule poly_fun_eqI_ge)
  fix z::int
  let ?z = "nat z"
  assume "max (aa 0) (bb 0) \<le> z"
  hence "aa 0 \<le> nat z" and "bb 0 \<le> nat z" and "0 \<le> z" by simp_all
  from this(3) have int_z: "int ?z = z" by simp
  have "d \<le> aa 0" unfolding aa_Suc_n[symmetric] using fin_X le0 unfolding aa_def by (rule \<b>_decreasing)
  hence "d \<le> ?z" using \<open>aa 0 \<le> nat z\<close> by (rule le_trans)
  hence int_zd: "int (?z - d) = z - int d" using int_z by linarith
  from \<open>d \<le> ?z\<close> have "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) ?z =
                      ((?z - d) + (n - 1)) choose (n - 1) + Hilbert_fun P ?z + Hilbert_fun N ?z"
    by (rule Hilbert_fun_X)
  also have "int \<dots> = (z - d + (n - 1)) gchoose (n - 1) + Hilbert_poly aa z + Hilbert_poly bb z"
    using X_not_empty valid_ps hom_ps cn_ps std_ps ext_ps \<open>aa 0 \<le> nat z\<close>
          valid_qs hom_qs cn_qs std_qs ext_qs \<open>bb 0 \<le> nat z\<close> \<open>0 \<le> z\<close>
    by (simp add: Hilbert_fun_eq_Hilbert_poly int_z aa_def bb_def int_binomial int_zd)
  finally show "?f z = ?g z" using fin_X X_not_empty \<open>0 \<le> z\<close>
    by (simp add: Hilbert_fun_Polys int_binomial) smt
qed (simp_all add: poly_fun_Hilbert_poly)

corollary dube_eq_1:
  "(\<lambda>z::int. (z + int n - 1) gchoose (n - 1)) =
    (\<lambda>z::int. ((z - d + n - 1) gchoose (n - 1)) + ((z - d + n) gchoose n) + ((z + n) gchoose n) - 2 -
           (\<Sum>i=1..n. ((z - aa i + i - 1) gchoose i) + ((z - bb i + i - 1) gchoose i)))"
  by (simp only: dube_eq_0) (auto simp: Hilbert_poly_def Let_def sum.distrib)

lemma dube_eq_2:
  assumes "j < n"
  shows "(\<lambda>z::int. (z + int n - int j - 1) gchoose (n - j - 1)) =
          (\<lambda>z::int. ((z - d + n - int j - 1) gchoose (n - j - 1)) + ((z - d + n - j) gchoose (n - j)) +
                    ((z + n - j) gchoose (n - j)) - 2 -
                    (\<Sum>i=Suc j..n. ((z - aa i + i - j - 1) gchoose (i - j)) + ((z - bb i + i - j - 1) gchoose (i - j))))"
    (is "?f = ?g")
proof -
  let ?h = "\<lambda>z i. ((z + (int i - aa i - 1)) gchoose i) + ((z + (int i - bb i - 1)) gchoose i)"
  let ?hj = "\<lambda>z i. ((z + (int i - aa i - 1) - j) gchoose (i - j)) + ((z + (int i - bb i - 1) - j) gchoose (i - j))"
  from assms have 1: "j \<le> n - Suc 0" and 2: "j \<le> n" by simp_all

  have eq1: "(bw_diff ^^ j) (\<lambda>z. \<Sum>i=1..j. ?h z i) = (\<lambda>_. if j = 0 then 0 else 2)"
  proof (cases j)
    case 0
    thus ?thesis by simp
  next
    case (Suc j0)
    hence "j \<noteq> 0" by simp
    have "(\<lambda>z::int. \<Sum>i = 1..j. ?h z i) = (\<lambda>z::int. (\<Sum>i = 1..j0. ?h z i) + ?h z j)"
      by (simp add: \<open>j = Suc j0\<close>)
    moreover have "(bw_diff ^^ j) \<dots> = (\<lambda>z::int. (\<Sum>i = 1..j0. (bw_diff ^^ j) (\<lambda>z. ?h z i) z) + 2)"
      by (simp add: bw_diff_gbinomial_pow)
    moreover have "(\<Sum>i = 1..j0. (bw_diff ^^ j) (\<lambda>z. ?h z i) z) = (\<Sum>i = 1..j0. 0)" for z::int
      using refl
    proof (rule sum.cong)
      fix i
      assume "i \<in> {1..j0}"
      hence "\<not> j \<le> i" by (simp add: \<open>j = Suc j0\<close>)
      thus "(bw_diff ^^ j) (\<lambda>z. ?h z i) z = 0" by (simp add: bw_diff_gbinomial_pow)
    qed
    ultimately show ?thesis by (simp add: \<open>j \<noteq> 0\<close>)
  qed

  have eq2: "(bw_diff ^^ j) (\<lambda>z. \<Sum>i=Suc j..n. ?h z i) = (\<lambda>z. (\<Sum>i=Suc j..n. ?hj z i))"
  proof -
    have "(bw_diff ^^ j) (\<lambda>z. \<Sum>i=Suc j..n. ?h z i) = (\<lambda>z. \<Sum>i=Suc j..n. (bw_diff ^^ j) (\<lambda>z. ?h z i) z)"
      by simp
    also have "\<dots> = (\<lambda>z. (\<Sum>i=Suc j..n. ?hj z i))"
    proof (intro ext sum.cong)
      fix z i
      assume "i \<in> {Suc j..n}"
      hence "j \<le> i" by simp
      thus "(bw_diff ^^ j) (\<lambda>z. ?h z i) z = ?hj z i" by (simp add: bw_diff_gbinomial_pow)
    qed (fact refl)
    finally show ?thesis .
  qed

  from 1 have "?f = (bw_diff ^^ j) (\<lambda>z::int. (z + (int n - 1)) gchoose (n - 1))"
    by (simp add: bw_diff_gbinomial_pow) (simp only: algebra_simps)
  also have "\<dots> = (bw_diff ^^ j) (\<lambda>z::int. (z + int n - 1) gchoose (n - 1))"
    by (simp only: algebra_simps)
  also have "\<dots> = (bw_diff ^^ j)
          (\<lambda>z::int. ((z - d + n - 1) gchoose (n - 1)) + ((z - d + n) gchoose n) + ((z + n) gchoose n) - 2 -
            (\<Sum>i=1..n. ((z - aa i + i - 1) gchoose i) + ((z - bb i + i - 1) gchoose i)))"
    by (simp only: dube_eq_1)
  also have "\<dots> = (bw_diff ^^ j)
          (\<lambda>z::int. ((z + (int n - d - 1)) gchoose (n - 1)) + ((z + (int n - d)) gchoose n) +
                    ((z + n) gchoose n) - 2 - (\<Sum>i=1..n. ?h z i))"
    by (simp only: algebra_simps)
  also have "\<dots> = (\<lambda>z::int. ((z + (int n - d - 1) - j) gchoose (n - 1 - j)) +
            ((z + (int n - d) - j) gchoose (n - j)) + ((z + n - j) gchoose (n - j)) - (if j = 0 then 2 else 0) -
            (bw_diff ^^ j) (\<lambda>z. \<Sum>i=1..n. ?h z i) z)"
    using 1 2 by (simp add: bw_diff_const_pow bw_diff_gbinomial_pow del: bw_diff_sum_pow)
  also from \<open>j \<le> n\<close> have "(\<lambda>z. \<Sum>i=1..n. ?h z i) = (\<lambda>z. (\<Sum>i=1..j. ?h z i) + (\<Sum>i=Suc j..n. ?h z i))"
    by (simp add: sum_split_nat_ivl)
  also have "(bw_diff ^^ j) \<dots> = (\<lambda>z. (bw_diff ^^ j) (\<lambda>z. \<Sum>i=1..j. ?h z i) z + (bw_diff ^^ j) (\<lambda>z. \<Sum>i=Suc j..n. ?h z i) z)"
    by (simp only: bw_diff_plus_pow)
  also have "\<dots> = (\<lambda>z. (if j = 0 then 0 else 2) + (\<Sum>i=Suc j..n. ?hj z i))"
    by (simp only: eq1 eq2)
  finally show ?thesis by (simp add: algebra_simps)
qed

lemma dube_eq_3:
  assumes "j < n"
  shows "(1::int) = (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - j) * ((int d - 1) gchoose (n - j)) - 1 -
                    (\<Sum>i=Suc j..n. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
proof -
  from assms have 1: "int (n - Suc j) = int n - j - 1" and 2: "int (n - j) = int n - j" by simp_all
  from assms have "int n - int j - 1 = int (n - j - 1)" by simp
  hence eq1: "int n - int j - 1 gchoose (n - Suc j) = 1" by simp
  from assms have "int n - int j = int (n - j)" by simp
  hence eq2: "int n - int j gchoose (n - j) = 1" by simp
  have eq3: "int n - d - j - 1 gchoose (n - Suc j) = (- 1)^(n - Suc j) * (int d - 1 gchoose (n - Suc j))"
    by (simp add: gbinomial_int_negated_upper[of "int n - d - j - 1"] 1)
  have eq4: "int n - d - j gchoose (n - j) = (- 1)^(n - j) * (int d - 1 gchoose (n - j))"
    by (simp add: gbinomial_int_negated_upper[of "int n - d - j"] 2)
  have eq5: "(\<Sum>i = Suc j..n. int i - aa i - j - 1 gchoose (i - j) + (int i - bb i - j - 1 gchoose (i - j))) =
        (\<Sum>i=Suc j..n. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    using refl
  proof (rule sum.cong)
    fix i
    assume "i \<in> {Suc j..n}"
    hence "j \<le> i" by simp
    hence 3: "int (i - j) = int i - j" by simp
    show "int i - aa i - j - 1 gchoose (i - j) + (int i - bb i - j - 1 gchoose (i - j)) =
          (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j)))"
      by (simp add: gbinomial_int_negated_upper[of "int i - aa i - j - 1"]
            gbinomial_int_negated_upper[of "int i - bb i - j - 1"] 3 distrib_left)
  qed
  from fun_cong[OF dube_eq_2, OF assms, of 0] show ?thesis by (simp add: eq1 eq2 eq3 eq4 eq5)
qed

lemma dube_aux_1:
  assumes "(h, {}) \<in> set ps \<union> set qs"
  shows "poly_deg h < max (aa 1) (bb 1)"
proof (rule ccontr)
  define z where "z = poly_deg h"
  assume "\<not> z < max (aa 1) (bb 1)"

  let ?S = "\<lambda>A. {h. (h, {}) \<in> A \<and> poly_deg h = z}"
  have fin: "finite (?S A)" if "finite A" for A::"((('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) \<times> 'x set) set"
  proof -
    have "(\<lambda>t. (t, {})) ` ?S A \<subseteq> A" by blast
    hence "finite ((\<lambda>t. (t, {}::'x set)) ` ?S A)" using that by (rule finite_subset)
    moreover have "inj_on (\<lambda>t. (t, {}::'x set)) (?S A)" by (rule inj_onI) simp
    ultimately show ?thesis by (rule finite_imageD)
  qed
  from finite_set have 1: "finite (?S (set ps))" by (rule fin)
  from finite_set have 2: "finite (?S (set qs))" by (rule fin)

  from \<open>\<not> z < max (aa 1) (bb 1)\<close> have "aa 1 \<le> z" and "bb 1 \<le> z" by simp_all
  have "d \<le> aa 1" unfolding aa_Suc_n[symmetric] aa_def using fin_X by (rule \<b>_decreasing) simp
  hence "d \<le> z" using \<open>aa 1 \<le> z\<close> by (rule le_trans)
  hence eq: "int (z - d) = int z - int d" by simp
  from \<open>d \<le> z\<close> have "Hilbert_fun (P[X]::(_ \<Rightarrow>\<^sub>0 'a) set) z =
                        ((z - d) + (n - 1)) choose (n - 1) + Hilbert_fun P z + Hilbert_fun N z"
    by (rule Hilbert_fun_X)
  also have "int \<dots> = ((int z - d + (n - 1)) gchoose (n - 1) + Hilbert_poly aa z + Hilbert_poly bb z) +
                        (int (card (?S (set ps))) + int (card (?S (set qs))))"
    using X_not_empty valid_ps hom_ps cn_ps std_ps ext_ps \<open>aa 1 \<le> z\<close>
          valid_qs hom_qs cn_qs std_qs ext_qs \<open>bb 1 \<le> z\<close>
    by (simp add: Hilbert_fun_eq_Hilbert_poly_plus_card aa_def bb_def int_binomial eq)
  finally have "((int z - d + n - 1) gchoose (n - 1) + Hilbert_poly aa z + Hilbert_poly bb z) +
                  (int (card (?S (set ps))) + int (card (?S (set qs)))) = int z + n - 1 gchoose (n - 1)"
    using fin_X X_not_empty by (simp add: Hilbert_fun_Polys int_binomial algebra_simps)
  also have "\<dots> = (int z - d + n - 1) gchoose (n - 1) + Hilbert_poly aa z + Hilbert_poly bb z"
    by (fact dube_eq_0[THEN fun_cong])
  finally have "int (card (?S (set ps))) + int (card (?S (set qs))) = 0" by simp
  hence "card (?S (set ps)) = 0" and "card (?S (set qs)) = 0" by simp_all
  with 1 2 have "?S (set ps \<union> set qs) = {}" by auto
  moreover from assms have "h \<in> ?S (set ps \<union> set qs)" by (simp add: z_def)
  ultimately have "h \<in> {}" by (rule subst)
  thus False by simp
qed

lemma
  shows aa_n: "aa n = d" and bb_n: "bb n = 0" and bb_0: "bb 0 \<le> max (aa 1) (bb 1)"
proof -
  let ?j = "n - Suc 0"
  from n_gr_0 have "?j < n" and eq1: "Suc ?j = n" and eq2: "n - ?j = 1" by simp_all
  from this(1) have "(1::int) = (- 1)^(n - Suc ?j) * ((int d - 1) gchoose (n - Suc ?j)) +
                    (- 1)^(n - ?j) * ((int d - 1) gchoose (n - ?j)) - 1 -
                    (\<Sum>i=Suc ?j..n. (- 1)^(i - ?j) * ((int (aa i) gchoose (i - ?j)) + (int (bb i) gchoose (i - ?j))))"
    by (rule dube_eq_3)
  hence eq: "aa n + bb n = d" by (simp add: eq1 eq2)
  hence "aa n \<le> d" by simp
  moreover have "d \<le> aa n" unfolding aa_Suc_n[symmetric] aa_def using fin_X by (rule \<b>_decreasing) simp
  ultimately show "aa n = d" by (rule antisym)
  with eq show "bb n = 0" by simp

  have "bb 0 = \<b> qs 0" by (simp only: bb_def)
  also from fin_X have "\<dots> \<le> max (aa 1) (bb 1)" (is "_ \<le> ?m")
  proof (rule \<b>_le)
    from fin_X ext_qs have "\<a> qs = bb (Suc n)" by (simp add: \<b>_card_X bb_def)
    also have "\<dots> \<le> bb 1" unfolding bb_def using fin_X by (rule \<b>_decreasing) simp
    also have "\<dots> \<le> ?m" by (rule max.cobounded2)
    finally show "\<a> qs \<le> ?m" .
  next
    fix h U
    assume "(h, U) \<in> set qs"
    show "poly_deg h < ?m"
    proof (cases "card U = 0")
      case True
      from fin_X valid_qs \<open>(h, U) \<in> set qs\<close> have "finite U" by (rule valid_decompD_finite)
      with True have "U = {}" by simp
      with \<open>(h, U) \<in> set qs\<close> have "(h, {}) \<in> set ps \<union> set qs" by simp
      thus ?thesis by (rule dube_aux_1)
    next
      case False
      hence "1 \<le> card U" by simp
      with fin_X \<open>(h, U) \<in> set qs\<close> have "poly_deg h < bb 1" unfolding bb_def by (rule \<b>)
      also have "\<dots> \<le> ?m" by (rule max.cobounded2)
      finally show ?thesis .
    qed
  qed
  finally show "bb 0 \<le> ?m" .
qed

lemma dube_eq_4:
  assumes "j < n"
  shows "(1::int) = 2 * (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) - 1 -
                    (\<Sum>i=Suc j..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
proof -
  from assms have "Suc j \<le> n" and "0 < n" and 1: "Suc (n - Suc j) = n - j" by simp_all
  have 2: "(- 1) ^ (n - Suc j) = - ((- (1::int)) ^ (n - j))" by (simp flip: 1)
  from assms have "(1::int) = (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - j) * ((int d - 1) gchoose (n - j)) - 1 -
                    (\<Sum>i=Suc j..n. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    by (rule dube_eq_3)
  also have "\<dots> = (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - j) * ((int d - 1) gchoose (n - j)) - 1 -
                    (- 1)^(n - j) * ((int (aa n) gchoose (n - j)) + (int (bb n) gchoose (n - j))) -
                    (\<Sum>i=Suc j..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    using \<open>0 < n\<close> \<open>Suc j \<le> n\<close> by (simp only: sum_tail_nat)
  also have "\<dots> = (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - j) * (((int d - 1) gchoose (n - j)) - (int d gchoose (n - j))) - 1 -
                    (\<Sum>i=Suc j..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    using assms by (simp add: aa_n bb_n gbinomial_0_left right_diff_distrib)
  also have "(- 1)^(n - j) * (((int d - 1) gchoose (n - j)) - (int d gchoose (n - j))) =
              (- 1)^(n - Suc j) * (((int d - 1 + 1) gchoose (Suc (n - Suc j))) - ((int d - 1) gchoose (Suc (n - Suc j))))"
    by (simp add: 1 2 flip: mult_minus_right)
  also have "\<dots> = (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j))"
    by (simp only: gbinomial_int_Suc_Suc, simp)
  finally show ?thesis by simp
qed

lemma cc_Suc:
  assumes "j < n - 1"
  shows "int (cc (Suc j)) = 2 + 2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) +
                   (\<Sum>i=j+2..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
proof -
  from assms have "j < n" and "Suc j \<le> n - 1" by simp_all
  hence "n - j = Suc (n - Suc j)" by simp
  hence eq: "(- 1) ^ (n - Suc j) = - ((- (1::int)) ^ (n - j))" by simp
  from \<open>j < n\<close> have "(1::int) = 2 * (- 1)^(n - Suc j) * ((int d - 1) gchoose (n - Suc j)) - 1 -
             (\<Sum>i=Suc j..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    by (rule dube_eq_4)
  also have "\<dots> = cc (Suc j) - 2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) - 1 -
             (\<Sum>i=j+2..n-1. (- 1)^(i - j) * ((int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))))"
    using \<open>Suc j \<le> n - 1\<close> by (simp add: sum.atLeast_Suc_atMost eq)
  finally show ?thesis by simp
qed

lemma cc_n_minus_1: "cc (n - 1) = 2 * d"
proof -
  let ?j = "n - 2"
  from n_gr_1 have 1: "Suc ?j = n - 1" and "?j < n - 1" and 2: "Suc (n - 1) = n"
    and 3: "n - (n - Suc 0) = Suc 0" and 4: "n - ?j = 2"
    by simp_all
  have "int (cc (n - 1)) = int (cc (Suc ?j))" by (simp only: 1)
  also from \<open>?j < n - 1\<close> have "\<dots> = 2 + 2 * (- 1) ^ (n - ?j) * (int d - 1 gchoose (n - Suc ?j)) +
         (\<Sum>i = ?j+2..n-1. (- 1) ^ (i - ?j) * (int (aa i) gchoose (i - ?j) + (int (bb i) gchoose (i - ?j))))"
    by (rule cc_Suc)
  also have "\<dots> = int (2 * d)" by (simp add: 1 2 3 4)
  finally show ?thesis by (simp only: int_int_eq)
qed

text \<open>Since the case @{prop "n = 2"} is settled, we can concentrate on @{prop "2 < n"} now.\<close>

context
  assumes n_gr_2: "2 < n"
begin

lemma cc_n_minus_2: "cc (n - 2) \<le> d\<^sup>2 + 2 * d"
proof -
  let ?j = "n - 3"
  from n_gr_2 have 1: "Suc ?j = n - 2" and "?j < n - 1" and 2: "Suc (n - 2) = n - Suc 0"
    and 3: "n - (n - 2) = 2" and 4: "n - ?j = 3"
    by simp_all
  have "int (cc (n - 2)) = int (cc (Suc ?j))" by (simp only: 1)
  also from \<open>?j < n - 1\<close> have "\<dots> = 2 + 2 * (- 1) ^ (n - ?j) * (int d - 1 gchoose (n - Suc ?j)) +
         (\<Sum>i = ?j+2..n-1. (- 1) ^ (i - ?j) * (int (aa i) gchoose (i - ?j) + (int (bb i) gchoose (i - ?j))))"
    by (rule cc_Suc)
  also have "\<dots> = (2 - 2 * (int d - 1 gchoose 2)) + ((int (aa (n - 1)) gchoose 2) + (int (bb (n - 1)) gchoose 2))"
    by (simp add: 1 2 3 4)
  also have "\<dots> \<le> (2 - 2 * (int d - 1 gchoose 2)) + (2 * int d gchoose 2)"
  proof (rule add_left_mono)
    have "int (aa (n - 1)) gchoose 2 + (int (bb (n - 1)) gchoose 2) \<le> int (aa (n - 1)) + int (bb (n - 1)) gchoose 2"
      by (rule gbinomial_int_plus_le) simp_all
    also have "\<dots> = int (2 * d) gchoose 2"  by (simp flip: cc_n_minus_1)
    also have "\<dots> = 2 * int d gchoose 2"  by (simp add: int_ops(7))
    finally show "int (aa (n - 1)) gchoose 2 + (int (bb (n - 1)) gchoose 2) \<le> 2 * int d gchoose 2" .
  qed
  also have "\<dots> = 2 - fact 2 * (int d - 1 gchoose 2) + (2 * int d gchoose 2)" by (simp only: fact_2)
  also have "\<dots> = 2 - (int d - 1) * (int d - 2) + (2 * int d gchoose 2)"
    by (simp only: gbinomial_int_mult_fact) (simp add: numeral_2_eq_2 prod.atLeast0_lessThan_Suc)
  also have "\<dots> = 2 - (int d - 1) * (int d - 2) + int d * (2 * int d - 1)"
    by (simp add: gbinomial_prod_rev numeral_2_eq_2 prod.atLeast0_lessThan_Suc)
  also have "\<dots> = int (d\<^sup>2 + 2 * d)" by (simp add: power2_eq_square) (simp only: algebra_simps)
  finally show ?thesis by (simp only: int_int_eq)
qed

lemma cc_Suc_le:
  assumes "j < n - 3"
  shows "int (cc (Suc j)) \<le> 2 + (int (cc (j + 2)) gchoose 2) + (\<Sum>i=j+4..n-1. int (cc i) gchoose (i - j))"
            \<comment>\<open>Could be proved without coercing to @{typ int}, because everything is non-negative.\<close>
proof -
  let ?f = "\<lambda>i j. (int (aa i) gchoose (i - j)) + (int (bb i) gchoose (i - j))"
  let ?S = "\<lambda>x y. (\<Sum>i=j+x..n-y. (- 1)^(i - j) * ?f i j)"
  let ?S3 = "\<lambda>x y. (\<Sum>i=j+x..n-y. (int (cc i) gchoose (i - j)))"
  have ie1: "int (aa i) gchoose k + (int (bb i) gchoose k) \<le> int (cc i) gchoose k" if "0 < k" for i k
  proof -
    from that have "int (aa i) gchoose k + (int (bb i) gchoose k) \<le> int (aa i) + int (bb i) gchoose k"
      by (rule gbinomial_int_plus_le) simp_all
    also have "\<dots> = int (cc i) gchoose k" by simp
    finally show ?thesis .
  qed
  from d_gr_0 have "0 \<le> int d - 1" by simp
  from assms have "0 < n - Suc j" by simp
  have f_nonneg: "0 \<le> ?f i j" for i by (simp add: gbinomial_int_nonneg)

  show ?thesis
  proof (cases "n = j + 4")
    case True
    hence j: "j = n - 4" by simp
    have 1: "n - Suc j = 3" and "j < n - 1" and 2: "Suc (n - 3) = Suc (Suc j)" and 3: "n - (n - 3) = 3"
      and 4: "n - j = 4" and 5: "n - Suc 0 = Suc (Suc (Suc j))" and 6: "n - 2 = Suc (Suc j)"
      by (simp_all add: True)
    from \<open>j < n - 1\<close> have "int (cc (Suc j)) = 2 + 2 * (- 1) ^ (n - j) * (int d - 1 gchoose (n - Suc j)) +
           (\<Sum>i = j+2..n-1. (- 1) ^ (i - j) * (int (aa i) gchoose (i - j) + (int (bb i) gchoose (i - j))))"
      by (rule cc_Suc)
    also have "\<dots> = (2 + ((int (aa (n - 2)) gchoose 2) + (int (bb (n - 2)) gchoose 2))) +
                    (2 * (int d - 1 gchoose 3) - ((int (aa (n - 1)) gchoose 3) + (int (bb (n - 1)) gchoose 3)))"
      by (simp add: 1 2 3 4 5 6)
    also have "\<dots> \<le> (2 + ((int (aa (n - 2)) gchoose 2) + (int (bb (n - 2)) gchoose 2))) + 0"
    proof (rule add_left_mono)
      from cc_n_minus_1 have eq1: "int (aa (n - 1)) + int (bb (n - 1)) = 2 * int d" by simp
      hence ie2: "int (aa (n - 1)) \<le> 2 * int d" by simp
      from \<open>0 \<le> int d - 1\<close> have "int d - 1 gchoose 3 \<le> int d gchoose 3" by (rule gbinomial_int_mono) simp
      hence "2 * (int d - 1 gchoose 3) \<le> 2 * (int d gchoose 3)" by simp
      also from _ ie2 have "\<dots> \<le> int (aa (n - 1)) gchoose 3 + (2 * int d - int (aa (n - 1)) gchoose 3)"
        by (rule binomial_int_ineq_3) simp
      also have "\<dots> = int (aa (n - 1)) gchoose 3 + (int (bb (n - 1)) gchoose 3)" by (simp flip: eq1)
      finally show "2 * (int d - 1 gchoose 3) - (int (aa (n - 1)) gchoose 3 + (int (bb (n - 1)) gchoose 3)) \<le> 0"
        by simp
    qed
    also have "\<dots> = 2 + ((int (aa (n - 2)) gchoose 2) + (int (bb (n - 2)) gchoose 2))" by simp
    also from ie1 have "\<dots> \<le> 2 + (int (cc (n - 2)) gchoose 2)" by (rule add_left_mono) simp
    also have "\<dots> = 2 + (int (cc (j + 2)) gchoose 2) + ?S3 4 1" by (simp add: True)
    finally show ?thesis .
  next
    case False
    with assms have "j + 4 \<le> n - 1" by simp
    from n_gr_1 have "0 < n - 1" by simp
    from assms have "j + 2 \<le> n - 1" and "j + 2 \<le> n - 2" by simp_all
    hence "n - j = Suc (n - Suc j)" by simp
    hence 1: "(- 1) ^ (n - Suc j) = - ((- (1::int)) ^ (n - j))" by simp
    from assms have "j < n - 1" by simp
    hence "int (cc (Suc j)) = 2 + 2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) + ?S 2 1"
      by (rule cc_Suc)
    also have "\<dots> = 2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - Suc j) * ((int (aa (n - 1)) gchoose (n - Suc j)) + (int (bb (n - 1)) gchoose (n - Suc j))) +
                    (2 + ?S 2 2)"
      using \<open>0 < n - 1\<close> \<open>j + 2 \<le> n - 1\<close> by (simp only: sum_tail_nat) (simp flip: numeral_2_eq_2)
    also have "\<dots> \<le> (int (cc (n - 1)) gchoose (n - Suc j)) + (2 + ?S 2 2)"
    proof (rule add_right_mono)
      have rl: "x - y \<le> x" if "0 \<le> y" for x y :: int using that by simp
      have "2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - Suc j) * ((int (aa (n - 1)) gchoose (n - Suc j)) + (int (bb (n - 1)) gchoose (n - Suc j))) =
              (-1)^(n - j) * (2 * ((int d - 1) gchoose (n - Suc j)) -
                    (int (aa (n - 1)) gchoose (n - Suc j)) - (int (bb (n - 1)) gchoose (n - Suc j)))"
        by (simp only: 1 algebra_simps)
      also have "\<dots> \<le> (int (cc (n - 1))) gchoose (n - Suc j)"
      proof (cases "even (n - j)")
        case True
        hence "(- 1) ^ (n - j) * (2 * (int d - 1 gchoose (n - Suc j)) - (int (aa (n - 1)) gchoose (n - Suc j)) -
                (int (bb (n - 1)) gchoose (n - Suc j))) =
              2 * (int d - 1 gchoose (n - Suc j)) - ((int (aa (n - 1)) gchoose (n - Suc j)) +
                                                     (int (bb (n - 1)) gchoose (n - Suc j)))"
          by simp
        also have "\<dots> \<le> 2 * (int d - 1 gchoose (n - Suc j))" by (rule rl) (simp add: gbinomial_int_nonneg)
        also have "\<dots> = (int d - 1 gchoose (n - Suc j)) + (int d - 1 gchoose (n - Suc j))" by simp
        also have "\<dots> \<le> (int d - 1) + (int d - 1) gchoose (n - Suc j)"
          using \<open>0 < n - Suc j\<close> \<open>0 \<le> int d - 1\<close> \<open>0 \<le> int d - 1\<close> by (rule gbinomial_int_plus_le)
        also have "\<dots> \<le> 2 * int d gchoose (n - Suc j)"
        proof (rule gbinomial_int_mono)
          from \<open>0 \<le> int d - 1\<close> show "0 \<le> int d - 1 + (int d - 1)" by simp
        qed simp
        also have "\<dots> = int (cc (n - 1)) gchoose (n - Suc j)" by (simp only: cc_n_minus_1) simp
        finally show ?thesis .
      next
        case False
        hence "(- 1) ^ (n - j) * (2 * (int d - 1 gchoose (n - Suc j)) - (int (aa (n - 1)) gchoose (n - Suc j)) -
                (int (bb (n - 1)) gchoose (n - Suc j))) =
              ((int (aa (n - 1)) gchoose (n - Suc j)) + (int (bb (n - 1)) gchoose (n - Suc j))) -
                2 * (int d - 1 gchoose (n - Suc j))"
          by simp
        also have "\<dots> \<le> (int (aa (n - 1)) gchoose (n - Suc j)) + (int (bb (n - 1)) gchoose (n - Suc j))"
          by (rule rl) (simp add: gbinomial_int_nonneg d_gr_0)
        also from \<open>0 < n - Suc j\<close> have "\<dots> \<le> int (cc (n - 1)) gchoose (n - Suc j)" by (rule ie1)
        finally show ?thesis .
      qed
      finally show "2 * (- 1)^(n - j) * ((int d - 1) gchoose (n - Suc j)) +
                    (- 1)^(n - Suc j) * ((int (aa (n - 1)) gchoose (n - Suc j)) + (int (bb (n - 1)) gchoose (n - Suc j))) \<le>
                    (int (cc (n - 1))) gchoose (n - Suc j)" .
    qed
    also have "\<dots> = 2 + (int (cc (n - 1)) gchoose ((n - 1) - j)) + ((int (aa (j + 2)) gchoose 2) +
                    (int (bb (j + 2)) gchoose 2)) + ?S 3 2"
      using \<open>j + 2 \<le> n - 2\<close> by (simp add: sum.atLeast_Suc_atMost numeral_3_eq_3)
    also have "\<dots> \<le> 2 + (int (cc (n - 1)) gchoose ((n - 1) - j)) + ((int (aa (j + 2)) gchoose 2) +
                    (int (bb (j + 2)) gchoose 2)) + ?S3 4 2"
    proof (rule add_left_mono)
      from \<open>j + 4 \<le> n - 1\<close> have "j + 3 \<le> n - 2" by simp
      hence "?S 3 2 = ?S 4 2 - ?f (j + 3) j" by (simp add: sum.atLeast_Suc_atMost add.commute)
      hence "?S 3 2 \<le> ?S 4 2" using f_nonneg[of "j + 3"] by simp
      also have "\<dots> \<le> ?S3 4 2"
      proof (rule sum_mono)
        fix i
        assume "i \<in> {j + 4..n - 2}"
        hence "0 < i - j" by simp
        from f_nonneg[of i] have "(- 1)^(i - j) * ?f i j \<le> ?f i j"
          by (smt minus_one_mult_self mult_cancel_right1 pos_zmult_eq_1_iff_lemma zero_less_mult_iff)
        also from \<open>0 < i - j\<close> have "\<dots> \<le> int (cc i) gchoose (i - j)" by (rule ie1)
        finally show "(- 1)^(i - j) * ?f i j \<le> int (cc i) gchoose (i - j)" .
      qed
      finally show "?S 3 2 \<le> ?S3 4 2" .
    qed
    also have "\<dots> = ((int (aa (j + 2)) gchoose 2) + (int (bb (j + 2)) gchoose 2)) + (2 + ?S3 4 1)"
      using \<open>0 < n - 1\<close> \<open>j + 4 \<le> n - 1\<close> by (simp only: sum_tail_nat) (simp flip: numeral_2_eq_2)
    also from ie1 have "\<dots> \<le> int (cc (j + 2)) gchoose 2 + (2 + ?S3 4 1)"
      by (rule add_right_mono) simp
    also have "\<dots> = 2 + (int (cc (j + 2)) gchoose 2) + ?S3 4 1" by (simp only: ac_simps)
    finally show ?thesis .
  qed
qed

corollary cc_le:
  assumes "0 < j" and "j < n - 2"
  shows "cc j \<le> 2 + (cc (j + 1) choose 2) + (\<Sum>i=j+3..n-1. cc i choose (Suc (i - j)))"
proof -
  define j0 where "j0 = j - 1"
  with assms have j: "j = Suc j0" and "j0 < n - 3" by simp_all
  have "int (cc j) = int (cc (Suc j0))" by (simp only: j)
  also have "\<dots> \<le> 2 + (int (cc (j0 + 2)) gchoose 2) + (\<Sum>i=j0+4..n-1. int (cc i) gchoose (i - j0))"
    using \<open>j0 < n - 3\<close> by (rule cc_Suc_le)
  also have "\<dots> = 2 + (int (cc (j + 1)) gchoose 2) + (\<Sum>i=j0+4..n-1. int (cc i) gchoose (i - j0))"
    by (simp add: j)
  also have "(\<Sum>i=j0+4..n-1. int (cc i) gchoose (i - j0)) = int (\<Sum>i=j+3..n-1. cc i choose (Suc (i - j)))"
    unfolding int_sum
  proof (rule sum.cong)
    fix i
    assume "i \<in> {j + 3..n - 1}"
    hence "Suc j0 < i" by (simp add: j)
    hence "i - j0 = Suc (i - j)" by (simp add: j)
    thus "int (cc i) gchoose (i - j0) = int (cc i choose (Suc (i - j)))" by (simp add: int_binomial)
  qed (simp add: j)
  finally have "int (cc j) \<le> int (2 + (cc (j + 1) choose 2) + (\<Sum>i = j + 3..n - 1. cc i choose (Suc (i - j))))"
    by (simp only: int_plus int_binomial)
  thus ?thesis by (simp only: zle_int)
qed

corollary cc_le_Dube_aux: "0 < j \<Longrightarrow> j + 1 \<le> n \<Longrightarrow> cc j \<le> Dube_aux n d j"
proof (induct j rule: Dube_aux.induct[where n=n])
  case step: (1 j)
  from step.prems(2) have "j + 2 < n \<or> j + 2 = n \<or> j + 1 = n" by auto
  thus ?case
  proof (elim disjE)
    assume *: "j + 2 < n"
    moreover have "0 < j + 1" by simp
    moreover from * have "j + 1 + 1 \<le> n" by simp
    ultimately have "cc (j + 1) \<le> Dube_aux n d (j + 1)" by (rule step.hyps)
    hence 1: "cc (j + 1) choose 2 \<le> Dube_aux n d (j + 1) choose 2"
      by (rule Binomial_Int.binomial_mono)
    have 2: "(\<Sum>i = j + 3..n - 1. cc i choose Suc (i - j)) \<le>
              (\<Sum>i = j + 3..n - 1. Dube_aux n d i choose Suc (i - j))"
    proof (rule sum_mono)
      fix i::nat
      note *
      moreover assume "i \<in> {j + 3..n - 1}"
      moreover from this \<open>2 < n\<close> have "0 < i" and "i + 1 \<le> n" by auto
      ultimately have "cc i \<le> Dube_aux n d i" by (rule step.hyps)
      thus "cc i choose Suc (i - j) \<le> Dube_aux n d i choose Suc (i - j)"
        by (rule Binomial_Int.binomial_mono)
    qed
    from * have "j < n - 2" by simp
    with step.prems(1) have "cc j \<le> 2 + (cc (j + 1) choose 2) + (\<Sum>i = j + 3..n - 1. cc i choose Suc (i - j))"
      by (rule cc_le)
    also from * 1 2 have "\<dots> \<le> Dube_aux n d j" by simp
    finally show ?thesis .
  next
    assume "j + 2 = n"
    hence "j = n - 2" and "Dube_aux n d j = d\<^sup>2 + 2 * d" by simp_all
    thus ?thesis by (simp only: cc_n_minus_2)
  next
    assume "j + 1 = n"
    hence "j = n - 1" and "Dube_aux n d j = 2 * d" by simp_all
    thus ?thesis by (simp only: cc_n_minus_1)
  qed
qed

end

lemma Dube_aux:
  assumes "g \<in> punit.reduced_GB F"
  shows "poly_deg g \<le> Dube_aux n d 1"
proof (cases "n = 2")
  case True
  from assms have "poly_deg g \<le> bb 0" by (rule deg_RGB)
  also have "\<dots> \<le> max (aa 1) (bb 1)" by (fact bb_0)
  also have "\<dots> \<le> cc (n - 1)" by (simp add: True)
  also have "\<dots> = 2 * d" by (fact cc_n_minus_1)
  also have "\<dots> = Dube_aux n d 1" by (simp add: True)
  finally show ?thesis .
next
  case False
  with \<open>1 < n\<close> have "2 < n" and "1 + 1 \<le> n" by simp_all
  from assms have "poly_deg g \<le> bb 0" by (rule deg_RGB)
  also have "\<dots> \<le> max (aa 1) (bb 1)" by (fact bb_0)
  also have "\<dots> \<le> cc 1" by simp
  also from \<open>2 < n\<close> _ \<open>1 + 1 \<le> n\<close> have "\<dots> \<le> Dube_aux n d 1" by (rule cc_le_Dube_aux) simp
  finally show ?thesis .
qed

end

theorem Dube:
  assumes "finite F" and "F \<subseteq> P[X]" and "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "g \<in> punit.reduced_GB F"
  shows "poly_deg g \<le> Dube (card X) (maxdeg F)"
proof (cases "F \<subseteq> {0}")
  case True
  hence "F = {} \<or> F = {0}" by blast
  with assms(4) show ?thesis by (auto simp: punit.reduced_GB_empty punit.reduced_GB_singleton)
next
  case False
  hence "F - {0} \<noteq> {}" by simp
  hence "F \<noteq> {}" by blast
  hence "poly_deg ` F \<noteq> {}" by simp
  from assms(1) have fin1: "finite (poly_deg ` F)" by (rule finite_imageI)
  from assms(1) have "finite (F - {0})" by simp
  hence fin: "finite (poly_deg ` (F - {0}))" by (rule finite_imageI)
  moreover from \<open>F - {0} \<noteq> {}\<close> have *: "poly_deg ` (F - {0}) \<noteq> {}" by simp
  ultimately have "maxdeg (F - {0}) \<in> poly_deg ` (F - {0})" unfolding maxdeg_def by (rule Max_in)
  then obtain f where "f \<in> F - {0}" and md1: "maxdeg (F - {0}) = poly_deg f" ..
  note this(2)
  moreover have "maxdeg (F - {0}) \<le> maxdeg F"
    unfolding maxdeg_def using image_mono * fin1 by (rule Max_mono) blast
  ultimately have "poly_deg f \<le> maxdeg F" by simp
  from \<open>f \<in> F - {0}\<close> have "f \<in> F" and "f \<noteq> 0" by simp_all
  from this(1) assms(2) have "f \<in> P[X]" ..
  have f_max: "poly_deg f' \<le> poly_deg f" if "f' \<in> F" for f'
  proof (cases "f' = 0")
    case True
    thus ?thesis by simp
  next
    case False
    with that have "f' \<in> F - {0}" by simp
    hence "poly_deg f' \<in> poly_deg ` (F - {0})" by (rule imageI)
    with fin show "poly_deg f' \<le> poly_deg f" unfolding md1[symmetric] maxdeg_def by (rule Max_ge)
  qed
  have "maxdeg F \<le> poly_deg f" unfolding maxdeg_def using fin1 \<open>poly_deg ` F \<noteq> {}\<close>
  proof (rule Max.boundedI)
    fix d
    assume "d \<in> poly_deg ` F"
    then obtain f' where "f' \<in> F" and "d = poly_deg f'" ..
    note this(2)
    also from \<open>f' \<in> F\<close> have "poly_deg f' \<le> poly_deg f" by (rule f_max)
    finally show "d \<le> poly_deg f" .
  qed
  with \<open>poly_deg f \<le> maxdeg F\<close> have md: "poly_deg f = maxdeg F" by (rule antisym)
  show ?thesis
  proof (cases "ideal {f} = ideal F")
    case True
    note assms(4)
    also have "punit.reduced_GB F = punit.reduced_GB {f}"
      using punit.finite_reduced_GB_finite punit.reduced_GB_is_reduced_GB_finite
      by (rule punit.reduced_GB_unique) (simp_all add: punit.reduced_GB_pmdl_finite[simplified] True)
    also have "\<dots> \<subseteq> {punit.monic f}" by (simp add: punit.reduced_GB_singleton)
    finally have "g \<in> {punit.monic f}" .
    hence "poly_deg g = poly_deg (punit.monic f)" by simp
    also from poly_deg_monom_mult_le[where c="1 / lcf f" and t=0 and p=f] have "\<dots> \<le> poly_deg f"
      by (simp add: punit.monic_def)
    also have "\<dots> = maxdeg F" by (fact md)
    also have "\<dots> \<le> Dube (card X) (maxdeg F)" by (fact Dube_ge_d)
    finally show ?thesis .
  next
    case False
    show ?thesis
    proof (cases "poly_deg f = 0")
      case True
      hence "monomial (lookup f 0) 0 = f" by (rule poly_deg_zero_imp_monomial)
      moreover define c where "c = lookup f 0"
      ultimately have f: "f = monomial c 0" by simp
      with \<open>f \<noteq> 0\<close> have "c \<noteq> 0" by (simp add: monomial_0_iff)
      from \<open>f \<in> F\<close> have "f \<in> ideal F" by (rule ideal.span_base)
      hence "punit.monom_mult (1 / c) 0 f \<in> ideal F" by (rule punit.pmdl_closed_monom_mult[simplified])
      with \<open>c \<noteq> 0\<close> have "ideal F = UNIV"
        by (simp add: f punit.monom_mult_monomial ideal_eq_UNIV_iff_contains_one)
      with assms(1) have "punit.reduced_GB F = {1}"
        by (simp only: ideal_eq_UNIV_iff_reduced_GB_eq_one_finite)
      with assms(4) show ?thesis by simp
    next
      case False
      hence "0 < poly_deg f" by simp
      have "card X \<le> 1 \<or> 1 < card X" by auto
      thus ?thesis
      proof
        note fin_X
        moreover assume "card X \<le> 1"
        moreover note assms(2)
        moreover from \<open>f \<in> F\<close> have "f \<in> ideal F" by (rule ideal.span_base)
        ultimately have "poly_deg g \<le> poly_deg f"
          using \<open>f \<noteq> 0\<close> assms(4) by (rule deg_reduced_GB_univariate_le)
        also have "\<dots> \<le> Dube (card X) (maxdeg F)" unfolding md by (fact Dube_ge_d)
        finally show ?thesis .
      next
        assume "1 < card X"
        hence "poly_deg g \<le> Dube_aux (card X) (poly_deg f) 1"
          using assms(1, 2) \<open>f \<in> F\<close> assms(3) f_max \<open>0 < poly_deg f\<close> \<open>ideal {f} \<noteq> ideal F\<close> assms(4)
          by (rule Dube_aux)
        also from \<open>1 < card X\<close> \<open>0 < poly_deg f\<close> have "\<dots> = Dube (card X) (maxdeg F)"
          by (simp add: Dube_def md)
        finally show ?thesis .
      qed
    qed
  qed
qed

corollary Dube_is_hom_GB_bound:
  "finite F \<Longrightarrow> F \<subseteq> P[X] \<Longrightarrow> is_hom_GB_bound F (Dube (card X) (maxdeg F))"
  by (intro is_hom_GB_boundI Dube)

end

corollary Dube_indets:
  assumes "finite F" and "\<And>f. f \<in> F \<Longrightarrow> homogeneous f" and "g \<in> punit.reduced_GB F"
  shows "poly_deg g \<le> Dube (card (\<Union>(indets ` F))) (maxdeg F)"
  using _ assms(1) _ assms(2, 3)
proof (rule Dube)
  from assms show "finite (\<Union>(indets ` F))" by (simp add: finite_indets)
next
  show "F \<subseteq> P[\<Union>(indets ` F)]" by (auto simp: Polys_alt)
qed

corollary Dube_is_hom_GB_bound_indets:
  "finite F \<Longrightarrow> is_hom_GB_bound F (Dube (card (\<Union>(indets ` F))) (maxdeg F))"
  by (intro is_hom_GB_boundI Dube_indets)

end (* pm_powerprod *)

hide_const (open) pm_powerprod.\<a> pm_powerprod.\<b>

context extended_ord_pm_powerprod
begin

lemma Dube_is_GB_cofactor_bound:
  assumes "finite X" and "finite F" and "F \<subseteq> P[X]"
  shows "is_GB_cofactor_bound F (Dube (Suc (card X)) (maxdeg F))"
  using assms(1, 3)
proof (rule hom_GB_bound_is_GB_cofactor_bound)
  let ?F = "homogenize None ` extend_indets ` F"
  let ?X = "insert None (Some ` X)"
  from assms(1) have "finite ?X" by simp
  moreover from assms(2) have "finite ?F" by (intro finite_imageI)
  moreover have "?F \<subseteq> P[?X]"
  proof
    fix f'
    assume "f' \<in> ?F"
    then obtain f where "f \<in> F" and f': "f' = homogenize None (extend_indets f)" by blast
    from this(1) assms(3) have "f \<in> P[X]" ..
    hence "extend_indets f \<in> P[Some ` X]" by (auto simp: Polys_alt indets_extend_indets)
    thus "f' \<in> P[?X]" unfolding f' by (rule homogenize_in_Polys)
  qed
  ultimately have "extended_ord.is_hom_GB_bound ?F (Dube (card ?X) (maxdeg ?F))"
    by (rule extended_ord.Dube_is_hom_GB_bound)
  moreover have "maxdeg ?F = maxdeg F"
  proof -
    have "maxdeg ?F = maxdeg (extend_indets ` F)"
      by (auto simp: indets_extend_indets intro: maxdeg_homogenize)
    also have "\<dots> = maxdeg F" by (simp add: maxdeg_def image_image)
    finally show "maxdeg ?F = maxdeg F" .
  qed
  moreover from assms(1) have "card ?X = card X + 1" by (simp add: card_image)
  ultimately show "extended_ord.is_hom_GB_bound ?F (Dube (Suc (card X)) (maxdeg F))" by simp
qed

lemma Dube_is_GB_cofactor_bound_explicit:
  assumes "finite X" and "finite F" and "F \<subseteq> P[X]"
  obtains G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and "\<And>g. g \<in> G \<Longrightarrow> \<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and>
                            (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> Dube (Suc (card X)) (maxdeg F) \<and>
                              (f \<notin> F \<longrightarrow> q f = 0))"
proof -
  from assms have "is_GB_cofactor_bound F (Dube (Suc (card X)) (maxdeg F))"
    (is "is_GB_cofactor_bound _ ?b") by (rule Dube_is_GB_cofactor_bound)
  moreover note assms(3)
  ultimately obtain G where "punit.is_Groebner_basis G" and "ideal G = ideal F" and "G \<subseteq> P[X]"
    and 1: "\<And>g. g \<in> G \<Longrightarrow> \<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                              (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> ?b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
    by (rule is_GB_cofactor_boundE_Polys) blast
  from this(1-3) show ?thesis
  proof
    fix g
    assume "g \<in> G"
    hence "\<exists>F' q. finite F' \<and> F' \<subseteq> F \<and> g = (\<Sum>f\<in>F'. q f * f) \<and>
                              (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> ?b \<and> (f \<notin> F' \<longrightarrow> q f = 0))"
      by (rule 1)
    then obtain F' q where "F' \<subseteq> F" and g: "g = (\<Sum>f\<in>F'. q f * f)" and "\<And>f. q f \<in> P[X]"
      and "\<And>f. poly_deg (q f * f) \<le> ?b" and 2: "\<And>f. f \<notin> F' \<Longrightarrow> q f = 0" by blast
    show "\<exists>q. g = (\<Sum>f\<in>F. q f * f) \<and> (\<forall>f. q f \<in> P[X] \<and> poly_deg (q f * f) \<le> ?b \<and> (f \<notin> F \<longrightarrow> q f = 0))"
    proof (intro exI allI conjI impI)
      from assms(2) \<open>F' \<subseteq> F\<close> have "(\<Sum>f\<in>F'. q f * f) = (\<Sum>f\<in>F. q f * f)"
      proof (intro sum.mono_neutral_left ballI)
        fix f
        assume "f \<in> F - F'"
        hence "f \<notin> F'" by simp
        hence "q f = 0" by (rule 2)
        thus "q f * f = 0" by simp
      qed
      thus "g = (\<Sum>f\<in>F. q f * f)" by (simp only: g)
    next
      fix f
      assume "f \<notin> F"
      with \<open>F' \<subseteq> F\<close> have "f \<notin> F'" by blast
      thus "q f = 0" by (rule 2)
    qed fact+
  qed
qed

corollary Dube_is_GB_cofactor_bound_indets:
  assumes "finite F"
  shows "is_GB_cofactor_bound F (Dube (Suc (card (\<Union>(indets ` F)))) (maxdeg F))"
  using _ assms _
proof (rule Dube_is_GB_cofactor_bound)
  from assms show "finite (\<Union>(indets ` F))" by (simp add: finite_indets)
next
  show "F \<subseteq> P[\<Union>(indets ` F)]" by (auto simp: Polys_alt)
qed

end (* extended_ord_pm_powerprod *)

end (* theory *)
