section \<open>Convex Hulls\<close>

text \<open>We define the notion of convex hull of a set or list of vectors and derive basic
  properties thereof.\<close>

theory Convex_Hull
  imports Cone
begin

context gram_schmidt
begin

definition "convex_lincomb c Vs b = (nonneg_lincomb c Vs b \<and> sum c Vs = 1)"

definition "convex_lincomb_list c Vs b = (nonneg_lincomb_list c Vs b \<and> sum c {0..<length Vs} = 1)"

definition "convex_hull Vs = {x. \<exists> Ws c. finite Ws \<and> Ws \<subseteq> Vs \<and> convex_lincomb c Ws x}"

lemma convex_hull_carrier[intro]: "Vs \<subseteq> carrier_vec n \<Longrightarrow> convex_hull Vs \<subseteq> carrier_vec n"
  unfolding convex_hull_def convex_lincomb_def nonneg_lincomb_def by auto

lemma convex_hull_mono: "Vs \<subseteq> Ws \<Longrightarrow> convex_hull Vs \<subseteq> convex_hull Ws"
  unfolding convex_hull_def by auto

lemma convex_lincomb_empty[simp]: "\<not> (convex_lincomb c {} x)"
  unfolding convex_lincomb_def by simp

lemma set_in_convex_hull:
  assumes "A \<subseteq> carrier_vec n"
  shows "A \<subseteq> convex_hull A"
proof
  fix a
  assume "a \<in> A"
  hence acarr: "a \<in> carrier_vec n" using assms by auto
  hence "convex_lincomb (\<lambda> x. 1) {a} a " unfolding convex_lincomb_def
    by (auto simp: nonneg_lincomb_def lincomb_def)
  then show "a \<in> convex_hull A" using \<open>a \<in> A\<close> unfolding convex_hull_def by auto
qed

lemma convex_hull_empty[simp]:
  "convex_hull {} = {}"
  "A \<subseteq> carrier_vec n \<Longrightarrow> convex_hull A = {} \<longleftrightarrow> A = {}"
proof -
  show "convex_hull {} = {}" unfolding convex_hull_def by auto
  then show "A \<subseteq> carrier_vec n \<Longrightarrow> convex_hull A = {} \<longleftrightarrow> A = {}"
    using set_in_convex_hull[of A] by auto
qed

lemma convex_hull_bound: assumes XBnd: "X \<subseteq> Bounded_vec Bnd"
  and X: "X \<subseteq> carrier_vec n"
shows "convex_hull X \<subseteq> Bounded_vec Bnd"
proof
  fix x
  assume "x \<in> convex_hull X"
  from this[unfolded convex_hull_def]
  obtain Y c where fin: "finite Y" and YX: "Y \<subseteq> X" and cx: "convex_lincomb c Y x" by auto
  from cx[unfolded convex_lincomb_def nonneg_lincomb_def]
  have x: "x = lincomb c Y" and sum: "sum c Y = 1" and c0: "\<And> y. y \<in> Y \<Longrightarrow> c y \<ge> 0" by auto
  from YX X XBnd have Y: "Y \<subseteq> carrier_vec n" and YBnd: "Y \<subseteq> Bounded_vec Bnd" by auto
  from x Y have dim: "dim_vec x = n" by auto
  show "x \<in> Bounded_vec Bnd" unfolding Bounded_vec_def mem_Collect_eq dim
  proof (intro allI impI)
    fix i
    assume i: "i < n"
    have "abs (x $ i) = abs (\<Sum>x\<in>Y. c x * x $ i)" unfolding x
      by (subst lincomb_index[OF i Y], auto)
    also have "\<dots> \<le> (\<Sum>x\<in>Y. abs (c x * x $ i))" by auto
    also have "\<dots> = (\<Sum>x\<in>Y. abs (c x) * abs (x $ i))" by (simp add: abs_mult)
    also have "\<dots> \<le> (\<Sum>x\<in>Y. abs (c x) * Bnd)"
      by (intro sum_mono mult_left_mono, insert YBnd[unfolded Bounded_vec_def] i Y, force+)
    also have "\<dots> = (\<Sum>x\<in>Y. abs (c x)) * Bnd"
      by (simp add: sum_distrib_right)
    also have "(\<Sum>x\<in>Y. abs (c x)) = (\<Sum>x\<in>Y. c x)"
      by (rule sum.cong, insert c0, auto)
    also have "\<dots> = 1" by fact
    finally show "\<bar>x $ i\<bar> \<le> Bnd" by auto
  qed
qed

definition "convex_hull_list Vs = {x. \<exists> c. convex_lincomb_list c Vs x}"

lemma lincomb_list_elem:
  "set Vs \<subseteq> carrier_vec n \<Longrightarrow>
   lincomb_list (\<lambda> j. if i=j then 1 else 0) Vs = (if i < length Vs then Vs ! i else 0\<^sub>v n)"
proof (induction Vs rule: rev_induct)
  case (snoc x Vs)
  have x: "x \<in> carrier_vec n" and Vs: "set Vs \<subseteq> carrier_vec n" using snoc.prems by auto
  let ?f = "\<lambda> j. if i = j then 1 else 0"
  have "lincomb_list ?f (Vs @ [x]) = lincomb_list ?f Vs + ?f (length Vs) \<cdot>\<^sub>v x"
    using x Vs by simp
  also have "\<dots> = (if i < length (Vs @ [x]) then (Vs @ [x]) ! i else 0\<^sub>v n)" (is ?goal)
    using less_linear[of i "length Vs"]
  proof (elim disjE)
    assume i: "i < length Vs"
    have "lincomb_list (\<lambda>j. if i = j then 1 else 0) Vs = Vs ! i"
      using snoc.IH[OF Vs] i by auto
    moreover have "(if i = length Vs then 1 else 0) \<cdot>\<^sub>v x = 0\<^sub>v n" using i x by auto
    moreover have "(if i < length (Vs @ [x]) then (Vs @ [x]) ! i else 0\<^sub>v n) = Vs ! i"
      using i append_Cons_nth_left by fastforce
    ultimately show ?goal using Vs i lincomb_list_carrier M.r_zero by metis
  next
    assume i: "i = length Vs"
    have "lincomb_list (\<lambda>j. if i = j then 1 else 0) Vs = 0\<^sub>v n"
      using snoc.IH[OF Vs] i by auto
    moreover have "(if i = length Vs then 1 else 0) \<cdot>\<^sub>v x = x" using i x by auto
    moreover have "(if i < length (Vs @ [x]) then (Vs @ [x]) ! i else 0\<^sub>v n) = x"
      using i append_Cons_nth_left by simp
    ultimately show ?goal using x by simp
  next
    assume i: "i > length Vs"
    have "lincomb_list (\<lambda>j. if i = j then 1 else 0) Vs = 0\<^sub>v n"
      using snoc.IH[OF Vs] i by auto
    moreover have "(if i = length Vs then 1 else 0) \<cdot>\<^sub>v x = 0\<^sub>v n" using i x by auto
    moreover have "(if i < length (Vs @ [x]) then (Vs @ [x]) ! i else 0\<^sub>v n) = 0\<^sub>v n"
      using i by simp
    ultimately show ?goal by simp
  qed
  finally show ?case by auto
qed simp

lemma set_in_convex_hull_list: fixes Vs :: "'a vec list"
  assumes "set Vs \<subseteq> carrier_vec n"
  shows "set Vs \<subseteq> convex_hull_list Vs"
proof
  fix x assume "x \<in> set Vs"
  then obtain i where i: "i < length Vs"
    and x: "x = Vs ! i" using set_conv_nth[of Vs] by auto
  let ?f = "\<lambda> j. if i = j then 1 else 0 :: 'a"
  have "lincomb_list ?f Vs = x" using i x lincomb_list_elem[OF assms] by auto
  moreover have "\<forall> j < length Vs. ?f j \<ge> 0" by auto
  moreover have "sum ?f {0..<length Vs} = 1" using i by simp
  ultimately show "x \<in> convex_hull_list Vs"
    unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
    by auto
qed

lemma convex_hull_list_combination:
  assumes Vs: "set Vs \<subseteq> carrier_vec n"
    and x: "x \<in> convex_hull_list Vs"
    and y: "y \<in> convex_hull_list Vs"
    and l0: "0 \<le> l" and l1: "l \<le> 1"
  shows "l \<cdot>\<^sub>v x + (1 - l) \<cdot>\<^sub>v y \<in> convex_hull_list Vs"
proof -
  from x obtain cx where x: "lincomb_list cx Vs = x" and cx0: "\<forall> i < length Vs. cx i \<ge> 0"
    and cx1: "sum cx {0..<length Vs} = 1"
    unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
    by auto
  from y obtain cy where y: "lincomb_list cy Vs = y" and cy0: "\<forall> i < length Vs. cy i \<ge> 0"
    and cy1: "sum cy {0..<length Vs} = 1"
    unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
    by auto
  let ?c = "\<lambda> i. l * cx i + (1 - l) * cy i"
  have "set Vs \<subseteq> carrier_vec n \<Longrightarrow>
        lincomb_list ?c Vs = l \<cdot>\<^sub>v lincomb_list cx Vs + (1 - l) \<cdot>\<^sub>v lincomb_list cy Vs"
  proof (induction Vs rule: rev_induct)
    case (snoc v Vs)
    have v: "v \<in> carrier_vec n" and Vs: "set Vs \<subseteq> carrier_vec n"
      using snoc.prems by auto
    have "lincomb_list ?c (Vs @ [v]) = lincomb_list ?c Vs + ?c (length Vs) \<cdot>\<^sub>v v"
      using snoc.prems by auto
    also have "lincomb_list ?c Vs =
               l \<cdot>\<^sub>v lincomb_list cx Vs + (1 - l) \<cdot>\<^sub>v lincomb_list cy Vs"
      by (rule snoc.IH[OF Vs])
    also have "?c (length Vs) \<cdot>\<^sub>v v =
               l \<cdot>\<^sub>v (cx (length Vs) \<cdot>\<^sub>v v) + (1 - l) \<cdot>\<^sub>v (cy (length Vs) \<cdot>\<^sub>v v)"
      using add_smult_distrib_vec smult_smult_assoc by metis
    also have "l \<cdot>\<^sub>v lincomb_list cx Vs + (1 - l) \<cdot>\<^sub>v lincomb_list cy Vs + \<dots> =
                  l \<cdot>\<^sub>v (lincomb_list cx Vs + cx (length Vs) \<cdot>\<^sub>v v) +
                  (1 - l) \<cdot>\<^sub>v (lincomb_list cy Vs + cy (length Vs) \<cdot>\<^sub>v v)"
      using lincomb_list_carrier[OF Vs] v
      by (simp add: M.add.m_assoc M.add.m_lcomm smult_r_distr)
    finally show ?case using Vs v by simp
  qed simp
  hence "lincomb_list ?c Vs = l \<cdot>\<^sub>v x + (1 - l) \<cdot>\<^sub>v y" using Vs x y by simp
  moreover have "\<forall> i < length Vs. ?c i \<ge> 0" using cx0 cy0 l0 l1 by simp
  moreover have "sum ?c {0..<length Vs} = 1"
  proof(simp add: sum.distrib)
    have "(\<Sum>i = 0..<length Vs. (1 - l) * cy i) = (1 - l) * sum cy {0..<length Vs}"
      using sum_distrib_left by metis
    moreover have "(\<Sum>i = 0..<length Vs. l * cx i) = l * sum cx {0..<length Vs}"
      using sum_distrib_left by metis
    ultimately show "(\<Sum>i = 0..<length Vs. l * cx i) + (\<Sum>i = 0..<length Vs. (1 - l) * cy i) = 1"
      using cx1 cy1 by simp
  qed
  ultimately show ?thesis
    unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
    by auto
qed

lemma convex_hull_list_mono:
  assumes "set Ws \<subseteq> carrier_vec n"
  shows "set Vs \<subseteq> set Ws \<Longrightarrow> convex_hull_list Vs \<subseteq> convex_hull_list Ws"
proof (standard, induction Vs)
  case Nil
  from Nil(2) show ?case unfolding convex_hull_list_def convex_lincomb_list_def by auto
next
  case (Cons v Vs)
  have v: "v \<in> set Ws" and Vs: "set Vs \<subseteq> set Ws" using Cons.prems(1) by auto
  hence v1: "v \<in> convex_hull_list Ws" using set_in_convex_hull_list[OF assms] by auto
  from Cons.prems(2) obtain c
    where x: "lincomb_list c (v # Vs) = x" and c0: "\<forall> i < length Vs + 1. c i \<ge> 0"
      and c1: "sum c {0..<length Vs + 1} = 1"
    unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
    by auto
  have x: "x = c 0 \<cdot>\<^sub>v v + lincomb_list (c \<circ> Suc) Vs" using Vs v assms x by auto

  show ?case proof (cases)
    assume P: "c 0 = 1"
    hence "sum (c \<circ> Suc) {0..<length Vs} = 0"
      using sum.atLeast0_lessThan_Suc_shift c1
      by (metis One_nat_def R.show_r_zero add.right_neutral add_Suc_right)
    moreover have "\<And> i. i \<in> {0..<length Vs} \<Longrightarrow> (c \<circ> Suc) i \<ge> 0"
      using c0 by simp
    ultimately have "\<forall> i \<in> {0..<length Vs}. (c \<circ> Suc) i = 0"
      using sum_nonneg_eq_0_iff by blast
    hence "\<And> i. i < length Vs \<Longrightarrow> (c \<circ> Suc) i \<cdot>\<^sub>v Vs ! i = 0\<^sub>v n"
      using Vs assms by (simp add: subset_code(1))
    hence "lincomb_list (c \<circ> Suc) Vs = 0\<^sub>v n"
      using lincomb_list_eq_0 by simp
    hence "x = v" using P x v assms by auto
    thus ?case using v1 by auto

  next

    assume P: "c 0 \<noteq> 1"
    have c1: "c 0 + sum (c \<circ> Suc) {0..<length Vs} = 1"
      using sum.atLeast0_lessThan_Suc_shift[of c] c1 by simp
    have "sum (c \<circ> Suc) {0..<length Vs} \<ge> 0" by (rule sum_nonneg, insert c0, simp)
    hence "c 0 < 1" using P c1 by auto
    let ?c' = "\<lambda> i. 1 / (1 - c 0) * (c \<circ> Suc) i"
    have "sum ?c' {0..<length Vs} = 1 / (1 - c 0) * sum (c \<circ> Suc) {0..<length Vs}"
      using c1 P sum_distrib_left by metis
    hence "sum ?c' {0..<length Vs} = 1" using P c1 by simp
    moreover have "\<forall> i < length Vs. ?c' i \<ge> 0" using c0 `c 0 < 1` by simp
    ultimately have c': "lincomb_list ?c' Vs \<in> convex_hull_list Ws"
      using Cons.IH[OF Vs]
        convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
      by blast
    have "lincomb_list ?c' Vs = 1 / (1 - c 0) \<cdot>\<^sub>v lincomb_list (c \<circ> Suc) Vs"
      by(rule lincomb_list_smult, insert Vs assms, auto)
    hence "(1 - c 0) \<cdot>\<^sub>v lincomb_list ?c' Vs = lincomb_list (c \<circ> Suc) Vs"
      using P by auto
    hence "x = c 0 \<cdot>\<^sub>v v + (1 - c 0) \<cdot>\<^sub>v lincomb_list ?c' Vs" using x by auto
    thus "x \<in> convex_hull_list Ws"
      using convex_hull_list_combination[OF assms v1 c'] c0 `c 0 < 1`
      by simp
  qed
qed

lemma convex_hull_list_eq_set:
  "set Vs \<subseteq> carrier_vec n \<Longrightarrow> set Vs = set Ws \<Longrightarrow> convex_hull_list Vs = convex_hull_list Ws"
  using convex_hull_list_mono by blast

lemma find_indices_empty: "(find_indices x Vs = []) = (x \<notin> set Vs)"
proof (induction Vs rule: rev_induct)
  case (snoc v Vs)
  show ?case
  proof
    assume "find_indices x (Vs @ [v]) = []"
    hence "x \<noteq> v \<and> find_indices x Vs = []" by auto
    thus "x \<notin> set (Vs @ [v])" using snoc by simp
  next
    assume "x \<notin> set (Vs @ [v])"
    hence "x \<noteq> v \<and> find_indices x Vs = []" using snoc by auto
    thus "find_indices x (Vs @ [v]) = []" by simp
  qed
qed simp

lemma distinct_list_find_indices:
  shows "\<lbrakk> i < length Vs; Vs ! i = x; distinct Vs \<rbrakk> \<Longrightarrow> find_indices x Vs = [i]"
proof (induction Vs rule: rev_induct)
  case (snoc v Vs)
  have dist: "distinct Vs" and xVs: "v \<notin> set Vs" using snoc.prems(3) by(simp_all)
  show ?case
  proof (cases)
    assume i: "i = length Vs"
    hence "x = v" using snoc.prems(2) by auto
    thus ?case using xVs find_indices_empty i
      by fastforce
  next
    assume "i \<noteq> length Vs"
    hence i: "i < length Vs" using snoc.prems(1) by simp
    hence Vsi: "Vs ! i = x" using snoc.prems(2) append_Cons_nth_left by fastforce
    hence "x \<noteq> v" using snoc.prems(3) i by auto
    thus ?case using snoc.IH[OF i Vsi dist] by simp
  qed
qed auto

lemma finite_convex_hull_iff_convex_hull_list: assumes Vs: "Vs \<subseteq> carrier_vec n"
  and id': "Vs = set Vsl'"
shows "convex_hull Vs = convex_hull_list Vsl'"
proof -
  have fin: "finite Vs" unfolding id' by auto
  from finite_distinct_list fin obtain Vsl
    where id: "Vs = set Vsl" and dist: "distinct Vsl" by auto
  from Vs id have Vsl: "set Vsl \<subseteq> carrier_vec n" by auto
  {
    fix c :: "nat \<Rightarrow> 'a"
    have "distinct Vsl \<Longrightarrow>(\<Sum>x\<in>set Vsl. sum_list (map c (find_indices x Vsl))) =
                          sum c {0..<length Vsl}"
    proof (induction Vsl rule: rev_induct)
      case (snoc v Vsl)
      let ?coef = "\<lambda> x. sum_list (map c (find_indices x (Vsl @ [v])))"
      let ?coef' = "\<lambda> x. sum_list (map c (find_indices x Vsl))"
      have dist: "distinct Vsl" using snoc.prems by simp
      have "sum ?coef (set (Vsl @ [v])) = sum_list (map ?coef (Vsl @ [v]))"
        by (rule sum.distinct_set_conv_list[OF snoc.prems, of ?coef])
      also have "\<dots> = sum_list (map ?coef Vsl) + ?coef v" by simp
      also have "sum_list (map ?coef Vsl) = sum ?coef (set Vsl)"
        using sum.distinct_set_conv_list[OF dist, of ?coef] by auto
      also have "\<dots> = sum ?coef' (set Vsl)"
      proof (intro R.finsum_restrict[of ?coef] restrict_ext, standard)
        fix x
        assume "x \<in> set Vsl"
        then obtain i where i: "i < length Vsl" and x: "x = Vsl ! i"
          using in_set_conv_nth[of x Vsl] by blast
        hence "(Vsl @ [v]) ! i = x" by (simp add: append_Cons_nth_left)
        hence "?coef x = c i"
          using distinct_list_find_indices[OF _ _ snoc.prems] i by fastforce
        also have  "c i = ?coef' x"
          using distinct_list_find_indices[OF i _ dist] x by simp
        finally show "?coef x = ?coef' x" by auto
      qed
      also have "\<dots> = sum c {0..<length Vsl}" by (rule snoc.IH[OF dist])
      also have "?coef v = c (length Vsl)"
        using distinct_list_find_indices[OF _ _ snoc.prems, of "length Vsl" v]
          nth_append_length by simp
      finally show ?case using sum.atLeast0_lessThan_Suc by simp
    qed simp
  } note sum_sumlist = this
  {
    fix b
    assume "b \<in> convex_hull_list Vsl"
    then obtain c where b: "lincomb_list c Vsl = b" and c: "(\<forall> i < length Vsl. c i \<ge> 0)"
      and c1: "sum c {0..<length Vsl} = 1"
      unfolding convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def
      by auto
    have "convex_lincomb (mk_coeff Vsl c) Vs b"
      unfolding b[symmetric] convex_lincomb_def nonneg_lincomb_def
      apply (subst lincomb_list_as_lincomb[OF Vsl])
      by (insert c c1, auto simp: id mk_coeff_def dist sum_sumlist intro!: sum_list_nonneg)
    hence "b \<in> convex_hull Vs"
      unfolding convex_hull_def convex_lincomb_def using fin by blast
  }
  moreover
  {
    fix b
    assume "b \<in> convex_hull Vs"
    then obtain c Ws where Ws: "Ws \<subseteq> Vs" and b: "lincomb c Ws = b"
      and c: "c ` Ws \<subseteq> {x. x \<ge> 0}" and c1: "sum c Ws = 1"
      unfolding convex_hull_def convex_lincomb_def nonneg_lincomb_def by auto
    let ?d = "\<lambda> x. if x \<in> Ws then c x else 0"
    have "lincomb ?d Vs = lincomb c Ws + lincomb (\<lambda> x. 0) (Vs - Ws)"
      using lincomb_union2[OF _ _ Diff_disjoint[of Ws Vs], of c "\<lambda> x. 0"]
        fin Vs Diff_partition[OF Ws] by metis
    also have "lincomb (\<lambda> x. 0) (Vs - Ws) = 0\<^sub>v n"
      using lincomb_zero[of "Vs - Ws" "\<lambda> x. 0"] Vs by auto
    finally have "lincomb ?d Vs = b" using b lincomb_closed Vs Ws by auto
    moreover have "?d ` Vs \<subseteq> {t. t \<ge> 0}" using c by auto
    moreover have "sum ?d Vs = 1" using  c1 R.extend_sum[OF fin Ws] by auto
    ultimately have "\<exists> c. convex_lincomb c Vs b"
      unfolding convex_lincomb_def nonneg_lincomb_def by blast
  }
  moreover
  {
    fix b
    assume "\<exists> c. convex_lincomb c Vs b"
    then obtain c where b: "lincomb c Vs = b" and c: "c ` Vs \<subseteq> {x. x \<ge> 0}"
      and c1: "sum c Vs = 1"
      unfolding convex_lincomb_def nonneg_lincomb_def by auto
    from lincomb_as_lincomb_list_distinct[OF Vsl dist, of c]
    have b: "lincomb_list (\<lambda>i. c (Vsl ! i)) Vsl = b"
      unfolding b[symmetric] id by simp
    have "1 = sum c (set Vsl)" using c1 id by auto
    also have "\<dots> = sum_list (map c Vsl)" by(rule sum.distinct_set_conv_list[OF dist])
    also have "\<dots> = sum ((!) (map c Vsl)) {0..<length Vsl}"
      using sum_list_sum_nth length_map by metis
    also have "\<dots> = sum (\<lambda> i. c (Vsl ! i)) {0..<length Vsl}" by simp
    finally have sum_1: "(\<Sum>i = 0..<length Vsl. c (Vsl ! i)) = 1" by simp

    have "\<exists> c. convex_lincomb_list c Vsl b"
      unfolding convex_lincomb_list_def nonneg_lincomb_list_def
      by (intro exI[of _ "\<lambda>i. c (Vsl ! i)"] conjI b sum_1)
        (insert c, force simp: set_conv_nth id)
    hence "b \<in> convex_hull_list Vsl" unfolding convex_hull_list_def by auto
  }
  ultimately have "convex_hull Vs = convex_hull_list Vsl" by auto
  also have "convex_hull_list Vsl = convex_hull_list Vsl'"
    using convex_hull_list_eq_set[OF Vsl, of Vsl'] id id' by simp
  finally show ?thesis by simp
qed

definition "convex S = (convex_hull S = S)"

lemma convex_convex_hull: "convex S \<Longrightarrow> convex_hull S = S"
  unfolding convex_def by auto

lemma convex_hull_convex_hull_listD: assumes A: "A \<subseteq> carrier_vec n"
  and x: "x \<in> convex_hull A"
shows "\<exists> as. set as \<subseteq> A \<and> x \<in> convex_hull_list as"
proof -
  from x[unfolded convex_hull_def]
  obtain X c where finX: "finite X" and XA: "X \<subseteq> A" and "convex_lincomb c X x" by auto
  hence x: "x \<in> convex_hull X" unfolding convex_hull_def by auto
  from finite_list[OF finX] obtain xs where X: "X = set xs" by auto
  from finite_convex_hull_iff_convex_hull_list[OF _ this] x XA A have x: "x \<in> convex_hull_list xs" by auto
  thus ?thesis using XA unfolding X by auto
qed

lemma convex_hull_convex_sum: assumes A: "A \<subseteq> carrier_vec n"
  and x: "x \<in> convex_hull A"
  and y: "y \<in> convex_hull A"
  and a: "0 \<le> a" "a \<le> 1"
shows "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> convex_hull A"
proof -
  from convex_hull_convex_hull_listD[OF A x] obtain xs where xs: "set xs \<subseteq> A"
    and x: "x \<in> convex_hull_list xs" by auto
  from convex_hull_convex_hull_listD[OF A y] obtain ys where ys: "set ys \<subseteq> A"
    and y: "y \<in> convex_hull_list ys" by auto
  have fin: "finite (set (xs @ ys))" by auto
  have sub: "set (xs @ ys) \<subseteq> A" using xs ys by auto
  from convex_hull_list_mono[of "xs @ ys" xs] x sub A have x: "x \<in> convex_hull_list (xs @ ys)" by auto
  from convex_hull_list_mono[of "xs @ ys" ys] y sub A have y: "y \<in> convex_hull_list (xs @ ys)" by auto
  from convex_hull_list_combination[OF _ x y a]
  have "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> convex_hull_list (xs @ ys)" using sub A by auto
  from finite_convex_hull_iff_convex_hull_list[of _ "xs @ ys"] this sub A
  have "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> convex_hull (set (xs @ ys))" by auto
  with convex_hull_mono[OF sub]
  show "a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> convex_hull A" by auto
qed

lemma convexI: assumes S: "S \<subseteq> carrier_vec n"
  and step: "\<And> a x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> 0 \<le> a \<Longrightarrow> a \<le> 1 \<Longrightarrow> a \<cdot>\<^sub>v x + (1 - a) \<cdot>\<^sub>v y \<in> S"
shows "convex S"
  unfolding convex_def
proof (standard, standard)
  fix z
  assume "z \<in> convex_hull S"
  from this[unfolded convex_hull_def] obtain W c where "finite W" and WS: "W \<subseteq> S"
    and "convex_lincomb c W z" by auto
  then show "z \<in> S"
  proof (induct W arbitrary: c z)
    case empty
    thus ?case unfolding convex_lincomb_def by auto
  next
    case (insert w W c z)
    have "convex_lincomb c (insert w W) z" by fact
    hence zl: "z = lincomb c (insert w W)" and nonneg: "\<And> w. w \<in> W \<Longrightarrow> 0 \<le> c w"
      and cw: "c w \<ge> 0"
      and sum: "sum c (insert w W) = 1"
      unfolding convex_lincomb_def nonneg_lincomb_def by auto
    have zl: "z = c w \<cdot>\<^sub>v w + lincomb c W" unfolding zl
      by (rule lincomb_insert2, insert insert S, auto)
    have sum: "c w + sum c W = 1" unfolding sum[symmetric]
      by (subst sum.insert, insert insert, auto)
    have W: "W \<subseteq> carrier_vec n" and w: "w \<in> carrier_vec n" using S insert by auto
    show ?case
    proof (cases "sum c W = 0")
      case True
      with nonneg have c0: "\<And> w. w \<in> W \<Longrightarrow> c w = 0"
        using insert(1) sum_nonneg_eq_0_iff by auto
      with sum have cw: "c w = 1" by auto
      have lin0: "lincomb c W = 0\<^sub>v n"
        by (intro lincomb_zero W, insert c0, auto)
      have "z = w" unfolding zl cw lin0 using w by simp
      with insert(4) show ?thesis by simp
    next
      case False
      have "sum c W \<ge> 0" using nonneg by (metis sum_nonneg)
      with False have pos: "sum c W > 0" by auto
      define b where "b = (\<lambda> w. inverse (sum c W) * c w)"
      have "convex_lincomb b W (lincomb b W)"
        unfolding convex_lincomb_def nonneg_lincomb_def b_def
      proof (intro conjI refl)
        show "(\<lambda>w. inverse (sum c W) * c w) ` W \<subseteq> Collect ((\<le>) 0)" using nonneg pos by auto
        show "(\<Sum>w\<in>W. inverse (sum c W) * c w) = 1" unfolding sum_distrib_left[symmetric] using False by auto
      qed
      from insert(3)[OF _ this] insert
      have IH: "lincomb b W \<in> S" by auto
      have lin: "lincomb c W = sum c W \<cdot>\<^sub>v lincomb b W"
        unfolding b_def
        by (subst lincomb_smult[symmetric, OF W], rule lincomb_cong[OF _ W], insert False, auto)
      from sum cw pos have sum: "sum c W = 1 - c w" and cw1: "c w \<le> 1" by auto
      show ?thesis unfolding zl lin unfolding sum
        by (rule step[OF _ IH cw cw1], insert insert, auto)
    qed
  qed
next
  show "S \<subseteq> convex_hull S" using S by (rule set_in_convex_hull)
qed

lemma convex_hulls_are_convex: assumes "A \<subseteq> carrier_vec n"
  shows "convex (convex_hull A)"
  by (intro convexI convex_hull_convex_sum convex_hull_carrier assms)

lemma convex_hull_sum: assumes A: "A \<subseteq> carrier_vec n" and B: "B \<subseteq> carrier_vec n"
  shows "convex_hull (A + B) = convex_hull A + convex_hull B"
proof
  note cA = convex_hull_carrier[OF A]
  note cB = convex_hull_carrier[OF B]
  have "convex (convex_hull A + convex_hull B)"
  proof (intro convexI sum_carrier_vec convex_hull_carrier A B)
    fix a :: 'a and x1 x2
    assume "x1 \<in> convex_hull A + convex_hull B" "x2 \<in> convex_hull A + convex_hull B"
    then obtain y1 y2 z1 z2 where
      x12: "x1 = y1 + z1" "x2 = y2 + z2" and
      y12: "y1 \<in> convex_hull A" "y2 \<in> convex_hull A" and
      z12: "z1 \<in> convex_hull B" "z2 \<in> convex_hull B"
      unfolding set_plus_def by auto
    from y12 z12 cA cB have carr:
      "y1 \<in> carrier_vec n" "y2 \<in> carrier_vec n"
      "z1 \<in> carrier_vec n" "z2 \<in> carrier_vec n"
      by auto
    assume a: "0 \<le> a" "a \<le> 1"
    have A: "a \<cdot>\<^sub>v y1 + (1 - a) \<cdot>\<^sub>v y2 \<in> convex_hull A" using y12 a A by (metis convex_hull_convex_sum)
    have B: "a \<cdot>\<^sub>v z1 + (1 - a) \<cdot>\<^sub>v z2 \<in> convex_hull B" using z12 a B by (metis convex_hull_convex_sum)
    have "a \<cdot>\<^sub>v x1 + (1 - a) \<cdot>\<^sub>v x2 = (a \<cdot>\<^sub>v y1 + a \<cdot>\<^sub>v z1) + ((1 - a) \<cdot>\<^sub>v y2 + (1 - a) \<cdot>\<^sub>v z2)" unfolding x12
      using carr by (auto simp: smult_add_distrib_vec)
    also have "\<dots> = (a \<cdot>\<^sub>v y1 + (1 - a) \<cdot>\<^sub>v y2) + (a \<cdot>\<^sub>v z1 + (1 - a) \<cdot>\<^sub>v z2)" using carr
      by (intro eq_vecI, auto)
    finally show "a \<cdot>\<^sub>v x1 + (1 - a) \<cdot>\<^sub>v x2 \<in> convex_hull A + convex_hull B"
      using A B by auto
  qed
  from convex_convex_hull[OF this]
  have id: "convex_hull (convex_hull A + convex_hull B) = convex_hull A + convex_hull B" .
  show "convex_hull (A + B) \<subseteq> convex_hull A + convex_hull B"
    by (subst id[symmetric], rule convex_hull_mono[OF set_plus_mono2]; intro set_in_convex_hull A B)
  show "convex_hull A + convex_hull B \<subseteq> convex_hull (A + B)"
  proof
    fix x
    assume "x \<in> convex_hull A + convex_hull B"
    then obtain y z where x: "x = y + z" and y: "y \<in> convex_hull A" and z: "z \<in> convex_hull B"
      by (auto simp: set_plus_def)
    from convex_hull_convex_hull_listD[OF A y] obtain ys where ysA: "set ys \<subseteq> A" and
      y: "y \<in> convex_hull_list ys" by auto
    from convex_hull_convex_hull_listD[OF B z] obtain zs where zsB: "set zs \<subseteq> B" and
      z: "z \<in> convex_hull_list zs" by auto
    from y[unfolded convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def]
    obtain c where yid: "y = lincomb_list c ys"
      and conv_c: "(\<forall>i<length ys. 0 \<le> c i) \<and> sum c {0..<length ys} = 1"
      by auto
    from z[unfolded convex_hull_list_def convex_lincomb_list_def nonneg_lincomb_list_def]
    obtain d where zid: "z = lincomb_list d zs"
      and conv_d: "(\<forall>i<length zs. 0 \<le> d i) \<and> sum d {0..<length zs} = 1"
      by auto
    from ysA A have ys: "set ys \<subseteq> carrier_vec n" by auto
    from zsB B have zs: "set zs \<subseteq> carrier_vec n" by auto
    have [intro, simp]: "lincomb_list x ys \<in> carrier_vec n" for x using lincomb_list_carrier[OF ys] .
    have [intro, simp]: "lincomb_list x zs \<in> carrier_vec n" for x using lincomb_list_carrier[OF zs] .
    have dim[simp]: "dim_vec (lincomb_list d zs) = n" by auto
    from yid have y: "y \<in> carrier_vec n" by auto
    from zid have z: "z \<in> carrier_vec n" by auto
    {
      fix x
      assume "x \<in> set (map ((+) y) zs)"
      then obtain z where "x = y + z" and "z \<in> set zs" by auto
      then obtain j where j: "j < length zs" and x: "x = y + zs ! j" unfolding set_conv_nth by auto
      hence mem: "zs ! j \<in> set zs" by auto
      hence zsj: "zs ! j \<in> carrier_vec n" using zs by auto
      let ?list = "(map (\<lambda> y. y + zs ! j) ys)"
      let ?set = "set ?list"
      have set: "?set \<subseteq> carrier_vec n" using ys A zsj by auto
      have lin_map: "lincomb_list c ?list \<in> carrier_vec n"
        by (intro lincomb_list_carrier[OF set])
      have "y + (zs ! j) = lincomb_list c ?list"
        unfolding yid using zsj lin_map lincomb_list_index[OF _ set] lincomb_list_index[OF _ ys]
        by (intro eq_vecI, auto simp: field_simps sum_distrib_right[symmetric] conv_c)
      hence "convex_lincomb_list c ?list (y + (zs ! j))"
        unfolding convex_lincomb_list_def nonneg_lincomb_list_def using conv_c by auto
      hence "y + (zs ! j) \<in> convex_hull_list ?list" unfolding convex_hull_list_def by auto
      with finite_convex_hull_iff_convex_hull_list[OF set refl]
      have "(y + zs ! j) \<in> convex_hull ?set" by auto
      also have "\<dots> \<subseteq> convex_hull (A + B)"
        by (rule convex_hull_mono, insert mem ys ysA zsB, force simp: set_plus_def)
      finally have "x \<in> convex_hull (A + B)" unfolding x .
    } note step1 = this
    {
      let ?list = "map ((+) y) zs"
      let ?set = "set ?list"
      have set: "?set \<subseteq> carrier_vec n" using zs B y by auto
      have lin_map: "lincomb_list d ?list \<in> carrier_vec n"
        by (intro lincomb_list_carrier[OF set])
      have [simp]: "i < n \<Longrightarrow> (\<Sum>j = 0..<length zs. d j * (y + zs ! j) $ i) =
        (\<Sum>j = 0..<length zs. d j * (y $ i + zs ! j $ i))" for i
        by (rule sum.cong, insert zs[unfolded set_conv_nth] y, auto)
      have "y + z = lincomb_list d ?list"
        unfolding zid using y zs lin_map lincomb_list_index[OF _ set] lincomb_list_index[OF _ zs]
          set lincomb_list_carrier[OF zs, of d] zs[unfolded set_conv_nth]
        by (intro eq_vecI, auto simp: field_simps sum_distrib_right[symmetric] conv_d)
      hence "convex_lincomb_list d ?list x" unfolding x
        unfolding convex_lincomb_list_def nonneg_lincomb_list_def using conv_d by auto
      hence "x \<in> convex_hull_list ?list" unfolding convex_hull_list_def by auto
      with finite_convex_hull_iff_convex_hull_list[OF set refl]
      have "x \<in> convex_hull ?set" by auto
      also have "\<dots> \<subseteq> convex_hull (convex_hull (A + B))"
        by (rule convex_hull_mono, insert step1, auto)
      also have "\<dots> = convex_hull (A + B)"
        by (rule convex_convex_hull[OF convex_hulls_are_convex], intro sum_carrier_vec A B)
      finally show "x \<in> convex_hull (A + B)" .
    }
  qed
qed

lemma convex_hull_in_cone:
  "convex_hull C \<subseteq> cone C"
  unfolding convex_hull_def cone_def convex_lincomb_def finite_cone_def by auto

lemma convex_cone:
  assumes C: "C \<subseteq> carrier_vec n"
  shows "convex (cone C)"
  unfolding convex_def
  using convex_hull_in_cone set_in_convex_hull[OF cone_carrier[OF C]] cone_cone[OF C]
  by blast

end
end