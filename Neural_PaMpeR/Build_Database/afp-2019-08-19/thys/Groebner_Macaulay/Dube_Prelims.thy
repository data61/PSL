(* Author: Alexander Maletzky *)

section \<open>Preliminaries\<close>

theory Dube_Prelims
  imports Groebner_Bases.General
begin

subsection \<open>Sets\<close>

lemma card_geq_ex_subset:
  assumes "card A \<ge> n"
  obtains B where "card B = n" and "B \<subseteq> A"
  using assms
proof (induct n arbitrary: thesis)
  case base: 0
  show ?case
  proof (rule base(1))
    show "card {} = 0" by simp
  next
    show "{} \<subseteq> A" ..
  qed
next
  case ind: (Suc n)
  from ind(3) have "n < card A" by simp
  obtain B where card: "card B = n" and "B \<subseteq> A"
  proof (rule ind(1))
    from \<open>n < card A\<close> show "n \<le> card A" by simp
  qed
  from \<open>n < card A\<close> have "card A \<noteq> 0" by simp
  with card_infinite[of A] have "finite A" by blast
  let ?C = "A - B"
  have "?C \<noteq> {}"
  proof
    assume "A - B = {}"
    hence "A \<subseteq> B" by simp
    from this \<open>B \<subseteq> A\<close> have "A = B" ..
    from \<open>n < card A\<close> show False unfolding \<open>A = B\<close> card by simp
  qed
  then obtain c where "c \<in> ?C" by auto
  hence "c \<notin> B" by simp
  hence "B - {c} = B" by simp
  show ?case
  proof (rule ind(2))
    thm card_insert
    have "card (B \<union> {c}) = card (insert c B)" by simp
    also have "... = Suc (card (B - {c}))"
      by (rule card_insert, rule finite_subset, fact \<open>B \<subseteq> A\<close>, fact)
    finally show "card (B \<union> {c}) = Suc n" unfolding \<open>B - {c} = B\<close> card .
  next
    show "B \<union> {c} \<subseteq> A" unfolding Un_subset_iff
    proof (intro conjI, fact)
      from \<open>c \<in> ?C\<close> show "{c} \<subseteq> A" by auto
    qed
  qed
qed

lemma card_2_E_1:
  assumes "card A = 2" and "x \<in> A"
  obtains y where "x \<noteq> y" and "A = {x, y}"
proof -
  have "A - {x} \<noteq> {}"
  proof
    assume "A - {x} = {}"
    with assms(2) have "A = {x}" by auto
    hence "card A = 1" by simp
    with assms show False by simp
  qed
  then obtain y where "y \<in> A - {x}" by auto
  hence "y \<in> A" and "x \<noteq> y" by auto
  show ?thesis
  proof
    show "A = {x, y}"
    proof (rule sym, rule card_seteq)
      from assms(1) show "finite A" using card_infinite by fastforce
    next
      from \<open>x \<in> A\<close> \<open>y \<in> A\<close> show "{x, y} \<subseteq> A" by simp
    next
      from \<open>x \<noteq> y\<close> show "card A \<le> card {x, y}" by (simp add: assms(1))
    qed
  qed fact
qed

lemma card_2_E:
  assumes "card A = 2"
  obtains x y where "x \<noteq> y" and "A = {x, y}"
proof -
  from assms have "A \<noteq> {}" by auto
  then obtain x where "x \<in> A" by blast
  with assms obtain y where "x \<noteq> y" and "A = {x, y}" by (rule card_2_E_1)
  thus ?thesis ..
qed

subsection \<open>Sums\<close>

lemma sum_tail_nat: "0 < b \<Longrightarrow> a \<le> (b::nat) \<Longrightarrow> sum f {a..b} = f b + sum f {a..b - 1}"
  by (metis One_nat_def Suc_pred add.commute not_le sum.cl_ivl_Suc)

lemma sum_atLeast_Suc_shift: "0 < b \<Longrightarrow> a \<le> b \<Longrightarrow> sum f {Suc a..b} = (\<Sum>i=a..b - 1. f (Suc i))"
  by (metis Suc_pred' sum.shift_bounds_cl_Suc_ivl)

lemma sum_split_nat_ivl:
  "a \<le> Suc j \<Longrightarrow> j \<le> b \<Longrightarrow> sum f {a..j} + sum f {Suc j..b} = sum f {a..b}"
  by (metis Suc_eq_plus1 le_Suc_ex sum.ub_add_nat)

subsection \<open>@{const count_list}\<close>

lemma count_list_eq_0_iff: "count_list xs x = 0 \<longleftrightarrow> x \<notin> set xs"
  by (induct xs) simp_all

lemma count_list_append: "count_list (xs @ ys) x = count_list xs x + count_list ys x"
  by (induct xs) simp_all

lemma count_list_map_ge: "count_list xs x \<le> count_list (map f xs) (f x)"
  by (induct xs) simp_all

lemma count_list_gr_1_E:
  assumes "1 < count_list xs x"
  obtains i j where "i < j" and "j < length xs" and "xs ! i = x" and "xs ! j = x"
proof -
  from assms have "count_list xs x \<noteq> 0" by simp
  hence "x \<in> set xs" by (simp only: count_list_eq_0_iff not_not)
  then obtain ys zs where xs: "xs = ys @ x # zs" and "x \<notin> set ys" by (meson split_list_first)
  hence "count_list xs x = Suc (count_list zs x)" by (simp add: count_list_append)
  with assms have "count_list zs x \<noteq> 0" by simp
  hence "x \<in> set zs" by (simp only: count_list_eq_0_iff not_not)
  then obtain j where "j < length zs" and "x = zs ! j" by (metis in_set_conv_nth)
  show ?thesis
  proof
    show "length ys < length ys + Suc j" by simp
  next
    from \<open>j < length zs\<close> show "length ys + Suc j < length xs" by (simp add: xs)
  next
    show "xs ! length ys = x" by (simp add: xs)
  next
    show "xs ! (length ys + Suc j) = x"
      by (simp only: xs \<open>x = zs ! j\<close> nth_append_length_plus nth_Cons_Suc)
  qed
qed

subsection \<open>@{const listset}\<close>

lemma listset_Cons: "listset (x # xs) = (\<Union>y\<in>x. (#) y ` listset xs)"
  by (auto simp: set_Cons_def)

lemma listset_ConsI: "y \<in> x \<Longrightarrow> ys' \<in> listset xs \<Longrightarrow> ys = y # ys' \<Longrightarrow> ys \<in> listset (x # xs)"
  by (simp add: set_Cons_def)

lemma listset_ConsE:
  assumes "ys \<in> listset (x# xs)"
  obtains y ys' where "y \<in> x" and "ys' \<in> listset xs" and "ys = y # ys'"
  using assms by (auto simp: set_Cons_def)

lemma listsetI:
  "length ys = length xs \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i) \<Longrightarrow> ys \<in> listset xs"
  by (induct ys xs rule: list_induct2)
     (simp_all, smt Suc_mono list.sel(3) mem_Collect_eq nth_Cons_0 nth_tl set_Cons_def zero_less_Suc)

lemma listsetD:
  assumes "ys \<in> listset xs"
  shows "length ys = length xs" and "\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i"
proof -
  from assms have "length ys = length xs \<and> (\<forall>i<length xs. ys ! i \<in> xs ! i)"
  proof (induct xs arbitrary: ys)
    case Nil
    thus ?case by simp
  next
    case (Cons x xs)
    from Cons.prems obtain y ys' where "y \<in> x" and "ys' \<in> listset xs" and ys: "ys = y # ys'"
      by (rule listset_ConsE)
    from this(2) have "length ys' = length xs \<and> (\<forall>i<length xs. ys' ! i \<in> xs ! i)" by (rule Cons.hyps)
    hence 1: "length ys' = length xs" and 2: "\<And>i. i < length xs \<Longrightarrow> ys' ! i \<in> xs ! i" by simp_all
    show ?case
    proof (intro conjI allI impI)
      fix i
      assume "i < length (x # xs)"
      show "ys ! i \<in> (x # xs) ! i"
      proof (cases i)
        case 0
        with \<open>y \<in> x\<close> show ?thesis by (simp add: ys)
      next
        case (Suc j)
        with \<open>i < length (x # xs)\<close> have "j < length xs" by simp
        hence "ys' ! j \<in> xs ! j" by (rule 2)
        thus ?thesis by (simp add: ys \<open>i = Suc j\<close>)
      qed
    qed (simp add: ys 1)
  qed
  thus "length ys = length xs" and "\<And>i. i < length xs \<Longrightarrow> ys ! i \<in> xs ! i" by simp_all
qed

lemma listset_singletonI: "a \<in> A \<Longrightarrow> ys = [a] \<Longrightarrow> ys \<in> listset [A]"
  by simp

lemma listset_singletonE:
  assumes "ys \<in> listset [A]"
  obtains a where "a \<in> A" and "ys = [a]"
  using assms by auto

lemma listset_doubletonI: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> ys = [a, b] \<Longrightarrow> ys \<in> listset [A, B]"
  by (simp add: set_Cons_def)

lemma listset_doubletonE:
  assumes "ys \<in> listset [A, B]"
  obtains a b where "a \<in> A" and "b \<in> B" and "ys = [a, b]"
  using assms by (auto simp: set_Cons_def)

lemma listset_appendI:
  "ys1 \<in> listset xs1 \<Longrightarrow> ys2 \<in> listset xs2 \<Longrightarrow> ys = ys1 @ ys2 \<Longrightarrow> ys \<in> listset (xs1 @ xs2)"
  by (induct xs1 arbitrary: ys ys1 ys2)
      (simp, auto simp del: listset.simps elim!: listset_ConsE intro!: listset_ConsI)

lemma listset_appendE:
  assumes "ys \<in> listset (xs1 @ xs2)"
  obtains ys1 ys2 where "ys1 \<in> listset xs1" and "ys2 \<in> listset xs2" and "ys = ys1 @ ys2"
  using assms
proof (induct xs1 arbitrary: thesis ys)
  case Nil
  have "[] \<in> listset []" by simp
  moreover from Nil(2) have "ys \<in> listset xs2" by simp
  ultimately show ?case by (rule Nil) simp
next
  case (Cons x xs1)
  from Cons.prems(2) have "ys \<in> listset (x # (xs1 @ xs2))" by simp
  then obtain y ys' where "y \<in> x" and "ys' \<in> listset (xs1 @ xs2)" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  from _ this(2) obtain ys1 ys2 where ys1: "ys1 \<in> listset xs1" and "ys2 \<in> listset xs2"
    and ys': "ys' = ys1 @ ys2" by (rule Cons.hyps)
  show ?case
  proof (rule Cons.prems)
    from \<open>y \<in> x\<close> ys1 refl show "y # ys1 \<in> listset (x # xs1)" by (rule listset_ConsI)
  next
    show "ys = (y # ys1) @ ys2" by (simp add: ys ys')
  qed fact
qed

lemma listset_map_imageI: "ys' \<in> listset xs \<Longrightarrow> ys = map f ys' \<Longrightarrow> ys \<in> listset (map ((`) f) xs)"
  by (induct xs arbitrary: ys ys')
    (simp, auto simp del: listset.simps elim!: listset_ConsE intro!: listset_ConsI)

lemma listset_map_imageE:
  assumes "ys \<in> listset (map ((`) f) xs)"
  obtains ys' where "ys' \<in> listset xs" and "ys = map f ys'"
  using assms
proof (induct xs arbitrary: thesis ys)
  case Nil
  from Nil(2) have "ys = map f []" by simp
  with _ show ?case by (rule Nil) simp
next
  case (Cons x xs)
  from Cons.prems(2) have "ys \<in> listset (f ` x # map ((`) f) xs)" by simp
  then obtain y ys' where "y \<in> f ` x" and "ys' \<in> listset (map ((`) f) xs)" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  from _ this(2) obtain ys1 where ys1: "ys1 \<in> listset xs" and ys': "ys' = map f ys1" by (rule Cons.hyps)
  from \<open>y \<in> f ` x\<close> obtain y1 where "y1 \<in> x" and y: "y = f y1" ..
  show ?case
  proof (rule Cons.prems)
    from \<open>y1 \<in> x\<close> ys1 refl show "y1 # ys1 \<in> listset (x # xs)" by (rule listset_ConsI)
  qed (simp add: ys ys' y)
qed

lemma listset_permE:
  assumes "ys \<in> listset xs" and "bij_betw f {..<length xs} {..<length xs'}"
    and "\<And>i. i < length xs \<Longrightarrow> xs' ! i = xs ! f i"
  obtains ys' where "ys' \<in> listset xs'" and "length ys' = length ys"
    and "\<And>i. i < length ys \<Longrightarrow> ys' ! i = ys ! f i"
proof -
  from assms(1) have len_ys: "length ys = length xs" by (rule listsetD)
  from assms(2) have "card {..<length xs} = card {..<length xs'}" by (rule bij_betw_same_card)
  hence len_xs: "length xs = length xs'" by simp
  define ys' where "ys' = map (\<lambda>i. ys ! (f i)) [0..<length ys]"
  have 1: "ys' ! i = ys ! f i" if "i < length ys" for i using that by (simp add: ys'_def)
  show ?thesis
  proof
    show "ys' \<in> listset xs'"
    proof (rule listsetI)
      show "length ys' = length xs'" by (simp add: ys'_def len_ys len_xs)

      fix i
      assume "i < length xs'"
      hence "i < length xs" by (simp only: len_xs)
      hence "i < length ys" by (simp only: len_ys)
      hence "ys' ! i = ys ! (f i)" by (rule 1)
      also from assms(1) have "\<dots> \<in> xs ! (f i)"
      proof (rule listsetD)
        from \<open>i < length xs\<close> have "i \<in> {..<length xs}" by simp
        hence "f i \<in> f ` {..<length xs}" by (rule imageI)
        also from assms(2) have "\<dots> = {..<length xs'}" by (simp add: bij_betw_def)
        finally show "f i < length xs" by (simp add: len_xs)
      qed
      also have "\<dots> = xs' ! i" by (rule sym) (rule assms(3), fact)
      finally show "ys' ! i \<in> xs' ! i" .
    qed
  next
    show "length ys' = length ys" by (simp add: ys'_def)
  qed (rule 1)
qed

lemma listset_closed_map:
  assumes "ys \<in> listset xs" and "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> x \<Longrightarrow> f y \<in> x"
  shows "map f ys \<in> listset xs"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y ys' where "y \<in> x" and "ys' \<in> listset xs" and ys: "ys = y # ys'"
    by (rule listset_ConsE)
  show ?case
  proof (rule listset_ConsI)
    from _ \<open>y \<in> x\<close> show "f y \<in> x" by (rule Cons.prems) simp
  next
    show "map f ys' \<in> listset xs"
    proof (rule Cons.hyps)
      fix x0 y0
      assume "x0 \<in> set xs"
      hence "x0 \<in> set (x # xs)" by simp
      moreover assume "y0 \<in> x0"
      ultimately show "f y0 \<in> x0" by (rule Cons.prems)
    qed fact
  qed (simp add: ys)
qed

lemma listset_closed_map2:
  assumes "ys1 \<in> listset xs" and "ys2 \<in> listset xs"
    and "\<And>x y1 y2. x \<in> set xs \<Longrightarrow> y1 \<in> x \<Longrightarrow> y2 \<in> x \<Longrightarrow> f y1 y2 \<in> x"
  shows "map2 f ys1 ys2 \<in> listset xs"
  using assms
proof (induct xs arbitrary: ys1 ys2)
  case Nil
  from Nil(1) show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y1 ys1' where "y1 \<in> x" and "ys1' \<in> listset xs" and ys1: "ys1 = y1 # ys1'"
    by (rule listset_ConsE)
  from Cons.prems(2) obtain y2 ys2' where "y2 \<in> x" and "ys2' \<in> listset xs" and ys2: "ys2 = y2 # ys2'"
    by (rule listset_ConsE)
  show ?case
  proof (rule listset_ConsI)
    from _ \<open>y1 \<in> x\<close> \<open>y2 \<in> x\<close> show "f y1 y2 \<in> x" by (rule Cons.prems) simp
  next
    show "map2 f ys1' ys2' \<in> listset xs"
    proof (rule Cons.hyps)
      fix x' y1' y2'
      assume "x' \<in> set xs"
      hence "x' \<in> set (x # xs)" by simp
      moreover assume "y1' \<in> x'" and "y2' \<in> x'"
      ultimately show "f y1' y2' \<in> x'" by (rule Cons.prems)
    qed fact+
  qed (simp add: ys1 ys2)
qed

lemma listset_empty_iff: "listset xs = {} \<longleftrightarrow> {} \<in> set xs"
  by (induct xs) (auto simp: listset_Cons simp del: listset.simps(2))

lemma listset_mono:
  assumes "length xs = length ys" and "\<And>i. i < length ys \<Longrightarrow> xs ! i \<subseteq> ys ! i"
  shows "listset xs \<subseteq> listset ys"
  using assms
proof (induct xs ys rule: list_induct2)
  case Nil
  show ?case by simp
next
  case (Cons x xs y ys)
  show ?case
  proof
    fix zs'
    assume "zs' \<in> listset (x # xs)"
    then obtain z zs where "z \<in> x" and zs: "zs \<in> listset xs" and zs': "zs' = z # zs"
      by (rule listset_ConsE)
    have "0 < length (y # ys)" by simp
    hence "(x # xs) ! 0 \<subseteq> (y # ys) ! 0" by (rule Cons.prems)
    hence "x \<subseteq> y" by simp
    with \<open>z \<in> x\<close> have "z \<in> y" ..
    moreover from zs have "zs \<in> listset ys"
    proof
      show "listset xs \<subseteq> listset ys"
      proof (rule Cons.hyps)
        fix i
        assume "i < length ys"
        hence "Suc i < length (y # ys)" by simp
        hence "(x # xs) ! Suc i \<subseteq> (y # ys) ! Suc i" by (rule Cons.prems)
        thus "xs ! i \<subseteq> ys ! i" by simp
      qed
    qed
    ultimately show "zs' \<in> listset (y # ys)" using zs' by (rule listset_ConsI)
  qed
qed

end (* theory *)
