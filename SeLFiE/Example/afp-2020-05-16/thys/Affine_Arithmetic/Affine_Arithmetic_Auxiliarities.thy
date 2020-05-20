theory Affine_Arithmetic_Auxiliarities
imports "HOL-Analysis.Multivariate_Analysis"
begin

subsection \<open>@{term sum_list}\<close>

lemma sum_list_nth_eqI:
  fixes xs ys::"'a::monoid_add list"
  shows
    "length xs = length ys \<Longrightarrow> (\<And>x y. (x, y) \<in> set (zip xs ys) \<Longrightarrow> x = y) \<Longrightarrow>
      sum_list xs = sum_list ys"
  by (induct xs ys rule: list_induct2) auto

lemma fst_sum_list: "fst (sum_list xs) = sum_list (map fst xs)"
  by (induct xs) auto

lemma snd_sum_list: "snd (sum_list xs) = sum_list (map snd xs)"
  by (induct xs) auto

lemma take_greater_eqI: "take c xs = take c ys \<Longrightarrow> c \<ge> a \<Longrightarrow> take a xs = take a ys"
proof (induct xs arbitrary: a c ys)
  case (Cons x xs) note ICons = Cons
  thus ?case
  proof (cases a)
    case (Suc b)
    thus ?thesis using Cons(2,3)
    proof (cases ys)
      case (Cons z zs)
      from ICons obtain d where c: "c = Suc d"
        by (auto simp: Cons Suc dest!: Suc_le_D)
      show ?thesis
        using ICons(2,3)
        by (auto simp: Suc Cons c intro: ICons(1))
    qed simp
  qed simp
qed (metis le_0_eq take_eq_Nil)

lemma take_max_eqD:
  "take (max a b) xs = take (max a b) ys \<Longrightarrow> take a xs = take a ys \<and> take b xs = take b ys"
  by (metis max.cobounded1 max.cobounded2 take_greater_eqI)

lemma take_Suc_eq: "take (Suc n) xs = (if n < length xs then take n xs @ [xs ! n] else xs)"
  by (auto simp: take_Suc_conv_app_nth)


subsection \<open>Radiant and Degree\<close>

definition "rad_of w = w * pi / 180"

definition "deg_of w = 180 * w / pi"

lemma rad_of_inverse[simp]: "deg_of (rad_of w) = w"
  and deg_of_inverse[simp]: "rad_of (deg_of w) = w"
  by (auto simp: deg_of_def rad_of_def)

lemma deg_of_monoI: "x \<le> y \<Longrightarrow> deg_of x \<le> deg_of y"
  by (auto simp: deg_of_def intro!: divide_right_mono)

lemma rad_of_monoI: "x \<le> y \<Longrightarrow> rad_of x \<le> rad_of y"
  by (auto simp: rad_of_def)

lemma deg_of_strict_monoI: "x < y \<Longrightarrow> deg_of x < deg_of y"
  by (auto simp: deg_of_def intro!: divide_strict_right_mono)

lemma rad_of_strict_monoI: "x < y \<Longrightarrow> rad_of x < rad_of y"
  by (auto simp: rad_of_def)

lemma deg_of_mono[simp]: "deg_of x \<le> deg_of y \<longleftrightarrow> x \<le> y"
  using rad_of_monoI
  by (fastforce intro!: deg_of_monoI)

lemma rad_of_mono[simp]: "rad_of x \<le> rad_of y \<longleftrightarrow> x \<le> y"
  using rad_of_monoI
  by (fastforce intro!: deg_of_monoI)

lemma deg_of_strict_mono[simp]: "deg_of x < deg_of y \<longleftrightarrow> x < y"
  using rad_of_strict_monoI
  by (fastforce intro!: deg_of_strict_monoI)

lemma rad_of_strict_mono[simp]: "rad_of x < rad_of y \<longleftrightarrow> x < y"
  using rad_of_strict_monoI
  by (fastforce intro!: deg_of_strict_monoI)

lemma rad_of_lt_iff: "rad_of d < r \<longleftrightarrow> d < deg_of r"
  and rad_of_gt_iff: "rad_of d > r \<longleftrightarrow> d > deg_of r"
  and rad_of_le_iff: "rad_of d \<le> r \<longleftrightarrow> d \<le> deg_of r"
  and rad_of_ge_iff: "rad_of d \<ge> r \<longleftrightarrow> d \<ge> deg_of r"
  using rad_of_strict_mono[of d "deg_of r"] rad_of_mono[of d "deg_of r"]
  by auto

end
