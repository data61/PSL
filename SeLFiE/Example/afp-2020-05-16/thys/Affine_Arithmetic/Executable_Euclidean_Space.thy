section \<open>Euclidean Space: Executability\<close>
theory Executable_Euclidean_Space
imports
  "HOL-Analysis.Multivariate_Analysis"
  "List-Index.List_Index"
  "HOL-Library.Float"
  Affine_Arithmetic_Auxiliarities
begin

subsection \<open>Ordered representation of Basis and Rounding of Components\<close>

class executable_euclidean_space = ordered_euclidean_space +
  fixes Basis_list eucl_down eucl_truncate_down eucl_truncate_up
  assumes eucl_down_def:
    "eucl_down p b = (\<Sum>i \<in> Basis. round_down p (b \<bullet> i) *\<^sub>R i)"
  assumes eucl_truncate_down_def:
    "eucl_truncate_down q b = (\<Sum>i \<in> Basis. truncate_down q (b \<bullet> i) *\<^sub>R i)"
  assumes eucl_truncate_up_def:
    "eucl_truncate_up q b = (\<Sum>i \<in> Basis. truncate_up q (b \<bullet> i) *\<^sub>R i)"
  assumes Basis_list[simp]: "set Basis_list = Basis"
  assumes distinct_Basis_list[simp]: "distinct Basis_list"
begin

lemma length_Basis_list:
  "length Basis_list = card Basis"
  by (metis Basis_list distinct_Basis_list distinct_card)

end

lemma eucl_truncate_down_zero[simp]: "eucl_truncate_down p 0 = 0"
  by (auto simp: eucl_truncate_down_def truncate_down_zero)

lemma eucl_truncate_up_zero[simp]: "eucl_truncate_up p 0 = 0"
  by (auto simp: eucl_truncate_up_def)

subsection \<open>Instantiations\<close>

instantiation real::executable_euclidean_space
begin

definition Basis_list_real :: "real list" where
  "Basis_list_real = [1]"

definition "eucl_down prec b = round_down prec b"
definition "eucl_truncate_down prec b = truncate_down prec b"
definition "eucl_truncate_up prec b = truncate_up prec b"

instance proof qed (auto simp: Basis_list_real_def eucl_down_real_def eucl_truncate_down_real_def
  eucl_truncate_up_real_def)

end

instantiation prod::(executable_euclidean_space, executable_euclidean_space)
  executable_euclidean_space
begin

definition Basis_list_prod :: "('a \<times> 'b) list" where
  "Basis_list_prod =
    zip Basis_list (replicate (length (Basis_list::'a list)) 0) @
    zip (replicate (length (Basis_list::'b list)) 0) Basis_list"

definition "eucl_down p a = (eucl_down p (fst a), eucl_down p (snd a))"
definition "eucl_truncate_down p a = (eucl_truncate_down p (fst a), eucl_truncate_down p (snd a))"
definition "eucl_truncate_up p a = (eucl_truncate_up p (fst a), eucl_truncate_up p (snd a))"

instance
proof
  show "set Basis_list = (Basis::('a*'b) set)"
    by (auto simp: Basis_list_prod_def Basis_prod_def elim!: in_set_zipE)
      (auto simp: Basis_list[symmetric] in_set_zip in_set_conv_nth simp del: Basis_list)
  show "distinct (Basis_list::('a*'b)list)"
    using distinct_Basis_list[where 'a='a] distinct_Basis_list[where 'a='b]
    by (auto simp: Basis_list_prod_def Basis_list intro: distinct_zipI1 distinct_zipI2
      elim!: in_set_zipE)
qed
  (auto simp: eucl_down_prod_def eucl_truncate_down_prod_def eucl_truncate_up_prod_def
    sum_Basis_prod_eq inner_add_left inner_sum_left inner_Basis eucl_down_def
    eucl_truncate_down_def eucl_truncate_up_def
    intro!: euclidean_eqI[where 'a="'a*'b"])

end

lemma eucl_truncate_down_Basis[simp]:
  "i \<in> Basis \<Longrightarrow> eucl_truncate_down e x \<bullet> i = truncate_down e (x \<bullet> i)"
  by (simp add: eucl_truncate_down_def)

lemma eucl_truncate_down_correct:
  "dist (x::'a::executable_euclidean_space) (eucl_down e x) \<in>
    {0..sqrt (DIM('a)) * 2 powr of_int (- e)}"
proof -
  have "dist x (eucl_down e x) = sqrt (\<Sum>i\<in>Basis. (dist (x \<bullet> i) (eucl_down e x \<bullet> i))\<^sup>2)"
    unfolding euclidean_dist_l2[where 'a='a] L2_set_def ..
  also have "\<dots> \<le> sqrt (\<Sum>i\<in>(Basis::'a set). ((2 powr of_int (- e))\<^sup>2))"
    by (intro real_sqrt_le_mono sum_mono power_mono)
      (auto simp: dist_real_def eucl_down_def abs_round_down_le)
  finally show ?thesis
    by (simp add: real_sqrt_mult)
qed

lemma eucl_down: "eucl_down e (x::'a::executable_euclidean_space) \<le> x"
  by (auto simp add: eucl_le[where 'a='a] round_down eucl_down_def)

lemma eucl_truncate_down: "eucl_truncate_down e (x::'a::executable_euclidean_space) \<le> x"
  by (auto simp add: eucl_le[where 'a='a] truncate_down)

lemma eucl_truncate_down_le:
  "x \<le> y \<Longrightarrow> eucl_truncate_down w x \<le> (y::'a::executable_euclidean_space)"
  using eucl_truncate_down
  by (rule order.trans)

lemma eucl_truncate_up_Basis[simp]: "i \<in> Basis \<Longrightarrow> eucl_truncate_up e x \<bullet> i = truncate_up e (x \<bullet> i)"
  by (simp add: eucl_truncate_up_def truncate_up_def)

lemma eucl_truncate_up: "x \<le> eucl_truncate_up e (x::'a::executable_euclidean_space)"
  by (auto simp add: eucl_le[where 'a='a] round_up truncate_up_def)

lemma eucl_truncate_up_le: "x \<le> y \<Longrightarrow> x \<le> eucl_truncate_up e (y::'a::executable_euclidean_space)"
  using _ eucl_truncate_up
  by (rule order.trans)

lemma eucl_truncate_down_mono:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<le> y \<Longrightarrow> eucl_truncate_down p x \<le> eucl_truncate_down p y"
  by (auto simp: eucl_le[where 'a='a] intro!: truncate_down_mono)

lemma eucl_truncate_up_mono:
  fixes x::"'a::executable_euclidean_space"
  shows "x \<le> y \<Longrightarrow> eucl_truncate_up p x \<le> eucl_truncate_up p y"
  by (auto simp: eucl_le[where 'a='a] intro!: truncate_up_mono)

lemma infnorm[code]:
  fixes x::"'a::executable_euclidean_space"
  shows "infnorm x = fold max (map (\<lambda>i. abs (x \<bullet> i)) Basis_list) 0"
  by (auto simp: Max.set_eq_fold[symmetric] infnorm_Max[symmetric] infnorm_pos_le
    intro!: max.absorb2[symmetric])

declare Inf_real_def[code del]
declare Sup_real_def[code del]
declare Inf_prod_def[code del]
declare Sup_prod_def[code del]
declare [[code abort: "Inf::real set \<Rightarrow> real"]]
declare [[code abort: "Sup::real set \<Rightarrow> real"]]
declare [[code abort: "Inf::('a::Inf * 'b::Inf) set \<Rightarrow> 'a * 'b"]]
declare [[code abort: "Sup::('a::Sup * 'b::Sup) set \<Rightarrow> 'a * 'b"]]

lemma nth_Basis_list_in_Basis[simp]:
  "n < length (Basis_list::'a::executable_euclidean_space list) \<Longrightarrow> Basis_list ! n \<in> (Basis::'a set)"
  by (metis Basis_list nth_mem)

subsection \<open>Representation as list\<close>

lemma nth_eq_iff_index:
  "distinct xs \<Longrightarrow> n < length xs \<Longrightarrow> xs ! n = i \<longleftrightarrow> n = index xs i"
  using index_nth_id by fastforce

lemma in_Basis_index_Basis_list: "i \<in> Basis \<Longrightarrow> i = Basis_list ! index Basis_list i"
  by simp

lemmas [simp] = length_Basis_list

lemma sum_Basis_sum_nth_Basis_list:
  "(\<Sum>i\<in>Basis. f i) = (\<Sum>i<DIM('a::executable_euclidean_space). f ((Basis_list::'a list) ! i))"
  apply (rule sum.reindex_cong[OF _ _ refl])
   apply (auto intro!: inj_on_nth)
  by (metis Basis_list image_iff in_Basis_index_Basis_list index_less_size_conv length_Basis_list lessThan_iff)

definition "eucl_of_list xs = (\<Sum>(x, i)\<leftarrow>zip xs Basis_list. x *\<^sub>R i)"

lemma eucl_of_list_nth:
  assumes "length xs = DIM('a)"
  shows "eucl_of_list xs = (\<Sum>i<DIM('a::executable_euclidean_space). (xs ! i) *\<^sub>R ((Basis_list::'a list) ! i))"
  by (auto simp: eucl_of_list_def sum_list_sum_nth length_Basis_list assms atLeast0LessThan)

lemma eucl_of_list_inner:
  fixes i::"'a::executable_euclidean_space"
  assumes i: "i \<in> Basis"
  assumes l: "length xs = DIM('a)"
  shows "eucl_of_list xs \<bullet> i = xs ! (index Basis_list i)"
  by (simp add: eucl_of_list_nth[OF l] inner_sum_left assms inner_Basis
      nth_eq_iff_index sum.delta if_distrib cong: if_cong)

lemma inner_eucl_of_list:
  fixes i::"'a::executable_euclidean_space"
  assumes i: "i \<in> Basis"
  assumes l: "length xs = DIM('a)"
  shows "i \<bullet> eucl_of_list xs = xs ! (index Basis_list i)"
  using eucl_of_list_inner[OF assms] by (auto simp: inner_commute)


definition "list_of_eucl x = map ((\<bullet>) x) Basis_list"

lemma index_Basis_list_nth[simp]:
  "i < DIM('a::executable_euclidean_space) \<Longrightarrow> index Basis_list ((Basis_list::'a list) ! i) = i"
  by (simp add: index_nth_id)

lemma list_of_eucl_eucl_of_list[simp]:
  "length xs = DIM('a::executable_euclidean_space) \<Longrightarrow> list_of_eucl (eucl_of_list xs::'a) = xs"
  by (auto simp: list_of_eucl_def eucl_of_list_inner intro!: nth_equalityI)

lemma eucl_of_list_list_of_eucl[simp]:
  "eucl_of_list (list_of_eucl x) = x"
  by (auto simp: list_of_eucl_def eucl_of_list_inner intro!: euclidean_eqI[where 'a='a])


lemma length_list_of_eucl[simp]: "length (list_of_eucl (x::'a::executable_euclidean_space)) = DIM('a)"
  by (auto simp: list_of_eucl_def)

lemma list_of_eucl_nth[simp]: "n < DIM('a::executable_euclidean_space) \<Longrightarrow> list_of_eucl x ! n = x \<bullet> (Basis_list ! n::'a)"
  by (auto simp: list_of_eucl_def)

lemma nth_ge_len: "n \<ge> length xs \<Longrightarrow> xs ! n = [] ! (n - length xs)"
  by (induction xs arbitrary: n) auto

lemma list_of_eucl_nth_if: "list_of_eucl x ! n = (if n < DIM('a::executable_euclidean_space) then x \<bullet> (Basis_list ! n::'a) else [] ! (n - DIM('a)))"
  apply (auto simp: list_of_eucl_def )
  apply (subst nth_ge_len)
   apply auto
  done

lemma list_of_eucl_eq_iff:
  "list_of_eucl (x::'a::executable_euclidean_space) = list_of_eucl (y::'b::executable_euclidean_space) \<longleftrightarrow>
  (DIM('a) = DIM('b) \<and> (\<forall>i < DIM('b). x \<bullet> Basis_list ! i = y \<bullet> Basis_list ! i))"
  by (auto simp: list_eq_iff_nth_eq)

lemma eucl_le_Basis_list_iff:
  "(x::'a::executable_euclidean_space) \<le> y \<longleftrightarrow>
  (\<forall>i<DIM('a). x \<bullet> Basis_list ! i \<le> y \<bullet> Basis_list ! i)"
  apply (auto simp:  eucl_le[where 'a='a])
  subgoal for i
    subgoal by (auto dest!: spec[where x="index Basis_list i"])
    done
  done

lemma eucl_of_list_inj: "length xs = DIM('a::executable_euclidean_space) \<Longrightarrow> length ys = DIM('a) \<Longrightarrow>
  (eucl_of_list xs::'a) = eucl_of_list (ys) \<Longrightarrow> xs = ys"
  apply (auto intro!: nth_equalityI simp: euclidean_eq_iff[where 'a="'a"] eucl_of_list_inner)
  using nth_Basis_list_in_Basis[where 'a="'a"]
  by fastforce

lemma eucl_of_list_map_plus[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. f x + g x) xs)::'a) =
    eucl_of_list (map f xs) + eucl_of_list (map g xs)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma eucl_of_list_map_uminus[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. - f x) xs)::'a) = - eucl_of_list (map f xs)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma eucl_of_list_map_mult_left[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. r * f x) xs)::'a) = r *\<^sub>R eucl_of_list (map f xs)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma eucl_of_list_map_mult_right[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. f x * r) xs)::'a) = r *\<^sub>R eucl_of_list (map f xs)"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma eucl_of_list_map_divide_right[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. f x / r) xs)::'a) = eucl_of_list (map f xs) /\<^sub>R r"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner divide_simps)

lemma eucl_of_list_map_const[simp]:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)"
  shows "(eucl_of_list (map (\<lambda>x. c) xs)::'a) = c *\<^sub>R One"
  by (auto intro!: euclidean_eqI[where 'a='a] simp: algebra_simps eucl_of_list_inner)

lemma replicate_eq_list_of_eucl_zero: "replicate DIM('a::executable_euclidean_space) 0 = list_of_eucl (0::'a)"
  by (auto intro!: nth_equalityI)

lemma eucl_of_list_append_zeroes[simp]: "eucl_of_list (xs @ replicate n 0) = eucl_of_list xs"
  unfolding eucl_of_list_def
  apply (auto simp: sum_list_sum_nth)
  apply (rule sum.mono_neutral_cong_right)
  by (auto simp: nth_append)

lemma Basis_prodD:
  assumes "(i, j) \<in> Basis"
  shows "i \<in> Basis \<and> j = 0 \<or> i = 0 \<and> j \<in> Basis"
  using assms
  by (auto simp: Basis_prod_def)

lemma eucl_of_list_take_DIM[simp]:
  assumes "d = DIM('b::executable_euclidean_space)"
  shows "(eucl_of_list (take d xs)::'b) = (eucl_of_list xs)"
  by (auto simp: eucl_of_list_inner eucl_of_list_def fst_sum_list sum_list_sum_nth assms dest!: Basis_prodD)

lemma eucl_of_list_eqI:
  assumes "take DIM('a) (xs @ replicate (DIM('a) - length xs) 0) =
    take DIM('a) (ys @ replicate (DIM('a) - length ys) 0)"
  shows "eucl_of_list xs = (eucl_of_list ys::'a::executable_euclidean_space)"
proof -
  have "(eucl_of_list xs::'a) = eucl_of_list (take DIM('a) (xs @ replicate (DIM('a) - length xs) 0))"
    by (simp add: )
  also note assms
  also have "eucl_of_list (take DIM('a) (ys @ replicate (DIM('a) - length ys) 0)) = (eucl_of_list ys::'a)"
    by simp
  finally show ?thesis .
qed

lemma eucl_of_list_replicate_zero[simp]: "eucl_of_list (replicate E 0) = 0"
proof -
  have "eucl_of_list (replicate E 0) = (eucl_of_list (replicate E 0 @ replicate (DIM('a) - E) 0)::'a)"
    by simp
  also have "\<dots> = eucl_of_list (replicate DIM('a) 0)"
    apply (rule eucl_of_list_eqI)
    by (auto simp: min_def nth_append intro!: nth_equalityI)
  also have "\<dots> = 0"
    by (simp add: replicate_eq_list_of_eucl_zero)
  finally show ?thesis by simp
qed

lemma eucl_of_list_Nil[simp]: "eucl_of_list [] = 0"
  using eucl_of_list_replicate_zero[of 0] by simp


lemma fst_eucl_of_list_prod:
  shows "fst (eucl_of_list xs::'b::executable_euclidean_space  \<times> _) = (eucl_of_list (take DIM('b) xs)::'b)"
  apply (auto simp: eucl_of_list_inner eucl_of_list_def fst_sum_list dest!: Basis_prodD)
  apply (simp add: sum_list_sum_nth)
  apply (rule sum.mono_neutral_cong_right)
  subgoal by simp
  subgoal by auto
  subgoal by (auto simp: Basis_list_prod_def nth_append)
  subgoal by (auto simp: Basis_list_prod_def nth_append)
  done

lemma index_zip_replicate1[simp]: "index (zip (replicate d a) bs) (a, b) = index bs b"
  if "d = length bs"
  using that
  by (induction bs arbitrary: d) auto

lemma index_zip_replicate2[simp]: "index (zip as (replicate d b)) (a, b) = index as a"
  if "d = length as"
  using that
  by (induction as arbitrary: d) auto

lemma index_Basis_list_prod[simp]:
  fixes a::"'a::executable_euclidean_space" and b::"'b::executable_euclidean_space"
  shows "a \<in> Basis \<Longrightarrow> index Basis_list (a, 0::'b) = index Basis_list a"
    "b \<in> Basis \<Longrightarrow> index Basis_list (0::'a, b) = DIM('a) + index Basis_list b"
  by (auto simp: Basis_list_prod_def index_append
      in_set_zip zip_replicate index_map_inj dest: spec[where x="index Basis_list a"])

lemma eucl_of_list_eq_takeI:
  assumes "(eucl_of_list (take DIM('a::executable_euclidean_space) xs)::'a) = x"
  shows "eucl_of_list xs = x"
  using eucl_of_list_take_DIM[OF refl, of xs, where 'b='a] assms
  by auto

lemma eucl_of_list_inner_le:
  fixes i::"'a::executable_euclidean_space"
  assumes i: "i \<in> Basis"
  assumes l: "length xs \<ge> DIM('a)"
  shows "eucl_of_list xs \<bullet> i = xs ! (index Basis_list i)"
proof -
  have "(eucl_of_list xs::'a) = eucl_of_list (take DIM('a) (xs @ (replicate (DIM('a) - length xs) 0)))"
    by (rule eucl_of_list_eq_takeI) simp
  also have "\<dots> \<bullet> i = xs ! (index Basis_list i)"
    using assms
    by (subst eucl_of_list_inner) auto
  finally show ?thesis .
qed

lemma eucl_of_list_prod_if:
  assumes "length xs = DIM('a::executable_euclidean_space) + DIM('b::executable_euclidean_space)"
  shows "eucl_of_list xs =
    (eucl_of_list (take DIM('a) xs)::'a, eucl_of_list (drop DIM('a) xs)::'b)"
  apply (rule euclidean_eqI)
  using assms
  apply (auto simp: eucl_of_list_inner dest!: Basis_prodD)
   apply (subst eucl_of_list_inner_le)
  apply (auto simp: Basis_list_prod_def index_append in_set_zip)
  done


lemma snd_eucl_of_list_prod:
  shows "snd (eucl_of_list xs::'b::executable_euclidean_space  \<times> 'c::executable_euclidean_space) =
    (eucl_of_list (drop DIM('b) xs)::'c)"
proof (cases "length xs \<le> DIM('b)")
  case True
  then show ?thesis
    by (auto simp: eucl_of_list_inner eucl_of_list_def snd_sum_list dest!: Basis_prodD)
      (simp add: sum_list_sum_nth Basis_list_prod_def nth_append)
next
  case False
  have "xs = take DIM('b) xs @ drop DIM('b) xs" by simp
  also have "eucl_of_list \<dots> = (eucl_of_list (\<dots> @ replicate (length xs - DIM('c)) 0)::'b \<times> 'c)"
    by simp
  finally have "eucl_of_list xs = (eucl_of_list (xs @ replicate (DIM('b) + DIM('c) - length xs) 0)::'b \<times> 'c)"
    by simp
  also have "\<dots> = eucl_of_list (take (DIM ('b \<times> 'c)) (xs @ replicate (DIM('b) + DIM('c) - length xs) 0))"
    by (simp add: )
  finally have *: "(eucl_of_list xs::'b\<times>'c) = eucl_of_list (take DIM('b \<times> 'c) (xs @ replicate (DIM('b) + DIM('c) - length xs) 0))"
    by simp
  show ?thesis
    apply (subst *)
    apply (subst eucl_of_list_prod_if)
    subgoal by simp
    subgoal
      apply simp
      apply (subst (2) eucl_of_list_take_DIM[OF refl, symmetric])
      apply (subst (2) eucl_of_list_take_DIM[OF refl, symmetric])
      apply (rule arg_cong[where f=eucl_of_list])
      by (auto intro!: nth_equalityI simp: nth_append min_def split: if_splits)
    done
qed

lemma eucl_of_list_prod:
  shows "eucl_of_list xs = (eucl_of_list (take DIM('b) xs)::'b::executable_euclidean_space,
    eucl_of_list (drop DIM('b) xs)::'c::executable_euclidean_space)"
  using snd_eucl_of_list_prod[of xs, where 'b='b and 'c='c]
  using fst_eucl_of_list_prod[of xs, where 'b='b and 'a='c]
  by (auto simp del: snd_eucl_of_list_prod fst_eucl_of_list_prod simp add: prod_eq_iff)

lemma eucl_of_list_real[simp]: "eucl_of_list [x] = (x::real)"
  by (auto simp: eucl_of_list_def Basis_list_real_def)

lemma eucl_of_list_append[simp]:
  assumes "length xs = DIM('i::executable_euclidean_space)"
  assumes "length ys = DIM('j::executable_euclidean_space)"
  shows "eucl_of_list (xs @ ys) = (eucl_of_list xs::'i, eucl_of_list ys::'j)"
  using assms
  by (auto simp: eucl_of_list_prod)

lemma list_allI: "(\<And>x. x \<in> set xs \<Longrightarrow> P x) \<Longrightarrow> list_all P xs"
  by (auto simp: list_all_iff)

lemma
  concat_map_nthI:
  assumes "\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set (f x) \<Longrightarrow> P y"
  assumes "j < length (concat (map f xs))"
  shows "P (concat (map f xs) ! j)"
proof -
  have "list_all P (concat (map f xs))"
    by (rule list_allI) (auto simp: assms)
  then show ?thesis
    by (auto simp: list_all_length assms)
qed

lemma map_nth_append1:
  assumes "length xs = d"
  shows "map ((!) (xs @ ys)) [0..<d] = xs"
  using assms
  by (auto simp: nth_append intro!: nth_equalityI)

lemma map_nth_append2:
  assumes "length ys = d"
  shows "map ((!) (xs @ ys)) [length xs..<length xs + d] = ys"
  using assms
  by (auto simp: intro!: nth_equalityI)

lemma length_map2 [simp]: "length (map2 f xs ys) = min (length xs) (length ys)"
  by simp

lemma map2_nth [simp]: "map2 f xs ys ! n = f (xs ! n) (ys ! n)"
  if "n < length xs" "n < length ys"
  using that by simp

lemma list_of_eucl_add: "list_of_eucl (x + y) = map2 (+) (list_of_eucl x) (list_of_eucl y)"
  by (auto intro!: nth_equalityI simp: inner_simps)

lemma list_of_eucl_inj:
  "list_of_eucl z = list_of_eucl y \<Longrightarrow> y = z"
  by (metis eucl_of_list_list_of_eucl)

lemma length_Basis_list_pos[simp]: "length Basis_list > 0"
  by (metis length_pos_if_in_set Basis_list SOME_Basis)

lemma Basis_list_nth_nonzero:
  "i < length (Basis_list::'a::executable_euclidean_space list) \<Longrightarrow> (Basis_list::'a list) ! i \<noteq> 0"
  by (auto dest!: nth_mem simp: nonzero_Basis)

lemma nth_Basis_list_prod:
  "i < DIM('a) + DIM('b) \<Longrightarrow> (Basis_list::('a::executable_euclidean_space \<times> 'b::executable_euclidean_space) list) ! i =
    (if i < DIM('a) then (Basis_list ! i, 0) else (0, Basis_list ! (i - DIM('a))))"
  by (auto simp: Basis_list_nth_nonzero prod_eq_iff Basis_list_prod_def nth_append not_less)

lemma eucl_of_list_if:
  assumes [simp]: "length xs = DIM('a::executable_euclidean_space)" "distinct xs"
  shows "eucl_of_list (map (\<lambda>xa. if xa = x then 1 else 0) (xs::nat list)) =
    (if x \<in> set xs then Basis_list ! index xs x else 0::'a)"
  by (rule euclidean_eqI) (auto simp: eucl_of_list_inner inner_Basis index_nth_id)


lemma take_append_take_minus_idem: "take n XS @ map ((!) XS) [n..<length XS] = XS"
  by (auto intro!: nth_equalityI simp: nth_append min_def)

lemma sum_list_Basis_list[simp]: "sum_list (map f Basis_list) = (\<Sum>b\<in>Basis. f b)"
  by (subst sum_list_distinct_conv_sum_set) (auto simp: Basis_list distinct_Basis_list)

lemma hd_Basis_list[simp]: "hd Basis_list \<in> Basis"
  unfolding Basis_list[symmetric]
  by (rule hd_in_set) (auto simp: set_empty[symmetric])

definition "inner_lv_rel a b = sum_list (map2 (*) a b)"

lemma eucl_of_list_inner_eq: "(eucl_of_list xs::'a) \<bullet> eucl_of_list ys = inner_lv_rel xs ys"
  if "length xs = DIM('a::executable_euclidean_space)" "length ys = DIM('a)"
  using that
  by (subst euclidean_inner[abs_def], subst sum_list_Basis_list[symmetric])
      (auto simp: eucl_of_list_inner sum_list_sum_nth index_nth_id inner_lv_rel_def)


lemma euclidean_vec_componentwise:
  "(\<Sum>(xa::'a::euclidean_space^'b::finite)\<in>Basis. f xa) = (\<Sum>a\<in>Basis. (\<Sum>b::'b\<in>UNIV. f (axis b a)))"
  apply (auto simp: Basis_vec_def)
  apply (subst sum.swap)
  apply (subst sum.Union_disjoint)
    apply auto
      apply (simp add: axis_eq_axis nonzero_Basis)
   apply (simp add: axis_eq_axis nonzero_Basis)
  apply (subst sum.reindex)
   apply (auto intro!: injI)
  subgoal
    apply (auto simp: set_eq_iff)
    by (metis (full_types) all_not_in_conv inner_axis_axis inner_eq_zero_iff nonempty_Basis nonzero_Basis)
  apply (rule sum.cong[OF refl])
  apply (auto )
  apply (rule sum.reindex_cong[OF _ _ refl])
  apply (auto intro!: inj_onI)
  using axis_eq_axis by blast

lemma vec_nth_inner_scaleR_craziness:
  "f (x $ i \<bullet> j) *\<^sub>R j = (\<Sum>xa\<in>UNIV. f (x $ xa \<bullet> j) *\<^sub>R axis xa j) $ i"
  by vector (auto simp: axis_def if_distrib scaleR_vec_def sum.delta' cong: if_cong)

instantiation vec :: ("{executable_euclidean_space}", enum) executable_euclidean_space
begin

definition Basis_list_vec :: "('a, 'b) vec list" where
  "Basis_list_vec = concat (map (\<lambda>n. map (axis n) Basis_list) enum_class.enum)"

definition eucl_down_vec :: "int \<Rightarrow> ('a, 'b) vec \<Rightarrow> ('a, 'b) vec" where
  "eucl_down_vec p x = (\<chi> i. eucl_down p (x $ i))"

definition eucl_truncate_down_vec :: "nat \<Rightarrow> ('a, 'b) vec \<Rightarrow> ('a, 'b) vec" where
  "eucl_truncate_down_vec p x = (\<chi> i. eucl_truncate_down p (x $ i))"

definition eucl_truncate_up_vec :: "nat \<Rightarrow> ('a, 'b) vec \<Rightarrow> ('a, 'b) vec" where
  "eucl_truncate_up_vec p x = (\<chi> i. eucl_truncate_up p (x $ i))"

instance
proof
  show *: "set (Basis_list::('a, 'b) vec list) = Basis"
    unfolding Basis_list_vec_def Basis_vec_def
    apply (auto simp: Basis_list_vec_def vec_eq_iff distinct_map Basis_vec_def
        intro!: distinct_concat inj_onI split: if_splits)
    apply (auto simp: Basis_list_vec_def vec_eq_iff distinct_map enum_distinct
        UNIV_enum[symmetric]
        intro!: distinct_concat inj_onI split: if_splits)
    done
  have "length (Basis_list::('a, 'b) vec list) = CARD('b) * DIM('a)"
    by (auto simp: Basis_list_vec_def length_concat o_def enum_distinct
        sum_list_distinct_conv_sum_set UNIV_enum[symmetric])
  then show "distinct (Basis_list::('a, 'b) vec list)"
    using * by (auto intro!: card_distinct)
qed (simp_all only: vector_cart[symmetric] vec_eq_iff
    eucl_down_vec_def eucl_down_def
    eucl_truncate_down_vec_def eucl_truncate_down_def
    eucl_truncate_up_vec_def eucl_truncate_up_def,
    auto simp: euclidean_vec_componentwise inner_axis Basis_list_vec_def
    vec_nth_inner_scaleR_craziness
    intro!: sum.cong[OF refl])
end


lemma concat_same_lengths_nth:
  assumes "\<And>xs. xs \<in> set XS \<Longrightarrow> length xs = N"
  assumes "i < length XS * N" "N > 0"
  shows "concat XS ! i = XS ! (i div N) ! (i mod N)"
  using assms
  apply (induction XS arbitrary: i)
   apply (auto simp: nth_append nth_Cons split: nat.splits)
   apply (simp add: div_eq_0_iff)
  by (metis Suc_inject div_geq mod_geq)

lemma concat_map_map_index:
  shows "concat (map (\<lambda>n. map (f n) xs) ys) =
    map (\<lambda>i. f (ys ! (i div length xs)) (xs ! (i mod length xs))) [0..<length xs * length ys]"
  apply (auto intro!: nth_equalityI simp: length_concat o_def sum_list_sum_nth)
  apply (subst concat_same_lengths_nth)
     apply (auto simp: )
  apply (subst nth_map_upt)
  apply (auto simp: ac_simps)
  apply (subst nth_map)
  apply (metis div_eq_0_iff div_mult2_eq mult.commute mult_0 not_less0)
  apply (subst nth_map)
  subgoal for i
    using gr_implies_not_zero by fastforce
  subgoal by simp
  done

lemma
  sum_list_zip_map:
  assumes "distinct xs"
  shows "(\<Sum>(x, y)\<leftarrow>zip xs (map g xs). f x y) = (\<Sum>x\<in>set xs. f x (g x))"
  by (force simp add: sum_list_distinct_conv_sum_set assms distinct_zipI1 split_beta'
    in_set_zip in_set_conv_nth inj_on_convol_ident
    intro!: sum.reindex_cong[where l="\<lambda>x. (x, g x)"])

lemma
  sum_list_zip_map_of:
  assumes "distinct bs"
  assumes "length xs = length bs"
  shows "(\<Sum>(x, y)\<leftarrow>zip xs bs. f x y) = (\<Sum>x\<in>set bs. f (the (map_of (zip bs xs) x)) x)"
proof -
  have "(\<Sum>(x, y)\<leftarrow>zip xs bs. f x y) = (\<Sum>(y, x)\<leftarrow>zip bs xs. f x y)"
    by (subst zip_commute) (auto simp: o_def split_beta')
  also have "\<dots> = (\<Sum>(x, y)\<leftarrow>zip bs (map (the o map_of (zip bs xs)) bs). f y x)"
  proof (rule arg_cong, rule map_cong)
    have "xs = (map (the \<circ> map_of (zip bs xs)) bs)"
      using assms
      by (auto intro!: nth_equalityI simp: map_nth map_of_zip_nth)
    then show "zip bs xs = zip bs (map (the \<circ> map_of (zip bs xs)) bs)"
      by simp
  qed auto
  also have "\<dots> = (\<Sum>x\<in>set bs. f (the (map_of (zip bs xs) x)) x)"
    using assms(1)
    by (subst sum_list_zip_map) (auto simp: o_def)
  finally show ?thesis .
qed



lemma vec_nth_matrix:
  "vec_nth (vec_nth (matrix y) i) j = vec_nth (y (axis j 1)) i"
  unfolding matrix_def by simp

lemma matrix_eqI:
  assumes "\<And>x. x \<in> Basis \<Longrightarrow> A *v x = B *v x"
  shows "(A::real^'n^'n) = B"
  apply vector
  using assms
  apply (auto simp: Basis_vec_def)
  by (metis cart_eq_inner_axis matrix_vector_mul_component)

lemma matrix_columnI:
  assumes "\<And>i. column i A = column i B"
  shows "(A::real^'n^'n) = B"
  using assms
  apply vector
  apply (auto simp: column_def)
  apply vector
  by (metis iso_tuple_UNIV_I vec_lambda_inject)

lemma
  vec_nth_Basis:
  fixes x::"real^'n"
  shows "x \<in> Basis \<Longrightarrow> vec_nth x i = (if x = axis i 1 then 1 else 0)"
  apply (auto simp: Basis_vec_def)
  by (metis cart_eq_inner_axis inner_axis_axis)

lemma vec_nth_eucl_of_list_eq: "length M = CARD('n) \<Longrightarrow>
  vec_nth (eucl_of_list M::real^'n::enum) i = M ! index Basis_list (axis i (1::real))"
  apply (auto simp: eucl_of_list_def)
  apply (subst sum_list_zip_map_of)
   apply (auto intro!: distinct_zipI2 simp: split_beta')
  apply (subst sum.cong[OF refl])
   apply (subst vec_nth_Basis)
    apply (force simp: set_zip)
  apply (rule refl)
  apply (auto simp: if_distrib sum.delta cong: if_cong)
  subgoal
    apply (cases "map_of (zip Basis_list M) (axis i 1::real^'n::enum)")
    subgoal premises prems
    proof -
      have "fst ` set (zip Basis_list M) = (Basis::(real^'n::enum) set)" using prems
        by (auto simp: in_set_zip)
      then show ?thesis
        using prems
        by (subst (asm) map_of_eq_None_iff) simp
    qed
    subgoal for a
      apply (auto simp: in_set_zip)
      subgoal premises prems for n
        by (metis DIM_cart DIM_real index_Basis_list_nth mult.right_neutral prems(2) prems(3))
      done
    done
  done

lemma index_Basis_list_axis1: "index Basis_list (axis i (1::real)) = index enum_class.enum i"
  apply (auto simp: Basis_list_vec_def Basis_list_real_def )
  apply (subst index_map_inj)
  by (auto intro!: injI simp: axis_eq_axis)

lemma vec_nth_eq_list_of_eucl1:
  "(vec_nth (M::real^'n::enum) i) = list_of_eucl M ! (index enum_class.enum i)"
  apply (subst eucl_of_list_list_of_eucl[of M, symmetric])
  apply (subst vec_nth_eucl_of_list_eq)
  unfolding index_Basis_list_axis1
  by auto

lemma enum_3[simp]: "(enum_class.enum::3 list) = [0, 1, 2]"
  by code_simp+

lemma three_eq_zero: "(3::3) = 0" by simp

lemma forall_3': "(\<forall>i::3. P i) \<longleftrightarrow> P 0 \<and> P 1 \<and> P 2"
  using forall_3 three_eq_zero by auto

lemma euclidean_eq_list_of_euclI: "x = y" if "list_of_eucl x = list_of_eucl y"
  using that
  by (metis eucl_of_list_list_of_eucl)

lemma axis_one_neq_zero[simp]: "axis xa (1::'a::zero_neq_one) \<noteq> 0"
  by (auto simp: axis_def vec_eq_iff)


lemma eucl_of_list_vec_nth3[simp]:
  "(eucl_of_list [g, h, i]::real^3) $ 0 = g"
  "(eucl_of_list [g, h, i]::real^3) $ 1 = h"
  "(eucl_of_list [g, h, i]::real^3) $ 2 = i"
  "(eucl_of_list [g, h, i]::real^3) $ 3 = g"
  by (auto simp: cart_eq_inner_axis eucl_of_list_inner vec_nth_eq_list_of_eucl1 index_Basis_list_axis1)

type_synonym R3 = "real*real*real"

lemma Basis_list_R3: "Basis_list = [(1,0,0), (0, 1, 0), (0, 0, 1)::R3]"
  by (auto simp: Basis_list_prod_def Basis_list_real_def zero_prod_def)

lemma Basis_list_vec3: "Basis_list = [axis 0 1::real^3, axis 1 1, axis 2 1]"
  by (auto simp: Basis_list_vec_def Basis_list_real_def)

lemma eucl_of_list3[simp]: "eucl_of_list [a, b, c] = (a, b, c)"
  by (auto simp: eucl_of_list_inner Basis_list_vec_def zero_prod_def
      Basis_prod_def Basis_list_vec3 Basis_list_R3
      intro!: euclidean_eqI[where 'a=R3])


subsection \<open>Bounded Linear Functions\<close>

subsection \<open>bounded linear functions\<close>

locale blinfun_syntax
begin
no_notation vec_nth (infixl "$" 90)
notation blinfun_apply (infixl "$" 999)
end

lemma bounded_linear_via_derivative:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector" \<comment> \<open>TODO: generalize?\<close>
  assumes "\<And>i. ((\<lambda>x. blinfun_apply (f x) i) has_derivative (\<lambda>x. f' y x i)) (at y)"
  shows "bounded_linear (f' y x)"
proof -
  interpret linear "f' y x"
  proof (unfold_locales, goal_cases)
    case (1 v w)
    from has_derivative_unique[OF assms[of "v + w", unfolded blinfun.bilinear_simps]
      has_derivative_add[OF assms[of v] assms[of w]], THEN fun_cong, of x]
    show ?case .
  next
    case (2 r v)
    from has_derivative_unique[OF assms[of "r *\<^sub>R v", unfolded blinfun.bilinear_simps]
      has_derivative_scaleR_right[OF assms[of v], of r], THEN fun_cong, of x]
    show ?case .
  qed
  let ?bnd = "\<Sum>i\<in>Basis. norm (f' y x i)"
  {
    fix v
    have "f' y x v = (\<Sum>i\<in>Basis. (v \<bullet> i) *\<^sub>R f' y x i)"
      by (subst euclidean_representation[symmetric]) (simp add: sum scaleR)
    also have "norm \<dots> \<le> norm v * ?bnd"
      by (auto intro!: order.trans[OF norm_sum] sum_mono mult_right_mono
        simp: sum_distrib_left Basis_le_norm)
    finally have "norm (f' y x v) \<le> norm v * ?bnd" .
  }
  then show ?thesis by unfold_locales auto
qed

definition blinfun_scaleR::"('a::real_normed_vector \<Rightarrow>\<^sub>L real) \<Rightarrow> 'b::real_normed_vector \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)"
  where "blinfun_scaleR a b = blinfun_scaleR_left b o\<^sub>L a"

lemma blinfun_scaleR_transfer[transfer_rule]:
  "rel_fun (pcr_blinfun (=) (=)) (rel_fun (=) (pcr_blinfun (=) (=)))
    (\<lambda>a b c. a c *\<^sub>R b) blinfun_scaleR"
  by (auto simp: blinfun_scaleR_def rel_fun_def pcr_blinfun_def cr_blinfun_def OO_def)

lemma blinfun_scaleR_rep_eq[simp]:
  "blinfun_scaleR a b c = a c *\<^sub>R b"
  by (simp add: blinfun_scaleR_def)

lemma bounded_linear_blinfun_scaleR: "bounded_linear (blinfun_scaleR a)"
  unfolding blinfun_scaleR_def[abs_def]
  by (auto intro!: bounded_linear_intros)

lemma blinfun_scaleR_has_derivative[derivative_intros]:
  assumes "(f has_derivative f') (at x within s)"
  shows "((\<lambda>x. blinfun_scaleR a (f x)) has_derivative (\<lambda>x. blinfun_scaleR a (f' x))) (at x within s)"
  using bounded_linear_blinfun_scaleR assms
  by (rule bounded_linear.has_derivative)

lemma blinfun_componentwise:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  shows "f = (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f x i))"
  by (auto intro!: blinfun_eqI
    simp: blinfun.sum_left euclidean_representation blinfun.scaleR_right[symmetric]
      blinfun.sum_right[symmetric])

lemma
  blinfun_has_derivative_componentwiseI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> ((\<lambda>x. f x i) has_derivative blinfun_apply (f' i)) (at x)"
  shows "(f has_derivative (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' i x))) (at x)"
  by (subst blinfun_componentwise) (force intro: derivative_eq_intros assms simp: blinfun.bilinear_simps)

lemma
  has_derivative_BlinfunI:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::euclidean_space \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  assumes "\<And>i. ((\<lambda>x. f x i) has_derivative (\<lambda>x. f' y x i)) (at y)"
  shows "(f has_derivative (\<lambda>x. Blinfun (f' y x))) (at y)"
proof -
  have 1: "f = (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f x i))"
    by (rule blinfun_componentwise)
  moreover have 2: "(\<dots> has_derivative (\<lambda>x. \<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' y x i))) (at y)"
    by (force intro: assms derivative_eq_intros)
  moreover
  interpret f': bounded_linear "f' y x" for x
    by (rule bounded_linear_via_derivative) (rule assms)
  have 3: "(\<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (f' y x i)) i = f' y x i" for x i
    by (auto simp: if_distrib if_distribR blinfun.bilinear_simps
      f'.scaleR[symmetric] f'.sum[symmetric] euclidean_representation
      intro!: blinfun_euclidean_eqI)
  have 4: "blinfun_apply (Blinfun (f' y x)) = f' y x" for x
    apply (subst bounded_linear_Blinfun_apply)
    subgoal by unfold_locales
    subgoal by simp
    done
  show ?thesis
    apply (subst 1)
    apply (rule 2[THEN has_derivative_eq_rhs])
    apply (rule ext)
    apply (rule blinfun_eqI)
    apply (subst 3)
    apply (subst 4)
    apply (rule refl)
    done
qed

lemma
  has_derivative_Blinfun:
  assumes "(f has_derivative f') F"
  shows "(f has_derivative Blinfun f') F"
  using assms
  by (subst bounded_linear_Blinfun_apply) auto

lift_definition flip_blinfun::
  "('a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector) \<Rightarrow> 'b \<Rightarrow>\<^sub>L 'a \<Rightarrow>\<^sub>L 'c" is
  "\<lambda>f x y. f y x"
  using bounded_bilinear.bounded_linear_left bounded_bilinear.bounded_linear_right bounded_bilinear.flip
  by auto

lemma flip_blinfun_apply[simp]: "flip_blinfun f a b = f b a"
  by transfer simp

lemma le_norm_blinfun:
  shows "norm (blinfun_apply f x) / norm x \<le> norm f"
  by transfer (rule le_onorm)

lemma norm_flip_blinfun[simp]: "norm (flip_blinfun x) = norm x" (is "?l = ?r")
proof (rule antisym)
  from order_trans[OF norm_blinfun, OF mult_right_mono, OF norm_blinfun, OF norm_ge_zero, of x]
  show "?l \<le> ?r"
    by (auto intro!: norm_blinfun_bound simp: ac_simps)
  have "norm (x a b) \<le> norm (flip_blinfun x) * norm a * norm b" for a b
  proof -
    have "norm (x a b) / norm a \<le> norm (flip_blinfun x b)"
      by (rule order_trans[OF _ le_norm_blinfun]) auto
    also have "\<dots> \<le> norm (flip_blinfun x) * norm b"
      by (rule norm_blinfun)
    finally show ?thesis
      by (auto simp add: divide_simps blinfun.bilinear_simps algebra_simps split: if_split_asm)
  qed
  then show "?r \<le> ?l"
    by (auto intro!: norm_blinfun_bound)
qed

lemma bounded_linear_flip_blinfun[bounded_linear]: "bounded_linear flip_blinfun"
  by unfold_locales (auto simp: blinfun.bilinear_simps intro!: blinfun_eqI exI[where x=1])

lemma dist_swap2_swap2[simp]: "dist (flip_blinfun f) (flip_blinfun g) = dist f g"
  by (metis (no_types) bounded_linear_flip_blinfun dist_blinfun_def linear_simps(2)
    norm_flip_blinfun)


context includes blinfun.lifting begin

lift_definition blinfun_of_vmatrix::"(real^'m^'n) \<Rightarrow> ((real^('m::finite)) \<Rightarrow>\<^sub>L (real^('n::finite)))" is
  "matrix_vector_mult:: ((real, 'm) vec, 'n) vec \<Rightarrow> ((real, 'm) vec \<Rightarrow> (real, 'n) vec)"
  unfolding linear_linear
  by (rule matrix_vector_mul_linear)

lemma matrix_blinfun_of_vmatrix[simp]: "matrix (blinfun_of_vmatrix M) = M"
  apply vector
  apply (auto simp: matrix_def)
  apply transfer
  by (metis cart_eq_inner_axis matrix_vector_mul_component)

end

lemma blinfun_apply_componentwise:
  "B = (\<Sum>i\<in>Basis. blinfun_scaleR (blinfun_inner_left i) (blinfun_apply B i))"
  using blinfun_componentwise[of "\<lambda>x. B", unfolded fun_eq_iff]
  by blast

lemma blinfun_apply_eq_sum:
  assumes [simp]: "length v = CARD('n)"
  shows "blinfun_apply (B::(real^'n::enum)\<Rightarrow>\<^sub>L(real^'m::enum)) (eucl_of_list v) =
    (\<Sum>i<CARD('m). \<Sum>j<CARD('n). ((B (Basis_list ! j) \<bullet> Basis_list ! i) * v ! j) *\<^sub>R (Basis_list ! i))"
  apply (subst blinfun_apply_componentwise[of B])
  apply (auto intro!: euclidean_eqI[where 'a="(real,'m) vec"]
      simp: blinfun.bilinear_simps eucl_of_list_inner inner_sum_left inner_Basis if_distrib
        sum_Basis_sum_nth_Basis_list nth_eq_iff_index if_distribR
        cong: if_cong)
  apply (subst sum.swap)
  by (auto simp: sum.delta algebra_simps)

lemma in_square_lemma[intro, simp]: "x * C + y < D * C" if "x < D" "y < C" for x::nat
proof -
  have "x * C + y < (D - 1) * C + C"
    apply (rule add_le_less_mono)
     apply (rule mult_right_mono)
    using that
    by auto
  also have "\<dots> \<le> D * C"
    using that
    by (auto simp: algebra_simps)
  finally show ?thesis .
qed

lemma less_square_imp_div_less[intro, simp]: "i < E * D \<Longrightarrow>  i div E < D" for i::nat
  by (metis div_eq_0_iff div_mult2_eq gr_implies_not0 mult_not_zero)

lemma in_square_lemma'[intro, simp]: "i < L \<Longrightarrow> n < N \<Longrightarrow> i * N + n < N * L" for i n::nat
  by (metis in_square_lemma mult.commute)

lemma
  distinct_nth_eq_iff:
  "distinct xs \<Longrightarrow> x < length xs \<Longrightarrow> y < length xs \<Longrightarrow> xs ! x = xs ! y \<longleftrightarrow> x = y"
  by (drule inj_on_nth[where I="{..<length xs}"]) (auto simp: inj_onD)

lemma index_Basis_list_axis2:
  "index Basis_list (axis (j::'j::enum) (axis (i::'i::enum) (1::real))) =
    (index enum_class.enum j) * CARD('i) + index enum_class.enum i"
  apply (auto simp: Basis_list_vec_def Basis_list_real_def o_def)
  apply (subst concat_map_map_index)
  unfolding card_UNIV_length_enum[symmetric]
  subgoal
  proof -
    have index_less_cardi: "index enum_class.enum k < CARD('i)" for k::'i
      by (rule index_less) (auto simp: enum_UNIV card_UNIV_length_enum)
    have index_less_cardj: "index enum_class.enum k < CARD('j)" for k::'j
      by (rule index_less) (auto simp: enum_UNIV card_UNIV_length_enum)
    have *: "axis j (axis i 1) =
      (\<lambda>i. axis (enum_class.enum ! (i div CARD('i)))
                      (axis (enum_class.enum ! (i mod CARD('i))) 1))
      ((index enum_class.enum j) * CARD('i) + index enum_class.enum i)"
      by (auto simp: index_less_cardi enum_UNIV)
    note less=in_square_lemma[OF index_less_cardj index_less_cardi, of j i]
    show ?thesis
      apply (subst *)
      apply (subst index_map_inj_on[where S="{..<CARD('j)*CARD('i)}"])
      subgoal
        apply (auto intro!: inj_onI simp: axis_eq_axis )
         apply (subst (asm) distinct_nth_eq_iff)
        apply (auto simp: enum_distinct card_UNIV_length_enum)
        subgoal for x y
          using gr_implies_not0 by fastforce
        subgoal for x y
          using gr_implies_not0 by fastforce
        subgoal for x y
          apply (drule inj_onD[OF inj_on_nth[OF enum_distinct[where 'a='j], where I = "{..<CARD('j)}"], rotated])
             apply (auto simp: card_UNIV_length_enum mult.commute)
          subgoal
            by (metis mod_mult_div_eq)
          done
        done
      subgoal using less by (auto simp: )
      subgoal by (auto simp: card_UNIV_length_enum ac_simps)
      subgoal apply (subst index_upt)
        subgoal using less by auto
        subgoal using less by (auto simp: ac_simps)
        subgoal using less by auto
        done
      done
  qed
  done

lemma
  vec_nth_Basis2:
  fixes x::"real^'n^'m"
  shows "x \<in> Basis \<Longrightarrow> vec_nth (vec_nth x i) j = ((if x = axis i (axis j 1) then 1 else 0))"
  by (auto simp: Basis_vec_def axis_def)

lemma vec_nth_eucl_of_list_eq2: "length M = CARD('n) * CARD('m) \<Longrightarrow>
  vec_nth (vec_nth (eucl_of_list M::real^'n::enum^'m::enum) i) j = M ! index Basis_list (axis i (axis j (1::real)))"
  apply (auto simp: eucl_of_list_def)
  apply (subst sum_list_zip_map_of)
   apply (auto intro!: distinct_zipI2 simp: split_beta')
  apply (subst sum.cong[OF refl])
   apply (subst vec_nth_Basis2)
    apply (force simp: set_zip)
  apply (rule refl)
  apply (auto simp: if_distrib sum.delta cong: if_cong)
  subgoal
    apply (cases "map_of (zip Basis_list M) (axis i (axis j 1)::real^'n::enum^'m::enum)")
    subgoal premises prems
    proof -
      have "fst ` set (zip Basis_list M) = (Basis::(real^'n::enum^'m::enum) set)" using prems
        by (auto simp: in_set_zip)
      then show ?thesis
        using prems
        by (subst (asm) map_of_eq_None_iff) auto
    qed
    subgoal for a
      apply (auto simp: in_set_zip)
      subgoal premises prems for n
      proof -
        have "n < card (Basis::(real^'n::_^'m::_) set)"
          by (simp add: prems(4))
        then show ?thesis
          by (metis index_Basis_list_nth prems(2))
      qed
      done
    done
  done

lemma vec_nth_eq_list_of_eucl2:
  "vec_nth (vec_nth (M::real^'n::enum^'m::enum) i) j =
    list_of_eucl M ! (index enum_class.enum i * CARD('n) + index enum_class.enum j)"
  apply (subst eucl_of_list_list_of_eucl[of M, symmetric])
  apply (subst vec_nth_eucl_of_list_eq2)
  unfolding index_Basis_list_axis2
  by auto

theorem
  eucl_of_list_matrix_vector_mult_eq_sum_nth_Basis_list:
  assumes "length M = CARD('n) * CARD('m)"
  assumes "length v = CARD('n)"
  shows "(eucl_of_list M::real^'n::enum^'m::enum) *v eucl_of_list v =
    (\<Sum>i<CARD('m).
      (\<Sum>j<CARD('n). M ! (i * CARD('n) + j) * v ! j) *\<^sub>R Basis_list ! i)"
  apply (vector matrix_vector_mult_def)
  apply (auto simp: )
  apply (subst vec_nth_eucl_of_list_eq2)
   apply (auto simp: assms)
  apply (subst vec_nth_eucl_of_list_eq)
   apply (auto simp: assms index_Basis_list_axis2 index_Basis_list_axis1 vec_nth_Basis sum.delta
      nth_eq_iff_index
      if_distrib cong: if_cong)
  subgoal for i
    apply (rule sum.reindex_cong[where l="nth enum_class.enum"])
      apply (auto simp: enum_distinct card_UNIV_length_enum distinct_nth_eq_iff intro!: inj_onI)
     apply (rule image_eqI[OF ])
      apply (rule nth_index[symmetric])
      apply (auto simp: enum_UNIV)
    by (auto simp: algebra_simps enum_UNIV enum_distinct index_nth_id)
  subgoal for i
    using index_less[of i "enum_class.enum" "CARD('n)"]
    by (auto simp: enum_UNIV card_UNIV_length_enum)
  done

lemma index_enum_less[intro, simp]: "index enum_class.enum (i::'n::enum) < CARD('n)"
  by (auto intro!: index_less simp: enum_UNIV card_UNIV_length_enum)

lemmas [intro, simp] = enum_distinct
lemmas [simp] = card_UNIV_length_enum[symmetric] enum_UNIV

lemma sum_index_enum_eq:
  "(\<Sum>(k::'n::enum)\<in>UNIV. f (index enum_class.enum k)) = (\<Sum>i<CARD('n). f i)"
  by (rule sum.reindex_cong[where l="nth enum_class.enum"])
    (force intro!: inj_onI simp: distinct_nth_eq_iff index_nth_id)+

end