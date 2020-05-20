(*
Author:  Florian Messner <florian.g.messner@uibk.ac.at>
Author:  Julian Parsert <julian.parsert@gmail.com>
Author:  Jonas Schöpf <jonas.schoepf@uibk.ac.at>
Author:  Christian Sternagel <c.sternagel@gmail.com>
License: LGPL
*)

section \<open>Vectors as Lists of Naturals\<close>

theory List_Vector
  imports Main
begin

(*TODO: move*)
lemma lex_lengthD: "(x, y) \<in> lex P \<Longrightarrow> length x = length y"
  by (auto simp: lexord_lex)

(*TODO: move*)
lemma lexI:
  assumes "length ys = length xs" and "i < length xs"
    and "take i xs = take i ys" and "(xs ! i, ys ! i) \<in> r"
  shows "(xs, ys) \<in> lex r"
proof -
  have "xs = take i xs @ xs ! i # drop (Suc i) xs"
    and "ys = take i ys @ ys ! i # drop (Suc i) ys"
    using assms by (metis id_take_nth_drop)+
  then show ?thesis
    using assms by (auto simp: lex_def lexn_conv)
qed

(*TODO: move*)
lemma lex_take_index:
  assumes "(xs, ys) \<in> lex r"
  obtains i where "length ys = length xs"
    and "i < length xs" and "take i xs = take i ys"
    and "(xs ! i, ys ! i) \<in> r"
proof -
  obtain n us x xs' y ys' where "(xs, ys) \<in> lexn r n" and "length xs = n" and "length ys = n"
    and "xs = us @ x # xs'" and "ys = us @ y # ys'" and "(x, y) \<in> r"
    using assms by (fastforce simp: lex_def lexn_conv)
  then show ?thesis by (intro that [of "length us"]) auto
qed

(*TODO: move*)
lemma mods_with_nats:
  assumes "(v::nat) > w"
    and "(v * b) mod a = (w * b) mod a"
  shows "((v - w) * b) mod a = 0"
  by (metis add_diff_cancel_left' assms left_diff_distrib'
      less_imp_le mod_mult_self1_is_0 mult_le_mono1 nat_mod_eq_lemma)

\<comment> \<open>The 0-vector of length \<open>n\<close>.\<close>
abbreviation zeroes :: "nat \<Rightarrow> nat list"
  where
    "zeroes n \<equiv> replicate n 0"

lemma rep_upd_unit:
  assumes "x = (zeroes n)[i := a]"
  shows "\<forall>j < length x. (j \<noteq> i \<longrightarrow> x ! j = 0) \<and> (j = i \<longrightarrow> x ! j = a)"
  using assms by simp

definition nonzero_iff: "nonzero xs \<longleftrightarrow> (\<exists>x\<in>set xs. x \<noteq> 0)"

lemma nonzero_append [simp]:
  "nonzero (xs @ ys) \<longleftrightarrow> nonzero xs \<or> nonzero ys" by (auto simp: nonzero_iff)


subsection \<open>The Inner Product\<close>

definition dotprod :: "nat list \<Rightarrow> nat list \<Rightarrow> nat" (infixl "\<bullet>" 70)
  where
    "xs \<bullet> ys = (\<Sum>i<min (length xs) (length ys). xs ! i * ys ! i)"

lemma dotprod_code [code]:
  "xs \<bullet> ys = sum_list (map (\<lambda>(x, y). x * y) (zip xs ys))"
  by (auto simp: dotprod_def sum_list_sum_nth lessThan_atLeast0)

lemma dotprod_commute:
  assumes "length xs = length ys"
  shows "xs \<bullet> ys = ys \<bullet> xs"
  using assms by (auto simp: dotprod_def mult.commute)

lemma dotprod_Nil [simp]: "[] \<bullet> [] = 0"
  by (simp add: dotprod_def)

lemma dotprod_Cons [simp]:
  "(x # xs) \<bullet> (y # ys) = x * y + xs \<bullet> ys"
  unfolding dotprod_def and length_Cons and min_Suc_Suc and sum.lessThan_Suc_shift by auto

lemma dotprod_1_right [simp]:
  "xs \<bullet> replicate (length xs) 1 = sum_list xs"
  by (induct xs) (simp_all)

lemma dotprod_0_right [simp]:
  "xs \<bullet> zeroes (length xs) = 0"
  by (induct xs) (simp_all)

lemma dotprod_unit [simp]:
  assumes "length a = n"
    and "k < n"
  shows "a \<bullet> (zeroes n)[k := zk] = a ! k * zk"
  using assms by (induct a arbitrary: k n) (auto split: nat.splits)

lemma dotprod_gt0:
  assumes "length x = length y" and "\<exists>i<length y. x ! i > 0 \<and> y ! i > 0"
  shows "x \<bullet> y > 0"
  using assms by (induct x y rule: list_induct2) (fastforce simp: nth_Cons split: nat.splits)+

lemma dotprod_gt0D:
  assumes "length x = length y"
    and "x \<bullet> y > 0"
  shows "\<exists>i<length y. x ! i > 0 \<and> y ! i > 0"
  using assms by (induct x y rule: list_induct2) (auto simp: Ex_less_Suc2)

lemma dotprod_gt0_iff [iff]:
  assumes "length x = length y"
  shows "x \<bullet> y > 0 \<longleftrightarrow> (\<exists>i<length y. x ! i > 0 \<and> y ! i > 0)"
  using assms and dotprod_gt0D and dotprod_gt0 by blast

lemma dotprod_append:
  assumes "length a = length b"
  shows"(a @ x) \<bullet> (b @ y) = a \<bullet> b + x \<bullet> y"
  using assms by (induct a b rule: list_induct2) auto

lemma dotprod_le_take:
  assumes "length a = length b"
    and "k \<le> length a"
  shows"take k a \<bullet> take k b \<le> a \<bullet> b"
  using assms and append_take_drop_id [of k a] and append_take_drop_id [of k b]
  by (metis add_right_cancel leI length_append length_drop not_add_less1 dotprod_append)

lemma dotprod_le_drop:
  assumes "length a = length b"
    and "k \<le> length a"
  shows "drop k a \<bullet> drop k b \<le> a \<bullet> b"
  using assms and append_take_drop_id [of k a] and append_take_drop_id [of k b]
  by (metis dotprod_append length_take order_refl trans_le_add2)

lemma dotprod_is_0 [simp]:
  assumes "length x = length y"
  shows "x \<bullet> y = 0 \<longleftrightarrow> (\<forall>i<length y. x ! i = 0 \<or> y ! i = 0)"
  using assms by (metis dotprod_gt0_iff neq0_conv)

lemma dotprod_eq_0_iff:
  assumes "length x = length a"
    and "0 \<notin> set a"
  shows "x \<bullet> a = 0 \<longleftrightarrow> (\<forall>e \<in> set x. e = 0)"
  using assms by (fastforce simp: in_set_conv_nth)

lemma dotprod_eq_nonzero_iff:
  assumes "a \<bullet> x = b \<bullet> y" and "length x = length a" and "length y = length b"
    and "0 \<notin> set a" and "0 \<notin> set b"
  shows "nonzero x \<longleftrightarrow> nonzero y"
  using assms by (auto simp: nonzero_iff) (metis dotprod_commute dotprod_eq_0_iff neq0_conv)+

lemma eq_0_iff:
  "xs = zeroes n \<longleftrightarrow> length xs = n \<and> (\<forall>x\<in>set xs. x = 0)"
  using in_set_replicate [of _ n 0] and replicate_eqI [of xs n 0] by auto

lemma not_nonzero_iff: "\<not> nonzero x \<longleftrightarrow> x = zeroes (length x)"
  by (auto simp: nonzero_iff replicate_length_same eq_0_iff)

lemma neq_0_iff':
  "xs \<noteq> zeroes n \<longleftrightarrow> length xs \<noteq> n \<or> (\<exists>x\<in>set xs. x > 0)"
  by (auto simp: eq_0_iff)

lemma dotprod_pointwise_le:
  assumes "length as = length xs"
    and "i < length as"
  shows "as ! i * xs ! i \<le> as \<bullet> xs"
proof -
  have "as \<bullet> xs = (\<Sum>i<min (length as) (length xs). as ! i * xs ! i)"
    by (simp add: dotprod_def)
  then show ?thesis
    using assms by (auto intro: member_le_sum)
qed

lemma replicate_dotprod:
  assumes "length y = n"
  shows "replicate n x \<bullet> y = x * sum_list y"
proof -
  have "x * (\<Sum>i<length y.  y ! i) = (\<Sum>i<length y. x * y ! i)"
    using sum_distrib_left by blast
  then show ?thesis
    using assms by (auto simp: dotprod_def sum_list_sum_nth atLeast0LessThan)
qed


subsection \<open>The Pointwise Order on Vectors\<close>

definition  less_eq :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" ("_/ \<le>\<^sub>v _" [51, 51] 50)
  where
    "xs \<le>\<^sub>v ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>i<length xs. xs ! i \<le> ys ! i)"

definition less :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" ("_/ <\<^sub>v _" [51, 51] 50)
  where
    "xs <\<^sub>v ys \<longleftrightarrow> xs \<le>\<^sub>v ys \<and> \<not> ys \<le>\<^sub>v xs"

interpretation order_vec: order less_eq less
  by (standard, auto simp add: less_def less_eq_def dual_order.antisym nth_equalityI) (force)

lemma less_eqI [intro?]: "length xs = length ys \<Longrightarrow> \<forall>i<length xs. xs ! i \<le> ys ! i \<Longrightarrow> xs \<le>\<^sub>v ys"
  by (auto simp: less_eq_def)

lemma le0 [simp, intro]: "zeroes (length xs) \<le>\<^sub>v xs" by (simp add: less_eq_def)

lemma le_list_update [simp]:
  assumes "xs \<le>\<^sub>v ys" and "i < length ys" and "z \<le> ys ! i"
  shows "xs[i := z] \<le>\<^sub>v ys"
  using assms by (auto simp: less_eq_def nth_list_update)

lemma le_Cons: "x # xs \<le>\<^sub>v y # ys \<longleftrightarrow> x \<le> y \<and> xs \<le>\<^sub>v ys"
  by (auto simp add: less_eq_def nth_Cons split: nat.splits)

lemma zero_less:
  assumes "nonzero x"
  shows "zeroes (length x) <\<^sub>v x"
  using assms and eq_0_iff order_vec.dual_order.strict_iff_order
  by (auto simp: nonzero_iff)

lemma le_append:
  assumes "length xs = length vs"
  shows "xs @ ys \<le>\<^sub>v vs @ ws \<longleftrightarrow> xs \<le>\<^sub>v vs \<and> ys \<le>\<^sub>v ws"
  using assms
  by (auto simp: less_eq_def nth_append)
    (metis add.commute add_diff_cancel_left' nat_add_left_cancel_less not_add_less2)

lemma less_Cons:
  "(x # xs) <\<^sub>v (y # ys) \<longleftrightarrow> length xs = length ys \<and> (x \<le> y \<and> xs <\<^sub>v ys \<or> x < y \<and> xs \<le>\<^sub>v ys)"
  by (simp add: less_def less_eq_def All_less_Suc2) (auto dest: leD)

lemma le_length [dest]:
  assumes "xs \<le>\<^sub>v ys"
  shows "length xs = length ys"
  using assms by (simp add: less_eq_def)

lemma less_length [dest]:
  assumes "x <\<^sub>v y"
  shows "length x = length y"
  using assms by (auto simp: less_def)

lemma less_append:
  assumes "xs <\<^sub>v vs " and "ys \<le>\<^sub>v ws"
  shows "xs @ ys <\<^sub>v vs @ ws"
proof -
  have "length xs  = length vs"
    using assms by blast
  then show ?thesis
    using assms by (induct xs vs rule: list_induct2) (auto simp: less_Cons le_append le_length)
qed

lemma less_appendD:
  assumes "xs @ ys <\<^sub>v vs @ ws"
    and "length xs = length vs"
  shows "xs <\<^sub>v vs \<or> ys <\<^sub>v ws"
  by (auto) (metis (no_types, lifting) assms le_append order_vec.order.strict_iff_order)

lemma less_append_cases:
  assumes "xs @ ys <\<^sub>v vs @ ws" and "length xs = length vs"
  obtains "xs <\<^sub>v vs" and "ys \<le>\<^sub>v ws" | "xs \<le>\<^sub>v vs" and "ys <\<^sub>v ws"
  using assms and that
  by (metis le_append less_appendD order_vec.order.strict_implies_order)

lemma less_append_swap:
  assumes "x @ y <\<^sub>v u @ v"
    and "length x = length u"
  shows "y @ x <\<^sub>v v @ u"
  using assms(2, 1)
  by (induct x u rule: list_induct2)
    (auto simp: order_vec.order.strict_iff_order le_Cons le_append le_length)

lemma le_sum_list_less:
  assumes "xs \<le>\<^sub>v ys"
    and "sum_list xs < sum_list ys"
  shows "xs <\<^sub>v ys"
proof -
  have "length xs = length ys" and "\<forall>i<length ys. xs ! i \<le> ys ! i"
    using assms by (auto simp: less_eq_def)
  then show ?thesis
    using \<open>sum_list xs < sum_list ys\<close>
    by (induct xs ys rule: list_induct2)
      (auto simp: less_Cons All_less_Suc2 less_eq_def)
qed

lemma dotprod_le_right:
  assumes "v \<le>\<^sub>v w"
    and "length b = length w"
  shows "b \<bullet> v \<le> b \<bullet> w"
  using assms by (auto simp: dotprod_def less_eq_def intro: sum_mono)

lemma dotprod_pointwise_le_right:
  assumes "length z = length u"
    and "length u = length v"
    and "\<forall>i<length v. u ! i \<le> v ! i"
  shows "z \<bullet> u \<le> z \<bullet> v"
  using assms by (intro dotprod_le_right) (auto intro: less_eqI)

lemma dotprod_le_left:
  assumes "v \<le>\<^sub>v w"
    and "length b = length w"
  shows "v \<bullet> b \<le> w \<bullet> b "
  using assms by (simp add: dotprod_le_right dotprod_commute le_length)

lemma dotprod_le:
  assumes "x \<le>\<^sub>v u" and "y \<le>\<^sub>v v"
    and "length y = length x" and "length v = length u"
  shows "x \<bullet> y \<le> u \<bullet> v"
  using assms by (metis dotprod_le_left dotprod_le_right le_length le_trans)

lemma dotprod_less_left:
  assumes "length b = length w"
    and "0 \<notin> set b"
    and "v <\<^sub>v w"
  shows "v \<bullet> b < w \<bullet> b"
proof -
  have "length v = length w" using assms
    using less_eq_def order_vec.order.strict_implies_order by blast
  then show ?thesis
    using assms
  proof (induct v w arbitrary: b rule: list_induct2)
    case (Cons x xs y ys)
    then show ?case
      by (cases b) (auto simp: less_Cons add_mono_thms_linordered_field dotprod_le_left)
  qed simp
qed

lemma le_append_swap:
  assumes "length y = length v"
    and "x @ y \<le>\<^sub>v w @ v"
  shows "y @ x \<le>\<^sub>v v @ w"
proof -
  have "length w = length x" using assms by auto
  with assms show ?thesis
    by (induct y v arbitrary: x w rule: list_induct2) (auto simp: le_Cons le_append)
qed

lemma le_append_swap_iff:
  assumes "length y = length v"
  shows "y @ x \<le>\<^sub>v v @ w  \<longleftrightarrow> x @ y \<le>\<^sub>v w @ v"
  using assms and le_append_swap
  by (auto) (metis (no_types, lifting) add_left_imp_eq le_length length_append)

lemma unit_less:
  assumes "i < n"
    and "x <\<^sub>v (zeroes n)[i := b]"
  shows "x ! i < b \<and> (\<forall>j<n. j \<noteq> i \<longrightarrow> x ! j = 0)"
proof
  show "x ! i < b"
    using assms less_def by fastforce
next
  have "x \<le>\<^sub>v (zeroes n)[i := b]" by (simp add: assms order_vec.less_imp_le)
  then show "\<forall>j<n. j \<noteq> i \<longrightarrow> x ! j = 0" by (auto simp: less_eq_def)
qed

lemma le_sum_list_mono:
  assumes "xs \<le>\<^sub>v ys"
  shows "sum_list xs \<le> sum_list ys"
  using assms and sum_list_mono [of "[0..<length ys]" "(!) xs" "(!) ys"]
  by (auto simp: less_eq_def) (metis map_nth)

lemma sum_list_less_diff_Ex:
  assumes "u \<le>\<^sub>v y"
    and "sum_list u < sum_list y"
  shows "\<exists>i<length y. u ! i < y ! i"
proof -
  have "length u = length y" and "\<forall>i<length y. u ! i \<le> y ! i"
    using \<open>u \<le>\<^sub>v y\<close> by (auto simp: less_eq_def)
  then show ?thesis
    using \<open>sum_list u < sum_list y\<close>
    by (induct u y rule: list_induct2) (force simp: Ex_less_Suc2 All_less_Suc2)+
qed

lemma less_vec_sum_list_less:
  assumes "v <\<^sub>v w"
  shows "sum_list v < sum_list w"
  using assms
proof -
  have "length v = length w"
    using assms less_eq_def less_imp_le by blast
  then show ?thesis
    using assms
  proof (induct v w rule: list_induct2)
    case (Cons x xs y ys)
    then show ?case
      using length_replicate less_Cons order_vec.order.strict_iff_order by force
  qed simp
qed

definition maxne0 :: "nat list \<Rightarrow> nat list \<Rightarrow> nat"
  where
    "maxne0 x a =
      (if length x = length a \<and> (\<exists>i<length a. x ! i \<noteq> 0)
      then Max {a ! i | i. i < length a \<and> x ! i \<noteq> 0}
      else 0)"

lemma maxne0_le_Max:
  "maxne0 x a \<le> Max (set a)"
  by (auto simp: maxne0_def nonzero_iff in_set_conv_nth) simp

lemma maxne0_Nil [simp]:
  "maxne0 [] as = 0"
  "maxne0 xs [] = 0"
  by (auto simp: maxne0_def)

lemma maxne0_Cons [simp]:
  "maxne0 (x # xs) (a # as) =
    (if length xs = length as then
      (if x = 0 then maxne0 xs as else max a (maxne0 xs as))
    else 0)"
proof -
  let ?a = "a # as" and ?x = "x # xs"
  have eq: "{?a ! i | i. i < length ?a \<and> ?x ! i \<noteq> 0} =
    (if x > 0 then {a} else {}) \<union> {as ! i | i. i < length as \<and> xs ! i \<noteq> 0}"
    by (auto simp: nth_Cons split: nat.splits) (metis Suc_pred)+
  show ?thesis
    unfolding maxne0_def and eq
    by (auto simp: less_Suc_eq_0_disj nth_Cons' intro: Max_insert2)
qed

lemma maxne0_times_sum_list_gt_dotprod:
  assumes "length b = length ys"
  shows "maxne0 ys b * sum_list ys \<ge> b \<bullet> ys"
  using assms
  apply (induct b ys rule: list_induct2)
   apply (auto  simp: max_def ring_distribs add_mono_thms_linordered_semiring(1))
  by (meson leI le_trans mult_less_cancel2 nat_less_le)

lemma max_times_sum_list_gt_dotprod:
  assumes "length b = length ys"
  shows "Max (set b) * sum_list ys \<ge> b \<bullet> ys"
proof -
  have "\<forall> e \<in> set b . Max (set b) \<ge> e" by simp
  then have "replicate (length ys) (Max (set b)) \<bullet> ys \<ge> b \<bullet> ys" (is "?rep \<ge> _")
    by (metis assms dotprod_pointwise_le_right dotprod_commute
        length_replicate nth_mem nth_replicate)
  moreover have "Max (set b) * sum_list ys = ?rep"
    using replicate_dotprod [of ys _ "Max (set b)"] by auto
  ultimately show ?thesis
    by (simp add: assms)
qed

lemma maxne0_mono:
  assumes "y \<le>\<^sub>v x"
  shows "maxne0 y a \<le> maxne0 x a"
proof (cases "length y = length a")
  case True
  have "length y = length x" using assms by (auto)
  then show ?thesis
    using assms and True
  proof (induct y x arbitrary: a rule: list_induct2)
    case (Cons x xs y ys)
    then show ?case by (cases a) (force simp: less_eq_def All_less_Suc2 le_max_iff_disj)+
  qed simp
next
  case False
  then show ?thesis
    using assms by (auto simp: maxne0_def)
qed

lemma all_leq_Max:
  assumes "x \<le>\<^sub>v y"
    and "x \<noteq> []"
  shows "\<forall>xi \<in> set x. xi \<le> Max (set y)"
  by (metis (no_types, lifting) List.finite_set Max_ge_iff
      assms in_set_conv_nth length_0_conv less_eq_def set_empty)

lemma le_not_less_replicate:
  "\<forall>x\<in>set xs. x \<le> b \<Longrightarrow> \<not> xs <\<^sub>v replicate (length xs) b \<Longrightarrow> xs = replicate (length xs) b"
  by (induct xs) (auto simp: less_Cons)

lemma le_replicateI: "\<forall>x\<in>set xs. x \<le> b \<Longrightarrow> xs \<le>\<^sub>v replicate (length xs) b"
  by (induct xs) (auto simp: le_Cons)

lemma le_take:
  assumes "x \<le>\<^sub>v y" and "i \<le> length x" shows "take i x \<le>\<^sub>v take i y"
  using assms by (auto simp: less_eq_def)

lemma wf_less:
  "wf {(x, y). x <\<^sub>v y}"
proof -
  have "wf (measure sum_list)" ..
  moreover have "{(x, y). x <\<^sub>v y} \<subseteq> measure sum_list"
    by (auto simp: less_vec_sum_list_less)
  ultimately show "wf {(x, y). x <\<^sub>v y}"
    by (rule wf_subset)
qed


subsection \<open>Pointwise Subtraction\<close>

definition vdiff :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" (infixl "-\<^sub>v" 65)
  where
    "w -\<^sub>v v = map (\<lambda>i. w ! i - v ! i) [0 ..< length w]"

lemma vdiff_Nil [simp]: "[] -\<^sub>v [] = []" by (simp add: vdiff_def)

lemma upt_Cons_conv:
  assumes "j < n"
  shows "[j..<n] = j # [j+1..<n]"
  by (simp add: assms upt_eq_Cons_conv)

lemma map_upt_Suc: "map f [Suc m ..< Suc n] = map (f \<circ> Suc) [m ..< n]"
  by (fold list.map_comp [of f "Suc" "[m ..< n]"]) (simp add: map_Suc_upt)

lemma vdiff_Cons [simp]:
  "(x # xs) -\<^sub>v (y # ys) = (x - y) # (xs -\<^sub>v ys)"
  by (simp add: vdiff_def upt_Cons_conv [OF zero_less_Suc] map_upt_Suc del: upt_Suc)

lemma vdiff_alt_def:
  assumes "length w = length v"
  shows "w -\<^sub>v v = map (\<lambda>(x, y). x - y) (zip w v)"
  using assms by (induct rule: list_induct2) simp_all

lemma vdiff_dotprod_distr:
  assumes "length b = length w"
    and "v \<le>\<^sub>v w"
  shows "(w -\<^sub>v v) \<bullet> b = w \<bullet> b - v \<bullet> b"
proof -
  have "length v = length w" and "\<forall>i<length w. v ! i \<le> w ! i"
    using assms less_eq_def by auto
  then show ?thesis
    using \<open>length b = length w\<close>
  proof (induct v w arbitrary: b rule: list_induct2)
    case (Cons x xs y ys)
    then show ?case
      by (cases b) (auto simp: All_less_Suc2 diff_mult_distrib
          dotprod_commute dotprod_pointwise_le_right)
  qed simp
qed

lemma sum_list_vdiff_distr [simp]:
  assumes "v \<le>\<^sub>v u"
  shows "sum_list (u -\<^sub>v v) = sum_list u - sum_list v"
  by (metis (no_types, lifting) assms diff_zero dotprod_1_right
      length_map length_replicate length_upt
      less_eq_def vdiff_def vdiff_dotprod_distr)

lemma vdiff_le:
  assumes "v \<le>\<^sub>v w"
    and "length v = length x"
  shows "v -\<^sub>v x \<le>\<^sub>v w"
  using assms by (auto simp add: less_eq_def vdiff_def)

lemma mods_with_vec:
  assumes "v <\<^sub>v w"
    and "0 \<notin> set b"
    and "length b = length w"
    and "(v \<bullet> b) mod a = (w \<bullet> b) mod a"
  shows "((w -\<^sub>v v) \<bullet> b) mod a = 0"
proof -
  have *: "v \<bullet> b < w \<bullet> b"
    using dotprod_less_left and assms by blast
  have "v \<le>\<^sub>v w"
    using assms by auto
  from vdiff_dotprod_distr [OF assms(3) this]
  have "((w -\<^sub>v v) \<bullet> b) mod a = (w \<bullet> b - v \<bullet> b) mod a "
    by simp
  also have "... = 0 mod a"
    using mods_with_nats [of "v \<bullet> b" "w \<bullet> b" "1" a, OF *] assms by auto
  finally show ?thesis by simp
qed

lemma mods_with_vec_2:
  assumes "v <\<^sub>v w"
    and "0 \<notin> set b"
    and "length b = length w"
    and "(b \<bullet> v) mod a = (b \<bullet> w) mod a"
  shows "(b \<bullet> (w -\<^sub>v v)) mod a = 0"
  by (metis (no_types, lifting) assms diff_zero dotprod_commute
      length_map length_upt less_eq_def order_vec.less_imp_le
      mods_with_vec vdiff_def)


subsection \<open>The Lexicographic Order on Vectors\<close>

abbreviation lex_less_than ("_/ <\<^sub>l\<^sub>e\<^sub>x _" [51, 51] 50)
  where
    "xs <\<^sub>l\<^sub>e\<^sub>x ys \<equiv> (xs, ys) \<in> lex less_than"

definition rlex (infix "<\<^sub>r\<^sub>l\<^sub>e\<^sub>x" 50)
  where
    "xs <\<^sub>r\<^sub>l\<^sub>e\<^sub>x ys \<longleftrightarrow> rev xs <\<^sub>l\<^sub>e\<^sub>x rev ys"

lemma rev_le [simp]:
  "rev xs \<le>\<^sub>v rev ys \<longleftrightarrow> xs \<le>\<^sub>v ys"
proof -
  { fix i assume i: "i < length ys" and [simp]: "length xs = length ys"
      and "\<forall>i < length ys. rev xs ! i \<le> rev ys ! i"
    then have "rev xs ! (length ys - i - 1) \<le> rev ys ! (length ys - i - 1)" by auto
    then have "xs ! i \<le> ys ! i" using i by (auto simp: rev_nth) }
  then show ?thesis by (auto simp: less_eq_def rev_nth)
qed

lemma rev_less [simp]:
  "rev xs <\<^sub>v rev ys \<longleftrightarrow> xs <\<^sub>v ys"
  by (simp add: less_def)

lemma less_imp_lex:
  assumes "xs <\<^sub>v ys" shows "xs <\<^sub>l\<^sub>e\<^sub>x ys"
proof -
  have "length ys = length xs" using assms by auto
  then show ?thesis using assms
    by (induct rule: list_induct2) (auto simp: less_Cons)
qed

lemma less_imp_rlex:
  assumes "xs <\<^sub>v ys" shows "xs <\<^sub>r\<^sub>l\<^sub>e\<^sub>x ys"
  using assms and less_imp_lex [of "rev xs" "rev ys"]
  by (simp add: rlex_def)

lemma lex_not_sym:
  assumes "xs <\<^sub>l\<^sub>e\<^sub>x ys"
  shows "\<not> ys <\<^sub>l\<^sub>e\<^sub>x xs"
proof
  assume "ys <\<^sub>l\<^sub>e\<^sub>x xs"
  then obtain i where "i < length xs" and "take i xs = take i ys"
    and "ys ! i < xs ! i" by (elim lex_take_index) auto
  moreover obtain j where "j < length xs" and "length ys = length xs" and "take j xs = take j ys"
    and "xs ! j < ys ! j" using assms by (elim lex_take_index) auto
  ultimately show False by (metis le_antisym nat_less_le nat_neq_iff nth_take)
qed

lemma rlex_not_sym:
  assumes "xs <\<^sub>r\<^sub>l\<^sub>e\<^sub>x ys"
  shows "\<not> ys <\<^sub>r\<^sub>l\<^sub>e\<^sub>x xs"
proof
  assume ass: "ys <\<^sub>r\<^sub>l\<^sub>e\<^sub>x xs"
  then obtain i where "i < length xs" and "take i xs = take i ys"
    and "ys ! i > xs ! i" using assms lex_not_sym rlex_def by blast
  moreover obtain j where "j < length xs" and "length ys = length xs" and "take j xs = take j ys"
    and "xs ! j > ys ! j" using assms rlex_def ass lex_not_sym by blast
  ultimately show False
    by (metis leD nat_less_le nat_neq_iff nth_take)
qed

lemma lex_trans:
  assumes "x <\<^sub>l\<^sub>e\<^sub>x y" and "y <\<^sub>l\<^sub>e\<^sub>x z"
  shows "x <\<^sub>l\<^sub>e\<^sub>x z"
proof -
  from assms obtain i and j where "length y = length x" and "length z = length x"
     and "i < length x" and "j < length x"
     and "take i x = take i y" and "take j y = take j z"
     and "x ! i < y ! i" and "y ! j < z ! j" by (fastforce elim!: lex_take_index)
  then show ?thesis
    apply (intro lexI [where i = "min i j"])
       apply (auto)
     apply (metis min.commute take_take)
    apply (auto simp: min_def)
     apply (metis dual_order.order_iff_strict dual_order.trans not_le nth_take)
    by (metis not_less nth_take)
qed

lemma rlex_trans:
  assumes "x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x y" and "y <\<^sub>r\<^sub>l\<^sub>e\<^sub>x z"
  shows "x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x z"
  using assms lex_trans rlex_def by blast

lemma lex_append_rightD:
  assumes "xs @ us <\<^sub>l\<^sub>e\<^sub>x ys @ vs" and "length xs = length ys"
    and "\<not> xs <\<^sub>l\<^sub>e\<^sub>x ys"
  shows "ys = xs \<and> us <\<^sub>l\<^sub>e\<^sub>x vs"
  using assms(2,1,3)
  by (induct xs ys rule: list_induct2) simp_all

lemma rlex_Cons:
  "x # xs <\<^sub>r\<^sub>l\<^sub>e\<^sub>x y # ys \<longleftrightarrow> xs <\<^sub>r\<^sub>l\<^sub>e\<^sub>x ys \<or> ys = xs \<and> x < y" (is "?A = ?B")
  by (cases "length ys = length xs")
    (auto simp: rlex_def intro: lex_append_rightI lex_append_leftI dest: lex_append_rightD lex_lengthD)

lemma rlex_irrefl:
  "\<not> x <\<^sub>r\<^sub>l\<^sub>e\<^sub>x x"
  by (induct x) (auto simp: rlex_def dest: lex_append_rightD)


subsection \<open>Code Equations\<close>

fun exists2
  where
    "exists2 d P [] [] \<longleftrightarrow> False"
  | "exists2 d P (x#xs) (y#ys) \<longleftrightarrow> P x y \<or> exists2 d P xs ys"
  | "exists2 d P _ _ \<longleftrightarrow> d"

lemma not_le_code [code_unfold]: "\<not> xs \<le>\<^sub>v ys \<longleftrightarrow> exists2 True (>) xs ys"
  by (induct "True" "(>) :: nat \<Rightarrow> nat \<Rightarrow> bool" xs ys rule: exists2.induct) (auto simp: le_Cons)

end
