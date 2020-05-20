section \<open>Lists\<close>

theory List_Extensions
imports "HOL-Library.Sublist"
begin

  declare remove1_idem[simp]

  lemma nth_append_simps[simp]:
    "i < length xs \<Longrightarrow> (xs @ ys) ! i = xs ! i"
    "i \<ge> length xs \<Longrightarrow> (xs @ ys) ! i = ys ! (i - length xs)"
    unfolding nth_append by simp+

  notation zip (infixr "||" 51)

  abbreviation "project A \<equiv> filter (\<lambda> a. a \<in> A)"
  abbreviation "select s w \<equiv> nths w s"

  lemma map_plus[simp]: "map (plus n) [i ..< j] = [i + n ..< j + n]"
  proof (induct n)
    case 0
    show ?case by simp
  next
    case (Suc n)
    have "map (plus (Suc n)) [i ..< j] = map (Suc \<circ> plus n) [i ..< j]" by simp
    also have "\<dots> = (map Suc \<circ> map (plus n)) [i ..< j]" by simp
    also have "\<dots> = map Suc (map (plus n) [i ..< j])" by simp
    also have "\<dots> = map Suc [i + n ..< j + n]" unfolding Suc by simp
    also have "\<dots> = [Suc (i + n) ..< Suc (j + n)]" unfolding map_Suc_upt by simp
    also have "\<dots> = [i + Suc n ..< j + Suc n]" by simp
    finally show ?case by this
  qed

  lemma singleton_list_lengthE[elim]:
    assumes "length xs = 1"
    obtains x
    where "xs = [x]"
  proof -
    have 0: "length xs = Suc 0" using assms by simp
    obtain y ys where 1: "xs = y # ys" "length ys = 0" using 0 Suc_length_conv by metis
    show ?thesis using that 1 by blast
  qed

  lemma singleton_hd_last: "length xs = 1 \<Longrightarrow> hd xs = last xs" by fastforce

  lemma set_subsetI[intro]:
    assumes "\<And> i. i < length xs \<Longrightarrow> xs ! i \<in> S"
    shows "set xs \<subseteq> S"
  proof
    fix x
    assume 0: "x \<in> set xs"
    obtain i where 1: "i < length xs" "x = xs ! i" using 0 unfolding in_set_conv_nth by blast
    show "x \<in> S" using assms(1) 1 by auto
  qed

  lemma hd_take[simp]:
    assumes "n \<noteq> 0" "xs \<noteq> []"
    shows "hd (take n xs) = hd xs"
  proof -
    have 1: "take n xs \<noteq> []" using assms by simp
    have 2: "0 < n" using assms by simp
    have "hd (take n xs) = take n xs ! 0" using hd_conv_nth[OF 1] by this
    also have "\<dots> = xs ! 0" using nth_take[OF 2] by this
    also have "\<dots> = hd xs" using hd_conv_nth[OF assms(2)] by simp
    finally show ?thesis by this
  qed
  lemma hd_drop[simp]:
    assumes "n < length xs"
    shows "hd (drop n xs) = xs ! n"
    using hd_drop_conv_nth assms by this
  lemma last_take[simp]:
    assumes "n < length xs"
    shows "last (take (Suc n) xs) = xs ! n"
  using assms
  proof (induct xs arbitrary: n)
    case (Nil)
    show ?case using Nil by simp
  next
    case (Cons x xs)
    show ?case using Cons by (auto) (metis Suc_less_eq Suc_pred)
  qed

  lemma split_list_first_unique:
    assumes "u\<^sub>1 @ [a] @ u\<^sub>2 = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set u\<^sub>1" "a \<notin> set v\<^sub>1"
    shows "u\<^sub>1 = v\<^sub>1"
  proof -
    obtain w where "u\<^sub>1 = v\<^sub>1 @ w \<and> w @ [a] @ u\<^sub>2 = [a] @ v\<^sub>2 \<or>
      u\<^sub>1 @ w = v\<^sub>1 \<and> [a] @ u\<^sub>2 = w @ [a] @ v\<^sub>2" using assms(1) append_eq_append_conv2 by blast
    thus ?thesis using assms(2, 3) by (auto) (metis hd_append2 list.sel(1) list.set_sel(1))+
  qed

end