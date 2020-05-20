section \<open>Augmented Type Syntax for Concrete Checker\<close>

theory Wasm_Checker_Types imports Wasm "HOL-Library.Sublist" begin

datatype ct =
    TAny
  | TSome t

datatype checker_type =
    TopType "ct list"
  | Type "t list"
  | Bot

definition to_ct_list :: "t list \<Rightarrow> ct list" where
  "to_ct_list ts = map TSome ts"

fun ct_eq :: "ct \<Rightarrow> ct \<Rightarrow> bool" where
  "ct_eq (TSome t) (TSome t') = (t = t')" 
| "ct_eq TAny _ = True"
| "ct_eq _ TAny = True"

definition ct_list_eq :: "ct list \<Rightarrow> ct list \<Rightarrow> bool" where
  "ct_list_eq ct1s ct2s = list_all2 ct_eq ct1s ct2s"

definition ct_prefix :: "ct list \<Rightarrow> ct list \<Rightarrow> bool" where
  "ct_prefix xs ys = (\<exists>as bs. ys = as@bs \<and> ct_list_eq as xs)"

definition ct_suffix :: "ct list \<Rightarrow> ct list \<Rightarrow> bool" where
  "ct_suffix xs ys = (\<exists>as bs. ys = as@bs \<and> ct_list_eq bs xs)"

lemma ct_eq_commute:
  assumes "ct_eq x y"
  shows "ct_eq y x"
  using assms
  by (metis ct_eq.elims(3) ct_eq.simps(1))

lemma ct_eq_flip: "ct_eq\<inverse>\<inverse> = ct_eq"
  using ct_eq_commute
  by fastforce

lemma ct_eq_common_tsome: "ct_eq x y = (\<exists>t. ct_eq x (TSome t) \<and> ct_eq (TSome t) y)"
  by (metis ct_eq.elims(3) ct_eq.simps(1))

lemma ct_list_eq_commute:
  assumes "ct_list_eq xs ys"
  shows "ct_list_eq ys xs"
  using assms ct_eq_commute List.List.list.rel_flip ct_eq_flip
  unfolding ct_list_eq_def
  by fastforce

lemma ct_list_eq_refl: "ct_list_eq xs xs"
  unfolding ct_list_eq_def
  by (metis ct_eq.elims(3) ct_eq.simps(1) list_all2_refl)

lemma ct_list_eq_length:
  assumes "ct_list_eq xs ys"
  shows "length xs = length ys"
  using assms list_all2_lengthD
  unfolding ct_list_eq_def
  by blast

lemma ct_list_eq_concat:
  assumes "ct_list_eq xs ys"
          "ct_list_eq xs' ys'"
  shows "ct_list_eq (xs@xs') (ys@ys')"
  using assms
  unfolding ct_list_eq_def
  by (simp add: list_all2_appendI)

lemma ct_list_eq_ts_conv_eq:
  "ct_list_eq (to_ct_list ts) (to_ct_list ts') = (ts = ts')"
  unfolding ct_list_eq_def to_ct_list_def
            list_all2_map1 list_all2_map2
            ct_eq.simps(1)
  by (simp add: list_all2_eq)

lemma ct_list_eq_exists: "\<exists>ys. ct_list_eq xs (to_ct_list ys)"
proof (induction xs)
  case Nil
  thus ?case
    unfolding ct_list_eq_def to_ct_list_def
    by (simp)
next
  case (Cons a xs)
  thus ?case
    unfolding ct_list_eq_def to_ct_list_def
    apply (cases a)
     apply (metis ct_eq.simps(3) ct_eq_commute list.rel_intros(2) list.simps(9))
    apply (metis ct_eq.simps(1) list.rel_intros(2) list.simps(9))
    done
qed

lemma ct_list_eq_common_tsome_list:
  "ct_list_eq xs ys = (\<exists>zs. ct_list_eq xs (to_ct_list zs) \<and> ct_list_eq (to_ct_list zs) ys)"
proof (induction ys arbitrary: xs)
  case Nil
  thus ?case
    unfolding ct_list_eq_def to_ct_list_def
    by simp
next
  case (Cons a ys)
  show ?case
  proof (safe)
    assume assms:"ct_list_eq xs (a # ys)"
    then obtain x' xs' where xs_def:"xs = x'#xs'"
      by (meson ct_list_eq_def list_all2_Cons2)
    then obtain zs where zs_def:"ct_eq x' a"
                                "ct_list_eq xs' (to_ct_list zs) \<and> ct_list_eq (to_ct_list zs) ys"
      using Cons[of xs'] assms list_all2_Cons
      unfolding ct_list_eq_def
      by fastforce
    obtain z where "ct_eq x' (TSome z)" "ct_eq (TSome z) a"
      using ct_eq_common_tsome[of x' a] zs_def(1)
      by fastforce
    hence "ct_list_eq (x'#xs') (to_ct_list (z#zs)) \<and> ct_list_eq (to_ct_list (z#zs)) (a # ys)"
      using zs_def(2) list_all2_Cons
      unfolding ct_list_eq_def to_ct_list_def
      by simp
    thus "\<exists>zs. ct_list_eq xs (to_ct_list zs) \<and> ct_list_eq (to_ct_list zs) (a # ys)"
      using xs_def
      by fastforce
  next
    fix zs
    assume assms:"ct_list_eq xs (to_ct_list zs)" "ct_list_eq (to_ct_list zs) (a # ys)"
    then obtain x' xs' z' zs' where "xs = x'#xs'"
                                    "zs = z'#zs'"
                                    "ct_list_eq xs' (to_ct_list zs')"
                                    "ct_list_eq (to_ct_list zs') (ys)"
      using list_all2_Cons2
      unfolding ct_list_eq_def to_ct_list_def list_all2_map1 list_all2_map2
      by (metis (no_types, lifting))
    thus "ct_list_eq xs (a # ys)"
      using assms Cons ct_list_eq_def to_ct_list_def ct_eq_common_tsome
      by (metis list.simps(9) list_all2_Cons)
  qed
qed

lemma ct_list_eq_cons_ct_list:
  assumes "ct_list_eq (to_ct_list as) (xs @ ys)"
  shows "\<exists>bs bs'. as = bs @ bs' \<and> ct_list_eq (to_ct_list bs) xs \<and> ct_list_eq (to_ct_list bs') ys"
  using assms
proof (induction xs arbitrary: as)
  case Nil
  thus ?case
    by (metis append_Nil ct_list_eq_ts_conv_eq list.simps(8) to_ct_list_def)
next
  case (Cons a xs)
  thus ?case
    unfolding ct_list_eq_def to_ct_list_def list_all2_map1
    by (meson list_all2_append2)
qed

lemma ct_list_eq_cons_ct_list1:
  assumes "ct_list_eq (to_ct_list as) (xs @ (to_ct_list ys))"
  shows "\<exists>bs. as = bs @ ys \<and> ct_list_eq (to_ct_list bs) xs"
  using ct_list_eq_cons_ct_list[OF assms] ct_list_eq_ts_conv_eq
  by fastforce

lemma ct_list_eq_shared:
  assumes "ct_list_eq xs (to_ct_list as)"
          "ct_list_eq ys (to_ct_list as)"
  shows "ct_list_eq xs ys"
  using assms ct_list_eq_def
  by (meson ct_list_eq_common_tsome_list ct_list_eq_commute)

lemma ct_list_eq_take:
  assumes "ct_list_eq xs ys"
  shows "ct_list_eq (take n xs) (take n ys)"
  using assms list_all2_takeI
  unfolding ct_list_eq_def
  by blast

lemma ct_prefixI [intro?]: 
  assumes "ys = as @ zs"
          "ct_list_eq as xs"
  shows "ct_prefix xs ys"
  using assms
  unfolding ct_prefix_def
  by blast

lemma ct_prefixE [elim?]:
  assumes "ct_prefix xs ys"
  obtains as zs where "ys = as @ zs" "ct_list_eq as xs"
  using assms
  unfolding ct_prefix_def
  by blast

lemma ct_prefix_snoc [simp]: "ct_prefix xs (ys @ [y]) = (ct_list_eq xs (ys@[y]) \<or> ct_prefix xs ys)"
proof (safe)
  assume "ct_prefix xs (ys @ [y])" "\<not> ct_prefix xs ys"
  thus "ct_list_eq xs (ys @ [y])"
    unfolding ct_prefix_def ct_list_eq_def
    by (metis butlast_append butlast_snoc ct_eq_flip list.rel_flip)
next
  assume "ct_list_eq xs (ys @ [y])"
  thus "ct_prefix xs (ys @ [y])"
    using ct_list_eq_commute ct_prefixI
    by fastforce
next
  assume "ct_prefix xs ys"
  thus "ct_prefix xs (ys @ [y])"
    using append_assoc
    unfolding ct_prefix_def
    by blast
qed

lemma ct_prefix_nil:"ct_prefix [] xs"
                    "\<not>ct_prefix (x # xs) []"
  by (simp_all add: ct_prefix_def ct_list_eq_def)

lemma Cons_ct_prefix_Cons[simp]: "ct_prefix (x # xs) (y # ys) = ((ct_eq x y) \<and> ct_prefix xs ys)"
proof (safe)
  assume "ct_prefix (x # xs) (y # ys)"
  thus "ct_eq x y"
    unfolding ct_prefix_def ct_list_eq_def
    by (metis ct_eq_commute hd_append2 list.sel(1) list.simps(3) list_all2_Cons2)
next
  assume "ct_prefix (x # xs) (y # ys)"
  thus "ct_prefix xs ys"
    unfolding ct_prefix_def ct_list_eq_def
    by (metis list.rel_distinct(1) list.sel(3) list_all2_Cons2 tl_append2)
next
  assume "ct_eq x y" "ct_prefix xs ys"
  thus "ct_prefix (x # xs) (y # ys)"
    unfolding ct_prefix_def ct_list_eq_def
    by (metis (full_types) append_Cons ct_list_eq_commute ct_list_eq_def list.rel_inject(2))
qed

lemma ct_prefix_code [code]:
  "ct_prefix [] xs = True"
  "ct_prefix (x # xs) [] = False"
  "ct_prefix (x # xs) (y # ys) = ((ct_eq x y) \<and> ct_prefix xs ys)"
  by (simp_all add: ct_prefix_nil)

lemma ct_suffix_to_ct_prefix [code]: "ct_suffix xs ys = ct_prefix (rev xs) (rev ys)"
  unfolding ct_suffix_def ct_prefix_def ct_list_eq_def
  by (metis list_all2_rev1 rev_append rev_rev_ident)

lemma inj_TSome: "inj TSome"
  by (meson ct.inject injI)

lemma to_ct_list_append:
  assumes "to_ct_list ts = as@bs"
  shows "\<exists>as'. to_ct_list as' = as"
        "\<exists>bs'. to_ct_list bs' = bs"
  using assms
proof (induct as arbitrary: ts)
  fix ts
  assume "to_ct_list ts = [] @ bs"
  thus "\<exists>as'. to_ct_list as' = []"
       "\<exists>bs'. to_ct_list bs' = bs"
    unfolding to_ct_list_def
    by auto
next
  case (Cons a as)
  fix ts
  assume local_assms:"to_ct_list ts = (a # as) @ bs"
  then obtain t' ts' where "ts = t'#ts'"
    unfolding to_ct_list_def
    by auto
  thus "\<exists>as'. to_ct_list as' = a # as"
       "\<exists>as'. to_ct_list as' = bs"
    using Cons local_assms
    unfolding to_ct_list_def
    apply simp_all
     apply (metis list.simps(9))
    apply blast
    done
qed

lemma ct_suffixI [intro?]: 
  assumes "ys = as @ zs"
          "ct_list_eq zs xs"
  shows "ct_suffix xs ys"
  using assms
  unfolding ct_suffix_def
  by blast

lemma ct_suffixE [elim?]:
  assumes "ct_suffix xs ys"
  obtains as zs where "ys = as @ zs" "ct_list_eq zs xs"
  using assms
  unfolding ct_suffix_def
  by blast

lemma ct_suffix_nil: "ct_suffix [] ts"
  unfolding ct_suffix_def
  using ct_list_eq_refl
  by auto

lemma ct_suffix_refl: "ct_suffix ts ts"
  unfolding ct_suffix_def
  using ct_list_eq_refl
  by auto

lemma ct_suffix_length:
  assumes "ct_suffix ts ts'"
  shows "length ts \<le> length ts'"
  using assms list_all2_lengthD
  unfolding ct_suffix_def ct_list_eq_def
  by fastforce

lemma ct_suffix_take:
  assumes "ct_suffix ts ts'"
  shows "ct_suffix ((take (length ts - n) ts)) ((take (length ts' - n) ts'))"
  using assms ct_list_eq_take append_eq_conv_conj
  unfolding ct_suffix_def
proof -
  assume "\<exists>as bs. ts' = as @ bs \<and> ct_list_eq bs ts"
  then obtain ccs :: "ct list" and ccsa :: "ct list" where
    f1: "ts' = ccs @ ccsa \<and> ct_list_eq ccsa ts"
    by moura
  then have f2: "length ccsa = length ts"
    by (meson ct_list_eq_length)
  have "\<And>n. ct_list_eq (take n ccsa) (take n ts)"
    using f1 by (meson ct_list_eq_take)
  then show "\<exists>cs csa. take (length ts' - n) ts' = cs @ csa \<and> ct_list_eq csa (take (length ts - n) ts)"
    using f2 f1 by auto
qed

lemma ct_suffix_ts_conv_suffix:
  "ct_suffix (to_ct_list ts) (to_ct_list ts') = suffix ts ts'"
proof safe
  assume "ct_suffix (to_ct_list ts) (to_ct_list ts')"
  then obtain as bs where "to_ct_list ts' = (to_ct_list as) @ (to_ct_list bs)"
                          "ct_list_eq (to_ct_list bs) (to_ct_list ts)"
    using to_ct_list_append
    unfolding ct_suffix_def
    by metis
  thus "suffix ts ts'"
    using ct_list_eq_ts_conv_eq
    unfolding ct_suffix_def to_ct_list_def suffix_def
    by (metis map_append)
next
  assume "suffix ts ts'"
  thus "ct_suffix (to_ct_list ts) (to_ct_list ts')"
    using ct_list_eq_ts_conv_eq
    unfolding ct_suffix_def to_ct_list_def suffix_def
    by (metis map_append)
qed

lemma ct_suffix_exists: "\<exists>ts_c. ct_suffix x1 (to_ct_list ts_c)"
  using ct_list_eq_commute ct_list_eq_exists ct_suffix_def
  by fastforce

lemma ct_suffix_ct_list_eq_exists:
  assumes "ct_suffix x1 x2"
  shows "\<exists>ts_c. ct_suffix x1 (to_ct_list ts_c) \<and> ct_list_eq (to_ct_list ts_c) x2"
proof -
  obtain as bs where x2_def:"x2 = as @ bs" "ct_list_eq x1 bs"
    using assms ct_list_eq_commute
    unfolding ct_suffix_def
    by blast
  then obtain ts_as ts_bs where "ct_list_eq as (to_ct_list ts_as)"
                                "ct_list_eq x1 (to_ct_list ts_bs)"
                                "ct_list_eq (to_ct_list ts_bs) bs"
    using ct_list_eq_common_tsome_list[of x1 bs] ct_list_eq_exists
    by fastforce
  thus ?thesis
    using x2_def ct_list_eq_commute
    unfolding ct_suffix_def to_ct_list_def
    by (metis ct_list_eq_def list_all2_appendI map_append)
qed

lemma ct_suffix_cons_ct_list:
  assumes "ct_suffix (xs@ys) (to_ct_list zs)"
  shows "\<exists>as bs. zs = as@bs \<and> ct_list_eq ys (to_ct_list bs) \<and> ct_suffix xs (to_ct_list as)"
proof -
  obtain as bs where "to_ct_list zs = (to_ct_list as) @ (to_ct_list bs)"
                     "ct_list_eq (to_ct_list bs) (xs @ ys)"
    using assms to_ct_list_append[of zs]
    unfolding ct_suffix_def
    by blast
  thus ?thesis
    using assms ct_list_eq_cons_ct_list[of bs xs ys]
    unfolding ct_suffix_def
  by (metis append.assoc ct_list_eq_commute ct_list_eq_ts_conv_eq map_append to_ct_list_def)
qed

lemma ct_suffix_cons_ct_list1:
  assumes "ct_suffix (xs@(to_ct_list ys)) (to_ct_list zs)"
  shows "\<exists>as. zs = as@ys \<and> ct_suffix xs (to_ct_list as)"
  using ct_suffix_cons_ct_list[OF assms] ct_list_eq_ts_conv_eq
  by fastforce

lemma ct_suffix_cons2:
  assumes "ct_suffix (xs) (ys@zs)"
          "length xs = length zs"
  shows "ct_list_eq xs zs"
  using assms
  by (metis append_eq_append_conv ct_list_eq_commute ct_list_eq_def ct_suffix_def list_all2_lengthD)
    
lemma ct_suffix_imp_ct_list_eq:
  assumes "ct_suffix xs ys"
  shows "ct_list_eq (drop (length ys - length xs) ys) xs"
  using assms ct_list_eq_def list_all2_lengthD
  unfolding ct_suffix_def
  by fastforce
  
lemma ct_suffix_extend_ct_list_eq:
  assumes "ct_suffix xs ys"
          "ct_list_eq xs' ys'"
  shows "ct_suffix (xs@xs') (ys@ys')"
  using assms
  unfolding ct_suffix_def ct_list_eq_def
  by (meson append.assoc ct_list_eq_commute ct_list_eq_def list_all2_appendI)

lemma ct_suffix_extend_any1:
  assumes "ct_suffix xs ys"
          "length xs < length ys"
  shows "ct_suffix (TAny#xs) ys"
proof -
  obtain as bs where ys_def:"ys = as@bs"
                            "ct_list_eq bs xs"
    using assms(1) ct_suffix_def
    by fastforce
  hence "length as > 0"
    using list_all2_lengthD assms(2)
    unfolding ct_list_eq_def
    by fastforce
  then obtain as' a where as_def:"as = as'@[a]"
    by (metis append_butlast_last_id length_greater_0_conv)
  hence "ct_list_eq (a#bs) (TAny#xs)"
    using ys_def
    by (meson ct_eq.simps(2) ct_list_eq_commute ct_list_eq_def list.rel_intros(2))
  thus ?thesis
    using as_def ys_def ct_suffix_def
    by fastforce
qed

lemma ct_suffix_singleton_any: "ct_suffix [TAny] [t]"
  using ct_suffix_extend_ct_list_eq[of "[]" "[]" "[TAny]" "[t]"] ct_suffix_nil
  by (simp add: ct_list_eq_def)

lemma ct_suffix_cons_it: "ct_suffix xs (xs'@xs)"
  using ct_list_eq_refl ct_suffix_def
  by blast

lemma ct_suffix_singleton:
  assumes "length cts > 0"
  shows "ct_suffix [TAny] cts"
proof -
  have "\<And>c. ct_prefix [TAny] [c]"
    using ct_suffix_singleton_any ct_suffix_to_ct_prefix by force
  then show ?thesis
    by (metis (no_types) Suc_leI append_butlast_last_id assms butlast.simps(2) ct_list_eq_commute
                         ct_prefix_nil(2) ct_prefix_snoc ct_suffix_def impossible_Cons length_Cons
                         list.size(3))
qed

lemma ct_suffix_less:
  assumes "ct_suffix (xs@xs') ys"
  shows "ct_suffix xs' ys"
  using assms
  unfolding ct_suffix_def
  by (metis append_eq_appendI ct_list_eq_def list_all2_append2)

lemma ct_suffix_unfold_one: "ct_suffix (xs@[x]) (ys@[y]) = ((ct_eq x y) \<and> ct_suffix xs ys)"
  using ct_prefix_code(3)
  by (simp add: ct_suffix_to_ct_prefix)

lemma ct_suffix_shared:
  assumes "ct_suffix cts (to_ct_list ts)"
          "ct_suffix cts' (to_ct_list ts)"
  shows "ct_suffix cts cts' \<or> ct_suffix cts' cts"
proof (cases "length cts > length cts'")
  case True
  obtain as bs where cts_def:"ts = as@bs"
                             "ct_list_eq cts (to_ct_list bs)"
    using assms(1) ct_suffix_def to_ct_list_def
    by (metis append_Nil ct_suffix_cons_ct_list)
  obtain as' bs' where cts'_def:"ts = as'@bs'"
                                "ct_list_eq cts' (to_ct_list bs')"
    using assms(2) ct_suffix_def to_ct_list_def
    by (metis append_Nil ct_suffix_cons_ct_list)
  obtain ct1s ct2s where "cts = ct1s@ct2s"
                         "length ct2s = length cts'"
    using True (* List.append_eq_conv_conj[of _ _ cts] *)
    by (metis add_diff_cancel_right' append_take_drop_id length_drop less_imp_le_nat nat_le_iff_add)
  show ?thesis
  proof -
    obtain tts :: "t list \<Rightarrow> ct list \<Rightarrow> ct list \<Rightarrow> t list" and ttsa :: "t list \<Rightarrow> ct list \<Rightarrow> ct list \<Rightarrow> t list" where
      "\<forall>x0 x1 x2. (\<exists>v3 v4. x0 = v3 @ v4 \<and> ct_list_eq x1 (to_ct_list v4) \<and> ct_suffix x2 (to_ct_list v3)) = (x0 = tts x0 x1 x2 @ ttsa x0 x1 x2 \<and> ct_list_eq x1 (to_ct_list (ttsa x0 x1 x2)) \<and> ct_suffix x2 (to_ct_list (tts x0 x1 x2)))"
      by moura
    then have f1: "as' @ bs' = tts (as' @ bs') ct2s ct1s @ ttsa (as' @ bs') ct2s ct1s \<and> ct_list_eq ct2s (to_ct_list (ttsa (as' @ bs') ct2s ct1s)) \<and> ct_suffix ct1s (to_ct_list (tts (as' @ bs') ct2s ct1s))"
      using assms(1) \<open>cts = ct1s @ ct2s\<close> cts'_def(1) ct_suffix_cons_ct_list by force
    then have "ct_list_eq cts' (to_ct_list (ttsa (as' @ bs') ct2s ct1s))"
      by (metis \<open>ct_suffix cts' (to_ct_list ts)\<close> \<open>length ct2s = length cts'\<close> cts'_def(1) ct_list_eq_length ct_suffix_cons2 map_append to_ct_list_def)
    then show ?thesis
      using f1 by (metis \<open>cts = ct1s @ ct2s\<close> ct_list_eq_shared ct_suffix_def)
  qed
next
  case False
  hence len:"length cts' \<ge> length cts"
    by linarith
  obtain as bs where cts_def:"ts = as@bs"
                             "ct_list_eq cts (to_ct_list bs)"
    using assms(1) ct_suffix_def to_ct_list_def
    by (metis append_Nil ct_suffix_cons_ct_list)
  obtain as' bs' where cts'_def:"ts = as'@bs'"
                                "ct_list_eq cts' (to_ct_list bs')"
    using assms(2) ct_suffix_def to_ct_list_def
    by (metis append_Nil ct_suffix_cons_ct_list)
  obtain ct1s ct2s where "cts' = ct1s@ct2s"
                         "length ct2s = length cts"
    using len (* List.append_eq_conv_conj[of _ _ cts] *)
    by (metis add_diff_cancel_right' append_take_drop_id length_drop nat_le_iff_add)
  show ?thesis
  proof -
    obtain tts :: "t list \<Rightarrow> ct list \<Rightarrow> ct list \<Rightarrow> t list" and ttsa :: "t list \<Rightarrow> ct list \<Rightarrow> ct list \<Rightarrow> t list" where
      "\<forall>x0 x1 x2. (\<exists>v3 v4. x0 = v3 @ v4 \<and> ct_list_eq x1 (to_ct_list v4) \<and> ct_suffix x2 (to_ct_list v3)) = (x0 = tts x0 x1 x2 @ ttsa x0 x1 x2 \<and> ct_list_eq x1 (to_ct_list (ttsa x0 x1 x2)) \<and> ct_suffix x2 (to_ct_list (tts x0 x1 x2)))"
      by moura
    then have f1: "as @ bs = tts (as @ bs) ct2s ct1s @ ttsa (as @ bs) ct2s ct1s \<and> ct_list_eq ct2s (to_ct_list (ttsa (as @ bs) ct2s ct1s)) \<and> ct_suffix ct1s (to_ct_list (tts (as @ bs) ct2s ct1s))"
      using assms(2) \<open>cts' = ct1s @ ct2s\<close> cts_def(1) ct_suffix_cons_ct_list by force
    then have "ct_list_eq cts (to_ct_list (ttsa (as @ bs) ct2s ct1s))"
      by (metis \<open>ct_suffix cts (to_ct_list ts)\<close> \<open>length ct2s = length cts\<close> cts_def(1) ct_list_eq_length ct_suffix_cons2 map_append to_ct_list_def)
    then show ?thesis
      using f1 by (metis \<open>cts' = ct1s @ ct2s\<close> ct_list_eq_shared ct_suffix_def)
  qed
qed

fun checker_type_suffix::"checker_type \<Rightarrow> checker_type \<Rightarrow> bool" where
  "checker_type_suffix (Type ts) (Type ts') = suffix ts ts'"
| "checker_type_suffix (Type ts) (TopType cts) = ct_suffix (to_ct_list ts) cts"
| "checker_type_suffix (TopType cts) (Type ts) = ct_suffix cts (to_ct_list ts)"
| "checker_type_suffix _ _ = False"

fun consume :: "checker_type \<Rightarrow> ct list \<Rightarrow> checker_type" where
  "consume (Type ts) cons = (if ct_suffix cons (to_ct_list ts)
                               then Type (take (length ts - length cons) ts)
                               else Bot)"
| "consume (TopType cts) cons = (if ct_suffix cons cts
                                  then TopType (take (length cts - length cons) cts)
                                  else (if ct_suffix cts cons
                                          then TopType []
                                          else Bot))"
| "consume _ _ = Bot"

fun produce :: "checker_type \<Rightarrow> checker_type \<Rightarrow> checker_type" where
  "produce (TopType ts) (Type ts') = TopType (ts@(to_ct_list ts'))"
| "produce (Type ts) (Type ts') = Type (ts@ts')"
| "produce (Type ts') (TopType ts) = TopType ts"
| "produce (TopType ts') (TopType ts) = TopType ts"
| "produce _ _ = Bot"

fun type_update :: "checker_type \<Rightarrow> ct list \<Rightarrow> checker_type \<Rightarrow> checker_type" where
  "type_update curr_type cons prods = produce (consume curr_type cons) prods"

fun select_return_top :: "[ct list] \<Rightarrow> ct \<Rightarrow> ct \<Rightarrow> checker_type" where
  "select_return_top ts ct1 TAny = TopType ((take (length ts - 3) ts) @ [ct1])"
| "select_return_top ts TAny ct2 = TopType ((take (length ts - 3) ts) @ [ct2])"
| "select_return_top ts (TSome t1) (TSome t2) = (if (t1 = t2)
                                                   then (TopType ((take (length ts - 3) ts) @ [TSome t1]))
                                                   else Bot)"

fun type_update_select :: "checker_type \<Rightarrow> checker_type" where
  "type_update_select (Type ts) = (if (length ts \<ge> 3 \<and> (ts!(length ts-2)) = (ts!(length ts-3)))
                                    then consume (Type ts) [TAny, TSome T_i32]
                                    else Bot)"
| "type_update_select (TopType ts) = (case length ts of
                                        0 \<Rightarrow> TopType [TAny]
                                      | Suc 0 \<Rightarrow> type_update (TopType ts) [TSome T_i32] (TopType [TAny])
                                      | Suc (Suc 0) \<Rightarrow> consume (TopType ts) [TSome T_i32]
                                      | _  \<Rightarrow> type_update (TopType ts) [TAny, TAny, TSome T_i32]
                                                          (select_return_top ts (ts!(length ts-2)) (ts!(length ts-3))))"
| "type_update_select _ = Bot"

fun c_types_agree :: "checker_type \<Rightarrow> t list \<Rightarrow> bool" where
  "c_types_agree (Type ts) ts' = (ts = ts')"
| "c_types_agree (TopType ts) ts' = ct_suffix ts (to_ct_list ts')"
| "c_types_agree Bot _ = False"

lemma consume_type:
  assumes "consume (Type ts) ts' = c_t"
          "c_t \<noteq> Bot"
  shows "\<exists>ts''. ct_list_eq (to_ct_list ts) ((to_ct_list ts'')@ts') \<and> c_t = Type ts''"
proof -
  {
    assume a1: "(if ct_suffix ts' (map TSome ts) then Type (take (length ts - length ts') ts) else Bot) = c_t"
    assume a2: "c_t \<noteq> Bot"
    obtain ccs :: "ct list \<Rightarrow> ct list \<Rightarrow> ct list" and ccsa :: "ct list \<Rightarrow> ct list \<Rightarrow> ct list" where
      f3: "\<forall>cs csa. \<not> ct_suffix cs csa \<or> csa = ccs cs csa @ ccsa cs csa \<and> ct_list_eq (ccsa cs csa) cs"
      using ct_suffixE by moura
    have f4: "ct_suffix ts' (map TSome ts)"
      using a2 a1 by metis
    then have f5: "ct_list_eq (ccsa ts' (map TSome ts)) ts'"
      using f3 by blast
    have f6: "take (length (map TSome ts) - length (ccsa ts' (map TSome ts))) (map TSome ts) @ ccsa ts' (map TSome ts) = map TSome ts"
      using f4 f3 by (metis (full_types) suffixI suffix_take)
    have "\<And>cs. ct_list_eq (cs @ ccsa ts' (map TSome ts)) (cs @ ts')"
      using f5 ct_list_eq_concat ct_list_eq_refl by blast
    then have "\<exists>tsa. ct_list_eq (map TSome ts) (map TSome tsa @ ts') \<and> c_t = Type tsa"
      using f6 f5 f4 a1 by (metis (no_types) ct_list_eq_length length_map take_map)
  }
  thus ?thesis
    using assms to_ct_list_def
    by simp
qed

lemma consume_top_geq:
  assumes "consume (TopType ts) ts' = c_t"
          "length ts \<ge> length ts'"
          "c_t \<noteq> Bot"
  shows "(\<exists>as bs. ts = as@bs \<and> ct_list_eq bs ts' \<and> c_t = TopType as)"
proof -
  consider (1) "ct_suffix ts' ts"
         | (2) "\<not>ct_suffix ts' ts" "ct_suffix ts ts'"
         | (3) "\<not>ct_suffix ts' ts" "\<not>ct_suffix ts ts'"
    by blast
  thus ?thesis
  proof (cases)
    case 1
    hence "TopType (take (length ts - length ts') ts) = c_t"
      using assms
      by simp
    thus ?thesis
      using assms(2) 1 ct_list_eq_def
      unfolding ct_suffix_def
      by (metis (no_types, lifting) append_eq_append_conv append_take_drop_id diff_diff_cancel length_drop list_all2_lengthD)
  next
    case 2
    thus ?thesis
      using assms append_eq_append_conv ct_list_eq_commute
      unfolding ct_suffix_def
      by (metis append.left_neutral ct_suffix_def ct_suffix_length le_antisym)
  next
    case 3
    thus ?thesis
      using assms
      by auto
  qed
qed

lemma consume_top_leq:
  assumes "consume (TopType ts) ts' = c_t"
          "length ts \<le> length ts'"
          "c_t \<noteq> Bot"
  shows "c_t = TopType []"
  using assms append_eq_conv_conj
  by fastforce

lemma consume_type_type:
  assumes "consume xs cons = (Type t_int)"
  shows "\<exists>tn. xs = Type tn"
  using assms
  apply (cases xs)
    apply simp_all
  apply (metis checker_type.distinct(1) checker_type.distinct(5))
  done

lemma produce_type_type:
  assumes "produce xs cons = (Type tm)"
  shows "\<exists>tn. xs = Type tn"
  apply (cases xs; cases cons)
  using assms
          apply simp_all
  done

lemma consume_weaken_type:
  assumes "consume (Type tn) cons = (Type t_int)"
  shows "consume (Type (ts@tn)) cons = (Type (ts@t_int))"
proof -
  obtain ts' where "ct_list_eq (to_ct_list tn) (to_ct_list ts' @ cons) \<and> Type t_int = Type ts'"
    using consume_type[OF assms]
    by blast
  have cond:"ct_suffix cons (to_ct_list tn)"
    using assms
    by (simp, metis checker_type.distinct(5))
  hence res:"t_int = take (length tn - length cons) tn"
    using assms
    by simp
  have "ct_suffix cons (to_ct_list (ts@tn))"
    using cond
    unfolding to_ct_list_def
    by (metis append_assoc ct_suffix_def map_append)
  moreover
  have "ts@t_int = take (length (ts@tn) - length cons) (ts@tn)"
    using res take_append cond ct_suffix_length to_ct_list_def
    by fastforce
  ultimately
  show ?thesis
    by simp
qed
    
lemma produce_weaken_type:
  assumes "produce (Type tn) cons = (Type tm)"
  shows "produce (Type (ts@tn)) cons = (Type (ts@tm))"
  using assms
  by (cases cons, simp_all)

lemma produce_nil: "produce ts (Type []) = ts"
  using to_ct_list_def
  by (cases ts, simp_all)

lemma c_types_agree_id: "c_types_agree (Type ts) ts"
  by simp

lemma c_types_agree_top1: "c_types_agree (TopType []) ts"
  using ct_suffix_ts_conv_suffix to_ct_list_def
  by (simp add: ct_suffix_nil)

lemma c_types_agree_top2:
  assumes "ct_list_eq ts (to_ct_list ts'')"
  shows "c_types_agree (TopType ts) (ts'@ts'')"
  using assms ct_list_eq_commute ct_suffix_def to_ct_list_def
  by auto

lemma c_types_agree_imp_ct_list_eq:
  assumes "c_types_agree (TopType cts) ts"
  shows "\<exists>ts' ts''. (ts = ts'@ts'') \<and> ct_list_eq cts (to_ct_list ts'')"
  using assms ct_suffix_def to_ct_list_def
  by (simp, metis ct_list_eq_commute ct_list_eq_ts_conv_eq ct_suffix_ts_conv_suffix suffixE
                  to_ct_list_append(2))

lemma c_types_agree_not_bot_exists:
  assumes "ts \<noteq> Bot"
  shows "\<exists>ts_c. c_types_agree ts ts_c"
  using assms ct_suffix_exists
  by (cases ts, simp_all)

lemma consume_c_types_agree:
  assumes "consume (Type ts) cts = (Type ts')"
          "c_types_agree ctn ts"
  shows "\<exists>c_t'. consume ctn cts = c_t' \<and> c_types_agree c_t' ts'"
  using assms
proof (cases ctn)
  case (TopType x1)
  have 1:"ct_suffix cts (to_ct_list ts)"
    using assms
    by (simp, metis checker_type.distinct(5))
  hence "ct_suffix cts x1 \<or> ct_suffix x1 cts"
    using TopType 1 assms(2) ct_suffix_shared
    by simp
  thus ?thesis
  proof (rule disjE)
    assume local_assms:"ct_suffix cts x1"
    hence 2:"consume (TopType x1) cts = TopType (take (length x1 - length cts) x1)"
      by simp
    have "(take (length ts - length cts) ts) = ts'"
      using assms 1
      by simp
    hence "c_types_agree (TopType (take (length x1 - length cts) x1)) ts'"
      using 2 assms local_assms TopType ct_suffix_take
      by (simp, metis length_map take_map to_ct_list_def)
    thus ?thesis
      using 2 TopType
      by simp
  next
    assume local_assms:"ct_suffix x1 cts"
    hence 3:"consume (TopType x1) cts = TopType []"
      by (simp add: ct_suffix_length)
    thus ?thesis
      using TopType c_types_agree_top1
      by blast
  qed
qed simp_all


lemma type_update_type:
  assumes "type_update (Type ts) (to_ct_list cons) prods = ts'"
          "ts' \<noteq> Bot"
        shows "(ts' = prods \<and> (\<exists>ts_c. prods = (TopType ts_c)))
               \<or> (\<exists>ts_a ts_b. prods = Type ts_a \<and> ts = ts_b@cons \<and> ts' = Type (ts_b@ts_a))"
  using assms
  apply (cases prods)
    apply simp_all
   apply (metis (full_types) produce.simps(3) produce.simps(7))
  using ct_suffix_ts_conv_suffix suffix_take to_ct_list_def
  apply fastforce
  done

lemma type_update_empty: "type_update ts cons (Type []) = consume ts cons"
  using produce_nil
  by simp

lemma type_update_top_top:
  assumes "type_update (TopType ts) (to_ct_list cons) (Type prods) = (TopType ts')"
          "c_types_agree (TopType ts') t_ag"
  shows "ct_suffix (to_ct_list prods) ts'"
        "\<exists>t_ag'. t_ag = t_ag'@prods \<and> c_types_agree (TopType ts) (t_ag'@cons)"
proof -
  consider (1) "ct_suffix (to_ct_list cons) ts"
         | (2) "\<not>ct_suffix (to_ct_list cons) ts" "ct_suffix ts (to_ct_list cons)"
         | (3) "\<not>ct_suffix (to_ct_list cons) ts" "\<not>ct_suffix ts (to_ct_list cons)"
    by blast
  hence "ct_suffix (to_ct_list prods) ts' \<and> (\<exists>t_ag'. t_ag = t_ag'@prods \<and> c_types_agree (TopType ts) (t_ag'@cons))"
  proof (cases)
    case 1
    hence "ts' = (take (length ts - length cons) ts) @ to_ct_list prods"
      using assms(1) to_ct_list_def
      by simp
    moreover
    then obtain t_ag' where "t_ag = t_ag' @ prods"
                            "ct_suffix (take (length ts - length cons) ts) (to_ct_list t_ag')"
      using assms(2) ct_suffix_cons_ct_list1
      unfolding c_types_agree.simps
      by blast
    moreover
    hence "ct_suffix ts (to_ct_list (t_ag'@cons))"
      using 1 ct_suffix_imp_ct_list_eq ct_suffix_extend_ct_list_eq to_ct_list_def
      by fastforce
    ultimately
    show ?thesis
      using c_types_agree.simps(2) ct_list_eq_ts_conv_eq ct_suffix_def
      by auto
  next
    case 2
    thus ?thesis
      using assms
      by (metis append.assoc c_types_agree.simps(2) checker_type.inject(1) consume.simps(2)
                ct_list_eq_ts_conv_eq ct_suffix_cons_ct_list ct_suffix_def map_append
                produce.simps(1) to_ct_list_def type_update.simps)
  next
    case 3
    thus ?thesis
      using assms
      by simp
  qed
  thus "ct_suffix (to_ct_list prods) ts'"
        "\<exists>t_ag'. t_ag = t_ag'@prods \<and> c_types_agree (TopType ts) (t_ag'@cons)"
  by simp_all
qed

lemma type_update_select_length0:
  assumes "type_update_select (TopType cts) = tm"
          "length cts = 0"
          "tm \<noteq> Bot"
  shows "tm = TopType [TAny]"
  using assms
  by simp

lemma type_update_select_length1:
  assumes "type_update_select (TopType cts) = tm"
          "length cts = 1"
          "tm \<noteq> Bot"
  shows "ct_list_eq cts [TSome T_i32]"
        "tm = TopType [TAny]"
proof -
  have 1:"type_update (TopType cts) [TSome T_i32] (TopType [TAny]) = tm"
    using assms(1,2)
    by simp
  hence "ct_suffix cts [TSome T_i32] \<or> ct_suffix [TSome T_i32] cts"
    using assms(3)
    by (metis consume.simps(2) produce.simps(7) type_update.simps)
  thus "ct_list_eq cts [TSome T_i32]"
    using assms(2,3) ct_suffix_imp_ct_list_eq
    by (metis One_nat_def Suc_length_conv ct_list_eq_commute diff_Suc_1 drop_0 list.size(3))
  show "tm = TopType [TAny]"
    using 1 assms(3) consume_top_leq
    by (metis One_nat_def assms(2) diff_Suc_1 diff_is_0_eq length_Cons list.size(3)
              produce.simps(4,7) type_update.simps)
qed


lemma type_update_select_length2:
  assumes "type_update_select (TopType cts) = tm"
          "length cts = 2"
          "tm \<noteq> Bot"
  shows "\<exists>t1 t2. cts = [t1, t2] \<and> ct_eq t2 (TSome T_i32) \<and> tm = TopType [t1]"
proof -
  obtain x y where cts_def:"cts = [x,y]"
    using assms(2) List.length_Suc_conv[of cts "Suc 0"]
    by (metis length_0_conv length_Suc_conv numeral_2_eq_2)
  moreover
  hence "consume (TopType [x,y]) [TSome T_i32] = tm"
    using assms(1,2)
    by simp
  moreover
  hence "ct_suffix [x,y] [TSome T_i32] \<or> ct_suffix [TSome T_i32] [x,y]"
    using assms(3)
    by (metis consume.simps(2))
  hence "ct_suffix [TSome T_i32] ([x]@[y])"
    using assms(2) ct_suffix_length
    by fastforce
  moreover
  hence "ct_eq y (TSome T_i32)"
    by (metis ct_eq_commute ct_list_eq_def ct_suffix_cons2 list.rel_sel list.sel(1) list.simps(3)
              list.size(4))
  ultimately
  show ?thesis
    by auto
qed

lemma type_update_select_length3:
  assumes "type_update_select (TopType cts) = (TopType ctm)"
          "length cts \<ge> 3"
  shows "\<exists>cts' ct1 ct2 ct3. cts = cts'@[ct1, ct2, ct3] \<and> ct_eq ct3 (TSome T_i32)"
proof -
  obtain cts' cts'' where cts_def:"cts = cts'@ cts''" "length cts'' = 3"
    using assms(2)
    by (metis append_take_drop_id diff_diff_cancel length_drop)
  then obtain ct1 cts''2 where "cts'' = ct1#cts''2" "length cts''2 = Suc (Suc 0)"
    using List.length_Suc_conv[of cts' "Suc (Suc 0)"]
    by (metis length_Suc_conv numeral_3_eq_3)
  then obtain ct2 ct3 where "cts'' = [ct1,ct2,ct3]"
    using List.length_Suc_conv[of cts''2 "Suc 0"]
    by (metis length_0_conv length_Suc_conv)
  hence cts_def2:"cts = cts'@ [ct1,ct2,ct3]"
    using cts_def
    by simp
  obtain nat where "length cts = Suc (Suc (Suc nat))"
    using assms(2)
    by (simp add: cts_def)
  hence "(type_update (TopType cts) [TAny, TAny, TSome T_i32] (select_return_top cts (cts ! (length cts - 2)) (cts ! (length cts - 3)))) = TopType ctm"
    using assms
    by simp
  then obtain c_mid where "consume (TopType cts) [TAny, TAny, TSome T_i32] = TopType c_mid"
    by (metis consume.simps(2) produce.simps(6) type_update.simps)
  hence "ct_suffix [TAny, TAny, TSome T_i32] (cts'@ [ct1,ct2,ct3])"
    using assms(2) consume_top_geq cts_def2
    by (metis checker_type.distinct(3) ct_suffix_def length_Cons list.size(3) numeral_3_eq_3)
  hence "ct_eq ct3 (TSome T_i32)"
    using ct_suffix_def ct_list_eq_def
    by (simp, metis append_eq_append_conv length_Cons list_all2_Cons list_all2_lengthD)
  thus ?thesis
    using cts_def2
    by simp
qed

lemma type_update_select_type_length3:
  assumes "type_update_select (Type tn) = (Type tm)"
  shows "\<exists>t ts'. tn = ts'@[t, t, T_i32]"
proof -
  have tn_cond:"(length tn \<ge> 3 \<and> (tn!(length tn-2)) = (tn!(length tn-3)))"
    using assms
    by (simp, metis checker_type.distinct(5))
  hence tm_def:"consume (Type tn) [TAny, TSome T_i32] = Type tm"
    using assms
    by simp
  obtain tn' tn'' where tn_split:"tn = tn'@tn''"
                                 "length tn'' = 3"
    using assms tn_cond
    by (metis append_take_drop_id diff_diff_cancel length_drop)
  then obtain t1 tn''2 where "tn'' = t1#tn''2" "length tn''2 = Suc (Suc 0)"
    by (metis length_Suc_conv numeral_3_eq_3)
  then obtain t2 t3 where tn''_def:"tn'' = [t1,t2,t3]"
    using List.length_Suc_conv[of tn''2 "Suc 0"]
    by (metis length_0_conv length_Suc_conv)
  hence tn_def:"tn = tn'@ [t1,t2,t3]"
    using tn_split
    by simp
  hence t1_t2_eq:"t1 = t2"
    using tn_cond
    by (metis (no_types, lifting) Suc_diff_Suc Suc_eq_plus1_left Suc_lessD tn''_def
                                  add_diff_cancel_right' diff_is_0_eq length_append neq0_conv
                                  not_less_eq_eq nth_Cons_0 nth_Cons_numeral
                                  nth_append numeral_2_eq_2 numeral_3_eq_3 numeral_One tn_split(2)
                                  zero_less_diff)
  have "ct_suffix [TAny, TSome T_i32] (to_ct_list (tn' @ [t1, t2, t3]))"
    using tn_def tm_def
    by (simp, metis checker_type.distinct(5))
  hence "t3 = T_i32"
    using ct_suffix_unfold_one[of "[TAny]" "TSome T_i32" "to_ct_list (tn' @ [t1, t2])" "TSome t3"]
          ct_eq.simps(1)
    unfolding to_ct_list_def
    by simp
  thus ?thesis
    using t1_t2_eq tn_def
    by simp
qed

lemma select_return_top_exists:
  assumes "select_return_top cts c1 c2 = ctm"
          "ctm \<noteq> Bot"
  shows "\<exists>xs. ctm = TopType xs"
  using assms
  by (meson select_return_top.elims)

lemma type_update_select_top_exists:
  assumes "type_update_select xs = (TopType tm)"
  shows "\<exists>tn. xs = TopType tn"
  using assms
proof (cases xs)
  case (Type x2)
  thus ?thesis
    using assms
    by (simp, metis checker_type.distinct(1) checker_type.distinct(3) consume.simps(1))
qed simp_all

lemma type_update_select_conv_select_return_top:
  assumes "ct_suffix [TSome T_i32] cts"
          "length cts \<ge> 3"
  shows "type_update_select (TopType cts) = (select_return_top cts (cts!(length cts-2)) (cts!(length cts-3)))"
proof -
  obtain nat where nat_def:"length cts = Suc (Suc (Suc nat))"
    using assms(2)
    by (metis add_eq_if diff_Suc_1 le_Suc_ex numeral_3_eq_3 nat.distinct(2))
  have "ct_suffix [TAny, TAny, TSome T_i32] cts"
    using assms ct_suffix_extend_any1
    by simp
  then obtain cts' where "consume (TopType cts) [TAny, TAny, TSome T_i32] = TopType cts'"
    by simp
  thus ?thesis
    using nat_def select_return_top_exists
    apply (cases "select_return_top cts (cts ! Suc nat) (cts ! nat)")
      apply simp_all
    apply blast
    done
qed

lemma select_return_top_ct_eq:
  assumes "select_return_top cts c1 c2 = TopType ctm"
          "length cts \<ge> 3"
          "c_types_agree (TopType ctm) cm"
  shows "\<exists>c' cm'. cm = cm'@[c']
                  \<and> ct_suffix (take (length cts - 3) cts) (to_ct_list cm')
                  \<and> ct_eq c1 (TSome c')
                  \<and> ct_eq c2 (TSome c')"
proof (cases c1)
  case TAny
  note outer_TAny = TAny
  show ?thesis
  proof (cases c2)
    case TAny
    hence "take (length cts - 3) cts @ [TAny] = ctm"
      using outer_TAny  assms ct_suffix_cons_ct_list
      by simp
    then obtain cm' c where "cm = cm' @ [c]"
                            "ct_suffix (take (length cts - 3) cts) (to_ct_list cm')"
      using ct_suffix_cons_ct_list[of "take (length cts - 3) cts" "[TAny]"]
            assms(3) c_types_agree.simps(2)[of ctm cm]
      unfolding ct_list_eq_def to_ct_list_def
      by (metis Suc_leI impossible_Cons length_Cons length_map list.exhaust list.size(3)
                list_all2_conv_all_nth zero_less_Suc)
    thus ?thesis
      using TAny outer_TAny ct_eq.simps(2)
      by blast
  next
    case (TSome x2)
    hence "take (length cts - 3) cts @ [TSome x2] = ctm"
      using outer_TAny assms ct_suffix_cons_ct_list
      by simp
    then obtain cm' where "cm = cm' @ [x2]"
                          "ct_suffix (take (length cts - 3) cts) (to_ct_list cm')"
      using ct_suffix_cons_ct_list[of "take (length cts - 3) cts" "[TSome x2]"]
            assms(3) c_types_agree.simps(2)[of ctm cm] ct_list_eq_ts_conv_eq
      unfolding ct_list_eq_def to_ct_list_def
      by (metis (no_types, hide_lams) list.simps(8,9))
    thus ?thesis
      using TSome outer_TAny
      by simp
  qed
next
  case (TSome x2)
  note outer_TSome = TSome
  show ?thesis
  proof (cases c2)
    case TAny
    hence "take (length cts - 3) cts @ [TSome x2] = ctm"
      using TSome assms ct_suffix_cons_ct_list
      by simp
    then obtain cm' where "cm = cm' @ [x2]"
                          "ct_suffix (take (length cts - 3) cts) (to_ct_list cm')"
      using ct_suffix_cons_ct_list[of "take (length cts - 3) cts" "[TSome x2]"]
            assms(3) c_types_agree.simps(2)[of ctm cm] ct_list_eq_ts_conv_eq
      unfolding ct_list_eq_def to_ct_list_def
      by (metis (no_types, hide_lams) list.simps(8,9))
    thus ?thesis
      using TSome TAny
      by simp
  next
    case (TSome x3)
    hence x_eq:"x2 = x3"
      using outer_TSome assms ct_suffix_cons_ct_list
      by (metis checker_type.distinct(3) select_return_top.simps(3))
    hence "take (length cts - 3) cts @ [TSome x2] = ctm"
      using TSome outer_TSome assms ct_suffix_cons_ct_list
      by (metis checker_type.inject(1) select_return_top.simps(3))
    then obtain cm' where "cm = cm' @ [x2]"
                          "ct_suffix (take (length cts - 3) cts) (to_ct_list cm')"
      using ct_suffix_cons_ct_list[of "take (length cts - 3) cts" "[TSome x2]"]
            assms(3) c_types_agree.simps(2)[of ctm cm] ct_list_eq_ts_conv_eq
      unfolding ct_list_eq_def to_ct_list_def
      by (metis (no_types, hide_lams) list.simps(8,9))
    thus ?thesis
      using TSome outer_TSome x_eq
      by simp
  qed
qed

end