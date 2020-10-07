(*  Title:      ListInf_Prefix.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Prefices on finite and infinite lists\<close>

theory ListInf_Prefix
imports "HOL-Library.Sublist" ListInf
begin

subsection \<open>Additional list prefix results\<close>

lemma prefix_eq_prefix_take_ex: "prefix xs ys = (\<exists>n. ys \<down> n = xs)"
apply (unfold prefix_def, safe)
apply (rule_tac x="length xs" in exI, simp)
apply (rule_tac x="ys \<up> n" in exI, simp)
done

lemma prefix_take_eq_prefix_take_ex: "(ys \<down> (length xs) = xs) = (\<exists>n. ys \<down> n = xs)"
by (fastforce simp: min_def)

lemma prefix_eq_prefix_take: "prefix xs ys = (ys \<down> (length xs) = xs)"
by (simp only: prefix_eq_prefix_take_ex prefix_take_eq_prefix_take_ex)

lemma strict_prefix_take_eq_strict_prefix_take_ex: "
  (ys \<down> (length xs) = xs \<and> xs \<noteq> ys) =
  ((\<exists>n. ys \<down> n = xs) \<and> xs \<noteq> ys)"
by (simp add: prefix_take_eq_prefix_take_ex)

lemma strict_prefix_eq_strict_prefix_take_ex: "strict_prefix xs ys = ((\<exists>n. ys \<down> n = xs) \<and> xs \<noteq> ys)"
by (simp add: strict_prefix_def prefix_eq_prefix_take_ex)
lemma strict_prefix_eq_strict_prefix_take: "strict_prefix xs ys = (ys \<down> (length xs) = xs \<and> xs \<noteq> ys)"
by (simp only: strict_prefix_eq_strict_prefix_take_ex strict_prefix_take_eq_strict_prefix_take_ex)



lemma take_imp_prefix: "prefix (xs \<down> n) xs"
by (rule take_is_prefix)

lemma eq_imp_prefix: "xs = (ys::'a list) \<Longrightarrow> prefix xs ys"
by simp

lemma le_take_imp_prefix: "a \<le> b \<Longrightarrow> prefix (xs \<down> a) (xs \<down> b)"
by (fastforce simp: prefix_eq_prefix_take_ex min_def)

lemma take_prefix_imp_le: "
  \<lbrakk> a \<le> length xs; prefix (xs \<down> a) (xs \<down> b) \<rbrakk> \<Longrightarrow> a \<le> b"
by (drule prefix_length_le, simp)

lemma take_prefixeq_le_conv: "
  a \<le> length xs \<Longrightarrow> prefix (xs \<down> a) (xs \<down> b) = (a \<le> b)"
apply (rule iffI)
 apply (rule take_prefix_imp_le, assumption+)
apply (rule le_take_imp_prefix, assumption+)
done
lemma append_imp_prefix[simp, intro]: "prefix a (a @ b)"
by (unfold prefix_def, blast)

lemma prefix_imp_take_eq: "
  \<lbrakk> n \<le> length xs; prefix xs ys \<rbrakk> \<Longrightarrow> xs \<down> n = ys \<down> n"
by (clarsimp simp: prefix_def)

lemma prefix_length_le_eq_conv: "(prefix xs ys \<and> length ys \<le> length xs) = (xs = ys)"
apply (rule iffI)
 apply (erule conjE)
 apply (frule prefix_length_le)
 apply (simp add: prefix_eq_prefix_take)
apply simp
done

lemma take_length_prefix_conv: "
  length xs \<le> length ys \<Longrightarrow> prefix (ys \<down> length xs) xs = prefix xs ys"
by (fastforce simp: prefix_eq_prefix_take)

lemma append_eq_imp_take: "
  \<lbrakk> k \<le> length xs; length r1 = k; r1 @ r2 = xs \<rbrakk> \<Longrightarrow> r1 = xs \<down> k"
by fastforce

lemma take_the_conv: "
  xs \<down> k = (if length xs \<le> k then xs else (THE r. length r = k \<and> (\<exists>r2. r @ r2 = xs)))"
apply (clarsimp simp: linorder_not_le)
apply (rule the1I2)
 apply (simp add: Ex1_def)
 apply (rule_tac x="xs \<down> k" in exI)
 apply (intro conjI)
   apply (simp add: min_eqR)
  apply (rule_tac x="xs \<up> k" in exI, simp)
 apply fastforce
apply fastforce
done


lemma prefix_refl: "prefix xs (xs::'a list)"
by (rule prefix_order.order_refl)

lemma prefix_trans: "\<lbrakk> prefix xs ys; prefix (ys::'a list) zs \<rbrakk> \<Longrightarrow> prefix xs zs"
by (rule prefix_order.order_trans)

lemma prefixeq_antisym: "\<lbrakk> prefix xs ys; prefix (ys::'a list) xs \<rbrakk> \<Longrightarrow> xs = ys"
by (rule prefix_order.antisym)


subsection \<open>Counting equal pairs\<close>
text \<open>Counting number of equal elements in two lists\<close>

definition mirror_pair :: "('a \<times> 'b) \<Rightarrow> ('b \<times> 'a)"
  where "mirror_pair p \<equiv> (snd p, fst p)"

lemma zip_mirror[rule_format]: "
  \<lbrakk> i < min (length xs) (length ys);
    p1 = (zip xs ys) ! i; p2 = (zip ys xs) ! i \<rbrakk> \<Longrightarrow>
  mirror_pair p1 = p2"
by (simp add: mirror_pair_def)

definition equal_pair :: "('a \<times> 'a) \<Rightarrow> bool"
  where "equal_pair p \<equiv> (fst p = snd p)"

lemma mirror_pair_equal: "equal_pair (mirror_pair p) = (equal_pair p)"
by (fastforce simp: mirror_pair_def equal_pair_def)

primrec
  equal_pair_count :: "('a \<times> 'a) list \<Rightarrow> nat"
where
  "equal_pair_count [] = 0"
| "equal_pair_count (p # ps) = (
    if (fst p = snd p)
      then Suc (equal_pair_count ps)
      else 0)"

lemma equal_pair_count_le: "equal_pair_count xs \<le> length xs"
by (induct xs, simp_all)

lemma equal_pair_count_0: "
  fst (hd ps) \<noteq> snd (hd ps) \<Longrightarrow> equal_pair_count ps = 0"
by (case_tac ps, simp_all)

lemma equal_pair_count_Suc: "
  equal_pair_count ((a, a) # ps) = Suc (equal_pair_count ps)"
by simp


lemma equal_pair_count_eq_pairwise[rule_format]: "
  \<lbrakk> length ps1 = length ps2;
    \<forall>i<length ps2. equal_pair (ps1 ! i) = equal_pair(ps2 ! i) \<rbrakk>
  \<Longrightarrow> equal_pair_count ps1 = equal_pair_count ps2"
apply (induct rule: list_induct2)
 apply simp
apply (fastforce simp add: equal_pair_def)
done

lemma equal_pair_count_mirror_pairwise[rule_format]: "
  \<lbrakk> length ps1 = length ps2;
    \<forall>i<length ps2. ps1 ! i = mirror_pair (ps2 ! i) \<rbrakk>
  \<Longrightarrow> equal_pair_count ps1 = equal_pair_count ps2"
apply (rule equal_pair_count_eq_pairwise, assumption)
apply (simp add: mirror_pair_equal)
done

(* The lemma states that all pairs with index < equal_pair_count ps
  are equal. It does not deal with maximality of equal_pair_count *)
lemma equal_pair_count_correct:"
  \<And>i. i < equal_pair_count ps \<Longrightarrow> equal_pair (ps ! i)"
apply (induct ps)
 apply simp
apply simp
apply (split if_split_asm)
apply (case_tac i)
apply (simp add: equal_pair_def)+
done

(* For @{text "i = equal_pair_count ps"} holds:
  either @{text "ps ! i"} not an equal pair,
  or all pairs are equal (@{text "equal_pair_count = length ps"}) *)
lemma equal_pair_count_maximality_aux[rule_format]: "\<And>i.
  i = equal_pair_count ps \<Longrightarrow> length ps = i \<or> \<not> equal_pair (ps ! i)"
apply (induct ps)
 apply simp
apply (simp add: equal_pair_def)
done

corollary equal_pair_count_maximality1a[rule_format]: "
  equal_pair_count ps = length ps \<or> \<not> equal_pair (ps!equal_pair_count ps)"
apply (insert equal_pair_count_maximality_aux[of "equal_pair_count ps" ps])
apply clarsimp
done

corollary equal_pair_count_maximality1b[rule_format]: "
  equal_pair_count ps \<noteq> length ps \<Longrightarrow>
  \<not> equal_pair (ps!equal_pair_count ps)"
by (insert equal_pair_count_maximality1a[of ps], simp)

lemma equal_pair_count_maximality2a[rule_format]: "
  equal_pair_count ps = length ps \<or> \<comment> \<open>either all pairs are equal\<close>
  (\<forall>i\<ge>equal_pair_count ps.(\<exists>j\<le>i. \<not>equal_pair (ps ! j)))"
apply clarsimp
apply (rule_tac x="equal_pair_count ps" in exI)
apply (simp add: equal_pair_count_maximality1b equal_pair_count_le)
done

corollary equal_pair_count_maximality2b[rule_format]: "
  equal_pair_count ps \<noteq> length ps \<Longrightarrow>
  \<forall>i\<ge>equal_pair_count ps.(\<exists>j\<le>i. \<not>equal_pair (ps!j))"
by (insert equal_pair_count_maximality2a[of ps], simp)

lemmas equal_pair_count_maximality =
  equal_pair_count_maximality1a equal_pair_count_maximality1b
  equal_pair_count_maximality2a equal_pair_count_maximality2b


subsection \<open>Prefix length\<close>

text \<open>Length of the prefix infimum\<close>

definition inf_prefix_length :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat"
  where "inf_prefix_length xs ys \<equiv> equal_pair_count (zip xs ys)"

value "int (inf_prefix_length [1::int,2,3,4,7,8,15] [1::int,2,3,4,7,15])"
value "int (inf_prefix_length [1::int,2,3,4] [1::int,2,3,4,7,15])"
value "int (inf_prefix_length [] [1::int,2,3,4,7,15])"
value "int (inf_prefix_length [1::int,2,3,4,5] [1::int,2,3,4,5])"

lemma inf_prefix_length_commute[rule_format]:
  "inf_prefix_length xs ys = inf_prefix_length ys xs"
apply (unfold inf_prefix_length_def)
apply (insert equal_pair_count_mirror_pairwise[of "zip xs ys" "zip ys xs"])
apply (simp add: equal_pair_count_mirror_pairwise[of "zip xs ys" "zip ys xs"] mirror_pair_def)
done

lemma inf_prefix_length_leL[intro]:
  "inf_prefix_length xs ys \<le> length xs"
apply (unfold inf_prefix_length_def)
apply (insert equal_pair_count_le[of "zip xs ys"])
apply simp
done

corollary inf_prefix_length_leR[intro]:
  "inf_prefix_length xs ys \<le> length ys"
by (simp add: inf_prefix_length_commute[of xs] inf_prefix_length_leL)

lemmas inf_prefix_length_le =
  inf_prefix_length_leL
  inf_prefix_length_leR

lemma inf_prefix_length_le_min[rule_format]:
  "inf_prefix_length xs ys \<le> min (length xs) (length ys)"
by (simp add: inf_prefix_length_le)

lemma hd_inf_prefix_length_0: "
  hd xs \<noteq> hd ys \<Longrightarrow> inf_prefix_length xs ys = 0"
apply (unfold inf_prefix_length_def)
apply (case_tac "xs = []", simp)
apply (case_tac "ys = []", simp)
apply (simp add: equal_pair_count_0 hd_zip)
done

lemma inf_prefix_length_NilL[simp]: "inf_prefix_length [] ys = 0"
by (simp add: inf_prefix_length_def)
lemma inf_prefix_length_NilR[simp]: "inf_prefix_length xs [] = 0"
by (simp add: inf_prefix_length_def)

lemma inf_prefix_length_Suc[simp]: "
  inf_prefix_length (a # xs) (a # ys) = Suc (inf_prefix_length xs ys)"
by (simp add: inf_prefix_length_def)

lemma inf_prefix_length_correct: "
  i < inf_prefix_length xs ys \<Longrightarrow> xs ! i = ys ! i"
apply (frule order_less_le_trans[OF _ inf_prefix_length_leL])
apply (frule order_less_le_trans[OF _ inf_prefix_length_leR])
apply (unfold inf_prefix_length_def)
apply (drule equal_pair_count_correct)
apply (simp add: equal_pair_def)
done

corollary nth_neq_imp_inf_prefix_length_le: "
  xs ! i \<noteq> ys ! i \<Longrightarrow> inf_prefix_length xs ys \<le> i"
apply (rule ccontr)
apply (simp add: inf_prefix_length_correct)
done

lemma inf_prefix_length_maximality1[rule_format]: "
  inf_prefix_length xs ys \<noteq> min (length xs) (length ys) \<Longrightarrow>
  xs ! (inf_prefix_length xs ys) \<noteq> ys ! (inf_prefix_length xs ys)"
apply (insert equal_pair_count_maximality1b[of "zip xs ys", folded inf_prefix_length_def], simp)
apply (drule neq_le_trans)
 apply (simp add: inf_prefix_length_le)
apply (simp add:  inf_prefix_length_def equal_pair_def)
done

corollary inf_prefix_length_maximality2[rule_format]: "
  \<lbrakk> inf_prefix_length xs ys \<noteq> min (length xs) (length ys);
    inf_prefix_length xs ys \<le> i \<rbrakk> \<Longrightarrow>
  \<exists>j\<le>i. xs ! j \<noteq> ys ! j"
apply (rule_tac x="inf_prefix_length xs ys" in exI)
apply (simp add: inf_prefix_length_maximality1 inf_prefix_length_le_min)
done

lemmas inf_prefix_length_maximality =
  inf_prefix_length_maximality1 inf_prefix_length_maximality2

lemma inf_prefix_length_append[simp]: "
  inf_prefix_length (zs @ xs) (zs @ ys) =
  length zs + inf_prefix_length xs ys"
apply (induct zs)
 apply simp
apply (simp add: inf_prefix_length_def)
done

lemma inf_prefix_length_take_correct: "
  n \<le> inf_prefix_length xs ys \<Longrightarrow> xs \<down> n = ys \<down> n"
apply (frule order_trans[OF _ inf_prefix_length_leL])
apply (frule order_trans[OF _ inf_prefix_length_leR])
apply (simp add: list_eq_iff inf_prefix_length_correct)
done

lemma inf_prefix_length_0_imp_hd_neq: "
  \<lbrakk> xs \<noteq> []; ys \<noteq> []; inf_prefix_length xs ys = 0 \<rbrakk> \<Longrightarrow> hd xs \<noteq> hd ys"
apply (rule ccontr)
apply (insert inf_prefix_length_maximality2[of xs ys 0])
apply (simp add: hd_eq_first)
done


subsection \<open>Prefix infimum\<close>

definition inf_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"  (infixl "\<sqinter>" 70)
  where "xs \<sqinter> ys \<equiv> xs \<down> (inf_prefix_length xs ys)"

lemma length_inf_prefix: "length (xs \<sqinter> ys) = inf_prefix_length xs ys"
by (simp add: inf_prefix_def min_eqR inf_prefix_length_leL)

lemma inf_prefix_commute: "xs \<sqinter> ys = ys \<sqinter> xs"
by (simp add: inf_prefix_def inf_prefix_length_commute[of ys] inf_prefix_length_take_correct)

lemma inf_prefix_takeL: "xs \<sqinter> ys = xs \<down> (inf_prefix_length xs ys)"
by (simp add: inf_prefix_def)

lemma inf_prefix_takeR: "xs \<sqinter> ys = ys \<down> (inf_prefix_length xs ys)"
by (subst inf_prefix_commute, subst inf_prefix_length_commute, rule inf_prefix_takeL)

lemma inf_prefix_correct: "i < length (xs \<sqinter> ys) \<Longrightarrow> xs ! i = ys ! i"
by (simp add: length_inf_prefix inf_prefix_length_correct)

corollary inf_prefix_correctL: "
  i < length (xs \<sqinter> ys) \<Longrightarrow> (xs \<sqinter> ys) ! i = xs ! i"
by (simp add: inf_prefix_takeL)

corollary inf_prefix_correctR: "
  i < length (xs \<sqinter> ys) \<Longrightarrow> (xs \<sqinter> ys) ! i = ys ! i"
by (simp add: inf_prefix_takeR)

lemma inf_prefix_take_correct: "
  n \<le> length (xs \<sqinter> ys) \<Longrightarrow> xs \<down> n = ys \<down> n"
by (simp add: length_inf_prefix inf_prefix_length_take_correct)

lemma is_inf_prefix[rule_format]: "
  \<lbrakk> length zs = length (xs \<sqinter> ys);
    \<And>i. i < length (xs \<sqinter> ys) \<Longrightarrow> zs ! i = xs ! i \<and> zs ! i = ys ! i \<rbrakk> \<Longrightarrow>
  zs = xs \<sqinter> ys"
by (simp add: list_eq_iff inf_prefix_def)

lemma hd_inf_prefix_Nil: "hd xs \<noteq> hd ys \<Longrightarrow> xs \<sqinter> ys = []"
by (simp add: inf_prefix_def hd_inf_prefix_length_0)

lemma inf_prefix_Nil_imp_hd_neq: "
  \<lbrakk> xs \<noteq> []; ys \<noteq> []; xs \<sqinter> ys = [] \<rbrakk> \<Longrightarrow> hd xs \<noteq> hd ys"
by (simp add: inf_prefix_def inf_prefix_length_0_imp_hd_neq)

lemma length_inf_prefix_append[simp]: "
  length ((zs @ xs) \<sqinter> (zs @ ys)) =
  length zs + length (xs \<sqinter> ys)"
by (simp add: length_inf_prefix)

lemma inf_prefix_append[simp]: "(zs @ xs) \<sqinter> (zs @ ys) = zs @ (xs \<sqinter> ys)"
apply (rule is_inf_prefix[symmetric], simp)
apply (clarsimp simp: nth_append)
apply (intro conjI inf_prefix_correctL inf_prefix_correctR, simp+)
done

lemma hd_neq_inf_prefix_append: "
  hd xs \<noteq> hd ys \<Longrightarrow> (zs @ xs) \<sqinter> (zs @ ys) = zs"
by (simp add: hd_inf_prefix_Nil)

lemma inf_prefix_NilL[simp]: "[] \<sqinter> ys = []"
by (simp del: length_0_conv add: length_0_conv[symmetric] length_inf_prefix)

corollary inf_prefix_NilR[simp]: "xs \<sqinter> [] = []"
by (simp add: inf_prefix_commute)

lemmas inf_prefix_Nil = inf_prefix_NilL inf_prefix_NilR

lemma inf_prefix_Cons[simp]: "(a # xs) \<sqinter> (a # ys) = a # xs \<sqinter> ys"
by (insert inf_prefix_append[of "[a]" xs ys], simp)

corollary inf_prefix_hd[simp]: "hd ((a # xs) \<sqinter> (a # ys)) = a"
by simp


lemma inf_prefix_le1: "prefix (xs \<sqinter> ys) xs"
by (simp add: inf_prefix_takeL take_imp_prefix)

lemma inf_prefix_le2: "prefix (xs \<sqinter> ys) ys"
by (simp add: inf_prefix_takeR take_imp_prefix)

lemma le_inf_prefix_iff: "prefix x (y \<sqinter> z) = (prefix x y \<and> prefix x z)"
apply (rule iffI)
 apply (blast intro: prefix_order.order_trans inf_prefix_le1 inf_prefix_le2)
apply (clarsimp simp: prefix_def)
done

lemma le_imp_le_inf_prefix: "\<lbrakk> prefix x y; prefix x z \<rbrakk> \<Longrightarrow> prefix x (y \<sqinter> z)"
by (rule le_inf_prefix_iff[THEN iffD2], simp)

interpretation prefix:
  semilattice_inf
    "(\<sqinter>) :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
    "prefix"
    "strict_prefix"
apply intro_locales
apply (rule class.semilattice_inf_axioms.intro)
apply (rule inf_prefix_le1)
apply (rule inf_prefix_le2)
apply (rule le_imp_le_inf_prefix, assumption+)
done


subsection \<open>Prefices for infinite lists\<close>

definition iprefix :: "'a list \<Rightarrow> 'a ilist \<Rightarrow> bool"  (infixl "\<sqsubseteq>" 50)
  where "xs \<sqsubseteq> f \<equiv> \<exists>g. f = xs \<frown> g"

lemma iprefix_eq_iprefix_take: "(xs \<sqsubseteq> f) = (f \<Down> length xs = xs)"
apply (unfold iprefix_def)
apply (rule iffI)
 apply clarsimp
apply (rule_tac x="f \<Up> (length xs)" in exI)
apply (subst i_append_i_take_i_drop_id[where n="length xs", symmetric], simp)
done

lemma iprefix_take_eq_iprefix_take_ex: "
  (f \<Down> length xs = xs) = (\<exists>n. f \<Down> n = xs)"
apply (rule iffI)
 apply (rule_tac x="length xs" in exI, assumption)
apply clarsimp
done

lemma iprefix_eq_iprefix_take_ex: "(xs \<sqsubseteq> f) = (\<exists>n. f \<Down> n = xs)"
by (simp add: iprefix_eq_iprefix_take iprefix_take_eq_iprefix_take_ex)

lemma i_take_imp_iprefix[intro]: "f \<Down> n \<sqsubseteq> f"
by (simp add: iprefix_eq_iprefix_take)

lemma i_take_prefix_le_conv: "prefix (f \<Down> a) (f \<Down> b) = (a \<le> b)"
by (fastforce simp: prefix_eq_prefix_take list_eq_iff)

lemma i_append_imp_iprefix[simp,intro]: "xs \<sqsubseteq> xs \<frown> f"
by (simp add: iprefix_def)

lemma iprefix_imp_take_eq: "
  \<lbrakk> n \<le> length xs; xs \<sqsubseteq> f \<rbrakk> \<Longrightarrow> xs \<down> n = f \<Down> n"
by (clarsimp simp: iprefix_eq_iprefix_take_ex min_eqR)

lemma prefixeq_iprefix_trans: "\<lbrakk> prefix xs ys; ys \<sqsubseteq> f \<rbrakk> \<Longrightarrow> xs \<sqsubseteq> f"
by (fastforce simp: iprefix_eq_iprefix_take_ex prefix_eq_prefix_take_ex)

lemma i_take_length_prefix_conv: "prefix (f \<Down> length xs) xs = (xs \<sqsubseteq> f)"
by (simp add: iprefix_eq_iprefix_take prefix_length_le_eq_conv[symmetric])

lemma iprefixI[intro?]: "f = xs \<frown> g \<Longrightarrow> xs \<sqsubseteq> f"
by (unfold iprefix_def, simp)

lemma iprefixE[elim?]: "\<lbrakk> xs \<sqsubseteq> f; \<And>g. f = xs \<frown> g \<Longrightarrow> C \<rbrakk> \<Longrightarrow> C"
by (unfold iprefix_def, blast)

lemma Nil_iprefix[iff]: "[] \<sqsubseteq> f"
by (unfold iprefix_def, simp)

lemma same_prefix_iprefix[simp]: "(xs @ ys \<sqsubseteq> xs \<frown> f) = (ys \<sqsubseteq> f)"
by (simp add: iprefix_eq_iprefix_take)

lemma prefix_iprefix[simp]: "prefix xs ys \<Longrightarrow> xs \<sqsubseteq> ys \<frown> f"
by (clarsimp simp: prefix_def iprefix_def i_append_assoc[symmetric] simp del: i_append_assoc)

lemma append_iprefixD: "xs @ ys \<sqsubseteq> f \<Longrightarrow> xs \<sqsubseteq> f"
by (clarsimp simp: iprefix_def i_append_assoc[symmetric] simp del: i_append_assoc)

lemma iprefix_length_le_imp_prefix: "
  \<lbrakk> xs \<sqsubseteq> ys \<frown> f; length xs \<le> length ys \<rbrakk> \<Longrightarrow> prefix xs ys"
by (clarsimp simp: iprefix_eq_iprefix_take_ex take_is_prefix)

lemma iprefix_i_append: "
  (xs \<sqsubseteq> ys \<frown> f) = (prefix xs ys \<or> (\<exists>zs. xs = ys @ zs \<and> zs \<sqsubseteq> f))"
apply (rule iffI)
 apply (case_tac "length xs \<le> length ys")
  apply (blast intro: iprefix_length_le_imp_prefix)
 apply (rule disjI2)
 apply (rule_tac x="f \<Down> (length xs - length ys)" in exI)
 apply (simp add: iprefix_eq_iprefix_take)
apply fastforce
done

lemma i_append_one_iprefix: "
  xs \<sqsubseteq> f \<Longrightarrow> xs @ [f (length xs)] \<sqsubseteq> f"
by (simp add: iprefix_eq_iprefix_take i_take_Suc_conv_app_nth)

lemma iprefix_same_length_le: "
  \<lbrakk> xs \<sqsubseteq> f; ys \<sqsubseteq> f; length xs \<le> length ys \<rbrakk> \<Longrightarrow> prefix xs ys"
by (clarsimp simp: iprefix_eq_iprefix_take_ex i_take_prefix_le_conv)

lemma iprefix_same_cases: "
  \<lbrakk> xs \<sqsubseteq> f; ys \<sqsubseteq> f \<rbrakk> \<Longrightarrow> prefix xs ys \<or> prefix ys xs"
apply (case_tac "length xs \<le> length ys")
apply (simp add: iprefix_same_length_le)+
done

lemma set_mono_iprefix: "xs \<sqsubseteq> f \<Longrightarrow> set xs \<subseteq> range f"
by (unfold iprefix_def, fastforce)

end
