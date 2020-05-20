(* Title:     Check_Monad
   Author:    Christian Sternagel
   Author:    René Thiemann
*)

section \<open>A Special Error Monad for Certification with Informative Error Messages\<close>

theory Check_Monad
imports Error_Monad
begin

text \<open>A check is either successful or fails with some error.\<close>
type_synonym
  'e check = "'e + unit"

abbreviation succeed :: "'e check"
where
  "succeed \<equiv> return ()"

definition check :: "bool \<Rightarrow> 'e \<Rightarrow> 'e check"
where
  "check b e = (if b then succeed else error e)"

lemma isOK_check [simp]:
  "isOK (check b e) = b" by (simp add: check_def)

lemma isOK_check_catch [simp]:
  "isOK (try check b e catch f) \<longleftrightarrow> b \<or> isOK (f e)"
  by (auto simp add: catch_def check_def)

definition check_return :: "'a check \<Rightarrow> 'b \<Rightarrow> 'a + 'b"
where
  "check_return chk res = (chk \<then> return res)"

lemma check_return [simp]:
  "check_return chk res = return res' \<longleftrightarrow> isOK chk \<and> res' = res"
  unfolding check_return_def by (cases chk) auto

lemma [code_unfold]:
  "check_return chk res = (case chk of Inr _ \<Rightarrow> Inr res | Inl e \<Rightarrow> Inl e)"
  unfolding check_return_def bind_def ..

abbreviation check_allm :: "('a \<Rightarrow> 'e check) \<Rightarrow> 'a list \<Rightarrow> 'e check"
where
  "check_allm f xs \<equiv> forallM f xs <+? snd"

abbreviation check_exm :: "('a \<Rightarrow> 'e check) \<Rightarrow> 'a list \<Rightarrow> ('e list \<Rightarrow> 'e) \<Rightarrow> 'e check"
where
  "check_exm f xs fld \<equiv> existsM f xs <+? fld"

lemma isOK_check_allm:
  "isOK (check_allm f xs) \<longleftrightarrow> (\<forall>x \<in> set xs. isOK (f x))"
  by simp

abbreviation check_allm_index :: "('a \<Rightarrow> nat \<Rightarrow> 'e check) \<Rightarrow> 'a list \<Rightarrow> 'e check"
where
  "check_allm_index f xs \<equiv> forallM_index f xs <+? snd"

abbreviation check_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a check"
where
  "check_all f xs \<equiv> check_allm (\<lambda>x. if f x then succeed else error x) xs"

abbreviation check_all_index :: "('a \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a \<times> nat) check"
where
  "check_all_index f xs \<equiv> check_allm_index (\<lambda>x i. if f x i then succeed else error (x, i)) xs"

lemma isOK_check_all_index [simp]:
  "isOK (check_all_index f xs) \<longleftrightarrow> (\<forall>i < length xs. f (xs ! i) i)"
  by auto

text \<open>The following version allows to modify the index during the check.\<close>
definition
  check_allm_gen_index ::
    "('a \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> ('a \<Rightarrow> nat \<Rightarrow> 'e check) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'e check"
where
  "check_allm_gen_index g f n xs = snd (foldl (\<lambda>(i, m) x. (g x i, m \<then> f x i)) (n, succeed) xs)"

lemma foldl_error:
  "snd (foldl (\<lambda>(i, m) x . (g x i, m \<then> f x i)) (n, error e) xs) = error e"
  by (induct xs arbitrary: n) auto

lemma isOK_check_allm_gen_index [simp]:
  assumes "isOK (check_allm_gen_index g f n xs)"
  shows "\<forall>x\<in>set xs. \<exists>i. isOK (f x i)"
using assms
proof (induct xs arbitrary: n)
  case (Cons x xs)
  show ?case
  proof (cases "isOK (f x n)")
    case True
    then have "\<exists>i. isOK (f x i)" by auto
    with True Cons show ?thesis
      unfolding check_allm_gen_index_def by (force simp: isOK_iff)
  next
    case False
    then obtain e where "f x n = error e" by (cases "f x n") auto
    with foldl_error [of g f _ e] and Cons show ?thesis
      unfolding check_allm_gen_index_def by auto
  qed
qed simp

lemma check_allm_gen_index [fundef_cong]:
  fixes f :: "'a \<Rightarrow> nat \<Rightarrow> 'e check"
  assumes "\<And>x n. x \<in> set xs \<Longrightarrow> g x n = g' x n"
    and "\<And>x n. x \<in> set xs \<Longrightarrow> f x n = f' x n"
  shows "check_allm_gen_index g f n xs = check_allm_gen_index g' f' n xs"
proof -
  { fix n m
    have "foldl (\<lambda>(i, m) x. (g x i, m \<then> f x i)) (n, m) xs =
      foldl (\<lambda>(i, m) x. (g' x i, m \<then> f' x i)) (n, m) xs"
      using assms by (induct xs arbitrary: n m) auto }
  then show ?thesis unfolding check_allm_gen_index_def by simp
qed

definition check_subseteq :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a check"
where
  "check_subseteq xs ys = check_all (\<lambda>x. x \<in> set ys) xs"

lemma isOK_check_subseteq [simp]:
  "isOK (check_subseteq xs ys) \<longleftrightarrow> set xs \<subseteq> set ys"
  by (auto simp: check_subseteq_def)

definition check_same_set :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a check"
where
  "check_same_set xs ys = (check_subseteq xs ys \<then> check_subseteq ys xs)"

lemma isOK_check_same_set [simp]:
  "isOK (check_same_set xs ys) \<longleftrightarrow> set xs = set ys"
  unfolding check_same_set_def by auto

definition check_disjoint :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a check"
where
  "check_disjoint xs ys = check_all (\<lambda>x. x \<notin> set ys) xs"

lemma isOK_check_disjoint [simp]:
  "isOK (check_disjoint xs ys) \<longleftrightarrow> set xs \<inter> set ys = {}"
  unfolding check_disjoint_def by (auto)

definition check_all_combinations :: "('a \<Rightarrow> 'a \<Rightarrow> 'b check) \<Rightarrow> 'a list \<Rightarrow> 'b check"
where
  "check_all_combinations c xs = check_allm (\<lambda>x. check_allm (c x) xs) xs"

lemma isOK_check_all_combinations [simp]:
  "isOK (check_all_combinations c xs) \<longleftrightarrow> (\<forall>x \<in> set xs. \<forall>y \<in> set xs. isOK (c x y))"
  unfolding check_all_combinations_def by simp

fun check_pairwise :: "('a \<Rightarrow> 'a \<Rightarrow> 'b check) \<Rightarrow> 'a list \<Rightarrow> 'b check"
where
  "check_pairwise c [] = succeed" |
  "check_pairwise c (x # xs) = (check_allm (c x) xs \<then> check_pairwise c xs)"

lemma pairwise_aux:
  "(\<forall>j<length (x # xs). \<forall>i<j. P ((x # xs) ! i) ((x # xs) ! j))
     = ((\<forall>j<length xs. P x (xs ! j)) \<and> (\<forall>j<length xs. \<forall>i<j. P (xs ! i) (xs ! j)))"
  (is "?C = (?A \<and> ?B)")
proof (intro iffI conjI)
  assume *: "?A \<and> ?B"
  show "?C"
  proof (intro allI impI)
    fix i j
    assume "j < length (x # xs)" and "i < j"
    then show "P ((x # xs) ! i) ((x # xs) ! j)"
    proof (induct j)
      case (Suc j)
      then show ?case
        using * by (induct i) simp_all
    qed simp
  qed
qed force+

lemma isOK_check_pairwise [simp]:
  "isOK (check_pairwise c xs) \<longleftrightarrow> (\<forall>j<length xs. \<forall>i<j. isOK (c (xs ! i) (xs ! j)))"
proof (induct xs)
  case (Cons x xs)
  have "isOK (check_allm (c x) xs) = (\<forall>j<length xs. isOK (c x (xs ! j)))"
    using all_set_conv_all_nth [of xs "\<lambda>y. isOK (c x y)"] by simp
  then have "isOK (check_pairwise c (x # xs)) =
    ((\<forall>j<length xs. isOK (c x (xs ! j))) \<and> (\<forall>j<length xs. \<forall>i<j. isOK (c (xs ! i) (xs ! j))))"
    by (simp add: Cons)
  then show ?case using pairwise_aux [of x xs "\<lambda>x y. isOK (c x y)"] by simp
qed auto

abbreviation check_exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> ('a list) check"
where
  "check_exists f xs \<equiv> check_exm (\<lambda>x. if f x then succeed else error [x]) xs concat"

lemma isOK_choice [simp]:
  "isOK (choice []) \<longleftrightarrow> False"
  "isOK (choice (x # xs)) \<longleftrightarrow> isOK x \<or> isOK (choice xs)"
  by (auto simp: choice.simps isOK_def split: sum.splits)

fun or_ok :: "'a check \<Rightarrow> 'a check \<Rightarrow> 'a check" where
  "or_ok (Inl a) b = b" |
  "or_ok (Inr a) b = Inr a" 

lemma or_is_or: "isOK (or_ok a b) = isOK a \<or> isOK b" using or_ok.elims by blast


end

