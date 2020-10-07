(*
  File: Quicksort.thy
  Author: Bohua Zhan
*)

section \<open>Quicksort\<close>

theory Quicksort
  imports Arrays_Ex
begin

text \<open>
  Functional version of quicksort.

  Implementation of quicksort is largely based on theory
  Imperative\_Quicksort in HOL/Imperative\_HOL/ex in the Isabelle
  library.
\<close>

subsection \<open>Outer remains\<close>
  
definition outer_remains :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "outer_remains xs xs' l r \<longleftrightarrow> (length xs = length xs' \<and> (\<forall>i. i < l \<or> r < i \<longrightarrow> xs ! i = xs' ! i))"

lemma outer_remains_length [forward]:
  "outer_remains xs xs' l r \<Longrightarrow> length xs = length xs'" by auto2

lemma outer_remains_eq [rewrite_back]:
  "outer_remains xs xs' l r \<Longrightarrow> i < l \<Longrightarrow> xs ! i = xs' ! i"
  "outer_remains xs xs' l r \<Longrightarrow> r < i \<Longrightarrow> xs ! i = xs' ! i" by auto2+

lemma outer_remains_sublist [backward2]:
  "outer_remains xs xs' l r \<Longrightarrow> i < l \<Longrightarrow> take i xs = take i xs'"
  "outer_remains xs xs' l r \<Longrightarrow> r < i \<Longrightarrow> drop i xs = drop i xs'"
  "i \<le> j \<Longrightarrow> j \<le> length xs \<Longrightarrow> outer_remains xs xs' l r \<Longrightarrow> j \<le> l \<Longrightarrow> sublist i j xs = sublist i j xs'"
  "i \<le> j \<Longrightarrow> j \<le> length xs \<Longrightarrow> outer_remains xs xs' l r \<Longrightarrow> i > r \<Longrightarrow> sublist i j xs = sublist i j xs'" by auto2+
setup \<open>del_prfstep_thm_eqforward @{thm outer_remains_def}\<close>

subsection \<open>part1 function\<close>  

function part1 :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a list)" where
  "part1 xs l r a = (
     if r \<le> l then (r, xs)
     else if xs ! l \<le> a then part1 xs (l + 1) r a
     else part1 (list_swap xs l r) l (r - 1) a)"
  by auto
  termination by (relation "measure (\<lambda>(_,l,r,_). r - l)") auto
setup \<open>register_wellform_data ("part1 xs l r a", ["r < length xs"])\<close>
setup \<open>add_prfstep_check_req ("part1 xs l r a", "r < length xs")\<close>

lemma part1_basic:
  "r < length xs \<Longrightarrow> l \<le> r \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow>
   outer_remains xs xs' l r \<and> mset xs' = mset xs \<and> l \<le> rs \<and> rs \<le> r"
@proof @fun_induct "part1 xs l r a" @unfold "part1 xs l r a" @qed
setup \<open>add_forward_prfstep_cond @{thm part1_basic} [with_term "part1 ?xs ?l ?r ?a"]\<close>

lemma part1_partitions1 [backward]:
  "r < length xs \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow> l \<le> i \<Longrightarrow> i < rs \<Longrightarrow> xs' ! i \<le> a"
@proof @fun_induct "part1 xs l r a" @unfold "part1 xs l r a" @qed

lemma part1_partitions2 [backward]:
  "r < length xs \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow> rs < i \<Longrightarrow> i \<le> r \<Longrightarrow> xs' ! i \<ge> a"
@proof @fun_induct "part1 xs l r a" @unfold "part1 xs l r a" @qed

subsection \<open>Paritition function\<close>

definition partition :: "('a::linorder list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a list)" where [rewrite]:
  "partition xs l r = (
    let p = xs ! r;
      (m, xs') = part1 xs l (r - 1) p;
      m' = if xs' ! m \<le> p then m + 1 else m
    in
      (m', list_swap xs' m' r))"
setup \<open>register_wellform_data ("partition xs l r", ["l < r", "r < length xs"])\<close>

lemma partition_basic:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs') = partition xs l r \<Longrightarrow>
   outer_remains xs xs' l r \<and> mset xs' = mset xs \<and> l \<le> rs \<and> rs \<le> r" by auto2
setup \<open>add_forward_prfstep_cond @{thm partition_basic} [with_term "partition ?xs ?l ?r"]\<close>
  
lemma partition_partitions1 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs') = partition xs l r \<Longrightarrow>
   x \<in> set (sublist l rs xs') \<Longrightarrow> x \<le> xs' ! rs"
@proof @obtain i where "i \<ge> l" "i < rs" "x = xs' ! i" @qed

lemma partition_partitions2 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs'') = partition xs l r \<Longrightarrow>
   x \<in> set (sublist (rs + 1) (r + 1) xs'') \<Longrightarrow> x \<ge> xs'' ! rs"
@proof
  @obtain i where "i \<ge> rs + 1" "i < r + 1" "x = xs'' ! i"
  @let "p = xs ! r"
  @let "m = fst (part1 xs l (r - 1) p)"
  @let "xs' = snd (part1 xs l (r - 1) p)"
  @case "xs' ! m \<le> p"
@qed
setup \<open>del_prfstep_thm @{thm partition_def}\<close>

lemma quicksort_term1:
  "\<not>r \<le> l \<Longrightarrow> \<not> length xs \<le> r \<Longrightarrow> x = partition xs l r \<Longrightarrow> (p, xs1) = x \<Longrightarrow> p - Suc l < r - l"
@proof @have "fst (partition xs l r) - l - 1 < r - l" @qed

lemma quicksort_term2:
  "\<not>r \<le> l \<Longrightarrow> \<not> length xs \<le> r \<Longrightarrow> x = partition xs l r \<Longrightarrow> (p, xs2) = x \<Longrightarrow> r - Suc p < r - l"
@proof @have "r - fst (partition xs l r) - 1 < r - l" @qed

subsection \<open>Quicksort function\<close>

function quicksort :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "quicksort xs l r = (
    if l \<ge> r then xs
    else if r \<ge> length xs then xs
    else let
      (p, xs1) = partition xs l r;
      xs2 = quicksort xs1 l (p - 1)
    in
      quicksort xs2 (p + 1) r)"
  by auto termination apply (relation "measure (\<lambda>(a, l, r). (r - l))") 
  by (auto simp add: quicksort_term1 quicksort_term2)

lemma quicksort_basic [rewrite_arg]:
  "mset (quicksort xs l r) = mset xs \<and> outer_remains xs (quicksort xs l r) l r"
@proof @fun_induct "quicksort xs l r" @unfold "quicksort xs l r" @qed

lemma quicksort_trivial1 [rewrite]:
  "l \<ge> r \<Longrightarrow> quicksort xs l r = xs"
@proof @unfold "quicksort xs l r" @qed

lemma quicksort_trivial2 [rewrite]:
  "r \<ge> length xs \<Longrightarrow> quicksort xs l r = xs"
@proof @unfold "quicksort xs l r" @qed

lemma quicksort_permutes [resolve]:
  "xs' = quicksort xs l r \<Longrightarrow> set (sublist l (r + 1) xs') = set (sublist l (r + 1) xs)"
@proof
  @case "l \<ge> r" @case "r \<ge> length xs"
  @have "xs = take l xs @ sublist l (r + 1) xs @ drop (r + 1) xs"
  @have "xs' = take l xs' @ sublist l (r + 1) xs' @ drop (r + 1) xs'"
  @have "take l xs = take l xs'"
  @have "drop (r + 1) xs = drop (r + 1) xs'"
@qed

lemma quicksort_sorts [forward_arg]:
  "r < length xs \<Longrightarrow> sorted (sublist l (r + 1) (quicksort xs l r))"
@proof @fun_induct "quicksort xs l r"
  @case "l \<ge> r" @with @case "l = r" @end
  @case "r \<ge> length xs"
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @let "xs3 = quicksort xs2 (p + 1) r"
  @have "sorted (sublist l (r + 1) xs3)" @with
    @have "l \<le> p" @have "p + 1 \<le> r + 1" @have "r + 1 \<le> length xs3"
    @have "sublist l p xs2 = sublist l p xs3"
    @have "set (sublist l p xs1) = set (sublist l p xs2)"
    @have "sublist (p + 1) (r + 1) xs1 = sublist (p + 1) (r + 1) xs2"
    @have "set (sublist (p + 1) (r + 1) xs2) = set (sublist (p + 1) (r + 1) xs3)"
    @have "\<forall>x\<in>set (sublist l p xs3). x \<le> xs3 ! p"
    @have "\<forall>x\<in>set (sublist (p + 1) (r + 1) xs3). x \<ge> xs3 ! p"
    @have "sorted (sublist l p xs3)"
    @have "sorted (sublist (p + 1) (r + 1) xs3)"
    @have "sublist l (r + 1) xs3 = sublist l p xs3 @ (xs3 ! p) # sublist (p + 1) (r + 1) xs3"
  @end
  @unfold "quicksort xs l r"
@qed

text \<open>Main result: correctness of functional quicksort.\<close>
theorem quicksort_sorts_all [rewrite]:
  "xs \<noteq> [] \<Longrightarrow> quicksort xs 0 (length xs - 1) = sort xs"
@proof
  @let "xs' = quicksort xs 0 (length xs - 1)"
  @have "sublist 0 (length xs - 1 + 1) xs' = xs'"
@qed

end
