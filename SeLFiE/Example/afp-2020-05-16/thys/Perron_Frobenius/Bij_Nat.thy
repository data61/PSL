(*
  Authors: J. Divasón, R. Thiemann, A. Yamada
*)
section \<open>Connecting HMA-matrices with JNF-matrices\<close>

text \<open>The following theories provide a connection between the type-based representation of vectors
  and matrices in HOL multivariate-analysis (HMA) with the set-based representation of vectors and matrices
  with integer indices in the Jordan-normal-form (JNF) development.\<close>

subsection \<open>Bijections between index types of HMA and natural numbers\<close>

text \<open>At the core of HMA-connect, there has to be a translation between indices
  of vectors and matrices, which are via index-types on the one hand, and natural
  numbers on the other hand.

  We some unspecified bijection in our application, and not the conversions
  to-nat and from-nat in theory 
  Rank-Nullity-Theorem/Mod-Type, since our definitions
  below do not enforce any further type constraints.\<close>

theory Bij_Nat
imports 
  "HOL-Library.Cardinality"
  "HOL-Library.Numeral_Type"
begin

lemma finite_set_to_list: "\<exists> xs :: 'a :: finite list. distinct xs \<and> set xs = Y"
proof -
  have "finite Y" by simp
  thus ?thesis 
  proof (induct Y rule: finite_induct)
    case (insert y Y)
    then obtain xs where xs: "distinct xs" "set xs = Y" by auto
    show ?case
      by (rule exI[of _ "y # xs"], insert xs insert(2), auto)
  qed simp
qed

definition univ_list :: "'a :: finite list" where
  "univ_list = (SOME xs. distinct xs \<and> set xs = UNIV)"

lemma univ_list: "distinct (univ_list :: 'a list)" "set univ_list = (UNIV :: 'a :: finite set)"
proof -
  let ?xs = "univ_list :: 'a list"
  have "distinct ?xs \<and> set ?xs = UNIV"
    unfolding univ_list_def
    by (rule someI_ex, rule finite_set_to_list)
  thus "distinct ?xs" "set ?xs = UNIV" by auto
qed

definition to_nat :: "'a :: finite \<Rightarrow> nat" where
  "to_nat a = (SOME i. univ_list ! i = a \<and> i < length (univ_list :: 'a list))"

definition from_nat :: "nat \<Rightarrow> 'a :: finite" where
  "from_nat i = univ_list ! i"

lemma length_univ_list_card: "length (univ_list :: 'a :: finite list) = CARD('a)"
  using distinct_card[of "univ_list :: 'a list", symmetric] 
  by (auto simp: univ_list)

lemma to_nat_ex: "\<exists>! i. univ_list ! i = (a :: 'a :: finite) \<and> i < length (univ_list :: 'a list)"
proof -
  let ?ul = "univ_list :: 'a list"
  have a_in_set: "a \<in> set ?ul" unfolding univ_list by auto
  from this [unfolded set_conv_nth] 
  obtain i where i1: "?ul ! i = a \<and> i < length ?ul" by auto
  show ?thesis
  proof (rule ex1I, rule i1)
    fix j
    assume "?ul ! j = a \<and> j < length ?ul"
    moreover have "distinct ?ul" by (simp add: univ_list)
    ultimately show "j = i" using i1 nth_eq_iff_index_eq by blast
  qed
qed
  
lemma to_nat_less_card: "to_nat (a :: 'a :: finite) < CARD('a)"
proof -
  let ?ul = "univ_list :: 'a list"
  from to_nat_ex[of a] obtain i where 
  i1: "univ_list ! i = a \<and> i<length (univ_list::'a list)" by auto
  show ?thesis unfolding to_nat_def
  proof (rule someI2, rule i1)
   fix x
   assume x: "?ul ! x = a \<and> x < length ?ul"
   thus "x < CARD ('a)" using x by (simp add: univ_list length_univ_list_card)
  qed
qed

lemma to_nat_from_nat_id: 
  assumes i: "i < CARD('a :: finite)" 
  shows "to_nat (from_nat i :: 'a) = i"
  unfolding to_nat_def from_nat_def
proof (rule some_equality, simp)
  have l: "length (univ_list::'a list) = card (set (univ_list::'a list))" 
    by (rule distinct_card[symmetric], simp add: univ_list)
  thus i2: "i < length (univ_list::'a list)"
    using i unfolding univ_list by simp
   fix n 
   assume n: "(univ_list::'a list) ! n = (univ_list::'a list) ! i \<and> n < length (univ_list::'a list)"
   have d: "distinct (univ_list::'a list)" using univ_list by simp      
   show "n = i" using nth_eq_iff_index_eq[OF d _ i2] n by auto
qed

lemma from_nat_inj: assumes i: "i < CARD('a :: finite)"
  and j: "j < CARD('a :: finite)"
  and id: "(from_nat i :: 'a) = from_nat j"
  shows "i = j"
proof -
  from arg_cong[OF id, of to_nat]
  show ?thesis using i j by (simp add: to_nat_from_nat_id)
qed

lemma from_nat_to_nat_id[simp]:
  "(from_nat (to_nat a)) = (a::'a :: finite)"
proof -
  have a_in_set: "a \<in> set (univ_list)" unfolding univ_list by auto
  from this [unfolded set_conv_nth] 
  obtain i where i1: "univ_list ! i = a \<and> i<length (univ_list::'a list)" by auto
  show ?thesis 
  unfolding to_nat_def from_nat_def
  by (rule someI2, rule i1, simp)
qed

lemma to_nat_inj[simp]: assumes "to_nat a = to_nat b"
  shows "a = b"
proof -
  from to_nat_ex[of a] to_nat_ex[of b]
  show "a = b" unfolding to_nat_def by (metis assms from_nat_to_nat_id)
qed

lemma range_to_nat: "range (to_nat :: 'a :: finite \<Rightarrow> nat) = {0 ..< CARD('a)}" (is "?l = ?r")
proof -
  {
    fix i
    assume "i \<in> ?l"
    hence "i \<in> ?r" using to_nat_less_card[where 'a = 'a] by auto
  }
  moreover
  {
    fix i
    assume "i \<in> ?r"
    hence "i < CARD('a)" by auto
    from to_nat_from_nat_id[OF this] 
    have "i \<in> ?l" by (metis range_eqI)
  }
  ultimately show ?thesis by auto
qed

lemma inj_to_nat: "inj to_nat" by (simp add: inj_on_def)

lemma bij_to_nat: "bij_betw to_nat (UNIV :: 'a :: finite set) {0 ..< CARD('a)}"
  unfolding bij_betw_def by (auto simp: range_to_nat inj_to_nat)


lemma numeral_nat: "(numeral m1 :: nat) * numeral n1 \<equiv> numeral (m1 * n1)" 
  "(numeral m1 :: nat) + numeral n1 \<equiv> numeral (m1 + n1)" by simp_all

lemmas card_num_simps = 
  card_num1 card_bit0 card_bit1 
  mult_num_simps
  add_num_simps 
  eq_num_simps
  mult_Suc_right mult_0_right One_nat_def add.right_neutral 
  numeral_nat Suc_numeral 

end
