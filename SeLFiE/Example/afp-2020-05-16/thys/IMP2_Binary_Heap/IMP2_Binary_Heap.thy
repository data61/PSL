theory IMP2_Binary_Heap
  imports IMP2.IMP2 IMP2.IMP2_Aux_Lemmas
begin
section \<open>Introduction\<close>
text \<open>In this submission imperative versions of the following array-based binary minimum heap
      functions are implemented and verified: insert, get-min, delete-min, make-heap.
      The latter three are then used to prove the correctness of an in-place heapsort, which sorts
      an array in descending order. To do that in Isabelle/HOL, the proof framework IMP2
      \cite{IMP2-AFP} is used. Here arrays are modeled by \<open>int \<Rightarrow> int\<close> functions. The imperative
      implementations are iterative versions of the partly recursive algorithms described in
      \cite{MS} and \cite{CLRS}.

      This submission starts with the basic definitions and lemmas, which are needed for array-based 
      binary heaps. These definitions and lemmas are parameterised with an arbitrary (transitive) 
      comparison function (where such a function is needed), so they are not only applicable to 
      minimum heaps. After some more general, useful lemmas on arrays, the imperative minimum heap 
      functions and the heapsort are implemented and verified.\<close>

section \<open>Heap Related Definitions and Theorems\<close>
subsection \<open>Array Bounds\<close>
text \<open>A small helper function is used to define valid array indices. Note that the lower index 
      bound \<open>l\<close> is arbitrary and not fixed to 0 or 1. The upper index bound \<open>r\<close> is not a valid
      index itself, so that the empty array can be denoted by having \<open>l = r\<close>.\<close>
abbreviation bounded :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "bounded l r x \<equiv> l \<le> x \<and> x < r"

subsection \<open>Parent and Children\<close>

subsubsection \<open>Definitions\<close>
text \<open>For the notion of an array-based binary heap, the parent and child relations on the array 
      indices need to be defined.\<close>
definition parent :: "int \<Rightarrow> int \<Rightarrow> int" where
  "parent l c = l + (c - l - 1) div 2"

definition l_child :: "int \<Rightarrow> int \<Rightarrow> int" where
  "l_child l p = 2 * p - l + 1"

definition r_child :: "int \<Rightarrow> int \<Rightarrow> int" where
  "r_child l p = 2 * p - l + 2"

subsubsection \<open>Lemmas\<close>
lemma parent_upper_bound: "parent l c < c \<longleftrightarrow> l \<le> c"
  unfolding parent_def by auto

lemma parent_upper_bound_alt: "l \<le> parent l c \<Longrightarrow> parent l c < c"
  unfolding parent_def by simp

lemma parent_lower_bound: "l \<le> parent l c \<longleftrightarrow> l < c"
  unfolding parent_def by linarith

lemma grand_parent_upper_bound: "parent l (parent l c) < c \<longleftrightarrow> l \<le> c"
  unfolding parent_def by linarith

corollary parent_bounds: "l < x \<Longrightarrow> x < r \<Longrightarrow> bounded l r (parent l x)"
  using parent_lower_bound parent_upper_bound_alt by fastforce


lemma l_child_lower_bound: " p < l_child l p \<longleftrightarrow> l \<le> p"
  unfolding l_child_def by simp

corollary l_child_lower_bound_alt: "l \<le> x \<Longrightarrow> x \<le> p \<Longrightarrow> x < l_child l p"
  using l_child_lower_bound[of p l] by linarith

lemma parent_l_child[simp]: "parent l (l_child l n) = n"
  unfolding parent_def l_child_def by simp


lemma r_child_lower_bound: "l \<le> p \<Longrightarrow> p < r_child l p"
  unfolding r_child_def by simp

corollary r_child_lower_bound_alt: "l \<le> x \<Longrightarrow> x \<le> p \<Longrightarrow> x < r_child l p"
  using r_child_lower_bound[of l p] by linarith

lemma parent_r_child[simp]: "parent l (r_child l n) = n"
  unfolding parent_def r_child_def by simp


lemma smaller_l_child: "l_child l x < r_child l x"
  unfolding l_child_def r_child_def by simp

lemma parent_two_children: 
  "(c = l_child l p \<or> c = r_child l p) \<longleftrightarrow> parent l c = p"
  unfolding parent_def l_child_def r_child_def by linarith

subsection \<open>Heap Invariants\<close>
subsubsection \<open>Definitions\<close>
text \<open>The following heap invariants and the following lemmas are parameterised with an arbitrary 
      (transitive) comparison function. For the concrete function implementations at the end of 
      this submission \<open>\<le>\<close> on ints is used.\<close>

text \<open>For the \<open>make_heap\<close> function, which transforms an unordered array into a valid heap,
      the notion of a partial heap is needed. Here the heap invariant only holds for array indices
      between a certain valid array index \<open>m\<close> and \<open>r\<close>. The standard heap invariant is then
      simply the special case where \<open>m = l\<close>.\<close>
definition is_partial_heap 
  :: "('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> 'a::order) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "is_partial_heap cmp heap l m r = (\<forall> x. bounded m r x \<longrightarrow> 
               bounded m r (parent l x) \<longrightarrow> cmp (heap (parent l x)) (heap x))"

abbreviation is_heap 
  :: "('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> 'a::order) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "is_heap cmp heap l r \<equiv> is_partial_heap cmp heap l l r"


text \<open>During all of the modifying heap functions the heap invariant is temporarily violated at
      a single index \<open>i\<close> and it is then gradually restored by either \<open>sift_down\<close> or 
      \<open>sift_up\<close>. The following definitions formalize these weakened invariants.

      The second part of the conjunction in the following definitions states, that the comparison 
      between the parent of \<open>i\<close> and each of the children of \<open>i\<close> evaluates to \<open>True\<close> without 
      explicitly using the child relations.\<close>
definition is_partial_heap_except_down 
  :: "('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> 'a::order) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "is_partial_heap_except_down cmp heap l m r i = (\<forall> x. bounded m r x \<longrightarrow>
    ((parent l x \<noteq> i \<longrightarrow> bounded m r (parent l x) \<longrightarrow> cmp (heap (parent l x)) (heap x)) \<and> 
     (parent l x = i \<longrightarrow> bounded m r (parent l (parent l x))  
                     \<longrightarrow> cmp (heap (parent l (parent l x))) (heap x))))"

abbreviation is_heap_except_down 
  :: "('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> 'a::order) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "is_heap_except_down cmp heap l r i \<equiv> is_partial_heap_except_down cmp heap l l r i"


text \<open>As mentioned the notion of a partial heap is only needed for \<open>make_heap\<close>, 
      which only uses \<open>sift_down\<close> internally, so there doesn't need to be an additional 
      definition for the partial heap version of the \<open>sift_up\<close> invariant.\<close>
definition is_heap_except_up 
  :: "('a::order \<Rightarrow> 'a::order \<Rightarrow> bool) \<Rightarrow> (int \<Rightarrow> 'a::order) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "is_heap_except_up cmp heap l r i = (\<forall> x. bounded l r x \<longrightarrow> 
    ((x \<noteq> i \<longrightarrow> bounded l r (parent l x) \<longrightarrow> cmp (heap (parent l x)) (heap x)) \<and> 
     (parent l x = i \<longrightarrow> bounded l r (parent l (parent l x)) 
                     \<longrightarrow> cmp (heap (parent l (parent l x))) (heap x))))"

subsubsection \<open>Lemmas\<close>

lemma empty_partial_heap[simp]: "is_partial_heap cmp heap l r r"
  unfolding is_partial_heap_def by linarith

lemma is_partial_heap_smaller_back: 
  "is_partial_heap cmp heap l m r \<Longrightarrow> r' \<le> r \<Longrightarrow> is_partial_heap cmp heap l m r'"
  unfolding is_partial_heap_def by simp

lemma is_partial_heap_smaller_front: 
  "is_partial_heap cmp heap l m r \<Longrightarrow> m \<le> m' \<Longrightarrow> is_partial_heap cmp heap l m' r"
  unfolding is_partial_heap_def by simp

text \<open>The second half of each array is a is a partial binary heap, since it contains only leafs,
      which are all trivial binary heaps.\<close>
lemma snd_half_is_partial_heap: 
  "(l + r) div 2 \<le> m \<Longrightarrow> is_partial_heap cmp heap l m r" 
  unfolding is_partial_heap_def parent_def by linarith

lemma modify_outside_partial_heap: 
  assumes 
    "heap = heap' on {m..<r}" 
    "is_partial_heap cmp heap l m r"
  shows "is_partial_heap cmp heap' l m r"
  using assms eq_onD unfolding is_partial_heap_def by fastforce

text \<open>The next few lemmas formalize how the heap invariant is weakened, when the heap is modified
      in a certain way.\<close>

text \<open>This lemma is used by \<open>make_heap\<close>.\<close>
lemma partial_heap_added_first_el: 
  assumes 
    "l \<le> m" "m \<le> r"
    "is_partial_heap cmp heap l (m + 1) r"
  shows "is_partial_heap_except_down cmp heap l m r m"
 unfolding is_partial_heap_except_down_def
proof
  fix x
  let ?p_x = "parent l x"
  let ?gp_x = "parent l ?p_x"
  show "bounded m r x \<longrightarrow>
        (?p_x \<noteq> m \<longrightarrow> bounded m r ?p_x \<longrightarrow> cmp (heap ?p_x) (heap x)) \<and>
        (?p_x = m \<longrightarrow> bounded m r ?gp_x \<longrightarrow> cmp (heap ?gp_x) (heap x))"
  proof
    assume x_bound: "bounded m r x"
    have p_x_lower: "?p_x \<noteq> m \<longrightarrow> bounded m r ?p_x \<longrightarrow> ?p_x \<ge> m + 1"
      by simp
    hence "?p_x \<noteq> m \<longrightarrow> bounded m r ?p_x \<longrightarrow> x \<ge> m + 1"
      using parent_upper_bound[of l x] x_bound assms(1) by linarith
    hence p_invariant: "(?p_x \<noteq> m \<longrightarrow> bounded m r ?p_x \<longrightarrow> cmp (heap ?p_x) (heap x))"
      using assms(3) is_partial_heap_def p_x_lower x_bound by blast

    have gp_up_bound: "(?p_x = m \<longrightarrow> ?gp_x < m)"
      by (simp add: assms(1) parent_upper_bound)
    show "(?p_x \<noteq> m \<longrightarrow> bounded m r ?p_x \<longrightarrow> cmp (heap ?p_x) (heap x)) \<and>
          (?p_x = m \<longrightarrow> bounded m r ?gp_x \<longrightarrow> cmp (heap ?gp_x) (heap x))"
      using gp_up_bound p_invariant by linarith
  qed
qed

text \<open>This lemma is used by \<open>del_min\<close>.\<close>
lemma heap_changed_first_el: 
  assumes "is_heap cmp heap l r" "l \<le> r"
  shows "is_heap_except_down cmp (heap(l := b)) l r l"
proof -
  have "is_partial_heap cmp heap l (l + 1) r"
    using assms(1) is_partial_heap_smaller_front by fastforce
  hence "is_partial_heap cmp (heap(l := b)) l (l + 1) r"
    using modify_outside_partial_heap[of heap] by simp
  thus ?thesis
    by (simp add: assms(2) partial_heap_added_first_el)
qed

text \<open>This lemma is used by \<open>insert\<close>.\<close>
lemma heap_appended_el: 
  assumes 
    "is_heap cmp heap l r" 
    "heap = heap' on {l..<r}"
  shows "is_heap_except_up cmp heap' l (r+1) r"
proof -
  have "is_heap cmp heap' l r" 
    using assms(1,2) modify_outside_partial_heap by blast 
  thus ?thesis unfolding is_partial_heap_def is_heap_except_up_def
    by (metis not_less_iff_gr_or_eq parent_upper_bound zless_add1_eq)
qed

subsubsection \<open>First Heap Element\<close>
text \<open>The next step is to show that the first element of the heap is always the ``smallest'' 
      according to the given comparison function. For the proof a rule for strong induction on lower
      bounded integers is needed. Its proof is based on the proof of strong induction on natural 
      numbers found in \cite{Str_Ind}.\<close>
lemma strong_int_gr_induct_helper: 
  assumes "k < (i::int)" "(\<And>i. k < i \<Longrightarrow> (\<And>j. k < j \<Longrightarrow> j < i \<Longrightarrow> P j) \<Longrightarrow> P i)"
  shows "\<And>j. k < j \<Longrightarrow> j < i \<Longrightarrow> P j"
  using assms
proof(induction i rule: int_gr_induct)
  case base 
  then show ?case by linarith 
next
  case (step i) 
  then show ?case 
  proof(cases "j = i")
    case True
    then show ?thesis using step.IH step.prems(1,3) by blast 
  next
    case False
    hence "j < i" using step.prems(2) by simp
    then show ?thesis using step.IH step.prems(1,3) by blast 
  qed
qed

theorem strong_int_gr_induct:
  assumes 
    "k < (i::int)" 
    "(\<And>i. k < i \<Longrightarrow> (\<And>j. k < j \<Longrightarrow> j < i \<Longrightarrow> P j) \<Longrightarrow> P i)" 
  shows "P i"
  using assms less_induct strong_int_gr_induct_helper by blast

text \<open>Now the main theorem, that the first heap element is the ``smallest'' according to the
      given comparison function, can be proven.\<close>
theorem heap_first_el:
  assumes 
    "is_heap cmp heap l r"
    "transp cmp"
    "l < x" "x < r"
  shows "cmp (heap l) (heap x)"
  using assms unfolding is_partial_heap_def
proof(induction x rule: strong_int_gr_induct[of l])
  case 1
  then show ?case using assms(3) by simp
next
  case (2 i)
  have cmp_pi_i: "cmp (heap (parent l i)) (heap i)"
    using "2.hyps" "2.prems"(1,4) parent_bounds by simp
  then show ?case 
  proof(cases)
    assume "parent l i > l"
    then have "cmp (heap l) (heap (parent l i))"
      using "2.IH" "2.prems"(1,2,4) parent_upper_bound_alt by simp
    then show ?thesis
      using "2.prems"(2) cmp_pi_i transpE by metis
  next
    assume "\<not> parent l i > l"
    then have "parent l i = l"
      using "2.hyps" dual_order.order_iff_strict parent_lower_bound by metis
    then show ?thesis
      using cmp_pi_i by simp
  qed
qed



section \<open>General Lemmas on Arrays\<close>
text \<open>Some additional lemmas on @{const "mset_ran"}, @{const "swap"} and @{const "eq_on"} are needed
      for the final proofs.\<close>

subsection \<open>Lemmas on @{const "mset_ran"}\<close>
abbreviation arr_mset :: "(int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a multiset" where
  "arr_mset arr l r \<equiv> mset_ran arr {l..<r}"

lemma in_mset_imp_in_array: 
  "x \<in># (arr_mset arr l r) \<longleftrightarrow> (\<exists>i. bounded l r i \<and> arr i = x)"
  unfolding mset_ran_def by fastforce

lemma arr_mset_remove_last: 
  "l \<le> r \<Longrightarrow> arr_mset arr l r = arr_mset arr l (r + 1) - {#arr r#}"
  by (simp add: intvs_upper_decr mset_ran_def)

lemma arr_mset_append: 
  "l \<le> r \<Longrightarrow> arr_mset arr l (r + 1) = arr_mset arr l r + {#arr r#}"
  using arr_mset_remove_last[of l r arr] by simp

corollary arr_mset_append_alt: 
  "l \<le> r \<Longrightarrow> arr_mset (arr(r := b)) l (r + 1) = arr_mset arr l r + {#b#}"
  by (simp add: arr_mset_append mset_ran_subst_outside)

lemma arr_mset_remove_first: 
  "i \<le> r \<Longrightarrow> arr_mset arr (i - 1) r = arr_mset arr i r + {#arr (i - 1)#}"
  by(induction r rule: int_ge_induct) (auto simp add: arr_mset_append)

lemma arr_mset_split: 
  assumes "l \<le> m" "m \<le> r"
  shows "arr_mset arr l r = arr_mset arr l m + arr_mset arr m r"
  using assms
proof(induction m rule: int_ge_induct[of l])
  case (step i)
  have add_last: "arr_mset arr l (i + 1) = arr_mset arr l i + {#arr i#}"
    using step arr_mset_append by blast
  have rem_first: "arr_mset arr (i+1) r = arr_mset arr i r - {#arr i#}"
    by (metis step.prems arr_mset_remove_first add_diff_cancel_right') 
  show ?case 
    using step add_last rem_first by fastforce
qed (simp)

text \<open>That the first element in a heap is the ``smallest'', can now be expressed using multisets.\<close>
corollary heap_first_el_alt:                                                   
  assumes 
    "transp cmp" 
    "is_heap cmp heap l r" 
    "x \<in># (arr_mset heap l r)" 
    "heap l \<noteq> x"
  shows "cmp (heap l) x"
  by(metis assms heap_first_el in_mset_imp_in_array le_less)


subsection \<open>Lemmas on @{term "swap"} and @{term "eq_on"}\<close>

lemma eq_on_subset: 
  "arr1 = arr2 on R \<Longrightarrow> S \<subseteq> R \<Longrightarrow> arr1 = arr2 on S"
  by (simp add: eq_on_def set_mp)

lemma swap_swaps: 
  "arr' = swap arr x y \<Longrightarrow> arr' y = arr x \<and> arr' x = arr y"
  unfolding swap_def by simp

lemma swap_only_swaps: 
  "arr' = swap arr x y \<Longrightarrow> z \<noteq> x \<Longrightarrow> z \<noteq> y \<Longrightarrow> arr' z = arr z"
  unfolding swap_def by simp

lemma swap_commute: "swap arr x y = swap arr y x"
  unfolding swap_def by fastforce

lemma swap_eq_on: 
  "arr1 = arr2 on S \<Longrightarrow> x \<notin> S \<Longrightarrow> y \<notin> S \<Longrightarrow> arr1 = swap arr2 x y on S"
  unfolding swap_def by simp

corollary swap_parent_eq_on: 
  assumes 
    "arr1 = arr2 on - {l..<r}" 
    "l < c" "c < r" 
  shows "arr1 = swap arr2 (parent l c) c on - {l..<r} "
  using parent_bounds swap_eq_on assms by fastforce

corollary swap_child_eq_on: 
  assumes 
    "arr1 = arr2 on - {l..<r}" 
    "c = l_child l p \<or> c = r_child l p" 
    "l \<le> p" "c < r" 
  shows "arr1 = swap arr2 p c on - {l..<r} "
  by (metis assms parent_lower_bound parent_two_children swap_parent_eq_on)

lemma swap_child_mset: 
  assumes 
    "arr_mset arr1 l r = arr_mset arr2 l r" 
    "c = l_child l p \<or> c = r_child l p" 
    "l \<le> p" "c < r" 
  shows "arr_mset arr1 l r = arr_mset (swap arr2 p c) l r"
proof -
  have child_bounded: "l < c \<and> c < r"
    by (metis assms(2-4) parent_lower_bound parent_two_children)
  have parent_bounded: "bounded l r p"
    by (metis assms(2-4) dual_order.strict_trans parent_two_children parent_upper_bound_alt)
  thus ?thesis
    using assms(1) child_bounded mset_ran_swap[of p "{l..<r}" c arr2] atLeastLessThan_iff
    by simp
qed

text \<open>The following lemma shows, which propositions have to hold on the pre-swap array, so that
      a comparison between two elements holds on the post-swap array. This is useful for the 
      proofs of the loop invariants of \<open>sift_up\<close> and \<open>sift_down\<close>. The lemma is kept 
      quite general (except for the argument order) and could probably be more closely
      related to the parent relation for more concise proofs.\<close>
lemma cmp_swapI: 
  fixes arr::"'a::order \<Rightarrow> 'a::order"
  assumes
    "m < n \<and> x < y"
    "m < n \<and> x < y \<Longrightarrow> x = m \<Longrightarrow> y = n \<Longrightarrow> P (arr n) (arr m)"
    "m < n \<and> x < y \<Longrightarrow> x \<noteq> m \<Longrightarrow> x \<noteq> n \<Longrightarrow> y \<noteq> m \<Longrightarrow> y \<noteq> n \<Longrightarrow> P (arr m) (arr n)"
    "m < n \<and> x < y \<Longrightarrow> x = m \<Longrightarrow> y \<noteq> m \<Longrightarrow> y \<noteq> n \<Longrightarrow>  P (arr y) (arr n)"
    "m < n \<and> x < y \<Longrightarrow> x = n \<Longrightarrow> y \<noteq> m \<Longrightarrow> y \<noteq> n \<Longrightarrow>  P (arr m) (arr y)"
    "m < n \<and> x < y \<Longrightarrow> x \<noteq> m \<Longrightarrow> x \<noteq> n \<Longrightarrow> y = n \<Longrightarrow> P (arr m) (arr x)"
    "m < n \<and> x < y \<Longrightarrow> x \<noteq> m \<Longrightarrow> x \<noteq> n \<Longrightarrow> y = m \<Longrightarrow> P (arr x) (arr n)"
  shows "P (swap arr x y m) (swap arr x y n)"
  by (metis assms order.asym swap_only_swaps swap_swaps)

section \<open>Imperative Heap Implementation\<close>
text \<open>The following imperative heap functions are based on \cite{MS} and \cite{CLRS}. All functions,
      that are recursive in these books, are iterative in the following implementations. The 
      function definitions are done with IMP2 \cite{IMP2-AFP}. From now on the heaps only contain 
      ints and only use \<open>\<le>\<close> as comparison function. The auxiliary lemmas used from now on are 
      heavily modeled after the proof goals, that are generated by the vcg tool (also part of IMP2).\<close>

subsection \<open>Simple Functions\<close>
subsubsection \<open>Parent, Children and Swap\<close>
text \<open>In this section the parent and children relations are expressed as IMP2 procedures. 
      Additionally a simple procedure, that swaps two array elements, is defined.\<close>
procedure_spec prnt (l, x) returns p
  assumes True
    ensures "p = parent l\<^sub>0 x\<^sub>0"
  defines \<open>p = ((x - l - 1) / 2 + l)\<close>
  by vcg (simp add: parent_def)

procedure_spec left_child (l, x) returns lc
  assumes True 
    ensures "lc = l_child l\<^sub>0 x\<^sub>0"
  defines \<open>lc = 2 * x - l + 1\<close>
  by vcg (simp add: l_child_def)

procedure_spec right_child (l, x) returns rc
  assumes True
    ensures "rc = r_child l\<^sub>0 x\<^sub>0"
  defines \<open>rc = 2 * x - l + 2\<close>
  by vcg (simp add: r_child_def)

procedure_spec swp (heap, x, y) returns heap
  assumes True
    ensures "heap = swap heap\<^sub>0 x\<^sub>0 y\<^sub>0 "
  defines \<open>tmp = heap[x]; heap[x] = heap[y]; heap[y] = tmp\<close>
  by vcg (simp add: swap_def)

subsubsection \<open>\<open>get_min\<close>\<close>
text \<open>In this section \<open>get_min\<close> is defined, which simply returns the first element (the minimum) of 
      the heap. For this definition an additional theorem is proven, which enables the use of
      @{const "Min_mset"} in the postcondition.\<close>

theorem heap_minimum: 
  assumes 
    "l < r" 
    "is_heap (\<le>) heap l r"
  shows "heap l = Min_mset (arr_mset heap l r)"
proof -
  have "(\<forall>x \<in># (arr_mset heap l r). (heap l) \<le> x)"
    using assms(2) heap_first_el_alt transp_le by blast
  thus ?thesis
    by (simp add: assms(1) dual_order.antisym)
qed

procedure_spec get_min (heap, l, r) returns min
  assumes "l < r \<and> is_heap (\<le>) heap l r"  
    ensures "min = Min_mset (arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0)"
  for heap[] l r
  defines \<open>min = heap[l]\<close>
  by vcg (simp add: heap_minimum)

subsection \<open>Modifying Functions\<close>

subsubsection \<open>\<open>sift_up\<close> and \<open>insert\<close>\<close>
text \<open>The next heap function is \<open>insert\<close>, which internally uses \<open>sift_up\<close>. In the beginning of 
      this section \<open>sift_up_step\<close> is proven, which states that each \<open>sift_up\<close> loop iteration 
      correctly transforms the weakened heap invariant. For its proof two additional
      auxiliary lemmas are used. After \<open>sift_up_step\<close> \<open>sift_up\<close> and then \<open>insert\<close> are verified.\<close>

text \<open>\<open>sift_up_step\<close> can be proven directly by the smt-solver without auxiliary lemmas, but they
      were introduced to show the proof details. The analogous proofs for \<open>sift_down\<close> were 
      just solved with smt, since the proof structure should be very similar, even though the 
      \<open>sift_down\<close> proof goals are slightly more complex.\<close>
lemma sift_up_step_aux1:
  fixes heap::"int \<Rightarrow> int"
  assumes  
    "is_heap_except_up (\<le>) heap l r x"
    "parent l x \<ge> l" 
    "(heap x) \<le> (heap (parent l x))" 
    "bounded l r k" 
    "k \<noteq> (parent l x)" 
    "bounded l r (parent l k)"
  shows "(swap heap (parent l x) x (parent l k)) \<le> (swap heap (parent l x) x k)"
  apply(intro cmp_swapI[of "(parent l k)" k "(parent l x)" x "(\<le>)" heap])
  subgoal using assms(2,6) parent_upper_bound_alt by blast
  subgoal using assms(3) by blast
  subgoal using assms(1,4,6) unfolding is_heap_except_up_def by blast
  subgoal using assms(1,3,4,6) unfolding is_heap_except_up_def by fastforce
  subgoal using assms(5) by blast
  subgoal by blast 
  subgoal using assms(1,2,4) unfolding is_heap_except_up_def by simp
  done

lemma sift_up_step_aux2: 
  fixes heap::"int \<Rightarrow> int"
  assumes
    "is_heap_except_up (\<le>) heap l r x"
    "parent l x \<ge> l"
    "heap x \<le> (heap (parent l x))"
    "bounded l r k"
    "parent l k = parent l x"
    "bounded l r (parent l (parent l k))"
  shows 
    "swap heap (parent l x) x (parent l (parent l k)) \<le> swap heap (parent l x) x k"
  using assms unfolding is_heap_except_up_def
proof-
  let ?gp_k = "parent l (parent l k)"
  let ?gp_x = "parent l (parent l x)"
  have gp_k_eq_gp_x: "swap heap (parent l x) x ?gp_k = heap ?gp_x"
    by (metis assms(2,5) grand_parent_upper_bound less_irrefl swap_only_swaps)
  show ?thesis
      using assms unfolding is_heap_except_up_def
  proof(cases)
    assume k_eq_x: "k = x"
    have "swap heap (parent l x) x k = heap (parent l x)"
      by (metis k_eq_x swap_swaps)
    then show ?thesis
      using assms(1,2,4,6) unfolding is_heap_except_up_def
      by (metis gp_k_eq_gp_x k_eq_x parent_bounds parent_lower_bound)
  next
    assume k_neq_x: "k \<noteq> x"
    have "swap heap (parent l x) x k = heap k"
      by (metis assms(5) gp_k_eq_gp_x k_neq_x swap_only_swaps)
    then show ?thesis using assms unfolding is_heap_except_up_def
      by (metis gp_k_eq_gp_x k_neq_x order_trans parent_bounds parent_lower_bound)
  qed
qed

lemma sift_up_step:
  fixes heap::"int \<Rightarrow> int"
  assumes  
    "is_heap_except_up (\<le>) heap l r x"
    "parent l x \<ge> l" 
    "(heap x) \<le> (heap (parent l x))"
  shows "is_heap_except_up (\<le>) (swap heap (parent l x) x) l r (parent l x)"
  using assms sift_up_step_aux1 sift_up_step_aux2
  unfolding is_heap_except_up_def by blast

text \<open>\<open>sift_up\<close> restores the heap invariant, that is only violated at the current position, by 
      iteratively swapping the current element with its parent until the beginning of the array is 
      reached or the current element is bigger than its parent.\<close>
procedure_spec sift_up (heap, l, r, x) returns heap
  assumes "is_heap_except_up (\<le>) heap l r x \<and> bounded l r x"
    ensures "is_heap (\<le>) heap l\<^sub>0 r\<^sub>0 \<and>
             arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 = arr_mset heap l\<^sub>0 r\<^sub>0 \<and>
             heap\<^sub>0 = heap on - {l\<^sub>0..<r\<^sub>0}"
  for heap[] l x r
  defines \<open>
    p = prnt(l, x);
    while (x > l \<and> heap[x] \<le> heap[p]) 
      @variant \<open>x - l\<close>
      @invariant \<open>is_heap_except_up (\<le>) heap l r x \<and> p = parent l x \<and> 
                  bounded l r x \<and> arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 = arr_mset heap l r \<and>
                  heap\<^sub>0 = heap  on - {l..<r}\<close> 
    {
        heap = swp(heap, p, x);
        x = p;
        p = prnt(l, x)
    }\<close>
  apply vcg_cs
  apply(intro conjI)
  subgoal using parent_lower_bound sift_up_step by blast
  subgoal using parent_lower_bound by blast
  subgoal using parent_bounds by blast
  subgoal using parent_bounds by (simp add: mset_ran_swap)
  subgoal using swap_parent_eq_on by blast
  subgoal using parent_upper_bound by simp
  subgoal unfolding is_heap_except_up_def is_partial_heap_def
    by (metis le_less not_less parent_lower_bound)
  done

text \<open>\<open>insert\<close> inserts an element into a heap by appending it to the heap and restoring the heap 
      invariant with @{const "sift_up"}.\<close>
procedure_spec insert (heap, l, r, el) returns (heap, l, r)
  assumes "is_heap (\<le>) heap l r \<and> l \<le> r"  
    ensures "is_heap (\<le>) heap l r \<and>
             arr_mset heap l r = arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 + {#el\<^sub>0#} \<and>
             l = l\<^sub>0 \<and> r = r\<^sub>0 + 1  \<and> heap\<^sub>0 = heap on - {l..<r}"
  for heap l r el
  defines \<open>
    heap[r] = el;
    x = r;
    r = r + 1;
    heap = sift_up(heap, l, r, x)
  \<close>
  apply vcg_cs 
  subgoal by (simp add: heap_appended_el)
  subgoal by (metis arr_mset_append_alt add_mset_add_single)
  done

subsubsection \<open>\<open>sift_down\<close>, \<open>del_min\<close> and \<open>make_heap\<close>\<close>
text \<open>The next heap functions are \<open>del_min\<close> and \<open>make_heap\<close>, which both use \<open>sift_down\<close> to 
      restore/establish the heap invariant. \<open>sift_down\<close> is proven first (this time without 
      additional auxiliary lemmas) followed by \<open>del_min\<close> and \<open>make_heap\<close>.\<close>

text \<open>\<open>sift_down\<close> restores the heap invariant, that is only violated at the current position, by 
      iteratively swapping the current element with its smallest child until the end of 
      the array is reached or the current element is smaller than its children.\<close>
procedure_spec sift_down(heap, l, r, x) returns heap 
  assumes "is_partial_heap_except_down (\<le>) heap l x r x \<and> l \<le> x \<and> x \<le> r"
    ensures "is_partial_heap (\<le>) heap l\<^sub>0 x\<^sub>0 r\<^sub>0 \<and> 
             arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 = arr_mset heap l\<^sub>0 r\<^sub>0 \<and> 
             heap\<^sub>0 = heap on - {l\<^sub>0..<r\<^sub>0}"
  defines \<open>
   lc = left_child(l, x);
   rc = right_child(l, x);
    while (lc < r \<and> (heap[lc] < heap[x] \<or> (rc < r \<and> heap[rc] < heap[x]))) 
      @variant \<open>r - x\<close>
      @invariant \<open>is_partial_heap_except_down (\<le>) heap l x\<^sub>0 r x \<and>
                  x\<^sub>0 \<le> x \<and> x \<le> r \<and> lc = l_child l x \<and> rc = r_child l x \<and>
                  arr_mset heap\<^sub>0 l r = arr_mset heap l r \<and>
                  heap\<^sub>0 = heap on - {l..<r}\<close>
  { 
    smallest = lc;
    if (rc < r \<and> heap[rc] < heap[lc]) {
      smallest = rc
    };
    heap = swp(heap, x, smallest);
    x = smallest;
    lc = left_child(l, x);
    rc = right_child(l, x)
  }\<close>
  apply vcg_cs
  subgoal
    apply(intro conjI)
    subgoal unfolding is_partial_heap_except_down_def
      by (smt parent_two_children swap_swaps swap_only_swaps
          swap_commute parent_upper_bound_alt)
    subgoal using r_child_lower_bound_alt by fastforce
    subgoal using swap_child_mset order_trans by blast
    subgoal using swap_child_eq_on by fastforce
    done
  subgoal
    by (meson less_le_trans not_le order.asym r_child_lower_bound) 
  subgoal
    apply(intro conjI)
    subgoal unfolding is_partial_heap_except_down_def
      by (smt parent_two_children swap_swaps swap_only_swaps
          swap_commute parent_upper_bound_alt)
    subgoal using l_child_lower_bound_alt by fastforce
    subgoal using swap_child_mset order_trans by blast
    subgoal using swap_child_eq_on by fastforce
    done
  subgoal 
    by (meson less_le_trans not_le order.asym l_child_lower_bound)
  subgoal unfolding is_partial_heap_except_down_def is_partial_heap_def
    by (metis dual_order.strict_trans not_less parent_two_children smaller_l_child)
  done


text \<open>\<open>del_min\<close> needs an additional lemma which shows, that it actually removes (only) the minimum
      from the heap.\<close>
lemma del_min_mset: 
  fixes heap::"int \<Rightarrow> int"
  assumes 
    "l < r"
    "is_heap (\<le>) heap l r"
    "mod_heap = heap(l := heap (r - 1))"
    "arr_mset mod_heap l (r - 1) = arr_mset new_heap l (r - 1)"
  shows 
    "arr_mset new_heap l (r - 1) = arr_mset heap l r - {#Min_mset (arr_mset heap l r)#}"
proof -
  let ?heap_mset = "arr_mset heap l r"
  have l_is_min: "heap l = Min_mset ?heap_mset"
    using assms(1,2) heap_minimum by blast
  have "(arr_mset mod_heap l r) = ?heap_mset + {#heap (r-1)#} - {#heap l#}"
    by (simp add: assms(1,3) mset_ran_subst_inside)
  hence "(arr_mset mod_heap l (r - 1)) = ?heap_mset - {#heap l#}"
    by (simp add: assms(1,3) arr_mset_remove_last) 
  thus ?thesis
    using assms(4) l_is_min by simp
qed

text \<open>\<open>del_min\<close> removes the minimum element from the heap by replacing the first element with the 
      last element, shrinking the array by one and subsequently restoring the heap invariant 
      with @{const "sift_down"}.\<close>
procedure_spec del_min (heap, l, r) returns (heap, l, r)
  assumes "l < r \<and> is_heap (\<le>) heap l r"  
    ensures "is_heap (\<le>) heap l r \<and> 
             arr_mset heap l r = arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 - {#Min_mset (arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0)#} \<and> 
             l = l\<^sub>0 \<and> r = r\<^sub>0 - 1 \<and> 
             heap\<^sub>0 = heap on - {l\<^sub>0..<r\<^sub>0}"
  for heap l r
  defines \<open>
    r = r - 1;
    heap[l] = heap[r];
    heap = sift_down(heap, l, r, l)
  \<close>
  apply vcg_cs
  subgoal by (simp add: heap_changed_first_el is_partial_heap_smaller_back)
  subgoal
    apply(rule conjI)
    subgoal using del_min_mset by blast
    subgoal by (simp add: eq_on_def intvs_incdec(3) intvs_lower_incr)
    done
  done


text \<open>\<open>make_heap\<close> transforms an arbitrary array into a heap by iterating through all array 
      positions from the middle of the array up to the beginning of the array and calling 
      @{const "sift_down"} for each one.\<close>
procedure_spec make_heap (heap, l, r) returns heap
  assumes "l \<le> r"  
    ensures "is_heap (\<le>) heap l\<^sub>0 r\<^sub>0 \<and> 
             arr_mset heap l\<^sub>0 r\<^sub>0 = arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 \<and> 
             heap\<^sub>0 = heap on - {l\<^sub>0..< r\<^sub>0}"
  for heap[] l r
  defines \<open>
    y = (r + l)/2 - 1;
    while (y \<ge> l)
          @variant \<open>y - l + 1\<close>
          @invariant \<open>is_partial_heap (\<le>) heap l (y + 1) r \<and>
                      arr_mset heap l r = arr_mset heap\<^sub>0 l\<^sub>0 r\<^sub>0 \<and>
                      l - 1 \<le> y \<and> y < r \<and> heap\<^sub>0 = heap on - {l..<r}\<close>
    {
      heap = sift_down(heap, l, r, y);
      y = y - 1
    }\<close> 
  apply(vcg_cs)
  subgoal 
    apply(rule conjI)
    subgoal by (simp add: snd_half_is_partial_heap add.commute)
    subgoal by linarith 
    done
  subgoal using partial_heap_added_first_el le_less by blast 
  subgoal using eq_on_trans by blast 
  subgoal using dual_order.antisym by fastforce
  done

subsection \<open>Heapsort Implementation\<close>

text \<open>The final part of this submission is the implementation of the in-place heapsort. Firstly it 
      builds the \<open>\<le>\<close>-heap and then it iteratively removes the minimum of the heap, which is put at 
      the now vacant end of the shrinking heap. This is done until the heap is empty, which leaves 
      the array sorted in descending order.\<close>
subsubsection \<open>Auxiliary Lemmas\<close>
text \<open>Firstly the notion of a sorted array is needed. This is more or less the same as 
      @{const "ran_sorted"} generalized for arbitrary comparison functions.\<close>
definition array_is_sorted :: "(int \<Rightarrow> int \<Rightarrow> bool) \<Rightarrow>  (int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "array_is_sorted cmp a l r \<equiv> \<forall>i. \<forall>j. bounded l r i \<longrightarrow> bounded l r j \<longrightarrow> i < j \<longrightarrow> cmp (a i) (a j)"

text \<open>This lemma states, that the heapsort doesn't change the elements contained in the array during
      the loop iterations.\<close>
lemma heap_sort_mset_step:
  fixes arr::"int \<Rightarrow> int"
  assumes 
    "l < m" "m \<le> r"
    "arr_mset arr' l (m - 1) = arr_mset arr l m - {#Min_mset (arr_mset arr l m)#}"
    "arr = arr' on - {l..<m}"
    "mod_arr = arr'(m - 1 := Min_mset (arr_mset arr l m))"
  shows "arr_mset arr l r = arr_mset mod_arr l r"
proof -
  let ?min = "{#Min_mset (arr_mset arr l m)#}"
  let ?new_arr_mset = "arr_mset mod_arr"
  have middle: "?new_arr_mset (m - 1) m = ?min"
    by (simp add: assms(5))
  have first_half: "?new_arr_mset l (m - 1) = arr_mset arr l m - ?min"
    by (simp add: assms(3,5) mset_ran_subst_outside)
  hence "?new_arr_mset l m = ?new_arr_mset l (m - 1) + ?new_arr_mset (m - 1) m"
    by (metis assms(1,3,5) diff_add_cancel middle arr_mset_append_alt zle_diff1_eq)
  hence first_half_middle: "?new_arr_mset l m = arr_mset arr l m"
    using middle first_half assms(1) by simp

  hence "mod_arr = arr on - {l..<m}"
    using assms(1,4,5) eq_on_sym eq_on_trans by auto
  then have second_half: "arr_mset arr m r = arr_mset mod_arr m r"
    by (simp add: eq_on_def mset_ran_cong)

  then show ?thesis
    by (metis arr_mset_split assms(1,2) first_half_middle le_less)
qed

text \<open>This lemma states, that each loop iteration leaves the growing second half of the array 
      sorted in descending order.\<close>
lemma heap_sort_second_half_sorted_step: 
  fixes arr::"int \<Rightarrow> int"
  assumes
    "l\<^sub>0 < m" "m \<le> r\<^sub>0"
    "arr = arr' on - {l\<^sub>0..<m}"
    "\<forall>i. \<forall>j. bounded m r\<^sub>0 i \<longrightarrow> bounded m r\<^sub>0 j \<longrightarrow>  i < j \<longrightarrow> arr j \<le> arr i"
    "\<forall>x\<in>#arr_mset arr l\<^sub>0 m. \<forall>y\<in>#arr_mset arr m r\<^sub>0. \<not> x < y"
    "bounded (m - 1) r\<^sub>0 i" 
    "bounded (m - 1) r\<^sub>0 j" 
    "i < j"
    "mod_arr = (arr'(m - 1 := Min_mset (arr_mset arr l\<^sub>0 m)))"
  shows "mod_arr j \<le> mod_arr i"
proof -
  have second_half_eq: "mod_arr = arr on {m..< r\<^sub>0}" 
    using assms(3, 9) unfolding eq_on_def by simp
  have j_stricter_bound: "bounded m r\<^sub>0 j"
    using assms(6-8) by simp
  then have el_at_j: "mod_arr j \<in># arr_mset arr m r\<^sub>0"
    using eq_onD second_half_eq by fastforce
  then show ?thesis 
  proof(cases)
    assume "i = (m-1)"
    then have "mod_arr i \<in># arr_mset arr l\<^sub>0 m"
      by (simp add: assms(1, 9))
    then show ?thesis
      using assms(5) el_at_j not_less by blast 
  next
    assume "i \<noteq> (m-1)"  
    then have "bounded m r\<^sub>0 i"
      using assms(6) by simp
    then show ?thesis 
      using assms(4, 8) eq_on_def j_stricter_bound second_half_eq by force
  qed
qed


text \<open>The following lemma shows that all elements in the first part of the array (the binary heap) 
      are bigger than the elements in the second part (the sorted part) after every iteration. This 
      lemma and the invariant of the \<open>heap_sort\<close> loop use \<open>\<not> x < y\<close> instead of \<open>x \<ge> y\<close> since 
      \<open>vcg_cs\<close> doesn't terminate in the latter case.\<close>
lemma heap_sort_fst_part_bigger_snd_part_step:
  fixes arr::"int \<Rightarrow> int" 
  assumes
    "l\<^sub>0 < m"
    "m \<le> r\<^sub>0"
    "arr_mset arr' l\<^sub>0 (m - 1) = arr_mset arr l\<^sub>0 m - {#Min_mset (arr_mset arr l\<^sub>0 m)#}"
    "arr = arr' on - {l\<^sub>0..<m}"
    "\<forall>x\<in>#arr_mset arr l\<^sub>0 m. \<forall>y\<in>#arr_mset arr m r\<^sub>0. \<not> x < y"
    "mod_arr = arr'(m - 1 := Min_mset (arr_mset arr l\<^sub>0 m))"
    "x\<in>#arr_mset mod_arr l\<^sub>0 (m - 1)"
    "y\<in>#arr_mset mod_arr (m - 1) r\<^sub>0"
  shows "\<not> x < y"
proof -
  have "{m..<r\<^sub>0} \<subseteq> - {l\<^sub>0..<m}" 
    by auto
  hence "arr' = arr on {m..<r\<^sub>0}" 
    using assms(4) eq_on_sym eq_on_subset by blast
  hence arr_eq_on: "mod_arr = arr on {m..<r\<^sub>0}"
    by (simp add: assms(6))
  hence same_mset: "arr_mset mod_arr m r\<^sub>0 = arr_mset arr m r\<^sub>0"
    using mset_ran_cong by blast
  have "x \<in># arr_mset arr l\<^sub>0 m" using same_mset assms
    by (metis assms(3,6,7) add_mset_remove_trivial_eq lran_upd_outside(2)
        mset_lran cancel_ab_semigroup_add_class.diff_right_commute
        diff_single_trivial multi_self_add_other_not_self order_refl)
  then have x_bigger_min: "x \<ge> Min_mset (arr_mset arr l\<^sub>0 m)"
    using Min_le by blast 
  have y_smaller_min: "y \<le> Min_mset (arr_mset arr l\<^sub>0 m)" 
  proof(cases "y = mod_arr (m - 1)")
    case False
    hence "y\<in>#arr_mset mod_arr (m - 1) r\<^sub>0 - {#mod_arr (m - 1)#}"
      by (metis assms(8) diff_single_trivial insert_DiffM insert_noteq_member)
    then have "y\<in>#arr_mset arr m r\<^sub>0"
      by (simp add: assms(2) intvs_decr_l mset_ran_insert same_mset)
    then show ?thesis
      using assms(1) assms(5) by fastforce 
  qed (simp add: assms(6))
  then show ?thesis
    using x_bigger_min by linarith 
qed

subsubsection \<open>Implementation\<close>
text \<open>Now finally the correctness of the \<open>heap_sort\<close> is shown. As mentioned, it starts by 
      transforming the array into a minimum heap using @{const "make_heap"}. Then in each 
      iteration it removes the first element from the heap with @{const "del_min"} after its value 
      was retrieved with @{const "get_min"}. This value is then put at the position freed by 
      @{const "del_min"}.\<close>
program_spec heap_sort
  assumes "l \<le> r"  
    ensures "array_is_sorted (\<ge>) arr l\<^sub>0 r\<^sub>0 \<and> 
             arr_mset arr\<^sub>0 l\<^sub>0 r\<^sub>0 = arr_mset arr l\<^sub>0 r\<^sub>0 \<and> 
             arr\<^sub>0 = arr on - {l\<^sub>0 ..<r\<^sub>0 } \<and> l = l\<^sub>0 \<and> r = r\<^sub>0"
  for l r arr[]
  defines \<open>
    arr = make_heap(arr, l, r);
    m = r;
    while (m > l)
      @variant \<open>m - l + 1\<close> 
      @invariant \<open>is_heap (\<le>) arr l m \<and>
        array_is_sorted (\<ge>) arr m r\<^sub>0 \<and>
        (\<forall>x \<in># arr_mset arr l\<^sub>0 m. \<forall>y \<in># arr_mset arr m r\<^sub>0. \<not> x < y) \<and>
        arr_mset arr\<^sub>0 l\<^sub>0 r\<^sub>0 = arr_mset arr l\<^sub>0 r\<^sub>0 \<and> 
        l \<le> m \<and> m \<le> r\<^sub>0 \<and> l = l\<^sub>0 \<and> arr\<^sub>0 = arr on - {l\<^sub>0 ..<r\<^sub>0}\<close>
    {
      min = get_min(arr, l, m);
      (arr, l, m) = del_min(arr, l, m);
      arr[m] = min 
    }
  \<close>
  apply vcg_cs
  subgoal unfolding array_is_sorted_def by simp
  subgoal
    apply(intro conjI)
    subgoal unfolding is_partial_heap_def by simp
    subgoal unfolding array_is_sorted_def using heap_sort_second_half_sorted_step
      by blast
    subgoal using heap_sort_fst_part_bigger_snd_part_step by blast
    subgoal using heap_sort_mset_step by blast
    subgoal unfolding eq_on_def
      by (metis ComplD ComplI atLeastLessThan_iff less_le_trans)
    done
  done
end
