(*  Title:      Imperative_Insertion_Sort
    Author:     Christian Sternagel
*)

section \<open>Insertion Sort\<close>

theory Imperative_Insertion_Sort
imports
  Imperative_Loops
  "HOL-Library.Multiset"
begin

subsection \<open>The Algorithm\<close>

abbreviation
  array_update :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array Heap" ("(_.'(_') \<leftarrow>/ _)" [1000, 0, 13] 14)
where
  "a.(i) \<leftarrow> x \<equiv> Array.upd i x a"

abbreviation array_nth :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" ("_.'(_')" [1000, 0] 14)
where
  "a.(i) \<equiv> Array.nth a i"

text \<open>
  A definition of insertion sort as given by Cormen et al.\ in \emph{Introduction to Algorithms}.
  Compared to the informal textbook version the variant below is a bit unwieldy due to explicit
  dereferencing of variables on the heap.

  To avoid ambiguities with existing syntax we use OCaml's notation for accessing (@{term "a.(i)"})
  and updating (@{term "a.(i) \<leftarrow> x"}) an array @{term a} at position @{term i}.
\<close>
definition
  "insertion_sort a = do {
    l \<leftarrow> Array.len a;
    for [1 ..< l] (\<lambda>j. do {
      \<comment> \<open>Insert \<open>a[j]\<close> into the sorted subarray \<open>a[1 .. j - 1].\<close>\<close>
      key \<leftarrow> a.(j);
      i \<leftarrow> ref j;
      while (do {
        i' \<leftarrow> ! i;
        if i' > 0 then do {x \<leftarrow> a.(i' - 1); return (x > key)}
        else return False})
      (do {
        i' \<leftarrow> ! i;
        x \<leftarrow> a.(i' - 1);
        a.(i') \<leftarrow> x;
        i := i' - 1
      });
      i' \<leftarrow> ! i;
      a.(i') \<leftarrow> key
    })
  }"

text \<open>
  The following definitions decompose the nested loops of the algorithm into more manageable chunks.
\<close>
definition "shiftr_p a (key::'a::{heap, linorder}) i =
  (do {i' \<leftarrow> ! i; if i' > 0 then do {x \<leftarrow> a.(i' - 1); return (x > key)} else return False})"

definition "shiftr_f a i = do {
  i' \<leftarrow> ! i;
  x \<leftarrow> a.(i' - 1);
  a.(i') \<leftarrow> x;
  i := i' - 1
}"

definition "shiftr a key i = while (shiftr_p a key i) (shiftr_f a i)"

definition "insert_elt a = (\<lambda>j. do {
  key \<leftarrow> a.(j);
  i \<leftarrow> ref j;
  shiftr a key i;
  i' \<leftarrow> ! i;
  a.(i') \<leftarrow> key
})"

definition "sort_upto a = (\<lambda>l. for [1 ..< l] (insert_elt a))"

lemma insertion_sort_alt_def:
  "insertion_sort a = (Array.len a \<bind> sort_upto a)"
  by (simp add: insertion_sort_def sort_upto_def shiftr_def shiftr_p_def shiftr_f_def insert_elt_def)


subsection \<open>Partial Correctness\<close>

lemma effect_shiftr_f:
  assumes "effect (shiftr_f a i) h h' u"
  shows "Ref.get h' i = Ref.get h i - 1 \<and>
    Array.get h' a = list_update (Array.get h a) (Ref.get h i) (Array.get h a ! (Ref.get h i - 1))"
  using assms by (auto simp: shiftr_f_def elim!: effect_elims)

lemma success_shiftr_p:
  "Ref.get h i < Array.length h a \<Longrightarrow> success (shiftr_p a key i) h"
  by (auto simp: success_def shiftr_p_def execute_simps)

interpretation ro_shiftr_p: ro_cond "shiftr_p a key i" for a key i
  by (unfold_locales)
     (auto simp: shiftr_p_def success_def execute_simps execute_bind_case split: option.split, metis effectI effect_nthE)

(*[0 .. j - 1]*)
definition [simp]: "ini h a j = take j (Array.get h a)"
(*[0 .. i - 1]*)
definition [simp]: "left h a i = take (Ref.get h i) (Array.get h a)"
(*[i+1 .. j]*)
definition [simp]: "right h a j i = take (j - Ref.get h i) (drop (Ref.get h i + 1) (Array.get h a))"
(*[0 .. i - 1, i + 1 .. j]*)
definition [simp]: "both h a j i = left h a i @ right h a j i"

lemma effect_shiftr:
  assumes "Ref.get h i = j" (is "?i h = _")
    and "j < Array.length h a"
    and "sorted (take j (Array.get h a))"
    and "effect (while (shiftr_p a key i) (shiftr_f a i)) h h' u"
  shows "Array.length h a = Array.length h' a \<and>
    ?i h' \<le> j \<and>
    mset (list_update (Array.get h a) j key) =
      mset (list_update (Array.get h' a) (?i h') key) \<and>
    ini h a j = both h' a j i \<and>
    sorted (both h' a j i) \<and>
    (\<forall>x \<in> set (right h' a j i). x > key)"
using assms(4, 2)
proof (induction rule: ro_shiftr_p.effect_while_induct)
  case base
  show ?case using assms by auto
next
  case (step h' h'' u)
  from \<open>success (shiftr_p a key i) h'\<close> and \<open>cond (shiftr_p a key i) h'\<close>
    have "?i h' > 0" and
    key: "Array.get h' a ! (?i h' - 1) > key"
    by (auto dest!: ro_shiftr_p.success_cond_effect)
       (auto simp: shiftr_p_def elim!: effect_elims effect_ifE)
  from effect_shiftr_f [OF \<open>effect (shiftr_f a i) h' h'' u\<close>]
    have [simp]: "?i h'' = ?i h' - 1"
    "Array.get h'' a = list_update (Array.get h' a) (?i h') (Array.get h' a ! (?i h' - 1))"
    by auto
  from step have *: "?i h' < length (Array.get h' a)"
    and **: "?i h' - (Suc 0) \<le> ?i h'" "?i h' \<le> length (Array.get h' a)"
    and "?i h' \<le> j"
    and "?i h' < Suc j"
    and IH: "ini h a j = both h' a j i"
    by (auto simp add: Array.length_def)
  have "Array.length h a = Array.length h'' a" using step by (simp add: Array.length_def)
  moreover
  have "?i h'' \<le> j" using step by auto
  moreover
  have "mset (list_update (Array.get h a) j key) =
    mset (list_update (Array.get h'' a) (?i h'') key)"
  proof -
    have "?i h' < length (Array.get h' a)"
      and "?i h' - 1 < length (Array.get h' a)" using * by auto
    then show ?thesis
      using step by (simp add: mset_update ac_simps nth_list_update)
  qed
  moreover
  have "ini h a j = both h'' a j i"
    using \<open>0 < ?i h'\<close> and \<open>?i h' \<le> j\<close> and \<open>?i h' < length (Array.get h' a)\<close> and ** and IH
    by (auto simp: upd_conv_take_nth_drop Suc_diff_le min_absorb1)
       (metis Suc_lessD Suc_pred take_Suc_conv_app_nth)

  moreover
  have "sorted (both h'' a j i)"
    using step and \<open>0 < ?i h'\<close> and \<open>?i h' \<le> j\<close> and \<open>?i h' < length (Array.get h' a)\<close> and **
    by (auto simp: IH upd_conv_take_nth_drop Suc_diff_le min_absorb1)
       (metis Suc_lessD Suc_pred append.simps append_assoc take_Suc_conv_app_nth)
  moreover
  have "\<forall>x \<in> set (right h'' a j i). x > key"
    using step and \<open>0 < ?i h'\<close> and \<open>?i h' < length (Array.get h' a)\<close> and key
    by (auto simp: upd_conv_take_nth_drop Suc_diff_le)
  ultimately show ?case by blast
qed

lemma sorted_take_nth:
  assumes "0 < i" and "i < length xs" and "xs ! (i - 1) \<le> y"
    and "sorted (take i xs)"
  shows "\<forall>x \<in> set (take i xs). x \<le> y"
proof -
  have "take i xs = take (i - 1) xs @ [xs ! (i - 1)]"
    using \<open>0 < i\<close> and \<open>i < length xs\<close>
    by (metis Suc_diff_1 less_imp_diff_less take_Suc_conv_app_nth)
  then show ?thesis
    using \<open>sorted (take i xs)\<close> and \<open>xs ! (i - 1) \<le>y\<close>
    by (auto simp: sorted_append)
qed

lemma effect_for_insert_elt:
  assumes "l \<le> Array.length h a"
    and "1 \<le> l"
    and "effect (for [1 ..< l] (insert_elt a)) h h' u"
  shows "Array.length h a = Array.length h' a \<and>
    sorted (take l (Array.get h' a)) \<and>
    mset (Array.get h a) = mset (Array.get h' a)"
using assms(2-)
proof (induction l h' rule: effect_for_induct)
  case base
  show ?case by (cases "Array.get h a") simp_all
next
  case (step j h' h'' u)
  with assms(1) have "j < Array.length h' a" by auto
  from step have sorted: "sorted (take j (Array.get h' a))" by blast
  from step(3) [unfolded insert_elt_def]
    obtain key and h\<^sub>1 and i and h\<^sub>2 and i'
    where key: "key = Array.get h' a ! j"
      and "effect (ref j) h' h\<^sub>1 i"
      and ref\<^sub>1: "Ref.get h\<^sub>1 i = j"
      and shiftr': "effect (shiftr a key i) h\<^sub>1 h\<^sub>2 ()"
      and [simp]: "Ref.get h\<^sub>2 i = i'"
      and [simp]: "h'' = Array.update a i' key h\<^sub>2"
      and "i' < Array.length h\<^sub>2 a"
      by (elim effect_bindE effect_nthE effect_lookupE effect_updE)
         (auto intro: effect_intros, metis effect_refE)

  from \<open>effect (ref j) h' h\<^sub>1 i\<close> have [simp]: "Array.get h\<^sub>1 a = Array.get h' a"
    by (metis array_get_alloc effectE execute_ref option.sel)

  have [simp]: "Array.length h\<^sub>1 a = Array.length h' a" by (simp add: Array.length_def)

  from step and assms(1)
    have "j < Array.length h\<^sub>1 a" "sorted (take j (Array.get h\<^sub>1 a))" by auto
  note shiftr = effect_shiftr [OF ref\<^sub>1 this shiftr' [unfolded shiftr_def], simplified]
  have "i' \<le> j" using shiftr by simp

  have "i' < length (Array.get h\<^sub>2 a)"
    by (metis \<open>i' < Array.length h\<^sub>2 a\<close> length_def)
  have [simp]: "min (Suc j) i' = i'" using \<open>i' \<le> j\<close> by simp
  have [simp]: "min (length (Array.get h\<^sub>2 a)) i' = i'"
    using \<open>i' < length (Array.get h\<^sub>2 a)\<close> by (simp)
  have take_Suc_j: "take (Suc j) (list_update (Array.get h\<^sub>2 a) i' key) =
    take i' (Array.get h\<^sub>2 a) @ key # take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a))"
    unfolding upd_conv_take_nth_drop [OF \<open>i' < length (Array.get h\<^sub>2 a)\<close>]
    by (auto) (metis Suc_diff_le \<open>i' \<le> j\<close> take_Suc_Cons)

  have "Array.length h a = Array.length h'' a"
    using shiftr by (auto) (metis step.IH)
  moreover
  have "mset (Array.get h a) = mset (Array.get h'' a)"
    using shiftr and step by (simp add: key)
  moreover
  have "sorted (take (Suc j) (Array.get h'' a))"
  proof -
    from ro_shiftr_p.effect_while_post [OF shiftr' [unfolded shiftr_def]]
      have "i' = 0 \<or> (0 < i' \<and> key \<ge> Array.get h\<^sub>2 a ! (i' - 1))"
      by (auto dest!: ro_shiftr_p.success_not_cond_effect)
         (auto elim!: effect_elims simp: shiftr_p_def)
    then show ?thesis
    proof
      assume [simp]: "i' = 0"
      have *: "take (Suc j) (list_update (Array.get h\<^sub>2 a) 0 key) =
        key # take j (drop 1 (Array.get h\<^sub>2 a))"
        by (simp) (metis \<open>i' = 0\<close> append_Nil take_Suc_j diff_zero take_0)
      from sorted and shiftr
        have "sorted (take j (drop 1 (Array.get h\<^sub>2 a)))"
        and "\<forall>x \<in> set (take j (drop 1 (Array.get h\<^sub>2 a))). key < x" by simp_all
      then have "sorted (key # take j (drop 1 (Array.get h\<^sub>2 a)))"
        by (metis less_imp_le sorted.simps(2))
      then show ?thesis by (simp add: *)
    next
      assume "0 < i' \<and> key \<ge> Array.get h\<^sub>2 a ! (i' - 1)"
      moreover
      have "sorted (take i' (Array.get h\<^sub>2 a) @ take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a)))"
        and "\<forall>x \<in> set (take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a))). key < x"
        using shiftr by auto
      ultimately have "\<forall>x \<in> set (take i' (Array.get h\<^sub>2 a)). x \<le> key"
        using sorted_take_nth [OF _ \<open>i' < length (Array.get h\<^sub>2 a)\<close>, of key]
        by (simp add: sorted_append)
      then show ?thesis
        using shiftr by (auto simp: take_Suc_j sorted_append less_imp_le)
    qed
  qed
  ultimately
  show ?case by blast
qed

lemma effect_insertion_sort:
  assumes "effect (insertion_sort a) h h' u"
  shows "mset (Array.get h a) = mset (Array.get h' a) \<and> sorted (Array.get h' a)"
  using assms
  apply (cases "Array.length h a")
  apply (auto elim!: effect_elims simp: insertion_sort_def Array.length_def)[1]
  unfolding insertion_sort_def
  unfolding shiftr_p_def [symmetric] shiftr_f_def [symmetric]
  unfolding shiftr_def [symmetric] insert_elt_def [symmetric]
  apply (elim effect_elims)
  apply (simp only:)
  apply (subgoal_tac "Suc nat \<le> Array.length h a")
  apply (drule effect_for_insert_elt)
  apply (auto simp: Array.length_def)
done


subsection \<open>Total Correctness\<close>

lemma success_shiftr_f:
  assumes "Ref.get h i < Array.length h a"
  shows "success (shiftr_f a i) h"
  using assms by (auto simp: success_def shiftr_f_def execute_simps)

lemma success_shiftr:
  assumes "Ref.get h i < Array.length h a"
  shows "success (while (shiftr_p a key i) (shiftr_f a i)) h"
proof -
  have "wf (measure (\<lambda>h. Ref.get h i))" by (metis wf_measure)
  then show ?thesis
  proof (induct taking: "\<lambda>h. Ref.get h i < Array.length h a" rule: ro_shiftr_p.success_while_induct)
    case (success_cond h)
    then show ?case by (metis success_shiftr_p)
  next
    case (success_body h)
    then show ?case by (blast intro: success_shiftr_f)
  next
    case (step h h' r)
    then show ?case
      by (auto dest!: effect_shiftr_f ro_shiftr_p.success_cond_effect simp: length_def)
         (auto simp: shiftr_p_def elim!: effect_elims effect_ifE)
  qed fact
qed

lemma effect_shiftr_index:
  assumes "effect (shiftr a key i) h h' u"
  shows "Ref.get h' i \<le> Ref.get h i"
  using assms unfolding shiftr_def
  by (induct h' rule: ro_shiftr_p.effect_while_induct) (auto dest: effect_shiftr_f)

lemma effect_shiftr_length:
  assumes "effect (shiftr a key i) h h' u"
  shows "Array.length h' a = Array.length h a"
  using assms unfolding shiftr_def
  by (induct h' rule: ro_shiftr_p.effect_while_induct) (auto simp: length_def dest: effect_shiftr_f)

lemma success_insert_elt:
  assumes "k < Array.length h a"
  shows "success (insert_elt a k) h"
proof -
  obtain key where "effect (a.(k)) h h key"
    using assms by (auto intro: effect_intros)
  moreover
  obtain i and h\<^sub>1 where "effect (ref k) h h\<^sub>1 i"
    and [simp]: "Ref.get h\<^sub>1 i = k"
    and [simp]: "Array.length h\<^sub>1 a = Array.length h a"
    by (auto simp: ref_def length_def) (metis Ref.get_alloc array_get_alloc effect_heapI)
  moreover
  obtain h\<^sub>2 where *: "effect (shiftr a key i) h\<^sub>1 h\<^sub>2 ()"
    using success_shiftr [of h\<^sub>1 i a key] and assms
    by (auto simp: success_def effect_def shiftr_def)
  moreover
  have "effect (! i) h\<^sub>2 h\<^sub>2 (Ref.get h\<^sub>2 i)"
    and "Ref.get h\<^sub>2 i \<le> Ref.get h\<^sub>1 i"
    and "Ref.get h\<^sub>2 i < Array.length h\<^sub>2 a"
    using effect_shiftr_index [OF *] and effect_shiftr_length [OF *] and assms
    by (auto intro!: effect_intros)
  moreover
  then obtain h\<^sub>3 and r where "effect (a.(Ref.get h\<^sub>2 i) \<leftarrow> key) h\<^sub>2 h\<^sub>3 r"
    using assms by (auto simp: effect_def execute_simps)
  ultimately
  have "effect (insert_elt a k) h h\<^sub>3 r"
    by (auto simp: insert_elt_def intro: effect_intros)
  then show ?thesis by (metis effectE)
qed

lemma for_insert_elt_correct:
  assumes "l \<le> Array.length h a"
    and "1 \<le> l"
  shows "\<exists>h'. effect (for [1 ..< l] (insert_elt a)) h h' () \<and>
    Array.length h a = Array.length h' a \<and>
    sorted (take l (Array.get h' a)) \<and>
    mset (Array.get h a) = mset (Array.get h' a)"
using assms(2)
proof (induction rule: for_induct)
  case (succeed k h)
  then show ?case using assms and success_insert_elt [of k h a] by auto
next
  case base
  show ?case by (cases "Array.get h a") simp_all
next
  case (step j h' h'' u)
  with assms(1) have "j < Array.length h' a" by auto
  from step have sorted: "sorted (take j (Array.get h' a))" by blast
  from step(4) [unfolded insert_elt_def]
    obtain key and h\<^sub>1 and i and h\<^sub>2 and i'
    where key: "key = Array.get h' a ! j"
      and "effect (ref j) h' h\<^sub>1 i"
      and ref\<^sub>1: "Ref.get h\<^sub>1 i = j"
      and shiftr': "effect (shiftr a key i) h\<^sub>1 h\<^sub>2 ()"
      and [simp]: "Ref.get h\<^sub>2 i = i'"
      and [simp]: "h'' = Array.update a i' key h\<^sub>2"
      and "i' < Array.length h\<^sub>2 a"
      by (elim effect_bindE effect_nthE effect_lookupE effect_updE)
         (auto intro: effect_intros, metis effect_refE)

  from \<open>effect (ref j) h' h\<^sub>1 i\<close> have [simp]: "Array.get h\<^sub>1 a = Array.get h' a"
    by (metis array_get_alloc effectE execute_ref option.sel)

  have [simp]: "Array.length h\<^sub>1 a = Array.length h' a" by (simp add: Array.length_def)

  from step and assms(1)
    have "j < Array.length h\<^sub>1 a" "sorted (take j (Array.get h\<^sub>1 a))" by auto
  note shiftr = effect_shiftr [OF ref\<^sub>1 this shiftr' [unfolded shiftr_def], simplified]
  have "i' \<le> j" using shiftr by simp

  have "i' < length (Array.get h\<^sub>2 a)"
    by (metis \<open>i' < Array.length h\<^sub>2 a\<close> length_def)
  have [simp]: "min (Suc j) i' = i'" using \<open>i' \<le> j\<close> by simp
  have [simp]: "min (length (Array.get h\<^sub>2 a)) i' = i'"
    using \<open>i' < length (Array.get h\<^sub>2 a)\<close> by (simp)
  have take_Suc_j: "take (Suc j) (list_update (Array.get h\<^sub>2 a) i' key) =
    take i' (Array.get h\<^sub>2 a) @ key # take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a))"
    unfolding upd_conv_take_nth_drop [OF \<open>i' < length (Array.get h\<^sub>2 a)\<close>]
    by (auto) (metis Suc_diff_le \<open>i' \<le> j\<close> take_Suc_Cons)

  have "Array.length h a = Array.length h'' a"
    using shiftr by (auto) (metis step.hyps(1))
  moreover
  have "mset (Array.get h a) = mset (Array.get h'' a)"
    using shiftr and step by (simp add: key)
  moreover
  have "sorted (take (Suc j) (Array.get h'' a))"
  proof -
    from ro_shiftr_p.effect_while_post [OF shiftr' [unfolded shiftr_def]]
      have "i' = 0 \<or> (0 < i' \<and> key \<ge> Array.get h\<^sub>2 a ! (i' - 1))"
      by (auto dest!: ro_shiftr_p.success_not_cond_effect)
         (auto elim!: effect_elims simp: shiftr_p_def)
    then show ?thesis
    proof
      assume [simp]: "i' = 0"
      have *: "take (Suc j) (list_update (Array.get h\<^sub>2 a) 0 key) =
        key # take j (drop 1 (Array.get h\<^sub>2 a))"
        by (simp) (metis \<open>i' = 0\<close> append_Nil take_Suc_j diff_zero take_0)
      from sorted and shiftr
        have "sorted (take j (drop 1 (Array.get h\<^sub>2 a)))"
        and "\<forall>x \<in> set (take j (drop 1 (Array.get h\<^sub>2 a))). key < x" by simp_all
      then have "sorted (key # take j (drop 1 (Array.get h\<^sub>2 a)))"
        by (metis less_imp_le sorted.simps(2))
      then show ?thesis by (simp add: *)
    next
      assume "0 < i' \<and> key \<ge> Array.get h\<^sub>2 a ! (i' - 1)"
      moreover
      have "sorted (take i' (Array.get h\<^sub>2 a) @ take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a)))"
        and "\<forall>x \<in> set (take (j - i') (drop (Suc i') (Array.get h\<^sub>2 a))). key < x"
        using shiftr by auto
      ultimately have "\<forall>x \<in> set (take i' (Array.get h\<^sub>2 a)). x \<le> key"
        using sorted_take_nth [OF _ \<open>i' < length (Array.get h\<^sub>2 a)\<close>, of key]
        by (simp add: sorted_append)
      then show ?thesis
        using shiftr by (auto simp: take_Suc_j sorted_append less_imp_le)
    qed
  qed
  ultimately
  show ?case by blast
qed

lemma insertion_sort_correct:
  "\<exists>h'. effect (insertion_sort a) h h' u \<and>
    mset (Array.get h a) = mset (Array.get h' a) \<and>
    sorted (Array.get h' a)"
proof (cases "Array.length h a = 0")
  assume "Array.length h a = 0"
  then have "effect (insertion_sort a) h h ()"
    and "mset (Array.get h a) = mset (Array.get h a)"
    and "sorted (Array.get h a)"
    by (auto simp: insertion_sort_def length_def intro!: effect_intros)
  then show ?thesis by auto
next
  assume "Array.length h a \<noteq> 0"
  then have "1 \<le> Array.length h a" by auto
  from for_insert_elt_correct [OF le_refl this]
    show ?thesis
    by (auto simp: insertion_sort_alt_def sort_upto_def)
       (metis One_nat_def effect_bindI effect_insertion_sort effect_lengthI insertion_sort_alt_def sort_upto_def)
qed

export_code insertion_sort in Haskell

end

