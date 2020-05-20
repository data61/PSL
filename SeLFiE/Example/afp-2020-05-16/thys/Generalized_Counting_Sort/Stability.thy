(*  Title:       An Efficient Generalization of Counting Sort for Large, possibly Infinite Key Ranges
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Proof of algorithm's stability"

theory Stability
  imports Sorting
begin

text \<open>
\null

In this section, it is formally proven that GCsort is \emph{stable}, viz. that the sublist of the
output of function @{const gcsort} built by picking out the objects having a given key matches the
sublist of the input objects' list built in the same way.

Here below, steps 5, 6, and 7 of the proof method are accomplished. Particularly, @{text stab_inv}
is the predicate that will be shown to be invariant over inductive set @{const gcsort_set}.

\null
\<close>

fun stab_inv :: "('b \<Rightarrow> 'a list) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<times> nat list \<times> 'a list \<Rightarrow>
  bool" where
"stab_inv f key (u, ns, xs) = (\<forall>k. [x\<leftarrow>xs. key x = k] = f k)"

lemma gcsort_stab_input:
 "stab_inv (\<lambda>k. [x\<leftarrow>xs. key x = k]) key (0, [length xs], xs)"
by simp

lemma gcsort_stab_intro:
 "stab_inv f key t \<Longrightarrow> [x\<leftarrow>gcsort_out t. key x = k] = f k"
by (cases t, simp add: gcsort_out_def)

text \<open>
\null

In what follows, step 9 of the proof method is accomplished.

First, lemma @{text fill_offs_enum_stable} proves that function @{const fill}, if its input offsets'
list is computed via the composition of functions @{const offs} and @{const enum}, does not modify
the sublist of its input objects' list formed by the objects having a given key. Moreover, lemmas
@{text mini_stable} and @{text maxi_stable} prove that the extraction of the leftmost minimum and
the rightmost maximum from an objects' list through functions @{const mini} and @{const maxi} is
endowed with the same property.

These lemmas are then used to prove lemma @{text gcsort_stab_inv}, which states that the sublist of
the objects having a given key within the objects' list is still the same after any recursive round.

\null
\<close>

lemma fill_stable [rule_format]:
  assumes
    A: "index_less index key" and
    B: "index_same index key"
  shows
   "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    ns \<noteq> [] \<longrightarrow>
    offs_pred ns ub xs index key mi ma \<longrightarrow>
      map the [w\<leftarrow>fill xs ns index key ub mi ma. \<exists>x. w = Some x \<and> key x = k] =
        [x\<leftarrow>xs. k = key x]"
proof (induction xs arbitrary: ns, simp_all add: Let_def, rule conjI,
 (rule_tac [!] impI)+, (erule_tac [!] conjE)+, simp_all)
  fix x xs and ns :: "nat list"
  let ?i = "index key x (length ns) mi ma"
  let ?ns' = "ns[?i := Suc (ns ! ?i)]"
  let ?ws = "[w\<leftarrow>fill xs ?ns' index key ub mi ma.
    \<exists>y. w = Some y \<and> key y = key x]"
  let ?ws' = "[w\<leftarrow>(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x].
    \<exists>y. w = Some y \<and> key y = key x]"
  assume
    C: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    D: "mi \<le> key x" and
    E: "key x \<le> ma" and
    F: "ns \<noteq> []" and
    G: "offs_pred ns ub (x # xs) index key mi ma"
  have H: "?i < length ns"
    using A and D and E and F by (simp add: index_less_def)
  assume "\<And>ns. ns \<noteq> [] \<longrightarrow> offs_pred ns ub xs index key mi ma \<longrightarrow>
    map the [w\<leftarrow>fill xs ns index key ub mi ma.
      \<exists>y. w = Some y \<and> key y = key x] =
    [y\<leftarrow>xs. key x = key y]"
  moreover have I: "offs_pred ?ns' ub xs index key mi ma"
    using G and H by (rule_tac offs_pred_cons, simp_all)
  ultimately have J: "map the ?ws = [y\<leftarrow>xs. key x = key y]"
    using F by simp
  have "ns ! ?i + offs_num (length ns) (x # xs) index key mi ma ?i \<le> ub"
    using G and H by (rule offs_pred_ub, simp add: offs_num_cons)
  hence K: "ns ! ?i < ub"
    by (simp add: offs_num_cons)
  moreover from this have
    L: "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! (ns ! ?i) = Some x"
    by (subst nth_list_update_eq, simp_all add: fill_length)
  ultimately have "0 < length ?ws'"
    by (simp add: length_filter_conv_card card_gt_0_iff,
     rule_tac exI [where x = "ns ! ?i"], simp add: fill_length)
  hence "\<exists>w ws. ?ws' = w # ws"
    by (rule_tac list.exhaust [of ?ws'], simp_all)
  then obtain w and ws where "?ws' = w # ws" by blast
  hence "\<exists>us vs y.
    (fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] = us @ w # vs \<and>
    (\<forall>u \<in> set us. \<forall>y. u = Some y \<longrightarrow> key y \<noteq> key x) \<and>
    w = Some y \<and> key y = key x \<and>
    ws = [w\<leftarrow>vs. \<exists>y. w = Some y \<and> key y = key x]"
    (is "\<exists>us vs y. ?P us vs y")
    by (simp add: filter_eq_Cons_iff, blast)
  then obtain us and vs and y where M: "?P us vs y" by blast
  let ?A = "{i. i < length ns \<and> 0 < offs_num (length ns) xs index key mi ma i \<and>
    ns ! i \<le> length us}"
  have "length us = ns ! ?i"
  proof (rule ccontr, erule neqE, cases "?A = {}",
   cases "0 < offs_num (length ns) xs index key mi ma 0", simp_all only: not_gr0)
    assume
      N: "length us < ns ! ?i" and
      O: "?A = {}" and
      P: "0 < offs_num (length ns) xs index key mi ma 0"
    have "length us < ns ! 0"
    proof (rule ccontr, simp add: not_less)
      assume "ns ! 0 \<le> length us"
      with F and P have "0 \<in> ?A" by simp
      with O show False by blast
    qed
    hence "length us < ?ns' ! 0"
      using F by (cases ?i, simp_all)
    hence "offs_none ?ns' ub xs index key mi ma (length us)"
      using P by (simp add: offs_none_def)
    hence "fill xs ?ns' index key ub mi ma ! (length us) = None"
      using C and F and I by (rule_tac fill_none [OF A], simp_all)
    hence "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! (length us) = None"
      using N by simp
    thus False
      using M by simp
  next
    assume
      N: "length us < ns ! ?i" and
      O: "?A = {}" and
      P: "offs_num (length ns) xs index key mi ma 0 = 0"
    from K and N have "length us < offs_next ?ns' ub xs index key mi ma 0"
    proof (rule_tac ccontr, simp only: not_less offs_next_def split: if_split_asm)
      assume "offs_set_next ?ns' xs index key mi ma 0 \<noteq> {}"
        (is "?B \<noteq> _")
      hence "Min ?B \<in> ?B"
        by (rule_tac Min_in, simp)
      moreover assume "?ns' ! Min ?B \<le> length us"
      hence "ns ! Min ?B \<le> length us"
        using H by (cases "Min ?B = ?i", simp_all)
      ultimately have "Min ?B \<in> ?A" by simp
      with O show False by blast
    qed
    hence "offs_none ?ns' ub xs index key mi ma (length us)"
      using P by (simp add: offs_none_def)
    hence "fill xs ?ns' index key ub mi ma ! (length us) = None"
      using C and F and I by (rule_tac fill_none [OF A], simp_all)
    hence "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! (length us) = None"
      using N by simp
    thus False
      using M by simp
  next
    assume N: "length us < ns ! ?i"
    assume "?A \<noteq> {}"
    hence "Max ?A \<in> ?A"
      by (rule_tac Max_in, simp)
    moreover from this have O: "Max ?A \<noteq> ?i"
      using N by (rule_tac notI, simp)
    ultimately have "index key y (length ?ns') mi ma = Max ?A"
    using C proof (rule_tac fill_index [OF A _ I, where j = "length us"], simp_all,
     rule_tac ccontr, simp only: not_less not_le offs_next_def split: if_split_asm)
      assume "ub \<le> length us"
      with N have "ub < ns ! ?i" by simp
      with K show False by simp
    next
      let ?B = "offs_set_next ?ns' xs index key mi ma (Max ?A)"
      assume "?ns' ! Min ?B \<le> length us"
      hence "ns ! Min ?B \<le> length us"
        using H by (cases "Min ?B = ?i", simp_all)
      moreover assume "?B \<noteq> {}"
      hence P: "Min ?B \<in> ?B"
        by (rule_tac Min_in, simp)
      ultimately have "Min ?B \<in> ?A" by simp
      hence "Min ?B \<le> Max ?A"
        by (rule_tac Max_ge, simp)
      thus False
        using P by simp
    next
      have "fill xs ?ns' index key ub mi ma ! length us =
        (fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! length us"
        using N by simp
      thus "fill xs ?ns' index key ub mi ma ! length us = Some y"
        using M by simp
    qed
    moreover have "index key y (length ?ns') mi ma = ?i"
      using B and D and E and M by (cases "y = x", simp_all add:
       index_same_def)
    ultimately show False
      using O by simp
  next
    assume N: "ns ! ?i < length us"
    hence "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! (ns ! ?i) =
      us ! (ns ! ?i)"
      using M by (simp add: nth_append)
    hence "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] ! (ns ! ?i) \<in> set us"
      using N by simp
    thus False
      using L and M by blast
  qed
  hence "take (ns ! ?i) ((fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x]) = us"
    using M by simp
  hence N: "take (ns ! ?i) (fill xs ?ns' index key ub mi ma) = us" by simp
  have "fill xs ?ns' index key ub mi ma =
    take (ns ! ?i) (fill xs ?ns' index key ub mi ma) @
    fill xs ?ns' index key ub mi ma ! (ns ! ?i) #
    drop (Suc (ns ! ?i)) (fill xs ?ns' index key ub mi ma)"
    (is "_ = ?ts @ _ # ?ds")
    using K by (rule_tac id_take_nth_drop, simp add: fill_length)
  moreover have "fill xs ?ns' index key ub mi ma ! (ns ! ?i) = None"
    using C and D and E and F and G by (rule_tac fill_index_none [OF A],
     simp_all)
  ultimately have O: "fill xs ?ns' index key ub mi ma = us @ None # ?ds"
    using N by simp
  have "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] =
    ?ts @ Some x # ?ds"
    using K by (rule_tac upd_conv_take_nth_drop, simp add: fill_length)
  hence "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] =
    us @ Some x # ?ds"
    using N by simp
  hence "?ws' = Some x # [w\<leftarrow>?ds. \<exists>y. w = Some y \<and> key y = key x]"
    using M by simp
  also have "\<dots> = Some x # ?ws"
    using M by (subst (2) O, simp)
  finally show "map the ?ws' = x # [y\<leftarrow>xs. key x = key y]"
    using J by simp
next
  fix x xs and ns :: "nat list"
  let ?i = "index key x (length ns) mi ma"
  let ?ns' = "ns[?i := Suc (ns ! ?i)]"
  let ?ws = "[w\<leftarrow>fill xs ?ns' index key ub mi ma. \<exists>y. w = Some y \<and> key y = k]"
  let ?ws' = "[w\<leftarrow>(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x].
    \<exists>y. w = Some y \<and> key y = k]"
  assume
    C: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    D: "mi \<le> key x" and
    E: "key x \<le> ma" and
    F: "ns \<noteq> []" and
    G: "offs_pred ns ub (x # xs) index key mi ma" and
    H: "k \<noteq> key x"
  have I: "?i < length ns"
    using A and D and E and F by (simp add: index_less_def)
  assume "\<And>ns. ns \<noteq> [] \<longrightarrow> offs_pred ns ub xs index key mi ma \<longrightarrow>
    map the [w\<leftarrow>fill xs ns index key ub mi ma.
      \<exists>y. w = Some y \<and> key y = k] =
    [y\<leftarrow>xs. k = key y]"
  moreover have "offs_pred ?ns' ub xs index key mi ma"
    using G and I by (rule_tac offs_pred_cons, simp_all)
  ultimately have J: "map the ?ws = [y\<leftarrow>xs. k = key y]"
    using F by simp
  have "ns ! ?i + offs_num (length ns) (x # xs) index key mi ma ?i \<le> ub"
    using G and I by (rule offs_pred_ub, simp add: offs_num_cons)
  hence K: "ns ! ?i < ub"
    by (simp add: offs_num_cons)
  have "fill xs ?ns' index key ub mi ma =
    take (ns ! ?i) (fill xs ?ns' index key ub mi ma) @
    fill xs ?ns' index key ub mi ma ! (ns ! ?i) #
    drop (Suc (ns ! ?i)) (fill xs ?ns' index key ub mi ma)"
    (is "_ = ?ts @ _ # ?ds")
    using K by (rule_tac id_take_nth_drop, simp add: fill_length)
  moreover have "fill xs ?ns' index key ub mi ma ! (ns ! ?i) = None"
    using C and D and E and F and G by (rule_tac fill_index_none [OF A],
     simp_all)
  ultimately have L: "fill xs ?ns' index key ub mi ma = ?ts @ None # ?ds"
    by simp
  have "(fill xs ?ns' index key ub mi ma)[ns ! ?i := Some x] =
    ?ts @ Some x # ?ds"
    using K by (rule_tac upd_conv_take_nth_drop, simp add: fill_length)
  moreover have "?ws = [w\<leftarrow>?ts. \<exists>y. w = Some y \<and> key y = k] @
    [w\<leftarrow>?ds. \<exists>y. w = Some y \<and> key y = k]"
    by (subst L, simp)
  ultimately have "?ws' = ?ws"
    using H by simp
  thus "map the ?ws' = [y\<leftarrow>xs. k = key y]"
    using J by simp
qed

lemma fill_offs_enum_stable [rule_format]:
  assumes
    A: "index_less index key" and
    B: "index_same index key"
  shows
   "\<forall>x \<in> set xs. key x \<in> {mi..ma} \<Longrightarrow>
    0 < n \<Longrightarrow>
      [x\<leftarrow>map the (fill xs (offs (enum xs index key n mi ma) 0)
        index key (length xs) mi ma). key x = k] = [x\<leftarrow>xs. k = key x]"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> [_\<leftarrow>map the ?ys. _] = _"
   is "_ \<Longrightarrow> _ \<Longrightarrow> [_\<leftarrow>map the (fill _ ?ns _ _ _ _ _). _] = _")
proof (subst fill_stable [symmetric, OF A B, of xs mi ma ?ns], simp,
 simp only: length_greater_0_conv [symmetric] offs_length enum_length,
 rule offs_enum_pred [OF A], simp, subst filter_map,
 simp add: filter_eq_nths fill_length)
  assume
    C: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    D: "0 < n"
  have "{i. i < length xs \<and> key (the (?ys ! i)) = k} =
    {i. i < length xs \<and> (\<exists>x. ?ys ! i = Some x \<and> key x = k)}"
    (is "?A = ?B")
  proof (rule set_eqI, rule iffI, simp_all, erule_tac [!] conjE, erule_tac [2] exE,
   erule_tac [2] conjE, simp_all)
    fix i
    assume E: "i < length xs" and F: "key (the (?ys ! i)) = k"
    have "\<exists>x. ?ys ! i = Some x"
    proof (cases "?ys ! i", simp_all)
      assume "?ys ! i = None"
      moreover have "?ys ! i \<in> set ?ys"
        using E by (rule_tac nth_mem, simp add: fill_length)
      ultimately have "None \<in> set ?ys" by simp
      moreover have "count (mset ?ys) None = 0"
        using C and D by (rule_tac fill_offs_enum_count_none [OF A], simp)
      ultimately show False by simp
    qed
    then obtain x where "?ys ! i = Some x" ..
    moreover from this have "key x = k"
      using F by simp
    ultimately show "\<exists>x. ?ys ! i = Some x \<and> key x = k" by simp
  qed
  thus "map the (nths ?ys ?A) = map the (nths ?ys ?B)" by simp
qed

lemma mini_first [rule_format]:
 "xs \<noteq> [] \<longrightarrow> i < mini xs key \<longrightarrow>
    key (xs ! mini xs key) < key (xs ! i)"
by (induction xs arbitrary: i, simp_all add: Let_def, (rule impI)+,
 erule conjE, simp add: not_le nth_Cons split: nat.split)

lemma maxi_last [rule_format]:
 "xs \<noteq> [] \<longrightarrow> maxi xs key < i \<longrightarrow> i < length xs \<longrightarrow>
    key (xs ! i) < key (xs ! maxi xs key)"
by (induction xs arbitrary: i, simp_all add: Let_def, (rule impI)+,
 rule le_less_trans, rule maxi_ub, rule nth_mem, simp)

lemma nths_range:
 "nths xs A = nths xs (A \<inter> {..<length xs})"
proof (induction xs arbitrary: A, simp_all add: nths_Cons)
  fix xs :: "'a list" and A
  assume "\<And>A. nths xs A = nths xs (A \<inter> {..<length xs})"
  hence "nths xs {i. Suc i \<in> A} = nths xs ({i. Suc i \<in> A} \<inter> {..<length xs})" .
  moreover have
   "{i. Suc i \<in> A} \<inter> {..<length xs} = {i. Suc i \<in> A \<and> i < length xs}"
    by blast
  ultimately show
   "nths xs {i. Suc i \<in> A} = nths xs {i. Suc i \<in> A \<and> i < length xs}"
    by simp
qed

lemma filter_nths_diff:
  assumes
    A: "i < length xs" and
    B: "\<not> P (xs ! i)"
  shows "[x\<leftarrow>nths xs (A - {i}). P x] = [x\<leftarrow>nths xs A. P x]"
proof (cases "i \<in> A", simp_all)
  case True
  have C: "xs = take i xs @ xs ! i # drop (Suc i) xs"
    (is "_ = ?ts @ _ # ?ds")
    using A by (rule id_take_nth_drop)
  have "nths xs A = nths ?ts A @ nths (xs ! i # ?ds) {j. j + length ?ts \<in> A}"
    by (subst C, simp add: nths_append)
  moreover have D: "length ?ts = i"
    using A by simp
  ultimately have E: "nths xs A = nths ?ts (A \<inter> {..<i}) @ xs ! i #
    nths ?ds {j. Suc j + i \<in> A}"
    (is "_ = ?vs @ _ # ?ws")
    using True by (simp add: nths_Cons, subst nths_range, simp)
  have "nths xs (A - {i}) = nths ?ts (A - {i}) @
    nths (xs ! i # ?ds) {j. j + length ?ts \<in> A - {i}}"
    by (subst C, simp add: nths_append)
  moreover have "(A - {i}) \<inter> {..<i} = A \<inter> {..<i}"
    by (rule set_eqI, rule iffI, simp_all)
  ultimately have "nths xs (A - {i}) = ?vs @ ?ws"
    using D by (simp add: nths_Cons, subst nths_range, simp)
  thus ?thesis
    using B and E by simp
qed

lemma mini_stable:
  assumes
    A: "xs \<noteq> []" and
    B: "mini xs key \<in> A"
      (is "?nmi \<in> _")
  shows "[x\<leftarrow>[xs ! ?nmi] @ nths xs (A - {?nmi}). key x = k] =
    [x\<leftarrow>nths xs A. key x = k]"
    (is "[x\<leftarrow>[?xmi] @ _. _] = _")
proof (simp, rule conjI, rule_tac [!] impI, rule_tac [2] filter_nths_diff,
 rule_tac [2] mini_less, simp_all add: A)
  assume C: "key ?xmi = k"
  moreover have "?nmi < length xs"
    using A by (rule_tac mini_less, simp)
  ultimately have "0 < length [x\<leftarrow>xs. key x = k]"
    by (simp add: length_filter_conv_card card_gt_0_iff, rule_tac exI, rule_tac conjI)
  hence "\<exists>y ys. [x\<leftarrow>xs. key x = k] = y # ys"
    by (rule_tac list.exhaust [of "[x\<leftarrow>xs. key x = k]"], simp_all)
  then obtain y and ys where "[x\<leftarrow>xs. key x = k] = y # ys" by blast
  hence "\<exists>us vs. xs = us @ y # vs \<and>
    (\<forall>u \<in> set us. key u \<noteq> k) \<and> key y = k \<and> ys = [x\<leftarrow>vs. key x = k]"
    (is "\<exists>us vs. ?P us vs")
    by (simp add: filter_eq_Cons_iff)
  then obtain us and vs where D: "?P us vs" by blast
  have E: "length us = ?nmi"
  proof (rule ccontr, erule neqE)
    assume "length us < ?nmi"
    with A have "key ?xmi < key (xs ! length us)"
      by (rule mini_first)
    also have "\<dots> = k"
      using D by simp
    finally show False
      using C by simp
  next
    assume F: "?nmi < length us"
    hence "?xmi = us ! ?nmi"
      using D by (simp add: nth_append)
    hence "?xmi \<in> set us"
      using F by simp
    thus False
      using C and D by simp
  qed
  moreover have "xs ! length us = y"
    using D by simp
  ultimately have F: "?xmi = y" by simp
  have "nths xs A = nths us A @ nths (y # vs) {i. i + ?nmi \<in> A}"
    using D and E by (simp add: nths_append)
  also have "\<dots> = nths us A @ y # nths vs {i. Suc i + ?nmi \<in> A}"
    (is "_ = _ @ _ # ?ws")
    using B by (simp add: nths_Cons)
  finally have G: "[x\<leftarrow>nths xs A. key x = k] = y # [x\<leftarrow>?ws. key x = k]"
    using D by (simp add: filter_empty_conv, rule_tac ballI,
     drule_tac in_set_nthsD, simp)
  have "nths xs (A - {?nmi}) = nths us (A - {?nmi}) @
    nths (y # vs) {i. i + ?nmi \<in> A - {?nmi}}"
    using D and E by (simp add: nths_append)
  also have "\<dots> = nths us (A - {?nmi}) @ ?ws"
    by (simp add: nths_Cons)
  finally have H: "[x\<leftarrow>nths xs (A - {?nmi}). key x = k] = [x\<leftarrow>?ws. key x = k]"
    using D by (simp add: filter_empty_conv, rule_tac ballI,
     drule_tac in_set_nthsD, simp)
  show "?xmi # [x\<leftarrow>nths xs (A - {?nmi}). key x = k] =
    [x\<leftarrow>nths xs A. key x = k]"
    using F and G and H by simp
qed

lemma maxi_stable:
  assumes
    A: "xs \<noteq> []" and
    B: "maxi xs key \<in> A"
      (is "?nma \<in> _")
  shows "[x\<leftarrow>nths xs (A - {?nma}) @ [xs ! ?nma]. key x = k] =
    [x\<leftarrow>nths xs A. key x = k]"
    (is "[x\<leftarrow>_ @ [?xma]. _] = _")
proof (simp, rule conjI, rule_tac [!] impI, rule_tac [2] filter_nths_diff,
 rule_tac [2] maxi_less, simp_all add: A)
  assume C: "key ?xma = k"
  moreover have D: "?nma < length xs"
    using A by (rule_tac maxi_less, simp)
  ultimately have "0 < length [x\<leftarrow>rev xs. key x = k]"
    by (simp add: length_filter_conv_card card_gt_0_iff,
     rule_tac exI [where x = "length xs - Suc ?nma"], simp add: rev_nth)
  hence "\<exists>y ys. [x\<leftarrow>rev xs. key x = k] = y # ys"
    by (rule_tac list.exhaust [of "[x\<leftarrow>rev xs. key x = k]"], simp_all)
  then obtain y and ys where "[x\<leftarrow>rev xs. key x = k] = y # ys" by blast
  hence "\<exists>us vs. rev xs = us @ y # vs \<and>
    (\<forall>u \<in> set us. key u \<noteq> k) \<and> key y = k \<and> ys = [x\<leftarrow>vs. key x = k]"
    (is "\<exists>us vs. ?P us vs")
    by (simp add: filter_eq_Cons_iff)
  then obtain us and vs where E: "?P us vs" by blast
  hence F: "xs = rev vs @ y # rev us"
    by (simp add: rev_swap)
  have G: "length us = length xs - Suc ?nma"
  proof (rule ccontr, erule neqE)
    assume "length us < length xs - Suc ?nma"
    hence "?nma < length xs - Suc (length us)" by simp
    moreover have "length xs - Suc (length us) < length xs"
      using D by simp
    ultimately have "key (xs ! (length xs - Suc (length us))) < key ?xma"
      by (rule maxi_last [OF A])
    moreover have "length us < length xs"
      using F by simp
    ultimately have "key (rev xs ! length us) < key ?xma"
      by (simp add: rev_nth)
    moreover have "key (rev xs ! length us) = k"
      using E by simp
    ultimately show False
      using C by simp
  next
    assume H: "length xs - Suc ?nma < length us"
    hence "rev xs ! (length xs - Suc ?nma) = us ! (length xs - Suc ?nma)"
      using E by (simp add: nth_append)
    hence "rev xs ! (length xs - Suc ?nma) \<in> set us"
      using H by simp
    hence "?xma \<in> set us"
      using D by (simp add: rev_nth)
    thus False
      using C and E by simp
  qed
  moreover have "rev xs ! length us = y"
    using E by simp
  ultimately have H: "?xma = y"
    using D by (simp add: rev_nth)
  have "length xs = length us + Suc ?nma"
    using D and G by simp
  hence I: "length vs = ?nma"
    using F by simp
  hence "nths xs A = nths (rev vs) A @ nths (y # rev us) {i. i + ?nma \<in> A}"
    using F by (simp add: nths_append)
  also have "\<dots> = nths (rev vs) (A \<inter> {..<?nma}) @ y #
    nths (rev us) {i. Suc i + ?nma \<in> A}"
    (is "_ = ?ws @ _ # _")
    using B and I by (simp add: nths_Cons, subst nths_range, simp)
  finally have J: "[x\<leftarrow>nths xs A. key x = k] = [x\<leftarrow>?ws. key x = k] @ [y]"
    using E by (simp add: filter_empty_conv, rule_tac ballI,
     drule_tac in_set_nthsD, simp)
  have "nths xs (A - {?nma}) = nths (rev vs) (A - {?nma}) @
    nths (y # rev us) {i. i + ?nma \<in> A - {?nma}}"
    using F and I by (simp add: nths_append)
  hence "nths xs (A - {?nma}) = nths (rev vs) ((A - {?nma}) \<inter> {..<?nma}) @
    nths (rev us) {i. Suc i + ?nma \<in> A}"
    using I by (simp add: nths_Cons, subst nths_range, simp)
  moreover have "(A - {?nma}) \<inter> {..<?nma} = A \<inter> {..<?nma}"
    by (rule set_eqI, rule iffI, simp_all)
  ultimately have K: "[x\<leftarrow>nths xs (A - {?nma}). key x = k] =
    [x\<leftarrow>?ws. key x = k]"
    using E by (simp add: filter_empty_conv, rule_tac ballI,
     drule_tac in_set_nthsD, simp)
  show "[x\<leftarrow>nths xs (A - {?nma}). key x = k] @ [?xma] =
    [x\<leftarrow>nths xs A. key x = k]"
    using H and J and K by simp
qed

lemma round_stab_inv [rule_format]:
 "index_less index key \<longrightarrow> index_same index key \<longrightarrow> bn_inv p q t \<longrightarrow>
    add_inv n t \<longrightarrow> stab_inv f key t \<longrightarrow> stab_inv f key (round index key p q r t)"
proof (induction index key p q r t arbitrary: n f rule: round.induct,
 (rule_tac [!] impI)+, simp, simp, simp_all only: simp_thms)
  fix index p q r u ns xs n f and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, tl xs)"
  assume
   "\<And>n f. bn_inv p q (u, ns, tl xs) \<longrightarrow> add_inv n (u, ns, tl xs) \<longrightarrow>
      stab_inv f key (u, ns, tl xs) \<longrightarrow> stab_inv f key ?t" and
   "bn_inv p q (u, Suc 0 # ns, xs)" and
   "add_inv n (u, Suc 0 # ns, xs)" and
   "stab_inv f key (u, Suc 0 # ns, xs)"
  thus "stab_inv f key (round index key p q r (u, Suc 0 # ns, xs))"
  proof (cases ?t, cases xs, simp_all add: add_suc, arith, erule_tac conjE,
   rule_tac allI, simp)
    fix k y ys xs'
    let ?f' = "f(key y := tl (f (key y)))"
    assume "\<And>n' f'. foldl (+) 0 ns = n' \<and> length ys = n' \<longrightarrow>
      (\<forall>k'. [x\<leftarrow>ys. key x = k'] = f' k') \<longrightarrow> (\<forall>k'. [x\<leftarrow>xs'. key x = k'] = f' k')"
    moreover assume "Suc (foldl (+) 0 ns) = n" and "Suc (length ys) = n"
    ultimately have "(\<forall>k'. [x\<leftarrow>ys. key x = k'] = ?f' k') \<longrightarrow>
      (\<forall>k'. [x\<leftarrow>xs'. key x = k'] = ?f' k')"
      by blast
    moreover assume A: "\<forall>k'. (if key y = k'
      then y # [x\<leftarrow>ys. key x = k'] else [x\<leftarrow>ys. key x = k']) = f k'"
    hence B: "f (key y) = y # [x\<leftarrow>ys. key x = key y]"
      by (drule_tac spec [where x = "key y"], simp)
    hence "\<forall>k'. [x\<leftarrow>ys. key x = k'] = ?f' k'"
    proof (rule_tac allI, simp, rule_tac impI)
      fix k'
      assume "k' \<noteq> key y"
      thus "[x\<leftarrow>ys. key x = k'] = f k'"
        using A by (drule_tac spec [where x = k'], simp)
    qed
    ultimately have C: "\<forall>k'. [x\<leftarrow>xs'. key x = k'] = ?f' k'" ..
    show "(key y = k \<longrightarrow> y # [x\<leftarrow>xs'. key x = k] = f k) \<and>
      (key y \<noteq> k \<longrightarrow> [x\<leftarrow>xs'. key x = k] = f k)"
    proof (rule conjI, rule_tac [!] impI)
      assume "key y = k"
      moreover have "tl (f (key y)) = [x\<leftarrow>xs'. key x = key y]"
        using C by simp
      hence "f (key y) = y # [x\<leftarrow>xs'. key x = key y]"
        using B by (subst hd_Cons_tl [symmetric], simp_all)
      ultimately show "y # [x\<leftarrow>xs'. key x = k] = f k" by simp
    next
      assume "key y \<noteq> k"
      thus "[x\<leftarrow>xs'. key x = k] = f k"
        using C by simp
    qed
  qed
next
  fix index p q r u m ns n f and key :: "'a \<Rightarrow> 'b" and xs :: "'a list"
  let ?ws = "take (Suc (Suc m)) xs"
  let ?ys = "drop (Suc (Suc m)) xs"
  let ?r = "\<lambda>m'. round_suc_suc index key ?ws m m' u"
  let ?t = "\<lambda>r' v. round index key p q r' (v, ns, ?ys)"
  assume
    A: "index_less index key" and
    B: "index_same index key"
  assume
   "\<And>ws a b c d e g h i n f.
      ws = ?ws \<Longrightarrow> a = bn_comp m p q r \<Longrightarrow> (b, c) = bn_comp m p q r \<Longrightarrow>
      d = ?r b \<Longrightarrow> (e, g) = ?r b \<Longrightarrow> (h, i) = g \<Longrightarrow>
        bn_inv p q (e, ns, ?ys) \<longrightarrow> add_inv n (e, ns, ?ys) \<longrightarrow>
          stab_inv f key (e, ns, ?ys) \<longrightarrow> stab_inv f key (?t c e)" and
   "bn_inv p q (u, Suc (Suc m) # ns, xs)" and
   "add_inv n (u, Suc (Suc m) # ns, xs)" and
   "stab_inv f key (u, Suc (Suc m) # ns, xs)"
  thus "stab_inv f key (round index key p q r (u, Suc (Suc m) # ns, xs))"
  proof (simp split: prod.split, ((rule_tac allI)+, ((rule_tac impI)+)?)+,
   (erule_tac conjE)+, subst (asm) (2) add_base_zero, simp)
    fix m' r' v ms' ws' xs' k
    let ?f = "\<lambda>k. [x\<leftarrow>?ys. key x = k]"
    let ?P = "\<lambda>f. \<forall>k. [x\<leftarrow>?ys. key x = k] = f k"
    let ?Q = "\<lambda>f. \<forall>k. [x\<leftarrow>xs'. key x = k] = f k"
    assume
      C: "?r m' = (v, ms', ws')" and
      D: "bn_comp m p q r = (m', r')" and
      E: "bn_valid m p q" and
      F: "Suc (Suc (foldl (+) 0 ns + m)) = n" and
      G: "length xs = n"
    assume "\<And>ws a b c d e g h i n' f.
      ws = ?ws \<Longrightarrow> a = (m', r') \<Longrightarrow> b = m' \<and> c = r' \<Longrightarrow>
      d = (v, ms', ws') \<Longrightarrow> e = v \<and> g = (ms', ws') \<Longrightarrow> h = ms' \<and> i = ws' \<Longrightarrow>
        foldl (+) 0 ns = n' \<and> n - Suc (Suc m) = n' \<longrightarrow> ?P f \<longrightarrow> ?Q f"
    hence "\<And>f. foldl (+) 0 ns = n - Suc (Suc m) \<longrightarrow> ?P f \<longrightarrow> ?Q f"
      by simp
    hence "\<And>f. ?P f \<longrightarrow> ?Q f"
      using F by simp
    hence "?P ?f \<longrightarrow> ?Q ?f" .
    hence "[x\<leftarrow>xs'. key x = k] = [x\<leftarrow>?ys. key x = k]" by simp
    moreover assume "\<forall>k. [x\<leftarrow>xs. key x = k] = f k"
    hence "f k = [x\<leftarrow>?ws @ ?ys. key x = k]" by simp
    ultimately have "f k = [x\<leftarrow>?ws. key x = k] @ [x\<leftarrow>xs'. key x = k]"
      by (subst (asm) filter_append, simp)
    with C [symmetric] show "[x\<leftarrow>ws'. key x = k] @ [x\<leftarrow>xs'. key x = k] = f k"
    proof (simp add: round_suc_suc_def Let_def del: filter.simps
     split: if_split_asm)
      let ?nmi = "mini ?ws key"
      let ?nma = "maxi ?ws key"
      let ?xmi = "?ws ! ?nmi"
      let ?xma = "?ws ! ?nma"
      let ?mi = "key ?xmi"
      let ?ma = "key ?xma"
      let ?k = "case m of 0 \<Rightarrow> m | Suc 0 \<Rightarrow> m | Suc (Suc i) \<Rightarrow> u + m'"
      let ?zs = "nths ?ws (- {?nmi, ?nma})"
      let ?ms = "enum ?zs index key ?k ?mi ?ma"
      have H: "length ?ws = Suc (Suc m)"
        using F and G by simp
      hence I: "?nmi \<noteq> ?nma"
        by (rule_tac mini_maxi_neq, simp)
      have "[x\<leftarrow>(([?xmi] @ map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma))
        @ [?xma]). key x = k] = [x\<leftarrow>?ws. key x = k]"
      proof (cases "m = 0")
        case True
        have "?nmi < length ?ws"
          using H by (rule_tac mini_less, simp)
        hence J: "?nmi < Suc (Suc 0)"
          using True by simp
        moreover have "?nma < length ?ws"
          using H by (rule_tac maxi_less, simp)
        hence K: "?nma < Suc (Suc 0)"
          using True by simp
        ultimately have "card ({..<Suc (Suc 0)} - {?nma} - {?nmi}) = 0"
          using I by ((subst card_Diff_singleton, simp, simp)+,
           subst card_lessThan, simp)
        hence L: "{..<Suc (Suc 0)} - {?nma} - {?nmi} = {}" by simp
        have "length (fill ?zs (offs ?ms 0) index key m ?mi ?ma) = 0"
          using True by (simp add: fill_length)
        hence M: "map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma) =
          nths ?ws ({..<Suc (Suc 0)} - {?nma} - {?nmi})"
          by (subst L, simp)
        show ?thesis
        proof (subst M, subst filter_append)
          show "[x\<leftarrow>[?xmi] @ nths ?ws ({..<Suc (Suc 0)} - {?nma} - {?nmi}).
            key x = k] @ [x\<leftarrow>[?xma]. key x = k] = [x\<leftarrow>?ws. key x = k]"
          proof (subst mini_stable, simp only: length_greater_0_conv
           [symmetric] H, simp add: I J, subst filter_append [symmetric])
            show "[x\<leftarrow>nths ?ws ({..<Suc (Suc 0)} - {?nma}) @ [?xma].
              key x = k] = [x\<leftarrow>?ws. key x = k]"
              by (subst maxi_stable, simp only: length_greater_0_conv
               [symmetric] H, simp add: K, simp add: True)
          qed
        qed
      next
        case False
        hence "0 < ?k"
          by (simp, drule_tac bn_comp_fst_nonzero [OF E], subst (asm) D,
           simp split: nat.split)
        hence "[x\<leftarrow>map the (fill ?zs (offs ?ms 0) index key (length ?zs) ?mi ?ma).
          key x = k] = [x\<leftarrow>?zs. k = key x]"
          by (rule_tac fill_offs_enum_stable [OF A B], simp, rule_tac conjI,
           ((rule_tac mini_lb | rule_tac maxi_ub), erule_tac in_set_nthsD)+)
        moreover have "[x\<leftarrow>?zs. k = key x] = [x\<leftarrow>?zs. key x = k]"
          by (rule filter_cong, simp, blast)
        ultimately have
          J: "[x\<leftarrow>map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma).
            key x = k] = [x\<leftarrow>?zs. key x = k]"
          using H by (simp add: mini_maxi_nths)
        show ?thesis
        proof (simp only: filter_append J, subst Compl_eq_Diff_UNIV,
         subst Diff_insert, subst filter_append [symmetric])
          show "[x\<leftarrow>[?xmi] @ nths ?ws (UNIV - {?nma} - {?nmi}). key x = k]
            @ [x\<leftarrow>[?xma]. key x = k] = [x\<leftarrow>?ws. key x = k]"
          proof (subst mini_stable, simp only: length_greater_0_conv
           [symmetric] H, simp add: I, subst filter_append [symmetric])
            show "[x\<leftarrow>nths ?ws (UNIV - {?nma}) @ [?xma]. key x = k] =
              [x\<leftarrow>?ws. key x = k]"
              by (subst maxi_stable, simp only: length_greater_0_conv
               [symmetric] H, simp, subst nths_range, subst H, simp)
          qed
        qed
      qed
      thus "[x\<leftarrow>?xmi # map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma) @
        [?xma]. key x = k] = [x\<leftarrow>?ws. key x = k]"
        by simp
    qed
  qed
qed

lemma gcsort_stab_inv:
  assumes
    A: "index_less index key" and
    B: "index_same index key" and
    C: "add_inv n t" and
    D: "n \<le> p"
  shows "\<lbrakk>t' \<in> gcsort_set index key p t; stab_inv f key t\<rbrakk> \<Longrightarrow>
    stab_inv f key t'"
by (erule gcsort_set.induct, simp, drule gcsort_add_inv [OF A _ C D],
 rule round_stab_inv [OF A B], simp_all del: bn_inv.simps, erule conjE,
 frule sym, erule subst, rule bn_inv_intro, insert D, simp)

text \<open>
\null

The only remaining task is to address step 10 of the proof method, which is done by proving theorem
@{text gcsort_stable}. It holds under the conditions that the objects' number is not larger than the
counters' upper bound and function @{text index} satisfies both predicates @{const index_less} and
@{const index_same}, and states that function @{const gcsort} leaves unchanged the sublist of the
objects having a given key within the input objects' list.

\null
\<close>

theorem gcsort_stable:
  assumes
    A: "index_less index key" and
    B: "index_same index key" and
    C: "length xs \<le> p"
  shows "[x\<leftarrow>gcsort index key p xs. key x = k] = [x\<leftarrow>xs. key x = k]"
proof -
  let ?t = "(0, [length xs], xs)"
  have "stab_inv (\<lambda>k. [x\<leftarrow>xs. key x = k]) key (gcsort_aux index key p ?t)"
    by (rule gcsort_stab_inv [OF A B _ C], rule gcsort_add_input,
     rule gcsort_aux_set, rule gcsort_stab_input)
  hence "[x\<leftarrow>gcsort_out (gcsort_aux index key p ?t). key x = k] =
    [x\<leftarrow>xs. key x = k]"
    by (rule gcsort_stab_intro)
  moreover have "?t = gcsort_in xs"
    by (simp add: gcsort_in_def)
  ultimately show ?thesis
    by (simp add: gcsort_def)
qed

end
