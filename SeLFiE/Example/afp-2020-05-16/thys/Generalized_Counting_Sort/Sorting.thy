(*  Title:       An Efficient Generalization of Counting Sort for Large, possibly Infinite Key Ranges
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Proof of objects' sorting"

theory Sorting
  imports Conservation
begin

text \<open>
\null

In this section, it is formally proven that GCsort actually sorts objects.

Here below, steps 5, 6, and 7 of the proof method are accomplished. Predicate @{text sort_inv} is
satisfied just in case, for any bucket delimited by the input counters' list $ns$, the keys of the
corresponding objects within the input objects' list $xs$ are not larger than those of the objects,
if any, to the right of that bucket. The underlying idea is that this predicate:

\begin{itemize}

\item
is trivially satisfied by the output of function @{const gcsort_in}, which places all objects into a
single bucket, and

\item
implies that $xs$ is sorted if every bucket delimited by $ns$ has size one, as happens when function
@{const gcsort_aux} terminates.

\end{itemize}

\null
\<close>

fun sort_inv :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> nat \<times> nat list \<times> 'a list \<Rightarrow> bool" where
"sort_inv key (u, ns, xs) =
  (\<forall>i < length ns. \<forall>j < offs ns 0 ! i. \<forall>k \<in> {offs ns 0 ! i..<length xs}.
    key (xs ! j) \<le> key (xs ! k))"

lemma gcsort_sort_input:
 "sort_inv key (0, [length xs], xs)"
by simp

lemma offs_nth:
  assumes
    A: "find (\<lambda>n. Suc 0 < n) ns = None" and
    B: "foldl (+) 0 ns = n" and
    C: "k < n"
  shows "\<exists>i < length ns. offs ns 0 ! i = k"
proof (cases ns, insert B C, simp, cases "k = 0", rule exI [of _ 0], simp,
 rule ccontr, simp (no_asm_use))
  fix m ms
  assume
    D: "ns = m # ms" and
    E: "0 < k" and
    F: "\<forall>i < length ns. offs ns 0 ! i \<noteq> k"
  have G: "\<forall>n \<in> set ns. n \<le> Suc 0"
    using A by (auto simp add: find_None_iff)
  let ?A = "{i. i < length ns \<and> offs ns 0 ! i < k}"
  have H: "Max ?A \<in> ?A"
    using D and E by (rule_tac Max_in, simp_all, rule_tac exI [of _ 0], simp)
  hence I: "Max ?A < length ns"
    by simp
  hence J: "offs ns 0 ! Max ?A = foldl (+) 0 (take (Max ?A) ns)"
    by (rule offs_add)
  have "Max ?A < length ns - Suc 0 \<or> Max ?A = length ns - Suc 0"
    (is "?P \<or> ?Q")
    using H by (simp, arith)
  moreover {
    assume ?P
    hence K: "Suc (Max ?A) < length ns" by simp
    hence "offs ns 0 ! Suc (Max ?A) = foldl (+) 0 (take (Suc (Max ?A)) ns)"
      by (rule offs_add)
    moreover have "take (Suc (Max ?A)) ns = take (Max ?A) ns @ [ns ! Max ?A]"
      using I by (rule take_Suc_conv_app_nth)
    ultimately have "offs ns 0 ! Suc (Max ?A) =
      offs ns 0 ! Max ?A + ns ! Max ?A"
      using J by simp
    moreover have "offs ns 0 ! Max ?A < k"
      using H by simp
    moreover have "ns ! Max ?A \<in> set ns"
      using I by (rule nth_mem)
    with G have "ns ! Max ?A \<le> Suc 0" ..
    ultimately have "offs ns 0 ! Suc (Max ?A) \<le> k" by simp
    moreover have "offs ns 0 ! Suc (Max ?A) \<noteq> k"
      using F and K by simp
    ultimately have "offs ns 0 ! Suc (Max ?A) < k" by simp
    hence "Suc (Max ?A) \<in> ?A"
      using K by simp
    hence "Suc (Max ?A) \<le> Max ?A"
      by (rule_tac Max_ge, simp)
    hence False by simp
  }
  moreover {
    assume ?Q
    hence "offs ns 0 ! Max ?A = foldl (+) 0 (take (length ns - Suc 0) ns)"
      using J by simp
    moreover have K: "length ns - Suc 0 < length ns"
      using D by simp
    hence "take (Suc (length ns - Suc 0)) ns =
      take (length ns - Suc 0) ns @ [ns ! (length ns - Suc 0)]"
      by (rule take_Suc_conv_app_nth)
    hence "foldl (+) 0 ns =
      foldl (+) 0 (take (length ns - Suc 0) ns @ [ns ! (length ns - Suc 0)])"
      by simp
    ultimately have "n = offs ns 0 ! Max ?A + ns ! (length ns - Suc 0)"
      using B by simp
    moreover have "offs ns 0 ! Max ?A < k"
      using H by simp
    moreover have "ns ! (length ns - Suc 0) \<in> set ns"
      using K by (rule nth_mem)
    with G have "ns ! (length ns - Suc 0) \<le> Suc 0" ..
    ultimately have "n \<le> k" by simp
    with C have False by simp
  }
  ultimately show False ..
qed

lemma gcsort_sort_intro:
 "\<lbrakk>sort_inv key t; add_inv n t; find (\<lambda>n. Suc 0 < n) (fst (snd t)) = None\<rbrakk> \<Longrightarrow>
    sorted (map key (gcsort_out t))"
proof (cases t, simp add: sorted_iff_nth_mono_less gcsort_out_def,
 erule conjE, (rule allI)+, (rule impI)+)
  fix ns xs j k
  assume "find (\<lambda>n. Suc 0 < n) ns = None" and "foldl (+) 0 ns = n"
  moreover assume A: "k < n"
  ultimately have "\<exists>i < length ns. offs ns 0 ! i = k"
    by (rule offs_nth)
  then obtain i where "i < length ns \<and> offs ns 0 ! i = k" ..
  moreover assume "\<forall>i < length ns. \<forall>j < offs ns 0 ! i. \<forall>k \<in> {offs ns 0 ! i..<n}.
    key (xs ! j) \<le> key (xs ! k)"
  hence "i < length ns \<longrightarrow> j < offs ns 0 ! i \<longrightarrow> k \<in> {offs ns 0 ! i..<n} \<longrightarrow>
    key (xs ! j) \<le> key (xs ! k)"
    by simp
  ultimately have "j < k \<longrightarrow> k < n \<longrightarrow> key (xs ! j) \<le> key (xs ! k)"
    by simp
  moreover assume "j < k"
  ultimately show "key (xs ! j) \<le> key (xs ! k)"
    using A by simp
qed

text \<open>
\null

As lemma @{thm [source] gcsort_sort_intro} comprises an additional assumption concerning the form of
the fixed points of function @{const gcsort_aux}, step 8 of the proof method is necessary this time
to prove that such assumption is satisfied.

\null
\<close>

lemma gcsort_sort_form:
 "find (\<lambda>n. Suc 0 < n) (fst (snd (gcsort_aux index key p t))) = None"
by (induction index key p t rule: gcsort_aux.induct, simp)

text \<open>
\null

Here below, step 9 of the proof method is accomplished.

In the most significant case of the proof by recursion induction of lemma @{text round_sort_inv},
namely that of a bucket $B$ with size larger than two and distinct minimum and maximum keys, the
following line of reasoning is adopted. Let $x$ be an object contained in a finer-grained bucket
$B'$ resulting from $B$'s partition, and $y$ an object to the right of $B'$. Then:

\begin{itemize}

\item
If $y$ is contained in some other finer-grained bucket resulting from $B$'s partition, inequality
@{term "key x \<le> key y"} holds because predicate @{const sort_inv} is satisfied by a counters' list
generated by function @{const enum} and an objects' list generated by function @{const fill} in case
@{const fill}'s input offsets' list is computed via the composition of functions @{const offs} and
@{const enum}, as happens within function @{const round}.
\\This is proven beforehand in lemma @{text fill_sort_inv}.

\item
Otherwise, inequality @{term "key x \<le> key y"} holds as well because object $x$ was contained in $B$
by lemma @{thm [source] fill_offs_enum_count_item}, object $y$ occurred to the right of $B$ by lemma
@{thm [source] round_count_inv}, and by hypothesis, the key of any object in $B$ was not larger than
that of any object to the right of $B$.

\end{itemize}

Using lemma @{text round_sort_inv}, the invariance of predicate @{const sort_inv} over inductive set
@{const gcsort_set} is then proven in lemma @{text gcsort_sort_inv}.

\null
\<close>

lemma mini_maxi_keys_le:
 "x \<in> set xs \<Longrightarrow> key (xs ! mini xs key) \<le> key (xs ! maxi xs key)"
by (frule mini_lb, drule maxi_ub, erule order_trans)

lemma mini_maxi_keys_eq [rule_format]:
 "key (xs ! mini xs key) = key (xs ! maxi xs key) \<longrightarrow> x \<in> set xs \<longrightarrow>
    key x = key (xs ! maxi xs key)"
by (induction xs, simp_all add: Let_def, (rule_tac [!] impI, (rule_tac [!] conjI)?)+,
 rule_tac [2-4] impI, frule_tac [1-3] mini_maxi_keys_le [where key = key], simp_all)

lemma offs_suc:
 "i < length ns \<Longrightarrow> offs ns (Suc k) ! i = Suc (offs ns k ! i)"
by (simp add: offs_add add_suc)

lemma offs_base_zero:
 "i < length ns \<Longrightarrow> offs ns k ! i = offs ns 0 ! i + k"
by (simp add: offs_add, subst add_base_zero, simp)

lemma offs_append:
 "offs (ms @ ns) k = offs ms k @ offs ns (foldl (+) k ms)"
by (induction ms arbitrary: k, simp_all)

lemma offs_enum_next_le [rule_format]:
  assumes
    A: "index_less index key" and
    B: "i < j" and
    C: "j < n" and
    D: "\<forall>x \<in> set xs. key x \<in> {mi..ma}"
  shows "offs_next (offs (enum xs index key n mi ma) k) (length xs + k)
    xs index key mi ma i \<le> offs (enum xs index key n mi ma) k ! j"
  (is "_ \<le> offs ?ns _ ! _")
proof (rule ccontr, simp add: not_le)
  assume E: "offs ?ns k ! j <
    offs_next (offs ?ns k) (length xs + k) xs index key mi ma i"
  from B have "offs_set_next (offs ?ns k) xs index key mi ma i =
    offs_set_next (offs ?ns k) xs index key mi ma j"
  proof (rule_tac set_eqI, rule_tac iffI, simp_all, rule_tac ccontr, simp add: not_less)
    fix m
    assume "m < length (offs ?ns k) \<and> i < m \<and>
      0 < offs_num (length (offs ?ns k)) xs index key mi ma m"
    hence F: "m \<in> offs_set_next (offs ?ns k) xs index key mi ma i"
      (is "_ \<in> ?A")
      by simp
    hence "Min ?A \<le> m"
      by (rule_tac Min_le, simp)
    moreover assume "m \<le> j"
    ultimately have "offs ?ns k ! Min ?A \<le> offs ?ns k ! j"
      using C by (rule_tac offs_mono, simp_all add: enum_length)
    hence "offs_next (offs ?ns k) (length xs + k) xs index key mi ma i \<le>
      offs ?ns k ! j"
      using F by (simp only: offs_next_def split: if_split, rule_tac conjI,
       blast, simp)
    thus False
      using E by simp
  qed
  hence "offs ?ns k ! j <
    offs_next (offs ?ns k) (length xs + k) xs index key mi ma j"
    using E by (simp only: offs_next_def)
  moreover have "offs_num n xs index key mi ma j = 0"
  proof (rule ccontr, simp)
    assume "0 < offs_num n xs index key mi ma j"
    hence "j \<in> offs_set_next (offs ?ns k) xs index key mi ma i"
      (is "_ \<in> ?A")
      using B and C by (simp add: offs_length enum_length)
    moreover from this have "Min ?A \<le> j"
      by (rule_tac Min_le, simp)
    hence "offs ?ns k ! Min ?A \<le> offs ?ns k ! j"
      using C by (erule_tac offs_mono, simp add: enum_length)
    ultimately have "offs_next (offs ?ns k) (length xs + k) xs index key mi ma i \<le>
      offs ?ns k ! j"
      by (simp only: offs_next_def split: if_split, rule_tac conjI, blast, simp)
    thus False
      using E by simp
  qed
  hence "offs ?ns k ! j =
    offs_next (offs ?ns k) (length xs + k) xs index key mi ma j"
    using A and C and D by (rule_tac offs_enum_zero, simp_all)
  ultimately show False by simp
qed

lemma offs_pred_ub_less:
 "\<lbrakk>offs_pred ns ub xs index key mi ma; i < length ns;
   0 < offs_num (length ns) xs index key mi ma i\<rbrakk> \<Longrightarrow>
     ns ! i < ub"
by (drule offs_pred_ub, assumption+, simp)

lemma fill_count_none [rule_format]:
  assumes A: "index_less index key"
  shows
   "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    ns \<noteq> [] \<longrightarrow>
    offs_pred ns ub xs index key mi ma \<longrightarrow>
    length xs \<le> ub \<longrightarrow>
      count (mset (fill xs ns index key ub mi ma)) None = ub - length xs"
  using A
proof (induction xs arbitrary: ns, simp_all add: replicate_count Let_def,
 (rule_tac impI)+, (erule_tac conjE)+, subst mset_update, simp add: fill_length,
 erule_tac offs_pred_ub_less, simp_all add: index_less_def offs_num_cons del:
 not_None_eq, subst conj_commute, rule_tac conjI, rule_tac [!] impI, rotate_tac,
 rotate_tac, erule_tac contrapos_np, rule_tac fill_index_none, simp_all)
  fix x xs and ns :: "nat list"
  let ?i = "index key x (length ns) mi ma"
  let ?ns' = "ns[?i := Suc (ns ! ?i)]"
  assume "\<And>ns. ns \<noteq> [] \<longrightarrow> offs_pred ns ub xs index key mi ma \<longrightarrow>
    count (mset (fill xs ns index key ub mi ma)) None = ub - length xs"
  moreover assume B: "ns \<noteq> []"
  moreover assume
   "offs_pred ns ub (x # xs) index key mi ma" and
   "mi \<le> key x" and
   "key x \<le> ma"
  hence "offs_pred ?ns' ub xs index key mi ma"
    using A and B by (rule_tac offs_pred_cons, simp_all add: index_less_def)
  ultimately show "count (mset (fill xs ?ns' index key ub mi ma)) None -
    Suc 0 = ub - Suc (length xs)"
    by simp
qed

lemma fill_offs_enum_count_none [rule_format]:
 "\<lbrakk>index_less index key; \<forall>x \<in> set xs. key x \<in> {mi..ma}; 0 < n\<rbrakk> \<Longrightarrow>
    count (mset (fill xs (offs (enum xs index key n mi ma) 0)
      index key (length xs) mi ma)) None = 0"
by (subst fill_count_none, simp_all, simp only: length_greater_0_conv [symmetric]
 offs_length enum_length, insert offs_enum_pred [of index key xs mi ma n 0], simp)

lemma fill_index [rule_format]:
  assumes A: "index_less index key"
  shows
   "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    offs_pred ns ub xs index key mi ma \<longrightarrow>
    i < length ns \<longrightarrow>
    0 < offs_num (length ns) xs index key mi ma i \<longrightarrow>
    j \<in> {ns ! i..<offs_next ns ub xs index key mi ma i} \<longrightarrow>
    fill xs ns index key ub mi ma ! j = Some x \<longrightarrow>
      index key x (length ns) mi ma = i"
proof (induction xs arbitrary: ns, simp add: offs_num_def, simp add: Let_def,
 (rule impI)+, (erule conjE)+, simp)
  fix y xs and ns :: "nat list"
  let ?i = "index key x (length ns) mi ma"
  let ?i' = "index key y (length ns) mi ma"
  let ?ns' = "ns[?i' := Suc (ns ! ?i')]"
  let ?P = "\<lambda>ns.
    offs_pred ns ub xs index key mi ma \<longrightarrow>
    i < length ns \<longrightarrow>
    0 < offs_num (length ns) xs index key mi ma i \<longrightarrow>
    ns ! i \<le> j \<and> j < offs_next ns ub xs index key mi ma i \<longrightarrow>
    fill xs ns index key ub mi ma ! j = Some x \<longrightarrow>
      index key x (length ns) mi ma = i"
  assume
    B: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    C: "mi \<le> key y" and
    D: "key y \<le> ma" and
    E: "offs_pred ns ub (y # xs) index key mi ma" and
    F: "i < length ns" and
    G: "0 < offs_num (length ns) (y # xs) index key mi ma i" and
    H: "ns ! i \<le> j" and
    I: "j < offs_next ns ub (y # xs) index key mi ma i" and
    J: "\<And>ns. ?P ns" and
    K: "(fill xs ?ns' index key ub mi ma)[ns ! ?i' := Some y] ! j = Some x"
  have "0 < length ns"
    using F by arith
  hence L: "?i' < length ns"
    using A and C and D by (simp add: index_less_def)
  hence "ns ! ?i' + offs_num (length ns) (y # xs) index key mi ma ?i' \<le> ub"
    by (rule_tac offs_pred_ub [OF E], simp_all add: offs_num_cons)
  hence "ns ! ?i' < ub"
    by (simp add: offs_num_cons)
  with K show "?i = i"
  proof (cases "j = ns ! ?i'", simp, subst (asm) nth_list_update_eq, simp_all
   add: fill_length)
    assume
      M: "j = ns ! ?i" and
      N: "y = x"
    show ?thesis
    proof (rule ccontr, erule neqE)
      assume "?i < i"
      hence "ns ! ?i + offs_num (length ns) (y # xs) index key mi ma ?i \<le> ns ! i"
        using F and G and N by (rule_tac offs_pred_asc [OF E], simp_all
         add: offs_num_cons)
      hence "j < ns ! i"
        using M and N by (simp add: offs_num_cons)
      thus False
        using H by simp
    next
      let ?A = "offs_set_next ns (y # xs) index key mi ma i"
      assume "i < ?i"
      hence O: "?i \<in> ?A"
        using N and L by (simp add: offs_num_cons)
      hence P: "Min ?A \<in> ?A"
        by (rule_tac Min_in, simp, blast)
      have "Min ?A \<le> ?i"
        using O by (rule_tac Min_le, simp)
      moreover have "?A \<noteq> {}"
        using O by blast
      ultimately have "offs_next ns ub (y # xs) index key mi ma i \<le> j"
      using M proof (simp only: offs_next_def, simp, subst (asm) le_less,
       erule_tac disjE, simp_all)
        assume "Min ?A < ?i"
        hence "ns ! Min ?A + offs_num (length ns) (y # xs) index key mi ma
          (Min ?A) \<le> ns ! ?i"
          using O and P by (rule_tac offs_pred_asc [OF E], simp_all)
        thus "ns ! Min ?A \<le> ns ! ?i" by simp
      qed
      thus False
        using I by simp
    qed
  next
    assume
      M: "j \<noteq> ns ! ?i'" and
      N: "fill xs ?ns' index key ub mi ma ! j = Some x"
    have "?P ?ns'" using J .
    moreover from D and F have "offs_pred ?ns' ub xs index key mi ma"
      using L by (rule_tac offs_pred_cons [OF E], simp)
    moreover have "i < length ?ns'"
      using F by simp
    moreover have "0 < offs_num (length ?ns') xs index key mi ma i"
    proof (rule ccontr, simp)
      assume O: "offs_num (length ns) xs index key mi ma i = 0"
      hence P: "offs_num (length ns) (y # xs) index key mi ma i = Suc 0"
        using G by (simp add: offs_num_cons split: if_split_asm)
      hence "i = ?i'"
        using O by (simp add: offs_num_cons split: if_split_asm)
      hence "ns ! i < j"
        using H and M by simp
      hence "ns ! i + offs_num (length ns) (y # xs) index key mi ma i \<le> j"
        using P by simp
      with F and G and I have "offs_none ns ub (y # xs) index key mi ma j"
        by (simp add: offs_none_def, rule_tac disjI1, rule_tac exI
         [where x = i], simp)
      with B and C and D and E and F have
       "fill (y # xs) ns index key ub mi ma ! j = None"
        by (rule_tac fill_none [OF A], simp_all, erule_tac disjE, simp_all, auto)
      thus False
        using K by (simp add: Let_def)
    qed
    moreover have "?ns' ! i \<le> j"
      using F and H and M by (cases "?i' = i", simp_all)
    moreover have "offs_next ns ub (y # xs) index key mi ma i \<le>
      offs_next ?ns' ub xs index key mi ma i"
      using G and L by (rule_tac offs_pred_next_cons [OF E], simp)
    hence "j < offs_next ?ns' ub xs index key mi ma i"
      using I by simp
    ultimately show ?thesis
      using N by simp
  qed
qed

lemma fill_offs_enum_index [rule_format]:
 "index_less index key \<Longrightarrow>
  \<forall>x \<in> set xs. key x \<in> {mi..ma} \<Longrightarrow>
  i < n \<Longrightarrow>
  0 < offs_num n xs index key mi ma i \<Longrightarrow>
  j \<in> {offs (enum xs index key n mi ma) 0 ! i..<
    offs_next (offs (enum xs index key n mi ma) 0) (length xs)
      xs index key mi ma i} \<Longrightarrow>
  fill xs (offs (enum xs index key n mi ma) 0) index key (length xs)
    mi ma ! j = Some x \<Longrightarrow>
    index key x n mi ma = i"
by (insert fill_index [of index key xs mi ma "offs (enum xs index key n mi ma) 0"
 "length xs" i j x], insert offs_enum_pred [of index key xs mi ma n 0],
 simp add: offs_length enum_length)

lemma fill_sort_inv [rule_format]:
  assumes
    A: "index_less index key" and
    B: "index_mono index key" and
    C: "\<forall>x \<in> set xs. key x \<in> {mi..ma}"
  shows "sort_inv key (u, enum xs index key n mi ma,
    map the (fill xs (offs (enum xs index key n mi ma) 0)
      index key (length xs) mi ma))"
  (is "sort_inv _ (_, ?ns, _)")
proof (simp, (rule allI, rule impI)+, rule ballI, simp add: enum_length fill_length,
 erule conjE)
  fix i j k
  let ?A = "{i. i < n \<and> 0 < ?ns ! i}"
  let ?B = "{i. i < n \<and> offs ?ns 0 ! i \<le> j \<and> 0 < offs_num n xs index key mi ma i}"
  let ?C = "{i. i < n \<and> offs ?ns 0 ! i \<le> k \<and> 0 < offs_num n xs index key mi ma i}"
  assume
    D: "i < n" and
    E: "j < offs ?ns 0 ! i" and
    F: "offs ?ns 0 ! i \<le> k" and
    G: "k < length xs"
  have H: "\<forall>i < length xs.
    \<exists>x. fill xs (offs ?ns 0) index key (length xs) mi ma ! i = Some x"
  proof (rule allI, rule impI, rule ccontr, simp)
    fix m
    assume "fill xs (offs ?ns 0) index key (length xs) mi ma ! m = None"
    moreover assume "m < length xs"
    hence "fill xs (offs ?ns 0) index key (length xs) mi ma ! m
      \<in> set (fill xs (offs ?ns 0) index key (length xs) mi ma)"
      by (rule_tac nth_mem, simp add: fill_length)
    ultimately have "None \<in> set (fill xs (offs ?ns 0) index key (length xs) mi ma)"
      by simp
    moreover have
     "count (mset (fill xs (offs ?ns 0) index key (length xs) mi ma)) None = 0"
      using C and D by (rule_tac fill_offs_enum_count_none [OF A], simp_all)
    ultimately show False by simp
  qed
  have "\<exists>y ys. xs = y # ys"
    using G by (rule_tac list.exhaust [of xs], simp_all)
  then obtain z and zs where I: "xs = z # zs" by blast
  hence "index key z n mi ma < n"
    using A and C and D by (simp add: index_less_def)
  moreover from this have "0 < ?ns ! index key z n mi ma"
    using I by (simp add: Let_def, subst nth_list_update_eq, simp_all add:
     enum_length)
  ultimately have "index key z n mi ma \<in> ?A" by simp
  hence J: "Min ?A \<in> ?A"
    by (rule_tac Min_in, simp, blast)
  hence "offs ?ns 0 ! 0 = offs ?ns 0 ! Min ?A"
  proof (cases "Min ?A = 0", simp_all, erule_tac offs_equal, simp_all add:
   enum_length, rule_tac ccontr, erule_tac conjE, simp)
    fix m
    assume "m < Min ?A" and "Min ?A < n" and "0 < ?ns ! m"
    moreover from this have "Min ?A \<le> m"
      by (rule_tac Min_le, simp_all)
    ultimately show False by simp
  qed
  moreover have "\<exists>m ms. ?ns = m # ms"
    using D by (rule_tac list.exhaust [of ?ns], simp_all,
     simp only: length_0_conv [symmetric] enum_length)
  then obtain m and ms where "?ns = m # ms" by blast
  ultimately have "offs ?ns 0 ! Min ?A = 0" by simp
  hence "Min ?A \<in> ?B"
    using J by (simp, subst enum_offs_num [symmetric], simp_all)
  hence K: "Max ?B \<in> ?B"
    by (rule_tac Max_in, simp, blast)
  moreover have "j < offs_next (offs ?ns 0) (length xs)
    xs index key mi ma (Max ?B)"
  proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI,
   rule_tac [2] ccontr, simp_all only: not_less)
    show "j < length xs"
      using E and F and G by simp
  next
    assume "offs_set_next (offs ?ns 0) xs index key mi ma (Max ?B) \<noteq> {}"
      (is "?Z \<noteq> _")
    hence L: "Min ?Z \<in> ?Z"
      by (rule_tac Min_in, simp)
    moreover assume "offs ?ns 0 ! Min ?Z \<le> j"
    ultimately have "Min ?Z \<in> ?B"
      by (simp add: offs_length enum_length)
    hence "Min ?Z \<le> Max ?B"
      by (rule_tac Max_ge, simp)
    thus False
      using L by simp
  qed
  moreover have
   "\<exists>x. fill xs (offs ?ns 0) index key (length xs) mi ma ! j = Some x"
    using E and F and G and H by simp
  then obtain x where
    L: "fill xs (offs ?ns 0) index key (length xs) mi ma ! j = Some x" ..
  ultimately have M: "index key x n mi ma = Max ?B"
    using C by (rule_tac fill_offs_enum_index [OF A], simp_all)
  have N: "Max ?B \<in> ?C"
    using E and F and K by simp
  hence "Max ?C \<in> ?C"
    by (rule_tac Max_in, simp, blast)
  moreover have O: "k < offs_next (offs ?ns 0) (length xs)
    xs index key mi ma (Max ?C)"
  proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI,
   rule_tac [2] ccontr, simp_all only: not_less)
    show "k < length xs" using G .
  next
    assume "offs_set_next (offs ?ns 0) xs index key mi ma (Max ?C) \<noteq> {}"
      (is "?Z \<noteq> _")
    hence P: "Min ?Z \<in> ?Z"
      by (rule_tac Min_in, simp)
    moreover assume "offs ?ns 0 ! Min ?Z \<le> k"
    ultimately have "Min ?Z \<in> ?C"
      by (simp add: offs_length enum_length)
    hence "Min ?Z \<le> Max ?C"
      by (rule_tac Max_ge, simp)
    thus False
      using P by simp
  qed
  moreover have
   "\<exists>x. fill xs (offs ?ns 0) index key (length xs) mi ma ! k = Some x"
    using G and H by simp
  then obtain y where
    P: "fill xs (offs ?ns 0) index key (length xs) mi ma ! k = Some y" ..
  ultimately have Q: "index key y n mi ma = Max ?C"
    using C by (rule_tac fill_offs_enum_index [OF A], simp_all)
  have "Max ?B \<le> Max ?C"
    using N by (rule_tac Max_ge, simp)
  hence "Max ?B < Max ?C"
  proof (rule_tac ccontr, simp)
    assume "Max ?B = Max ?C"
    hence "offs ?ns 0 ! i < offs_next (offs ?ns 0) (length xs)
      xs index key mi ma (Max ?B)"
      using F and O by simp
    moreover have "offs ?ns 0 ! Max ?B < offs ?ns 0 ! i"
      using E and K by simp
    with K have "Max ?B < i"
      by (erule_tac contrapos_pp, subst not_less, subst (asm) not_less,
       erule_tac offs_mono, simp add: enum_length)
    hence "offs_next (offs ?ns 0) (length xs + 0) xs index key mi ma (Max ?B) \<le>
      offs ?ns 0 ! i"
      using C and D by (rule_tac offs_enum_next_le [OF A], simp_all)
    ultimately show False by simp
  qed
  hence R: "index key x n mi ma < index key y n mi ma"
    using M and Q by simp
  have "count (mset (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))) x = count (mset xs) x"
    using C and D by (rule_tac fill_offs_enum_count_item [OF A], simp_all)
  moreover have S: "j < length (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))"
    using E and F and G by (simp add: fill_length)
  hence "map the (fill xs (offs ?ns 0) index key (length xs) mi ma) ! j
    \<in> set (map the (fill xs (offs ?ns 0) index key (length xs) mi ma))"
    by (rule nth_mem)
  hence "0 < count (mset (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))) x"
    using L and S by simp
  ultimately have T: "x \<in> set xs" by simp
  have "count (mset (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))) y = count (mset xs) y"
    using C and D by (rule_tac fill_offs_enum_count_item [OF A], simp_all)
  moreover have U: "k < length (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))"
    using G by (simp add: fill_length)
  hence "map the (fill xs (offs ?ns 0) index key (length xs) mi ma) ! k
    \<in> set (map the (fill xs (offs ?ns 0) index key (length xs) mi ma))"
    by (rule nth_mem)
  hence "0 < count (mset (map the (fill xs (offs ?ns 0) index key
    (length xs) mi ma))) y"
    using P and U by simp
  ultimately have V: "y \<in> set xs" by simp
  have "key y \<le> key x \<longrightarrow> index key y n mi ma \<le> index key x n mi ma"
    using B and C and T and V by (simp add: index_mono_def)
  hence "key x < key y"
    by (rule_tac contrapos_pp [OF R], simp add: not_less)
  thus "key (the (fill xs (offs ?ns 0) index key (length xs) mi ma ! j)) \<le>
    key (the (fill xs (offs ?ns 0) index key (length xs) mi ma ! k))"
    using L and P by simp
qed

lemma round_sort_inv [rule_format]:
 "index_less index key \<longrightarrow> index_mono index key \<longrightarrow> bn_inv p q t \<longrightarrow>
    add_inv n t \<longrightarrow> sort_inv key t \<longrightarrow> sort_inv key (round index key p q r t)"
proof (induction index key p q r t arbitrary: n rule: round.induct,
 (rule_tac [!] impI)+, simp, simp_all only: simp_thms)
  fix index p q r u ns xs n and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, xs)"
  assume "\<And>n. bn_inv p q (u, ns, xs) \<longrightarrow> add_inv n (u, ns, xs) \<longrightarrow>
    sort_inv key (u, ns, xs) \<longrightarrow> sort_inv key ?t"
  hence "bn_inv p q (u, ns, xs) \<longrightarrow> add_inv n (u, ns, xs) \<longrightarrow>
    sort_inv key (u, ns, xs) \<longrightarrow> sort_inv key ?t" .
  moreover assume
   "bn_inv p q (u, 0 # ns, xs)"
   "add_inv n (u, 0 # ns, xs)" and
   "sort_inv key (u, 0 # ns, xs)"
  ultimately show "sort_inv key (round index key p q r (u, 0 # ns, xs))"
    by auto
next
  fix index p q r u ns xs n and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, tl xs)"
  assume
    A: "index_less index key" and
    B: "bn_inv p q (u, Suc 0 # ns, xs)"
  moreover assume
   "\<And>n. bn_inv p q (u, ns, tl xs) \<longrightarrow> add_inv n (u, ns, tl xs) \<longrightarrow>
      sort_inv key (u, ns, tl xs) \<longrightarrow> sort_inv key ?t" and
   "add_inv n (u, Suc 0 # ns, xs)" and
   "sort_inv key (u, Suc 0 # ns, xs)"
  ultimately show "sort_inv key (round index key p q r (u, Suc 0 # ns, xs))"
  proof (cases ?t, cases xs, simp_all add: add_suc, (rule_tac allI, rule_tac impI)+,
   rule_tac ballI, simp, (erule_tac conjE)+, simp)
    fix i j k y ys u' ns' xs'
    assume
      C: "round index key p q r (u, ns, ys) = (u', ns', xs')" and
      D: "Suc (foldl (+) 0 ns) = n" and
      E: "Suc (length ys) = n" and
      F: "\<forall>i < Suc (length ns).
        \<forall>j < (0 # offs ns (Suc 0)) ! i. \<forall>k \<in> {(0 # offs ns (Suc 0)) ! i..<n}.
          key ((y # ys) ! j) \<le> key (ys ! (k - Suc 0))"
    assume A': "j < (0 # offs ns' (Suc 0)) ! i"
    hence "\<exists>i'. i = Suc i'"
      by (rule_tac nat.exhaust [of i], simp_all)
    then obtain i' where B': "i = Suc i'" ..
    assume "i < Suc (length ns')"
    hence G: "i' < length ns'"
      using B' by simp
    hence H: "j < Suc (offs ns' 0 ! i')"
      using A' and B' by (simp add: offs_suc)
    assume "(0 # offs ns' (Suc 0)) ! i \<le> k"
    hence "Suc (offs ns' 0 ! i') \<le> k"
      using B' and G by (simp add: offs_suc)
    moreover from this have "\<exists>k'. k = Suc k'"
      by (rule_tac nat.exhaust [of k], simp_all)
    then obtain k' where I: "k = Suc k'" ..
    ultimately have J: "offs ns' 0 ! i' \<le> k'" by simp
    assume "k < Suc (length xs')"
    hence K: "k' < length xs'"
      using I by simp
    let ?P = "\<lambda>n. foldl (+) 0 ns = n \<and> length ys = n"
    let ?Q = "\<lambda>n. \<forall>i < length ns.
      \<forall>j < offs ns 0 ! i. \<forall>k \<in> {offs ns 0 ! i..<n}.
        key (ys ! j) \<le> key (ys ! k)"
    let ?R = "\<forall>i < length ns'.
      \<forall>j < offs ns' 0 ! i. \<forall>k \<in> {offs ns' 0 ! i..<length xs'}.
        key (xs' ! j) \<le> key (xs' ! k)"
    assume "\<And>n. ?P n \<longrightarrow> ?Q n \<longrightarrow> ?R"
    hence "?P (n - Suc 0) \<longrightarrow> ?Q (n - Suc 0) \<longrightarrow> ?R" .
    hence "?Q (n - Suc 0) \<longrightarrow> ?R"
      using D and E by auto
    moreover have "?Q (n - Suc 0)"
    proof ((rule allI, rule impI)+, rule ballI, simp, erule conjE)
      fix i j k
      have "Suc i < Suc (length ns) \<longrightarrow> (\<forall>j < (0 # offs ns (Suc 0)) ! Suc i.
        \<forall>k \<in> {(0 # offs ns (Suc 0)) ! Suc i..<n}.
          key ((y # ys) ! j) \<le> key (ys ! (k - Suc 0)))"
        using F ..
      moreover assume "i < length ns"
      ultimately have "Suc j < Suc (offs ns 0 ! i) \<longrightarrow>
        (\<forall>k \<in> {Suc (offs ns 0 ! i)..<n}.
          key ((y # ys) ! Suc j) \<le> key (ys ! (k - Suc 0)))"
        by (auto simp add: offs_suc)
      moreover assume "j < offs ns 0 ! i"
      ultimately have "\<forall>k \<in> {Suc (offs ns 0 ! i)..<n}.
        key (ys ! j) \<le> key (ys ! (k - Suc 0))"
        by simp
      moreover assume "offs ns 0 ! i \<le> k" and "k < n - Suc 0"
      hence "Suc k \<in> {Suc (offs ns 0 ! i)..<n}" by simp
      ultimately have "key (ys ! j) \<le> key (ys ! (Suc k - Suc 0))" ..
      thus "key (ys ! j) \<le> key (ys ! k)" by simp
    qed
    ultimately have ?R ..
    from I show "key ((y # xs') ! j) \<le> key (xs' ! (k - Suc 0))"
    proof (cases j, simp_all)
      have "bn_inv p q (u, ns, ys)"
        using B by simp
      moreover have "add_inv (n - Suc 0) (u, ns, ys)"
        using D and E by auto
      moreover have "count_inv (\<lambda>x. count (mset ys) x) (u, ns, ys)" by simp
      ultimately have "count_inv (\<lambda>x. count (mset ys) x)
        (round index key p q r (u, ns, ys))"
        by (rule round_count_inv [OF A])
      hence "count (mset xs') (xs' ! k') = count (mset ys) (xs' ! k')"
        using C by simp
      moreover have "0 < count (mset xs') (xs' ! k')"
        using K by simp
      ultimately have "xs' ! k' \<in> set ys" by simp
      hence "\<exists>m < length ys. ys ! m = xs' ! k'"
        by (simp add: in_set_conv_nth)
      then obtain m where L: "m < length ys \<and> ys ! m = xs' ! k'" ..
      have "Suc 0 < Suc (length ns) \<longrightarrow> (\<forall>j < (0 # offs ns (Suc 0)) ! Suc 0.
        \<forall>k \<in> {(0 # offs ns (Suc 0)) ! Suc 0..<n}.
          key ((y # ys) ! j) \<le> key (ys ! (k - Suc 0)))"
        using F ..
      moreover have M: "0 < length ns"
        using D [symmetric] and E and L by (rule_tac ccontr, simp)
      ultimately have "\<forall>k \<in> {Suc (offs ns 0 ! 0)..<n}.
        key y \<le> key (ys ! (k - Suc 0))"
        by (auto simp add: offs_suc)
      hence "\<forall>k \<in> {Suc 0..<n}. key y \<le> key (ys ! (k - Suc 0))"
        using M by (cases ns, simp_all)
      moreover have "Suc m \<in> {Suc 0..<n}"
        using E and L by simp
      ultimately have "key y \<le> key (ys ! (Suc m - Suc 0))" ..
      thus "key y \<le> key (xs' ! k')"
        using L by simp
    next
      case (Suc j')
      moreover have "i' < length ns' \<longrightarrow> (\<forall>j < offs ns' 0 ! i'.
        \<forall>k \<in> {offs ns' 0 ! i'..<length xs'}. key (xs' ! j) \<le> key (xs' ! k))"
        using `?R` ..
      hence "j' < offs ns' 0 ! i' \<longrightarrow>
        (\<forall>k \<in> {offs ns' 0 ! i'..<length xs'}. key (xs' ! j') \<le> key (xs' ! k))"
        using G by simp
      ultimately have "\<forall>k \<in> {offs ns' 0 ! i'..<length xs'}.
        key (xs' ! j') \<le> key (xs' ! k)"
        using H by simp
      moreover have "k' \<in> {offs ns' 0 ! i'..<length xs'}"
        using J and K by simp
      ultimately show "key (xs' ! j') \<le> key (xs' ! k')" ..
    qed
  qed
next
  fix index p q r u m ns n and key :: "'a \<Rightarrow> 'b" and xs :: "'a list"
  let ?ws = "take (Suc (Suc m)) xs"
  let ?ys = "drop (Suc (Suc m)) xs"
  let ?r = "\<lambda>m'. round_suc_suc index key ?ws m m' u"
  let ?t = "\<lambda>r' v. round index key p q r' (v, ns, ?ys)"
  assume
    A: "index_less index key" and
    B: "index_mono index key" and
    C: "bn_inv p q (u, Suc (Suc m) # ns, xs)"
  assume
   "\<And>ws a b c d e f g h n.
      ws = ?ws \<Longrightarrow> a = bn_comp m p q r \<Longrightarrow> (b, c) = bn_comp m p q r \<Longrightarrow>
      d = ?r b \<Longrightarrow> (e, f) = ?r b \<Longrightarrow> (g, h) = f \<Longrightarrow>
        bn_inv p q (e, ns, ?ys) \<longrightarrow> add_inv n (e, ns, ?ys) \<longrightarrow>
          sort_inv key (e, ns, ?ys) \<longrightarrow> sort_inv key (?t c e)" and
   "add_inv n (u, Suc (Suc m) # ns, xs)" and
   "sort_inv key (u, Suc (Suc m) # ns, xs)"
  with C show "sort_inv key (round index key p q r (u, Suc (Suc m) # ns, xs))"
  proof (simp split: prod.split, ((rule_tac allI)+, (rule_tac impI)+)+,
   rule_tac ballI, simp, (erule_tac conjE)+, subst (asm) (2) add_base_zero, simp)
    fix m' r' v ms' ws' u' ns' xs' i j k
    let ?nmi = "mini ?ws key"
    let ?nma = "maxi ?ws key"
    let ?xmi = "?ws ! ?nmi"
    let ?xma = "?ws ! ?nma"
    let ?mi = "key ?xmi"
    let ?ma = "key ?xma"
    let ?k = "case m of 0 \<Rightarrow> m | Suc 0 \<Rightarrow> m | Suc (Suc i) \<Rightarrow> u + m'"
    let ?zs = "nths ?ws (- {?nmi, ?nma})"
    let ?ms = "enum ?zs index key ?k ?mi ?ma"
    let ?P = "\<lambda>n'. foldl (+) 0 ns = n' \<and> n - Suc (Suc m) = n'"
    let ?Q = "\<lambda>n'. \<forall>i < length ns.
      \<forall>j < offs ns 0 ! i. \<forall>k \<in> {offs ns 0 ! i..<n'}.
        key (xs ! Suc (Suc (m + j))) \<le> key (xs ! Suc (Suc (m + k)))"
    let ?R = "\<forall>i < length ns'.
      \<forall>j < offs ns' 0 ! i. \<forall>k \<in> {offs ns' 0 ! i..<length xs'}.
        key (xs' ! j) \<le> key (xs' ! k)"
    assume
      D: "?r m' = (v, ms', ws')" and
      E: "?t r' v = (u', ns', xs')" and
      F: "bn_comp m p q r = (m', r')" and
      G: "bn_valid m p q" and
      H: "Suc (Suc (foldl (+) 0 ns + m)) = n" and
      I: "length xs = n" and
      J: "\<forall>i < Suc (length ns). \<forall>j < (0 # offs ns (Suc (Suc m))) ! i.
        \<forall>k \<in> {(0 # offs ns (Suc (Suc m))) ! i..<n}.
          key (xs ! j) \<le> key (xs ! k)" and
      K: "i < length ms' + length ns'" and
      L: "j < offs (ms' @ ns') 0 ! i" and
      M: "offs (ms' @ ns') 0 ! i \<le> k" and
      N: "k < length ws' + length xs'"
    have O: "length ?ws = Suc (Suc m)"
      using H and I by simp
    with D [symmetric] have P: "length ws' = Suc (Suc m)"
      by (simp add: round_suc_suc_def Let_def fill_length split: if_split_asm)
    have Q: "\<And>i. i < m \<Longrightarrow>
      the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! i) \<in> set ?ws"
    proof -
      fix i
      let ?x = "the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! i)"
      assume R: "i < m"
      hence "0 < m" by simp
      hence "0 < ?k"
        by (drule_tac bn_comp_fst_nonzero [OF G], subst (asm) F,
         simp split: nat.split)
      hence "count (mset (map the (fill ?zs (offs ?ms 0)
        index key (length ?zs) ?mi ?ma))) ?x = count (mset ?zs) ?x"
        by (rule_tac fill_offs_enum_count_item [OF A], simp, rule_tac conjI,
         ((rule_tac mini_lb | rule_tac maxi_ub), erule_tac in_set_nthsD)+)
      hence "count (mset (map the (fill ?zs (offs ?ms 0)
        index key m ?mi ?ma))) ?x = count (mset ?zs) ?x"
        using O by (simp add: mini_maxi_nths)
      moreover have "0 < count (mset (map the (fill ?zs (offs ?ms 0)
        index key m ?mi ?ma))) ?x"
        using R by (simp add: fill_length)
      ultimately have "?x \<in> set ?zs" by simp
      thus "?x \<in> set ?ws"
        by (rule in_set_nthsD)
    qed
    have R: "\<And>i. i < Suc (Suc m) \<Longrightarrow> Suc (Suc m) \<le> k \<Longrightarrow>
      key (?ws ! i) \<le> key (xs' ! (k - Suc (Suc m)))"
    proof -
      fix i
      have "bn_inv p q (v, ns, ?ys)"
        using C by simp
      moreover have "add_inv (n - Suc (Suc m)) (v, ns, ?ys)"
        using H and I by simp
      moreover have "count_inv (\<lambda>x. count (mset ?ys) x) (v, ns, ?ys)"
        by simp
      ultimately have "count_inv (\<lambda>x. count (mset ?ys) x) (?t r' v)"
        by (rule round_count_inv [OF A])
      hence S: "count (mset xs') (xs' ! (k - Suc (Suc m))) =
        count (mset ?ys) (xs' ! (k - Suc (Suc m)))"
        using E by simp
      have "k < Suc (Suc (m + length xs'))"
        using N and P by simp
      moreover assume "Suc (Suc m) \<le> k"
      ultimately have "0 < count (mset xs') (xs' ! (k - Suc (Suc m)))"
        by simp
      hence "xs' ! (k - Suc (Suc m)) \<in> set ?ys"
        using S by simp
      hence "\<exists>p < length ?ys. ?ys ! p = xs' ! (k - Suc (Suc m))"
        by (simp add: in_set_conv_nth)
      then obtain p where
        T: "p < length ?ys \<and> ?ys ! p = xs' ! (k - Suc (Suc m))" ..
      have "Suc 0 < Suc (length ns) \<longrightarrow>
        (\<forall>j < (0 # offs ns (Suc (Suc m))) ! Suc 0.
         \<forall>k \<in> {(0 # offs ns (Suc (Suc m))) ! Suc 0..<n}.
           key (xs ! j) \<le> key (xs ! k))"
        using J ..
      moreover have U: "0 < length ns"
        using H [symmetric] and I and T by (rule_tac ccontr, simp)
      ultimately have "\<forall>j < offs ns (Suc (Suc m)) ! 0.
        \<forall>k \<in> {offs ns (Suc (Suc m)) ! 0..<n}. key (xs ! j) \<le> key (xs ! k)"
        by simp
      moreover assume "i < Suc (Suc m)"
      moreover have "offs ns (Suc (Suc m)) ! 0 = Suc (Suc m)"
        using U by (subst offs_base_zero, simp, cases ns, simp_all)
      ultimately have "\<forall>k \<in> {Suc (Suc m)..<n}. key (?ws ! i) \<le> key (xs ! k)"
        by simp
      moreover have "Suc (Suc m) + p \<in> {Suc (Suc m)..<n}"
        using I and T by (simp, arith)
      ultimately have "key (?ws ! i) \<le> key (xs ! (Suc (Suc m) + p))" ..
      thus "key (?ws ! i) \<le> key (xs' ! (k - Suc (Suc m)))"
        using O and T by simp
    qed
    assume "\<And>ws a b c d e f g h n'.
      ws = ?ws \<Longrightarrow> a = (m', r') \<Longrightarrow> b = m' \<and> c = r' \<Longrightarrow>
      d = (v, ms', ws') \<Longrightarrow> e = v \<and> f = (ms', ws') \<Longrightarrow> g = ms' \<and> h = ws' \<Longrightarrow>
        ?P n' \<longrightarrow> ?Q n' \<longrightarrow> ?R"
    hence "?P (n - Suc (Suc m)) \<longrightarrow> ?Q (n - Suc (Suc m)) \<longrightarrow> ?R"
      by simp
    hence "?Q (n - Suc (Suc m)) \<longrightarrow> ?R"
      using H by simp
    moreover have "?Q (n - Suc (Suc m))"
    proof ((rule allI, rule impI)+, rule ballI, simp, erule conjE,
     subst (1 2) append_take_drop_id [of "Suc (Suc m)", symmetric],
     simp only: nth_append O, simp)
      fix i j k
      have "Suc i < Suc (length ns) \<longrightarrow>
        (\<forall>j < (0 # offs ns (Suc (Suc m))) ! Suc i.
         \<forall>k \<in> {(0 # offs ns (Suc (Suc m))) ! Suc i..<n}.
           key ((xs) ! j) \<le> key (xs ! k))"
        using J ..
      moreover assume "i < length ns"
      ultimately have "j < offs ns 0 ! i \<longrightarrow>
        (\<forall>k \<in> {offs ns 0 ! i + Suc (Suc m)..<n}.
          key (xs ! (Suc (Suc m) + j)) \<le> key (xs ! k))"
        by (simp, subst (asm) offs_base_zero, simp,
         subst (asm) (2) offs_base_zero, simp_all)
      moreover assume "j < offs ns 0 ! i"
      ultimately have "\<forall>k \<in> {offs ns 0 ! i + Suc (Suc m)..<n}.
        key (?ys ! j) \<le> key (xs ! k)"
        using O by simp
      moreover assume "offs ns 0 ! i \<le> k" and "k < n - Suc (Suc m)"
      hence "Suc (Suc m) + k \<in> {offs ns 0 ! i + Suc (Suc m)..<n}"
        by simp
      ultimately have "key (?ys ! j) \<le> key (xs ! (Suc (Suc m) + k))" ..
      thus "key (?ys ! j) \<le> key (?ys ! k)"
        using O by simp
    qed
    ultimately have ?R ..
    show "key ((ws' @ xs') ! j) \<le> key ((ws' @ xs') ! k)"
    proof (simp add: nth_append not_less P, (rule_tac [!] conjI,
     rule_tac [!] impI)+, rule_tac [3] FalseE)
      assume
        S: "j < Suc (Suc m)" and
        T: "k < Suc (Suc m)"
      from D [symmetric] show "key (ws' ! j) \<le> key (ws' ! k)"
      proof (simp add: round_suc_suc_def Let_def split: if_split_asm,
       (erule_tac [2] conjE)+, simp_all)
        assume U: "?mi = ?ma"
        have "j < length ?ws"
          using S and O by simp
        hence "?ws ! j \<in> set ?ws"
          by (rule nth_mem)
        with U have "key (?ws ! j) = ?ma"
          by (rule mini_maxi_keys_eq)
        moreover have "k < length ?ws"
          using T and O by simp
        hence "?ws ! k \<in> set ?ws"
          by (rule nth_mem)
        with U have "key (?ws ! k) = ?ma"
          by (rule mini_maxi_keys_eq)
        ultimately show "key (?ws ! j) \<le> key (?ws ! k)" by simp
      next
        assume U: "ms' = Suc 0 # ?ms @ [Suc 0]"
        hence V: "j < (0 # offs (?ms @ Suc 0 # ns') (Suc 0)) ! i"
          using L by simp
        hence "\<exists>i'. i = Suc i'"
          by (rule_tac nat.exhaust [of i], simp_all)
        then obtain i' where W: "i = Suc i'" ..
        have "i < Suc (Suc (?k + length ns'))"
          using K and U by (simp add: enum_length)
        hence X: "i' < Suc (?k + length ns')"
          using W by simp
        hence Y: "j < Suc (offs (?ms @ Suc 0 # ns') 0 ! i')"
          using V and W by (simp add: enum_length offs_suc)
        have "(0 # offs (?ms @ Suc 0 # ns') (Suc 0)) ! i \<le> k"
          using M and U by simp
        hence "Suc (offs (?ms @ Suc 0 # ns') 0 ! i') \<le> k"
          using W and X by (simp add: enum_length offs_suc)
        moreover from this have "\<exists>k'. k = Suc k'"
          by (rule_tac nat.exhaust [of k], simp_all)
        then obtain k' where Z: "k = Suc k'" ..
        ultimately have AA: "offs (?ms @ Suc 0 # ns') 0 ! i' \<le> k'"
          by simp
        have AB: "j \<le> k'"
          using Y and AA by simp
        with Z show
         "key ((?xmi # map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma) @
            [?xma]) ! j) \<le>
          key ((?xmi # map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma) @
            [?xma]) ! k)"
        proof (cases j, case_tac [2] "j < Suc m", simp_all add: nth_append
         not_less fill_length, rule_tac [1-2] conjI, rule_tac [1-4] impI,
         rule_tac [5] FalseE, simp_all)
          assume "k' < m"
          hence "the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k') \<in> set ?ws"
            by (rule Q)
          thus "?mi \<le> key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k'))"
            by (rule mini_lb)
        next
          assume "m \<le> k'"
          hence "k' = m"
            using T and Z by simp
          thus "?mi \<le> key ([?xma] ! (k' - m))"
            by (simp, rule_tac mini_maxi_keys_le, rule_tac nth_mem [of 0],
             subst O, simp)
        next
          fix j'
          have "sort_inv key (0, ?ms, map the (fill ?zs (offs ?ms 0) index key
            (length ?zs) ?mi ?ma))"
            by (rule fill_sort_inv [OF A B], simp, rule conjI,
             ((rule mini_lb | rule maxi_ub), erule in_set_nthsD)+)
          hence "sort_inv key (0, ?ms, map the (fill ?zs (offs ?ms 0) index key
            m ?mi ?ma))"
            using O by (simp add: mini_maxi_nths)
          hence "\<forall>i < ?k. \<forall>j < offs ?ms 0 ! i. \<forall>k \<in> {offs ?ms 0 ! i..<m}.
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j)) \<le>
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k))"
            by (simp add: enum_length fill_length)
          moreover assume AC: "k' < m"
          hence AD: "offs (?ms @ Suc 0 # ns') 0 ! i' < m"
            using AA by simp
          have AE: "i' < ?k"
          proof (rule contrapos_pp [OF AD], simp add: not_less offs_append
           nth_append offs_length enum_length)
            have "0 < m"
              using AC by simp
            hence "0 < ?k"
              by (drule_tac bn_comp_fst_nonzero [OF G], subst (asm) F,
               simp split: nat.split)
            with A have "foldl (+) 0 ?ms = length ?zs"
              by (rule enum_add, simp, rule_tac conjI,
               ((rule_tac mini_lb | rule_tac maxi_ub), erule_tac in_set_nthsD)+)
            hence "foldl (+) 0 ?ms = m"
              using O by (simp add: mini_maxi_nths)
            with X show "m \<le> (foldl (+) 0 ?ms #
              offs ns' (Suc (foldl (+) 0 ?ms))) ! (i' - ?k)"
              by (cases "i' - ?k", simp_all, subst offs_base_zero, simp_all)
          qed
          ultimately have "\<forall>j < offs ?ms 0 ! i'. \<forall>k \<in> {offs ?ms 0 ! i'..<m}.
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j)) \<le>
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k))"
            by simp
          moreover assume "j = Suc j'"
          with Y and AE have "j' < offs ?ms 0 ! i'"
            by (simp add: offs_append nth_append offs_length enum_length)
          ultimately have "\<forall>k \<in> {offs ?ms 0 ! i'..<m}.
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j')) \<le>
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k))"
            by simp
          moreover from AA and AE have "offs ?ms 0 ! i' \<le> k'"
            by (simp add: offs_append nth_append offs_length enum_length)
          hence "k' \<in> {offs ?ms 0 ! i'..<m}"
            using AC by simp
          ultimately show
           "key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j')) \<le>
            key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! k'))" ..
        next
          fix j'
          assume "j' < m"
          hence "the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j') \<in> set ?ws"
            (is "?x \<in> _")
            by (rule Q)
          moreover assume "m \<le> k'"
          hence "k' = m"
            using T and Z by simp
          ultimately show "key ?x \<le> key ([?xma] ! (k' - m))"
            by (simp, rule_tac maxi_ub)
        next
          fix j'
          assume "j = Suc j'" and "m \<le> j'"
          hence "Suc m \<le> j" by simp
          hence "Suc (Suc m) \<le> k"
            using Z and AB by simp
          thus False
            using T by simp
        qed
      qed
    next
      assume
        S: "j < Suc (Suc m)" and
        T: "Suc (Suc m) \<le> k"
      from D [symmetric] show "key (ws' ! j) \<le> key (xs' ! (k - Suc (Suc m)))"
      proof (simp add: round_suc_suc_def Let_def split: if_split_asm,
       rule_tac R [OF S T], cases j, case_tac [2] "j < Suc m",
       simp_all add: nth_append not_less fill_length)
        have "?nmi < length ?ws"
          using O by (rule_tac mini_less, simp)
        hence "?nmi < Suc (Suc m)"
          using O by simp
        thus "?mi \<le> key (xs' ! (k - Suc (Suc m)))"
          using T by (rule R)
      next
        fix j'
        assume "j' < m"
        hence U: "the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j') \<in> set ?ws"
          by (rule Q)
        have "\<exists>p < Suc (Suc m). ?ws ! p =
          the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j')"
          using O and U by (simp add: in_set_conv_nth)
        then obtain p where V: "p < Suc (Suc m) \<and> ?ws ! p =
          the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j')" ..
        hence "key (?ws ! p) \<le> key (xs' ! (k - Suc (Suc m)))"
          using T by (rule_tac R, simp)
        thus "key (the (fill ?zs (offs ?ms 0) index key m ?mi ?ma ! j')) \<le>
          key (xs' ! (k - Suc (Suc m)))"
          using V by simp
      next
        fix j'
        assume "j = Suc j'" and "m \<le> j'"
        moreover from this have "Suc m \<le> j" by simp
        hence "j = Suc m"
          using S by simp
        ultimately have "j' = m" by simp
        thus "key ([?xma] ! (j' - m)) \<le> key (xs' ! (k - Suc (Suc m)))"
        proof simp
          have "?nma < length ?ws"
            using O by (rule_tac maxi_less, simp)
          hence "?nma < Suc (Suc m)"
            using O by simp
          thus "?ma \<le> key (xs' ! (k - Suc (Suc m)))"
            using T by (rule R)
        qed
      qed
    next
      assume "k < Suc (Suc m)" and "Suc (Suc m) \<le> j"
      hence "k < j" by simp
      moreover have "j < k"
        using L and M by simp
      ultimately show False by simp
    next
      assume
        S: "Suc (Suc m) \<le> j" and
        T: "Suc (Suc m) \<le> k"
      have U: "0 < length ns' \<and> 0 < length xs'"
      proof (rule ccontr, simp, erule disjE)
        have "bn_inv p q (v, ns, ?ys)"
          using C by simp
        moreover have "add_inv (n - Suc (Suc m)) (v, ns, ?ys)"
          using H and I by simp
        ultimately have "add_inv (n - Suc (Suc m)) (?t r' v)"
          by (rule round_add_inv [OF A])
        hence "length xs' = foldl (+) 0 ns'"
          using E by simp
        moreover assume "ns' = []"
        ultimately have "length xs' = 0" by simp
        hence "k < Suc (Suc m)"
          using N and P by simp
        thus False
          using T by simp
      next
        assume "xs' = []"
        hence "k < Suc (Suc m)"
          using N and P by simp
        thus False
          using T by simp
      qed
      hence V: "i - length ms' < length ns'"
        using K by arith
      hence W: "\<forall>j < offs ns' 0 ! (i - length ms').
        \<forall>k \<in> {offs ns' 0 ! (i - length ms')..<length xs'}.
          key (xs' ! j) \<le> key (xs' ! k)"
        using `?R` by simp
      from D [symmetric] have X: "foldl (+) 0 ms' = Suc (Suc m)"
      proof (simp add: round_suc_suc_def Let_def add_replicate add_suc
       split: if_split_asm, cases "m = 0")
        case True
        hence "?k = 0" by simp
        hence "length ?ms = 0"
          by (simp add: enum_length)
        thus "foldl (+) 0 ?ms = m"
          using True by simp
      next
        case False
        hence "0 < ?k"
          by (simp, drule_tac bn_comp_fst_nonzero [OF G], subst (asm) F,
           simp split: nat.split)
        with A have "foldl (+) 0 ?ms = length ?zs"
          by (rule enum_add, simp, rule_tac conjI,
           ((rule_tac mini_lb | rule_tac maxi_ub), erule_tac in_set_nthsD)+)
        thus "foldl (+) 0 ?ms = m"
          using O by (simp add: mini_maxi_nths)
      qed
      have "length ms' < i"
      proof (rule ccontr, simp add: not_less)
        assume "i \<le> length ms'"
        moreover have "length ms' < length (ms' @ ns')"
          using U by simp
        ultimately have "offs (ms' @ ns') 0 ! i \<le>
          offs (ms' @ ns') 0 ! (length ms')"
          by (rule offs_mono)
        also have "\<dots> = Suc (Suc m)"
          using U and X by (simp add: offs_append nth_append offs_length,
           cases ns', simp_all)
        finally have "offs (ms' @ ns') 0 ! i \<le> Suc (Suc m)" .
        hence "j < Suc (Suc m)"
          using L by simp
        thus False
          using S by simp
      qed
      hence Y: "offs (ms' @ ns') 0 ! i =
        Suc (Suc m) + offs ns' 0 ! (i - length ms')"
        using X by (simp add: offs_append nth_append offs_length,
         subst offs_base_zero [OF V], simp)
      hence "j < Suc (Suc m) + offs ns' 0 ! (i - length ms')"
        using L by simp
      moreover from this have "0 < offs ns' 0 ! (i - length ms')"
        using S by (rule_tac ccontr, simp)
      ultimately have "j - Suc (Suc m) < offs ns' 0 ! (i - length ms')"
        by simp
      hence Z: "\<forall>k \<in> {offs ns' 0 ! (i - length ms')..<length xs'}.
        key (xs' ! (j - Suc (Suc m))) \<le> key (xs' ! k)"
        using W by simp
      have "offs ns' 0 ! (i - length ms') \<le> k - Suc (Suc m)"
        using M and Y by simp
      moreover have "k - Suc (Suc m) < length xs'"
        using N and P and U by arith
      ultimately have "k - Suc (Suc m) \<in>
        {offs ns' 0 ! (i - length ms')..<length xs'}"
        by simp
      with Z show "key (xs' ! (j - Suc (Suc m))) \<le>
        key (xs' ! (k - Suc (Suc m)))" ..
    qed
  qed
qed

lemma gcsort_sort_inv:
  assumes
    A: "index_less index key" and
    B: "index_mono index key" and
    C: "add_inv n t" and
    D: "n \<le> p"
  shows "\<lbrakk>t' \<in> gcsort_set index key p t; sort_inv key t\<rbrakk> \<Longrightarrow>
    sort_inv key t'"
by (erule gcsort_set.induct, simp, drule gcsort_add_inv [OF A _ C D],
 rule round_sort_inv [OF A B], simp_all del: bn_inv.simps, erule conjE,
 frule sym, erule subst, rule bn_inv_intro, insert D, simp)

text \<open>
\null

The only remaining task is to address step 10 of the proof method, which is done by proving theorem
@{text gcsort_sorted}. It holds under the conditions that the objects' number is not larger than the
counters' upper bound and function @{text index} satisfies both predicates @{const index_less} and
@{const index_mono}, and states that function @{const gcsort} is successful in sorting the input
objects' list.

\null
\<close>

theorem gcsort_sorted:
  assumes
    A: "index_less index key" and
    B: "index_mono index key" and
    C: "length xs \<le> p"
  shows "sorted (map key (gcsort index key p xs))"
proof -
  let ?t = "(0, [length xs], xs)"
  have "sort_inv key (gcsort_aux index key p ?t)"
    by (rule gcsort_sort_inv [OF A B _ C], rule gcsort_add_input,
     rule gcsort_aux_set, rule gcsort_sort_input)
  moreover have "add_inv (length xs) (gcsort_aux index key p ?t)"
    by (rule gcsort_add_inv [OF A _ _ C],
     rule gcsort_aux_set, rule gcsort_add_input)
  ultimately have "sorted (map key (gcsort_out (gcsort_aux index key p ?t)))"
    by (rule gcsort_sort_intro, simp add: gcsort_sort_form)
  moreover have "?t = gcsort_in xs"
    by (simp add: gcsort_in_def)
  ultimately show ?thesis
    by (simp add: gcsort_def)
qed

end
