(*  Title:       An Efficient Generalization of Counting Sort for Large, possibly Infinite Key Ranges
    Author:      Pasquale Noce
                 Software Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Proof of objects' conservation"

theory Conservation
  imports 
    Algorithm 
    "HOL-Library.Multiset"
begin

text \<open>
\null

In this section, it is formally proven that GCsort \emph{conserves objects}, viz. that the objects'
list returned by function @{const gcsort} contains as many occurrences of any given object as the
input objects' list.

Here below, steps 5, 6, and 7 of the proof method are accomplished. Particularly, @{text count_inv}
is the predicate that will be shown to be invariant over inductive set @{const gcsort_set}.

\null
\<close>

fun count_inv :: "('a \<Rightarrow> nat) \<Rightarrow> nat \<times> nat list \<times> 'a list \<Rightarrow> bool" where
"count_inv f (u, ns, xs) = (\<forall>x. count (mset xs) x = f x)"

lemma gcsort_count_input:
 "count_inv (count (mset xs)) (0, [length xs], xs)"
by simp

lemma gcsort_count_intro:
 "count_inv f t \<Longrightarrow> count (mset (gcsort_out t)) x = f x"
by (cases t, simp add: gcsort_out_def)

text \<open>
\null

The main task to be accomplished to prove that GCsort conserves objects is to prove that so does
function @{const fill} in case its input offsets' list is computed via the composition of functions
@{const offs} and @{const enum}, as happens within function @{const round}.

To achieve this result, a multi-step strategy will be adopted. The first step, addressed here below,
opens with the definition of predicate @{text offs_pred}, satisfied by an offsets' list $ns$ and an
objects' list $xs$ just in case each bucket delimited by $ns$ is sufficiently large to accommodate
the corresponding objects in $xs$. Then, lemma @{text offs_pred_cons} shows that this predicate, if
satisfied initially, keeps being true if each object in $xs$ is consumed as happens within function
@{const fill}, viz. increasing the corresponding offset in $ns$ by one.

\null
\<close>

definition offs_num :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat" where
"offs_num n xs index key mi ma i \<equiv>
  length [x\<leftarrow>xs. index key x n mi ma = i]"

abbreviation offs_set_next :: "nat list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat set" where
"offs_set_next ns xs index key mi ma i \<equiv>
  {k. k < length ns \<and> i < k \<and> 0 < offs_num (length ns) xs index key mi ma k}"

abbreviation offs_set_prev :: "nat list \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat set" where
"offs_set_prev ns xs index key mi ma i \<equiv>
  {k. i < length ns \<and> k < i \<and> 0 < offs_num (length ns) xs index key mi ma k}"

definition offs_next :: "nat list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat" where
"offs_next ns ub xs index key mi ma i \<equiv>
  if offs_set_next ns xs index key mi ma i = {}
  then ub else ns ! Min (offs_set_next ns xs index key mi ma i)"

definition offs_none :: "nat list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> bool" where
"offs_none ns ub xs index key mi ma i \<equiv>
  (\<exists>j < length ns. 0 < offs_num (length ns) xs index key mi ma j \<and>
    i \<in> {ns ! j + offs_num (length ns) xs index key mi ma j..<
      offs_next ns ub xs index key mi ma j}) \<or>
  offs_num (length ns) xs index key mi ma 0 = 0 \<and>
    i < offs_next ns ub xs index key mi ma 0 \<or>
  0 < offs_num (length ns) xs index key mi ma 0 \<and>
    i < ns ! 0"

definition offs_pred :: "nat list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a, 'b) index_sign \<Rightarrow>
  ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" where
"offs_pred ns ub xs index key mi ma \<equiv>
  \<forall>i < length ns. offs_num (length ns) xs index key mi ma i \<le>
    offs_next ns ub xs index key mi ma i - ns ! i"

lemma offs_num_cons:
 "offs_num n (x # xs) index key mi ma i =
   (if index key x n mi ma = i then Suc else id) (offs_num n xs index key mi ma i)"
by (simp add: offs_num_def)

lemma offs_next_prev:
 "(0 < offs_num (length ns) xs index key mi ma i \<and>
    offs_set_next ns xs index key mi ma i \<noteq> {} \<and>
    Min (offs_set_next ns xs index key mi ma i) = j) =
  (0 < offs_num (length ns) xs index key mi ma j \<and>
    offs_set_prev ns xs index key mi ma j \<noteq> {} \<and>
    Max (offs_set_prev ns xs index key mi ma j) = i)"
  (is "?P = ?Q")
proof (rule iffI, (erule_tac [!] conjE)+)
  let ?A = "offs_set_next ns xs index key mi ma i"
  let ?B = "offs_set_prev ns xs index key mi ma j"
  assume
    A: "0 < offs_num (length ns) xs index key mi ma i" and
    B: "?A \<noteq> {}" and
    C: "Min ?A = j"
  have "Min ?A \<in> ?A"
    using B by (rule_tac Min_in, simp)
  hence D: "j \<in> ?A"
    using C by simp
  hence E: "i \<in> ?B"
    using A by simp
  show ?Q
  proof (rule conjI, rule_tac [2] conjI)
    show "0 < offs_num (length ns) xs index key mi ma j"
      using D by simp
  next
    show "?B \<noteq> {}"
      using E by blast
  next
    from E show "Max ?B = i"
    proof (subst Max_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
     (erule_tac conjE)+, rule_tac ccontr, simp)
      fix k
      assume F: "k < j" and "j < length ns"
      hence "k < length ns" by simp
      moreover assume
       "\<not> k \<le> i" and
       "0 < offs_num (length ns) xs index key mi ma k"
      ultimately have "k \<in> ?A" by simp
      hence "Min ?A \<le> k"
        by (rule_tac Min_le, simp)
      thus False
        using C and F by simp
    qed
  qed
next
  let ?A = "offs_set_prev ns xs index key mi ma j"
  let ?B = "offs_set_next ns xs index key mi ma i"
  assume
    A: "0 < offs_num (length ns) xs index key mi ma j" and
    B: "?A \<noteq> {}" and
    C: "Max ?A = i"
  have "Max ?A \<in> ?A"
    using B by (rule_tac Max_in, simp)
  hence D: "i \<in> ?A"
    using C by simp
  hence E: "j \<in> ?B"
    using A by simp
  show ?P
  proof (rule conjI, rule_tac [2] conjI)
    show "0 < offs_num (length ns) xs index key mi ma i"
      using D by simp
  next
    show "?B \<noteq> {}"
      using E by blast
  next
    from E show "Min ?B = j"
    proof (subst Min_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
     (erule_tac conjE)+, rule_tac ccontr, simp)
      fix k
      assume
       "j < length ns" and
       "\<not> j \<le> k" and
       "0 < offs_num (length ns) xs index key mi ma k"
      hence "k \<in> ?A" by simp
      hence "k \<le> Max ?A"
        by (rule_tac Max_ge, simp)
      moreover assume "i < k"
      ultimately show False
        using C by simp
    qed
  qed
qed

lemma offs_next_cons_eq:
  assumes
    A: "index key x (length ns) mi ma = i" and
    B: "i < length ns" and
    C: "0 < offs_num (length ns) (x # xs) index key mi ma j"
  shows
   "offs_set_prev ns (x # xs) index key mi ma i = {} \<or>
      Max (offs_set_prev ns (x # xs) index key mi ma i) \<noteq> j \<Longrightarrow>
    offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
      offs_next ns ub (x # xs) index key mi ma j"
  (is "?P \<or> ?Q \<Longrightarrow> _")
proof (simp only: disj_imp, cases "j < i")
  let ?A = "offs_set_prev ns (x # xs) index key mi ma i"
  let ?B = "offs_set_next (ns[i := Suc (ns ! i)]) xs index key mi ma j"
  let ?C = "offs_set_next ns (x # xs) index key mi ma j"
  case True
  hence D: "j \<in> ?A"
    using B and C by simp
  hence "j \<le> Max ?A"
    by (rule_tac Max_ge, simp)
  moreover assume "\<not> ?P \<longrightarrow> ?Q"
  hence ?Q
    using D by blast
  ultimately have E: "j < Max ?A" by simp
  have F: "Max ?A \<in> ?A"
    using D by (rule_tac Max_in, simp, blast)
  have G: "Max ?A \<in> ?B"
  proof (simp, rule conjI, rule_tac [2] conjI)
    show "Max ?A < length ns"
      using F by auto
  next
    show "j < Max ?A"
      using E .
  next
    have "0 < offs_num (length ns) (x # xs) index key mi ma (Max ?A)"
      using F by blast
    moreover have "Max ?A < i"
      using F by blast
    ultimately show "0 < offs_num (length ns) xs index key mi ma (Max ?A)"
      using A by (simp add: offs_num_cons)
  qed
  hence H: "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
    ns[i := Suc (ns ! i)] ! Min ?B"
    by (simp only: offs_next_def split: if_split, blast)
  have "Min ?B \<le> Max ?A"
    using G by (rule_tac Min_le, simp)
  moreover have "Max ?A < i"
    using F by blast
  ultimately have I: "Min ?B < i" by simp
  hence J: "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
    ns ! Min ?B"
    using H by simp
  have "Min ?B \<in> ?B"
    using G by (rule_tac Min_in, simp, blast)
  hence K: "Min ?B \<in> ?C"
    using A and I by (simp add: offs_num_cons)
  hence L: "Min ?C \<le> Min ?B"
    by (rule_tac Min_le, simp)
  have "Min ?C \<in> ?C"
    using K by (rule_tac Min_in, simp, blast)
  moreover have "Min ?C < i"
    using L and I by simp
  ultimately have "Min ?C \<in> ?B"
    using A by (simp add: offs_num_cons)
  hence "Min ?B \<le> Min ?C"
    using G by (rule_tac Min_le, simp)
  hence "Min ?B = Min ?C"
    using L by simp
  moreover have "offs_next ns ub (x # xs) index key mi ma j = ns ! Min ?C"
    using K by (simp only: offs_next_def split: if_split, blast)
  ultimately show ?thesis
    using J by simp
next
  let ?A = "offs_set_next (ns[i := Suc (ns ! i)]) xs index key mi ma j"
  let ?B = "offs_set_next ns (x # xs) index key mi ma j"
  case False
  hence "?A = ?B"
    using A by (rule_tac set_eqI, simp add: offs_num_cons)
  thus ?thesis
  proof (simp only: offs_next_def split: if_split,
   (rule_tac conjI, blast, rule_tac impI)+)
    assume "?B \<noteq> {}"
    hence "Min ?B \<in> ?B"
      by (rule_tac Min_in, simp)
    hence "i < Min ?B"
      using False by simp
    thus "ns[i := Suc (ns ! i)] ! Min ?B = ns ! Min ?B" by simp
  qed
qed

lemma offs_next_cons_neq:
  assumes
    A: "index key x (length ns) mi ma = i" and
    B: "offs_set_prev ns (x # xs) index key mi ma i \<noteq> {}" and
    C: "Max (offs_set_prev ns (x # xs) index key mi ma i) = j"
  shows "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
    (if 0 < offs_num (length ns) xs index key mi ma i
     then Suc (ns ! i)
     else offs_next ns ub (x # xs) index key mi ma i)"
proof (simp, rule conjI, rule_tac [!] impI)
  let ?A = "offs_set_next ns (x # xs) index key mi ma j"
  assume "0 < offs_num (length ns) xs index key mi ma i"
  with A have "offs_set_next (ns[i := Suc (ns ! i)]) xs index key mi ma j = ?A"
    by (rule_tac set_eqI, rule_tac iffI, simp_all add: offs_num_cons split:
     if_split_asm)
  moreover have "0 < offs_num (length ns) (x # xs) index key mi ma i"
    using A by (simp add: offs_num_def)
  hence "0 < offs_num (length ns) (x # xs) index key mi ma j \<and> ?A \<noteq> {} \<and>
    Min ?A = i"
    using B and C by (subst offs_next_prev, simp)
  ultimately show "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
    Suc (ns ! i)"
    using B by (simp only: offs_next_def, simp, subst nth_list_update_eq, blast,
     simp)
next
  let ?A = "offs_set_prev ns (x # xs) index key mi ma i"
  assume "offs_num (length ns) xs index key mi ma i = 0"
  with A have "offs_set_next (ns[i := Suc (ns ! i)]) xs index key mi ma j =
    offs_set_next ns (x # xs) index key mi ma i"
  proof (rule_tac set_eqI, rule_tac iffI, simp_all add: offs_num_cons split:
   if_split_asm, rule_tac conjI, rule_tac notI, simp, rule_tac impI,
   (erule_tac [!] conjE)+, rule_tac ccontr, simp_all)
    fix k
    have "i < length ns"
      using B by blast
    moreover assume "i \<noteq> k" and "\<not> i < k"
    hence "k < i" by simp
    moreover assume "0 < offs_num (length ns) xs index key mi ma k"
    ultimately have "k \<in> ?A"
      by (simp add: offs_num_cons)
    hence "k \<le> Max ?A"
      by (rule_tac Max_ge, simp)
    moreover assume "j < k"
    ultimately show False
      using C by simp
  next
    fix k
    have "Max ?A \<in> ?A"
      using B by (rule_tac Max_in, simp_all)
    hence "j < i"
      using C by simp
    moreover assume "i < k"
    ultimately show "j < k" by simp
  qed
  with B show "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j =
    offs_next ns ub (x # xs) index key mi ma i"
  proof (simp only: offs_next_def split: if_split, (rule_tac conjI, rule_tac [!] impI,
   simp)+, subst nth_list_update, blast, simp (no_asm_simp))
    assume "offs_set_next ns (x # xs) index key mi ma i \<noteq> {}"
    hence "Min (offs_set_next ns (x # xs) index key mi ma i)
      \<in> offs_set_next ns (x # xs) index key mi ma i"
      by (rule_tac Min_in, simp)
    thus "i \<noteq> Min (offs_set_next ns (x # xs) index key mi ma i)" by simp
  qed
qed

lemma offs_pred_ub_aux [rule_format]:
  assumes A: "offs_pred ns ub xs index key mi ma"
  shows "i < length ns \<Longrightarrow>
    \<forall>j < length ns. i \<le> j \<longrightarrow> 0 < offs_num (length ns) xs index key mi ma j \<longrightarrow>
      ns ! j + offs_num (length ns) xs index key mi ma j \<le> ub"
proof (erule strict_inc_induct, rule_tac [!] allI, (rule_tac [!] impI)+,
 drule le_less_Suc_eq, simp_all)
  fix i
  assume B: "length ns = Suc i"
  hence "offs_num (Suc i) xs index key mi ma i \<le>
    offs_next ns ub xs index key mi ma i - ns ! i"
    using A by (simp add: offs_pred_def)
  moreover have "offs_next ns ub xs index key mi ma i = ub"
    using B by (simp add: offs_next_def)
  ultimately have "offs_num (Suc i) xs index key mi ma i \<le> ub - ns ! i" by simp
  moreover assume "0 < offs_num (Suc i) xs index key mi ma i"
  ultimately show "ns ! i + offs_num (Suc i) xs index key mi ma i \<le> ub" by simp
next
  fix i j
  assume "j < length ns"
  hence "offs_num (length ns) xs index key mi ma j \<le>
    offs_next ns ub xs index key mi ma j - ns ! j"
    using A by (simp add: offs_pred_def)
  moreover assume
    B: "\<forall>k < length ns. Suc i \<le> k \<longrightarrow>
      0 < offs_num (length ns) xs index key mi ma k \<longrightarrow>
      ns ! k + offs_num (length ns) xs index key mi ma k \<le> ub" and
    C: "i \<le> j"
  have "offs_next ns ub xs index key mi ma j \<le> ub"
  proof (simp only: offs_next_def split: if_split, rule conjI, simp, rule impI)
    let ?A = "offs_set_next ns xs index key mi ma j"
    assume "?A \<noteq> {}"
    hence "Min ?A \<in> ?A"
      by (rule_tac Min_in, simp)
    hence "ns ! Min ?A + offs_num (length ns) xs index key mi ma (Min ?A) \<le> ub"
      using B and C by simp
    thus "ns ! Min ?A \<le> ub" by simp
  qed
  ultimately have "offs_num (length ns) xs index key mi ma j \<le> ub - ns ! j"
    by simp
  moreover assume "0 < offs_num (length ns) xs index key mi ma j"
  ultimately show "ns ! j + offs_num (length ns) xs index key mi ma j \<le> ub"
    by simp
qed

lemma offs_pred_ub:
 "\<lbrakk>offs_pred ns ub xs index key mi ma; i < length ns;
   0 < offs_num (length ns) xs index key mi ma i\<rbrakk> \<Longrightarrow>
     ns ! i + offs_num (length ns) xs index key mi ma i \<le> ub"
by (drule offs_pred_ub_aux, assumption+, simp)

lemma offs_pred_asc_aux [rule_format]:
  assumes A: "offs_pred ns ub xs index key mi ma"
  shows "i < length ns \<Longrightarrow>
    \<forall>j k. k < length ns \<longrightarrow> i \<le> j \<longrightarrow> j < k \<longrightarrow>
      0 < offs_num (length ns) xs index key mi ma j \<longrightarrow>
      0 < offs_num (length ns) xs index key mi ma k \<longrightarrow>
      ns ! j + offs_num (length ns) xs index key mi ma j \<le> ns ! k"
proof (erule strict_inc_induct, simp, (rule allI)+, (rule impI)+, simp)
  fix i j k
  assume
    B: "k < length ns" and
    C: "j < k"
  hence "j < length ns" by simp
  hence "offs_num (length ns) xs index key mi ma j \<le>
    offs_next ns ub xs index key mi ma j - ns ! j"
    using A by (simp add: offs_pred_def)
  moreover assume
    D: "\<forall>j k. k < length ns \<longrightarrow> Suc i \<le> j \<longrightarrow> j < k \<longrightarrow>
      0 < offs_num (length ns) xs index key mi ma j \<longrightarrow>
      0 < offs_num (length ns) xs index key mi ma k \<longrightarrow>
      ns ! j + offs_num (length ns) xs index key mi ma j \<le> ns ! k" and
    E: "i \<le> j" and
    F: "0 < offs_num (length ns) xs index key mi ma k"
  have "offs_next ns ub xs index key mi ma j \<le> ns ! k"
  proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI,
   rule ccontr, simp)
    assume "\<forall>n > j. n < length ns \<longrightarrow>
      offs_num (length ns) xs index key mi ma n = 0"
    hence "offs_num (length ns) xs index key mi ma k = 0"
      using B and C by simp
    thus False
      using F by simp
  next
    let ?A = "offs_set_next ns xs index key mi ma j"
    have G: "k \<in> ?A"
      using B and C and F by simp
    hence "Min ?A \<le> k"
      by (rule_tac Min_le, simp)
    hence "Min ?A < k \<or> Min ?A = k"
      by (simp add: le_less)
    moreover {
      have "Suc i \<le> Min ?A \<longrightarrow> Min ?A < k \<longrightarrow>
        0 < offs_num (length ns) xs index key mi ma (Min ?A) \<longrightarrow>
        ns ! Min ?A + offs_num (length ns) xs index key mi ma (Min ?A) \<le> ns ! k"
        using B and D and F by simp
      moreover assume "Min ?A < k"
      moreover have "Min ?A \<in> ?A"
        using G by (rule_tac Min_in, simp, blast)
      ultimately have "ns ! Min ?A < ns ! k"
        using E by simp
    }
    moreover {
      assume "Min ?A = k"
      hence "ns ! Min ?A = ns ! k" by simp
    }
    ultimately show "ns ! Min ?A \<le> ns ! k"
      by (simp add: le_less, blast)
  qed
  ultimately have "offs_num (length ns) xs index key mi ma j \<le> ns ! k - ns ! j"
    by simp
  moreover assume "0 < offs_num (length ns) xs index key mi ma j"
  ultimately show "ns ! j + offs_num (length ns) xs index key mi ma j \<le> ns ! k"
    by simp
qed

lemma offs_pred_asc:
 "\<lbrakk>offs_pred ns ub xs index key mi ma; i < j; j < length ns;
   0 < offs_num (length ns) xs index key mi ma i;
   0 < offs_num (length ns) xs index key mi ma j\<rbrakk> \<Longrightarrow>
     ns ! i + offs_num (length ns) xs index key mi ma i \<le> ns ! j"
by (drule offs_pred_asc_aux, erule less_trans, assumption+, rule order_refl)

lemma offs_pred_next:
  assumes
    A: "offs_pred ns ub xs index key mi ma" and
    B: "i < length ns" and
    C: "0 < offs_num (length ns) xs index key mi ma i"
  shows "ns ! i < offs_next ns ub xs index key mi ma i"
proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI)
  have "ns ! i + offs_num (length ns) xs index key mi ma i \<le> ub"
    using A and B and C by (rule offs_pred_ub)
  thus "ns ! i < ub"
    using C by simp
next
  assume "offs_set_next ns xs index key mi ma i \<noteq> {}"
  hence "Min (offs_set_next ns xs index key mi ma i)
    \<in> offs_set_next ns xs index key mi ma i"
    by (rule_tac Min_in, simp)
  hence "ns ! i + offs_num (length ns) xs index key mi ma i \<le>
    ns ! Min (offs_set_next ns xs index key mi ma i)"
    using C by (rule_tac offs_pred_asc [OF A], simp_all)
  thus "ns ! i < ns ! Min (offs_set_next ns xs index key mi ma i)"
    using C by simp
qed

lemma offs_pred_next_cons_less:
  assumes
    A: "offs_pred ns ub (x # xs) index key mi ma" and
    B: "index key x (length ns) mi ma = i" and
    C: "offs_set_prev ns (x # xs) index key mi ma i \<noteq> {}" and
    D: "Max (offs_set_prev ns (x # xs) index key mi ma i) = j"
  shows "offs_next ns ub (x # xs) index key mi ma j <
    offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j"
  (is "?M < ?N")
proof -
  have E: "0 < offs_num (length ns) (x # xs) index key mi ma i"
    using B by (simp add: offs_num_cons)
  hence "0 < offs_num (length ns) (x # xs) index key mi ma j \<and>
    offs_set_next ns (x # xs) index key mi ma j \<noteq> {} \<and>
    Min (offs_set_next ns (x # xs) index key mi ma j) = i"
    using C and D by (subst offs_next_prev, simp)
  hence F: "?M = ns ! i"
    by (simp only: offs_next_def, simp)
  have "?N = (if 0 < offs_num (length ns) xs index key mi ma i
    then Suc (ns ! i)
    else offs_next ns ub (x # xs) index key mi ma i)"
    using B and C and D by (rule offs_next_cons_neq)
  thus ?thesis
  proof (split if_split_asm)
    assume "?N = Suc (ns ! i)"
    thus ?thesis
      using F by simp
  next
    assume "?N = offs_next ns ub (x # xs) index key mi ma i"
    moreover have "ns ! i < offs_next ns ub (x # xs) index key mi ma i"
      using C by (rule_tac offs_pred_next [OF A _ E], blast)
    ultimately show ?thesis
      using F by simp
  qed
qed

lemma offs_pred_next_cons:
  assumes
    A: "offs_pred ns ub (x # xs) index key mi ma" and
    B: "index key x (length ns) mi ma = i" and
    C: "i < length ns" and
    D: "0 < offs_num (length ns) (x # xs) index key mi ma j"
  shows "offs_next ns ub (x # xs) index key mi ma j \<le>
    offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma j"
  (is "?M \<le> ?N")
proof -
  let ?P = "offs_set_prev ns (x # xs) index key mi ma i \<noteq> {} \<and>
    Max (offs_set_prev ns (x # xs) index key mi ma i) = j"
  have "?P \<or> \<not> ?P" by blast
  moreover {
    assume ?P
    hence "?M < ?N"
      using B by (rule_tac offs_pred_next_cons_less [OF A], simp_all)
    hence ?thesis by simp
  }
  moreover {
    assume "\<not> ?P"
    hence "?N = ?M"
      by (rule_tac offs_next_cons_eq [OF B C D], blast)
    hence ?thesis by simp
  }
  ultimately show ?thesis ..
qed

lemma offs_pred_cons:
  assumes
    A: "offs_pred ns ub (x # xs) index key mi ma" and
    B: "index key x (length ns) mi ma = i" and
    C: "i < length ns"
  shows "offs_pred (ns[i := Suc (ns ! i)]) ub xs index key mi ma"
  using A
proof (simp add: offs_pred_def, rule_tac allI, rule_tac impI, simp)
  let ?ns' = "ns[i := Suc (ns ! i)]"
  fix j
  assume
   "\<forall>j < length ns. offs_num (length ns) (x # xs) index key mi ma j \<le>
      offs_next ns ub (x # xs) index key mi ma j - ns ! j" and
   "j < length ns"
  hence D: "offs_num (length ns) (x # xs) index key mi ma j \<le>
    offs_next ns ub (x # xs) index key mi ma j - ns ! j"
    by simp
  from B and C show "offs_num (length ns) xs index key mi ma j \<le>
    offs_next ?ns' ub xs index key mi ma j - ?ns' ! j"
  proof (cases "j = i", case_tac [2] "0 < offs_num (length ns) xs index key mi ma j",
   simp_all)
    assume "j = i"
    hence "offs_num (length ns) xs index key mi ma i \<le>
      offs_next ns ub (x # xs) index key mi ma i - Suc (ns ! i)"
      using B and D by (simp add: offs_num_cons)
    moreover have "offs_next ns ub (x # xs) index key mi ma i \<le>
      offs_next ?ns' ub xs index key mi ma i"
      using B by (rule_tac offs_pred_next_cons [OF A _ C], simp_all add:
       offs_num_cons)
    ultimately show "offs_num (length ns) xs index key mi ma i \<le>
      offs_next ?ns' ub xs index key mi ma i - Suc (ns ! i)"
      by simp
  next
    assume "j \<noteq> i"
    hence "offs_num (length ns) xs index key mi ma j \<le>
      offs_next ns ub (x # xs) index key mi ma j - ns ! j"
      using B and D by (simp add: offs_num_cons)
    moreover assume "0 < offs_num (length ns) xs index key mi ma j"
    hence "offs_next ns ub (x # xs) index key mi ma j \<le>
      offs_next ?ns' ub xs index key mi ma j"
      using B by (rule_tac offs_pred_next_cons [OF A _ C], simp_all add:
       offs_num_cons)
    ultimately show "offs_num (length ns) xs index key mi ma j \<le>
      offs_next ?ns' ub xs index key mi ma j - ns ! j"
      by simp
  qed
qed

text \<open>
\null

The next step consists of proving, as done in lemma @{text fill_count_item} in what follows, that if
certain conditions hold, particularly if offsets' list $ns$ and objects' list $xs$ satisfy predicate
@{const offs_pred}, then function @{const fill} conserves objects if called using $xs$ and $ns$ as
its input arguments.

This lemma is proven by induction on $xs$. Hence, lemma @{thm [source] offs_pred_cons}, proven in
the previous step, is used to remove the antecedent containing predicate @{const offs_pred} from the
induction hypothesis, which has the form of an implication.

\null
\<close>

lemma offs_next_zero:
  assumes
    A: "i < length ns" and
    B: "offs_num (length ns) xs index key mi ma i = 0" and
    C: "offs_set_prev ns xs index key mi ma i = {}"
  shows "offs_next ns ub xs index key mi ma 0 =
    offs_next ns ub xs index key mi ma i"
proof -
  have "offs_set_next ns xs index key mi ma 0 =
    offs_set_next ns xs index key mi ma i"
  proof (rule set_eqI, rule iffI, simp_all, (erule conjE)+, rule ccontr, simp add:
   not_less)
    fix j
    assume D: "0 < offs_num (length ns) xs index key mi ma j"
    assume "j \<le> i"
    hence "j < i \<or> j = i"
      by (simp add: le_less)
    moreover {
      assume "j < i"
      hence "j \<in> offs_set_prev ns xs index key mi ma i"
        using A and D by simp
      hence False
        using C by simp
    }
    moreover {
      assume "j = i"
      hence False
        using B and D by simp
    }
    ultimately show False ..
  qed
  thus ?thesis
    by (simp only: offs_next_def)
qed

lemma offs_next_zero_cons_eq:
  assumes
    A: "index key x (length ns) mi ma = i" and
    B: "offs_num (length ns) (x # xs) index key mi ma 0 = 0" and
    C: "offs_set_prev ns (x # xs) index key mi ma i \<noteq> {}"
      (is "?A \<noteq> _")
  shows "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma 0 =
    offs_next ns ub (x # xs) index key mi ma 0"
proof -
  have D: "Min ?A \<in> ?A"
    using C by (rule_tac Min_in, simp)
  moreover have E: "0 < Min ?A"
  proof (rule ccontr, simp)
    assume "Min ?A = 0"
    hence "offs_num (length ns) (x # xs) index key mi ma (Min ?A) = 0"
      using B by simp
    moreover have "0 < offs_num (length ns) (x # xs) index key mi ma (Min ?A)"
      using D by auto
    ultimately show False by simp
  qed
  ultimately have "Min ?A \<in> offs_set_next ns (x # xs) index key mi ma 0"
    (is "_ \<in> ?B")
    by auto
  moreover from this have "Min ?B = Min ?A"
  proof (subst Min_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
   (erule_tac conjE)+, rule_tac ccontr, simp add: not_le)
    fix j
    assume F: "j < Min ?A"
    have "i < length ns"
      using D by simp
    moreover have "Min ?A < i"
      using D by auto
    hence "j < i"
      using F by simp
    moreover assume "0 < offs_num (length ns) (x # xs) index key mi ma j"
    ultimately have "j \<in> ?A" by simp
    hence "Min ?A \<le> j"
      by (rule_tac Min_le, simp)
    thus False
      using F by simp
  qed
  moreover have "Min ?A \<in> offs_set_next (ns[i := Suc (ns ! i)])
    xs index key mi ma 0"
    (is "_ \<in> ?C")
    using D and E by (auto, simp add: offs_num_cons A [symmetric])
  moreover from this have "Min ?C = Min ?A"
  proof (subst Min_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
   (erule_tac conjE)+, rule_tac ccontr, simp add: not_le)
    fix j
    assume F: "j < Min ?A"
    have "i < length ns"
      using D by simp
    moreover have "Min ?A < i"
      using D by auto
    hence "j < i"
      using F by simp
    moreover assume "0 < offs_num (length ns) xs index key mi ma j"
    hence "0 < offs_num (length ns) (x # xs) index key mi ma j"
      by (simp add: offs_num_cons)
    ultimately have "j \<in> ?A" by simp
    hence "Min ?A \<le> j"
      by (rule_tac Min_le, simp)
    thus False
      using F by simp
  qed
  moreover have "Min ?A < i"
    using D by auto
  ultimately show ?thesis
    by (simp only: offs_next_def split: if_split,
     (rule_tac conjI, blast, rule_tac impI)+, simp)
qed

lemma offs_next_zero_cons_neq:
  assumes
    A: "index key x (length ns) mi ma = i" and
    B: "i < length ns" and
    C: "0 < i" and
    D: "offs_set_prev ns (x # xs) index key mi ma i = {}"
  shows "offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma 0 =
    (if 0 < offs_num (length ns) xs index key mi ma i
     then Suc (ns ! i)
     else offs_next ns ub (x # xs) index key mi ma i)"
proof (simp, rule conjI, rule_tac [!] impI)
  let ?ns' = "ns[i := Suc (ns ! i)]"
  assume "0 < offs_num (length ns) xs index key mi ma i"
  with A have "offs_set_next ?ns' xs index key mi ma 0 =
    offs_set_next ns (x # xs) index key mi ma 0"
    by (rule_tac set_eqI, rule_tac iffI, simp_all add: offs_num_cons split:
     if_split_asm)
  moreover have "i \<in> offs_set_next ns (x # xs) index key mi ma 0"
    using A and B and C by (simp add: offs_num_cons)
  moreover from this have
   "Min (offs_set_next ns (x # xs) index key mi ma 0) = i"
  proof (subst Min_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
   (erule_tac conjE)+, rule_tac ccontr, simp add: not_le)
    fix j
    assume "j < i" and "0 < offs_num (length ns) (x # xs) index key mi ma j"
    hence "j \<in> offs_set_prev ns (x # xs) index key mi ma i"
      using B by simp
    thus False
      using D by simp
  qed
  ultimately show "offs_next ?ns' ub xs index key mi ma 0 = Suc (ns ! i)"
    by (simp only: offs_next_def split: if_split, rule_tac conjI, rule_tac [!] impI,
     simp_all)
next
  let ?ns' = "ns[i := Suc (ns ! i)]"
  assume "offs_num (length ns) xs index key mi ma i = 0"
  moreover have "offs_set_prev ?ns' xs index key mi ma i = {}"
    using D by (simp add: offs_num_cons split: if_split_asm, blast)
  ultimately have "offs_next ?ns' ub xs index key mi ma 0 =
    offs_next ?ns' ub xs index key mi ma i"
    using B by (rule_tac offs_next_zero, simp_all)
  moreover have "offs_next ?ns' ub xs index key mi ma i =
    offs_next ns ub (x # xs) index key mi ma i"
    using A and B and D by (rule_tac offs_next_cons_eq, simp_all add:
     offs_num_cons)
  ultimately show "offs_next ?ns' ub xs index key mi ma 0 =
    offs_next ns ub (x # xs) index key mi ma i"
    by simp
qed

lemma offs_pred_zero_cons_less:
  assumes
    A: "offs_pred ns ub (x # xs) index key mi ma" and
    B: "index key x (length ns) mi ma = i" and
    C: "i < length ns" and
    D: "0 < i" and
    E: "offs_set_prev ns (x # xs) index key mi ma i = {}"
  shows "offs_next ns ub (x # xs) index key mi ma 0 <
    offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma 0"
  (is "?M < ?N")
proof -
  have "i \<in> offs_set_next ns (x # xs) index key mi ma 0"
    using B and C and D by (simp add: offs_num_cons)
  moreover from this have
   "Min (offs_set_next ns (x # xs) index key mi ma 0) = i"
  proof (subst Min_eq_iff, simp, blast, simp, rule_tac allI, rule_tac impI,
   (erule_tac conjE)+, rule_tac ccontr, simp add: not_le)
    fix j
    assume "j < i" and "0 < offs_num (length ns) (x # xs) index key mi ma j"
    hence "j \<in> offs_set_prev ns (x # xs) index key mi ma i"
      using C by simp
    thus False
      using E by simp
  qed
  ultimately have F: "?M = ns ! i"
    by (simp only: offs_next_def split: if_split, blast)
  have "?N = (if 0 < offs_num (length ns) xs index key mi ma i
    then Suc (ns ! i)
    else offs_next ns ub (x # xs) index key mi ma i)"
    using B and C and D and E by (rule offs_next_zero_cons_neq)
  thus ?thesis
  proof (split if_split_asm)
    assume "?N = Suc (ns ! i)"
    thus ?thesis
      using F by simp
  next
    assume "?N = offs_next ns ub (x # xs) index key mi ma i"
    moreover have "ns ! i < offs_next ns ub (x # xs) index key mi ma i"
      using B by (rule_tac offs_pred_next [OF A C], simp add: offs_num_cons)
    ultimately show ?thesis
      using F by simp
  qed
qed

lemma offs_pred_zero_cons:
  assumes
    A: "offs_pred ns ub (x # xs) index key mi ma" and
    B: "index key x (length ns) mi ma = i" and
    C: "i < length ns" and
    D: "offs_num (length ns) (x # xs) index key mi ma 0 = 0"
  shows "offs_next ns ub (x # xs) index key mi ma 0 \<le>
    offs_next (ns[i := Suc (ns ! i)]) ub xs index key mi ma 0"
  (is "?M \<le> ?N")
proof (cases "offs_set_prev ns (x # xs) index key mi ma i = {}")
  case True
  have "0 < i"
    using B and D by (rule_tac ccontr, simp add: offs_num_cons)
  hence "?M < ?N"
    using True and B by (rule_tac offs_pred_zero_cons_less [OF A _ C])
  thus ?thesis by simp
next
  case False
  hence "?N = ?M"
    by (rule offs_next_zero_cons_eq [OF B D])
  thus ?thesis by simp
qed

lemma replicate_count:
 "count (mset (replicate n x)) x = n"
by (induction n, simp_all)

lemma fill_none [rule_format]:
  assumes A: "index_less index key"
  shows
   "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    ns \<noteq> [] \<longrightarrow>
    offs_pred ns ub xs index key mi ma \<longrightarrow>
    offs_none ns ub xs index key mi ma i \<longrightarrow>
      fill xs ns index key ub mi ma ! i = None"
proof (induction xs arbitrary: ns, simp add: offs_none_def offs_num_def offs_next_def,
 (rule impI)+, simp add: Let_def, (erule conjE)+)
  fix x xs and ns :: "nat list"
  let ?i' = "index key x (length ns) mi ma"
  let ?ns' = "ns[?i' := Suc (ns ! ?i')]"
  assume
    B: "offs_pred ns ub (x # xs) index key mi ma" and
    C: "offs_none ns ub (x # xs) index key mi ma i"
  assume
    D: "ns \<noteq> []" and "mi \<le> key x" and "key x \<le> ma"
  moreover from this have
    E: "?i' < length ns"
    using A by (simp add: index_less_def)
  hence "offs_pred ?ns' ub xs index key mi ma"
    by (rule_tac offs_pred_cons [OF B], simp)
  moreover assume "\<And>ns. ns \<noteq> [] \<longrightarrow> offs_pred ns ub xs index key mi ma \<longrightarrow>
    offs_none ns ub xs index key mi ma i \<longrightarrow>
    fill xs ns index key ub mi ma ! i = None"
  ultimately have
    F: "offs_none ?ns' ub xs index key mi ma i \<longrightarrow>
      fill xs ?ns' index key ub mi ma ! i = None"
    by simp
  show "(fill xs ?ns' index key ub mi ma)[ns ! ?i' := Some x] ! i = None"
  proof (insert C, simp add: offs_none_def, erule disjE, erule_tac [2] disjE, simp_all
   add: offs_num_cons split: if_split_asm, erule conjE, rule case_split, drule mp,
   assumption, simp_all, (erule conjE)+, (erule_tac [2] conjE)+,
   erule_tac [3] conjE, erule_tac [5] conjE)
    fix j
    assume
      G: "?i' = j" and
      H: "j < length ns" and
      I: "Suc (ns ! j + offs_num (length ns) xs index key mi ma j) \<le> i" and
      J: "i < offs_next ns ub (x # xs) index key mi ma j"
    show "fill xs (ns[j := Suc (ns ! j)]) index key ub mi ma ! i = None"
    proof (cases "0 < offs_num (length ns) xs index key mi ma j",
     case_tac [2] "offs_set_prev ns (x # xs) index key mi ma j \<noteq> {}",
     simp_all only: not_not not_gr0)
      have "j < length ns \<and> 0 < offs_num (length ns) xs index key mi ma j \<and>
        ?ns' ! j + offs_num (length ns) xs index key mi ma j \<le> i \<and>
        i < offs_next ?ns' ub xs index key mi ma j \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def, blast)
      moreover assume "0 < offs_num (length ns) xs index key mi ma j"
      moreover have "?ns' ! j + offs_num (length ns) xs index key mi ma j \<le> i"
        using G and H and I by simp
      moreover have "0 < offs_num (length ns) (x # xs) index key mi ma j"
        using G by (simp add: offs_num_cons)
      hence "offs_next ns ub (x # xs) index key mi ma j \<le>
        offs_next ?ns' ub xs index key mi ma j"
        using G and H by (rule_tac offs_pred_next_cons [OF B], simp_all)
      hence "i < offs_next ?ns' ub xs index key mi ma j"
        using J by simp
      ultimately have "fill xs ?ns' index key ub mi ma ! i = None"
        using H by blast
      thus ?thesis
        using G by simp
    next
      let ?j' = "Max (offs_set_prev ns (x # xs) index key mi ma j)"
      have "?j' < length ns \<and> 0 < offs_num (length ns) xs index key mi ma ?j' \<and>
        ?ns' ! ?j' + offs_num (length ns) xs index key mi ma ?j' \<le> i \<and>
        i < offs_next ?ns' ub xs index key mi ma ?j' \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def, blast)
      moreover assume K: "offs_set_prev ns (x # xs) index key mi ma j \<noteq> {}"
      hence "?j' \<in> offs_set_prev ns (x # xs) index key mi ma j"
        by (rule_tac Max_in, simp)
      hence L: "?j' < length ns \<and> ?j' < j \<and>
        0 < offs_num (length ns) xs index key mi ma ?j'"
        using G by (auto, subst (asm) (2) offs_num_cons, simp)
      moreover have "ns ! ?j' + offs_num (length ns) (x # xs)
        index key mi ma ?j' \<le> ns ! j"
        using G and H and L by (rule_tac offs_pred_asc [OF B], simp_all add:
         offs_num_cons)
      hence "?ns' ! ?j' + offs_num (length ns) xs index key mi ma ?j' \<le> ns ! j"
        using G and H and L by (subst nth_list_update, simp_all add: offs_num_cons)
      hence "?ns' ! ?j' + offs_num (length ns) xs index key mi ma ?j' \<le> i"
        using I by simp
      moreover assume M: "offs_num (length ns) xs index key mi ma j = 0"
      have "offs_next (ns[j := Suc (ns ! j)]) ub xs index key mi ma ?j' =
       (if 0 < offs_num (length ns) xs index key mi ma j
        then Suc (ns ! j)
        else offs_next ns ub (x # xs) index key mi ma j)"
        using G and K by (rule_tac offs_next_cons_neq, simp_all)
      hence "offs_next ?ns' ub xs index key mi ma ?j' =
        offs_next ns ub (x # xs) index key mi ma j"
        using G and M by simp
      hence "i < offs_next ?ns' ub xs index key mi ma ?j'"
        using J by simp
      ultimately have "fill xs ?ns' index key ub mi ma ! i = None" by blast
      thus ?thesis
        using G by simp
    next
      have "offs_num (length ns) xs index key mi ma 0 = 0 \<and>
        i < offs_next ?ns' ub xs index key mi ma 0 \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def)
      moreover assume
        K: "offs_set_prev ns (x # xs) index key mi ma j = {}" and
        L: "offs_num (length ns) xs index key mi ma j = 0"
      have "offs_set_prev ns (x # xs) index key mi ma j =
        offs_set_prev ?ns' xs index key mi ma j"
        using G by (rule_tac set_eqI, rule_tac iffI,
         simp_all add: offs_num_cons split: if_split_asm)
      hence M: "offs_set_prev ?ns' xs index key mi ma j = {}"
        using K by simp
      hence "offs_num (length ns) xs index key mi ma 0 = 0"
        using H and L by (cases j, simp_all)
      moreover have N: "offs_next ?ns' ub xs index key mi ma 0 =
        offs_next ?ns' ub xs index key mi ma j"
        using H and L and M by (rule_tac offs_next_zero, simp_all)
      have "offs_next ?ns' ub xs index key mi ma j =
        offs_next ns ub (x # xs) index key mi ma j"
        using G and H and K by (subst offs_next_cons_eq, simp_all add:
         offs_num_cons)
      hence "i < offs_next ?ns' ub xs index key mi ma 0"
        using J and N by simp
      ultimately have "fill xs ?ns' index key ub mi ma ! i = None" by blast
      thus ?thesis
        using G by simp
    qed
  next
    fix j
    assume
      G: "?i' \<noteq> j" and
      H: "j < length ns" and
      I: "ns ! j + offs_num (length ns) xs index key mi ma j \<le> i" and
      J: "i < offs_next ns ub (x # xs) index key mi ma j" and
      K: "0 < offs_num (length ns) xs index key mi ma j"
    from G have "ns ! ?i' \<noteq> i"
    proof (rule_tac notI, cases "?i' < j", simp_all add: not_less le_less)
      assume "?i' < j"
      hence "ns ! ?i' + offs_num (length ns) (x # xs) index key mi ma ?i' \<le> ns ! j"
        using H and K by (rule_tac offs_pred_asc [OF B], simp_all add:
         offs_num_cons)
      moreover assume "ns ! ?i' = i"
      ultimately have "i < ns ! j" by (simp add: offs_num_cons)
      thus False
        using I by simp
    next
      assume "j < ?i'"
      hence L: "?i' \<in> offs_set_next ns (x # xs) index key mi ma j"
        (is "_ \<in> ?A")
        using E by (simp add: offs_num_cons)
      hence "Min ?A \<le> ?i'"
        by (rule_tac Min_le, simp)
      hence "Min ?A < ?i' \<or> Min ?A = ?i'"
        by (simp add: le_less)
      hence "ns ! Min ?A \<le> ns ! ?i'"
      proof (rule disjE, simp_all)
        assume "Min ?A < ?i'"
        moreover have "Min ?A \<in> ?A"
          using L by (rule_tac Min_in, simp, blast)
        hence "0 < offs_num (length ns) (x # xs) index key mi ma (Min ?A)"
          by simp
        ultimately have "ns ! Min ?A + offs_num (length ns) (x # xs)
          index key mi ma (Min ?A) \<le> ns ! ?i'"
          using E by (rule_tac offs_pred_asc [OF B], simp_all add: offs_num_cons)
        thus ?thesis by simp
      qed
      hence "offs_next ns ub (x # xs) index key mi ma j \<le> ns ! ?i'"
        using L by (simp only: offs_next_def split: if_split, blast)
      moreover assume "ns ! ?i' = i"
      ultimately show False
        using J by simp
    qed
    thus "(fill xs ?ns' index key ub mi ma)[ns ! ?i' := Some x] ! i = None"
    proof simp
      have "j < length ns \<and> 0 < offs_num (length ns) xs index key mi ma j \<and>
        ?ns' ! j + offs_num (length ns) xs index key mi ma j \<le> i \<and>
        i < offs_next ?ns' ub xs index key mi ma j \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def, blast)
      moreover have "offs_next ns ub (x # xs) index key mi ma j \<le>
        offs_next ?ns' ub xs index key mi ma j"
        using E and K by (rule_tac offs_pred_next_cons [OF B], simp_all add:
         offs_num_cons)
      hence "i < offs_next ?ns' ub xs index key mi ma j"
        using J by simp
      ultimately show "fill xs ?ns' index key ub mi ma ! i = None"
        using G and H and I and K by simp
    qed
  next
    assume
      G: "0 < ?i'" and
      H: "offs_num (length ns) xs index key mi ma 0 = 0" and
      I: "i < offs_next ns ub (x # xs) index key mi ma 0"
    have "ns ! ?i' \<noteq> i"
    proof
      have "0 < offs_num (length ns) (x # xs) index key mi ma ?i'"
        by (simp add: offs_num_cons)
      hence L: "?i' \<in> offs_set_next ns (x # xs) index key mi ma 0"
        (is "_ \<in> ?A")
        using E and G by simp
      hence "Min ?A \<le> ?i'"
        by (rule_tac Min_le, simp)
      hence "Min ?A < ?i' \<or> Min ?A = ?i'"
        by (simp add: le_less)
      hence "ns ! Min ?A \<le> ns ! ?i'"
      proof (rule disjE, simp_all)
        assume "Min ?A < ?i'"
        moreover have "Min ?A \<in> ?A"
          using L by (rule_tac Min_in, simp, blast)
        hence "0 < offs_num (length ns) (x # xs) index key mi ma (Min ?A)"
          by simp
        ultimately have "ns ! Min ?A + offs_num (length ns) (x # xs)
          index key mi ma (Min ?A) \<le> ns ! ?i'"
          using E by (rule_tac offs_pred_asc [OF B], simp_all add: offs_num_cons)
        thus ?thesis by simp
      qed
      hence "offs_next ns ub (x # xs) index key mi ma 0 \<le> ns ! ?i'"
        using L by (simp only: offs_next_def split: if_split, blast)
      moreover assume "ns ! ?i' = i"
      ultimately show False
        using I by simp
    qed
    thus "(fill xs ?ns' index key ub mi ma)[ns ! ?i' := Some x] ! i = None"
    proof simp
      have "offs_num (length ns) xs index key mi ma 0 = 0 \<and>
        i < offs_next ?ns' ub xs index key mi ma 0 \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def)
      moreover have "offs_next ns ub (x # xs) index key mi ma 0 \<le>
        offs_next ?ns' ub xs index key mi ma 0"
        using E and G and H by (rule_tac offs_pred_zero_cons [OF B],
         simp_all add: offs_num_cons)
      hence "i < offs_next ?ns' ub xs index key mi ma 0"
        using I by simp
      ultimately show "fill xs ?ns' index key ub mi ma ! i = None"
        using H by simp
    qed
  next
    assume
      G: "?i' = 0" and
      H: "i < ns ! 0"
    show "fill xs (ns[0 := Suc (ns ! 0)]) index key ub mi ma ! i = None"
    proof (cases "0 < offs_num (length ns) xs index key mi ma 0", simp_all)
      have "0 < offs_num (length ns) xs index key mi ma 0 \<and> i < ?ns' ! 0 \<longrightarrow>
        fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def)
      moreover assume "0 < offs_num (length ns) xs index key mi ma 0"
      moreover have "i < ?ns' ! 0"
        using D and G and H by simp
      ultimately show ?thesis
        using G by simp
    next
      have "offs_num (length ns) xs index key mi ma 0 = 0 \<and>
        i < offs_next ?ns' ub xs index key mi ma 0 \<longrightarrow>
          fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def)
      moreover assume "offs_num (length ns) xs index key mi ma 0 = 0"
      moreover have I: "offs_next ?ns' ub xs index key mi ma 0 =
        offs_next ns ub (x # xs) index key mi ma 0"
        using D and G by (rule_tac offs_next_cons_eq, simp_all add:
         offs_num_cons)
      have "ns ! 0 < offs_next ns ub (x # xs) index key mi ma 0"
        using D and G by (rule_tac offs_pred_next [OF B], simp_all add:
         offs_num_cons)
      hence "i < offs_next ?ns' ub xs index key mi ma 0"
        using H and I by simp
      ultimately show ?thesis
        using G by simp
    qed
  next
    assume
      G: "0 < ?i'" and
      H: "0 < offs_num (length ns) xs index key mi ma 0" and
      I: "i < ns ! 0"
    have "ns ! ?i' \<noteq> i"
    proof -
      have "ns ! 0 + offs_num (length ns) (x # xs) index key mi ma 0 \<le> ns ! ?i'"
        using H by (rule_tac offs_pred_asc [OF B G E], simp_all add:
         offs_num_cons)
      moreover have "0 < offs_num (length ns) (x # xs) index key mi ma 0"
        using H by (simp add: offs_num_cons)
      ultimately show ?thesis
        using I by simp
    qed
    thus "(fill xs ?ns' index key ub mi ma)[ns ! ?i' := Some x] ! i = None"
    proof simp
      have "0 < offs_num (length ns) xs index key mi ma 0 \<and> i < ?ns' ! 0 \<longrightarrow>
        fill xs ?ns' index key ub mi ma ! i = None"
        using F by (simp add: offs_none_def)
      moreover have "i < ?ns' ! 0"
        using G and I by simp
      ultimately show "fill xs ?ns' index key ub mi ma ! i = None"
        using H by simp
    qed
  qed
qed

lemma fill_index_none [rule_format]:
  assumes
    A: "index_less index key" and
    B: "key x \<in> {mi..ma}" and
    C: "ns \<noteq> []" and
    D: "offs_pred ns ub (x # xs) index key mi ma"
  shows "\<forall>x \<in> set xs. key x \<in> {mi..ma} \<Longrightarrow>
    fill xs (ns[(index key x (length ns) mi ma) :=
      Suc (ns ! index key x (length ns) mi ma)]) index key ub mi ma !
        (ns ! index key x (length ns) mi ma) = None"
  (is "_ \<Longrightarrow> fill _ ?ns' _ _ _ _ _ ! (_ ! ?i) = _")
  using A and B and C and D
proof (rule_tac fill_none, simp_all, rule_tac offs_pred_cons,
 simp_all, simp add: index_less_def, cases "0 < ?i",
 cases "offs_set_prev ns (x # xs) index key mi ma ?i = {}",
 case_tac [3] "0 < offs_num (length ns) xs index key mi ma 0")
  assume
    E: "0 < ?i" and
    F: "offs_set_prev ns (x # xs) index key mi ma ?i = {}"
  have G: "?i < length ns"
    using A and B and C by (simp add: index_less_def)
  hence "offs_num (length ns) (x # xs) index key mi ma 0 = 0"
    using E and F by (rule_tac ccontr, simp)
  hence "offs_num (length ns) xs index key mi ma 0 = 0"
    by (simp add: offs_num_cons split: if_split_asm)
  moreover have "offs_next ?ns' ub xs index key mi ma 0 =
   (if 0 < offs_num (length ns) xs index key mi ma ?i
    then Suc (ns ! ?i)
    else offs_next ns ub (x # xs) index key mi ma ?i)"
    using E and F and G by (rule_tac offs_next_zero_cons_neq, simp_all)
  hence "ns ! ?i < offs_next ?ns' ub xs index key mi ma 0"
    by (simp split: if_split_asm, rule_tac offs_pred_next [OF D G], simp add:
     offs_num_cons)
  ultimately show "offs_none ?ns' ub xs index key mi ma (ns ! ?i)"
    by (simp add: offs_none_def)
next
  assume
    E: "0 < ?i" and
    F: "offs_set_prev ns (x # xs) index key mi ma ?i \<noteq> {}"
      (is "?A \<noteq> _")
  have G: "?i < length ns"
    using A and B and C by (simp add: index_less_def)
  have H: "Max ?A \<in> ?A"
    using F by (rule_tac Max_in, simp)
  hence I: "Max ?A < ?i" by blast
  have "Max ?A < length ns"
    using H by auto
  moreover have "0 < offs_num (length ns) (x # xs) index key mi ma (Max ?A)"
    using H by auto
  hence "0 < offs_num (length ns) xs index key mi ma (Max ?A)"
    using I by (subst (asm) offs_num_cons, split if_split_asm, simp_all)
  moreover have "ns ! Max ?A + offs_num (length ns) (x # xs)
    index key mi ma (Max ?A) \<le> ns ! ?i"
    using G and H by (rule_tac offs_pred_asc [OF D], simp_all add: offs_num_cons)
  hence "?ns' ! Max ?A + offs_num (length ns) xs
    index key mi ma (Max ?A) \<le> ns ! ?i"
    using I by (simp add: offs_num_cons)
  moreover have "offs_next ?ns' ub xs index key mi ma (Max ?A) =
   (if 0 < offs_num (length ns) xs index key mi ma ?i
    then Suc (ns ! ?i)
    else offs_next ns ub (x # xs) index key mi ma ?i)"
    using F and I by (rule_tac offs_next_cons_neq, simp_all)
  hence "ns ! ?i < offs_next ?ns' ub xs index key mi ma (Max ?A)"
    by (simp split: if_split_asm, rule_tac offs_pred_next [OF D G], simp add:
     offs_num_cons)
  ultimately show "offs_none ?ns' ub xs index key mi ma (ns ! ?i)"
    by (simp add: offs_none_def, blast)
next
  assume "0 < offs_num (length ns) xs index key mi ma 0" and "\<not> 0 < ?i"
  moreover have "?i < length ns"
    using A and B and C by (simp add: index_less_def)
  ultimately show "offs_none ?ns' ub xs index key mi ma (ns ! ?i)"
    by (simp add: offs_none_def)
next
  assume
    E: "\<not> 0 < ?i" and
    F: "\<not> 0 < offs_num (length ns) xs index key mi ma 0"
  have G: "?i < length ns"
    using A and B and C by (simp add: index_less_def)
  have "offs_num (length ns) xs index key mi ma 0 = 0"
    using F by simp
  moreover have "offs_next ?ns' ub xs index key mi ma ?i =
    offs_next ns ub (x # xs) index key mi ma ?i"
    using E and G by (rule_tac offs_next_cons_eq, simp_all add: offs_num_cons)
  hence "ns ! ?i < offs_next ?ns' ub xs index key mi ma ?i"
    by (simp, rule_tac offs_pred_next [OF D G], simp add: offs_num_cons)
  hence "ns ! ?i < offs_next ?ns' ub xs index key mi ma 0"
    using E by simp
  ultimately show "offs_none ?ns' ub xs index key mi ma (ns ! ?i)"
    by (simp add: offs_none_def)
qed

lemma fill_count_item [rule_format]:
  assumes A: "index_less index key"
  shows
   "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    ns \<noteq> [] \<longrightarrow>
    offs_pred ns ub xs index key mi ma \<longrightarrow>
    length xs \<le> ub \<longrightarrow>
      count (mset (map the (fill xs ns index key ub mi ma))) x =
      count (mset xs) x + (if the None = x then ub - length xs else 0)"
proof (induction xs arbitrary: ns, simp add: replicate_count, (rule impI)+,
 simp add: Let_def map_update del: count_add_mset mset_map split del: if_split,
 (erule conjE)+, subst add_mset_add_single, simp only: count_single count_union)
  fix y xs and ns :: "nat list"
  let ?i = "index key y (length ns) mi ma"
  let ?ns' = "ns[?i := Suc (ns ! ?i)]"
  assume
    B: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    C: "mi \<le> key y" and
    D: "key y \<le> ma" and
    E: "ns \<noteq> []" and
    F: "offs_pred ns ub (y # xs) index key mi ma" and
    G: "Suc (length xs) \<le> ub"
  have H: "?i < length ns"
    using A and C and D and E by (simp add: index_less_def)
  assume "\<And>ns. ns \<noteq> [] \<longrightarrow> offs_pred ns ub xs index key mi ma \<longrightarrow>
    count (mset (map the (fill xs ns index key ub mi ma))) x =
    count (mset xs) x + (if the None = x then ub - length xs else 0)"
  moreover have "offs_pred ?ns' ub xs index key mi ma"
    using F and H by (rule_tac offs_pred_cons, simp_all)
  ultimately have "count (mset (map the (fill xs ?ns' index key ub mi ma))) x =
    count (mset xs) x + (if the None = x then ub - length xs else 0)"
    using E by simp
  moreover have "ns ! ?i + offs_num (length ns) (y # xs)
    index key mi ma ?i \<le> ub"
    using F and H by (rule offs_pred_ub, simp add: offs_num_cons)
  hence "ns ! ?i < ub"
    by (simp add: offs_num_cons)
  ultimately show "count (mset ((map the (fill xs ?ns' index key ub mi ma))
    [ns ! ?i := y])) x = count (mset xs) x + (if y = x then 1 else 0) +
    (if the None = x then ub - length (y # xs) else 0)"
  proof (subst mset_update, simp add: fill_length, subst add_mset_add_single, simp
   only: count_diff count_single count_union, subst nth_map, simp add: fill_length,
   subst add.assoc, subst (3) add.commute, subst add.assoc [symmetric],
   subst add_right_cancel)
    have "fill xs ?ns' index key ub mi ma ! (ns ! ?i) = None"
      using B and C and D and E by (rule_tac fill_index_none [OF A _ _ F],
       simp_all)
    thus "count (mset xs) x + (if the None = x then ub - length xs else 0) -
      (if the (fill xs ?ns' index key ub mi ma ! (ns ! ?i)) = x then 1 else 0) =
      count (mset xs) x + (if the None = x then ub - length (y # xs) else 0)"
      using G by simp
  qed
qed

text \<open>
\null

Finally, lemma @{text offs_enum_pred} here below proves that, if $ns$ is the offsets' list obtained
by applying the composition of functions @{const offs} and @{const enum} to objects' list $xs$, then
predicate @{const offs_pred} is satisfied by $ns$ and $xs$.

This result is in turn used, together with lemma @{thm [source] fill_count_item}, to prove lemma
@{text fill_offs_enum_count_item}, which states that function @{const fill} conserves objects if its
input offsets' list is computed via the composition of functions @{const offs} and @{const enum}.

\null
\<close>

lemma enum_offs_num:
 "i < n \<Longrightarrow> enum xs index key n mi ma ! i = offs_num n xs index key mi ma i"
by (induction xs, simp add: offs_num_def, simp add: Let_def offs_num_cons,
 subst nth_list_update_eq, simp_all add: enum_length)

lemma offs_length:
 "length (offs ns i) = length ns"
by (induction ns arbitrary: i, simp_all)

lemma offs_add [rule_format]:
 "i < length ns \<longrightarrow> offs ns k ! i = foldl (+) k (take i ns)"
by (induction ns arbitrary: i k, simp, simp add: nth_Cons split: nat.split)

lemma offs_mono_aux:
 "i \<le> j \<Longrightarrow> j < length ns \<Longrightarrow> offs ns k ! i \<le> offs ns k ! (i + (j - i))"
by (simp only: offs_add take_add, simp add: add_le)

lemma offs_mono:
 "i \<le> j \<Longrightarrow> j < length ns \<Longrightarrow> offs ns k ! i \<le> offs ns k ! j"
by (frule offs_mono_aux, simp_all)

lemma offs_update:
 "j < length ns \<Longrightarrow>
    offs (ns[i := Suc (ns ! i)]) k ! j = (if j \<le> i then id else Suc) (offs ns k ! j)"
by (simp add: offs_add not_le take_update_swap, rule impI, subst nth_take [symmetric],
 assumption, subst add_update, simp_all)

lemma offs_equal_suc:
  assumes
    A: "Suc i < length ns" and
    B: "ns ! i = 0"
  shows "offs ns m ! i = offs ns m ! Suc i"
proof -
  have "offs ns m ! i = foldl (+) m (take i ns)"
    using A by (subst offs_add, simp_all)
  also have "\<dots> = foldl (+) m (take i ns @ [ns ! i])"
    using B by simp
  also have "\<dots> = foldl (+) m (take (Suc i) ns)"
    using A by (subst take_Suc_conv_app_nth, simp_all)
  also have "\<dots> = offs ns m ! Suc i"
    using A by (subst offs_add, simp_all)
  finally show ?thesis .
qed

lemma offs_equal [rule_format]:
 "i < j \<Longrightarrow> j < length ns \<Longrightarrow>
    (\<forall>k \<in> {i..<j}. ns ! k = 0) \<longrightarrow> offs ns m ! i = offs ns m ! j"
proof (erule strict_inc_induct, rule_tac [!] impI, simp_all, erule offs_equal_suc, simp)
  fix i
  assume A: "i < j" and "j < length ns"
  hence "Suc i < length ns" by simp
  moreover assume "\<forall>k \<in> {i..<j}. ns ! k = 0"
  hence "ns ! i = 0"
    using A by simp
  ultimately have "offs ns m ! i = offs ns m ! Suc i"
    by (rule offs_equal_suc)
  also assume "\<dots> = offs ns m ! j"
  finally show "offs ns m ! i = offs ns m ! j" .
qed

lemma offs_enum_last [rule_format]:
  assumes
    A: "index_less index key" and
    B: "0 < n" and
    C: "\<forall>x \<in> set xs. key x \<in> {mi..ma}"
  shows "offs (enum xs index key n mi ma) k ! (n - Suc 0) +
    offs_num n xs index key mi ma (n - Suc 0) = length xs + k"
proof -
  let ?ns = "enum xs index key n mi ma"
  from B have D: "last ?ns = offs_num n xs index key mi ma (n - Suc 0)"
    by (subst last_conv_nth, subst length_0_conv [symmetric], simp_all add:
     enum_length, subst enum_offs_num, simp_all)
  have "offs ?ns k ! (n - Suc 0) = foldl (+) k (take (n - Suc 0) ?ns)"
    using B by (rule_tac offs_add, simp add: enum_length)
  also have "\<dots> = foldl (+) k (butlast ?ns)"
    by (simp add: butlast_conv_take enum_length)
  finally have "offs ?ns k ! (n - Suc 0) + offs_num n xs index key mi ma
    (n - Suc 0) = foldl (+) k (butlast ?ns @ [last ?ns])"
    using D by simp
  also have "\<dots> = foldl (+) k ?ns"
    using B by (subst append_butlast_last_id, subst length_0_conv [symmetric],
     simp_all add: enum_length)
  also have "\<dots> = foldl (+) 0 ?ns + k"
    by (rule add_base_zero)
  also have "\<dots> = length xs + k"
    using A and B and C by (subst enum_add, simp_all)
  finally show ?thesis .
qed

lemma offs_enum_ub [rule_format]:
  assumes
    A: "index_less index key" and
    B: "i < n" and
    C: "\<forall>x \<in> set xs. key x \<in> {mi..ma}"
  shows "offs (enum xs index key n mi ma) k ! i \<le> length xs + k"
proof -
  let ?ns = "enum xs index key n mi ma"
  have "offs ?ns k ! i \<le> offs ?ns k ! (n - Suc 0)"
    using B by (rule_tac offs_mono, simp_all add: enum_length)
  also have "\<dots> \<le> offs ?ns k ! (n - Suc 0) +
    offs_num n xs index key mi ma (n - Suc 0)"
    by simp
  also have "\<dots> = length xs + k"
    using A and B and C by (rule_tac offs_enum_last, simp_all)
  finally show ?thesis .
qed

lemma offs_enum_next_ge [rule_format]:
  assumes
    A: "index_less index key" and
    B: "i < n"
  shows "\<forall>x \<in> set xs. key x \<in> {mi..ma} \<Longrightarrow>
    offs (enum xs index key n mi ma) k ! i \<le>
      offs_next (offs (enum xs index key n mi ma) k) (length xs + k)
        xs index key mi ma i"
  (is "_ \<Longrightarrow> offs ?ns _ ! _ \<le> _")
proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI,
 rule offs_enum_ub [OF A B], simp)
  assume "offs_set_next (offs ?ns k) xs index key mi ma i \<noteq> {}"
    (is "?A \<noteq> _")
  hence C: "Min ?A \<in> ?A"
    by (rule_tac Min_in, simp)
  hence "i \<le> Min ?A" by simp
  moreover have "Min ?A < length ?ns"
    using C by (simp add: offs_length)
  ultimately show "offs ?ns k ! i \<le> offs ?ns k ! Min ?A"
    by (rule offs_mono)
qed

lemma offs_enum_zero_aux [rule_format]:
 "\<lbrakk>index_less index key; 0 < n; \<forall>x \<in> set xs. key x \<in> {mi..ma};
   offs_num n xs index key mi ma (n - Suc 0) = 0\<rbrakk> \<Longrightarrow>
     offs (enum xs index key n mi ma) k ! (n - Suc 0) = length xs + k"
by (subst offs_enum_last [where key = key and mi = mi and ma = ma,
 symmetric], simp+)

lemma offs_enum_zero [rule_format]:
  assumes
    A: "index_less index key" and
    B: "i < n" and
    C: "\<forall>x \<in> set xs. key x \<in> {mi..ma}" and
    D: "offs_num n xs index key mi ma i = 0"
  shows "offs (enum xs index key n mi ma) k ! i =
    offs_next (offs (enum xs index key n mi ma) k) (length xs + k)
      xs index key mi ma i"
proof (simp only: offs_next_def split: if_split, rule conjI, rule_tac [!] impI,
 cases "i = n - Suc 0", simp)
  assume "i = n - Suc 0"
  thus "offs (enum xs index key n mi ma) k ! (n - Suc 0) = length xs + k"
    using A and B and C and D by (rule_tac offs_enum_zero_aux, simp_all)
next
  let ?ns = "enum xs index key n mi ma"
  assume E: "offs_set_next (offs ?ns k) xs index key mi ma i = {}"
    (is "?A = _")
  assume "i \<noteq> n - Suc 0"
  hence F: "i < n - Suc 0"
    using B by simp
  hence "offs ?ns k ! i = offs ?ns k ! (n - Suc 0)"
  proof (rule offs_equal, simp_all add: enum_length le_less,
   erule_tac conjE, erule_tac disjE, rule_tac ccontr, drule_tac [2] sym, simp_all)
    fix j
    assume G: "j < n - Suc 0"
    hence "j < length (offs ?ns k)"
      by (simp add: offs_length enum_length)
    moreover assume "i < j"
    moreover assume "0 < ?ns ! j"
    hence "0 < offs_num (length (offs ?ns k)) xs index key mi ma j"
      using G by (subst (asm) enum_offs_num, simp_all add:
       offs_length enum_length)
    ultimately have "j \<in> ?A" by simp
    thus False
      using E by simp
  next
    show "?ns ! i = 0"
      using B and D by (subst enum_offs_num, simp_all)
  qed
  also from A and B and C have "\<dots> = length xs + k"
  proof (rule_tac offs_enum_zero_aux, simp_all, rule_tac ccontr, simp)
    have "n - Suc 0 < length (offs ?ns k)"
      using B by (simp add: offs_length enum_length)
    moreover assume "0 < offs_num n xs index key mi ma (n - Suc 0)"
    hence "0 < offs_num (length (offs ?ns k)) xs index key mi ma (n - Suc 0)"
      by (simp add: offs_length enum_length)
    ultimately have "n - Suc 0 \<in> ?A"
      using F by simp
    thus False
      using E by simp
  qed
  finally show "offs (enum xs index key n mi ma) k ! i = length xs + k" .
next
  let ?ns = "enum xs index key n mi ma"
  assume "offs_set_next (offs ?ns k) xs index key mi ma i \<noteq> {}"
    (is "?A \<noteq> _")
  hence "Min ?A \<in> ?A"
    by (rule_tac Min_in, simp)
  thus "offs ?ns k ! i = offs ?ns k ! Min ?A"
  proof (rule_tac offs_equal, simp_all add: le_less, simp add: offs_length,
   (erule_tac conjE)+, erule_tac disjE, rule_tac ccontr, drule_tac [2] sym, simp_all)
    fix j
    assume E: "j < Min ?A" and "Min ?A < length (offs ?ns k)"
    hence F: "j < length (offs ?ns k)" by simp
    moreover assume "i < j"
    moreover assume "0 < ?ns ! j"
    hence "0 < offs_num (length (offs ?ns k)) xs index key mi ma j"
      using F by (subst (asm) enum_offs_num, simp_all add:
       offs_length enum_length)
    ultimately have "j \<in> ?A" by simp
    hence "Min ?A \<le> j"
      by (rule_tac Min_le, simp)
    thus False
      using E by simp
  next
    show "?ns ! i = 0"
      using B and D by (subst enum_offs_num, simp_all)
  qed
qed

lemma offs_enum_next_cons [rule_format]:
  assumes
    A: "index_less index key" and
    B: "\<forall>x \<in> set xs. key x \<in> {mi..ma}"
  shows "(if i < index key x n mi ma then (\<le>) else (<))
    (offs_next (offs (enum xs index key n mi ma) k)
      (length xs + k) xs index key mi ma i)
    (offs_next (offs ((enum xs index key n mi ma) [index key x n mi ma :=
      Suc (enum xs index key n mi ma ! index key x n mi ma)]) k)
      (Suc (length xs + k)) (x # xs) index key mi ma i)"
  (is "(if i < ?i' then _ else _)
    (offs_next (offs ?ns _) _ _ _ _ _ _ _)
    (offs_next (offs ?ns' _) _ _ _ _ _ _ _)")
proof (simp_all only: offs_next_def not_less split: if_split, (rule conjI, rule impI)+,
 simp, simp, (rule_tac [!] impI, (rule_tac [!] conjI)?)+, rule_tac [2-3] FalseE,
 rule_tac [4] conjI, rule_tac [4-5] impI)
  assume
    C: "offs_set_next (offs ?ns k) xs index key mi ma i = {}"
      (is "?A = _") and
    D: "offs_set_next (offs ?ns' k) (x # xs) index key mi ma i \<noteq> {}"
      (is "?A' \<noteq> _") and
    E: "i < ?i'"
  from C have F: "\<forall>j \<noteq> ?i'. j \<notin> ?A'"
    by (rule_tac allI, rule_tac impI, rule_tac notI, simp add: enum_length
     offs_length offs_num_cons split: if_split_asm, (erule_tac conjE)+, simp)
  from D have "Min ?A' \<in> ?A'"
    by (rule_tac Min_in, simp)
  hence G: "Min ?A' < n"
    by (simp add: offs_length enum_length)
  have H: "Min ?A' = ?i'"
  proof (rule Min_eqI, simp, rule eq_refl, erule contrapos_pp, insert F, simp)
    have "\<exists>j. j \<in> ?A'"
      using D by blast
    then obtain j where "j \<in> ?A'" ..
    moreover from this have "j = ?i'"
      by (erule_tac contrapos_pp, insert F, simp)
    ultimately show "?i' \<in> ?A'" by simp
  qed
  with G have "offs ?ns' k ! Min ?A' = offs ?ns k ! Min ?A'"
    by (subst offs_update, simp_all add: enum_length)
  also from A and B and G and H have
   "\<dots> = offs_next (offs ?ns k) (length xs + k) xs index key mi ma (Min ?A')"
  proof (rule_tac offs_enum_zero, simp_all, rule_tac ccontr, simp)
    assume "?i' < n" and "0 < offs_num n xs index key mi ma ?i'"
    hence "?i' \<in> ?A"
      using E by (simp add: offs_length enum_length)
    thus False
      using C by simp
  qed
  also have "\<dots> = length xs + k"
  proof (simp only: offs_next_def split: if_split, rule conjI, simp, rule impI,
   rule FalseE, simp, erule exE, (erule conjE)+)
    fix j
    assume "j < length (offs ?ns k)"
    moreover assume "Min ?A' < j"
    hence "i < j"
      using E and H by simp
    moreover assume "0 < offs_num (length (offs ?ns k)) xs index key mi ma j"
    ultimately have "j \<in> ?A" by simp
    thus False
      using C by simp
  qed
  finally show "length xs + k \<le> offs ?ns' k ! Min ?A'" by simp
next
  assume
    C: "offs_set_next (offs ?ns k) xs index key mi ma i = {}"
      (is "?A = _") and
    D: "offs_set_next (offs ?ns' k) (x # xs) index key mi ma i \<noteq> {}"
      (is "?A' \<noteq> _") and
    E: "?i' \<le> i"
  have "\<exists>j. j \<in> ?A'"
    using D by blast
  then obtain j where F: "j \<in> ?A'" ..
  hence "j < length (offs ?ns k)"
    by (simp add: offs_length)
  moreover have "i < j"
    using F by simp
  moreover from this have
   "0 < offs_num (length (offs ?ns k)) xs index key mi ma j"
    using E and F by (simp add: offs_length enum_length offs_num_cons)
  ultimately have "j \<in> ?A" by simp
  thus False
    using C by simp
next
  assume
    C: "offs_set_next (offs ?ns k) xs index key mi ma i \<noteq> {}"
      (is "?A \<noteq> _") and
    D: "offs_set_next (offs ?ns' k) (x # xs) index key mi ma i = {}"
      (is "?A' = _")
  have "\<exists>j. j \<in> ?A"
    using C by blast
  then obtain j where E: "j \<in> ?A" ..
  hence "j < length (offs ?ns' k)"
    by (simp add: offs_length)
  moreover have "i < j"
    using E by simp
  moreover have "0 < offs_num (length (offs ?ns' k)) (x # xs) index key mi ma j"
    using E by (simp add: offs_length enum_length offs_num_cons)
  ultimately have "j \<in> ?A'" by simp
  thus False
    using D by simp
next
  assume "offs_set_next (offs ?ns k) xs index key mi ma i \<noteq> {}"
    (is "?A \<noteq> _")
  hence "Min ?A \<in> ?A"
    by (rule_tac Min_in, simp)
  hence C: "Min ?A < n"
    by (simp add: offs_length enum_length)
  assume "offs_set_next (offs ?ns' k) (x # xs) index key mi ma i \<noteq> {}"
    (is "?A' \<noteq> _")
  hence D: "Min ?A' \<in> ?A'"
    by (rule_tac Min_in, simp)
  hence E: "Min ?A' < n"
    by (simp add: offs_length enum_length)
  have "offs ?ns k ! Min ?A \<le> offs ?ns k ! Min ?A'"
  proof (cases "offs_num n xs index key mi ma (Min ?A') = 0")
    case True
    have "offs ?ns k ! Min ?A' =
      offs_next (offs ?ns k) (length xs + k) xs index key mi ma (Min ?A')"
      using A and B and E and True by (rule_tac offs_enum_zero, simp_all)
    also from A and B and C have "\<dots> \<ge> offs ?ns k ! Min ?A"
    proof (simp only: offs_next_def split: if_split, rule_tac conjI, rule_tac [!] impI,
     rule_tac offs_enum_ub, simp, simp, simp)
      assume "offs_set_next (offs ?ns k) xs index key mi ma (Min ?A') \<noteq> {}"
        (is "?B \<noteq> _")
      hence "Min ?B \<in> ?B"
        by (rule_tac Min_in, simp)
      hence "Min ?B \<in> ?A"
        using D by simp
      moreover from this have "Min ?A \<le> Min ?B"
        by (rule_tac Min_le, simp)
      ultimately show "offs ?ns k ! Min ?A \<le> offs ?ns k ! Min ?B"
        by (rule_tac offs_mono, simp_all add: offs_length)
    qed
    finally show ?thesis .
  next
    case False
    hence "Min ?A' \<in> ?A"
      using D by (simp add: offs_length enum_length)
    hence "Min ?A \<le> Min ?A'"
      by (rule_tac Min_le, simp)
    thus ?thesis
      by (rule offs_mono, simp_all add: enum_length E)
  qed
  also have "\<dots> \<le> offs ?ns' k ! Min ?A'"
    using E by (subst offs_update, simp_all add: enum_length)
  finally show "offs ?ns k ! Min ?A \<le> offs ?ns' k ! Min ?A'" .
next
  let ?A = "offs_set_next (offs ?ns k) xs index key mi ma i"
  assume "offs_set_next (offs ?ns' k) (x # xs) index key mi ma i \<noteq> {}"
    (is "?A' \<noteq> _")
  hence C: "Min ?A' \<in> ?A'"
    by (rule_tac Min_in, simp)
  hence D: "Min ?A' < n"
    by (simp add: offs_length enum_length)
  assume "?i' \<le> i"
  hence E: "?i' < Min ?A'"
    using C by simp
  hence "0 < offs_num n xs index key mi ma (Min ?A')"
    using C by (simp add: offs_length enum_length offs_num_cons)
  hence "Min ?A' \<in> ?A"
    using C by (simp add: offs_length enum_length)
  hence "Min ?A \<le> Min ?A'"
    by (rule_tac Min_le, simp)
  hence "offs ?ns k ! Min ?A \<le> offs ?ns k ! Min ?A'"
    by (rule offs_mono, simp_all add: enum_length D)
  also have "\<dots> < offs ?ns' k ! Min ?A'"
    using E by (subst offs_update, simp_all add: enum_length D)
  finally show "offs ?ns k ! Min ?A < offs ?ns' k ! Min ?A'" .
qed

lemma offs_enum_pred [rule_format]:
  assumes A: "index_less index key"
  shows "(\<forall>x \<in> set xs. key x \<in> {mi..ma}) \<longrightarrow>
    offs_pred (offs (enum xs index key n mi ma) k) (length xs + k)
      xs index key mi ma"
proof (induction xs, simp add: offs_pred_def offs_num_def,
 simp add: Let_def offs_pred_def offs_length enum_length, rule impI, (erule conjE)+,
 simp, rule allI, rule impI, erule allE, drule mp, assumption)
  fix x xs i
  let ?i' = "index key x n mi ma"
  let ?ns = "enum xs index key n mi ma"
  let ?ns' = "?ns[?i' := Suc (?ns ! ?i')]"
  assume
    B: "\<forall>x \<in> set xs. mi \<le> key x \<and> key x \<le> ma" and
    C: "i < n" and
    D: "offs_num n xs index key mi ma i \<le>
      offs_next (offs ?ns k) (length xs + k) xs index key mi ma i - offs ?ns k ! i"
  have E: "(if i < ?i' then (\<le>) else (<))
    (offs_next (offs ?ns k) (length xs + k) xs index key mi ma i)
    (offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i)"
    using A and B by (subst offs_enum_next_cons, simp_all)
  show "offs_num n (x # xs) index key mi ma i \<le>
    offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i -
      offs ?ns' k ! i"
  proof (subst offs_update, simp add: enum_length C, rule linorder_cases [of i ?i'],
   simp_all add: offs_num_cons)
    assume "i < ?i'"
    hence "offs_next (offs ?ns k) (length xs + k) xs index key mi ma i \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i"
      using E by simp
    thus "offs_num n xs index key mi ma i \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i -
        offs ?ns k ! i"
      using D by arith
  next
    assume F: "i = ?i'"
    hence "Suc (offs_num n xs index key mi ma ?i') \<le>
      Suc (offs_next (offs ?ns k) (length xs + k) xs index key mi ma ?i' -
        offs ?ns k ! ?i')"
      using D by simp
    also from A and B and C and F have "\<dots> =
      Suc (offs_next (offs ?ns k) (length xs + k) xs index key mi ma ?i') -
        offs ?ns k ! ?i'"
      by (rule_tac Suc_diff_le [symmetric], rule_tac offs_enum_next_ge, simp_all)
    finally have "Suc (offs_num n xs index key mi ma ?i') \<le>
      Suc (offs_next (offs ?ns k) (length xs + k) xs index key mi ma ?i') -
        offs ?ns k ! ?i'" .
    moreover have
     "Suc (offs_next (offs ?ns k) (length xs + k) xs index key mi ma ?i') \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma ?i'"
      using E and F by simp
    ultimately show "Suc (offs_num n xs index key mi ma ?i') \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma ?i' -
        offs ?ns k ! ?i'"
      by arith
  next
    assume "?i' < i"
    hence "Suc (offs_next (offs ?ns k) (length xs + k) xs index key mi ma i) \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i"
      using E by simp
    thus "offs_num n xs index key mi ma i \<le>
      offs_next (offs ?ns' k) (Suc (length xs + k)) (x # xs) index key mi ma i -
        Suc (offs ?ns k ! i)"
      using D by arith
  qed
qed

lemma fill_offs_enum_count_item [rule_format]:
 "\<lbrakk>index_less index key; \<forall>x \<in> set xs. key x \<in> {mi..ma}; 0 < n\<rbrakk> \<Longrightarrow>
    count (mset (map the (fill xs (offs (enum xs index key n mi ma) 0)
      index key (length xs) mi ma))) x =
    count (mset xs) x"
by (subst fill_count_item, simp_all, simp only: length_greater_0_conv [symmetric]
 offs_length enum_length, insert offs_enum_pred [of index key xs mi ma n 0], simp)

text \<open>
\null

Using lemma @{thm [source] fill_offs_enum_count_item}, step 9 of the proof method can now be dealt
with. It is accomplished by proving lemma @{text gcsort_count_inv}, which states that the number of
the occurrences of whatever object in the objects' list is still the same after any recursive round.

\null
\<close>

lemma nths_count:
 "count (mset (nths xs A)) x =
    count (mset xs) x - card {i. i < length xs \<and> i \<notin> A \<and> xs ! i = x}"
proof (induction xs arbitrary: A, simp_all add: nths_Cons)
  fix v xs A
  let ?B = "{i. i < length xs \<and> Suc i \<notin> A \<and> xs ! i = x}"
  let ?C = "\<lambda>v. {i. i < Suc (length xs) \<and> i \<notin> A \<and> (v # xs) ! i = x}"
  have A: "\<And>v. ?C v = ?C v \<inter> {0} \<union> ?C v \<inter> {i. \<exists>j. i = Suc j}"
    by (subst Int_Un_distrib [symmetric], auto, arith)
  have "\<And>v. card (?C v) = card (?C v \<inter> {0}) + card (?C v \<inter> {i. \<exists>j. i = Suc j})"
    by (subst A, rule card_Un_disjoint, simp_all, blast)
  moreover have "\<And>v. card ?B = card (?C v \<inter> {i. \<exists>j. i = Suc j})"
    by (rule bij_betw_same_card [of Suc], auto)
  ultimately show
   "(0 \<in> A \<longrightarrow>
      (v = x \<longrightarrow> Suc (count (mset xs) x - card ?B) =
        Suc (count (mset xs) x) - card (?C x)) \<and>
      (v \<noteq> x \<longrightarrow> count (mset xs) x - card ?B =
        count (mset xs) x - card (?C v))) \<and>
    (0 \<notin> A \<longrightarrow>
      (v = x \<longrightarrow> count (mset xs) x - card ?B =
        Suc (count (mset xs) x) - card (?C x)) \<and>
      (v \<noteq> x \<longrightarrow> count (mset xs) x - card ?B =
        count (mset xs) x - card (?C v)))"
  proof ((rule_tac [!] conjI, rule_tac [!] impI)+, simp_all)
    have "card ?B \<le> count (mset xs) x"
      by (simp add: count_mset length_filter_conv_card, rule card_mono,
       simp, blast)
    thus "Suc (count (mset xs) x - card ?B) = Suc (count (mset xs) x) - card ?B"
      by (rule Suc_diff_le [symmetric])
  qed
qed

lemma round_count_inv [rule_format]:
 "index_less index key \<longrightarrow> bn_inv p q t \<longrightarrow> add_inv n t \<longrightarrow> count_inv f t \<longrightarrow>
    count_inv f (round index key p q r t)"
proof (induction index key p q r t arbitrary: n f rule: round.induct,
 (rule_tac [!] impI)+, simp, simp, simp_all only: simp_thms)
  fix index p q r u ns xs n f and key :: "'a \<Rightarrow> 'b"
  let ?t = "round index key p q r (u, ns, tl xs)"
  assume
   "\<And>n f. bn_inv p q (u, ns, tl xs) \<longrightarrow> add_inv n (u, ns, tl xs) \<longrightarrow>
      count_inv f (u, ns, tl xs) \<longrightarrow> count_inv f ?t" and
   "bn_inv p q (u, Suc 0 # ns, xs)" and
   "add_inv n (u, Suc 0 # ns, xs)" and
   "count_inv f (u, Suc 0 # ns, xs)"
  thus "count_inv f (round index key p q r (u, Suc 0 # ns, xs))"
  proof (cases ?t, simp add: add_suc, rule_tac allI, cases xs,
   simp_all add: disj_imp split: if_split_asm)
    fix y ys x and xs' :: "'a list"
    assume "\<And>n f. foldl (+) 0 ns = n \<and> length ys = n \<longrightarrow>
      (\<forall>x. count (mset ys) x = f x) \<longrightarrow> (\<forall>x. count (mset xs') x = f x)"
    moreover assume "Suc (foldl (+) 0 ns) = n" and "Suc (length ys) = n"
    ultimately have "\<And>n f. (\<forall>x. count (mset ys) x = f x) \<longrightarrow>
      (\<forall>x. count (mset xs') x = f x)"
      by blast
    moreover assume A: "\<forall>x. (y = x \<longrightarrow> Suc (count (mset ys) x) = f x) \<and>
      (y \<noteq> x \<longrightarrow> count (mset ys) x = f x)"
    have "\<forall>x. count (mset ys) x = (f(y := f y - Suc 0)) x"
      (is "\<forall>x. _ = ?f' x")
      by (simp add: A, insert spec [OF A, where x = y], simp)
    ultimately have "\<forall>x. count (mset xs') x = ?f' x" ..
    thus "(y = x \<longrightarrow> Suc (count (mset xs') x) = f x) \<and>
      (y \<noteq> x \<longrightarrow> count (mset xs') x = f x)"
      by (simp, insert spec [OF A, where x = y], rule_tac impI, simp)
  qed
next
  fix index p q r u m ns n f and key :: "'a \<Rightarrow> 'b" and xs :: "'a list"
  let ?ws = "take (Suc (Suc m)) xs"
  let ?ys = "drop (Suc (Suc m)) xs"
  let ?r = "\<lambda>m'. round_suc_suc index key ?ws m m' u"
  let ?t = "\<lambda>r' v. round index key p q r' (v, ns, ?ys)"
  assume A: "index_less index key"
  assume
   "\<And>ws a b c d e g h i n f.
      ws = ?ws \<Longrightarrow> a = bn_comp m p q r \<Longrightarrow> (b, c) = bn_comp m p q r \<Longrightarrow>
      d = ?r b \<Longrightarrow> (e, g) = ?r b \<Longrightarrow> (h, i) = g \<Longrightarrow>
        bn_inv p q (e, ns, ?ys) \<longrightarrow> add_inv n (e, ns, ?ys) \<longrightarrow>
          count_inv f (e, ns, ?ys) \<longrightarrow> count_inv f (?t c e)" and
   "bn_inv p q (u, Suc (Suc m) # ns, xs)" and
   "add_inv n (u, Suc (Suc m) # ns, xs)" and
   "count_inv f (u, Suc (Suc m) # ns, xs)"
  thus "count_inv f (round index key p q r (u, Suc (Suc m) # ns, xs))"
  proof (simp split: prod.split, ((rule_tac allI)+, ((rule_tac impI)+)?)+,
   (erule_tac conjE)+, subst (asm) (2) add_base_zero, simp)
    fix m' r' v ms' ws' xs' x
    assume
      B: "?r m' = (v, ms', ws')" and
      C: "bn_comp m p q r = (m', r')" and
      D: "bn_valid m p q" and
      E: "Suc (Suc (foldl (+) 0 ns + m)) = n" and
      F: "length xs = n"
    assume "\<And>ws a b c d e g h i n' f.
      ws = ?ws \<Longrightarrow> a = (m', r') \<Longrightarrow> b = m' \<and> c = r' \<Longrightarrow>
      d = (v, ms', ws') \<Longrightarrow> e = v \<and> g = (ms', ws') \<Longrightarrow> h = ms' \<and> i = ws' \<Longrightarrow>
        foldl (+) 0 ns = n' \<and> n - Suc (Suc m) = n' \<longrightarrow>
          (\<forall>x. count (mset ?ys) x = f x) \<longrightarrow> (\<forall>x. count (mset xs') x = f x)"
    hence "foldl (+) 0 ns = n - Suc (Suc m) \<longrightarrow>
      (\<forall>x. count (mset xs') x = count (mset ?ys) x)"
      by simp
    hence "count (mset xs') x = count (mset ?ys) x"
      using E by simp
    moreover assume "\<forall>x. count (mset xs) x = f x"
    ultimately have "f x = count (mset ?ws) x + count (mset xs') x"
      by (subst (asm) append_take_drop_id [of "Suc (Suc m)", symmetric],
       subst (asm) mset_append, simp)
    with B [symmetric] show "count (mset ws') x + count (mset xs') x = f x"
    proof (simp add: round_suc_suc_def Let_def del: count_add_mset mset_map
     split: if_split_asm, subst (1 2) add_mset_add_single, simp
     only: count_single count_union)
      let ?nmi = "mini ?ws key"
      let ?nma = "maxi ?ws key"
      let ?xmi = "?ws ! ?nmi"
      let ?xma = "?ws ! ?nma"
      let ?mi = "key ?xmi"
      let ?ma = "key ?xma"
      let ?k = "case m of 0 \<Rightarrow> m | Suc 0 \<Rightarrow> m | Suc (Suc i) \<Rightarrow> u + m'"
      let ?zs = "nths ?ws (- {?nmi, ?nma})"
      let ?ms = "enum ?zs index key ?k ?mi ?ma"
      let ?A = "{i. i < Suc (Suc m) \<and> (i = ?nmi \<or> i = ?nma) \<and> ?ws ! i = x}"
      have G: "length ?ws = Suc (Suc m)"
        using E and F by simp
      hence H: "card ?A \<le> count (mset ?ws) x"
        by (simp add: count_mset length_filter_conv_card, rule_tac card_mono,
         simp, blast)
      show "count (mset (map the (fill ?zs (offs ?ms 0) index key m ?mi ?ma))) x
        + (if ?xma = x then 1 else 0) + (if ?xmi = x then 1 else 0) =
        count (mset ?ws) x"
      proof (cases "m = 0")
        case True
        hence I: "length ?zs = 0"
          using G by (simp add: mini_maxi_nths)
        have "count (mset ?zs) x = count (mset ?ws) x - card ?A"
          using G by (subst nths_count, simp)
        hence J: "count (mset ?ws) x = card ?A"
          using H and I by simp
        from I show ?thesis
        proof (simp, (rule_tac [!] conjI, rule_tac [!] impI)+,
         simp_all (no_asm_simp) add: True)
          assume "?xmi = x" and "?xma = x"
          with G have "?A = {?nmi, ?nma}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, erule_tac disjE,
             insert mini_less [of ?ws key], insert maxi_less [of ?ws key],
             simp_all)
          with G have "card ?A = Suc (Suc 0)"
            by (simp, subst card_insert_disjoint, simp_all,
             rule_tac mini_maxi_neq, simp)
          thus "Suc (Suc 0) = count (mset (take (Suc (Suc 0)) xs)) x"
            using True and J by simp
        next
          assume "?xmi \<noteq> x" and "?xma = x"
          with G have "?A = {?nma}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, insert maxi_less [of ?ws key], simp_all)
          thus "Suc 0 = count (mset (take (Suc (Suc 0)) xs)) x"
            using True and J by simp
        next
          assume "?xmi = x" and "?xma \<noteq> x"
          with G have "?A = {?nmi}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, insert mini_less [of ?ws key], simp_all)
          thus "Suc 0 = count (mset (take (Suc (Suc 0)) xs)) x"
            using True and J by simp
        next
          assume "?xmi \<noteq> x" and "?xma \<noteq> x"
          hence "?A = {}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, simp_all)
          hence "count (mset ?ws) x = 0"
            using J by simp
          thus "x \<notin> set (take (Suc (Suc 0)) xs)"
            using True by simp
        qed
      next
        case False
        hence "0 < ?k"
          by (simp, drule_tac bn_comp_fst_nonzero [OF D], subst (asm) C,
           simp split: nat.split)
        hence "count (mset (map the (fill ?zs (offs ?ms 0) index key
          (length ?zs) ?mi ?ma))) x = count (mset ?zs) x"
          by (rule_tac fill_offs_enum_count_item [OF A], simp, rule_tac conjI,
           ((rule_tac mini_lb | rule_tac maxi_ub), erule_tac in_set_nthsD)+)
        with G show ?thesis
        proof (simp, (rule_tac [!] conjI, rule_tac [!] impI)+,
         simp_all add: mini_maxi_nths nths_count)
          assume "?xmi = x" and "?xma = x"
          with G have "?A = {?nmi, ?nma}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, erule_tac disjE,
             insert mini_less [of ?ws key], insert maxi_less [of ?ws key],
             simp_all)
          with G have "card ?A = Suc (Suc 0)"
            by (simp, subst card_insert_disjoint, simp_all,
             rule_tac mini_maxi_neq, simp)
          thus "Suc (Suc (count (mset ?ws) x - card ?A)) = count (mset ?ws) x"
            using H by simp
        next
          assume "?xmi \<noteq> x" and "?xma = x"
          with G have "?A = {?nma}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, insert maxi_less [of ?ws key], simp_all)
          thus "Suc (count (mset ?ws) x - card ?A) = count (mset ?ws) x"
            using H by simp
        next
          assume "?xmi = x" and "?xma \<noteq> x"
          with G have "?A = {?nmi}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, insert mini_less [of ?ws key], simp_all)
          thus "Suc (count (mset ?ws) x - card ?A) = count (mset ?ws) x"
            using H by simp
        next
          assume "?xmi \<noteq> x" and "?xma \<noteq> x"
          hence "?A = {}"
            by (rule_tac set_eqI, rule_tac iffI, simp_all, (erule_tac conjE)+,
             erule_tac disjE, simp_all)
          thus "count (mset ?ws) x - card ?A = count (mset ?ws) x"
            by (simp (no_asm_simp))
        qed
      qed
    qed
  qed
qed

lemma gcsort_count_inv:
  assumes
    A: "index_less index key" and
    B: "add_inv n t" and
    C: "n \<le> p"
  shows "\<lbrakk>t' \<in> gcsort_set index key p t; count_inv f t\<rbrakk> \<Longrightarrow>
    count_inv f t'"
by (erule gcsort_set.induct, simp, drule gcsort_add_inv [OF A _ B C],
 rule round_count_inv [OF A], simp_all del: bn_inv.simps, erule conjE,
 frule sym, erule subst, rule bn_inv_intro, insert C, simp)

text \<open>
\null

The only remaining task is to address step 10 of the proof method, which is done by proving theorem
@{text gcsort_count}. It holds under the conditions that the objects' number is not larger than the
counters' upper bound and function @{text index} satisfies predicate @{const index_less}, and states
that for any object, function @{const gcsort} leaves unchanged the number of its occurrences within
the input objects' list.

\null
\<close>

theorem gcsort_count:
  assumes
    A: "index_less index key" and
    B: "length xs \<le> p"
  shows "count (mset (gcsort index key p xs)) x = count (mset xs) x"
proof -
  let ?t = "(0, [length xs], xs)"
  have "count_inv (count (mset xs)) (gcsort_aux index key p ?t)"
    by (rule gcsort_count_inv [OF A _ B], rule gcsort_add_input,
     rule gcsort_aux_set, rule gcsort_count_input)
  hence "count (mset (gcsort_out (gcsort_aux index key p ?t))) x =
    (count (mset xs)) x"
    by (rule gcsort_count_intro)
  moreover have "?t = gcsort_in xs"
    by (simp add: gcsort_in_def)
  ultimately show ?thesis
    by (simp add: gcsort_def)
qed

end
