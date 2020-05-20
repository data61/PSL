section \<open>Bin Packing\<close>

theory Approx_BP_Hoare
  imports Complex_Main "HOL-Hoare.Hoare_Logic" "HOL-Library.Disjoint_Sets"
begin

text \<open>The algorithm and proofs are based on the work by Berghammer and Reuter @{cite BerghammerR03}.\<close>

subsection \<open>Formalization of a Correct Bin Packing\<close>

text \<open>Definition of the unary operator \<open>\<lbrakk>\<cdot>\<rbrakk>\<close> from the article.
      \<open>B\<close> will only be wrapped into a set if it is non-empty.\<close>
definition wrap :: "'a set \<Rightarrow> 'a set set" where
  "wrap B = (if B = {} then {} else {B})"

lemma wrap_card:
  "card (wrap B) \<le> 1"
  unfolding wrap_def by auto

text \<open>If \<open>M\<close> and \<open>N\<close> are pairwise disjoint with \<open>V\<close> and not yet contained in V,
      then the union of \<open>M\<close> and \<open>N\<close> is also pairwise disjoint with \<open>V\<close>.\<close>
lemma pairwise_disjnt_Un:
  assumes "pairwise disjnt ({M} \<union> {N} \<union> V)" "M \<notin> V" "N \<notin> V"
  shows "pairwise disjnt ({M \<union> N} \<union> V)"
  using assms unfolding pairwise_def by auto

text \<open>A Bin Packing Problem is defined like in the article:\<close>
locale BinPacking =
  fixes U :: "'a set" \<comment> \<open>A finite, non-empty set of objects\<close>
    and w :: "'a \<Rightarrow> real" \<comment> \<open>A mapping from objects to their respective weights (positive real numbers)\<close>
    and c :: nat \<comment> \<open>The maximum capacity of a bin (a natural number)\<close>
    and S :: "'a set" \<comment> \<open>The set of \<open>small\<close> objects (weight no larger than \<open>1/2\<close> of \<open>c\<close>)\<close>
    and L :: "'a set" \<comment> \<open>The set of \<open>large\<close> objects (weight larger than \<open>1/2\<close> of \<open>c\<close>)\<close>
  assumes weight: "\<forall>u \<in> U. 0 < w(u) \<and> w(u) \<le> c"
      and U_Finite: "finite U"
      and U_NE: "U \<noteq> {}"
      and S_def: "S = {u \<in> U. w(u) \<le> c / 2}"
      and L_def: "L = U - S"
begin

text \<open>In the article, this is defined as \<open>w\<close> as well. However, to avoid ambiguity,
      we will abbreviate the weight of a bin as \<open>W\<close>.\<close>
abbreviation W :: "'a set \<Rightarrow> real" where
  "W B \<equiv> (\<Sum>u \<in> B. w(u))"

text \<open>\<open>P\<close> constitutes as a correct bin packing if \<open>P\<close> is a partition of \<open>U\<close>
      (as defined in @{thm [source] partition_on_def}) and the weights of
      the bins do not exceed their maximum capacity \<open>c\<close>.\<close>
definition bp :: "'a set set \<Rightarrow> bool" where
  "bp P \<longleftrightarrow> partition_on U P \<and> (\<forall>B \<in> P. W(B) \<le> c)"

lemma bpE:
  assumes "bp P"
  shows "pairwise disjnt P" "{} \<notin> P" "\<Union>P = U" "\<forall>B \<in> P. W(B) \<le> c"
  using assms unfolding bp_def partition_on_def by blast+

lemma bpI:
  assumes "pairwise disjnt P" "{} \<notin> P" "\<Union>P = U" "\<forall>B \<in> P. W(B) \<le> c"
  shows "bp P"
  using assms unfolding bp_def partition_on_def by blast

text \<open>Although we assume the \<open>S\<close> and \<open>L\<close> sets as given, manually obtaining them from \<open>U\<close> is trivial
      and can be achieved in linear time. Proposed by the article @{cite "BerghammerR03"}.\<close>
lemma S_L_set_generation:
"VARS S L W u
  {True}
  S := {}; L := {}; W := U;
  WHILE W \<noteq> {}
  INV {W \<subseteq> U \<and> S = {v \<in> U - W. w(v) \<le> c / 2} \<and> L = {v \<in> U - W. w(v) > c / 2}} DO
    u := (SOME u. u \<in> W);
    IF 2 * w(u) \<le> c
    THEN S := S \<union> {u}
    ELSE L := L \<union> {u} FI;
    W := W - {u}
  OD
  {S = {v \<in> U. w(v) \<le> c / 2} \<and> L = {v \<in> U. w(v) > c / 2}}"
  by vcg (auto simp: some_in_eq)

subsection \<open>The Proposed Approximation Algorithm\<close>

subsubsection \<open>Functional Correctness\<close>

text \<open>According to the article, \<open>inv\<^sub>1\<close> holds if \<open>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}\<close>
      is a correct solution for the bin packing problem @{cite BerghammerR03}. However, various
      assumptions made in the article seem to suggest that more information is demanded from this
      invariant and, indeed, mere correctness (as defined in @{thm [source] bp_def}) does not appear to suffice.
      To amend this, four additional conjuncts have been added to this invariant, whose necessity
      will be explained in the following proofs. It should be noted that there may be other (shorter) ways to amend this invariant.
      This approach, however, makes for rather straight-forward proofs, as these conjuncts can be utilized and proved in relatively few steps.\<close>
definition inv\<^sub>1 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<longleftrightarrow> bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}) \<comment> \<open>A correct solution to the bin packing problem\<close>
                       \<and> \<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V \<comment> \<open>The partial solution does not contain objects that have not yet been assigned\<close>
                       \<and> B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<comment> \<open>\<open>B\<^sub>1\<close> is distinct from all the other bins\<close>
                       \<and> B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2) \<comment> \<open>\<open>B\<^sub>2\<close> is distinct from all the other bins\<close>
                       \<and> (P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {} \<comment> \<open>The first and second partial solutions are disjoint from each other.\<close>"
(*
lemma "partition_on U (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}) \<Longrightarrow> u \<in> V \<Longrightarrow>
partition_on U (P\<^sub>1 \<union> wrap (insert u B\<^sub>1) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> (V-{u})})"
  nitpick*)
lemma inv\<^sub>1E:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  shows "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})"
    and "\<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V"
    and "B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    and "B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2)"
    and "(P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
  using assms unfolding inv\<^sub>1_def by auto

lemma inv\<^sub>1I:
  assumes "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})"
    and "\<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V"
    and "B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    and "B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2)"
    and "(P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  using assms unfolding inv\<^sub>1_def by blast

lemma wrap_Un [simp]: "wrap (M \<union> {x}) = {M \<union> {x}}" unfolding wrap_def by simp
lemma wrap_empty [simp]: "wrap {} = {}" unfolding wrap_def by simp
lemma wrap_not_empty [simp]: "M \<noteq> {} \<longleftrightarrow> wrap M = {M}" unfolding wrap_def by simp

text \<open>If \<open>inv\<^sub>1\<close> holds for the current partial solution, and the weight of an object \<open>u \<in> V\<close> added to \<open>B\<^sub>1\<close> does
      not exceed its capacity, then \<open>inv\<^sub>1\<close> also holds if \<open>B\<^sub>1\<close> and \<open>{u}\<close> are replaced by \<open>B\<^sub>1 \<union> {u}\<close>.\<close>
lemma inv\<^sub>1_stepA:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V" "W(B\<^sub>1) + w(u) \<le> c"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

  text \<open>In the proof for \<open>Theorem 3.2\<close> of the article it is erroneously argued that
        if \<open>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}\<close> is a partition of \<open>U\<close>,
        then the same holds if \<open>B\<^sub>1\<close> is replaced by \<open>B\<^sub>1 \<union> {u}\<close>.
        This is, however, not necessarily the case if \<open>B\<^sub>1\<close> or \<open>{u}\<close> are already contained in the partial solution.
        Suppose \<open>P\<^sub>1\<close> contains the non-empty bin \<open>B\<^sub>1\<close>, then \<open>P\<^sub>1 \<union> wrap B\<^sub>1\<close> would still be pairwise disjoint, provided \<open>P\<^sub>1\<close> was pairwise disjoint before, as the union simply ignores the duplicate \<open>B\<^sub>1\<close>. Now, if the algorithm modifies \<open>B\<^sub>1\<close> by adding an element from \<open>V\<close> such that \<open>B\<^sub>1\<close> becomes some non-empty \<open>B\<^sub>1'\<close> with \<open>B\<^sub>1 \<inter> B\<^sub>1' \<noteq> \<emptyset>\<close> and \<open>B\<^sub>1' \<notin> P\<^sub>1\<close>, one can see that this property would no longer be preserved.
        To avoid such a situation, we will use the first additional conjunct in \<open>inv\<^sub>1\<close> to ensure that \<open>{u}\<close>
        is not yet contained in the partial solution, and the second additional conjunct to ensure that \<open>B\<^sub>1\<close>
        is not yet contained in the partial solution.\<close>

  \<comment> \<open>Rule 1: Pairwise Disjoint\<close>
  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "{{v} |v. v \<in> V} = {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    using assms(2) by blast
  then have "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> ({{u}} \<union> {{v} |v. v \<in> V - {u}}))"
    using bprules(1) assms(2) by simp
  then have "pairwise disjnt (wrap B\<^sub>1 \<union> {{u}} \<union> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})" by (simp add: Un_commute)
  then have assm: "pairwise disjnt (wrap B\<^sub>1 \<union> {{u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by (simp add: Un_assoc)
  have "pairwise disjnt ({B\<^sub>1 \<union> {u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
  proof (cases \<open>B\<^sub>1 = {}\<close>)
    case True with assm show ?thesis by simp
  next
    case False
    with assm have assm: "pairwise disjnt ({B\<^sub>1} \<union> {{u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by simp
    from NOTIN have "{u} \<notin> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}" by blast
    from pairwise_disjnt_Un[OF assm _ this] invrules(2,3) show ?thesis
      using False by auto
  qed
  then have 1: "pairwise disjnt (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})"
    unfolding wrap_Un by simp

  \<comment> \<open>Rule 2: No empty sets\<close>
  from bprules(2) have 2: "{} \<notin> P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}"
    unfolding wrap_def by simp

  \<comment> \<open>Rule 3: Union preserved\<close>
  from bprules(3) have "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}) = U"
    using assms(2) by blast
  then have 3: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}) = U"
    unfolding wrap_def by force

  \<comment> \<open>Rule 4: Weights below capacity\<close>
  have "0 < w u" using weight assms(2) bprules(3) by blast
  have "finite B\<^sub>1" using bprules(3) U_Finite by (cases \<open>B\<^sub>1 = {}\<close>) auto
  then have "W (B\<^sub>1 \<union> {u}) \<le> W B\<^sub>1 + w u" using \<open>0 < w u\<close> by (cases \<open>u \<in> B\<^sub>1\<close>) (auto simp: insert_absorb)
  also have "... \<le> c" using assms(3) .
  finally have "W (B\<^sub>1 \<union> {u}) \<le> c" .
  then have "\<forall>B \<in> wrap (B\<^sub>1 \<union> {u}). W B \<le> c" unfolding wrap_Un by blast
  moreover have "\<forall>B\<in>P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    using bprules(4) by blast
  ultimately have 4: "\<forall>B\<in>P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c" by blast
  from bpI[OF 1 2 3 4] have 1: "bp (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})" .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have "u \<in> U" using assms(2) bprules(3) by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - (V - {u})"
    unfolding L R invrules(2) ..
  have 3: "B\<^sub>1 \<union> {u} \<notin> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2"
    using NOTIN by auto
  have 4: "B\<^sub>2 \<notin> P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2"
    using invrules(4) NOTIN unfolding wrap_def by fastforce
  have 5: "(P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u})) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
    using invrules(5) NOTIN unfolding wrap_Un by auto

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

text \<open>If \<open>inv\<^sub>1\<close> holds for the current partial solution, and the weight of an object \<open>u \<in> V\<close> added to \<open>B\<^sub>2\<close> does
      not exceed its capacity, then \<open>inv\<^sub>1\<close> also holds if \<open>B\<^sub>2\<close> and \<open>{u}\<close> are replaced by \<open>B\<^sub>2 \<union> {u}\<close>.\<close>
lemma inv\<^sub>1_stepB:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V" "W B\<^sub>2 + w u \<le> c"
  shows "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

text \<open>The argumentation here is similar to the one in @{thm [source] inv\<^sub>1_stepA} with
      \<open>B\<^sub>1\<close> replaced with \<open>B\<^sub>2\<close> and using the first and third additional conjuncts of \<open>inv\<^sub>1\<close>
      to amend the issue, instead of the first and second.\<close>
  \<comment> \<open>Rule 1: Pairwise Disjoint\<close>
  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "{{v} |v. v \<in> V} = {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    using assms(2) by blast
  then have "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}})"
    using bprules(1) assms(2) by simp
  then have assm: "pairwise disjnt (wrap B\<^sub>2 \<union> {{u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
    by (simp add: Un_assoc Un_commute)
  have "pairwise disjnt ({B\<^sub>2 \<union> {u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
  proof (cases \<open>B\<^sub>2 = {}\<close>)
    case True with assm show ?thesis by simp
  next
    case False
    with assm have assm: "pairwise disjnt ({B\<^sub>2} \<union> {{u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by simp
    from NOTIN have "{u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}" by blast
    from pairwise_disjnt_Un[OF assm _ this] invrules(2,4) show ?thesis
      using False by auto
  qed
  then have 1: "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}})"
    unfolding wrap_Un by simp

  \<comment> \<open>Rule 2: No empty sets\<close>
  from bprules(2) have 2: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}"
    unfolding wrap_def by simp

  \<comment> \<open>Rule 3: Union preserved\<close>
  from bprules(3) have "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}) = U"
    using assms(2) by blast
  then have 3: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}) = U"
    unfolding wrap_def by force

  \<comment> \<open>Rule 4: Weights below capacity\<close>
  have "0 < w u" using weight assms(2) bprules(3) by blast
  have "finite B\<^sub>2" using bprules(3) U_Finite by (cases \<open>B\<^sub>2 = {}\<close>) auto
  then have "W (B\<^sub>2 \<union> {u}) \<le> W B\<^sub>2 + w u" using \<open>0 < w u\<close> by (cases \<open>u \<in> B\<^sub>2\<close>) (auto simp: insert_absorb)
  also have "... \<le> c" using assms(3) .
  finally have "W (B\<^sub>2 \<union> {u}) \<le> c" .
  then have "\<forall>B \<in> wrap (B\<^sub>2 \<union> {u}). W B \<le> c" unfolding wrap_Un by blast
  moreover have "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    using bprules(4) by blast
  ultimately have 4: "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    by auto
  from bpI[OF 1 2 3 4] have 1: "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}})" .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have "u \<in> U" using assms(2) bprules(3) by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = U - (V - {u})"
    unfolding L R using invrules(2) by simp
  have 3: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})"
    using bpE(2)[OF 1] by simp
  have 4: "B\<^sub>2 \<union> {u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2"
    using NOTIN by auto
  have 5: "(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}) \<inter> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = {}"
    using invrules(5) NOTIN unfolding wrap_empty wrap_Un by auto

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

text \<open>If \<open>inv\<^sub>1\<close> holds for the current partial solution, then \<open>inv\<^sub>1\<close> also holds if \<open>B\<^sub>1\<close> and \<open>B\<^sub>2\<close> are
      added to \<open>P\<^sub>1\<close> and \<open>P\<^sub>2\<close> respectively, \<open>B\<^sub>1\<close> is emptied and \<open>B\<^sub>2\<close> initialized with \<open>u \<in> V\<close>.\<close>
lemma inv\<^sub>1_stepC:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V"
  shows "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)]
  \<comment> \<open>Rule 1-4: Correct Bin Packing\<close>
  have "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}}
      = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    by (metis (no_types, lifting) Un_assoc Un_empty_right insert_not_empty wrap_empty wrap_not_empty)
  also have "... = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}"
    using assms(2) by auto
  finally have EQ: "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}}
                  = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}" .
  from invrules(1) have 1: "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}})"
    unfolding EQ .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "u \<in> U" using assms(2) bpE(3)[OF invrules(1)] by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}) = U - (V - {u})"
    unfolding L R using invrules(2) by auto
  have 3: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}"
    using bpE(2)[OF 1] by simp
  have 4: "{u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using NOTIN by auto
  have 5: "(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}) = {}"
    using invrules(5) NOTIN unfolding wrap_def by force

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

text \<open>A simplified version of the bin packing algorithm proposed in the article.
      It serves as an introduction into the approach taken, and, while it does not provide the desired
      approximation factor, it does ensure that \<open>P\<close> is a correct solution of the bin packing problem.\<close>
lemma simple_bp_correct:
"VARS P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u
  {True}
  P\<^sub>1 := {}; P\<^sub>2 := {}; B\<^sub>1 := {}; B\<^sub>2 := {}; V := U;
  WHILE V \<inter> S \<noteq> {} INV {inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V} DO
    u := (SOME u. u \<in> V); V := V - {u};
    IF W(B\<^sub>1) + w(u) \<le> c
    THEN B\<^sub>1 := B\<^sub>1 \<union> {u}
    ELSE IF W(B\<^sub>2) + w(u) \<le> c
         THEN B\<^sub>2 := B\<^sub>2 \<union> {u}
         ELSE P\<^sub>2 := P\<^sub>2 \<union> wrap B\<^sub>2; B\<^sub>2 := {u} FI;
         P\<^sub>1 := P\<^sub>1 \<union> wrap B\<^sub>1; B\<^sub>1 := {} FI
  OD;
  P := P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} | v. v \<in> V}
  {bp P}"
proof (vcg, goal_cases)
  case (1 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  show ?case
    unfolding bp_def partition_on_def pairwise_def wrap_def inv\<^sub>1_def
    using weight by auto
next
  case (2 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  then have INV: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" ..
  from 2 have "V \<noteq> {}" by blast
  then have IN: "(SOME u. u \<in> V) \<in> V" by (simp add: some_in_eq)
  from inv\<^sub>1_stepA[OF INV IN] inv\<^sub>1_stepB[OF INV IN] inv\<^sub>1_stepC[OF INV IN]
  show ?case by blast
next
  case (3 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  then show ?case unfolding inv\<^sub>1_def by blast
qed

subsubsection \<open>Lower Bounds for the Bin Packing Problem\<close>

lemma bp_bins_finite [simp]:
  assumes "bp P"
  shows "\<forall>B \<in> P. finite B"
  using bpE(3)[OF assms] U_Finite by (meson Sup_upper finite_subset)

lemma bp_sol_finite [simp]:
  assumes "bp P"
  shows "finite P"
  using bpE(3)[OF assms] U_Finite by (simp add: finite_UnionD)

text \<open>If \<open>P\<close> is a solution of the bin packing problem, then no bin in \<open>P\<close> may contain more than
      one large object.\<close>
lemma only_one_L_per_bin:
  assumes "bp P" "B \<in> P"
  shows "\<forall>x \<in> B. \<forall>y \<in> B. x \<noteq> y \<longrightarrow> x \<notin> L \<or> y \<notin> L"
proof (rule ccontr, simp)
  assume "\<exists>x\<in>B. \<exists>y\<in>B. x \<noteq> y \<and> x \<in> L \<and> y \<in> L"
  then obtain x y where *: "x \<in> B" "y \<in> B" "x \<noteq> y" "x \<in> L" "y \<in> L" by blast
  then have "c < w x + w y" using L_def S_def by force
  have "finite B" using assms by simp
  have "y \<in> B - {x}" using *(2,3) by blast
  have "W B = W (B - {x}) + w x"
    using *(1) \<open>finite B\<close> by (simp add: sum.remove)
  also have "... = W (B - {x} - {y}) + w x + w y"
    using \<open>y \<in> B - {x}\<close> \<open>finite B\<close> by (simp add: sum.remove)
  finally have *: "W B = W (B - {x} - {y}) + w x + w y" .
  have "\<forall>u \<in> B. 0 < w u" using bpE(3)[OF assms(1)] assms(2) weight by blast
  then have "0 \<le> W (B - {x} - {y})" by (smt DiffD1 sum_nonneg)
  with * have "c < W B" using \<open>c < w x + w y\<close> by simp
  then show False using bpE(4)[OF assms(1)] assms(2) by fastforce
qed

text \<open>If \<open>P\<close> is a solution of the bin packing problem, then the amount of large objects
      is a lower bound for the amount of bins in P.\<close>
lemma L_lower_bound_card:
  assumes "bp P"
  shows "card L \<le> card P"
proof -
  have "\<forall>x \<in> L. \<exists>B \<in> P. x \<in> B"
    using bpE(3)[OF assms] L_def by blast
  then obtain f where f_def: "\<forall>u \<in> L. u \<in> f u \<and> f u \<in> P" by metis
  then have "inj_on f L"
    unfolding inj_on_def using only_one_L_per_bin[OF assms] by blast
  then have card_eq: "card L = card (f ` L)" by (simp add: card_image)
  have "f ` L \<subseteq> P" using f_def by blast
  moreover have "finite P" using assms by simp
  ultimately have "card (f ` L) \<le> card P" by (simp add: card_mono)
  then show ?thesis unfolding card_eq .
qed

text \<open>If \<open>P\<close> is a solution of the bin packing problem, then the amount of bins of a subset of P
      in which every bin contains a large object is a lower bound on the amount of large objects.\<close>
lemma subset_bp_card:
  assumes "bp P" "M \<subseteq> P" "\<forall>B \<in> M. B \<inter> L \<noteq> {}"
  shows "card M \<le> card L"
proof -
  have "\<forall>B \<in> M. \<exists>u \<in> L. u \<in> B" using assms(3) by fast
  then have "\<exists>f. \<forall>B \<in> M. f B \<in> L \<and> f B \<in> B" by metis
  then obtain f where f_def: "\<forall>B \<in> M. f B \<in> L \<and> f B \<in> B" ..
  have "inj_on f M"
  proof (rule ccontr)
    assume "\<not> inj_on f M"
    then have "\<exists>x \<in> M. \<exists>y \<in> M. x \<noteq> y \<and> f x = f y" unfolding inj_on_def by blast
    then obtain x y where *: "x \<in> M" "y \<in> M" "x \<noteq> y" "f x = f y" by blast
    then have "\<exists>u. u \<in> x \<and> u \<in> y" using f_def by metis
    then have "x \<inter> y \<noteq> {}" by blast
    moreover have "pairwise disjnt M" using pairwise_subset[OF bpE(1)[OF assms(1)] assms(2)] .
    ultimately show False using * unfolding pairwise_def disjnt_def by simp
  qed
  moreover have "finite L" using L_def U_Finite by blast
  moreover have "f ` M \<subseteq> L" using f_def by blast
  ultimately show ?thesis using card_inj_on_le by blast
qed

text \<open>If \<open>P\<close> is a correct solution of the bin packing problem, \<open>inv\<^sub>1\<close> holds for the partial solution,
      and every bin in \<open>P\<^sub>1 \<union> wrap B\<^sub>1\<close> contains a large object, then the amount of bins in
      \<open>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L}\<close> is a lower bound for the amount of bins in \<open>P\<close>.\<close>
lemma L_bins_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L \<noteq> {}"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L}) \<le> card P"
proof -
  note invrules = inv\<^sub>1E[OF assms(2)]
  have "\<forall>B \<in> {{v} |v. v \<in> V \<inter> L}. B \<inter> L \<noteq> {}" by blast
  with assms(3) have
    "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L} \<subseteq> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}"
    "\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L}. B \<inter> L \<noteq> {}" by blast+
  from subset_bp_card[OF invrules(1) this] show ?thesis
    using L_lower_bound_card[OF assms(1)] by linarith
qed

text \<open>If \<open>P\<close> is a correct solution of the bin packing problem, then the sum of the weights of the
      objects is equal to the sum of the weights of the bins in \<open>P\<close>.\<close>
lemma sum_Un_eq_sum_sum:
  assumes "bp P"
  shows "(\<Sum>u \<in> U. w u) = (\<Sum>B \<in> P. W B)"
proof -
  have FINITE: "\<forall>B \<in> P. finite B" using assms by simp
  have DISJNT: "\<forall>A \<in> P. \<forall>B \<in> P. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using bpE(1)[OF assms] unfolding pairwise_def disjnt_def .
  have "(\<Sum>u \<in> (\<Union>P). w u) = (\<Sum>B \<in> P. W B)"
    using sum.Union_disjoint[OF FINITE DISJNT] by auto
  then show ?thesis unfolding bpE(3)[OF assms] .
qed

text \<open>If \<open>P\<close> is a correct solution of the bin packing problem, then the sum of the weights of the items
      is a lower bound of amount of bins in \<open>P\<close> multiplied by their maximum capacity.\<close>
lemma sum_lower_bound_card:
  assumes "bp P"
  shows "(\<Sum>u \<in> U. w u) \<le> c * card P"
proof -
  have *: "\<forall>B \<in> P. 0 < W B \<and> W B \<le> c"
    using bpE(2-4)[OF assms] weight by (metis UnionI assms bp_bins_finite sum_pos)
  have "(\<Sum>u \<in> U. w u) = (\<Sum>B \<in> P. W B)"
    using sum_Un_eq_sum_sum[OF assms] .
  also have "... \<le> (\<Sum>B \<in> P. c)" using sum_mono * by fastforce
  also have "... = c * card P" by simp
  finally show ?thesis .
qed

lemma bp_NE:
  assumes "bp P"
  shows "P \<noteq> {}"
  using U_NE bpE(3)[OF assms] by blast

lemma sum_Un_ge:
  fixes f :: "_ \<Rightarrow> real"
  assumes "finite M" "finite N" "\<forall>B \<in> M \<union> N. 0 < f B"
  shows "sum f M \<le> sum f (M \<union> N)"
proof -
  have "0 \<le> sum f N - sum f (M \<inter> N)"
    using assms by (smt DiffD1 inf.cobounded2 UnCI sum_mono2)
  then have "sum f M \<le> sum f M + sum f N - sum f (M \<inter> N)"
    by simp
  also have "... = sum f (M \<union> N)"
    using sum_Un[OF assms(1,2), symmetric] .
  finally show ?thesis .
qed

text \<open>If \<open>bij_exists\<close> holds, one can obtain a function which is bijective between the bins in \<open>P\<close>
and the objects in \<open>V\<close> such that an object returned by the function would cause the bin to
exceed its capacity.\<close>
definition bij_exists :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bij_exists P V = (\<exists>f. bij_betw f P V \<and> (\<forall>B \<in> P. W B + w (f B) > c))"

text \<open>If \<open>P\<close> is a functionally correct solution of the bin packing problem, \<open>inv\<^sub>1\<close> holds for the
partial solution, and such a bijective function exists between the bins in \<open>P\<^sub>1\<close> and the objects in
@{term "P\<^sub>2 \<union> wrap B\<^sub>2"}, the following strict lower bound can be shown:\<close>
lemma P\<^sub>1_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "card P\<^sub>1 + 1 \<le> card P"
proof (cases \<open>P\<^sub>1 = {}\<close>)
  case True
  have "finite P" using assms(1) by simp
  then have "1 \<le> card P" using bp_NE[OF assms(1)]
    by (metis Nat.add_0_right Suc_diff_1 Suc_le_mono card_gt_0_iff le0 mult_Suc_right nat_mult_1)
  then show ?thesis unfolding True by simp
next
  note invrules = inv\<^sub>1E[OF assms(2)]
  case False
  obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B \<in> P\<^sub>1. W B + w (f B) > c"
    using assms(3) unfolding bij_exists_def by blast
  have FINITE: "finite P\<^sub>1" "finite (P\<^sub>2 \<union> wrap B\<^sub>2)" "finite (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)" "finite (wrap B\<^sub>1 \<union> {{v} |v. v \<in> V})"
    using inv\<^sub>1E(1)[OF assms(2)] bp_sol_finite by blast+

  have F: "\<forall>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. finite B" using invrules(1) by simp
  have D: "\<forall>A \<in> P\<^sub>2 \<union> wrap B\<^sub>2. \<forall>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using bpE(1)[OF invrules(1)] unfolding pairwise_def disjnt_def by auto
  have sum_eq: "W (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) = (\<Sum>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. W B)"
    using sum.Union_disjoint[OF F D] by auto

  have "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}. 0 < W B"
    using bpE(2,3)[OF invrules(1)] weight by (metis (no_types, lifting) UnionI bp_bins_finite invrules(1) sum_pos)
  then have "(\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B) \<le> (\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> (wrap B\<^sub>1 \<union> {{v} |v. v \<in> V}). W B)"
    using sum_Un_ge[OF FINITE(3,4), of W] by blast
  also have "... = (\<Sum>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}. W B)" by (smt Un_assoc Un_commute) 
  also have "... = W U" using sum_Un_eq_sum_sum[OF invrules(1), symmetric] .
  finally have *: "(\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B) \<le> W U" .

  \<comment> \<open>This follows from the fourth and final additional conjunct of \<open>inv\<^sub>1\<close> and is necessary to combine the sums of the bins
      of the two partial solutions. This does not inherently follow from the union being a correct solution,
      as this need not be the case if \<open>P\<^sub>1\<close> and \<open>P\<^sub>2 \<union> wrap B\<^sub>2\<close> happened to be equal.\<close>
  have DISJNT: "P\<^sub>1 \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}" using invrules(5) by blast

  \<comment> \<open>This part of the proof is based on the proof on page 72 of the article @{cite BerghammerR03}.\<close>
  have "c * card P\<^sub>1 = (\<Sum>B \<in> P\<^sub>1. c)" by simp
  also have "... < (\<Sum>B \<in> P\<^sub>1. W B + w (f B))"
    using f_def(2) sum_strict_mono[OF FINITE(1) False] by fastforce
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + (\<Sum>B \<in> P\<^sub>1. w (f B))"
    by (simp add: Groups_Big.comm_monoid_add_class.sum.distrib)
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + W (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" unfolding sum.reindex_bij_betw[OF f_def(1), of w] ..
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + (\<Sum>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. W B)" unfolding sum_eq ..
  also have "... = (\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B)" using sum.union_disjoint[OF FINITE(1,2) DISJNT, of W] by (simp add: Un_assoc)
  also have "... \<le> (\<Sum>u \<in> U. w u)" using * .
  also have "... \<le> c * card P" using sum_lower_bound_card[OF assms(1)] .
  finally show ?thesis by (meson discrete nat_mult_less_cancel_disj of_nat_less_imp_less)
qed

text \<open>As @{thm wrap_card} holds, it follows that the amount of bins in \<open>P\<^sub>1 \<union> wrap B\<^sub>1\<close>
      are a lower bound for the amount of bins in \<open>P\<close>.\<close>
lemma P\<^sub>1_B\<^sub>1_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1) \<le> card P"
proof -
  have "card (P\<^sub>1 \<union> wrap B\<^sub>1) \<le> card P\<^sub>1 + card (wrap B\<^sub>1)"
    using card_Un_le by blast
  also have "... \<le> card P\<^sub>1 + 1" using wrap_card by simp
  also have "... \<le> card P" using P\<^sub>1_lower_bound_card[OF assms] .
  finally show ?thesis .
qed

text \<open>If \<open>inv\<^sub>1\<close> holds, there are at most half as many bins in \<open>P\<^sub>2\<close> as there are objects in \<open>P\<^sub>2\<close>, and we can again
      obtain a bijective function between the bins in \<open>P\<^sub>1\<close> and the objects of the second partial solution,
      then the amount of bins in the second partial solution are a strict lower bound for half the bins of
      the first partial solution.\<close>
lemma P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> card P\<^sub>1 + 1"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

  have "pairwise disjnt (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using bprules(1) pairwise_subset by blast
  moreover have "B\<^sub>2 \<notin> P\<^sub>2" using invrules(4) by simp
  ultimately have DISJNT: "\<Union>P\<^sub>2 \<inter> B\<^sub>2 = {}"
    by (auto, metis (no_types, hide_lams) sup_bot.right_neutral Un_insert_right disjnt_iff mk_disjoint_insert pairwise_insert wrap_Un)

  have "finite (\<Union>P\<^sub>2)" using U_Finite bprules(3) by auto
  have "finite B\<^sub>2" using bp_bins_finite[OF invrules(1)] wrap_not_empty by blast
  have "finite P\<^sub>2" "finite (wrap B\<^sub>2)" using bp_sol_finite[OF invrules(1)] by blast+
  have DISJNT2: "P\<^sub>2 \<inter> wrap B\<^sub>2 = {}" unfolding wrap_def using \<open>B\<^sub>2 \<notin> P\<^sub>2\<close> by auto
  have "card (wrap B\<^sub>2) \<le> card B\<^sub>2"
  proof (cases \<open>B\<^sub>2 = {}\<close>)
    case False
    then have "1 \<le> card B\<^sub>2" by (simp add: leI \<open>finite B\<^sub>2\<close>)
    then show ?thesis using wrap_card[of B\<^sub>2] by linarith
  qed simp

  \<comment> \<open>This part of the proof is based on the proof on page 73 of the article @{cite BerghammerR03}.\<close>
  from assms(2) have "2 * card P\<^sub>2 + 2 * card (wrap B\<^sub>2) \<le> card (\<Union>P\<^sub>2) + card (wrap B\<^sub>2) + 1"
    using wrap_card[of B\<^sub>2] by linarith
  then have "2 * (card P\<^sub>2 + card (wrap B\<^sub>2)) \<le> card (\<Union>P\<^sub>2) + card B\<^sub>2 + 1"
    using \<open>card (wrap B\<^sub>2) \<le> card B\<^sub>2\<close> by simp
  then have "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card (\<Union>P\<^sub>2 \<union> B\<^sub>2) + 1"
    using card_Un_disjoint[OF \<open>finite (\<Union>P\<^sub>2)\<close> \<open>finite B\<^sub>2\<close> DISJNT]
      and card_Un_disjoint[OF \<open>finite P\<^sub>2\<close> \<open>finite (wrap B\<^sub>2)\<close> DISJNT2] by argo
  then have "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2)) + 1"
    by (cases \<open>B\<^sub>2 = {}\<close>) (auto simp: Un_commute)
  then show "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card P\<^sub>1 + 1"
    using assms(3) bij_betw_same_card unfolding bij_exists_def by metis
qed

subsubsection \<open>Proving the Approximation Factor\<close>

text \<open>We define \<open>inv\<^sub>2\<close> as it is defined in the article.
      These conjuncts allow us to prove the desired approximation factor.\<close>
definition inv\<^sub>2 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<longleftrightarrow> inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<comment> \<open>\<open>inv\<^sub>1\<close> holds for the partial solution\<close>
                       \<and> (V \<inter> L \<noteq> {} \<longrightarrow> (\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L \<noteq> {})) \<comment> \<open>If there are still large objects left, then every bin of the first partial solution must contain a large object\<close>
                       \<and> bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2)) \<comment> \<open>There exists a bijective function between the bins of the first partial solution and the objects of the second one\<close>
                       \<and> (2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)) \<comment> \<open>There are at most twice as many bins in \<open>P\<^sub>2\<close> as there are objects in \<open>P\<^sub>2\<close>\<close>"

lemma inv\<^sub>2E:
  assumes "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
    and "V \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L \<noteq> {}"
    and "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
    and "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)"
  using assms unfolding inv\<^sub>2_def by blast+

lemma inv\<^sub>2I:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
    and "V \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L \<noteq> {}"
    and "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
    and "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)"
  shows "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  using assms unfolding inv\<^sub>2_def by blast

text \<open>If \<open>P\<close> is a correct solution of the bin packing problem, \<open>inv\<^sub>2\<close> holds for the partial solution,
      and there are no more small objects left to be distributed, then the amount of bins of the partial solution
      is no larger than \<open>3 / 2\<close> of the amount of bins in \<open>P\<close>. This proof strongly follows the proof in
      \<open>Theorem 4.1\<close> of the article @{cite BerghammerR03}.\<close>
lemma bin_packing_lower_bound_card:
  assumes "V \<inter> S = {}" "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "bp P"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}) \<le> 3 / 2 * card P"
proof (cases \<open>V = {}\<close>)
  note invrules = inv\<^sub>2E[OF assms(2)]
  case True
  then have "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})
           = card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)" by simp
  also have "... \<le> card (P\<^sub>1 \<union> wrap B\<^sub>1) + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using card_Un_le[of \<open>P\<^sub>1 \<union> wrap B\<^sub>1\<close>] by (simp add: Un_assoc)
  also have "... \<le> card P + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using P\<^sub>1_B\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by simp
  also have "... \<le> card P + card P / 2"
    using P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1[OF invrules(1,4,3)]
      and P\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by linarith
  finally show ?thesis by linarith
next
  note invrules = inv\<^sub>2E[OF assms(2)]
  case False
  have "U = S \<union> L" using S_def L_def by blast
  then have *: "V = V \<inter> L"
    using bpE(3)[OF inv\<^sub>1E(1)[OF invrules(1)]]
      and assms(1) by blast
  with False have NE: "V \<inter> L \<noteq> {}" by simp
  have "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})
      = card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L} \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    using * by (simp add: Un_commute Un_assoc)
  also have "... \<le> card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L}) + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using card_Un_le[of \<open>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> V \<inter> L}\<close>] by (simp add: Un_assoc)
  also have "... \<le> card P + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using L_bins_lower_bound_card[OF assms(3) invrules(1) invrules(2)[OF NE]] by linarith
  also have "... \<le> card P + card P / 2"
    using P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1[OF invrules(1,4,3)]
      and P\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by linarith
  finally show ?thesis by linarith
qed

text \<open>We define \<open>inv\<^sub>3\<close> as it is defined in the article.
      This final conjunct allows us to prove that the invariant will be maintained by the algorithm.\<close>
definition inv\<^sub>3 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<longleftrightarrow> inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<and> B\<^sub>2 \<subseteq> S"

lemma inv\<^sub>3E:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  shows "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" and "B\<^sub>2 \<subseteq> S"
  using assms unfolding inv\<^sub>3_def by blast+

lemma inv\<^sub>3I:
  assumes "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" and "B\<^sub>2 \<subseteq> S"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  using assms unfolding inv\<^sub>3_def by blast

lemma loop_init:
  "inv\<^sub>3 {} {} {} {} U"
proof -
  have *: "inv\<^sub>1 {} {} {} {} U"
    unfolding bp_def partition_on_def pairwise_def wrap_def inv\<^sub>1_def
    using weight by auto
  have "bij_exists {} (\<Union> ({} \<union> wrap {}))"
    using bij_betwI' unfolding bij_exists_def by fastforce
  from inv\<^sub>2I[OF * _ this] have "inv\<^sub>2 {} {} {} {} U" by auto
  from inv\<^sub>3I[OF this] show ?thesis by blast
qed

text \<open>If \<open>B\<^sub>1\<close> is empty and there are no large objects left, then \<open>inv\<^sub>3\<close> will be maintained
      if \<open>B\<^sub>1\<close> is initialized with \<open>u \<in> V \<inter> S\<close>.\<close>
lemma loop_stepA:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "B\<^sub>1 = {}" "V \<inter> L = {}" "u \<in> V \<inter> S"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have WEIGHT: "W B\<^sub>1 + w u \<le> c" using S_def assms(2,4) by simp
  from assms(4) have "u \<in> V" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this WEIGHT] assms(2) have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})" by simp
  have 2: "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap {u}. B \<inter> L \<noteq> {}" using assms(3) by blast
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

text \<open>If \<open>B\<^sub>1\<close> is empty and there are large objects left, then \<open>inv\<^sub>3\<close> will be maintained
      if \<open>B\<^sub>1\<close> is initialized with \<open>u \<in> V \<inter> L\<close>.\<close>
lemma loop_stepB:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "B\<^sub>1 = {}" "u \<in> V \<inter> L"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have WEIGHT: "W B\<^sub>1 + w u \<le> c" using L_def weight assms(2,3) by simp
  from assms(3) have "u \<in> V" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this WEIGHT] assms(2) have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})" by simp
  have "\<forall>B\<in>P\<^sub>1. B \<inter> L \<noteq> {}" using assms(3) invrules(2) by blast
  then have 2: "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap {u}. B \<inter> L \<noteq> {}"
    using assms(3) by (metis Int_iff UnE empty_iff insertE singletonI wrap_not_empty)
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (V - {u})" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

text \<open>If \<open>B\<^sub>1\<close> is not empty and \<open>u \<in> V \<inter> S\<close> does not exceed its maximum capacity, then \<open>inv\<^sub>3\<close>
      will be maintained if \<open>B\<^sub>1\<close> and \<open>{u}\<close> are replaced with \<open>B\<^sub>1 \<union> {u}\<close>.\<close>
lemma loop_stepC:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "B\<^sub>1 \<noteq> {}" "u \<in> V \<inter> S" "W B\<^sub>1 + w(u) \<le> c"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (V - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  from assms(3) have "u \<in> V" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this assms(4)] have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (V - {u})" .
  have "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L \<noteq> {}" using invrules(2) by blast
  then have 2: "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}). B \<inter> L \<noteq> {}"
    by (metis Int_commute Un_empty_right Un_insert_right assms(2) disjoint_insert(2) insert_iff wrap_not_empty)
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (V - {u})" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

text \<open>If \<open>B\<^sub>1\<close> is not empty and \<open>u \<in> V \<inter> S\<close> does exceed its maximum capacity but not the capacity of \<open>B\<^sub>2\<close>,
      then \<open>inv\<^sub>3\<close> will be maintained if \<open>B\<^sub>1\<close> is added to \<open>P\<^sub>1\<close> and emptied, and \<open>B\<^sub>2\<close> and \<open>{u}\<close> are replaced with \<open>B\<^sub>2 \<union> {u}\<close>.\<close>
lemma loop_stepD:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "B\<^sub>1 \<noteq> {}" "u \<in> V \<inter> S" "W B\<^sub>1 + w(u) > c" "W B\<^sub>2 + w(u) \<le> c"
  shows "inv\<^sub>3 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (V - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  from assms(3) have "u \<in> V" by blast
  from inv\<^sub>1_stepB[OF invrules(1) this assms(5)] have 1: "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (V - {u})" .

  have 2: "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}. B \<inter> L \<noteq> {}"
    using invrules(2) unfolding wrap_empty by blast

  from invrules(3) obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B\<in>P\<^sub>1. c < W B + w (f B)" unfolding bij_exists_def by blast
  have "B\<^sub>1 \<notin> P\<^sub>1" using inv\<^sub>1E(3)[OF invrules(1)] by blast
  have "u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" using inv\<^sub>1E(2)[OF invrules(1)] assms(3) by blast
  then have "(\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}))) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}}))"
    by (metis Sup_empty Un_assoc Union_Un_distrib ccpo_Sup_singleton wrap_empty wrap_not_empty)
  also have "... = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" by simp
  finally have UN: "(\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}))) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" .
  have "wrap B\<^sub>1 = {B\<^sub>1}" using wrap_not_empty[of B\<^sub>1] assms(2) by simp
  let ?f = "f (B\<^sub>1 := u)"
  have BIJ: "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))"
    unfolding wrap_empty \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> UN using f_def(1) \<open>B\<^sub>1 \<notin> P\<^sub>1\<close> \<open>u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))\<close>
    by (metis (no_types, lifting) bij_betw_cong fun_upd_other fun_upd_same notIn_Un_bij_betw3)
  have "c < W B\<^sub>1 + w (?f B\<^sub>1)" using assms(4) by simp
  then have "(\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))"
    unfolding \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> using f_def(2) by simp
  with BIJ have "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))
              \<and> (\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))" by blast
  then have 3: "bij_exists (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))"
    unfolding bij_exists_def by blast
  from inv\<^sub>2I[OF 1 2 3] have "inv\<^sub>2 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (V - {u})" using invrules(4) by blast

  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] assms(3) by blast
qed

text \<open>If the maximum capacity of \<open>B\<^sub>2\<close> is exceeded by \<open>u \<in> V \<inter> S\<close>,
      then \<open>B\<^sub>2\<close> must contain at least two objects.\<close>
lemma B\<^sub>2_at_least_two_objects:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V \<inter> S" "W B\<^sub>2 + w(u) > c"
  shows "2 \<le> card B\<^sub>2"
proof (rule ccontr, simp add: not_le)
  have FINITE: "finite B\<^sub>2" using inv\<^sub>1E(1)[OF inv\<^sub>2E(1)[OF inv\<^sub>3E(1)[OF assms(1)]]]
    by (metis (no_types, lifting) Finite_Set.finite.simps U_Finite Union_Un_distrib bpE(3) ccpo_Sup_singleton finite_Un wrap_not_empty)
  assume "card B\<^sub>2 < 2"
  then consider (0) "card B\<^sub>2 = 0" | (1) "card B\<^sub>2 = 1" by linarith
  then show False proof cases
    case 0 then have "B\<^sub>2 = {}" using FINITE by simp
    then show ?thesis using assms(2,3) S_def by simp
  next
    case 1 then obtain v where "B\<^sub>2 = {v}"
      using card_1_singletonE by auto
    with inv\<^sub>3E(2)[OF assms(1)] have "2 * w v \<le> c" using S_def by simp
    moreover from \<open>B\<^sub>2 = {v}\<close> have "W B\<^sub>2 = w v" by simp
    ultimately show ?thesis using assms(2,3) S_def by simp
  qed
qed

text \<open>If \<open>B\<^sub>1\<close> is not empty and \<open>u \<in> V \<inter> S\<close> exceeds the maximum capacity of both \<open>B\<^sub>1\<close> and \<open>B\<^sub>2\<close>,
      then \<open>inv\<^sub>3\<close> will be maintained if \<open>B\<^sub>1\<close> and \<open>B\<^sub>2\<close> are added to \<open>P\<^sub>1\<close> and \<open>P\<^sub>2\<close> respectively,
      emptied, and \<open>B\<^sub>2\<close> initialized with \<open>u\<close>.\<close>
lemma loop_stepE:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "B\<^sub>1 \<noteq> {}" "u \<in> V \<inter> S" "W B\<^sub>1 + w(u) > c" "W B\<^sub>2 + w(u) > c"
  shows "inv\<^sub>3 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (V - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  from assms(3) have "u \<in> V" by blast
  from inv\<^sub>1_stepC[OF invrules(1) this] have 1: "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (V - {u})" .

  have 2: "(V - {u}) \<inter> L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}. B \<inter> L \<noteq> {}"
    using invrules(2) unfolding wrap_empty by blast

  from invrules(3) obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B\<in>P\<^sub>1. c < W B + w (f B)" unfolding bij_exists_def by blast
  have "B\<^sub>1 \<notin> P\<^sub>1" using inv\<^sub>1E(3)[OF invrules(1)] by blast
  have "u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" using inv\<^sub>1E(2)[OF invrules(1)] assms(3) by blast
  have "(\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u})) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}}))" unfolding wrap_def by simp
  also have "... = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" by simp
  finally have UN: "(\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u})) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" .
  have "wrap B\<^sub>1 = {B\<^sub>1}" using wrap_not_empty[of B\<^sub>1] assms(2) by simp
  let ?f = "f (B\<^sub>1 := u)"
  have BIJ: "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))"
    unfolding wrap_empty \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> UN using f_def(1) \<open>B\<^sub>1 \<notin> P\<^sub>1\<close> \<open>u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))\<close>
    by (metis (no_types, lifting) bij_betw_cong fun_upd_other fun_upd_same notIn_Un_bij_betw3)
  have "c < W B\<^sub>1 + w (?f B\<^sub>1)" using assms(4) by simp
  then have "(\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))"
    unfolding \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> using f_def(2) by simp
  with BIJ have "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))
              \<and> (\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))" by blast
  then have 3: "bij_exists (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))"
    unfolding bij_exists_def by blast

  have 4: "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> card (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))"
  proof -
    note bprules = bpE[OF inv\<^sub>1E(1)[OF invrules(1)]]
    have "pairwise disjnt (P\<^sub>2 \<union> wrap B\<^sub>2)"
      using bprules(1) pairwise_subset by blast
    moreover have "B\<^sub>2 \<notin> P\<^sub>2" using inv\<^sub>1E(4)[OF invrules(1)]  by simp
    ultimately have DISJNT: "\<Union>P\<^sub>2 \<inter> B\<^sub>2 = {}"
      by (auto, metis (no_types, hide_lams) sup_bot.right_neutral Un_insert_right disjnt_iff mk_disjoint_insert pairwise_insert wrap_Un)
    have "finite (\<Union>P\<^sub>2)" using U_Finite bprules(3) by auto
    have "finite B\<^sub>2" using inv\<^sub>1E(1)[OF invrules(1)] bp_bins_finite wrap_not_empty by blast

    have "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> 2 * (card P\<^sub>2 + card (wrap B\<^sub>2))"
      using card_Un_le[of P\<^sub>2 \<open>wrap B\<^sub>2\<close>] by simp
    also have "... \<le> 2 * card P\<^sub>2 + 2" using wrap_card by auto
    also have "... \<le> card (\<Union> P\<^sub>2) + 2" using invrules(4) by simp
    also have "... \<le> card (\<Union> P\<^sub>2) + card B\<^sub>2" using B\<^sub>2_at_least_two_objects[OF assms(1,3,5)] by simp
    also have "... = card (\<Union> (P\<^sub>2 \<union> {B\<^sub>2}))" using DISJNT card_Un_disjoint[OF \<open>finite (\<Union>P\<^sub>2)\<close> \<open>finite B\<^sub>2\<close>] by (simp add: Un_commute)
    also have "... = card (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" by (cases \<open>B\<^sub>2 = {}\<close>) auto
    finally show ?thesis .
  qed
  from inv\<^sub>2I[OF 1 2 3 4] have "inv\<^sub>2 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (V - {u})" .

  from inv\<^sub>3I[OF this] show ?thesis using assms(3) by blast
qed

text \<open>The bin packing algorithm as it is proposed in the article @{cite BerghammerR03}.
      \<open>P\<close> will not only be a correct solution of the bin packing problem, but the amount of bins
      will be a lower bound for \<open>3 / 2\<close> of the amount of bins of any correct solution \<open>Q\<close>, and thus
      guarantee an approximation factor of \<open>3 / 2\<close> for the optimum.\<close>
lemma bp_approx:
"VARS P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u
  {True}
  P\<^sub>1 := {}; P\<^sub>2 := {}; B\<^sub>1 := {}; B\<^sub>2 := {}; V := U;
  WHILE V \<inter> S \<noteq> {} INV {inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V} DO 
    IF B\<^sub>1 \<noteq> {}
    THEN u := (SOME u. u \<in> V \<inter> S)
    ELSE IF V \<inter> L \<noteq> {}
         THEN u := (SOME u. u \<in> V \<inter> L)
         ELSE u := (SOME u. u \<in> V \<inter> S) FI FI;
    V := V - {u};
    IF W(B\<^sub>1) + w(u) \<le> c
    THEN B\<^sub>1 := B\<^sub>1 \<union> {u}
    ELSE IF W(B\<^sub>2) + w(u) \<le> c
         THEN B\<^sub>2 := B\<^sub>2 \<union> {u}
         ELSE P\<^sub>2 := P\<^sub>2 \<union> wrap B\<^sub>2; B\<^sub>2 := {u} FI;
         P\<^sub>1 := P\<^sub>1 \<union> wrap B\<^sub>1; B\<^sub>1 := {} FI
  OD;
  P := P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} | v. v \<in> V}
  {bp P \<and> (\<forall>Q. bp Q \<longrightarrow> card P \<le> 3 / 2 * card Q)}"
proof (vcg, goal_cases)
case (1 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  then show ?case by (simp add: loop_init)
next
  case (2 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  then have INV: "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" ..
  let ?s = "SOME u. u \<in> V \<inter> S"
  let ?l = "SOME u. u \<in> V \<inter> L"
  have LIN: "V \<inter> L \<noteq> {} \<Longrightarrow> ?l \<in> V \<inter> L" using some_in_eq by metis
  then have LWEIGHT: "V \<inter> L \<noteq> {} \<Longrightarrow> w ?l \<le> c" using L_def weight by blast
  from 2 have "V \<inter> S \<noteq> {}" ..
  then have IN: "?s \<in> V \<inter> S" using some_in_eq by metis
  then have "w ?s \<le> c" using S_def by simp

  then show ?case
    using LWEIGHT loop_stepA[OF INV _ _ IN] loop_stepB[OF INV _ LIN] loop_stepC[OF INV _ IN]
      and loop_stepD[OF INV _ IN] loop_stepE[OF INV _ IN] by (cases \<open>B\<^sub>1 = {}\<close>, cases \<open>V \<inter> L = {}\<close>) auto
next
  case (3 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V u)
  then have INV: "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" and EMPTY: "V \<inter> S = {}" by blast+
  from inv\<^sub>1E(1)[OF inv\<^sub>2E(1)[OF inv\<^sub>3E(1)[OF INV]]] and bin_packing_lower_bound_card[OF EMPTY inv\<^sub>3E(1)[OF INV]]
    show ?case by blast
qed

end (* BinPacking *)

subsection \<open>The Full Linear Time Version of the Proposed Algorithm\<close>

text \<open>Finally, we prove the Algorithm proposed on page 78 of the article @{cite BerghammerR03}.
      This version generates the S and L sets beforehand and uses them directly to calculate the solution,
      thus removing the need for intersection operations, and ensuring linear time if we can
      perform \<open>insertion, removal, and selection of an element, the union of two sets,
      and the emptiness test in constant time\<close> @{cite BerghammerR03}.\<close>

locale BinPacking_Complete =
  fixes U :: "'a set" \<comment> \<open>A finite, non-empty set of objects\<close>
    and w :: "'a \<Rightarrow> real" \<comment> \<open>A mapping from objects to their respective weights (positive real numbers)\<close>
    and c :: nat \<comment> \<open>The maximum capacity of a bin (as a natural number)\<close>
  assumes weight: "\<forall>u \<in> U. 0 < w(u) \<and> w(u) \<le> c"
      and U_Finite: "finite U"
      and U_NE: "U \<noteq> {}"
begin

text \<open>The correctness proofs will be identical to the ones of the simplified algorithm.\<close>

abbreviation W :: "'a set \<Rightarrow> real" where
  "W B \<equiv> (\<Sum>u \<in> B. w(u))"

definition bp :: "'a set set \<Rightarrow> bool" where
  "bp P \<longleftrightarrow> partition_on U P \<and> (\<forall>B \<in> P. W(B) \<le> c)"

lemma bpE:
  assumes "bp P"
  shows "pairwise disjnt P" "{} \<notin> P" "\<Union>P = U" "\<forall>B \<in> P. W(B) \<le> c"
  using assms unfolding bp_def partition_on_def by blast+

lemma bpI:
  assumes "pairwise disjnt P" "{} \<notin> P" "\<Union>P = U" "\<forall>B \<in> P. W(B) \<le> c"
  shows "bp P"
  using assms unfolding bp_def partition_on_def by blast

definition inv\<^sub>1 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V \<longleftrightarrow> bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}) \<comment> \<open>A correct solution to the bin packing problem\<close>
                       \<and> \<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V \<comment> \<open>The partial solution does not contain objects that have not yet been assigned\<close>
                       \<and> B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<comment> \<open>\<open>B\<^sub>1\<close> is distinct from all the other bins\<close>
                       \<and> B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2) \<comment> \<open>\<open>B\<^sub>2\<close> is distinct from all the other bins\<close>
                       \<and> (P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {} \<comment> \<open>The first and second partial solutions are disjoint from each other.\<close>"

lemma inv\<^sub>1E:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  shows "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})"
    and "\<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V"
    and "B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    and "B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2)"
    and "(P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
  using assms unfolding inv\<^sub>1_def by auto

lemma inv\<^sub>1I:
  assumes "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V})"
    and "\<Union>(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - V"
    and "B\<^sub>1 \<notin> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    and "B\<^sub>2 \<notin> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2)"
    and "(P\<^sub>1 \<union> wrap B\<^sub>1) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V"
  using assms unfolding inv\<^sub>1_def by blast

lemma wrap_Un [simp]: "wrap (M \<union> {x}) = {M \<union> {x}}" unfolding wrap_def by simp
lemma wrap_empty [simp]: "wrap {} = {}" unfolding wrap_def by simp
lemma wrap_not_empty [simp]: "M \<noteq> {} \<longleftrightarrow> wrap M = {M}" unfolding wrap_def by simp

lemma inv\<^sub>1_stepA:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V" "W(B\<^sub>1) + w(u) \<le> c"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

  \<comment> \<open>Rule 1: Pairwise Disjoint\<close>
  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "{{v} |v. v \<in> V} = {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    using assms(2) by blast
  then have "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> ({{u}} \<union> {{v} |v. v \<in> V - {u}}))"
    using bprules(1) assms(2) by simp
  then have "pairwise disjnt (wrap B\<^sub>1 \<union> {{u}} \<union> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})" by (simp add: Un_commute)
  then have assm: "pairwise disjnt (wrap B\<^sub>1 \<union> {{u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by (simp add: Un_assoc)
  have "pairwise disjnt ({B\<^sub>1 \<union> {u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
  proof (cases \<open>B\<^sub>1 = {}\<close>)
    case True with assm show ?thesis by simp
  next
    case False
    with assm have assm: "pairwise disjnt ({B\<^sub>1} \<union> {{u}} \<union> (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by simp
    from NOTIN have "{u} \<notin> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}" by blast
    from pairwise_disjnt_Un[OF assm _ this] invrules(2,3) show ?thesis
      using False by auto
  qed
  then have 1: "pairwise disjnt (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})"
    unfolding wrap_Un by simp

  \<comment> \<open>Rule 2: No empty sets\<close>
  from bprules(2) have 2: "{} \<notin> P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}"
    unfolding wrap_def by simp

  \<comment> \<open>Rule 3: Union preserved\<close>
  from bprules(3) have "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}) = U"
    using assms(2) by blast
  then have 3: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}) = U"
    unfolding wrap_def by force

  \<comment> \<open>Rule 4: Weights below capacity\<close>
  have "0 < w u" using weight assms(2) bprules(3) by blast
  have "finite B\<^sub>1" using bprules(3) U_Finite by (cases \<open>B\<^sub>1 = {}\<close>) auto
  then have "W (B\<^sub>1 \<union> {u}) \<le> W B\<^sub>1 + w u" using \<open>0 < w u\<close> by (cases \<open>u \<in> B\<^sub>1\<close>) (auto simp: insert_absorb)
  also have "... \<le> c" using assms(3) .
  finally have "W (B\<^sub>1 \<union> {u}) \<le> c" .
  then have "\<forall>B \<in> wrap (B\<^sub>1 \<union> {u}). W B \<le> c" unfolding wrap_Un by blast
  moreover have "\<forall>B\<in>P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    using bprules(4) by blast
  ultimately have 4: "\<forall>B\<in>P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c" by blast
  from bpI[OF 1 2 3 4] have 1: "bp (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}})" .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have "u \<in> U" using assms(2) bprules(3) by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2 \<union> wrap B\<^sub>2) = U - (V - {u})"
    unfolding L R invrules(2) ..
  have 3: "B\<^sub>1 \<union> {u} \<notin> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2"
    using NOTIN by auto
  have 4: "B\<^sub>2 \<notin> P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}) \<union> P\<^sub>2"
    using invrules(4) NOTIN unfolding wrap_def by fastforce
  have 5: "(P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u})) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}"
    using invrules(5) NOTIN unfolding wrap_Un by auto

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

lemma inv\<^sub>1_stepB:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V" "W B\<^sub>2 + w u \<le> c"
  shows "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "{{v} |v. v \<in> V} = {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    using assms(2) by blast
  then have "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}})"
    using bprules(1) assms(2) by simp
  then have assm: "pairwise disjnt (wrap B\<^sub>2 \<union> {{u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
    by (simp add: Un_assoc Un_commute)
  have "pairwise disjnt ({B\<^sub>2 \<union> {u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))"
  proof (cases \<open>B\<^sub>2 = {}\<close>)
    case True with assm show ?thesis by simp
  next
    case False
    with assm have assm: "pairwise disjnt ({B\<^sub>2} \<union> {{u}} \<union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}))" by simp
    from NOTIN have "{u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}" by blast
    from pairwise_disjnt_Un[OF assm _ this] invrules(2,4) show ?thesis
      using False by auto
  qed
  then have 1: "pairwise disjnt (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}})"
    unfolding wrap_Un by simp

  \<comment> \<open>Rule 2: No empty sets\<close>
  from bprules(2) have 2: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}"
    unfolding wrap_def by simp

  \<comment> \<open>Rule 3: Union preserved\<close>
  from bprules(3) have "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}) = U"
    using assms(2) by blast
  then have 3: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}) = U"
    unfolding wrap_def by force

  \<comment> \<open>Rule 4: Weights below capacity\<close>
  have "0 < w u" using weight assms(2) bprules(3) by blast
  have "finite B\<^sub>2" using bprules(3) U_Finite by (cases \<open>B\<^sub>2 = {}\<close>) auto
  then have "W (B\<^sub>2 \<union> {u}) \<le> W B\<^sub>2 + w u" using \<open>0 < w u\<close> by (cases \<open>u \<in> B\<^sub>2\<close>) (auto simp: insert_absorb)
  also have "... \<le> c" using assms(3) .
  finally have "W (B\<^sub>2 \<union> {u}) \<le> c" .
  then have "\<forall>B \<in> wrap (B\<^sub>2 \<union> {u}). W B \<le> c" unfolding wrap_Un by blast
  moreover have "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    using bprules(4) by blast
  ultimately have 4: "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}}. W B \<le> c"
    by auto
  from bpI[OF 1 2 3 4] have 1: "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}) \<union> {{v} |v. v \<in> V - {u}})" .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have "u \<in> U" using assms(2) bprules(3) by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap B\<^sub>2) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = U - (V - {u})"
    unfolding L R using invrules(2) by simp
  have 3: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})"
    using bpE(2)[OF 1] by simp
  have 4: "B\<^sub>2 \<union> {u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> P\<^sub>2"
    using NOTIN by auto
  have 5: "(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}) \<inter> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})) = {}"
    using invrules(5) NOTIN unfolding wrap_empty wrap_Un by auto

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

lemma inv\<^sub>1_stepC:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V" "u \<in> V"
  shows "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (V - {u})"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)]
  \<comment> \<open>Rule 1-4: Correct Bin Packing\<close>
  have "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}}
      = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}} \<union> {{v} |v. v \<in> V - {u}}"
    by (metis (no_types, lifting) Un_assoc Un_empty_right insert_not_empty wrap_empty wrap_not_empty)
  also have "... = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}"
    using assms(2) by auto
  finally have EQ: "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}}
                  = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V}" .
  from invrules(1) have 1: "bp (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u} \<union> {{v} |v. v \<in> V - {u}})"
    unfolding EQ .

  \<comment> \<open>Auxiliary information is preserved\<close>
  have NOTIN: "\<forall>M \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> V - {u}}. u \<notin> M"
    using invrules(2) assms(2) by blast
  have "u \<in> U" using assms(2) bpE(3)[OF invrules(1)] by blast
  then have R: "U - (V - {u}) = U - V \<union> {u}" by blast
  have L: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}) = \<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}"
    unfolding wrap_def using NOTIN by auto
  have 2: "\<Union> (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}) = U - (V - {u})"
    unfolding L R using invrules(2) by auto
  have 3: "{} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> (P\<^sub>2 \<union> wrap B\<^sub>2) \<union> wrap {u}"
    using bpE(2)[OF 1] by simp
  have 4: "{u} \<notin> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {} \<union> (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using NOTIN by auto
  have 5: "(P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}) \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}) = {}"
    using invrules(5) NOTIN unfolding wrap_def by force

  from inv\<^sub>1I[OF 1 2 3 4 5] show ?thesis .
qed

text \<open>From this point onward, we will require a different approach for proving lower bounds.
      Instead of fixing and assuming the definitions of the \<open>S\<close> and \<open>L\<close> sets, we will introduce
      the abbreviations \<open>S\<^sub>U\<close> and \<open>L\<^sub>U\<close> for any occurrences of the original \<open>S\<close> and \<open>L\<close> sets.
      The union of \<open>S\<close> and \<open>L\<close> can be interpreted as \<open>V\<close>. As a result, occurrences of \<open>V \<inter> S\<close>
      become \<open>(S \<union> L) \<inter> S = S\<close>, and \<open>V \<inter> L\<close> become \<open>(S \<union> L) \<inter> L = L\<close>.
      Occurrences of these sets will have to be replaced appropriately.\<close>
abbreviation S\<^sub>U where
  "S\<^sub>U \<equiv> {u \<in> U. w u \<le> c / 2}"

abbreviation L\<^sub>U where
  "L\<^sub>U \<equiv> {u \<in> U. c / 2 < w u}"

text \<open>As we will remove elements from \<open>S\<close> and \<open>L\<close>, we will only be able to show that they remain
      subsets of \<open>S\<^sub>U\<close> and \<open>L\<^sub>U\<close> respectively.\<close>
abbreviation SL where
  "SL S L \<equiv> S \<subseteq> S\<^sub>U \<and> L \<subseteq> L\<^sub>U"

lemma bp_bins_finite [simp]:
  assumes "bp P"
  shows "\<forall>B \<in> P. finite B"
  using bpE(3)[OF assms] U_Finite by (meson Sup_upper finite_subset)

lemma bp_sol_finite [simp]:
  assumes "bp P"
  shows "finite P"
  using bpE(3)[OF assms] U_Finite by (simp add: finite_UnionD)

lemma only_one_L_per_bin:
  assumes "bp P" "B \<in> P"
  shows "\<forall>x \<in> B. \<forall>y \<in> B. x \<noteq> y \<longrightarrow> x \<notin> L\<^sub>U \<or> y \<notin> L\<^sub>U"
proof (rule ccontr, simp)
  assume "\<exists>x\<in>B. \<exists>y\<in>B. x \<noteq> y \<and> y \<in> U \<and> x \<in> U \<and> real c < w x * 2 \<and> real c < w y * 2"
  then obtain x y where *: "x \<in> B" "y \<in> B" "x \<noteq> y" "x \<in> L\<^sub>U" "y \<in> L\<^sub>U" by auto
  then have "c < w x + w y" by force
  have "finite B" using assms by simp
  have "y \<in> B - {x}" using *(2,3) by blast
  have "W B = W (B - {x}) + w x"
    using *(1) \<open>finite B\<close> by (simp add: sum.remove)
  also have "... = W (B - {x} - {y}) + w x + w y"
    using \<open>y \<in> B - {x}\<close> \<open>finite B\<close> by (simp add: sum.remove)
  finally have *: "W B = W (B - {x} - {y}) + w x + w y" .
  have "\<forall>u \<in> B. 0 < w u" using bpE(3)[OF assms(1)] assms(2) weight by blast
  then have "0 \<le> W (B - {x} - {y})" by (smt DiffD1 sum_nonneg)
  with * have "c < W B" using \<open>c < w x + w y\<close> by simp
  then show False using bpE(4)[OF assms(1)] assms(2) by fastforce
qed

lemma L_lower_bound_card:
  assumes "bp P"
  shows "card L\<^sub>U \<le> card P"
proof -
  have "\<forall>x \<in> L\<^sub>U. \<exists>B \<in> P. x \<in> B"
    using bpE(3)[OF assms] by blast
  then obtain f where f_def: "\<forall>u \<in> L\<^sub>U. u \<in> f u \<and> f u \<in> P" by metis
  then have "inj_on f L\<^sub>U"
    unfolding inj_on_def using only_one_L_per_bin[OF assms] by blast
  then have card_eq: "card L\<^sub>U = card (f ` L\<^sub>U)" by (simp add: card_image)
  have "f ` L\<^sub>U \<subseteq> P" using f_def by blast
  moreover have "finite P" using assms by simp
  ultimately have "card (f ` L\<^sub>U) \<le> card P" by (simp add: card_mono)
  then show ?thesis unfolding card_eq .
qed

lemma subset_bp_card:
  assumes "bp P" "M \<subseteq> P" "\<forall>B \<in> M. B \<inter> L\<^sub>U \<noteq> {}"
  shows "card M \<le> card L\<^sub>U"
proof -
  have "\<forall>B \<in> M. \<exists>u \<in> L\<^sub>U. u \<in> B" using assms(3) by fast
  then have "\<exists>f. \<forall>B \<in> M. f B \<in> L\<^sub>U \<and> f B \<in> B" by metis
  then obtain f where f_def: "\<forall>B \<in> M. f B \<in> L\<^sub>U \<and> f B \<in> B" ..
  have "inj_on f M"
  proof (rule ccontr)
    assume "\<not> inj_on f M"
    then have "\<exists>x \<in> M. \<exists>y \<in> M. x \<noteq> y \<and> f x = f y" unfolding inj_on_def by blast
    then obtain x y where *: "x \<in> M" "y \<in> M" "x \<noteq> y" "f x = f y" by blast
    then have "\<exists>u. u \<in> x \<and> u \<in> y" using f_def by metis
    then have "x \<inter> y \<noteq> {}" by blast
    moreover have "pairwise disjnt M" using pairwise_subset[OF bpE(1)[OF assms(1)] assms(2)] .
    ultimately show False using * unfolding pairwise_def disjnt_def by simp
  qed
  moreover have "finite L\<^sub>U" using U_Finite by auto
  moreover have "f ` M \<subseteq> L\<^sub>U" using f_def by blast
  ultimately show ?thesis using card_inj_on_le by blast
qed

lemma L_bins_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)" "\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L\<^sub>U \<noteq> {}"
      and SL_def: "SL S L"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L}) \<le> card P"
proof -
  note invrules = inv\<^sub>1E[OF assms(2)]
  have "\<forall>B \<in> {{v} |v. v \<in> L}. B \<inter> L\<^sub>U \<noteq> {}" using SL_def by blast
  with assms(3) have
    "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L} \<subseteq> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L}"
    "\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L}. B \<inter> L\<^sub>U \<noteq> {}" by blast+
  from subset_bp_card[OF invrules(1) this] show ?thesis
    using L_lower_bound_card[OF assms(1)] by linarith
qed

lemma sum_Un_eq_sum_sum:
  assumes "bp P"
  shows "(\<Sum>u \<in> U. w u) = (\<Sum>B \<in> P. W B)"
proof -
  have FINITE: "\<forall>B \<in> P. finite B" using assms by simp
  have DISJNT: "\<forall>A \<in> P. \<forall>B \<in> P. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using bpE(1)[OF assms] unfolding pairwise_def disjnt_def .
  have "(\<Sum>u \<in> (\<Union>P). w u) = (\<Sum>B \<in> P. W B)"
    using sum.Union_disjoint[OF FINITE DISJNT] by auto
  then show ?thesis unfolding bpE(3)[OF assms] .
qed

lemma sum_lower_bound_card:
  assumes "bp P"
  shows "(\<Sum>u \<in> U. w u) \<le> c * card P"
proof -
  have *: "\<forall>B \<in> P. 0 < W B \<and> W B \<le> c"
    using bpE(2-4)[OF assms] weight by (metis UnionI assms bp_bins_finite sum_pos)
  have "(\<Sum>u \<in> U. w u) = (\<Sum>B \<in> P. W B)"
    using sum_Un_eq_sum_sum[OF assms] .
  also have "... \<le> (\<Sum>B \<in> P. c)" using sum_mono * by fastforce
  also have "... = c * card P" by simp
  finally show ?thesis .
qed

lemma bp_NE:
  assumes "bp P"
  shows "P \<noteq> {}"
  using U_NE bpE(3)[OF assms] by blast

lemma sum_Un_ge:
  fixes f :: "_ \<Rightarrow> real"
  assumes "finite M" "finite N" "\<forall>B \<in> M \<union> N. 0 < f B"
  shows "sum f M \<le> sum f (M \<union> N)"
proof -
  have "0 \<le> sum f N - sum f (M \<inter> N)"
    using assms by (smt DiffD1 inf.cobounded2 UnCI sum_mono2)
  then have "sum f M \<le> sum f M + sum f N - sum f (M \<inter> N)"
    by simp
  also have "... = sum f (M \<union> N)"
    using sum_Un[OF assms(1,2), symmetric] .
  finally show ?thesis .
qed

definition bij_exists :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "bij_exists P V = (\<exists>f. bij_betw f P V \<and> (\<forall>B \<in> P. W B + w (f B) > c))"

lemma P\<^sub>1_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "card P\<^sub>1 + 1 \<le> card P"
proof (cases \<open>P\<^sub>1 = {}\<close>)
  case True
  have "finite P" using assms(1) by simp
  then have "1 \<le> card P" using bp_NE[OF assms(1)]
    by (metis Nat.add_0_right Suc_diff_1 Suc_le_mono card_gt_0_iff le0 mult_Suc_right nat_mult_1)
  then show ?thesis unfolding True by simp
next
  note invrules = inv\<^sub>1E[OF assms(2)]
  case False
  obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B \<in> P\<^sub>1. W B + w (f B) > c"
    using assms(3) unfolding bij_exists_def by blast
  have FINITE: "finite P\<^sub>1" "finite (P\<^sub>2 \<union> wrap B\<^sub>2)" "finite (P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)" "finite (wrap B\<^sub>1 \<union> {{v} |v. v \<in> S \<union> L})"
    using inv\<^sub>1E(1)[OF assms(2)] bp_sol_finite by blast+

  have F: "\<forall>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. finite B" using invrules(1) by simp
  have D: "\<forall>A \<in> P\<^sub>2 \<union> wrap B\<^sub>2. \<forall>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using bpE(1)[OF invrules(1)] unfolding pairwise_def disjnt_def by auto
  have sum_eq: "W (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) = (\<Sum>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. W B)"
    using sum.Union_disjoint[OF F D] by auto

  have "\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L}. 0 < W B"
    using bpE(2,3)[OF invrules(1)] weight by (metis (no_types, lifting) UnionI bp_bins_finite invrules(1) sum_pos)
  then have "(\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B) \<le> (\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> (wrap B\<^sub>1 \<union> {{v} |v. v \<in> S \<union> L}). W B)"
    using sum_Un_ge[OF FINITE(3,4), of W] by blast
  also have "... = (\<Sum>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L}. W B)" by (smt Un_assoc Un_commute) 
  also have "... = W U" using sum_Un_eq_sum_sum[OF invrules(1), symmetric] .
  finally have *: "(\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B) \<le> W U" .
  have DISJNT: "P\<^sub>1 \<inter> (P\<^sub>2 \<union> wrap B\<^sub>2) = {}" using invrules(5) by blast

  \<comment> \<open>This part of the proof is based on the proof on page 72 of the article @{cite BerghammerR03}.\<close>
  have "c * card P\<^sub>1 = (\<Sum>B \<in> P\<^sub>1. c)" by simp
  also have "... < (\<Sum>B \<in> P\<^sub>1. W B + w (f B))"
    using f_def(2) sum_strict_mono[OF FINITE(1) False] by fastforce
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + (\<Sum>B \<in> P\<^sub>1. w (f B))"
    by (simp add: Groups_Big.comm_monoid_add_class.sum.distrib)
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + W (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" unfolding sum.reindex_bij_betw[OF f_def(1), of w] ..
  also have "... = (\<Sum>B \<in> P\<^sub>1. W B) + (\<Sum>B \<in> P\<^sub>2 \<union> wrap B\<^sub>2. W B)" unfolding sum_eq ..
  also have "... = (\<Sum>B \<in> P\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2. W B)" using sum.union_disjoint[OF FINITE(1,2) DISJNT, of W] by (simp add: Un_assoc)
  also have "... \<le> (\<Sum>u \<in> U. w u)" using * .
  also have "... \<le> c * card P" using sum_lower_bound_card[OF assms(1)] .
  finally show ?thesis by (meson discrete nat_mult_less_cancel_disj of_nat_less_imp_less)
qed

lemma P\<^sub>1_B\<^sub>1_lower_bound_card:
  assumes "bp P" "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1) \<le> card P"
proof -
  have "card (P\<^sub>1 \<union> wrap B\<^sub>1) \<le> card P\<^sub>1 + card (wrap B\<^sub>1)"
    using card_Un_le by blast
  also have "... \<le> card P\<^sub>1 + 1" using wrap_card by simp
  also have "... \<le> card P" using P\<^sub>1_lower_bound_card[OF assms] .
  finally show ?thesis .
qed

lemma P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)" "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)" "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
  shows "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> card P\<^sub>1 + 1"
proof -
  note invrules = inv\<^sub>1E[OF assms(1)] and bprules = bpE[OF invrules(1)]

  have "pairwise disjnt (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using bprules(1) pairwise_subset by blast
  moreover have "B\<^sub>2 \<notin> P\<^sub>2" using invrules(4) by simp
  ultimately have DISJNT: "\<Union>P\<^sub>2 \<inter> B\<^sub>2 = {}"
    by (auto, metis (no_types, hide_lams) sup_bot.right_neutral Un_insert_right disjnt_iff mk_disjoint_insert pairwise_insert wrap_Un)

  have "finite (\<Union>P\<^sub>2)" using U_Finite bprules(3) by auto
  have "finite B\<^sub>2" using bp_bins_finite[OF invrules(1)] wrap_not_empty by blast
  have "finite P\<^sub>2" "finite (wrap B\<^sub>2)" using bp_sol_finite[OF invrules(1)] by blast+
  have DISJNT2: "P\<^sub>2 \<inter> wrap B\<^sub>2 = {}" unfolding wrap_def using \<open>B\<^sub>2 \<notin> P\<^sub>2\<close> by auto
  have "card (wrap B\<^sub>2) \<le> card B\<^sub>2"
  proof (cases \<open>B\<^sub>2 = {}\<close>)
    case False
    then have "1 \<le> card B\<^sub>2" by (simp add: leI \<open>finite B\<^sub>2\<close>)
    then show ?thesis using wrap_card[of B\<^sub>2] by linarith
  qed simp

  \<comment> \<open>This part of the proof is based on the proof on page 73 of the article @{cite BerghammerR03}.\<close>
  from assms(2) have "2 * card P\<^sub>2 + 2 * card (wrap B\<^sub>2) \<le> card (\<Union>P\<^sub>2) + card (wrap B\<^sub>2) + 1"
    using wrap_card[of B\<^sub>2] by linarith
  then have "2 * (card P\<^sub>2 + card (wrap B\<^sub>2)) \<le> card (\<Union>P\<^sub>2) + card B\<^sub>2 + 1"
    using \<open>card (wrap B\<^sub>2) \<le> card B\<^sub>2\<close> by simp
  then have "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card (\<Union>P\<^sub>2 \<union> B\<^sub>2) + 1"
    using card_Un_disjoint[OF \<open>finite (\<Union>P\<^sub>2)\<close> \<open>finite B\<^sub>2\<close> DISJNT]
      and card_Un_disjoint[OF \<open>finite P\<^sub>2\<close> \<open>finite (wrap B\<^sub>2)\<close> DISJNT2] by argo
  then have "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2)) + 1"
    by (cases \<open>B\<^sub>2 = {}\<close>) (auto simp: Un_commute)
  then show "2 * (card (P\<^sub>2 \<union> wrap B\<^sub>2)) \<le> card P\<^sub>1 + 1"
    using assms(3) bij_betw_same_card unfolding bij_exists_def by metis
qed

text \<open>We add \<open>SL S L\<close> to \<open>inv\<^sub>2\<close> to ensure that the \<open>S\<close> and \<open>L\<close> sets only contain objects with correct weights.\<close>
definition inv\<^sub>2 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L \<longleftrightarrow> inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L) \<comment> \<open>\<open>inv\<^sub>1\<close> holds for the partial solution\<close>
                       \<and> (L \<noteq> {} \<longrightarrow> (\<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L\<^sub>U \<noteq> {})) \<comment> \<open>If there are still large objects left, then every bin of the first partial solution must contain a large object\<close>
                       \<and> bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2)) \<comment> \<open>There exists a bijective function between the bins of the first partial solution and the objects of the second one\<close>
                       \<and> (2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)) \<comment> \<open>There are at most twice as many bins in \<open>P\<^sub>2\<close> as there are objects in \<open>P\<^sub>2\<close>\<close>
                       \<and> SL S L \<comment> \<open>\<open>S\<close> and \<open>L\<close> are subsets of \<open>S\<^sub>U\<close> and \<open>L\<^sub>U\<close>\<close>"

lemma inv\<^sub>2E:
  assumes "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L"
  shows "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)"
    and "L \<noteq> {} \<Longrightarrow> \<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L\<^sub>U \<noteq> {}"
    and "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
    and "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)"
    and "SL S L"
  using assms unfolding inv\<^sub>2_def by blast+

lemma inv\<^sub>2I:
  assumes "inv\<^sub>1 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 (S \<union> L)"
    and "L \<noteq> {} \<Longrightarrow> \<forall>B \<in> P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L\<^sub>U \<noteq> {}"
    and "bij_exists P\<^sub>1 (\<Union>(P\<^sub>2 \<union> wrap B\<^sub>2))"
    and "2 * card P\<^sub>2 \<le> card (\<Union>P\<^sub>2)"
    and "SL S L"
  shows "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L"
  using assms unfolding inv\<^sub>2_def by blast

lemma bin_packing_lower_bound_card:
  assumes "S = {}" "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "bp P"
  shows "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L}) \<le> 3 / 2 * card P"
proof (cases \<open>L = {}\<close>)
  note invrules = inv\<^sub>2E[OF assms(2)]
  case True
  then have "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L})
           = card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2)" using assms(1) by simp
  also have "... \<le> card (P\<^sub>1 \<union> wrap B\<^sub>1) + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using card_Un_le[of \<open>P\<^sub>1 \<union> wrap B\<^sub>1\<close>] by (simp add: Un_assoc)
  also have "... \<le> card P + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using P\<^sub>1_B\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by simp
  also have "... \<le> card P + card P / 2"
    using P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1[OF invrules(1,4,3)]
      and P\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by linarith
  finally show ?thesis by linarith
next
  note invrules = inv\<^sub>2E[OF assms(2)]
  case False
  have "card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> S \<union> L})
      = card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L} \<union> P\<^sub>2 \<union> wrap B\<^sub>2)"
    using assms(1) by (simp add: Un_commute Un_assoc)
  also have "... \<le> card (P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L}) + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using card_Un_le[of \<open>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> {{v} |v. v \<in> L}\<close>] by (simp add: Un_assoc)
  also have "... \<le> card P + card (P\<^sub>2 \<union> wrap B\<^sub>2)"
    using L_bins_lower_bound_card[OF assms(3) invrules(1) invrules(2)[OF False] invrules(5)] by linarith
  also have "... \<le> card P + card P / 2"
    using P\<^sub>2_B\<^sub>2_lower_bound_P\<^sub>1[OF invrules(1,4,3)]
      and P\<^sub>1_lower_bound_card[OF assms(3) invrules(1,3)] by linarith
  finally show ?thesis by linarith
qed

definition inv\<^sub>3 :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L \<longleftrightarrow> inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L \<and> B\<^sub>2 \<subseteq> S\<^sub>U"

lemma inv\<^sub>3E:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L"
  shows "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" and "B\<^sub>2 \<subseteq> S\<^sub>U"
  using assms unfolding inv\<^sub>3_def by blast+

lemma inv\<^sub>3I:
  assumes "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" and "B\<^sub>2 \<subseteq> S\<^sub>U"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L"
  using assms unfolding inv\<^sub>3_def by blast

lemma loop_init:
  "inv\<^sub>3 {} {} {} {} S\<^sub>U L\<^sub>U"
proof -
  have "S\<^sub>U \<union> L\<^sub>U = U" by auto
  then have *: "inv\<^sub>1 {} {} {} {} (S\<^sub>U \<union> L\<^sub>U)"
    unfolding bp_def partition_on_def pairwise_def wrap_def inv\<^sub>1_def
    using weight by auto
  have "bij_exists {} (\<Union> ({} \<union> wrap {}))"
    using bij_betwI' unfolding bij_exists_def by fastforce
  from inv\<^sub>2I[OF * _ this] have "inv\<^sub>2 {} {} {} {} S\<^sub>U L\<^sub>U" by auto
  from inv\<^sub>3I[OF this] show ?thesis by blast
qed

lemma loop_stepA:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "B\<^sub>1 = {}" "L = {}" "u \<in> S"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (S - {u}) L"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have WEIGHT: "W B\<^sub>1 + w u \<le> c" using invrules(5) assms(2,4) by fastforce
  from assms(4) have "u \<in> S \<union> L" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this WEIGHT] assms(2,3) have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (S - {u} \<union> L)" by simp
  have 2: "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap {u}. B \<inter> L\<^sub>U \<noteq> {}" using assms(3) by blast
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (S - {u}) L" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

lemma loop_stepB:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "B\<^sub>1 = {}" "u \<in> L"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 S (L - {u})"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have WEIGHT: "W B\<^sub>1 + w u \<le> c" using weight invrules(5) assms(2,3) by fastforce

  \<comment> \<open>This observation follows from the fact that the \<open>S\<close> and \<open>L\<close> sets have to be disjoint from each other,
      and allows us to reuse our proofs of the preservation of \<open>inv\<^sub>1\<close> by simply replacing \<open>V\<close> with \<open>S \<union> L\<close>\<close>
  have *: "S \<union> L - {u} = S \<union> (L - {u})" using invrules(5) assms(3) by force
  from assms(3) have "u \<in> S \<union> L" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this WEIGHT] assms(2) * have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 (S \<union> (L - {u}))" by simp
  have "\<forall>B\<in>P\<^sub>1. B \<inter> L\<^sub>U \<noteq> {}" "{u} \<inter> L\<^sub>U \<noteq> {}" using assms(3) invrules(2,5) by blast+
  then have 2: "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap {u}. B \<inter> L\<^sub>U \<noteq> {}"
    using assms(3) by (metis (full_types) Un_iff empty_iff insert_iff wrap_not_empty)
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 {u} B\<^sub>2 S (L - {u})" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

lemma loop_stepC:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "B\<^sub>1 \<noteq> {}" "u \<in> S" "W B\<^sub>1 + w(u) \<le> c"
  shows "inv\<^sub>3 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (S - {u}) L"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]

  \<comment> \<open>Same approach, but removing \<open>{u}\<close> from \<open>S\<close> instead of \<open>L\<close>\<close>
  have *: "S \<union> L - {u} = (S - {u}) \<union> L" using invrules(5) assms(3) by force
  from assms(3) have "u \<in> S \<union> L" by blast
  from inv\<^sub>1_stepA[OF invrules(1) this assms(4)] * have 1: "inv\<^sub>1 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (S - {u} \<union> L)" by simp
  have "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. B \<inter> L\<^sub>U \<noteq> {}" using invrules(2) by blast
  then have 2: "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap (B\<^sub>1 \<union> {u}). B \<inter> L\<^sub>U \<noteq> {}"
    by (smt Int_insert_left Un_empty_right Un_iff Un_insert_right assms(2) insert_not_empty singletonD singletonI wrap_def)
  from inv\<^sub>2I[OF 1 2] invrules have "inv\<^sub>2 P\<^sub>1 P\<^sub>2 (B\<^sub>1 \<union> {u}) B\<^sub>2 (S - {u}) L" by blast
  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] .
qed

lemma loop_stepD:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "B\<^sub>1 \<noteq> {}" "u \<in> S" "W B\<^sub>1 + w(u) > c" "W B\<^sub>2 + w(u) \<le> c"
  shows "inv\<^sub>3 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (S - {u}) L"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have *: "S \<union> L - {u} = (S - {u}) \<union> L" using invrules(5) assms(3) by force
  from assms(3) have "u \<in> S \<union> L" by blast
  from inv\<^sub>1_stepB[OF invrules(1) this assms(5)] * have 1: "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (S - {u} \<union> L)" by simp

  have 2: "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}. B \<inter> L\<^sub>U \<noteq> {}"
    using invrules(2) unfolding wrap_empty by blast

  from invrules(3) obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B\<in>P\<^sub>1. c < W B + w (f B)" unfolding bij_exists_def by blast
  have "B\<^sub>1 \<notin> P\<^sub>1" using inv\<^sub>1E(3)[OF invrules(1)] by blast
  have "u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" using inv\<^sub>1E(2)[OF invrules(1)] assms(3) by blast
  then have "(\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}))) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}}))"
    by (metis Sup_empty Un_assoc Union_Un_distrib ccpo_Sup_singleton wrap_empty wrap_not_empty)
  also have "... = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" by simp
  finally have UN: "(\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u}))) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" .
  have "wrap B\<^sub>1 = {B\<^sub>1}" using wrap_not_empty[of B\<^sub>1] assms(2) by simp
  let ?f = "f (B\<^sub>1 := u)"
  have BIJ: "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))"
    unfolding wrap_empty \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> UN using f_def(1) \<open>B\<^sub>1 \<notin> P\<^sub>1\<close> \<open>u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))\<close>
    by (metis (no_types, lifting) bij_betw_cong fun_upd_other fun_upd_same notIn_Un_bij_betw3)
  have "c < W B\<^sub>1 + w (?f B\<^sub>1)" using assms(4) by simp
  then have "(\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))"
    unfolding \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> using f_def(2) by simp
  with BIJ have "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))
              \<and> (\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))" by blast
  then have 3: "bij_exists (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap (B\<^sub>2 \<union> {u})))"
    unfolding bij_exists_def by blast
  from inv\<^sub>2I[OF 1 2 3] have "inv\<^sub>2 (P\<^sub>1 \<union> wrap B\<^sub>1) P\<^sub>2 {} (B\<^sub>2 \<union> {u}) (S - {u}) L" using invrules(4,5) by blast

  from inv\<^sub>3I[OF this] show ?thesis using inv\<^sub>3E(2)[OF assms(1)] assms(3) invrules(5) by blast
qed

lemma B\<^sub>2_at_least_two_objects:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "u \<in> S" "W B\<^sub>2 + w(u) > c"
  shows "2 \<le> card B\<^sub>2"
proof (rule ccontr, simp add: not_le)
  have FINITE: "finite B\<^sub>2" using inv\<^sub>1E(1)[OF inv\<^sub>2E(1)[OF inv\<^sub>3E(1)[OF assms(1)]]]
    by (metis (no_types, lifting) Finite_Set.finite.simps U_Finite Union_Un_distrib bpE(3) ccpo_Sup_singleton finite_Un wrap_not_empty)
  assume "card B\<^sub>2 < 2"
  then consider (0) "card B\<^sub>2 = 0" | (1) "card B\<^sub>2 = 1" by linarith
  then show False proof cases
    case 0 then have "B\<^sub>2 = {}" using FINITE by simp
    then show ?thesis using assms(2,3) inv\<^sub>2E(5)[OF inv\<^sub>3E(1)[OF assms(1)]] by force
  next
    case 1 then obtain v where "B\<^sub>2 = {v}"
      using card_1_singletonE by auto
    with inv\<^sub>3E(2)[OF assms(1)] have "2 * w v \<le> c" using inv\<^sub>2E(5)[OF inv\<^sub>3E(1)[OF assms(1)]] by simp
    moreover from \<open>B\<^sub>2 = {v}\<close> have "W B\<^sub>2 = w v" by simp
    ultimately show ?thesis using assms(2,3) inv\<^sub>2E(5)[OF inv\<^sub>3E(1)[OF assms(1)]] by force
  qed
qed

lemma loop_stepE:
  assumes "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" "B\<^sub>1 \<noteq> {}" "u \<in> S" "W B\<^sub>1 + w(u) > c" "W B\<^sub>2 + w(u) > c"
  shows "inv\<^sub>3 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (S - {u}) L"
proof -
  note invrules = inv\<^sub>2E[OF inv\<^sub>3E(1)[OF assms(1)]]
  have *: "S \<union> L - {u} = (S - {u}) \<union> L" using invrules(5) assms(3) by force
  from assms(3) have "u \<in> S \<union> L" by blast
  from inv\<^sub>1_stepC[OF invrules(1) this] * have 1: "inv\<^sub>1 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (S - {u} \<union> L)" by simp

  have 2: "L \<noteq> {} \<Longrightarrow> \<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1 \<union> wrap {}. B \<inter> L\<^sub>U \<noteq> {}"
    using invrules(2) unfolding wrap_empty by blast

  from invrules(3) obtain f where f_def: "bij_betw f P\<^sub>1 (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" "\<forall>B\<in>P\<^sub>1. c < W B + w (f B)" unfolding bij_exists_def by blast
  have "B\<^sub>1 \<notin> P\<^sub>1" using inv\<^sub>1E(3)[OF invrules(1)] by blast
  have "u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" using inv\<^sub>1E(2)[OF invrules(1)] assms(3) by blast
  have "(\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u})) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{u}}))" unfolding wrap_def by simp
  also have "... = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" by simp
  finally have UN: "(\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u})) = (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2)) \<union> {u}" .
  have "wrap B\<^sub>1 = {B\<^sub>1}" using wrap_not_empty[of B\<^sub>1] assms(2) by simp
  let ?f = "f (B\<^sub>1 := u)"
  have BIJ: "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))"
    unfolding wrap_empty \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> UN using f_def(1) \<open>B\<^sub>1 \<notin> P\<^sub>1\<close> \<open>u \<notin> (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))\<close>
    by (metis (no_types, lifting) bij_betw_cong fun_upd_other fun_upd_same notIn_Un_bij_betw3)
  have "c < W B\<^sub>1 + w (?f B\<^sub>1)" using assms(4) by simp
  then have "(\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))"
    unfolding \<open>wrap B\<^sub>1 = {B\<^sub>1}\<close> using f_def(2) by simp
  with BIJ have "bij_betw ?f (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))
              \<and> (\<forall>B\<in>P\<^sub>1 \<union> wrap B\<^sub>1. c < W B + w (?f B))" by blast
  then have 3: "bij_exists (P\<^sub>1 \<union> wrap B\<^sub>1) (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2 \<union> wrap {u}))"
    unfolding bij_exists_def by blast

  have 4: "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> card (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))"
  proof -
    note bprules = bpE[OF inv\<^sub>1E(1)[OF invrules(1)]]
    have "pairwise disjnt (P\<^sub>2 \<union> wrap B\<^sub>2)"
      using bprules(1) pairwise_subset by blast
    moreover have "B\<^sub>2 \<notin> P\<^sub>2" using inv\<^sub>1E(4)[OF invrules(1)]  by simp
    ultimately have DISJNT: "\<Union>P\<^sub>2 \<inter> B\<^sub>2 = {}"
      by (auto, metis (no_types, hide_lams) sup_bot.right_neutral Un_insert_right disjnt_iff mk_disjoint_insert pairwise_insert wrap_Un)
    have "finite (\<Union>P\<^sub>2)" using U_Finite bprules(3) by auto
    have "finite B\<^sub>2" using inv\<^sub>1E(1)[OF invrules(1)] bp_bins_finite wrap_not_empty by blast

    have "2 * card (P\<^sub>2 \<union> wrap B\<^sub>2) \<le> 2 * (card P\<^sub>2 + card (wrap B\<^sub>2))"
      using card_Un_le[of P\<^sub>2 \<open>wrap B\<^sub>2\<close>] by simp
    also have "... \<le> 2 * card P\<^sub>2 + 2" using wrap_card by auto
    also have "... \<le> card (\<Union> P\<^sub>2) + 2" using invrules(4) by simp
    also have "... \<le> card (\<Union> P\<^sub>2) + card B\<^sub>2" using B\<^sub>2_at_least_two_objects[OF assms(1,3,5)] by simp
    also have "... = card (\<Union> (P\<^sub>2 \<union> {B\<^sub>2}))" using DISJNT card_Un_disjoint[OF \<open>finite (\<Union>P\<^sub>2)\<close> \<open>finite B\<^sub>2\<close>] by (simp add: Un_commute)
    also have "... = card (\<Union> (P\<^sub>2 \<union> wrap B\<^sub>2))" by (cases \<open>B\<^sub>2 = {}\<close>) auto
    finally show ?thesis .
  qed
  from inv\<^sub>2I[OF 1 2 3 4] have "inv\<^sub>2 (P\<^sub>1 \<union> wrap B\<^sub>1) (P\<^sub>2 \<union> wrap B\<^sub>2) {} {u} (S - {u}) L"
    using invrules(5) by blast

  from inv\<^sub>3I[OF this] show ?thesis using assms(3) invrules(5) by blast
qed

text \<open>The bin packing algorithm as it is proposed on page 78 of the article @{cite BerghammerR03}.
      \<open>P\<close> will not only be a correct solution of the bin packing problem, but the amount of bins
      will be a lower bound for \<open>3 / 2\<close> of the amount of bins of any correct solution \<open>Q\<close>, and thus
      guarantee an approximation factor of \<open>3 / 2\<close> for the optimum.\<close>
lemma bp_approx:
"VARS P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u
  {True}
  S := {}; L:= {}; V := U;
  WHILE V \<noteq> {} INV {V \<subseteq> U \<and> S = {u \<in> U - V. w(u) \<le> c / 2} \<and> L = {u \<in> U - V. c / 2 < w(u)}} DO
    u := (SOME u. u \<in> V);
    IF w(u) \<le> c / 2
    THEN S := S \<union> {u}
    ELSE L := L \<union> {u} FI;
    V := V - {u}
  OD;
  P\<^sub>1 := {}; P\<^sub>2 := {}; B\<^sub>1 := {}; B\<^sub>2 := {};
  WHILE S \<noteq> {} INV {inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L} DO 
    IF B\<^sub>1 \<noteq> {}
    THEN u := (SOME u. u \<in> S); S := S - {u}
    ELSE IF L \<noteq> {}
         THEN u := (SOME u. u \<in> L); L := L - {u}
         ELSE u := (SOME u. u \<in> S); S := S - {u} FI FI;
    IF W(B\<^sub>1) + w(u) \<le> c
    THEN B\<^sub>1 := B\<^sub>1 \<union> {u}
    ELSE IF W(B\<^sub>2) + w(u) \<le> c
         THEN B\<^sub>2 := B\<^sub>2 \<union> {u}
         ELSE P\<^sub>2 := P\<^sub>2 \<union> wrap B\<^sub>2; B\<^sub>2 := {u} FI;
         P\<^sub>1 := P\<^sub>1 \<union> wrap B\<^sub>1; B\<^sub>1 := {} FI
  OD;
  P := P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2; V := L;
  WHILE V \<noteq> {}
  INV {S = {} \<and> inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L \<and> V \<subseteq> L \<and> P = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v}|v. v \<in> L - V}} DO
    u := (SOME u. u \<in> V); P := P \<union> {{u}}; V := V - {u}
  OD
  {bp P \<and> (\<forall>Q. bp Q \<longrightarrow> card P \<le> 3 / 2 * card Q)}"
proof (vcg, goal_cases)
  case (1 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then show ?case by blast
next
  case (2 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then show ?case by (auto simp: some_in_eq)
next
  case (3 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then show ?case using loop_init by force
next
  case (4 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then have INV: "inv\<^sub>3 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L" ..
  let ?s = "SOME u. u \<in> S"
  let ?l = "SOME u. u \<in> L"
  note SL_def = inv\<^sub>2E(5)[OF inv\<^sub>3E(1)[OF INV]]
  have LIN: "L \<noteq> {} \<Longrightarrow> ?l \<in> L" using some_in_eq by metis
  then have LWEIGHT: "L \<noteq> {} \<Longrightarrow> w ?l \<le> c" using weight SL_def by blast
  from 4 have "S \<noteq> {}" ..
  then have IN: "?s \<in> S" using some_in_eq by metis
  then have "w ?s \<le> c" using SL_def by auto
  then show ?case
    using LWEIGHT loop_stepA[OF INV _ _ IN] loop_stepB[OF INV _ LIN] loop_stepC[OF INV _ IN]
      and loop_stepD[OF INV _ IN] loop_stepE[OF INV _ IN] by (cases \<open>B\<^sub>1 = {}\<close>, cases \<open>L = {}\<close>) auto
next
  case (5 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then show ?case by blast
next
  case (6 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then have *: "(SOME u. u \<in> V) \<in> V" "(SOME u. u \<in> V) \<in> L" by (auto simp add: some_in_eq)
  then have "P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> L - (V - {SOME u. u \<in> V})}
           = P\<^sub>1 \<union> wrap B\<^sub>1 \<union> P\<^sub>2 \<union> wrap B\<^sub>2 \<union> {{v} |v. v \<in> L - V \<union> {SOME u. u \<in> V}}"
    by blast
  with 6 * show ?case by blast
next
  case (7 P P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 V S L u)
  then have *: "inv\<^sub>2 P\<^sub>1 P\<^sub>2 B\<^sub>1 B\<^sub>2 S L"
    using inv\<^sub>3E(1) by blast
  from inv\<^sub>1E(1)[OF inv\<^sub>2E(1)[OF *]] 7
  have "bp P" by fastforce
  with bin_packing_lower_bound_card[OF _ *] 7
  show ?case by fastforce
qed

end (* BinPacking_Complete *)

end (* Theory *)