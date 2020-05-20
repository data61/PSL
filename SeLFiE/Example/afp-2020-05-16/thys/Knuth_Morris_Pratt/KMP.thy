theory KMP
  imports Refine_Imperative_HOL.IICF
    "HOL-Library.Sublist"
begin

declare len_greater_imp_nonempty[simp del] min_absorb2[simp]
no_notation Ref.update ("_ := _" 62)

section\<open>Specification\<close>text_raw\<open>\label{sec:spec}\<close>

subsection\<open>Sublist-predicate with a position check\<close>

subsubsection\<open>Definition\<close>

text \<open>One could define\<close>
definition "sublist_at' xs ys i \<equiv> take (length xs) (drop i ys) = xs"  

text\<open>However, this doesn't handle out-of-bound indexes uniformly:\<close>
value[nbe] "sublist_at' [] [a] 5"
value[nbe] "sublist_at' [a] [a] 5"
value[nbe] "sublist_at' [] [] 5"

text\<open>Instead, we use a recursive definition:\<close>
fun sublist_at :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> bool" where
  "sublist_at (x#xs) (y#ys) 0 \<longleftrightarrow> x=y \<and> sublist_at xs ys 0" |
  "sublist_at xs (y#ys) (Suc i) \<longleftrightarrow> sublist_at xs ys i" |
  "sublist_at [] ys 0 \<longleftrightarrow> True" |
  "sublist_at _ [] _ \<longleftrightarrow> False"

text\<open>In the relevant cases, both definitions agree:\<close>
lemma "i \<le> length ys \<Longrightarrow> sublist_at xs ys i \<longleftrightarrow> sublist_at' xs ys i"
  unfolding sublist_at'_def
  by (induction xs ys i rule: sublist_at.induct) auto

text\<open>However, the new definition has some reasonable properties:\<close>
subsubsection\<open>Properties\<close>
lemma sublist_lengths: "sublist_at xs ys i \<Longrightarrow> i + length xs \<le> length ys"
  by (induction xs ys i rule: sublist_at.induct) auto

lemma Nil_is_sublist: "sublist_at ([] :: 'x list) ys i \<longleftrightarrow> i \<le> length ys"
  by (induction "[] :: 'x list" ys i rule: sublist_at.induct) auto

text\<open>Furthermore, we need:\<close>
lemma sublist_step[intro]:
  "\<lbrakk>i + length xs < length ys; sublist_at xs ys i; ys!(i + length xs) = x\<rbrakk> \<Longrightarrow> sublist_at (xs@[x]) ys i"
  apply (induction xs ys i rule: sublist_at.induct)
      apply auto
  using sublist_at.elims(3) by fastforce

lemma all_positions_sublist:
"\<lbrakk>i + length xs \<le> length ys; \<forall>jj<length xs. ys!(i+jj) = xs!jj\<rbrakk> \<Longrightarrow> sublist_at xs ys i"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: Nil_is_sublist)
next
  case (snoc x xs)
  from \<open>i + length (xs @ [x]) \<le> length ys\<close> have "i + length xs \<le> length ys" by simp
  moreover have "\<forall>jj<length xs. ys!(i + jj) = xs!jj"
    by (simp add: nth_append snoc.prems(2))
  ultimately have "sublist_at xs ys i"
    using snoc.IH by simp
  then show ?case
    using snoc.prems by auto
qed

lemma sublist_all_positions: "sublist_at xs ys i \<Longrightarrow> \<forall>jj<length xs. ys!(i+jj) = xs!jj"
  by (induction xs ys i rule: sublist_at.induct) (auto simp: nth_Cons')

text\<open>It also connects well to theory @{theory "HOL-Library.Sublist"} (compare @{thm[source] sublist_def}):\<close>
lemma sublist_at_altdef:
  "sublist_at xs ys i \<longleftrightarrow> (\<exists>ps ss. ys = ps@xs@ss \<and> i = length ps)"
proof (induction xs ys i rule: sublist_at.induct)
  case (2 ss t ts i)
  show "sublist_at ss (t#ts) (Suc i) \<longleftrightarrow> (\<exists>xs ys. t#ts = xs@ss@ys \<and> Suc i = length xs)"
    (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then have "sublist_at ss ts i" by simp
    with "2.IH" obtain xs where "\<exists>ys. ts = xs@ss@ys \<and> i = length xs" by auto
    then have "\<exists>ys. t#ts = (t#xs)@ss@ys \<and> Suc i = length (t#xs)" by simp
    then show ?rhs by blast
  next
    assume ?rhs
    then obtain xs where "\<exists>ys. t#ts = xs@ss@ys \<and> Suc i = length xs" by blast
    then have "\<exists>ys. ts = (tl xs)@ss@ys \<and> i = length (tl xs)"
      by (metis hd_Cons_tl length_0_conv list.sel(3) nat.simps(3) size_Cons_lem_eq tl_append2)
    then have "\<exists>xs ys. ts = xs@ss@ys \<and> i = length xs" by blast
    with "2.IH" show ?lhs by simp
  qed
qed auto

corollary sublist_iff_sublist_at: "Sublist.sublist xs ys \<longleftrightarrow> (\<exists>i. sublist_at xs ys i)"
  by (simp add: sublist_at_altdef Sublist.sublist_def)

subsection\<open>Sublist-check algorithms\<close>

text\<open>
  We use the Isabelle Refinement Framework (Theory @{theory Refine_Monadic.Refine_Monadic}) to
  phrase the specification and the algorithm. 
\<close>
text\<open>@{term s} for "searchword" / "searchlist", @{term t} for "text"\<close>
definition "kmp_SPEC s t = SPEC (\<lambda>
  None \<Rightarrow> \<nexists>i. sublist_at s t i |
  Some i \<Rightarrow> sublist_at s t i \<and> (\<forall>ii<i. \<not>sublist_at s t ii))"

lemma is_arg_min_id: "is_arg_min id P i \<longleftrightarrow> P i \<and> (\<forall>ii<i. \<not>P ii)"
  unfolding is_arg_min_def by auto

lemma kmp_result: "kmp_SPEC s t =
  RETURN (if sublist s t then Some (LEAST i. sublist_at s t i) else None)"
  unfolding kmp_SPEC_def sublist_iff_sublist_at
  apply (auto intro: LeastI dest: not_less_Least split: option.splits)
  by (meson LeastI nat_neq_iff not_less_Least)

corollary weak_kmp_SPEC: "kmp_SPEC s t \<le> SPEC (\<lambda>pos. pos\<noteq>None \<longleftrightarrow> Sublist.sublist s t)"
  by (simp add: kmp_result)

lemmas kmp_SPEC_altdefs =
  kmp_SPEC_def[folded is_arg_min_id]
  kmp_SPEC_def[folded sublist_iff_sublist_at]
  kmp_result

section\<open>Naive algorithm\<close>

text\<open>Since KMP is a direct advancement of the naive "test-all-starting-positions" approach, we provide it here for comparison:\<close>

subsection\<open>Invariants\<close>
definition "I_out_na s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> j = 0
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
definition "I_in_na s t i \<equiv> \<lambda>(j,pos).
  case pos of None \<Rightarrow> j < length s \<and> (\<forall>jj<j. t!(i+jj) = s!(jj))
    | Some p \<Rightarrow> sublist_at s t i"

subsection\<open>Algorithm\<close>

(*Algorithm is common knowledge \<longrightarrow> remove citation here, move explanations to KMP below?*)
text\<open>The following definition is taken from Helmut Seidl's lecture on algorithms and data structures@{cite GAD} except that we
\<^item> output the identified position @{term \<open>pos :: nat option\<close>} instead of just @{const True}
\<^item> use @{term \<open>pos :: nat option\<close>} as break-flag to support the abort within the loops
\<^item> rewrite @{prop \<open>i \<le> length t - length s\<close>} in the first while-condition to @{prop \<open>i + length s \<le> length t\<close>} to avoid having to use @{typ int} for list indexes (or the additional precondition @{prop \<open>length s \<le> length t\<close>})
\<close>

definition "naive_algorithm s t \<equiv> do {
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_out_na s t) (\<lambda>(i,_,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    (_,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,_). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      let i = i + 1;
      let j = 0;
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

subsection\<open>Correctness\<close>

text\<open>The basic lemmas on @{const sublist_at} from the previous chapter together with @{theory Refine_Monadic.Refine_Monadic}'s verification condition generator / solver suffice:\<close>

lemma "s \<noteq> [] \<Longrightarrow> naive_algorithm s t \<le> kmp_SPEC s t"
  unfolding naive_algorithm_def kmp_SPEC_def I_out_na_def I_in_na_def
  apply (refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
    WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
    )
                 apply (vc_solve solve: asm_rl)
  subgoal by (metis add_Suc_right all_positions_sublist less_antisym)
  subgoal using less_Suc_eq by blast
  subgoal by (metis less_SucE sublist_all_positions)
  subgoal by (auto split: option.splits) (metis sublist_lengths add_less_cancel_right leI le_less_trans)
  done

text\<open>Note that the precondition cannot be removed without an extra branch: If @{prop \<open>s = []\<close>}, the inner while-condition accesses out-of-bound memory. This will apply to KMP, too.\<close>

section\<open>Knuth--Morris--Pratt algorithm\<close>

text\<open>Just like our templates@{cite KMP77}@{cite GAD}, we first verify the main routine and discuss the computation of the auxiliary values @{term \<open>\<ff> s\<close>} only in a later section.\<close>

subsection\<open>Preliminaries: Borders of lists\<close>

definition "border xs ys \<longleftrightarrow> prefix xs ys \<and> suffix xs ys"
definition "strict_border xs ys \<longleftrightarrow> border xs ys \<and> length xs < length ys"
definition "intrinsic_border ls \<equiv> ARG_MAX length b. strict_border b ls"

subsubsection\<open>Properties\<close>

interpretation border_order: order border strict_border
  by standard (auto simp: border_def suffix_def strict_border_def)
interpretation border_bot: order_bot Nil border strict_border
  by standard (simp add: border_def)

lemma borderE[elim]:
  fixes xs ys :: "'a list"
  assumes "border xs ys"
  obtains "prefix xs ys" and "suffix xs ys"
  using assms unfolding border_def by blast

lemma strict_borderE[elim]:
  fixes xs ys :: "'a list"
  assumes "strict_border xs ys"
  obtains "border xs ys" and "length xs < length ys"
  using assms unfolding strict_border_def by blast

lemma strict_border_simps[simp]:
  "strict_border xs [] \<longleftrightarrow> False"
  "strict_border [] (x # xs) \<longleftrightarrow> True"
  by (simp_all add: strict_border_def)

lemma strict_border_prefix: "strict_border xs ys \<Longrightarrow> strict_prefix xs ys"
  and strict_border_suffix: "strict_border xs ys \<Longrightarrow> strict_suffix xs ys"
  and strict_border_imp_nonempty: "strict_border xs ys \<Longrightarrow> ys \<noteq> []"
  and strict_border_prefix_suffix: "strict_border xs ys \<longleftrightarrow> strict_prefix xs ys \<and> strict_suffix xs ys"
  by (auto simp: border_order.order.strict_iff_order border_def)

lemma border_length_le: "border xs ys \<Longrightarrow> length xs \<le> length ys"
  unfolding border_def by (simp add: prefix_length_le)

lemma border_length_r_less (*rm*): "\<forall>xs. strict_border xs ys \<longrightarrow> length xs < length ys"
  using strict_borderE by auto

lemma border_positions: "border xs ys \<Longrightarrow> \<forall>i<length xs. ys!i = ys!(length ys - length xs + i)"
  unfolding border_def
  by (metis diff_add_inverse diff_add_inverse2 length_append not_add_less1 nth_append prefixE suffixE)

lemma all_positions_drop_length_take: "\<lbrakk>i \<le> length w; i \<le> length x;
  \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
    \<Longrightarrow> drop (length w - i) w = take i x"
  by (cases "i = length x") (auto intro: nth_equalityI)

lemma all_positions_suffix_take: "\<lbrakk>i \<le> length w; i \<le> length x;
  \<forall>j<i. x ! j = w ! (length w + j - i)\<rbrakk>
    \<Longrightarrow> suffix (take i x) w"
  by (metis all_positions_drop_length_take suffix_drop)

lemma suffix_butlast: "suffix xs ys \<Longrightarrow> suffix (butlast xs) (butlast ys)"
  unfolding suffix_def by (metis append_Nil2 butlast.simps(1) butlast_append)

lemma positions_border: "\<forall>j<l. w!j = w!(length w - l + j) \<Longrightarrow> border (take l w) w"
  by (cases "l < length w") (simp_all add: border_def all_positions_suffix_take take_is_prefix)

lemma positions_strict_border: "l < length w \<Longrightarrow> \<forall>j<l. w!j = w!(length w - l + j) \<Longrightarrow> strict_border (take l w) w"
  by (simp add: positions_border strict_border_def)

lemmas intrinsic_borderI = arg_max_natI[OF _ border_length_r_less, folded intrinsic_border_def]

lemmas intrinsic_borderI' = border_bot.bot.not_eq_extremum[THEN iffD1, THEN intrinsic_borderI]

lemmas intrinsic_border_max = arg_max_nat_le[OF _ border_length_r_less, folded intrinsic_border_def]

lemma nonempty_is_arg_max_ib: "ys \<noteq> [] \<Longrightarrow> is_arg_max length (\<lambda>xs. strict_border xs ys) (intrinsic_border ys)"
  by (simp add: intrinsic_borderI' intrinsic_border_max is_arg_max_linorder)

lemma intrinsic_border_less: "w \<noteq> [] \<Longrightarrow> length (intrinsic_border w) < length w"
  using intrinsic_borderI[of w] border_length_r_less intrinsic_borderI' by blast

lemma intrinsic_border_take_less: "j > 0 \<Longrightarrow> w \<noteq> [] \<Longrightarrow> length (intrinsic_border (take j w)) < length w"
  by (metis intrinsic_border_less length_take less_not_refl2 min_less_iff_conj take_eq_Nil)

subsubsection\<open>Examples\<close>

lemma border_example: "{b. border b ''aabaabaa''} = {'''', ''a'', ''aa'', ''aabaa'', ''aabaabaa''}"
  (is "{b. border b ?l} = {?take0, ?take1, ?take2, ?take5, ?l}")
proof
  show "{?take0, ?take1, ?take2, ?take5, ?l} \<subseteq> {b. border b ?l}"
    by simp eval
  have "\<not>border ''aab'' ?l" "\<not>border ''aaba'' ?l" "\<not>border ''aabaab'' ?l" "\<not>border ''aabaaba'' ?l"
    by eval+
  moreover have "{b. border b ?l} \<subseteq> set (prefixes ?l)"
    using border_def in_set_prefixes by blast
  ultimately show "{b. border b ?l} \<subseteq> {?take0, ?take1, ?take2, ?take5, ?l}"
    by auto
qed

corollary strict_border_example: "{b. strict_border b ''aabaabaa''} = {'''', ''a'', ''aa'', ''aabaa''}"
  (is "?l = ?r")
proof
  have "?l \<subseteq> {b. border b ''aabaabaa''}"
    by auto
  also have "\<dots> = {'''', ''a'', ''aa'', ''aabaa'', ''aabaabaa''}"
    by (fact border_example)
  finally show "?l \<subseteq> ?r" by auto
  show "?r \<subseteq> ?l" by simp eval
qed

corollary "intrinsic_border ''aabaabaa'' = ''aabaa''"
proof - \<comment> \<open>We later obtain a fast algorithm for that.\<close>
  have exhaust: "strict_border b ''aabaabaa'' \<longleftrightarrow> b \<in> {'''', ''a'', ''aa'', ''aabaa''}" for b
    using strict_border_example by auto
  then have
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''''"
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''a''"
    "\<not>is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''aa''"
    "is_arg_max length (\<lambda>b. strict_border b ''aabaabaa'') ''aabaa''"
    unfolding is_arg_max_linorder by auto
  moreover have "strict_border (intrinsic_border ''aabaabaa'') ''aabaabaa''"
    using intrinsic_borderI' by blast
  note this[unfolded exhaust]
  ultimately show ?thesis
    by simp (metis list.discI nonempty_is_arg_max_ib)
qed

subsection\<open>Main routine\<close>

text\<open>The following is Seidl's "border"-table@{cite GAD} (values shifted by 1 so we don't need @{typ int}),
or equivalently, "f" from Knuth's, Morris' and Pratt's paper@{cite KMP77} (with indexes starting at 0).\<close>
fun \<ff> :: "'a list \<Rightarrow> nat \<Rightarrow> nat" where
  "\<ff> s 0 = 0" \<comment> \<open>This increments the compare position while @{prop \<open>j=(0::nat)\<close>}\<close> |
  "\<ff> s j = length (intrinsic_border (take j s)) + 1"
text\<open>Note that we use their "next" only implicitly.\<close>

subsubsection\<open>Invariants\<close>
definition "I_outer s t \<equiv> \<lambda>(i,j,pos).
  (\<forall>ii<i. \<not>sublist_at s t ii) \<and>
  (case pos of None \<Rightarrow> (\<forall>jj<j. t!(i+jj) = s!(jj)) \<and> j < length s
    | Some p \<Rightarrow> p=i \<and> sublist_at s t i)"
text\<open>For the inner loop, we can reuse @{const I_in_na}.\<close>

subsubsection\<open>Algorithm\<close>
text\<open>First, we use the non-evaluable function @{const \<ff>} directly:\<close>
definition "kmp s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length s);
      let i = i + (j - \<ff> s j + 1);
      let j = max 0 (\<ff> s j - 1); \<comment> \<open>\<open>max\<close> not necessary\<close>
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

subsubsection\<open>Correctness\<close>
lemma \<ff>_eq_0_iff_j_eq_0[simp]: "\<ff> s j = 0 \<longleftrightarrow> j = 0"
  by (cases j) simp_all

lemma j_le_\<ff>_le: "j \<le> length s \<Longrightarrow> \<ff> s j \<le> j"
  apply (cases j)
  apply simp_all
  by (metis Suc_leI intrinsic_border_less length_take list.size(3) min.absorb2 nat.simps(3) not_less)

lemma j_le_\<ff>_le': "0 < j \<Longrightarrow> j \<le> length s \<Longrightarrow> \<ff> s j - 1 < j"
  by (metis diff_less j_le_\<ff>_le le_eq_less_or_eq less_imp_diff_less less_one)

lemma \<ff>_le: "s \<noteq> [] \<Longrightarrow> \<ff> s j - 1 < length s"
  by (cases j) (simp_all add: intrinsic_border_take_less)

(*
  Only needed for run-time analysis
lemma "p576 et seq":
  assumes
    "j \<le> length s" and
    assignments:
    "i' = i + (j + 1 - \<ff> s j)"
    "j' = max 0 (\<ff> s j - 1)"
  shows
    sum_no_decrease: "i' + j' \<ge> i + j" and
    i_increase: "i' > i"
  using assignments by (simp_all add: j_le_\<ff>_le[OF assms(1), THEN le_imp_less_Suc])
*)

lemma reuse_matches: 
  assumes j_le: "j \<le> length s"
  and old_matches: "\<forall>jj<j. t ! (i + jj) = s ! jj"
  shows "\<forall>jj<\<ff> s j - 1. t ! (i + (j - \<ff> s j + 1) + jj) = s ! jj"
    (is "\<forall>jj<?j'. t ! (?i' + jj) = s ! jj")
proof (cases "j>0")
  assume "j>0"
  have \<ff>_le: "\<ff> s j \<le> j"
    by (simp add: j_le j_le_\<ff>_le)
  with old_matches have 1: "\<forall>jj<?j'. t ! (?i' + jj) = s ! (j - \<ff> s j + 1 + jj)"
    by (metis ab_semigroup_add_class.add.commute add.assoc diff_diff_cancel less_diff_conv)
  have [simp]: "length (take j s) = j" "length (intrinsic_border (take j s)) = ?j'"
    by (simp add: j_le) (metis \<open>0 < j\<close> diff_add_inverse2 \<ff>.elims nat_neq_iff)
  then have "\<forall>jj<?j'. take j s ! jj = take j s ! (j - (\<ff> s j - 1) + jj)"
    by (metis intrinsic_borderI' \<open>0 < j\<close> border_positions length_greater_0_conv strict_border_def)
  then have "\<forall>jj<?j'. take j s ! jj = take j s ! (j - \<ff> s j + 1 + jj)"
    by (simp add: \<ff>_le)
  then have 2: "\<forall>jj<?j'. s ! (j - \<ff> s j + 1 + jj) = s ! jj"
    using \<ff>_le by simp
  from 1 2 show ?thesis by simp
qed simp

theorem shift_safe:
  assumes
    "\<forall>ii<i. \<not>sublist_at s t ii"
    "t!(i+j) \<noteq> s!j" and
    [simp]: "j < length s" and
    matches: "\<forall>jj<j. t!(i+jj) = s!jj"
  defines
    assignment: "i' \<equiv> i + (j - \<ff> s j + 1)"
  shows
    "\<forall>ii<i'. \<not>sublist_at s t ii"
proof (standard, standard)
  fix ii
  assume "ii < i'"
  then consider \<comment> \<open>The position falls into one of three categories:\<close>
    (old) "ii < i" |
    (current) "ii = i" |
    (skipped) "ii > i"
    by linarith
  then show "\<not>sublist_at s t ii"
  proof cases
    case old \<comment> \<open>Old position, use invariant.\<close>
    with \<open>\<forall>ii<i. \<not>sublist_at s t ii\<close> show ?thesis by simp
  next
    case current \<comment> \<open>The mismatch occurred while testing this alignment.\<close>
    with \<open>t!(i+j) \<noteq> s!j\<close> show ?thesis
      using sublist_all_positions[of s t i] by auto
  next
    case skipped \<comment> \<open>The skipped positions.\<close>
    then have "0<j"
      using \<open>ii < i'\<close> assignment by linarith
    then have less_j[simp]: "j + i - ii < j" and le_s: "j + i - ii \<le> length s"
      using \<open>ii < i'\<close> assms(3) skipped by linarith+
    note \<ff>_le[simp] = j_le_\<ff>_le[OF assms(3)[THEN less_imp_le]]
    have "0 < \<ff> s j"
      using \<open>0 < j\<close> \<ff>_eq_0_iff_j_eq_0 neq0_conv by blast
    then have "j + i - ii > \<ff> s j - 1"
      using \<open>ii < i'\<close> assignment \<ff>_le by linarith
    then have contradiction_goal: "j + i - ii > length (intrinsic_border (take j s))"
      by (metis \<ff>.elims \<open>0 < j\<close> add_diff_cancel_right' not_gr_zero)
    show ?thesis
    proof
      assume "sublist_at s t ii"
      note sublist_all_positions[OF this]
      with le_s have a: "\<forall>jj < j+i-ii. t!(ii+jj) = s!jj"
        by simp
      have ff1: "\<not> ii < i"
        by (metis not_less_iff_gr_or_eq skipped)
      then have "i + (ii - i + jj) = ii + jj" for jj
        by (metis add.assoc add_diff_inverse_nat)
      then have "\<not> jj < j + i - ii \<or> t ! (ii + jj) = s ! (ii - i + jj)" if "ii - i + jj < j" for jj
        using that ff1 by (metis matches)
      then have "\<not> jj < j + i - ii \<or> t ! (ii + jj) = s ! (ii - i + jj)" for jj
        using ff1 by auto
      with matches have "\<forall>jj < j+i-ii. t!(ii+jj) = s!(ii-i+jj)" by metis
      then have "\<forall>jj < j+i-ii. s!jj = s!(ii-i+jj)"
        using a by auto
      then have "\<forall>jj < j+i-ii. (take j s)!jj = (take j s)!(ii-i+jj)"
        using \<open>i<ii\<close> by auto
      with positions_strict_border[of "j+i-ii" "take j s", simplified]
      have "strict_border (take (j+i-ii) s) (take j s)".
      note intrinsic_border_max[OF this]
      also note contradiction_goal
      also have "j+i-ii \<le> length s" by (fact le_s)
      ultimately
      show False by simp
    qed
  qed
qed

lemma kmp_correct: "s \<noteq> []
  \<Longrightarrow> kmp s t \<le> kmp_SPEC s t"
  unfolding kmp_def kmp_SPEC_def I_outer_def I_in_na_def
  apply (refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(i,_,pos). length t - i + (if pos = None then 1 else 0))"]
    WHILEIT_rule[where R="measure (\<lambda>(j,_::nat option). length s - j)"]
    )
                   apply (vc_solve solve: asm_rl)
  subgoal by (metis add_Suc_right all_positions_sublist less_antisym)
  subgoal using less_antisym by blast
  subgoal for i jout j using shift_safe[of i s t j] by fastforce
  subgoal for i jout j using reuse_matches[of j s t i] \<ff>_le by simp
  subgoal by (auto split: option.splits) (metis sublist_lengths add_less_cancel_right leI le_less_trans)
  done

subsubsection\<open>Storing the @{const \<ff>}-values\<close>
text\<open>We refine the algorithm to compute the @{const \<ff>}-values only once at the start:\<close>
definition compute_\<ff>s_SPEC :: "'a list \<Rightarrow> nat list nres" where
  "compute_\<ff>s_SPEC s \<equiv> SPEC (\<lambda>\<ff>s. length \<ff>s = length s + 1 \<and> (\<forall>j\<le>length s. \<ff>s!j = \<ff> s j))"

definition "kmp1 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  \<ff>s \<leftarrow> compute_\<ff>s_SPEC (butlast s); \<comment> \<open>At the last char, we abort instead.\<close>
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length \<ff>s);
      let i = i + (j - \<ff>s!j + 1);
      let j = max 0 (\<ff>s!j - 1); \<comment> \<open>\<open>max\<close> not necessary\<close>
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

lemma \<ff>_butlast[simp]: "j < length s \<Longrightarrow> \<ff> (butlast s) j = \<ff> s j"
  by (cases j) (simp_all add: take_butlast)

lemma kmp1_refine: "kmp1 s t \<le> kmp s t"
  apply (rule refine_IdD)
  unfolding kmp1_def kmp_def Let_def compute_\<ff>s_SPEC_def nres_monad_laws
  apply (intro ASSERT_refine_right ASSERT_refine_left)
   apply simp
  apply (rule Refine_Basic.intro_spec_refine)
  apply refine_rcg
                apply refine_dref_type
                apply vc_solve
  done

text\<open>Next, an algorithm that satisfies @{const compute_\<ff>s_SPEC}:\<close>
subsection\<open>Computing @{const \<ff>}\<close>
subsubsection\<open>Invariants\<close>

definition "I_out_cb s \<equiv> \<lambda>(\<ff>s,i,j).
  length s + 1 = length \<ff>s \<and>
  (\<forall>jj<j. \<ff>s!jj = \<ff> s jj) \<and>
  \<ff>s!(j-1) = i \<and>
  0 < j"
definition "I_in_cb s j \<equiv> \<lambda>i.
  if j=1 then i=0 \<comment> \<open>first iteration\<close>
  else
    strict_border (take (i-1) s) (take (j-1) s) \<and>
    \<ff> s j \<le> i + 1"

subsubsection\<open>Algorithm\<close>

text\<open>Again, we follow Seidl@{cite GAD}, p.582. Apart from the +1-shift, we make another modification:
Instead of directly setting @{term \<open>\<ff>s!1\<close>}, we let the first loop-iteration (if there is one) do that for us.
This allows us to remove the precondition @{prop \<open>s \<noteq> []\<close>}, as the index bounds are respected even in that corner case.\<close>

definition compute_\<ff>s :: "'a list \<Rightarrow> nat list nres" where
  "compute_\<ff>s s = do {
  let \<ff>s=replicate (length s + 1) 0; \<comment> \<open>only the first 0 is needed\<close>
  let i=0;
  let j=1;
  (\<ff>s,_,_) \<leftarrow> WHILEIT (I_out_cb s) (\<lambda>(\<ff>s,_,j). j < length \<ff>s) (\<lambda>(\<ff>s,i,j). do {
    i \<leftarrow> WHILEIT (I_in_cb s j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length \<ff>s);
      let i=\<ff>s!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length \<ff>s);
    let \<ff>s=\<ff>s[j:=i];
    let j=j+1;
    RETURN (\<ff>s,i,j)
  }) (\<ff>s,i,j);
  
  RETURN \<ff>s
}"

subsubsection\<open>Correctness\<close>
lemma take_length_ib[simp]:
  assumes "0 < j" "j \<le> length s"
    shows "take (length (intrinsic_border (take j s))) s = intrinsic_border (take j s)"
proof -
  from assms have "prefix (intrinsic_border (take j s)) (take j s)"
    by (metis intrinsic_borderI' border_def list.size(3) neq0_conv not_less strict_border_def take_eq_Nil)
  also have "prefix (take j s) s"
    by (simp add: \<open>j \<le> length s\<close> take_is_prefix)
  finally show ?thesis
    by (metis append_eq_conv_conj prefixE)
qed

lemma ib_singleton[simp]: "intrinsic_border [z] = []"
  by (metis intrinsic_border_less length_Cons length_greater_0_conv less_Suc0 list.size(3))

lemma border_butlast: "border xs ys \<Longrightarrow> border (butlast xs) (butlast ys)"
  apply (auto simp: border_def)
   apply (metis butlast_append prefixE prefix_order.eq_refl prefix_prefix prefixeq_butlast)
  apply (metis Sublist.suffix_def append.right_neutral butlast.simps(1) butlast_append)
  done

corollary strict_border_butlast: "xs \<noteq> [] \<Longrightarrow> strict_border xs ys \<Longrightarrow> strict_border (butlast xs) (butlast ys)"
  unfolding strict_border_def by (simp add: border_butlast less_diff_conv)

lemma border_take_lengths: "i \<le> length s \<Longrightarrow> border (take i s) (take j s) \<Longrightarrow> i \<le> j"
  using border_length_le by fastforce

lemma border_step: "border xs ys \<longleftrightarrow> border (xs@[ys!length xs]) (ys@[ys!length xs])"
  apply (auto simp: border_def suffix_def)
  using append_one_prefix prefixE apply fastforce
  using append_prefixD apply blast
  done

corollary strict_border_step: "strict_border xs ys \<longleftrightarrow> strict_border (xs@[ys!length xs]) (ys@[ys!length xs])"
  unfolding strict_border_def using border_step by auto

lemma ib_butlast: "length w \<ge> 2 \<Longrightarrow> length (intrinsic_border w) \<le> length (intrinsic_border (butlast w)) + 1"
proof -
  assume "length w \<ge> 2"
  then have "w \<noteq> []" by auto
  then have "strict_border (intrinsic_border w) w"
    by (fact intrinsic_borderI')
  with \<open>2 \<le> length w\<close> have "strict_border (butlast (intrinsic_border w)) (butlast w)"
    by (metis One_nat_def border_bot.bot.not_eq_extremum butlast.simps(1) len_greater_imp_nonempty length_butlast lessI less_le_trans numerals(2) strict_border_butlast zero_less_diff)
  then have "length (butlast (intrinsic_border w)) \<le> length (intrinsic_border (butlast w))"
    using intrinsic_border_max by blast
  then show ?thesis
    by simp
qed

corollary \<ff>_Suc(*rm*): "Suc i \<le> length w \<Longrightarrow> \<ff> w (Suc i) \<le> \<ff> w i + 1"
  apply (cases i)
   apply (simp_all add: take_Suc0)
  by (metis One_nat_def Suc_eq_plus1 Suc_to_right butlast_take diff_is_0_eq ib_butlast length_take min.absorb2 nat.simps(3) not_less_eq_eq numerals(2))

lemma \<ff>_step_bound(*rm*):
  assumes "j \<le> length w"
  shows "\<ff> w j \<le> \<ff> w (j-1) + 1"
  using assms[THEN j_le_\<ff>_le] \<ff>_Suc assms
  by (metis One_nat_def Suc_pred le_SucI not_gr_zero trans_le_add2)

lemma border_take_\<ff>: "border (take (\<ff> s i - 1) s ) (take i s)"
  apply (cases i, simp_all)
  by (metis intrinsic_borderI' border_order.eq_iff border_order.less_imp_le border_positions nat.simps(3) nat_le_linear positions_border take_all take_eq_Nil take_length_ib zero_less_Suc)

corollary \<ff>_strict_borderI: "y = \<ff> s (i-1) \<Longrightarrow> strict_border (take (i-1) s) (take (j-1) s) \<Longrightarrow> strict_border (take (y-1) s) (take (j-1) s)"
  using border_order.less_le_not_le border_order.order.trans border_take_\<ff> by blast

corollary strict_border_take_\<ff>: "0 < i \<Longrightarrow> i \<le> length s \<Longrightarrow> strict_border (take (\<ff> s i - 1) s ) (take i s)"
  by (meson border_order.less_le_not_le border_take_\<ff> border_take_lengths j_le_\<ff>_le' leD)

lemma \<ff>_is_max: "j \<le> length s \<Longrightarrow> strict_border b (take j s) \<Longrightarrow> \<ff> s j \<ge> length b + 1"
  by (metis \<ff>.elims add_le_cancel_right add_less_same_cancel2 border_length_r_less intrinsic_border_max length_take min_absorb2 not_add_less2)

theorem skipping_ok:
  assumes j_bounds[simp]: "1 < j" "j \<le> length s"
    and mismatch: "s!(i-1) \<noteq> s!(j-1)"
    and greater_checked: "\<ff> s j \<le> i + 1"
    and "strict_border (take (i-1) s) (take (j-1) s)"
  shows "\<ff> s j \<le> \<ff> s (i-1) + 1"
proof (rule ccontr)
  assume "\<not>\<ff> s j \<le> \<ff> s (i-1) + 1"
  then have i_bounds: "0 < i" "i \<le> length s"
    using greater_checked assms(5) take_Nil by fastforce+
  then have i_less_j: "i < j"
    using assms(5) border_length_r_less nz_le_conv_less by auto
  from \<open>\<not>\<ff> s j \<le> \<ff> s (i-1) + 1\<close> greater_checked consider
    (tested) "\<ff> s j = i + 1" \<comment> \<open>This contradicts @{thm mismatch}\<close> |
    (skipped) "\<ff> s (i-1) + 1 < \<ff> s j" "\<ff> s j \<le> i"
      \<comment> \<open>This contradicts @{thm \<ff>_is_max[of "i-1" s]}\<close>
    by linarith
  then show False
  proof cases
    case tested
    then have "\<ff> s j - 1 = i" by simp
    moreover note border_positions[OF border_take_\<ff>[of s j, unfolded this]]
    ultimately have "take j s ! (i-1) = s!(j-1)" using i_bounds i_less_j by simp
    with \<open>i < j\<close> have "s!(i-1) = s!(j-1)"
      by (simp add: less_imp_diff_less)
    with mismatch show False..
  next
    case skipped
    let ?border = "take (i-1) s"
      \<comment> \<open>This border of @{term \<open>take (j-1) s\<close>} could not be extended to a border of @{term \<open>take j s\<close>} due to the mismatch.\<close>
    let ?impossible = "take (\<ff> s j - 2) s"
      \<comment> \<open>A strict border longer than @{term \<open>intrinsic_border ?border\<close>}, a contradiction.\<close>
    have "length (take j s) = j"
      by simp
    have "\<ff> s j - 2 < i - 1"
      using skipped by linarith
    then have less_s: "\<ff> s j - 2 < length s" "i - 1 < length s"
      using \<open>i < j\<close> j_bounds(2) by linarith+
    then have strict: "length ?impossible < length ?border"
      using \<open>\<ff> s j - 2 < i - 1\<close> by auto
    moreover {
      have "prefix ?impossible (take j s)"
        using prefix_length_prefix take_is_prefix
        by (metis (no_types, lifting) \<open>length (take j s) = j\<close> j_bounds(2) diff_le_self j_le_\<ff>_le length_take less_s(1) min_simps(2) order_trans)
      moreover have "prefix ?border (take j s)"
        by (metis (no_types, lifting) \<open>length (take j s) = j\<close> diff_le_self i_less_j le_trans length_take less_or_eq_imp_le less_s(2) min_simps(2) prefix_length_prefix take_is_prefix)
      ultimately have "prefix ?impossible ?border"
        using strict less_imp_le_nat prefix_length_prefix by blast
    } moreover {
      have "suffix (take (\<ff> s j - 1) s) (take j s)" using border_take_\<ff>
        by (auto simp: border_def)
      note suffix_butlast[OF this]
      then have "suffix ?impossible (take (j-1) s)"
        by (metis One_nat_def j_bounds(2) butlast_take diff_diff_left \<ff>_le len_greater_imp_nonempty less_or_eq_imp_le less_s(2) one_add_one)
      then have "suffix ?impossible (take (j-1) s)" "suffix ?border (take (j-1) s)"
        using assms(5) by auto
      from suffix_length_suffix[OF this strict[THEN less_imp_le]]
        have "suffix ?impossible ?border".
    }
    ultimately have "strict_border ?impossible ?border"
      unfolding strict_border_def[unfolded border_def] by blast
    note \<ff>_is_max[of "i-1" s, OF _ this]
    then have "length (take (\<ff> s j - 2) s) + 1 \<le> \<ff> s (i-1)"
      using less_imp_le_nat less_s(2) by blast
    then have "\<ff> s j - 1 \<le> \<ff> s (i-1)"
      by (simp add: less_s(1))
    then have "\<ff> s j \<le> \<ff> s (i-1) + 1"
      using le_diff_conv by blast
    with skipped(1) show False
      by linarith
  qed
qed

lemma extend_border:
  assumes "j \<le> length s"
  assumes "s!(i-1) = s!(j-1)"
  assumes "strict_border (take (i-1) s) (take (j-1) s)"
  assumes "\<ff> s j \<le> i + 1"
  shows "\<ff> s j = i + 1"
proof -
  from assms(3) have pos_in_range: "i - 1 < length s " "length (take (i-1) s) = i - 1"
    using border_length_r_less min_less_iff_conj by auto
  with strict_border_step[THEN iffD1, OF assms(3)] have "strict_border (take (i-1) s @ [s!(i-1)]) (take (j-1) s @ [s!(i-1)])"
    by (metis assms(3) border_length_r_less length_take min_less_iff_conj nth_take)
  with pos_in_range have "strict_border (take i s) (take (j-1) s @ [s!(i-1)])"
    by (metis Suc_eq_plus1 Suc_pred add.left_neutral border_bot.bot.not_eq_extremum border_order.less_asym neq0_conv take_0 take_Suc_conv_app_nth)
  then have "strict_border (take i s) (take (j-1) s @ [s!(j-1)])"
    by (simp only: \<open>s!(i-1) = s!(j-1)\<close>)
  then have "strict_border (take i s) (take j s)"
    by (metis One_nat_def Suc_pred assms(1,3) diff_le_self less_le_trans neq0_conv nz_le_conv_less strict_border_imp_nonempty take_Suc_conv_app_nth take_eq_Nil)
  with \<ff>_is_max[OF assms(1) this] have "\<ff> s j \<ge> i + 1"
    using Suc_leI by fastforce
  with \<open>\<ff> s j \<le> i + 1\<close> show ?thesis
    using le_antisym by presburger
qed

lemma compute_\<ff>s_correct: "compute_\<ff>s s \<le> compute_\<ff>s_SPEC s"
  unfolding compute_\<ff>s_SPEC_def compute_\<ff>s_def I_out_cb_def I_in_cb_def
  apply (simp, refine_vcg
    WHILEIT_rule[where R="measure (\<lambda>(\<ff>s,i,j). length s + 1 - j)"]
    WHILEIT_rule[where R="measure id"] \<comment> \<open>@{term \<open>i::nat\<close>} decreases with every iteration.\<close>
    )
                      apply (vc_solve, fold One_nat_def)
  subgoal for b j by (rule strict_border_take_\<ff>, auto)
  subgoal by (metis Suc_eq_plus1 \<ff>_step_bound less_Suc_eq_le)
  subgoal by fastforce
  subgoal
    by (metis (no_types, lifting) One_nat_def Suc_lessD Suc_pred border_length_r_less \<ff>_strict_borderI length_take less_Suc_eq less_Suc_eq_le min.absorb2)
  subgoal for b j i
    by (metis (no_types, lifting) One_nat_def Suc_diff_1 Suc_eq_plus1 Suc_leI border_take_lengths less_Suc_eq_le less_antisym skipping_ok strict_border_def)
  subgoal by (metis Suc_diff_1 border_take_lengths j_le_\<ff>_le less_Suc_eq_le strict_border_def)
  subgoal for b j i jj
    by (metis Suc_eq_plus1 Suc_eq_plus1_left add.right_neutral extend_border \<ff>_eq_0_iff_j_eq_0 j_le_\<ff>_le le_zero_eq less_Suc_eq less_Suc_eq_le nth_list_update_eq nth_list_update_neq)
  subgoal by linarith
  done

subsubsection\<open>Index shift\<close>
text\<open>To avoid inefficiencies, we refine @{const compute_\<ff>s} to take @{term s}
instead of @{term \<open>butlast s\<close>} (it still only uses @{term \<open>butlast s\<close>}).\<close>
definition compute_butlast_\<ff>s :: "'a list \<Rightarrow> nat list nres" where
  "compute_butlast_\<ff>s s = do {
  let \<ff>s=replicate (length s) 0;
  let i=0;
  let j=1;
  (\<ff>s,_,_) \<leftarrow> WHILEIT (I_out_cb (butlast s)) (\<lambda>(b,i,j). j < length b) (\<lambda>(\<ff>s,i,j). do {
    ASSERT (j < length \<ff>s);
    i \<leftarrow> WHILEIT (I_in_cb (butlast s) j) (\<lambda>i. i>0 \<and> s!(i-1) \<noteq> s!(j-1)) (\<lambda>i. do {
      ASSERT (i-1 < length \<ff>s);
      let i=\<ff>s!(i-1);
      RETURN i
    }) i;
    let i=i+1;
    ASSERT (j < length \<ff>s);
    let \<ff>s=\<ff>s[j:=i];
    let j=j+1;
    RETURN (\<ff>s,i,j)
  }) (\<ff>s,i,j);
  
  RETURN \<ff>s
}"

lemma compute_\<ff>s_inner_bounds: 
  assumes "I_out_cb s (\<ff>s,ix,j)"
  assumes "j < length \<ff>s"
  assumes "I_in_cb s j i"
  shows "i-1 < length s" "j-1 < length s"
  using assms
    by (auto simp: I_out_cb_def I_in_cb_def split: if_splits)

lemma compute_butlast_\<ff>s_refine[refine]:
  assumes "(s,s') \<in> br butlast ((\<noteq>) [])"
  shows "compute_butlast_\<ff>s s \<le> \<Down> Id (compute_\<ff>s_SPEC s')"
proof -
  have "compute_butlast_\<ff>s s \<le> \<Down> Id (compute_\<ff>s s')"
    unfolding compute_butlast_\<ff>s_def compute_\<ff>s_def 
    apply (refine_rcg)
              apply (refine_dref_type)
    using assms apply (vc_solve simp: in_br_conv)
     apply (metis Suc_pred length_greater_0_conv replicate_Suc)
    by (metis One_nat_def compute_\<ff>s_inner_bounds nth_butlast)
  also note compute_\<ff>s_correct
  finally show ?thesis by simp
qed

subsection\<open>Conflation\<close>
text\<open>We replace @{const compute_\<ff>s_SPEC} with @{const compute_butlast_\<ff>s}\<close>
definition "kmp2 s t \<equiv> do {
  ASSERT (s \<noteq> []);
  let i=0;
  let j=0;
  let pos=None;
  \<ff>s \<leftarrow> compute_butlast_\<ff>s s;
  (_,_,pos) \<leftarrow> WHILEIT (I_outer s t) (\<lambda>(i,j,pos). i + length s \<le> length t \<and> pos=None) (\<lambda>(i,j,pos). do {
    ASSERT (i + length s \<le> length t \<and> pos=None);
    (j,pos) \<leftarrow> WHILEIT (I_in_na s t i) (\<lambda>(j,pos). t!(i+j) = s!j \<and> pos=None) (\<lambda>(j,pos). do {
      let j=j+1;
      if j=length s then RETURN (j,Some i) else RETURN (j,None)
    }) (j,pos);
    if pos=None then do {
      ASSERT (j < length \<ff>s);
      let i = i + (j - \<ff>s!j + 1);
      let j = max 0 (\<ff>s!j - 1); \<comment> \<open>\<open>max\<close> not necessary\<close>
      RETURN (i,j,None)
    } else RETURN (i,j,Some i)
  }) (i,j,pos);

  RETURN pos
}"

text\<open>Using @{thm [source] compute_butlast_\<ff>s_refine} (it has attribute @{attribute refine}), the proof is trivial:\<close>
lemma kmp2_refine: "kmp2 s t \<le> kmp1 s t"
  apply (rule refine_IdD)
  unfolding kmp2_def kmp1_def
  apply refine_rcg
                  apply refine_dref_type
                  apply (vc_solve simp: in_br_conv)
  done

lemma kmp2_correct: "s \<noteq> []
  \<Longrightarrow> kmp2 s t \<le> kmp_SPEC s t"
proof -
  assume "s \<noteq> []"
  have "kmp2 s t \<le> kmp1 s t" by (fact kmp2_refine)
  also have "... \<le> kmp s t" by (fact kmp1_refine)
  also have "... \<le> kmp_SPEC s t" by (fact kmp_correct[OF \<open>s \<noteq> []\<close>])
  finally show ?thesis.
qed

text\<open>For convenience, we also remove the precondition:\<close>
definition "kmp3 s t \<equiv> do {
  if s=[] then RETURN (Some 0) else kmp2 s t
}"

lemma kmp3_correct: "kmp3 s t \<le> kmp_SPEC s t"
  unfolding kmp3_def by (simp add: kmp2_correct) (simp add: kmp_SPEC_def)

section \<open>Refinement to Imperative/HOL\<close>

lemma eq_id_param: "((=), (=)) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp

lemmas in_bounds_aux = compute_\<ff>s_inner_bounds[of "butlast s" for s, simplified]

sepref_definition compute_butlast_\<ff>s_impl is compute_butlast_\<ff>s :: "(arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn nat_assn"
  unfolding compute_butlast_\<ff>s_def
  supply in_bounds_aux[dest]
  supply eq_id_param[where 'a='a, sepref_import_param]
  apply (rewrite array_fold_custom_replicate)
  by sepref
  
  
declare compute_butlast_\<ff>s_impl.refine[sepref_fr_rules]

sepref_register compute_\<ff>s

lemma kmp_inner_in_bound:
  assumes "i + length s \<le> length t"
  assumes "I_in_na s t i (j,None)"
  shows "i + j < length t" "j < length s"
  using assms
  by (auto simp: I_in_na_def)
  
sepref_definition kmp_impl is "uncurry kmp3" :: "(arl_assn id_assn)\<^sup>k *\<^sub>a (arl_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a option_assn nat_assn"
  unfolding kmp3_def kmp2_def
  apply (simp only: max_0L) \<comment> \<open>Avoid the unneeded @{const max}\<close>
  apply (rewrite in "WHILEIT (I_in_na _ _ _) \<hole>" conj_commute)
  apply (rewrite in "WHILEIT (I_in_na _ _ _) \<hole>" short_circuit_conv)
  supply kmp_inner_in_bound[dest]
  supply option.splits[split]
  supply eq_id_param[where 'a='a, sepref_import_param]
  by sepref

export_code kmp_impl in SML_imp module_name KMP

lemma kmp3_correct':
  "(uncurry kmp3, uncurry kmp_SPEC) \<in> Id \<times>\<^sub>r Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI; clarsimp)
  apply (fact kmp3_correct)
  done

lemmas kmp_impl_correct' = kmp_impl.refine[FCOMP kmp3_correct']

subsection \<open>Overall Correctness Theorem\<close>
text \<open>The following theorem relates the final Imperative HOL algorithm to its specification,
  using, beyond basic HOL concepts
    \<^item> Hoare triples for Imperative/HOL, provided by the Separation Logic Framework for Imperative/HOL (Theory @{theory Separation_Logic_Imperative_HOL.Sep_Main});
    \<^item> The assertion @{const arl_assn} to specify array-lists, which we use to represent the input strings of the algorithm;
    \<^item> The @{const sublist_at} function that we defined in section \ref{sec:spec}.
  \<close>
theorem kmp_impl_correct:
  "< arl_assn id_assn s si * arl_assn id_assn t ti > 
       kmp_impl si ti 
   <\<lambda>r. arl_assn id_assn s si * arl_assn id_assn t ti * \<up>(
      case r of None \<Rightarrow>  \<nexists>i. sublist_at s t i
              | Some i \<Rightarrow> sublist_at s t i \<and> (\<forall>ii<i. \<not> sublist_at s t ii)
    )>\<^sub>t"
  by (sep_auto 
    simp: pure_def kmp_SPEC_def
    split: option.split
    heap:  kmp_impl_correct'[THEN hfrefD, THEN hn_refineD, of "(s,t)" "(si,ti)", simplified])

definition "kmp_string_impl \<equiv> kmp_impl :: (char array \<times> nat) \<Rightarrow> _"

section \<open>Tests of Generated ML-Code\<close>

ML_val \<open>
  fun str2arl s = (Array.fromList (@{code String.explode} s), @{code nat_of_integer} (String.size s))
  fun kmp s t = map_option @{code integer_of_nat} (@{code kmp_string_impl} (str2arl s) (str2arl t) ())
  
  val test1 = kmp "anas" "bananas"
  val test2 = kmp "" "bananas"
  val test3 = kmp "hide_fact" (File.read @{file \<open>~~/src/HOL/Main.thy\<close>})
  val test4 = kmp "sorry" (File.read @{file \<open>~~/src/HOL/HOL.thy\<close>})  
\<close>

end
