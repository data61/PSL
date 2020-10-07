(*
 * Finite Set lemmas.
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced July 2006.
 * License: BSD
 *)

(*<*)
theory FSext

imports Main

begin
(*>*)

(* **************************************** *)

section\<open>General Lemmas\<close>

subsection\<open>Extra Finite-Set Lemmas\<close>

text\<open>Small variant of @{thm [source] "Finite_Set.finite_subset_induct"}:
also assume @{term "F \<subseteq> A"} in the induction hypothesis.\<close>

lemma finite_subset_induct' [consumes 2, case_names empty insert]:
  assumes "finite F" and "F \<subseteq> A"
    and empty: "P {}"
    and insert: "\<And>a F. \<lbrakk>finite F; a \<in> A; F \<subseteq> A; a \<notin> F; P F \<rbrakk> \<Longrightarrow> P (insert a F)"
  shows "P F"
proof -
  from \<open>finite F\<close>
  have "F \<subseteq> A \<Longrightarrow> ?thesis"
  proof induct
    show "P {}" by fact
  next
    fix x F
    assume "finite F" and "x \<notin> F" and
      P: "F \<subseteq> A \<Longrightarrow> P F" and i: "insert x F \<subseteq> A"
    show "P (insert x F)"
    proof (rule insert)
      from i show "x \<in> A" by blast
      from i have "F \<subseteq> A" by blast
      with P show "P F" .
      show "finite F" by fact
      show "x \<notin> F" by fact
      show "F \<subseteq> A" by fact
    qed
  qed
  with \<open>F \<subseteq> A\<close> show ?thesis by blast
qed

text\<open>A slight improvement on @{thm [source] "List.finite_list"} - add
@{term "distinct"}.\<close>

lemma finite_list: "finite A \<Longrightarrow> \<exists>l. set l = A \<and> distinct l"
proof(induct rule: finite_induct)
  case (insert x F)
  then obtain l where "set l = F \<and> distinct l" by auto
  with insert have "set (x#l) = insert x F \<and> distinct (x#l)" by auto
  thus ?case by blast
qed auto

subsection\<open>Extra bijection lemmas\<close>

lemma bij_betw_onto: "bij_betw f A B \<Longrightarrow> f ` A = B" unfolding bij_betw_def by simp

lemma inj_on_UnI: "\<lbrakk> inj_on f A; inj_on f B; f ` (A - B) \<inter> f ` (B - A) = {} \<rbrakk> \<Longrightarrow> inj_on f (A \<union> B)"
  by (auto iff: inj_on_Un)

lemma card_compose_bij:
  assumes bijf: "bij_betw f A A"
  shows "card { a \<in> A. P (f a) } = card { a \<in> A. P a }"
proof -
  from bijf have T: "f ` { a \<in> A. P (f a) } = { a \<in> A. P a }"
    unfolding bij_betw_def by auto
  from bijf have "card { a \<in> A. P (f a) } = card (f ` { a \<in> A. P (f a) })"
    unfolding bij_betw_def by (auto intro: subset_inj_on card_image[symmetric])
  with T show ?thesis by simp
qed

lemma card_eq_bij:
  assumes cardAB: "card A = card B"
      and finiteA: "finite A" and finiteB: "finite B"
  obtains f where "bij_betw f A B"
proof -
  from finiteA obtain g where G: "bij_betw g A {0..<card A}"
    by (blast dest: ex_bij_betw_finite_nat)
  from finiteB obtain h where H: "bij_betw h {0..<card B} B"
    by (blast dest: ex_bij_betw_nat_finite)
  from G H cardAB have I: "inj_on (h \<circ> g) A"
    unfolding bij_betw_def by - (rule comp_inj_on, simp_all)
  from G H cardAB have "(h \<circ> g) ` A = B"
    unfolding bij_betw_def by auto (metis image_cong image_image)
  with I have "bij_betw (h \<circ> g) A B"
    unfolding bij_betw_def by blast
  thus thesis ..
qed

lemma bij_combine:
  assumes ABCD: "A \<subseteq> B" "C \<subseteq> D"
      and bijf: "bij_betw f A C"
      and bijg: "bij_betw g (B - A) (D - C)"
  obtains h
    where "bij_betw h B D"
      and "\<And>x. x \<in> A \<Longrightarrow> h x = f x"
      and "\<And>x. x \<in> B - A \<Longrightarrow> h x = g x" 
proof -
  let ?h = "\<lambda>x. if x \<in> A then f x else g x"
  have "inj_on ?h (A \<union> (B - A))"
  proof(rule inj_on_UnI)
    from bijf show "inj_on ?h A"
      by - (rule inj_onI, auto dest: inj_onD bij_betw_imp_inj_on)
    from bijg show "inj_on ?h (B - A)"
      by - (rule inj_onI, auto dest: inj_onD bij_betw_imp_inj_on)
    from bijf bijg show "?h ` (A - (B - A)) \<inter> ?h ` (B - A - A) = {}"
      by (simp, blast dest: bij_betw_onto)
  qed
  with ABCD have "inj_on ?h B" by (auto iff: Un_absorb1)
  moreover
  have "?h ` B = D"
  proof -
    from ABCD have "?h ` B = f ` A \<union> g ` (B - A)" by (auto iff: image_Un Un_absorb1)
    also from ABCD bijf bijg have "\<dots> = D" by (blast dest: bij_betw_onto)
    finally show ?thesis .
  qed
  ultimately have "bij_betw ?h B D"
              and "\<And>x. x \<in> A \<Longrightarrow> ?h x = f x"
              and "\<And>x. x \<in> B - A \<Longrightarrow> ?h x = g x"
    unfolding bij_betw_def by auto
  thus thesis ..
qed

lemma bij_complete:
  assumes finiteC: "finite C"
      and ABC: "A \<subseteq> C" "B \<subseteq> C"
      and bijf: "bij_betw f A B"
  obtains f' where "bij_betw f' C C"
      and "\<And>x. x \<in> A \<Longrightarrow> f' x = f x"
      and "\<And>x. x \<in> C - A \<Longrightarrow> f' x \<in> C - B"
proof -
  from finiteC ABC bijf have "card B = card A"
    unfolding bij_betw_def
    by (auto iff: inj_on_iff_eq_card [symmetric] intro: finite_subset)
  with finiteC ABC bijf have "card (C - A) = card (C - B)"
    by (auto iff: finite_subset card_Diff_subset)
  with finiteC obtain g where bijg: "bij_betw g (C - A) (C - B)"
    by - (drule card_eq_bij, auto)
  from ABC bijf bijg
  obtain f' where bijf': "bij_betw f' C C"
              and f'f: "\<And>x. x \<in> A \<Longrightarrow> f' x = f x"
              and f'g: "\<And>x. x \<in> C - A \<Longrightarrow> f' x = g x"
    by - (drule bij_combine, auto)
  from f'g bijg have "\<And>x. x \<in> C - A \<Longrightarrow> f' x \<in> C - B"
    by (blast dest: bij_betw_onto)
  with bijf' f'f show thesis ..
qed

lemma card_greater:
  assumes finiteA: "finite A"
      and c: "card { x \<in> A. P x } > card { x \<in> A. Q x }"
  obtains C
    where "card ({ x \<in> A. P x } - C) = card { x \<in> A. Q x }"
      and "C \<noteq> {}"
      and "C \<subseteq> { x \<in> A. P x }"
proof -
  let ?PA = "{ x \<in> A . P x }"
  let ?QA = "{ x \<in> A . Q x }"
  from finiteA obtain p where P: "bij_betw p {0..<card ?PA} ?PA"
    using ex_bij_betw_nat_finite[where M="?PA"]
    by (blast intro: finite_subset)
  let ?CN = "{card ?QA..<card ?PA}"
  let ?C = "p ` ?CN"
  have "card ({ x \<in> A. P x } - ?C) = card ?QA"
  proof -
    have nat_add_sub_shuffle: "\<And>x y z. \<lbrakk> (x::nat) > y; x - y = z \<rbrakk> \<Longrightarrow> x - z = y" by simp
    from P have T: "p ` {card ?QA..<card ?PA} \<subseteq> ?PA"
      unfolding bij_betw_def by auto
    from P have "card ?PA - card ?QA = card ?C"
      unfolding bij_betw_def
      by (auto iff: card_image subset_inj_on[where A="?CN"])
    with c have "card ?PA - card ?C = card ?QA" by (rule nat_add_sub_shuffle)
    with finiteA P T have "card (?PA - ?C) = card ?QA"
      unfolding bij_betw_def by (auto iff: finite_subset card_Diff_subset)
    thus ?thesis .
  qed
  moreover
  from P c have "?C \<noteq> {}"
    unfolding bij_betw_def by auto
  moreover
  from P have "?C \<subseteq> { x \<in> A. P x }"
    unfolding bij_betw_def by auto
  ultimately show thesis ..
qed

subsection\<open>Collections of witnesses: @{term "hasw"}, @{term "has"}\<close>

text \<open>

Given a set of cardinality at least $n$, we can find up to $n$ distinct
witnesses. The built-in @{term "card"} function unfortunately satisfies:

\begin{center}
 @{thm [source] "Finite_Set.card_infinite"}: @{thm "Finite_Set.card_infinite"
 [no_vars]}
\end{center}

These lemmas handle the infinite case uniformly.

Thanks to Gerwin Klein suggesting this approach.

\<close>

definition hasw :: "'a list \<Rightarrow> 'a set \<Rightarrow> bool" where
  "hasw xs S \<equiv> set xs \<subseteq> S \<and> distinct xs"

definition has :: "nat \<Rightarrow> 'a set \<Rightarrow> bool" where
  "has n S \<equiv> \<exists>xs. hasw xs S \<and> length xs = n"

declare hasw_def[simp]

lemma hasI[intro]: "hasw xs S \<Longrightarrow> has (length xs) S" by (unfold has_def, auto)

lemma card_has:
  assumes cardS: "card S = n"
  shows "has n S"
proof(cases "n = 0")
  case True thus ?thesis by (simp add: has_def)
next
  case False
  with cardS card_eq_0_iff[where A=S] have finiteS: "finite S" by simp
  show ?thesis
  proof(rule ccontr)
    assume nhas: "\<not> has n S"
    with distinct_card[symmetric]
    have nxs: "\<not> (\<exists> xs. set xs \<subseteq> S \<and> distinct xs \<and> card (set xs) = n)"
      by (auto simp add: has_def)
    from finite_list finiteS
    obtain xs where "S = set xs" by blast
    with cardS nxs show False by auto
  qed
qed

lemma card_has_rev:
  assumes finiteS: "finite S"
  shows "has n S \<Longrightarrow> card S \<ge> n" (is "?lhs \<Longrightarrow> ?rhs")
proof -
  assume ?lhs
  then obtain xs
    where "set xs \<subseteq> S \<and> n = length xs"
      and dxs: "distinct xs" by (unfold has_def hasw_def, blast)
  with card_mono[OF finiteS] distinct_card[OF dxs, symmetric]
  show ?rhs by simp
qed

lemma has_0: "has 0 S" by (simp add: has_def)

lemma has_suc_notempty: "has (Suc n) S \<Longrightarrow> {} \<noteq> S"
  by (clarsimp simp add: has_def)

lemma has_suc_subset: "has (Suc n) S \<Longrightarrow> {} \<subset> S"
  by (rule psubsetI, (simp add: has_suc_notempty)+)

lemma has_notempty_1:
  assumes Sne: "S \<noteq> {}"
  shows "has 1 S"
proof -
  from Sne obtain x where "x \<in> S" by blast
  hence "set [x] \<subseteq> S \<and> distinct [x] \<and> length [x] = 1" by auto
  thus ?thesis by (unfold has_def hasw_def, blast)
qed

lemma has_le_has:
  assumes h: "has n S"
      and nn': "n' \<le> n"
  shows "has n' S"
proof -
  from h obtain xs where "hasw xs S" "length xs = n" by (unfold has_def, blast)
  with nn' set_take_subset[where n="n'" and xs="xs"]
  have "hasw (take n' xs) S" "length (take n' xs) = n'"
    by (simp_all add: min_def, blast+)
  thus ?thesis by (unfold has_def, blast)
qed

lemma has_ge_has_not:
  assumes h: "\<not>has n S"
      and nn': "n \<le> n'"
  shows "\<not>has n' S"
  using h nn' by (blast dest: has_le_has)

lemma has_eq:
  assumes h: "has n S"
      and hn': "\<not>has (Suc n) S"
  shows "card S = n"
proof -
  from h obtain xs
    where xs: "hasw xs S" and lenxs: "length xs = n" by (unfold has_def, blast)
  have "set xs = S"
  proof
    from xs show "set xs \<subseteq> S" by simp
  next
    show "S \<subseteq> set xs"
    proof(rule ccontr)
      assume "\<not> S \<subseteq> set xs"
      then obtain x where "x \<in> S" "x \<notin> set xs" by blast
      with lenxs xs have "hasw (x # xs) S" "length (x # xs) = Suc n" by simp_all
      with hn' show False by (unfold has_def, blast)
    qed
  qed
  with xs lenxs distinct_card show "card S = n" by auto
qed

lemma has_extend_witness:
  assumes h: "has n S"
  shows "\<lbrakk> set xs \<subseteq> S; length xs < n \<rbrakk> \<Longrightarrow> set xs \<subset> S"
proof(induct xs)
  case Nil
  with h has_suc_notempty show ?case by (cases n, auto)
next
  case (Cons x xs)
  have "set (x # xs) \<noteq> S"
  proof
    assume Sxxs: "set (x # xs) = S"
    hence finiteS: "finite S" by auto
    from h obtain xs'
      where Sxs': "set xs' \<subseteq> S"
        and dlxs': "distinct xs' \<and> length xs' = n"
      by (unfold has_def hasw_def, blast)
    with distinct_card have "card (set xs') = n" by auto
    with finiteS Sxs' card_mono have "card S \<ge> n" by auto
    moreover
    from Sxxs Cons card_length[where xs="x # xs"]
    have "card S < n" by auto
    ultimately show False by simp
  qed
  with Cons show ?case by auto
qed

lemma has_extend_witness':
  "\<lbrakk> has n S; hasw xs S; length xs < n \<rbrakk> \<Longrightarrow> \<exists>x. hasw (x # xs) S"
  by (simp, blast dest: has_extend_witness)

lemma has_witness_two:
  assumes hasnS: "has n S"
      and nn': "2 \<le> n"
  shows "\<exists>x y. hasw [x,y] S"
proof -
  have has2S: "has 2 S" by (rule has_le_has[OF hasnS nn'])
  from has_extend_witness'[OF has2S, where xs="[]"]
  obtain x where "x \<in> S" by auto
  with has_extend_witness'[OF has2S, where xs="[x]"]
  show ?thesis by auto
qed

lemma has_witness_three:
  assumes hasnS: "has n S"
      and nn': "3 \<le> n"
  shows "\<exists>x y z. hasw [x,y,z] S"
proof -
  from nn' obtain x y where "hasw [x,y] S"
    using has_witness_two[OF hasnS] by auto
  with nn' show ?thesis
    using has_extend_witness'[OF hasnS, where xs="[x,y]"] by auto
qed

lemma finite_set_singleton_contra:
  assumes finiteS: "finite S"
      and Sne: "S \<noteq> {}"
      and cardS: "card S > 1 \<Longrightarrow> False"
  shows "\<exists>j. S = {j}"
proof -
  from cardS Sne card_0_eq[OF finiteS] have Scard: "card S = 1" by auto
  from has_extend_witness[where xs="[]", OF card_has[OF this]]
  obtain j where "{j} \<subseteq> S" by auto
  from card_seteq[OF finiteS this] Scard show ?thesis by auto
qed

(*<*)
end
(*>*)
