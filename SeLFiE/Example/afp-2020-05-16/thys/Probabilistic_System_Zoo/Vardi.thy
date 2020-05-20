section \<open>Vardi Systems\<close>

(*<*)
theory Vardi
imports 
  Probabilistic_Hierarchy
begin
(*>*)

context notes [[bnf_internals]]
begin
  datatype ('a, 'b, 'k) var0 = PMF "('a \<times> 'b) pmf" | BPS "('a \<times> 'b) set['k]"
end

inductive var_eq :: "('a, 'b, 'k) var0 \<Rightarrow> ('a, 'b, 'k) var0 \<Rightarrow> bool" (infixl "\<sim>" 65) where
  var_eq_reflp[intro]: "x \<sim> x"
| [intro]: "PMF (return_pmf (a, x)) \<sim> BPS (bsingleton (a, x))"
| [intro]: "BPS (bsingleton (a, x)) \<sim> PMF (return_pmf (a, x))"

lemma var_eq_symp: "x \<sim> y \<Longrightarrow> y \<sim> x"
  by (auto elim: var_eq.cases)

lemma var_eq_transp: "x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sim> z"
  by (auto elim!: var_eq.cases)

quotient_type ('a, 'b, 'k) var = "('a, 'b, 'k) var0" / "(\<sim>)"
  by (auto intro: equivpI reflpI sympI transpI  var_eq_symp var_eq_transp)

lift_definition map_var  :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a, 'b, 'k) var \<Rightarrow> ('c, 'd, 'k) var"
  is map_var0
  by (auto elim!: var_eq.cases simp: map_bset_bsingleton)

lift_definition set1_var  :: "('a, 'b, 'k) var \<Rightarrow> 'a set"
  is set1_var0
  by (auto elim!: var_eq.cases)

lift_definition set2_var  :: "('a, 'b, 'k) var \<Rightarrow> 'b set"
  is set2_var0
  by (auto elim!: var_eq.cases)

inductive rel_var :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'b, 'k) var \<Rightarrow> ('c, 'd, 'k) var \<Rightarrow> bool" for R S where
  "set1_var x \<subseteq> {(x, y). R x y} \<Longrightarrow> set2_var x \<subseteq> {(x, y). S x y} \<Longrightarrow>
    rel_var R S (map_var fst fst x) (map_var snd snd x)"

abbreviation (input) "var0_of_gen_emb \<equiv> case_option (BPS bempty) PMF"
abbreviation (input) "var0_of_lts_emb \<equiv> BPS"

lift_definition var_of_gen_emb :: "('a \<times> 'b) pmf option \<Rightarrow> ('a, 'b, 'k) var" is var0_of_gen_emb .
lift_definition var_of_lts_emb :: "('a \<times> 'b) set['k] \<Rightarrow> ('a, 'b, 'k) var" is var0_of_lts_emb .

abbreviation "bisimilar_var \<equiv> bisimilar (\<lambda>R. rel_var (=) R)"

lemma map_var0_eq_BPS_iff[simp]:
  "map_var0 f g z = BPS X \<longleftrightarrow> (\<exists>Y. z = BPS Y \<and> map_bset (map_prod f g) Y = X)"
  by (cases z) auto

lemma map_var0_eq_PMF_iff[simp]:
  "map_var0 f g z = PMF p \<longleftrightarrow> (\<exists>q. z = PMF q \<and> map_pmf (map_prod f g) q = p)"
  by (cases z) auto

lemma "bisimilar_lts s1 s2 x y \<longleftrightarrow> bisimilar_var (var_of_lts_emb o s1) (var_of_lts_emb o s2) x y"
  (is "_ \<longleftrightarrow> bisimilar_var (?emb1 o _) (?emb2 o _) _ _")
unfolding bisimilar_def o_apply proof safe
  fix R assume "R x y" and
    bis: "\<forall>x y. R x y \<longrightarrow> rel_bset (rel_prod (=) R) (s1 x) (s2 y)"
  from \<open>R x y\<close> show "\<exists>R. R x y \<and> (\<forall>x y. R x y \<longrightarrow> rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y)))"
  proof (intro exI[of _ R], safe)
    fix x y
    assume "R x y"
    with bis have *: "rel_bset (rel_prod (=) R) (s1 x) (s2 y)" by blast
    then obtain z where
      "set_bset z \<subseteq> {(x, y). rel_prod (=) R x y}" "map_bset fst z = s1 x" "map_bset snd z = s2 y"
      by (auto simp: bset.in_rel)
    then show "rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))"
      unfolding rel_var.simps by (transfer fixing: z)
        (force simp: bset.map_comp o_def split_beta prod_set_simps
        intro: exI[of _ "BPS (map_bset (\<lambda>((a,b),(c,d)). ((a,c),(b,d))) z)"])
  qed
next
  fix R assume "R x y" and
    bis: "\<forall>x y. R x y \<longrightarrow> rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))"
  from \<open>R x y\<close> show "\<exists>R. R x y \<and> (\<forall>x y. R x y \<longrightarrow> rel_bset (rel_prod (=) R) (s1 x) (s2 y))"
  proof (intro exI[of _ R], safe)
    fix x y
    assume "R x y"
    with bis have "rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))" by blast
    then obtain z where *:
      "set1_var z \<subseteq> {(x, y). x = y}" "set2_var z \<subseteq> {(x, y). R x y}"
      "?emb1 (s1 x) = map_var fst fst z" "?emb2 (s2 y) = map_var snd snd z"
      by (auto simp: rel_var.simps)
    then show "rel_bset (rel_prod (=) R) (s1 x) (s2 y)"
      by (transfer fixing: s1 s2) (fastforce simp: bset.in_rel bset.map_comp o_def map_pmf_eq_return_pmf_iff
        split_beta[abs_def] map_prod_def subset_eq split_beta prod_set_defs elim!: var_eq.cases
        intro: exI[of _ "map_bset (\<lambda>((a,b),(c,d)). ((a,c),(b,d))) z" for z]
          exI[of _ "bsingleton ((a,c),(b,d))" for a b c d])
  qed
qed

lemma "bisimilar_gen s1 s2 x y \<longleftrightarrow> bisimilar_var (var_of_gen_emb o s1) (var_of_gen_emb o s2) x y"
  (is "_ \<longleftrightarrow> bisimilar_var (?emb1 o _) (?emb2 o _) _ _")
unfolding bisimilar_def o_apply proof safe
  fix R assume "R x y" and
    bis: "\<forall>x y. R x y \<longrightarrow> rel_option (rel_pmf (rel_prod (=) R)) (s1 x) (s2 y)"
  from \<open>R x y\<close> show "\<exists>R. R x y \<and> (\<forall>x y. R x y \<longrightarrow> rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y)))"
  proof (intro exI[of _ R], safe)
    fix x y
    assume "R x y"
    with bis have *: "rel_option (rel_pmf (rel_prod (=) R)) (s1 x) (s2 y)" by blast
    then show "rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))"
    proof (cases "s1 x" "s2 y" rule: option.exhaust[case_product option.exhaust])
      case None_None then show ?thesis unfolding rel_var.simps
        by (transfer fixing: s1 s2) (auto simp: bempty.rep_eq intro!: exI[of _ "BPS bempty"])
    next
      case (Some_Some p q)
      with * obtain z where
        "set_pmf z \<subseteq> {(x, y). rel_prod (=) R x y}" "map_pmf fst z = p" "map_pmf snd z = q"
        by (auto simp: pmf.in_rel)
      with Some_Some show ?thesis unfolding rel_var.simps
        by (transfer fixing: s1 s2 z) (force simp: pmf.map_comp o_def split_beta prod_set_simps
          intro: exI[of _ "PMF (map_pmf (\<lambda>((a,b),(c,d)). ((a,c),(b,d))) z)"])
    qed auto
  qed
next
  fix R assume "R x y" and
    bis: "\<forall>x y. R x y \<longrightarrow> rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))"
  from \<open>R x y\<close> show "\<exists>R. R x y \<and> (\<forall>x y. R x y \<longrightarrow>
     rel_option (rel_pmf (rel_prod (=) R)) (s1 x) (s2 y))"
  proof (intro exI[of _ R], safe)
    fix x y
    assume "R x y"
    with bis have "rel_var (=) R (?emb1 (s1 x)) (?emb2 (s2 y))" by blast
    then obtain z where *:
        "set1_var z \<subseteq> {(x, y). x = y}" "set2_var z \<subseteq> {(x, y). R x y}"
        "?emb1 (s1 x) = map_var fst fst z" "?emb2 (s2 y) = map_var snd snd z"
        by (auto simp: rel_var.simps)
    then show "rel_option (rel_pmf (rel_prod (=) R)) (s1 x) (s2 y)"
    proof (cases "s1 x" "s2 y" rule: option.exhaust[case_product option.exhaust])
      case Some_None
      with * show ?thesis by transfer (auto simp: bempty.rep_eq elim!: var_eq.cases)
    next
      case None_Some
      with * show ?thesis by transfer (auto elim!: var_eq.cases)
    next
      case (Some_Some p q)
      with * show ?thesis
        by transfer (fastforce simp: subset_eq split_beta prod_set_defs
          elim!: var_eq.cases intro!: rel_pmf_reflI)
    qed simp
  qed
qed

(*<*)
end
(*>*)
