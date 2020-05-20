(*
Author:  Akihisa Yamada (2018-2019)
License: LGPL (see file COPYING.LESSER)
*)
section \<open>Binary Relations\<close>

text \<open>We start with basic properties of binary relations.\<close>

theory Binary_Relations
imports Main
(* uses mainly concepts from the theories Complete_Partial_Order, Wellfounded, Partial_Function *)
begin

text \<open>Below we introduce an Isabelle-notation for $\{ \ldots x\ldots \mid x \in X \}$.\<close>

syntax
  "_range" :: "'a \<Rightarrow> pttrn \<Rightarrow> 'a set" ("(1{_ /|./ _})")
  "_image" :: "'a \<Rightarrow> pttrn \<Rightarrow> 'a set \<Rightarrow> 'a set"  ("(1{_ /|./ (_/ \<in> _)})")
translations
  "{e |. p}" \<rightleftharpoons> "CONST range (\<lambda>p. e)"
  "{e |. p \<in> A}" \<rightleftharpoons> "CONST image (\<lambda>p. e) A"

lemma image_constant:
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i = y"
  shows "f ` I = (if I = {} then {} else {y})"
  using assms by auto


subsection \<open>Various Definitions\<close>

text \<open>Here we introduce various definitions for binary relations.
The first one is our abbreviation for the dual of a relation.\<close>

abbreviation(input) dual ("(_\<^sup>-)" [1000] 1000) where "r\<^sup>- x y \<equiv> r y x"

lemma conversep_as_dual[simp]: "conversep r = r\<^sup>-" by auto

text \<open>Monotonicity is already defined in the library.\<close>
lemma monotone_dual: "monotone r s f \<Longrightarrow> monotone r\<^sup>- s\<^sup>- f"
  by (auto simp: monotone_def)

lemma monotone_id: "monotone r r id"
  by (auto simp: monotone_def)

text \<open>So is the chain, but it is somehow hidden. We reactivate it.\<close>
abbreviation "chain \<equiv> Complete_Partial_Order.chain"

context fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) begin

text \<open>Here we define the following notions in a standard manner:
(upper) bounds of a set:\<close>
definition "bound X b \<equiv> \<forall>x \<in> X. x \<sqsubseteq> b"

lemma boundI[intro!]: "(\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> bound X b"
  and boundE[elim]: "bound X b \<Longrightarrow> ((\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: bound_def)

lemma bound_empty: "bound {} = (\<lambda>x. True)" by auto
lemma bound_insert[simp]: "bound (insert x X) b \<longleftrightarrow> x \<sqsubseteq> b \<and> bound X b" by auto

lemma bound_cmono: assumes "X \<subseteq> Y" shows "bound Y x \<Longrightarrow> bound X x"
  using assms by auto

text \<open>Extreme (greatest) elements in a set:\<close>
definition "extreme X e \<equiv> e \<in> X \<and> (\<forall>x \<in> X. x \<sqsubseteq> e)"

lemma extremeI[intro]: "e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> extreme X e"
  and extremeD: "extreme X e \<Longrightarrow> e \<in> X" "extreme X e \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e)"
  and extremeE[elim]: "extreme X e \<Longrightarrow> (e \<in> X \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> e) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (auto simp: extreme_def)

lemma extreme_UNIV[simp]: "extreme UNIV t \<longleftrightarrow> (\<forall>x. x \<sqsubseteq> t)" by auto

lemma extremes_equiv: "extreme X b \<Longrightarrow> extreme X c \<Longrightarrow> b \<sqsubseteq> c \<and> c \<sqsubseteq> b" by auto

text \<open>Directed sets:\<close>
definition "directed X \<equiv> \<forall>x \<in> X. \<forall> y \<in> X. \<exists>z \<in> X. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"

lemma directedE:
  assumes "directed X" and "x \<in> X" and "y \<in> X"
    and "\<And>z. z \<in> X \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: directed_def)

lemma directedI[intro]:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> \<exists>z \<in> X. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  shows "directed X" 
  using assms by (auto simp: directed_def)

lemma chain_imp_directed: "chain (\<sqsubseteq>) X \<Longrightarrow> directed X"
  by (intro directedI, auto elim: chainE)

text \<open>And sets of elements which are self-related:\<close>
definition "reflexive_on X \<equiv> \<forall>x \<in> X. x \<sqsubseteq> x"

lemma reflexive_onI[intro]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> x" shows "reflexive_on X" using assms reflexive_on_def by auto

lemma reflexive_onE[elim]:
  assumes "reflexive_on X" and "(\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> x) \<Longrightarrow> thesis" shows thesis
  using assms reflexive_on_def by auto

lemma chain_imp_reflexive: "chain (\<sqsubseteq>) X \<Longrightarrow> reflexive_on X" by (auto elim: chainE)

end

context fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

text \<open>Now suprema and infima are given uniformly as follows. \<close>
abbreviation "extreme_bound X \<equiv> extreme (\<lambda>x y. y \<sqsubseteq> x) {b. bound (\<sqsubseteq>) X b}"

lemma extreme_boundI[intro]:
  assumes "\<And>b. bound (\<sqsubseteq>) X b \<Longrightarrow> s \<sqsubseteq> b" and "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> s"
  shows "extreme_bound X s"
  using assms by auto

lemma extreme_bound_mono:
  assumes XY: "X \<subseteq> Y"
    and bX: "extreme_bound X bX"
    and bY: "extreme_bound Y bY"
  shows "bX \<sqsubseteq> bY"
proof-
  have "bound (\<sqsubseteq>) X bY" using XY bY by force
  with bX show ?thesis by auto
qed

lemma extreme_bound_iff:
  shows "extreme_bound X b \<longleftrightarrow> (\<forall>c. (\<forall>x\<in>X. x \<sqsubseteq> c) \<longrightarrow> b \<sqsubseteq> c) \<and> (\<forall>x \<in> X. x \<sqsubseteq> b)"
  by (auto simp: extreme_def)

lemma extreme_bound_singleton_refl[simp]:
  "extreme_bound {x} x \<longleftrightarrow> x \<sqsubseteq> x" by auto

lemma extreme_bound_equiv: "extreme_bound X b \<Longrightarrow> c \<in> X \<Longrightarrow> b \<sqsubseteq> c \<Longrightarrow> c \<sqsubseteq> b"
  by auto

lemma extreme_bound_image_const:
  "x \<sqsubseteq> x \<Longrightarrow> C \<noteq> {} \<Longrightarrow> (\<And>i. i \<in> C \<Longrightarrow> f i = x) \<Longrightarrow> extreme_bound (f ` C) x"
  by (auto simp: image_constant)

lemma extreme_bound_UN_const:
  "x \<sqsubseteq> x \<Longrightarrow> C \<noteq> {} \<Longrightarrow> (\<And>i y. i \<in> C \<Longrightarrow> P i y \<longleftrightarrow> x = y) \<Longrightarrow>
  extreme_bound (\<Union>i\<in>C. {y. P i y}) x"
  by auto

end

context
  fixes r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma fun_ordI: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> fun_ord (\<sqsubseteq>) f g"
  and fun_ordD: "fun_ord (\<sqsubseteq>) f g \<Longrightarrow> f x \<sqsubseteq> g x"
  by (auto simp: fun_ord_def)

lemma dual_fun_ord: "(fun_ord (\<sqsubseteq>))\<^sup>- = fun_ord (\<sqsubseteq>)\<^sup>-" by (auto intro!:ext simp: fun_ord_def)

lemma fun_extreme_bound_iff:
  shows "extreme_bound (fun_ord (\<sqsubseteq>)) F e \<longleftrightarrow> (\<forall>x. extreme_bound (\<sqsubseteq>) {f x |. f \<in> F} (e x))" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI allI extreme_boundI fun_ordI)
  fix f x
  assume ?r
  then have e: "extreme_bound (\<sqsubseteq>) {f x |. f \<in> F} (e x)" by auto
  show "f \<in> F \<Longrightarrow> f x \<sqsubseteq> e x" using extremeD(1)[OF e] by auto
  assume "bound (fun_ord (\<sqsubseteq>)) F f"
  then have "bound (\<sqsubseteq>) {f x |. f \<in> F} (f x)" by (auto simp: fun_ord_def)
  with e show "e x \<sqsubseteq> f x" by auto
next
  fix x y
  assume l: ?l
  from l have e: "f \<in> F \<Longrightarrow> f x \<sqsubseteq> e x" for f by (auto dest!:extremeD simp: fun_ord_def)
  then show "y \<in> {f x |. f \<in> F} \<Longrightarrow> y \<sqsubseteq> e x" by auto
  assume "bound (\<sqsubseteq>) {f x |. f \<in> F} y"
  with extremeD(1)[OF l] have "bound (fun_ord (\<sqsubseteq>)) F (e(x:=y))" by (auto simp: fun_ord_def elim!:boundE)
  with l have "fun_ord (\<sqsubseteq>) e (e(x:=y))" by auto
  from fun_ordD[OF this, of x]
  show "e x \<sqsubseteq> y" by auto
qed

context
  fixes ir :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<preceq>" 50)
  fixes f
  assumes mono: "monotone (\<preceq>) (\<sqsubseteq>) f"
begin

lemma monotone_chain_image:
  assumes chain: "chain (\<preceq>) C" shows "chain (\<sqsubseteq>) (f ` C)"
proof (rule chainI)
  fix x y
  assume "x \<in> f ` C" and "y \<in> f ` C"
  then obtain i j where ij: "i \<in> C" "j \<in> C" and [simp]: "x = f i" "y = f j" by auto
  from chain ij have "i \<preceq> j \<or> j \<preceq> i" by (auto elim: chainE)
  with ij mono show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by (elim disjE, auto dest: monotoneD) 
qed

lemma monotone_directed_image:
  assumes dir: "directed (\<preceq>) D" shows "directed (\<sqsubseteq>) (f ` D)"
proof (rule directedI, safe)
  fix x y assume "x \<in> D" and "y \<in> D"
  with dir obtain z where z: "z \<in> D" and "x \<preceq> z" and "y \<preceq> z" by (auto elim: directedE)
  with mono have "f x \<sqsubseteq> f z" and "f y \<sqsubseteq> f z" by (auto dest: monotoneD)
  with z show "\<exists>fz \<in> f ` D. f x \<sqsubseteq> fz \<and> f y \<sqsubseteq> fz" by auto
qed

context
  fixes e C
  assumes e: "extreme (\<preceq>) C e"
begin

lemma monotone_extreme_imp_extreme_bound:
  shows "extreme_bound (\<sqsubseteq>) (f ` C) (f e)"
  using monotoneD[OF mono] e
  by (auto simp: image_def intro!:extreme_boundI elim!:extremeE boundE)

lemma monotone_extreme_extreme_boundI:
  "x = f e \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` C) x"
  using monotone_extreme_imp_extreme_bound by auto

end

end

end

subsection \<open>Locales for Binary Relations\<close>

text \<open>We now define basic properties of binary relations,
in form of \emph{locales}~\cite{Kammuller00,locale}.\<close>

subsubsection \<open>Syntactic Locales\<close>

text \<open>The following locales do not assume anything, but provide infix notations for
relations. \<close>

locale less_eq_syntax = fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

locale less_syntax = fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)

locale equivalence_syntax = fixes equiv :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sim>" 50)
begin

abbreviation equiv_class ("[_]\<^sub>\<sim>") where "[x]\<^sub>\<sim> \<equiv> { y. x \<sim> y }"

end

text \<open>Next ones introduce abbreviations for dual etc.
To avoid needless constants, one should be careful when declaring them as sublocales.\<close>

locale less_eq_dualize = less_eq_syntax
begin

abbreviation (input) greater_eq (infix "\<sqsupseteq>" 50) where "x \<sqsupseteq> y \<equiv> y \<sqsubseteq> x"
abbreviation (input) equiv (infix "\<sim>" 50) where "x \<sim> y \<equiv> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"

lemma equiv_sym[sym]: "x \<sim> y \<Longrightarrow> y \<sim> x" by auto

end

locale less_dualize = less_syntax
begin

abbreviation (input) greater (infix "\<sqsupset>" 50) where "x \<sqsupset> y \<equiv> y \<sqsubset> x"

end

subsubsection \<open>Basic Properties of Relations\<close>

text \<open>In the following we define basic properties in form of locales.\<close>

locale reflexive = less_eq_syntax + assumes refl[iff]: "x \<sqsubseteq> x"
begin

lemma eq_implies: "x = y \<Longrightarrow> x \<sqsubseteq> y" by auto

lemma extreme_singleton[simp]: "extreme (\<sqsubseteq>) {x} y \<longleftrightarrow> x = y" by auto

lemma extreme_bound_singleton[iff]: "extreme_bound (\<sqsubseteq>) {x} x" by auto

end
lemmas reflexiveI[intro] = reflexive.intro

locale irreflexive = less_syntax + assumes irrefl[iff]: "\<not> x \<sqsubset> x"
begin

lemma implies_not_eq: "x \<sqsubset> y \<Longrightarrow> x \<noteq> y" by auto

end
lemmas irreflexiveI[intro] = irreflexive.intro

locale transitive = less_eq_syntax + assumes trans[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
lemmas [intro?] = transitive.intro

locale symmetric = equivalence_syntax + assumes sym[sym]: "x \<sim> y \<Longrightarrow> y \<sim> x"
begin

lemma dual_sym: "(\<sim>)\<^sup>- = (\<sim>)" using sym by auto

end
lemmas [intro] = symmetric.intro

locale antisymmetric = less_eq_syntax + assumes antisym[dest]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
begin

interpretation less_eq_dualize. 

lemma equiv_iff_eq_refl: "x \<sim> y \<longleftrightarrow> x = y \<and> y \<sqsubseteq> y" by auto

lemma extreme_unique: "extreme (\<sqsubseteq>) X x \<Longrightarrow> extreme (\<sqsubseteq>) X y \<longleftrightarrow> x = y"
  by (auto elim!: extremeE)

lemma ex_extreme_iff_ex1: "Ex (extreme (\<sqsubseteq>) X) \<longleftrightarrow> Ex1 (extreme (\<sqsubseteq>) X)" by (auto simp: extreme_unique)

lemma ex_extreme_iff_the:
   "Ex (extreme (\<sqsubseteq>) X) \<longleftrightarrow> extreme (\<sqsubseteq>) X (The (extreme (\<sqsubseteq>) X))"
  apply (rule iffI)
  apply (rule  theI')
  using extreme_unique by auto

end
lemmas antisymmetricI[intro] = antisymmetric.intro

text \<open>The following notion is new, generalizing antisymmetry and transitivity.\<close>

locale semiattractive = less_eq_syntax +
  assumes attract: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z"
begin

interpretation less_eq_dualize.

lemma equiv_trans:
  assumes xy: "x \<sim> y" and yz: "y \<sim> z" shows "x \<sim> z"
  using attract[of y x z] attract[of y z x] xy yz by auto

lemma extreme_bound_quasi_const:
  assumes C: "C \<noteq> {}" and const: "\<forall>y \<in> C. y \<sim> x" shows "extreme_bound (\<sqsubseteq>) C x"
proof (intro extreme_boundI)
  from C obtain c where c: "c \<in> C" by auto
  with const have cx: "c \<sim> x" by auto
  fix b assume "bound (\<sqsubseteq>) C b"
  with c have cb: "c \<sqsubseteq> b" by auto
  from attract[of c x b] cb cx show "x \<sqsubseteq> b" by auto
next
  fix c assume "c \<in> C"
  with const show "c \<sqsubseteq> x" by auto
qed

lemma extreme_bound_quasi_const_iff:
  assumes C: "C \<noteq> {}" and const: "\<forall>z \<in> C. z \<sim> x"
  shows "extreme_bound (\<sqsubseteq>) C y \<longleftrightarrow> x \<sim> y"
proof (intro iffI)
  assume "extreme_bound (\<sqsubseteq>) C y"
  with const show "x \<sim> y"
    by (metis C extreme_bound_quasi_const extremes_equiv)
next
  assume xy: "x \<sim> y"
  with const equiv_trans[of _ x y] have Cy: "\<forall>z \<in> C. z \<sim> y" by auto
  show "extreme_bound (\<sqsubseteq>) C y"
    using extreme_bound_quasi_const[OF C Cy].
qed

end

locale attractive = semiattractive + dual: semiattractive "(\<sqsubseteq>)\<^sup>-"

sublocale transitive \<subseteq> attractive by (unfold_locales, auto dest: trans)

sublocale antisymmetric \<subseteq> attractive by (unfold_locales, auto)

locale asymmetric = irreflexive + strict: antisymmetric "(\<sqsubset>)"
begin

lemma asym[trans]: "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> thesis" by auto

end

context
  fixes less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50)
begin

lemma asymmetricI[intro]:
  assumes "\<And>x y. x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False" 
  shows "asymmetric (\<sqsubset>)"
  apply unfold_locales using assms by auto

lemma asymmetric_def': "asymmetric (\<sqsubset>) \<equiv> \<forall>x y. \<not> (x \<sqsubset> y \<and> y \<sqsubset> x)"
  by (auto simp: atomize_eq dest!: asymmetric.asym)

end

locale well_founded = less_syntax +
  assumes induct: "\<And>P a. (\<And>x. (\<And>y. y \<sqsubset> x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"
begin

lemma wfP[intro!]: "wfP (\<sqsubset>)" using induct wfPUNIVI by blast

sublocale asymmetric
proof (intro asymmetricI notI)
  show "x \<sqsubset> y \<Longrightarrow> y \<sqsubset> x \<Longrightarrow> False" for x y by (induct x arbitrary: y rule: induct)
qed

end

subsubsection \<open>Combined Properties\<close>

text \<open>Some combinations of the above basic properties are given names.\<close>

locale quasi_order = reflexive + transitive

locale near_order = antisymmetric + transitive

locale pseudo_order = reflexive + antisymmetric
begin

lemma equiv_eq[simp]: "x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longleftrightarrow> x = y" by auto

lemma extreme_bound_singleton_eq[simp]: "extreme_bound (\<sqsubseteq>) {x} y \<longleftrightarrow> x = y" by auto

lemma eq_iff: "x = y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x" by auto

lemma extreme_order_iff_eq[simp]: "extreme (\<sqsubseteq>) {x. x \<sqsubseteq> e} s \<longleftrightarrow> e = s" by auto

end

locale partial_order = quasi_order + antisymmetric

sublocale partial_order \<subseteq> pseudo_order + near_order ..

locale strict_order = irreflexive + transitive "(\<sqsubset>)"

sublocale strict_order \<subseteq> asymmetric by (auto dest: trans)
sublocale strict_order \<subseteq> near_order "(\<sqsubset>)" ..

locale well_founded_order = well_founded + transitive "(\<sqsubset>)"

sublocale well_founded_order \<subseteq> strict_order ..

locale tolerance = equivalence_syntax + reflexive "(\<sim>)" + symmetric "(\<sim>)"

locale partial_equivalence = equivalence_syntax + symmetric "(\<sim>)" + transitive "(\<sim>)"

locale equivalence = equivalence_syntax + symmetric "(\<sim>)" + quasi_order "(\<sim>)"

sublocale equivalence \<subseteq> partial_equivalence ..

text \<open>Some combinations lead to uninteresting relations.\<close>

proposition reflexive_irreflexive_is_empty:
  assumes "reflexive r" and "irreflexive r"
  shows "r = (\<lambda>x y. False)"
proof(intro ext iffI)
  interpret irreflexive r + reflexive r using assms by auto
  fix x y
  assume "r x y"
  with irrefl have "x \<noteq> y" by auto
  with refl show False by auto
qed auto

proposition symmetric_antisymmetric_imp_eq:
  assumes "symmetric r" and "antisymmetric r"
  shows "r x y \<Longrightarrow> x = y"
proof-
  interpret symmetric r + antisymmetric r using assms by auto
  fix x y
  assume "r x y"
  with sym[OF this] show "x = y" by auto
qed

proposition nontolerance:
  fixes r (infix "\<bowtie>" 50)
  shows "irreflexive (\<bowtie>) \<and> symmetric (\<bowtie>) \<longleftrightarrow> tolerance (\<lambda>x y. \<not> x \<bowtie> y)"
proof safe
  assume "irreflexive (\<bowtie>)" and "symmetric (\<bowtie>)"
  then interpret irreflexive "(\<bowtie>)" + symmetric "(\<bowtie>)".
  show "tolerance (\<lambda>x y. \<not> x \<bowtie> y)" by (unfold_locales, auto dest: sym)
next
  assume "tolerance (\<lambda>x y. \<not> x \<bowtie> y)"
  then interpret tolerance "\<lambda>x y. \<not> x \<bowtie> y".
  show "irreflexive (\<bowtie>)" by auto
  show "symmetric (\<bowtie>)" using sym by auto
qed

proposition irreflexive_transitive_symmetric_is_empty:
  assumes "irreflexive r" and "transitive r" and "symmetric r"
  shows "r = (\<lambda>x y. False)"
proof(intro ext iffI)
  interpret strict_order r using assms by (unfold strict_order_def, auto)
  interpret symmetric r using assms by auto
  fix x y
  assume "r x y"
  also note sym[OF this]
  finally have "r x x".
  then show False by auto
qed auto

subsection \<open>Totality\<close>

locale total = less_syntax + assumes total: "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x"
begin

lemma cases[case_names less eq greater]:
  assumes "x \<sqsubset> y \<Longrightarrow> P" and "x = y \<Longrightarrow> P" and "y \<sqsubset> x \<Longrightarrow> P"
  shows "P" using total assms by auto

lemma neqE: "x \<noteq> y \<Longrightarrow> (x \<sqsubset> y \<Longrightarrow> P) \<Longrightarrow> (y \<sqsubset> x \<Longrightarrow> P) \<Longrightarrow> P" by (cases x y rule: cases, auto)

end
lemmas totalI[intro] = total.intro

text \<open>Totality is negated antisymmetry \cite[Proposition 2.2.4]{Schmidt1993}.\<close>
proposition total_iff_neg_antisymmetric:
  fixes less (infix "\<sqsubset>" 50)
  shows "total (\<sqsubset>) \<longleftrightarrow> antisymmetric (\<lambda>x y. \<not> x \<sqsubset> y)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI totalI antisymmetricI)
  assume ?l
  then interpret total.
  fix x y
  assume "\<not> x \<sqsubset> y" and "\<not> y \<sqsubset> x"
  then show "x = y" by (cases x y rule: cases, auto)
next
  assume ?r
  then interpret neg: antisymmetric "(\<lambda>x y. \<not> x \<sqsubset> y)".
  fix x y
  show "x \<sqsubset> y \<or> x = y \<or> y \<sqsubset> x" using neg.antisym by auto
qed

locale total_irreflexive = total + irreflexive
begin

lemma neq_iff: "x \<noteq> y \<longleftrightarrow> x \<sqsubset> y \<or> y \<sqsubset> x" by (auto elim:neqE)

end

locale total_reflexive = reflexive + weak: total "(\<sqsubseteq>)"
begin

lemma comparable: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by (cases x y rule:weak.cases, auto)

lemma comparable_cases[case_names le ge]:
  assumes "x \<sqsubseteq> y \<Longrightarrow> P" and "y \<sqsubseteq> x \<Longrightarrow> P" shows "P" using assms comparable by auto

lemma chain_UNIV: "chain (\<sqsubseteq>) UNIV" by (intro chainI comparable)

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma total_reflexiveI[intro]:
  assumes "\<And>x y. x \<sqsubseteq> y \<or> y \<sqsubseteq> x" shows "total_reflexive (\<sqsubseteq>)"
  using assms by (unfold_locales, auto)

lemma total_reflexive_def': "total_reflexive (\<sqsubseteq>) \<equiv> \<forall>x y. x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  by (unfold atomize_eq, auto dest: total_reflexive.comparable)

end

locale total_pseudo_order = total_reflexive + antisymmetric
begin

sublocale pseudo_order ..

lemma not_weak_iff: "\<not> y \<sqsubseteq> x \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y" by (cases x y rule:comparable_cases, auto)

end

locale total_quasi_order = total_reflexive + transitive
begin

sublocale quasi_order ..

end

locale total_order = total_quasi_order + antisymmetric
begin

sublocale partial_order + total_pseudo_order ..

end

text \<open>A strict total order defines a total weak order, so we will formalize
it after giving locales for pair of weak and strict parts.\<close>

subsection \<open>Order Pairs\<close>

locale compatible_ordering = less_eq_syntax + less_syntax + reflexive "(\<sqsubseteq>)" + irreflexive "(\<sqsubset>)" +
  assumes weak_strict_trans[trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<sqsubset> z"
  assumes strict_weak_trans[trans]: "x \<sqsubset> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubset> z"
  assumes strict_implies_weak: "x \<sqsubset> y \<Longrightarrow> x \<sqsubseteq> y"
begin

text \<open>The strict part is necessarily transitive.\<close>

sublocale strict: transitive "(\<sqsubset>)"
  using weak_strict_trans[OF strict_implies_weak] by unfold_locales

text \<open>The following sequence of declarations are in order to obtain fact names in a manner
similar to the Isabelle/HOL facts of orders.\<close>

interpretation strict_order "(\<sqsubset>)" ..

sublocale strict: near_order "(\<sqsubset>)" by unfold_locales

sublocale asymmetric "(\<sqsubset>)" by unfold_locales

sublocale strict_order "(\<sqsubset>)" ..

thm strict.antisym strict.trans asym irrefl

lemma strict_implies_not_weak: "x \<sqsubset> y \<Longrightarrow> \<not> y \<sqsubseteq> x" by (auto dest: strict_weak_trans)

end

locale attractive_ordering = compatible_ordering + attractive

locale pseudo_ordering = compatible_ordering + antisymmetric
begin

sublocale pseudo_order + attractive_ordering ..

end

locale quasi_ordering = compatible_ordering + transitive
begin

sublocale quasi_order + attractive_ordering ..

end

locale partial_ordering = compatible_ordering + near_order
begin

sublocale partial_order + pseudo_ordering + quasi_ordering ..

end

locale well_founded_ordering = quasi_ordering + well_founded

locale total_ordering = compatible_ordering + total_order
begin

sublocale partial_ordering ..

end

locale strict_total_ordering = partial_ordering + total "(\<sqsubset>)"
begin

sublocale total_irreflexive "(\<sqsubset>)" ..

sublocale total_reflexive "(\<sqsubseteq>)"
proof
  fix x y show "x \<sqsubseteq> y \<or> y \<sqsubseteq> x" by (cases x y rule: cases, auto dest: strict_implies_weak)
qed

sublocale total_ordering ..

sublocale old: ordering "(\<sqsubseteq>)" "(\<sqsubset>)"
proof-
  have "a \<sqsubseteq> b \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<sqsubset> b" for a b
    by (cases a b rule: cases, auto dest: strict_implies_weak)
  then show "ordering (\<sqsubseteq>) (\<sqsubset>)"
    by (unfold_locales, auto dest:strict_implies_weak trans)
qed

lemma not_weak[simp]: "\<not> x \<sqsubseteq> y \<longleftrightarrow> y \<sqsubset> x" by (simp add: not_weak_iff old.strict_iff_order)

lemma not_strict[simp]: "\<not> x \<sqsubset> y \<longleftrightarrow> y \<sqsubseteq> x" by (auto simp: old.strict_iff_order)

end


text \<open>A locale which defines an equivalence relation. Be careful when declaring simp rules etc.,
as the equivalence will often be rewritten to equality.\<close>

locale quasi_order_equivalence = quasi_order + equivalence_syntax +
  assumes equiv_def: "x \<sim> y \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
begin

sublocale equiv: equivalence by (unfold_locales, auto simp: equiv_def dest: trans)

lemma [trans]:
  shows equiv_weak_trans: "x \<sim> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
    and weak_equiv_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sqsubseteq> z"
  by (auto simp: equiv_def dest: trans)

lemma extreme_order_iff_equiv[simp]: "extreme (\<sqsubseteq>) {x. x \<sqsubseteq> e} y \<longleftrightarrow> e \<sim> y"
  by (auto simp: equiv_def intro!: extremeI dest: trans)

lemma extreme_bound_iff_equiv:
  assumes bX: "extreme_bound (\<sqsubseteq>) X b" shows "extreme_bound (\<sqsubseteq>) X c \<longleftrightarrow> b \<sim> c"
proof(rule iffI)
  from bX have bX: "bound (\<sqsubseteq>) X b" and leastb: "\<And>x. bound (\<sqsubseteq>) X x \<Longrightarrow> b \<sqsubseteq> x" by auto
  { fix c assume "extreme_bound (\<sqsubseteq>) X c"
    then have cbounds: "bound (\<sqsubseteq>) X c" and leastc: "\<And>b. bound (\<sqsubseteq>) X b \<Longrightarrow> c \<sqsubseteq> b" by auto
    from leastb[OF cbounds] leastc[OF bX] show "b \<sim> c" by (auto simp: equiv_def)
  }
  { fix c assume bc: "b \<sim> c"
    show "extreme_bound (\<sqsubseteq>) X c"
    proof(intro extreme_boundI)
      fix x assume "x \<in> X"
      with bX have "x \<sqsubseteq> b" by auto
      with bc show "x \<sqsubseteq> c" by (auto dest: trans simp: equiv_def)
    next
      fix x assume "bound (\<sqsubseteq>) X x"
      from leastb[OF this] bc show "c \<sqsubseteq> x" by (auto dest: trans simp: equiv_def)
    qed
  }
qed

lemma extremes_are_equiv: "extreme (\<sqsubseteq>) X x \<Longrightarrow> extreme (\<sqsubseteq>) X y \<Longrightarrow> x \<sim> y"
  by (auto simp: equiv_def)

end

locale quasi_ordering_equivalence = compatible_ordering + quasi_order_equivalence
begin

lemma [trans]:
  shows equiv_strict_trans: "x \<sim> y \<Longrightarrow> y \<sqsubset> z \<Longrightarrow> x \<sqsubset> z"
    and strict_equiv_trans: "x \<sqsubset> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<sqsubset> z"
  by (auto simp: equiv_def dest: weak_strict_trans strict_weak_trans)

end

subsection \<open>Relating to Classes\<close>

text \<open>In Isabelle 2019 (and earlier), we should declare sublocales in class before declaring dual
sublocales, since otherwise facts would be prefixed by ``dual.dual.''\<close>

context ord begin

abbreviation upper_bound where "upper_bound \<equiv> bound (\<le>)"

abbreviation least where "least \<equiv> extreme (\<lambda>x y. y \<le> x)"

abbreviation lower_bound where "lower_bound \<equiv> bound (\<lambda>x y. y \<le> x)"

abbreviation greatest where "greatest \<equiv> extreme (\<le>)"

abbreviation supremum where "supremum \<equiv> extreme_bound (\<le>)"

abbreviation infimum where "infimum \<equiv> extreme_bound (\<lambda>x y. y \<le> x)"

lemma Least_eq_The_least: "Least P = The (least {x. P x})"
  by (auto simp: Least_def extreme_def[unfolded atomize_eq, THEN ext])

lemma Greatest_eq_The_greatest: "Greatest P = The (greatest {x. P x})"
  by (auto simp: Greatest_def extreme_def[unfolded atomize_eq, THEN ext])

end

lemma fun_ord_le: "fun_ord (\<le>) = (\<le>)" by (intro ext, simp add: fun_ord_def le_fun_def)
lemma fun_ord_ge: "fun_ord (\<ge>) = (\<ge>)" by (intro ext, simp add: fun_ord_def le_fun_def)

lemmas fun_supremum_iff = fun_extreme_bound_iff[of "(\<le>)", unfolded fun_ord_le]
lemmas fun_infimum_iff = fun_extreme_bound_iff[of "(\<ge>)", unfolded fun_ord_ge]

class compat = ord + assumes "compatible_ordering (\<le>) (<)"
begin

sublocale order: compatible_ordering using compat_axioms unfolding class.compat_def.

end

text \<open>We should have imported locale-based facts in classes, e.g.:\<close>
thm order.trans order.strict.trans order.refl order.irrefl order.asym order.extreme_bound_singleton

class attractive_order = ord + assumes "attractive_ordering (\<le>) (<)"
begin

interpretation order: attractive_ordering
  using attractive_order_axioms unfolding class.attractive_order_def.

subclass compat ..

sublocale order: attractive_ordering ..

end

thm order.extreme_bound_quasi_const

class psorder = ord + assumes "pseudo_ordering (\<le>) (<)"
begin

text \<open>We need to declare subclasses before sublocales in order to preserve facts for superclasses.\<close>

interpretation order: pseudo_ordering using psorder_axioms unfolding class.psorder_def.

subclass attractive_order ..

sublocale order: pseudo_ordering ..

end

class qorder = ord + assumes "quasi_ordering (\<le>) (<)"
begin

interpretation order: quasi_ordering using qorder_axioms unfolding class.qorder_def.

subclass attractive_order ..

sublocale order: quasi_ordering ..

end

class porder = ord + assumes "partial_ordering (\<le>) (<)"
begin

interpretation order: partial_ordering using porder_axioms unfolding class.porder_def.

subclass psorder ..
subclass qorder ..

sublocale order: partial_ordering ..

end

class wf_qorder = ord + assumes "well_founded_ordering (\<le>) (<)"
begin

interpretation order: well_founded_ordering using wf_qorder_axioms unfolding class.wf_qorder_def.

subclass qorder ..

sublocale order: well_founded_ordering ..

end

class totalorder = ord + assumes "total_ordering (\<le>) (<)"
begin

interpretation order: total_ordering using totalorder_axioms unfolding class.totalorder_def.

subclass porder ..

sublocale order: total_ordering ..

end

text \<open>Isabelle/HOL's @{class preorder} belongs to @{class qorder}, but not vice versa.\<close>

subclass (in preorder) qorder
  apply unfold_locales
  apply (fact order_refl)
  apply simp
  apply (fact le_less_trans)
  apply (fact less_le_trans)
  apply (fact less_imp_le)
  apply (fact order_trans)
  done

subclass (in order) porder by (unfold_locales, auto)

subclass (in wellorder) wf_qorder by (unfold_locales, fact less_induct)

text \<open>Isabelle/HOL's @{class linorder} is equivalent to our locale @{locale strict_total_ordering}.\<close>

context linorder begin

interpretation order: strict_total_ordering by (unfold_locales, auto)

subclass totalorder ..

sublocale order: strict_total_ordering ..

end

text \<open>Tests: facts should be available in the most general classes.\<close>

thm order.strict.trans[where 'a="'a::compat"]
thm order.extreme_bound_quasi_const[where 'a="'a::attractive_order"]
thm order.extreme_bound_singleton_eq[where 'a="'a::psorder"]
thm order.trans[where 'a="'a::qorder"]
thm order.comparable_cases[where 'a="'a::totalorder"]
thm order.cases[where 'a="'a::linorder"]

subsection \<open>Declaring Duals\<close>

text \<open>At this point, we declare dual as sublocales.\<close>

sublocale less_eq_syntax \<subseteq> dual: less_eq_syntax "(\<sqsubseteq>)\<^sup>-".

sublocale reflexive \<subseteq> dual: reflexive "(\<sqsubseteq>)\<^sup>-" by auto

sublocale attractive \<subseteq> dual: attractive "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale irreflexive \<subseteq> dual: irreflexive "(\<sqsubset>)\<^sup>-" by (unfold_locales, auto)

sublocale transitive \<subseteq> dual: transitive "(\<sqsubseteq>)\<^sup>-" by (unfold_locales, erule trans)

sublocale antisymmetric \<subseteq> dual: antisymmetric "(\<sqsubseteq>)\<^sup>-" by auto

sublocale asymmetric \<subseteq> dual: asymmetric "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale total \<subseteq> dual: total "(\<sqsubset>)\<^sup>-" using total by auto

sublocale total_reflexive \<subseteq> dual: total_reflexive "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale total_irreflexive \<subseteq> dual: total_irreflexive "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale pseudo_order \<subseteq> dual: pseudo_order "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale quasi_order \<subseteq> dual: quasi_order "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale partial_order \<subseteq> dual: partial_order "(\<sqsubseteq>)\<^sup>-" by unfold_locales

text \<open>In the following dual sublocale declaration, ``rewrites'' eventually cleans up redundant
facts.\<close>

sublocale symmetric \<subseteq> dual: symmetric "(\<sim>)\<^sup>-" rewrites "(\<sim>)\<^sup>- = (\<sim>)"
  using symmetric_axioms by (auto simp: dual_sym)

sublocale equivalence \<subseteq> dual: equivalence "(\<sim>)\<^sup>-" rewrites "(\<sim>)\<^sup>- = (\<sim>)"
  by (unfold_locales, auto simp: dual_sym sym)

sublocale total_pseudo_order \<subseteq> dual: total_pseudo_order "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale total_quasi_order \<subseteq> dual: total_quasi_order "(\<sqsubseteq>)\<^sup>-" by unfold_locales

sublocale compatible_ordering \<subseteq> dual: compatible_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-"
  using weak_strict_trans strict_weak_trans strict_implies_weak by unfold_locales

sublocale attractive_ordering \<subseteq> dual: attractive_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale pseudo_ordering \<subseteq> dual: pseudo_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale quasi_ordering \<subseteq> dual: quasi_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale partial_ordering \<subseteq> dual: partial_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-" by unfold_locales

sublocale total_ordering \<subseteq> dual: total_ordering "(\<sqsubseteq>)\<^sup>-" "(\<sqsubset>)\<^sup>-" by unfold_locales


lemma(in antisymmetric) monotone_extreme_imp_extreme_bound_iff:
  fixes ir (infix "\<preceq>" 50)
  assumes "monotone (\<preceq>) (\<sqsubseteq>) f" and i: "extreme (\<preceq>) C i"
  shows "extreme_bound (\<sqsubseteq>) (f ` C) x \<longleftrightarrow> f i = x"
  using dual.extreme_unique monotone_extreme_extreme_boundI[OF assms] by auto


subsection \<open>Instantiations\<close>

text \<open>Finally, we instantiate our classes for sanity check.\<close>

instance nat :: linorder ..

text \<open>Pointwise ordering of functions are compatible only if the weak part is transitive.\<close>

instance "fun" :: (type,qorder) compat
proof (intro_classes, unfold_locales)
  note [simp] = le_fun_def less_fun_def
  fix f g h :: "'a \<Rightarrow> 'b"
  { assume fg: "f \<le> g" and gh: "g < h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally show "f x \<le> h x" for x.
      assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      also from fg have "f x \<le> g x" for x by auto
      finally have "h \<le> g" by auto
      with gh show False by auto
    qed
  }
  { assume fg: "f < g" and gh: "g \<le> h"
    show "f < h"
    proof (unfold less_fun_def, intro conjI le_funI notI)
      from fg have "f x \<le> g x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally show "f x \<le> h x" for x.
      assume hf: "h \<le> f"
      then have "h x \<le> f x" for x by auto
      also from gh have "g x \<le> h x" for x by auto
      finally have "g \<le> f" by auto
      with fg show False by auto
    qed
  }
  show "f < g \<Longrightarrow> f \<le> g" by auto
  show "\<not>f < f" by auto
  show "f \<le> f" by auto
qed

instance "fun" :: (type,qorder) qorder
  by (intro_classes, unfold_locales, auto simp: le_fun_def dest: order.trans)

instance "fun" :: (type,porder) porder
  by (intro_classes, unfold_locales, auto simp: less_fun_def le_fun_def)

end
