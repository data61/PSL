(*
  Copyright (c) 2014-2019 by Clemens Ballarin
  This file is licensed under the 3-clause BSD license.
*)

theory Group_Theory imports Set_Theory begin

hide_const monoid
hide_const group
hide_const inverse

no_notation quotient (infixl "'/'/" 90)


section \<open>Monoids and Groups\<close>

subsection \<open>Monoids of Transformations and Abstract Monoids\<close>

text \<open>Def 1.1\<close>
text \<open>p 28, ll 28--30\<close>
locale monoid =
  fixes M and composition (infixl "\<cdot>" 70) and unit ("\<one>")
  assumes composition_closed [intro, simp]: "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> M"
    and unit_closed [intro, simp]: "\<one> \<in> M"
    and associative [intro]: "\<lbrakk> a \<in> M; b \<in> M; c \<in> M \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
    and left_unit [intro, simp]: "a \<in> M \<Longrightarrow> \<one> \<cdot> a = a"
    and right_unit [intro, simp]: "a \<in> M \<Longrightarrow> a \<cdot> \<one> = a"

text \<open>p 29, ll 27--28\<close>
locale submonoid = monoid M "(\<cdot>)" \<one>
  for N and M and composition (infixl "\<cdot>" 70) and unit ("\<one>") +
  assumes subset [intro, simp]: "N \<subseteq> M"
    and sub_composition_closed: "\<lbrakk> a \<in> N; b \<in> N \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> N"
    and sub_unit_closed: "\<one> \<in> N"
begin

text \<open>p 29, ll 27--28\<close>
lemma sub [intro, simp]:
  "a \<in> N \<Longrightarrow> a \<in> M"
  using subset by blast

text \<open>p 29, ll 32--33\<close>
sublocale sub: monoid N "(\<cdot>)" \<one>
  by unfold_locales (auto simp: sub_composition_closed sub_unit_closed)

end (* submonoid *)

text \<open>p 29, ll 33--34\<close>
theorem submonoid_transitive:
  assumes "submonoid K N composition unit"
    and "submonoid N M composition unit"
  shows "submonoid K M composition unit"
proof -
  interpret K: submonoid K N composition unit by fact
  interpret M: submonoid N M composition unit by fact
  show ?thesis by unfold_locales auto
qed

text \<open>p 28, l 23\<close>
locale transformations =
  fixes S :: "'a set"

(*  assumes non_vacuous: "S \<noteq> {}" *) (* Jacobson requires this but we don't need it, strange. *)

text \<open>Monoid of all transformations\<close>
text \<open>p 28, ll 23--24\<close>
sublocale transformations \<subseteq> monoid "S \<rightarrow>\<^sub>E S" "compose S" "identity S"
  by unfold_locales (auto simp: PiE_def compose_eq compose_assoc Id_compose compose_Id)

text \<open>@{term N} is a monoid of transformations of the set @{term S}.\<close>
text \<open>p 29, ll 34--36\<close>
locale transformation_monoid =
  transformations S + submonoid M "S \<rightarrow>\<^sub>E S" "compose S" "identity S" for M and S
begin

text \<open>p 29, ll 34--36\<close>
lemma transformation_closed [intro, simp]:
  "\<lbrakk> \<alpha> \<in> M; x \<in> S \<rbrakk> \<Longrightarrow> \<alpha> x \<in> S"
  by (metis PiE_iff sub)

text \<open>p 29, ll 34--36\<close>
lemma transformation_undefined [intro, simp]:
  "\<lbrakk> \<alpha> \<in> M; x \<notin> S \<rbrakk> \<Longrightarrow> \<alpha> x = undefined"
  by (metis PiE_arb sub)

end (* transformation_monoid *)


subsection \<open>Groups of Transformations and Abstract Groups\<close>

context monoid begin

text \<open>Invertible elements\<close>

text \<open>p 31, ll 3--5\<close>
definition invertible where "u \<in> M \<Longrightarrow> invertible u \<longleftrightarrow> (\<exists>v \<in> M. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>)"

text \<open>p 31, ll 3--5\<close>
lemma invertibleI [intro]:
  "\<lbrakk> u \<cdot> v = \<one>; v \<cdot> u = \<one>; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> invertible u"
  unfolding invertible_def by fast

text \<open>p 31, ll 3--5\<close>
lemma invertibleE [elim]:
  "\<lbrakk> invertible u; \<And>v. \<lbrakk> u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>; v \<in> M \<rbrakk> \<Longrightarrow> P; u \<in> M \<rbrakk> \<Longrightarrow> P"
  unfolding invertible_def by fast

text \<open>p 31, ll 6--7\<close>
theorem inverse_unique:
  "\<lbrakk> u \<cdot> v' = \<one>; v \<cdot> u = \<one>; u \<in> M;  v \<in> M; v' \<in> M \<rbrakk> \<Longrightarrow> v = v'"
  by (metis associative left_unit right_unit)

text \<open>p 31, l 7\<close>
definition inverse where "inverse = (\<lambda>u \<in> M. THE v. v \<in> M \<and> u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>)"

text \<open>p 31, l 7\<close>
theorem inverse_equality:
  "\<lbrakk> u \<cdot> v = \<one>; v \<cdot> u = \<one>; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> inverse u = v"
  unfolding inverse_def using inverse_unique by simp blast

text \<open>p 31, l 7\<close>
lemma invertible_inverse_closed [intro, simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse u \<in> M"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma inverse_undefined [intro, simp]:
  "u \<notin> M \<Longrightarrow> inverse u = undefined"
  by (simp add: inverse_def)

text \<open>p 31, l 7\<close>
lemma invertible_left_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse u \<cdot> u = \<one>"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma invertible_right_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> u \<cdot> inverse u = \<one>"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma invertible_left_cancel [simp]:
  "\<lbrakk> invertible x; x \<in> M; y \<in> M; z \<in> M \<rbrakk> \<Longrightarrow> x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z"
  by (metis associative invertible_def left_unit)

text \<open>p 31, l 7\<close>
lemma invertible_right_cancel [simp]:
  "\<lbrakk> invertible x; x \<in> M; y \<in> M; z \<in> M \<rbrakk> \<Longrightarrow> y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z"
  by (metis associative invertible_def right_unit)

text \<open>p 31, l 7\<close>
lemma inverse_unit [simp]: "inverse \<one> = \<one>"
  using inverse_equality by blast

text \<open>p 31, ll 7--8\<close>
theorem invertible_inverse_invertible [intro, simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> invertible (inverse u)"
  using invertible_left_inverse invertible_right_inverse by blast

text \<open>p 31, l 8\<close>
theorem invertible_inverse_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse (inverse u) = u"
  by (simp add: inverse_equality)

end (* monoid *)

context submonoid begin

text \<open>Reasoning about @{term invertible} and @{term inverse} in submonoids.\<close>

text \<open>p 31, l 7\<close>
lemma submonoid_invertible [intro, simp]:
  "\<lbrakk> sub.invertible u; u \<in> N \<rbrakk> \<Longrightarrow> invertible u"
  using invertibleI by blast

text \<open>p 31, l 7\<close>
lemma submonoid_inverse_closed [intro, simp]:
  "\<lbrakk> sub.invertible u; u \<in> N \<rbrakk> \<Longrightarrow> inverse u \<in> N"
  using inverse_equality by auto

end (* submonoid *)

text \<open>Def 1.2\<close>
text \<open>p 31, ll 9--10\<close>
locale group =
  monoid G "(\<cdot>)" \<one> for G and composition (infixl "\<cdot>" 70) and unit ("\<one>") +
  assumes invertible [simp, intro]: "u \<in> G \<Longrightarrow> invertible u"

text \<open>p 31, ll 11--12\<close>
locale subgroup = submonoid G M "(\<cdot>)" \<one> + sub: group G "(\<cdot>)" \<one>
  for G and M and composition (infixl "\<cdot>" 70) and unit ("\<one>")
begin

text \<open>Reasoning about @{term invertible} and @{term inverse} in subgroups.\<close>

text \<open>p 31, ll 11--12\<close>
lemma subgroup_inverse_equality [simp]:
  "u \<in> G \<Longrightarrow> inverse u = sub.inverse u"
  by (simp add: inverse_equality)

text \<open>p 31, ll 11--12\<close>
lemma subgroup_inverse_iff [simp]:
  "\<lbrakk> invertible x; x \<in> M \<rbrakk> \<Longrightarrow> inverse x \<in> G \<longleftrightarrow> x \<in> G"
  using invertible_inverse_inverse sub.invertible_inverse_closed by fastforce

end (* subgroup *)


text \<open>p 31, ll 11--12\<close>
lemma subgroup_transitive [trans]:
  assumes "subgroup K H composition unit"
    and "subgroup H G composition unit"
  shows "subgroup K G composition unit"
proof -
  interpret K: subgroup K H composition unit by fact
  interpret H: subgroup H G composition unit by fact
  show ?thesis by unfold_locales auto
qed

context monoid begin

text \<open>Jacobson states both directions, but the other one is trivial.\<close>
text \<open>p 31, ll 12--15\<close>
theorem subgroupI:
  fixes G
  assumes subset [THEN subsetD, intro]: "G \<subseteq> M"
    and [intro]: "\<one> \<in> G"
    and [intro]: "\<And>g h. \<lbrakk> g \<in> G; h \<in> G \<rbrakk> \<Longrightarrow> g \<cdot> h \<in> G"
    and [intro]: "\<And>g. g \<in> G \<Longrightarrow> invertible g"
    and [intro]: "\<And>g. g \<in> G \<Longrightarrow> inverse g \<in> G"
  shows "subgroup G M (\<cdot>) \<one>"
proof -
  interpret sub: monoid G "(\<cdot>)" \<one> by unfold_locales auto
  show ?thesis
  proof unfold_locales
    fix u assume [intro]: "u \<in> G" show "sub.invertible u"
    using invertible_left_inverse invertible_right_inverse by blast
  qed auto
qed

text \<open>p 31, l 16\<close>
definition "Units = {u \<in> M. invertible u}"

text \<open>p 31, l 16\<close>
lemma mem_UnitsI:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> u \<in> Units"
  unfolding Units_def by clarify

text \<open>p 31, l 16\<close>
lemma mem_UnitsD:
  "\<lbrakk> u \<in> Units \<rbrakk> \<Longrightarrow> invertible u \<and> u \<in> M"
  unfolding Units_def by clarify

text \<open>p 31, ll 16--21\<close>
interpretation units: subgroup Units M
proof (rule subgroupI)
  fix u1 u2
  assume Units [THEN mem_UnitsD, simp]: "u1 \<in> Units" "u2 \<in> Units"
  have "(u1 \<cdot> u2) \<cdot> (inverse u2 \<cdot> inverse u1) = (u1 \<cdot> (u2 \<cdot> inverse u2)) \<cdot> inverse u1"
    by (simp add: associative del: invertible_left_inverse invertible_right_inverse)
  also have "\<dots> = \<one>" by simp
  finally have inv1: "(u1 \<cdot> u2) \<cdot> (inverse u2 \<cdot> inverse u1) = \<one>" by simp  \<comment> \<open>ll 16--18\<close>
  have "(inverse u2 \<cdot> inverse u1) \<cdot> (u1 \<cdot> u2) = (inverse u2 \<cdot> (inverse u1 \<cdot> u1)) \<cdot> u2"
    by (simp add: associative del: invertible_left_inverse invertible_right_inverse)
  also have "\<dots> = \<one>" by simp
  finally have inv2: "(inverse u2 \<cdot> inverse u1) \<cdot> (u1 \<cdot> u2) = \<one>" by simp  \<comment> \<open>l 9, “and similarly”\<close>
  show "u1 \<cdot> u2 \<in> Units" using inv1 inv2 invertibleI mem_UnitsI by auto
qed (auto simp: Units_def)

text \<open>p 31, ll 21--22\<close>
theorem group_of_Units [intro, simp]:
  "group Units (\<cdot>) \<one>"
  ..

text \<open>p 31, l 19\<close>
lemma composition_invertible [simp, intro]:
  "\<lbrakk> invertible x; invertible y; x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)"
  using mem_UnitsD mem_UnitsI by blast

text \<open>p 31, l 20\<close>
lemma unit_invertible:
  "invertible \<one>"
  by fast

text \<open>Useful simplification rules\<close>
text \<open>p 31, l 22\<close>
lemma invertible_right_inverse2:
  "\<lbrakk> invertible u; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> u \<cdot> (inverse u \<cdot> v) = v"
  by (simp add: associative [THEN sym])

text \<open>p 31, l 22\<close>
lemma invertible_left_inverse2:
  "\<lbrakk> invertible u; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> inverse u \<cdot> (u \<cdot> v) = v"
  by (simp add: associative [THEN sym])

text \<open>p 31, l 22\<close>
lemma inverse_composition_commute:
  assumes [simp]: "invertible x" "invertible y" "x \<in> M" "y \<in> M"
  shows "inverse (x \<cdot> y) = inverse y \<cdot> inverse x"
proof -
  have "inverse (x \<cdot> y) \<cdot> (x \<cdot> y) = (inverse y \<cdot> inverse x) \<cdot> (x \<cdot> y)"
  by (simp add: invertible_left_inverse2 associative)
  then show ?thesis by (simp del: invertible_left_inverse)
qed

end (* monoid *)

text \<open>p 31, l 24\<close>
context transformations begin

text \<open>p 31, ll 25--26\<close>
theorem invertible_is_bijective:
  assumes dom: "\<alpha> \<in> S \<rightarrow>\<^sub>E S"
  shows "invertible \<alpha> \<longleftrightarrow> bij_betw \<alpha> S S"
proof -
  from dom interpret map \<alpha> S S by unfold_locales
  show ?thesis by (auto simp add: bij_betw_iff_has_inverse invertible_def)
qed

text \<open>p 31, ll 26--27\<close>
theorem Units_bijective:
  "Units = {\<alpha> \<in> S \<rightarrow>\<^sub>E S. bij_betw \<alpha> S S}"
  unfolding Units_def by (auto simp add: invertible_is_bijective)

text \<open>p 31, ll 26--27\<close>
lemma Units_bij_betwI [intro, simp]:
  "\<alpha> \<in> Units \<Longrightarrow> bij_betw \<alpha> S S"
  by (simp add: Units_bijective)

text \<open>p 31, ll 26--27\<close>
lemma Units_bij_betwD [dest, simp]:
  "\<lbrakk> \<alpha> \<in> S \<rightarrow>\<^sub>E S; bij_betw \<alpha> S S \<rbrakk> \<Longrightarrow> \<alpha> \<in> Units"
  unfolding Units_bijective by simp

text \<open>p 31, ll 28--29\<close>
abbreviation "Sym \<equiv> Units"

text \<open>p 31, ll 26--28\<close>
sublocale symmetric: group "Sym" "compose S" "identity S"
  by (fact group_of_Units)

end (* transformations *)

text \<open>p 32, ll 18--19\<close>
locale transformation_group =
  transformations S + symmetric: subgroup G Sym "compose S" "identity S" for G and S
begin

text \<open>p 32, ll 18--19\<close>
lemma transformation_group_closed [intro, simp]:
  "\<lbrakk> \<alpha> \<in> G; x \<in> S \<rbrakk> \<Longrightarrow> \<alpha> x \<in> S"
  using bij_betwE by blast

text \<open>p 32, ll 18--19\<close>
lemma transformation_group_undefined [intro, simp]:
  "\<lbrakk> \<alpha> \<in> G; x \<notin> S \<rbrakk> \<Longrightarrow> \<alpha> x = undefined"
  by (metis compose_def symmetric.sub.right_unit restrict_apply)

end (* transformation_group *)


subsection \<open>Isomorphisms.  Cayley's Theorem\<close>

text \<open>Def 1.3\<close>
text \<open>p 37, ll 7--11\<close>
locale monoid_isomorphism =
  bijective_map \<eta> M M' +  source: monoid M "(\<cdot>)" \<one> + target: monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl "\<cdot>" 70) and unit ("\<one>")
    and M' and composition' (infixl "\<cdot>''" 70) and unit' ("\<one>''") +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> x \<cdot>' \<eta> y = \<eta> (x \<cdot> y)"
    and commutes_with_unit: "\<eta> \<one> = \<one>'"

text \<open>p 37, l 10\<close>
definition isomorphic_as_monoids (infixl "\<cong>\<^sub>M" 50)
  where "\<M> \<cong>\<^sub>M \<M>' \<longleftrightarrow> (let (M, composition, unit) = \<M>; (M', composition', unit') = \<M>' in
  (\<exists>\<eta>. monoid_isomorphism \<eta> M composition unit M' composition' unit'))"

text \<open>p 37, ll 11--12\<close>
locale monoid_isomorphism' =
  bijective_map \<eta> M M' +  source: monoid M "(\<cdot>)" \<one> + target: monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl "\<cdot>" 70) and unit ("\<one>")
    and M' and composition' (infixl "\<cdot>''" 70) and unit' ("\<one>''") +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> x \<cdot>' \<eta> y = \<eta> (x \<cdot> y)"

text \<open>p 37, ll 11--12\<close>
sublocale monoid_isomorphism \<subseteq> monoid_isomorphism'
  by unfold_locales (simp add: commutes_with_composition)

text \<open>Both definitions are equivalent.\<close>
text \<open>p 37, ll 12--15\<close>
sublocale monoid_isomorphism' \<subseteq> monoid_isomorphism
proof unfold_locales
  {
    fix y assume "y \<in> M'"
    then obtain x where "\<eta> x = y" "x \<in> M" by (metis image_iff surjective)
    then have "y \<cdot>' \<eta> \<one> = y" using commutes_with_composition by auto
  }
  then show "\<eta> \<one> = \<one>'" by fastforce
qed (simp add: commutes_with_composition)

context monoid_isomorphism begin

text \<open>p 37, ll 30--33\<close>
theorem inverse_monoid_isomorphism:
  "monoid_isomorphism (restrict (inv_into M \<eta>) M') M' (\<cdot>') \<one>' M (\<cdot>) \<one>"
  using commutes_with_composition commutes_with_unit surjective by unfold_locales auto

end (* monoid_isomorphism *)

text \<open>We only need that @{term \<eta>} is symmetric.\<close>
text \<open>p 37, ll 28--29\<close>
theorem isomorphic_as_monoids_symmetric:
  "(M, composition, unit) \<cong>\<^sub>M (M', composition', unit') \<Longrightarrow> (M', composition', unit') \<cong>\<^sub>M (M, composition, unit)"
  by (simp add: isomorphic_as_monoids_def) (meson monoid_isomorphism.inverse_monoid_isomorphism)

text \<open>p 38, l 4\<close>
locale left_translations_of_monoid = monoid begin

(*
  We take the liberty of omitting "left_" from the name of the translation operation.  The derived
  transformation monoid and group won't be qualified with "left" either.  This avoids qualifications
  such as "left.left_...".  In contexts where left and right translations are used simultaneously,
  notably subgroup_of_group, qualifiers are needed.
*)

text \<open>p 38, ll 5--7\<close>
definition translation ("'(_')\<^sub>L") where "translation = (\<lambda>a \<in> M. \<lambda>x \<in> M. a \<cdot> x)"

text \<open>p 38, ll 5--7\<close>
lemma translation_map [intro, simp]:
  "a \<in> M \<Longrightarrow> (a)\<^sub>L \<in> M \<rightarrow>\<^sub>E M"
  unfolding translation_def by simp

text \<open>p 38, ll 5--7\<close>
lemma Translations_maps [intro, simp]:
  "translation ` M \<subseteq> M \<rightarrow>\<^sub>E M"
  by (simp add: image_subsetI)

text \<open>p 38, ll 5--7\<close>
lemma translation_apply:
  "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> (a)\<^sub>L b = a \<cdot> b"
  unfolding translation_def by auto

text \<open>p 38, ll 5--7\<close>
lemma translation_exist:
  "f \<in> translation ` M \<Longrightarrow> \<exists>a \<in> M. f = (a)\<^sub>L"
  by auto

text \<open>p 38, ll 5--7\<close>
lemmas Translations_E [elim] = translation_exist [THEN bexE]

text \<open>p 38, l 10\<close>
theorem translation_unit_eq [simp]:
  "identity M = (\<one>)\<^sub>L"
  unfolding translation_def by auto

text \<open>p 38, ll 10--11\<close>
theorem translation_composition_eq [simp]:
  assumes [simp]: "a \<in> M" "b \<in> M"
  shows "compose M (a)\<^sub>L (b)\<^sub>L = (a \<cdot> b)\<^sub>L"
  unfolding translation_def by rule (simp add: associative compose_def)

(* Activate @{locale monoid} to simplify subsequent proof. *)
text \<open>p 38, ll 7--9\<close>
sublocale transformation: transformations M .

text \<open>p 38, ll 7--9\<close>
theorem Translations_transformation_monoid:
  "transformation_monoid (translation ` M) M"
  by unfold_locales auto

text \<open>p 38, ll 7--9\<close>
sublocale transformation: transformation_monoid "translation ` M" M
  by (fact Translations_transformation_monoid)

text \<open>p 38, l 12\<close>
sublocale map translation M "translation ` M"
  by unfold_locales (simp add: translation_def)

text \<open>p 38, ll 12--16\<close>
theorem translation_isomorphism [intro]:
  "monoid_isomorphism translation M (\<cdot>) \<one> (translation ` M) (compose M) (identity M)"
proof unfold_locales
  have "inj_on translation M"
  proof (rule inj_onI)
    fix a b
    assume [simp]: "a \<in> M" "b \<in> M" "(a)\<^sub>L = (b)\<^sub>L"
    have "(a)\<^sub>L \<one> = (b)\<^sub>L \<one>" by simp
    then show "a = b" by (simp add: translation_def)
  qed
  then show "bij_betw translation M (translation ` M)"
    by (simp add: inj_on_imp_bij_betw)
qed simp_all

text \<open>p 38, ll 12--16\<close>
sublocale monoid_isomorphism translation M "(\<cdot>)" \<one> "translation ` M" "compose M" "identity M" ..

end (* left_translations_of_monoid *)

context monoid begin

text \<open>p 38, ll 1--2\<close>
interpretation left_translations_of_monoid ..

text \<open>p 38, ll 1--2\<close>
theorem cayley_monoid:
  "\<exists>M' composition' unit'. transformation_monoid M' M \<and> (M, (\<cdot>), \<one>) \<cong>\<^sub>M (M', composition', unit')"
  by (simp add: isomorphic_as_monoids_def) (fast intro: Translations_transformation_monoid)

end (* monoid *)

text \<open>p 38, l 17\<close>
locale left_translations_of_group = group begin

text \<open>p 38, ll 17--18\<close>
sublocale left_translations_of_monoid where M = G ..

text \<open>p 38, ll 17--18\<close>
notation translation ("'(_')\<^sub>L")

text \<open>
  The group of left translations is a subgroup of the symmetric group,
  hence @{term transformation.sub.invertible}.
\<close>
text \<open>p 38, ll 20--22\<close>
theorem translation_invertible [intro, simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.invertible (a)\<^sub>L"
proof
  show "compose G (a)\<^sub>L (inverse a)\<^sub>L = identity G" by simp
next
  show "compose G (inverse a)\<^sub>L (a)\<^sub>L = identity G" by simp
qed auto

text \<open>p 38, ll 19--20\<close>
theorem translation_bijective [intro, simp]:
  "a \<in> G \<Longrightarrow> bij_betw (a)\<^sub>L G G"
  by (blast intro: transformation.invertible_is_bijective [THEN iffD1])

text \<open>p 38, ll 18--20\<close>
theorem Translations_transformation_group:
  "transformation_group (translation ` G) G"
proof unfold_locales
  show "(translation ` G) \<subseteq> transformation.Sym"
    unfolding transformation.Units_bijective by auto
next
  fix \<alpha>
  assume \<alpha>: "\<alpha> \<in> translation ` G"
  then obtain a where a: "a \<in> G" and eq: "\<alpha> = (a)\<^sub>L" ..
  with translation_invertible show "transformation.sub.invertible \<alpha>" by simp
qed auto

text \<open>p 38, ll 18--20\<close>
sublocale transformation: transformation_group "translation ` G" G
  by (fact Translations_transformation_group)

end (* left_translations_of_group *)

context group begin

text \<open>p 38, ll 2--3\<close>
interpretation left_translations_of_group ..

text \<open>p 38, ll 2--3\<close>
theorem cayley_group:
  "\<exists>G' composition' unit'. transformation_group G' G \<and> (G, (\<cdot>), \<one>) \<cong>\<^sub>M (G', composition', unit')"
  by (simp add: isomorphic_as_monoids_def) (fast intro: Translations_transformation_group)

end (* group *)

text \<open>Exercise 3\<close>

text \<open>p 39, ll 9--10\<close>
locale right_translations_of_group = group begin

text \<open>p 39, ll 9--10\<close>
definition translation ("'(_')\<^sub>R") where "translation = (\<lambda>a \<in> G. \<lambda>x \<in> G. x \<cdot> a)"

text \<open>p 39, ll 9--10\<close>
abbreviation "Translations \<equiv> translation ` G"

text \<open>The isomorphism that will be established is a map different from @{term translation}.\<close>
text \<open>p 39, ll 9--10\<close>
interpretation aux: map translation G Translations
  by unfold_locales (simp add: translation_def)

text \<open>p 39, ll 9--10\<close>
lemma translation_map [intro, simp]:
  "a \<in> G \<Longrightarrow> (a)\<^sub>R \<in> G \<rightarrow>\<^sub>E G"
  unfolding translation_def by simp

text \<open>p 39, ll 9--10\<close>
lemma Translation_maps [intro, simp]:
  "Translations \<subseteq> G \<rightarrow>\<^sub>E G"
  by (simp add: image_subsetI)

text \<open>p 39, ll 9--10\<close>
lemma translation_apply:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> (a)\<^sub>R b = b \<cdot> a"
  unfolding translation_def by auto

text \<open>p 39, ll 9--10\<close>
lemma translation_exist:
  "f \<in> Translations \<Longrightarrow> \<exists>a \<in> G. f = (a)\<^sub>R"
  by auto

text \<open>p 39, ll 9--10\<close>
lemmas Translations_E [elim] = translation_exist [THEN bexE]

text \<open>p 39, ll 9--10\<close>
lemma translation_unit_eq [simp]:
  "identity G = (\<one>)\<^sub>R"
  unfolding translation_def by auto

text \<open>p 39, ll 10--11\<close>
lemma translation_composition_eq [simp]:
  assumes [simp]: "a \<in> G" "b \<in> G"
  shows "compose G (a)\<^sub>R (b)\<^sub>R = (b \<cdot> a)\<^sub>R"
  unfolding translation_def by rule (simp add: associative compose_def)

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformations G .

text \<open>p 39, ll 10--11\<close>
lemma Translations_transformation_monoid:
  "transformation_monoid Translations G"
  by unfold_locales auto

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformation_monoid Translations G
  by (fact Translations_transformation_monoid)

text \<open>p 39, ll 10--11\<close>
lemma translation_invertible [intro, simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.invertible (a)\<^sub>R"
proof
  show "compose G (a)\<^sub>R (inverse a)\<^sub>R = identity G" by simp
next
  show "compose G (inverse a)\<^sub>R (a)\<^sub>R = identity G" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
lemma translation_bijective [intro, simp]:
  "a \<in> G \<Longrightarrow> bij_betw (a)\<^sub>R G G"
  by (blast intro: transformation.invertible_is_bijective [THEN iffD1])

text \<open>p 39, ll 10--11\<close>
theorem Translations_transformation_group:
  "transformation_group Translations G"
proof unfold_locales
  show "Translations \<subseteq> transformation.Sym"
  unfolding transformation.Units_bijective by auto
next
  fix \<alpha>
  assume \<alpha>: "\<alpha> \<in> Translations"
  then obtain a where a: "a \<in> G" and eq: "\<alpha> = (a)\<^sub>R" ..
  with translation_invertible show "transformation.sub.invertible \<alpha>" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformation_group Translations G
  by (rule Translations_transformation_group)

text \<open>p 39, ll 10--11\<close>
lemma translation_inverse_eq [simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.inverse (a)\<^sub>R = (inverse a)\<^sub>R"
proof (rule transformation.sub.inverse_equality)
  show "compose G (a)\<^sub>R (inverse a)\<^sub>R = identity G" by simp
next
  show "compose G (inverse a)\<^sub>R (a)\<^sub>R = identity G" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
theorem translation_inverse_monoid_isomorphism [intro]:
  "monoid_isomorphism (\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R) G (\<cdot>) \<one> Translations (compose G) (identity G)"
  (is "monoid_isomorphism ?inv _ _ _ _ _ _")
proof unfold_locales
  show "?inv \<in> G \<rightarrow>\<^sub>E Translations" by (simp del: translation_unit_eq)
next
  note bij_betw_compose [trans]
  have "bij_betw inverse G G"
    by (rule bij_betwI [where g = inverse]) auto
  also have "bij_betw translation G Translations"
    by (rule bij_betwI [where g = "\<lambda>\<alpha>\<in>Translations. \<alpha> \<one>"]) (auto simp: translation_apply)
  finally show "bij_betw ?inv G Translations"
    by (simp cong: bij_betw_cong add: compose_eq del: translation_unit_eq)
next
  fix x and y
  assume [simp]: "x \<in> G" "y \<in> G"
  show "compose G (?inv x) (?inv y) = (?inv (x \<cdot> y))" by (simp add: inverse_composition_commute del: translation_unit_eq)
next
  show "?inv \<one> = identity G" by (simp del: translation_unit_eq) simp
qed

text \<open>p 39, ll 10--11\<close>
sublocale monoid_isomorphism
  "\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R" G "(\<cdot>)" \<one> Translations "compose G" "identity G" ..

end (* right_translations_of_group *)


subsection \<open>Generalized Associativity.  Commutativity\<close>

text \<open>p 40, l 27; p 41, ll 1--2\<close>
locale commutative_monoid = monoid +
  assumes commutative: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
  
text \<open>p 41, l 2\<close>
locale abelian_group = group + commutative_monoid G "(\<cdot>)" \<one>


subsection \<open>Orbits.  Cosets of a Subgroup\<close>

context transformation_group begin

text \<open>p 51, ll 18--20\<close>
definition Orbit_Relation
  where "Orbit_Relation = {(x, y). x \<in> S \<and> y \<in> S \<and> (\<exists>\<alpha> \<in> G. y = \<alpha> x)}"

text \<open>p 51, ll 18--20\<close>
lemma Orbit_Relation_memI [intro]:
  "\<lbrakk> \<exists>\<alpha> \<in> G. y = \<alpha> x; x \<in> S \<rbrakk> \<Longrightarrow> (x, y) \<in> Orbit_Relation"
  unfolding Orbit_Relation_def by auto

text \<open>p 51, ll 18--20\<close>
lemma Orbit_Relation_memE [elim]:
  "\<lbrakk> (x, y) \<in> Orbit_Relation; \<And>\<alpha>. \<lbrakk> \<alpha> \<in> G; x \<in> S; y = \<alpha> x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding Orbit_Relation_def by auto

text \<open>p 51, ll 20--23, 26--27\<close>
sublocale orbit: equivalence S Orbit_Relation
proof (unfold_locales, auto simp: Orbit_Relation_def)
  fix x
  assume x: "x \<in> S"
  then have id: "x = identity S x" by simp
  with x show "\<exists>\<alpha> \<in> G. x = \<alpha> x" by fast
  fix \<alpha>
  assume \<alpha>: "\<alpha> \<in> G"
  with x id have y: "x = compose S (symmetric.inverse \<alpha>) \<alpha> x" by auto
  with x \<alpha> show "\<exists>\<alpha>' \<in> G. x = \<alpha>' (\<alpha> x)"
    by (metis compose_eq symmetric.sub.invertible symmetric.submonoid_inverse_closed)
  fix \<beta>
  assume \<beta>: "\<beta> \<in> G"
  with x have "\<beta> (\<alpha> x) = compose S \<beta> \<alpha> x" by (simp add: compose_eq)
  with \<alpha> \<beta> show "\<exists>\<gamma> \<in> G. \<beta> (\<alpha> x) = \<gamma> x" by fast
qed

text \<open>p 51, ll 23--24\<close>
theorem orbit_equality:
  "x \<in> S \<Longrightarrow> orbit.Class x = {\<alpha> x | \<alpha>. \<alpha> \<in> G}"
by (simp add: orbit.Class_def) (blast intro: orbit.symmetric dest: orbit.symmetric)

end (* transformation_group *)

context monoid_isomorphism begin

text \<open>p 52, ll 16--17\<close>
theorem image_subgroup:
  assumes "subgroup G M (\<cdot>) \<one>"
  shows "subgroup (\<eta> ` G) M' (\<cdot>') \<one>'"
proof -
  interpret subgroup G M "(\<cdot>)" \<one> by fact
  interpret image: monoid "\<eta> ` G" "(\<cdot>')" "\<one>'"
    by unfold_locales (auto simp add: commutes_with_composition commutes_with_unit [symmetric])
  show ?thesis
  proof (unfold_locales, auto)
    fix x
    assume x: "x \<in> G"
    show "image.invertible (\<eta> x)"
    proof
      show "\<eta> (sub.inverse x) \<in> \<eta> ` G" using x by simp
    qed (auto simp: x commutes_with_composition commutes_with_unit)
  qed
qed

end (* monoid_isomorphism *)

text \<open>
  Technical device to achieve Jacobson's notation for @{text Right_Coset} and @{text Left_Coset}.  The
  definitions are pulled out of @{text subgroup_of_group} to a context where @{text H} is not a parameter.
\<close>
text \<open>p 52, l 20\<close>
locale coset_notation = fixes composition (infixl "\<cdot>" 70)  begin

text \<open>Equation 23\<close>
text \<open>p 52, l 20\<close>
definition Right_Coset (infixl "|\<cdot>" 70) where "H |\<cdot> x = {h \<cdot> x | h. h \<in> H}"

text \<open>p 53, ll 8--9\<close>
definition Left_Coset (infixl "\<cdot>|" 70) where "x \<cdot>| H = {x \<cdot> h | h. h \<in> H}"

text \<open>p 52, l 20\<close>
lemma Right_Coset_memI [intro]:
  "h \<in> H \<Longrightarrow> h \<cdot> x \<in> H |\<cdot> x"
  unfolding Right_Coset_def by blast

text \<open>p 52, l 20\<close>
lemma Right_Coset_memE [elim]:
  "\<lbrakk> a \<in> H |\<cdot> x; \<And>h. \<lbrakk> h \<in> H; a = h \<cdot> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding Right_Coset_def by blast

text \<open>p 53, ll 8--9\<close>
lemma Left_Coset_memI [intro]:
  "h \<in> H \<Longrightarrow> x \<cdot> h \<in> x \<cdot>| H"
  unfolding Left_Coset_def by blast

text \<open>p 53, ll 8--9\<close>
lemma Left_Coset_memE [elim]:
  "\<lbrakk> a \<in> x \<cdot>| H; \<And>h. \<lbrakk> h \<in> H; a = x \<cdot> h \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding Left_Coset_def by blast

end (* coset_notation *)

text \<open>p 52, l 12\<close>
locale subgroup_of_group = subgroup H G "(\<cdot>)" \<one> + coset_notation "(\<cdot>)" + group G "(\<cdot>)" \<one>
  for H and G and composition (infixl "\<cdot>" 70) and unit ("\<one>")
begin

text \<open>p 52, ll 12--14\<close>
interpretation left: left_translations_of_group ..
interpretation right: right_translations_of_group ..

text \<open>
  @{term "left.translation ` H"} denotes Jacobson's @{text "H\<^sub>L(G)"} and
  @{term "left.translation ` G"} denotes Jacobson's @{text "G\<^sub>L"}.
\<close>

text \<open>p 52, ll 16--18\<close>
theorem left_translations_of_subgroup_are_transformation_group [intro]:
  "transformation_group (left.translation ` H) G"
proof -
  have "subgroup (left.translation ` H) (left.translation ` G) (compose G) (identity G)"
    by (rule left.image_subgroup) unfold_locales
  also have "subgroup (left.translation ` G) left.transformation.Sym (compose G) (identity G)" ..
  finally interpret right_coset: subgroup "left.translation ` H" left.transformation.Sym "compose G" "identity G" .
  show ?thesis ..
qed

text \<open>p 52, l 18\<close>
interpretation transformation_group "left.translation ` H" G ..

text \<open>p 52, ll 19--20\<close>
theorem Right_Coset_is_orbit:
  "x \<in> G \<Longrightarrow> H |\<cdot> x = orbit.Class x"
  using left.translation_apply by (auto simp: orbit_equality Right_Coset_def) (metis imageI sub)

text \<open>p 52, ll 24--25\<close>
theorem Right_Coset_Union:
  "(\<Union>x\<in>G. H |\<cdot> x) = G"
  by (simp add: Right_Coset_is_orbit)

text \<open>p 52, l 26\<close>
theorem Right_Coset_bij:
  assumes G [simp]: "x \<in> G" "y \<in> G"
  shows "bij_betw (inverse x \<cdot> y)\<^sub>R (H |\<cdot> x) (H |\<cdot> y)"
proof (rule bij_betw_imageI)
  show "inj_on (inverse x \<cdot> y)\<^sub>R (H |\<cdot> x)"
    by (fastforce intro: inj_onI simp add: Right_Coset_is_orbit right.translation_apply orbit.block_closed)
next
  show "(inverse x \<cdot> y)\<^sub>R ` (H |\<cdot> x) = H |\<cdot> y"
    by (force simp add: right.translation_apply associative invertible_right_inverse2)
qed

text \<open>p 52, ll 25--26\<close>
theorem Right_Cosets_cardinality:
  "\<lbrakk> x \<in> G; y \<in> G \<rbrakk> \<Longrightarrow> card (H |\<cdot> x) = card (H |\<cdot> y)"
  by (fast intro: bij_betw_same_card Right_Coset_bij)

text \<open>p 52, l 27\<close>
theorem Right_Coset_unit:
  "H |\<cdot> \<one> = H"
  by (force simp add: Right_Coset_def)

text \<open>p 52, l 27\<close>
theorem Right_Coset_cardinality:
  "x \<in> G \<Longrightarrow> card (H |\<cdot> x) = card H"
  using Right_Coset_unit Right_Cosets_cardinality unit_closed by presburger

text \<open>p 52, ll 31--32\<close>
definition "index = card orbit.Partition"

text \<open>Theorem 1.5\<close>
text \<open>p 52, ll 33--35; p 53, ll 1--2\<close>
theorem lagrange:
  "finite G \<Longrightarrow> card G = card H * index"
  unfolding index_def
  apply (subst card_partition)
      apply (auto simp: finite_UnionD orbit.complete orbit.disjoint)
  apply (metis Right_Coset_cardinality Right_Coset_is_orbit orbit.Block_self orbit.element_exists)
  done

end (* subgroup_of_group *)

text \<open>Left cosets\<close>

context subgroup begin

text \<open>p 31, ll 11--12\<close>
lemma image_of_inverse [intro, simp]:
  "x \<in> G \<Longrightarrow> x \<in> inverse ` G"
  by (metis image_eqI sub.invertible sub.invertible_inverse_closed sub.invertible_inverse_inverse subgroup_inverse_equality)

end (* subgroup *)

context group begin

(* Does Jacobson show this somewhere? *)
text \<open>p 53, ll 6--7\<close>
lemma inverse_subgroupI:
  assumes sub: "subgroup H G (\<cdot>) \<one>"
  shows "subgroup (inverse ` H) G (\<cdot>) \<one>"
proof -
  from sub interpret subgroup H G "(\<cdot>)" \<one> .
  interpret inv: monoid "inverse ` H" "(\<cdot>)" \<one>
    by unfold_locales (auto simp del: subgroup_inverse_equality)
  interpret inv: group "inverse ` H" "(\<cdot>)" \<one>
    by unfold_locales (force simp del: subgroup_inverse_equality)
  show ?thesis
    by unfold_locales (auto simp del: subgroup_inverse_equality)
qed

text \<open>p 53, ll 6--7\<close>
lemma inverse_subgroupD:
  assumes sub: "subgroup (inverse ` H) G (\<cdot>) \<one>"
    and inv: "H \<subseteq> Units"
  shows "subgroup H G (\<cdot>) \<one>"
proof -
  from sub have "subgroup (inverse ` inverse ` H) G (\<cdot>) \<one>" by (rule inverse_subgroupI)
  moreover from inv [THEN subsetD, simplified Units_def] have "inverse ` inverse ` H = H"
    by (simp cong: image_cong add: image_comp)
  ultimately show ?thesis by simp
qed

end (* group *)

context subgroup_of_group begin

text \<open>p 53, l 6\<close>
interpretation right_translations_of_group ..

text \<open>
  @{term "translation ` H"} denotes Jacobson's @{text "H\<^sub>R(G)"} and
  @{term "Translations"} denotes Jacobson's @{text "G\<^sub>R"}.
\<close>

text \<open>p 53, ll 6--7\<close>
theorem right_translations_of_subgroup_are_transformation_group [intro]:
  "transformation_group (translation ` H) G"
proof -
  have "subgroup ((\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R) ` H) Translations (compose G) (identity G)"
    by (rule image_subgroup) unfold_locales
  also have "subgroup Translations transformation.Sym (compose G) (identity G)" ..
  finally interpret left_coset: subgroup "translation ` H" transformation.Sym "compose G" "identity G"
    by (auto intro: transformation.symmetric.inverse_subgroupD cong: image_cong
      simp: image_image transformation.symmetric.Units_def simp del: translation_unit_eq)
  show ?thesis ..
qed

text \<open>p 53, ll 6--7\<close>
interpretation transformation_group "translation ` H" G ..

text \<open>Equation 23 for left cosets\<close>
text \<open>p 53, ll 7--8\<close>
theorem Left_Coset_is_orbit:
  "x \<in> G \<Longrightarrow> x \<cdot>| H = orbit.Class x"
  using translation_apply
  by (auto simp: orbit_equality Left_Coset_def) (metis imageI sub)

end (* subgroup_of_group *)


subsection \<open>Congruences.  Quotient Monoids and Groups\<close>

text \<open>Def 1.4\<close>
text \<open>p 54, ll 19--22\<close>
locale monoid_congruence = monoid + equivalence where S = M +
  assumes cong: "\<lbrakk> (a, a') \<in> E; (b, b') \<in> E \<rbrakk> \<Longrightarrow> (a \<cdot> b, a' \<cdot> b') \<in> E"
begin

text \<open>p 54, ll 26--28\<close>
theorem Class_cong:
  "\<lbrakk> Class a = Class a'; Class b = Class b'; a \<in> M; a' \<in> M; b \<in> M; b' \<in> M \<rbrakk> \<Longrightarrow> Class (a \<cdot> b) = Class (a' \<cdot> b')"
  by (simp add: Class_equivalence cong)

text \<open>p 54, ll 28--30\<close>
definition quotient_composition (infixl "[\<cdot>]" 70)
  where "quotient_composition = (\<lambda>A \<in> M / E. \<lambda>B \<in> M / E. THE C. \<exists>a \<in> A. \<exists>b \<in> B. C = Class (a \<cdot> b))"

text \<open>p 54, ll 28--30\<close>
theorem Class_commutes_with_composition:
  "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> Class a [\<cdot>] Class b = Class (a \<cdot> b)"
  by (auto simp: quotient_composition_def intro: Class_cong [OF Class_eq Class_eq] del: equalityI)

text \<open>p 54, ll 30--31\<close>
theorem quotient_composition_closed [intro, simp]:
  "\<lbrakk> A \<in> M / E; B \<in> M / E \<rbrakk> \<Longrightarrow> A [\<cdot>] B \<in> M / E"
  by (erule quotient_ClassE)+ (simp add: Class_commutes_with_composition)

text \<open>p 54, l 32; p 55, ll 1--3\<close>
sublocale quotient: monoid "M / E" "([\<cdot>])" "Class \<one>"
  by unfold_locales (auto simp: Class_commutes_with_composition associative elim!: quotient_ClassE)

end (* monoid_congruence *)

text \<open>p 55, ll 16--17\<close>
locale group_congruence = group + monoid_congruence where M = G begin

text \<open>p 55, ll 16--17\<close>
notation quotient_composition (infixl "[\<cdot>]" 70)

text \<open>p 55, l 18\<close>
theorem Class_right_inverse:
  "a \<in> G \<Longrightarrow> Class a [\<cdot>] Class (inverse a) = Class \<one>"
  by (simp add: Class_commutes_with_composition)

text \<open>p 55, l 18\<close>
theorem Class_left_inverse:
  "a \<in> G \<Longrightarrow> Class (inverse a) [\<cdot>] Class a = Class \<one>"
  by (simp add: Class_commutes_with_composition)

text \<open>p 55, l 18\<close>
theorem Class_invertible:
  "a \<in> G \<Longrightarrow> quotient.invertible (Class a)"
  by (blast intro!: Class_right_inverse Class_left_inverse)+

text \<open>p 55, l 18\<close>
theorem Class_commutes_with_inverse:
  "a \<in> G \<Longrightarrow> quotient.inverse (Class a) = Class (inverse a)"
  by (rule quotient.inverse_equality) (auto simp: Class_right_inverse Class_left_inverse)

text \<open>p 55, l 17\<close>
sublocale quotient: group "G / E" "([\<cdot>])" "Class \<one>"
  by unfold_locales (metis Block_self Class_invertible element_exists)

end (* group_congruence *)

text \<open>Def 1.5\<close>
text \<open>p 55, ll 22--25\<close>
locale normal_subgroup =
  subgroup_of_group K G "(\<cdot>)" \<one> for K and G and composition (infixl "\<cdot>" 70) and unit ("\<one>") +
  assumes normal: "\<lbrakk> g \<in> G; k \<in> K \<rbrakk> \<Longrightarrow> inverse g \<cdot> k \<cdot> g \<in> K"

text \<open>Lemmas from the proof of Thm 1.6\<close>

context subgroup_of_group begin

text \<open>We use @{term H} for @{term K}.\<close>
text \<open>p 56, ll 14--16\<close>
theorem Left_equals_Right_coset_implies_normality:
  assumes [simp]: "\<And>g. g \<in> G \<Longrightarrow> g \<cdot>| H = H |\<cdot> g"
  shows "normal_subgroup H G (\<cdot>) \<one>"
proof
  fix g k
  assume [simp]: "g \<in> G" "k \<in> H"
  have "k \<cdot> g \<in> g \<cdot>| H" by auto
  then obtain k' where "k \<cdot> g = g \<cdot> k'" and "k' \<in> H" by blast
  then show "inverse g \<cdot> k \<cdot> g \<in> H" by (simp add: associative invertible_left_inverse2)
qed

end (* subgroup_of_group *)

text \<open>Thm 1.6, first part\<close>

context group_congruence begin

text \<open>Jacobson's $K$\<close>
text \<open>p 56, l 29\<close>
definition "Normal = Class \<one>"

text \<open>p 56, ll 3--6\<close>
interpretation subgroup "Normal" G "(\<cdot>)" \<one>
  unfolding Normal_def
proof (rule subgroupI)
  fix k1 and k2
  assume K: "k1 \<in> Class \<one>" "k2 \<in> Class \<one>"
  then have "k1 \<cdot> k2 \<in> Class (k1 \<cdot> k2)" by blast
  also have "\<dots> = Class k1 [\<cdot>] Class k2" using K by (auto simp add: Class_commutes_with_composition Class_closed)
  also have "\<dots> = Class \<one> [\<cdot>] Class \<one>" using K by (metis ClassD Class_eq unit_closed)
  also have "\<dots> = Class \<one>" by simp
  finally show "k1 \<cdot> k2 \<in> Class \<one>" .
next
  fix k
  assume K: "k \<in> Class \<one>"
  then have "inverse k \<in> Class (inverse k)" by blast
  also have "\<dots> = quotient.inverse (Class k)" using Class_commutes_with_inverse K by blast
  also have "\<dots> = quotient.inverse (Class \<one>)" using Block_self K by auto
  also have "\<dots> = Class \<one>" using quotient.inverse_unit by blast
  finally show "inverse k \<in> Class \<one>" .
qed auto

text \<open>Coset notation\<close>
text \<open>p 56, ll 5--6\<close>
interpretation subgroup_of_group "Normal" G "(\<cdot>)" \<one> ..

text \<open>Equation 25 for right cosets\<close>
text \<open>p 55, ll 29--30; p 56, ll 6--11\<close>
theorem Right_Coset_Class_unit:
  assumes g: "g \<in> G" shows "Normal |\<cdot> g = Class g"
  unfolding Normal_def
proof auto
  fix a  \<comment> \<open>ll 6--8\<close>
  assume a: "a \<in> Class g"
  from a g have "a \<cdot> inverse g \<in> Class (a \<cdot> inverse g)" by blast
  also from a g have "\<dots> = Class a [\<cdot>] Class (inverse g)"
    by (simp add: Class_commutes_with_composition block_closed)
  also from a g have "\<dots> = Class g [\<cdot>] quotient.inverse (Class g)"
    using Block_self Class_commutes_with_inverse by auto
  also from g have "\<dots> = Class \<one>" by simp
  finally show "a \<in> Class \<one> |\<cdot> g"
    unfolding Right_Coset_def
    by simp (metis Class_closed a associative g inverse_equality invertible invertible_def right_unit) 
next
  fix a  \<comment> \<open>ll 8--9\<close>
  assume a: "a \<in> Class \<one> |\<cdot> g"
  then obtain k where eq: "a = k \<cdot> g" and k: "k \<in> Class \<one>" by blast
  with g have "Class a = Class k [\<cdot>] Class g" using Class_commutes_with_composition by auto
  also from k have "\<dots> = Class \<one> [\<cdot>] Class g" using Block_self by auto
  also from g have "\<dots> = Class g" by simp
  finally show "a \<in> Class g" using g eq k composition_closed quotient.unit_closed by blast
qed

text \<open>Equation 25 for left cosets\<close>
text \<open>p 55, ll 29--30; p 56, ll 6--11\<close>
theorem Left_Coset_Class_unit:
  assumes g: "g \<in> G" shows "g \<cdot>| Normal = Class g"
  unfolding Normal_def
proof auto
  fix a  \<comment> \<open>ll 6--8\<close>
  assume a: "a \<in> Class g"
  from a g have "inverse g \<cdot> a \<in> Class (inverse g \<cdot> a)" by blast
  also from a g have "\<dots> = Class (inverse g) [\<cdot>] Class a"
    by (simp add: Class_commutes_with_composition block_closed)
  also from a g have "\<dots> = quotient.inverse (Class g) [\<cdot>] Class g"
    using Block_self Class_commutes_with_inverse by auto
  also from g have "\<dots> = Class \<one>" by simp
  finally show "a \<in> g \<cdot>| Class \<one>"
    unfolding Left_Coset_def
    by simp (metis Class_closed a associative g inverse_equality invertible invertible_def right_unit) 
next
  fix a  \<comment> \<open>ll 8--9, ``the same thing holds''\<close>
  assume a: "a \<in> g \<cdot>| Class \<one>"
  then obtain k where eq: "a = g \<cdot> k" and k: "k \<in> Class \<one>" by blast
  with g have "Class a = Class g [\<cdot>] Class k" using Class_commutes_with_composition by auto
  also from k have "\<dots> = Class g [\<cdot>] Class \<one>" using Block_self by auto
  also from g have "\<dots> = Class g" by simp
  finally show "a \<in> Class g" using g eq k composition_closed quotient.unit_closed by blast
qed

text \<open>Thm 1.6, statement of first part\<close>
text \<open>p 55, ll 28--29; p 56, ll 12--16\<close>
theorem Class_unit_is_normal:
  "normal_subgroup Normal G (\<cdot>) \<one>"
proof -
  {
    fix g
    assume "g \<in> G"
    then have "g \<cdot>| Normal = Normal |\<cdot> g" by (simp add: Right_Coset_Class_unit Left_Coset_Class_unit)
  }
  then show ?thesis by (rule Left_equals_Right_coset_implies_normality)
qed

sublocale normal: normal_subgroup Normal G "(\<cdot>)" \<one>
  by (fact Class_unit_is_normal)

end (* group_congruence *)

context normal_subgroup begin

text \<open>p 56, ll 16--19\<close>
theorem Left_equals_Right_coset:
  "g \<in> G \<Longrightarrow> g \<cdot>| K = K |\<cdot> g"
proof
  assume [simp]: "g \<in> G"
  show "K |\<cdot> g \<subseteq> g \<cdot>| K"
  proof
    fix x
    assume x: "x \<in> K |\<cdot> g"
    then obtain k where "x = k \<cdot> g" and [simp]: "k \<in> K" by (auto simp add: Right_Coset_def)
    then have "x = g \<cdot> (inverse g \<cdot> k \<cdot> g)" by (simp add: associative invertible_right_inverse2)
    also from normal have "\<dots> \<in> g \<cdot>| K" by (auto simp add: Left_Coset_def)
    finally show "x \<in> g \<cdot>| K" .
  qed
next
  assume [simp]: "g \<in> G"
  show "g \<cdot>| K \<subseteq> K |\<cdot> g"
  proof
    fix x
    assume x: "x \<in> g \<cdot>| K"
    then obtain k where "x = g \<cdot> k" and [simp]: "k \<in> K" by (auto simp add: Left_Coset_def)
    then have "x = (inverse (inverse g) \<cdot> k \<cdot> inverse g) \<cdot> g" by (simp add: associative del: invertible_right_inverse)
    also from normal [where g = "inverse g"] have "\<dots> \<in> K |\<cdot> g" by (auto simp add: Right_Coset_def)
    finally show "x \<in> K |\<cdot> g" .
  qed
qed

text \<open>Thm 1.6, second part\<close>

text \<open>p 55, ll 31--32; p 56, ll 20--21\<close>
definition "Congruence = {(a, b). a \<in> G \<and> b \<in> G \<and> inverse a \<cdot> b \<in> K}"

text \<open>p 56, ll 21--22\<close>
interpretation right_translations_of_group ..

text \<open>p 56, ll 21--22\<close>
interpretation transformation_group "translation ` K" G rewrites "Orbit_Relation = Congruence"
proof -
  interpret transformation_group "translation ` K" G ..
  show "Orbit_Relation = Congruence"
    unfolding Orbit_Relation_def Congruence_def
    by (force simp: invertible_left_inverse2 invertible_right_inverse2 translation_apply simp del: restrict_apply)
qed rule

text \<open>p 56, ll 20--21\<close>
lemma CongruenceI: "\<lbrakk> a = b \<cdot> k; a \<in> G; b \<in> G; k \<in> K \<rbrakk> \<Longrightarrow> (a, b) \<in> Congruence"
  by (clarsimp simp: Congruence_def associative inverse_composition_commute)

text \<open>p 56, ll 20--21\<close>
lemma CongruenceD: "(a, b) \<in> Congruence \<Longrightarrow> \<exists>k\<in>K. a = b \<cdot> k"
  by (drule orbit.symmetric) (force simp: Congruence_def invertible_right_inverse2)

text \<open>
  ``We showed in the last section that the relation we are considering is an equivalence relation in
  @{term G} for any subgroup @{term K} of @{term G}.  We now proceed to show that normality of @{term K}
  ensures that [...] $a \equiv b \pmod{K}$ is a congruence.''
\<close>
text \<open>p 55, ll 30--32; p 56, ll 1, 22--28\<close>
sublocale group_congruence where E = Congruence rewrites "Normal = K"
proof -
  show "group_congruence G (\<cdot>) \<one> Congruence"
  proof unfold_locales
    note CongruenceI [intro] CongruenceD [dest]
    fix a g b h
    assume 1: "(a, g) \<in> Congruence" and 2: "(b, h) \<in> Congruence"
    then have G: "a \<in> G" "g \<in> G" "b \<in> G" "h \<in> G" unfolding Congruence_def by clarify+
    from 1 obtain k1 where a: "a = g \<cdot> k1" and k1: "k1 \<in> K" by blast
    from 2 obtain k2 where b: "b = h \<cdot> k2" and k2: "k2 \<in> K" by blast
    from G Left_equals_Right_coset have "K |\<cdot> h = h \<cdot>| K" by blast
    with k1 obtain k3 where c: "k1 \<cdot> h = h \<cdot> k3" and k3: "k3 \<in> K"
      unfolding Left_Coset_def Right_Coset_def by blast
    from G k1 k2 a b have "a \<cdot> b = g \<cdot> k1 \<cdot> h \<cdot> k2" by (simp add: associative)
    also from G k1 k3 c have "\<dots> = g \<cdot> h \<cdot> k3 \<cdot> k2" by (simp add: associative)
    also have "\<dots> = (g \<cdot> h) \<cdot> (k3 \<cdot> k2)" using G k2 k3 by (simp add: associative)
    finally show "(a \<cdot> b, g \<cdot> h) \<in> Congruence" using G k2 k3 by blast
  qed
  then interpret group_congruence where E = Congruence .
  show "Normal = K"
    unfolding Normal_def orbit.Class_def unfolding Congruence_def
    using invertible_inverse_inverse submonoid_inverse_closed by fastforce 
qed

end (* normal_subgroup *)  (* deletes translations and orbits, recovers Class for congruence class *)

context group begin

text \<open>Pulled out of @{locale normal_subgroup} to achieve standard notation.\<close>
text \<open>p 56, ll 31--32\<close>
abbreviation Factor_Group (infixl "'/'/" 75)
  where "S // K \<equiv> S / (normal_subgroup.Congruence K G (\<cdot>) \<one>)"

end (* group *)

context normal_subgroup begin

text \<open>p 56, ll 28--29\<close>
theorem Class_unit_normal_subgroup: "Class \<one> = K"
  unfolding Class_def unfolding Congruence_def
  using invertible_inverse_inverse submonoid_inverse_closed by fastforce

text \<open>p 56, ll 1--2; p 56, l 29\<close>
theorem Class_is_Left_Coset:
  "g \<in> G \<Longrightarrow> Class g = g \<cdot>| K"
  using Left_Coset_Class_unit Class_unit_normal_subgroup by simp

text \<open>p 56, l 29\<close>
lemma Left_CosetE: "\<lbrakk> A \<in> G // K; \<And>a. a \<in> G \<Longrightarrow> P (a \<cdot>| K) \<rbrakk> \<Longrightarrow> P A"
  by (metis Class_is_Left_Coset quotient_ClassE)

text \<open>Equation 26\<close>
text \<open>p 56, ll 32--34\<close>
theorem factor_composition [simp]:
  "\<lbrakk> g \<in> G; h \<in> G \<rbrakk> \<Longrightarrow> (g \<cdot>| K) [\<cdot>] (h \<cdot>| K) = g \<cdot> h \<cdot>| K"
  using Class_commutes_with_composition Class_is_Left_Coset by auto

text \<open>p 56, l 35\<close>
theorem factor_unit:
  "K = \<one> \<cdot>| K"
  using Class_is_Left_Coset Class_unit_normal_subgroup by blast

text \<open>p 56, l 35\<close>
theorem factor_inverse [simp]:
  "g \<in> G \<Longrightarrow> quotient.inverse (g \<cdot>| K) = (inverse g \<cdot>| K)"
  using Class_commutes_with_inverse Class_is_Left_Coset by auto

end (* normal_subgroup *)

text \<open>p 57, ll 4--5\<close>
locale subgroup_of_abelian_group = subgroup_of_group H G "(\<cdot>)" \<one> + abelian_group G "(\<cdot>)" \<one>
  for H and G and composition (infixl "\<cdot>" 70) and unit ("\<one>")

text \<open>p 57, ll 4--5\<close>
sublocale subgroup_of_abelian_group \<subseteq> normal_subgroup H G "(\<cdot>)" \<one>
  using commutative invertible_right_inverse2 by unfold_locales auto


subsection \<open>Homomorphims\<close>

text \<open>Def 1.6\<close>
text \<open>p 58, l 33; p 59, ll 1--2\<close>
locale monoid_homomorphism =
  map \<eta> M M'+  source: monoid M "(\<cdot>)" \<one> + target: monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl "\<cdot>" 70) and unit ("\<one>")
    and M' and composition' (infixl "\<cdot>''" 70) and unit' ("\<one>''") +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> (x \<cdot> y) = \<eta> x \<cdot>' \<eta> y"
    and commutes_with_unit: "\<eta> \<one> = \<one>'"
begin

text \<open>Jacobson notes that @{thm [source] commutes_with_unit} is not necessary for groups, but doesn't make use of that later.\<close>

text \<open>p 58, l 33; p 59, ll 1--2\<close>
notation source.invertible ("invertible _" [100] 100)
notation source.inverse ("inverse _" [100] 100)
notation target.invertible ("invertible'' _" [100] 100)
notation target.inverse ("inverse'' _" [100] 100)

end (* monoid_homomorphism *)

text \<open>p 59, ll 29--30\<close>
locale monoid_epimorphism = monoid_homomorphism + surjective_map \<eta> M M'

text \<open>p 59, l 30\<close>
locale monoid_monomorphism = monoid_homomorphism + injective_map \<eta> M M'

text \<open>p 59, ll 30--31\<close>
sublocale monoid_isomorphism \<subseteq> monoid_epimorphism
  by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)

text \<open>p 59, ll 30--31\<close>
sublocale monoid_isomorphism \<subseteq> monoid_monomorphism
  by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)

context monoid_homomorphism begin

text \<open>p 59, ll 33--34\<close>
theorem invertible_image_lemma:
  assumes "invertible a" "a \<in> M"
  shows "\<eta> a \<cdot>' \<eta> (inverse a) = \<one>'" and "\<eta> (inverse a) \<cdot>' \<eta> a = \<one>'"
  using assms commutes_with_composition commutes_with_unit source.inverse_equality
  by auto (metis source.invertible_inverse_closed source.invertible_left_inverse)

text \<open>p 59, l 34; p 60, l 1\<close>
theorem invertible_target_invertible [intro, simp]:
  "\<lbrakk> invertible a; a \<in> M \<rbrakk> \<Longrightarrow> invertible' (\<eta> a)"
  using invertible_image_lemma by blast

text \<open>p 60, l 1\<close>
theorem invertible_commutes_with_inverse:
  "\<lbrakk> invertible a; a \<in> M \<rbrakk> \<Longrightarrow> \<eta> (inverse a) = inverse' (\<eta> a)"
  using invertible_image_lemma target.inverse_equality by fastforce

end (* monoid_homomorphism *)

text \<open>p 60, ll 32--34; p 61, l 1\<close>
sublocale monoid_congruence \<subseteq> natural: monoid_homomorphism Class M "(\<cdot>)" \<one> "M / E" "([\<cdot>])" "Class \<one>"
  by unfold_locales (auto simp: PiE_I Class_commutes_with_composition)

text \<open>Fundamental Theorem of Homomorphisms of Monoids\<close>

text \<open>p 61, ll 5, 14--16\<close>
sublocale monoid_homomorphism \<subseteq> image: submonoid "\<eta> ` M" M' "(\<cdot>')" "\<one>'"
  by unfold_locales (auto simp: commutes_with_composition [symmetric] commutes_with_unit [symmetric])

text \<open>p 61, l 4\<close>
locale monoid_homomorphism_fundamental = monoid_homomorphism begin

text \<open>p 61, ll 17--18\<close>
sublocale fiber_relation \<eta> M M' ..
notation Fiber_Relation ("E'(_')")

text \<open>p 61, ll 6--7, 18--20\<close>
sublocale monoid_congruence where E = "E(\<eta>)"
  using Class_eq
  by unfold_locales (rule Class_equivalence [THEN iffD1],
    auto simp: left_closed right_closed commutes_with_composition Fiber_equality)

text \<open>p 61, ll 7--9\<close>
text \<open>
  @{term induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term induced} is unique: @{thm [display] factorization} @{thm [display] uniqueness}.
\<close>

text \<open>p 61, l 20\<close>
notation quotient_composition (infixl "[\<cdot>]" 70)

text \<open>p 61, ll 7--8, 22--25\<close>
sublocale induced: monoid_homomorphism induced "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" "M'" "(\<cdot>')" "\<one>'"
  apply unfold_locales
    apply (auto simp: commutes_with_unit)
  apply (fastforce simp: commutes_with_composition commutes_with_unit Class_commutes_with_composition)
  done

text \<open>p 61, ll 9, 26\<close>
sublocale natural: monoid_epimorphism Class M "(\<cdot>)" \<one> "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" ..

text \<open>p 61, ll 9, 26--27\<close>
sublocale induced: monoid_monomorphism induced "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" "M'" "(\<cdot>')" "\<one>'" ..

end (* monoid_homomorphism_fundamental *)

text \<open>p 62, ll 12--13\<close>
locale group_homomorphism =
  monoid_homomorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'" +
  source: group G "(\<cdot>)" \<one> + target: group G' "(\<cdot>')" "\<one>'"
  for \<eta> and G and composition (infixl "\<cdot>" 70) and unit ("\<one>")
    and G' and composition' (infixl "\<cdot>''" 70) and unit' ("\<one>''")
begin

text \<open>p 62, l 13\<close>
sublocale image: subgroup "\<eta> ` G" G' "(\<cdot>')" "\<one>'"
  using invertible_image_lemma by unfold_locales auto

text \<open>p 62, ll 13--14\<close>
definition "Ker = \<eta> -` {\<one>'} \<inter> G"

text \<open>p 62, ll 13--14\<close>
lemma Ker_equality:
  "Ker = {a | a. a \<in> G \<and> \<eta> a = \<one>'}"
  unfolding Ker_def by auto

text \<open>p 62, ll 13--14\<close>
lemma Ker_closed [intro, simp]:
  "a \<in> Ker \<Longrightarrow> a \<in> G"
  unfolding Ker_def by simp

text \<open>p 62, ll 13--14\<close>
lemma Ker_image [intro]: (* loops as a simprule *)
  "a \<in> Ker \<Longrightarrow> \<eta> a = \<one>'"
  unfolding Ker_def by simp

text \<open>p 62, ll 13--14\<close>
lemma Ker_memI [intro]: (* loops as a simprule *)
  "\<lbrakk> \<eta> a = \<one>'; a \<in> G \<rbrakk> \<Longrightarrow> a \<in> Ker"
  unfolding Ker_def by simp

text \<open>p 62, ll 15--16\<close>
sublocale kernel: normal_subgroup Ker G
proof -
  interpret kernel: submonoid Ker G
    unfolding Ker_def by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)
  interpret kernel: subgroup Ker G
    by unfold_locales (force intro: source.invertible_right_inverse simp: Ker_image invertible_commutes_with_inverse)
  show "normal_subgroup Ker G (\<cdot>) \<one>"
    apply unfold_locales
    unfolding Ker_def
    by (auto simp: commutes_with_composition invertible_image_lemma(2))
qed

text \<open>p 62, ll 17--20\<close>
theorem injective_iff_kernel_unit:
  "inj_on \<eta> G \<longleftrightarrow> Ker = {\<one>}"
proof (rule Not_eq_iff [THEN iffD1, OF iffI])
  assume "Ker \<noteq> {\<one>}"
  then obtain b where b: "b \<in> Ker" "b \<noteq> \<one>" by blast
  then have "\<eta> b = \<eta> \<one>" by (simp add: Ker_image)
  with b show "\<not> inj_on \<eta> G"  by (meson inj_onD kernel.sub source.unit_closed)
next
  assume "\<not> inj_on \<eta> G"
  then obtain a b where "a \<noteq> b" and ab: "a \<in> G" "b \<in> G" "\<eta> a = \<eta> b" by (meson inj_onI)
  then have "inverse a \<cdot> b \<noteq> \<one>" "\<eta> (inverse a \<cdot> b) = \<one>'"
    using ab source.invertible_right_inverse2
    by force (metis ab commutes_with_composition invertible_image_lemma(2) source.invertible source.invertible_inverse_closed)
  then have "inverse a \<cdot> b \<in> Ker" using Ker_memI ab by blast
  then show "Ker \<noteq> {\<one>}" using \<open>inverse a \<cdot> b \<noteq> \<one>\<close> by blast
qed

end (* group_homomorphism *)

text \<open>p 62, l 24\<close>
locale group_epimorphism = group_homomorphism + monoid_epimorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'"

text \<open>p 62, l 21\<close>
locale normal_subgroup_in_kernel =
  group_homomorphism + contained: normal_subgroup L G "(\<cdot>)" \<one> for L +
  assumes subset: "L \<subseteq> Ker"
begin

text \<open>p 62, l 21\<close>
notation contained.quotient_composition (infixl "[\<cdot>]" 70)

text \<open>"homomorphism onto @{term "G // L"}"\<close>
text \<open>p 62, ll 23--24\<close>
sublocale natural: group_epimorphism contained.Class G "(\<cdot>)" \<one> "G // L" "([\<cdot>])" "contained.Class \<one>" ..

text \<open>p 62, ll 25--26\<close>
theorem left_coset_equality:
  assumes eq: "a \<cdot>| L = b \<cdot>| L" and [simp]: "a \<in> G" and b: "b \<in> G"
  shows "\<eta> a = \<eta> b"
proof -
  obtain l where l: "b = a \<cdot> l" "l \<in> L"
    by (metis b contained.Class_is_Left_Coset contained.Class_self eq kernel.Left_Coset_memE)
  then have "\<eta> a = \<eta> a \<cdot>' \<eta> l" using Ker_image monoid_homomorphism.commutes_with_composition subset by auto
  also have "\<dots> = \<eta> b" by (simp add: commutes_with_composition l)
  finally show ?thesis .
qed

text \<open>$\bar{\eta}$\<close>
text \<open>p 62, ll 26--27\<close>
definition "induced = (\<lambda>A \<in> G // L. THE b. \<exists>a \<in> G. a \<cdot>| L = A \<and> b = \<eta> a)"

text \<open>p 62, ll 26--27\<close>
lemma induced_closed [intro, simp]:
  assumes [simp]: "A \<in> G // L" shows "induced A \<in> G'"
proof -
  obtain a where a: "a \<in> G" "a \<cdot>| L = A" using contained.Class_is_Left_Coset contained.Partition_def assms by auto
  have "(THE b. \<exists>a \<in> G. a \<cdot>| L = A \<and> b = \<eta> a) \<in> G'"
    apply (rule theI2)
    using a by (auto intro: left_coset_equality)
  then show ?thesis unfolding induced_def by simp
qed

text \<open>p 62, ll 26--27\<close>
lemma induced_undefined [intro, simp]:
  "A \<notin> G // L \<Longrightarrow> induced A = undefined"
  unfolding induced_def by simp

text \<open>p 62, ll 26--27\<close>
theorem induced_left_coset_closed [intro, simp]:
  "a \<in> G \<Longrightarrow> induced (a \<cdot>| L) \<in> G'"
  using contained.Class_is_Left_Coset contained.Class_in_Partition by auto 

text \<open>p 62, ll 26--27\<close>
theorem induced_left_coset_equality [simp]:
  assumes [simp]: "a \<in> G" shows "induced (a \<cdot>| L) = \<eta> a"
proof -
  have "(THE b. \<exists>a' \<in> G. a' \<cdot>| L = a \<cdot>| L \<and> b = \<eta> a') = \<eta> a"
    by (rule the_equality) (auto intro: left_coset_equality)
  then show ?thesis unfolding induced_def
    using contained.Class_is_Left_Coset contained.Class_in_Partition by auto 
qed

text \<open>p 62, l 27\<close>
theorem induced_Left_Coset_commutes_with_composition [simp]:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> induced ((a \<cdot>| L) [\<cdot>] (b \<cdot>| L)) = induced (a \<cdot>| L) \<cdot>' induced (b \<cdot>| L)"
  by (simp add: commutes_with_composition)

text \<open>p 62, ll 27--28\<close>
theorem induced_group_homomorphism:
  "group_homomorphism induced (G // L) ([\<cdot>]) (contained.Class \<one>) G' (\<cdot>') \<one>'"
  apply unfold_locales
    apply (auto elim!: contained.Left_CosetE simp: commutes_with_composition commutes_with_unit)
  using contained.factor_unit induced_left_coset_equality apply (fastforce simp: contained.Class_unit_normal_subgroup)
  done

text \<open>p 62, l 28\<close>
sublocale induced: group_homomorphism induced "G // L" "([\<cdot>])" "contained.Class \<one>" G' "(\<cdot>')" "\<one>'"
  by (fact induced_group_homomorphism)

text \<open>p 62, ll 28--29\<close>
theorem factorization_lemma: "a \<in> G \<Longrightarrow> compose G induced contained.Class a = \<eta> a"
  unfolding compose_def by (simp add: contained.Class_is_Left_Coset)

text \<open>p 62, ll 29--30\<close>
theorem factorization [simp]: "compose G induced contained.Class = \<eta>"
  by rule (simp add: compose_def contained.Class_is_Left_Coset)

text \<open>
  Jacobson does not state the uniqueness of @{term induced} explicitly but he uses it later,
  for rings, on p 107.
\<close>
text \<open>p 62, l 30\<close>
theorem uniqueness:
  assumes map: "\<beta> \<in> G // L \<rightarrow>\<^sub>E G'"
    and factorization: "compose G \<beta> contained.Class = \<eta>"
  shows "\<beta> = induced"
proof
  fix A
  show "\<beta> A = induced A"
  proof (cases "A \<in> G // L")
    case True
    then obtain a where [simp]: "A = contained.Class a" "a \<in> G" by fast
    then have "\<beta> (contained.Class a) = \<eta> a" by (metis compose_eq factorization)
    also have "\<dots> = induced (contained.Class a)" by (simp add: contained.Class_is_Left_Coset)
    finally show ?thesis by simp
  qed (simp add: induced_def PiE_arb [OF map])
qed

text \<open>p 62, l 31\<close>
theorem induced_image:
  "induced ` (G // L) = \<eta> ` G"
  by (metis factorization contained.natural.surjective surj_compose)

text \<open>p 62, l 33\<close>
interpretation L: normal_subgroup L Ker
  by unfold_locales (auto simp: subset, metis kernel.sub kernel.subgroup_inverse_equality contained.normal)

text \<open>p 62, ll 31--33\<close>
theorem induced_kernel:
  "induced.Ker = Ker / L.Congruence" (* Ker // L is apparently not the right thing *)
proof -
  have "induced.Ker = { a \<cdot>| L | a. a \<in> G \<and> a \<in> Ker }"
    unfolding induced.Ker_equality
    by simp (metis (hide_lams) contained.Class_is_Left_Coset Ker_image Ker_memI
        induced_left_coset_equality contained.Class_in_Partition contained.representant_exists)
  also have "\<dots> = Ker / L.Congruence"
    using L.Class_is_Left_Coset L.Class_in_Partition
    by auto (metis L.Class_is_Left_Coset L.representant_exists kernel.sub)
  finally show ?thesis .
qed

text \<open>p 62, ll 34--35\<close>
theorem induced_inj_on:
  "inj_on induced (G // L) \<longleftrightarrow> L = Ker"
  apply (simp add: induced.injective_iff_kernel_unit induced_kernel contained.Class_unit_normal_subgroup)
  apply rule
  using L.block_exists apply auto [1]
  using L.Block_self L.Class_unit_normal_subgroup L.quotient.unit_closed L.representant_exists
  apply auto
  done

end (* normal_subgroup_in_kernel *)

text \<open>Fundamental Theorem of Homomorphisms of Groups\<close>

text \<open>p 63, l 1\<close>
locale group_homomorphism_fundamental = group_homomorphism begin

text \<open>p 63, l 1\<close>
notation kernel.quotient_composition (infixl "[\<cdot>]" 70)

text \<open>p 63, l 1\<close>
sublocale normal_subgroup_in_kernel where L = Ker by unfold_locales rule

text \<open>p 62, ll 36--37; p 63, l 1\<close>
text \<open>
  @{term induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term induced} is unique: @{thm [display] factorization} @{thm [display] uniqueness}
\<close>

end (* group_homomorphism_fundamental *)

text \<open>p 63, l 5\<close>
locale group_isomorphism = group_homomorphism + bijective_map \<eta> G G' begin

text \<open>p 63, l 5\<close>
sublocale monoid_isomorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'" 
  by unfold_locales (auto simp: commutes_with_composition)

text \<open>p 63, l 6\<close>
lemma inverse_group_isomorphism:
  "group_isomorphism (restrict (inv_into G \<eta>) G') G' (\<cdot>') \<one>' G (\<cdot>) \<one>"
  using commutes_with_composition commutes_with_unit surjective by unfold_locales auto

end (* group_isomorphism *)

text \<open>p 63, l 6\<close>
definition isomorphic_as_groups (infixl "\<cong>\<^sub>G" 50)
  where "\<G> \<cong>\<^sub>G \<G>' \<longleftrightarrow> (let (G, composition, unit) = \<G>; (G', composition', unit') = \<G>' in
  (\<exists>\<eta>. group_isomorphism \<eta> G composition unit G' composition' unit'))"

text \<open>p 63, l 6\<close>
lemma isomorphic_as_groups_symmetric:
  "(G, composition, unit) \<cong>\<^sub>G (G', composition', unit') \<Longrightarrow> (G', composition', unit') \<cong>\<^sub>G (G, composition, unit)"
  by (simp add: isomorphic_as_groups_def) (meson group_isomorphism.inverse_group_isomorphism)

text \<open>p 63, l 1\<close>
sublocale group_isomorphism \<subseteq> group_epimorphism ..

text \<open>p 63, l 1\<close>
locale group_epimorphism_fundamental = group_homomorphism_fundamental + group_epimorphism begin

text \<open>p 63, ll 1--2\<close>
interpretation image: group_homomorphism induced "G // Ker" "([\<cdot>])" "kernel.Class \<one>" "(\<eta> ` G)" "(\<cdot>')" "\<one>'"
  by (simp add: surjective group_homomorphism_fundamental.intro induced_group_homomorphism)

text \<open>p 63, ll 1--2\<close>
sublocale image: group_isomorphism induced "G // Ker" "([\<cdot>])" "kernel.Class \<one>" "(\<eta> ` G)" "(\<cdot>')" "\<one>'"
  using induced_group_homomorphism
  by unfold_locales (auto simp: bij_betw_def induced_image induced_inj_on induced.commutes_with_composition)

end (* group_epimorphism_fundamental *)

context group_homomorphism begin

text \<open>p 63, ll 5--7\<close>
theorem image_isomorphic_to_factor_group:
  "\<exists>K composition unit. normal_subgroup K G (\<cdot>) \<one> \<and> (\<eta> ` G, (\<cdot>'), \<one>') \<cong>\<^sub>G (G // K, composition, unit)"
proof -
  interpret image: group_epimorphism_fundamental where G' = "\<eta> ` G"
    by unfold_locales (auto simp: commutes_with_composition)
  have "group_isomorphism image.induced (G // Ker) ([\<cdot>]) (kernel.Class \<one>) (\<eta> ` G) (\<cdot>') \<one>'" ..
  then have "(\<eta> ` G, (\<cdot>'), \<one>') \<cong>\<^sub>G (G // Ker, ([\<cdot>]), kernel.Class \<one>)"
    by (simp add: isomorphic_as_groups_def) (meson group_isomorphism.inverse_group_isomorphism)
  moreover have "normal_subgroup Ker G (\<cdot>) \<one>" ..
  ultimately show ?thesis by blast
qed

end (* group_homomorphism *)

end
