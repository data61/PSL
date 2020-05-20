(*
  Copyright (c) 2015--2019 by Clemens Ballarin
  This file is licensed under the 3-clause BSD license.
*)

theory Ring_Theory imports Group_Theory begin

no_notation plus (infixl "+" 65)
no_notation minus (infixl "-" 65)
no_notation uminus ("- _" [81] 80)
no_notation quotient (infixl "'/'/" 90)


section \<open>Rings\<close>

subsection \<open>Definition and Elementary Properties\<close>

text \<open>Def 2.1\<close>
text \<open>p 86, ll 20--28\<close>
locale ring = additive: abelian_group R "(+)" \<zero> + multiplicative: monoid R "(\<cdot>)" \<one>
  for R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>") +
  assumes distributive: "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> a \<cdot> (b + c) = a \<cdot> b + a \<cdot> c"
    "\<lbrakk> a \<in> R; b \<in> R; c \<in> R \<rbrakk> \<Longrightarrow> (b + c) \<cdot> a = b \<cdot> a + c \<cdot> a"
begin

text \<open>p 86, ll 20--28\<close>
notation additive.inverse ("- _" [66] 65)
abbreviation subtraction (infixl "-" 65) where "a - b \<equiv> a + (- b)"  (* or, alternatively, a definition *)

end (* ring *)

text \<open>p 87, ll 10--12\<close>
locale subring =
  additive: subgroup S R "(+)" \<zero> + multiplicative: submonoid S R "(\<cdot>)" \<one>
  for S and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>")

context ring begin

text \<open>p 88, ll 26--28\<close>
lemma right_zero [simp]:
  assumes [simp]: "a \<in> R" shows "a \<cdot> \<zero> = \<zero>"
proof -
  have "a \<cdot> \<zero> = a \<cdot> (\<zero> + \<zero>)" by simp
  also have "\<dots> = a \<cdot> \<zero> + a \<cdot> \<zero>" by (simp add: distributive del: additive.left_unit additive.right_unit)
  finally have "a \<cdot> \<zero> - a \<cdot> \<zero> = a \<cdot> \<zero> + a \<cdot> \<zero> - a \<cdot> \<zero>" by simp
  then show ?thesis by (simp add: additive.associative del: additive.invertible_left_cancel)
qed

text \<open>p 88, l 29\<close>
lemma left_zero [simp]:
  assumes [simp]: "a \<in> R" shows "\<zero> \<cdot> a = \<zero>"
proof -
  have "\<zero> \<cdot> a = (\<zero> + \<zero>) \<cdot> a" by simp
  also have "\<dots> = \<zero> \<cdot> a + \<zero> \<cdot> a" by (simp add: distributive del: additive.left_unit additive.right_unit)
  finally have "\<zero> \<cdot> a - \<zero> \<cdot> a = \<zero> \<cdot> a + \<zero> \<cdot> a - \<zero> \<cdot> a" by simp
  then show ?thesis by (simp add: additive.associative del: additive.invertible_left_cancel)
qed

text \<open>p 88, ll 29--30; p 89, ll 1--2\<close>
lemma left_minus:
  assumes [simp]: "a \<in> R" "b \<in> R" shows "(- a) \<cdot> b = - a \<cdot> b"
proof -
  have "\<zero> = \<zero> \<cdot> b" by simp
  also have "\<dots> = (a - a) \<cdot> b" by simp
  also have "\<dots> = a \<cdot> b + (- a) \<cdot> b" by (simp add: distributive del: additive.invertible_right_inverse)
  finally have "- a \<cdot> b + \<zero> = - a \<cdot> b + a \<cdot> b + (- a) \<cdot> b" by (simp add: additive.associative del: additive.invertible_left_inverse)
  then show ?thesis by simp
qed

text \<open>p 89, l 3\<close>
lemma right_minus:
  assumes [simp]: "a \<in> R" "b \<in> R" shows "a \<cdot> (- b) = - a \<cdot> b"
proof -
  have "\<zero> = a \<cdot> \<zero>" by simp
  also have "\<dots> = a \<cdot> (b - b)" by simp
  also have "\<dots> = a \<cdot> b + a \<cdot> (- b)" by (simp add: distributive del: additive.invertible_right_inverse)
  finally have "- a \<cdot> b + \<zero> = - a \<cdot> b + a \<cdot> b + a \<cdot> (- b)" by (simp add: additive.associative del: additive.invertible_left_inverse)
  then show ?thesis by simp
qed

end (* ring *)


subsection \<open>Ideals, Quotient Rings\<close>

text \<open>p 101, ll 2--5\<close>
locale ring_congruence = ring +
  additive: group_congruence R "(+)" \<zero> E +
  multiplicative: monoid_congruence R "(\<cdot>)" \<one> E
  for E
begin

text \<open>p 101, ll 2--5\<close>
notation additive.quotient_composition (infixl "[+]" 65)
notation additive.quotient.inverse ("[-] _" [66] 65)
notation multiplicative.quotient_composition (infixl "[\<cdot>]" 70)

text \<open>p 101, ll 5--11\<close>
sublocale quotient: ring "R / E" "([+])" "([\<cdot>])" "additive.Class \<zero>" "additive.Class \<one>"
  by unfold_locales
    (auto simp: additive.Class_commutes_with_composition additive.associative additive.commutative
     multiplicative.Class_commutes_with_composition distributive elim!: additive.quotient_ClassE)

end (* ring_congruence *)

text \<open>p 101, ll 12--13\<close>
locale subgroup_of_additive_group_of_ring =
  additive: subgroup I R "(+)" \<zero> + ring R "(+)" "(\<cdot>)" \<zero> \<one>
  for I and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>")
begin

text \<open>p 101, ll 13--14\<close>
definition "Ring_Congruence = {(a, b). a \<in> R \<and> b \<in> R \<and> a - b \<in> I}"

text \<open>p 101, ll 13--14\<close>
lemma Ring_CongruenceI: "\<lbrakk> a - b \<in> I; a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> (a, b) \<in> Ring_Congruence"
  using Ring_Congruence_def by blast

text \<open>p 101, ll 13--14\<close>
lemma Ring_CongruenceD: "(a, b) \<in> Ring_Congruence \<Longrightarrow> a - b \<in> I"
  using Ring_Congruence_def by blast

text \<open>
  Jacobson's definition of ring congruence deviates from that of group congruence; this complicates
  the proof.
\<close>
text \<open>p 101, ll 12--14\<close>
sublocale additive: subgroup_of_abelian_group I R "(+)" \<zero>  (* implies normal_subgroup *)
  rewrites additive_congruence: "additive.Congruence = Ring_Congruence"
proof -
  show "subgroup_of_abelian_group I R (+) \<zero>"
    using additive.commutative additive.invertible_right_inverse2 by unfold_locales auto
  then interpret additive: subgroup_of_abelian_group I R "(+)" \<zero> .
  {
    fix a b
    assume [simp]: "a \<in> R" "b \<in> R"
    have "a - b \<in> I \<longleftrightarrow> - (a - b) \<in> I" by auto
    also have "\<dots> \<longleftrightarrow> - a + b \<in> I" by (simp add: additive.commutative additive.inverse_composition_commute)
    finally have "a - b \<in> I \<longleftrightarrow> - a + b \<in> I" .
  }
  then show "additive.Congruence = Ring_Congruence"
    unfolding additive.Congruence_def Ring_Congruence_def by auto
qed

text \<open>p 101, l 14\<close>
notation additive.Left_Coset (infixl "+|" 65)

end (* subgroup_of_additive_group_of_ring *)

text \<open>Def 2.2\<close>
text \<open>p 101, ll 21--22\<close>
locale ideal = subgroup_of_additive_group_of_ring +
  assumes ideal: "\<lbrakk> a \<in> R; b \<in> I \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> I" "\<lbrakk> a \<in> R; b \<in> I \<rbrakk> \<Longrightarrow> b \<cdot> a \<in> I"

context subgroup_of_additive_group_of_ring begin

text \<open>p 101, ll 14--17\<close>
theorem multiplicative_congruence_implies_ideal:
  assumes "monoid_congruence R (\<cdot>) \<one> Ring_Congruence"
  shows "ideal I R (+) (\<cdot>) \<zero> \<one>"
proof -
  interpret multiplicative: monoid_congruence R "(\<cdot>)" \<one> Ring_Congruence by fact
  show ?thesis
  proof
    fix a b
    assume [simp]: "a \<in> R" "b \<in> I"
    have congs: "(a, a) \<in> Ring_Congruence" "(b, \<zero>) \<in> Ring_Congruence"
      by (auto simp: additive.ClassD additive.Class_unit_normal_subgroup)
    from congs have "(a \<cdot> b, \<zero>) \<in> Ring_Congruence" using multiplicative.cong by fastforce
    then show "a \<cdot> b \<in> I" using additive.Class_unit_normal_subgroup by blast
    from congs have "(b \<cdot> a, \<zero>) \<in> Ring_Congruence" using multiplicative.cong by fastforce
    then show "b \<cdot> a \<in> I"  using additive.Class_unit_normal_subgroup by blast
  qed
qed

end (* subgroup_of_additive_group_of_ring *)

context ideal begin

text \<open>p 101, ll 17--20\<close>
theorem multiplicative_congruence [intro]:
  assumes a: "(a, a') \<in> Ring_Congruence" and b: "(b, b') \<in> Ring_Congruence"
  shows "(a \<cdot> b, a' \<cdot> b') \<in> Ring_Congruence"
proof -
  note Ring_CongruenceI [intro] Ring_CongruenceD [dest]
  from a b have [simp]: "a \<in> R" "a' \<in> R" "b \<in> R" "b' \<in> R" by auto
  from a have [simp]: "a - a' \<in> I" ..
  have "a \<cdot> b - a' \<cdot> b = (a - a') \<cdot> b" by (simp add: distributive left_minus)
  also have "\<dots> \<in> I" by (simp add: ideal)
  finally have ab: "a \<cdot> b - a' \<cdot> b \<in> I" .  \<comment> \<open>ll 18--19\<close>
  from b have [simp]: "b - b' \<in> I" ..
  have "a' \<cdot> b - a' \<cdot> b' = a' \<cdot> (b - b')" by (simp add: distributive right_minus)
  also have "\<dots> \<in> I" by (simp add: ideal)
  finally have a'b': "a' \<cdot> b - a' \<cdot> b' \<in> I" .  \<comment> \<open>l 19\<close>
  have "a \<cdot> b - a' \<cdot> b' = (a \<cdot> b - a' \<cdot> b) + (a' \<cdot> b - a' \<cdot> b')"
    by (simp add: additive.associative) (simp add: additive.associative [symmetric])
  also have "\<dots> \<in> I" using ab a'b' by simp
  finally show "(a \<cdot> b, a' \<cdot> b') \<in> Ring_Congruence" by auto  \<comment> \<open>ll 19--20\<close>
qed

text \<open>p 101, ll 23--24\<close>
sublocale ring_congruence where E = Ring_Congruence by unfold_locales rule

end (* ideal *)

context ring begin

text \<open>Pulled out of @{locale ideal} to achieve standard notation.\<close>
text \<open>p 101, ll 24--26\<close>
abbreviation Quotient_Ring (infixl "'/'/" 75)
  where "S // I \<equiv> S / (subgroup_of_additive_group_of_ring.Ring_Congruence I R (+) \<zero>)"

end (* ring *)

text \<open>p 101, ll 24--26\<close>
locale quotient_ring = ideal begin

text \<open>p 101, ll 24--26\<close>
sublocale quotient: ring "R // I" "([+])" "([\<cdot>])" "additive.Class \<zero>" "additive.Class \<one>" ..

text \<open>p 101, l 26\<close>
lemmas Left_Coset = additive.Left_CosetE

text \<open>Equation 17 (1)\<close>
text \<open>p 101, l 28\<close>
lemmas quotient_addition = additive.factor_composition

text \<open>Equation 17 (2)\<close>
text \<open>p 101, l 29\<close>
theorem quotient_multiplication [simp]:
  "\<lbrakk> a \<in> R; b \<in> R \<rbrakk> \<Longrightarrow> (a +| I) [\<cdot>] (b +| I) = a \<cdot> b +| I"
  using multiplicative.Class_commutes_with_composition additive.Class_is_Left_Coset by auto

text \<open>p 101, l 30\<close>
lemmas quotient_zero = additive.factor_unit
lemmas quotient_negative = additive.factor_inverse

end (* quotient_ring *)


subsection \<open>Homomorphisms of Rings.  Basic Theorems\<close>

text \<open>Def 2.3\<close>
text \<open>p 106, ll 7--9\<close>
locale ring_homomorphism =
  map \<eta> R R' + source: ring R "(+)" "(\<cdot>)" \<zero> \<one> + target: ring R' "(+')" "(\<cdot>')" "\<zero>'" "\<one>'" +
  additive: group_homomorphism \<eta> R "(+)" \<zero> R' "(+')" "\<zero>'" +
  multiplicative: monoid_homomorphism \<eta> R "(\<cdot>)" \<one> R' "(\<cdot>')" "\<one>'"
  for \<eta>
    and R and addition (infixl "+" 65) and multiplication (infixl "\<cdot>" 70) and zero ("\<zero>") and unit ("\<one>")
    and R' and addition' (infixl "+''" 65) and multiplication' (infixl "\<cdot>''" 70) and zero' ("\<zero>''") and unit' ("\<one>''")

text \<open>p 106, l 17\<close>
locale ring_epimorphism = ring_homomorphism + surjective_map \<eta> R R'

text \<open>p 106, ll 14--18\<close>
sublocale quotient_ring \<subseteq> natural: ring_epimorphism
  where \<eta> = additive.Class and R' = "R // I" and addition' = "([+])" and multiplication' =  "([\<cdot>])"
    and zero' = "additive.Class \<zero>" and unit' = "additive.Class \<one>"
  ..

context ring_homomorphism begin

text \<open>
  Jacobson reasons via @{term "a - b \<in> additive.Ker"} being a congruence; we prefer the direct proof,
  since it is very simple.
\<close>
text \<open>p 106, ll 19--21\<close>
sublocale kernel: ideal where I = additive.Ker
  by unfold_locales (auto simp: additive.Ker_image multiplicative.commutes_with_composition)

end (* ring_homomorphism *)

text \<open>p 106, l 22\<close>
locale ring_monomorphism = ring_homomorphism + injective_map \<eta> R R'

context ring_homomorphism begin

text \<open>p 106, ll 21--23\<close>
theorem ring_monomorphism_iff_kernel_unit:
  "ring_monomorphism \<eta> R (+) (\<cdot>) \<zero> \<one> R' (+') (\<cdot>') \<zero>' \<one>' \<longleftrightarrow> additive.Ker = {\<zero>}" (is "?monom \<longleftrightarrow> ?ker")
proof
  assume ?monom then interpret ring_monomorphism . show ?ker by (simp add: additive.injective_iff_kernel_unit [symmetric])
next
  assume ?ker then show ?monom by unfold_locales (simp add: additive.injective_iff_kernel_unit)
qed
  
end (* ring_homomorphism *)

text \<open>p 106, ll 23--25\<close>
sublocale ring_homomorphism \<subseteq> image: subring "\<eta> ` R" R' "(+')" "(\<cdot>')" "\<zero>'" "\<one>'" ..

text \<open>p 106, ll 26--27\<close>
locale ideal_in_kernel =
  ring_homomorphism + contained: ideal I R "(+)" "(\<cdot>)" \<zero> \<one> for I +
  assumes subset: "I \<subseteq> additive.Ker"
begin

text \<open>p 106, ll 26--27\<close>
notation contained.additive.quotient_composition (infixl "[+]" 65)
notation contained.multiplicative.quotient_composition (infixl "[\<cdot>]" 70)

text \<open>Provides @{text additive.induced}, which Jacobson calls $\bar{\eta}$.\<close>
text \<open>p 106, l 30\<close>
sublocale additive: normal_subgroup_in_kernel \<eta> R "(+)" \<zero> R' "(+')" "\<zero>'" I
  rewrites "normal_subgroup.Congruence I R addition zero = contained.Ring_Congruence"
  by unfold_locales (rule subset contained.additive_congruence)+

text \<open>Only the multiplicative part needs some work.\<close>
text \<open>p 106, ll 27--30\<close>
sublocale induced: ring_homomorphism additive.induced "R // I" "([+])" "([\<cdot>])" "contained.additive.Class \<zero>" "contained.additive.Class \<one>"
  using contained.multiplicative.Class_commutes_with_composition
  by unfold_locales
    (auto elim!: contained.additive.Left_CosetE simp: contained.additive.Class_is_Left_Coset multiplicative.commutes_with_composition multiplicative.commutes_with_unit)

text \<open>p 106, l 30; p 107, ll 1--3\<close>
text \<open>
  @{term additive.induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term additive.induced} is unique: @{thm [display] additive.factorization} @{thm [display] additive.uniqueness}
\<close>

end (* ideal_in_kernel *)

text \<open>Fundamental Theorem of Homomorphisms of Rings\<close>

text \<open>p 107, l 6\<close>
locale ring_homomorphism_fundamental = ring_homomorphism begin

text \<open>p 107, l 6\<close>
notation kernel.additive.quotient_composition (infixl "[+]" 65)
notation kernel.multiplicative.quotient_composition (infixl "[\<cdot>]" 70)

text \<open>p 107, l 6\<close>
sublocale ideal_in_kernel where I = additive.Ker by unfold_locales rule

text \<open>p 107, ll 8--9\<close>
sublocale natural: ring_epimorphism
  where \<eta> = kernel.additive.Class and R' = "R // additive.Ker"
    and addition' = "kernel.additive.quotient_composition"
    and multiplication' = "kernel.multiplicative.quotient_composition"
    and zero' = "kernel.additive.Class \<zero>" and unit' = "kernel.additive.Class \<one>"
  ..

text \<open>p 107, l 9\<close>
sublocale induced: ring_monomorphism
  where \<eta> = additive.induced and R = "R // additive.Ker"
    and addition = "kernel.additive.quotient_composition"
    and multiplication = "kernel.multiplicative.quotient_composition"
    and zero = "kernel.additive.Class \<zero>" and unit = "kernel.additive.Class \<one>"
  by unfold_locales (simp add: additive.induced_inj_on)

end (* ring_homomorphism_fundamental *)

text \<open>p 107, l 11\<close>
locale ring_isomorphism = ring_homomorphism + bijective_map \<eta> R R' begin

text \<open>p 107, l 11\<close>
sublocale ring_monomorphism ..
sublocale ring_epimorphism ..

text \<open>p 107, l 11\<close>
lemma inverse_ring_isomorphism:
  "ring_isomorphism (restrict (inv_into R \<eta>) R') R' (+') (\<cdot>') \<zero>' \<one>' R (+) (\<cdot>) \<zero> \<one>"
  using additive.commutes_with_composition [symmetric] additive.commutes_with_unit
    multiplicative.commutes_with_composition [symmetric] multiplicative.commutes_with_unit surjective
  by unfold_locales auto

end (* ring_isomorphsim *)

text \<open>p 107, l 11\<close>
definition isomorphic_as_rings (infixl "\<cong>\<^sub>R" 50)
  where "\<R> \<cong>\<^sub>R \<R>' \<longleftrightarrow> (let (R, addition, multiplication, zero, unit) = \<R>; (R', addition', multiplication', zero', unit') = \<R>' in
  (\<exists>\<eta>. ring_isomorphism \<eta> R addition multiplication zero unit R' addition' multiplication' zero' unit'))"

text \<open>p 107, l 11\<close>
lemma isomorphic_as_rings_symmetric:
  "(R, addition, multiplication, zero, unit) \<cong>\<^sub>R (R', addition', multiplication', zero', unit') \<Longrightarrow>
   (R', addition', multiplication', zero', unit') \<cong>\<^sub>R (R, addition, multiplication, zero, unit)"
  by (simp add: isomorphic_as_rings_def) (meson ring_isomorphism.inverse_ring_isomorphism)

context ring_homomorphism begin

text \<open>Corollary\<close>
text \<open>p 107, ll 11--12\<close>
theorem image_is_isomorphic_to_quotient_ring:
  "\<exists>K add mult zero one. ideal K R (+) (\<cdot>) \<zero> \<one> \<and> (\<eta> ` R, (+'), (\<cdot>'), \<zero>', \<one>') \<cong>\<^sub>R (R // K, add, mult, zero, one)"
proof -
  interpret image: ring_homomorphism_fundamental where R' = "\<eta> ` R"
    by unfold_locales (auto simp: target.additive.commutative additive.commutes_with_composition
      multiplicative.commutes_with_composition target.distributive multiplicative.commutes_with_unit)
  have "ring_isomorphism image.additive.induced (R // additive.Ker) ([+]) ([\<cdot>]) (kernel.additive.Class \<zero>) (kernel.additive.Class \<one>) (\<eta> ` R) (+') (\<cdot>') \<zero>' \<one>'"
    by unfold_locales (simp add: image.additive.induced_image bij_betw_def)
  then have "(\<eta> ` R, (+'), (\<cdot>'), \<zero>', \<one>') \<cong>\<^sub>R (R // additive.Ker, ([+]), ([\<cdot>]), kernel.additive.Class \<zero>, kernel.additive.Class \<one>)"
    by (simp add: isomorphic_as_rings_def) (meson ring_isomorphism.inverse_ring_isomorphism)
  moreover have "ideal additive.Ker R (+) (\<cdot>) \<zero> \<one>" ..
  ultimately show ?thesis by blast
qed

end (* ring_homomorphism *)

end
