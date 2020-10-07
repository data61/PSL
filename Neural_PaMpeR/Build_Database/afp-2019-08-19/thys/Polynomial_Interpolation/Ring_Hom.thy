(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Several Locales for Homomorphisms Between Types.\<close>

theory Ring_Hom
imports 
  HOL.Complex
  Main
  "HOL-Library.Multiset"
  "HOL-Computational_Algebra.Factorial_Ring"
begin

hide_const (open) mult

text \<open>
Many standard operations can be interpreted as homomorphisms in some sense.
Since declaring some lemmas as [simp] will interfere with existing simplification rules,
we introduce named theorems that would be added to the simp set when necessary.

The following collects distribution lemmas for homomorphisms.
Its symmetric version can often be useful.\<close>
named_theorems hom_distribs

subsection \<open>Basic Homomorphism Locales\<close>

locale zero_hom =
  fixes hom :: "'a :: zero \<Rightarrow> 'b :: zero"
  assumes hom_zero[simp]: "hom 0 = 0"

locale one_hom =
  fixes hom :: "'a :: one \<Rightarrow> 'b :: one"
  assumes hom_one[simp]: "hom 1 = 1"

locale times_hom =
  fixes hom :: "'a :: times \<Rightarrow> 'b :: times"
  assumes hom_mult[hom_distribs]: "hom (x * y) = hom x * hom y"

locale plus_hom =
  fixes hom :: "'a :: plus \<Rightarrow> 'b :: plus"
  assumes hom_add[hom_distribs]: "hom (x + y) = hom x + hom y"

locale semigroup_mult_hom =
  times_hom hom for hom :: "'a :: semigroup_mult \<Rightarrow> 'b :: semigroup_mult"

locale semigroup_add_hom =
  plus_hom hom for hom :: "'a :: semigroup_add \<Rightarrow> 'b :: semigroup_add"

locale monoid_mult_hom = one_hom hom + semigroup_mult_hom hom
  for hom :: "'a :: monoid_mult \<Rightarrow> 'b :: monoid_mult"
begin
  text \<open>Homomorphism distributes over product:\<close>
  lemma hom_prod_list: "hom (prod_list xs) = prod_list (map hom xs)"
    by (induct xs, auto simp: hom_distribs)
  text \<open>but since it introduces unapplied @{term hom}, the reverse direction would be simp.\<close>
  lemmas prod_list_map_hom[simp] = hom_prod_list[symmetric]
  lemma hom_power[hom_distribs]: "hom (x ^ n) = hom x ^ n"
    by (induct n, auto simp: hom_distribs)
end

locale monoid_add_hom = zero_hom hom + semigroup_add_hom hom
  for hom :: "'a :: monoid_add \<Rightarrow> 'b :: monoid_add"
begin
  lemma hom_sum_list: "hom (sum_list xs) = sum_list (map hom xs)"
    by (induct xs, auto simp: hom_distribs)
  lemmas sum_list_map_hom[simp] = hom_sum_list[symmetric]
  lemma hom_add_eq_zero: assumes "x + y = 0" shows "hom x + hom y = 0"
  proof -
    have "0 = x + y" using assms..
    hence "hom 0 = hom (x + y)" by simp
    thus ?thesis by (auto simp: hom_distribs)
  qed
end

locale group_add_hom = monoid_add_hom hom
  for hom :: "'a :: group_add \<Rightarrow> 'b :: group_add"
begin
  lemma hom_uminus[hom_distribs]: "hom (-x) = - hom x"
    by (simp add: eq_neg_iff_add_eq_0 hom_add_eq_zero)
  lemma hom_minus [hom_distribs]: "hom (x - y) = hom x - hom y"
    unfolding diff_conv_add_uminus hom_distribs..
end

subsection \<open>Commutativity\<close>

locale ab_semigroup_mult_hom = semigroup_mult_hom hom
  for hom :: "'a :: ab_semigroup_mult \<Rightarrow> 'b :: ab_semigroup_mult"

locale ab_semigroup_add_hom = semigroup_add_hom hom
  for hom :: "'a :: ab_semigroup_add \<Rightarrow> 'b :: ab_semigroup_add"

locale comm_monoid_mult_hom = monoid_mult_hom hom
  for hom :: "'a :: comm_monoid_mult \<Rightarrow> 'b :: comm_monoid_mult"
begin
  sublocale ab_semigroup_mult_hom..
  lemma hom_prod[hom_distribs]: "hom (prod f X) = (\<Prod>x \<in> X. hom (f x))"
    by (cases "finite X", induct rule:finite_induct; simp add: hom_distribs)
  lemma hom_prod_mset: "hom (prod_mset X) = prod_mset (image_mset hom X)"
    by (induct X, auto simp: hom_distribs)
  lemmas prod_mset_image[simp] = hom_prod_mset[symmetric]
  lemma hom_dvd[intro,simp]: assumes "p dvd q" shows "hom p dvd hom q"
  proof -
    from assms obtain r where "q = p * r" unfolding dvd_def by auto
    from arg_cong[OF this, of hom] show ?thesis unfolding dvd_def by (auto simp: hom_distribs)
  qed
  lemma hom_dvd_1[simp]: "x dvd 1 \<Longrightarrow> hom x dvd 1" using hom_dvd[of x 1] by simp
end

locale comm_monoid_add_hom = monoid_add_hom hom
  for hom :: "'a :: comm_monoid_add \<Rightarrow> 'b :: comm_monoid_add"
begin
  sublocale ab_semigroup_add_hom..
  lemma hom_sum[hom_distribs]: "hom (sum f X) = (\<Sum>x \<in> X. hom (f x))"
    by (cases "finite X", induct rule:finite_induct; simp add: hom_distribs)
  lemma hom_sum_mset[hom_distribs,simp]: "hom (sum_mset X) = sum_mset (image_mset hom X)"
    by (induct X, auto simp: hom_distribs)
end

locale ab_group_add_hom = group_add_hom hom
  for hom :: "'a :: ab_group_add \<Rightarrow> 'b :: ab_group_add"
begin
  sublocale comm_monoid_add_hom..
end

locale semiring_hom = comm_monoid_add_hom hom + monoid_mult_hom hom
  for hom :: "'a :: semiring_1 \<Rightarrow> 'b :: semiring_1"
begin
  lemma hom_mult_eq_zero: assumes "x * y = 0" shows "hom x * hom y = 0"
  proof -
    have "0 = x * y" using assms..
    hence "hom 0 = hom (x * y)" by simp
    thus ?thesis by (auto simp:hom_distribs)
  qed
end

locale ring_hom = semiring_hom hom
  for hom :: "'a :: ring_1 \<Rightarrow> 'b :: ring_1"
begin
  sublocale ab_group_add_hom hom..
end

locale comm_semiring_hom = semiring_hom hom
  for hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
begin
  sublocale comm_monoid_mult_hom..
end

locale comm_ring_hom = ring_hom hom
  for hom :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin
  sublocale comm_semiring_hom..
end

locale idom_hom = comm_ring_hom hom
  for hom :: "'a :: idom \<Rightarrow> 'b :: idom"

subsection \<open>Division\<close>

locale idom_divide_hom = idom_hom hom
  for hom :: "'a :: idom_divide \<Rightarrow> 'b :: idom_divide" +
  assumes hom_div[hom_distribs]: "hom (x div y) = hom x div hom y"
begin

end

locale field_hom = idom_hom hom
  for hom :: "'a :: field \<Rightarrow> 'b :: field"
begin

  lemma hom_inverse[hom_distribs]: "hom (inverse x) = inverse (hom x)"
    by (metis hom_mult hom_one hom_zero inverse_unique inverse_zero right_inverse)

  sublocale idom_divide_hom hom
  proof
    fix x y
    have "hom (x / y) = hom (x * inverse y)" by (simp add: field_simps)
    thus "hom (x / y) = hom x / hom y" unfolding hom_distribs by (simp add: field_simps)
  qed

end

locale field_char_0_hom = field_hom hom
  for hom :: "'a :: field_char_0 \<Rightarrow> 'b :: field_char_0"


subsection \<open>(Partial) Injectivitiy\<close>

locale zero_hom_0 = zero_hom +
  assumes hom_0: "\<And>x. hom x = 0 \<Longrightarrow> x = 0"
begin
  lemma hom_0_iff[iff]: "hom x = 0 \<longleftrightarrow> x = 0" using hom_0 by auto
end

locale one_hom_1 = one_hom +
  assumes hom_1: "\<And>x. hom x = 1 \<Longrightarrow> x = 1"
begin
  lemma hom_1_iff[iff]: "hom x = 1 \<longleftrightarrow> x = 1" using hom_1 by auto
end

text \<open>Next locales are at this point not interesting.
  They will retain some results when we think of polynomials.
\<close>
locale monoid_mult_hom_1 = monoid_mult_hom + one_hom_1

locale monoid_add_hom_0 = monoid_add_hom + zero_hom_0

locale comm_monoid_mult_hom_1 = monoid_mult_hom_1 hom
  for hom :: "'a :: comm_monoid_mult \<Rightarrow> 'b :: comm_monoid_mult"

locale comm_monoid_add_hom_0 = monoid_add_hom_0 hom
  for hom :: "'a :: comm_monoid_add \<Rightarrow> 'b :: comm_monoid_add"


locale injective =
  fixes f :: "'a \<Rightarrow> 'b" assumes injectivity: "\<And>x y. f x = f y \<Longrightarrow> x = y"
begin
  lemma eq_iff[simp]: "f x = f y \<longleftrightarrow> x = y" using injectivity by auto
  lemma inj_f: "inj f" by (auto intro: injI)
  lemma inv_f_f[simp]: "inv f (f x) = x" by (fact inv_f_f[OF inj_f])
end

locale inj_zero_hom = zero_hom + injective hom
begin
  sublocale zero_hom_0 by (unfold_locales, auto intro: injectivity)
end

locale inj_one_hom = one_hom + injective hom
begin
  sublocale one_hom_1 by (unfold_locales, auto intro: injectivity)
end

locale inj_semigroup_mult_hom = semigroup_mult_hom + injective hom

locale inj_semigroup_add_hom = semigroup_add_hom + injective hom

locale inj_monoid_mult_hom = monoid_mult_hom + inj_semigroup_mult_hom
begin
  sublocale inj_one_hom..
  sublocale monoid_mult_hom_1..
end

locale inj_monoid_add_hom = monoid_add_hom + inj_semigroup_add_hom
begin
  sublocale inj_zero_hom..
  sublocale monoid_add_hom_0..
end

locale inj_comm_monoid_mult_hom = comm_monoid_mult_hom + inj_monoid_mult_hom
begin
  sublocale comm_monoid_mult_hom_1..
end

locale inj_comm_monoid_add_hom = comm_monoid_add_hom + inj_monoid_add_hom
begin
  sublocale comm_monoid_add_hom_0..
end

locale inj_semiring_hom = semiring_hom + injective hom
begin
  sublocale inj_comm_monoid_add_hom + inj_monoid_mult_hom..
end

locale inj_comm_semiring_hom = comm_semiring_hom + inj_semiring_hom
begin
  sublocale inj_comm_monoid_mult_hom..
end

text \<open>For groups, injectivity is easily ensured.\<close>
locale inj_group_add_hom = group_add_hom + zero_hom_0
begin
  sublocale injective hom
  proof
    fix x y assume "hom x = hom y"
    then have "hom (x-y) = 0" by (auto simp: hom_distribs)
    then show "x = y" by simp
  qed
  sublocale inj_monoid_add_hom..
end

locale inj_ab_group_add_hom = ab_group_add_hom + inj_group_add_hom
begin
  sublocale inj_comm_monoid_add_hom..
end

locale inj_ring_hom = ring_hom + zero_hom_0
begin
  sublocale inj_ab_group_add_hom..
  sublocale inj_semiring_hom..
end

locale inj_comm_ring_hom = comm_ring_hom + zero_hom_0
begin
  sublocale inj_ring_hom..
  sublocale inj_comm_semiring_hom..
end

locale inj_idom_hom = idom_hom + zero_hom_0
begin
  sublocale inj_comm_ring_hom..
end

text \<open>Field homomorphism is always injective.\<close>
context field_hom begin
  sublocale zero_hom_0
  proof (unfold_locales, rule ccontr)
    fix x
    assume "hom x = 0" and x0: "x \<noteq> 0"
    then have "inverse (hom x) = 0" by simp
    then have "hom (inverse x) = 0" by (simp add: hom_distribs)
    then have "hom (inverse x * x) = 0" by (simp add: hom_distribs)
    with x0 have "hom 1 = hom 0" by simp
    then have "(1 :: 'b) = 0" by simp
    then show False by auto
  qed
  sublocale inj_idom_hom..
end

subsection \<open>Surjectivity and Isomorphisms\<close>

locale surjective =
  fixes f :: "'a \<Rightarrow> 'b"
  assumes surj: "surj f"
begin
  lemma f_inv_f[simp]: "f (inv f x) = x"
     by (rule cong, auto simp: surj[unfolded surj_iff o_def id_def])
end

locale bijective = injective + surjective

lemma bijective_eq_bij: "bijective f = bij f"
proof(intro iffI)
  assume "bijective f"
  then interpret bijective f.
  show "bij f" using injectivity surj by (auto intro!: bijI injI)
next
  assume "bij f"
  from this[unfolded bij_def]
  show "bijective f" by (unfold_locales, auto dest: injD)
qed

context bijective
begin
  lemmas bij = bijective_axioms[unfolded bijective_eq_bij]
  interpretation inv: bijective "inv f"
    using bijective_axioms bij_imp_bij_inv by (unfold bijective_eq_bij)
  sublocale inv: surjective "inv f"..
  sublocale inv: injective "inv f"..
  lemma inv_inv_f_eq[simp]: "inv (inv f) = f" using inv_inv_eq[OF bij].
  lemma f_eq_iff[simp]: "f x = y \<longleftrightarrow> x = inv f y" by auto
  lemma inv_f_eq_iff[simp]: "inv f x = y \<longleftrightarrow> x = f y" by auto
end

locale monoid_mult_isom = inj_monoid_mult_hom + bijective hom
begin
  sublocale inv: bijective "inv hom"..
  sublocale inv: inj_monoid_mult_hom "inv hom"
  proof (unfold_locales)
    fix hx hy :: 'b
    from bij obtain x y where hx: "hx = hom x" and hy: "hy = hom y" by (meson bij_pointE)
    show "inv hom (hx*hy) = inv hom hx * inv hom hy" by (unfold hx hy, fold hom_mult, simp)
    have "inv hom (hom 1) = 1" by (unfold inv_f_f, simp)
    then show "inv hom 1 = 1" by simp
  qed
end

locale monoid_add_isom = inj_monoid_add_hom + bijective hom
begin
  sublocale inv: bijective "inv hom"..
  sublocale inv: inj_monoid_add_hom "inv hom"
  proof (unfold_locales)
    fix hx hy :: 'b
    from bij obtain x y where hx: "hx = hom x" and hy: "hy = hom y" by (meson bij_pointE)
    show "inv hom (hx+hy) = inv hom hx + inv hom hy" by (unfold hx hy, fold hom_add, simp)
    have "inv hom (hom 0) = 0" by (unfold inv_f_f, simp)
    then show "inv hom 0 = 0" by simp
  qed
end

locale comm_monoid_mult_isom = monoid_mult_isom hom
  for hom :: "'a :: comm_monoid_mult \<Rightarrow> 'b :: comm_monoid_mult"
begin
  sublocale inv: monoid_mult_isom "inv hom"..
  sublocale inj_comm_monoid_mult_hom..

  lemma hom_dvd_hom[simp]: "hom x dvd hom y \<longleftrightarrow> x dvd y"
  proof
    assume "hom x dvd hom y"
    then obtain hz where "hom y = hom x * hz" by (elim dvdE)
    moreover obtain z where "hz = hom z" using bij by (elim bij_pointE)
    ultimately have "hom y = hom (x * z)" by (auto simp: hom_distribs)
    from this[unfolded eq_iff] have "y = x * z".
    then show "x dvd y" by (intro dvdI)
  qed (rule hom_dvd)

  lemma hom_dvd_simp[simp]:
    shows "hom x dvd y' \<longleftrightarrow> x dvd inv hom y'"
    using hom_dvd_hom[of x "inv hom y'"] by simp

end

locale comm_monoid_add_isom = monoid_add_isom hom
  for hom :: "'a :: comm_monoid_add \<Rightarrow> 'b :: comm_monoid_add"
begin
  sublocale inv: monoid_add_isom "inv hom" by (unfold_locales; simp add: hom_distribs)
  sublocale inj_comm_monoid_add_hom..
end

locale semiring_isom = inj_semiring_hom hom + bijective hom for hom
begin
  sublocale inv: inj_semiring_hom "inv hom" by (unfold_locales; simp add: hom_distribs)
  sublocale inv: bijective "inv hom"..
  sublocale monoid_mult_isom..
  sublocale comm_monoid_add_isom..
end

locale comm_semiring_isom = semiring_isom hom
  for hom :: "'a :: comm_semiring_1 \<Rightarrow> 'b :: comm_semiring_1"
begin
  sublocale inv: semiring_isom "inv hom" by (unfold_locales; simp add: hom_distribs)
  sublocale comm_monoid_mult_isom..
  sublocale inj_comm_semiring_hom..
end

locale ring_isom = inj_ring_hom + surjective hom
begin
  sublocale semiring_isom..
  sublocale inv: inj_ring_hom "inv hom" by (unfold_locales; simp add: hom_distribs)
end

locale comm_ring_isom = ring_isom hom
  for hom :: "'a :: comm_ring_1 \<Rightarrow> 'b :: comm_ring_1"
begin
  sublocale comm_semiring_isom..
  sublocale inj_comm_ring_hom..
  sublocale inv: ring_isom "inv hom" by (unfold_locales; simp add: hom_distribs)
end

locale idom_isom = comm_ring_isom + inj_idom_hom
begin
  sublocale inv: comm_ring_isom "inv hom" by (unfold_locales; simp add: hom_distribs)
  sublocale inv: inj_idom_hom "inv hom"..
end

locale field_isom = field_hom + surjective hom
begin
  sublocale idom_isom..
  sublocale inv: field_hom "inv hom" by (unfold_locales; simp add: hom_distribs)
end

locale inj_idom_divide_hom = idom_divide_hom hom + inj_idom_hom hom
  for hom :: "'a :: idom_divide \<Rightarrow> 'b :: idom_divide" 
begin
lemma hom_dvd_iff[simp]: "(hom p dvd hom q) = (p dvd q)"
proof (cases "p = 0")
  case False
  show ?thesis
  proof
    assume "hom p dvd hom q" from this[unfolded dvd_def] obtain k where 
      id: "hom q = hom p * k" by auto
    hence "(hom q div hom p) = (hom p * k) div hom p" by simp
    also have "\<dots> = k" by (rule nonzero_mult_div_cancel_left, insert False, simp)
    also have "hom q div hom p = hom (q div p)" by (simp add: hom_div)
    finally have "k = hom (q div p)" by auto
    from id[unfolded this] have "hom q = hom (p * (q div p))" by (simp add: hom_mult)
    hence "q = p * (q div p)" by simp
    thus "p dvd q" unfolding dvd_def ..
  qed simp
qed simp
end

context field_hom
begin
sublocale inj_idom_divide_hom ..
end


subsection \<open>Example Interpretations\<close>

interpretation of_int_hom: ring_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: comm_ring_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: idom_hom of_int by (unfold_locales, auto)
interpretation of_int_hom: inj_ring_hom "of_int :: int \<Rightarrow> 'a :: {ring_1,ring_char_0}"
  by (unfold_locales, auto)
interpretation of_int_hom: inj_comm_ring_hom "of_int :: int \<Rightarrow> 'a :: {comm_ring_1,ring_char_0}"
  by (unfold_locales, auto)
interpretation of_int_hom: inj_idom_hom "of_int :: int \<Rightarrow> 'a :: {idom,ring_char_0}"
  by (unfold_locales, auto)

text \<open>Somehow @{const of_rat} is defined only on \<open>char_0\<close>.\<close>
interpretation of_rat_hom: field_char_0_hom "of_rat"
  by (unfold_locales, auto simp: of_rat_add of_rat_mult of_rat_inverse of_rat_minus)

interpretation of_real_hom: inj_ring_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: inj_comm_ring_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: inj_idom_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: field_hom of_real by (unfold_locales, auto)
interpretation of_real_hom: field_char_0_hom "of_real" by (unfold_locales, auto)


text \<open>Constant multiplication in a semiring is only a monoid homomorphism.\<close>

interpretation mult_hom: comm_monoid_add_hom "\<lambda>x. c * x" for c :: "'a :: semiring_1"
  by (unfold_locales, auto simp: field_simps)

end
