(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
section \<open>Polynomials in Rings and Fields\<close>

subsection \<open>Polynomials in Rings\<close>

text \<open>We use a locale to work with polynomials in some integer-modulo ring.\<close>

theory Poly_Mod
  imports
  "HOL-Computational_Algebra.Primes"
  Polynomial_Factorization.Square_Free_Factorization
  Unique_Factorization_Poly
  "HOL-Word.Misc_Arithmetic" 
begin

locale poly_mod = fixes m :: "int" 
begin

definition M :: "int \<Rightarrow> int" where "M x = x mod m" 

lemma M_0[simp]: "M 0 = 0"
  by (auto simp add: M_def)

lemma M_M[simp]: "M (M x) = M x"
  by (auto simp add: M_def)

lemma M_plus[simp]: "M (M x + y) = M (x + y)" "M (x + M y) = M (x + y)"
  by (auto simp add: M_def mod_simps)
  
lemma M_minus[simp]: "M (M x - y) = M (x - y)" "M (x - M y) = M (x - y)" 
  by (auto simp add: M_def mod_simps)

lemma M_times[simp]: "M (M x * y) = M (x * y)" "M (x * M y) = M (x * y)"
  by (auto simp add: M_def mod_simps)

lemma M_sum: "M (sum (\<lambda> x. M (f x)) A) = M (sum f A)"
proof (induct A rule: infinite_finite_induct) 
  case (insert x A)
  from insert(1-2) have "M (\<Sum>x\<in>insert x A. M (f x)) = M (f x + M ((\<Sum>x\<in>A. M (f x))))" by simp
  also have "M ((\<Sum>x\<in>A. M (f x))) = M ((\<Sum>x\<in>A. f x))" using insert by simp
  finally show ?case using insert by simp
qed auto


definition Mp :: "int poly \<Rightarrow> int poly" where "Mp = map_poly M"

lemma Mp_0[simp]: "Mp 0 = 0" unfolding Mp_def by auto

lemma Mp_coeff: "coeff (Mp f) i = M (coeff f i)" unfolding Mp_def 
  by (simp add: M_def coeff_map_poly) 

abbreviation eq_m :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infixl "=m" 50) where
  "f =m g \<equiv> (Mp f = Mp g)"

notation eq_m (infixl "=m" 50)

abbreviation degree_m :: "int poly \<Rightarrow> nat" where 
  "degree_m f \<equiv> degree (Mp f)" 

lemma mult_Mp[simp]: "Mp (Mp f * g) = Mp (f * g)" "Mp (f * Mp g) = Mp (f * g)" 
proof -
  {
    fix f g
    have "Mp (Mp f * g) = Mp (f * g)" 
    unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff
    proof 
      fix n
      show "M (\<Sum>i\<le>n. M (coeff f i) * coeff g (n - i)) = M (\<Sum>i\<le>n. coeff f i * coeff g (n - i))"
        by (subst M_sum[symmetric], rule sym, subst M_sum[symmetric], unfold M_times, simp)
    qed
  }
  from this[of f g] this[of g f] show "Mp (Mp f * g) = Mp (f * g)" "Mp (f * Mp g) = Mp (f * g)"
    by (auto simp: ac_simps)
qed

lemma plus_Mp[simp]: "Mp (Mp f + g) = Mp (f + g)" "Mp (f + Mp g) = Mp (f + g)" 
  unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff by (auto simp add: Mp_coeff)

lemma minus_Mp[simp]: "Mp (Mp f - g) = Mp (f - g)" "Mp (f - Mp g) = Mp (f - g)" 
  unfolding poly_eq_iff Mp_coeff unfolding coeff_mult Mp_coeff by (auto simp add: Mp_coeff)    

lemma Mp_smult[simp]: "Mp (smult (M a) f) = Mp (smult a f)" "Mp (smult a (Mp f)) = Mp (smult a f)" 
  unfolding Mp_def smult_as_map_poly
  by (rule poly_eqI, auto simp: coeff_map_poly)+

lemma Mp_Mp[simp]: "Mp (Mp f) = Mp f" unfolding Mp_def
  by (intro poly_eqI, auto simp: coeff_map_poly)

lemma Mp_smult_m_0[simp]: "Mp (smult m f) = 0" 
  by (intro poly_eqI, auto simp: Mp_coeff, auto simp: M_def)

definition dvdm :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" (infix "dvdm" 50) where
  "f dvdm g = (\<exists> h. g =m f * h)"
notation dvdm (infix "dvdm" 50)


lemma dvdmE:
  assumes fg: "f dvdm g"
    and main: "\<And>h. g =m f * h \<Longrightarrow> Mp h = h \<Longrightarrow> thesis"
  shows "thesis"
proof-
  from fg obtain h where "g =m f * h" by (auto simp: dvdm_def)
  then have "g =m f * Mp h" by auto
  from main[OF this] show thesis by auto
qed

lemma Mp_dvdm[simp]: "Mp f dvdm g \<longleftrightarrow> f dvdm g"
  and dvdm_Mp[simp]: "f dvdm Mp g \<longleftrightarrow> f dvdm g" by (auto simp: dvdm_def)

definition irreducible_m
  where "irreducible_m f = (\<not>f =m 0 \<and> \<not> f dvdm 1 \<and> (\<forall>a b. f =m a * b \<longrightarrow> a dvdm 1 \<or> b dvdm 1))"

definition irreducible\<^sub>d_m :: "int poly \<Rightarrow> bool" where "irreducible\<^sub>d_m f \<equiv>
   degree_m f > 0 \<and>
   (\<forall> g h. degree_m g < degree_m f \<longrightarrow> degree_m h < degree_m f \<longrightarrow> \<not> f =m g * h)"

definition prime_elem_m
  where "prime_elem_m f \<equiv> \<not> f =m 0 \<and> \<not> f dvdm 1 \<and> (\<forall>g h. f dvdm g * h \<longrightarrow> f dvdm g \<or> f dvdm h)"

lemma degree_m_le_degree [intro!]: "degree_m f \<le> degree f"
  by (simp add: Mp_def degree_map_poly_le)

lemma irreducible\<^sub>d_mI:
  assumes f0: "degree_m f > 0"
      and main: "\<And>g h. Mp g = g \<Longrightarrow> Mp h = h \<Longrightarrow> degree g > 0 \<Longrightarrow> degree g < degree_m f \<Longrightarrow> degree h > 0 \<Longrightarrow> degree h < degree_m f \<Longrightarrow> f =m g * h \<Longrightarrow> False"
    shows "irreducible\<^sub>d_m f"
proof (unfold irreducible\<^sub>d_m_def, intro conjI allI impI f0 notI)
  fix g h
  assume deg: "degree_m g < degree_m f" "degree_m h < degree_m f" and "f =m g * h"
  then have f: "f =m Mp g * Mp h" by simp
  have "degree_m f \<le> degree_m g + degree_m h"
    unfolding f using degree_mult_le order.trans by blast
  with main[of "Mp g" "Mp h"] deg f show False by auto
qed

lemma irreducible\<^sub>d_mE:
  assumes "irreducible\<^sub>d_m f"
    and "degree_m f > 0 \<Longrightarrow> (\<And>g h. degree_m g < degree_m f \<Longrightarrow> degree_m h < degree_m f \<Longrightarrow> \<not> f =m g * h) \<Longrightarrow> thesis"
  shows thesis
  using assms by (unfold irreducible\<^sub>d_m_def, auto)

lemma irreducible\<^sub>d_mD:
  assumes "irreducible\<^sub>d_m f"
  shows "degree_m f > 0" and "\<And>g h. degree_m g < degree_m f \<Longrightarrow> degree_m h < degree_m f \<Longrightarrow> \<not> f =m g * h"
  using assms by (auto elim: irreducible\<^sub>d_mE)

definition square_free_m :: "int poly \<Rightarrow> bool" where 
  "square_free_m f = (\<not> f =m 0 \<and> (\<forall> g. degree_m g \<noteq> 0 \<longrightarrow> \<not> (g * g dvdm f)))"

definition coprime_m :: "int poly \<Rightarrow> int poly \<Rightarrow> bool" where 
  "coprime_m f g = (\<forall> h. h dvdm f \<longrightarrow> h dvdm g \<longrightarrow> h dvdm 1)"

lemma Mp_square_free_m[simp]: "square_free_m (Mp f) = square_free_m f" 
  unfolding square_free_m_def dvdm_def by simp

lemma square_free_m_cong: "square_free_m f \<Longrightarrow> Mp f = Mp g \<Longrightarrow> square_free_m g" 
  unfolding square_free_m_def dvdm_def by simp

lemma Mp_prod_mset[simp]: "Mp (prod_mset (image_mset Mp b)) = Mp (prod_mset b)" 
proof (induct b)
  case (add x b)
  have "Mp (prod_mset (image_mset Mp ({#x#}+b))) = Mp (Mp x * prod_mset (image_mset Mp b))" by simp
  also have "\<dots> = Mp (Mp x * Mp (prod_mset (image_mset Mp b)))" by simp
  also have "\<dots> = Mp ( Mp x * Mp (prod_mset b))" unfolding add by simp
  finally show ?case by simp
qed simp

lemma Mp_prod_list: "Mp (prod_list (map Mp b)) = Mp (prod_list b)" 
proof (induct b)
  case (Cons b xs)
  have "Mp (prod_list (map Mp (b # xs))) = Mp (Mp b * prod_list (map Mp xs))" by simp
  also have "\<dots> = Mp (Mp b * Mp (prod_list (map Mp xs)))" by simp
  also have "\<dots> = Mp (Mp b * Mp (prod_list xs))" unfolding Cons by simp
  finally show ?case by simp
qed simp

text \<open>Polynomial evaluation modulo\<close>
definition "M_poly p x \<equiv> M (poly p x)"

lemma M_poly_Mp[simp]: "M_poly (Mp p) = M_poly p"
proof(intro ext, induct p)
  case 0 show ?case by auto
next
  case IH: (pCons a p)
  from IH(1) have "M_poly (Mp (pCons a p)) x = M (a + M(x * M_poly (Mp p) x))"
    by (simp add: M_poly_def Mp_def)
  also note IH(2)[of x]
  finally show ?case by (simp add: M_poly_def)
qed

lemma Mp_lift_modulus: assumes "f =m g" 
  shows "poly_mod.eq_m (m * k) (smult k f) (smult k g)" 
  using assms unfolding poly_eq_iff poly_mod.Mp_coeff coeff_smult
  unfolding poly_mod.M_def by simp

lemma Mp_ident_product: "n > 0 \<Longrightarrow> Mp f = f \<Longrightarrow> poly_mod.Mp (m * n) f = f"
  unfolding poly_eq_iff poly_mod.Mp_coeff poly_mod.M_def 
  by (auto simp add: zmod_zmult2_eq) (metis mod_div_trivial mod_0)

lemma Mp_shrink_modulus: assumes "poly_mod.eq_m (m * k) f g" "k \<noteq> 0" 
  shows "f =m g" 
proof -
  from assms have a: "\<And> n. coeff f n mod (m * k) = coeff g n mod (m * k)"
    unfolding poly_eq_iff poly_mod.Mp_coeff unfolding poly_mod.M_def by auto
  show ?thesis unfolding poly_eq_iff poly_mod.Mp_coeff unfolding poly_mod.M_def
  proof
    fix n
    show "coeff f n mod m = coeff g n mod m" using a[of n] \<open>k \<noteq> 0\<close> 
      by (metis mod_mult_right_eq mult.commute mult_cancel_left mult_mod_right)
  qed
qed  
  

lemma degree_m_le: "degree_m f \<le> degree f" unfolding Mp_def by (rule degree_map_poly_le)

lemma degree_m_eq: "coeff f (degree f) mod m \<noteq> 0 \<Longrightarrow> m > 1 \<Longrightarrow> degree_m f = degree f" 
  using degree_m_le[of f] unfolding Mp_def
  by (auto intro: degree_map_poly simp: Mp_def poly_mod.M_def)

lemma degree_m_mult_le:  
  assumes eq: "f =m g * h" 
  shows "degree_m f \<le> degree_m g + degree_m h" 
proof -
  have "degree_m f = degree_m (Mp g * Mp h)" using eq by simp
  also have "\<dots> \<le> degree (Mp g * Mp h)" by (rule degree_m_le)
  also have "\<dots> \<le> degree_m g + degree_m h" by (rule degree_mult_le)
  finally show ?thesis by auto
qed

lemma degree_m_smult_le: "degree_m (smult c f) \<le> degree_m f"
  by (metis Mp_0 coeff_0 degree_le degree_m_le degree_smult_eq poly_mod.Mp_smult(2) smult_eq_0_iff)

lemma irreducible_m_Mp[simp]: "irreducible_m (Mp f) \<longleftrightarrow> irreducible_m f" by (simp add: irreducible_m_def)

lemma eq_m_irreducible_m: "f =m g \<Longrightarrow> irreducible_m f \<longleftrightarrow> irreducible_m g"
  using irreducible_m_Mp by metis

definition mset_factors_m where "mset_factors_m F p \<equiv>
  F \<noteq> {#} \<and> (\<forall>f. f \<in># F \<longrightarrow> irreducible_m f) \<and> p =m prod_mset F"

end

declare poly_mod.M_def[code]
declare poly_mod.Mp_def[code]

definition Irr_Mon :: "'a :: comm_semiring_1 poly set"
  where "Irr_Mon = {x. irreducible x \<and> monic x}" 

definition factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "factorization Factors f cfs \<equiv> (case cfs of (c,fs) \<Rightarrow> f = (smult c (prod_mset fs)) \<and> (set_mset fs \<subseteq> Factors))" 

definition unique_factorization :: "'a :: comm_semiring_1 poly set \<Rightarrow> 'a poly \<Rightarrow> ('a \<times> 'a poly multiset) \<Rightarrow> bool" where
  "unique_factorization Factors f cfs = (Collect (factorization Factors f) = {cfs})" 

lemma irreducible_multD:
  assumes l: "irreducible (a*b)"
  shows "a dvd 1 \<and> irreducible b \<or> b dvd 1 \<and> irreducible a"
proof-
  from l have "a dvd 1 \<or> b dvd 1" by auto
  then show ?thesis
  proof(elim disjE)
    assume a: "a dvd 1"
    with l have "irreducible b"
      unfolding irreducible_def
      by (meson is_unit_mult_iff mult.left_commute mult_not_zero)
    with a show ?thesis by auto
  next
    assume a: "b dvd 1"
    with l have "irreducible a"
      unfolding irreducible_def
      by (meson is_unit_mult_iff mult_not_zero semiring_normalization_rules(16))
    with a show ?thesis by auto
  qed
qed

lemma irreducible_dvd_prod_mset:
  fixes p :: "'a :: field poly"
  assumes irr: "irreducible p" and dvd: "p dvd prod_mset as"
  shows "\<exists> a \<in># as. p dvd a"
proof -
  from irr[unfolded irreducible_def] have deg: "degree p \<noteq> 0" by auto
  hence p1: "\<not> p dvd 1" unfolding dvd_def
    by (metis degree_1 nonzero_mult_div_cancel_left div_poly_less linorder_neqE_nat mult_not_zero not_less0 zero_neq_one)
  from dvd show ?thesis
  proof (induct as)
    case (add a as)
    hence "prod_mset (add_mset a as) = a * prod_mset as" by auto
    from add(2)[unfolded this] add(1) irr
    show ?case by auto
  qed (insert p1, auto)
qed

lemma monic_factorization_unique_mset:
  fixes P::"'a::field poly multiset"
  assumes eq: "prod_mset P = prod_mset Q" 
    and P: "set_mset P \<subseteq> {q. irreducible q \<and> monic q}"
    and Q: "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}"
  shows "P = Q" 
proof -
  {
    fix P Q :: "'a poly multiset"
    assume id: "prod_mset P = prod_mset Q" 
    and P: "set_mset P \<subseteq> {q. irreducible q \<and> monic q}"
    and Q: "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}"
    hence "P \<subseteq># Q"
    proof (induct P arbitrary: Q)
      case (add x P Q')
      from add(3) have irr: "irreducible x" and mon: "monic x" by auto
      have "\<exists> a \<in># Q'. x dvd a"
      proof (rule irreducible_dvd_prod_mset[OF irr])
        show "x dvd prod_mset Q'" unfolding add(2)[symmetric] by simp
      qed
      then obtain y Q where Q': "Q' = add_mset y Q" and xy: "x dvd y" by (meson mset_add)
      from add(4) Q' have irr': "irreducible y" and mon': "monic y" by auto
      have "x = y"  using irr irr' xy mon mon'
        by (metis irreducibleD' irreducible_not_unit poly_dvd_antisym)
      hence Q': "Q' = Q + {#x#}" using Q' by auto
      from mon have x0: "x \<noteq> 0" by auto
      from arg_cong[OF add(2)[unfolded Q'], of "\<lambda> z. z div x"] 
      have eq: "prod_mset P = prod_mset Q" using x0 by auto
      from add(3-4)[unfolded Q'] 
      have "set_mset P \<subseteq> {q. irreducible q \<and> monic q}" "set_mset Q \<subseteq> {q. irreducible q \<and> monic q}" 
        by auto
      from add(1)[OF eq this] show ?case unfolding Q' by auto
    qed auto
  }
  from this[OF eq P Q] this[OF eq[symmetric] Q P]
  show ?thesis by auto
qed


lemma exactly_one_monic_factorization:
  assumes mon: "monic (f :: 'a :: field poly)"
  shows "\<exists>! fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible q \<and> monic q}"
proof -
  from monic_irreducible_factorization[OF mon]
  obtain gs g where fin: "finite gs" and f: "f = (\<Prod>a\<in>gs. a ^ Suc (g a))" 
    and gs: "gs \<subseteq> {q. irreducible q \<and> monic q}" 
    by blast
  from fin 
  have "\<exists> fs. set_mset fs \<subseteq> gs \<and> prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" 
  proof (induct gs)
    case (insert a gs)
    from insert(3) obtain fs where *: "set_mset fs \<subseteq> gs" "prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" by auto    
    let ?fs = "fs + replicate_mset (Suc (g a)) a" 
    show ?case 
    proof (rule exI[of _ "fs + replicate_mset (Suc (g a)) a"], intro conjI)
      show "set_mset ?fs \<subseteq> insert a gs" using *(1) by auto
      show "prod_mset ?fs = (\<Prod>a\<in>insert a gs. a ^ Suc (g a))" 
        by (subst prod.insert[OF insert(1-2)], auto simp: *(2))
    qed
  qed simp
  then obtain fs where "set_mset fs \<subseteq> gs" "prod_mset fs = (\<Prod>a\<in>gs. a ^ Suc (g a))" by auto
  with gs f have ex: "\<exists>fs. f = prod_mset fs \<and> set_mset fs \<subseteq> {q. irreducible q \<and> monic q}"
    by (intro exI[of _ fs], auto)
  thus ?thesis using monic_factorization_unique_mset by blast
qed

lemma monic_prod_mset:
  fixes as :: "'a :: idom poly multiset"
  assumes "\<And> a. a \<in> set_mset as \<Longrightarrow> monic a"
  shows "monic (prod_mset as)" using assms
  by (induct as, auto intro: monic_mult)

lemma exactly_one_factorization:
  assumes f: "f \<noteq> (0 :: 'a :: field poly)"
  shows "\<exists>! cfs. factorization Irr_Mon f cfs"
proof -
  let ?a = "coeff f (degree f)" 
  let ?b = "inverse ?a" 
  let ?g = "smult ?b f" 
  define g where "g = ?g"
  from f have a: "?a \<noteq> 0" "?b \<noteq> 0" by (auto simp: field_simps)
  hence "monic g" unfolding g_def by simp
  note ex1 = exactly_one_monic_factorization[OF this, folded Irr_Mon_def]
  then obtain fs where g: "g = prod_mset fs" "set_mset fs \<subseteq> Irr_Mon" by auto
  let ?cfs = "(?a,fs)" 
  have cfs: "factorization Irr_Mon f ?cfs" unfolding factorization_def split g(1)[symmetric]
    using g(2) unfolding g_def by (simp add: a field_simps)
  show ?thesis
  proof (rule, rule cfs)
    fix dgs
    assume fact: "factorization Irr_Mon f dgs" 
    obtain d gs where dgs: "dgs = (d,gs)" by force
    from fact[unfolded factorization_def dgs split]
    have fd: "f = smult d (prod_mset gs)" and gs: "set_mset gs \<subseteq> Irr_Mon" by auto
    have "monic (prod_mset gs)" by (rule monic_prod_mset, insert gs[unfolded Irr_Mon_def], auto)
    hence d: "d = ?a" unfolding fd by auto
    from arg_cong[OF fd, of "\<lambda> x. smult ?b x", unfolded d g_def[symmetric]]
    have "g = prod_mset gs" using a by (simp add: field_simps)
    with ex1 g gs have "gs = fs" by auto
    thus "dgs = ?cfs" unfolding dgs d by auto
  qed
qed

lemma mod_ident_iff: "m > 0 \<Longrightarrow> (x :: int) mod m = x \<longleftrightarrow> x \<in> {0 ..< m}"
  by (metis Divides.pos_mod_bound Divides.pos_mod_sign atLeastLessThan_iff mod_pos_pos_trivial)

declare prod_mset_prod_list[simp]

lemma mult_1_is_id[simp]: "(*) (1 :: 'a :: ring_1) = id" by auto

context poly_mod
begin

lemma degree_m_eq_monic: "monic f \<Longrightarrow> m > 1 \<Longrightarrow> degree_m f = degree f" 
  by (rule degree_m_eq) auto

lemma monic_degree_m_lift: assumes "monic f" "k > 1" "m > 1"
  shows "monic (poly_mod.Mp (m * k) f)" 
proof -
  have deg: "degree (poly_mod.Mp (m * k) f) = degree f" 
    by (rule poly_mod.degree_m_eq_monic[of f "m * k"], insert assms, auto simp: less_1_mult)
  show ?thesis unfolding poly_mod.Mp_coeff deg assms poly_mod.M_def using assms(2-)
    by (simp add: less_1_mult)
qed

end


locale poly_mod_2 = poly_mod m for m +
  assumes m1: "m > 1"
begin

lemma M_1[simp]: "M 1 = 1" unfolding M_def using m1
  by auto

lemma Mp_1[simp]: "Mp 1 = 1" unfolding Mp_def by simp

lemma monic_degree_m[simp]: "monic f \<Longrightarrow> degree_m f = degree f" 
  using degree_m_eq_monic[of f] using m1 by auto

lemma monic_Mp: "monic f \<Longrightarrow> monic (Mp f)" 
  by (auto simp: Mp_coeff)

lemma Mp_0_smult_sdiv_poly: assumes "Mp f = 0" 
  shows "smult m (sdiv_poly f m) = f"
proof (intro poly_eqI, unfold Mp_coeff coeff_smult sdiv_poly_def, subst coeff_map_poly, force)
  fix n
  from assms have "coeff (Mp f) n = 0" by simp
  hence 0: "coeff f n mod m = 0" unfolding Mp_coeff M_def .
  thus "m * (coeff f n div m) = coeff f n" by auto
qed

lemma Mp_product_modulus: "m' = m * k \<Longrightarrow> k > 0 \<Longrightarrow> Mp (poly_mod.Mp m' f) = Mp f" 
  by (intro poly_eqI, unfold poly_mod.Mp_coeff poly_mod.M_def, auto simp: mod_mod_cancel) 

end

lemma (in poly_mod) degree_m_eq_prime:
  assumes f0: "Mp f \<noteq> 0"
  and deg: "degree_m f = degree f" 
  and eq: "f =m g * h" 
  and p: "prime m" 
  shows "degree_m f = degree_m g + degree_m h" 
proof -
  interpret poly_mod_2 m using prime_ge_2_int[OF p] unfolding poly_mod_2_def by simp
  from f0 eq have "Mp (Mp g * Mp h) \<noteq> 0" by auto
  hence "Mp g * Mp h \<noteq> 0" using Mp_0 by (cases "Mp g * Mp h", auto)
  hence g0: "Mp g \<noteq> 0" and h0: "Mp h \<noteq> 0" by auto
  have "degree (Mp (g * h)) = degree_m (Mp g * Mp h)" by simp
  also have "\<dots> = degree (Mp g * Mp h)" 
  proof (rule degree_m_eq[OF _ m1], rule)
    have id: "\<And> g. coeff (Mp g) (degree (Mp g)) mod m = coeff (Mp g) (degree (Mp g))" 
      unfolding M_def[symmetric] Mp_coeff by simp
    from p have p': "prime m" unfolding prime_int_nat_transfer unfolding prime_nat_iff by auto 
    assume "coeff (Mp g * Mp h) (degree (Mp g * Mp h)) mod m = 0" 
    from this[unfolded coeff_degree_mult] 
    have "coeff (Mp g) (degree (Mp g)) mod m = 0 \<or> coeff (Mp h) (degree (Mp h)) mod m = 0"
      unfolding dvd_eq_mod_eq_0[symmetric] using m1 prime_dvd_mult_int[OF p'] by auto    
    with g0 h0 show False unfolding id by auto
  qed
  also have "\<dots> = degree (Mp g) + degree (Mp h)" 
    by (rule degree_mult_eq[OF g0 h0])
  finally show ?thesis using eq by simp
qed 

lemma monic_smult_add_small: assumes "f = 0 \<or> degree f < degree g" and mon: "monic g" 
  shows "monic (g + smult q f)"
proof (cases "f = 0")
  case True
  thus ?thesis using mon by auto
next
  case False
  with assms have "degree f < degree g" by auto
  hence "degree (smult q f) < degree g" by (meson degree_smult_le not_less order_trans)
  thus ?thesis using mon using coeff_eq_0 degree_add_eq_left by fastforce
qed

context poly_mod 
begin

definition factorization_m :: "int poly \<Rightarrow> (int \<times> int poly multiset) \<Rightarrow> bool" where
  "factorization_m f cfs \<equiv> (case cfs of (c,fs) \<Rightarrow> f =m (smult c (prod_mset fs)) \<and> 
    (\<forall> f \<in> set_mset fs. irreducible\<^sub>d_m f \<and> monic (Mp f)))"

definition Mf :: "int \<times> int poly multiset \<Rightarrow> int \<times> int poly multiset" where
  "Mf cfs \<equiv> case cfs of (c,fs) \<Rightarrow> (M c, image_mset Mp fs)" 

lemma Mf_Mf[simp]: "Mf (Mf x) = Mf x" 
proof (cases x, auto simp: Mf_def, goal_cases)
  case (1 c fs)
  show ?case by (induct fs, auto)
qed

definition equivalent_fact_m :: "int \<times> int poly multiset \<Rightarrow> int \<times> int poly multiset \<Rightarrow> bool" where
  "equivalent_fact_m cfs dgs = (Mf cfs = Mf dgs)" 

definition unique_factorization_m :: "int poly \<Rightarrow> (int \<times> int poly multiset) \<Rightarrow> bool" where
  "unique_factorization_m f cfs = (Mf ` Collect (factorization_m f) = {Mf cfs})"

lemma Mp_irreducible\<^sub>d_m[simp]: "irreducible\<^sub>d_m (Mp f) = irreducible\<^sub>d_m f" 
  unfolding irreducible\<^sub>d_m_def dvdm_def by simp

lemma Mf_factorization_m[simp]: "factorization_m f (Mf cfs) = factorization_m f cfs" 
  unfolding factorization_m_def Mf_def
proof (cases cfs, simp, goal_cases)
  case (1 c fs)
  have "Mp (smult c (prod_mset fs)) = Mp (smult (M c) (Mp (prod_mset fs)))" by simp
  also have "\<dots> = Mp (smult (M c) (Mp (prod_mset (image_mset Mp fs))))"
    unfolding Mp_prod_mset by simp
  also have "\<dots> = Mp (smult (M c) (prod_mset (image_mset Mp fs)))" unfolding Mp_smult ..
  finally show ?case by auto
qed    

lemma unique_factorization_m_imp_factorization: assumes "unique_factorization_m f cfs" 
  shows "factorization_m f cfs" 
proof -
  from assms[unfolded unique_factorization_m_def] obtain dfs where
     fact: "factorization_m f dfs" and id: "Mf cfs = Mf dfs" by blast
  from fact have "factorization_m f (Mf dfs)" by simp
  from this[folded id] show ?thesis by simp
qed

lemma unique_factorization_m_alt_def: "unique_factorization_m f cfs = (factorization_m f cfs
  \<and> (\<forall> dgs. factorization_m f dgs \<longrightarrow> Mf dgs = Mf cfs))" 
  using unique_factorization_m_imp_factorization[of f cfs]
  unfolding unique_factorization_m_def by auto

end

context poly_mod_2
begin

lemma factorization_m_lead_coeff: assumes "factorization_m f (c,fs)" 
  shows "lead_coeff (Mp f) = M c" 
proof -
  note * = assms[unfolded factorization_m_def split]
  have "monic (prod_mset (image_mset Mp fs))" by (rule monic_prod_mset, insert *, auto)
  hence "monic (Mp (prod_mset (image_mset Mp fs)))" by (rule monic_Mp)
  from this[unfolded Mp_prod_mset] have monic: "monic (Mp (prod_mset fs))" by simp
  from * have "lead_coeff (Mp f) = lead_coeff (Mp (smult c (prod_mset fs)))" by simp
  also have "Mp (smult c (prod_mset fs)) = Mp (smult (M c) (Mp (prod_mset fs)))" by simp
  finally show ?thesis 
    using monic \<open>smult c (prod_mset fs) =m smult (M c) (Mp (prod_mset fs))\<close>
    by (metis M_M M_def Mp_0 Mp_coeff lead_coeff_smult m1 mult_cancel_left2 poly_mod.degree_m_eq smult_eq_0_iff)
qed

lemma factorization_m_smult: assumes "factorization_m f (c,fs)" 
  shows "factorization_m (smult d f) (c * d,fs)"
proof -
  note * = assms[unfolded factorization_m_def split]
  from * have f: "Mp f = Mp (smult c (prod_mset fs))" by simp
  have "Mp (smult d f) = Mp (smult d (Mp f))" by simp
  also have "\<dots> = Mp (smult (c * d) (prod_mset fs))" unfolding f by (simp add: ac_simps)
  finally show ?thesis using assms
  unfolding factorization_m_def split by auto
qed

lemma factorization_m_prod: assumes "factorization_m f (c,fs)" "factorization_m g (d,gs)" 
  shows "factorization_m (f * g) (c * d, fs + gs)"
proof -
  note * = assms[unfolded factorization_m_def split]
  have "Mp (f * g) = Mp (Mp f * Mp g)" by simp
  also have "Mp f = Mp (smult c (prod_mset fs))" using * by simp
  also have "Mp g = Mp (smult d (prod_mset gs))" using * by simp
  finally have "Mp (f * g) = Mp (smult (c * d) (prod_mset (fs + gs)))" unfolding mult_Mp
    by (simp add: ac_simps)
  with * show ?thesis unfolding factorization_m_def split by auto
qed

lemma Mp_factorization_m[simp]: "factorization_m (Mp f) cfs = factorization_m f cfs" 
  unfolding factorization_m_def by simp

lemma Mp_unique_factorization_m[simp]: 
  "unique_factorization_m (Mp f) cfs = unique_factorization_m f cfs" 
  unfolding unique_factorization_m_alt_def by simp

lemma unique_factorization_m_cong: "unique_factorization_m f cfs \<Longrightarrow> Mp f = Mp g 
  \<Longrightarrow> unique_factorization_m g cfs"
  unfolding Mp_unique_factorization_m[of f, symmetric] by simp

lemma unique_factorization_mI: assumes "factorization_m f (c,fs)" 
  and "\<And> d gs. factorization_m f (d,gs) \<Longrightarrow> Mf (d,gs) = Mf (c,fs)"
  shows "unique_factorization_m f (c,fs)" 
  unfolding unique_factorization_m_alt_def 
    by (intro conjI[OF assms(1)] allI impI, insert assms(2), auto)

lemma unique_factorization_m_smult: assumes uf: "unique_factorization_m f (c,fs)"
  and d: "M (di * d) = 1"
  shows "unique_factorization_m (smult d f) (c * d,fs)"
proof (rule unique_factorization_mI[OF factorization_m_smult])
  show "factorization_m f (c, fs)" using uf[unfolded unique_factorization_m_alt_def] by auto
  fix e gs
  assume fact: "factorization_m (smult d f) (e,gs)" 
  from factorization_m_smult[OF this, of di] 
  have "factorization_m (Mp (smult di (smult d f))) (e * di, gs)" by simp
  also have "Mp (smult di (smult d f)) = Mp (smult (M (di * d)) f)" by simp
  also have "\<dots> = Mp f" unfolding d by simp
  finally have fact: "factorization_m f (e * di, gs)" by simp
  with uf[unfolded unique_factorization_m_alt_def] have eq: "Mf (e * di, gs) = Mf (c, fs)" by blast
  from eq[unfolded Mf_def] have "M (e * di) = M c" by simp
  from arg_cong[OF this, of "\<lambda> x. M (x * d)"]
  have "M (e * M (di * d)) = M (c * d)" by (simp add: ac_simps)
  from this[unfolded d] have e: "M e = M (c * d)" by simp
  with eq
  show "Mf (e,gs) = Mf (c * d, fs)" unfolding Mf_def split by simp
qed  

lemma unique_factorization_m_smultD: assumes uf: "unique_factorization_m (smult d f) (c,fs)"
  and d: "M (di * d) = 1"
  shows "unique_factorization_m f (c * di,fs)"
proof -
  from d have d': "M (d * di) = 1" by (simp add: ac_simps)
  show ?thesis
  proof (rule unique_factorization_m_cong[OF unique_factorization_m_smult[OF uf d']], 
    rule poly_eqI, unfold Mp_coeff coeff_smult)
    fix n
    have "M (di * (d * coeff f n)) = M (M (di * d) * coeff f n)" by (auto simp: ac_simps)
    from this[unfolded d] show "M (di * (d * coeff f n)) = M (coeff f n)" by simp
  qed
qed

lemma degree_m_eq_lead_coeff: "degree_m f = degree f \<Longrightarrow> lead_coeff (Mp f) = M (lead_coeff f)"
  by (simp add: Mp_coeff)

lemma unique_factorization_m_zero: assumes "unique_factorization_m f (c,fs)" 
  shows "M c \<noteq> 0" 
proof
  assume c: "M c = 0" 
  from unique_factorization_m_imp_factorization[OF assms]
  have "Mp f = Mp (smult (M c) (prod_mset fs))" unfolding factorization_m_def split 
    by simp
  from this[unfolded c] have f: "Mp f = 0" by simp
  have "factorization_m f (0,{#})" 
    unfolding factorization_m_def split f by auto
  moreover have "Mf (0,{#}) = (0,{#})" unfolding Mf_def by auto
  ultimately have fact1: "(0, {#}) \<in> Mf ` Collect (factorization_m f)" by force
  define g :: "int poly" where "g = [:0,1:]" 
  have mpg: "Mp g = [:0,1:]" unfolding Mp_def
    by (auto simp: g_def)
  {
    fix g h
    assume *: "degree (Mp g) = 0" "degree (Mp h) = 0" "[:0, 1:] = Mp (g * h)" 
    from arg_cong[OF *(3), of degree] have "1 = degree_m (Mp g * Mp h)" by simp
    also have "\<dots> \<le> degree (Mp g * Mp h)" by (rule degree_m_le)
    also have "\<dots> \<le> degree (Mp g) + degree (Mp h)" by (rule degree_mult_le)
    also have "\<dots> \<le> 0" using * by simp
    finally have False by simp
  } note irr = this    
  have "factorization_m f (0,{# g #})" 
    unfolding factorization_m_def split using irr
    by (auto simp: irreducible\<^sub>d_m_def f mpg)
  moreover have "Mf (0,{# g #}) = (0,{# g #})" unfolding Mf_def by (auto simp: mpg, simp add: g_def)
  ultimately have fact2: "(0, {#g#}) \<in> Mf ` Collect (factorization_m f)" by force
  note [simp] = assms[unfolded unique_factorization_m_def]
  from fact1[simplified, folded fact2[simplified]] show False by auto
qed


end

context poly_mod
begin

lemma dvdm_smult: assumes "f dvdm g" 
  shows "f dvdm smult c g" 
proof -
  from assms[unfolded dvdm_def] obtain h where g: "g =m f * h" by auto
  show ?thesis unfolding dvdm_def
  proof (intro exI[of _ "smult c h"])
    have "Mp (smult c g) = Mp (smult c (Mp g))" by simp
    also have "Mp g = Mp (f * h)" using g by simp
    finally show "Mp (smult c g) = Mp (f * smult c h)" by simp
  qed
qed

lemma dvdm_factor: assumes "f dvdm g" 
  shows "f dvdm g * h" 
proof -
  from assms[unfolded dvdm_def] obtain k where g: "g =m f * k" by auto
  show ?thesis unfolding dvdm_def
  proof (intro exI[of _ "h * k"])
    have "Mp (g * h) = Mp (Mp g * h)" by simp
    also have "Mp g = Mp (f * k)" using g by simp
    finally show "Mp (g * h) = Mp (f * (h * k))" by (simp add: ac_simps)
  qed
qed    

lemma square_free_m_smultD: assumes "square_free_m (smult c f)" 
  shows "square_free_m f" 
  unfolding square_free_m_def
proof (intro conjI allI impI)
  fix g
  assume "degree_m g \<noteq> 0" 
  with assms[unfolded square_free_m_def] have "\<not> g * g dvdm smult c f" by auto
  thus "\<not> g * g dvdm f" using dvdm_smult[of "g * g" f c] by blast
next
  from assms[unfolded square_free_m_def] have "\<not> smult c f =m 0" by simp
  thus "\<not> f =m 0" 
    by (metis Mp_smult(2) smult_0_right)
qed

lemma square_free_m_smultI: assumes sf: "square_free_m f" 
  and inv: "M (ci * c) = 1" 
  shows "square_free_m (smult c f)" 
proof -
  have "square_free_m (smult ci (smult c f))" 
  proof (rule square_free_m_cong[OF sf], rule poly_eqI, unfold Mp_coeff coeff_smult)
    fix n
    have "M (ci * (c * coeff f n)) = M ( M (ci * c) * coeff f n)" by (simp add: ac_simps)
    from this[unfolded inv] show "M (coeff f n) = M (ci * (c * coeff f n))" by simp
  qed
  from square_free_m_smultD[OF this] show ?thesis .
qed


lemma square_free_m_factor: assumes "square_free_m (f * g)" 
  shows "square_free_m f" "square_free_m g"
proof -
  {
    fix f g
    assume sf: "square_free_m (f * g)" 
    have "square_free_m f"         
      unfolding square_free_m_def
    proof (intro conjI allI impI)
      fix h
      assume "degree_m h \<noteq> 0" 
      with sf[unfolded square_free_m_def] have "\<not> h * h dvdm f * g" by auto
      thus "\<not> h * h dvdm f" using dvdm_factor[of "h * h" f g] by blast
    next
      from sf[unfolded square_free_m_def] have "\<not> f * g =m 0" by simp
      thus "\<not> f =m 0"
        by (metis mult.commute mult_zero_right poly_mod.mult_Mp(2))
    qed
  }
  from this[of f g] this[of g f] assms 
  show "square_free_m f" "square_free_m g" by (auto simp: ac_simps)
qed

end

context poly_mod_2
begin

lemma Mp_ident_iff: "Mp f = f \<longleftrightarrow> (\<forall> n. coeff f n \<in> {0 ..< m})" 
proof -
  have m0: "m > 0" using m1 by simp
  show ?thesis unfolding poly_eq_iff Mp_coeff M_def mod_ident_iff[OF m0] by simp
qed

lemma Mp_ident_iff': "Mp f = f \<longleftrightarrow> (set (coeffs f) \<subseteq> {0 ..< m})" 
proof -
  have 0: "0 \<in> {0 ..< m}" using m1 by auto
  have ran: "(\<forall>n. coeff f n \<in> {0..<m}) \<longleftrightarrow> range (coeff f) \<subseteq> {0 ..< m}" by blast
  show ?thesis unfolding Mp_ident_iff ran using range_coeff[of f] 0 by auto
qed
end

lemma Mp_Mp_pow_is_Mp: "n \<noteq> 0 \<Longrightarrow> p > 1 \<Longrightarrow> poly_mod.Mp p (poly_mod.Mp (p^n) f) 
  = poly_mod.Mp p f"
  using  poly_mod_2.Mp_product_modulus poly_mod_2_def by(subst power_eq_if, auto)

lemma M_M_pow_is_M: "n \<noteq> 0 \<Longrightarrow> p > 1 \<Longrightarrow> poly_mod.M p (poly_mod.M (p^n) f) 
  = poly_mod.M p f" using Mp_Mp_pow_is_Mp[of n p "[:f:]"]
  by (metis coeff_pCons_0 poly_mod.Mp_coeff)

definition inverse_mod :: "int \<Rightarrow> int \<Rightarrow> int" where
  "inverse_mod x m = fst (bezout_coefficients x m)" 

lemma inverse_mod:
  "(inverse_mod x m * x) mod m = 1"
  if "coprime x m" "m > 1"
proof -
  from bezout_coefficients [of x m "inverse_mod x m" "snd (bezout_coefficients x m)"]
  have "inverse_mod x m * x + snd (bezout_coefficients x m) * m = gcd x m"
    by (simp add: inverse_mod_def)
  with that have "inverse_mod x m * x + snd (bezout_coefficients x m) * m = 1"
    by simp
  then have "(inverse_mod x m * x + snd (bezout_coefficients x m) * m) mod m = 1 mod m"
    by simp
  with \<open>m > 1\<close> show ?thesis
    by simp
qed

lemma inverse_mod_pow:
  "(inverse_mod x (p ^ n) * x) mod (p ^ n) = 1"
  if "coprime x p" "p > 1" "n \<noteq> 0" 
  using that by (auto intro: inverse_mod)

lemma (in poly_mod) inverse_mod_coprime:
  assumes p: "prime m" 
  and cop: "coprime x m" shows "M (inverse_mod x m * x) = 1" 
  unfolding M_def using inverse_mod_pow[OF cop, of 1] p
  by (auto simp: prime_int_iff)

lemma (in poly_mod) inverse_mod_coprime_exp:
  assumes m: "m = p^n" and p: "prime p" 
  and n: "n \<noteq> 0" and cop: "coprime x p"
  shows "M (inverse_mod x m * x) = 1" 
  unfolding M_def unfolding m using inverse_mod_pow[OF cop _ n] p
  by (auto simp: prime_int_iff)

locale poly_mod_prime = poly_mod p for p :: int +
  assumes prime: "prime p" 
begin

sublocale poly_mod_2 p using prime unfolding poly_mod_2_def
  using prime_gt_1_int by force

lemma square_free_m_prod_imp_coprime_m: assumes sf: "square_free_m (A * B)" 
  shows "coprime_m A B"
  unfolding coprime_m_def
proof (intro allI impI)
  fix h
  assume dvd: "h dvdm A" "h dvdm B"
  then obtain ha hb where *: "Mp A = Mp (h * ha)" "Mp B = Mp (h * hb)" 
    unfolding dvdm_def by auto
  have AB: "Mp (A * B) = Mp (Mp A * Mp B)" by simp
  from this[unfolded *, simplified] 
  have eq: "Mp (A * B) = Mp (h * h * (ha * hb))" by (simp add: ac_simps)
  hence dvd_hh: "(h * h) dvdm (A * B)" unfolding dvdm_def by auto
  {
    assume "degree_m h \<noteq> 0" 
    from sf[unfolded square_free_m_def, THEN conjunct2, rule_format, OF this]
    have "\<not> h * h dvdm A * B" . 
    with dvd_hh have False by simp
  }
  hence "degree (Mp h) = 0" by auto
  then obtain c where hc: "Mp h = [: c :]" by (rule degree_eq_zeroE)
  {
    assume "c = 0" 
    hence "Mp h = 0" unfolding hc by auto
    with *(1) have "Mp A = 0"
      by (metis Mp_0 mult_zero_left poly_mod.mult_Mp(1))
    with sf[unfolded square_free_m_def, THEN conjunct1] have False
      by (simp add: AB)
  }
  hence c0: "c \<noteq> 0" by auto    
  with arg_cong[OF hc[symmetric], of "\<lambda> f. coeff f 0", unfolded Mp_coeff M_def] m1
  have "c \<ge> 0" "c < p" by auto
  with c0 have c_props:"c > 0" "c < p" by auto
  with prime have "prime p" by simp
  with c_props have "coprime p c"
    by (auto intro: prime_imp_coprime dest: zdvd_not_zless)
  then have "coprime c p"
    by (simp add: ac_simps)
  from inverse_mod_coprime[OF prime this]
  obtain d where d: "M (c * d) = 1" by (auto simp: ac_simps)
  show "h dvdm 1" unfolding dvdm_def
  proof (intro exI[of _ "[:d:]"])
    have "Mp (h * [: d :]) = Mp (Mp h * [: d :])" by simp
    also have "\<dots> = Mp ([: c * d :])" unfolding hc by (auto simp: ac_simps)
    also have "\<dots> = [: M (c * d) :]" unfolding Mp_def
      by (metis (no_types) M_0 map_poly_pCons Mp_0 Mp_def d zero_neq_one)
    also have "\<dots> = 1" unfolding d by simp
    finally show "Mp 1 = Mp (h * [:d:])" by simp
  qed
qed

lemma coprime_exp_mod: "coprime lu p \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> lu mod p ^ n \<noteq> 0" 
  using prime by fastforce

end

context poly_mod
begin

definition Dp :: "int poly \<Rightarrow> int poly" where
  "Dp f = map_poly (\<lambda> a. a div m) f" 

lemma Dp_Mp_eq: "f = Mp f + smult m (Dp f)"
  by (rule poly_eqI, auto simp: Mp_coeff M_def Dp_def coeff_map_poly)

lemma dvd_imp_dvdm:
  assumes "a dvd b" shows "a dvdm b"
  by (metis assms dvd_def dvdm_def)

lemma dvdm_add:
  assumes a: "u dvdm a"
  and b: "u dvdm b"
  shows "u dvdm (a+b)"
proof -
  obtain a' where a: "a =m u*a'" using a unfolding dvdm_def by auto
  obtain b' where b: "b =m u*b'" using b unfolding dvdm_def by auto
  have "Mp (a + b) = Mp (u*a'+u*b')" using a b
    by (metis poly_mod.plus_Mp(1) poly_mod.plus_Mp(2))
  also have "... = Mp (u * (a'+ b'))"
    by (simp add: distrib_left)
  finally show ?thesis unfolding dvdm_def by auto
qed


lemma monic_dvdm_constant:
  assumes uk: "u dvdm [:k:]"
  and u1: "monic u" and u2: "degree u > 0" 
  shows "k mod m = 0"
proof -
  have d1: "degree_m [:k:] = degree [:k:]"    
    by (metis degree_pCons_0 le_zero_eq poly_mod.degree_m_le)
  obtain h where h: "Mp [:k:] = Mp (u * h)"
    using uk unfolding dvdm_def by auto
  have d2: "degree_m [:k:] = degree_m (u*h)" using h by metis
  have d3: "degree (map_poly M (u * map_poly M h)) = degree (u * map_poly M h)" 
    by (rule degree_map_poly)
       (metis coeff_degree_mult leading_coeff_0_iff mult.right_neutral M_M Mp_coeff Mp_def u1)
  thus ?thesis using assms d1 d2 d3
    by (auto, metis M_def map_poly_pCons degree_mult_right_le h leD map_poly_0 
        mult_poly_0_right pCons_eq_0_iff M_0 Mp_def mult_Mp(2)) 
qed

lemma div_mod_imp_dvdm:
  assumes "\<exists>q r. b = q * a + Polynomial.smult m r"
  shows "a dvdm b"
proof -
  from assms  obtain q r where b:"b = a * q + smult m r"
    by (metis mult.commute)
  have a: "Mp (Polynomial.smult m r) = 0" by auto
  show ?thesis 
  proof (unfold dvdm_def, rule exI[of _ q])
    have "Mp (a * q + smult m r) = Mp (a * q + Mp (smult m r))" 
      using plus_Mp(2)[of "a*q" "smult m r"] by auto
    also have "... = Mp (a*q)" by auto
    finally show "eq_m b (a * q)" using b by auto
  qed
qed

lemma lead_coeff_monic_mult:
  fixes p :: "'a :: {comm_semiring_1,semiring_no_zero_divisors} poly"
  assumes "monic p" shows "lead_coeff (p * q) = lead_coeff q"
  using assms by (simp add: lead_coeff_mult)

lemma degree_m_mult_eq:
  assumes p: "monic p" and q: "lead_coeff q mod m \<noteq> 0" and m1: "m > 1"
  shows "degree (Mp (p * q)) = degree p + degree q"
proof-
  have "lead_coeff (p * q) mod m \<noteq> 0"
    using q p by (auto simp: lead_coeff_monic_mult)
  with m1 show ?thesis
    by (auto simp: degree_m_eq intro!: degree_mult_eq)
qed

lemma dvdm_imp_degree_le:
  assumes pq: "p dvdm q" and p: "monic p" and q0: "Mp q \<noteq> 0" and m1: "m > 1"
  shows "degree p \<le> degree q"
proof-
  from q0
  have q: "lead_coeff (Mp q) mod m \<noteq> 0"
    by (metis Mp_Mp Mp_coeff leading_coeff_neq_0 M_def)
  from pq obtain r where Mpq: "Mp q = Mp (p * Mp r)" by (auto elim: dvdmE)
  with p q have "lead_coeff (Mp r) mod m \<noteq> 0"
    by (metis Mp_Mp Mp_coeff leading_coeff_0_iff mult_poly_0_right M_def)
  from degree_m_mult_eq[OF p this m1] Mpq
  have "degree p \<le> degree_m q" by simp
  thus ?thesis using degree_m_le le_trans by blast
qed

lemma dvdm_uminus [simp]:
  "p dvdm -q \<longleftrightarrow> p dvdm q"
  by (metis add.inverse_inverse dvdm_smult smult_1_left smult_minus_left)


(*TODO: simp?*)
lemma Mp_const_poly: "Mp [:a:] = [:a mod m:]"   
  by (simp add: Mp_def M_def Polynomial.map_poly_pCons)

lemma dvdm_imp_div_mod:
  assumes "u dvdm g"
  shows "\<exists>q r. g = q*u + smult m r"
proof -
  obtain q where q: "Mp g = Mp (u*q)" 
    using assms unfolding dvdm_def by fast
  have "(u*q) = Mp (u*q) + smult m (Dp (u*q))"
    by (simp add: poly_mod.Dp_Mp_eq[of "u*q"])
  hence uq: "Mp (u*q) = (u*q) - smult m (Dp (u*q))"
    by auto  
  have g: "g = Mp g + smult m (Dp g)"
    by (simp add: poly_mod.Dp_Mp_eq[of "g"])
  also have "... = poly_mod.Mp m (u*q) + smult m (Dp g)" using q by simp
  also have "... = u * q - smult m (Dp (u * q)) + smult m (Dp g)" 
    unfolding uq by auto
  also have "... = u * q + smult m (-Dp (u*q)) + smult m (Dp g)" by auto  
  also have "... = u * q + smult m (-Dp (u*q) + Dp g)" 
    unfolding smult_add_right by auto
  also have "... = q * u + smult m (-Dp (u*q) + Dp g)" by auto
  finally show ?thesis by auto
qed

corollary div_mod_iff_dvdm:
  shows "a dvdm b = (\<exists>q r. b = q * a + Polynomial.smult m r)"
  using div_mod_imp_dvdm dvdm_imp_div_mod by blast

lemma dvdmE':
  assumes "p dvdm q" and "\<And>r. q =m p * Mp r \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: dvdm_def)

end

context poly_mod_2
begin
lemma factorization_m_mem_dvdm: assumes fact: "factorization_m f (c,fs)" 
  and mem: "Mp g \<in># image_mset Mp fs" 
shows "g dvdm f" 
proof - 
  from fact have "factorization_m f (Mf (c, fs))" by auto
  then obtain l where f: "factorization_m f (l, image_mset Mp fs)" by (auto simp: Mf_def)
  from multi_member_split[OF mem] obtain ls where 
    fs: "image_mset Mp fs = {# Mp g #} + ls" by auto
  from f[unfolded fs split factorization_m_def] show "g dvdm f" 
    unfolding dvdm_def
    by (intro exI[of _ "smult l (prod_mset ls)"], auto simp del: Mp_smult 
        simp add: Mp_smult(2)[of _ "Mp g * prod_mset ls", symmetric], simp)
qed

lemma dvdm_degree: "monic u \<Longrightarrow> u dvdm f \<Longrightarrow> Mp f \<noteq> 0 \<Longrightarrow> degree u \<le> degree f"
  using dvdm_imp_degree_le m1 by blast

end

lemma (in poly_mod_prime) pl_dvdm_imp_p_dvdm:
  assumes l0: "l \<noteq> 0" 
  and pl_dvdm: "poly_mod.dvdm (p^l) a b"
  shows "a dvdm b"
proof -
  from l0 have l_gt_0: "l > 0" by auto
  with m1 interpret pl: poly_mod_2 "p^l" by (unfold_locales, auto)
  have p_rw: "p * p ^ (l - 1) = p ^ l" by (rule power_minus_simp[symmetric, OF l_gt_0])
  obtain q r where b: "b = q * a + smult (p^l) r" using pl.dvdm_imp_div_mod[OF pl_dvdm] by auto
  have "smult (p^l) r = smult p (smult (p ^ (l - 1)) r)" unfolding smult_smult p_rw ..
  hence b2: "b = q * a + smult p (smult (p ^ (l - 1)) r)" using b by auto
  show ?thesis
    by (rule div_mod_imp_dvdm, rule exI[of _ q], 
        rule exI[of _ "(smult (p ^ (l - 1)) r)"], auto simp add: b2)
qed


end