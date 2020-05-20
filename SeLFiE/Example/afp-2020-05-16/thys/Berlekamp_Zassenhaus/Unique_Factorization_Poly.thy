(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Unique Factorization Domain for Polynomials\<close>

text \<open>In this theory we prove that the polynomials over a unique factorization domain (UFD) form a UFD.\<close>

theory Unique_Factorization_Poly
imports
  Unique_Factorization
  Polynomial_Factorization.Missing_Polynomial_Factorial 
  Subresultants.More_Homomorphisms 
  "HOL-Computational_Algebra.Field_as_Ring"
begin

hide_const (open) module.smult
hide_const (open) Divisibility.irreducible

instantiation fract :: (idom) "{normalization_euclidean_semiring, euclidean_ring}"
begin

definition [simp]: "normalize_fract \<equiv> (normalize_field :: 'a fract \<Rightarrow> _)"
definition [simp]: "unit_factor_fract = (unit_factor_field :: 'a fract \<Rightarrow> _)"
definition [simp]: "euclidean_size_fract = (euclidean_size_field :: 'a fract \<Rightarrow> _)"
definition [simp]: "modulo_fract = (mod_field :: 'a fract \<Rightarrow> _)"

instance by standard (simp_all add: dvd_field_iff divide_simps)

end

instantiation fract :: (idom) euclidean_ring_gcd
begin

definition gcd_fract :: "'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract" where
  "gcd_fract \<equiv> Euclidean_Algorithm.gcd"
definition lcm_fract :: "'a fract \<Rightarrow> 'a fract \<Rightarrow> 'a fract" where
  "lcm_fract \<equiv> Euclidean_Algorithm.lcm"
definition Gcd_fract :: "'a fract set \<Rightarrow> 'a fract" where
 "Gcd_fract \<equiv> Euclidean_Algorithm.Gcd"
definition Lcm_fract :: "'a fract set \<Rightarrow> 'a fract" where
 "Lcm_fract \<equiv> Euclidean_Algorithm.Lcm"

instance
  by (standard, simp_all add: gcd_fract_def lcm_fract_def Gcd_fract_def Lcm_fract_def)

end
(*field + unique_euclidean_ring + euclidean_ring_gcd + normalization_semidom_multiplicative*)

instantiation fract :: (idom) unique_euclidean_ring
begin

definition [simp]: "division_segment_fract (x :: 'a fract) = (1 :: 'a fract)"

instance by standard (auto split: if_splits)
end

instance fract :: (idom) field_gcd by standard auto


definition divides_ff :: "'a::idom fract \<Rightarrow> 'a fract \<Rightarrow> bool"
  where "divides_ff x y \<equiv> \<exists> r. y = x * to_fract r"

lemma ff_list_pairs: 
  "\<exists> xs. X = map (\<lambda> (x,y). Fraction_Field.Fract x y) xs \<and> 0 \<notin> snd ` set xs"
proof (induct X)
  case (Cons a X)
  from Cons(1) obtain xs where X: "X = map (\<lambda> (x,y). Fraction_Field.Fract x y)  xs" and xs: "0 \<notin> snd ` set xs"
    by auto
  obtain x y where a: "a = Fraction_Field.Fract x y" and y: "y \<noteq> 0" by (cases a, auto)
  show ?case unfolding X a using xs y
    by (intro exI[of _ "(x,y) # xs"], auto)
qed auto

lemma divides_ff_to_fract[simp]: "divides_ff (to_fract x) (to_fract y) \<longleftrightarrow> x dvd y"
  unfolding divides_ff_def dvd_def
  by (simp add: to_fract_def eq_fract(1) mult.commute)

lemma
  shows divides_ff_mult_cancel_left[simp]: "divides_ff (z * x) (z * y) \<longleftrightarrow> z = 0 \<or> divides_ff x y"
    and divides_ff_mult_cancel_right[simp]: "divides_ff (x * z) (y * z) \<longleftrightarrow> z = 0 \<or> divides_ff x y"
  unfolding divides_ff_def by auto

definition gcd_ff_list :: "'a::ufd fract list \<Rightarrow> 'a fract \<Rightarrow> bool" where
  "gcd_ff_list X g = (
     (\<forall> x \<in> set X. divides_ff g x) \<and> 
     (\<forall> d. (\<forall> x \<in> set X. divides_ff d x) \<longrightarrow> divides_ff d g))"

lemma gcd_ff_list_exists: "\<exists> g. gcd_ff_list (X :: 'a::ufd fract list) g"
proof -
  interpret some_gcd: idom_gcd "(*)" "1 :: 'a" "(+)" 0 "(-)" uminus some_gcd
    rewrites "dvd.dvd ((*)) = (dvd)" by (unfold_locales, auto simp: dvd_rewrites)
  from ff_list_pairs[of X] obtain xs where X: "X = map (\<lambda> (x,y). Fraction_Field.Fract x y) xs"
    and xs: "0 \<notin> snd ` set xs" by auto
  define r where "r \<equiv> prod_list (map snd xs)"
  have r: "r \<noteq> 0" unfolding r_def prod_list_zero_iff using xs by auto
  define ys where "ys \<equiv> map (\<lambda> (x,y). x * prod_list (remove1 y (map snd xs))) xs"
  {
    fix i
    assume "i < length X"
    hence i: "i < length xs" unfolding X by auto
    obtain x y where xsi: "xs ! i = (x,y)" by force
    with i have "(x,y) \<in> set xs" unfolding set_conv_nth by force
    hence y_mem: "y \<in> set (map snd xs)" by force
    with xs have y: "y \<noteq> 0" by force
    from i have id1: "ys ! i = x * prod_list (remove1 y (map snd xs))" unfolding ys_def using xsi by auto
    from i xsi have id2: "X ! i = Fraction_Field.Fract x y" unfolding X by auto
    have lp: "prod_list (remove1 y (map snd xs)) * y = r" unfolding r_def
      by (rule prod_list_remove1[OF y_mem])
    have "ys ! i \<in> set ys" using i unfolding ys_def by auto
    moreover have "to_fract (ys ! i) = to_fract r * (X ! i)"
      unfolding id1 id2 to_fract_def mult_fract
      by (subst eq_fract(1), force, force simp: y, simp add: lp)
    ultimately have "ys ! i \<in> set ys" "to_fract (ys ! i) = to_fract r * (X ! i)" .
  } note ys = this
  define G where "G \<equiv> some_gcd.listgcd ys"
  define g where "g \<equiv> to_fract G * Fraction_Field.Fract 1 r"
  have len: "length X = length ys" unfolding X ys_def by auto
  show ?thesis
  proof (rule exI[of _ g], unfold gcd_ff_list_def, intro ballI conjI impI allI)
    fix x
    assume "x \<in> set X"
    then obtain i where i: "i < length X" and x: "x = X ! i" unfolding set_conv_nth by auto
    from ys[OF i] have id: "to_fract (ys ! i) = to_fract r * x" 
      and ysi: "ys ! i \<in> set ys" unfolding x by auto
    from some_gcd.listgcd[OF ysi] have "G dvd ys ! i" unfolding G_def .
    then obtain d where ysi: "ys ! i = G * d" unfolding dvd_def by auto
    have "to_fract d * (to_fract G * Fraction_Field.Fract 1 r) = x * (to_fract r * Fraction_Field.Fract 1 r)" 
      using id[unfolded ysi]
      by (simp add: ac_simps)
    also have "\<dots> = x" using r unfolding to_fract_def by (simp add: eq_fract One_fract_def)
    finally have "to_fract d * (to_fract G * Fraction_Field.Fract 1 r) = x" by simp
    thus "divides_ff g x" unfolding divides_ff_def g_def 
      by (intro exI[of _ d], auto)
  next
    fix d
    assume "\<forall>x \<in> set X. divides_ff d x"
    hence "Ball ((\<lambda> x. to_fract r * x) ` set X) ( divides_ff (to_fract r * d))" by simp
    also have "(\<lambda> x. to_fract r * x) ` set X = to_fract ` set ys"
      unfolding set_conv_nth using ys len by force
    finally have dvd: "Ball (set ys) (\<lambda> y. divides_ff (to_fract r * d) (to_fract y))" by auto
    obtain nd dd where d: "d = Fraction_Field.Fract nd dd" and dd: "dd \<noteq> 0" by (cases d, auto)
    {
      fix y
      assume "y \<in> set ys"
      hence "divides_ff (to_fract r * d) (to_fract y)" using dvd by auto
      from this[unfolded divides_ff_def d to_fract_def mult_fract]
      obtain ra where "Fraction_Field.Fract y 1 = Fraction_Field.Fract (r * nd * ra) dd" by auto
      hence "y * dd = ra * (r * nd)" by (simp add: eq_fract dd)
      hence "r * nd dvd y * dd" by auto
    }
    hence "r * nd dvd some_gcd.listgcd ys * dd" by (rule some_gcd.listgcd_greatest_mult)
    hence "divides_ff (to_fract r * d) (to_fract G)" unfolding to_fract_def d mult_fract
      G_def divides_ff_def by (auto simp add: eq_fract dd dvd_def)
    also have "to_fract G = to_fract r * g" unfolding g_def using r
      by (auto simp: to_fract_def eq_fract)
    finally show "divides_ff d g" using r by simp
  qed
qed

definition some_gcd_ff_list :: "'a :: ufd fract list \<Rightarrow> 'a fract" where
  "some_gcd_ff_list xs = (SOME g. gcd_ff_list xs g)"

lemma some_gcd_ff_list: "gcd_ff_list xs (some_gcd_ff_list xs)"
  unfolding some_gcd_ff_list_def using gcd_ff_list_exists[of xs]
  by (rule someI_ex)

lemma some_gcd_ff_list_divides: "x \<in> set xs \<Longrightarrow> divides_ff (some_gcd_ff_list xs) x"
  using some_gcd_ff_list[of xs] unfolding gcd_ff_list_def by auto

lemma some_gcd_ff_list_greatest: "(\<forall>x \<in> set xs. divides_ff d x) \<Longrightarrow> divides_ff d (some_gcd_ff_list xs)"
  using some_gcd_ff_list[of xs] unfolding gcd_ff_list_def by auto

lemma divides_ff_refl[simp]: "divides_ff x x"
  unfolding divides_ff_def
  by (rule exI[of _ 1], auto simp: to_fract_def One_fract_def)

lemma divides_ff_trans:
  "divides_ff x y \<Longrightarrow> divides_ff y z \<Longrightarrow> divides_ff x z"
  unfolding divides_ff_def
  by (auto simp del: to_fract_hom.hom_mult simp add: to_fract_hom.hom_mult[symmetric])

lemma divides_ff_mult_right: "a \<noteq> 0 \<Longrightarrow> divides_ff (x * inverse a) y \<Longrightarrow> divides_ff x (a * y)"
  unfolding divides_ff_def divide_inverse[symmetric] by auto

definition eq_dff :: "'a :: ufd fract \<Rightarrow> 'a fract \<Rightarrow> bool" (infix "=dff" 50) where
  "x =dff y \<longleftrightarrow> divides_ff x y \<and> divides_ff y x"

lemma eq_dffI[intro]: "divides_ff x y \<Longrightarrow> divides_ff y x \<Longrightarrow> x =dff y" 
  unfolding eq_dff_def by auto

lemma eq_dff_refl[simp]: "x =dff x"
  by (intro eq_dffI, auto)

lemma eq_dff_sym: "x =dff y \<Longrightarrow> y =dff x" unfolding eq_dff_def by auto

lemma eq_dff_trans[trans]: "x =dff y \<Longrightarrow> y =dff z \<Longrightarrow> x =dff z"
  unfolding eq_dff_def using divides_ff_trans by auto

lemma eq_dff_cancel_right[simp]: "x * y =dff x * z \<longleftrightarrow> x = 0 \<or> y =dff z" 
  unfolding eq_dff_def by auto

lemma eq_dff_mult_right_trans[trans]: "x =dff y * z \<Longrightarrow> z =dff u \<Longrightarrow> x =dff y * u"
  using eq_dff_trans by force

lemma some_gcd_ff_list_smult: "a \<noteq> 0 \<Longrightarrow> some_gcd_ff_list (map ((*) a) xs) =dff a * some_gcd_ff_list xs"
proof 
  let ?g = "some_gcd_ff_list (map ((*) a) xs)"
  show "divides_ff (a * some_gcd_ff_list xs) ?g"
    by (rule some_gcd_ff_list_greatest, insert some_gcd_ff_list_divides[of _ xs], auto simp: divides_ff_def)
  assume a: "a \<noteq> 0"
  show "divides_ff ?g (a * some_gcd_ff_list xs)"
  proof (rule divides_ff_mult_right[OF a some_gcd_ff_list_greatest], intro ballI)
    fix x
    assume x: "x \<in> set xs"
    have "divides_ff (?g * inverse a) x = divides_ff (inverse a * ?g) (inverse a * (a * x))"
      using a by (simp add: field_simps)
    also have "\<dots>" using a x by (auto intro: some_gcd_ff_list_divides)
    finally show "divides_ff (?g * inverse a) x" .
  qed
qed

definition content_ff :: "'a::ufd fract poly \<Rightarrow> 'a fract" where 
  "content_ff p = some_gcd_ff_list (coeffs p)"

lemma content_ff_iff: "divides_ff x (content_ff p) \<longleftrightarrow> (\<forall> c \<in> set (coeffs p). divides_ff x c)" (is "?l = ?r")
proof
  assume ?l
  from divides_ff_trans[OF this, unfolded content_ff_def, OF some_gcd_ff_list_divides] show ?r ..
next
  assume ?r
  thus ?l unfolding content_ff_def by (intro some_gcd_ff_list_greatest, auto)
qed

lemma content_ff_divides_ff: "x \<in> set (coeffs p) \<Longrightarrow> divides_ff (content_ff p) x"
  unfolding content_ff_def by (rule some_gcd_ff_list_divides)

lemma content_ff_0[simp]: "content_ff 0 = 0"
  using content_ff_iff[of 0 0] by (auto simp: divides_ff_def)

lemma content_ff_0_iff[simp]: "(content_ff p = 0) = (p = 0)"
proof (cases "p = 0")
  case False
  define a where "a \<equiv> last (coeffs p)"
  define xs where "xs \<equiv> coeffs p"
  from False
  have mem: "a \<in> set (coeffs p)" and a: "a \<noteq> 0"
    unfolding a_def last_coeffs_eq_coeff_degree[OF False] coeffs_def by auto
  from content_ff_divides_ff[OF mem] have "divides_ff (content_ff p) a" .
  with a have "content_ff p \<noteq> 0" unfolding divides_ff_def by auto
  with False show ?thesis by auto
qed auto

lemma content_ff_eq_dff_nonzero: "content_ff p =dff x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> p \<noteq> 0"
  using divides_ff_def eq_dff_def by force

lemma content_ff_smult: "content_ff (smult (a::'a::ufd fract) p) =dff a * content_ff p"
proof (cases "a = 0")
  case False note a = this
  have id: "coeffs (smult a p) = map ((*) a) (coeffs p)"
    unfolding coeffs_smult using a by (simp add: Polynomial.coeffs_smult)
  show ?thesis unfolding content_ff_def id using some_gcd_ff_list_smult[OF a] .
qed simp

definition normalize_content_ff
  where "normalize_content_ff (p::'a::ufd fract poly) \<equiv> smult (inverse (content_ff p)) p"

lemma smult_normalize_content_ff: "smult (content_ff p) (normalize_content_ff p) = p"  
  unfolding normalize_content_ff_def
  by (cases "p = 0", auto)

lemma content_ff_normalize_content_ff_1: assumes p0: "p \<noteq> 0" 
  shows "content_ff (normalize_content_ff p) =dff 1"
proof -
  have "content_ff p = content_ff (smult (content_ff p) (normalize_content_ff p))" unfolding smult_normalize_content_ff ..
  also have "\<dots> =dff content_ff p * content_ff (normalize_content_ff p)" by (rule content_ff_smult)
  finally show ?thesis unfolding eq_dff_def divides_ff_def using p0 by auto
qed

lemma content_ff_to_fract: assumes "set (coeffs p) \<subseteq> range to_fract"
  shows "content_ff p \<in> range to_fract"
proof -
  have "divides_ff 1 (content_ff p)" using assms
    unfolding content_ff_iff unfolding divides_ff_def[abs_def] by auto
  thus ?thesis unfolding divides_ff_def by auto
qed

lemma content_ff_map_poly_to_fract: "content_ff (map_poly to_fract (p :: 'a :: ufd poly)) \<in> range to_fract"
  by (rule content_ff_to_fract, subst coeffs_map_poly, auto)

lemma range_coeffs_to_fract: assumes "set (coeffs p) \<subseteq> range to_fract" 
  shows "\<exists> m. coeff p i = to_fract m"
proof -
  from assms(1) to_fract_0 have "coeff p i \<in> range to_fract" using range_coeff [of p]
    by auto (metis contra_subsetD to_fract_hom.hom_zero insertE range_eqI)
  thus ?thesis by auto
qed

lemma divides_ff_coeff: assumes "set (coeffs p) \<subseteq> range to_fract" and "divides_ff (to_fract n) (coeff p i)"
  shows "\<exists> m. coeff p i = to_fract n * to_fract m"
proof -
  from range_coeffs_to_fract[OF assms(1)]  obtain k where pi: "coeff p i = to_fract k" by auto
  from assms(2)[unfolded this] have "n dvd k" by simp
  then obtain j where k: "k = n * j" unfolding Rings.dvd_def by auto
  show ?thesis unfolding pi k by auto
qed

definition inv_embed :: "'a :: ufd fract \<Rightarrow> 'a" where
  "inv_embed = the_inv to_fract"

lemma inv_embed[simp]: "inv_embed (to_fract x) = x"
  unfolding inv_embed_def
  by (rule the_inv_f_f, auto simp: inj_on_def)

lemma inv_embed_0[simp]: "inv_embed 0 = 0" unfolding to_fract_0[symmetric] inv_embed by simp

lemma range_to_fract_embed_poly: assumes "set (coeffs p) \<subseteq> range to_fract"
  shows "p = map_poly to_fract (map_poly inv_embed p)"
proof -
  have "p = map_poly (to_fract o inv_embed) p"
    by (rule sym, rule map_poly_idI, insert assms, auto)
  also have "\<dots> = map_poly to_fract (map_poly inv_embed p)" 
    by (subst map_poly_map_poly, auto)
  finally show ?thesis .
qed

lemma content_ff_to_fract_coeffs_to_fract: assumes "content_ff p \<in> range to_fract"
  shows "set (coeffs p) \<subseteq> range to_fract"
proof 
  fix x
  assume "x \<in> set (coeffs p)"
  from content_ff_divides_ff[OF this] assms[unfolded eq_dff_def] show "x \<in> range to_fract"
    unfolding divides_ff_def by (auto simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
qed

lemma content_ff_1_coeffs_to_fract: assumes "content_ff p =dff 1"
  shows "set (coeffs p) \<subseteq> range to_fract"
proof 
  fix x
  assume "x \<in> set (coeffs p)"
  from content_ff_divides_ff[OF this] assms[unfolded eq_dff_def] show "x \<in> range to_fract"
    unfolding divides_ff_def by (auto simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
qed

lemma gauss_lemma:
  fixes p q :: "'a :: ufd fract poly"
  shows "content_ff (p * q) =dff content_ff p * content_ff q"
proof (cases "p = 0 \<or> q = 0")
  case False
  hence p: "p \<noteq> 0" and q: "q \<noteq> 0" by auto
  let ?c = "content_ff :: 'a fract poly \<Rightarrow> 'a fract"
  {
    fix p q :: "'a fract poly"
    assume cp1: "?c p =dff 1" and cq1: "?c q =dff 1"
    define ip where "ip \<equiv> map_poly inv_embed p"
    define iq where "iq \<equiv> map_poly inv_embed q"
    interpret map_poly_hom: map_poly_comm_ring_hom to_fract..
    from content_ff_1_coeffs_to_fract[OF cp1] have cp: "set (coeffs p) \<subseteq> range to_fract" .
    from content_ff_1_coeffs_to_fract[OF cq1] have cq: "set (coeffs q) \<subseteq> range to_fract" .
    have ip: "p = map_poly to_fract ip" unfolding ip_def
      by (rule range_to_fract_embed_poly[OF cp])
    have iq: "q = map_poly to_fract iq" unfolding iq_def
      by (rule range_to_fract_embed_poly[OF cq])
    have cpq0: "?c (p * q) \<noteq> 0"
      unfolding content_ff_0_iff using cp1 cq1 content_ff_eq_dff_nonzero[of _ 1] by auto
    have cpq: "set (coeffs (p * q)) \<subseteq> range to_fract" unfolding ip iq
    unfolding map_poly_hom.hom_mult[symmetric] to_fract_hom.coeffs_map_poly_hom by auto
    have ctnt: "?c (p * q) \<in> range to_fract" using content_ff_to_fract[OF cpq] .
    then obtain cpq where id: "?c (p * q) = to_fract cpq" by auto
    have dvd: "divides_ff 1 (?c (p * q))" using ctnt unfolding divides_ff_def by auto
    from cpq0[unfolded id] have cpq0: "cpq \<noteq> 0" unfolding to_fract_def Zero_fract_def by auto
    hence cpqM: "cpq \<in> carrier mk_monoid" by auto
    have "?c (p * q) =dff 1"
    proof (rule ccontr)
      assume "\<not> ?c (p * q) =dff 1"
      with dvd have "\<not> divides_ff (?c (p * q)) 1"
        unfolding eq_dff_def by auto
      from this[unfolded id divides_ff_def] have cpq: "\<And> r. cpq * r \<noteq> 1" 
        by (auto simp: to_fract_def One_fract_def eq_fract)
      then have cpq1: "\<not> cpq dvd 1" by (auto elim:dvdE simp:ac_simps)
      from mset_factors_exist[OF cpq0 cpq1]
      obtain F where F: "mset_factors F cpq" by auto
      have "F \<noteq> {#}" using F by auto
      then obtain f where f: "f \<in># F" by auto
      with F have irrf: "irreducible f" and f0: "f \<noteq> 0" by (auto dest: mset_factorsD)
      from irrf have pf: "prime_elem f" by simp
      note * = this[unfolded prime_elem_def]
      from * have no_unit: "\<not> f dvd 1" by auto
      from * f0 have prime: "\<And> a b. f dvd a * b \<Longrightarrow> f dvd a \<or> f dvd b" unfolding dvd_def by force
      let ?f = "to_fract f"
      from F f
      have fdvd: "f dvd cpq" by (auto intro:mset_factors_imp_dvd)
      hence "divides_ff ?f (to_fract cpq)" by simp
      from divides_ff_trans[OF this, folded id, OF content_ff_divides_ff] 
      have dvd: "\<And> z. z \<in> set (coeffs (p * q)) \<Longrightarrow> divides_ff ?f z" .
      {
        fix p :: "'a fract poly"
        assume cp: "?c p =dff 1" 
        let ?P = "\<lambda> i. \<not> divides_ff ?f (coeff p i)"
        {
          assume "\<forall> c \<in> set (coeffs p). divides_ff ?f c"           
          hence n: "divides_ff ?f (?c p)" unfolding content_ff_iff by auto
          from divides_ff_trans[OF this] cp[unfolded eq_dff_def] have "divides_ff ?f 1" by auto
          also have "1 = to_fract 1" by simp
          finally have "f dvd 1" by (unfold divides_ff_to_fract)
          hence False using no_unit unfolding dvd_def by (auto simp: ac_simps)
        }
        then obtain cp where cp: "cp \<in> set (coeffs p)" and ncp: "\<not> divides_ff ?f cp" by auto
        hence "cp \<in> range (coeff p)" unfolding range_coeff by auto
        with ncp have "\<exists> i. ?P i" by auto
        from LeastI_ex[OF this] not_less_Least[of _ ?P]
        have "\<exists> i. ?P i \<and> (\<forall> j. j < i \<longrightarrow> divides_ff ?f (coeff p j))" by blast
      } note cont = this
      from cont[OF cp1] obtain r where 
        r: "\<not> divides_ff ?f (coeff p r)" and r': "\<And> i. i < r \<Longrightarrow> divides_ff ?f (coeff p i)" by auto
      have "\<forall> i. \<exists> k. i < r \<longrightarrow> coeff p i = ?f * to_fract k" using divides_ff_coeff[OF cp r'] by blast
      from choice[OF this] obtain rr where r': "\<And> i. i < r \<Longrightarrow> coeff p i = ?f * to_fract (rr i)" by blast
      let ?r = "coeff p r"
      from cont[OF cq1] obtain s where 
        s: "\<not> divides_ff ?f (coeff q s)" and s': "\<And> i. i < s \<Longrightarrow> divides_ff ?f (coeff q i)" by auto
      have "\<forall> i. \<exists> k. i < s \<longrightarrow> coeff q i = ?f * to_fract k" using divides_ff_coeff[OF cq s'] by blast
      from choice[OF this] obtain ss where s': "\<And> i. i < s \<Longrightarrow> coeff q i = ?f * to_fract (ss i)" by blast
      from range_coeffs_to_fract[OF cp] have "\<forall> i. \<exists> m. coeff p i = to_fract m" ..
      from choice[OF this] obtain pi where pi: "\<And> i. coeff p i = to_fract (pi i)" by blast
      from range_coeffs_to_fract[OF cq] have "\<forall> i. \<exists> m. coeff q i = to_fract m" ..
      from choice[OF this] obtain qi where qi: "\<And> i. coeff q i = to_fract (qi i)" by blast
      let ?s = "coeff q s"
      let ?g = "\<lambda> i. coeff p i * coeff q (r + s - i)"
      define a where "a = (\<Sum>i\<in>{..<r}. (rr i * qi (r + s - i)))"
      define b where "b = (\<Sum> i \<in> {Suc r..r + s}. pi i * (ss (r + s - i)))" 
      have "coeff (p * q) (r + s) = (\<Sum>i\<le>r + s. ?g i)" unfolding coeff_mult ..
      also have "{..r+s} = {..< r} \<union> {r .. r+s}" by auto
      also have "(\<Sum>i\<in>{..<r} \<union> {r..r + s}. ?g i)
        = (\<Sum>i\<in>{..<r}. ?g i) + (\<Sum> i \<in> {r..r + s}. ?g i)" 
        by (rule sum.union_disjoint, auto)
      also have "(\<Sum>i\<in>{..<r}. ?g i) = (\<Sum>i\<in>{..<r}. ?f * (to_fract (rr i) * to_fract (qi (r + s - i))))"
        by (rule sum.cong[OF refl], insert r' qi, auto)
      also have "\<dots> = to_fract (f * a)" by (simp add: a_def sum_distrib_left)
      also have "(\<Sum> i \<in> {r..r + s}. ?g i) = ?g r + (\<Sum> i \<in> {Suc r..r + s}. ?g i)"
        by (subst sum.remove[of _ r], auto intro: sum.cong)
      also have "(\<Sum> i \<in> {Suc r..r + s}. ?g i) = (\<Sum> i \<in> {Suc r..r + s}. ?f * (to_fract (pi i) * to_fract (ss (r + s - i))))"
        by (rule sum.cong[OF refl], insert s' pi, auto)
      also have "\<dots> = to_fract (f * b)" by (simp add: sum_distrib_left b_def)
      finally have cpq: "coeff (p * q) (r + s) = to_fract (f * (a + b)) + ?r * ?s" by (simp add: field_simps)
      {
        fix i
        from dvd[of "coeff (p * q) i"] have "divides_ff ?f (coeff (p * q) i)" using range_coeff[of "p * q"] 
          by (cases "coeff (p * q) i = 0", auto simp: divides_ff_def)
      }
      from this[of "r + s", unfolded cpq] have "divides_ff ?f (to_fract (f * (a + b) + pi r * qi s))" 
        unfolding pi qi by simp
      from this[unfolded divides_ff_to_fract] have "f dvd pi r * qi s"
        by (metis dvd_add_times_triv_left_iff mult.commute)
      from prime[OF this] have "f dvd pi r \<or> f dvd qi s" by auto
      with r s show False unfolding pi qi by auto
    qed
  } note main = this
  define n where "n \<equiv> normalize_content_ff :: 'a fract poly \<Rightarrow> 'a fract poly"
  let ?s = "\<lambda> p. smult (content_ff p) (n p)"
  have "?c (p * q) = ?c (?s p * ?s q)" unfolding smult_normalize_content_ff n_def by simp
  also have "?s p * ?s q = smult (?c p * ?c q) (n p * n q)" by (simp add: mult.commute)
  also have "?c (\<dots>) =dff (?c p * ?c q) * ?c (n p * n q)" by (rule content_ff_smult)
  also have "?c (n p * n q) =dff 1" unfolding n_def
    by (rule main, insert p q, auto simp: content_ff_normalize_content_ff_1)
  finally show ?thesis by simp
qed auto

abbreviation (input) "content_ff_ff p \<equiv> content_ff (map_poly to_fract p)"

lemma factorization_to_fract:
  assumes q: "q \<noteq> 0" and factor: "map_poly to_fract (p :: 'a :: ufd poly) = q * r"
  shows "\<exists> q' r' c. c \<noteq> 0 \<and> q = smult c (map_poly to_fract q') \<and>
    r = smult (inverse c) (map_poly to_fract r') \<and>
    content_ff_ff q' =dff 1 \<and> p = q' * r'"
proof -
  let ?c = content_ff
  let ?p = "map_poly to_fract p"
  interpret map_poly_inj_comm_ring_hom "to_fract :: 'a \<Rightarrow> _"..
  define cq where "cq \<equiv> normalize_content_ff q"
  define cr where "cr \<equiv> smult (content_ff q) r"
  define q' where "q' \<equiv> map_poly inv_embed cq"
  define r' where "r' \<equiv> map_poly inv_embed cr"
  from content_ff_map_poly_to_fract have cp_ff: "?c ?p \<in> range to_fract" by auto
  from smult_normalize_content_ff[of q] have cqs: "q = smult (content_ff q) cq" unfolding cq_def ..
  from content_ff_normalize_content_ff_1[OF q] have c_cq: "content_ff cq =dff 1" unfolding cq_def .
  from content_ff_1_coeffs_to_fract[OF this] have cq_ff: "set (coeffs cq) \<subseteq> range to_fract" .
  have factor: "?p = cq * cr" unfolding factor cr_def using cqs
    by (metis mult_smult_left mult_smult_right)
  from gauss_lemma[of cq cr] have cp: "?c ?p =dff ?c cq * ?c cr" unfolding factor .
  with c_cq have "?c ?p =dff ?c cr"
    by (metis eq_dff_mult_right_trans mult.commute mult.right_neutral)
  with cp_ff have "?c cr \<in> range to_fract"
    by (metis divides_ff_def to_fract_hom.hom_mult eq_dff_def image_iff range_eqI)
  from content_ff_to_fract_coeffs_to_fract[OF this] have cr_ff: "set (coeffs cr) \<subseteq> range to_fract" by auto
  have cq: "cq = map_poly to_fract q'" unfolding q'_def
    by (rule range_to_fract_embed_poly[OF cq_ff])
  have cr: "cr = map_poly to_fract r'" unfolding r'_def
    by (rule range_to_fract_embed_poly[OF cr_ff])
  from factor[unfolded cq cr]
  have p: "p = q' * r'" by (simp add: injectivity)
  from c_cq have ctnt: "content_ff_ff q' =dff 1" using cq q'_def by force
  from cqs have idq: "q = smult (?c q) (map_poly to_fract q')" unfolding cq .
  with q have cq: "?c q \<noteq> 0" by auto
  have "r = smult (inverse (?c q)) cr" unfolding cr_def using cq by auto
  also have "cr = map_poly to_fract r'" by (rule cr)
  finally have idr: "r = smult (inverse (?c q)) (map_poly to_fract r')" by auto
  from cq p ctnt idq idr show ?thesis by blast
qed

lemma irreducible_PM_M_PFM:
  assumes irr: "irreducible p"
  shows "degree p = 0 \<and> irreducible (coeff p 0) \<or> 
  degree p \<noteq> 0 \<and> irreducible (map_poly to_fract p) \<and> content_ff_ff p =dff 1"
proof-
  interpret map_poly_inj_idom_hom to_fract..
  from irr[unfolded irreducible_altdef]
  have p0: "p \<noteq> 0" and irr: "\<not> p dvd 1" "\<And> b. b dvd p \<Longrightarrow> \<not> p dvd b \<Longrightarrow> b dvd 1" by auto
  show ?thesis
  proof (cases "degree p = 0")
    case True
    from degree0_coeffs[OF True] obtain a where p: "p = [:a:]" by auto
    note irr = irr[unfolded p]
    from p p0 have a0: "a \<noteq> 0" by auto
    moreover have "\<not> a dvd 1" using irr(1) by simp
    moreover {
      fix b
      assume "b dvd a" "\<not> a dvd b"
      hence "[:b:] dvd [:a:]" "\<not> [:a:] dvd [:b:]" unfolding const_poly_dvd .
      from irr(2)[OF this] have "b dvd 1" unfolding const_poly_dvd_1 .
    }
    ultimately have "irreducible a" unfolding irreducible_altdef by auto
    with True show ?thesis unfolding p by auto
  next
    case False
    let ?E = "map_poly to_fract"
    let ?p = "?E p"
    have dp: "degree ?p \<noteq> 0" using False by simp
    from p0 have p': "?p \<noteq> 0" by simp
    moreover have "\<not> ?p dvd 1" 
      proof
        assume "?p dvd 1" then obtain q where id: "?p * q = 1" unfolding dvd_def by auto
        have deg: "degree (?p * q) = degree ?p + degree q"
          by (rule degree_mult_eq, insert id, auto)
        from arg_cong[OF id, of degree, unfolded deg] dp show False by auto
      qed
    moreover {
      fix q
      assume "q dvd ?p" and ndvd: "\<not> ?p dvd q"
      then obtain r where fact: "?p = q * r" unfolding dvd_def by auto
      with p' have q0: "q \<noteq> 0" by auto
      from factorization_to_fract[OF this fact] obtain q' r' c where *: "c \<noteq> 0" "q = smult c (?E q')"
        "r = smult (inverse c) (?E r')" "content_ff_ff q' =dff 1"
        "p = q' * r'" by auto
      hence "q' dvd p" unfolding dvd_def by auto
      note irr = irr(2)[OF this]
      have "\<not> p dvd q'"
      proof
        assume "p dvd q'"
        then obtain u where q': "q' = p * u" unfolding dvd_def by auto
        from arg_cong[OF this, of "\<lambda> x. smult c (?E x)", unfolded *(2)[symmetric]]
        have "q = ?p * smult c (?E u)" by simp
        hence "?p dvd q" unfolding dvd_def by blast
        with ndvd show False ..
      qed
      from irr[OF this] have "q' dvd 1" .
      from divides_degree[OF this] have "degree q' = 0" by auto
      from degree0_coeffs[OF this] obtain a' where "q' = [:a':]" by auto
      from *(2)[unfolded this] obtain a where q: "q = [:a:]"
        by (simp add: to_fract_hom.map_poly_pCons_hom)
      with q0 have a: "a \<noteq> 0" by auto
      have "q dvd 1" unfolding q const_poly_dvd_1 using a unfolding dvd_def
        by (intro exI[of _ "inverse a"], auto)
    }
    ultimately have irr_p': "irreducible ?p" unfolding irreducible_altdef by auto
    let ?c = "content_ff"
    have "?c ?p \<in> range to_fract"
      by (rule content_ff_to_fract, unfold to_fract_hom.coeffs_map_poly_hom, auto)
    then obtain c where cp: "?c ?p = to_fract c" by auto
    from p' cp have c: "c \<noteq> 0" by auto
    have "?c ?p =dff 1" unfolding cp
    proof (rule ccontr)
      define cp where "cp = normalize_content_ff ?p"
      from smult_normalize_content_ff[of ?p] have cps: "?p = smult (to_fract c) cp" unfolding cp_def cp ..
      from content_ff_normalize_content_ff_1[OF p'] have c_cp: "content_ff cp =dff 1" unfolding cp_def .
      from range_to_fract_embed_poly[OF content_ff_1_coeffs_to_fract[OF c_cp]] obtain cp' where "cp = ?E cp'" by auto
      from cps[unfolded this] have "p = smult c cp'" by (simp add: injectivity)
      hence dvd: "[: c :] dvd p" unfolding dvd_def by auto
      have "\<not> p dvd [: c :]" using divides_degree[of p "[: c :]"] c False by auto
      from irr(2)[OF dvd this] have "c dvd 1" by simp
      assume "\<not> to_fract c =dff 1"
      from this[unfolded eq_dff_def One_fract_def to_fract_def[symmetric] divides_ff_def to_fract_mult]
      have c1: "\<And> r. 1 \<noteq> c * r" by (auto simp: ac_simps simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
      with \<open>c dvd 1\<close> show False unfolding dvd_def by blast
    qed
    with False irr_p' show ?thesis by auto
  qed
qed

lemma irreducible_M_PM:
  fixes p :: "'a :: ufd poly" assumes 0: "degree p = 0" and irr: "irreducible (coeff p 0)"
  shows "irreducible p"
proof (cases "p = 0")
  case True
  thus ?thesis using assms by auto
next
  case False
  from degree0_coeffs[OF 0] obtain a where p: "p = [:a:]" by auto
  with False have a0: "a \<noteq> 0" by auto
  from p irr have "irreducible a" by auto
  from this[unfolded irreducible_altdef]
  have a1: "\<not> a dvd 1" and irr: "\<And> b. b dvd a \<Longrightarrow> \<not> a dvd b \<Longrightarrow> b dvd 1" by auto
  { 
    fix b
    assume *: "b dvd [:a:]" "\<not> [:a:] dvd b"
    from divides_degree[OF this(1)] a0 have "degree b = 0" by auto
    from degree0_coeffs[OF this] obtain bb where b: "b = [: bb :]" by auto
    from * irr[of bb] have "b dvd 1" unfolding b const_poly_dvd by auto
  }
  with a0 a1 show ?thesis by (auto simp: irreducible_altdef p)
qed

lemma primitive_irreducible_imp_degree:
 "primitive (p::'a::{semiring_gcd,idom} poly) \<Longrightarrow> irreducible p \<Longrightarrow> degree p > 0"
  by (unfold irreducible_primitive_connect[symmetric], auto)

lemma irreducible_degree_field:
  fixes p :: "'a :: field poly" assumes "irreducible p"
  shows "degree p > 0"
proof-
  {
    assume "degree p = 0"
    from degree0_coeffs[OF this] assms obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
    hence "1 = p * [:inverse a:]" by auto
    hence "p dvd 1" ..
    hence "p \<in> Units mk_monoid" by simp
    with assms have False unfolding irreducible_def by auto
  } then show ?thesis by auto
qed

lemma irreducible_PFM_PM: assumes
  irr: "irreducible (map_poly to_fract p)" and ct: "content_ff_ff p =dff 1"
  shows "irreducible p"
proof -
  let ?E = "map_poly to_fract"
  let ?p = "?E p"
  from ct have p0: "p \<noteq> 0" by (auto simp: eq_dff_def divides_ff_def)
  moreover
    from irreducible_degree_field[OF irr] have deg: "degree p \<noteq> 0" by simp
    from irr[unfolded irreducible_altdef]
    have irr: "\<And> b. b dvd ?p \<Longrightarrow> \<not> ?p dvd b \<Longrightarrow> b dvd 1" by auto
    have "\<not> p dvd 1" using deg divides_degree[of p 1] by auto
  moreover {
    fix q :: "'a poly"
    assume dvd: "q dvd p" and ndvd: "\<not> p dvd q"
    from dvd obtain r where pqr: "p = q * r" ..
    from arg_cong[OF this, of ?E] have pqr': "?p = ?E q * ?E r" by simp
    from p0 pqr have q: "q \<noteq> 0" and r: "r \<noteq> 0" by auto
    have dp: "degree p = degree q + degree r" unfolding pqr
      by (subst degree_mult_eq, insert q r, auto)
    from eq_dff_trans[OF eq_dff_sym[OF gauss_lemma[of "?E q" "?E r", folded pqr']] ct]
    have ct: "content_ff (?E q) * content_ff (?E r) =dff 1" .
    from content_ff_map_poly_to_fract obtain cq where cq: "content_ff (?E q) = to_fract cq" by auto
    from content_ff_map_poly_to_fract obtain cr where cr: "content_ff (?E r) = to_fract cr" by auto
    note ct[unfolded cq cr to_fract_mult eq_dff_def divides_ff_def]
    from this[folded hom_distribs]
    obtain c where c: "cq * cr * c = 1" by (auto simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
    hence one: "1 = cq * (c * cr)" "1 = cr * (c * cq)" by (auto simp: ac_simps)
    {
      assume *: "degree q \<noteq> 0 \<and> degree r \<noteq> 0"
      with dp have "degree q < degree p" by auto
      hence "degree (?E q) < degree (?E p)" by simp
      hence ndvd: "\<not> ?p dvd ?E q" using divides_degree[of ?p "?E q"] q by auto
      have "?E q dvd ?p" unfolding pqr' by auto
      from irr[OF this ndvd] have "?E q dvd 1" .
      from divides_degree[OF this] * have False by auto
    }
    hence "degree q = 0 \<or> degree r = 0" by blast
    then have "q dvd 1" 
    proof
      assume "degree q = 0"
      from degree0_coeffs[OF this] q obtain a where q: "q = [:a:]" and a: "a \<noteq> 0" by auto
      hence id: "set (coeffs (?E q)) = {to_fract a}" by auto
      have "divides_ff (to_fract a) (content_ff (?E q))" unfolding content_ff_iff id by auto
      from this[unfolded cq divides_ff_def, folded hom_distribs]
      obtain rr where cq: "cq = a * rr" by (auto simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
      with one(1) have "1 = a * (rr * c * cr)" by (auto simp: ac_simps)
      hence "a dvd 1" ..
      thus ?thesis by (simp add: q)
    next
      assume "degree r = 0"
      from degree0_coeffs[OF this] r obtain a where r: "r = [:a:]" and a: "a \<noteq> 0" by auto
      hence id: "set (coeffs (?E r)) = {to_fract a}" by auto
      have "divides_ff (to_fract a) (content_ff (?E r))" unfolding content_ff_iff id by auto
      note this[unfolded cr divides_ff_def to_fract_mult]
      note this[folded hom_distribs]
      then obtain rr where cr: "cr = a * rr" by (auto simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
      with one(2) have one: "1 = a * (rr * c * cq)" by (auto simp: ac_simps)
      from arg_cong[OF pqr[unfolded r], of "\<lambda> p. p * [:rr * c * cq:]"]
      have "p * [:rr * c * cq:] = q * [:a * (rr * c * cq):]" by (simp add: ac_simps)
      also have "\<dots> = q" unfolding one[symmetric] by auto
      finally obtain r where "q = p * r" by blast
      hence "p dvd q" ..
      with ndvd show ?thesis by auto
    qed
  }
  ultimately show ?thesis by (auto simp:irreducible_altdef)
qed

lemma irreducible_cases: "irreducible p \<longleftrightarrow>
  degree p = 0 \<and> irreducible (coeff p 0) \<or> 
  degree p \<noteq> 0 \<and> irreducible (map_poly to_fract p) \<and> content_ff_ff p =dff 1"
  using irreducible_PM_M_PFM irreducible_M_PM irreducible_PFM_PM
  by blast

lemma dvd_PM_iff: "p dvd q \<longleftrightarrow> divides_ff (content_ff_ff p) (content_ff_ff q) \<and> 
  map_poly to_fract p dvd map_poly to_fract q"
proof -
  interpret map_poly_inj_idom_hom to_fract..
  let ?E = "map_poly to_fract"
  show ?thesis (is "?l = ?r")
  proof
    assume "p dvd q"
    then obtain r where qpr: "q = p * r" ..
    from arg_cong[OF this, of ?E]
    have dvd: "?E p dvd ?E q" by auto
    from content_ff_map_poly_to_fract obtain cq where cq: "content_ff_ff q = to_fract cq" by auto
    from content_ff_map_poly_to_fract obtain cp where cp: "content_ff_ff p = to_fract cp" by auto
    from content_ff_map_poly_to_fract obtain cr where cr: "content_ff_ff r = to_fract cr" by auto
    from gauss_lemma[of "?E p" "?E r", folded hom_distribs qpr, unfolded cq cp cr]
    have "divides_ff (content_ff_ff p) (content_ff_ff q)" unfolding cq cp eq_dff_def
      by (metis divides_ff_def divides_ff_trans)
    with dvd show ?r by blast
  next
    assume ?r
    show ?l 
    proof (cases "q = 0")
      case True
      with \<open>?r\<close> show ?l by auto
    next
      case False note q = this
      hence q': "?E q \<noteq> 0" by auto
      from \<open>?r\<close> obtain rr where qpr: "?E q = ?E p * rr" unfolding dvd_def by auto
      with q have p: "p \<noteq> 0" and Ep: "?E p \<noteq> 0" and rr: "rr \<noteq> 0" by auto
      from gauss_lemma[of "?E p" rr, folded qpr] 
      have ct: "content_ff_ff q =dff content_ff_ff p * content_ff rr"
        by auto
      from content_ff_map_poly_to_fract[of p] obtain cp where cp: "content_ff_ff p = to_fract cp" by auto
      from content_ff_map_poly_to_fract[of q] obtain cq where cq: "content_ff_ff q = to_fract cq" by auto
      from \<open>?r\<close>[unfolded cp cq] have "divides_ff (to_fract cp) (to_fract cq)" ..
      with ct[unfolded cp cq eq_dff_def] have "content_ff rr \<in> range to_fract"
        by (metis (no_types, lifting) Ep content_ff_0_iff cp divides_ff_def 
          divides_ff_trans mult.commute mult_right_cancel range_eqI)
      from range_to_fract_embed_poly[OF content_ff_to_fract_coeffs_to_fract[OF this]] obtain r
        where rr: "rr = ?E r" by auto
      from qpr[unfolded rr, folded hom_distribs]
      have "q = p * r" by (rule injectivity)
      thus "p dvd q" ..
    qed
  qed
qed

lemma factorial_monoid_poly: "factorial_monoid (mk_monoid :: 'a :: ufd poly monoid)"
proof (fold factorial_condition_one, intro conjI)
  interpret M: factorial_monoid "mk_monoid :: 'a monoid" by (fact factorial_monoid)
  interpret PFM: factorial_monoid "mk_monoid :: 'a fract poly monoid" 
    by (rule as_ufd.factorial_monoid)
  interpret PM: comm_monoid_cancel "mk_monoid :: 'a poly monoid" by (unfold_locales, auto)
  let ?E = "map_poly to_fract"
  show "divisor_chain_condition_monoid (mk_monoid::'a poly monoid)"
  proof (unfold_locales, unfold mk_monoid_simps)
    let ?rel' = "{(x::'a poly, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> properfactor x y}"
    let ?rel'' = "{(x::'a, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> properfactor x y}"
    let ?relPM = "{(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> x dvd y \<and> \<not> y dvd (x :: 'a poly)}"
    let ?relM = "{(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> x dvd y \<and> \<not> y dvd (x :: 'a)}"
    have id: "?rel' = ?relPM" using properfactor_nz by auto
    have id': "?rel'' = ?relM" using properfactor_nz by auto
    have "wf ?rel''" using M.division_wellfounded by auto
    hence wfM: "wf ?relM" using id' by auto
    let ?c = "\<lambda> p. inv_embed (content_ff_ff p)"
    let ?f = "\<lambda> p. (degree p, ?c p)"
    note wf = wf_inv_image[OF wf_lex_prod[OF wf_less wfM], of ?f]
    show "wf ?rel'" unfolding id
    proof (rule wf_subset[OF wf], clarify)
      fix p q :: "'a poly"
      assume p: "p \<noteq> 0" and q: "q \<noteq> 0" and dvd: "p dvd q" and ndvd: "\<not> q dvd p"
      from dvd obtain r where qpr: "q = p * r" ..
      from degree_mult_eq[of p r, folded qpr] q qpr have r: "r \<noteq> 0" 
        and deg: "degree q = degree p + degree r" by auto
      show "(p,q) \<in> inv_image ({(x, y). x < y} <*lex*> ?relM) ?f"
      proof (cases "degree p = degree q")
        case False
        with deg have "degree p < degree q" by auto
        thus ?thesis by auto
      next
        case True
        with deg have "degree r = 0" by simp
        from degree0_coeffs[OF this] r obtain a where ra: "r = [:a:]" and a: "a \<noteq> 0" by auto
        from arg_cong[OF qpr, of "\<lambda> p. ?E p * [:inverse (to_fract a):]"] a
        have "?E p = ?E q * [:inverse (to_fract a):]"
          by (auto simp: ac_simps ra)
        hence "?E q dvd ?E p" ..
        with ndvd dvd_PM_iff have ndvd: "\<not> divides_ff (content_ff_ff q) (content_ff_ff p)" by auto
        from content_ff_map_poly_to_fract obtain cq where cq: "content_ff_ff q = to_fract cq" by auto
        from content_ff_map_poly_to_fract obtain cp where cp: "content_ff_ff p = to_fract cp" by auto
        from ndvd[unfolded cp cq] have ndvd: "\<not> cq dvd cp" by simp
        from iffD1[OF dvd_PM_iff,OF dvd,unfolded cq cp]
        have dvd: "cp dvd cq" by simp
        have c_p: "?c p = cp" unfolding cp by simp
        have c_q: "?c q = cq" unfolding cq by simp
        from q cq have cq0: "cq \<noteq> 0" by auto
        from p cp have cp0: "cp \<noteq> 0" by auto
        from ndvd cq0 cp0 dvd have "(?c p, ?c q) \<in> ?relM" unfolding c_p c_q by auto
        with True show ?thesis by auto
      qed
    qed
  qed
  show "primeness_condition_monoid (mk_monoid::'a poly monoid)"
  proof (unfold_locales, unfold mk_monoid_simps)
    fix p :: "'a poly"
    assume p: "p \<noteq> 0" and "irred p"
    then have irr: "irreducible p" by auto
    from p have p': "?E p \<noteq> 0" by auto
    from irreducible_PM_M_PFM[OF irr] have choice: "degree p = 0 \<and> irred (coeff p 0)
      \<or> degree p \<noteq> 0 \<and> irred (?E p) \<and> content_ff_ff p =dff 1" by auto
    show "Divisibility.prime mk_monoid p"
    proof (rule Divisibility.primeI, unfold mk_monoid_simps mem_Units)
      show "\<not> p dvd 1"
      proof
        assume "p dvd 1"
        from divides_degree[OF this] have dp: "degree p = 0" by auto
        from degree0_coeffs[OF this] p obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
        with choice have irr: "irreducible a" by auto
        from \<open>p dvd 1\<close>[unfolded p] have "a dvd 1" by auto
        with irr show False unfolding irreducible_def by auto
      qed
      fix q r :: "'a poly"
      assume q: "q \<noteq> 0" and r: "r \<noteq> 0" and "factor p (q * r)"
      from this[unfolded factor_idom] have "p dvd q * r" by auto
      from iffD1[OF dvd_PM_iff this] have dvd_ct: "divides_ff (content_ff_ff p) (content_ff (?E (q * r)))"
        and dvd_E: "?E p dvd ?E q * ?E r" by auto
      from gauss_lemma[of "?E q" "?E r"] divides_ff_trans[OF dvd_ct, of "content_ff_ff q * content_ff_ff r"]
      have dvd_ct: "divides_ff (content_ff_ff p) (content_ff_ff q * content_ff_ff r)"
        unfolding eq_dff_def by auto
      from choice
      have "p dvd q \<or> p dvd r"
      proof
        assume "degree p \<noteq> 0 \<and> irred (?E p) \<and> content_ff_ff p =dff 1"
        hence deg: "degree p \<noteq> 0" and irr: "irred (?E p)" and ct: "content_ff_ff p =dff 1" by auto
        from PFM.irreducible_prime[OF irr] p have prime: "Divisibility.prime mk_monoid (?E p)" by auto
        from q r have Eq: "?E q \<in> carrier mk_monoid" and Er: "?E r \<in> carrier mk_monoid" 
          and q': "?E q \<noteq> 0" and r': "?E r \<noteq> 0" and qr': "?E q * ?E r \<noteq> 0" by auto
        from PFM.prime_divides[OF Eq Er prime] q' r' qr' dvd_E
        have dvd_E: "?E p dvd ?E q \<or> ?E p dvd ?E r" by simp
        from ct have ct: "divides_ff (content_ff_ff p) 1" unfolding eq_dff_def by auto
        moreover have "\<And> q. divides_ff 1 (content_ff_ff q)" using content_ff_map_poly_to_fract
          unfolding divides_ff_def by auto
        from divides_ff_trans[OF ct this] have ct: "\<And> q. divides_ff (content_ff_ff p) (content_ff_ff q)" .
        with dvd_E show ?thesis using dvd_PM_iff by blast
      next
        assume "degree p = 0 \<and> irred (coeff p 0)"
        hence deg: "degree p = 0" and irr: "irred (coeff p 0)" by auto
        from degree0_coeffs[OF deg] p obtain a where p: "p = [:a:]" and a: "a \<noteq> 0" by auto
        with irr have irr: "irred a" and aM: "a \<in> carrier mk_monoid" by auto
        from M.irreducible_prime[OF irr aM] have prime: "Divisibility.prime mk_monoid a" .
        from content_ff_map_poly_to_fract obtain cq where cq: "content_ff_ff q = to_fract cq" by auto
        from content_ff_map_poly_to_fract obtain cp where cp: "content_ff_ff p = to_fract cp" by auto
        from content_ff_map_poly_to_fract obtain cr where cr: "content_ff_ff r = to_fract cr" by auto
        have "divides_ff (to_fract a) (content_ff_ff p)" unfolding p content_ff_iff using a by auto
        from divides_ff_trans[OF this[unfolded cp] dvd_ct[unfolded cp cq cr]]
        have "divides_ff (to_fract a) (to_fract (cq * cr))" by simp
        hence dvd: "a dvd cq * cr" by (auto simp add: divides_ff_def simp del: to_fract_hom.hom_mult simp: to_fract_hom.hom_mult[symmetric])
        from content_ff_divides_ff[of "to_fract a" "?E p"] have "divides_ff (to_fract cp) (to_fract a)"
          using cp a p by auto
        hence cpa: "cp dvd a" by simp
        from a q r cq cr have aM: "a \<in> carrier mk_monoid" and qM: "cq \<in> carrier mk_monoid" and rM: "cr \<in> carrier mk_monoid"
          and q': "cq \<noteq> 0" and r': "cr \<noteq> 0" and qr': "cq * cr \<noteq> 0" 
          by auto
        from M.prime_divides[OF qM rM prime] q' r' qr' dvd
        have "a dvd cq \<or> a dvd cr" by simp
        with dvd_trans[OF cpa] have dvd: "cp dvd cq \<or> cp dvd cr" by auto
        have "\<And> q. ?E p * (smult (inverse (to_fract a)) q) = q" unfolding p using a by (auto simp: one_poly_def)
        hence Edvd: "\<And> q. ?E p dvd q" unfolding dvd_def by metis
        from dvd Edvd show ?thesis apply (subst(1 2) dvd_PM_iff) unfolding cp cq cr by auto
      qed
      thus "factor p q \<or> factor p r" unfolding factor_idom using p q r by auto
    qed
  qed
qed

instance poly :: (ufd) ufd
  by (intro class.ufd.of_class.intro factorial_monoid_imp_ufd factorial_monoid_poly)


lemma primitive_iff_some_content_dvd_1:
  fixes f :: "'a :: ufd poly" (* gcd_condition suffices... *)
  shows "primitive f \<longleftrightarrow> some_gcd.listgcd (coeffs f) dvd 1" (is "_ \<longleftrightarrow> ?c dvd 1")
proof(intro iffI primitiveI)
  fix x
  assume "(\<And>y. y \<in> set (coeffs f) \<Longrightarrow> x dvd y)"
  from some_gcd.listgcd_greatest[of "coeffs f", OF this]
  have "x dvd ?c" by simp
  also assume "?c dvd 1"
  finally show "x dvd 1".
next
  assume "primitive f"
  from primitiveD[OF this some_gcd.listgcd[of _ "coeffs f"]]
  show "?c dvd 1" by auto
qed

end
