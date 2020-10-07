(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Result is Unique\<close>

text \<open>We combine the finite field factorization algorithm with Hensel-lifting to
  obtain factorizations mod $p^n$. Moreover, we prove results on unique-factorizations
  in mod $p^n$ which admit to extend the uniqueness result for binary Hensel-lifting
  to the general case. As a consequence, our factorization algorithm will produce
  unique factorizations mod $p^n$.\<close> 

theory Berlekamp_Hensel
imports 
  Finite_Field_Factorization_Record_Based
  Hensel_Lifting
begin

hide_const coeff monom

definition berlekamp_hensel :: "int \<Rightarrow> nat \<Rightarrow> int poly \<Rightarrow> int poly list" where
  "berlekamp_hensel p n f = (case finite_field_factorization_int p f of
    (_,fs) \<Rightarrow> hensel_lifting p n f fs)"

text \<open>Finite field factorization in combination with Hensel-lifting delivers 
  factorization modulo $p^k$ where factors are irreducible modulo $p$.
  Assumptions: input polynomial is square-free modulo $p$.\<close>

context poly_mod_prime begin

lemma berlekamp_hensel_main:
  assumes n: "n \<noteq> 0"
    and res: "berlekamp_hensel p n f = gs" 
    and cop: "coprime (lead_coeff f) p" 
    and sf: "square_free_m f" 
    and berl: "finite_field_factorization_int p f = (c,fs)" 
  shows "poly_mod.factorization_m (p ^ n) f (lead_coeff f, mset gs) \<comment> \<open>factorization mod \<open>p^n\<close>\<close>"
    and "sort (map degree fs) = sort (map degree gs)"
    and "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and>  \<comment> \<open>monic and normalized\<close>
        poly_mod.irreducible_m p g \<and> \<comment> \<open>irreducibility even mod \<open>p\<close>\<close>
        poly_mod.degree_m p g = degree g  \<comment> \<open>mod \<open>p\<close> does not change degree of \<open>g\<close>\<close>"
proof -
  from res[unfolded berlekamp_hensel_def berl split] 
  have hen: "hensel_lifting p n f fs = gs" .
  note bh = finite_field_factorization_int[OF sf berl]
  from bh have "poly_mod.factorization_m p f (c, mset fs)" "c \<in> {0..<p}" "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})" 
    by (auto simp: poly_mod.unique_factorization_m_alt_def)
  note hen = hensel_lifting[OF n hen cop sf, OF this]
  show "poly_mod.factorization_m (p ^ n) f (lead_coeff f, mset gs)" 
    "sort (map degree fs) = sort (map degree gs)"
    "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and>  
      poly_mod.irreducible_m p g \<and> 
      poly_mod.degree_m p g = degree g" using hen by auto
qed

theorem berlekamp_hensel:
  assumes cop: "coprime (lead_coeff f) p"
    and sf: "square_free_m f"
    and res: "berlekamp_hensel p n f = gs"
    and n: "n \<noteq> 0"
  shows "poly_mod.factorization_m (p^n) f (lead_coeff f, mset gs) \<comment> \<open>factorization mod \<open>p^n\<close>\<close>"
    and "\<And> g. g \<in> set gs \<Longrightarrow> poly_mod.Mp (p^n) g = g \<and> poly_mod.irreducible_m p g
      \<comment> \<open>normalized and \<open>irreducible\<close> even mod \<open>p\<close>\<close>"
proof -
  obtain c fs where "finite_field_factorization_int p f = (c,fs)" by force
  from berlekamp_hensel_main[OF n res cop sf this]
  show "poly_mod.factorization_m (p^n) f (lead_coeff f, mset gs)" 
    "\<And> g. g \<in> set gs \<Longrightarrow> poly_mod.Mp (p^n) g = g \<and> poly_mod.irreducible_m p g" by auto
qed

lemma berlekamp_and_hensel_separated:
  assumes cop: "coprime (lead_coeff f) p"
    and sf: "square_free_m f"
    and res: "hensel_lifting p n f fs = gs"
    and berl: "finite_field_factorization_int p f = (c,fs)"
    and n: "n \<noteq> 0"
  shows "berlekamp_hensel p n f = gs"
    and "sort (map degree fs) = sort (map degree gs)"
proof -
  show "berlekamp_hensel p n f = gs" unfolding res[symmetric]
    berlekamp_hensel_def hensel_lifting_def berl split Let_def ..
  from berlekamp_hensel_main[OF n this cop sf berl] show "sort (map degree fs) = sort (map degree gs)"
    by auto 
qed

end

lemma prime_cop_exp_poly_mod:
  assumes prime: "prime p" and cop: "coprime c p" and n: "n \<noteq> 0"
  shows "poly_mod.M (p^n) c \<in> {1 ..< p^n}"
proof -
  from prime have p1: "p > 1" by (simp add: prime_int_iff)
  interpret poly_mod_2 "p^n" unfolding poly_mod_2_def using p1 n by simp
  from cop p1 m1 have "M c \<noteq> 0"
    by (auto simp add: M_def)
  moreover have "M c < p^n" "M c \<ge> 0" unfolding M_def using m1 by auto
  ultimately show ?thesis by auto
qed

context poly_mod_2
begin

context
  fixes p :: int
  assumes prime: "prime p"
begin

interpretation p: poly_mod_prime p using prime by unfold_locales

lemma coprime_lead_coeff_factor: assumes "coprime (lead_coeff (f * g)) p"
  shows "coprime (lead_coeff f) p" "coprime (lead_coeff g) p" 
proof -
  {
    fix f g 
    assume cop: "coprime (lead_coeff (f * g)) p" 
    from this[unfolded lead_coeff_mult]
    have "coprime (lead_coeff f) p" using prime
      by simp
  }
  from this[OF assms] this[of g f] assms
  show "coprime (lead_coeff f) p" "coprime (lead_coeff g) p" by (auto simp: ac_simps)
qed

lemma unique_factorization_m_factor: assumes uf: "unique_factorization_m (f * g) (c,hs)"
  and cop: "coprime (lead_coeff (f * g)) p"  
  and sf: "p.square_free_m (f * g)" 
  and n: "n \<noteq> 0" 
  and m: "m = p^n" 
  shows "\<exists> fs gs. unique_factorization_m f (lead_coeff f,fs) 
  \<and> unique_factorization_m g (lead_coeff g,gs) 
  \<and> Mf (c,hs) = Mf (lead_coeff f * lead_coeff g, fs + gs)
  \<and> image_mset Mp fs = fs \<and> image_mset Mp gs = gs"
proof -
  from prime have p1: "1 < p" by (simp add: prime_int_iff)
  interpret p: poly_mod_2 p by (standard, rule p1)
  note sf = p.square_free_m_factor[OF sf]
  note cop = coprime_lead_coeff_factor[OF cop]
  from cop have copm: "coprime (lead_coeff f) m" "coprime (lead_coeff g) m" 
    by (simp_all add: m)
  have df: "degree_m f = degree f" 
    by (rule degree_m_eq[OF _ m1], insert copm(1) m1, auto)  
  have dg: "degree_m g = degree g" 
    by (rule degree_m_eq[OF _ m1], insert copm(2) m1, auto)  
  define fs where "fs \<equiv> mset (berlekamp_hensel p n f)"
  define gs where "gs \<equiv> mset (berlekamp_hensel p n g)"
  from p.berlekamp_hensel[OF cop(1) sf(1) refl n, folded m]
  have f: "factorization_m f (lead_coeff f,fs)" 
    and f_id: "\<And> f. f \<in># fs \<Longrightarrow> Mp f = f" unfolding fs_def by auto
  from p.berlekamp_hensel[OF cop(2) sf(2) refl n, folded m]
  have g: "factorization_m g (lead_coeff g,gs)" 
    and g_id: "\<And> f. f \<in># gs \<Longrightarrow> Mp f = f" unfolding gs_def by auto
  from factorization_m_prod[OF f g] uf[unfolded unique_factorization_m_alt_def]
  have eq: "Mf (lead_coeff f * lead_coeff g, fs + gs) = Mf (c,hs)" by blast
  have uff: "unique_factorization_m f (lead_coeff f,fs)" 
  proof (rule unique_factorization_mI[OF f])
    fix e ks
    assume "factorization_m f (e,ks)" 
    from factorization_m_prod[OF this g] uf[unfolded unique_factorization_m_alt_def]
      factorization_m_lead_coeff[OF this, unfolded degree_m_eq_lead_coeff[OF df]]
    have "Mf (e * lead_coeff g, ks + gs) = Mf (c,hs)" and e: "M (lead_coeff f) = M e" by blast+
    from this[folded eq, unfolded Mf_def split] 
    have ks: "image_mset Mp ks = image_mset Mp fs" by auto
    show "Mf (e, ks) = Mf (lead_coeff f, fs)" unfolding Mf_def split ks e by simp
  qed
  have idf: "image_mset Mp fs = fs" using f_id by (induct fs, auto)
  have idg: "image_mset Mp gs = gs" using g_id by (induct gs, auto)
  have ufg: "unique_factorization_m g (lead_coeff g,gs)" 
  proof (rule unique_factorization_mI[OF g])
    fix e ks
    assume "factorization_m g (e,ks)" 
    from factorization_m_prod[OF f this] uf[unfolded unique_factorization_m_alt_def]
      factorization_m_lead_coeff[OF this, unfolded degree_m_eq_lead_coeff[OF dg]]
    have "Mf (lead_coeff f * e, fs + ks) = Mf (c,hs)" and e: "M (lead_coeff g) = M e" by blast+
    from this[folded eq, unfolded Mf_def split] 
    have ks: "image_mset Mp ks = image_mset Mp gs" by auto
    show "Mf (e, ks) = Mf (lead_coeff g, gs)" unfolding Mf_def split ks e by simp
  qed
  from uff ufg eq[symmetric] idf idg show ?thesis by auto
qed

lemma unique_factorization_factorI:
  assumes ufact: "unique_factorization_m (f * g) FG"
    and cop: "coprime (lead_coeff (f * g)) p"
    and sf: "poly_mod.square_free_m p (f * g)"
    and n: "n \<noteq> 0" 
    and m: "m = p^n" 
  shows "factorization_m f F \<Longrightarrow> unique_factorization_m f F"
    and "factorization_m g G \<Longrightarrow> unique_factorization_m g G"
proof -
  obtain c fg where FG: "FG = (c,fg)" by force
  from unique_factorization_m_factor[OF ufact[unfolded FG] cop sf n m]
  obtain fs gs where ufact: "unique_factorization_m f (lead_coeff f, fs)" 
    "unique_factorization_m g (lead_coeff g, gs)" by auto
  from ufact(1) show "factorization_m f F \<Longrightarrow> unique_factorization_m f F"
    by (metis unique_factorization_m_alt_def)
  from ufact(2) show "factorization_m g G \<Longrightarrow> unique_factorization_m g G"
    by (metis unique_factorization_m_alt_def)
qed

end

lemma monic_Mp_prod_mset: assumes fs: "\<And> f. f \<in># fs \<Longrightarrow> monic (Mp f)" 
  shows "monic (Mp (prod_mset fs))"
proof -
  have "monic (prod_mset (image_mset Mp fs))"
    by (rule monic_prod_mset, insert fs, auto)
  from monic_Mp[OF this] have "monic (Mp (prod_mset (image_mset Mp fs)))" .
  also have "Mp (prod_mset (image_mset Mp fs)) = Mp (prod_mset fs)" by (rule Mp_prod_mset)
  finally show ?thesis .
qed

lemma degree_Mp_mult_monic: assumes "monic f" "monic g"
  shows "degree (Mp (f * g)) = degree f + degree g"
  by (metis zero_neq_one assms degree_monic_mult leading_coeff_0_iff monic_degree_m monic_mult)
  
lemma factorization_m_degree: assumes "factorization_m f (c,fs)" 
  and 0: "Mp f \<noteq> 0" 
  shows "degree_m f = sum_mset (image_mset degree_m fs)" 
proof -
  note a = assms[unfolded factorization_m_def split] 
  hence deg: "degree_m f = degree_m (smult c (prod_mset fs))" 
    and fs: "\<And> f. f \<in># fs \<Longrightarrow> monic (Mp f)" by auto
  define gs where "gs \<equiv> Mp (prod_mset fs)" 
  from monic_Mp_prod_mset[OF fs] have mon_gs: "monic gs" unfolding gs_def .
  have d:"degree (Mp (Polynomial.smult c gs)) = degree gs"
  proof -
    have f1: "0 \<noteq> c" by (metis "0" Mp_0 a(1) smult_eq_0_iff)
    then have "M c \<noteq> 0" by (metis (no_types) "0" assms(1) factorization_m_lead_coeff leading_coeff_0_iff)
    then show "degree (Mp (Polynomial.smult c gs)) = degree gs"
      unfolding monic_degree_m[OF mon_gs,symmetric]
      using f1 by (metis coeff_smult degree_m_eq degree_smult_eq m1 mon_gs monic_degree_m mult_cancel_left1 poly_mod.M_def)
  qed
  note deg
  also have "degree_m (smult c (prod_mset fs)) = degree_m (smult c gs)"
    unfolding gs_def by simp
  also have "\<dots> = degree gs" using d.
  also have "\<dots> = sum_mset (image_mset degree_m fs)" unfolding gs_def
    using fs
  proof (induct fs)
    case (add f fs)
    have mon: "monic (Mp f)" "monic (Mp (prod_mset fs))" using monic_Mp_prod_mset[of fs]
      add(2) by auto
    have "degree (Mp (prod_mset (add_mset f fs))) = degree (Mp (Mp f * Mp (prod_mset fs)))" 
      by (auto simp: ac_simps)
    also have "\<dots> = degree (Mp f) + degree (Mp (prod_mset fs))" 
      by (rule degree_Mp_mult_monic[OF mon])
    also have "degree (Mp (prod_mset fs)) = sum_mset (image_mset degree_m fs)" 
      by (rule add(1), insert add(2), auto)
    finally show ?case by (simp add: ac_simps)
  qed simp
  finally show ?thesis .
qed

lemma degree_m_mult_le: "degree_m (f * g) \<le> degree_m f + degree_m g" 
  using degree_m_mult_le by auto

lemma degree_m_prod_mset_le: "degree_m (prod_mset fs) \<le> sum_mset (image_mset degree_m fs)" 
proof (induct fs)
  case empty
  show ?case by simp
next
  case (add f fs)
  then show ?case using degree_m_mult_le[of f "prod_mset fs"] by auto
qed

end


context poly_mod_prime
begin

lemma unique_factorization_m_factor_partition: assumes l0: "l \<noteq> 0" 
  and uf: "poly_mod.unique_factorization_m (p^l) f (lead_coeff f, mset gs)" 
  and f: "f = f1 * f2" 
  and cop: "coprime (lead_coeff f) p" 
  and sf: "square_free_m f" 
  and part: "List.partition (\<lambda>gi. gi dvdm f1) gs = (gs1, gs2)" 
shows "poly_mod.unique_factorization_m (p^l) f1 (lead_coeff f1, mset gs1)"
  "poly_mod.unique_factorization_m (p^l) f2 (lead_coeff f2, mset gs2)"
proof -
  interpret pl: poly_mod_2 "p^l" by (standard, insert m1 l0, auto)
  let ?I = "image_mset pl.Mp" 
  note Mp_pow [simp] = Mp_Mp_pow_is_Mp[OF l0 m1]
  have [simp]: "pl.Mp x dvdm u = (x dvdm u)" for x u unfolding dvdm_def using Mp_pow[of x]
    by (metis poly_mod.mult_Mp(1))
  have gs_split: "set gs = set gs1 \<union> set gs2" using part by auto
  from pl.unique_factorization_m_factor[OF prime uf[unfolded f] _ _ l0 refl, folded f, OF cop sf]
  obtain hs1 hs2 where uf': "pl.unique_factorization_m f1 (lead_coeff f1, hs1)" 
      "pl.unique_factorization_m f2 (lead_coeff f2, hs2)"
    and gs_hs: "?I (mset gs) = hs1 + hs2"
    unfolding pl.Mf_def split by auto
  have gs_gs: "?I (mset gs) = ?I (mset gs1) + ?I (mset gs2)" using part 
    by (auto, induct gs arbitrary: gs1 gs2, auto)
  with gs_hs have gs_hs12: "?I (mset gs1) + ?I (mset gs2) = hs1 + hs2" by auto
  note pl_dvdm_imp_p_dvdm = pl_dvdm_imp_p_dvdm[OF l0]
  note fact = pl.unique_factorization_m_imp_factorization[OF uf]
  have gs1: "?I (mset gs1) = {#x \<in># ?I (mset gs). x dvdm f1#}"
    using part by (auto, induct gs arbitrary: gs1 gs2, auto)
  also have "\<dots> = {#x \<in># hs1. x dvdm f1#} + {#x \<in># hs2. x dvdm f1#}" unfolding gs_hs by simp
  also have "{#x \<in># hs2. x dvdm f1#} = {#}" 
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    then obtain x where x: "x \<in># hs2" and dvd: "x dvdm f1" by fastforce
    from x gs_hs have "x \<in># ?I (mset gs)" by auto
    with fact[unfolded pl.factorization_m_def]
    have xx: "pl.irreducible\<^sub>d_m x" "monic x" by auto
    from square_free_m_prod_imp_coprime_m[OF sf[unfolded f]] 
    have cop_h_f: "coprime_m f1 f2" by auto  
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf'(2)], of x] x 
    have "pl.dvdm x f2" by auto
    hence "x dvdm f2" by (rule pl_dvdm_imp_p_dvdm)
    from cop_h_f[unfolded coprime_m_def, rule_format, OF dvd this] 
    have "x dvdm 1" by auto
    from dvdm_imp_degree_le[OF this xx(2) _ m1] have "degree x = 0" by auto
    with xx show False unfolding pl.irreducible\<^sub>d_m_def by auto
  qed
  also have "{#x \<in># hs1. x dvdm f1#} = hs1"
  proof (rule ccontr)
    assume "\<not> ?thesis" 
    from filter_mset_inequality[OF this]
    obtain x where x: "x \<in># hs1" and dvd: "\<not> x dvdm f1" by blast
    from pl.factorization_m_mem_dvdm[OF pl.unique_factorization_m_imp_factorization[OF uf'(1)], 
      of x] x dvd 
    have "pl.dvdm x f1" by auto
    from pl_dvdm_imp_p_dvdm[OF this] dvd show False by auto
  qed
  finally have gs_hs1: "?I (mset gs1) = hs1" by simp
  with gs_hs12 have "?I (mset gs2) = hs2" by auto
  with uf' gs_hs1 have "pl.unique_factorization_m f1 (lead_coeff f1, ?I (mset gs1))"
     "pl.unique_factorization_m f2 (lead_coeff f2, ?I (mset gs2))" by auto
  thus "pl.unique_factorization_m f1 (lead_coeff f1, mset gs1)"
     "pl.unique_factorization_m f2 (lead_coeff f2, mset gs2)"
    unfolding pl.unique_factorization_m_def 
    by (auto simp: pl.Mf_def image_mset.compositionality o_def)
qed

lemma factorization_pn_to_factorization_p: assumes fact: "poly_mod.factorization_m (p^n) C (c,fs)"
  and sf: "square_free_m C" 
  and n: "n \<noteq> 0" 
shows "factorization_m C (c,fs)" 
proof -
  let ?q = "p^n" 
  from n m1 have q: "?q > 1" by simp
  interpret q: poly_mod_2 ?q by (standard, insert q, auto)
  from fact[unfolded q.factorization_m_def]
  have eq: "q.Mp C = q.Mp (Polynomial.smult c (prod_mset fs))" 
    and irr: "\<And> f. f \<in># fs \<Longrightarrow> q.irreducible\<^sub>d_m f" 
    and mon: "\<And> f. f \<in># fs \<Longrightarrow> monic (q.Mp f)" 
    by auto
  from arg_cong[OF eq, of Mp]
  have eq: "eq_m C (smult c (prod_mset fs))" 
    by (simp add: Mp_Mp_pow_is_Mp m1 n)
  show ?thesis unfolding factorization_m_def split
  proof (rule conjI[OF eq], intro ballI conjI)
    fix f
    assume f: "f \<in># fs" 
    from mon[OF this] have mon_qf: "monic (q.Mp f)" .
    hence lc: "lead_coeff (q.Mp f) = 1" by auto
    from mon_qf show mon_f: "monic (Mp f)" 
      by (metis Mp_Mp_pow_is_Mp m1 monic_Mp n)
    from irr[OF f] have irr: "q.irreducible\<^sub>d_m f" .
    hence "q.degree_m f \<noteq> 0" unfolding q.irreducible\<^sub>d_m_def by auto
    also have "q.degree_m f = degree_m f" using mon[OF f]
      by (metis Mp_Mp_pow_is_Mp m1 monic_degree_m n)
    finally have deg: "degree_m f \<noteq> 0" by auto
    from f obtain gs where fs: "fs = {#f#} + gs"
      by (metis mset_subset_eq_single subset_mset.add_diff_inverse)
    from eq[unfolded fs] have "Mp C = Mp (f * smult c (prod_mset gs))" by auto
    from square_free_m_factor[OF square_free_m_cong[OF sf this]]
    have sf_f: "square_free_m f" by simp
    have sf_Mf: "square_free_m (q.Mp f)"
      by (rule square_free_m_cong[OF sf_f], auto simp: Mp_Mp_pow_is_Mp n m1) 
    have "coprime (lead_coeff (q.Mp f)) p" using mon[OF f] prime by simp
    from berlekamp_hensel[OF this sf_Mf refl n, unfolded lc] obtain gs where
      qfact: "q.factorization_m (q.Mp f) (1, mset gs)"
      and "\<And> g. g \<in> set gs \<Longrightarrow> irreducible_m g" by blast
    hence fact: "q.Mp f = q.Mp (prod_list gs)" 
      and gs: "\<And> g. g\<in> set gs \<Longrightarrow> irreducible\<^sub>d_m g \<and> q.irreducible\<^sub>d_m g \<and> monic (q.Mp g)" 
      unfolding q.factorization_m_def by auto
    from q.factorization_m_degree[OF qfact]
    have deg: "q.degree_m (q.Mp f) = sum_mset (image_mset q.degree_m (mset gs))"
      using mon_qf by fastforce
    from irr[unfolded q.irreducible\<^sub>d_m_def]
    have "sum_mset (image_mset q.degree_m (mset gs)) \<noteq> 0" by (fold deg, auto)
    then obtain g gs' where gs1: "gs = g # gs'" by (cases gs, auto)
    {
      assume "gs' \<noteq> []" 
      then obtain h hs where gs2: "gs' = h # hs" by (cases gs', auto)
      from deg gs[unfolded q.irreducible\<^sub>d_m_def] 
      have small: "q.degree_m g < q.degree_m f" 
        "q.degree_m h + sum_mset (image_mset q.degree_m (mset hs)) < q.degree_m f" 
        unfolding gs1 gs2 by auto
      have "q.eq_m f (g * (h * prod_list hs))" 
        using fact unfolding gs1 gs2 by simp
      with irr[unfolded q.irreducible\<^sub>d_m_def, THEN conjunct2, rule_format, of g "h * prod_list hs"]
        small(1) have "\<not> q.degree_m (h * prod_list hs) < q.degree_m f" by auto
      hence "q.degree_m f \<le> q.degree_m (h * prod_list hs)" by simp
      also have "\<dots> = q.degree_m (prod_mset ({#h#} + mset hs))" by simp
      also have "\<dots> \<le> sum_mset (image_mset q.degree_m ({#h#} + mset hs))" 
        by (rule q.degree_m_prod_mset_le)
      also have "\<dots> < q.degree_m f" using small(2) by simp
      finally have False by simp
    }
    hence gs1: "gs = [g]" unfolding gs1 by (cases gs', auto)
    with fact have "q.Mp f = q.Mp g" by auto
    from arg_cong[OF this, of Mp] have eq: "Mp f = Mp g" 
      by (simp add: Mp_Mp_pow_is_Mp m1 n)
    from gs[unfolded gs1] have g: "irreducible\<^sub>d_m g" by auto
    with eq show "irreducible\<^sub>d_m f" unfolding irreducible\<^sub>d_m_def by auto
  qed
qed

lemma unique_monic_hensel_factorization: 
  assumes ufact: "unique_factorization_m C (1,Fs)"
  and C: "monic C" "square_free_m C" 
  and n: "n \<noteq> 0" 
  shows "\<exists> Gs. poly_mod.unique_factorization_m (p^n) C (1, Gs)"
  using ufact C
proof (induct Fs arbitrary: C rule: wf_induct[OF wf_measure[of size]])
  case (1 Fs C)
  let ?q = "p^n" 
  from n m1 have q: "?q > 1" by simp
  interpret q: poly_mod_2 ?q by (standard, insert q, auto)
  note [simp] = Mp_Mp_pow_is_Mp[OF n m1]
  note IH = 1(1)[rule_format]
  note ufact = 1(2)
  hence fact: "factorization_m C (1, Fs)" unfolding unique_factorization_m_alt_def by auto
  note monC = 1(3)
  note sf = 1(4)
  let ?n = "size Fs" 
  {
    fix d gs
    assume qfact: "q.factorization_m C (d,gs)" 
    from q.factorization_m_lead_coeff[OF this] q.monic_Mp[OF monC] 
    have d1: "q.M d = 1" by auto
    
    from factorization_pn_to_factorization_p[OF qfact sf n]
    have "factorization_m C (d,gs)" .
    with ufact d1 have "q.M d = 1" "M d = 1" "image_mset Mp gs = image_mset Mp Fs" 
      unfolding unique_factorization_m_alt_def Mf_def by auto    
  } note pre_unique = this
  show ?case
  proof (cases Fs)
    case empty
    with fact C have "Mp C = 1" unfolding factorization_m_def by auto
    hence "degree (Mp C) = 0" by simp
    with degree_m_eq_monic[OF monC m1] have "degree C = 0" by simp
    with monC have C1: "C = 1" using monic_degree_0 by blast
    with fact have fact: "q.factorization_m C (1,{#})" 
      by (auto simp: q.factorization_m_def)
    show ?thesis 
    proof (rule exI, rule q.unique_factorization_mI[OF fact])
      fix d gs
      assume fact: "q.factorization_m C (d,gs)" 
      from pre_unique[OF this, unfolded empty]
      show "q.Mf (d, gs) = q.Mf (1, {#})" by (auto simp: q.Mf_def)
    qed      
  next
    case (add D H) note FDH = this
    let ?D = "Mp D" 
    let ?H = "Mp (prod_mset H)"
    from fact have monFs: "\<And> F. F \<in># Fs \<Longrightarrow> monic (Mp F)" 
      and prod: "eq_m C (prod_mset Fs)" unfolding factorization_m_def by auto
    hence monD: "monic ?D" unfolding FDH by auto
    from square_free_m_cong[OF sf, of "D * prod_mset H"] prod[unfolded FDH]
    have "square_free_m (D * prod_mset H)" by (auto simp: ac_simps)
    from square_free_m_prod_imp_coprime_m[OF this]    
    have "coprime_m D (prod_mset H)" .
    hence cop': "coprime_m ?D ?H" unfolding coprime_m_def dvdm_def Mp_Mp by simp
    from fact have eq': "eq_m (?D * ?H) C"
      unfolding FDH by (simp add: factorization_m_def ac_simps)
    note unique_hensel_binary[OF prime cop' eq' Mp_Mp Mp_Mp monD n]
    from ex1_implies_ex[OF this] this
    obtain A B where CAB: "q.eq_m (A * B) C" and monA: "monic A" and DA: "eq_m ?D A"
      and HB: "eq_m ?H B" and norm: "q.Mp A = A" "q.Mp B = B" 
      and unique: "\<And> D' H'. q.eq_m (D' * H') C \<Longrightarrow>
          monic D' \<Longrightarrow>
          eq_m (Mp D) D' \<Longrightarrow> eq_m (Mp (prod_mset H)) H' \<Longrightarrow> q.Mp D' = D' \<Longrightarrow> q.Mp H' = H'
        \<Longrightarrow> D' = A \<and> H' = B" by blast
    note hensel_bin_wit = CAB monA DA HB norm
    from monA have monA': "monic (q.Mp A)" by (rule q.monic_Mp)
    from q.monic_Mp[OF monC] CAB have monicP:"monic (q.Mp (A * B))" by auto
    have f4: "\<And>p. coeff (A * p) (degree (A * p)) = coeff p (degree p)"
      by (simp add: coeff_degree_mult monA)
    have f2: "\<And>p n i. coeff p n mod i = coeff (poly_mod.Mp i p) n"
        using poly_mod.M_def poly_mod.Mp_coeff by presburger
    hence "coeff B (degree B) = 0 \<or> monic B"
        using monicP f4 by (metis (no_types) norm(2) q.degree_m_eq q.m1)
    hence monB: "monic B"
        using f4 monicP by (metis norm(2) leading_coeff_0_iff)
    from monA monB have lcAB: "lead_coeff (A * B) = 1" by (rule monic_mult)
    hence copAB: "coprime (lead_coeff (A * B)) p" by auto
    from arg_cong[OF CAB, of Mp]
    have CAB': "eq_m C (A * B)" by auto
    from sf CAB' have sfAB: "square_free_m (A * B)" using square_free_m_cong by blast
    from CAB' ufact have ufact: "unique_factorization_m (A * B) (1, Fs)"
      using unique_factorization_m_cong by blast
    have "(1 :: nat) \<noteq> 0" "p = p ^ 1" by auto
    note u_factor = unique_factorization_factorI[OF prime ufact copAB sfAB this]
    from fact DA have "irreducible\<^sub>d_m D" "eq_m A D" unfolding add factorization_m_def by auto
    hence "irreducible\<^sub>d_m A" using Mp_irreducible\<^sub>d_m by fastforce
    from irreducible\<^sub>d_lifting[OF n _ this] have irrA: "q.irreducible\<^sub>d_m A" using monA
      by (simp add: m1 poly_mod.degree_m_eq_monic q.m1)
    
    from add have lenH: "(H,Fs) \<in> measure size" by auto
    from HB fact have factB: "factorization_m B (1, H)" 
      unfolding FDH factorization_m_def by auto
    from u_factor(2)[OF factB] have ufactB: "unique_factorization_m B (1, H)" .

    from sfAB have sfB: "square_free_m B" by (rule square_free_m_factor)
    from IH[OF lenH ufactB monB sfB] obtain Bs where
      IH2: "q.unique_factorization_m B (1, Bs)" by auto
    
    from CAB have "q.Mp C = q.Mp (q.Mp A * q.Mp B)" by simp
    also have "q.Mp A * q.Mp B = q.Mp A * q.Mp (prod_mset Bs)" 
      using IH2 unfolding q.unique_factorization_m_alt_def q.factorization_m_def by auto
    also have "q.Mp \<dots> = q.Mp (A * prod_mset Bs)" by simp
    finally have factC: "q.factorization_m C (1, {# A #} + Bs)" using IH2 monA' irrA
      by (auto simp: q.unique_factorization_m_alt_def q.factorization_m_def)
    show ?thesis 
    proof (rule exI, rule q.unique_factorization_mI[OF factC])
      fix d gs
      assume dgs: "q.factorization_m C (d,gs)"
      from pre_unique[OF dgs, unfolded add] have d1: "q.M d = 1" and
        gs_fs: "image_mset Mp gs = {# Mp D #} + image_mset Mp H" by (auto simp: ac_simps)
      have "\<forall>f m p ma. image_mset f m \<noteq> add_mset (p::int poly) ma \<or>
                (\<exists>mb pa. m = add_mset (pa::int poly) mb \<and> f pa = p \<and> image_mset f mb = ma)"
          by (simp add: msed_map_invR)
      then obtain g hs where gs: "gs = {# g #} + hs" and gD: "Mp g = Mp D" 
        and hsH: "image_mset Mp hs = image_mset Mp H"
        using gs_fs by (metis add_mset_add_single union_commute)
      from dgs[unfolded q.factorization_m_def split] 
      have eq: "q.Mp C = q.Mp (smult d (prod_mset gs))" 
        and irr_mon: "\<And> g. g\<in>#gs \<Longrightarrow> q.irreducible\<^sub>d_m g \<and> monic (q.Mp g)"
        using d1 by auto
      note eq
      also have "q.Mp (smult d (prod_mset gs)) = q.Mp (smult (q.M d) (prod_mset gs))" 
        by simp
      also have "\<dots> = q.Mp (prod_mset gs)" unfolding d1 by simp
      finally have eq: "q.eq_m (q.Mp g * q.Mp (prod_mset hs)) C" unfolding gs by simp
      from gD have Dg: "eq_m (Mp D) (q.Mp g)" by simp
      have "Mp (prod_mset H) = Mp (prod_mset (image_mset Mp H))" by simp
      also have "\<dots> = Mp (prod_mset hs)" unfolding hsH[symmetric] by simp
      finally have Hhs: "eq_m (Mp (prod_mset H)) (q.Mp (prod_mset hs))" by simp
      from irr_mon[of g, unfolded gs] have mon_g: "monic (q.Mp g)" by auto
      from unique[OF eq mon_g Dg Hhs q.Mp_Mp q.Mp_Mp]
      have gA: "q.Mp g = A" and hsB: "q.Mp (prod_mset hs) = B" by auto
      have "q.factorization_m B (1, hs)" unfolding q.factorization_m_def split
        by (simp add: hsB norm irr_mon[unfolded gs])
      with IH2 have hsBs: "q.Mf (1,hs) = q.Mf (1,Bs)" unfolding q.unique_factorization_m_alt_def by blast
      show "q.Mf (d, gs) = q.Mf (1, {# A #} + Bs)" 
        using gA hsBs d1 unfolding gs q.Mf_def by auto
    qed
  qed
qed

theorem berlekamp_hensel_unique:
  assumes cop: "coprime (lead_coeff f) p"
  and sf: "poly_mod.square_free_m p f"
  and res: "berlekamp_hensel p n f = gs"
  and n: "n \<noteq> 0"
  shows "poly_mod.unique_factorization_m (p^n) f (lead_coeff f, mset gs) \<comment> \<open>unique factorization mod \<open>p^n\<close>\<close>"
    "\<And> g. g \<in> set gs \<Longrightarrow> poly_mod.Mp (p^n) g = g   \<comment> \<open>normalized\<close>"
proof -
  let ?q = "p^n" 
  interpret q: poly_mod_2 ?q unfolding poly_mod_2_def using m1 n by simp
  from berlekamp_hensel[OF assms]
  have bh_fact: "q.factorization_m f (lead_coeff f, mset gs)" by auto
  from berlekamp_hensel[OF assms]
  show "\<And> g. g \<in> set gs \<Longrightarrow> poly_mod.Mp (p^n) g = g" by blast
    from prime have p1: "p > 1" by (simp add: prime_int_iff)
  let ?lc = "coeff f (degree f)" 
  define ilc where "ilc \<equiv> inverse_mod ?lc (p ^ n)"
  from cop p1 n have inv: "q.M (ilc * ?lc) = 1"
    by (auto simp add: q.M_def ilc_def inverse_mod_pow)
  hence ilc0: "ilc \<noteq> 0" by (cases "ilc = 0", auto)
  {
    fix q
    assume "ilc * ?lc = ?q * q" 
    from arg_cong[OF this, of q.M] have "q.M (ilc * ?lc) = 0" 
      unfolding q.M_def by auto
    with inv have False by auto
  } note not_dvd = this
  let ?in = "q.Mp (smult ilc f)" 
  have mon: "monic ?in" unfolding q.Mp_coeff coeff_smult
    by (subst q.degree_m_eq[OF _ q.m1], insert not_dvd, auto simp: inv ilc0)
  have "q.Mp f = q.Mp (smult (q.M (?lc * ilc)) f)" using inv by (simp add: ac_simps)
  also have "\<dots> = q.Mp (smult ?lc (smult ilc f))" by simp
  finally have f: "q.Mp f = q.Mp (smult ?lc (smult ilc f))" . 
  from arg_cong[OF f, of Mp]
  have "Mp f = Mp (smult ?lc (smult ilc f))" 
    by (simp add: Mp_Mp_pow_is_Mp n p1)
  from arg_cong[OF this, of square_free_m, unfolded Mp_square_free_m] sf
  have "square_free_m (smult (coeff f (degree f)) (smult ilc f))" by simp
  from square_free_m_smultD[OF this] have sf: "square_free_m (smult ilc f)" .
  have Mp_in: "Mp ?in = Mp (smult ilc f)" 
    by (simp add: Mp_Mp_pow_is_Mp n p1)
  from Mp_square_free_m[of ?in, unfolded Mp_in] sf have sf: "square_free_m ?in"
    unfolding Mp_square_free_m by simp
  obtain a b where "finite_field_factorization_int p ?in = (a,b)" by force
  from finite_field_factorization_int[OF sf this]
  have ufact: "unique_factorization_m ?in (a, mset b)" by auto
  from unique_factorization_m_imp_factorization[OF this]
  have fact: "factorization_m ?in (a, mset b)" .
  from factorization_m_lead_coeff[OF this] monic_Mp[OF mon] 
  have "M a = 1" by auto
  with ufact have "unique_factorization_m ?in (1, mset b)" 
    unfolding unique_factorization_m_def Mf_def by auto
  from unique_monic_hensel_factorization[OF this mon sf n]
  obtain hs where "q.unique_factorization_m ?in (1, hs)" by auto
  hence unique: "q.unique_factorization_m (smult ilc f) (1, hs)"
    unfolding unique_factorization_m_def Mf_def by auto
  from q.factorization_m_smult[OF q.unique_factorization_m_imp_factorization[OF unique], of ?lc]
  have "q.factorization_m (smult (ilc * ?lc) f) (?lc, hs)" by (simp add: ac_simps)
  moreover have "q.Mp (smult (q.M (ilc * ?lc)) f) = q.Mp f" unfolding inv by simp
  ultimately have fact: "q.factorization_m f (?lc, hs)" 
    unfolding q.factorization_m_def by auto
  have "q.unique_factorization_m f (?lc, hs)" 
  proof (rule q.unique_factorization_mI[OF fact])
    fix d us
    assume other_fact: "q.factorization_m f (d,us)" 
    from q.factorization_m_lead_coeff[OF this] have lc: "q.M d = lead_coeff (q.Mp f)" ..
    have lc: "q.M d = q.M ?lc" unfolding lc
      by (metis bh_fact q.factorization_m_lead_coeff)
    from q.factorization_m_smult[OF other_fact, of ilc] unique
    have eq: "q.Mf (d * ilc, us) = q.Mf (1, hs)" unfolding q.unique_factorization_m_def by auto
    thus "q.Mf (d, us) = q.Mf (?lc, hs)" using lc unfolding q.Mf_def by auto
  qed
  with bh_fact show "q.unique_factorization_m f (lead_coeff f, mset gs)" 
    unfolding q.unique_factorization_m_alt_def by metis
qed

lemma hensel_lifting_unique:
  assumes n: "n \<noteq> 0" 
  and res: "hensel_lifting p n f fs = gs"                        \<comment> \<open>result of hensel is fact. \<open>gs\<close>\<close>
  and cop: "coprime (lead_coeff f) p" 
  and sf: "poly_mod.square_free_m p f" 
  and fact: "poly_mod.factorization_m p f (c, mset fs)"          \<comment> \<open>input is fact. \<open>fs mod p\<close>\<close>
  and c: "c \<in> {0..<p}" 
  and norm: "(\<forall>fi\<in>set fs. set (coeffs fi) \<subseteq> {0..<p})" 
shows "poly_mod.unique_factorization_m (p^n) f (lead_coeff f, mset gs)" \<comment> \<open>unique factorization mod \<open>p^n\<close>\<close>
    "sort (map degree fs) = sort (map degree gs)"                       \<comment> \<open>degrees stay the same\<close>
    "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and>    \<comment> \<open>monic and normalized\<close>
      poly_mod.irreducible_m p g \<and>                              \<comment> \<open>irreducibility even mod \<open>p\<close>\<close>
      poly_mod.degree_m p g = degree g   \<comment> \<open>mod \<open>p\<close> does not change degree of \<open>g\<close>\<close>"
proof -
  note hensel = hensel_lifting[OF assms]
  show "sort (map degree fs) = sort (map degree gs)" 
    "\<And> g. g \<in> set gs \<Longrightarrow> monic g \<and> poly_mod.Mp (p^n) g = g \<and> 
      poly_mod.irreducible_m p g \<and>                            
      poly_mod.degree_m p g = degree g" using hensel by auto
  from berlekamp_hensel_unique[OF cop sf refl n]
  have "poly_mod.unique_factorization_m (p ^ n) f (lead_coeff f, mset (berlekamp_hensel p n f))"  by auto
  with hensel(1) show "poly_mod.unique_factorization_m (p^n) f (lead_coeff f, mset gs)" 
    by (metis poly_mod.unique_factorization_m_alt_def)
qed

end

end
