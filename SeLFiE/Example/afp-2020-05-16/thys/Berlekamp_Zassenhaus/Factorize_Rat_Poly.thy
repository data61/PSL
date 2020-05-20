(*
    Authors:      Jose Divasón
                  Sebastiaan Joosten
                  René Thiemann
                  Akihisa Yamada
*)
subsection \<open>Factoring Rational Polynomials\<close>

text \<open>We combine the factorization algorithm for integer polynomials
  with Gauss Lemma to a factorization algorithm for rational polynomials.\<close>
theory Factorize_Rat_Poly
imports 
  Factorize_Int_Poly
begin

(*TODO: Move*)
interpretation content_hom: monoid_mult_hom
  "content::'a::{factorial_semiring, semiring_gcd, normalization_semidom_multiplicative} poly \<Rightarrow> _"
by (unfold_locales, auto simp: content_mult)

lemma prod_dvd_1_imp_all_dvd_1:
  assumes "finite X" and "prod f X dvd 1" and "x \<in> X" shows "f x dvd 1"
proof (insert assms, induct rule:finite_induct)
  case IH: (insert x' X)
  show ?case
  proof (cases "x = x'")
    case True
    with IH show ?thesis using  dvd_trans[of "f x'" "f x' * _" 1]
      by (metis dvd_triv_left prod.insert)
  next
    case False
    then show ?thesis using IH by (auto intro!: IH(3) dvd_trans[of "prod f X" "_ * prod f X" 1])
  qed
qed simp

context
  fixes alg :: int_poly_factorization_algorithm
begin
definition factorize_rat_poly_generic :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list" where
  "factorize_rat_poly_generic f = (case rat_to_normalized_int_poly f of
     (c,g) \<Rightarrow> case factorize_int_poly_generic alg g of (d,fs) \<Rightarrow> (c * rat_of_int d, 
     map (\<lambda> (fi,i). (map_poly rat_of_int fi, i)) fs))" 
  
lemma factorize_rat_poly_0[simp]: "factorize_rat_poly_generic 0 = (0,[])" 
  unfolding factorize_rat_poly_generic_def rat_to_normalized_int_poly_def by simp

lemma factorize_rat_poly:
  assumes res: "factorize_rat_poly_generic f = (c,fs)"
  shows "square_free_factorization f (c,fs)"
    and "(fi,i) \<in> set fs \<Longrightarrow> irreducible fi"
proof(atomize(full), cases "f=0", goal_cases)
  case 1 with res show ?case by (auto simp: square_free_factorization_def)
next
  case 2 show ?case
  proof (unfold square_free_factorization_def split, intro conjI impI allI)
    let ?r = rat_of_int
    let ?rp = "map_poly ?r" 
    obtain d g where ri: "rat_to_normalized_int_poly f = (d,g)" by force
    obtain e gs where fi: "factorize_int_poly_generic alg g = (e,gs)" by force
    from res[unfolded factorize_rat_poly_generic_def ri fi split]
    have c: "c = d * ?r e" and fs: "fs = map (\<lambda> (fi,i). (?rp fi, i)) gs" by auto
    from factorize_int_poly[OF fi]
    have irr: "(fi, i) \<in> set gs \<Longrightarrow> irreducible fi \<and> content fi = 1" for fi i
      using irreducible_imp_primitive[of fi] by auto
    note sff = factorize_int_poly(1)[OF fi]
    note sff' = square_free_factorizationD[OF sff]
    {
      fix n f 
      have "?rp (f ^ n) = (?rp f) ^ n"
        by (induct n, auto simp: hom_distribs)
    } note exp = this
    show dist: "distinct fs" using sff'(5) unfolding fs distinct_map inj_on_def by auto
    interpret mh: map_poly_inj_idom_hom rat_of_int..
    have "f = smult d (?rp g)" using rat_to_normalized_int_poly[OF ri] by auto
    also have "\<dots> = smult d (?rp (smult e (\<Prod>(a, i)\<in>set gs. a ^ Suc i)))" using sff'(1) by simp
    also have "\<dots> = smult c (?rp (\<Prod>(a, i)\<in>set gs. a ^ Suc i))" unfolding c by (simp add: hom_distribs)
    also have "?rp (\<Prod>(a, i)\<in>set gs. a ^ Suc i) = (\<Prod>(a, i)\<in>set fs. a ^ Suc i)"
      unfolding prod.distinct_set_conv_list[OF sff'(5)] prod.distinct_set_conv_list[OF dist]
      unfolding fs
      by (insert exp, auto intro!: arg_cong[of _ _ "\<lambda>x. prod_list (map x gs)"] simp: hom_distribs of_int_poly_hom.hom_prod_list)
    finally show f: "f = smult c (\<Prod>(a, i)\<in>set fs. a ^ Suc i)" by auto
    {
      fix a i
      assume ai: "(a,i) \<in> set fs" 
      from ai obtain A where a: "a = ?rp A" and A: "(A,i) \<in> set gs" unfolding fs by auto
      fix b j
      assume "(b,j) \<in> set fs" and diff: "(a,i) \<noteq> (b,j)"
      from this(1) obtain B where b: "b = ?rp B" and B: "(B,j) \<in> set gs" unfolding fs by auto
      from diff[unfolded a b] have "(A,i) \<noteq> (B,j)" by auto
      from sff'(3)[OF A B this]
      show "Rings.coprime a b"
        by (auto simp add: coprime_iff_gcd_eq_1 gcd_rat_to_gcd_int a b)
    }
    {
      fix fi i
      assume "(fi,i) \<in> set fs" 
      then obtain gi where fi: "fi = ?rp gi" and gi: "(gi,i) \<in> set gs" unfolding fs by auto
      from irr[OF gi] have cf_gi: "primitive gi" by auto
      then have "primitive (?rp gi)" by (auto simp: content_field_poly)
      note [simp] = irreducible_primitive_connect[OF cf_gi] irreducible_primitive_connect[OF this]
      show "irreducible fi"
      using irr[OF gi] fi irreducible\<^sub>d_int_rat[of gi,simplified] by auto
      then show "degree fi > 0" "square_free fi" unfolding fi
        by (auto intro: irreducible_imp_square_free)
    }
    {
      assume "f = 0" with ri have *: "d = 1" "g = 0" unfolding rat_to_normalized_int_poly_def by auto
      with sff'(4)[OF *(2)] show "c = 0" "fs = []" unfolding c fs by auto
    }
  qed
qed

end

abbreviation factorize_rat_poly where 
  "factorize_rat_poly \<equiv> factorize_rat_poly_generic berlekamp_zassenhaus_factorization_algorithm" 

end
