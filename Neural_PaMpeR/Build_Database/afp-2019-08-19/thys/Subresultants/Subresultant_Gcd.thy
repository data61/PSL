section \<open>Computing the Gcd via the subresultant PRS\<close>

text \<open>This theory now formalizes how the subresultant PRS can be used to calculate the gcd
  of two polynomials. Moreover, it proves the connection between resultants and gcd, namely that
  the resultant is 0 iff the degree of the gcd is non-zero.\<close>

theory Subresultant_Gcd
imports
  Subresultant
  Polynomial_Factorization.Missing_Polynomial_Factorial
begin

subsection \<open>Algorithm\<close>

definition gcd_impl_primitive where
  [code del]: "gcd_impl_primitive G1 G2 = normalize (primitive_part (fst (subresultant_prs dichotomous_Lazard G1 G2)))" 

definition gcd_impl_main where
  [code del]: "gcd_impl_main G1 G2 = (if G1 = 0 then 0 else if G2 = 0 then normalize G1 else
   smult (gcd (content G1) (content G2))
     (gcd_impl_primitive (primitive_part G1) (primitive_part G2)))"

definition gcd_impl where
  "gcd_impl f g = (if length (coeffs f) \<ge> length (coeffs g) then gcd_impl_main f g  else gcd_impl_main g f)"

subsection \<open>Soundness Proof for @{term "gcd_impl = gcd"}\<close>

locale subresultant_prs_gcd = subresultant_prs_locale2 F n \<delta> f k \<beta> G1 G2 for
       F :: "nat \<Rightarrow> 'a :: factorial_ring_gcd fract poly"
    and n :: "nat \<Rightarrow> nat"
    and \<delta> :: "nat \<Rightarrow> nat"
    and f :: "nat \<Rightarrow> 'a fract"
    and k :: nat
    and \<beta> :: "nat \<Rightarrow> 'a fract"
    and G1 G2 :: "'a poly"
begin
text \<open>The subresultant PRS computes the gcd up to a scalar multiple.\<close>

lemma subresultant_prs_gcd: assumes "subresultant_prs dichotomous_Lazard G1 G2 = (Gk, hk)"
  shows "\<exists> a b. a \<noteq> 0 \<and> b \<noteq> 0 \<and> smult a (gcd G1 G2) = smult b (normalize Gk)"
proof -
  from subresultant_prs[OF dichotomous_Lazard assms]
  have Fk: "F k = ffp Gk" and "\<forall> i. \<exists> H. i \<noteq> 0 \<longrightarrow> F i = ffp H"
    and "\<forall> i. \<exists> b. 3 \<le> i \<longrightarrow> i \<le> Suc k \<longrightarrow> \<beta> i = ff b" by auto
  from choice[OF this(2)] choice[OF this(3)] obtain H beta where
    FH: "\<And> i. i \<noteq> 0 \<Longrightarrow> F i = ffp (H i)" and
    beta: "\<And> i. 3 \<le> i \<Longrightarrow> i \<le> Suc k \<Longrightarrow> \<beta> i = ff (beta i)" by auto
  from Fk FH[OF k0] FH[of 1] FH[of 2] FH[of "Suc k"] F0[of "Suc k"] F1 F2
  have border: "H k = Gk" "H 1 = G1" "H 2 = G2" "H (Suc k) = 0" by auto
  have "i \<noteq> 0 \<Longrightarrow> i \<le> k \<Longrightarrow> \<exists> a b. a \<noteq> 0 \<and> b \<noteq> 0 \<and> smult a (gcd G1 G2) = smult b (gcd (H i) (H (Suc i)))" for i
  proof (induct i rule: less_induct)
    case (less i)
    from less(3) have ik: "i \<le> k" .
    from less(2) have "i = 1 \<or> i \<ge> 2" by auto
    thus ?case
    proof
      assume "i = 1"
      thus ?thesis unfolding border[symmetric] by (intro exI[of _ 1], auto simp: numeral_2_eq_2)
    next
      assume i2: "i \<ge> 2"
      with ik have "i - 1 < i" "i - 1 \<noteq> 0" and imk: "i - 1 \<le> k" by auto
      from less(1)[OF this] i2
      obtain a b where a: "a \<noteq> 0" and b: "b \<noteq> 0" and IH: "smult a (gcd G1 G2) = smult b (gcd (H (i - 1)) (H i))" by auto
      define M where "M = pseudo_mod (H (i - 1)) (H i)"
      define c where "c = \<beta> (Suc i)"
      have M: "pseudo_mod (F (i - 1)) (F i) = ffp M" unfolding to_fract_hom.pseudo_mod_hom[symmetric] M_def
         using i2 FH by auto
      have c: "c \<noteq> 0" using \<beta>0 unfolding c_def .
      from i2 ik have 3: "Suc i \<ge> 3" "Suc i \<le> Suc k" by auto
      from pmod[OF 3]
      have pm: "smult c (F (Suc i)) = pseudo_mod (F (i - 1)) (F i)" unfolding c_def by simp
      from beta[OF 3, folded c_def] obtain d where cd: "c = ff d" by auto
      with c have d: "d \<noteq> 0" by auto
      from pm[unfolded cd M] FH[of "Suc i"]
      have "ffp (smult d (H (Suc i))) = ffp M" by auto
      hence pm: "smult d (H (Suc i)) = M" by (rule map_poly_hom.injectivity)
      from ik F0[of i] i2 FH[of i] have Hi0: "H i \<noteq> 0" by auto
      from pseudo_mod[OF this, of "H (i - 1)", folded M_def]
      obtain c Q where c: "c \<noteq> 0" and "smult c (H (i - 1)) = H i * Q + M" by auto
      from this[folded pm] have "smult c (H (i - 1)) = Q * H i + smult d (H (Suc i))" by simp
      from gcd_add_mult[of "H i" Q "smult d (H (Suc i))", folded this]
      have "gcd (H i) (smult c (H (i - 1))) = gcd (H i) (smult d (H (Suc i)))" .
      with gcd_smult_ex[OF c, of "H (i - 1)" "H i"] obtain e where
        e: "e \<noteq> 0" and "gcd (H i) (smult d (H (Suc i))) = smult e (gcd (H i) (H (i - 1)))"
        unfolding gcd.commute[of "H i"] by auto
      with gcd_smult_ex[OF d, of "H (Suc i)" "H i"] obtain c where
        c: "c \<noteq> 0" and "smult c (gcd (H i) (H (Suc i))) = smult e (gcd (H (i - 1)) (H i))"
        unfolding gcd.commute[of "H i"] by auto
      from arg_cong[OF this(2), of "smult b"] arg_cong[OF IH, of "smult e"]
      have "smult (e * a) (gcd G1 G2) = smult (b * c) (gcd (H i) (H (Suc i)))" unfolding smult_smult
        by (simp add: ac_simps)
      moreover have "e * a \<noteq> 0" "b * c \<noteq> 0" using a b c e by auto
      ultimately show ?thesis by blast
    qed
  qed
  from this[OF k0 le_refl, unfolded border]
  obtain a b where "a \<noteq> 0" "b \<noteq> 0" and "smult a (gcd G1 G2) = smult b (normalize Gk)" by auto
  thus ?thesis by auto
qed


lemma gcd_impl_primitive: assumes "primitive_part G1 = G1" and "primitive_part G2 = G2"
shows "gcd_impl_primitive G1 G2 = gcd G1 G2"
proof -
  let ?pp = primitive_part
  let ?c = "content"
  let ?n = normalize
  from F2 F0[of 2] k2 have G2: "G2 \<noteq> 0" by auto
  obtain Gk hk where sub: "subresultant_prs dichotomous_Lazard G1 G2 = (Gk, hk)" by force
  have impl: "gcd_impl_primitive G1 G2 = ?n (?pp Gk)" unfolding gcd_impl_primitive_def sub by auto
  from subresultant_prs_gcd[OF sub]
  obtain a b where a: "a \<noteq> 0" and b: "b \<noteq> 0" and id: "smult a (gcd G1 G2) = smult b (?n Gk)"
    by auto
  define c where "c = unit_factor (gcd G1 G2)"
  define d where "d = smult (unit_factor a) c"
  from G2 have c: "is_unit c" unfolding c_def by auto
  from arg_cong[OF id, of ?pp, unfolded primitive_part_smult primitive_part_gcd assms
     primitive_part_normalize c_def[symmetric]]
  have id: "d * gcd G1 G2 = smult (unit_factor b) (?n (?pp Gk))" unfolding d_def by simp
  have d: "is_unit d" unfolding d_def using c a
    by (simp add: is_unit_smult_iff)
  from is_unitE[OF d]
  obtain e where e: "is_unit e" and de: "d * e = 1" by metis
  define a where "a = smult (unit_factor b) e"
  from arg_cong[OF id, of "\<lambda> x. e * x"]
  have "(d * e) * gcd G1 G2 = a * (?n (?pp Gk))" by (simp add: ac_simps a_def)
  hence id: "gcd G1 G2 = a * (?n (?pp Gk))" using de by simp
  have a: "is_unit a" unfolding a_def using b e
    by (simp add: is_unit_smult_iff)
  define b where "b = unit_factor (?pp Gk)"
  have "Gk \<noteq> 0" using subresultant_prs[OF dichotomous_Lazard sub] F0[OF k0] by auto
  hence b: "is_unit b" unfolding b_def by auto
  from is_unitE[OF b]
  obtain c where c: "is_unit c" and bc: "b * c = 1" by metis
  obtain d where d: "is_unit d" and dac: "d = a * c" using c a by auto
  have "gcd G1 G2 = d * (b * ?n (?pp Gk))"
    unfolding id dac using bc by (simp add: ac_simps)
  also have "b * ?n (?pp Gk) = ?pp Gk" unfolding b_def by simp
  finally have "gcd G1 G2 = d * ?pp Gk" by simp
  from arg_cong[OF this, of ?n]
  have "gcd G1 G2 = ?n (d * ?pp Gk)" by simp
  also have "\<dots> = ?n (?pp Gk)" using d
    unfolding normalize_mult by (simp add: is_unit_normalize)
  finally show ?thesis unfolding impl ..
qed
end

lemma gcd_impl_main: assumes len: "length (coeffs G1) \<ge> length (coeffs G2)"
  shows "gcd_impl_main G1 G2 = gcd G1 G2"
proof (cases "G1 = 0")
  case G1: False
  show ?thesis
  proof (cases "G2 = 0")
    case G2: False
    let ?pp = "primitive_part"
    from G2 have G2: "?pp G2 \<noteq> 0" and id: "(G2 = 0) = False" by auto
    from len have len: "length (coeffs (?pp G1)) \<ge> length (coeffs (?pp G2))" by simp
    from enter_subresultant_prs[OF len G2] obtain F n d f k b
      where "subresultant_prs_locale2 F n d f k b (?pp G1) (?pp G2)" by auto
    interpret subresultant_prs_locale2 F n d f k b "?pp G1" "?pp G2" by fact
    interpret subresultant_prs_gcd F n d f k b "?pp G1" "?pp G2" ..
    show ?thesis unfolding gcd_impl_main_def gcd_poly_decompose[of G1] id if_False using G1
      by (subst gcd_impl_primitive, auto)
  next
    case True
    thus ?thesis unfolding gcd_impl_main_def by simp
  qed
next
  case True
  with len have "G2 = 0" by auto
  thus ?thesis using True unfolding gcd_impl_main_def by simp
qed


theorem gcd_impl[simp]: "gcd_impl = gcd"
proof (intro ext)
  fix f g :: "'a poly"
  show "gcd_impl f g = gcd f g"
  proof (cases "length (coeffs f) \<ge> length (coeffs g)")
    case True
    thus ?thesis unfolding gcd_impl_def gcd_impl_main[OF True] by auto
  next
    case False
    hence "length (coeffs g) \<ge> length (coeffs f)" by auto
    from gcd_impl_main[OF this]
    show ?thesis unfolding gcd_impl_def gcd.commute[of f g] using False by auto
  qed
qed


text \<open>The implementation also reveals an important connection between resultant and gcd.\<close>

lemma resultant_0_gcd: "resultant f g = 0 \<longleftrightarrow> degree (gcd f g) \<noteq> 0"
proof -
  {
    fix f g :: "'a poly"
    assume len: "length (coeffs f) \<ge> length (coeffs g)"
    {
      assume g: "g \<noteq> 0"
      with len have f: "f \<noteq> 0" by auto
      let ?f = "primitive_part f"
      let ?g = "primitive_part g"
      let ?c = "content"
      from len have len: "length (coeffs ?f) \<ge> length (coeffs ?g)" by simp
      obtain Gk hk where sub: "subresultant_prs dichotomous_Lazard ?f ?g = (Gk,hk)" by force
      have cf: "?c f \<noteq> 0" and cg: "?c g \<noteq> 0" using f g by auto
      {
        from g have "?g \<noteq> 0" by auto
        from enter_subresultant_prs[OF len this] obtain F n d f k b
          where "subresultant_prs_locale2 F n d f k b ?f ?g" by auto
        interpret subresultant_prs_locale2 F n d f k b ?f ?g by fact
        from subresultant_prs[OF dichotomous_Lazard sub] have "h k = ff hk" by auto
        with h0[OF le_refl] have "hk \<noteq> 0" by auto
      } note hk0 = this
      have "resultant f g = 0 \<longleftrightarrow> resultant (smult (?c f) ?f) (smult (?c g) ?g) = 0" by simp
      also have "\<dots> \<longleftrightarrow> resultant ?f ?g = 0" unfolding resultant_smult_left[OF cf] resultant_smult_right[OF cg]
        using cf cg by auto
      also have "\<dots> \<longleftrightarrow> resultant_impl_main dichotomous_Lazard ?f ?g = 0" 
        unfolding resultant_impl[symmetric] resultant_impl_def resultant_impl_main_def 
        resultant_impl_generic_def using len by auto
      also have "\<dots> \<longleftrightarrow> (degree Gk \<noteq> 0)"
        unfolding resultant_impl_main_def sub split using g hk0 by auto
      also have "degree Gk = degree (gcd_impl_primitive ?f ?g)"
        unfolding gcd_impl_primitive_def sub by simp
      also have "\<dots> = degree (gcd_impl_main f g)"
        unfolding gcd_impl_main_def using f g by auto
      also have "\<dots> = degree (gcd f g)" unfolding gcd_impl[symmetric] gcd_impl_def using len by auto
      finally have "(resultant f g = 0) = (degree (gcd f g) \<noteq> 0)" .
    }
    moreover
    {
      assume g: "g = 0" and f: "degree f \<noteq> 0"
      have "(resultant f g = 0) = (degree (gcd f g) \<noteq> 0)"
        unfolding g using f by auto
    }
    moreover
    {
      assume g: "g = 0" and f: "degree f = 0"
      have "(resultant f g = 0) = (degree (gcd f g) \<noteq> 0)"
        unfolding g using f by (auto simp: resultant_def sylvester_mat_def sylvester_mat_sub_def)
    }
    ultimately have "(resultant f g = 0) = (degree (gcd f g) \<noteq> 0)" by blast
  } note main = this
  show ?thesis
  proof (cases "length (coeffs f) \<ge> length (coeffs g)")
    case True
    from main[OF True] show ?thesis .
  next
    case False
    hence "length (coeffs g) \<ge> length (coeffs f)" by auto
    from main[OF this] show ?thesis
      unfolding gcd.commute[of g f] resultant_swap[of g f] by (simp split: if_splits)
  qed
qed

subsection \<open>Code Equations\<close>

definition [code del]:
  "gcd_impl_rec = subresultant_prs_main_impl fst"
definition [code del]:
  "gcd_impl_start = subresultant_prs_impl fst"

lemma gcd_impl_rec_code[code]:
  "gcd_impl_rec Gi_1 Gi ni_1 d1_1 hi_2 = (
    let pmod = pseudo_mod Gi_1 Gi
     in
     if pmod = 0 then Gi
        else let
           ni = degree Gi;
           d1 = ni_1 - ni;
           gi_1 = lead_coeff Gi_1;
           hi_1 = (if d1_1 = 1 then gi_1 else dichotomous_Lazard gi_1 hi_2 d1_1);
           divisor = if d1 = 1 then gi_1 * hi_1 else if even d1 then - gi_1 * hi_1 ^ d1 else gi_1 * hi_1 ^ d1;
           Gi_p1 = sdiv_poly pmod divisor
       in gcd_impl_rec Gi Gi_p1 ni d1 hi_1)"
  unfolding gcd_impl_rec_def subresultant_prs_main_impl.simps[of _ Gi_1] split Let_def
  unfolding gcd_impl_rec_def[symmetric]
  by (rule if_cong, auto)

lemma gcd_impl_start_code[code]:
  "gcd_impl_start G1 G2 =
     (let pmod = pseudo_mod G1 G2
         in if pmod = 0 then G2
            else let
                 n2 = degree G2;
                 n1 = degree G1;
                 d1 = n1 - n2;
                 G3 = if even d1 then - pmod else pmod;
                 pmod = pseudo_mod G2 G3
                 in if pmod = 0
                    then G3
                    else let
                           g2 = lead_coeff G2;
                           n3 = degree G3;
                           h2 = (if d1 = 1 then g2 else g2 ^ d1);
                           d2 = n2 - n3;
                           divisor = (if d2 = 1 then g2 * h2 else if even d2 then - g2 * h2 ^ d2 else g2 * h2 ^ d2);
                           G4 = sdiv_poly pmod divisor
                         in gcd_impl_rec G3 G4 n3 d2 h2)"
proof -
  obtain d1 where d1: "degree G1 - degree G2 = d1" by auto
  have id1: "(if even d1 then - pmod else pmod) = (-1)^ (d1 + 1) * (pmod :: 'a poly)" for pmod by simp
  show ?thesis
    unfolding gcd_impl_start_def subresultant_prs_impl_def gcd_impl_rec_def[symmetric] Let_def split
    unfolding d1
    unfolding id1
    by (rule if_cong, auto)
qed

lemma gcd_impl_main_code[code]:
  "gcd_impl_main G1 G2 = (if G1 = 0 then 0 else if G2 = 0 then normalize G1 else
    let c1 = content G1;
      c2 = content G2;
      p1 = map_poly (\<lambda> x. x div c1) G1;
      p2 = map_poly (\<lambda> x. x div c2) G2
     in smult (gcd c1 c2) (normalize (primitive_part (gcd_impl_start p1 p2))))"
  unfolding gcd_impl_main_def Let_def primitive_part_def gcd_impl_start_def gcd_impl_primitive_def
    subresultant_prs_impl by simp

corollary gcd_via_subresultant: "gcd f g = gcd_impl f g" by simp

text \<open>Note that we did not activate @{thm gcd_via_subresultant} as code-equation, since according to our experiments,
  the subresultant-gcd algorithm is not always more efficient than the currently active equation.
  In particular, on @{typ "int poly"} @{const gcd_impl} performs worse, but on multi-variate polynomials,
  e.g., @{typ "int poly poly poly"}, @{const gcd_impl} is preferable.\<close>

end
