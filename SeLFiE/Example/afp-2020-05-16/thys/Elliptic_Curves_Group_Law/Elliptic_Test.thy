section \<open>Validating the Specification\<close>

theory Elliptic_Test
imports
  Elliptic_Locale
  "HOL-Number_Theory.Residues"
begin

subsection \<open>Specialized Definitions for Prime Fields\<close>

definition mmult :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" (infixl "**\<index>" 70)
where "x **\<^bsub>m\<^esub> y = x * y mod m"

definition madd :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" (infixl "++\<index>" 65)
where "x ++\<^bsub>m\<^esub> y = (x + y) mod m"

definition msub :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" (infixl "--\<index>" 65)
where "x --\<^bsub>m\<^esub> y = (x - y) mod m"

definition mpow :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int" (infixr "^^^\<index>" 80)
where "x ^^^\<^bsub>m\<^esub> n = x ^ n mod m"

lemma (in residues) res_of_natural_eq: "\<guillemotleft>n\<guillemotright>\<^sub>\<nat> = int n mod m"
  by (induct n)
    (simp_all add: of_natural_def res_zero_eq res_one_eq res_add_eq mod_add_right_eq)

lemma (in residues) res_of_integer_eq: "\<guillemotleft>i\<guillemotright> = i mod m"
  by (simp add: of_integer_def res_of_natural_eq res_neg_eq mod_minus_eq)

lemma (in residues) res_pow_eq: "x [^] (n::nat) = x ^ n mod m"
  using m_gt_one
  by (induct n)
    (simp_all add: res_one_eq res_mult_eq mult_ac mod_mult_right_eq)

lemma (in residues) res_sub_eq: "(x mod m) \<ominus> (y mod m) = (x mod m - y mod m) mod m"
  by (simp add: minus_eq res_neg_eq res_add_eq mod_minus_eq mod_add_eq mod_diff_eq)

definition mpdouble :: "int \<Rightarrow> int \<Rightarrow> int ppoint \<Rightarrow> int ppoint" where
  "mpdouble m a p =
     (let (x, y, z) = p
      in
        if z = 0 then p
        else
          let
            l = 2 mod m **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> z;
            n = 3 mod m **\<^bsub>m\<^esub> x ^^^\<^bsub>m\<^esub> 2 ++\<^bsub>m\<^esub> a **\<^bsub>m\<^esub> z ^^^\<^bsub>m\<^esub> 2
          in
            (l **\<^bsub>m\<^esub> (n ^^^\<^bsub>m\<^esub> 2 --\<^bsub>m\<^esub> 4 mod m **\<^bsub>m\<^esub> x **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> l),
             n **\<^bsub>m\<^esub> (6 mod m **\<^bsub>m\<^esub> x **\<^bsub>m\<^esub> y **\<^bsub>m\<^esub> l --\<^bsub>m\<^esub> n ^^^\<^bsub>m\<^esub> 2) --\<^bsub>m\<^esub>
             2 mod m **\<^bsub>m\<^esub> y ^^^\<^bsub>m\<^esub> 2 **\<^bsub>m\<^esub> l ^^^\<^bsub>m\<^esub> 2,
             l ^^^\<^bsub>m\<^esub> 3))"

definition mpadd :: "int \<Rightarrow> int \<Rightarrow> int ppoint \<Rightarrow> int ppoint \<Rightarrow> int ppoint" where
  "mpadd m a p\<^sub>1 p\<^sub>2 =
     (let
        (x\<^sub>1, y\<^sub>1, z\<^sub>1) = p\<^sub>1;
        (x\<^sub>2, y\<^sub>2, z\<^sub>2) = p\<^sub>2
      in
        if z\<^sub>1 = 0 then p\<^sub>2
        else if z\<^sub>2 = 0 then p\<^sub>1
        else
          let
            d\<^sub>1 = x\<^sub>2 **\<^bsub>m\<^esub> z\<^sub>1;
            d\<^sub>2 = x\<^sub>1 **\<^bsub>m\<^esub> z\<^sub>2;
            l = d\<^sub>1 --\<^bsub>m\<^esub> d\<^sub>2;
            n = y\<^sub>2 **\<^bsub>m\<^esub> z\<^sub>1 --\<^bsub>m\<^esub> y\<^sub>1 **\<^bsub>m\<^esub> z\<^sub>2
          in
            if l = 0 then
              if n = 0 then mpdouble m a p\<^sub>1
              else (0, 0, 0)
            else
              let h = n ^^^\<^bsub>m\<^esub> 2 **\<^bsub>m\<^esub> z\<^sub>1 **\<^bsub>m\<^esub> z\<^sub>2 --\<^bsub>m\<^esub> (d\<^sub>1 ++\<^bsub>m\<^esub> d\<^sub>2) **\<^bsub>m\<^esub> l ^^^\<^bsub>m\<^esub> 2
              in
                (l **\<^bsub>m\<^esub> h,
                 (d\<^sub>2 **\<^bsub>m\<^esub> l ^^^\<^bsub>m\<^esub> 2 --\<^bsub>m\<^esub> h) **\<^bsub>m\<^esub> n --\<^bsub>m\<^esub> l ^^^\<^bsub>m\<^esub> 3 **\<^bsub>m\<^esub> y\<^sub>1 **\<^bsub>m\<^esub> z\<^sub>2,
                 l ^^^\<^bsub>m\<^esub> 3 **\<^bsub>m\<^esub> z\<^sub>1 **\<^bsub>m\<^esub> z\<^sub>2))"

lemma (in residues) pdouble_residue_eq: "pdouble a p = mpdouble m a p"
  by (simp only: pdouble_def mpdouble_def
    madd_def mmult_def msub_def mpow_def res_zero_eq res_add_eq res_mult_eq res_of_integer_eq
    res_pow_eq res_sub_eq)

lemma (in residues) padd_residue_eq: "padd a p\<^sub>1 p\<^sub>2 = mpadd m a p\<^sub>1 p\<^sub>2"
  by (simp only: padd_def mpadd_def pdouble_residue_eq
    madd_def mmult_def msub_def mpow_def res_zero_eq res_add_eq res_mult_eq res_of_integer_eq
    res_pow_eq res_sub_eq Let_def)

fun fast_ppoint_mult :: "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int ppoint \<Rightarrow> int ppoint"
where
  "fast_ppoint_mult m a n p =
     (if n = 0 then (0, 0, 0)
      else if n mod 2 = 0 then mpdouble m a (fast_ppoint_mult m a (n div 2) p)
      else mpadd m a p (mpdouble m a (fast_ppoint_mult m a (n div 2) p)))"

lemma fast_ppoint_mult_0 [simp]: "fast_ppoint_mult m a 0 p = (0, 0, 0)"
  by simp

lemma fast_ppoint_mult_even [simp]:
  "n \<noteq> 0 \<Longrightarrow> n mod 2 = 0 \<Longrightarrow>
   fast_ppoint_mult m a n p = mpdouble m a (fast_ppoint_mult m a (n div 2) p)"
  by simp

lemma fast_ppoint_mult_odd [simp]:
  "n \<noteq> 0 \<Longrightarrow> n mod 2 \<noteq> 0 \<Longrightarrow>
   fast_ppoint_mult m a n p = mpadd m a p (mpdouble m a (fast_ppoint_mult m a (n div 2) p))"
  by simp

declare fast_ppoint_mult.simps [simp del]

locale residues_prime_gt2 = residues_prime +
  assumes gt2: "2 < p"

sublocale residues_prime_gt2 < ell_field
  using gt2
  by unfold_locales (simp add: res_of_integer_eq res_zero_eq)

lemma (in residues_prime_gt2) fast_ppoint_mult_closed:
  assumes "a \<in> carrier R" "b \<in> carrier R" "on_curvep a b q"
  shows "on_curvep a b (fast_ppoint_mult (int p) a n q)"
  using assms
proof (induct "int p" a n q rule: fast_ppoint_mult.induct)
  case (1 a n q)
  show ?case
  proof (cases "n = 0")
    case True
    then show ?thesis using m_gt_one
      by (simp add: on_curvep_infinity [simplified res_zero_eq] res_carrier_eq)
  next
    case False
    with 1 show ?thesis
      by (cases "n mod 2 = 0")
        (simp_all add: padd_residue_eq [symmetric] pdouble_residue_eq [symmetric]
          padd_closed pdouble_closed)
  qed
qed
  
lemma (in residues_prime_gt2) point_mult_residue_eq:
  assumes "a \<in> carrier R" "b \<in> carrier R" "on_curvep a b q" "nonsingular a b"
  shows "proj_eq (ppoint_mult a n q) (fast_ppoint_mult (int p) a n q)"
proof -
  from assms
  have "point_mult a n (make_affine q) = make_affine (fast_ppoint_mult (int p) a n q)"
  proof (induct "int p" a n q rule: fast_ppoint_mult.induct)
    case (1 a n q)
    show ?case
    proof (cases "n = 0")
      case True
      then show ?thesis by (simp add: make_affine_infinity [simplified res_zero_eq])
    next
      case False
      have "point_mult a n (make_affine q) =
        point_mult a (n div 2 * 2 + n mod 2) (make_affine q)"
        by simp
      also from 1
      have "\<dots> = add a (point_mult a 2 (point_mult a (n div 2) (make_affine q)))
        (point_mult a (n mod 2) (make_affine q))"
        by (simp only: point_mult_mult point_mult_add
          on_curvep_iff_on_curve [symmetric] on_curvep_imp_in_carrierp)
      also have "\<dots> = make_affine (fast_ppoint_mult (int p) a n q)"
        using 1 False
        by (cases "n mod 2 = 0")
          (simp_all add: padd_residue_eq [symmetric] pdouble_residue_eq [symmetric] add_0_r
             padd_correct pdouble_correct
             fast_ppoint_mult_closed on_curvep_imp_in_carrierp [of a b]
             point_mult2_eq_double pdouble_closed
             add_assoc [symmetric] add_comm add_comm' on_curvep_iff_on_curve [symmetric])
      finally show ?thesis .
    qed
  qed
  with assms show ?thesis
    by (simp add: make_affine_proj_eq_iff fast_ppoint_mult_closed
      ppoint_mult_correct on_curvep_imp_in_carrierp [of a b])
qed

definition mmake_affine :: "int \<Rightarrow> int ppoint \<Rightarrow> int point" where
  "mmake_affine q p =
     (let (x, y, z) = p
      in if z = 0 then Infinity else
        let (a, b) = bezout_coefficients z q
        in Point (a **\<^bsub>q\<^esub> x) (a **\<^bsub>q\<^esub>y))"

lemma (in residues_prime) make_affine_residue_eq:
  assumes "in_carrierp q"
  shows "make_affine q = mmake_affine (int p) q"
proof (cases q)
  case (fields x y z)
  show ?thesis
  proof (cases "z = 0")
    case True
    with fields show ?thesis by (simp add: make_affine_def mmake_affine_def res_zero_eq)
  next
    case False
    show ?thesis
    proof (cases "bezout_coefficients z (int p)")
      case (Pair a b)
      with fields False assms have "\<not> int p dvd z"
        by (auto simp add: in_carrierp_def res_carrier_eq prime_imp_coprime zdvd_not_zless)
      with p_prime have "coprime (int p) z"
        by (auto intro: prime_imp_coprime)
      then have "coprime z (int p)"
        by (simp add: ac_simps)
      then have "fst (bezout_coefficients z (int p)) * z +
        snd (bezout_coefficients z (int p)) * int p = 1"
        by (simp add: bezout_coefficients_fst_snd)
      with m_gt_one have "fst (bezout_coefficients z (int p)) * z mod int p = 1"
        by (auto dest: arg_cong [of _ _ "\<lambda>x. x mod int p"])
      then have "z \<otimes> (fst (bezout_coefficients z (int p)) mod int p) = \<one>"
        by (simp add: res_mult_eq res_one_eq mult.commute mod_mult_right_eq)
      with fields assms have "inv z = fst (bezout_coefficients z (int p)) mod int p"
        by (simp add: inverse_unique in_carrierp_def res_carrier_eq)
      with fields Pair False show ?thesis
        by (simp add: make_affine_def mmake_affine_def res_zero_eq m_div_def
          res_mult_eq mmult_def mod_mult_right_eq mult.commute)
    qed
  qed
qed

definition mon_curve :: "int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int point \<Rightarrow> bool" where
  "mon_curve m a b p = (case p of
       Infinity \<Rightarrow> True
     | Point x y \<Rightarrow> 0 \<le> x \<and> x < m \<and> 0 \<le> y \<and> y < m \<and>
         y ^^^\<^bsub>m\<^esub> 2 = x ^^^\<^bsub>m\<^esub> 3 ++\<^bsub>m\<^esub> a **\<^bsub>m\<^esub> x ++\<^bsub>m\<^esub> b)"

lemma (in residues_prime_gt2) on_curve_residues_eq:
  "on_curve a b q = mon_curve (int p) a b q"
  by (simp add: on_curve_def mon_curve_def res_carrier_eq res_add_eq res_mult_eq res_pow_eq
    madd_def mmult_def mpow_def split: point.split)

subsection \<open>The NIST Curve P-521\<close>

text \<open>
The following test data is taken from RFC 5903 \cite{RFC5903}, \S 3.3 and \S 8.3.
The curve parameters can also be found in \S D.1.2.5 of FIPS PUB 186-4 \cite{FIPS186-4}.
\<close>

definition m :: int where
  "m = 0x01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF"

definition a :: int where
  "a = m - 3"

definition b :: int where
  "b = 0x0051953EB9618E1C9A1F929A21A0B68540EEA2DA725B99B315F3B8B489918EF109E156193951EC7E937B1652C0BD3BB1BF073573DF883D2C34F1EF451FD46B503F00"

definition gx :: int where
  "gx = 0x00C6858E06B70404E9CD9E3ECB662395B4429C648139053FB521F828AF606B4D3DBAA14B5E77EFE75928FE1DC127A2FFA8DE3348B3C1856A429BF97E7E31C2E5BD66"

definition gy :: int where
  "gy = 0x011839296A789A3BC0045C8A5FB42C7D1BD998F54449579B446817AFBD17273E662C97EE72995EF42640C550B9013FAD0761353C7086A272C24088BE94769FD16650"

definition priv :: nat where
  "priv = 0x0037ADE9319A89F4DABDB3EF411AACCCA5123C61ACAB57B5393DCE47608172A095AA85A30FE1C2952C6771D937BA9777F5957B2639BAB072462F68C27A57382D4A52"

definition pubx :: int where
  "pubx = 0x0015417E84DBF28C0AD3C278713349DC7DF153C897A1891BD98BAB4357C9ECBEE1E3BF42E00B8E380AEAE57C2D107564941885942AF5A7F4601723C4195D176CED3E"

definition puby :: int where
  "puby = 0x017CAE20B6641D2EEB695786D8C946146239D099E18E1D5A514C739D7CB4A10AD8A788015AC405D7799DC75E7B7D5B6CF2261A6A7F1507438BF01BEB6CA3926F9582"

definition order :: nat where
  "order = 0x01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409"

lemma "mon_curve m a b (Point gx gy)"
  by eval

lemma "mmake_affine m (fast_ppoint_mult m a priv (gx, gy, 1)) = Point pubx puby"
  by eval

lemma "mmake_affine m (fast_ppoint_mult m a order (gx, gy, 1)) = Infinity"
  by eval
  
end
