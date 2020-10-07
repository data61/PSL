(*  
    Author:      Sebastiaan Joosten
                 René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Real Algebraic Numbers\<close>

text \<open>Whereas we previously only proved the closure properties of algebraic numbers, this
  theory adds the numeric computations that are required to separate the roots, and to
  pick unique representatives of algebraic numbers. 

  The development is split into three major parts. First, an ambiguous representation of 
  algebraic numbers is used, afterwards another layer is used with special treatment of rational numbers
  which still does not admit unique representatives, and finally, a quotient type is created modulo 
  the equivalence.
  
  The theory also contains a code-setup to implement real numbers via real algebraic numbers.\<close>


text \<open>The results are taken from the textbook \cite[pages 329ff]{AlgNumbers}.\<close>


theory Real_Algebraic_Numbers
imports 
  "Abstract-Rewriting.SN_Order_Carrier"
  Deriving.Compare_Rat
  Deriving.Compare_Real
  Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
  Algebraic_Numbers
  Sturm_Rat
begin

(*TODO: move *)
lemma ex1_imp_Collect_singleton: "(\<exists>!x. P x) \<and> P x \<longleftrightarrow> Collect P = {x}"
proof(intro iffI conjI, unfold conj_imp_eq_imp_imp)
  assume "Ex1 P" "P x" then show "Collect P = {x}" by blast
next
  assume Px: "Collect P = {x}"
  then have "P y \<longleftrightarrow> x = y" for y by auto
  then show "Ex1 P" by auto
  from Px show "P x" by auto
qed

lemma ex1_Collect_singleton[consumes 2]:
  assumes "\<exists>!x. P x" and "P x" and "Collect P = {x} \<Longrightarrow> thesis" shows thesis
  by (rule assms(3), subst ex1_imp_Collect_singleton[symmetric], insert assms(1,2), auto)

lemma ex1_iff_Collect_singleton: "P x \<Longrightarrow> (\<exists>!x. P x) \<longleftrightarrow> Collect P = {x}"
  by (subst ex1_imp_Collect_singleton[symmetric], auto)

context
  fixes f
  assumes bij: "bij f"
begin
lemma bij_imp_ex1_iff: "(\<exists>!x. P (f x)) \<longleftrightarrow> (\<exists>!y. P y)" (is "?l = ?r")
proof (intro iffI)
  assume l: ?l
  then obtain x where "P (f x)" by auto
  with l have *: "{x} = Collect (P o f)" by auto
  also have "f ` \<dots> = {y. P (f (Hilbert_Choice.inv f y))}" using bij_image_Collect_eq[OF bij] by auto
  also have "\<dots> = {y. P y}"
  proof-
    have "f (Hilbert_Choice.inv f y) = y" for y by (meson bij bij_inv_eq_iff)
    then show ?thesis by simp
  qed
  finally have "Collect P = {f x}" by auto
  then show ?r by (fold ex1_imp_Collect_singleton, auto)
next
  assume r: ?r
  then obtain y where "P y" by auto
  with r have "{y} = Collect P" by auto
  also have "Hilbert_Choice.inv f ` \<dots> = Collect (P \<circ> f)"
    using bij_image_Collect_eq[OF bij_imp_bij_inv[OF bij]] bij by (auto simp: inv_inv_eq)
  finally have "Collect (P o f) = {Hilbert_Choice.inv f y}" by (simp add: o_def)
  then show ?l by (fold ex1_imp_Collect_singleton, auto)
qed

lemma bij_ex1_imp_the_shift:
  assumes ex1: "\<exists>!y. P y" shows "(THE x. P (f x)) = Hilbert_Choice.inv f (THE y. P y)" (is "?l = ?r")
proof-
  from ex1 have "P (THE y. P y)" by (rule the1I2)
  moreover from ex1[folded bij_imp_ex1_iff] have "P (f (THE x. P (f x)))" by (rule the1I2)
  ultimately have "(THE y. P y) = f (THE x. P (f x))" using ex1 by auto
  also have "Hilbert_Choice.inv f \<dots> = (THE x. P (f x))" using bij by (simp add: bij_is_inj)
  finally show "?l = ?r" by auto
qed

lemma bij_imp_Collect_image: "{x. P (f x)} = Hilbert_Choice.inv f ` {y. P y}" (is "?l = ?g ` _")
proof-
  have "?l = ?g ` f ` ?l" by (simp add: image_comp inv_o_cancel[OF bij_is_inj[OF bij]])
  also have "f ` ?l = {f x | x. P (f x)}" by auto
  also have "\<dots> = {y. P y}" by (metis bij bij_iff)
  finally show ?thesis.
qed

lemma bij_imp_card_image: "card (f ` X) = card X"
  by (metis bij bij_iff card.infinite finite_imageD inj_onI inj_on_iff_eq_card)

end

lemma bij_imp_card: assumes bij: "bij f" shows "card {x. P (f x)} = card {x. P x}"
unfolding bij_imp_Collect_image[OF bij] bij_imp_card_image[OF bij_imp_bij_inv[OF bij]]..

lemma bij_add: "bij (\<lambda>x. x + y :: 'a :: group_add)" (is ?g1)
  and bij_minus: "bij (\<lambda>x. x - y :: 'a)" (is ?g2)
  and inv_add[simp]: "Hilbert_Choice.inv (\<lambda>x. x + y) = (\<lambda>x. x - y)" (is ?g3)
  and inv_minus[simp]: "Hilbert_Choice.inv (\<lambda>x. x - y) = (\<lambda>x. x + y)" (is ?g4)
proof-
  have 1: "(\<lambda>x. x - y) \<circ> (\<lambda>x. x + y) = id" and 2: "(\<lambda>x. x + y) \<circ> (\<lambda>x. x - y) = id" by auto
  from o_bij[OF 1 2] show ?g1.
  from o_bij[OF 2 1] show ?g2.
  from inv_unique_comp[OF 2 1] show ?g3.
  from inv_unique_comp[OF 1 2] show ?g4.
qed

lemmas ex1_shift[simp] = bij_imp_ex1_iff[OF bij_add] bij_imp_ex1_iff[OF bij_minus]

lemma ex1_the_shift:
  assumes ex1: "\<exists>!y :: 'a :: group_add. P y"
  shows "(THE x. P (x + d)) = (THE y. P y) - d"
    and "(THE x. P (x - d)) = (THE y. P y) + d"
  unfolding bij_ex1_imp_the_shift[OF bij_add ex1] bij_ex1_imp_the_shift[OF bij_minus ex1] by auto

lemma card_shift_image[simp]:
  shows "card ((\<lambda>x :: 'a :: group_add. x + d) ` X) = card X"
    and "card ((\<lambda>x. x - d) ` X) = card X"
  by (auto simp: bij_imp_card_image[OF bij_add] bij_imp_card_image[OF bij_minus])

lemma irreducible_root_free:
  fixes p :: "'a :: {idom,comm_ring_1} poly"
  assumes irr: "irreducible p" shows "root_free p"
proof (cases "degree p" "1::nat" rule: linorder_cases)
  case greater
  {
    fix x
    assume "poly p x = 0"
    hence "[:-x,1:] dvd p" using poly_eq_0_iff_dvd by blast
    then obtain r where p: "p = r * [:-x,1:]" by (elim dvdE, auto)
    have deg: "degree [:-x,1:] = 1" by simp
    have dvd: "\<not> [:-x,1:] dvd 1" by (auto simp: poly_dvd_1)
    from greater have "degree r \<noteq> 0" using degree_mult_le[of r "[:-x,1:]", unfolded deg, folded p] by auto
    then have "\<not> r dvd 1" by (auto simp: poly_dvd_1)
    with p irr irreducibleD[OF irr p] dvd have False by auto
  }
  thus ?thesis unfolding root_free_def by auto
next
  case less then have deg: "degree p = 0" by auto
  from deg obtain p0 where p: "p = [:p0:]" using degree0_coeffs by auto
  with irr have "p \<noteq> 0" by auto
  with p have "poly p x \<noteq> 0" for x by auto
  thus ?thesis by (auto simp: root_free_def)
qed (auto simp: root_free_def)


(* **************************************************************** *)
subsection \<open>Real Algebraic Numbers -- Innermost Layer\<close>

text \<open>We represent a real algebraic number \<open>\<alpha>\<close> by a tuple (p,l,r):
    \<open>\<alpha>\<close> is the unique root in the interval [l,r]
    and l and r have the same sign. We always assume that p is normalized, i.e.,
    p is the unique irreducible and positive content-free polynomial 
    which represents the algebraic number.

  This representation clearly admits duplicate representations for the same number, e.g.
  (...,x-3, 3,3) is equivalent to (...,x-3,2,10).\<close>

subsubsection \<open>Basic Definitions\<close>

type_synonym real_alg_1 = "int poly \<times> rat \<times> rat"

fun poly_real_alg_1 :: "real_alg_1 \<Rightarrow> int poly" where "poly_real_alg_1 (p,_,_) = p"
fun rai_ub :: "real_alg_1 \<Rightarrow> rat" where "rai_ub (_,_,r) = r"
fun rai_lb :: "real_alg_1 \<Rightarrow> rat" where "rai_lb (_,l,_) = l"

abbreviation "roots_below p x \<equiv> {y :: real. y \<le> x \<and> ipoly p y = 0}"

abbreviation(input) unique_root :: "real_alg_1 \<Rightarrow> bool" where
  "unique_root plr \<equiv> (\<exists>! x. root_cond plr x)"

abbreviation the_unique_root :: "real_alg_1 \<Rightarrow> real" where
  "the_unique_root plr \<equiv> (THE x. root_cond plr x)"

abbreviation real_of_1 where "real_of_1 \<equiv> the_unique_root"

lemma root_condI[intro]:
  assumes "of_rat (rai_lb plr) \<le> x" and "x \<le> of_rat (rai_ub plr)" and "ipoly (poly_real_alg_1 plr) x = 0"
  shows "root_cond plr x"
  using assms by (auto simp: root_cond_def)

lemma root_condE[elim]:
  assumes "root_cond plr x"
      and "of_rat (rai_lb plr) \<le> x \<Longrightarrow> x \<le> of_rat (rai_ub plr) \<Longrightarrow> ipoly (poly_real_alg_1 plr) x = 0 \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto simp: root_cond_def)

lemma
  assumes ur: "unique_root plr"
  defines "x \<equiv> the_unique_root plr" and "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  shows unique_rootD: "of_rat l \<le> x" "x \<le> of_rat r" "ipoly p x = 0" "root_cond plr x"
        "x = y \<longleftrightarrow> root_cond plr y" "y = x \<longleftrightarrow> root_cond plr y"
    and the_unique_root_eqI: "root_cond plr y \<Longrightarrow> y = x" "root_cond plr y \<Longrightarrow> x = y"
proof -
  from ur show x: "root_cond plr x" unfolding x_def by (rule theI')
  have "plr = (p,l,r)" by (cases plr, auto simp: p_def l_def r_def)
  from x[unfolded this] show "of_rat l \<le> x" "x \<le> of_rat r" "ipoly p x = 0" by auto
  from x ur
  show "root_cond plr y \<Longrightarrow> y = x" and "root_cond plr y \<Longrightarrow> x = y"
   and "x = y \<longleftrightarrow> root_cond plr y" and "y = x \<longleftrightarrow> root_cond plr y" by auto
qed

lemma unique_rootE:
  assumes ur: "unique_root plr"
  defines "x \<equiv> the_unique_root plr" and "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes main: "of_rat l \<le> x \<Longrightarrow> x \<le> of_rat r \<Longrightarrow> ipoly p x = 0 \<Longrightarrow> root_cond plr x \<Longrightarrow>
        (\<And>y. x = y \<longleftrightarrow> root_cond plr y) \<Longrightarrow> (\<And>y. y = x \<longleftrightarrow> root_cond plr y) \<Longrightarrow> thesis"
  shows thesis by (rule main, unfold x_def p_def l_def r_def; rule unique_rootD[OF ur])

lemma unique_rootI:
  assumes "\<And> y. root_cond plr y \<Longrightarrow> x = y" "root_cond plr x"
  shows "unique_root plr" using assms by blast

definition poly_cond :: "int poly \<Rightarrow> bool" where
  "poly_cond p = (lead_coeff p > 0 \<and> irreducible p)"

lemma poly_condI[intro]:
  assumes "lead_coeff p > 0" and "irreducible p" shows "poly_cond p" using assms by (auto simp: poly_cond_def)

lemma poly_condD:
  assumes "poly_cond p"
  shows "irreducible p" and "lead_coeff p > 0" and "root_free p" and "square_free p" and "p \<noteq> 0"
  using assms unfolding poly_cond_def using irreducible_root_free irreducible_imp_square_free cf_pos_def by auto

lemma poly_condE[elim]:
  assumes "poly_cond p"
      and "irreducible p \<Longrightarrow> lead_coeff p > 0 \<Longrightarrow> root_free p \<Longrightarrow> square_free p \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> thesis"
  shows thesis
  using assms by (auto dest:poly_condD)

definition invariant_1 :: "real_alg_1 \<Rightarrow> bool" where
  "invariant_1 tup \<equiv> case tup of (p,l,r) \<Rightarrow>
    unique_root (p,l,r) \<and> sgn l = sgn r \<and> poly_cond p"


lemma invariant_1I:
  assumes "unique_root plr" and "sgn (rai_lb plr) = sgn (rai_ub plr)" and "poly_cond (poly_real_alg_1 plr)"
  shows "invariant_1 plr"
  using assms by (auto simp: invariant_1_def)

lemma
  assumes "invariant_1 plr"
  defines "x \<equiv> the_unique_root plr" and "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  shows invariant_1D: "root_cond plr x"
    "sgn l = sgn r" "sgn x = of_rat (sgn r)" "unique_root plr" "poly_cond p" "degree p > 0" "primitive p"
    and invariant_1_root_cond: "\<And> y. root_cond plr y \<longleftrightarrow> y = x"
proof -
  let ?l = "of_rat l :: real"
  let ?r = "of_rat r :: real"
  have plr: "plr = (p,l,r)" by (cases plr, auto simp: p_def l_def r_def)
  from assms
  show ur: "unique_root plr" and sgn: "sgn l = sgn r" and pc: "poly_cond p" by (auto simp: invariant_1_def)
  from ur show rc: "root_cond plr x" by (auto simp add: x_def plr intro: theI')
  from this[unfolded plr] have x: "ipoly p x = 0" and bnd: "?l \<le> x" "x \<le> ?r" by auto
  show "sgn x = of_rat (sgn r)"
  proof (cases "0::real" "x" rule:linorder_cases)
    case less
    with bnd(2) have "0 < ?r" by arith
    thus ?thesis using less by simp
  next
    case equal
    with bnd have "?l \<le> 0" "?r \<ge> 0" by auto
    hence "l \<le> 0" "r \<ge> 0" by auto
    with \<open>sgn l = sgn r\<close> have "l = 0" "r = 0" unfolding sgn_rat_def by (auto split: if_splits)
    with rc[unfolded plr]
    show ?thesis by auto
  next
    case greater
    with bnd(1) have "?l < 0" by arith
    thus ?thesis unfolding \<open>sgn l = sgn r\<close>[symmetric] using greater by simp
  qed
  from the_unique_root_eqI[OF ur] rc
  show "\<And> y. root_cond plr y \<longleftrightarrow> y = x" by metis
  {
    assume "degree p = 0"
    with poly_zero[OF x, simplified] sgn bnd have "p = 0" by auto
    with pc have "False" by auto
  }
  then show "degree p > 0" by auto
  with pc show "primitive p" by (intro irreducible_imp_primitive, auto)
qed

lemma invariant_1E[elim]:
  assumes "invariant_1 plr"
  defines "x \<equiv> the_unique_root plr" and "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes main: "root_cond plr x \<Longrightarrow>
      sgn l = sgn r \<Longrightarrow> sgn x = of_rat (sgn r) \<Longrightarrow> unique_root plr \<Longrightarrow> poly_cond p \<Longrightarrow> degree p > 0 \<Longrightarrow>
      primitive p \<Longrightarrow> thesis"
  shows thesis apply (rule main)
  using assms(1) unfolding x_def p_def l_def r_def by (auto dest: invariant_1D)

lemma invariant_1_realI:
  fixes plr :: real_alg_1
  defines "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes x: "root_cond plr x" and "sgn l = sgn r"
      and ur: "unique_root plr"
      and "poly_cond p"
  shows "invariant_1 plr \<and> real_of_1 plr = x"
  using the_unique_root_eqI[OF ur x] assms by (cases plr, auto intro: invariant_1I)
    
lemma real_of_1_0:
  assumes "invariant_1 (p,l,r)"
  shows [simp]: "the_unique_root (p,l,r) = 0 \<longleftrightarrow> r = 0"
    and [dest]: "l = 0 \<Longrightarrow> r = 0"
    and [intro]: "r = 0 \<Longrightarrow> l = 0"
  using assms by (auto simp: sgn_0_0)


lemma invariant_1_pos: assumes rc: "invariant_1 (p,l,r)"
  shows [simp]:"the_unique_root (p,l,r) > 0 \<longleftrightarrow> r > 0" (is "?x > 0 \<longleftrightarrow> _")
    and [simp]:"the_unique_root (p,l,r) < 0 \<longleftrightarrow> r < 0"
    and [simp]:"the_unique_root (p,l,r) \<le> 0 \<longleftrightarrow> r \<le> 0"
    and [simp]:"the_unique_root (p,l,r) \<ge> 0 \<longleftrightarrow> r \<ge> 0"
    and [intro]: "r > 0 \<Longrightarrow> l > 0"
    and [dest]: "l > 0 \<Longrightarrow> r > 0"
    and [intro]: "r < 0 \<Longrightarrow> l < 0"
    and [dest]: "l < 0 \<Longrightarrow> r < 0"
proof(atomize(full),goal_cases)
  case 1
  let ?r = "real_of_rat"
  from assms[unfolded invariant_1_def]
  have ur: "unique_root (p,l,r)" and sgn: "sgn l = sgn r" by auto
  from unique_rootD(1-2)[OF ur] have le: "?r l \<le> ?x" "?x \<le> ?r r" by auto
  from rc show ?case
  proof (cases r "0::rat" rule:linorder_cases)
    case greater
    with sgn have "sgn l = 1" by simp
    hence l0: "l > 0" by (auto simp: sgn_1_pos)
    hence "?r l > 0" by auto
    hence "?x > 0" using le(1) by arith
    with greater l0 show ?thesis by auto
  next
    case equal
    with real_of_1_0[OF rc] show ?thesis by auto
  next
    case less
    hence "?r r < 0" by auto
    with le(2) have "?x < 0" by arith
    with less sgn show ?thesis by (auto simp: sgn_1_neg)
  qed
qed

definition invariant_1_2 where
  "invariant_1_2 rai \<equiv> invariant_1 rai \<and> degree (poly_real_alg_1 rai) > 1"

definition poly_cond2 where "poly_cond2 p \<equiv> poly_cond p \<and> degree p > 1"

lemma poly_cond2I[intro!]: "poly_cond p \<Longrightarrow> degree p > 1 \<Longrightarrow> poly_cond2 p" by (simp add: poly_cond2_def)

lemma poly_cond2D:
  assumes "poly_cond2 p"
  shows "poly_cond p" and "degree p > 1" using assms by (auto simp: poly_cond2_def)

lemma poly_cond2E[elim!]:
  assumes "poly_cond2 p" and "poly_cond p \<Longrightarrow> degree p > 1 \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: poly_cond2_def)

lemma invariant_1_2_poly_cond2: "invariant_1_2 rai \<Longrightarrow> poly_cond2 (poly_real_alg_1 rai)"
  unfolding invariant_1_def invariant_1_2_def poly_cond2_def by auto

lemma invariant_1_2I[intro!]:
  assumes "invariant_1 rai" and "degree (poly_real_alg_1 rai) > 1" shows "invariant_1_2 rai"
  using assms by (auto simp: invariant_1_2_def)

lemma invariant_1_2E[elim!]:
  assumes "invariant_1_2 rai"
      and "invariant_1 rai \<Longrightarrow> degree (poly_real_alg_1 rai) > 1 \<Longrightarrow> thesis"
  shows thesis using assms[unfolded invariant_1_2_def] by auto


lemma invariant_1_2_realI:
  fixes plr :: real_alg_1
  defines "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes x: "root_cond plr x" and sgn: "sgn l = sgn r" and ur: "unique_root plr" and p: "poly_cond2 p"
  shows "invariant_1_2 plr \<and> real_of_1 plr = x"
  using invariant_1_realI[OF x] p sgn ur unfolding p_def l_def r_def by auto
  
subsection \<open>Real Algebraic Numbers = Rational + Irrational Real Algebraic Numbers\<close>

text \<open>In the next representation of real algebraic numbers, we distinguish between
  rational and irrational numbers. The advantage is that whenever we only work on
  rational numbers, there is not much overhead involved in comparison to the 
  existing implementation of real numbers which just supports the rational numbers.
  For irrational numbers we additionally store the number of the root, counting from
  left to right. For instance $-\sqrt{2}$ and $\sqrt{2}$ would be root number 1 and 2
  of $x^2 - 2$.\<close>

subsubsection \<open>Definitions and Algorithms on Raw Type\<close>
datatype real_alg_2 = Rational rat | Irrational nat real_alg_1

  
fun invariant_2 :: "real_alg_2 \<Rightarrow> bool" where 
  "invariant_2 (Irrational n rai) = (invariant_1_2 rai
    \<and> n = card(roots_below (poly_real_alg_1 rai) (real_of_1 rai)))"
| "invariant_2 (Rational r) = True"
  
fun real_of_2 :: "real_alg_2 \<Rightarrow> real" where
  "real_of_2 (Rational r) = of_rat r"
| "real_of_2 (Irrational n rai) = real_of_1 rai"

definition of_rat_2 :: "rat \<Rightarrow> real_alg_2" where
  [code_unfold]: "of_rat_2 = Rational"

lemma of_rat_2: "real_of_2 (of_rat_2 x) = of_rat x" "invariant_2 (of_rat_2 x)"
  by (auto simp: of_rat_2_def)

(* Invariant type *)
typedef real_alg_3 = "Collect invariant_2" 
  morphisms rep_real_alg_3 Real_Alg_Invariant 
  by (rule exI[of _ "Rational 0"], auto)

setup_lifting type_definition_real_alg_3

lift_definition real_of_3 :: "real_alg_3 \<Rightarrow> real" is real_of_2 .

(* *************** *)
subsubsection \<open>Definitions and Algorithms on Quotient Type\<close>

quotient_type real_alg = real_alg_3 / "\<lambda> x y. real_of_3 x = real_of_3 y"
  morphisms rep_real_alg Real_Alg_Quotient
  by (auto simp: equivp_def) metis

(* real_of *)
lift_definition real_of :: "real_alg \<Rightarrow> real" is real_of_3 .

lemma real_of_inj: "(real_of x = real_of y) = (x = y)"
  by (transfer, simp)

(* ********************** *)
subsubsection \<open>Sign\<close>

definition sgn_1 :: "real_alg_1 \<Rightarrow> rat" where
  "sgn_1 x = sgn (rai_ub x)" 

lemma sgn_1: "invariant_1 x \<Longrightarrow> real_of_rat (sgn_1 x) = sgn (real_of_1 x)"
  unfolding sgn_1_def by auto

lemma sgn_1_inj: "invariant_1 x \<Longrightarrow> invariant_1 y \<Longrightarrow> real_of_1 x = real_of_1 y \<Longrightarrow> sgn_1 x = sgn_1 y"
  by (auto simp: sgn_1_def elim!: invariant_1E)

(* ********************** *)
subsubsection \<open>Normalization: Bounds Close Together\<close>

lemma unique_root_lr: assumes ur: "unique_root plr" shows "rai_lb plr \<le> rai_ub plr" (is "?l \<le> ?r")
proof -
  let ?p = "poly_real_alg_1 plr"
  from ur[unfolded root_cond_def]
  have ex1: "\<exists>! x :: real. of_rat ?l \<le> x \<and> x \<le> of_rat ?r \<and> ipoly ?p x = 0" by (cases plr, simp)
  then obtain x :: real where bnd: "of_rat ?l \<le> x" "x \<le> of_rat ?r" and rt: "ipoly ?p x = 0" by auto
  from bnd have "real_of_rat ?l \<le> of_rat ?r" by linarith
  thus "?l \<le> ?r" by (simp add: of_rat_less_eq)
qed

locale map_poly_zero_hom_0 = base: zero_hom_0
begin
  sublocale zero_hom_0 "map_poly hom" by (unfold_locales,auto)
end
interpretation of_int_poly_hom:
  map_poly_zero_hom_0 "of_int :: int \<Rightarrow> 'a :: {ring_1, ring_char_0}" ..

lemma ipoly_roots_finite: "p \<noteq> 0 \<Longrightarrow> finite {x :: 'a :: {idom, ring_char_0}. ipoly p x = 0}"
  by (rule poly_roots_finite, simp)


lemma roots_below_the_unique_root:
  assumes ur: "unique_root (p,l,r)"
  shows "roots_below p (the_unique_root (p,l,r)) = roots_below p (of_rat r)" (is "roots_below p ?x = _")
proof-
  from ur have rc: "root_cond (p,l,r) ?x" by (auto dest!: unique_rootD)
  with ur have x: "{x. root_cond (p,l,r) x} = {?x}" by (auto intro: the_unique_root_eqI)
  from rc have "?x \<in> {y. ?x \<le> y \<and> y \<le> of_rat r \<and> ipoly p y = 0}" by auto
  with rc have l1x: "... = {?x}" by (intro equalityI, fold x(1), force, simp add: x)

  have rb:"roots_below p (of_rat r) = roots_below p ?x \<union> {y. ?x < y \<and> y \<le> of_rat r \<and> ipoly p y = 0}"
    using rc by auto
  have emp: "\<And>x. the_unique_root (p, l, r) < x \<Longrightarrow>
                  x \<notin> {ra. ?x \<le> ra \<and> ra \<le> real_of_rat r \<and> ipoly p ra = 0}"
    using l1x by auto
  with rb show ?thesis by auto
qed

lemma unique_root_sub_interval:
  assumes ur: "unique_root (p,l,r)"
      and rc: "root_cond (p,l',r') (the_unique_root (p,l,r))"
      and between: "l \<le> l'" "r' \<le> r"
  shows "unique_root (p,l',r')"
    and "the_unique_root (p,l',r') = the_unique_root (p,l,r)"
proof -
  from between have ord: "real_of_rat l \<le> of_rat l'" "real_of_rat r' \<le> of_rat r" by (auto simp: of_rat_less_eq)
  from rc have lr': "real_of_rat l' \<le> of_rat r'" by auto
  with ord have lr: "real_of_rat l \<le> real_of_rat r" by auto
  show "\<exists>!x. root_cond (p, l', r') x"
  proof (rule, rule rc)
    fix y
    assume "root_cond (p,l',r') y"
    with ord have "root_cond (p,l,r) y" by (auto intro!:root_condI)
    from the_unique_root_eqI[OF ur this] show "y = the_unique_root (p,l,r)" by simp
  qed
  from the_unique_root_eqI[OF this rc] 
  show "the_unique_root (p,l',r') = the_unique_root (p,l,r)" by simp
qed

lemma invariant_1_sub_interval:
  assumes rc: "invariant_1 (p,l,r)"
      and sub: "root_cond (p,l',r') (the_unique_root (p,l,r))"
      and between: "l \<le> l'" "r' \<le> r"
  shows "invariant_1 (p,l',r')" and "real_of_1 (p,l',r') = real_of_1 (p,l,r)"
proof -
  let ?r = real_of_rat
  note rcD = invariant_1D[OF rc]
  from rc
  have ur: "unique_root (p, l', r')"
    and id: "the_unique_root (p, l', r') = the_unique_root (p, l, r)"
    by (atomize(full), intro conjI unique_root_sub_interval[OF _ sub between], auto)
  show "real_of_1 (p,l',r') = real_of_1 (p,l,r)"
    using id by simp
  from rcD(1)[unfolded split] have "?r l \<le> ?r r" by auto
  hence lr: "l \<le> r" by (auto simp: of_rat_less_eq)
  from unique_rootD[OF ur] have "?r l' \<le> ?r r'" by auto
  hence lr': "l' \<le> r'" by (auto simp: of_rat_less_eq)
  have "sgn l' = sgn r'"
  proof (cases "r" "0::rat" rule: linorder_cases)
    case less
    with lr lr' between have "l < 0" "l' < 0" "r' < 0" "r < 0" by auto
    thus ?thesis unfolding sgn_rat_def by auto
  next
    case equal with rcD(2) have "l = 0" using sgn_0_0 by auto
    with equal between lr' have "l' = 0" "r' = 0" by auto then show ?thesis by auto
  next
    case greater
    with rcD(4) have "sgn r = 1" unfolding sgn_rat_def by (cases "r = 0", auto)
    with rcD(2) have "sgn l = 1" by simp
    hence l: "l > 0" unfolding sgn_rat_def by (cases "l = 0"; cases "l < 0"; auto)
    with lr lr' between have "l > 0" "l' > 0" "r' > 0" "r > 0" by auto
    thus ?thesis unfolding sgn_rat_def by auto
  qed
  with between ur rc show "invariant_1 (p,l',r')" by (auto simp add: invariant_1_def id)
qed

lemma root_sign_change: assumes
    p0: "poly (p::real poly) x = 0" and
    pd_ne0: "poly (pderiv p) x \<noteq> 0"
  obtains d where
    "0 < d"
    "sgn (poly p (x - d)) \<noteq> sgn (poly p (x + d))"
    "sgn (poly p (x - d)) \<noteq> 0"
    "0 \<noteq> sgn (poly p (x + d))"
    "\<forall> d' > 0. d' \<le> d \<longrightarrow> sgn (poly p (x + d')) = sgn (poly p (x + d)) \<and> sgn (poly p (x - d')) = sgn (poly p (x - d))"
proof -
  assume a:"(\<And>d. 0 < d \<Longrightarrow>
          sgn (poly p (x - d)) \<noteq> sgn (poly p (x + d)) \<Longrightarrow>
          sgn (poly p (x - d)) \<noteq> 0 \<Longrightarrow>
          0 \<noteq> sgn (poly p (x + d)) \<Longrightarrow>
          \<forall>d'>0. d' \<le> d \<longrightarrow>
                 sgn (poly p (x + d')) = sgn (poly p (x + d)) \<and> sgn (poly p (x - d')) = sgn (poly p (x - d)) \<Longrightarrow>
          thesis)"
  from pd_ne0 consider "poly (pderiv p) x > 0" | "poly (pderiv p) x < 0" by linarith
  thus ?thesis proof(cases)
    case 1
    obtain d1 where d1:"\<And>h. 0<h \<Longrightarrow> h < d1 \<Longrightarrow> poly p (x - h) < 0" "d1 > 0"
      using DERIV_pos_inc_left[OF poly_DERIV 1] p0 by auto
    obtain d2 where d2:"\<And>h. 0<h \<Longrightarrow> h < d2 \<Longrightarrow> poly p (x + h) > 0" "d2 > 0"
      using DERIV_pos_inc_right[OF poly_DERIV 1] p0 by auto
    have g0:"0 < (min d1 d2) / 2" using d1 d2 by auto
    hence m1:"min d1 d2 / 2 < d1" and m2:"min d1 d2 / 2 < d2" by auto
    { fix d
      assume a1:"0 < d" and a2:"d < min d1 d2"
      have "sgn (poly p (x - d)) = -1" "sgn (poly p (x + d)) = 1"
        using d1(1)[OF a1] d2(1)[OF a1] a2 by auto
    } note d=this
    show ?thesis by(rule a[OF g0];insert d g0 m1 m2, simp)
  next
    case 2
    obtain d1 where d1:"\<And>h. 0<h \<Longrightarrow> h < d1 \<Longrightarrow> poly p (x - h) > 0" "d1 > 0"
      using DERIV_neg_dec_left[OF poly_DERIV 2] p0 by auto
    obtain d2 where d2:"\<And>h. 0<h \<Longrightarrow> h < d2 \<Longrightarrow> poly p (x + h) < 0" "d2 > 0"
      using DERIV_neg_dec_right[OF poly_DERIV 2] p0 by auto
    have g0:"0 < (min d1 d2) / 2" using d1 d2 by auto
    hence m1:"min d1 d2 / 2 < d1" and m2:"min d1 d2 / 2 < d2" by auto
    { fix d
      assume a1:"0 < d" and a2:"d < min d1 d2"
      have "sgn (poly p (x - d)) = 1" "sgn (poly p (x + d)) = -1"
        using d1(1)[OF a1] d2(1)[OF a1] a2 by auto
    } note d=this
    show ?thesis by(rule a[OF g0];insert d g0 m1 m2, simp)
  qed
qed

lemma rational_root_free_degree_iff: assumes rf: "root_free (map_poly rat_of_int p)" and rt: "ipoly p x = 0"
  shows "(x \<in> \<rat>) = (degree p = 1)"
proof 
  assume "x \<in> \<rat>"
  then obtain y where x: "x = of_rat y" (is "_ = ?x") unfolding Rats_def by blast
  from rt[unfolded x] have "poly (map_poly rat_of_int p) y = 0" by simp
  with rf show "degree p = 1" unfolding root_free_def by auto
next
  assume "degree p = 1"
  from degree1_coeffs[OF this]
  obtain a b where p: "p = [:a,b:]" and b: "b \<noteq> 0" by auto
  from rt[unfolded p hom_distribs] have "of_int a + x * of_int b = 0" by auto
  from arg_cong[OF this, of "\<lambda> x. (x - of_int a) / of_int b"]
  have "x = - of_rat (of_int a) / of_rat (of_int b)" using b by auto
  also have "\<dots> = of_rat (- of_int a / of_int b)" unfolding of_rat_minus of_rat_divide ..
  finally show "x \<in> \<rat>" by auto
qed

lemma rational_poly_cond_iff: assumes "poly_cond p" and "ipoly p x = 0" and "degree p > 1"
  shows "(x \<in> \<rat>) = (degree p = 1)"
proof (rule rational_root_free_degree_iff[OF _ assms(2)])
  from poly_condD[OF assms(1)] irreducible_connect_rev[of p] assms(3)
  have p: "irreducible\<^sub>d p" by auto
  from irreducible\<^sub>d_int_rat[OF this]
  have "irreducible (map_poly rat_of_int p)" by simp
  thus "root_free (map_poly rat_of_int p)" by (rule irreducible_root_free) 
qed

lemma poly_cond_degree_gt_1: assumes "poly_cond p" "degree p > 1" "ipoly p x = 0"
  shows "x \<notin> \<rat>" 
  using rational_poly_cond_iff[OF assms(1,3)] assms(2) by simp

lemma poly_cond2_no_rat_root: assumes "poly_cond2 p" 
  shows "ipoly p (real_of_rat x) \<noteq> 0"
  using poly_cond_degree_gt_1[of p "real_of_rat x"] assms by auto

context 
  fixes p :: "int poly"
  and x :: "rat"
begin
  
lemma gt_rat_sign_change:
  assumes ur: "unique_root plr"
  defines "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes p: "poly_cond2 p" and in_interval: "l \<le> y" "y \<le> r"
shows "(sgn (ipoly p y) = sgn (ipoly p r)) = (of_rat y > the_unique_root plr)" (is "?gt = _")
proof (rule ccontr)
  have plr[simp]: "plr = (p,l,r)" by (cases plr, auto simp: p_def l_def r_def)
  assume "?gt \<noteq> (real_of_rat y > the_unique_root plr)"
  note a = this[unfolded plr]
  from p have "irreducible p" by auto
  note nz = poly_cond2_no_rat_root[OF p]
  hence "p \<noteq> 0" unfolding irreducible_def by auto
  hence p0_real: "real_of_int_poly p \<noteq> (0::real poly)" by auto
  let ?p = "real_of_int_poly p"
  note urD = unique_rootD[OF ur, simplified]
  let ?ur = "the_unique_root (p, l, r)"
  let ?r = real_of_rat
  from poly_cond2_no_rat_root p
  have ru:"ipoly p y \<noteq> 0" by auto
  from in_interval have in':"?r l \<le> ?r y" "?r y \<le> ?r r" unfolding of_rat_less_eq by auto
  from p square_free_of_int_poly[of p] square_free_rsquarefree
  have rsf:"rsquarefree ?p" by auto
  have ur3:"poly ?p ?ur = 0" using urD(3) by simp
  from ur have "?ur \<le> of_rat r" by (auto elim!: unique_rootE)
  moreover
    from nz have "ipoly p (real_of_rat r) \<noteq> 0" by auto
    with ur3 have "real_of_rat r \<noteq> real_of_1 (p,l,r)" by force
  ultimately have "?ur < ?r r" by auto
  hence ur2: "0 < ?r r - ?ur" by linarith
  from rsquarefree_roots rsf ur3
  have pd_nonz:"poly (pderiv ?p) ?ur \<noteq> 0" by auto
  obtain d where d':"\<And>d'. d'>0 \<Longrightarrow> d' \<le> d \<Longrightarrow>
             sgn (poly ?p (?ur + d')) = sgn (poly ?p (?ur + d)) \<and>
             sgn (poly ?p (?ur - d')) = sgn (poly ?p (?ur - d))"
      "sgn (poly ?p (?ur - d)) \<noteq> sgn (poly ?p (?ur + d))"
      "sgn (poly ?p (?ur + d)) \<noteq> 0"
      and d_ge_0:"d > 0"
    by (metis root_sign_change[OF ur3 pd_nonz])
  have sr:"sgn (poly ?p (?ur + d)) = sgn (poly ?p (?r r))"
  proof (cases "?r r - ?ur \<le> d")
    case True show ?thesis using d'(1)[OF ur2 True] by auto
  next
    case False hence less:"?ur + d < ?r r" by auto
    show ?thesis
    proof(rule no_roots_inbetween_imp_same_sign[OF less,rule_format],goal_cases)
      case (1 x)
      from ur 1 d_ge_0 have ran: "real_of_rat l \<le> x" "x \<le> real_of_rat r" by (auto elim!: unique_rootE)
      from 1 d_ge_0 have "the_unique_root (p, l, r) \<noteq> x" by auto
      with ur have "\<not> root_cond (p,l,r) x" by auto
      with ran show ?case by auto
    qed
  qed
  consider "?r l < ?ur - d" "?r l < ?ur" | "0 < ?ur - ?r l" "?ur - ?r l \<le> d" | "?ur = ?r l"
    using urD by argo
  hence sl:"sgn (poly ?p (?ur - d)) = sgn (poly ?p (?r l)) \<or> 0 = sgn (poly ?p (?r l))"
  proof (cases)
    case 1
    have "sgn (poly ?p (?r l)) = sgn (poly ?p (?ur - d))"
    proof(rule no_roots_inbetween_imp_same_sign[OF 1(1),rule_format],goal_cases)
      case (1 x)
      from ur 1 d_ge_0 have ran: "real_of_rat l \<le> x" "x \<le> real_of_rat r" by (auto elim!: unique_rootE)
      from 1 d_ge_0 have "the_unique_root (p, l, r) \<noteq> x" by auto
      with ur have "\<not> root_cond (p,l,r) x" by auto
      with ran show ?case by auto
    qed
    thus ?thesis by auto
  next case 2 show ?thesis using d'(1)[OF 2] by simp
  qed (insert ur3,simp)
  have diff_sign: "sgn (ipoly p l) \<noteq> sgn (ipoly p r)"
    using d'(2-) sr sl real_of_rat_sgn by auto
  have ur':"\<And>x. real_of_rat l \<le> x \<and> x \<le> real_of_rat y \<Longrightarrow> ipoly p x = 0 \<Longrightarrow> \<not> (?r y \<le> the_unique_root (p,l,r))"
  proof(standard+,goal_cases)
    case (1 x)
    {
      assume id: "the_unique_root (p,l,r) = ?r y" 
      from nz[of y] id ur have False by (auto elim!: unique_rootE)
    } note neq = this
    have "root_cond (p, l, r) x" unfolding root_cond_def
      using 1 a ur by (auto elim!: unique_rootE)
    with conjunct2[OF 1(1)] 1(2-) the_unique_root_eqI[OF ur]
    show ?case by (auto intro!: neq)
  qed
  hence ur'':"\<forall>x. real_of_rat y \<le> x \<and> x \<le> real_of_rat r \<longrightarrow> poly (real_of_int_poly p) x \<noteq> 0 \<Longrightarrow> \<not> (?r y \<le> the_unique_root (p,l,r))"
    using urD(2,3) by auto
  have "(sgn (ipoly p y) = sgn (ipoly p r)) = (?r y > the_unique_root (p,l,r))"
  proof(cases "sgn (ipoly p r) = sgn (ipoly p y)")
    case True
    have sgn:"sgn (poly ?p (real_of_rat l)) \<noteq> sgn (poly ?p (real_of_rat y))" using True diff_sign
      by (simp add: real_of_rat_sgn)
    have ly:"of_rat l < (of_rat y::real)" using in_interval True diff_sign less_eq_rat_def of_rat_less by auto
    with no_roots_inbetween_imp_same_sign[OF ly,of ?p] sgn ur' True
    show ?thesis by force
  next
    case False
    hence ne:"sgn (ipoly p (real_of_rat y)) \<noteq> sgn (ipoly p (real_of_rat r))" by (simp add: real_of_rat_sgn)
    have ry:"of_rat y < (of_rat r::real)" using in_interval False diff_sign less_eq_rat_def of_rat_less by auto
    obtain x where x:"real_of_rat y \<le> x" "x \<le> real_of_rat r" "ipoly p x = 0"
      using no_roots_inbetween_imp_same_sign[OF ry,of ?p] ne by auto
    hence lx:"real_of_rat l \<le> x" using in_interval
      using False a urD by auto
    have "?ur = x" using x lx ur by (intro the_unique_root_eqI, auto)
    then show ?thesis using False x by auto
  qed
  thus False using diff_sign(1) a ru by(cases "ipoly p r = 0";auto simp:sgn_0_0)
qed
  
definition tighten_poly_bounds :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<times> rat \<times> rat" where
  "tighten_poly_bounds l r sr = (let m = (l + r) / 2; sm = sgn (ipoly p m) in 
    if sm = sr
     then (l,m,sm) else (m,r,sr))"

lemma tighten_poly_bounds: assumes res: "tighten_poly_bounds l r sr = (l',r',sr')"
  and ur: "unique_root (p,l,r)"
  and p:  "poly_cond2 p"   
  and sr: "sr = sgn (ipoly p r)" 
  shows "root_cond (p,l',r') (the_unique_root (p,l,r))" "l \<le> l'" "l' \<le> r'" "r' \<le> r" 
    "(r' - l') = (r - l) / 2" "sr' = sgn (ipoly p r')" 
proof -
  let ?x = "the_unique_root (p,l,r)"
  let ?x' = "the_unique_root (p,l',r')"
  let ?m = "(l + r) / 2"
  note d = tighten_poly_bounds_def Let_def
  from unique_root_lr[OF ur] have lr: "l \<le> r" by auto
  thus "l \<le> l'" "l' \<le> r'" "r' \<le> r" "(r' - l') = (r - l) / 2" "sr' = sgn (ipoly p r')"
    using res sr unfolding d by (auto split: if_splits)
  hence "l \<le> ?m" "?m \<le> r" by auto
  note le = gt_rat_sign_change[OF ur,simplified,OF p this]
  note urD = unique_rootD[OF ur]
  show "root_cond (p,l',r') ?x"
  proof (cases "sgn (ipoly p ?m) = sgn (ipoly p r)")
    case *: False
    with res sr have id: "l' = ?m" "r' = r" unfolding d by auto
    from *[unfolded le] urD show ?thesis unfolding id by auto
  next
    case *: True 
    with res sr have id: "l' = l" "r' = ?m" unfolding d by auto
    from *[unfolded le] urD show ?thesis unfolding id by auto
  qed
qed

partial_function (tailrec) tighten_poly_bounds_epsilon :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<times> rat \<times> rat" where
  [code]: "tighten_poly_bounds_epsilon l r sr = (if r - l \<le> x then (l,r,sr) else
    (case tighten_poly_bounds l r sr of (l',r',sr') \<Rightarrow> tighten_poly_bounds_epsilon l' r' sr'))"
    
partial_function (tailrec) tighten_poly_bounds_for_x :: "rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow>
  rat \<times> rat \<times> rat" where 
  [code]: "tighten_poly_bounds_for_x l r sr = (if x < l \<or> r < x then (l, r, sr) else
     (case tighten_poly_bounds l r sr of (l',r',sr') \<Rightarrow> tighten_poly_bounds_for_x l' r' sr'))"

lemma tighten_poly_bounds_epsilon:
  assumes ur: "unique_root (p,l,r)"
  defines u: "u \<equiv> the_unique_root (p,l,r)"
  assumes p: "poly_cond2 p"
      and res: "tighten_poly_bounds_epsilon l r sr = (l',r',sr')"
      and sr: "sr = sgn (ipoly p r)" 
      and x: "x > 0"
  shows "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "r' - l' \<le> x" "sr' = sgn (ipoly p r')" 
proof -
  let ?u = "the_unique_root (p,l,r)"
  define delta where "delta = x / 2"
  have delta: "delta > 0" unfolding delta_def using x by auto
  let ?dist = "\<lambda> (l,r,sr). r - l"
  let ?rel = "inv_image {(x, y). 0 \<le> y \<and> delta_gt delta x y} ?dist"
  note SN = SN_inv_image[OF delta_gt_SN[OF delta], of ?dist]
  note simps = res[unfolded tighten_poly_bounds_for_x.simps[of l r]]
  let ?P = "\<lambda> (l,r,sr). unique_root (p,l,r) \<longrightarrow> u = the_unique_root (p,l,r) 
    \<longrightarrow> tighten_poly_bounds_epsilon l r sr = (l',r',sr') 
    \<longrightarrow> sr = sgn (ipoly p r)
    \<longrightarrow> l \<le> l' \<and> r' \<le> r \<and> r' - l' \<le> x \<and> root_cond (p,l',r') u \<and> sr' = sgn (ipoly p r')"
  have "?P (l,r,sr)"
  proof (induct rule: SN_induct[OF SN])
    case (1 lr)
    obtain l r sr where lr: "lr = (l,r,sr)" by (cases lr, auto)
    show ?case unfolding lr split
    proof (intro impI)
      assume ur: "unique_root (p, l, r)"
        and u: "u = the_unique_root (p, l, r)"
        and res: "tighten_poly_bounds_epsilon l r sr = (l', r', sr')"
        and sr: "sr = sgn (ipoly p r)" 
      note tur = unique_rootD[OF ur]
      note simps = tighten_poly_bounds_epsilon.simps[of l r sr]
      show "l \<le> l' \<and> r' \<le> r \<and> r' - l' \<le> x \<and> root_cond (p, l', r') u \<and> sr' = sgn (ipoly p r')"
      proof (cases "r - l \<le> x")
        case True
        with res[unfolded simps] ur tur(4) u sr
        show ?thesis by auto
      next
        case False 
        hence x: "r - l > x" by auto
        let ?tight = "tighten_poly_bounds l r sr"
        obtain L R SR where tight: "?tight = (L,R,SR)" by (cases ?tight, auto)
        note tighten = tighten_poly_bounds[OF tight[unfolded sr] ur p]
        from unique_root_sub_interval[OF ur tighten(1-2,4)] p
        have ur': "unique_root (p,L,R)" "u = the_unique_root (p,L,R)" unfolding u by auto
        from res[unfolded simps tight] False sr have "tighten_poly_bounds_epsilon L R SR = (l',r',sr')" by auto
        note IH = 1[of "(L,R,SR)", unfolded tight split lr, rule_format, OF _ ur' this]
        have "L \<le> l' \<and> r' \<le> R \<and> r' - l' \<le> x \<and> root_cond (p, l', r') u \<and> sr' = sgn (ipoly p r')"
          by (rule IH, insert tighten False, auto simp: delta_gt_def delta_def)
        thus ?thesis using tighten by auto
      qed
    qed
  qed
  from this[unfolded split u, rule_format, OF ur refl res sr] 
  show "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "r' - l' \<le> x" "sr' = sgn (ipoly p r')" using u by auto
qed

lemma tighten_poly_bounds_for_x:
  assumes ur: "unique_root (p,l,r)"
  defines u: "u \<equiv> the_unique_root (p,l,r)"
  assumes p: "poly_cond2 p" 
      and res: "tighten_poly_bounds_for_x l r sr = (l',r',sr')"
      and sr: "sr = sgn (ipoly p r)" 
  shows "l \<le> l'" "l' \<le> r'" "r' \<le> r" "root_cond (p,l',r') u" "\<not> (l' \<le> x \<and> x \<le> r')" "sr' = sgn (ipoly p r')" "unique_root (p,l',r')"
proof -
  let ?u = "the_unique_root (p,l,r)"
  let ?x = "real_of_rat x"
  define delta where "delta = abs ((u - ?x) / 2)"
  let ?p = "real_of_int_poly p"
  note ru = unique_rootD[OF ur]
  {
    assume "u = ?x"
    note u = this[unfolded u]
    from poly_cond2_no_rat_root[OF p] ur have False by (elim unique_rootE, auto simp: u)
  }
  hence delta: "delta > 0" unfolding delta_def by auto
  let ?dist = "\<lambda> (l,r,sr). real_of_rat (r - l)"
  let ?rel = "inv_image {(x, y). 0 \<le> y \<and> delta_gt delta x y} ?dist"
  note SN = SN_inv_image[OF delta_gt_SN[OF delta], of ?dist]
  note simps = res[unfolded tighten_poly_bounds_for_x.simps[of l r]]
  let ?P = "\<lambda> (l,r,sr). unique_root (p,l,r) \<longrightarrow> u = the_unique_root (p,l,r) 
    \<longrightarrow> tighten_poly_bounds_for_x l r sr = (l',r',sr') 
    \<longrightarrow> sr = sgn (ipoly p r)
    \<longrightarrow> l \<le> l' \<and> r' \<le> r \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p,l',r') u \<and> sr' = sgn (ipoly p r')"
  have "?P (l,r,sr)"
  proof (induct rule: SN_induct[OF SN])
    case (1 lr)
    obtain l r sr where lr: "lr = (l,r,sr)" by (cases lr, auto)
    let ?l = "real_of_rat l"
    let ?r = "real_of_rat r"
    show ?case unfolding lr split
    proof (intro impI)
      assume ur: "unique_root (p, l, r)"
        and u: "u = the_unique_root (p, l, r)"
        and res: "tighten_poly_bounds_for_x l r sr = (l', r', sr')"
        and sr: "sr = sgn (ipoly p r)" 
      note tur = unique_rootD[OF ur]
      note simps = tighten_poly_bounds_for_x.simps[of l r]
      show "l \<le> l' \<and> r' \<le> r \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p, l', r') u \<and> sr' = sgn (ipoly p r')"
      proof (cases "x < l \<or> r < x")
        case True
        with res[unfolded simps] ur tur(4) u sr
        show ?thesis by auto
      next
        case False 
        hence x: "?l \<le> ?x" "?x \<le> ?r" by (auto simp: of_rat_less_eq)
        let ?tight = "tighten_poly_bounds l r sr"
        obtain L R SR where tight: "?tight = (L,R,SR)" by (cases ?tight, auto)
        note tighten = tighten_poly_bounds[OF tight ur p sr]
        from unique_root_sub_interval[OF ur tighten(1-2,4)] p
        have ur': "unique_root (p,L,R)" "u = the_unique_root (p,L,R)" unfolding u by auto
        from res[unfolded simps tight] False have "tighten_poly_bounds_for_x L R SR = (l',r',sr')" by auto
        note IH = 1[of ?tight, unfolded tight split lr, rule_format, OF _ ur' this]
        let ?DIFF = "real_of_rat (R - L)" let ?diff = "real_of_rat (r - l)"
        have diff0: "0 \<le> ?DIFF" using tighten(3)
          by (metis cancel_comm_monoid_add_class.diff_cancel diff_right_mono of_rat_less_eq of_rat_hom.hom_zero)
        have *: "r - l - (r - l) / 2 = (r - l) / 2" by (auto simp: field_simps)
        have "delta_gt delta ?diff ?DIFF = (abs (u - of_rat x) \<le> real_of_rat (r - l) * 1)"
          unfolding delta_gt_def tighten(5) delta_def of_rat_diff[symmetric] * by (simp add: hom_distribs)
        also have "real_of_rat (r - l) * 1 = ?r - ?l" 
          unfolding of_rat_divide of_rat_mult of_rat_diff by auto
        also have "abs (u - of_rat x) \<le> ?r - ?l" using x ur by (elim unique_rootE, auto simp: u)
        finally have delta: "delta_gt delta ?diff ?DIFF" .
        have "L \<le> l' \<and> r' \<le> R \<and> \<not> (l' \<le> x \<and> x \<le> r') \<and> root_cond (p, l', r') u \<and> sr' = sgn (ipoly p r')"
          by (rule IH, insert delta diff0 tighten(6), auto)
        with \<open>l \<le> L\<close> \<open>R \<le> r\<close> show ?thesis by auto
      qed
    qed
  qed
  from this[unfolded split u, rule_format, OF ur refl res sr] 
  show *: "l \<le> l'" "r' \<le> r" "root_cond (p,l',r') u" "\<not> (l' \<le> x \<and> x \<le> r')" "sr' = sgn (ipoly p r')" unfolding u 
    by auto
  from *(3)[unfolded split] have "real_of_rat l' \<le> of_rat r'" by auto
  thus "l' \<le> r'" unfolding of_rat_less_eq .
  show "unique_root (p,l',r')" using ur *(1-3) p poly_condD(5) u unique_root_sub_interval(1) by blast
qed
end

definition real_alg_precision :: rat where
  "real_alg_precision \<equiv> Rat.Fract 1 2"

lemma real_alg_precision: "real_alg_precision > 0" 
  by eval

definition normalize_bounds_1_main :: "rat \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_1" where
  "normalize_bounds_1_main eps rai = (case rai of (p,l,r) \<Rightarrow>
    let (l',r',sr') = tighten_poly_bounds_epsilon p eps l r (sgn (ipoly p r));
        fr = rat_of_int (floor r');
        (l'',r'',_) = tighten_poly_bounds_for_x p fr l' r' sr'
    in (p,l'',r''))"

definition normalize_bounds_1 :: "real_alg_1 \<Rightarrow> real_alg_1" where 
  "normalize_bounds_1 = (normalize_bounds_1_main real_alg_precision)"

context
  fixes p q and l r :: rat
  assumes cong: "\<And> x. real_of_rat l \<le> x \<Longrightarrow> x \<le> of_rat r \<Longrightarrow> (ipoly p x = (0 :: real)) = (ipoly q x = 0)"
begin
lemma root_cond_cong: "root_cond (p,l,r) = root_cond (q,l,r)"
  by (intro ext, insert cong, auto simp: root_cond_def)

lemma the_unique_root_cong: 
  "the_unique_root (p,l,r) = the_unique_root (q,l,r)"
  unfolding root_cond_cong ..

lemma unique_root_cong: 
  "unique_root (p,l,r) = unique_root (q,l,r)"
  unfolding root_cond_cong ..
end

lemma normalize_bounds_1_main: assumes eps: "eps > 0" and rc: "invariant_1_2 x"
  defines y: "y \<equiv> normalize_bounds_1_main eps x"
  shows "invariant_1_2 y \<and> (real_of_1 y = real_of_1 x)"
proof -
  obtain p l r where x: "x = (p,l,r)" by (cases x) auto
  note rc = rc[unfolded x]
  obtain l' r' sr' where tb: "tighten_poly_bounds_epsilon p eps l r (sgn (ipoly p r)) = (l',r',sr')" 
    by (cases rule: prod_cases3, auto)
  let ?fr = "rat_of_int (floor r')"
  obtain l'' r'' sr'' where tbx: "tighten_poly_bounds_for_x p ?fr l' r' sr' = (l'',r'',sr'')"
    by (cases rule: prod_cases3, auto)
  from y[unfolded normalize_bounds_1_main_def x] tb tbx
  have y: "y = (p, l'', r'')" 
    by (auto simp: Let_def)
  from rc have "unique_root (p, l, r)" and p2: "poly_cond2 p" by auto
  from tighten_poly_bounds_epsilon[OF this tb refl eps]
  have bnd: "l \<le> l'" "r' \<le> r" and rc': "root_cond (p, l', r') (the_unique_root (p, l, r))" 
    and eps: "r' - l' \<le> eps" (* currently not relevant for lemma *)
    and sr': "sr' = sgn (ipoly p r')" by auto
  from invariant_1_sub_interval[OF _ rc' bnd] rc
  have inv': "invariant_1 (p, l', r')" and eq: "real_of_1 (p, l', r') = real_of_1 (p, l, r)" by auto
  have bnd: "l' \<le> l''" "r'' \<le> r'" and rc': "root_cond (p, l'', r'') (the_unique_root (p, l', r'))"
    by (rule tighten_poly_bounds_for_x[OF _ p2 tbx sr'], fact invariant_1D[OF inv'])+
  from invariant_1_sub_interval[OF inv' rc' bnd] p2 eq
  show ?thesis unfolding y x by auto
qed

lemma normalize_bounds_1: assumes x: "invariant_1_2 x"
  shows "invariant_1_2 (normalize_bounds_1 x) \<and> (real_of_1 (normalize_bounds_1 x) = real_of_1 x)" 
proof(cases x)
  case xx:(fields p l r)
  let ?res = "(p,l,r)"
  have norm: "normalize_bounds_1 x = (normalize_bounds_1_main real_alg_precision ?res)" 
    unfolding normalize_bounds_1_def by (simp add: xx)
  from x have x: "invariant_1_2 ?res" "real_of_1 ?res = real_of_1 x" unfolding xx by auto
  from normalize_bounds_1_main[OF real_alg_precision x(1)] x(2-)
  show ?thesis unfolding normalize_bounds_1_def xx by auto
qed
  
lemma normalize_bound_1_poly: "poly_real_alg_1 (normalize_bounds_1 rai) = poly_real_alg_1 rai" 
  unfolding normalize_bounds_1_def normalize_bounds_1_main_def Let_def
  by (auto split: prod.splits)

definition real_alg_2_main :: "root_info \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where 
  "real_alg_2_main ri rai \<equiv> let p = poly_real_alg_1 rai
     in (if degree p = 1 then Rational (Rat.Fract (- coeff p 0) (coeff p 1))
       else (case normalize_bounds_1 rai of (p',l,r) \<Rightarrow>
       Irrational (root_info.number_root ri r) (p',l,r)))"

definition real_alg_2 :: "real_alg_1 \<Rightarrow> real_alg_2" where 
  "real_alg_2 rai \<equiv> let p = poly_real_alg_1 rai
     in (if degree p = 1 then Rational (Rat.Fract (- coeff p 0) (coeff p 1))
       else (case normalize_bounds_1 rai of (p',l,r) \<Rightarrow>
       Irrational (root_info.number_root (root_info p) r) (p',l,r)))"

lemma degree_1_ipoly: assumes "degree p = Suc 0"
  shows "ipoly p x = 0 \<longleftrightarrow> (x = real_of_rat (Rat.Fract (- coeff p 0) (coeff p 1)))"
proof -
  from roots1[of "map_poly real_of_int p"] assms
  have "ipoly p x = 0 \<longleftrightarrow> x \<in> {roots1 (real_of_int_poly p)}" by auto
  also have "\<dots> = (x = real_of_rat (Rat.Fract (- coeff p 0) (coeff p 1)))" 
    unfolding Fract_of_int_quotient roots1_def hom_distribs
    by auto
  finally show ?thesis .
qed

lemma invariant_1_degree_0:
  assumes inv: "invariant_1 rai"
  shows "degree (poly_real_alg_1 rai) \<noteq> 0" (is "degree ?p \<noteq> 0")
proof (rule notI)
  assume deg: "degree ?p = 0"
  from inv have "ipoly ?p (real_of_1 rai) = 0" by auto
  with deg have "?p = 0" by (meson less_Suc0 representsI represents_degree)
  with inv show False by auto
qed

lemma real_alg_2_main:
  assumes inv: "invariant_1 rai"
  defines [simp]: "p \<equiv> poly_real_alg_1 rai"
  assumes ric: "irreducible (poly_real_alg_1 rai) \<Longrightarrow> root_info_cond ri (poly_real_alg_1 rai)" 
  shows "invariant_2 (real_alg_2_main ri rai)" "real_of_2 (real_alg_2_main ri rai) = real_of_1 rai"
proof (atomize(full))
  define l r where [simp]: "l \<equiv> rai_lb rai" and [simp]: "r \<equiv> rai_ub rai"
  show "invariant_2 (real_alg_2_main ri rai) \<and> real_of_2 (real_alg_2_main ri rai) = real_of_1 rai" 
    unfolding id using invariant_1D
  proof (cases "degree p" "Suc 0" rule: linorder_cases)
    case deg: equal
    hence id: "real_alg_2_main ri rai = Rational (Rat.Fract (- coeff p 0) (coeff p 1))" 
      unfolding real_alg_2_main_def Let_def by auto
    note rc = invariant_1D[OF inv]
    from degree_1_ipoly[OF deg, of "the_unique_root rai"] rc(1)
    show ?thesis unfolding id by auto
  next
    case deg: greater
    with inv have inv: "invariant_1_2 rai" unfolding p_def by auto
    define rai' where "rai' = normalize_bounds_1 rai"
    have rai': "real_of_1 rai = real_of_1 rai'" and inv': "invariant_1_2 rai'" 
      unfolding rai'_def using normalize_bounds_1[OF inv] by auto
    obtain p' l' r' where "rai' = (p',l',r')" by (cases rai')
    with arg_cong[OF rai'_def, of poly_real_alg_1, unfolded normalize_bound_1_poly] split
    have split: "rai' = (p,l',r')" by auto
    from inv'[unfolded split]
    have "poly_cond p" by auto
    from poly_condD[OF this] have irr: "irreducible p" by simp
    from ric irr have ric: "root_info_cond ri p" by auto
    have id: "real_alg_2_main ri rai = (Irrational (root_info.number_root ri r') rai')" 
      unfolding real_alg_2_main_def Let_def using deg split rai'_def
      by (auto simp: rai'_def rai')
    show ?thesis unfolding id using rai' root_info_condD(2)[OF ric] 
         inv'[unfolded split]
      apply (elim invariant_1_2E invariant_1E) using inv'
      by(auto simp: split roots_below_the_unique_root)
  next
    case deg: less then have "degree p = 0" by auto
    from this invariant_1_degree_0[OF inv] have "p = 0" by simp
    with inv show ?thesis by auto
  qed
qed

lemma real_alg_2: assumes "invariant_1 rai" 
  shows "invariant_2 (real_alg_2 rai)" "real_of_2 (real_alg_2 rai) = real_of_1 rai"
proof -
  have deg: "0 < degree (poly_real_alg_1 rai)" using assms by auto
  have "real_alg_2 rai = real_alg_2_main (root_info (poly_real_alg_1 rai)) rai" 
    unfolding real_alg_2_def real_alg_2_main_def Let_def by auto
  from real_alg_2_main[OF assms root_info, folded this, simplified] deg
  show "invariant_2 (real_alg_2 rai)" "real_of_2 (real_alg_2 rai) = real_of_1 rai" by auto
qed

lemma invariant_2_realI:
  fixes plr :: real_alg_1
  defines "p \<equiv> poly_real_alg_1 plr" and "l \<equiv> rai_lb plr" and "r \<equiv> rai_ub plr"
  assumes x: "root_cond plr x" and sgn: "sgn l = sgn r"
      and ur: "unique_root plr"
      and p: "poly_cond p"
  shows "invariant_2 (real_alg_2 plr) \<and> real_of_2 (real_alg_2 plr) = x"
  using invariant_1_realI[OF x,folded p_def l_def r_def] sgn ur p
    real_alg_2[of plr] by auto

(* ********************* *)
subsubsection \<open>Comparisons\<close>

fun compare_rat_1 :: "rat \<Rightarrow> real_alg_1 \<Rightarrow> order" where
  "compare_rat_1 x (p,l,r) = (if x < l then Lt else if x > r then Gt else
      if sgn (ipoly p x) = sgn(ipoly p r) then Gt else Lt)" 
  
lemma compare_rat_1: assumes rai: "invariant_1_2 y" 
  shows "compare_rat_1 x y = compare (of_rat x) (real_of_1 y)" 
proof-
  define p l r where "p \<equiv> poly_real_alg_1 y" "l \<equiv> rai_lb y" "r \<equiv> rai_ub y"
  then have y [simp]: "y = (p,l,r)" by (cases y, auto)
  from rai have ur: "unique_root y" by auto
  show ?thesis 
  proof (cases "x < l \<or> x > r")
    case True
    {
      assume xl: "x < l" 
      hence "real_of_rat x < of_rat l" unfolding of_rat_less by auto
      with rai have "of_rat x < the_unique_root y" by (auto elim!: invariant_1E)
      with xl rai have ?thesis by (cases y, auto simp: compare_real_def comparator_of_def)
    }
    moreover
    {
      assume xr: "\<not> x < l" "x > r" 
      hence "real_of_rat x > of_rat r" unfolding of_rat_less by auto
      with rai have "of_rat x > the_unique_root y" by (auto elim!: invariant_1E)
      with xr rai have ?thesis by (cases y, auto simp: compare_real_def comparator_of_def)
    }
    ultimately show ?thesis using True by auto
  next
    case False
    have 0: "ipoly p (real_of_rat x) \<noteq> 0" by (rule poly_cond2_no_rat_root, insert rai, auto)
    with rai have diff: "real_of_1 y \<noteq> of_rat x" by (auto elim!: invariant_1E)
    have "\<And> P. (1 < degree (poly_real_alg_1 y) \<Longrightarrow> \<exists>!x. root_cond y x \<Longrightarrow> poly_cond p \<Longrightarrow> P) \<Longrightarrow> P"
       using poly_real_alg_1.simps y rai invariant_1_2E invariant_1E by metis
    from this[OF gt_rat_sign_change] False
    have left: "compare_rat_1 x y = (if real_of_rat x \<le> the_unique_root y then Lt else Gt)"
      by (auto simp:poly_cond2_def)
    also have "\<dots> = compare (real_of_rat x) (real_of_1 y)" using diff
      by (auto simp: compare_real_def comparator_of_def)
    finally show ?thesis .
  qed
qed
  
lemma cf_pos_0[simp]: "\<not> cf_pos 0" 
  unfolding cf_pos_def by auto


(* ********************* *)
subsubsection\<open>Negation\<close>

fun uminus_1 :: "real_alg_1 \<Rightarrow> real_alg_1" where
  "uminus_1 (p,l,r) = (abs_int_poly (poly_uminus p), -r, -l)"

lemma uminus_1: assumes x: "invariant_1 x"
  defines y: "y \<equiv> uminus_1 x"
  shows "invariant_1 y \<and> (real_of_1 y = - real_of_1 x)"
proof (cases x)
  case plr: (fields p l r)
  from x plr have inv: "invariant_1 (p,l,r)" by auto
  note * = invariant_1D[OF this]
  from plr have x: "x = (p,l,r)" by simp
  let ?p = "poly_uminus p"
  let ?mp = "abs_int_poly ?p"
  have y: "y = (?mp, -r , -l)" 
    unfolding y plr by (simp add: Let_def)
  {
    fix y
    assume "root_cond (?mp, - r, - l) y"
    hence mpy: "ipoly ?mp y = 0" and bnd: "- of_rat r \<le> y" "y \<le> - of_rat l"
      unfolding root_cond_def by (auto simp: of_rat_minus)
    from mpy have id: "ipoly p (- y) = 0" by auto
    from bnd have bnd: "of_rat l \<le> - y" "-y \<le> of_rat r" by auto
    from id bnd have "root_cond (p, l, r) (-y)" unfolding root_cond_def by auto
    with inv x have "real_of_1 x = -y" by (auto intro!: the_unique_root_eqI)
    then have "-real_of_1 x = y" by auto
  } note inj = this
  have rc: "root_cond (?mp, - r, - l) (- real_of_1 x)"
    using * unfolding root_cond_def y x by (auto simp: of_rat_minus sgn_minus_rat)
  from inj rc have ur': "unique_root (?mp, -r, -l)" by (auto intro: unique_rootI)
  with rc have the: "- real_of_1 x = the_unique_root (?mp, -r, -l)" by (auto intro: the_unique_root_eqI)
  have xp: "p represents (real_of_1 x)" using * unfolding root_cond_def split represents_def x by auto
  from * have mon: "lead_coeff ?mp > 0" by (unfold pos_poly_abs_poly, auto)
  from poly_uminus_irreducible * have mi: "irreducible ?mp" by auto
  from mi mon have pc': "poly_cond ?mp" by (auto simp: cf_pos_def)
  from poly_condD[OF pc'] have irr: "irreducible ?mp" by auto
  show ?thesis unfolding y apply (intro invariant_1_realI ur' rc) using pc' inv by auto
qed

lemma uminus_1_2:
  assumes x: "invariant_1_2 x"
  defines y: "y \<equiv> uminus_1 x"
  shows "invariant_1_2 y \<and> (real_of_1 y = - real_of_1 x)"
proof -
  from x have "invariant_1 x" by auto
  from uminus_1[OF this] have *: "real_of_1 y = - real_of_1 x" 
    "invariant_1 y" unfolding y by auto
  obtain p l r where id: "x = (p,l,r)" by (cases x)
  from x[unfolded id] have "degree p > 1" by auto
  moreover have "poly_real_alg_1 y = abs_int_poly (poly_uminus p)"
    unfolding y id uminus_1.simps split Let_def by auto
  ultimately have "degree (poly_real_alg_1 y) > 1" by simp
  with * show ?thesis by auto
qed
  
fun uminus_2 :: "real_alg_2 \<Rightarrow> real_alg_2" where
  "uminus_2 (Rational r) = Rational (-r)"
| "uminus_2 (Irrational n x) = real_alg_2 (uminus_1 x)"

lemma uminus_2: assumes "invariant_2 x" 
  shows "real_of_2 (uminus_2 x) = uminus (real_of_2 x)"
  "invariant_2 (uminus_2 x)"
  using assms real_alg_2 uminus_1 by (atomize(full), cases x, auto simp: hom_distribs)

declare uminus_1.simps[simp del]


lift_definition uminus_3 :: "real_alg_3 \<Rightarrow> real_alg_3" is uminus_2 
  by (auto simp: uminus_2)

lemma uminus_3: "real_of_3 (uminus_3 x) = - real_of_3 x"
  by (transfer, auto simp: uminus_2)
    
instantiation real_alg :: uminus
begin
lift_definition uminus_real_alg :: "real_alg \<Rightarrow> real_alg" is uminus_3
  by (simp add: uminus_3)
instance ..
end

lemma uminus_real_alg: "- (real_of x) = real_of (- x)"
  by (transfer, rule uminus_3[symmetric])

(* ********************* *)
subsubsection\<open>Inverse\<close>

fun inverse_1 :: "real_alg_1 \<Rightarrow> real_alg_2" where
  "inverse_1 (p,l,r) = real_alg_2 (abs_int_poly (reflect_poly p), inverse r, inverse l)"

lemma invariant_1_2_of_rat: assumes rc: "invariant_1_2 rai" 
  shows "real_of_1 rai \<noteq> of_rat x" 
proof -
  obtain p l r where rai: "rai = (p, l, r)" by (cases rai, auto)
  from rc[unfolded rai]
  have "poly_cond2 p" "ipoly p (the_unique_root (p, l, r)) = 0" by (auto elim!: invariant_1E)
  from poly_cond2_no_rat_root[OF this(1), of x] this(2) show ?thesis unfolding rai by auto
qed
  
lemma inverse_1:
  assumes rcx: "invariant_1_2 x"
  defines y: "y \<equiv> inverse_1 x"
  shows "invariant_2 y \<and> (real_of_2 y = inverse (real_of_1 x))"
proof (cases x)
  case x: (fields p l r)
  from x rcx have rcx: "invariant_1_2 (p,l,r)" by auto
  from invariant_1_2_poly_cond2[OF rcx] have pc2: "poly_cond2 p" by simp
  have x0: "real_of_1 (p,l,r) \<noteq> 0" using invariant_1_2_of_rat[OF rcx, of 0] x by auto
  let ?x = "real_of_1 (p,l,r)"
  let ?mp = "abs_int_poly (reflect_poly p)"
  from x0 rcx have lr0: "l \<noteq> 0" and "r \<noteq> 0" by auto
  from x0 rcx have y: "y = real_alg_2 (?mp, inverse r, inverse l)"
    unfolding y x Let_def inverse_1.simps by auto
  from rcx have mon: "lead_coeff ?mp > 0" by (unfold lead_coeff_abs_int_poly, auto)
  {
    fix y
    assume "root_cond (?mp, inverse r, inverse l) y"
    hence mpy: "ipoly ?mp y = 0" and bnd: "inverse (of_rat r) \<le> y" "y \<le> inverse (of_rat l)"
      unfolding root_cond_def by (auto simp: of_rat_inverse)
    from sgn_real_mono[OF bnd(1)] sgn_real_mono[OF bnd(2)] 
    have "sgn (of_rat r) \<le> sgn y" "sgn y \<le> sgn (of_rat l)"
      by (simp_all add: algebra_simps)
    with rcx have sgn: "sgn (inverse (of_rat r)) = sgn y" "sgn y = sgn (inverse (of_rat l))" 
      unfolding sgn_inverse inverse_sgn
      by (auto simp add: real_of_rat_sgn intro: order_antisym)
    from sgn[simplified, unfolded real_of_rat_sgn] lr0 have "y \<noteq> 0" by (auto simp:sgn_0_0)
    with mpy have id: "ipoly p (inverse y) = 0" by (auto simp: ipoly_reflect_poly)
    from inverse_le_sgn[OF sgn(1) bnd(1)] inverse_le_sgn[OF sgn(2) bnd(2)]
    have bnd: "of_rat l \<le> inverse y" "inverse y \<le> of_rat r" by auto
    from id bnd have "root_cond (p,l,r) (inverse y)" unfolding root_cond_def by auto
    from rcx this x0 have "?x = inverse y" by auto
    then have "inverse ?x = y" by auto
  } note inj = this
  have rc: "root_cond (?mp, inverse r, inverse l) (inverse ?x)"
    using rcx x0 apply (elim invariant_1_2E invariant_1E)
    by (simp add: root_cond_def of_rat_inverse real_of_rat_sgn inverse_le_iff_sgn ipoly_reflect_poly)
  from inj rc have ur: "unique_root (?mp, inverse r, inverse l)" by (auto intro: unique_rootI)
  with rc have the: "the_unique_root (?mp, inverse r, inverse l) = inverse ?x" by (auto intro: the_unique_root_eqI)
  have xp: "p represents ?x" unfolding split represents_def using rcx by (auto elim!: invariant_1E)
  from reflect_poly_irreducible[OF _ xp x0] poly_condD rcx
  have mi: "irreducible ?mp" by auto
  from mi mon have un: "poly_cond ?mp" by (auto simp: poly_cond_def)
  show ?thesis using rcx rc ur unfolding y
    by (intro invariant_2_realI, auto simp: x y un)
qed
  
fun inverse_2 :: "real_alg_2 \<Rightarrow> real_alg_2" where
  "inverse_2 (Rational r) = Rational (inverse r)"
| "inverse_2 (Irrational n x) = inverse_1 x"

lemma inverse_2: assumes "invariant_2 x"
  shows "real_of_2 (inverse_2 x) = inverse (real_of_2 x)"
  "invariant_2 (inverse_2 x)"
    using assms
    by (atomize(full), cases x, auto simp: real_alg_2 inverse_1 hom_distribs)

lift_definition inverse_3 :: "real_alg_3 \<Rightarrow> real_alg_3" is inverse_2 
  by (auto simp: inverse_2)

lemma inverse_3: "real_of_3 (inverse_3 x) = inverse (real_of_3 x)"
  by (transfer, auto simp: inverse_2)
  

(* ********************* *)
subsubsection\<open>Floor\<close>

fun floor_1 :: "real_alg_1 \<Rightarrow> int" where
  "floor_1 (p,l,r) = (let
    (l',r',sr') = tighten_poly_bounds_epsilon p (1/2) l r (sgn (ipoly p r));
    fr = floor r';
    fl = floor l';
    fr' = rat_of_int fr
    in (if fr = fl then fr else
    let (l'',r'',sr'') = tighten_poly_bounds_for_x p fr' l' r' sr'
    in if fr' < l'' then fr else fl))"

lemma floor_1: assumes "invariant_1_2 x"
  shows "floor (real_of_1 x) = floor_1 x"
proof (cases x)
  case (fields p l r)
  obtain l' r' sr' where tbe: "tighten_poly_bounds_epsilon p (1 / 2) l r (sgn (ipoly p r)) = (l',r',sr')" 
    by (cases rule: prod_cases3, auto)    
  let ?fr = "floor r'"
  let ?fl = "floor l'"
  let ?fr' = "rat_of_int ?fr"
  obtain l'' r'' sr'' where tbx: "tighten_poly_bounds_for_x p ?fr' l' r' sr' = (l'',r'',sr'')" 
    by (cases rule: prod_cases3, auto)    
  note rc = assms[unfolded fields]
  hence rc1: "invariant_1 (p,l,r)" by auto
  have id: "floor_1 x = ((if ?fr = ?fl then ?fr 
    else if ?fr' < l'' then ?fr else ?fl))"
    unfolding fields floor_1.simps tbe Let_def split tbx by simp
  let ?x = "real_of_1 x" 
  have x: "?x = the_unique_root (p,l,r)" unfolding fields by simp
  have bnd: "l \<le> l'" "r' \<le> r" "r' - l' \<le> 1 / 2"
    and rc': "root_cond (p, l', r') (the_unique_root (p, l, r))" 
    and sr': "sr' = sgn (ipoly p r')"
    by (atomize(full), intro conjI tighten_poly_bounds_epsilon[OF _ _ tbe refl],insert rc,auto elim!: invariant_1E)
  let ?r = real_of_rat
  from rc'[folded x, unfolded split]
  have ineq: "?r l' \<le> ?x" "?x \<le> ?r r'" "?r l' \<le> ?r r'" by auto
  hence lr': "l' \<le> r'" unfolding of_rat_less_eq by simp
  have flr: "?fl \<le> ?fr"
    by (rule floor_mono[OF lr'])
  from invariant_1_sub_interval[OF rc1 rc' bnd(1,2)] 
  have rc': "invariant_1 (p, l', r')"
    and id': "the_unique_root (p, l', r') = the_unique_root (p, l, r)" by auto
  with rc have rc2': "invariant_1_2 (p, l', r')" by auto
  have x: "?x = the_unique_root (p,l',r')"
    unfolding fields using id' by simp
  {
    assume "?fr \<noteq> ?fl"
    with flr have flr: "?fl \<le> ?fr - 1" by simp
    have "?fr' \<le> r'"  "l' \<le> ?fr'" using flr bnd by linarith+
  } note fl_diff = this
  show ?thesis
  proof (cases "?fr = ?fl")
    case True
    hence id1: "floor_1 x = ?fr" unfolding id by auto
    from True have id: "floor (?r l') = floor (?r r')" unfolding real_of_rat_floor by simp
    have "floor ?x \<le> floor (?r r')"
      by (rule floor_mono[OF ineq(2)])
    moreover have "floor (?r l') \<le> floor ?x"
      by (rule floor_mono[OF ineq(1)])
    ultimately have "floor ?x = floor (?r r')" unfolding id by simp
    thus ?thesis unfolding id1 real_of_rat_floor .
  next
    case False
    with id have id: "floor_1 x = (if ?fr' < l'' then ?fr else ?fl)" by simp
    from rc2' have "unique_root (p,l',r')" "poly_cond2 p" by auto
    from tighten_poly_bounds_for_x[OF this tbx sr']
    have ineq': "l' \<le> l''" "r'' \<le> r'" and lr'': "l'' \<le> r''" and rc'': "root_cond (p,l'',r'') ?x"
      and fr': "\<not> (l'' \<le> ?fr' \<and> ?fr' \<le> r'')" unfolding x by auto
    from rc''[unfolded split]
    have ineq'': "?r l'' \<le> ?x" "?x \<le> ?r r''" by auto
    from False have "?fr \<noteq> ?fl" by auto
    note fr = fl_diff[OF this]
    show ?thesis
    proof (cases "?fr' < l''")
      case True
      with id have id: "floor_1 x = ?fr" by simp 
      have "floor ?x \<le> ?fr" using floor_mono[OF ineq(2)] by simp
      moreover
      from True have "?r ?fr' < ?r l''" unfolding of_rat_less .
      with ineq''(1) have "?r ?fr' \<le> ?x" by simp
      from floor_mono[OF this]
      have "?fr \<le> floor ?x" by simp 
      ultimately show ?thesis unfolding id by auto
    next
      case False
      with id have id: "floor_1 x = ?fl" by simp
      from False have "l'' \<le> ?fr'" by auto
      from floor_mono[OF ineq(1)] have "?fl \<le> floor ?x" by simp
      moreover have "floor ?x \<le> ?fl"
      proof -
        from False fr' have fr': "r'' < ?fr'" by auto
        hence "floor r'' < ?fr" by linarith
        with floor_mono[OF ineq''(2)] 
        have "floor ?x \<le> ?fr - 1" by auto
        also have "?fr - 1 = floor (r' - 1)" by simp
        also have "\<dots> \<le> ?fl"
          by (rule floor_mono, insert bnd, auto)
        finally show ?thesis .
      qed
      ultimately show ?thesis unfolding id by auto
    qed
  qed
qed

(* ********************* *)
subsubsection\<open>Generic Factorization and Bisection Framework\<close>

lemma card_1_Collect_ex1: assumes "card (Collect P) = 1"
  shows "\<exists>! x. P x"
proof -
  from assms[unfolded card_eq_1_iff] obtain x where "Collect P = {x}" by auto
  thus ?thesis
    by (intro ex1I[of _ x], auto)
qed

fun sub_interval :: "rat \<times> rat \<Rightarrow> rat \<times> rat \<Rightarrow> bool" where
  "sub_interval (l,r) (l',r') = (l' \<le> l \<and> r \<le> r')"

fun in_interval :: "rat \<times> rat \<Rightarrow> real \<Rightarrow> bool" where 
  "in_interval (l,r) x = (of_rat l \<le> x \<and> x \<le> of_rat r)" 

definition converges_to :: "(nat \<Rightarrow> rat \<times> rat) \<Rightarrow> real \<Rightarrow> bool" where
  "converges_to f x \<equiv> (\<forall> n. in_interval (f n) x \<and> sub_interval (f (Suc n)) (f n))
   \<and> (\<forall> (eps :: real) > 0. \<exists> n l r. f n = (l,r) \<and> of_rat r - of_rat l \<le> eps)"

context
  fixes bnd_update :: "'a \<Rightarrow> 'a" 
  and bnd_get :: "'a \<Rightarrow> rat \<times> rat"
begin

definition at_step :: "(nat \<Rightarrow> rat \<times> rat) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool" where
  "at_step f n a \<equiv> \<forall> i. bnd_get ((bnd_update ^^ i) a) = f (n + i)"

partial_function (tailrec) select_correct_factor_main
  :: "'a \<Rightarrow> (int poly \<times> root_info)list \<Rightarrow> (int poly \<times> root_info)list
    \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> nat \<Rightarrow> (int poly \<times> root_info) \<times> rat \<times> rat" where
  [code]: "select_correct_factor_main bnd todo old l r n = (case todo of Nil
    \<Rightarrow> if n = 1 then (hd old, l, r) else let bnd' = bnd_update bnd in (case bnd_get bnd' of (l,r) \<Rightarrow> 
      select_correct_factor_main bnd' old [] l r 0)
   | Cons (p,ri) todo \<Rightarrow> let m = root_info.l_r ri l r in 
      if m = 0 then select_correct_factor_main bnd todo old l r n
      else select_correct_factor_main bnd todo ((p,ri) # old) l r (n + m))"

definition select_correct_factor :: "'a \<Rightarrow> (int poly \<times> root_info)list \<Rightarrow>
    (int poly \<times> root_info) \<times> rat \<times> rat" where
  "select_correct_factor init polys = (case bnd_get init of (l,r) \<Rightarrow>
    select_correct_factor_main init polys [] l r 0)"

lemma select_correct_factor_main: assumes conv: "converges_to f x"
  and at: "at_step f i a"
  and res: "select_correct_factor_main a todo old l r n = ((q,ri_fin),(l_fin,r_fin))"
  and bnd: "bnd_get a = (l,r)"
  and ri: "\<And> q ri. (q,ri) \<in> set todo \<union> set old \<Longrightarrow> root_info_cond ri q"
  and q0: "\<And> q ri. (q,ri) \<in> set todo \<union> set old \<Longrightarrow> q \<noteq> 0"
  and ex: "\<exists>q. q \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q x = 0"
  and dist: "distinct (map fst (todo @ old))"
  and old: "\<And> q ri. (q,ri) \<in> set old \<Longrightarrow> root_info.l_r ri l r \<noteq> 0"
  and un: "\<And> x :: real. (\<exists>q. q \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q x = 0) \<Longrightarrow> 
    \<exists>!q. q \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q x = 0"
  and n: "n = sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old)"
  shows "unique_root (q,l_fin,r_fin) \<and> (q,ri_fin) \<in> set todo \<union> set old \<and> x = the_unique_root (q,l_fin,r_fin)"
proof -
  define orig where "orig = set todo \<union> set old"
  have orig: "set todo \<union> set old \<subseteq> orig" unfolding orig_def by auto
  let ?rts = "{x :: real. \<exists> q ri. (q,ri) \<in> orig \<and> ipoly q x = 0}"
  define rts where "rts = ?rts"
  let ?h = "\<lambda> (x,y). abs (x - y)" 
  let ?r = real_of_rat
  have rts: "?rts = (\<Union> ((\<lambda> (q,ri). {x. ipoly q x = 0}) ` set (todo @ old)))" unfolding orig_def by auto
  have "finite rts" unfolding rts rts_def
    using finite_ipoly_roots[OF q0] finite_set[of "todo @ old"] by auto  
  hence fin: "finite (rts \<times> rts - Id)" by auto   
  define diffs where "diffs = insert 1 {abs (x - y) | x y. x \<in> rts \<and> y \<in> rts \<and> x \<noteq> y}"
  have "finite {abs (x - y) | x y. x \<in> rts \<and> y \<in> rts \<and> x \<noteq> y}"
    by (rule subst[of _ _ finite, OF _ finite_imageI[OF fin, of ?h]], auto)
  hence diffs: "finite diffs" "diffs \<noteq> {}" unfolding diffs_def by auto
  define eps where "eps = Min diffs / 2"
  have "\<And> x. x \<in> diffs \<Longrightarrow> x > 0" unfolding diffs_def by auto
  with Min_gr_iff[OF diffs] have eps: "eps > 0" unfolding eps_def by auto
  note conv = conv[unfolded converges_to_def] 
  from conv eps obtain N L R where 
    N: "f N = (L,R)" "?r R - ?r L \<le> eps" by auto
  obtain pair where pair: "pair = (todo,i)" by auto
  define rel where "rel = measures [ \<lambda> (t,i). N - i, \<lambda> (t :: (int poly \<times> root_info) list,i). length t]"
  have wf: "wf rel" unfolding rel_def by simp
  show ?thesis
    using at res bnd ri q0 ex dist old un n pair orig
  proof (induct pair arbitrary: todo i old a l r n rule: wf_induct[OF wf])
    case (1 pair todo i old a l r n)
    note IH = 1(1)[rule_format]
    note at = 1(2)
    note res = 1(3)[unfolded select_correct_factor_main.simps[of _ todo]]
    note bnd = 1(4)
    note ri = 1(5)
    note q0 = 1(6)
    note ex = 1(7)
    note dist = 1(8)
    note old = 1(9)
    note un = 1(10)
    note n = 1(11)
    note pair = 1(12)
    note orig = 1(13)
    from at[unfolded at_step_def, rule_format, of 0] bnd have fi: "f i = (l,r)" by auto
    with conv have inx: "in_interval (f i) x" by blast
    hence lxr: "?r l \<le> x" "x \<le> ?r r" unfolding fi by auto
    from order.trans[OF this] have lr: "l \<le> r" unfolding of_rat_less_eq .
    show ?case 
    proof (cases todo)
      case (Cons rri tod)
      obtain s ri where rri: "rri = (s,ri)" by force
      with Cons have todo: "todo = (s,ri) # tod" by simp
      note res = res[unfolded todo list.simps split Let_def]
      from root_info_condD(1)[OF ri[of s ri, unfolded todo] lr]
      have ri': "root_info.l_r ri l r = card {x. root_cond (s, l, r) x}" by auto
      from q0 have s0: "s \<noteq> 0" unfolding todo by auto
      from finite_ipoly_roots[OF s0] have fins: "finite {x. root_cond (s, l, r) x}" 
        unfolding root_cond_def by auto
      have rel: "((tod,i), pair) \<in> rel" unfolding rel_def pair todo by simp
      show ?thesis
      proof (cases "root_info.l_r ri l r = 0")
        case True
        with res have res: "select_correct_factor_main a tod old l r n = ((q, ri_fin), l_fin, r_fin)" by auto
        from ri'[symmetric, unfolded True] fins have empty: "{x. root_cond (s, l, r) x} = {}" by simp
        from ex lxr empty have ex': "(\<exists>q. q \<in> fst ` set tod \<union> fst ` set old \<and> ipoly q x = 0)"
          unfolding todo root_cond_def split by auto
        have "unique_root (q, l_fin, r_fin) \<and> (q, ri_fin) \<in> set tod \<union> set old \<and> 
          x = the_unique_root (q, l_fin, r_fin)"
        proof (rule IH[OF rel at res bnd ri _ ex' _ _ _ n refl], goal_cases)
          case (5 y) thus ?case using un[of y] unfolding todo by auto
        next
          case 2 thus ?case using q0 unfolding todo by auto
        qed (insert dist old orig, auto simp: todo)
        thus ?thesis unfolding todo by auto
      next
        case False
        with res have res: "select_correct_factor_main a tod ((s, ri) # old) l r 
          (n + root_info.l_r ri l r) = ((q, ri_fin), l_fin, r_fin)" by auto
        from ex have ex': "\<exists>q. q \<in> fst ` set tod \<union> fst ` set ((s, ri) # old) \<and> ipoly q x = 0"
          unfolding todo by auto
        from dist have dist: "distinct (map fst (tod @ (s, ri) # old))" unfolding todo by auto
        have id: "set todo \<union> set old = set tod \<union> set ((s, ri) # old)" unfolding todo by simp
        show ?thesis unfolding id
        proof (rule IH[OF rel at res bnd ri _ ex' dist], goal_cases)
          case 4 thus ?case using un unfolding todo by auto
        qed (insert old False orig, auto simp: q0 todo n)
      qed
    next
      case Nil
      note res = res[unfolded Nil list.simps Let_def]
      from ex[unfolded Nil] lxr obtain s where "s \<in> fst ` set old \<and> root_cond (s,l,r) x"
        unfolding root_cond_def by auto
      then obtain q1 ri1 old' where old': "old = (q1,ri1) # old'" using id by (cases old, auto)
      let ?ri = "root_info.l_r ri1 l r"
      from old[unfolded old'] have 0: "?ri \<noteq> 0" by auto
      from n[unfolded old'] 0 have n0: "n \<noteq> 0" by auto
      from ri[unfolded old'] have ri': "root_info_cond ri1 q1" by auto
      show ?thesis
      proof (cases "n = 1")
        case False
        with n0 have n1: "n > 1" by auto
        obtain l' r' where bnd': "bnd_get (bnd_update a) = (l',r')" by force        
        with res False have res: "select_correct_factor_main (bnd_update a) old [] l' r' 0 =
          ((q, ri_fin), l_fin, r_fin)" by auto
        have at': "at_step f (Suc i) (bnd_update a)" unfolding at_step_def
        proof (intro allI, goal_cases)
          case (1 n)
          have id: "(bnd_update ^^ Suc n) a = (bnd_update ^^ n) (bnd_update a)"
            by (induct n, auto)
          from at[unfolded at_step_def, rule_format, of "Suc n"]
          show ?case unfolding id by simp
        qed
        from 0[unfolded root_info_condD(1)[OF ri' lr]] obtain y1 where y1: "root_cond (q1,l,r) y1" 
          by (cases "Collect (root_cond (q1, l, r)) = {}", auto)
        from n1[unfolded n old'] 
        have "?ri > 1 \<or> sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old') \<noteq> 0"
          by (cases "sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old')", auto)
        hence "\<exists> q2 ri2 y2. (q2,ri2) \<in> set old \<and> root_cond (q2,l,r) y2 \<and> y1 \<noteq> y2"
        proof
          assume "?ri > 1"
          with root_info_condD(1)[OF ri' lr] have "card {x. root_cond (q1, l, r) x} > 1" by simp
          from card_gt_1D[OF this] y1 obtain y2 where "root_cond (q1,l,r) y2" and "y1 \<noteq> y2" by auto
          thus ?thesis unfolding old' by auto
        next
          assume "sum_list (map (\<lambda> (q,ri). root_info.l_r ri l r) old') \<noteq> 0"
          then obtain q2 ri2 where mem: "(q2,ri2) \<in> set old'" and ri2: "root_info.l_r ri2 l r \<noteq> 0" by auto
          with q0 ri have "root_info_cond ri2 q2" unfolding old' by auto
          from ri2[unfolded root_info_condD(1)[OF this lr]] obtain y2 where y2: "root_cond (q2,l,r) y2"
            by (cases "Collect (root_cond (q2, l, r)) = {}", auto)
          from dist[unfolded old'] split_list[OF mem] have diff: "q1 \<noteq> q2" by auto
          from y1 have q1: "q1 \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q1 y1 = 0"
            unfolding old' root_cond_def by auto
          from y2 have q2: "q2 \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q2 y2 = 0"
            unfolding old' root_cond_def using mem by force
          have "y1 \<noteq> y2"
          proof
            assume id: "y1 = y2"
            from q1 have "\<exists> q1. q1 \<in> fst ` set todo \<union> fst ` set old \<and> ipoly q1 y1 = 0" by blast
            from un[OF this] q1 q2[folded id] have "q1 = q2" by auto
            with diff show False by simp
          qed
          with mem y2 show ?thesis unfolding old' by auto
        qed
        then obtain q2 ri2 y2 where 
          mem2: "(q2,ri2) \<in> set old" and y2: "root_cond (q2,l,r) y2" and diff: "y1 \<noteq> y2" by auto
        from mem2 orig have "(q1,ri1) \<in> orig" "(q2,ri2) \<in> orig"  unfolding old' by auto
        with y1 y2 diff have "abs (y1 - y2) \<in> diffs" unfolding diffs_def rts_def root_cond_def by auto
        from Min_le[OF diffs(1) this] have "abs (y1 - y2) \<ge> 2 * eps" unfolding eps_def by auto
        with eps have eps: "abs (y1 - y2) > eps" by auto
        from y1 y2 have l: "of_rat l \<le> min y1 y2" unfolding root_cond_def by auto
        from y1 y2 have r: "of_rat r \<ge> max y1 y2" unfolding root_cond_def by auto
        from l r eps have eps: "of_rat r - of_rat l > eps" by auto
        have "i < N" 
        proof (rule ccontr)
          assume "\<not> i < N"
          hence "\<exists> k. i = N + k" by presburger
          then obtain k where i: "i = N + k" by auto
          {
            fix k l r
            assume "f (N + k) = (l,r)"
            hence "of_rat r - of_rat l \<le> eps"
            proof (induct k arbitrary: l r)
              case 0
              with N show ?case by auto
            next
              case (Suc k l r)
              obtain l' r' where f: "f (N + k) = (l',r')" by force
              from Suc(1)[OF this] have IH: "?r r' - ?r l' \<le> eps" by auto
              from f Suc(2) conv[THEN conjunct1, rule_format, of "N + k"] 
              have "?r l \<ge> ?r l'" "?r r \<le> ?r r'"
                by (auto simp: of_rat_less_eq)
              thus ?case using IH by auto
            qed
          } note * = this
          from at[unfolded at_step_def i, rule_format, of 0] bnd  have "f (N + k) = (l,r)" by auto
          from *[OF this] eps
          show False by auto
        qed
        hence rel: "((old, Suc i), pair) \<in> rel" unfolding pair rel_def by auto
        from dist have dist: "distinct (map fst (old @ []))" unfolding Nil by auto
        have id: "set todo \<union> set old = set old \<union> set []" unfolding Nil by auto
        show ?thesis unfolding id
        proof (rule IH[OF rel at' res bnd' ri _ _ dist _ _ _ refl], goal_cases)
          case 2 thus ?case using q0 by auto
        qed (insert ex un orig Nil, auto)
      next
        case True
        with res old' have id: "q = q1" "ri_fin = ri1" "l_fin = l" "r_fin = r" by auto
        from n[unfolded True old'] 0 have 1: "?ri = 1" 
          by (cases ?ri; cases "?ri - 1", auto)
        from root_info_condD(1)[OF ri' lr] 1 have "card {x. root_cond (q1,l,r) x} = 1" by auto
        from card_1_Collect_ex1[OF this]
        have unique: "unique_root (q1,l,r)" .
        from ex[unfolded Nil old'] consider (A) "ipoly q1 x = 0" 
          | (B) q where "q \<in> fst ` set old'" "ipoly q x = 0" by auto
        hence "x = the_unique_root (q1,l,r)"
        proof (cases)
          case A
          with lxr have "root_cond (q1,l,r) x" unfolding root_cond_def by auto
          from the_unique_root_eqI[OF unique this] show ?thesis by simp
        next
          case (B q)
          with lxr have "root_cond (q,l,r) x" unfolding root_cond_def by auto
          hence empty: "{x. root_cond (q,l,r) x} \<noteq> {}" by auto
          from B(1) obtain ri' where mem: "(q,ri') \<in> set old'" by force
          from q0[unfolded old'] mem have q0: "q \<noteq> 0" by auto
          from finite_ipoly_roots[OF this] have "finite {x. root_cond (q,l,r) x}" 
            unfolding root_cond_def by auto
          with empty have card: "card {x. root_cond (q,l,r) x} \<noteq> 0" by simp
          from ri[unfolded old'] mem have "root_info_cond ri' q" by auto
          from root_info_condD(1)[OF this lr] card have "root_info.l_r ri' l r \<noteq> 0" by auto
          with n[unfolded True old'] 1 split_list[OF mem] have False by auto
          thus ?thesis by simp
        qed
        thus ?thesis unfolding id using unique ri' unfolding old' by auto
      qed
    qed
  qed
qed

lemma select_correct_factor: assumes 
      conv: "converges_to (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) x"
  and res: "select_correct_factor init polys = ((q,ri),(l,r))"
  and ri: "\<And> q ri. (q,ri) \<in> set polys \<Longrightarrow> root_info_cond ri q"
  and q0: "\<And> q ri. (q,ri) \<in> set polys \<Longrightarrow> q \<noteq> 0"
  and ex: "\<exists>q. q \<in> fst ` set polys \<and> ipoly q x = 0"
  and dist: "distinct (map fst polys)"
  and un: "\<And> x :: real. (\<exists>q. q \<in> fst ` set polys \<and> ipoly q x = 0) \<Longrightarrow> 
    \<exists>!q. q \<in> fst ` set polys \<and> ipoly q x = 0"
  shows "unique_root (q,l,r) \<and> (q,ri) \<in> set polys \<and> x = the_unique_root (q,l,r)"
proof -
  obtain l' r' where init: "bnd_get init = (l',r')" by force
  from res[unfolded select_correct_factor_def init split]
  have res: "select_correct_factor_main init polys [] l' r' 0 = ((q, ri), l, r)" by auto
  have at: "at_step (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) 0 init" unfolding at_step_def by auto
  have "unique_root (q,l,r) \<and> (q,ri) \<in> set polys \<union> set [] \<and> x = the_unique_root (q,l,r)"
    by (rule select_correct_factor_main[OF conv at res init ri], insert dist un ex q0, auto)
  thus ?thesis by auto
qed

definition real_alg_2' :: "root_info \<Rightarrow> int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> real_alg_2" where
  [code del]: "real_alg_2' ri p l r = (
    if degree p = 1 then Rational (Rat.Fract (- coeff p 0) (coeff p 1)) else
    real_alg_2_main ri (case tighten_poly_bounds_for_x p 0 l r (sgn (ipoly p r)) of
              (l',r',sr') \<Rightarrow> (p, l', r')))"

lemma real_alg_2'_code[code]: "real_alg_2' ri p l r =
 (if degree p = 1 then Rational (Rat.Fract (- coeff p 0) (coeff p 1))
     else case normalize_bounds_1
        (case tighten_poly_bounds_for_x p 0 l r (sgn (ipoly p r)) of (l', r', sr') \<Rightarrow> (p, l', r')) 
     of (p', l, r) \<Rightarrow> Irrational (root_info.number_root ri r) (p', l, r))"  
  unfolding real_alg_2'_def real_alg_2_main_def
  by (cases "tighten_poly_bounds_for_x p 0 l r (sgn (ipoly p r))", simp add: Let_def)
    
definition real_alg_2'' :: "root_info \<Rightarrow> int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> real_alg_2" where
  "real_alg_2'' ri p l r = (case normalize_bounds_1
        (case tighten_poly_bounds_for_x p 0 l r (sgn (ipoly p r)) of (l', r', sr') \<Rightarrow> (p, l', r')) 
     of (p', l, r) \<Rightarrow> Irrational (root_info.number_root ri r) (p', l, r))" 

lemma real_alg_2'': "degree p \<noteq> 1 \<Longrightarrow> real_alg_2'' ri p l r = real_alg_2' ri p l r" 
  unfolding real_alg_2'_code real_alg_2''_def by auto
  
lemma poly_cond_degree_0_imp_no_root:
  fixes x :: "'b :: {comm_ring_1,ring_char_0}"
  assumes pc: "poly_cond p" and deg: "degree p = 0" shows "ipoly p x \<noteq> 0"
proof
  from pc have "p \<noteq> 0" by auto
  moreover assume "ipoly p x = 0"
    note poly_zero[OF this]
  ultimately show False using deg by auto
qed

lemma real_alg_2':
  assumes ur: "unique_root (q,l,r)" and pc: "poly_cond q" and ri: "root_info_cond ri q"
  shows "invariant_2 (real_alg_2' ri q l r) \<and> real_of_2 (real_alg_2' ri q l r) = the_unique_root (q,l,r)" (is "_ \<and> _ = ?x")
proof (cases "degree q" "Suc 0" rule: linorder_cases)
  case deg: less
  then have "degree q = 0" by auto
  from poly_cond_degree_0_imp_no_root[OF pc this] ur have False by force
  then show ?thesis by auto
next
  case deg: equal
  hence id: "real_alg_2' ri q l r = Rational (Rat.Fract (- coeff q 0) (coeff q 1))" 
    unfolding real_alg_2'_def by auto
  show ?thesis unfolding id using degree_1_ipoly[OF deg]
    using unique_rootD(4)[OF ur] by auto
next
  case deg: greater
  with pc have pc2: "poly_cond2 q" by auto
  let ?rai = "real_alg_2' ri q l r"
  let ?r = real_of_rat
  obtain l' r' sr' where tight: "tighten_poly_bounds_for_x q 0 l r (sgn (ipoly q r)) = (l',r',sr')" 
    by (cases rule: prod_cases3, auto)
  let ?rai' = "(q, l', r')" 
  have rai': "?rai = real_alg_2_main ri ?rai'"
    unfolding real_alg_2'_def using deg tight by auto
  hence rai: "real_of_1 ?rai' = the_unique_root (q,l',r')" by auto
  note tight = tighten_poly_bounds_for_x[OF ur pc2 tight refl]
  let ?x = "the_unique_root (q, l, r)"
  from tight have tight: "root_cond (q,l',r') ?x" "l \<le> l'" "l' \<le> r'" "r' \<le> r" "l' > 0 \<or> r' < 0" by auto
  from unique_root_sub_interval[OF ur tight(1) tight(2,4)] poly_condD[OF pc]
  have ur': "unique_root (q, l', r')" and x: "?x = the_unique_root (q,l',r')" by auto
  from tight(2-) have sgn: "sgn l' = sgn r'" by auto
  show ?thesis unfolding rai' using real_alg_2_main[of ?rai' ri] invariant_1_realI[of ?rai' ?x]
    by (auto simp: tight(1) sgn pc ri ur')
qed

definition select_correct_factor_int_poly :: "'a \<Rightarrow> int poly \<Rightarrow> real_alg_2" where
  "select_correct_factor_int_poly init p \<equiv> 
     let qs = factors_of_int_poly p;
         polys = map (\<lambda> q. (q, root_info q)) qs;
         ((q,ri),(l,r)) = select_correct_factor init polys
      in real_alg_2' ri q l r"

lemma select_correct_factor_int_poly: assumes 
      conv: "converges_to (\<lambda> i. bnd_get ((bnd_update ^^ i) init)) x"
  and rai: "select_correct_factor_int_poly init p = rai"
  and x: "ipoly p x = 0"
  and p: "p \<noteq> 0"
  shows "invariant_2 rai \<and> real_of_2 rai = x"
proof -
  obtain qs where fact: "factors_of_int_poly p = qs" by auto
  define polys where "polys = map (\<lambda> q. (q, root_info q)) qs"
  obtain q ri l r where res: "select_correct_factor init polys = ((q,ri),(l,r))"
    by (cases "select_correct_factor init polys", auto)
  have fst: "map fst polys = qs" "fst ` set polys = set qs" unfolding polys_def map_map o_def 
    by force+
  note fact' = factors_of_int_poly[OF fact]
  note rai = rai[unfolded select_correct_factor_int_poly_def Let_def fact, 
    folded polys_def, unfolded res split]
  from fact' fst have dist: "distinct (map fst polys)" by auto
  from fact'(2)[OF p, of x] x fst 
  have ex: "\<exists>q. q \<in> fst ` set polys \<and> ipoly q x = 0" by auto
  {
    fix q ri
    assume "(q,ri) \<in> set polys"
    hence ri: "ri = root_info q" and q: "q \<in> set qs" unfolding polys_def by auto
    from fact'(1)[OF q] have *: "lead_coeff q > 0" "irreducible q" "degree q > 0" by auto
    from * have q0: "q \<noteq> 0" by auto
    from root_info[OF *(2-3)] ri have ri: "root_info_cond ri q" by auto
    note ri q0 *
  } note polys = this
  have "unique_root (q, l, r) \<and> (q, ri) \<in> set polys \<and> x = the_unique_root (q, l, r)"
    by (rule select_correct_factor[OF conv res polys(1) _ ex dist, unfolded fst, OF _ _ fact'(3)[OF p]],
    insert fact'(2)[OF p] polys(2), auto)
  hence ur: "unique_root (q,l,r)" and mem: "(q,ri) \<in> set polys" and x: "x = the_unique_root (q,l,r)" by auto
  note polys = polys[OF mem]
  from polys(3-4) have ty: "poly_cond q" by (simp add: poly_cond_def)
  show ?thesis unfolding x rai[symmetric] by (intro real_alg_2' ur ty polys(1))
qed
end

(* ********************* *)
subsubsection\<open>Addition\<close>

lemma ipoly_0_0[simp]: "ipoly f (0::'a::{comm_ring_1,ring_char_0}) = 0 \<longleftrightarrow> poly f 0 = 0"
  unfolding poly_0_coeff_0 by simp

lemma add_rat_roots_below[simp]: "roots_below (poly_add_rat r p) x = (\<lambda>y. y + of_rat r) ` roots_below p (x - of_rat r)"
proof (unfold add_rat_roots image_def, intro Collect_eqI, goal_cases)
  case (1 y) then show ?case by (auto intro: exI[of _ "y - real_of_rat r"])
qed

lemma add_rat_root_cond:
  shows "root_cond (cf_pos_poly (poly_add_rat m p),l,r) x = root_cond (p, l - m, r - m) (x - of_rat m)"
  by (unfold root_cond_def, auto simp add: add_rat_roots hom_distribs)

lemma add_rat_unique_root: "unique_root (cf_pos_poly (poly_add_rat m p), l, r) = unique_root (p, l-m, r-m)"
  by (auto simp: add_rat_root_cond)

fun add_rat_1 :: "rat \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_1" where
  "add_rat_1 r1 (p2,l2,r2) = (
    let p = cf_pos_poly (poly_add_rat r1 p2);
      (l,r,sr) = tighten_poly_bounds_for_x p 0 (l2+r1) (r2+r1) (sgn (ipoly p (r2+r1)))
    in
    (p,l,r))"

lemma poly_real_alg_1_add_rat[simp]:
  "poly_real_alg_1 (add_rat_1 r y) = cf_pos_poly (poly_add_rat r (poly_real_alg_1 y))"
  by (cases y, auto simp: Let_def split: prod.split)

lemma sgn_cf_pos:
  assumes "lead_coeff p > 0" shows "sgn (ipoly (cf_pos_poly p) (x::'a::linordered_field)) = sgn (ipoly p x)"
proof (cases "p = 0")
  case True with assms show ?thesis by auto
next
  case False
  from cf_pos_poly_main False obtain d where p': "Polynomial.smult d (cf_pos_poly p) = p" by auto
  have "d > 0"
  proof (rule zero_less_mult_pos2)
    from False assms have "0 < lead_coeff p" by (auto simp: cf_pos_def)
    also from p' have "\<dots> = d * lead_coeff (cf_pos_poly p)" by (metis lead_coeff_smult)
    finally show "0 < \<dots>".
    show "lead_coeff (cf_pos_poly p) > 0" using False by (unfold lead_coeff_cf_pos_poly)
  qed
  moreover from p' have "ipoly p x = of_int d * ipoly (cf_pos_poly p) x"
    by (fold poly_smult of_int_hom.map_poly_hom_smult, auto)
  ultimately show ?thesis by (auto simp: sgn_mult[where 'a='a])
qed

lemma add_rat_1: fixes r1 :: rat assumes inv_y: "invariant_1_2 y"
  defines "z \<equiv> add_rat_1 r1 y"
  shows "invariant_1_2 z \<and> (real_of_1 z = of_rat r1 + real_of_1 y)"
proof (cases y)
  case y_def: (fields p2 l2 r2)
  define p where "p \<equiv> cf_pos_poly (poly_add_rat r1 p2)"
  obtain l r sr where lr: "tighten_poly_bounds_for_x p 0 (l2+r1) (r2+r1) (sgn (ipoly p (r2+r1))) = (l,r,sr)"
    by (metis surj_pair)
  from lr have z: "z = (p,l,r)" by (auto simp: y_def z_def p_def Let_def)
  from inv_y have ur: "unique_root (p, l2 + r1, r2 + r1)"
    by (auto simp: p_def add_rat_root_cond y_def add_rat_unique_root)
  from inv_y[unfolded y_def invariant_1_2_def,simplified] have pc2: "poly_cond2 p"
    unfolding p_def
    apply (intro poly_cond2I poly_add_rat_irreducible poly_condI, unfold lead_coeff_cf_pos_poly)
    apply (auto elim!: invariant_1E)
   done
  note main = tighten_poly_bounds_for_x[OF ur pc2 lr refl, simplified]
  then have "sgn l = sgn r" unfolding sgn_if apply simp apply linarith done
  from invariant_1_2_realI[OF main(4) _ main(7), simplified, OF this pc2] main(1-3) ur
  show ?thesis by (auto simp: z p_def y_def add_rat_root_cond ex1_the_shift)
qed

fun tighten_poly_bounds_binary :: "int poly \<Rightarrow> int poly \<Rightarrow> (rat \<times> rat \<times> rat) \<times> rat \<times> rat \<times> rat \<Rightarrow> (rat \<times> rat \<times> rat) \<times> rat \<times> rat \<times> rat"  where
  "tighten_poly_bounds_binary cr1 cr2 ((l1,r1,sr1),(l2,r2,sr2)) = 
     (tighten_poly_bounds cr1 l1 r1 sr1, tighten_poly_bounds cr2 l2 r2 sr2)"

lemma tighten_poly_bounds_binary:
  assumes ur: "unique_root (p1,l1,r1)" "unique_root (p2,l2,r2)" and pt: "poly_cond2 p1" "poly_cond2 p2" 
  defines "x \<equiv> the_unique_root (p1,l1,r1)" and "y \<equiv> the_unique_root (p2,l2,r2)"
  assumes bnd: "\<And> l1 r1 l2 r2 l r sr1 sr2. I l1 \<Longrightarrow> I l2 \<Longrightarrow> root_cond (p1,l1,r1) x \<Longrightarrow> root_cond (p2,l2,r2) y \<Longrightarrow>
      bnd ((l1,r1,sr1),(l2,r2,sr2)) = (l,r) \<Longrightarrow> of_rat l \<le> f x y \<and> f x y \<le> of_rat r"
  and approx: "\<And> l1 r1 l2 r2 l1' r1' l2' r2' l l' r r' sr1 sr2 sr1' sr2'. 
    I l1 \<Longrightarrow> I l2 \<Longrightarrow>
    l1 \<le> r1 \<Longrightarrow> l2 \<le> r2 \<Longrightarrow> 
    (l,r) = bnd ((l1,r1,sr1), (l2,r2,sr2)) \<Longrightarrow>
    (l',r') = bnd ((l1',r1',sr1'), (l2',r2',sr2')) \<Longrightarrow>
    (l1',r1') \<in> {(l1,(l1+r1)/2),((l1+r1)/2,r1)} \<Longrightarrow>
    (l2',r2') \<in> {(l2,(l2+r2)/2),((l2+r2)/2,r2)} \<Longrightarrow>
    (r' - l') \<le> 3/4 * (r - l) \<and> l \<le> l' \<and> r' \<le> r"
  and I_mono: "\<And> l l'. I l \<Longrightarrow> l \<le> l' \<Longrightarrow> I l'"
  and I: "I l1" "I l2" 
  and sr: "sr1 = sgn (ipoly p1 r1)" "sr2 = sgn (ipoly p2 r2)"
  shows "converges_to (\<lambda> i. bnd ((tighten_poly_bounds_binary p1 p2 ^^ i) ((l1,r1,sr1),(l2,r2,sr2))))
     (f x y)"
proof -
  let ?upd = "tighten_poly_bounds_binary p1 p2"
  define upd where "upd = ?upd"
  define init where "init = ((l1, r1, sr1), l2, r2, sr2)"
  let ?g = "(\<lambda>i. bnd ((upd ^^ i) init))"
  obtain l r where bnd_init: "bnd init = (l,r)" by force
  note ur1 = unique_rootD[OF ur(1)]
  note ur2 = unique_rootD[OF ur(2)]
  from ur1(4) ur2(4) x_def y_def
  have rc1: "root_cond (p1,l1,r1) x" and rc2: "root_cond (p2,l2,r2) y" by auto
  define g where "g = ?g"
  {
    fix i L1 R1 L2 R2 L R j SR1 SR2
    assume "((upd ^^ i)) init = ((L1,R1,SR1),(L2,R2,SR2))" "g i = (L,R)"
    hence "I L1 \<and> I L2 \<and> root_cond (p1,L1,R1) x \<and> root_cond (p2,L2,R2) y \<and>
      unique_root (p1, L1, R1) \<and> unique_root (p2, L2, R2) \<and> in_interval (L,R) (f x y) \<and> 
      (i = Suc j \<longrightarrow> sub_interval (g i) (g j) \<and> (R - L \<le> 3/4 * (snd (g j) - fst (g j))))
      \<and> SR1 = sgn (ipoly p1 R1) \<and> SR2 = sgn (ipoly p2 R2)"
    proof (induct i arbitrary: L1 R1 L2 R2 L R j SR1 SR2)
      case 0
      thus ?case using I rc1 rc2 ur bnd[of l1 l2 r1 r2 sr1 sr2 L R] g_def sr unfolding init_def by auto
    next
      case (Suc i)
      obtain l1 r1 l2 r2 sr1 sr2 where updi: "(upd ^^ i) init = ((l1, r1, sr1), l2, r2, sr2)" by (cases "(upd ^^ i) init", auto)
      obtain l r where bndi: "bnd ((l1, r1, sr1), l2, r2, sr2) = (l,r)" by force
      hence gi: "g i = (l,r)" using updi unfolding g_def by auto
      have "(upd ^^ Suc i) init = upd ((l1, r1, sr1), l2, r2, sr2)" using updi by simp
      from Suc(2)[unfolded this] have upd: "upd ((l1, r1, sr1), l2, r2, sr2) = ((L1, R1, SR1), L2, R2, SR2)" .
      from upd updi Suc(3) have bndsi: "bnd ((L1, R1, SR1), L2, R2, SR2) = (L,R)" by (auto simp: g_def)
      from Suc(1)[OF updi gi] have I: "I l1" "I l2" 
        and rc: "root_cond (p1,l1,r1) x" "root_cond (p2,l2,r2) y"
        and ur: "unique_root (p1, l1, r1)" "unique_root (p2, l2, r2)"
        and sr: "sr1 = sgn (ipoly p1 r1)" "sr2 = sgn (ipoly p2 r2)" 
        by auto
      from upd[unfolded upd_def] 
      have tight: "tighten_poly_bounds p1 l1 r1 sr1 = (L1, R1, SR1)" "tighten_poly_bounds p2 l2 r2 sr2 = (L2, R2, SR2)"
        by auto
      note tight1 = tighten_poly_bounds[OF tight(1) ur(1) pt(1) sr(1)]
      note tight2 = tighten_poly_bounds[OF tight(2) ur(2) pt(2) sr(2)]
      from tight1 have lr1: "l1 \<le> r1" by auto
      from tight2 have lr2: "l2 \<le> r2" by auto
      note ur1 = unique_rootD[OF ur(1)]
      note ur2 = unique_rootD[OF ur(2)]
      from tight1 I_mono[OF I(1)] have I1: "I L1" by auto
      from tight2 I_mono[OF I(2)] have I2: "I L2" by auto
      note ur1 = unique_root_sub_interval[OF ur(1) tight1(1,2,4)]
      note ur2 = unique_root_sub_interval[OF ur(2) tight2(1,2,4)]
      from rc(1) ur ur1 have x: "x = the_unique_root (p1,L1,R1)" by (auto intro!:the_unique_root_eqI)
      from rc(2) ur ur2 have y: "y = the_unique_root (p2,L2,R2)" by (auto intro!:the_unique_root_eqI)
      from unique_rootD[OF ur1(1)] x have x: "root_cond (p1,L1,R1) x" by auto
      from unique_rootD[OF ur2(1)] y have y: "root_cond (p2,L2,R2) y" by auto
      from tight(1) have half1: "(L1, R1) \<in> {(l1, (l1 + r1) / 2), ((l1 + r1) / 2, r1)}"
        unfolding tighten_poly_bounds_def Let_def by (auto split: if_splits)
      from tight(2) have half2: "(L2, R2) \<in> {(l2, (l2 + r2) / 2), ((l2 + r2) / 2, r2)}"
        unfolding tighten_poly_bounds_def Let_def by (auto split: if_splits)
      from approx[OF I lr1 lr2 bndi[symmetric] bndsi[symmetric] half1 half2]
      have "R - L \<le> 3 / 4 * (r - l) \<and> l \<le> L \<and> R \<le> r" .
      hence "sub_interval (g (Suc i)) (g i)" "R - L \<le> 3/4 * (snd (g i) - fst (g i))" 
        unfolding gi Suc(3) by auto
      with bnd[OF I1 I2 x y bndsi]
      show ?case using I1 I2 x y ur1 ur2 tight1(6) tight2(6) by auto
    qed
  } note invariants = this
  define L where "L = (\<lambda> i. fst (g i))"
  define R where "R = (\<lambda> i. snd (g i))"
  {
    fix i
    obtain l1 r1 l2 r2 sr1 sr2 where updi: "(upd ^^ i) init = ((l1, r1, sr1), l2, r2, sr2)" by (cases "(upd ^^ i) init", auto)
    obtain l r where bnd': "bnd ((l1, r1, sr1), l2, r2, sr2) = (l,r)" by force
    have gi: "g i = (l,r)" unfolding g_def updi bnd' by auto
    hence id: "l = L i" "r = R i" unfolding L_def R_def by auto
    from invariants[OF updi gi[unfolded id]] 
    have "in_interval (L i, R i) (f x y)" 
      "\<And> j. i = Suc j \<Longrightarrow> sub_interval (g i) (g j) \<and> R i - L i \<le> 3 / 4 * (R j - L j)"
      unfolding L_def R_def by auto
  } note * = this
  {
    fix i
    from *(1)[of i] *(2)[of "Suc i", OF refl]
    have "in_interval (g i) (f x y)" "sub_interval (g (Suc i)) (g i)" 
      "R (Suc i) - L (Suc i) \<le> 3 / 4 * (R i - L i)" unfolding L_def R_def by auto
  } note * = this
  show ?thesis unfolding upd_def[symmetric] init_def[symmetric] g_def[symmetric]
    unfolding converges_to_def 
  proof (intro conjI allI impI, rule *(1), rule *(2))
    fix eps :: real
    assume eps: "0 < eps"
    let ?r = real_of_rat 
    define r where "r = (\<lambda> n. ?r (R n))" 
    define l where "l = (\<lambda> n. ?r (L n))"
    define diff where "diff = (\<lambda> n. r n - l n)" 
    {
      fix n
      from *(3)[of n] have "?r (R (Suc n) - L (Suc n)) \<le> ?r (3 / 4 * (R n - L n))"
        unfolding of_rat_less_eq by simp
      also have "?r (R (Suc n) - L (Suc n)) = (r (Suc n) - l (Suc n))"
        unfolding of_rat_diff r_def l_def by simp
      also have "?r (3 / 4 * (R n - L n)) = 3 / 4 * (r n - l n)" 
        unfolding r_def l_def by (simp add: hom_distribs)
      finally have "diff (Suc n) \<le> 3 / 4 * diff n" unfolding diff_def .
    } note * = this
    {
      fix i
      have "diff i \<le> (3/4)^i * diff 0" 
      proof (induct i)
        case (Suc i)
        from Suc *[of i] show ?case by auto
      qed auto
    }
    then obtain c where *: "\<And> i. diff i \<le> (3/4)^i * c" by auto
    have "\<exists> n. diff n \<le> eps"
    proof (cases "c \<le> 0")
      case True
      with *[of 0] eps show ?thesis by (intro exI[of _ 0], auto)
    next
      case False  
      hence c: "c > 0" by auto
      with eps have "inverse c * eps > 0" by auto
      from exp_tends_to_zero[of "3/4 :: real", OF _ _ this] obtain n where 
        "(3/4) ^ n \<le> inverse c * eps" by auto
      from mult_right_mono[OF this, of c] c
      have "(3/4) ^ n * c \<le> eps" by (auto simp: field_simps)
      with *[of n] show ?thesis by (intro exI[of _ n], auto)
    qed
    then obtain n where "?r (R n) - ?r (L n) \<le> eps" unfolding l_def r_def diff_def by blast
    thus "\<exists>n l r. g n = (l, r) \<and> ?r r - ?r l \<le> eps" unfolding L_def R_def by (intro exI[of _ n], force)
  qed
qed

fun add_1 :: "real_alg_1 \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where
  "add_1 (p1,l1,r1) (p2,l2,r2) = (
     select_correct_factor_int_poly
       (tighten_poly_bounds_binary p1 p2)
       (\<lambda> ((l1,r1,sr1),(l2,r2,sr2)). (l1 + l2, r1 + r2))
       ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))) 
       (poly_add p1 p2))"

lemma add_1:
  assumes x: "invariant_1_2 x" and y: "invariant_1_2 y"
  defines z: "z \<equiv> add_1 x y"
  shows "invariant_2 z \<and> (real_of_2 z = real_of_1 x + real_of_1 y)"
proof (cases x)
  case xt: (fields p1 l1 r1)
  show ?thesis
  proof (cases y)
    case yt: (fields p2 l2 r2)
    let ?x = "real_of_1 (p1, l1, r1)"
    let ?y = "real_of_1 (p2, l2, r2)"
    let ?p = "poly_add p1 p2"
    note x = x[unfolded xt]
    note y = y[unfolded yt]
    from x have ax: "p1 represents ?x" unfolding represents_def by (auto elim!: invariant_1E)
    from y have ay: "p2 represents ?y" unfolding represents_def by (auto elim!: invariant_1E)
    let ?bnd = "(\<lambda>((l1, r1, sr1 :: rat), l2 :: rat, r2 :: rat, sr2 :: rat). (l1 + l2, r1 + r2))"
    define bnd where "bnd = ?bnd"
    have "invariant_2 z \<and> real_of_2 z = ?x + ?y"
    proof (intro select_correct_factor_int_poly)
      from represents_add[OF ax ay]
      show "?p \<noteq> 0" "ipoly ?p (?x + ?y) = 0" by auto
      from z[unfolded xt yt]
      show sel: "select_correct_factor_int_poly
          (tighten_poly_bounds_binary p1 p2)
          bnd 
          ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))) 
          (poly_add p1 p2) = z" by (auto simp: bnd_def)
      have ur1: "unique_root (p1,l1,r1)" "poly_cond2 p1" using x by auto
      have ur2: "unique_root (p2,l2,r2)" "poly_cond2 p2" using y by auto
      show "converges_to
        (\<lambda>i. bnd ((tighten_poly_bounds_binary p1 p2 ^^ i)
        ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))))) (?x + ?y)"
        by (intro tighten_poly_bounds_binary ur1 ur2; force simp: bnd_def hom_distribs)
    qed
    thus ?thesis unfolding xt yt .
  qed
qed

declare add_rat_1.simps[simp del]
declare add_1.simps[simp del]

(* ********************* *)
subsubsection\<open>Multiplication\<close>
  
context
begin
private fun mult_rat_1_pos :: "rat \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where
  "mult_rat_1_pos r1 (p2,l2,r2) = real_alg_2 (cf_pos_poly (poly_mult_rat r1 p2), l2*r1, r2*r1)"

private fun mult_1_pos :: "real_alg_1 \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where
  "mult_1_pos (p1,l1,r1) (p2,l2,r2) =
      select_correct_factor_int_poly 
        (tighten_poly_bounds_binary p1 p2)
        (\<lambda> ((l1,r1,sr1),(l2,r2,sr2)). (l1 * l2, r1 * r2))
        ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))) 
        (poly_mult p1 p2)"

fun mult_rat_1 :: "rat \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where
  "mult_rat_1 x y = 
    (if x < 0 then uminus_2 (mult_rat_1_pos (-x) y)
      else if x = 0 then Rational 0 else (mult_rat_1_pos x y))"

fun mult_1 :: "real_alg_1 \<Rightarrow> real_alg_1 \<Rightarrow> real_alg_2" where
  "mult_1 x y = (case (x,y) of ((p1,l1,r1),(p2,l2,r2)) \<Rightarrow>
   if r1 > 0 then
     if r2 > 0 then mult_1_pos x y
     else uminus_2 (mult_1_pos x (uminus_1 y))
   else if r2 > 0 then uminus_2 (mult_1_pos (uminus_1 x) y)
     else mult_1_pos (uminus_1 x) (uminus_1 y))"

lemma mult_rat_1_pos: fixes r1 :: rat assumes r1: "r1 > 0" and y: "invariant_1 y"
  defines z: "z \<equiv> mult_rat_1_pos r1 y"
  shows "invariant_2 z \<and> (real_of_2 z = of_rat r1 * real_of_1 y)" 
proof -
  obtain p2 l2 r2 where yt: "y = (p2,l2,r2)" by (cases y, auto)
  let ?x = "real_of_rat r1"
  let ?y = "real_of_1 (p2, l2, r2)"
  let ?p = "poly_mult_rat r1 p2"
  let ?mp = "cf_pos_poly ?p"
  note y = y[unfolded yt]
  note yD = invariant_1D[OF y]
  from yD r1 have p: "?p \<noteq> 0" and r10: "r1 \<noteq> 0" by auto
  hence mp: "?mp \<noteq> 0" by simp
  from yD(1)
  have rt: "ipoly p2 ?y = 0" and bnd: "of_rat l2 \<le> ?y" "?y \<le> of_rat r2" by auto
  from rt r1 have rt: "ipoly ?mp (?x * ?y) = 0" by (auto simp add: field_simps ipoly_mult_rat[OF r10])
  from yD(5) have irr: "irreducible p2"
    unfolding represents_def using y unfolding root_cond_def split by auto
  from poly_mult_rat_irreducible[OF this _ r10] yD
  have irr: "irreducible ?mp" by simp
  from p have mon: "cf_pos ?mp" by auto
  obtain l r where lr: "l = l2 * r1" "r = r2 * r1" by force
  from bnd r1 have bnd: "of_rat l \<le> ?x * ?y" "?x * ?y \<le> of_rat r" unfolding lr of_rat_mult by auto
  with rt have rc: "root_cond (?mp,l,r) (?x * ?y)" unfolding root_cond_def by auto
  have ur: "unique_root (?mp,l,r)"
  proof (rule ex1I, rule rc)
    fix z
    assume "root_cond (?mp,l,r) z"
    from this[unfolded root_cond_def split] have bndz: "of_rat l \<le> z" "z \<le> of_rat r" 
      and rt: "ipoly ?mp z = 0" by auto
    have "fst (quotient_of r1) \<noteq> 0" using quotient_of_div[of r1] r10 by (cases "quotient_of r1", auto)
    with rt have rt: "ipoly p2 (z * inverse ?x) = 0" by (auto simp: ipoly_mult_rat[OF r10])
    from bndz r1 have "of_rat l2 \<le> z * inverse ?x" "z * inverse ?x \<le> of_rat r2" unfolding lr of_rat_mult
      by (auto simp: field_simps)
    with rt have "root_cond (p2,l2,r2) (z * inverse ?x)" unfolding root_cond_def by auto
    also note invariant_1_root_cond[OF y]
    finally have "?y = z * inverse ?x" by auto
    thus "z = ?x * ?y" using r1 by auto
  qed
  from r1 have sgnr: "sgn r = sgn r2" unfolding lr 
    by (cases "r2 = 0"; cases "r2 < 0"; auto simp: mult_neg_pos mult_less_0_iff)
  from r1 have sgnl: "sgn l = sgn l2" unfolding lr 
    by (cases "l2 = 0"; cases "l2 < 0"; auto simp: mult_neg_pos mult_less_0_iff)
  from the_unique_root_eqI[OF ur rc] have xy: "?x * ?y = the_unique_root (?mp,l,r)" by auto
  from z[unfolded yt, simplified, unfolded Let_def lr[symmetric] split]
  have z: "z = real_alg_2 (?mp, l, r)" by simp
  have yp2: "p2 represents ?y" using yD unfolding root_cond_def split represents_def by auto
  with irr mon have pc: "poly_cond ?mp" by (auto simp: poly_cond_def cf_pos_def)
  have rc: "invariant_1 (?mp, l, r)" unfolding z using yD(2) pc ur 
    by (auto simp add: invariant_1_def ur mp sgnr sgnl)
  show ?thesis unfolding z using real_alg_2[OF rc]
    unfolding yt xy unfolding z by simp
qed

lemma mult_1_pos: assumes x: "invariant_1_2 x" and y: "invariant_1_2 y"
  defines z: "z \<equiv> mult_1_pos x y"
  assumes pos: "real_of_1 x > 0" "real_of_1 y > 0"
  shows "invariant_2 z \<and> (real_of_2 z = real_of_1 x * real_of_1 y)" 
proof -
  obtain p1 l1 r1 where xt: "x = (p1,l1,r1)" by (cases x, auto)
  obtain p2 l2 r2 where yt: "y = (p2,l2,r2)" by (cases y, auto)
  let ?x = "real_of_1 (p1, l1, r1)"
  let ?y = "real_of_1 (p2, l2, r2)"
  let ?r = "real_of_rat"
  let ?p = "poly_mult p1 p2"
  note x = x[unfolded xt]
  note y = y[unfolded yt]
  from x y have basic: "unique_root (p1, l1, r1)" "poly_cond2 p1" "unique_root (p2, l2, r2)" "poly_cond2 p2" by auto
  from basic have irr1: "irreducible p1" and irr2: "irreducible p2" by auto
  from x have ax: "p1 represents ?x" unfolding represents_def by (auto elim!:invariant_1E)
  from y have ay: "p2 represents ?y" unfolding represents_def by (auto elim!:invariant_1E)
  from ax ay pos[unfolded xt yt] have axy: "?p represents (?x * ?y)"
    by (intro represents_mult represents_irr_non_0[OF irr2], auto)
  from representsD[OF this] have p: "?p \<noteq> 0" and rt: "ipoly ?p (?x * ?y) = 0" .
  from x pos(1)[unfolded xt] have "?r r1 > 0" unfolding split by auto
  hence "sgn r1 = 1" unfolding sgn_rat_def by (auto split: if_splits)
  with x have "sgn l1 = 1" by auto
  hence l1_pos: "l1 > 0" unfolding sgn_rat_def by (cases "l1 = 0"; cases "l1 < 0"; auto)
  from y pos(2)[unfolded yt] have "?r r2 > 0" unfolding split by auto
  hence "sgn r2 = 1" unfolding sgn_rat_def by (auto split: if_splits)
  with y have "sgn l2 = 1" by auto
  hence l2_pos: "l2 > 0" unfolding sgn_rat_def by (cases "l2 = 0"; cases "l2 < 0"; auto)
  let ?bnd = "(\<lambda>((l1, r1, sr1 :: rat), l2 :: rat, r2 :: rat, sr2 :: rat). (l1 * l2, r1 * r2))"
  define bnd where "bnd = ?bnd"
  obtain z' where sel: "select_correct_factor_int_poly
        (tighten_poly_bounds_binary p1 p2)
        bnd 
        ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))) 
        ?p = z'" by auto
  have main: "invariant_2 z' \<and> real_of_2 z' = ?x * ?y"
  proof (rule select_correct_factor_int_poly[OF _ sel rt p])
    {
      fix l1 r1 l2 r2 l1' r1' l2' r2' l l' r r' :: rat
      let ?m1 = "(l1+r1)/2" let ?m2 = "(l2+r2)/2"
      define d1 where "d1 = r1 - l1" 
      define d2 where "d2 = r2 - l2"
      let ?M1 = "l1 + d1/2" let ?M2 = "l2 + d2/2"
      assume le: "l1 > 0" "l2 > 0" "l1 \<le> r1" "l2 \<le> r2" and id: "(l, r) = (l1 * l2, r1 * r2)"
        "(l', r') = (l1' * l2', r1' * r2')" 
        and mem: "(l1', r1') \<in> {(l1, ?m1), (?m1, r1)}"
          "(l2', r2') \<in> {(l2, ?m2), (?m2, r2)}"
      hence id: "l = l1 * l2" "r = (l1 + d1) * (l2 + d2)" "l' = l1' * l2'" "r' = r1' * r2'" 
        "r1 = l1 + d1" "r2 = l2 + d2" and id': "?m1 = ?M1" "?m2 = ?M2"
        unfolding d1_def d2_def by (auto simp: field_simps)
      define l1d1 where "l1d1 = l1 + d1"
      from le have ge0: "d1 \<ge> 0" "d2 \<ge> 0" "l1 \<ge> 0" "l2 \<ge> 0" unfolding d1_def d2_def by auto
      have "4 * (r' - l') \<le> 3 * (r - l)" 
      proof (cases "l1' = l1 \<and> r1' = ?M1 \<and> l2' = l2 \<and> r2' = ?M2")
        case True
        hence id2: "l1' = l1" "r1' = ?M1" "l2' = l2" "r2' = ?M2" by auto
        show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp 
      next
        case False note 1 = this
        show ?thesis
        proof (cases "l1' = l1 \<and> r1' = ?M1 \<and> l2' = ?M2 \<and> r2' = r2")
          case True
          hence id2: "l1' = l1" "r1' = ?M1" "l2' = ?M2" "r2' = r2" by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
        next
          case False note 2 = this
          show ?thesis
          proof (cases "l1' = ?M1 \<and> r1' = r1 \<and> l2' = l2 \<and> r2' = ?M2")
            case True
            hence id2: "l1' = ?M1" "r1' = r1" "l2' = l2" "r2' = ?M2" by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
          next
            case False note 3 = this
            from 1 2 3 mem have id2: "l1' = ?M1" "r1' = r1" "l2' = ?M2" "r2' = r2"
              unfolding id' by auto
          show ?thesis unfolding id id2 unfolding ring_distribs using ge0 by simp
          qed
        qed
      qed
      hence "r' - l' \<le> 3 / 4 * (r - l)" by simp
    } note decr = this
    show "converges_to
        (\<lambda>i. bnd ((tighten_poly_bounds_binary p1 p2 ^^ i)
        ((l1,r1,sgn (ipoly p1 r1)),(l2,r2, sgn (ipoly p2 r2))))) (?x * ?y)"
    proof (intro tighten_poly_bounds_binary[where f = "(*)" and I = "\<lambda> l. l > 0"]
      basic l1_pos l2_pos, goal_cases)
      case (1 L1 R1 L2 R2 L R)
      hence "L = L1 * L2" "R = R1 * R2" unfolding bnd_def by auto
      hence id: "?r L = ?r L1 * ?r L2" "?r R = ?r R1 * ?r R2" by (auto simp: hom_distribs)
      from 1(3-4) have le: "?r L1 \<le> ?x" "?x \<le> ?r R1" "?r L2 \<le> ?y" "?y \<le> ?r R2" 
        unfolding root_cond_def by auto
      from 1(1-2) have lt: "0 < ?r L1" "0 < ?r L2" by auto
      from mult_mono[OF le(1,3), folded id] lt le have L: "?r L \<le> ?x * ?y" by linarith
      have R: "?x * ?y \<le> ?r R"
        by (rule mult_mono[OF le(2,4), folded id], insert lt le, linarith+)
      show ?case using L R by blast
    next
      case (2 l1 r1 l2 r2 l1' r1' l2' r2' l l' r r')
      from 2(5-6) have lr: "l = l1 * l2" "r = r1 * r2" "l' = l1' * l2'" "r' = r1' * r2'"
        unfolding bnd_def by auto      
      from 2(1-4) have le: "0 < l1" "0 < l2" "l1 \<le> r1" "l2 \<le> r2" by auto
      from 2(7-8) le have le': "l1 \<le> l1'" "r1' \<le> r1" "l2 \<le> l2'" "r2' \<le> r2" "0 < r2'" "0 < r2" by auto
      from mult_mono[OF le'(1,3), folded lr] le le' have l: "l \<le> l'" by auto
      have r: "r' \<le> r" by (rule mult_mono[OF le'(2,4), folded lr], insert le le', linarith+)
      have "r' - l' \<le> 3 / 4 * (r - l)"
        by (rule decr[OF _ _ _ _ _ _ 2(7-8)], insert le le' lr, auto)
      thus ?case using l r by blast
    qed auto
  qed
  have z': "z' = z" unfolding z[unfolded xt yt, simplified, unfolded bnd_def[symmetric] sel]
    by auto
  from main[unfolded this] show ?thesis unfolding xt yt by simp
qed
  
lemma mult_1: assumes x: "invariant_1_2 x" and y: "invariant_1_2 y"
  defines z[simp]: "z \<equiv> mult_1 x y"
  shows "invariant_2 z \<and> (real_of_2 z = real_of_1 x * real_of_1 y)" 
proof -
  obtain p1 l1 r1 where xt[simp]: "x = (p1,l1,r1)" by (cases x)
  obtain p2 l2 r2 where yt[simp]: "y = (p2,l2,r2)" by (cases y)
  let ?xt = "(p1, l1, r1)"
  let ?yt = "(p2, l2, r2)"
  let ?x = "real_of_1 ?xt"
  let ?y = "real_of_1 ?yt"
  let ?mxt = "uminus_1 ?xt"
  let ?myt = "uminus_1 ?yt"
  let ?mx = "real_of_1 ?mxt"
  let ?my = "real_of_1 ?myt"
  let ?r = "real_of_rat"
  from invariant_1_2_of_rat[OF x, of 0] have x0: "?x < 0 \<or> ?x > 0" by auto
  from invariant_1_2_of_rat[OF y, of 0] have y0: "?y < 0 \<or> ?y > 0" by auto
  from uminus_1_2[OF x] have mx: "invariant_1_2 ?mxt" and [simp]: "?mx = - ?x" by auto
  from uminus_1_2[OF y] have my: "invariant_1_2 ?myt" and [simp]: "?my = - ?y" by auto
  have id: "r1 > 0 \<longleftrightarrow> ?x > 0" "r1 < 0 \<longleftrightarrow> ?x < 0" "r2 > 0 \<longleftrightarrow> ?y > 0" "r2 < 0 \<longleftrightarrow> ?y < 0"
    using x y by auto
  show ?thesis
  proof (cases "?x > 0")
    case x0: True
    show ?thesis 
    proof (cases "?y > 0")
      case y0: True
      with x y x0 mult_1_pos[OF x y] show ?thesis by auto
    next
      case False
      with y0 have y0: "?y < 0" by auto
      with x0 have z: "z = uminus_2 (mult_1_pos ?xt ?myt)"
        unfolding z xt yt mult_1.simps split id by simp
      from x0 y0 mult_1_pos[OF x my] uminus_2[of "mult_1_pos ?xt ?myt"]
      show ?thesis unfolding z by simp
    qed
  next
    case False
    with x0 have x0: "?x0 < 0" by simp
    show ?thesis
    proof (cases "?y > 0")
      case y0: True
      with x0 x y id have z: "z = uminus_2 (mult_1_pos ?mxt ?yt)" by simp
      from x0 y0 mult_1_pos[OF mx y] uminus_2[of "mult_1_pos ?mxt ?yt"]
      show ?thesis unfolding z by auto
    next
      case False
      with y0 have y0: "?y < 0" by simp
      with x0 x y have z: "z = mult_1_pos ?mxt ?myt" by auto
      with x0 y0 x y mult_1_pos[OF mx my]
      show ?thesis unfolding z by auto
    qed
  qed
qed
  

lemma mult_rat_1: fixes x assumes y: "invariant_1 y"  
  defines z: "z \<equiv> mult_rat_1 x y"
  shows "invariant_2 z \<and> (real_of_2 z = of_rat x * real_of_1 y)" 
proof (cases y)
  case yt: (fields p2 l2 r2)
  let ?yt = "(p2, l2, r2)"
  let ?x = "real_of_rat x"
  let ?y = "real_of_1 ?yt"
  let ?myt = "mult_rat_1_pos (- x) ?yt"
  note y = y[unfolded yt]
  note z = z[unfolded yt]
  show ?thesis
  proof(cases x "0::rat" rule:linorder_cases)
    case x: greater
    with z have z: "z = mult_rat_1_pos x ?yt" by simp
    from mult_rat_1_pos[OF x y] 
    show ?thesis unfolding yt z by auto
  next
    case less
    then have x: "- x > 0" by auto
    hence z: "z = uminus_2 ?myt" unfolding z by simp
    from mult_rat_1_pos[OF x y] have rc: "invariant_2 ?myt"
      and rr: "real_of_2 ?myt = - ?x * ?y" by (auto simp: hom_distribs)
    from uminus_2[OF rc] rr show ?thesis unfolding z[symmetric] unfolding yt[symmetric]
      by simp
  qed (auto simp: z)
qed
end
  
declare mult_1.simps[simp del]
declare mult_rat_1.simps[simp del]

(* ********************* *)
subsubsection\<open>Root\<close>

definition ipoly_root_delta :: "int poly \<Rightarrow> real" where
  "ipoly_root_delta p = Min (insert 1 { abs (x - y) | x y. ipoly p x = 0 \<and> ipoly p y = 0 \<and> x \<noteq> y}) / 4"

lemma ipoly_root_delta: assumes "p \<noteq> 0"
  shows "ipoly_root_delta p > 0"
    "2 \<le> card (Collect (root_cond (p, l, r))) \<Longrightarrow> ipoly_root_delta p \<le> real_of_rat (r - l) / 4"
proof -
  let ?z = "0 :: real"
  let ?R = "{x. ipoly p x = ?z}"
  let ?set = "{ abs (x - y) | x y. ipoly p x = ?z  \<and> ipoly p y = 0 \<and> x \<noteq> y}"
  define S where "S = insert 1 ?set"
  from finite_ipoly_roots[OF assms] have finR: "finite ?R" and fin: "finite (?R \<times> ?R)" by auto
  have "finite ?set"
    by (rule finite_subset[OF _ finite_imageI[OF fin, of "\<lambda> (x,y). abs (x - y)"]], force)
  hence fin: "finite S" and ne: "S \<noteq> {}" and pos: "\<And> x. x \<in> S \<Longrightarrow> x > 0" unfolding S_def by auto
  have delta: "ipoly_root_delta p = Min S / 4" unfolding ipoly_root_delta_def S_def ..
  have pos: "Min S > 0" using fin ne pos by auto
  show "ipoly_root_delta p > 0" unfolding delta using pos by auto
  let ?S = "Collect (root_cond (p, l, r))"
  assume "2 \<le> card ?S"
  hence 2: "Suc (Suc 0) \<le> card ?S" by simp
  from 2[unfolded card_le_Suc_iff[of _ ?S]] obtain x T where 
    ST: "?S = insert x T" and xT: "x \<notin> T" and 1: "Suc 0 \<le> card T" by auto
  from 1[unfolded card_le_Suc_iff[of _ T]] obtain y where yT: "y \<in> T" by auto
  from ST xT yT have x: "x \<in> ?S" and y: "y \<in> ?S" and xy: "x \<noteq> y" by auto
  hence "abs (x - y) \<in> S" unfolding S_def root_cond_def[abs_def] by auto
  with fin have "Min S \<le> abs (x - y)" by auto
  with pos have le: "Min S / 2 \<le> abs (x - y) / 2" by auto
  from x y have "abs (x - y) \<le> of_rat r - of_rat l" unfolding root_cond_def[abs_def] by auto
  also have "\<dots> = of_rat (r - l)" by (auto simp: of_rat_diff)
  finally have "abs (x - y) / 2 \<le> of_rat (r - l) / 2" by auto
  with le show "ipoly_root_delta p \<le> real_of_rat (r - l) / 4" unfolding delta by auto
qed

lemma sgn_less_eq_1_rat: fixes a b :: rat
  shows "sgn a = 1 \<Longrightarrow> a \<le> b \<Longrightarrow> sgn b = 1" 
  by (metis (no_types, hide_lams) not_less one_neq_neg_one one_neq_zero order_trans sgn_rat_def)

lemma sgn_less_eq_1_real: fixes a b :: real
  shows "sgn a = 1 \<Longrightarrow> a \<le> b \<Longrightarrow> sgn b = 1" 
  by (metis (no_types, hide_lams) not_less one_neq_neg_one one_neq_zero order_trans sgn_real_def)

definition compare_1_rat :: "real_alg_1 \<Rightarrow> rat \<Rightarrow> order" where
  "compare_1_rat rai = (let p = poly_real_alg_1 rai in
    if degree p = 1 then let x = Rat.Fract (- coeff p 0) (coeff p 1)
     in (\<lambda> y. compare y x)
    else (\<lambda> y. compare_rat_1 y rai))" 

lemma compare_real_of_rat: "compare (real_of_rat x) (of_rat y) = compare x y" 
  unfolding compare_rat_def compare_real_def comparator_of_def of_rat_less by auto

lemma compare_1_rat: assumes rc: "invariant_1 y"
  shows "compare_1_rat y x = compare (of_rat x) (real_of_1 y)"
proof (cases "degree (poly_real_alg_1 y)" "Suc 0" rule: linorder_cases)
  case less with invariant_1_degree_0[OF rc] show ?thesis by auto
next
  case deg: greater
  with rc have rc: "invariant_1_2 y" by auto
  from deg compare_rat_1[OF rc, of x]
  show ?thesis unfolding compare_1_rat_def by auto
next
  case deg: equal
  obtain p l r where y: "y = (p,l,r)" by (cases y)
  note rc = invariant_1D[OF rc[unfolded y]]
  from deg have p: "degree p = Suc 0" 
    and id: "compare_1_rat y x = compare x (Rat.Fract (- coeff p 0) (coeff p 1))" 
    unfolding compare_1_rat_def by (auto simp: Let_def y)
  from rc(1)[unfolded split] have "ipoly p (real_of_1 y) = 0" 
    unfolding y by auto
  with degree_1_ipoly[OF p, of "real_of_1 y"] 
  have id': "real_of_1 y = real_of_rat (Rat.Fract (- coeff p 0) (coeff p 1))" by simp
  show ?thesis unfolding id id' compare_real_of_rat ..
qed
  
context
  fixes n :: nat
begin
private definition initial_lower_bound :: "rat \<Rightarrow> rat" where 
  "initial_lower_bound l = (if l \<le> 1 then l else of_int (root_rat_floor n l))"

private definition initial_upper_bound :: "rat \<Rightarrow> rat" where
  "initial_upper_bound r = (of_int (root_rat_ceiling n r))"
  
context
  fixes cmpx :: "rat \<Rightarrow> order" 
begin  
fun tighten_bound_root :: 
  "rat \<times> rat \<Rightarrow> rat \<times> rat" where
  "tighten_bound_root (l',r') = (let 
      m' = (l' + r') / 2;
      m = m' ^ n      
      in case cmpx m of 
         Eq \<Rightarrow> (m',m')
       | Lt \<Rightarrow> (m',r')
       | Gt \<Rightarrow> (l',m'))" 
  
lemma tighten_bound_root: assumes sgn: "sgn il = 1" "real_of_1 x \<ge> 0" and
  il: "real_of_rat il \<le> root n (real_of_1 x)" and 
  ir: "root n (real_of_1 x) \<le> real_of_rat ir" and
  rai: "invariant_1 x" and
  cmpx: "cmpx = compare_1_rat x" and
  n: "n \<noteq> 0" 
shows "converges_to (\<lambda> i. (tighten_bound_root ^^ i) (il, ir))
     (root n (real_of_1 x))" (is "converges_to ?f ?x")
  unfolding converges_to_def
proof (intro conjI impI allI)
  {
    fix x :: real
    have "x \<ge> 0 \<Longrightarrow> (root n x) ^ n = x" using n by simp
  } note root_exp_cancel = this
  {
    fix x :: real
    have "x \<ge> 0 \<Longrightarrow> root n (x ^ n) = x" using n
      using real_root_pos_unique by blast
  } note root_exp_cancel' = this
  from il ir have "real_of_rat il \<le> of_rat ir" by auto
  hence ir_il: "il \<le> ir" by (auto simp: of_rat_less_eq)
  from n have n': "n > 0" by auto
  {
    fix i
    have "in_interval (?f i) ?x \<and> sub_interval (?f i) (il,ir) \<and> (i \<noteq> 0 \<longrightarrow> sub_interval (?f i) (?f (i - 1))) 
      \<and> snd (?f i) - fst (?f i) \<le> (ir - il) / 2^i"
    proof (induct i)
      case 0
      show ?case using il ir by auto
    next
      case (Suc i)
      obtain l' r' where id: "(tighten_bound_root ^^ i) (il, ir) = (l',r')" 
        by (cases "(tighten_bound_root ^^ i) (il, ir)", auto)
      let ?m' = "(l' + r') / 2" 
      let ?m = "?m' ^ n" 
      define m where "m = ?m" 
      note IH = Suc[unfolded id split snd_conv fst_conv] 
      from IH have "sub_interval (l', r') (il, ir)" by auto
      hence ill': "il \<le> l'" "r' \<le> ir" by auto
      with sgn have l'0: "l' > 0" using sgn_1_pos sgn_less_eq_1_rat by blast
      from IH have lr'x: "in_interval (l', r') ?x" by auto
      hence lr'': "real_of_rat l' \<le> of_rat r'" by auto
      hence lr': "l' \<le> r'" unfolding of_rat_less_eq .
      with l'0 have r'0: "r' > 0" by auto
      note compare = compare_1_rat[OF rai, of ?m, folded cmpx]
      from IH have *: "r' - l' \<le> (ir - il) / 2 ^ i" by auto
      have "r' - (l' + r') / 2 = (r' - l') / 2" by (simp add: field_simps)
      also have "\<dots> \<le> (ir - il) / 2 ^ i / 2" using * 
        by (rule divide_right_mono, auto)  
      finally have size: "r' - (l' + r') / 2 \<le> (ir - il) / (2 * 2 ^ i)" by simp
      also have "r' - (l' + r') / 2 = (l' + r') / 2 - l'" by auto
      finally have size': "(l' + r') / 2 - l' \<le> (ir - il) / (2 * 2 ^ i)" by simp
      have "root n (real_of_rat ?m) = root n ((real_of_rat ?m') ^ n)" by (simp add: hom_distribs)
      also have "\<dots> = real_of_rat ?m'" 
        by (rule root_exp_cancel', insert l'0 lr', auto)
      finally have root: "root n (of_rat ?m) = of_rat ?m'" .
      show ?case 
      proof (cases "cmpx ?m")
        case Eq
        from compare[unfolded Eq] have "real_of_1 x = of_rat ?m" 
          unfolding compare_real_def comparator_of_def by (auto split: if_splits)
        from arg_cong[OF this, of "root n"] have "?x = root n (of_rat ?m)" .
        also have "\<dots> = root n  (real_of_rat ?m') ^ n"
          using n real_root_power by (auto simp: hom_distribs)
        also have "\<dots> = of_rat ?m'" 
          by (rule root_exp_cancel, insert IH sgn(2) l'0 r'0, auto)
        finally have x: "?x = of_rat ?m'"  .
        show ?thesis using x id Eq lr' ill' ir_il by (auto simp: Let_def)
      next
        case Lt 
        from compare[unfolded Lt] have lt: "of_rat ?m \<le> real_of_1 x" 
          unfolding compare_real_def comparator_of_def by (auto split: if_splits)
        have id'': "?f (Suc i) = (?m',r')" "?f (Suc i - 1) = (l',r')"  
          using Lt id by (auto simp add: Let_def)
        from real_root_le_mono[OF n' lt] 
        have "of_rat ?m' \<le> ?x" unfolding root by simp
        with lr'x lr'' have ineq': "real_of_rat l' + real_of_rat r' \<le> ?x * 2" by (auto simp: hom_distribs)
        show ?thesis unfolding id'' 
          by (auto simp: Let_def hom_distribs, insert size ineq' lr' ill' lr'x ir_il, auto)
      next
        case Gt
        from compare[unfolded Gt] have lt: "of_rat ?m \<ge> real_of_1 x" 
          unfolding compare_real_def comparator_of_def by (auto split: if_splits)
        have id'': "?f (Suc i) = (l',?m')" "?f (Suc i - 1) = (l',r')"  
          using Gt id by (auto simp add: Let_def)
        from real_root_le_mono[OF n' lt] 
        have "?x \<le> of_rat ?m'" unfolding root by simp
        with lr'x lr'' have ineq': "?x * 2 \<le> real_of_rat l' + real_of_rat r'" by (auto simp: hom_distribs)
        show ?thesis unfolding id'' 
          by (auto simp: Let_def hom_distribs, insert size' ineq' lr' ill' lr'x ir_il, auto)
      qed
    qed
  } note main = this
  fix i
  from main[of i] show "in_interval (?f i) ?x" by auto
  from main[of "Suc i"] show "sub_interval (?f (Suc i)) (?f i)" by auto
  fix eps :: real
  assume eps: "0 < eps" 
  define c where "c = eps / (max (real_of_rat (ir - il)) 1)" 
  have c0: "c > 0" using eps unfolding c_def by auto    
  from exp_tends_to_zero[OF _ _ this, of "1/2"] obtain i where c: "(1/2)^i \<le> c" by auto
  obtain l' r' where fi: "?f i = (l',r')" by force
  from main[of i, unfolded fi] have le: "r' - l' \<le> (ir - il) / 2 ^ i" by auto
  have iril: "real_of_rat (ir - il) \<ge> 0" using ir_il by (auto simp: of_rat_less_eq)
  show "\<exists>n la ra. ?f n = (la, ra) \<and> real_of_rat ra - real_of_rat la \<le> eps" 
  proof (intro conjI exI, rule fi)
    have "real_of_rat r' - of_rat l' = real_of_rat (r' - l')" by (auto simp: hom_distribs)
    also have "\<dots> \<le> real_of_rat ((ir - il) / 2 ^ i)" using le unfolding of_rat_less_eq .
    also have "\<dots> = (real_of_rat (ir - il)) * ((1/2) ^ i)" by (simp add: field_simps hom_distribs)
    also have "\<dots> \<le> (real_of_rat (ir - il)) * c" 
      by (rule mult_left_mono[OF c iril])
    also have "\<dots> \<le> eps"
    proof (cases "real_of_rat (ir - il) \<le> 1")
      case True
      hence "c = eps" unfolding c_def by (auto simp: hom_distribs)
      thus ?thesis using eps True by auto
    next
      case False
      hence "max (real_of_rat (ir - il)) 1 = real_of_rat (ir - il)" "real_of_rat (ir - il) \<noteq> 0" 
        by (auto simp: hom_distribs)
      hence "(real_of_rat (ir - il)) * c = eps" unfolding c_def by auto
      thus ?thesis by simp
    qed
    finally show "real_of_rat r' - of_rat l' \<le> eps" .
  qed
qed
end

private fun root_pos_1 :: "real_alg_1 \<Rightarrow> real_alg_2" where
  "root_pos_1 (p,l,r) = (
      (select_correct_factor_int_poly 
        (tighten_bound_root (compare_1_rat (p,l,r)))
        (\<lambda> x. x)
        (initial_lower_bound l, initial_upper_bound r)
        (poly_nth_root n p)))"

fun root_1 :: "real_alg_1 \<Rightarrow> real_alg_2" where
"root_1 (p,l,r) = (
  if n = 0 \<or> r = 0 then Rational 0
  else if r > 0 then root_pos_1 (p,l,r)
  else uminus_2 (root_pos_1 (uminus_1 (p,l,r))))"

context
  assumes n: "n \<noteq> 0"
begin

lemma initial_upper_bound: assumes x: "x > 0" and xr: "x \<le> of_rat r"
  shows "sgn (initial_upper_bound r) = 1" "root n x \<le> of_rat (initial_upper_bound r)"
proof -
  have n: "n > 0" using n by auto
  note d = initial_upper_bound_def
  let ?r = "initial_upper_bound r"
  from x xr have r0: "r > 0" by (meson not_less of_rat_le_0_iff order_trans)
  hence "of_rat r > (0 :: real)" by auto
  hence "root n (of_rat r) > 0" using n by simp
  hence "1 \<le> ceiling (root n (of_rat r))" by auto
  hence "(1 :: rat) \<le> of_int (ceiling (root n (of_rat r)))" by linarith
  also have "\<dots> = ?r" unfolding d by simp
  finally show "sgn ?r = 1" unfolding sgn_rat_def by auto
  have "root n x \<le> root n (of_rat r)"
    unfolding real_root_le_iff[OF n] by (rule xr)
  also have "\<dots> \<le> of_rat ?r" unfolding d by simp
  finally show "root n x \<le> of_rat ?r" .
qed

lemma initial_lower_bound: assumes l: "l > 0" and lx: "of_rat l \<le> x"
  shows "sgn (initial_lower_bound l) = 1" "of_rat (initial_lower_bound l) \<le> root n x"
proof -
  have n: "n > 0" using n by auto
  note d = initial_lower_bound_def
  let ?l = "initial_lower_bound l"
  from l lx have x0: "x > 0" by (meson not_less of_rat_le_0_iff order_trans)
  have "sgn ?l = 1 \<and> of_rat ?l \<le> root n x"
  proof (cases "l \<le> 1")
    case True
    hence ll: "?l = l" and l0: "of_rat l \<ge> (0 :: real)" and l1: "of_rat l \<le> (1 :: real)" 
      using l unfolding True d by auto
    have sgn: "sgn ?l = 1" using l unfolding ll by auto
    have "of_rat ?l = of_rat l" unfolding ll by simp
    also have "of_rat l \<le> root n (of_rat l)" using real_root_increasing[OF _ _ l0 l1, of 1 n] n
      by (cases "n = 1", auto)
    also have "\<dots> \<le> root n x" using lx unfolding real_root_le_iff[OF n] .
    finally show ?thesis using sgn by auto
  next
    case False
    hence l: "(1 :: real) \<le> of_rat l" and ll: "?l = of_int (floor (root n (of_rat l)))" 
      unfolding d by auto
    hence "root n 1 \<le> root n (of_rat l)"
      unfolding real_root_le_iff[OF n] by auto
    hence "1 \<le> root n (of_rat l)" using n by auto
    from floor_mono[OF this] have "1 \<le> ?l"
      using one_le_floor unfolding ll by fastforce
    hence sgn: "sgn ?l = 1" by simp
    have "of_rat ?l \<le> root n (of_rat l)" unfolding ll by simp
    also have "\<dots> \<le> root n x" using lx unfolding real_root_le_iff[OF n] .
    finally have "of_rat ?l \<le> root n x" .
    with sgn show ?thesis by auto
  qed
  thus "sgn ?l = 1" "of_rat ?l \<le> root n x" by auto
qed

lemma root_pos_1:
  assumes x: "invariant_1 x" and pos: "rai_ub x > 0"
  defines y: "y \<equiv> root_pos_1 x"
  shows "invariant_2 y \<and> real_of_2 y = root n (real_of_1 x)"
proof (cases x)
  case (fields p l r)
  let ?l = "initial_lower_bound l"
  let ?r = "initial_upper_bound r"
  from x fields have rai: "invariant_1 (p,l,r)" by auto
  note * = invariant_1D[OF this]
  let ?x = "the_unique_root (p,l,r)"
  from pos[unfolded fields] *
  have sgnl: "sgn l = 1" by auto
  from sgnl have l0: "l > 0" by (unfold sgn_1_pos)
  hence ll0: "real_of_rat l > 0" by auto
  from * have lx: "of_rat l \<le> ?x" by auto
  with ll0 have x0: "?x > 0" by linarith
  note il = initial_lower_bound[OF l0 lx]
  from * have "?x \<le> of_rat r" by auto
  note iu = initial_upper_bound[OF x0 this]
  let ?p = "poly_nth_root n p"
  from x0 have id: "root n ?x ^ n = ?x" using n real_root_pow_pos by blast
  have rc: "root_cond (?p, ?l, ?r) (root n ?x)"
    using il iu * by (intro root_condI, auto simp: ipoly_nth_root id)
  hence root: "ipoly ?p (root n (real_of_1 x)) = 0" 
    unfolding root_cond_def fields by auto
  from * have "p \<noteq> 0" by auto
  hence p': "?p \<noteq> 0" using poly_nth_root_0[of n p] n by auto
  have tbr: "0 \<le> real_of_1 x"
            "real_of_rat (initial_lower_bound l) \<le> root n (real_of_1 x)"
            "root n (real_of_1 x) \<le> real_of_rat (initial_upper_bound r)"
     using x0 il(2) iu(2) fields by auto
  from select_correct_factor_int_poly[OF tighten_bound_root[OF il(1)[folded fields] tbr x refl n] refl root p']
  show ?thesis by (simp add: y fields)
qed

end

lemma root_1: assumes x: "invariant_1 x"
  defines y: "y \<equiv> root_1 x"
  shows "invariant_2 y \<and> (real_of_2 y = root n (real_of_1 x))"
proof (cases "n = 0 \<or> rai_ub x = 0")
  case True
  with x have "n = 0 \<or> real_of_1 x = 0" by (cases x, auto)
  then have "root n (real_of_1 x) = 0" by auto
  then show ?thesis unfolding y root_1.simps
    using x by (cases x, auto)
next
  case False with x have n: "n \<noteq> 0" and x0: "real_of_1 x \<noteq> 0" by (simp, cases x, auto)
  note rt = root_pos_1
  show ?thesis
  proof (cases "rai_ub x" "0::rat" rule:linorder_cases)
    case greater
    with rt[OF n x this] n show ?thesis by (unfold y, cases x, simp)
  next
    case less
    let ?um = "uminus_1"
    let ?rt = "root_pos_1"
    from n less y x0 have y: "y = uminus_2 (?rt (?um x))" by (cases x, auto)
    from uminus_1[OF x] have umx: "invariant_1 (?um x)" and umx2: "real_of_1 (?um x) = - real_of_1 x" by auto
    with x less have "0 < rai_ub (uminus_1 x)"
      by (cases x, auto simp: uminus_1.simps Let_def)
    from rt[OF n umx this] umx2 have rumx: "invariant_2 (?rt (?um x))" 
      and rumx2: "real_of_2 (?rt (?um x)) = root n (- real_of_1 x)"
      by auto
    from uminus_2[OF rumx] rumx2 y real_root_minus show ?thesis by auto
  next
    case equal with x0 x show ?thesis by (cases x, auto)
  qed
qed
end
  
declare root_1.simps[simp del]

(* ********************** *)
subsubsection \<open>Embedding of Rational Numbers\<close>

definition of_rat_1 :: "rat \<Rightarrow> real_alg_1" where
  "of_rat_1 x \<equiv> (poly_rat x,x,x)"

lemma of_rat_1:
  shows "invariant_1 (of_rat_1 x)" and "real_of_1 (of_rat_1 x) = of_rat x"
  unfolding of_rat_1_def
by (atomize(full), intro invariant_1_realI unique_rootI poly_condI, auto )

fun info_2 :: "real_alg_2 \<Rightarrow> rat + int poly \<times> nat" where
  "info_2 (Rational x) = Inl x"
| "info_2 (Irrational n (p,l,r)) = Inr (p,n)" 
    
lemma info_2_card: assumes rc: "invariant_2 x"
  shows "info_2 x = Inr (p,n) \<Longrightarrow> poly_cond p \<and> ipoly p (real_of_2 x) = 0 \<and> degree p \<ge> 2 
    \<and> card (roots_below p (real_of_2 x)) = n"
    "info_2 x = Inl y \<Longrightarrow> real_of_2 x = of_rat y" 
proof (atomize(full), goal_cases)
  case 1
  show ?case
  proof (cases x)
    case (Irrational m rai)
    then obtain q l r where x: "x = Irrational m (q,l,r)" by (cases rai, auto)
    show ?thesis
    proof (cases "q = p \<and> m = n")
      case False
      thus ?thesis using x by auto
    next
      case True
      with x have x: "x = Irrational n (p,l,r)" by auto
      from rc[unfolded x, simplified] have inv: "invariant_1_2 (p,l,r)" and 
        n: "card (roots_below p (real_of_2 x)) = n" and 1: "degree p \<noteq> 1" 
        by (auto simp: x)
      from inv have "degree p \<noteq> 0" unfolding irreducible_def by auto
      with 1 have "degree p \<ge> 2" by linarith
      thus ?thesis unfolding n using inv x by (auto elim!: invariant_1E)
    qed
  qed auto
qed
  
lemma real_of_2_Irrational: "invariant_2 (Irrational n rai) \<Longrightarrow> real_of_2 (Irrational n rai) \<noteq> of_rat x" 
proof
  assume "invariant_2 (Irrational n rai)" and rat: "real_of_2 (Irrational n rai) = real_of_rat x" 
  hence "real_of_1 rai \<in> \<rat>" "invariant_1_2 rai" by auto
  from invariant_1_2_of_rat[OF this(2)] rat show False by auto
qed
            
lemma info_2: assumes 
    ix: "invariant_2 x" and iy: "invariant_2 y"
  shows "info_2 x = info_2 y \<longleftrightarrow> real_of_2 x = real_of_2 y"
proof (cases x)
  case x: (Irrational n1 rai1)
  note ix = ix[unfolded x]
  show ?thesis
  proof (cases y)
    case (Rational y)
    with real_of_2_Irrational[OF ix, of y] show ?thesis unfolding x by (cases rai1, auto)
  next
    case y: (Irrational n2 rai2)
    obtain p1 l1 r1 where rai1: "rai1 = (p1,l1,r1)" by (cases rai1)
    obtain p2 l2 r2 where rai2: "rai2 = (p2,l2,r2)" by (cases rai2)
    let ?rx = "the_unique_root (p1,l1,r1)"
    let ?ry = "the_unique_root (p2,l2,r2)"
    have id: "(info_2 x = info_2 y) = (p1 = p2 \<and> n1 = n2)" 
      "(real_of_2 x = real_of_2 y) = (?rx = ?ry)" 
      unfolding x y rai1 rai2 by auto
    from ix[unfolded x rai1]
    have ix: "invariant_1 (p1, l1, r1)" and deg1: "degree p1 > 1" and n1: "n1 = card (roots_below p1 ?rx)" by auto
    note Ix = invariant_1D[OF ix]
    from deg1 have p1_0: "p1 \<noteq> 0" by auto
    from iy[unfolded y rai2] 
    have iy: "invariant_1 (p2, l2, r2)" and "degree p2 > 1" and n2: "n2 = card (roots_below p2 ?ry)"  by auto
    note Iy = invariant_1D[OF iy]
    show ?thesis unfolding id
    proof
      assume eq: "?rx = ?ry" 
      from Ix
      have algx: "p1 represents ?rx \<and> irreducible p1 \<and> lead_coeff p1 > 0" unfolding represents_def by auto
      from iy
      have algy: "p2 represents ?rx \<and> irreducible p2 \<and> lead_coeff p2 > 0" unfolding represents_def eq by (auto elim!: invariant_1E)
      from algx have "algebraic ?rx" unfolding algebraic_altdef_ipoly by auto
      note unique = algebraic_imp_represents_unique[OF this]
      with algx algy have id: "p2 = p1" by auto
      from eq id n1 n2 show "p1 = p2 \<and> n1 = n2" by auto
    next
      assume "p1 = p2 \<and> n1 = n2" 
      hence id: "p1 = p2" "n1 = n2" by auto
      hence card: "card (roots_below p1 ?rx) = card (roots_below p1 ?ry)" unfolding n1 n2 by auto
      show "?rx = ?ry"
      proof (cases ?rx ?ry rule: linorder_cases)
        case less
        have "roots_below p1 ?rx = roots_below p1 ?ry"
        proof (intro card_subset_eq finite_subset[OF _ ipoly_roots_finite] card)
          from less show "roots_below p1 ?rx \<subseteq> roots_below p1 ?ry" by auto
        qed (insert p1_0, auto)
        then show ?thesis using id less unique_rootD(3)[OF Iy(4)] by (auto simp: less_eq_real_def)
      next
        case equal
        then show ?thesis by (simp add: id)
      next
        case greater
        have "roots_below p1 ?ry = roots_below p1 ?rx"
        proof (intro card_subset_eq card[symmetric] finite_subset[OF _ ipoly_roots_finite[OF p1_0]])
          from greater show "roots_below p1 ?ry \<subseteq> roots_below p1 ?rx" by auto
        qed auto
        hence "roots_below p2 ?ry = roots_below p2 ?rx" unfolding id by auto
        thus ?thesis using id greater unique_rootD(3)[OF Ix(4)] by (auto simp: less_eq_real_def)
      qed
    qed
  qed
next
  case x: (Rational x)
  show ?thesis
  proof (cases y)
    case (Rational y)
    thus ?thesis using x by auto
  next
    case y: (Irrational n rai)
    with real_of_2_Irrational[OF iy[unfolded y], of x] show ?thesis unfolding x by (cases rai, auto)
  qed
qed
  
lemma info_2_unique: "invariant_2 x \<Longrightarrow> invariant_2 y \<Longrightarrow> 
  real_of_2 x = real_of_2 y \<Longrightarrow> info_2 x = info_2 y"
  using info_2 by blast
  
lemma info_2_inj: "invariant_2 x \<Longrightarrow> invariant_2 y \<Longrightarrow> info_2 x = info_2 y \<Longrightarrow>
  real_of_2 x = real_of_2 y"
  using info_2 by blast    

context
  fixes cr1 cr2 :: "rat \<Rightarrow> rat \<Rightarrow> nat"
begin
partial_function (tailrec) compare_1 :: "int poly \<Rightarrow> int poly \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> order" where
  [code]: "compare_1 p1 p2 l1 r1 sr1 l2 r2 sr2 = (if r1 < l2 then Lt else if r2 < l1 then Gt 
    else let 
      (l1',r1',sr1') = tighten_poly_bounds p1 l1 r1 sr1;
      (l2',r2',sr2') = tighten_poly_bounds p2 l2 r2 sr2
    in compare_1 p1 p2 l1' r1' sr1' l2' r2' sr2')
    "
  
lemma compare_1:
  assumes ur1: "unique_root (p1,l1,r1)"
  and ur2: "unique_root (p2,l2,r2)"
  and pc: "poly_cond2 p1" "poly_cond2 p2"
  and diff: "the_unique_root (p1,l1,r1) \<noteq> the_unique_root (p2,l2,r2)"
  and sr: "sr1 = sgn (ipoly p1 r1)" "sr2 = sgn (ipoly p2 r2)" 
 shows "compare_1 p1 p2 l1 r1 sr1 l2 r2 sr2 = compare (the_unique_root (p1,l1,r1)) (the_unique_root (p2,l2,r2))"
proof -
  let ?r = real_of_rat
  {
    fix d x y
    assume d: "d = (r1 - l1) + (r2 - l2)" and xy: "x = the_unique_root (p1,l1,r1)" "y = the_unique_root (p2,l2,r2)"
    define delta where "delta = abs (x - y) / 4"
    have delta: "delta > 0" and diff: "x \<noteq> y" unfolding delta_def using diff xy by auto
    let ?rel' = "{(x, y). 0 \<le> y \<and> delta_gt delta x y}"
    let ?rel = "inv_image ?rel' ?r"
    have SN: "SN ?rel" by (rule SN_inv_image[OF delta_gt_SN[OF delta]])
    from d ur1 ur2 
    have ?thesis unfolding xy[symmetric] using xy sr
    proof (induct d arbitrary: l1 r1 l2 r2 sr1 sr2 rule: SN_induct[OF SN])
      case (1 d l1 r1 l2 r2)
      note IH = 1(1)
      note d = 1(2)
      note ur = 1(3-4)
      note xy = 1(5-6)
      note sr = 1(7-8)
      note simps = compare_1.simps[of p1 p2 l1 r1 sr1 l2 r2 sr2]
      note urx = unique_rootD[OF ur(1), folded xy]
      note ury = unique_rootD[OF ur(2), folded xy]
      show ?case (is "?l = _")
      proof (cases "r1 < l2")
        case True
        hence l: "?l = Lt" and lt: "?r r1 < ?r l2" unfolding simps of_rat_less by auto
        show ?thesis unfolding l using lt True urx(2) ury(1) 
          by (auto simp: compare_real_def comparator_of_def)
      next
        case False note le = this
        show ?thesis
        proof (cases "r2 < l1")
          case True
          with le have l: "?l = Gt" and lt: "?r r2 < ?r l1" unfolding simps of_rat_less by auto
          show ?thesis unfolding l using lt True ury(2) urx(1) 
            by (auto simp: compare_real_def comparator_of_def)
        next
          case False
          obtain l1' r1' sr1' where tb1: "tighten_poly_bounds p1 l1 r1 sr1 = (l1',r1',sr1')" 
            by (cases rule: prod_cases3, auto)
          obtain l2' r2' sr2' where tb2: "tighten_poly_bounds p2 l2 r2 sr2 = (l2',r2',sr2')" 
            by (cases rule: prod_cases3, auto)            
          from False le tb1 tb2 have l: "?l = compare_1 p1 p2 l1' r1' sr1' l2' r2' sr2'" unfolding simps 
            by auto
          from tighten_poly_bounds[OF tb1 ur(1) pc(1) sr(1)]
          have rc1: "root_cond (p1, l1', r1') (the_unique_root (p1, l1, r1))" 
            and bnd1: "l1 \<le> l1'" "l1' \<le> r1'" "r1' \<le> r1" and d1: "r1' - l1' = (r1 - l1) / 2" 
            and sr1: "sr1' = sgn (ipoly p1 r1')" by auto
          from pc have "p1 \<noteq> 0" "p2 \<noteq> 0" by auto
          from unique_root_sub_interval[OF ur(1) rc1 bnd1(1,3)] xy ur this
          have ur1: "unique_root (p1, l1', r1')" and x: "x = the_unique_root (p1, l1', r1')" by (auto intro!: the_unique_root_eqI)
          from tighten_poly_bounds[OF tb2 ur(2) pc(2) sr(2)]
          have rc2: "root_cond (p2, l2', r2') (the_unique_root (p2, l2, r2))" 
            and bnd2: "l2 \<le> l2'" "l2' \<le> r2'" "r2' \<le> r2" and d2: "r2' - l2' = (r2 - l2) / 2" 
            and sr2: "sr2' = sgn (ipoly p2 r2')" by auto
          from unique_root_sub_interval[OF ur(2) rc2 bnd2(1,3)] xy ur pc
          have ur2: "unique_root (p2, l2', r2')" and y: "y = the_unique_root (p2, l2', r2')" by auto
          define d' where "d' = d/2"
          have d': "d' = r1' - l1' + (r2' - l2')" unfolding d'_def d d1 d2 by (simp add: field_simps)
          have d'0: "d' \<ge> 0" using bnd1 bnd2 unfolding d' by auto
          have dd: "d - d' = d/2" unfolding d'_def by simp
          have "abs (x - y) \<le> 2 * ?r d"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            hence lt: "2 * ?r d < abs (x - y)" by auto
            have "r1 - l1 \<le> d" "r2 - l2 \<le> d" unfolding d using bnd1 bnd2 by auto
            from this[folded of_rat_less_eq[where 'a = real]] lt 
            have "?r (r1 - l1) < abs (x - y) / 2" "?r (r2 - l2) < abs (x - y) / 2" 
              and dd: "?r r1 - ?r l1 \<le> ?r d" "?r r2 - ?r l2 \<le> ?r d" by (auto simp: of_rat_diff)
            from le have "r1 \<ge> l2" by auto hence r1l2: "?r r1 \<ge> ?r l2" unfolding of_rat_less_eq by auto
            from False have "r2 \<ge> l1" by auto hence r2l1: "?r r2 \<ge> ?r l1" unfolding of_rat_less_eq by auto            
            show False
            proof (cases "x \<le> y")
              case True
              from urx(1-2) dd(1) have "?r r1 \<le> x + ?r d" by auto 
              with r1l2 have "?r l2 \<le> x + ?r d" by auto
              with True lt ury(2) dd(2) show False by auto
            next
              case False
              from ury(1-2) dd(2) have "?r r2 \<le> y + ?r d" by auto 
              with r2l1 have "?r l1 \<le> y + ?r d" by auto
              with False lt urx(2) dd(1) show False by auto
            qed              
          qed
          hence dd': "delta_gt delta (?r d) (?r d')"
             unfolding delta_gt_def delta_def using dd by (auto simp: hom_distribs)
          show ?thesis unfolding l
            by (rule IH[OF _ d' ur1 ur2 x y sr1 sr2], insert d'0 dd', auto)
        qed
      qed
    qed
  }
  thus ?thesis by auto
qed
end
  
(* **************************************************************** *)  

fun real_alg_1 :: "real_alg_2 \<Rightarrow> real_alg_1" where
  "real_alg_1 (Rational r) = of_rat_1 r"
| "real_alg_1 (Irrational n rai) = rai"
  
lemma real_alg_1: "real_of_1 (real_alg_1 x) = real_of_2 x"
  by (cases x, auto simp: of_rat_1)
    
definition root_2 :: "nat \<Rightarrow> real_alg_2 \<Rightarrow> real_alg_2" where
  "root_2 n x = root_1 n (real_alg_1 x)"

lemma root_2: assumes "invariant_2 x"
  shows "real_of_2 (root_2 n x) = root n (real_of_2 x)"
  "invariant_2 (root_2 n x)"
proof (atomize(full), cases x, goal_cases)
  case (1 y)
  from of_rat_1[of y] root_1[of "of_rat_1 y" n] assms 1 real_alg_2
  show ?case by (simp add: root_2_def)
next
  case (2 i rai)
  from root_1[of rai n] assms 2 real_alg_2 
  show ?case by (auto simp: root_2_def)
qed
  
fun add_2 :: "real_alg_2 \<Rightarrow> real_alg_2 \<Rightarrow> real_alg_2" where
  "add_2 (Rational r) (Rational q) = Rational (r + q)"
| "add_2 (Rational r) (Irrational n x) = Irrational n (add_rat_1 r x)"
| "add_2 (Irrational n x) (Rational q) = Irrational n (add_rat_1 q x)"
| "add_2 (Irrational n x) (Irrational m y) = add_1 x y"

lemma add_2: assumes x: "invariant_2 x" and y: "invariant_2 y" 
  shows "invariant_2 (add_2 x y)" (is ?g1)
    and "real_of_2 (add_2 x y) = real_of_2 x + real_of_2 y" (is ?g2)
  using assms add_rat_1 add_1
  by (atomize (full), (cases x; cases y), auto simp: hom_distribs)

fun mult_2 :: "real_alg_2 \<Rightarrow> real_alg_2 \<Rightarrow> real_alg_2" where
  "mult_2 (Rational r) (Rational q) = Rational (r * q)"
| "mult_2 (Rational r) (Irrational n y) = mult_rat_1 r y"
| "mult_2 (Irrational n x) (Rational q) = mult_rat_1 q x"
| "mult_2 (Irrational n x) (Irrational m y) = mult_1 x y"

lemma mult_2: assumes "invariant_2 x" "invariant_2 y"
  shows "real_of_2 (mult_2 x y) = real_of_2 x * real_of_2 y"
  "invariant_2 (mult_2 x y)"
  using assms
  by (atomize(full), (cases x; cases y; auto simp: mult_rat_1 mult_1 hom_distribs))

fun to_rat_2 :: "real_alg_2 \<Rightarrow> rat option" where
  "to_rat_2 (Rational r) = Some r"
| "to_rat_2 (Irrational n rai) = None"

lemma to_rat_2: assumes rc: "invariant_2 x" 
  shows "to_rat_2 x = (if real_of_2 x \<in> \<rat> then Some (THE q. real_of_2 x = of_rat q) else None)"
proof (cases x)
  case (Irrational n rai)
  from real_of_2_Irrational[OF rc[unfolded this]] show ?thesis
    unfolding Irrational Rats_def by auto
qed simp 
  
fun equal_2 :: "real_alg_2 \<Rightarrow> real_alg_2 \<Rightarrow> bool" where
  "equal_2 (Rational r) (Rational q) = (r = q)" 
| "equal_2 (Irrational n (p,_)) (Irrational m (q,_)) = (p = q \<and> n = m)"
| "equal_2 (Rational r) (Irrational _ yy) = False"
| "equal_2 (Irrational _ xx) (Rational q) = False"

lemma equal_2[simp]: assumes rc: "invariant_2 x" "invariant_2 y" 
  shows "equal_2 x y = (real_of_2 x = real_of_2 y)"
  using info_2[OF rc]
  by (cases x; cases y, auto)

fun compare_2 :: "real_alg_2 \<Rightarrow> real_alg_2 \<Rightarrow> order" where 
  "compare_2 (Rational r) (Rational q) = (compare r q)"
| "compare_2 (Irrational n (p,l,r)) (Irrational m (q,l',r')) = (if p = q \<and> n = m then Eq
    else compare_1 p q l r (sgn (ipoly p r)) l' r' (sgn (ipoly q r')))" 
| "compare_2 (Rational r) (Irrational _ xx) = (compare_rat_1 r xx)"
| "compare_2 (Irrational _ xx) (Rational r) = (invert_order (compare_rat_1 r xx))"  

lemma compare_2: assumes rc: "invariant_2 x" "invariant_2 y"
  shows "compare_2 x y = compare (real_of_2 x) (real_of_2 y)"
proof (cases x)
  case (Rational r) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    show ?thesis unfolding xx yy by (simp add: compare_rat_def compare_real_def comparator_of_def of_rat_less)
  next
    case (Irrational n yy) note yy = this
    from compare_rat_1 rc
    show ?thesis unfolding xx yy by (simp add: of_rat_1)
  qed
next
  case (Irrational n xx) note xx = this
  show ?thesis
  proof (cases y)
    case (Rational q) note yy = this
    from compare_rat_1 rc
    show ?thesis unfolding xx yy by simp
  next
    case (Irrational m yy) note yy = this
    obtain p l r where xxx: "xx = (p,l,r)" by (cases xx)
    obtain q l' r' where yyy: "yy = (q,l',r')" by (cases yy)
    note rc = rc[unfolded xx xxx yy yyy]
    from rc have I: "invariant_1_2 (p,l,r)" "invariant_1_2 (q,l',r')" by auto
    then have "unique_root (p,l,r)" "unique_root (q,l',r')" "poly_cond2 p" "poly_cond2 q" by auto
    from compare_1[OF this _ refl refl]
    show ?thesis using equal_2[OF rc] unfolding xx xxx yy yyy by simp
  qed
qed

fun sgn_2 :: "real_alg_2 \<Rightarrow> rat" where
  "sgn_2 (Rational r) = sgn r"
| "sgn_2 (Irrational n rai) = sgn_1 rai"

lemma sgn_2: "invariant_2 x \<Longrightarrow> real_of_rat (sgn_2 x) = sgn (real_of_2 x)" 
  using sgn_1 by (cases x, auto simp: real_of_rat_sgn)

fun floor_2 :: "real_alg_2 \<Rightarrow> int" where
  "floor_2 (Rational r) = floor r"
| "floor_2 (Irrational n rai) = floor_1 rai"

lemma floor_2: "invariant_2 x \<Longrightarrow> floor_2 x = floor (real_of_2 x)"
  by (cases x, auto simp: floor_1)
  
(* *************** *)
subsubsection \<open>Definitions and Algorithms on Type with Invariant\<close>

lift_definition of_rat_3 :: "rat \<Rightarrow> real_alg_3" is of_rat_2
  by (auto simp: of_rat_2)


    
lemma of_rat_3: "real_of_3 (of_rat_3 x) = of_rat x"
  by (transfer, auto simp: of_rat_2)

lift_definition root_3 :: "nat \<Rightarrow> real_alg_3 \<Rightarrow> real_alg_3" is root_2 
  by (auto simp: root_2)

lemma root_3: "real_of_3 (root_3 n x) = root n (real_of_3 x)"
  by (transfer, auto simp: root_2)

lift_definition equal_3 :: "real_alg_3 \<Rightarrow> real_alg_3 \<Rightarrow> bool" is equal_2 .

lemma equal_3: "equal_3 x y = (real_of_3 x = real_of_3 y)"
  by (transfer, auto)  

lift_definition compare_3 :: "real_alg_3 \<Rightarrow> real_alg_3 \<Rightarrow> order" is compare_2 .

lemma compare_3: "compare_3 x y = (compare (real_of_3 x) (real_of_3 y))"
  by (transfer, auto simp: compare_2)  
    
lift_definition add_3 :: "real_alg_3 \<Rightarrow> real_alg_3 \<Rightarrow> real_alg_3" is add_2 
  by (auto simp: add_2)

lemma add_3: "real_of_3 (add_3 x y) = real_of_3 x + real_of_3 y"
  by (transfer, auto simp: add_2)

lift_definition mult_3 :: "real_alg_3 \<Rightarrow> real_alg_3 \<Rightarrow> real_alg_3" is mult_2 
  by (auto simp: mult_2)

lemma mult_3: "real_of_3 (mult_3 x y) = real_of_3 x * real_of_3 y"
  by (transfer, auto simp: mult_2)

lift_definition sgn_3 :: "real_alg_3 \<Rightarrow> rat" is sgn_2 . 

lemma sgn_3: "real_of_rat (sgn_3 x) = sgn (real_of_3 x)" 
  by (transfer, auto simp: sgn_2)

lift_definition to_rat_3 :: "real_alg_3 \<Rightarrow> rat option" is to_rat_2 .

lemma to_rat_3: "to_rat_3 x = 
  (if real_of_3 x \<in> \<rat> then Some (THE q. real_of_3 x = of_rat q) else None)"
  by (transfer, simp add: to_rat_2)

lift_definition floor_3 :: "real_alg_3 \<Rightarrow> int" is floor_2 .

lemma floor_3: "floor_3 x = floor (real_of_3 x)"
  by (transfer, auto simp: floor_2)

(* *************** *)
(* info *)

lift_definition info_3 :: "real_alg_3 \<Rightarrow> rat + int poly \<times> nat" is info_2 .  

lemma info_3_fun: "real_of_3 x = real_of_3 y \<Longrightarrow> info_3 x = info_3 y"
  by (transfer, intro info_2_unique, auto)

lift_definition info_real_alg :: "real_alg \<Rightarrow> rat + int poly \<times> nat" is info_3
  by (metis info_3_fun)
    
lemma info_real_alg: 
  "info_real_alg x = Inr (p,n) \<Longrightarrow> p represents (real_of x) \<and> card {y. y \<le> real_of x \<and> ipoly p y = 0} = n \<and> irreducible p" 
  "info_real_alg x = Inl q \<Longrightarrow> real_of x = of_rat q" 
proof (atomize(full), transfer, transfer, goal_cases)
  case (1 x p n q)
  from 1 have x: "invariant_2 x" by auto
  note info = info_2_card[OF this]
  show ?case 
  proof (cases x)
    case irr: (Irrational m rai)
    from info(1)[of p n]
    show ?thesis unfolding irr by (cases rai, auto simp: poly_cond_def)
  qed (insert 1 info, auto)
qed
    
(* add *)
instantiation real_alg :: plus
begin
lift_definition plus_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" is add_3
  by (simp add: add_3)
instance ..
end

lemma plus_real_alg: "(real_of x) + (real_of y) = real_of (x + y)"
  by (transfer, rule add_3[symmetric])

(* minus *)
instantiation real_alg :: minus
begin
definition minus_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" where
  "minus_real_alg x y = x + (-y)"
instance ..
end

lemma minus_real_alg: "(real_of x) - (real_of y) = real_of (x - y)"
  unfolding minus_real_alg_def minus_real_def uminus_real_alg plus_real_alg  ..  

(* of_rat *)
lift_definition of_rat_real_alg :: "rat \<Rightarrow> real_alg" is of_rat_3 .

lemma of_rat_real_alg: "real_of_rat x = real_of (of_rat_real_alg x)"
  by (transfer, rule of_rat_3[symmetric])

(* zero *)
instantiation real_alg :: zero
begin
definition zero_real_alg :: "real_alg" where "zero_real_alg \<equiv> of_rat_real_alg 0"
instance ..
end

lemma zero_real_alg: "0 = real_of 0"
  unfolding zero_real_alg_def by (simp add: of_rat_real_alg[symmetric])

(* one *)
instantiation real_alg :: one
begin
definition one_real_alg :: "real_alg" where "one_real_alg \<equiv> of_rat_real_alg 1"
instance ..
end

lemma one_real_alg: "1 = real_of 1"
  unfolding one_real_alg_def by (simp add: of_rat_real_alg[symmetric])

(* times *)
instantiation real_alg :: times
begin
lift_definition times_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" is mult_3
  by (simp add: mult_3)
instance ..
end

lemma times_real_alg: "(real_of x) * (real_of y) = real_of (x * y)"
  by (transfer, rule mult_3[symmetric])

(* inverse *)
instantiation real_alg :: inverse
begin
lift_definition inverse_real_alg :: "real_alg \<Rightarrow> real_alg" is inverse_3
  by (simp add: inverse_3)
definition divide_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg" where
  "divide_real_alg x y = x * inverse y" (* TODO: better to use poly_div *)
instance ..
end

lemma inverse_real_alg: "inverse (real_of x) = real_of (inverse x)"
  by (transfer, rule inverse_3[symmetric])

lemma divide_real_alg: "(real_of x) / (real_of y) = real_of (x / y)"
  unfolding divide_real_alg_def times_real_alg[symmetric] divide_real_def inverse_real_alg ..

(* group *)
instance real_alg :: ab_group_add
  apply intro_classes
  apply (transfer, unfold add_3, force)
  apply (unfold zero_real_alg_def, transfer, unfold add_3 of_rat_3, force)
  apply (transfer, unfold add_3 of_rat_3, force)
  apply (transfer, unfold add_3 uminus_3 of_rat_3, force)
  apply (unfold minus_real_alg_def, force)
done

(* field *)
instance real_alg :: field
  apply intro_classes
  apply (transfer, unfold mult_3, force)
  apply (transfer, unfold mult_3, force)
  apply (unfold one_real_alg_def, transfer, unfold mult_3 of_rat_3, force)
  apply (transfer, unfold mult_3 add_3, force simp: field_simps)
  apply (unfold zero_real_alg_def, transfer, unfold of_rat_3, force)
  apply (transfer, unfold mult_3 inverse_3 of_rat_3, force simp: field_simps)
  apply (unfold divide_real_alg_def, force)
  apply (transfer, unfold inverse_3 of_rat_3, force)
done

(* numeral *)
instance real_alg :: numeral ..  

(* root *)
lift_definition root_real_alg :: "nat \<Rightarrow> real_alg \<Rightarrow> real_alg" is root_3
  by (simp add: root_3)

lemma root_real_alg: "root n (real_of x) = real_of (root_real_alg n x)"
  by (transfer, rule root_3[symmetric])

(* sgn *)
lift_definition sgn_real_alg_rat :: "real_alg \<Rightarrow> rat" is sgn_3
  by (insert sgn_3, metis to_rat_of_rat)

lemma sgn_real_alg_rat: "real_of_rat (sgn_real_alg_rat x) = sgn (real_of x)" 
  by (transfer, auto simp: sgn_3)

instantiation real_alg :: sgn
begin
definition sgn_real_alg :: "real_alg \<Rightarrow> real_alg" where
  "sgn_real_alg x = of_rat_real_alg (sgn_real_alg_rat x)"
instance ..
end

lemma sgn_real_alg: "sgn (real_of x) = real_of (sgn x)"
  unfolding sgn_real_alg_def of_rat_real_alg[symmetric]
  by (transfer, simp add: sgn_3)

(* equal *)
instantiation real_alg :: equal
begin
lift_definition equal_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" is equal_3 
  by (simp add: equal_3)
instance 
proof
  fix x y :: real_alg
  show "equal_class.equal x y = (x = y)"
    by (transfer, simp add: equal_3)
qed
end

lemma equal_real_alg: "HOL.equal (real_of x) (real_of y) = (x = y)"
  unfolding equal_real_def by (transfer, auto)

(* comparisons *)
instantiation real_alg :: ord 
begin

definition less_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" where
  [code del]: "less_real_alg x y = (real_of x < real_of y)"

definition less_eq_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> bool" where
  [code del]: "less_eq_real_alg x y = (real_of x \<le> real_of y)"

instance ..
end    

lemma less_real_alg: "less (real_of x) (real_of y) = (x < y)" unfolding less_real_alg_def ..
lemma less_eq_real_alg: "less_eq (real_of x) (real_of y) = (x \<le> y)" unfolding less_eq_real_alg_def ..

instantiation real_alg :: compare_order
begin

lift_definition compare_real_alg :: "real_alg \<Rightarrow> real_alg \<Rightarrow> order" is compare_3
  by (simp add: compare_3)

lemma compare_real_alg: "compare (real_of x) (real_of y) = (compare x y)"
  by (transfer, simp add: compare_3)

instance
proof (intro_classes, unfold compare_real_alg[symmetric, abs_def])
  show "le_of_comp (\<lambda>x y. compare (real_of x) (real_of y)) = (\<le>)" 
    by (intro ext, auto simp: compare_real_def comparator_of_def le_of_comp_def less_eq_real_alg_def)
  show "lt_of_comp (\<lambda>x y. compare (real_of x) (real_of y)) = (<)"
    by (intro ext, auto simp: compare_real_def comparator_of_def lt_of_comp_def less_real_alg_def)
  show "comparator (\<lambda>x y. compare (real_of x) (real_of y))" 
    unfolding comparator_def 
  proof (intro conjI impI allI)
    fix x y z :: "real_alg"
    let ?r = real_of
    note rc = comparator_compare[where 'a = real, unfolded comparator_def]
    from rc show "invert_order (compare (?r x) (?r y)) = compare (?r y) (?r x)" by blast
    from rc show "compare (?r x) (?r y) = Lt \<Longrightarrow> compare (?r y) (?r z) = Lt \<Longrightarrow> compare (?r x) (?r z) = Lt" by blast
    assume "compare (?r x) (?r y) = Eq"
    with rc have "?r x = ?r y" by blast
    thus "x = y" unfolding real_of_inj .
  qed
qed
end
  
lemma less_eq_real_alg_code[code]: 
  "(less_eq :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool) = le_of_comp compare"
  "(less :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool) = lt_of_comp compare"
  by (rule ord_defs(1)[symmetric], rule ord_defs(2)[symmetric])

instantiation real_alg :: abs
begin

definition abs_real_alg :: "real_alg \<Rightarrow> real_alg" where
  "abs_real_alg x = (if real_of x < 0 then uminus x else x)"
instance ..
end

lemma abs_real_alg: "abs (real_of x) = real_of (abs x)"
  unfolding abs_real_alg_def abs_real_def if_distrib
  by (auto simp: uminus_real_alg)

lemma sgn_real_alg_sound: "sgn x = (if x = 0 then 0 else if 0 < real_of x then 1 else - 1)"
  (is "_ = ?r")
proof -
  have "real_of (sgn x) = sgn (real_of x)" by (simp add: sgn_real_alg)
  also have "\<dots> = real_of ?r" unfolding sgn_real_def if_distrib 
  by (auto simp: less_real_alg_def 
    zero_real_alg_def one_real_alg_def of_rat_real_alg[symmetric] equal_real_alg[symmetric]
    equal_real_def uminus_real_alg[symmetric])
  finally show "sgn x = ?r" unfolding equal_real_alg[symmetric] equal_real_def by simp
qed

lemma real_of_of_int: "real_of_rat (rat_of_int z) = real_of (of_int z)"
proof (cases "z \<ge> 0")
  case True
  define n where "n = nat z"
  from True have z: "z = int n" unfolding n_def by simp
  show ?thesis unfolding z
    by (induct n, auto simp: zero_real_alg plus_real_alg[symmetric] one_real_alg hom_distribs)
next
  case False
  define n where "n = nat (-z)"
  from False have z: "z = - int n" unfolding n_def by simp
  show ?thesis unfolding z
    by (induct n, auto simp: zero_real_alg plus_real_alg[symmetric] one_real_alg uminus_real_alg[symmetric]
      minus_real_alg[symmetric] hom_distribs)
qed

instance real_alg :: linordered_field
  apply standard
     apply (unfold less_eq_real_alg_def plus_real_alg[symmetric], force)
    apply (unfold abs_real_alg_def less_real_alg_def zero_real_alg[symmetric], rule refl)
   apply (unfold less_real_alg_def times_real_alg[symmetric], force)
  apply (rule sgn_real_alg_sound)
  done

instantiation real_alg :: floor_ceiling
begin
lift_definition floor_real_alg :: "real_alg \<Rightarrow> int" is floor_3
  by (auto simp: floor_3)

lemma floor_real_alg: "floor (real_of x) = floor x"
  by (transfer, auto simp: floor_3)

instance 
proof
  fix x :: real_alg
  show "of_int \<lfloor>x\<rfloor> \<le> x \<and> x < of_int (\<lfloor>x\<rfloor> + 1)" unfolding floor_real_alg[symmetric]
    using floor_correct[of "real_of x"] unfolding less_eq_real_alg_def less_real_alg_def
    real_of_of_int[symmetric] by (auto simp: hom_distribs)
  hence "x \<le> of_int (\<lfloor>x\<rfloor> + 1)" by auto
  thus "\<exists>z. x \<le> of_int z" by blast
qed
end

definition real_alg_of_real :: "real \<Rightarrow> real_alg" where
  "real_alg_of_real x = (if (\<exists> y. x = real_of y) then (THE y. x = real_of y) else 0)" 

lemma real_alg_of_real_code[code]: "real_alg_of_real (real_of x) = x"
  using real_of_inj unfolding real_alg_of_real_def by auto

lift_definition to_rat_real_alg_main :: "real_alg \<Rightarrow> rat option" is to_rat_3
  by (simp add: to_rat_3)

lemma to_rat_real_alg_main: "to_rat_real_alg_main x = (if real_of x \<in> \<rat> then 
  Some (THE q. real_of x = of_rat q) else None)"
  by (transfer, simp add: to_rat_3)

definition to_rat_real_alg :: "real_alg \<Rightarrow> rat" where
  "to_rat_real_alg x = (case to_rat_real_alg_main x of Some q \<Rightarrow> q | None \<Rightarrow> 0)"

definition is_rat_real_alg :: "real_alg \<Rightarrow> bool" where
  "is_rat_real_alg x = (case to_rat_real_alg_main x of Some q \<Rightarrow> True | None \<Rightarrow> False)"

lemma is_rat_real_alg: "is_rat (real_of x) = (is_rat_real_alg x)"
  unfolding is_rat_real_alg_def is_rat to_rat_real_alg_main by auto

lemma to_rat_real_alg: "to_rat (real_of x) = (to_rat_real_alg x)"
  unfolding to_rat to_rat_real_alg_def to_rat_real_alg_main by auto


subsection \<open>Real Algebraic Numbers as Implementation for Real Numbers\<close>

lemmas real_alg_code_eqns =  
  one_real_alg
  zero_real_alg
  uminus_real_alg
  root_real_alg
  minus_real_alg
  plus_real_alg
  times_real_alg
  inverse_real_alg
  divide_real_alg
  equal_real_alg
  less_real_alg
  less_eq_real_alg
  compare_real_alg
  sgn_real_alg
  abs_real_alg
  floor_real_alg
  is_rat_real_alg
  to_rat_real_alg

code_datatype real_of

declare [[code drop:
  "plus :: real \<Rightarrow> real \<Rightarrow> real"
  "uminus :: real \<Rightarrow> real"
  "minus :: real \<Rightarrow> real \<Rightarrow> real"
  "times :: real \<Rightarrow> real \<Rightarrow> real"
  "inverse :: real \<Rightarrow> real"
  "divide :: real \<Rightarrow> real \<Rightarrow> real"
  "floor :: real \<Rightarrow> int"
  "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"
  "compare :: real \<Rightarrow> real \<Rightarrow> order"
  "less_eq :: real \<Rightarrow> real \<Rightarrow> bool"
  "less :: real \<Rightarrow> real \<Rightarrow> bool"
  "0 :: real"
  "1 :: real"
  "sgn :: real \<Rightarrow> real"
  "abs :: real \<Rightarrow> real"
  root]]

declare real_alg_code_eqns [code equation]

lemma [code]:
  "Ratreal = real_of \<circ> of_rat_real_alg"
  by (transfer, transfer) (simp add: fun_eq_iff of_rat_2)

end
