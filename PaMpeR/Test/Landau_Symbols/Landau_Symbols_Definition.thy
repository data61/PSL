(*
  File:   Landau_Symbols_Definition.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Landau symbols for reasoning about the asymptotic growth of functions. 
*)
section {* Definition of Landau symbols *}

theory Landau_Symbols_Definition
imports 
  Complex_Main
  "HOL-Library.Function_Algebras" 
  "HOL-Library.Set_Algebras"
  Landau_Library
begin

subsection {* Eventual non-negativity/non-zeroness *}

text {* 
  For certain transformations of Landau symbols, it is required that the functions involved 
  are eventually non-negative of non-zero. In the following, we set up a system to guide the 
  simplifier to discharge these requirements during simplification at least in obvious cases.
*}

definition "eventually_nonzero F f \<longleftrightarrow> eventually (\<lambda>x. (f x :: _ :: real_normed_field) \<noteq> 0) F"
definition "eventually_nonneg F f \<longleftrightarrow> eventually (\<lambda>x. (f x :: _ :: linordered_field) \<ge> 0) F"

named_theorems eventually_nonzero_simps

lemmas [eventually_nonzero_simps] = 
  eventually_nonzero_def [symmetric] eventually_nonneg_def [symmetric]

lemma eventually_nonzeroD: "eventually_nonzero F f \<Longrightarrow> eventually (\<lambda>x. f x \<noteq> 0) F"
  by (simp add: eventually_nonzero_def)

lemma eventually_nonzero_const [eventually_nonzero_simps]:
  "eventually_nonzero F (\<lambda>_::_::linorder. c) \<longleftrightarrow> F = bot \<or> c \<noteq> 0"
  unfolding eventually_nonzero_def by (auto simp add: eventually_False)

lemma eventually_nonzero_inverse [eventually_nonzero_simps]:
  "eventually_nonzero F (\<lambda>x. inverse (f x)) \<longleftrightarrow> eventually_nonzero F f"
  unfolding eventually_nonzero_def by simp

lemma eventually_nonzero_mult [eventually_nonzero_simps]:
  "eventually_nonzero F (\<lambda>x. f x * g x) \<longleftrightarrow> eventually_nonzero F f \<and> eventually_nonzero F g"
  unfolding eventually_nonzero_def by (simp_all add: eventually_conj_iff[symmetric])

lemma eventually_nonzero_pow [eventually_nonzero_simps]:
  "eventually_nonzero F (\<lambda>x::_::linorder. f x ^ n) \<longleftrightarrow> n = 0 \<or> eventually_nonzero F f"
  by (induction n) (auto simp: eventually_nonzero_simps)

lemma eventually_nonzero_divide [eventually_nonzero_simps]:
  "eventually_nonzero F (\<lambda>x. f x / g x) \<longleftrightarrow> eventually_nonzero F f \<and> eventually_nonzero F g"
  unfolding eventually_nonzero_def by (simp_all add: eventually_conj_iff[symmetric])

lemma eventually_nonzero_ident_at_top_linorder [eventually_nonzero_simps]:
  "eventually_nonzero at_top (\<lambda>x::'a::{real_normed_field,linordered_field}. x)"
  unfolding eventually_nonzero_def by (simp add: eventually_not_equal)
    
lemma eventually_nonzero_ident_nhds [eventually_nonzero_simps]:
  "eventually_nonzero (nhds a) (\<lambda>x. x) \<longleftrightarrow> a \<noteq> 0"
  using eventually_nhds_in_open[of "-{0}" a]
  by (auto elim!: eventually_mono simp: eventually_nonzero_def open_Compl 
           dest: eventually_nhds_x_imp_x)

lemma eventually_nonzero_ident_at_within [eventually_nonzero_simps]:
  "eventually_nonzero (at a within A) (\<lambda>x. x)"
  using eventually_nonzero_ident_nhds[of a]
  by (cases "a = 0") (auto simp: eventually_nonzero_def eventually_at_filter elim!: eventually_mono)

lemma eventually_nonzero_ln_at_top [eventually_nonzero_simps]:
  "eventually_nonzero at_top (\<lambda>x::real. ln x)"
  unfolding eventually_nonzero_def by (subst eventually_ln_at_top) (rule eventually_not_equal)

lemma eventually_nonzero_ln_const_at_top [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonzero at_top (\<lambda>x. ln (b * x :: real))"
  unfolding eventually_nonzero_def 
    apply (rule eventually_mono [OF eventually_gt_at_top[of "max 1 (inverse b)"]])
  by (metis exp_ln exp_minus exp_minus_inverse less_numeral_extra(3) ln_gt_zero max_less_iff_conj mult.commute mult_strict_right_mono)

lemma eventually_nonzero_ln_const'_at_top [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonzero at_top (\<lambda>x. ln (x * b :: real))"
  using eventually_nonzero_ln_const_at_top[of b] by (simp add: mult.commute)

lemma eventually_nonzero_powr_at_top [eventually_nonzero_simps]:
  "eventually_nonzero at_top (\<lambda>x::real. f x powr p) \<longleftrightarrow> eventually_nonzero at_top f"
  unfolding eventually_nonzero_def by simp



lemma eventually_nonneg_const [eventually_nonzero_simps]:
  "eventually_nonneg F (\<lambda>_. c) \<longleftrightarrow> F = bot \<or> c \<ge> 0"
  unfolding eventually_nonneg_def by (auto simp: eventually_False)

lemma eventually_nonneg_inverse [eventually_nonzero_simps]:
  "eventually_nonneg F (\<lambda>x. inverse (f x)) \<longleftrightarrow> eventually_nonneg F f"
  unfolding eventually_nonneg_def by (intro eventually_subst) (auto)

lemma eventually_nonneg_add [eventually_nonzero_simps]:
  assumes "eventually_nonneg F f" "eventually_nonneg F g"
  shows   "eventually_nonneg F (\<lambda>x. f x + g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_mult [eventually_nonzero_simps]:
  assumes "eventually_nonneg F f" "eventually_nonneg F g"
  shows   "eventually_nonneg F (\<lambda>x. f x * g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_mult' [eventually_nonzero_simps]:
  assumes "eventually_nonneg F (\<lambda>x. -f x)" "eventually_nonneg F (\<lambda>x. - g x)"
  shows   "eventually_nonneg F (\<lambda>x. f x * g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim (auto intro: mult_nonpos_nonpos)

lemma eventually_nonneg_divide [eventually_nonzero_simps]:
  assumes "eventually_nonneg F f" "eventually_nonneg F g"
  shows   "eventually_nonneg F (\<lambda>x. f x / g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim simp

lemma eventually_nonneg_divide' [eventually_nonzero_simps]:
  assumes "eventually_nonneg F (\<lambda>x. -f x)" "eventually_nonneg F (\<lambda>x. - g x)"
  shows   "eventually_nonneg F (\<lambda>x. f x / g x)"
  using assms unfolding eventually_nonneg_def by eventually_elim (auto intro: divide_nonpos_nonpos)

lemma eventually_nonneg_ident_at_top [eventually_nonzero_simps]:
  "eventually_nonneg at_top (\<lambda>x. x)" unfolding eventually_nonneg_def by (rule eventually_ge_at_top)

lemma eventually_nonneg_ident_nhds [eventually_nonzero_simps]:
  fixes a :: "'a :: {linorder_topology, linordered_field}"
  shows "a > 0 \<Longrightarrow> eventually_nonneg (nhds a) (\<lambda>x. x)" unfolding eventually_nonneg_def
  using eventually_nhds_in_open[of "{0<..}" a]
  by (auto simp: eventually_nonneg_def dest: eventually_nhds_x_imp_x elim!: eventually_mono)

lemma eventually_nonneg_ident_at_within [eventually_nonzero_simps]:
  fixes a :: "'a :: {linorder_topology, linordered_field}"
  shows "a > 0 \<Longrightarrow> eventually_nonneg (at a within A) (\<lambda>x. x)"
  using eventually_nonneg_ident_nhds[of a]
  by (auto simp: eventually_nonneg_def eventually_at_filter elim: eventually_mono)

lemma eventually_nonneg_pow [eventually_nonzero_simps]:
  "eventually_nonneg F f \<Longrightarrow> eventually_nonneg F (\<lambda>x. f x ^ n)"
  by (induction n) (auto simp: eventually_nonzero_simps)

lemma eventually_nonneg_powr [eventually_nonzero_simps]:
  "eventually_nonneg F (\<lambda>x. f x powr y :: real)" by (simp add: eventually_nonneg_def)

lemma eventually_nonneg_ln_at_top [eventually_nonzero_simps]:
  "eventually_nonneg at_top (\<lambda>x. ln x :: real)" 
  by (simp add: eventually_nonneg_def eventually_ln_at_top eventually_ge_at_top)

lemma eventually_nonneg_ln_const [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonneg at_top (\<lambda>x. ln (b*x) :: real)" 
  unfolding eventually_nonneg_def using eventually_ge_at_top[of "inverse b"]
  by eventually_elim (simp_all add: field_simps)

lemma eventually_nonneg_ln_const' [eventually_nonzero_simps]:
  "b > 0 \<Longrightarrow> eventually_nonneg at_top (\<lambda>x. ln (x*b) :: real)" 
  using eventually_nonneg_ln_const[of b] by (simp add: mult.commute)



subsection {* Definition of Landau symbols *}

text {*
  Our Landau symbols are sign-oblivious, i.e. any function always has the same growth 
  as its absolute. This has the advantage of making some cancelling rules for sums nicer, but 
  introduces some problems in other places. Nevertheless, we found this definition more convenient
  to work with.
*}

(* TODO: Generalise w.r.t. arbitrary filters? *)

definition bigo :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" 
    ("(1O[_]'(_'))")
  where "bigo F g = {f. (\<exists>c>0. eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F)}"  

definition smallo :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" 
    ("(1o[_]'(_'))")
  where "smallo F g = {f. (\<forall>c>0. eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F)}"

definition bigomega :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" 
    ("(1\<Omega>[_]'(_'))")
  where "bigomega F g = {f. (\<exists>c>0. eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F)}"  

definition smallomega :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" 
    ("(1\<omega>[_]'(_'))")
  where "smallomega F g = {f. (\<forall>c>0. eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F)}"

definition bigtheta :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set" 
    ("(1\<Theta>[_]'(_'))")
  where "bigtheta F g = bigo F g \<inter> bigomega F g"

abbreviation bigo_at_top ("(2O'(_'))") where
  "O(g) \<equiv> bigo at_top g"    

abbreviation smallo_at_top ("(2o'(_'))") where
  "o(g) \<equiv> smallo at_top g"

abbreviation bigomega_at_top ("(2\<Omega>'(_'))") where
  "\<Omega>(g) \<equiv> bigomega at_top g"

abbreviation smallomega_at_top ("(2\<omega>'(_'))") where
  "\<omega>(g) \<equiv> smallomega at_top g"

abbreviation bigtheta_at_top ("(2\<Theta>'(_'))") where
  "\<Theta>(g) \<equiv> bigtheta at_top g"
    

text {* The following is a set of properties that all Landau symbols satisfy. *}

named_theorems landau_divide_simps

locale landau_symbol =
  fixes L  :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  and   L'  :: "'c filter \<Rightarrow> ('c \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('c \<Rightarrow> 'b) set"
  and   Lr  :: "'a filter \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) set"
  assumes bot': "L bot f = UNIV"
  assumes filter_mono': "F1 \<le> F2 \<Longrightarrow> L F2 f \<subseteq> L F1 f"
  assumes in_filtermap_iff: 
    "f' \<in> L (filtermap h' F') g' \<longleftrightarrow> (\<lambda>x. f' (h' x)) \<in> L' F' (\<lambda>x. g' (h' x))"
  assumes filtercomap: 
    "f' \<in> L F'' g' \<Longrightarrow> (\<lambda>x. f' (h' x)) \<in> L' (filtercomap h' F'') (\<lambda>x. g' (h' x))"
  assumes sup: "f \<in> L F1 g \<Longrightarrow> f \<in> L F2 g \<Longrightarrow> f \<in> L (sup F1 F2) g"
  assumes in_cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)"
  assumes cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> L F (f) = L F (g)"
  assumes cong_bigtheta: "f \<in> \<Theta>[F](g) \<Longrightarrow> L F (f) = L F (g)"
  assumes in_cong_bigtheta: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)"
  assumes cmult [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. c * f x) = L F (f)"
  assumes cmult_in_iff [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. c * f x) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  assumes mult_left [simp]: "f \<in> L F (g) \<Longrightarrow> (\<lambda>x. h x * f x) \<in> L F (\<lambda>x. h x * g x)"
  assumes inverse: "eventually (\<lambda>x. f x \<noteq> 0) F \<Longrightarrow> eventually (\<lambda>x. g x \<noteq> 0) F \<Longrightarrow> 
                        f \<in> L F (g) \<Longrightarrow> (\<lambda>x. inverse (g x)) \<in> L F (\<lambda>x. inverse (f x))"
  assumes subsetI: "f \<in> L F (g) \<Longrightarrow> L F (f) \<subseteq> L F (g)"
  assumes plus_subset1: "f \<in> o[F](g) \<Longrightarrow> L F (g) \<subseteq> L F (\<lambda>x. f x + g x)"
  assumes trans: "f \<in> L F (g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  assumes compose: "f \<in> L F (g) \<Longrightarrow> filterlim h' F G \<Longrightarrow> (\<lambda>x. f (h' x)) \<in> L' G (\<lambda>x. g (h' x))"
  assumes norm_iff [simp]: "(\<lambda>x. norm (f x)) \<in> Lr F (\<lambda>x. norm (g x)) \<longleftrightarrow> f \<in> L F (g)"
  assumes abs [simp]: "Lr Fr (\<lambda>x. \<bar>fr x\<bar>) = Lr Fr fr"
  assumes abs_in_iff [simp]: "(\<lambda>x. \<bar>fr x\<bar>) \<in> Lr Fr gr \<longleftrightarrow> fr \<in> Lr Fr gr"
begin

lemma bot [simp]: "f \<in> L bot g" by (simp add: bot')
  
lemma filter_mono: "F1 \<le> F2 \<Longrightarrow> f \<in> L F2 g \<Longrightarrow> f \<in> L F1 g"
  using filter_mono'[of F1 F2] by blast

lemma cong_ex: 
  "eventually (\<lambda>x. f1 x = f2 x) F \<Longrightarrow> eventually (\<lambda>x. g1 x = g2 x) F \<Longrightarrow>
     f1 \<in> L F (g1) \<longleftrightarrow> f2 \<in> L F (g2)" 
  by (subst cong, assumption, subst in_cong, assumption, rule refl)

lemma cong_ex_bigtheta: 
  "f1 \<in> \<Theta>[F](f2) \<Longrightarrow> g1 \<in> \<Theta>[F](g2) \<Longrightarrow> f1 \<in> L F (g1) \<longleftrightarrow> f2 \<in> L F (g2)" 
  by (subst cong_bigtheta, assumption, subst in_cong_bigtheta, assumption, rule refl)

lemma bigtheta_trans1: 
  "f \<in> L F (g) \<Longrightarrow> g \<in> \<Theta>[F](h) \<Longrightarrow> f \<in> L F (h)"
  by (subst cong_bigtheta[symmetric])

lemma bigtheta_trans2: 
  "f \<in> \<Theta>[F](g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (subst in_cong_bigtheta)
    
lemma cmult' [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. f x * c) = L F (f)"
  by (subst mult.commute) (rule cmult)

lemma cmult_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x * c) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  by (subst mult.commute) (rule cmult_in_iff)

lemma cdiv [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. f x / c) = L F (f)"
  using cmult'[of "inverse c" F f] by (simp add: field_simps)

lemma cdiv_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x / c) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  using cmult_in_iff'[of "inverse c" f] by (simp add: field_simps)
  
lemma uminus [simp]: "L F (\<lambda>x. -g x) = L F (g)" using cmult[of "-1"] by simp

lemma uminus_in_iff [simp]: "(\<lambda>x. -f x) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  using cmult_in_iff[of "-1"] by simp

lemma const: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>_. c) = L F (\<lambda>_. 1)"
  by (subst (2) cmult[symmetric]) simp_all

(* Simplifier loops without the NO_MATCH *)
lemma const' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> L F (\<lambda>_. c) = L F (\<lambda>_. 1)"
  by (rule const)

lemma const_in_iff: "c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L F (f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (f)"
  using cmult_in_iff'[of c "\<lambda>_. 1"] by simp

lemma const_in_iff' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L F (f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (f)"
  by (rule const_in_iff)

lemma plus_subset2: "g \<in> o[F](f) \<Longrightarrow> L F (f) \<subseteq> L F (\<lambda>x. f x + g x)"
  by (subst add.commute) (rule plus_subset1)

lemma mult_right [simp]: "f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (\<lambda>x. g x * h x)"
  using mult_left by (simp add: mult.commute)

lemma mult: "f1 \<in> L F (g1) \<Longrightarrow> f2 \<in> L F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
  by (rule trans, erule mult_left, erule mult_right)

lemma inverse_cancel:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "(\<lambda>x. inverse (f x)) \<in> L F (\<lambda>x. inverse (g x)) \<longleftrightarrow> g \<in> L F (f)"
proof
  assume "(\<lambda>x. inverse (f x)) \<in> L F (\<lambda>x. inverse (g x))"
  from inverse[OF _ _ this] assms show "g \<in> L F (f)" by simp
qed (intro inverse assms)

lemma divide_right:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  assumes "f \<in> L F (g)"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x)"
  by (subst (1 2) divide_inverse) (intro mult_right inverse assms)

lemma divide_right_iff:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> f \<in> L F (g)"
proof
  assume "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x)"
  from mult_right[OF this, of h] assms show "f \<in> L F (g)"
    by (subst (asm) cong_ex[of _ f F _ g]) (auto elim!: eventually_mono)
qed (simp add: divide_right assms)

lemma divide_left:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "g \<in> L F(f)"
  shows   "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x)"
  by (subst (1 2) divide_inverse) (intro mult_left inverse assms)

lemma divide_left_iff:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x) \<longleftrightarrow> g \<in> L F (f)"
proof
  assume A: "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x)"
  from assms have B: "eventually (\<lambda>x. h x / f x / h x = inverse (f x)) F"
    by eventually_elim (simp add: divide_inverse)
  from assms have C: "eventually (\<lambda>x. h x / g x / h x = inverse (g x)) F"
    by eventually_elim (simp add: divide_inverse)
  from divide_right[OF assms(3) A] assms show "g \<in> L F (f)"
    by (subst (asm) cong_ex[OF B C]) (simp add: inverse_cancel)
qed (simp add: divide_left assms)

lemma divide:
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  assumes "f1 \<in> L F (f2)" "g2 \<in> L F (g1)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> L F (\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse) (intro mult inverse assms)
  
lemma divide_eq1:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "f \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
proof-
  have "f \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x / h x) \<in> L F (\<lambda>x. g x / h x)"
    using assms by (intro in_cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma divide_eq2:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x) \<longleftrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
proof-
  have "L F (\<lambda>x. g x) = L F (\<lambda>x. g x * h x / h x)"
    using assms by (intro cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma inverse_eq1:
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> L F (\<lambda>x. inverse (g x)) \<longleftrightarrow> (\<lambda>x. f x * g x) \<in> L F (\<lambda>_. 1)"
  using divide_eq1[of g F f "\<lambda>_. 1"] by (simp add: divide_inverse assms)

lemma inverse_eq2:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  shows   "(\<lambda>x. inverse (f x)) \<in> L F (g) \<longleftrightarrow> (\<lambda>x. 1) \<in> L F (\<lambda>x. f x * g x)"
  using divide_eq2[of f F "\<lambda>_. 1" g] by (simp add: divide_inverse assms mult_ac)

lemma inverse_flip:
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  assumes "(\<lambda>x. inverse (g x)) \<in> L F (h)"
  shows   "(\<lambda>x. inverse (h x)) \<in> L F (g)"
using assms by (simp add: divide_eq1 divide_eq2 inverse_eq_divide mult.commute)

lemma lift_trans:
  assumes "f \<in> L F (g)"
  assumes "(\<lambda>x. t x (g x)) \<in> L F (h)"
  assumes "\<And>f g. f \<in> L F (g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L F (\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L F (h)"
  by (rule trans[OF assms(3)[OF assms(1)] assms(2)])

lemma lift_trans':
  assumes "f \<in> L F (\<lambda>x. t x (g x))"
  assumes "g \<in> L F (h)"
  assumes "\<And>g h. g \<in> L F (h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> L F (\<lambda>x. t x (h x))"
  shows   "f \<in> L F (\<lambda>x. t x (h x))"
  by (rule trans[OF assms(1) assms(3)[OF assms(2)]])

lemma lift_trans_bigtheta:
  assumes "f \<in> L F (g)"
  assumes "(\<lambda>x. t x (g x)) \<in> \<Theta>[F](h)"
  assumes "\<And>f g. f \<in> L F (g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L F (\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L F (h)"
  using cong_bigtheta[OF assms(2)] assms(3)[OF assms(1)] by simp

lemma lift_trans_bigtheta':
  assumes "f \<in> L F (\<lambda>x. t x (g x))"
  assumes "g \<in> \<Theta>[F](h)"
  assumes "\<And>g h. g \<in> \<Theta>[F](h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> \<Theta>[F](\<lambda>x. t x (h x))"
  shows   "f \<in> L F (\<lambda>x. t x (h x))"
  using cong_bigtheta[OF assms(3)[OF assms(2)]] assms(1)  by simp

lemmas [landau_divide_simps] = 
  inverse_cancel divide_left_iff divide_eq1 divide_eq2 inverse_eq1 inverse_eq2

end


text {* 
  The symbols $O$ and $o$ and $\Omega$ and $\omega$ are dual, so for many rules, replacing $O$ with 
  $\Omega$, $o$ with $\omega$, and $\leq$ with $\geq$ in a theorem yields another valid theorem.
  The following locale captures this fact.
*}

locale landau_pair = 
  fixes L l :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  fixes L' l' :: "'c filter \<Rightarrow> ('c \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('c \<Rightarrow> 'b) set"
  fixes Lr lr :: "'a filter \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) set"
  and   R :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes L_def: "L F g = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F}"
  and     l_def: "l F g = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F}"
  and     L'_def: "L' F' g' = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g' x))) F'}"
  and     l'_def: "l' F' g' = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g' x))) F'}"
  and     Lr_def: "Lr F'' g'' = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g'' x))) F''}"
  and     lr_def: "lr F'' g'' = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g'' x))) F''}"
  and     R:     "R = op \<le> \<or> R = op \<ge>"

interpretation landau_o: 
    landau_pair bigo smallo bigo smallo bigo smallo "op \<le>"
  by unfold_locales (auto simp: bigo_def smallo_def intro!: ext)

interpretation landau_omega: 
    landau_pair bigomega smallomega bigomega smallomega bigomega smallomega "op \<ge>"
  by unfold_locales (auto simp: bigomega_def smallomega_def intro!: ext)


context landau_pair
begin

lemmas R_E = disjE [OF R, case_names le ge]

lemma bigI:
  "c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F \<Longrightarrow> f \<in> L F (g)"
  unfolding L_def by blast

lemma bigE:
  assumes "f \<in> L F (g)"
  obtains c where "c > 0" "eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F"
  using assms unfolding L_def by blast

lemma smallI:
  "(\<And>c. c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F) \<Longrightarrow> f \<in> l F (g)"
  unfolding l_def by blast

lemma smallD:
  "f \<in> l F (g) \<Longrightarrow> c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F"
  unfolding l_def by blast
    
lemma bigE_nonneg_real:
  assumes "f \<in> Lr F (g)" "eventually (\<lambda>x. f x \<ge> 0) F"
  obtains c where "c > 0" "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
proof-
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F"
    by (auto simp: Lr_def)
  from c(2) assms(2) have "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
    by eventually_elim simp
  from c(1) and this show ?thesis by (rule that)
qed

lemma smallD_nonneg_real:
  assumes "f \<in> lr F (g)" "eventually (\<lambda>x. f x \<ge> 0) F" "c > 0"
  shows   "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
  using assms by (auto simp: lr_def dest!: spec[of _ c] elim: eventually_elim2)

lemma small_imp_big: "f \<in> l F (g) \<Longrightarrow> f \<in> L F (g)"
  by (rule bigI[OF _ smallD, of 1]) simp_all
  
lemma small_subset_big: "l F (g) \<subseteq> L F (g)"
  using small_imp_big by blast

lemma R_refl [simp]: "R x x" using R by auto

lemma R_linear: "\<not>R x y \<Longrightarrow> R y x"
  using R by auto

lemma R_trans [trans]: "R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  using R by auto

lemma R_mult_left_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (c*a) (c*b)"
  using R by (auto simp: mult_left_mono)

lemma R_mult_right_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (a*c) (b*c)"
  using R by (auto simp: mult_right_mono)

lemma big_trans:
  assumes "f \<in> L F (g)" "g \<in> L F (h)"
  shows   "f \<in> L F (h)"
proof-
  from assms(1) guess c by (elim bigE) note c = this
  from assms(2) guess d by (elim bigE) note d = this
  from c(2) d(2) have "eventually (\<lambda>x. R (norm (f x)) (c * d * (norm (h x)))) F"
  proof eventually_elim
    fix x assume "R (norm (f x)) (c * (norm (g x)))"
    also assume "R (norm (g x)) (d * (norm (h x)))"
    with c(1) have "R (c * (norm (g x))) (c * (d * (norm (h x))))"
      by (intro R_mult_left_mono) simp_all
    finally show "R (norm (f x)) (c * d * (norm (h x)))" by (simp add: algebra_simps)
  qed
  with c(1) d(1) show ?thesis by (intro bigI[of "c*d"]) simp_all
qed

lemma big_small_trans:
  assumes "f \<in> L F (g)" "g \<in> l F (h)"
  shows   "f \<in> l F (h)"
proof (rule smallI)
  fix c :: real assume c: "c > 0"
  from assms(1) guess d by (elim bigE) note d = this
  note d(2)
  moreover from c d assms(2) 
    have "eventually (\<lambda>x. R (norm (g x)) (c * inverse d * norm (h x))) F" 
    by (intro smallD) simp_all
  ultimately show "eventually (\<lambda>x. R (norm (f x)) (c * (norm (h x)))) F"
    by eventually_elim (erule R_trans, insert R d(1), auto simp: field_simps)
qed

lemma small_big_trans:
  assumes "f \<in> l F (g)" "g \<in> L F (h)"
  shows   "f \<in> l F (h)"
proof (rule smallI)
  fix c :: real assume c: "c > 0"
  from assms(2) guess d by (elim bigE) note d = this
  note d(2)
  moreover from c d assms(1) 
    have "eventually (\<lambda>x. R (norm (f x)) (c * inverse d * norm (g x))) F"
    by (intro smallD) simp_all
  ultimately show "eventually (\<lambda>x. R (norm (f x)) (c * norm (h x))) F"
    by eventually_elim (rotate_tac 2, erule R_trans, insert R c d(1), auto simp: field_simps)
qed

lemma small_trans:
  "f \<in> l F (g) \<Longrightarrow> g \<in> l F (h) \<Longrightarrow> f \<in> l F (h)"
  by (rule big_small_trans[OF small_imp_big])

lemma small_big_trans':
  "f \<in> l F (g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule small_imp_big[OF small_big_trans])

lemma big_small_trans':
  "f \<in> L F (g) \<Longrightarrow> g \<in> l F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule small_imp_big[OF big_small_trans])

lemma big_subsetI [intro]: "f \<in> L F (g) \<Longrightarrow> L F (f) \<subseteq> L F (g)"
  by (intro subsetI) (drule (1) big_trans)

lemma small_subsetI [intro]: "f \<in> L F (g) \<Longrightarrow> l F (f) \<subseteq> l F (g)"
  by (intro subsetI) (drule (1) small_big_trans)

lemma big_refl [simp]: "f \<in> L F (f)"
  by (rule bigI[of 1]) simp_all

lemma small_refl_iff: "f \<in> l F (f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof (rule iffI[OF _ smallI])
  assume f: "f \<in> l F f"
  have "(1/2::real) > 0" "(2::real) > 0" by simp_all
  from smallD[OF f this(1)] smallD[OF f this(2)]
    show "eventually (\<lambda>x. f x = 0) F" by eventually_elim (insert R, auto)
next
  fix c :: real assume "c > 0" "eventually (\<lambda>x. f x = 0) F"
  from this(2) show "eventually (\<lambda>x. R (norm (f x)) (c * norm (f x))) F"
    by eventually_elim simp_all
qed

lemma big_small_asymmetric: "f \<in> L F (g) \<Longrightarrow> g \<in> l F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) big_small_trans) (simp add: small_refl_iff)

lemma small_big_asymmetric: "f \<in> l F (g) \<Longrightarrow> g \<in> L F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) small_big_trans) (simp add: small_refl_iff)

lemma small_asymmetric: "f \<in> l F (g) \<Longrightarrow> g \<in> l F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) small_trans) (simp add: small_refl_iff)


lemma plus_aux:
  assumes "f \<in> o[F](g)"
  shows "g \<in> L F (\<lambda>x. f x + g x)"
proof (rule R_E)
  assume [simp]: "R = op \<le>"
  have A: "1/2 > (0::real)" by simp
  {
    fix x assume "norm (f x) \<le> 1/2 * norm (g x)"
    hence "1/2 * (norm (g x)) \<le> (norm (g x)) - (norm (f x))" by simp
    also have "norm (g x) - norm (f x) \<le> norm (f x + g x)"
      by (subst add.commute) (rule norm_diff_ineq)
    finally have "1/2 * (norm (g x)) \<le> norm (f x + g x)" by simp
  } note B = this
  
  show "g \<in> L F (\<lambda>x. f x + g x)"
    apply (rule bigI[of "2"], simp)
    using landau_o.smallD[OF assms A] apply eventually_elim
    using B apply (simp add: algebra_simps) 
    done
next
  assume [simp]: "R = (\<lambda>x y. x \<ge> y)"
  show "g \<in> L F (\<lambda>x. f x + g x)"
  proof (rule bigI[of "1/2"])
    show "eventually (\<lambda>x. R (norm (g x)) (1/2 * norm (f x + g x))) F"
      using landau_o.smallD[OF assms zero_less_one]
    proof eventually_elim
      case (elim x)
      have "norm (f x + g x) \<le> norm (f x) + norm (g x)" by (rule norm_triangle_ineq)
      also note elim
      finally show ?case by simp
    qed
  qed simp_all
qed

end



lemma bigomega_iff_bigo: "g \<in> \<Omega>[F](f) \<longleftrightarrow> f \<in> O[F](g)"
proof
  assume "f \<in> O[F](g)"
  then guess c by (elim landau_o.bigE)
  thus "g \<in> \<Omega>[F](f)" by (intro landau_omega.bigI[of "inverse c"]) (simp_all add: field_simps)
next
  assume "g \<in> \<Omega>[F](f)"
  then guess c by (elim landau_omega.bigE)
  thus "f \<in> O[F](g)" by (intro landau_o.bigI[of "inverse c"]) (simp_all add: field_simps)
qed

lemma smallomega_iff_smallo: "g \<in> \<omega>[F](f) \<longleftrightarrow> f \<in> o[F](g)"
proof
  assume "f \<in> o[F](g)"
  from landau_o.smallD[OF this, of "inverse c" for c]
    show "g \<in> \<omega>[F](f)" by (intro landau_omega.smallI) (simp_all add: field_simps)
next
  assume "g \<in> \<omega>[F](f)"
  from landau_omega.smallD[OF this, of "inverse c" for c]
    show "f \<in> o[F](g)" by (intro landau_o.smallI) (simp_all add: field_simps)
qed


context landau_pair
begin

lemma big_mono:
  "eventually (\<lambda>x. R (norm (f x)) (norm (g x))) F \<Longrightarrow> f \<in> L F (g)"
  by (rule bigI[OF zero_less_one]) simp

lemma big_mult:
  assumes "f1 \<in> L F (g1)" "f2 \<in> L F (g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
proof-
  from assms(1) guess c1 by (elim bigE) note c1 = this
  from assms(2) guess c2 by (elim bigE) note c2 = this
  
  from c1(1) and c2(1) have "c1 * c2 > 0" by simp
  moreover have "eventually (\<lambda>x. R (norm (f1 x * f2 x)) (c1 * c2 * norm (g1 x * g2 x))) F"
    using c1(2) c2(2)
  proof eventually_elim
    case (elim x)
    show ?case
    proof (cases rule: R_E)
      case le
      have "norm (f1 x) * norm (f2 x) \<le> (c1 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim le c1(1) c2(1) by (intro mult_mono mult_nonneg_nonneg) auto
      with le show ?thesis by (simp add: le norm_mult mult_ac)
    next
      case ge
      have "(c1 * norm (g1 x)) * (c2 * norm (g2 x)) \<le> norm (f1 x) * norm (f2 x)"
        using elim ge c1(1) c2(1) by (intro mult_mono mult_nonneg_nonneg) auto
      with ge show ?thesis by (simp_all add: norm_mult mult_ac)
    qed
  qed
  ultimately show ?thesis by (rule bigI)
qed

lemma small_big_mult:
  assumes "f1 \<in> l F (g1)" "f2 \<in> L F (g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
proof (rule smallI)
  fix c1 :: real assume c1: "c1 > 0"
  from assms(2) guess c2 by (elim bigE) note c2 = this
  with c1 assms(1) have "eventually (\<lambda>x. R (norm (f1 x)) (c1 * inverse c2 * norm (g1 x))) F"
    by (auto intro!: smallD)
  thus "eventually (\<lambda>x. R (norm (f1 x * f2 x)) (c1 * norm (g1 x * g2 x))) F" using c2(2)
  proof eventually_elim
    case (elim x)
    show ?case
    proof (cases rule: R_E)
      case le
      have "norm (f1 x) * norm (f2 x) \<le> (c1 * inverse c2 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim le c1(1) c2(1) by (intro mult_mono mult_nonneg_nonneg) auto
      with le c2(1) show ?thesis by (simp add: le norm_mult field_simps)
    next
      case ge
      have "norm (f1 x) * norm (f2 x) \<ge> (c1 * inverse c2 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim ge c1(1) c2(1) by (intro mult_mono mult_nonneg_nonneg) auto
      with ge c2(1) show ?thesis by (simp add: ge norm_mult field_simps)
    qed
  qed
qed

lemma big_small_mult: 
  "f1 \<in> L F (g1) \<Longrightarrow> f2 \<in> l F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
  by (subst (1 2) mult.commute) (rule small_big_mult)

lemma small_mult: "f1 \<in> l F (g1) \<Longrightarrow> f2 \<in> l F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
  by (rule small_big_mult, assumption, rule small_imp_big)

lemmas mult = big_mult small_big_mult big_small_mult small_mult


sublocale big: landau_symbol L L' Lr
proof
  have L: "L = bigo \<or> L = bigomega"
    by (rule R_E) (auto simp: bigo_def L_def bigomega_def fun_eq_iff)
  {
    fix c :: 'b and F and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    hence "(\<lambda>x. c * f x) \<in> L F f" by (intro bigI[of "norm c"]) (simp_all add: norm_mult)
  } note A = this
  {
    fix c :: 'b and F and f :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"] 
      show "L F (\<lambda>x. c * f x) = L F f" by (intro equalityI big_subsetI) (simp_all add: field_simps)
  }
  {
    fix c :: 'b and F and f g :: "'a \<Rightarrow> 'b" assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
      have "(\<lambda>x. c * f x) \<in> L F f" "f \<in> L F (\<lambda>x. c * f x)" by (simp_all add: field_simps)
    thus "((\<lambda>x. c * f x) \<in> L F g) = (f \<in> L F g)" by (intro iffI) (erule (1) big_trans)+
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> L F (g)"
    assume B: "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
    from A guess c by (elim bigE) note c = this
    from c(2) B have "eventually (\<lambda>x. R (norm (inverse (g x))) (c * norm (inverse (f x)))) F"
      by eventually_elim (rule R_E, insert c(1), simp_all add: field_simps norm_inverse norm_divide)
    with c(1) show "(\<lambda>x. inverse (g x)) \<in> L F (\<lambda>x. inverse (f x))" by (rule bigI)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume "f \<in> o[F](g)"
    with plus_aux show "L F g \<subseteq> L F (\<lambda>x. f x + g x)" by (blast intro!: big_subsetI) 
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "eventually (\<lambda>x. f x = g x) F"
    show "L F (f) = L F (g)" unfolding L_def by (subst eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume A: "eventually (\<lambda>x. f x = g x) F"
    show "f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)" unfolding L_def mem_Collect_eq
      by (subst (1) eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume "f \<in> L F g" thus "L F f \<subseteq> L F g" by (rule big_subsetI)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> \<Theta>[F](g)"
    with A L show "L F (f) = L F (g)" unfolding bigtheta_def
      by (intro equalityI big_subsetI) (auto simp: bigomega_iff_bigo)
    fix h:: "'a \<Rightarrow> 'b"
    show "f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)" by (rule disjE[OF L]) 
      (insert A, auto simp: bigtheta_def bigomega_iff_bigo intro: landau_o.big_trans)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume "f \<in> L F g"
    thus "(\<lambda>x. h x * f x) \<in> L F (\<lambda>x. h x * g x)" by (intro big_mult) simp
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume "f \<in> L F g" "g \<in> L F h"
    thus "f \<in> L F (h)" by (rule big_trans)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G
    assume "f \<in> L F g" and "filterlim h F G"
    thus "(\<lambda>x. f (h x)) \<in> L' G (\<lambda>x. g (h x))" by (auto simp: L_def L'_def filterlim_iff)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F G :: "'a filter"
    assume "f \<in> L F g" "f \<in> L G g"
    from this [THEN bigE] guess c1 c2 . note c12 = this
    define c where "c = (if R c1 c2 then c2 else c1)"
    from c12 have c: "R c1 c" "R c2 c" "c > 0" by (auto simp: c_def dest: R_linear)
    with c12(2,4) have "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F"
                     "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) G"
      by (force elim: eventually_mono intro: R_trans[OF _ R_mult_right_mono])+
    with c show "f \<in> L (sup F G) g" by (auto simp: L_def eventually_sup)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G :: "'a filter"
    assume "(f \<in> L F g)"
    thus "((\<lambda>x. f (h x)) \<in> L' (filtercomap h F) (\<lambda>x. g (h x)))"
      unfolding L_def L'_def by auto
  }
qed (auto simp: L_def Lr_def eventually_filtermap L'_def
          intro: filter_leD exI[of _ "1::real"])

sublocale small: landau_symbol l l' lr
proof
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" and F assume "c \<noteq> 0"
    hence "(\<lambda>x. c * f x) \<in> L F f" by (intro bigI[of "norm c"]) (simp_all add: norm_mult)
  } note A = this
  {
    fix c :: 'b and f :: "'a \<Rightarrow> 'b" and F assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"] 
      show "l F (\<lambda>x. c * f x) = l F f" 
        by (intro equalityI small_subsetI) (simp_all add: field_simps)
  }
  {
    fix c :: 'b and f g :: "'a \<Rightarrow> 'b" and F assume "c \<noteq> 0"
    from `c \<noteq> 0` and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
      have "(\<lambda>x. c * f x) \<in> L F f" "f \<in> L F (\<lambda>x. c * f x)" by (simp_all add: field_simps)
    thus "((\<lambda>x. c * f x) \<in> l F g) = (f \<in> l F g)" by (intro iffI) (erule (1) big_small_trans)+
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume "f \<in> o[F](g)"
    with plus_aux show "l F g \<subseteq> l F (\<lambda>x. f x + g x)" by (blast intro!: small_subsetI) 
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> l F (g)"
    assume B: "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
    show "(\<lambda>x. inverse (g x)) \<in> l F (\<lambda>x. inverse (f x))"
    proof (rule smallI)
      fix c :: real assume c: "c > 0"
      from B smallD[OF A c] 
        show "eventually (\<lambda>x. R (norm (inverse (g x))) (c * norm (inverse (f x)))) F"
        by eventually_elim (rule R_E, simp_all add: field_simps norm_inverse norm_divide)
    qed
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "eventually (\<lambda>x. f x = g x) F"
    show "l F (f) = l F (g)" unfolding l_def by (subst eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume A: "eventually (\<lambda>x. f x = g x) F"
    show "f \<in> l F (h) \<longleftrightarrow> g \<in> l F (h)" unfolding l_def mem_Collect_eq
      by (subst (1) eventually_subst'[OF A]) (rule refl)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume "f \<in> l F g" 
    thus "l F f \<subseteq> l F g" by (intro small_subsetI small_imp_big)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> \<Theta>[F](g)"
    have L: "L = bigo \<or> L = bigomega"
      by (rule R_E) (auto simp: bigo_def L_def bigomega_def fun_eq_iff)
    with A show "l F (f) = l F (g)" unfolding bigtheta_def
      by (intro equalityI small_subsetI) (auto simp: bigomega_iff_bigo)
    have l: "l = smallo \<or> l = smallomega"
      by (rule R_E) (auto simp: smallo_def l_def smallomega_def fun_eq_iff)
    fix h:: "'a \<Rightarrow> 'b"
    show "f \<in> l F (h) \<longleftrightarrow> g \<in> l F (h)" by (rule disjE[OF l]) 
      (insert A, auto simp: bigtheta_def bigomega_iff_bigo smallomega_iff_smallo 
       intro: landau_o.big_small_trans landau_o.small_big_trans)
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume "f \<in> l F g"
    thus "(\<lambda>x. h x * f x) \<in> l F (\<lambda>x. h x * g x)" by (intro big_small_mult) simp
  }
  {
    fix f g h :: "'a \<Rightarrow> 'b" and F assume "f \<in> l F g" "g \<in> l F h"
    thus "f \<in> l F (h)" by (rule small_trans)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G
    assume "f \<in> l F g" and "filterlim h F G"
    thus "(\<lambda>x. f (h x)) \<in> l' G (\<lambda>x. g (h x))"
      by (auto simp: l_def l'_def filterlim_iff)
  }
  {
    fix f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G :: "'a filter"
    assume "(f \<in> l F g)"
    thus "((\<lambda>x. f (h x)) \<in> l' (filtercomap h F) (\<lambda>x. g (h x)))"
      unfolding l_def l'_def by auto
  }
qed (auto simp: l_def lr_def eventually_filtermap l'_def eventually_sup intro: filter_leD)


text {* These rules allow chaining of Landau symbol propositions in Isar with "also".*}

lemma big_mult_1:    "f \<in> L F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> L F (h) \<Longrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
  and big_mult_1':   "(\<lambda>_. 1) \<in> L F (g) \<Longrightarrow> f \<in> L F (h) \<Longrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
  and small_mult_1:  "f \<in> l F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> L F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1': "(\<lambda>_. 1) \<in> L F (g) \<Longrightarrow> f \<in> l F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1'':  "f \<in> L F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> l F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1''': "(\<lambda>_. 1) \<in> l F (g) \<Longrightarrow> f \<in> L F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemma big_1_mult:    "f \<in> L F (g) \<Longrightarrow> h \<in> L F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
  and big_1_mult':   "h \<in> L F (\<lambda>_. 1) \<Longrightarrow> f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
  and small_1_mult:  "f \<in> l F (g) \<Longrightarrow> h \<in> L F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult': "h \<in> L F (\<lambda>_. 1) \<Longrightarrow> f \<in> l F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult'':  "f \<in> L F (g) \<Longrightarrow> h \<in> l F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult''': "h \<in> l F (\<lambda>_. 1) \<Longrightarrow> f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemmas mult_1_trans = 
  big_mult_1 big_mult_1' small_mult_1 small_mult_1' small_mult_1'' small_mult_1'''
  big_1_mult big_1_mult' small_1_mult small_1_mult' small_1_mult'' small_1_mult'''

lemma big_equal_iff_bigtheta: "L F (f) = L F (g) \<longleftrightarrow> f \<in> \<Theta>[F](g)"
proof
  have L: "L = bigo \<or> L = bigomega"
    by (rule R_E) (auto simp: fun_eq_iff L_def bigo_def bigomega_def)
  fix f g :: "'a \<Rightarrow> 'b" assume "L F (f) = L F (g)"
  with big_refl[of f F] big_refl[of g F] have "f \<in> L F (g)" "g \<in> L F (f)" by simp_all
  thus "f \<in> \<Theta>[F](g)" using L unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)
qed (rule big.cong_bigtheta)

end


context landau_symbol
begin
  
lemma plus_absorb1:
  assumes "f \<in> o[F](g)"
  shows   "L F (\<lambda>x. f x + g x) = L F (g)"
proof (intro equalityI)
  from plus_subset1 and assms show "L F g \<subseteq> L F (\<lambda>x. f x + g x)" .
  from landau_o.small.plus_subset1[OF assms] and assms have "(\<lambda>x. -f x) \<in> o[F](\<lambda>x. f x + g x)"
    by (auto simp: landau_o.small.uminus_in_iff)
  from plus_subset1[OF this] show "L F (\<lambda>x. f x + g x) \<subseteq> L F (g)" by simp
qed

lemma plus_absorb2: "g \<in> o[F](f) \<Longrightarrow> L F (\<lambda>x. f x + g x) = L F (f)"
  using plus_absorb1[of g F f] by (simp add: add.commute)

lemma diff_absorb1: "f \<in> o[F](g) \<Longrightarrow> L F (\<lambda>x. f x - g x) = L F (g)"
  by (simp only: diff_conv_add_uminus plus_absorb1 landau_o.small.uminus uminus)

lemma diff_absorb2: "g \<in> o[F](f) \<Longrightarrow> L F (\<lambda>x. f x - g x) = L F (f)"
  by (simp only: diff_conv_add_uminus plus_absorb2 landau_o.small.uminus_in_iff)

lemmas absorb = plus_absorb1 plus_absorb2 diff_absorb1 diff_absorb2

end


lemma bigthetaI [intro]: "f \<in> O[F](g) \<Longrightarrow> f \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> \<Theta>[F](g)"
  unfolding bigtheta_def bigomega_def by blast

lemma bigthetaD1 [dest]: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> O[F](g)" 
  and bigthetaD2 [dest]: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> \<Omega>[F](g)"
  unfolding bigtheta_def bigo_def bigomega_def by blast+

lemma bigtheta_refl [simp]: "f \<in> \<Theta>[F](f)"
  unfolding bigtheta_def by simp

lemma bigtheta_sym: "f \<in> \<Theta>[F](g) \<longleftrightarrow> g \<in> \<Theta>[F](f)"
  unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)

lemmas landau_flip =
  bigomega_iff_bigo[symmetric] smallomega_iff_smallo[symmetric]
  bigomega_iff_bigo smallomega_iff_smallo bigtheta_sym


interpretation landau_theta: landau_symbol bigtheta bigtheta bigtheta
proof
  fix f g :: "'a \<Rightarrow> 'b" and F
  assume "f \<in> o[F](g)"
  hence "O[F](g) \<subseteq> O[F](\<lambda>x. f x + g x)" "\<Omega>[F](g) \<subseteq> \<Omega>[F](\<lambda>x. f x + g x)"
    by (rule landau_o.big.plus_subset1 landau_omega.big.plus_subset1)+
  thus "\<Theta>[F](g) \<subseteq> \<Theta>[F](\<lambda>x. f x + g x)" unfolding bigtheta_def by blast
next
  fix f g :: "'a \<Rightarrow> 'b" and F 
  assume "f \<in> \<Theta>[F](g)"
  thus A: "\<Theta>[F](f) = \<Theta>[F](g)" 
    apply (subst (1 2) bigtheta_def)
    apply (subst landau_o.big.cong_bigtheta landau_omega.big.cong_bigtheta, assumption)+
    apply (rule refl)
    done
  thus "\<Theta>[F](f) \<subseteq> \<Theta>[F](g)" by simp
  fix h :: "'a \<Rightarrow> 'b"
  show "f \<in> \<Theta>[F](h) \<longleftrightarrow> g \<in> \<Theta>[F](h)" by (subst (1 2) bigtheta_sym) (simp add: A)
next
  fix f g h :: "'a \<Rightarrow> 'b" and F
  assume "f \<in> \<Theta>[F](g)" "g \<in> \<Theta>[F](h)"
  thus "f \<in> \<Theta>[F](h)" unfolding bigtheta_def
    by (blast intro: landau_o.big.trans landau_omega.big.trans)
next
  fix f :: "'a \<Rightarrow> 'b" and F1 F2 :: "'a filter"
  assume "F1 \<le> F2"
  thus "\<Theta>[F2](f) \<subseteq> \<Theta>[F1](f)"
    by (auto simp: bigtheta_def intro: landau_o.big.filter_mono landau_omega.big.filter_mono)
qed (auto simp: bigtheta_def landau_o.big.norm_iff 
                landau_o.big.cmult landau_omega.big.cmult 
                landau_o.big.cmult_in_iff landau_omega.big.cmult_in_iff 
                landau_o.big.in_cong landau_omega.big.in_cong
                landau_o.big.mult landau_omega.big.mult
                landau_o.big.inverse landau_omega.big.inverse 
                landau_o.big.compose landau_omega.big.compose
                landau_o.big.bot' landau_omega.big.bot'
                landau_o.big.in_filtermap_iff landau_omega.big.in_filtermap_iff
                landau_o.big.sup landau_omega.big.sup
                landau_o.big.filtercomap landau_omega.big.filtercomap
          dest: landau_o.big.cong landau_omega.big.cong)

lemmas landau_symbols = 
  landau_o.big.landau_symbol_axioms landau_o.small.landau_symbol_axioms
  landau_omega.big.landau_symbol_axioms landau_omega.small.landau_symbol_axioms 
  landau_theta.landau_symbol_axioms

lemma bigoI [intro]:
  assumes "eventually (\<lambda>x. (norm (f x)) \<le> c * (norm (g x))) F"
  shows   "f \<in> O[F](g)"
proof (rule landau_o.bigI)
  show "max 1 c > 0" by simp
  note assms
  moreover have "\<And>x. c * (norm (g x)) \<le> max 1 c * (norm (g x))" by (simp add: mult_right_mono)
  ultimately show "eventually (\<lambda>x. (norm (f x)) \<le> max 1 c * (norm (g x))) F"
    by (auto elim!: eventually_mono dest: order.trans)
qed

lemma smallomegaD [dest]:
  assumes "f \<in> \<omega>[F](g)"
  shows   "eventually (\<lambda>x. (norm (f x)) \<ge> c * (norm (g x))) F"
proof (cases "c > 0")
  case False
  show ?thesis 
    by (intro always_eventually allI, rule order.trans[of _ 0])
       (insert False, auto intro!: mult_nonpos_nonneg)
qed (blast dest: landau_omega.smallD[OF assms, of c])

  
lemma bigthetaI':
  assumes "c1 > 0" "c2 > 0"
  assumes "eventually (\<lambda>x. c1 * (norm (g x)) \<le> (norm (f x)) \<and> (norm (f x)) \<le> c2 * (norm (g x))) F"
  shows   "f \<in> \<Theta>[F](g)"
apply (rule bigthetaI)
apply (rule landau_o.bigI[OF assms(2)]) using assms(3) apply (eventually_elim, simp)
apply (rule landau_omega.bigI[OF assms(1)]) using assms(3) apply (eventually_elim, simp)
done

lemma bigthetaI_cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> f \<in> \<Theta>[F](g)"
  by (intro bigthetaI'[of 1 1]) (auto elim!: eventually_mono)
    
lemma (in landau_symbol) ev_eq_trans1: 
  "f \<in> L F (g) \<Longrightarrow> eventually (\<lambda>x. g x = h x) F \<Longrightarrow> f \<in> L F (h)"
  by (rule bigtheta_trans1[OF _ bigthetaI_cong])

lemma (in landau_symbol) ev_eq_trans2: 
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule bigtheta_trans2[OF bigthetaI_cong])

declare landau_o.smallI landau_omega.bigI landau_omega.smallI [intro]
declare landau_o.bigE landau_omega.bigE [elim]
declare landau_o.smallD

lemma (in landau_symbol) bigtheta_trans1': 
  "f \<in> L F (g) \<Longrightarrow> h \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> L F (h)"
  by (subst cong_bigtheta[symmetric]) (simp add: bigtheta_sym)

lemma (in landau_symbol) bigtheta_trans2': 
  "g \<in> \<Theta>[F](f) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule bigtheta_trans2, subst bigtheta_sym)

lemma bigo_bigomega_trans:      "f \<in> O[F](g) \<Longrightarrow> h \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> O[F](h)"
  and bigo_smallomega_trans:    "f \<in> O[F](g) \<Longrightarrow> h \<in> \<omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and smallo_bigomega_trans:    "f \<in> o[F](g) \<Longrightarrow> h \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and smallo_smallomega_trans:  "f \<in> o[F](g) \<Longrightarrow> h \<in> \<omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and bigomega_bigo_trans:      "f \<in> \<Omega>[F](g) \<Longrightarrow> h \<in> O[F](g) \<Longrightarrow> f \<in> \<Omega>[F](h)"
  and bigomega_smallo_trans:    "f \<in> \<Omega>[F](g) \<Longrightarrow> h \<in> o[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  and smallomega_bigo_trans:    "f \<in> \<omega>[F](g) \<Longrightarrow> h \<in> O[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  and smallomega_smallo_trans:  "f \<in> \<omega>[F](g) \<Longrightarrow> h \<in> o[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  by (unfold bigomega_iff_bigo smallomega_iff_smallo)
     (erule (1) landau_o.big_trans landau_o.big_small_trans landau_o.small_big_trans 
                landau_o.big_trans landau_o.small_trans)+

lemmas landau_trans_lift [trans] =
  landau_symbols[THEN landau_symbol.lift_trans]
  landau_symbols[THEN landau_symbol.lift_trans']
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta]
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta']

lemmas landau_mult_1_trans [trans] =
  landau_o.mult_1_trans landau_omega.mult_1_trans

lemmas landau_trans [trans] = 
  landau_symbols[THEN landau_symbol.bigtheta_trans1]
  landau_symbols[THEN landau_symbol.bigtheta_trans2]
  landau_symbols[THEN landau_symbol.bigtheta_trans1']
  landau_symbols[THEN landau_symbol.bigtheta_trans2']
  landau_symbols[THEN landau_symbol.ev_eq_trans1]
  landau_symbols[THEN landau_symbol.ev_eq_trans2]

  landau_o.big_trans landau_o.small_trans landau_o.small_big_trans landau_o.big_small_trans
  landau_omega.big_trans landau_omega.small_trans 
    landau_omega.small_big_trans landau_omega.big_small_trans

  bigo_bigomega_trans bigo_smallomega_trans smallo_bigomega_trans smallo_smallomega_trans 
  bigomega_bigo_trans bigomega_smallo_trans smallomega_bigo_trans smallomega_smallo_trans


lemma bigtheta_inverse [simp]: 
  shows "(\<lambda>x. inverse (f x)) \<in> \<Theta>[F](\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<in> \<Theta>[F](g)"
proof-
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> \<Theta>[F](g)"
    then guess c1 c2 :: real unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    note c = this
    from c(3) have "inverse c2 > 0" by simp
    moreover from c(2,4)
      have "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse c2 * norm (inverse (g x))) F"
    proof eventually_elim
      fix x assume A: "(norm (f x)) \<le> c1 * (norm (g x))" "c2 * (norm (g x)) \<le> (norm (f x))"
      from A c(1,3) have "f x = 0 \<longleftrightarrow> g x = 0" by (auto simp: field_simps mult_le_0_iff)
      with A c(1,3) show "norm (inverse (f x)) \<le> inverse c2 * norm (inverse (g x))"
        by (force simp: field_simps norm_inverse norm_divide)
    qed
    ultimately have "(\<lambda>x. inverse (f x)) \<in> O[F](\<lambda>x. inverse (g x))" by (rule landau_o.bigI)
  }
  thus ?thesis unfolding bigtheta_def 
    by (force simp: bigomega_iff_bigo bigtheta_sym)
qed

lemma bigtheta_divide:
  assumes "f1 \<in> \<Theta>(f2)" "g1 \<in> \<Theta>(g2)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> \<Theta>(\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse, intro landau_theta.mult) (simp_all add: bigtheta_inverse assms)

lemma eventually_nonzero_bigtheta:
  assumes "f \<in> \<Theta>[F](g)"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) F \<longleftrightarrow> eventually (\<lambda>x. g x \<noteq> 0) F"
proof-
  {
    fix f g :: "'a \<Rightarrow> 'b" and F assume A: "f \<in> \<Theta>[F](g)" and B: "eventually (\<lambda>x. f x \<noteq> 0) F"
    from A guess c1 c2 unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    from B this(2,4) have "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim auto
  }
  with assms show ?thesis by (force simp: bigtheta_sym)
qed

lemma eventually_nonzero_bigtheta':
  "f \<in> \<Theta>[F](g) \<Longrightarrow> eventually_nonzero F f \<longleftrightarrow> eventually_nonzero F g"
  unfolding eventually_nonzero_def by (rule eventually_nonzero_bigtheta)

lemma bigtheta_mult_eq: "\<Theta>[F](\<lambda>x. f x * g x) = \<Theta>[F](f) * \<Theta>[F](g)"
proof (intro equalityI subsetI)
  fix h assume "h \<in> \<Theta>[F](f) * \<Theta>[F](g)"
  thus "h \<in> \<Theta>[F](\<lambda>x. f x * g x)"
    by (elim set_times_elim, hypsubst, unfold func_times) (erule (1) landau_theta.mult)
next
  fix h assume "h \<in> \<Theta>[F](\<lambda>x. f x * g x)"
  then guess c1 c2 :: real unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
  note c = this

  def h1 \<equiv> "\<lambda>x. if g x = 0 then if f x = 0 then if h x = 0 then h x else 1 else f x else h x / g x"
  def h2 \<equiv> "\<lambda>x. if g x = 0 then if f x = 0 then h x else h x / f x else g x" 

  have "h = h1 * h2" by (intro ext) (auto simp: h1_def h2_def field_simps)
  moreover have "h1 \<in> \<Theta>[F](f)"
  proof (rule bigthetaI')
    from c(3) show "min c2 1 > 0" by simp
    from c(1) show "max c1 1 > 0" by simp
    from c(2,4) 
      show "eventually (\<lambda>x. min c2 1 * (norm (f x)) \<le> norm (h1 x) \<and> 
                            norm (h1 x) \<le> max c1 1 * (norm (f x))) F"
      apply eventually_elim
    proof (rule conjI)
      fix x assume A: "(norm (h x)) \<le> c1 * norm (f x * g x)" 
               and B: "(norm (h x)) \<ge> c2 * norm (f x * g x)"
      have m: "min c2 1 * (norm (f x)) \<le> 1 * (norm (f x))" by (rule mult_right_mono) simp_all
      have "min c2 1 * norm (f x * g x) \<le> c2 * norm (f x * g x)" by (intro mult_right_mono) simp_all
      also note B
      finally show "norm (h1 x) \<ge> min c2 1 * (norm (f x))" using m A
        by (cases "g x = 0") (simp_all add: h1_def norm_mult norm_divide field_simps)+

      have m: "1 * (norm (f x)) \<le> max c1 1 * (norm (f x))" by (rule mult_right_mono) simp_all
      note A
      also have "c1 * norm (f x * g x) \<le> max c1 1 * norm (f x * g x)" 
        by (intro mult_right_mono) simp_all
      finally show "norm (h1 x) \<le> max c1 1 * (norm (f x))" using m A
        by (cases "g x = 0") (simp_all add: h1_def norm_mult norm_divide field_simps)+
    qed
  qed
  moreover have "h2 \<in> \<Theta>[F](g)"
  proof (rule bigthetaI')
    from c(3) show "min c2 1 > 0" by simp
    from c(1) show "max c1 1 > 0" by simp
    from c(2,4) 
      show "eventually (\<lambda>x. min c2 1 * (norm (g x)) \<le> norm (h2 x) \<and>  
                            norm (h2 x) \<le> max c1 1 * (norm (g x))) F"
      apply eventually_elim
    proof (rule conjI)
      fix x assume A: "(norm (h x)) \<le> c1 * norm (f x * g x)" 
               and B: "(norm (h x)) \<ge> c2 * norm (f x * g x)"
      have m: "min c2 1 * (norm (f x)) \<le> 1 * (norm (f x))" by (rule mult_right_mono) simp_all
      have "min c2 1 * norm (f x * g x) \<le> c2 * norm (f x * g x)" 
        by (intro mult_right_mono) simp_all
      also note B
      finally show "norm (h2 x) \<ge> min c2 1 * (norm (g x))" using m A B
        by (cases "g x = 0") (auto simp: h2_def abs_mult field_simps)+

      have m: "1 * (norm (g x)) \<le> max c1 1 * (norm (g x))" by (rule mult_right_mono) simp_all
      note A
      also have "c1 * norm (f x * g x) \<le> max c1 1 * norm (f x * g x)" 
        by (intro mult_right_mono) simp_all
      finally show "norm (h2 x) \<le> max c1 1 * (norm (g x))" using m A
        by (cases "g x = 0") (simp_all add: h2_def abs_mult field_simps)+
    qed
  qed
  ultimately show "h \<in> \<Theta>[F](f) * \<Theta>[F](g)" by blast
qed



subsection {* Landau symbols and limits *}

lemma bigoI_tendsto_norm:
  fixes f g
  assumes "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> O[F](g)"
proof (rule bigoI)
  from assms have "eventually (\<lambda>x. dist (norm (f x / g x)) c < 1) F" 
    using tendstoD by force
  thus "eventually (\<lambda>x. (norm (f x)) \<le> (norm c + 1) * (norm (g x))) F"
    unfolding dist_real_def using assms(2)
  proof eventually_elim
    case (elim x)
    have "(norm (f x)) - norm c * (norm (g x)) \<le> norm ((norm (f x)) - c * (norm (g x)))"
      unfolding norm_mult [symmetric] using norm_triangle_ineq2[of "norm (f x)" "c * norm (g x)"]
      by (simp add: norm_mult abs_mult)
    also from elim have "\<dots> = norm (norm (g x)) * norm (norm (f x / g x) - c)"
      unfolding norm_mult [symmetric] by (simp add: algebra_simps norm_divide)
    also from elim have "norm (norm (f x / g x) - c) \<le> 1" by simp
    hence "norm (norm (g x)) * norm (norm (f x / g x) - c) \<le> norm (norm (g x)) * 1" 
      by (rule mult_left_mono) simp_all
    finally show ?case by (simp add: algebra_simps)
  qed
qed

lemma bigoI_tendsto:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> O[F](g)"
  using assms by (rule bigoI_tendsto_norm[OF tendsto_norm])

lemma bigomegaI_tendsto_norm:
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Omega>[F](g)"
proof (cases "F = bot")
  case False
  show ?thesis
  proof (rule landau_omega.bigI)
    from lim  have "c \<ge> 0" by (rule tendsto_lowerbound) (insert False, simp_all)
    with c_not_0 have "c > 0" by simp
    with c_not_0 show "c/2 > 0" by simp
    from lim have ev: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> eventually (\<lambda>x. norm (norm (f x / g x) - c) < \<epsilon>) F"
      by (subst (asm) tendsto_iff) (simp add: dist_real_def)
    from ev[OF `c/2 > 0`] show "eventually (\<lambda>x. (norm (f x)) \<ge> c/2 * (norm (g x))) F"
    proof (eventually_elim)
      fix x assume B: "norm (norm (f x / g x) - c) < c / 2"
      from B have g: "g x \<noteq> 0" by auto
      from B have "-c/2 < -norm (norm (f x / g x) - c)" by simp
      also have "... \<le> norm (f x / g x) - c" by simp
      finally show "(norm (f x)) \<ge> c/2 * (norm (g x))" using g 
        by (simp add: field_simps norm_mult norm_divide)
    qed
  qed
qed simp

lemma bigomegaI_tendsto:
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Omega>[F](g)"
  by (rule bigomegaI_tendsto_norm[OF _ tendsto_norm, of c]) (insert assms, simp_all)

lemma smallomegaI_filterlim_at_top_norm:
  assumes lim: "filterlim (\<lambda>x. norm (f x / g x)) at_top F"
  shows   "f \<in> \<omega>[F](g)"
proof (rule landau_omega.smallI)
  fix c :: real assume c_pos: "c > 0"
  from lim have ev: "eventually (\<lambda>x. norm (f x / g x) \<ge> c) F"
    by (subst (asm) filterlim_at_top) simp
  thus "eventually (\<lambda>x. (norm (f x)) \<ge> c * (norm (g x))) F"
  proof eventually_elim
    fix x assume A: "norm (f x / g x) \<ge> c"
    from A c_pos have "g x \<noteq> 0" by auto
    with A show "(norm (f x)) \<ge> c * (norm (g x))" by (simp add: field_simps norm_divide)
  qed
qed
  
(* TODO: Move ? *)
lemma filterlim_at_infinity_imp_norm_at_top:
  assumes "filterlim f at_infinity F"
  shows   "filterlim (\<lambda>x. norm (f x)) at_top F"
proof -
  {
    fix r :: real 
    have "\<forall>\<^sub>F x in F. r \<le> norm (f x)" using filterlim_at_infinity[of 0 f F] assms 
      by (cases "r > 0") 
         (auto simp: not_less intro: always_eventually order.trans[OF _ norm_ge_zero])
  }
  thus ?thesis by (auto simp: filterlim_at_top)
qed
  
lemma filterlim_norm_at_top_imp_at_infinity:
  assumes "filterlim (\<lambda>x. norm (f x)) at_top F"
  shows   "filterlim f at_infinity F"
  using filterlim_at_infinity[of 0 f F] assms by (auto simp: filterlim_at_top)

lemma smallomegaI_filterlim_at_infinity:
  assumes lim: "filterlim (\<lambda>x. f x / g x) at_infinity F"
  shows   "f \<in> \<omega>[F](g)"
proof (rule smallomegaI_filterlim_at_top_norm)
  from lim show "filterlim (\<lambda>x. norm (f x / g x)) at_top F"
    by (rule filterlim_at_infinity_imp_norm_at_top)
qed

lemma smallomegaD_filterlim_at_top_norm:
  assumes "f \<in> \<omega>[F](g)"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "LIM x F. norm (f x / g x) :> at_top"
proof (subst filterlim_at_top_gt, clarify)
  fix c :: real assume c: "c > 0"
  from landau_omega.smallD[OF assms(1) this] assms(2) 
    show "eventually (\<lambda>x. norm (f x / g x) \<ge> c) F" 
    by eventually_elim (simp add: field_simps norm_divide)
qed
  
lemma smallomegaD_filterlim_at_infinity:
  assumes "f \<in> \<omega>[F](g)"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "LIM x F. f x / g x :> at_infinity"
  using assms by (intro filterlim_norm_at_top_imp_at_infinity smallomegaD_filterlim_at_top_norm)

lemma smalloI_tendsto:
  assumes lim: "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> o[F](g)"
proof (rule landau_o.smallI)
  fix c :: real assume c_pos: "c > 0"
  from c_pos and lim have ev: "eventually (\<lambda>x. norm (f x / g x) < c) F"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  with assms(2) show "eventually (\<lambda>x. (norm (f x)) \<le> c * (norm (g x))) F"
    by eventually_elim (simp add: field_simps norm_divide)
qed

lemma smalloD_tendsto:
  assumes "f \<in> o[F](g)"
  shows   "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
unfolding tendsto_iff
proof clarify
  fix e :: real assume e: "e > 0"
  hence "e/2 > 0" by simp
  from landau_o.smallD[OF assms this] show "eventually (\<lambda>x. dist (f x / g x) 0 < e) F"
  proof eventually_elim
    fix x assume "(norm (f x)) \<le> e/2 * (norm (g x))"
    with e have "dist (f x / g x) 0 \<le> e/2"
      by (cases "g x = 0") (simp_all add: dist_real_def norm_divide field_simps)
    also from e have "... < e" by simp
    finally show "dist (f x / g x) 0 < e" by simp
  qed
qed

lemma bigthetaI_tendsto_norm:
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Theta>[F](g)"
proof (rule bigthetaI)
  from c_not_0 have "\<bar>c\<bar> > 0" by simp
  with lim have "eventually (\<lambda>x. norm (norm (f x / g x) - c) < \<bar>c\<bar>) F"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  hence g: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim (auto simp add: field_simps)

  from lim g show "f \<in> O[F](g)" by (rule bigoI_tendsto_norm)
  from c_not_0 and lim show "f \<in> \<Omega>[F](g)" by (rule bigomegaI_tendsto_norm)
qed

lemma bigthetaI_tendsto:
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Theta>[F](g)"
  using assms by (intro bigthetaI_tendsto_norm[OF _ tendsto_norm, of "c"]) simp_all

lemma tendsto_add_smallo:
  assumes "(f1 \<longlongrightarrow> a) F"
  assumes "f2 \<in> o[F](f1)"
  shows   "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
proof (subst filterlim_cong[OF refl refl])
  from landau_o.smallD[OF assms(2) zero_less_one] 
    have "eventually (\<lambda>x. norm (f2 x) \<le> norm (f1 x)) F" by simp
  thus "eventually (\<lambda>x. f1 x + f2 x = f1 x * (1 + f2 x / f1 x)) F"
    by eventually_elim (auto simp: field_simps)
next
  from assms(1) show "((\<lambda>x. f1 x * (1 + f2 x / f1 x)) \<longlongrightarrow> a) F"
    by (force intro: tendsto_eq_intros smalloD_tendsto[OF assms(2)])
qed

lemma tendsto_diff_smallo:
  shows "(f1 \<longlongrightarrow> a) F \<Longrightarrow> f2 \<in> o[F](f1) \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) F"
  using tendsto_add_smallo[of f1 a F "\<lambda>x. -f2 x"] by simp

lemma tendsto_add_smallo_iff:
  assumes "f2 \<in> o[F](f1)"
  shows   "(f1 \<longlongrightarrow> a) F \<longleftrightarrow> ((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
proof
  assume "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
  hence "((\<lambda>x. f1 x + f2 x - f2 x) \<longlongrightarrow> a) F"
    by (rule tendsto_diff_smallo) (simp add: landau_o.small.plus_absorb2 assms)
  thus "(f1 \<longlongrightarrow> a) F" by simp
qed (rule tendsto_add_smallo[OF _ assms])

lemma tendsto_diff_smallo_iff:
  shows "f2 \<in> o[F](f1) \<Longrightarrow> (f1 \<longlongrightarrow> a) F \<longleftrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) F"
  using tendsto_add_smallo_iff[of "\<lambda>x. -f2 x" F f1 a] by simp

lemma tendsto_divide_smallo:
  assumes "((\<lambda>x. f1 x / g1 x) \<longlongrightarrow> a) F"
  assumes "f2 \<in> o[F](f1)" "g2 \<in> o[F](g1)"
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  shows   "((\<lambda>x. (f1 x + f2 x) / (g1 x + g2 x)) \<longlongrightarrow> a) F" (is "(?f \<longlongrightarrow> _) _")
proof (subst tendsto_cong)
  let ?f' = "\<lambda>x. (f1 x / g1 x) * (1 + f2 x / f1 x) / (1 + g2 x / g1 x)"

  have "(?f' \<longlongrightarrow> a * (1 + 0) / (1 + 0)) F"
  by (rule tendsto_mult tendsto_divide tendsto_add assms tendsto_const 
        smalloD_tendsto[OF assms(2)] smalloD_tendsto[OF assms(3)])+ simp_all
  thus "(?f' \<longlongrightarrow> a) F" by simp

  have "(1/2::real) > 0" by simp
  from landau_o.smallD[OF assms(2) this] landau_o.smallD[OF assms(3) this]
    have "eventually (\<lambda>x. norm (f2 x) \<le> norm (f1 x)/2) F"
         "eventually (\<lambda>x. norm (g2 x) \<le> norm (g1 x)/2) F" by simp_all
  with assms(4) show "eventually (\<lambda>x. ?f x = ?f' x) F"
  proof eventually_elim
    fix x assume A: "norm (f2 x) \<le> norm (f1 x)/2" and 
                 B: "norm (g2 x) \<le> norm (g1 x)/2" and C: "g1 x \<noteq> 0"
    show "?f x = ?f' x"
    proof (cases "f1 x = 0")
      assume D: "f1 x \<noteq> 0"
      from D have "f1 x + f2 x = f1 x * (1 + f2 x/f1 x)" by (simp add: field_simps)
      moreover from C have "g1 x + g2 x = g1 x * (1 + g2 x/g1 x)" by (simp add: field_simps)
      ultimately have "?f x = (f1 x * (1 + f2 x/f1 x)) / (g1 x * (1 + g2 x/g1 x))" by (simp only:)
      also have "... = ?f' x" by simp
      finally show ?thesis .
    qed (insert A, simp)
  qed
qed


lemma bigo_powr:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> O[F](g)" "p \<ge> 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)"
proof-
  from assms(1) guess c by (elim landau_o.bigE landau_omega.bigE IntE)
  note c = this
  from c(2) assms(2) have "eventually (\<lambda>x. (norm (f x)) powr p \<le> (c * (norm (g x))) powr p) F"
    by (auto elim!: eventually_mono intro!: powr_mono2_ex)
  thus "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)" using c(1)
    by (intro bigoI[of _ "c powr p"]) (simp_all add: powr_mult)
qed

lemma smallo_powr:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> o[F](g)" "p > 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o[F](\<lambda>x. \<bar>g x\<bar> powr p)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "c > 0"
  hence "c powr (1/p) > 0" by simp
  from landau_o.smallD[OF assms(1) this] 
  show "eventually (\<lambda>x. norm (\<bar>f x\<bar> powr p) \<le> c * norm (\<bar>g x\<bar> powr p)) F"
  proof eventually_elim
    fix x assume "(norm (f x)) \<le> c powr (1 / p) * (norm (g x))"
    with assms(2) have "(norm (f x)) powr p \<le> (c powr (1 / p) * (norm (g x))) powr p"
      by (intro powr_mono2_ex) simp_all
    also from assms(2) c have "... = c * (norm (g x)) powr p"
      by (simp add: field_simps powr_mult powr_powr)
    finally show "norm (\<bar>f x\<bar> powr p) \<le> c * norm (\<bar>g x\<bar> powr p)" by simp
  qed
qed

lemma smallo_powr_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> o[F](g)" "p > 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr p) \<in> o[F](\<lambda>x. g x powr p)"
proof -
  from assms(3) have "(\<lambda>x. f x powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr p)" 
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also have "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o[F](\<lambda>x. \<bar>g x\<bar> powr p)" by (intro smallo_powr) fact+
  also from assms(4) have "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. g x powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show ?thesis .
qed

lemma bigtheta_powr:
  fixes f :: "'a \<Rightarrow> real"
  shows "f \<in> \<Theta>[F](g) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>g x\<bar> powr p)"
apply (cases "p < 0")
apply (subst bigtheta_inverse[symmetric], subst (1 2) powr_minus[symmetric])
unfolding bigtheta_def apply (auto simp: bigomega_iff_bigo intro!: bigo_powr)
done

lemma bigo_powr_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> O[F](g)" "p \<ge> 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr p) \<in> O[F](\<lambda>x. g x powr p)"
proof -
  from assms(3) have "(\<lambda>x. f x powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr p)" 
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also have "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)" by (intro bigo_powr) fact+
  also from assms(4) have "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. g x powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show ?thesis .
qed

lemma zero_in_smallo [simp]: "(\<lambda>_. 0) \<in> o[F](f)"
  by (intro landau_o.smallI) simp_all

lemma zero_in_bigo [simp]: "(\<lambda>_. 0) \<in> O[F](f)"
  by (intro landau_o.bigI[of 1]) simp_all

lemma in_bigomega_zero [simp]: "f \<in> \<Omega>[F](\<lambda>x. 0)"
  by (rule landau_omega.bigI[of 1]) simp_all

lemma in_smallomega_zero [simp]: "f \<in> \<omega>[F](\<lambda>x. 0)"
  by (simp add: smallomega_iff_smallo)


lemma in_smallo_zero_iff [simp]: "f \<in> o[F](\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof
  assume "f \<in> o[F](\<lambda>_. 0)"
  from landau_o.smallD[OF this, of 1] show "eventually (\<lambda>x. f x = 0) F" by simp
next
  assume "eventually (\<lambda>x. f x = 0) F"
  hence "\<forall>c>0. eventually (\<lambda>x. (norm (f x)) \<le> c * \<bar>0\<bar>) F" by simp
  thus "f \<in> o[F](\<lambda>_. 0)" unfolding smallo_def by simp
qed

lemma in_bigo_zero_iff [simp]: "f \<in> O[F](\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof
  assume "f \<in> O[F](\<lambda>_. 0)"
  thus "eventually (\<lambda>x. f x = 0) F" by (elim landau_o.bigE) simp
next
  assume "eventually (\<lambda>x. f x = 0) F"
  hence "eventually (\<lambda>x. (norm (f x)) \<le> 1 * \<bar>0\<bar>) F" by simp
  thus "f \<in> O[F](\<lambda>_. 0)" by (intro landau_o.bigI[of 1]) simp_all
qed

lemma zero_in_smallomega_iff [simp]: "(\<lambda>_. 0) \<in> \<omega>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (simp add: smallomega_iff_smallo)

lemma zero_in_bigomega_iff [simp]: "(\<lambda>_. 0) \<in> \<Omega>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (simp add: bigomega_iff_bigo)

lemma zero_in_bigtheta_iff [simp]: "(\<lambda>_. 0) \<in> \<Theta>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  unfolding bigtheta_def by simp

lemma in_bigtheta_zero_iff [simp]: "f \<in> \<Theta>[F](\<lambda>x. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  unfolding bigtheta_def by simp


lemma cmult_in_bigo_iff    [simp]:  "(\<lambda>x. c * f x) \<in> O[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> O[F](g)"
  and cmult_in_bigo_iff'   [simp]:  "(\<lambda>x. f x * c) \<in> O[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> O[F](g)"
  and cmult_in_smallo_iff  [simp]:  "(\<lambda>x. c * f x) \<in> o[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> o[F](g)"
  and cmult_in_smallo_iff' [simp]: "(\<lambda>x. f x * c) \<in> o[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> o[F](g)"
  by (cases "c = 0", simp, simp)+

lemma bigo_const [simp]: "(\<lambda>_. c) \<in> O[F](\<lambda>_. 1)" by (rule bigoI[of _ "norm c"]) simp

lemma bigo_const_iff [simp]: "(\<lambda>_. c1) \<in> O[F](\<lambda>_. c2) \<longleftrightarrow> F = bot \<or> c1 = 0 \<or> c2 \<noteq> 0"
  by (cases "c1 = 0"; cases "c2 = 0")
     (auto simp: bigo_def eventually_False intro: exI[of _ 1] exI[of _ "norm c1 / norm c2"])

lemma bigomega_const_iff [simp]: "(\<lambda>_. c1) \<in> \<Omega>[F](\<lambda>_. c2) \<longleftrightarrow> F = bot \<or> c1 \<noteq> 0 \<or> c2 = 0"
  by (cases "c1 = 0"; cases "c2 = 0")
     (auto simp: bigomega_def eventually_False mult_le_0_iff 
           intro: exI[of _ 1] exI[of _ "norm c1 / norm c2"])


lemma smallo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> o(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> o(\<lambda>x. g (real x))"
  by (force intro!: eventually_nat_real landau_o.smallI dest!: landau_o.smallD)

lemma bigo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> O(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> O(\<lambda>x. g (real x))"
  by (elim landau_o.bigE, erule landau_o.bigI, erule eventually_nat_real)

lemma smallomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<omega>(\<lambda>x. g (real x))"
  by (force intro!: eventually_nat_real landau_omega.smallI dest!: landau_omega.smallD)

lemma bigomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Omega>(\<lambda>x. g (real x))"
  by (elim landau_omega.bigE, erule landau_omega.bigI, erule eventually_nat_real)

lemma bigtheta_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Theta>(\<lambda>x. g (real x))"
  unfolding bigtheta_def using bigo_real_nat_transfer bigomega_real_nat_transfer by blast

lemmas landau_real_nat_transfer [intro] = 
  bigo_real_nat_transfer smallo_real_nat_transfer bigomega_real_nat_transfer 
  smallomega_real_nat_transfer bigtheta_real_nat_transfer


lemma landau_symbol_if_at_top_eq [simp]:
  assumes "landau_symbol L L' Lr"
  shows   "L at_top (\<lambda>x::'a::linordered_semidom. if x = a then f x else g x) = L at_top (g)"
apply (rule landau_symbol.cong[OF assms])
using less_add_one[of a] apply (auto intro: eventually_mono  eventually_ge_at_top[of "a + 1"])
done

lemmas landau_symbols_if_at_top_eq [simp] = landau_symbols[THEN landau_symbol_if_at_top_eq]



lemma sum_in_smallo:
  assumes "f \<in> o[F](h)" "g \<in> o[F](h)"
  shows   "(\<lambda>x. f x + g x) \<in> o[F](h)" "(\<lambda>x. f x - g x) \<in> o[F](h)"
proof-
  {
    fix f g assume fg: "f \<in> o[F](h)" "g \<in> o[F](h)"
    have "(\<lambda>x. f x + g x) \<in> o[F](h)"
    proof (rule landau_o.smallI)
      fix c :: real assume "c > 0"
      hence "c/2 > 0" by simp
      from fg[THEN landau_o.smallD[OF _ this]]
      show "eventually (\<lambda>x. norm (f x + g x) \<le> c * (norm (h x))) F"
        by eventually_elim (auto intro: order.trans[OF norm_triangle_ineq])
    qed
  }
  from this[of f g] this[of f "\<lambda>x. -g x"] assms
    show "(\<lambda>x. f x + g x) \<in> o[F](h)" "(\<lambda>x. f x - g x) \<in> o[F](h)" by simp_all
qed

lemma sum_in_bigo:
  assumes "f \<in> O[F](h)" "g \<in> O[F](h)"
  shows   "(\<lambda>x. f x + g x) \<in> O[F](h)" "(\<lambda>x. f x - g x) \<in> O[F](h)"
proof-
  {
    fix f g assume fg: "f \<in> O[F](h)" "g \<in> O[F](h)"
    from fg(1) guess c1 by (elim landau_o.bigE) note c1 = this
    from fg(2) guess c2 by (elim landau_o.bigE) note c2 = this
    from c1(2) c2(2) have "eventually (\<lambda>x. norm (f x + g x) \<le> (c1 + c2) * (norm (h x))) F"
      by eventually_elim (auto simp: algebra_simps intro: order.trans[OF norm_triangle_ineq])
    hence "(\<lambda>x. f x + g x) \<in> O[F](h)" by (rule bigoI)
  }
  from this[of f g] this[of f "\<lambda>x. -g x"] assms
    show "(\<lambda>x. f x + g x) \<in> O[F](h)" "(\<lambda>x. f x - g x) \<in> O[F](h)" by simp_all
qed


lemma tendsto_ln_over_powr: 
  assumes "(a::real) > 0"
  shows   "((\<lambda>x. ln x / x powr a) \<longlongrightarrow> 0) at_top"
proof (rule lhospital_at_top_at_top)
  from assms show "LIM x at_top. x powr a :> at_top" by (rule powr_at_top)
  show "eventually (\<lambda>x. a * x powr (a - 1) \<noteq> 0) at_top"
    using eventually_gt_at_top[of "0::real"] by eventually_elim (insert assms, simp)
  show "eventually (\<lambda>x::real. (ln has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_ln by (elim eventually_mono) simp
  show "eventually (\<lambda>x. ((\<lambda>x. x powr a) has_real_derivative a * x powr (a - 1)) (at x)) at_top"
    using eventually_gt_at_top[of "0::real"] DERIV_powr by (elim eventually_mono) simp
  have "eventually (\<lambda>x. inverse a * x powr -a = inverse x / (a*x powr (a-1))) at_top"
    using eventually_gt_at_top[of "0::real"] 
    by (elim eventually_mono) (simp add: field_simps powr_diff powr_minus)
  moreover from assms have "((\<lambda>x. inverse a * x powr -a) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_mult_right_zero tendsto_neg_powr filterlim_ident) simp_all
  ultimately show "((\<lambda>x. inverse x / (a * x powr (a - 1))) \<longlongrightarrow> 0) at_top"
    by (subst (asm) tendsto_cong) simp_all
qed

lemma tendsto_ln_powr_over_powr: 
  assumes "(a::real) > 0" "b > 0"
  shows   "((\<lambda>x. ln x powr a / x powr b) \<longlongrightarrow> 0) at_top"
proof-
  have "eventually (\<lambda>x. ln x powr a / x powr b = (ln x / x powr (b/a)) powr a) at_top"
    using assms eventually_gt_at_top[of "1::real"]
    by (elim eventually_mono) (simp add: powr_divide powr_powr)
  moreover have "eventually (\<lambda>x. 0 < ln x / x powr (b / a)) at_top"
    using eventually_gt_at_top[of "1::real"] by (elim eventually_mono) simp
  with assms have "((\<lambda>x. (ln x / x powr (b/a)) powr a) \<longlongrightarrow> 0) at_top"
    by (intro tendsto_zero_powrI tendsto_ln_over_powr) (simp_all add: eventually_mono)
  ultimately show ?thesis by (subst tendsto_cong) simp_all
qed

lemma tendsto_ln_powr_over_powr': 
  assumes "b > 0"
  shows   "((\<lambda>x::real. ln x powr a / x powr b) \<longlongrightarrow> 0) at_top"
proof (cases "a \<le> 0")
  assume a: "a \<le> 0"
  show ?thesis
  proof (rule tendsto_sandwich[of "\<lambda>_::real. 0"])
    have "eventually (\<lambda>x. ln x powr a \<le> 1) at_top" unfolding eventually_at_top_linorder
    proof (intro allI exI impI)
      fix x :: real assume "x \<ge> exp 1"
      from ln_mono[OF _ less_le_trans[OF _ this] this] have "ln x \<ge> 1" by simp
      hence "ln x powr a \<le> ln (exp 1) powr a" using a by (intro powr_mono2') simp_all
      thus "ln x powr a \<le> 1" by simp
    qed
    thus "eventually (\<lambda>x. ln x powr a / x powr b \<le> x powr -b) at_top"
      by eventually_elim (insert a, simp add: field_simps powr_minus divide_right_mono)
  qed (auto intro!: filterlim_ident tendsto_neg_powr assms)
qed (intro tendsto_ln_powr_over_powr, simp_all add: assms)

lemma tendsto_ln_over_ln:
  assumes "(a::real) > 0" "c > 0"
  shows   "((\<lambda>x. ln (a*x) / ln (c*x)) \<longlongrightarrow> 1) at_top"
proof (rule lhospital_at_top_at_top)
  show "LIM x at_top. ln (c*x) :> at_top"
    by (intro filterlim_compose[OF ln_at_top] filterlim_tendsto_pos_mult_at_top[OF tendsto_const] 
              filterlim_ident assms(2))
  show "eventually (\<lambda>x. ((\<lambda>x. ln (a*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse a"] assms
    by (auto elim!: eventually_mono intro!: derivative_eq_intros simp: field_simps)
  show "eventually (\<lambda>x. ((\<lambda>x. ln (c*x)) has_real_derivative (inverse x)) (at x)) at_top"
    using eventually_gt_at_top[of "inverse c"] assms
    by (auto elim!: eventually_mono intro!: derivative_eq_intros simp: field_simps)
  show "((\<lambda>x::real. inverse x / inverse x) \<longlongrightarrow> 1) at_top"
    by (subst tendsto_cong[of _ "\<lambda>_. 1"]) (simp_all add: eventually_not_equal)
qed (simp_all add: eventually_not_equal)

lemma tendsto_ln_powr_over_ln_powr:
  assumes "(a::real) > 0" "c > 0"
  shows   "((\<lambda>x. ln (a*x) powr d / ln (c*x) powr d) \<longlongrightarrow> 1) at_top"
proof-
  have "eventually (\<lambda>x. ln (a*x) powr d / ln (c*x) powr d = (ln (a*x) / ln (c*x)) powr d) at_top"
    using assms eventually_gt_at_top[of "max (inverse a) (inverse c)"]
    by (auto elim!: eventually_mono simp: powr_divide field_simps)
  moreover have "((\<lambda>x. (ln (a*x) / ln (c*x)) powr d) \<longlongrightarrow> 1) at_top" using assms
    by (intro tendsto_eq_rhs[OF tendsto_powr[OF tendsto_ln_over_ln tendsto_const]]) simp_all
  ultimately show ?thesis by (subst tendsto_cong)
qed

lemma tendsto_ln_powr_over_ln_powr': 
  "c > 0 \<Longrightarrow> ((\<lambda>x::real. ln x powr d / ln (c*x) powr d) \<longlongrightarrow> 1) at_top"
  using tendsto_ln_powr_over_ln_powr[of 1 c d] by simp

lemma tendsto_ln_powr_over_ln_powr'': 
  "a > 0 \<Longrightarrow> ((\<lambda>x::real. ln (a*x) powr d / ln x powr d) \<longlongrightarrow> 1) at_top"
  using tendsto_ln_powr_over_ln_powr[of _ 1] by simp

lemma bigtheta_const_ln_powr [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x) powr d) \<in> \<Theta>(\<lambda>x. ln x powr d)"
  by (intro bigthetaI_tendsto[of 1] tendsto_ln_powr_over_ln_powr'') simp

lemma bigtheta_const_ln_pow [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x) ^ d) \<in> \<Theta>(\<lambda>x. ln x ^ d)"
proof-
  assume A: "a > 0"
  hence "(\<lambda>x::real. ln (a*x) ^ d) \<in> \<Theta>(\<lambda>x. ln (a*x) powr real d)"
    by (subst bigtheta_sym, intro bigthetaI_cong powr_realpow_eventually 
         filterlim_compose[OF ln_at_top] 
         filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ filterlim_ident])
  also from A have "(\<lambda>x. ln (a*x) powr real d) \<in> \<Theta>(\<lambda>x. ln x powr real d)" by simp
  also have "(\<lambda>x. ln x powr real d) \<in> \<Theta>(\<lambda>x. ln x ^ d)"
    by (intro bigthetaI_cong powr_realpow_eventually filterlim_compose[OF ln_at_top] filterlim_ident)
  finally show ?thesis .
qed

lemma bigtheta_const_ln [simp]: "a > 0 \<Longrightarrow> (\<lambda>x::real. ln (a*x)) \<in> \<Theta>(\<lambda>x. ln x)"
  using tendsto_ln_over_ln[of a 1]  by (intro bigthetaI_tendsto[of 1]) simp_all



context landau_symbol
begin

lemma mult_cancel_left:
  assumes "f1 \<in> \<Theta>[F](g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  notes   [trans] = bigtheta_trans1 bigtheta_trans2
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f2 \<in> L F (g2)"
proof
  assume A: "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
  from assms have nz: "eventually (\<lambda>x. f1 x \<noteq> 0) F" by (simp add: eventually_nonzero_bigtheta)
  hence "f2 \<in> \<Theta>[F](\<lambda>x. f1 x * f2 x / f1 x)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also from A assms nz have "(\<lambda>x. f1 x * f2 x / f1 x) \<in> L F (\<lambda>x. g1 x * g2 x / f1 x)" 
    by (intro divide_right) simp_all
  also from assms nz have "(\<lambda>x. g1 x * g2 x / f1 x) \<in> \<Theta>[F](\<lambda>x. g1 x * g2 x / g1 x)"
    by (intro landau_theta.mult landau_theta.divide) (simp_all add: bigtheta_sym)
  also from assms have "(\<lambda>x. g1 x * g2 x / g1 x) \<in> \<Theta>[F](g2)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show "f2 \<in> L F (g2)" .
next
  assume "f2 \<in> L F (g2)"
  hence "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. f1 x * g2 x)" by (rule mult_left)
  also have "(\<lambda>x. f1 x * g2 x) \<in> \<Theta>[F](\<lambda>x. g1 x * g2 x)"
    by (intro landau_theta.mult_right assms)
  finally show "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)" .
qed

lemma mult_cancel_right:
  assumes "f2 \<in> \<Theta>[F](g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f1 \<in> L F (g1)"
  by (subst (1 2) mult.commute) (rule mult_cancel_left[OF assms])

lemma divide_cancel_right:
  assumes "f2 \<in> \<Theta>[F](g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L F (\<lambda>x. g1 x / g2 x) \<longleftrightarrow> f1 \<in> L F (g1)"
  by (subst (1 2) divide_inverse, intro mult_cancel_right bigtheta_inverse) (simp_all add: assms)

lemma divide_cancel_left:
  assumes "f1 \<in> \<Theta>[F](g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L F (\<lambda>x. g1 x / g2 x) \<longleftrightarrow> 
             (\<lambda>x. inverse (f2 x)) \<in> L F (\<lambda>x. inverse (g2 x))"
  by (simp only: divide_inverse mult_cancel_left[OF assms])

end


lemma powr_smallo_iff:
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> o[F](\<lambda>x. g x powr q) \<longleftrightarrow> p < q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) F" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> o[F](\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)"
    from landau_o.big_small_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) F" by simp
    with A have "eventually (\<lambda>_::'a. False) F" by eventually_elim simp
    thus False by (simp add: eventually_False assms)
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_diff [symmetric] )
    with `p < q` show ?thesis by auto
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B `p = q` show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr landau_o.small_imp_big simp: powr_diff [symmetric] )
    with B `p > q` show ?thesis by auto
  qed
qed

lemma powr_bigo_iff:
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> O[F](\<lambda>x. g x powr q) \<longleftrightarrow> p \<le> q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) F" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> O[F](\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> O[F](\<lambda>x. g x powr q)"
    from landau_o.small_big_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) F" by simp
    with A have "eventually (\<lambda>_::'a. False) F" by eventually_elim simp
    thus False by (simp add: eventually_False assms)
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_diff [symmetric] )
    with `p < q` show ?thesis by (auto intro: landau_o.small_imp_big)
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B `p = q` show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp: powr_diff [symmetric] )
    with B `p > q` show ?thesis by (auto intro: landau_o.small_imp_big)
  qed
qed

lemma powr_bigtheta_iff: 
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> \<Theta>[F](\<lambda>x. g x powr q) \<longleftrightarrow> p = q"
  using assms unfolding bigtheta_def by (auto simp: bigomega_iff_bigo powr_bigo_iff)



subsection {* Rewriting Landau symbols *}

text {* 
  Since the simplifier does not currently rewriting with relations other than equality,
  but we want to rewrite terms like @{term "\<Theta>(\<lambda>x. log 2 x * x)"} to @{term "\<Theta>(\<lambda>x. ln x * x)"}, 
  we need to bring the term into something that contains @{term "\<Theta>(\<lambda>x. log 2 x)"} and 
  @{term "\<Theta>(\<lambda>x. x)"}, which can then be rewritten individually.
  For this, we introduce the following constants and rewrite rules. The rules are mainly used 
  by the simprocs, but may be useful for manual reasoning occasionally.
*}

definition "set_mult A B = {\<lambda>x. f x * g x |f g. f \<in> A \<and> g \<in> B}"
definition "set_inverse A = {\<lambda>x. inverse (f x) |f. f \<in> A}"
definition "set_divide A B = {\<lambda>x. f x / g x |f g. f \<in> A \<and> g \<in> B}"
definition "set_pow A n = {\<lambda>x. f x ^ n |f. f \<in> A}"
definition "set_powr A y = {\<lambda>x. f x powr y |f. f \<in> A}"

lemma bigtheta_mult_eq_set_mult:
  shows "\<Theta>[F](\<lambda>x. f x * g x) = set_mult (\<Theta>[F](f)) (\<Theta>[F](g))"
  unfolding bigtheta_mult_eq set_mult_def set_times_def func_times by blast

lemma bigtheta_inverse_eq_set_inverse:
  shows "\<Theta>[F](\<lambda>x. inverse (f x)) = set_inverse (\<Theta>[F](f))"
proof (intro equalityI subsetI)
  fix g :: "'a \<Rightarrow> 'b" assume "g \<in> \<Theta>[F](\<lambda>x. inverse (f x))"
  hence "(\<lambda>x. inverse (g x)) \<in> \<Theta>[F](\<lambda>x. inverse (inverse (f x)))" by (subst bigtheta_inverse)
  also have "(\<lambda>x. inverse (inverse (f x))) = f" by (rule ext) simp
  finally show "g \<in> set_inverse (\<Theta>[F](f))" unfolding set_inverse_def by force
next
  fix g :: "'a \<Rightarrow> 'b" assume "g \<in> set_inverse (\<Theta>[F](f))"
  then obtain g' where "g = (\<lambda>x. inverse (g' x))" "g' \<in> \<Theta>[F](f)" unfolding set_inverse_def by blast
  hence "(\<lambda>x. inverse (g' x)) \<in> \<Theta>[F](\<lambda>x. inverse (f x))" by (subst bigtheta_inverse)
  also from `g = (\<lambda>x. inverse (g' x))` have "(\<lambda>x. inverse (g' x)) = g" by (intro ext) simp
  finally show "g \<in> \<Theta>[F](\<lambda>x. inverse (f x))" .
qed

lemma set_divide_inverse: 
  "set_divide (A :: (_ \<Rightarrow> (_ :: division_ring)) set) B = set_mult A (set_inverse B)"
proof (intro equalityI subsetI)
  fix f assume "f \<in> set_divide A B"
  then obtain g h where "f = (\<lambda>x. g x / h x)" "g \<in> A" "h \<in> B" unfolding set_divide_def by blast
  hence "f = g * (\<lambda>x. inverse (h x))" "(\<lambda>x. inverse (h x)) \<in> set_inverse B"
    unfolding set_inverse_def by (auto simp: divide_inverse)
  with `g \<in> A` show "f \<in> set_mult A (set_inverse B)" unfolding set_mult_def by force
next
  fix f assume "f \<in> set_mult A (set_inverse B)"
  then obtain g h where "f = g * (\<lambda>x. inverse (h x))" "g \<in> A" "h \<in> B"
    unfolding set_times_def set_inverse_def set_mult_def by force
  hence "f = (\<lambda>x. g x / h x)" by (intro ext) (simp add: divide_inverse)
  with `g \<in> A` `h \<in> B` show "f \<in> set_divide A B" unfolding set_divide_def by blast
qed

lemma bigtheta_divide_eq_set_divide:
  shows "\<Theta>[F](\<lambda>x. f x / g x) = set_divide (\<Theta>[F](f)) (\<Theta>[F](g))"
  by (simp only: set_divide_inverse divide_inverse bigtheta_mult_eq_set_mult 
                 bigtheta_inverse_eq_set_inverse)

primrec bigtheta_pow where
  "bigtheta_pow F A 0 = \<Theta>[F](\<lambda>_. 1)"
| "bigtheta_pow F A (Suc n) = set_mult A (bigtheta_pow F A n)"

lemma bigtheta_pow_eq_set_pow: "\<Theta>[F](\<lambda>x. f x ^ n) = bigtheta_pow F (\<Theta>[F](f)) n"
  by (induction n) (simp_all add: bigtheta_mult_eq_set_mult)

definition bigtheta_powr where
  "bigtheta_powr F A y = (if y = 0 then {f. \<exists>g\<in>A. eventually_nonneg F g \<and> f \<in> \<Theta>[F](\<lambda>x. g x powr y)} 
     else {f. \<exists>g\<in>A. eventually_nonneg F g \<and> (\<forall>x. (norm (f x)) = g x powr y)})"

lemma bigtheta_powr_eq_set_powr: 
  assumes "eventually_nonneg F f"
  shows   "\<Theta>[F](\<lambda>x. f x powr (y::real)) = bigtheta_powr F (\<Theta>[F](f)) y"
proof (cases "y = 0")
  assume [simp]: "y = 0"
  show ?thesis
  proof (intro equalityI subsetI)
    fix h assume "h \<in> bigtheta_powr F \<Theta>[F](f) y"
    then obtain g where g: "g \<in> \<Theta>[F](f)" "eventually_nonneg F g" "h \<in> \<Theta>[F](\<lambda>x. g x powr 0)"
      unfolding bigtheta_powr_def by force
    note this(3)
    also have "(\<lambda>x. g x powr 0) \<in> \<Theta>[F](\<lambda>x. \<bar>g x\<bar> powr 0)" 
      using assms unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    also from g(1) have "(\<lambda>x. \<bar>g x\<bar> powr 0) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr 0)" 
      by (rule bigtheta_powr)
    also from g(2) have "(\<lambda>x. f x powr 0) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr 0)" 
      unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally show "h \<in> \<Theta>[F](\<lambda>x. f x powr y)" by simp
  next
    fix h assume "h \<in> \<Theta>[F](\<lambda>x. f x powr y)"
    with assms have "\<exists>g\<in>\<Theta>[F](f). eventually_nonneg F g \<and> h \<in> \<Theta>[F](\<lambda>x. g x powr 0)"
      by (intro bexI[of _ f] conjI) simp_all
    thus "h \<in> bigtheta_powr F \<Theta>[F](f) y" unfolding bigtheta_powr_def by simp
  qed
next
  assume y: "y \<noteq> 0"
  show ?thesis
  proof (intro equalityI subsetI)
    fix h assume h: "h \<in> \<Theta>[F](\<lambda>x. f x powr y)"
    let ?h' = "\<lambda>x. \<bar>h x\<bar> powr inverse y"
    from bigtheta_powr[OF h, of "inverse y"] y
      have "?h' \<in> \<Theta>[F](\<lambda>x. f x powr 1)" by (simp add: powr_powr)
    also have "(\<lambda>x. f x powr 1) \<in> \<Theta>[F](f)" using assms unfolding eventually_nonneg_def 
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally have "?h' \<in> \<Theta>[F](f)" .
    with y have "\<exists>g\<in>\<Theta>[F](f). eventually_nonneg F g \<and> (\<forall>x. (norm (h x)) = g x powr y)"
      by (intro bexI[of _ ?h']) (simp_all add: powr_powr eventually_nonneg_def)
    thus "h \<in> bigtheta_powr F \<Theta>[F](f) y" using y unfolding bigtheta_powr_def by simp
  next
    fix h assume "h \<in> bigtheta_powr F (\<Theta>[F](f)) y"
    with y obtain g where A: "g \<in> \<Theta>[F](f)" "\<And>x. \<bar>h x\<bar> = g x powr y" "eventually_nonneg F g"
      unfolding bigtheta_powr_def by force
    from this(3) have "(\<lambda>x. g x powr y) \<in> \<Theta>[F](\<lambda>x. \<bar>g x\<bar> powr y)" unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    also from A(1) have "(\<lambda>x. \<bar>g x\<bar> powr y) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr y)" by (rule bigtheta_powr)
    also have "(\<lambda>x. \<bar>f x\<bar> powr y) \<in> \<Theta>[F](\<lambda>x. f x powr y)" using assms unfolding eventually_nonneg_def
      by (intro bigthetaI_cong) (auto elim!: eventually_mono)
    finally have "(\<lambda>x. \<bar>h x\<bar>) \<in> \<Theta>[F](\<lambda>x. f x powr y)" by (subst A(2))
    thus "(\<lambda>x. h x) \<in> \<Theta>[F](\<lambda>x. f x powr y)" by simp
  qed
qed


lemmas bigtheta_factors_eq = 
  bigtheta_mult_eq_set_mult bigtheta_inverse_eq_set_inverse bigtheta_divide_eq_set_divide 
  bigtheta_pow_eq_set_pow bigtheta_powr_eq_set_powr

lemmas landau_bigtheta_congs = landau_symbols[THEN landau_symbol.cong_bigtheta]

lemma (in landau_symbol) meta_cong_bigtheta: "\<Theta>[F](f) \<equiv> \<Theta>[F](g) \<Longrightarrow> L F (f) \<equiv> L F (g)"
  using bigtheta_refl[of f] by (intro eq_reflection cong_bigtheta) blast

lemmas landau_bigtheta_meta_congs = landau_symbols[THEN landau_symbol.meta_cong_bigtheta]

(* TODO: Make this work with bigtheta_powr_eq_set_powr *)
  
  
(* Additional theorems, contributed by Andreas Lochbihler and adapted by Manuel Eberl *)

lemma eventually_nonneg_at_top: 
  assumes "filterlim f at_top F"
  shows   "eventually_nonneg F f"
proof -
  from assms have "eventually (\<lambda>x. f x \<ge> 0) F"
    by (simp add: filterlim_at_top)
  thus ?thesis unfolding eventually_nonneg_def by eventually_elim simp
qed

lemma eventually_nonzero_at_top: 
  assumes "filterlim (f :: 'a \<Rightarrow> 'b :: {linordered_field, real_normed_field}) at_top F"
  shows   "eventually_nonzero F f"
proof -
  from assms have "eventually (\<lambda>x. f x \<ge> 1) F"
    by (simp add: filterlim_at_top)
  thus ?thesis unfolding eventually_nonzero_def by eventually_elim auto
qed

lemma eventually_nonneg_at_top_ASSUMPTION [eventually_nonzero_simps]:
  "ASSUMPTION (filterlim f at_top F) \<Longrightarrow> eventually_nonneg F f"
  by (simp add: ASSUMPTION_def eventually_nonneg_at_top)

lemma eventually_nonzero_at_top_ASSUMPTION [eventually_nonzero_simps]:
  "ASSUMPTION (filterlim f (at_top :: 'a :: {linordered_field, real_normed_field} filter) F) \<Longrightarrow> 
     eventually_nonzero F f"
  using eventually_nonzero_at_top[of f F] by (simp add: ASSUMPTION_def)

lemma filterlim_at_top_iff_smallomega:
  fixes f :: "_ \<Rightarrow> real"
  shows "filterlim f at_top F \<longleftrightarrow> f \<in> \<omega>[F](\<lambda>_. 1) \<and> eventually_nonneg F f"
  unfolding eventually_nonneg_def
proof safe
  assume A: "filterlim f at_top F"
  thus B: "eventually (\<lambda>x. f x \<ge> 0) F" by (simp add: eventually_nonzero_simps)
  {
    fix c
    from A have "filterlim (\<lambda>x. norm (f x)) at_top F"
      by (intro filterlim_at_infinity_imp_norm_at_top filterlim_at_top_imp_at_infinity) 
    hence "eventually (\<lambda>x. norm (f x) \<ge> c) F" by (auto simp: filterlim_at_top)
  }
  thus "f \<in> \<omega>[F](\<lambda>_. 1)" by (rule landau_omega.smallI)
next
  assume A: "f \<in> \<omega>[F](\<lambda>_. 1)" and B: "eventually (\<lambda>x. f x \<ge> 0) F"
  {
    fix c :: real assume "c > 0"
    from landau_omega.smallD[OF A this] B 
      have "eventually (\<lambda>x. f x \<ge> c) F" by eventually_elim simp
  }
  thus "filterlim f at_top F"
    by (subst filterlim_at_top_gt[of _ _ 0]) simp_all
qed

lemma smallomega_1_iff: 
  "eventually_nonneg F f \<Longrightarrow> f \<in> \<omega>[F](\<lambda>_. 1 :: real) \<longleftrightarrow> filterlim f at_top F"
  by (simp add: filterlim_at_top_iff_smallomega)

lemma smallo_1_iff: 
  "eventually_nonneg F f \<Longrightarrow> (\<lambda>_. 1 :: real) \<in> o[F](f) \<longleftrightarrow> filterlim f at_top F"
  by (simp add: filterlim_at_top_iff_smallomega smallomega_iff_smallo)

lemma eventually_nonneg_add1 [eventually_nonzero_simps]:
  assumes "eventually_nonneg F f" "g \<in> o[F](f)"
  shows   "eventually_nonneg F (\<lambda>x. f x + g x :: real)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_add2 [eventually_nonzero_simps]:
  assumes "eventually_nonneg F g" "f \<in> o[F](g)"
  shows   "eventually_nonneg F (\<lambda>x. f x + g x :: real)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_diff1 [eventually_nonzero_simps]:
  assumes "eventually_nonneg F f" "g \<in> o[F](f)"
  shows   "eventually_nonneg F (\<lambda>x. f x - g x :: real)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma eventually_nonneg_diff2 [eventually_nonzero_simps]:
  assumes "eventually_nonneg F (\<lambda>x. - g x)" "f \<in> o[F](g)"
  shows   "eventually_nonneg F (\<lambda>x. f x - g x :: real)"
  using  landau_o.smallD[OF assms(2) zero_less_one] assms(1) unfolding eventually_nonneg_def
  by eventually_elim simp_all

lemma bigo_const_inverse [simp]:
  assumes "filterlim f at_top F" "F \<noteq> bot"
  shows "(\<lambda>_. c) \<in> O[F](\<lambda>x. inverse (f x) :: real) \<longleftrightarrow> c = 0"
proof -
  {
    assume A: "(\<lambda>_. 1) \<in> O[F](\<lambda>x. inverse (f x))"
    from assms have "(\<lambda>_. 1) \<in> o[F](f)"
      by (simp add: eventually_nonzero_simps smallomega_iff_smallo filterlim_at_top_iff_smallomega)
    also from assms A have "f \<in> O[F](\<lambda>_. 1)"
      by (simp add: eventually_nonzero_simps landau_divide_simps)
    finally have False using assms by (simp add: landau_o.small_refl_iff)
  }
  thus ?thesis by (cases "c = 0") auto
qed
 
lemma smallo_const_inverse [simp]:
  "filterlim f at_top F \<Longrightarrow> F \<noteq> bot \<Longrightarrow> (\<lambda>_. c :: real) \<in> o[F](\<lambda>x. inverse (f x)) \<longleftrightarrow> c = 0"
  by (auto dest: landau_o.small_imp_big)

lemma const_in_smallo_const [simp]: "(\<lambda>_. b) \<in> o(\<lambda>_ :: _ :: linorder. c) \<longleftrightarrow> b = 0" (is "?lhs \<longleftrightarrow> ?rhs")
  by (cases "b = 0"; cases "c = 0") (simp_all add: landau_o.small_refl_iff)

end
