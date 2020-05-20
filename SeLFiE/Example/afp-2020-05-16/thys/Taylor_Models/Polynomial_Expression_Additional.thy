theory Polynomial_Expression_Additional
  imports
    "Polynomial_Expression"
    "HOL-Decision_Procs.Approximation"
begin

lemma real_of_float_eq_zero_iff[simp]: "real_of_float x = 0 \<longleftrightarrow> x = 0"
  by (simp add: real_of_float_eq)

text \<open>Theory @{theory Taylor_Models.Polynomial_Expression} contains a, more or less, 1:1 generalization
   of theory \<open>Multivariate_Polynomial\<close>. Any additions belong here.\<close>

declare [[coercion_map map_poly]]
declare [[coercion "interval_of::float\<Rightarrow>float interval"]]

text \<open>Apply float interval arguments to a float poly.\<close>
value "Ipoly [Ivl (Float 4 (-6)) (Float 10 6)] (poly.Add (poly.C (Float 3 5)) (poly.Bound 0))"

text \<open>@{term map_poly} for homomorphisms\<close>

lemma map_poly_homo_polyadd_eq_zero_iff:
  "map_poly f (p +\<^sub>p q) = 0\<^sub>p \<longleftrightarrow> p +\<^sub>p q = 0\<^sub>p"
  if [symmetric, simp]: "\<And>x y. f (x + y) = f x + f y" "\<And>x. f x = 0 \<longleftrightarrow> x = 0"
  by (induction p q rule: polyadd.induct) auto

lemma zero_iffD: "(\<And>x. f x = 0 \<longleftrightarrow> x = 0) \<Longrightarrow> f 0 = 0"
  by auto

lemma map_poly_homo_polyadd:
  "map_poly f (p1 +\<^sub>p p2) = map_poly f p1 +\<^sub>p map_poly f p2"
  if [simp]: "\<And>x y. f (x + y) = f x + f y" "\<And>x. f x = 0 \<longleftrightarrow> x = 0"
  by (induction p1 p2 rule: polyadd.induct)
    (auto simp: zero_iffD[OF that(2)] Let_def map_poly_homo_polyadd_eq_zero_iff)

lemma map_poly_homo_polyneg:
  "map_poly f (~\<^sub>p p1) = ~\<^sub>p (map_poly f p1)"
  if [simp]: "\<And>x y. f (- x) = - f x"
  by (induction p1) (auto simp: Let_def map_poly_homo_polyadd_eq_zero_iff)

lemma map_poly_homo_polysub:
  "map_poly f (p1 -\<^sub>p p2) = map_poly f p1 -\<^sub>p map_poly f p2"
  if [simp]: "\<And>x y. f (x + y) = f x + f y" "\<And>x. f x = 0 \<longleftrightarrow> x = 0" "\<And>x y. f (- x) = - f x"
  by (auto simp: polysub_def map_poly_homo_polyadd map_poly_homo_polyneg)

lemma map_poly_homo_polymul:
  "map_poly f (p1 *\<^sub>p p2) = map_poly f p1 *\<^sub>p map_poly f p2"
  if [simp]: "\<And>x y. f (x + y) = f x + f y" "\<And>x. f x = 0 \<longleftrightarrow> x = 0" "\<And>x y. f (x * y) = f x * f y"
  by (induction p1 p2 rule: polymul.induct)
    (auto simp: zero_iffD[OF that(2)] map_poly_homo_polyadd)

lemma map_poly_homo_polypow:
  "map_poly f (p1 ^\<^sub>p n) = map_poly f p1 ^\<^sub>p n"
  if [simp]: "\<And>x y. f (x + y) = f x + f y" "\<And>x. f x = 0 \<longleftrightarrow> x = 0" "\<And>x y. f (x * y) = f x * f y"
    "f 1 = 1" 
proof(induction n rule: nat_less_induct)
  case (1 n)
  then show ?case
    apply (cases n)
     apply (auto simp: map_poly_homo_polyadd map_poly_homo_polymul)
    by (smt Suc_less_eq div2_less_self even_Suc odd_Suc_div_two map_poly_homo_polymul that)
qed

lemmas map_poly_homo_polyarith = map_poly_homo_polyadd map_poly_homo_polyneg map_poly_homo_polysub map_poly_homo_polymul map_poly_homo_polypow

text \<open>Count the number of parameters of a polynomial.\<close>

fun num_params :: "'a poly \<Rightarrow> nat"
  where "num_params (poly.C c) = 0"
  | "num_params (poly.Bound n)  = Suc n"
  | "num_params (poly.Add a b)  = max (num_params a) (num_params b)"
  | "num_params (poly.Sub a b)  = max (num_params a) (num_params b)"
  | "num_params (poly.Mul a b)  = max (num_params a) (num_params b)"
  | "num_params (poly.Neg a)    = num_params a"
  | "num_params (poly.Pw a n)   = num_params a"
  | "num_params (poly.CN a n b) = max (max (num_params a) (num_params b)) (Suc n)"

lemma num_params_map_poly[simp]:
  shows "num_params (map_poly f p) = num_params p"
  by (induction p, simp_all)

lemma num_params_polyadd:
  shows "num_params (p1 +\<^sub>p p2) \<le> max (num_params p1) (num_params p2)"
proof (induction p1 p2 rule: polyadd.induct)
  case (4 c n p c' n' p')
  then show ?case
    by auto (auto simp: max_def Let_def split: if_splits)
qed auto

lemma num_params_polyneg:
  shows "num_params (~\<^sub>p p) = num_params p"
  by (induction p rule: polyneg.induct) simp_all

lemma num_params_polymul:
  shows "num_params (p1 *\<^sub>p p2) \<le> max (num_params p1) (num_params p2)"
proof (induction p1 p2 rule: polymul.induct)
  case (4 c n p c' n' p')
  then show ?case
    by auto (auto simp: max_def Let_def split: if_splits
          intro!: num_params_polyadd[THEN order_trans])
qed auto

lemma num_params_polypow:
  shows "num_params (p ^\<^sub>p n) \<le> num_params p"
  apply (induction n rule: polypow.induct)
  unfolding polypow.simps
  by (auto intro!: order_trans[OF num_params_polymul]
      simp: Let_def simp del: polypow.simps)

lemma num_params_polynate:
  shows "num_params (polynate p) \<le> num_params p"
proof(induction p rule: polynate.induct)
  case (2 l r)
  thus ?case
    using num_params_polyadd[of "polynate l" "polynate r"]
    by simp
next
  case (3 l r)
  thus ?case
    using num_params_polyadd[of "polynate l" "~\<^sub>p (polynate r)"] 
    by (simp add: polysub_def num_params_polyneg)
next
  case (4 l r)
  thus ?case
    using num_params_polymul[of "polynate l" "polynate r"]
    by simp
next
  case (5 p)
  thus ?case
    by (simp add: num_params_polyneg)
next
  case (6 p n)
  thus ?case
    using num_params_polypow[of n "polynate p"]
    by simp
qed simp_all

lemma polynate_map_poly_real[simp]:
  fixes p :: "float poly"
  shows "map_poly real_of_float (polynate p) = polynate (map_poly real_of_float p)"
  by (induction p) (simp_all add: map_poly_homo_polyarith)

text \<open>Evaluating a float poly is equivalent to evaluating the corresponding
   real poly with the float parameters converted to reals.\<close>
lemma Ipoly_real_float_eqiv:
  fixes p::"float poly" and xs::"float list"
  assumes "num_params p \<le> length xs"
  shows "Ipoly xs (p::real poly) = Ipoly xs p"
  using assms by (induction p, simp_all)

text \<open>Evaluating an \<open>'a poly\<close> with \<open>'a interval\<close> arguments is monotone.\<close>
lemma Ipoly_interval_args_mono:
  fixes p::"'a::linordered_idom poly"
    and   x::"'a list"
    and   xs::"'a interval list"
  assumes "x all_in\<^sub>i xs"
  assumes "num_params p \<le> length xs"
  shows "Ipoly x p \<in> set_of (Ipoly xs (map_poly interval_of p))"
  using assms
  by (induction p)
    (auto simp: all_in_i_def plus_in_intervalI minus_in_intervalI times_in_intervalI
      uminus_in_intervalI set_of_power_mono)

lemma Ipoly_interval_args_inc_mono:
  fixes p::"'a::{real_normed_algebra, linear_continuum_topology, linordered_idom} poly"
    and   I::"'a interval list" and J::"'a interval list"
  assumes "num_params p \<le> length I"
  assumes "I all_subset J"
  shows "set_of (Ipoly I (map_poly interval_of p)) \<subseteq> set_of (Ipoly J (map_poly interval_of p))"
  using assms
  by (induction p)
    (simp_all add: set_of_add_inc set_of_sub_inc set_of_mul_inc set_of_neg_inc set_of_pow_inc)

section \<open>Splitting polynomials to reduce floating point precision\<close>

text \<open>TODO: Move this!
  Definitions regarding floating point numbers should not be in a theory about polynomials.\<close>
fun float_prec :: "float \<Rightarrow> int"
  where "float_prec f = (let p=exponent f in if p \<ge> 0 then 0 else -p)"

fun float_round :: "nat \<Rightarrow> float \<Rightarrow> float"
  where "float_round prec f = (
         let d = float_down prec f; u = float_up prec f
         in if f - d < u - f then d else u)"


text \<open>Splits any polynomial \<open>p\<close> into two polynomials \<open>l\<close>, \<open>r\<close>, such that \<open>\<forall>x::real. p(x) = l(x) + r(x)\<close>
   and all floating point coefficients in \<open>p\<close> are rounded to precision \<open>prec\<close>.
   Not all cases need to give good results. Polynomials normalized with polynate
   only contain \<open>poly.C\<close> and \<open>poly.CN\<close> constructors.\<close>
fun split_by_prec :: "nat \<Rightarrow> float poly \<Rightarrow> float poly * float poly"
  where "split_by_prec prec (poly.C f) = (let r = float_round prec f in (poly.C r, poly.C (f - r)))"
  | "split_by_prec prec (poly.Bound n) = (poly.Bound n, poly.C 0)"
  | "split_by_prec prec (poly.Add l r) = (let (ll, lr) = split_by_prec prec l;
                                                (rl, rr) = split_by_prec prec r
                                            in (poly.Add ll rl, poly.Add lr rr))"
  | "split_by_prec prec (poly.Sub l r) = (let (ll, lr) = split_by_prec prec l;
                                             (rl, rr) = split_by_prec prec r
                                         in (poly.Sub ll rl, poly.Sub lr rr))"
  | "split_by_prec prec (poly.Mul l r) = (let (ll, lr) = split_by_prec prec l;
                                                (rl, rr) = split_by_prec prec r
                                            in (poly.Mul ll rl, poly.Add (poly.Add (poly.Mul lr rl) (poly.Mul ll rr)) (poly.Mul lr rr)))"
  | "split_by_prec prec (poly.Neg p) = (let (l, r) = split_by_prec prec p in (poly.Neg l, poly.Neg r))"
  | "split_by_prec prec (poly.Pw p 0) = (poly.C 1, poly.C 0)"
  | "split_by_prec prec (poly.Pw p (Suc n)) = (let (l, r) = split_by_prec prec p in (poly.Pw l n, poly.Sub (poly.Pw p (Suc n)) (poly.Pw l n)))"
  | "split_by_prec prec (poly.CN c n p) = (let (cl, cr) = split_by_prec prec c;
                                                 (pl, pr) = split_by_prec prec p
                                             in (poly.CN cl n pl, poly.CN cr n pr))"

text \<open>TODO: Prove precision constraint on \<open>l\<close>.\<close>
lemma split_by_prec_correct:
  fixes args :: "real list"
  assumes "(l, r) = split_by_prec prec p"
  shows "Ipoly args p = Ipoly args l + Ipoly args r" (is ?P1)
    and   "num_params l \<le> num_params p" (is ?P2)
    and   "num_params r \<le> num_params p" (is ?P3)
  unfolding atomize_conj
  using assms
proof(induction p arbitrary: l r)
  case (Add p1 p2 l r)
  thus ?case
    apply(simp add: Add(1,2)[OF prod.collapse] split_beta)
    using max.coboundedI1 max.coboundedI2 prod.collapse
    by metis
next
  case (Sub p1 p2 l r)
  thus ?case
    apply(simp add: Sub(1,2)[OF prod.collapse] split_beta)
    using max.coboundedI1 max.coboundedI2 prod.collapse
    by metis
next
  case (Mul p1 p2 l r)
  thus ?case
    apply(simp add: Mul(1,2)[OF prod.collapse] split_beta algebra_simps)
    using max.coboundedI1 max.coboundedI2 prod.collapse
    by metis
next
  case (Neg p l r) 
  thus ?case by (simp add: Neg(1)[OF prod.collapse] split_beta)
next
  case (Pw p n l r)
  thus ?case by (cases n) (simp_all add: Pw(1)[OF prod.collapse] split_beta)
next
  case (CN c n p2)
  thus ?case
    apply(simp add: CN(1,2)[OF prod.collapse] split_beta algebra_simps) 
    by (meson le_max_iff_disj prod.collapse)
qed (simp_all add: Let_def)

section \<open>Splitting polynomials by degree\<close>

fun maxdegree :: "('a::zero) poly \<Rightarrow> nat"
  where "maxdegree (poly.C c) = 0"
  | "maxdegree (poly.Bound n) = 1"
  | "maxdegree (poly.Add l r) = max (maxdegree l) (maxdegree r)"
  | "maxdegree (poly.Sub l r) = max (maxdegree l) (maxdegree r)"
  | "maxdegree (poly.Mul l r) = maxdegree l + maxdegree r"
  | "maxdegree (poly.Neg p) = maxdegree p"
  | "maxdegree (poly.Pw p n) = n * maxdegree p"
  | "maxdegree (poly.CN c n p) = max (maxdegree c) (1 + maxdegree p)"

fun split_by_degree :: "nat \<Rightarrow> 'a::zero poly \<Rightarrow> 'a poly * 'a poly"
  where "split_by_degree n (poly.C c) = (poly.C c, poly.C 0)"
  | "split_by_degree 0 p = (poly.C 0, p)"
  | "split_by_degree (Suc n) (poly.CN c v p) = (
         let (cl, cr) = split_by_degree (Suc n) c;
             (pl, pr) = split_by_degree n p
         in (poly.CN cl v pl, poly.CN cr v pr))"
    \<comment> \<open>This function is only intended for use on polynomials in normal form.
       Hence most cases never get executed.\<close>
  | "split_by_degree n p = (poly.C 0, p)"

lemma split_by_degree_correct:
  fixes x :: "real list" and p :: "float poly"
  assumes "(l, r) = split_by_degree ord p"
  shows "maxdegree l \<le> ord" (is ?P1)
    and   "Ipoly x p = Ipoly x l + Ipoly x r" (is ?P2)
    and   "num_params l \<le> num_params p" (is ?P3)
    and   "num_params r \<le> num_params p" (is ?P4)
  unfolding atomize_conj
  using assms
proof(induction p arbitrary: l r ord)
  case (C c l r ord)
  thus ?case by simp
next
  case (Bound v l r ord)
  thus ?case by (cases ord) simp_all
next
  case (Add p1 p2 l r ord)
  thus ?case by (cases ord) simp_all
next
  case (Sub p1 p2 l r ord)
  thus ?case by (cases ord) simp_all
next
  case (Mul p1 p2 l r ord)
  thus ?case by (cases ord) simp_all
next
  case (Neg p l r ord)
  thus ?case by (cases ord) simp_all
next
  case (Pw p k l r ord)
  thus ?case by (cases ord) simp_all
next
  case (CN c v p l r ord)
  then show ?case
  proof(cases ord)
    case (Suc m)
    obtain cl cr where cl_cr_def: "(cl, cr) = split_by_degree (Suc m) c"
      by (cases "split_by_degree (Suc m) c", simp)
    obtain pl pr where pl_pr_def: "(pl, pr) = split_by_degree m p"
      by (cases "split_by_degree m p", simp)
    have [simp]: "Ipoly x p = Ipoly x pl + Ipoly x pr"
      using CN(2)[OF pl_pr_def]
      by (cases ord) simp_all
    from CN(3)
    have l_decomp: "l = CN cl v pl" and r_decomp: "r = CN cr v pr"
      by (simp_all add: Suc cl_cr_def[symmetric] pl_pr_def[symmetric])
    show ?thesis
      using CN(1)[OF cl_cr_def]  CN(2)[OF pl_pr_def]
      unfolding l_decomp
      by (cases p) (auto simp add: l_decomp r_decomp algebra_simps Suc)
  qed simp
qed

text \<open>Operations on lists.\<close>

lemma length_map2[simp]: "length (map2 f a b) = min (length a) (length b)"
proof(induction "map2 f a b" arbitrary: a b)
  case (Nil a b)
  hence "a = [] | b = []"
    by(cases a, simp, cases b, simp_all)
  then show ?case
    by auto
next
  case (Cons x c a b)
  have "0 < length a \<and> 0 < length b"
    using Cons(2)
    by (cases a, simp, cases b, simp_all)
  then obtain xa ar xb br
    where a_decomp[simp]: "a = xa # ar"
      and   b_decomp[simp]: "b = xb # br"
    by (cases a, simp_all, cases b, simp_all)
  show ?case
    using Cons
    by simp
qed

lemma map2_nth[simp]:
  assumes "n < length a"
  assumes "n < length b"
  shows "(map2 f a b)!n = f (a!n) (b!n)"
  using assms
proof(induction n arbitrary: a b)
  case (0 a b)
  have "0 < length a" and "0 < length b"
    using 0
    by simp_all
  thus ?case
    using 0
    by simp
next
  case (Suc n a b)
  from Suc.prems have  "0 < length a" "0 < length b" "n < length (tl a)" "n < length (tl b)"
    using Suc.prems by auto
  have "map2 f a b = map2 f (hd a # tl a) (hd b # tl b)"
    using \<open>0 < length a\<close> \<open>0 < length b\<close>
    by simp
  also have "\<dots> ! Suc n = map2 f (tl a) (tl b) ! n"
    by simp
  also have "\<dots> = f (tl a ! n) (tl b ! n)"
    using \<open>n < length (tl a)\<close> \<open>n < length (tl b)\<close> by (rule Suc.IH)
  also have "tl a ! n = (hd a # tl a) ! Suc n" by simp
  also have "(hd a # tl a) = a" using \<open>0 < length a\<close> by simp
  also have "tl b ! n = (hd b # tl b) ! Suc n" by simp
  also have "(hd b # tl b) = b" using \<open>0 < length b\<close> by simp
  finally show ?case .
qed

text \<open>Translating a polynomial by a vector.\<close>
fun poly_translate :: "'a list \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
  where "poly_translate vs (poly.C c)  = poly.C c"
  | "poly_translate vs (poly.Bound n) = poly.Add (poly.Bound n) (poly.C (vs ! n))"
  | "poly_translate vs (poly.Add l r) = poly.Add (poly_translate vs l) (poly_translate vs r)"
  | "poly_translate vs (poly.Sub l r) = poly.Sub (poly_translate vs l) (poly_translate vs r)"
  | "poly_translate vs (poly.Mul l r) = poly.Mul (poly_translate vs l) (poly_translate vs r)"
  | "poly_translate vs (poly.Neg p) = poly.Neg (poly_translate vs p)"
  | "poly_translate vs (poly.Pw p n) = poly.Pw (poly_translate vs p) n"
  | "poly_translate vs (poly.CN c n p) = poly.Add (poly_translate vs c) (poly.Mul (poly.Add (poly.Bound n) (poly.C (vs ! n))) (poly_translate vs p))"

text \<open>Translating a polynomial is equivalent to translating its argument.\<close>
lemma poly_translate_correct:
  assumes "num_params p \<le> length x"
  assumes "length x = length v"
  shows "Ipoly x (poly_translate v p) = Ipoly (map2 (+) x v) p"
  using assms
  by (induction p, simp_all)

lemma real_poly_translate: 
  assumes "num_params p \<le> length v"
  shows "Ipoly x (map_poly real_of_float (poly_translate v p)) = Ipoly x (poly_translate v (map_poly real_of_float p))"
  using assms
  by (induction p, simp_all)

lemma num_params_poly_translate[simp]:
  shows "num_params (poly_translate v p) = num_params p"
  by (induction p, simp_all)

end
