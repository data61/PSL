(*  Title:      Multivariate_Polynomial.thy
    Author:     Amine Chaieb
    Modified by Christoph Traut to work on the most general type possible, for the use in Taylor models.
*)

section \<open>Implementation and verification of multivariate polynomials\<close>

theory Polynomial_Expression
imports Complex_Main 
        "HOL-Decision_Procs.Rat_Pair"
        "HOL-Decision_Procs.Polynomial_List"
        "HOL-Library.Float"
begin

text \<open>TODO: generalize in library and remove this theory.\<close>

subsection \<open>Datatype of polynomial expressions\<close>

datatype 'a poly = C 'a | Bound nat | Add "'a poly" "'a poly" | Sub "'a poly" "'a poly"
  | Mul "'a poly" "'a poly"| Neg "'a poly"| Pw "'a poly" nat | CN "'a poly" nat "'a poly"

abbreviation poly_0 :: "'a::zero poly" ("0\<^sub>p") where "0\<^sub>p \<equiv> C 0"
abbreviation poly_p :: "'a \<Rightarrow> 'a poly" ("'((_)')\<^sub>p") where "(i)\<^sub>p \<equiv> C i"


subsection\<open>Boundedness, substitution and all that\<close>

primrec polysize:: "'a poly \<Rightarrow> nat"
where
  "polysize (C c) = 1"
| "polysize (Bound n) = 1"
| "polysize (Neg p) = 1 + polysize p"
| "polysize (Add p q) = 1 + polysize p + polysize q"
| "polysize (Sub p q) = 1 + polysize p + polysize q"
| "polysize (Mul p q) = 1 + polysize p + polysize q"
| "polysize (Pw p n) = 1 + polysize p"
| "polysize (CN c n p) = 4 + polysize c + polysize p"

primrec polybound0:: "'a poly \<Rightarrow> bool" \<comment> \<open>a poly is INDEPENDENT of Bound 0\<close>
where
  "polybound0 (C c) \<longleftrightarrow> True"
| "polybound0 (Bound n) \<longleftrightarrow> n > 0"
| "polybound0 (Neg a) \<longleftrightarrow> polybound0 a"
| "polybound0 (Add a b) \<longleftrightarrow> polybound0 a \<and> polybound0 b"
| "polybound0 (Sub a b) \<longleftrightarrow> polybound0 a \<and> polybound0 b"
| "polybound0 (Mul a b) \<longleftrightarrow> polybound0 a \<and> polybound0 b"
| "polybound0 (Pw p n) \<longleftrightarrow> polybound0 p"
| "polybound0 (CN c n p) \<longleftrightarrow> n \<noteq> 0 \<and> polybound0 c \<and> polybound0 p"

primrec polysubst0:: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" \<comment> \<open>substitute a poly into a poly for Bound 0\<close>
where
  "polysubst0 t (C c) = C c"
| "polysubst0 t (Bound n) = (if n = 0 then t else Bound n)"
| "polysubst0 t (Neg a) = Neg (polysubst0 t a)"
| "polysubst0 t (Add a b) = Add (polysubst0 t a) (polysubst0 t b)"
| "polysubst0 t (Sub a b) = Sub (polysubst0 t a) (polysubst0 t b)"
| "polysubst0 t (Mul a b) = Mul (polysubst0 t a) (polysubst0 t b)"
| "polysubst0 t (Pw p n) = Pw (polysubst0 t p) n"
| "polysubst0 t (CN c n p) =
    (if n = 0 then Add (polysubst0 t c) (Mul t (polysubst0 t p))
     else CN (polysubst0 t c) n (polysubst0 t p))"

fun decrpoly:: "'a poly \<Rightarrow> 'a poly"
where
  "decrpoly (Bound n) = Bound (n - 1)"
| "decrpoly (Neg a) = Neg (decrpoly a)"
| "decrpoly (Add a b) = Add (decrpoly a) (decrpoly b)"
| "decrpoly (Sub a b) = Sub (decrpoly a) (decrpoly b)"
| "decrpoly (Mul a b) = Mul (decrpoly a) (decrpoly b)"
| "decrpoly (Pw p n) = Pw (decrpoly p) n"
| "decrpoly (CN c n p) = CN (decrpoly c) (n - 1) (decrpoly p)"
| "decrpoly a = a"


subsection \<open>Degrees and heads and coefficients\<close>

fun degree :: "'a poly \<Rightarrow> nat"
where
  "degree (CN c 0 p) = 1 + degree p"
| "degree p = 0"

fun head :: "'a poly \<Rightarrow> 'a poly"
where
  "head (CN c 0 p) = head p"
| "head p = p"

text \<open>More general notions of degree and head.\<close>

fun degreen :: "'a poly \<Rightarrow> nat \<Rightarrow> nat"
where
  "degreen (CN c n p) = (\<lambda>m. if n = m then 1 + degreen p n else 0)"
| "degreen p = (\<lambda>m. 0)"

fun headn :: "'a poly \<Rightarrow> nat \<Rightarrow> 'a poly"
where
  "headn (CN c n p) = (\<lambda>m. if n \<le> m then headn p m else CN c n p)"
| "headn p = (\<lambda>m. p)"

fun coefficients :: "'a poly \<Rightarrow> 'a poly list"
where
  "coefficients (CN c 0 p) = c # coefficients p"
| "coefficients p = [p]"

fun isconstant :: "'a poly \<Rightarrow> bool"
where
  "isconstant (CN c 0 p) = False"
| "isconstant p = True"

fun behead :: "'a::zero poly \<Rightarrow> 'a poly"
where
  "behead (CN c 0 p) = (let p' = behead p in if p' = 0\<^sub>p then c else CN c 0 p')"
| "behead p = 0\<^sub>p"

fun headconst :: "'a poly \<Rightarrow> 'a"
where
  "headconst (CN c n p) = headconst p"
| "headconst (C n) = n"


subsection \<open>Operations for normalization\<close>

declare if_cong[fundef_cong del]
declare let_cong[fundef_cong del]

fun polyadd :: "'a::{plus,zero} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" (infixl "+\<^sub>p" 60)
where
  "polyadd (C c) (C c') = C (c + c')"
| "polyadd (C c) (CN c' n' p') = CN (polyadd (C c) c') n' p'"
| "polyadd (CN c n p) (C c') = CN (polyadd c (C c')) n p"
| "polyadd (CN c n p) (CN c' n' p') =
    (if n < n' then CN (polyadd c (CN c' n' p')) n p
     else if n' < n then CN (polyadd (CN c n p) c') n' p'
     else
      let
        cc' = polyadd c c';
        pp' = polyadd p p'
      in if pp' = 0\<^sub>p then cc' else CN cc' n pp')"
| "polyadd a b = Add a b"


fun polyneg :: "'a::uminus poly \<Rightarrow> 'a poly" ("~\<^sub>p")
where
  "polyneg (C c) = C (-c)"
| "polyneg (CN c n p) = CN (polyneg c) n (polyneg p)"
| "polyneg a = Neg a"

definition polysub :: "'a::{plus,zero,uminus} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" (infixl "-\<^sub>p" 60)
  where "p -\<^sub>p q = polyadd p (polyneg q)"

fun polymul :: "'a::{plus,zero,times} poly \<Rightarrow> 'a poly \<Rightarrow> 'a poly" (infixl "*\<^sub>p" 60)
where
  "polymul (C c) (C c') = C (c * c')"
| "polymul (C c) (CN c' n' p') =
    (if c = 0 then 0\<^sub>p else CN (polymul (C c) c') n' (polymul (C c) p'))"
| "polymul (CN c n p) (C c') =
    (if c' = 0  then 0\<^sub>p else CN (polymul c (C c')) n (polymul p (C c')))"
| "polymul (CN c n p) (CN c' n' p') =
    (if n < n' then CN (polymul c (CN c' n' p')) n (polymul p (CN c' n' p'))
     else if n' < n then CN (polymul (CN c n p) c') n' (polymul (CN c n p) p')
     else polyadd (polymul (CN c n p) c') (CN 0\<^sub>p n' (polymul (CN c n p) p')))"
| "polymul a b = Mul a b"

declare if_cong[fundef_cong]
declare let_cong[fundef_cong]

fun polypow :: "nat \<Rightarrow> 'a::{plus,zero,times,one} poly \<Rightarrow> 'a poly"
where
  "polypow 0 = (\<lambda>p. (1)\<^sub>p)"
| "polypow n =
    (\<lambda>p.
      let
        q = polypow (n div 2) p;
        d = polymul q q
      in if even n then d else polymul p d)"

abbreviation poly_pow :: "'a::{plus,zero,times,one} poly \<Rightarrow> nat \<Rightarrow> 'a poly" (infixl "^\<^sub>p" 60)
  where "a ^\<^sub>p k \<equiv> polypow k a"

function polynate :: "'a::{plus,uminus,zero,times,one} poly \<Rightarrow> 'a poly"
where
  "polynate (Bound n) = CN 0\<^sub>p n (1)\<^sub>p"
| "polynate (Add p q) = polynate p +\<^sub>p polynate q"
| "polynate (Sub p q) = polynate p -\<^sub>p polynate q"
| "polynate (Mul p q) = polynate p *\<^sub>p polynate q"
| "polynate (Neg p) = ~\<^sub>p (polynate p)"
| "polynate (Pw p n) = polynate p ^\<^sub>p n"
| "polynate (CN c n p) = polynate (Add c (Mul (Bound n) p))"
| "polynate (C c) = C c"
  by pat_completeness auto
termination by (relation "measure polysize") auto

fun poly_cmul :: "'a::{plus,times,zero} \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "poly_cmul y (C x) = C (y * x)"
| "poly_cmul y (CN c n p) = CN (poly_cmul y c) n (poly_cmul y p)"
| "poly_cmul y p = C y *\<^sub>p p"

definition monic :: "'a::{plus,zero,times,one,inverse} poly \<Rightarrow> 'a poly \<times> bool"
where
  "monic p =
    (let h = headconst p
     in if h = 0 then (p, False) else (poly_cmul(1 / h) p, True))"


subsection \<open>Pseudo-division\<close>

definition shift1 :: "'a::zero poly \<Rightarrow> 'a poly"
  where "shift1 p = CN 0\<^sub>p 0 p"

abbreviation funpow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
  where "funpow \<equiv> compow"

partial_function (tailrec) polydivide_aux :: "'a::{plus,zero,uminus,times} poly \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> nat \<times> 'a poly"
where
  "polydivide_aux a n p k s =
    (if s = 0\<^sub>p then (k, s)
     else
      let
        b = head s;
        m = degree s
      in
        if m < n then (k,s)
        else
          let p' = funpow (m - n) shift1 p
          in
            if a = b then polydivide_aux a n p k (s -\<^sub>p p')
            else polydivide_aux a n p (Suc k) ((a *\<^sub>p s) -\<^sub>p (b *\<^sub>p p')))"

definition polydivide :: "'a::{plus,zero,uminus,times} poly \<Rightarrow> 'a poly \<Rightarrow> nat \<times> 'a poly"
  where "polydivide s p = polydivide_aux (head p) (degree p) p 0 s"

fun poly_deriv_aux :: "'a::{plus,zero,uminus,times,one} \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "poly_deriv_aux n (CN c 0 p) = CN (poly_cmul n c) 0 (poly_deriv_aux (n + 1) p)"
| "poly_deriv_aux n p = poly_cmul n p"

fun poly_deriv :: "'a::{plus,zero,uminus,times,one} poly \<Rightarrow> 'a poly"
where
  "poly_deriv (CN c 0 p) = poly_deriv_aux 1 p"
| "poly_deriv p = 0\<^sub>p"


subsection \<open>Semantics of the polynomial representation\<close>

primrec Ipoly :: "'a list \<Rightarrow> 'a poly \<Rightarrow> 'a::{plus,zero,minus,uminus,times,one,power}"
where
  "Ipoly bs (C c) = c"
| "Ipoly bs (Bound n) = bs!n"
| "Ipoly bs (Neg a) = - Ipoly bs a"
| "Ipoly bs (Add a b) = Ipoly bs a + Ipoly bs b"
| "Ipoly bs (Sub a b) = Ipoly bs a - Ipoly bs b"
| "Ipoly bs (Mul a b) = Ipoly bs a * Ipoly bs b"
| "Ipoly bs (Pw t n) = Ipoly bs t ^ n"
| "Ipoly bs (CN c n p) = Ipoly bs c + (bs!n) * Ipoly bs p"

(*abbreviation Ipoly_syntax :: "'a poly \<Rightarrow> 'a list \<Rightarrow>'a::{plus,zero,minus,uminus,times,one,power}"  ("\<lparr>_\<rparr>\<^sub>p\<^bsup>_\<^esup>")
  where "\<lparr>p\<rparr>\<^sub>p\<^bsup>bs\<^esup> \<equiv> Ipoly bs p"*)

lemmas RIpoly_eqs = Ipoly.simps

subsection \<open>Normal form and normalization\<close>

fun isnpolyh:: "'a::zero poly \<Rightarrow> nat \<Rightarrow> bool"
where
  (* TODO: Inject normalization via a custom type class here? *)
  (*"isnpolyh (C c) = (\<lambda>k. isnormNum c)"*)
  "isnpolyh (C c) = (\<lambda>k. True)"
| "isnpolyh (CN c n p) = (\<lambda>k. n \<ge> k \<and> isnpolyh c (Suc n) \<and> isnpolyh p n \<and> p \<noteq> 0\<^sub>p)"
| "isnpolyh p = (\<lambda>k. False)"

lemma isnpolyh_mono: "n' \<le> n \<Longrightarrow> isnpolyh p n \<Longrightarrow> isnpolyh p n'"
  by (induct p rule: isnpolyh.induct) auto

definition isnpoly :: "'a::zero poly \<Rightarrow> bool"
  where "isnpoly p = isnpolyh p 0"

text \<open>polyadd preserves normal forms\<close>

lemma polyadd_normh: "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> isnpolyh (polyadd p q) (min n0 n1)"
proof (induct p q arbitrary: n0 n1 rule: polyadd.induct)
  case (2 ab c' n' p' n0 n1)
  from 2 have  th1: "isnpolyh (C ab) (Suc n')"
    by simp
  from 2(3) have th2: "isnpolyh c' (Suc n')" and nplen1: "n' \<ge> n1"
    by simp_all
  with isnpolyh_mono have cp: "isnpolyh c' (Suc n')"
    by simp
  with 2(1)[OF th1 th2] have th3:"isnpolyh (C ab +\<^sub>p c') (Suc n')"
    by simp
  from nplen1 have n01len1: "min n0 n1 \<le> n'"
    by simp
  then show ?case using 2 th3
    by simp
next
  case (3 c' n' p' ab n1 n0)
  from 3 have  th1: "isnpolyh (C ab) (Suc n')"
    by simp
  from 3(2) have th2: "isnpolyh c' (Suc n')"  and nplen1: "n' \<ge> n1"
    by simp_all
  with isnpolyh_mono have cp: "isnpolyh c' (Suc n')"
    by simp
  with 3(1)[OF th2 th1] have th3:"isnpolyh (c' +\<^sub>p C ab) (Suc n')"
    by simp
  from nplen1 have n01len1: "min n0 n1 \<le> n'"
    by simp
  then show ?case using 3 th3
    by simp
next
  case (4 c n p c' n' p' n0 n1)
  then have nc: "isnpolyh c (Suc n)" and np: "isnpolyh p n"
    by simp_all
  from 4 have nc': "isnpolyh c' (Suc n')" and np': "isnpolyh p' n'"
    by simp_all
  from 4 have ngen0: "n \<ge> n0"
    by simp
  from 4 have n'gen1: "n' \<ge> n1"
    by simp
  consider (eq) "n = n'" | (lt) "n < n'" | (gt) "n > n'"
    by arith
  then show ?case
  proof cases
    case eq
    with "4.hyps"(3)[OF nc nc']
    have ncc':"isnpolyh (c +\<^sub>p c') (Suc n)"
      by auto
    then have ncc'n01: "isnpolyh (c +\<^sub>p c') (min n0 n1)"
      apply(rule isnpolyh_mono[where n'="min n0 n1", rotated])
      using  ngen0 n'gen1
      by auto
    from eq "4.hyps"(4)[OF np np'] have npp': "isnpolyh (p +\<^sub>p p') n"
      by simp
    have minle: "min n0 n1 \<le> n'"
      using ngen0 n'gen1 eq by simp
    from minle npp' ncc'n01 4 eq ngen0 n'gen1 ncc' show ?thesis
      by (simp add: Let_def)
  next
    case lt
    have "min n0 n1 \<le> n0"
      by simp
    with 4 lt have th1:"min n0 n1 \<le> n"
      by auto
    from 4 have th21: "isnpolyh c (Suc n)"
      by simp
    from 4 have th22: "isnpolyh (CN c' n' p') n'"
      by simp
    from lt have th23: "min (Suc n) n' = Suc n"
      by arith
    from "4.hyps"(1)[OF th21 th22] have "isnpolyh (polyadd c (CN c' n' p')) (Suc n)"
      using th23 by simp
    with 4 lt th1 show ?thesis
      by simp
  next
    case gt
    then have gt': "n' < n \<and> \<not> n < n'"
      by simp
    have "min n0 n1 \<le> n1"
      by simp
    with 4 gt have th1: "min n0 n1 \<le> n'"
      by auto
    from 4 have th21: "isnpolyh c' (Suc n')"
      by simp_all
    from 4 have th22: "isnpolyh (CN c n p) n"
      by simp
    from gt have th23: "min n (Suc n') = Suc n'"
      by arith
    from "4.hyps"(2)[OF th22 th21] have "isnpolyh (polyadd (CN c n p) c') (Suc n')"
      using th23 by simp
    with 4 gt th1 show ?thesis
      by simp
  qed
qed auto

lemma polyadd[simp]:
fixes p :: "'a::ring_1 poly"
shows "Ipoly bs (polyadd p q) = Ipoly bs p + Ipoly bs q"
  by (induct p q rule: polyadd.induct)
     (auto simp add: Let_def field_simps distrib_left[symmetric] simp del: distrib_left_NO_MATCH)

lemma polyadd_norm: "isnpoly p \<Longrightarrow> isnpoly q \<Longrightarrow> isnpoly (polyadd p q)"
  using polyadd_normh[of p 0 q 0] by (simp add: isnpoly_def)

text \<open>The degree of addition and other general lemmas needed for the normal form of polymul.\<close>

lemma polyadd_different_degreen:
  assumes "isnpolyh p n0"
    and "isnpolyh q n1"
    and "degreen p m \<noteq> degreen q m"
    and "m \<le> min n0 n1"
  shows "degreen (polyadd p q) m = max (degreen p m) (degreen q m)"
  using assms
proof (induct p q arbitrary: m n0 n1 rule: polyadd.induct)
  case (4 c n p c' n' p' m n0 n1)
  show ?case
  proof (cases "n = n'")
    case True
    with 4(4)[of n n m] 4(3)[of "Suc n" "Suc n" m] 4(5-7)
    show ?thesis by (auto simp: Let_def)
  next
    case False
    with 4 show ?thesis by auto
  qed
qed auto

lemma headnz[simp]: "isnpolyh p n \<Longrightarrow> p \<noteq> 0\<^sub>p \<Longrightarrow> headn p m \<noteq> 0\<^sub>p"
  by (induct p arbitrary: n rule: headn.induct) auto

lemma degree_isnpolyh_Suc[simp]: "isnpolyh p (Suc n) \<Longrightarrow> degree p = 0"
  by (induct p arbitrary: n rule: degree.induct) auto

lemma degreen_0[simp]: "isnpolyh p n \<Longrightarrow> m < n \<Longrightarrow> degreen p m = 0"
  by (induct p arbitrary: n rule: degreen.induct) auto

lemma degree_isnpolyh_Suc': "n > 0 \<Longrightarrow> isnpolyh p n \<Longrightarrow> degree p = 0"
  by (induct p arbitrary: n rule: degree.induct) auto

lemma degree_npolyhCN[simp]: "isnpolyh (CN c n p) n0 \<Longrightarrow> degree c = 0"
  using degree_isnpolyh_Suc by auto

lemma degreen_npolyhCN[simp]: "isnpolyh (CN c n p) n0 \<Longrightarrow> degreen c n = 0"
  using degreen_0 by auto


lemma degreen_polyadd:
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
    and m: "m \<le> max n0 n1"
  shows "degreen (p +\<^sub>p q) m \<le> max (degreen p m) (degreen q m)"
  using np nq m
proof (induct p q arbitrary: n0 n1 m rule: polyadd.induct)
  case (2 c c' n' p' n0 n1)
  then show ?case
    by (cases n') simp_all
next
  case (3 c n p c' n0 n1)
  then show ?case
    by (cases n) auto
next
  case (4 c n p c' n' p' n0 n1 m)
  show ?case
  proof (cases "n = n'")
    case True
    with 4(4)[of n n m] 4(3)[of "Suc n" "Suc n" m] 4(5-7)
    show ?thesis by (auto simp: Let_def)
  next
    case False
    then show ?thesis by simp
  qed
qed auto

lemma polyadd_eq_const_degreen:
  assumes "isnpolyh p n0"
    and "isnpolyh q n1"
    and "polyadd p q = C c"
  shows "degreen p m = degreen q m"
  using assms
proof (induct p q arbitrary: m n0 n1 c rule: polyadd.induct)
  case (4 c n p c' n' p' m n0 n1 x)
  consider "n = n'" | "n > n' \<or> n < n'" by arith
  then show ?case
  proof cases
    case 1
    with 4 show ?thesis
      by (cases "p +\<^sub>p p' = 0\<^sub>p") (auto simp add: Let_def)
  next
    case 2
    with 4 show ?thesis by auto
  qed
qed simp_all

lemma polymul_properties:
fixes p::"'a::field poly"
  assumes np: "isnpolyh p n0"
      and nq: "isnpolyh q n1"
      and m: "m \<le> min n0 n1"
  shows "isnpolyh (p *\<^sub>p q) (min n0 n1)"
    and "p *\<^sub>p q = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p \<or> q = 0\<^sub>p"
    and "degreen (p *\<^sub>p q) m = (if p = 0\<^sub>p \<or> q = 0\<^sub>p then 0 else degreen p m + degreen q m)"
  using np nq m
proof (induct p q arbitrary: n0 n1 m rule: polymul.induct)
  case (2 c c' n' p')
  {
    case (1 n0 n1)
    with "2.hyps"(4-6)[of n' n' n'] and "2.hyps"(1-3)[of "Suc n'" "Suc n'" n']
    show ?case by (auto simp add: min_def)
  next
    case (2 n0 n1)
    then show ?case by auto
  next
    case (3 n0 n1)
    then show ?case using "2.hyps" by auto
  }
next
  case (3 c n p c')
  {
    case (1 n0 n1)
    with "3.hyps"(4-6)[of n n n] and "3.hyps"(1-3)[of "Suc n" "Suc n" n]
    show ?case by (auto simp add: min_def)
  next
    case (2 n0 n1)
    then show ?case by auto
  next
    case (3 n0 n1)
    then show ?case  using "3.hyps" by auto
  }
next
  case (4 c n p c' n' p')
  let ?cnp = "CN c n p" let ?cnp' = "CN c' n' p'"
  {
    case (1 n0 n1)
    then have cnp: "isnpolyh ?cnp n"
      and cnp': "isnpolyh ?cnp' n'"
      and np: "isnpolyh p n"
      and nc: "isnpolyh c (Suc n)"
      and np': "isnpolyh p' n'"
      and nc': "isnpolyh c' (Suc n')"
      and nn0: "n \<ge> n0"
      and nn1: "n' \<ge> n1"
      by simp_all
    {
      assume "n < n'"
      with "4.hyps"(4-5)[OF np cnp', of n] and "4.hyps"(1)[OF nc cnp', of n] nn0 cnp
      have ?case by (simp add: min_def)
    } moreover {
      assume "n' < n"
      with "4.hyps"(16-17)[OF cnp np', of "n'"] and "4.hyps"(13)[OF cnp nc', of "Suc n'"] nn1 cnp'
      have ?case by (cases "Suc n' = n") (simp_all add: min_def)
    } moreover {
      assume "n' = n"
      with "4.hyps"(16-17)[OF cnp np', of n] and "4.hyps"(13)[OF cnp nc', of n] cnp cnp' nn1 nn0
      have ?case
        apply (auto intro!: polyadd_normh)
        apply (simp_all add: min_def isnpolyh_mono[OF nn0])
        done
    }
    ultimately show ?case by arith
  next
    fix n0 n1 m
    assume np: "isnpolyh ?cnp n0"
    assume np':"isnpolyh ?cnp' n1"
    assume m: "m \<le> min n0 n1"
    let ?d = "degreen (?cnp *\<^sub>p ?cnp') m"
    let ?d1 = "degreen ?cnp m"
    let ?d2 = "degreen ?cnp' m"
    let ?eq = "?d = (if ?cnp = 0\<^sub>p \<or> ?cnp' = 0\<^sub>p then 0  else ?d1 + ?d2)"
    have "n' < n \<or> n < n' \<or> n' = n" by auto
    moreover
    {
      assume "n' < n \<or> n < n'"
      with "4.hyps"(3,6,18) np np' m have ?eq
        by auto
    }
    moreover
    {
      assume nn': "n' = n"
      then have nn: "\<not> n' < n \<and> \<not> n < n'" by arith
      from "4.hyps"(16,18)[of n n' n]
        "4.hyps"(13,14)[of n "Suc n'" n]
        np np' nn'
      have norm:
        "isnpolyh ?cnp n"
        "isnpolyh c' (Suc n)"
        "isnpolyh (?cnp *\<^sub>p c') n"
        "isnpolyh p' n"
        "isnpolyh (?cnp *\<^sub>p p') n"
        "isnpolyh (CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n"
        "?cnp *\<^sub>p c' = 0\<^sub>p \<longleftrightarrow> c' = 0\<^sub>p"
        "?cnp *\<^sub>p p' \<noteq> 0\<^sub>p"
        by (auto simp add: min_def)
      {
        assume mn: "m = n"
        from "4.hyps"(17,18)[OF norm(1,4), of n]
          "4.hyps"(13,15)[OF norm(1,2), of n] norm nn' mn
        have degs:
          "degreen (?cnp *\<^sub>p c') n = (if c' = 0\<^sub>p then 0 else ?d1 + degreen c' n)"
          "degreen (?cnp *\<^sub>p p') n = ?d1  + degreen p' n"
          by (simp_all add: min_def)
        from degs norm have th1: "degreen (?cnp *\<^sub>p c') n < degreen (CN 0\<^sub>p n (?cnp *\<^sub>p p')) n"
          by simp
        then have neq: "degreen (?cnp *\<^sub>p c') n \<noteq> degreen (CN 0\<^sub>p n (?cnp *\<^sub>p p')) n"
          by simp
        have nmin: "n \<le> min n n"
          by (simp add: min_def)
        from polyadd_different_degreen[OF norm(3,6) neq nmin] th1
        have deg: "degreen (CN c n p *\<^sub>p c' +\<^sub>p CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n =
            degreen (CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n"
          by simp
        from "4.hyps"(16-18)[OF norm(1,4), of n]
          "4.hyps"(13-15)[OF norm(1,2), of n]
          mn norm m nn' deg
        have ?eq by simp
      }
      moreover
      {
        assume mn: "m \<noteq> n"
        then have mn': "m < n"
          using m np by auto
        from nn' m np have max1: "m \<le> max n n"
          by simp
        then have min1: "m \<le> min n n"
          by simp
        then have min2: "m \<le> min n (Suc n)"
          by simp
        from "4.hyps"(16-18)[OF norm(1,4) min1]
          "4.hyps"(13-15)[OF norm(1,2) min2]
          degreen_polyadd[OF norm(3,6) max1]
        have "degreen (?cnp *\<^sub>p c' +\<^sub>p CN 0\<^sub>p n (?cnp *\<^sub>p p')) m \<le>
            max (degreen (?cnp *\<^sub>p c') m) (degreen (CN 0\<^sub>p n (?cnp *\<^sub>p p')) m)"
          using mn nn' np np' by simp
        with "4.hyps"(16-18)[OF norm(1,4) min1]
          "4.hyps"(13-15)[OF norm(1,2) min2]
          degreen_0[OF norm(3) mn']
        have ?eq using nn' mn np np' by clarsimp
      }
      ultimately have ?eq by blast
    }
    ultimately show ?eq by blast
  }
  {
    case (2 n0 n1)
    then have np: "isnpolyh ?cnp n0"
      and np': "isnpolyh ?cnp' n1"
      and m: "m \<le> min n0 n1"
      by simp_all
    then have mn: "m \<le> n" by simp
    let ?c0p = "CN 0\<^sub>p n (?cnp *\<^sub>p p')"
    {
      assume C: "?cnp *\<^sub>p c' +\<^sub>p ?c0p = 0\<^sub>p" "n' = n"
      then have nn: "\<not> n' < n \<and> \<not> n < n'"
        by simp
      from "4.hyps"(16-18) [of n n n]
        "4.hyps"(13-15)[of n "Suc n" n]
        np np' C(2) mn
      have norm:
        "isnpolyh ?cnp n"
        "isnpolyh c' (Suc n)"
        "isnpolyh (?cnp *\<^sub>p c') n"
        "isnpolyh p' n"
        "isnpolyh (?cnp *\<^sub>p p') n"
        "isnpolyh (CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n"
        "?cnp *\<^sub>p c' = 0\<^sub>p \<longleftrightarrow> c' = 0\<^sub>p"
        "?cnp *\<^sub>p p' \<noteq> 0\<^sub>p"
        "degreen (?cnp *\<^sub>p c') n = (if c' = 0\<^sub>p then 0 else degreen ?cnp n + degreen c' n)"
        "degreen (?cnp *\<^sub>p p') n = degreen ?cnp n + degreen p' n"
        by (simp_all add: min_def)
      from norm have cn: "isnpolyh (CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n"
        by simp
      have degneq: "degreen (?cnp *\<^sub>p c') n < degreen (CN 0\<^sub>p n (?cnp *\<^sub>p p')) n"
        using norm by simp
      from polyadd_eq_const_degreen[OF norm(3) cn C(1), where m="n"] degneq
      have False by simp
    }
    then show ?case using "4.hyps" by clarsimp
  }
qed auto

lemma polymul[simp]:
fixes p::"'a::field poly"
shows "Ipoly bs (p *\<^sub>p q) = Ipoly bs p * Ipoly bs q"
  by (induct p q rule: polymul.induct) (auto simp add: field_simps)

lemma polymul_normh:
  fixes p::"'a::field poly"
  shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> isnpolyh (p *\<^sub>p q) (min n0 n1)"
  using polymul_properties(1) by blast

lemma polymul_eq0_iff:
  fixes p::"'a::field poly"
  shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> p *\<^sub>p q = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p \<or> q = 0\<^sub>p"
  using polymul_properties(2) by blast

lemma polymul_degreen:
  fixes p::"'a::field poly"
  shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> m \<le> min n0 n1 \<Longrightarrow>
    degreen (p *\<^sub>p q) m = (if p = 0\<^sub>p \<or> q = 0\<^sub>p then 0 else degreen p m + degreen q m)"
  by (fact polymul_properties(3))

lemma polymul_norm:
  fixes p::"'a::field poly"
  shows "isnpoly p \<Longrightarrow> isnpoly q \<Longrightarrow> isnpoly (polymul p q)"
  using polymul_normh[of "p" "0" "q" "0"] by (simp add: isnpoly_def)

lemma headconst_zero: 
  fixes p::"'a::zero poly"
  shows "isnpolyh p n0 \<Longrightarrow> headconst p = 0 \<longleftrightarrow> p = 0\<^sub>p"
  by (induct p arbitrary: n0 rule: headconst.induct) auto

(*lemma headconst_isnormNum: "isnpolyh p n0 \<Longrightarrow> isnormNum (headconst p)"
  by (induct p arbitrary: n0) auto

lemma monic_eqI:
  assumes np: "isnpolyh p n0"
  shows "INum (headconst p) * Ipoly bs (fst (monic p)) =
    (Ipoly bs p ::'a::{field_char_0,field, power})"
  unfolding monic_def Let_def
proof (cases "headconst p = 0\<^sub>N", simp_all add: headconst_zero[OF np])
  let ?h = "headconst p"
  assume pz: "p \<noteq> 0\<^sub>p"
  {
    assume hz: "INum ?h = (0::'a)"
    from headconst_isnormNum[OF np] have norm: "isnormNum ?h" "isnormNum 0\<^sub>N"
      by simp_all
    from isnormNum_unique[where ?'a = 'a, OF norm] hz have "?h = 0\<^sub>N"
      by simp
    with headconst_zero[OF np] have "p = 0\<^sub>p"
      by blast
    with pz have False
      by blast
  }
  then show "INum (headconst p) = (0::'a) \<longrightarrow> \<lparr>p\<rparr>\<^sub>p\<^bsup>bs\<^esup> = 0"
    by blast
qed*)


text \<open>polyneg is a negation and preserves normal forms\<close>

lemma polyneg[simp]:
fixes p::"'a::ring_1 poly"
shows "Ipoly bs (polyneg p) = - Ipoly bs p"
  by (induct p rule: polyneg.induct) auto

lemma polyneg0:
fixes p::"'a::ring_1 poly"
shows "isnpolyh p n \<Longrightarrow> (~\<^sub>p p) = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p"
  by (induct p arbitrary: n rule: polyneg.induct) auto

lemma polyneg_polyneg:
fixes p::"'a::ring_1 poly"
shows "isnpolyh p n0 \<Longrightarrow> ~\<^sub>p (~\<^sub>p p) = p"
  by (induct p arbitrary: n0 rule: polyneg.induct) auto

lemma polyneg_normh:
fixes p::"'a::ring_1 poly"
shows "isnpolyh p n \<Longrightarrow> isnpolyh (polyneg p) n"
  by (induct p arbitrary: n rule: polyneg.induct) (auto simp add: polyneg0)

lemma polyneg_norm:
fixes p::"'a::ring_1 poly"
shows "isnpoly p \<Longrightarrow> isnpoly (polyneg p)"
  using polyneg_normh by (simp add: isnpoly_def)


text \<open>polysub is a substraction and preserves normal forms\<close>

lemma polysub[simp]:
fixes p::"'a::ring_1 poly"
shows "Ipoly bs (polysub p q) = Ipoly bs p - Ipoly bs q"
  by (simp add: polysub_def)

lemma polysub_normh:
fixes p::"'a::ring_1 poly"
shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> isnpolyh (polysub p q) (min n0 n1)"
  by (simp add: polysub_def polyneg_normh polyadd_normh)

lemma polysub_norm:
fixes p::"'a::ring_1 poly"
shows "isnpoly p \<Longrightarrow> isnpoly q \<Longrightarrow> isnpoly (polysub p q)"
  proof-
    assume "isnpoly p" "isnpoly q"
    from polyadd_norm[OF _ polyneg_norm, OF this]
    have "isnpoly (p +\<^sub>p ~\<^sub>p q)" .
    thus "isnpoly (polysub p q)"
      by (simp add: polysub_def)
  qed

lemma polysub_same_0[simp]:
  fixes p::"'a::ring_1 poly"
  shows "isnpolyh p n0 \<Longrightarrow> polysub p p = 0\<^sub>p"
  unfolding polysub_def split_def fst_conv snd_conv
  by (induct p arbitrary: n0) (auto simp add: Let_def Nsub0[simplified Nsub_def])

lemma polysub_0:
  fixes p::"'a::ring_1 poly"
  shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> p -\<^sub>p q = 0\<^sub>p \<longleftrightarrow> p = q"
  unfolding polysub_def split_def fst_conv snd_conv
  by (induct p q arbitrary: n0 n1 rule:polyadd.induct)
    (auto simp: Nsub0[simplified Nsub_def] Let_def)

text \<open>polypow is a power function and preserves normal forms\<close>

lemma polypow[simp]:
  "Ipoly bs (polypow n p) = (Ipoly bs p :: 'a::field) ^ n"
proof (induct n rule: polypow.induct)
  case 1
  then show ?case
    by simp
next
  fix n assume hyp: "\<And>x. Ipoly bs (p ^\<^sub>p Suc n div 2) = Ipoly bs p ^ (Suc n div 2)" 
  let ?q = "polypow ((Suc n) div 2) p"
  let ?d = "polymul ?q ?q"
  have "odd (Suc n) \<or> even (Suc n)"
    by simp
  moreover
  {
    assume odd: "odd (Suc n)"
    have th: "(Suc (Suc (Suc 0) * (Suc n div Suc (Suc 0)))) = Suc n div 2 + Suc n div 2 + 1"
      by arith
    from odd have "Ipoly bs (p ^\<^sub>p Suc n) = Ipoly bs (polymul p ?d)"
      by (simp add: Let_def)
    also have "\<dots> = (Ipoly bs p) * (Ipoly bs p)^(Suc n div 2) * (Ipoly bs p)^(Suc n div 2)"
      using hyp by simp
    also have "\<dots> = (Ipoly bs p) ^ (Suc n div 2 + Suc n div 2 + 1)"
      by (simp only: power_add power_one_right) simp
    also have "\<dots> = (Ipoly bs p) ^ (Suc (Suc (Suc 0) * (Suc n div Suc (Suc 0))))"
      by (simp only: th)
    finally have "Ipoly bs (p ^\<^sub>p Suc n) = Ipoly bs p ^ Suc n" unfolding numeral_2_eq_2 [symmetric]
    using odd_two_times_div_two_nat [OF odd] by simp
  }
  moreover
  {
    assume even: "even (Suc n)"
    from even have "Ipoly bs (p ^\<^sub>p Suc n) = Ipoly bs ?d"
      by (simp add: Let_def)
    also have "\<dots> = (Ipoly bs p) ^ (2 * (Suc n div 2))"
      using hyp by (simp only: mult_2 power_add) simp
    finally have "Ipoly bs (p ^\<^sub>p Suc n) = Ipoly bs p ^ Suc n" using even_two_times_div_two [OF even]
      by simp
  }
  ultimately show "Ipoly bs (p ^\<^sub>p Suc n) = Ipoly bs p ^ Suc n" by blast
qed

lemma polypow_normh:
  fixes p :: "'a::field poly"
  shows "isnpolyh p n \<Longrightarrow> isnpolyh (polypow k p) n"
proof (induct k arbitrary: n rule: polypow.induct)
  case 1
  then show ?case by auto
next
  fix k n assume hyps: "(\<And>x n. isnpolyh p n \<Longrightarrow> isnpolyh (p ^\<^sub>p Suc k div 2) n)" "isnpolyh p n"
  let ?q = "polypow (Suc k div 2) p"
  let ?d = "polymul ?q ?q"
  from hyps have th1: "isnpolyh ?q n" and th2: "isnpolyh p n"
    by blast+
  from polymul_normh[OF th1 th1] have dn: "isnpolyh ?d n"
    by simp
  from polymul_normh[OF th2 dn] have on: "isnpolyh (polymul p ?d) n"
    by simp
  from dn on show "isnpolyh (p ^\<^sub>p Suc k) n" by (simp, unfold Let_def) auto
qed

lemma polypow_norm:
  fixes p :: "'a::field poly"
  shows "isnpoly p \<Longrightarrow> isnpoly (polypow k p)"
  by (simp add: polypow_normh isnpoly_def)

text \<open>Finally the whole normalization\<close>

lemma polynate [simp]:
  "Ipoly bs (polynate p) = (Ipoly bs p :: 'a ::field)"
  by (induct p rule: polynate.induct) auto

lemma polynate_norm[simp]:
  fixes p :: "'a::field poly"
  shows "isnpoly (polynate p)"
  by (induct p rule: polynate.induct)
     (simp_all add: polyadd_norm polymul_norm polysub_norm polyneg_norm polypow_norm,
      simp_all add: isnpoly_def)

text \<open>shift1\<close>


lemma shift1:
  fixes p :: "'a::ring_1 poly"
  shows "Ipoly bs (shift1 p) = Ipoly bs (Mul (Bound 0) p)"
  by (simp add: shift1_def)

lemma shift1_isnpoly:
  assumes "isnpoly p"
    and "p \<noteq> 0\<^sub>p"
  shows "isnpoly (shift1 p) "
  using assms by (simp add: shift1_def isnpoly_def)

lemma shift1_nz[simp]:"shift1 p \<noteq> 0\<^sub>p"
  by (simp add: shift1_def)

lemma funpow_shift1_isnpoly: "isnpoly p \<Longrightarrow> p \<noteq> 0\<^sub>p \<Longrightarrow> isnpoly (funpow n shift1 p)"
  by (induct n arbitrary: p) (auto simp add: shift1_isnpoly funpow_swap1)

lemma funpow_isnpolyh:
  assumes "\<And>p. isnpolyh p n \<Longrightarrow> isnpolyh (f p) n"
    and "isnpolyh p n"
  shows "isnpolyh (funpow k f p) n"
  using assms by (induct k arbitrary: p) auto

lemma funpow_shift1:
  "(Ipoly bs (funpow n shift1 p) :: 'a :: comm_ring_1) =
    Ipoly bs (Mul (Pw (Bound 0) n) p)"
  by (induct n arbitrary: p) (simp_all add: shift1_isnpoly shift1)

lemma shift1_isnpolyh: "isnpolyh p n0 \<Longrightarrow> p \<noteq> 0\<^sub>p \<Longrightarrow> isnpolyh (shift1 p) 0"
  using isnpolyh_mono[where n="n0" and n'="0" and p="p"] by (simp add: shift1_def)

lemma funpow_shift1_1:
  "(Ipoly bs (funpow n shift1 p) :: 'a :: field) =
    Ipoly bs (funpow n shift1 (1)\<^sub>p *\<^sub>p p)"
  by (simp add: funpow_shift1)

lemma poly_cmul[simp]:
  fixes p :: "'a::comm_ring_1 poly"
  shows "Ipoly bs (poly_cmul c p) = Ipoly bs (Mul (C c) p)"
  by (induct p, simp_all add: field_simps)

lemma behead:
  assumes "isnpolyh p n"
  shows "Ipoly bs (Add (Mul (head p) (Pw (Bound 0) (degree p))) (behead p)) =
    (Ipoly bs p :: 'a :: comm_ring_1)"
  using assms
proof (induct p arbitrary: n rule: behead.induct)
  case (1 c p n)
  then have pn: "isnpolyh p n" by simp
  from 1(1)[OF pn]
  have th:"Ipoly bs (Add (Mul (head p) (Pw (Bound 0) (degree p))) (behead p)) = Ipoly bs p" .
  then show ?case using "1.hyps"
    apply (simp add: Let_def,cases "behead p = 0\<^sub>p")
    apply (simp_all add: th[symmetric] field_simps)
    done
qed (auto simp add: Let_def)

lemma behead_isnpolyh:
  assumes "isnpolyh p n"
  shows "isnpolyh (behead p) n"
  using assms by (induct p rule: behead.induct) (auto simp add: Let_def isnpolyh_mono)


subsection \<open>Miscellaneous lemmas about indexes, decrementation, substitution  etc ...\<close>

lemma isnpolyh_polybound0: "isnpolyh p (Suc n) \<Longrightarrow> polybound0 p"
proof (induct p arbitrary: n rule: poly.induct, auto, goal_cases)
  case prems: (1 c n p n')
  then have "n = Suc (n - 1)"
    by simp
  then have "isnpolyh p (Suc (n - 1))"
    using \<open>isnpolyh p n\<close> by simp
  with prems(2) show ?case
    by simp
qed

lemma isconstant_polybound0: "isnpolyh p n0 \<Longrightarrow> isconstant p \<longleftrightarrow> polybound0 p"
  by (induct p arbitrary: n0 rule: isconstant.induct) (auto simp add: isnpolyh_polybound0)

lemma decrpoly_zero[simp]: "decrpoly p = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p"
  by (induct p) auto

lemma decrpoly_normh: "isnpolyh p n0 \<Longrightarrow> polybound0 p \<Longrightarrow> isnpolyh (decrpoly p) (n0 - 1)"
  apply (induct p arbitrary: n0)
  apply auto
  apply atomize
  apply (rename_tac nat a b, erule_tac x = "Suc nat" in allE)
  apply auto
  done

lemma head_polybound0: "isnpolyh p n0 \<Longrightarrow> polybound0 (head p)"
  by (induct p  arbitrary: n0 rule: head.induct) (auto intro: isnpolyh_polybound0)

lemma polybound0_I:
  assumes "polybound0 a"
  shows "Ipoly (b # bs) a = Ipoly (b' # bs) a"
  using assms by (induct a rule: poly.induct) auto

lemma polysubst0_I: "Ipoly (b # bs) (polysubst0 a t) = Ipoly ((Ipoly (b # bs) a) # bs) t"
  by (induct t) simp_all

lemma polysubst0_I':
  assumes "polybound0 a"
  shows "Ipoly (b # bs) (polysubst0 a t) = Ipoly ((Ipoly (b' # bs) a) # bs) t"
  by (induct t) (simp_all add: polybound0_I[OF assms, where b="b" and b'="b'"])

lemma decrpoly:
  assumes "polybound0 t"
  shows "Ipoly (x # bs) t = Ipoly bs (decrpoly t)"
  using assms by (induct t rule: decrpoly.induct) simp_all

lemma polysubst0_polybound0:
  assumes "polybound0 t"
  shows "polybound0 (polysubst0 t a)"
  using assms by (induct a rule: poly.induct) auto

lemma degree0_polybound0: "isnpolyh p n \<Longrightarrow> degree p = 0 \<Longrightarrow> polybound0 p"
  by (induct p arbitrary: n rule: degree.induct) (auto simp add: isnpolyh_polybound0)

primrec maxindex :: "'a poly \<Rightarrow> nat"
where
  "maxindex (Bound n) = n + 1"
| "maxindex (CN c n p) = max  (n + 1) (max (maxindex c) (maxindex p))"
| "maxindex (Add p q) = max (maxindex p) (maxindex q)"
| "maxindex (Sub p q) = max (maxindex p) (maxindex q)"
| "maxindex (Mul p q) = max (maxindex p) (maxindex q)"
| "maxindex (Neg p) = maxindex p"
| "maxindex (Pw p n) = maxindex p"
| "maxindex (C x) = 0"

definition wf_bs :: "'a list \<Rightarrow> 'a poly \<Rightarrow> bool"
  where "wf_bs bs p \<longleftrightarrow> length bs \<ge> maxindex p"

lemma wf_bs_coefficients: "wf_bs bs p \<Longrightarrow> \<forall>c \<in> set (coefficients p). wf_bs bs c"
proof (induct p rule: coefficients.induct)
  case (1 c p)
  show ?case
  proof
    fix x
    assume xc: "x \<in> set (coefficients (CN c 0 p))"
    then have "x = c \<or> x \<in> set (coefficients p)"
      by simp
    moreover
    {
      assume "x = c"
      then have "wf_bs bs x"
        using "1.prems" unfolding wf_bs_def by simp
    }
    moreover
    {
      assume H: "x \<in> set (coefficients p)"
      from "1.prems" have "wf_bs bs p"
        unfolding wf_bs_def by simp
      with "1.hyps" H have "wf_bs bs x"
        by blast
    }
    ultimately show "wf_bs bs x"
      by blast
  qed
qed simp_all

lemma maxindex_coefficients: "\<forall>c \<in> set (coefficients p). maxindex c \<le> maxindex p"
  by (induct p rule: coefficients.induct) auto

lemma wf_bs_I: "wf_bs bs p \<Longrightarrow> Ipoly (bs @ bs') p = Ipoly bs p"
  unfolding wf_bs_def by (induct p) (auto simp add: nth_append)

lemma take_maxindex_wf:
  assumes wf: "wf_bs bs p"
  shows "Ipoly (take (maxindex p) bs) p = Ipoly bs p"
proof -
  let ?ip = "maxindex p"
  let ?tbs = "take ?ip bs"
  from wf have "length ?tbs = ?ip"
    unfolding wf_bs_def by simp
  then have wf': "wf_bs ?tbs p"
    unfolding wf_bs_def by  simp
  have eq: "bs = ?tbs @ drop ?ip bs"
    by simp
  from wf_bs_I[OF wf', of "drop ?ip bs"] show ?thesis
    using eq by simp
qed

lemma decr_maxindex: "polybound0 p \<Longrightarrow> maxindex (decrpoly p) = maxindex p - 1"
  by (induct p) auto

lemma wf_bs_insensitive: "length bs = length bs' \<Longrightarrow> wf_bs bs p = wf_bs bs' p"
  unfolding wf_bs_def by simp

lemma wf_bs_insensitive': "wf_bs (x # bs) p = wf_bs (y # bs) p"
  unfolding wf_bs_def by simp

lemma wf_bs_coefficients': "\<forall>c \<in> set (coefficients p). wf_bs bs c \<Longrightarrow> wf_bs (x # bs) p"
  by (induct p rule: coefficients.induct) (auto simp add: wf_bs_def)

lemma coefficients_Nil[simp]: "coefficients p \<noteq> []"
  by (induct p rule: coefficients.induct) simp_all

lemma coefficients_head: "last (coefficients p) = head p"
  by (induct p rule: coefficients.induct) auto

lemma wf_bs_decrpoly: "wf_bs bs (decrpoly p) \<Longrightarrow> wf_bs (x # bs) p"
  unfolding wf_bs_def by (induct p rule: decrpoly.induct) auto

lemma length_le_list_ex: "length xs \<le> n \<Longrightarrow> \<exists>ys. length (xs @ ys) = n"
  apply (rule exI[where x="replicate (n - length xs) z" for z])
  apply simp
  done

lemma isnpolyh_Suc_const: "isnpolyh p (Suc n) \<Longrightarrow> isconstant p"
  apply (cases p)
  apply auto
  apply (rename_tac nat a, case_tac "nat")
  apply simp_all
  done

lemma wf_bs_polyadd: "wf_bs bs p \<and> wf_bs bs q \<longrightarrow> wf_bs bs (p +\<^sub>p q)"
  unfolding wf_bs_def by (induct p q rule: polyadd.induct) (auto simp add: Let_def)

lemma wf_bs_polyul: "wf_bs bs p \<Longrightarrow> wf_bs bs q \<Longrightarrow> wf_bs bs (p *\<^sub>p q)"
  unfolding wf_bs_def
  apply (induct p q arbitrary: bs rule: polymul.induct)
  apply (simp_all add: wf_bs_polyadd)
  apply clarsimp
  apply (rule wf_bs_polyadd[unfolded wf_bs_def, rule_format])
  apply auto
  done

lemma wf_bs_polyneg: "wf_bs bs p \<Longrightarrow> wf_bs bs (~\<^sub>p p)"
  unfolding wf_bs_def by (induct p rule: polyneg.induct) auto

lemma wf_bs_polysub: "wf_bs bs p \<Longrightarrow> wf_bs bs q \<Longrightarrow> wf_bs bs (p -\<^sub>p q)"
  unfolding polysub_def split_def fst_conv snd_conv
  using wf_bs_polyadd wf_bs_polyneg by blast


subsection \<open>Canonicity of polynomial representation, see lemma isnpolyh_unique\<close>

definition "polypoly bs p = map (Ipoly bs) (coefficients p)"
definition "polypoly' bs p = map (Ipoly bs \<circ> decrpoly) (coefficients p)"
definition "poly_nate bs p = map (Ipoly bs \<circ> decrpoly) (coefficients (polynate p))"

lemma coefficients_normh: "isnpolyh p n0 \<Longrightarrow> \<forall>q \<in> set (coefficients p). isnpolyh q n0"
proof (induct p arbitrary: n0 rule: coefficients.induct)
  case (1 c p n0)
  have cp: "isnpolyh (CN c 0 p) n0"
    by fact
  then have norm: "isnpolyh c 0" "isnpolyh p 0" "p \<noteq> 0\<^sub>p" "n0 = 0"
    by (auto simp add: isnpolyh_mono[where n'=0])
  from "1.hyps"[OF norm(2)] norm(1) norm(4) show ?case
    by simp
qed auto

lemma coefficients_isconst: "isnpolyh p n \<Longrightarrow> \<forall>q \<in> set (coefficients p). isconstant q"
  by (induct p arbitrary: n rule: coefficients.induct) (auto simp add: isnpolyh_Suc_const)

lemma polypoly_polypoly':
  assumes np: "isnpolyh p n0"
  shows "polypoly (x # bs) p = polypoly' bs p"
proof -
  let ?cf = "set (coefficients p)"
  from coefficients_normh[OF np] have cn_norm: "\<forall> q\<in> ?cf. isnpolyh q n0" .
  {
    fix q
    assume q: "q \<in> ?cf"
    from q cn_norm have th: "isnpolyh q n0"
      by blast
    from coefficients_isconst[OF np] q have "isconstant q"
      by blast
    with isconstant_polybound0[OF th] have "polybound0 q"
      by blast
  }
  then have "\<forall>q \<in> ?cf. polybound0 q" ..
  then have "\<forall>q \<in> ?cf. Ipoly (x # bs) q = Ipoly bs (decrpoly q)"
    using polybound0_I[where b=x and bs=bs and b'=y] decrpoly[where x=x and bs=bs]
    by auto
  then show ?thesis
    unfolding polypoly_def polypoly'_def by simp
qed

lemma polypoly_poly:
  assumes "isnpolyh p n0"
  shows "Ipoly (x # bs) p = poly (polypoly (x # bs) p) x"
  using assms
  by (induct p arbitrary: n0 bs rule: coefficients.induct) (auto simp add: polypoly_def)

lemma polypoly'_poly:
  assumes "isnpolyh p n0"
  shows "Ipoly (x # bs) p = poly (polypoly' bs p) x"
  using polypoly_poly[OF assms, simplified polypoly_polypoly'[OF assms]] .

lemma polypoly_poly_polybound0:
  assumes "isnpolyh p n0"
    and "polybound0 p"
  shows "polypoly bs p = [Ipoly bs p]"
  using assms
  unfolding polypoly_def
  apply (cases p)
  apply auto
  apply (rename_tac nat a, case_tac nat)
  apply auto
  done

lemma head_isnpolyh: "isnpolyh p n0 \<Longrightarrow> isnpolyh (head p) n0"
  by (induct p rule: head.induct) auto

lemma headn_nz[simp]: "isnpolyh p n0 \<Longrightarrow> headn p m = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p"
  by (cases p) auto

lemma head_eq_headn0: "head p = headn p 0"
  by (induct p rule: head.induct) simp_all

lemma head_nz[simp]: "isnpolyh p n0 \<Longrightarrow> head p = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p"
  by (simp add: head_eq_headn0)

lemma isnpolyh_zero_iff:
fixes p :: "'a::idom_char_0 poly"
  assumes nq: "isnpolyh p n0"
    and eq :"\<forall>bs. wf_bs bs p \<longrightarrow> Ipoly bs p = 0"
  shows "p = 0\<^sub>p"
  using nq eq
proof (induct "maxindex p" arbitrary: p n0 rule: less_induct)
  case less
  note np = \<open>isnpolyh p n0\<close> and zp = \<open>\<forall>bs. wf_bs bs p \<longrightarrow> Ipoly bs p = (0::'a)\<close>
  {
    assume nz: "maxindex p = 0"
    then obtain c where "p = C c"
      using np by (cases p) auto
    with zp np have "p = 0\<^sub>p"
      unfolding wf_bs_def by simp
  }
  moreover
  {
    assume nz: "maxindex p \<noteq> 0"
    let ?h = "head p"
    let ?hd = "decrpoly ?h"
    let ?ihd = "maxindex ?hd"
    from head_isnpolyh[OF np] head_polybound0[OF np]
    have h: "isnpolyh ?h n0" "polybound0 ?h"
      by simp_all
    then have nhd: "isnpolyh ?hd (n0 - 1)"
      using decrpoly_normh by blast

    from maxindex_coefficients[of p] coefficients_head[of p, symmetric]
    have mihn: "maxindex ?h \<le> maxindex p"
      by auto
    with decr_maxindex[OF h(2)] nz have ihd_lt_n: "?ihd < maxindex p"
      by auto
    {
      fix bs :: "'a list"
      assume bs: "wf_bs bs ?hd"
      let ?ts = "take ?ihd bs"
      let ?rs = "drop ?ihd bs"
      have ts: "wf_bs ?ts ?hd"
        using bs unfolding wf_bs_def by simp
      have bs_ts_eq: "?ts @ ?rs = bs"
        by simp
      from wf_bs_decrpoly[OF ts] have tsh: " \<forall>x. wf_bs (x # ?ts) ?h"
        by simp
      from ihd_lt_n have "\<forall>x. length (x # ?ts) \<le> maxindex p"
        by simp
      with length_le_list_ex obtain xs where xs: "length ((x # ?ts) @ xs) = maxindex p"
        by blast
      then have "\<forall>x. wf_bs ((x # ?ts) @ xs) p"
        unfolding wf_bs_def by simp
      with zp have "\<forall>x. Ipoly ((x # ?ts) @ xs) p = 0"
        by blast
      then have "\<forall>x. Ipoly (x # (?ts @ xs)) p = 0"
        by simp
      with polypoly_poly[OF np] polypoly_polypoly'[OF np]
      have "\<forall>x. poly (polypoly' (?ts @ xs) p) x = poly [] x"
        by simp
      then have "poly (polypoly' (?ts @ xs) p) = poly []"
        by auto
      then have "\<forall>c \<in> set (coefficients p). Ipoly (?ts @ xs) (decrpoly c) = 0"
        by (simp add: poly_zero polypoly'_def)
      with coefficients_head[of p, symmetric]
      have th0: "Ipoly (?ts @ xs) ?hd = 0"
        by simp
      from bs have wf'': "wf_bs ?ts ?hd"
        unfolding wf_bs_def by simp
      with th0 wf_bs_I[of ?ts ?hd xs] have "Ipoly ?ts ?hd = 0"
        by simp
      with wf'' wf_bs_I[of ?ts ?hd ?rs] bs_ts_eq have "Ipoly bs ?hd = 0"
        by simp
    }
    then have hdz: "\<forall>bs. wf_bs bs ?hd \<longrightarrow> Ipoly bs ?hd = (0::'a)"
      by blast
    from less(1)[OF ihd_lt_n nhd] hdz have "?hd = 0\<^sub>p"
      by blast
    then have "?h = 0\<^sub>p" by simp
    with head_nz[OF np] have "p = 0\<^sub>p" by simp
  }
  ultimately show "p = 0\<^sub>p"
    by blast
qed

lemma isnpolyh_unique:
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
  shows "(\<forall>bs. Ipoly bs p = (Ipoly bs q :: 'a::idom_char_0)) \<longleftrightarrow> p = q"
proof auto
  assume H: "\<forall>bs. (Ipoly bs p ::'a) = Ipoly bs q"
  then have "\<forall>bs. Ipoly bs (p -\<^sub>p q) = (0::'a)"
    by simp
  then have "\<forall>bs. wf_bs bs (p -\<^sub>p q) \<longrightarrow> Ipoly bs (p -\<^sub>p q) = (0::'a)"
    using wf_bs_polysub[where p=p and q=q] by auto
  with isnpolyh_zero_iff[OF polysub_normh[OF np nq]] polysub_0[OF np nq] show "p = q"
    by blast
qed


text \<open>consequences of unicity on the algorithms for polynomial normalization\<close>

lemma polyadd_commute:
  fixes p :: "'a::idom_char_0 poly"
  assumes np: "isnpolyh p n0"
      and nq: "isnpolyh q n1"
  shows "p +\<^sub>p q = q +\<^sub>p p"
  using isnpolyh_unique[OF polyadd_normh[OF np nq] polyadd_normh[OF nq np]]
  by simp

lemma zero_normh: "isnpolyh 0\<^sub>p n"
  by simp

lemma one_normh: "isnpolyh (1)\<^sub>p n"
  by simp

lemma polyadd_0[simp]:
  fixes p :: "'a::idom_char_0 poly"
  assumes np: "isnpolyh p n0"
  shows "p +\<^sub>p 0\<^sub>p = p"
    and "0\<^sub>p +\<^sub>p p = p"
  using isnpolyh_unique[OF polyadd_normh[OF np zero_normh] np]
    isnpolyh_unique[OF polyadd_normh[OF zero_normh np] np] by simp_all

lemma polymul_1[simp]:
  fixes p :: "'a::field_char_0 poly"
  assumes np: "isnpolyh p n0"
  shows "p *\<^sub>p (1)\<^sub>p = p"
    and "(1)\<^sub>p *\<^sub>p p = p"
  using isnpolyh_unique[OF polymul_normh[OF np one_normh] np]
    isnpolyh_unique[OF polymul_normh[OF one_normh np] np] by simp_all

lemma polymul_0[simp]:
  fixes p :: "'a::field_char_0 poly"
  assumes np: "isnpolyh p n0"
  shows "p *\<^sub>p 0\<^sub>p = 0\<^sub>p"
    and "0\<^sub>p *\<^sub>p p = 0\<^sub>p"
  using isnpolyh_unique[OF polymul_normh[OF np zero_normh] zero_normh]
    isnpolyh_unique[OF polymul_normh[OF zero_normh np] zero_normh] by simp_all

lemma polymul_commute:
  fixes p :: "'a::field_char_0 poly"
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
  shows "p *\<^sub>p q = q *\<^sub>p p"
  using isnpolyh_unique[OF polymul_normh[OF np nq] polymul_normh[OF nq np]]
  by simp

declare polyneg_polyneg [simp]

lemma isnpolyh_polynate_id [simp]:
  fixes p :: "'a::field_char_0 poly"
  assumes np: "isnpolyh p n0"
  shows "polynate p = p"
  using isnpolyh_unique[OF polynate_norm[of p, unfolded isnpoly_def] np]
    polynate
  by simp

lemma polynate_idempotent[simp]:
  fixes p :: "'a::field_char_0 poly"
  shows "polynate (polynate p) = polynate p"
  using isnpolyh_polynate_id[OF polynate_norm[of p, unfolded isnpoly_def]] .

lemma poly_nate_polypoly': "poly_nate bs p = polypoly' bs (polynate p)"
  unfolding poly_nate_def polypoly'_def ..

lemma poly_nate_poly:
  "poly (poly_nate bs p) = (\<lambda>x:: 'a ::field. Ipoly (x # bs) p)"
  using polypoly'_poly[OF polynate_norm[unfolded isnpoly_def], symmetric, of bs p]
  unfolding poly_nate_polypoly' by auto


subsection \<open>heads, degrees and all that\<close>

lemma degree_eq_degreen0: "degree p = degreen p 0"
  by (induct p rule: degree.induct) simp_all

lemma degree_polyneg:
  assumes "isnpolyh p n"
  shows "degree (polyneg p) = degree p"
  apply (induct p rule: polyneg.induct)
  using assms
  apply simp_all
  apply (case_tac na)
  apply auto
  done

lemma degree_polyadd:
  fixes p::"'a::{plus,zero} poly"
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
  shows "degree (p +\<^sub>p q) \<le> max (degree p) (degree q)"
  using degreen_polyadd[OF np nq, where m= "0"] by (simp add: degree_eq_degreen0)


lemma degree_polysub:
  fixes p::"'a::ring_1 poly"
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
  shows "degree (p -\<^sub>p q) \<le> max (degree p) (degree q)"
proof-
  from polyneg_normh[OF nq] have nq': "isnpolyh (~\<^sub>p q) n1" .
  from degree_polyadd[OF np nq'] show ?thesis
    by (simp add: polysub_def degree_polyneg[OF nq])
qed

lemma degree_polysub_samehead:
  fixes p::"'a::ring_1 poly"
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
    and h: "head p = head q"
    and d: "degree p = degree q"
  shows "degree (p -\<^sub>p q) < degree p \<or> (p -\<^sub>p q = 0\<^sub>p)"
  unfolding polysub_def split_def fst_conv snd_conv
  using np nq h d
proof (induct p q rule: polyadd.induct)
  case (1 c c')
  then show ?case
    by (simp add: Nsub_def Nsub0[simplified Nsub_def])
next
  case (2 c c' n' p')
  from 2 have "degree (C c) = degree (CN c' n' p')"
    by simp
  then have nz: "n' > 0"
    by (cases n') auto
  then have "head (CN c' n' p') = CN c' n' p'"
    by (cases n') auto
  with 2 show ?case
    by simp
next
  case (3 c n p c')
  then have "degree (C c') = degree (CN c n p)"
    by simp
  then have nz: "n > 0"
    by (cases n) auto
  then have "head (CN c n p) = CN c n p"
    by (cases n) auto
  with 3 show ?case by simp
next
  case (4 c n p c' n' p')
  then have H:
    "isnpolyh (CN c n p) n0"
    "isnpolyh (CN c' n' p') n1"
    "head (CN c n p) = head (CN c' n' p')"
    "degree (CN c n p) = degree (CN c' n' p')"
    by simp_all
  then have degc: "degree c = 0" and degc': "degree c' = 0"
    by simp_all
  have degnc: "degree (~\<^sub>p c) = 0" and degnc': "degree (~\<^sub>p c') = 0"
    using H(1-2) degc by (auto simp: degree_polyneg)
  from H have cnh: "isnpolyh c (Suc n)" and c'nh: "isnpolyh c' (Suc n')"
    by simp_all
  from degree_polysub[OF cnh c'nh, simplified polysub_def] degc degc'
  have degcmc': "degree (c +\<^sub>p  ~\<^sub>pc') = 0"
    by simp
  from H have pnh: "isnpolyh p n" and p'nh: "isnpolyh p' n'"
    by auto
  have "n = n' \<or> n < n' \<or> n > n'"
    by arith
  moreover
  {
    assume nn': "n = n'"
    have "n = 0 \<or> n > 0" by arith
    moreover
    {
      assume nz: "n = 0"
      then have ?case using 4 nn'
        by (auto simp add: Let_def degcmc')
    }
    moreover
    {
      assume nz: "n > 0"
      with nn' H(3) have  cc': "c = c'" and pp': "p = p'"
        by (cases n, auto)+
      then have ?case
        using polysub_same_0[OF p'nh, simplified polysub_def split_def fst_conv snd_conv]
        using polysub_same_0[OF c'nh, simplified polysub_def]
        using nn' 4 by (simp add: Let_def)
    }
    ultimately have ?case by blast
  }
  moreover
  {
    assume nn': "n < n'"
    then have n'p: "n' > 0"
      by simp
    then have headcnp':"head (CN c' n' p') = CN c' n' p'"
      by (cases n') simp_all
    have degcnp': "degree (CN c' n' p') = 0"
      and degcnpeq: "degree (CN c n p) = degree (CN c' n' p')"
      using 4 nn' by (cases n', simp_all)
    then have "n > 0"
      by (cases n) simp_all
    then have headcnp: "head (CN c n p) = CN c n p"
      by (cases n) auto
    from H(3) headcnp headcnp' nn' have ?case
      by auto
  }
  moreover
  {
    assume nn': "n > n'"
    then have np: "n > 0" by simp
    then have headcnp:"head (CN c n p) = CN c n p"
      by (cases n) simp_all
    from 4 have degcnpeq: "degree (CN c' n' p') = degree (CN c n p)"
      by simp
    from np have degcnp: "degree (CN c n p) = 0"
      by (cases n) simp_all
    with degcnpeq have "n' > 0"
      by (cases n') simp_all
    then have headcnp': "head (CN c' n' p') = CN c' n' p'"
      by (cases n') auto
    from H(3) headcnp headcnp' nn' have ?case by auto
  }
  ultimately show ?case by blast
qed auto

lemma shift1_head : "isnpolyh p n0 \<Longrightarrow> head (shift1 p) = head p"
  by (induct p arbitrary: n0 rule: head.induct) (simp_all add: shift1_def)

lemma funpow_shift1_head: "isnpolyh p n0 \<Longrightarrow> p\<noteq> 0\<^sub>p \<Longrightarrow> head (funpow k shift1 p) = head p"
proof (induct k arbitrary: n0 p)
  case 0
  then show ?case
    by auto
next
  case (Suc k n0 p)
  then have "isnpolyh (shift1 p) 0"
    by (simp add: shift1_isnpolyh)
  with Suc have "head (funpow k shift1 (shift1 p)) = head (shift1 p)"
    and "head (shift1 p) = head p"
    by (simp_all add: shift1_head)
  then show ?case
    by (simp add: funpow_swap1)
qed

lemma shift1_degree: "degree (shift1 p) = 1 + degree p"
  by (simp add: shift1_def)

lemma funpow_shift1_degree: "degree (funpow k shift1 p) = k + degree p "
  by (induct k arbitrary: p) (auto simp add: shift1_degree)

lemma funpow_shift1_nz: "p \<noteq> 0\<^sub>p \<Longrightarrow> funpow n shift1 p \<noteq> 0\<^sub>p"
  by (induct n arbitrary: p) simp_all

lemma head_isnpolyh_Suc[simp]: "isnpolyh p (Suc n) \<Longrightarrow> head p = p"
  by (induct p arbitrary: n rule: degree.induct) auto
lemma headn_0[simp]: "isnpolyh p n \<Longrightarrow> m < n \<Longrightarrow> headn p m = p"
  by (induct p arbitrary: n rule: degreen.induct) auto
lemma head_isnpolyh_Suc': "n > 0 \<Longrightarrow> isnpolyh p n \<Longrightarrow> head p = p"
  by (induct p arbitrary: n rule: degree.induct) auto
lemma head_head[simp]: "isnpolyh p n0 \<Longrightarrow> head (head p) = head p"
  by (induct p rule: head.induct) auto

lemma polyadd_eq_const_degree:
  "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> polyadd p q = C c \<Longrightarrow> degree p = degree q"
  using polyadd_eq_const_degreen by (simp add: degree_eq_degreen0)

lemma polyadd_head:
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
    and deg: "degree p \<noteq> degree q"
  shows "head (p +\<^sub>p q) = (if degree p < degree q then head q else head p)"
  using np nq deg
  apply (induct p q arbitrary: n0 n1 rule: polyadd.induct)
  apply simp_all
  apply (case_tac n', simp, simp)
  apply (case_tac n, simp, simp)
  apply (case_tac n, case_tac n', simp add: Let_def)
  apply (auto simp add: polyadd_eq_const_degree)[2]
  apply (metis head_nz)
  apply (metis head_nz)
  apply (metis degree.simps(9) gr0_conv_Suc head.simps(1) less_Suc0 not_less_eq)
  done

lemma polymul_head_polyeq:
  fixes p :: "'a::field poly"
  shows "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> p \<noteq> 0\<^sub>p \<Longrightarrow> q \<noteq> 0\<^sub>p \<Longrightarrow> head (p *\<^sub>p q) = head p *\<^sub>p head q"
proof (induct p q arbitrary: n0 n1 rule: polymul.induct)
  case (2 c c' n' p' n0 n1)
  then have "isnpolyh (head (CN c' n' p')) n1"
    by (simp_all add: head_isnpolyh)
  then show ?case
    using 2 by (cases n') auto
next
  case (3 c n p c' n0 n1)
  then have "isnpolyh (head (CN c n p)) n0"
    by (simp_all add: head_isnpolyh)
  then show ?case
    using 3 by (cases n) auto
next
  case (4 c n p c' n' p' n0 n1)
  then have norm: "isnpolyh p n" "isnpolyh c (Suc n)" "isnpolyh p' n'" "isnpolyh c' (Suc n')"
    "isnpolyh (CN c n p) n" "isnpolyh (CN c' n' p') n'"
    by simp_all
  have "n < n' \<or> n' < n \<or> n = n'" by arith
  moreover
  {
    assume nn': "n < n'"
    then have ?case
      using norm "4.hyps"(2)[OF norm(1,6)] "4.hyps"(1)[OF norm(2,6)]
      apply simp
      apply (cases n)
      apply simp
      apply (cases n')
      apply simp_all
      done
  }
  moreover {
    assume nn': "n'< n"
    then have ?case
      using norm "4.hyps"(6) [OF norm(5,3)] "4.hyps"(5)[OF norm(5,4)]
      apply simp
      apply (cases n')
      apply simp
      apply (cases n)
      apply auto
      done
  }
  moreover
  {
    assume nn': "n' = n"
    from nn' polymul_normh[OF norm(5,4)]
    have ncnpc':"isnpolyh (CN c n p *\<^sub>p c') n" by (simp add: min_def)
    from nn' polymul_normh[OF norm(5,3)] norm
    have ncnpp':"isnpolyh (CN c n p *\<^sub>p p') n" by simp
    from nn' ncnpp' polymul_eq0_iff[OF norm(5,3)] norm(6)
    have ncnpp0':"isnpolyh (CN 0\<^sub>p n (CN c n p *\<^sub>p p')) n" by simp
    from polyadd_normh[OF ncnpc' ncnpp0']
    have nth: "isnpolyh ((CN c n p *\<^sub>p c') +\<^sub>p (CN 0\<^sub>p n (CN c n p *\<^sub>p p'))) n"
      by (simp add: min_def)
    {
      assume np: "n > 0"
      with nn' head_isnpolyh_Suc'[OF np nth]
        head_isnpolyh_Suc'[OF np norm(5)] head_isnpolyh_Suc'[OF np norm(6)[simplified nn']]
      have ?case by simp
    }
    moreover
    {
      assume nz: "n = 0"
      from polymul_degreen[OF norm(5,4), where m="0"]
        polymul_degreen[OF norm(5,3), where m="0"] nn' nz degree_eq_degreen0
      norm(5,6) degree_npolyhCN[OF norm(6)]
    have dth: "degree (CN c 0 p *\<^sub>p c') < degree (CN 0\<^sub>p 0 (CN c 0 p *\<^sub>p p'))"
      by (smt "4.prems"(4) One_nat_def add_Suc add_less_imp_less_left comm_monoid_add_class.add_0 degree.simps(1) eq_imp_le gr_implies_not0 head.simps(1) head_nz min_0L norm(3) not_less_eq)
    then have dth': "degree (CN c 0 p *\<^sub>p c') \<noteq> degree (CN 0\<^sub>p 0 (CN c 0 p *\<^sub>p p'))"
      by simp
    from polyadd_head[OF ncnpc'[simplified nz] ncnpp0'[simplified nz] dth'] dth
    have ?case
      using norm "4.hyps"(6)[OF norm(5,3)] "4.hyps"(5)[OF norm(5,4)] nn' nz
      by simp
    }
    ultimately have ?case
      by (cases n) auto
  }
  ultimately show ?case by blast
qed simp_all

lemma degree_coefficients: "degree p = length (coefficients p) - 1"
  by (induct p rule: degree.induct) auto

lemma degree_head[simp]: "degree (head p) = 0"
  by (induct p rule: head.induct) auto

lemma degree_CN: "isnpolyh p n \<Longrightarrow> degree (CN c n p) \<le> 1 + degree p"
  by (cases n) simp_all

lemma degree_CN': "isnpolyh p n \<Longrightarrow> degree (CN c n p) \<ge>  degree p"
  by (cases n) simp_all

lemma polyadd_different_degree:
  "isnpolyh p n0 \<Longrightarrow> isnpolyh q n1 \<Longrightarrow> degree p \<noteq> degree q \<Longrightarrow>
    degree (polyadd p q) = max (degree p) (degree q)"
  by (simp add: degree_eq_degreen0 polyadd_different_degreen)

lemma degreen_polyneg: "isnpolyh p n0 \<Longrightarrow> degreen (~\<^sub>p p) m = degreen p m"
  by (induct p arbitrary: n0 rule: polyneg.induct) auto

lemma degree_polymul:
  fixes p :: "'a::field poly"
  assumes np: "isnpolyh p n0"
    and nq: "isnpolyh q n1"
  shows "degree (p *\<^sub>p q) \<le> degree p + degree q"
  using polymul_degreen[OF np nq, where m="0"]
  by (simp add: degree_eq_degreen0)

lemma polyneg_degree: "isnpolyh p n \<Longrightarrow> degree (polyneg p) = degree p"
  by (induct p arbitrary: n rule: degree.induct) auto

lemma polyneg_head: "isnpolyh p n \<Longrightarrow> head (polyneg p) = polyneg (head p)"
  by (induct p arbitrary: n rule: degree.induct) auto


subsection \<open>Correctness of polynomial pseudo division\<close>

(*lemma polydivide_aux_properties:
  fixes p :: "'a::field poly"
  assumes np: "isnpolyh p n0"
    and ns: "isnpolyh s n1"
    and ap: "head p = a"
    and ndp: "degree p = n"
    and pnz: "p \<noteq> 0\<^sub>p"
  shows "polydivide_aux a n p k s = (k', r) \<longrightarrow> k' \<ge> k \<and> (degree r = 0 \<or> degree r < degree p) \<and>
    (\<exists>nr. isnpolyh r nr) \<and> (\<exists>q n1. isnpolyh q n1 \<and> (polypow (k' - k) a) *\<^sub>p s = p *\<^sub>p q +\<^sub>p r)"
  using ns
proof (induct "degree s" arbitrary: s k k' r n1 rule: less_induct)
  case less
  let ?qths = "\<exists>q n1. isnpolyh q n1 \<and> (a ^\<^sub>p (k' - k) *\<^sub>p s = p *\<^sub>p q +\<^sub>p r)"
  let ?ths = "polydivide_aux a n p k s = (k', r) \<longrightarrow>  k \<le> k' \<and>
    (degree r = 0 \<or> degree r < degree p) \<and> (\<exists>nr. isnpolyh r nr) \<and> ?qths"
  let ?b = "head s"
  let ?p' = "funpow (degree s - n) shift1 p"
  let ?xdn = "funpow (degree s - n) shift1 (1)\<^sub>p"
  let ?akk' = "a ^\<^sub>p (k' - k)"
  note ns = \<open>isnpolyh s n1\<close>
  from np have np0: "isnpolyh p 0"
    using isnpolyh_mono[where n="n0" and n'="0" and p="p"] by simp
  have np': "isnpolyh ?p' 0"
    using funpow_shift1_isnpoly[OF np0[simplified isnpoly_def[symmetric]] pnz, where n="degree s - n"]
    by (simp add: isnpoly_def)
  have headp': "head ?p' = head p"
    using funpow_shift1_head[OF np pnz] by simp
  from funpow_shift1_isnpoly[where p="(1)\<^sub>p"] have nxdn: "isnpolyh ?xdn 0"
    (*by (simp add: isnpoly_def)*)
    sorry
  from polypow_normh [OF head_isnpolyh[OF np0], where k="k' - k"] ap
  have nakk':"isnpolyh ?akk' 0" by blast
  {
    assume sz: "s = 0\<^sub>p"
    then have ?ths
      using np polydivide_aux.simps
      apply clarsimp
      apply (rule exI[where x="0\<^sub>p"])
      apply simp
      done
  }
  moreover
  {
    assume sz: "s \<noteq> 0\<^sub>p"
    {
      assume dn: "degree s < n"
      then have "?ths"
        using ns ndp np polydivide_aux.simps
        apply auto
        apply (rule exI[where x="0\<^sub>p"])
        apply simp
        done
    }
    moreover
    {
      assume dn': "\<not> degree s < n"
      then have dn: "degree s \<ge> n"
        by arith
      have degsp': "degree s = degree ?p'"
        using dn ndp funpow_shift1_degree[where k = "degree s - n" and p="p"]
        by simp
      {
        assume ba: "?b = a"
        then have headsp': "head s = head ?p'"
          using ap headp' by simp
        have nr: "isnpolyh (s -\<^sub>p ?p') 0"
          using polysub_normh[OF ns np'] by simp
        from degree_polysub_samehead[OF ns np' headsp' degsp']
        have "degree (s -\<^sub>p ?p') < degree s \<or> s -\<^sub>p ?p' = 0\<^sub>p"
          by simp
        moreover
        {
          assume deglt:"degree (s -\<^sub>p ?p') < degree s"
          from polydivide_aux.simps sz dn' ba
          have eq: "polydivide_aux a n p k s = polydivide_aux a n p k (s -\<^sub>p ?p')"
            by (simp add: Let_def)
          {
            assume h1: "polydivide_aux a n p k s = (k', r)"
            from less(1)[OF deglt nr, of k k' r] trans[OF eq[symmetric] h1]
            have kk': "k \<le> k'"
              and nr: "\<exists>nr. isnpolyh r nr"
              and dr: "degree r = 0 \<or> degree r < degree p"
              and q1: "\<exists>q nq. isnpolyh q nq \<and> a ^\<^sub>p k' - k *\<^sub>p (s -\<^sub>p ?p') = p *\<^sub>p q +\<^sub>p r"
              by auto
            from q1 obtain q n1 where nq: "isnpolyh q n1"
              and asp: "a^\<^sub>p (k' - k) *\<^sub>p (s -\<^sub>p ?p') = p *\<^sub>p q +\<^sub>p r"
              by blast
            from nr obtain nr where nr': "isnpolyh r nr"
              by blast
            from polymul_normh[OF nakk' ns] have nakks': "isnpolyh (a ^\<^sub>p (k' - k) *\<^sub>p s) 0"
              by simp
            from polyadd_normh[OF polymul_normh[OF nakk' nxdn] nq]
            have nq': "isnpolyh (?akk' *\<^sub>p ?xdn +\<^sub>p q) 0" by simp
            from polyadd_normh[OF polymul_normh[OF np
              polyadd_normh[OF polymul_normh[OF nakk' nxdn] nq]] nr']
            have nqr': "isnpolyh (p *\<^sub>p (?akk' *\<^sub>p ?xdn +\<^sub>p q) +\<^sub>p r) 0"
              by simp
            from asp have "\<forall>bs :: 'a::{field_char_0,field} list.
              Ipoly bs (a^\<^sub>p (k' - k) *\<^sub>p (s -\<^sub>p ?p')) = Ipoly bs (p *\<^sub>p q +\<^sub>p r)"
              by simp
            then have "\<forall>bs :: 'a::{field_char_0,field} list.
              Ipoly bs (a^\<^sub>p (k' - k)*\<^sub>p s) =
              Ipoly bs (a^\<^sub>p (k' - k)) * Ipoly bs ?p' + Ipoly bs p * Ipoly bs q + Ipoly bs r"
              by (simp add: field_simps)
            then have "\<forall>bs :: 'a::{field_char_0,field} list.
              Ipoly bs (a ^\<^sub>p (k' - k) *\<^sub>p s) =
              Ipoly bs (a^\<^sub>p (k' - k)) * Ipoly bs (funpow (degree s - n) shift1 (1)\<^sub>p *\<^sub>p p) +
              Ipoly bs p * Ipoly bs q + Ipoly bs r"
              by (auto simp only: funpow_shift1_1)
            then have "\<forall>bs:: 'a::{field_char_0,field} list.
              Ipoly bs (a ^\<^sub>p (k' - k) *\<^sub>p s) =
              Ipoly bs p * (Ipoly bs (a^\<^sub>p (k' - k)) * Ipoly bs (funpow (degree s - n) shift1 (1)\<^sub>p) +
              Ipoly bs q) + Ipoly bs r"
              by (simp add: field_simps)
            then have "\<forall>bs:: 'a::{field_char_0,field} list.
              Ipoly bs (a ^\<^sub>p (k' - k) *\<^sub>p s) =
              Ipoly bs (p *\<^sub>p ((a^\<^sub>p (k' - k)) *\<^sub>p (funpow (degree s - n) shift1 (1)\<^sub>p) +\<^sub>p q) +\<^sub>p r)"
              by simp
            with isnpolyh_unique[OF nakks' nqr']
            have "a ^\<^sub>p (k' - k) *\<^sub>p s =
              p *\<^sub>p ((a^\<^sub>p (k' - k)) *\<^sub>p (funpow (degree s - n) shift1 (1)\<^sub>p) +\<^sub>p q) +\<^sub>p r"
              by blast
            then have ?qths using nq'
              apply (rule_tac x="(a^\<^sub>p (k' - k)) *\<^sub>p (funpow (degree s - n) shift1 (1)\<^sub>p) +\<^sub>p q" in exI)
              apply (rule_tac x="0" in exI)
              apply simp
              done
            with kk' nr dr have "k \<le> k' \<and> (degree r = 0 \<or> degree r < degree p) \<and>
              (\<exists>nr. isnpolyh r nr) \<and> ?qths"
              by blast
          }
          then have ?ths by blast
        }
        moreover
        {
          assume spz:"s -\<^sub>p ?p' = 0\<^sub>p"
          from spz isnpolyh_unique[OF polysub_normh[OF ns np'], where q="0\<^sub>p", symmetric, where ?'a = "'a::{field_char_0,field}"]
          have "\<forall>bs:: 'a::{field_char_0,field} list. Ipoly bs s = Ipoly bs ?p'"
            by simp
          then have "\<forall>bs:: 'a::{field_char_0,field} list. Ipoly bs s = Ipoly bs (?xdn *\<^sub>p p)"
            using np nxdn
            apply simp
            apply (simp only: funpow_shift1_1)
            apply simp
            done
          then have sp': "s = ?xdn *\<^sub>p p"
            using isnpolyh_unique[OF ns polymul_normh[OF nxdn np]]
            by blast
          {
            assume h1: "polydivide_aux a n p k s = (k', r)"
            from polydivide_aux.simps sz dn' ba
            have eq: "polydivide_aux a n p k s = polydivide_aux a n p k (s -\<^sub>p ?p')"
              by (simp add: Let_def)
            also have "\<dots> = (k,0\<^sub>p)"
              using polydivide_aux.simps spz by simp
            finally have "(k', r) = (k, 0\<^sub>p)"
              using h1 by simp
            with sp'[symmetric] ns np nxdn polyadd_0(1)[OF polymul_normh[OF np nxdn]]
              polyadd_0(2)[OF polymul_normh[OF np nxdn]] have ?ths
              apply auto
              apply (rule exI[where x="?xdn"])
              apply (auto simp add: polymul_commute[of p])
              done
          }
        }
        ultimately have ?ths by blast
      }
      moreover
      {
        assume ba: "?b \<noteq> a"
        from polysub_normh[OF polymul_normh[OF head_isnpolyh[OF np0, simplified ap] ns]
          polymul_normh[OF head_isnpolyh[OF ns] np']]
        have nth: "isnpolyh ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p')) 0"
          by (simp add: min_def)
        have nzths: "a *\<^sub>p s \<noteq> 0\<^sub>p" "?b *\<^sub>p ?p' \<noteq> 0\<^sub>p"
          using polymul_eq0_iff[OF head_isnpolyh[OF np0, simplified ap] ns]
            polymul_eq0_iff[OF head_isnpolyh[OF ns] np']head_nz[OF np0] ap pnz sz head_nz[OF ns]
            funpow_shift1_nz[OF pnz]
          by simp_all
        from polymul_head_polyeq[OF head_isnpolyh[OF np] ns] head_nz[OF np] sz ap head_head[OF np] pnz
          polymul_head_polyeq[OF head_isnpolyh[OF ns] np'] head_nz [OF ns] sz funpow_shift1_nz[OF pnz, where n="degree s - n"]
        have hdth: "head (a *\<^sub>p s) = head (?b *\<^sub>p ?p')"
          using head_head[OF ns] funpow_shift1_head[OF np pnz]
            polymul_commute[OF head_isnpolyh[OF np] head_isnpolyh[OF ns]]
          by (simp add: ap)
        from polymul_degreen[OF head_isnpolyh[OF np] ns, where m="0"]
          head_nz[OF np] pnz sz ap[symmetric]
          funpow_shift1_nz[OF pnz, where n="degree s - n"]
          polymul_degreen[OF head_isnpolyh[OF ns] np', where m="0"] head_nz[OF ns]
          ndp dn
        have degth: "degree (a *\<^sub>p s) = degree (?b *\<^sub>p ?p')"
          by (simp add: degree_eq_degreen0[symmetric] funpow_shift1_degree)
        {
          assume dth: "degree ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p')) < degree s"
          from polysub_normh[OF polymul_normh[OF head_isnpolyh[OF np] ns]
            polymul_normh[OF head_isnpolyh[OF ns]np']] ap
          have nasbp': "isnpolyh ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p')) 0"
            by simp
          {
            assume h1:"polydivide_aux a n p k s = (k', r)"
            from h1 polydivide_aux.simps sz dn' ba
            have eq:"polydivide_aux a n p (Suc k) ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p')) = (k',r)"
              by (simp add: Let_def)
            with less(1)[OF dth nasbp', of "Suc k" k' r]
            obtain q nq nr where kk': "Suc k \<le> k'"
              and nr: "isnpolyh r nr"
              and nq: "isnpolyh q nq"
              and dr: "degree r = 0 \<or> degree r < degree p"
              and qr: "a ^\<^sub>p (k' - Suc k) *\<^sub>p ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p')) = p *\<^sub>p q +\<^sub>p r"
              by auto
            from kk' have kk'': "Suc (k' - Suc k) = k' - k"
              by arith
            {
              fix bs :: "'a::{field_char_0,field} list"
              from qr isnpolyh_unique[OF polypow_normh[OF head_isnpolyh[OF np], where k="k' - Suc k", simplified ap] nasbp', symmetric]
              have "Ipoly bs (a ^\<^sub>p (k' - Suc k) *\<^sub>p ((a *\<^sub>p s) -\<^sub>p (?b *\<^sub>p ?p'))) = Ipoly bs (p *\<^sub>p q +\<^sub>p r)"
                by simp
              then have "Ipoly bs a ^ (Suc (k' - Suc k)) * Ipoly bs s =
                Ipoly bs p * Ipoly bs q + Ipoly bs a ^ (k' - Suc k) * Ipoly bs ?b * Ipoly bs ?p' + Ipoly bs r"
                by (simp add: field_simps)
              then have "Ipoly bs a ^ (k' - k)  * Ipoly bs s =
                Ipoly bs p * Ipoly bs q + Ipoly bs a ^ (k' - Suc k) * Ipoly bs ?b * Ipoly bs ?xdn * Ipoly bs p + Ipoly bs r"
                by (simp add: kk'' funpow_shift1_1[where n="degree s - n" and p="p"])
              then have "Ipoly bs (a ^\<^sub>p (k' - k) *\<^sub>p s) =
                Ipoly bs p * (Ipoly bs q + Ipoly bs a ^ (k' - Suc k) * Ipoly bs ?b * Ipoly bs ?xdn) + Ipoly bs r"
                by (simp add: field_simps)
            }
            then have ieq:"\<forall>bs :: 'a::{field_char_0,field} list.
                Ipoly bs (a ^\<^sub>p (k' - k) *\<^sub>p s) =
                Ipoly bs (p *\<^sub>p (q +\<^sub>p (a ^\<^sub>p (k' - Suc k) *\<^sub>p ?b *\<^sub>p ?xdn)) +\<^sub>p r)"
              by auto
            let ?q = "q +\<^sub>p (a ^\<^sub>p (k' - Suc k) *\<^sub>p ?b *\<^sub>p ?xdn)"
            from polyadd_normh[OF nq polymul_normh[OF polymul_normh[OF polypow_normh[OF head_isnpolyh[OF np], where k="k' - Suc k"] head_isnpolyh[OF ns], simplified ap] nxdn]]
            have nqw: "isnpolyh ?q 0"
              by simp
            from ieq isnpolyh_unique[OF polymul_normh[OF polypow_normh[OF head_isnpolyh[OF np], where k="k' - k"] ns, simplified ap] polyadd_normh[OF polymul_normh[OF np nqw] nr]]
            have asth: "(a ^\<^sub>p (k' - k) *\<^sub>p s) = p *\<^sub>p (q +\<^sub>p (a ^\<^sub>p (k' - Suc k) *\<^sub>p ?b *\<^sub>p ?xdn)) +\<^sub>p r"
              by blast
            from dr kk' nr h1 asth nqw have ?ths
              apply simp
              apply (rule conjI)
              apply (rule exI[where x="nr"], simp)
              apply (rule exI[where x="(q +\<^sub>p (a ^\<^sub>p (k' - Suc k) *\<^sub>p ?b *\<^sub>p ?xdn))"], simp)
              apply (rule exI[where x="0"], simp)
              done
          }
          then have ?ths by blast
        }
        moreover
        {
          assume spz: "a *\<^sub>p s -\<^sub>p (?b *\<^sub>p ?p') = 0\<^sub>p"
          {
            fix bs :: "'a::{field_char_0,field} list"
            from isnpolyh_unique[OF nth, where ?'a="'a" and q="0\<^sub>p",simplified,symmetric] spz
            have "Ipoly bs (a*\<^sub>p s) = Ipoly bs ?b * Ipoly bs ?p'"
              by simp
            then have "Ipoly bs (a*\<^sub>p s) = Ipoly bs (?b *\<^sub>p ?xdn) * Ipoly bs p"
              by (simp add: funpow_shift1_1[where n="degree s - n" and p="p"])
            then have "Ipoly bs (a*\<^sub>p s) = Ipoly bs (p *\<^sub>p (?b *\<^sub>p ?xdn))"
              by simp
          }
          then have hth: "\<forall>bs :: 'a::{field_char_0,field} list.
            Ipoly bs (a *\<^sub>p s) = Ipoly bs (p *\<^sub>p (?b *\<^sub>p ?xdn))" ..
          from hth have asq: "a *\<^sub>p s = p *\<^sub>p (?b *\<^sub>p ?xdn)"
            using isnpolyh_unique[where ?'a = "'a::{field_char_0,field}", OF polymul_normh[OF head_isnpolyh[OF np] ns]
                    polymul_normh[OF np polymul_normh[OF head_isnpolyh[OF ns] nxdn]],
              simplified ap]
            by simp
          {
            assume h1: "polydivide_aux a n p k s = (k', r)"
            from h1 sz ba dn' spz polydivide_aux.simps polydivide_aux.simps
            have "(k', r) = (Suc k, 0\<^sub>p)"
              by (simp add: Let_def)
            with h1 np head_isnpolyh[OF np, simplified ap] ns polymul_normh[OF head_isnpolyh[OF ns] nxdn]
              polymul_normh[OF np polymul_normh[OF head_isnpolyh[OF ns] nxdn]] asq
            have ?ths
              apply (clarsimp simp add: Let_def)
              apply (rule exI[where x="?b *\<^sub>p ?xdn"])
              apply simp
              apply (rule exI[where x="0"], simp)
              done
          }
          then have ?ths by blast
        }
        ultimately have ?ths
          using degree_polysub_samehead[OF polymul_normh[OF head_isnpolyh[OF np0, simplified ap] ns] polymul_normh[OF head_isnpolyh[OF ns] np'] hdth degth] polymul_degreen[OF head_isnpolyh[OF np] ns, where m="0"]
            head_nz[OF np] pnz sz ap[symmetric]
          by (auto simp add: degree_eq_degreen0[symmetric])
      }
      ultimately have ?ths by blast
    }
    ultimately have ?ths by blast
  }
  ultimately show ?ths by blast
qed

lemma polydivide_properties:
  assumes "SORT_CONSTRAINT('a::{field_char_0,field})"
    and np: "isnpolyh p n0"
    and ns: "isnpolyh s n1"
    and pnz: "p \<noteq> 0\<^sub>p"
  shows "\<exists>k r. polydivide s p = (k, r) \<and>
    (\<exists>nr. isnpolyh r nr) \<and> (degree r = 0 \<or> degree r < degree p) \<and>
    (\<exists>q n1. isnpolyh q n1 \<and> polypow k (head p) *\<^sub>p s = p *\<^sub>p q +\<^sub>p r)"
proof -
  have trv: "head p = head p" "degree p = degree p"
    by simp_all
  from polydivide_def[where s="s" and p="p"] have ex: "\<exists> k r. polydivide s p = (k,r)"
    by auto
  then obtain k r where kr: "polydivide s p = (k,r)"
    by blast
  from trans[OF polydivide_def[where s="s"and p="p", symmetric] kr]
    polydivide_aux_properties[OF np ns trv pnz, where k="0" and k'="k" and r="r"]
  have "(degree r = 0 \<or> degree r < degree p) \<and>
    (\<exists>nr. isnpolyh r nr) \<and> (\<exists>q n1. isnpolyh q n1 \<and> head p ^\<^sub>p k - 0 *\<^sub>p s = p *\<^sub>p q +\<^sub>p r)"
    by blast
  with kr show ?thesis
    apply -
    apply (rule exI[where x="k"])
    apply (rule exI[where x="r"])
    apply simp
    done
qed*)


subsection \<open>More about polypoly and pnormal etc\<close>

definition "isnonconstant p \<longleftrightarrow> \<not> isconstant p"

lemma isnonconstant_pnormal_iff:
  assumes "isnonconstant p"
  shows "pnormal (polypoly bs p) \<longleftrightarrow> Ipoly bs (head p) \<noteq> 0"
proof
  let ?p = "polypoly bs p"
  assume H: "pnormal ?p"
  have csz: "coefficients p \<noteq> []"
    using assms by (cases p) auto
  from coefficients_head[of p] last_map[OF csz, of "Ipoly bs"] pnormal_last_nonzero[OF H]
  show "Ipoly bs (head p) \<noteq> 0"
    by (simp add: polypoly_def)
next
  assume h: "Ipoly bs (head p) \<noteq> 0"
  let ?p = "polypoly bs p"
  have csz: "coefficients p \<noteq> []"
    using assms by (cases p) auto
  then have pz: "?p \<noteq> []"
    by (simp add: polypoly_def)
  then have lg: "length ?p > 0"
    by simp
  from h coefficients_head[of p] last_map[OF csz, of "Ipoly bs"]
  have lz: "last ?p \<noteq> 0"
    by (simp add: polypoly_def)
  from pnormal_last_length[OF lg lz] show "pnormal ?p" .
qed

lemma isnonconstant_coefficients_length: "isnonconstant p \<Longrightarrow> length (coefficients p) > 1"
  unfolding isnonconstant_def
  apply (cases p)
  apply simp_all
  apply (rename_tac nat a, case_tac nat)
  apply auto
  done

lemma isnonconstant_nonconstant:
  assumes "isnonconstant p"
  shows "nonconstant (polypoly bs p) \<longleftrightarrow> Ipoly bs (head p) \<noteq> 0"
proof
  let ?p = "polypoly bs p"
  assume nc: "nonconstant ?p"
  from isnonconstant_pnormal_iff[OF assms, of bs] nc
  show "Ipoly bs (head p) \<noteq> 0"
    unfolding nonconstant_def by blast
next
  let ?p = "polypoly bs p"
  assume h: "Ipoly bs (head p) \<noteq> 0"
  from isnonconstant_pnormal_iff[OF assms, of bs] h
  have pn: "pnormal ?p"
    by blast
  {
    fix x
    assume H: "?p = [x]"
    from H have "length (coefficients p) = 1"
      unfolding polypoly_def by auto
    with isnonconstant_coefficients_length[OF assms]
    have False by arith
  }
  then show "nonconstant ?p"
    using pn unfolding nonconstant_def by blast
qed

lemma pnormal_length: "p \<noteq> [] \<Longrightarrow> pnormal p \<longleftrightarrow> length (pnormalize p) = length p"
  apply (induct p)
  apply (simp_all add: pnormal_def)
  apply (case_tac "p = []")
  apply simp_all
  done

lemma degree_degree:
  assumes "isnonconstant p"
  shows "degree p = Polynomial_List.degree (polypoly bs p) \<longleftrightarrow> Ipoly bs (head p) \<noteq> 0"
proof
  let ?p = "polypoly bs p"
  assume H: "degree p = Polynomial_List.degree ?p"
  from isnonconstant_coefficients_length[OF assms] have pz: "?p \<noteq> []"
    unfolding polypoly_def by auto
  from H degree_coefficients[of p] isnonconstant_coefficients_length[OF assms]
  have lg: "length (pnormalize ?p) = length ?p"
    unfolding Polynomial_List.degree_def polypoly_def by simp
  then have "pnormal ?p"
    using pnormal_length[OF pz] by blast
  with isnonconstant_pnormal_iff[OF assms] show "Ipoly bs (head p) \<noteq> 0"
    by blast
next
  let ?p = "polypoly bs p"
  assume H: "Ipoly bs (head p) \<noteq> 0"
  with isnonconstant_pnormal_iff[OF assms] have "pnormal ?p"
    by blast
  with degree_coefficients[of p] isnonconstant_coefficients_length[OF assms]
  show "degree p = Polynomial_List.degree ?p"
    unfolding polypoly_def pnormal_def Polynomial_List.degree_def by auto
qed


section \<open>Swaps ; Division by a certain variable\<close>

primrec swap :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly"
where
  "swap n m (C x) = C x"
| "swap n m (Bound k) = Bound (if k = n then m else if k = m then n else k)"
| "swap n m (Neg t) = Neg (swap n m t)"
| "swap n m (Add s t) = Add (swap n m s) (swap n m t)"
| "swap n m (Sub s t) = Sub (swap n m s) (swap n m t)"
| "swap n m (Mul s t) = Mul (swap n m s) (swap n m t)"
| "swap n m (Pw t k) = Pw (swap n m t) k"
| "swap n m (CN c k p) = CN (swap n m c) (if k = n then m else if k=m then n else k) (swap n m p)"

lemma swap:
  assumes "n < length bs"
    and "m < length bs"
  shows "Ipoly bs (swap n m t) = Ipoly ((bs[n:= bs!m])[m:= bs!n]) t"
proof (induct t)
  case (Bound k)
  then show ?case
    using assms by simp
next
  case (CN c k p)
  then show ?case
    using assms by simp
qed simp_all

lemma swap_swap_id [simp]: "swap n m (swap m n t) = t"
  by (induct t) simp_all

lemma swap_commute: "swap n m p = swap m n p"
  by (induct p) simp_all

lemma swap_same_id[simp]: "swap n n t = t"
  by (induct t) simp_all

definition "swapnorm n m t = polynate (swap n m t)"

lemma swapnorm:
  fixes t :: "'a::field poly"
  assumes nbs: "n < length bs"
    and mbs: "m < length bs"
  shows "((Ipoly bs (swapnorm n m t))) =
    Ipoly ((bs[n:= bs!m])[m:= bs!n]) t"
  by (simp add: swap[OF assms] swapnorm_def)

lemma swapnorm_isnpoly [simp]:
  fixes p :: "'a::field poly"
  shows "isnpoly (swapnorm n m p)"
  by (simp add: swapnorm_def)

definition "polydivideby n s p =
  (let
    ss = swapnorm 0 n s;
    sp = swapnorm 0 n p;
    h = head sp;
    (k, r) = polydivide ss sp
   in (k, swapnorm 0 n h, swapnorm 0 n r))"

lemma swap_nz [simp]: "swap n m p = 0\<^sub>p \<longleftrightarrow> p = 0\<^sub>p"
  by (induct p) simp_all

fun isweaknpoly :: "'a poly \<Rightarrow> bool"
where
  "isweaknpoly (C c) = True"
| "isweaknpoly (CN c n p) \<longleftrightarrow> isweaknpoly c \<and> isweaknpoly p"
| "isweaknpoly p = False"

lemma isnpolyh_isweaknpoly: "isnpolyh p n0 \<Longrightarrow> isweaknpoly p"
  by (induct p arbitrary: n0) auto

lemma swap_isweanpoly: "isweaknpoly p \<Longrightarrow> isweaknpoly (swap n m p)"
  by (induct p) auto

end