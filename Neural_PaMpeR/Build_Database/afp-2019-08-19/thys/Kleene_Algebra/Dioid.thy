(* Title:      From Semilattices to Dioids
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Dioids\<close>

theory Dioid
imports Signatures
begin

subsection \<open>Join Semilattices\<close> 

text \<open>Join semilattices can be axiomatised order-theoretically or
algebraically. A join semilattice (or upper semilattice) is either a
poset in which every pair of elements has a join (or least upper
bound), or a set endowed with an associative, commutative, idempotent
binary operation. It is well known that the order-theoretic definition
induces the algebraic one and vice versa. We start from the algebraic
axiomatisation because it is easily expandable to dioids, using
Isabelle's type class mechanism.

In Isabelle/HOL, a type class @{class semilattice_sup} is available.
Alas, we cannot use this type class because we need the symbol~\<open>+\<close> for the join operation in the dioid expansion and subclass
proofs in Isabelle/HOL require the two type classes involved to have
the same fixed signature.

Using {\em add\_assoc} as a name for the first assumption in class
{\em join\_semilattice} would lead to name clashes: we will later
define classes that inherit from @{class semigroup_add}, which
provides its own assumption {\em add\_assoc}, and prove that these are
subclasses of {\em join\_semilattice}. Hence the primed name.
\<close>

class join_semilattice = plus_ord +
  assumes add_assoc' [ac_simps]: "(x + y) + z = x + (y + z)"
  and add_comm [ac_simps] : "x + y = y + x"
  and add_idem [simp]: "x + x = x"
begin

lemma add_left_comm [ac_simps]: "y + (x + z) = x + (y + z)"
  using local.add_assoc' local.add_comm by auto

lemma add_left_idem [ac_simps]: "x + (x + y) = x + y"
  unfolding add_assoc' [symmetric] by simp

text \<open>The definition @{term "x \<le> y \<longleftrightarrow> x + y = y"} of the order is
hidden in class @{class plus_ord}.

We show some simple order-based properties of semilattices. The
first one states that every semilattice is a partial order.\<close>

subclass order
proof
  fix x y z :: 'a
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    using local.add_comm local.less_def local.less_eq_def by force
  show "x \<le> x"
    by (simp add: local.less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (metis add_assoc' less_eq_def)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (simp add: local.add_comm local.less_eq_def)
qed

text \<open>Next we show that joins are least upper bounds.\<close>

sublocale join: semilattice_sup "(+)"
  by (unfold_locales; simp add: ac_simps local.less_eq_def)

text \<open>Next we prove that joins are isotone (order preserving).\<close>

lemma add_iso: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
  using join.sup_mono by blast

text \<open>
  The next lemma links the definition of order as @{term "x \<le> y \<longleftrightarrow> x + y = y"}
  with a perhaps more conventional one known, e.g., from arithmetics.
\<close>

lemma order_prop: "x \<le> y \<longleftrightarrow> (\<exists>z. x + z = y)"
proof
  assume "x \<le> y"
  hence "x + y = y"
    by (simp add: less_eq_def)
  thus "\<exists>z. x + z = y"
    by auto
next
  assume "\<exists>z. x + z = y"
  then obtain c where "x + c = y"
    by auto
  hence "x + c \<le> y"
    by simp
  thus "x \<le> y"
    by simp
qed

end (* join_semilattice *)


subsection \<open>Join Semilattices with an Additive Unit\<close>

text \<open>We now expand join semilattices by an additive unit~$0$. Is
the least element with respect to the order, and therefore often
denoted by~\<open>\<bottom>\<close>. Semilattices with a least element are often
called \emph{bounded}.\<close>

class join_semilattice_zero = join_semilattice + zero +
  assumes add_zero_l [simp]: "0 + x = x"

begin

subclass comm_monoid_add
  by (unfold_locales, simp_all add: add_assoc') (simp add: add_comm)

sublocale join: bounded_semilattice_sup_bot "(+)" "(\<le>)" "(<)" 0
  by unfold_locales (simp add: local.order_prop)
  
lemma no_trivial_inverse: "x \<noteq> 0 \<Longrightarrow> \<not>(\<exists>y. x + y = 0)"
  by (metis local.add_0_right local.join.sup_left_idem)

end (* join_semilattice_zero *)


subsection \<open>Near Semirings\<close>

text \<open>\emph{Near semirings} (also called seminearrings) are
generalisations of near rings to the semiring case. They have been
studied, for instance, in G.~Pilz's book~\cite{pilz83nearrings} on
near rings. According to his definition, a near semiring consists of
an additive and a multiplicative semigroup that interact via a single
distributivity law (left or right). The additive semigroup is not
required to be commutative. The definition is influenced by partial
transformation semigroups.

We only consider near semirings in which addition is commutative, and
in which the right distributivity law holds. We call such near
semirings \emph{abelian}.\<close>

class ab_near_semiring = ab_semigroup_add + semigroup_mult +  
  assumes distrib_right' [simp]: "(x + y) \<cdot> z = x \<cdot> z + y \<cdot> z"

subclass (in semiring) ab_near_semiring
  by (unfold_locales, metis distrib_right)

class ab_pre_semiring = ab_near_semiring +
  assumes subdistl_eq: "z \<cdot> x + z \<cdot> (x + y) = z \<cdot> (x + y)"

subsection \<open>Variants of Dioids\<close>

text \<open>A \emph{near dioid} is an abelian near semiring in which
addition is idempotent. This generalises the notion of (additively)
idempotent semirings by dropping one distributivity law. Near dioids
are a starting point for process algebras.

By modelling variants of dioids as variants of semirings in which
addition is idempotent we follow the tradition of
Birkhoff~\cite{birkhoff67lattices}, but deviate from the definitions
in Gondran and Minoux's book~\cite{gondran10graphs}.\<close>

class near_dioid = ab_near_semiring + plus_ord +
  assumes add_idem' [simp]: "x + x = x"

begin

text \<open>Since addition is idempotent, the additive (commutative)
semigroup reduct of a near dioid is a semilattice. Near dioids are
therefore ordered by the semilattice order.\<close>

subclass join_semilattice
  by unfold_locales (auto simp add: add.commute add.left_commute)

text \<open>It follows that multiplication is right-isotone (but not
necessarily left-isotone).\<close>

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
proof -
  assume "x \<le> y"
  hence "x + y = y"
    by (simp add: less_eq_def)
  hence "(x + y) \<cdot> z = y \<cdot> z"
    by simp
  thus "x \<cdot> z \<le> y \<cdot> z"
    by (simp add: less_eq_def)
qed

lemma "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  (* nitpick [expect=genuine] -- "3-element counterexample" *)
oops

text \<open>The next lemma states that, in every near dioid, left
isotonicity and left subdistributivity are equivalent.\<close>

lemma mult_isol_equiv_subdistl:
  "(\<forall>x y z. x \<le> y \<longrightarrow> z \<cdot> x \<le> z \<cdot> y) \<longleftrightarrow> (\<forall>x y z. z \<cdot> x \<le> z \<cdot> (x + y))"
  by (metis local.join.sup_absorb2 local.join.sup_ge1)

text \<open>The following lemma is relevant to propositional Hoare logic.\<close>

lemma phl_cons1: "x \<le> w \<Longrightarrow> w \<cdot> y \<le> y \<cdot> z \<Longrightarrow> x \<cdot> y \<le> y \<cdot> z"
  using dual_order.trans mult_isor by blast

end (* near_dioid *)


text \<open>We now make multiplication in near dioids left isotone, which
is equivalent to left subdistributivity, as we have seen. The
corresponding structures form the basis of probabilistic Kleene
algebras~\cite{mciverweber05pka} and game
algebras~\cite{venema03gamealgebra}. We are not aware that these
structures have a special name, so we baptise them \emph{pre-dioids}.

We do not explicitly define pre-semirings since we have no application
for them.\<close>

class pre_dioid = near_dioid +
  assumes subdistl: "z \<cdot> x \<le> z \<cdot> (x + y)"

begin

text \<open>Now, obviously, left isotonicity follows from left subdistributivity.\<close>

lemma subdistl_var: "z \<cdot> x + z \<cdot> y \<le> z \<cdot> (x + y)"
  using local.mult_isol_equiv_subdistl local.subdistl by auto

subclass ab_pre_semiring
  apply unfold_locales
  by (simp add: local.join.sup_absorb2 local.subdistl)

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
proof -
  assume "x \<le> y"
  hence "x + y = y"
    by (simp add: less_eq_def)
  also have "z \<cdot> x + z \<cdot> y \<le> z \<cdot> (x + y)"
    using subdistl_var by blast
  moreover have "... = z \<cdot> y"
    by (simp add: calculation)
  ultimately show "z \<cdot> x \<le> z \<cdot> y"
    by auto
qed

lemma mult_isol_var: "u \<le> x \<Longrightarrow> v \<le> y \<Longrightarrow> u \<cdot> v \<le> x \<cdot> y"
  by (meson local.dual_order.trans local.mult_isor mult_isol)

lemma mult_double_iso: "x \<le> y \<Longrightarrow> w \<cdot> x \<cdot> z \<le> w \<cdot> y \<cdot> z"
  by (simp add: local.mult_isor mult_isol)

text \<open>The following lemmas are relevant to propositional Hoare logic.\<close>

lemma phl_cons2: "w \<le> x \<Longrightarrow> z \<cdot> y \<le> y \<cdot> w \<Longrightarrow> z \<cdot> y \<le> y \<cdot> x"
  using local.order_trans mult_isol by blast

lemma phl_seq: 
assumes "p \<cdot> x \<le> x \<cdot> r"
and "r \<cdot> y \<le> y \<cdot> q" 
shows "p \<cdot> (x \<cdot> y) \<le> x \<cdot> y \<cdot> q"
proof -
  have "p \<cdot> x \<cdot> y \<le> x \<cdot> r \<cdot> y"
    using assms(1) mult_isor by blast
  thus ?thesis
    by (metis assms(2) order_prop order_trans subdistl mult_assoc)
qed

lemma phl_cond: 
assumes "u \<cdot> v \<le> v \<cdot> u \<cdot> v" and "u \<cdot> w \<le> w \<cdot> u \<cdot> w" 
and "\<And>x y. u \<cdot> (x + y) \<le> u \<cdot> x + u \<cdot> y"
and "u \<cdot> v \<cdot> x \<le> x \<cdot> z" and "u \<cdot> w \<cdot> y \<le> y \<cdot> z" 
shows "u \<cdot> (v \<cdot> x + w \<cdot> y) \<le> (v \<cdot> x + w \<cdot> y) \<cdot> z"
proof -
  have a: "u \<cdot> v \<cdot> x \<le> v \<cdot> x \<cdot> z" and b: "u \<cdot> w \<cdot> y \<le> w \<cdot> y \<cdot> z"
    by (metis assms mult_assoc phl_seq)+
  have  "u \<cdot> (v \<cdot> x + w \<cdot> y) \<le> u \<cdot> v \<cdot> x + u \<cdot> w \<cdot> y"
    using assms(3) mult_assoc by auto
  also have "... \<le> v \<cdot> x \<cdot> z + w \<cdot> y \<cdot> z"
    using a b join.sup_mono by blast
  finally show ?thesis
    by simp
qed

lemma phl_export1:
assumes "x \<cdot> y \<le> y \<cdot> x \<cdot> y"
and "(x \<cdot> y) \<cdot> z \<le> z \<cdot> w"
shows "x \<cdot> (y \<cdot> z) \<le> (y \<cdot> z) \<cdot> w"
proof -
  have "x \<cdot> y \<cdot> z \<le> y \<cdot> x \<cdot> y \<cdot> z"
    by (simp add: assms(1) mult_isor)
  thus ?thesis
    using assms(1) assms(2) mult_assoc phl_seq by auto 
qed

lemma phl_export2: 
assumes "z \<cdot> w \<le> w \<cdot> z \<cdot> w"
and "x \<cdot> y \<le> y \<cdot> z"
shows "x \<cdot> (y \<cdot> w) \<le> y \<cdot> w \<cdot> (z \<cdot> w)"
proof -
  have "x \<cdot> y \<cdot> w \<le> y \<cdot> z \<cdot> w"
    using assms(2) mult_isor by blast
  thus ?thesis
    by (metis assms(1) dual_order.trans order_prop subdistl mult_assoc)
qed

end (* pre_dioid *)

text \<open>By adding a full left distributivity law we obtain semirings
(which are already available in Isabelle/HOL as @{class semiring})
from near semirings, and dioids from near dioids. Dioids are therefore
idempotent semirings.\<close>

class dioid = near_dioid + semiring

subclass (in dioid) pre_dioid
  by unfold_locales (simp add: local.distrib_left)

subsection \<open>Families of Nearsemirings with a Multiplicative Unit\<close>

text \<open>Multiplicative units are important, for instance, for defining
an operation of finite iteration or Kleene star on dioids. We do not
introduce left and right units separately since we have no application
for this.\<close>

class ab_near_semiring_one = ab_near_semiring + one +
  assumes mult_onel [simp]: "1 \<cdot> x = x"
  and mult_oner [simp]: "x \<cdot> 1 = x"

begin

subclass monoid_mult
  by (unfold_locales, simp_all)

end (* ab_near_semiring_one *)

class ab_pre_semiring_one = ab_near_semiring_one + ab_pre_semiring

class near_dioid_one = near_dioid + ab_near_semiring_one

begin

text \<open>The following lemma is relevant to propositional Hoare logic.\<close>

lemma phl_skip: "x \<cdot> 1 \<le> 1 \<cdot> x"
  by simp

end

text \<open>For near dioids with one, it would be sufficient to require
$1+1=1$. This implies @{term "x+x=x"} for arbitray~@{term x} (but that
would lead to annoying redundant proof obligations in mutual
subclasses of @{class near_dioid_one} and @{class near_dioid} later).
\<close>

class pre_dioid_one = pre_dioid + near_dioid_one

class dioid_one = dioid + near_dioid_one

subclass (in dioid_one) pre_dioid_one ..


subsection \<open>Families of Nearsemirings with Additive Units\<close>

text \<open>
We now axiomatise an additive unit~$0$ for nearsemirings. The zero is
usually required to satisfy annihilation properties with respect to
multiplication. Due to applications we distinguish a zero which is
only a left annihilator from one that is also a right annihilator.
More briefly, we call zero either a left unit or a unit.

Semirings and dioids with a right zero only can be obtained from those
with a left unit by duality.
\<close>

class ab_near_semiring_one_zerol = ab_near_semiring_one + zero +
  assumes add_zerol [simp]: "0 + x = x"
  and annil [simp]: "0 \<cdot> x = 0"

begin 

text \<open>Note that we do not require~$0 \neq 1$.\<close>

lemma add_zeror [simp]: "x + 0 = x"
  by (subst add_commute) simp

end (* ab_near_semiring_one_zerol *)

class ab_pre_semiring_one_zerol = ab_near_semiring_one_zerol + ab_pre_semiring

begin

text \<open>The following lemma shows that there is no point defining pre-semirings separately from dioids.\<close>

lemma "1 + 1 = 1"
proof -
  have "1 + 1 = 1 \<cdot> 1 + 1 \<cdot> (1 + 0)"
    by simp
  also have "... = 1 \<cdot> (1 + 0)"
    using subdistl_eq by presburger
  finally show ?thesis
    by simp
qed

end (* ab_pre_semiring_one_zerol *)

class near_dioid_one_zerol = near_dioid_one + ab_near_semiring_one_zerol

subclass (in near_dioid_one_zerol) join_semilattice_zero
  by (unfold_locales, simp)

class pre_dioid_one_zerol = pre_dioid_one + ab_near_semiring_one_zerol

subclass (in pre_dioid_one_zerol) near_dioid_one_zerol ..

class semiring_one_zerol = semiring + ab_near_semiring_one_zerol

class dioid_one_zerol = dioid_one + ab_near_semiring_one_zerol

subclass (in dioid_one_zerol) pre_dioid_one_zerol ..

text \<open>We now make zero also a right annihilator.\<close>

class ab_near_semiring_one_zero = ab_near_semiring_one_zerol +
  assumes annir [simp]: "x \<cdot> 0 = 0"

class semiring_one_zero = semiring + ab_near_semiring_one_zero

class near_dioid_one_zero = near_dioid_one_zerol + ab_near_semiring_one_zero

class pre_dioid_one_zero = pre_dioid_one_zerol + ab_near_semiring_one_zero

subclass (in pre_dioid_one_zero) near_dioid_one_zero ..

class dioid_one_zero = dioid_one_zerol + ab_near_semiring_one_zero

subclass (in dioid_one_zero) pre_dioid_one_zero ..

subclass (in dioid_one_zero) semiring_one_zero ..

subsection \<open>Duality by Opposition\<close>

text \<open>
Swapping the order of multiplication in a semiring (or dioid) gives
another semiring (or dioid), called its \emph{dual} or
\emph{opposite}.
\<close>

definition (in times) opp_mult (infixl "\<odot>" 70)
  where "x \<odot> y \<equiv> y \<cdot> x"

lemma (in semiring_1) dual_semiring_1:
  "class.semiring_1 1 (\<odot>) (+) 0"
  by unfold_locales (auto simp add: opp_mult_def mult.assoc distrib_right distrib_left)

lemma (in dioid_one_zero) dual_dioid_one_zero:
  "class.dioid_one_zero (+) (\<odot>) 1 0 (\<le>) (<)"
  by unfold_locales (auto simp add: opp_mult_def mult.assoc distrib_right distrib_left)

subsection \<open>Selective Near Semirings\<close>

text \<open>In this section we briefly sketch a generalisation of the
notion of \emph{dioid}. Some important models, e.g. max-plus and
min-plus semirings, have that property.\<close>

class selective_near_semiring = ab_near_semiring + plus_ord +
  assumes select: "x + y = x \<or> x + y = y"

begin

lemma select_alt: "x + y \<in> {x,y}"
  by (simp add: local.select)

text \<open>It follows immediately that every selective near semiring is a near dioid.\<close>

subclass near_dioid
  by (unfold_locales, meson select)

text \<open>Moreover, the order in a selective near semiring is obviously linear.\<close>

subclass linorder
  by (unfold_locales, metis add.commute join.sup.orderI select)

end (*selective_near_semiring*)

class selective_semiring = selective_near_semiring + semiring_one_zero

begin

subclass dioid_one_zero ..

end (* selective_semiring *)

end
