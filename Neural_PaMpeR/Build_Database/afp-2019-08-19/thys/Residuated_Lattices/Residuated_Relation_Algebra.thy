(* Title:      Residuated Relation Algebras
   Author:     Victor Gomes <vborgesferreiragomes1 at sheffield.ac.uk>
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Residuated Relation Algebras\<close>

theory Residuated_Relation_Algebra
  imports Residuated_Boolean_Algebras Relation_Algebra.Relation_Algebra
begin

context boolean_algebra begin

text \<open>
  The notation used in the relation algebra AFP entry differs a little from ours.
\<close>

notation
  times (infixl "\<cdot>" 70)
  and plus (infixl "+" 65)
  and Groups.zero_class.zero ("0")
  and Groups.one_class.one ("1")

no_notation
  inf (infixl "\<cdot>" 70)
  and sup (infixl "+" 65)
  and bot ("0")
  and top ("1")

end

text \<open>
  We prove that a unital residuated boolean algebra enriched with two simple
  equalities form a non-associative relation algebra, that is, a relation
  algebra where the associativity law does not hold.
\<close>

class nra = unital_residuated_boolean +
  assumes conv1: "x \<rhd> y = (x \<rhd> 1)\<cdot>y"
  and conv2: "x \<lhd> y = x\<cdot>(1 \<lhd> y)"
begin

text \<open>
  When the converse operation is set to be $\lambda x.\  x \rhd 1$,
  a unital residuated boolean algebra forms a non associative relation algebra.
\<close>
  
lemma conv_invol: "x \<rhd> 1 \<rhd> 1 = x"
  by (metis local.conv1 local.jonsson1b local.mult_onel)

lemma conv_add: "x \<squnion> y \<rhd> 1 = (x \<rhd> 1) \<squnion> (y \<rhd> 1)"
  by (metis local.conjr2_sup)

lemma conv_contrav: "x\<cdot>y \<rhd> 1 = (y \<rhd> 1)\<cdot>(x \<rhd> 1)"
  by (metis local.conv1 local.conv2 local.jonsson1b local.jonsson2c)

lemma conv_res: "(x \<rhd> 1)\<cdot>- (x\<cdot>y) \<le> - y"
  by (metis local.comp_anti local.conjugate_r_def local.conv1 local.double_compl local.res_rc1)

text \<open>
  Similarly, for $x^\smile = 1 \lhd x$, since $x \rhd 1 = 1 \lhd x$ when
  $x \rhd 1 \rhd 1 = x$ holds.
\<close>

lemma conv_invol': "1 \<lhd> (1 \<lhd> x) = x"
  by (metis local.conv_invol local.jonsson3c)

lemma conv_add': "1 \<lhd> (x \<squnion> y) = (1 \<lhd> x) \<squnion> (1 \<lhd> y)"
  by (metis local.conjl1_sup)

lemma conv_contrav': "1 \<lhd> x\<cdot>y = (1 \<lhd> y)\<cdot>(1 \<lhd> x)"
  by (metis local.conv_contrav local.conv_invol local.jonsson3c)

lemma conv_res': "(1 \<lhd> x)\<cdot>- (x\<cdot>y) \<le> - y"
  by (metis conv_res local.conv_invol local.jonsson3c)
  
end (* nra *)

text \<open>
  Since the previous axioms are equivalent when multiplication is associative
  in a residuated boolean monoid, one of them are sufficient to
  derive a relation algebra.
\<close>

class residuated_ra = residuated_boolean_monoid +
  assumes conv: "x \<rhd> y = (x \<rhd> 1)\<cdot>y"
begin

subclass nra
proof (standard, fact conv)
  fix x y show "x \<lhd> y = x\<cdot>(1 \<lhd> y)"
    by (metis conv jonsson4)
qed

sublocale relation_algebra where
  composition = "(\<cdot>)" and unit = 1 and
  converse = "\<lambda>x. x \<rhd> 1"
proof
  fix x y z
  show "x\<cdot>y\<cdot>z = x\<cdot>(y\<cdot>z)"
    by (metis local.mult_assoc)
  show "x\<cdot>1 = x"
    by (metis local.mult_onel)
  show "(x \<squnion> y)\<cdot>z = x\<cdot>z \<squnion> y\<cdot>z"
    by (metis local.distr)
  show "x \<rhd> 1 \<rhd> 1 = x"
    by (metis local.conv_invol)
  show "x \<squnion> y \<rhd> 1 = (x \<rhd> 1) \<squnion> (y \<rhd> 1)"
    by (metis local.conv_add)
  show "x\<cdot>y \<rhd> 1 = (y \<rhd> 1)\<cdot>(x \<rhd> 1)"
    by (metis local.conv_contrav)
  show "(x \<rhd> 1)\<cdot>- (x\<cdot>y) \<le> - y"
    by (metis local.conv_res)
qed

end (* residuated_ra *)

end
