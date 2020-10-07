(* Title:      Domain Semirings
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Domain Semirings\<close>

theory Domain_Semiring
imports Kleene_Algebra.Kleene_Algebra

begin

subsection \<open>Domain Semigroups and Domain Monoids\<close>

class domain_op =
  fixes domain_op :: "'a \<Rightarrow> 'a" ("d")

text \<open>First we define the class of domain semigroups. Axioms are taken from~\cite{DesharnaisJipsenStruth}.\<close>

class domain_semigroup = semigroup_mult + domain_op +
  assumes dsg1 [simp]: "d x \<cdot> x = x"
  and dsg2 [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
  and dsg3 [simp]: "d (d x \<cdot> y) = d x \<cdot> d y"
  and dsg4: "d x \<cdot> d y = d y \<cdot> d x"

begin

lemma domain_invol [simp]: "d (d x) = d x"
proof -
  have "d (d x) = d (d (d x \<cdot> x))"
    by simp
  also have "... = d (d x \<cdot> d x)"
    using dsg3 by presburger
  also have "... = d (d x \<cdot> x)"
    by simp
  finally show ?thesis
    by simp
qed

text \<open>The next lemmas show that domain elements form semilattices.\<close>

lemma dom_el_idem [simp]: "d x \<cdot> d x = d x"
proof -
  have "d x \<cdot> d x = d (d x \<cdot> x)"
    using dsg3 by presburger
  thus ?thesis
    by simp
qed

lemma dom_mult_closed [simp]: "d (d x \<cdot> d y) = d x \<cdot> d y"
  by simp

lemma dom_lc3 [simp]: "d x \<cdot> d (x \<cdot> y) = d (x \<cdot> y)"
proof -
  have "d x \<cdot> d (x \<cdot> y) = d (d x \<cdot> x \<cdot> y)"
    using dsg3 mult_assoc by presburger
  thus ?thesis
    by simp
qed

lemma d_fixpoint: "(\<exists>y. x = d y) \<longleftrightarrow> x = d x"
  by auto

lemma d_type: "\<forall>P. (\<forall>x. x = d x \<longrightarrow> P x) \<longleftrightarrow> (\<forall>x. P (d x))"
  by (metis domain_invol)

text \<open>We define the semilattice ordering on domain semigroups and explore the semilattice of domain elements from the order point of view.\<close>

definition ds_ord :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y \<longleftrightarrow> x = d x \<cdot> y"

lemma ds_ord_refl: "x \<sqsubseteq> x"
  by (simp add: ds_ord_def)

lemma ds_ord_trans: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
proof -
  assume "x \<sqsubseteq> y" and a: "y \<sqsubseteq> z"
  hence b: "x = d x \<cdot> y"
    using ds_ord_def by blast
  hence "x = d x \<cdot> d y \<cdot> z"
    using a ds_ord_def mult_assoc by force
  also have "... = d (d x \<cdot> y) \<cdot> z"
    by simp
  also have "... = d x \<cdot> z"
    using b by auto
  finally show ?thesis
    using ds_ord_def by blast
qed

lemma ds_ord_antisym: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
proof -
  assume a: "x \<sqsubseteq> y" and "y \<sqsubseteq> x"
  hence b: "y = d y \<cdot> x"
    using ds_ord_def by auto
  have "x = d x \<cdot> d y \<cdot> x"
    using a b ds_ord_def mult_assoc by force
  also have "... = d y \<cdot> x"
    by (metis (full_types) b dsg3 dsg4)
  thus ?thesis
    using b calculation by presburger
qed

text \<open>This relation is indeed an order.\<close>

sublocale  ds: order "(\<sqsubseteq>)" "\<lambda>x y. (x \<sqsubseteq> y \<and> x \<noteq> y)"
proof
  show "\<And>x y. (x \<sqsubseteq> y \<and> x \<noteq> y) = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
    using ds_ord_antisym by blast
  show "\<And>x. x \<sqsubseteq> x"
    by (rule ds_ord_refl)
  show "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"
    by (rule ds_ord_trans)
  show "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"
    by (rule ds_ord_antisym)
qed

lemma ds_ord_eq: "x \<sqsubseteq> d x \<longleftrightarrow> x = d x"
  by (simp add: ds_ord_def)

lemma "x \<sqsubseteq> y \<Longrightarrow> z \<cdot> x \<sqsubseteq> z \<cdot> y"
(*nitpick [expect=genuine]*)
oops

lemma ds_ord_iso_right: "x \<sqsubseteq> y \<Longrightarrow> x \<cdot> z \<sqsubseteq> y \<cdot> z"
proof -
  assume "x \<sqsubseteq> y"
  hence a: "x = d x \<cdot> y"
    by (simp add: ds_ord_def)
  hence "x \<cdot> z = d x \<cdot> y \<cdot> z"
    by auto
  also have "... = d (d x \<cdot> y \<cdot> z) \<cdot> d x \<cdot> y \<cdot> z"
    using dsg1 mult_assoc by presburger
  also have "... = d (x \<cdot> z) \<cdot> d x \<cdot> y \<cdot> z"
    using a by presburger
  finally show ?thesis
    using ds_ord_def dsg4 mult_assoc by auto
qed

text \<open>The order on domain elements could as well be defined based on multiplication/meet.\<close>

lemma ds_ord_sl_ord: "d x \<sqsubseteq> d y \<longleftrightarrow> d x \<cdot> d y = d x"
  using ds_ord_def by auto

lemma ds_ord_1: "d (x \<cdot> y) \<sqsubseteq> d x"
  by (simp add: ds_ord_sl_ord dsg4)

lemma ds_subid_aux: "d x \<cdot> y \<sqsubseteq> y"
  by (simp add: ds_ord_def mult_assoc)

lemma "y \<cdot> d x \<sqsubseteq> y"
(*nitpick [expect=genuine]*)
oops

lemma ds_dom_iso: "x \<sqsubseteq> y \<Longrightarrow> d x \<sqsubseteq> d y"
proof -
  assume "x \<sqsubseteq> y"
  hence "x = d x \<cdot> y"
    by (simp add: ds_ord_def)
  hence "d x = d (d x \<cdot> y)"
    by presburger
  also have "... = d x \<cdot> d y"
    by simp
  finally show ?thesis
    using ds_ord_sl_ord by auto
qed

lemma ds_dom_llp: "x \<sqsubseteq> d y \<cdot> x \<longleftrightarrow> d x \<sqsubseteq> d y"
proof
  assume "x \<sqsubseteq> d y \<cdot> x"
  hence "x = d y \<cdot> x"
    by (simp add: ds_subid_aux ds.order.antisym)
  hence "d x = d (d y \<cdot> x)"
    by presburger
  thus "d x \<sqsubseteq> d y"
    using ds_ord_sl_ord dsg4 by force
next
  assume "d x \<sqsubseteq> d y"
  thus "x \<sqsubseteq> d y \<cdot> x"
    by (metis (no_types) ds_ord_iso_right dsg1)
qed

lemma ds_dom_llp_strong: "x = d y \<cdot> x \<longleftrightarrow> d x \<sqsubseteq> d y"
  by (simp add: ds_dom_llp ds.eq_iff ds_subid_aux)

definition refines :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "refines x y \<equiv> d y \<sqsubseteq> d x \<and> (d y) \<cdot> x \<sqsubseteq> y"

lemma refines_refl: "refines x x"
  using refines_def by simp

lemma refines_trans: "refines x y \<Longrightarrow> refines y z \<Longrightarrow> refines x z"
  unfolding refines_def
  by (metis domain_invol ds.dual_order.trans dsg1 dsg3 ds_ord_def)

lemma refines_antisym: "refines x y \<Longrightarrow> refines y x \<Longrightarrow> x = y"
  unfolding refines_def
  using ds_dom_llp ds_ord_antisym by fastforce

sublocale ref: order "refines" "\<lambda>x y. (refines x y \<and> x \<noteq> y)"
proof
  show "\<And>x y. (refines x y \<and> x \<noteq> y) = (refines x y \<and> \<not> refines y x)"
    using refines_antisym by blast
  show "\<And>x. refines x x"
    by (rule refines_refl)
  show "\<And>x y z. refines x y \<Longrightarrow> refines y z \<Longrightarrow> refines x z"
    by (rule refines_trans)
  show "\<And>x y. refines x y \<Longrightarrow> refines y x \<Longrightarrow> x = y"
    by (rule refines_antisym)
qed

end

text \<open>We expand domain semigroups to domain monoids.\<close>

class domain_monoid = monoid_mult + domain_semigroup
begin

lemma dom_one [simp]: "d 1 = 1"
proof -
  have "1 = d 1 \<cdot> 1"
    using dsg1 by presburger
  thus ?thesis
    by simp
qed

lemma ds_subid_eq: "x \<sqsubseteq> 1 \<longleftrightarrow> x = d x"
  by (simp add: ds_ord_def)

end

subsection \<open>Domain Near-Semirings\<close>

text \<open>The axioms for domain near-semirings are taken from~\cite{DesharnaisStruthAMAST}.\<close>

class domain_near_semiring = ab_near_semiring + plus_ord + domain_op +
  assumes dns1 [simp]: "d x \<cdot> x = x"
  and dns2 [simp]: "d (x \<cdot> d y) = d(x \<cdot> y)"
  and dns3 [simp]: "d (x + y) = d x + d y"
  and dns4: "d x \<cdot> d y = d y \<cdot> d x"
  and dns5 [simp]: "d x \<cdot> (d x + d y) = d x"

begin

text \<open>Domain near-semirings are automatically dioids; addition is idempotent.\<close>

subclass near_dioid
proof
  show "\<And>x. x + x = x"
  proof -
    fix x
    have a: "d x = d x \<cdot> d (x + x)"
      using dns3 dns5 by presburger
    have "d (x + x) = d (x + x + (x + x)) \<cdot> d (x + x)"
      by (metis (no_types) dns3  dns4 dns5)
    hence "d (x + x) = d (x + x) + d (x + x)"
      by simp
    thus "x + x = x"
      by (metis a dns1 dns4 distrib_right')
  qed
qed

text \<open>Next we prepare to show that domain near-semirings are domain semigroups.\<close>

lemma dom_iso: "x \<le> y \<Longrightarrow> d x \<le> d y"
  using order_prop by auto

lemma dom_add_closed [simp]: "d (d x + d y) = d x + d y"
proof -
  have "d (d x + d y) = d (d x) + d (d y)"
    by simp
  thus ?thesis
    by (metis dns1 dns2 dns3 dns4)
qed

lemma dom_absorp_2 [simp]: "d x + d x \<cdot> d y = d x"
proof -
  have "d x + d x \<cdot> d y = d x \<cdot> d x + d x \<cdot> d y"
    by (metis add_idem' dns5)
  also have "... = (d x + d y) \<cdot> d x"
    by (simp add: dns4)
  also have "... = d x \<cdot> (d x + d y)"
    by (metis dom_add_closed dns4)
  finally show ?thesis
    by simp
qed

lemma dom_1: "d (x \<cdot> y) \<le> d x"
proof -
  have "d (x \<cdot> y) = d (d x \<cdot> d (x \<cdot> y))"
    by (metis dns1 dns2 mult_assoc)
  also have "... \<le> d (d x) + d (d x \<cdot> d (x \<cdot> y))"
    by simp
  also have "... = d (d x + d x \<cdot> d (x \<cdot> y))"
    using dns3  by presburger
  also have "... = d (d x)"
    by simp
  finally show ?thesis
    by (metis dom_add_closed add_idem')
qed

lemma dom_subid_aux2: "d x \<cdot> y \<le> y"
proof -
  have "d x \<cdot> y \<le> d (x + d y) \<cdot> y"
    by (simp add: mult_isor)
  also have "... = (d x + d (d y)) \<cdot> d y \<cdot> y"
    using dns1 dns3 mult_assoc by presburger
  also have "... = (d y + d y \<cdot> d x) \<cdot> y"
    by (simp add: dns4 add_commute)
  finally show ?thesis
    by simp
qed

lemma dom_glb: "d x \<le> d y \<Longrightarrow> d x \<le> d z \<Longrightarrow> d x \<le> d y \<cdot> d z"
  by (metis dns5 less_eq_def mult_isor)

lemma dom_glb_eq: "d x \<le> d y \<cdot> d z \<longleftrightarrow> d x \<le> d y \<and> d x \<le> d z"
proof -
  have "d x \<le> d z \<longrightarrow> d x \<le> d z"
    by meson
  then show ?thesis
    by (metis (no_types) dom_absorp_2 dom_glb dom_subid_aux2 local.dual_order.trans local.join.sup.coboundedI2)
qed

lemma dom_ord: "d x \<le> d y \<longleftrightarrow> d x \<cdot> d y = d x"
proof
  assume "d x \<le> d y"
  hence "d x + d y = d y"
    by (simp add: less_eq_def)
  thus "d x \<cdot> d y = d x"
    by (metis dns5)
next
  assume "d x \<cdot> d y = d x"
  thus "d x \<le> d y"
    by (metis dom_subid_aux2)
qed

lemma dom_export [simp]: "d (d x \<cdot> y) = d x \<cdot> d y"
proof (rule antisym)
  have "d (d x \<cdot> y) = d (d (d x \<cdot> y)) \<cdot> d (d x \<cdot> y)"
    using dns1 by presburger
  also have "... = d (d x \<cdot> d y) \<cdot> d (d x \<cdot> y)"
    by (metis dns1 dns2 mult_assoc)
  finally show a: "d (d x \<cdot> y) \<le> d x \<cdot> d y"
    by (metis (no_types) dom_add_closed dom_glb dom_1 add_idem' dns2 dns4)
  have "d (d x \<cdot> y) = d (d x \<cdot> y) \<cdot> d x"
    using a dom_glb_eq dom_ord by force
  hence "d x \<cdot> d y = d (d x \<cdot> y) \<cdot> d y"
    by (metis dns1 dns2 mult_assoc)
  thus "d x \<cdot> d y \<le> d (d x \<cdot> y)"
    using a dom_glb_eq dom_ord by auto
qed

subclass domain_semigroup
 by (unfold_locales, auto simp: dns4)

text \<open>We compare the domain semigroup ordering with that of the dioid.\<close>

lemma d_two_orders: "d x \<sqsubseteq> d y \<longleftrightarrow> d x \<le> d y"
  by (simp add: dom_ord ds_ord_sl_ord)

lemma two_orders: "x \<sqsubseteq> y \<Longrightarrow> x \<le> y"
  by (metis dom_subid_aux2 ds_ord_def)

lemma "x \<le> y \<Longrightarrow> x \<sqsubseteq> y"
(*nitpick [expect=genuine]*)
oops

text \<open>Next we prove additional properties.\<close>

lemma dom_subdist: "d x \<le> d (x + y)"
  by simp

lemma dom_distrib: "d x + d y \<cdot> d z = (d x + d y) \<cdot> (d x + d z)"
proof -
  have "(d x + d y) \<cdot> (d x + d z) = d x \<cdot> (d x + d z) + d y \<cdot> (d x + d z)"
    using distrib_right' by blast
  also have "... = d x + (d x + d z) \<cdot> d y"
    by (metis (no_types) dns3 dns5 dsg4)
  also have "... = d x + d x \<cdot> d y + d z \<cdot> d y"
    using add_assoc' distrib_right' by presburger
  finally show ?thesis
    by (simp add: dsg4)
qed

lemma dom_llp1: "x \<le> d y \<cdot> x \<Longrightarrow> d x \<le> d y"
proof -
  assume "x \<le> d y \<cdot> x"
  hence "d x \<le> d (d y \<cdot> x)"
    using dom_iso by blast
  also have "... = d y \<cdot> d x"
    by simp
  finally show "d x \<le> d y"
    by (simp add: dom_glb_eq)
qed

lemma dom_llp2: "d x \<le> d y \<Longrightarrow> x \<le> d y \<cdot> x"
  using d_two_orders local.ds_dom_llp two_orders by blast

lemma dom_llp: "x \<le> d y \<cdot> x \<longleftrightarrow> d x \<le> d y"
  using dom_llp1 dom_llp2 by blast

end

text \<open>We expand domain near-semirings by an additive unit, using slightly different axioms.\<close>

class domain_near_semiring_one = ab_near_semiring_one + plus_ord + domain_op +
  assumes dnso1 [simp]: "x + d x \<cdot> x = d x \<cdot> x"
  and dnso2 [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
  and dnso3 [simp]: "d x + 1 = 1"
  and dnso4 [simp]: "d (x + y) = d x + d y"
  and dnso5: "d x \<cdot> d y = d y \<cdot> d x"

begin

text \<open>The previous axioms are derivable.\<close>

subclass domain_near_semiring
proof
  show a: "\<And>x. d x \<cdot> x = x"
    by (metis add_commute local.dnso3 local.distrib_right' local.dnso1 local.mult_onel)
  show "\<And>x y. d (x \<cdot> d y) = d (x \<cdot> y)"
    by simp
  show "\<And>x y. d (x + y) = d x + d y"
    by simp
  show "\<And>x y. d x \<cdot> d y = d y \<cdot> d x"
    by (simp add: dnso5)
  show "\<And>x y. d x \<cdot> (d x + d y) = d x"
  proof -
    fix x y
    have "\<And>x. 1 + d x = 1"
      using add_commute dnso3 by presburger
    thus "d x \<cdot> (d x + d y) = d x"
      by (metis (no_types) a dnso2 dnso4 dnso5 distrib_right' mult_onel)
  qed
qed

subclass domain_monoid ..

lemma dom_subid: "d x \<le> 1"
  by (simp add: less_eq_def)

end

text \<open>We add a left unit of multiplication.\<close>

class domain_near_semiring_one_zerol = ab_near_semiring_one_zerol + domain_near_semiring_one +
  assumes dnso6 [simp]: "d 0 = 0"

begin

lemma domain_very_strict: "d x = 0 \<longleftrightarrow> x = 0"
  by (metis annil dns1 dnso6)

lemma dom_weakly_local: "x \<cdot> y = 0 \<longleftrightarrow> x \<cdot> d y = 0"
proof -
  have "x \<cdot> y = 0 \<longleftrightarrow> d (x \<cdot> y) = 0"
    by (simp add: domain_very_strict)
  also have "... \<longleftrightarrow> d (x \<cdot> d y) = 0"
    by simp
  finally show ?thesis
    using domain_very_strict by blast
qed

end

subsection \<open>Domain Pre-Dioids\<close>

text \<open>
  Pre-semirings with one and a left zero are automatically dioids.
  Hence there is no point defining domain pre-semirings separately from domain dioids. The axioms
are once again from~\cite{DesharnaisStruthAMAST}.
\<close>

class domain_pre_dioid_one = pre_dioid_one + domain_op +
  assumes dpd1 : "x \<le> d x \<cdot> x"
  and dpd2 [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
  and dpd3 [simp]: "d x \<le> 1"
  and dpd4 [simp]: "d (x + y) = d x + d y"

begin

text \<open>We prepare to show that every domain pre-dioid with one is a domain near-dioid with one.\<close>

lemma dns1'' [simp]: "d x \<cdot> x = x"
proof (rule antisym)
  show "d x \<cdot> x \<le> x"
    using dpd3  mult_isor by fastforce
  show "x \<le> d x \<cdot> x "
    by (simp add: dpd1)
qed

lemma d_iso: "x \<le> y \<Longrightarrow> d x \<le> d y"
  by (metis dpd4 less_eq_def)

lemma domain_1'': "d (x \<cdot> y) \<le> d x"
proof -
  have "d (x \<cdot> y) = d (x \<cdot> d y)"
    by simp
  also have "... \<le> d (x \<cdot> 1)"
    by (meson d_iso dpd3 mult_isol)
  finally show ?thesis
    by simp
qed

lemma domain_export'' [simp]: "d (d x \<cdot> y) = d x \<cdot> d y"
proof (rule antisym)
  have one: "d (d x \<cdot> y) \<le> d x"
    by (metis dpd2 domain_1'' mult_onel)
  have two: "d (d x \<cdot> y) \<le> d y"
    using d_iso dpd3 mult_isor by fastforce
  have "d (d x \<cdot> y) = d (d (d x \<cdot> y)) \<cdot> d (d x \<cdot> y)"
    by simp
  also have "... = d (d x \<cdot> y) \<cdot> d (d x \<cdot> y)"
    by (metis dns1'' dpd2 mult_assoc)
  thus "d (d x \<cdot> y) \<le> d x \<cdot> d y"
    using mult_isol_var one two by force
next
  have "d x \<cdot> d y \<le> 1"
    by (metis dpd3  mult_1_right mult_isol order.trans)
  thus "d x \<cdot> d y \<le> d (d x \<cdot> y)"
    by (metis dns1'' dpd2 mult_isol mult_oner)
qed

lemma dom_subid_aux1'': "d x \<cdot> y \<le> y"
proof -
  have "d x \<cdot> y \<le> 1 \<cdot> y"
    using dpd3 mult_isor by blast
  thus ?thesis
    by simp
qed

lemma dom_subid_aux2'': "x \<cdot> d y \<le> x"
  using dpd3 mult_isol by fastforce

lemma d_comm: "d x \<cdot> d y = d y \<cdot> d x"
proof (rule antisym)
  have "d x \<cdot> d y = (d x \<cdot> d y) \<cdot> (d x \<cdot> d y)"
    by (metis dns1'' domain_export'')
  thus "d x \<cdot> d y \<le> d y \<cdot> d x"
    by (metis dom_subid_aux1'' dom_subid_aux2'' mult_isol_var)
next
  have "d y \<cdot> d x = (d y \<cdot> d x) \<cdot> (d y \<cdot> d x)"
    by (metis dns1'' domain_export'')
  thus "d y \<cdot> d x \<le> d x \<cdot> d y"
    by (metis dom_subid_aux1'' dom_subid_aux2'' mult_isol_var)
qed

subclass domain_near_semiring_one
  by (unfold_locales, auto simp: d_comm local.join.sup.absorb2)

lemma domain_subid: "x \<le> 1 \<Longrightarrow> x \<le> d x"
  by (metis dns1 mult_isol mult_oner)

lemma d_preserves_equation: "d y \<cdot> x \<le> x \<cdot> d z \<longleftrightarrow> d y \<cdot> x = d y \<cdot> x \<cdot> d z"
  by (metis dom_subid_aux2'' local.antisym local.dom_el_idem local.dom_subid_aux2 local.order_prop local.subdistl mult_assoc)

lemma d_restrict_iff: "(x \<le> y) \<longleftrightarrow> (x \<le> d x \<cdot> y)"
  by (metis dom_subid_aux2 dsg1 less_eq_def order_trans subdistl)

lemma d_restrict_iff_1: "(d x \<cdot> y \<le> z) \<longleftrightarrow> (d x \<cdot> y \<le> d x \<cdot> z)"
  by (metis dom_subid_aux2 domain_1'' domain_invol dsg1 mult_isol_var order_trans)

end

text \<open>We add once more a left unit of multiplication.\<close>

class domain_pre_dioid_one_zerol = domain_pre_dioid_one + pre_dioid_one_zerol +
  assumes dpd5 [simp]: "d 0 = 0"

begin

subclass domain_near_semiring_one_zerol
  by (unfold_locales, simp)

end

subsection \<open>Domain Semirings\<close>

text \<open>We do not consider domain semirings without units separately at the moment. The axioms are taken from from~\cite{DesharnaisStruthSCP}\<close>

class domain_semiringl = semiring_one_zerol + plus_ord + domain_op +
  assumes dsr1 [simp]: "x + d x \<cdot> x = d x \<cdot> x"
  and dsr2 [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
  and dsr3 [simp]: "d x + 1 = 1"
  and dsr4 [simp]: "d 0 = 0"
  and dsr5 [simp]: "d (x + y) = d x + d y"

begin

text \<open>Every domain semiring is automatically a domain pre-dioid with one and left zero.\<close>

subclass dioid_one_zerol
  by (standard, metis add_commute dsr1 dsr3 distrib_left mult_oner)

subclass domain_pre_dioid_one_zerol
  by (standard, auto simp: less_eq_def)

end

class domain_semiring = domain_semiringl + semiring_one_zero

subsection \<open>The Algebra of Domain Elements\<close>

text \<open>We show that the domain elements of a domain semiring form a distributive lattice. Unfortunately we cannot prove this within the type class of domain semirings.\<close>

typedef (overloaded)  'a d_element = "{x :: 'a :: domain_semiring. x = d x}"
  by (rule_tac x = 1 in exI, simp add: domain_subid order_class.eq_iff)

setup_lifting type_definition_d_element

instantiation d_element :: (domain_semiring) bounded_lattice

begin

lift_definition less_eq_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> bool" is "(<)" .

lift_definition bot_d_element :: "'a d_element" is 0
  by simp

lift_definition top_d_element :: "'a d_element" is 1
  by simp

lift_definition inf_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> 'a d_element" is "(\<cdot>)"
  by (metis dsg3)

lift_definition sup_d_element :: "'a d_element \<Rightarrow> 'a d_element \<Rightarrow> 'a d_element" is "(+)"
  by simp

instance
  apply (standard; transfer)
  apply (simp add: less_le_not_le)+
  apply (metis dom_subid_aux2'')
  apply (metis dom_subid_aux2)
  apply (metis dom_glb)
  apply simp+
  by (metis dom_subid)

end

instance d_element :: (domain_semiring) distrib_lattice
  by (standard, transfer, metis dom_distrib)

subsection \<open>Domain Semirings with a Greatest Element\<close>

text \<open>If there is a greatest element in the semiring, then we have another equality.\<close>

class domain_semiring_top = domain_semiring + order_top

begin

notation top ("\<top>")

lemma kat_equivalence_greatest: "d x \<le> d y \<longleftrightarrow> x \<le> d y \<cdot> \<top>"
proof
  assume "d x \<le> d y"
  thus "x \<le> d y \<cdot> \<top>"
    by (metis dsg1 mult_isol_var top_greatest)
next
  assume "x \<le> d y \<cdot> \<top>"
  thus "d x \<le> d y"
    using dom_glb_eq dom_iso by fastforce
qed

end

subsection \<open>Forward Diamond Operators\<close>

context domain_semiringl

begin

text \<open>We define a forward diamond operator over a domain semiring. A more modular consideration is not given at the moment.\<close>

definition fd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("( |_\<rangle> _)" [61,81] 82) where
  "|x\<rangle> y = d (x \<cdot> y)"

lemma fdia_d_simp [simp]: "|x\<rangle> d y = |x\<rangle> y"
  by (simp add: fd_def)

lemma fdia_dom [simp]: "|x\<rangle> 1 = d x"
  by (simp add: fd_def)

lemma fdia_add1: "|x\<rangle> (y + z) = |x\<rangle> y + |x\<rangle> z"
  by (simp add: fd_def distrib_left)

lemma fdia_add2: "|x + y\<rangle> z = |x\<rangle> z + |y\<rangle> z"
  by (simp add: fd_def distrib_right)

lemma fdia_mult: "|x \<cdot> y\<rangle> z = |x\<rangle> |y\<rangle> z"
  by (simp add: fd_def mult_assoc)

lemma fdia_one [simp]: "|1\<rangle> x = d x"
  by (simp add: fd_def)

lemma fdemodalisation1: "d z \<cdot> |x\<rangle> y = 0 \<longleftrightarrow> d z \<cdot> x \<cdot> d y = 0"
proof -
  have "d z \<cdot> |x\<rangle> y = 0 \<longleftrightarrow> d z \<cdot> d (x \<cdot> y) = 0"
    by (simp add: fd_def)
  also have "... \<longleftrightarrow> d z \<cdot> x \<cdot> y = 0"
    by (metis annil dnso6 dsg1 dsg3 mult_assoc)
  finally show ?thesis
    using dom_weakly_local by auto
qed

lemma fdemodalisation2: "|x\<rangle> y \<le> d z \<longleftrightarrow> x \<cdot> d y \<le> d z \<cdot> x"
proof
  assume "|x\<rangle> y \<le> d z"
  hence a: "d (x \<cdot> d y) \<le> d z"
    by (simp add: fd_def)
  have "x \<cdot> d y = d (x \<cdot> d y) \<cdot> x \<cdot> d y"
    using dsg1 mult_assoc by presburger
  also have "... \<le> d z \<cdot> x \<cdot> d y"
    using a calculation dom_llp2 mult_assoc by auto
  finally show "x \<cdot> d y \<le> d z \<cdot> x"
    using dom_subid_aux2'' order_trans by blast
next
  assume "x \<cdot> d y \<le> d z \<cdot> x"
  hence "d (x \<cdot> d y) \<le> d (d z \<cdot> d x)"
    using dom_iso by fastforce
  also have "... \<le> d (d z)"
    using domain_1'' by blast
  finally show "|x\<rangle> y \<le> d z"
    by (simp add: fd_def)
qed

lemma fd_iso1: "d x \<le> d y \<Longrightarrow> |z\<rangle> x \<le> |z\<rangle> y"
  using fd_def local.dom_iso local.mult_isol by fastforce

lemma fd_iso2: "x \<le> y \<Longrightarrow> |x\<rangle> z \<le> |y\<rangle> z"
  by (simp add: fd_def dom_iso mult_isor)

lemma fd_zero_var [simp]: "|0\<rangle> x = 0"
  by (simp add: fd_def)

lemma fd_subdist_1: "|x\<rangle> y \<le> |x\<rangle> (y + z)"
  by (simp add: fd_iso1)

lemma fd_subdist_2: "|x\<rangle> (d y \<cdot> d z) \<le> |x\<rangle> y"
  by (simp add: fd_iso1 dom_subid_aux2'')

lemma fd_subdist: "|x\<rangle> (d y \<cdot> d z) \<le> |x\<rangle> y \<cdot> |x\<rangle> z"
  using fd_def fd_iso1 fd_subdist_2 dom_glb dom_subid_aux2 by auto

lemma fdia_export_1: "d y \<cdot> |x\<rangle> z = |d y \<cdot> x\<rangle> z"
  by (simp add: fd_def mult_assoc)

end

context domain_semiring

begin

lemma fdia_zero [simp]: "|x\<rangle> 0 = 0"
  by (simp add: fd_def)

end

subsection \<open>Domain Kleene Algebras\<close>

text \<open>We add the Kleene star to our considerations. Special domain axioms are not needed.\<close>

class domain_left_kleene_algebra = left_kleene_algebra_zerol + domain_semiringl

begin

lemma dom_star [simp]: "d (x\<^sup>\<star>) = 1"
proof -
  have "d (x\<^sup>\<star>) = d (1 + x \<cdot> x\<^sup>\<star>)"
    by simp
  also have "... = d 1 + d (x \<cdot> x\<^sup>\<star>)"
    using dns3 by blast
  finally show ?thesis
    using add_commute local.dsr3 by auto
qed

lemma fdia_star_unfold [simp]: "|1\<rangle> y + |x\<rangle> |x\<^sup>\<star>\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof -
  have "|1\<rangle> y + |x\<rangle> |x\<^sup>\<star>\<rangle> y = |1 + x \<cdot> x\<^sup>\<star>\<rangle> y"
    using local.fdia_add2 local.fdia_mult by presburger
  thus ?thesis
    by simp
qed

lemma fdia_star_unfoldr [simp]: "|1\<rangle> y + |x\<^sup>\<star>\<rangle> |x\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof -
  have "|1\<rangle> y + |x\<^sup>\<star>\<rangle> |x\<rangle> y = |1 + x\<^sup>\<star> \<cdot> x\<rangle> y"
    using fdia_add2 fdia_mult by presburger
  thus ?thesis
    by simp
qed

lemma fdia_star_unfold_var [simp]: "d y + |x\<rangle> |x\<^sup>\<star>\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof -
  have "d y + |x\<rangle> |x\<^sup>\<star>\<rangle> y = |1\<rangle> y + |x\<rangle> |x\<^sup>\<star>\<rangle> y"
    by simp
  also have "... = |1 + x \<cdot> x\<^sup>\<star>\<rangle> y"
    using fdia_add2 fdia_mult by presburger
  finally show ?thesis
    by simp
qed

lemma fdia_star_unfoldr_var [simp]: "d y + |x\<^sup>\<star>\<rangle> |x\<rangle> y = |x\<^sup>\<star>\<rangle> y"
proof -
  have "d y + |x\<^sup>\<star>\<rangle> |x\<rangle> y = |1\<rangle> y + |x\<^sup>\<star>\<rangle> |x\<rangle> y"
    by simp
  also have "... = |1 + x\<^sup>\<star> \<cdot> x\<rangle> y"
    using fdia_add2 fdia_mult by presburger
  finally show ?thesis
    by simp
qed

lemma fdia_star_induct_var: "|x\<rangle> y \<le> d y \<Longrightarrow> |x\<^sup>\<star>\<rangle> y \<le> d y"
proof -
  assume a1: "|x\<rangle> y \<le> d y"
  hence "x \<cdot> d y \<le> d y \<cdot> x"
    by (simp add: fdemodalisation2)
  hence "x\<^sup>\<star> \<cdot> d y \<le> d y \<cdot> x\<^sup>\<star>"
    by (simp add: star_sim1)
  thus ?thesis
    by (simp add: fdemodalisation2)
qed

lemma fdia_star_induct: "d z + |x\<rangle> y \<le> d y \<Longrightarrow> |x\<^sup>\<star>\<rangle> z \<le> d y"
proof -
  assume a: "d z + |x\<rangle> y \<le> d y"
  hence b: "d z \<le> d y" and c: "|x\<rangle> y \<le> d y"
    apply (simp add: local.join.le_supE)
    using a by auto
  hence d: "|x\<^sup>\<star>\<rangle> z \<le> |x\<^sup>\<star>\<rangle> y"
    using fd_def fd_iso1 by auto
  have "|x\<^sup>\<star>\<rangle> y \<le> d y"
    using c fdia_star_induct_var by blast
  thus ?thesis
    using d by fastforce
qed

lemma fdia_star_induct_eq: "d z + |x\<rangle> y = d y \<Longrightarrow> |x\<^sup>\<star>\<rangle> z \<le> d y"
  by (simp add: fdia_star_induct)

end

class domain_kleene_algebra = kleene_algebra + domain_semiring

begin

subclass domain_left_kleene_algebra ..

end

end
