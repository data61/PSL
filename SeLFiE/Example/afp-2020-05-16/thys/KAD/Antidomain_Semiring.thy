(* Title:      Antidomain Semirings
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Antidomain Semirings\<close>

theory Antidomain_Semiring
imports Domain_Semiring
begin

subsection \<open>Antidomain Monoids\<close>

text \<open>We axiomatise antidomain monoids, using the axioms of~\cite{DesharnaisJipsenStruth}.\<close>

class antidomain_op =
  fixes antidomain_op :: "'a \<Rightarrow> 'a" ("ad")

class antidomain_left_monoid = monoid_mult + antidomain_op +
  assumes am1 [simp]: "ad x \<cdot> x = ad 1"
  and am2: "ad x \<cdot> ad y = ad y \<cdot> ad x"
  and am3 [simp]: "ad (ad x) \<cdot> x = x"
  and am4 [simp]: "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
  and am5 [simp]: "ad (x \<cdot> y) \<cdot> x \<cdot> ad y = ad (x \<cdot> y) \<cdot> x"

begin

no_notation domain_op ("d")
no_notation zero_class.zero ("0")

text \<open>We define a zero element and operations of domain and addition.\<close>

definition a_zero :: "'a" ("0") where
  "0 = ad 1"

definition am_d :: "'a \<Rightarrow> 'a" ("d") where
   "d x = ad (ad x)"

definition am_add_op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65) where
  "x \<oplus> y \<equiv> ad (ad x \<cdot> ad y)"

lemma a_d_zero [simp]: "ad x \<cdot> d x = 0"
  by (metis am1 am2 a_zero_def am_d_def)

lemma a_d_one [simp]: "d x \<oplus> ad x = 1"
  by (metis am1 am3 mult_1_right am_d_def am_add_op_def)

lemma n_annil [simp]: "0 \<cdot> x = 0"
proof -
  have "0 \<cdot> x = d x \<cdot> ad x \<cdot> x"
    by (simp add: a_zero_def am_d_def)
  also have "... = d x \<cdot> 0"
    by (metis am1 mult_assoc a_zero_def)
  thus ?thesis
    by (metis am1 am2 am3 mult_assoc a_zero_def)
qed

lemma a_mult_idem [simp]: "ad x \<cdot> ad x = ad x"
proof -
  have "ad x \<cdot> ad x = ad (1 \<cdot> x) \<cdot> 1 \<cdot> ad x"
    by simp
  also have "... = ad (1 \<cdot> x) \<cdot> 1"
    using am5 by blast
  finally show ?thesis
    by simp
qed

lemma a_add_idem [simp]: "ad x \<oplus> ad x = ad x"
  by (metis am1 am3 am4 mult_1_right am_add_op_def)

text \<open>The next three axioms suffice to show that the domain elements form a Boolean algebra.\<close>

lemma a_add_comm: "x \<oplus> y = y \<oplus> x"
  using am2 am_add_op_def by auto

lemma a_add_assoc: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
proof -
  have "\<And>x y. ad x \<cdot> ad (x \<cdot> y) = ad x"
    by (metis a_mult_idem am2 am4 mult_assoc)
  thus ?thesis
    by (metis a_add_comm am_add_op_def local.am3 local.am4 mult_assoc)
qed

lemma huntington [simp]: "ad (x \<oplus> y) \<oplus> ad (x \<oplus> ad y) = ad x"
  using a_add_idem am_add_op_def by auto

lemma a_absorb1 [simp]: "(ad x \<oplus> ad y) \<cdot> ad x = ad x"
  by (metis a_add_idem a_mult_idem am4 mult_assoc am_add_op_def)

lemma a_absorb2 [simp]: "ad x \<oplus> ad x \<cdot> ad y = ad x"
proof -
  have "ad (ad x) \<cdot> ad (ad x \<cdot> ad y) = ad (ad x)"
    by (metis (no_types) a_mult_idem local.am4 local.mult.semigroup_axioms semigroup.assoc)
  then show ?thesis
    using a_add_idem am_add_op_def by auto
qed

text \<open>The distributivity laws remain to be proved; our proofs follow those of Maddux~\cite{Maddux}.\<close>

lemma prod_split [simp]: "ad x \<cdot> ad y \<oplus> ad x \<cdot> d y = ad x"
  using a_add_idem am_d_def am_add_op_def by auto

lemma sum_split [simp]: "(ad x \<oplus> ad y) \<cdot> (ad x \<oplus> d y) = ad x"
  using a_add_idem am_d_def am_add_op_def by fastforce

lemma a_comp_simp [simp]: "(ad x \<oplus> ad y) \<cdot> d x = ad y \<cdot> d x"
proof -
  have f1: "(ad x \<oplus> ad y) \<cdot> d x = ad (ad (ad x) \<cdot> ad (ad y)) \<cdot> ad (ad x) \<cdot> ad (ad (ad y))"
    by (simp add: am_add_op_def am_d_def)
  have f2: "ad y = ad (ad (ad y))"
    using a_add_idem am_add_op_def by auto
  have "ad y = ad (ad (ad x) \<cdot> ad (ad y)) \<cdot> ad y"
    by (metis (no_types) a_absorb1 a_add_comm am_add_op_def)
  then show ?thesis
    using f2 f1 by (simp add: am_d_def local.am2 local.mult.semigroup_axioms semigroup.assoc)
qed

lemma a_distrib1: "ad x \<cdot> (ad y \<oplus> ad z) = ad x \<cdot> ad y \<oplus> ad x \<cdot> ad z"
proof -
  have f1: "\<And>a. ad (ad (ad (a::'a)) \<cdot> ad (ad a)) = ad a"
    using a_add_idem am_add_op_def by auto
  have f2: "\<And>a aa. ad ((a::'a) \<cdot> aa) \<cdot> (a \<cdot> ad aa) = ad (a \<cdot> aa) \<cdot> a"
    using local.am5 mult_assoc by auto
  have f3: "\<And>a. ad (ad (ad (a::'a))) = ad a"
    using f1 by simp
  have "\<And>a. ad (a::'a) \<cdot> ad a = ad a"
    by simp
  then have "\<And>a aa. ad (ad (ad (a::'a) \<cdot> ad aa)) = ad aa \<cdot> ad a"
    using f3 f2 by (metis (no_types) local.am2 local.am4 mult_assoc)
  then have  "ad x \<cdot> (ad y \<oplus> ad z) = ad x \<cdot> (ad y \<oplus> ad z) \<cdot> ad y \<oplus> ad x \<cdot> (ad y \<oplus> ad z) \<cdot> d y"
    using am_add_op_def am_d_def local.am2 local.am4 by presburger
  also have "... = ad x \<cdot> ad y \<oplus> ad x \<cdot> (ad y \<oplus> ad z) \<cdot> d y"
    by (simp add: mult_assoc)
  also have "... = ad x \<cdot> ad y \<oplus> ad x \<cdot> ad z \<cdot> d y"
    by (simp add: mult_assoc)
  also have "... = ad x \<cdot> ad y \<oplus> ad x \<cdot> ad y \<cdot> ad z \<oplus> ad x \<cdot> ad z \<cdot> d y"
    by (metis a_add_idem a_mult_idem local.am4 mult_assoc am_add_op_def)
  also have "... = ad x \<cdot> ad y \<oplus> (ad x \<cdot> ad z \<cdot> ad y \<oplus> ad x \<cdot> ad z \<cdot> d y)"
    by (metis am2 mult_assoc a_add_assoc)
  finally show ?thesis
    by (metis a_add_idem a_mult_idem am4 am_d_def am_add_op_def)
qed

lemma a_distrib2: "ad x \<oplus> ad y \<cdot> ad z = (ad x \<oplus> ad y) \<cdot> (ad x \<oplus> ad z)"
proof -
  have f1: "\<And>a aa ab. ad (ad (ad (a::'a) \<cdot> ad aa) \<cdot> ad (ad a \<cdot> ad ab)) = ad a \<cdot> ad (ad (ad aa) \<cdot> ad (ad ab))"
    using a_distrib1 am_add_op_def by auto
  have "\<And>a. ad (ad (ad (a::'a))) = ad a"
    by (metis a_absorb2 a_mult_idem am_add_op_def)
  then have "ad (ad (ad x) \<cdot> ad (ad y)) \<cdot> ad (ad (ad x) \<cdot> ad (ad z)) = ad (ad (ad x) \<cdot> ad (ad y \<cdot> ad z))"
    using f1 by (metis (full_types))
  then show ?thesis
    by (simp add: am_add_op_def)
qed

lemma aa_loc [simp]: "d (x \<cdot> d y) = d (x \<cdot> y)"
proof -
  have f1: "x \<cdot> d y \<cdot> y = x \<cdot> y"
    by (metis am3 mult_assoc am_d_def)
  have f2: "\<And>w z. ad (w \<cdot> z) \<cdot> (w \<cdot> ad z) = ad (w \<cdot> z) \<cdot> w"
    by (metis am5 mult_assoc)
  hence f3: "\<And>z. ad (x \<cdot> y) \<cdot> (x \<cdot> z) = ad (x \<cdot> y) \<cdot> (x \<cdot> (ad (ad (ad y) \<cdot> y) \<cdot> z))"
    using f1 by (metis (no_types) mult_assoc am_d_def)
  have "ad (x \<cdot> ad (ad y)) \<cdot> (x \<cdot> y) = 0" using f1
    by (metis am1 mult_assoc n_annil a_zero_def am_d_def)
  thus ?thesis
    by (metis a_d_zero am_d_def f3 local.am1 local.am2 local.am3 local.am4)
qed

lemma a_loc [simp]: "ad (x \<cdot> d y) = ad (x \<cdot> y)"
proof -
  have "\<And>a. ad (ad (ad (a::'a))) = ad a"
    using am_add_op_def am_d_def prod_split by auto
  then show ?thesis
    by (metis (full_types) aa_loc am_d_def)
qed

lemma d_a_export [simp]: "d (ad x \<cdot> y) = ad x \<cdot> d y"
proof -
  have f1: "\<And>a aa. ad ((a::'a) \<cdot> ad (ad aa)) = ad (a \<cdot> aa)"
    using a_loc am_d_def by auto
  have "\<And>a. ad (ad (a::'a) \<cdot> a) = 1"
    using a_d_one am_add_op_def am_d_def by auto
  then have "\<And>a aa. ad (ad (ad (a::'a) \<cdot> ad aa)) = ad a \<cdot> ad aa"
    using f1 by (metis a_distrib2 am_add_op_def local.mult_1_left)
  then show ?thesis
    using f1 by (metis (no_types) am_d_def)
qed

text \<open>Every antidomain monoid is a domain monoid.\<close>

sublocale dm: domain_monoid am_d "(\<cdot>)" 1
  apply (unfold_locales)
  apply (simp add: am_d_def)
  apply simp
  using am_d_def d_a_export apply auto[1]
  by (simp add: am_d_def local.am2)

lemma ds_ord_iso1: "x \<sqsubseteq> y \<Longrightarrow> z \<cdot> x \<sqsubseteq> z \<cdot> y"
(*nitpick [expect=genuine]*)
oops

lemma a_very_costrict: "ad x = 1 \<longleftrightarrow> x = 0"
proof
  assume a: "ad x = 1"
  hence "0 = ad x \<cdot> x"
    using a_zero_def by force
  thus "x = 0"
    by (simp add: a)
next
  assume "x = 0"
  thus "ad x = 1"
    using a_zero_def am_d_def dm.dom_one by auto
qed

lemma a_weak_loc: "x \<cdot> y = 0 \<longleftrightarrow> x \<cdot> d y = 0"
proof -
  have "x \<cdot> y = 0 \<longleftrightarrow> ad (x \<cdot> y) = 1"
    by (simp add: a_very_costrict)
  also have "... \<longleftrightarrow> ad (x \<cdot> d y) = 1"
    by simp
  finally show ?thesis
    using a_very_costrict by blast
qed

lemma a_closure [simp]: "d (ad x) = ad x"
  using a_add_idem am_add_op_def am_d_def by auto

lemma a_d_mult_closure [simp]: "d (ad x \<cdot> ad y) = ad x \<cdot> ad y"
  by simp

lemma kat_3': "d x \<cdot> y \<cdot> ad z = 0 \<Longrightarrow> d x \<cdot> y = d x \<cdot> y \<cdot> d z"
  by (metis dm.dom_one local.am5 local.mult_1_left a_zero_def am_d_def)

lemma s4 [simp]: "ad x \<cdot> ad (ad x \<cdot> y) = ad x \<cdot> ad y"
proof -
  have "\<And>a aa. ad (a::'a) \<cdot> ad (ad aa) = ad (ad (ad a \<cdot> aa))"
    using am_d_def d_a_export by presburger
  then have "\<And>a aa. ad (ad (a::'a)) \<cdot> ad aa = ad (ad (ad aa \<cdot> a))"
    using local.am2 by presburger
  then show ?thesis
    by (metis a_comp_simp a_d_mult_closure am_add_op_def am_d_def local.am2)
qed

end

class antidomain_monoid = antidomain_left_monoid +
  assumes am6 [simp]: "x \<cdot> ad 1 = ad 1"

begin

lemma kat_3_equiv: "d x \<cdot> y \<cdot> ad z = 0 \<longleftrightarrow> d x \<cdot> y = d x \<cdot> y \<cdot> d z"
  apply standard
  apply (metis kat_3')
  by (simp add: mult_assoc a_zero_def am_d_def)

no_notation a_zero ("0")
no_notation am_d ("d")

end

subsection \<open>Antidomain Near-Semirings\<close>

text \<open>We define antidomain near-semirings. We do not consider units separately. The axioms are taken from~\cite{DesharnaisStruthAMAST}.\<close>

notation zero_class.zero ("0")

class antidomain_near_semiring = ab_near_semiring_one_zerol + antidomain_op + plus_ord +
  assumes ans1 [simp]: "ad x \<cdot> x = 0"
  and ans2 [simp]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and ans3 [simp]: "ad (ad x) + ad x = 1"
  and ans4 [simp]: "ad (x + y) = ad x \<cdot> ad y"

begin

definition ans_d :: "'a \<Rightarrow> 'a" ("d") where
   "d x = ad (ad x)"

lemma a_a_one [simp]: "d 1 = 1"
proof -
  have "d 1 = d 1 + 0"
    by simp
  also have "... = d 1 + ad 1"
    by (metis ans1 mult_1_right)
  finally show ?thesis
    by (simp add: ans_d_def)
qed

lemma a_very_costrict': "ad x = 1 \<longleftrightarrow> x = 0"
proof
  assume "ad x = 1"
  hence "x = ad x \<cdot> x"
    by simp
  thus "x = 0"
    by auto
next
  assume "x = 0"
  hence "ad x = ad 0"
    by blast
  thus "ad x = 1"
    by (metis a_a_one ans_d_def local.ans1 local.mult_1_right)
qed

lemma one_idem [simp]: "1 + 1 = 1"
proof -
  have "1 + 1 = d 1 + d 1"
    by simp
  also have "... = ad (ad 1 \<cdot> 1) + ad (ad 1 \<cdot> d 1)"
    using a_a_one ans_d_def by auto
  also have "... = ad (ad 1 \<cdot> d 1)"
    using ans_d_def local.ans2 by presburger
  also have "... = ad (ad 1 \<cdot> 1)"
    by simp
  also have "... = d 1"
    by (simp add: ans_d_def)
  finally show ?thesis
    by simp
qed

text \<open>Every antidomain near-semiring is automatically a dioid, and therefore ordered.\<close>

subclass near_dioid_one_zerol
proof
  show "\<And>x. x + x = x"
  proof -
    fix x
    have "x + x = 1 \<cdot> x + 1 \<cdot> x"
      by simp
    also have "... = (1 + 1) \<cdot> x"
      using distrib_right' by presburger
    finally show "x + x = x"
      by simp
  qed
qed

lemma d1_a [simp]: "d x \<cdot> x = x"
proof -
  have "x = (d x + ad x) \<cdot> x"
    by (simp add: ans_d_def)
  also have "... = d x \<cdot> x + ad x \<cdot> x"
    using distrib_right' by blast
  also have "... = d x \<cdot> x + 0"
    by simp
  finally show ?thesis
    by auto
qed

lemma a_comm: "ad x \<cdot> ad y = ad y \<cdot> ad x"
  using add_commute ans4 by fastforce

lemma a_subid: "ad x \<le> 1"
  using local.ans3 local.join.sup_ge2 by fastforce

lemma a_subid_aux1: "ad x \<cdot> y \<le> y"
  using a_subid mult_isor by fastforce

lemma a_subdist: "ad (x + y) \<le> ad x"
  by (metis a_subid_aux1 ans4 add_comm)

lemma a_antitone: "x \<le> y \<Longrightarrow> ad y \<le> ad x"
  using a_subdist local.order_prop by auto

lemma a_mul_d [simp]: "ad x \<cdot> d x = 0"
  by (metis a_comm ans_d_def local.ans1)

lemma a_gla1: "ad x \<cdot> y = 0 \<Longrightarrow> ad x \<le> ad y"
proof -
  assume "ad x \<cdot> y = 0"
  hence a: "ad x \<cdot> d y = 0"
    by (metis a_subid a_very_costrict' ans_d_def local.ans2 local.join.sup.order_iff)
  have "ad x = (d y + ad y ) \<cdot> ad x"
    by (simp add: ans_d_def)
  also have "... = d y \<cdot> ad x + ad y \<cdot> ad x"
    using distrib_right' by blast
  also have "... = ad x \<cdot> d y + ad x \<cdot> ad y"
    using a_comm ans_d_def by auto
  also have "... = ad x \<cdot> ad y"
    by (simp add: a)
  finally show "ad x \<le> ad y"
    by (metis a_subid_aux1)
qed

lemma a_gla2: "ad x \<le> ad y \<Longrightarrow> ad x \<cdot> y = 0"
proof -
  assume "ad x \<le> ad y"
  hence "ad x \<cdot> y \<le> ad y \<cdot> y"
    using mult_isor by blast
  thus ?thesis
    by (simp add: join.le_bot)
qed

lemma a2_eq [simp]: "ad (x \<cdot> d y) = ad (x \<cdot> y)"
proof (rule antisym)
  show "ad (x \<cdot> y) \<le> ad (x \<cdot> d y)"
    by (simp add: ans_d_def local.less_eq_def)
next
  show "ad (x \<cdot> d y) \<le> ad (x \<cdot> y)"
    by (metis a_gla1 a_mul_d ans1 d1_a mult_assoc)
qed

lemma a_export' [simp]: "ad (ad x \<cdot> y) = d x + ad y"
proof (rule antisym)
  have "ad (ad x \<cdot> y) \<cdot> ad x \<cdot> d y = 0"
    by (simp add: a_gla2 local.mult.semigroup_axioms semigroup.assoc)
  hence a: "ad (ad x \<cdot> y) \<cdot> d y \<le> ad (ad x)"
    by (metis a_comm a_gla1 ans4 mult_assoc ans_d_def)
  have "ad (ad x \<cdot> y) = ad (ad x \<cdot> y) \<cdot> d y + ad (ad x \<cdot> y) \<cdot> ad y"
    by (metis (no_types) add_commute ans3 ans4 distrib_right' mult_onel ans_d_def)
  thus "ad (ad x \<cdot> y) \<le> d x + ad y"
    by (metis a_subid_aux1 a join.sup_mono ans_d_def)
next
  show "d x + ad y \<le> ad (ad x \<cdot> y)"
    by (metis a2_eq a_antitone a_comm a_subid_aux1 join.sup_least ans_d_def)
qed

text \<open>Every antidomain near-semiring is a domain near-semiring.\<close>

sublocale dnsz: domain_near_semiring_one_zerol "(+)" "(\<cdot>)" 1 0 "ans_d" "(\<le>)" "(<)"
  apply (unfold_locales)
  apply simp
  using a2_eq ans_d_def apply auto[1]
  apply (simp add: a_subid ans_d_def local.join.sup_absorb2)
  apply (simp add: ans_d_def)
  apply (simp add: a_comm ans_d_def)
  using a_a_one a_very_costrict' ans_d_def by force

lemma a_idem [simp]: "ad x \<cdot> ad x = ad x"
proof -
  have "ad x = (d x + ad x ) \<cdot> ad x"
    by (simp add: ans_d_def)
  also have "... = d x \<cdot> ad x + ad x \<cdot> ad x"
    using distrib_right' by blast
  finally show ?thesis
    by (simp add: ans_d_def)
qed

lemma a_3_var [simp]: "ad x \<cdot> ad y \<cdot> (x + y) = 0"
  by (metis ans1 ans4)

lemma a_3 [simp]: "ad x \<cdot> ad y \<cdot> d (x + y) = 0"
  by (metis a_mul_d ans4)

lemma a_closure' [simp]: "d (ad x) = ad x"
proof -
  have "d (ad x) = ad (1 \<cdot> d x)"
    by (simp add: ans_d_def)
  also have "... = ad (1 \<cdot> x)"
    using a2_eq by blast
  finally show ?thesis
    by simp
qed

text \<open>The following counterexamples show that some of the antidomain monoid axioms do not need to hold.\<close>

lemma "x \<cdot> ad 1 = ad 1"
(*nitpick [expect=genuine]*)
oops

lemma "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
(*nitpick [expect=genuine]*)
oops

lemma "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
(*nitpick [expect=genuine]*)
oops

lemma phl_seq_inv: "d v \<cdot> x \<cdot> y \<cdot> ad w = 0 \<Longrightarrow> \<exists>z. d v \<cdot> x \<cdot> d z = 0 \<and> ad z \<cdot> y \<cdot> ad w = 0"
proof -
  assume "d v \<cdot> x \<cdot> y \<cdot> ad w = 0"
  hence "d v \<cdot> x \<cdot> d (y \<cdot> ad w) = 0 \<and> ad (y \<cdot> ad w) \<cdot> y \<cdot> ad w = 0"
    by (metis dnsz.dom_weakly_local local.ans1 mult_assoc)
  thus "\<exists>z. d v \<cdot> x \<cdot> d z = 0 \<and> ad z \<cdot> y \<cdot> ad w = 0"
    by blast
qed

lemma a_fixpoint: "ad x = x \<Longrightarrow> (\<forall>y. y = 0)"
proof -
  assume a1: "ad x = x"
  { fix aa :: 'a
    have "aa = 0"
      using a1 by (metis (no_types) a_mul_d ans_d_def local.annil local.ans3 local.join.sup.idem local.mult_1_left)
  }
  then show ?thesis
    by blast
qed

no_notation ans_d ("d")

end

subsection \<open>Antidomain Pre-Dioids\<close>

text \<open>Antidomain pre-diods are based on a different set of axioms, which are again taken from~\cite{DesharnaisStruthAMAST}.\<close>

class antidomain_pre_dioid = pre_dioid_one_zerol + antidomain_op +
  assumes apd1 [simp]: "ad x \<cdot> x = 0"
  and apd2 [simp]: "ad (x \<cdot> y) \<le> ad (x \<cdot> ad (ad y))"
  and apd3 [simp]: "ad (ad x) + ad x = 1"

begin

definition apd_d :: "'a \<Rightarrow> 'a" ("d") where
   "d x = ad (ad x)"

lemma a_very_costrict'': "ad x = 1 \<longleftrightarrow> x = 0"
  by (metis add_commute local.add_zerol local.antisym local.apd1 local.apd3 local.join.bot_least local.mult_1_right local.phl_skip)

lemma a_subid': "ad x \<le> 1"
  using local.apd3 local.join.sup_ge2 by fastforce

lemma d1_a' [simp]: "d x \<cdot> x = x"
proof -
  have "x = (d x + ad x) \<cdot> x"
    by (simp add: apd_d_def)
  also have "... = d x \<cdot> x + ad x \<cdot> x"
    using distrib_right' by blast
  also have "... = d x \<cdot> x + 0"
    by simp
  finally show ?thesis
    by auto
qed

lemma a_subid_aux1': "ad x \<cdot> y \<le> y"
  using a_subid' mult_isor by fastforce

lemma a_mul_d' [simp]: "ad x \<cdot> d x = 0"
proof -
  have "1 = ad (ad x \<cdot> x)"
    using a_very_costrict'' by force
  thus ?thesis
    by (metis a_subid' a_very_costrict'' apd_d_def local.antisym local.apd2)
qed

lemma a_d_closed [simp]: "d (ad x) = ad x"
proof (rule antisym)
  have "d (ad x) = (d x + ad x) \<cdot> d (ad x)"
    by (simp add: apd_d_def)
  also have "... = ad (ad x) \<cdot> ad (d x) + ad x \<cdot> d (ad x)"
    using apd_d_def local.distrib_right' by presburger
  also have "... = ad x \<cdot> d (ad x)"
    using a_mul_d' apd_d_def by auto
      finally show "d (ad x) \<le> ad x"
    by (metis a_subid' mult_1_right mult_isol apd_d_def)
next
  have "ad x = ad (1 \<cdot> x)"
    by simp
  also have "... \<le> ad (1 \<cdot> d x)"
    using apd_d_def local.apd2 by presburger
  also have "... = ad (d x)"
    by simp
  finally show "ad x \<le> d (ad x)"
   by (simp add: apd_d_def)
qed

lemma meet_ord_def: "ad x \<le> ad y \<longleftrightarrow> ad x \<cdot> ad y = ad x"
  by (metis a_d_closed a_subid_aux1' d1_a' eq_iff mult_1_right mult_isol)

lemma d_weak_loc: "x \<cdot> y = 0 \<longleftrightarrow> x \<cdot> d y = 0"
proof -
  have "x \<cdot> y = 0 \<longleftrightarrow> ad (x \<cdot> y) = 1"
    by (simp add: a_very_costrict'')
  also have "... \<longleftrightarrow> ad (x \<cdot> d y) = 1"
    by (metis apd1 apd2 a_subid' apd_d_def d1_a' eq_iff mult_1_left mult_assoc)
  finally show ?thesis
    by (simp add: a_very_costrict'')
qed

lemma gla_1: "ad x \<cdot> y = 0 \<Longrightarrow> ad x \<le> ad y"
proof -
  assume "ad x \<cdot> y = 0"
  hence a: "ad x \<cdot> d y = 0"
    using d_weak_loc by force
  hence "d y = ad x \<cdot> d y + d y"
    by simp
  also have "... = (1 + ad x) \<cdot> d y"
    using join.sup_commute by auto
  also have "... = (d x + ad x) \<cdot> d y"
    using apd_d_def calculation by auto
  also have "... = d x \<cdot> d y"
    by (simp add: a join.sup_commute)
  finally have "d y \<le> d x"
    by (metis apd_d_def a_subid' mult_1_right mult_isol)
  hence "d y \<cdot> ad x = 0"
    by (metis apd_d_def a_d_closed a_mul_d' distrib_right' less_eq_def no_trivial_inverse)
  hence "ad x = ad y \<cdot> ad x"
    by (metis apd_d_def apd3 add_0_left distrib_right' mult_1_left)
  thus "ad x \<le> ad y"
    by (metis add_commute apd3 mult_oner subdistl)
qed

lemma a2_eq' [simp]: "ad (x \<cdot> d y) = ad (x \<cdot> y)"
proof (rule antisym)
  show "ad (x \<cdot> y) \<le> ad (x \<cdot> d y)"
    by (simp add: apd_d_def)
next
  show "ad (x \<cdot> d y) \<le> ad (x \<cdot> y)"
    by (metis gla_1 apd1 a_mul_d' d1_a' mult_assoc)
qed

lemma a_supdist_var: "ad (x + y) \<le> ad x"
  by (metis gla_1 apd1 join.le_bot subdistl)

lemma a_antitone': "x \<le> y \<Longrightarrow> ad y \<le> ad x"
  using a_supdist_var local.order_prop by auto

lemma a_comm_var: "ad x \<cdot> ad y \<le> ad y \<cdot> ad x"
proof -
  have "ad x \<cdot> ad y = d (ad x \<cdot> ad y) \<cdot> ad x \<cdot> ad y"
    by (simp add: mult_assoc)
  also have "... \<le> d (ad x \<cdot> ad y) \<cdot> ad x"
    using a_subid' mult_isol by fastforce
  also have "... \<le> d (ad y) \<cdot> ad x"
    by (simp add: a_antitone' a_subid_aux1' apd_d_def local.mult_isor)
  finally show ?thesis
    by simp
qed

lemma a_comm': "ad x \<cdot> ad y = ad y \<cdot> ad x"
  by (simp add: a_comm_var eq_iff)

lemma a_closed [simp]: "d (ad x \<cdot> ad y) = ad x \<cdot> ad y"
proof -
  have f1: "\<And>x y. ad x \<le> ad (ad y \<cdot> x)"
    by (simp add: a_antitone' a_subid_aux1')
  have "\<And>x y. d (ad x \<cdot> y) \<le> ad x"
    by (metis a2_eq' a_antitone' a_comm' a_d_closed apd_d_def f1)
  hence "\<And>x y. d (ad x \<cdot> y) \<cdot> y = ad x \<cdot> y"
    by (metis d1_a' meet_ord_def mult_assoc apd_d_def)
  thus ?thesis
    by (metis f1 a_comm' apd_d_def meet_ord_def)
qed

lemma a_export'' [simp]: "ad (ad x \<cdot> y) = d x + ad y"
proof (rule antisym)
  have "ad (ad x \<cdot> y) \<cdot> ad x \<cdot> d y = 0"
    using d_weak_loc mult_assoc by fastforce
  hence a: "ad (ad x \<cdot> y) \<cdot> d y \<le> d x"
    by (metis a_closed a_comm' apd_d_def gla_1 mult_assoc)
  have "ad (ad x \<cdot> y) = ad (ad x \<cdot> y) \<cdot> d y + ad (ad x \<cdot> y) \<cdot> ad y"
    by (metis apd3 a_comm' d1_a' distrib_right' mult_1_right apd_d_def)
  thus "ad (ad x \<cdot> y) \<le> d x + ad y"
    by (metis a_subid_aux1' a join.sup_mono)
next
  have "ad y \<le> ad (ad x \<cdot> y)"
    by (simp add: a_antitone' a_subid_aux1')
  thus "d x + ad y \<le> ad (ad x \<cdot> y)"
    by (metis apd_d_def a_mul_d' d1_a' gla_1 apd1 join.sup_least mult_assoc)
qed

lemma d1_sum_var: "x + y \<le> (d x + d y) \<cdot> (x + y)"
proof -
  have "x + y = d x \<cdot> x + d y \<cdot> y"
    by simp
  also have "... \<le> (d x + d y) \<cdot> x + (d x + d y) \<cdot> y"
    using local.distrib_right' local.join.sup_ge1 local.join.sup_ge2 local.join.sup_mono by presburger
  finally show ?thesis
    using order_trans subdistl_var by blast
qed

lemma a4': "ad (x + y) = ad x \<cdot> ad y"
proof (rule antisym)
  show "ad (x + y) \<le> ad x \<cdot> ad y"
    by (metis a_d_closed a_supdist_var add_commute d1_a' local.mult_isol_var)
  hence "ad x \<cdot> ad y = ad x \<cdot> ad y + ad (x + y)"
    using less_eq_def add_commute by simp
  also have "... = ad (ad (ad x \<cdot> ad y) \<cdot> (x + y))"
    by (metis a_closed a_export'')
  finally show "ad x \<cdot> ad y \<le> ad (x + y)"
    using a_antitone' apd_d_def d1_sum_var by auto
qed

text \<open>Antidomain pre-dioids are domain pre-dioids and antidomain near-semirings, but still not antidomain monoids.\<close>

sublocale dpdz: domain_pre_dioid_one_zerol "(+)" "(\<cdot>)" 1 0 "(\<le>)" "(<)" "\<lambda>x. ad (ad x)"
  apply (unfold_locales)
  using apd_d_def d1_a' apply auto[1]
  using a2_eq' apd_d_def apply auto[1]
  apply (simp add: a_subid')
  apply (simp add: a4' apd_d_def)
  by (metis a_mul_d' a_very_costrict'' apd_d_def local.mult_onel)

subclass antidomain_near_semiring
  apply (unfold_locales)
  apply simp
  using local.apd2 local.less_eq_def apply blast
  apply simp
  by (simp add: a4')

lemma a_supdist: "ad (x + y) \<le> ad x + ad y"
  using a_supdist_var local.join.le_supI1 by auto

lemma a_gla: "ad x \<cdot> y = 0 \<longleftrightarrow> ad x \<le> ad y"
  using gla_1 a_gla2 by blast

lemma a_subid_aux2: "x \<cdot> ad y \<le> x"
  using a_subid' mult_isol by fastforce

lemma a42_var: "d x \<cdot> d y \<le> ad (ad x + ad y)"
  by (simp add: apd_d_def)

lemma d1_weak [simp]: "(d x + d y) \<cdot> x = x"
proof -
  have "(d x + d y) \<cdot> x = (1 + d y) \<cdot> x"
    by simp
  thus ?thesis
   by (metis add_commute apd_d_def dpdz.dnso3 local.mult_1_left)
qed

lemma "x \<cdot> ad 1 = ad 1"
(*nitpick [expect=genuine]*)
oops

lemma "ad x \<cdot> (y + z) = ad x \<cdot> y + ad x \<cdot> z"
(*nitpick [expect=genuine]*)
oops

lemma "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
(*nitpick [expect=genuine]*)
oops

lemma "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
(*nitpick [expect=genuine]*)
oops

no_notation apd_d ("d")

end

subsection \<open>Antidomain Semirings\<close>

text \<open>Antidomain semirings are direct expansions of antidomain pre-dioids, but do not require idempotency of addition. Hence we give a slightly different axiomatisation, following~\cite{DesharnaisStruthSCP}.\<close>

class antidomain_semiringl = semiring_one_zerol + plus_ord + antidomain_op +
  assumes as1 [simp]: "ad x \<cdot> x = 0"
  and as2 [simp]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and as3 [simp]: "ad (ad x) + ad x = 1"

begin

definition ads_d :: "'a \<Rightarrow> 'a" ("d") where
  "d x = ad (ad x)"

lemma one_idem': "1 + 1 = 1"
  by (metis as1 as2 as3 add_zeror mult.right_neutral)

text \<open>Every antidomain semiring is a dioid and an antidomain pre-dioid.\<close>

subclass dioid
  by (standard, metis distrib_left mult.right_neutral one_idem')

subclass antidomain_pre_dioid
  by (unfold_locales, auto simp: local.less_eq_def)

lemma am5_lem [simp]: "ad (x \<cdot> y) \<cdot> ad (x \<cdot> ad y) = ad x"
proof -
  have "ad (x \<cdot> y ) \<cdot> ad (x \<cdot> ad y) = ad (x \<cdot> d y) \<cdot> ad (x \<cdot> ad y)"
    using ads_d_def local.a2_eq' local.apd_d_def by auto
  also have "... = ad (x \<cdot> d y + x \<cdot> ad y)"
    using ans4 by presburger
  also have "... = ad (x \<cdot> (d y + ad y))"
    using distrib_left by presburger
  finally show ?thesis
    by (simp add: ads_d_def)
qed

lemma am6_lem [simp]: "ad (x \<cdot> y) \<cdot> x \<cdot> ad y = ad (x \<cdot> y) \<cdot> x"
proof -
  fix x y
  have "ad (x \<cdot> y) \<cdot> x \<cdot> ad y = ad (x \<cdot> y) \<cdot> x \<cdot> ad y + 0"
    by simp
  also have "... = ad (x \<cdot> y) \<cdot> x \<cdot> ad y + ad (x \<cdot> d y) \<cdot> x \<cdot> d y"
    using ans1 mult_assoc by presburger
  also have "... = ad (x \<cdot> y) \<cdot> x \<cdot> (ad y + d y)"
    using ads_d_def local.a2_eq' local.apd_d_def local.distrib_left by auto
  finally show "ad (x \<cdot> y) \<cdot> x \<cdot> ad y = ad (x \<cdot> y) \<cdot> x"
    using add_commute ads_d_def local.as3 by auto
qed

lemma a_zero [simp]: "ad 0 = 1"
  by (simp add: local.a_very_costrict'')

lemma a_one [simp]: "ad 1 = 0"
  using a_zero local.dpdz.dpd5 by blast

subclass antidomain_left_monoid
  by (unfold_locales, auto simp:  local.a_comm')

text \<open>Every antidomain left semiring is a domain left semiring.\<close>

no_notation domain_semiringl_class.fd ("( |_\<rangle> _)" [61,81] 82)

definition fdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("( |_\<rangle> _)" [61,81] 82) where
  "|x\<rangle> y = ad (ad (x \<cdot> y))"

sublocale ds: domain_semiringl "(+)" "(\<cdot>)" 1 0 "\<lambda>x. ad (ad x)" "(\<le>)" "(<)"
  rewrites "ds.fd x y \<equiv> fdia x y"
proof -
  show "class.domain_semiringl (+) (\<cdot>) 1 0 (\<lambda>x. ad (ad x)) (\<le>) (<) "
    by (unfold_locales, auto simp: local.dpdz.dpd4 ans_d_def)
  then interpret ds: domain_semiringl "(+)" "(\<cdot>)" 1 0 "\<lambda>x. ad (ad x)" "(\<le>)" "(<)" .
  show "ds.fd x y \<equiv> fdia x y"
    by (auto simp: fdia_def ds.fd_def)
qed

lemma fd_eq_fdia [simp]: "domain_semiringl.fd (\<cdot>) d x y \<equiv> fdia x y"
proof -
  have "class.domain_semiringl (+) (\<cdot>) 1 0 d (\<le>) (<)"
    by (unfold_locales, auto simp: ads_d_def local.ans_d_def)
  hence "domain_semiringl.fd (\<cdot>) d x y = d ((\<cdot>) x y)"
    by (rule domain_semiringl.fd_def)
  also have "... = ds.fd x y"
    by (simp add: ds.fd_def ads_d_def)
  finally show "domain_semiringl.fd (\<cdot>) d x y \<equiv> |x\<rangle> y"
    by auto
qed

end

class antidomain_semiring = antidomain_semiringl + semiring_one_zero

begin

text \<open>Every antidomain semiring is an antidomain monoid.\<close>

subclass antidomain_monoid
  by (standard, metis ans1 mult_1_right annir)

lemma "a_zero = 0"
  by (simp add: local.a_zero_def)

sublocale ds: domain_semiring "(+)" "(\<cdot>)" 1 0 "\<lambda>x. ad (ad x)" "(\<le>)" "(<)"
  rewrites "ds.fd x y \<equiv> fdia x y"
  by unfold_locales

end

subsection \<open>The Boolean Algebra of Domain Elements\<close>

typedef (overloaded) 'a a2_element = "{x :: 'a :: antidomain_semiring. x = d x}"
  by (rule_tac x=1 in exI, auto simp: ads_d_def)

setup_lifting type_definition_a2_element

instantiation a2_element :: (antidomain_semiring) boolean_algebra

begin

lift_definition less_eq_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element \<Rightarrow> bool" is "(<)" .

lift_definition bot_a2_element :: "'a a2_element" is 0
  by (simp add: ads_d_def)

lift_definition top_a2_element :: "'a a2_element" is 1
  by (simp add: ads_d_def)

lift_definition inf_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element \<Rightarrow> 'a a2_element" is "(\<cdot>)"
  by (metis (no_types, lifting) ads_d_def dpdz.dom_mult_closed)

lift_definition sup_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element \<Rightarrow> 'a a2_element" is "(+)"
  by (metis ads_d_def ds.dsr5)

lift_definition minus_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element \<Rightarrow> 'a a2_element" is "\<lambda>x y. x \<cdot> ad y"
  by (metis (no_types, lifting) ads_d_def dpdz.domain_export'')

lift_definition uminus_a2_element :: "'a a2_element \<Rightarrow> 'a a2_element" is antidomain_op
  by (simp add: ads_d_def)

instance
  apply (standard; transfer)
  apply (simp add: less_le_not_le)
  apply simp
  apply auto[1]
  apply simp
  apply (metis a_subid_aux2 ads_d_def)
  apply (metis a_subid_aux1' ads_d_def)
  apply (metis (no_types, lifting) ads_d_def dpdz.dom_glb)
  apply simp
  apply simp
  apply simp
  apply simp
  apply (metis a_subid' ads_d_def)
  apply (metis (no_types, lifting) ads_d_def dpdz.dom_distrib)
  apply (metis ads_d_def ans1)
  apply (metis ads_d_def ans3)
  by simp

end

subsection \<open>Further Properties\<close>

context antidomain_semiringl

begin

lemma a_2_var: "ad x \<cdot> d y = 0 \<longleftrightarrow> ad x \<le> ad y"
  using local.a_gla local.ads_d_def local.dpdz.dom_weakly_local by auto

text \<open>The following two lemmas give the Galois connection of Heyting algebras.\<close>

lemma da_shunt1: "x \<le> d y + z \<Longrightarrow> x \<cdot> ad y \<le> z"
proof -
  assume "x \<le> d y + z"
  hence "x \<cdot> ad y \<le> (d y + z) \<cdot> ad y"
    using mult_isor by blast
  also have "... = d y \<cdot> ad y + z \<cdot> ad y"
    by simp
  also have "... \<le> z"
    by (simp add: a_subid_aux2 ads_d_def)
  finally show "x \<cdot> ad y \<le> z"
    by simp
qed

lemma da_shunt2: "x \<le> ad y + z \<Longrightarrow> x \<cdot> d y \<le> z"
  using da_shunt1 local.a_add_idem local.ads_d_def am_add_op_def by auto

lemma d_a_galois1: "d x \<cdot> ad y \<le> d z \<longleftrightarrow> d x \<le> d z + d y"
  by (metis add_assoc local.a_gla local.ads_d_def local.am2 local.ans4 local.ans_d_def local.dnsz.dnso4)

lemma d_a_galois2: "d x \<cdot> d y \<le> d z \<longleftrightarrow> d x \<le> d z + ad y"
proof -
  have "\<And>a aa. ad ((a::'a) \<cdot> ad (ad aa)) = ad (a \<cdot> aa)"
    using local.a2_eq' local.apd_d_def by force
  then show ?thesis
    by (metis d_a_galois1 local.a_export' local.ads_d_def local.ans_d_def)
qed

lemma d_cancellation_1: "d x \<le> d y + d x \<cdot> ad y"
proof -
  have a: "d (d x \<cdot> ad y) = ad y \<cdot> d x"
    using local.a_closure' local.ads_d_def local.am2 local.ans_d_def by auto
  hence "d x \<le> d (d x \<cdot> ad y) + d y"
    using d_a_galois1 local.a_comm_var local.ads_d_def by fastforce
  thus ?thesis
    using a add_commute local.ads_d_def local.am2 by auto
qed

lemma d_cancellation_2: "(d z + d y) \<cdot> ad y \<le> d z"
  by (simp add: da_shunt1)

lemma a_de_morgan: "ad (ad x \<cdot> ad y) = d (x + y)"
  by (simp add: local.ads_d_def)

lemma a_de_morgan_var_3: "ad (d x + d y) = ad x \<cdot> ad y"
  using local.a_add_idem local.ads_d_def am_add_op_def by auto

lemma a_de_morgan_var_4: "ad (d x \<cdot> d y) = ad x + ad y"
  using local.a_add_idem local.ads_d_def am_add_op_def by auto

lemma a_4: "ad x \<le> ad (x \<cdot> y)"
  using local.a_add_idem local.a_antitone' local.dpdz.domain_1'' am_add_op_def by fastforce

lemma a_6: "ad (d x \<cdot> y) = ad x + ad y"
  using a_de_morgan_var_4 local.ads_d_def by auto

lemma a_7: "d x \<cdot> ad (d y + d z) = d x \<cdot> ad y \<cdot> ad z"
  using a_de_morgan_var_3 local.mult.semigroup_axioms semigroup.assoc by fastforce

lemma a_d_add_closure [simp]: "d (ad x + ad y) = ad x + ad y"
  using local.a_add_idem local.ads_d_def am_add_op_def by auto

lemma d_6 [simp]: "d x + ad x \<cdot> d y = d x + d y"
proof -
  have "ad (ad x \<cdot> (x + ad y)) = d (x + y)"
    by (simp add: distrib_left ads_d_def)
  thus ?thesis
    by (simp add: local.ads_d_def local.ans_d_def)
qed

lemma d_7 [simp]: "ad x + d x \<cdot> ad y = ad x + ad y"
  by (metis a_d_add_closure local.ads_d_def local.ans4 local.s4)

lemma a_mult_add: "ad x \<cdot> (y + x) = ad x \<cdot> y"
  by (simp add: distrib_left)

lemma kat_2: "y \<cdot> ad z \<le> ad x \<cdot> y \<Longrightarrow> d x \<cdot> y \<cdot> ad z = 0"
proof -
  assume a: "y \<cdot> ad z \<le> ad x \<cdot> y"
  hence "d x \<cdot> y \<cdot> ad z \<le> d x \<cdot> ad x \<cdot> y"
    using local.mult_isol mult_assoc by presburger
  thus ?thesis
    using local.join.le_bot ads_d_def by auto
qed

lemma kat_3: "d x \<cdot> y \<cdot> ad z = 0 \<Longrightarrow> d x \<cdot> y = d x \<cdot> y \<cdot> d z"
  using local.a_zero_def local.ads_d_def local.am_d_def local.kat_3' by auto

lemma kat_4: "d x \<cdot> y = d x \<cdot> y \<cdot> d z \<Longrightarrow> d x \<cdot> y \<le> y \<cdot> d z"
  using a_subid_aux1 mult_assoc ads_d_def by auto

lemma kat_2_equiv: "y \<cdot> ad z \<le> ad x \<cdot> y \<longleftrightarrow> d x \<cdot> y \<cdot> ad z = 0"
proof
  assume "y \<cdot> ad z \<le> ad x \<cdot> y"
  thus "d x \<cdot> y \<cdot> ad z = 0"
    by (simp add: kat_2)
next
  assume 1: "d x \<cdot> y \<cdot> ad z = 0"
  have "y \<cdot> ad z = (d x + ad x) \<cdot> y \<cdot> ad z"
    by (simp add: local.ads_d_def)
  also have "... = d x \<cdot> y \<cdot> ad z + ad x \<cdot> y \<cdot> ad z"
    using local.distrib_right by presburger
  also have "... = ad x \<cdot> y \<cdot> ad z"
    using "1" by auto
  also have "... \<le> ad x \<cdot> y"
    by (simp add: local.a_subid_aux2)
  finally show "y \<cdot> ad z \<le> ad x \<cdot> y" .
qed

lemma kat_4_equiv: "d x \<cdot> y = d x \<cdot> y \<cdot> d z \<longleftrightarrow> d x \<cdot> y \<le> y \<cdot> d z"
  using local.ads_d_def local.dpdz.d_preserves_equation by auto

lemma kat_3_equiv_opp: "ad z \<cdot> y \<cdot> d x = 0 \<longleftrightarrow> y \<cdot> d x = d z \<cdot> y \<cdot> d x"
proof -
  have "ad z \<cdot> (y \<cdot> d x) = 0 \<longrightarrow> (ad z \<cdot> y \<cdot> d x = 0) = (y \<cdot> d x = d z \<cdot> y \<cdot> d x)"
    by (metis (no_types, hide_lams) add_commute local.add_zerol local.ads_d_def local.as3 local.distrib_right' local.mult_1_left mult_assoc)
  thus ?thesis
    by (metis a_4 local.a_add_idem local.a_gla2 local.ads_d_def mult_assoc am_add_op_def)
qed

lemma kat_4_equiv_opp: "y \<cdot> d x = d z \<cdot> y \<cdot> d x \<longleftrightarrow> y \<cdot> d x \<le> d z \<cdot> y"
  using kat_2_equiv kat_3_equiv_opp local.ads_d_def by auto

subsection \<open>Forward Box and Diamond Operators\<close>

lemma fdemodalisation22: "|x\<rangle> y \<le> d z \<longleftrightarrow> ad z \<cdot> x \<cdot> d y = 0"
proof -
  have "|x\<rangle> y \<le> d z \<longleftrightarrow> d (x \<cdot> y) \<le> d z"
    by (simp add: fdia_def ads_d_def)
  also have "... \<longleftrightarrow> ad z \<cdot> d (x \<cdot> y) = 0"
    by (metis add_commute local.a_gla local.ads_d_def local.ans4)
  also have "... \<longleftrightarrow> ad z \<cdot> x \<cdot> y = 0"
    using dpdz.dom_weakly_local mult_assoc ads_d_def by auto
  finally show ?thesis
    using dpdz.dom_weakly_local ads_d_def by auto
qed

lemma dia_diff_var: "|x\<rangle> y \<le> |x\<rangle> (d y \<cdot> ad z) + |x\<rangle> z"
proof -
  have 1: "|x\<rangle> (d y \<cdot> d z) \<le> |x\<rangle> (1 \<cdot> d z)"
    using dpdz.dom_glb_eq ds.fd_subdist fdia_def ads_d_def by force
  have "|x\<rangle> y = |x\<rangle> (d y \<cdot> (ad z + d z))"
    by (metis as3 add_comm ds.fdia_d_simp mult_1_right ads_d_def)
  also have "... = |x\<rangle> (d y \<cdot> ad z) + |x\<rangle> (d y \<cdot> d z)"
    by (simp add: local.distrib_left local.ds.fdia_add1)
  also have "... \<le> |x\<rangle> (d y \<cdot> ad z) + |x\<rangle> (1 \<cdot> d z)"
    using "1" local.join.sup.mono by blast
  finally show ?thesis
    by (simp add: fdia_def ads_d_def)
qed

lemma dia_diff: "|x\<rangle> y \<cdot> ad ( |x\<rangle> z ) \<le> |x\<rangle> (d y \<cdot> ad z)"
  using fdia_def dia_diff_var d_a_galois2 ads_d_def by metis

lemma fdia_export_2: "ad y \<cdot> |x\<rangle> z = |ad y \<cdot> x\<rangle> z"
  using local.am_d_def local.d_a_export local.fdia_def mult_assoc by auto

lemma fdia_split: "|x\<rangle> y = d z \<cdot> |x\<rangle> y + ad z \<cdot> |x\<rangle> y"
  by (metis mult_onel ans3 distrib_right ads_d_def)

definition fbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("( |_] _)" [61,81] 82) where
  "|x] y = ad (x \<cdot> ad y)"

text \<open>The next lemmas establish the De Morgan duality between boxes and diamonds.\<close>

lemma fdia_fbox_de_morgan_2: "ad ( |x\<rangle> y) = |x] ad y"
  using fbox_def local.a_closure local.a_loc local.am_d_def local.fdia_def by auto

lemma fbox_simp: "|x] y = |x] d y"
  using fbox_def local.a_add_idem local.ads_d_def am_add_op_def by auto

lemma fbox_dom [simp]: "|x] 0 = ad x"
  by (simp add: fbox_def)

lemma fbox_add1: "|x] (d y \<cdot> d z) = |x] y \<cdot> |x] z"
  using a_de_morgan_var_4 fbox_def local.distrib_left by auto

lemma fbox_add2: "|x + y] z = |x] z \<cdot> |y] z"
  by (simp add: fbox_def)

lemma fbox_mult: "|x \<cdot> y] z = |x] |y] z"
  using fbox_def local.a2_eq' local.apd_d_def mult_assoc by auto

lemma fbox_zero [simp]: "|0] x = 1"
  by (simp add: fbox_def)

lemma fbox_one [simp]: "|1] x = d x"
  by (simp add: fbox_def ads_d_def)

lemma fbox_iso: "d x \<le> d y \<Longrightarrow> |z] x \<le> |z] y"
proof -
  assume "d x \<le> d y"
  hence "ad y \<le> ad x"
    using local.a_add_idem local.a_antitone' local.ads_d_def am_add_op_def by fastforce
  hence "z \<cdot> ad y \<le> z \<cdot> ad x"
    by (simp add: mult_isol)
  thus "|z] x \<le> |z] y"
    by (simp add: fbox_def a_antitone')
qed

lemma fbox_antitone_var: "x \<le> y \<Longrightarrow> |y] z \<le> |x] z"
  by (simp add: fbox_def a_antitone mult_isor)

lemma fbox_subdist_1: "|x] (d y \<cdot> d z) \<le> |x] y"
  using a_de_morgan_var_4 fbox_def local.a_supdist_var local.distrib_left by force

lemma fbox_subdist_2: "|x] y \<le>|x] (d y + d z)"
  by (simp add: fbox_iso ads_d_def)

lemma fbox_subdist: "|x] d y + |x] d z \<le> |x] (d y + d z)"
  by (simp add: fbox_iso sup_least ads_d_def)

lemma fbox_diff_var: "|x] (d y + ad z) \<cdot> |x] z \<le> |x] y"
proof -
  have "ad (ad y) \<cdot> ad (ad z) = ad (ad z + ad y)"
    using local.dpdz.dsg4 by auto
  then have "d (d (d y + ad z) \<cdot> d z) \<le> d y"
    by (simp add: local.a_subid_aux1' local.ads_d_def)
  then show ?thesis
    by (metis fbox_add1 fbox_iso)
qed

lemma fbox_diff: "|x] (d y + ad z) \<le> |x] y + ad ( |x] z )"
proof -
  have f1: "\<And>a. ad (ad (ad (a::'a))) = ad a"
    using local.a_closure' local.ans_d_def by force
  have f2: "\<And>a aa. ad (ad (a::'a)) + ad aa = ad (ad a \<cdot> aa)"
    using local.ans_d_def by auto
  have f3: "\<And>a aa. ad ((a::'a) + aa) = ad (aa + a)"
    by (simp add: local.am2)
  then have f4: "\<And>a aa. ad (ad (ad (a::'a) \<cdot> aa)) = ad (ad aa + a)"
    using f2 f1 by (metis (no_types) local.ans4)
  have f5: "\<And>a aa ab. ad ((a::'a) \<cdot> (aa + ab)) = ad (a \<cdot> (ab + aa))"
    using f3 local.distrib_left by presburger
  have f6: "\<And>a aa. ad (ad (ad (a::'a) + aa)) = ad (ad aa \<cdot> a)"
    using f3 f1 by fastforce
  have "ad (x \<cdot> ad (y + ad z)) \<le> ad (ad (x \<cdot> ad z) \<cdot> (x \<cdot> ad y))"
    using f5 f2 f1 by (metis (no_types) a_mult_add fbox_def fbox_subdist_1 local.a_gla2 local.ads_d_def local.ans4 local.distrib_left local.gla_1 mult_assoc)
  then show ?thesis
    using f6 f4 f3 f1 by (simp add: fbox_def local.ads_d_def)
qed

end

context antidomain_semiring

begin

lemma kat_1: "d x \<cdot> y \<le> y \<cdot> d z \<Longrightarrow> y \<cdot> ad z \<le> ad x \<cdot> y"
proof -
  assume a: "d x \<cdot> y \<le> y \<cdot> d z"
  have "y \<cdot> ad z = d x \<cdot> y \<cdot> ad z + ad x \<cdot> y \<cdot> ad z"
    by (metis local.ads_d_def local.as3 local.distrib_right local.mult_1_left)
  also have "... \<le> y \<cdot> (d z \<cdot> ad z) + ad x \<cdot> y \<cdot> ad z"
    by (metis a add_iso mult_isor mult_assoc)
  also have "... = ad x \<cdot> y \<cdot> ad z"
    by (simp add: ads_d_def)
  finally show "y \<cdot> ad z \<le> ad x \<cdot> y"
    using local.a_subid_aux2 local.dual_order.trans by blast
qed

lemma kat_1_equiv: "d x \<cdot> y \<le> y \<cdot> d z \<longleftrightarrow> y \<cdot> ad z \<le> ad x \<cdot> y"
  using kat_1 kat_2 kat_3 kat_4 by blast

lemma kat_3_equiv': "d x \<cdot> y \<cdot> ad z = 0 \<longleftrightarrow> d x \<cdot> y = d x \<cdot> y \<cdot> d z"
  by (simp add: kat_1_equiv local.kat_2_equiv local.kat_4_equiv)

lemma kat_1_equiv_opp: "y \<cdot> d x \<le> d z \<cdot> y \<longleftrightarrow> ad z \<cdot> y \<le> y \<cdot> ad x"
  by (metis kat_1_equiv local.a_closure' local.ads_d_def local.ans_d_def)

lemma kat_2_equiv_opp: "ad z \<cdot> y \<le> y \<cdot> ad x \<longleftrightarrow> ad z \<cdot> y \<cdot> d x = 0"
  by (simp add: kat_1_equiv_opp local.kat_3_equiv_opp local.kat_4_equiv_opp)

lemma fbox_one_1 [simp]: "|x] 1 = 1"
  by (simp add: fbox_def)

lemma fbox_demodalisation3: "d y \<le> |x] d z \<longleftrightarrow> d y \<cdot> x \<le> x \<cdot> d z"
  by (simp add: fbox_def a_gla kat_2_equiv_opp mult_assoc ads_d_def)

end

subsection \<open>Antidomain Kleene Algebras\<close>

class antidomain_left_kleene_algebra = antidomain_semiringl + left_kleene_algebra_zerol

begin

sublocale dka: domain_left_kleene_algebra "(+)" "(\<cdot>)" 1 0 d "(\<le>)" "(<)" star
  rewrites "domain_semiringl.fd (\<cdot>) d x y \<equiv> |x\<rangle> y"
  by (unfold_locales, auto simp add: local.ads_d_def ans_d_def)

lemma a_star [simp]: "ad (x\<^sup>\<star>) = 0"
  using dka.dom_star local.a_very_costrict'' local.ads_d_def by force

lemma fbox_star_unfold [simp]: "|1] z \<cdot> |x] |x\<^sup>\<star>] z = |x\<^sup>\<star>] z"
proof -
  have "ad (ad z + x \<cdot> (x\<^sup>\<star> \<cdot> ad z)) = ad (x\<^sup>\<star> \<cdot> ad z)"
    using local.conway.dagger_unfoldl_distr mult_assoc by auto
  then show ?thesis
    using local.a_closure' local.ans_d_def local.fbox_def local.fdia_def local.fdia_fbox_de_morgan_2 by fastforce
qed

lemma fbox_star_unfold_var [simp]: "d z \<cdot> |x] |x\<^sup>\<star>] z = |x\<^sup>\<star>] z"
  using fbox_star_unfold by auto

lemma fbox_star_unfoldr [simp]: "|1] z \<cdot> |x\<^sup>\<star>] |x] z = |x\<^sup>\<star>] z"
  by (metis fbox_star_unfold fbox_mult star_slide_var)

lemma fbox_star_unfoldr_var [simp]: "d z \<cdot> |x\<^sup>\<star>] |x] z = |x\<^sup>\<star>] z"
  using fbox_star_unfoldr by auto

lemma fbox_star_induct_var: "d y \<le> |x] y \<Longrightarrow> d y \<le> |x\<^sup>\<star>] y"
proof -
  assume a1: "d y \<le> |x] y"
  have "\<And>a. ad (ad (ad (a::'a))) = ad a"
    using local.a_closure' local.ans_d_def by auto
  then have "ad (ad (x\<^sup>\<star> \<cdot> ad y)) \<le> ad y"
    using a1 by (metis dka.fdia_star_induct local.a_export' local.ads_d_def local.ans4 local.ans_d_def local.eq_refl local.fbox_def local.fdia_def local.meet_ord_def)
  then have "ad (ad y + ad (x\<^sup>\<star> \<cdot> ad y)) = zero_class.zero"
    by (metis (no_types) add_commute local.a_2_var local.ads_d_def local.ans4)
  then show ?thesis
    using local.a_2_var local.ads_d_def local.fbox_def by auto
qed

lemma fbox_star_induct: "d y \<le> d z \<cdot> |x] y \<Longrightarrow> d y \<le> |x\<^sup>\<star>] z"
proof -
  assume a1: "d y \<le> d z \<cdot> |x] y"
  hence a: "d y \<le> d z" and "d y \<le> |x] y"
    apply (metis local.a_subid_aux2 local.dual_order.trans local.fbox_def)
    using a1 dka.dom_subid_aux2 local.dual_order.trans by blast
  hence "d y \<le> |x\<^sup>\<star>] y"
    using fbox_star_induct_var by blast
  thus ?thesis
    using a local.fbox_iso local.order.trans by blast
qed

lemma fbox_star_induct_eq: "d z \<cdot> |x] y = d y \<Longrightarrow> d y \<le> |x\<^sup>\<star>] z"
  by (simp add: fbox_star_induct)

lemma fbox_export_1: "ad y + |x] y = |d y \<cdot> x] y"
  by (simp add: local.a_6 local.fbox_def mult_assoc)

lemma fbox_export_2: "d y + |x] y = |ad y \<cdot> x] y"
  by (simp add: local.ads_d_def local.ans_d_def local.fbox_def mult_assoc)

end

class antidomain_kleene_algebra = antidomain_semiring + kleene_algebra

begin

subclass antidomain_left_kleene_algebra ..

lemma "d p \<le> |(d t \<cdot> x)\<^sup>\<star> \<cdot> ad t] (d q \<cdot> ad t) \<Longrightarrow> d p \<le> |d t \<cdot> x] d q"
(*nitpick [expect=genuine]*)
oops

end

end
