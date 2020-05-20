(*
    Title:      Mod_Type.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Class for modular arithmetic\<close>

theory Mod_Type
imports
  "HOL-Library.Numeral_Type"
  "HOL-Analysis.Cartesian_Euclidean_Space"
  Dual_Order
begin

subsection\<open>Definition and properties\<close>

text\<open>Class for modular arithmetic. It is inspired by the locale mod\_type.\<close>

class mod_type = times + wellorder + neg_numeral +
fixes Rep :: "'a => int"
  and Abs :: "int => 'a"
  assumes type: "type_definition Rep Abs {0..<int CARD ('a)}"
  and size1: "1 < int CARD ('a)"
  and zero_def: "0 = Abs 0"
  and one_def:  "1 = Abs 1"
  and add_def:  "x + y = Abs ((Rep x + Rep y) mod (int CARD ('a)))"
  and mult_def: "x * y = Abs ((Rep x * Rep y) mod (int CARD ('a)))"
  and diff_def: "x - y = Abs ((Rep x - Rep y) mod (int CARD ('a)))"
  and minus_def: "- x = Abs ((- Rep x) mod (int CARD ('a)))"
  and strict_mono_Rep: "strict_mono Rep"
begin

lemma size0: "0 < int CARD ('a)"
  using size1 by simp

lemmas definitions =
  zero_def one_def add_def mult_def minus_def diff_def

lemma Rep_less_n: "Rep x < int CARD ('a)"
  by (rule type_definition.Rep [OF type, simplified, THEN conjunct2])

lemma Rep_le_n: "Rep x \<le> int CARD ('a)"
  by (rule Rep_less_n [THEN order_less_imp_le])

lemma Rep_inject_sym: "x = y \<longleftrightarrow> Rep x = Rep y"
  by (rule type_definition.Rep_inject [OF type, symmetric])

lemma Rep_inverse: "Abs (Rep x) = x"
  by (rule type_definition.Rep_inverse [OF type])

lemma Abs_inverse: "m \<in> {0..<int CARD ('a)} \<Longrightarrow> Rep (Abs m) = m"
  by (rule type_definition.Abs_inverse [OF type])

lemma Rep_Abs_mod: "Rep (Abs (m mod int CARD ('a))) = m mod int CARD ('a)"
  by (simp add: Abs_inverse pos_mod_conj [OF size0])

lemma Rep_Abs_0: "Rep (Abs 0) = 0"
  apply (rule Abs_inverse [of 0])
  using size0 by simp

lemma Rep_0: "Rep 0 = 0"
  by (simp add: zero_def Rep_Abs_0)

lemma Rep_Abs_1: "Rep (Abs 1) = 1"
  by (simp add: Abs_inverse size1)

lemma Rep_1: "Rep 1 = 1"
  by (simp add: one_def Rep_Abs_1)

lemma Rep_mod: "Rep x mod int CARD ('a) = Rep x"
  apply (rule_tac x=x in type_definition.Abs_cases [OF type])
  apply (simp add: type_definition.Abs_inverse [OF type])
done

lemmas Rep_simps =
  Rep_inject_sym Rep_inverse Rep_Abs_mod Rep_mod Rep_Abs_0 Rep_Abs_1

subsection\<open>Conversion between a modular class and the subset of natural numbers associated.\<close>
text\<open>Definitions to make transformations among elements of a modular class and naturals\<close>
definition to_nat :: "'a => nat"
  where "to_nat = nat \<circ> Rep"

definition Abs' :: "int => 'a"
  where "Abs' x = Abs(x mod int CARD ('a))"

definition from_nat :: "nat \<Rightarrow> 'a"
  where "from_nat = (Abs' \<circ> int)"

lemma bij_Rep: "bij_betw (Rep) (UNIV::'a set) {0..<int CARD('a)}"
proof (unfold bij_betw_def, rule conjI)
  show "inj Rep" by (metis strict_mono_imp_inj_on strict_mono_Rep)
  show "range Rep = {0..<int CARD('a)}" using Typedef.type_definition.Rep_range[OF type] .
qed

lemma mono_Rep: "mono Rep" by (metis strict_mono_Rep strict_mono_mono)

lemma Rep_ge_0: "0 \<le> Rep x" using bij_Rep unfolding bij_betw_def by auto

lemma bij_Abs: "bij_betw (Abs) {0..<int CARD('a)} (UNIV::'a set)"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on Abs {0..<int CARD('a)}" by (metis inj_on_inverseI type type_definition.Abs_inverse)
  show "Abs ` {0..<int CARD('a)} = (UNIV::'a set)" by (metis type type_definition.univ)
qed

corollary bij_Abs': "bij_betw (Abs') {0..<int CARD('a)} (UNIV::'a set)"
proof (unfold bij_betw_def, rule conjI)
  show "inj_on Abs' {0..<int CARD('a)}"
    unfolding inj_on_def Abs'_def
    by (auto, metis Rep_Abs_mod mod_pos_pos_trivial)
  show "Abs' ` {0..<int CARD('a)} = (UNIV::'a set)"
  proof (unfold image_def Abs'_def, auto)
    fix x show "\<exists>xa\<in>{0..<int CARD('a)}. x = Abs xa"
      by (rule bexI[of _ "Rep x"], auto simp add: Rep_less_n[of x] Rep_ge_0[of x], metis Rep_inverse)
  qed
qed

lemma bij_from_nat: "bij_betw (from_nat) {0..<CARD('a)} (UNIV::'a set)"
proof (unfold bij_betw_def, rule conjI)
  have set_eq: "{0::int..<int CARD('a)} = int` {0..<CARD('a)}" apply (auto)
  proof -
    fix x::int  assume x1: "(0::int) \<le> x" and x2: "x < int CARD('a)" show "x \<in> int ` {0::nat..<CARD('a)}"
    proof (unfold image_def, auto, rule bexI[of _ "nat x"])
      show " x = int (nat x)" using x1 by auto
      show "nat x \<in> {0::nat..<CARD('a)}" using x1 x2 by auto
    qed
  qed
  show "inj_on (from_nat::nat\<Rightarrow>'a) {0::nat..<CARD('a)}"
  proof (unfold from_nat_def , rule comp_inj_on)
    show "inj_on int {0::nat..<CARD('a)}" by (metis inj_of_nat subset_inj_on top_greatest)
    show "inj_on (Abs'::int=>'a) (int ` {0::nat..<CARD('a)})"
      using bij_Abs unfolding bij_betw_def set_eq
      by (metis (hide_lams, no_types) Abs'_def Abs_inverse Rep_inverse Rep_mod inj_on_def set_eq)
  qed
  show "(from_nat::nat=>'a)` {0::nat..<CARD('a)} = UNIV"
    unfolding from_nat_def using bij_Abs'
    unfolding bij_betw_def set_eq o_def by blast
qed

lemma to_nat_is_inv: "the_inv_into {0..<CARD('a)} (from_nat::nat=>'a) = (to_nat::'a=>nat)"
proof (unfold the_inv_into_def fun_eq_iff from_nat_def to_nat_def o_def, clarify)
  fix x::"'a" show "(THE y::nat. y \<in> {0::nat..<CARD('a)} \<and> Abs' (int y) = x) = nat (Rep x)"
  proof (rule the_equality, auto)
    show " Abs' (Rep x) = x" by (metis Abs'_def Rep_inverse Rep_mod)
    show "nat (Rep x) < CARD('a)" by (metis (full_types) Rep_less_n nat_int size0 zless_nat_conj)
    assume x:  "\<not> (0::int) \<le> Rep x" show "(0::nat) < CARD('a)" and "Abs' (0::int) = x"
      using Rep_ge_0 x by auto
  next
    fix y::nat assume y: "y < CARD('a)"
    have "(Rep(Abs'(int y)::'a)) = (Rep((Abs(int y mod int CARD('a)))::'a))" unfolding Abs'_def ..
    also have "... =  (Rep (Abs (int y)::'a))" using zmod_int[of y "CARD('a)"]
      using y mod_less by auto
    also have "... =  (int y)" proof (rule Abs_inverse) show "int y \<in> {0::int..<int CARD('a)}"
      using y by auto qed
    finally show "y = nat (Rep (Abs' (int y)::'a))" by (metis nat_int)
  qed
qed

lemma bij_to_nat: "bij_betw (to_nat) (UNIV::'a set) {0..<CARD('a)}"
  using bij_betw_the_inv_into[OF bij_from_nat] unfolding to_nat_is_inv .

lemma finite_mod_type: "finite (UNIV::'a set)"
  using finite_imageD[of "to_nat" "UNIV::'a set"] using bij_to_nat unfolding bij_betw_def by auto

subclass (in mod_type) finite by (intro_classes, rule finite_mod_type)

lemma least_0: "(LEAST n. n \<in> (UNIV::'a set)) = 0"
proof (rule Least_equality, auto)
  fix y::"'a"
  have "(0::'a) \<le> Abs (Rep y mod int CARD('a))" using strict_mono_Rep unfolding strict_mono_def
  by (metis (hide_lams, mono_tags) Rep_0 Rep_ge_0 strict_mono_Rep strict_mono_less_eq)
  also have "... = y" by (metis Rep_inverse Rep_mod)
  finally show "(0::'a) \<le> y" .
qed

lemma add_to_nat_def: "x + y = from_nat (to_nat x + to_nat y)"
  unfolding from_nat_def to_nat_def o_def using Rep_ge_0[of x] using Rep_ge_0[of y]
  using Rep_less_n[of x] Rep_less_n[of y]
  unfolding Abs'_def unfolding add_def[of x y] by auto

lemma to_nat_1: "to_nat 1 = 1"
  by (simp add: to_nat_def Rep_1)

lemma add_def':
  shows "x + y = Abs' (Rep x + Rep y)" unfolding Abs'_def using add_def by simp

lemma Abs'_0:
  shows "Abs' (CARD('a))=(0::'a)" by (metis (hide_lams, mono_tags) Abs'_def mod_self zero_def)

lemma Rep_plus_one_le_card:
  assumes a: "a + 1 \<noteq> 0"
  shows "(Rep a) + 1 < CARD ('a)"
proof (rule ccontr)
  assume "\<not> Rep a + 1 < CARD('a)" hence to_nat_eq_card: "Rep a + 1 = CARD('a)"
    using Rep_less_n
    by (simp add: add1_zle_eq order_class.less_le)
  have "a+1 = Abs' (Rep a + Rep (1::'a))" using add_def' by auto
  also have "... = Abs' ((Rep a) + 1)" using Rep_1 by simp
  also have "... = Abs' (CARD('a))" unfolding to_nat_eq_card ..
  also have "... = 0" using Abs'_0 by auto
  finally show False using a by contradiction
qed

lemma to_nat_plus_one_less_card: "\<forall>a. a+1 \<noteq> 0 --> to_nat a + 1 < CARD('a)"
proof (clarify)
fix a
assume a: "a + 1 \<noteq> 0"
have "Rep a + 1 < int CARD('a)" using Rep_plus_one_le_card[OF a] by auto
hence "nat (Rep a + 1) < nat (int CARD('a))" unfolding zless_nat_conj using size0 by fast
thus "to_nat a + 1 < CARD('a)" unfolding to_nat_def o_def using nat_add_distrib[OF Rep_ge_0] by simp
qed

corollary to_nat_plus_one_less_card':
assumes "a+1 \<noteq> 0"
shows "to_nat a + 1 < CARD('a)" using to_nat_plus_one_less_card assms by simp

lemma strict_mono_to_nat: "strict_mono to_nat"
  using strict_mono_Rep
  unfolding strict_mono_def to_nat_def using Rep_ge_0 by (metis comp_apply nat_less_eq_zless)

lemma to_nat_eq [simp]: "to_nat x = to_nat y \<longleftrightarrow> x = y"
  using injD [OF bij_betw_imp_inj_on[OF bij_to_nat]] by blast

lemma mod_type_forall_eq [simp]: "(\<forall>j::'a. (to_nat j)<CARD('a) \<longrightarrow> P j) = (\<forall>a. P a)"
proof (auto)
  fix a assume a: "\<forall>j. (to_nat::'a=>nat) j < CARD('a) \<longrightarrow> P j"
  have "(to_nat::'a=>nat) a < CARD('a)" using bij_to_nat unfolding bij_betw_def by auto
  thus "P a" using a by auto
qed

lemma to_nat_from_nat:
  assumes t:"to_nat j = k"
  shows "from_nat k = j"
proof -
  have "from_nat k = from_nat (to_nat j)"  unfolding t ..
  also have "... = from_nat (the_inv_into {0..<CARD('a)} (from_nat) j)" unfolding to_nat_is_inv ..
  also have "... = j"
  proof (rule f_the_inv_into_f)
    show "inj_on from_nat {0..<CARD('a)}" by (metis bij_betw_imp_inj_on bij_from_nat)
    show "j \<in> from_nat ` {0..<CARD('a)}" by (metis UNIV_I bij_betw_def bij_from_nat)
  qed
  finally show "from_nat k = j" .
qed

lemma to_nat_mono:
  assumes ab: "a < b"
  shows "to_nat a < to_nat b"
  using strict_mono_to_nat unfolding strict_mono_def using assms by fast

lemma to_nat_mono':
  assumes ab: "a \<le> b"
  shows "to_nat a \<le> to_nat b"
proof (cases "a=b")
  case True thus ?thesis by auto
next
  case False
  hence "a<b" using ab by simp
  thus ?thesis using to_nat_mono by fastforce
qed

lemma least_mod_type:
  shows "0 \<le> (n::'a)"
  using least_0 by (metis (full_types) Least_le UNIV_I)

lemma to_nat_from_nat_id:
  assumes x: "x<CARD('a)"
  shows "to_nat ((from_nat x)::'a) = x"
  unfolding to_nat_is_inv[symmetric] proof (rule the_inv_into_f_f)
  show "inj_on (from_nat::nat=>'a) {0..<CARD('a)}" using bij_from_nat unfolding bij_betw_def by auto
  show "x \<in> {0..<CARD('a)}" using x by simp
qed

lemma from_nat_to_nat_id[simp]:
  shows "from_nat (to_nat x) = x" by (metis to_nat_from_nat)

lemma from_nat_to_nat:
  assumes t:"from_nat j = k" and j: "j<CARD('a)"
  shows "to_nat k = j" by (metis j t to_nat_from_nat_id)

lemma from_nat_mono:
  assumes i_le_j: "i<j" and j: "j<CARD('a)"
  shows "(from_nat i::'a) < from_nat j"
proof -
have i: "i<CARD('a)" using i_le_j j by simp
obtain a where a: "i=to_nat a"
  using bij_to_nat unfolding bij_betw_def using i to_nat_from_nat_id by metis
obtain b where b: "j=to_nat b"
  using bij_to_nat unfolding bij_betw_def using j to_nat_from_nat_id by metis
show ?thesis by (metis a b from_nat_to_nat_id i_le_j strict_mono_less strict_mono_to_nat)
qed

lemma from_nat_mono':
  assumes i_le_j: "i \<le> j" and "j<CARD ('a)"
  shows "(from_nat i::'a) \<le> from_nat j"
proof (cases "i=j")
  case True
  have "(from_nat i::'a) = from_nat j" using True by simp
  thus ?thesis by simp
next
  case False
  hence "i<j" using i_le_j by simp
  thus ?thesis by (metis assms(2) from_nat_mono less_imp_le)
qed

lemma to_nat_suc:
  assumes "to_nat (x)+1 < CARD ('a)"
  shows "to_nat (x + 1::'a) = (to_nat x) + 1"
proof -
  have "(x::'a) + 1 = from_nat (to_nat x + to_nat (1::'a))" unfolding add_to_nat_def ..
  hence "to_nat ((x::'a) + 1) = to_nat (from_nat (to_nat x + to_nat (1::'a))::'a)" by presburger
  also have "... = to_nat (from_nat (to_nat x + 1)::'a)" unfolding to_nat_1 ..
  also have "... = (to_nat x + 1)" by (metis assms to_nat_from_nat_id)
  finally show ?thesis .
qed

lemma to_nat_le:
  assumes "y < from_nat k"
  shows  "to_nat y < k"
proof (cases "k<CARD('a)")
  case True show ?thesis by (metis (full_types) True assms to_nat_from_nat_id to_nat_mono)
next
  case False have "to_nat y < CARD ('a)" using bij_to_nat unfolding bij_betw_def by auto
  thus ?thesis using False by auto
qed

lemma le_Suc:
  assumes ab: "a < (b::'a)"
  shows "a + 1 \<le> b"
proof -
  have "a + 1 = (from_nat (to_nat (a + 1))::'a)" using from_nat_to_nat_id [of "a+1",symmetric] .
  also have "... \<le> (from_nat (to_nat (b::'a))::'a)"
  proof (rule from_nat_mono')
    have "to_nat a < to_nat b" using ab by (metis to_nat_mono)
    hence "to_nat a + 1 \<le> to_nat b" by simp
    thus "to_nat b < CARD ('a)" using bij_to_nat unfolding  bij_betw_def by auto
    hence "to_nat a + 1 < CARD ('a)" by (metis \<open>to_nat a + 1 \<le> to_nat b\<close> preorder_class.le_less_trans)
    thus "to_nat (a + 1) \<le> to_nat b" by (metis \<open>to_nat a + 1 \<le> to_nat b\<close> to_nat_suc)
  qed
  also have "... = b" by (metis from_nat_to_nat_id)
  finally show "a + (1::'a) \<le> b" .
qed

lemma le_Suc':
assumes ab: "a + 1 \<le> b"
  and less_card: "(to_nat a) + 1 < CARD ('a)"
  shows "a < b"
proof -
  have "a = (from_nat (to_nat a)::'a)" using from_nat_to_nat_id [of "a",symmetric] .
  also have "... < (from_nat (to_nat b)::'a)"
  proof (rule from_nat_mono)
    show "to_nat b < CARD('a)" using bij_to_nat unfolding  bij_betw_def by auto
    have "to_nat (a + 1) \<le>  to_nat b" using ab by (metis to_nat_mono')
    hence "to_nat (a) + 1 \<le>  to_nat b"  using to_nat_suc[OF less_card] by auto
    thus "to_nat a < to_nat b" by simp
  qed
  finally show "a < b" by (metis to_nat_from_nat)
qed

lemma Suc_le:
  assumes less_card: "(to_nat a) + 1 < CARD ('a)"
  shows "a < a + 1"
proof -
  have "(to_nat a) < (to_nat a) + 1" by simp
  hence "(to_nat a) < to_nat (a + 1)" by (metis less_card to_nat_suc)
  hence "(from_nat (to_nat a)::'a) < from_nat (to_nat (a + 1))"
    by (rule from_nat_mono, metis less_card to_nat_suc)
  thus "a < a + 1" by (metis to_nat_from_nat)
qed

lemma Suc_le':
  fixes a::'a
  assumes "a + 1 \<noteq> 0"
  shows "a < a + 1" using Suc_le to_nat_plus_one_less_card assms by blast

lemma from_nat_not_eq:
  assumes a_eq_to_nat: "a \<noteq> to_nat b"
  and a_less_card: "a<CARD('a)"
  shows "from_nat a \<noteq> b"
proof (rule ccontr)
  assume "\<not> from_nat a \<noteq> b" hence "from_nat a = b" by simp
  hence "to_nat ((from_nat a)::'a) = to_nat b" by auto
  thus False by (metis a_eq_to_nat a_less_card to_nat_from_nat_id)
qed

lemma Suc_less:
  fixes i::'a
  assumes "i<j"
  and "i+1 \<noteq> j"
  shows "i+1<j" by (metis assms le_Suc le_neq_trans)


lemma Greatest_is_minus_1: "\<forall>a::'a. a \<le> -1"
proof (clarify)
  fix a::'a
  have zero_ge_card_1: "0 \<le> int CARD('a) - 1" using size1 by auto
  have card_less: "int CARD('a) - 1 < int CARD('a)" by auto
  have not_zero: "1 mod int CARD('a) \<noteq> 0"
    by (metis (hide_lams, mono_tags) Rep_Abs_1 Rep_mod zero_neq_one)
  have int_card: "int (CARD('a) - 1) = int CARD('a) - 1" using of_nat_diff[of 1 "CARD ('a)"]
    using size1 by simp
  have "a = Abs' (Rep a)" by (metis (hide_lams, mono_tags) Rep_0 add_0_right add_def'
      monoid_add_class.add.right_neutral)
  also have "... = Abs' (int (nat (Rep a)))" by (metis Rep_ge_0 int_nat_eq)
  also have "...  \<le> Abs' (int (CARD('a) - 1))"
  proof (rule from_nat_mono'[unfolded from_nat_def o_def, of "nat (Rep a)" "CARD('a) - 1"])
    show "nat (Rep a) \<le> CARD('a) - 1" using Rep_less_n
      using int_card nat_le_iff by auto
    show "CARD('a) - 1 < CARD('a)" using finite_UNIV_card_ge_0 finite_mod_type by fastforce
  qed
  also have "... = - 1"
  unfolding Abs'_def unfolding minus_def zmod_zminus1_eq_if unfolding Rep_1
  apply (rule cong [of Abs], rule refl)
  unfolding if_not_P [OF not_zero]
  unfolding int_card
  unfolding mod_pos_pos_trivial[OF zero_ge_card_1 card_less]
  using mod_pos_pos_trivial[OF _ size1] by presburger
  finally show "a \<le> -1" by fastforce
qed

lemma a_eq_minus_1: "\<forall>a::'a. a+1 = 0 \<longrightarrow> a = -1"
  by (metis eq_neg_iff_add_eq_0)


lemma forall_from_nat_rw:
  shows "(\<forall>x\<in>{0..<CARD('a)}. P (from_nat x::'a)) = (\<forall>x. P (from_nat x))"
proof (auto)
  fix y assume *: "\<forall>x\<in>{0..<CARD('a)}. P (from_nat x)"
  have "from_nat y \<in> (UNIV::'a set)" by auto
  from this obtain x where x1: "from_nat y = (from_nat x::'a)" and x2: "x\<in>{0..<CARD('a)}"
    using bij_from_nat unfolding bij_betw_def
    by (metis from_nat_to_nat_id rangeI the_inv_into_onto to_nat_is_inv)
  show "P (from_nat y::'a)" unfolding x1 using * x2 by simp
qed

lemma from_nat_eq_imp_eq:
  assumes f_eq: "from_nat x = (from_nat xa::'a)"
and x: "x<CARD('a)" and xa: "xa<CARD('a)"
  shows "x=xa" using assms from_nat_not_eq by metis

lemma to_nat_less_card:
  fixes j::"'a"
  shows "to_nat j < CARD ('a)"
  using bij_to_nat unfolding bij_betw_def by auto

lemma from_nat_0: "from_nat 0 = 0"
  unfolding from_nat_def o_def of_nat_0 Abs'_def mod_0 zero_def ..
lemma to_nat_0: "to_nat 0 = 0" unfolding to_nat_def o_def Rep_0 nat_0 ..
lemma to_nat_eq_0: "(to_nat x = 0) = (x = 0)" using to_nat_0 to_nat_from_nat by auto


lemma suc_not_zero:
  assumes "to_nat a + 1 \<noteq> CARD('a)"
  shows "a+1 \<noteq> 0"
proof (rule ccontr, simp)
  assume a_plus_one_zero: "a + 1 = 0"
  hence rep_eq_card: "Rep a + 1 = CARD('a)"
    using assms to_nat_0 Suc_eq_plus1 Suc_lessI Zero_not_Suc to_nat_less_card to_nat_suc
    by (metis (hide_lams, mono_tags))
  moreover have "Rep a + 1 < CARD('a)"
    using Abs'_0 Rep_1 Suc_eq_plus1 Suc_lessI Suc_neq_Zero add_def' assms
    rep_eq_card to_nat_0 to_nat_less_card to_nat_suc by (metis (hide_lams, mono_tags))
  ultimately show False by fastforce
qed


lemma from_nat_suc:
shows "from_nat (j + 1) = from_nat j + 1"
unfolding from_nat_def o_def Abs'_def add_def' Rep_1 Rep_Abs_mod
unfolding of_nat_add apply (subst mod_add_left_eq) unfolding of_nat_1 ..

lemma to_nat_plus_1_set:
shows "to_nat a + 1 \<in> {1..<CARD('a)+1}"
using to_nat_less_card by simp

end

lemma from_nat_CARD:
  shows "from_nat (CARD('a)) = (0::'a::{mod_type})"
  unfolding from_nat_def o_def Abs'_def by (simp add: zero_def)


subsection\<open>Instantiations\<close>

instantiation bit0 and bit1:: (finite) mod_type
begin

definition "(Rep::'a bit0 => int)  x = Rep_bit0 x"
definition "(Abs::int => 'a bit0) x = Abs_bit0' x"

definition "(Rep::'a bit1 => int)  x = Rep_bit1 x"
definition "(Abs::int => 'a bit1) x = Abs_bit1' x"

instance
proof
  show "(0::'a bit0) = Abs (0::int)" unfolding Abs_bit0_def Abs_bit0'_def zero_bit0_def by auto
  show "(1::int) < int CARD('a bit0)" by (metis bit0.size1)
  show "type_definition (Rep::'a bit0 => int) (Abs:: int => 'a bit0) {0::int..<int CARD('a bit0)}"
  proof (unfold type_definition_def Rep_bit0_def [abs_def]
      Abs_bit0_def [abs_def] Abs_bit0'_def, intro conjI)
    show "\<forall>x::'a bit0. Rep_bit0 x \<in> {0::int..<int CARD('a bit0)}"
      unfolding card_bit0 unfolding of_nat_mult
      using Rep_bit0 [where ?'a = "'a"] by simp
    show "\<forall>x::'a bit0. Abs_bit0 (Rep_bit0 x mod int CARD('a bit0)) = x"
      by (metis Rep_bit0_inverse bit0.Rep_mod)
    show "\<forall>y::int. y \<in> {0::int..<int CARD('a bit0)}
      \<longrightarrow> Rep_bit0 ((Abs_bit0::int => 'a bit0) (y mod int CARD('a bit0))) = y"
      by (metis bit0.Abs_inverse bit0.Rep_mod)
  qed
  show "(1::'a bit0) = Abs (1::int)" unfolding Abs_bit0_def Abs_bit0'_def one_bit0_def
    by (metis bit0.of_nat_eq of_nat_1 one_bit0_def)
  fix x y :: "'a bit0"
  show "x + y = Abs ((Rep x + Rep y) mod int CARD('a bit0))"
    unfolding Abs_bit0_def Rep_bit0_def plus_bit0_def Abs_bit0'_def by fastforce
  show "x * y = Abs (Rep x * Rep y mod int CARD('a bit0))"
    unfolding Abs_bit0_def Rep_bit0_def times_bit0_def Abs_bit0'_def by fastforce
  show "x - y = Abs ((Rep x - Rep y) mod int CARD('a bit0))"
    unfolding Abs_bit0_def Rep_bit0_def minus_bit0_def Abs_bit0'_def by fastforce
  show "- x = Abs (- Rep x mod int CARD('a bit0))"
    unfolding Abs_bit0_def Rep_bit0_def uminus_bit0_def Abs_bit0'_def by fastforce
  show "(0::'a bit1) = Abs (0::int)" unfolding Abs_bit1_def Abs_bit1'_def zero_bit1_def by auto
  show "(1::int) < int CARD('a bit1)" by (metis bit1.size1)
  show "(1::'a bit1) = Abs (1::int)" unfolding Abs_bit1_def Abs_bit1'_def one_bit1_def
    by (metis bit1.of_nat_eq of_nat_1 one_bit1_def)
  fix x y :: "'a bit1"
  show "x + y = Abs ((Rep x + Rep y) mod int CARD('a bit1))"
    unfolding Abs_bit1_def Abs_bit1'_def Rep_bit1_def plus_bit1_def by fastforce
  show "x * y = Abs (Rep x * Rep y mod int CARD('a bit1))"
    unfolding Abs_bit1_def Rep_bit1_def times_bit1_def Abs_bit1'_def by fastforce
  show "x - y = Abs ((Rep x - Rep y) mod int CARD('a bit1))"
    unfolding Abs_bit1_def Rep_bit1_def minus_bit1_def Abs_bit1'_def by fastforce
  show "- x = Abs (- Rep x mod int CARD('a bit1))"
    unfolding Abs_bit1_def Rep_bit1_def uminus_bit1_def Abs_bit1'_def by fastforce
  show "type_definition (Rep::'a bit1 => int) (Abs:: int => 'a bit1) {0::int..<int CARD('a bit1)}"
  proof (unfold type_definition_def Rep_bit1_def [abs_def]
      Abs_bit1_def [abs_def] Abs_bit1'_def, intro conjI)
    have int_2: "int 2 = 2" by auto
   show "\<forall>x::'a bit1. Rep_bit1 x \<in> {0::int..<int CARD('a bit1)}"
      unfolding card_bit1
      unfolding of_nat_Suc of_nat_mult
      using Rep_bit1 [where ?'a = "'a"]
      unfolding int_2 ..
   show "\<forall>x::'a bit1. Abs_bit1 (Rep_bit1 x mod int CARD('a bit1)) = x"
      by (metis Rep_bit1_inverse bit1.Rep_mod)
   show "\<forall>y::int. y \<in> {0::int..<int CARD('a bit1)}
    \<longrightarrow> Rep_bit1 ((Abs_bit1::int => 'a bit1) (y mod int CARD('a bit1))) = y"
   by (metis bit1.Abs_inverse bit1.Rep_mod)
  qed
  show "strict_mono (Rep::'a bit0 => int)" unfolding strict_mono_def
    by (metis Rep_bit0_def less_bit0_def)
  show "strict_mono (Rep::'a bit1 => int)" unfolding strict_mono_def
    by (metis Rep_bit1_def less_bit1_def)
qed
end

end


