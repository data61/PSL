(* 
  Title: Sup-Lattices and Other Simplifications
  Author: Georg Struth 
  Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Sup-Lattices and Other Simplifications\<close>

theory Sup_Lattice
  imports  Main 
           "HOL-Library.Lattice_Syntax"

begin

text \<open>Some definitions for orderings and lattices in Isabelle could be simpler. The strict order in 
in ord could be defined instead of being axiomatised. The function mono could have been defined on ord
and not on order---even on a general (di)graph it serves as a morphism. In complete lattices, the 
supremum---and dually the infimum---suffices to define the other operations (in the Isabelle/HOL-definition
infimum, binary supremum and infimum, bottom and top element are axiomatised). This not only increases
the number of proof obligations in subclass or sublocale statements, instantiations or interpretations,
it also complicates situations where suprema are presented faithfully, e.g. mapped onto suprema in 
some subalgebra, whereas infima in the subalgebra are different from those in the super-structure.\<close>


text \<open>It would be even nicer to use a class less-eq which dispenses with the strict order symbol
in ord. Then one would not have to redefine this symbol in all instantiations or interpretations.
At least, it does not carry any proof obligations.\<close>

context ord
begin

text \<open>ub-set yields the set of all upper bounds of a set; lb-set the set of all lower bounds.\<close>

definition ub_set :: "'a set \<Rightarrow> 'a set" where
  "ub_set X = {y. \<forall>x \<in> X. x \<le> y}"

definition lb_set :: "'a set \<Rightarrow> 'a set" where
  "lb_set X = {y. \<forall>x \<in> X. y \<le> x}"

end

definition ord_pres :: "('a::ord \<Rightarrow> 'b::ord) \<Rightarrow> bool" where
 "ord_pres f = (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma ord_pres_mono: 
  fixes f :: "'a::order \<Rightarrow> 'b::order"
  shows "mono f = ord_pres f"
  by (simp add: mono_def ord_pres_def)

class preorder_lean = ord +
  assumes preorder_refl: "x \<le> x"
  and preorder_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"

begin

definition le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "le x y = (x \<le> y \<and> \<not> (x \<ge> y))"

end

sublocale preorder_lean \<subseteq> prel: preorder "(\<le>)" le
  by (unfold_locales, auto simp add: le_def preorder_refl preorder_trans)
 
class order_lean = preorder_lean +
  assumes order_antisym: "x \<le> y \<Longrightarrow> x \<ge> y \<Longrightarrow> x = y"

sublocale order_lean \<subseteq> posl: order "(\<le>)" le
  by (unfold_locales, simp add: order_antisym)

class Sup_lattice = order_lean + Sup +
  assumes Sups_upper: "x \<in> X \<Longrightarrow> x \<le> \<Squnion>X"
  and Sups_least: "(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> \<Squnion>X \<le> z"

begin

definition Infs :: "'a set \<Rightarrow> 'a" where
  "Infs X =  \<Squnion>{y. \<forall>x \<in> X. y \<le> x}"

definition sups :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "sups x y = \<Squnion>{x,y}"

definition infs :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "infs x y = Infs{x,y}"

definition bots :: 'a where 
  "bots = \<Squnion>{}"

definition tops :: 'a where
  "tops = Infs{}"

lemma Infs_prop: "Infs = Sup \<circ> lb_set"
  unfolding fun_eq_iff by (simp add: Infs_def prel.lb_set_def)

end

class Inf_lattice = order_lean + Inf +
  assumes Infi_lower: "x \<in> X \<Longrightarrow> \<Sqinter>X \<le> x"
  and Infi_greatest: "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> \<Sqinter>X"

begin

definition Supi :: "'a set \<Rightarrow> 'a" where
  "Supi X = \<Sqinter>{y. \<forall>x \<in> X. x \<le> y}"

definition supi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "supi x y = Supi{x,y}"

definition infi :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "infi x y = \<Sqinter>{x,y}"

definition boti :: 'a where 
  "boti = Supi{}"

definition topi :: 'a where
  "topi = \<Sqinter>{}"

lemma Supi_prop: "Supi = Inf \<circ> ub_set"
  unfolding fun_eq_iff by (simp add: Supi_def prel.ub_set_def)

end

sublocale Inf_lattice \<subseteq> ldual: Sup_lattice Inf "(\<ge>)"
  rewrites "ldual.Infs = Supi"
  and "ldual.infs = supi"
  and "ldual.sups = infi"
  and "ldual.tops = boti"
  and "ldual.bots = topi"
proof-
  show "class.Sup_lattice Inf (\<ge>)"
    by (unfold_locales, simp_all add: Infi_lower Infi_greatest preorder_trans)
  then interpret ldual: Sup_lattice Inf "(\<ge>)".
  show a: "ldual.Infs = Supi"
    unfolding fun_eq_iff by (simp add: ldual.Infs_def Supi_def)
  show "ldual.infs = supi"
    unfolding fun_eq_iff by (simp add: a ldual.infs_def supi_def)
  show "ldual.sups = infi"
    unfolding fun_eq_iff by (simp add: ldual.sups_def infi_def) 
  show "ldual.tops = boti"
    by (simp add: a ldual.tops_def boti_def)
  show "ldual.bots = topi"
    by (simp add: ldual.bots_def topi_def)
qed

sublocale Sup_lattice \<subseteq> supclat: complete_lattice Infs Sup_class.Sup infs "(\<le>)" le sups bots tops
  apply unfold_locales
  unfolding Infs_def infs_def sups_def bots_def tops_def
  by (simp_all, auto intro: Sups_least, simp_all add: Sups_upper)
       
 sublocale Inf_lattice \<subseteq> infclat: complete_lattice Inf_class.Inf Supi infi "(\<le>)" le supi boti topi
  by (unfold_locales, simp_all add: ldual.Sups_upper ldual.Sups_least ldual.supclat.Inf_lower ldual.supclat.Inf_greatest)

end










