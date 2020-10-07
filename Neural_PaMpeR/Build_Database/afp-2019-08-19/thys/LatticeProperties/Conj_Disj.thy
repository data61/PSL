section \<open>Conjunctive and Disjunctive Functions\<close>

(*
    Author: Viorel Preoteasa
*)

theory Conj_Disj
imports Main
begin

text\<open>
This theory introduces the definitions and some properties for 
conjunctive, disjunctive, universally conjunctive, and universally 
disjunctive functions.
\<close>

locale conjunctive =
  fixes inf_b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and inf_c :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "conjunctive = {x . (\<forall> y z . times_abc x (inf_b y z) = inf_c (times_abc x y) (times_abc x z))}"

lemma conjunctiveI:
  assumes "(\<And>b c. times_abc a (inf_b b c) = inf_c (times_abc a b) (times_abc a c))"
  shows "a \<in> conjunctive"
  using assms by (simp add: conjunctive_def)

lemma conjunctiveD: "x \<in> conjunctive \<Longrightarrow> times_abc x (inf_b y z) = inf_c (times_abc x y) (times_abc x z)"
  by (simp add: conjunctive_def)

end

interpretation Apply: conjunctive "inf::'a::semilattice_inf \<Rightarrow> 'a \<Rightarrow> 'a"
  "inf::'b::semilattice_inf \<Rightarrow> 'b \<Rightarrow> 'b" "\<lambda> f . f"
  done

interpretation Comp: conjunctive "inf::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "inf::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" "(o)"
  done

lemma "Apply.conjunctive = Comp.conjunctive"
  apply (simp add: Apply.conjunctive_def Comp.conjunctive_def)
  apply safe
  apply (simp_all add: fun_eq_iff inf_fun_def)
  apply (drule_tac x = "\<lambda> u . y" in spec)
  apply (drule_tac x = "\<lambda> u . z" in spec)
  by simp

locale disjunctive =
  fixes sup_b :: "'b \<Rightarrow> 'b \<Rightarrow> 'b"
  and sup_c :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "disjunctive = {x . (\<forall> y z . times_abc x (sup_b y z) = sup_c (times_abc x y) (times_abc x z))}"

lemma disjunctiveI:
  assumes "(\<And>b c. times_abc a (sup_b b c) = sup_c (times_abc a b) (times_abc a c))"
  shows "a \<in> disjunctive"
  using assms by (simp add: disjunctive_def)

lemma disjunctiveD: "x \<in> disjunctive \<Longrightarrow> times_abc x (sup_b y z) = sup_c (times_abc x y) (times_abc x z)"
  by (simp add: disjunctive_def)

end

interpretation Apply: disjunctive "sup::'a::semilattice_sup \<Rightarrow> 'a \<Rightarrow> 'a"
  "sup::'b::semilattice_sup \<Rightarrow> 'b \<Rightarrow> 'b" "\<lambda> f . f"
  done

interpretation Comp: disjunctive "sup::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "sup::('a::lattice \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" "(o)"
  done

lemma apply_comp_disjunctive: "Apply.disjunctive = Comp.disjunctive"
  apply (simp add: Apply.disjunctive_def Comp.disjunctive_def)
  apply safe
  apply (simp_all add: fun_eq_iff sup_fun_def)
  apply (drule_tac x = "\<lambda> u . y" in spec)
  apply (drule_tac x = "\<lambda> u . z" in spec)
  by simp

locale Conjunctive =
  fixes Inf_b :: "'b set \<Rightarrow> 'b"
  and Inf_c :: "'c set \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "Conjunctive = {x . (\<forall> X . times_abc x (Inf_b X) = Inf_c ((times_abc x) ` X) )}"

lemma ConjunctiveI:
  assumes "\<And>A. times_abc a (Inf_b A) = Inf_c ((times_abc a) ` A)"
  shows "a \<in> Conjunctive"
  using assms by (simp add: Conjunctive_def)

lemma ConjunctiveD:
  assumes "a \<in> Conjunctive"
  shows "times_abc a (Inf_b A) = Inf_c ((times_abc a) ` A)"
  using assms by (simp add: Conjunctive_def)

end

interpretation Apply: Conjunctive Inf Inf "\<lambda> f . f"
  done

interpretation Comp: Conjunctive "Inf::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "Inf::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" "(o)"
  done

lemma "Apply.Conjunctive = Comp.Conjunctive"
proof
  show "Apply.Conjunctive \<subseteq> (Comp.Conjunctive :: ('a \<Rightarrow> 'a) set)"
  proof
    fix f
    assume "f \<in> (Apply.Conjunctive :: ('a \<Rightarrow> 'a) set)"
    then have *: "f (Inf A) = (INF a\<in>A. f a)" for A
      by (auto dest!: Apply.ConjunctiveD)
    show "f \<in> (Comp.Conjunctive :: ('a \<Rightarrow> 'a) set)"
    proof (rule Comp.ConjunctiveI)
      fix G :: "('a \<Rightarrow> 'a) set"
      from * have "f (INF f\<in>G. f a) = Inf (f ` (\<lambda>f. f a) ` G)"
        for a :: 'a .
      then show "f \<circ> Inf G = Inf (comp f ` G)"
        by (simp add: fun_eq_iff image_comp)
    qed
  qed
  show "Comp.Conjunctive \<subseteq> (Apply.Conjunctive :: ('a \<Rightarrow> 'a) set)"
  proof
    fix f
    assume "f \<in> (Comp.Conjunctive :: ('a \<Rightarrow> 'a) set)"
    then have *: "f \<circ> Inf G = (INF g\<in>G. f \<circ> g)" for G :: "('a \<Rightarrow> 'a) set"
      by (auto dest!: Comp.ConjunctiveD)
    show "f \<in> (Apply.Conjunctive :: ('a \<Rightarrow> 'a) set)"
    proof (rule Apply.ConjunctiveI)
      fix A :: "'a set"
      from * have "f \<circ> (INF a\<in>A. (\<lambda>b :: 'a. a)) = Inf ((\<circ>) f ` (\<lambda>a b. a) ` A)" .
      then show "f (Inf A) = Inf (f ` A)"
        by (simp add: fun_eq_iff image_comp)
    qed
  qed
qed  
        
locale Disjunctive =
  fixes Sup_b :: "'b set \<Rightarrow> 'b"
  and Sup_c :: "'c set \<Rightarrow> 'c"
  and times_abc :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"
begin

definition
  "Disjunctive = {x . (\<forall> X . times_abc x (Sup_b X) = Sup_c ((times_abc x) ` X) )}"

lemma DisjunctiveI:
  assumes "\<And>A. times_abc a (Sup_b A) = Sup_c ((times_abc a) ` A)"
  shows "a \<in> Disjunctive"
  using assms by (simp add: Disjunctive_def)

lemma DisjunctiveD: "x \<in> Disjunctive \<Longrightarrow> times_abc x (Sup_b X) = Sup_c ((times_abc x) ` X)"
  by (simp add: Disjunctive_def)

end

interpretation Apply: Disjunctive Sup Sup "\<lambda> f . f"
  done

interpretation Comp: Disjunctive "Sup::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  "Sup::(('a::complete_lattice \<Rightarrow> 'a) set) \<Rightarrow> ('a \<Rightarrow> 'a)" "(o)"
  done

lemma "Apply.Disjunctive = Comp.Disjunctive"
proof
  show "Apply.Disjunctive \<subseteq> (Comp.Disjunctive :: ('a \<Rightarrow> 'a) set)"
  proof
    fix f
    assume "f \<in> (Apply.Disjunctive :: ('a \<Rightarrow> 'a) set)"
    then have *: "f (Sup A) = (SUP a\<in>A. f a)" for A
      by (auto dest!: Apply.DisjunctiveD)
    show "f \<in> (Comp.Disjunctive :: ('a \<Rightarrow> 'a) set)"
    proof (rule Comp.DisjunctiveI)
      fix G :: "('a \<Rightarrow> 'a) set"
      from * have "f (SUP f\<in>G. f a) = Sup (f ` (\<lambda>f. f a) ` G)"
        for a :: 'a .
      then show "f \<circ> Sup G = Sup (comp f ` G)"
        by (simp add: fun_eq_iff image_comp)
    qed
  qed
  show "Comp.Disjunctive \<subseteq> (Apply.Disjunctive :: ('a \<Rightarrow> 'a) set)"
  proof
    fix f
    assume "f \<in> (Comp.Disjunctive :: ('a \<Rightarrow> 'a) set)"
    then have *: "f \<circ> Sup G = (SUP g\<in>G. f \<circ> g)" for G :: "('a \<Rightarrow> 'a) set"
      by (auto dest!: Comp.DisjunctiveD)
    show "f \<in> (Apply.Disjunctive :: ('a \<Rightarrow> 'a) set)"
    proof (rule Apply.DisjunctiveI)
      fix A :: "'a set"
      from * have "f \<circ> (SUP a\<in>A. (\<lambda>b :: 'a. a)) = Sup ((\<circ>) f ` (\<lambda>a b. a) ` A)" .
      then show "f (Sup A) = Sup (f ` A)"
        by (simp add: fun_eq_iff image_comp)
    qed
  qed
qed  

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Conjunctive \<Longrightarrow> F \<in> Apply.conjunctive"
  apply (simp add: Apply.Conjunctive_def Apply.conjunctive_def)
  apply safe
  apply (drule_tac x = "{y, z}" in spec)
  by simp

lemma [simp]: "F \<in> Apply.conjunctive \<Longrightarrow> mono F"
  apply (simp add: Apply.conjunctive_def mono_def)
  apply safe
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "y" in spec)
  apply (subgoal_tac "inf x y = x")
  apply simp
  apply (subgoal_tac "inf (F x) (F y) \<le> F y")
  apply simp
  apply (rule inf_le2)
  apply (rule antisym)
  by simp_all

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Conjunctive \<Longrightarrow> F top = top"
  apply (simp add: Apply.Conjunctive_def)
  apply (drule_tac x="{}" in spec)
  by simp

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Disjunctive \<Longrightarrow> F \<in> Apply.disjunctive"
  apply (simp add: Apply.Disjunctive_def Apply.disjunctive_def)
  apply safe
  apply (drule_tac x = "{y, z}" in spec)
  by simp

lemma [simp]: "F \<in> Apply.disjunctive \<Longrightarrow> mono F"
  apply (simp add: Apply.disjunctive_def mono_def)
  apply safe
  apply (drule_tac x = "x" in spec)
  apply (drule_tac x = "y" in spec)
  apply (subgoal_tac "sup x y = y")
  apply simp
  apply (subgoal_tac "F x \<le> sup (F x) (F y)")
  apply simp
  apply (rule sup_ge1)
  apply (rule antisym)
  apply simp
  by (rule sup_ge2)

lemma [simp]: "(F::'a::complete_lattice \<Rightarrow> 'b::complete_lattice) \<in> Apply.Disjunctive \<Longrightarrow> F bot = bot"
  apply (simp add: Apply.Disjunctive_def)
  apply (drule_tac x="{}" in spec)
  by simp

lemma weak_fusion: "h \<in> Apply.Disjunctive \<Longrightarrow> mono f \<Longrightarrow> mono g \<Longrightarrow> 
    h o f \<le> g o h \<Longrightarrow> h (lfp f) \<le> lfp g"
  apply (rule_tac P = "\<lambda> x . h x \<le> lfp g" in lfp_ordinal_induct, simp_all)
  apply (rule_tac y = "g (h S)" in order_trans)
  apply (simp add: le_fun_def)
  apply (rule_tac y = "g (lfp g)" in order_trans)
  apply (rule_tac f = g in monoD, simp_all)
  apply (simp add: lfp_unfold [symmetric])
  apply (simp add: Apply.DisjunctiveD)
  by (rule SUP_least, blast)

lemma inf_Disj: "(\<lambda> (x::'a::complete_distrib_lattice) . inf x y) \<in> Apply.Disjunctive"
  by (simp add: Apply.Disjunctive_def fun_eq_iff Sup_inf)

end
