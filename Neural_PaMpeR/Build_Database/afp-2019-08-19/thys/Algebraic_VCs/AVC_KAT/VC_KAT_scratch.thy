(* Title: Program Correctness Component Based on Kleene Algebra with Tests
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Two Standalone Components\<close>

theory VC_KAT_scratch
  imports Main
begin

subsection \<open>Component Based on Kleene Algebra with Tests\<close>

text \<open>This component supports the verification and step-wise refinement of simple while programs
in a partial correctness setting.\<close>

subsubsection \<open>KAT: Definition and Basic Properties\<close>

notation times (infixl "\<cdot>" 70)

class plus_ord = plus + ord +
  assumes less_eq_def: "x \<le> y \<longleftrightarrow> x + y = y"
  and less_def: "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

class dioid = semiring + one + zero + plus_ord +
  assumes add_idem [simp]: "x + x = x"
  and mult_onel [simp]: "1 \<cdot> x = x"
  and mult_oner [simp]: "x \<cdot> 1 = x"
  and add_zerol [simp]: "0 + x = x"
  and annil [simp]: "0 \<cdot> x = 0"
  and annir [simp]: "x \<cdot> 0 = 0"

begin

subclass monoid_mult 
  by (standard, simp_all)

subclass order
  apply (standard, simp_all add: less_def less_eq_def add_commute)
  apply force
  by (metis add_assoc)

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"
  by (metis distrib_left less_eq_def)

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"
  by (metis distrib_right less_eq_def)
                                         
lemma add_iso: "x \<le> y \<Longrightarrow> x + z \<le> y + z"
  by (metis (no_types, lifting) abel_semigroup.commute add.abel_semigroup_axioms add.semigroup_axioms add_idem less_eq_def semigroup.assoc)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_assoc add_commute less_eq_def order.ordering_axioms ordering.refl)

end

class kleene_algebra = dioid + 
  fixes star :: "'a \<Rightarrow> 'a" ("_\<^sup>\<star>" [101] 100)
  assumes star_unfoldl: "1 + x \<cdot> x\<^sup>\<star> \<le> x\<^sup>\<star>"  
  and star_unfoldr: "1 + x\<^sup>\<star> \<cdot> x \<le> x\<^sup>\<star>"
  and star_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x\<^sup>\<star> \<cdot> z \<le> y"
  and star_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x\<^sup>\<star> \<le> y"

begin

lemma star_sim: "x \<cdot> y \<le> z \<cdot> x \<Longrightarrow> x \<cdot> y\<^sup>\<star> \<le> z\<^sup>\<star> \<cdot> x"
proof - 
  assume "x \<cdot> y \<le> z \<cdot> x"
  hence "x + z\<^sup>\<star> \<cdot> x \<cdot> y \<le> x + z\<^sup>\<star> \<cdot> z \<cdot> x"
    by (metis add_lub distrib_left eq_refl less_eq_def mult_assoc)
  also have  "... \<le> z\<^sup>\<star> \<cdot> x"
    using add_lub mult_isor star_unfoldr by fastforce
  finally show ?thesis
    by (simp add: star_inductr) 
qed

end

class kat = kleene_algebra +
  fixes at :: "'a \<Rightarrow> 'a" 
  assumes test_one [simp]: "at (at 1) = 1"
  and test_mult [simp]: "at (at (at (at x) \<cdot> at (at y))) = at (at y) \<cdot> at (at x)" 
  and test_mult_comp [simp]: "at x \<cdot> at (at x) = 0"
  and test_de_morgan: "at x + at y = at (at (at x) \<cdot> at (at y))"

begin

definition t_op :: "'a \<Rightarrow> 'a" ("t_" [100] 101) where
  "t x = at (at x)"

lemma t_n [simp]: "t (at x) = at x"
  by (metis add_idem test_de_morgan test_mult t_op_def)

lemma t_comm: "t x \<cdot> t y = t y \<cdot> t x"
  by (metis add_commute test_de_morgan test_mult t_op_def)

lemma t_idem [simp]: "t x \<cdot> t x = t x"
  by (metis add_idem test_de_morgan test_mult t_op_def)

lemma t_mult_closed [simp]: "t (t x \<cdot> t y) = t x \<cdot> t y"
  using t_comm t_op_def by auto

subsubsection\<open>Propositional Hoare Logic\<close>

definition H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "H p x q \<longleftrightarrow> t p \<cdot> x \<le> x \<cdot> t q"

definition if_then_else :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = t p \<cdot> x + at p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (t p \<cdot> x)\<^sup>\<star> \<cdot> at p"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

lemma H_skip: "H p 1 p"
  by (simp add: H_def)

lemma H_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (meson H_def mult_isol mult_isor order.trans)

lemma H_seq: "H r y q \<Longrightarrow> H p x r  \<Longrightarrow> H p (x \<cdot> y) q"
proof -
  assume h1: "H p x r" and h2: "H r y q"  
  hence h3: "t p \<cdot> x \<le> x \<cdot> t r" and h4: "t r \<cdot> y \<le> y \<cdot> t q"
    using H_def apply  blast using H_def h2 by blast
  hence "t p \<cdot> x \<cdot> y \<le> x \<cdot> t r \<cdot> y"
    using mult_isor by blast
  also have "... \<le> x \<cdot> y \<cdot> t q"
    by (simp add: h4 mult_isol mult_assoc)
  finally show ?thesis
    by (simp add: H_def mult_assoc)
qed

lemma H_cond: "H (t p \<cdot> t r) x q \<Longrightarrow> H (t p \<cdot> at r) y q \<Longrightarrow> H p (if r then x else y fi) q"
proof -
  assume h1: "H (t p \<cdot> t r) x q" and h2: "H (t p \<cdot> at r) y q"
  hence h3: "t r \<cdot> t p \<cdot> t r \<cdot> x \<le> t r \<cdot> x \<cdot> t q" and h4: "at r \<cdot> t p \<cdot> at r \<cdot> y \<le> at r \<cdot> y \<cdot> t q"
    by (simp add: H_def mult_isol mult_assoc, metis H_def h2 mult_isol mult_assoc t_mult_closed t_n)
  hence h5: "t p \<cdot> t r \<cdot> x \<le> t r \<cdot> x \<cdot> t q" and  h6: "t p \<cdot> at r \<cdot> y \<le> at r \<cdot> y \<cdot> t q"
    by (simp add: mult_assoc t_comm, metis h4 mult_assoc t_comm t_idem t_n)
  have "t p \<cdot> (t r \<cdot> x + at r \<cdot> y) = t p \<cdot> t r \<cdot> x + t p \<cdot> at r \<cdot> y"
    by (simp add: distrib_left mult_assoc)
  also have "... \<le> t r \<cdot> x \<cdot> t q + t p \<cdot> at r \<cdot> y"
    using h5 add_iso by blast
  also have "... \<le> t r \<cdot> x \<cdot> t q + at r \<cdot> y \<cdot> t q"
    by (simp add: add_commute h6 add_iso)
  finally show ?thesis
    by (simp add: H_def if_then_else_def distrib_right)
qed

lemma H_loop: "H (t p \<cdot> t r) x p \<Longrightarrow> H p (while r do x od) (t p \<cdot> at r)"
proof - 
  assume  "H (t p \<cdot> t r) x p"
  hence "t r \<cdot> t p \<cdot> t r \<cdot> x \<le> t r \<cdot> x \<cdot> t p"
    by (metis H_def distrib_left less_eq_def mult_assoc t_mult_closed)
  hence "t p \<cdot> t r \<cdot> x \<le> t r \<cdot> x \<cdot> t p"
    by (simp add: mult_assoc t_comm)
  hence "t p \<cdot> (t r \<cdot> x)\<^sup>\<star> \<cdot> at r \<le> (t r \<cdot> x)\<^sup>\<star> \<cdot> t p \<cdot> at r"
    by (metis mult_isor star_sim mult_assoc)
  hence "t p \<cdot> (t r \<cdot> x)\<^sup>\<star> \<cdot> at r \<le> (t r \<cdot> x)\<^sup>\<star> \<cdot> at r \<cdot> t p \<cdot> at r"
    by (metis mult_assoc t_comm t_idem t_n)
  thus ?thesis
    by (metis H_def mult_assoc t_mult_closed t_n while_def)
qed

lemma H_while_inv: "t p \<le> t i \<Longrightarrow> t i \<cdot> at r \<le> t q \<Longrightarrow> H (t i \<cdot> t r) x i \<Longrightarrow> H p (while r inv i do x od) q"
  by (metis H_cons H_loop t_mult_closed t_n while_inv_def)

end

subsubsection\<open>Soundness and Relation KAT\<close>

notation relcomp (infixl ";" 70)

interpretation rel_d: dioid Id "{}" "(\<union>)" "(;)" "(\<subseteq>)" "(\<subset>)" 
  by (standard, auto)

lemma (in dioid) power_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  apply (induct i; clarsimp simp add: add_lub)
  by (metis local.dual_order.trans local.mult_isol mult_assoc)

lemma (in dioid) power_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
  apply (induct i; clarsimp simp add: add_lub)
  proof -
    fix i
    assume "z \<cdot> x ^ i \<le> y" "z \<le> y" "y \<cdot> x \<le> y"
    hence "(z \<cdot> x ^ i) \<cdot> x \<le> y"
      using local.dual_order.trans local.mult_isor by blast
    thus "z \<cdot> (x \<cdot> x ^ i) \<le> y"
      by (simp add: mult_assoc local.power_commutes)
  qed

lemma power_is_relpow: "rel_d.power X i = X ^^ i"
  by (induct i, simp_all add: relpow_commute)

lemma rel_star_def: "X^* = (\<Union>i. rel_d.power X i)"
  by (simp add: power_is_relpow rtrancl_is_UN_relpow)

lemma rel_star_contl: "X ; Y^* = (\<Union>i. X ; rel_d.power Y i)"
  by (simp add: rel_star_def relcomp_UNION_distrib)

lemma rel_star_contr: "X^* ; Y = (\<Union>i. (rel_d.power X i) ; Y)"
  by (simp add: rel_star_def relcomp_UNION_distrib2)

definition rel_at :: "'a rel \<Rightarrow> 'a rel" where 
  "rel_at X = Id \<inter> - X"  

interpretation rel_kat: kat Id "{}" "(\<union>)" "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl rel_at
  apply standard 
  apply auto[2]
  by (auto simp: rel_star_contr rel_d.power_inductl rel_star_contl  SUP_least rel_d.power_inductr rel_at_def)

subsubsection\<open>Embedding Predicates in Relations\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

abbreviation p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> \<equiv> {(s,s) |s. P s}"

lemma t_p2r [simp]: "rel_kat.t_op \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (auto simp add: rel_kat.t_op_def rel_at_def)
 
lemma p2r_neg_hom [simp]: "rel_at \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not> P s\<rceil>" 
  by (auto simp: rel_at_def)

lemma p2r_conj_hom [simp]: "\<lceil>P\<rceil> \<inter> \<lceil>Q\<rceil> = \<lceil>\<lambda>s.  P s \<and> Q s\<rceil>"
  by auto 

lemma p2r_conj_hom_var [simp]: "\<lceil>P\<rceil> ; \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>" 
  by auto 

lemma p2r_disj_hom [simp]: "\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<or> Q s\<rceil>"
  by auto 

lemma impl_prop [simp]: "\<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow>  Q s)"
  by auto 

subsubsection \<open>Store and Assignment\<close>

type_synonym 'a store = "string  \<Rightarrow> 'a"

definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
  "v ::= e = {(s, s(v := e s)) |s. True}"

lemma H_assign: "rel_kat.H \<lceil>\<lambda>s. P (s (v := e s))\<rceil> (v ::= e) \<lceil>P\<rceil>"
  by (auto simp: gets_def rel_kat.H_def rel_kat.t_op_def rel_at_def)

lemma H_assign_var: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
  by (auto simp: gets_def rel_kat.H_def rel_kat.t_op_def rel_at_def)

abbreviation H_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("PRE _ _ POST _" [64,64,64] 63) where
  "PRE P X POST Q \<equiv> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"

abbreviation if_then_else_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> rel_kat.if_then_else \<lceil>P\<rceil> X Y"

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ INV _ DO _ OD" [64,64,64] 63) where
  "WHILE P INV I DO X OD \<equiv> rel_kat.while_inv \<lceil>P\<rceil> \<lceil>I\<rceil> X"

subsubsection \<open>Verification Example\<close>

lemma euclid:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (rule rel_kat.H_while_inv, simp_all, clarsimp)
  apply (intro rel_kat.H_seq)
  apply (subst H_assign, simp)+
  apply (rule H_assign_var)
  using gcd_red_nat by auto

subsubsection \<open>Definition of Refinement KAT\<close>

class rkat = kat +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes R1: "H p (R p q) q"
  and R2: "H p x q \<Longrightarrow> x \<le> R p q"

begin

subsubsection \<open>Propositional Refinement Calculus\<close>

lemma R_skip: "1 \<le> R p p"
  by (simp add: H_skip R2)

lemma R_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> R p' q' \<le> R p q"
  by (simp add: H_cons R2 R1)

lemma R_seq: "(R p r) \<cdot> (R r q) \<le> R p q"
  using H_seq R2 R1 by blast

lemma R_cond: "if v then (R (t v \<cdot> t p) q) else (R (at v \<cdot> t p) q) fi \<le> R p q"
  by (metis H_cond R1 R2 t_comm t_n)

lemma R_loop: "while q do (R (t p \<cdot> t q) p) od  \<le> R p (t p \<cdot> at q)"
  by (simp add: H_loop R2 R1)

end

subsubsection \<open>Soundness and Relation RKAT\<close>

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_kat.H P X Q}"

interpretation rel_rkat: rkat Id "{}" "(\<union>)"  "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl rel_at rel_R
  by (standard, auto simp: rel_R_def rel_kat.H_def rel_kat.t_op_def rel_at_def)

subsubsection \<open>Assignment Laws\<close>

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (simp add: H_assign_var rel_rkat.R2)

lemma R_assignr: "(\<forall>s. Q' s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (rel_R \<lceil>P\<rceil> \<lceil>Q'\<rceil>) ; (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
proof -
  assume a1: "\<forall>s. Q' s \<longrightarrow> Q (s(v := e s))"
  have "\<forall>p pa cs f. \<exists>fa. (p fa \<or> cs ::= f \<subseteq> rel_R \<lceil>p\<rceil> \<lceil>pa\<rceil>) \<and> (\<not> pa (fa(cs := f fa::'a)) \<or> cs ::= f \<subseteq> rel_R \<lceil>p\<rceil> \<lceil>pa\<rceil>)"
    using R_assign by blast
  hence "v ::= e \<subseteq> rel_R \<lceil>Q'\<rceil> \<lceil>Q\<rceil>" 
    using a1 by blast
  thus ?thesis 
    by (meson dual_order.trans rel_d.mult_isol rel_rkat.R_seq)
qed

lemma R_assignl: "(\<forall>s. P s \<longrightarrow> P' (s (v := e s))) \<Longrightarrow> (v ::= e) ; (rel_R \<lceil>P'\<rceil> \<lceil>Q\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
proof -
  assume a1: "\<forall>s. P s \<longrightarrow> P' (s(v := e s))"
  have "\<forall>p pa cs f. \<exists>fa. (p fa \<or> cs ::= f \<subseteq> rel_R \<lceil>p\<rceil> \<lceil>pa\<rceil>) \<and> (\<not> pa (fa(cs := f fa::'a)) \<or> cs ::= f \<subseteq> rel_R \<lceil>p\<rceil> \<lceil>pa\<rceil>)"
    using R_assign by blast
  then have "v ::= e \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>P'\<rceil>"
    using a1 by blast
  then show ?thesis
    by (meson dual_order.trans rel_d.mult_isor rel_rkat.R_seq)
qed  

subsubsection \<open>Refinement Example\<close>

lemma var_swap_ref1: 
  "rel_R \<lceil>\<lambda>s. s ''x'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> 
   \<supseteq> (''z'' ::= (\<lambda>s. s ''x'')); rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>"
  by (rule R_assignl, auto) 

lemma var_swap_ref2: 
  "rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> 
   \<supseteq> (''x'' ::= (\<lambda>s. s ''y'')); rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''x'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>"
  by (rule R_assignl, auto)

lemma var_swap_ref3:  
  "rel_R \<lceil>\<lambda>s. s ''z'' = a \<and> s ''x'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> 
   \<supseteq> (''y'' ::= (\<lambda>s. s ''z'')); rel_R \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil>" 
  by (rule R_assignl, auto)

lemma var_swap_ref_var: 
  "rel_R \<lceil>\<lambda>s. s ''x'' = a \<and> s ''y'' = b\<rceil> \<lceil>\<lambda>s. s ''x'' = b \<and> s ''y'' = a\<rceil> 
   \<supseteq> (''z'' ::= (\<lambda>s. s ''x'')); (''x'' ::= (\<lambda>s. s ''y'')); (''y'' ::= (\<lambda>s. s ''z''))"
  using var_swap_ref1 var_swap_ref2 var_swap_ref3 rel_rkat.R_skip  by fastforce

end


