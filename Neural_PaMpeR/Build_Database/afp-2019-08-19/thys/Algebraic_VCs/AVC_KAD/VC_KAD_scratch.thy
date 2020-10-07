(* Title: Program Correctness Component Based on Kleene Algebra with Domain
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsection\<open>Component Based on Kleene Algebra with Domain\<close>

text \<open>This component supports the verification and step-wise refinement of simple while programs
in a partial correctness setting.\<close>

theory VC_KAD_scratch
  imports Main
begin

subsubsection \<open>KAD: Definitions and Basic Properties\<close>

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
  by (standard, simp_all add: less_def less_eq_def add_commute, auto, metis add_assoc)

lemma mult_isor: "x \<le> y \<Longrightarrow> x \<cdot> z \<le> y \<cdot> z"   
  by (metis distrib_right less_eq_def)

lemma mult_isol: "x \<le> y \<Longrightarrow> z \<cdot> x \<le> z \<cdot> y"   
  by (metis distrib_left less_eq_def)   

lemma add_iso: "x \<le> y \<Longrightarrow> z + x \<le> z + y"
  by (metis add.semigroup_axioms add_idem less_eq_def semigroup.assoc)

lemma add_ub: "x \<le> x + y"
  by (metis add_assoc add_idem less_eq_def)

lemma add_lub: "x + y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (metis add_assoc add_commute less_eq_def order.ordering_axioms ordering.refl)

end

class kleene_algebra  = dioid +
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

class antidomain_kleene_algebra = kleene_algebra + 
  fixes ad :: "'a \<Rightarrow> 'a" ("ad")
  assumes as1 [simp]: "ad x \<cdot> x = 0"
  and as2 [simp]: "ad (x \<cdot> y) + ad (x \<cdot> ad (ad y)) = ad (x \<cdot> ad (ad y))"
  and as3 [simp]: "ad (ad x) + ad x = 1"

begin

definition dom_op :: "'a \<Rightarrow> 'a" ("d") where
  "d x = ad (ad x)"

lemma a_subid_aux: "ad x \<cdot> y \<le> y"
  by (metis add_commute add_ub as3 mult_1_left mult_isor)

lemma d1_a [simp]: "d x \<cdot> x = x"
  by (metis add_commute dom_op_def add_zerol as1 as3 distrib_right mult_1_left)

lemma a_mul_d [simp]: "ad x \<cdot> d x = 0"
  by (metis add_commute dom_op_def add_zerol as1 as2 distrib_right mult_1_left)

lemma a_d_closed [simp]: "d (ad x) = ad x"
  by (metis d1_a dom_op_def add_zerol as1 as3 distrib_left mult_1_right)

lemma a_idem [simp]: "ad x \<cdot> ad x = ad x"
  by (metis a_d_closed d1_a)

lemma meet_ord: "ad x \<le> ad y \<longleftrightarrow> ad x \<cdot> ad y = ad x"
  by (metis a_d_closed a_subid_aux d1_a antisym mult_1_right mult_isol)

lemma d_wloc: "x \<cdot> y = 0 \<longleftrightarrow> x \<cdot> d y = 0"
  by (metis a_subid_aux d1_a dom_op_def add_ub antisym as1 as2 mult_1_right mult_assoc)

lemma gla_1: "ad x \<cdot> y = 0 \<Longrightarrow> ad x \<le> ad y"
  by (metis a_subid_aux d_wloc dom_op_def add_zerol as3 distrib_left mult_1_right)

lemma a2_eq [simp]: "ad (x \<cdot> d y) = ad (x \<cdot> y)"
  by (metis a_mul_d d1_a dom_op_def gla_1 add_ub antisym as1 as2 mult_assoc)

lemma a_supdist: "ad (x + y) \<le> ad x"
  by (metis add_commute gla_1 add_ub add_zerol as1 distrib_left less_eq_def)

lemma a_antitone: "x \<le> y \<Longrightarrow> ad y \<le> ad x"
  by (metis a_supdist less_eq_def)

lemma a_comm: "ad x \<cdot> ad y = ad y \<cdot> ad x"
proof -
{ fix x y
  have "ad x \<cdot> ad y = d (ad x \<cdot> ad y) \<cdot> ad x \<cdot> ad y"
    by (simp add: mult_assoc)
  also have "... \<le> d (ad y) \<cdot> ad x"
    by (metis a_antitone a_d_closed a_subid_aux mult_oner a_subid_aux dom_op_def mult_isol mult_isor meet_ord)   
  finally have "ad x \<cdot> ad y \<le> ad y \<cdot> ad x"
    by simp }
  thus ?thesis
    by (simp add: antisym)
qed

lemma a_closed [simp]: "d (ad x \<cdot> ad y) = ad x \<cdot> ad y"
proof -
  have f1: "\<And>x y. ad x \<le> ad (ad y \<cdot> x)"
    by (simp add: a_antitone a_subid_aux)
  have "\<And>x y. d (ad x \<cdot> y) \<le> ad x"
    by (metis a2_eq a_antitone a_comm a_d_closed dom_op_def f1)
  hence "\<And>x y. d (ad x \<cdot> y) \<cdot> y = ad x \<cdot> y"
    by (metis d1_a dom_op_def meet_ord mult_assoc)
  thus ?thesis
    by (metis a_comm a_idem dom_op_def)
qed

lemma a_exp [simp]: "ad (ad x \<cdot> y) = d x + ad y"
proof (rule antisym)
  have "ad (ad x \<cdot> y) \<cdot> ad x \<cdot> d y = 0"
    using d_wloc mult_assoc by fastforce
  hence a: "ad (ad x \<cdot> y) \<cdot> d y \<le> d x"
    by (metis a_closed a_comm dom_op_def gla_1 mult_assoc)
  have "ad (ad x \<cdot> y) = ad (ad x \<cdot> y) \<cdot> d y + ad (ad x \<cdot> y) \<cdot> ad y"
    by (metis dom_op_def as3 distrib_left mult_oner)
  also have "... \<le> d x +  ad (ad x \<cdot> y) \<cdot> ad y"
    using a add_lub dual_order.trans by blast
  finally show "ad (ad x \<cdot> y) \<le> d x + ad y"
    by (metis a_antitone a_comm a_subid_aux meet_ord)
next
  have "ad y \<le> ad (ad x \<cdot> y)"
    by (simp add: a_antitone a_subid_aux)
  thus "d x + ad y \<le> ad (ad x \<cdot> y)"
    by (metis a2_eq a_antitone a_comm a_subid_aux dom_op_def add_lub)
qed  

lemma d1_sum_var: "x + y \<le> (d x + d y) \<cdot> (x + y)"
proof -
  have "x + y = d x \<cdot> x + d y \<cdot> y"
    by simp
  also have "... \<le> (d x + d y) \<cdot> x + (d x + d y) \<cdot> y"
    by (metis add_commute add_lub add_ub combine_common_factor)
  finally show ?thesis
    by (simp add: distrib_left)
qed

lemma a4: "ad (x + y) = ad x \<cdot> ad y"
proof (rule antisym)
  show "ad (x + y) \<le> ad x \<cdot> ad y"
    by (metis a_supdist add_commute mult_isor meet_ord)
  hence "ad x \<cdot> ad y = ad x \<cdot> ad y + ad (x + y)"
    using less_eq_def add_commute by simp
  also have "... = ad (ad (ad x \<cdot> ad y) \<cdot> (x + y))"
    by (metis a_closed a_exp)
  finally show "ad x \<cdot> ad y \<le> ad (x + y)"
    using a_antitone d1_sum_var dom_op_def by auto
qed

lemma kat_prop: "d x \<cdot> y \<le> y \<cdot> d z \<longleftrightarrow> d x \<cdot> y \<cdot> ad z = 0"
proof
  show  "d x \<cdot> y \<le> y \<cdot> d z \<Longrightarrow> d x \<cdot> y \<cdot> ad z = 0"
    by (metis add_commute dom_op_def add_zerol annir as1 less_eq_def mult_isor mult_assoc)
next 
  assume h: "d x \<cdot> y \<cdot> ad z = 0"
  hence "d x \<cdot> y = d x \<cdot> y \<cdot> d z + d x \<cdot> y \<cdot> ad z"
    by (metis dom_op_def as3 distrib_left mult_1_right)
  thus  "d x \<cdot> y \<le> y \<cdot> d z"
    by (metis a_subid_aux add_commute dom_op_def h add_zerol mult_assoc)
qed

lemma shunt: "ad x \<le> ad y + ad z \<longleftrightarrow> ad x \<cdot> d y \<le> ad z" 
proof 
  assume "ad x \<le> ad y + ad z"
  hence "ad x \<cdot> d y \<le> ad y \<cdot> d y + ad z \<cdot> d y"
    by (metis distrib_right mult_isor)
  thus " ad x \<cdot> d y \<le> ad z"
    by (metis a_closed a_d_closed a_exp a_mul_d a_supdist dom_op_def dual_order.trans less_eq_def)
next 
  assume h: "ad x \<cdot> d y \<le> ad z"
  have "ad x = ad x \<cdot> ad y + ad x \<cdot> d y"
    by (metis add_commute dom_op_def as3 distrib_left mult_1_right)
  also have "... \<le> ad x \<cdot> ad y + ad z"
    using h add_lub dual_order.trans by blast
  also have "... \<le> ad y + ad z"
    by (metis a_subid_aux add_commute add_lub add_ub dual_order.trans)
  finally show "ad x \<le> ad y + ad z" 
    by simp
qed

subsubsection \<open>wp Calculus\<close>

definition if_then_else :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = d p \<cdot> x + ad p \<cdot> y"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while p do x od = (d p \<cdot> x)\<^sup>\<star> \<cdot> ad p"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

definition wp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "wp x p = ad (x \<cdot> ad p)"

lemma demod: " d p \<le> wp x q \<longleftrightarrow> d p \<cdot> x \<le> x \<cdot> d q"
  by (metis as1 dom_op_def gla_1 kat_prop meet_ord mult_assoc wp_def)

lemma wp_weaken: "wp x p \<le> wp (x \<cdot> ad q) (d p \<cdot> ad q)"
  by (metis a4 a_antitone a_d_closed a_mul_d dom_op_def gla_1 mult_isol mult_assoc wp_def)

lemma wp_seq [simp]: "wp (x \<cdot> y) q = wp x (wp y q)"
  using a2_eq dom_op_def mult_assoc wp_def by auto

lemma wp_seq_var: "p \<le> wp x r \<Longrightarrow> r \<le> wp y q \<Longrightarrow> p \<le> wp (x \<cdot> y) q"
proof -
  assume a1: "p \<le> wp x r"
  assume a2: "r \<le> wp y q"
  have "\<forall>z. \<not> wp x r \<le> z \<or> p \<le> z"
    using a1 dual_order.trans by blast
  then show ?thesis
    using a2 a_antitone mult_isol wp_def wp_seq by auto
qed

lemma wp_cond_var [simp]: "wp (if p then x else y fi) q = (ad p + wp x q) \<cdot> (d p + wp y q)"
  using a4 a_d_closed dom_op_def if_then_else_def distrib_right mult_assoc wp_def by auto

lemma wp_cond_aux1 [simp]: "d p \<cdot> wp (if p then x else y fi) q = d p \<cdot> wp x q"
proof -
  have "d p \<cdot> wp (if p then x else y fi) q = ad (ad p) \<cdot> (ad p + wp x q) \<cdot> (d p + wp y q)"
    using dom_op_def mult.semigroup_axioms semigroup.assoc wp_cond_var by fastforce
  also have "... = wp x q \<cdot> d p \<cdot> (d p + d (wp y q))"
    using a_comm a_d_closed dom_op_def distrib_left wp_def by auto 
  also have "... = wp x q \<cdot> d p"
    by (metis a_exp dom_op_def add_ub meet_ord mult_assoc)
  finally show ?thesis
    by (simp add: a_comm dom_op_def wp_def)
qed

lemma wp_cond_aux2 [simp]: "ad p \<cdot> wp (if p then x else y fi) q = ad p \<cdot> wp y q"
  by (metis (no_types) abel_semigroup.commute if_then_else_def a_d_closed add.abel_semigroup_axioms dom_op_def wp_cond_aux1)

lemma wp_cond [simp]: "wp (if p then x else y fi) q = (d p \<cdot> wp x q) + (ad p \<cdot> wp y q)"
  by (metis as3 distrib_right dom_op_def mult_1_left wp_cond_aux2 wp_cond_aux1)

lemma wp_star_induct_var: "d q \<le> wp x q \<Longrightarrow> d q \<le> wp (x\<^sup>\<star>) q" 
  using demod star_sim by blast

lemma wp_while: "d p \<cdot> d r \<le> wp x p \<Longrightarrow> d p \<le> wp (while r do x od) (d p \<cdot> ad r)"
proof -
  assume "d p \<cdot> d r \<le> wp x p"
  hence "d p \<le> wp (d r \<cdot> x) p"
    using dom_op_def mult.semigroup_axioms semigroup.assoc shunt wp_def by fastforce
  hence "d p \<le> wp ((d r \<cdot> x)\<^sup>\<star>) p"
    using wp_star_induct_var by blast
  thus ?thesis
    by (metis order.ordering_axioms ordering.trans while_def wp_weaken)
qed

lemma wp_while_inv: "d p \<le> d i \<Longrightarrow> d i \<cdot> ad r \<le> d q \<Longrightarrow> d i \<cdot> d r \<le> wp x i \<Longrightarrow> d p \<le> wp (while r inv i do x od) q"
proof -
  assume a1: "d p \<le> d i" and a2: "d i \<cdot> ad r \<le> d q" and "d i \<cdot> d r \<le> wp x i"
  hence "d i \<le> wp (while r inv i do x od) (d i \<cdot> ad r)"
    by (simp add: while_inv_def wp_while)
  also have "... \<le>  wp (while r inv i do x od) q"
    by (metis a2 a_antitone a_d_closed dom_op_def mult_isol wp_def)
  finally show ?thesis
    using a1 dual_order.trans by blast
qed

lemma wp_while_inv_break: "d p \<le> wp y i \<Longrightarrow> d i \<cdot> ad r \<le> d q \<Longrightarrow> d i \<cdot> d r \<le> wp x i \<Longrightarrow> d p \<le> wp (y \<cdot> (while r inv i do x od)) q"
  by (metis dom_op_def eq_refl mult_1_left mult_1_right wp_def wp_seq wp_seq_var wp_while_inv)

end

subsubsection \<open>Soundness and Relation KAD\<close>

notation relcomp (infixl ";" 70)

interpretation rel_d: dioid Id "{}" "(\<union>)" "(;)" "(\<subseteq>)" "(\<subset>)"
  by (standard, auto)

lemma (in dioid) pow_inductl: "z + x \<cdot> y \<le> y \<Longrightarrow> x ^ i \<cdot> z \<le> y"
  apply (induct i; clarsimp simp add: add_lub)
  by (metis local.dual_order.trans local.mult_isol mult_assoc)

lemma (in dioid) pow_inductr: "z + y \<cdot> x \<le> y \<Longrightarrow> z \<cdot> x ^ i \<le> y"
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

definition rel_ad :: "'a rel \<Rightarrow> 'a rel" where
  "rel_ad R = {(x,x) | x. \<not> (\<exists>y. (x,y) \<in> R)}" 

interpretation rel_aka: antidomain_kleene_algebra Id "{}" "(\<union>)"  "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl rel_ad
  apply standard
  apply auto[2]
  by (auto simp: rel_star_contr rel_d.pow_inductl rel_star_contl SUP_least rel_d.pow_inductr rel_ad_def)

subsubsection \<open>Embedding Predicates in Relations\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

abbreviation p2r :: "'a pred \<Rightarrow> 'a rel" ("\<lceil>_\<rceil>") where
  "\<lceil>P\<rceil> \<equiv> {(s,s) |s. P s}"

lemma d_p2r [simp]: "rel_aka.dom_op \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (auto simp: rel_aka.dom_op_def rel_ad_def)

lemma p2r_neg_hom [simp]: "rel_ad \<lceil>P\<rceil> = \<lceil>\<lambda>s. \<not>P s\<rceil>" 
  by (auto simp: rel_ad_def)

lemma p2r_conj_hom [simp]: "\<lceil>P\<rceil> \<inter> \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>"
  by auto

lemma p2r_conj_hom_var [simp]: "\<lceil>P\<rceil> ; \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<and> Q s\<rceil>" 
  by auto

lemma p2r_disj_hom [simp]: "\<lceil>P\<rceil> \<union> \<lceil>Q\<rceil> = \<lceil>\<lambda>s. P s \<or> Q s\<rceil>"
  by auto

subsubsection \<open>Store and Assignment\<close>

type_synonym 'a store = "string  \<Rightarrow> 'a"

definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
  "v ::= e = {(s,s (v := e s)) |s. True}"

lemma wp_assign [simp]: "rel_aka.wp (v ::= e) \<lceil>Q\<rceil> = \<lceil>\<lambda>s. Q (s (v := e s))\<rceil>"
  by (auto simp: rel_aka.wp_def gets_def rel_ad_def)

abbreviation spec_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("PRE _ _ POST _" [64,64,64] 63) where
  "PRE P X POST Q \<equiv> rel_aka.dom_op \<lceil>P\<rceil> \<subseteq> rel_aka.wp X \<lceil>Q\<rceil>"

abbreviation if_then_else_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> rel_aka.if_then_else \<lceil>P\<rceil> X Y"

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ INV _ DO _ OD" [64,64,64] 63) where
  "WHILE P INV I DO X OD \<equiv> rel_aka.while_inv \<lceil>P\<rceil> \<lceil>I\<rceil> X"

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
  apply (rule rel_aka.wp_while_inv, simp_all) using gcd_red_nat by auto

context antidomain_kleene_algebra
begin

subsubsection\<open>Propositional Hoare Logic\<close>

definition H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "H p x q \<longleftrightarrow> d p \<le> wp x q"

lemma H_skip: "H p 1 p"
  by (simp add: H_def dom_op_def wp_def)

lemma H_cons: "d p \<le> d p' \<Longrightarrow> d q' \<le> d q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (meson H_def demod mult_isol order_trans)

lemma H_seq: "H p x r \<Longrightarrow> H r y q \<Longrightarrow> H p (x \<cdot> y) q"
  by (metis H_def a_d_closed demod dom_op_def wp_seq_var)

lemma H_cond: "H (d p \<cdot> d r) x q \<Longrightarrow> H (d p \<cdot> ad r) y q \<Longrightarrow> H p (if r then x else y fi) q"
proof -
  assume  h1: "H (d p \<cdot> d r) x q" and h2: "H (d p \<cdot> ad r) y q"
  hence h3: "d p \<cdot> d r \<le> wp x q" and h4: "d p \<cdot> ad r \<le> wp y q"
    using H_def a_closed dom_op_def apply auto[1]
    using H_def h2 a_closed dom_op_def by auto
  hence h5: "d p  \<le> ad r + wp x q" and h6: "d p  \<le> d r + wp y q"
    apply (simp add: dom_op_def shunt wp_def)
    using h4 a_d_closed dom_op_def shunt wp_def by auto
  hence "d p \<le> d p  \<cdot> (d r + wp y q)"
    by (metis a_idem distrib_left dom_op_def less_eq_def)
  also have  "... \<le> (ad r + wp x q) \<cdot> (d r + wp y q)"
    by (simp add: h5 mult_isor)
  finally show ?thesis
    by (simp add: H_def)
qed

lemma H_loop: "H (d p \<cdot> d r) x p \<Longrightarrow> H p (while r do x od) (d p \<cdot> ad r)"
  by (metis (full_types) H_def a_closed dom_op_def wp_while)

lemma H_while_inv: "d p \<le> d i \<Longrightarrow> d i \<cdot> ad r \<le> d q \<Longrightarrow> H (d i \<cdot> d r) x i \<Longrightarrow> H p (while r inv i do x od) q"
  using H_def a_closed dom_op_def wp_while_inv by auto

end

subsubsection\<open>Definition of Refinement KAD\<close>

class rkad = antidomain_kleene_algebra +
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes R_def: "x \<le> R p q \<longleftrightarrow> d p \<le> wp x q"

begin

subsubsection \<open>Propositional Refinement Calculus\<close>

lemma HR: "H p x q \<longleftrightarrow> x \<le> R p q"
  by (simp add: H_def R_def)

lemma wp_R1: "d p \<le> wp (R p q) q"
  using R_def by blast

lemma wp_R2: "x \<le> R (wp x q) q"
  by (simp add: R_def wp_def)

lemma wp_R3: "d p \<le> wp x q \<Longrightarrow> x \<le> R p q"
  by (simp add: R_def)

lemma H_R1: "H p (R p q) q"
  by (simp add: HR)

lemma H_R2: "H p x q \<Longrightarrow> x \<le> R p q"
  by (simp add: HR)

lemma R_skip: "1 \<le> R p p"
  by (simp add: H_R2 H_skip)

lemma R_cons: "d p \<le> d p' \<Longrightarrow> d q' \<le> d q \<Longrightarrow> R p' q' \<le> R p q"
  by (simp add: H_R1 H_R2 H_cons)

lemma R_seq: "(R p r) \<cdot> (R r q) \<le> R p q"
  using H_R1 H_R2 H_seq by blast

lemma R_cond: "if v then (R (d v \<cdot> d p) q) else (R (ad v \<cdot> d p) q) fi \<le> R p q"
  by (simp add: H_R1 H_R2 H_cond a_comm dom_op_def)

lemma R_loop: "while q do (R (d p \<cdot> d q) p) od \<le> R p (d p \<cdot> ad q)"
  by (simp add: H_R1 H_R2 H_loop)

end

subsubsection \<open>Soundness and Relation RKAD\<close>

definition rel_R :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" where 
  "rel_R P Q = \<Union>{X. rel_aka.dom_op P \<subseteq> rel_aka.wp X Q}"

interpretation rel_rkad: rkad Id "{}" "(\<union>)"  "(;)" "(\<subseteq>)" "(\<subset>)" rtrancl rel_ad rel_R
  by (standard, auto simp: rel_R_def rel_aka.dom_op_def rel_ad_def rel_aka.wp_def, blast)

subsubsection \<open>Assignment Laws\<close>

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (auto simp: rel_rkad.R_def)

lemma H_assign_var: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> rel_aka.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
  by (auto simp: rel_aka.H_def rel_aka.dom_op_def rel_ad_def gets_def rel_aka.wp_def)

lemma R_assignr: "(\<forall>s. Q' s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (rel_R \<lceil>P\<rceil> \<lceil>Q'\<rceil>) ; (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  apply (subst rel_rkad.HR[symmetric], rule rel_aka.H_seq) defer 
  by (erule H_assign_var, simp add: rel_rkad.H_R1)

lemma R_assignl: "(\<forall>s. P s \<longrightarrow> P' (s (v := e s))) \<Longrightarrow> (v ::= e) ; (rel_R \<lceil>P'\<rceil> \<lceil>Q\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (subst rel_rkad.HR[symmetric], rule rel_aka.H_seq, erule H_assign_var, simp add: rel_rkad.H_R1)

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
  using var_swap_ref1 var_swap_ref2 var_swap_ref3 rel_rkad.R_skip  by fastforce

end



