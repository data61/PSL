(* Title: Verification Component Based on KAT
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Components Based on Kleene Algebra with Tests\<close>

subsection \<open>Verification Component\<close>      

text \<open>This component supports the verification of simple while programs
in a partial correctness setting.\<close>

theory VC_KAT
imports "../P2S2R"
        KAT_and_DRA.PHL_KAT 
        KAT_and_DRA.KAT_Models

begin

text\<open>This first part changes some of the facts from the AFP KAT theories. It should be added to KAT in the next AFP version. 
Currently these facts provide an interface between the KAT theories and the verification component.\<close>

no_notation if_then_else ("if _ then _ else _ fi" [64,64,64] 63)
no_notation while ("while _ do _ od" [64,64] 63)
no_notation Archimedean_Field.ceiling ("\<lceil>_\<rceil>")

notation relcomp (infixl ";" 70)               
notation p2r ("\<lceil>_\<rceil>")

context kat 
begin

subsubsection \<open>Definitions of Hoare Triple\<close>

definition H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "H p x q \<longleftrightarrow> t p \<cdot> x \<le> x \<cdot> t q" 

lemma H_var1: "H p x q \<longleftrightarrow> t p \<cdot> x \<cdot> n q = 0"
  by (metis H_def n_kat_3 t_n_closed)

lemma H_var2: "H p x q \<longleftrightarrow> t p \<cdot> x = t p \<cdot> x \<cdot> t q"
  by (simp add: H_def n_kat_2)

subsubsection \<open>Syntax for Conditionals and Loops\<close>

definition ifthenelse :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("if _ then _ else _ fi" [64,64,64] 63) where
  "if p then x else y fi = (t p \<cdot> x + n p \<cdot> y)"

definition while :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ do _ od" [64,64] 63) where
  "while b do x od = (t b \<cdot> x)\<^sup>\<star> \<cdot> n b"

definition while_inv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("while _ inv _ do _ od" [64,64,64] 63) where
  "while p inv i do x od = while p do x od"

subsubsection \<open>Propositional Hoare Logic\<close>

lemma H_skip:  "H p 1 p"
  by (simp add: H_def)

lemma H_cons_1: "t p \<le> t p' \<Longrightarrow> H p' x q \<Longrightarrow> H p x q"
  using H_def phl_cons1 by blast

lemma H_cons_2: "t q' \<le> t q \<Longrightarrow> H p x q' \<Longrightarrow> H p x q"
  using H_def phl_cons2 by blast          

lemma H_cons: "t p \<le> t p' \<Longrightarrow> t q' \<le> t q \<Longrightarrow> H p' x q' \<Longrightarrow> H p x q"
  by (simp add: H_cons_1 H_cons_2)

lemma H_seq_swap: "H p x r \<Longrightarrow> H r y q \<Longrightarrow> H p (x \<cdot> y) q"
  by (simp add: H_def phl_seq)

lemma H_seq: "H r y q \<Longrightarrow> H p x r \<Longrightarrow> H p (x \<cdot> y) q"
  by (simp add: H_seq_swap)

lemma H_exp1: "H (t p \<cdot> t r) x q \<Longrightarrow> H p (t r \<cdot> x) q"
  using H_def n_de_morgan_var2 phl.ht_at_phl_export1 by auto

lemma H_exp2: "H p x q \<Longrightarrow> H p (x \<cdot> t r) (t q \<cdot> t r)"
  by (metis H_def phl.ht_at_phl_export2 test_mult)

lemma H_cond_iff: "H p (if r then x else y fi) q \<longleftrightarrow> H (t p \<cdot> t r) x q \<and> H (t p \<cdot> n r) y q"
proof -
  have "H p (if r then x else y fi) q \<longleftrightarrow> t p \<cdot> (t r \<cdot> x + n r \<cdot> y) \<cdot> n q = 0"
    by (simp add: H_var1 ifthenelse_def)
  also have "... \<longleftrightarrow> t p \<cdot> t r \<cdot> x \<cdot> n q + t p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (simp add: distrib_left mult_assoc)
  also have "... \<longleftrightarrow> t p \<cdot> t r \<cdot> x \<cdot> n q = 0 \<and> t p \<cdot> n r \<cdot> y \<cdot> n q = 0"
    by (metis add_0_left no_trivial_inverse)
  finally show ?thesis
    by (metis H_var1 test_mult)
qed

lemma H_cond: "H (t p \<cdot> t r) x q \<Longrightarrow> H (t p \<cdot> n r) y q \<Longrightarrow> H p (if r then x else y fi) q"
  by (simp add: H_cond_iff)

lemma H_loop: "H (t p \<cdot> t r) x p \<Longrightarrow> H p (while r do x od) (t p \<cdot> n r)"
proof -
  assume a1: "H (t p \<cdot> t r) x p"
  have "t (t p \<cdot> n r) = n r \<cdot> t p \<cdot> n r"
    using n_preserve test_mult by presburger
  then show ?thesis
    using a1 H_def H_exp1 conway.phl.it_simr phl_export2 while_def by auto
qed

lemma H_while_inv: "t p \<le> t i \<Longrightarrow> t i \<cdot> n r \<le> t q \<Longrightarrow> H (t i \<cdot> t r) x i \<Longrightarrow> H p (while r inv i do x od) q"
  by (metis H_cons H_loop test_mult while_inv_def)

text \<open>Finally we prove a frame rule.\<close>

lemma H_frame: "H p x p \<Longrightarrow> H q x r \<Longrightarrow> H (t p \<cdot> t q) x (t p \<cdot> t r)"
proof -
  assume "H p x p" and a: "H q x r"
  hence b: "t p \<cdot> x \<le> x \<cdot> t p" and "t q \<cdot> x \<le> x \<cdot> t r"
    using H_def apply blast using H_def a by blast
  hence "t p \<cdot> t q \<cdot> x \<le> t p \<cdot> x \<cdot> t r"
    by (simp add: mult_assoc mult_isol)
  also have "... \<le> x \<cdot> t p \<cdot> t r"
    by (simp add: b mult_isor)
  finally show ?thesis
    by (metis H_def mult_assoc test_mult)
qed
    
end

subsubsection \<open>Store and Assignment\<close>

text \<open>The proper verification component starts here.\<close>

type_synonym 'a store = "string  \<Rightarrow> 'a"

lemma t_p2r [simp]: "rel_dioid_tests.t \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (auto simp: p2r_def)

lemma impl_prop [simp]: "\<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow>  Q s)"
  by (auto simp: p2r_def)

lemma Id_simp [simp]: "Id \<inter> (- Id \<union> X) = Id \<inter> X" 
  by auto

lemma Id_p2r [simp]: "Id \<inter> \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (auto simp: Id_def p2r_def)

lemma Id_p2r_simp [simp]: "Id \<inter> (- Id \<union> \<lceil>P\<rceil>) = \<lceil>P\<rceil>"
  by simp 

text \<open>Next we derive the assignment command and assignment rules.\<close>

definition gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store rel" ("_ ::= _" [70, 65] 61) where 
  "v ::= e = {(s,s (v := e s)) |s. True}"

lemma H_assign_prop: "\<lceil>\<lambda>s. P (s (v := e s))\<rceil> ; (v ::= e) = (v ::= e) ; \<lceil>P\<rceil>"
  by (auto simp: p2r_def gets_def)

lemma H_assign: "rel_kat.H \<lceil>\<lambda>s. P (s (v := e s))\<rceil> (v ::= e) \<lceil>P\<rceil>"
  by (auto simp add: rel_kat.H_def gets_def p2r_def)

lemma H_assign_var: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
  by (auto simp: p2r_def gets_def rel_kat.H_def)

lemma H_assign_iff [simp]: "rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s. P s \<longrightarrow> Q (s (v := e s)))"
  by (auto simp: p2r_def gets_def rel_kat.H_def)

lemma H_assign_floyd: " rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>\<lambda>s. \<exists>w. s v = e (s(v := w)) \<and> P (s(v := w))\<rceil>"
  by (rule H_assign_var, metis fun_upd_same fun_upd_triv fun_upd_upd)

subsubsection \<open>Simplified Hoare Rules\<close>

lemma sH_cons_1: "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> rel_kat.H \<lceil>P'\<rceil> X \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"
  by (rule rel_kat.H_cons_1, auto simp only: p2r_def)

lemma sH_cons_2: "\<forall>s. Q' s \<longrightarrow> Q s \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q'\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"
  by (rule rel_kat.H_cons_2, auto simp only: p2r_def)

lemma sH_cons: "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> \<forall>s. Q' s \<longrightarrow> Q s \<Longrightarrow> rel_kat.H \<lceil>P'\<rceil> X \<lceil>Q'\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"
  by (simp add: sH_cons_1 sH_cons_2)
  
lemma sH_cond: "rel_kat.H \<lceil>P \<sqinter> T\<rceil> X \<lceil>Q\<rceil> \<Longrightarrow> rel_kat.H \<lceil>P \<sqinter> - T\<rceil> Y \<lceil>Q\<rceil>  \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (rel_kat.ifthenelse \<lceil>T\<rceil> X Y) \<lceil>Q\<rceil>"
  by (rule rel_kat.H_cond, auto simp add: rel_kat.H_def p2r_def, blast+)

lemma sH_cond_iff: "rel_kat.H \<lceil>P\<rceil> (rel_kat.ifthenelse \<lceil>T\<rceil> X Y) \<lceil>Q\<rceil> \<longleftrightarrow> (rel_kat.H \<lceil>P \<sqinter> T\<rceil> X \<lceil>Q\<rceil> \<and> rel_kat.H \<lceil>P \<sqinter> - T\<rceil> Y \<lceil>Q\<rceil>)"
  by (simp add: rel_kat.H_cond_iff)

lemma sH_while_inv: "\<forall>s. P s \<longrightarrow> I s \<Longrightarrow> \<forall>s. I s \<and> \<not> R s \<longrightarrow> Q s \<Longrightarrow> rel_kat.H \<lceil>I \<sqinter> R\<rceil> X \<lceil>I\<rceil> 
                     \<Longrightarrow> rel_kat.H \<lceil>P\<rceil> (rel_kat.while_inv \<lceil>R\<rceil> \<lceil>I\<rceil> X) \<lceil>Q\<rceil>"
  by (rule rel_kat.H_while_inv, auto simp: p2r_def rel_kat.H_def, fastforce)

lemma sH_H: "rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil> \<longleftrightarrow> (\<forall>s s'. P s \<longrightarrow> (s,s') \<in> X \<longrightarrow> Q s')"
  by (simp add: rel_kat.H_def, auto simp add: p2r_def)

text \<open>Finally we provide additional syntax for specifications and commands.\<close>
 
abbreviation H_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a pred \<Rightarrow> bool" ("PRE _ _ POST _" [64,64,64] 63) where
  "PRE P X POST Q \<equiv> rel_kat.H \<lceil>P\<rceil> X \<lceil>Q\<rceil>"

abbreviation if_then_else_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> rel_kat.ifthenelse \<lceil>P\<rceil> X Y"

abbreviation while_sugar :: "'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ DO _ OD" [64,64] 63) where
  "WHILE P  DO X OD \<equiv> rel_kat.while \<lceil>P\<rceil> X"

abbreviation while_inv_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a rel \<Rightarrow> 'a rel" ("WHILE _ INV _ DO _ OD" [64,64,64] 63) where
  "WHILE P INV I DO X OD \<equiv> rel_kat.while_inv \<lceil>P\<rceil> \<lceil>I\<rceil> X"

lemma H_cond_iff2[simp]: "PRE p (IF r THEN x ELSE y FI) POST q \<longleftrightarrow> (PRE (p \<sqinter> r) x POST q) \<and> (PRE (p \<sqinter> - r) y POST q)"
  by (simp add: rel_kat.H_cond_iff)

end
