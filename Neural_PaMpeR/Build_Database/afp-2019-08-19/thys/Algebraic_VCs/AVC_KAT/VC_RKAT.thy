(* Title: Refinement Component Based on KAT
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

theory VC_RKAT
  imports "../RKAT_Models"

begin

text \<open>This component supports the step-wise refinement of simple while programs
in a partial correctness setting.\<close>

subsubsection \<open>Assignment Laws\<close>

text \<open>The store model is taken from KAT\<close>

lemma R_assign: "(\<forall>s. P s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
proof - 
  assume "(\<forall>s. P s \<longrightarrow> Q (s (v := e s)))"
  hence "rel_kat.H \<lceil>P\<rceil> (v ::= e) \<lceil>Q\<rceil>"
    by (rule H_assign_var)
  thus ?thesis
    by (rule rel_rkat.R2)
qed

lemma R_assignr: "(\<forall>s. Q' s \<longrightarrow> Q (s (v := e s))) \<Longrightarrow> (rel_R \<lceil>P\<rceil> \<lceil>Q'\<rceil>) ; (v ::= e) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"  
  by (metis H_assign_var rel_kat.H_seq rel_rkat.R1 rel_rkat.R2)   

lemma R_assignl: "(\<forall>s. P s \<longrightarrow> P' (s (v := e s))) \<Longrightarrow> (v ::= e) ; (rel_R \<lceil>P'\<rceil> \<lceil>Q\<rceil>) \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (metis H_assign_var rel_kat.H_seq rel_rkat.R1 rel_rkat.R2)

subsubsection \<open>Simplified Refinement Laws\<close>

lemma R_cons: "(\<forall>s. P s \<longrightarrow> P' s) \<Longrightarrow> (\<forall>s. Q' s \<longrightarrow> Q s) \<Longrightarrow> rel_R \<lceil>P'\<rceil> \<lceil>Q'\<rceil> \<subseteq> rel_R \<lceil>P\<rceil> \<lceil>Q\<rceil>"
  by (simp add: rel_rkat.R1 rel_rkat.R2 sH_cons_1 sH_cons_2)

lemma if_then_else_ref: "X \<subseteq> X' \<Longrightarrow> Y \<subseteq> Y' \<Longrightarrow> IF P THEN X ELSE Y FI \<subseteq> IF P THEN X' ELSE Y' FI"
  by (auto simp: rel_kat.ifthenelse_def)
                                     
lemma while_ref: "X \<subseteq> X' \<Longrightarrow> WHILE P DO X OD \<subseteq> WHILE P DO X' OD"
  by (simp add: rel_kat.while_def rel_dioid.mult_isol rel_dioid.mult_isor rel_kleene_algebra.star_iso)
                                                               
end


