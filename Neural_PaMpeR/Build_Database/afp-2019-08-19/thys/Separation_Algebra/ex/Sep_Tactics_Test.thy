(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

theory Sep_Tactics_Test
imports "../Sep_Tactics"
begin

text \<open>Substitution and forward/backward reasoning\<close>

typedecl p
typedecl val
typedecl heap

axiomatization where heap_sep_algebra: "OFCLASS(heap, sep_algebra_class)"
instance heap :: sep_algebra by (rule heap_sep_algebra)

axiomatization
  points_to :: "p \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> bool" and
  val :: "heap \<Rightarrow> p \<Rightarrow> val"
where
  points_to: "(points_to p v ** P) h \<Longrightarrow> val h p = v"


lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_subst (2) points_to)
  apply (sep_subst (asm) points_to)
  apply (sep_subst points_to)
  oops

lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_drule points_to)
  apply simp
  oops

lemma
  "\<lbrakk> Q2 (val h p); (K ** T ** blub ** P ** points_to p v ** P ** J) h \<rbrakk>
   \<Longrightarrow> Q (val h p) (val h p)"
  apply (sep_frule points_to)
  apply simp
  oops

consts
  update :: "p \<Rightarrow> val \<Rightarrow> heap \<Rightarrow> heap"

schematic_goal
  assumes a: "\<And>P. (stuff p ** P) H \<Longrightarrow> (other_stuff p v ** P) (update p v H)"
  shows "(X ** Y ** other_stuff p ?v) (update p v H)"
  apply (sep_rule a)
  oops


text \<open>Example of low-level rewrites\<close>

lemma "\<lbrakk> unrelated s ; (P ** Q ** R) s \<rbrakk> \<Longrightarrow> (A ** B ** Q ** P) s"
  apply (tactic \<open>dresolve_tac @{context} [mk_sep_select_rule @{context} true (3, 1)] 1\<close>)
  apply (tactic \<open>resolve_tac @{context} [mk_sep_select_rule @{context} false (4, 2)] 1\<close>)
  (* now sep_conj_impl1 can be used *)
  apply (erule (1) sep_conj_impl)
  oops


text \<open>Conjunct selection\<close>

lemma "(A ** B ** Q ** P) s"
  apply (sep_select 1)
  apply (sep_select 3)
  apply (sep_select 4)
  oops

lemma "\<lbrakk> also unrelated; (A ** B ** Q ** P) s \<rbrakk> \<Longrightarrow> unrelated"
  apply (sep_select_asm 2)
  oops


section \<open>Test cases for \<open>sep_cancel\<close>.\<close>

lemma
  assumes forward: "\<And>s g p v. A g p v s \<Longrightarrow> AA g p s "
  shows "\<And>xv yv P s y x s. (A g x yv ** A g y yv ** P) s \<Longrightarrow> (AA g y ** sep_true) s"
  by (sep_cancel add: forward)

lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "(A ** generic ** B) s \<Longrightarrow> (instance ** sep_true) s"
  by (sep_cancel add: forward)

lemma "\<lbrakk> (A ** B) sa ; (A ** Y) s \<rbrakk> \<Longrightarrow> (A ** X) s"
  apply (sep_cancel)
  oops

lemma "\<lbrakk> (A ** B) sa ; (A ** Y) s \<rbrakk> \<Longrightarrow> (\<lambda>s. (A ** X) s) s"
  apply (sep_cancel)
  oops

schematic_goal "\<lbrakk> (B ** A ** C) s \<rbrakk> \<Longrightarrow> (\<lambda>s. (A ** ?X) s) s"
  by (sep_cancel)

(* test backtracking on premises with same state *)
lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "\<lbrakk> (A ** B) s ; (generic ** Y) s \<rbrakk> \<Longrightarrow> (X ** instance) s"
  apply (sep_cancel add: forward)
  oops

lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  shows "generic s \<Longrightarrow> instance s"
  by (sep_cancel add: forward)

lemma
  assumes forward: "\<And>s. generic s \<Longrightarrow> instance s"
  assumes forward2: "\<And>s. instance s \<Longrightarrow> instance2 s"
  shows "generic s \<Longrightarrow> (instance2 ** sep_true) s"
  by (sep_cancel_blast add: forward forward2)

end

