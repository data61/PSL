(* Title: Adaptation of example from HOL/Hoare/Separation
   Author: Gerwin Klein, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

section "Example from HOL/Hoare/Separation"

theory Simple_Separation_Example
  imports "HOL-Hoare.Hoare_Logic_Abort" "../Sep_Heap_Instance"
          "../Sep_Tactics"
begin

declare [[syntax_ambiguity_warning = false]]

type_synonym heap = "(nat \<Rightarrow> nat option)"

(* This syntax isn't ideal, but this is what is used in the original *)
definition maps_to:: "nat \<Rightarrow> nat \<Rightarrow> heap \<Rightarrow> bool" ("_ \<mapsto> _" [56,51] 56)
  where "x \<mapsto> y \<equiv> \<lambda>h. h = [x \<mapsto> y]"

(* If you don't mind syntax ambiguity: *)
notation pred_ex  (binder "\<exists>" 10)

(* could be generated automatically *)
definition maps_to_ex :: "nat \<Rightarrow> heap \<Rightarrow> bool" ("_ \<mapsto> -" [56] 56)
  where "x \<mapsto> - \<equiv> \<exists>y. x \<mapsto> y"


(* could be generated automatically *)
lemma maps_to_maps_to_ex [elim!]:
  "(p \<mapsto> v) s \<Longrightarrow> (p \<mapsto> -) s"
  by (auto simp: maps_to_ex_def)

(* The basic properties of maps_to: *)
lemma maps_to_write:
  "(p \<mapsto> - ** P) H \<Longrightarrow> (p \<mapsto> v ** P) (H (p \<mapsto> v))"
  apply (clarsimp simp: sep_conj_def maps_to_def maps_to_ex_def split: option.splits)
  apply (rule_tac x=y in exI)
  apply (auto simp: sep_disj_fun_def map_convs map_add_def split: option.splits)
  done

lemma points_to:
  "(p \<mapsto> v ** P) H \<Longrightarrow> the (H p) = v"
  by (auto elim!: sep_conjE
           simp: sep_disj_fun_def maps_to_def map_convs map_add_def
           split: option.splits)


(* This differs from the original and uses separation logic for the definition. *)
primrec
  list :: "nat \<Rightarrow> nat list \<Rightarrow> heap \<Rightarrow> bool"
where
  "list i [] = (\<langle>i=0\<rangle> and \<box>)"
| "list i (x#xs) = (\<langle>i=x \<and> i\<noteq>0\<rangle> and (EXS j. i \<mapsto> j ** list j xs))"

lemma list_empty [simp]:
  shows "list 0 xs = (\<lambda>s. xs = [] \<and> \<box> s)"
  by (cases xs) auto

(* The examples from Hoare/Separation.thy *)
lemma "VARS x y z w h
 {(x \<mapsto> y ** z \<mapsto> w) h}
 SKIP
 {x \<noteq> z}"
  apply vcg
  apply(auto elim!: sep_conjE simp: maps_to_def sep_disj_fun_def domain_conv)
done

lemma "VARS H x y z w
 {(P ** Q) H}
 SKIP
 {(Q ** P) H}"
  apply vcg
  apply(simp add: sep_conj_commute)
done

lemma "VARS H
 {p\<noteq>0 \<and> (p \<mapsto> - ** list q qs) H}
 H := H(p \<mapsto> q)
 {list p (p#qs) H}"
  apply vcg
  apply (auto intro: maps_to_write)
done

lemma "VARS H p q r
  {(list p Ps ** list q Qs) H}
  WHILE p \<noteq> 0
  INV {\<exists>ps qs. (list p ps ** list q qs) H \<and> rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := the(H p); H := H(r \<mapsto> q); q := r OD
  {list q (rev Ps @ Qs) H}"
  apply vcg
    apply fastforce
   apply clarsimp
   apply (case_tac ps, simp)
   apply (rename_tac p ps')
   apply (clarsimp simp: sep_conj_exists sep_conj_ac)
   apply (sep_subst points_to)
   apply (rule_tac x = "ps'" in exI)
   apply (rule_tac x = "p # qs" in exI)
   apply (simp add: sep_conj_exists sep_conj_ac)
   apply (rule exI)
   apply (sep_rule maps_to_write)
   apply ((sep_cancel add: maps_to_maps_to_ex)+)[1]
  apply clarsimp
  done

end
