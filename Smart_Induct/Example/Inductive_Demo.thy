(*
 * This file "Induction_Demo.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory Inductive_Demo
imports Main "../Smart_Induct"
begin

subsection "Inductive definition of the even numbers"

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"

thm ev0 evSS
thm ev.intros

text \<open>Using the introduction rules:\<close>

lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

thm evSS[OF evSS[OF ev0]]

text \<open>A recursive definition of evenness:\<close>

fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text \<open>A simple example of rule induction:\<close>

lemma "ev n \<Longrightarrow> evn n" smart_induct
apply(induction rule: ev.induct)
 apply(simp)
apply(simp)
done

text \<open>An induction on the computation of @{const evn}:\<close>

lemma "evn n \<Longrightarrow> ev n" smart_induct
apply(induction n rule: evn.induct)
  apply (simp add: ev0)
 apply simp
apply(simp add: evSS)
done

text \<open>No problem with termination
because the premises are always smaller than the conclusion:\<close>

declare ev.intros[simp,intro]

text \<open>A shorter proof:\<close>

lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
apply(simp_all)
done

text \<open>The power of "arith":\<close>

lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k" smart_induct
apply(induction rule: ev.induct)
 apply(simp)
apply arith
done


subsection "Inductive definition of the reflexive transitive closure"

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z" smart_induct
apply(induction rule: star.induct)
apply(assumption)
apply(rename_tac u x y)
apply(metis step)
done

end
