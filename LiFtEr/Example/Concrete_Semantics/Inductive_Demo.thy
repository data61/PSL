(*
 * This file "Inductive_Demo.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory Inductive_Demo
imports Main
begin

subsection{*Inductive definition of the even numbers*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"
print_theorems

thm ev0 evSS
thm ev.intros

text{* Using the introduction rules: *}
lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

thm evSS[OF evSS[OF ev0]]

text{* A recursive definition of evenness: *}
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text{*A simple example of rule induction: *}
lemma "ev n \<Longrightarrow> evn n"
apply(induction rule: ev.induct)
 apply(simp)
apply(simp)
done

text{* An induction on the computation of evn: *}
lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
  apply (simp add: ev0)
 apply simp
apply(simp add: evSS)
done

text{* No problem with termination because the premises are always smaller
than the conclusion: *}
declare ev.intros[simp,intro]

text{* A shorter proof: *}
lemma "evn n \<Longrightarrow> ev n"
apply(induction n rule: evn.induct)
apply(simp_all)
done

text{* The power of arith: *}
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
apply(induction rule: ev.induct)
 apply(simp)
apply arith
done

subsection{*Inductive definition of the reflexive transitive closure *}

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply(rename_tac u x y)
apply(metis step)
done

end
