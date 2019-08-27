(*
 * This file "List_Demo.thy" was originally developed by Tobias Nipkow and Gerwin Klein
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory List_Demo
imports Main
begin

datatype 'a list = Nil | Cons "'a" "'a list"

term "Nil"

declare [[names_short]]

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev(Cons True (Cons False Nil))"

value "rev(Cons a (Cons b Nil))"


lemma app_Nil2[simp]: "app xs Nil = xs"
apply (induction xs)
apply auto
done

lemma app_assoc[simp]: "app (app xs ys) zs = app xs (app ys zs)"
apply (induction xs)
apply auto
done

lemma rev_app[simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
apply (induction xs)
apply auto
done

theorem rev_rev[simp]: "rev (rev xs) = xs"
apply (induction xs)
apply auto
done

(* Hint for demo:
   do the proof top down, discovering the lemmas one by one,
*)

end
