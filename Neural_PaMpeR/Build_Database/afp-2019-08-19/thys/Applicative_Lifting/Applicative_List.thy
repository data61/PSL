(* Author: Joshua Schneider, ETH Zurich *)

subsection \<open>Lists\<close>

theory Applicative_List imports
  Applicative
  "HOL-Library.Adhoc_Overloading"
begin

definition "ap_list fs xs = List.bind fs (\<lambda>f. List.bind xs (\<lambda>x. [f x]))"

adhoc_overloading Applicative.ap ap_list

lemma Nil_ap[simp]: "ap_list [] xs = []"
unfolding ap_list_def by simp

lemma ap_Nil[simp]: "ap_list fs [] = []"
unfolding ap_list_def by (induction fs) simp_all

lemma ap_list_transfer[transfer_rule]:
  "rel_fun (list_all2 (rel_fun A B)) (rel_fun (list_all2 A) (list_all2 B)) ap_list ap_list"
unfolding ap_list_def[abs_def] List.bind_def
by transfer_prover

context includes applicative_syntax
begin

lemma cons_ap_list: "(f # fs) \<diamondop> xs = map f xs @ fs \<diamondop> xs"
unfolding ap_list_def by (induction xs) simp_all

lemma append_ap_distrib: "(fs @ gs) \<diamondop> xs = fs \<diamondop> xs @ gs \<diamondop> xs"
unfolding ap_list_def by (induction fs) simp_all

applicative list
for
  pure: "\<lambda>x. [x]"
  ap: ap_list
  rel: list_all2
  set: set
proof -
  fix x :: "'a list"
  show "[\<lambda>x. x] \<diamondop> x = x" unfolding ap_list_def by (induction x) simp_all
next
  fix g :: "('b \<Rightarrow> 'c) list" and f :: "('a \<Rightarrow> 'b) list" and x
  let ?B = "\<lambda>g f x. g (f x)"
  show "[?B] \<diamondop> g \<diamondop> f \<diamondop> x = g \<diamondop> (f \<diamondop> x)"
  proof (induction g)
    case Nil show ?case by simp
  next
    case (Cons g gs)
    have g_comp: "[?B g] \<diamondop> f \<diamondop> x = [g] \<diamondop> (f \<diamondop> x)"
    proof (induction f)
      case Nil show ?case by simp
    next
      case (Cons f fs)
      have "[?B g] \<diamondop> (f # fs) \<diamondop> x = [g] \<diamondop> ([f] \<diamondop> x) @ [?B g] \<diamondop> fs \<diamondop> x"
        by (simp add: cons_ap_list)
      also have "... = [g] \<diamondop> ([f] \<diamondop> x) @ [g] \<diamondop> (fs \<diamondop> x)" using Cons.IH ..
      also have "... = [g] \<diamondop> ((f # fs) \<diamondop> x)" by (simp add: cons_ap_list)
      finally show ?case .
    qed
    have "[?B] \<diamondop> (g # gs) \<diamondop> f \<diamondop> x = [?B g] \<diamondop> f \<diamondop> x @ [?B] \<diamondop> gs \<diamondop> f \<diamondop> x"
      by (simp add: cons_ap_list append_ap_distrib)
    also have "... = [g] \<diamondop> (f \<diamondop> x) @ gs \<diamondop> (f \<diamondop> x)" using g_comp Cons.IH by simp
    also have "... = (g # gs) \<diamondop> (f \<diamondop> x)" by (simp add: cons_ap_list)
    finally show ?case .
  qed
next
  fix f :: "('a \<Rightarrow> 'b) list" and x
  show "f \<diamondop> [x] = [\<lambda>f. f x] \<diamondop> f" unfolding ap_list_def by simp
next
  fix R :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  show "rel_fun R (list_all2 R) (\<lambda>x. [x]) (\<lambda>x. [x])" by transfer_prover
next
  fix R and f :: "('a \<Rightarrow> 'b) list" and g :: "('a \<Rightarrow> 'c) list" and x
  assume [transfer_rule]: "list_all2 (rel_fun (eq_on (set x)) R) f g"
  have [transfer_rule]: "list_all2 (eq_on (set x)) x x" by (simp add: list_all2_same)
  show "list_all2 R (f \<diamondop> x) (g \<diamondop> x)" by transfer_prover
qed (simp add: cons_ap_list)

lemma map_ap_conv[applicative_unfold]: "map f x = [f] \<diamondop> x"
unfolding ap_list_def List.bind_def
by simp

end

end
