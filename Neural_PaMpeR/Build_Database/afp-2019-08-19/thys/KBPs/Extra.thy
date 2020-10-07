(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Extra
imports
  "HOL-Library.Option_ord"
  "HOL-Library.Product_Lexorder"
begin

(* Extra lemmas that are not noteworthy. *)

lemma relation_mono:
  "\<lbrakk> A \<subseteq> C; B \<subseteq> D \<rbrakk> \<Longrightarrow> A \<times> B \<subseteq> C \<times> D"
  by bestsimp

lemma quotientI2:
  "\<lbrakk> x \<in> A; X = r `` {x} \<rbrakk> \<Longrightarrow> X \<in> A // r"
  by (simp add: quotientI)

(*

Concretely enumerate all the agent action functions. Can't be too
abstract here as we want extensionality.

Introduced in the clock view.

*)

definition
  listToFun :: "('a \<times> 'b list) list \<Rightarrow> ('a \<Rightarrow> 'b) list"
where
  "listToFun xs \<equiv> foldr (\<lambda>(a, acts) M. [ m(a := act) . m \<leftarrow> M, act \<leftarrow> acts ])
                     xs
                     [(\<lambda>_. undefined)]"

lemma listToFun_futz:
  "\<lbrakk> M \<in> set (listToFun xs); x \<in> fst ` set xs \<rbrakk>
     \<Longrightarrow> M x \<in> { y |y ys. (x, ys) \<in> set xs \<and> y \<in> set ys}"
  unfolding listToFun_def
  apply (induct xs arbitrary: M)
   apply (simp_all add: split_def)
  apply (case_tac a)
  apply clarsimp
  apply auto
  done

lemma distinct_map_fst:
  "\<lbrakk> x \<notin> fst ` set xs; distinct (map fst xs) \<rbrakk> \<Longrightarrow> (x, y) \<notin> set xs"
  by (induct xs) auto

lemma listToFun_futz_rev:
  "\<lbrakk> \<And>x. M x \<in> (if x \<in> fst ` set xs then { y |y ys. (x, ys) \<in> set xs \<and> y \<in> set ys} else {undefined}); distinct (map fst xs) \<rbrakk>
      \<Longrightarrow> M \<in> set (listToFun xs)"
proof(induct xs arbitrary: M)
  case Nil thus ?case
    unfolding listToFun_def by simp
next
  case (Cons x xs)
  let ?M' = "M(fst x := undefined)"
  have M': "?M' \<in> set (listToFun xs)"
    apply (rule Cons.hyps)
     prefer 2
     using Cons(3)
     apply simp
    apply (case_tac "xa = fst x")
     using Cons(3)
     apply simp
    apply (case_tac "xa \<in> fst ` set xs")
     apply (cut_tac x=xa in Cons(2))
     apply (cases x)
     apply auto[1]
    apply (cut_tac x=xa in Cons(2))
    apply simp
    done
  then show ?case
    unfolding listToFun_def
    apply (cases x)
    apply simp
    apply (rule bexI[where x="?M'"])
     apply simp_all
    apply (rule_tac x="M a" in image_eqI)
     apply simp
    apply (cut_tac x=a in Cons(2))
    using Cons(3)
    apply clarsimp
    apply (erule disjE)
     apply simp
    apply (auto dest: distinct_map_fst)
    done
qed

definition
  listToFuns :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'b) list"
where
  "listToFuns f \<equiv> listToFun \<circ> map (\<lambda>x. (x, f x))"

lemma map_id_clunky:
  "set xs = UNIV \<Longrightarrow> x \<in> fst ` set (map (\<lambda>x. (x, f x)) xs)"
  apply (simp only: set_map[symmetric] map_map)
  apply simp
  done

(*

The main result is that we can freely move between representations.

*)

lemma listToFuns_ext:
  assumes xs: "set xs = UNIV"
  assumes d: "distinct xs"
  shows "g \<in> set (listToFuns f xs) \<longleftrightarrow> (\<forall>x. g x \<in> set (f x))"
  unfolding listToFuns_def
  apply simp
  apply rule
   apply clarsimp
   apply (cut_tac x=x in listToFun_futz[where M=g, OF _ map_id_clunky[OF xs]])
    apply simp
   apply clarsimp
  apply (rule listToFun_futz_rev)
   using map_id_clunky[OF xs]
   apply auto[1]
   apply (rule_tac x="f xa" in exI)
    apply simp
   apply simp
  using d
  apply (simp add: distinct_map)
  apply (auto intro: inj_onI)
  done

lemma listToFun_splice:
  assumes xs: "set xs = UNIV"
  assumes d: "distinct xs"
  assumes g: "g \<in> set (listToFuns f xs)"
  assumes h: "h \<in> set (listToFuns f xs)"
  shows "g(x := h x) \<in> set (listToFuns f xs)"
  using g h by (auto iff: listToFuns_ext[OF xs d])
(*<*)

end
(*>*)
