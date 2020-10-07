(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Continuations
imports
  HOLCF
  Maybe
  Nats
  WorkerWrapperNew
begin
(*>*)

section\<open>Tagless interpreter via double-barreled continuations\<close>

text\<open>\label{sec:continuations}\<close>

type_synonym 'a Cont = "('a \<rightarrow> 'a) \<rightarrow> 'a"

definition
  val2cont :: "'a \<rightarrow> 'a Cont" where
  "val2cont \<equiv> (\<Lambda> a c. c\<cdot>a)"

definition
  cont2val :: "'a Cont \<rightarrow> 'a" where
  "cont2val \<equiv> (\<Lambda> f. f\<cdot>ID)"

lemma cont2val_val2cont_id: "cont2val oo val2cont = ID"
  by (rule cfun_eqI, simp add: val2cont_def cont2val_def)

domain Expr =
    Val (lazy val::"Nat")
  | Add (lazy addl::"Expr") (lazy addr::"Expr")
  | Throw
  | Catch (lazy cbody::"Expr") (lazy chandler::"Expr")

fixrec eval :: "Expr \<rightarrow> Nat Maybe"
where
  "eval\<cdot>(Val\<cdot>n) = Just\<cdot>n"
| "eval\<cdot>(Add\<cdot>x\<cdot>y) = mliftM2 (\<Lambda> a b. a + b)\<cdot>(eval\<cdot>x)\<cdot>(eval\<cdot>y)"
| "eval\<cdot>Throw = mfail"
| "eval\<cdot>(Catch\<cdot>x\<cdot>y) = mcatch\<cdot>(eval\<cdot>x)\<cdot>(eval\<cdot>y)"

fixrec eval_body :: "(Expr \<rightarrow> Nat Maybe) \<rightarrow> Expr \<rightarrow> Nat Maybe"
where
  "eval_body\<cdot>r\<cdot>(Val\<cdot>n) = Just\<cdot>n"
| "eval_body\<cdot>r\<cdot>(Add\<cdot>x\<cdot>y) = mliftM2 (\<Lambda> a b. a + b)\<cdot>(r\<cdot>x)\<cdot>(r\<cdot>y)"
| "eval_body\<cdot>r\<cdot>Throw = mfail"
| "eval_body\<cdot>r\<cdot>(Catch\<cdot>x\<cdot>y) = mcatch\<cdot>(r\<cdot>x)\<cdot>(r\<cdot>y)"

lemma eval_body_strictExpr[simp]: "eval_body\<cdot>r\<cdot>\<bottom> = \<bottom>"
  by (subst eval_body.unfold, simp)

lemma eval_eval_body_eq: "eval = fix\<cdot>eval_body"
  by (rule cfun_eqI, subst eval_def, subst eval_body.unfold, simp)

subsection\<open>Worker/wrapper\<close>

definition
  unwrapC :: "(Expr \<rightarrow> Nat Maybe) \<rightarrow> (Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe)" where
  "unwrapC \<equiv> \<Lambda> g e s f. case g\<cdot>e of Nothing \<Rightarrow> f | Just\<cdot>n \<Rightarrow> s\<cdot>n"

lemma unwrapC_strict[simp]: "unwrapC\<cdot>\<bottom> = \<bottom>"
  unfolding unwrapC_def by (rule cfun_eqI)+ simp

definition
  wrapC :: "(Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe) \<rightarrow> (Expr \<rightarrow> Nat Maybe)" where
  "wrapC \<equiv> \<Lambda> g e. g\<cdot>e\<cdot>Just\<cdot>Nothing"

lemma wrapC_unwrapC_id: "wrapC oo unwrapC = ID"
proof(intro cfun_eqI)
  fix g e
  show "(wrapC oo unwrapC)\<cdot>g\<cdot>e = ID\<cdot>g\<cdot>e"
    by (cases "g\<cdot>e", simp_all add: wrapC_def unwrapC_def)
qed

definition
  eval_work :: "Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe" where
  "eval_work \<equiv> fix\<cdot>(unwrapC oo eval_body oo wrapC)"

definition
  eval_wrap :: "Expr \<rightarrow> Nat Maybe" where
  "eval_wrap \<equiv> wrapC\<cdot>eval_work"

fixrec eval_body' :: "(Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe)
                    \<rightarrow> Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe"
where
  "eval_body'\<cdot>r\<cdot>(Val\<cdot>n)\<cdot>s\<cdot>f = s\<cdot>n"
| "eval_body'\<cdot>r\<cdot>(Add\<cdot>x\<cdot>y)\<cdot>s\<cdot>f = (case wrapC\<cdot>r\<cdot>x of
                                     Nothing \<Rightarrow> f
                                   | Just\<cdot>n \<Rightarrow> (case wrapC\<cdot>r\<cdot>y of
                                                    Nothing \<Rightarrow> f
                                                  | Just\<cdot>m \<Rightarrow> s\<cdot>(n + m)))"
| "eval_body'\<cdot>r\<cdot>Throw\<cdot>s\<cdot>f = f"
| "eval_body'\<cdot>r\<cdot>(Catch\<cdot>x\<cdot>y)\<cdot>s\<cdot>f = (case wrapC\<cdot>r\<cdot>x of
                                       Nothing \<Rightarrow> (case wrapC\<cdot>r\<cdot>y of
                                                      Nothing \<Rightarrow> f
                                                    | Just\<cdot>n \<Rightarrow> s\<cdot>n)
                                     | Just\<cdot>n \<Rightarrow> s\<cdot>n)"

lemma eval_body'_strictExpr[simp]: "eval_body'\<cdot>r\<cdot>\<bottom>\<cdot>s\<cdot>f = \<bottom>"
  by (subst eval_body'.unfold, simp)

definition
  eval_work' :: "Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe" where
  "eval_work' \<equiv> fix\<cdot>eval_body'"

text\<open>This proof is unfortunately quite messy, due to the
simplifier's inability to cope with HOLCF's case distinctions.\<close>

lemma eval_body'_eval_body_eq: "eval_body' = unwrapC oo eval_body oo wrapC"
  apply (intro cfun_eqI)
  apply (unfold unwrapC_def wrapC_def)
  apply (case_tac xa)
      apply simp_all
    apply (simp add: wrapC_def)
    apply (case_tac "x\<cdot>Expr1\<cdot>Just\<cdot>Nothing")
     apply simp_all
    apply (case_tac "x\<cdot>Expr2\<cdot>Just\<cdot>Nothing")
     apply simp_all
   apply (simp add: mfail_def)
  apply (simp add: mcatch_def wrapC_def)
  apply (case_tac "x\<cdot>Expr1\<cdot>Just\<cdot>Nothing")
   apply simp_all
  done

fixrec eval_body_final :: "(Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe)
                         \<rightarrow> Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe"
where
  "eval_body_final\<cdot>r\<cdot>(Val\<cdot>n)\<cdot>s\<cdot>f = s\<cdot>n"
| "eval_body_final\<cdot>r\<cdot>(Add\<cdot>x\<cdot>y)\<cdot>s\<cdot>f = r\<cdot>x\<cdot>(\<Lambda> n. r\<cdot>y\<cdot>(\<Lambda> m. s\<cdot>(n + m))\<cdot>f)\<cdot>f"
| "eval_body_final\<cdot>r\<cdot>Throw\<cdot>s\<cdot>f = f"
| "eval_body_final\<cdot>r\<cdot>(Catch\<cdot>x\<cdot>y)\<cdot>s\<cdot>f = r\<cdot>x\<cdot>s\<cdot>(r\<cdot>y\<cdot>s\<cdot>f)"

lemma eval_body_final_strictExpr[simp]: "eval_body_final\<cdot>r\<cdot>\<bottom>\<cdot>s\<cdot>f = \<bottom>"
  by (subst eval_body_final.unfold, simp)

lemma eval_body'_eval_body_final_eq: "eval_body_final oo unwrapC oo wrapC = eval_body'"
  apply (rule cfun_eqI)+
  apply (case_tac xa)
     apply (simp_all add: unwrapC_def)
  done

definition
  eval_work_final :: "Expr \<rightarrow> (Nat \<rightarrow> Nat Maybe) \<rightarrow> Nat Maybe \<rightarrow> Nat Maybe" where
  "eval_work_final \<equiv> fix\<cdot>eval_body_final"

definition
  eval_final :: "Expr \<rightarrow> Nat Maybe" where
  "eval_final \<equiv> (\<Lambda> e. eval_work_final\<cdot>e\<cdot>Just\<cdot>Nothing)"

lemma "eval = eval_final"
proof -
  have "eval = fix\<cdot>eval_body" by (rule eval_eval_body_eq)
  also from wrapC_unwrapC_id unwrapC_strict have "\<dots> = wrapC\<cdot>(fix\<cdot>eval_body_final)"
    apply (rule worker_wrapper_fusion_new)
    using eval_body'_eval_body_final_eq eval_body'_eval_body_eq by simp
  also have "\<dots> = eval_final"
    unfolding eval_final_def eval_work_final_def wrapC_def
    by simp
  finally show ?thesis .
qed

(*<*)
end
(*>*)
