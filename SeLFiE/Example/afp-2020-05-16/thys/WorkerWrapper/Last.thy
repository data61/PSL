(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Last
imports
  HOLCF
  LList
  WorkerWrapper
begin

(*>*)
section\<open>Optimise ``last''.\<close>

text\<open>Andy Gill's solution, mechanised. No fusion, works fine using their rule.\<close>

subsection\<open>The @{term "last"} function.\<close>

fixrec llast :: "'a llist \<rightarrow> 'a"
where
  "llast\<cdot>(x :@ yys) = (case yys of lnil \<Rightarrow> x | y :@ ys \<Rightarrow> llast\<cdot>yys)"

lemma llast_strict[simp]: "llast\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec llast_body :: "('a llist \<rightarrow> 'a) \<rightarrow> 'a llist \<rightarrow> 'a"
where
  "llast_body\<cdot>f\<cdot>(x :@ yys) = (case yys of lnil \<Rightarrow> x | y :@ ys \<Rightarrow> f\<cdot>yys)"

lemma llast_llast_body: "llast = fix\<cdot>llast_body"
  by (rule cfun_eqI, subst llast_def, subst llast_body.unfold, simp)

definition wrap :: "('a \<rightarrow> 'a llist \<rightarrow> 'a) \<rightarrow> ('a llist \<rightarrow> 'a)" where
  "wrap \<equiv> \<Lambda> f (x :@ xs). f\<cdot>x\<cdot>xs"

definition unwrap :: "('a llist \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a llist \<rightarrow> 'a)" where
  "unwrap \<equiv> \<Lambda> f x xs. f\<cdot>(x :@ xs)"

lemma unwrap_strict[simp]: "unwrap\<cdot>\<bottom> = \<bottom>"
  unfolding unwrap_def by ((rule cfun_eqI)+, simp)

lemma wrap_unwrap_ID: "wrap oo unwrap oo llast_body = llast_body"
  unfolding llast_body_def wrap_def unwrap_def
  apply (rule cfun_eqI)+
  apply (case_tac xa)
  apply (simp_all add: fix_const)
  done

definition llast_worker :: "('a \<rightarrow> 'a llist \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a llist \<rightarrow> 'a" where
  "llast_worker \<equiv> \<Lambda> r x yys. case yys of lnil \<Rightarrow> x | y :@ ys \<Rightarrow> r\<cdot>y\<cdot>ys"

definition llast' :: "'a llist \<rightarrow> 'a" where
  "llast' \<equiv> wrap\<cdot>(fix\<cdot>llast_worker)"

lemma llast_worker_llast_body: "llast_worker = unwrap oo llast_body oo wrap"
  unfolding llast_worker_def llast_body_def wrap_def unwrap_def
  apply (rule cfun_eqI)+
  apply (case_tac xb)
  apply (simp_all add: fix_const)
  done

lemma llast'_llast: "llast' = llast" (is "?lhs = ?rhs")
proof -
  have "?rhs = fix\<cdot>llast_body" by (simp only: llast_llast_body)
  also have "\<dots> = wrap\<cdot>(fix\<cdot>(unwrap oo llast_body oo wrap))"
    by (simp only: worker_wrapper_body[OF wrap_unwrap_ID])
  also have "\<dots> = wrap\<cdot>(fix\<cdot>(llast_worker))"
    by (simp only: llast_worker_llast_body)
  also have "... = ?lhs" unfolding llast'_def by simp
  finally show ?thesis by simp
qed

end
