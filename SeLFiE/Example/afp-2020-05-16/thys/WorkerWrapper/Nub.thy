(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Nub
imports
  HOLCF
  LList
  Maybe
  Nats
  WorkerWrapperNew
begin
(*>*)

section\<open>Transforming $O(n^2)$ \emph{nub} into an $O(n\lg n)$ one\<close>

text\<open>Andy Gill's solution, mechanised.\<close>

subsection\<open>The @{term "nub"} function.\<close>

fixrec nub :: "Nat llist \<rightarrow> Nat llist"
where
  "nub\<cdot>lnil = lnil"
| "nub\<cdot>(x :@ xs) = x :@ nub\<cdot>(lfilter\<cdot>(neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>xs)"

lemma nub_strict[simp]: "nub\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec nub_body :: "(Nat llist \<rightarrow> Nat llist) \<rightarrow> Nat llist \<rightarrow> Nat llist"
where
  "nub_body\<cdot>f\<cdot>lnil = lnil"
| "nub_body\<cdot>f\<cdot>(x :@ xs) = x :@ f\<cdot>(lfilter\<cdot>(neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>xs)"

lemma nub_nub_body_eq: "nub = fix\<cdot>nub_body"
  by (rule cfun_eqI, subst nub_def, subst nub_body.unfold, simp)

(* **************************************** *)

subsection\<open>Optimised data type.\<close>

text \<open>Implement sets using lazy lists for now. Lifting up HOL's @{typ "'a
set"} type causes continuity grief.\<close>

type_synonym NatSet = "Nat llist"

definition
  SetEmpty :: "NatSet" where
  "SetEmpty \<equiv> lnil"

definition
  SetInsert :: "Nat \<rightarrow> NatSet \<rightarrow> NatSet" where
  "SetInsert \<equiv> lcons"

definition
  SetMem :: "Nat \<rightarrow> NatSet \<rightarrow> tr" where
  "SetMem \<equiv> lmember\<cdot>(bpred (=))"

lemma SetMem_strict[simp]: "SetMem\<cdot>x\<cdot>\<bottom> = \<bottom>" by (simp add: SetMem_def)
lemma SetMem_SetEmpty[simp]: "SetMem\<cdot>x\<cdot>SetEmpty = FF"
  by (simp add: SetMem_def SetEmpty_def)
lemma SetMem_SetInsert: "SetMem\<cdot>v\<cdot>(SetInsert\<cdot>x\<cdot>s) = (SetMem\<cdot>v\<cdot>s orelse x =\<^sub>B v)"
  by (simp add: SetMem_def SetInsert_def)

text \<open>AndyG's new type.\<close>

domain R = R (lazy resultR :: "Nat llist") (lazy exceptR :: "NatSet")

definition
  nextR :: "R \<rightarrow> (Nat * R) Maybe" where
  "nextR = (\<Lambda> r. case ldropWhile\<cdot>(\<Lambda> x. SetMem\<cdot>x\<cdot>(exceptR\<cdot>r))\<cdot>(resultR\<cdot>r) of
                     lnil \<Rightarrow> Nothing
                   | x :@ xs \<Rightarrow> Just\<cdot>(x, R\<cdot>xs\<cdot>(exceptR\<cdot>r)))"

lemma nextR_strict1[simp]: "nextR\<cdot>\<bottom> = \<bottom>" by (simp add: nextR_def)
lemma nextR_strict2[simp]: "nextR\<cdot>(R\<cdot>\<bottom>\<cdot>S) = \<bottom>" by (simp add: nextR_def)

lemma nextR_lnil[simp]: "nextR\<cdot>(R\<cdot>lnil\<cdot>S) = Nothing" by (simp add: nextR_def)

definition
  filterR :: "Nat \<rightarrow> R \<rightarrow> R" where
  "filterR \<equiv> (\<Lambda> v r. R\<cdot>(resultR\<cdot>r)\<cdot>(SetInsert\<cdot>v\<cdot>(exceptR\<cdot>r)))"

definition
  c2a :: "Nat llist \<rightarrow> R" where
  "c2a \<equiv> \<Lambda> xs. R\<cdot>xs\<cdot>SetEmpty"

definition
  a2c :: "R \<rightarrow> Nat llist" where
  "a2c \<equiv> \<Lambda> r. lfilter\<cdot>(\<Lambda> v. neg\<cdot>(SetMem\<cdot>v\<cdot>(exceptR\<cdot>r)))\<cdot>(resultR\<cdot>r)"

lemma a2c_strict[simp]: "a2c\<cdot>\<bottom> = \<bottom>" unfolding a2c_def by simp

lemma a2c_c2a_id: "a2c oo c2a = ID"
  by (rule cfun_eqI, simp add: a2c_def c2a_def lfilter_const_true)

definition
  wrap :: "(R \<rightarrow> Nat llist) \<rightarrow> Nat llist \<rightarrow> Nat llist" where
  "wrap \<equiv> \<Lambda> f xs. f\<cdot>(c2a\<cdot>xs)"

definition
  unwrap :: "(Nat llist \<rightarrow> Nat llist) \<rightarrow> R \<rightarrow> Nat llist" where
  "unwrap \<equiv> \<Lambda> f r. f\<cdot>(a2c\<cdot>r)"

lemma unwrap_strict[simp]: "unwrap\<cdot>\<bottom> = \<bottom>"
  unfolding unwrap_def by (rule cfun_eqI, simp)

lemma wrap_unwrap_id: "wrap oo unwrap = ID"
  using cfun_fun_cong[OF a2c_c2a_id]
  by - ((rule cfun_eqI)+, simp add: wrap_def unwrap_def)

text \<open>Equivalences needed for later.\<close>

lemma TR_deMorgan: "neg\<cdot>(x orelse y) = (neg\<cdot>x andalso neg\<cdot>y)"
  by (rule trE[where p=x], simp_all)

lemma case_maybe_case:
  "(case (case L of lnil \<Rightarrow> Nothing | x :@ xs \<Rightarrow> Just\<cdot>(h\<cdot>x\<cdot>xs)) of
     Nothing \<Rightarrow> f | Just\<cdot>(a, b) \<Rightarrow> g\<cdot>a\<cdot>b)
   =
   (case L of lnil \<Rightarrow> f | x :@ xs \<Rightarrow> g\<cdot>(fst (h\<cdot>x\<cdot>xs))\<cdot>(snd (h\<cdot>x\<cdot>xs)))"
  apply (cases L, simp_all)
  apply (case_tac "h\<cdot>a\<cdot>llist")
  apply simp
  done

lemma case_a2c_case_caseR:
    "(case a2c\<cdot>w of lnil \<Rightarrow> f | x :@ xs \<Rightarrow> g\<cdot>x\<cdot>xs)
   = (case nextR\<cdot>w of Nothing \<Rightarrow> f | Just\<cdot>(x, r) \<Rightarrow> g\<cdot>x\<cdot>(a2c\<cdot>r))" (is "?lhs = ?rhs")
proof -
  have "?rhs = (case (case ldropWhile\<cdot>(\<Lambda> x. SetMem\<cdot>x\<cdot>(exceptR\<cdot>w))\<cdot>(resultR\<cdot>w) of
                     lnil \<Rightarrow> Nothing
                   | x :@ xs \<Rightarrow> Just\<cdot>(x, R\<cdot>xs\<cdot>(exceptR\<cdot>w))) of Nothing \<Rightarrow> f | Just\<cdot>(x, r) \<Rightarrow> g\<cdot>x\<cdot>(a2c\<cdot>r))"
    by (simp add: nextR_def)
  also have "\<dots> = (case ldropWhile\<cdot>(\<Lambda> x. SetMem\<cdot>x\<cdot>(exceptR\<cdot>w))\<cdot>(resultR\<cdot>w) of
                     lnil \<Rightarrow> f | x :@ xs \<Rightarrow> g\<cdot>x\<cdot>(a2c\<cdot>(R\<cdot>xs\<cdot>(exceptR\<cdot>w))))"
    using case_maybe_case[where L="ldropWhile\<cdot>(\<Lambda> x. SetMem\<cdot>x\<cdot>(exceptR\<cdot>w))\<cdot>(resultR\<cdot>w)"
                            and f=f and g="\<Lambda> x r. g\<cdot>x\<cdot>(a2c\<cdot>r)" and h="\<Lambda> x xs. (x, R\<cdot>xs\<cdot>(exceptR\<cdot>w))"]
    by simp
  also have "\<dots> = ?lhs"
    apply (simp add: a2c_def)
    apply (cases "resultR\<cdot>w")
      apply simp_all
    apply (rule_tac p="SetMem\<cdot>a\<cdot>(exceptR\<cdot>w)" in trE)
      apply simp_all
    apply (induct_tac llist)
       apply simp_all
    apply (rule_tac p="SetMem\<cdot>aa\<cdot>(exceptR\<cdot>w)" in trE)
      apply simp_all
    done
  finally show "?lhs = ?rhs" by simp
qed

lemma filter_filterR: "lfilter\<cdot>(neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>(a2c\<cdot>r) = a2c\<cdot>(filterR\<cdot>x\<cdot>r)"
  using filter_filter[where p="Tr.neg oo (\<Lambda> y. x =\<^sub>B y)" and q="\<Lambda> v. Tr.neg\<cdot>(SetMem\<cdot>v\<cdot>(exceptR\<cdot>r))"]
  unfolding a2c_def filterR_def
  by (cases r, simp_all add: SetMem_SetInsert TR_deMorgan)

text\<open>Apply worker/wrapper. Unlike Gill/Hutton, we manipulate the body of
the worker into the right form then apply the lemma.\<close>

definition
  nub_body' :: "(R \<rightarrow> Nat llist) \<rightarrow> R \<rightarrow> Nat llist" where
  "nub_body' \<equiv> \<Lambda> f r. case a2c\<cdot>r of lnil \<Rightarrow> lnil
                                   | x :@ xs \<Rightarrow> x :@ f\<cdot>(c2a\<cdot>(lfilter\<cdot>(neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>xs))"

lemma nub_body_nub_body'_eq: "unwrap oo nub_body oo wrap = nub_body'"
  unfolding nub_body_def nub_body'_def unwrap_def wrap_def a2c_def c2a_def
  by ((rule cfun_eqI)+
     , case_tac "lfilter\<cdot>(\<Lambda> v. Tr.neg\<cdot>(SetMem\<cdot>v\<cdot>(exceptR\<cdot>xa)))\<cdot>(resultR\<cdot>xa)"
     , simp_all add: fix_const)

definition
  nub_body'' :: "(R \<rightarrow> Nat llist) \<rightarrow> R \<rightarrow> Nat llist" where
  "nub_body'' \<equiv> \<Lambda> f r. case nextR\<cdot>r of Nothing \<Rightarrow> lnil
                                      | Just\<cdot>(x, xs) \<Rightarrow> x :@ f\<cdot>(c2a\<cdot>(lfilter\<cdot>(neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>(a2c\<cdot>xs)))"

lemma nub_body'_nub_body''_eq: "nub_body' = nub_body''"
proof(rule cfun_eqI)+
  fix f r show "nub_body'\<cdot>f\<cdot>r = nub_body''\<cdot>f\<cdot>r"
    unfolding nub_body'_def nub_body''_def
    using case_a2c_case_caseR[where f="lnil" and g="\<Lambda> x xs. x :@ f\<cdot>(c2a\<cdot>(lfilter\<cdot>(Tr.neg oo (\<Lambda> y. x =\<^sub>B y))\<cdot>xs))" and w="r"]
    by simp
qed

definition
  nub_body''' :: "(R \<rightarrow> Nat llist) \<rightarrow> R \<rightarrow> Nat llist" where
  "nub_body''' \<equiv> (\<Lambda> f r. case nextR\<cdot>r of Nothing \<Rightarrow> lnil
                                      | Just\<cdot>(x, xs) \<Rightarrow> x :@ f\<cdot>(filterR\<cdot>x\<cdot>xs))"

lemma nub_body''_nub_body'''_eq: "nub_body'' = nub_body''' oo (unwrap oo wrap)"
  unfolding nub_body''_def nub_body'''_def wrap_def unwrap_def
  by ((rule cfun_eqI)+, simp add: filter_filterR)

text\<open>Finally glue it all together.\<close>

lemma nub_wrap_nub_body''': "nub = wrap\<cdot>(fix\<cdot>nub_body''')"
  using worker_wrapper_fusion_new[OF wrap_unwrap_id unwrap_strict, where body=nub_body]
        nub_nub_body_eq
        nub_body_nub_body'_eq
        nub_body'_nub_body''_eq
        nub_body''_nub_body'''_eq
  by simp

end
