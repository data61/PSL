(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory UnboxedNats
imports
  HOLCF
  Nats
  WorkerWrapperNew
begin
(*>*)

section\<open>Unboxing types.\<close>

text\<open>The original application of the worker/wrapper transformation
was the unboxing of flat types by \citet{SPJ-JL:1991}. We can model
the boxed and unboxed types as (respectively) pointed and unpointed
domains in HOLCF. Concretely @{typ "UNat"} denotes the discrete domain
of naturals, @{typ "UNat\<^sub>\<bottom>"} the lifted (flat and pointed) variant, and
@{typ "Nat"} the standard boxed domain, isomorphic to @{typ
"UNat\<^sub>\<bottom>"}. This latter distinction helps us keep the boxed naturals and
lifted function codomains separated; applications of @{term "unbox"}
should be thought of in the same way as Haskell's @{term "newtype"}
constructors, i.e. operationally equivalent to @{term "ID"}.

The divergence monad is used to handle the unboxing, see below.\<close>

subsection\<open>Factorial example.\<close>

text\<open>Standard definition of factorial.\<close>

fixrec fac :: "Nat \<rightarrow> Nat"
where
  "fac\<cdot>n = If n =\<^sub>B 0 then 1 else n * fac\<cdot>(n - 1)"

declare fac.simps[simp del]

lemma fac_strict[simp]: "fac\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

definition
  fac_body :: "(Nat \<rightarrow> Nat) \<rightarrow> Nat \<rightarrow> Nat" where
  "fac_body \<equiv> \<Lambda> r n. If n =\<^sub>B 0 then 1 else n * r\<cdot>(n - 1)"

lemma fac_body_strict[simp]: "fac_body\<cdot>r\<cdot>\<bottom> = \<bottom>"
  unfolding fac_body_def by simp

lemma fac_fac_body_eq: "fac = fix\<cdot>fac_body"
  unfolding fac_body_def by (rule cfun_eqI, subst fac_def, simp)

text\<open>Wrap / unwrap functions. Note the explicit lifting of the
co-domain. For some reason the published version of
\citet{GillHutton:2009} does not discuss this point: if we're going to
handle recursive functions, we need a bottom.

@{term "unbox"} simply removes the tag, yielding a possibly-divergent
unboxed value, the result of the function.\<close>

definition
  unwrapB :: "(Nat \<rightarrow> Nat) \<rightarrow> UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "unwrapB \<equiv> \<Lambda> f. unbox oo f oo box"

text\<open>Note that the monadic bind operator @{term "(>>=)"} here stands
in for the \textsf{case} construct in the paper.\<close>

definition
  wrapB :: "(UNat \<rightarrow> UNat\<^sub>\<bottom>) \<rightarrow> Nat \<rightarrow> Nat" where
  "wrapB \<equiv> \<Lambda> f x . unbox\<cdot>x >>= f >>= box"

lemma wrapB_unwrapB_body:
  assumes strictF: "f\<cdot>\<bottom> = \<bottom>"
  shows "(wrapB oo unwrapB)\<cdot>f = f" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix x :: Nat
  have "?lhs\<cdot>x = unbox\<cdot>x >>= (\<Lambda> x'. unwrapB\<cdot>f\<cdot>x' >>= box)"
    unfolding wrapB_def by simp
  also have "\<dots> = unbox\<cdot>x >>= (\<Lambda> x'. unbox\<cdot>(f\<cdot>(box\<cdot>x')) >>= box)"
    unfolding unwrapB_def by simp
  also from strictF have "\<dots> = f\<cdot>x" by (cases x, simp_all)
  finally show "?lhs\<cdot>x = ?rhs\<cdot>x" .
qed

text\<open>Apply worker/wrapper.\<close>

definition
  fac_work :: "UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "fac_work \<equiv> fix\<cdot>(unwrapB oo fac_body oo wrapB)"

definition
  fac_wrap :: "Nat \<rightarrow> Nat" where
  "fac_wrap \<equiv> wrapB\<cdot>fac_work"

lemma fac_fac_ww_eq: "fac = fac_wrap" (is "?lhs = ?rhs")
proof -
  have "wrapB oo unwrapB oo fac_body = fac_body"
    using wrapB_unwrapB_body[OF fac_body_strict]
    by - (rule cfun_eqI, simp)
  thus ?thesis
    using worker_wrapper_body[where computation=fac and body=fac_body and wrap=wrapB and unwrap=unwrapB]
    unfolding fac_work_def fac_wrap_def by (simp add: fac_fac_body_eq)
qed

text\<open>This is not entirely faithful to the paper, as they don't
explicitly handle the lifting of the codomain.\<close>

definition
  fac_body' :: "(UNat \<rightarrow> UNat\<^sub>\<bottom>) \<rightarrow> UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "fac_body' \<equiv> \<Lambda> r n.
     unbox\<cdot>(If box\<cdot>n =\<^sub>B 0
              then 1
              else unbox\<cdot>(box\<cdot>n - 1) >>= r >>= (\<Lambda> b. box\<cdot>n * box\<cdot>b))"

lemma fac_body'_fac_body: "fac_body' = unwrapB oo fac_body oo wrapB" (is "?lhs = ?rhs")
proof(rule cfun_eqI)+
  fix r x
  show "?lhs\<cdot>r\<cdot>x = ?rhs\<cdot>r\<cdot>x"
    using bbind_case_distr_strict[where f="\<Lambda> y. box\<cdot>x * y" and g="unbox\<cdot>(box\<cdot>x - 1)"]
          bbind_case_distr_strict[where f="\<Lambda> y. box\<cdot>x * y" and h="box"]
    unfolding fac_body'_def fac_body_def unwrapB_def wrapB_def by simp
qed

text\<open>The @{term "up"} constructors here again mediate the
isomorphism, operationally doing nothing. Note the switch to the
machine-oriented \emph{if} construct: the test @{term "n = 0"} cannot
diverge.\<close>

definition
  fac_body_final :: "(UNat \<rightarrow> UNat\<^sub>\<bottom>) \<rightarrow> UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "fac_body_final \<equiv> \<Lambda> r n.
     if n = 0 then up\<cdot>1 else r\<cdot>(n -\<^sub># 1) >>= (\<Lambda> b. up\<cdot>(n *\<^sub># b))"

lemma fac_body_final_fac_body': "fac_body_final = fac_body'" (is "?lhs = ?rhs")
proof(rule cfun_eqI)+
  fix r x
  show "?lhs\<cdot>r\<cdot>x = ?rhs\<cdot>r\<cdot>x"
    using bbind_case_distr_strict[where f="unbox" and g="r\<cdot>(x -\<^sub># 1)" and h="(\<Lambda> b. box\<cdot>(x *\<^sub># b))"]
    unfolding fac_body_final_def fac_body'_def uMinus_def uMult_def zero_Nat_def one_Nat_def
    by simp
qed

definition
  fac_work_final :: "UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "fac_work_final \<equiv> fix\<cdot>fac_body_final"

definition
  fac_final :: "Nat \<rightarrow> Nat" where
  "fac_final \<equiv> \<Lambda> n. unbox\<cdot>n >>= fac_work_final >>= box"

lemma fac_fac_final: "fac = fac_final" (is "?lhs=?rhs")
proof -
  have "?lhs = fac_wrap" by (rule fac_fac_ww_eq)
  also have "\<dots> = wrapB\<cdot>fac_work" by (simp only: fac_wrap_def)
  also have "\<dots> = wrapB\<cdot>(fix\<cdot>(unwrapB oo fac_body oo wrapB))" by (simp only: fac_work_def)
  also have "\<dots> = wrapB\<cdot>(fix\<cdot>fac_body')" by (simp only: fac_body'_fac_body)
  also have "\<dots> = wrapB\<cdot>fac_work_final" by (simp only: fac_body_final_fac_body' fac_work_final_def)
  also have "\<dots> = fac_final" by (simp add: fac_final_def wrapB_def)
  finally show ?thesis .
qed

(* **************************************** *)

subsection\<open>Introducing an accumulator.\<close>

text\<open>

The final version of factorial uses unboxed naturals but is not
tail-recursive. We can apply worker/wrapper once more to introduce an
accumulator, similar to \S\ref{sec:accum}.

The monadic machinery complicates things slightly here. We use
\emph{Kleisli composition}, denoted @{term "(>=>)"}, in the
homomorphism.

Firstly we introduce an ``accumulator'' monoid and show the
homomorphism.

\<close>

type_synonym UNatAcc = "UNat \<rightarrow> UNat\<^sub>\<bottom>"

definition
  n2a :: "UNat \<rightarrow> UNatAcc" where
  "n2a \<equiv> \<Lambda> m n. up\<cdot>(m *\<^sub># n)"

definition
  a2n :: "UNatAcc \<rightarrow> UNat\<^sub>\<bottom>" where
  "a2n \<equiv> \<Lambda> a. a\<cdot>1"

lemma a2n_strict[simp]: "a2n\<cdot>\<bottom> = \<bottom>"
  unfolding a2n_def by simp

lemma a2n_n2a: "a2n\<cdot>(n2a\<cdot>u) = up\<cdot>u"
  unfolding a2n_def n2a_def by (simp add: uMult_arithmetic)

lemma A_hom_mult: "n2a\<cdot>(x *\<^sub># y) = (n2a\<cdot>x >=> n2a\<cdot>y)"
  unfolding n2a_def bKleisli_def by (simp add: uMult_arithmetic)

definition
  unwrapA :: "(UNat \<rightarrow> UNat\<^sub>\<bottom>) \<rightarrow> UNat \<rightarrow> UNatAcc" where
  "unwrapA \<equiv> \<Lambda> f n. f\<cdot>n >>= n2a"

lemma unwrapA_strict[simp]: "unwrapA\<cdot>\<bottom> = \<bottom>"
  unfolding unwrapA_def by (rule cfun_eqI) simp

definition
  wrapA :: "(UNat \<rightarrow> UNatAcc) \<rightarrow> UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "wrapA \<equiv> \<Lambda> f. a2n oo f"

lemma wrapA_unwrapA_id: "wrapA oo unwrapA = ID"
  unfolding wrapA_def unwrapA_def
  apply (rule cfun_eqI)+
  apply (case_tac "x\<cdot>xa")
  apply (simp_all add: a2n_n2a)
  done

text\<open>Some steps along the way.\<close>

definition
  fac_acc_body1 :: "(UNat \<rightarrow> UNatAcc) \<rightarrow> UNat \<rightarrow> UNatAcc" where
  "fac_acc_body1 \<equiv> \<Lambda> r n.
     if n = 0 then n2a\<cdot>1 else wrapA\<cdot>r\<cdot>(n -\<^sub># 1) >>= (\<Lambda> res. n2a\<cdot>(n *\<^sub># res))"

lemma fac_acc_body1_fac_body_final_eq: "fac_acc_body1 = unwrapA oo fac_body_final oo wrapA"
  unfolding fac_acc_body1_def fac_body_final_def wrapA_def unwrapA_def
  by (rule cfun_eqI)+ simp

text\<open>Use the homomorphism.\<close>

definition
  fac_acc_body2 :: "(UNat \<rightarrow> UNatAcc) \<rightarrow> UNat \<rightarrow> UNatAcc" where
  "fac_acc_body2 \<equiv> \<Lambda> r n.
     if n = 0 then n2a\<cdot>1 else wrapA\<cdot>r\<cdot>(n -\<^sub># 1) >>= (\<Lambda> res. n2a\<cdot>n >=> n2a\<cdot>res)"

lemma fac_acc_body2_body1_eq: "fac_acc_body2 = fac_acc_body1"
  unfolding fac_acc_body1_def fac_acc_body2_def
  by (rule cfun_eqI)+ (simp add: A_hom_mult)

text\<open>Apply worker/wrapper.\<close>

definition
  fac_acc_body3 :: "(UNat \<rightarrow> UNatAcc) \<rightarrow> UNat \<rightarrow> UNatAcc" where
  "fac_acc_body3 \<equiv> \<Lambda> r n.
     if n = 0 then n2a\<cdot>1 else n2a\<cdot>n >=> r\<cdot>(n -\<^sub># 1)"

lemma fac_acc_body3_body2: "fac_acc_body3 oo (unwrapA oo wrapA) = fac_acc_body2" (is "?lhs=?rhs")
proof(rule cfun_eqI)+
  fix r n acc
  show "((fac_acc_body3 oo (unwrapA oo wrapA))\<cdot>r\<cdot>n\<cdot>acc) = fac_acc_body2\<cdot>r\<cdot>n\<cdot>acc"
    unfolding fac_acc_body2_def fac_acc_body3_def unwrapA_def
    using bbind_case_distr_strict[where f="\<Lambda> y. n2a\<cdot>n >=> y" and h="n2a", symmetric]
    by simp
qed

lemma fac_work_final_body3_eq: "fac_work_final = wrapA\<cdot>(fix\<cdot>fac_acc_body3)"
  unfolding fac_work_final_def
  by (rule worker_wrapper_fusion_new[OF wrapA_unwrapA_id unwrapA_strict])
     (simp add: fac_acc_body3_body2 fac_acc_body2_body1_eq fac_acc_body1_fac_body_final_eq)

definition
  fac_acc_body_final :: "(UNat \<rightarrow> UNatAcc) \<rightarrow> UNat \<rightarrow> UNatAcc" where
  "fac_acc_body_final \<equiv> \<Lambda> r n acc.
     if n = 0 then up\<cdot>acc else r\<cdot>(n -\<^sub># 1)\<cdot>(n *\<^sub># acc)"

definition
  fac_acc_work_final :: "UNat \<rightarrow> UNat\<^sub>\<bottom>" where
  "fac_acc_work_final \<equiv> \<Lambda> x. fix\<cdot>fac_acc_body_final\<cdot>x\<cdot>1"

lemma fac_acc_work_final_fac_acc_work3_eq: "fac_acc_body_final = fac_acc_body3" (is "?lhs=?rhs")
  unfolding fac_acc_body3_def fac_acc_body_final_def n2a_def bKleisli_def
  by (rule cfun_eqI)+
     (simp add: uMult_arithmetic)

lemma fac_acc_work_final_fac_work: "fac_acc_work_final = fac_work_final" (is "?lhs=?rhs")
proof -
  have "?rhs = wrapA\<cdot>(fix\<cdot>fac_acc_body3)" by (rule fac_work_final_body3_eq)
  also have "\<dots> = wrapA\<cdot>(fix\<cdot>fac_acc_body_final)"
    using fac_acc_work_final_fac_acc_work3_eq by simp
  also have "\<dots> = ?lhs"
    unfolding fac_acc_work_final_def wrapA_def a2n_def
    by (simp add: cfcomp1)
  finally show ?thesis by simp
qed

(*<*)
end
(*>*)
