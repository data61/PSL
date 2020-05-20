(*<*)
(*
 * The worker/wrapper transformation, following Gill and Hutton.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Accumulator
imports
  HOLCF
  LList
  WorkerWrapperNew
begin
(*>*)

section\<open>Naive reverse becomes accumulator-reverse.\<close>

text\<open>\label{sec:accum}\<close>

subsection\<open>Hughes lists, naive reverse, worker-wrapper optimisation.\<close>

text\<open>The ``Hughes'' list type.\<close>

type_synonym 'a H = "'a llist \<rightarrow> 'a llist"

definition
  list2H :: "'a llist \<rightarrow> 'a H" where
  "list2H \<equiv> lappend"

lemma acc_c2a_strict[simp]: "list2H\<cdot>\<bottom> = \<bottom>"
  by (rule cfun_eqI, simp add: list2H_def)

definition
  H2list :: "'a H \<rightarrow> 'a llist" where
  "H2list \<equiv> \<Lambda> f . f\<cdot>lnil"

text\<open>The paper only claims the homomorphism holds for finite lists,
but in fact it holds for all lazy lists in HOLCF. They are trying to
dodge an explicit appeal to the equation @{thm "inst_cfun_pcpo"},
which does not hold in Haskell.\<close>

lemma H_llist_hom_append: "list2H\<cdot>(xs :++ ys) = list2H\<cdot>xs oo list2H\<cdot>ys" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix zs
  have "?lhs\<cdot>zs = (xs :++ ys) :++ zs" by (simp add: list2H_def)
  also have "\<dots> = xs :++ (ys :++ zs)" by (rule lappend_assoc)
  also have "\<dots> = list2H\<cdot>xs\<cdot>(ys :++ zs)" by (simp add: list2H_def)
  also have "\<dots> = list2H\<cdot>xs\<cdot>(list2H\<cdot>ys\<cdot>zs)" by (simp add: list2H_def)
  also have "\<dots> = (list2H\<cdot>xs oo list2H\<cdot>ys)\<cdot>zs" by simp
  finally show "?lhs\<cdot>zs = (list2H\<cdot>xs oo list2H\<cdot>ys)\<cdot>zs" .
qed

lemma H_llist_hom_id: "list2H\<cdot>lnil = ID" by (simp add: list2H_def)

lemma H2list_list2H_inv: "H2list oo list2H = ID"
  by (rule cfun_eqI, simp add: H2list_def list2H_def)

text\<open>\citet[\S4.2]{GillHutton:2009} define the naive reverse
function as follows.\<close>

fixrec lrev :: "'a llist \<rightarrow> 'a llist"
where
  "lrev\<cdot>lnil = lnil"
| "lrev\<cdot>(x :@ xs) = lrev\<cdot>xs :++ (x :@ lnil)"

text\<open>Note ``body'' is the generator of @{term "lrev_def"}.\<close>

lemma lrev_strict[simp]: "lrev\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec lrev_body :: "('a llist \<rightarrow> 'a llist) \<rightarrow> 'a llist \<rightarrow> 'a llist"
where
  "lrev_body\<cdot>r\<cdot>lnil = lnil"
| "lrev_body\<cdot>r\<cdot>(x :@ xs) = r\<cdot>xs :++ (x :@ lnil)"

lemma lrev_body_strict[simp]: "lrev_body\<cdot>r\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

text\<open>This is trivial but syntactically a bit touchy. Would be nicer
to define @{term "lrev_body"} as the generator of the fixpoint
definition of @{term "lrev"} directly.\<close>

lemma lrev_lrev_body_eq: "lrev = fix\<cdot>lrev_body"
  by (rule cfun_eqI, subst lrev_def, subst lrev_body.unfold, simp)

text\<open>Wrap / unwrap functions.\<close>

definition
  unwrapH :: "('a llist \<rightarrow> 'a llist) \<rightarrow> 'a llist \<rightarrow> 'a H" where
  "unwrapH \<equiv> \<Lambda> f xs . list2H\<cdot>(f\<cdot>xs)"

lemma unwrapH_strict[simp]: "unwrapH\<cdot>\<bottom> = \<bottom>"
  unfolding unwrapH_def by (rule cfun_eqI, simp)

definition
  wrapH :: "('a llist \<rightarrow> 'a H) \<rightarrow> 'a llist \<rightarrow> 'a llist" where
  "wrapH \<equiv> \<Lambda> f xs . H2list\<cdot>(f\<cdot>xs)"

lemma wrapH_unwrapH_id: "wrapH oo unwrapH = ID" (is "?lhs = ?rhs")
proof(rule cfun_eqI)+
  fix f xs
  have "?lhs\<cdot>f\<cdot>xs = H2list\<cdot>(list2H\<cdot>(f\<cdot>xs))" by (simp add: wrapH_def unwrapH_def)
  also have "\<dots> = (H2list oo list2H)\<cdot>(f\<cdot>xs)" by simp
  also have "\<dots> = ID\<cdot>(f\<cdot>xs)" by (simp only: H2list_list2H_inv)
  also have "\<dots> = ?rhs\<cdot>f\<cdot>xs" by simp
  finally show "?lhs\<cdot>f\<cdot>xs = ?rhs\<cdot>f\<cdot>xs" .
qed

subsection\<open>Gill/Hutton-style worker/wrapper.\<close>

definition
  lrev_work :: "'a llist \<rightarrow> 'a H" where
  "lrev_work \<equiv> fix\<cdot>(unwrapH oo lrev_body oo wrapH)"

definition
  lrev_wrap :: "'a llist \<rightarrow> 'a llist" where
  "lrev_wrap \<equiv> wrapH\<cdot>lrev_work"

lemma lrev_lrev_ww_eq: "lrev = lrev_wrap"
  using worker_wrapper_id[OF wrapH_unwrapH_id lrev_lrev_body_eq]
  by (simp add: lrev_wrap_def lrev_work_def)

subsection\<open>Optimise worker/wrapper.\<close>

text\<open>Intermediate worker.\<close>

fixrec lrev_body1 :: "('a llist \<rightarrow> 'a H) \<rightarrow> 'a llist \<rightarrow> 'a H"
where
  "lrev_body1\<cdot>r\<cdot>lnil = list2H\<cdot>lnil"
| "lrev_body1\<cdot>r\<cdot>(x :@ xs) = list2H\<cdot>(wrapH\<cdot>r\<cdot>xs :++ (x :@ lnil))"

definition
  lrev_work1 :: "'a llist \<rightarrow> 'a H" where
  "lrev_work1 \<equiv> fix\<cdot>lrev_body1"

lemma lrev_body_lrev_body1_eq: "lrev_body1 = unwrapH oo lrev_body oo wrapH"
  apply (rule cfun_eqI)+
  apply (subst lrev_body.unfold)
  apply (subst lrev_body1.unfold)
  apply (case_tac xa)
  apply (simp_all add: list2H_def wrapH_def unwrapH_def)
  done

lemma lrev_work1_lrev_work_eq: "lrev_work1 = lrev_work"
  by (unfold lrev_work_def lrev_work1_def,
      rule cfun_arg_cong[OF lrev_body_lrev_body1_eq])

text\<open>Now use the homomorphism.\<close>

fixrec lrev_body2 :: "('a llist \<rightarrow> 'a H) \<rightarrow> 'a llist \<rightarrow> 'a H"
where
  "lrev_body2\<cdot>r\<cdot>lnil = ID"
| "lrev_body2\<cdot>r\<cdot>(x :@ xs) = list2H\<cdot>(wrapH\<cdot>r\<cdot>xs) oo list2H\<cdot>(x :@ lnil)"

lemma lrev_body2_strict[simp]: "lrev_body2\<cdot>r\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

definition
  lrev_work2 :: "'a llist \<rightarrow> 'a H" where
  "lrev_work2 \<equiv> fix\<cdot>lrev_body2"

lemma lrev_work2_strict[simp]: "lrev_work2\<cdot>\<bottom> = \<bottom>"
  unfolding lrev_work2_def
  by (subst fix_eq) simp

lemma lrev_body2_lrev_body1_eq: "lrev_body2 = lrev_body1"
  by ((rule cfun_eqI)+
     , (subst lrev_body1.unfold, subst lrev_body2.unfold)
     , (simp add: H_llist_hom_append[symmetric] H_llist_hom_id))

lemma lrev_work2_lrev_work1_eq: "lrev_work2 = lrev_work1"
  by (unfold lrev_work2_def lrev_work1_def
     , rule cfun_arg_cong[OF lrev_body2_lrev_body1_eq])

text \<open>Simplify.\<close>

fixrec lrev_body3 :: "('a llist \<rightarrow> 'a H) \<rightarrow> 'a llist \<rightarrow> 'a H"
where
  "lrev_body3\<cdot>r\<cdot>lnil = ID"
| "lrev_body3\<cdot>r\<cdot>(x :@ xs) = r\<cdot>xs oo list2H\<cdot>(x :@ lnil)"

lemma lrev_body3_strict[simp]: "lrev_body3\<cdot>r\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

definition
  lrev_work3 :: "'a llist \<rightarrow> 'a H" where
  "lrev_work3 \<equiv> fix\<cdot>lrev_body3"

lemma lrev_wwfusion: "list2H\<cdot>((wrapH\<cdot>lrev_work2)\<cdot>xs) = lrev_work2\<cdot>xs"
proof -
  {
    have "list2H oo wrapH\<cdot>lrev_work2 = unwrapH\<cdot>(wrapH\<cdot>lrev_work2)"
      by (rule cfun_eqI, simp add: unwrapH_def)
    also have "\<dots> = (unwrapH oo wrapH)\<cdot>lrev_work2" by simp
    also have "\<dots> = lrev_work2"
      apply -
      apply (rule worker_wrapper_fusion[OF wrapH_unwrapH_id, where body="lrev_body"])
      apply (auto iff: lrev_body2_lrev_body1_eq lrev_body_lrev_body1_eq lrev_work2_def lrev_work1_def)
      done
    finally have "list2H oo wrapH\<cdot>lrev_work2 = lrev_work2" .
  }
  thus ?thesis using cfun_eq_iff[where f="list2H oo wrapH\<cdot>lrev_work2" and g="lrev_work2"] by auto
qed

text\<open>If we use this result directly, we only get a partially-correct
program transformation, see \citet{Tullsen:PhDThesis} for details.\<close>

lemma "lrev_work3 \<sqsubseteq> lrev_work2"
  unfolding lrev_work3_def
proof(rule fix_least)
  {
    fix xs have "lrev_body3\<cdot>lrev_work2\<cdot>xs = lrev_work2\<cdot>xs"
    proof(cases xs)
      case bottom thus ?thesis by simp
    next
      case lnil thus ?thesis
        unfolding lrev_work2_def
        by (subst fix_eq[where F="lrev_body2"], simp)
    next
      case (lcons y ys)
      hence "lrev_body3\<cdot>lrev_work2\<cdot>xs = lrev_work2\<cdot>ys oo list2H\<cdot>(y :@ lnil)" by simp
      also have "\<dots> = list2H\<cdot>((wrapH\<cdot>lrev_work2)\<cdot>ys) oo list2H\<cdot>(y :@ lnil)"
        using lrev_wwfusion[where xs=ys] by simp
      also from lcons have "\<dots> = lrev_body2\<cdot>lrev_work2\<cdot>xs" by simp
      also have "\<dots> = lrev_work2\<cdot>xs"
        unfolding lrev_work2_def by (simp only: fix_eq[symmetric])
      finally show ?thesis by simp
    qed
  }
  thus "lrev_body3\<cdot>lrev_work2 = lrev_work2" by (rule cfun_eqI)
qed

text\<open>We can't show the reverse inclusion in the same way as the
fusion law doesn't hold for the optimised definition. (Intuitively we
haven't established that it is equal to the original @{term "lrev"}
definition.) We could show termination of the optimised definition
though, as it operates on finite lists. Alternatively we can use
induction (over the list argument) to show total equivalence.

The following lemma shows that the fusion Gill/Hutton want to do is
completely sound in this context, by appealing to the lazy list
induction principle.\<close>

lemma lrev_work3_lrev_work2_eq: "lrev_work3 = lrev_work2" (is "?lhs = ?rhs")
proof(rule cfun_eqI)
  fix x
  show "?lhs\<cdot>x = ?rhs\<cdot>x"
  proof(induct x)
    show "lrev_work3\<cdot>\<bottom> = lrev_work2\<cdot>\<bottom>"
      apply (unfold lrev_work3_def lrev_work2_def)
      apply (subst fix_eq[where F="lrev_body2"])
      apply (subst fix_eq[where F="lrev_body3"])
      by (simp add: lrev_body3.unfold lrev_body2.unfold)
  next
    show "lrev_work3\<cdot>lnil = lrev_work2\<cdot>lnil"
      apply (unfold lrev_work3_def lrev_work2_def)
      apply (subst fix_eq[where F="lrev_body2"])
      apply (subst fix_eq[where F="lrev_body3"])
      by (simp add: lrev_body3.unfold lrev_body2.unfold)
  next
    fix a l assume "lrev_work3\<cdot>l = lrev_work2\<cdot>l"
    thus "lrev_work3\<cdot>(a :@ l) = lrev_work2\<cdot>(a :@ l)"
      apply (unfold lrev_work3_def lrev_work2_def)
      apply (subst fix_eq[where F="lrev_body2"])
      apply (subst fix_eq[where F="lrev_body3"])
      apply (fold lrev_work3_def lrev_work2_def)
      apply (simp add: lrev_body3.unfold lrev_body2.unfold lrev_wwfusion)
      done
  qed simp_all
qed

text\<open>Use the combined worker/wrapper-fusion rule. Note we get a weaker lemma.\<close>

lemma lrev3_2_syntactic: "lrev_body3 oo (unwrapH oo wrapH) = lrev_body2"
  apply (subst lrev_body2.unfold, subst lrev_body3.unfold)
  apply (rule cfun_eqI)+
  apply (case_tac xa)
    apply (simp_all add: unwrapH_def)
  done

lemma lrev_work3_lrev_work2_eq': "lrev = wrapH\<cdot>lrev_work3"
proof -
  from lrev_lrev_body_eq
  have "lrev = fix\<cdot>lrev_body" .
  also from wrapH_unwrapH_id unwrapH_strict
  have "\<dots> = wrapH\<cdot>(fix\<cdot>lrev_body3)"
    by (rule worker_wrapper_fusion_new
       , simp add: lrev3_2_syntactic lrev_body2_lrev_body1_eq lrev_body_lrev_body1_eq)
  finally show ?thesis unfolding lrev_work3_def by simp
qed

text\<open>Final syntactic tidy-up.\<close>

fixrec lrev_body_final :: "('a llist \<rightarrow> 'a H) \<rightarrow> 'a llist \<rightarrow> 'a H"
where
  "lrev_body_final\<cdot>r\<cdot>lnil\<cdot>ys = ys"
| "lrev_body_final\<cdot>r\<cdot>(x :@ xs)\<cdot>ys = r\<cdot>xs\<cdot>(x :@ ys)"

definition
  lrev_work_final :: "'a llist \<rightarrow> 'a H" where
  "lrev_work_final \<equiv> fix\<cdot>lrev_body_final"

definition
  lrev_final :: "'a llist \<rightarrow> 'a llist" where
  "lrev_final \<equiv> \<Lambda> xs. lrev_work_final\<cdot>xs\<cdot>lnil"

lemma lrev_body_final_lrev_body3_eq': "lrev_body_final\<cdot>r\<cdot>xs = lrev_body3\<cdot>r\<cdot>xs"
  apply (subst lrev_body_final.unfold)
  apply (subst lrev_body3.unfold)
  apply (cases xs)
  apply (simp_all add: list2H_def ID_def cfun_eqI)
  done

lemma lrev_body_final_lrev_body3_eq: "lrev_body_final = lrev_body3"
  by (simp only: lrev_body_final_lrev_body3_eq' cfun_eqI)

lemma lrev_final_lrev_eq: "lrev = lrev_final" (is "?lhs = ?rhs")
proof -
  have "?lhs = lrev_wrap" by (rule lrev_lrev_ww_eq)
  also have "\<dots> = wrapH\<cdot>lrev_work" by (simp only: lrev_wrap_def)
  also have "\<dots> = wrapH\<cdot>lrev_work1" by (simp only: lrev_work1_lrev_work_eq)
  also have "\<dots> = wrapH\<cdot>lrev_work2" by (simp only: lrev_work2_lrev_work1_eq)
  also have "\<dots> = wrapH\<cdot>lrev_work3" by (simp only: lrev_work3_lrev_work2_eq)
  also have "\<dots> = wrapH\<cdot>lrev_work_final" by (simp only: lrev_work3_def lrev_work_final_def lrev_body_final_lrev_body3_eq)
  also have "\<dots> = lrev_final" by (simp add: lrev_final_def cfun_eqI H2list_def wrapH_def)
  finally show ?thesis .
qed

(*<*)
end
(*>*)
