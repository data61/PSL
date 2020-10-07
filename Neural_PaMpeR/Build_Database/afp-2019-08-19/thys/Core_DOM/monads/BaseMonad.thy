(***********************************************************************************
 * Copyright (c) 2016-2018 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>The Monad Infrastructure\<close>
text\<open>In this theory, we introduce the basic infrastructure for our monadic class encoding.\<close>
theory BaseMonad
  imports
    "../classes/BaseClass"
    "../preliminaries/Heap_Error_Monad"
begin
subsection\<open>Datatypes\<close>

datatype exception = NotFoundError | SegmentationFault | HierarchyRequestError | AssertException 
  | NonTerminationException | InvokeError | TypeError | DebugException nat

lemma finite_set_in [simp]: "x \<in> fset FS \<longleftrightarrow> x |\<in>| FS"
  by (meson notin_fset)

consts put_M :: 'a
consts get_M :: 'a
consts delete_M :: 'a

lemma sorted_list_of_set_eq [dest]: 
  "sorted_list_of_set (fset x) = sorted_list_of_set (fset y) \<Longrightarrow> x = y"
  by (metis finite_fset fset_inject sorted_list_of_set(1))


locale l_ptr_kinds_M =
  fixes ptr_kinds :: "'heap \<Rightarrow> 'ptr::linorder fset"
begin
definition a_ptr_kinds_M :: "('heap, exception, 'ptr list) prog"
  where
    "a_ptr_kinds_M = do {
      h \<leftarrow> get_heap;
      return (sorted_list_of_set (fset (ptr_kinds h)))
    }"

lemma ptr_kinds_M_ok [simp]: "h \<turnstile> ok a_ptr_kinds_M"
  by(simp add: a_ptr_kinds_M_def)

lemma ptr_kinds_M_pure [simp]: "pure a_ptr_kinds_M h"
  by (auto simp add: a_ptr_kinds_M_def intro: bind_pure_I)

lemma ptr_kinds_ptr_kinds_M [simp]: "ptr \<in> set |h \<turnstile> a_ptr_kinds_M|\<^sub>r \<longleftrightarrow> ptr |\<in>| ptr_kinds h"
  by(simp add: a_ptr_kinds_M_def)

lemma ptr_kinds_M_ptr_kinds [simp]: 
  "h \<turnstile> a_ptr_kinds_M \<rightarrow>\<^sub>r xa \<longleftrightarrow> xa = sorted_list_of_set (fset (ptr_kinds h))"
  by(auto simp add: a_ptr_kinds_M_def)
lemma ptr_kinds_M_ptr_kinds_returns_result [simp]: 
  "h \<turnstile> a_ptr_kinds_M \<bind> f \<rightarrow>\<^sub>r x \<longleftrightarrow> h \<turnstile> f (sorted_list_of_set (fset (ptr_kinds h))) \<rightarrow>\<^sub>r x"
  by(auto simp add: a_ptr_kinds_M_def)
lemma ptr_kinds_M_ptr_kinds_returns_heap [simp]: 
  "h \<turnstile> a_ptr_kinds_M \<bind> f \<rightarrow>\<^sub>h h' \<longleftrightarrow> h \<turnstile> f (sorted_list_of_set (fset (ptr_kinds h))) \<rightarrow>\<^sub>h h'"
  by(auto simp add: a_ptr_kinds_M_def)
end

locale l_get_M = 
  fixes get :: "'ptr \<Rightarrow> 'heap \<Rightarrow> 'obj option"
  fixes type_wf :: "'heap \<Rightarrow> bool"
  fixes ptr_kinds :: "'heap \<Rightarrow> 'ptr fset"
  assumes "type_wf h \<Longrightarrow> ptr |\<in>| ptr_kinds h \<Longrightarrow> get ptr h \<noteq> None"
  assumes "get ptr h \<noteq> None \<Longrightarrow> ptr |\<in>| ptr_kinds h"
begin

definition a_get_M :: "'ptr \<Rightarrow> ('obj \<Rightarrow> 'result) \<Rightarrow>  ('heap, exception, 'result) prog"
  where
    "a_get_M ptr getter = (do {
      h \<leftarrow> get_heap;
      (case get ptr h of
        Some res \<Rightarrow> return (getter res)
      | None \<Rightarrow> error SegmentationFault)
    })"

lemma get_M_pure [simp]: "pure (a_get_M ptr getter) h"
  by(auto simp add: a_get_M_def bind_pure_I split: option.splits)

lemma get_M_ok:
  "type_wf h \<Longrightarrow> ptr |\<in>| ptr_kinds h \<Longrightarrow> h \<turnstile> ok (a_get_M ptr getter)"
  apply(simp add: a_get_M_def)
  by (metis l_get_M_axioms l_get_M_def option.case_eq_if return_ok)
lemma get_M_ptr_in_heap:
  "h \<turnstile> ok (a_get_M ptr getter) \<Longrightarrow> ptr |\<in>| ptr_kinds h"
  apply(simp add: a_get_M_def)
  by (metis error_returns_result is_OK_returns_result_E l_get_M_axioms l_get_M_def option.simps(4))

end

locale l_put_M = l_get_M get for get :: "'ptr \<Rightarrow> 'heap \<Rightarrow> 'obj option" +
  fixes put :: "'ptr \<Rightarrow> 'obj \<Rightarrow> 'heap \<Rightarrow> 'heap"
begin
definition a_put_M :: "'ptr \<Rightarrow> (('v \<Rightarrow> 'v) \<Rightarrow> 'obj \<Rightarrow> 'obj) \<Rightarrow> 'v \<Rightarrow> ('heap, exception, unit) prog"
  where
    "a_put_M ptr setter v = (do {
      obj \<leftarrow> a_get_M ptr id;
      h \<leftarrow> get_heap;
      return_heap (put ptr (setter (\<lambda>_. v) obj) h)
    })"

lemma put_M_ok:
  "type_wf h \<Longrightarrow> ptr |\<in>| ptr_kinds h \<Longrightarrow> h \<turnstile> ok (a_put_M ptr setter v)"
  by(auto simp add: a_put_M_def intro!: bind_is_OK_I2 dest: get_M_ok elim!: bind_is_OK_E)

lemma put_M_ptr_in_heap:
  "h \<turnstile> ok (a_put_M ptr setter v) \<Longrightarrow> ptr |\<in>| ptr_kinds h"
  by(auto simp add: a_put_M_def intro!: bind_is_OK_I2 elim: get_M_ptr_in_heap 
      dest: is_OK_returns_result_I elim!: bind_is_OK_E)

end

subsection \<open>Setup for Defining Partial Functions\<close>

lemma execute_admissible: 
  "ccpo.admissible (fun_lub (flat_lub (Inl (e::'e)))) (fun_ord (flat_ord (Inl e)))
     ((\<lambda>a. \<forall>(h::'heap) h2 (r::'result). h \<turnstile> a = Inr (r, h2) \<longrightarrow> P h h2 r) \<circ> Prog)"
proof (unfold comp_def, rule ccpo.admissibleI, clarify)
  fix A :: "('heap \<Rightarrow> 'e + 'result \<times> 'heap) set"
  let ?lub = "Prog (fun_lub (flat_lub (Inl e)) A)"
  fix h h2 r
  assume 1: "Complete_Partial_Order.chain (fun_ord (flat_ord (Inl e))) A"
    and 2: "\<forall>xa\<in>A. \<forall>h h2 r. h \<turnstile> Prog xa = Inr (r, h2)  \<longrightarrow> P h h2 r"
    and 4: "h \<turnstile> Prog (fun_lub (flat_lub (Inl e)) A) = Inr (r, h2)"
  have h1:"\<And>a. Complete_Partial_Order.chain (flat_ord (Inl e)) {y. \<exists>f\<in>A. y = f a}"
    by (rule chain_fun[OF 1])
  show "P h h2 r"
    using chain_fun[OF 1] flat_lub_in_chain[OF chain_fun[OF 1]] 2 4 unfolding execute_def fun_lub_def
    by force
qed

lemma execute_admissible2: 
  "ccpo.admissible (fun_lub (flat_lub (Inl (e::'e)))) (fun_ord (flat_ord (Inl e)))
     ((\<lambda>a. \<forall>(h::'heap) h' h2 h2' (r::'result) r'. 
                    h \<turnstile> a = Inr (r, h2) \<longrightarrow> h' \<turnstile> a = Inr (r', h2') \<longrightarrow> P h h' h2 h2' r r') \<circ> Prog)"
proof (unfold comp_def, rule ccpo.admissibleI, clarify)
  fix A :: "('heap \<Rightarrow> 'e + 'result \<times> 'heap) set"
  let ?lub = "Prog (fun_lub (flat_lub (Inl e)) A)"
  fix h h' h2 h2' r r'
  assume 1: "Complete_Partial_Order.chain (fun_ord (flat_ord (Inl e))) A"
    and 2 [rule_format]: "\<forall>xa\<in>A. \<forall>h h' h2 h2' r r'. h \<turnstile> Prog xa = Inr (r, h2) 
                          \<longrightarrow> h' \<turnstile> Prog xa = Inr (r', h2') \<longrightarrow> P h h' h2 h2' r r'"
    and 4: "h \<turnstile> Prog (fun_lub (flat_lub (Inl e)) A) = Inr (r, h2)"
    and 5: "h' \<turnstile> Prog (fun_lub (flat_lub (Inl e)) A) = Inr (r', h2')"
  have h1:"\<And>a. Complete_Partial_Order.chain (flat_ord (Inl e)) {y. \<exists>f\<in>A. y = f a}"
    by (rule chain_fun[OF 1])
  have "h \<turnstile> ?lub \<in> {y. \<exists>f\<in>A. y = f h}"
    using flat_lub_in_chain[OF h1] 4
    unfolding execute_def fun_lub_def
    by auto
  moreover have "h' \<turnstile> ?lub \<in> {y. \<exists>f\<in>A. y = f h'}"
    using flat_lub_in_chain[OF h1] 5
    unfolding execute_def fun_lub_def
    by auto
  ultimately obtain f where
    "f \<in> A" and
    "h \<turnstile> Prog f = Inr (r, h2)" and
    "h' \<turnstile> Prog f = Inr (r', h2')"
    using 1 4 5 
    apply(auto simp add:  chain_def fun_ord_def flat_ord_def execute_def)[1]
    by (metis Inl_Inr_False)
  then show "P h h' h2 h2' r r'"
    by(fact 2)
qed

definition dom_prog_ord :: 
  "('heap, exception, 'result) prog \<Rightarrow> ('heap, exception, 'result) prog \<Rightarrow> bool" where
  "dom_prog_ord = img_ord (\<lambda>a b. execute b a) (fun_ord (flat_ord (Inl NonTerminationException)))"

definition dom_prog_lub :: 
  "('heap, exception, 'result) prog set \<Rightarrow> ('heap, exception, 'result) prog" where
  "dom_prog_lub = img_lub (\<lambda>a b. execute b a) Prog (fun_lub (flat_lub (Inl NonTerminationException)))"

lemma dom_prog_lub_empty: "dom_prog_lub {} = error NonTerminationException"
  by(simp add: dom_prog_lub_def img_lub_def fun_lub_def flat_lub_def error_def)

lemma dom_prog_interpretation: "partial_function_definitions dom_prog_ord dom_prog_lub"
proof -
  have "partial_function_definitions (fun_ord (flat_ord (Inl NonTerminationException))) 
                                     (fun_lub (flat_lub (Inl NonTerminationException)))"
    by (rule partial_function_lift) (rule flat_interpretation)
  then show ?thesis
    apply (simp add: dom_prog_lub_def dom_prog_ord_def flat_interpretation execute_def)
    using partial_function_image prog.expand prog.sel by blast
qed

interpretation dom_prog: partial_function_definitions dom_prog_ord dom_prog_lub
  rewrites "dom_prog_lub {} \<equiv> error NonTerminationException"
  by (fact dom_prog_interpretation)(simp add: dom_prog_lub_empty)

lemma admissible_dom_prog: 
  "dom_prog.admissible (\<lambda>f. \<forall>x h h' r. h \<turnstile> f x \<rightarrow>\<^sub>r r \<longrightarrow> h \<turnstile> f x \<rightarrow>\<^sub>h h' \<longrightarrow> P x h h' r)"
proof (rule admissible_fun[OF dom_prog_interpretation])
  fix x
  show "ccpo.admissible dom_prog_lub dom_prog_ord (\<lambda>a. \<forall>h h' r. h \<turnstile> a \<rightarrow>\<^sub>r r \<longrightarrow> h \<turnstile> a \<rightarrow>\<^sub>h h' 
         \<longrightarrow> P x h h' r)"
    unfolding dom_prog_ord_def dom_prog_lub_def
  proof (intro admissible_image partial_function_lift flat_interpretation)
    show "ccpo.admissible (fun_lub (flat_lub (Inl NonTerminationException))) 
                          (fun_ord (flat_ord (Inl NonTerminationException)))
     ((\<lambda>a. \<forall>h h' r. h \<turnstile> a \<rightarrow>\<^sub>r r \<longrightarrow> h \<turnstile> a \<rightarrow>\<^sub>h h' \<longrightarrow> P x h h' r) \<circ> Prog)"
      by(auto simp add: execute_admissible returns_result_def returns_heap_def split: sum.splits)
  next
    show "\<And>x y. (\<lambda>b. b \<turnstile> x) = (\<lambda>b. b \<turnstile> y) \<Longrightarrow> x = y"
      by(simp add: execute_def prog.expand)
  next
    show "\<And>x. (\<lambda>b. b \<turnstile> Prog x) = x"
      by(simp add: execute_def)
  qed
qed

lemma admissible_dom_prog2:
  "dom_prog.admissible (\<lambda>f. \<forall>x h h2 h' h2' r r2. h \<turnstile> f x \<rightarrow>\<^sub>r r \<longrightarrow> h \<turnstile> f x \<rightarrow>\<^sub>h h' 
            \<longrightarrow> h2 \<turnstile> f x \<rightarrow>\<^sub>r r2 \<longrightarrow> h2 \<turnstile> f x \<rightarrow>\<^sub>h h2' \<longrightarrow> P x h h2 h' h2' r r2)"
proof (rule admissible_fun[OF dom_prog_interpretation])
  fix x
  show "ccpo.admissible dom_prog_lub dom_prog_ord (\<lambda>a. \<forall>h h2 h' h2' r r2. h \<turnstile> a \<rightarrow>\<^sub>r r 
                   \<longrightarrow> h \<turnstile> a \<rightarrow>\<^sub>h h' \<longrightarrow> h2 \<turnstile> a \<rightarrow>\<^sub>r r2 \<longrightarrow> h2 \<turnstile> a \<rightarrow>\<^sub>h h2' \<longrightarrow> P x h h2 h' h2' r r2)"
    unfolding dom_prog_ord_def dom_prog_lub_def
  proof (intro admissible_image partial_function_lift flat_interpretation)
    show "ccpo.admissible (fun_lub (flat_lub (Inl NonTerminationException))) 
                          (fun_ord (flat_ord (Inl NonTerminationException)))
     ((\<lambda>a. \<forall>h h2 h' h2' r r2. h \<turnstile> a \<rightarrow>\<^sub>r r \<longrightarrow> h \<turnstile> a \<rightarrow>\<^sub>h h' \<longrightarrow> h2 \<turnstile> a \<rightarrow>\<^sub>r r2 \<longrightarrow> h2 \<turnstile> a \<rightarrow>\<^sub>h h2' 
                 \<longrightarrow> P x h h2 h' h2' r r2) \<circ> Prog)"
      by(auto simp add: returns_result_def returns_heap_def intro!: ccpo.admissibleI 
          dest!: ccpo.admissibleD[OF execute_admissible2[where P="P x"]] 
          split: sum.splits)
  next
    show "\<And>x y. (\<lambda>b. b \<turnstile> x) = (\<lambda>b. b \<turnstile> y) \<Longrightarrow> x = y"
      by(simp add: execute_def prog.expand)
  next
    show "\<And>x. (\<lambda>b. b \<turnstile> Prog x) = x"
      by(simp add: execute_def)
  qed
qed

lemma fixp_induct_dom_prog:
  fixes F :: "'c \<Rightarrow> 'c" and
    U :: "'c \<Rightarrow> 'b \<Rightarrow> ('heap, exception, 'result) prog" and
    C :: "('b \<Rightarrow> ('heap, exception, 'result) prog) \<Rightarrow> 'c" and
    P :: "'b \<Rightarrow> 'heap \<Rightarrow> 'heap \<Rightarrow> 'result \<Rightarrow> bool"
  assumes mono: "\<And>x. monotone (fun_ord dom_prog_ord) dom_prog_ord (\<lambda>f. U (F (C f)) x)"
  assumes eq: "f \<equiv> C (ccpo.fixp (fun_lub dom_prog_lub) (fun_ord dom_prog_ord) (\<lambda>f. U (F (C f))))"
  assumes inverse2: "\<And>f. U (C f) = f"
  assumes step: "\<And>f x h h' r. (\<And>x h h' r. h \<turnstile> (U f x) \<rightarrow>\<^sub>r r \<Longrightarrow> h \<turnstile> (U f x) \<rightarrow>\<^sub>h h' \<Longrightarrow> P x h h' r) 
    \<Longrightarrow> h \<turnstile> (U (F f) x) \<rightarrow>\<^sub>r r \<Longrightarrow> h \<turnstile> (U (F f) x) \<rightarrow>\<^sub>h h' \<Longrightarrow> P x h h' r"
  assumes defined: "h \<turnstile> (U f x) \<rightarrow>\<^sub>r r" and "h \<turnstile> (U f x) \<rightarrow>\<^sub>h h'"
  shows "P x h h' r"
  using step defined dom_prog.fixp_induct_uc[of U F C, OF mono eq inverse2 admissible_dom_prog, of P]
  by (metis assms(6) error_returns_heap)

declaration \<open>Partial_Function.init "dom_prog" @{term dom_prog.fixp_fun}
  @{term dom_prog.mono_body} @{thm dom_prog.fixp_rule_uc} @{thm dom_prog.fixp_induct_uc}
  (SOME @{thm fixp_induct_dom_prog})\<close>


abbreviation "mono_dom_prog \<equiv> monotone (fun_ord dom_prog_ord) dom_prog_ord"

lemma dom_prog_ordI:
  assumes "\<And>h. h \<turnstile> f \<rightarrow>\<^sub>e NonTerminationException \<or> h \<turnstile> f = h \<turnstile> g"
  shows "dom_prog_ord f g"
proof(auto simp add: dom_prog_ord_def img_ord_def fun_ord_def flat_ord_def)[1]
  fix x
  assume "x \<turnstile> f \<noteq> x \<turnstile> g"
  then show "x \<turnstile> f = Inl NonTerminationException"
    using assms[where h=x]
    by(auto simp add: returns_error_def split: sum.splits)
qed

lemma dom_prog_ordE:
  assumes "dom_prog_ord x y"
  obtains "h \<turnstile> x \<rightarrow>\<^sub>e NonTerminationException" | " h \<turnstile> x = h \<turnstile> y"
  using assms unfolding dom_prog_ord_def img_ord_def fun_ord_def flat_ord_def
  using returns_error_def by force


lemma bind_mono [partial_function_mono]:
  fixes B :: "('a \<Rightarrow> ('heap, exception, 'result) prog) \<Rightarrow> ('heap, exception, 'result2) prog"
  assumes mf: "mono_dom_prog B" and mg: "\<And>y. mono_dom_prog (\<lambda>f. C y f)"
  shows "mono_dom_prog (\<lambda>f. B f \<bind> (\<lambda>y. C y f))"
proof (rule monotoneI)
  fix f g :: "'a \<Rightarrow> ('heap, exception, 'result) prog"
  assume fg: "dom_prog.le_fun f g"
  from mf
  have 1: "dom_prog_ord (B f) (B g)" by (rule monotoneD) (rule fg)
  from mg
  have 2: "\<And>y'. dom_prog_ord (C y' f) (C y' g)" by (rule monotoneD) (rule fg)

  have "dom_prog_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y. C y f))"
    (is "dom_prog_ord ?L ?R")
  proof (rule dom_prog_ordI)
    fix h
    from 1 show "h \<turnstile> ?L \<rightarrow>\<^sub>e NonTerminationException \<or> h \<turnstile> ?L = h \<turnstile> ?R"
      apply(rule dom_prog_ordE) 
       apply(auto)[1]
      using bind_cong by fastforce
  qed
  also
  have h1: "dom_prog_ord (B g \<bind> (\<lambda>y'. C y' f)) (B g \<bind> (\<lambda>y'. C y' g))"
    (is "dom_prog_ord ?L ?R")
  proof (rule dom_prog_ordI)
    (* { *)
    fix h
    show "h \<turnstile> ?L \<rightarrow>\<^sub>e NonTerminationException \<or> h \<turnstile> ?L = h \<turnstile> ?R"
    proof (cases "h \<turnstile> ok (B g)")
      case True
      then obtain x h' where x: "h \<turnstile> B g \<rightarrow>\<^sub>r x" and h': "h \<turnstile> B g \<rightarrow>\<^sub>h h'"
        by blast
      then have "dom_prog_ord (C x f) (C x g)"
        using 2 by simp
      then show ?thesis
        using x h'
        apply(auto intro!: bind_returns_error_I3 dest: returns_result_eq dest!: dom_prog_ordE)[1]
        apply(auto simp add: execute_bind_simp)[1]
        using "2" dom_prog_ordE by metis
    next
      case False
      then obtain e where e: "h \<turnstile> B g \<rightarrow>\<^sub>e e"
        by(simp add: is_OK_def returns_error_def split: sum.splits)
      have "h \<turnstile> B g \<bind> (\<lambda>y'. C y' f) \<rightarrow>\<^sub>e e"
        using e by(auto)
      moreover have "h \<turnstile> B g \<bind> (\<lambda>y'. C y' g) \<rightarrow>\<^sub>e e"
        using e by auto
      ultimately show ?thesis
        using bind_returns_error_eq by metis
    qed
  qed
  finally (dom_prog.leq_trans)
  show "dom_prog_ord (B f \<bind> (\<lambda>y. C y f)) (B g \<bind> (\<lambda>y'. C y' g))" .
qed

lemma mono_dom_prog1 [partial_function_mono]:
  fixes g ::  "('a \<Rightarrow> ('heap, exception, 'result) prog) \<Rightarrow> 'b \<Rightarrow> ('heap, exception, 'result) prog"
  assumes "\<And>x. (mono_dom_prog (\<lambda>f. g f x))"
  shows "mono_dom_prog (\<lambda>f. map_M (g f) xs)"
  using assms
  apply (induct xs) 
  by(auto simp add: call_mono dom_prog.const_mono intro!: bind_mono)

lemma mono_dom_prog2 [partial_function_mono]:
  fixes g ::  "('a \<Rightarrow> ('heap, exception, 'result) prog) \<Rightarrow> 'b \<Rightarrow> ('heap, exception, 'result) prog"
  assumes "\<And>x. (mono_dom_prog (\<lambda>f. g f x))"
  shows "mono_dom_prog (\<lambda>f. forall_M (g f) xs)"
  using assms
  apply (induct xs) 
  by(auto simp add: call_mono dom_prog.const_mono intro!: bind_mono)

lemma sorted_list_set_cong [simp]: 
  "sorted_list_of_set (fset FS) = sorted_list_of_set (fset FS') \<longleftrightarrow> FS = FS'"
  by auto

end
