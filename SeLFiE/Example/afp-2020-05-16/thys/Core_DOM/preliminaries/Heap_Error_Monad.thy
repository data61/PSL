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

section\<open>The Heap Error Monad\<close>
text \<open>In this theory, we define a heap and error monad for modeling exceptions. 
This allows us to define composite methods similar to stateful programming in Haskell, 
but also to stay close to the official DOM specification.\<close>
theory 
  Heap_Error_Monad
  imports
    Hiding_Type_Variables
    "HOL-Library.Monad_Syntax"
begin

subsection \<open>The Program Data Type\<close>

datatype ('heap, 'e, 'result) prog = Prog (the_prog: "'heap \<Rightarrow> 'e + 'result \<times> 'heap")
register_default_tvars "('heap, 'e, 'result) prog" (print, parse)

subsection \<open>Basic Functions\<close>

definition 
  bind :: "(_, 'result) prog \<Rightarrow> ('result \<Rightarrow> (_, 'result2) prog) \<Rightarrow> (_, 'result2) prog"
  where
    "bind f g = Prog (\<lambda>h. (case (the_prog f) h of Inr (x, h') \<Rightarrow> (the_prog (g x)) h' 
                                                | Inl exception \<Rightarrow> Inl exception))"

adhoc_overloading Monad_Syntax.bind bind

definition 
  execute :: "'heap \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> ('e + 'result \<times> 'heap)" 
  ("((_)/ \<turnstile> (_))" [51, 52] 55)
  where
    "execute h p = (the_prog p) h"

definition 
  returns_result :: "'heap \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> 'result \<Rightarrow> bool" 
  ("((_)/ \<turnstile> (_)/ \<rightarrow>\<^sub>r (_))" [60, 35, 61] 65)
  where
    "returns_result h p r \<longleftrightarrow> (case h \<turnstile> p of Inr (r', _) \<Rightarrow> r = r' | Inl _ \<Rightarrow> False)"

fun select_result ("|(_)|\<^sub>r")
  where
    "select_result (Inr (r, _)) = r"
  | "select_result (Inl _) = undefined"

lemma returns_result_eq [elim]: "h \<turnstile> f \<rightarrow>\<^sub>r y \<Longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>r y' \<Longrightarrow> y = y'"
  by(auto simp add: returns_result_def split: sum.splits)

definition 
  returns_heap :: "'heap \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> 'heap \<Rightarrow> bool" 
  ("((_)/ \<turnstile> (_)/ \<rightarrow>\<^sub>h (_))" [60, 35, 61] 65)
  where
    "returns_heap h p h' \<longleftrightarrow> (case h \<turnstile> p of Inr (_ , h'') \<Rightarrow> h' = h'' | Inl _ \<Rightarrow> False)"

lemma returns_heap_eq [elim]: "h \<turnstile> f \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>h h'' \<Longrightarrow> h' = h''"
  by(auto simp add: returns_heap_def split: sum.splits)

definition 
  returns_error :: "'heap \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> 'e \<Rightarrow> bool" 
  ("((_)/ \<turnstile> (_)/ \<rightarrow>\<^sub>e (_))" [60, 35, 61] 65)
  where
    "returns_error h p e = (case h \<turnstile> p of Inr _ \<Rightarrow> False | Inl e' \<Rightarrow> e = e')"

definition is_OK :: "'heap \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> bool" ("((_)/ \<turnstile> ok (_))" [75, 75])
  where
    "is_OK h p = (case h \<turnstile> p of Inr _ \<Rightarrow> True | Inl _ \<Rightarrow> False)"

lemma is_OK_returns_result_I [intro]: "h \<turnstile> f \<rightarrow>\<^sub>r y \<Longrightarrow> h \<turnstile> ok f"
  by(auto simp add: is_OK_def returns_result_def split: sum.splits)

lemma is_OK_returns_result_E [elim]:
  assumes "h \<turnstile> ok f"
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x"
  using assms by(auto simp add: is_OK_def returns_result_def split: sum.splits)

lemma is_OK_returns_heap_I [intro]: "h \<turnstile> f \<rightarrow>\<^sub>h h' \<Longrightarrow> h \<turnstile> ok f"
  by(auto simp add: is_OK_def returns_heap_def split: sum.splits)

lemma is_OK_returns_heap_E [elim]:
  assumes "h \<turnstile> ok f"
  obtains h' where "h \<turnstile> f \<rightarrow>\<^sub>h h'"
  using assms by(auto simp add: is_OK_def returns_heap_def split: sum.splits)

lemma select_result_I:
  assumes "h \<turnstile> ok f"
    and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> P x"
  shows "P |h \<turnstile> f|\<^sub>r"
  using assms
  by(auto simp add: is_OK_def returns_result_def split: sum.splits)

lemma select_result_I2 [simp]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x"
  shows "|h \<turnstile> f|\<^sub>r = x"
  using assms
  by(auto simp add: is_OK_def returns_result_def split: sum.splits)

lemma returns_result_select_result [simp]:
  assumes "h \<turnstile> ok f"
  shows "h \<turnstile> f \<rightarrow>\<^sub>r |h \<turnstile> f|\<^sub>r"
  using assms
  by (simp add: select_result_I)

lemma select_result_E:
  assumes "P |h \<turnstile> f|\<^sub>r" and "h \<turnstile> ok f" 
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "P x"
  using assms
  by(auto simp add: is_OK_def returns_result_def split: sum.splits)

lemma select_result_eq: "(\<And>x .h \<turnstile> f \<rightarrow>\<^sub>r x = h' \<turnstile> f \<rightarrow>\<^sub>r x) \<Longrightarrow> |h \<turnstile> f|\<^sub>r = |h' \<turnstile> f|\<^sub>r"
  by (metis (no_types, lifting) is_OK_def old.sum.simps(6) select_result.elims 
      select_result_I select_result_I2)

definition error :: "'e \<Rightarrow> ('heap, 'e, 'result) prog"
  where
    "error exception = Prog (\<lambda>h. Inl exception)"

lemma error_bind [iff]: "(error e \<bind> g) = error e"
  unfolding error_def bind_def by auto

lemma error_returns_result [simp]: "\<not> (h \<turnstile> error e \<rightarrow>\<^sub>r y)"
  unfolding returns_result_def error_def execute_def by auto

lemma error_returns_heap [simp]: "\<not> (h \<turnstile> error e \<rightarrow>\<^sub>h h')"
  unfolding returns_heap_def error_def execute_def by auto

lemma error_returns_error [simp]: "h \<turnstile> error e \<rightarrow>\<^sub>e e"
  unfolding returns_error_def error_def execute_def by auto

definition return :: "'result \<Rightarrow> ('heap, 'e, 'result) prog"
  where
    "return result = Prog (\<lambda>h. Inr (result, h))"

lemma return_ok [simp]: "h \<turnstile> ok (return x)"
  by(simp add: return_def is_OK_def execute_def)

lemma return_bind [iff]: "(return x \<bind> g) = g x"
  unfolding return_def bind_def by auto

lemma return_id [simp]: "f \<bind> return = f"
  by (induct f) (auto simp add: return_def bind_def split: sum.splits prod.splits)

lemma return_returns_result [iff]: "(h \<turnstile> return x \<rightarrow>\<^sub>r y) = (x = y)"
  unfolding returns_result_def return_def execute_def by auto

lemma return_returns_heap [iff]: "(h \<turnstile> return x \<rightarrow>\<^sub>h h') = (h = h')"
  unfolding returns_heap_def return_def execute_def by auto

lemma return_returns_error [iff]: "\<not> h \<turnstile> return x \<rightarrow>\<^sub>e e"
  unfolding returns_error_def execute_def return_def by auto

definition noop :: "('heap, 'e, unit) prog"
  where
    "noop = return ()"

lemma noop_returns_heap [simp]: "h \<turnstile> noop \<rightarrow>\<^sub>h h' \<longleftrightarrow> h = h'"
  by(simp add: noop_def)

definition get_heap :: "('heap, 'e, 'heap) prog"
  where
    "get_heap = Prog (\<lambda>h. h \<turnstile> return h)"

lemma get_heap_ok [simp]: "h \<turnstile> ok (get_heap)"
  by (simp add: get_heap_def execute_def is_OK_def return_def)

lemma get_heap_returns_result [simp]: "(h \<turnstile> get_heap \<bind> (\<lambda>h'. f h') \<rightarrow>\<^sub>r x) = (h \<turnstile> f h \<rightarrow>\<^sub>r x)"
  by(simp add: get_heap_def returns_result_def bind_def return_def execute_def)

lemma get_heap_returns_heap [simp]: "(h \<turnstile> get_heap \<bind> (\<lambda>h'. f h') \<rightarrow>\<^sub>h h'') = (h \<turnstile> f h \<rightarrow>\<^sub>h h'')"
  by(simp add: get_heap_def returns_heap_def bind_def return_def execute_def)

lemma get_heap_is_OK [simp]: "(h \<turnstile> ok (get_heap \<bind> (\<lambda>h'. f h'))) = (h \<turnstile> ok (f h))"
  by(auto simp add: get_heap_def is_OK_def bind_def return_def execute_def)

lemma get_heap_E [elim]: "(h \<turnstile> get_heap \<rightarrow>\<^sub>r x) \<Longrightarrow> x = h"
  by(simp add: get_heap_def returns_result_def return_def execute_def)

definition return_heap :: "'heap \<Rightarrow> ('heap, 'e, unit) prog"
  where
    "return_heap h = Prog (\<lambda>_. h \<turnstile> return ())"

lemma return_heap_E [iff]: "(h \<turnstile> return_heap h' \<rightarrow>\<^sub>h h'') = (h'' = h')"
  by(simp add: return_heap_def returns_heap_def return_def execute_def)

lemma return_heap_returns_result [simp]: "h \<turnstile> return_heap h' \<rightarrow>\<^sub>r ()"
  by(simp add: return_heap_def execute_def returns_result_def return_def)


subsection \<open>Pure Heaps\<close>

definition pure :: "('heap, 'e, 'result) prog \<Rightarrow> 'heap \<Rightarrow> bool"
  where "pure f h \<longleftrightarrow> h \<turnstile> ok f \<longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>h h"

lemma return_pure [simp]: "pure (return x) h"
  by(simp add: pure_def return_def is_OK_def returns_heap_def execute_def)

lemma error_pure [simp]: "pure (error e) h"
  by(simp add: pure_def error_def is_OK_def returns_heap_def execute_def)

lemma noop_pure [simp]: "pure (noop) h"
  by (simp add: noop_def)

lemma get_pure [simp]: "pure get_heap h"
  by(simp add: pure_def get_heap_def is_OK_def returns_heap_def return_def execute_def)

lemma pure_returns_heap_eq:
  "h \<turnstile> f \<rightarrow>\<^sub>h h' \<Longrightarrow> pure f h \<Longrightarrow> h = h'"
  by (meson pure_def is_OK_returns_heap_I returns_heap_eq)

lemma pure_eq_iff:     
  "(\<forall>h' x. h \<turnstile> f \<rightarrow>\<^sub>r x \<longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>h h' \<longrightarrow> h = h') \<longleftrightarrow> pure f h"
  by(auto simp add: pure_def)

subsection \<open>Bind\<close>

lemma bind_assoc [simp]:
  "((bind f g) \<bind> h) = (f \<bind> (\<lambda>x. (g x \<bind> h)))"
  by(auto simp add: bind_def split: sum.splits)

lemma bind_returns_result_E:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y"
  obtains x h' where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>r y"
  using assms by(auto simp add: bind_def returns_result_def returns_heap_def execute_def 
      split: sum.splits)

lemma bind_returns_result_E2:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y" and "pure f h"
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> g x \<rightarrow>\<^sub>r y"
  using assms pure_returns_heap_eq bind_returns_result_E by metis

lemma bind_returns_result_E3:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y" and "h \<turnstile> f \<rightarrow>\<^sub>r x" and "pure f h"
  shows "h \<turnstile> g x \<rightarrow>\<^sub>r y"
  using assms returns_result_eq bind_returns_result_E2 by metis

lemma bind_returns_result_E4:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y" and "h \<turnstile> f \<rightarrow>\<^sub>r x" 
  obtains h' where "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>r y"
  using assms returns_result_eq bind_returns_result_E by metis

lemma bind_returns_heap_E:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h''"
  obtains x h' where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>h h''"
  using assms by(auto simp add: bind_def returns_result_def returns_heap_def execute_def 
      split: sum.splits)

lemma bind_returns_heap_E2 [elim]:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h'" and "pure f h"
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> g x \<rightarrow>\<^sub>h h'"
  using assms pure_returns_heap_eq by (fastforce elim: bind_returns_heap_E)

lemma bind_returns_heap_E3 [elim]:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h'" and "h \<turnstile> f \<rightarrow>\<^sub>r x" and "pure f h" 
  shows "h \<turnstile> g x \<rightarrow>\<^sub>h h'"
  using assms pure_returns_heap_eq returns_result_eq by (fastforce elim: bind_returns_heap_E)

lemma bind_returns_heap_E4:
  assumes "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h''" and "h \<turnstile> f \<rightarrow>\<^sub>h h'"
  obtains x where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h' \<turnstile> g x \<rightarrow>\<^sub>h h''"
  using assms
  by (metis bind_returns_heap_E returns_heap_eq)

lemma bind_returns_error_I [intro]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>e e"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>e e"
  using assms
  by(auto simp add: returns_error_def bind_def execute_def split: sum.splits)

lemma bind_returns_error_I3:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>e e"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>e e"
  using assms
  by(auto simp add: returns_error_def bind_def execute_def returns_heap_def returns_result_def 
      split: sum.splits)

lemma bind_returns_error_I2 [intro]:
  assumes "pure f h" and "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> g x \<rightarrow>\<^sub>e e"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>e e"
  using assms
  by (meson bind_returns_error_I3 is_OK_returns_result_I pure_def)

lemma bind_is_OK_E [elim]:
  assumes "h \<turnstile> ok (f \<bind> g)"
  obtains x h' where "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> ok (g x)"
  using assms 
  by(auto simp add: bind_def returns_result_def returns_heap_def is_OK_def execute_def 
      split: sum.splits)

lemma bind_is_OK_E2:
  assumes "h \<turnstile> ok (f \<bind> g)" and "h \<turnstile> f \<rightarrow>\<^sub>r x"
  obtains h' where "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> ok (g x)"
  using assms 
  by(auto simp add: bind_def returns_result_def returns_heap_def is_OK_def execute_def 
      split: sum.splits)

lemma bind_returns_result_I [intro]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>r y"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y"
  using assms 
  by(auto simp add: bind_def returns_result_def returns_heap_def execute_def 
      split: sum.splits)

lemma bind_pure_returns_result_I [intro]:
  assumes "pure f h" and "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> g x \<rightarrow>\<^sub>r y"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y"
  using assms
  by (meson bind_returns_result_I pure_def is_OK_returns_result_I)

lemma bind_pure_returns_result_I2 [intro]:
  assumes "pure f h" and "h \<turnstile> ok f" and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h \<turnstile> g x \<rightarrow>\<^sub>r y"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y"
  using assms by auto

lemma bind_returns_heap_I [intro]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> g x \<rightarrow>\<^sub>h h''"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h''"
  using assms 
  by(auto simp add: bind_def returns_result_def returns_heap_def execute_def 
      split: sum.splits)

lemma bind_returns_heap_I2 [intro]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h' \<turnstile> g x \<rightarrow>\<^sub>h h''"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>h h''"
  using assms
  by (meson bind_returns_heap_I is_OK_returns_heap_I is_OK_returns_result_E)

lemma bind_is_OK_I [intro]:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'" and "h' \<turnstile> ok (g x)"
  shows "h \<turnstile> ok (f \<bind> g)"
  by (meson assms(1) assms(2) assms(3) bind_returns_heap_I is_OK_returns_heap_E 
      is_OK_returns_heap_I)

lemma bind_is_OK_I2 [intro]:
  assumes "h \<turnstile> ok f" and "\<And>x h'. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> ok (g x)"
  shows "h \<turnstile> ok (f \<bind> g)"
  using assms by blast  

lemma bind_is_OK_pure_I [intro]:
  assumes "pure f h" and "h \<turnstile> ok f" and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h \<turnstile> ok (g x)"
  shows "h \<turnstile> ok (f \<bind> g)"
  using assms by blast

lemma bind_pure_I:
  assumes "pure f h" and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> pure (g x) h"
  shows "pure (f \<bind> g) h"
  using assms
  by (metis bind_returns_heap_E2 pure_def pure_returns_heap_eq is_OK_returns_heap_E)

lemma pure_pure:
  assumes "h \<turnstile> ok f" and "pure f h"
  shows "h \<turnstile> f \<rightarrow>\<^sub>h h"
  using assms returns_heap_eq 
  unfolding pure_def
  by auto

lemma bind_returns_error_eq: 
  assumes "h \<turnstile> f \<rightarrow>\<^sub>e e"
    and "h \<turnstile> g \<rightarrow>\<^sub>e e"
  shows "h \<turnstile> f = h \<turnstile> g"
  using assms 
  by(auto simp add: returns_error_def split: sum.splits)

subsection \<open>Map\<close>

fun map_M :: "('x \<Rightarrow> ('heap, 'e, 'result) prog) \<Rightarrow> 'x list \<Rightarrow> ('heap, 'e, 'result list) prog"
  where
    "map_M f [] = return []"
  | "map_M f (x#xs) = do {
      y \<leftarrow> f x;
      ys \<leftarrow> map_M f xs;
      return (y # ys)
    }"

lemma map_M_ok_I [intro]: 
  "(\<And>x. x \<in> set xs \<Longrightarrow> h \<turnstile> ok (f x)) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> pure (f x) h) \<Longrightarrow> h \<turnstile> ok (map_M f xs)"
  apply(induct xs)
  by (simp_all add: bind_is_OK_I2 bind_is_OK_pure_I)

lemma map_M_pure_I : "\<And>h. (\<And>x. x \<in> set xs \<Longrightarrow> pure (f x) h) \<Longrightarrow> pure (map_M f xs) h"
  apply(induct xs)
   apply(simp)
  by(auto intro!: bind_pure_I)

lemma map_M_pure_E :
  assumes "h \<turnstile> map_M g xs \<rightarrow>\<^sub>r ys" and "x \<in> set xs" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (g x) h"
  obtains y where "h \<turnstile> g x \<rightarrow>\<^sub>r y" and "y \<in> set ys"
  apply(insert assms, induct xs arbitrary: ys)
   apply(simp)
  apply(auto elim!: bind_returns_result_E)[1]
  by (metis (full_types) pure_returns_heap_eq)

lemma map_M_pure_E2:
  assumes "h \<turnstile> map_M g xs \<rightarrow>\<^sub>r ys" and "y \<in> set ys" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (g x) h"
  obtains x where "h \<turnstile> g x \<rightarrow>\<^sub>r y" and "x \<in> set xs"
  apply(insert assms, induct xs arbitrary: ys)
   apply(simp)
  apply(auto elim!: bind_returns_result_E)[1]
  by (metis (full_types) pure_returns_heap_eq)


subsection \<open>Forall\<close>

fun forall_M :: "('y \<Rightarrow> ('heap, 'e, 'result) prog) \<Rightarrow> 'y list \<Rightarrow> ('heap, 'e, unit) prog"
  where
    "forall_M P [] = return ()"
  | "forall_M P (x # xs) = do {
      P x;
      forall_M P xs
    }"
    (* 
lemma forall_M_elim:
  assumes "h \<turnstile> forall_M P xs \<rightarrow>\<^sub>r True" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (P x) h"
  shows "\<forall>x \<in> set xs. h \<turnstile> P x \<rightarrow>\<^sub>r True"
  apply(insert assms, induct xs)
   apply(simp)
  apply(auto elim!: bind_returns_result_E)[1]
  by (metis (full_types) pure_returns_heap_eq) *)

lemma pure_forall_M_I: "(\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h) \<Longrightarrow> pure (forall_M P xs) h"
  apply(induct xs)
  by(auto intro!: bind_pure_I)
    (* 
lemma forall_M_pure_I:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> h \<turnstile> P x \<rightarrow>\<^sub>r True" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (P x)h" 
  shows "h \<turnstile> forall_M P xs \<rightarrow>\<^sub>r True"
  apply(insert assms, induct xs)
   apply(simp)
  by(fastforce)

lemma forall_M_pure_eq:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> h \<turnstile> P x \<rightarrow>\<^sub>r True \<longleftrightarrow> h' \<turnstile> P x \<rightarrow>\<^sub>r True" 
      and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (P x) h"
  shows "(h \<turnstile> forall_M P xs \<rightarrow>\<^sub>r True) \<longleftrightarrow> h' \<turnstile> forall_M P xs \<rightarrow>\<^sub>r True"
  using assms
  by(auto intro!: forall_M_pure_I dest!: forall_M_elim) *)

subsection \<open>Fold\<close>

fun fold_M :: "('result \<Rightarrow> 'y \<Rightarrow> ('heap, 'e, 'result) prog) \<Rightarrow> 'result \<Rightarrow> 'y list
  \<Rightarrow> ('heap, 'e, 'result) prog"
  where 
    "fold_M f d [] = return d" |
    "fold_M f d (x # xs) = do { y \<leftarrow> f d x; fold_M f y xs }"

lemma fold_M_pure_I : "(\<And>d x. pure (f d x) h) \<Longrightarrow> (\<And>d. pure (fold_M f d xs) h)"
  apply(induct xs)
  by(auto intro: bind_pure_I)

subsection \<open>Filter\<close>

fun filter_M :: "('x \<Rightarrow> ('heap, 'e, bool) prog) \<Rightarrow> 'x list \<Rightarrow> ('heap, 'e, 'x list) prog"
  where
    "filter_M P [] = return []"
  | "filter_M P (x#xs) = do {
      p \<leftarrow> P x;
      ys \<leftarrow> filter_M P xs;
      return (if p then x # ys else ys)
    }"

lemma filter_M_pure_I [intro]: "(\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h) \<Longrightarrow> pure (filter_M P xs)h"
  apply(induct xs) 
  by(auto intro!: bind_pure_I)

lemma filter_M_is_OK_I [intro]: "(\<And>x. x \<in> set xs \<Longrightarrow> h \<turnstile> ok (P x)) \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h) \<Longrightarrow> h \<turnstile> ok (filter_M P xs)"
  apply(induct xs)
   apply(simp)
  by(auto intro!: bind_is_OK_pure_I)

lemma filter_M_not_more_elements:
  assumes "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys" and "\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h" and "x \<in> set ys"
  shows "x \<in> set xs"
  apply(insert assms, induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2 split: if_splits intro!: set_ConsD)

lemma filter_M_in_result_if_ok:
  assumes "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys" and "\<And>h x. x \<in> set xs \<Longrightarrow> pure (P x) h" and "x \<in> set xs" and "h \<turnstile> P x \<rightarrow>\<^sub>r True"
  shows "x \<in> set ys"
  apply(insert assms, induct xs arbitrary: ys)
   apply(simp)
  apply(auto elim!: bind_returns_result_E2)[1]
  by (metis returns_result_eq)

lemma filter_M_holds_for_result:
  assumes "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys" and "x \<in> set ys" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (P x) h"
  shows "h \<turnstile> P x \<rightarrow>\<^sub>r True"
  apply(insert assms, induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2 split: if_splits intro!: set_ConsD)

lemma filter_M_empty_I:
  assumes "\<And>x. pure (P x) h"
    and "\<forall>x \<in> set xs. h \<turnstile> P x \<rightarrow>\<^sub>r False"
  shows "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r []"
  using assms
  apply(induct xs)
  by(auto intro!: bind_pure_returns_result_I)

lemma filter_M_subset_2: "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys \<Longrightarrow> h' \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys' 
                          \<Longrightarrow> (\<And>x. pure (P x) h) \<Longrightarrow> (\<And>x. pure (P x) h') 
                          \<Longrightarrow> (\<forall>b. \<forall>x \<in> set xs. h \<turnstile> P x \<rightarrow>\<^sub>r True \<longrightarrow> h' \<turnstile> P x \<rightarrow>\<^sub>r b \<longrightarrow> b) 
                          \<Longrightarrow> set ys \<subseteq> set ys'"
proof -
  assume 1: "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys" and 2: "h' \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys'" 
    and 3: "(\<And>x. pure (P x) h)" and "(\<And>x. pure (P x) h')" 
    and 4: "\<forall>b. \<forall>x\<in>set xs. h \<turnstile> P x \<rightarrow>\<^sub>r True \<longrightarrow> h' \<turnstile> P x \<rightarrow>\<^sub>r b \<longrightarrow> b"
  have h1: "\<forall>x \<in> set xs. h' \<turnstile> ok (P x)"
    using 2 3 \<open>(\<And>x. pure (P x) h')\<close>
    apply(induct xs arbitrary: ys')
    by(auto elim!: bind_returns_result_E2)
  then have 5: "\<forall>x\<in>set xs. h \<turnstile> P x \<rightarrow>\<^sub>r True \<longrightarrow> h' \<turnstile> P x \<rightarrow>\<^sub>r True"
    using 4
    apply(auto)[1]
    by (metis is_OK_returns_result_E)
  show ?thesis
    using 1 2 3 5 \<open>(\<And>x. pure (P x) h')\<close>
    apply(induct xs arbitrary: ys ys')
     apply(auto)[1]
    apply(auto elim!: bind_returns_result_E2 split: if_splits)[1]
          apply auto[1]
         apply auto[1]
        apply(metis returns_result_eq)
       apply auto[1]
      apply auto[1]
     apply auto[1]
    by(auto)
qed

lemma filter_M_subset: "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys \<Longrightarrow> set ys \<subseteq> set xs"
  apply(induct xs arbitrary: h ys)
   apply(auto)[1]
  apply(auto elim!: bind_returns_result_E split: if_splits)[1]
   apply blast
  by blast

lemma filter_M_distinct: "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys \<Longrightarrow> distinct xs \<Longrightarrow> distinct ys"
  apply(induct xs arbitrary: h ys)
   apply(auto)[1]
  using filter_M_subset
  apply(auto elim!: bind_returns_result_E)[1]
  by fastforce

lemma filter_M_filter: "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h) 
                       \<Longrightarrow> (\<forall>x \<in> set xs. h \<turnstile> ok P x) \<and> ys = filter (\<lambda>x. |h \<turnstile> P x|\<^sub>r) xs"
  apply(induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2)

lemma filter_M_filter2: "(\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h \<and>  h \<turnstile> ok P x) 
                       \<Longrightarrow> filter (\<lambda>x. |h \<turnstile> P x|\<^sub>r) xs = ys \<Longrightarrow> h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys"
  apply(induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I)

lemma filter_ex1: "\<exists>!x \<in> set xs. P x \<Longrightarrow> P x \<Longrightarrow> x \<in> set xs \<Longrightarrow> distinct xs 
                  \<Longrightarrow> filter P xs = [x]"
  apply(auto)[1]
  apply(induct xs)
   apply(auto)[1]
  apply(auto)[1]
  using filter_empty_conv by fastforce

lemma filter_M_ex1:
  assumes "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys"
    and "x \<in> set xs"
    and "\<exists>!x \<in> set xs. h \<turnstile> P x \<rightarrow>\<^sub>r True"
    and "\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h"
    and "distinct xs"
    and "h \<turnstile> P x \<rightarrow>\<^sub>r True"
  shows "ys = [x]"
proof -
  have *: "\<exists>!x \<in> set xs. |h \<turnstile> P x|\<^sub>r"
    apply(insert assms(1) assms(3) assms(4))
    apply(drule filter_M_filter) 
     apply(simp)
    apply(auto simp add: select_result_I2)[1]
    by (metis (full_types) is_OK_returns_result_E select_result_I2)
  then show ?thesis
    apply(insert assms(1) assms(4))
    apply(drule filter_M_filter)
     apply(auto)[1] 
    by (metis * assms(2) assms(5) assms(6) distinct_filter 
        distinct_length_2_or_more filter_empty_conv filter_set list.exhaust 
        list.set_intros(1) list.set_intros(2) member_filter select_result_I2)
qed

lemma filter_M_eq:
  assumes "\<And>x. pure (P x) h" and "\<And>x. pure (P x) h'"
    and "\<And>b x. x \<in> set xs \<Longrightarrow> h \<turnstile> P x \<rightarrow>\<^sub>r b = h' \<turnstile> P x \<rightarrow>\<^sub>r b"
  shows "h \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys \<longleftrightarrow> h' \<turnstile> filter_M P xs \<rightarrow>\<^sub>r ys"
  using assms
  apply (induct xs arbitrary: ys)
  by(auto elim!: bind_returns_result_E2 intro!: bind_pure_returns_result_I 
      dest: returns_result_eq)


subsection \<open>Map Filter\<close>

definition map_filter_M :: "('x \<Rightarrow> ('heap, 'e, 'y option) prog) \<Rightarrow> 'x list
  \<Rightarrow> ('heap, 'e, 'y list) prog"
  where
    "map_filter_M f xs = do {
      ys_opts \<leftarrow> map_M f xs;
      ys_no_opts \<leftarrow> filter_M (\<lambda>x. return (x \<noteq> None)) ys_opts;
      map_M (\<lambda>x. return (the x)) ys_no_opts
    }"

lemma map_filter_M_pure: "(\<And>x h. x \<in> set xs \<Longrightarrow> pure (f x) h) \<Longrightarrow> pure (map_filter_M f xs) h"
  by(auto simp add: map_filter_M_def map_M_pure_I intro!: bind_pure_I)

lemma map_filter_M_pure_E:
  assumes "h \<turnstile> (map_filter_M::('x \<Rightarrow> ('heap, 'e, 'y option) prog) \<Rightarrow> 'x list
  \<Rightarrow> ('heap, 'e, 'y list) prog) f xs \<rightarrow>\<^sub>r ys" and "y \<in> set ys" and "\<And>x h. x \<in> set xs \<Longrightarrow> pure (f x) h"
  obtains x where "h \<turnstile> f x \<rightarrow>\<^sub>r Some y" and "x \<in> set xs"
proof -
  obtain ys_opts ys_no_opts where
    ys_opts: "h \<turnstile> map_M f xs \<rightarrow>\<^sub>r ys_opts" and
    ys_no_opts: "h \<turnstile> filter_M (\<lambda>x. (return (x \<noteq> None)::('heap, 'e, bool) prog)) ys_opts \<rightarrow>\<^sub>r ys_no_opts" and
    ys: "h \<turnstile> map_M (\<lambda>x. (return (the x)::('heap, 'e, 'y) prog)) ys_no_opts \<rightarrow>\<^sub>r ys"
    using assms
    by(auto simp add: map_filter_M_def map_M_pure_I elim!: bind_returns_result_E2)
  have "\<forall>y \<in> set ys_no_opts. y \<noteq> None"
    using ys_no_opts filter_M_holds_for_result
    by fastforce
  then have "Some y \<in> set ys_no_opts"
    using map_M_pure_E2 ys \<open>y \<in> set ys\<close>
    by (metis (no_types, lifting) option.collapse return_pure return_returns_result)
  then have "Some y \<in> set ys_opts"
    using filter_M_subset ys_no_opts by fastforce
  then show "(\<And>x. h \<turnstile> f x \<rightarrow>\<^sub>r Some y \<Longrightarrow> x \<in> set xs \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by (metis assms(3) map_M_pure_E2 ys_opts)
qed


subsection \<open>Iterate\<close>

fun iterate_M :: "('heap, 'e, 'result) prog list \<Rightarrow> ('heap, 'e, 'result) prog"
  where
    "iterate_M [] = return undefined"
  | "iterate_M (x # xs) = x \<bind> (\<lambda>_. iterate_M xs)"


lemma iterate_M_concat:
  assumes "h \<turnstile> iterate_M xs \<rightarrow>\<^sub>h h'"
    and "h' \<turnstile> iterate_M ys \<rightarrow>\<^sub>h h''"
  shows "h \<turnstile> iterate_M (xs @ ys) \<rightarrow>\<^sub>h h''"
  using assms
  apply(induct "xs" arbitrary: h h'')
   apply(simp)
  apply(auto)[1]
  by (meson bind_returns_heap_E bind_returns_heap_I)

subsection\<open>Miscellaneous Rules\<close>

lemma execute_bind_simp:
  assumes "h \<turnstile> f \<rightarrow>\<^sub>r x" and "h \<turnstile> f \<rightarrow>\<^sub>h h'"
  shows "h \<turnstile> f \<bind> g = h' \<turnstile> g x"
  using assms 
  by(auto simp add: returns_result_def returns_heap_def bind_def execute_def  
      split: sum.splits)

lemma bind_cong [fundef_cong]:
  fixes f1 f2 :: "('heap, 'e, 'result) prog"
    and g1 g2 :: "'result \<Rightarrow> ('heap, 'e, 'result2) prog"
  assumes "h \<turnstile> f1 = h \<turnstile> f2"
    and "\<And>y h'. h \<turnstile> f1 \<rightarrow>\<^sub>r y \<Longrightarrow> h \<turnstile> f1 \<rightarrow>\<^sub>h h' \<Longrightarrow> h' \<turnstile> g1 y = h' \<turnstile> g2 y"
  shows "h \<turnstile> (f1 \<bind> g1) = h \<turnstile> (f2 \<bind> g2)"
  apply(insert assms, cases "h \<turnstile> f1") 
  by(auto simp add: bind_def returns_result_def returns_heap_def execute_def 
      split: sum.splits)

lemma bind_cong_2:
  assumes "pure f h" and "pure f h'"
    and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x = h' \<turnstile> f \<rightarrow>\<^sub>r x"
    and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h \<turnstile> g x \<rightarrow>\<^sub>r y = h' \<turnstile> g x \<rightarrow>\<^sub>r y'"
  shows "h \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y = h' \<turnstile> f \<bind> g \<rightarrow>\<^sub>r y'"
  using assms
  by(auto intro!: bind_pure_returns_result_I elim!: bind_returns_result_E2)

lemma bind_case_cong [fundef_cong]:
  assumes "x = x'" and "\<And>a. x = Some a \<Longrightarrow> f a h = f' a h"
  shows "(case x of Some a \<Rightarrow> f a | None \<Rightarrow> g) h = (case x' of Some a \<Rightarrow> f' a | None \<Rightarrow> g) h"
  by (insert assms, simp add: option.case_eq_if)


subsection \<open>Reasoning About Reads and Writes\<close>

definition preserved :: "('heap, 'e, 'result) prog \<Rightarrow> 'heap \<Rightarrow> 'heap \<Rightarrow> bool"
  where
    "preserved f h h' \<longleftrightarrow> (\<forall>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<longleftrightarrow> h' \<turnstile> f \<rightarrow>\<^sub>r x)"

lemma reflp_preserved_f [simp]: "reflp (preserved f)"
  by(auto simp add: preserved_def reflp_def)
lemma transp_preserved_f [simp]: "transp (preserved f)"
  by(auto simp add: preserved_def transp_def)


definition 
  all_args :: "('a \<Rightarrow> ('heap, 'e, 'result) prog) \<Rightarrow> ('heap, 'e, 'result) prog set"
  where
    "all_args f = (\<Union>arg. {f arg})"


definition  
  reads :: "('heap \<Rightarrow> 'heap \<Rightarrow> bool) set \<Rightarrow> ('heap, 'e, 'result) prog \<Rightarrow> 'heap 
            \<Rightarrow> 'heap \<Rightarrow> bool"
  where
    "reads S getter h h' \<longleftrightarrow> (\<forall>P \<in> S. reflp P \<and> transp P) \<and> ((\<forall>P \<in> S. P h h') 
                              \<longrightarrow> preserved getter h h')"

lemma reads_singleton [simp]: "reads {preserved f} f h h'"
  by(auto simp add: reads_def)

lemma reads_bind_pure:
  assumes "pure f h" and "pure f h'"
    and "reads S f h h'"
    and "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> reads S (g x) h h'"
  shows "reads S (f \<bind> g) h h'"
  using assms
  by(auto simp add: reads_def pure_pure preserved_def 
      intro!: bind_pure_returns_result_I is_OK_returns_result_I 
      dest: pure_returns_heap_eq 
      elim!: bind_returns_result_E)

lemma reads_insert_writes_set_left: "\<forall>P \<in> S. reflp P \<and> transp P \<Longrightarrow> reads {getter} f h h' \<Longrightarrow> reads (insert getter S) f h h'"
  unfolding reads_def by simp

lemma reads_insert_writes_set_right: "reflp getter \<Longrightarrow> transp getter \<Longrightarrow> reads S f h h' \<Longrightarrow> reads (insert getter S) f h h'"
  unfolding reads_def by blast

lemma reads_subset: "reads S f h h' \<Longrightarrow> \<forall>P \<in> S' - S. reflp P \<and> transp P \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> reads S' f h h'"
  by(auto simp add: reads_def)

lemma return_reads [simp]: "reads {} (return x) h h'"
  by(simp add: reads_def preserved_def)

lemma error_reads [simp]: "reads {} (error e) h h'"
  by(simp add: reads_def preserved_def)

lemma noop_reads [simp]: "reads {} noop h h'"
  by(simp add: reads_def noop_def preserved_def)

lemma filter_M_reads:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h" and "\<And>x. x \<in> set xs \<Longrightarrow> pure (P x) h'"
    and "\<And>x. x \<in> set xs \<Longrightarrow> reads S (P x) h h'"
    and "\<forall>P \<in> S. reflp P \<and> transp P"
  shows "reads S (filter_M P xs) h h'"
  using assms
  apply(induct xs)
  by(auto intro: reads_subset[OF return_reads] intro!: reads_bind_pure)

definition writes :: 
  "('heap, 'e, 'result) prog set \<Rightarrow> ('heap, 'e, 'result2) prog \<Rightarrow> 'heap \<Rightarrow> 'heap \<Rightarrow> bool"
  where                                                                                
    "writes S setter h h' 
     \<longleftrightarrow> (h \<turnstile> setter \<rightarrow>\<^sub>h h' \<longrightarrow> (\<exists>progs. set progs \<subseteq> S \<and> h \<turnstile> iterate_M progs \<rightarrow>\<^sub>h h'))"

lemma writes_singleton [simp]: "writes (all_args f) (f a) h h'"
  apply(auto simp add: writes_def all_args_def)[1]
  apply(rule exI[where x="[f a]"])
  by(auto)

lemma writes_singleton2 [simp]: "writes {f} f h h'"
  apply(auto simp add: writes_def all_args_def)[1]
  apply(rule exI[where x="[f]"])
  by(auto)

lemma writes_union_left_I:
  assumes "writes S f h h'"
  shows "writes (S \<union> S') f h h'"
  using assms
  by(auto simp add: writes_def)

lemma writes_union_right_I:
  assumes "writes S' f h h'"
  shows "writes (S \<union> S') f h h'"
  using assms
  by(auto simp add: writes_def)

lemma writes_union_minus_split:
  assumes "writes (S - S2) f h h'"
    and "writes (S' - S2) f h h'"
  shows "writes ((S \<union> S') - S2) f h h'"
  using assms
  by(auto simp add: writes_def)

lemma writes_subset: "writes S f h h' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> writes S' f h h'"
  by(auto simp add: writes_def)

lemma writes_error [simp]: "writes S (error e) h h'"
  by(simp add: writes_def)

lemma writes_not_ok [simp]: "\<not>h \<turnstile> ok f \<Longrightarrow> writes S f h h'"
  by(auto simp add: writes_def)

lemma writes_pure [simp]:
  assumes "pure f h"
  shows "writes S f h h'"
  using assms
  apply(auto simp add: writes_def)[1]
  by (metis bot.extremum iterate_M.simps(1) list.set(1) pure_returns_heap_eq return_returns_heap)

lemma writes_bind:
  assumes "\<And>h2. writes S f h h2" 
  assumes "\<And>x h2. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> h \<turnstile> f \<rightarrow>\<^sub>h h2 \<Longrightarrow> writes S (g x) h2 h'"
  shows "writes S (f \<bind> g) h h'"
  using assms
  apply(auto simp add: writes_def elim!: bind_returns_heap_E)[1]
  by (metis iterate_M_concat le_supI set_append)

lemma writes_bind_pure:
  assumes "pure f h"
  assumes "\<And>x. h \<turnstile> f \<rightarrow>\<^sub>r x \<Longrightarrow> writes S (g x) h h'"
  shows "writes S (f \<bind> g) h h'"
  using assms
  by(auto simp add: writes_def elim!: bind_returns_heap_E2)

lemma writes_small_big:
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h' w. w \<in> SW \<Longrightarrow>  h \<turnstile> w \<rightarrow>\<^sub>h h' \<Longrightarrow> P h h'"
  assumes "reflp P"
  assumes "transp P"
  shows "P h h'"
proof -
  obtain progs where "set progs \<subseteq> SW" and iterate: "h \<turnstile> iterate_M progs \<rightarrow>\<^sub>h h'"
    by (meson assms(1) assms(2) writes_def)
  then have "\<And>h h'. \<forall>prog \<in> set progs. h \<turnstile> prog \<rightarrow>\<^sub>h h' \<longrightarrow> P h h'"
    using assms(3) by auto
  with iterate assms(4) assms(5) have "h \<turnstile> iterate_M progs \<rightarrow>\<^sub>h h' \<Longrightarrow> P h h'"
  proof(induct progs arbitrary: h)
    case Nil
    then show ?case
      using reflpE by force
  next
    case (Cons a progs)
    then show ?case
      apply(auto elim!: bind_returns_heap_E)[1]
      by (metis (full_types) transpD)
  qed
  then show ?thesis
    using assms(1) iterate by blast
qed

lemma reads_writes_preserved:
  assumes "reads SR getter h h'"
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> SR. r h h')"
  shows "h \<turnstile> getter \<rightarrow>\<^sub>r x \<longleftrightarrow> h' \<turnstile> getter \<rightarrow>\<^sub>r x"
proof -
  obtain progs where "set progs \<subseteq> SW" and iterate: "h \<turnstile> iterate_M progs \<rightarrow>\<^sub>h h'"
    by (meson assms(2) assms(3) writes_def)
  then have "\<And>h h'. \<forall>prog \<in> set progs. h \<turnstile> prog \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> SR. r h h')"
    using assms(4) by blast
  with iterate have "\<forall>r \<in> SR. r h h'"
    using writes_small_big assms(1) unfolding reads_def
    by (metis assms(2) assms(3) assms(4))
  then show ?thesis
    using assms(1)
    by (simp add: preserved_def reads_def)
qed

lemma reads_writes_separate_forwards:
  assumes "reads SR getter h h'"
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "h \<turnstile> getter \<rightarrow>\<^sub>r x"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> SR. r h h')"
  shows "h' \<turnstile> getter \<rightarrow>\<^sub>r x"
  using reads_writes_preserved[OF assms(1) assms(2) assms(3) assms(5)] assms(4)
  by(auto simp add: preserved_def)

lemma reads_writes_separate_backwards:
  assumes "reads SR getter h h'"
  assumes "writes SW setter h h'"
  assumes "h \<turnstile> setter \<rightarrow>\<^sub>h h'"
  assumes "h' \<turnstile> getter \<rightarrow>\<^sub>r x"
  assumes "\<And>h h'. \<forall>w \<in> SW. h \<turnstile> w \<rightarrow>\<^sub>h h' \<longrightarrow> (\<forall>r \<in> SR. r h h')"
  shows "h \<turnstile> getter \<rightarrow>\<^sub>r x"
  using reads_writes_preserved[OF assms(1) assms(2) assms(3) assms(5)] assms(4)
  by(auto simp add: preserved_def)

end
