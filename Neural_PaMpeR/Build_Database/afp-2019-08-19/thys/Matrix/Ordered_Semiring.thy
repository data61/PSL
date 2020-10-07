(*  Title:       Executable Matrix Operations on Matrices of Arbitrary Dimensions
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

(*
Copyright 2013 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
theory Ordered_Semiring 
imports 
  "HOL-Algebra.Ring"
  "Abstract-Rewriting.SN_Orders"
begin

record 'a ordered_semiring = "'a ring" +
  geq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succeq>\<index>" 50)
  gt :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<succ>\<index>" 50)
  max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("Max\<index>")

lemmas ordered_semiring_record_simps = ring_record_simps ordered_semiring.simps

locale ordered_semiring = semiring +
  assumes compat: "\<lbrakk>s \<succeq> (t :: 'a); t \<succ> u; s \<in> carrier R; t \<in> carrier R; u \<in> carrier R\<rbrakk> \<Longrightarrow> s \<succ> u"
  and compat2: "\<lbrakk>s \<succ> (t :: 'a); t \<succeq> u; s \<in> carrier R ; t \<in> carrier R; u \<in> carrier R\<rbrakk> \<Longrightarrow> s \<succ> u"
  and plus_left_mono: "\<lbrakk>x \<succeq> y; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> z \<succeq> y \<oplus> z"
  and times_left_mono: "\<lbrakk>z \<succeq> \<zero>; x \<succeq> y; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> z \<succeq> y \<otimes> z"
  and times_right_mono: "\<lbrakk>x \<succeq> \<zero>; y \<succeq> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<otimes> y \<succeq> x \<otimes> z"
  and geq_refl: "x \<in> carrier R \<Longrightarrow> x \<succeq> x"
  and geq_trans[trans]: "\<lbrakk>x \<succeq> y; y \<succeq> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succeq> z"
  and gt_trans[trans]: "\<lbrakk>x \<succ> y; y \<succ> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<succ> z"
  and gt_imp_ge: "x \<succ> y \<Longrightarrow> x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> x \<succeq> y"
  and max_comm: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> Max x y = Max y x"
  and max_ge: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> Max x y \<succeq> x"
  and max_id: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> x \<succeq> y \<Longrightarrow> Max x y = x"
  and max_mono: "x \<succeq> y \<Longrightarrow> x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> z \<in> carrier R \<Longrightarrow> Max z x \<succeq> Max z y"
  and wf_max[simp, intro]: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> Max x y \<in> carrier R"
  and one_geq_zero: "\<one> \<succeq> \<zero>"
begin
lemma max_ge_right: assumes x: "x \<in> carrier R" and y: "y \<in> carrier R" shows "Max x y \<succeq> y"
  by (unfold max_comm[OF x y], rule max_ge[OF y x])

lemma wf_max0: "x \<in> carrier R \<Longrightarrow> Max \<zero> x \<in> carrier R" using wf_max[of \<zero> x] by auto

lemma max0_id_pos: assumes x: "x \<succeq> \<zero>" and wf: "x \<in> carrier R"
  shows "Max \<zero> x = x" unfolding max_comm[OF zero_closed wf] by (rule max_id[OF wf zero_closed x])
end
hide_const (open) gt geq max

subsection \<open>A connection between class based semirings and set based semirings\<close>

definition class_semiring :: "'a itself \<Rightarrow> 'b \<Rightarrow> ('a :: {plus,times,one,zero},'b)ring_scheme" where
  "class_semiring _ b \<equiv> \<lparr> carrier = UNIV, mult = (*), one = 1, zero = 0, add = (+), \<dots> = b\<rparr>"

lemma class_semiring: "semiring (class_semiring (TYPE('a :: ordered_semiring_1)) b)"
  unfolding class_semiring_def
  by (unfold_locales, auto simp: field_simps)

definition class_ordered_semiring :: "'a itself \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> ('a,'b) ordered_semiring_scheme" where
  "class_ordered_semiring a gt b \<equiv> class_semiring a \<lparr>
    ordered_semiring.geq = (\<ge>),
    gt = gt,
    max = max,
    \<dots> = b\<rparr>"

lemma class_ordered_semiring: assumes "order_pair (gt :: ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool)) d"
  shows "ordered_semiring 
    (class_ordered_semiring (TYPE('a)) gt b)" 
  (is "ordered_semiring ?R")
proof -
  interpret order_pair gt d by fact
  interpret semiring ?R unfolding class_ordered_semiring_def by (rule class_semiring)
  show ?thesis 
    by (unfold_locales, unfold class_ordered_semiring_def class_semiring_def, auto
    intro: compat compat2 gt_imp_ge ge_trans max_comm max_id max_mono ge_refl one_ge_zero
     times_left_mono times_right_mono plus_left_mono)
qed

lemma (in one_mono_ordered_semiring_1) class_ordered_semiring:  
  "ordered_semiring 
    (class_ordered_semiring (TYPE('a)) (\<succ>) b)" 
  by (rule class_ordered_semiring[of _ default], unfold_locales)

lemma (in both_mono_ordered_semiring_1) class_ordered_semiring:  
  "ordered_semiring 
    (class_ordered_semiring (TYPE('a)) (\<succ>) b)" 
  by (rule class_ordered_semiring[of _ default], unfold_locales)


end
