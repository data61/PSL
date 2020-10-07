(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Determinism\<close>

theory Determinism imports WellDefined begin

text_raw \<open>\label{s:prog_determ}\<close>

text \<open>We provide a set of lemmas for establishing that
  appropriately restricted programs are fully additive, and
  maximal in the refinement order.  This is particularly useful
  with data refinement, as it implies correspondence.\<close>

subsection  \<open>Additivity\<close>

lemma additive_wp_Abort:
  "additive (wp (Abort))"
  by(auto simp:wp_eval)

text \<open>@{term "wlp Abort"} is not additive.\<close>

lemma additive_wp_Skip:
  "additive (wp (Skip))"
  by(auto simp:wp_eval)

lemma additive_wp_Apply:
  "additive (wp (Apply f))"
  by(auto simp:wp_eval)

lemma additive_wp_Seq:
  fixes a::"'s prog"
  assumes adda: "additive (wp a)"
      and addb: "additive (wp b)"
      and wb:   "well_def b"
  shows "additive (wp (a ;; b))"
proof(rule additiveI, unfold wp_eval o_def)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  assume sP: "sound P" and sQ: "sound Q"

  note hb = well_def_wp_healthy[OF wb]

  from addb sP sQ
  have "wp b (\<lambda>s. P s + Q s) = (\<lambda>s. wp b P s + wp b Q s)"
    by(blast dest:additiveD)
  with adda sP sQ hb
  show "wp a (wp b (\<lambda>s. P s + Q s)) s =
        wp a (wp b P) s + (wp a (wp b Q)) s"
    by(auto intro:fun_cong[OF additiveD])
qed

lemma additive_wp_PC:
  "\<lbrakk> additive (wp a); additive (wp b) \<rbrakk> \<Longrightarrow> additive (wp (a \<^bsub>P\<^esub>\<oplus> b))"
  by(rule additiveI, simp add:additiveD field_simps wp_eval)

text \<open>@{term DC} is not additive.\<close>

lemma additive_wp_SetPC:
  "\<lbrakk> \<And>x s. x \<in> supp (p s) \<Longrightarrow> additive (wp (a x)); \<And>s. finite (supp (p s)) \<rbrakk> \<Longrightarrow>
   additive (wp (SetPC a p))"
  by(rule additiveI,
     simp add:wp_eval additiveD distrib_left sum.distrib)

lemma additive_wp_Bind:
  "\<lbrakk> \<And>x. additive (wp (a (f x))) \<rbrakk> \<Longrightarrow> additive (wp (Bind f a))"
  by(simp add:wp_eval additive_def)

lemma additive_wp_Embed:
  "\<lbrakk> additive t \<rbrakk> \<Longrightarrow> additive (wp (Embed t))"
  by(simp add:wp_eval)

lemma additive_wp_repeat:
  "additive (wp a) \<Longrightarrow> well_def a \<Longrightarrow> additive (wp (repeat n a))"
  by(induct n, auto simp:additive_wp_Skip intro:additive_wp_Seq wd_intros)

lemmas fa_intros =
  additive_wp_Abort additive_wp_Skip
  additive_wp_Apply additive_wp_Seq
  additive_wp_PC    additive_wp_SetPC
  additive_wp_Bind  additive_wp_Embed
  additive_wp_repeat

subsection \<open>Maximality\<close>

lemma max_wp_Skip:
  "maximal (wp Skip)"
  by(simp add:maximal_def wp_eval)

lemma max_wp_Apply:
  "maximal (wp (Apply f))"
  by(auto simp:wp_eval o_def)

lemma max_wp_Seq:
  "\<lbrakk> maximal (wp a); maximal (wp b) \<rbrakk> \<Longrightarrow> maximal (wp (a ;; b))"
  by(simp add:wp_eval maximal_def)

lemma max_wp_PC:
  "\<lbrakk> maximal (wp a); maximal (wp b) \<rbrakk> \<Longrightarrow> maximal (wp (a \<^bsub>P\<^esub>\<oplus> b))"
  by(rule maximalI, simp add:maximalD field_simps wp_eval)

lemma max_wp_DC:
  "\<lbrakk> maximal (wp a); maximal (wp b) \<rbrakk> \<Longrightarrow> maximal (wp (a \<Sqinter> b))"
  by(rule maximalI, simp add:wp_eval maximalD)

lemma max_wp_SetPC:
  "\<lbrakk> \<And>s a. a \<in> supp (P s) \<Longrightarrow> maximal (wp (p a)); \<And>s. (\<Sum>a\<in>supp (P s). P s a) = 1 \<rbrakk> \<Longrightarrow>
  maximal (wp (SetPC p P))"
  by(auto simp:maximalD wp_def SetPC_def sum_distrib_right[symmetric])

lemma max_wp_SetDC:
  fixes p::"'a \<Rightarrow> 's prog"
  assumes mp: "\<And>s a. a \<in> S s \<Longrightarrow> maximal (wp (p a))"
      and ne: "\<And>s. S s \<noteq> {}"
  shows "maximal (wp (SetDC p S))"
proof(rule maximalI, rule ext, unfold wp_eval)
  fix c::real and s::'s
  assume "0 \<le> c"
  hence "Inf ((\<lambda>a. wp (p a) (\<lambda>_. c) s) ` S s) = Inf ((\<lambda>_. c) ` S s)"
    using mp by(simp add:maximalD cong:image_cong)
  also {
    from ne obtain a where "a \<in> S s" by blast
    hence "Inf ((\<lambda>_. c) ` S s) = c"
      by (auto simp add: image_constant_conv cong del: INF_cong_simp)
  }
  finally show "Inf ((\<lambda>a. wp (p a) (\<lambda>_. c) s) ` S s) = c" .
qed
 
lemma max_wp_Embed:
  "maximal t \<Longrightarrow> maximal (wp (Embed t))"
  by(simp add:wp_eval)

lemma max_wp_repeat:
  "maximal (wp a) \<Longrightarrow> maximal (wp (repeat n a))"
  by(induct n, simp_all add:max_wp_Skip max_wp_Seq)

lemma max_wp_Bind:
  assumes ma: "\<And>s. maximal (wp (a (f s)))"
  shows "maximal (wp (Bind f a))"
proof(rule maximalI, rule ext, simp add:wp_eval)
  fix c::real and s
  assume "0 \<le> c"
  with ma have "wp (a (f s)) (\<lambda>_. c) = (\<lambda>_. c)" by(blast)
  thus "wp (a (f s)) (\<lambda>_. c) s = c" by(auto)
qed

lemmas max_intros =
  max_wp_Skip  max_wp_Apply
  max_wp_Seq   max_wp_PC
  max_wp_DC    max_wp_SetPC
  max_wp_SetDC max_wp_Embed
  max_wp_Bind  max_wp_repeat

text \<open>A healthy transformer that terminates is maximal.\<close>
lemma healthy_term_max:
  assumes ht: "healthy t"
      and trm: "\<lambda>s. 1 \<tturnstile> t (\<lambda>s. 1)"
  shows "maximal t"
proof(intro maximalI ext)
  fix c::real and s
  assume nnc: "0 \<le> c"

  have "t (\<lambda>s. c) s = t (\<lambda>s. 1 * c) s" by(simp)
  also from nnc healthy_scalingD[OF ht]
  have "... = c * t (\<lambda>s. 1) s" by(simp add:scalingD)
  also {
    from ht have "t (\<lambda>s. 1) \<tturnstile> \<lambda>s. 1" by(auto)
    with trm have "t (\<lambda>s. 1) = (\<lambda>s. 1)" by(auto)
    hence "c * t (\<lambda>s. 1) s = c" by(simp)
  }
  finally show "t (\<lambda>s. c) s = c" .
qed

subsection \<open>Determinism\<close>

lemma det_wp_Skip:
  "determ (wp Skip)"
  using max_intros fa_intros by(blast)

lemma det_wp_Apply:
  "determ (wp (Apply f))"
  by(intro determI fa_intros max_intros)

lemma det_wp_Seq:
  "determ (wp a) \<Longrightarrow> determ (wp b) \<Longrightarrow> well_def b \<Longrightarrow> determ (wp (a ;; b))"
  by(intro determI fa_intros max_intros, auto)

lemma det_wp_PC:
  "determ (wp a) \<Longrightarrow> determ (wp b) \<Longrightarrow> determ (wp (a \<^bsub>P\<^esub>\<oplus> b))"
  by(intro determI fa_intros max_intros, auto)

lemma det_wp_SetPC:
  "(\<And>x s. x \<in> supp (p s) \<Longrightarrow> determ (wp (a x))) \<Longrightarrow>
   (\<And>s. finite (supp (p s))) \<Longrightarrow>
   (\<And>s. sum (p s) (supp (p s)) = 1) \<Longrightarrow>
   determ (wp (SetPC a p))"
  by(intro determI fa_intros max_intros, auto)

lemma det_wp_Bind:
  "(\<And>x. determ (wp (a (f x)))) \<Longrightarrow> determ (wp (Bind f a))"
  by(intro determI fa_intros max_intros, auto)

lemma det_wp_Embed:
  "determ t \<Longrightarrow> determ (wp (Embed t))"
  by(simp add:wp_eval)

lemma det_wp_repeat:
  "determ (wp a) \<Longrightarrow> well_def a \<Longrightarrow> determ (wp (repeat n a))"
  by(intro determI fa_intros max_intros, auto)

lemmas determ_intros =
  det_wp_Skip det_wp_Apply
  det_wp_Seq  det_wp_PC
  det_wp_SetPC det_wp_Bind
  det_wp_Embed det_wp_repeat

end
