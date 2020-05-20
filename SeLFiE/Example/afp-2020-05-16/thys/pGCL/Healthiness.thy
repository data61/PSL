(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Healthiness\<close>

theory Healthiness imports Embedding begin

subsection \<open>The Healthiness of the Embedding\<close>

text \<open>Healthiness is mostly derived by structural induction using
  the simplifier.  @{term Abort}, @{term Skip} and @{term Apply}
  form base cases.\<close>

lemma healthy_wp_Abort:
  "healthy (wp Abort)"
proof(rule healthy_parts)
  fix b and P::"'a \<Rightarrow> real"
  assume nP: "nneg P" and bP: "bounded_by b P"
  thus "bounded_by b (wp Abort P)"
    unfolding wp_eval by(blast)
  show "nneg (wp Abort P)"
    unfolding wp_eval by(blast)
next
  fix P Q::"'a expect"
  show "wp Abort P \<tturnstile> wp Abort Q"
    unfolding wp_eval by(blast)
next
  fix P and c and s::'a
  show "c * wp Abort P s = wp Abort (\<lambda>s. c * P s) s"
    unfolding wp_eval by(auto)
qed

lemma nearly_healthy_wlp_Abort:
  "nearly_healthy (wlp Abort)"
proof(rule nearly_healthyI)
  fix P::"'s \<Rightarrow> real"
  show "unitary (wlp Abort P)"
    by(simp add:wp_eval)
next
  fix P Q :: "'s expect"
  assume "P \<tturnstile> Q" and "unitary P" and "unitary Q"
  thus "wlp Abort P \<tturnstile> wlp Abort Q"
    unfolding wp_eval by(blast)
qed

lemma healthy_wp_Skip:
  "healthy (wp Skip)"
  by(force intro!:healthy_parts simp:wp_eval)

lemma nearly_healthy_wlp_Skip:
  "nearly_healthy (wlp Skip)"
  by(auto simp:wp_eval)

lemma healthy_wp_Seq:
  fixes t::"'s prog" and u
  assumes ht: "healthy (wp t)" and hu: "healthy (wp u)"
  shows "healthy (wp (t ;; u))"
proof(rule healthy_parts, simp_all add:wp_eval)
  fix b and P::"'s \<Rightarrow> real"
  assume "bounded_by b P" and "nneg P"
  with hu have "bounded_by b (wp u P)" and "nneg (wp u P)" by(auto)
  with ht show "bounded_by b (wp t (wp u P))"
           and "nneg (wp t (wp u P))" by(auto)
next
  fix P::"'s \<Rightarrow> real" and Q
  assume "sound P" and "sound Q" and "P \<tturnstile> Q"
  with hu have "sound (wp u P)" and "sound (wp u Q)"
    and "wp u P \<tturnstile> wp u Q" by(auto)
  with ht show "wp t (wp u P) \<tturnstile> wp t (wp u Q)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and c::real and s
  assume pos: "0 \<le> c" and sP: "sound P"
  with ht and hu have "c * wp t (wp u P) s = wp t (\<lambda>s. c * wp u P s) s"
    by(auto intro!:scalingD)
  also with hu and pos and sP have "... = wp t (wp u (\<lambda>s. c * P s)) s"
    by(simp add:scalingD[OF healthy_scalingD])
  finally show "c * wp t (wp u P) s = wp t (wp u (\<lambda>s. c * P s)) s" .
qed

lemma nearly_healthy_wlp_Seq:
  fixes t::"'s prog" and u
  assumes ht: "nearly_healthy (wlp t)" and hu: "nearly_healthy (wlp u)"
  shows "nearly_healthy (wlp (t ;; u))"
proof(rule nearly_healthyI, simp_all add:wp_eval)
  fix b and P::"'s \<Rightarrow> real"
  assume "unitary P"
  with hu have "unitary (wlp u P)" by(auto)
  with ht show "unitary (wlp t (wlp u P))" by(auto)
next
  fix P Q::"'s \<Rightarrow> real"
  assume "unitary P" and "unitary Q" and "P \<tturnstile> Q"
  with hu have "unitary (wlp u P)" and "unitary (wlp u Q)"
    and "wlp u P \<tturnstile> wlp u Q" by(auto)
  with ht show "wlp t (wlp u P) \<tturnstile> wlp t (wlp u Q)" by(auto)
qed

lemma healthy_wp_PC:
  fixes f::"'s prog" 
  assumes hf: "healthy (wp f)" and hg: "healthy (wp g)"
      and uP: "unitary P"
  shows "healthy (wp (f \<^bsub>P\<^esub>\<oplus> g))"
proof(intro healthy_parts bounded_byI nnegI le_funI, simp_all add:wp_eval)
  fix b and Q::"'s \<Rightarrow> real" and s::'s
  assume nQ: "nneg Q" and bQ: "bounded_by b Q"

  txt \<open>Non-negative:\<close>
  from nQ and bQ and hf have "0 \<le> wp f Q s" by(auto)
  with uP have "0 \<le> P s * ..." by(auto intro:mult_nonneg_nonneg)
  moreover {
    from uP have "0 \<le> 1 - P s"
      by auto
    with nQ and bQ and hg have "0 \<le> ... * wp g Q s"
      by (metis healthy_nnegD2 mult_nonneg_nonneg nneg_def)
  }
  ultimately show "0 \<le> P s * wp f Q s + (1 - P s) * wp g Q s"
    by(auto intro:mult_nonneg_nonneg)

  txt \<open>Bounded:\<close>
  from nQ bQ hf have "wp f Q s \<le> b" by(auto)
  with uP nQ bQ hf have "P s * wp f Q s \<le> P s * b"
    by(blast intro!:mult_mono)
  moreover {
    from nQ bQ hg uP
    have "wp g Q s \<le> b" and "0 \<le> 1 - P s"
      by auto
    with nQ bQ hg have "(1 - P s) * wp g Q s \<le> (1 - P s) * b"
      by(blast intro!:mult_mono)
  }
  ultimately have "P s * wp f Q s + (1 - P s) * wp g Q s \<le>
                   P s * b + (1 - P s) * b"
    by(blast intro:add_mono)
  also have "... = b" by(auto simp:algebra_simps)
  finally show "P s * wp f Q s + (1 - P s) * wp g Q s \<le> b" .
next
  txt \<open>Monotonic:\<close>
  fix Q R::"'s \<Rightarrow> real" and s
  assume sQ: "sound Q" and sR: "sound R" and le: "Q \<tturnstile> R"

  with hf have "wp f Q s \<le> wp f R s" by(blast dest:mono_transD)
  with uP have "P s * wp f Q s \<le> P s * wp f R s"
    by(auto intro:mult_left_mono)
  moreover {
    from sQ sR le hg
    have "wp g Q s \<le> wp g R s" by(blast dest:mono_transD)
    moreover from uP have "0 \<le> 1 - P s"
      by auto
    ultimately have "(1 - P s) * wp g Q s \<le> (1 - P s) * wp g R s"
      by(auto intro:mult_left_mono)
  }
  ultimately show "P s * wp f Q s + (1 - P s) * wp g Q s \<le>
                   P s * wp f R s + (1 - P s) * wp g R s" by(auto)
next
  txt \<open>Scaling:\<close>
  fix Q::"'s \<Rightarrow> real" and c::real and s::'s
  assume sQ: "sound Q" and pos: "0 \<le> c"
  have "c * (P s * wp f Q s + (1 - P s) * wp g Q s) =
        P s * (c * wp f Q s) + (1 - P s) * (c * wp g Q s)"
    by(simp add:distrib_left)
  also have "... = P s * wp f (\<lambda>s.  c * Q s) s +
                   (1 - P s) * wp g (\<lambda>s. c * Q s) s"
    using hf hg sQ pos
    by(simp add:scalingD[OF healthy_scalingD])
  finally show "c * (P s * wp f Q s + (1 - P s) * wp g Q s) =
                P s * wp f (\<lambda>s. c * Q s) s + (1 - P s) * wp g (\<lambda>s. c * Q s) s" .
qed

lemma nearly_healthy_wlp_PC:
  fixes f::"'s prog" 
  assumes hf: "nearly_healthy (wlp f)"
      and hg: "nearly_healthy (wlp g)"
      and uP: "unitary P"
  shows "nearly_healthy (wlp (f \<^bsub>P\<^esub>\<oplus> g))"
proof(intro nearly_healthyI unitaryI2 nnegI bounded_byI le_funI,
      simp_all add:wp_eval)
  fix Q::"'s expect" and s::'s
  assume uQ: "unitary Q"
  from uQ hf hg have utQ: "unitary (wlp f Q)" "unitary (wlp g Q)" by(auto)
  from uP have nnP: "0 \<le> P s" "0 \<le> 1 - P s"
    by auto
  moreover from utQ have "0 \<le> wlp f Q s" "0 \<le> wlp g Q s" by(auto)
  ultimately show "0 \<le> P s * wlp f Q s + (1 - P s) * wlp g Q s"
    by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)

  from utQ have "wlp f Q s \<le> 1" "wlp g Q s \<le> 1" by(auto)
  with nnP have "P s * wlp f Q s + (1 - P s) * wlp g Q s \<le> P s * 1 + (1 - P s) * 1"
    by(blast intro:add_mono mult_left_mono)
  thus "P s * wlp f Q s + (1 - P s) * wlp g Q s \<le> 1" by(simp)

  fix R::"'s expect"
  assume uR: "unitary R" and le: "Q \<tturnstile> R"
  with uQ have "wlp f Q s \<le> wlp f R s"
    by(auto intro:le_funD[OF nearly_healthy_monoD, OF hf])
  with nnP have "P s * wlp f Q s \<le> P s * wlp f R s"
    by(auto intro:mult_left_mono)
  moreover {
    from uQ uR le have "wlp g Q s \<le> wlp g R s"
      by(auto intro:le_funD[OF nearly_healthy_monoD, OF hg])
    with nnP have "(1 - P s) * wlp g Q s \<le> (1 - P s) * wlp g R s"
      by(auto intro:mult_left_mono)
  }
  ultimately show "P s * wlp f Q s + (1 - P s) * wlp g Q s \<le>
                   P s * wlp f R s + (1 - P s) * wlp g R s"
    by(auto)
qed

lemma healthy_wp_DC:
  fixes f::"'s prog"
  assumes hf: "healthy (wp f)" and hg: "healthy (wp g)"
  shows "healthy (wp (f \<Sqinter> g))"
proof(intro healthy_parts bounded_byI nnegI le_funI, simp_all only:wp_eval)
  fix b and P::"'s \<Rightarrow> real" and s::'s
  assume nP: "nneg P" and bP: "bounded_by b P"

  with hf have "bounded_by b (wp f P)" by(auto)
  hence "wp f P s \<le> b" by(blast)
  thus "min (wp f P s) (wp g P s) \<le> b" by(auto)

  from nP bP assms show "0 \<le> min (wp f P s) (wp g P s)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and Q and s::'s
  from assms have mf: "mono_trans (wp f)" and mg: "mono_trans (wp g)" by(auto)
  assume sP: "sound P" and sQ: "sound Q" and le: "P \<tturnstile> Q"
  hence "wp f P s \<le> wp f Q s" and "wp g P s \<le> wp g Q s"
    by(auto intro:le_funD[OF mono_transD[OF mf]] le_funD[OF mono_transD[OF mg]])
  thus "min (wp f P s) (wp g P s) \<le> min (wp f Q s) (wp g Q s)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and c::real and s::'s
  assume sP: "sound P" and pos: "0 \<le> c"
  from assms have sf: "scaling (wp f)" and sg: "scaling (wp g)" by(auto)
  from pos have "c * min (wp f P s) (wp g P s) =
                 min (c * wp f P s) (c * wp g P s)"
    by(simp add:min_distrib)
  also from sP and pos
  have "... = min (wp f (\<lambda>s. c * P s) s) (wp g (\<lambda>s. c * P s) s)"
    by(simp add:scalingD[OF sf] scalingD[OF sg])
  finally show "c * min (wp f P s) (wp g P s) =
                min (wp f (\<lambda>s. c * P s) s) (wp g (\<lambda>s. c * P s) s)" .
qed

lemma nearly_healthy_wlp_DC:
  fixes f::"'s prog"
  assumes hf: "nearly_healthy (wlp f)"
      and hg: "nearly_healthy (wlp g)"
  shows "nearly_healthy (wlp (f \<Sqinter> g))"
proof(intro nearly_healthyI bounded_byI nnegI le_funI unitaryI2,
      simp_all add:wp_eval, safe)
  fix P::"'s \<Rightarrow> real" and s::'s
  assume uP: "unitary P"
  with hf hg have utP: "unitary (wlp f P)" "unitary (wlp g P)" by(auto)
  thus "0 \<le> wlp f P s" "0 \<le> wlp g P s" by(auto)

  have "min (wlp f P s) (wlp g P s) \<le> wlp f P s" by(auto)
  also from utP have "... \<le> 1" by(auto)
  finally show "min (wlp f P s) (wlp g P s) \<le> 1" .

  fix Q::"'s \<Rightarrow> real"
  assume uQ: "unitary Q" and le: "P \<tturnstile> Q"
  have "min (wlp f P s) (wlp g P s) \<le> wlp f P s" by(auto)
  also from uP uQ le have "... \<le> wlp f Q s"
    by(auto intro:le_funD[OF nearly_healthy_monoD, OF hf])
  finally show "min (wlp f P s) (wlp g P s) \<le> wlp f Q s" .

  have "min (wlp f P s) (wlp g P s) \<le> wlp g P s" by(auto)
  also from uP uQ le have "... \<le> wlp g Q s"
    by(auto intro:le_funD[OF nearly_healthy_monoD, OF hg])
  finally show "min (wlp f P s) (wlp g P s) \<le> wlp g Q s" .
qed

lemma healthy_wp_AC:
  fixes f::"'s prog"
  assumes hf: "healthy (wp f)" and hg: "healthy (wp g)"
  shows "healthy (wp (f \<Squnion> g))"
proof(intro healthy_parts bounded_byI nnegI le_funI, simp_all only:wp_eval)
  fix b and P::"'s \<Rightarrow> real" and s::'s
  assume nP: "nneg P" and bP: "bounded_by b P"

  with hf have "bounded_by b (wp f P)" by(auto)
  hence "wp f P s \<le> b" by(blast)
  moreover {
    from bP nP hg have "bounded_by b (wp g P)" by(auto)
    hence "wp g P s \<le> b" by(blast)
  }
  ultimately show "max (wp f P s) (wp g P s) \<le> b" by(auto)

  from nP bP assms have "0 \<le> wp f P s" by(auto)
  thus "0 \<le> max (wp f P s) (wp g P s)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and Q and s::'s
  from assms have mf: "mono_trans (wp f)" and mg: "mono_trans (wp g)" by(auto)
  assume sP: "sound P" and sQ: "sound Q" and le: "P \<tturnstile> Q"
  hence "wp f P s \<le> wp f Q s" and "wp g P s \<le> wp g Q s"
    by(auto intro:le_funD[OF mono_transD, OF mf] le_funD[OF mono_transD, OF mg])
  thus "max (wp f P s) (wp g P s) \<le> max (wp f Q s) (wp g Q s)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and c::real and s::'s
  assume sP: "sound P" and pos: "0 \<le> c"
  from assms have sf: "scaling (wp f)" and sg: "scaling (wp g)" by(auto)
  from pos have "c * max (wp f P s) (wp g P s) =
                 max (c * wp f P s) (c * wp g P s)"
    by(simp add:max_distrib)
  also from sP and pos
  have "... = max (wp f (\<lambda>s. c * P s) s) (wp g (\<lambda>s. c * P s) s)"
    by(simp add:scalingD[OF sf] scalingD[OF sg])
  finally show "c * max (wp f P s) (wp g P s) =
                max (wp f (\<lambda>s. c * P s) s) (wp g (\<lambda>s. c * P s) s)" .
qed

lemma nearly_healthy_wlp_AC:
  fixes f::"'s prog"
  assumes hf: "nearly_healthy (wlp f)"
      and hg: "nearly_healthy (wlp g)"
  shows "nearly_healthy (wlp (f \<Squnion> g))"
proof(intro nearly_healthyI bounded_byI nnegI unitaryI2 le_funI, simp_all only:wp_eval)
  fix b and P::"'s \<Rightarrow> real" and s::'s
  assume uP: "unitary P"

  with hf have "wlp f P s \<le> 1" by(auto)
  moreover from uP hg have "unitary (wlp g P)" by(auto)
  hence "wlp g P s \<le> 1" by(auto)
  ultimately show "max (wlp f P s) (wlp g P s) \<le> 1" by(auto)

  from uP hf have "unitary (wlp f P)" by(auto)
  hence "0 \<le> wlp f P s" by(auto)
  thus "0 \<le> max (wlp f P s) (wlp g P s)" by(auto)
next
  fix P::"'s \<Rightarrow> real" and Q and s::'s
  assume uP: "unitary P" and uQ: "unitary Q" and le: "P \<tturnstile> Q"
  hence "wlp f P s \<le> wlp f Q s" and "wlp g P s \<le> wlp g Q s"
    by(auto intro:le_funD[OF nearly_healthy_monoD, OF hf]
                  le_funD[OF nearly_healthy_monoD, OF hg])
  thus "max (wlp f P s) (wlp g P s) \<le> max (wlp f Q s) (wlp g Q s)" by(auto)
qed

lemma healthy_wp_Embed:
  "healthy t \<Longrightarrow> healthy (wp (Embed t))"
  unfolding wp_def Embed_def by(simp)

lemma nearly_healthy_wlp_Embed:
  "nearly_healthy t \<Longrightarrow> nearly_healthy (wlp (Embed t))"
  unfolding wlp_def Embed_def by(simp)

lemma healthy_wp_repeat:
  assumes h_a: "healthy (wp a)"
  shows "healthy (wp (repeat n a))" (is "?X n")
proof(induct n)
  show "?X 0" by(auto simp:wp_eval)
next
  fix n assume IH: "?X n"
  thus "?X (Suc n)" by(simp add:healthy_wp_Seq h_a)
qed

lemma nearly_healthy_wlp_repeat:
  assumes h_a: "nearly_healthy (wlp a)"
  shows "nearly_healthy (wlp (repeat n a))" (is "?X n")
proof(induct n)
  show "?X 0" by(simp add:wp_eval)
next
  fix n assume IH: "?X n"
  thus "?X (Suc n)" by(simp add:nearly_healthy_wlp_Seq h_a)
qed

lemma healthy_wp_SetDC:
  fixes prog::"'b \<Rightarrow> 'a prog" and S::"'a \<Rightarrow> 'b set"
  assumes healthy:  "\<And>x s. x \<in> S s \<Longrightarrow> healthy (wp (prog x))"
      and nonempty: "\<And>s. \<exists>x. x \<in> S s"
  shows "healthy (wp (SetDC prog S))" (is "healthy ?T")
proof(intro healthy_parts bounded_byI nnegI le_funI, simp_all only:wp_eval)
  fix b and P::"'a \<Rightarrow> real" and s::'a
  assume bP: "bounded_by b P" and nP: "nneg P"
  hence sP: "sound P" by(auto)

  from nonempty obtain x where xin: "x \<in> (\<lambda>a. wp (prog a) P s) ` S s" by(blast)
  moreover from sP and healthy
  have "\<forall>x\<in>(\<lambda>a. wp (prog a) P s) ` S s. 0 \<le> x" by(auto)
  ultimately have "Inf ((\<lambda>a. wp (prog a) P s) ` S s) \<le> x"
    by(intro cInf_lower bdd_belowI, auto)
  also from xin and healthy and sP and bP have "x \<le> b" by(blast)
  finally show "Inf ((\<lambda>a. wp (prog a) P s) ` S s) \<le> b" .

  from xin and sP and healthy
  show "0 \<le> Inf ((\<lambda>a. wp (prog a) P s) ` S s)" by(blast intro:cInf_greatest)
next
  fix P::"'a \<Rightarrow> real" and Q and s::'a
  assume sP: "sound P" and sQ: "sound Q" and le: "P \<tturnstile> Q"

  from nonempty obtain x where xin: "x \<in> (\<lambda>a. wp (prog a) P s) ` S s" by(blast)
  moreover from sP and healthy
  have "\<forall>x\<in>(\<lambda>a. wp (prog a) P s) ` S s. 0 \<le> x" by(auto)
  moreover
  have "\<forall>x\<in>(\<lambda>a. wp (prog a) Q s) ` S s. \<exists>y\<in>(\<lambda>a. wp (prog a) P s) ` S s. y \<le> x"
  proof(rule ballI, clarify, rule bexI)
    fix x and a assume ain: "a \<in> S s"
    with healthy and sP and sQ and le show "wp (prog a) P s \<le> wp (prog a) Q s"
      by(auto dest:mono_transD[OF healthy_monoD])
    from ain show "wp (prog a) P s \<in> (\<lambda>a. wp (prog a) P s) ` S s" by(simp)
  qed
  ultimately
  show "Inf ((\<lambda>a. wp (prog a) P s) ` S s) \<le> Inf ((\<lambda>a. wp (prog a) Q s) ` S s)"
    by(intro cInf_mono, blast+)
next
  fix P::"'a \<Rightarrow> real" and c::real and s::'a
  assume sP: "sound P" and pos: "0 \<le> c"
  from nonempty obtain x where xin: "x \<in> (\<lambda>a. wp (prog a) P s) ` S s" by(blast)
  have "c * Inf ((\<lambda>a. wp (prog a) P s) ` S s) =
        Inf ((*) c ` ((\<lambda>a. wp (prog a) P s) ` S s))" (is "?U = ?V")
  proof(rule antisym)
    show "?U \<le> ?V"
    proof(rule cInf_greatest)
      from nonempty show "(*) c ` (\<lambda>a. wp (prog a) P s) ` S s \<noteq> {}" by(auto)
      fix x assume "x \<in> (*) c ` (\<lambda>a. wp (prog a) P s) ` S s"
      then obtain y where yin: "y \<in> (\<lambda>a. wp (prog a) P s) ` S s" and rwx: "x = c * y" by(auto)
      have "Inf ((\<lambda>a. wp (prog a) P s) ` S s) \<le> y"
      proof(intro cInf_lower[OF yin] bdd_belowI)
        fix z assume zin: "z \<in> (\<lambda>a. wp (prog a) P s) ` S s"
        then obtain a where "a \<in> S s" and "z = wp (prog a) P s" by(auto)
        with sP show "0 \<le> z" by(auto dest:healthy)
      qed
      with pos rwx show "c * Inf ((\<lambda>a. wp (prog a) P s) ` S s) \<le> x" by(auto intro:mult_left_mono)
    qed
    show "?V \<le> ?U"
    proof(cases)
      assume cz: "c = 0"
      moreover {
        from nonempty obtain c where "c \<in> S s" by(auto)
        hence "\<exists>x. \<exists>xa\<in>S s. x = wp (prog xa) P s" by(auto)
      }
      ultimately show ?thesis by(simp add:image_def)
    next
      assume "c \<noteq> 0"
      from nonempty have "S s \<noteq> {}" by blast
      then have "inverse c * (INF x\<in>S s. c * wp (prog x) P s) \<le> (INF a\<in>S s. wp (prog a) P s)"
      proof (rule cINF_greatest)
        fix x
        assume "x \<in> S s"
        have "bdd_below ((\<lambda>x. c * wp (prog x) P s) ` S s)"
        proof (rule bdd_belowI [of _ 0])
          fix z
          assume "z \<in> (\<lambda>x. c * wp (prog x) P s) ` S s"
          then obtain b where "b \<in> S s" and rwz: "z = c * wp (prog b) P s" by auto
          with sP have "0 \<le> wp (prog b) P s" by (auto dest: healthy)
          with pos show "0 \<le> z" by (auto simp: rwz intro: mult_nonneg_nonneg)
        qed
        then have "(INF x\<in>S s. c * wp (prog x) P s) \<le> c * wp (prog x) P s"
        using \<open>x \<in> S s\<close> by (rule cINF_lower)
        with \<open>c \<noteq> 0\<close> show "inverse c * (INF x\<in>S s. c * wp (prog x) P s) \<le> wp (prog x) P s"
          by (simp add: mult_div_mono_left pos)
      qed
      with \<open>c \<noteq> 0\<close> have "inverse c * ?V \<le> inverse c * ?U"
        by (simp add: mult.assoc [symmetric] image_comp)
      with pos have "c * (inverse c * ?V) \<le> c * (inverse c * ?U)"
        by(auto intro:mult_left_mono)
      with \<open>c \<noteq> 0\<close> show ?thesis by (simp add:mult.assoc [symmetric])
    qed
  qed
  also have "... = Inf ((\<lambda>a. c * wp (prog a) P s) ` S s)"
    by (simp add: image_comp)
  also from sP and pos have "... = Inf ((\<lambda>a. wp (prog a) (\<lambda>s. c * P s) s) ` S s)"
    by(simp add:scalingD[OF healthy_scalingD, OF healthy] cong:image_cong)
  finally show "c * Inf ((\<lambda>a. wp (prog a) P s) ` S s) =
                Inf ((\<lambda>a. wp (prog a) (\<lambda>s. c * P s) s) ` S s)" .
qed

lemma nearly_healthy_wlp_SetDC:
  fixes prog::"'b \<Rightarrow> 'a prog" and S::"'a \<Rightarrow> 'b set"
  assumes healthy:  "\<And>x s. x \<in> S s \<Longrightarrow> nearly_healthy (wlp (prog x))"
      and nonempty: "\<And>s. \<exists>x. x \<in> S s"
  shows "nearly_healthy (wlp (SetDC prog S))" (is "nearly_healthy ?T")
proof(intro nearly_healthyI unitaryI2 bounded_byI nnegI le_funI, simp_all only:wp_eval)
  fix b and P::"'a \<Rightarrow> real" and s::'a
  assume uP: "unitary P"

  from nonempty obtain x where xin: "x \<in> (\<lambda>a. wlp (prog a) P s) ` S s" by(blast)
  moreover {
    from uP healthy
    have "\<forall>x\<in>(\<lambda>a. wlp (prog a) P) ` S s. unitary x" by(auto)
    hence "\<forall>x\<in>(\<lambda>a. wlp (prog a) P) ` S s. 0 \<le> x s" by(auto)
    hence "\<forall>y\<in>(\<lambda>a. wlp (prog a) P s) ` S s. 0 \<le> y" by(auto)
  }
  ultimately have "Inf ((\<lambda>a. wlp (prog a) P s) ` S s) \<le> x" by(intro cInf_lower bdd_belowI, auto)
  also from xin healthy uP have "x \<le> 1" by(blast)
  finally show "Inf ((\<lambda>a. wlp (prog a) P s) ` S s) \<le> 1" .

  from xin uP healthy
  show "0 \<le> Inf ((\<lambda>a. wlp (prog a) P s) ` S s)"
    by(blast dest!:unitary_sound[OF nearly_healthy_unitaryD[OF _ uP]]
             intro:cInf_greatest)
next
  fix P::"'a \<Rightarrow> real" and Q and s::'a
  assume uP: "unitary P" and uQ: "unitary Q" and le: "P \<tturnstile> Q"

  from nonempty obtain x where xin: "x \<in> (\<lambda>a. wlp (prog a) P s) ` S s" by(blast)
  moreover {
    from uP healthy
    have "\<forall>x\<in>(\<lambda>a. wlp (prog a) P) ` S s. unitary x" by(auto)
    hence "\<forall>x\<in>(\<lambda>a. wlp (prog a) P) ` S s. 0 \<le> x s" by(auto)
    hence "\<forall>y\<in>(\<lambda>a. wlp (prog a) P s) ` S s. 0 \<le> y" by(auto)
  }
  moreover
  have "\<forall>x\<in>(\<lambda>a. wlp (prog a) Q s) ` S s. \<exists>y\<in>(\<lambda>a. wlp (prog a) P s) ` S s. y \<le> x"
  proof(rule ballI, clarify, rule bexI)
    fix x and a assume ain: "a \<in> S s"
    from uP uQ le show "wlp (prog a) P s \<le> wlp (prog a) Q s"
      by(auto intro:le_funD[OF nearly_healthy_monoD[OF healthy, OF ain]])
    from ain show "wlp (prog a) P s \<in> (\<lambda>a. wlp (prog a) P s) ` S s" by(simp)
  qed
  ultimately
  show "Inf ((\<lambda>a. wlp (prog a) P s) ` S s) \<le> Inf ((\<lambda>a. wlp (prog a) Q s) ` S s)"
    by(intro cInf_mono, blast+)
qed

lemma healthy_wp_SetPC:
  fixes p::"'s \<Rightarrow> 'a \<Rightarrow> real"
  and   f::"'a \<Rightarrow> 's prog"
  assumes healthy: "\<And>a s. a \<in> supp (p s) \<Longrightarrow> healthy (wp (f a))"
      and sound: "\<And>s. sound (p s)"
      and sub_dist: "\<And>s. (\<Sum>a\<in>supp (p s). p s a) \<le> 1"
  shows "healthy (wp (SetPC f p))" (is "healthy ?X")
proof(intro healthy_parts bounded_byI nnegI le_funI, simp_all add:wp_eval)
  fix b and P::"'s \<Rightarrow> real" and s::'s
  assume bP: "bounded_by b P" and nP: "nneg P"
  hence sP: "sound P" by(auto)

  from sP and bP and healthy have "\<And>a s. a \<in> supp (p s) \<Longrightarrow> wp (f a) P s \<le> b"
    by(blast dest:healthy_bounded_byD)
  with sound have "(\<Sum>a\<in>supp (p s). p s a * wp (f a) P s) \<le> (\<Sum>a\<in>supp (p s). p s a * b)"
    by(blast intro:sum_mono mult_left_mono)
  also have "... = (\<Sum>a\<in>supp (p s). p s a) * b"
    by(simp add:sum_distrib_right)
  also {
    from bP and nP have "0 \<le> b" by(blast)
    with sub_dist have "(\<Sum>a\<in>supp (p s). p s a) * b \<le> 1 * b"
      by(rule mult_right_mono)
  }
  also have "1 * b = b" by(simp)
  finally show "(\<Sum>a\<in>supp (p s). p s a * wp (f a) P s) \<le> b" .

  show "0 \<le> (\<Sum>a\<in>supp (p s). p s a * wp (f a) P s)"
  proof(rule sum_nonneg [OF mult_nonneg_nonneg])
    fix x
    from sound show "0 \<le> p s x" by(blast)
    assume "x \<in> supp (p s)" with sP and healthy
    show "0 \<le> wp (f x) P s" by(blast)
  qed
next
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s
  assume s_P: "sound P" and s_Q: "sound Q" and ent: "P \<tturnstile> Q"
  with healthy have "\<And>a. a \<in> supp (p s) \<Longrightarrow> wp (f a) P s \<le> wp (f a) Q s"
    by(blast)
  with sound show "(\<Sum>a\<in>supp (p s). p s a * wp (f a) P s) \<le>
                   (\<Sum>a\<in>supp (p s). p s a * wp (f a) Q s)"
    by(blast intro:sum_mono mult_left_mono)
next
  fix P::"'s \<Rightarrow> real" and c::real and s::'s
  assume sound: "sound P" and pos: "0 \<le> c"
  have "c * (\<Sum>a\<in>supp (p s). p s a * wp (f a) P s) =
        (\<Sum>a\<in>supp (p s). p s a * (c * wp (f a) P s))"
       (is "?A = ?B")
    by(simp add:sum_distrib_left ac_simps)
  also from sound and pos and healthy
  have "... = (\<Sum>a\<in>supp (p s). p s a * wp (f a) (\<lambda>s. c * P s) s)"
    by(auto simp:scalingD[OF healthy_scalingD])
  finally show "?A = ..." .
qed

lemma nearly_healthy_wlp_SetPC:
  fixes p::"'s \<Rightarrow> 'a \<Rightarrow> real"
  and   f::"'a \<Rightarrow> 's prog"
  assumes healthy: "\<And>a s. a \<in> supp (p s) \<Longrightarrow> nearly_healthy (wlp (f a))"
      and sound: "\<And>s. sound (p s)"
      and sub_dist: "\<And>s. (\<Sum>a\<in>supp (p s). p s a) \<le> 1"
  shows "nearly_healthy (wlp (SetPC f p))" (is "nearly_healthy ?X")
proof(intro nearly_healthyI unitaryI2 bounded_byI nnegI le_funI, simp_all only:wp_eval)
  fix b and P::"'s \<Rightarrow> real" and s::'s
  assume uP: "unitary P"

  from uP healthy have "\<And>a. a \<in> supp (p s) \<Longrightarrow> unitary (wlp (f a) P)" by(auto)
  hence "\<And>a. a \<in> supp (p s) \<Longrightarrow> wlp (f a) P s \<le> 1" by(auto)
  with sound have "(\<Sum>a\<in>supp (p s). p s a * wlp (f a) P s) \<le> (\<Sum>a\<in>supp (p s). p s a * 1)"
    by(blast intro:sum_mono mult_left_mono)
  also have "... = (\<Sum>a\<in>supp (p s). p s a)"
    by(simp add:sum_distrib_right)
  also note sub_dist
  finally show "(\<Sum>a\<in>supp (p s). p s a * wlp (f a) P s) \<le> 1" .
  show "0 \<le> (\<Sum>a\<in>supp (p s). p s a * wlp (f a) P s)"
  proof(rule sum_nonneg [OF mult_nonneg_nonneg])
    fix x
    from sound show "0 \<le> p s x" by(blast)
    assume "x \<in> supp (p s)" with uP healthy
    show "0 \<le> wlp (f x) P s" by(blast)
  qed
next
  fix P::"'s expect" and Q::"'s expect" and s
  assume uP: "unitary P" and uQ: "unitary Q" and le: "P \<tturnstile> Q"
  hence "\<And>a. a \<in> supp (p s) \<Longrightarrow> wlp (f a) P s \<le> wlp (f a) Q s"
    by(blast intro:le_funD[OF nearly_healthy_monoD, OF healthy])
  with sound show "(\<Sum>a\<in>supp (p s). p s a * wlp (f a) P s) \<le>
                   (\<Sum>a\<in>supp (p s). p s a * wlp (f a) Q s)"
    by(blast intro:sum_mono mult_left_mono)
qed

lemma healthy_wp_Apply:
  "healthy (wp (Apply f))"
  unfolding Apply_def wp_def by(blast)

lemma nearly_healthy_wlp_Apply:
  "nearly_healthy (wlp (Apply f))"
  by(intro nearly_healthyI unitaryI2 nnegI bounded_byI, auto simp:o_def wp_eval)

lemma healthy_wp_Bind:
  fixes f::"'s \<Rightarrow> 'a"
  assumes hsub: "\<And>s. healthy (wp (p (f s)))"
  shows "healthy (wp (Bind f p))"
proof(intro healthy_parts nnegI bounded_byI le_funI, simp_all only:wp_eval)
  fix b and P::"'s expect" and s::'s
  assume bP: "bounded_by b P" and nP: "nneg P"
  with hsub have "bounded_by b (wp (p (f s)) P)" by(auto)
  thus "wp (p (f s)) P s \<le> b" by(auto)
  from bP nP hsub have "nneg (wp (p (f s)) P)" by(auto)
  thus "0 \<le> wp (p (f s)) P s" by(auto)
next
  fix P Q::"'s expect" and s::'s
  assume "sound P" "sound Q" "P \<tturnstile> Q"
  thus "wp (p (f s)) P s \<le> wp (p (f s)) Q s"
    by(rule le_funD[OF mono_transD, OF healthy_monoD, OF hsub])
next
  fix P::"'s expect" and c::real and s::'s
  assume "sound P" and "0 \<le> c"
  thus "c * wp (p (f s)) P s = wp (p (f s)) (\<lambda>s. c * P s) s"
    by(simp add:scalingD[OF healthy_scalingD, OF hsub])
qed

lemma nearly_healthy_wlp_Bind:
  fixes f::"'s \<Rightarrow> 'a"
  assumes hsub: "\<And>s. nearly_healthy (wlp (p (f s)))"
  shows "nearly_healthy (wlp (Bind f p))"
proof(intro nearly_healthyI unitaryI2 nnegI bounded_byI le_funI, simp_all only:wp_eval)
  fix P::"'s expect" and s::'s assume uP: "unitary P"
  with hsub have "unitary (wlp (p (f s)) P)" by(auto)
  thus "0 \<le> wlp (p (f s)) P s" "wlp (p (f s)) P s \<le> 1" by(auto)

  fix Q::"'s expect"
  assume "unitary Q" "P \<tturnstile> Q"
  with uP show "wlp (p (f s)) P s \<le> wlp (p (f s)) Q s"
    by(blast intro:le_funD[OF nearly_healthy_monoD, OF hsub])
qed

subsection \<open>Healthiness for Loops\<close>

lemma wp_loop_step_mono:
  fixes t u::"'s trans"
  assumes hb: "healthy (wp body)"
      and le: "le_trans t u"
      and ht: "\<And>P. sound P \<Longrightarrow> sound (t P)"
      and hu: "\<And>P. sound P \<Longrightarrow> sound (u P)"
  shows "le_trans (wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))
                  (wp (body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
proof(intro le_transI le_funI, simp add:wp_eval)
  fix P::"'s expect" and s::'s
  assume sP: "sound P"
  with le have "t P \<tturnstile> u P" by(auto)
  moreover from sP ht hu have "sound (t P)" "sound (u P)" by(auto)
  ultimately have "wp body (t P) s \<le> wp body (u P) s"
    by(auto intro:le_funD[OF mono_transD, OF healthy_monoD, OF hb])
  thus "\<guillemotleft>G\<guillemotright> s * wp body (t P) s \<le> \<guillemotleft>G\<guillemotright> s * wp body (u P) s "
    by(auto intro:mult_left_mono)
qed

lemma wlp_loop_step_mono:
  fixes t u::"'s trans"
  assumes mb: "nearly_healthy (wlp body)"
      and le: "le_utrans t u"
      and ht: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
      and hu: "\<And>P. unitary P \<Longrightarrow> unitary (u P)"
  shows "le_utrans (wlp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))
                   (wlp (body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))"
proof(intro le_utransI le_funI, simp add:wp_eval)
  fix P::"'s expect" and s::'s
  assume uP: "unitary P"
  with le have "t P \<tturnstile> u P" by(auto)
  moreover from uP ht hu have "unitary (t P)" "unitary (u P)" by(auto)
  ultimately have "wlp body (t P) s \<le> wlp body (u P) s"
    by(rule le_funD[OF nearly_healthy_monoD[OF mb]])
  thus "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s \<le> \<guillemotleft>G\<guillemotright> s * wlp body (u P) s "
    by(auto intro:mult_left_mono)
qed

text \<open>For each sound expectation, we have a pre fixed point of the loop body.
This lets us use the relevant fixed-point lemmas.\<close>
lemma lfp_loop_fp:
  assumes hb: "healthy (wp body)"
      and sP: "sound P"
  shows "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. bound_of P) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<tturnstile> \<lambda>s. bound_of P"
proof(rule le_funI)
  fix s
  from sP have "sound (\<lambda>s. bound_of P)" by(auto)
  moreover hence "bounded_by (bound_of P) (\<lambda>s. bound_of P)" by(auto)
  ultimately have "bounded_by (bound_of P) (wp body (\<lambda>s. bound_of P))"
    using hb by(auto)
  hence "wp body (\<lambda>s. bound_of P) s \<le> bound_of P" by(auto)
  moreover from sP have "P s \<le> bound_of P" by(auto)
  ultimately have "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>a. bound_of P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le>
                   \<guillemotleft>G\<guillemotright> s * bound_of P + (1 - \<guillemotleft>G\<guillemotright> s) * bound_of P"
    by(blast intro:add_mono mult_left_mono)
  thus "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>a. bound_of P) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> bound_of P"
    by(simp add:algebra_simps negate_embed)
qed

lemma lfp_loop_greatest:
  fixes P::"'s expect"
  assumes lb: "\<And>R. \<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<tturnstile> R \<Longrightarrow> sound R \<Longrightarrow> Q \<tturnstile> R"
      and hb: "healthy (wp body)"
      and sP: "sound P"
      and sQ: "sound Q"
  shows "Q \<tturnstile> lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
  using sP by(auto intro!:lfp_exp_greatest[OF lb sQ] sP lfp_loop_fp hb)

lemma lfp_loop_sound:
  fixes P::"'s expect"
  assumes hb: "healthy (wp body)"
      and sP: "sound P"
  shows "sound (lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s))"
  using assms by(auto intro!:lfp_exp_sound lfp_loop_fp)

lemma wlp_loop_step_unitary:
  fixes t u::"'s trans"
  assumes hb: "nearly_healthy (wlp body)"
      and ht: "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
      and uP: "unitary P"
  shows "unitary (wlp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P)"
proof(intro unitaryI2 nnegI bounded_byI, simp_all add:wp_eval)
  fix s::'s
  from ht uP have utP: "unitary (t P)" by(auto)
  with hb have "unitary (wlp body (t P))" by(auto)
  hence "0 \<le> wlp body (t P) s" by(auto)
  with uP show "0 \<le> \<guillemotleft> G \<guillemotright> s * wlp body (t P) s + (1 - \<guillemotleft> G \<guillemotright> s) * P s"
    by(auto intro!:add_nonneg_nonneg mult_nonneg_nonneg)
  from ht uP have "bounded_by 1 (t P)" by(auto)
  with utP hb have "bounded_by 1 (wlp body (t P))" by(auto)
  hence "wlp body (t P) s \<le> 1" by(auto)
  with uP have "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le> \<guillemotleft>G\<guillemotright> s * 1 + (1 - \<guillemotleft>G\<guillemotright> s) * 1"
    by(blast intro:add_mono mult_left_mono)
  also have "... = 1" by(simp)
  finally show "\<guillemotleft>G\<guillemotright> s * wlp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le> 1" .
qed

lemma wp_loop_step_sound:
  fixes t u::"'s trans"
  assumes hb: "healthy (wp body)"
      and ht: "\<And>P. sound P \<Longrightarrow> sound (t P)"
      and sP: "sound P"
  shows "sound (wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P)"
proof(intro soundI2 nnegI bounded_byI, simp_all add:wp_eval)
  fix s::'s
  from ht sP have stP: "sound (t P)" by(auto)
  with hb have "0 \<le> wp body (t P) s" by(auto)
  with sP show "0 \<le> \<guillemotleft> G \<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft> G \<guillemotright> s) * P s"
    by(auto intro!:add_nonneg_nonneg mult_nonneg_nonneg)

  from ht sP have "sound (t P)" by(auto)
  moreover hence "bounded_by (bound_of (t P)) (t P)" by(auto)
  ultimately have "wp body (t P) s \<le> bound_of (t P)" using hb by(auto)
  hence "wp body (t P) s \<le> max (bound_of P) (bound_of (t P))" by(auto)
  moreover {
    from sP have "P s \<le> bound_of P" by(auto)
    hence "P s \<le> max (bound_of P) (bound_of (t P))" by(auto)
  }
  ultimately
  have "\<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le>
        \<guillemotleft>G\<guillemotright> s * max (bound_of P) (bound_of (t P)) +
        (1 - \<guillemotleft>G\<guillemotright> s) * max (bound_of P) (bound_of (t P))"
    by(blast intro:add_mono mult_left_mono)
  also have "... = max (bound_of P) (bound_of (t P))" by(simp add:algebra_simps)
  finally show "\<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le>
                max (bound_of P) (bound_of (t P))" .
qed

text \<open>This gives the equivalence with the alternative definition for
  loops\citep[\S7, p.~198, footnote 23]{McIver_M_04}.\<close>

lemma wlp_Loop1:
  fixes body :: "'s prog"
  assumes unitary: "unitary P"
      and healthy: "nearly_healthy (wlp body)"
  shows "wlp (do G \<longrightarrow> body od) P =
   gfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
  (is "?X = gfp_exp (?Y P)")
proof -
  let "?Z u" = "(body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"
  show ?thesis
  proof(simp only: wp_eval, intro gfp_pulldown assms le_funI)
    fix u P
    show "wlp (?Z u) P = ?Y P (u P)" by(simp add:wp_eval negate_embed)
  next
    fix t::"'s trans" and P::"'s expect"
    assume ut: "\<And>Q. unitary Q \<Longrightarrow> unitary (t Q)" and uP: "unitary P"
    thus "unitary (wlp (?Z t) P)"
      by(rule wlp_loop_step_unitary[OF healthy])
  next
    fix P Q::"'s expect"
    assume uP: "unitary P" and uQ: "unitary Q"
    show "unitary (\<lambda>a. \<guillemotleft> G \<guillemotright> a * wlp body Q a + \<guillemotleft> \<N> G \<guillemotright> a * P a)"
    proof(intro unitaryI2 nnegI bounded_byI)
      fix s::'s
      from healthy uQ
      have "unitary (wlp body Q)" by(auto)
      hence "0 \<le> wlp body Q s" by(auto)
      with uP show "0 \<le> \<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
        by(auto intro!:add_nonneg_nonneg mult_nonneg_nonneg)

      from healthy uQ have "bounded_by 1 (wlp body Q)" by(auto)
      with uP have "\<guillemotleft>G\<guillemotright> s * wlp body Q s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<le> \<guillemotleft>G\<guillemotright> s * 1 + (1 - \<guillemotleft>G\<guillemotright> s) * 1"
        by(blast intro:add_mono mult_left_mono)
      also have "... = 1" by(simp)
      finally show "\<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> 1"
        by(simp add:negate_embed)
    qed
  next
    fix P Q R::"'s expect" and s::'s
    assume uP: "unitary P" and uQ: "unitary Q" and uR: "unitary R"
       and le: "Q \<tturnstile> R"
    hence "wlp body Q s \<le> wlp body R s"
      by(blast intro:le_funD[OF nearly_healthy_monoD, OF healthy])
    thus "\<guillemotleft>G\<guillemotright> s * wlp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le>
          \<guillemotleft>G\<guillemotright> s * wlp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
      by(auto intro:mult_left_mono)
  next
    fix t u::"'s trans"
    assume "le_utrans t u"
           "\<And>P. unitary P \<Longrightarrow> unitary (t P)"
           "\<And>P. unitary P \<Longrightarrow> unitary (u P)"
    thus "le_utrans (wlp (?Z t)) (wlp (?Z u))"
      by(blast intro!:wlp_loop_step_mono[OF healthy])
  qed
qed

lemma wp_loop_sound:
  assumes sP: "sound P"
      and hb: "healthy (wp body)"
  shows "sound (wp do G \<longrightarrow> body od P)"
proof(simp only: wp_eval, intro lfp_trans_sound sP)
  let ?v = "\<lambda>P s. bound_of P"
  show "le_trans (wp (body ;; Embed ?v \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) ?v"
    by(intro le_transI, simp add:wp_eval lfp_loop_fp[unfolded negate_embed] hb)
  show "\<And>P. sound P \<Longrightarrow> sound (?v P)" by(auto)
qed

text \<open>Likewise, we can rewrite strict loops.\<close>
lemma wp_Loop1:
  fixes body :: "'s prog"
  assumes sP: "sound P"
      and healthy: "healthy (wp body)"
  shows "wp (do G \<longrightarrow> body od) P =
   lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
  (is "?X = lfp_exp (?Y P)")
proof -
  let "?Z u" = "(body ;; Embed u \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)"
  show ?thesis
  proof(simp only: wp_eval, intro lfp_pulldown assms le_funI sP mono_transI)
    fix u P
    show "wp (?Z u) P = ?Y P (u P)" by(simp add:wp_eval negate_embed)
  next
    fix t::"'s trans" and P::"'s expect"
    assume ut: "\<And>Q. sound Q \<Longrightarrow> sound (t Q)" and uP: "sound P"
    with healthy show "sound (wp (?Z t) P)" by(rule wp_loop_step_sound)
  next
    fix P Q::"'s expect"
    assume sP: "sound P" and sQ: "sound Q"
    show "sound (\<lambda>a. \<guillemotleft> G \<guillemotright> a * wp body Q a + \<guillemotleft> \<N> G \<guillemotright> a * P a)"
    proof(intro soundI2 nnegI bounded_byI)
      fix s::'s
      from sQ have "nneg Q" "bounded_by (bound_of Q) Q" by(auto)
      with healthy have "bounded_by (bound_of Q) (wp body Q)" by(auto)
      hence "wp body Q s \<le> bound_of Q" by(auto)
      hence "wp body Q s \<le> max (bound_of P) (bound_of Q)" by(auto)
      moreover {
        from sP have "P s \<le> bound_of P" by(auto)
        hence "P s \<le> max (bound_of P) (bound_of Q)" by(auto)
      }
      ultimately have "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le>
                       \<guillemotleft>G\<guillemotright> s * max (bound_of P) (bound_of Q) +
                       \<guillemotleft>\<N> G\<guillemotright> s * max (bound_of P) (bound_of Q)"
        by(auto intro!:add_mono mult_left_mono)
      also have "... = max (bound_of P) (bound_of Q)" by(simp add:algebra_simps negate_embed)
      finally show "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> max (bound_of P) (bound_of Q)" .

      from sP have "0 \<le> P s" by(auto)
      moreover from sQ healthy have "0 \<le> wp body Q s" by(auto)
      ultimately show "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
        by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)
    qed
  next
    fix P Q R::"'s expect" and s::'s
    assume sQ: "sound Q" and sR: "sound R"
       and le: "Q \<tturnstile> R"
    hence "wp body Q s \<le> wp body R s"
      by(blast intro:le_funD[OF mono_transD, OF healthy_monoD, OF healthy])
    thus "\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le>
          \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s"
      by(auto intro:mult_left_mono)
  next
    fix t u::"'s trans"
    assume le: "le_trans t u"
       and st: "\<And>P. sound P \<Longrightarrow> sound (t P)"
       and su: "\<And>P. sound P \<Longrightarrow> sound (u P)"
    with healthy show "le_trans (wp (?Z t)) (wp (?Z u))"
      by(rule wp_loop_step_mono)
  next
    from healthy show "le_trans (wp (?Z (\<lambda>P s. bound_of P))) (\<lambda>P s. bound_of P)"
      by(intro le_transI, simp add:wp_eval lfp_loop_fp[unfolded negate_embed])
  next
    fix P::"'s expect" and s::'s
    assume "sound P"
    thus "sound (\<lambda>s. bound_of P)" by(auto)
  qed
qed

lemma nearly_healthy_wlp_loop:
  fixes body::"'s prog"
  assumes hb: "nearly_healthy (wlp body)"
  shows "nearly_healthy (wlp (do G \<longrightarrow> body od))"
proof(intro nearly_healthyI unitaryI2 nnegI2 bounded_byI2, simp_all add:wlp_Loop1 hb)
  fix P::"'s expect"
  assume uP: "unitary P"
  let "?X R" = "\<lambda>Q s. \<guillemotleft> G \<guillemotright> s * wlp body Q s + \<guillemotleft> \<N> G \<guillemotright> s * R s"

  show "\<lambda>s. 0 \<tturnstile> gfp_exp (?X P)"
  proof(rule gfp_exp_upperbound)
    show "unitary (\<lambda>s. 0::real)" by(auto)
    with hb have "unitary (wlp body (\<lambda>s. 0))" by(auto)
    with uP show "\<lambda>s. 0 \<tturnstile> (?X P (\<lambda>s. 0))"
      by(blast intro!:le_funI add_nonneg_nonneg mult_nonneg_nonneg)
  qed

  show "gfp_exp (?X P) \<tturnstile> \<lambda>s. 1"
  proof(rule gfp_exp_least)
    show "unitary (\<lambda>s. 1::real)" by(auto)
    fix Q::"'s expect"
    assume "unitary Q"
    thus "Q \<tturnstile> \<lambda>s. 1" by(auto)
  qed

  fix Q::"'s expect"
  assume uQ: "unitary Q" and le: "P \<tturnstile> Q"
  show "gfp_exp (?X P) \<tturnstile> gfp_exp (?X Q)"
  proof(rule gfp_exp_least)
    fix R::"'s expect" assume uR: "unitary R"
    assume fp: "R \<tturnstile> ?X P R"
    also from le have "... \<tturnstile> ?X Q R"
      by(blast intro:add_mono mult_left_mono le_funI)
    finally show "R \<tturnstile> gfp_exp (?X Q)"
      using uR by(auto intro:gfp_exp_upperbound)
  next
    show "unitary (gfp_exp (?X Q))"
    proof(rule gfp_exp_unitary, intro unitaryI2 nnegI bounded_byI)
      fix R::"'s expect" and s::'s assume uR: "unitary R"
      with hb have ubP: "unitary (wlp body R)" by(auto)
      with uQ show "0 \<le> \<guillemotleft> G \<guillemotright> s * wlp body R s + \<guillemotleft> \<N> G \<guillemotright> s * Q s"
        by(blast intro:add_nonneg_nonneg mult_nonneg_nonneg)

      from ubP uQ have "wlp body R s \<le> 1" "Q s \<le> 1" by(auto)
      hence "\<guillemotleft> G \<guillemotright> s * wlp body R s + \<guillemotleft> \<N> G \<guillemotright> s * Q s \<le> \<guillemotleft>G\<guillemotright> s * 1 + \<guillemotleft>\<N> G\<guillemotright> s * 1"
        by(blast intro:add_mono mult_left_mono)
      thus "\<guillemotleft> G \<guillemotright> s * wlp body R s + \<guillemotleft> \<N> G \<guillemotright> s * Q s \<le> 1"
        by(simp add:negate_embed)
    qed
  qed
qed

text \<open>We show healthiness by appealing to the properties of expectation fixed points, applied
to the alternative loop definition.\<close>
lemma healthy_wp_loop:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
  shows "healthy (wp (do G \<longrightarrow> body od))"
proof -
  let "?X P" = "(\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
  show ?thesis
  proof(intro healthy_parts bounded_byI2 nnegI2, simp_all add:wp_Loop1 hb soundI2 sound_intros)
    fix P::"'s expect" and c::real and s::'s
    assume sP: "sound P" and nnc: "0 \<le> c"
    show "c * (lfp_exp (?X P)) s = lfp_exp (?X (\<lambda>s. c * P s)) s"
    proof(cases)
      assume "c = 0" thus ?thesis
      proof(simp, intro antisym)
        from hb have fp: "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>_. 0) s \<tturnstile> \<lambda>s. 0" by(simp)
        hence "lfp_exp (\<lambda>P s. \<guillemotleft>G\<guillemotright> s * wp body P s) \<tturnstile> \<lambda>s. 0"
          by(auto intro:lfp_exp_lowerbound)
        thus "lfp_exp (\<lambda>P s. \<guillemotleft>G\<guillemotright> s * wp body P s) s \<le> 0" by(auto)
        have "\<lambda>s. 0 \<tturnstile> lfp_exp (\<lambda>P s. \<guillemotleft>G\<guillemotright> s * wp body P s)"
          by(auto intro:lfp_exp_greatest fp)
        thus "0 \<le> lfp_exp (\<lambda>P s. \<guillemotleft>G\<guillemotright> s * wp body P s) s" by(auto)
      qed
    next
      have onesided: "\<And>P c. c \<noteq> 0 \<Longrightarrow> 0 \<le> c \<Longrightarrow> sound P \<Longrightarrow>
            \<lambda>a. c * lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) a \<tturnstile>
                    lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * (c * P b))"
      proof -
        fix P::"'s expect" and c::real
        assume cnz: "c \<noteq> 0" and nnc: "0 \<le> c" and sP: "sound P"
        with nnc have cpos: "0 < c" by(auto)
        hence nnic: "0 \<le> inverse c" by(auto)
        show "\<lambda>a. c * lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) a \<tturnstile>
              lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * (c * P b))"
        proof(rule lfp_exp_greatest)
          fix Q::"'s expect"
          assume sQ: "sound Q"
             and fp: "\<lambda>b. \<guillemotleft>G\<guillemotright> b * wp body Q b + \<guillemotleft>\<N> G\<guillemotright> b * (c * P b) \<tturnstile> Q"
          hence "\<And>s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * (c * P s) \<le> Q s" by(auto)
          with nnic
          have "\<And>s. inverse c * (\<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * (c * P s)) \<le>
                     inverse c * Q s"
            by(auto intro:mult_left_mono)
          hence "\<And>s. \<guillemotleft>G\<guillemotright> s * (inverse c * wp body Q s) + (inverse c * c) * \<guillemotleft>\<N> G\<guillemotright> s * P s \<le>
                     inverse c * Q s"
            by(simp add:algebra_simps)
          hence "\<And>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. inverse c * Q s) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le>
                     inverse c * Q s"
            by(simp add:cnz scalingD[OF healthy_scalingD, OF hb sQ nnic])
          hence "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. inverse c * Q s) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<tturnstile>
                 \<lambda>s. inverse c * Q s" by(rule le_funI)
          moreover from nnic sQ have "sound (\<lambda>s. inverse c * Q s)"
            by(iprover intro:sound_intros)
          ultimately have "lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) \<tturnstile>
                           \<lambda>s. inverse c * Q s"
            by(rule lfp_exp_lowerbound)
          hence "\<And>s. lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) s \<le> inverse c * Q s"
            by(rule le_funD)
          with nnc
          have "\<And>s. c * lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) s \<le>
                     c * (inverse c * Q s)"
            by(auto intro:mult_left_mono)
          also from cnz have "\<And>s. ... s = Q s" by(simp)
          finally show "\<lambda>a. c * lfp_exp (\<lambda>a b. \<guillemotleft>G\<guillemotright> b * wp body a b + \<guillemotleft>\<N> G\<guillemotright> b * P b) a \<tturnstile> Q"
            by(rule le_funI)
        next
          from sP have "sound (\<lambda>s. bound_of P)" by(auto)
          with hb sP have "sound (lfp_exp (?X P))"
            by(blast intro:lfp_exp_sound lfp_loop_fp)
          with nnc show "sound (\<lambda>s. c * lfp_exp (?X P) s)"
            by(auto intro!:sound_intros)

          from hb sP nnc
          show "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. bound_of (\<lambda>s. c * P s)) s +
                    \<guillemotleft>\<N> G\<guillemotright> s * (c * P s) \<tturnstile> \<lambda>s. bound_of (\<lambda>s. c * P s)"
            by(iprover intro:lfp_loop_fp sound_intros)

          from sP nnc show "sound (\<lambda>s. bound_of (\<lambda>s. c * P s))"
            by(auto intro!:sound_intros)
        qed
      qed

      assume nzc: "c \<noteq> 0"
      show ?thesis (is "?X P c s = ?Y P c s")
      proof(rule fun_cong[where x=s], rule antisym)
        from nzc nnc sP show "?X P c \<tturnstile> ?Y P c" by(rule onesided)

        from nzc have nzic: "inverse c \<noteq> 0" by(auto)
        moreover with nnc have nnic: "0 \<le> inverse c" by(auto)
        moreover from nnc sP have scP: "sound (\<lambda>s. c * P s)" by(auto intro!:sound_intros)
        ultimately have "?X (\<lambda>s. c * P s) (inverse c) \<tturnstile> ?Y (\<lambda>s. c * P s) (inverse c)"
          by(rule onesided)
        with nnc have "\<lambda>s. c * ?X (\<lambda>s. c * P s) (inverse c) s \<tturnstile>
                       \<lambda>s. c * ?Y (\<lambda>s. c * P s) (inverse c) s"
          by(blast intro:mult_left_mono)
        with nzc show "?Y P c \<tturnstile> ?X P c" by(simp add:mult.assoc[symmetric])
      qed
    qed
  next
    fix P::"'s expect" and b::real
    assume bP: "bounded_by b P" and nP: "nneg P"
    show "lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s) \<tturnstile> \<lambda>s. b"
    proof(intro lfp_exp_lowerbound le_funI)
      fix s::'s
      from bP nP hb have "bounded_by b (wp body (\<lambda>s. b))" by(auto)
      hence "wp body (\<lambda>s. b) s \<le> b" by(auto)
      moreover from bP have "P s \<le> b" by(auto)
      ultimately have "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. b) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> \<guillemotleft>G\<guillemotright> s * b + \<guillemotleft>\<N> G\<guillemotright> s * b"
        by(auto intro!:add_mono mult_left_mono)
      also have "... = b" by(simp add:negate_embed field_simps)
      finally show "\<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. b) s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<le> b" .
      from bP nP have "0 \<le> b" by(auto)
      thus "sound (\<lambda>s. b)" by(auto)
    qed
    from hb bP nP show "\<lambda>s. 0 \<tturnstile> lfp_exp (\<lambda>Q s. \<guillemotleft>G\<guillemotright> s * wp body Q s + \<guillemotleft>\<N> G\<guillemotright> s * P s)"
      by(auto dest!:sound_nneg intro!:lfp_loop_greatest)
  next
    fix P Q::"'s expect"
    assume sP: "sound P" and sQ: "sound Q" and le: "P \<tturnstile> Q"
    show "lfp_exp (?X P) \<tturnstile> lfp_exp (?X Q)"
    proof(rule lfp_exp_greatest)
      fix R::"'s expect"
      assume sR: "sound R"
         and fp: "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * Q s \<tturnstile> R"
      from le have "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s \<tturnstile>
                    \<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * Q s"
        by(auto intro:le_funI add_left_mono mult_left_mono)
      also note fp
      finally show "lfp_exp (\<lambda>R s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s) \<tturnstile> R"
        using sR by(auto intro:lfp_exp_lowerbound)
    next
      from hb sP show "sound (lfp_exp (\<lambda>R s. \<guillemotleft>G\<guillemotright> s * wp body R s + \<guillemotleft>\<N> G\<guillemotright> s * P s))"
        by(rule lfp_loop_sound)
      from hb sQ show "\<lambda>s. \<guillemotleft>G\<guillemotright> s * wp body (\<lambda>s. bound_of Q) s +  \<guillemotleft>\<N> G\<guillemotright> s * Q s \<tturnstile> \<lambda>s. bound_of Q"
        by(rule lfp_loop_fp)
      from sQ show "sound (\<lambda>s. bound_of Q)" by(auto)
    qed
  qed
qed

text \<open>Use 'simp add:healthy\_intros' or 'blast intro:healthy\_intros' as
        appropriate to discharge healthiness side-contitions for primitive
        programs automatically.\<close>
lemmas healthy_intros =
  healthy_wp_Abort nearly_healthy_wlp_Abort healthy_wp_Skip   nearly_healthy_wlp_Skip
  healthy_wp_Seq   nearly_healthy_wlp_Seq   healthy_wp_PC     nearly_healthy_wlp_PC
  healthy_wp_DC    nearly_healthy_wlp_DC    healthy_wp_AC     nearly_healthy_wlp_AC
  healthy_wp_Embed nearly_healthy_wlp_Embed healthy_wp_Apply  nearly_healthy_wlp_Apply
  healthy_wp_SetDC nearly_healthy_wlp_SetDC healthy_wp_SetPC  nearly_healthy_wlp_SetPC
  healthy_wp_Bind  nearly_healthy_wlp_Bind  healthy_wp_repeat nearly_healthy_wlp_repeat
  healthy_wp_loop  nearly_healthy_wlp_loop

end
