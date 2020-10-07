(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Sublinearity\<close>

theory Sublinearity imports Embedding Healthiness LoopInduction begin

subsection \<open>Nonrecursive Primitives\<close>

text \<open>Sublinearity of non-recursive programs is generally straightforward, and follows from the
alebraic properties of the underlying operations, together with healthiness.\<close>

lemma sublinear_wp_Skip:
  "sublinear (wp Skip)"
  by(auto simp:wp_eval)

lemma sublinear_wp_Abort:
  "sublinear (wp Abort)"
  by(auto simp:wp_eval)

lemma sublinear_wp_Apply:
  "sublinear (wp (Apply f))"
  by(auto simp:wp_eval)

lemma sublinear_wp_Seq:
  fixes x::"'s prog"
  assumes slx: "sublinear (wp x)" and sly: "sublinear (wp y)"
      and hx:  "healthy (wp x)"   and hy:  "healthy (wp y)"
  shows "sublinear (wp (x ;; y))"
proof(rule sublinearI, simp add:wp_eval)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  and a::real and b::real and c::real
  assume sP: "sound P" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"

  with slx hy have "a * wp x (wp y P) s + b * wp x (wp y Q) s \<ominus> c \<le>
                    wp x (\<lambda>s. a * wp y P s + b * wp y Q s \<ominus> c) s"
    by(blast intro:sublinearD)
  also {      
    from sP sQ nna nnb nnc sly
    have "\<And>s. a * wp y P s + b * wp y Q s \<ominus> c \<le>
              wp y (\<lambda>s. a * P s + b * Q s \<ominus> c) s"
      by(blast intro:sublinearD)
    moreover from sP sQ hy
    have "sound (wp y P)" and "sound (wp y Q)" by(auto)
    moreover with nna nnb nnc
    have "sound (\<lambda>s. a * wp y P s + b * wp y Q s \<ominus> c)"
      by(auto intro!:sound_intros tminus_sound)
    moreover from sP sQ nna nnb nnc
    have "sound (\<lambda>s. a * P s + b * Q s \<ominus> c)"
      by(auto intro!:sound_intros tminus_sound)
    moreover with hy have "sound (wp y (\<lambda>s. a * P s + b * Q s \<ominus> c))"
      by(blast)
    ultimately
    have "wp x (\<lambda>s. a * wp y P s + b * wp y Q s \<ominus> c) s \<le>
          wp x (wp y (\<lambda>s. a * P s + b * Q s \<ominus> c)) s"
      by(blast intro!:le_funD[OF mono_transD[OF healthy_monoD[OF hx]]])
  }
  finally show "a * wp x (wp y P) s + b * wp x (wp y Q) s \<ominus> c \<le>
                wp x (wp y (\<lambda>s. a * P s + b * Q s \<ominus> c)) s" .
qed

lemma sublinear_wp_PC:
  fixes x::"'s prog"
  assumes slx: "sublinear (wp x)" and sly: "sublinear (wp y)"
      and uP: "unitary P"
  shows "sublinear (wp (x \<^bsub>P\<^esub>\<oplus> y))"
proof(rule sublinearI, simp add:wp_eval)
  fix R::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  and a::real and b::real and c::real
  assume sR: "sound R" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"

  have "a * (P s * wp x Q s + (1 - P s) * wp y Q s) +
        b * (P s * wp x R s + (1 - P s) * wp y R s) \<ominus> c =
        (P s * a * wp x Q s + (1 - P s) * a * wp y Q s) +
        (P s * b * wp x R s + (1 - P s) * b * wp y R s) \<ominus> c"
    by(simp add:field_simps)
  also
  have "... = (P s * a * wp x Q s + P s * b * wp x R s) +
              ((1 - P s) * a * wp y Q s + (1 - P s) * b * wp y R s) \<ominus> c"
    by(simp add:ac_simps)
  also
  have "... = P s * (a * wp x Q s + b * wp x R s) +
              (1 - P s) * (a * wp y Q s + b * wp y R s) \<ominus>
              (P s * c + (1 - P s) * c)"
    by(simp add:field_simps)
  also
  have "... \<le> (P s * (a * wp x Q s + b * wp x R s) \<ominus> P s * c) +
              ((1 - P s) * (a * wp y Q s + b * wp y R s) \<ominus> (1 - P s) * c)"
    by(rule tminus_add_mono)
  also {
      from uP have "0 \<le> P s" and "0 \<le> 1 - P s"
        by(auto simp:sign_simps)
      hence "(P s * (a * wp x Q s + b * wp x R s) \<ominus> P s * c) +
             ((1 - P s) * (a * wp y Q s + b * wp y R s) \<ominus> (1 - P s) * c) =
             P s * (a * wp x Q s + b * wp x R s \<ominus> c) +
             (1 - P s) * (a * wp y Q s + b * wp y R s  \<ominus> c)"
        by(simp add:tminus_left_distrib)
  }
  also {
    from sQ sR nna nnb nnc slx
    have "a * wp x Q s + b * wp x R s \<ominus> c \<le>
          wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast)
    moreover
    from sQ sR nna nnb nnc sly
    have "a * wp y Q s + b * wp y R s \<ominus> c \<le>
          wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast)
    moreover
    from uP have "0 \<le> P s" and "0 \<le> 1 - P s"
      by(auto simp:sign_simps)
    ultimately
    have "P s * (a * wp x Q s + b * wp x R s \<ominus> c) +
          (1 - P s) * (a * wp y Q s + b * wp y R s  \<ominus> c) \<le>
          P s * wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s +
          (1 - P s) * wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast intro:add_mono mult_left_mono)
  }
  finally
  show " a * (P s * wp x Q s + (1 - P s) * wp y Q s) +
         b * (P s * wp x R s + (1 - P s) * wp y R s) \<ominus> c \<le>
         P s * wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s +
         (1 - P s) * wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s" .
qed

lemma sublinear_wp_DC:
  fixes x::"'s prog"
  assumes slx: "sublinear (wp x)" and sly: "sublinear (wp y)"
  shows "sublinear (wp (x \<Sqinter> y))"
proof(rule sublinearI, simp only:wp_eval)
  fix R::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  and a::real and b::real and c::real
  assume sR: "sound R" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"

  from nna nnb
  have "a * min (wp x Q s) (wp y Q s) +
        b * min (wp x R s) (wp y R s) \<ominus> c =
        min (a * wp x Q s) (a * wp y Q s) +
        min (b * wp x R s) (b * wp y R s) \<ominus> c"
    by(simp add:min_distrib)
  also
  have "... \<le> min (a * wp x Q s + b * wp x R s)
                  (a * wp y Q s + b * wp y R s) \<ominus> c"
    by(auto intro!:tminus_left_mono)
  also
  have "... = min (a * wp x Q s + b * wp x R s \<ominus> c)
                  (a * wp y Q s + b * wp y R s \<ominus> c)"
    by(rule min_tminus_distrib)
  also {
    from slx sQ sR nna nnb nnc
    have "a * wp x Q s + b * wp x R s \<ominus> c \<le>
          wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast)
    moreover
    from sly sQ sR nna nnb nnc
    have "a * wp y Q s + b * wp y R s \<ominus> c \<le>
          wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast)
    ultimately
    have "min (a * wp x Q s + b * wp x R s \<ominus> c)
              (a * wp y Q s + b * wp y R s \<ominus> c) \<le>
          min (wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s)
              (wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s)"
      by(auto)
  }
  finally show "a * min (wp x Q s) (wp y Q s) +
                b * min (wp x R s) (wp y R s) \<ominus> c \<le>
               min (wp x (\<lambda>s. a * Q s + b * R s \<ominus> c) s)
                   (wp y (\<lambda>s. a * Q s + b * R s \<ominus> c) s)" .
qed

text \<open>As for continuity, we insist on a finite support.\<close>
lemma sublinear_wp_SetPC:
  fixes p::"'a \<Rightarrow> 's prog"
  assumes slp: "\<And>s a. a \<in> supp (P s) \<Longrightarrow> sublinear (wp (p a))"
      and sum: "\<And>s. (\<Sum>a\<in>supp (P s). P s a) \<le> 1"
      and nnP: "\<And>s a. 0 \<le> P s a"
      and fin: "\<And>s. finite (supp (P s))"
  shows "sublinear (wp (SetPC p P))"
proof(rule sublinearI, simp add:wp_eval)
  fix R::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  and a::real and b::real and c::real
  assume sR: "sound R" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"
  have "a * (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') Q s) +
        b * (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') R s) \<ominus> c =
        (\<Sum>a'\<in>supp (P s). P s a' * (a * wp (p a') Q s + b * wp (p a') R s)) \<ominus> c"
    by(simp add:field_simps sum_distrib_left sum.distrib)
  also have "... \<le>
             (\<Sum>a'\<in>supp (P s). P s a' * (a * wp (p a') Q s + b * wp (p a') R s)) \<ominus>
             (\<Sum>a'\<in>supp (P s). P s a' * c)"
  proof(rule tminus_right_antimono)
    have "(\<Sum>a'\<in>supp (P s). P s a' * c) \<le> (\<Sum>a'\<in>supp (P s). P s a') * c"
      by(simp add:sum_distrib_right)
    also from sum and nnc have "... \<le> 1 * c"
      by(rule mult_right_mono)
    finally show "(\<Sum>a'\<in>supp (P s). P s a' * c) \<le> c" by(simp)
  qed
  also from fin
  have "... \<le> (\<Sum>a'\<in>supp (P s). P s a' * (a * wp (p a') Q s + b * wp (p a') R s) \<ominus> P s a' * c)"
    by(blast intro:tminus_sum_mono)
  also have "... = (\<Sum>a'\<in>supp (P s). P s a' * (a * wp (p a') Q s + b * wp (p a') R s \<ominus> c))"
    by(simp add:nnP tminus_left_distrib)
  also {
    from slp sQ sR nna nnb nnc
    have "\<And>a'. a' \<in> supp (P s) \<Longrightarrow> a * wp (p a') Q s + b * wp (p a') R s \<ominus> c \<le>
                                    wp (p a') (\<lambda>s. a * Q s + b * R s \<ominus> c) s"
      by(blast)
    with nnP
    have "(\<Sum>a'\<in>supp (P s). P s a' * (a * wp (p a') Q s + b * wp (p a') R s \<ominus> c)) \<le>
          (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') (\<lambda>s. a * Q s + b * R s \<ominus> c) s)"
      by(blast intro:sum_mono mult_left_mono)
  }
  finally
  show "a * (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') Q s) +
        b * (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') R s) \<ominus> c \<le>
        (\<Sum>a'\<in>supp (P s). P s a' * wp (p a') (\<lambda>s. a * Q s + b * R s \<ominus> c) s)" .
qed

lemma sublinear_wp_SetDC:
  fixes p::"'a \<Rightarrow> 's prog"
  assumes slp: "\<And>s a. a \<in> S s \<Longrightarrow> sublinear (wp (p a))"
      and hp:  "\<And>s a. a \<in> S s \<Longrightarrow> healthy (wp (p a))"
      and ne:  "\<And>s. S s \<noteq> {}"
  shows "sublinear (wp (SetDC p S))"
proof(rule sublinearI, simp add:wp_eval, rule cInf_greatest)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s and x y
  and a::real and b::real and c::real
  assume sP: "sound P" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"

  from ne show "(\<lambda>pr. wp (p pr) (\<lambda>s. a * P s + b * Q s \<ominus> c) s) ` S s \<noteq> {}" by(auto)

  assume yin: "y \<in> (\<lambda>pr. wp (p pr) (\<lambda>s. a * P s + b * Q s \<ominus> c) s) ` S s"
  then obtain x where xin: "x \<in> S s" and rwy: "y = wp (p x) (\<lambda>s. a * P s + b * Q s \<ominus> c) s"
    by(auto)

  from xin hp sP nna
  have "a * Inf ((\<lambda>a. wp (p a) P s) ` S s) \<le> a * wp (p x) P s"
    by(intro mult_left_mono[OF cInf_lower] bdd_belowI[where m=0], blast+)
  moreover from xin hp sQ nnb
  have "b * Inf ((\<lambda>a. wp (p a) Q s) ` S s) \<le> b * wp (p x) Q s"
    by(intro mult_left_mono[OF cInf_lower] bdd_belowI[where m=0], blast+)
  ultimately
  have "a * Inf ((\<lambda>a. wp (p a) P s) ` S s) +
        b * Inf ((\<lambda>a. wp (p a) Q s) ` S s) \<ominus> c \<le>
        a * wp (p x) P s + b * wp (p x) Q s \<ominus> c"
    by(blast intro:tminus_left_mono add_mono)

  also from xin slp sP sQ nna nnb nnc
  have "... \<le> wp (p x) (\<lambda>s. a * P s + b * Q s \<ominus> c) s"
    by(blast)

  finally show "a * Inf ((\<lambda>a. wp (p a) P s) ` S s) + b * Inf ((\<lambda>a. wp (p a) Q s) ` S s) \<ominus> c \<le> y"
    by(simp add:rwy)
qed

lemma sublinear_wp_Embed:
  "sublinear t \<Longrightarrow> sublinear (wp (Embed t))"
  by(simp add:wp_eval)

lemma sublinear_wp_repeat:
  "\<lbrakk> sublinear (wp p); healthy (wp p) \<rbrakk> \<Longrightarrow> sublinear (wp (repeat n p))"
  by(induct n, simp_all add:sublinear_wp_Seq sublinear_wp_Skip healthy_wp_repeat)

lemma sublinear_wp_Bind:
  "\<lbrakk> \<And>s. sublinear (wp (a (f s))) \<rbrakk> \<Longrightarrow> sublinear (wp (Bind f a))"
  by(rule sublinearI, simp add:wp_eval, auto)

subsection \<open>Sublinearity for Loops\<close>

text \<open>We break the proof of sublinearity loops into separate proofs of sub-distributivity and
sub-additivity.  The first follows by transfinite induction.\<close>
lemma sub_distrib_wp_loop:
  fixes body::"'s prog"
  assumes sdb: "sub_distrib (wp body)"
      and hb:  "healthy (wp body)"
      and nhb: "nearly_healthy (wlp body)"
  shows "sub_distrib (wp (do G \<longrightarrow> body od))"
proof -
  have "\<forall>P s. sound P \<longrightarrow> wp (do G \<longrightarrow> body od) P s \<ominus> 1 \<le> 
                          wp (do G \<longrightarrow> body od) (\<lambda>s. P s \<ominus> 1) s"
  proof(rule loop_induct[OF hb nhb], safe)
    fix S::"('s trans \<times> 's trans) set" and P::"'s expect" and s::'s
    assume saS: "\<forall>x\<in>S. \<forall>P s. sound P \<longrightarrow> fst x P s \<ominus> 1 \<le> fst x (\<lambda>s. P s \<ominus> 1) s"
       and sP: "sound P"
       and fS: "\<forall>x\<in>S. feasible (fst x)"

    from sP have sPm: "sound (\<lambda>s. P s \<ominus> 1)" by(auto intro:tminus_sound)

    have nnSup: "\<And>s. 0 \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s"
    proof(cases "S={}", simp add:Sup_trans_def Sup_exp_def)
      fix s
      assume "S \<noteq> {}"
      then obtain x where xin: "x\<in>S" by(auto)
      with fS sPm have "0 \<le> fst x (\<lambda>s. P s \<ominus> 1) s" by(auto)
      also from xin fS sPm have "... \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s"
        by(auto intro!: le_funD[OF Sup_trans_upper2])
      finally show "?thesis s" .
    qed

    have "\<And>x s. fst x P s \<le> (fst x P s \<ominus> 1) + 1" by(simp add:tminus_def)
    also from saS sP
    have "\<And>x s. x\<in>S \<Longrightarrow> (fst x P s \<ominus> 1) + 1 \<le> fst x (\<lambda>s. P s \<ominus> 1) s + 1"
      by(auto intro:add_right_mono)
    also {
      from sP have "sound (\<lambda>s. P s \<ominus> 1)" by(auto intro:tminus_sound)
      with fS have "\<And>x s. x\<in>S \<Longrightarrow> fst x (\<lambda>s. P s \<ominus> 1) s + 1 \<le>
                                   Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s + 1"
        by(blast intro!: add_right_mono le_funD[OF Sup_trans_upper2])
    }
    finally have le: "\<And>s. \<forall>x\<in>S. fst x P s \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s + 1"
      by(auto)
    moreover from nnSup have nn: "\<And>s. 0 \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s + 1"
      by(auto intro:add_nonneg_nonneg)
    ultimately
    have leSup: "Sup_trans (fst ` S) P s \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s + 1"
      unfolding Sup_trans_def
      by(intro le_funD[OF Sup_exp_least], auto)

    show "Sup_trans (fst ` S) P s \<ominus> 1 \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s"
    proof(cases "Sup_trans (fst ` S) P s \<le> 1", simp_all add:nnSup)
      from leSup have "Sup_trans (fst ` S) P s - 1 \<le>
                       Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s + 1 - 1"
        by(auto)
      thus "Sup_trans (fst ` S) P s - 1 \<le> Sup_trans (fst ` S) (\<lambda>s. P s \<ominus> 1) s" by(simp)
    qed
  next
    fix t::"'s trans" and P::"'s expect" and s::'s
    assume IH: "\<forall>P s. sound P \<longrightarrow> t P s \<ominus> 1 \<le> t (\<lambda>a. P a \<ominus> 1) s"
       and ft: "feasible t"
       and sP: "sound P"

     from sP have "sound (\<lambda>s. P s \<ominus> 1)" by(auto intro:tminus_sound)
     with ft have s2: "sound (t (\<lambda>s. P s \<ominus> 1))" by(auto)
     from sP ft have "sound (t P)" by(auto)
     hence s3: "sound (\<lambda>s. t P s \<ominus> 1)" by(auto intro!:tminus_sound)

    show "wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) P s \<ominus> 1 \<le>
          wp (body ;; Embed t \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) (\<lambda>a. P a \<ominus> 1) s"
    proof(simp add:wp_eval)
      have "\<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<ominus> 1 =
            \<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<ominus> (\<guillemotleft>G\<guillemotright> s + (1 - \<guillemotleft>G\<guillemotright> s))"
        by(simp)
      also have "... \<le> (\<guillemotleft>G\<guillemotright> s * wp body (t P) s \<ominus> \<guillemotleft>G\<guillemotright> s) +
                        ((1 - \<guillemotleft>G\<guillemotright> s) * P s \<ominus> (1 - \<guillemotleft>G\<guillemotright> s))"
        by(rule tminus_add_mono)
      also have "... = \<guillemotleft>G\<guillemotright> s * (wp body (t P) s \<ominus> 1) + (1 - \<guillemotleft>G\<guillemotright> s) * (P s \<ominus> 1)"
        by(simp add:tminus_left_distrib)
      also {
        from ft sP have "wp body (t P) s \<ominus> 1 \<le> wp body (\<lambda>s. t P s \<ominus> 1) s"
          by(auto intro:sub_distribD[OF sdb])
        also {
          from IH sP have "\<lambda>s. t P s \<ominus> 1 \<tturnstile> t (\<lambda>s. P s \<ominus> 1)" by(auto)
          with sP ft s2 s3 have "wp body (\<lambda>s. t P s \<ominus> 1) s \<le> wp body (t (\<lambda>s. P s \<ominus> 1)) s"
            by(blast intro:le_funD[OF mono_transD, OF healthy_monoD, OF hb])
        }
        finally have "\<guillemotleft>G\<guillemotright> s * (wp body (t P) s \<ominus> 1) + (1 - \<guillemotleft>G\<guillemotright> s) * (P s \<ominus> 1) \<le>
                      \<guillemotleft>G\<guillemotright> s * wp body (t (\<lambda>s. P s \<ominus> 1)) s + (1 - \<guillemotleft>G\<guillemotright> s) * (P s \<ominus> 1)"
          by(auto intro:add_right_mono mult_left_mono)
      }
      finally show "\<guillemotleft>G\<guillemotright> s * wp body (t P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s \<ominus> 1 \<le>
                    \<guillemotleft>G\<guillemotright> s * wp body (t (\<lambda>s. P s \<ominus> 1)) s + (1 - \<guillemotleft>G\<guillemotright> s) * (P s \<ominus> 1)" .
    qed
  next
    fix t t'::"'s trans" and P::"'s expect" and s::'s
    assume IH: "\<forall>P s. sound P \<longrightarrow> t P s \<ominus> 1 \<le> t (\<lambda>a. P a \<ominus> 1) s"
       and eq: "equiv_trans t t'" and sP: "sound P"

    from sP have "t' P s \<ominus> 1 = t P s \<ominus> 1" by(simp add:equiv_transD[OF eq])
    also from sP IH have "... \<le> t (\<lambda>s. P s \<ominus> 1) s" by(auto)
    also {
      from sP have "sound (\<lambda>s. P s \<ominus> 1)" by(simp add:tminus_sound)
      hence "t (\<lambda>s. P s \<ominus> 1) s = t' (\<lambda>s. P s \<ominus> 1) s" by(simp add:equiv_transD[OF eq])
    }
    finally show "t' P s \<ominus> 1 \<le> t' (\<lambda>s. P s \<ominus> 1) s" .
  qed
  thus ?thesis by(auto intro!:sub_distribI)
qed

text \<open>For sub-additivity, we again use the limit-of-iterates characterisation.  Firstly, all
iterates are sublinear:\<close>
lemma sublinear_iterates:
  assumes hb: "healthy (wp body)"
      and sb: "sublinear (wp body)"
  shows "sublinear (iterates body G i)"
  by(induct i, auto intro!:sublinear_wp_PC sublinear_wp_Seq sublinear_wp_Skip sublinear_wp_Embed
                           assms healthy_intros iterates_healthy)

text \<open>From this, sub-additivity follows for the limit (i.e. the loop), by appealing to the
property at all steps.\<close>
lemma sub_add_wp_loop:
  fixes body::"'s prog"
  assumes sb: "sublinear (wp body)"
      and cb:  "bd_cts (wp body)"
      and hwp:  "healthy (wp body)"
  shows "sub_add (wp (do G \<longrightarrow> body od))"
proof
  fix P Q::"'s expect" and s::'s
  assume sP: "sound P" and sQ: "sound Q"

  from hwp cb sP have "(\<lambda>i. iterates body G i P s) \<longlonglongrightarrow> wp do G \<longrightarrow> body od P s"
    by(rule loop_iterates)
  moreover
  from hwp cb sQ have "(\<lambda>i. iterates body G i Q s) \<longlonglongrightarrow> wp do G \<longrightarrow> body od Q s"
    by(rule loop_iterates)
  ultimately
  have "(\<lambda>i. iterates body G i P s + iterates body G i Q s) \<longlonglongrightarrow>
        wp do G \<longrightarrow> body od P s + wp do G \<longrightarrow> body od Q s"
    by(rule tendsto_add)
  moreover {
    from sublinear_subadd[OF sublinear_iterates, OF hwp sb,
                          OF healthy_feasibleD[OF iterates_healthy, OF hwp]] sP sQ
    have "\<And>i. iterates body G i P s + iterates body G i Q s \<le> iterates body G i (\<lambda>s. P s + Q s) s"
      by(rule sub_addD)
  }
  moreover {
    from sP sQ have "sound (\<lambda>s. P s + Q s)" by(blast intro:sound_intros)
    with hwp cb have "(\<lambda>i. iterates body G i (\<lambda>s. P s + Q s) s) \<longlonglongrightarrow>
                           wp do G \<longrightarrow> body od (\<lambda>s. P s + Q s) s"
      by(blast intro:loop_iterates)
  }
  ultimately
  show "wp do G \<longrightarrow> body od P s + wp do G \<longrightarrow> body od Q s \<le> wp do G \<longrightarrow> body od (\<lambda>s. P s + Q s) s"
    by(blast intro:LIMSEQ_le)  
qed

lemma sublinear_wp_loop:
  fixes body::"'s prog"
  assumes hb:  "healthy (wp body)"
      and nhb: "nearly_healthy (wlp body)"
      and sb:  "sublinear (wp body)"
      and cb:  "bd_cts (wp body)"
  shows "sublinear (wp (do G \<longrightarrow> body od))"
   using sublinear_sub_distrib[OF sb] sublinear_subadd[OF sb]
         hb healthy_feasibleD[OF hb]
   by(iprover intro:sd_sa_sublinear[OF _ _ healthy_wp_loop[OF hb]]
                    sub_distrib_wp_loop sub_add_wp_loop assms)

lemmas sublinear_intros =
  sublinear_wp_Abort
  sublinear_wp_Skip
  sublinear_wp_Apply
  sublinear_wp_Seq
  sublinear_wp_PC
  sublinear_wp_DC
  sublinear_wp_SetPC
  sublinear_wp_SetDC
  sublinear_wp_Embed
  sublinear_wp_repeat
  sublinear_wp_Bind
  sublinear_wp_loop

end
