(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section \<open>Continuity\<close>

theory Continuity imports Healthiness begin

text \<open>We rely on one additional healthiness property, continuity, which is shown here seperately,
as its proof relies, in general, on healthiness.  It is only relevant when a program appears
in an inductive context i.e.~inside a loop.\<close>

text \<open>A continuous transformer preserves limits (or the suprema of ascending chains).\<close>
definition bd_cts :: "'s trans \<Rightarrow> bool"
where "bd_cts t = (\<forall>M. (\<forall>i. (M i \<tturnstile> M (Suc i)) \<and> sound (M i)) \<longrightarrow>
                       (\<exists>b. \<forall>i. bounded_by b (M i)) \<longrightarrow>
                       t (Sup_exp (range M)) = Sup_exp (range (t o M)))"

lemma bd_ctsD:
  "\<lbrakk> bd_cts t; \<And>i. M i \<tturnstile> M (Suc i); \<And>i. sound (M i); \<And>i. bounded_by b (M i) \<rbrakk> \<Longrightarrow>
   t (Sup_exp (range M)) = Sup_exp (range (t o M))"
  unfolding bd_cts_def by(auto)

lemma bd_ctsI:
  "(\<And>b M. (\<And>i. M i \<tturnstile> M (Suc i)) \<Longrightarrow> (\<And>i. sound (M i)) \<Longrightarrow> (\<And>i. bounded_by b (M i)) \<Longrightarrow>
         t (Sup_exp (range M)) = Sup_exp (range (t o M))) \<Longrightarrow> bd_cts t"
  unfolding bd_cts_def by(auto)

text \<open>A generalised property for transformers of transformers.\<close>
definition bd_cts_tr :: "('s trans \<Rightarrow> 's trans) \<Rightarrow> bool"
where "bd_cts_tr T = (\<forall>M. (\<forall>i. le_trans (M i) (M (Suc i)) \<and> feasible (M i)) \<longrightarrow>
                          equiv_trans (T (Sup_trans (M ` UNIV))) (Sup_trans ((T o M) ` UNIV)))"

lemma bd_cts_trD:
  "\<lbrakk> bd_cts_tr T; \<And>i. le_trans (M i) (M (Suc i)); \<And>i. feasible (M i) \<rbrakk> \<Longrightarrow>
   equiv_trans (T (Sup_trans (M ` UNIV))) (Sup_trans ((T o M) ` UNIV))"
  by(simp add:bd_cts_tr_def)

lemma bd_cts_trI:
  "(\<And>M. (\<And>i. le_trans (M i) (M (Suc i))) \<Longrightarrow> (\<And>i. feasible (M i)) \<Longrightarrow>
         equiv_trans (T (Sup_trans (M ` UNIV))) (Sup_trans ((T o M) ` UNIV))) \<Longrightarrow> bd_cts_tr T"
  by(simp add:bd_cts_tr_def)

subsection \<open>Continuity of Primitives\<close>

lemma cts_wp_Abort:
  "bd_cts (wp (Abort::'s prog))"
proof -
  have X: "range (\<lambda>(i::nat) (s::'s). 0) = {\<lambda>s. 0}" by(auto)
  show ?thesis by(intro bd_ctsI, simp add:wp_eval o_def Sup_exp_def X)
qed

lemma cts_wp_Skip:
  "bd_cts (wp Skip)"
  by(rule bd_ctsI, simp add:wp_def Skip_def o_def)

lemma cts_wp_Apply:
  "bd_cts (wp (Apply f))"
proof -
  have X: "\<And>M s. {P (f s) |P. P \<in> range M} = {P s |P. P \<in> range (\<lambda>i s. M i (f s))}" by(auto)
  show ?thesis by(intro bd_ctsI ext, simp add:wp_eval o_def Sup_exp_def X)
qed

lemma cts_wp_Bind:
  fixes a::"'a \<Rightarrow> 's prog"
  assumes ca: "\<And>s. bd_cts (wp (a (f s)))"
  shows "bd_cts (wp (Bind f a))"
proof(rule bd_ctsI)
  fix M::"nat \<Rightarrow> 's expect" and c::real
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)" and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by c (M i)"
  with bd_ctsD[OF ca]
  have "\<And>s. wp (a (f s)) (Sup_exp (range M)) =
            Sup_exp (range (wp (a (f s)) o M))"
    by(auto)
  moreover have "\<And>s. {fa s |fa. fa \<in> range (\<lambda>x. wp (a (f s)) (M x))} =
                      {fa s |fa. fa \<in> range (\<lambda>x s. wp (a (f s)) (M x) s)}"
    by(auto)
  ultimately show "wp (Bind f a) (Sup_exp (range M)) =
                   Sup_exp (range (wp (Bind f a) \<circ> M))"
    by(simp add:wp_eval o_def Sup_exp_def)
qed

text \<open>The first nontrivial proof.  We transform the suprema into limits, and appeal to the
continuity of the underlying operation (here infimum).  This is typical of the remainder of the
nonrecursive elements.\<close>
lemma cts_wp_DC:
  fixes a b::"'s prog"
  assumes ca: "bd_cts (wp a)"
      and cb: "bd_cts (wp b)"
      and ha: "healthy (wp a)"
      and hb: "healthy (wp b)"
  shows "bd_cts (wp (a \<Sqinter> b))"
proof(rule bd_ctsI, rule antisym)
  fix M::"nat \<Rightarrow> 's expect" and c::real
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)" and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by c (M i)"

  from ha hb have hab: "healthy (wp (a \<Sqinter> b))" by(rule healthy_intros)
  from bM have leSup: "\<And>i. M i \<tturnstile> Sup_exp (range M)" by(auto intro:Sup_exp_upper)
  from sM bM have sSup: "sound (Sup_exp (range M))" by(auto intro:Sup_exp_sound)

  show "Sup_exp (range (wp (a \<Sqinter> b) \<circ> M)) \<tturnstile> wp (a \<Sqinter> b) (Sup_exp (range M))"
  proof(rule Sup_exp_least, clarsimp, rule le_funI)
    fix i s
    from mono_transD[OF healthy_monoD[OF hab]] leSup sM sSup
    have "wp (a \<Sqinter> b) (M i) \<tturnstile> wp (a \<Sqinter> b) (Sup_exp (range M))" by(auto)
    thus "wp (a \<Sqinter> b) (M i) s \<le> wp (a \<Sqinter> b) (Sup_exp (range M)) s" by(auto)

    from hab sSup have "sound (wp (a \<Sqinter> b) (Sup_exp (range M)))" by(auto)
    thus "nneg (wp (a \<Sqinter> b) (Sup_exp (range M)))" by(auto)
  qed

  from sM bM ha have "\<And>i. bounded_by c (wp a (M i))" by(auto)
  hence baM: "\<And>i s. wp a (M i) s \<le> c" by(auto)
  from sM bM hb have "\<And>i. bounded_by c (wp b (M i))" by(auto)
  hence bbM: "\<And>i s. wp b (M i) s \<le> c" by(auto)

  show "wp (a \<Sqinter> b) (Sup_exp (range M)) \<tturnstile> Sup_exp (range (wp (a \<Sqinter> b) \<circ> M))"
  proof(simp add:wp_eval o_def, rule le_funI)
    fix s::'s
    from bd_ctsD[OF ca, of M, OF chain sM bM] bd_ctsD[OF cb, of M, OF chain sM bM]
    have "min (wp a (Sup_exp (range M)) s) (wp b (Sup_exp (range M)) s) =
          min (Sup_exp (range (wp a o M)) s) (Sup_exp (range (wp b o M)) s)" by(simp)
    also {
      have "{f s |f. f \<in> range (\<lambda>x. wp a (M x))} = range (\<lambda>i. wp a (M i) s)"
           "{f s |f. f \<in> range (\<lambda>x. wp b (M x))} = range (\<lambda>i. wp b (M i) s)"
        by(auto)
      hence "min (Sup_exp (range (wp a o M)) s) (Sup_exp (range (wp b o M)) s) =
            min (Sup (range (\<lambda>i. wp a (M i) s))) (Sup (range (\<lambda>i. wp b (M i) s)))"
        by(simp add:Sup_exp_def o_def)
    }
    also {
      have "(\<lambda>i. wp a (M i) s) \<longlonglongrightarrow> Sup (range (\<lambda>i. wp a (M i) s))"
      proof(rule increasing_LIMSEQ)
        fix n
        from mono_transD[OF healthy_monoD, OF ha] sM chain
        show "wp a (M n) s \<le> wp a (M (Suc n)) s" by(auto intro:le_funD)
        from baM show "wp a (M n) s \<le> Sup (range (\<lambda>i. wp a (M i) s))"
          by(intro cSup_upper bdd_aboveI, auto)

        fix e::real assume pe: "0 < e"
        from baM have cSup: "Sup (range (\<lambda>i. wp a (M i) s)) \<in> closure (range (\<lambda>i. wp a (M i) s))"
          by(blast intro:closure_contains_Sup)
        with pe obtain y where yin: "y \<in> (range (\<lambda>i. wp a (M i) s))"
                          and dy: "dist y (Sup (range (\<lambda>i. wp a (M i) s))) < e"
          by(blast dest:iffD1[OF closure_approachable])
        from yin obtain i where "y = wp a (M i) s" by(auto)
        with dy have "dist (wp a (M i) s) (Sup (range (\<lambda>i. wp a (M i) s))) < e"
          by(simp)
        moreover from baM have "wp a (M i) s \<le> Sup (range (\<lambda>i. wp a (M i) s))"
          by(intro cSup_upper bdd_aboveI, auto)
        ultimately have "Sup (range (\<lambda>i. wp a (M i) s)) \<le> wp a (M i) s + e"
          by(simp add:dist_real_def)
        thus "\<exists>i. Sup (range (\<lambda>i. wp a (M i) s)) \<le> wp a (M i) s + e" by(auto)
      qed
      moreover
      have "(\<lambda>i. wp b (M i) s) \<longlonglongrightarrow> Sup (range (\<lambda>i. wp b (M i) s))"
      proof(rule increasing_LIMSEQ)
        fix n
        from mono_transD[OF healthy_monoD, OF hb] sM chain
        show "wp b (M n) s \<le> wp b (M (Suc n)) s" by(auto intro:le_funD)
        from bbM show "wp b (M n) s \<le> Sup (range (\<lambda>i. wp b (M i) s))"
          by(intro cSup_upper bdd_aboveI, auto)

        fix e::real assume pe: "0 < e"
        from bbM have cSup: "Sup (range (\<lambda>i. wp b (M i) s)) \<in> closure (range (\<lambda>i. wp b (M i) s))"
          by(blast intro:closure_contains_Sup)
        with pe obtain y where yin: "y \<in> (range (\<lambda>i. wp b (M i) s))"
                          and dy: "dist y (Sup (range (\<lambda>i. wp b (M i) s))) < e"
          by(blast dest:iffD1[OF closure_approachable])
        from yin obtain i where "y = wp b (M i) s" by(auto)
        with dy have "dist (wp b (M i) s) (Sup (range (\<lambda>i. wp b (M i) s))) < e"
          by(simp)
        moreover from bbM have "wp b (M i) s \<le> Sup (range (\<lambda>i. wp b (M i) s))"
          by(intro cSup_upper bdd_aboveI, auto)
        ultimately have "Sup (range (\<lambda>i. wp b (M i) s)) \<le> wp b (M i) s + e"
          by(simp add:dist_real_def)
        thus "\<exists>i. Sup (range (\<lambda>i. wp b (M i) s)) \<le> wp b (M i) s + e" by(auto)
      qed
      ultimately have "(\<lambda>i. min (wp a (M i) s) (wp b (M i) s)) \<longlonglongrightarrow>
                       min (Sup (range (\<lambda>i. wp a (M i) s))) (Sup (range (\<lambda>i. wp b (M i) s)))"
        by(rule tendsto_min)
      moreover have "bdd_above (range (\<lambda>i. min (wp a (M i) s) (wp b (M i) s)))"
      proof(intro bdd_aboveI, clarsimp)
        fix i
        have "min (wp a (M i) s) (wp b (M i) s) \<le> wp a (M i) s" by(auto)
        also {
          from ha sM bM have "bounded_by c (wp a (M i))" by(auto)
          hence "wp a (M i) s \<le>  c" by(auto)
        }
        finally show "min (wp a (M i) s) (wp b (M i) s) \<le> c" .
      qed
      ultimately
      have "min (Sup (range (\<lambda>i. wp a (M i) s))) (Sup (range (\<lambda>i. wp b (M i) s))) \<le>
            Sup (range (\<lambda>i. min (wp a (M i) s) (wp b (M i) s)))"
        by(blast intro:LIMSEQ_le_const2 cSup_upper min.mono[OF baM bbM])
    }
    also {
      have "range (\<lambda>i. min (wp a (M i) s) (wp b (M i) s)) =
            {f s |f. f \<in> range (\<lambda>i s. min (wp a (M i) s) (wp b (M i) s))}"
        by(auto)
      hence "Sup (range (\<lambda>i. min (wp a (M i) s) (wp b (M i) s))) =
           Sup_exp (range (\<lambda>i s. min (wp a (M i) s) (wp b (M i) s))) s"
        by (simp add: Sup_exp_def cong del: SUP_cong_simp)
    }
    finally show "min (wp a (Sup_exp (range M)) s) (wp b (Sup_exp (range M)) s) \<le>
                  Sup_exp (range (\<lambda>i s. min (wp a (M i) s) (wp b (M i) s))) s" .
  qed
qed

lemma cts_wp_Seq:
  fixes a b::"'s prog"
  assumes ca: "bd_cts (wp a)"
      and cb: "bd_cts (wp b)"
      and hb: "healthy (wp b)"
  shows "bd_cts (wp (a ;; b))"
proof(rule bd_ctsI, simp add:o_def wp_eval)
  fix M::"nat \<Rightarrow> 's expect" and c::real
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)" and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by c (M i)"
  hence "wp a (wp b (Sup_exp (range M))) = wp a (Sup_exp (range (wp b o M)))"
    by(subst bd_ctsD[OF cb], auto)
  also {
    from sM hb have "\<And>i. sound ((wp b o M) i)" by(auto)
    moreover from chain sM
    have "\<And>i. (wp b o M) i \<tturnstile> (wp b o M) (Suc i)"
      by(auto intro:mono_transD[OF healthy_monoD, OF hb])
    moreover from sM bM hb have "\<And>i. bounded_by c ((wp b o M) i)" by(auto)
    ultimately have "wp a (Sup_exp (range (wp b o M))) =
                     Sup_exp (range (wp a o (wp b o M)))"
      by(subst bd_ctsD[OF ca], auto)
  }
  also have "Sup_exp (range (wp a o (wp b o M))) =
             Sup_exp (range (\<lambda>i. wp a (wp b (M i))))"
    by(simp add:o_def)
  finally show "wp a (wp b (Sup_exp (range M))) =
                Sup_exp (range (\<lambda>i. wp a (wp b (M i))))" .
qed

lemma cts_wp_PC:
  fixes a b::"'s prog"
  assumes ca: "bd_cts (wp a)"
      and cb: "bd_cts (wp b)"
      and ha: "healthy (wp a)"
      and hb: "healthy (wp b)"
      and up: "unitary p"
  shows "bd_cts (wp (PC a p b))"
proof(rule bd_ctsI, rule ext, simp add:o_def wp_eval)
  fix M::"nat \<Rightarrow> 's expect" and c::real and s::'s
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)" and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by c (M i)"

  from sM have "\<And>i. nneg (M i)" by(auto)
  with bM have nc: "0 \<le> c" by(auto)

  from chain sM bM have "wp a (Sup_exp (range M)) = Sup_exp (range (wp a o M))"
    by(rule bd_ctsD[OF ca])
  hence "wp a (Sup_exp (range M)) s = Sup_exp (range (wp a o M)) s"
    by(simp)
  also {
    have "{f s |f. f \<in> range (\<lambda>x. wp a (M x))} = range (\<lambda>i. wp a (M i) s)"
      by(auto)
    hence "Sup_exp (range (wp a o M)) s = Sup (range (\<lambda>i. wp a (M i) s))"
      by(simp add:Sup_exp_def o_def)
  }
  finally have "p s * wp a (Sup_exp (range M)) s =
                p s * Sup (range (\<lambda>i. wp a (M i) s))" by(simp)
  also have "... = Sup {p s * x |x. x \<in> range (\<lambda>i. wp a (M i) s)}"
  proof(rule cSup_mult, blast, clarsimp)
    from up show "0 \<le> p s" by(auto)
    fix i
    from sM bM ha have "bounded_by c (wp a (M i))" by(auto)
    thus "wp a (M i) s \<le> c" by(auto)
  qed
  also {
    have "{p s * x |x. x \<in> range (\<lambda>i. wp a (M i) s)} = range (\<lambda>i. p s * wp a (M i) s)"
      by(auto)
    hence "Sup {p s * x |x. x \<in> range (\<lambda>i. wp a (M i) s)} =
           Sup (range (\<lambda>i. p s * wp a (M i) s))" by(simp)
  }
  finally have "p s * wp a (Sup_exp (range M)) s = Sup (range (\<lambda>i. p s * wp a (M i) s))" .
  moreover {
    from chain sM bM have "wp b (Sup_exp (range M)) = Sup_exp (range (wp b o M))"
      by(rule bd_ctsD[OF cb])
    hence "wp b (Sup_exp (range M)) s = Sup_exp (range (wp b o M)) s"
      by(simp)
    also {
      have "{f s |f. f \<in> range (\<lambda>x. wp b (M x))} = range (\<lambda>i. wp b (M i) s)"
        by(auto)
      hence "Sup_exp (range (wp b o M)) s = Sup (range (\<lambda>i. wp b (M i) s))"
        by(simp add:Sup_exp_def o_def)
    }
    finally have "(1 - p s) * wp b (Sup_exp (range M)) s =
                  (1 - p s) * Sup (range (\<lambda>i. wp b (M i) s))" by(simp)
    also have "... = Sup {(1 - p s) * x |x. x \<in> range (\<lambda>i. wp b (M i) s)}"
    proof(rule cSup_mult, blast, clarsimp)
      from up show "0 \<le> 1 - p s"
        by auto
      fix i
      from sM bM hb have "bounded_by c (wp b (M i))" by(auto)
      thus "wp b (M i) s \<le> c" by(auto)
    qed
    also {
      have "{(1 - p s) * x |x. x \<in> range (\<lambda>i. wp b (M i) s)} =
            range (\<lambda>i. (1 - p s) * wp b (M i) s)"
        by(auto)
      hence "Sup {(1 - p s) * x |x. x \<in> range (\<lambda>i. wp b (M i) s)} =
             Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))" by(simp)
    }
    finally have "(1 - p s) * wp b (Sup_exp (range M)) s =
                  Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))" .
  }
  ultimately
  have "p s * wp a (Sup_exp (range M)) s + (1 - p s) * wp b (Sup_exp (range M)) s =
        Sup (range (\<lambda>i. p s * wp a (M i) s)) + Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
    by(simp)
  also {
    from bM sM ha have "\<And>i. bounded_by c (wp a (M i))" by(auto)
    hence "\<And>i. wp a (M i) s \<le> c" by(auto)
    moreover from up have "0 \<le> p s" by(auto)
    ultimately have "\<And>i. p s * wp a (M i) s \<le> p s * c" by(auto intro:mult_left_mono)
    also from up nc have "p s * c \<le> 1 * c" by(blast intro:mult_right_mono)
    also have "... = c" by(simp)
    finally have baM: "\<And>i. p s * wp a (M i) s \<le> c" .

    have lima: "(\<lambda>i. p s * wp a (M i) s) \<longlonglongrightarrow> Sup (range (\<lambda>i. p s * wp a (M i) s))"
    proof(rule increasing_LIMSEQ)
      fix n
      from sM chain healthy_monoD[OF ha] have "wp a (M n) \<tturnstile> wp a (M (Suc n))"
        by(auto)
      with up show "p s * wp a (M n) s \<le> p s * wp a (M (Suc n)) s"
        by(blast intro:mult_left_mono)
      from baM show "p s * wp a (M n) s \<le> Sup (range (\<lambda>i. p s * wp a (M i) s))"
        by(intro cSup_upper bdd_aboveI, auto)
    next
      fix e::real
      assume pe: "0 < e"
      from baM have "Sup (range (\<lambda>i. p s * wp a (M i) s)) \<in>
                     closure (range (\<lambda>i. p s * wp a (M i) s))"
        by(blast intro:closure_contains_Sup)
      thm closure_approachable
      with pe obtain y where yin: "y \<in> range (\<lambda>i. p s * wp a (M i) s)"
                         and dy: "dist y (Sup (range (\<lambda>i. p s * wp a (M i) s))) < e"
        by(blast dest:iffD1[OF closure_approachable])
      from yin obtain i where "y = p s * wp a (M i) s" by(auto)
      with dy have "dist (p s * wp a (M i) s) (Sup (range (\<lambda>i. p s * wp a (M i) s))) < e"
        by(simp)
      moreover from baM have "p s * wp a (M i) s \<le> Sup (range (\<lambda>i. p s * wp a (M i) s))"
        by(intro cSup_upper bdd_aboveI, auto)
      ultimately have "Sup (range (\<lambda>i. p s * wp a (M i) s)) \<le> p s * wp a (M i) s + e"
        by(simp add:dist_real_def)
      thus "\<exists>i. Sup (range (\<lambda>i. p s * wp a (M i) s)) \<le> p s * wp a (M i) s + e" by(auto)
    qed

    from bM sM hb have "\<And>i. bounded_by c (wp b (M i))" by(auto)
    hence "\<And>i. wp b (M i) s \<le> c" by(auto)
    moreover from up have "0 \<le> (1 - p s)"
      by auto
    ultimately have "\<And>i. (1 - p s) * wp b (M i) s \<le> (1 - p s) * c" by(auto intro:mult_left_mono)
    also {
      from up have "1 - p s \<le> 1" by(auto)
      with nc have "(1 - p s) * c \<le> 1 * c" by(blast intro:mult_right_mono)
    }
    also have "1 * c = c" by(simp)
    finally have bbM: "\<And>i. (1 - p s) * wp b (M i) s \<le> c" .

    have limb: "(\<lambda>i. (1 - p s) * wp b (M i) s) \<longlonglongrightarrow> Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
    proof(rule increasing_LIMSEQ)
      fix n
      from sM chain healthy_monoD[OF hb] have "wp b (M n) \<tturnstile> wp b (M (Suc n))"
        by(auto)
      moreover from up have "0 \<le> 1 - p s"
        by auto
      ultimately show "(1 - p s) * wp b (M n) s \<le> (1 - p s) * wp b (M (Suc n)) s"
        by(blast intro:mult_left_mono)
      from bbM show "(1 - p s) * wp b (M n) s \<le> Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
        by(intro cSup_upper bdd_aboveI, auto)
    next
      fix e::real
      assume pe: "0 < e"
      from bbM have "Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s)) \<in>
                     closure (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
        by(blast intro:closure_contains_Sup)
      with pe obtain y where yin: "y \<in> range (\<lambda>i. (1 - p s) * wp b (M i) s)"
                         and dy: "dist y (Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))) < e"
        by(blast dest:iffD1[OF closure_approachable])
      from yin obtain i where "y = (1 - p s) * wp b (M i) s" by(auto)
      with dy have "dist ((1 - p s) * wp b (M i) s)
                         (Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))) < e"
        by(simp)
      moreover from bbM
      have "(1 - p s) * wp b (M i) s \<le> Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
        by(intro cSup_upper bdd_aboveI, auto)
      ultimately have "Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s)) \<le> (1 - p s) * wp b (M i) s + e"
        by(simp add:dist_real_def)
      thus "\<exists>i. Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s)) \<le> (1 - p s) * wp b (M i) s + e" by(auto)
    qed

    from lima limb have "(\<lambda>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s) \<longlonglongrightarrow>
      Sup (range (\<lambda>i. p s * wp a (M i) s)) + Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s))"
      by(rule tendsto_add)
    moreover from add_mono[OF baM bbM]
    have "\<And>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s \<le>
                       Sup (range (\<lambda>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s))"
      by(intro cSup_upper bdd_aboveI, auto)
    ultimately have "Sup (range (\<lambda>i. p s * wp a (M i) s)) +
                     Sup (range (\<lambda>i. (1 - p s) * wp b (M i) s)) \<le>
                     Sup (range (\<lambda>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s))"
      by(blast intro: LIMSEQ_le_const2)
  }
  also {
    have "range (\<lambda>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s) =
          {f s |f. f \<in> range (\<lambda>x s. p s * wp a (M x) s + (1 - p s) * wp b (M x) s)}"
      by(auto)
    hence "Sup (range (\<lambda>i. p s * wp a (M i) s + (1 - p s) * wp b (M i) s)) =
           Sup_exp (range (\<lambda>x s. p s * wp a (M x) s + (1 - p s) * wp b (M x) s)) s"
      by (simp add: Sup_exp_def cong del: SUP_cong_simp)
  }
  finally
  have "p s * wp a (Sup_exp (range M)) s + (1 - p s) * wp b (Sup_exp (range M)) s \<le>
        Sup_exp (range (\<lambda>i s. p s * wp a (M i) s + (1 - p s) * wp b (M i) s)) s" .
  moreover
  have "Sup_exp (range (\<lambda>i s. p s * wp a (M i) s + (1 - p s) * wp b (M i) s)) s \<le>
        p s * wp a (Sup_exp (range M)) s + (1 - p s) * wp b (Sup_exp (range M)) s"
  proof(rule le_funD[OF Sup_exp_least], clarsimp, rule le_funI)
    fix i::nat and s::'s
    from bM have leSup: "M i \<tturnstile> Sup_exp (range M)"
      by(blast intro: Sup_exp_upper)
    moreover from sM bM have sSup: "sound (Sup_exp (range M))"
      by(auto intro:Sup_exp_sound)
    moreover note healthy_monoD[OF ha] sM
    ultimately have "wp a (M i) \<tturnstile> wp a (Sup_exp (range M))" by(auto)
    hence "wp a (M i) s \<le> wp a (Sup_exp (range M)) s" by(auto)
    moreover {
      from leSup sSup healthy_monoD[OF hb] sM
      have "wp b (M i) \<tturnstile> wp b (Sup_exp (range M))" by(auto)
      hence "wp b (M i) s \<le> wp b (Sup_exp (range M)) s" by(auto)
    }
    moreover from up have "0 \<le> p s" "0 \<le> 1 - p s"
      by auto
    ultimately
    show "p s * wp a (M i) s + (1 - p s) * wp b (M i) s \<le>
          p s * wp a (Sup_exp (range M)) s + (1 - p s) * wp b (Sup_exp (range M)) s"
      by(blast intro:add_mono mult_left_mono)

    from sSup ha hb have "sound (wp a (Sup_exp (range M)))"
                         "sound (wp b (Sup_exp (range M)))"
      by(auto)
    hence "\<And>s. 0 \<le> wp a (Sup_exp (range M)) s" "\<And>s. 0 \<le> wp b (Sup_exp (range M)) s"
      by(auto)
    moreover from up have "\<And>s. 0 \<le> p s" "\<And>s. 0 \<le> 1 - p s"
      by auto
    ultimately show "nneg (\<lambda>c. p c * wp a (Sup_exp (range M)) c +
                          (1 - p c) * wp b (Sup_exp (range M)) c)"
      by(blast intro:add_nonneg_nonneg mult_nonneg_nonneg)
  qed
  ultimately show "p s * wp a (Sup_exp (range M)) s + (1 - p s) * wp b (Sup_exp (range M)) s =
                  Sup_exp (range (\<lambda>x s. p s * wp a (M x) s + (1 - p s) * wp b (M x) s)) s"
    by(auto)
qed

text \<open>Both set-based choice operators are only continuous for finite sets (probabilistic choice
\emph{can} be extended infinitely, but we have not done so).  The proofs for both are inductive,
and rely on the above results on binary operators.\<close>

lemma SetPC_Bind:
  "SetPC a p = Bind p (\<lambda>p. SetPC a (\<lambda>_. p))"
  by(intro ext, simp add:SetPC_def Bind_def Let_def)

lemma SetPC_remove:
  assumes nz: "p x \<noteq> 0" and n1: "p x \<noteq> 1"
      and fsupp: "finite (supp p)"
  shows "SetPC a (\<lambda>_. p) = PC (a x) (\<lambda>_. p x) (SetPC a (\<lambda>_. dist_remove p x))"
proof(intro ext, simp add:SetPC_def PC_def)
  fix ab P s
  from nz have "x \<in> supp p" by(simp add:supp_def)
  hence "supp p = insert x (supp p - {x})" by(auto)
  hence "(\<Sum>x\<in>supp p. p x * a x ab P s) =
         (\<Sum>x\<in>insert x (supp p - {x}). p x * a x ab P s)"
    by(simp)
  also from fsupp
  have "... = p x * a x ab P s + (\<Sum>x\<in>supp p - {x}. p x * a x ab P s)"
    by(blast intro:sum.insert)
  also from n1
  have "... = p x * a x ab P s + (1 - p x) * ((\<Sum>x\<in>supp p - {x}. p x * a x ab P s) / (1 - p x))"
    by(simp add:field_simps)
  also have "... = p x * a x ab P s +
                   (1 - p x) * ((\<Sum>y\<in>supp p - {x}. (p y / (1 - p x)) * a y ab P s))"
    by(simp add:sum_divide_distrib)
  also have "... = p x * a x ab P s +
                   (1 - p x) * ((\<Sum>y\<in>supp p - {x}. dist_remove p x y * a y ab P s))"
    by(simp add:dist_remove_def)
  also from nz n1
  have "... = p x * a x ab P s +
              (1 - p x) * ((\<Sum>y\<in>supp (dist_remove p x). dist_remove p x y * a y ab P s))"
    by(simp add:supp_dist_remove)
  finally show "(\<Sum>x\<in>supp p. p x * a x ab P s) =
                 p x * a x ab P s +
                 (1 - p x) * (\<Sum>y\<in>supp (dist_remove p x). dist_remove p x y * a y ab P s)" .
qed

lemma cts_bot:
  "bd_cts (\<lambda>(P::'s expect) (s::'s). 0::real)"
proof -
  have X: "\<And>s::'s. {(P::'s expect) s |P. P \<in> range (\<lambda>P s. 0)} = {0}" by(auto)
  show ?thesis by(intro bd_ctsI, simp add:Sup_exp_def o_def X)
qed

lemma wp_SetPC_nil:
  "wp (SetPC a (\<lambda>s a. 0)) = (\<lambda>P s. 0)"
  by(intro ext, simp add:wp_eval)

lemma SetPC_sgl:
  "supp p = {x} \<Longrightarrow> SetPC a (\<lambda>_. p) = (\<lambda>ab P s. p x * a x ab P s)"
  by(simp add:SetPC_def)

lemma bd_cts_scale:
  fixes a::"'s trans"
  assumes ca: "bd_cts a"
      and ha: "healthy a"
      and nnc: "0 \<le> c"
  shows "bd_cts (\<lambda>P s. c * a P s)"
proof(intro bd_ctsI ext, simp add:o_def)
  fix M::"nat \<Rightarrow> 's expect" and d::real and s::'s
  assume chain: "\<And>i. M i \<tturnstile> M (Suc i)" and sM: "\<And>i. sound (M i)"
     and bM: "\<And>i. bounded_by d (M i)"

  from sM have "\<And>i. nneg (M i)" by(auto)
  with bM have nnd: "0 \<le> d" by(auto)

  from sM bM have sSup: "sound (Sup_exp (range M))" by(auto intro:Sup_exp_sound)
  with healthy_scalingD[OF ha] nnc
  have "c * a (Sup_exp (range M)) s = a (\<lambda>s. c * Sup_exp (range M) s) s"
    by(auto intro:scalingD)
  also {
    have "\<And>s. {f s |f. f \<in> range M} = range (\<lambda>i. M i s)" by(auto)
    hence "a (\<lambda>s. c * Sup_exp (range M) s) s =
           a (\<lambda>s. c * Sup (range (\<lambda>i. M i s))) s"
      by(simp add:Sup_exp_def)
  }
  also {
    from bM have "\<And>x s. x \<in> range (\<lambda>i. M i s) \<Longrightarrow> x \<le> d" by(auto)
    with nnc have "a (\<lambda>s. c * Sup (range (\<lambda>i. M i s))) s =
                   a (\<lambda>s. Sup {c*x |x. x \<in> range (\<lambda>i. M i s)}) s"
      by(subst cSup_mult, blast+)
  }
  also {
    have X: "\<And>s. {c * x |x. x \<in> range (\<lambda>i. M i s)} = range (\<lambda>i. c * M i s)" by(auto)
    have "a (\<lambda>s. Sup {c * x |x. x \<in> range (\<lambda>i. M i s)}) s =
          a (\<lambda>s. Sup (range (\<lambda>i. c * M i s))) s" by(simp add:X)
  }
  also {
    have "\<And>s. range (\<lambda>i. c * M i s) = {f s |f. f \<in> range (\<lambda>i s. c * M i s)}"
      by(auto)
    hence "(\<lambda>s. Sup (range (\<lambda>i. c * M i s))) = Sup_exp (range (\<lambda>i s. c * M i s))"
      by (simp add: Sup_exp_def cong del: SUP_cong_simp)
    hence "a (\<lambda>s. Sup (range (\<lambda>i. c * M i s))) s =
           a (Sup_exp (range (\<lambda>i s. c * M i s))) s" by(simp)
  }
  also {
    from le_funD[OF chain] nnc
    have "\<And>i. (\<lambda>s. c * M i s) \<tturnstile> (\<lambda>s. c * M (Suc i) s)"
      by(auto intro:le_funI[OF mult_left_mono])
    moreover from sM nnc
    have "\<And>i. sound (\<lambda>s. c * M i s)"
      by(auto intro:sound_intros)
    moreover from bM nnc
    have "\<And>i. bounded_by (c * d) (\<lambda>s. c * M i s)"
      by(auto intro:mult_left_mono)
    ultimately
    have "a (Sup_exp (range (\<lambda>i s. c * M i s))) =
          Sup_exp (range (a o (\<lambda>i s. c * M i s)))"
      by(rule bd_ctsD[OF ca])
    hence "a (Sup_exp (range (\<lambda>i s. c * M i s))) s =
          Sup_exp (range (a o (\<lambda>i s. c * M i s))) s"
      by(auto)
  }
  also have "Sup_exp (range (a o (\<lambda>i s. c * M i s))) s =
             Sup_exp (range (\<lambda>x. a (\<lambda>s. c * M x s))) s"
    by(simp add:o_def)
  also {
    from nnc sM
    have "\<And>x. a (\<lambda>s. c * M x s) = (\<lambda>s. c * a (M x) s)"
      by(auto intro:scalingD[OF healthy_scalingD, OF ha, symmetric])
    hence "Sup_exp (range (\<lambda>x. a (\<lambda>s. c * M x s))) s =
           Sup_exp (range (\<lambda>x s. c * a (M x) s)) s"
      by(simp)
  }
  finally show "c * a (Sup_exp (range M)) s = Sup_exp (range (\<lambda>x s. c * a (M x) s)) s" .
qed

lemma cts_wp_SetPC_const:
  fixes a::"'a \<Rightarrow> 's prog"
  assumes ca: "\<And>x. x \<in> (supp p) \<Longrightarrow> bd_cts (wp (a x))"
      and ha: "\<And>x. x \<in> (supp p) \<Longrightarrow> healthy (wp (a x))"
      and up: "unitary p"
      and sump: "sum p (supp p) \<le> 1"
      and fsupp: "finite (supp p)"
  shows "bd_cts (wp (SetPC a (\<lambda>_. p)))"
proof(cases "supp p = {}", simp add:supp_empty SetPC_def wp_def cts_bot)
  assume nesupp: "supp p \<noteq> {}"
  from fsupp have "unitary p \<longrightarrow> sum p (supp p) \<le> 1 \<longrightarrow> 
                   (\<forall>x\<in>supp p. bd_cts (wp (a x))) \<longrightarrow>
                   (\<forall>x\<in>supp p. healthy (wp (a x))) \<longrightarrow>
                   bd_cts (wp (SetPC a (\<lambda>_. p)))"
  proof(induct "supp p" arbitrary:p, simp add:supp_empty wp_SetPC_nil cts_bot, clarify)
    fix x::'a and F::"'a set" and p::"'a \<Rightarrow> real"
    assume fF: "finite F"
    assume "insert x F = supp p"
    hence pstep: "supp p = insert x F" by(simp)
    hence xin: "x \<in> supp p" by(auto)
    assume up: "unitary p" and ca: "\<forall>x\<in>supp p. bd_cts (wp (a x))"
       and ha: "\<forall>x\<in>supp p. healthy (wp (a x))"
       and sump: "sum p (supp p) \<le> 1"
       and xni: "x \<notin> F"
    assume IH: "\<And>p. F = supp p \<Longrightarrow>
                     unitary p \<longrightarrow> sum p (supp p) \<le> 1 \<longrightarrow>
                     (\<forall>x\<in>supp p. bd_cts (wp (a x))) \<longrightarrow>
                     (\<forall>x\<in>supp p. healthy (wp (a x))) \<longrightarrow>
                     bd_cts (wp (SetPC a (\<lambda>_. p)))"

    from fF pstep have fsupp: "finite (supp p)" by(auto)

    from xin have nzp: "p x \<noteq> 0" by(simp add:supp_def)

    have xy_le_sum:
      "\<And>y. y \<in> supp p \<Longrightarrow> y \<noteq> x \<Longrightarrow> p x + p y \<le> sum p (supp p)"
    proof -
      fix y assume yin: "y \<in> supp p" and yne: "y \<noteq> x"
      from up have "0 \<le> sum p (supp p - {x,y})"
        by(auto intro:sum_nonneg)
      hence "p x + p y \<le> p x + p y + sum p (supp p - {x,y})"
        by(auto)
    also {
      from yin yne fsupp
      have "p y + sum p (supp p - {x,y}) = sum p (supp p - {x})"
        by(subst sum.insert[symmetric], (blast intro!:sum.cong)+)
      moreover
      from xin fsupp
      have "p x + sum p (supp p - {x}) = sum p (supp p)"
        by(subst sum.insert[symmetric], (blast intro!:sum.cong)+)
      ultimately
      have "p x + p y + sum p (supp p - {x, y}) = sum p (supp p)" by(simp)
    }
    finally show "p x + p y \<le> sum p (supp p)" .
    qed

    have n1p: "\<And>y. y \<in> supp p \<Longrightarrow> y \<noteq> x \<Longrightarrow> p x \<noteq> 1"
    proof(rule ccontr, simp)
      assume px1: "p x = 1"
      fix y assume yin: "y \<in> supp p" and yne: "y \<noteq> x"
      from up have "0 \<le> p y" by(auto)
      with yin have "0 < p y" by(auto simp:supp_def)
      hence "0 + p x < p y + p x" by(rule add_strict_right_mono)
      with px1 have "1 < p x + p y" by(simp)
      also from yin yne have "p x + p y \<le> sum p (supp p)"
        by(rule xy_le_sum)
      finally show False using sump by(simp)
    qed

    show "bd_cts (wp (SetPC a (\<lambda>_. p)))"
    proof(cases "F = {}")
      case True with pstep have "supp p = {x}" by(simp)
      hence "wp (SetPC a (\<lambda>_. p)) = (\<lambda>P s. p x * wp (a x) P s)"
        by(simp add:SetPC_sgl wp_def)
      moreover {
        from up ca ha xin have "bd_cts (wp (a x))" "healthy (wp (a x))" "0 \<le> p x"
          by(auto)
        hence "bd_cts (\<lambda>P s. p x * wp (a x) P s)"
          by(rule bd_cts_scale)
      } 
      ultimately show ?thesis by(simp)
    next
      assume neF: "F \<noteq> {}"
      then obtain y where yinF: "y \<in> F" by(auto)
      with xni have yne: "y \<noteq> x" by(auto)
      from yinF pstep have yin: "y \<in> supp p" by(auto)

      from supp_dist_remove[of p x, OF nzp n1p, OF yin yne]
      have supp_sub: "supp (dist_remove p x) \<subseteq> supp p" by(auto)

      from xin ca have cax: "bd_cts (wp (a x))" by(auto)
      from xin ha have hax: "healthy (wp (a x))" by(auto)

      from supp_sub ha have hra: "\<forall>x\<in>supp (dist_remove p x). healthy (wp (a x))"
        by(auto)
      from supp_sub ca have cra: "\<forall>x\<in>supp (dist_remove p x). bd_cts (wp (a x))"
        by(auto)

      from supp_dist_remove[of p x, OF nzp n1p, OF yin yne] pstep xni
      have Fsupp: "F = supp (dist_remove p x)"
        by(simp)

      have udp: "unitary (dist_remove p x)"
      proof(intro unitaryI2 nnegI bounded_byI)
        fix y
        show "0 \<le> dist_remove p x y"
        proof(cases "y=x", simp_all add:dist_remove_def)
          from up have "0 \<le> p y" "0 \<le> 1 - p x"
            by auto
          thus "0 \<le> p y / (1 - p x)"
            by(rule divide_nonneg_nonneg)
        qed
        show "dist_remove p x y \<le> 1"
        proof(cases "y=x", simp_all add:dist_remove_def,
              cases "y\<in>supp p", simp_all add:nsupp_zero)
          assume yne: "y \<noteq> x" and yin: "y \<in> supp p"
          hence "p x + p y \<le> sum p (supp p)"
            by(auto intro:xy_le_sum)
          also note sump
          finally have "p y \<le> 1 - p x" by(auto)
          moreover from up have "p x \<le> 1" by(auto)
          moreover from yin yne have "p x \<noteq> 1" by(rule n1p)
          ultimately show "p y / (1 - p x) \<le> 1" by(auto)
        qed
      qed

      from xin have pxn0: "p x \<noteq> 0" by(auto simp:supp_def)
      from yin yne have pxn1: "p x \<noteq> 1" by(rule n1p)

      from pxn0 pxn1 have "sum (dist_remove p x) (supp (dist_remove p x)) =
                           sum (dist_remove p x) (supp p - {x})"
        by(simp add:supp_dist_remove)
      also have "... = (\<Sum>y\<in>supp p - {x}. p y / (1 - p x))"
        by(simp add:dist_remove_def)
      also have "... = (\<Sum>y\<in>supp p - {x}. p y) / (1 - p x)"
        by(simp add:sum_divide_distrib)
      also {
        from xin have "insert x (supp p) = supp p" by(auto)
        with fsupp have "p x + (\<Sum>y\<in>supp p - {x}. p y) = sum p (supp p)"
          by(simp add:sum.insert[symmetric])
        also note sump
        finally have "sum p (supp p - {x}) \<le> 1 - p x" by(auto)
        moreover {
          from up have "p x \<le> 1" by(auto)
          with pxn1 have "p x < 1" by(auto)
          hence "0 < 1 - p x" by(auto)
        }
        ultimately have "sum p (supp p - {x}) / (1 - p x) \<le> 1"
          by(auto)
      }
      finally have sdp: "sum (dist_remove p x) (supp (dist_remove p x)) \<le> 1" .

      from Fsupp udp sdp hra cra IH
      have cts_dr: "bd_cts (wp (SetPC a (\<lambda>_. dist_remove p x)))"
        by(auto)

      from up have upx: "unitary (\<lambda>_. p x)" by(auto)
      
      from pxn0 pxn1 fsupp hra show ?thesis
        by(simp add:SetPC_remove,
           blast intro:cts_wp_PC cax cts_dr hax healthy_intros
                       unitary_sound[OF udp] sdp upx)
    qed
  qed
  with assms show ?thesis by(auto)
qed

lemma cts_wp_SetPC:
  fixes a::"'a \<Rightarrow> 's prog"
  assumes ca: "\<And>x s. x \<in> (supp (p s)) \<Longrightarrow> bd_cts (wp (a x))"
      and ha: "\<And>x s. x \<in> (supp (p s)) \<Longrightarrow> healthy (wp (a x))"
      and up: "\<And>s. unitary (p s)"
      and sump: "\<And>s. sum (p s) (supp (p s)) \<le> 1"
      and fsupp: "\<And>s. finite (supp (p s))"
  shows "bd_cts (wp (SetPC a p))"
proof -
  from assms have "bd_cts (wp (Bind p (\<lambda>p. SetPC a (\<lambda>_. p))))"
    by(iprover intro!:cts_wp_Bind cts_wp_SetPC_const)
  thus ?thesis by(simp add:SetPC_Bind[symmetric])
qed

lemma wp_SetDC_Bind:
  "SetDC a S = Bind S (\<lambda>S. SetDC a (\<lambda>_. S))"
  by(intro ext, simp add:SetDC_def Bind_def)

lemma SetDC_finite_insert:
  assumes fS: "finite S"
      and neS: "S \<noteq> {}"
  shows "SetDC a (\<lambda>_. insert x S) = a x \<Sqinter> SetDC a (\<lambda>_. S)"
proof (intro ext, simp add: SetDC_def DC_def cong del: image_cong_simp cong add: INF_cong_simp)
  fix ab P s
  from fS have A: "finite (insert (a x ab P s) ((\<lambda>x. a x ab P s) ` S))" 
           and B: "finite (((\<lambda>x. a x ab P s) ` S))" by(auto)
  from neS have C: "insert (a x ab P s) ((\<lambda>x. a x ab P s) ` S) \<noteq> {}"
            and D: "(\<lambda>x. a x ab P s) ` S \<noteq> {}" by(auto)
  from A C have "Inf (insert (a x ab P s) ((\<lambda>x. a x ab P s) ` S)) =
                 Min (insert (a x ab P s) ((\<lambda>x. a x ab P s) ` S))"
    by(auto intro:cInf_eq_Min)
  also from B D have "... = min (a x ab P s) (Min ((\<lambda>x. a x ab P s) ` S))"
    by(auto intro:Min_insert)
  also from B D have "... = min (a x ab P s) (Inf ((\<lambda>x. a x ab P s) ` S))"
    by(simp add:cInf_eq_Min)
  finally show "(INF x\<in>insert x S. a x ab P s) =
    min (a x ab P s) (INF x\<in>S. a x ab P s)"
    by (simp cong del: INF_cong_simp)
qed

lemma SetDC_singleton:
  "SetDC a (\<lambda>_. {x}) = a x"
  by (simp add: SetDC_def cong del: INF_cong_simp)

lemma cts_wp_SetDC_const:
  fixes a::"'a \<Rightarrow> 's prog"
  assumes ca: "\<And>x. x \<in> S \<Longrightarrow> bd_cts (wp (a x))"
      and ha: "\<And>x. x \<in> S \<Longrightarrow> healthy (wp (a x))"
      and fS: "finite S"
      and neS: "S \<noteq> {}"
  shows "bd_cts (wp (SetDC a (\<lambda>_. S)))"
proof -
  have "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
        (\<forall>x\<in>S. bd_cts (wp (a x))) \<longrightarrow>
        (\<forall>x\<in>S. healthy (wp (a x))) \<longrightarrow>
        bd_cts (wp (SetDC a (\<lambda>_. S)))"
  proof(induct S rule:finite_induct, simp, clarsimp)
    fix x::'a and F::"'a set"
    assume fF: "finite F"
       and IH: "F \<noteq> {} \<Longrightarrow> bd_cts (wp (SetDC a (\<lambda>_. F)))"
       and cax: "bd_cts (wp (a x))"
       and hax: "healthy (wp (a x))"
       and haF: "\<forall>x\<in>F. healthy (wp (a x))"
    show "bd_cts (wp (SetDC a (\<lambda>_. insert x F)))"
    proof(cases "F = {}", simp add:SetDC_singleton cax)
      assume "F \<noteq> {}"
      with fF cax hax haF IH show "bd_cts (wp (SetDC a (\<lambda>_. insert x F)))"
       by(auto intro!:cts_wp_DC healthy_intros simp:SetDC_finite_insert)
    qed
  qed
  with assms show ?thesis by(auto)
qed

lemma cts_wp_SetDC:
  fixes a::"'a \<Rightarrow> 's prog"
  assumes ca: "\<And>x s. x \<in> S s \<Longrightarrow> bd_cts (wp (a x))"
      and ha: "\<And>x s. x \<in> S s \<Longrightarrow> healthy (wp (a x))"
      and fS: "\<And>s. finite (S s)"
      and neS: "\<And>s. S s \<noteq> {}"
  shows "bd_cts (wp (SetDC a S))"
proof -
  from assms have "bd_cts (wp (Bind S (\<lambda>S. SetDC a (\<lambda>_. S))))"
    by(iprover intro!:cts_wp_Bind cts_wp_SetDC_const)
  thus ?thesis by(simp add:wp_SetDC_Bind[symmetric])
qed

lemma cts_wp_repeat:
  "bd_cts (wp a) \<Longrightarrow> healthy (wp a) \<Longrightarrow> bd_cts (wp (repeat n a))"
  by(induct n, auto intro:cts_wp_Skip cts_wp_Seq healthy_intros)

lemma cts_wp_Embed:
  "bd_cts t \<Longrightarrow> bd_cts (wp (Embed t))"
  by(simp add:wp_eval)

subsection \<open>Continuity of a Single Loop Step\<close>

text \<open>A single loop iteration is continuous, in the more general sense defined above for
transformer transformers.\<close>
lemma cts_wp_loopstep:
  fixes body::"'s prog"
  assumes hb: "healthy (wp body)"
      and cb: "bd_cts (wp body)"
  shows "bd_cts_tr (\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip))" (is "bd_cts_tr ?F")
proof(rule bd_cts_trI, rule le_trans_antisym)
  fix M::"nat \<Rightarrow> 's trans" and b::real
  assume chain: "\<And>i. le_trans (M i) (M (Suc i))"
     and fM:    "\<And>i. feasible (M i)"
  show fw: "le_trans (Sup_trans (range (?F o M))) (?F (Sup_trans (range M)))"
  proof(rule le_transI[OF Sup_trans_least2], clarsimp)
    fix P Q::"'s expect" and t
    assume sP: "sound P"
    assume nQ: "nneg Q" and bP: "bounded_by (bound_of P) Q"
    hence sQ: "sound Q" by(auto)

    from fM have fSup: "feasible (Sup_trans (range M))"
      by(auto intro:feasible_Sup_trans)

    from sQ fM have "M t Q \<tturnstile> Sup_trans (range M) Q"
      by(auto intro:Sup_trans_upper2)
    moreover from sQ fM fSup
      have sMtP: "sound (M t Q)" "sound (Sup_trans (range M) Q)" by(auto)
    ultimately have "wp body (M t Q) \<tturnstile> wp body (Sup_trans (range M) Q)"
      using healthy_monoD[OF hb] by(auto)
    hence "\<And>s. wp body (M t Q) s \<le> wp body (Sup_trans (range M) Q) s"
      by(rule le_funD)
    thus "?F (M t) Q \<tturnstile> ?F (Sup_trans (range M)) Q"
      by(intro le_funI, simp add:wp_eval mult_left_mono)

    show "nneg (wp (body ;; Embed (Sup_trans (range M)) \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip) Q)"
    proof(rule nnegI, simp add:wp_eval)
      fix s::'s
        from fSup sQ have "sound (Sup_trans (range M) Q)" by(auto)
        with hb have "sound (wp body (Sup_trans (range M) Q))" by(auto)
        hence "0 \<le> wp body (Sup_trans (range M) Q) s" by(auto)
        moreover from sQ have "0 \<le> Q s" by(auto)
        ultimately show "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body (Sup_trans (range M) Q) s + (1 - \<guillemotleft>G\<guillemotright> s) * Q s"
          by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)
    qed
  next
    fix P::"'s expect" assume sP: "sound P"
    thus "nneg P" "bounded_by (bound_of P) P" by(auto)
    show "\<forall>u\<in>range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M).
            \<forall>R. nneg R \<and> bounded_by (bound_of P) R \<longrightarrow>
                nneg (u R) \<and> bounded_by (bound_of P) (u R)"
    proof(clarsimp, intro conjI nnegI bounded_byI, simp_all add:wp_eval)
      fix u::nat and R::"'s expect" and s::'s
      assume nR: "nneg R" and bR: "bounded_by (bound_of P) R"
      hence sR: "sound R" by(auto)
      with fM have sMuR: "sound (M u R)" by(auto)
      with hb have "sound (wp body (M u R))" by(auto)
      hence "0 \<le> wp body (M u R) s" by(auto)
      moreover from nR have "0 \<le> R s" by(auto)
      ultimately show "0 \<le> \<guillemotleft>G\<guillemotright> s * wp body (M u R) s + (1 - \<guillemotleft>G\<guillemotright> s) * R s"
        by(auto intro:add_nonneg_nonneg mult_nonneg_nonneg)

      from sR bR fM have "bounded_by (bound_of P) (M u R)" by(auto)
      with sMuR hb have "bounded_by (bound_of P) (wp body (M u R))" by(auto)
      hence "wp body (M u R) s \<le> bound_of P" by(auto)
      moreover from bR have "R s \<le> bound_of P" by(auto)
      ultimately have "\<guillemotleft>G\<guillemotright> s * wp body (M u R) s + (1 - \<guillemotleft>G\<guillemotright> s) * R s \<le>
                       \<guillemotleft>G\<guillemotright> s * bound_of P + (1 - \<guillemotleft>G\<guillemotright> s) * bound_of P"
        by(auto intro:add_mono mult_left_mono)
      also have "... = bound_of P" by(simp add:algebra_simps)
      finally show "\<guillemotleft>G\<guillemotright> s * wp body (M u R) s + (1 - \<guillemotleft>G\<guillemotright> s) * R s \<le> bound_of P" .
    qed
  qed

  show "le_trans (?F (Sup_trans (range M))) (Sup_trans (range (?F o M)))"
   proof(rule le_transI, rule le_funI, simp add: wp_eval cong del: image_cong_simp)
    fix P::"'s expect" and s::'s
    assume sP: "sound P"
    have "{t P |t. t \<in> range M} = range (\<lambda>i. M i P)"
      by(blast)
    hence "wp body (Sup_trans (range M) P) s = wp body (Sup_exp (range (\<lambda>i. M i P))) s"
      by(simp add:Sup_trans_def)
    also {
      from sP fM have "\<And>i. sound (M i P)" by(auto)
      moreover from sP chain have "\<And>i. M i P \<tturnstile> M (Suc i) P" by(auto)
      moreover {
        from sP have "bounded_by (bound_of P) P" by(auto)
        with sP fM have "\<And>i. bounded_by (bound_of P) (M i P)" by(auto)
      }
      ultimately have "wp body (Sup_exp (range (\<lambda>i. M i P))) s =
                       Sup_exp (range (\<lambda>i. wp body (M i P))) s"
        by(subst bd_ctsD[OF cb], auto simp:o_def)
    }
    also have "Sup_exp (range (\<lambda>i. wp body (M i P))) s =
               Sup {f s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
      by(simp add:Sup_exp_def)
    finally have "\<guillemotleft>G\<guillemotright> s * wp body (Sup_trans (range M) P) s + (1 - \<guillemotleft>G\<guillemotright> s) * P s =
                  \<guillemotleft>G\<guillemotright> s * Sup {f s |f. f \<in> range (\<lambda>i. wp body (M i P))} + (1 - \<guillemotleft>G\<guillemotright> s) * P s"
      by(simp)
    also {
      from sP fM have "\<And>i. sound (M i P)" by(auto)
      moreover from sP fM have "\<And>i. bounded_by (bound_of P) (M i P)" by(auto)
      ultimately have "\<And>i. bounded_by (bound_of P) (wp body (M i P))" using hb by(auto)
      hence bound: "\<And>i. wp body (M i P) s \<le> bound_of P" by(auto)
      moreover
      have "{\<guillemotleft> G \<guillemotright> s * x |x. x \<in> {f s |f. f \<in> range (\<lambda>i. wp body (M i P))}} =
            {\<guillemotleft> G \<guillemotright> s * f s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
        by(blast)
      ultimately
      have "\<guillemotleft>G\<guillemotright> s * Sup {f s |f. f \<in> range (\<lambda>i. wp body (M i P))} =
            Sup {\<guillemotleft>G\<guillemotright> s * f s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
        by(subst cSup_mult, auto)
      moreover {
        have "{x + (1-\<guillemotleft>G\<guillemotright> s) * P s |x.
               x \<in> {\<guillemotleft>G\<guillemotright> s * f s |f. f \<in> range (\<lambda>i. wp body (M i P))}} =
              {\<guillemotleft>G\<guillemotright> s * f s + (1-\<guillemotleft>G\<guillemotright> s) * P s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
          by(blast)
        moreover from bound sP have "\<And>i. \<guillemotleft>G\<guillemotright> s * wp body (M i P) s \<le> bound_of P"
          by(cases "G s", auto)
        ultimately
        have "Sup {\<guillemotleft>G\<guillemotright> s * f s |f. f \<in> range (\<lambda>i. wp body (M i P))} + (1-\<guillemotleft>G\<guillemotright> s) * P s =
              Sup {\<guillemotleft>G\<guillemotright> s * f s + (1-\<guillemotleft>G\<guillemotright> s) * P s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
          by(subst cSup_add, auto)
      }
      ultimately
      have "\<guillemotleft>G\<guillemotright> s * Sup {f s |f. f \<in> range (\<lambda>i. wp body (M i P))} + (1-\<guillemotleft>G\<guillemotright> s) * P s =
            Sup {\<guillemotleft>G\<guillemotright> s * f s + (1-\<guillemotleft>G\<guillemotright> s) * P s |f. f \<in> range (\<lambda>i. wp body (M i P))}"
        by(simp)
    }
    also {
      have "\<And>i. \<guillemotleft>G\<guillemotright> s * wp body (M i P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s =
                 ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M) i P s"
        by(simp add:wp_eval)
      also have "\<And>i. ... i \<le>
                 Sup {f s |f. f \<in> {t P |t. t \<in> range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M)}}"
      proof(intro cSup_upper bdd_aboveI, blast, clarsimp simp:wp_eval)
        fix i
        from sP have bP: "bounded_by (bound_of P) P" by(auto)
        with sP fM have "sound (M i P)" "bounded_by (bound_of P) (M i P)" by(auto)
        with hb have "bounded_by (bound_of P) (wp body (M i P))" by(auto)
        with bP have "wp body (M i P) s \<le> bound_of P" "P s \<le> bound_of P" by(auto)
        hence "\<guillemotleft>G\<guillemotright> s * wp body (M i P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s \<le>
               \<guillemotleft>G\<guillemotright> s * (bound_of P) + (1-\<guillemotleft>G\<guillemotright> s) * (bound_of P)"
          by(auto intro:add_mono mult_left_mono)
        also have "... = bound_of P" by(simp add:algebra_simps)
        finally show "\<guillemotleft>G\<guillemotright> s * wp body (M i P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s \<le> bound_of P" .
      qed
      finally
      have "Sup {\<guillemotleft>G\<guillemotright> s * f s + (1-\<guillemotleft>G\<guillemotright> s) * P s |f. f \<in> range (\<lambda>i. wp body (M i P))} \<le>
            Sup {f s |f. f \<in> {t P |t. t \<in> range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M)}}"
        by(blast intro:cSup_least)
    }
    also have "Sup {f s |f. f \<in> {t P |t. t \<in> range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M)}} =
               Sup_trans (range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M)) P s"
      by(simp add:Sup_trans_def Sup_exp_def)
    finally show "\<guillemotleft>G\<guillemotright> s * wp body (Sup_trans (range M) P) s + (1-\<guillemotleft>G\<guillemotright> s) * P s \<le>
                  Sup_trans (range ((\<lambda>x. wp (body ;; Embed x \<^bsub>\<guillemotleft> G \<guillemotright>\<^esub>\<oplus> Skip)) \<circ> M)) P s" .
  qed
qed

end
