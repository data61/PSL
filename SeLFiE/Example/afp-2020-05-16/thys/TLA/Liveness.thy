(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section "Liveness"

theory Liveness
imports Rules
begin

text\<open>This theory derives proof rules for liveness properties.\<close>

definition enabled :: "'a formula \<Rightarrow> 'a formula"
where "enabled F \<equiv> \<lambda> s. \<exists> t. ((first s) ## t) \<Turnstile> F"

syntax "_Enabled" :: "lift \<Rightarrow> lift" ("(Enabled _)" [90] 90)

translations "_Enabled" \<rightleftharpoons> "CONST enabled"

definition WeakF :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "WeakF F v \<equiv> TEMP \<diamond>\<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> \<box>\<diamond>\<langle>F\<rangle>_v"

definition StrongF :: "('a::world) formula \<Rightarrow> ('a,'b) stfun \<Rightarrow> 'a formula"
where "StrongF F v \<equiv> TEMP \<box>\<diamond>Enabled \<langle>F\<rangle>_v \<longrightarrow> \<box>\<diamond>\<langle>F\<rangle>_v"

text\<open>
  Lamport's TLA defines the above notions for actions.
  In \tlastar{}, (pre-)formulas generalise TLA's actions and the above
  definition is the natural generalisation of enabledness to pre-formulas.
  In particular, we have chosen to define \<open>enabled\<close> such that it
  yields itself a temporal formula, although its value really just depends
  on the first state of the sequence it is evaluated over.
  Then, the definitions of weak and strong fairness are exactly as in TLA.
\<close>

syntax
 "_WF" :: "[lift,lift] \<Rightarrow> lift" ("(WF'(_')'_(_))"  [20,1000] 90)
 "_SF" :: "[lift,lift] \<Rightarrow> lift" ("(SF'(_')'_(_))"  [20,1000] 90)
 "_WFsp" :: "[lift,lift] \<Rightarrow> lift" ("(WF '(_')'_(_))"  [20,1000] 90)
 "_SFsp" :: "[lift,lift] \<Rightarrow> lift" ("(SF '(_')'_(_))"  [20,1000] 90)

translations
 "_WF" \<rightleftharpoons> "CONST WeakF"
 "_SF" \<rightleftharpoons> "CONST StrongF"
 "_WFsp" \<rightharpoonup> "CONST WeakF"
 "_SFsp" \<rightharpoonup> "CONST StrongF"


subsection "Properties of @{term enabled}"

theorem enabledI: "\<turnstile> F \<longrightarrow> Enabled F"
proof (clarsimp)
  fix w
  assume "w \<Turnstile> F"
  with seq_app_first_tail[of w] have "((first w) ## tail w) \<Turnstile> F" by simp
  thus "w \<Turnstile> Enabled F" by (auto simp: enabled_def)
qed

theorem enabledE:
  assumes "s \<Turnstile> Enabled F" and "\<And>u. (first s ## u) \<Turnstile> F \<Longrightarrow> Q"
  shows "Q"
  using assms unfolding enabled_def by blast

lemma enabled_mono: 
  assumes "w \<Turnstile> Enabled F" and "\<turnstile> F \<longrightarrow> G" 
  shows "w \<Turnstile> Enabled G"
  using assms[unlifted] unfolding enabled_def by blast

lemma Enabled_disj1: "\<turnstile> Enabled F \<longrightarrow> Enabled (F \<or> G)"
  by (auto simp: enabled_def)

lemma  Enabled_disj2: "\<turnstile> Enabled F \<longrightarrow> Enabled (G \<or> F)"
  by (auto simp: enabled_def)

lemma  Enabled_conj1: "\<turnstile> Enabled (F \<and> G) \<longrightarrow> Enabled F"
  by (auto simp: enabled_def)

lemma  Enabled_conj2: "\<turnstile> Enabled (G \<and> F) \<longrightarrow> Enabled F"
  by (auto simp: enabled_def)

lemma Enabled_disjD: "\<turnstile> Enabled (F \<or> G) \<longrightarrow> Enabled F \<or> Enabled G"
  by (auto simp: enabled_def)

lemma Enabled_disj: "\<turnstile> Enabled (F \<or> G) = (Enabled F \<or> Enabled G)"
  by (auto simp: enabled_def)

lemmas enabled_disj_rew = Enabled_disj[int_rewrite]

lemma Enabled_ex: "\<turnstile> Enabled (\<exists> x. F x) = (\<exists> x. Enabled (F x))"
  by (force simp: enabled_def)

subsection "Fairness Properties" 

lemma WF_alt: "\<turnstile> WF(A)_v = (\<box>\<diamond>\<not>Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v)"
proof -
  have "\<turnstile> WF(A)_v = (\<not>\<diamond>\<box> Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v)" by (auto simp: WeakF_def)
  thus ?thesis by (simp add: dualization_rew)
qed

lemma SF_alt: "\<turnstile> SF(A)_v = (\<diamond>\<box>\<not>Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v)"
proof -
  have "\<turnstile> SF(A)_v = (\<not>\<box>\<diamond> Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v)" by (auto simp: StrongF_def)
  thus ?thesis by (simp add: dualization_rew)
qed

lemma alwaysWFI: "\<turnstile> WF(A)_v \<longrightarrow> \<box>WF(A)_v"
  unfolding WF_alt[int_rewrite] by (rule MM6)

theorem WF_always[simp_unl]: "\<turnstile> \<box>WF(A)_v = WF(A)_v"
  by (rule int_iffI[OF ax1 alwaysWFI])

theorem WF_eventually[simp_unl]: "\<turnstile> \<diamond>WF(A)_v = WF(A)_v"
proof -
  have 1: "\<turnstile> \<not>WF(A)_v = (\<diamond>\<box>Enabled \<langle>A\<rangle>_v \<and> \<not> \<box>\<diamond>\<langle>A\<rangle>_v)"
    by (auto simp: WeakF_def)
  have "\<turnstile> \<box>\<not>WF(A)_v = \<not>WF(A)_v"
    by (simp add: 1[int_rewrite] STL5[int_rewrite] dualization_rew)
  thus ?thesis
    by (auto simp: eventually_def)
qed

lemma alwaysSFI: "\<turnstile> SF(A)_v \<longrightarrow> \<box>SF(A)_v"
proof -
  have "\<turnstile> \<box>\<diamond>\<box>\<not>Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<box>(\<box>\<diamond>\<box>\<not>Enabled \<langle>A\<rangle>_v \<or> \<box>\<diamond>\<langle>A\<rangle>_v)"
    by (rule MM6)
  thus ?thesis unfolding SF_alt[int_rewrite] by simp
qed

theorem SF_always[simp_unl]: "\<turnstile> \<box>SF(A)_v = SF(A)_v"
  by (rule int_iffI[OF ax1 alwaysSFI])

theorem SF_eventually[simp_unl]: "\<turnstile> \<diamond>SF(A)_v = SF(A)_v"
proof -
  have 1: "\<turnstile> \<not>SF(A)_v = (\<box>\<diamond>Enabled \<langle>A\<rangle>_v \<and> \<not> \<box>\<diamond>\<langle>A\<rangle>_v)"
    by (auto simp: StrongF_def)
  have "\<turnstile> \<box>\<not>SF(A)_v = \<not>SF(A)_v"
    by (simp add: 1[int_rewrite] STL5[int_rewrite] dualization_rew)
  thus ?thesis
    by (auto simp: eventually_def)
qed

theorem SF_imp_WF: "\<turnstile> SF (A)_v \<longrightarrow> WF (A)_v"
  unfolding WeakF_def StrongF_def by (auto dest: E20[unlift_rule])

lemma enabled_WFSF: "\<turnstile> \<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> (WF(F)_v = SF(F)_v)"
proof -
  have "\<turnstile> \<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> \<diamond>\<box>Enabled \<langle>F\<rangle>_v" by (rule E3)
  hence "\<turnstile> \<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> WF(F)_v \<longrightarrow> SF(F)_v" by (auto simp: WeakF_def StrongF_def)
  moreover
  have "\<turnstile> \<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> \<box>\<diamond>Enabled \<langle>F\<rangle>_v" by (rule STL4[OF E3])
  hence "\<turnstile> \<box>Enabled \<langle>F\<rangle>_v \<longrightarrow> SF(F)_v \<longrightarrow> WF(F)_v" by (auto simp: WeakF_def StrongF_def)
  ultimately show ?thesis by force
qed

theorem WF1_general:
  assumes h1: "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q"
      and h2: "|~ P \<and> N \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q"
      and h3: "\<turnstile> P \<and> N \<longrightarrow> Enabled \<langle>A\<rangle>_v"
      and h4: "|~ P \<and> Unchanged w \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>N \<and> WF(A)_v \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> \<box>(\<box>N \<and> WF(A)_v) \<longrightarrow> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)"
  proof (rule STL4)
    have "\<turnstile> \<box>(P \<and> N) \<longrightarrow> \<diamond>\<box>Enabled \<langle>A\<rangle>_v" by (rule lift_imp_trans[OF h3[THEN STL4] E3])
    hence "\<turnstile> \<box>P \<and> \<box>N \<and> WF(A)_v \<longrightarrow> \<box>\<diamond>\<langle>A\<rangle>_v" by (auto simp: WeakF_def STL5[int_rewrite])
    with ax1[of "TEMP \<diamond>\<langle>A\<rangle>_v"] show "\<turnstile> \<box>N \<and> WF(A)_v \<longrightarrow> \<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v" by force
  qed
  hence "\<turnstile> \<box>N \<and> WF(A)_v \<longrightarrow> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)"
    by (simp add: STL5[int_rewrite])
  with AA22[OF h1 h2 h4] show ?thesis by force
qed

text \<open>Lamport's version of the rule is derived as a special case.\<close>

theorem WF1: 
  assumes h1: "|~ P \<and> [N]_v \<longrightarrow> \<circle>P \<or> \<circle>Q"
      and h2: "|~ P \<and> \<langle>N \<and> A\<rangle>_v \<longrightarrow> \<circle>Q"
      and h3: "\<turnstile> P \<longrightarrow> Enabled \<langle>A\<rangle>_v"
      and h4: "|~ P \<and> Unchanged v \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>[N]_v \<and> WF(A)_v \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> \<box>\<box>[N]_v \<and> WF(A)_v \<longrightarrow> (P \<leadsto> Q)"
  proof (rule WF1_general)
    from h1 T9[of N v] show "|~ P \<and> \<box>[N]_v \<longrightarrow> \<circle>P \<or> \<circle>Q" by force
  next
    from T9[of N v] have "|~ P \<and> \<box>[N]_v \<and> \<langle>A\<rangle>_v \<longrightarrow> P \<and> \<langle>N \<and> A\<rangle>_v"
      by (auto simp: actrans_def angle_actrans_def)
    from this h2 show "|~ P \<and> \<box>[N]_v \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q" by (rule pref_imp_trans)
  next
    from h3 T9[of N v] show "\<turnstile> P \<and> \<box>[N]_v \<longrightarrow> Enabled \<langle>A\<rangle>_v" by force
  qed (rule h4)
  thus ?thesis by simp
qed

text \<open>
  The corresponding rule for strong fairness has an additional hypothesis
  \<open>\<box>F\<close>, which is typically a conjunction of other fairness properties
  used to prove that the helpful action eventually becomes enabled.
\<close>

theorem SF1_general:
  assumes h1: "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q"
      and h2: "|~ P \<and> N \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q"
      and h3: "\<turnstile> \<box>P \<and> \<box>N \<and> \<box>F \<longrightarrow> \<diamond>Enabled \<langle>A\<rangle>_v"
      and h4: "|~ P \<and> Unchanged w \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>N \<and> SF(A)_v \<and> \<box>F \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> \<box>(\<box>N \<and> SF(A)_v \<and> \<box>F) \<longrightarrow> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)"
  proof (rule STL4)
    have "\<turnstile> \<box>(\<box>P \<and> \<box>N \<and> \<box>F) \<longrightarrow> \<box>\<diamond>Enabled \<langle>A\<rangle>_v" by (rule STL4[OF h3])
    hence "\<turnstile> \<box>P \<and> \<box>N \<and> \<box>F \<and> SF(A)_v \<longrightarrow> \<box>\<diamond>\<langle>A\<rangle>_v" by (auto simp: StrongF_def STL5[int_rewrite])
    with ax1[of "TEMP \<diamond>\<langle>A\<rangle>_v"] show "\<turnstile> \<box>N \<and> SF(A)_v \<and> \<box>F \<longrightarrow> \<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v" by force
  qed
  hence "\<turnstile> \<box>N \<and> SF(A)_v \<and> \<box>F \<longrightarrow> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)"
    by (simp add: STL5[int_rewrite])
  with AA22[OF h1 h2 h4] show ?thesis by force
qed

theorem SF1:
  assumes h1: "|~ P \<and> [N]_v \<longrightarrow> \<circle>P \<or> \<circle>Q"
      and h2: "|~ P \<and> \<langle>N \<and> A\<rangle>_v \<longrightarrow> \<circle>Q"
      and h3: "\<turnstile> \<box>P \<and> \<box>[N]_v \<and> \<box>F \<longrightarrow> \<diamond>Enabled \<langle>A\<rangle>_v"
      and h4: "|~ P \<and> Unchanged v \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>[N]_v \<and> SF(A)_v \<and> \<box>F \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> \<box>\<box>[N]_v \<and> SF(A)_v \<and> \<box>F \<longrightarrow> (P \<leadsto> Q)"
  proof (rule SF1_general)
    from h1 T9[of N v] show "|~ P \<and> \<box>[N]_v \<longrightarrow> \<circle>P \<or> \<circle>Q" by force
  next
    from T9[of N v] have "|~ P \<and> \<box>[N]_v \<and> \<langle>A\<rangle>_v \<longrightarrow> P \<and> \<langle>N \<and> A\<rangle>_v"
      by (auto simp: actrans_def angle_actrans_def)
    from this h2 show "|~ P \<and> \<box>[N]_v \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q" by (rule pref_imp_trans)
  next
    from h3 show "\<turnstile> \<box>P \<and> \<box>\<box>[N]_v \<and> \<box>F \<longrightarrow> \<diamond>Enabled \<langle>A\<rangle>_v" by simp
  qed (rule h4)
  thus ?thesis by simp
qed

text \<open>
  Lamport proposes the following rule as an introduction rule for \<open>WF\<close> formulas.
\<close>

theorem WF2:
  assumes h1: "|~ \<langle>N \<and> B\<rangle>_f \<longrightarrow> \<langle>M\<rangle>_g"
      and h2: "|~ P \<and> \<circle>P \<and> \<langle>N \<and> A\<rangle>_f \<longrightarrow> B"
      and h3: "\<turnstile> P \<and> Enabled \<langle>M\<rangle>_g \<longrightarrow> Enabled \<langle>A\<rangle>_f"
      and h4: "\<turnstile> \<box>[N \<and> \<not>B]_f \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<longrightarrow> \<diamond>\<box>P"
  shows "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<box>F \<longrightarrow> WF(M)_g"
proof -
  have "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
  proof -
    have 1: "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow> \<diamond>\<box>P"
    proof -
      have A: "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow>
                 \<box>(\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> \<diamond>\<box>(\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g)"
        unfolding STL6[int_rewrite] (* important to do this before STL5 is applied *)
        by (auto simp: STL5[int_rewrite] dualization_rew)
      have B: "\<turnstile> \<box>(\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> \<diamond>\<box>(\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g) \<longrightarrow>
                 \<diamond>((\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> \<box>(\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g))"
        by (rule SE2)
      from lift_imp_trans[OF A B]
      have "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<box>F \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow>
              \<diamond>((\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> (\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g))"
        by (simp add: STL5[int_rewrite])
      moreover
      from h1 have "|~ [N]_f \<longrightarrow> [\<not>M]_g \<longrightarrow> [N \<and> \<not>B]_f" by (auto simp: actrans_def angle_actrans_def)
      hence "\<turnstile> \<box>[[N]_f]_f \<longrightarrow> \<box>[[\<not>M]_g \<longrightarrow> [N \<and> \<not>B]_f]_f" by (rule M2)
      from lift_imp_trans[OF this ax4] have "\<turnstile> \<box>[N]_f \<and> \<box>[\<not>M]_g \<longrightarrow> \<box>[N \<and> \<not>B]_f"
        by (force intro: T4[unlift_rule])
      with h4 have "\<turnstile> (\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> (\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g) \<longrightarrow> \<diamond>\<box>P"
        by force
      from STL4_eve[OF this]
      have "\<turnstile> \<diamond>((\<box>[N]_f \<and> WF(A)_f \<and> \<box>F) \<and> (\<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g)) \<longrightarrow> \<diamond>\<box>P" by simp
      ultimately
      show ?thesis by (rule lift_imp_trans)
    qed
    have 2: "\<turnstile> \<box>[N]_f \<and> WF(A)_f \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> \<diamond>\<box>P \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
    proof -
      have A: "\<turnstile> \<diamond>\<box>P \<and> \<diamond>\<box>Enabled \<langle>M\<rangle>_g \<and> WF(A)_f \<longrightarrow> \<box>\<diamond>\<langle>A\<rangle>_f"
        using h3[THEN STL4, THEN STL4_eve] by (auto simp: STL6[int_rewrite] WeakF_def)
      have B: "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
      proof -
        from M1[of P f] have "\<turnstile> \<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (force intro: AA29[unlift_rule])
        hence "\<turnstile> \<diamond>\<box>(\<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f) \<longrightarrow> \<diamond>\<box>\<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (rule STL4_eve[OF STL4])
        hence "\<turnstile> \<diamond>\<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (simp add: STL6[int_rewrite])
        with AA29[of N f A]
        have B1: "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f" by force
        from h2 have "|~ \<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f \<longrightarrow> \<langle>N \<and> B\<rangle>_f"
          by (auto simp: angle_actrans_sem[unlifted])
        from B1 this[THEN AA25, THEN STL4] have "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>N \<and> B\<rangle>_f"
          by (rule lift_imp_trans)
        moreover
        have "\<turnstile> \<box>\<diamond>\<langle>N \<and> B\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g" by (rule h1[THEN AA25, THEN STL4])
        ultimately show ?thesis by (rule lift_imp_trans)
      qed
      from A B show ?thesis by force
    qed
    from 1 2 show ?thesis by force
  qed
  thus ?thesis by (auto simp: WeakF_def)
qed

text \<open>
  Lamport proposes an analogous theorem for introducing strong fairness, and its
  proof is very similar, in fact, it was obtained by copy and paste, with minimal
  modifications.
\<close>

theorem SF2:
  assumes h1: "|~ \<langle>N \<and> B\<rangle>_f \<longrightarrow> \<langle>M\<rangle>_g"
      and h2: "|~ P \<and> \<circle>P \<and> \<langle>N \<and> A\<rangle>_f \<longrightarrow> B"
      and h3: "\<turnstile> P \<and> Enabled \<langle>M\<rangle>_g \<longrightarrow> Enabled \<langle>A\<rangle>_f"
      and h4: "\<turnstile> \<box>[N \<and> \<not>B]_f \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<longrightarrow> \<diamond>\<box>P"
  shows "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>F \<longrightarrow> SF(M)_g"
proof -
  have "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
  proof -
    have 1: "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow> \<diamond>\<box>P"
    proof -
      have A: "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow>
                 \<box>(\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> \<diamond>\<box>(\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g)"
        unfolding STL6[int_rewrite] (* important to do this before STL5 is applied *)
        by (auto simp: STL5[int_rewrite] dualization_rew)
      have B: "\<turnstile> \<box>(\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> \<diamond>\<box>(\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g) \<longrightarrow>
                 \<diamond>((\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> \<box>(\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g))"
        by (rule SE2)
      from lift_imp_trans[OF A B]
      have "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>F \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<not>\<box>\<diamond>\<langle>M\<rangle>_g \<longrightarrow>
              \<diamond>((\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> (\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g))"
        by (simp add: STL5[int_rewrite])
      moreover
      from h1 have "|~ [N]_f \<longrightarrow> [\<not>M]_g \<longrightarrow> [N \<and> \<not>B]_f" by (auto simp: actrans_def angle_actrans_def)
      hence "\<turnstile> \<box>[[N]_f]_f \<longrightarrow> \<box>[[\<not>M]_g \<longrightarrow> [N \<and> \<not>B]_f]_f" by (rule M2)
      from lift_imp_trans[OF this ax4] have "\<turnstile> \<box>[N]_f \<and> \<box>[\<not>M]_g \<longrightarrow> \<box>[N \<and> \<not>B]_f"
        by (force intro: T4[unlift_rule])
      with h4 have "\<turnstile> (\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> (\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g) \<longrightarrow> \<diamond>\<box>P"
        by force
      from STL4_eve[OF this]
      have "\<turnstile> \<diamond>((\<box>[N]_f \<and> SF(A)_f \<and> \<box>F) \<and> (\<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<box>[\<not>M]_g)) \<longrightarrow> \<diamond>\<box>P" by simp
      ultimately
      show ?thesis by (rule lift_imp_trans)
    qed
    have 2: "\<turnstile> \<box>[N]_f \<and> SF(A)_f \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> \<diamond>\<box>P \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
    proof -
      have "\<turnstile> \<box>\<diamond>(P \<and> Enabled \<langle>M\<rangle>_g) \<and> SF(A)_f \<longrightarrow> \<box>\<diamond>\<langle>A\<rangle>_f"
        using h3[THEN STL4_eve, THEN STL4] by (auto simp: StrongF_def)
      with E28 have A: "\<turnstile> \<diamond>\<box>P \<and> \<box>\<diamond>Enabled \<langle>M\<rangle>_g \<and> SF(A)_f \<longrightarrow> \<box>\<diamond>\<langle>A\<rangle>_f"
        by force
      have B: "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g"
      proof -
        from M1[of P f] have "\<turnstile> \<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (force intro: AA29[unlift_rule])
        hence "\<turnstile> \<diamond>\<box>(\<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f) \<longrightarrow> \<diamond>\<box>\<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (rule STL4_eve[OF STL4])
        hence "\<turnstile> \<diamond>\<box>P \<and> \<box>\<diamond>\<langle>N \<and> A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f"
          by (simp add: STL6[int_rewrite])
        with AA29[of N f A]
        have B1: "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f" by force
        from h2 have "|~ \<langle>(P \<and> \<circle>P) \<and> (N \<and> A)\<rangle>_f \<longrightarrow> \<langle>N \<and> B\<rangle>_f"
          by (auto simp: angle_actrans_sem[unlifted])
        from B1 this[THEN AA25, THEN STL4] have "\<turnstile> \<box>[N]_f \<and> \<diamond>\<box>P \<and>  \<box>\<diamond>\<langle>A\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>N \<and> B\<rangle>_f"
          by (rule lift_imp_trans)
        moreover
        have "\<turnstile> \<box>\<diamond>\<langle>N \<and> B\<rangle>_f \<longrightarrow> \<box>\<diamond>\<langle>M\<rangle>_g" by (rule h1[THEN AA25, THEN STL4])
        ultimately show ?thesis by (rule lift_imp_trans)
      qed
      from A B show ?thesis by force
    qed
    from 1 2 show ?thesis by force
  qed
  thus ?thesis by (auto simp: StrongF_def)
qed

text \<open>This is the lattice rule from TLA\<close>

theorem wf_leadsto:
  assumes h1: "wf r"
      and h2: "\<And>x. \<turnstile> F x \<leadsto> (G \<or> (\<exists>y. #((y,x) \<in> r) \<and> F y))"
  shows       "\<turnstile> F x \<leadsto> G"
using h1
proof (rule wf_induct)
  fix x
  assume ih: "\<forall>y. (y, x) \<in> r \<longrightarrow> (\<turnstile> F y \<leadsto> G)"
  show "\<turnstile> F x \<leadsto> G"
  proof -
    from ih have "\<turnstile> (\<exists>y. #((y,x) \<in> r) \<and> F y) \<leadsto> G"
      by (force simp: LT21[int_rewrite] LT33[int_rewrite])
    with h2 show ?thesis by (force intro: LT19[unlift_rule])
  qed
qed

subsection "Stuttering Invariance"

theorem stut_Enabled: "STUTINV Enabled \<langle>F\<rangle>_v"
  by (auto simp: enabled_def stutinv_def dest!: sim_first)

theorem stut_WF: "NSTUTINV F \<Longrightarrow> STUTINV WF(F)_v"
  by (auto simp: WeakF_def stut_Enabled bothstutinvs)

theorem stut_SF: "NSTUTINV F \<Longrightarrow> STUTINV SF(F)_v"
  by (auto simp: StrongF_def stut_Enabled bothstutinvs)

lemmas livestutinv = stut_WF stut_SF stut_Enabled

end
