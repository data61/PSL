(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section "A Proof System for TLA* "

theory Rules 
imports PreFormulas  
begin

text\<open>
  We prove soundness of the proof system of \tlastar{}, from which the system
  verification rules from Lamport's original TLA paper will be derived. 
  This theory is still state-independent, thus state-dependent enableness proofs,
  required for proofs based on fairness assumptions, and flexible quantification,
  are not discussed here. 

  The \tlastar{} paper \cite{Merz99} suggest both a \emph{hetereogeneous} and a 
  \emph{homogenous} proof system for \tlastar{}.
  The homogeneous version eliminates the auxiliary definitions from the
  \<open>Preformula\<close> theory, creating a single provability relation.
  This axiomatisation is based on the fact that a pre-formula can only be used
  via the \<open>sq\<close> rule. In a nutshell, \<open>sq\<close> is applied to
  \<open>pax1\<close> to \<open>pax5\<close>, and \<open>nex\<close>, \<open>pre\<close> and \<open>pmp\<close>
  are changed to accommodate this. It is argued that while the hetereogenous version
  is easier to understand, the homogenous system avoids the introduction of an
  auxiliary provability relation. However, the price to pay is that reasoning about
  pre-formulas (in particular, actions) has to be performed in the scope of
  temporal operators such as \<open>\<box>[P]_v\<close>, which is notationally quite heavy,
  We prefer here the heterogeneous approach, which exposes the pre-formulas and
  lets us use standard HOL rules more directly.
\<close>

subsection "The Basic Axioms"

theorem fmp: assumes "\<turnstile> F" and "\<turnstile> F \<longrightarrow> G" shows "\<turnstile> G"
  using assms[unlifted] by auto

theorem pmp: assumes "|~ F" and "|~ F \<longrightarrow> G" shows "|~ G"
  using assms[unlifted] by auto

theorem sq: assumes "|~ P" shows "\<turnstile> \<box>[P]_v"
  using assms[unlifted] by (auto simp: action_def)

theorem pre: assumes "\<turnstile> F" shows "|~ F"
  using assms by auto

theorem nex: assumes h1: "\<turnstile> F" shows "|~ \<circle>F"
  using assms by (auto simp: nexts_def)

theorem ax0: "\<turnstile> # True"
  by auto

theorem ax1: "\<turnstile> \<box>F \<longrightarrow> F"
proof (clarsimp simp: always_def)
  fix w
  assume "\<forall>n. (w |\<^sub>s n) \<Turnstile> F"
  hence "(w |\<^sub>s 0) \<Turnstile> F" ..
  thus "w \<Turnstile> F" by simp
qed

theorem ax2: "\<turnstile> \<box>F \<longrightarrow> \<box>[\<box>F]_v"
  by (auto simp: always_def action_def suffix_plus)

theorem ax3:
  assumes H: "|~ F \<and> Unchanged v \<longrightarrow> \<circle>F" 
  shows "\<turnstile> \<box>[F \<longrightarrow> \<circle>F]_v \<longrightarrow> (F \<longrightarrow> \<box>F)"
proof (clarsimp simp: always_def)
  fix w n
  assume a1: "w \<Turnstile> \<box>[F \<longrightarrow> \<circle>F]_v" and  a2: "w \<Turnstile> F"
  show "(w |\<^sub>s n) \<Turnstile> F"
  proof (induct n)
    from a2 show "(w |\<^sub>s 0) \<Turnstile> F" by simp
  next
    fix m
    assume a3: "(w |\<^sub>s m) \<Turnstile> F"
    with a1 H[unlifted] show "(w |\<^sub>s (Suc m)) \<Turnstile> F"
      by (auto simp: nexts_def action_def tail_suffix_suc)
  qed
qed

theorem ax4: "\<turnstile> \<box>[P \<longrightarrow> Q]_v \<longrightarrow> (\<box>[P]_v \<longrightarrow> \<box>[Q]_v)"
  by (force simp: action_def)

theorem ax5: "\<turnstile> \<box>[v` \<noteq> $v]_v"
  by (auto simp: action_def unch_def)

theorem pax0: "|~ # True"
  by auto

theorem pax1 [simp_unl]: "|~ (\<circle>\<not>F) = (\<not>\<circle>F)"
  by (auto simp: nexts_def)

theorem pax2: "|~ \<circle>(F \<longrightarrow> G) \<longrightarrow> (\<circle>F \<longrightarrow> \<circle>G)"
  by (auto simp: nexts_def)

theorem pax3: "|~ \<box>F \<longrightarrow> \<circle>\<box>F"
  by (auto simp: always_def nexts_def tail_def suffix_plus)

theorem pax4: "|~ \<box>[P]_v = ([P]_v \<and> \<circle>\<box>[P]_v)"
proof (auto)
  fix w
  assume "w \<Turnstile> \<box>[P]_v"
  from this[unfolded action_def] have "((w |\<^sub>s 0) \<Turnstile> P) \<or> ((w |\<^sub>s 0) \<Turnstile> Unchanged v)" ..
  thus "w \<Turnstile> [P]_v" by (simp add: actrans_def)
next
  fix w
  assume "w \<Turnstile> \<box>[P]_v"
  thus "w \<Turnstile> \<circle>\<box>[P]_v" by (auto simp: nexts_def action_def tail_def suffix_plus)
next
  fix w
  assume 1: "w \<Turnstile> [P]_v" and 2: "w \<Turnstile> \<circle>\<box>[P]_v"
  show "w \<Turnstile> \<box>[P]_v"
  proof (auto simp: action_def)
    fix i
    assume 3: "\<not> ((w |\<^sub>s i) \<Turnstile> Unchanged v)"
    show "(w |\<^sub>s i) \<Turnstile> P"
    proof (cases i)
      assume "i = 0"
      with 1 3 show ?thesis by (simp add: actrans_def)
    next
      fix j
      assume "i = Suc j"
      with 2 3 show ?thesis by (auto simp: nexts_def action_def tail_def suffix_plus)
    qed
  qed
qed

theorem pax5: "|~ \<circle>\<box>F \<longrightarrow> \<box>[\<circle>F]_v"
  by (auto simp: nexts_def always_def action_def tail_def suffix_plus)

text \<open>
  Theorem to show that universal quantification distributes over the always
  operator. Since the \tlastar{} paper only addresses the propositional fragment,
  this theorem does not appear there.
\<close>

theorem allT:  "\<turnstile> (\<forall>x. \<box>(F x)) = (\<box>(\<forall>x. F x))"
  by (auto simp: always_def)

theorem allActT:  "\<turnstile> (\<forall>x. \<box>[F x]_v) = (\<box>[(\<forall>x. F x)]_v)"
  by (force simp: action_def)

subsection "Derived Theorems"

text\<open>
  This section includes some derived theorems based on the axioms, taken
  from the \tlastar{} paper~\cite{Merz99}. We mimic the proofs given there
  and avoid semantic reasoning whenever possible.

  The \<open>alw\<close> theorem of~\cite{Merz99} states that if F holds
  in all worlds then it always holds, i.e. $F \vDash \Box F$. However,
  the derivation of this theorem (using the proof rules above) 
  relies on access of the set of free variables (FV), which is not
  available in a shallow encoding.

  However, we can prove a similar rule \<open>alw2\<close> using an additional
  hypothesis @{term "|~ F \<and> Unchanged v \<longrightarrow> \<circle>F"}.
\<close>

theorem alw2: 
  assumes h1: "\<turnstile> F" and h2: "|~ F \<and> Unchanged v \<longrightarrow> \<circle>F"
  shows "\<turnstile> \<box>F"
proof -
  from h1 have g2: "|~ \<circle>F" by (rule nex)
  hence g3: "|~ F \<longrightarrow> \<circle>F" by auto
  hence g4:"\<turnstile> \<box>[(F \<longrightarrow> \<circle>F)]_v" by (rule sq)
  from h2 have "\<turnstile> \<box>[(F \<longrightarrow> \<circle>F)]_v \<longrightarrow> F \<longrightarrow> \<box>F" by (rule ax3)
  with g4[unlifted] have g5: "\<turnstile> F \<longrightarrow> \<box>F" by auto
  with h1[unlifted] show ?thesis by auto
qed

text\<open>
  Similar theorem, assuming that @{term "F"} is stuttering invariant.
\<close>

theorem alw3:
  assumes h1: "\<turnstile> F" and h2: "stutinv F"
  shows "\<turnstile> \<box>F"
proof -
  from h2 have "|~ F \<and> Unchanged id \<longrightarrow> \<circle>F"  by (rule pre_id_unch)
  with h1 show ?thesis by (rule alw2)
qed

text\<open>
  In a deep embedding, we could prove that all (proper) \tlastar{}
  formulas are stuttering invariant and then get rid of the second
  hypothesis of rule \<open>alw3\<close>. In fact, the rule is even true
  for pre-formulas, as shown by the following rule, whose proof relies
  on semantical reasoning.
\<close>
theorem alw: assumes H1: "\<turnstile> F" shows "\<turnstile> \<box>F"
  using H1 by (auto simp: always_def)

theorem alw_valid_iff_valid: "(\<turnstile> \<box>F) = (\<turnstile> F)"
proof
  assume "\<turnstile> \<box>F"
  from this ax1 show "\<turnstile> F" by (rule fmp)
qed (rule alw)

text \<open>
  \cite{Merz99} proves the following theorem using the deduction theorem of
  \tlastar{}: \<open>(\<turnstile> F \<Longrightarrow> \<turnstile> G) \<Longrightarrow> \<turnstile> []F \<longrightarrow> G\<close>, which can only be
  proved by induction on the formula structure, in a deep embedding.
\<close>

theorem T1[simp_unl]: "\<turnstile> \<box>\<box>F = []F"
proof (auto simp: always_def suffix_plus)
  fix w n
  assume "\<forall>m k. (w |\<^sub>s (k+m)) \<Turnstile> F"
  hence "(w |\<^sub>s (n+0)) \<Turnstile> F" by blast
  thus "(w |\<^sub>s n) \<Turnstile> F" by simp
qed

theorem T2[simp_unl]: "\<turnstile> \<box>\<box>[P]_v = \<box>[P]_v"
proof -
  have 1: "|~ \<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v" using pax4 by force
  hence "\<turnstile> \<box>[\<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v]_v" by (rule sq)
  moreover
  have "\<turnstile> \<box>[ \<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v ]_v \<longrightarrow> \<box>[P]_v \<longrightarrow> \<box>\<box>[P]_v"
    by (rule ax3) (auto elim: 1[unlift_rule])
  moreover
  have "\<turnstile> \<box>\<box>[P]_v \<longrightarrow> \<box>[P]_v" by (rule ax1)
  ultimately show ?thesis by force
qed

theorem T3[simp_unl]: "\<turnstile> \<box>[[P]_v]_v = \<box>[P]_v"
proof -
  have "|~ P \<longrightarrow> [P]_v" by (auto simp: actrans_def)
  hence "\<turnstile> \<box>[(P \<longrightarrow> [P]_v)]_v" by (rule sq)
  with ax4 have "\<turnstile> \<box>[P]_v \<longrightarrow> \<box>[[P]_v]_v" by force
  moreover
  have "|~ [P]_v \<longrightarrow> v`\<noteq> $v \<longrightarrow> P" by (auto simp: unch_def actrans_def)
  hence "\<turnstile> \<box>[[P]_v \<longrightarrow> v`\<noteq> $v \<longrightarrow> P]_v" by (rule sq)
  with ax5 have "\<turnstile> \<box>[[P]_v]_v \<longrightarrow> \<box>[P]_v" by (force intro: ax4[unlift_rule])
  ultimately show ?thesis by force
qed

theorem M2: 
  assumes h: "|~ F \<longrightarrow> G"
  shows "\<turnstile> \<box>[F]_v \<longrightarrow> \<box>[G]_v"
  using sq[OF h] ax4 by force

theorem N1:
  assumes h: "\<turnstile> F \<longrightarrow> G"
  shows "|~ \<circle>F \<longrightarrow> \<circle>G"
  by (rule pmp[OF nex[OF h] pax2])

theorem T4: "\<turnstile> \<box>[P]_v \<longrightarrow> \<box>[[P]_v]_w"
proof -
  have "\<turnstile> \<box>\<box>[P]_v \<longrightarrow> \<box>[\<box>\<box>[P]_v]_w" by (rule ax2)
  moreover
  from pax4 have "|~ \<box>\<box>[P]_v \<longrightarrow> [P]_v" unfolding T2[int_rewrite] by force
  hence "\<turnstile> \<box>[\<box>\<box>[P]_v]_w \<longrightarrow> \<box>[[P]_v]_w" by (rule M2)
  ultimately show ?thesis unfolding T2[int_rewrite] by (rule lift_imp_trans)
qed

theorem T5: "\<turnstile> \<box>[[P]_w]_v \<longrightarrow> \<box>[[P]_v]_w"
proof -
  have "|~ [[P]_w]_v \<longrightarrow> [[P]_v]_w" by (auto simp: actrans_def)
  hence "\<turnstile> \<box>[[[P]_w]_v]_w \<longrightarrow> \<box>[[[P]_v]_w]_w" by (rule M2)
  with T4 show ?thesis unfolding T3[int_rewrite] by (rule lift_imp_trans)
qed

theorem T6: "\<turnstile> \<box>F \<longrightarrow> \<box>[\<circle>F]_v"
proof -
  from ax1 have "|~ \<circle>(\<box>F \<longrightarrow> F)" by (rule nex)
  with pax2 have "|~ \<circle>\<box>F \<longrightarrow> \<circle>F" by force
  with pax3 have "|~ \<box>F \<longrightarrow> \<circle>F" by (rule pref_imp_trans)
  hence "\<turnstile> \<box>[\<box>F]_v \<longrightarrow> \<box>[\<circle>F]_v" by (rule M2)
  with ax2 show ?thesis by (rule lift_imp_trans)
qed

theorem T7: 
  assumes h: "|~ F \<and> Unchanged v \<longrightarrow> \<circle>F"
  shows "|~ (F \<and> \<circle>\<box>F) = \<box>F"
proof -
  have "\<turnstile> \<box>[\<circle>F \<longrightarrow> F \<longrightarrow> \<circle>F]_v" by (rule sq) auto
  with ax4 have "\<turnstile> \<box>[\<circle>F]_v \<longrightarrow> \<box>[(F \<longrightarrow> \<circle>F)]_v" by force
  with ax3[OF h, unlifted] have "\<turnstile> \<box>[\<circle>F]_v \<longrightarrow> (F \<longrightarrow> \<box>F)" by force
  with pax5 have "|~ F \<and> \<circle>\<box>F \<longrightarrow> \<box>F" by force
  with ax1[of "TEMP F",unlifted] pax3[of "TEMP F",unlifted] show ?thesis by force
qed

theorem T8: "|~ \<circle>(F \<and> G) = (\<circle>F \<and> \<circle>G)"
proof -
  have "|~ \<circle>(F \<and> G) \<longrightarrow> \<circle>F" by (rule N1) auto
  moreover
  have "|~ \<circle>(F \<and> G) \<longrightarrow> \<circle>G" by (rule N1) auto
  moreover
  have "\<turnstile> F \<longrightarrow> G \<longrightarrow> F \<and> G" by auto
  from nex[OF this] have "|~ \<circle>F \<longrightarrow> \<circle>G \<longrightarrow> \<circle>(F \<and> G)" 
    by (force intro: pax2[unlift_rule])
  ultimately show ?thesis by force
qed

lemma T9: "|~ \<box>[A]_v \<longrightarrow> [A]_v"
  using pax4 by force

theorem H1: 
  assumes h1: "\<turnstile> \<box>[P]_v" and h2: "\<turnstile> \<box>[P \<longrightarrow> Q]_v" 
  shows "\<turnstile> \<box>[Q]_v"
  using assms ax4[unlifted] by force

theorem H2: assumes h1: "\<turnstile> F" shows "\<turnstile> \<box>[F]_v"
  using h1 by (blast dest: pre sq)

theorem H3: 
  assumes h1: "\<turnstile> \<box>[P \<longrightarrow> Q]_v" and h2: "\<turnstile> \<box>[Q \<longrightarrow> R]_v"
  shows "\<turnstile> \<box>[P \<longrightarrow> R]_v"
proof -
  have "|~ (P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> R)" by auto
  hence "\<turnstile> \<box>[(P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> R)]_v" by (rule sq)
  with h1 have "\<turnstile> \<box>[(Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> R)]_v" by (rule H1)
  with h2 show ?thesis by (rule H1)
qed

theorem H4: "\<turnstile> \<box>[[P]_v \<longrightarrow> P]_v"
proof -
  have "|~ v` \<noteq> $v \<longrightarrow> ([P]_v \<longrightarrow> P)" by (auto simp: unch_def actrans_def)
  hence "\<turnstile> \<box>[v` \<noteq> $v \<longrightarrow> ([P]_v \<longrightarrow> P)]_v" by (rule sq)
  with ax5 show ?thesis by (rule H1)
qed

theorem H5: "\<turnstile> \<box>[\<box>F \<longrightarrow> \<circle>\<box>F]_v"
  by (rule pax3[THEN sq])

subsection "Some other useful derived theorems"

theorem P1: "|~ \<box>F \<longrightarrow> \<circle>F"
proof -
  have "|~ \<circle>\<box>F \<longrightarrow> \<circle>F" by (rule N1[OF ax1])
  with pax3 show ?thesis by (rule pref_imp_trans)
qed

theorem P2: "|~ \<box>F \<longrightarrow> F \<and> \<circle>F"
  using ax1[of F] P1[of F] by force

theorem P4: "\<turnstile> \<box>F \<longrightarrow> \<box>[F]_v"
proof -
  have "\<turnstile> \<box>[\<box>F]_v \<longrightarrow> \<box>[F]_v" by (rule M2[OF pre[OF ax1]])
  with ax2 show ?thesis by (rule lift_imp_trans)
qed

theorem P5: "\<turnstile> \<box>[P]_v \<longrightarrow> \<box>[\<box>[P]_v]_w"
proof -
  have "\<turnstile> \<box>\<box>[P]_v \<longrightarrow> \<box>[\<box>[P]_v]_w" by (rule P4)
  thus ?thesis by (unfold T2[int_rewrite])
qed

theorem M0: "\<turnstile> \<box>F \<longrightarrow> \<box>[F \<longrightarrow> \<circle>F]_v" 
proof -
  from P1 have "|~ \<box>F \<longrightarrow> F \<longrightarrow> \<circle>F" by force 
  hence "\<turnstile> \<box>[\<box>F]_v \<longrightarrow> \<box>[F \<longrightarrow> \<circle>F]_v" by (rule M2)
  with ax2 show ?thesis by (rule lift_imp_trans)
qed

theorem M1: "\<turnstile> \<box>F \<longrightarrow> \<box>[F \<and> \<circle>F]_v"
proof -
  have "|~ \<box>F \<longrightarrow> F \<and> \<circle>F" by (rule P2)
  hence "\<turnstile> \<box>[\<box>F]_v \<longrightarrow> \<box>[F \<and> \<circle>F]_v" by (rule M2)
  with ax2 show ?thesis by (rule lift_imp_trans)
qed

theorem M3: assumes h: "\<turnstile> F" shows "\<turnstile> \<box>[\<circle>F]_v"
  using alw[OF h] T6 by (rule fmp)

lemma M4: "\<turnstile> \<box>[\<circle>(F \<and> G) = (\<circle>F \<and> \<circle>G)]_v"
  by (rule sq[OF T8])

theorem M5: "\<turnstile> \<box>[ \<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v ]_w"
proof (rule sq)
  show "|~ \<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v" by (auto simp: pax4[unlifted])
qed

theorem M6: "\<turnstile> \<box>[F \<and> G]_v \<longrightarrow> \<box>[F]_v \<and> \<box>[G]_v"
proof -
  have "\<turnstile> \<box>[F \<and> G]_v \<longrightarrow> \<box>[F]_v" by (rule M2) auto
  moreover
  have "\<turnstile> \<box>[F \<and> G]_v \<longrightarrow> \<box>[G]_v" by (rule M2) auto
  ultimately show ?thesis by force
qed

theorem M7: "\<turnstile> \<box>[F]_v \<and> \<box>[G]_v \<longrightarrow> \<box>[F \<and> G]_v"
proof -
  have "|~ F \<longrightarrow> G \<longrightarrow> F \<and> G" by auto
  hence "\<turnstile> \<box>[F]_v \<longrightarrow> \<box>[G \<longrightarrow> F \<and> G]_v" by (rule M2)
  with ax4 show ?thesis by force
qed

theorem M8: "\<turnstile> \<box>[F \<and> G]_v = (\<box>[F]_v \<and> \<box>[G]_v)"
  by (rule int_iffI[OF M6 M7])

theorem M9: "|~ \<box>F \<longrightarrow> F \<and> \<circle>\<box>F"
  using pre[OF ax1[of "F"]] pax3[of "F"] by force

theorem M10: 
  assumes h: "|~ F \<and> Unchanged v \<longrightarrow> \<circle>F"
  shows "|~ F \<and> \<circle>\<box>F \<longrightarrow> \<box>F"
  using T7[OF h] by auto

theorem M11:
  assumes h: "|~ [A]_f \<longrightarrow> [B]_g"
  shows "\<turnstile> \<box>[A]_f \<longrightarrow> \<box>[B]_g"
proof -
  from h have "\<turnstile> \<box>[[A]_f]_g \<longrightarrow> \<box>[[B]_g]_g" by (rule M2)
  with T4 show ?thesis by force
qed

theorem M12: "\<turnstile> (\<box>[A]_f \<and> \<box>[B]_g) = \<box>[[A]_f \<and> [B]_g]_(f,g)"
proof -
  have "\<turnstile> \<box>[A]_f \<and> \<box>[B]_g \<longrightarrow> \<box>[[A]_f \<and> [B]_g]_(f,g)"
    by (auto simp: M8[int_rewrite] elim: T4[unlift_rule])
  moreover
  have "|~ [[A]_f \<and> [B]_g]_(f,g) \<longrightarrow> [A]_f"
    by (auto simp: actrans_def unch_def all_before_eq all_after_eq)
  hence "\<turnstile> \<box>[[A]_f \<and> [B]_g]_(f,g) \<longrightarrow> \<box>[A]_f" by (rule M11)
  moreover
  have "|~ [[A]_f \<and> [B]_g]_(f,g) \<longrightarrow> [B]_g"
    by (auto simp: actrans_def unch_def all_before_eq all_after_eq)
  hence "\<turnstile> \<box>[[A]_f \<and> [B]_g]_(f,g) \<longrightarrow> \<box>[B]_g"
    by (rule M11)
  ultimately show ?thesis by force
qed

text \<open>
  We now derive Lamport's 6 simple temporal logic rules (STL1)-(STL6) \cite{Lamport94}.
  Firstly, STL1 is the same as @{thm alw} derived above.
\<close>

lemmas STL1 = alw

text \<open>
  STL2 and STL3 have also already been derived.
\<close>

lemmas STL2 = ax1 

lemmas STL3 = T1

text \<open>
  As with the derivation of @{thm alw}, a purely syntactic derivation of 
  (STL4) relies on an additional argument -- either using \<open>Unchanged\<close>
  or \<open>STUTINV\<close>.
\<close>

theorem STL4_2: 
  assumes h1: "\<turnstile> F \<longrightarrow> G" and h2: "|~ G \<and> Unchanged v \<longrightarrow> \<circle>G"
  shows "\<turnstile> \<box>F \<longrightarrow> \<box>G"
proof -
  from ax1[of F] h1 have "\<turnstile> \<box>F \<longrightarrow> G" by (rule lift_imp_trans)
  moreover
  from h1 have "|~ \<circle>F \<longrightarrow> \<circle>G" by (rule N1)
  hence "|~ \<circle>F \<longrightarrow> G \<longrightarrow> \<circle>G" by auto
  hence "\<turnstile> \<box>[\<circle>F]_v \<longrightarrow> \<box>[G \<longrightarrow> \<circle>G]_v" by (rule M2)
  with T6 have "\<turnstile> \<box>F \<longrightarrow> \<box>[G \<longrightarrow> \<circle>G]_v" by (rule lift_imp_trans)
  moreover
  from h2 have "\<turnstile> \<box>[G \<longrightarrow> \<circle>G]_v \<longrightarrow> G \<longrightarrow> \<box>G" by (rule ax3)
  ultimately
  show ?thesis by force
qed

lemma STL4_3:
  assumes h1: "\<turnstile> F \<longrightarrow> G" and h2: "STUTINV G"
  shows "\<turnstile> \<box>F \<longrightarrow> \<box>G"
using h1 h2[THEN pre_id_unch] by (rule STL4_2)

text \<open>Of course, the original rule can be derived semantically\<close>

lemma STL4: assumes h: "\<turnstile> F \<longrightarrow> G" shows "\<turnstile> \<box>F \<longrightarrow> \<box>G"
  using h by (force simp: always_def)

text \<open>Dual rule for \<open>\<diamond>\<close>\<close>

lemma STL4_eve: assumes h: "\<turnstile> F \<longrightarrow> G" shows "\<turnstile> \<diamond>F \<longrightarrow> \<diamond>G"
  using h by (force simp: eventually_defs)

text\<open>
  Similarly, a purely syntactic derivation of (STL5) requires extra hypotheses.
\<close>

theorem STL5_2: 
  assumes h1: "|~ F \<and> Unchanged f \<longrightarrow> \<circle>F"
      and h2: "|~ G \<and> Unchanged g \<longrightarrow> \<circle>G"
  shows "\<turnstile> \<box>(F \<and> G) = (\<box>F \<and> \<box>G)"
proof (rule int_iffI)
  have "\<turnstile> F \<and> G \<longrightarrow> F" by auto
  from this h1 have "\<turnstile> \<box>(F \<and> G) \<longrightarrow> \<box>F" by (rule STL4_2)
  moreover
  have "\<turnstile> F \<and> G \<longrightarrow> G" by auto
  from this h2 have "\<turnstile> \<box>(F \<and> G) \<longrightarrow> \<box>G" by (rule STL4_2)
  ultimately show "\<turnstile> \<box>(F \<and> G) \<longrightarrow> \<box>F \<and> \<box>G" by force
next
  have "|~ Unchanged (f,g) \<longrightarrow> Unchanged f \<and> Unchanged g" by (auto simp: unch_defs)
  with h1[unlifted] h2[unlifted] T8[of F G, unlifted]
  have h3: "|~ (F \<and> G) \<and> Unchanged (f,g) \<longrightarrow> \<circle>(F \<and> G)" by force
  from ax1[of F] ax1[of G] have "\<turnstile> \<box>F \<and> \<box>G \<longrightarrow> F \<and> G" by force
  moreover
  from ax2[of F] ax2[of G] have "\<turnstile> \<box>F \<and> \<box>G \<longrightarrow> \<box>[\<box>F]_(f,g) \<and> \<box>[\<box>G]_(f,g)" by force
  with M8 have "\<turnstile> \<box>F \<and> \<box>G \<longrightarrow> \<box>[\<box>F \<and> \<box>G]_(f,g)" by force
  moreover
  from P1[of F] P1[of G] have "|~ \<box>F \<and> \<box>G \<longrightarrow> F \<and> G \<longrightarrow> \<circle>(F \<and> G)"
    unfolding T8[int_rewrite] by force
  hence "\<turnstile> \<box>[ \<box>F \<and> \<box>G ]_(f,g) \<longrightarrow> \<box>[F \<and> G \<longrightarrow> \<circle>(F \<and> G)]_(f,g)" by (rule M2)
  from this ax3[OF h3] have "\<turnstile> \<box>[ \<box>F \<and> \<box>G ]_(f,g) \<longrightarrow> F \<and> G \<longrightarrow> \<box>(F \<and> G)"
    by (rule lift_imp_trans)
  ultimately show "\<turnstile> \<box>F \<and> \<box>G \<longrightarrow> \<box>(F \<and> G)" by force
qed

theorem STL5_21: 
  assumes h1: "stutinv F" and h2: "stutinv G"
  shows "\<turnstile> \<box>(F \<and> G) = (\<box>F \<and> \<box>G)"
  using h1[THEN pre_id_unch] h2[THEN pre_id_unch] by (rule STL5_2)

text \<open>We also derive STL5 semantically.\<close>

lemma STL5: "\<turnstile> \<box>(F \<and> G) = (\<box>F \<and> \<box>G)" 
  by (auto simp: always_def)

text \<open>Elimination rule corresponding to \<open>STL5\<close> in unlifted form.\<close>

lemma box_conjE:
  assumes "s \<Turnstile> \<box>F" and "s \<Turnstile> \<box>G" and "s \<Turnstile> \<box>(F \<and> G) \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: STL5[unlifted])

lemma box_thin:
  assumes h1: "s \<Turnstile> \<box>F" and h2: "PROP W"
  shows "PROP W"
  using h2 .

text \<open>Finally, we derive STL6 (only semantically)\<close>

lemma STL6: "\<turnstile> \<diamond>\<box>(F \<and> G) = (\<diamond>\<box>F \<and> \<diamond>\<box>G)"
proof auto
  fix w
  assume a1: "w \<Turnstile> \<diamond>\<box>F" and  a2: "w \<Turnstile> \<diamond>\<box>G"
  from a1 obtain nf where nf: "(w |\<^sub>s nf) \<Turnstile> \<box>F" by (auto simp: eventually_defs)
  from a2 obtain ng where ng: "(w |\<^sub>s ng) \<Turnstile> \<box>G" by (auto simp: eventually_defs)
  let ?n = "max nf ng"
  have "nf \<le> ?n" by simp
  from this nf have "(w |\<^sub>s ?n) \<Turnstile> \<box>F" by (rule linalw)
  moreover
  have "ng \<le> ?n" by simp
  from this ng have "(w |\<^sub>s ?n) \<Turnstile> \<box>G" by (rule linalw)
  ultimately
  have "(w |\<^sub>s ?n) \<Turnstile> \<box>(F \<and> G)" by (rule box_conjE)
  thus "w \<Turnstile> \<diamond>\<box>(F \<and> G)" by (auto simp: eventually_defs)
next
  fix w
  assume h: "w \<Turnstile> \<diamond>\<box>(F \<and> G)"
  have "\<turnstile> F \<and> G \<longrightarrow> F" by auto
  hence "\<turnstile> \<diamond>\<box>(F \<and> G) \<longrightarrow> \<diamond>\<box>F" by (rule STL4_eve[OF STL4])
  with h show "w \<Turnstile> \<diamond>\<box>F" by auto
next
  fix w
  assume h: "w \<Turnstile> \<diamond>\<box>(F \<and> G)"
  have "\<turnstile> F \<and> G \<longrightarrow> G" by auto
  hence "\<turnstile> \<diamond>\<box>(F \<and> G) \<longrightarrow> \<diamond>\<box>G" by (rule STL4_eve[OF STL4])
  with h show "w \<Turnstile> \<diamond>\<box>G" by auto
qed

lemma MM0: "\<turnstile> \<box>(F \<longrightarrow> G) \<longrightarrow> \<box>F \<longrightarrow> \<box>G"
proof -
  have "\<turnstile> \<box>(F \<and> (F \<longrightarrow> G)) \<longrightarrow> \<box>G" by (rule STL4) auto
  thus ?thesis by (auto simp: STL5[int_rewrite])
qed

lemma MM1: assumes h: "\<turnstile> F = G" shows "\<turnstile> \<box>F = \<box>G"
  by (auto simp: h[int_rewrite])
  
theorem MM2: "\<turnstile> \<box>A \<and> \<box>(B \<longrightarrow> C) \<longrightarrow> \<box>(A \<and> B \<longrightarrow> C)"
proof -
  have "\<turnstile> \<box>(A \<and> (B \<longrightarrow> C)) \<longrightarrow> \<box>(A \<and> B \<longrightarrow> C)" by (rule STL4) auto
  thus ?thesis by (auto simp: STL5[int_rewrite])
qed

theorem MM3: "\<turnstile> \<box>\<not>A \<longrightarrow> \<box>(A \<and> B \<longrightarrow> C)"
  by (rule STL4) auto

theorem MM4[simp_unl]: "\<turnstile> \<box>#F = #F"
proof (cases "F")
  assume "F"
  hence 1: "\<turnstile> #F" by auto
  hence "\<turnstile> \<box>#F" by (rule alw)
  with 1 show ?thesis by force
next
  assume "\<not>F"
  hence 1: "\<turnstile> \<not> #F" by auto
  from ax1 have "\<turnstile> \<not> #F \<longrightarrow> \<not> \<box>#F" by (rule lift_imp_neg)
  with 1 show ?thesis by force
qed

theorem MM4b[simp_unl]: "\<turnstile> \<box>\<not>#F = \<not>#F"
proof -
  have "\<turnstile> \<not>#F = #(\<not>F)" by auto
  hence "\<turnstile> \<box>\<not>#F = \<box>#(\<not>F)" by (rule MM1)
  thus ?thesis by auto
qed

theorem MM5: "\<turnstile> \<box>F \<or> \<box>G \<longrightarrow> \<box>(F \<or> G)"
proof -
  have "\<turnstile> \<box>F \<longrightarrow> \<box>(F \<or> G)" by (rule STL4) auto
  moreover
  have "\<turnstile> \<box>G \<longrightarrow> \<box>(F \<or> G)" by (rule STL4) auto
  ultimately show ?thesis by force
qed

theorem MM6: "\<turnstile> \<box>F \<or> \<box>G \<longrightarrow> \<box>(\<box>F \<or> \<box>G)"
proof -
  have "\<turnstile> \<box>\<box>F \<or> \<box>\<box>G \<longrightarrow> \<box>(\<box>F \<or> \<box>G)" by (rule MM5)
  thus ?thesis by simp
qed

lemma MM10: 
  assumes h: "|~ F = G" shows "\<turnstile> \<box>[F]_v = \<box>[G]_v"
  by (auto simp: h[int_rewrite])

lemma MM9: 
  assumes h: "\<turnstile> F = G" shows "\<turnstile> \<box>[F]_v = \<box>[G]_v"
  by (rule MM10[OF pre[OF h]])

theorem MM11: "\<turnstile> \<box>[\<not>(P \<and> Q)]_v \<longrightarrow> \<box>[P]_v \<longrightarrow> \<box>[P \<and> \<not>Q]_v"
proof -
  have "\<turnstile> \<box>[\<not>(P \<and> Q)]_v \<longrightarrow> \<box>[P \<longrightarrow> P \<and> \<not>Q]_v" by (rule M2) auto
  from this ax4 show ?thesis by (rule lift_imp_trans)
qed

theorem MM12[simp_unl]: "\<turnstile> \<box>[\<box>[P]_v]_v = \<box>[P]_v"
proof (rule int_iffI)
  have "|~ \<box>[P]_v \<longrightarrow> [P]_v" by (auto simp: pax4[unlifted])
  hence "\<turnstile> \<box>[\<box>[P]_v]_v \<longrightarrow> \<box>[[P]_v]_v" by (rule M2)
  thus "\<turnstile> \<box>[\<box>[P]_v]_v \<longrightarrow> \<box>[P]_v" by (unfold T3[int_rewrite])
next
  have "\<turnstile> \<box>\<box>[P]_v \<longrightarrow> \<box>[\<box>\<box>[P]_v]_v" by (rule ax2)
  thus "\<turnstile> \<box>[P]_v \<longrightarrow> \<box>[\<box>[P]_v]_v" by auto
qed

subsection "Theorems about the eventually operator"

\<comment> \<open>rules to push negation inside modal operators, sometimes useful for rewriting\<close>
theorem dualization:
  "\<turnstile> \<not>\<box>F = \<diamond>\<not>F"
  "\<turnstile> \<not>\<diamond>F = \<box>\<not>F"
  "\<turnstile> \<not>\<box>[A]_v = \<diamond>\<langle>\<not>A\<rangle>_v"
  "\<turnstile> \<not>\<diamond>\<langle>A\<rangle>_v = \<box>[\<not>A]_v"
  unfolding eventually_def angle_action_def by simp_all 

lemmas dualization_rew = dualization[int_rewrite]
lemmas dualization_unl = dualization[unlifted]

theorem E1: "\<turnstile> \<diamond>(F \<or> G) = (\<diamond>F \<or> \<diamond>G)"
proof -
  have "\<turnstile> \<box>\<not>(F \<or> G) = \<box>(\<not>F \<and> \<not>G)" by (rule MM1) auto
  thus ?thesis unfolding eventually_def STL5[int_rewrite] by force
qed

theorem E3: "\<turnstile> F \<longrightarrow> \<diamond>F"
  unfolding eventually_def by (force dest: ax1[unlift_rule])

theorem E4: "\<turnstile> \<box>F \<longrightarrow> \<diamond>F"
  by (rule lift_imp_trans[OF ax1 E3])

theorem E5: "\<turnstile> \<box>F \<longrightarrow> \<box>\<diamond>F"
proof -
  have "\<turnstile> \<box>\<box>F \<longrightarrow> \<box>\<diamond>F" by (rule STL4[OF E4])
  thus ?thesis by simp
qed

theorem E6:  "\<turnstile> \<box>F \<longrightarrow> \<diamond>\<box>F"
  using E4[of "TEMP \<box>F"] by simp

theorem E7: 
  assumes h: "|~ \<not>F \<and> Unchanged v \<longrightarrow> \<circle>\<not>F"
  shows      "|~ \<diamond>F \<longrightarrow> F \<or> \<circle>\<diamond>F"
proof -
  from h have "|~ \<not>F \<and> \<circle>\<box>\<not>F \<longrightarrow> \<box>\<not>F" by (rule M10)
  thus ?thesis by (auto simp: eventually_def)
qed

theorem E8: "\<turnstile> \<diamond>(F \<longrightarrow> G) \<longrightarrow> \<box>F \<longrightarrow> \<diamond>G"
proof -
  have "\<turnstile> \<box>(F \<and> \<not>G) \<longrightarrow> \<box>\<not>(F \<longrightarrow> G)" by (rule STL4) auto
  thus ?thesis unfolding eventually_def STL5[int_rewrite] by auto
qed

theorem E9: "\<turnstile> \<box>(F \<longrightarrow> G) \<longrightarrow> \<diamond>F \<longrightarrow> \<diamond>G"
proof -
  have "\<turnstile> \<box>(F \<longrightarrow> G) \<longrightarrow> \<box>(\<not>G \<longrightarrow> \<not>F)" by (rule STL4) auto
  with MM0[of "TEMP \<not>G" "TEMP \<not>F"] show ?thesis unfolding eventually_def by force
qed

theorem E10[simp_unl]: "\<turnstile> \<diamond>\<diamond>F = \<diamond>F"
  by (simp add: eventually_def)

theorem E22:
  assumes h: "\<turnstile> F = G"
  shows "\<turnstile> \<diamond>F = \<diamond>G"
  by (auto simp: h[int_rewrite])

theorem E15[simp_unl]: "\<turnstile> \<diamond>#F = #F"
  by (simp add: eventually_def)

theorem E15b[simp_unl]: "\<turnstile> \<diamond>\<not>#F = \<not>#F"
  by (simp add: eventually_def)

theorem E16: "\<turnstile> \<diamond>\<box>F \<longrightarrow> \<diamond>F"
  by (rule STL4_eve[OF ax1])

text \<open>An action version of STL6\<close>

lemma STL6_act: "\<turnstile> \<diamond>(\<box>[F]_v \<and> \<box>[G]_w) = (\<diamond>\<box>[F]_v \<and> \<diamond>\<box>[G]_w)"
proof -
  have "\<turnstile> (\<diamond>\<box>(\<box>[F]_v \<and> \<box>[G]_w)) = \<diamond>(\<box>\<box>[F]_v \<and> \<box>\<box>[G]_w)" by (rule E22[OF STL5])
  thus ?thesis by (auto simp: STL6[int_rewrite])
qed

lemma SE1: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(\<box>F \<and> G)"
proof -
  have "\<turnstile> \<box>\<not>(\<box>F \<and> G) \<longrightarrow> \<box>(\<box>F \<longrightarrow> \<not>G)" by (rule STL4) auto
  with MM0 show ?thesis by (force simp: eventually_def)
qed

lemma SE2: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(F \<and> G)"
proof -
  have "\<turnstile> \<box>F \<and> G \<longrightarrow> F \<and> G" by (auto elim: ax1[unlift_rule])
  hence "\<turnstile> \<diamond>(\<box>F \<and> G) \<longrightarrow> \<diamond>(F \<and> G)" by (rule STL4_eve)
  with SE1 show ?thesis by (rule lift_imp_trans)
qed

lemma SE3: "\<turnstile> \<box>F \<and> \<diamond>G \<longrightarrow> \<diamond>(G \<and> F)"
proof -
  have "\<turnstile> \<diamond>(F \<and> G) \<longrightarrow> \<diamond>(G \<and> F)" by (rule STL4_eve) auto
  with SE2 show ?thesis by (rule lift_imp_trans)
qed

lemma SE4: 
  assumes h1: "s \<Turnstile> \<box>F" and  h2: "s \<Turnstile> \<diamond>G" and  h3: "\<turnstile> \<box>F \<and> G \<longrightarrow> H"
  shows "s \<Turnstile> \<diamond>H"
  using h1 h2 h3[THEN STL4_eve] SE1 by force

theorem E17: "\<turnstile> \<box>\<diamond>\<box>F \<longrightarrow> \<box>\<diamond>F"
  by (rule STL4[OF STL4_eve[OF ax1]])

theorem E18: "\<turnstile> \<box>\<diamond>\<box>F \<longrightarrow> \<diamond>\<box>F"
  by (rule ax1)

theorem E19: "\<turnstile> \<diamond>\<box>F \<longrightarrow> \<box>\<diamond>\<box>F"
proof -
  have "\<turnstile> (\<box>F \<and> \<not>\<box>F) = #False" by auto
  hence "\<turnstile> \<diamond>\<box>(\<box>F \<and> \<not>\<box>F) = \<diamond>\<box>#False" by (rule E22[OF MM1])
  thus ?thesis unfolding STL6[int_rewrite] by (auto simp: eventually_def)
qed

theorem E20: "\<turnstile> \<diamond>\<box>F \<longrightarrow> \<box>\<diamond>F"
  by (rule lift_imp_trans[OF E19 E17])

theorem E21[simp_unl]: "\<turnstile> \<box>\<diamond>\<box>F = \<diamond>\<box>F"
  by (rule int_iffI[OF E18 E19])

theorem E27[simp_unl]: "\<turnstile> \<diamond>\<box>\<diamond>F = \<box>\<diamond>F"
  using E21 unfolding eventually_def by force

lemma E28: "\<turnstile> \<diamond>\<box>F \<and> \<box>\<diamond>G \<longrightarrow> \<box>\<diamond>(F \<and> G)"
proof -
  have "\<turnstile> \<diamond>\<box>(\<box>F \<and> \<diamond>G) \<longrightarrow> \<diamond>\<box>\<diamond>(F \<and> G)" by (rule STL4_eve[OF STL4[OF SE2]])
  thus ?thesis by (simp add: STL6[int_rewrite])
qed

lemma E23: "|~ \<circle>F \<longrightarrow> \<diamond>F"
  using P1 by (force simp: eventually_def)

lemma E24: "\<turnstile> \<diamond>\<box>Q \<longrightarrow> \<box>[\<diamond>Q]_v"
  by (rule lift_imp_trans[OF E20 P4])

lemma E25: "\<turnstile> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>A"
  using P4 by (force simp: eventually_def angle_action_def)

lemma E26: "\<turnstile> \<box>\<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<box>\<diamond>A" 
  by (rule STL4[OF E25])

lemma allBox: "(s \<Turnstile> \<box>(\<forall>x. F x)) = (\<forall>x. s \<Turnstile> \<box>(F x))"
  unfolding allT[unlifted] ..

lemma E29: "|~ \<circle>\<diamond>F \<longrightarrow> \<diamond>F"
  unfolding eventually_def using pax3 by force

lemma E30:
  assumes h1: "\<turnstile> F \<longrightarrow> \<box>F" and h2: "\<turnstile> \<diamond>F"
  shows "\<turnstile> \<diamond>\<box>F"
  using h2 h1[THEN STL4_eve] by (rule fmp)

lemma E31: "\<turnstile> \<box>(F \<longrightarrow> \<box>F) \<and> \<diamond>F \<longrightarrow> \<diamond>\<box>F"
proof -
  have "\<turnstile> \<box>(F \<longrightarrow> \<box>F) \<and> \<diamond>F \<longrightarrow> \<diamond>(\<box>(F \<longrightarrow> \<box>F) \<and> F)" by (rule SE1)
  moreover
  have "\<turnstile> \<box>(F \<longrightarrow> \<box>F) \<and> F \<longrightarrow> \<box>F" using ax1[of "TEMP F \<longrightarrow> \<box>F"] by auto
  hence "\<turnstile> \<diamond>(\<box>(F \<longrightarrow> \<box>F) \<and> F) \<longrightarrow> \<diamond>\<box>F" by (rule STL4_eve)
  ultimately show ?thesis by (rule lift_imp_trans)
qed

lemma allActBox: "(s \<Turnstile> \<box>[(\<forall>x. F x)]_v) = (\<forall>x. s \<Turnstile> \<box>[(F x)]_v)"
  unfolding allActT[unlifted] ..

theorem exEE: "\<turnstile> (\<exists>x. \<diamond>(F x)) = \<diamond>(\<exists>x. F x)"
proof -
  have "\<turnstile> \<not>(\<exists> x. \<diamond>(F x)) = \<not>\<diamond>(\<exists> x. F x)"
    by (auto simp: eventually_def Not_Rex[int_rewrite] allBox)
  thus ?thesis by force
qed

theorem exActE: "\<turnstile> (\<exists>x. \<diamond>\<langle>F x\<rangle>_v) = \<diamond>\<langle>(\<exists>x. F x)\<rangle>_v"
proof -
  have "\<turnstile> \<not>(\<exists>x. \<diamond>\<langle>F x\<rangle>_v) = \<not>\<diamond>\<langle>(\<exists>x. F x)\<rangle>_v"
    by (auto simp: angle_action_def Not_Rex[int_rewrite] allActBox)
  thus ?thesis by force
qed


subsection "Theorems about the leadsto operator"

theorem LT1: "\<turnstile> F \<leadsto> F"
  unfolding leadsto_def by (rule alw[OF E3])

theorem LT2: assumes h: "\<turnstile> F \<longrightarrow> G" shows "\<turnstile> F \<longrightarrow> \<diamond>G"
  by (rule lift_imp_trans[OF h E3])

theorem LT3: assumes h: "\<turnstile> F \<longrightarrow> G" shows "\<turnstile> F \<leadsto> G"
  unfolding leadsto_def by (rule alw[OF LT2[OF h]])

theorem LT4: "\<turnstile> F \<longrightarrow> (F \<leadsto> G) \<longrightarrow> \<diamond>G"
  unfolding leadsto_def using ax1[of "TEMP F \<longrightarrow> \<diamond>G"] by auto

theorem LT5: "\<turnstile> \<box>(F \<longrightarrow> \<diamond>G) \<longrightarrow> \<diamond>F \<longrightarrow> \<diamond>G"
  using E9[of "F" "TEMP \<diamond>G"] by simp

theorem LT6: "\<turnstile> \<diamond>F \<longrightarrow> (F \<leadsto> G) \<longrightarrow> \<diamond>G"
  unfolding leadsto_def using LT5[of "F" "G"] by auto

theorem LT9[simp_unl]: "\<turnstile> \<box>(F \<leadsto> G) = (F \<leadsto> G)"
  by (auto simp: leadsto_def)

theorem LT7: "\<turnstile> \<box>\<diamond>F \<longrightarrow> (F \<leadsto> G) \<longrightarrow> \<box>\<diamond>G"
proof -
  have "\<turnstile> \<box>\<diamond>F \<longrightarrow> \<box>((F \<leadsto> G) \<longrightarrow> \<diamond>G)" by (rule STL4[OF LT6])
  from lift_imp_trans[OF this MM0] show ?thesis by simp
qed

theorem LT8: "\<turnstile> \<box>\<diamond>G \<longrightarrow> (F \<leadsto> G)"
  unfolding leadsto_def by (rule STL4) auto

theorem LT13: "\<turnstile> (F \<leadsto> G) \<longrightarrow> (G \<leadsto> H) \<longrightarrow> (F \<leadsto> H)"
proof -
  have "\<turnstile> \<diamond>G \<longrightarrow> (G \<leadsto> H) \<longrightarrow> \<diamond>H" by (rule LT6)
  hence "\<turnstile> \<box>(F \<longrightarrow> \<diamond>G) \<longrightarrow> \<box>((G \<leadsto> H) \<longrightarrow> (F \<longrightarrow> \<diamond>H))" by (intro STL4) auto
  from lift_imp_trans[OF this MM0] show ?thesis by (simp add: leadsto_def)
qed

theorem LT11: "\<turnstile> (F \<leadsto> G) \<longrightarrow> (F \<leadsto> (G \<or> H))"
proof -
  have "\<turnstile> G \<leadsto> (G \<or> H)" by (rule LT3) auto
  with LT13[of "F" "G" "TEMP (G \<or> H)"] show ?thesis by force 
qed

theorem LT12: "\<turnstile> (F \<leadsto> H) \<longrightarrow>  (F \<leadsto> (G \<or> H))"
proof -
  have "\<turnstile> H \<leadsto> (G \<or> H)" by (rule LT3) auto
  with LT13[of "F" "H" "TEMP (G \<or> H)"] show ?thesis by force
qed

theorem LT14: "\<turnstile> ((F \<or> G) \<leadsto> H) \<longrightarrow> (F \<leadsto> H)"
  unfolding leadsto_def by (rule STL4) auto

theorem LT15: "\<turnstile> ((F \<or> G) \<leadsto> H) \<longrightarrow> (G \<leadsto> H)"
  unfolding leadsto_def by (rule STL4) auto 

theorem LT16: "\<turnstile> (F \<leadsto> H) \<longrightarrow> (G \<leadsto> H) \<longrightarrow> ((F \<or> G) \<leadsto> H)"
proof -
  have "\<turnstile> \<box>(F \<longrightarrow> \<diamond>H) \<longrightarrow> \<box>((G \<longrightarrow> \<diamond>H) \<longrightarrow> (F \<or> G \<longrightarrow> \<diamond>H))" by (rule STL4) auto
  from lift_imp_trans[OF this MM0] show ?thesis by (unfold leadsto_def)
qed

theorem LT17: "\<turnstile> ((F \<or> G) \<leadsto> H) = ((F \<leadsto> H) \<and> (G \<leadsto> H))"
  by (auto elim: LT14[unlift_rule] LT15[unlift_rule]
                 LT16[unlift_rule])

theorem LT10:
  assumes h: "\<turnstile> (F \<and> \<not>G) \<leadsto> G"
  shows "\<turnstile> F \<leadsto> G"
proof -
  from h have "\<turnstile> ((F \<and> \<not>G) \<or> G) \<leadsto> G"
    by (auto simp: LT17[int_rewrite] LT1[int_rewrite])
  moreover
  have "\<turnstile> F \<leadsto> ((F \<and> \<not>G) \<or> G)" by (rule LT3, auto)
  ultimately
  show ?thesis by (force elim: LT13[unlift_rule])
qed

theorem LT18: "\<turnstile> (A \<leadsto> (B \<or> C)) \<longrightarrow> (B \<leadsto> D) \<longrightarrow> (C \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
proof -
  have "\<turnstile> (B \<leadsto> D) \<longrightarrow> (C \<leadsto> D) \<longrightarrow> ((B \<or> C) \<leadsto> D)" by (rule LT16)
  thus ?thesis by (force elim: LT13[unlift_rule])
qed

theorem LT19: "\<turnstile> (A \<leadsto> (D \<or> B)) \<longrightarrow> (B \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
  using LT18[of "A" "D" "B" "D"] LT1[of "D"] by force

theorem LT20: "\<turnstile> (A \<leadsto> (B \<or> D)) \<longrightarrow> (B \<leadsto> D) \<longrightarrow> (A \<leadsto> D)"
  using LT18[of "A" "B" "D" "D"] LT1[of "D"] by force

theorem LT21: "\<turnstile> ((\<exists>x. F x) \<leadsto> G) = (\<forall>x. (F x \<leadsto> G))"
proof -
  have "\<turnstile> \<box>((\<exists>x. F x) \<longrightarrow> \<diamond>G) = \<box>(\<forall>x. (F x \<longrightarrow> \<diamond>G))" by (rule MM1) auto
  thus ?thesis by (unfold leadsto_def allT[int_rewrite])
qed

theorem LT22: "\<turnstile> (F \<leadsto> (G \<or> H)) \<longrightarrow> \<box>\<not>G \<longrightarrow> (F \<leadsto> H)"
proof -
  have "\<turnstile> \<box>\<not>G \<longrightarrow> (G \<leadsto> H)" unfolding leadsto_def by (rule STL4) auto
  thus ?thesis by (force elim: LT20[unlift_rule])
qed

lemma LT23: "|~ (P \<longrightarrow> \<circle>Q) \<longrightarrow> (P \<longrightarrow> \<diamond>Q)"
  by (auto dest: E23[unlift_rule])

theorem LT24: "\<turnstile> \<box>I \<longrightarrow> ((P \<and> I) \<leadsto> Q) \<longrightarrow> P \<leadsto> Q"
proof -
  have "\<turnstile> \<box>I \<longrightarrow> \<box>((P \<and> I \<longrightarrow> \<diamond>Q) \<longrightarrow> (P \<longrightarrow> \<diamond>Q))" by (rule STL4) auto
  from lift_imp_trans[OF this MM0] show ?thesis by (unfold leadsto_def)
qed

theorem LT25[simp_unl]: "\<turnstile> (F \<leadsto> #False) = \<box>\<not>F"
unfolding leadsto_def proof (rule MM1)
  show "\<turnstile> (F \<longrightarrow> \<diamond>#False) = \<not>F" by simp
qed

lemma LT28: 
  assumes h: "|~ P \<longrightarrow> \<circle>P \<or> \<circle>Q"
  shows "|~ (P \<longrightarrow> \<circle>P) \<or> \<diamond>Q"
  using h E23[of Q] by force

lemma LT29:
  assumes h1: "|~ P \<longrightarrow> \<circle>P \<or> \<circle>Q" and   h2: "|~ P \<and> Unchanged v \<longrightarrow> \<circle>P"
  shows "\<turnstile> P \<longrightarrow> \<box>P \<or> \<diamond>Q"
proof -
  from h1[THEN LT28] have "|~ \<box>\<not>Q \<longrightarrow> (P \<longrightarrow> \<circle>P)" unfolding eventually_def by auto
  hence "\<turnstile> \<box>[\<box>\<not>Q]_v \<longrightarrow> \<box>[P \<longrightarrow> \<circle>P]_v" by (rule M2)
  moreover
  have "\<turnstile> \<not>\<diamond>Q \<longrightarrow> \<box>[\<box>\<not>Q]_v" unfolding dualization_rew by (rule ax2)
  moreover
  note ax3[OF h2]
  ultimately
  show ?thesis by force 
qed

lemma LT30:
  assumes h: "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q"
  shows "|~ N \<longrightarrow> (P \<longrightarrow> \<circle>P) \<or> \<diamond>Q"
  using h E23 by force

lemma LT31:
  assumes h1: "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q" and h2: "|~ P \<and> Unchanged v \<longrightarrow> \<circle>P"
  shows"\<turnstile> \<box>N \<longrightarrow> P \<longrightarrow> \<box>P \<or> \<diamond>Q"
proof -
  from h1[THEN LT30] have "|~ N \<longrightarrow> \<box>\<not>Q \<longrightarrow> P \<longrightarrow> \<circle>P" unfolding eventually_def by auto
  hence "\<turnstile> \<box>[N \<longrightarrow> \<box>\<not>Q \<longrightarrow> P \<longrightarrow> \<circle>P]_v" by (rule sq)
  hence "\<turnstile> \<box>[N]_v \<longrightarrow> \<box>[\<box>\<not>Q]_v \<longrightarrow> \<box>[P \<longrightarrow> \<circle>P]_v"
    by (force intro: ax4[unlift_rule])
  with P4 have "\<turnstile> \<box>N \<longrightarrow> \<box>[\<box>\<not>Q]_v \<longrightarrow> \<box>[P \<longrightarrow> \<circle>P]_v" by (rule lift_imp_trans)
  moreover
  have "\<turnstile> \<not>\<diamond>Q \<longrightarrow> \<box>[\<box>\<not>Q]_v" unfolding dualization_rew by (rule ax2)
  moreover
  note ax3[OF h2]
  ultimately
  show ?thesis by force
qed

lemma LT33: "\<turnstile> ((#P \<and> F) \<leadsto> G) = (#P \<longrightarrow> (F \<leadsto> G))"
  by (cases "P", auto simp: leadsto_def)

lemma AA1: "\<turnstile> \<box>[#False]_v \<longrightarrow> \<not>\<diamond>\<langle>Q\<rangle>_v"
  unfolding dualization_rew by (rule M2) auto

lemma AA2: "\<turnstile> \<box>[P]_v \<and> \<diamond>\<langle>Q\<rangle>_v \<longrightarrow> \<diamond>\<langle>P \<and> Q\<rangle>_v"
proof -
  have "\<turnstile> \<box>[P \<longrightarrow> ~(P \<and> Q) \<longrightarrow> \<not>Q]_v" by (rule sq) (auto simp: actrans_def)
  hence "\<turnstile> \<box>[P]_v \<longrightarrow> \<box>[~(P \<and> Q)]_v \<longrightarrow> \<box>[\<not>Q]_v"
    by (force intro: ax4[unlift_rule])
  thus ?thesis by (auto simp: angle_action_def)
qed

lemma AA3: "\<turnstile> \<box>P \<and> \<box>[P \<longrightarrow> Q]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>Q"
proof -
  have "\<turnstile> \<box>P \<and> \<box>[P \<longrightarrow> Q]_v \<longrightarrow> \<box>[P \<and> (P \<longrightarrow> Q)]_v"
    by (auto dest: P4[unlift_rule] simp: M8[int_rewrite])
  moreover
  have "\<turnstile> \<box>[P \<and> (P \<longrightarrow> Q)]_v \<longrightarrow> \<box>[Q]_v" by (rule M2) auto
  ultimately have "\<turnstile> \<box>P \<and> \<box>[P \<longrightarrow> Q]_v \<longrightarrow> \<box>[Q]_v" by (rule lift_imp_trans)
  moreover
  have "\<turnstile> \<diamond>(Q \<and> A) \<longrightarrow> \<diamond>Q" by (rule STL4_eve) auto
  hence "\<turnstile> \<diamond>\<langle>Q \<and> A\<rangle>_v \<longrightarrow> \<diamond>Q" by (force dest: E25[unlift_rule])
  with AA2 have "\<turnstile> \<box>[Q]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>Q" by (rule lift_imp_trans)
  ultimately show ?thesis by force
qed

lemma AA4: "\<turnstile> \<diamond>\<langle>\<langle>A\<rangle>_v\<rangle>_w \<longrightarrow> \<diamond>\<langle>\<langle>A\<rangle>_w\<rangle>_v"
  unfolding angle_action_def angle_actrans_def using T5 by force

lemma AA7: assumes h: "|~ F \<longrightarrow> G" shows "\<turnstile> \<diamond>\<langle>F\<rangle>_v \<longrightarrow> \<diamond>\<langle>G\<rangle>_v"
proof -
  from h have "\<turnstile> \<box>[\<not>G]_v \<longrightarrow> \<box>[\<not>F]_v" by (intro M2) auto
  thus ?thesis unfolding angle_action_def by force
qed

lemma AA6: "\<turnstile> \<box>[P \<longrightarrow> Q]_v \<and> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>Q\<rangle>_v"
proof -
  have "\<turnstile> \<diamond>\<langle>(P \<longrightarrow> Q) \<and> P\<rangle>_v \<longrightarrow> \<diamond>\<langle>Q\<rangle>_v" by (rule AA7) auto
  with AA2 show ?thesis by (rule lift_imp_trans)
qed

lemma AA8: "\<turnstile> \<box>[P]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<box>[P]_v \<and> A\<rangle>_v"
proof -
  have "\<turnstile> \<box>[\<box>[P]_v]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<box>[P]_v \<and> A\<rangle>_v" by (rule AA2)
  with P5 show ?thesis by force
qed

lemma AA9: "\<turnstile> \<box>[P]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>[P]_v \<and> A\<rangle>_v"
proof -
  have "\<turnstile> \<box>[[P]_v]_v \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>[P]_v \<and> A\<rangle>_v" by (rule AA2)
  thus ?thesis by simp
qed

lemma AA10: "\<turnstile> \<not>(\<box>[P]_v \<and> \<diamond>\<langle>\<not>P\<rangle>_v)"
  unfolding angle_action_def by auto

lemma AA11: "\<turnstile> \<not>\<diamond>\<langle>v$ = $v\<rangle>_v"
  unfolding dualization_rew by (rule ax5)

lemma AA15: "\<turnstile> \<diamond>\<langle>P \<and> Q\<rangle>_v \<longrightarrow> \<diamond>\<langle>P\<rangle>_v"
  by (rule AA7) auto

lemma AA16: "\<turnstile> \<diamond>\<langle>P \<and> Q\<rangle>_v \<longrightarrow> \<diamond>\<langle>Q\<rangle>_v"
  by (rule AA7) auto

lemma AA13: "\<turnstile> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>v$ \<noteq> $v\<rangle>_v"
proof -
  have "\<turnstile> \<box>[v$ \<noteq> $v]_v \<and> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>v$ \<noteq> $v \<and> P\<rangle>_v" by (rule AA2)
  hence "\<turnstile> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>v$ \<noteq> $v \<and> P\<rangle>_v" by (simp add: ax5[int_rewrite])
  from this AA15 show ?thesis by (rule lift_imp_trans)
qed

lemma AA14: "\<turnstile> \<diamond>\<langle>P \<or> Q\<rangle>_v = (\<diamond>\<langle>P\<rangle>_v \<or> \<diamond>\<langle>Q\<rangle>_v)"
proof -
  have "\<turnstile> \<box>[\<not>(P \<or> Q)]_v = \<box>[\<not>P \<and> \<not>Q]_v" by (rule MM10) auto
  hence "\<turnstile> \<box>[\<not>(P \<or> Q)]_v = (\<box>[\<not>P]_v \<and> \<box>[\<not>Q]_v)" by (unfold M8[int_rewrite])
  thus ?thesis unfolding angle_action_def by auto
qed

lemma AA17: "\<turnstile> \<diamond>\<langle>[P]_v \<and> A\<rangle>_v \<longrightarrow> \<diamond>\<langle>P \<and> A\<rangle>_v"
proof -
  have "\<turnstile> \<box>[v$ \<noteq> $v \<and> \<not>(P \<and> A)]_v \<longrightarrow> \<box>[\<not>([P]_v \<and> A)]_v"
    by (rule M2) (auto simp: actrans_def unch_def)
  with ax5[of "v"] show ?thesis
    unfolding angle_action_def M8[int_rewrite] by force
qed

lemma AA19: "\<turnstile> \<box>P \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>P \<and> A\<rangle>_v"
  using P4 by (force intro: AA2[unlift_rule])

lemma AA20: 
  assumes h1: "|~ P \<longrightarrow> \<circle>P \<or> \<circle>Q"
     and  h2: "|~ P \<and> A \<longrightarrow> \<circle>Q"
     and  h3: "|~ P \<and> Unchanged w \<longrightarrow> \<circle>P" 
  shows "\<turnstile> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v) \<longrightarrow> (P \<leadsto> Q)"
proof -
  from h2 E23 have "|~ P \<and> A \<longrightarrow> \<diamond>Q" by force
  hence "\<turnstile> \<diamond>\<langle>P \<and> A\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<diamond>Q\<rangle>_v" by (rule AA7)
  with E25[of "TEMP \<diamond>Q" "v"] have "\<turnstile> \<diamond>\<langle>P \<and> A\<rangle>_v \<longrightarrow> \<diamond>Q" by force
  with AA19 have "\<turnstile> \<box>P \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>Q" by (rule lift_imp_trans)
  with LT29[OF h1 h3] have "\<turnstile> (\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v) \<longrightarrow> (P \<longrightarrow> \<diamond>Q)" by force
  thus ?thesis unfolding leadsto_def by (rule STL4)
qed

lemma AA21: "|~ \<diamond>\<langle>\<circle>F\<rangle>_v \<longrightarrow> \<circle>\<diamond>F"
  using pax5[of "TEMP \<not>F" "v"] unfolding angle_action_def eventually_def by auto

theorem AA24[simp_unl]: "\<turnstile> \<diamond>\<langle>\<langle>P\<rangle>_f\<rangle>_f = \<diamond>\<langle>P\<rangle>_f"
  unfolding angle_action_def angle_actrans_def by simp

lemma AA22: 
  assumes h1: "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q"
     and  h2: "|~ P \<and> N \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q"
     and  h3: "|~ P \<and> Unchanged w \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>N \<and> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v) \<longrightarrow> (P \<leadsto> Q)"
proof -
  from h2 have "|~ \<langle>(N \<and> P) \<and> A\<rangle>_v \<longrightarrow> \<circle>Q" by (auto simp: angle_actrans_sem[int_rewrite])
  from pref_imp_trans[OF this E23] have "\<turnstile> \<diamond>\<langle>\<langle>(N \<and> P) \<and> A\<rangle>_v\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<diamond>Q\<rangle>_v" by (rule AA7)
  hence "\<turnstile> \<diamond>\<langle>(N \<and> P) \<and> A\<rangle>_v \<longrightarrow> \<diamond>Q" by (force dest: E25[unlift_rule])
  with AA19 have "\<turnstile> \<box>(N \<and> P) \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>Q" by (rule lift_imp_trans)
  hence "\<turnstile> \<box>N \<and> \<box>P \<and> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>Q" by (auto simp: STL5[int_rewrite])
  with LT31[OF h1 h3] have "\<turnstile> \<box>N \<and> (\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v) \<longrightarrow> (P \<longrightarrow> \<diamond>Q)" by force
  hence "\<turnstile> \<box>(\<box>N \<and> (\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)) \<longrightarrow> \<box>(P \<longrightarrow> \<diamond>Q)" by (rule STL4)
  thus ?thesis by (simp add: leadsto_def STL5[int_rewrite])
qed

lemma AA23:
  assumes "|~ P \<and> N \<longrightarrow> \<circle>P \<or> \<circle>Q"
     and  "|~ P \<and> N \<and> \<langle>A\<rangle>_v \<longrightarrow> \<circle>Q"
     and  "|~ P \<and> Unchanged w \<longrightarrow> \<circle>P"
  shows "\<turnstile> \<box>N \<and> \<box>\<diamond>\<langle>A\<rangle>_v \<longrightarrow> (P \<leadsto> Q)"
proof -
  have "\<turnstile> \<box>\<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<box>(\<box>P \<longrightarrow> \<diamond>\<langle>A\<rangle>_v)" by (rule STL4) auto
  with AA22[OF assms] show ?thesis by force
qed

lemma AA25: 
  assumes h: "|~ \<langle>P\<rangle>_v \<longrightarrow> \<langle>Q\<rangle>_w"
  shows "\<turnstile> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>Q\<rangle>_w"
proof -
  from h have "\<turnstile> \<diamond>\<langle>\<langle>P\<rangle>_v\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<langle>P\<rangle>_w\<rangle>_v"
    by (intro AA7) (auto simp: angle_actrans_def actrans_def)
  with AA4 have "\<turnstile> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<langle>P\<rangle>_v\<rangle>_w" by force
  from this AA7[OF h] have "\<turnstile> \<diamond>\<langle>P\<rangle>_v \<longrightarrow> \<diamond>\<langle>\<langle>Q\<rangle>_w\<rangle>_w" by (rule lift_imp_trans)
  thus ?thesis by simp
qed

lemma AA26:
  assumes h: "|~ \<langle>A\<rangle>_v = \<langle>B\<rangle>_w"
  shows "\<turnstile> \<diamond>\<langle>A\<rangle>_v = \<diamond>\<langle>B\<rangle>_w"
proof -
  from h have "|~ \<langle>A\<rangle>_v \<longrightarrow> \<langle>B\<rangle>_w" by auto
  hence "\<turnstile> \<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<diamond>\<langle>B\<rangle>_w" by (rule AA25)
  moreover
  from h have "|~ \<langle>B\<rangle>_w \<longrightarrow> \<langle>A\<rangle>_v" by auto
  hence "\<turnstile> \<diamond>\<langle>B\<rangle>_w \<longrightarrow> \<diamond>\<langle>A\<rangle>_v" by (rule AA25)
  ultimately
  show ?thesis by force
qed

theorem AA28[simp_unl]: "\<turnstile> \<diamond>\<diamond>\<langle>A\<rangle>_v = \<diamond>\<langle>A\<rangle>_v"
  unfolding eventually_def angle_action_def by simp

theorem AA29: "\<turnstile> \<box>[N]_v \<and> \<box>\<diamond>\<langle>A\<rangle>_v \<longrightarrow> \<box>\<diamond>\<langle>N \<and> A\<rangle>_v"
proof -
  have "\<turnstile> \<box>(\<box>[N]_v \<and> \<diamond>\<langle>A\<rangle>_v) \<longrightarrow> \<box>\<diamond>\<langle>N \<and> A\<rangle>_v" by (rule STL4[OF AA2])
  thus ?thesis by (simp add: STL5[int_rewrite])
qed

theorem AA30[simp_unl]: "\<turnstile> \<diamond>\<langle>\<diamond>\<langle>P\<rangle>_f\<rangle>_f = \<diamond>\<langle>P\<rangle>_f"
  unfolding angle_action_def by simp

theorem AA31: "\<turnstile> \<diamond>\<langle>\<circle>F\<rangle>_v \<longrightarrow> \<diamond>F"
  using pref_imp_trans[OF AA21 E29] by auto

lemma AA32[simp_unl]: "\<turnstile> \<box>\<diamond>\<box>[A]_v = \<diamond>\<box>[A]_v"
  using E21[of "TEMP \<box>[A]_v"] by simp

lemma AA33[simp_unl]: "\<turnstile> \<diamond>\<box>\<diamond>\<langle>A\<rangle>_v = \<box>\<diamond>\<langle>A\<rangle>_v"
  using E27[of "TEMP \<diamond>\<langle>A\<rangle>_v"] by simp

subsection "Lemmas about the next operator"

lemma N2: assumes h: "\<turnstile> F = G" shows "|~ \<circle>F = \<circle>G"
  by (simp add: h[int_rewrite])

lemmas next_and = T8

lemma next_or: "|~ \<circle>(F \<or> G) = (\<circle>F \<or> \<circle>G)"
proof (rule pref_iffI)
  have "|~ \<circle>((F \<or> G) \<and> \<not>F) \<longrightarrow> \<circle>G" by (rule N1) auto
  thus "|~ \<circle>(F \<or> G) \<longrightarrow> \<circle>F \<or> \<circle>G" by (auto simp: T8[int_rewrite])
next
  have "|~ \<circle>F \<longrightarrow> \<circle>(F \<or> G)" by (rule N1) auto
  moreover have "|~ \<circle>G \<longrightarrow> \<circle>(F \<or> G)" by (rule N1) auto
  ultimately show "|~ \<circle>F \<or> \<circle>G \<longrightarrow> \<circle>(F \<or> G)" by force
qed

lemma next_imp: "|~ \<circle>(F \<longrightarrow> G) = (\<circle>F \<longrightarrow> \<circle>G)"
proof (rule pref_iffI)
  have "|~ \<circle>G \<longrightarrow> \<circle>(F \<longrightarrow> G)" by (rule N1) auto
  moreover have "|~ \<circle>\<not>F \<longrightarrow> \<circle>(F \<longrightarrow> G)" by (rule N1) auto
  ultimately show "|~ (\<circle>F \<longrightarrow> \<circle>G) \<longrightarrow> \<circle>(F \<longrightarrow> G)" by force
qed (rule pax2)

lemmas next_not = pax1

lemma next_eq: "|~ \<circle>(F = G) = (\<circle>F = \<circle>G)"
proof -
  have "|~ \<circle>(F = G) = \<circle>((F \<longrightarrow> G) \<and> (G \<longrightarrow> F))" by (rule N2) auto
  from this[int_rewrite] show ?thesis
    by (auto simp: next_and[int_rewrite] next_imp[int_rewrite])
qed

lemma next_noteq: "|~ \<circle>(F \<noteq> G) = (\<circle>F \<noteq> \<circle>G)"
  by (simp add: next_eq[int_rewrite])

lemma next_const[simp_unl]: "|~ \<circle>#P = #P"
proof (cases "P")
  assume "P"
  hence 1: "\<turnstile> #P" by auto
  hence "|~ \<circle>#P" by (rule nex)
  with 1 show ?thesis by force
next
  assume "\<not>P"
  hence 1: "\<turnstile> \<not>#P" by auto
  hence "|~ \<circle>\<not>#P" by (rule nex)
  with 1 show ?thesis by force
qed

text \<open>
  The following are proved semantically because they are essentially
  first-order theorems.
\<close>
lemma next_fun1: "|~ \<circle>f<x> = f<\<circle>x>"
  by (auto simp: nexts_def)

lemma next_fun2: "|~ \<circle>f<x,y> = f<\<circle>x,\<circle>y>"
  by (auto simp: nexts_def)

lemma next_fun3: "|~ \<circle>f<x,y,z> = f<\<circle>x,\<circle>y,\<circle>z>"
  by (auto simp: nexts_def)

lemma next_fun4: "|~ \<circle>f<x,y,z,zz> = f<\<circle>x,\<circle>y,\<circle>z,\<circle>zz>"
  by (auto simp: nexts_def)

lemma next_forall: "|~ \<circle>(\<forall> x. P x) = (\<forall> x. \<circle> P x)"
  by (auto simp: nexts_def)

lemma next_exists: "|~ \<circle>(\<exists> x. P x) = (\<exists> x. \<circle> P x)"
  by (auto simp: nexts_def)

lemma next_exists1: "|~ \<circle>(\<exists>! x. P x) = (\<exists>! x. \<circle> P x)"
  by (auto simp: nexts_def)

text \<open>
  Rewrite rules to push the ``next'' operator inward over connectives.
  (Note that axiom \<open>pax1\<close> and theorem \<open>next_const\<close> are anyway active
  as rewrite rules.)
\<close>
lemmas next_commutes[int_rewrite] =
  next_and next_or next_imp next_eq 
  next_fun1 next_fun2 next_fun3 next_fun4
  next_forall next_exists next_exists1

lemmas ifs_eq[int_rewrite] = after_fun3 next_fun3 before_fun3

lemmas next_always = pax3

lemma t1: "|~ \<circle>$x = x$"
  by (simp add: before_def after_def nexts_def first_tail_second)

text \<open>
  Theorem \<open>next_eventually\<close> should not be used "blindly".
\<close>
lemma next_eventually:
  assumes h: "stutinv F"
  shows "|~ \<diamond>F \<longrightarrow> \<not>F \<longrightarrow> \<circle>\<diamond>F"
proof -
  from h have 1: "stutinv (TEMP \<not>F)" by (rule stut_not)
  have "|~ \<box>\<not>F = (\<not>F \<and> \<circle>\<box>\<not>F)" unfolding T7[OF pre_id_unch[OF 1], int_rewrite] by simp
  thus ?thesis by (auto simp: eventually_def)
qed

lemma next_action: "|~ \<box>[P]_v \<longrightarrow> \<circle>\<box>[P]_v"
  using pax4[of P v] by auto

subsection "Higher Level Derived Rules"

text \<open>
  In most verification tasks the low-level rules discussed above are not used directly. 
  Here, we derive some higher-level rules more suitable for verification. In particular, 
  variants of Lamport's rules \<open>TLA1\<close>, \<open>TLA2\<close>, \<open>INV1\<close> and \<open>INV2\<close>
  are derived, where \<open>|~\<close> is used where appropriate.
\<close>

theorem TLA1: 
  assumes H: "|~ P \<and> Unchanged f \<longrightarrow> \<circle>P" 
  shows "\<turnstile> \<box>P = (P \<and> \<box>[P \<longrightarrow> \<circle>P]_f)"
proof (rule int_iffI)
  from ax1[of P] M0[of P f] show "\<turnstile> \<box>P \<longrightarrow> P \<and> \<box>[P \<longrightarrow> \<circle>P]_f" by force
next
  from ax3[OF H] show "\<turnstile> P \<and> \<box>[P \<longrightarrow> \<circle>P]_f \<longrightarrow> \<box>P" by auto
qed

theorem TLA2:
  assumes h1: "\<turnstile> P \<longrightarrow> Q"
      and h2: "|~ P \<and> \<circle>P \<and> [A]_f \<longrightarrow> [B]_g"
  shows "\<turnstile> \<box>P \<and> \<box>[A]_f \<longrightarrow> \<box>Q \<and> \<box>[B]_g"
proof -
  from h2 have "\<turnstile> \<box>[P \<and> \<circle>P \<and> [A]_f]_g \<longrightarrow> \<box>[[B]_g]_g" by (rule M2)
  hence "\<turnstile> \<box>[P \<and> \<circle>P]_g \<and> \<box>[[A]_f]_g \<longrightarrow> \<box>[B]_g" by (auto simp add: M8[int_rewrite])
  with M1[of P g] T4[of A f g] have "\<turnstile> \<box>P \<and> \<box>[A]_f \<longrightarrow> \<box>[B]_g" by force
  with h1[THEN STL4] show ?thesis by force
qed

theorem INV1: 
  assumes H: "|~ I \<and> [N]_f \<longrightarrow> \<circle>I"
  shows "\<turnstile> I \<and> \<box>[N]_f \<longrightarrow> \<box>I"
proof -
  from H have "|~ [N]_f \<longrightarrow> I \<longrightarrow> \<circle>I" by auto
  hence "\<turnstile> \<box>[[N]_f]_f \<longrightarrow> \<box>[I \<longrightarrow> \<circle>I]_f" by (rule M2)
  moreover
  from H have "|~ I \<and> Unchanged f \<longrightarrow> \<circle>I" by (auto simp: actrans_def)
  hence "\<turnstile> \<box>[I \<longrightarrow> \<circle>I]_f \<longrightarrow> I \<longrightarrow> \<box>I" by (rule ax3)
  ultimately show ?thesis by force
qed

theorem INV2: "\<turnstile> \<box>I \<longrightarrow> \<box>[N]_f = \<box>[N \<and> I \<and> \<circle>I]_f"
proof -
  from M1[of I f] have "\<turnstile> \<box>I \<longrightarrow> (\<box>[N]_f = \<box>[N]_f \<and> \<box>[I \<and> \<circle>I]_f)" by auto
  thus ?thesis by (auto simp: M8[int_rewrite])
qed

lemma R1:
  assumes H: "|~ Unchanged w \<longrightarrow> Unchanged v" 
  shows "\<turnstile> \<box>[F]_w \<longrightarrow> \<box>[F]_v"
proof -
  from H have "|~ [F]_w \<longrightarrow> [F]_v" by (auto simp: actrans_def)
  thus ?thesis by (rule M11)
qed

theorem invmono:
  assumes h1: "\<turnstile> I \<longrightarrow> P"
      and h2: "|~ P \<and> [N]_f \<longrightarrow> \<circle>P" 
  shows "\<turnstile> I \<and> \<box>[N]_f \<longrightarrow> \<box>P"
  using h1 INV1[OF h2] by force

theorem preimpsplit:
  assumes "|~ I \<and> N \<longrightarrow> Q"
      and "|~ I \<and> Unchanged v \<longrightarrow> Q"
  shows "|~ I \<and> [N]_v \<longrightarrow> Q"
  using assms[unlift_rule] by (auto simp: actrans_def)

theorem refinement1: 
  assumes h1: "\<turnstile> P \<longrightarrow> Q"
      and h2: "|~ I \<and> \<circle>I \<and> [A]_f \<longrightarrow> [B]_g"
  shows "\<turnstile> P \<and> \<box>I \<and> \<box>[A]_f \<longrightarrow> Q \<and> \<box>[B]_g"
proof -
  have "\<turnstile> I \<longrightarrow> #True" by simp
  from this h2 have "\<turnstile> \<box>I \<and> \<box>[A]_f \<longrightarrow> \<box>#True \<and> \<box>[B]_g" by (rule TLA2)
  with h1 show ?thesis by force
qed

theorem inv_join:
  assumes "\<turnstile> P \<longrightarrow> \<box>Q" and "\<turnstile> P \<longrightarrow> \<box>R"
  shows "\<turnstile> P \<longrightarrow> \<box>(Q \<and> R)"
  using assms[unlift_rule] unfolding STL5[int_rewrite] by force

lemma inv_cases: "\<turnstile> \<box>(A \<longrightarrow> B) \<and> \<box>(\<not>A \<longrightarrow> B) \<longrightarrow> \<box>B"
proof -
  have "\<turnstile> \<box>((A \<longrightarrow> B) \<and> (\<not>A \<longrightarrow> B)) \<longrightarrow> \<box>B" by (rule STL4) auto
  thus ?thesis by (simp add: STL5[int_rewrite])
qed

end
