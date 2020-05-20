subsection \<open>Decomposing Conditionals\<close>

theory Conditionals
imports
  Complex_Main
  "../Case_Labeling"
  "HOL-Eisbach.Eisbach"
begin

context begin
  interpretation Labeling_Syntax .

  lemma DC_conj:
    assumes "C\<langle>inp,ct,outp': a\<rangle>" "C\<langle>outp',ct,outp: b\<rangle>"
    shows "C\<langle>inp,ct,outp: a \<and> b\<rangle>"
    using assms unfolding LABEL_simps by auto

  lemma DC_if:
    fixes ct defines "ct' \<equiv> \<lambda>pos name. (name, pos,[]) # ct"
    assumes "H\<langle>ct' inp ''then'': a\<rangle> \<Longrightarrow> C\<langle>Suc inp,ct' inp ''then'', outp': b\<rangle>"
    assumes "H\<langle>ct' outp' ''else'': \<not>a\<rangle> \<Longrightarrow> C\<langle>Suc outp',ct' outp' ''else'', outp: c\<rangle>"
    shows "C\<langle>inp,ct,outp: if a then b else c\<rangle>"
    using assms(2-) unfolding LABEL_simps by auto

  lemma DC_final:
    assumes "V\<langle>(''g'',inp,[]), ct: a\<rangle>"
    shows "C\<langle>inp,ct,Suc inp: a\<rangle>"
    using assms unfolding LABEL_simps by auto

end

method vcg_dc = (intro DC_conj DC_if; rule DC_final)

lemma
  assumes a: "a"
    and d: "b \<Longrightarrow> c \<Longrightarrow> d"
    and d': "b \<Longrightarrow> c \<Longrightarrow> d'"
    and e: "b \<Longrightarrow> \<not>c \<Longrightarrow> e"
    and f: "\<not>b \<Longrightarrow> f"
  shows "a \<and> (if b then (if c then d \<and> d' else e) else f)"
  apply (rule Initial_Label)
  apply vcg_dc
proof casify
  case g show ?case by (fact a)
next
  case "then" note b = \<open>b\<close>
  { case "then" note c = \<open>c\<close>
    { case g show ?case using b c by (fact d)
    next
      case ga show ?case using b c by (fact d')
    }
  next
    case else
    { case g show ?case using "then" else by (fact e) }
  }
next
  case "else"
  { case g show ?case using else by (fact f) }
qed



subsection \<open>Protecting similar subgoals\<close>

text \<open>
  The proof below fails if the @{verbatim disambig_subgoals} option is omitted: all three
  subgoals have the same conclusion and can be discharged without using their assumptions.
  If the case @{verbatim g} is solved first, it discharges instead the subgoal @{prop "a \<Longrightarrow> b"},
  making the case @{command then} fail afterwards.

  The @{verbatim disambig_subgoals} options prevents this by inserting vacuous assumptions.
\<close>

lemma
  assumes b
  shows "(if a then b else b) \<and> b"
  apply (rule Initial_Label)
  apply vcg_dc
proof (casify (disambig_subgoals))
  case g show ?case by (fact \<open>b\<close>)
next
  case "then" case g show ?case by (fact \<open>b\<close>)
next
  case "else" case g show ?case by (fact \<open>b\<close>)
qed



subsection \<open>Unnamed Cases\<close>

lemma
  assumes "a \<Longrightarrow> b" "\<not>a \<Longrightarrow> c" "d"
  shows "(if a then b else c) \<and> d"
  apply (rule Initial_Label)
  apply vcg_dc
  apply (simp_all only: LABEL_simps)[2]
proof (casify (disambig_subgoals))
  case unnamed from \<open>a\<close> show ?case by fact
next
  case unnameda from \<open>\<not>a\<close> show ?case by fact
next
  case g show ?case by fact
qed

end
