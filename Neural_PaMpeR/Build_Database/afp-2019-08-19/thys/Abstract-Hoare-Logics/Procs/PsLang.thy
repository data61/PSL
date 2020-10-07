(*  Title:       Mutually recursive procedures
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

section "Hoare Logics for Mutually Recursive Procedure"

theory PsLang imports Main begin

subsection\<open>The language\<close>

typedecl state
typedecl pname

type_synonym bexp = "state \<Rightarrow> bool"

datatype
  com = Do "state \<Rightarrow> state set"
      | Semi  com com          ("_; _"  [60, 60] 10)
      | Cond  bexp com com     ("IF _ THEN _ ELSE _"  60)
      | While bexp com         ("WHILE _ DO _"  60)
      | CALL pname
      | Local "(state \<Rightarrow> state)" com "(state \<Rightarrow> state \<Rightarrow> state)"
               ("LOCAL _; _; _" [0,0,60] 60)

consts body :: "pname \<Rightarrow> com"

text\<open>We generalize from a single procedure to a whole set of
procedures following the ideas of von Oheimb~\cite{Oheimb-FSTTCS99}.
The basic setup is modified only in a few places:
\begin{itemize}
\item We introduce a new basic type @{typ pname} of procedure names.
\item Constant @{term body} is now of type @{typ"pname \<Rightarrow> com"}.
\item The @{term CALL} command now has an argument of type @{typ pname},
the name of the procedure that is to be called.
\end{itemize}
\<close>

inductive
  exec :: "state \<Rightarrow> com \<Rightarrow> state \<Rightarrow> bool"   ("_/ -_\<rightarrow>/ _" [50,0,50] 50)
where
    Do:     "t \<in> f s \<Longrightarrow> s -Do f\<rightarrow> t"

  | Semi:   "\<lbrakk> s0 -c1\<rightarrow> s1; s1 -c2\<rightarrow> s2 \<rbrakk> \<Longrightarrow> s0 -c1;c2\<rightarrow> s2"

  | IfTrue:  "\<lbrakk> b s;  s -c1\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2\<rightarrow> t"
  | IfFalse: "\<lbrakk> \<not>b s; s -c2\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c1 ELSE c2\<rightarrow> t"

  | WhileFalse: "\<not>b s \<Longrightarrow> s -WHILE b DO c\<rightarrow> s"
  | WhileTrue:  "\<lbrakk> b s; s -c\<rightarrow> t; t -WHILE b DO c\<rightarrow> u \<rbrakk>
                \<Longrightarrow> s -WHILE b DO c\<rightarrow> u"

  | Call: "s -body p\<rightarrow> t \<Longrightarrow> s -CALL p\<rightarrow> t"

  | Local: "f s -c\<rightarrow> t \<Longrightarrow> s -LOCAL f; c; g\<rightarrow> g s t"

lemma [iff]: "(s -Do f\<rightarrow> t) = (t \<in> f s)"
by(auto elim: exec.cases intro:exec.intros)

lemma [iff]: "(s -c;d\<rightarrow> u) = (\<exists>t. s -c\<rightarrow> t \<and> t -d\<rightarrow> u)"
by(auto elim: exec.cases intro:exec.intros)

lemma [iff]: "(s -IF b THEN c ELSE d\<rightarrow> t) =
              (s -if b s then c else d\<rightarrow> t)"
apply(rule iffI)
 apply(auto elim: exec.cases intro:exec.intros)
apply(auto intro:exec.intros split:if_split_asm)
done

lemma [iff]: "(s -CALL p\<rightarrow> t) = (s -body p\<rightarrow> t)"
by(blast elim: exec.cases intro:exec.intros)

lemma [iff]: "(s -LOCAL f; c; g\<rightarrow> u) = (\<exists>t. f s -c\<rightarrow> t \<and> u = g s t)"
by(fastforce elim: exec.cases intro:exec.intros)

inductive
  execn :: "state \<Rightarrow> com \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"   ("_/ -_-_\<rightarrow>/ _" [50,0,0,50] 50)
where
    Do:     "t \<in> f s \<Longrightarrow> s -Do f-n\<rightarrow> t"

  | Semi:   "\<lbrakk> s0 -c0-n\<rightarrow> s1; s1 -c1-n\<rightarrow> s2 \<rbrakk> \<Longrightarrow> s0 -c0;c1-n\<rightarrow> s2"

  | IfTrue: "\<lbrakk> b s; s -c0-n\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c0 ELSE c1-n\<rightarrow> t"

  | IfFalse: "\<lbrakk> \<not>b s; s -c1-n\<rightarrow> t \<rbrakk> \<Longrightarrow> s -IF b THEN c0 ELSE c1-n\<rightarrow> t"

  | WhileFalse: "\<not>b s \<Longrightarrow> s -WHILE b DO c-n\<rightarrow> s"

  | WhileTrue:  "\<lbrakk> b s; s -c-n\<rightarrow> t; t -WHILE b DO c-n\<rightarrow> u \<rbrakk>
                \<Longrightarrow> s -WHILE b DO c-n\<rightarrow> u"

  | Call:  "s -body p-n\<rightarrow> t \<Longrightarrow> s -CALL p-Suc n\<rightarrow> t"

  | Local: "f s -c-n\<rightarrow> t \<Longrightarrow> s -LOCAL f; c; g-n\<rightarrow> g s t"

lemma [iff]: "(s -Do f-n\<rightarrow> t) = (t \<in> f s)"
by(auto elim: execn.cases intro:execn.intros)

lemma [iff]: "(s -c1;c2-n\<rightarrow> u) = (\<exists>t. s -c1-n\<rightarrow> t \<and> t -c2-n\<rightarrow> u)"
by(best elim: execn.cases intro:execn.intros)

lemma [iff]: "(s -IF b THEN c ELSE d-n\<rightarrow> t) =
              (s -if b s then c else d-n\<rightarrow> t)"
apply auto
apply(blast elim: execn.cases intro:execn.intros)+
done

lemma [iff]: "(s -CALL p- 0\<rightarrow> t) = False"
by(blast elim: execn.cases intro:execn.intros)

lemma [iff]: "(s -CALL p-Suc n\<rightarrow> t) = (s -body p-n\<rightarrow> t)"
by(blast elim: execn.cases intro:execn.intros)

lemma [iff]: "(s -LOCAL f; c; g-n\<rightarrow> u) = (\<exists>t. f s -c-n\<rightarrow> t \<and> u = g s t)"
by(auto elim: execn.cases intro:execn.intros)


lemma exec_mono[rule_format]: "s -c-m\<rightarrow> t \<Longrightarrow> \<forall>n. m \<le> n \<longrightarrow> s -c-n\<rightarrow> t"
apply(erule execn.induct)
       apply(blast)
      apply(blast)
     apply(simp)
    apply(simp)
   apply(simp add:execn.intros)
  apply(blast intro:execn.intros)
 apply(clarify)
 apply(rename_tac m)
 apply(case_tac m)
  apply simp
 apply simp
apply blast
done

lemma exec_iff_execn: "(s -c\<rightarrow> t) = (\<exists>n. s -c-n\<rightarrow> t)"
apply(rule iffI)
 apply(erule exec.induct)
        apply blast
       apply clarify
       apply(rename_tac m n)
       apply(rule_tac x = "max m n" in exI)
       apply(fastforce intro:exec.intros exec_mono simp add:max_def)
      apply fastforce
     apply fastforce
    apply(blast intro:execn.intros)
   apply clarify
   apply(rename_tac m n)
   apply(rule_tac x = "max m n" in exI)
   apply(fastforce elim:execn.WhileTrue exec_mono simp add:max_def)
  apply blast
 apply blast
apply(erule exE, erule execn.induct)
       apply blast
      apply blast
     apply fastforce
    apply fastforce
   apply(erule exec.WhileFalse)
  apply(blast intro: exec.intros)
 apply blast
apply blast
done

lemma while_lemma[rule_format]:
"s -w-n\<rightarrow> t \<Longrightarrow> \<forall>b c. w = WHILE b DO c \<and> P s \<and>
                    (\<forall>s s'. P s \<and> b s \<and> s -c-n\<rightarrow> s' \<longrightarrow> P s') \<longrightarrow> P t \<and> \<not>b t"
apply(erule execn.induct)
apply clarify+
defer
apply clarify+
apply(subgoal_tac "P t")
apply blast
apply blast
done

lemma while_rule:
 "\<lbrakk>s -WHILE b DO c-n\<rightarrow> t; P s; \<And>s s'. \<lbrakk>P s; b s; s -c-n\<rightarrow> s' \<rbrakk> \<Longrightarrow> P s'\<rbrakk>
  \<Longrightarrow> P t \<and> \<not>b t"
apply(drule while_lemma)
prefer 2 apply assumption
apply blast
done

end
