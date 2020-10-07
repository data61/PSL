(*  Title:       Inductive definition of Hoare logic
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory Hoare imports Lang begin

subsection\<open>Hoare logic for partial correctness\<close>

text\<open>We continue our semantic approach by modelling assertions just
like boolean expressions, i.e.\ as functions:\<close>

type_synonym assn = "state \<Rightarrow> bool"

text\<open>Hoare triples are triples of the form \<open>{P} c {Q}\<close>, where
the assertions \<open>P\<close> and \<open>Q\<close> are the so-called pre and
postconditions. Such a triple is \emph{valid} (denoted by \<open>\<Turnstile>\<close>)
iff every (terminating) execution starting in a state satisfying \<open>P\<close>
ends up in a state satisfying \<open>Q\<close>:\<close>

definition
 hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
 "\<Turnstile> {P}c{Q} \<longleftrightarrow> (\<forall>s t. s -c\<rightarrow> t \<longrightarrow> P s \<longrightarrow> Q t)"

text\<open>\noindent
This notion of validity is called \emph{partial correctness} because
it does not require termination of @{term c}.

Provability in Hoare logic is indicated by \<open>\<turnstile>\<close> and defined
inductively:\<close>

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
  (*<*)Do:(*>*)"\<turnstile> {\<lambda>s. \<forall>t \<in> f s. P t} Do f {P}"

| (*<*)Semi:(*>*)"\<lbrakk> \<turnstile> {P}c1{Q};  \<turnstile> {Q}c2{R} \<rbrakk>  \<Longrightarrow>  \<turnstile> {P} c1;c2 {R}"

| (*<*)If:(*>*)"\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> b s} c1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not>b s} c2 {Q} \<rbrakk>
  \<Longrightarrow> \<turnstile> {P} IF b THEN c1 ELSE c2 {Q}"

| (*<*)While:(*>*)"\<turnstile> {\<lambda>s. P s \<and> b s} c {P}  \<Longrightarrow>  \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not>b s}"

| (*<*)Conseq:(*>*)"\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P}c{Q};  \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk>  \<Longrightarrow>  \<turnstile> {P'}c{Q'}"

| (*<*)Local:(*>*) "\<lbrakk> \<And>s. P s \<Longrightarrow> P' s (f s); \<forall>s. \<turnstile> {P' s} c {Q \<circ> (g s)} \<rbrakk> \<Longrightarrow>
        \<turnstile> {P} LOCAL f;c;g {Q}"

text\<open>Soundness is proved by induction on the derivation of @{prop"\<turnstile>
{P} c {Q}"}:\<close>

theorem hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
apply(unfold hoare_valid_def)
apply(erule hoare.induct)
      apply blast
     apply blast
    apply clarsimp
   apply clarify
   apply(drule while_rule)
   prefer 3
   apply (assumption, assumption, blast)
  apply blast
apply clarify
apply(erule allE)
apply clarify
apply(erule allE)
apply(erule allE)
apply(erule impE)
apply assumption
apply simp
apply(erule mp)
apply(simp)
done

text\<open>
Completeness is not quite as straightforward, but still easy. The
proof is best explained in terms of the \emph{weakest precondition}:\<close>

definition
 wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
 "wp c Q = (\<lambda>s. \<forall>t. s -c\<rightarrow> t \<longrightarrow> Q t)"

text\<open>\noindent Dijkstra calls this the weakest \emph{liberal}
precondition to emphasize that it corresponds to partial
correctness. We use ``weakest precondition'' all the time and let the
context determine if we talk about partial or total correctness ---
the latter is introduced further below.

The following lemmas about @{term wp} are easily derived:
\<close>

lemma [simp]: "wp (Do f) Q = (\<lambda>s. \<forall>t \<in> f s. Q(t))"
apply(unfold wp_def)
apply(rule ext)
apply blast
done

lemma [simp]: "wp (c\<^sub>1;c\<^sub>2) R = wp c\<^sub>1 (wp c\<^sub>2 R)"
apply(unfold wp_def)
apply(rule ext)
apply blast
done

lemma [simp]:
 "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. wp (if b s then c\<^sub>1 else c\<^sub>2) Q s)"
apply(unfold wp_def)
apply(rule ext)
apply auto
done

lemma wp_while:
 "wp (WHILE b DO c) Q =
           (\<lambda>s. if b s then wp (c;WHILE b DO c) Q s else Q s)"
apply(rule ext)
apply(unfold wp_def)
apply auto
apply(blast intro:exec.intros)
apply(simp add:unfold_while)
apply(blast intro:exec.intros)
apply(simp add:unfold_while)
done

lemma [simp]:
 "wp (LOCAL f;c;g) Q = (\<lambda>s. wp c (Q o (g s)) (f s))"
apply(unfold wp_def)
apply(rule ext)
apply auto
done

lemma strengthen_pre: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile> {P}c{Q}  \<rbrakk> \<Longrightarrow> \<turnstile> {P'}c{Q}"
by(erule hoare.Conseq, assumption, blast)

lemma weaken_post: "\<lbrakk> \<turnstile> {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow> \<turnstile> {P}c{Q'}"
apply(rule hoare.Conseq)
apply(fast, assumption, assumption)
done

text\<open>By induction on @{term c} one can easily prove\<close>

lemma wp_is_pre[rule_format]: "\<turnstile> {wp c Q} c {Q}"
apply (induct c arbitrary: Q)
apply simp_all

apply(blast intro:hoare.Do hoare.Conseq)

apply(blast intro:hoare.Semi hoare.Conseq)

apply(blast intro:hoare.If hoare.Conseq)

apply(rule weaken_post)
apply(rule hoare.While)
apply(rule strengthen_pre)
prefer 2
apply blast
apply(clarify)
apply(drule fun_eq_iff[THEN iffD1, OF wp_while, THEN spec, THEN iffD1])
apply simp
apply(clarify)
apply(drule fun_eq_iff[THEN iffD1, OF wp_while, THEN spec, THEN iffD1])
apply(simp split:if_split_asm)

apply(fast intro!: hoare.Local)
done

text\<open>\noindent
from which completeness follows more or less directly via the
rule of consequence:\<close>

theorem hoare_relative_complete: "\<Turnstile> {P}c{Q}  \<Longrightarrow>  \<turnstile> {P}c{Q}"
apply (rule strengthen_pre[OF _ wp_is_pre])
apply(unfold hoare_valid_def wp_def)
apply blast
done

end
