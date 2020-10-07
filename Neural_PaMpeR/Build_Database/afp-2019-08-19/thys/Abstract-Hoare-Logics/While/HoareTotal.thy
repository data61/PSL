(*  Title:       Inductive definition of Hoare logic for total correctness
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory HoareTotal imports Hoare Termi begin

subsection\<open>Hoare logic for total correctness\<close>

text\<open>
Now that we have termination, we can define
total validity, \<open>\<Turnstile>\<^sub>t\<close>, as partial validity and guaranteed termination:\<close>

definition
 hoare_tvalid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q} \<and> (\<forall>s. P s \<longrightarrow> c\<down>s)"

text\<open>Proveability of Hoare triples in the proof system for total
correctness is written \<open>\<turnstile>\<^sub>t {P}c{Q}\<close> and defined
inductively. The rules for \<open>\<turnstile>\<^sub>t\<close> differ from those for
\<open>\<turnstile>\<close> only in the one place where nontermination can arise: the
@{term While}-rule.\<close>

inductive
  thoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t ({(1_)}/ (_)/ {(1_)})" 50)
where
  Do:  "\<turnstile>\<^sub>t {\<lambda>s. (\<forall>t \<in> f s. P t) \<and> f s \<noteq> {}} Do f {P}"
| Semi: "\<lbrakk> \<turnstile>\<^sub>t {P}c{Q}; \<turnstile>\<^sub>t {Q}d{R} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P} c;d {R}"
| If: "\<lbrakk> \<turnstile>\<^sub>t {\<lambda>s. P s \<and> b s}c{Q}; \<turnstile>\<^sub>t {\<lambda>s. P s \<and> ~b s}d{Q}  \<rbrakk> \<Longrightarrow>
      \<turnstile>\<^sub>t {P} IF b THEN c ELSE d {Q}"
| While:
  "\<lbrakk>wf r;  \<forall>s'. \<turnstile>\<^sub>t {\<lambda>s. P s \<and> b s \<and> s' = s} c {\<lambda>s. P s \<and> (s,s') \<in> r}\<rbrakk>
   \<Longrightarrow> \<turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>s. P s \<and> \<not>b s}"
| Conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>t {P'}c{Q'}"

| Local: "(!!s. P s \<Longrightarrow> P' s (f s)) \<Longrightarrow> \<forall>p. \<turnstile>\<^sub>t {P' p} c {Q o (g p)} \<Longrightarrow>
        \<turnstile>\<^sub>t {P} LOCAL f;c;g {Q}"

text\<open>\noindent The@{term While}- rule is like the one for partial
correctness but it requires additionally that with every execution of
the loop body a wellfounded relation (@{prop"wf r"}) on the state
space decreases.

The soundness theorem\<close>

(* Tried to use this lemma to simplify the soundness proof.
   But "\<turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> (!s. P s \<longrightarrow> c\<down>s)" is not provable because too weak
lemma total_implies_partial: "\<turnstile>\<^sub>t {P} c {Q} \<Longrightarrow> \<turnstile> {P} c {Q}"
apply(erule thoare.induct)
      apply(rule hoare.intros)
        apply (clarify) apply assumption
      apply(rule hoare.intros)
      apply blast
     apply(blast intro:hoare.intros)
    apply(blast intro:hoare.intros)
   defer
   apply(blast intro:hoare.intros)
  apply(blast intro:hoare.intros)
apply(rule hoare.intros)
apply(rule hoare_relative_complete)
apply(unfold hoare_valid_def)
apply(clarify)
apply(erule allE, erule conjE)
apply(drule hoare_sound)
apply(unfold hoare_valid_def)
apply(blast)
done
*)

theorem "\<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"
apply(unfold hoare_tvalid_def hoare_valid_def)
apply(erule thoare.induct)
      apply blast
     apply blast
    apply clarsimp
   defer
   apply blast
 apply(rule conjI)
  apply clarify
  apply(erule allE)
  apply clarify
  apply(erule allE, erule allE, erule impE, erule asm_rl)
  apply simp
  apply(erule mp)
  apply(simp)
 apply blast
apply(rule conjI)
 apply(rule allI)
 apply(erule wf_induct)
 apply clarify
 apply(drule unfold_while[THEN iffD1])
 apply (simp split: if_split_asm)
 apply blast
apply(rule allI)
apply(erule wf_induct)
apply clarify
apply(case_tac "b x")
 apply (blast intro: termi.WhileTrue)
apply (erule termi.WhileFalse)
done
(*>*)

text\<open>\noindent In the @{term While}-case we perform a
local proof by wellfounded induction over the given relation @{term r}.

The completeness proof proceeds along the same lines as the one for partial
correctness. First we have to strengthen our notion of weakest precondition
to take termination into account:\<close>

definition
 wpt :: "com \<Rightarrow> assn \<Rightarrow> assn" ("wp\<^sub>t") where
  "wp\<^sub>t c Q = (\<lambda>s. wp c Q s \<and> c\<down>s)"

lemmas wp_defs = wp_def wpt_def

lemma [simp]: "wp\<^sub>t (Do f) Q = (\<lambda>s. (\<forall>t \<in> f s. Q t) \<and> f s \<noteq> {})"
by(simp add: wpt_def)

lemma [simp]: "wp\<^sub>t (c\<^sub>1;c\<^sub>2) R = wp\<^sub>t c\<^sub>1 (wp\<^sub>t c\<^sub>2 R)"
apply(unfold wp_defs)
apply(rule ext)
apply blast
done

lemma [simp]:
 "wp\<^sub>t (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = (\<lambda>s. wp\<^sub>t (if b s then c\<^sub>1 else c\<^sub>2) Q s)"
apply(unfold wp_defs)
apply(rule ext)
apply auto
done

lemma [simp]: "wp\<^sub>t (LOCAL f;c;g) Q = (\<lambda>s. wp\<^sub>t c (Q o (g s)) (f s))"
apply(unfold wp_defs)
apply(rule ext)
apply auto
done

lemma strengthen_pre: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t {P}c{Q}  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P'}c{Q}"
by(erule thoare.Conseq, assumption, blast)

lemma weaken_post: "\<lbrakk> \<turnstile>\<^sub>t {P}c{Q}; \<forall>s. Q s \<longrightarrow> Q' s  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q'}"
apply(rule thoare.Conseq)
apply(fast, assumption, assumption)
done

inductive_cases [elim!]: "WHILE b DO c \<down> s"

lemma wp_is_pre[rule_format]: "\<turnstile>\<^sub>t {wp\<^sub>t c Q} c {Q}"
apply (induct c arbitrary: Q)
     apply simp_all
     apply(blast intro:thoare.Do thoare.Conseq)
    apply(blast intro:thoare.Semi thoare.Conseq)
   apply(blast intro:thoare.If thoare.Conseq)
  defer
 apply(fastforce intro!: thoare.Local)
apply(rename_tac b c Q)
apply(rule weaken_post)
 apply(rule_tac b=b and c=c in thoare.While)
  apply(rule_tac b=b and c=c in wf_termi)
 defer
 apply (simp add:wp_defs unfold_while)
apply(rule allI)
apply(rule strengthen_pre)
 prefer 2
 apply fast
apply(clarsimp simp add: wp_defs)
apply(blast intro:exec.intros)
done

text\<open>\noindent The @{term While}-case is interesting because we now have to furnish a
suitable wellfounded relation. Of course the execution of the loop
body directly yields the required relation.
The actual completeness theorem follows directly, in the same manner
as for partial correctness.\<close>

theorem "\<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> \<turnstile>\<^sub>t {P}c{Q}"
apply (rule strengthen_pre[OF _ wp_is_pre])
apply(unfold hoare_tvalid_def hoare_valid_def wp_defs)
apply blast
done

end
