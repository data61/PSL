(*  Title:       Inductive definition of Hoare logic
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory PsHoare imports PsLang begin

subsection\<open>Hoare logic for partial correctness\<close>

type_synonym 'a assn = "'a \<Rightarrow> state \<Rightarrow> bool"
type_synonym 'a cntxt = "('a assn \<times> com \<times> 'a assn)set"

definition
 valid :: "'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
 "\<Turnstile> {P}c{Q} \<equiv> (\<forall>s t z. s -c\<rightarrow> t \<longrightarrow> P z s \<longrightarrow> Q z t)"

definition
 valids :: "'a cntxt \<Rightarrow> bool" ("|\<Turnstile> _" 50) where
 "|\<Turnstile> D \<equiv> (\<forall>(P,c,Q) \<in> D. \<Turnstile> {P}c{Q})"

definition
 nvalid :: "nat \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile>_ {(1_)}/ (_)/ {(1_)}" 50) where
 "\<Turnstile>n {P}c{Q} \<equiv> (\<forall>s t z. s -c-n\<rightarrow> t \<longrightarrow> P z s \<longrightarrow> Q z t)"

definition
 nvalids :: "nat \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("|\<Turnstile>'__/ _" 50) where
 "|\<Turnstile>_n C \<equiv> (\<forall>(P,c,Q) \<in> C. \<Turnstile>n {P}c{Q})"

text\<open>We now need an additional notion of
validity \mbox{\<open>C |\<Turnstile> D\<close>} where @{term D} is a set as well. The
reason is that we can now have mutually recursive procedures whose
correctness needs to be established by simultaneous induction. Instead
of sets of Hoare triples we may think of conjunctions. We define both
\<open>C |\<Turnstile> D\<close> and its relativized version:\<close>

definition
 cvalids :: "'a cntxt \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("_ |\<Turnstile>/ _" 50) where
  "C |\<Turnstile> D \<longleftrightarrow> |\<Turnstile> C \<longrightarrow> |\<Turnstile> D"

definition
 cnvalids :: "'a cntxt \<Rightarrow> nat \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("_ |\<Turnstile>'__/ _" 50) where
  "C |\<Turnstile>_n D \<longleftrightarrow> |\<Turnstile>_n C \<longrightarrow> |\<Turnstile>_n D"

text\<open>Our Hoare logic now defines judgements of the form \<open>C \<tturnstile>
D\<close> where both @{term C} and @{term D} are (potentially infinite) sets
of Hoare triples; \<open>C \<turnstile> {P}c{Q}\<close> is simply an abbreviation for
\<open>C \<tturnstile> {(P,c,Q)}\<close>.\<close>

inductive
  hoare :: "'a cntxt \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("_ \<tturnstile>/ _" 50)
  and hoare3 :: "'a cntxt \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("_ \<turnstile>/ ({(1_)}/ (_)/ {(1_)})" 50)
where
  "C \<turnstile> {P}c{Q}  \<equiv>  C \<tturnstile> {(P,c,Q)}"
| Do:  "C \<turnstile> {\<lambda>z s. \<forall>t \<in> f s . P z t} Do f {P}"
| Semi: "\<lbrakk> C \<turnstile> {P}c{Q}; C \<turnstile> {Q}d{R} \<rbrakk> \<Longrightarrow> C \<turnstile> {P} c;d {R}"
| If: "\<lbrakk> C \<turnstile> {\<lambda>z s. P z s \<and> b s}c{Q}; C \<turnstile> {\<lambda>z s. P z s \<and> \<not>b s}d{Q}  \<rbrakk> \<Longrightarrow>
      C \<turnstile> {P} IF b THEN c ELSE d {Q}"
| While: "C \<turnstile> {\<lambda>z s. P z s \<and> b s} c {P} \<Longrightarrow>
          C \<turnstile> {P} WHILE b DO c {\<lambda>z s. P z s \<and> \<not>b s}"

| Conseq: "\<lbrakk> C \<turnstile> {P'}c{Q'};
             \<forall>s t. (\<forall>z. P' z s \<longrightarrow> Q' z t) \<longrightarrow> (\<forall>z. P z s \<longrightarrow> Q z t) \<rbrakk> \<Longrightarrow>
           C \<turnstile> {P}c{Q}"

| Call: "\<lbrakk> \<forall>(P,c,Q) \<in> C. \<exists>p. c = CALL p;
     C \<tturnstile> {(P,b,Q). \<exists>p. (P,CALL p,Q) \<in> C \<and> b = body p} \<rbrakk>
  \<Longrightarrow> {} \<tturnstile> C"

| Asm: "(P,CALL p,Q) \<in> C \<Longrightarrow> C \<turnstile> {P} CALL p {Q}"

| ConjI: "\<forall>(P,c,Q) \<in> D. C \<turnstile> {P}c{Q}  \<Longrightarrow>  C \<tturnstile> D"
| ConjE: "\<lbrakk> C \<tturnstile> D; (P,c,Q) \<in> D \<rbrakk> \<Longrightarrow> C \<turnstile> {P}c{Q}"

| Local: "\<lbrakk> \<forall>s'. C \<turnstile> {\<lambda>z s. P z s' \<and> s = f s'} c {\<lambda>z t. Q z (g s' t)} \<rbrakk> \<Longrightarrow>
        C \<turnstile> {P} LOCAL f;c;g {Q}"
monos split_beta


lemmas valid_defs = valid_def valids_def cvalids_def
                    nvalid_def nvalids_def cnvalids_def

theorem "C \<tturnstile> D  \<Longrightarrow>  C |\<Turnstile> D"

txt\<open>\noindent As before, we prove a generalization of @{prop"C |\<Turnstile> D"},
namely @{prop"\<forall>n. C |\<Turnstile>_n D"}, by induction on @{prop"C \<tturnstile> D"}, with an
induction on @{term n} in the @{term CALL} case.\<close>

apply(subgoal_tac "\<forall>n. C |\<Turnstile>_n D")
apply(unfold valid_defs exec_iff_execn[THEN eq_reflection])
 apply fast
apply(erule hoare.induct)
      apply simp
     apply simp
     apply fast
    apply simp
   apply clarify
   apply(drule while_rule)
   prefer 3
   apply (assumption, assumption)
   apply simp
  apply simp
  apply fast
 apply(rule allI, rule impI)
 apply(induct_tac n)
  apply force
 apply clarify
 apply(frule bspec, assumption)
 apply (simp(no_asm_use))
 apply fast
apply simp
apply fast

apply simp
apply fast

apply fast

apply fastforce
done

definition MGT :: "com \<Rightarrow> state assn \<times> com \<times> state assn" where
  [simp]: "MGT c = (\<lambda>z s. z = s, c, \<lambda>z t. z -c\<rightarrow> t)"

lemma strengthen_pre:
 "\<lbrakk> \<forall>z s. P' z s \<longrightarrow> P z s; C\<turnstile> {P}c{Q}  \<rbrakk> \<Longrightarrow> C\<turnstile> {P'}c{Q}"
by(rule hoare.Conseq, assumption, blast)

lemma MGT_implies_complete:
  "{} \<tturnstile> {MGT c} \<Longrightarrow> \<Turnstile> {P}c{Q} \<Longrightarrow> {} \<turnstile> {P}c{Q::state assn}"
apply(unfold MGT_def)
apply (erule hoare.Conseq)
apply(simp add: valid_defs)
done

lemma MGT_lemma: "\<forall>p. C \<tturnstile> {MGT(CALL p)}  \<Longrightarrow>  C \<tturnstile> {MGT c}"
apply (simp)
apply(induct_tac c)
    apply (rule strengthen_pre[OF _ hoare.Do])
    apply blast
   apply simp
   apply (rule hoare.Semi)
    apply blast
   apply (rule hoare.Conseq)
    apply blast
   apply blast
  apply clarsimp
  apply(rule hoare.If)
   apply(rule hoare.Conseq)
    apply blast
   apply simp
  apply(rule hoare.Conseq)
   apply blast
  apply simp
 prefer 2
 apply simp
apply(rename_tac b c)
apply(rule hoare.Conseq)
 apply(rule_tac P = "\<lambda>z s. (z,s) \<in> ({(s,t). b s \<and> s -c\<rightarrow> t})^*"
       in hoare.While)
 apply(erule hoare.Conseq)
 apply(blast intro:rtrancl_into_rtrancl)
apply clarsimp
apply(rename_tac s t)
apply(erule_tac x = s in allE)
apply clarsimp
apply(erule converse_rtrancl_induct)
 apply(blast intro:exec.intros)
apply(fast elim:exec.WhileTrue)

apply(fastforce intro: hoare.Local elim!: hoare.Conseq)
done

lemma MGT_body: "(P, CALL p, Q) = MGT (CALL pa) \<Longrightarrow> C \<tturnstile> {MGT (body p)} \<Longrightarrow> C \<turnstile> {P} body p {Q}"
apply clarsimp
done

declare MGT_def[simp del]

lemma MGT_CALL: "{} \<tturnstile> {mgt. \<exists>p. mgt = MGT(CALL p)}"
apply (rule hoare.Call)
 apply(fastforce simp add:MGT_def)
apply(rule hoare.ConjI)
apply clarsimp
apply (erule MGT_body)
apply(rule MGT_lemma)
apply(unfold MGT_def)
apply(fast intro: hoare.Asm)
done

theorem Complete: "\<Turnstile> {P}c{Q}  \<Longrightarrow>  {} \<turnstile> {P}c{Q::state assn}"
apply(rule MGT_implies_complete)
 prefer 2
 apply assumption
apply (rule MGT_lemma)
apply(rule allI)
apply(unfold MGT_def)
apply(rule hoare.ConjE[OF MGT_CALL])
apply(simp add:MGT_def fun_eq_iff)
done

end
