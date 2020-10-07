(*  Title:       Inductive definition of Hoare logic
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory PHoare imports PLang begin

subsection\<open>Hoare logic for partial correctness\<close>

text\<open>Taking auxiliary variables seriously means that assertions must
now depend on them as well as on the state. Initially we do not fix
the type of auxiliary variables but parameterize the type of
assertions with a type variable @{typ 'a}:\<close>

type_synonym 'a assn = "'a \<Rightarrow> state \<Rightarrow> bool"

text\<open>
The second major change is the need to reason about Hoare
triples in a context: proofs about recursive procedures are conducted
by induction where we assume that all @{term CALL}s satisfy the given
pre/postconditions and have to show that the body does as well. The
assumption is stored in a context, which is a set of Hoare triples:\<close>

type_synonym 'a cntxt = "('a assn \<times> com \<times> 'a assn)set"

text\<open>\noindent In the presence of only a single procedure the context will
always be empty or a singleton set. With multiple procedures, larger
sets can arise.

Now that we have contexts, validity becomes more complicated. Ordinary
validity (w.r.t.\ partial correctness) is still what it used to be,
except that we have to take auxiliary variables into account as well:
\<close>

definition
 valid :: "'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
     "\<Turnstile> {P}c{Q} \<longleftrightarrow> (\<forall>s t. s -c\<rightarrow> t \<longrightarrow> (\<forall>z. P z s \<longrightarrow> Q z t))"

text\<open>\noindent Auxiliary variables are always denoted by @{term z}.

Validity of a context and validity of a Hoare triple in a context are defined
as follows:\<close>

definition
 valids :: "'a cntxt \<Rightarrow> bool" ("|\<Turnstile> _" 50) where
  [simp]: "|\<Turnstile> C \<equiv> (\<forall>(P,c,Q) \<in> C. \<Turnstile> {P}c{Q})"

definition
 cvalid :: "'a cntxt \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("_ \<Turnstile>/ {(1_)}/ (_)/ {(1_)}" 50) where
  "C \<Turnstile> {P}c{Q} \<longleftrightarrow> |\<Turnstile> C \<longrightarrow> \<Turnstile> {P}c{Q}"

text\<open>\noindent Note that @{prop"{} \<Turnstile> {P}c{Q}"} is equivalent to
@{prop"\<Turnstile> {P}c{Q}"}.

Unfortunately, this is not the end of it. As we have two
semantics, \<open>-c\<rightarrow>\<close> and \<open>-c-n\<rightarrow>\<close>, we also need a second notion
of validity parameterized with the recursion depth @{term n}:\<close>

definition
 nvalid :: "nat \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile>_ {(1_)}/ (_)/ {(1_)}" 50) where
  "\<Turnstile>n {P}c{Q} \<equiv> (\<forall>s t. s -c-n\<rightarrow> t \<longrightarrow> (\<forall>z. P z s \<longrightarrow> Q z t))"

definition
 nvalids :: "nat \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("|\<Turnstile>'__/ _" 50) where
  "|\<Turnstile>_n C \<equiv> (\<forall>(P,c,Q) \<in> C. \<Turnstile>n {P}c{Q})"

definition
 cnvalid :: "'a cntxt \<Rightarrow> nat \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("_ \<Turnstile>_/ {(1_)}/ (_)/ {(1_)}" 50) where
  "C \<Turnstile>n {P}c{Q} \<longleftrightarrow> |\<Turnstile>_n C \<longrightarrow> \<Turnstile>n {P}c{Q}"

text\<open>Finally we come to the proof system for deriving triples in a context:\<close>

inductive
  hoare :: "'a cntxt \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("_ \<turnstile>/ ({(1_)}/ (_)/ {(1_)})" 50)
where
   (*<*)Do:(*>*)"C \<turnstile> {\<lambda>z s. \<forall>t \<in> f s . P z t} Do f {P}"

 | (*<*)Semi:(*>*)"\<lbrakk> C \<turnstile> {P}c1{Q}; C \<turnstile> {Q}c2{R} \<rbrakk> \<Longrightarrow> C \<turnstile> {P} c1;c2 {R}"

 | (*<*)If:(*>*)"\<lbrakk> C \<turnstile> {\<lambda>z s. P z s \<and> b s}c1{Q};  C \<turnstile> {\<lambda>z s. P z s \<and> \<not>b s}c2{Q}  \<rbrakk>
   \<Longrightarrow> C \<turnstile> {P} IF b THEN c1 ELSE c2 {Q}"

 | (*<*)While:(*>*)"C \<turnstile> {\<lambda>z s. P z s \<and> b s} c {P}
   \<Longrightarrow> C \<turnstile> {P} WHILE b DO c {\<lambda>z s. P z s \<and> \<not>b s}"

 | (*<*)Conseq:(*>*)"\<lbrakk> C \<turnstile> {P'}c{Q'};  \<forall>s t. (\<forall>z. P' z s \<longrightarrow> Q' z t) \<longrightarrow> (\<forall>z. P z s \<longrightarrow> Q z t) \<rbrakk>
   \<Longrightarrow> C \<turnstile> {P}c{Q}"

 | (*<*)Call:(*>*)"{(P,CALL,Q)} \<turnstile> {P}body{Q} \<Longrightarrow> {} \<turnstile> {P} CALL {Q}"

 | (*<*)Asm:(*>*)"{(P,CALL,Q)} \<turnstile> {P} CALL {Q}"
 | (*<*)Local:(*>*) "\<lbrakk> \<forall>s'. C \<turnstile> {\<lambda>z s. P z s' \<and> s = f s'} c {\<lambda>z t. Q z (g s' t)} \<rbrakk> \<Longrightarrow>
        C \<turnstile> {P} LOCAL f;c;g {Q}"

abbreviation hoare1 :: "'a cntxt \<Rightarrow> 'a assn \<times> com \<times> 'a assn \<Rightarrow> bool" ("_ \<turnstile> _") where
  "C \<turnstile> x \<equiv> C \<turnstile> {fst x}fst (snd x){snd (snd x)}"

text\<open>\noindent The first four rules are familiar, except for their adaptation
to auxiliary variables. The @{term CALL} rule embodies induction and
has already been motivated above. Note that it is only applicable if
the context is empty. This shows that we never need nested induction.
For the same reason the assumption rule (the last rule) is stated with
just a singleton context.

The rule of consequence is explained in the accompanying paper.
\<close>

lemma strengthen_pre:
 "\<lbrakk> \<forall>z s. P' z s \<longrightarrow> P z s; C\<turnstile> {P}c{Q}  \<rbrakk> \<Longrightarrow> C\<turnstile> {P'}c{Q}"
by(rule hoare.Conseq, assumption, blast)

lemmas valid_defs = valid_def valids_def cvalid_def
                    nvalid_def nvalids_def cnvalid_def

theorem hoare_sound: "C \<turnstile> {P}c{Q}  \<Longrightarrow>  C \<Turnstile> {P}c{Q}"
txt\<open>\noindent requires a generalization: @{prop"\<forall>n. C \<Turnstile>n
{P}c{Q}"} is proved instead, from which the actual theorem follows
directly via lemma @{thm[source]exec_iff_execn} in \S\ref{sec:proc1-lang}.
The generalization
is proved by induction on @{term c}. The reason for the generalization
is that soundness of the @{term CALL} rule is proved by induction on the
maximal call depth, i.e.\ @{term n}.\<close>
apply(subgoal_tac "\<forall>n. C \<Turnstile>n {P}c{Q}")
apply(unfold valid_defs exec_iff_execn)
 apply fast
apply(erule hoare.induct)
        apply simp
       apply fast
      apply simp
     apply clarify
     apply(drule while_rule)
       prefer 3
       apply (assumption, assumption)
     apply fast
    apply fast
   prefer 2
   apply simp
 apply(rule allI, rule impI)
 apply(induct_tac n)
  apply blast
 apply clarify
 apply (simp(no_asm_use))
 apply blast
apply auto
done

text\<open>
The completeness proof employs the notion of a \emph{most general triple} (or
\emph{most general formula}):\<close>

definition
  MGT :: "com \<Rightarrow> state assn \<times> com \<times> state assn" where
  "MGT c = (\<lambda>z s. z = s, c, \<lambda>z t. z -c\<rightarrow> t)"

declare MGT_def[simp]

text\<open>\noindent Note that the type of @{term z} has been identified with
@{typ state}.  This means that for every state variable there is an auxiliary
variable, which is simply there to record the value of the program variables
before execution of a command. This is exactly what, for example, VDM offers
by allowing you to refer to the pre-value of a variable in a
postcondition. The intuition behind @{term"MGT c"} is
that it completely describes the operational behaviour of @{term c}.  It is
easy to see that, in the presence of the new consequence rule,
\mbox{@{prop"{} \<turnstile> MGT c"}} implies completeness:\<close>

lemma MGT_implies_complete:
 "{} \<turnstile> MGT c  \<Longrightarrow>  {} \<Turnstile> {P}c{Q}  \<Longrightarrow>  {} \<turnstile> {P}c{Q::state assn}"
apply(simp add: MGT_def)
apply (erule hoare.Conseq)
apply(simp add: valid_defs)
done

text\<open>In order to discharge @{prop"{} \<turnstile> MGT c"} one proves\<close>

lemma MGT_lemma: "C \<turnstile> MGT CALL  \<Longrightarrow>  C \<turnstile> MGT c"
apply (simp)
apply(induct_tac c)
      apply (rule strengthen_pre[OF _ hoare.Do])
      apply blast
     apply(blast intro:hoare.Semi hoare.Conseq)
    apply(rule hoare.If)
    apply(erule hoare.Conseq)
     apply simp
    apply(erule hoare.Conseq)
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
  apply simp
 apply(fast elim:exec.WhileTrue)
apply(fastforce intro: hoare.Local elim!: hoare.Conseq)
done

text\<open>\noindent The proof is by induction on @{term c}. In the @{term
While}-case it is easy to show that @{term"\<lambda>z t. (z,t) \<in> ({(s,t). b
s \<and> s -c\<rightarrow> t})^*"} is invariant. The precondition \mbox{@{term[source]"\<lambda>z s. z=s"}}
establishes the invariant and a reflexive transitive closure
induction shows that the invariant conjoined with @{prop"\<not>b t"}
implies the postcondition \mbox{@{term"\<lambda>z t. z -WHILE b DO c\<rightarrow> t"}}. The
remaining cases are trivial.

Using the @{thm[source]MGT_lemma} (together with the \<open>CALL\<close> and the
assumption rule) one can easily derive\<close>

lemma MGT_CALL: "{} \<turnstile> MGT CALL"
apply(simp add: MGT_def)
apply (rule hoare.Call)
apply (rule hoare.Conseq[OF MGT_lemma[simplified], OF hoare.Asm])
apply (fast intro:exec.intros)
done

text\<open>\noindent Using the @{thm[source]MGT_lemma} once more we obtain
@{prop"{} \<turnstile> MGT c"} and thus by @{thm[source]MGT_implies_complete}
completeness.\<close>

theorem "{} \<Turnstile> {P}c{Q}  \<Longrightarrow>  {} \<turnstile> {P}c{Q::state assn}"
apply(erule MGT_implies_complete[OF MGT_lemma[OF MGT_CALL]])
done

end
