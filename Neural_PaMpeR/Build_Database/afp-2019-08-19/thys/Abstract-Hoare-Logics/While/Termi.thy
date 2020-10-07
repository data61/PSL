(*  Title:       Inductive definition of termination
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory Termi imports Lang begin

subsection\<open>Termination\<close>

text\<open>Although partial correctness appeals because of its simplicity,
in many cases one would like the additional assurance that the command
is guaranteed to termiate if started in a state that satisfies the
precondition. Even to express this we need to define when a command is
guaranteed to terminate. We can do this without modifying our existing
semantics by merely adding a second inductively defined judgement
\<open>c\<down>s\<close> that expresses guaranteed termination of @{term c}
started in state @{term s}:\<close>

inductive
  termi :: "com \<Rightarrow> state \<Rightarrow> bool" (infixl "\<down>" 50)
where
  (*<*)Do[iff]:(*>*) "f s \<noteq> {} \<Longrightarrow> Do f \<down> s"

| (*<*)Semi[intro!]:(*>*) "\<lbrakk> c\<^sub>1 \<down> s\<^sub>0; \<forall>s\<^sub>1. s\<^sub>0 -c\<^sub>1\<rightarrow> s\<^sub>1 \<longrightarrow> c\<^sub>2 \<down> s\<^sub>1 \<rbrakk> \<Longrightarrow> (c\<^sub>1;c\<^sub>2) \<down> s\<^sub>0"

| (*<*)IfT[intro,simp]:(*>*) "\<lbrakk>  b s; c\<^sub>1 \<down> s \<rbrakk> \<Longrightarrow> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<down> s"
| (*<*)IfF[intro,simp]:(*>*) "\<lbrakk> \<not>b s; c\<^sub>2 \<down> s \<rbrakk> \<Longrightarrow> IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<down> s"

| (*<*)WhileFalse:(*>*) "\<not>b s \<Longrightarrow> WHILE b DO c \<down> s"
| (*<*)WhileTrue:(*>*) "\<lbrakk> b s; c \<down> s; \<forall>t. s -c\<rightarrow> t \<longrightarrow> WHILE b DO c \<down> t \<rbrakk> \<Longrightarrow> WHILE b DO c \<down> s"

| (*<*)Local:(*>*) "c \<down> f s \<Longrightarrow> LOCAL f;c;g \<down> s"


lemma [iff]: "Do f \<down> s = (f s \<noteq> {})"
apply(rule iffI)
 prefer 2
 apply(best intro:termi.intros)
apply(erule termi.cases)
apply blast+
done

lemma [iff]: "((c\<^sub>1;c\<^sub>2) \<down> s\<^sub>0) = (c\<^sub>1 \<down> s\<^sub>0 \<and> (\<forall>s\<^sub>1. s\<^sub>0 -c\<^sub>1\<rightarrow> s\<^sub>1 \<longrightarrow> c\<^sub>2 \<down> s\<^sub>1))"
apply(rule iffI)
 prefer 2
 apply(best intro:termi.intros)
apply(erule termi.cases)
apply blast+
done            

lemma [iff]: "(IF b THEN c\<^sub>1 ELSE c\<^sub>2 \<down> s) =
              ((if b s then c\<^sub>1 else c\<^sub>2) \<down> s)"
apply simp
apply(rule conjI)
apply(rule impI)
apply(rule iffI)
prefer 2
apply(blast intro:termi.intros)
apply(erule termi.cases)
apply blast+
apply(rule impI)
apply(rule iffI)
prefer 2
apply(blast intro:termi.intros)
apply(erule termi.cases)
apply blast+
done

lemma [iff]: "(LOCAL f;c;g \<down> s) = (c \<down> f s)"
by(fast elim: termi.cases intro:termi.intros)

lemma termi_while_lemma[rule_format]:
 "w\<down>fk \<Longrightarrow>
 (\<forall>k b c. fk = f k \<and> w = WHILE b DO c \<and> (\<forall>i. f i -c\<rightarrow> f(Suc i))
          \<longrightarrow> (\<exists>i. \<not>b(f i)))"
apply(erule termi.induct)
apply simp_all
apply blast
apply blast
done

lemma termi_while:
 "\<lbrakk> (WHILE b DO c) \<down> f k;  \<forall>i. f i -c\<rightarrow> f(Suc i) \<rbrakk> \<Longrightarrow> \<exists>i. \<not>b(f i)"
by(blast intro:termi_while_lemma)

lemma wf_termi: "wf {(t,s). WHILE b DO c \<down> s \<and> b s \<and> s -c\<rightarrow> t}"
apply(subst wf_iff_no_infinite_down_chain)
apply(rule notI)
apply clarsimp
apply(insert termi_while)
apply blast
done

end
