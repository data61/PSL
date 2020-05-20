(*  Title:      Inductive definition of termination
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)
theory PTermi imports PLang begin

subsection\<open>Termination\<close>

inductive
  termi :: "com \<Rightarrow> state \<Rightarrow> bool" (infixl "\<down>" 50)
where
  Do[iff]: "f s \<noteq> {} \<Longrightarrow> Do f \<down> s"
| Semi[intro!]:   "\<lbrakk> c1 \<down> s0; \<And>s1. s0 -c1\<rightarrow> s1 \<Longrightarrow> c2 \<down> s1 \<rbrakk>
            \<Longrightarrow> (c1;c2) \<down> s0"

| IfTrue[intro,simp]: "\<lbrakk> b s; c1 \<down> s \<rbrakk> \<Longrightarrow> IF b THEN c1 ELSE c2 \<down> s"
| IfFalse[intro,simp]: "\<lbrakk> \<not>b s; c2 \<down> s \<rbrakk> \<Longrightarrow> IF b THEN c1 ELSE c2 \<down> s"

| WhileFalse: "\<not>b s \<Longrightarrow> WHILE b DO c \<down> s"

| WhileTrue:  "\<lbrakk> b s; c \<down> s; \<And>t. s -c\<rightarrow> t \<Longrightarrow> WHILE b DO c \<down> t \<rbrakk>
                \<Longrightarrow> WHILE b DO c \<down> s"
| "body \<down> s \<Longrightarrow> CALL \<down> s"

| Local: "c \<down> f s \<Longrightarrow> LOCAL f;c;g \<down> s"

lemma [iff]: "(Do f \<down> s) = (f s \<noteq> {})"
apply(rule iffI)
 prefer 2
 apply(best intro:termi.intros)
apply(erule termi.cases)
apply blast+
done

lemma [iff]: "((c1;c2) \<down> s0) = (c1 \<down> s0 \<and> (\<forall>s1. s0 -c1\<rightarrow> s1 \<longrightarrow> c2 \<down> s1))"
apply(rule iffI)
 prefer 2
 apply(best intro:termi.intros)
apply(erule termi.cases)
apply blast+
done

lemma [iff]: "(IF b THEN c1 ELSE c2 \<down> s) =
              ((if b s then c1 else c2) \<down> s)"
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

lemma [iff]: "(CALL \<down> s) = (body \<down> s)"
by(fast elim: termi.cases intro:termi.intros)

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
