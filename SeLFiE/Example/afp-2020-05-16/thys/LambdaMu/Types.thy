subsection \<open>Types\<close>
  
theory Types
  imports Syntax
begin
  
text\<open>We implement typing environments as (total) functions from natural numbers to types,
     following the approach of Stefan Berghofer in his formalisation of the simply typed
     $\lambda$-calculus in the Isabelle/HOL library.
     An empty typing environment may be represented by an arbitrary function of the correct type
     as it will never be queried when a typing judgement is valid. We split typing environments,
     dedicating one environment to $\lambda$-variables and another to $\mu$-variables, and
     use $\Gamma$ and $\Delta$ to range over the former and latter, respectively.\<close>

text\<open>From src/HOL/Proofs/LambdaType.thy\<close>
  
definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91) where
  "e\<langle>i:a\<rangle> = (\<lambda>j. if j < i then e j else if j = i then a else e (j-1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  by (rule ext) (simp_all add: shift_def split: nat.split, force)
   
inductive typing_trm :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"  
     ("_ , _ \<turnstile>\<^sub>T _ : _" [50, 50, 50, 50] 50)
and typing_cmd :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type) \<Rightarrow> cmd \<Rightarrow> bool"
     ("_ , _ \<turnstile>\<^sub>C _" [50, 50, 50] 50)
where 
  var [intro!]: "\<lbrakk> \<Gamma> x = T \<rbrakk> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T `x : T" |
  app [intro!]: "\<lbrakk> \<Gamma>, \<Delta> \<turnstile>\<^sub>T t : (T1\<rightarrow>T2); \<Gamma>, \<Delta> \<turnstile>\<^sub>T s : T1 \<rbrakk>
                    \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T (t\<degree>s) : T2" |
  lambda [intro!]: "\<lbrakk> \<Gamma>\<langle>0:T1\<rangle>, \<Delta> \<turnstile>\<^sub>T t : T2 \<rbrakk>
                    \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T (\<lambda> T1 : t) : (T1\<rightarrow>T2)" |
  activate [intro!]: "\<lbrakk> \<Gamma>, \<Delta>\<langle>0:T\<rangle> \<turnstile>\<^sub>C c \<rbrakk> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T (\<mu> T : c) : T" |
  passivate [intro!]: "\<lbrakk> \<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T; \<Delta> x = T\<rbrakk> \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>C (<x> t)"

inductive_cases typing_elims [elim!]:
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T `x : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t\<degree>s : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T \<lambda> T1 : t : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T \<mu> T1 : t : T"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C <x> t"

inductive_cases type_arrow_elim:
  "\<Gamma> , \<Delta> \<turnstile>\<^sub>T t : T1 \<rightarrow> T2"

lemma uniqueness:
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T1 \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>T t : T2 \<Longrightarrow> T1 = T2"
  "\<Gamma>, \<Delta> \<turnstile>\<^sub>C c \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>\<^sub>C c"
  apply(induct arbitrary: T2 rule: typing_trm_typing_cmd.inducts)
  using typing_cmd.cases apply blast+
done

end
