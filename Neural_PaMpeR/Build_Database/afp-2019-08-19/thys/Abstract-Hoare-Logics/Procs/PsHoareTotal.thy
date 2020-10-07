(*  Title:       Inductive definition of Hoare logic for total correctness
    Author:      Tobias Nipkow, 2001/2006
    Maintainer:  Tobias Nipkow
*)

theory PsHoareTotal imports PsHoare PsTermi begin

subsection\<open>Hoare logic for total correctness\<close>

definition
 tvalid :: "'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_)}" 50) where
    "\<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> \<Turnstile> {P}c{Q} \<and> (\<forall>z s. P z s \<longrightarrow> c\<down>s)"

definition
 valids :: "'a cntxt \<Rightarrow> bool" ("|\<Turnstile>\<^sub>t _" 50) where
 "|\<Turnstile>\<^sub>t D \<longleftrightarrow> (\<forall>(P,c,Q) \<in> D. \<Turnstile>\<^sub>t {P}c{Q})"

definition
 ctvalid :: "'a cntxt \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool"
            ("(_ /\<Turnstile>\<^sub>t {(1_)}/ (_)/ {(1_))}" 50) where
 "C \<Turnstile>\<^sub>t {P}c{Q} \<longleftrightarrow> |\<Turnstile>\<^sub>t C \<longrightarrow>  \<Turnstile>\<^sub>t {P}c{Q}"

definition
 cvalids :: "'a cntxt \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("_ |\<Turnstile>\<^sub>t/ _" 50) where
  "C |\<Turnstile>\<^sub>t D \<longleftrightarrow> |\<Turnstile>\<^sub>t C \<longrightarrow> |\<Turnstile>\<^sub>t D"

inductive
  thoare :: "'a cntxt \<Rightarrow> 'a cntxt \<Rightarrow> bool" ("(_ |\<turnstile>\<^sub>t/ _)" 50)
  and thoare' :: "'a cntxt \<Rightarrow> 'a assn \<Rightarrow> com \<Rightarrow> 'a assn \<Rightarrow> bool"
    ("(_ \<turnstile>\<^sub>t/ ({(1_)}/ (_)/ {(1_)}))" [50,0,0,0] 50)
where
 "C \<turnstile>\<^sub>t {P}c{Q}  \<equiv>  C |\<turnstile>\<^sub>t {(P,c,Q)}"
| Do: "C \<turnstile>\<^sub>t {\<lambda>z s. (\<forall>t \<in> f s . P z t) \<and> f s \<noteq> {}} Do f {P}"
| Semi: "\<lbrakk> C \<turnstile>\<^sub>t {P}c1{Q}; C \<turnstile>\<^sub>t {Q}c2{R} \<rbrakk> \<Longrightarrow> C \<turnstile>\<^sub>t {P} c1;c2 {R}"
| If: "\<lbrakk> C \<turnstile>\<^sub>t {\<lambda>z s. P z s \<and> b s}c{Q}; C \<turnstile>\<^sub>t {\<lambda>z s. P z s \<and> ~b s}d{Q}  \<rbrakk> \<Longrightarrow>
      C \<turnstile>\<^sub>t {P} IF b THEN c ELSE d {Q}"
| While:(*>*)
  "\<lbrakk>wf r;  \<forall>s'. C \<turnstile>\<^sub>t {\<lambda>z s. P z s \<and> b s \<and> s' = s} c {\<lambda>z s. P z s \<and> (s,s') \<in> r}\<rbrakk>
   \<Longrightarrow> C \<turnstile>\<^sub>t {P} WHILE b DO c {\<lambda>z s. P z s \<and> \<not>b s}"

| Call:
  "\<lbrakk> wf r;
     \<forall>q pre.
       (\<Union>p. {(\<lambda>z s. P p z s \<and> ((p,s),(q,pre)) \<in> r,CALL p,Q p)})
       \<turnstile>\<^sub>t {\<lambda>z s. P q z s \<and> s = pre} body q {Q q} \<rbrakk>
   \<Longrightarrow> {} |\<turnstile>\<^sub>t \<Union>p. {(P p, CALL p, Q p)}"

| Asm: "(P,CALL p,Q) \<in> C \<Longrightarrow> C \<turnstile>\<^sub>t {P} CALL p {Q}"

| Conseq:
  "\<lbrakk> C \<turnstile>\<^sub>t {P'}c{Q'};
     (\<forall>s t. (\<forall>z. P' z s \<longrightarrow> Q' z t) \<longrightarrow> (\<forall>z. P z s \<longrightarrow> Q z t)) \<and>
     (\<forall>s. (\<exists>z. P z s) \<longrightarrow> (\<exists>z. P' z s)) \<rbrakk>
   \<Longrightarrow> C \<turnstile>\<^sub>t {P}c{Q}"

| ConjI: "\<forall>(P,c,Q) \<in> D. C \<turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  C |\<turnstile>\<^sub>t D"
| ConjE: "\<lbrakk> C |\<turnstile>\<^sub>t D; (P,c,Q) \<in> D \<rbrakk> \<Longrightarrow> C \<turnstile>\<^sub>t {P}c{Q}"

| Local: "\<lbrakk> \<forall>s'. C \<turnstile>\<^sub>t {\<lambda>z s. P z s' \<and> s = f s'} c {\<lambda>z t. Q z (g s' t)} \<rbrakk> \<Longrightarrow>
        C \<turnstile>\<^sub>t {P} LOCAL f;c;g {Q}"
monos split_beta

lemma strengthen_pre:
 "\<lbrakk> \<forall>z s. P' z s \<longrightarrow> P z s; C \<turnstile>\<^sub>t {P}c{Q}  \<rbrakk> \<Longrightarrow> C \<turnstile>\<^sub>t {P'}c{Q}"
by(rule thoare.Conseq, assumption, blast)

lemma weaken_post:
 "\<lbrakk> C \<turnstile>\<^sub>t {P}c{Q}; \<forall>z s. Q z s \<longrightarrow> Q' z s \<rbrakk> \<Longrightarrow> C \<turnstile>\<^sub>t {P}c{Q'}"
by(erule thoare.Conseq, blast)


lemmas tvalid_defs = tvalid_def ctvalid_def valids_def cvalids_def valid_defs

lemma [iff]:
"(\<Turnstile>\<^sub>t {\<lambda>z s. \<exists>n. P n z s}c{Q}) = (\<forall>n. \<Turnstile>\<^sub>t {P n}c{Q})"
apply(unfold tvalid_defs)
apply fast
done

lemma [iff]:
"(\<Turnstile>\<^sub>t {\<lambda>z s. P z s \<and> P'}c{Q}) = (P' \<longrightarrow> \<Turnstile>\<^sub>t {P}c{Q})"
apply(unfold tvalid_defs)
apply fast
done

lemma [iff]: "(\<Turnstile>\<^sub>t {P}CALL p{Q}) = (\<Turnstile>\<^sub>t {P}body p{Q})"
apply(unfold tvalid_defs)
apply fast
done

lemma unfold_while:
 "(s -WHILE b DO c\<rightarrow> u) =
  (s -IF b THEN c;WHILE b DO c ELSE Do(\<lambda>s. {s})\<rightarrow> u)"
by(auto elim: exec.cases intro:exec.intros split:if_split_asm)

theorem "C |\<turnstile>\<^sub>t D  \<Longrightarrow>  C |\<Turnstile>\<^sub>t D"
apply(erule thoare.induct)
       apply(simp only:tvalid_defs)
       apply fast
      apply(simp add:tvalid_defs)
      apply fast
     apply(simp only:tvalid_defs)
     apply clarsimp
    prefer 3
    apply(simp add:tvalid_defs)
    apply fast
   prefer 3
   apply(simp add:tvalid_defs)
   apply blast
  apply(simp add:tvalid_defs)
  apply(rule impI, rule conjI)
   apply(rule allI)
   apply(erule wf_induct)
   apply clarify
   apply(drule unfold_while[THEN iffD1])
   apply (simp split: if_split_asm)
   apply fast
  apply(rule allI, rule allI)
  apply(erule wf_induct)
  apply clarify
  apply(case_tac "b x")
   prefer 2
   apply (erule termi.WhileFalse)
  apply(rule termi.WhileTrue, assumption)
   apply fast
  apply (subgoal_tac "(t,x):r")
   apply fast
  apply blast

 defer

apply(simp add:tvalid_defs)
apply fast

apply(simp (no_asm_use) add:tvalid_defs)
apply fast

apply(simp add:tvalid_defs)
apply fast

apply(simp (no_asm_use) add:valids_def ctvalid_def cvalids_def)
apply(rule allI)
apply(rename_tac q)
apply(subgoal_tac "\<forall>pre. \<Turnstile>\<^sub>t {\<lambda>z s. P (fst(q,pre)) z s & s=(snd(q,pre))} body (fst(q,pre)) {Q (fst(q,pre))}")
 apply(simp (no_asm_use) add:tvalid_defs)
 apply fast
apply(rule allI)
apply(erule_tac wf_induct)
apply(simp add:split_paired_all)
apply(rename_tac q pre)
apply(erule allE, erule allE, erule conjE, erule impE)
 prefer 2
 apply assumption
apply(rotate_tac 1, erule thin_rl)
apply(unfold tvalid_defs)
apply fast
done

definition MGT\<^sub>t :: "com \<Rightarrow> state assn \<times> com \<times> state assn" where
  [simp]: "MGT\<^sub>t c = (\<lambda>z s. z = s \<and> c\<down>s, c, \<lambda>z t. z -c\<rightarrow> t)"

lemma MGT_implies_complete:
 "{} |\<turnstile>\<^sub>t {MGT\<^sub>t c} \<Longrightarrow> {} \<Turnstile>\<^sub>t {P}c{Q} \<Longrightarrow> {} \<turnstile>\<^sub>t {P}c{Q::state assn}"
apply(unfold MGT\<^sub>t_def)
apply (erule thoare.Conseq)
apply(simp add: tvalid_defs)
apply blast
done

lemma while_termiE: "\<lbrakk> WHILE b DO c \<down> s; b s \<rbrakk> \<Longrightarrow> c \<down> s"
by(erule termi.cases, auto)

lemma while_termiE2: "\<lbrakk> WHILE b DO c \<down> s; b s; s -c\<rightarrow> t \<rbrakk> \<Longrightarrow> WHILE b DO c \<down> t"
by(erule termi.cases, auto)

lemma MGT_lemma: "\<forall>p. {} |\<turnstile>\<^sub>t {MGT\<^sub>t(CALL p)}  \<Longrightarrow>  {} |\<turnstile>\<^sub>t {MGT\<^sub>t c}"
apply (simp)
apply(induct_tac c)
     apply (rule strengthen_pre[OF _ thoare.Do])
     apply blast
    apply(rename_tac com1 com2)
    apply(rule_tac Q = "\<lambda>z s. z -com1\<rightarrow>s & com2\<down>s" in thoare.Semi)
     apply(erule thoare.Conseq)
     apply fast
    apply(erule thoare.Conseq)
    apply fast
   apply(rule thoare.If)
    apply(erule thoare.Conseq)
    apply simp
   apply(erule thoare.Conseq)
   apply simp
  defer
  apply simp
 apply(fast intro:thoare.Local elim!: thoare.Conseq)
apply(rename_tac b c)
apply(rule_tac P' = "\<lambda>z s. (z,s) \<in> ({(s,t). b s \<and> s -c\<rightarrow> t})^* \<and>
                           WHILE b DO c \<down> s" in thoare.Conseq)
 apply(rule_tac thoare.While[OF wf_termi])
 apply(rule allI)
 apply(erule thoare.Conseq)
 apply(fastforce intro:rtrancl_into_rtrancl dest:while_termiE while_termiE2)
apply(rule conjI)
 apply clarsimp
 apply(erule_tac x = s in allE)
 apply clarsimp
 apply(erule converse_rtrancl_induct)
  apply(erule exec.WhileFalse)
 apply(fast elim:exec.WhileTrue)
apply(fast intro: rtrancl_refl)
done


inductive_set
  exec1 :: "((com list \<times> state) \<times> (com list \<times> state))set"
  and exec1' :: "(com list \<times> state) \<Rightarrow> (com list \<times> state) \<Rightarrow> bool"  ("_ \<rightarrow> _" [81,81] 100)
where
  "cs0 \<rightarrow> cs1 \<equiv> (cs0,cs1) : exec1"

| Do[iff]: "t \<in> f s \<Longrightarrow> ((Do f)#cs,s) \<rightarrow> (cs,t)"

| Semi[iff]: "((c1;c2)#cs,s) \<rightarrow> (c1#c2#cs,s)"

| IfTrue:   "b s \<Longrightarrow> ((IF b THEN c1 ELSE c2)#cs,s) \<rightarrow> (c1#cs,s)"
| IfFalse: "\<not>b s \<Longrightarrow> ((IF b THEN c1 ELSE c2)#cs,s) \<rightarrow> (c2#cs,s)"

| WhileFalse: "\<not>b s \<Longrightarrow> ((WHILE b DO c)#cs,s) \<rightarrow> (cs,s)"
| WhileTrue:   "b s \<Longrightarrow> ((WHILE b DO c)#cs,s) \<rightarrow> (c#(WHILE b DO c)#cs,s)"

| Call[iff]: "(CALL p#cs,s) \<rightarrow> (body p#cs,s)"

| Local[iff]: "((LOCAL f;c;g)#cs,s) \<rightarrow> (c # Do(\<lambda>t. {g s t})#cs, f s)"

abbreviation
  exectr :: "(com list \<times> state) \<Rightarrow> (com list \<times> state) \<Rightarrow> bool"  ("_ \<rightarrow>\<^sup>* _" [81,81] 100)
  where "cs0 \<rightarrow>\<^sup>* cs1 \<equiv> (cs0,cs1) : exec1^*"

inductive_cases exec1E[elim!]:
 "([],s) \<rightarrow> (cs',s')"
 "(Do f#cs,s) \<rightarrow> (cs',s')"
 "((c1;c2)#cs,s) \<rightarrow> (cs',s')"
 "((IF b THEN c1 ELSE c2)#cs,s) \<rightarrow> (cs',s')"
 "((WHILE b DO c)#cs,s) \<rightarrow> (cs',s')"
 "(CALL p#cs,s) \<rightarrow> (cs',s')"
 "((LOCAL f;c;g)#cs,s) \<rightarrow> (cs',s')"

lemma [iff]: "\<not> ([],s) \<rightarrow> u"
by (induct u) blast

lemma app_exec: "(cs,s) \<rightarrow> (cs',s') \<Longrightarrow> (cs@cs2,s) \<rightarrow> (cs'@cs2,s')"
apply(erule exec1.induct)
       apply(simp_all del:fun_upd_apply)
   apply(blast intro:exec1.intros)+
done

lemma app_execs: "(cs,s) \<rightarrow>\<^sup>* (cs',s') \<Longrightarrow> (cs@cs2,s) \<rightarrow>\<^sup>* (cs'@cs2,s')"
apply(erule rtrancl_induct2)
 apply blast
apply(blast intro:app_exec rtrancl_trans)
done

lemma exec_impl_execs[rule_format]:
 "s -c\<rightarrow> s' \<Longrightarrow> \<forall>cs. (c#cs,s) \<rightarrow>\<^sup>* (cs,s')"
apply(erule exec.induct)
         apply blast
        apply(blast intro:rtrancl_trans)
       apply(blast intro:exec1.IfTrue rtrancl_trans)
      apply(blast intro:exec1.IfFalse rtrancl_trans)
     apply(blast intro:exec1.WhileFalse rtrancl_trans)
    apply(blast intro:exec1.WhileTrue rtrancl_trans)
   apply(blast intro: rtrancl_trans)
apply(blast intro: rtrancl_trans)
done

inductive
  execs :: "state \<Rightarrow> com list \<Rightarrow> state \<Rightarrow> bool"  ("_/ =_\<Rightarrow>/ _" [50,0,50] 50)
where
  "s =[]\<Rightarrow> s"
| "s -c\<rightarrow> t \<Longrightarrow> t =cs\<Rightarrow> u \<Longrightarrow> s =c#cs\<Rightarrow> u"

inductive_cases [elim!]:
 "s =[]\<Rightarrow> t"
 "s =c#cs\<Rightarrow> t"

theorem exec1s_impl_execs: "(cs,s) \<rightarrow>\<^sup>* ([],t) \<Longrightarrow> s =cs\<Rightarrow> t"
apply(erule converse_rtrancl_induct2)
 apply(rule execs.intros)
apply(erule exec1.cases)
apply(blast intro:execs.intros)
apply(blast intro:execs.intros)
apply(fastforce intro:execs.intros)
apply(fastforce intro:execs.intros)
apply(blast intro:execs.intros exec.intros)+
done



theorem exec1s_impl_exec: "([c],s) \<rightarrow>\<^sup>* ([],t) \<Longrightarrow> s -c\<rightarrow> t"
by(blast dest: exec1s_impl_execs)

primrec termis :: "com list \<Rightarrow> state \<Rightarrow> bool" (infixl "\<Down>" 60) where
  "[]\<Down>s = True"
| "c#cs \<Down> s = (c\<down>s \<and> (\<forall>t. s -c\<rightarrow> t \<longrightarrow> cs\<Down>t))"

lemma exec1_pres_termis: "(cs,s) \<rightarrow> (cs',s') \<Longrightarrow> cs\<Down>s \<longrightarrow> cs'\<Down>s'"
apply(erule exec1.induct)
       apply(simp_all del:fun_upd_apply)
   apply blast
  apply(blast intro:exec.WhileFalse)
 apply(blast intro:while_termiE while_termiE2 exec.WhileTrue)
apply blast
done

lemma execs_pres_termis: "(cs,s) \<rightarrow>\<^sup>* (cs',s') \<Longrightarrow> cs\<Down>s \<longrightarrow> cs'\<Down>s'"
apply(erule rtrancl_induct2)
 apply blast
apply(blast dest:exec1_pres_termis)
done

lemma execs_pres_termi: "\<lbrakk> ([c],s) \<rightarrow>\<^sup>* (c'#cs',s'); c\<down>s \<rbrakk> \<Longrightarrow> c'\<down>s'"
apply(insert execs_pres_termis[of "[c]" _ "c'#cs'",simplified])
apply blast
done

definition  termi_call_steps :: "((pname \<times> state) \<times> (pname \<times> state))set" where
  "termi_call_steps =
    {((q,t),(p,s)). body p\<down>s \<and> (\<exists>cs. ([body p], s) \<rightarrow>\<^sup>* (CALL q# cs, t))}"

lemma lem:
  "\<forall>y. (a,y)\<in>r\<^sup>+ \<longrightarrow> P a \<longrightarrow> P y \<Longrightarrow> ((b,a) \<in> {(y,x). P x \<and> (x,y)\<in>r}\<^sup>+) = ((b,a) \<in> {(y,x). P x \<and> (x,y)\<in>r\<^sup>+})"
apply(rule iffI)
 apply clarify
 apply(erule trancl_induct)
  apply blast
 apply(blast intro:trancl_trans)
apply clarify
apply(erule trancl_induct)
 apply blast
apply(blast intro:trancl_trans)
done


lemma renumber_aux:
 "\<lbrakk>\<forall>i. (a,f i) \<in> r^* \<and> (f i,f(Suc i)) : r; (a,b) : r^* \<rbrakk> \<Longrightarrow> b = f 0 \<longrightarrow> (\<exists>f. f 0 = a & (\<forall>i. (f i, f(Suc i)) : r))"
apply(erule converse_rtrancl_induct)
 apply blast
apply(clarsimp)
apply(rule_tac x="\<lambda>i. case i of 0 \<Rightarrow> y | Suc i \<Rightarrow> fa i" in exI)
apply simp
apply clarify
apply(case_tac i)
 apply simp_all
done

lemma renumber:
 "\<forall>i. (a,f i) : r^* \<and> (f i,f(Suc i)) : r \<Longrightarrow> \<exists>f. f 0 = a & (\<forall>i. (f i, f(Suc i)) : r)"
by(blast dest:renumber_aux)


definition inf :: "com list \<Rightarrow> state \<Rightarrow> bool" where
  "inf cs s \<longleftrightarrow> (\<exists>f. f 0 = (cs,s) \<and> (\<forall>i. f i \<rightarrow> f(Suc i)))"

lemma [iff]: "\<not> inf [] s"
apply(unfold inf_def)
apply clarify
apply(erule_tac x = 0 in allE)
apply simp
done

lemma [iff]: "\<not> inf [Do f] s"
apply(unfold inf_def)
apply clarify
apply(frule_tac x = 0 in spec)
apply(erule_tac x = 1 in allE)
apply (case_tac "fa (Suc 0)")
apply clarsimp
done

lemma [iff]: "inf ((c1;c2)#cs) s = inf (c1#c2#cs) s"
apply(unfold inf_def)
apply(rule iffI)
apply clarify
apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
apply(frule_tac x = 0 in spec)
apply (case_tac "f (Suc 0)")
apply clarsimp
apply clarify
apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> ((c1;c2)#cs,s) | Suc i \<Rightarrow> f i" in exI)
apply(simp split:nat.split)
done

lemma [iff]: "inf ((IF b THEN c1 ELSE c2)#cs) s =
              inf ((if b s then c1 else c2)#cs) s"
apply(unfold inf_def)
apply(rule iffI)
 apply clarsimp
 apply(frule_tac x = 0 in spec)
 apply (case_tac "f (Suc 0)")
 apply(rule conjI)
  apply clarsimp
  apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
  apply clarsimp
 apply clarsimp
 apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
 apply clarsimp
apply clarsimp
apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> ((IF b THEN c1 ELSE c2)#cs,s) | Suc i \<Rightarrow> f i" in exI)
apply(simp add: exec1.intros split:nat.split)
done

lemma [simp]:
 "inf ((WHILE b DO c)#cs) s =
  (if b s then inf (c#(WHILE b DO c)#cs) s else inf cs s)"
apply(unfold inf_def)
apply(rule iffI)
 apply clarsimp
 apply(frule_tac x = 0 in spec)
 apply (case_tac "f (Suc 0)")
 apply(rule conjI)
  apply clarsimp
  apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
  apply clarsimp
 apply clarsimp
 apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
 apply clarsimp
apply (clarsimp split:if_splits)
 apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> ((WHILE b DO c)#cs,s) | Suc i \<Rightarrow> f i" in exI)
 apply(simp add: exec1.intros split:nat.split)
apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> ((WHILE b DO c)#cs,s) | Suc i \<Rightarrow> f i" in exI)
apply(simp add: exec1.intros split:nat.split)
done

lemma [iff]: "inf (CALL p#cs) s =  inf (body p#cs) s"
apply(unfold inf_def)
apply(rule iffI)
 apply clarsimp
 apply(frule_tac x = 0 in spec)
 apply (case_tac "f (Suc 0)")
 apply clarsimp
 apply(rule_tac x = "\<lambda>i. f(Suc i)" in exI)
 apply clarsimp
apply clarsimp
apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> (CALL p#cs,s) | Suc i \<Rightarrow> f i" in exI)
apply(simp add: exec1.intros split:nat.split)
done

lemma [iff]: "inf ((LOCAL f;c;g)#cs) s =
              inf (c#Do(\<lambda>t. {g s t})#cs) (f s)"
apply(unfold inf_def)
apply(rule iffI)
 apply clarsimp
 apply(rename_tac F)
 apply(frule_tac x = 0 in spec)
 apply (case_tac "F (Suc 0)")
 apply clarsimp
 apply(rule_tac x = "\<lambda>i. F(Suc i)" in exI)
 apply clarsimp
apply (clarsimp)
apply(rename_tac F)
apply(rule_tac x = "\<lambda>i. case i of 0 \<Rightarrow> ((LOCAL f;c;g)#cs,s) | Suc i \<Rightarrow> F i" in exI)
apply(simp add: exec1.intros split:nat.split)
done

lemma exec1_only1_aux: "(ccs,s) \<rightarrow> (cs',t) \<Longrightarrow>
                    \<forall>c cs. ccs = c#cs \<longrightarrow> (\<exists>cs1. cs' = cs1 @ cs)"
apply(erule exec1.induct)
apply force+
done

lemma exec1_only1: "(c#cs,s) \<rightarrow> (cs',t) \<Longrightarrow> \<exists>cs1. cs' = cs1 @ cs"
by(blast dest:exec1_only1_aux)

lemma exec1_drop_suffix_aux:
"(cs12,s) \<rightarrow> (cs1'2,s') \<Longrightarrow> \<forall>cs1 cs2 cs1'.
 cs12 = cs1@cs2 & cs1'2 = cs1'@cs2 & cs1 \<noteq> [] \<longrightarrow> (cs1,s) \<rightarrow> (cs1',s')"
apply(erule exec1.induct)
       apply (force intro:exec1.intros simp add: neq_Nil_conv)+
done

lemma exec1_drop_suffix:
 "(cs1@cs2,s) \<rightarrow> (cs1'@cs2,s') \<Longrightarrow> cs1 \<noteq> [] \<Longrightarrow> (cs1,s) \<rightarrow> (cs1',s')"
by(blast dest:exec1_drop_suffix_aux)

lemma execs_drop_suffix[rule_format(no_asm)]:
  "\<lbrakk> f 0 = (c#cs,s);\<forall>i. f(i) \<rightarrow> f(Suc i) \<rbrakk> \<Longrightarrow>
   (\<forall>i<k. p i \<noteq> [] & fst(f i) = p i@cs) \<longrightarrow> fst(f k) = p k@cs
   \<longrightarrow> ([c],s) \<rightarrow>\<^sup>* (p k,snd(f k))"
apply(induct_tac k)
 apply simp
apply (clarsimp)
apply(erule rtrancl_into_rtrancl)
apply(erule_tac x = n in allE)
apply(erule_tac x = n in allE)
apply(case_tac "f n")
apply(case_tac "f(Suc n)")
apply simp
apply(blast dest:exec1_drop_suffix)
done

lemma execs_drop_suffix0:
  "\<lbrakk> f 0 = (c#cs,s);\<forall>i. f(i) \<rightarrow> f(Suc i); \<forall>i<k. p i \<noteq> [] & fst(f i) = p i@cs;
     fst(f k) = cs; p k = [] \<rbrakk> \<Longrightarrow> ([c],s) \<rightarrow>\<^sup>* ([],snd(f k))"
apply(drule execs_drop_suffix,assumption,assumption)
 apply simp
apply simp
done

lemma skolemize1: "\<forall>x. P x \<longrightarrow> (\<exists>y. Q x y) \<Longrightarrow> \<exists>f.\<forall>x. P x \<longrightarrow> Q x (f x)"
apply(rule_tac x = "\<lambda>x. SOME y. Q x y" in exI)
apply(fast intro:someI2)
done

lemma least_aux: "\<lbrakk>f 0 = (c # cs, s); \<forall>i. f i \<rightarrow> f (Suc i);
        fst(f k) = cs; \<forall>i<k. fst(f i) \<noteq> cs\<rbrakk>
       \<Longrightarrow> \<forall>i \<le> k. (\<exists>p. (p \<noteq> []) = (i < k) & fst(f i) = p @ cs)"
apply(rule allI)
apply(induct_tac i)
 apply simp
 apply (rule ccontr)
 apply simp
apply clarsimp
apply(drule order_le_imp_less_or_eq)
apply(erule disjE)
 prefer 2
 apply simp
apply simp
apply(erule_tac x = n in allE)
apply(erule_tac x = "Suc n" in allE)
apply(case_tac "f n")
apply(case_tac "f(Suc n)")
apply simp
apply(rename_tac sn csn1 sn1)
apply (clarsimp simp add: neq_Nil_conv)
apply(drule exec1_only1)
apply (clarsimp simp add: neq_Nil_conv)
apply(erule disjE)
 apply clarsimp
apply clarsimp
apply(case_tac cs1)
 apply simp
apply simp
done

lemma least_lem: "\<lbrakk>f 0 = (c#cs,s); \<forall>i. f i \<rightarrow> f(Suc i); \<exists>i. fst(f i) = cs \<rbrakk>
       \<Longrightarrow> \<exists>k. fst(f k) = cs & ([c],s) \<rightarrow>\<^sup>* ([],snd(f k))"
apply(rule_tac x="LEAST i. fst(f i) = cs" in exI)
apply(rule conjI)
 apply(fast intro: LeastI)
apply(subgoal_tac
 "\<forall>i\<le>LEAST i. fst (f i) = cs. \<exists>p. ((p \<noteq> []) = (i<(LEAST i. fst (f i) = cs))) & fst(f i) = p@cs")
 apply(drule skolemize1)
 apply clarify
 apply(rename_tac p)
 apply(erule_tac p=p in execs_drop_suffix0, assumption)
   apply (blast dest:order_less_imp_le)
  apply(fast intro: LeastI)
 apply(erule thin_rl)
 apply(erule_tac x = "LEAST j. fst (f j) = fst (f i)" in allE)
 apply blast
apply(erule least_aux,assumption)
 apply(fast intro: LeastI)
apply clarify
apply(drule not_less_Least)
apply blast
done

lemma skolemize2: "\<forall>x.\<exists>y. P x y \<Longrightarrow> \<exists>f.\<forall>x. P x (f x)"
apply(rule_tac x = "\<lambda>x. SOME y. P x y" in exI)
apply(fast intro:someI2)
done

lemma inf_cases: "inf (c#cs) s \<Longrightarrow> inf [c] s \<or> (\<exists>t. s -c\<rightarrow> t \<and> inf cs t)"
apply(unfold inf_def)
apply (clarsimp del: disjCI)
apply(case_tac "\<exists>i. fst(f i) = cs")
 apply(rule disjI2)
 apply(drule least_lem, assumption, assumption)
 apply clarify
 apply(drule exec1s_impl_exec)
 apply(case_tac "f k")
 apply simp
 apply (rule exI, rule conjI, assumption)
 apply(rule_tac x="\<lambda>i. f(i+k)" in exI)
 apply (clarsimp)
apply(rule disjI1)
apply simp
apply(subgoal_tac "\<forall>i. \<exists>p. p \<noteq> [] \<and> fst(f i) = p@cs")
 apply(drule skolemize2)
 apply clarify
 apply(rename_tac p)
 apply(rule_tac x = "\<lambda>i. (p i, snd(f i))" in exI)
 apply(rule conjI)
  apply(erule_tac x = 0 in allE, erule conjE)
  apply simp
 apply clarify
 apply(erule_tac x = i in allE)
 apply(erule_tac x = i in allE)
 apply(frule_tac x = i in spec)
 apply(erule_tac x = "Suc i" in allE)
 apply(case_tac "f i")
 apply(case_tac "f(Suc i)")
 apply clarsimp
 apply(blast intro:exec1_drop_suffix)
apply(clarify)
apply(induct_tac i)
 apply force
apply clarsimp
apply(case_tac p)
 apply blast
apply(erule_tac x=n in allE)
apply(erule_tac x="Suc n" in allE)
apply(case_tac "f n")
apply(case_tac "f(Suc n)")
apply clarsimp
apply(drule exec1_only1)
apply clarsimp
done

lemma termi_impl_not_inf: "c \<down> s \<Longrightarrow> \<not> inf [c] s"
apply(erule termi.induct)
        (*Do*)
        apply clarify
       (*Semi*)
       apply(blast dest:inf_cases)
      (* Cond *)
      apply clarsimp
     apply clarsimp
    (*While*)
    apply clarsimp
   apply(fastforce dest:inf_cases)
  (*Call*)
  apply blast
 (*Local*)
 apply(blast dest:inf_cases)
done

lemma termi_impl_no_inf_chain:
 "c\<down>s \<Longrightarrow> \<not>(\<exists>f. f 0 = ([c],s) \<and> (\<forall>i::nat. (f i, f(i+1)) : exec1^+))"
apply(subgoal_tac "wf({(y,x). ([c],s) \<rightarrow>\<^sup>* x & x \<rightarrow> y}^+)")
 apply(simp only:wf_iff_no_infinite_down_chain)
 apply(erule contrapos_nn)
 apply clarify
 apply(subgoal_tac "\<forall>i. ([c], s) \<rightarrow>\<^sup>* f i")
  prefer 2
  apply(rule allI)
  apply(induct_tac i)
   apply simp
  apply simp
  apply(blast intro: trancl_into_rtrancl rtrancl_trans)
 apply(rule_tac x=f in exI)
 apply clarify
 apply(drule_tac x=i in spec)
 apply(subst lem)
  apply(blast intro: trancl_into_rtrancl rtrancl_trans)
 apply clarsimp
apply(rule wf_trancl)
apply(simp only:wf_iff_no_infinite_down_chain)
apply(clarify)
apply simp
apply(drule renumber)
apply(fold inf_def)
apply(simp add: termi_impl_not_inf)
done

primrec cseq :: "(nat \<Rightarrow> pname \<times> state) \<Rightarrow> nat \<Rightarrow> com list" where
  "cseq S 0 = []"
|  "cseq S (Suc i) = (SOME cs. ([body(fst(S i))], snd(S i)) \<rightarrow>\<^sup>*
                              (CALL(fst(S(i+1)))# cs, snd(S(i+1)))) @ cseq S i"

lemma wf_termi_call_steps: "wf termi_call_steps"
apply(unfold termi_call_steps_def)
apply(simp only:wf_iff_no_infinite_down_chain)
apply(clarify)
apply(rename_tac S)
apply simp
apply(subgoal_tac
 "\<exists>Cs. Cs 0 = [] & (\<forall>i. (body(fst(S i)) # Cs i,snd(S i)) \<rightarrow>\<^sup>*
                        (CALL(fst(S(i+1)))# Cs(i+1), snd(S(i+1))))")
prefer 2
 apply(rule_tac x = "cseq S" in exI)
 apply clarsimp
 apply(erule_tac x=i in allE)
 apply clarsimp
 apply(rename_tac q t p s cs)
 apply(erule_tac P = "\<lambda>cs.([body p],s) \<rightarrow>\<^sup>* (CALL q# cs, t)" in someI2)
 apply(fastforce dest:app_execs)
apply clarify
apply(subgoal_tac
 "\<forall>i. ((body(fst(S i))# Cs i,snd(S i)), (body(fst(S(i+1)))# Cs(i+1), snd(S(i+1)))) : exec1^+")
 prefer 2
 apply(blast intro:rtrancl_into_trancl1)
apply(subgoal_tac "\<exists>f. f 0 = ([body(fst(S 0))],snd(S 0)) \<and> (\<forall>i. (f i, f(i+1)) : exec1^+)")
 prefer 2
 apply(rule_tac x = "\<lambda>i.(body(fst(S i))#Cs i,snd(S i))" in exI)
 apply blast
apply(erule_tac x=0 in allE)
apply(simp add:split_def)
apply clarify
apply(drule termi_impl_no_inf_chain)
apply simp
apply blast
done

lemma CALL_lemma:
"(\<Union>p. {(\<lambda>z s. (z=s \<and> body p\<down>s) \<and> ((p,s),(q,pre)) \<in> termi_call_steps, CALL p,
        \<lambda>z s. z -body p\<rightarrow> s)}) \<turnstile>\<^sub>t
 {\<lambda>z s. (z=s \<and> body q\<down>pre) \<and> (\<exists>cs. ([body q],pre) \<rightarrow>\<^sup>* (c#cs,s))} c
 {\<lambda>z s. z -c\<rightarrow> s}"
apply(induct_tac c)
(*Do*)
     apply (rule strengthen_pre[OF _ thoare.Do])
     apply(blast dest: execs_pres_termi)
(*Semi*)
    apply(rename_tac c1 c2)
    apply(rule_tac Q = "\<lambda>z s. body q\<down>pre & (\<exists>cs. ([body q], pre) \<rightarrow>\<^sup>* (c2#cs,s)) & z -c1\<rightarrow>s & c2\<down>s" in thoare.Semi)
     apply(erule thoare.Conseq)
     apply(rule conjI)
      apply clarsimp
      apply(subgoal_tac "s -c1\<rightarrow> t")
       prefer 2
       apply(blast intro: exec1.Semi exec_impl_execs rtrancl_trans)
      apply(subgoal_tac "([body q], pre) \<rightarrow>\<^sup>* (c2 # cs, t)")
       prefer 2
       apply(blast intro:exec1.Semi[THEN r_into_rtrancl] exec_impl_execs rtrancl_trans)
      apply(subgoal_tac "([body q], pre) \<rightarrow>\<^sup>* (c2 # cs, t)")
       prefer 2
       apply(blast intro: exec_impl_execs rtrancl_trans)
      apply(blast intro:exec_impl_execs rtrancl_trans execs_pres_termi)
     apply(fast intro: exec1.Semi rtrancl_trans)
    apply(erule thoare.Conseq)
    apply blast
(*Call*)
   prefer 3
   apply(simp only:termi_call_steps_def)
   apply(rule thoare.Conseq[OF thoare.Asm])
    apply blast
   apply(blast dest: execs_pres_termi)
(*If*)
  apply(rule thoare.If)
   apply(erule thoare.Conseq)
   apply simp
   apply(blast intro: exec1.IfTrue rtrancl_trans)
  apply(erule thoare.Conseq)
  apply simp
  apply(blast intro: exec1.IfFalse rtrancl_trans)
(*Local*)
 defer
 apply simp
 apply(rule thoare.Local)
 apply(rule allI)
 apply(erule thoare.Conseq)
 apply (clarsimp)
 apply(rule conjI)
  apply (clarsimp)
  apply(drule rtrancl_trans[OF _ r_into_rtrancl[OF exec1.Local]])
  apply(fast)
 apply (clarsimp)
 apply(drule rtrancl_trans[OF _ r_into_rtrancl[OF exec1.Local]])
 apply blast
(*While*)
apply(rename_tac b c)
apply(rule_tac P' = "\<lambda>z s. (z,s) \<in> ({(s,t). b s \<and> s -c\<rightarrow> t})^* \<and> body q\<down>pre \<and>
           (\<exists>cs. ([body q], pre) \<rightarrow>\<^sup>* ((WHILE b DO c) # cs, s))" in thoare.Conseq)
 apply(rule_tac thoare.While[OF wf_termi])
 apply(rule allI)
 apply(erule thoare.Conseq)
 apply clarsimp
 apply(rule conjI)
  apply clarsimp
  apply(rule conjI)
   apply(blast intro: rtrancl_trans exec1.WhileTrue)
  apply(rule conjI)
   apply(rule exI, rule rtrancl_trans, assumption)
   apply(blast intro: exec1.WhileTrue exec_impl_execs rtrancl_trans)
  apply(rule conjI)
   apply(blast intro:execs_pres_termi)
  apply(blast intro: exec1.WhileTrue exec_impl_execs rtrancl_trans)
 apply(blast intro: exec1.WhileTrue exec_impl_execs rtrancl_trans)
apply(rule conjI)
 apply clarsimp
 apply(erule_tac x = s in allE)
 apply clarsimp
 apply(erule impE)
  apply blast
 apply clarify
 apply(erule_tac a=s in converse_rtrancl_induct)
  apply(erule exec.WhileFalse)
 apply(fast elim:exec.WhileTrue)
apply(fast intro: rtrancl_refl)
done

lemma CALL_cor:
"(\<Union>p. {(\<lambda>z s. (z=s \<and> body p\<down>s) \<and> ((p,s),(q,pre)) \<in> termi_call_steps, CALL p,
        \<lambda>z s. z -body p\<rightarrow> s)}) \<turnstile>\<^sub>t
 {\<lambda>z s. (z=s \<and> body q\<down>s) \<and> s = pre} body q {\<lambda>z s. z -body q\<rightarrow> s}"
apply(rule strengthen_pre[OF _ CALL_lemma])
apply blast
done

lemma MGT_CALL: "{} |\<turnstile>\<^sub>t (\<Union>p. {MGT\<^sub>t(CALL p)})"
apply(simp add: MGT\<^sub>t_def)
apply(rule thoare.Call)
apply(rule wf_termi_call_steps)
apply clarify
apply(rule CALL_cor)
done

lemma MGT_CALL1: "\<forall>p. {} |\<turnstile>\<^sub>t {MGT\<^sub>t(CALL p)}"
by(fastforce intro:MGT_CALL[THEN ConjE])

theorem "{} \<Turnstile>\<^sub>t {P}c{Q}  \<Longrightarrow>  {} \<turnstile>\<^sub>t {P}c{Q::state assn}"
apply(erule MGT_implies_complete[OF MGT_lemma[OF MGT_CALL1]])
done

end
