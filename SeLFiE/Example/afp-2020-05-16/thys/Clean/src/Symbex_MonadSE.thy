(******************************************************************************
 * Clean
 *
 * Copyright (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

theory Symbex_MonadSE
  imports Seq_MonadSE
begin
  


subsection\<open>Definition and Properties of Valid Execution Sequences\<close>

text\<open>A key-notion in our framework is the \emph{valid} execution
sequence, \ie{} a sequence that:
\begin{enumerate}
\item terminates (not obvious since while),
\item results in a final @{term True},
\item does not fail globally (but recall the FailSave and FailPurge
      variants of @{term mbind}-operators, that handle local exceptions in
      one or another way).
\end{enumerate}
Seen from an automata perspective (where the monad - operations correspond to
the step function), valid execution sequences can be used to model ``feasible paths''
across an automaton.\<close>

definition valid_SE :: "'\<sigma> \<Rightarrow> (bool,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> bool" (infix "\<Turnstile>" 15)
where "(\<sigma> \<Turnstile> m) = (m \<sigma> \<noteq> None \<and> fst(the (m \<sigma>)))"
text\<open>This notation consideres failures as valid -- a definition
inspired by I/O conformance.\<close>

subsubsection\<open>Valid Execution Sequences and their Symbolic Execution\<close>
lemma exec_unit_SE [simp]: "(\<sigma> \<Turnstile> (result P)) = (P)"
by(auto simp: valid_SE_def unit_SE_def)

lemma exec_unit_SE' [simp]: "(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. Some (f \<sigma>, \<sigma>))) = (f \<sigma>\<^sub>0)"
by(simp add: valid_SE_def )

lemma exec_fail_SE [simp]: "(\<sigma> \<Turnstile> fail\<^sub>S\<^sub>E) = False"
by(auto simp: valid_SE_def fail_SE_def)

lemma exec_fail_SE'[simp]: "\<not>(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. None))"
by(simp add: valid_SE_def )

text\<open>The following the rules are in a sense the heart of the entire symbolic execution approach\<close>
lemma  exec_bind_SE_failure:
"A \<sigma> = None \<Longrightarrow> \<not>(\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)

lemma  exec_bind_SE_failure2:
"A \<sigma> = None \<Longrightarrow> \<not>(\<sigma> \<Turnstile> ((A ;- M)))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def bind_SE'_def)
  
  
lemma exec_bind_SE_success: 
"A \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s))) = (\<sigma>' \<Turnstile> (M b))"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def )
    
lemma exec_bind_SE_success2: 
"A \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma> \<Turnstile> ((A ;- M))) = (\<sigma>' \<Turnstile> M)"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def bind_SE'_def )
    

lemma exec_bind_SE_success': (* atomic boolean Monad "Query Functions" *) 
"M \<sigma> = Some(f \<sigma>,\<sigma>) \<Longrightarrow>  (\<sigma> \<Turnstile> M) = f \<sigma>"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )




lemma exec_bind_SE_success'':
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> v \<sigma>'. the(A \<sigma>) = (v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


lemma exec_bind_SE_success''':
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> a. (A \<sigma>) = Some a \<and> (snd a) \<Turnstile> (M (fst a))"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


lemma  exec_bind_SE_success'''' :
"\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> v \<sigma>'. A \<sigma> = Some(v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
apply(auto simp: valid_SE_def unit_SE_def bind_SE_def)
apply(cases "A \<sigma>", simp_all)
apply(drule_tac x="A \<sigma>" and f=the in arg_cong, simp)
apply(rule_tac x="fst aa" in exI)
apply(rule_tac x="snd aa" in exI, auto)
done


lemma valid_bind_cong : " f \<sigma> = g \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (x \<leftarrow> f ; M x)) = (\<sigma> \<Turnstile> (x \<leftarrow> g ; M x))"
  unfolding bind_SE'_def bind_SE_def valid_SE_def
    by simp
  
lemma valid_bind'_cong : " f \<sigma> = g \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> f ;- M) = (\<sigma> \<Turnstile> g ;- M)"
  unfolding bind_SE'_def bind_SE_def valid_SE_def
    by simp


text\<open>Recall \verb+mbind_unit+ for the base case.\<close>

lemma valid_mbind_mt : "(\<sigma> \<Turnstile> ( s \<leftarrow>  mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e [] f; unit\<^sub>S\<^sub>E (P s))) = P [] " by simp
lemma valid_mbind_mtE: "\<sigma> \<Turnstile> ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e [] f; unit\<^sub>S\<^sub>E (P s)) \<Longrightarrow> (P [] \<Longrightarrow> Q) \<Longrightarrow> Q"
by(auto simp: valid_mbind_mt)

lemma valid_mbind'_mt : "(\<sigma> \<Turnstile> ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p [] f; unit\<^sub>S\<^sub>E (P s))) = P [] " by simp
lemma valid_mbind'_mtE: "\<sigma> \<Turnstile> ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p [] f; unit\<^sub>S\<^sub>E (P s)) \<Longrightarrow> (P [] \<Longrightarrow> Q) \<Longrightarrow> Q"
by(auto simp: valid_mbind'_mt)

lemma valid_mbind''_mt : "(\<sigma> \<Turnstile> ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e [] f; unit\<^sub>S\<^sub>E (P s))) = P [] " 
by(simp add: mbind''.simps valid_SE_def bind_SE_def unit_SE_def)
lemma valid_mbind''_mtE: "\<sigma> \<Turnstile> ( s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e [] f; unit\<^sub>S\<^sub>E (P s)) \<Longrightarrow> (P [] \<Longrightarrow> Q) \<Longrightarrow> Q"
by(auto simp: valid_mbind''_mt)


lemma exec_mbindFSave_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ; M s)) =  (\<sigma> \<Turnstile> (M []))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def)

lemma exec_mbindFStop_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; M s)) =  (False)"
by(simp add: exec_bind_SE_failure)

lemma exec_mbindFPurge_failure: 
"ioprog a \<sigma> = None \<Longrightarrow> 
   (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ; M s)) = (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (S) ioprog ; M s))" 
by(simp add: valid_SE_def unit_SE_def bind_SE_def mbind''.simps)


lemma exec_mbindFSave_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog \<sigma>'", auto)

lemma exec_mbindFStop_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog \<sigma>'", auto simp:  mbind'.simps)

lemma exec_mbindFPurge_success : 
"ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
   (\<sigma>  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ; M s)) = 
   (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog ; M (b#s)))"
unfolding valid_SE_def unit_SE_def bind_SE_def 
by(cases "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog \<sigma>'", auto simp:  mbind''.simps)

lemma exec_mbindFSave:
"(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e  (a#S) ioprog ; return (P s))) =
    (case ioprog a \<sigma> of
       None \<Rightarrow> (\<sigma>  \<Turnstile> (return (P [])))
     | Some(b,\<sigma>') \<Rightarrow> (\<sigma>'  \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e  S ioprog ; return (P (b#s)))))"
apply(case_tac "ioprog a \<sigma>")
apply(auto simp: exec_mbindFSave_failure  exec_mbindFSave_success split: prod.splits)
done

lemma mbind_eq_sexec: 
assumes * : "\<And>b \<sigma>'. f a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
             (os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S f; P (b#os)) = (os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S f; P' (b#os))"
shows       "( a \<leftarrow> f a;  x \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S f; P (a # x)) \<sigma> = 
             ( a \<leftarrow> f a;  x \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S f; P'(a # x)) \<sigma>"
  apply(cases "f a \<sigma> = None")
  apply(subst bind_SE_def, simp)
 apply(subst bind_SE_def, simp)
 apply auto
 apply(subst bind_SE_def, simp)
 apply(subst bind_SE_def, simp)
apply(simp add: *)
done


lemma mbind_eq_sexec': 
assumes * : "\<And>b \<sigma>'. f a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
             (P (b))\<sigma>' = (P' (b))\<sigma>'"
shows       "( a \<leftarrow> f a;  P (a)) \<sigma> = 
             ( a \<leftarrow> f a;  P'(a)) \<sigma>"
 apply(cases "f a \<sigma> = None")
   apply(subst bind_SE_def, simp)
  apply(subst bind_SE_def, simp)
  apply auto
  apply(subst bind_SE_def, simp)
  apply(subst bind_SE_def, simp)
 apply(simp add: *)
done

lemma mbind'_concat:
"(os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (S@T) f; P os) = (os \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S f; os' \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p T f; P (os @ os'))"
proof (rule ext, rename_tac "\<sigma>", induct S arbitrary: \<sigma> P) 
   case Nil show ?case by simp
next
   case (Cons a S) show ?case 
        apply(insert Cons.hyps, simp)
        by(rule mbind_eq_sexec',simp)
qed

lemma assert_suffix_inv : 
              "\<sigma> \<Turnstile> ( _ \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p xs istep; assert\<^sub>S\<^sub>E (P)) 
               \<Longrightarrow> \<forall>\<sigma>. P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> (_ \<leftarrow> istep x; assert\<^sub>S\<^sub>E (P)))
               \<Longrightarrow> \<sigma> \<Turnstile> ( _ \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (xs @ [x]) istep; assert\<^sub>S\<^sub>E (P))"
apply(subst mbind'_concat, simp)
unfolding bind_SE_def assert_SE_def valid_SE_def
apply(auto split: option.split option.split_asm)
apply(case_tac "aa",simp_all)
apply(case_tac "P bb",simp_all)
apply (metis option.distinct(1))
apply(case_tac "aa",simp_all)
apply(case_tac "P bb",simp_all)
by (metis option.distinct(1))



text\<open>Universal splitting and symbolic execution rule\<close>
lemma exec_mbindFSave_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e (a#S) ioprog ;  (P s)))"
  and   none: "ioprog a \<sigma> = None \<Longrightarrow> (\<sigma> \<Turnstile> (P [])) \<Longrightarrow> Q"
  and   some: "\<And> b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S ioprog;(P (b#s)))) \<Longrightarrow> Q "
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(rule none[OF ass])
        apply(insert ass, erule_tac ioprog1=ioprog in exec_mbindFSave_failure[THEN iffD1],rule seq)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFSave_success[THEN iffD1],rule seq)
        done
qed

text\<open>The next rule reveals the particular interest in deduction;
       as an elimination rule, it allows for a linear conversion of a validity judgement
       @{term "mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p"} over an input list @{term "S"} into a constraint system; without any 
       branching ... Symbolic execution can even be stopped tactically whenever 
       @{term "ioprog a \<sigma> = Some(b,\<sigma>')"} comes to a contradiction.\<close>
lemma exec_mbindFStop_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p (a#S) ioprog ; (P s)))"
  and   some: "\<And>b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>'\<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p S ioprog;(P(b#s)))) \<Longrightarrow> Q"
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(insert ass seq)
        apply(drule_tac \<sigma>=\<sigma> and S=S and M=P in exec_mbindFStop_failure, simp)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFStop_success[THEN iffD1],rule seq)
        done
qed


lemma exec_mbindFPurge_E:
assumes seq : "(\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e (a#S) ioprog ;  (P s)))"
  and   none: "ioprog a \<sigma> = None \<Longrightarrow> (\<sigma> \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog;(P (s)))) \<Longrightarrow> Q"
  and   some: "\<And> b \<sigma>'. ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma>' \<Turnstile> (s \<leftarrow> mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>P\<^sub>u\<^sub>r\<^sub>g\<^sub>e S ioprog;(P (b#s)))) \<Longrightarrow> Q "
shows   "Q"
using seq
proof(cases "ioprog a \<sigma>")  
   case None  assume ass:"ioprog a \<sigma> = None" show "Q" 
        apply(rule none[OF ass])
        apply(insert ass, erule_tac ioprog1=ioprog in exec_mbindFPurge_failure[THEN iffD1],rule seq)
        done
next
   case (Some aa) assume ass:"ioprog a \<sigma> = Some aa" show "Q" 
        apply(insert ass,cases "aa",simp, rename_tac "out" "\<sigma>'")
        apply(erule some)
        apply(insert ass,simp)
        apply(erule_tac ioprog1=ioprog in exec_mbindFPurge_success[THEN iffD1],rule seq)
        done
qed


lemma assert_disch1 :" P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) = (\<sigma> \<Turnstile> (M True))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch2 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P ; M s))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch3 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (assert\<^sub>S\<^sub>E P))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch4 :" P \<sigma> \<Longrightarrow>  (\<sigma> \<Turnstile> (assert\<^sub>S\<^sub>E P))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_simp : "(\<sigma> \<Turnstile> assert\<^sub>S\<^sub>E P) = P \<sigma>"
by (meson assert_disch3 assert_disch4)

lemmas assert_D = assert_simp[THEN iffD1]  (* legacy *)

lemma assert_bind_simp : "(\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) = (P \<sigma> \<and> (\<sigma> \<Turnstile> (M True)))"
by(auto simp: bind_SE_def assert_SE_def valid_SE_def split: HOL.if_split_asm)

lemmas assert_bindD = assert_bind_simp[THEN iffD1]  (* legacy *)


lemma assume_D : "(\<sigma> \<Turnstile> (_ \<leftarrow> assume\<^sub>S\<^sub>E P; M)) \<Longrightarrow> \<exists> \<sigma>. (P \<sigma> \<and> (\<sigma> \<Turnstile> M) )"
apply(auto simp: bind_SE_def assume_SE_def valid_SE_def split: HOL.if_split_asm)
apply(rule_tac x="Eps P" in exI, auto)
apply(subst Hilbert_Choice.someI,assumption,simp)
done


lemma assume_E :
assumes *  : "\<sigma> \<Turnstile> ( _ \<leftarrow> assume\<^sub>S\<^sub>E P; M) "
and     ** : "\<And> \<sigma>. P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> M  \<Longrightarrow> Q"
shows  "Q"
apply(insert *)
by(insert *[THEN assume_D], auto intro: **)

lemma assume_E' :
assumes *  : "\<sigma> \<Turnstile> assume\<^sub>S\<^sub>E P ;- M"
and     ** : "\<And> \<sigma>. P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> M  \<Longrightarrow> Q"
shows  "Q"
by(insert *[simplified "bind_SE'_def", THEN assume_D], auto intro: **)


text\<open>These two rule prove that the SE Monad in connection with the notion of valid sequence
is actually sufficient for a representation of a Boogie-like language. The SBE monad with explicit
sets of states --- to be shown below --- is strictly speaking not necessary (and will therefore
be discontinued in the development).\<close>

term "if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi"

lemma if_SE_D1 : "P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = (\<sigma> \<Turnstile> B\<^sub>1)"
by(auto simp: if_SE_def valid_SE_def)

lemma if_SE_D1' : "P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> (B\<^sub>1;-M))"
by(auto simp: if_SE_def valid_SE_def bind_SE'_def bind_SE_def)


lemma if_SE_D2 : "\<not> P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = (\<sigma> \<Turnstile> B\<^sub>2)"
by(auto simp: if_SE_def valid_SE_def)

lemma if_SE_D2' : "\<not> P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M) = (\<sigma> \<Turnstile> B\<^sub>2;-M)"
by(auto simp: if_SE_def valid_SE_def bind_SE'_def bind_SE_def)


lemma if_SE_split_asm : 
"(\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = ((P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>1)) \<or> (\<not> P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>2)))"
by(cases "P \<sigma>",auto simp: if_SE_D1 if_SE_D2)

lemma if_SE_split_asm': 
"(\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M) = ((P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>1;-M)) \<or> (\<not> P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>2;-M)))"
by(cases "P \<sigma>",auto simp: if_SE_D1' if_SE_D2')


lemma if_SE_split: 
"(\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi)) = ((P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>1)) \<and> (\<not> P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>2)))"
by(cases "P \<sigma>", auto simp: if_SE_D1 if_SE_D2)


lemma if_SE_split': 
"(\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M) = ((P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>1;-M)) \<and> (\<not> P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>2;-M)))"
by(cases "P \<sigma>", auto simp: if_SE_D1' if_SE_D2')

lemma if_SE_execE:
  assumes A: "\<sigma> \<Turnstile> ((if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi))"
   and   B: "P \<sigma>  \<Longrightarrow> \<sigma> \<Turnstile> (B\<^sub>1) \<Longrightarrow> Q"
   and   C: "\<not> P \<sigma>\<Longrightarrow> \<sigma> \<Turnstile> (B\<^sub>2) \<Longrightarrow> Q"
  shows  "Q"
by(insert A [simplified if_SE_split],cases  "P \<sigma>", simp_all, auto elim: B C)


lemma if_SE_execE':
  assumes A: "\<sigma> \<Turnstile> ((if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi);-M)"
   and   B: "P \<sigma>  \<Longrightarrow> \<sigma> \<Turnstile> (B\<^sub>1;-M) \<Longrightarrow> Q"
   and   C: "\<not> P \<sigma>\<Longrightarrow> \<sigma> \<Turnstile> (B\<^sub>2;-M) \<Longrightarrow> Q"
  shows  "Q"
by(insert A [simplified if_SE_split'],cases  "P \<sigma>", simp_all, auto elim: B C)


lemma exec_while : 
"(\<sigma> \<Turnstile> ((while\<^sub>S\<^sub>E b do c od) ;- M)) = 
 (\<sigma> \<Turnstile> ((if\<^sub>S\<^sub>E b then c ;- (while\<^sub>S\<^sub>E b do c od) else unit\<^sub>S\<^sub>E ()fi) ;- M))"
apply(subst while_SE_unfold)
by(simp add: bind_SE'_def )

lemmas exec_whileD = exec_while[THEN iffD1]

lemma if_SE_execE'':
"\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi) ;- M 
\<Longrightarrow> (P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> B\<^sub>1 ;- M \<Longrightarrow> Q) 
\<Longrightarrow> (\<not> P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> B\<^sub>2 ;- M \<Longrightarrow> Q) 
\<Longrightarrow> Q"
by(auto elim: if_SE_execE')

definition "opaque (x::bool) = x"
lemma if_SE_execE''_pos:
"\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi) ;- M 
\<Longrightarrow> (P \<sigma> \<Longrightarrow> \<sigma> \<Turnstile> B\<^sub>1 ;- M \<Longrightarrow> Q) 
\<Longrightarrow> (opaque (\<sigma> \<Turnstile> (if\<^sub>S\<^sub>E P then B\<^sub>1 else B\<^sub>2 fi) ;- M) \<Longrightarrow> Q) 
\<Longrightarrow> Q"
using opaque_def by auto


lemma [code]:
  "(\<sigma> \<Turnstile> m) = (case (m \<sigma>) of None  \<Rightarrow> False | (Some (x,y))  \<Rightarrow> x)"
  apply(simp add: valid_SE_def)
  apply(cases "m \<sigma> = None", simp_all) 
  apply(insert not_None_eq, auto)
done

    
(* for the moment no good idea to state the case where the body eventually crashes. *)
lemma "P  \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E P ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  (x=X) \<and> Q x \<sigma>))"
oops

lemma "\<forall>\<sigma>. \<exists> X. \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E P ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  x=X \<and> Q x \<sigma>))"
oops


lemma monadic_sequence_rule:
      "\<And> X \<sigma>\<^sub>1. (\<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E (\<lambda>\<sigma>'. (\<sigma>=\<sigma>') \<and>  P \<sigma>) ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  (x=X) \<and> (\<sigma>=\<sigma>\<^sub>1) \<and> Q x \<sigma>)))
               \<and> 
               (\<sigma>\<^sub>1 \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E (\<lambda>\<sigma>.  (\<sigma>=\<sigma>\<^sub>1) \<and> Q x \<sigma>) ; y  \<leftarrow> M'; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  R x y \<sigma>)))
       \<Longrightarrow>
               \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E (\<lambda>\<sigma>'. (\<sigma>=\<sigma>') \<and>  P \<sigma>) ; x  \<leftarrow> M; y  \<leftarrow> M'; assert\<^sub>S\<^sub>E (R x y))"
apply(elim exE impE conjE)
apply(drule assume_D) 
apply(elim exE impE conjE)
unfolding valid_SE_def assume_SE_def assert_SE_def bind_SE_def
apply(auto split: if_split HOL.if_split_asm Option.option.split Option.option.split_asm)
apply (metis (mono_tags, lifting) option.simps(3) someI_ex)
oops


  
lemma "\<exists> X. \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E P ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>.  x=X \<and> Q x \<sigma>))
       \<Longrightarrow> 
            \<sigma> \<Turnstile> (_  \<leftarrow> assume\<^sub>S\<^sub>E P ; x  \<leftarrow> M; assert\<^sub>S\<^sub>E (\<lambda>\<sigma>. Q x \<sigma>))"
unfolding valid_SE_def assume_SE_def assert_SE_def bind_SE_def
by(auto split: if_split HOL.if_split_asm Option.option.split Option.option.split_asm)


lemma exec_skip:
"(\<sigma> \<Turnstile> skip\<^sub>S\<^sub>E ;- M) = (\<sigma> \<Turnstile> M)"
by (simp add: skip\<^sub>S\<^sub>E_def)

lemmas exec_skipD = exec_skip[THEN iffD1]


text\<open>Test-Refinements will be stated in terms of the failsave @{term mbind}, opting 
       more generality. The following lemma allows for an  optimization both in 
       test execution as well as in symbolic execution for an important special case of
       the post-codition: Whenever the latter has the constraint that the length of input and 
       output sequence equal each other (that is to say: no failure occured), failsave mbind
       can be reduced to failstop mbind ...\<close>
lemma mbindFSave_vs_mbindFStop : 
  "(\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog); result(length \<iota>s = length os \<and> P \<iota>s os))) = 
   (\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog); result(P \<iota>s os)))"
  apply(rule_tac x=P in spec)
  apply(rule_tac x=\<sigma> in spec)
  proof(induct "\<iota>s") 
     case Nil show ?case by(simp_all add: mbind_try try_SE_def del: Seq_MonadSE.mbind.simps)
     case (Cons a \<iota>s) show ?case
          apply(rule allI, rename_tac "\<sigma>",rule allI, rename_tac "P")
          apply(insert Cons.hyps)
          apply(case_tac "ioprog a \<sigma>")
          apply(simp only: exec_mbindFSave_failure exec_mbindFStop_failure, simp)
          apply(simp add:  split_paired_all del: Seq_MonadSE.mbind.simps )
          apply(rename_tac "\<sigma>'") 
          apply(subst exec_mbindFSave_success, assumption)
          apply(subst (2) exec_bind_SE_success, assumption)
          apply(erule_tac x="\<sigma>'" in allE)
          apply(erule_tac x="\<lambda>\<iota>s s. P (a # \<iota>s) (aa # s)" in allE) (* heureka ! *)
          apply(simp)
      done
  qed


lemma mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e_vs_mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p:
assumes A: "\<forall> \<iota> \<sigma>. ioprog \<iota> \<sigma> \<noteq> None"
shows      "(\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog); P os)) = 
            (\<sigma> \<Turnstile> (os \<leftarrow> (mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog); P os))" 
proof(induct "\<iota>s") 
  case Nil show ?case by simp
next 
  case (Cons a \<iota>s) 
       from Cons.hyps                           
       have B:"\<forall> S f \<sigma>. mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e S f \<sigma> \<noteq> None " by simp
       have C:"\<forall>\<sigma>. mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>t\<^sub>o\<^sub>p \<iota>s ioprog \<sigma> = mbind\<^sub>F\<^sub>a\<^sub>i\<^sub>l\<^sub>S\<^sub>a\<^sub>v\<^sub>e \<iota>s ioprog \<sigma>" 
               apply(induct \<iota>s, simp)
               apply(rule allI,rename_tac "\<sigma>")
               apply(simp add: Seq_MonadSE.mbind'.simps(2))
               apply(insert A, erule_tac x="a" in allE)
               apply(erule_tac x="\<sigma>" and P="\<lambda>\<sigma> . ioprog a \<sigma> \<noteq> None" in allE)
               apply(auto split:option.split)
               done
       show ?case 
       apply(insert A,erule_tac x="a" in allE,erule_tac x="\<sigma>" in allE)
       apply(simp, elim exE)
       apply(rename_tac  "out" "\<sigma>'")
       apply(insert B, erule_tac x=\<iota>s in allE, erule_tac x=ioprog in allE, erule_tac x=\<sigma>' in allE)
       apply(subst(asm) not_None_eq, elim exE)
       apply(subst  exec_bind_SE_success)
       apply(simp   split: option.split, auto)
       apply(rule_tac s="(\<lambda> a b c. a # (fst c)) out \<sigma>' (aa, b)" in trans, simp,rule refl)
       apply(rule_tac s="(\<lambda> a b c. (snd c)) out \<sigma>' (aa, b)" in trans, simp,rule refl)
       apply(simp_all)
       apply(subst  exec_bind_SE_success, assumption)
       apply(subst  exec_bind_SE_success)
       apply(rule_tac s="Some (aa, b)" in  trans,simp_all add:C)
       apply(subst(asm)  exec_bind_SE_success, assumption)
       apply(subst(asm)  exec_bind_SE_success)
       apply(rule_tac s="Some (aa, b)" in  trans,simp_all add:C)
    done
qed

subsection\<open>Miscellaneous\<close>

no_notation unit_SE ("(result _)" 8)

end
  