section \<open>Semantics of IMP\<close>
theory Semantics
imports Syntax "HOL-Eisbach.Eisbach_Tools" 
begin

subsection \<open>State\<close>
text \<open>The state maps variable names to values\<close>
type_synonym state = "vname \<Rightarrow> val"

text \<open>We introduce some syntax for the null state, and a state where only certain 
  variables are set.\<close>
definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. \<lambda>i. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

subsubsection \<open>State Combination\<close>
text \<open>The state combination operator constructs a state by 
  taking the local variables from one state, and the globals from another state.\<close>

definition combine_states :: "state \<Rightarrow> state \<Rightarrow> state" ("<_|_>" [0,0] 1000)
  where "<s|t> n = (if is_local n then s n else t n)"

text \<open>We prove some basic facts. 

Note that we use Isabelle's context command to locally declare the 
  definition of @{const combine_states} as simp lemma, such that it is 
  unfolded automatically.\<close>
  
context notes [simp] = combine_states_def begin

lemma combine_collapse: "<s|s> = s" by auto

lemma combine_nest:  
  "<s|<s'|t>> = <s|t>"
  "<<s|t'>|t> = <s|t>"
  by auto  
  
lemma combine_query: 
  "is_local x \<Longrightarrow> <s|t> x = s x"  
  "is_global x \<Longrightarrow> <s|t> x = t x"  
  by auto

lemma combine_upd: 
  "is_local x \<Longrightarrow> <s|t>(x:=v) = <s(x:=v)|t>"  
  "is_global x \<Longrightarrow> <s|t>(x:=v) = <s|t(x:=v)>"  
  by auto  
  
lemma combine_cases[cases type]:
  obtains l g where "s = <l|g>"
  by (fastforce)
  
end  
  
  
  
    
  
  
subsection \<open>Arithmetic Expressions\<close>
text \<open>The evaluation of arithmetic expressions is straightforward. \<close>
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> pval" where
  "aval (N n) s = n" 
| "aval (Vidx x i) s = s x (aval i s)" 
| "aval (Unop f a\<^sub>1) s = f (aval a\<^sub>1 s)"
| "aval (Binop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

subsection \<open>Boolean Expressions\<close>
text \<open>The evaluation of Boolean expressions is straightforward. \<close>

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
  "bval (Bc v) s = v" 
| "bval (Not b) s = (\<not> bval b s)" 
| "bval (BBinop f b\<^sub>1 b\<^sub>2) s = f (bval b\<^sub>1 s) (bval b\<^sub>2 s)" 
| "bval (Cmpop f a\<^sub>1 a\<^sub>2) s = f (aval a\<^sub>1 s) (aval a\<^sub>2 s)"

subsection \<open>Big-Step Semantics\<close>
text \<open>The big-step semantics is a relation from commands and start states to end states,
  such that there is a terminating execution.

  If there is no such execution, no end state will be related to the command and start state.
  This either means that the program does not terminate, or gets stuck because it tries to call
  an undefined procedure.

  The inference rules of the big-step semantics are pretty straightforward.
\<close>

inductive big_step :: "program \<Rightarrow> com \<times> state \<Rightarrow> state \<Rightarrow> bool" 
  ("_: _ \<Rightarrow> _" [1000,55,55] 55)
where
  \<comment> \<open>No-Op\<close>
  Skip: "\<pi>:(SKIP,s) \<Rightarrow> s" 
  
  \<comment> \<open>Assignments\<close>
| AssignIdx: "\<pi>:(x[i] ::= a,s) \<Rightarrow> s(x := (s x)(aval i s := aval a s))" 
| ArrayCpy: "\<pi>:(x[] ::= y,s) \<Rightarrow> s(x := s y)" 
| ArrayClear: "\<pi>:(CLEAR x[],s) \<Rightarrow> s(x := (\<lambda>_. 0))" 
| Assign_Locals: "\<pi>:(Assign_Locals l,s) \<Rightarrow> <l|s>"

  \<comment> \<open>Block commands\<close>
| Seq: "\<lbrakk> \<pi>:(c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  \<pi>:(c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> \<pi>:(c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" 
| IfTrue: "\<lbrakk> bval b s; \<pi>:(c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<pi>:(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" 
| IfFalse: "\<lbrakk> \<not>bval b s;  \<pi>:(c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<pi>:(IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" 
| Scope: "\<lbrakk> \<pi>:(c,<<>|s>) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> \<pi>:(SCOPE c, s) \<Rightarrow> <s|s'>"
| WhileFalse: "\<not>bval b s \<Longrightarrow> \<pi>:(WHILE b DO c,s) \<Rightarrow> s" 
| WhileTrue: "\<lbrakk> bval b s\<^sub>1;  \<pi>:(c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  \<pi>:(WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
    \<Longrightarrow> \<pi>:(WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3"

  \<comment> \<open>Procedure commands\<close>        
| PCall: "\<lbrakk> \<pi> p = Some c; \<pi>:(c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<pi>:(PCall p,s) \<Rightarrow> t"    
| PScope: "\<lbrakk> \<pi>':(c,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<pi>:(PScope \<pi>' c, s) \<Rightarrow> t"


subsubsection \<open>Proof Automation\<close>    
text \<open>
  We do some setup to make proofs over the big-step semantics more automatic.
\<close>

declare big_step.intros [intro]
lemmas big_step_induct[induct set] = big_step.induct[split_format(complete)]

inductive_simps Skip_simp: "\<pi>:(SKIP,s) \<Rightarrow> t"
inductive_simps AssignIdx_simp: "\<pi>:(x[i] ::= a,s) \<Rightarrow> t"
inductive_simps ArrayCpy_simp: "\<pi>:(x[] ::= y,s) \<Rightarrow> t"
inductive_simps ArrayInit_simp: "\<pi>:(CLEAR x[],s) \<Rightarrow> t"
inductive_simps AssignLocals_simp: "\<pi>:(Assign_Locals l,s) \<Rightarrow> t"

inductive_simps Seq_simp: "\<pi>:(c1;;c2,s1) \<Rightarrow> s3"
inductive_simps If_simp: "\<pi>:(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_simps Scope_simp: "\<pi>:(SCOPE c,s) \<Rightarrow> t"
inductive_simps PCall_simp: "\<pi>:(PCall p,s) \<Rightarrow> t"
inductive_simps PScope_simp: "\<pi>:(PScope \<pi>' p,s) \<Rightarrow> t"

lemmas big_step_simps = 
  Skip_simp AssignIdx_simp ArrayCpy_simp ArrayInit_simp
  Seq_simp If_simp Scope_simp PCall_simp PScope_simp

  
inductive_cases SkipE[elim!]: "\<pi>:(SKIP,s) \<Rightarrow> t"
inductive_cases AssignIdxE[elim!]: "\<pi>:(x[i] ::= a,s) \<Rightarrow> t"
inductive_cases ArrayCpyE[elim!]: "\<pi>:(x[] ::= y,s) \<Rightarrow> t"
inductive_cases ArrayInitE[elim!]: "\<pi>:(CLEAR x[],s) \<Rightarrow> t"
inductive_cases AssignLocalsE[elim!]: "\<pi>:(Assign_Locals l,s) \<Rightarrow> t"

inductive_cases SeqE[elim!]: "\<pi>:(c1;;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "\<pi>:(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases ScopeE[elim!]: "\<pi>:(SCOPE c,s) \<Rightarrow> t"
inductive_cases PCallE[elim!]: "\<pi>:(PCall p,s) \<Rightarrow> t"
inductive_cases PScopeE[elim!]: "\<pi>:(PScope \<pi>' p,s) \<Rightarrow> t"
  
inductive_cases WhileE[elim]: "\<pi>:(WHILE b DO c,s) \<Rightarrow> t"
                             

subsubsection \<open>Automatic Derivation\<close>
  (* TODO: More comments, test *)
  (* Testing the programs by constructing big-step derivations automatically *)    
    
  (* This rule is used to enforce simplification of the newly generated state, before passing it on *)
  lemma Assign': "s' = s(x := (s x)(aval i s := aval a s)) \<Longrightarrow> \<pi>:(x[i] ::= a, s) \<Rightarrow> s'" by auto
  lemma ArrayCpy': "s' = s(x := (s y)) \<Longrightarrow> \<pi>:(x[] ::= y, s) \<Rightarrow> s'" by auto
  lemma ArrayClear': "s' = s(x := (\<lambda>_. 0)) \<Longrightarrow> \<pi>:(CLEAR x[], s) \<Rightarrow> s'" by auto

  lemma Scope': "s\<^sub>1 = <<>|s> \<Longrightarrow> \<pi>:(c,s\<^sub>1) \<Rightarrow> t \<Longrightarrow> t' = <s|t> \<Longrightarrow> \<pi>:(Scope c,s) \<Rightarrow> t'" by auto

  named_theorems deriv_unfolds \<open>Unfold rules before derivations\<close>
  
  method bs_simp = simp add: combine_nest combine_upd combine_query fun_upd_same fun_upd_other del: fun_upd_apply
  
  method big_step' = 
    rule Skip Seq PScope
  | (rule Assign' ArrayCpy' ArrayClear', (bs_simp;fail)) 
  | (rule IfTrue IfFalse WhileTrue WhileFalse PCall Scope'), (bs_simp;fail)
  | unfold deriv_unfolds
  | (bs_simp; fail)
  
      
  method big_step = 
    rule Skip 
  | rule Seq, (big_step;fail), (big_step;fail)
  | rule PScope, (big_step;fail)  
  | (rule Assign' ArrayCpy' ArrayClear', (bs_simp;fail)) 
  | (rule IfTrue IfFalse), (bs_simp;fail), (big_step;fail)
  | rule WhileTrue, (bs_simp;fail), (big_step;fail), (big_step;fail)
  | rule WhileFalse, (bs_simp;fail)
  | rule PCall, (bs_simp;fail), (big_step;fail)
  | (rule Scope', (bs_simp;fail), (big_step;fail), (bs_simp;fail))
  | unfold deriv_unfolds, big_step
  
  schematic_goal "Map.empty: (
    ''a'' ::= N 1;;
    WHILE Cmpop (\<lambda>x y. y < x) (V ''n'') (N 0) DO (
      ''a'' ::= Binop (+) (V ''a'') (V ''a'');; 
      ''n'' ::= Binop (-) (V ''n'') (N 1)
    ),<''n'':=(\<lambda>_. 5)>) \<Rightarrow> ?s"  
    by big_step



subsection \<open>Command Equivalence\<close>

text \<open>Two commands are equivalent if they have the same semantics.\<close>
definition
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>\<pi> s t. \<pi>:(c,s) \<Rightarrow> t  = \<pi>:(c',s) \<Rightarrow> t)"

lemma equivI[intro?]: "\<lbrakk>
  \<And>s t \<pi>. \<pi>:(c,s) \<Rightarrow> t \<Longrightarrow> \<pi>:(c',s) \<Rightarrow> t; 
  \<And>s t \<pi>. \<pi>:(c',s) \<Rightarrow> t \<Longrightarrow> \<pi>:(c,s) \<Rightarrow> t\<rbrakk> 
  \<Longrightarrow> c \<sim> c'"  
  by (auto simp: equiv_c_def)
  
lemma equivD[dest]: "c \<sim> c' \<Longrightarrow> \<pi>:(c,s) \<Rightarrow> t \<longleftrightarrow> \<pi>:(c',s) \<Rightarrow> t"  
  by (auto simp: equiv_c_def)

text \<open>Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive.\<close>

lemma equiv_refl[simp, intro!]:  "c \<sim> c"
  by (blast intro: equivI)
lemma equiv_sym[sym]:   "(c \<sim> c') \<Longrightarrow> (c' \<sim> c)"
  by (blast intro: equivI)
lemma equiv_trans[trans]: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''"
  by (blast intro: equivI)

subsubsection \<open>Basic Equivalences\<close>
lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by rule auto

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
  by (auto intro!: equivI)

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
  by (auto intro!: equivI)

lemma sim_while_cong_aux:
  "\<lbrakk>\<pi>:(WHILE b DO c,s) \<Rightarrow> t; bval b = bval b'; c \<sim> c' \<rbrakk> \<Longrightarrow> \<pi>:(WHILE b' DO c',s) \<Rightarrow> t"
  by(induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct) auto

lemma sim_while_cong: "bval b = bval b' \<Longrightarrow> c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b' DO c'"
  using equiv_c_def sim_while_cong_aux by auto

subsection \<open>Execution is Deterministic\<close>

text \<open>This proof is automatic.\<close>

theorem big_step_determ: "\<lbrakk> \<pi>:(c,s) \<Rightarrow> t; \<pi>:(c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
proof (induction arbitrary: u rule: big_step.induct)
  case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
    then show ?case by blast
qed fastforce+

subsection \<open>Small-Step Semantics\<close>

text \<open>
  The small step semantics is defined by a step function on
  a pair of command and state. Intuitively, the command is 
  the remaining part of the program that still has to be executed.
  The step function is defined to stutter if the command is @{const SKIP}.
  
  Moreover, the step function is explicitly partial, returning @{const None} 
  on error, i.e., on an undefined procedure call.

  Most steps are straightforward. 
  For a sequential composition, steps are performed on the first command, 
  until it has been reduced to @{const SKIP}, then the sequential composition is 
  reduced to the second command. 

  A while command is reduced by unfolding the loop once.
    
  A scope command is reduced to the inner command, followed by 
  an @{const Assign_Locals} command to restore the original local variables.

  A procedure scope command is reduced by performing a step in the inner command, 
  with the new procedure environment, until the inner command has been reduced to @{const SKIP}.
  Then, the whole command is reduced to @{const SKIP}. 
\<close>

fun small_step :: "program \<Rightarrow> com \<times> state \<rightharpoonup> com \<times> state" where
  "small_step \<pi> (x[i]::=a,s) = Some (SKIP, s(x := (s x)(aval i s := aval a s)))"
| "small_step \<pi> (x[]::=y,s) = Some (SKIP, s(x := s y))"  
| "small_step \<pi> (CLEAR x[],s) = Some (SKIP, s(x := (\<lambda>_. 0)))"
| "small_step \<pi> (Assign_Locals l,s) = Some (SKIP,<l|s>)"
| "small_step \<pi> (SKIP;;c,s) = Some (c,s)"
| "small_step \<pi> (c\<^sub>1;;c\<^sub>2,s) = (case small_step \<pi> (c\<^sub>1,s) of Some (c\<^sub>1',s') \<Rightarrow> Some (c\<^sub>1';;c\<^sub>2,s') | _ \<Rightarrow> None)"
| "small_step \<pi> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) = Some (if bval b s then (c\<^sub>1,s) else (c\<^sub>2,s))"
| "small_step \<pi> (SCOPE c, s) = Some (c;;Assign_Locals s, <<>|s>)"
| "small_step \<pi> (WHILE b DO c,s) = Some (IF b THEN c;;WHILE b DO c ELSE SKIP, s)"
| "small_step \<pi> (PCall p, s) = (case \<pi> p of Some c \<Rightarrow> Some (c, s) | _ \<Rightarrow> None)"
| "small_step \<pi> (PScope \<pi>' SKIP, s) = Some (SKIP,s)"
| "small_step \<pi> (PScope \<pi>' c, s) = (case small_step \<pi>' (c,s) of Some (c',s') \<Rightarrow> Some (PScope \<pi>' c', s') | _ \<Rightarrow> None)"
| "small_step \<pi> (SKIP,s) = Some (SKIP,s)"

text \<open>
  We define the reflexive transitive closure of the step function.
\<close>
inductive small_steps :: "program \<Rightarrow> com \<times> state \<Rightarrow> (com \<times> state) option \<Rightarrow> bool" where
  [simp]: "small_steps \<pi> cs (Some cs)"
| "\<lbrakk> small_step \<pi> cs = None \<rbrakk> \<Longrightarrow> small_steps \<pi> cs None"
| "\<lbrakk> small_step \<pi> cs = Some cs1; small_steps \<pi> cs1 cs2 \<rbrakk> \<Longrightarrow> small_steps \<pi> cs cs2"

lemma small_steps_append: "small_steps \<pi> cs\<^sub>1 (Some cs\<^sub>2) \<Longrightarrow> small_steps \<pi> cs\<^sub>2 cs\<^sub>3 \<Longrightarrow> small_steps \<pi> cs\<^sub>1 cs\<^sub>3"
  apply (induction \<pi> cs\<^sub>1 "Some cs\<^sub>2" arbitrary: cs\<^sub>2 rule: small_steps.induct)
  apply (auto intro: small_steps.intros)
  done

subsubsection \<open>Equivalence to Big-Step Semantics\<close>
text \<open>We show that the small-step semantics yields a final 
  configuration if and only if the big-step semantics terminates with the respective state.
  
  Moreover, we show that the big-step semantics gets stuck if the small-step semantics 
  yields an error.
  \<close>
  
lemma small_big_append: "small_step \<pi> cs\<^sub>1 = Some cs\<^sub>2 \<Longrightarrow> \<pi>: cs\<^sub>2 \<Rightarrow> s\<^sub>3 \<Longrightarrow> \<pi>: cs\<^sub>1 \<Rightarrow> s\<^sub>3"
  apply (induction \<pi> cs\<^sub>1 arbitrary: cs\<^sub>2 s\<^sub>3 rule: small_step.induct)
  apply (auto split: option.splits if_splits)
  done

lemma smalls_big_append: "small_steps \<pi> cs\<^sub>1 (Some cs\<^sub>2) \<Longrightarrow> \<pi>: cs\<^sub>2 \<Rightarrow> s\<^sub>3 \<Longrightarrow> \<pi>: cs\<^sub>1 \<Rightarrow> s\<^sub>3"
  apply (induction \<pi> cs\<^sub>1 "Some cs\<^sub>2" arbitrary: cs\<^sub>2 rule: small_steps.induct)
  apply (auto intro: small_big_append)
  done

lemma small_imp_big:
  assumes "small_steps \<pi> cs\<^sub>1 (Some (SKIP,s\<^sub>2))" 
  shows "\<pi>: cs\<^sub>1 \<Rightarrow> s\<^sub>2"
  using smalls_big_append[OF assms]
  by auto
  
lemma small_steps_skip_term[simp]: "small_steps \<pi> (SKIP, s) cs' \<longleftrightarrow> cs'=Some (SKIP,s)"  
  apply rule
  subgoal
    apply (induction \<pi> "(SKIP,s)" cs' arbitrary: s rule: small_steps.induct)
    by (auto intro: small_steps.intros)
  by (auto intro: small_steps.intros)
    
lemma small_seq: "\<lbrakk>c\<noteq>SKIP; small_step \<pi> (c,s) = Some (c',s')\<rbrakk> \<Longrightarrow> small_step \<pi> (c;;cx,s) = Some (c';;cx,s')"  
  apply (induction \<pi> "(c,s)" arbitrary: c s c' s' rule: small_step.induct)
  apply auto
  done
  
lemma smalls_seq: "\<lbrakk>small_steps \<pi> (c,s) (Some (c',s'))\<rbrakk> \<Longrightarrow> small_steps \<pi> (c;;cx,s) (Some (c';;cx,s'))"
  apply (induction \<pi> "(c,s)" "Some (c',s')" arbitrary: c s c' s' rule: small_steps.induct)
  apply (auto dest: small_seq intro: small_steps.intros)
  by (metis option.simps(1) prod.simps(1) small_seq small_step.simps(31) small_steps.intros(3))

lemma small_pscope:  
  "\<lbrakk>c\<noteq>SKIP; small_step \<pi>' (c,s) = Some (c',s')\<rbrakk> \<Longrightarrow> small_step \<pi> (PScope \<pi>' c,s) = Some (PScope \<pi>' c',s')"
  apply (induction \<pi> "(c,s)" arbitrary: c s c' s' rule: small_step.induct)
  apply auto 
  done
    
lemma smalls_pscope:   
  "small_steps \<pi>' (c, s) (Some (c', s')) \<Longrightarrow> small_steps \<pi> (PScope \<pi>' c, s) (Some (PScope \<pi>' c',s'))"
  apply (induction \<pi>' "(c,s)" "(Some (c', s'))" arbitrary: c s rule: small_steps.induct)
  apply auto
  by (metis (no_types, hide_lams) option.inject prod.inject small_pscope small_steps.simps small_steps_append small_steps_skip_term)
  
  
  
lemma big_imp_small:
  assumes "\<pi>: cs \<Rightarrow> t"
  shows "small_steps \<pi> cs (Some (SKIP,t))"
  using assms
proof induction
  case (Skip \<pi> s)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (AssignIdx \<pi> x i a s)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (ArrayCpy \<pi> x y s)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (ArrayClear \<pi> x s)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (Seq \<pi> c\<^sub>1 s\<^sub>1 s\<^sub>2 c\<^sub>2 s\<^sub>3)
  then show ?case
    by (meson small_step.simps(5) small_steps.intros(3) small_steps_append smalls_seq)
next
  case (IfTrue b s \<pi> c\<^sub>1 t c\<^sub>2)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (IfFalse b s \<pi> c\<^sub>2 t c\<^sub>1)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (Scope \<pi> c s s')
  then show ?case 
  by (meson small_step.simps(17) small_step.simps(4) small_step.simps(5) small_steps.intros(1) small_steps.intros(3) small_steps_append smalls_seq)
next
  case (WhileFalse b s \<pi> c)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (WhileTrue b s\<^sub>1 \<pi> c s\<^sub>2 s\<^sub>3)
  then show ?case 
  proof -
    have "\<forall>ca p. (small_steps \<pi> p (Some (SKIP, s\<^sub>3)) \<or> Some (ca, s\<^sub>2) \<noteq> Some (WHILE b DO c, s\<^sub>2)) \<or> small_step \<pi> p \<noteq> Some (c;; ca, s\<^sub>1)"
      by (metis (no_types) WhileTrue.IH(1) WhileTrue.IH(2) small_step.simps(5) small_steps.intros(3) small_steps_append smalls_seq)
    then have "\<forall>ca cb cc. (small_steps \<pi> (IF b THEN cc ELSE ca, s\<^sub>1) (Some (SKIP, s\<^sub>3)) \<or> Some (cb, s\<^sub>2) \<noteq> Some (WHILE b DO c, s\<^sub>2)) \<or> Some (cc, s\<^sub>1) \<noteq> Some (c;; cb, s\<^sub>1)"
      using WhileTrue.hyps(1) by force
    then show ?thesis
      using small_step.simps(18) small_steps.intros(3) by blast
  qed
  
next
  case (PCall \<pi> p c s t)
  then show ?case by (auto 0 4 intro: small_steps.intros)
next
  case (PScope \<pi>' c s t \<pi>)
  then show ?case 
    by (meson small_step.simps(20) small_steps.simps small_steps_append smalls_pscope)
  
next
  case (Assign_Locals \<pi> l s)
  then show ?case by (auto 0 4 intro: small_steps.intros)
qed

  
text \<open>The big-step semantics yields a state \<open>t\<close>, iff and only iff there is a transition 
  of the small-step semantics to \<open>(SKIP,t).\<close>
\<close>
theorem big_eq_small: "\<pi>: cs\<Rightarrow>t \<longleftrightarrow> small_steps \<pi> cs (Some (SKIP,t))"
  using big_imp_small small_imp_big by blast

lemma small_steps_determ: 
  assumes "small_steps \<pi> cs None"  
  shows "\<not>small_steps \<pi> cs (Some (SKIP, t))"  
  using assms
  apply (induction \<pi> cs "None::(com\<times>state) option" arbitrary: t rule: small_steps.induct)
  apply (auto elim: small_steps.cases)
  done

text \<open>If the small-step semantics reaches a failure state, the big-step semantics gets stuck.\<close>    
corollary small_imp_big_fail: 
  assumes "small_steps \<pi> cs None"
  shows "\<nexists>t. \<pi>: cs \<Rightarrow> t"
  using assms
  by (auto simp: big_eq_small small_steps_determ)
   
  
  
subsection \<open>Weakest Precondition\<close>  

text \<open>The following definitions are made wrt.\ a fixed program \<open>\<pi>\<close>, which becomes the first
  parameter of the defined constants when the context is left.\<close>
context
  fixes \<pi> :: program
begin
  
  text \<open>Weakest precondition: 
    \<open>c\<close> terminates with a state that satisfies \<open>Q\<close>, when started from \<open>s\<close>.\<close>
  definition "wp c Q s \<equiv> \<exists>t. \<pi>: (c,s) \<Rightarrow> t \<and> Q t"
    \<comment> \<open>Note that this definition exploits that the semantics is deterministic! 
      In general, we must ensure absence of infinite executions\<close>

  text \<open>Weakest liberal precondition: 
    If \<open>c\<close> terminates when started from \<open>s\<close>, the new state satisfies \<open>Q\<close>.\<close>    
  definition "wlp c Q s \<equiv> \<forall>t. \<pi>:(c,s) \<Rightarrow> t \<longrightarrow> Q t"
  
  subsubsection \<open>Basic Properties\<close>
  
  context 
    notes [abs_def,simp] = wp_def wlp_def
  begin
    lemma wp_imp_wlp: "wp c Q s \<Longrightarrow> wlp c Q s"
      using big_step_determ by force
      
    lemma wlp_and_term_imp_wp: "wlp c Q s \<and> \<pi>:(c,s) \<Rightarrow> t \<Longrightarrow> wp c Q s" by auto    
    
    lemma wp_equiv: "c \<sim> c' \<Longrightarrow> wp c = wp c'" by auto
    lemma wp_conseq: "wp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wp c Q s" by auto
    
    lemma wlp_equiv: "c \<sim> c' \<Longrightarrow> wlp c = wlp c'" by auto
    lemma wlp_conseq: "wlp c P s \<Longrightarrow> \<lbrakk>\<And>s. P s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> wlp c Q s" by auto
    
      
  
  subsubsection \<open>Unfold Rules\<close>
    lemma wp_skip_eq: "wp SKIP Q s = Q s" by auto
    lemma wp_assign_idx_eq: "wp (x[i]::=a) Q s = Q (s(x:=(s x)(aval i s := aval a s)))" by auto
    lemma wp_arraycpy_eq: "wp (x[]::=a) Q s = Q (s(x:=s a))" by auto
    lemma wp_arrayinit_eq: "wp (CLEAR x[]) Q s = Q (s(x:=(\<lambda>_. 0)))" by auto
    lemma wp_assign_locals_eq: "wp (Assign_Locals l) Q s = Q <l|s>" by auto
    lemma wp_seq_eq: "wp (c\<^sub>1;;c\<^sub>2) Q s = wp c\<^sub>1 (wp c\<^sub>2 Q) s" by auto
    lemma wp_if_eq: "wp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s 
      = (if bval b s then wp c\<^sub>1 Q s else wp c\<^sub>2 Q s)" by auto
    
    lemma wp_scope_eq: "wp (SCOPE c) Q s = wp c (\<lambda>s'. Q <s|s'>) <<>|s>" by auto
    lemma wp_pcall_eq: "\<pi> p = Some c \<Longrightarrow> wp (PCall p) Q s = wp c Q s" by auto 
    
    lemmas wp_eq = wp_skip_eq wp_assign_idx_eq wp_arraycpy_eq wp_arrayinit_eq 
      wp_assign_locals_eq wp_seq_eq wp_scope_eq
    lemmas wp_eq' = wp_eq wp_if_eq
    
    lemma wlp_skip_eq: "wlp SKIP Q s = Q s" by auto
    lemma wlp_assign_idx_eq: "wlp (x[i]::=a) Q s = Q (s(x:=(s x)(aval i s := aval a s)))" by auto
    lemma wlp_arraycpy_eq: "wlp (x[]::=a) Q s = Q (s(x:=s a))" by auto
    lemma wlp_arrayinit_eq: "wlp (CLEAR x[]) Q s = Q (s(x:=(\<lambda>_. 0)))" by auto
    lemma wlp_assign_locals_eq: "wlp (Assign_Locals l) Q s = Q <l|s>" by auto
    lemma wlp_seq_eq: "wlp (c\<^sub>1;;c\<^sub>2) Q s = wlp c\<^sub>1 (wlp c\<^sub>2 Q) s" by auto
    lemma wlp_if_eq: "wlp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q s 
      = (if bval b s then wlp c\<^sub>1 Q s else wlp c\<^sub>2 Q s)" by auto

    lemma wlp_scope_eq: "wlp (SCOPE c) Q s = wlp c (\<lambda>s'. Q <s|s'>) <<>|s>" by auto
    lemma wlp_pcall_eq: "\<pi> p = Some c \<Longrightarrow> wlp (PCall p) Q s = wlp c Q s" by auto 
      
          
    lemmas wlp_eq = wlp_skip_eq wlp_assign_idx_eq wlp_arraycpy_eq wlp_arrayinit_eq 
      wlp_assign_locals_eq wlp_seq_eq wlp_scope_eq
    lemmas wlp_eq' = wlp_eq wlp_if_eq
  end
  
  lemma wlp_while_unfold: "wlp (WHILE b DO c) Q s = (if bval b s then wlp c (wlp (WHILE b DO c) Q) s else Q s)"
    apply (subst wlp_equiv[OF while_unfold])
    apply (simp add: wlp_eq')
    done
  
  lemma wp_while_unfold: "wp (WHILE b DO c) Q s = (if bval b s then wp c (wp (WHILE b DO c) Q) s else Q s)"
    apply (subst wp_equiv[OF while_unfold])
    apply (simp add: wp_eq')
    done
    
end \<comment> \<open>Context fixing program\<close>

text \<open>Unfold rules for procedure scope\<close>
lemma wp_pscope_eq: "wp \<pi> (PScope \<pi>' c) Q s = wp \<pi>' (c) Q s"
  unfolding wp_def by auto

lemma wlp_pscope_eq: "wlp \<pi> (PScope \<pi>' c) Q s = wlp \<pi>' (c) Q s"
  unfolding wlp_def by auto
  
subsubsection \<open>Weakest precondition and Program Equivalence\<close>
text \<open>The following three statements are equivalent:
  \<^enum> The commands \<open>c\<close> and \<open>c'\<close> are equivalent
  \<^enum> The weakest preconditions are equivalent, for all procedure environments
  \<^enum> The weakest liberal preconditions are equivalent, for all procedure environments
\<close>

lemma wp_equiv_iff: "(\<forall>\<pi>. wp \<pi> c = wp \<pi> c') \<longleftrightarrow> c \<sim> c'"
  unfolding equiv_c_def
  using big_step_determ unfolding wp_def
  by (auto; metis)

lemma wlp_equiv_iff: "(\<forall>\<pi>. wlp \<pi> c = wlp \<pi> c') \<longleftrightarrow> c \<sim> c'" 
  unfolding equiv_c_def wlp_def
  by (auto; metis (no_types, hide_lams))


subsubsection \<open>While Loops and Weakest Precondition\<close>  

text \<open>Exchanging the loop condition by an equivalent one, and the loop 
  body by one with the same weakest precondition, does not change the weakest 
  precondition of the loop.\<close>  
lemma sim_while_wp_aux:
  assumes "bval b = bval b'" 
  assumes "wp \<pi> c = wp \<pi> c'" 
  assumes "\<pi>: (WHILE b DO c, s) \<Rightarrow> t"
  shows "\<pi>: (WHILE b' DO c', s) \<Rightarrow> t"
  using assms(3,2)
  apply (induction \<pi> "WHILE b DO c" s t)
  apply (auto simp: assms(1))
  by (metis WhileTrue big_step_determ wp_def)
        
lemma sim_while_wp: "bval b = bval b' \<Longrightarrow> wp \<pi> c = wp \<pi> c' \<Longrightarrow> wp \<pi> (WHILE b DO c) = wp \<pi> (WHILE b' DO c')"
  apply (intro ext)
  apply (auto 0 3 simp: wp_def intro: sim_while_wp_aux)
  done

text \<open>The same lemma for weakest liberal preconditions.\<close>  
lemma sim_while_wlp_aux:
  assumes "bval b = bval b'" 
  assumes "wlp \<pi> c = wlp \<pi> c'" 
  assumes "\<pi>: (WHILE b DO c, s) \<Rightarrow> t"
  shows "\<pi>: (WHILE b' DO c', s) \<Rightarrow> t"
  using assms(3,2)
  apply (induction \<pi> "WHILE b DO c" s t)
  apply (auto simp: assms(1,2))
  by (metis WhileTrue wlp_def)
        
lemma sim_while_wlp: "bval b = bval b' \<Longrightarrow> wlp \<pi> c = wlp \<pi> c' \<Longrightarrow> wlp \<pi> (WHILE b DO c) = wlp \<pi> (WHILE b' DO c')"
  apply (intro ext)
  apply (auto 0 3 simp: wlp_def intro: sim_while_wlp_aux)
  done
  
      
subsection \<open>Invariants for While-Loops\<close>
  text \<open>We prove the standard invariant rules for while loops.
    We first prove them in a slightly non-standard form, summarizing the 
    loop step and loop exit assumptions. Then, we derive the standard form 
    with separate assumptions for step and loop exit.
  \<close>
    
  subsubsection \<open>Partial Correctness\<close>
  lemma wlp_whileI':
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp \<pi> c I s else Q s)"
    shows "wlp \<pi> (WHILE b DO c) Q s\<^sub>0"
    unfolding wlp_def
  proof clarify
    fix t
    assume "\<pi>: (WHILE b DO c, s\<^sub>0) \<Rightarrow> t"
    thus "Q t" using INIT STEP
    proof (induction \<pi> "WHILE b DO c" s\<^sub>0 t rule: big_step_induct)
      case (WhileFalse s) with STEP show "Q s" by auto
    next
      case (WhileTrue s\<^sub>1 \<pi> s\<^sub>2 s\<^sub>3)
      note STEP' = WhileTrue.prems(2)
      
      from STEP'[OF \<open>I s\<^sub>1\<close>] \<open>bval b s\<^sub>1\<close> have "wlp \<pi> c I s\<^sub>1" by simp
      with \<open>\<pi>: (c, s\<^sub>1) \<Rightarrow> s\<^sub>2\<close> have "I s\<^sub>2" unfolding wlp_def by blast
      moreover have \<open>I s\<^sub>2 \<Longrightarrow> Q s\<^sub>3\<close> using STEP' WhileTrue.hyps(5) by blast 
      ultimately show "Q s\<^sub>3" by blast
    qed
  qed

  (* Short proof (not the shortest possible one ;) ) *)
  lemma 
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wlp \<pi> c I s else Q s)"
    shows "wlp \<pi> (WHILE b DO c) Q s\<^sub>0"
    using STEP
    unfolding wlp_def
    apply clarify subgoal premises prems for t
      using prems(2,1) INIT
      by (induction \<pi> "WHILE b DO c" s\<^sub>0 t rule: big_step_induct; meson)
    done
    
  subsubsection \<open>Total Correctness\<close>
  text \<open>For total correctness, each step must decrease the state wrt.~a well-founded relation.\<close>
    
  lemma wp_whileI':
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wp \<pi> c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s)"
    shows "wp \<pi> (WHILE b DO c) Q s\<^sub>0"
    using WF INIT 
  proof (induction rule: wf_induct_rule[where a=s\<^sub>0]) (* Instantiation required to avoid strange HO-unification problem! *)
    case (less s)
    show "wp \<pi> (WHILE b DO c) Q s" 
    proof (rule wp_while_unfold[THEN iffD2])
      show "if bval b s then wp \<pi> c (wp \<pi> (WHILE b DO c) Q) s else Q s" 
      proof (split if_split; intro allI impI conjI)
        assume [simp]: "bval b s"
        
        from STEP \<open>I s\<close> have "wp \<pi> c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s" by simp
        thus "wp \<pi> c (wp \<pi> (WHILE b DO c) Q) s" proof (rule wp_conseq)
          fix s' assume "I s' \<and> (s',s)\<in>R"
          with less.IH show "wp \<pi> (WHILE b DO c) Q s'" by blast
        qed
      next
        assume [simp]: "\<not>bval b s"
        from STEP \<open>I s\<close> show "Q s" by simp
      qed
    qed
  qed

  (* Short Proof *)  
  lemma 
    assumes WF: "wf R"
    assumes INIT: "I s\<^sub>0"
    assumes STEP: "\<And>s. I s \<Longrightarrow> (if bval b s then wp \<pi> c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s)"
    shows "wp \<pi> (WHILE b DO c) Q s\<^sub>0"
    using WF INIT 
    apply (induction rule: wf_induct_rule[where a=s\<^sub>0])
    apply (subst wp_while_unfold)
    by (smt STEP wp_conseq)
    
    
  subsubsection \<open>Standard Forms of While Rules\<close>  
  lemma wlp_whileI:
    assumes INIT: "I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk>I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wlp \<pi> c I \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wlp \<pi> (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wlp_whileI' by auto
    
    
  lemma wp_whileI:
    assumes WF: "wf R"
    assumes INIT: "I \<ss>\<^sub>0"
    assumes STEP: "\<And>\<ss>. \<lbrakk>I \<ss>; bval b \<ss> \<rbrakk> \<Longrightarrow> wp \<pi> c (\<lambda>\<ss>'. I \<ss>' \<and> (\<ss>',\<ss>)\<in>R) \<ss>"
    assumes FINAL: "\<And>\<ss>. \<lbrakk> I \<ss>; \<not>bval b \<ss> \<rbrakk> \<Longrightarrow> Q \<ss>"
    shows "wp \<pi> (WHILE b DO c) Q \<ss>\<^sub>0"
    using assms wp_whileI' by auto


subsection \<open>Modularity of Programs\<close>    
text \<open>Adding more procedures does not change the semantics of the existing ones.\<close>

lemma map_leD: "m\<subseteq>\<^sub>mm' \<Longrightarrow> m x = Some v \<Longrightarrow> m' x = Some v"
  by (metis domI map_le_def)
  
lemma big_step_mono_prog:
  assumes "\<pi> \<subseteq>\<^sub>m \<pi>'"  
  assumes "\<pi>:(c,s) \<Rightarrow> t"
  shows "\<pi>':(c,s) \<Rightarrow> t"
  using assms(2,1)
  apply (induction \<pi> c s t rule: big_step_induct)
  by (auto dest: map_leD)
    
  
text \<open>Wrapping a set of recursive procedures into a procedure scope\<close>  
lemma localize_recursion:
  "\<pi>': (PScope \<pi> c, s) \<Rightarrow> t \<longleftrightarrow> \<pi>:(c,s) \<Rightarrow> t"
  by auto
  
  
  
subsection \<open>Strongest Postcondition\<close>  

context fixes \<pi> :: program begin
  definition "sp P c t \<equiv> \<exists>s. P s \<and> \<pi>: (c,s) \<Rightarrow> t"

  context notes [simp] = sp_def[abs_def] begin
  
    text \<open>Intuition: There exists an old value \<open>vx\<close> for the assigned variable\<close>
    lemma sp_arraycpy_eq: "sp P (x[]::=y) t \<longleftrightarrow> (\<exists>vx. let s = t(x:=vx) in t x = s y \<and> P s)" 
      apply (auto simp: big_step_simps)
       apply (intro exI conjI, assumption, auto) []
      apply (intro exI conjI, assumption, auto) []
      done
    
    text \<open>Version with renaming of assigned variable\<close>
    lemma sp_arraycpy_eq': "sp P (x[]::=y) t \<longleftrightarrow> t x = t y \<and> (\<exists>vx. P (t(x:=vx,y:=t x)))" 
      apply (auto simp: big_step_simps)
       apply (metis fun_upd_triv)
      apply (intro exI conjI, assumption) 
      apply auto
      done
      
      
    lemma sp_skip_eq: "sp P SKIP t \<longleftrightarrow> P t" by auto
    lemma sp_seq_eq: "sp P (c\<^sub>1;;c\<^sub>2) t \<longleftrightarrow> sp (sp P c\<^sub>1) c\<^sub>2 t" by auto
    
  end  
end
  
subsection \<open>Hoare-Triples\<close>    

text \<open>A Hoare-triple summarizes the precondition, command, and postcondition.\<close>
        
definition HT 
  where "HT \<pi> P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wp \<pi> c (Q s\<^sub>0) s\<^sub>0)"

definition HT_partial
  where "HT_partial \<pi> P c Q \<equiv> (\<forall>s\<^sub>0. P s\<^sub>0 \<longrightarrow> wlp \<pi> c (Q s\<^sub>0) s\<^sub>0)"

text \<open>Consequence rule---strengthen the precondition, weaken the postcondition.\<close>  
lemma HT_conseq: 
  assumes "HT \<pi> P c Q"
  assumes "\<And>s. P' s \<Longrightarrow> P s"
  assumes "\<And>s\<^sub>0 s. \<lbrakk>P s\<^sub>0; P' s\<^sub>0; Q s\<^sub>0 s \<rbrakk> \<Longrightarrow> Q' s\<^sub>0 s"
  shows "HT \<pi> P' c Q'"
  using assms unfolding HT_def by (blast intro: wp_conseq)

lemma HT_partial_conseq: 
  assumes "HT_partial \<pi> P c Q"
  assumes "\<And>s. P' s \<Longrightarrow> P s"
  assumes "\<And>s\<^sub>0 s. \<lbrakk>P s\<^sub>0; P' s\<^sub>0; Q s\<^sub>0 s \<rbrakk> \<Longrightarrow> Q' s\<^sub>0 s"
  shows "HT_partial \<pi> P' c Q'"
  using assms unfolding HT_partial_def by (blast intro: wlp_conseq)
  
  
text \<open>Simple rule for presentation in lecture: Use a Hoare-triple during VCG.\<close>
lemma wp_modularity_rule:
  "\<lbrakk>HT \<pi> P c Q; P s; (\<And>s'. Q s s' \<Longrightarrow> Q' s')\<rbrakk> \<Longrightarrow> wp \<pi> c Q' s"
  unfolding HT_def
  by (blast intro: wp_conseq)


subsubsection \<open>Sets of Hoare-Triples\<close>  
type_synonym htset = "((state \<Rightarrow> bool) \<times> com \<times> (state \<Rightarrow> state \<Rightarrow> bool)) set"

definition "HTset \<pi> \<Theta> \<equiv> \<forall>(P,c,Q)\<in>\<Theta>. HT \<pi> P c Q"
    
definition "HTset_r r \<pi> \<Theta> \<equiv> \<forall>(P,c,Q)\<in>\<Theta>. HT \<pi> (\<lambda>s. r c s \<and> P s) c Q"
    
subsubsection \<open>Deriving Parameter Frame Adjustment Rules\<close>

text \<open>The following rules can be used to derive Hoare-triples when adding
  prologue and epilogue code, and wrapping the command into a scope.
  
  This will be used to implement the local variables and parameter passing protocol 
  of procedures.
\<close>

text \<open> Intuition: 
  New precondition is weakest one we need to ensure \<open>P\<close> after prologue.
\<close>
lemma adjust_prologue:
  assumes "HT \<pi> P body Q"
  shows "HT \<pi> (wp \<pi> prologue P) (prologue;;body) (\<lambda>s\<^sub>0 s. wp \<pi> prologue (\<lambda>s\<^sub>0. Q s\<^sub>0 s) s\<^sub>0)"
  using assms
  unfolding HT_def
  apply (auto simp: wp_eq)
  using wp_def by fastforce

text \<open> Intuition:
  New postcondition is strongest one we can get from \<open>Q\<close> after epilogue.
  
  We have to be careful with non-terminating epilogue, though!
\<close>  
lemma adjust_epilogue:
  assumes "HT \<pi> P body Q"  
  assumes TERMINATES: "\<forall>s. \<exists>t. \<pi>: (epilogue,s) \<Rightarrow> t"
  shows "HT \<pi> P (body;;epilogue) (\<lambda>s\<^sub>0. sp \<pi> (Q s\<^sub>0) epilogue)"
  using assms
  unfolding HT_def
  apply (simp add: wp_eq)
  apply (force simp: sp_def wp_def)
  done
  
text \<open>Intuition: 
  Scope can be seen as assignment of locals before and after inner command.
  Thus, this rule is a combined forward and backward assignment rule, for
  the epilogue \<open>locals:=<>\<close> and the prologue \<open>locals:=old_locals\<close>.
\<close>  
lemma adjust_scope:
  assumes "HT \<pi> P body Q"
  shows "HT \<pi> (\<lambda>s. P <<>|s>) (SCOPE body) (\<lambda>s\<^sub>0 s. \<exists>l. Q (<<>|s\<^sub>0>) (<l|s>))"
  using assms unfolding HT_def
  apply (auto simp: wp_eq combine_nest)
  apply (auto simp: wp_def) 
  by (metis combine_collapse)

subsubsection \<open>Proof for Recursive Specifications\<close>

text \<open>Prove correct any set of Hoare-triples, e.g., mutually recursive ones.\<close>
lemma HTsetI:    
  assumes "wf R"
  assumes RL: "\<And>P c Q s\<^sub>0. \<lbrakk> HTset_r (\<lambda>c' s'. ((c',s'),(c,s\<^sub>0))\<in>R ) \<pi> \<Theta>; (P,c,Q)\<in>\<Theta>; P s\<^sub>0 \<rbrakk> \<Longrightarrow> wp \<pi> c (Q s\<^sub>0) s\<^sub>0"
  shows "HTset \<pi> \<Theta>"
  unfolding HTset_def HT_def 
proof clarsimp
  fix P c Q s\<^sub>0
  assume "(P,c,Q)\<in>\<Theta>" "P s\<^sub>0"
  with \<open>wf R\<close> show "wp \<pi> c (Q s\<^sub>0) s\<^sub>0"
    apply (induction "(c,s\<^sub>0)" arbitrary: c s\<^sub>0 P Q)
    using RL unfolding HTset_r_def HT_def
    by blast
    
qed  
    

lemma HT_simple_recursiveI:
  assumes "wf R"
  assumes "\<And>s. \<lbrakk>HT \<pi> (\<lambda>s'. (f s', f s)\<in>R \<and> P s') c Q; P s \<rbrakk> \<Longrightarrow> wp \<pi> c (Q s) s"
  shows "HT \<pi> P c Q"
  using HTsetI[where R="inv_image R (f o snd)" and \<pi>=\<pi> and \<Theta> = "{(P,c,Q)}"] assms
  by (auto simp: HTset_r_def HTset_def)


lemma HT_simple_recursive_procI:
  assumes "wf R"
  assumes "\<And>s. \<lbrakk>HT \<pi> (\<lambda>s'. (f s', f s)\<in>R \<and> P s') (PCall p) Q; P s \<rbrakk> \<Longrightarrow> wp \<pi> (PCall p) (Q s) s"
  shows "HT \<pi> P (PCall p) Q"
  using HTsetI[where R="inv_image R (f o snd)" and \<pi>=\<pi> and \<Theta> = "{(P,PCall p,Q)}"] assms
  by (auto simp: HTset_r_def HTset_def)
  
  
    
lemma
  assumes "wf R"
  assumes "\<And>s P p Q. \<lbrakk> 
    \<And>P' p' Q'. (P',p',Q')\<in>\<Theta> 
      \<Longrightarrow> HT \<pi> (\<lambda>s'. ((p',s'),(p,s))\<in>R \<and> P' s') (PCall p') Q';
    (P,p,Q)\<in>\<Theta>; P s 
  \<rbrakk> \<Longrightarrow> wp \<pi> (PCall p) (Q s) s"
  shows "\<forall>(P,p,Q)\<in>\<Theta>. HT \<pi> P (PCall p) Q"  
proof -

  have "HTset \<pi> {(P, PCall p, Q) |P p Q. (P, p, Q) \<in> \<Theta>}"
    apply (rule HTsetI[where R="inv_image R (\<lambda>x. case x of (PCall p,s) \<Rightarrow> (p,s))"])
    subgoal using \<open>wf R\<close> by simp
    subgoal for P c Q s
      apply clarsimp
      apply (rule assms(2)[where P=P])
        apply simp_all
      unfolding HTset_r_def
      proof goal_cases
        case (1 p P' p' Q')
        
        from "1"(1)[rule_format, of "(P',PCall p',Q')", simplified] "1"(2-)
          show ?case by auto
      qed
    done
    
  thus ?thesis by (auto simp: HTset_def)
qed
    

subsection \<open>Completeness of While-Rule\<close>

text \<open>Idea: Use \<open>wlp\<close> as invariant\<close>
lemma wlp_whileI'_complete:
  assumes "wlp \<pi> (WHILE b DO c) Q s\<^sub>0"
  obtains I where
    "I s\<^sub>0"
    "\<And>s. I s \<Longrightarrow> if bval b s then wlp \<pi> c I s else Q s"
proof
  let ?I = "wlp \<pi> (WHILE b DO c) Q"
  {
    show "?I s\<^sub>0" by fact
  next
    fix s
    assume "?I s"
    then show "if bval b s then wlp \<pi> c ?I s else Q s"
      apply (subst (asm) wlp_while_unfold) 
      .
  }  
qed
   
text \<open>Idea: Remaining loop iterations as variant\<close>

inductive count_it for \<pi> b c where
  "\<not>bval b s \<Longrightarrow> count_it \<pi> b c s 0"
| "\<lbrakk>bval b s; \<pi>: (c,s) \<Rightarrow> s'; count_it \<pi> b c s' n \<rbrakk> \<Longrightarrow> count_it \<pi> b c s (Suc n )"  

lemma count_it_determ:
  "count_it \<pi> b c s n \<Longrightarrow> count_it \<pi> b c s n' \<Longrightarrow> n' = n"
  apply (induction arbitrary: n' rule: count_it.induct)
  subgoal using count_it.cases by blast 
  subgoal by (metis big_step_determ count_it.cases)
  done

lemma count_it_ex:   
  assumes "\<pi>: (WHILE b DO c,s) \<Rightarrow> t"
  shows "\<exists>n. count_it \<pi> b c s n"
  using assms
  apply (induction \<pi> "WHILE b DO c" s t arbitrary: b c)
   apply (auto intro: count_it.intros)
  done

definition "variant \<pi> b c s \<equiv> THE n. count_it \<pi> b c s n"  

lemma variant_decreases:
  assumes STEPB: "bval b s" 
  assumes STEPC: "\<pi>: (c,s) \<Rightarrow> s'" 
  assumes TERM: "\<pi>: (WHILE b DO c,s') \<Rightarrow> t"
  shows "variant \<pi> b c s' < variant \<pi> b c s"
proof -
  from count_it_ex[OF TERM] obtain n' where CI': "count_it \<pi> b c s' n'" ..
  moreover from count_it.intros(2)[OF STEPB STEPC this] have "count_it \<pi> b c s (Suc n')" .
  ultimately have "variant \<pi> b c s' = n'" "variant \<pi> b c s = Suc n'" 
    unfolding variant_def using count_it_determ by blast+
  thus ?thesis by simp 
qed

lemma wp_whileI'_complete:
  fixes \<pi> b c
  defines "R\<equiv>measure (variant \<pi> b c)"
  assumes "wp \<pi> (WHILE b DO c) Q s\<^sub>0"
  obtains I where
    "wf R"
    "I s\<^sub>0"
    "\<And>s. I s \<Longrightarrow> if bval b s then wp \<pi> c (\<lambda>s'. I s' \<and> (s',s)\<in>R) s else Q s"
proof   
  show \<open>wf R\<close> unfolding R_def by auto
  let ?I = "wp \<pi> (WHILE b DO c) Q"
  {
    show "?I s\<^sub>0" by fact
  next
    fix s
    assume "?I s"
    then show "if bval b s then wp \<pi> c (\<lambda>s'. ?I s' \<and> (s',s)\<in>R) s else Q s"
      apply (subst (asm) wp_while_unfold) 
      apply clarsimp
      by (auto simp: wp_def R_def intro: variant_decreases)
      
  }  
qed  
    
    
      
  
  
end
                                 