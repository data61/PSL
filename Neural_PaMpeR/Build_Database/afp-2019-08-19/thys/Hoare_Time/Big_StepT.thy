section "Big Step Semantics with Time"
theory Big_StepT imports Big_Step begin

subsection "Big-Step with Time Semantics of Commands"

inductive
  big_step_t :: "com \<times> state \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"  ("_ \<Rightarrow> _ \<Down> _" 55)
where
Skip: "(SKIP,s) \<Rightarrow> Suc 0 \<Down> s" |
Assign: "(x ::= a,s) \<Rightarrow> Suc 0 \<Down> s(x := aval a s)" |
Seq: "\<lbrakk> (c1,s1) \<Rightarrow> x \<Down> s2;  (c2,s2) \<Rightarrow> y \<Down> s3 ; z=x+y \<rbrakk> \<Longrightarrow> (c1;;c2, s1) \<Rightarrow> z \<Down> s3" |
IfTrue: "\<lbrakk> bval b s;  (c1,s) \<Rightarrow> x \<Down> t; y=x+1 \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c2,s) \<Rightarrow> x \<Down> t; y=x+1  \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> y \<Down> t" |
WhileFalse: "\<lbrakk> \<not>bval b s \<rbrakk> \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> Suc 0 \<Down> s" |
WhileTrue: "\<lbrakk> bval b s1;  (c,s1) \<Rightarrow> x \<Down> s2;  (WHILE b DO c, s2) \<Rightarrow> y \<Down> s3; 1+x+y=z  \<rbrakk> 
    \<Longrightarrow> (WHILE b DO c, s1) \<Rightarrow> z \<Down> s3"


text\<open>We want to execute the big-step rules:\<close>

code_pred big_step_t .

text\<open>For inductive definitions we need command
       \texttt{values} instead of \texttt{value}.\<close>

values "{(t, x). (SKIP, \<lambda>_. 0) \<Rightarrow> x \<Down> t}"

text\<open>We need to translate the result state into a list
to display it.\<close>

values "{map t [''x''] |t x. (SKIP, <''x'' := 42>) \<Rightarrow> x \<Down> t}"

values "{map t [''x''] |t x. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> x \<Down> t}"

values "{map t [''x'',''y''] |t x.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> x \<Down> t}"


text\<open>Proof automation:\<close>
 
declare big_step_t.intros [intro]
  
lemmas big_step_t_induct = big_step_t.induct[split_format(complete)]

subsection "Rule inversion"

text\<open>What can we deduce from @{prop "(SKIP,s) \<Rightarrow> x \<Down> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it:\<close>

inductive_cases Skip_tE[elim!]: "(SKIP,s) \<Rightarrow> x \<Down> t"
thm Skip_tE

text\<open>This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands:\<close>

inductive_cases Assign_tE[elim!]: "(x ::= a,s) \<Rightarrow> p \<Down> t"
thm Assign_tE
inductive_cases Seq_tE[elim!]: "(c1;;c2,s1) \<Rightarrow> p \<Down> s3"
thm Seq_tE
inductive_cases If_tE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> x \<Down> t"
thm If_tE

inductive_cases While_tE[elim]: "(WHILE b DO c,s) \<Rightarrow> x \<Down> t"
thm While_tE
text\<open>Only [elim]: [elim!] would not terminate.\<close>

text\<open>An automatic example:\<close>

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> x \<Down> t \<Longrightarrow> t = s"
by blast

text\<open>Rule inversion by hand via the ``cases'' method:\<close>

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> x \<Down> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  \<comment> \<open>inverting assms\<close>
    case IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_t_simp:
  "(x ::= a,s) \<Rightarrow> Suc 0 \<Down>  s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by (auto)

text \<open>An example combining rule inversion and derivations\<close>
lemma Seq_t_assoc:
  "((c1;; c2;; c3, s) \<Rightarrow> p \<Down>  s') \<longleftrightarrow> ((c1;; (c2;; c3), s) \<Rightarrow> p \<Down> s')"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> p \<Down> s'"
  then obtain s1 s2 p1 p2 p3 where
    c1: "(c1, s) \<Rightarrow> p1 \<Down> s1" and
    c2: "(c2, s1) \<Rightarrow> p2 \<Down> s2" and
    c3: "(c3, s2) \<Rightarrow> p3 \<Down> s'" and
    p: "p = p1 + (p2 + p3)" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> p2 + p3 \<Down>  s'" apply (rule Seq) by simp
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> p \<Down> s'" unfolding p apply (rule Seq) by simp
next
  \<comment> \<open>The other direction is analogous\<close>
  assume "(c1;; (c2;; c3), s) \<Rightarrow> p \<Down> s'"
  then obtain s1 s2 p1 p2 p3 where
    c1: "(c1, s) \<Rightarrow> p1 \<Down> s1" and
    c2: "(c2, s1) \<Rightarrow> p2 \<Down> s2" and
    c3: "(c3, s2) \<Rightarrow> p3 \<Down> s'" and
    p: "p = (p1 + p2) + p3" by auto
  from c1 c2
  have "(c1;; c2, s) \<Rightarrow> p1 + p2 \<Down>  s2" apply (rule Seq) by simp
  from this c3
  show "(c1;; c2;; c3, s) \<Rightarrow> p \<Down> s'" unfolding p apply (rule Seq) by simp
qed


subsection "Relation to Big-Step Semantics"

lemma "(\<exists>p. ((c, s) \<Rightarrow> p \<Down>  s')) = ((c, s) \<Rightarrow> s')"
proof 
    assume "\<exists>p. (c, s) \<Rightarrow> p \<Down> s'"
    then obtain p where "(c, s) \<Rightarrow> p \<Down> s'"
by blast
    then show "((c, s) \<Rightarrow> s')"
      apply(induct c s p s' rule: big_step_t_induct)
        prefer 2 apply(rule Big_Step.Assign)
        apply(auto) done
next
  assume "((c, s) \<Rightarrow> s')"
  then show "(\<exists>p. ((c, s) \<Rightarrow> p \<Down>  s'))"
    apply(induct c s s' rule: big_step_induct)
      by blast+
qed

 
subsection "Execution is deterministic"

text \<open>This proof is automatic.\<close>

theorem big_step_t_determ: "\<lbrakk> (c,s) \<Rightarrow> p \<Down> t; (c,s) \<Rightarrow> q \<Down> u \<rbrakk> \<Longrightarrow> u = t"
  apply (induction arbitrary: u q rule: big_step_t.induct)
  apply blast+ done
 

theorem big_step_t_determ2: "\<lbrakk> (c,s) \<Rightarrow> p \<Down> t; (c,s) \<Rightarrow> q \<Down> u \<rbrakk> \<Longrightarrow> (u = t \<and> p=q)"
  apply  (induction arbitrary: u q rule: big_step_t_induct) 
    apply(elim Skip_tE) apply(simp)
    apply(elim Assign_tE) apply(simp)
  apply blast
    apply(elim If_tE) apply(simp) apply blast
    apply(elim If_tE)  apply blast apply(simp)
    apply(erule While_tE) apply(simp) apply blast
    proof (goal_cases)
      case 1
      from 1(7) show ?case apply(safe) 
        apply(erule While_tE)
          using 1(1-6) apply fast
          using 1(1-6) apply (simp)
        apply(erule While_tE)
          using 1(1-6) apply fast
          using 1(1-6) by (simp)
     qed
         
       
lemma bigstep_det: "(c1, s) \<Rightarrow> p1 \<Down> t1 \<Longrightarrow> (c1, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p1=p \<and> t1=t"
  using big_step_t_determ2 by simp


lemma bigstep_progress: "(c, s) \<Rightarrow> p \<Down> t \<Longrightarrow> p > 0"
apply(induct rule: big_step_t.induct, auto) done

abbreviation terminates ("\<down>") where "terminates cs \<equiv> (\<exists>n a. (cs \<Rightarrow> n \<Down> a))"
abbreviation thestate ("\<down>\<^sub>s") where "thestate cs \<equiv> (THE a. \<exists>n. (cs \<Rightarrow> n \<Down> a))" 
abbreviation thetime ("\<down>\<^sub>t") where "thetime cs \<equiv> (THE n. \<exists>a. (cs \<Rightarrow> n \<Down> a))"  
            
  
lemma bigstepT_the_cost: "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> \<down>\<^sub>t(c, s) = t"
  using bigstep_det by blast 

lemma bigstepT_the_state: "(c, s) \<Rightarrow> t \<Down> s' \<Longrightarrow> \<down>\<^sub>s(c, s) = s'"
  using bigstep_det by blast 


lemma SKIPnot: "(\<not> (SKIP, s) \<Rightarrow> p \<Down> t) = (s\<noteq>t \<or> p\<noteq>Suc 0)" by blast

 
lemma SKIPp: "\<down>\<^sub>t(SKIP,s) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma SKIPt: "\<down>\<^sub>s(SKIP,s) = s"
  apply(rule the_equality)
  apply fast
  apply auto done 


lemma ASSp: "(THE p. Ex (big_step_t (x ::= e, s) p)) = Suc 0"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSt: "(THE t. \<exists>p. (x ::= e, s) \<Rightarrow> p \<Down> t) = s(x := aval e s)"
  apply(rule the_equality)
  apply fast
  apply auto done 

lemma ASSnot: "( \<not> (x ::= e, s) \<Rightarrow> p \<Down> t ) = (p\<noteq>Suc 0 \<or> t\<noteq>s(x := aval e s))"
  apply auto done
       
    
    
lemma If_THE_True: "Suc (THE n. \<exists>a. (c1, s) \<Rightarrow> n \<Down> a) =  (THE n. \<exists>a. (IF b THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a)"
     if T: "bval b s" and c1_t: "terminates (c1,s)" for s l
proof -
  from c1_t obtain p t where a: "(c1, s) \<Rightarrow> p \<Down> t" by blast
  with T have b: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t"  using IfTrue by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c1, s) \<Rightarrow> n \<Down> a) = p" by simp
moreover    
  from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a) = p+1" by simp
ultimately
  show ?thesis by simp
qed

lemma If_THE_False: "Suc (THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a) =  (THE n. \<exists>a. (IF b THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a)"
     if T: "\<not>bval b s" and c2_t: "\<down> (c2,s)" for s l
proof -
  from c2_t obtain p t where a: "(c2, s) \<Rightarrow> p \<Down> t"  by blast
  with T have b: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> p+1 \<Down> t"  using IfFalse by simp
  from a bigstepT_the_cost have "(THE n. \<exists>a. (c2, s) \<Rightarrow> n \<Down> a) = p" by simp
moreover    
  from b bigstepT_the_cost have "(THE n. \<exists>a. (IF b THEN c1 ELSE c2, s) \<Rightarrow> n \<Down> a) = p+1" by simp
ultimately
  show ?thesis by simp
qed
    
  
end
