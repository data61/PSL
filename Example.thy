(* This file, Example.thy, contains small examples, including Example2 presented in the FM2016 draft. *)
theory Example
imports PSL "~~/src/HOL/Eisbach/Eisbach"
begin

method my_simp = simp

strategy UserSimp = User< my_simp >
lemma "True \<and> True \<or> False"
find_proof UserSimp
oops

method test_match =(match premises in I: "Q \<longrightarrow> A" and I':"Q" for Q A \<Rightarrow>
   \<open>match conclusion in A \<Rightarrow> \<open>rule mp [OF I I']\<close>\<close>)

lemma "\<And> P. Q \<longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P"
by (match premises in I: "Q \<longrightarrow> A" and I':"Q" for A \<Rightarrow>
   \<open>match conclusion in A \<Rightarrow> \<open>rule mp [OF I I']\<close>\<close>)

method if_match = (match conclusion in "((P::'a \<Rightarrow> 'b) = (Q::'a \<Rightarrow> 'b))" for P Q \<Rightarrow> \<open>succeed\<close>)
method extI =  (rule ext)
method if_match2 = (match conclusion in "((P::'a) = (Q::'a))" for P Q \<Rightarrow> \<open>succeed\<close>)

strategy IfMatch  = Thens [User <if_match>, Skip]
strategy IfMatch2 = Thens [User <if_match>, User <succeed>]
strategy IfMatch3 = Thens [User <if_match>, Rule]
strategy IfMatch4 = Thens [User <if_match>, User < rule >]
strategy IfMatch5 = Thens [Skip, User <succeed>]
strategy IfMatch6 = Thens [Skip, User < if_match >, Skip]
strategy IfMatch7 = Thens [User <succeed>, Skip]
strategy IfMatch8 = Alts [User <succeed>, User <succeed>]

consts "QQ"::"'a \<Rightarrow> 'b"
consts "PP"::"'a \<Rightarrow> 'b"

lemma "(QQ = PP)"
find_proof IfMatch
find_proof IfMatch2
find_proof IfMatch3
find_proof IfMatch4
find_proof IfMatch5
find_proof IfMatch6
find_proof IfMatch7
find_proof IfMatch8
apply(if_match)
oops

definition "my_foo \<equiv> True"
thm my_foo_def(1)

strategy UserSimp2 = Thens [User < simp add: my_foo_def(1) >, IsSolved]
lemma "my_foo"
find_proof UserSimp2
oops

strategy Hammer = Hammer
lemma "True \<or> False"
find_proof Hammer
oops

strategy FFporHam = POrs [Fastforce, Hammer]

lemma
 assumes "P"
 shows "P"
find_proof FFporHam
oops

strategy FFpaltHam = Thens [PAlts [Fastforce, Hammer], IsSolved]

lemma
 assumes "P"
 shows "P"
find_proof FFpaltHam
oops

strategy MultiFF = Thens [Fastforce, IsSolved, Fastforce, IsSolved]
lemma "True" and "True"
apply -
subgoal
find_proof MultiFF
oops

strategy Auto2 = Thens [Subgoal, Auto, IsSolved, Subgoal, Auto, IsSolved]
lemma "True" and "True"
find_proof Auto2
oops

inductive foo::"'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "foo x y"

(* You can use the default strategy with a single command "try_hard".*)
lemma "foo 8 90"
find_proof Hammer
apply -
oops

definition "my_true = True"
lemma my_truth: "my_true \<and> True"
try_hard
apply -
oops

lemma assumes D shows "B \<longrightarrow> B \<or> C" and "D" and "D"
try_hard
apply -
oops

strategy my_strategy = Thens [Skip, Alts [Fail, Ors [Fail, Hammer]]]

lemma
  assumes "B"
  shows "B \<and> (True \<or> False)"
find_proof my_strategy
apply -
oops

strategy Simps =  RepeatN ( Ors [Simp, Defer] )

lemma shows "True" and "False" and "True" and "True"
find_proof Simps
apply -
oops

(* By deferring non-sledgehammable proof obligations, human engineers can focus on meaningful
 * parts of their problems. *)
strategy Hammers =  RepeatN ( Ors [Hammer, Defer]  )

(* A radically simplified example. *)
definition "safe_state x y \<equiv> True"
lemma state_safety:"safe_state (x::bool) (y::bool) = True"
apply normalization done

definition "ps_safe (x::bool) (y::bool) \<equiv> safe_state True True"
definition "valid_trans p s s' x \<equiv> True"

lemma cnjct2: 
shows 1:"ps_safe p s"
 and  2:"valid_trans p s s' x"
 and  3:"ps_safe p s'"
find_proof Hammers
apply -
oops

lemma "x \<or> True" and "(1::int) > 0"
try_hard
apply -
oops

strategy testCut = Thens [Repeat (Cut 10 (Dynamic (Rule))), IsSolved]
lemma "True \<and> True"
find_proof testCut
oops

lemma "True \<equiv> True"
thm meta_eq_to_obj_eq
find_theorems "?x \<equiv> ?y" "?x = ?y" name:"meta"
apply auto done

end