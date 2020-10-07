section \<open>Assertions, commands, and separation logic proof rules\<close>

theory Ribbons_Basic imports 
  Main 
begin 

text \<open>We define a command language, assertions, and the rules of separation
  logic, plus some derived rules that are used by our tool. This is the only 
  theory file that is loaded by the tool. We keep it as small as possible. 
\<close>

subsection \<open>Assertions\<close>

text \<open>The language of assertions includes (at least) an emp constant, 
  a star-operator, and existentially-quantified logical variables.\<close>

typedecl assertion

axiomatization
  Emp :: "assertion"

axiomatization
  Star :: "assertion \<Rightarrow> assertion \<Rightarrow> assertion" (infixr "\<star>" 55)
where
  star_comm: "p \<star> q = q \<star> p" and 
  star_assoc: "(p \<star> q) \<star> r = p \<star> (q \<star> r)" and 
  star_emp: "p \<star> Emp = p" and
  emp_star: "Emp \<star> p = p"

lemma star_rot: 
  "q \<star> p \<star> r = p \<star> q \<star> r" 
using star_assoc star_comm by auto

axiomatization 
  Exists :: "string \<Rightarrow> assertion \<Rightarrow> assertion"

text \<open>Extracting the set of program variables mentioned in an assertion.\<close>
axiomatization 
  rd_ass :: "assertion \<Rightarrow> string set"
where rd_emp: "rd_ass Emp = {}"
  and rd_star: "rd_ass (p \<star> q) = rd_ass p \<union> rd_ass q"
  and rd_exists: "rd_ass (Exists x p) = rd_ass p"

subsection \<open>Commands\<close>

text \<open>The language of commands comprises (at least) non-deterministic 
  choice, non-deterministic looping, skip and sequencing.\<close>

typedecl command

axiomatization 
  Choose :: "command \<Rightarrow> command \<Rightarrow> command"

axiomatization 
  Loop :: "command \<Rightarrow> command"

axiomatization 
  Skip :: "command"

axiomatization
  Seq :: "command \<Rightarrow> command \<Rightarrow> command" (infixr ";;" 55)
where seq_assoc: "c1 ;; (c2 ;; c3) = (c1 ;; c2) ;; c3"
  and seq_skip: "c ;; Skip = c"
  and skip_seq: "Skip ;; c = c"

text \<open>Extracting the set of program variables read by a command.\<close>
axiomatization
  rd_com :: "command \<Rightarrow> string set"
where rd_com_choose: "rd_com (Choose c1 c2) = rd_com c1 \<union> rd_com c2"
  and rd_com_loop: "rd_com (Loop c) = rd_com c"
  and rd_com_skip: "rd_com (Skip) = {}"
  and rd_com_seq: "rd_com (c1 ;; c2) = rd_com c1 \<union> rd_com c2"

text \<open>Extracting the set of program variables written by a command.\<close>
axiomatization
  wr_com :: "command \<Rightarrow> string set"
where wr_com_choose: "wr_com (Choose c1 c2) = wr_com c1 \<union> wr_com c2"
  and wr_com_loop: "wr_com (Loop c) = wr_com c"
  and wr_com_skip: "wr_com (Skip) = {}"
  and wr_com_seq: "wr_com (c1 ;; c2) = wr_com c1 \<union> wr_com c2"

subsection \<open>Separation logic proof rules\<close>

text \<open>Note that the frame rule has a side-condition concerning program
  variables. When proving the soundness of our graphical formalisation of
  ribbon proofs, we shall omit this side-condition.\<close>

inductive
  prov_triple :: "assertion \<times> command \<times> assertion \<Rightarrow> bool"
where
  exists: "prov_triple (p, c, q) \<Longrightarrow> prov_triple (Exists x p, c, Exists x q)"
| choose: "\<lbrakk> prov_triple (p, c1, q); prov_triple (p, c2, q) \<rbrakk> 
  \<Longrightarrow> prov_triple (p, Choose c1 c2, q)"
| loop: "prov_triple (p, c, p) \<Longrightarrow> prov_triple (p, Loop c, p)" 
| frame: "\<lbrakk> prov_triple (p, c, q); wr_com(c) \<inter> rd_ass(r) = {} \<rbrakk> 
  \<Longrightarrow> prov_triple (p \<star> r, c, q \<star> r)"
| skip: "prov_triple (p, Skip, p)"
| seq: "\<lbrakk> prov_triple (p, c1, q); prov_triple (q, c2, r) \<rbrakk> 
  \<Longrightarrow> prov_triple (p, c1 ;; c2, r)"

text \<open>Here are some derived proof rules, which are used in our 
  ribbon-checking tool.\<close>

lemma choice_lemma:
  assumes "prov_triple (p1, c1, q1)" and "prov_triple (p2, c2, q2)"
    and "p = p1" and "p1 = p2" and "q = q1" and "q1 = q2"
  shows "prov_triple (p, Choose c1 c2, q)"
using assms prov_triple.choose by auto

lemma loop_lemma:
  assumes "prov_triple (p1, c, q1)" and "p = p1" and "p1 = q1" and "q1 = q"
  shows "prov_triple (p, Loop c, q)"
using assms prov_triple.loop by auto

lemma seq_lemma:
  assumes "prov_triple (p1, c1, q1)" and "prov_triple (p2, c2, q2)" 
    and "q1 = p2"
  shows "prov_triple (p1, c1 ;; c2, q2)"
using assms prov_triple.seq by auto

end
