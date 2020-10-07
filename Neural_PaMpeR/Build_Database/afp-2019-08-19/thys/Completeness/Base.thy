section "Base"

theory Base
imports PermutationLemmas
begin

subsection "Integrate with Isabelle libraries?"

    \<comment> \<open>Misc\<close>

  \<comment> \<open>FIXME added by tjr, forms basis of a lot of proofs of existence of inf sets\<close>
  \<comment> \<open>something like this should be in FiniteSet, asserting nats are not finite\<close>
lemma natset_finite_max: assumes a: "finite A"
  shows "Suc (Max A) \<notin> A"
proof (cases "A = {}")
  case True
  thus ?thesis by auto
next
  case False
  with a have "Max A \<in> A \<and> (\<forall>s \<in> A. s \<le> Max A)" by simp
  thus ?thesis by auto
qed

    \<comment> \<open>not used\<close>
lemma not_finite_univ: "~ finite (UNIV::nat set)"
  apply rule
  apply(drule_tac natset_finite_max)
  by force

  \<comment> \<open>FIXME should be in main lib\<close>
lemma LeastI_ex: "(\<exists> x. P (x::'a::wellorder)) \<Longrightarrow> P (LEAST x. P x)"
  by(blast intro: LeastI)


subsection "Summation"

primrec summation :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat"
where
  "summation f 0 = f 0"
| "summation f (Suc n) = f (Suc n) + summation f n"


subsection "Termination Measure"

primrec exp :: "[nat,nat] \<Rightarrow> nat"
where
  "exp x 0       = 1"
| "exp x (Suc m) = x * exp x m"

primrec sumList     :: "nat list \<Rightarrow> nat"
where
  "sumList []     = 0"
| "sumList (x#xs) = x + sumList xs"


subsection "Functions"

definition
  preImage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b set \<Rightarrow> 'a set" where
  "preImage f A = { x . f x \<in> A}"

definition
  pre :: "('a \<Rightarrow> 'b) => 'b \<Rightarrow> 'a set" where
  "pre f a = { x . f x = a}"

definition
  equalOn :: "['a set,'a => 'b,'a => 'b] => bool" where
  "equalOn A f g = (!x:A. f x = g x)"    

lemma preImage_insert: "preImage f (insert a A) = pre f a Un preImage f A"
  by(auto simp add: preImage_def pre_def)

lemma preImageI: "f x : A ==> x : preImage f A"
  by(simp add: preImage_def)
    
lemma preImageE: "x : preImage f A ==> f x : A"
  by(simp add: preImage_def)

lemma equalOn_Un:  "equalOn (A \<union> B) f g = (equalOn A f g \<and> equalOn B f g)"
  by(auto simp add: equalOn_def) 

lemma equalOnD: "equalOn A f g \<Longrightarrow> (\<forall> x \<in> A . f x = g x)"
  by(simp add: equalOn_def)

lemma equalOnI:"(\<forall> x \<in> A . f x = g x) \<Longrightarrow> equalOn A f g"
  by(simp add: equalOn_def)

lemma equalOn_UnD: "equalOn (A Un B) f g ==> equalOn A f g & equalOn B f g"
  by(auto simp: equalOn_def)


    \<comment> \<open>FIXME move following elsewhere?\<close>
lemma inj_inv_singleton[simp]: "\<lbrakk> inj f; f z = y \<rbrakk> \<Longrightarrow> {x. f x = y} = {z}"
  apply rule
  apply(auto simp: inj_on_def) done

lemma finite_pre[simp]: "inj f \<Longrightarrow> finite (pre f x)"
  apply(simp add: pre_def) 
  apply (cases "\<exists> y. f y = x", auto) done

lemma finite_preImage[simp]: "\<lbrakk> finite A; inj f \<rbrakk> \<Longrightarrow> finite (preImage f A)"
  apply(induct A rule: finite_induct) 
  apply(simp add: preImage_def)
  apply(simp add: preImage_insert) done


end
