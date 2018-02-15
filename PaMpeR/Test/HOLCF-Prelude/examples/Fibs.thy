theory "Fibs"
  imports
    "../HOLCF_Prelude"
    "../Definedness"
begin

section \<open>Fibonacci sequence\<close>

text \<open>
  In this example, we show that the self-recursive lazy definition of the
  fibonacci sequence is actually defined and correct.
\<close>

fixrec fibs :: "[Integer]" where
  [simp del]: "fibs = 0 : 1 : zipWith\<cdot>(+)\<cdot>fibs\<cdot>(tail\<cdot>fibs)"

fun fib :: "int \<Rightarrow> int" where
  "fib n = (if n \<le> 0 then 0 else if n = 1 then 1 else fib (n - 1) + fib (n - 2))"

declare fib.simps [simp del]

lemma fibs_0 [simp]:
  "fibs !! 0 = 0"
  by (subst fibs.simps) simp

lemma fibs_1 [simp]:
  "fibs !! 1 = 1"
  by (subst fibs.simps) simp

text \<open>And the proof that @{term "fibs !! i"} is defined and the fibs value.\<close>

(* Strange isabelle simplifier bug? *)
lemma [simp]:"-1 + \<lbrakk>i\<rbrakk> = \<lbrakk> i \<rbrakk> - 1" by simp
lemma [simp]:"-2 + \<lbrakk>i\<rbrakk> = \<lbrakk> i \<rbrakk> - 2" by simp

lemma nth_fibs:
  assumes "defined i" and "\<lbrakk> i \<rbrakk> \<ge> 0" shows "defined (fibs !! i)" and "\<lbrakk> fibs !! i \<rbrakk> = fib \<lbrakk> i \<rbrakk>"
  using assms
proof(induction i rule:nonneg_full_Int_induct)
  case (Suc i)
  case 1
  with Suc show ?case
    apply (cases "\<lbrakk>i\<rbrakk> = 0")
     apply (subst fibs.simps, (subst fib.simps)?, simp add: nth_zipWith nth_tail)
    apply (cases "\<lbrakk>i\<rbrakk> = 1")
     apply (subst fibs.simps, (subst fib.simps)?, simp add: nth_zipWith nth_tail)
    apply (subst fibs.simps, (subst fib.simps)?, simp add: nth_zipWith nth_tail)
    done
qed (subst fibs.simps, (subst fib.simps)?, simp add: nth_zipWith nth_tail)+

end