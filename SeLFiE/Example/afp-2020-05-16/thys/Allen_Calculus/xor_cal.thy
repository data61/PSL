(*
Title:  Allen's qualitative temporal calculus
Author:  Fadoua Ghourabi (fadouaghourabi@gmail.com)
Affiliation: Ochanomizu University, Japan
*)

theory xor_cal

imports

  Main

begin
definition xor::"bool \<Rightarrow> bool \<Rightarrow> bool" (infixl "\<oplus>" 60)
where "xor A B \<equiv> (A \<and> \<not>B) \<or> (\<not>A \<and> B)"

declare xor_def [simp]

interpretation bool:semigroup "(\<oplus>) "
proof
{ fix a b c show "a \<oplus> b \<oplus> c = a \<oplus> (b \<oplus> c)" by auto}
qed

lemma xor_distr_L [simp]:"A \<oplus> (B \<oplus> C) = (A\<and>\<not>B\<and>\<not>C)\<or>(A\<and>B\<and>C)\<or>(\<not>A\<and>B\<and>\<not>C)\<or>(\<not>A\<and>\<not>B\<and>C)"
by auto

lemma xor_distr_R [simp]:"(A \<oplus> B) \<oplus> C = A \<oplus> (B \<oplus> C)"
by auto

end
