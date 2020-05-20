section \<open>Trivia\<close>

(*<*)
theory Trivia
imports Main
begin
(*>*)

lemma measure_induct2:
fixes meas :: "'a \<Rightarrow> 'b \<Rightarrow> nat"
assumes "\<And>x1 x2. (\<And>y1 y2. meas y1 y2 < meas x1 x2 \<Longrightarrow> S y1 y2) \<Longrightarrow> S x1 x2"
shows "S x1 x2"
proof-
  let ?m = "\<lambda> x1x2. meas (fst x1x2) (snd x1x2)" let ?S = "\<lambda> x1x2. S (fst x1x2) (snd x1x2)"
  have "?S (x1,x2)"
  apply(rule measure_induct[of ?m ?S])
  using assms by (metis fst_conv snd_conv)
  thus ?thesis by auto
qed

text\<open>Right cons:\<close>

abbreviation Rcons (infix "##" 70) where "xs ## x \<equiv> xs @ [x]"

lemma two_singl_Rcons: "[a,b] = [a] ## b" by auto

(*<*)
end
(*>*)
