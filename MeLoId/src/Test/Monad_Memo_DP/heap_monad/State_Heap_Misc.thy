subsection \<open>Miscellaneous Parametricity Theorems\<close>

theory State_Heap_Misc
  imports Main
begin
context  includes lifting_syntax begin
lemma rel_fun_comp:
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h"
  shows "(R1 OO R2 ===> S1 OO S2) f h"
  using assms by (auto intro!: rel_funI dest!: rel_funD)

lemma rel_fun_comp1:
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "R' = R1 OO R2"
  shows "(R' ===> S1 OO S2) f h"
  using assms rel_fun_comp by metis

lemma rel_fun_comp2:
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "S' = S1 OO S2"
  shows "(R1 OO R2 ===> S') f h"
  using assms rel_fun_comp by metis

lemma rel_fun_relcompp:
  "((R1 ===> S1) OO (R2 ===> S2)) a b \<Longrightarrow> ((R1 OO R2) ===> (S1 OO S2)) a b"
  unfolding OO_def rel_fun_def by blast

lemma rel_fun_comp1':
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "\<And> a b. R' a b \<Longrightarrow> (R1 OO R2) a b"
  shows "(R' ===> S1 OO S2) f h"
  by (auto intro: assms rel_fun_mono[OF rel_fun_comp1])

lemma rel_fun_comp2':
  assumes "(R1 ===> S1) f g" "(R2 ===> S2) g h" "\<And> a b. (S1 OO S2) a b \<Longrightarrow> S' a b"
  shows "(R1 OO R2 ===> S') f h"
  by (auto intro: assms rel_fun_mono[OF rel_fun_comp1])

end
end