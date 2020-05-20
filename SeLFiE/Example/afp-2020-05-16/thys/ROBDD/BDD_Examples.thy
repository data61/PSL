section\<open>Tests and examples\<close>
theory BDD_Examples
imports Level_Collapse
begin

text\<open>Just two simple examples:\<close>

lemma "<emp> do {
  s \<leftarrow> emptyci;
  (t,s) \<leftarrow> tci s;
  tautci t s
} <\<lambda>r. \<up>(r = True)>\<^sub>t"
by sep_auto

lemma "<emp> do {
  s \<leftarrow> emptyci;
  (a,s) \<leftarrow> litci 0 s;
  (b,s) \<leftarrow> litci 1 s;
  (c,s) \<leftarrow> litci 2 s;
  (t1i,s) \<leftarrow> orci a b s;
  (t1,s) \<leftarrow> andci t1i c s;
  (t2i1,s) \<leftarrow> andci a c s;
  (t2i2,s) \<leftarrow> andci b c s;
  (t2,s) \<leftarrow> orci t2i1 t2i2 s;
  eqci t1 t2
} <\<up>>\<^sub>t"
by sep_auto

end
