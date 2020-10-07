theory ND_Compl_Truthtable_Compact
imports ND_Compl_Truthtable Compactness
begin
  
theorem 
  fixes \<Gamma> :: "'a :: countable formula set"
  shows "\<Gamma> \<TTurnstile> F \<Longrightarrow> \<Gamma> \<turnstile> F"
proof -
  assume \<open>\<Gamma> \<TTurnstile> F\<close>
  with compact_to_formula guess G .
  from ND_complete \<open>\<Turnstile> \<^bold>\<And>G \<^bold>\<rightarrow> F\<close> have \<open>{} \<turnstile> \<^bold>\<And>G \<^bold>\<rightarrow> F\<close> .
  with AssmBigAnd have \<open>set G \<turnstile> F\<close> ..
  with Weaken show ?thesis using \<open>set G \<subseteq> \<Gamma>\<close> .
qed
  

end
