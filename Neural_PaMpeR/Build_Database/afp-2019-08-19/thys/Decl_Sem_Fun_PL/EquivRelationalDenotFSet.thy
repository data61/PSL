section "Relational and denotational views are equivalent"

theory EquivRelationalDenotFSet
  imports RelationalSemFSet DeclSemAsDenotFSet
begin
    
lemma denot_implies_rel: "(v \<in> E e \<rho>) \<Longrightarrow> (\<rho> \<turnstile> e \<Rightarrow> v)"
proof (induction e arbitrary: v \<rho>)
 case (EIf e1 e2 e3)
  then show ?case 
    apply simp apply clarify apply (rename_tac n) apply (case_tac n) apply force apply simp
    apply (rule rifnz) apply force+ done
qed auto

lemma rel_implies_denot: "\<rho> \<turnstile> e \<Rightarrow> v \<Longrightarrow> v \<in> E e \<rho>" 
  by (induction \<rho> e v rule: rel_sem.induct) auto

theorem equivalence_relational_denotational: "(v \<in> E e \<rho>) = (\<rho> \<turnstile> e \<Rightarrow> v)"
  using denot_implies_rel rel_implies_denot by blast
  
end
  
