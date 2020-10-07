(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

section "Properties of Tame Graph Enumeration (2)"

theory TameEnumProps
imports GeneratorProps
begin


text\<open>Completeness of filter for final graphs.\<close>

lemma untame_negFin:
assumes pl: "inv g" and fin: "final g" and tame: "tame g"
shows "is_tame g"
proof (unfold is_tame_def, intro conjI)
  show "tame10 g" using tame by(auto simp:tame_def)
next
  show "tame11a g" using tame by(auto simp:tame_def)
next
  show "tame12o g" using tame by(auto simp:tame_def)
next
next
  from tame obtain w where adm: "admissible w g"
    and sqn: "(\<Sum>\<^bsub>f \<in> faces g\<^esub> w f) < squanderTarget" by(auto simp:tame_def tame13a_def)
  moreover have "squanderLowerBound g \<le>  (\<Sum>\<^bsub>f \<in> faces g\<^esub> w f)"
    using pl fin tame adm sqn by (rule total_weight_lowerbound)
  ultimately show "is_tame13a g" by(auto simp:is_tame13a_def)
qed


lemma next_tame_comp:
 "\<lbrakk> tame g; final g; Seed\<^bsub>p\<^esub> [next_tame0 p]\<rightarrow>* g \<rbrakk>
 \<Longrightarrow> Seed\<^bsub>p\<^esub> [next_tame\<^bsub>p\<^esub>]\<rightarrow>* g"
apply (unfold next_tame_def)
apply(rule filter_tame_succs[OF inv_inv_next_tame0])
     apply(simp add:next_tame0_def finalGraph_def)
    apply(rule context_conjI)
     apply(simp)
    apply(blast dest:untame_negFin)
   apply assumption
  apply(rule inv_Seed)
 apply assumption+
done


end
