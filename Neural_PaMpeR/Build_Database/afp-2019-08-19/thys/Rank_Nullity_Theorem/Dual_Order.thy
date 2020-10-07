(*  
    Title:      Dual_Order.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)


section "Dual Order"

theory Dual_Order
  imports Main
begin

subsection\<open>Interpretation of dual wellorder based on wellorder\<close>

lemma wf_wellorderI2:
  assumes wf: "wf {(x::'a::ord, y). y < x}"
  assumes lin: "class.linorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
  shows "class.wellorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
  using lin unfolding class.wellorder_def apply (rule conjI)
  apply (rule class.wellorder_axioms.intro) by (blast intro: wf_induct_rule [OF wf])


lemma (in preorder) tranclp_less': "(>)\<^sup>+\<^sup>+ = (>)"
  by(auto simp add: fun_eq_iff intro: less_trans elim: tranclp.induct)

interpretation dual_wellorder: wellorder "(\<ge>)::('a::{linorder, finite}=>'a=>bool)" "(>)" 
proof (rule wf_wellorderI2)
  show "wf {(x :: 'a, y). y < x}"
    by(auto simp add: trancl_def tranclp_less' intro!: finite_acyclic_wf acyclicI)
  show "class.linorder (\<lambda>(x::'a) y::'a. y \<le> x) (\<lambda>(x::'a) y::'a. y < x)"
    unfolding class.linorder_def unfolding class.linorder_axioms_def unfolding class.order_def 
    unfolding class.preorder_def unfolding class.order_axioms_def by auto  
qed

subsection\<open>Properties of the Greatest operator\<close>
  
lemma dual_wellorder_Least_eq_Greatest[simp]: "dual_wellorder.Least = Greatest" 
  by (auto simp add: Greatest_def dual_wellorder.Least_def)

lemmas GreatestI = dual_wellorder.LeastI[unfolded dual_wellorder_Least_eq_Greatest]
lemmas GreatestI2_ex = dual_wellorder.LeastI2_ex[unfolded dual_wellorder_Least_eq_Greatest]
lemmas GreatestI2_wellorder = dual_wellorder.LeastI2_wellorder[unfolded dual_wellorder_Least_eq_Greatest]
lemmas GreatestI_ex = dual_wellorder.LeastI_ex[unfolded dual_wellorder_Least_eq_Greatest]
lemmas not_greater_Greatest = dual_wellorder.not_less_Least[unfolded dual_wellorder_Least_eq_Greatest]
lemmas GreatestI2 = dual_wellorder.LeastI2[unfolded dual_wellorder_Least_eq_Greatest]
lemmas Greatest_ge = dual_wellorder.Least_le[unfolded dual_wellorder_Least_eq_Greatest]

end
