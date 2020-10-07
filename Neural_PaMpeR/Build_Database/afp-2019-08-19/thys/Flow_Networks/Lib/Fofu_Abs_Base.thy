theory Fofu_Abs_Base
imports 
  Complex_Main 
  "HOL-Library.Rewrite"
  Automatic_Refinement.Misc
  Refine_Imperative_HOL.Sepref_Misc
  "Program-Conflict-Analysis.LTS"
begin  

  (* TODO: Move *)
  lemma swap_in_iff_inv: "prod.swap p \<in> S \<longleftrightarrow> p \<in> S\<inverse>"
    apply (cases p) by auto
  
      
(* TODO: Move *)  
lemma length_filter_disj_or_conv:
  assumes "\<And>x. x\<in>set xs \<longrightarrow> \<not>(P x \<and> Q x)"
  shows "length [x \<leftarrow> xs. P x \<or> Q x] = length (filter P xs) + length (filter Q xs)"  
  using assms
  by (induction xs) auto  

(* TODO: Move. Extract an element from a summation, combined with congruence. *)  
lemma sum_arb:
  assumes A_fin: "finite A"
      and x_mem: "x \<in> A" 
      and x_dif: "\<forall>y\<in>A. y \<noteq> x \<longrightarrow> g y = h y"
    shows "(\<Sum>a\<in>A. g a) = (\<Sum>a\<in>A - {x}. h a) + g x"
proof -
  have "A = (A - {x}) \<union> {x}" using x_mem by auto
  moreover note sum.union_disjoint[of "A - {x}" "{x}" g]
  moreover note sum.cong[of "A - {x}" "A - {x}" g h]
  ultimately show ?thesis using A_fin x_dif by auto
qed
  
    
    
    
lemma trcl_cons_conv: 
  "(u,a#xs,v)\<in>trcl R \<longleftrightarrow> (\<exists>uh. (u,a,uh)\<in>R \<and> (uh,xs,v)\<in>trcl R)"
  by (auto dest!: trcl_uncons)
  
lemma trcl_conc_conv: 
  "(u,xs@ys,v)\<in>trcl R \<longleftrightarrow> (\<exists>uh. (u,xs,uh)\<in>trcl R \<and> (uh,ys,v)\<in>trcl R)"    
  by (auto dest!: trcl_unconcat intro: trcl_concat)
  
lemmas trcl_conv = trcl_cons_conv trcl_conc_conv
  \<comment> \<open>Adding these to simpset will split all cons and append operations in paths\<close>

      
      
  
end
