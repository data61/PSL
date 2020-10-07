(*
    Author:     Wenda Li <wl302@cam.ac.uk / liwenda1990@hotmail.com>
*)

section \<open>Some examples of applying the method winding\_eval\<close>

theory Winding_Number_Eval_Examples imports Winding_Number_Eval
begin
  
lemma example1:
  assumes "R>1"
  shows "winding_number (part_circlepath 0 R 0 pi +++ linepath (-R) R) \<i> = 1"
proof (eval_winding,simp_all)
  define CR where  "CR \<equiv>part_circlepath 0 R 0 pi"
  define L where "L\<equiv> linepath (- (complex_of_real R)) R"
  show "\<i> \<notin> path_image CR" unfolding CR_def using \<open>R>1\<close>
    by (intro not_on_circlepathI,auto)  
  show *:"\<i> \<notin> closed_segment (- (of_real R)) R" using \<open>R>1\<close> complex_eq_iff
    by (intro not_on_closed_segmentI,auto)
  from cindex_pathE_linepath[OF this] have "cindex_pathE L \<i> = -1"
    unfolding L_def using \<open>R>1\<close> by auto
  moreover have "cindex_pathE CR \<i> = -1"
    unfolding CR_def using \<open>R>1\<close> 
    apply (subst cindex_pathE_part_circlepath)
    by (simp_all add:jumpF_pathstart_part_circlepath jumpF_pathfinish_part_circlepath)
  ultimately show "- complex_of_real (cindex_pathE CR \<i>) - cindex_pathE L \<i> = 2"
    unfolding L_def CR_def by auto
qed

lemma example2:
  assumes "R>1"
  shows "winding_number (part_circlepath 0 R 0 pi +++ linepath (-R) R) (-\<i>) = 0"
proof (eval_winding,simp_all)
  define CR where  "CR \<equiv>part_circlepath 0 R 0 pi"
  define L where "L\<equiv> linepath (- (complex_of_real R)) R"
  show "-\<i> \<notin> path_image CR" unfolding CR_def using \<open>R>1\<close>
    by (intro not_on_circlepathI,auto)  
  show *:"-\<i> \<notin> closed_segment (- (of_real R)) R" using \<open>R>1\<close> complex_eq_iff
    by (intro not_on_closed_segmentI,auto)
  from cindex_pathE_linepath[OF this] have "cindex_pathE L (-\<i>) = 1"
    unfolding L_def using \<open>R>1\<close> by auto
  moreover have "cindex_pathE CR (-\<i>) = -1"
    unfolding CR_def using \<open>R>1\<close> 
    apply (subst cindex_pathE_part_circlepath)
    by (simp_all add:jumpF_pathstart_part_circlepath jumpF_pathfinish_part_circlepath)
  ultimately show "-cindex_pathE CR (-\<i>) = cindex_pathE L (-\<i>)"
    unfolding L_def CR_def by auto    
qed
 
lemma example3:
  fixes lb ub z :: complex
  defines "rec \<equiv>  linepath lb (Complex (Re ub) (Im lb)) +++ linepath (Complex (Re ub) (Im lb)) ub 
              +++ linepath ub (Complex (Re lb) (Im ub)) +++ linepath (Complex (Re lb) (Im ub)) lb"
  assumes order_asms:"Re lb < Re z" "Re z < Re ub" "Im lb < Im z" "Im z < Im ub"
  shows "winding_number rec z = 1"
  unfolding rec_def
proof (eval_winding)    
  let ?l1 = "linepath lb (Complex (Re ub) (Im lb))"
  and ?l2 = "linepath (Complex (Re ub) (Im lb)) ub"
  and ?l3 = "linepath ub (Complex (Re lb) (Im ub))"
  and ?l4 = "linepath (Complex (Re lb) (Im ub)) lb"
  show l1: "z \<notin> path_image ?l1" 
    apply (auto intro!: not_on_closed_segmentI_complex)
    using order_asms by (metis diff_gt_0_iff_gt mult_pos_pos order.asym zero_less_mult_pos2)
  show l2:"z \<notin> path_image ?l2" 
    apply (auto intro!: not_on_closed_segmentI_complex)      
    using order_asms by (metis diff_gt_0_iff_gt linordered_field_class.sign_simps(44) order.asym)
  show l3:"z \<notin> path_image ?l3" 
    apply (auto intro!: not_on_closed_segmentI_complex)      
    using order_asms by (metis diff_less_0_iff_less linordered_field_class.sign_simps(44) order.asym)
  show l4:"z \<notin> path_image ?l4"  
    apply (auto intro!: not_on_closed_segmentI_complex)      
    using order_asms by (metis diff_less_0_iff_less linordered_field_class.sign_simps(44) order.asym)
  show "- complex_of_real (cindex_pathE ?l1 z + (cindex_pathE ?l2 z + (cindex_pathE ?l3 z +
          cindex_pathE ?l4 z))) = 2 * 1"  
  proof -
    have "(Im z - Im ub) * (Re ub - Re lb) < 0" 
      using mult_less_0_iff order_asms(1) order_asms(2) order_asms(4) by fastforce
    then have "cindex_pathE ?l3 z = -1"
      apply (subst cindex_pathE_linepath)
      using l3 order_asms by (auto simp add:algebra_simps)
    moreover have "(Im lb - Im z) * (Re ub - Re lb) <0" 
      using mult_less_0_iff order_asms(1) order_asms(2) order_asms(3) by fastforce
    then have "cindex_pathE ?l1 z = -1"    
      apply (subst cindex_pathE_linepath)
      using l1 order_asms by (auto simp add:algebra_simps)  
    moreover have "cindex_pathE ?l2 z = 0"    
      apply (subst cindex_pathE_linepath)
      using l2 order_asms by (auto simp add:algebra_simps)  
    moreover have "cindex_pathE ?l4 z = 0"
      apply (subst cindex_pathE_linepath)
      using l4 order_asms by (auto simp add:algebra_simps) 
    ultimately show ?thesis by auto
  qed
qed
   
end
