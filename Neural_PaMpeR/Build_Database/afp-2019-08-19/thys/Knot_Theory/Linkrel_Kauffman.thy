section\<open>Tangle moves and Kauffman bracket\<close>

theory Linkrel_Kauffman 
imports Computations
begin 


lemma mat1_vert_wall_left: 
assumes "is_tangle_diagram b"
shows
"rat_poly.matrix_mult  (blockmat (make_vert_block (nat (domain_wall b)))) (kauff_mat b)
             = (kauff_mat b)"
proof-
 have "mat (2^(nat (domain_wall b))) (length (kauff_mat b)) (kauff_mat b)"  
           by (metis assms matrix_kauff_mat) 
 moreover have "(blockmat (make_vert_block (nat (domain_wall b))))
                       = mat1 (2^(nat (domain_wall b)))"
               using make_vert_block_map_blockmat by auto
 ultimately show ?thesis by (metis blockmat_make_vert mat1_mult_left prop_make_vert_equiv(1))
qed 

lemma mat1_vert_wall_right: 
assumes "is_tangle_diagram b"
shows
"rat_poly.matrix_mult  (kauff_mat b) (blockmat (make_vert_block (nat (codomain_wall b))))
             = (kauff_mat b)"
proof-
 have "mat (rat_poly.row_length (kauff_mat b)) (2^(nat (codomain_wall b))) (kauff_mat b)"  
           by (metis assms matrix_kauff_mat) 
 moreover have "(blockmat (make_vert_block (nat (codomain_wall b))))
                       = mat1 (2^(nat (codomain_wall b)))"
          using make_vert_block_map_blockmat by auto
 ultimately show ?thesis by (metis mat1_rt_mult)
qed 

lemma compress_top_inv:"(compress_top w1 w2) \<Longrightarrow> kauff_mat w1 = kauff_mat w2"
proof-
 assume assm:"compress_top w1 w2"
 have " \<exists>B.((w1 = (basic (make_vert_block (nat (domain_wall B))))\<circ> B)
                              \<and>(w2 = (B \<circ> (basic ([]))))\<and>(codomain_wall B = 0)
          \<and>(is_tangle_diagram B))"
        using compress_top_def assm by auto
 then obtain B where "(w1 = (basic (make_vert_block (nat (domain_wall B))))\<circ> B)
                              \<and>(w2 = (B \<circ> (basic ([]))))\<and>(codomain_wall B = 0)\<and>(is_tangle_diagram B)"
        by auto
 then have 1:"(w1 = (basic (make_vert_block (nat (domain_wall B))))\<circ> B)
                         \<and>(w2 = (B \<circ> (basic ([]))))\<and>(codomain_wall B = 0)\<and>(is_tangle_diagram B)"
        by auto
 then have "kauff_mat(w1) = (kauff_mat ((basic (make_vert_block (nat (domain_wall B))))\<circ> B))"
        by auto
 moreover then have "... = kauff_mat ((make_vert_block (nat (domain_wall B)))*B)"
        by auto
 moreover then have "... = rat_poly.matrix_mult (blockmat (make_vert_block (nat (domain_wall B))))
                                    (kauff_mat B)"
        by auto
 moreover then have "... = (kauff_mat B)" 
        using 1 mat1_vert_wall_left by (metis)
 ultimately have "kauff_mat(w1) = kauff_mat B"
        by auto
 moreover have "kauff_mat w2 = kauff_mat B"
        using 1 by (metis left_mat_compose)
 ultimately show ?thesis by auto
qed

lemma domain_make_vert_int:"(n \<ge> 0) \<Longrightarrow> (domain_block (make_vert_block (nat n)))
                      = n"
 using domain_make_vert by auto

lemma compress_bottom_inv:"(compress_bottom w1 w2) \<Longrightarrow> kauff_mat w1 = kauff_mat w2"
proof-
 assume assm:"compress_bottom w1 w2"
 have "\<exists>B.((w1 = B \<circ> (basic (make_vert_block (nat (codomain_wall B)))))
                              \<and>(w2 = ((basic ([]) \<circ> B)))\<and>(domain_wall B = 0)
                               \<and>(is_tangle_diagram B))"
     using compress_bottom_def assm by auto
 then obtain B where "((w1 = B \<circ> (basic (make_vert_block (nat (codomain_wall B)))))
                              \<and>(w2 = ((basic ([]) \<circ> B)))\<and>(domain_wall B = 0)
                               \<and>(is_tangle_diagram B))"
     by auto
 then have 1:"((w1 = B \<circ> (basic (make_vert_block (nat (codomain_wall B)))))
                              \<and>(w2 = ((basic ([]) \<circ> B)))\<and>(domain_wall B = 0)
                               \<and>(is_tangle_diagram B))"
     by auto
 then have "kauff_mat(w1) = (kauff_mat ( B \<circ> (basic (make_vert_block (nat (codomain_wall B))))))"
     by auto
  moreover then have "... = rat_poly.matrix_mult (kauff_mat B)
                                    (kauff_mat (basic (make_vert_block (nat (codomain_wall B)))))"
  proof-
   have "is_tangle_diagram B"
         using 1 by auto
   moreover have "is_tangle_diagram  (basic (make_vert_block (nat (codomain_wall B))))"
         using is_tangle_diagram.simps by auto
   moreover have "codomain_wall B = domain_wall (basic (make_vert_block (nat (codomain_wall B))))"
   proof-
    have "codomain_wall B \<ge> 0"
     apply (induct B) 
     by (auto) (metis codomain_block_nonnegative)
    then have "domain_block (make_vert_block (nat (codomain_wall B)))
                     = codomain_wall B"
              using domain_make_vert_int by auto
    then show ?thesis unfolding domain_wall.simps(1)  by auto
   qed
  ultimately show ?thesis using tangle_compose_matrix by auto
 qed    
 moreover then have  "... = rat_poly.matrix_mult (kauff_mat B)
                                    (blockmat (make_vert_block (nat (codomain_wall B))))"
     using kauff_mat.simps(1) tangle_compose_matrix  by auto     
 moreover then have "... = (kauff_mat B)" 
     using 1 mat1_vert_wall_right by auto        
 ultimately have "kauff_mat(w1) = kauff_mat B"
     by auto
 moreover have "kauff_mat w2 = kauff_mat B"
     using 1 by (metis right_mat_compose)
 ultimately show ?thesis by auto
qed



theorem compress_inv:"compress w1 w2 \<Longrightarrow> (kauff_mat w1 = kauff_mat w2)"
 unfolding compress_def using compress_bottom_inv compress_top_inv
 by auto

lemma striaghten_topdown_computation:"kauff_mat ((basic ([vert,cup]))\<circ>(basic ([cap,vert])))
                  =  kauff_mat ((basic ([vert]))\<circ>(basic ([vert])))"
 apply(simp add:kauff_mat_def)
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply (auto simp add:inverse1 inverse2)
 done

theorem straighten_topdown_inv:"straighten_topdown w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding straighten_topdown_def using striaghten_topdown_computation by auto

lemma striaghten_downtop_computation:"kauff_mat ((basic ([cup,vert]))\<circ>(basic ([vert,cap])))
                  =  kauff_mat ((basic ([vert]))\<circ>(basic ([vert])))"
 apply(simp add:kauff_mat_def)
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply (auto simp add:inverse1 inverse2)
 done

theorem straighten_downtop_inv:"straighten_downtop w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding straighten_downtop_def using striaghten_downtop_computation by auto
      
theorem straighten_inv:"straighten w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding straighten_def using straighten_topdown_inv straighten_downtop_inv by auto

(*swing relations*)

lemma kauff_mat_swingpos:
 "kauff_mat (r_over_braid) = kauff_mat (l_over_braid)"
 apply (simp)
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(auto simp add:computation_swingpos)
 done

lemma swing_pos_inv:"swing_pos w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding swing_pos_def using kauff_mat_swingpos by auto


lemma kauff_mat_swingneg:
"kauff_mat (r_under_braid) = kauff_mat (l_under_braid)"
 apply (simp)
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(auto simp add:computation_swingneg)
 done

lemma swing_neg_inv:"swing_neg w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding swing_neg_def using kauff_mat_swingneg by auto

theorem swing_inv:
"swing w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding swing_def using swing_pos_inv swing_neg_inv by auto

lemma rotate_toppos_kauff_mat:"kauff_mat ((basic [vert,over])\<circ>(basic [cap, vert])) 
                      =  kauff_mat ((basic [under,vert])\<circ>(basic [vert,cap]))"
 apply (simp)
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(simp add:computation_toppos)
 done
 
lemma rotate_toppos_inv:"rotate_toppos w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding rotate_toppos_def using rotate_toppos_kauff_mat by auto

lemma rotate_topneg_kauff_mat:"kauff_mat ((basic [vert,under])\<circ>(basic [cap, vert])) 
                      =  kauff_mat ((basic [over,vert])\<circ>(basic [vert,cap]))"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(simp add:computation_toppos)
 done 

lemma rotate_topneg_inv:"rotate_topneg w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding rotate_topneg_def using rotate_topneg_kauff_mat by auto

lemma rotate_downpos_kauff_mat:
 "kauff_mat ((basic [cup,vert])\<circ>(basic [vert,over]))= kauff_mat ((basic [vert,cup])\<circ>(basic [under,vert]))"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(simp add:computation_downpos)  
 done     


lemma rotate_downpos_inv:"rotate_downpos w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding rotate_downpos_def using rotate_downpos_kauff_mat by auto


lemma rotate_downneg_kauff_mat:
 "kauff_mat ((basic [cup,vert])\<circ>(basic [vert,under]))= kauff_mat ((basic [vert,cup])\<circ>(basic [over,vert]))"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 apply(simp add:computation_downpos)  
 done     


lemma rotate_downneg_inv:"rotate_downneg w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding rotate_downneg_def using rotate_downneg_kauff_mat by auto

(*the matrix is an invariant under rotation *)
theorem rotate_inv:"rotate w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding rotate_def using rotate_downneg_inv rotate_downpos_inv rotate_topneg_inv   
           rotate_toppos_inv by auto

(*framed_uncross begins*)


lemma positive_flip_kauff_mat:
 "kauff_mat (left_over) = kauff_mat (right_over)"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 using computatition_positive_flip apply auto[1]
 using computatition_positive_flip by auto     

lemma uncross_positive_flip_inv: "uncross_positive_flip w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding uncross_positive_flip_def using  positive_flip_kauff_mat by auto


lemma negative_flip_kauff_mat: "kauff_mat (left_under) = kauff_mat (right_under)"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)  
 using computation_negative_flip apply auto
 done

lemma uncross_negative_flip_inv: "uncross_negative_flip w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding uncross_negative_flip_def using  negative_flip_kauff_mat by auto

theorem framed_uncross_inv:"(framed_uncross w1 w2) \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding framed_uncross_def using uncross_negative_flip_inv uncross_positive_flip_inv
 by auto

(*pull begins here*)

lemma  pos_neg_kauff_mat:
"kauff_mat ((basic [over]) \<circ> (basic [under])) 
                    = kauff_mat ((basic [vert,vert]) \<circ> (basic [vert,vert])) "
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply(auto simp add:inverse1 inverse2)
 apply(auto simp add:computation_pull_pos_neg)
 done 


lemma pull_posneg_inv: "pull_posneg w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding pull_posneg_def using  pos_neg_kauff_mat by auto

lemma  neg_pos_kauff_mat:"kauff_mat ((basic [under]) \<circ> (basic [over])) 
   = kauff_mat ((basic [vert,vert]) \<circ> (basic [vert,vert])) "
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply(auto simp add:inverse1 inverse2)
 using computation_pull_pos_neg by (simp add: computation_downpos)
         
lemma pull_negpos_inv:"pull_negpos w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding pull_negpos_def using neg_pos_kauff_mat by auto

theorem pull_inv:"pull w1 w2 \<Longrightarrow> (kauff_mat w1) = (kauff_mat w2)"
 unfolding pull_def using pull_posneg_inv pull_negpos_inv by auto

theorem slide_inv:"slide w1 w2 \<Longrightarrow> (kauff_mat w1 = kauff_mat w2)"
proof-
 assume assm:"slide w1 w2"
 have " \<exists>B.((w1 = ((basic (make_vert_block (nat (domain_block B))))\<circ>(basic B)))
               \<and>(w2 = ((basic B)\<circ>(basic (make_vert_block (nat (codomain_block B))))))
               \<and> ((domain_block B) \<noteq> 0))"
       using slide_def assm  by auto
 then obtain B where  "((w1 = ((basic (make_vert_block (nat (domain_block B))))\<circ>(basic B)))
               \<and>(w2 = ((basic B)\<circ>(basic (make_vert_block (nat (codomain_block B))))))
               \<and> ((domain_block B) \<noteq> 0))" by auto
 then have 1:"((w1 = ((basic (make_vert_block (nat (domain_block B))))\<circ>(basic B)))
               \<and>(w2 = ((basic B)\<circ>(basic (make_vert_block (nat (codomain_block B))))))
               \<and> ((domain_block B) \<noteq> 0))"
       by auto
 have "kauff_mat w1 = kauff_mat (basic B)"
 proof-
  have s1:"mat (2^(nat (domain_block B))) (length (blockmat B)) (blockmat B)"
          by (metis matrix_blockmat row_length_domain_block) 
  have "w1 = ((basic (make_vert_block (nat (domain_wall (basic B))))\<circ>(basic B)))"
          using 1 domain_wall.simps by auto
  then have "kauff_mat w1 = rat_poly.matrix_mult 
                                     (kauff_mat (basic (make_vert_block (nat (domain_wall (basic B))))))
                                      (kauff_mat (basic B))"
          using tangle_compose_matrix is_tangle_diagram.simps 
          by (metis compose_Nil kauff_mat.simps(1) kauff_mat.simps(2))
  moreover then have "... =  rat_poly.matrix_mult  (mat1 (2^(nat (domain_block B)))) (blockmat B)"
          using kauff_mat.simps(1) domain_wall.simps(1) by (metis make_vert_block_map_blockmat)
  moreover have "... = (blockmat B)"
          using s1 mat1_mult_left by (metis make_vert_equiv_mat prop_make_vert_equiv(1))
  ultimately show ?thesis by auto
 qed 
 moreover have "kauff_mat w2 = kauff_mat (basic B)"
  proof-
   have s1:"mat (2^(nat (domain_block B))) (2^(nat (codomain_block B))) (blockmat B)"
            by (metis length_codomain_block matrix_blockmat row_length_domain_block)
   have "w2  = ((basic B) \<circ>(basic (make_vert_block (nat (codomain_wall (basic B))))))"
           using 1 domain_wall.simps by auto
   then have "kauff_mat w2 = 
                         rat_poly.matrix_mult 
                            (kauff_mat (basic B)) 
                            (kauff_mat (basic (make_vert_block (nat (codomain_wall (basic B))))))"
           using tangle_compose_matrix is_tangle_diagram.simps 
           by (metis compose_Nil kauff_mat.simps(1) kauff_mat.simps(2))
   moreover then have "... =  rat_poly.matrix_mult  (blockmat B) (mat1 (2^(nat (codomain_block B)))) "
                             using kauff_mat.simps(1) domain_wall.simps(1) 
           by (metis blockmat_make_vert codomain_wall.simps(1) make_vert_equiv_mat)
   moreover have "... = (blockmat B)"
           using s1  by (metis mat1_rt_mult)
   ultimately show ?thesis by auto
  qed 
  ultimately show ?thesis by auto
qed

theorem framed_linkrel_inv:"framed_linkrel w1 w2 \<Longrightarrow> (kauff_mat w1)= (kauff_mat w2)"
 unfolding framed_linkrel_def
 apply(auto)
 using framed_uncross_inv pull_inv straighten_inv  swing_inv rotate_inv compress_inv slide_inv 
 by auto


end
