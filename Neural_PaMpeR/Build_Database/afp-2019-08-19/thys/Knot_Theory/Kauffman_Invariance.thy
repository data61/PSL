section\<open>Kauffman\_Invariance: Proving the invariance of Kauffman Bracket\<close>

theory Kauffman_Invariance
imports Link_Algebra Linkrel_Kauffman
begin

text\<open>In the following theorem, we prove that the kauffman matrix 
 is invariant of framed link invariance\<close>

theorem kauffman_invariance:"(w1::wall) ~f w2 \<Longrightarrow> kauff_mat w1 = kauff_mat w2"
proof(induction rule:Framed_Tangle_Equivalence.induct)
 case refl
  show ?case using refl by auto
 next
 case sym
  show ?case using sym by auto
 next
 case trans
  show ?case using trans by auto
 next
 case compose_eq
  show ?case using compose_eq tangle_compose_matrix by auto
 next
 case codomain_compose
  show ?case using codomain_compose left_mat_compose by auto
 next
 case domain_compose
  show ?case using domain_compose right_mat_compose by auto
 next
 case tensor_eq
  show ?case using  tensor_eq.IH Tensor_Invariance by (metis)
 next
 case equality
  show ?case using framed_linkrel_inv equality by auto
qed



lemma "rat_poly_times A B = 1"
 using inverse1  by (metis )

text\<open>we calculate kauffman bracket of a few links\<close>

text\<open>kauffman bracket of an unknot with zero crossings\<close>
lemma "kauff_mat ([cup]*(basic [cap])) = [[-(A^2) - (B^2)]]"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 by (simp add: power2_eq_square)
text\<open>kauffman bracket of an a two component unlinked unknot 
    with zero crossings\<close>

lemma "kauff_mat ([cup,cup]*(basic [cap,cap]))= [[((A^4)+(B^4)) + 2]]"
 apply(simp add:mat_multI_def)
 apply(simp add:matT_vec_multI_def)
 apply(auto simp add:replicate_def rat_poly.row_length_def)
 apply(auto simp add:scalar_prod)
 apply(auto simp add:unlink_computation)
 done


definition trefoil_polynomial::"rat_poly"
where
"trefoil_polynomial \<equiv>
rat_poly_plus
     (rat_poly_times (rat_poly_times A A)
       (rat_poly_plus
         (rat_poly_times B
           (rat_poly_times B
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times A A))))
         (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
           (rat_poly_plus (rat_poly_times B (rat_poly_times B (rat_poly_times A A)))
             (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
               (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
                 (rat_poly_times A A)))))))
     (rat_poly_plus
       (rat_poly_times 2
         (rat_poly_times A
           (rat_poly_times A
             (rat_poly_times A
               (rat_poly_times A (rat_poly_times A (rat_poly_times B B)))))))
       (rat_poly_times (rat_poly_times B B)
         (rat_poly_times B
           (rat_poly_times (A - rat_poly_times (rat_poly_times B B) B)
             (rat_poly_times B (rat_poly_times B B))))))"

text\<open>kauffman bracket of trefoil\<close>
lemma trefoil:
"kauff_mat ([cup,cup]*[vert,over,vert]*[vert,over,vert]*[vert,over,vert]
              *(basic [cap,cap]))
          = [[trefoil_polynomial]]"
 by(simp add: mat_multI_def matT_vec_multI_def rat_poly.row_length_def
   scalar_prod trefoil_polynomial_def)

end
