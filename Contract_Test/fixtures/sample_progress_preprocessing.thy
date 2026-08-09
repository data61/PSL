(* AbductionProver progress report 4 (TBC preprocessing), 245s. The goal is not proved yet; these auxiliary lemmas are, completely, in
   the order they were proved. *)
lemma identity_5220574: "x nil2 var_1 = var_1"
apply auto
done
lemma idempotent_element_5221382: "x nil2 nil2 = nil2"
apply (auto simp add: identity_5220574)
done
lemma identity_5220852: "x var_1 nil2 = var_1"
apply (induct "var_1")
apply (auto simp add: identity_5220574 idempotent_element_5221382)
done
lemma associativity_5220242: "x (x var_1 var_2) var_3 = x var_1 (x var_2 var_3)"
apply (induct "var_1" arbitrary:var_2)
apply (auto simp add: identity_5220574 idempotent_element_5221382 identity_5220852)
done
lemma associativity_5219910: "x var_1 (x var_2 var_3) = x (x var_1 var_2) var_3"
apply (induct "var_1" arbitrary:var_2)
apply (auto simp add: identity_5220574 idempotent_element_5221382 identity_5220852 associativity_5220242)
done
