

proof -


have associativity_31515938: "x var_1 (x var_2 var_3) = x (x var_1 var_2) var_3" for var_3 var_2 var_1
apply (induct "var_1")
apply auto
done
have identity_31516640: "x nil2 var_1 = var_1" for var_1
apply auto
done
have identity_31516918: "x var_1 nil2 = var_1" for var_1
apply (induct "var_1")
apply auto
done
have idempotent_element_31517454: "x nil2 nil2 = nil2"
apply auto
done
have abduced_lemma_remove_function_33136254: "S (length (x var_0 var_1)) = length (x var_0 (cons2 var_2 var_1))" for var_2 var_1 var_0
apply (induct var_0)
apply (simp_all add: associativity_31515938 identity_31516640 identity_31516918 idempotent_element_31517454)
done
have abduced_lemma_tactic_31723170: "length (x var_3 var_4) = length (x var_4 var_3) \<Longrightarrow> S (length (x var_4 var_3)) = length (x var_4 (cons2 var_5 var_3))" for var_5 var_4 var_3
apply (simp add: abduced_lemma_remove_function_33136254 add: associativity_31515938 identity_31516640 identity_31516918 idempotent_element_31517454)
done
show "length (x y z) = length (x z y)"
apply (induct "y" "z" rule:S04_p02_decl.x.induct)
apply (auto simp add: associativity_31515938 identity_31516640 identity_31516918 idempotent_element_31517454)
apply (simp add: abduced_lemma_tactic_31723170 add: associativity_31515938 identity_31516640 identity_31516918 idempotent_element_31517454)
done
qed
