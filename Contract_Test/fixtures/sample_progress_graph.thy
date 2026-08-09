(* AbductionProver progress report 6 (graph search), 372s. The goal is not proved yet; these auxiliary lemmas are, completely, in
   the order they were proved. *)


have associativity_5215138: "x var_1 (x var_2 var_3) = x (x var_1 var_2) var_3" for var_3 var_2 var_1
apply (induct "var_1" arbitrary:var_2)
apply auto
done
have identity_5215802: "x nil2 var_1 = var_1" for var_1
apply auto
done
have identity_5216080: "x var_1 nil2 = var_1" for var_1
apply (induct "var_1")
apply auto
done
have idempotent_element_5216616: "x nil2 nil2 = nil2"
apply auto
done
