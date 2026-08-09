(* AbductionProver did not prove the goal. These auxiliary lemmas were proved
   completely, in the order they were proved. Pasted as-is at the point the prover
   was invoked, the block establishes them for real and closes the still-open goal
   with sorry - replace the sorry when you have the proof. *)
proof -
have example_prelude_1: "x nil2 var_1 = var_1" for var_1
apply auto
done
have example_graph_1: "length (x var_1 var_2) = length (x var_2 var_1)" for var_2 var_1
apply (auto simp add: example_prelude_1)
done
show ?thesis sorry
qed
