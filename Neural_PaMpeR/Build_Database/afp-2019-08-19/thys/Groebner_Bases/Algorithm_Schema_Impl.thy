(* Author: Alexander Maletzky *)

section \<open>Code Equations Related to the Computation of Gr\"obner Bases\<close>

theory Algorithm_Schema_Impl
  imports Algorithm_Schema Benchmarks
begin

lemma card_keys_MP_oalist [code]: "card_keys (MP_oalist xs) = length (fst (list_of_oalist_ntm xs))"
proof -
  let ?rel = "ko.lt (key_order_of_nat_term_order_inv (snd (list_of_oalist_ntm xs)))"
  have "irreflp ?rel" by (simp add: irreflp_def)
  moreover have "transp ?rel" by (simp add: lt_of_nat_term_order_alt)
  ultimately have *: "distinct (map fst (fst (list_of_oalist_ntm xs)))" using oa_ntm.list_of_oalist_sorted
    by (rule distinct_sorted_wrt_irrefl)
  have "card_keys (MP_oalist xs) = length (map fst (fst (list_of_oalist_ntm xs)))"
    by (simp only: card_keys_def keys_MP_oalist image_set o_def oa_ntm.sorted_domain_def[symmetric],
        rule distinct_card, fact *)
  also have "... = length (fst (list_of_oalist_ntm xs))" by simp
  finally show ?thesis .
qed

end (* theory *)
