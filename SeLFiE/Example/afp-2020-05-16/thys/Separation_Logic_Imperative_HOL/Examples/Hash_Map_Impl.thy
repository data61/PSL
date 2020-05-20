section "Hash-Maps (Interface Instantiations)"
theory Hash_Map_Impl
imports Imp_Map_Spec Hash_Map
begin

lemma hm_map_impl: "imp_map is_hashmap"
  apply unfold_locales
  apply (rule is_hashmap_prec)
  done
interpretation hm: imp_map is_hashmap by (rule hm_map_impl)

lemma hm_empty_impl: "imp_map_empty is_hashmap hm_new"
  apply unfold_locales
  apply (sep_auto heap: hm_new_rule)
  done
interpretation hm: imp_map_empty is_hashmap hm_new by (rule hm_empty_impl)

lemma hm_lookup_impl: "imp_map_lookup is_hashmap hm_lookup"
  apply unfold_locales
  apply (sep_auto heap: hm_lookup_rule)
  done
interpretation hm: imp_map_lookup is_hashmap hm_lookup by (rule hm_lookup_impl)

lemma hm_update_impl: "imp_map_update is_hashmap hm_update"
  apply unfold_locales
  apply (sep_auto heap: hm_update_rule)
  done
interpretation hm: imp_map_update is_hashmap hm_update by (rule hm_update_impl)

lemma hm_delete_impl: "imp_map_delete is_hashmap hm_delete"
  apply unfold_locales
  apply (sep_auto heap: hm_delete_rule)
  done
interpretation hm: imp_map_delete is_hashmap hm_delete by (rule hm_delete_impl)

lemma hm_is_empty_impl: "imp_map_is_empty is_hashmap hm_isEmpty"
  apply unfold_locales
  apply (sep_auto heap: hm_isEmpty_rule)
  done
interpretation hm: imp_map_is_empty is_hashmap hm_isEmpty
  by (rule hm_is_empty_impl)

lemma hm_size_impl: "imp_map_size is_hashmap hm_size"
  apply unfold_locales
  apply (sep_auto heap: hm_size_rule)
  done
interpretation hm: imp_map_size is_hashmap hm_size by (rule hm_size_impl)

lemma hm_iterate_impl: 
  "imp_map_iterate is_hashmap hm_is_it hm_it_init hm_it_has_next hm_it_next"
  apply unfold_locales
  apply (rule hm_it_init_rule)
  apply (erule hm_it_next_rule)
  apply (rule hm_it_has_next_rule)
  apply (rule ent_frame_fwd[OF hm_it_finish])
  apply (frame_inference)
  apply solve_entails
  done
interpretation hm: 
  imp_map_iterate is_hashmap hm_is_it hm_it_init hm_it_has_next hm_it_next
  by (rule hm_iterate_impl)

(*
definition "hm_is_it'' m ht l' it \<equiv> 
  \<exists>\<^sub>Al. hm_is_it' l ht l' it * \<up>(map_of (concat l) = m)"

lemma hm_iterate'_impl: 
  "imp_map_iterate' is_hashmap hm_is_it'' hm_it_init hm_it_has_next hm_it_next"
  apply unfold_locales
  apply (rule hm_it_init_rule)
  apply (erule hm_it_next_rule)
  apply (rule hm_it_has_next_rule)
  apply (rule ent_frame_fwd[OF hm_it_finish])
  apply (frame_inference)
  apply solve_entails
  done

*)

export_code hm_new hm_lookup hm_update hm_delete hm_isEmpty hm_size 
  hm_it_init hm_it_has_next hm_it_next
  checking SML_imp

end
