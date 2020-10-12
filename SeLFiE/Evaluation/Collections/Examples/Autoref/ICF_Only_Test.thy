theory ICF_Only_Test
imports 
  Collections.Refine_Dflt_Only_ICF 
begin

declare [[autoref_trace_failed_id]]

subsection "Array Hash Map Tests"

context begin interpretation autoref_syn .

schematic_goal
  "(?f::?'c, \<lambda>m. (m)(1::nat\<mapsto>2::nat)) \<in> ?R"
  apply (autoref (keep_goal))
  done

(* Optimizations *)

subsection "List Map Tests"

definition foo::"(nat\<rightharpoonup>nat) nres" where "foo \<equiv>
  do {
    let X = Map.empty;
    ASSERT (1 \<notin> dom X);
    RETURN (X(1 \<mapsto> 2))
  }"

schematic_goal list_map_update_dj_test:
  "(?f::?'c, foo ::: \<langle>\<langle>Id,Id\<rangle>lm.rel\<rangle>nres_rel) \<in> ?R"
  unfolding foo_def 
  apply autoref_monadic
  done

schematic_goal 
  "(?f::?'c, [1::nat \<mapsto> 2::nat, 3\<mapsto>4] ::: \<langle>nat_rel,nat_rel\<rangle>lm.rel) \<in> ?R"
  apply autoref
  done

schematic_goal list_map_test:
  "(?f::?'c, RETURN (([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<langle>nat_rel,nat_rel\<rangle>lm.rel) |`(-{1}))) \<in> ?R"
apply (autoref_monadic)
done
concrete_definition list_map_test uses list_map_test
value list_map_test

schematic_goal
  "(?f::?'c, RETURN (card (dom ([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<langle>nat_rel,nat_rel\<rangle>lm.rel)))) \<in> ?R"
apply (autoref_monadic)
done

end
end
