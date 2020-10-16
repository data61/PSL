theory ICF_Test
imports 
  Collections.Refine_Dflt_ICF 
begin

declare [[autoref_trace_failed_id]]

subsection "Array Hash Map Tests"


schematic_goal
  "(?f::?'c, [{1::nat} |-> {2::nat}]) \<in> ?R"
  by (autoref (keep_goal))

schematic_goal
  "(?f::?'c, \<lambda>m. (m)(1::nat\<mapsto>2::nat)) \<in> ?R"
  apply (autoref (keep_goal))
  done


schematic_goal
  "(?f::?'c, \<lambda>m. (m:::\<^sub>r\<langle>Id,Id\<rangle>dflt_ahm_rel)(1::nat\<mapsto>2::nat)) \<in> ?R"
  apply (autoref (keep_goal))
  done

schematic_goal
  "(?f::?'c, Map.empty:::\<^sub>r\<langle>Id,Id\<rangle>dflt_ahm_rel) \<in> ?R"
apply (autoref)
done

schematic_goal
  fixes mi m
  (* TODO: Obviously, we cannot override the tyREL-rule for 
    "nat\<rightharpoonup>nat" with this: *)
  assumes [autoref_rules]: "(mi,m)\<in>\<langle>nat_rel,nat_rel\<rangle>dflt_ahm_rel"
  shows "(?f::?'c, 
    RETURN (card (dom (m:::\<^sub>r\<langle>nat_rel,nat_rel\<rangle>dflt_ahm_rel)))) \<in> ?R"
  apply (autoref_monadic)
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
  "(?f::?'c, foo :::\<^sub>r \<langle>\<langle>Id,Id\<rangle>list_map_rel\<rangle>nres_rel) \<in> ?R"
  unfolding foo_def 
  apply autoref_monadic
  done

schematic_goal 
  "(?f::?'c, [1::nat \<mapsto> 2::nat, 3\<mapsto>4] :::\<^sub>r \<langle>nat_rel,nat_rel\<rangle>list_map_rel) \<in> ?R"
  apply autoref
  done

schematic_goal list_map_test:
  "(?f::?'c, RETURN (([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<^sub>r\<langle>nat_rel,nat_rel\<rangle>list_map_rel) |`(-{1}))) \<in> ?R"
apply (autoref_monadic)
done
concrete_definition list_map_test uses list_map_test
value list_map_test

(* Why does this work:*)
schematic_goal
  "(?f::?'c, RETURN (card (dom ([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<^sub>r\<langle>nat_rel,nat_rel\<rangle>list_map_rel)))) \<in> ?R"
apply (autoref_monadic)
done

(* But this doesn't? This is not specific to list_map;
   it doesn't work with dflt_rbt_rel either.*)
(*schematic_lemma
  "(?f::?'c, RETURN (dom ([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<^sub>r\<langle>nat_rel,nat_rel\<rangle>list_map_rel))) \<in> ?R"
apply (autoref_monadic)
done*)


subsection "Array-Map Tests"

term "{1,2::nat} \<union> {3,4}"

schematic_goal array_set_test_code:
  "(?f::?'c, RETURN (({1,2::nat} \<union> {3,4} 
       :::\<^sub>r \<langle>nat_rel\<rangle>iam_set_rel )))\<in>?R" 
by (autoref_monadic (trace))

concrete_definition array_set_test uses array_set_test_code
print_theorems
value [nbe] array_set_test

schematic_goal
  "(?f::?'c, RETURN (({1} :::\<^sub>r \<langle>nat_rel\<rangle>dflt_rs_rel) = {}))\<in>?R" 
apply (autoref_monadic (trace))
done

schematic_goal
  "(?f::?'c, RETURN (card {1,2,3::nat}))\<in>?R" 
apply (autoref_monadic (trace))
done

schematic_goal
  "(?f::?'c, RETURN (\<forall>x\<in>{1,2,3::nat}. x<4))\<in>?R" 
apply (autoref_monadic (trace))
done

schematic_goal
  "(?f::?'c, RETURN (\<exists>x\<in>{1,2,3::nat}. x<4))\<in>?R" 
apply (autoref_monadic (trace))
done

schematic_goal
  "(?f::?'c, RETURN (({1} :::\<^sub>r \<langle>nat_rel\<rangle>iam_set_rel) = {}))\<in>?R" 
  apply (autoref_monadic (trace))
  done

schematic_goal
  assumes [autoref_rules]: "(f,f')\<in>nat_rel\<rightarrow>Rb"
  shows "(?f::?'c,f' 3)\<in>?R"
  by (autoref)


schematic_goal "(?f::?'c,
  RETURN (({1,2::nat} \<times> {3,4::nat}) :::\<^sub>r \<langle>\<langle>Id,Id\<rangle>prod_rel\<rangle>dflt_rs_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN ({1,2::nat} \<inter> ({3,4::nat}) :::\<^sub>r \<langle>Id\<rangle>list_set_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN ({1,2::nat} \<inter> ({3,4::nat}) :::\<^sub>r \<langle>Id\<rangle>dflt_rs_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN (card (dom ([ 1::nat \<mapsto> True, 2\<mapsto>False ] :::\<^sub>r \<langle>Id,Id\<rangle>dflt_rm_rel )))
)\<in>?R"
  by autoref_monadic


schematic_goal "(?f::?'c,
  {1,2::'a::numeral} \<times> {3,4::'a}
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  {1,2::'a::{numeral,hashable}} \<times> ({3,4::'a} :::\<^sub>r \<langle>Id\<rangle>dflt_ahs_rel)
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  {1,2::nat} \<times> {3,4::nat}
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  {1,2::nat} \<inter> {3,4::nat}
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  RETURN (({1,2::nat} \<times> {3,4::nat}) :::\<^sub>r \<langle>\<langle>Id,Id\<rangle>prod_rel\<rangle>dflt_rs_rel)
)\<in>?R"
  by autoref_monadic

(* TODO: ty_REL hint is ignored. Reason: Seems to not properly work with GAs! *)
schematic_goal 
  notes [autoref_tyrel] = ty_REL[where 'a = "(nat\<times>nat) set" 
    and R="\<langle>\<langle>Id,Id\<rangle>prod_rel\<rangle>dflt_rs_rel"] 
  shows "(?f::?'c,
    RETURN (({1,2::nat} \<times> {3,4::nat}))
  )\<in>?R"
  by autoref_monadic

(* TODO: Iterator optimization does not capture 
    foldli ((map fst \<circ> rbt_to_list) x)
pattern!
*)

text \<open>We have an optimized version for add on red-black trees\<close>
schematic_goal "(?f::?'c,
  [ 1::nat \<mapsto> True, 2::nat \<mapsto> False ] ++ [ 3::nat \<mapsto> True, 4::nat \<mapsto> False ]
)\<in>?R"
  by (autoref (keep_goal))

text \<open>The optimized version is also transfered through the map2set converter\<close>
schematic_goal "(?f::?'c,
  {1,2::nat} \<union> {3,4}
)\<in>?R"
  by (autoref (keep_goal))

text \<open>For list-sets, the generic version is used\<close>
schematic_goal "(?f::?'c,
  {1,2::nat} \<union> {3,4} :::\<^sub>r \<langle>Id\<rangle>list_set_rel
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  ({{1::nat}:::\<^sub>r\<langle>Id\<rangle> map2set_rel dflt_rm_rel} ) 
  \<union> ({{2,3,4,5,5,6,7,8,98,9,0}}) 
)\<in>?R"
  by (autoref (keep_goal))

text \<open>The next two lemmas demonstrate optimization: The insert-operation
  is translated by @{term "(#)"}\<close>
schematic_goal "(?f::?'c, {1,2,3,4::nat}:::\<^sub>r\<langle>Id\<rangle>list_set_rel
  )\<in>?R"
  by (autoref (keep_goal))

schematic_goal 
  "(?f::?'c, {{1},{2},{3},{4::nat}}:::\<^sub>r\<langle>?R'::(?'d\<times>_) set\<rangle>list_set_rel
  )\<in>?R"
  by (autoref (keep_goal))


schematic_goal "(?f::?'c,
  SPEC (\<lambda>x. x\<in>({1,2,3::nat}:::\<^sub>r\<langle>Id\<rangle>dflt_rs_rel)) 
)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?f::?'c,
  \<lambda>s::nat set. {s} \<union> {{1,2,3}} = {{1}}
)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?f::?'c,
  \<forall>(k,v)\<in>map_to_set [1::nat\<mapsto>2::nat]. k>v
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c, do {
  let s = ({1,2,3::nat}:::\<^sub>r\<langle>Id\<rangle>dflt_rs_rel);
  FOREACH s (\<lambda>n s. RETURN (n+s)) 0
}
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c, do {
  let s = ({{1,2,3::nat}, {}, {1,2}});
  FOREACH s (\<lambda>n s. RETURN (n \<union> s)) {}
}
)\<in>?R"
  by (autoref_monadic)

schematic_goal "(?f::?'c,
  SPEC (\<lambda>x. x\<in>({1,2,3::nat})) 
)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?f::?'c,
  \<lambda>s::nat set. {s} \<union> {{1,2,3}} = {{1}}
)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?f::?'c,
  \<forall>(k,v)\<in>map_to_set [1::nat\<mapsto>2::nat]. k>v
)\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?f::?'c,
  [ 1::nat \<mapsto> [ 2::nat \<mapsto> 3::nat, 1::nat \<mapsto> 3::nat ] ]
)\<in>?R"
  apply (autoref (keep_goal))
  done



text \<open>Indirect Annotation\<close>
consts 
  rel_set1 :: rel_name
  rel_set2 :: rel_name

definition 
  "algo \<equiv> ( {1,2,3::nat}::#\<^sub>rrel_set1, {1,2,3::nat}::#\<^sub>rrel_set2 )"

schematic_goal 
  notes [autoref_rel_indirect] = 
    REL_INDIRECT[of rel_set1 "\<langle>Rk\<rangle>list_set_rel" for Rk]
    REL_INDIRECT[of rel_set2 "\<langle>Rk\<rangle>dflt_rs_rel" for Rk]
  shows "(?f::?'c,algo) \<in> ?R"
  unfolding algo_def
  by (autoref)

schematic_goal 
  notes [autoref_rel_indirect] = 
    REL_INDIRECT[of rel_set1 "\<langle>Rk\<rangle>dflt_rs_rel" for Rk]
    REL_INDIRECT[of rel_set2 "\<langle>Rk\<rangle>dflt_rs_rel" for Rk]
  shows "(?f::?'c,algo) \<in> ?R"
  unfolding algo_def
  by (autoref)

end
