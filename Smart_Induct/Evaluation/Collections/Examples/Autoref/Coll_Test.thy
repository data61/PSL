theory Coll_Test
imports 
  Collections.Refine_Dflt 
  Succ_Graph
begin

declare [[autoref_trace_failed_id]]

context begin interpretation autoref_syn .

schematic_goal "(?c::?'c,
  RETURN (({(1::nat,2::nat),(3,4)}):::(\<langle>\<langle>nat_rel,nat_rel\<rangle>prod_rel\<rangle>(map2set_rel (ahm_rel ?bhc))) )
)\<in>?R"
  apply autoref_monadic
  done

term dflt_ahs_rel

schematic_goal "(?c::?'c, \<lambda>(a::'a::hashable) (b::'a::hashable).
  ({(a,b)}:::\<langle>?Rk::(?'b::hashable\<times>_) set\<rangle>dflt_ahs_rel)
)\<in>?R"
  apply (autoref (keep_goal))
  done

subsection "Foreach-Loops"
schematic_goal "(?c::?'c,
  FOREACH {1,2,3::nat} (\<lambda>i s. RETURN (i+s)) 0
)\<in>?R"
  apply autoref_monadic
  done

schematic_goal "(?c::?'c,
  FOREACH (map_to_set [1::nat\<mapsto>True, 2\<mapsto>False]) (\<lambda>(k,v) s. RETURN (k+s)) 0
)\<in>?R"
  apply autoref_monadic
  done

(* TODO: generic algorithm for bounded hash code of sets! *)
schematic_goal "(?c::?'c,
  FOREACH 
    (map_to_set ([{1::nat}\<mapsto>True, {2}\<mapsto>False]:::\<langle>\<langle>nat_rel\<rangle>dflt_rs_rel,bool_rel\<rangle>(rbt_map_rel ?cmp))) 
    (\<lambda>(k,v) s. RETURN (v\<and>s)) False
)\<in>?R"
  apply autoref_monadic
  done

subsection "Array Hash Map Tests"

schematic_goal
  "(?f::?'c, \<lambda>m. (m)(1::nat\<mapsto>2::nat)) \<in> ?R"
  apply (autoref (keep_goal))
  done


schematic_goal
  "(?f::?'c, \<lambda>m. (m:::\<langle>Id,Id\<rangle>dflt_ahm_rel)(1::nat\<mapsto>2::nat)) \<in> ?R"
apply (autoref (keep_goal))
done

schematic_goal
  "(?f::?'c, Map.empty:::\<langle>Id,Id\<rangle>dflt_ahm_rel) \<in> ?R"
apply (autoref)
done

schematic_goal
  fixes mi m
  (* TODO: Obviously, we cannot override the tyREL-rule for 
    "nat\<rightharpoonup>nat" with this: *)
  assumes [autoref_rules]: "(mi,m)\<in>\<langle>nat_rel,nat_rel\<rangle>dflt_ahm_rel"
  shows "(?f::?'c, 
    RETURN (card (dom (m:::\<langle>nat_rel,nat_rel\<rangle>dflt_ahm_rel)))) \<in> ?R"
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
  "(?f::?'c, foo ::: \<langle>\<langle>Id,Id\<rangle>list_map_rel\<rangle>nres_rel) \<in> ?R"
  unfolding foo_def 
  apply autoref_monadic
  done

schematic_goal 
  "(?f::?'c, [1::nat \<mapsto> 2::nat, 3\<mapsto>4] ::: \<langle>nat_rel,nat_rel\<rangle>list_map_rel) \<in> ?R"
  apply autoref
  done

schematic_goal list_map_test:
  "(?f::?'c, RETURN (([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<langle>nat_rel,nat_rel\<rangle>list_map_rel) |`(-{1}))) \<in> ?R"
apply (autoref_monadic)
done
concrete_definition list_map_test uses list_map_test
value list_map_test

(* Why does this work:*)
schematic_goal
  "(?f::?'c, RETURN (card (dom ([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<langle>nat_rel,nat_rel\<rangle>list_map_rel)))) \<in> ?R"
apply (autoref_monadic)
done

(* But this doesn't? This is not specific to list_map;
   it doesn't work with dflt_rbt_rel either.*)
(*schematic_lemma
  "(?f::?'c, RETURN (dom ([1 \<mapsto> 2, 3::nat \<mapsto> 4::nat]
       :::\<langle>nat_rel,nat_rel\<rangle>list_map_rel))) \<in> ?R"
apply (autoref_monadic)
done*)


subsection "Array-Map Tests"

term "{1,2::nat} \<union> {3,4}"

schematic_goal array_set_test_code:
  "(?f::?'c, RETURN (({1,2::nat} \<union> {3,4} 
       ::: \<langle>nat_rel\<rangle>iam_set_rel )))\<in>?R" 
by (autoref_monadic (trace))

concrete_definition array_set_test uses array_set_test_code
print_theorems
value [nbe] array_set_test

schematic_goal
  "(?f::?'c, RETURN (({1} ::: \<langle>nat_rel\<rangle>dflt_rs_rel) = {}))\<in>?R" 
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
  "(?f::?'c, RETURN (({1} ::: \<langle>nat_rel\<rangle>iam_set_rel) = {}))\<in>?R" 
  apply (autoref_monadic (trace))
  done

schematic_goal
  assumes [autoref_rules]: "(f,f')\<in>nat_rel\<rightarrow>Rb"
  shows "(?f::?'c,f' 3)\<in>?R"
  by (autoref)


schematic_goal "(?f::?'c,
  RETURN (({1,2::nat} \<times> {3,4::nat}) ::: \<langle>\<langle>Id,Id\<rangle>prod_rel\<rangle>dflt_rs_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN ({1,2::nat} \<inter> ({3,4::nat}) ::: \<langle>Id\<rangle>list_set_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN ({1,2::nat} \<inter> ({3,4::nat}) ::: \<langle>Id\<rangle>dflt_rs_rel)
)\<in>?R"
  by autoref_monadic

schematic_goal "(?f::?'c,
  RETURN (card (dom ([ 1::nat \<mapsto> True, 2\<mapsto>False ] ::: \<langle>Id,Id\<rangle>dflt_rm_rel )))
)\<in>?R"
  by autoref_monadic

text \<open>A hairy case for the operator identification heuristics for maps:\<close>
schematic_goal 
  shows "(?f::?'c,
  \<lambda>m (x::'a::linorder) (y::'b::linorder). case_option
    None
    (\<lambda>m'. m' y)
    (m x)
)\<in>?R"
  by (autoref (keep_goal))


schematic_goal 
  shows "(?f::?'c,
  \<lambda>m (x::'a::hashable) (y::'b::hashable). case_option
    None
    (\<lambda>m'. m' y)
    (m x)
)\<in>?R"
  apply (autoref (keep_goal))
  done


schematic_goal 
  shows "(?f::?'c,
  \<lambda>m (x::'a::hashable) (y::'b::linorder). case_option
    None
    (\<lambda>m'. m' y)
    (m (x:::Id))
)\<in>?R"
  by (autoref (keep_goal))


schematic_goal "(?f::?'c,
  {1,2::'a::numeral} \<times> {3,4::'a}
)\<in>?R"
  by (autoref (keep_goal))

schematic_goal "(?f::?'c,
  {1,2::'a::{numeral,hashable}} \<times> ({3,4::'a} ::: \<langle>Id\<rangle>dflt_ahs_rel)
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
  RETURN (({1,2::nat} \<times> {3,4::nat}) ::: \<langle>\<langle>Id,Id\<rangle>prod_rel\<rangle>dflt_rs_rel)
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
  {1,2::nat} \<union> {3,4} ::: \<langle>Id\<rangle>list_set_rel
)\<in>?R"
  by (autoref (keep_goal))


lemma is_refgoal: "(c,a)\<in>R \<Longrightarrow> (c,a)\<in>R" .

schematic_goal "(?f::?'c,
  ({{1::nat}:::\<langle>Id\<rangle> map2set_rel dflt_rm_rel} ) 
  \<union> ({{2,3,4,5,5,6,7,8,98,9,0}}) 
)\<in>?R"
  by (autoref (keep_goal))


text \<open>The next two lemmas demonstrate optimization: The insert-operation
  is translated by @{term "(#)"}\<close>
schematic_goal "(?f::?'c, {1,2,3,4::nat}:::\<langle>Id\<rangle>list_set_rel
  )\<in>?R"
  by (autoref (keep_goal))

schematic_goal 
  "(?f::?'c, {{1},{2},{3},{4::nat}}:::\<langle>?R'::(?'d\<times>_) set\<rangle>list_set_rel
  )\<in>?R"
  by (autoref (keep_goal))


schematic_goal "(?f::?'c,
  SPEC (\<lambda>x. x\<in>({1,2,3::nat}:::\<langle>Id\<rangle>dflt_rs_rel)) 
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
  let s = ({1,2,3::nat}:::\<langle>Id\<rangle>dflt_rs_rel);
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
  ({{1::nat}} ) 
  \<union> ({{2,3,4,5,5,6,7,8,98,9,0}}) 
)\<in>?R"
  by (autoref (keep_goal))

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

end

text \<open>Indirect Annotation\<close>
consts 
  rel_set1 :: rel_name
  rel_set2 :: rel_name


context begin interpretation autoref_syn .

definition 
  "algo \<equiv> ( {1,2,3::nat}::#rel_set1, {1,2,3::nat}::#rel_set2 )"

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



text \<open>A witness of the red algorithm is a node on the stack and a path
  to this node\<close>
type_synonym 'v red_witness = "('v list \<times> 'v) option"
text \<open>Prepend node to red witness\<close>
fun prep_wit_red :: "'v \<Rightarrow> 'v red_witness \<Rightarrow> 'v red_witness" where
  "prep_wit_red v None = None"
| "prep_wit_red v (Some (p,u)) = Some (v#p,u)"

text \<open>
  Initial witness for node \<open>u\<close> with onstack successor \<open>v\<close> 
\<close>
definition red_init_witness :: "'v \<Rightarrow> 'v \<Rightarrow> 'v red_witness" where
  "red_init_witness u v = Some ([u],v)"

definition red_dfs where
  "red_dfs E onstack V u \<equiv> 
    REC\<^sub>T (\<lambda>D (V,u). do {
      let V=(insert u V);

      \<comment> \<open>Check whether we have a successor on stack\<close>
      brk \<leftarrow> FOREACH\<^sub>C (E``{u}) (\<lambda>brk. brk=None) 
        (\<lambda>t _. if t\<in>onstack then RETURN (red_init_witness u t) else RETURN None)
        None;

      \<comment> \<open>Recurse for successors\<close>
      case brk of
        None \<Rightarrow>
          FOREACH\<^sub>C ((E``{u})) (\<lambda>(V,brk). brk=None)
            (\<lambda>t (V,_). 
              if t\<notin>V then do {
                (V,brk) \<leftarrow> D (V,t);
                RETURN (V,prep_wit_red u brk)
              } else RETURN (V,None))
            (V,None)
      | _ \<Rightarrow> RETURN (V,brk)
    }) (V,u)
  "

abbreviation "i_red_witness \<equiv> \<langle>\<langle>\<langle>i_nat\<rangle>\<^sub>ii_list,i_nat\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option"
lemma [autoref_itype]:
  "red_init_witness ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_nat \<rightarrow>\<^sub>i i_red_witness"
  "prep_wit_red ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_red_witness \<rightarrow>\<^sub>i i_red_witness"
  by auto

abbreviation "red_witness_rel \<equiv> \<langle>\<langle>\<langle>nat_rel\<rangle>list_rel,nat_rel\<rangle>prod_rel\<rangle>option_rel"

lemma [autoref_rules_raw]:
  "(red_init_witness,red_init_witness) \<in> nat_rel\<rightarrow>nat_rel\<rightarrow>red_witness_rel"
  "(prep_wit_red,prep_wit_red) \<in> nat_rel \<rightarrow> red_witness_rel \<rightarrow> red_witness_rel"
  by (auto)

(*schematic_lemma 
  "(?f, RECT (\<lambda>D x. D x)) \<in> (?R::(?'c\<times>_) set)"
  apply (autoref (keep_goal))
  done*)

schematic_goal red_dfs_impl:
  notes [[goals_limit = 1]]
  fixes u'::"nat" and V'::"nat set"
  assumes [autoref_rules]:
    "(u,u')\<in>nat_rel" 
    "(V,V')\<in>\<langle>nat_rel\<rangle>dflt_rs_rel" 
    "(onstack,onstack')\<in>\<langle>nat_rel\<rangle>dflt_rs_rel" 
    "(E,E')\<in>\<langle>nat_rel\<rangle>slg_rel"
  shows "(?f, red_dfs E' onstack' V' u') \<in> (?R::(?'c\<times>_) set)"
  apply -
  unfolding red_dfs_def
  apply (autoref_monadic (trace))
  done

concrete_definition red_dfs_impl for E onstack V u uses red_dfs_impl 

prepare_code_thms red_dfs_impl_def

export_code red_dfs_impl checking SML


end
end
