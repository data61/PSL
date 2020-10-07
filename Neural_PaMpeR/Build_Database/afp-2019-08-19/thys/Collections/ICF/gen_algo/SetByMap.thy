(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedMap, transfer of iterators to OrderedSet

*)
section \<open>\isaheader{Implementing Sets by Maps}\<close>
theory SetByMap
imports 
  "../spec/SetSpec"
  "../spec/MapSpec"
  SetGA
  MapGA
begin
text_raw \<open>\label{thy:SetByMap}\<close>

text \<open>
  In this theory, we show how to implement sets
  by maps.
\<close>

(* TODO: We could also define some more operations directly,
  e.g. union, ball, bex, \<dots> *)

text \<open>Auxiliary lemma\<close>
lemma foldli_foldli_map_eq:
  "foldli (foldli l (\<lambda>x. True) (\<lambda>x l. l@[f x]) []) c f' \<sigma>0
    = foldli l c (f' o f) \<sigma>0"
proof -
  show ?thesis
    apply (simp add: map_by_foldl foldli_map foldli_foldl)
    done
qed

locale SetByMapDefs =
  map: StdBasicMapDefs ops
  for ops :: "('x,unit,'s,'more) map_basic_ops_scheme"
begin
  definition "\<alpha> s \<equiv> dom (map.\<alpha> s)"
  definition "invar s \<equiv> map.invar s"
  definition empty where "empty \<equiv> map.empty"
  definition "memb x s \<equiv> map.lookup x s \<noteq> None"
  definition "ins x s \<equiv> map.update x () s"
  definition "ins_dj x s \<equiv> map.update_dj x () s"
  definition "delete x s \<equiv> map.delete x s"
  definition list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" 
    where "list_it s c f \<sigma>0 \<equiv> it_to_it (map.list_it s) c (f o fst) \<sigma>0"

  local_setup \<open>Locale_Code.lc_decl_del @{term list_it}\<close>

  lemma list_it_alt: "list_it s = map_iterator_dom (map.iteratei s)"
  proof -
    have A: "\<And>f. (\<lambda>(x,_). f x) = (\<lambda>x. f (fst x))" by auto
    show ?thesis
      unfolding list_it_def[abs_def] map_iterator_dom_def
        poly_map_iteratei_defs.iteratei_def
        set_iterator_image_def set_iterator_image_filter_def
      by (auto simp: comp_def)
  qed

  lemma list_it_unfold:
    "it_to_it (list_it s) c f \<sigma>0 = map.iteratei s c (f o fst) \<sigma>0"
    unfolding list_it_def[abs_def] it_to_it_def
    unfolding poly_map_iteratei_defs.iteratei_def it_to_it_def
    by (simp add: foldli_foldli_map_eq comp_def)

  definition [icf_rec_def]: "dflt_basic_ops \<equiv> \<lparr>
    bset_op_\<alpha> = \<alpha>,
    bset_op_invar = invar,
    bset_op_empty = empty,
    bset_op_memb = memb,
    bset_op_ins = ins,
    bset_op_ins_dj = ins_dj,
    bset_op_delete = delete,
    bset_op_list_it = list_it
    \<rparr>"
  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_basic_ops}\<close>

end

setup \<open>
  (Record_Intf.add_unf_thms_global @{thms 
    SetByMapDefs.list_it_def[abs_def]
  })
\<close> 


(*lemmas [code_unfold] = SetByMapDefs.list_it_def[abs_def]*)

locale SetByMap = SetByMapDefs ops +
  map: StdBasicMap ops
  for ops :: "('x,unit,'s,'more) map_basic_ops_scheme"
begin
  lemma empty_impl: "set_empty \<alpha> invar empty"
    apply unfold_locales
    unfolding \<alpha>_def invar_def empty_def
    by (auto simp: map.empty_correct)

  lemma memb_impl: "set_memb \<alpha> invar memb"
    apply unfold_locales
    unfolding \<alpha>_def invar_def memb_def
    by (auto simp: map.lookup_correct)

  lemma ins_impl: "set_ins \<alpha> invar ins"
    apply unfold_locales
    unfolding \<alpha>_def invar_def ins_def
    by (auto simp: map.update_correct)

  lemma ins_dj_impl: "set_ins_dj \<alpha> invar ins_dj"
    apply unfold_locales
    unfolding \<alpha>_def invar_def ins_dj_def
    by (auto simp: map.update_dj_correct)

  lemma delete_impl: "set_delete \<alpha> invar delete"
    apply unfold_locales
    unfolding \<alpha>_def invar_def delete_def
    by (auto simp: map.delete_correct)
  
  lemma list_it_impl: "poly_set_iteratei \<alpha> invar list_it"
  proof
    fix s
    assume I: "invar s"
    hence I': "map.invar s" unfolding invar_def .

    have S: "\<And>f. (\<lambda>(x,_). f x) = (\<lambda>xy. f (fst xy))"
      by auto
  
    from map_iterator_dom_correct[OF map.iteratei_correct[OF I']] 
    show "set_iterator (list_it s) (\<alpha> s)"
      unfolding \<alpha>_def list_it_alt .

    show "finite (\<alpha> s)"
      unfolding \<alpha>_def by (simp add: map.finite[OF I'])
  qed

  lemma dflt_basic_ops_impl: "StdBasicSet dflt_basic_ops"
    apply (rule StdBasicSet.intro)
    apply (simp_all add: icf_rec_unf)
    apply (rule empty_impl memb_impl ins_impl
      ins_dj_impl delete_impl 
      list_it_impl[unfolded SetByMapDefs.list_it_def[abs_def]]
    )+
    done
end


locale OSetByOMapDefs = SetByMapDefs ops +
  map: StdBasicOMapDefs ops
  for ops :: "('x::linorder,unit,'s,'more) omap_basic_ops_scheme"
begin
  definition ordered_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" 
    where "ordered_list_it s c f \<sigma>0 
    \<equiv> it_to_it (map.ordered_list_it s) c (f o fst) \<sigma>0"
    (*where "list_it s c f \<sigma>0 \<equiv> it_to_it (map.list_it s) c (f o fst) \<sigma>0"*)
  local_setup \<open>Locale_Code.lc_decl_del @{term ordered_list_it}\<close>

  definition rev_list_it :: "'s \<Rightarrow> ('x,'x list) set_iterator" 
    where "rev_list_it s c f \<sigma>0 \<equiv> it_to_it (map.rev_list_it s) c (f o fst) \<sigma>0"
    (*where "rev_list_it s c f \<sigma>0 \<equiv> map.rev_iterateoi s c (f o fst) \<sigma>0"*)
  local_setup \<open>Locale_Code.lc_decl_del @{term rev_list_it}\<close>


  definition [icf_rec_def]: "dflt_basic_oops \<equiv> 
    set_basic_ops.extend dflt_basic_ops \<lparr>
      bset_op_ordered_list_it = ordered_list_it,
      bset_op_rev_list_it = rev_list_it
      \<rparr>"
  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_basic_oops}\<close>

end

setup \<open>
  (Record_Intf.add_unf_thms_global @{thms 
    OSetByOMapDefs.ordered_list_it_def[abs_def]
    OSetByOMapDefs.rev_list_it_def[abs_def]
  })
\<close> 

(*lemmas [code_unfold] = OSetByOMapDefs.ordered_list_it_def[abs_def]
  OSetByOMapDefs.rev_list_it_def[abs_def]*)

locale OSetByOMap = OSetByOMapDefs ops +
  SetByMap ops + map: StdBasicOMap ops
  for ops :: "('x::linorder,unit,'s,'more) omap_basic_ops_scheme"
begin
  lemma ordered_list_it_impl: "poly_set_iterateoi \<alpha> invar ordered_list_it"
  proof
    fix s
    assume I: "invar s"
    hence I': "map.invar s" unfolding invar_def .

    have S: "\<And>f. (\<lambda>(x,_). f x) = (\<lambda>xy. f (fst xy))"
      by auto

    have A: "\<And>s. ordered_list_it s = map_iterator_dom (map.iterateoi s)"
      unfolding ordered_list_it_def[abs_def] 
        map_iterator_dom_def set_iterator_image_alt_def map.iterateoi_def 
      by (simp add: S comp_def)
  
    from map_iterator_linord_dom_correct[OF map.iterateoi_correct[OF I']] 
    show "set_iterator_linord (ordered_list_it s) (\<alpha> s)"
      unfolding \<alpha>_def A .

    show "finite (\<alpha> s)"
      unfolding \<alpha>_def by (simp add: map.finite[OF I'])
  qed

  lemma rev_list_it_impl: "poly_set_rev_iterateoi \<alpha> invar rev_list_it"
  proof
    fix s
    assume I: "invar s"
    hence I': "map.invar s" unfolding invar_def .

    have S: "\<And>f. (\<lambda>(x,_). f x) = (\<lambda>xy. f (fst xy))"
      by auto

    have A: "\<And>s. rev_list_it s = map_iterator_dom (map.rev_iterateoi s)"
      unfolding rev_list_it_def[abs_def] 
        map_iterator_dom_def set_iterator_image_alt_def map.rev_iterateoi_def 
      by (simp add: S comp_def)
  
    from map_iterator_rev_linord_dom_correct[
      OF map.rev_iterateoi_correct[OF I']] 
    show "set_iterator_rev_linord (rev_list_it s) (\<alpha> s)"
      unfolding \<alpha>_def A .

    show "finite (\<alpha> s)"
      unfolding \<alpha>_def by (simp add: map.finite[OF I'])

  qed

  lemma dflt_basic_oops_impl: "StdBasicOSet dflt_basic_oops"
  proof -
    interpret aux: StdBasicSet dflt_basic_ops by (rule dflt_basic_ops_impl)

    show ?thesis
      apply (rule StdBasicOSet.intro)
      apply (rule StdBasicSet.intro)
      apply icf_locales
      apply (simp_all add: icf_rec_unf)
      apply (rule 
        ordered_list_it_impl[unfolded ordered_list_it_def[abs_def]] 
        rev_list_it_impl[unfolded rev_list_it_def[abs_def]]
      )+
      done
  qed
end

sublocale SetByMap < basic: StdBasicSet "dflt_basic_ops" 
  by (rule dflt_basic_ops_impl)

sublocale OSetByOMap < obasic: StdBasicOSet "dflt_basic_oops" 
  by (rule dflt_basic_oops_impl)

lemma proper_it'_map2set: "proper_it' it it' 
  \<Longrightarrow> proper_it' (\<lambda>s c f. it s c (f o fst)) (\<lambda>s c f. it' s c (f o fst))"
  unfolding proper_it'_def
  apply clarsimp
  apply (drule_tac x=s in spec)
  apply (erule proper_itE)
  apply (rule proper_itI)
  apply (auto simp add: foldli_map[symmetric] intro!: ext)
  done


end
