section \<open>Graphs by Hashmaps\<close>
theory HashGraphImpl
imports 
  GraphByMap 
begin


text \<open>
  Abbreviation: hlg
\<close>

type_synonym ('V,'E) hlg = 
  "('V,('V,'E ls) HashMap.hashmap) HashMap.hashmap"

setup Locale_Code.open_block
interpretation hh_mvif: g_value_image_filter_loc hm_ops hm_ops 
  by unfold_locales
interpretation hlg_gbm: GraphByMap hm_ops hm_ops ls_ops 
  "hh_mvif.g_value_image_filter"
  by unfold_locales
setup Locale_Code.close_block

definition [icf_rec_def]: "hlg_ops \<equiv> hlg_gbm.gbm_ops"

setup Locale_Code.open_block
interpretation hlg: StdGraph hlg_ops
  unfolding hlg_ops_def
  by (rule hlg_gbm.gbm_ops_impl)
setup Locale_Code.close_block
setup \<open>ICF_Tools.revert_abbrevs "HashGraphImpl.hlg"\<close>

thm map_iterator_dom_def set_iterator_image_def
  set_iterator_image_filter_def

definition test_codegen where "test_codegen \<equiv> (
  hlg.empty,
  hlg.add_node,
  hlg.delete_node,
  hlg.add_edge,
  hlg.delete_edge,
  hlg.from_list,
  hlg.to_list,
  hlg.nodes_it,
  hlg.edges_it,
  hlg.succ_it
)"

export_code test_codegen in SML

end
