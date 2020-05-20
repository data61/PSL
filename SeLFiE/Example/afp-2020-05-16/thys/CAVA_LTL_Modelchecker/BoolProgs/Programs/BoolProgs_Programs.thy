theory BoolProgs_Programs
imports
  BoolProgs_Philosophers
  BoolProgs_ReaderWriter
  BoolProgs_Simple
  BoolProgs_LeaderFilters
  CAVA_Base.Code_String
  (*"HOL-Library.List_lexord"*)
begin

definition progs :: "(String.literal, String.literal \<times> String.literal \<times> (nat \<Rightarrow> (bprog \<times> config) \<times> const_map \<times> fun_map)) mapping"
where "progs =  mapping_from_list [
                (STR ''RW'', (STR ''Reader/Writer'', STR ''# Readers and # Writers'', \<lambda>n. (reader_writer n n, rw_const n, rw_fun n))),
                (STR ''S'', (STR ''Simple Variable Setting'', STR ''# Variables'', \<lambda>n. (simple n, simple_const n, simple_fun n))),
                (STR ''P'', (STR ''Dining Philosophers'', STR ''# Philosophers'', \<lambda>n. (philosophers n, phil_const n, phil_fun n))),
                (STR ''LF'', (STR ''Leader Filters'', STR ''# Processes'', \<lambda>n. (leader_filters n, lf_const n, lf_fun n)))
              ]"

(* ensure this is an actual key *)
definition "default_prog \<equiv> STR ''S''"

definition keys_of_map :: "(String.literal, 'a) mapping \<Rightarrow> String.literal list" where
  "keys_of_map \<equiv> Mapping.ordered_keys"

definition chose_prog :: "String.literal \<Rightarrow> nat \<Rightarrow> String.literal \<times> String.literal \<times> (bprog \<times> config) \<times> const_map \<times> fun_map"
where "chose_prog P n = (case Mapping.lookup progs P of 
                          Some (descr, ndescr, p) \<Rightarrow> (descr, ndescr, p n) 
                        | None \<Rightarrow> let (descr, ndescr, p) = the (Mapping.lookup progs default_prog)
                                 in (descr + STR '' (fallback)'', ndescr, p n))"

definition list_progs :: "(String.literal \<times> String.literal \<times> String.literal) list" where
  "list_progs \<equiv> let keys = keys_of_map progs in
                map (\<lambda>k. let (descr, ndescr, p) = the (Mapping.lookup progs k)
                         in (k, descr, ndescr)) keys"
end
