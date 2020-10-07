section \<open>\isaheader{Generic Collection Framework (Internal)}\<close>
theory GenCF
imports 
  "Impl/Impl_List_Set" 
  "Impl/Impl_List_Map" 
  "Impl/Impl_RBT_Map" 
  "Impl/Impl_Array_Map"
  "Impl/Impl_Array_Hash_Map"
  "Impl/Impl_Array_Stack"
  "Impl/Impl_Cfun_Set"
  "Impl/Impl_Bit_Set"
  "Impl/Impl_Uv_Set"
  "Gen/Gen_Set"
  "Gen/Gen_Map"
  "Gen/Gen_Map2Set"
  "Gen/Gen_Comp"
  "Gen/Gen_Hash"
  "../Lib/Code_Target_ICF"
begin

  text \<open>Use one of the \<open>Refine_Dflt\<close>-theories as entry-point!\<close>

  text \<open>Useful Abbreviations\<close>
  abbreviation "dflt_rs_rel \<equiv> map2set_rel dflt_rm_rel"
  abbreviation "iam_set_rel \<equiv> map2set_rel iam_map_rel"
  abbreviation "dflt_ahs_rel \<equiv> map2set_rel dflt_ahm_rel"

  abbreviation ahs_rel where "ahs_rel bhc \<equiv> (map2set_rel (ahm_rel bhc))"

end
