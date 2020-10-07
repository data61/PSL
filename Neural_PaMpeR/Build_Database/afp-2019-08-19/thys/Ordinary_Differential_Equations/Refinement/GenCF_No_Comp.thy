section \<open>Generic Collection Framework (Internal)\<close>
theory GenCF_No_Comp
imports
  Collections.Impl_List_Set
  Collections.Impl_List_Map
  Collections.Impl_RBT_Map
  Collections.Impl_Array_Map
  Collections.Impl_Array_Hash_Map
  Collections.Impl_Array_Stack
  Collections.Impl_Cfun_Set
  Collections.Impl_Bit_Set
  Collections.Impl_Uv_Set
  Collections.Gen_Set
  Collections.Gen_Map
  Collections.Gen_Map2Set
  Collections.Gen_Hash
  Collections.Code_Target_ICF
  Automatic_Refinement.Refine_Lib
  "HOL-Analysis.Analysis"
begin

  text \<open>TODO: need to keep in sync with \<open>../../Collections/GenCF/CenCF\<close> ...\<close>

  text \<open> Use one of the \<open>Refine_Dflt\<close>-theories as entry-point! \<close>

  text \<open> Useful Abbreviations \<close>
  abbreviation "dflt_rs_rel \<equiv> map2set_rel dflt_rm_rel"
  abbreviation "iam_set_rel \<equiv> map2set_rel iam_map_rel"
  abbreviation "dflt_ahs_rel \<equiv> map2set_rel dflt_ahm_rel"

  abbreviation ahs_rel where "ahs_rel bhc \<equiv> (map2set_rel (ahm_rel bhc))"

end
