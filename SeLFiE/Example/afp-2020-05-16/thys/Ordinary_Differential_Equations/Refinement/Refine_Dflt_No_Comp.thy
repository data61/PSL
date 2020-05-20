section \<open>Default Setup\<close>
theory Refine_Dflt_No_Comp
imports
  Refine_Monadic.Refine_Monadic
  GenCF_No_Comp
  Collections.Code_Target_ICF
begin

text \<open>TODO: need to keep in sync with \<open>../../Collections/Refine_Dflt\<close> ...\<close>

text \<open> Configurations \<close>

lemmas tyrel_dflt_nat_set[autoref_tyrel] = 
  ty_REL[where 'a="nat set" and R="\<langle>Id\<rangle>dflt_rs_rel"]

lemmas tyrel_dflt_bool_set[autoref_tyrel] = 
  ty_REL[where 'a="bool set" and R="\<langle>Id\<rangle>list_set_rel"]

lemmas tyrel_dflt_nat_map[autoref_tyrel] = 
  ty_REL[where R="\<langle>nat_rel,Rv\<rangle>dflt_rm_rel"] for Rv

lemmas tyrel_dflt = tyrel_dflt_nat_set tyrel_dflt_bool_set tyrel_dflt_nat_map


local_setup \<open>
  let open Autoref_Fix_Rel in
    declare_prio "Gen-AHM-map-hashable" 
      @{term "\<langle>Rk::(_\<times>_::hashable) set,Rv\<rangle>ahm_rel bhc"} PR_LAST #>
    declare_prio "Gen-RBT-map-linorder" 
      @{term "\<langle>Rk::(_\<times>_::linorder) set,Rv\<rangle>rbt_map_rel lt"} PR_LAST #>
    declare_prio "Gen-AHM-map" @{term "\<langle>Rk,Rv\<rangle>ahm_rel bhc"} PR_LAST #>
    declare_prio "Gen-RBT-map" @{term "\<langle>Rk,Rv\<rangle>rbt_map_rel lt"} PR_LAST
  end
\<close>


text "Fallbacks"
local_setup \<open>
  let open Autoref_Fix_Rel in
    declare_prio "Gen-List-Set" @{term "\<langle>R\<rangle>list_set_rel"} PR_LAST #>
    declare_prio "Gen-List-Map" @{term "\<langle>R\<rangle>list_map_rel"} PR_LAST
  end
\<close>

end
