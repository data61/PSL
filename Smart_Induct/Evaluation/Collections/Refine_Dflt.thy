section \<open>\isaheader{Default Setup}\<close>
theory Refine_Dflt
imports 
  Refine_Monadic.Refine_Monadic
  "GenCF/GenCF"
  "Lib/Code_Target_ICF"
begin

text \<open>Configurations\<close>

lemmas tyrel_dflt_nat_set = 
  ty_REL[where 'a="nat set" and R="\<langle>Id\<rangle>dflt_rs_rel"]

lemmas tyrel_dflt_bool_set = 
  ty_REL[where 'a="bool set" and R="\<langle>Id\<rangle>list_set_rel"]

lemmas tyrel_dflt_nat_map = 
  ty_REL[where R="\<langle>nat_rel,Rv\<rangle>dflt_rm_rel"] for Rv

lemmas tyrel_dflt_old = tyrel_dflt_nat_set tyrel_dflt_bool_set tyrel_dflt_nat_map

lemmas tyrel_dflt_linorder_set = 
  ty_REL[where R="\<langle>Id::('a::linorder\<times>'a) set\<rangle>dflt_rs_rel"]
  
lemmas tyrel_dflt_linorder_map = 
  ty_REL[where R="\<langle>Id::('a::linorder\<times>'a) set,R\<rangle>dflt_rm_rel"] for R
  
lemmas tyrel_dflt_bool_map = 
  ty_REL[where R="\<langle>Id::(bool\<times>bool) set,R\<rangle>list_map_rel"] for R

lemmas tyrel_dflt = tyrel_dflt_linorder_set tyrel_dflt_bool_set tyrel_dflt_linorder_map tyrel_dflt_bool_map

declare tyrel_dflt[autoref_tyrel]



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

text \<open>Quick test of setup:\<close>
context begin
private schematic_goal test_dflt_tyrel1: "(?c::?'c,{1,2,3::int})\<in>?R" (*RBT*)
  by autoref
private lemmas asm_rl[of "_\<in>\<langle>int_rel\<rangle>dflt_rs_rel", OF test_dflt_tyrel1]

private schematic_goal test_dflt_tyrel2: "(?c::?'c,{True, False})\<in>?R" (*List*)
  by autoref
private lemmas asm_rl[of "_\<in>\<langle>bool_rel\<rangle>list_set_rel", OF test_dflt_tyrel2]

private schematic_goal test_dflt_tyrel3: "(?c::?'c,[1::int\<mapsto>0::nat])\<in>?R" (*RBT*)
  by autoref
private lemmas asm_rl[of "_\<in>\<langle>int_rel,nat_rel\<rangle>dflt_rm_rel", OF test_dflt_tyrel3]

private schematic_goal test_dflt_tyrel4: "(?c::?'c,[False\<mapsto>0::nat])\<in>?R" (*List*)
  by autoref
private lemmas asm_rl[of "_\<in>\<langle>bool_rel,nat_rel\<rangle>list_map_rel", OF test_dflt_tyrel4]

end





end
