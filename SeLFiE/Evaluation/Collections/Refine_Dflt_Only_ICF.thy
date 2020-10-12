section \<open>\isaheader{Entry Point with only the ICF}\<close>
theory Refine_Dflt_Only_ICF
imports
  Refine_Monadic.Refine_Monadic
  "ICF/Collections"
  "Lib/Code_Target_ICF"
begin

text \<open>Contains the Monadic Refinement Framework and the original
  Isabelle Collection Framework. The generic collection framework is
  not included\<close>

local_setup \<open>
  let open Autoref_Fix_Rel in
    declare_prio "RBT-set" @{term "\<langle>R\<rangle>rs.rel"} PR_LAST #>
    declare_prio "Hash-set" @{term "\<langle>R\<rangle>hs.rel"} PR_LAST #>
    declare_prio "List-set" @{term "\<langle>R\<rangle>lsi.rel"} PR_LAST
  end
\<close>

local_setup \<open>
  let open Autoref_Fix_Rel in
    declare_prio "RBT-map" @{term "\<langle>Rk,Rv\<rangle>rm.rel"} PR_LAST #>
    declare_prio "Hash-map" @{term "\<langle>Rk,Rv\<rangle>hm.rel"} PR_LAST #>
    declare_prio "List-map" @{term "\<langle>Rk,Rv\<rangle>lmi.rel"} PR_LAST
  end
\<close>

end
