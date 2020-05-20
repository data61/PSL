(*<*)
theory Consensus_Types
imports Main
begin
(*>*)

subsection \<open>Consensus: types\<close>
typedecl process

text \<open>Once we start taking maximums (e.g. in Last\_Voting), we will need the process set to be finite\<close>
axiomatization where process_finite: 
  (* "class.finite TYPE(process)" *)
  "OFCLASS(process, finite_class)"

instance process :: finite by (rule process_finite)

abbreviation
  "N \<equiv> card (UNIV::process set)"   \<comment> \<open>number of processes\<close>

typedecl val     \<comment> \<open>Type of values to choose from\<close>

type_synonym round = nat

end
