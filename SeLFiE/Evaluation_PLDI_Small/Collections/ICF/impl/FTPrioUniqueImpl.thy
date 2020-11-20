section \<open>\isaheader{Implementation of Unique Priority Queues by Finger Trees}\<close>
theory FTPrioUniqueImpl
imports 
  FTAnnotatedListImpl 
  "../gen_algo/PrioUniqueByAnnotatedList"
begin
(*@impl PrioUnique
  @type ('a::linorder,'p::linorder) aluprioi
  @abbrv aluprioi
  Unique priority queues based on 2-3 finger trees.
*)

subsection "Definitions"

type_synonym ('a,'b) aluprioi = "(unit, ('a, 'b) LP) FingerTree"

setup Locale_Code.open_block
interpretation aluprio_ga: aluprio ft_ops by unfold_locales
setup Locale_Code.close_block

definition [icf_rec_def]: "aluprioi_ops \<equiv> aluprio_ga.aluprio_ops"

setup Locale_Code.open_block
interpretation aluprioi: StdUprio aluprioi_ops
  unfolding aluprioi_ops_def
  by (rule aluprio_ga.aluprio_ops_impl)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "aluprioi"\<close>

definition test_codegen where "test_codegen \<equiv> (
  aluprioi.empty,
  aluprioi.isEmpty,
  aluprioi.insert,
  aluprioi.pop,
  aluprioi.prio
)"

export_code test_codegen checking SML

end
