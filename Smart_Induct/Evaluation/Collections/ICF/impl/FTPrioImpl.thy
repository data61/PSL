section \<open>\isaheader{Implementation of Priority Queues by Finger Trees}\<close>
theory FTPrioImpl
imports FTAnnotatedListImpl 
  "../gen_algo/PrioByAnnotatedList"
begin
(*@impl Prio
  @type ('a,'p::linorder) alprioi
  @abbrv alprioi
  Priority queues based on 2-3 finger trees.
*)

type_synonym ('a,'p) alprioi = "(unit, ('a, 'p) Prio) FingerTree"

setup Locale_Code.open_block
interpretation alprio_ga: alprio ft_ops by unfold_locales
setup Locale_Code.close_block

definition [icf_rec_def]: "alprioi_ops \<equiv> alprio_ga.alprio_ops"

setup Locale_Code.open_block
interpretation alprioi: StdPrio alprioi_ops
  unfolding alprioi_ops_def
  by (rule alprio_ga.alprio_ops_impl)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "alprioi"\<close>


definition test_codegen where "test_codegen \<equiv> (
  alprioi.empty,
  alprioi.isEmpty,
  alprioi.insert,
  alprioi.find,
  alprioi.delete,
  alprioi.meld
)"

export_code test_codegen checking SML

end
