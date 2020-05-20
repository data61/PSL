(*  Title:       $AFP/Nested_Multisets_Ordinals/zmultiset_simprocs.ML
    Author:      Mathias Fleury <mathias.fleury at mpi-inf.mpg.de>, 2017

Simprocs for zmultisets, based on Larry Paulson's simprocs for natural numbers
and numerals.
*)

signature ZMULTISET_SIMPROCS =
sig
  val subset_cancel_zmsets: Proof.context -> cterm -> thm option
  val subseteq_cancel_zmsets: Proof.context -> cterm -> thm option
end;

structure ZMultiset_Simprocs : ZMULTISET_SIMPROCS =
struct

structure Subset_Cancel_Multiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name subset_zmset}
  val dest_bal = HOLogic.dest_bin @{const_name subset_zmset} dummyT
  val bal_add1 = @{thm zmset_subset_add_iff1[unfolded repeat_zmset_iterate_add]} RS trans
  val bal_add2 = @{thm zmset_subset_add_iff2[unfolded repeat_zmset_iterate_add]} RS trans
);

structure Subseteq_Cancel_Multiset = Cancel_Fun
 (open Cancel_Data
  val mk_bal   = HOLogic.mk_binrel @{const_name subseteq_zmset}
  val dest_bal = HOLogic.dest_bin @{const_name subseteq_zmset} dummyT
  val bal_add1 = @{thm zmset_subseteq_add_iff1[unfolded repeat_zmset_iterate_add]} RS trans
  val bal_add2 = @{thm zmset_subseteq_add_iff2[unfolded repeat_zmset_iterate_add]} RS trans
);

val subset_cancel_zmsets = Subset_Cancel_Multiset.proc;
val subseteq_cancel_zmsets = Subseteq_Cancel_Multiset.proc;

end
