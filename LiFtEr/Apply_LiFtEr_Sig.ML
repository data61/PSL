(*  Title:      PSL/LiFtEr/Apply_LiFtEr_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature APPLY_LIFTER =
sig

val update_assert : Inttab.key -> LiFtEr.assrt -> theory -> theory;
val update_ind_mod: Inttab.key -> LiFtEr.assrt -> theory -> theory;
val get_assrt     : Proof.context -> Inttab.key -> LiFtEr.assrt -> theory -> theory;
val get_ind_mod   : Proof.context -> Inttab.key -> LiFtEr.assrt -> theory -> theory;
val activate      : unit -> unit;

end;