(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
signature BNF_ACCESS =
sig
(* thms *)
val induct_thms : Proof.context -> string list -> thm list
val case_thms : Proof.context -> string list -> thm list
val distinct_thms : Proof.context -> string list -> thm list list
val inject_thms : Proof.context -> string list -> thm list list
val set_simps : Proof.context -> string list -> thm list list
val case_simps : Proof.context -> string list -> thm list list
val map_simps : Proof.context -> string list -> thm list list
val map_comps : Proof.context -> string list -> thm list

(* terms *)
val map_terms : Proof.context -> string list -> term list
val set_terms : Proof.context -> string list -> term list list
val case_consts : Proof.context -> string list -> term list
val constr_terms : Proof.context -> string -> term list

(* types *)
val constr_argument_types : Proof.context -> string list -> typ list list list
val bnf_types : Proof.context -> string list -> typ list

end

structure Bnf_Access : BNF_ACCESS =
struct

fun constr_terms lthy = BNF_FP_Def_Sugar.fp_sugar_of lthy
  #> the #> #fp_ctr_sugar #> #ctr_sugar #> #ctrs

fun induct_thms lthy =
  map (hd o #co_inducts o the o #fp_co_induct_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun case_thms lthy =
  map (#exhaust o #ctr_sugar o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun set_simps lthy = 
  map (#set_thms o #fp_bnf_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun distinct_thms lthy =
  map (#distincts o #ctr_sugar o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun inject_thms lthy =
  map (#injects o #ctr_sugar o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun case_simps lthy = 
  map (#case_thms o #ctr_sugar o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun map_simps lthy = 
  map (#map_thms o #fp_bnf_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun map_comps lthy tycos = hd tycos
  |> (#bnfs o #fp_res o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)
  |> map (BNF_Def.map_comp_of_bnf)

fun constr_argument_types lthy = 
  map (#ctrXs_Tss o #fp_ctr_sugar o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun bnf_types lthy = 
  map (#X o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)

fun map_terms lthy tycos = hd tycos
  |> (#bnfs o #fp_res o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)
  |> map (BNF_Def.map_of_bnf)

fun set_terms lthy tycos = hd tycos
  |> (#bnfs o #fp_res o the o BNF_FP_Def_Sugar.fp_sugar_of lthy)
  |> map (BNF_Def.sets_of_bnf)

fun case_consts lthy = map (BNF_FP_Def_Sugar.fp_sugar_of lthy
  #> the #> #fp_ctr_sugar #> #ctr_sugar #> #casex)

end
