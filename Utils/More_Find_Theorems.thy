(* This file provides an interface of find_theorem for PSL.                               *)
(* This file does not include significant code duplication with the Isabelle source code. *)
theory More_Find_Theorems
imports Isabelle_Utils
begin

ML{* signature FIND_THEOREMS2 =
sig
  include FIND_THEOREMS;
  type context;
  type ref;
  type get_rules = context -> thm -> (ref * thm) list;
  type get_rule_names = context -> thm -> string list;
  val get_criterion             : string -> string -> (bool * 'a criterion) list;
  val name_to_rules             : context -> thm -> string -> string -> (ref * thm) list;
  val names_to_rules            : context -> thm -> string -> string list -> (ref * thm) list
  val get_rule_names            : get_rules -> context -> thm -> xstring list;
  val get_simp_rules            : get_rules;
  val get_induct_rules          : get_rules;
  val get_coinduction_rules     : get_rules;
  (* These get_(elim, intro, dest)_rules may not be powerful enough. *)
  val get_elim_rules            : get_rules;
  val get_intro_rules           : get_rules;
  val get_dest_rules            : get_rules;
  val get_split_rules           : get_rules;
  val get_simp_rule_names       : get_rule_names;
  val get_induct_rule_names     : get_rule_names;
  val get_coinduction_rule_names: get_rule_names;
  val get_elim_rule_names       : get_rule_names;
  val get_intro_rule_names      : get_rule_names;
  val get_dest_rule_names       : get_rule_names;
  val get_split_rule_names      : get_rule_names;
end;
*}

ML{* structure Find_Theorems2 =
struct

open Find_Theorems;

type context = Proof.context;
type ref = Facts.ref;

fun get_criterion kind_name name = [(true, Name name), (true, Name kind_name)];

fun name_to_rules ctxt goal kind_name name =
  find_theorems ctxt (SOME goal) NONE true (get_criterion kind_name name) |> snd;

fun names_to_rules ctxt goal kind_name names = names
  |> map (name_to_rules ctxt goal kind_name)
  |> flat
  |> distinct (Thm.eq_thm o Utils.map_pair snd);

fun get_rule_names (get_rules:context -> thm -> (ref * thm) list) ctxt goal =
  let
    val related_rules          = get_rules ctxt goal;
    val related_rule_names     = map (Facts.string_of_ref o fst) related_rules;
    fun get_thm  thm_nm        = SOME (Proof_Context.get_thm  ctxt thm_nm) handle ERROR _ => NONE;
    fun get_thms thm_nm        = SOME (Proof_Context.get_thms ctxt
      (Utils.rm_parentheses_with_contents_in_the_end thm_nm)) handle ERROR _ => NONE;
    fun cannot_get_thm  thm_nm = is_none (get_thm thm_nm);
    fun cannot_get_thms thm_nm = is_none (get_thms thm_nm);
    fun cannot_get thm_nm      = cannot_get_thm thm_nm andalso cannot_get_thms thm_nm;
    val available_rule_names   = filter_out cannot_get related_rule_names;
  in
    available_rule_names
  end;

fun get_simp_rules (ctxt:context) (goal:thm) =
  let
    val const_names   = Isabelle_Utils.get_const_names_in_thm goal;
    val related_rules = names_to_rules ctxt goal "" const_names;
    val simpset_thms  = ctxt |> simpset_of |> Raw_Simplifier.dest_ss |> #simps |> map snd;
    fun eq_test (thm1, (_, thm2)) = Thm.eq_thm (thm1, thm2);
    val unique_rules  = subtract eq_test simpset_thms related_rules;
  in
    unique_rules : (Facts.ref * thm) list
  end;

fun get_simp_rule_names ctxt goal = get_rule_names get_simp_rules ctxt goal : string list;

fun get_induct_rules (ctxt:context) (goal:thm) =
  let
    val const_names  = Isabelle_Utils.get_const_names_in_thm goal : string list;
    val induct_rules = names_to_rules ctxt goal ".induct" const_names;
  in
    induct_rules : (Facts.ref * thm) list
  end;
fun get_induct_rule_names ctxt goal = get_rule_names get_induct_rules ctxt goal : string list;

fun get_coinduction_rules (ctxt:context) (goal:thm) =
  let
    val const_names   = Isabelle_Utils.get_const_names_in_thm goal : string list;
    fun get_coinduct_rules post = names_to_rules ctxt goal post const_names;
    val coinduct_rules1 = get_coinduct_rules ".coinduct";
    val coinduct_rules2 = get_coinduct_rules ".coinduct_strong";
  in
    coinduct_rules1 @ coinduct_rules2: (Facts.ref * thm) list
  end;
fun get_coinduction_rule_names ctxt goal = get_rule_names get_coinduction_rules ctxt goal : string list;

fun get_elim_rules  ctxt goal = find_theorems ctxt (SOME goal) NONE true [(true, Elim)] |> snd;
fun get_intro_rules ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Intro)] |> snd;
fun get_dest_rules  ctxt goal = find_theorems ctxt (SOME goal) (SOME 100) true [(true, Dest)] |> snd;
        
fun get_elim_rule_names  ctxt goal = get_rule_names get_elim_rules  ctxt goal : string list;
fun get_intro_rule_names ctxt goal = get_rule_names get_intro_rules ctxt goal : string list;
fun get_dest_rule_names  ctxt goal = get_rule_names get_dest_rules  ctxt goal : string list;

fun get_split_rules ctxt goal =
  let
    (* For split, we need to use typ_names instead of const_names. *)
    val used_typ_names = Isabelle_Utils.get_typ_names_in_thm goal;
    val related_rules  = names_to_rules ctxt goal "split" used_typ_names
  in
    related_rules : (Facts.ref * thm) list
  end;

fun get_split_rule_names ctxt goal = get_rule_names get_split_rules ctxt goal;

end;
*}

end