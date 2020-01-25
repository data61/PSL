(*  Title:      Smart_Induct/src/Dynamic_Induct.thy
    Author:     Yutaka Nagashima, CIIRC, CTU, University of Innsbruck
*)
structure Dynamic_Induct =
struct

structure Induct_Seed  =
struct

datatype modifier = 
  On        of string
| Arbitrary of string
| Rule      of string;

type modifiers = modifier list;

fun get_ons   (fvars:string list) = map On fvars;
fun get_arbs  (fvars:string list) = map Arbitrary fvars;
fun get_rules (rules:string list) = map Rule rules;

fun order' ordered [] = ordered
 |  order' (ons, arbs, rules) (On        var :: mods) = order' (ons @ [On var], arbs,                   rules              ) mods
 |  order' (ons, arbs, rules) (Arbitrary var :: mods) = order' (ons,            arbs @ [Arbitrary var], rules              ) mods
 |  order' (ons, arbs, rules) (Rule     rule :: mods) = order' (ons,            arbs,                   rules @ [Rule rule]) mods;

fun order (mods:modifiers) = (*(ons, arbs, rules)*)
  order' ([],[],[]) mods : (modifiers * modifiers * modifiers)

fun get_name (On        name) = name
  | get_name (Arbitrary name) = name
  | get_name (Rule      name) = name;

val get_names = map get_name;

fun mods_have_two_rules' (Rule _::mods) acc = mods_have_two_rules' mods (acc + 1)
  | mods_have_two_rules' (_     ::mods) acc = mods_have_two_rules' mods acc
  | mods_have_two_rules' []             acc = acc;

fun mods_have_more_than_one_rule mods = mods_have_two_rules' mods 0 > 1;

fun filter_out_mods_w_too_many_rules (modss:modifiers Seq.seq) =
    Seq.filter (not o mods_have_more_than_one_rule) modss: modifiers Seq.seq;

fun mods_to_string (mods:modifiers): string =
  let 
    val prefix_if_nonnil = Utils.prefix_if_nonempty;
  in
    mods |> order |> (fn (ons, arbs, rules) =>
    get_names ons
    @ prefix_if_nonnil "arbitrary:" (get_names arbs)
    @ prefix_if_nonnil "rule:"      (get_names rules))
    |> Dynamic_Utils.get_meth_nm ""
  end;

fun get_all_modifiers (state:Proof.state) =
  let
    val {context: Proof.context, goal: thm,...} = Proof.goal state;
    val free_var_names   = Isabelle_Utils.get_free_var_names_in_1st_subg goal;
    val induct_rules     = Find_Theorems2.get_induct_rule_names context goal : string list;
    val all_induct_mods  = get_ons free_var_names @ get_arbs free_var_names @ get_rules induct_rules;
  in
    all_induct_mods : modifiers
  end;

val pick_vars = filter     (fn modi => case modi of On _ => true | _ => false);
val dump_vars = filter_out (fn modi => case modi of On _ => true | _ => false);

fun reordered_mods (mods:modifiers)=
  let
    val vars   = pick_vars mods : modifiers;
    val varss  = Nitpick_Util.all_permutations vars : modifiers list;
    val others = dump_vars mods : modifiers;
    val combs  = map (fn vs => vs @ others) varss;
  in
    combs:modifiers list
  end;

end;

(* ITG: Induct_Tactic_Generator. *)
structure ITG : DYNAMIC_TACTIC_GENERATOR = mk_Dynamic_Tactic_Generator (Induct_Seed);

fun pst_to_modifiers (state:Proof.state) =
  let
    val all_modifiers  = ITG.get_all_modifiers state : ITG.modifiers;
    (*We need to consider all permutations because induct is order sensitive.*)
    val all_modifierss = Seq2.powerset (Seq.of_list all_modifiers)
                      |> Seq.map Seq.list_of
                      |> Seq.map Induct_Seed.reordered_mods
                      |> Seq.map Seq.of_list
                      |> Seq.flat
                      |> Induct_Seed.filter_out_mods_w_too_many_rules
                      |> Seq.chop 10000 |> fst : ITG.modifiers list;
    val _ = tracing ("smart_induct produced " ^ Int.toString (length all_modifierss) ^ " combinations of arguments for the induct method." )
  in
    all_modifierss: ITG.modifiers list
  end;

structure IS = Induct_Seed;




fun modifiers_to_str (mods: IS.modifiers) : string =
  enclose "apply (" ")" ("induct" ^ IS.mods_to_string mods);

structure DU = Dynamic_Utils;
structure IU = Isabelle_Utils;

fun str_to_nontac (meth:string) : DU.state DU.nontac =
  IU.TIMEOUT_in 3.0 (Utils.try_with (K Seq.empty) DU.string_to_nontac_on_pstate meth);

fun state_to_nontacs (pst:DU.state): DU.state DU.nontac list = pst
  |> pst_to_modifiers
  |> map (fn mods => "induct" ^ IS.mods_to_string mods)
  |> map (try str_to_nontac)
  |> Utils.somes;

fun get_fst_result (pst:Proof.state) (nontac: Proof.state DU.nontac) : DU.state option =
      (try nontac pst: DU.state Seq.seq option)
  >>= (try Seq.hd: DU.state Seq.seq -> Dynamic_Utils.state option);

fun mods_return_something (pst:Proof.state) (mods: IS.modifiers) =
  Option.isSome (get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)));

fun pst_to_functioning_modifiers (pst:Proof.state) =
  let
    val modifierss     = pst_to_modifiers pst                         : ITG.modifiers list;
    fun tag_mods mods  = (mods_return_something pst mods, mods)       : (bool * ITG.modifiers);
    val tagged_modss   = Par_List.map tag_mods modifierss             : (bool * ITG.modifiers) list;
    val filtered_modss = filter (fst) tagged_modss |> map snd         : ITG.modifiers list;
    val _              = tracing ("... out of which " ^ Int.toString (length filtered_modss) ^ " of them return some results.");
  in
    filtered_modss
  end;

fun mods_to_returned_thm_option (pst:Proof.state) (mods:IS.modifiers) =
  let
    val returned_pst_option = get_fst_result pst (str_to_nontac ("induct " ^ IS.mods_to_string mods)): Proof.state option;
    val returend_thm_option = Option.map IU.proof_state_to_thm returned_pst_option: thm option;
  in
    returend_thm_option
  end;

end;