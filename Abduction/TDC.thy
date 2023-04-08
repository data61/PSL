(*
 * TDC.thy
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
theory TDC
  imports "../TBC/TBC"
  keywords "top_down_prove" :: thy_goal_stmt
begin


ML\<open> (*Util*)
fun rm_typ (Const (str, _))  = Const (str, dummyT)
  | rm_typ (Free  (str, _))  = Free  (str, dummyT)
  | rm_typ (Var   (idx, _))  = Var   (idx, dummyT)
  | rm_typ (Bound  i      )  = Bound i
  | rm_typ (Abs (str, _, t)) = Abs   (str, dummyT, t)
  | rm_typ (tm1 $ tm2)       = rm_typ tm1 $ rm_typ tm2;

exception NOT_THE_SAME_TERMS;

fun standardize_vnames' (Free (fvar_name, typ)) (mapping:(string * string) list): term * ((string * string) list) =
(*TODO: check if we have a constant of the same name.*)
    if AList.defined (op =) mapping fvar_name
      then (Free (the (AList.lookup (op =) mapping fvar_name), typ), mapping)
      else (Free ("var_" ^ Int.toString (length mapping), typ),
             (fvar_name, "var_" ^ Int.toString (length mapping))::mapping)
  | standardize_vnames' (Abs (_, typ, trm)) mapping =
      let
        val (new_trm, new_mapping) = standardize_vnames' trm mapping
      in
        (Abs ("", typ, new_trm), new_mapping)
      end
  | standardize_vnames' (trm1 $ trm2) mapping =
      let
        val (new_trm1, new_mapping1) = standardize_vnames' trm1 mapping
        val (new_trm2, new_mapping2) = standardize_vnames' trm2 new_mapping1
      in
        (new_trm1 $ new_trm2, new_mapping2)
      end
  | standardize_vnames' trm mapping = (trm, mapping)

fun standardize_vnames trm = fst (standardize_vnames' trm [])

fun numb_of_distinct_atom (is_atom:term -> bool) (trm:term) =
   Term.fold_aterms (fn t => fn acc => if is_atom t then t :: acc else acc) trm []
|> distinct (op =)
|> length;

fun numb_of_distinct_fvars (trm:term) = numb_of_distinct_atom is_Free trm;

fun numb_of_distinct_bvars (trm:term) = numb_of_distinct_atom is_Bound trm;

fun strip_all_body_nested (Const ("Pure.all", _) $ Abs (_, _, t)) = strip_all_body_nested t
  | strip_all_body_nested (Abs (str, typ, trm)) = Abs (str, typ, strip_all_body_nested trm)
  | strip_all_body_nested (trm1 $ trm2) = strip_all_body_nested trm1 $ strip_all_body_nested trm2
  | strip_all_body_nested t = t;

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun get_all_names_in_trm trm =
  Isabelle_Utils.get_cnames_in_trm trm @ Isabelle_Utils.get_abs_names_in_trm trm @ Isabelle_Utils.get_free_var_names_in_trm trm;

fun get_fresh_free_var_name_in_trm' (ctxt:Proof.context) (trm:term) (n:int) =
  let
    val numb_of_fvars = numb_of_distinct_fvars trm + n;
    val fst_candidate = mk_free_variable_of_typ dummyT numb_of_fvars |> dest_Free |> fst: string;
    fun is_free_in_ctxt (name:string) = is_Free (Syntax.read_term ctxt name): bool;
    val all_names_in_trm  = get_all_names_in_trm trm |> distinct (op =): strings;
    fun is_fresh (current_candidate:string) =
        not (member (op =) all_names_in_trm current_candidate) andalso is_free_in_ctxt current_candidate;
    fun add_a_if_taken (current_candidate:string): string =
      if is_fresh current_candidate then current_candidate else add_a_if_taken (current_candidate ^ "a");
    val result = add_a_if_taken fst_candidate: string
  in
    result
  end;

fun get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
  Free (get_fresh_free_var_name_in_trm' ctxt trm n, typ);

fun get_fresh_free_var_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) =
    get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (0:int)

fun get_fresh_free_vars_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
    map (get_fresh_free_var_of_typ_in_trm' ctxt typ trm) (List.tabulate (n, I)): terms;

fun mk_unbound_bound_vars_free_vars (ctxt:Proof.context) (trm:term) =
  let
    val trm = standardize_vnames trm;
    val stripped_trm = strip_all_body_nested trm;
    val bvars = Term.fold_aterms (fn t => fn acc => if is_Bound t then t :: acc else acc) stripped_trm [];
    val distinct_bvars = distinct (op =) bvars: terms;
    val numb_of_distinct_bvars = length distinct_bvars: int;
    val fvars = get_fresh_free_vars_of_typ_in_trm ctxt dummyT stripped_trm numb_of_distinct_bvars: terms;
    val bvar_fvar_pairs = distinct_bvars ~~ fvars: (term * term) list;
    fun replace_bvar (bvar:term, fvar: term) (trm as Bound _)      = if trm = bvar then fvar else trm
      | replace_bvar  p                      (Abs (str, typ, trm)) = Abs (str, typ, replace_bvar p trm)
      | replace_bvar  p                      (trm1 $ trm2)         = replace_bvar p trm1 $ replace_bvar p trm2
      | replace_bvar  _                       trm                  = trm;
    val result = fold replace_bvar bvar_fvar_pairs trm: term;
  in
    result: term
  end;

fun strip_outermost_meta_quantifier (trm as (quantifier $ abstraction)) =
   (case quantifier of
      Const ("Pure.all", _) => (case abstraction of
        Abs (var_name, var_type, _) =>
          (let
             val variable = Term.Free (var_name, var_type)
           in (true, Term.betapply (abstraction, variable))
           end)
      | _ => (false, trm))
    | _ => (false, trm))
  | strip_outermost_meta_quantifier trm = (false, trm);

fun strip_outermost_meta_quantifiers (trm:term) =
    let
      val (worked, res) = strip_outermost_meta_quantifier trm
    in
      if worked
      then
        strip_outermost_meta_quantifiers res
      else
        res
    end;

fun is_prop trm = body_type (type_of trm) = @{typ "prop"}

fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun alpha_eq_over_fvar trm1 trm2 =
  let
    val (non_prop1, non_prop2) = Utils.map_pair remove_Trueprop (trm1, trm2): (term * term);
    val converted1 = standardize_vnames non_prop1
    val converted2 = standardize_vnames non_prop2
  in
    converted1 = converted2
  end;
\<close>

(*** Top_Down_Util ***)
ML\<open>
(*
 * Top_Down_Util.ML
 *
 * Utility functions for our top-down approach, as known as "deep conjecturing".
 *
 * Authors:
 *   Yutaka Nagashima
 *)
(*** signature TOP_DOWN_UTIL ***)
signature TOP_DOWN_UTIL =
sig

val get_subtrms                      : term -> terms;
val get_both_sides_of_eqs_in_term    : term -> (term * term) list;
val get_consts_for_conjecturing      : Proof.context -> term -> terms;
val remove_type_consts               : term -> term;
val read_terms                       : Proof.context -> strings -> terms;
val read_props                       : Proof.context -> strings -> terms;
val check_terms                      : Proof.context -> terms -> terms;
val get_fresh_free_var_of_typ_in_trm : Proof.context -> typ -> term -> term;
val get_fresh_free_vars_of_typ_in_trm: Proof.context -> typ -> term -> int -> terms;
val mk_pst_to_prove_from_term        : Proof.context -> term -> Proof.state;

end;

(*** structure Top_Down_Util ***)
structure Top_Down_Util: TOP_DOWN_UTIL =
struct

(* How to get the list of subterms? *)(*TODO: code-duplication with Proof_Goal_Transformer.*)
fun get_subtrms (Const p:term) = [Const p]
 |  get_subtrms (Free  p:term) = [Free  p]
 |  get_subtrms (Var   p:term) = [Var   p]
 |  get_subtrms (Bound i:term) = [Bound i]
 |  get_subtrms (trm as Abs (_, _, sub)) = trm :: get_subtrms sub
 |  get_subtrms (trm as trm1 $ trm2) = trm :: get_subtrms trm1 @ get_subtrms trm2;

fun get_both_sides_of_eqs_in_term (term:term): (term * term) list =
  let
    val subtrms = get_subtrms term: terms;
    val pairs   = List.mapPartial (try HOLogic.dest_eq) subtrms;
  in
    pairs
  end;

(* How can I find a list of constants used in the definitions of the constants appearing in a term? *)
fun get_consts_for_conjecturing (ctxt:Proof.context) (trm:term) =
  let
    val cnames_in_trm   = Isabelle_Utils.get_cnames_in_trm trm: string list;
    val simp_rules      = map (Find_Theorems2.get_thms_of_name_with_suffix ctxt "simps") cnames_in_trm |> flat;
    val consts_in_simps = map Isabelle_Utils.get_consts_in_thm simp_rules |> flat |> distinct (op =);
  in
    consts_in_simps : terms
  end;

val remove_type_consts = Isabelle_Utils.strip_atyp: term -> term;
fun read_terms ctxt    = List.mapPartial (try (Syntax.read_term ctxt)): strings -> terms;
fun read_props ctxt    = List.mapPartial (try (Syntax.read_prop ctxt)): strings -> terms;
fun check_terms ctxt   = List.mapPartial (try (Syntax.check_term ctxt)): terms -> terms;

fun get_fresh_free_var_name_in_trm' (ctxt:Proof.context) (trm:term) (n:int) =
  let
    val numb_of_fvars = numb_of_distinct_fvars trm + n;
    fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);
    val fst_candidate = mk_free_variable_of_typ dummyT numb_of_fvars |> dest_Free |> fst: string;
    fun is_free_in_ctxt (name:string) = is_Free (Syntax.read_term ctxt name): bool;
    fun get_all_names_in_trm trm =
        Isabelle_Utils.get_cnames_in_trm trm @ Isabelle_Utils.get_abs_names_in_trm trm @ Isabelle_Utils.get_free_var_names_in_trm trm;
    val all_names_in_trm  = get_all_names_in_trm trm |> distinct (op =): strings;                                                                                                                      
    fun is_fresh (current_candidate:string) = 
        not (member (op =) all_names_in_trm current_candidate) andalso is_free_in_ctxt current_candidate;
    fun add_a_if_taken (current_candidate:string): string =
      if is_fresh current_candidate then current_candidate else add_a_if_taken (current_candidate ^ "a");
    val result = add_a_if_taken fst_candidate: string
  in
    result
  end;

fun get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
  Free (get_fresh_free_var_name_in_trm' ctxt trm n, typ);

fun get_fresh_free_var_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) =
    get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (0:int)

fun get_fresh_free_vars_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
    map (get_fresh_free_var_of_typ_in_trm' ctxt typ trm) (List.tabulate (n, I)): terms;

val add_one_more_free_var = undefined; (* use tables and powerset. *)

fun mk_pst_to_prove_from_term (ctxt:Proof.context) term =
    let
      val prop = if is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] ctxt: Proof.state
    end;

end;

(*** signature TOP_DOWN_CONJECTURING ***)
signature TOP_DOWN_CONJECTURING =
sig

val top_down_conjectures: Proof.context -> term -> (string * term) list;

end;

fun non_prop_trm_to_dummy_eq (ctxt:Proof.context) (lhs:term) =
  let
(*
    val standardized_lhs = Isabelle_Utils.standardize_vnames lhs: term;
*)
    val new_free_var     = Top_Down_Util.get_fresh_free_var_of_typ_in_trm ctxt dummyT lhs;
    val dummy_eq         = HOLogic.mk_eq (lhs, new_free_var);
    val dummy_eq_prop    = HOLogic.mk_Trueprop dummy_eq;
    val checked_eq       = try (Syntax.check_prop ctxt) dummy_eq_prop;
    val dummy_cterm      = Option.map (Thm.cterm_of ctxt) checked_eq;
    val dummy_thm        = Option.map Thm.trivial dummy_cterm;
  in
    dummy_thm
  end;

fun simp_non_prop_term (ctxt:Proof.context) (trm:term) =
  let
    val dummy_thm            = non_prop_trm_to_dummy_eq ctxt trm: thm option;
    val simplifier           = Basic_Simplifier.simplify ctxt
    val simped_dummy_thm     = Option.mapPartial (try (Isabelle_Utils.timeout_apply (Time.fromSeconds 1) simplifier)) dummy_thm: thm option;
    val simped_fst_goal      = Option.map Thm.concl_of simped_dummy_thm: term option;
    val simped_fst_pair      = Option.mapPartial (try (HOLogic.dest_eq o HOLogic.dest_Trueprop)) simped_fst_goal: (term * term) option;
    val simped_lhs           = Option.map fst simped_fst_pair: term option;
    val possibly_simped_term = if is_some simped_lhs then the simped_lhs else trm: term;
  in
    possibly_simped_term: term
  end;

fun is_in (small:term) (big:term) =
  let
    fun is_in' (small':term) (big':term) =
      if small' = big'
      then true
      else case big' of
          Abs (_, _, middle) => is_in' small' middle
        | mid1 $ mid2 => is_in' small' mid1 orelse is_in' small' mid2
        | _ => false
  in
    is_in' (rm_typ small) (rm_typ big)
  end;

fun mk_extended_rhses (ctxt:Proof.context) (candidate_args:terms) (candidate_func as Const _:term): terms =
  let
   (*TODO: if func does not take explicit functions, filter out non-nullary constants from candidate_args*)
    val candidate_func_wo_type_consts = Top_Down_Util.remove_type_consts candidate_func      : term;
    val candidate_args_wo_type_consts = map Top_Down_Util.remove_type_consts candidate_args  : terms;
    val arg_numb                      = type_of candidate_func |> Term.binder_types |> length: int;
    fun mk_rhses (n:int) (partial_cnjct:term) =
      if n > 0
      then
        let
          val unchecked_partial_terms      = map (fn arg => partial_cnjct $ arg) candidate_args_wo_type_consts: terms;
          val checked_partial_terms        = Top_Down_Util.check_terms ctxt unchecked_partial_terms                         : terms;
          val partial_terms_wo_type_consts = map Top_Down_Util.remove_type_consts checked_partial_terms                     : terms;
          val result                       = map (mk_rhses (n-1)) partial_terms_wo_type_consts |> flat        : terms;
        in
           result
        end
      else [partial_cnjct];
    val rhses = mk_rhses arg_numb candidate_func_wo_type_consts: terms;
    val rhses_wo_type_consts = map Top_Down_Util.remove_type_consts rhses: terms;
    val simped_rhses = map (simp_non_prop_term ctxt) rhses_wo_type_consts;
    val rhses_wo_duplications =  distinct (op =) simped_rhses: terms;
  in
    rhses_wo_duplications |> map Top_Down_Util.remove_type_consts
  end
  | mk_extended_rhses _ _ _ = [];

fun replace_redundant_compound_subtrm_with_free_var' (ctxt:Proof.context) (lhs, rhs) =
  let
    val ((*func*)_, args) = strip_comb lhs: (term * terms);
    val fvars_in_rhs = Isabelle_Utils.get_free_var_names_in_trm rhs: strings;
    fun in_rhs (fvar_name:string) = exists (equal fvar_name) fvars_in_rhs: bool;
    fun has_fvar_that_is_not_in_rhs (arg:term) =
      let
        val fvar_names_in_arg = Isabelle_Utils.get_free_var_names_in_trm arg: strings;
        val result = forall (fn fvar_in_arg => not (in_rhs fvar_in_arg)) fvar_names_in_arg: bool;
      in
        result
      end;
    val compound_args = filter (fn arg => Isabelle_Utils.is_Abs arg orelse Isabelle_Utils.is_App arg) args: terms;
    val args_to_be_abstracted = filter has_fvar_that_is_not_in_rhs compound_args;
    val numb_of_args_to_be_abstracted = length args_to_be_abstracted: int
    val fresh_free_vars = Top_Down_Util.get_fresh_free_vars_of_typ_in_trm ctxt dummyT (lhs $ rhs) numb_of_args_to_be_abstracted: terms;
    val subst = subst_free (args_to_be_abstracted ~~ fresh_free_vars)
    val new_lhs = subst lhs
  in
    (new_lhs, rhs)
  end;

fun is_only_in_subtrm_of (small:term) (subtrm:term) (big:term) =
  let
    val small'  = rm_typ small;
    val subtrm' = rm_typ subtrm;
    val big'    = rm_typ big;
    fun is_only_in_subtrm_of' (big' as Abs (_, _, mid)) =
        if   subtrm' = big'
        then true
        else (is_only_in_subtrm_of' mid)
      | is_only_in_subtrm_of' (big' as mid1 $ mid2) =
        if subtrm' = big'
        then true
        else
            (if (is_only_in_subtrm_of' mid1) then true else not (is_in small' mid1))
          andalso
            (if (is_only_in_subtrm_of' mid2) then true else not (is_in small' mid2))
      | is_only_in_subtrm_of' atom = subtrm' = atom; 
  in
            is_in small'  subtrm'
    andalso is_in subtrm' big'
    andalso is_only_in_subtrm_of' big'
  end;

fun has_fvar_appearing_only_in_the_same_compound_trm (trm:term) =
(* this might be strictly more powerful than replace_redundant_compound_subtrm_with_free_var' *)
let
(*flatten ignores Abs!*)
  val subtrms = Isabelle_Utils.flatten_trm trm |> map rm_typ |> distinct (op =): terms;
  val compound_subtrms = filter (fn subtrm => Isabelle_Utils.is_Abs subtrm orelse Isabelle_Utils.is_App subtrm) subtrms: terms;
  val free_vars = filter is_Free subtrms: terms;
  fun fvar_appears_only_in_the_same_compound_trm (fvar:term) = exists (fn sub => is_only_in_subtrm_of fvar sub trm) compound_subtrms;
  val result = exists fvar_appears_only_in_the_same_compound_trm free_vars
in
  result
end

fun replace_redundant_compound_subtrm_with_free_var ctxt (lhs, rhs) =
   replace_redundant_compound_subtrm_with_free_var' ctxt (lhs, rhs)
|> swap
|> replace_redundant_compound_subtrm_with_free_var' ctxt
|> swap;

val _ = Scan.optional: ('a -> 'b * 'a) -> 'b -> 'a -> 'b * 'a;
type dsfasd = Nunchaku_Reconstruct.isa_model
\<close>

(*** Term_Table_for_Top_Down ***)
ML\<open>
(*
 * Term_Table_for_Top_Down.ML
 *
 * Authors:
 *   Yutaka Nagashima
 *)
(*** signature TERM_TABLE_FOR_TOP_DOWN ***)
signature TERM_TABLE_FOR_TOP_DOWN =
sig

type table;
type path;
type paths;

val update_ancestors_of: (table * path -> table) -> table -> path -> table;
val get_children       : table -> ints -> paths;
val get_descendents    : table -> path -> paths;
val rm_descendents     : table -> path -> table;

type node;
type unode;
val update_node_of_unode      : node -> unode -> unode;
val update_print_of_unode     : string -> unode -> unode;
val update_inner_path_of_unode: path -> unode -> unode;

val update_tag_of_unode                          : Proof.context -> unode -> unode;
val update_unode                                 : Proof.context -> unode -> string -> node -> unode;
val update_unode_in_table                        : Proof.context -> unode -> string -> node -> table -> table;
val update_print_of_unode_because_of_its_children: unode -> table -> table;
val update_print_of_path_because_of_its_children : table -> path -> table;
val update_unode_then_its_ancestors_in_table     : table -> path -> unode -> table;
val new_unode_of_fvar                            : int -> path -> unode;

end;

(*** structure Term_Table_for_Top_Down ***)
structure Term_Table_for_Top_Down: TERM_TABLE_FOR_TOP_DOWN =
struct

open Unique_Node;

type table = Inner_Path_To_Unode.path_to_unode_table;
type path  = ints;
type paths = ints list;

fun update_ancestors_of _                                (table:table) [] = table
  | update_ancestors_of (update:(table * path) -> table) (table:table) (path:path) =
    let
      val parent_path = Utils.init path;
      val is_defined  = Inner_Path_To_Unode.defined table parent_path: bool;
      val _ = if is_defined then () else error "update_ancestors failed. undefined unique_node.";
      val updated_table = update (table, parent_path): table;
    in
      update_ancestors_of update  updated_table (parent_path)
    end;

fun get_children' (path_to_unode_table:Inner_Path_To_Unode.path_to_unode_table) (parent_path:path) (nth_child:int) (acc:paths) =
  let
    val nth_child_is_defined = Inner_Path_To_Unode.defined path_to_unode_table (parent_path @ single nth_child): bool;
    val result =
      if   nth_child_is_defined
      then get_children' path_to_unode_table parent_path (nth_child + 1) (acc @ single (parent_path @ single nth_child))
      else acc
  in
    result         
  end;

fun get_children (path_to_unode_table:table) (parent_path:path) =
  get_children' path_to_unode_table parent_path 0 []: ints list;


fun get_descendents (table:table) (path:path): paths =
    let
      val children_paths = get_children table path: ints list;
      val other_descendents_paths = map (get_descendents table) children_paths: ints list list;
    in
      children_paths @ flat other_descendents_paths: ints list
    end;

fun rm_descendents (table:table) (path:path): table =
    let
      val descendents_paths = get_descendents table path: ints list;
      val new_table = fold Inner_Path_Table.delete_safe descendents_paths table: table
    in
      new_table
    end;

fun update_node_of_unode (new_node:node) ({print, inner_path, tag, ...}: unode) =
{
 node       = new_node,
 print      = print,
 inner_path = inner_path,
 tag        = tag
}: unode;

fun update_print_of_unode (new_print:string) ({node, inner_path, tag,...}:Unique_Node.unode) =
{
 node       = node,
 print      = new_print,
 inner_path = inner_path,
 tag        = tag
}: unode;

fun update_inner_path_of_unode (new_inner_path:ints) ({node, print, tag,...}:Unique_Node.unode) =
{
 node       = node,
 print      = print,
 inner_path = new_inner_path,
 tag        = tag
}: unode;


fun update_tag_of_unode (ctxt:Proof.context) (unode as {node, print, inner_path, tag}:unode) =
    case node of (NC (cname, typ)) =>
      let
        val new_tag = {
          part_of_prem           = #part_of_prem  tag                                                      : bool,
          part_of_cncl           = #part_of_cncl  tag                                                      : bool,
          is_premise             = #is_premise    tag                                                      : bool,
          is_conclusion          = #is_conclusion tag                                                      : bool,
          defined_with_n_clauses = SOME (SeLFiE_Util.ctxt_n_cname_to_number_of_defining_clauses ctxt cname): int option,
          is_defined_with        = SOME (Definition_Pattern.get_command ctxt cname)                        : Definition_Pattern.command option,
          take_n_params          = SOME (Isabelle_Utils.count_numb_of_args_of_fun_typ typ)                 : int option
        }: tag;
      in
        {node       = node,
         print      = print,
         inner_path = inner_path,
         tag        = new_tag
        }: Unique_Node.unode
      end
| _ => unode;

fun update_unode (ctxt:Proof.context) (old_unode:unode) (new_print:string) (new_node:node) =
   update_node_of_unode new_node old_unode
|> update_print_of_unode new_print
|> update_tag_of_unode ctxt: unode;

fun update_unode_in_table (ctxt:Proof.context) (old_unode:unode) (new_print:string) (new_node:node) (old_table:table) =
  let
    val new_unode = update_unode ctxt old_unode new_print new_node: unode;
    val path      = #inner_path old_unode: ints;
    val new_table = Inner_Path_Table.update (path, new_unode) old_table;
  in
    new_table: table
  end;

fun update_print_of_unode_because_of_its_children (unode as {node, inner_path, ...}: unode) (table:table): table =
  case node of
    NA =>
      let
        val children_paths  = get_children table inner_path                            : ints list;
        val sorted_paths    = sort (list_ord int_ord) children_paths                   : ints list;
        val children        = map (the o Inner_Path_To_Unode.lookup table) sorted_paths: unode list;
        val children_prints = map (enclose "(" ")" o #print) children                  : strings;
        val func_print      = hd children_prints                                       : string;
        val args_prints     = tl children_prints                                       : strings;
        val new_print       =
            if func_print = "(Pure.imp)"
            then String.concatWith " \<Longrightarrow> " args_prints
            else if func_print = "(Pure.conjunction)"
            then String.concatWith " &&& " args_prints
            else String.concatWith " " children_prints;
        val new_unode      = update_print_of_unode new_print unode;
        val new_graph      = Inner_Path_Table.update (inner_path, new_unode) table
      in
        new_graph
      end
  | NL vname_typ_pairs =>
      let
        val vnames    = map fst vname_typ_pairs: strings;
        val lambdas   = "\<lambda> " ^ String.concatWith " " vnames ^ ". ";
        val child     = Inner_Path_To_Unode.lookup table (inner_path @ [0]) |> the: unode;
        val new_print = lambdas ^ #print child;
        val new_unode = update_print_of_unode new_print unode;
        val new_graph = Inner_Path_Table.update (inner_path, new_unode) table
      in
        new_graph
      end
  | _ => table;

fun update_print_of_path_because_of_its_children (table:table) (path:path): table =
  let
    val is_defined = Inner_Path_To_Unode.defined table path: bool;
    val _          = if is_defined then () else error "update_print_of_path_because_of_its_children failed. undefined unique_node.";
    val unode      = Inner_Path_To_Unode.lookup table path |> the: unode;
    val new_table  = update_print_of_unode_because_of_its_children unode table;
  in
    new_table
  end;

fun update_unode_then_its_ancestors_in_table (table:table) (path:path) (unode:unode) =
  let
    val is_defined        = Inner_Path_To_Unode.defined table path: bool;
    val _                 = if is_defined then () else error "update_print_of_path_because_of_its_children failed. undefined unique_node.";
    val table_w_new_unode = Inner_Path_Table.update (path, unode) table: table;
    val has_parent        = length path > 0                            : bool;
    val table             = if has_parent
                            then update_ancestors_of (uncurry update_print_of_path_because_of_its_children) table_w_new_unode path: table
                            else table_w_new_unode;
  in
    table
  end;

fun new_unode_of_fvar (int:int) (path:path) =
  let
    val print = "var_" ^ Int.toString int;
    val node  = NF (print, dummyT);
    val dummy_tag = {
      part_of_prem           = true: bool,
      part_of_cncl           = true: bool,
      is_premise             = true: bool,
      is_conclusion          = true: bool,
      defined_with_n_clauses = NONE: int option,
      is_defined_with        = NONE: Definition_Pattern.command option,
      take_n_params          = NONE: int option
    };
    val unode = {node = node, print = print, inner_path = path, tag = dummy_tag}: unode;
  in
    unode
  end;

end;
\<close>

(*** Generalise_By_Renaming ***)
ML\<open>
(*** structure Generalise_By_Renaming ***)
structure Generalise_By_Renaming: TOP_DOWN_CONJECTURING =
(*TODO: too many candidates are produced.*)
struct

fun count_fvars' (Const _) acc = acc
  | count_fvars' (Free _) acc = acc + 1
  | count_fvars' (Var _) acc = acc
  | count_fvars' (Bound _) acc = acc
  | count_fvars' (Abs (_, _, body)) acc = count_fvars' body acc
  | count_fvars' (trm1 $ trm2) acc = count_fvars' trm2 (count_fvars' trm1 acc)

fun count_fvars trm = count_fvars' trm 0;

fun get_ints (ints_so_far:ints) =
  let
    val _ = if length ints_so_far = 0 then error "get_ints failed with an empty list." else (); 
    val maximum = Utils.ints_to_max_option ints_so_far |> the;
    val next_candidates = 1 upto (maximum + 1): ints;
    val new_intss = map (fn new_int => ints_so_far @ [new_int]) next_candidates: ints list;
  in
    new_intss: ints list
  end;

fun get_intss' (upper_limit:int) (intss_so_far:ints list) =
  if length (hd intss_so_far) < (upper_limit:int)
  then get_intss' upper_limit (map get_ints intss_so_far |> flat)
  else intss_so_far;

fun get_intss (upper_limit:int) = get_intss' upper_limit [[1]];

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun replace (Const p) [] = Const p
  | replace (Free (_, typ)) ([int]:ints) = mk_free_variable_of_typ typ int
  | replace (Var p) [] = Var p
  | replace (Bound i) [] = Bound i
  | replace (Abs (name, typ, body)) ints =
    let
      val new_bodies = replace body ints: term;
    in
      Abs (name, typ, new_bodies)
    end
  | replace (func $ arg) ints =
    let
      val numb_of_fvars_in_func = count_fvars func;
      val (ints_for_func, ints_for_arg) = chop numb_of_fvars_in_func ints: (ints * ints);
    in
      replace func ints_for_func $ replace arg ints_for_arg
    end
  | replace _ _ = error "replace failed. Pattern-matching failed!";

fun generalise_by_rename_free_variables' _ (trm:term) =
  if 0 < count_fvars trm andalso count_fvars trm < 8
  then
    let
      val numb_of_fvars = count_fvars trm: int;
      val intss = get_intss numb_of_fvars: ints list;
    in
      map (replace trm) intss
    end
  else [];

(*Util*)
fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun top_down_conjectures ctxt trm =
  map (fn tm => ("generalise_by_renaming", tm))
  (generalise_by_rename_free_variables' ctxt trm
  |> map (HOLogic.mk_Trueprop o remove_Trueprop)
  |> map (try (Syntax.check_term ctxt))
  |> Utils.somes);

end;
\<close>

(*** Generalise_Then_Extend ***)
ML\<open>
(*** structure Generalise_Then_Extend ***)
structure Generalise_Then_Extend: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;

fun extension_for_one_lhs_n_one_func (ctxt:Proof.context) (lhs:term, candidate_args:terms) (candidate_func:term) =
  let
    val lhs_wo_type_consts          = Isabelle_Utils.strip_atyp lhs                                      : term
    val rhses                       = mk_extended_rhses ctxt candidate_args candidate_func               : terms;
    val rhses_wo_type_consts        = map Isabelle_Utils.strip_atyp rhses                                : terms;
    val eq_pairs                    = map (pair lhs_wo_type_consts) rhses_wo_type_consts                 : (term * term) list;
    val eq_pairs_filtered           = map (replace_redundant_compound_subtrm_with_free_var ctxt) eq_pairs: (term * term) list;
    val eqs                         = map HOLogic.mk_eq eq_pairs_filtered                                : terms;
    val standardized_eqs            = map standardize_vnames eqs                                         : terms;
    val distinct_eqs                = distinct (op =) standardized_eqs                                   : terms;
    val eqs_checked                 = check_terms ctxt distinct_eqs                                      : terms;(*Warning: somehow Syntax.read_prop does not work here*)
    val eqs_wo_meaningless_compound = filter_out has_fvar_appearing_only_in_the_same_compound_trm eqs_checked
    val result_as_strings           = map (Isabelle_Utils.trm_to_string ctxt) eqs_wo_meaningless_compound: strings;
    val result_as_terms             = List.mapPartial (try (Syntax.read_prop ctxt)) result_as_strings    : terms;
    val result_wo_type_consts       = map remove_type_consts result_as_terms                             : terms;
  in
    result_wo_type_consts
  end;

fun extension_for_one_lhs (ctxt:Proof.context) (candidate_funcs:terms) (lhs:term, candidate_args:terms) =
   map (extension_for_one_lhs_n_one_func ctxt (lhs:term, candidate_args:terms)) candidate_funcs
|> flat
|> map standardize_vnames
|> distinct (op =);

open Term_Table_for_Top_Down;

fun generalise_exactly_one_subterm_str (ctxt:Proof.context) (trm:term) =
  let
    (*TODO: Where should I standardize free variable names? I should avoid repeating this operation as far as possible.*)
    val trm                    = standardize_vnames trm                                        : term;
    val p2u_table              = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm   : table;
    val numb_of_distinct_fvars = numb_of_distinct_fvars trm                                    : int;
    fun mk_new_unode_of_fvar (var_id:int) (path:ints) = new_unode_of_fvar var_id path                         : unode;
    fun unode_is_not_var ({node,...}:unode) = not (Unique_Node.is_NF node orelse
                                                   Unique_Node.is_NV node orelse
                                                   Unique_Node.is_NB node)                                    : bool;
    fun unode_is_not_func ({tag,...}:unode) = (#take_n_params tag = SOME 0) orelse (#take_n_params tag = NONE): bool;
    fun condition_on_unode (unode:unode)    = unode_is_not_var unode andalso unode_is_not_func unode          : bool;
    val all_non_var_paths   = Inner_Path_Table.dest p2u_table |> filter (condition_on_unode o snd) |> map fst : ints list;
    val var_id_n_path_pairs = map (pair numb_of_distinct_fvars) all_non_var_paths                             : (int * ints) list;
    fun abstract_over_one_print (table:table) (var_id:int, path:ints): table =
      let
        val unode     = mk_new_unode_of_fvar var_id path;
        val new_table = update_unode_then_its_ancestors_in_table table path unode;
      in
        new_table
      end;
    val new_tables       = map (abstract_over_one_print p2u_table) var_id_n_path_pairs : table list;
    val roots            = map (the o Utils.flip Inner_Path_Table.lookup []) new_tables: unode list;
    val roots_prints     = map #print roots                                            : strings;
  in
    roots_prints
  end;

fun read_terms ctxt = List.mapPartial (try (Syntax.read_term ctxt)): strings -> terms;

fun generalise_exactly_one_subterm (ctxt:Proof.context) (trm:term): terms =
let
  val result_strs  = generalise_exactly_one_subterm_str ctxt trm: strings;
  val result_terms = read_terms ctxt result_strs                : terms;
in
  result_terms
end;

fun get_free_vars_in_trm' trm = if Term.is_Free trm then [trm] else [];

fun get_free_vars_in_trm trm = Term.fold_aterms (fn trm => fn acc => get_free_vars_in_trm' trm @ acc |> distinct (op =)) trm [];

fun mk_fvar_of (i:int) = Free ("var_" ^ Int.toString i, dummyT);
fun mk_fvars   (i:int) = map mk_fvar_of (List.tabulate (i, I));

fun top_down_conjectures (ctxt:Proof.context) (orig_trm:term) =
  let
    val freevars_in_orig          = get_free_vars_in_trm orig_trm: terms;
    val standardized_fvars_in_gen = mk_fvars (length freevars_in_orig + 1): terms;
    val consts                    = get_consts_for_conjecturing ctxt orig_trm                                        : terms;
    val equality_pairs            = get_both_sides_of_eqs_in_term orig_trm                                           : (term * term) list;
    val cleaned_pairs             = map (apply2 (mk_unbound_bound_vars_free_vars ctxt)) equality_pairs: (term * term) list;
    fun get_free_vars trm         = get_free_vars_in_trm trm |> map Isabelle_Utils.strip_atyp                        : terms;
    (*TODO: move this filter to mk_extended_rhses*)
    fun is_nullary_const (Const (_, typ)) = Isabelle_Utils.count_numb_of_args_of_fun_typ typ = 0
      | is_nullary_const  _               = false
    val nullalry_consts = filter is_nullary_const consts

    fun generalise_pairs (lhs: term, rhs: term) =
    let
      val generalised_lhses = generalise_exactly_one_subterm ctxt lhs: terms;
      val generalised_rhses = generalise_exactly_one_subterm ctxt rhs: terms;
      val new_pairs    = map (fn new_lhs => pair new_lhs rhs) (lhs::generalised_lhses)
                       @ map (fn new_lhs => pair new_lhs lhs) (rhs::generalised_rhses)
    in
      new_pairs: (term * term) list
    end;
    val generalised_pairs  = map generalise_pairs cleaned_pairs |> flat;
    fun add_candidate_args (lhs, rhs) = (lhs, distinct (op =) (rhs :: nullalry_consts @ standardized_fvars_in_gen) |> distinct (op =))  : term * term list;
    val candidate_pairs    = map add_candidate_args generalised_pairs                      : (term * term list) list;

    val filtered_pairs     = filter_out (is_Free o fst) candidate_pairs                    : (term * term list) list;

    val extension_eqs      = map (extension_for_one_lhs ctxt consts) filtered_pairs |> flat: terms;
    val checked_eqs        = check_terms ctxt extension_eqs                                : terms;
    val results            = map (pair "generalisation_then_extension") checked_eqs
  in
    results
  end;

end;
\<close>

(*** Abstract_Same_Term ***)
ML\<open>
(*** structure Abstract_Same_Term ***)
structure Abstract_Same_Term: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;
open Term_Table_for_Top_Down;

fun abstract_same_term_str (ctxt:Proof.context) (trm:term) =
  let
    (*TODO: Where should I standardize free variable names? I should avoid repeating this operation as far as possible.*)
    val trm       = standardize_vnames trm: term;
    val p2u_table = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm;  
    val p2p_table = Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table p2u_table;
    val numb_of_distinct_fvars = numb_of_distinct_fvars trm: int;
  
    fun mk_new_unode_of_fvar (var_id:int) (path:ints) = new_unode_of_fvar var_id path: unode;
  
    fun mk_paths_n_unodes_pairs (var_id:int, paths:ints list) = map (fn path => (path, mk_new_unode_of_fvar var_id path)) paths: (ints * unode) list;
  
    fun update_table_for_pair (path:ints, unode:unode) (t:table): table = update_unode_then_its_ancestors_in_table t path unode;
  
    val same_print_paths = Print_Table.dest p2p_table |> map snd: ints list list;
  
    fun unode_is_compound ({node,...}:unode) = Unique_Node.is_NL node orelse Unique_Node.is_NA node: bool;
  
    fun points_to_compound_subtrm (path:ints) =
       Inner_Path_Table.lookup p2u_table path <$> unode_is_compound |> Utils.is_some_true: bool;
  
    fun all_paths_point_to_compound (paths:ints list) = forall points_to_compound_subtrm paths: bool;
  
    val same_compound_print_paths = filter all_paths_point_to_compound same_print_paths: ints list list;
  
    fun powerset (xs:'a list) =
      let
        fun poset ([],    base) = single base
          | poset (y::ys, base) = (poset (ys, base)) @ (poset (ys, y::base))
      in
        poset (xs, [])
      end;
  
    val paths_powerset = powerset same_compound_print_paths: ints list list list;
  
    fun tag_var_id_to_paths_set' _      ([]:ints list list) acc = acc: (int * ints list) list
      | tag_var_id_to_paths_set' var_id (paths::set)        acc = tag_var_id_to_paths_set' (var_id + 1) set (pair var_id paths :: acc);
  
    fun tag_var_id_to_paths_set paths_set = tag_var_id_to_paths_set' numb_of_distinct_fvars paths_set []: (int * ints list) list;
  
    val var_id_n_paths_powerset = map tag_var_id_to_paths_set paths_powerset: (int * ints list) list list;
  
    fun abstract_over_one_print (var_id:int, paths:ints list) (table:table): table =
      let
        val path_n_unode_pairs = mk_paths_n_unodes_pairs (var_id, paths): (ints * unode) list;
      in
        fold update_table_for_pair path_n_unode_pairs table
      end;
  
    fun abstract_over_mult_prints (pairs:(int * ints list) list) = fold abstract_over_one_print pairs p2u_table: table;
    val new_tables       = map abstract_over_mult_prints var_id_n_paths_powerset: table list;
    val roots            = map (the o Utils.flip Inner_Path_Table.lookup []) new_tables: unode list;
    val roots_prints     = map #print roots                                            : strings;
  in
    roots_prints
  end;
  
  fun top_down_conjectures (ctxt:Proof.context) (trm:term) =
    let
      val cnjctrs_strs         = abstract_same_term_str ctxt trm                                       : strings;
      val cnjctrs              = map (try (Syntax.read_prop ctxt)) cnjctrs_strs |> map the_list |> flat: terms;
      val standardized_cnjctrs = map standardize_vnames cnjctrs                         : terms;
      val unique_cnjectrs      = distinct (op =) standardized_cnjctrs                                  : terms;
      val tagged_cnjctrs       = map (pair "abstract_same_term)") unique_cnjectrs                      : (string * term) list;
    in
      tagged_cnjctrs
    end;

end;
\<close>

(*** SeLFiE_for_Top_Down ***)
ML\<open>
(*  Title:      PSL/UR/SeLFiE_for_Top_Down.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development
*)

structure SeLFiE_for_Top_Down =
struct

open Eval_Syntactic_Sugar;

val fvars_in_prem_should_appear_in_concl =
  All ("trm_occ_in_prem", SeLFiE_Util.QOuter_Path,
    Imply (
      And (
        Node_Is_Free (Variable "trm_occ_in_prem"),
        Is_A_Meta_Premise_Or_Below (Variable "trm_occ_in_prem")
      ),
      Some ("trm_occ_in_cncl", SeLFiE_Util.QOuter_Path,
        Ands [
          Has_Same_Prnt_As (Variable "trm_occ_in_prem", Variable "trm_occ_in_cncl"),
          Node_Is_Free (Variable "trm_occ_in_cncl"),
          Is_A_Meta_Conclusion_Or_Below (Variable "trm_occ_in_cncl")
        ]
      )
    )
  );

(* Due to the use of simplifier, this might be obsolete.*)
val does_not_have_trivial_equality =
  Not (
    Some ("equality", SeLFiE_Util.QOuter_Path,
      And (
        Unode_Has_Print (Variable "equality", Print "HOL.eq"),
        Some ("lhs", SeLFiE_Util.QOuter_Path,
          And (
            Is_Nth_Argument_Of (Variable "lhs", Number 0, Variable "equality"),
            Some ("rhs", SeLFiE_Util.QOuter_Path,
              And (
                Has_Same_Prnt_As (Variable "lhs", Variable "rhs"),
                Is_Nth_Argument_Of (Variable "rhs", Number 1, Variable "equality")
              )
            )
          )
        )
      )
    )
  );

val has_func_with_three_occs_in_a_row =
  Some ("func", SeLFiE_Util.QOuter_Print,
    Ands [
      Print_Is_Cnst (Variable "func"),
      Not (Is_Subprint_Of (Print "Pure", Variable "func")),
      Not (Is_Subprint_Of (Print "HOL",  Variable "func")),
      Some_Of ("func_occ1", Variable "func",
        Ands [
          Some ("arg_of_func_occ1", SeLFiE_Util.QOuter_Path,
            Ands [
              Node_Is_App (Variable "arg_of_func_occ1"),
              Is_An_Argument_Of (Variable "arg_of_func_occ1", Variable "func_occ1"),
              Some_Of ("func_occ2", Variable "func",
                Ands [
                  Is_Nth_Child_Of (Variable "func_occ2", Number 0, Variable "arg_of_func_occ1"),

                  Some ("arg_of_func_occ2", SeLFiE_Util.QOuter_Path,
                    Ands [
                      Node_Is_App (Variable "arg_of_func_occ2"),
                      Is_An_Argument_Of (Variable "arg_of_func_occ2", Variable "func_occ2"),
                      Some_Of ("func_occ3", Variable "func",
                        Ands [
                          Is_Nth_Child_Of (Variable "func_occ3", Number 0, Variable "arg_of_func_occ2")
                        ]
                      )
                    ]
                  )

                ]
              )
            ]
          )
        ]
      )
    ]
  );

fun run_assertion (pst:Proof.state)  (assrt:assert) (cnjctr:term) =
  let
    val outer_path_to_unode_table = Outer_Path_To_Unode.pst_n_trm_to_path_to_unode_table pst cnjctr                                               : Outer_Path_To_Unode.path_to_unode_table;
    val gen_path_table            = Gen_Path.Outer_Path_To_Unode outer_path_to_unode_table                                                        : Gen_Path.gen_path_to_unode_table;
    val empty_argument            = SeLFiE_Util.Induct_Arguments {ons = [], arbs = [], rules = []}                                                : SeLFiE_Util.induct_arguments;
    val outer_domains             = Quantifier_Domain.inout_pst_n_trm_n_induct_args_to_domains Quantifier_Domain.Out gen_path_table empty_argument: Quantifier_Domain.domains;
  in
    eval pst outer_path_to_unode_table outer_domains empty_argument assrt = True
  end;

end;
\<close>

(*** Top_Down_Conjecturing ***)
ML\<open>
(*** structure Remove_Outermost_Assumption ***)
structure Remove_Outermost_Assumption: TOP_DOWN_CONJECTURING =
struct

fun top_down_conjectures _ (trm:term) = try Logic.dest_implies trm <$> snd <$> pair "remove_assumption" |> the_list: (string * term) list;

end;

(*** structure Remove_Function ***)
structure Remove_Function(*: TOP_DOWN_CONJECTURING*) =
struct

open Top_Down_Util;
open Term_Table_for_Top_Down;

fun path_is_app (table:table) (path:ints) = Inner_Path_To_Unode.defined table (path @ [1]);

fun remove_path_in_table (table:table) (app_path:ints) =
  let
    val is_defined           = Inner_Path_To_Unode.defined table app_path: bool;
    val _                    = if is_defined then () else error "remove_function_in_table failed. undefined unique_node.";
    val children_paths       = get_children table app_path                                                       : ints list;
    val children             = map (the o Inner_Path_Table.lookup table) children_paths                          : unode list;
    val children_w_new_paths = map (update_inner_path_of_unode app_path) children                                : unode list;
    val app_removed_tables   = map (update_unode_then_its_ancestors_in_table table app_path) children_w_new_paths: table list;
    val roots                = map (the o Utils.flip Inner_Path_Table.lookup []) app_removed_tables              : unode list;
    val roots_prints         = map #print roots                                                                  : strings;
  in
    roots_prints: strings
  end;

fun remove_function_in_table (table:table) =
  let
    val keys      = Inner_Path_Table.keys table                           : ints list;
    val apps_keys = filter (path_is_app table) keys                       : ints list;
    val results   = map (remove_path_in_table table) apps_keys |> flat: strings;
  in
    results
  end;

fun remove_functions_in_trm (ctxt:Proof.context) (trm:term) =
  let
    val p2u_table    = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm: Inner_Path_To_Unode.path_to_unode_table;
    val cnjctrs_strs = remove_function_in_table p2u_table                                        : strings;
    val cnjctrs      = map (try (Syntax.read_prop ctxt)) cnjctrs_strs |> map the_list |> flat    : terms;
    val simped_cnjctrs = map (simp_non_prop_term ctxt) cnjctrs
  in
    simped_cnjctrs
  end;

open Unique_Node;

fun remove_multiple_occurrences_of_functions (ctxt:Proof.context) (trm:term) =
  let
    val const_names = Term.add_const_names trm []: strings;
    fun rm_a_func_of_name (Const (name, typ) $ arg) (cname:string) = if cname = name then arg else (Const (name, typ) $ rm_a_func_of_name arg cname)
      | rm_a_func_of_name (func $ arg) (cname:string) = rm_a_func_of_name func cname $ rm_a_func_of_name arg cname
      | rm_a_func_of_name (Abs (str, typ, subtrm)) (cname:string) = Abs (str, typ, rm_a_func_of_name subtrm cname)
      | rm_a_func_of_name trm _ = trm
    val new_trms = map (rm_a_func_of_name trm) const_names: terms;
    val new_strs = map (Isabelle_Utils.trm_to_string ctxt) new_trms: strings;
    val cnjctrs = Top_Down_Util.read_props ctxt new_strs: terms;
  in
    cnjctrs
  end;

fun top_down_conjectures (ctxt:Proof.context) (trm:term) =
  let
(*
val _ = tracing "The original term is "
val _ = tracing (Isabelle_Utils.trm_to_string ctxt trm);
*)
    val one_less_occ         = remove_functions_in_trm ctxt trm                 : terms;
    val one_less_prnt        = remove_multiple_occurrences_of_functions ctxt trm: terms;
(*
val _ = tracing "one_less_occ is "
val _ = map (tracing o Isabelle_Utils.trm_to_string ctxt) one_less_occ;
val _ = tracing "one_less_prnt is "
val _ = map (tracing o Isabelle_Utils.trm_to_string ctxt) one_less_prnt;
*)
    val cnjctrs              = one_less_occ @ one_less_prnt |> distinct (op =)  : terms;
    val standardized_cnjctrs = map standardize_vnames cnjctrs    : terms;
    val unique_cnjectrs      = distinct (op =) standardized_cnjctrs             : terms;
    val tagged_cnjctrs       = map (pair "remove_function)") unique_cnjectrs    : (string * term) list;
  in
    tagged_cnjctrs
  end;

end;

(*** structure Replace_Imp_With_Eq ***)
structure Replace_Imp_With_Eq: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;

fun count_const_of_name_in (cname:string) (trm:term) =
  let
    fun count_const_of_name' (Const (name,  _)) acc = if cname = name then acc + 1 else acc
      | count_const_of_name' (Free           _) acc = acc
      | count_const_of_name' (Var            _) acc = acc
      | count_const_of_name' (Bound          _) acc = acc
      | count_const_of_name' (Abs (_, _, body)) acc = count_const_of_name' body acc
      | count_const_of_name' (trm1 $ trm2     ) acc = count_const_of_name' trm2 (count_const_of_name' trm1 acc)
  in
    count_const_of_name' trm 0
  end;

fun top_down_conjectures (ctxt:Proof.context) (trm:term) =
  let
    val has_exactly_one_meta_imp = count_const_of_name_in "Pure.imp" trm = 1;
    fun replace_imp_w_eq (Const ("Pure.imp", _)) = Const ("HOL.eq", dummyT)
      | replace_imp_w_eq (Const  p             ) = Const p
      | replace_imp_w_eq (Free   p             ) = Free  p
      | replace_imp_w_eq (Var    p             ) = Var   p
      | replace_imp_w_eq (Bound  i             ) = Bound i
      | replace_imp_w_eq (Abs  (name, typ, trm)) = Abs (name, typ, replace_imp_w_eq trm)
      | replace_imp_w_eq (Const ("Pure.imp", _) $ (Const ("HOL.Trueprop", _) $ lhs) $ (Const ("HOL.Trueprop", _) $ rhs)) =
        Const ("HOL.Trueprop", dummyT) $ (Const ("HOL.eq", dummyT) $ lhs $ rhs)
      | replace_imp_w_eq (func $ arg)            = replace_imp_w_eq func $ replace_imp_w_eq arg;
    val conjectures = if has_exactly_one_meta_imp then check_terms ctxt [replace_imp_w_eq trm] else [];
    val results     = map (pair "replace_imp_with_eq") conjectures
  in
    results
  end;

end;

(*** structure All_Top_Down_Conjecturing ***)
structure All_Top_Down_Conjecturing: TOP_DOWN_CONJECTURING =
struct

fun is_composite trm = Isabelle_Utils.is_Abs trm orelse Isabelle_Utils.is_App trm: bool;

(*TODO: code-duplication with SeLFiE/Eval_Print.ML*)
fun read_term_then_check_term (ctxt:Proof.context) (print:string) (checker: term -> bool) =
    try (Syntax.read_term ctxt) print
<$> checker
 |> Utils.is_some_true;

fun has_no_multiple_occ_of_composite_subtrm (ctxt:Proof.context) (trm:term) =
let
  val p2u_table = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm: Inner_Path_To_Unode.path_to_unode_table;
  val p2p_table = Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table p2u_table: Print_To_Inner_Paths.print_to_paths_table;
  val prints = Print_To_Inner_Paths.print_to_paths_table_to_prints p2p_table: strings;
  fun print_has_multiple_paths (print:string) =
    let
      val paths = Print_Table.lookup_list p2p_table print;
      val has_multi = not (length paths = 1): bool;
    in
      has_multi
    end;
  val duplicated_prints = filter print_has_multiple_paths prints: strings;
  val duplicated_composites = filter (fn print => read_term_then_check_term ctxt print is_composite) duplicated_prints: strings;
  val has_dupulicates = null duplicated_composites: bool;
in
  has_dupulicates: bool
end;

(* Prod31 for example needs this congruence(?).
fun eq_over_same_func (ctxt:Proof.context) (trm:term) =
  let
    val trm_wo_Trueprop = Isabelle_Utils.remove_Trueprop trm;
    val trm_w_prnt  = Unique_Node.trm_to_trm_w_prnt ctxt trm_wo_Trueprop;
    val utrm_w_prnt = Unique_Node.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val result = case utrm_w_prnt of
        Unique_Node.UA_Prnt (Unique_Node.UC_Prnt ("HOL.eq", _, "HOL.eq"),
          [Unique_Node.UA_Prnt (func1, _, _),
           Unique_Node.UA_Prnt (func2, _, _)], _) => func1 = func2
      | _ => false
  in
    result
  end;
*)

fun top_down_conjectures (ctxt:Proof.context) trm =
  let
    val _ = tracing "[[[[[[[[[[[top_down_conjecture starts]]]]]]]]]]": unit;
    val standardized_trm = standardize_vnames trm
    val results = (
      Remove_Outermost_Assumption.top_down_conjectures ctxt standardized_trm
    (*@ Generalise_By_Renaming.top_down_conjectures ctxt standardized_trm*)
    @ (Generalise_Then_Extend.top_down_conjectures ctxt standardized_trm       |> filter (fn (_, trm) => has_no_multiple_occ_of_composite_subtrm ctxt trm))
    @ Remove_Function.top_down_conjectures ctxt standardized_trm
    @ Abstract_Same_Term.top_down_conjectures ctxt standardized_trm
    @ Replace_Imp_With_Eq.top_down_conjectures ctxt standardized_trm)
      |> map (apsnd (simp_non_prop_term ctxt))
      |> map (apsnd standardize_vnames)
      |> distinct (fn (f, s) => snd f = snd s)
(*
      |> filter_out (fn (_, trm) => eq_over_same_func ctxt trm)
*)
      |> filter_out (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm)
      |> filter (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.fvars_in_prem_should_appear_in_concl trm)
      |> filter (fn (_, trm) => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm) SeLFiE_for_Top_Down.does_not_have_trivial_equality trm);
    val _ = map (tracing o Isabelle_Utils.trm_to_string ctxt o snd) results: unit list;
    val _ = tracing "[[[[[[[[[[[top_down_conjecture ends]]]]]]]]]]": unit;
  in
    results
  end;

end;
\<close>

(*** And_Node ***)
ML\<open>
(*** AND_NODE ***)
signature AND_NODE =
sig

(** andnode and functions on andnode **)
(* andnodes do not have corresponding constructs in resulting proof scripts. *)
type andnode;
type andnodes;

(* update of andnode *)
val update_proved_completely: andnode -> andnode;
val update_refuted          : andnode -> andnode;

end

(*** And_Node ***)
structure And_Node: AND_NODE =
struct

(** andnode and functions on andnode **)
(* andnode *)
type andnode =
{
 subgoals               : terms, (*Used to detect the order of sub-goals.*)
 proved_completely      : bool,
 refuted                : bool
};

(* andnodes *)
type andnodes = andnode list;

(** update of andnode **)
(* update_proved_completely_of_andnode *)
fun update_proved_completely (
{
  subgoals: terms,
  refuted: bool, ...
}: andnode) =
{
  subgoals          = subgoals,
  proved_completely = true,
  refuted           = refuted
}: andnode;

(* update_refuted_of_andnode *)
fun update_refuted (
{
  subgoals                  : terms,
  proved_completely: bool,...
}: andnode) =
{
  subgoals          = subgoals,
  proved_completely = proved_completely,
  refuted           = true
}: andnode;

end;
\<close>

(*** Or_Node ***)
ML\<open>
(*** OR_NODE ***)
signature OR_NODE =
sig

(** ornode and functions on ornode **)
type ornode;
type ornodes;

(* query on ornode *)
val is_refuted          : ornode -> bool;
val is_worth_proving    : Proof.context -> ornode -> bool;

(* creation of ornode *)
type is_final_goal = bool;
val mk_ornode: is_final_goal -> term -> ornode;

(* update of ornode *)
val update_gg_parent_not_finished: ornode -> bool -> ornode;
val update_proved_completely     : ornode -> ornode;
val update_proof_n_proof_id      : string -> ornode -> ornode;
val update_refuted               : ornode -> ornode;
val update_branch                : ornode -> ornode;

end;

(*** Or_Node ***)
structure Or_Node: OR_NODE =
struct

(** ornode and functions on ornode **)
(* ornode and ornodes *)
type ornode = {
  final_goal                      : bool,
  branch                          : bool,
  lemma_name                      : string,
  lemma_term                      : term,(*For now we ignore "assumes" and "using".*)
  proof                           : string option,(*Proof script to finish proving this node.*)
  proof_id                        : int option,(*To track dependency. based on the timing proved with or w/o assuming conjectures.*)
  refuted                         : bool,
  proved_completely               : bool, (*= proved w/o assuming conjectures.*)
  (* If an or-node has a great grandparent that is not proved or refuted and this node is not
   * proved_completely, this node still needs a proof.*)
  gg_parent_not_finished          : bool
};

type ornodes = ornode list;
              
(** query on ornode **)

(* is_refuted *)
fun is_refuted ({refuted,...}:ornode) = refuted: bool;

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (ornode:ornode) =
(tracing "@@ In is_worth_proving";
 tracing ("  " ^ Isabelle_Utils.trm_to_string ctxt (#lemma_term ornode));
 if is_none (#proof ornode) then tracing "  TRUE: has no proof" else tracing "  has a proof";
 if #gg_parent_not_finished ornode then tracing "  TRUE: gg_parent_not_finished" else tracing "  gg_parent_finished";
 if not (#refuted ornode) then tracing "  TRUE: not refuted" else tracing "  refuted";

    (*TODO: I don't think type checking should happen here. But much earlier.*)
    is_some (try (Syntax.check_term ctxt) (#lemma_term ornode))
  andalso
    #gg_parent_not_finished ornode
  andalso
    not (#refuted ornode): bool
  andalso
    is_none (#proof ornode));

(* creation of ornode *)
type is_final_goal = bool;
fun mk_ornode (is_final_goal:is_final_goal) (goal:term) =
  let
    (*TODO: check if the name is already taken.*)
    val name = (if is_final_goal then "original_goal_" else "top_down_lemma_") ^ serial_string ();
  in
   {final_goal             = is_final_goal,
    branch                 = false,
    lemma_name             = name,
    lemma_term             = goal,
    proof                  = NONE,
    proof_id               = NONE,
    refuted                = false,
    proved_completely      = false,(*We do not search for a counterexample before checking for duplication.*)
    gg_parent_not_finished = true
   }: ornode
  end;

(** update of ornode **)
(* update_gg_parent_not_finished *)
(* 
 * unlike proved_completely, gg_parent_not_finished can change both ways.
 * For example, when a new conjecture from one or-node is identical to an existing conjecture,
 * we have to add a new grand parent to this existing conjecture. 
 * Such operation may change the gg_parent_not_finished of this existing one from
 * false to true.
 *)
fun update_gg_parent_not_finished ({
  final_goal       : bool,
  branch           : bool,
  lemma_name       : string,
  lemma_term       : term,
  proof            : string option,
  proof_id         : int option,
  refuted          : bool,
  proved_completely: bool,...
}: ornode) (gg_parent_not_finished: bool) =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = refuted,
  proved_completely      = proved_completely,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_proved_completely *)
fun update_proved_completely ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  refuted               : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal            = final_goal,
  branch                = branch,
  lemma_name            = lemma_name,
  lemma_term            = lemma_term,
  proof                 = proof,     
  proof_id              = proof_id,
  refuted               = refuted,
  proved_completely     = true,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:string) ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  refuted               : bool,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode)  =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = SOME proof,
  proof_id               = (Unsynchronized.inc PBC_Utils.proof_id_counter; SOME (Unsynchronized.! PBC_Utils.proof_id_counter)),
  refuted                = refuted,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_refuted *)
fun update_refuted ({
  final_goal            : bool,
  branch                : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal             = final_goal,
  branch                 = branch,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = true,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

(* update_branch *)
fun update_branch ({
  final_goal            : bool,
  lemma_name            : string,
  lemma_term            : term,
  proof                 : string option,
  proof_id              : int option,
  refuted               : bool,
  proved_completely     : bool,
  gg_parent_not_finished: bool,...
}: ornode) =
{
  final_goal             = final_goal,
  branch                 = true,
  lemma_name             = lemma_name,
  lemma_term             = lemma_term,
  proof                  = proof,
  proof_id               = proof_id,
  refuted                = refuted,
  proved_completely      = proved_completely: bool,
  gg_parent_not_finished = gg_parent_not_finished
}: ornode;

end;
\<close>

(*** Or2And_Edge ***)
ML\<open>
signature OR2AND_EDGE =

sig

(** or2and_edge and functions on or2and_edge **)
datatype how_to_get_andnodes_from_ornode = Tactic of string | Conjecture;
val how_to_get_andnodes_from_ornode_of: how_to_get_andnodes_from_ornode -> string;
val proof_is_from_tactic: how_to_get_andnodes_from_ornode -> bool;

type or2and_edge;
val or2and_edge_to_proof: or2and_edge -> string;

end;

structure Or2And_Edge: OR2AND_EDGE =
struct

(** or2and_edge and functions on or2and_edge **)
(* how_to_get_andnodes_from_ornode *)
datatype how_to_get_andnodes_from_ornode = Tactic of string | Conjecture;

(* how_to_get_andnodes_from_ornode_of *)
fun how_to_get_andnodes_from_ornode_of  Conjecture     = ""
  | how_to_get_andnodes_from_ornode_of (Tactic string) = string;

(* proof_is_from_tactic *)
fun proof_is_from_tactic (Tactic _) = true
  | proof_is_from_tactic _ = false;

(* or2and_edge *)
type or2and_edge = {
  how_to_get_andnodes_from_ornode: how_to_get_andnodes_from_ornode,
  proof_of_ornode_assmng_andnodes: string option}(*NONE: we cannot prove the or-node.*)

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof ({proof_of_ornode_assmng_andnodes, ...}:or2and_edge) =
  if   is_some proof_of_ornode_assmng_andnodes
  then the proof_of_ornode_assmng_andnodes
  else error "edge_to_final_proof failed. We do not know how to prove the or-node assuming the subgoals of the and-node.";

end;
\<close>

(*** Proof_Graph_Node ***)
ML\<open>
(*** PROOF_GRAPH_NODE ***)
signature PROOF_GRAPH_NODE =
sig

type ornode;
type andnode;
type or2and_edge;

(** proof_node **)
datatype proof_node =
  Or_Node   of ornode  (*Edges from Or_Node are alternative steps to prove this node, one of which we have to complete.*)
| And_Node  of andnode (*sub-goals, all of which we have to prove.*)
| Or_To_And of or2and_edge;

(* query on proof_node *)
val is_ornode                                    : proof_node -> bool;
val is_andnode                                   : proof_node -> bool;
val is_or2and_edge                               : proof_node -> bool;

(* query on proof_node for ornode and andnode *)
val is_proved_completely                         : proof_node -> bool;
val is_refuted                                   : proof_node -> bool;

(* query on proof_node for ornode *)
val proof_id_of                                  : proof_node -> int option;
val proof_of                                     : proof_node -> string option;
val is_branch                                    : proof_node -> bool;
val is_final_goal                                : proof_node -> bool;
val lemma_name_of                                : proof_node -> string;
val is_worth_proving                             : Proof.context -> proof_node -> bool;

(* query on proof_node for or2and_edge *)
val ornode_proved_assmng_andnodes: proof_node -> bool;
val or2and_edge_to_proof         : proof_node -> string;

(* destructors of proof_node *)
val dest_Or_Node  : proof_node -> ornode;
val dest_And_Node : proof_node -> andnode;
val dest_Or_To_And: proof_node -> or2and_edge;

(* creation of proof_node *)
type is_final_goal = bool;
val mk_ornode: is_final_goal -> term -> proof_node;

end;


(*** Proof_Graph_Node ***)
structure Proof_Graph_Node: PROOF_GRAPH_NODE =
struct

open Or_Node;
open And_Node;
open Or2And_Edge;

(** proof_node **)
datatype proof_node =
  Or_Node   of ornode  (*Edges from Or_Node are alternative steps to prove this node, one of which we have to complete.*)
| And_Node  of andnode (*sub-goals, all of which we have to prove.*)
| Or_To_And of or2and_edge;

(** query on proof_node **)
(* is_ornode *)
fun is_ornode (Or_Node _) = true
  | is_ornode _ = false;

(* is_andnode *)
fun is_andnode (And_Node _) = true
  | is_andnode _ = false;

(* is_or2and_edge *)
fun is_or2and_edge (Or_To_And _) = true
  | is_or2and_edge _ = false;

(* is_proved_completely *)
fun is_proved_completely (Or_Node  nd) = #proved_completely nd
  | is_proved_completely (And_Node nd) = #proved_completely nd
  | is_proved_completely (Or_To_And _) = error "is_proved_completely failed."

(* is_refuted *)
fun is_refuted (Or_Node  ornode ) = #refuted ornode
  | is_refuted (And_Node andnode) = #refuted andnode
  | is_refuted _                  = error "is_refuted failed. This should not be applied to an edge."

(* is_worth_proving *)
fun is_worth_proving ctxt (Or_Node  or_nd) = Or_Node.is_worth_proving ctxt or_nd
  | is_worth_proving _    (And_Node     _) = error "is_worth_proving failed. This is And_Node."
  | is_worth_proving _    (Or_To_And    _) = error "is_worth_proving failed. This is Or_To_And.";

fun proof_id_of (Or_Node or_nd) = #proof_id or_nd
  | proof_id_of  _              = error "proof_id_of. This is not Or_Node."

(* proof_of *)
fun proof_of (Or_Node or_nd) = #proof or_nd
  | proof_of  _              = error "proof_of failed. This is not Or_Node."

(* is_branch *)
fun is_branch (Or_Node or_nd) = #branch or_nd
  | is_branch _ = error "is_branch failed. This is not Or_Node."

(* is_final_goal *)
fun is_final_goal (Or_Node or_nd) = #final_goal or_nd
  | is_final_goal  _              = error "is_final_goal. This is not Or_Node."

(* ornode_proved_assmng_andnodes *)
fun ornode_proved_assmng_andnodes (Or_To_And or2and_edge:proof_node) =
    #proof_of_ornode_assmng_andnodes or2and_edge |> is_some
  | ornode_proved_assmng_andnodes _ = error "ornode_proved_assmng_andnodes";

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof (Or_To_And or2and_edge:proof_node) = Or2And_Edge.or2and_edge_to_proof or2and_edge
  | or2and_edge_to_proof _ = error "or2and_edge_to_proof failed. This is not or2and_edge."

(* lemma_name_of *)
fun lemma_name_of (Or_Node or_nd) = #lemma_name or_nd
  | lemma_name_of _ = error "lemma_name_of failed. Not an Or_Node."

(** destructors on proof_node **)
(* dest_Or_Node *)
fun dest_Or_Node (Or_Node or_b) = or_b
  | dest_Or_Node _ = error "dest_Or_Node failed.";

(* dest_And_Node *)
fun dest_And_Node (And_Node and_b) = and_b
  | dest_And_Node _ = error "dest_And_Node failed.";

(* dest_Or_To_And *)
fun dest_Or_To_And (Or_To_And edge) = edge
  | dest_Or_To_And _ = error "dest_Or_To_And_failed";

(* creation of proof_node *)
type is_final_goal = bool;

(* mk_ornode *)
fun mk_ornode (is_final_goal:is_final_goal) (goal:term) = Or_Node (Or_Node.mk_ornode is_final_goal goal): proof_node;

end;
\<close>

(*** Proof_Graph_Node_Util ***)
ML\<open>
(*** PROOF_GRAPH_NODE ***)
signature PROOF_GRAPH_NODE_UTIL =
sig

type ornode     = Proof_Graph_Node.ornode;
type andnode    = Proof_Graph_Node.andnode;
type proof_node = Proof_Graph_Node.proof_node;

(* update of proof_node *)
val update_gg_parent_not_finished: bool -> proof_node -> proof_node;
val update_proved_completely     : proof_node -> proof_node;
val update_proof_n_proof_id      : string -> proof_node -> proof_node;
val update_refuted               : proof_node -> proof_node;
val update_branch                : proof_node -> proof_node;

end;

(*** Proof_Graph_Node_Util ***)
structure Proof_Graph_Node_Util: PROOF_GRAPH_NODE_UTIL =
struct

open Proof_Graph_Node;

(** update of proof_node **)
(* update_gg_parent_not_finished *)
fun update_gg_parent_not_finished b (Or_Node ornode) = Or_Node.update_gg_parent_not_finished ornode b |> Or_Node
  | update_gg_parent_not_finished _  and_or_edge     = and_or_edge;

(* update_proved_completely *)
fun update_proved_completely (Or_Node  ornode ) = Or_Node.update_proved_completely ornode |> Or_Node
  | update_proved_completely (And_Node andnode) = And_Node.update_proved_completely andnode |> And_Node
  | update_proved_completely (Or_To_And      _) = error "update_proved_completely failed.";

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id proof (Or_Node ornode) = Or_Node.update_proof_n_proof_id proof ornode |> Or_Node
  | update_proof_n_proof_id _      and_or_edge     = and_or_edge;

(* update_refuted *)
fun update_refuted (Or_Node  ornode ) = Or_Node.update_refuted  ornode  |> Or_Node
  | update_refuted (And_Node andnode) = And_Node.update_refuted andnode |> And_Node
  | update_refuted _                  = error "update_refuted failed. Or_To_And edge!";

(* update_branch *)
fun update_branch (Or_Node ornode) = Or_Node.update_branch ornode |> Or_Node
  | update_branch _                = error "update_branch failed!";

end;
\<close>

(*** Proof_Graph ***)
ML\<open>
(*** PROOF_GRAPH ***)
signature PROOF_GRAPH =
sig

(** proof_graph **)
(* key, PGraph_Key, and PGraph *)
datatype node_type = Or_N | And_N | O2A_E of int;
val node_type_compare: (node_type * node_type) -> order;

structure PGraph: GRAPH

type proof_node;

type key;
type keys;

val  print_key: Proof.context -> key -> unit list;
val  equal_keys: (key * key) -> bool;

type proof_graph;

(* creation of key_val pair *)
type is_final_goal = bool;
val mk_ornode:  is_final_goal -> term -> (key * proof_node);
val mk_andnode: terms -> (key * proof_node);

(* initialization *)
val mk_initial_graph                              : term -> proof_graph;

(* query on key and graph *)
val is_branch     : proof_graph -> key -> bool;
val is_ornode     : key -> bool;
val is_andnode    : key -> bool;
val is_or2and_edge: key -> bool;

(* query on proof_node for ornode and andnode *)
val is_proved_completely                         : proof_graph -> key -> bool;
val is_refuted                                   : proof_graph -> key -> bool;

(* query on proof_node for ornode *)
val is_final_goal                                : proof_graph -> key -> bool;
val lemma_name_of                                : proof_graph -> key -> string;
val proof_of                                     : proof_graph -> key -> string;
val proof_id_of                                  : proof_graph -> key -> int option;

val grand_parents                                : proof_graph -> key -> keys;
val grand_children                               : proof_graph -> key -> keys;
val all_gg_parents_are_proved                    : proof_graph -> key -> bool;

(* query on proof_node for or2and_edge *)
val ornode_proved_assmng_andnodes                : proof_graph -> key -> bool;
val or2and_edge_to_proof                         : proof_graph -> key -> string;

val is_worth_proving                             : Proof.context -> proof_graph -> key -> bool;

(*TODO: it is a little strange that we have proof_of and or2and_edge_to_proof separately.*)
val get_final_goal                               : proof_graph -> key;
val keys_tobe_expanded_in                        : Proof.context -> proof_graph -> keys;

val goal_as_string                               : Proof.state -> key -> string;

(* query on proof_graph *)
val final_goal_proved_completely                 : proof_graph -> bool;

end;

(*** Proof_Graph ***)
structure Proof_Graph: PROOF_GRAPH =
struct

open Proof_Graph_Node_Util;

(** proof_graph **)
(* node_type *)
datatype node_type = Or_N | And_N | O2A_E of int;

(* node_type_compare *)
fun node_type_compare (Or_N,     Or_N    ) = EQUAL
 |  node_type_compare (Or_N,     _       ) = LESS
 |  node_type_compare (And_N,    O2A_E _ ) = LESS
 |  node_type_compare (And_N,    And_N   ) = EQUAL
 |  node_type_compare (And_N,    _       ) = GREATER
 |  node_type_compare (O2A_E i1, O2A_E i2) = Int.compare (i1, i2)
 |  node_type_compare (O2A_E _,  _       ) = GREATER;

fun term_compare (trm1, trm2) =
  Term_Ord.term_ord ((standardize_vnames trm1), (standardize_vnames trm2))

(* PGraph_Key *)
structure PGraph_Key =
    struct
      type key = (node_type * terms)
      val  ord = prod_ord node_type_compare (list_ord term_compare)
    end:KEY

(* PGraph *)
structure PGraph = Graph (PGraph_Key): GRAPH;

(* proof_graph *)
type proof_graph = proof_node PGraph.T;

(* key *)
type key  = PGraph.key

fun print_key  (ctxt:Proof.context) ((_, trms): key) =
  (
    tracing "  key is";
    map (fn trm => tracing ("    " ^ Isabelle_Utils.trm_to_string ctxt trm)) trms
  );

(* keys *)
type keys = PGraph.key list;

(* equal_key *)
fun equal_keys key_pair = PGraph_Key.ord key_pair = EQUAL;

(* creation of key_val pair *)
type is_final_goal = bool;

fun mk_ornode (is_final_goal:is_final_goal) (goal:term) =
  (
    (Or_N, [goal]): key,
    Proof_Graph_Node.mk_ornode is_final_goal goal: Proof_Graph_Node.proof_node
   );

fun mk_andnode (goals:terms) =
  (
    (And_N, goals): key,
    Proof_Graph_Node.And_Node {
      subgoals          = goals,
      proved_completely = false,
      refuted           = false
   });

(* mk_initial_graph *)
fun mk_initial_graph (goal:term) =
  let
    val root_pair = mk_ornode true goal: key * Proof_Graph_Node.proof_node;
    val empty_graph = PGraph.empty: proof_graph;
  in
    PGraph.new_node root_pair empty_graph
  end;

(** query on key **)
(* is_branch *)
fun is_branch (graph:proof_graph) (key:key) =
  PGraph.get_node graph key |> Proof_Graph_Node.is_branch: bool;

(* is_ornode *)
fun is_ornode (Or_N, _) = true
  | is_ornode  _        = false;

(* is_andnode *)
fun is_andnode (And_N, _) = true
  | is_andnode  _         = false;

(* is_or2and_edge *)
fun is_or2and_edge (O2A_E _, _) = true
  | is_or2and_edge  _           = false;

(* is_proved_completely *)
fun is_proved_completely (graph:proof_graph) (key:key): bool =
  PGraph.get_node graph key |> Proof_Graph_Node.is_proved_completely;

(* is_refuted *)
fun is_refuted (graph:proof_graph) (key:key): bool =
  PGraph.get_node graph key |> Proof_Graph_Node.is_refuted;

(* lemma_name_of *)
fun lemma_name_of (graph:proof_graph) (key:key) =
  PGraph.get_node graph key |> Proof_Graph_Node.lemma_name_of: string;

(* grand_relatives *)
fun grand_relatives (graph:proof_graph) (key:key) (preds_or_succs: proof_graph -> key -> key list): keys =
  let
    val immediate_keys = preds_or_succs graph key: keys;
    val grand_keys = map (preds_or_succs graph) immediate_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* grand_parents *)
fun grand_parents (graph:proof_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_preds;

(* grand_children *)
fun grand_children (graph:proof_graph) (key:key): keys = grand_relatives graph key PGraph.immediate_succs;

(* great_grand_relatives *)
fun great_grand_relatives (graph:proof_graph) (key:key) (preds_or_succs: proof_graph -> key -> key list): keys =
  let
    val grand_relatives_keys = grand_relatives graph key preds_or_succs: keys;
    val grand_keys = map (preds_or_succs graph) grand_relatives_keys |> flat |> distinct equal_keys;
  in
    grand_keys
  end;

(* great_grand_parents *)
fun great_grand_parents (graph:proof_graph) (key:key): keys = great_grand_relatives graph key grand_parents;

(* all_gg_parents_are_proved *)
fun all_gg_parents_are_proved (graph:proof_graph) (key as (Or_N, _)): bool = all_great_grandparents_are_proved_for_or key graph
  | all_gg_parents_are_proved _ _: bool = error "all_great_grandparents_are_proved failed. And_N"
and all_great_grandparents_are_proved_for_or key graph =
  let
    val great_grand_parents_keys  = great_grand_parents graph key: keys;
    val great_grand_parents_nodes = map (PGraph.get_node graph) great_grand_parents_keys: proof_node list;
  in
   null great_grand_parents_keys orelse forall Proof_Graph_Node.is_proved_completely great_grand_parents_nodes
  end;

(* is_final_goal *)
fun is_final_goal (graph:proof_graph) (key as (Or_N, _): key): bool =
    PGraph.get_node graph key |> Proof_Graph_Node.is_final_goal
  | is_final_goal _ _ = false;

(* get_final_goal *)
fun get_final_goal (graph:proof_graph) =
  let
    val final_goals = PGraph.keys graph |> filter (is_final_goal graph): keys;
    val final_goal  = if length final_goals = 1
                      then hd final_goals
                      else error "get_final_goal failed. Not exactly one final_goals.";
  in
    final_goal
  end;

(* is_worth_proving *)
fun is_worth_proving (ctxt:Proof.context) (graph:proof_graph) (key:key)  =
  PGraph.get_node graph key |> Proof_Graph_Node.is_worth_proving ctxt: bool;

(* proof_id_of *)
fun proof_id_of (graph:proof_graph) (key:key) = PGraph.get_node graph key |> Proof_Graph_Node.proof_id_of: int option;

(* proof_of *)
fun proof_of (graph:proof_graph) (key:key) =
  let
    val maybe_proof = PGraph.get_node graph key |> Proof_Graph_Node.proof_of: string option;
  in
    if is_some maybe_proof
    then the maybe_proof
    else error "proof_of failed. No proof yet."
  end;

(* goal_as_string *)
fun goal_as_string (pst:Proof.state) ((Or_N, [term]):key) = Isabelle_Utils.trm_to_string (Proof.context_of pst) term
  | goal_as_string (pst:Proof.state) ((And_N, terms):key) = map (Isabelle_Utils.trm_to_string (Proof.context_of pst)) terms |> String.concatWith "\n"
  | goal_as_string _ _ = error "goal_as_string in Proof_Graph.ML failed"

(* keys_tobe_expanded_in *)
fun keys_tobe_expanded_in (ctxt:Proof.context) (graph:proof_graph): keys =
  let
    val or_keys                        = PGraph.keys graph |> filter is_ornode          : keys;
val _ = tracing ("ALL OR_KEYS: ");
val _ = map (print_key ctxt) or_keys;
    val orleaf_keys                    = filter_out (is_branch graph) or_keys           : keys
val _ = tracing ("ALL orleaf_keys: ");
val _ = map (print_key ctxt) orleaf_keys;
    val keys_worth_trying              = filter (is_worth_proving ctxt graph) orleaf_keys: keys;
val _ = tracing ("ALL keys_worth_trying: ");
val _ = map (print_key ctxt) keys_worth_trying;
    val final_goal_key                 = get_final_goal graph                           : key;
val _ = tracing ("FINAL GOAL IS: ");
val _ =  print_key ctxt final_goal_key;
    val keys_reachable_from_final_goal = PGraph.all_succs graph [final_goal_key]        : keys;
    val _                              = tracing ("Number of keys_reachable_from_final_goal: " ^ Int.toString (length keys_reachable_from_final_goal));
    val _ = map (print_key ctxt) keys_reachable_from_final_goal
    val result = inter equal_keys keys_worth_trying keys_reachable_from_final_goal;
    val _                              = tracing ("Number of keys_reachable_from_final_goal after removing dups: " ^ Int.toString (length result));
    val _ = map (print_key ctxt) result
  in
    result
  end;

(* ornode_proved_assmng_andnodes *)
fun ornode_proved_assmng_andnodes (graph:proof_graph) (key:key) =
    Proof_Graph_Node.ornode_proved_assmng_andnodes (PGraph.get_node graph key);

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof (graph:proof_graph) (key:key) =
    Proof_Graph_Node.or2and_edge_to_proof (PGraph.get_node graph key);

(* final_goal_proved_completely *)
fun final_goal_proved_completely (graph:proof_graph) =
  let
    val final_goal_key    = get_final_goal graph                     : key;
    val final_goal_proved = is_proved_completely graph final_goal_key: bool;
  in
    final_goal_proved
  end;

end;
\<close>

(*** Proof_Graph_Util ***)
ML\<open>
(*** PROOF_GRAPH_UTIL ***)
signature PROOF_GRAPH_UTIL =
sig

type proof_graph;
type key;
type keys;
type andnode;
type proof_node;

(* update of proof_graph *)
val update_gg_parent_not_finished_in_proof_graph       : proof_graph -> proof_graph;
val update_proof_n_proof_id                            : string -> key -> proof_graph -> proof_graph;
val update_branch                                      : key -> proof_graph -> proof_graph;
val update_proved_completely                           : key -> proof_graph -> proof_graph;

(*TODO: maybe update_proved_completely_of_graph_because_orleaf_is_proved should go to Proof_By_Abduction(_Util.ML)*)
val update_proved_completely_of_graph_because_orleaf_is_proved: Proof.context -> key -> proof_graph -> proof_graph;

val add_andnodes                                        : Proof.context -> (key * proof_node) list -> proof_graph -> keys * proof_graph;
val add_ornodes                                         : Proof.context -> (key * proof_node) list -> proof_graph -> keys * proof_graph;

val add_edge_acyclic_if_possible                        : key -> key -> proof_graph -> proof_graph;
val add_edges_from_andnodes_to_ornodes                  : keys -> proof_graph -> proof_graph;

end;

(*** Proof_Graph_Util ***)
structure Proof_Graph_Util: PROOF_GRAPH_UTIL =
struct

open Proof_Graph_Node;
open Proof_Graph;

(** update of proof_node **)
(* update_gg_parent_not_finished_in_proof_graph *)
(* update_gg_parent_not_finished_in_proof_graph assumes that the graph is already updated by
 * update_proved_completely_of_graph_because_orleaf_is_proved. *)
(* There is no point in updating gg_parent_not_finished for a particular node:
 * proving one ornode may change proved_completely of any node in the graph. *)
fun update_gg_parent_not_finished_in_proof_graph (graph:proof_graph) =
    let
      val keys = PGraph.keys graph: keys;
      val or_keys = filter is_ornode keys: keys;
      fun check_n_update_a_node (key:key) (gr:proof_graph): proof_graph =
          let
            val tracing' = if false then tracing else K ();
            val _               = tracing' "before does_need_proof";
            val does_need_proof = not (all_gg_parents_are_proved gr key)       : bool;
            val _               = tracing' "before update";
            val update          = Proof_Graph_Node_Util.update_gg_parent_not_finished does_need_proof: proof_node -> proof_node;
          in
            PGraph.map_node key update gr
          end;
    in
      fold check_n_update_a_node or_keys graph
    end;

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:string) (key:key) (graph:proof_graph) =
    PGraph.map_node key (Proof_Graph_Node_Util.update_proof_n_proof_id proof) graph: proof_graph;

(* update_branch *)
fun update_branch (key:key) (graph:proof_graph) =
    PGraph.map_node key Proof_Graph_Node_Util.update_branch graph: proof_graph;

(* update_proved_completely *)
fun update_proved_completely (key:key) (graph:proof_graph) =
    PGraph.map_node key Proof_Graph_Node_Util.update_proved_completely graph: proof_graph;

(* update_proved_completely_of_graph_because_orleaf_is_proved *)
fun update_proved_completely_of_graph_because_orleaf_is_proved (ctxt:Proof.context) (key as (Or_N, _): key) (graph:proof_graph): proof_graph =
    let
      val tracing' = if true then tracing else K ();
      fun forall_at_least_one assertion xs = forall assertion xs andalso (length xs > 0);
      val children = PGraph.immediate_succs;
      val parents  = PGraph.immediate_preds;
      fun update_proved_wo_assmng_cnjctr_of_graph (key as (Or_N, trms)) (graph:proof_graph) =
          if not (is_branch graph key)(*If this or-node is a leaf, we do not have to care about the effects of its children.*)
          then
            let
              val _ = tracing' "Currently processing a leaf-like or-node."
              val graph_w_one_node_updated = update_proved_completely key graph: proof_graph;
              val parents_keys = parents graph_w_one_node_updated key: keys;
              val _ = tracing' ("Extracted parents! Amount:" ^ (Int.toString (length parents_keys)))
              val result = fold update_proved_wo_assmng_cnjctr_of_graph parents_keys graph_w_one_node_updated
            in
              result: proof_graph
            end
          else
           (tracing' "  Or_N is passed to update_proved_wo_assmng_cnjctr_of_graph";
            map (fn trm => tracing' ("    " ^ Isabelle_Utils.trm_to_string ctxt trm)) trms;
            update_branch key graph exists parents grand_children (* Root ~ And -> OR -> Edge -> And ~ Leaf *)
           )
        | update_proved_wo_assmng_cnjctr_of_graph (key as (And_N, trms)) (graph:proof_graph) = (
          tracing' "  And_N is passed to update_proved_wo_assmng_cnjctr_of_graph";
          map (fn trm => tracing' ("    " ^ Isabelle_Utils.trm_to_string ctxt trm)) trms;
          update_branch key graph forall_at_least_one grand_parents children) (* Root ~ OR -> Edge -> And -> OR ~ Leaf *)
        | update_proved_wo_assmng_cnjctr_of_graph (O2A_E _, _) _ = error "update_proved_wo_assmng_cnjctr_of_graph failed! O2A_E!"
      and update_branch key graph (forall_or_exists) (parent_or_grand_parent) (child_or_grand_child) =
          let
            val children_keys = child_or_grand_child graph key: keys;
            fun print_one_key ((_, [])) = ()
              | print_one_key ((nd_typ, tm::tms)) =(
                  tracing ("   " ^ (Isabelle_Utils.trm_to_string ctxt tm));
                  print_one_key (nd_typ, tms))
            val this_node_is_newly_proved_wo_assmng_cnjctr =
                 (if is_proved_completely graph key |> not(*TODO: TO BE REMOVED*)
                  then tracing "  The following is true: (is_proved_completely graph key |> not)"
                  else tracing "  The following is false: (is_proved_completely graph key |> not)";
                  is_proved_completely graph key |> not(*This node was not proved yet*)
                  )
                andalso
                 (if forall_or_exists (fn key => is_proved_completely graph key) children_keys(*TODO: TO BE REMOVED*)
                  then tracing "  The following is true: forall_or_exists (fn key => is_proved_completely graph key) children_keys"
                  else tracing "  The following is false: forall_or_exists (fn key => is_proved_completely graph key) children_keys";
                  (*for or-node:  this node is now proved because one grandchild (and-node) is proved.*)
                  (*for and-node: this node is now proved because all children (or-node) are proved.*)
                  forall_or_exists (fn key => is_proved_completely graph key) children_keys: bool                  );
                  (*TODO: Can I really use forall for and-node? What if an and-node has no children at all.*)

            val some_grandchild_of_ornode_that_proved_completely: key option =
                if   is_ornode key andalso this_node_is_newly_proved_wo_assmng_cnjctr
                then (
                  let
                    val _ = tracing "  The following is true: is_ornode key andalso this_node_is_newly_proved_wo_assmng_cnjctr"
                    val proved_grandchildren = filter (fn key => is_proved_completely graph key) children_keys
                  in
                    SOME (hd proved_grandchildren)
                  end
                  )
                else (
                    tracing "  The following is false: is_ornode key andalso this_node_is_newly_proved_wo_assmng_cnjctr";
                    NONE
                    );

            val graph_w_one_node_updated' =
                if   this_node_is_newly_proved_wo_assmng_cnjctr
                then (tracing' "  We call update_proved_completely.";
                      update_proved_completely key graph)
                else (tracing' "  No change in ancestral situation.";
                      graph);

            val graph_w_one_node_updated =
                if   is_some some_grandchild_of_ornode_that_proved_completely
                then (
                  let
                    val _ = tracing' "  is_some some_grandchild_of_ornode_that_proved_completely.";
                    val grandchild_of_ornode_that_proved_completely = the some_grandchild_of_ornode_that_proved_completely;
                    val _ = tracing "  Let's look at the AND-node who is a grand child of ornode under consideration (some_grandchild_of_ornode_that_proved_completely):"
                    val _ = print_one_key grandchild_of_ornode_that_proved_completely
                    val to_and_edges = PGraph.immediate_preds graph_w_one_node_updated' grandchild_of_ornode_that_proved_completely;
                    val from_or_edges = PGraph.immediate_succs graph_w_one_node_updated' key
                    val inter_edges = inter equal_keys to_and_edges from_or_edges;
                    val or2edge = if length inter_edges > 0 then hd inter_edges else error "graph_w_one_node_updated failed!";
                    
                    val script_to_prove_ornode = or2and_edge_to_proof graph_w_one_node_updated' or2edge: string;
                  in
                    update_proof_n_proof_id script_to_prove_ornode key graph_w_one_node_updated'
                  end
                )
                else (
                  tracing' "  is_none some_grandchild_of_ornode_that_proved_completely.";
                  graph_w_one_node_updated')

            val parents_keys = parent_or_grand_parent graph_w_one_node_updated key: keys;

            val result =
                if   this_node_is_newly_proved_wo_assmng_cnjctr
                (*for or-node:  we have to update its parents (and-node).*)
                (*for and-node: we have to update its grand parents (or-node).*)
                then fold update_proved_wo_assmng_cnjctr_of_graph parents_keys graph_w_one_node_updated
                else graph;

          in
            result
          end;
    in
      (* TODO: We have to update proof_id of ancestors.
       * PGraph.topological_order, ignore PGraph.isolated, compare the difference, map update_proof_id_of_proof_node
       * We can ignore this issue for now, at the cost of strictly sticking to the dependency imposed by the graph
       * and not allowing sledgehammer to use lemmas that are not immediate successors.*)
      update_proved_wo_assmng_cnjctr_of_graph key graph
    end
  | update_proved_completely_of_graph_because_orleaf_is_proved _ _ _ =
    error "update_proved_completely_of_graph_because_orleaf_is_proved failed.";

fun add_nodes (ctxt:Proof.context) (key_value_pairs: (key * proof_node) list) (graph: proof_graph) (or_and:string) =
    let
      val numb_of_created_keys = length key_value_pairs: int;
(*
      val _ = if or_and = "or" then tracing ("Number of newly produced " ^ or_and ^ "-nodes: " ^ Int.toString numb_of_created_keys ^ ".") else ();
*)
      fun new_node (k, v) (acc, g:proof_graph): (keys * proof_graph) =
          (k :: acc, PGraph.new_node (k, v) g)
          handle PGraph.DUP _ => ((*tracing ("Duplicated " ^ or_and ^ "-node. We use the existing one, which may have been proved_wo_assmng_cnjctr.");*) (acc, g));
      val (newly_added_keys, resulting_graph) = fold new_node key_value_pairs ([], graph): keys * proof_graph;
      val number_of_duplicated_keys = numb_of_created_keys - length newly_added_keys;
(*
      val _ = if or_and = "or" then tracing ("Number of discarded "^ or_and ^"-nodes due to duplication: " ^ Int.toString number_of_duplicated_keys ^ ".") else ();
*)
    in
     (newly_added_keys, resulting_graph)
    end;

(* add_andnodes *)
fun add_andnodes ctxt (key_value_pairs: (key * proof_node) list) (graph: proof_graph) =
    add_nodes ctxt key_value_pairs graph "and";

(* add_ornodes *)
fun add_ornodes ctxt (key_value_pairs: (key * proof_node) list) (graph: proof_graph) =
    add_nodes ctxt key_value_pairs graph "or";

(* add_edge_acyclic_if_possible *)
fun add_edge_acyclic_if_possible source_key target_key g =
  PGraph.add_edge_acyclic (source_key, target_key) g handle PGraph.CYCLES _ => (tracing "CYCLES detected!"; g): proof_graph;

local

(* add_edges_from_andnode_to_ornodes *)
fun add_edges_from_andnode_to_ornodes (and_key as (And_N, terms):key) (graph:proof_graph) =
  let
    val ornode_keys = map (fn trm => (Or_N, [trm])) terms: keys;
    val non_refuted_ornode_keys = filter_out (Proof_Graph.is_refuted graph) ornode_keys: keys;
    val graph_w_and_to_or_edges = fold (add_edge_acyclic_if_possible and_key) non_refuted_ornode_keys graph: proof_graph;
  in
    graph_w_and_to_or_edges
  end
 | add_edges_from_andnode_to_ornodes _ _ = error "add_edges_from_andnode_to_ornodes failed.";

in

(* add_edges_from_andnodes_to_ornodes *)
fun add_edges_from_andnodes_to_ornodes (and_keys:keys) (graph:proof_graph) =
    fold add_edges_from_andnode_to_ornodes and_keys graph: proof_graph;

end;

end;
\<close>

(*** Proof_By_Abduction_Util ***)
ML\<open>
(*** PROOF_BY_ABDUCTION_UTIL ***)
signature PROOF_BY_ABDUCTION_UTIL =
sig

type proof_graph;
type key;
type how_to_get_andnodes_from_ornode;
type andnode;
type proof_node
type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : proof_node,
      state      : Proof.state};
type seeds_of_andnode;

val print_seed_of_andnode: Proof.context -> seed_of_andnode -> unit list;
val seed_is_from_tactic: seed_of_andnode -> bool;

val find_counterexample_update                       : Proof.state -> key -> proof_graph -> proof_graph;
val mk_pst_to_prove_from_key                         : Proof.state -> key -> Proof.state;
val prove_orkey_completely                           : key -> proof_graph -> Proof.state -> (Proof.state * string) option;
(*TODO: apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes is called only once. No need to export it.*)
val apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes: Proof.state -> seed_of_andnode list;
val add_or2and_edge                                  : key -> seed_of_andnode -> proof_graph -> proof_graph;

val filter_out_bad_seeds_of_andnode: term (*parental or-node*) -> Proof.state -> proof_graph -> seeds_of_andnode -> seeds_of_andnode
val conjectures_to_seeds_of_andnode: (Proof.state (*default pst*) * Proof.state (*chained pst to proved the parental ornode*)) -> terms -> seeds_of_andnode;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction_Util: PROOF_BY_ABDUCTION_UTIL =
struct

structure PGraph = Proof_Graph.PGraph;

type proof_graph                     = Proof_Graph.proof_graph;
type key                             = Proof_Graph.key;
type keys                            = Proof_Graph.keys;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type andnode                         = And_Node.andnode;
type proof_node                      = Proof_Graph_Node.proof_node;

type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : proof_node,
      state      : Proof.state};

type seeds_of_andnode = seed_of_andnode list;

fun print_seed_of_andnode ctxt ({andnode_key,...}: seed_of_andnode) = (
  tracing "== print_seed_of_andnode:  ==";
  map (tracing o Isabelle_Utils.trm_to_string ctxt) (snd andnode_key)
);

fun seed_is_from_tactic ({proof, ...}) = Or2And_Edge.proof_is_from_tactic proof: bool;

(* apply_Extend_Leaf_to_pst_get_records_to_mk_andnodes *)
(*TODO: handle the case where we actually finish to prove this.*)
fun apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes (pst:Proof.state) =
    let
      val ctxt          = Proof.context_of pst;
      val extend_str    = PSL_Interface.lookup ctxt "Extend_Leaf" |> the                     : PSL_Interface.strategy;
      val timeouts      = {overall = 60.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}   : PBC_Utils.timeouts;
      val result_seq    = PBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst []: (Dynamic_Utils.log * Proof.state) Seq.seq;
      val result_list   = Seq.list_of result_seq                                             : (Dynamic_Utils.log * Proof.state) list;
      val script_n_psts = map (apfst Dynamic_Utils.mk_apply_script) result_list              : (string * Proof.state) list;
      fun mk_proof_key_value (pscript, pst) =
          let
            val subgs = Isabelle_Utils.pst_to_subgs pst
(*
val _ = tracing "------"
val _ = map (Isabelle_Utils.trm_to_string ctxt) subgs |> map tracing
*)
            val subgs_wo_meta_uni = map strip_outermost_meta_quantifiers subgs: terms;
            fun check_print_read ctxt term = term
             |> Syntax.check_term ctxt
             |> Isabelle_Utils.trm_to_string ctxt
             |> Syntax.read_term ctxt
             |> standardize_vnames;

            fun check_print_read_terms ctxt terms = map (check_print_read ctxt) terms: terms;
            fun pass_check_print_read_terms ctxt terms = try (check_print_read_terms ctxt) terms |> is_some;

            val nonempty_subgs =
              if length subgs = 0 orelse not (pass_check_print_read_terms ctxt subgs_wo_meta_uni)
              then [@{prop "True"}]
              else subgs_wo_meta_uni: terms;

            val key   = (Proof_Graph.And_N, nonempty_subgs): key;
            val value = Proof_Graph_Node.And_Node
                   ({subgoals          = nonempty_subgs,
                     proved_completely = false,
                     refuted           = false}: andnode): proof_node;
          in
            {proof = Or2And_Edge.Tactic pscript, andnode_key = key, value = value, state = pst}: seed_of_andnode
          end;
    in
      map mk_proof_key_value script_n_psts: seeds_of_andnode
    end;

(* find_counterexample_update *)
(*TODO: for andnodes we can get the result quickly if we use its children (ornodes) -> Maybe it is better to *)
fun find_counterexample_update (pst:Proof.state) (key:key) (graph:proof_graph) =
  let
    val found_counter_example = exists (fn trm => PBC_Utils.term_has_counterexample_in_pst trm pst) (snd key)
  in
    if   found_counter_example
    then PGraph.map_node key Proof_Graph_Node_Util.update_refuted graph(*TODO: We need update_refuted in Proof_Graph.ML*)
    else graph
  end;

(* mk_pst_to_prove_from_key *)
(*TODO: Don't ignore local assumptions.*)
fun mk_pst_to_prove_from_key (pst:Proof.state) (Proof_Graph.Or_N, [term]) =
    let
      val prop = if is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key (pst:Proof.state) (Proof_Graph.And_N, [term]) =
    let
      val prop = if is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key _ _ = error "mk_pst_to_prove_from_key failed!";

(* prove_orkey_completely *)
fun prove_orkey_completely (or_key as (Proof_Graph.Or_N:Proof_Graph.node_type, [lemma_term]):key) (graph:proof_graph) (pst:Proof.state) =
    let
      val lemma_name            = Proof_Graph.lemma_name_of graph or_key                                    : string;
      val pst_to_prove          = mk_pst_to_prove_from_key pst or_key                                       : Proof.state;
      val timeouts              = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}          : PBC_Utils.timeouts;
      val maybe_result          = PBC_Utils.pst_to_proofscript_opt timeouts "Attack_On_Or_Node" pst_to_prove: (string * Proof.state) option;
      val cheated_pst           = PBC_Utils.cheat_lemma_term_in_pst lemma_name lemma_term pst
      fun mk_result (script, _) = Option.map (rpair script) cheated_pst;
      val result                = Option.mapPartial mk_result maybe_result: (Proof.state * string) option
    in
      result
    end
  | prove_orkey_completely _ _ _ = error "try_to_prove_orkey_completely failed!";

(* add_or2and_edge *)
fun add_or2and_edge
     (or_key as (Proof_Graph.Or_N, [ornode_term]):key)(*parent node*)
     ({andnode_key: key,
       proof      : how_to_get_andnodes_from_ornode,
       state      : Proof.state, ...}: seed_of_andnode)(*child nodes*)
   (graph:proof_graph): proof_graph =
   let
val _ = tracing "start add_or2and";
     val or_leave_keys = PGraph.immediate_succs graph andnode_key: keys;(*these or_leave_keys are gg_children of or_key*)
     fun or_key_to_term (Proof_Graph.Or_N, [orleaf_term]) = orleaf_term
       | or_key_to_term  _                                = error "or_key_to_term failed.";
     fun mk_name_term_pair (orleaf_key:key) = (Proof_Graph.lemma_name_of graph orleaf_key, or_key_to_term orleaf_key): (string * term);
     val name_term_pairs      = map mk_name_term_pair or_leave_keys: (string * term) list;
     val pst_w_or_terms_assmd = Proof.map_context (PBC_Utils.assume_terms_in_ctxt name_term_pairs) state: Proof.state;(*TODO: FIXME:*)
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}: PBC_Utils.timeouts;
     val how_we_got_andnode   = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof            : string;
(*     
     val _ = tracing "-"
     val _ = tracing "finish_goal_after_assuming_subgoals_n_conjectures. ";
     val _ = tracing "or-node is: "
     val _ = (Proof_Graph.print_key (Proof.context_of state) or_key)
     val _ = tracing "and-node is: "
     val _ = (Proof_Graph.print_key (Proof.context_of state) andnode_key)
*)
(*TODO: FIXME: \<rightarrow> No need to fix?*)
(*
 * The use of pst_w_or_term_assmd is wrong here.
 * We use a Proof.state to attack the (remaining) of or-node.
 * But this state is for the and-node.
 * We should send a proof state that is associated with or-node.
 *)
     val script_opt_gen = PBC_Utils.pst_to_proofscript_opt timeouts "finish_goal_after_assuming_subgoals_n_conjectures" pst_w_or_terms_assmd <$> fst;
     fun mk_script_opt_for_tactic (tactic_script:string) = how_we_got_andnode ^ tactic_script;
     val script_opt =
          if how_we_got_andnode = "" (*explicit conjecturing*)
          then                                                                                     
            script_opt_gen
          else
            (Option.map mk_script_opt_for_tactic script_opt_gen)(*TODO: We have to check if we can prove the remaining goals.*)
     (*TODO: or2and_edge_val is a function on proof_node. It should be encapsulated in Proof_Node.ML.*)
     val or2and_edge_val      = Proof_Graph_Node.Or_To_And {
                                   how_to_get_andnodes_from_ornode = proof,
                                   proof_of_ornode_assmng_andnodes = script_opt}: proof_node;                              
     val or2and_edge_key     = ((Proof_Graph.O2A_E (serial())), []): key;
     val graph_w_or2and_edge = PGraph.new_node (or2and_edge_key, or2and_edge_val) graph: proof_graph;
     val graph_w_or2and_edge_connected = graph_w_or2and_edge
                                      |> Proof_Graph_Util.add_edge_acyclic_if_possible or_key or2and_edge_key
                                      |> Proof_Graph_Util.add_edge_acyclic_if_possible or2and_edge_key andnode_key: proof_graph;
     (*This cuts the edge that connects or2and_edge_key and andnode.*)
     fun cut_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals (or2and_edge_key:key) (graph:proof_graph): proof_graph =
       (* If connecting the labelled-edge and and-node would make the graph cyclic, *)
       (* we should not have added an edge between the labelled-edge and and-node.  *)
       if PGraph.is_edge graph (andnode_key, or2and_edge_key)
       then
         let
           val and_keys = PGraph.immediate_succs graph or2and_edge_key: keys;
           val _        = if length and_keys = 1 then () else error "cut_edge_from_andnode_to_ornode_if_no_parental_ornode_can_be_proved_assmng_subgoals failed. Zero or more than one and_keys.";
           val and_key  = hd and_keys: key;
           val parental_ornode_can_be_proved_assmng_subgoals = Proof_Graph.ornode_proved_assmng_andnodes graph or2and_edge_key: bool;
         in
           if parental_ornode_can_be_proved_assmng_subgoals
           then graph
           else PGraph.del_edge (or2and_edge_key, and_key) graph
         end
       else graph;
     val result = cut_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals or2and_edge_key graph_w_or2and_edge_connected;
   in
     if is_some script_opt then result else graph
   end
 | add_or2and_edge _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed."

val tracing' = if true then tracing else K ();

fun condition_to_filter_out (parent_or:term) (pst:Proof.state) (pg:proof_graph) (seed:seed_of_andnode) =
    let
      val final_goal      = Proof_Graph.get_final_goal pg |> snd |> hd: term;
(*
      val final_goal_size = Term.size_of_term final_goal |> Real.fromInt: real;
      val factor = case #proof seed of Or2And_Edge.Tactic _ => 5.0 | _ => 3.0: real;
      val upper_limit     = Real.min (factor * final_goal_size, 45.0): real;
*)
val upper_limit = 45.0
      fun concl_is_alpha_eq_to trm imp =
        let
          val cncl = Logic.strip_imp_concl imp |> remove_Trueprop: term;
        in
          alpha_eq_over_fvar trm cncl
        end;

      val trms       = snd (#andnode_key seed)                                    : terms;
      val trms_empty = null trms
      fun too_large _ = exists (fn trm => Real.fromInt (Term.size_of_term trm) > upper_limit) trms: bool;
      fun eq_to_final_goal _ = exists (alpha_eq_over_fvar final_goal) trms: bool;
      fun concl_is_eq_to_final_goal _ = exists (concl_is_alpha_eq_to final_goal) trms: bool;
      fun has_func_with_three_occs_in_a_row _ = exists
      (fn trm => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term (Proof.context_of pst) trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm) trms;
    in
      trms_empty orelse too_large () orelse
      (eq_to_final_goal () andalso seed_is_from_tactic seed) orelse
      (concl_is_eq_to_final_goal () andalso seed_is_from_tactic seed) orelse
      has_func_with_three_occs_in_a_row ()
    end;

fun filter_out_bad_seeds_of_andnode (parent_or:term) (pst:Proof.state) (graph:proof_graph) (seeds:seeds_of_andnode) =
  filter_out (condition_to_filter_out parent_or pst graph) seeds: seeds_of_andnode;
                                                                                      
fun conjectures_to_seed_of_andnode (pst:Proof.state) (cnjctr:term): seed_of_andnode =
  let
    val (key, proof_node) = Proof_Graph.mk_andnode [cnjctr]
  in
     {andnode_key = key                   : key,
      proof       = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
      value       = proof_node            : proof_node,
      state       = pst                   : Proof.state}
  end;

(*TODO: code-duplication with mk_pst_to_prove_from_key*)
fun mk_pst_to_prove_from_term (pst:Proof.state) (term:term) =
    let
      val prop = if is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end;

fun conjectures_to_seeds_of_andnode (pst:Proof.state, pst_to_prove_ornode:Proof.state) (cnjctrs:terms) =
let
  fun check_prop (trm:term) = try (Syntax.check_prop (Proof.context_of (mk_pst_to_prove_from_term pst trm))) trm: term option;
  val checked_cnjctrs = List.mapPartial check_prop cnjctrs
  val result = map (fn trm => conjectures_to_seed_of_andnode pst_to_prove_ornode trm) checked_cnjctrs
in
  result
end;
(*
     map (try (Syntax.check_term (Proof.context_of pst))) cnjctrs
  |> Utils.somes
  |> map (conjectures_to_seed_of_andnode pst): seeds_of_andnode;
*)
end;
\<close>

(*** Proof_By_Abduction ***)
ML\<open>
(*
 * Proof_By_Abduction.ML
 *
 * Authors:
 *   Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited
 *)

(*** PROOF_BY_ABDUCTION ***)
signature PROOF_BY_ABDUCTION =
sig

type proof_graph;
type key;
type andnode;
type proof_node;
type state;

val work_on_andnode      : state -> key -> proof_graph -> proof_graph;
val work_on_ornode       : key -> (state * proof_graph) -> (state * proof_graph);
val print_proof_of_graph : state -> proof_graph -> unit;
val loop                 : int -> (state * proof_graph) -> (state * proof_graph);
val top_down_conjecturing: state -> term -> unit;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type proof_graph                     = Proof_Graph.proof_graph;
type key                             = Proof_Graph.key;
type keys                            = Proof_Graph.keys;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type andnode                         = And_Node.andnode;
type proof_node                      = Proof_Graph_Node.proof_node;
type state                           = Proof.state;

open Proof_Graph;
open Proof_Graph_Util;

structure PBAU = Proof_By_Abduction_Util;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_andnode  = PBAU.seed_of_andnode;
type seeds_of_andnode = seed_of_andnode list;



fun print_lemma_and_proof_of_key (graph:proof_graph) (pst:state) (key:key) =
    let
      val name  = lemma_name_of graph key : string;
      val stmt  = goal_as_string pst key  : string;
      val proof = proof_of graph key      : string;
    in
       "lemma " ^ name ^ ": " ^ enclose "\"" "\"" stmt ^ "\n" ^ proof
    end;

(* work_on_andnode *)
fun work_on_andnode (pst:state) (and_key as (And_N, subgoals):key) (graph:proof_graph) =
    let
(*
      val _ = tracing "Start work_on_andnode"
*)
      val pairs_to_mk_ornodes             = map (mk_ornode false) subgoals                                           : (key * proof_node) list;
      val (new_or_keys, graph_w_ornodes)  = add_ornodes (Proof.context_of pst) pairs_to_mk_ornodes graph             : keys * proof_graph;
      val graph_w_quickchecked_ornodes    = fold (PBAU.find_counterexample_update pst) new_or_keys graph_w_ornodes   : proof_graph;
      val graph_w_edges                   = add_edges_from_andnodes_to_ornodes [and_key] graph_w_quickchecked_ornodes: proof_graph;
    in
      graph_w_edges
    end
  | work_on_andnode _ _ _ = error "work_on_andnode failed! Not an And_N key!";

(* work_on_ornode *)
fun work_on_ornode (or_key as (Or_N, [lemma_term]):key) (pst:state, graph:proof_graph): state * Proof_Graph_Util.proof_graph =
    (*TODO: we should check if the node is still worth proving.*)
    let
val _ = tracing "Start computing work_on_ornode"
       val ctxt         = Proof.context_of pst;
       val maybe_proved = PBAU.prove_orkey_completely or_key graph pst: (state * string) option;
    in
      if is_some maybe_proved (*ornode was proved completely.*)
      then
        let
          val _ = tracing "We PROVED the work_on_ornode"
          val (pst_w_proved_lemma, proof) = the maybe_proved: (state * string);

          (*Important tricky part! TODO: make these as one function.*)
          val updated1      = graph    |> update_proof_n_proof_id proof or_key
          val updated2      = updated1 |> update_proved_completely_of_graph_because_orleaf_is_proved (Proof.context_of pst) or_key
          val updated_graph = updated2 |> update_gg_parent_not_finished_in_proof_graph;
        in
           (pst_w_proved_lemma, updated_graph)(*TODO: We are actually not taking advantage of pst_w_proved_lemma. pst seems good enough.*)
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          val pst_to_prove       = PBAU.mk_pst_to_prove_from_key pst or_key                           : state;
          val seeds_from_tactics = PBAU.apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes pst_to_prove: seeds_of_andnode;

          fun seeds_to_updated_graph (seeds: seeds_of_andnode): proof_graph =
            let
              val pairs_to_mk_andnodes                 = map (fn {andnode_key, value,...} => (andnode_key, value)) seeds                      : (key * proof_node) list;
              val graph_w_ornode_is_now_branch         = update_branch or_key graph                                                           : proof_graph;
              val (new_andnds_keys, graph_w_andnodes)  = add_andnodes (Proof.context_of pst) pairs_to_mk_andnodes graph_w_ornode_is_now_branch: (keys * proof_graph);

              val graph_w_ornodes                      = fold (work_on_andnode pst) new_andnds_keys graph_w_andnodes                          : proof_graph;

              fun one_of_ands_child_nodes_is_refuted (and_key:key) (graph:proof_graph) =
              let
                val child_ors = PGraph.immediate_succs graph and_key: keys;
                val is_refuted = exists (Proof_Graph.is_refuted graph) child_ors: bool;
                val result_graph = if is_refuted then PGraph.map_node and_key Proof_Graph_Node_Util.update_refuted graph
                                   else graph
              in
                result_graph
              end;
              val graph_w_refuted_andnodes             = fold (Proof_By_Abduction_Util.find_counterexample_update pst) new_andnds_keys graph_w_ornodes
                                                         (*fold one_of_ands_child_nodes_is_refuted new_andnds_keys graph_w_ornodes : proof_graph;*)

              fun seed_is_refuted ({andnode_key,...}:seed_of_andnode) =  Proof_Graph.is_refuted graph_w_refuted_andnodes andnode_key: bool;
              val seeds_not_refuted_yet                = filter_out seed_is_refuted seeds: seeds_of_andnode;
              val seeds_of_newly_added_andnodes        = filter (fn seed => member equal_keys new_andnds_keys (#andnode_key seed)) seeds_not_refuted_yet: seeds_of_andnode;
              val graph_w_ornodes_n_or2add_edges       = fold (PBAU.add_or2and_edge or_key) seeds_of_newly_added_andnodes graph_w_ornodes               : proof_graph;
            in
              graph_w_ornodes_n_or2add_edges: Proof_Graph_Util.proof_graph
            end;
          (*conjecturing*)
          val seeds_from_conjectures = All_Top_Down_Conjecturing.top_down_conjectures (Proof.context_of pst) lemma_term
                                    |> map snd (*TODO: At the moment, we throw away the hints for top-down auxiliary lemma names, since incorporating this information requires changing the type of andnode.*)
                                    |> PBAU.conjectures_to_seeds_of_andnode (pst, pst_to_prove): seeds_of_andnode;
                    val filtered_seeds = PBAU.filter_out_bad_seeds_of_andnode lemma_term pst graph (seeds_from_conjectures @ seeds_from_tactics): seeds_of_andnode;
(*
val _ = tracing "PRINT FILTERED SEEDS OF AND-NODES"
val _ = map (Proof_By_Abduction_Util.print_seed_of_andnode ctxt) filtered_seeds
*)
        in
          (pst, seeds_to_updated_graph filtered_seeds)
        end
    end
  | work_on_ornode _ _ = error "work_on_ornode failed. Not an Or_N.";     

fun work_on_ornode_if_original_goral_is_unproved (or_key:key) (pst, graph) =
  if final_goal_proved_completely graph
  then (pst, graph)
  else work_on_ornode or_key (pst, graph)

(* print_proof_of_graph *)
(*topological sort is not good enough due to our use of state.*)
fun print_proof_of_graph (pst:state) (graph:proof_graph) =
    let
      val keys                         = PGraph.keys graph |> filter is_ornode |> rev: keys;
      val key_prf_id_pairs             = map (fn key => (key, proof_id_of graph key)) keys: (key * int option) list;
      val key_prf_id_pairs_solved_only = filter (fn (_, id) => is_some id) key_prf_id_pairs: (key * int option) list;
      val key_prf_id_pairs_wo_opt      = map (apsnd the) key_prf_id_pairs_solved_only: (key * int) list;
      fun compare ((_, id1), (_, id2)) = Int.compare (id1, id2): order;                        
      val sorted_keys                  = sort compare key_prf_id_pairs_wo_opt |> map fst: key list;
      val final_script                 = "\n" ^ (map (print_lemma_and_proof_of_key graph pst) sorted_keys |> String.concatWith "\n");
      val _ = Active.sendback_markup_properties [Markup.padding_command] final_script |> tracing;
    in
      ()
    end;

(* loop *)
fun loop (counter:int) (pst:state, graph: proof_graph) =
    if counter < 8
    then
      let
        val _                          = tracing ("==== In loop. Counter is: " ^ Int.toString counter ^ " =====");
        val ctxt                       = Proof.context_of pst;
        val keys_worth_expanding       = keys_tobe_expanded_in ctxt graph                     : keys;
        val _ = tracing ("The number of keys worth expanding is:" ^ Int.toString (length keys_worth_expanding));
        val _ = tracing "They are:"
        fun print_key ctxt key = map (tracing o Isabelle_Utils.trm_to_string ctxt) (snd key);
        val _ = map (fn k => (tracing ""; print_key ctxt k)) keys_worth_expanding
        val (_, graph_w_keys_expanded) = fold work_on_ornode_if_original_goral_is_unproved keys_worth_expanding (pst, graph): (state * proof_graph);
        val solved                     = final_goal_proved_completely graph_w_keys_expanded: bool;
        val _                          = tracing (if solved then "    In loop. Solved." else "    In loop. Not solved.")
      in
        (if solved then K I else loop) (counter + 1) (pst, graph_w_keys_expanded) 
      end
    else
      (pst, graph);

(* top_down_conjecturing *)
fun top_down_conjecturing (pst:state) (term:term) =
    let
      val initial_graph            = mk_initial_graph term;
      val (final_pst, final_graph) = loop 0 (pst, initial_graph);
    in
      print_proof_of_graph final_pst final_graph
    end;

end;
\<close>

strategy Extend_Leaf =
  Alts [
    Clarsimp,
    Thens [
      Smart_Induct,
      User< simp_all>
    ]
  ]

strategy finish_goal_after_assuming_subgoals_n_conjectures =
  Thens [
    Repeat (Hammer),
    IsSolved
  ]

strategy Attack_On_Or_Node = 
  Ors [
    Thens [
      Smart_Induct,
      Thens [
        Auto,
        IsSolved
      ]
    ],
    Thens [
      Hammer,
      IsSolved
    ]
  ]

(* UI *)
ML\<open> (*This part (the definitions of long_keyword, long_statement, and short_statement) are from
by Pure/Pure.thy in Isabelle/HOL's source code.*)

local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl))
: Token.T list ->
  (bool * Attrib.binding * (xstring * Position.T) list *
   Element.context list * Element.statement)
  *
  Token.T list;

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem _ descr =
  Outer_Syntax.local_theory @{command_keyword top_down_prove} ("state " ^ descr)
    (((long_statement || short_statement) >> (fn (_, _, _, _(*elems*), concl) =>
       (fn lthy =>
          let
            fun stmt_to_stmt_as_string (Element.Shows [((_, _), [(stmt, _)])]) = stmt: string
              | stmt_to_stmt_as_string _ = error "stmt_to_concl_name failed in United_Reasoning";
            val cncl_as_trm  = Syntax.read_term lthy (stmt_to_stmt_as_string concl) |> standardize_vnames: term;
            val standardized_cncl = standardize_vnames cncl_as_trm;
            val cxtx_wo_verbose_warnings =
                Config.put SMT_Config.verbose false lthy
             |> Config.put Metis_Generate.verbose false
             |> Context_Position.set_visible false: Proof.context;
            val pst = Proof.init cxtx_wo_verbose_warnings: Proof.state;
            val _ = tracing "before top_down_conjecturing";
            val _ = Proof_By_Abduction.top_down_conjecturing pst standardized_cncl;
          in
            lthy
          end)))
     );

in

val _ = theorem \<^command_keyword>\<open>top_down_prove\<close> "theorem";

end;
\<close>

end