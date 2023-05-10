(*
 * TDC.thy
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
theory TDC
  imports "../TBC/TBC"
  keywords "prove" :: thy_goal_stmt
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

fun parallel_filter_in_or_out (filter_in:bool) (condition:'a -> bool) (xs:'a list) =
let
  val bools          = Par_List.map condition xs: bool list;
  val pairs          = xs ~~ bools              : ('a * bool) list;
  val filtered_pairs = if filter_in
                       then filter     snd pairs
                       else filter_out snd pairs: ('a * bool) list;
  val result         = map fst filtered_pairs   : 'a list;
in
  result
end;

fun parallel_filter     (condition:'a -> bool) (xs:'a list) = parallel_filter_in_or_out true  condition xs;
fun parallel_filter_out (condition:'a -> bool) (xs:'a list) = parallel_filter_in_or_out false condition xs;

\<close>

(*** Top_Down_Util ***)
ML_file \<open>Top_Down_Util.ML\<close>
ML_file \<open>Top_Down_Util2.ML\<close>
ML_file \<open>Generalise_By_Renaming.ML\<close>



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

ML_file \<open>Generalise_Then_Extend.ML\<close>

ML_file \<open>Abstract_Same_Term.ML\<close>
ML_file \<open>Remove_Function.ML\<close>

ML\<open>
(*** structure Remove_Outermost_Assumption ***)
structure Remove_Outermost_Assumption: TOP_DOWN_CONJECTURING =
struct

fun top_down_conjectures _ (trm:term) = try Logic.dest_implies trm <$> snd <$> pair "remove_assumption" |> the_list: (string * term) list;

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
\<close>

ML_file \<open>All_Top_Down_Conjecturing.ML\<close>
ML_file \<open>And_Node.ML\<close>
ML_file \<open>Or_Node.ML\<close>
ML_file \<open>Or2And_Edge.ML\<close>
ML_file \<open>Proof_Graph_Node.ML\<close>
ML_file \<open>Proof_Graph_Node_Util.ML\<close>
ML_file \<open>Proof_Graph.ML\<close>
ML_file \<open>Proof_Graph_Util.ML\<close>
ML_file \<open>Proof_By_Abduction_Util.ML\<close>
ML_file \<open>Proof_By_Abduction.ML\<close>

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
  Outer_Syntax.local_theory @{command_keyword prove} ("state " ^ descr)
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
            val _ = Proof_By_Abduction.top_down_conjecturing pst standardized_cncl;
          in
            lthy
          end)))
     );

in

val _ = theorem \<^command_keyword>\<open>prove\<close> "prove";

end;
\<close>

end