(*  Title:      PaMpeR_Interface.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    Enable the which_method command.
*)

(*** PAMPER_INTERFACE ***)
signature PAMPER_INTERFACE = 
sig
  val build_final_trees:  string list -> (string * Regression_Tree.final_tree) list;
  val PaMpeR_activate:    unit -> unit;
  val lookup:             Proof.context -> string -> Regression_Tree.final_tree option;
  val get_method_rank:    string -> Proof.state -> string;
end;

(*** PaMpeR_Interface ***)
structure PaMpeR_Interface:PAMPER_INTERFACE = 
struct

infix 1 liftM;
fun (m liftM f) = Option.map f m;
structure RT = Regression_Tree;

val path = Resources.master_directory @{theory} |> File.platform_path : string;
val path_to_meth_names = path ^ "/Preprocess/method_names": string;
val path_to_rtree      = path ^ "/regression_trees.txt";

(*all_method_names: The database has to be present in PSL/PaMpeR/Preprocess.*)
val all_method_names =
  let
    val bash_script     = "while read line; do echo -e \"$line\n\"; done <" ^ path_to_meth_names : string;
    val bash_input      = Isabelle_System.bash_output bash_script |> fst : string;
    val dist_meth_names = bash_input |> String.tokens (fn c => c = #"\n") |> distinct  (op =);
  in
    dist_meth_names : string list
  end;

(* Database to store regression trees. *)
structure Regression_Trees = Generic_Data
(
  type T     = RT.final_tree Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup ctxt = (Symtab.lookup o Regression_Trees.get) (Context.Proof ctxt);

fun update (k, v)  = Regression_Trees.map (Symtab.update_new (k, v))
  |> Context.theory_map
  |> Local_Theory.background_theory;

val reset = Regression_Trees.map (fn _ => Symtab.empty)
  |> Context.theory_map
  |> Local_Theory.background_theory;

(* Database to store quick assertions. *)
(*TODO: this table has at most one element. AList seems to be good enough.*)
structure Dynamic_Feature_Extractor = Generic_Data
(
  type T     = (thm -> Proof.context -> thm list -> bool) list Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun dfe_lookup ctxt = (Symtab.lookup o Dynamic_Feature_Extractor.get) (Context.Proof ctxt);

fun dfe_update (k, v)  = Dynamic_Feature_Extractor.map (Symtab.update_new (k, v))
  |> Context.theory_map
  |> Local_Theory.background_theory;

(* build final trees and register them in a table *)
fun build_ftree (meth_name:string) =
  let
    fun did_success sth =  if is_some sth then " successfully " else " NOT really "; 
    val _ = Utils.debug_mssg true ("building a final tree for " ^ meth_name) ();
    val database = try Database.parse_database meth_name : Database.database option;
    val _ = Utils.debug_mssg true  ("after" ^ did_success database ^ "building database for " ^ meth_name) ();
    val big_tree = Option.map (try RT.get_big_tree) database |> Option.join: RT.growing_tree option;    
    val _ = Utils.debug_mssg true  ("after" ^ did_success big_tree ^ "building big_tree for " ^ meth_name) ();
    val ftree = Option.map (try RT.post_process) big_tree |> Option.join: RT.final_tree option;
    val _ = Utils.debug_mssg true  ("after" ^ did_success ftree ^ "building final_tree for " ^ meth_name) ();
    val result = if is_some ftree then SOME (meth_name, the ftree) else NONE;
  in
   result
  end;

fun build_final_trees (meth_names:string list) = Par_List.map build_ftree meth_names
 |> (fn opts => (filter is_none opts |> length |> Int.toString |> (fn numb => tracing ("The number of failures is " ^ numb)); opts))
 |> filter is_some
 |> map the;

fun register_final_trees (lthy:local_theory) = fold update (build_final_trees all_method_names) lthy;

fun mk_parser func = fn (tkns:Token.T list) => (func, tkns);

(* print out regression trees in PaMpeR/regression_trees.txt *)
fun print_out_ftree (ctxt:Proof.context) (meth_name:string) =
  let
    val final_tree    = lookup ctxt meth_name: RT.final_tree option;
    val _ = if is_none final_tree
            then tracing ("no final tree available for " ^ meth_name)
            else tracing ("final tree available for " ^ meth_name);
    val ftree_as_str  = Option.map RT.print_final_tree final_tree: string option;
    val bash_command  =
      if is_some ftree_as_str
      then "echo -n '" ^ meth_name ^ "," ^ the ftree_as_str ^ "\n" ^ "' >> " ^ path_to_rtree
      else "echo -n '" ^ "No final tree available for " ^ meth_name ^ "'";
    val exit_int     = Isabelle_System.bash (bash_command:string);
    val _ = if exit_int = 0 then () else tracing "print_out_ftree failed! The bach returned a non-0 value.";
  in
    ()
  end;

fun print_out_all_ftrees (meth_names:string list) (lthy:local_theory) =
  (Isabelle_System.bash ("rm " ^ path_to_rtree);
   map (print_out_ftree lthy) meth_names;
   lthy);

(* read regression trees printed in in PaMpeR/regression_trees.txt *)
fun read_regression_trees (lthy:local_theory)=
  let
    val lines = try TextIO.openIn path_to_rtree
      liftM  TextIO.inputAll
      liftM  split_lines
      liftM (rev o tl o rev) (*The last line is empty.*)
      |> (fn SOME sth => sth | NONE => []): string list;
    open Parser_Combinator;
    infix >>=;
    fun get_string (symbols:Symbol.symbol Seq.seq) = symbols |> Seq.list_of |> String.concat: string;
    val parse_one_line =
      many (sat (fn x => x <> ","))  |> token >>= (fn mname_symbols: string Seq.seq =>
      string "," |> token >>= (fn _ =>
      many (sat (Symbol.not_eof)) |> token >>= (fn ptree_symbols:string Seq.seq=>
      (mname_symbols, ptree_symbols) |> apply2 get_string |> (fn (mname, ptree) =>
      result (mname, RT.parse_printed_tree ptree)))));
    fun read_final_tree (line:string) = line
      |> Symbol.explode
      |> parse parse_one_line
      |> Seq.hd
      |> fst;
    fun register_final_trees (lthy:local_theory) = fold (update o read_final_tree) lines lthy;
  in register_final_trees lthy end;

(* build and register fast assertions *)
local

fun get_fast_assertions (lthy:local_theory) =
  let
    fun get_ftrees ctxt = map (the_list o lookup ctxt) all_method_names |> flat: RT.final_tree list;
    val features = lthy |> get_ftrees |> RT.used_features: int list;
    val leng     = length Assertions.assertions: int;
    val dummys   = List.tabulate (leng, (fn _ => fn _ => fn _ => fn _ => true (*dummy value*)));
    fun swap_nth (n:int) (xs:(thm -> Proof.context -> thm list -> bool) list) =
      nth_map (n - 1) (fn _ => nth Assertions.assertions (n - 1)) xs;
    val fast_asserts = fold swap_nth features dummys;
  in
   fast_asserts: (thm -> Proof.context -> thm list -> bool) list
  end;

in

fun register_fast_assertions lthy = dfe_update ("fast_assetions", (get_fast_assertions lthy)) lthy

end;

(* print out qualitative messages to explain why PaMpeR recommends the given methods in the output panel. *)
fun why_method (mname:string) (pstate:Proof.state) =
  let
    val ctxt = Proof.context_of pstate;
    val fast_assertions = (flat o the_list oo dfe_lookup) ctxt "fast_assetions"
                        : (thm -> Proof.context -> thm list -> bool) list;
    val ass_results = if null fast_assertions
      then (tracing "fast_assertions is empty. Did you forget to call build_fast_feature_extractor?";
            Assertions.eval_assertion_for_ML_bool pstate)
      else Assertions.eval_assertion_gen pstate fast_assertions: RT.feature_values ;
    val ftree = lookup ctxt mname: RT.final_tree option;
    val important_feats = ftree liftM RT.important_features ass_results |> these: RT.feature_name list;
    val full_explanations = ass_results ~~ Assertions.explanations: (bool * string) list;
    fun get_mssg (assrt_succ:bool, explanation:string) =
      if assrt_succ
      then "Because " ^ explanation
      else "Because it is not true that " ^ explanation;
    fun print_nth (i:int) = (tracing o get_mssg o nth full_explanations) (i - 1): unit;
    val _ = map print_nth important_feats: unit list;
  in
    ()
  end;

(* parser for the why_method *)
local
  type trans_trans = Toplevel.transition -> Toplevel.transition;
  open Parser_Combinator;
  infix >>=;
in

(*TODO: code duplication with Isar_Interface.ML*)
val parse_method_name = token word >>= result : string parser;

(*TODO: code duplication with Isar_Interface.ML*)
fun tokens_to_string tokens = tokens |> map Token.unparse |> String.concatWith " ";

(*TODO: code duplication with Isar_Interface.ML*)
fun string_parser_to_token_parser (symbols_parser:'a parser) = (fn (tokens:Token.T list) =>
  tokens
  |> tokens_to_string
  |> Symbol.explode
  |> symbols_parser
  |> Seq.hd
  (*This function assumes that the string_parser consumes the entire string.*)
  |> apsnd (K ([]))) : 'a Token.parser;

(*TODO: code duplication with Isar_Interface.ML*)
fun parser_to_trans_trans_parser (inv_p : 'a parser)
  (get_trans_trans : 'a -> trans_trans) =
  string_parser_to_token_parser (inv_p >>= (result o get_trans_trans)) : trans_trans Token.parser;

(*TODO: rename get_trans_trans*)
fun get_trans_trans (method_name:string) =
   (((Toplevel.keep_proof:(Toplevel.state -> unit) -> trans_trans)
   (fn top =>
    let
      val proof_state = Toplevel.proof_of top;
      val _ = why_method method_name proof_state;
    in
     ()
    end)
   ):trans_trans);

end;

(* print out recommendation in the output panel. *)
local

fun get_top_methods (pstate:Proof.state) =
  let
    val ctxt = Proof.context_of pstate;
    val fast_assertions = (flat o the_list oo dfe_lookup) ctxt "fast_assetions"
                        : (thm -> Proof.context -> thm list -> bool) list;
    val ass_results = if null fast_assertions
      then (tracing "fast_assertions is empty. Did you forget to call build_fast_feature_extractor?";
            Assertions.eval_assertion_for_ML_bool pstate)
      else Assertions.eval_assertion_gen pstate fast_assertions: bool list;
    fun get_ftree (meth_name:string) = lookup ctxt meth_name: RT.final_tree option;
    val get_expect = RT.lookup_expect ass_results;
    fun get_top_result' (best_meth, best_exp) (meth_name::names:string list) =
         let
           val expct = meth_name |> get_ftree |>
             (fn SOME ftree => get_expect ftree
               | NONE       => (tracing ("failed at " ^ meth_name);0.0));
         in
           if best_exp < expct
           then get_top_result' (meth_name, expct)    names
           else get_top_result' (best_meth, best_exp) names
         end
      | get_top_result' best_so_far [] = best_so_far;
    fun get_top_result meth_names =
      let
        val top = get_top_result' ("auto", 0.0) meth_names : (string * real);
        val exp_str = top |> snd |>  Real.toString;
        val _ = tracing ("  " ^ fst top ^ " with expectation of " ^ exp_str);
      in
        remove (op =) (fst top) meth_names
      end;
    val _ = tracing "Promising methods for this proof goal are:"
    (*TODO: better if I use Lazy Sequence here?*)
    val _ =
       get_top_result all_method_names |> (fn (wo_1) =>
       get_top_result wo_1             |> (fn (wo_2) =>
       get_top_result wo_2             |> (fn (wo_3) =>
       get_top_result wo_3             |> (fn (wo_4) =>
       get_top_result wo_4             |> (fn (wo_5) =>
       get_top_result wo_5             |> (fn (wo_6) =>
       get_top_result wo_6             |> (fn (wo_7) =>
       get_top_result wo_7             |> (fn (wo_8) =>
       get_top_result wo_8             |> (fn (wo_9) =>
       get_top_result wo_9             |> (fn (wo_10) =>
       get_top_result wo_10            |> (fn (wo_11) =>
       get_top_result wo_11            |> (fn (wo_12) =>
       get_top_result wo_12            |> (fn (wo_13) =>
       get_top_result wo_13            |> (fn (wo_14) =>
       get_top_result wo_14            |> (fn (wo_15) =>
       get_top_result wo_15)))))))))))))))
  in () end;
in

val which_method_cmd = Toplevel.keep_proof (fn Tstate =>
  let
    val state = Toplevel.proof_of Tstate
  in
    get_top_methods state
  end);

end;

(* Register Isar commands. *)
fun PaMpeR_activate _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword build_regression_trees}
      "build regression trees and register them from databases." (mk_parser register_final_trees);

    val _ = Outer_Syntax.local_theory @{command_keyword reset_regression_tree_table}
      "reset the table containing final trees to Table.empty." (mk_parser reset);

    val _ = Outer_Syntax.local_theory @{command_keyword print_out_regression_trees}
      "print-out regression trees stored in memory to PaMpeR/regression_trees.txt."
      (mk_parser (print_out_all_ftrees all_method_names));

    val _ = Outer_Syntax.local_theory @{command_keyword read_regression_trees}
      "read regression trees in PaMpeR/regression_trees.txt and register them from databases."
      (mk_parser read_regression_trees);

    val _ = Outer_Syntax.command @{command_keyword which_method} "recommend which method to use."
        (Scan.succeed which_method_cmd);

   val _ = Outer_Syntax.command @{command_keyword why_method}
        "give qualitative explanations as to why one should use the given method."
        (parser_to_trans_trans_parser parse_method_name get_trans_trans);

    val _ = Outer_Syntax.local_theory @{command_keyword build_fast_feature_extractor}
      "build a quick version of feature extractor by ignoring unrelevant assertions."
      (mk_parser register_fast_assertions)
  in
    ()
  end;

type trans_trans = Toplevel.transition -> Toplevel.transition;

(*TODO: remove the code-duplication with get_top_methods.*)
fun get_method_rank (human_meth_name:string) (pstate:Proof.state) =
  let
    val ctxt = Proof.context_of pstate;
    val fast_assertions = (flat o the_list oo dfe_lookup) ctxt "fast_assetions"
                        : (thm -> Proof.context -> thm list -> bool) list;
    val ass_results = if null fast_assertions
      then (tracing "fast_assertions is empty. Did you forget to call build_fast_feature_extractor?";
            Assertions.eval_assertion_for_ML_bool pstate)
      else Assertions.eval_assertion_gen pstate fast_assertions: bool list;
    val get_expect = RT.lookup_expect ass_results: RT.final_tree -> real;
    fun get_expect_pair (meth_name:string) =
      let
        val expect = lookup ctxt meth_name liftM get_expect: real option;
        val result = expect liftM (fn exp => (meth_name, exp)):(string * real) option;
      in
        result
      end;
    val expect_pairs = map get_expect_pair all_method_names |> filter is_some |> map the: (string * real) list;
    val sorted_pairs = sort (fn (p1, p2) => Real.compare (snd p2, snd p1)) expect_pairs: (string * real) list;
    val total_numb   = sorted_pairs |> length;
    fun meth_is_nth (meth_name:string) = find_index ((equal meth_name) o fst) sorted_pairs + 1: int;
    val mssg = human_meth_name ^ " " ^ (human_meth_name |> meth_is_nth |> Int.toString) ^ " out of "
               ^ Int.toString total_numb 
  in
    mssg:string
  end;

fun show_method_rank (meth_name:string) (pstate:Proof.state) = tracing (get_method_rank meth_name pstate);

(*TODO: rename get_trans_trans and remove the code duplication with the above function of the same name.*)
fun get_trans_trans (method_name:string) =
   (((Toplevel.keep_proof:(Toplevel.state -> unit) -> trans_trans)
   (fn top =>           
    let
      val proof_state = Toplevel.proof_of top;
      val _ = show_method_rank method_name proof_state;
    in
     ()
    end)
   ):trans_trans);

val _ = Outer_Syntax.command @{command_keyword rank_method}
  "given a method name and proof state, shows which rank the which_method command gives to the method in the proof state."
  (parser_to_trans_trans_parser parse_method_name get_trans_trans);

end;

PaMpeR_Interface.PaMpeR_activate ();
