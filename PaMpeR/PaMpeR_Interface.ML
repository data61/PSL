(*  Title:      PaMpeR_Interface.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    Enable the Proof_advice keyword.
    Using a built in bash egrep to search the trained recommendation database. Outputting most promising 9 methods.
*)

signature PAMPER_INTERFACE = 
sig
  val build_final_trees : string list -> (string * Regression_Tree.final_tree);
  val register_ftrees_command: unit -> unit;
  val PaMpeR_activate : unit -> unit;
  val lookup: Proof.context -> string -> Regression_Tree.final_tree option;
end;

structure PaMpeR_Interface = 
struct

val path = Resources.master_directory @{theory} |> File.platform_path : string;
val path_to_ftrees  = path ^ "/RTrees/" : string
val _               = Isabelle_System.bash ("rm -r " ^ path_to_ftrees ^ "*");
val _               = Isabelle_System.bash ("mkdir " ^ path_to_ftrees);

(*all_method_names: The database has to be present in PSL/PaMpeR/.*)
val all_method_names =
  let
    val bash_script = "while read line \n do echo $line | awk '{print $1;}' \n done < '" ^ path ^ "/method_names" ^ "'" : string;
    val bash_input  = Bash.process bash_script |> #out : string;
    val dist_meth_names = bash_input |> String.tokens (fn c => c = #"\n") |> distinct  (op =);
  in
    dist_meth_names : string list
  end;

structure RT = Regression_Tree;

(* build final trees and register them in a table *)

fun build_ftree (meth_name:string) =
  (tracing ("building a final tree for " ^ meth_name);
   (meth_name, (RT.post_process o RT.get_big_tree o Database.parse_database) meth_name));

(*FIXME: the use of "try" here is unsafe.*)
fun build_final_trees (meth_names:string list) = Par_List.map (try build_ftree) meth_names
 |> (fn opts => (filter is_none opts |> length |> Int.toString |> (fn numb => tracing ("The number of failures is " ^ numb)); opts))
 |> filter is_some
 |> map the;

structure Data = Generic_Data
(
  type T     = Regression_Tree.final_tree Symtab.table;
  val empty  = Symtab.empty : T;
  val extend = I;
  val merge  = Symtab.merge (K true);
);

fun lookup ctxt = (Symtab.lookup o Data.get) (Context.Proof ctxt);

fun update (k, v)  = Data.map (Symtab.update_new (k, v))
  |> Context.theory_map
  |> Local_Theory.background_theory;

val reset = Data.map (fn _ => Symtab.empty)
  |> Context.theory_map
  |> Local_Theory.background_theory;

fun get_all_final_trees_gen how = how all_method_names:  (string * Regression_Tree.final_tree) list;

fun register_final_trees (lthy:local_theory) = fold update (get_all_final_trees_gen build_final_trees) lthy;

fun mk_parser (func) = fn (tkns:Token.T list) => (func, tkns);

fun register_ftrees_command _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword build_regression_trees}
      "build regression trees and register them from databases."
      (mk_parser register_final_trees);
  in () end;

(*TODO: This line should be moved out.*)
val _ = register_ftrees_command ();

(* reset the table containing final trees. *)
fun reset_regression_tree_table_cmd _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword reset_regression_tree_table}
      "reset the table containing final trees to Table.empty."
      (mk_parser reset);
  in () end;

(*TODO: This line should be moved out.*)
val _ = reset_regression_tree_table_cmd ();

(* print out regression trees in PaMpeR/RTrees *)

(*FIXME: use the option monad more effectively.*)
fun print_out_ftree (ctxt:Proof.context) (meth_name:string) =
  let
    val final_tree   = lookup ctxt meth_name: Regression_Tree.final_tree option;
    val _ = if is_none final_tree then tracing ("no final tree available for " ^ meth_name) else ();
    val ftree_as_str = Option.map Regression_Tree.print_final_tree final_tree: string option;
    val bash_command =
      if is_some ftree_as_str
      then "echo -n '" ^ the ftree_as_str  ^ "' > " ^ path_to_ftrees ^ meth_name
      else "echo -n '" ^ "No final tree available for " ^ meth_name ^ "'";
    val exit_int     = Isabelle_System.bash (bash_command:string);
    val _ = if exit_int = 0 then () else tracing "print_out_ftree failed! The bach returned a non-0 value.";
  in
    ()
  end;

fun print_out_all_ftrees (meth_names:string list) (lthy:local_theory) =
  (Par_List.map (print_out_ftree lthy) meth_names; lthy);

fun register_printout_all_ftree_cmd _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword print_out_regression_trees}
      "build regression trees and register them from databases."
      (mk_parser (print_out_all_ftrees all_method_names));
  in () end;

(*TODO: This line should be moved out.*)
val _ = register_printout_all_ftree_cmd ();

(* read regression trees printed in in PaMpeR/RTrees *)
val read_regression_trees =
  let
    fun get_ptree (meth_name:string) = Bash.process ("head -1 " ^ path_to_ftrees ^ meth_name) |> #out: string;
    fun read_final_tree (meth_name:string) = (meth_name, Regression_Tree.parse_printed_tree (get_ptree meth_name));
    fun read_final_trees (meth_names:string list) = Par_List.map read_final_tree meth_names;
    fun register_final_trees (lthy:local_theory) = fold update (get_all_final_trees_gen read_final_trees) lthy;
  in register_final_trees end;

fun read_regression_trees_cmd _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword read_regression_trees}
      "build regression trees and register them from databases."
      (mk_parser read_regression_trees);
  in () end;

(*TODO: This line should be moved out.*)
val _ = read_regression_trees_cmd ();

fun PaMpeR_activate _ =
let

fun get_top_5 (pstate:Proof.state) =
  let
    val ass_results = Assertions.eval_assertion_for_ML_bool pstate;
    val ctxt = Proof.context_of pstate;
    fun get_ftree (meth_name:string) = lookup ctxt meth_name: Regression_Tree.final_tree option;
    val get_exp = Regression_Tree.lookup_exp ass_results;
    fun get_top_result' (best_meth, best_exp) (meth_name::names:string list) =
     let
       val expct = meth_name |> get_ftree |> the |> get_exp;
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
        val _ = tracing ("A promising method is " ^ fst top ^ " with expectation of " ^ exp_str);
      in
        remove (op =) (fst top) meth_names
      end;
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
       get_top_result wo_9)))))))))
(*
    val (top_meth_name, top_exp) = get_top_result (all_method_names ()) |> apsnd Real.toString : (string * string);
*)

  in () end;

(*TODO: rename simp_interface.*)
val simp_interface = Toplevel.keep_proof (fn Tstate =>
  let
    val state = Toplevel.proof_of Tstate
  in
    get_top_5 state
  end);

val _ = Outer_Syntax.command @{command_keyword proof_advice} "Method recommender"
    (Scan.succeed simp_interface);
in
  ()
end;

end;

PaMpeR_Interface.PaMpeR_activate ();
