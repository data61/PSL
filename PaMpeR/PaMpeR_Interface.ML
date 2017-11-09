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

(*all_method_names: The database has to be present in PSL/PaMpeR/.*)
fun all_method_names _ = Preprocess.all_method_names;

structure RT = Regression_Tree;

fun build_ftree (meth_name:string) =
  (tracing ("building a final tree for " ^ meth_name);
   (meth_name, (RT.post_process o RT.get_big_tree o Database.parse_database) meth_name));

fun build_final_trees (meth_names:string list) = Par_List.map build_ftree meth_names;

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
  |> Local_Theory.background_theory;;

fun build_all_final_trees _ = (build_final_trees o all_method_names) ();

fun register_final_trees lthy = fold update (build_all_final_trees ()(*dummy*)) lthy;

fun mk_parser (func) = fn (tkns:Token.T list) => (func, tkns);

fun register_ftrees_command _ =
  let
    val _ = Outer_Syntax.local_theory @{command_keyword build_regression_trees}
      "build regression trees and register them from databases."
      (mk_parser register_final_trees);
  in () end;

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
       (remove (op =) (fst top) meth_names)
      end;
(*TODO: better if I use Lazy Sequence here?*)
    val _ =
       get_top_result (all_method_names ()) |> (fn (wo_1) =>
       get_top_result wo_1           |> (fn (wo_2) =>
       get_top_result wo_2           |> (fn (wo_3) =>
       get_top_result wo_3           |> (fn (wo_4) =>
       get_top_result wo_4           |> (fn (wo_5) =>
       get_top_result wo_5           |> (fn (wo_6) =>
       get_top_result wo_6           |> (fn (wo_7) =>
       get_top_result wo_7           |> (fn (wo_8) =>
       get_top_result wo_8           |> (fn (wo_9) =>
       get_top_result wo_9         )))))))))
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
