(* Title:  Evaluate_ASE.thy
   Author Yutaka Nagashima, CIIRC, CTU
*)

theory Evaluate_ASE
  imports "../PaMpeR" Main
begin

ML{*
val path = Resources.master_directory @{theory} |> File.platform_path : string;
val path_to_PaMpeR     = unsuffix "/Evaluate_ASE" path;
val path_to_EvalData   = path ^ "/EvalDatabase": string;
val path_to_rtree      = path_to_PaMpeR ^ "/regression_trees.txt";
val path_to_meth_names = path_to_PaMpeR ^ "/Preprocess/method_names": string;
val path_to_evaluation = path ^ "/evaluation.txt" : string;

(*all_method_names: The database has to be present in PSL/PaMpeR/Preprocess.*)
val all_method_names =
  let
    val bash_script     = "while read line; do echo -e \"$line\n\"; done <" ^ path_to_meth_names : string;
    val bash_input      = Bash.process bash_script |> #out : string;
    val dist_meth_names = bash_input |> String.tokens (fn c => c = #"\n") |> distinct  (op =);
  in
    dist_meth_names : string list
  end;
*}

ML{* fun input_all (accm:string list) (ins:TextIO.instream) =
(* TODO: code-duplication with input_all in MergeDatabase.thy in PaMpeR/Merge_Database. *)
  let
    val one_vec = TextIO.inputLine ins;
    val result = if is_none one_vec then accm else
      let
        val next = the one_vec |> unsuffix "\n";
        val leng = length accm;
        val _ = if leng mod 10000 = 0 then leng |> Int.toString |> tracing else ();
      in
        input_all (accm @ [next]) ins
      end;
  in
    result
  end;
*}

ML{* val lines = input_all [] (TextIO.openIn path_to_EvalData);
val _ = (tracing o Int.toString o length) lines;
*}

ML{* fun get_pairs (line:string) = space_explode " " line
  |> (fn [x, y, z] => (x, y, z) | _ => error "not a triple" );
*}

ML{* val pairs = map get_pairs lines *}

ML{* fun read_one_line (file_nema: string, meth_name:string, ass_result:string) =
let
  val ass_result_bool : bool list = space_explode "," ass_result
    |> List.mapPartial Int.fromString
    |> map (fn x => if x = 1 then true else false)
    |> (fn bs => if length bs = 108 then error "The length of boolean arrays is not always 108" else bs);
in
  (file_nema, meth_name, ass_result_bool)
end;
*}

ML{* val all_lines = map read_one_line pairs: (string * string * bool list) list; *}

ML{*
structure RT = Regression_Tree;
infix 1 liftM;
fun (m liftM f) = Option.map f m;
*}

ML{* fun get_method_rank (human_meth_name:string) (ass_results:bool list) =
  let
    val get_expect = RT.lookup_expect ass_results: RT.final_tree -> real;
    fun get_expect_pair (meth_name:string) =
      let
        val expect = PaMpeR_Interface.lookup @{context} meth_name liftM get_expect: real option;
        val result = expect liftM (fn exp => (meth_name, exp)):(string * real) option;
      in
        result
      end;
    val expect_pairs = map get_expect_pair all_method_names |> filter is_some |> map the: (string * real) list;
    val sorted_pairs = sort (fn (p1, p2) => Real.compare (snd p2, snd p1)) expect_pairs: (string * real) list;
    val total_numb   = sorted_pairs |> length;
    fun meth_is_nth (meth_name:string) = find_index ((equal meth_name) o fst) sorted_pairs + 1: int;
    val mssg = human_meth_name ^ " " ^ (human_meth_name |> meth_is_nth |> Int.toString) ^ " out of "
               ^ Int.toString total_numb ^ "\n"
  in
    mssg
  end;
*}

ML{* fun print_eval_one_line (line_numb: string, human_meth_name:string, ass_results:bool list) = 
let
  val _ = tracing line_numb;
  val mssg : string = get_method_rank human_meth_name ass_results;
  fun print (x:string) = Isabelle_System.bash ("echo -n '" ^ x ^ "' >> " ^ path_to_evaluation);
in
  print mssg
end;
*}

ML{* map print_eval_one_line all_lines *}

end