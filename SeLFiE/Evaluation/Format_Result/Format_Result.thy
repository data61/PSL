theory Format_Result
  imports "PSL.PSL"
begin

ML_file  "../../../LiFtEr/Matrix_sig.ML"
ML_file  "../../../LiFtEr/Matrix_Struct.ML"

ML\<open>
val path = File.platform_path (Resources.master_directory @{theory}) ^ "/tacas2021_timeout5.csv";
val get_lines = split_lines o TextIO.inputAll o TextIO.openIn;
\<close>

ML\<open>
type datapoint =
 {file_name                       :string,
  line_number                     : int,
  rank                            : int option,
  score                           : real option,
  execution_time                  : int(*,
  arbitrary                       : bool,
  rule                            : bool,
  hand_writte_rule                : bool,
  induct_on_subterm               : bool*)
  };

type datapoints = datapoint list;

fun int_to_bool 1 = true
  | int_to_bool 0 = false
  | int_to_bool _ = error "int_to_bool";

fun read_one_line (line:string) =
  let
    val (file_name::numbers_as_strings) = String.tokens (fn c=> str c = ";") line: string list;
    val line_number    = nth numbers_as_strings 0 |> Int.fromString  |> the;
    val rank           = nth numbers_as_strings 1 |> Int.fromString;
    val score          = nth numbers_as_strings 2 |> Real.fromString;
    val execution_time = nth numbers_as_strings 3 |> Int.fromString  |> the;
    val result =
          {file_name                        = file_name,
           line_number                      = line_number,
           rank                             = rank,
           score                            = score,
           execution_time                   = execution_time(*
           arbitrary                        = nth numbers_as_ints 7  |> the |> int_to_bool,
           rule                             = nth numbers_as_ints 8  |> the |> int_to_bool,
           hand_writte_rule                 = nth numbers_as_ints 9  |> the |> int_to_bool,
           induct_on_subterm                = nth numbers_as_ints 10 |> the |> int_to_bool*)
           };
  in
    result
  end;

val lines = get_lines path
  |> (map (try read_one_line))
 |> (fn x => (tracing (Int.toString (length x)) ; x))
  |> Utils.somes
 |> (fn x => (tracing (Int.toString (length x)) ; x))
: datapoints

\<close>
ML\<open>
fun real_to_percentage_with_precision (real:real) = (1000.0 * real |> Real.round |> Real.fromInt) / 10.0: real;
fun real_to_percentage_with_precision_str (real:real) = real_to_percentage_with_precision real |> Real.toString: string;
fun real_to_percentage     (real:real) = 100.0 * real |> Real.round             : int;
fun real_to_percentage_str (real:real) = real_to_percentage real |> Int.toString: string;
fun print_pair (label:string, coincidence_rate:real) =
  enclose "(" ")" (label ^ ", " ^ real_to_percentage_str coincidence_rate);
fun print_pair_with_precision (label:string, coincidence_rate:real) =
  enclose "(" ")" (label ^ ", " ^ real_to_percentage_with_precision_str coincidence_rate);
fun print_one_line (pairs:(string * real) list) =
  "\addplot coordinates {" ^ (String.concatWith " " (map print_pair_with_precision pairs)) ^ "};\n": string;

fun point_is_in_file (file_name:string) (point:datapoint)   = #file_name point = file_name;
fun points_in_file   (file_name:string) (points:datapoints) = filter (point_is_in_file file_name) points;

fun point_is_among_top_n (top_n:int) (point:datapoint) =
   Option.map (fn rank => rank <= top_n) (#rank point)
|> Utils.is_some_true;

fun points_among_top_n (top_n:int) (points:datapoints) = filter (point_is_among_top_n top_n) points;

fun get_coincidence_rate_top_n (points:datapoints) (top_n:int) =
  let
    val numb_of_points           = points |> length |> Real.fromInt: real;
    val datapoints_among_top_n   = points_among_top_n top_n points;
    val numb_of_points_among_top = datapoints_among_top_n |> length |> Real.fromInt: real;
  in
    (numb_of_points_among_top / numb_of_points): real
  end;
\<close>
ML\<open>
fun get_coincidence_rate_for_file_for_top_n (points:datapoints) (file_name:string) (top_n:int) =
  let
    val datapoints_in_file                 = points_in_file file_name points
  in
    get_coincidence_rate_top_n datapoints_in_file top_n: real
  end;

fun datapoints_to_all_file_names (points:datapoints) = map #file_name points |> distinct (op =);

fun datapoints_to_coincidence_rates (points:datapoints) (top_ns:ints) = map (get_coincidence_rate_top_n points) top_ns: real list;

fun attach_file_name_to_coincidence_rates (file_name:string) (rates) = map (fn rate => (file_name, rate)) rates;
\<close>
ML\<open>
fun datapoints_to_coincidence_rate_pairs_for_one_file (points:datapoints) (file_name:string) (top_ns:ints) =
  map (fn top_n => (file_name, get_coincidence_rate_for_file_for_top_n points file_name top_n)) top_ns: (string * real) list;
\<close>

ML\<open>
fun datapoints_to_coincidence_rate_pairs (points:datapoints) (top_ns:ints) =
  let
val _ = tracing (Int.toString (length points));
    val file_names                      = datapoints_to_all_file_names points;
    val overall_coincidence_rates       = datapoints_to_coincidence_rates points top_ns |> attach_file_name_to_coincidence_rates "overall": (string * real) list;
    val coincidence_rates_for_each_file = map (fn file_name => datapoints_to_coincidence_rate_pairs_for_one_file points file_name top_ns) file_names: (string * real) list list;
    val all_pairs                       = coincidence_rates_for_each_file @ [overall_coincidence_rates]: (string * real) list list;
  in
    all_pairs |> Matrix.matrix_to_row_of_columns_matrix |> Matrix.transpose_rcmatrix |> the |> Matrix.row_of_columns_matrix_to_matrix
  end;
\<close>


ML\<open> val tikz_for_coincidence_rates = get_coincidence_rate_for_file_for_top_n lines "~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy" 1;\<close>

ML\<open>(*result*)
fun from_pair_matrix_to_tikz_barplot (pairs) = pairs
|> map print_one_line
|> (fn addplots:strings => (String.concatWith ", " (datapoints_to_all_file_names lines) ^ "\n") :: addplots)
|> String.concat
|> tracing;

val coincidence_rates_for_files = 
   datapoints_to_coincidence_rate_pairs lines [1,2,3,5,8,10]
|> from_pair_matrix_to_tikz_barplot;

(*
~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, ~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 30.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 28.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 35.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 60.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 15.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 40.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 32.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 50.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 53.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 72.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 60.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 45.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 41.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 31.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 46.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 45.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 36.4) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 66.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 22.7) (overall, 39.2)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 41.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 53.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 49.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 80.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 80.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 43.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 57.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 60.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 69.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 81.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 62.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 60.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 75.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 68.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 61.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 65.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 54.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 83.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 40.9) (overall, 54.6)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 49.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 64.1) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 55.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 80.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 80.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 46.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 71.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 61.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 69.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 81.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 62.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 66.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 95.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 70.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 66.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 75.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 54.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 83.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 68.2) (overall, 61.1)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 54.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 67.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 64.4) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 90.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 25.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 80.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 46.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 75.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 68.5) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 69.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 90.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 65.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 78.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 78.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 77.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 77.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 83.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 77.3) (overall, 66.9)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 67.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 70.1) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 78.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 25.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 90.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 56.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 78.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 70.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 76.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 90.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 68.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 78.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 87.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 79.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 77.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 81.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 83.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 77.3) (overall, 73.2)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/NormByEval/NBE.thy, 71.2) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/BinomialHeap.thy, 77.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 81.4) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/CoreC++/TypeSafe.thy, 25.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Depth-First-Search/DFS.thy, 90.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Finger-Trees/FingerTree.thy, 58.7) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 78.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 70.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KBPs/Kripke.thy, 76.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Build.thy, 20.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/KD_Tree.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/KD_Tree/Nearest_Neighbors.thy, 90.9) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/LTL/Disjunctive_Normal_Form.thy, 68.6) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/PCF/OpSem.thy, 81.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Priority_Search_Trees/PST_RBT.thy, 100.0) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 87.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 79.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/Simpl/SmallStep.thy, 77.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1A.thy, 81.8) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/VerifyThis2019/Challenge1B.thy, 83.3) (~/Workplace/PSL_Perform/PSL/SeLFiE/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 77.3) (overall, 75.3)};
*)
\<close>

declare [[ML_print_depth=2000]]

ML\<open>(*result*)
fun sort_datapoints_wrt_execution_time (points:datapoints) =
 sort (fn (poin1, poin2) => Int.compare (#execution_time poin1, #execution_time poin2)) points: datapoints;
       
fun milli_sec_to_sec_with_precision (milli:int) =
  (((Real.fromInt milli) / 100.0) |> Real.round |> Real.fromInt) / 10.0;

val pairs_of_successful_points =
   sort_datapoints_wrt_execution_time lines
|> Utils.index
|> filter (is_some o #rank o snd)
|> map (fn (index, point) => (index, #execution_time point |> milli_sec_to_sec_with_precision));

val pairs_of_failure_points =
   sort_datapoints_wrt_execution_time lines
|> Utils.index
|> filter (is_none o #rank o snd)
|> map (fn (index, point) => (index, #execution_time point |> milli_sec_to_sec_with_precision));

fun print_pairs_real pairs = map (fn (index, time) => "(" ^ Int.toString index ^ ", " ^ Real.toString time ^ ")") pairs |> String.concatWith " ";

print_pairs_real pairs_of_successful_points;
print_pairs_real pairs_of_failure_points;
\<close>

(*faster smarter*)                              
ML\<open>
fun get_coincidence_rate_for_top_ns_for_file (points:datapoints) (top_ns:ints) (file_name:string) =
  let
    val datapoints_in_file = points_in_file file_name points
  in
    map (get_coincidence_rate_top_n datapoints_in_file) top_ns: real list
  end;

fun datapoints_to_coincidence_rate_pairs (points:datapoints) (top_ns:ints) =
  let
    val file_names                      = datapoints_to_all_file_names points;
    val overall_coincidence_rates       = datapoints_to_coincidence_rates points top_ns |> attach_file_name_to_coincidence_rates "overall": (string * real) list;
    val coincidence_rates_for_each_file = map (fn file_name => (file_name, get_coincidence_rate_for_top_ns_for_file points top_ns file_name)) file_names: (string * real list) list;
    fun mk_string (fname, reals)        = String.concatWith " & " (fname :: (map (fn real => real_to_percentage_with_precision_str real) reals)) : string;
    val _ = map (tracing o mk_string) (coincidence_rates_for_each_file)
  in
    ()
  end;

val _ = datapoints_to_coincidence_rate_pairs lines [1,3,5,10];

\<close>

(*faster smarter*)                              
ML\<open>
fun get_coincidence_rate_for_top_ns_for_file (points:datapoints) (top_ns:ints) (file_name:string) =
  let
    val datapoints_in_file = points_in_file file_name points
  in
    map (get_coincidence_rate_top_n datapoints_in_file) top_ns: real list
  end;

fun points_in_file_with_overall   (file_name:string) (points:datapoints) = 
  if file_name = "overall"
  then points
  else filter (point_is_in_file file_name) points;

fun datapoints_to_coincidence_rate_pairs (points:datapoints) (top_ns:ints) =
  let
    val file_names                      = datapoints_to_all_file_names points;
    val overall_coincidence_rates       = ("overall", datapoints_to_coincidence_rates points top_ns): (string * real list);
    val coincidence_rates_for_each_file = map (fn file_name => (file_name, get_coincidence_rate_for_top_ns_for_file points top_ns file_name)) file_names: (string * real list) list;
    fun mk_string (fname, reals)        = String.concatWith " & " (fname :: (Int.toString o length) (points_in_file_with_overall fname points):: (map (fn real => real_to_percentage_with_precision_str real) reals)) ^ " \\"^"\\": string;
    val _ = map (tracing o mk_string) (coincidence_rates_for_each_file @ [overall_coincidence_rates])
  in
    ()
  end;

val _ = datapoints_to_coincidence_rate_pairs lines [1,3,5,10];

(*
NBE.thy & 30.8 & 49.0 & 54.8 & 71.2 
BinomialHeap.thy & 28.2 & 64.1 & 67.5 & 77.8 
SkewBinomialHeap.thy & 35.6 & 55.9 & 64.4 & 81.4 
BooleanExpressionCheckers.thy & 60.0 & 80.0 & 90.0 & 100.0 
TypeSafe.thy & 15.0 & 20.0 & 25.0 & 25.0 
DFS.thy & 20.0 & 80.0 & 80.0 & 90.0 
FingerTree.thy & 40.5 & 46.8 & 46.8 & 58.7 
Goodstein_Lambda.thy & 32.7 & 71.2 & 75.0 & 78.8 
HybridLogic.thy & 50.6 & 61.8 & 68.5 & 70.8 
Kripke.thy & 53.8 & 69.2 & 69.2 & 76.9 
Build.thy & 10.0 & 20.0 & 20.0 & 20.0 
KDTree.thy & 77.8 & 77.8 & 100.0 & 100.0 
NearestNeighbors.thy & 72.7 & 81.8 & 90.9 & 90.9 
Disjunctive_Normal_Form.thy & 60.0 & 62.9 & 65.7 & 68.6 
OpSem.thy & 45.5 & 66.7 & 78.8 & 81.8 
PSTRBT.thy & 41.7 & 95.8 & 100.0 & 100.0 
Graphs.thy & 31.7 & 70.7 & 78.0 & 87.8 
RepFinGroups.thy & 46.5 & 66.7 & 77.8 & 79.8 
SmallStep.thy & 45.5 & 75.8 & 77.3 & 77.3 
Challenge1A.thy & 36.4 & 54.5 & 72.7 & 81.8 
Challenge1B.thy & 66.7 & 83.3 & 83.3 & 83.3 
Cantor_NF.thy & 22.7 & 68.2 & 77.3 & 77.3 
overall & 39.2 & 61.1 & 66.9 & 75.3 
*)
\<close>

end