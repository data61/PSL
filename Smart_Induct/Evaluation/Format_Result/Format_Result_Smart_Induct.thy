theory Format_Result_Smart_Induct
  imports "PSL.PSL" "../../../SeLFiE/Evaluation/Format_Result/Format_Result_Semantic_Induct"
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
    val (file_name::numbers_as_strings) = String.tokens (fn c=> str c = ",") line: string list;
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
val median_value_of_execution_time = lines |> map #execution_time |> sort Int.compare |>  Utils.flip nth 547
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
~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, ~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 16.9) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 27.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 28.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 20.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 0.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 40.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 19.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 23.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 0.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 9.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 17.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 16.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 15.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 19.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 9.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 21.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 16.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 18.2) (overall, 21.5)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 31.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 44.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 49.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 5.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 24.6) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 38.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 15.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 9.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 42.9) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 26.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 24.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 36.6) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 29.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 36.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 33.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 40.9) (overall, 36.3)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 39.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 50.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 56.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 5.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 43.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 46.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 15.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 9.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 51.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 39.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 33.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 41.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 38.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 37.9) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 33.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 50.0) (overall, 44.7)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 53.9) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 50.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 59.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 80.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 15.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 43.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 61.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 30.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 9.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 57.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 47.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 45.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 51.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 42.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 47.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 33.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 59.1) (overall, 50.3)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 60.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 62.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 67.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 80.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 15.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 50.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 67.3) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 30.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 18.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 57.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 54.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 48.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 61.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 45.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 47.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 59.1) (overall, 56.2)};
ddplot coordinates {(~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Hybrid_Logic/Hybrid_Logic.thy, 64.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/BinomialHeap.thy, 62.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Binomial-Heaps/SkewBinomialHeap.thy, 67.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Boolean_Expression_Checkers/Boolean_Expression_Checkers.thy, 80.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/CoreC++/TypeSafe.thy, 15.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Depth-First-Search/DFS.thy, 70.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Finger-Trees/FingerTree.thy, 52.4) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Goodstein_Lambda/Goodstein_Lambda.thy, 71.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KBPs/Kripke.thy, 30.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Build.thy, 10.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/KD_Tree.thy, 77.8) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/KD_Tree/Nearest_Neighbors.thy, 18.2) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/LTL/Disjunctive_Normal_Form.thy, 57.1) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/NormByEval/NBE.thy, 58.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/PCF/OpSem.thy, 48.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Priority_Search_Trees/PST_RBT.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Probabilistic_Timed_Automata/library/Graphs.thy, 61.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Rep_Fin_Groups/Rep_Fin_Groups.thy, 45.5) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/Simpl/SmallStep.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1A.thy, 72.7) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/VerifyThis2019/Challenge1B.thy, 50.0) (~/Workplace/PSL_Perform/PSL/Smart_Induct/Evaluation/ZFC_in_HOL/Cantor_NF.thy, 59.1) (overall, 57.4)};
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

ML\<open>
val numb_of_Challenge = 12.0;
val numb_of_DFS       = 10.0;
val numb_of_Goodstein = 52.0;
val numb_of_NN        = 11.0;
val numb_of_PST       = 24.0;
val numb_of_HL        = 89.0;
val numb_of_NBE       = 104
val numb_of_SStep     = 66.0;
val numb_of_Cantor    = 22.0;
val numb_of_Skew      = 177.0;
val numb_of_BinomHeap = 117.0;
val numb_of_Boolean   = 20.0;
val numb_of_Core_Type = 20.0;
val numb_of_DFS       = 10.0;
val numb_of_FingerTr  = 126.0;
val numb_of_Goodstein = 52.0;
val numb_of_Kripke    = 13.0;
val numb_of_KD_Build  = 10.0;
val numb_of_KD_KD     = 9.0;
val numb_of_KD_NN     = 11.0;
val numb_of_LTL_Disj  = 35.0;
val numb_of_NBE       = 104;
val numb_of_PCF_OpSem = 33.0;
val numb_of_PST_RBT   = 24.0;
val numb_of_PAuto_Grap= 41.0;
val numb_of_Rep_Fin_G = 99.0;
val numb_of_Challeg_1A= 11.0;
val numb_of_Challeg_1B= 6.0;

val total_numb        = length lines |> Real.fromInt;
\<close>

(*faster smarter*)                              
ML\<open>
fun get_coincidence_rate_top_n (points:datapoints) (top_n:int) =
  let
    val numb_of_points           = points |> length |> Real.fromInt: real;
    val points_within_timeout = filter (fn point => #execution_time point < 5000) points;
    val datapoints_among_top_n   = points_among_top_n top_n points_within_timeout;
    val numb_of_points_among_top = datapoints_among_top_n |> length |> Real.fromInt: real;
  in
    (numb_of_points_among_top / numb_of_points): real
  end;

fun datapoints_to_coincidence_rates (points:datapoints) (top_ns:ints) = map (get_coincidence_rate_top_n points) top_ns: real list;

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

fun get_coincidence_rate_for_top_ns_for_file (points:datapoints) (top_ns:ints) (file_name:string) =
  let
    val datapoints_in_file = points_in_file file_name points
  in
    map (get_coincidence_rate_top_n datapoints_in_file) top_ns: real list
  end;

fun get_return_rates_for_points (points:datapoints) (timeout:int) =
  let
    val numb_of_datapoints = length points |> Real.fromInt: real;
    val datapoints_in_timeout = filter (fn datapoint => #execution_time datapoint < timeout) points;
    val numb_of_datapoints_in_timeout = length datapoints_in_timeout |> Real.fromInt: real;
    val return_rate = (numb_of_datapoints_in_timeout / numb_of_datapoints)
  in
    return_rate
  end;

fun get_return_rate_for_file (points:datapoints) (file_name:string) (timeout:int) =
  let
    val datapoints_in_file = points_in_file file_name points;
    val return_rate = get_return_rates_for_points datapoints_in_file timeout
  in
    return_rate
  end;

fun get_return_rates_for_file (points:datapoints) (timeouts:ints) (file_name:string) =
  map (get_return_rate_for_file points file_name) timeouts;

val overall_name = "1/2/3/4/5/6/7/overall"

fun points_in_file_with_overall   (file_name:string) (points:datapoints) = 
  if file_name = overall_name
  then points
  else filter (point_is_in_file file_name) points;

fun datapoints_to_coincidence_rate_pairs (points:datapoints) (top_ns:ints) (timeouts:ints)=
  let                  
    val file_names                      = datapoints_to_all_file_names points;
    val overall_coincidence_rates       = (overall_name, datapoints_to_coincidence_rates points top_ns @ map (get_return_rates_for_points points) timeouts): (string * real list);
    val coincidence_rates_for_each_file = map (fn file_name => (file_name, get_coincidence_rate_for_top_ns_for_file points top_ns file_name @ get_return_rates_for_file points timeouts file_name)) file_names: (string * real list) list;
    fun mk_string (fname, reals)        = String.concatWith " & " (fname :: "old" :: (Int.toString o length) (points_in_file_with_overall fname points):: (map (fn real => real_to_percentage_with_precision_str real) reals)) ^ " \\"^"\\": string;
    val result = map (mk_string) (coincidence_rates_for_each_file @ [overall_coincidence_rates])
  in
    result
  end;

val smart_induct_result = datapoints_to_coincidence_rate_pairs lines [1,3,5,10] [200,500,1000,2000,5000];  
(*overall & 1095 & 20.1 & 42.8 & 48.5 & 55.3 & 0.0 & 3.5 & 16.9 & 38.3 & 70.2 \\ *)

\<close>

ML\<open> (*both semantic induct and smart induct*)
val both_results = smart_induct_result @ semantic_induct_result
|> map (String.concat o drop 7 o String.tokens (fn c=> str c = "/"))
|> sort string_ord;

val _ = map tracing both_results;
(*
BinomialHeapsBinomialHeap & new & 117 & 28.2 & 64.1 & 66.7 & 76.9 & 1.7 & 12.8 & 51.3 & 85.5 & 97.4 \\ 
BinomialHeapsBinomialHeap & old & 117 & 25.6 & 48.7 & 48.7 & 60.7 & 0.0 & 0.9 & 7.7 & 23.9 & 77.8 \\ 
BinomialHeapsSkewBinomialHeap & new & 177 & 35.6 & 55.9 & 64.4 & 81.4 & 2.3 & 27.1 & 56.5 & 87.0 & 99.4 \\ 
BinomialHeapsSkewBinomialHeap & old & 177 & 26.0 & 51.4 & 54.2 & 61.6 & 0.0 & 1.1 & 7.9 & 32.8 & 76.3 \\ 
BooleanExpressionCheckersBooleanExpressionCheckers & new & 20 & 60.0 & 80.0 & 90.0 & 100.0 & 30.0 & 60.0 & 85.0 & 100.0 & 100.0 \\ 
BooleanExpressionCheckersBooleanExpressionCheckers & old & 20 & 10.0 & 60.0 & 70.0 & 70.0 & 0.0 & 5.0 & 25.0 & 40.0 & 70.0 \\ 
CoreC++TypeSafe & new & 20 & 15.0 & 20.0 & 25.0 & 25.0 & 0.0 & 0.0 & 5.0 & 15.0 & 35.0 \\ 
CoreC++TypeSafe & old & 20 & 0.0 & 5.0 & 15.0 & 15.0 & 0.0 & 0.0 & 0.0 & 5.0 & 20.0 \\ 
DepthFirstSearchDFS & new & 10 & 20.0 & 80.0 & 80.0 & 90.0 & 20.0 & 70.0 & 100.0 & 100.0 & 100.0 \\ 
DepthFirstSearchDFS & old & 10 & 40.0 & 70.0 & 70.0 & 70.0 & 0.0 & 10.0 & 30.0 & 30.0 & 80.0 \\ 
FingerTreesFingerTree & new & 126 & 40.5 & 45.2 & 45.2 & 57.1 & 4.0 & 17.5 & 38.1 & 58.7 & 68.3 \\ 
FingerTreesFingerTree & old & 126 & 19.0 & 43.7 & 43.7 & 52.4 & 0.0 & 0.8 & 20.6 & 33.3 & 61.1 \\ 
GoodsteinLambdaGoodsteinLambda & new & 52 & 32.7 & 71.2 & 75.0 & 78.8 & 7.7 & 26.9 & 65.4 & 92.3 & 98.1 \\ 
GoodsteinLambdaGoodsteinLambda & old & 52 & 21.2 & 44.2 & 59.6 & 69.2 & 0.0 & 5.8 & 28.8 & 55.8 & 86.5 \\ 
HybridLogicHybridLogic & new & 89 & 47.2 & 58.4 & 62.9 & 65.2 & 13.5 & 28.1 & 44.9 & 64.0 & 79.8 \\ 
HybridLogicHybridLogic & old & 89 & 16.9 & 39.3 & 53.9 & 64.0 & 0.0 & 5.6 & 24.7 & 52.8 & 74.2 \\ 
KBPsKripke & new & 13 & 53.8 & 69.2 & 69.2 & 76.9 & 0.0 & 15.4 & 38.5 & 53.8 & 100.0 \\ 
KBPsKripke & old & 13 & 0.0 & 15.4 & 30.8 & 30.8 & 0.0 & 0.0 & 7.7 & 15.4 & 30.8 \\ 
KDTreeBuild & new & 10 & 10.0 & 10.0 & 10.0 & 10.0 & 0.0 & 0.0 & 0.0 & 20.0 & 60.0 \\ 
KDTreeBuild & old & 10 & 10.0 & 10.0 & 10.0 & 10.0 & 0.0 & 0.0 & 0.0 & 10.0 & 20.0 \\ 
KDTreeKDTree & new & 9 & 77.8 & 77.8 & 100.0 & 100.0 & 11.1 & 33.3 & 88.9 & 100.0 & 100.0 \\ 
KDTreeKDTree & old & 9 & 77.8 & 77.8 & 77.8 & 77.8 & 0.0 & 0.0 & 33.3 & 100.0 & 100.0 \\ 
KDTreeNearestNeighbors & new & 11 & 54.5 & 63.6 & 72.7 & 72.7 & 0.0 & 0.0 & 0.0 & 9.1 & 72.7 \\ 
KDTreeNearestNeighbors & old & 11 & 0.0 & 0.0 & 0.0 & 9.1 & 0.0 & 0.0 & 0.0 & 0.0 & 9.1 \\ 
LTLDisjunctiveNormalForm & new & 35 & 60.0 & 62.9 & 65.7 & 68.6 & 34.3 & 71.4 & 82.9 & 97.1 & 100.0 \\ 
LTLDisjunctiveNormalForm & old & 35 & 17.1 & 48.6 & 54.3 & 54.3 & 0.0 & 14.3 & 25.7 & 74.3 & 94.3 \\ 
NormByEvalNBE & new & 104 & 30.8 & 49.0 & 54.8 & 71.2 & 5.8 & 23.1 & 48.1 & 70.2 & 88.5 \\ 
NormByEvalNBE & old & 104 & 15.4 & 38.5 & 46.2 & 56.7 & 0.0 & 3.8 & 21.2 & 41.3 & 70.2 \\ 
PCFOpSem & new & 33 & 45.5 & 66.7 & 78.8 & 81.8 & 9.1 & 18.2 & 36.4 & 54.5 & 84.8 \\ 
PCFOpSem & old & 33 & 12.1 & 30.3 & 42.4 & 45.5 & 0.0 & 9.1 & 15.2 & 21.2 & 45.5 \\ 
PrioritySearchTreesPSTRBT & new & 24 & 41.7 & 95.8 & 100.0 & 100.0 & 0.0 & 0.0 & 20.8 & 58.3 & 100.0 \\ 
PrioritySearchTreesPSTRBT & old & 24 & 45.8 & 45.8 & 45.8 & 45.8 & 0.0 & 0.0 & 4.2 & 16.7 & 45.8 \\ 
ProbabilisticTimedAutomatalibraryGraphs & new & 41 & 31.7 & 70.7 & 78.0 & 87.8 & 36.6 & 61.0 & 75.6 & 87.8 & 100.0 \\ 
ProbabilisticTimedAutomatalibraryGraphs & old & 41 & 19.5 & 41.5 & 51.2 & 61.0 & 0.0 & 12.2 & 41.5 & 56.1 & 87.8 \\ 
RepFinGroupsRepFinGroups & new & 99 & 41.4 & 58.6 & 67.7 & 68.7 & 5.1 & 17.2 & 29.3 & 47.5 & 76.8 \\ 
RepFinGroupsRepFinGroups & old & 99 & 9.1 & 38.4 & 42.4 & 45.5 & 0.0 & 1.0 & 7.1 & 29.3 & 69.7 \\ 
SimplSmallStep & new & 66 & 45.5 & 75.8 & 77.3 & 77.3 & 15.2 & 21.2 & 33.3 & 47.0 & 83.3 \\ 
SimplSmallStep & old & 66 & 21.2 & 37.9 & 47.0 & 50.0 & 0.0 & 1.5 & 19.7 & 48.5 & 63.6 \\ 
VerifyThis2019Challenge1A & new & 11 & 36.4 & 54.5 & 72.7 & 81.8 & 63.6 & 63.6 & 90.9 & 100.0 & 100.0 \\ 
VerifyThis2019Challenge1A & old & 11 & 72.7 & 72.7 & 72.7 & 72.7 & 0.0 & 27.3 & 54.5 & 90.9 & 100.0 \\ 
VerifyThis2019Challenge1B & new & 6 & 66.7 & 83.3 & 83.3 & 83.3 & 33.3 & 33.3 & 66.7 & 100.0 & 100.0 \\ 
VerifyThis2019Challenge1B & old & 6 & 0.0 & 16.7 & 16.7 & 33.3 & 0.0 & 33.3 & 33.3 & 50.0 & 66.7 \\ 
ZFCinHOLCantorNF & new & 22 & 18.2 & 50.0 & 50.0 & 50.0 & 0.0 & 13.6 & 36.4 & 40.9 & 54.5 \\ 
ZFCinHOLCantorNF & old & 22 & 18.2 & 50.0 & 59.1 & 59.1 & 0.0 & 0.0 & 22.7 & 63.6 & 86.4 \\ 
overall & new & 1095 & 38.2 & 59.3 & 64.5 & 72.7 & 8.8 & 24.7 & 47.8 & 69.8 & 86.8 \\ 
overall & old & 1095 & 20.1 & 42.8 & 48.5 & 55.3 & 0.0 & 3.5 & 16.9 & 38.3 & 70.2 \\ 
*)
\<close>

end
