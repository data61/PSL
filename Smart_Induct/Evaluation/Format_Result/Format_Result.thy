theory Format_Result
  imports "PSL.PSL"
begin

ML_file  "../../../LiFtEr/Matrix_sig.ML"
ML_file  "../../../LiFtEr/Matrix_Struct.ML"

ML\<open>
val path = File.platform_path (Resources.master_directory @{theory}) ^ "/FMCAD2020.csv";
val get_lines = split_lines o TextIO.inputAll o TextIO.openIn;

type datapoint =
 {file_name                       :string,
  numb_of_candidates_after_step_1 : int,
  numb_of_candidates_after_step_2a: int,
  numb_of_candidates_after_step_2b: int,
  line_number                     : int,
  rank                            : int option,
  score                           : int,
  execution_time                  : int,
  arbitrary                       : bool,
  rule                            : bool,
  hand_writte_rule                : bool,
  induct_on_subterm               : bool
  };

type datapoints = datapoint list;

fun int_to_bool 1 = true
  | int_to_bool 0 = false
  | int_to_bool _ = error "int_to_bool";

fun read_one_line (line:string) =
  let
    val (file_name::numbers_as_strings) = String.tokens (fn c=> str c = ",") line: string list;
    val numbers_as_ints = map (Int.fromString) numbers_as_strings: int option list;
    val result =
          {file_name                        = file_name,
           line_number                      = nth numbers_as_ints 0 |> the,
           rank                             = nth numbers_as_ints 1,
           numb_of_candidates_after_step_1  = nth numbers_as_ints 2  |> the,
           numb_of_candidates_after_step_2a = nth numbers_as_ints 3  |> the,
           numb_of_candidates_after_step_2b = nth numbers_as_ints 4  |> the,
           score                            = nth numbers_as_ints 5  |> the,
           execution_time                   = nth numbers_as_ints 6  |> the,
           arbitrary                        = nth numbers_as_ints 7  |> the |> int_to_bool,
           rule                             = nth numbers_as_ints 8  |> the |> int_to_bool,
           hand_writte_rule                 = nth numbers_as_ints 9  |> the |> int_to_bool,
           induct_on_subterm                = nth numbers_as_ints 10 |> the |> int_to_bool
           };
  in
    result
  end;

val lines = get_lines path
  |> (map (try read_one_line))
  |> Utils.somes: datapoints;

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

fun get_coincidence_rate_for_file_for_top_n (points:datapoints) (file_name:string) (top_n:int) =
  let
    val datapoints_in_file                 = points_in_file file_name points
  in
    get_coincidence_rate_top_n datapoints_in_file top_n: real
  end;

fun datapoints_to_all_file_names (points:datapoints) = map #file_name points |> distinct (op =);

fun datapoints_to_coincidence_rates (points:datapoints) (top_ns:ints) = map (get_coincidence_rate_top_n points) top_ns: real list;

fun attach_file_name_to_coincidence_rates (file_name:string) (rates) = map (fn rate => (file_name, rate)) rates;

fun datapoints_to_coincidence_rate_pairs_for_one_file (points:datapoints) (file_name:string) (top_ns:ints) =
  map (fn top_n => (file_name, get_coincidence_rate_for_file_for_top_n points file_name top_n)) top_ns: (string * real) list;

fun datapoints_to_coincidence_rate_pairs (points:datapoints) (top_ns:ints) =
  let
    val file_names                      = datapoints_to_all_file_names points;
    val overall_coincidence_rates       = datapoints_to_coincidence_rates points top_ns |> attach_file_name_to_coincidence_rates "overall": (string * real) list;
    val coincidence_rates_for_each_file = map (fn file_name => datapoints_to_coincidence_rate_pairs_for_one_file points file_name top_ns) file_names: (string * real) list list;
    val all_pairs                       = coincidence_rates_for_each_file @ [overall_coincidence_rates]: (string * real) list list;
  in
    all_pairs |> Matrix.matrix_to_row_of_columns_matrix |> Matrix.transpose_rcmatrix |> the |> Matrix.row_of_columns_matrix_to_matrix
  end;
\<close>

ML\<open>(*result*)
fun file_name_to_proportion_of_rule (points:datapoints) (file_name:string) =
  let
    val datapoints_in_file                   = points_in_file file_name points;
    val datapoints_in_file_with_rule         = filter #rule datapoints_in_file: datapoints;
    val numb_of_datapoints_in_file           = length datapoints_in_file           |> Real.fromInt: real;
    val numb_of_datapoints_in_file_with_rule = length datapoints_in_file_with_rule |> Real.fromInt: real;
  in
    (numb_of_datapoints_in_file_with_rule / numb_of_datapoints_in_file)
  end;

fun points_to_proportions_of_rules (points:datapoints) =
let
  val file_names = datapoints_to_all_file_names points: strings;
  val pairs      = map (fn file_name:string => (file_name, file_name_to_proportion_of_rule points file_name)) file_names: (string * real) list;
  val line       = print_one_line pairs;
in
  line
end;

fun file_name_to_proportion_of_arbitrary (points:datapoints) (file_name:string) =
  let
    val datapoints_in_file                   = points_in_file file_name points;
    val datapoints_in_file_with_rule         = filter #arbitrary datapoints_in_file: datapoints;
    val numb_of_datapoints_in_file           = length datapoints_in_file           |> Real.fromInt: real;
    val numb_of_datapoints_in_file_with_rule = length datapoints_in_file_with_rule |> Real.fromInt: real;
  in
    (numb_of_datapoints_in_file_with_rule / numb_of_datapoints_in_file)
  end;

fun points_to_proportions_of_arbs (points:datapoints) =
let
  val file_names = datapoints_to_all_file_names points: strings;
  val pairs      = map (fn file_name:string => (file_name, file_name_to_proportion_of_arbitrary points file_name)) file_names: (string * real) list;
  val line       = print_one_line pairs;
in
  line
end;

val _ = tracing (points_to_proportions_of_rules lines);
val _ = tracing (points_to_proportions_of_arbs  lines);
\<close>

ML\<open> val tikz_for_coincidence_rates = get_coincidence_rate_for_file_for_top_n lines "~/Workplace/PSL/Smart_Induct/Evaluation/DFS.thy" 1;\<close>

ML\<open>(*result*)
fun from_pair_matrix_to_tikz_barplot (pairs) = pairs
|> map print_one_line
|> (fn addplots:strings => (String.concatWith ", " (datapoints_to_all_file_names lines) ^ "\n") :: addplots)
|> String.concat
|> tracing;

val coincidence_rates_for_files = 
   datapoints_to_coincidence_rate_pairs lines [1,3,5,8,10]
|> from_pair_matrix_to_tikz_barplot;

(*
\addplot coordinates {(Challenge, 75.0) (DFS, 50.0) (Goodstein, 28.8) (NN, 9.1) (PST, 100.0) (overall, 49.5)};
\addplot coordinates {(Challenge, 75.0) (DFS, 80.0) (Goodstein, 51.9) (NN, 9.1) (PST, 100.0) (overall, 63.3)};
\addplot coordinates {(Challenge, 75.0) (DFS, 80.0) (Goodstein, 69.2) (NN, 18.2) (PST, 100.0) (overall, 72.5)};
\addplot coordinates {(Challenge, 75.0) (DFS, 80.0) (Goodstein, 76.9) (NN, 63.6) (PST, 100.0) (overall, 80.7)};
\addplot coordinates {(Challenge, 75.0) (DFS, 80.0) (Goodstein, 80.8) (NN, 63.6) (PST, 100.0) (overall, 82.6)};
*)
\<close>

ML\<open>
fun datapoints_to_points_for_functional_induction (points:datapoints) = filter (#rule) points;
fun datapoints_to_points_with_generalisation (points:datapoints) = filter (#arbitrary) points;

type four_types =
  {w_rule_w_arb  : datapoints,
   w_rule_wo_arb : datapoints,
   wo_rule_w_arb : datapoints,
   wo_rule_wo_arb: datapoints}

fun datapoints_to_four_types (points:datapoints) =
let
  val w_rule         = filter     #rule      points;
  val w_rule_w_arb   = filter     #arbitrary w_rule;
  val w_rule_wo_arb  = filter_out #arbitrary w_rule;
  val wo_rule        = filter_out #rule      points;
  val wo_rule_w_arb  = filter     #arbitrary wo_rule;
  val wo_rule_wo_arb = filter_out #arbitrary wo_rule;
in
  {w_rule_w_arb   = w_rule_w_arb  : datapoints,
   w_rule_wo_arb  = w_rule_wo_arb : datapoints,
   wo_rule_w_arb  = wo_rule_w_arb : datapoints,
   wo_rule_wo_arb = wo_rule_wo_arb: datapoints}: four_types           
end;
\<close>

ML\<open> (*result*)
local
val four_types_of_points = datapoints_to_four_types lines;

fun tag_the_type_name (name:string) (numbs)  = map (fn numb => (name, numb)) numbs: (string * 'a) list;
val rates_for_w_rule_w_arb   = datapoints_to_coincidence_rates (#w_rule_w_arb   four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-w-arb";
val rates_for_w_rule_wo_arb  = datapoints_to_coincidence_rates (#w_rule_wo_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-wo-arb";
val rates_for_wo_rule_w_arb  = datapoints_to_coincidence_rates (#wo_rule_w_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-w-arb";
val rates_for_wo_rule_wo_arb = datapoints_to_coincidence_rates (#wo_rule_wo_arb four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-wo-arb";

val m = [
  rates_for_w_rule_w_arb  ,
  rates_for_wo_rule_w_arb ,
  rates_for_w_rule_wo_arb ,
  rates_for_wo_rule_wo_arb];

val transposed_m = m |> Matrix.matrix_to_row_of_columns_matrix |> Matrix.transpose_rcmatrix |> the |> Matrix.row_of_columns_matrix_to_matrix;
in
val _ = from_pair_matrix_to_tikz_barplot transposed_m
end
(*
\addplot coordinates {(w-rule-w-arb, 0.0) (wo-rule-w-arb, 14.3) (w-rule-wo-arb, 78.2) (wo-rule-wo-arb, 29.0)};
\addplot coordinates {(w-rule-w-arb, 11.1) (wo-rule-w-arb, 21.4) (w-rule-wo-arb, 83.6) (wo-rule-wo-arb, 61.3)};
\addplot coordinates {(w-rule-w-arb, 22.2) (wo-rule-w-arb, 28.6) (w-rule-wo-arb, 87.3) (wo-rule-wo-arb, 80.6)};
\addplot coordinates {(w-rule-w-arb, 33.3) (wo-rule-w-arb, 50.0) (w-rule-wo-arb, 90.9) (wo-rule-wo-arb, 96.8)};
*)
\<close>

ML\<open> (*result for Goodstein*)
local
(*val four_types_of_points = datapoints_to_four_types (filter (fn point => #file_name point = "Goodstein") lines);*)
val four_types_of_points = datapoints_to_four_types lines;

fun tag_the_type_name (name:string) (numbs)  = map (fn numb => (name, numb)) numbs: (string * 'a) list;
val rates_for_w_rule_w_arb   = datapoints_to_coincidence_rates (#w_rule_w_arb   four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-w-arb";
val rates_for_w_rule_wo_arb  = datapoints_to_coincidence_rates (#w_rule_wo_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-wo-arb";
val rates_for_wo_rule_w_arb  = datapoints_to_coincidence_rates (#wo_rule_w_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-w-arb";
val rates_for_wo_rule_wo_arb = datapoints_to_coincidence_rates (#wo_rule_wo_arb four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-wo-arb";

val rates_for_w_rule  = datapoints_to_coincidence_rates (filter     (#rule) lines) [1,3,5,10] |> tag_the_type_name "w-rule";
val rates_for_wo_rule = datapoints_to_coincidence_rates (filter_out (#rule) lines) [1,3,5,10] |> tag_the_type_name "wo-rule";

val m = [
  rates_for_w_rule_w_arb  ,
  rates_for_wo_rule_w_arb ,
  rates_for_w_rule_wo_arb ,
  rates_for_wo_rule_wo_arb,
  rates_for_w_rule,
  rates_for_wo_rule
];

val transposed_m = m |> Matrix.matrix_to_row_of_columns_matrix |> Matrix.transpose_rcmatrix |> the |> Matrix.row_of_columns_matrix_to_matrix;
in
val _ = from_pair_matrix_to_tikz_barplot transposed_m
end;
(*
\addplot coordinates {(w-rule-w-arb, 0.0) (wo-rule-w-arb, 14.3) (w-rule-wo-arb, 78.2) (wo-rule-wo-arb, 29.0) (w-rule, 67.2) (wo-rule, 24.4)};
\addplot coordinates {(w-rule-w-arb, 11.1) (wo-rule-w-arb, 21.4) (w-rule-wo-arb, 83.6) (wo-rule-wo-arb, 61.3) (w-rule, 73.4) (wo-rule, 48.9)};
\addplot coordinates {(w-rule-w-arb, 22.2) (wo-rule-w-arb, 28.6) (w-rule-wo-arb, 87.3) (wo-rule-wo-arb, 80.6) (w-rule, 78.1) (wo-rule, 64.4)};
\addplot coordinates {(w-rule-w-arb, 33.3) (wo-rule-w-arb, 50.0) (w-rule-wo-arb, 90.9) (wo-rule-wo-arb, 96.8) (w-rule, 82.8) (wo-rule, 82.2)};
*)
\<close>

ML\<open> (*result for non-Goodstein*)
local
val four_types_of_points = datapoints_to_four_types (filter_out (fn point => #file_name point = "Goodstein") lines);

fun tag_the_type_name (name:string) (numbs)  = map (fn numb => (name, numb)) numbs: (string * 'a) list;
val rates_for_w_rule_w_arb   = datapoints_to_coincidence_rates (#w_rule_w_arb   four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-w-arb";
val rates_for_w_rule_wo_arb  = datapoints_to_coincidence_rates (#w_rule_wo_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "w-rule-wo-arb";
val rates_for_wo_rule_w_arb  = datapoints_to_coincidence_rates (#wo_rule_w_arb  four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-w-arb";
val rates_for_wo_rule_wo_arb = datapoints_to_coincidence_rates (#wo_rule_wo_arb four_types_of_points) [1,3,5,10] |> tag_the_type_name "wo-rule-wo-arb";

val m = [
  rates_for_w_rule_w_arb  ,
  rates_for_w_rule_wo_arb ,
  rates_for_wo_rule_w_arb ,
  rates_for_wo_rule_wo_arb
];

val transposed_m = m |> Matrix.matrix_to_row_of_columns_matrix |> Matrix.transpose_rcmatrix |> the |> Matrix.row_of_columns_matrix_to_matrix;
in
val _ = from_pair_matrix_to_tikz_barplot transposed_m
end
\<close>

ML\<open>(*result*)
fun datapoints_to_proportion (points:datapoints) =
let
  val numb_of_all_points     = length points                       |> Real.fromInt;
  val four_types             = datapoints_to_four_types points;
  val numb_of_w_rule_w_arb   = length (#w_rule_w_arb   four_types) |> Real.fromInt: real;
  val numb_of_w_rule_wo_arb  = length (#w_rule_wo_arb  four_types) |> Real.fromInt: real;
  val numb_of_wo_rule_w_arb  = length (#wo_rule_w_arb  four_types) |> Real.fromInt: real;
  val numb_of_wo_rule_wo_arb = length (#wo_rule_wo_arb four_types) |> Real.fromInt: real;
  val proportion_of_w_rule_w_arb   = ((numb_of_w_rule_w_arb   / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val proportion_of_w_rule_wo_arb  = ((numb_of_w_rule_wo_arb  / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val proportion_of_wo_rule_w_arb  = ((numb_of_wo_rule_w_arb  / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val proportion_of_wo_rule_wo_arb = ((numb_of_wo_rule_wo_arb / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
in
 (numb_of_w_rule_w_arb,
  numb_of_w_rule_wo_arb,
  numb_of_wo_rule_w_arb,
  numb_of_wo_rule_wo_arb,
  proportion_of_w_rule_w_arb ,
  proportion_of_w_rule_wo_arb,
  proportion_of_wo_rule_w_arb,
  proportion_of_wo_rule_wo_arb)
end;

datapoints_to_proportion lines;                                      
\<close>
(*
DFS.thy, Challenge1A.thy, Goodstein_Lambda.thy, PST_RBT.thy, Nearest_Neighbors.thy
\addplot coordinates {(DFS, 50) (Challenge1A, 75) (Goodstein, 27) (PST, 100) (NN, 9) (overall, 49)};
\addplot coordinates {(DFS, 80) (Challenge1A, 75) (Goodstein, 48) (PST, 100) (NN, 9) (overall, 61)};
\addplot coordinates {(DFS, 80) (Challenge1A, 75) (Goodstein, 65) (PST, 100) (NN, 18) (overall, 71)};
\addplot coordinates {(DFS, 80) (Challenge1A, 75) (Goodstein, 75) (PST, 100) (NN, 64) (overall, 80)};
\addplot coordinates {(DFS, 80) (Challenge1A, 75) (Goodstein, 79) (PST, 100) (NN, 64) (overall, 82)};
 
*)

ML\<open>(*result*)
fun datapoints_to_proportion_of_induct_on_subterm (points:datapoints) =
let
  val numb_of_all_points          = length points |> Real.fromInt            : real;
  val induct_on_subterms          = filter     #induct_on_subterm points     : datapoints;
  val induct_on_variables         = filter_out #induct_on_subterm points     : datapoints;
  val numb_of_induct_on_subterms  = length induct_on_subterms  |> Real.fromInt: real;
  val numb_of_induct_on_variables = length induct_on_variables |> Real.fromInt: real;
  val proportion_of_on_subterms   = ((numb_of_induct_on_subterms   / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val proportion_of_on_variables  = ((numb_of_induct_on_variables  / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val induct_on_hand_writte_rule  = filter     #hand_writte_rule points              : datapoints;
  val numb_of_handwrittens        = length induct_on_hand_writte_rule |> Real.fromInt: real;
  val both_handwritten_rule_and_subterm = filter #induct_on_subterm induct_on_hand_writte_rule;
  val numb_of_both_handwritten_rule_and_subterm = length both_handwritten_rule_and_subterm |> Real.fromInt: real;
  val numb_of_only_handwritten_rule_not_subterm = numb_of_handwrittens       - numb_of_both_handwritten_rule_and_subterm: real;
  val numb_of_only_subterm_not_handwritten_rule = numb_of_induct_on_subterms - numb_of_both_handwritten_rule_and_subterm: real;
  val numb_of_those_in_scope = numb_of_all_points - numb_of_both_handwritten_rule_and_subterm - numb_of_only_handwritten_rule_not_subterm - numb_of_only_subterm_not_handwritten_rule;
  val prop_of_both_handwritten_rule_and_subterm = ((numb_of_both_handwritten_rule_and_subterm / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt) / 10.0: real;
  val prop_of_only_handwritten_rule_not_subterm = ((numb_of_only_handwritten_rule_not_subterm / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt) / 10.0: real;
  val prop_of_only_subterm_not_handwritten_rule = ((numb_of_only_subterm_not_handwritten_rule / numb_of_all_points * 1000.0) |> Real.round |> Real.fromInt) / 10.0: real;
  val prop_of_those_in_scope = 100.0 - prop_of_both_handwritten_rule_and_subterm - prop_of_only_handwritten_rule_not_subterm - prop_of_only_subterm_not_handwritten_rule;
in
 ((prop_of_both_handwritten_rule_and_subterm,  numb_of_both_handwritten_rule_and_subterm),
  (prop_of_only_handwritten_rule_not_subterm,  numb_of_only_handwritten_rule_not_subterm),
  (prop_of_only_subterm_not_handwritten_rule,  numb_of_only_subterm_not_handwritten_rule),
  (prop_of_those_in_scope                   ,  numb_of_those_in_scope                   ))
end;

datapoints_to_proportion_of_induct_on_subterm lines;                                      
\<close>

ML\<open>(*result*)
fun datapoints_to_proportion_of_hand_writte_rule (points:datapoints) =
let
  val induct_w_rules              = filter #rule points                              : datapoints;
  val numb_of_induct_w_rules      = length induct_w_rules |> Real.fromInt            : real;
  val induct_on_hand_writte_rule  = filter     #hand_writte_rule induct_w_rules      : datapoints;
  val induct_on_generated_rule    = filter_out #hand_writte_rule induct_w_rules      : datapoints;
  val numb_of_handwrittens        = length induct_on_hand_writte_rule |> Real.fromInt: real;
  val numb_of_generateds          = length induct_on_generated_rule   |> Real.fromInt: real;
  val proportion_of_handwrittens  = ((numb_of_handwrittens   / numb_of_induct_w_rules * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
  val proportion_of_generateds    = ((numb_of_generateds     / numb_of_induct_w_rules * 1000.0) |> Real.round |> Real.fromInt)/ 10.0: real;
in
 (numb_of_induct_w_rules,
  numb_of_handwrittens,                                           
  numb_of_generateds,
  proportion_of_handwrittens ,
  proportion_of_generateds)
end;

datapoints_to_proportion_of_hand_writte_rule lines;                                      
\<close>

ML\<open>(*result*)
fun datapoints_to_handwritten_and_subterm (points:datapoints) =
  points |> filter #hand_writte_rule |> filter #induct_on_subterm;

datapoints_to_handwritten_and_subterm lines |> length;
\<close>

declare [[ML_print_depth=200]]

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
fun datapoints_with_indices_sorted_wrt_numb_of_candidates (points:datapoints) =
  let
    val sorted_wrt_step_2b             = sort (fn (point1, point2) => Int.compare (#numb_of_candidates_after_step_2b point1, #numb_of_candidates_after_step_2b point2)) points            : datapoints;
    val sorted_wrt_step_2b_then_step_1 = sort (fn (point1, point2) => Int.compare (#numb_of_candidates_after_step_1  point1,  #numb_of_candidates_after_step_1 point2)) sorted_wrt_step_2b: datapoints;
    val indexed                        = Utils.index sorted_wrt_step_2b_then_step_1;
  in
    indexed: (int * datapoint) list
  end;
\<close>

ML\<open>(*result*)
fun print_pairs_int pairs = map (fn (index, time) => "(" ^ Int.toString index ^ ", " ^ Int.toString time ^ ")") pairs |> String.concatWith " ";

fun five_types_of_pairs (points:datapoints) =
  let
    val indexed_sorted_points         = datapoints_with_indices_sorted_wrt_numb_of_candidates points: (int * datapoint) list;
    val indexed_sorted_points_success = filter (is_some o #rank o snd) indexed_sorted_points: (int * datapoint) list;
    val indexed_sorted_points_failure = filter (is_none o #rank o snd) indexed_sorted_points: (int * datapoint) list;
    
    val after_step1_success  = map (fn pair => apsnd #numb_of_candidates_after_step_1  pair) indexed_sorted_points_success: (int * int) list;
    val after_step2b_success = map (fn pair => apsnd #numb_of_candidates_after_step_2b pair) indexed_sorted_points_success: (int * int) list;
    val after_step1_failure  = map (fn pair => apsnd #numb_of_candidates_after_step_1  pair) indexed_sorted_points_failure: (int * int) list;
    val after_step2b_failure = map (fn pair => apsnd #numb_of_candidates_after_step_2b pair) indexed_sorted_points_failure: (int * int) list;
    val rank_success         = map (fn pair => apsnd (the o #rank)                     pair) indexed_sorted_points_success: (int * int) list;
    val _ = (tracing o print_pairs_int) after_step1_success;
    val _ = (tracing o print_pairs_int) after_step2b_success;
    val _ = (tracing o print_pairs_int) after_step1_failure;
    val _ = (tracing o print_pairs_int) after_step2b_failure;
    val _ = (tracing o print_pairs_int) rank_success;
  in
    ()
  end;

five_types_of_pairs lines;
\<close>

ML\<open>
val numb_of_Challenge = 12.0;
val numb_of_DFS       = 10.0;
val numb_of_Goodstein = 52.0;
val numb_of_NN        = 11.0;
val numb_of_PST       = 24.0;
val total_numb        = length lines |> Real.fromInt;


val proportion_of_Challenge = ((Real.fromInt o Real.round) ((numb_of_Challenge / total_numb) * 1000.0)) / 10.0;
val proportion_of_DFS       = ((Real.fromInt o Real.round) ((numb_of_DFS       / total_numb) * 1000.0)) / 10.0;
val proportion_of_Goodstein = ((Real.fromInt o Real.round) ((numb_of_Goodstein / total_numb) * 1000.0)) / 10.0;
val proportion_of_NN        = ((Real.fromInt o Real.round) ((numb_of_NN        / total_numb) * 1000.0)) / 10.0;
val proportion_of_PST       = ((Real.fromInt o Real.round) ((numb_of_PST       / total_numb) * 1000.0)) / 10.0;
val proportion_of_Challenge = ((Real.fromInt o Real.round) ((numb_of_Challenge / total_numb) * 1000.0)) / 10.0;
val s = 24.0/109.0
\<close>

end