theory Format_Result_Semantic_Induct
  imports "PSL.PSL"
begin

ML_file  "../../../LiFtEr/Matrix_Sig.ML"
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
    val datapoints_in_file = points_in_file file_name points;
  in
    get_coincidence_rate_top_n datapoints_in_file top_n: real
  end;

fun datapoints_to_all_file_names (points:datapoints) = map #file_name points |> distinct (op =);

fun datapoints_to_coincidence_rates (points:datapoints) (top_ns:ints) = map (get_coincidence_rate_top_n points) top_ns: real list;

fun attach_file_name_to_coincidence_rates (file_name:string) (rates) = map (fn rate => (file_name, rate)) rates;
\<close>

declare [[ML_print_depth=2000]]

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
    fun mk_string (fname, reals)        = String.concatWith " & " (fname  :: "new" :: (Int.toString o length) (points_in_file_with_overall fname points):: (map (fn real => real_to_percentage_with_precision_str real) reals)) ^ " \\"^"\\": string;
    val result = map (mk_string) (coincidence_rates_for_each_file @ [overall_coincidence_rates])
  in
    result
  end;

val semantic_induct_result = datapoints_to_coincidence_rate_pairs lines [1,3,5,10] [200,500,1000,2000,5000];
(*overall & 1095 & 38.2 & 59.3 & 64.5 & 72.7 & 8.8 & 24.7 & 47.8 & 69.8 & 86.8*)
\<close>

end