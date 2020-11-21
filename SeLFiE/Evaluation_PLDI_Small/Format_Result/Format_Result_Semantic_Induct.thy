theory Format_Result_Semantic_Induct
  imports "PSL.PSL"
begin

ML_file  "../../../LiFtEr/Matrix_Sig.ML"
ML_file  "../../../LiFtEr/Matrix_Struct.ML"

declare [[ML_print_depth=2000]]

ML\<open>
val path = File.platform_path (Resources.master_directory @{theory}) ^ "/Database.csv";
val get_lines = split_lines o TextIO.inputAll o TextIO.openIn;
\<close>

ML\<open>
type datapoint =
 {file_name             :string,
  line_number           : int,
  with_selfie_success   : bool,
  without_selfie_success: bool,
  with_selfie_time      : int,
  without_selfie_time   : int
  };

type datapoints = datapoint list;

fun int_to_bool 1 = true
  | int_to_bool 0 = false
  | int_to_bool _ = error "int_to_bool";

fun read_one_line (line:string) =
  let
    val (file_name::numbers_as_strings) = String.tokens (fn c=> str c = ";") line: string list;
    val line_number                     = nth numbers_as_strings 0 |> Int.fromString |> the;
    val with_selfie_success             = nth numbers_as_strings 1 |> Int.fromString |> Option.map int_to_bool |> the;
    val without_selfie_success          = nth numbers_as_strings 2 |> Int.fromString |> Option.map int_to_bool |> the;
    val with_selfie_time                = nth numbers_as_strings 3 |> Int.fromString |> the;
    val without_selfie_time             = nth numbers_as_strings 4 |> Int.fromString |> the;
    val result =
      {file_name              = file_name             :string,
       line_number            = line_number           : int,
       with_selfie_success    = with_selfie_success   : bool,
       without_selfie_success = without_selfie_success: bool,
       with_selfie_time       = with_selfie_time      : int,
       without_selfie_time    = without_selfie_time   : int
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
fun real_to_percentage_with_precision (real:real)     = (1000.0 * real |> Real.round |> Real.fromInt) / 10.0   : real;
fun real_to_percentage_with_precision_str (real:real) = real_to_percentage_with_precision real |> Real.toString: string;
fun real_to_percentage     (real:real)                = 100.0 * real |> Real.round                             : int;
fun real_to_percentage_str (real:real)                = real_to_percentage real |> Int.toString                : string;
\<close>

ML\<open>
fun with_selfie_success_case_for_timeout    (data:datapoints) (timeout:int) =
  let
    val numb_of_cases = data |> filter (#with_selfie_success   ) |> filter (fn dpoint => #with_selfie_time    dpoint < timeout) |> length |> Real.fromInt;
    val percentage    = real_to_percentage_with_precision (numb_of_cases / (Real.fromInt (length data)))
  in
    percentage
  end;

fun without_selfie_success_case_for_timeout (data:datapoints) (timeout:int) =
  let
    val numb_of_cases = data |> filter (#without_selfie_success) |> filter (fn dpoint => #without_selfie_time dpoint < timeout) |> length |> Real.fromInt;
    val percentage    = real_to_percentage_with_precision (numb_of_cases / (Real.fromInt (length data)))
  in
    percentage
  end;
\<close>

ML\<open>
fun datapoints_n_timeouts_to_success_rates (_:datapoints)     []                 = []
  | datapoints_n_timeouts_to_success_rates (data:datapoints) (timeout::timeouts) =
    (with_selfie_success_case_for_timeout    data timeout, without_selfie_success_case_for_timeout data timeout)
    :: datapoints_n_timeouts_to_success_rates data timeouts;
\<close>

ML\<open>
val results1 = datapoints_n_timeouts_to_success_rates lines [300,1000,3000,10000,30000]
\<close>

ML\<open>
fun datapoints_to_sucessful_datapoints_speedups (data:datapoints) = data
 |> filter (#without_selfie_success)
 |> filter (fn dpoint => #without_selfie_time dpoint < 30000) 
 |> filter (#with_selfie_success)
 |> filter (fn dpoint => #with_selfie_time dpoint < 30000)
 |> map (fn point => (Real.fromInt (#without_selfie_time point) / Real.fromInt (#with_selfie_time point))): real list;

val speedups = datapoints_to_sucessful_datapoints_speedups lines |> sort Real.compare;
val numb_of_successful_pairs = length speedups;
val sdfa= nth  [1,2] 0;
val half = 126.0 / 2.0;
val median_value_for_speedup = 0.5 * (nth speedups 62 + nth speedups 63);

val distribution_of_speedups =
let
  fun numb_of_speedups_below (limit:real) = filter (fn speedup => speedup < limit         ) speedups |> length |> Real.fromInt;
  fun numb_of_speedups_above (limit:real) = filter (fn speedup => Real.<= (limit, speedup)) speedups |> length |> Real.fromInt;
  val distribution =
  [numb_of_speedups_below 1.0,
   numb_of_speedups_below 5.0  - numb_of_speedups_below 1.0,
   numb_of_speedups_below 10.0 - numb_of_speedups_below 5.0,
   numb_of_speedups_below 15.0 - numb_of_speedups_below 10.0,
   numb_of_speedups_below 20.0 - numb_of_speedups_below 15.0,
                                 numb_of_speedups_above 20.0
   ]
in
  map (fn numb_of_cases => (numb_of_cases, real_to_percentage_with_precision (numb_of_cases / (Real.fromInt numb_of_successful_pairs)))) distribution
end;

fun datapoints_to_numb_of_sucessful_datapoints_only_by_psl_with_selfie (data:datapoints) = data
 |> filter_out (fn dpoint => #without_selfie_success dpoint andalso #without_selfie_time dpoint < 30000) 
 |> filter (#with_selfie_success)
 |> filter (fn dpoint => #with_selfie_time dpoint < 30000)
 |> length

fun datapoints_to_numb_of_sucessful_datapoints_only_by_psl_without_selfie (data:datapoints) = data
 |> filter (#without_selfie_success)
 |> filter (fn dpoint => #without_selfie_time dpoint < 30000) 
 |> filter_out (fn dpoint => #with_selfie_success dpoint andalso #with_selfie_time dpoint < 30000)
 |> length

fun datapoints_to_numb_of_sucessful_datapoints_by_psl_with_or_without_selfie (data:datapoints) = data
 |> filter (fn dpoint => (#with_selfie_success    dpoint andalso #with_selfie_time    dpoint < 30000) orelse
                         (#without_selfie_success dpoint andalso #without_selfie_time dpoint < 30000))
 |> length
\<close>

ML\<open>(*results*)
datapoints_n_timeouts_to_success_rates lines [300,1000,3000,10000,30000];
median_value_for_speedup;
distribution_of_speedups;
datapoints_to_numb_of_sucessful_datapoints_only_by_psl_with_selfie lines;
datapoints_to_numb_of_sucessful_datapoints_only_by_psl_without_selfie lines;
datapoints_to_numb_of_sucessful_datapoints_by_psl_with_or_without_selfie lines;
length lines;
\<close>
(*
ML\<open>
fun with_selfie_success_case_for_timeout    (data:datapoints) (timeout:int) =
  let
    val numb_of_cases = data |> filter (#with_selfie_success   ) |> filter (fn dpoint => #with_selfie_time    dpoint < timeout) |> length |> Real.fromInt;
    val percentage    =  (numb_of_cases / (Real.fromInt (length data)))
  in
    percentage
  end;

fun without_selfie_success_case_for_timeout (data:datapoints) (timeout:int) =
  let
    val numb_of_cases = data |> filter (#without_selfie_success) |> filter (fn dpoint => #without_selfie_time dpoint < timeout) |> length |> Real.fromInt;
    val percentage    =  (numb_of_cases / (Real.fromInt (length data)))
  in
    percentage
  end;
\<close>

ML\<open>
fun datapoints_n_timeouts_to_success_rates (_:datapoints)     []                 = []
  | datapoints_n_timeouts_to_success_rates (data:datapoints) (timeout::timeouts) =
    (with_selfie_success_case_for_timeout    data timeout, without_selfie_success_case_for_timeout data timeout)
    :: datapoints_n_timeouts_to_success_rates data timeouts;
\<close>

ML\<open>
val results1 = datapoints_n_timeouts_to_success_rates lines [300,1000,3000,10000,30000];
100.0 * ((0.2564841499 - 0.01729106628)/ 0.01729106628)
\<close>
*)
end