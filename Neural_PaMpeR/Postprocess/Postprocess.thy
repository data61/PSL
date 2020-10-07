(* Title:  Preprocess.thy
   Author Yutaka Nagashima, CIIRC, CTU

   This file assumes that you have build a Database in PSL/PaMpeR/Build_Database.
   And PSL/PaMpeR/Build_Database/Database is used for the training.
*)
theory Postprocess
imports "Pure"
begin

ML_file "../../src/Utils.ML"

ML{*
fun postprocess _ =

let

val proc             = Bash.process;
val path             = Resources.master_directory @{theory} |> File.platform_path : string;
val path_to_PaMpeR   = unsuffix "/Postprocess" path;
val path_to_all_meth_names = path_to_PaMpeR ^ "/Preprocess/method_names": string;
val path_to_all_meth_namees_standard = path_to_PaMpeR ^ "/Preprocess/method_names_in_standard_library": string;
val path_to_Database = path_to_PaMpeR ^ "/Build_Database/Database":string;
val eval_file        = path_to_PaMpeR ^ "/Evaluate_ASE/evaluation_success.txt";
fun thr_dig (r:real) = ((r * 1000.0) |> Real.round |> Real.fromInt |> (fn x => x / 10.0)):real;
fun two_dig (r:real) = ((r * 1000.0) |> Real.round |> Real.fromInt |> (fn x => x / 10.0) |> Real.round):int;
val datasize_real    = proc ("wc " ^ path_to_Database ^ " | awk '{print $1;}'")
                     |> #out |> Int.fromString |> the |> Real.fromInt;
val testsize_real    = proc ("wc " ^ eval_file ^ " | awk '{print $1;}'")
                     |> #out |> Int.fromString |> the |> Real.fromInt;

(*TODO: remove code duplication with Preprocess.thy, PaMpeR_Interface.thy and Postprocess.thy.*)
val all_method_names =
  let
    val bash_script = "while read line \n do echo $line | awk '{print $1;}' \n done < '" ^ path_to_all_meth_names ^ "'" : string;
    val bash_input  = Bash.process bash_script |> #out : string;
    val dist_meth_names = bash_input |> String.tokens (fn c => c = #"\n") |> distinct  (op =);
  in
    dist_meth_names : string list
  end;

val method_names_standard =
  let
    val bash_script = "while read line \n do echo $line | awk '{print $1;}' \n done < '" ^ path_to_all_meth_namees_standard ^ "'" : string;
    val bash_input  = Bash.process bash_script |> #out : string;
    val dist_meth_names = bash_input |> String.tokens (fn c => c = #"\n") |> distinct  (op =);
  in
    dist_meth_names : string list
  end;

val method_names_user_defined = subtract (op =) method_names_standard all_method_names;

fun postprocess_one_meth (_    :string) (0:int) (_:int) (_              )  (numbs:real option list) = numbs
 |  postprocess_one_meth (mname:string) (n:int) (t:int) (accm:real option) (numbs:real option list) =
  let
    val rank       = t - (n - 1);
    val total_occr = proc ("grep '^" ^ mname ^ "\\s' " ^ eval_file ^ " | wc | awk '{print $1;}'") |> #out |> Real.fromString;
    val numb  = proc ("grep '^" ^ mname ^ " " ^ Int.toString rank ^ " out' " ^ eval_file ^ " | wc | awk '{print $1;}'") |> #out |> Real.fromString;
    fun maybe_div (l:real option, r:real option) =
      if is_some l andalso is_some r
      then (if Real.isFinite (the l / the r)
        then SOME (the l / the r)
        else NONE)
      else NONE;
    val perc = maybe_div (numb, total_occr);
    fun maybe_plus (l:real option, r:real option) =
      if is_some l andalso is_some r then SOME (the l + the r) else NONE;
    val accm' = maybe_plus (accm, perc);
  in
    postprocess_one_meth mname (n - 1) t accm' (numbs@[accm']): real option list
  end;

fun postprocess_one_meth' (n:int) (mname:string) =
  let
    val maybe_numbs = postprocess_one_meth mname n n (SOME 0.0) []
      |> map (Option.map two_dig) :int option list;
    val numbs = if forall is_some maybe_numbs
      then map the maybe_numbs
      else (tracing ("postprocess_all_meths partially failed. Some Nones were detected for " ^ mname);[]):int list;
    val numbs_strs = map Int.toString numbs: string list;
    val occur_in_train = if mname = "-"
      then proc ("grep ' - ' " ^ path_to_Database ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the
      else proc ("grep '\\b" ^ mname ^ "\\b' " ^ path_to_Database ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the;
    val occur_in_train_str = Int.toString occur_in_train;
    val occur_in_test_str  = proc ("grep '^" ^ mname ^ "\\s' " ^ eval_file ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the |> Int.toString;
    val occur_in_train_real = Real.fromInt occur_in_train;
    val occur_in_test_real = proc ("grep '^" ^ mname ^ "\\s' " ^ eval_file ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the |> Real.fromInt;
    val frequency_train = thr_dig (occur_in_train_real / datasize_real) |> Real.toString: string;
    val frequency_test = thr_dig (occur_in_test_real /  testsize_real) |> Real.toString: string;
    val line_latex = "'\\verb|" ^ mname ^ "| & " ^ occur_in_train_str ^ " & " ^ frequency_train ^ " & " ^ occur_in_test_str ^ " & " ^ frequency_test ^ " & " ^
            (space_implode " & " numbs_strs) ^ "\\" ^ "\\" ^ "'";
    val line_raw = "'[(*" ^ mname ^ "*) " ^ (space_implode "," numbs_strs) ^ "]'";
  in
    (if null numbs then ("", "","","","","") else (line_latex, line_raw, frequency_train, frequency_test, occur_in_train_str, occur_in_test_str))
  end;

fun postprocess_all_meth n mnames = Par_List.map (postprocess_one_meth' n) mnames: (string * string * string * string * string * string) list;

fun print_one_result (dest:string) (line:string) = proc ("echo " ^ line ^ " >> " ^ path ^ dest);

val among_top_nth = 15:int;

in

 postprocess_all_meth among_top_nth method_names_standard |> map (fn (latex, raw, fq_train, fq_test,occ_train,occ_test) => (
   print_one_result "/eval_result_in_standard_latex.txt" latex;
   print_one_result "/eval_result_in_standard_raw.txt" raw;
   print_one_result "/eval_result_in_standard_frequencey_train.txt" fq_train;
   print_one_result "/eval_result_in_standard_frequencey_test.txt" fq_test;
   print_one_result "/eval_result_in_standard_occ_train.txt" occ_train;
   print_one_result "/eval_result_in_standard_occ_test.txt" occ_test
  ));

 postprocess_all_meth among_top_nth method_names_user_defined |> map (fn (latex, raw, fq_train, fq_test,occ_train,occ_test) => (
   print_one_result "/eval_result_user_defined_latex.txt" latex;
   print_one_result "/eval_result_user_defined_raw.txt" raw;
   print_one_result "/eval_result_user_defined_frequencey_train.txt" fq_train;
   print_one_result "/eval_result_user_defined_frequencey_test.txt" fq_test;
   print_one_result "/eval_result_user_defined_occ_train.txt" occ_train;
   print_one_result "/eval_result_user_defined_occ_test.txt" occ_test
  ));

 postprocess_all_meth among_top_nth all_method_names |> map (fn (latex, raw, fq_train, fq_test,occ_train,occ_test) => (
   print_one_result "/eval_result_all_methods_latex.txt" latex;
   print_one_result "/eval_result_all_methods_raw.txt" raw;
   print_one_result "/eval_result_all_methods_raw_frequencey_train.txt" fq_train;
   print_one_result "/eval_result_all_methods_raw_frequencey_test.txt" fq_test;
   print_one_result "/eval_result_all_methods_occ_train.txt" occ_train;
   print_one_result "/eval_result_all_methods_occ_test.txt" occ_test
  ))

end;
*}

ML{*
postprocess ();
*}

(* Consider using sort -k3q -nr eval_result.txt *)

end