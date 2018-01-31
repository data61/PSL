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
val path_to_all_meth_names = path_to_PaMpeR ^ "/method_names": string;
val path_to_Database = path_to_PaMpeR ^ "/Build_Database/Database":string;
val eval_file        = path_to_PaMpeR ^ "/Evaluation/evaluation.txt";
fun two_dig (r:real) =  ((r * 100.0) |> Real.round |> Real.fromInt);
val datasize_real    = proc ("wc " ^ path_to_Database ^ " | awk '{print $1;}'")
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

fun postprocess_all_meths (mname::mnames:string list) (n:int) (lines:string list)=
  let
    val maybe_numbs = postprocess_one_meth mname n n (SOME 0.0) []
      |> map (Option.map two_dig) :real option list;
    val numbs = if forall is_some maybe_numbs
      then map the maybe_numbs
      else (tracing ("postprocess_all_meths partially failed. Some Nones were detected for " ^ mname);[]):real list;
    val numbs_strs = map Real.toString numbs: string list;
    val total_occr = proc ("grep '^" ^ mname ^ "\\s' " ^ path_to_Database ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the |> Int.toString;
    val total_real = proc ("grep '^" ^ mname ^ "\\s' " ^ path_to_Database ^ " | wc | awk '{print $1;}'") |> #out |> Int.fromString |> the |> Real.fromInt;
    val freqency   = two_dig (total_real / datasize_real) |> Real.toString: string;
    val line = mname ^ " " ^ total_occr ^ " " ^ freqency ^ " " ^ (space_implode " " numbs_strs);
    val _ = if null numbs then () else
      (proc ("echo " ^ line ^ " >> " ^ path ^ "/eval_result.txt"); ());
  in
    postprocess_all_meths mnames n (lines @ [line])
  end
 | postprocess_all_meths ([]:string list) (_:int) (lines) = lines;

in
postprocess_all_meths all_method_names 15 []
end;
*}

ML{*
postprocess ();
*}

end