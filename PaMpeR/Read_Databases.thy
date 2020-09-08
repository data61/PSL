theory Read_Databases
imports Pure
begin

ML_file "../SeLFiE/Definition_Pattern.ML"
ML_file "../SeLFiE/Util.ML" (*TODO, FIXME: Utils.ML has test cases that involve constants and types defined in Main, but not in Pure*)

ML\<open> signature DATABASE =
sig
  type used          = bool;
  type feature_name  = int;
  type feature_value = bool;
  type meth_name     = string;
  type one_line      = used * (feature_name * feature_value) list;
  type database      = one_line list;
  (*get_Database_names has to be called only *after* generating pre-processed databases.*)
  val get_meth_names  : unit -> meth_name list;
  val parse_database  : meth_name -> database;
  val parse_databases : unit -> database list;
end;
\<close>

ML\<open> structure Database:DATABASE =
struct

type used          = bool;
type feature_name  = int;
type feature_value = bool;
type meth_name     = string;
type one_line      = used * (feature_name * feature_value) list;
type database      = one_line list;
val  pamper_path   = Resources.master_directory @{theory} |> File.platform_path;

fun get_meth_names () =
  let
    val new_line = "\n" |> String.toCString |> Char.fromCString |> the;
    val double_quote:string = str (#"\"");
    val bash_script : string =
     ("for f in " ^ pamper_path ^ "/Databases/* \n" ^
      "do" ^
      "  bname=$( basename " ^ double_quote ^ "$f" ^ double_quote ^")\n" ^
      "  echo $bname\n" ^
      "done");
  in
    Isabelle_System.bash_output bash_script
    |> fst
    |> String.tokens (fn c => new_line = c)
  end;

fun parse_database (meth_name:string) =
  let
    fun read_one_line (line:string) =
      let
        fun get_raw_line (line:string) = line
        |> String.tokens (fn c => str c = ",")
        |> (map (the o Int.fromString));
        fun is_used (line:int list) = if hd line = 0 then false else true;
        fun int_to_bool (0:int) = false
          | int_to_bool (1:int) = true
          | int_to_bool _       = error "int_to_bool failed.";
        fun get_feature_vector (line:int list) = tl line
          |> Utils.index
          |> map (apsnd int_to_bool);
        val raw_line = get_raw_line line;
        val one_line = (is_used raw_line, get_feature_vector raw_line);
      in
        one_line : one_line
      end;
    val read_lines    = split_lines o TextIO.inputAll o TextIO.openIn : string -> string list;
    val database_path = pamper_path ^ "/Databases/" ^ meth_name : string;
    fun parse (lines:string list) = map (try read_one_line) lines |> map the_list |> flat: one_line list;
    val result        = database_path |> read_lines |> parse : one_line list;
  in
    result
  end;

fun parse_databases () = get_meth_names () |> map parse_database;

end
\<close>

end