(*  Title:      MergeDatabase.thy
    Author:     Yutaka Nagashima CTU, CVUT, CIIRC / University of Innsbruck

    Depending on the machine's capability, producing Database using PSL/PaMpeR/Build_Database
    can be hard: applying more than 100 assertions to numerous proof obligations in large proof
    corpora can lead to unexpected problems, such as the lack of available memory space.
    This is particularly serious when one tries to extract Database using parallelism.
    Our approach is to apply a small number of assertions for each Database extraction and 
    merge the resulting databases together after applying assertions.

    This file, MergeDatabase.thy, helps you merge fragmented databases into one.
    To use MergeDatabase.thy properly, you have to add the file names of partial databases in 
    "file_names" manually in the order of assertions.

    Warning! If you use multiple machines for database extraction. You might end up having different
    location identifiers for the same location, because these location identifiers include not only
    the line numbers and theory names but also the path to the theory file.
*)
theory MergeDatabase
imports Pure
begin

ML\<open>
type data = ((string * string) * string) list;

(* Very naive merge algorithm. It assumes that both databases are already sorted. *)
fun merge_two' ([]:data) (_:data) (output:data) = output:data
 |  merge_two' ((x12, x3)::x_rest:data) (ys:data) (output:data)  =
  let
    fun eq_pair_str ((x,y):((string * string) * (string * string))) = eq_pair (op =) (op =) (x, y);
    val y3 = AList.lookup eq_pair_str ys x12;
    val new = if is_some y3 then [(x12, x3 ^ "," ^ the y3)] else [];
  in
    merge_two' x_rest ys (output @ new)
  end;

fun merge_two xs ys = merge_two' xs ys [];

fun  merge_one (ys:data) ((x12, x3)) =
  let
    fun eq_pair_str ((x,y):((string * string) * (string * string))) = eq_pair (op =) (op =) (x, y);
    val y3 = AList.lookup eq_pair_str ys x12;
    val new = if is_some y3 then [(x12, x3 ^ "," ^ the y3)] else [];
  in
    new
  end;

fun merge_two xs ys = Par_List.map (merge_one ys) xs |> flat: data;

fun merge_many [] = []
 |  merge_many (db::dbs:data list) = fold merge_two dbs db;

fun list_to_pair [x, y] = (x, y)
 |  list_to_pair _ = error "list_to_pair failed.";

fun merge_many [] = []
 |  merge_many (db::[]:data list) = db
 |  merge_many (db1::db2::[]:data list) = merge_two db1 db2
 |  merge_many (db1::db2::db3::[]:data list) = merge_two (merge_two db1 db2) db3
 |  merge_many (dbs:data list) =
  (Par_List.map merge_many [take (length dbs div 2) dbs, drop (length dbs div 2) dbs])
 |> list_to_pair
 |> uncurry merge_two;

(* The use of Table makes it necessary to sort the database prior to this step. *)

structure DataKey:KEY =
struct
  type key = (string * string);
  fun ord ((k1a, k1b), (k2a,k2b)) = String.compare (k1a ^ k1b, k2a ^ k2b);
end;

structure MyData = Table (DataKey);

type data_tbl  = string MyData.table;
type data_tbls = string MyData.table list;

fun  merge_one (ys:data_tbl) ((x12, x3)) =
  let
    val y3 = MyData.lookup ys x12;
    val new = if is_some y3 then [(x12, x3 ^ "," ^ the y3)] else [];
  in
    new
  end;

fun merge_two xs ys = Par_List.map (merge_one ys) (MyData.dest xs) |> flat |> MyData.make: data_tbl;

fun list_to_pair [x, y] = (x, y)
 |  list_to_pair _ = error "list_to_pair failed.";

fun merge_many' [] = error "merge_many failed. empty list."
 |  merge_many' (db::[]:data_tbls) = db
 |  merge_many' (db1::db2::[]:data_tbls) = merge_two db1 db2
 |  merge_many' (db1::db2::db3::[]:data_tbls) = merge_two (merge_two db1 db2) db3
 |  merge_many' (dbs:data_tbls) =
  (Par_List.map merge_many' [take (length dbs div 2) dbs, drop (length dbs div 2) dbs])
 |> list_to_pair
 |> uncurry merge_two;

fun merge_many (dbs:data list) =
let
   val sorted_dist = Par_List.map (sort_distinct (fn (p1, p2) => DataKey.ord (apply2 fst (p1, p2)))) dbs: data list;
   val db_tbls = Par_List.map MyData.make sorted_dist: string MyData.table list;
   val merged  = merge_many' db_tbls;
in
 MyData.dest merged
end;

\<close>



ML\<open>
val path = (Resources.master_directory @{theory} |> File.platform_path |> (fn name => name ^ "/"));
val path_to_database_names = path ^ "file_names.txt";
val file_names = ["ExampleDatabase1", "ExampleDatabase2"];
val paths = map (fn fname:string => path ^ fname) file_names: string list;

val input_files = Par_List.map TextIO.openIn paths: TextIO.instream list;
\<close>

ML\<open>
fun input_all (accm:string list) (ins:TextIO.instream) =
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
\<close>

ML\<open>
val liness = Par_List.map (input_all []) (input_files);
val _ = length liness |> Int.toString |> tracing;
val _ = map (tracing o Int.toString o length) liness;

fun get_pairs (line:string) = space_explode " " line
  |> (fn [x, y, z] => SOME ((x, y), z)
       | _ => (tracing "not a triple"; NONE) );

fun lines_to_pairs (lines:string list) = map get_pairs lines
 |> filter is_some |> map the;
fun liness_to_pairss (liness: string list list) = map lines_to_pairs liness;

val pairss = liness_to_pairss liness: ((string * string) * string) list list;

val merged = merge_many pairss;
val _ = length merged |> Int.toString |> tracing;

fun mk_one_line ((x:string, y:string), z:string) = x ^ " " ^ y ^ " " ^ z;

fun mk_lines (lines:((string * string) * string) list) = map mk_one_line lines |> String.concatWith "\n";

val output_lines = mk_lines (merge_many pairss)

val outstream = TextIO.openOut (path ^ "output.txt");
val _ = TextIO.outputSubstr (outstream, Substring.full output_lines);
val _ = TextIO.flushOut outstream;
\<close>

end
