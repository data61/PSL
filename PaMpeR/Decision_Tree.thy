(*  Title:      Decision_Tree.ML
    Author:     Yutaka Nagashima, CIIRC, CTU

    This file contains an experimental implementation of a decision tree construction algorithm.
*)
theory Decision_Tree
  imports Read_Databases
begin

ML_file "../src/Utils.ML"
ML_file "../src/Parser_Combinator.ML"

ML{*
val debug_mode = false;
fun debug switch (str:string) (f) = if debug_mode orelse switch then (tracing str; f) else f;
*}

(* Let us assume that the feature vector is a vector of boolean values for now. *)
ML{* signature REGRESSION_TREE =
sig
  type feature_name   = Database.feature_name;
  type feature_value  = bool;
  type feature        = feature_name * feature_value;
  type feature_vector = feature list;
  type used           = Database.used;
  type one_invocation = used * feature_vector;
  type database       = one_invocation list;
  datatype growing_tree = Leaf of database
                        | Branch of {True:    growing_tree,
                                     Feature: feature,
                                     False:   growing_tree };
  (*A criterion is the maximum number all regions.*)
  type criterion  = int;
  datatype final_tree = FLeaf of real
                      | FBranch of {More:    final_tree,
                                    Feature: feature,
                                    Less:    final_tree};

  val bool_to_real: bool -> real;
  val get_database_of_tree:      growing_tree -> database;
  val get_numb_of_elms: growing_tree -> int;
  val criterionN: criterion;
  val get_avrg_of_database:      database -> real;
  val get_avrg_of_gtree:         growing_tree -> real;
  val get_RSS:                   feature_name -> database -> real
  val get_feature_with_mini_RSS: database -> feature_name option;
  val split_region:              database -> growing_tree option;
  val get_big_tree:              database -> growing_tree;
  val gtree_leaf_map:            (database -> real) -> growing_tree -> final_tree;
  val post_process:              growing_tree -> final_tree;
  val print_final_tree:          final_tree -> string;
  val parse_printed_tree:        string -> final_tree;
end;
*}

ML{* structure Regression_Tree: REGRESSION_TREE = struct

type feature_name     = Database.feature_name;
type feature_value    = bool;
type feature          = (feature_name * feature_value);
type feature_vector   = feature list;
type used             = bool;
type one_invocation   = (used * feature_vector);
type database         = one_invocation list;
datatype growing_tree = Leaf of database
                      | Branch of {True:    growing_tree,
                                   Feature: feature,
                                   False:   growing_tree };
type criterion  = int;
datatype final_tree = FLeaf of real
                    | FBranch of {More:    final_tree,
                                  Feature: feature,
                                  Less:    final_tree};

fun bool_to_real true  = 1.0
 |  bool_to_real false = 0.0;

fun get_database_of_tree (Leaf dtbs) = dtbs
 |  get_database_of_tree (Branch {True=TrueT, False=FalseT, ...}) =
      get_database_of_tree TrueT @ get_database_of_tree FalseT;

fun get_numb_of_elms (Leaf dtbs) = List.length dtbs
 |  get_numb_of_elms (Branch {True=TrueT, False=FalseT, ...}) =
      get_numb_of_elms TrueT + get_numb_of_elms FalseT;

val criterionN = 1000;

fun get_avrg_of_database dtbs =
  let
    fun is_meth_used ((is_used, _):one_invocation) = is_used;
    val size    = length dtbs |> Real.fromInt;
    val trues   = filter is_meth_used dtbs |> length |> Real.fromInt;
    val average = trues / size;
  in
    average
  end;

fun get_avrg_of_gtree (gtree:growing_tree) =
  gtree |> get_database_of_tree |> get_avrg_of_database;

fun eq_feature (feat1:feature_name, feat2:feature_name) = feat1 = feat2 : bool;

fun option_error (err_msg:string) NONE      = error err_msg
 |  option_error  _              (SOME sth) = sth;

fun get_fval_of_fname (fname:feature_name) (fvec:feature_vector) =
  AList.lookup eq_feature fvec fname |> option_error "get_fval failed";

fun get_fval_of_one_invocation (fname:feature_name) ((_, fvec):one_invocation) =
  get_fval_of_fname fname fvec:feature_value;

fun split_database' (_    :feature_name) ([]:database)           accumlator     = accumlator        
 |  split_database' (fname:feature_name) (datum::data:database) (trues, falses) =
  let
    val fval       = get_fval_of_one_invocation fname datum;
    val accmulator = if fval then (datum::trues, falses) else (trues, datum::falses);
  in
    split_database' fname data accmulator
  end;

fun split_database fname data = split_database' fname data ([],[])
  |> (fn p as (left, right) => (
        debug false ("the number of left  elements is " ^ Int.toString (length left)) ();
        debug false ("the number of right elements is " ^ Int.toString (length right)) ();
      p));

fun get_RSS (fname as (Database.Feature fint):feature_name) (data:database) =
let
  val _ = debug false ("splitting at Feature " ^ Int.toString fint) ();
  val (trues, falses)  = split_database fname data : (database * database);
  val (t_avrg, f_avrg) = apply2 get_avrg_of_database (trues, falses);
  fun residual_square _       ([]:database)          (accm:real) = accm
   |  residual_square average (datum::data:database) (accm:real) =
    let
      val fval = fst datum |> bool_to_real;
      val diff = fval - average;
      val sqr  = diff * diff;
      val new_accm = accm + sqr;
    in
      residual_square average data new_accm
    end;
   val _ = debug false ("t_avrg in get_RSS is  " ^ Real.toString t_avrg) ();
   val _ = debug false ("f_avrg in get_RSS is  " ^ Real.toString f_avrg) ();
   val rss_true  = if Real.isNan t_avrg then Real.posInf else residual_square t_avrg trues  0.0;
   val rss_false = if Real.isNan f_avrg then Real.posInf else residual_square f_avrg falses 0.0;
   val _ = debug false ("In get_RSS, the number of residual_square is " ^ (Real.toString (rss_true + rss_false) ^ " for Feature " ^ Int.toString fint))
in
  rss_true + rss_false
end;

fun database_to_fname_list ([]:database) = error "database_to_fname_list failed"
  | database_to_fname_list (datum::_)    = snd datum |> map fst: feature_name list;

(* This can be inefficient for boolean feature values 
 * because it checks features that have been already checked in upper nodes. *)
fun get_feat_with_mini_RSS' (_:database)    (best_fname:feature_name, _:real)        ([]:feature_name list)         = best_fname
 |  get_feat_with_mini_RSS' (data:database) (best_fname:feature_name, mini_rss:real) (fname::fnames:feature_name list) = 
  let
    val new_rss              = get_RSS fname data;
    val _ = debug false ("new_rss is " ^ Real.toString new_rss) ();
    val (new_best, new_mini) = if new_rss < mini_rss then (fname, new_rss) else (best_fname, mini_rss);
  in
    get_feat_with_mini_RSS' data (new_best, new_mini) fnames
  end;

fun get_feature_with_mini_RSS (data:database) =
  let
    val fnames = database_to_fname_list data: feature_name list;
    val fname as (Database.Feature fint) = if length fnames > 0 then hd fnames else error "get_feature_with_mini_RSS failed!";
    val rss    = get_RSS fname data;
    val _ = debug false ("for " ^ Int.toString fint ^ "th feature: rss is " ^ Real.toString rss) ();
    val fname = get_feat_with_mini_RSS' data (fname, rss) fnames;
    val mini_rss = get_RSS fname data;
    val result = if Real.== (Real.posInf, mini_rss) then NONE else SOME fname;
  in
    result
  end;

(*TODO: clean-up*)
fun split_region (database:database) =
  let
    val fname_to_split = get_feature_with_mini_RSS database: feature_name option;
    val result =
      if is_some fname_to_split
      then
        let
          val split_at as (Database.Feature fname) = the fname_to_split;
          val (trues, falses) = split_database split_at database: (database * database);
        in (tracing ("making a Branch by splitting at " ^ Int.toString fname);
            Branch {True    = Leaf trues,
                    Feature = (the fname_to_split, true (*Our feature is binary. So, this does not matter here.*)),
                    False   = Leaf falses} |> SOME)
        end
      else
         NONE;
  in result end;

(* FIXME: to be refined. *)
fun gtree_repeat (Leaf data) =
     (debug false "gtree_repeat in the first clause" ();
      if   length data < criterionN
      then Leaf data
      else (if is_some (split_region data)
           then gtree_repeat (split_region data |> the)
           else Leaf data):growing_tree)
(*
      else gtree_repeat (split_region data))
*)
  | gtree_repeat (Branch {True=right, Feature=feat, False=left}) =
     (debug false "gtree_repeat in the second clause" ();
      Branch {True    = gtree_repeat right,
              Feature = feat,
              False   = gtree_repeat left}:growing_tree);

fun get_big_tree (data:database) = gtree_repeat (Leaf data);

fun gtree_leaf_map (f:database -> real) (Leaf dtbs:growing_tree) = FLeaf (f dtbs)
  | gtree_leaf_map (f:database -> real) (Branch {True = gtree1, Feature = feature, False = gtree2}) =
      FBranch {More    =  gtree_leaf_map f gtree1,
               Feature = feature,
               Less    =  gtree_leaf_map f gtree2 };

fun post_process (gtree:growing_tree) = gtree_leaf_map get_avrg_of_database gtree : final_tree;

fun print_feat ((Database.Feature f_index, _):feature) = Int.toString f_index;

fun print_final_tree (FLeaf real) = "expectation " ^ Real.toString real
  | print_final_tree (FBranch {More = ftree1, Feature = feat, Less = ftree2}) =
    "(" ^ String.concatWith ", " [print_feat feat, print_final_tree ftree1, print_final_tree ftree2] ^ ")";

local

open Parser_Combinator;
infix >>= plus;

in

fun parse_fleaf _ =
  token (string "expectation") >>= K (
  token real >>= (fn expectation =>
  result (FLeaf expectation)))
and parse_fbranch _ =
  token (symbol "(")     >>= K (
  token int              >>= (fn feat_index:int =>
  token (symbol ",")     >>= K (
  token (parse_ftree ()) >>= (fn more_tree =>
  token (symbol ",")     >>= K (
  token (parse_ftree ()) >>= (fn less_tree =>
  token (symbol ")")     >>= K (
  result (FBranch {More = more_tree,
                   Feature = (Database.Feature feat_index, true),
                   Less = less_tree})
  )))))))
and parse_ftree _ = parse (parse_fleaf () plus parse_fbranch ());

fun parse_printed_tree (dtr:string) = parse_ftree () (String.explode dtr |> map Char.toString) |> Seq.hd |> fst;

end;

end;
*}

(* test *)
ML{*
local
  open  Regression_Tree;
  structure RT = Regression_Tree;
  val ftree = RT.FBranch {More = RT.FLeaf ~2.2,
                          Feature = (Database.Feature 3, true),
                          Less = RT.FLeaf ~1.1};
  val ftree2 = RT.FBranch {More = ftree, Feature = (Database.Feature 1, true), Less = ftree};
  val ftree3 = RT.FBranch {More = ftree2, Feature = (Database.Feature 10, true), Less = ftree2};
in
  val test_string = RT.print_final_tree ftree3;
end;

tracing test_string;
*}

ML{* tracing test_string*}

ML{* Regression_Tree.parse_printed_tree test_string *}

(* test using datasets *)

(* To use this test, you have to generate the database and pre-process it first. *)

ML{* val rgtree = Regression_Tree.get_big_tree (Database.parse_database "induct"); *}

ML{* val ftree = Regression_Tree.post_process rgtree; *}

ML{* val printed_tree = Regression_Tree.print_final_tree ftree; *}

ML{* tracing printed_tree; *}

end