(*
 * Generalise_By_Renaming.ML
 *
 * Utility functions for our top-down approach, as known as "deep conjecturing".
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** structure Generalise_By_Renaming ***)
structure Generalise_By_Renaming: TOP_DOWN_CONJECTURING =
(*TODO: too many candidates are produced.*)
struct

fun count_fvars' (Const _) acc = acc
  | count_fvars' (Free _) acc = acc + 1
  | count_fvars' (Var _) acc = acc
  | count_fvars' (Bound _) acc = acc
  | count_fvars' (Abs (_, _, body)) acc = count_fvars' body acc
  | count_fvars' (trm1 $ trm2) acc = count_fvars' trm2 (count_fvars' trm1 acc)

fun count_fvars trm = count_fvars' trm 0;

fun get_ints (ints_so_far:ints) =
  let
    val _ = if length ints_so_far = 0 then error "get_ints failed with an empty list." else (); 
    val maximum = Utils.ints_to_max_option ints_so_far |> the;
    val next_candidates = 1 upto (maximum + 1): ints;
    val new_intss = map (fn new_int => ints_so_far @ [new_int]) next_candidates: ints list;
  in
    new_intss: ints list
  end;

fun get_intss' (upper_limit:int) (intss_so_far:ints list) =
  if length (hd intss_so_far) < (upper_limit:int)
  then get_intss' upper_limit (map get_ints intss_so_far |> flat)
  else intss_so_far;

fun get_intss (upper_limit:int) = get_intss' upper_limit [[1]];

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun replace (Const p) [] = Const p
  | replace (Free (_, typ)) ([int]:ints) = mk_free_variable_of_typ typ int
  | replace (Var p) [] = Var p
  | replace (Bound i) [] = Bound i
  | replace (Abs (name, typ, body)) ints =
    let
      val new_bodies = replace body ints: term;
    in
      Abs (name, typ, new_bodies)
    end
  | replace (func $ arg) ints =
    let
      val numb_of_fvars_in_func = count_fvars func;
      val (ints_for_func, ints_for_arg) = chop numb_of_fvars_in_func ints: (ints * ints);
    in
      replace func ints_for_func $ replace arg ints_for_arg
    end
  | replace _ _ = error "replace failed. Pattern-matching failed!";

fun generalise_by_rename_free_variables' _ (trm:term) =
  if 0 < count_fvars trm andalso count_fvars trm < 8
  then
    let
      val numb_of_fvars = count_fvars trm: int;
      val intss = get_intss numb_of_fvars: ints list;
    in
      map (replace trm) intss
    end
  else [];

(*Util*)
fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun top_down_conjectures ctxt trm =
  map (fn tm => ("generalise_by_renaming", tm))
  (generalise_by_rename_free_variables' ctxt trm
  |> map (HOLogic.mk_Trueprop o remove_Trueprop)
  |> map (try (Syntax.check_term ctxt))
  |> Utils.somes);

end;