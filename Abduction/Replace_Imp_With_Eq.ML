(*
 * Replace_Imp_With_Eq.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** structure Replace_Imp_With_Eq ***)
structure Replace_Imp_With_Eq: TOP_DOWN_CONJECTURING =
struct

open Top_Down_Util;

fun count_const_of_name_in (cname:string) (trm:term) =
  let
    fun count_const_of_name' (Const (name,  _)) acc = if cname = name then acc + 1 else acc
      | count_const_of_name' (Free           _) acc = acc
      | count_const_of_name' (Var            _) acc = acc
      | count_const_of_name' (Bound          _) acc = acc
      | count_const_of_name' (Abs (_, _, body)) acc = count_const_of_name' body acc
      | count_const_of_name' (trm1 $ trm2     ) acc = count_const_of_name' trm2 (count_const_of_name' trm1 acc)
  in
    count_const_of_name' trm 0
  end;

fun top_down_conjectures (ctxt:Proof.context) (trm:term) =
  let
    val has_exactly_one_meta_imp = count_const_of_name_in "Pure.imp" trm = 1;
    fun replace_imp_w_eq (Const ("Pure.imp", _)) = Const ("HOL.eq", dummyT)
      | replace_imp_w_eq (Const  p             ) = Const p
      | replace_imp_w_eq (Free   p             ) = Free  p
      | replace_imp_w_eq (Var    p             ) = Var   p
      | replace_imp_w_eq (Bound  i             ) = Bound i
      | replace_imp_w_eq (Abs  (name, typ, trm)) = Abs (name, typ, replace_imp_w_eq trm)
      | replace_imp_w_eq (Const ("Pure.imp", _) $ (Const ("HOL.Trueprop", _) $ lhs) $ (Const ("HOL.Trueprop", _) $ rhs)) =
        Const ("HOL.Trueprop", dummyT) $ (Const ("HOL.eq", dummyT) $ lhs $ rhs)
      | replace_imp_w_eq (func $ arg)            = replace_imp_w_eq func $ replace_imp_w_eq arg;
    val conjectures = if has_exactly_one_meta_imp then check_terms ctxt [replace_imp_w_eq trm] else [];
    val results     = map (pair "replace_imp_with_eq") conjectures
  in
    results
  end;

end;