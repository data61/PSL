(*  Title:      Recursion-Theory-I/Utils.ML
    Author:     Michael Nedzelsky, email: MichaelNedzelsky <at> yandex <dot> ru

Some utilities for work with primitive recursive functions.
*)

(******** Utility functions. ***************)

exception BadArgument

fun extract_prop_arg (Const (@{const_name Pure.prop}, _) $ t) = t
  | extract_prop_arg  _ = raise BadArgument

fun extract_trueprop_arg (Const (@{const_name "Trueprop"}, _) $ t) = t
  | extract_trueprop_arg  _ = raise BadArgument

fun extract_set_args (Const (@{const_name Set.member}, _) $ t1 $ t2)  = (t1, t2)
  | extract_set_args  _ = raise BadArgument

fun get_num_by_set @{const_name PRecFun.PrimRec1} = 1
  | get_num_by_set @{const_name PRecFun.PrimRec2} = 2
  | get_num_by_set @{const_name PRecFun.PrimRec3} = 3
  | get_num_by_set _ = raise BadArgument

fun remove_abs (Abs (_, _, t)) = remove_abs t
  | remove_abs t = t

fun extract_free_from_app (t1 $ t2) (n: int) = extract_free_from_app t1 (n + 1)
  | extract_free_from_app (Free (s, tp)) n = (s, tp, n)
  | extract_free_from_app (Const (s, tp)) n = (s, tp, n)
  | extract_free_from_app _ n = raise BadArgument

fun extract_free_arg t = extract_free_from_app (remove_abs t) 0

fun get_comp_by_indexes (1, 1) = @{thm pr_comp1_1}
  | get_comp_by_indexes (1, 2) = @{thm pr_comp1_2}
  | get_comp_by_indexes (1, 3) = @{thm pr_comp1_3}
  | get_comp_by_indexes (2, 1) = @{thm pr_comp2_1}
  | get_comp_by_indexes (2, 2) = @{thm pr_comp2_2}
  | get_comp_by_indexes (2, 3) = @{thm pr_comp2_3}
  | get_comp_by_indexes (3, 1) = @{thm pr_comp3_1}
  | get_comp_by_indexes (3, 2) = @{thm pr_comp3_2}
  | get_comp_by_indexes (3, 3) = @{thm pr_comp3_3}
  | get_comp_by_indexes _ = raise BadArgument


(************ Tactic. ***************)

fun pr_comp_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val t = extract_trueprop_arg (Logic.strip_imp_concl t)
    val (t1, t2) = extract_set_args t
    val n2 =
      let
        val Const (s, _) = t2
      in
        get_num_by_set s
      end
    val (name, _, n1) = extract_free_arg t1
    val comp = get_comp_by_indexes (n1, n2)
  in
    Rule_Insts.res_inst_tac ctxt
      [((("f", 0), Position.none), Variable.revert_fixed ctxt name)] [] comp i
  end
  handle BadArgument => no_tac)

fun prec0_tac ctxt facts i =
  Method.insert_tac ctxt facts i THEN
  REPEAT (assume_tac ctxt i ORELSE pr_comp_tac ctxt i)
