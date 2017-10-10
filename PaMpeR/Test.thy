(* Title:  PSL/PaMpeR/Test.thy
   Author: Yutaka Nagashima, CIIRC, CTU
*)
theory Test
  imports PaMpeR "../PSL"
  keywords "assert_nth_true" :: diag
   and     "assert_nth_false" :: diag
   and     "asserts_check" :: diag
begin

ML{*
signature ASSERTION_CHECKER =
sig
  val activate_assertion_checker: unit -> unit;
end;

structure Assertion_Checker : ASSERTION_CHECKER =
struct

structure Pc = Parser_Combinator;

infix >>=;
type trans_trans = Toplevel.transition -> Toplevel.transition;

fun get_trans_trans_gen (yes_no:int) (assert_numb:int) =
    (((Toplevel.keep_proof:(Toplevel.state -> unit) -> trans_trans)
      (fn top =>
       let
         val proof_state   = Toplevel.proof_of top;
         val results = Assertions.eval_assertion_for_ML proof_state |> map Real.floor;
         val nth_result = List.nth (results, assert_numb - 1);
         val mssg = if yes_no = 0 then "false" else if yes_no = 1 then "true" else "something went wrong";
       in
         (@{assert} (nth_result = yes_no); tracing (Int.toString assert_numb ^ "th assertion is " ^ mssg))
       end)
     ):trans_trans);

fun get_trans_trans_ints (expected_results:int Seq.seq) =
    (((Toplevel.keep_proof:(Toplevel.state -> unit) -> trans_trans)
      (fn top =>
       let
         val proof_state     = Toplevel.proof_of top;
         val results         = Assertions.eval_assertion_for_ML proof_state |> map Real.floor;
         (* The checker should inform which assertion failed to given expectations.*)
         val expected        = Seq.list_of expected_results;
         val expected_length = length expected;
         val results_length  = length results;
         val shorter = if expected_length < results_length 
           then (tracing  ("Note that PaMpeR applies " ^ (Int.toString results_length) ^ 
                 " assertions but you provided only " ^ (Int.toString expected_length) ^ " integers.");
                 expected_length)
           else (tracing ("Note that you provided more integers than the number of assertions PaMpeR uses" ^
                 ". We ignore the surplus expectations."); results_length);
         val trimed_expected = take shorter expected;
         val trimed_results  =  take shorter results;
         val pairs           = trimed_expected ~~ trimed_results;
         val expect_met      = map (op =) pairs;
         fun take_numbs (ass:'a -> bool) (ys:'a list) =
           let
             fun take_numbs' (_:int)   (results:int list) ([]:'a list)    = results
               | take_numbs' (acc:int) (results:int list) (x::xs:'a list) =
                 take_numbs' (acc + 1) (if ass x then acc::results else results) xs;
           in
             (* numbering starts from 1 *)
             take_numbs' 1 [] ys : int list
           end;
         fun show_message (xs:int list)  = map (fn n => tracing (Int.toString n ^ "th assertion failed.")) xs;
         val _ = take_numbs (not) expect_met |> show_message;
         fun has_no_false xs = Utils.flip (fold (fn b1 => fn b2 => b1 andalso b2)) true xs : bool;
       in
         @{assert} (has_no_false expect_met)
       end)
     ):trans_trans);

fun activate_assertion_checker _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword assert_nth_false} "check if one assertion certainly fails"
        (PSL_Interface.parser_to_trans_trans_parser (Pc.nat:int Pc.parser) (get_trans_trans_gen 0));
    val _ =
      Outer_Syntax.command @{command_keyword assert_nth_true} "check if one assertion certainly holds"
        (PSL_Interface.parser_to_trans_trans_parser (Pc.nat:int Pc.parser) (get_trans_trans_gen 1));
    val _ =
      Outer_Syntax.command @{command_keyword asserts_check} "check if multiple assertions are working as expected."
        (PSL_Interface.parser_to_trans_trans_parser (Pc.token Pc.ints: int Seq.seq Pc.parser) (get_trans_trans_ints));
  in () end;
end;
*}

ML{* Assertion_Checker.activate_assertion_checker ();*}

lemma
  assumes "True"
  shows "True"
  assert_nth_true 1
  assert_nth_false 2
  assert_nth_true 1
  asserts_check [1, 0, 0]
    apply simp
  done
    
end