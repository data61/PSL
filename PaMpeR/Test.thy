theory Test
  imports PaMpeR Main
  keywords "assert_nth_true" :: diag
   and     "assert_nth_false" :: diag
begin

ML_file "../src/Parser_Combinator.ML"

ML{*

local

fun tokens_to_string tokens = tokens |> map Token.unparse |> String.concatWith " ";

fun string_parser_to_token_parser (symbols_parser:'a Parser_Combinator.parser) = (fn (tokens:Token.T list) =>
  tokens
  |> tokens_to_string
  |> Symbol.explode
  |> symbols_parser
  |> Seq.hd
  (*This function assumes that the string_parser consumes the entire string.*)
  |> apsnd (K ([]))) : 'a Token.parser;

structure Pc = Parser_Combinator;

infix >>=;
val op >>= =  Parser_Combinator.>>=;
type trans_trans = Toplevel.transition -> Toplevel.transition;

fun invocation_parser_to_trans_trans_parser (inv_p : int Pc.parser)
  (get_trans_trans : int -> trans_trans) =
  string_parser_to_token_parser (inv_p >>= (Pc.result o get_trans_trans)) : trans_trans Token.parser;

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

in

    val _ =
      Outer_Syntax.command @{command_keyword assert_nth_false} "initial goal refinement step (unstructured)"
        (invocation_parser_to_trans_trans_parser (Pc.nat:int Pc.parser) (get_trans_trans_gen 0));
    val _ =
      Outer_Syntax.command @{command_keyword assert_nth_true} "initial goal refinement step (unstructured)"
        (invocation_parser_to_trans_trans_parser (Pc.nat:int Pc.parser) (get_trans_trans_gen 1));

end;
*}

lemma
  assumes "True"
  shows "True"
  assert_nth_true 1
  assert_nth_false 2
  assert_nth_true 1
    apply simp
  done
    
end