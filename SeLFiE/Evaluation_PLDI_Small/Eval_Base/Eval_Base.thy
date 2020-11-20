theory Eval_Base
  imports "PSL.PSL"
  keywords "apply2" :: prf_script
   and     "proof2" :: prf_block
   and     "by2"    :: "qed"
begin

ML\<open> (*enumerate*)
fun enumerate' [] _ = []
  | enumerate' (x::xs) acc = (acc, x) :: enumerate' xs (acc + 1)

fun enumerate xs = enumerate' xs 1;
\<close>

ML_file "Permutation.ML"

strategy PSL_WO_SeLFiE =
(*
PThenOne [DInduct, Auto_Solve]
*)
  Ors [
       Auto_Solve,
       PThenOne [DInduct, Auto_Solve],
       PThenOne [DInduct,
                 Thens [Auto, RepeatN(Hammer), IsSolved]
                 ]
  ]

strategy PSL_W_SeLFiE =
(*
PThenOne [Smart_Induct, Auto_Solve]
*)
  Ors [
       Auto_Solve,
       PThenOne [Smart_Induct, Auto_Solve],
       PThenOne [Smart_Induct,
                 Thens [Auto, RepeatN(Hammer), IsSolved]
                 ]
  ]

ML\<open>

local

infix 1 <*> <$>;

type trans_trans = Toplevel.transition -> Toplevel.transition;
open Parser_Combinator;

in

type proved = bool;

type result = {
  location    : (string * string),
  with_selfie : proved,
  wo_selfie   : proved,
  time_with   : int,
  time_without: int
};

fun result_to_string
({location   : (string * string),
  with_selfie: proved,
  wo_selfie  : proved,
  time_with   : int,
  time_without: int
}) =
let
  val list =
    [fst location, snd location,
     if with_selfie then "1" else "0",
     if wo_selfie   then "1" else "0",
     Int.toString time_with,
     Int.toString time_without
     ];
  val one_line = String.concatWith "," list;
in
   one_line: string
end;

end;

val write_result = undefined: result -> unit;

\<close>

ML\<open> fun model_meth_n_pst_to_fst_thm (model_meth:Method.text_range) (pst:Proof.state): thm =
  let
    val model_result_option = try (Proof.apply model_meth) pst
      >>= try Seq.filter_results
      >>= try Seq.hd
      >>= try Isabelle_Utils.proof_state_to_thm: thm option;
    val model_result = Option.getOpt (model_result_option, TrueI): thm;
  in
    model_result:thm
  end;

val timelimit_for_eval = seconds 30.0;
\<close>


ML\<open> fun evaluate (pst:Proof.state, m: Method.text_range) =
let
  fun timeout f                = Isabelle_Utils.timeout_apply timelimit_for_eval f;
  fun timeout_none f           = Utils.try_with NONE      (Isabelle_Utils.timeout_apply timelimit_for_eval f);
  fun timeout_false f          = Utils.try_with false     (Isabelle_Utils.timeout_apply timelimit_for_eval f);
  fun timeout_empty f          = Utils.try_with Seq.empty (Isabelle_Utils.timeout_apply timelimit_for_eval f);
  val ctxt                     = Proof.context_of pst: Proof.context;
  val psl_wo_selfie_str        = PSL_Interface.lookup ctxt "PSL_WO_SeLFiE" |> the;
  val psl_w_selfie_str         = PSL_Interface.lookup ctxt "PSL_W_SeLFiE"  |> the;
  fun str_to_result str        = timeout_empty ((timeout PSL_Interface.get_monad_tactic str) pst) [] |> (timeout_none Seq.pull) |> timeout_false is_some: bool;
  val time_before_without      = Time.now();
  val wo_selfie_result         = timeout_false str_to_result psl_wo_selfie_str: bool;
  val time_after_without       = Time.now ();
  val time_before_with         = Time.now();
  val w_selfie_result          = timeout_false str_to_result psl_w_selfie_str : bool;
  val time_after_with          = Time.now();
  val duration_without = Time.toMilliseconds (time_after_without - time_before_without);
  val duration_with    = Time.toMilliseconds (time_after_with    - time_before_with);
  fun string_some NONE = "Method_None_SOMETHING_WENT_WRONG"
   |  string_some (SOME x) = x;
  val location =
     (Method.position (SOME m) |> Position.file_of |> string_some,
      Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some);
  val result =
      {location    = location,
       with_selfie = w_selfie_result,
       wo_selfie   = wo_selfie_result,
       time_with   = duration_with,
       time_without= duration_without
       }: result;
in
  result_to_string result
end;
\<close>

ML\<open>
local

(*Method.text_range = text * Position.range;*)
fun state_to_unit  (pst:Proof.state) (m) =
  let
    val message = Isabelle_Utils.timeout_apply timelimit_for_eval evaluate (pst, m);
    val _ = tracing message;
    val path = Resources.master_directory @{theory} |> File.platform_path : string;
    val path_to_database  = path ^ "/Database.txt" : string;
    val _ = Isabelle_System.bash
            ("echo -n '" ^ message ^"\n" ^
             "' >> " ^ path_to_database);
  in () end

in

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply2\<close> "initial goal refinement step (unstructured)"
    (Method.parse >> (fn m => (
       Method.report m;
       Toplevel.proofs (fn pst =>
         (Isabelle_Utils.timeout_apply timelimit_for_eval (state_to_unit pst) m;
          Proof.apply m pst)
       ))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>proof2\<close> "backward proof step"
    (Scan.option Method.parse >> (fn m =>
      (Option.map Method.report m;
       Toplevel.proof (fn state =>
         let
          val _= Option.map (state_to_unit state) m;
          val state' = state |> Proof.proof m |> Seq.the_result "";
          val _ =
            Output.information
              (Proof_Context.print_cases_proof (Proof.context_of state) (Proof.context_of state'));
        in state' end))))

fun pst_to_unit m = (fn toplevel_state => state_to_unit (Toplevel.proof_of toplevel_state) m): Toplevel.state -> unit;
fun get_name (Method.Source src) = ((Token.name_of_src src)|>fst)

    fun local_terminal_proof (m1, m2) = (Toplevel.proof o 
          (fn m => 
            (fn state:Proof.state => 
              (state_to_unit state m1;
            Proof.local_future_terminal_proof m state)))) (m1, m2);
    fun global_terminal_proof (m1, m2) = 
        (Toplevel.end_proof o 
         K o 
         (fn m => 
             (fn state => (
                state_to_unit state m1;
                Proof.global_future_terminal_proof m state)))) (m1, m2)
    
    fun terminal_proof m = local_terminal_proof m o global_terminal_proof m;
    
    val _ =
      Outer_Syntax.command @{command_keyword by2} "terminal backward proof"
        (Method.parse -- Scan.option Method.parse >> (fn (m1, m2) =>
         (Method.report m1;
          Option.map Method.report m2;
          terminal_proof (m1, m2))));

end;
\<close>

end
