(*  Title:      PaMpeR_Base.thy
    Author:     Yutaka Nagashima, CIIRC, CTU    
*)
theory PaMpeR_Base
  imports "SeLFiE.SeLFiE"
  keywords "apply2" :: prf_script
   and     "proof2" :: prf_block
begin

ML_file "Assertions.ML"

ML\<open> signature FE_INTERFACE = 
sig
  val FE_activate : unit -> unit
end;
\<close>

ML\<open> structure FE_Interface : FE_INTERFACE = 
struct
  fun get_name (Method.Source src) = ((Token.name_of_src src)|>fst)
    | get_name _ = "\n"
  fun FE_activate _ = 
  let
    val path = Resources.master_directory @{theory} |> File.platform_path : string;
    val path_to_database  = path ^ "/Database" : string;
    fun string_some NONE = "PANIC_SOMETHING_WENT_WRONG"
     |  string_some (SOME x) = x;    
    val _ =
      Outer_Syntax.command @{command_keyword apply2} "initial goal refinement step (unstructured)"
        (Method.parse >> (fn m => (Method.report m;
          Toplevel.proofs (fn pst => (
            if (get_name o fst) m = "\n"
            then 0
            else
              Isabelle_System.bash
                ("echo -n '" ^
                 (Method.position (SOME m) |> Position.file_of |> string_some) ^
                 (Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " " ^
                 (get_name o fst) m ^ " " ^ (Assertions.eval_assertion pst) ^ "\n" ^
                 "' >> " ^ path_to_database);
              Proof.apply m pst)))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>proof2\<close> "backward proof step"
    (Scan.option Method.parse >> (fn m =>
      (Option.map Method.report m;
       Toplevel.proof (fn state =>
         let
           val _ =
             if is_some m andalso (get_name o fst o the) m = "\n"
             then 0
             else
               Isabelle_System.bash
                 ("echo -n '" ^
                  (Method.position (SOME (the m)) |> Position.file_of |> string_some) ^
                  (Method.position (SOME (the m)) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " " ^
                  (get_name o fst o the) m ^ " " ^ (Assertions.eval_assertion state) ^ "\n" ^
                  "' >> " ^ path_to_database);
          val state' = state |> Proof.proof m |> Seq.the_result "";
          val _ =
            Output.information
              (Proof_Context.print_cases_proof (Proof.context_of state) (Proof.context_of state'));
        in state' end))))
      in
        ()
      end;

end;
\<close>

ML\<open>
FE_Interface.FE_activate ()
\<close>

lemma "True"
  by auto
  

end
