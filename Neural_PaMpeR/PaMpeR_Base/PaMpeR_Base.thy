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
  | get_name _ = "\n";

fun pst_to_pstate_to_1st_subg_n_chained_facts_as_strings (pst:Proof.state) =
    Isabelle_Utils.pstate_to_1st_subg_n_chained_facts pst
 |> map (Isabelle_Utils.trm_to_string (Proof.context_of pst)): strings;

fun pst_to_pstate_to_1st_subg_n_chained_facts (pst:Proof.state) =
  let
    val ctxt = Proof.context_of pst: Proof.context;
    val term_to_string = Isabelle_Utils.trm_to_string ctxt: term -> string;
    val fstgoal_n_chained_facts = Isabelle_Utils.pstate_to_1st_subg_n_chained_facts_record pst: {fst_subg:term option, chained_facts:terms};
  in
    {fst_subg      = "First_Subgoal " ^ Option.getOpt (Option.map term_to_string (#fst_subg fstgoal_n_chained_facts), ""),
     chained_facts = map (fn trm => "Chained_Fact " ^ term_to_string trm) (#chained_facts fstgoal_n_chained_facts)}
  end;

fun string_some NONE = "Cant_find_location_in_the_interactive_mode!"
 |  string_some (SOME x) = x;
val path = Resources.master_directory @{theory} |> File.platform_path : string;
val path_to_database  = path ^ "/Database.txt" : string;
fun method_n_string_to_line_in_database (m:Method.text_range) (string:string) =
          if (get_name o fst) m = "\n"
          then 0
          else
            Isabelle_System.bash
              ("echo -n '" ^
               (Method.position (SOME m) |> Position.file_of |> string_some) ^
               (Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " " ^ string ^ "\n' >> " ^ path_to_database);

fun FE_activate _ =
  let
    val _ =
      Outer_Syntax.command @{command_keyword apply2} "initial goal refinement step (unstructured)"
        (Method.parse >> (fn m => (Method.report m;
          Toplevel.proofs (fn pst => (
            let
              val fst_subg_n_chained_facts = pst_to_pstate_to_1st_subg_n_chained_facts pst;
            in
              (method_n_string_to_line_in_database m ((get_name o fst) m ^ " " ^ (Assertions.eval_assertion pst));
               method_n_string_to_line_in_database m (#fst_subg fst_subg_n_chained_facts);
               map (method_n_string_to_line_in_database m) (#chained_facts fst_subg_n_chained_facts));
              Proof.apply m pst
            end)))));
    val _ =
      Outer_Syntax.command \<^command_keyword>\<open>proof2\<close> "backward proof step"
        (Scan.option Method.parse >> (fn m =>
          (Option.map Method.report m;
           Toplevel.proof (fn state =>
             let
              val _ =
                if is_some m
                then
                  let
                    val meth = the m;
                    val fst_subg_n_chained_facts = pst_to_pstate_to_1st_subg_n_chained_facts state;
                  in
                  (method_n_string_to_line_in_database meth ((get_name o fst) meth ^ " " ^ (Assertions.eval_assertion state));
                   method_n_string_to_line_in_database meth (#fst_subg fst_subg_n_chained_facts);
                   map (method_n_string_to_line_in_database meth) (#chained_facts (fst_subg_n_chained_facts)))
                  end
                else [];
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
FE_Interface.FE_activate ();
\<close>

end
