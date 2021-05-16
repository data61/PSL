(*  Title:      FE_Interface.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CTU, CIIRC, University of Innsbruck

    Initiates the Feature Extraction system by overwritting Isar 
    keyword proof, apply and by.
    
    Warning: Requires disabling the duplication check in outer_syntax.ML
             This file is being updated for Isabelle2021. Not production-ready yet.
    
    To generate Database, please do the following:

        1.Search and open outer_syntax.ML. (It usually resides in src/Pure/Isar/)
        2. a. Replace the return value of function err_dup_command by ()
           b. Re-define the "merge" function in the structure "Data" as following:
              fun merge data : T = data |> Symtab.join (fn name => fn (cmd1, cmd2) => cmd2);
        3.Search and open src/HOL/Main.thy
        4.import PSL/MiLkMaId/src/Build_Database.thy into src/HOL/Main.thy
        5.add the following code snippet in the end of src/HOL/Main.thy just before the "end" keyword.
           ML_file "~/path_to_PSL/PSL/src/Utils.ML"
           ML_file "~/path_to_PSL/PSL/src/Subtool.ML"
           ML_file "~/path_to_PSL/PSL/src/../PGT/PGT.ML"
           ML_file "~/path_to_PSL/PSL/src/Dynamic_Tactic_Generation.ML"
           ML_file "~/path_to_PSL/PSL/src/Constructor_Class.ML"
           ML_file "~/path_to_PSL/PSL/src/Instantiation.ML"
           ML_file "~/path_to_PSL/PSL/src/Monadic_Prover.ML"
           ML_file "~/path_to_PSL/PSL/MeLoId/src/Build_Database/FE_Interface.ML"
           ML{*FE_Interface.FE_activate ()*}
          Note that the paths to MeLoId files have to be adjusted for each machine.
        6.Rebuild Isabelle heap

    By default the extracted feature file would be stored in PSL/MiLkMaId/src/Build_Database/Database.
*)
signature FE_INTERFACE = 
sig
  val FE_activate : unit -> unit
end;

structure FE_Interface : FE_INTERFACE = 
struct

  infix 1 >>= <$>;
  fun (m >>= f) = Option.mapPartial f m;
  fun (m <$> f) = Option.map f m;

  datatype induct_typ = Induct | Induction | Induct_Tac;

  fun which_induct (meth_name:string) =
    if "induct"     = meth_name then SOME Induct     else
    if "induction"  = meth_name then SOME Induction  else
    if "induct_tac" = meth_name then SOME Induct_Tac else NONE;

  fun FE_activate _ =
  let
    fun which_directory Induct     = "Induct/"
     |  which_directory Induction  = "Induction/"
     |  which_directory Induct_Tac = "Induct_Tac/";

    fun get_new_path' (induct:string) =
      File.platform_path (Resources.master_directory @{theory}) ^ "/Database/" ^ induct ^ serial_string ();

    fun get_new_path (meth_name:string) : string option = SOME meth_name
     >>= which_induct
     <$> which_directory
     <$> get_new_path';

    fun string_some NONE = "PANIC_SOMETHING_WENT_WRONG"
     |  string_some (SOME x) = x;

    fun gen_print_datum (datum:Smart_Induct.datum) =
      let
        val within = if #within_psls_scope datum
                     then "Within_the_scope_of_PSL"
                     else "Outside_the_scope_of_PSL": string;
        val numb_of_successful_meths = #numb_of_successful_meths datum |> Int.toString: string;
        val numb_of_created_methds   = #numb_of_created_methds   datum |> Int.toString: string;
        val first_line               = space_implode " " [within, numb_of_successful_meths,  numb_of_created_methds]: string;
        fun print_one_line (line:Smart_Induct.one_line) =
          let
            val bool_to_int_str = Int.toString o Utils.bool_to_int       : bool -> string;
            val used            = #used line |> bool_to_int_str          : string;
            val ass_results     = #ass_results line
                               |> Utils.add_index
                               |> map (apfst Int.toString)
                               |> map (apsnd bool_to_int_str)
                               |> map (fn (x,y) => x ^ ":" ^y)
           (*map bool_to_int_str (#ass_results line): strings;*)
            val meth_str        = "arguments_are " ^ #meth_w_args line   : string;
          in
            space_implode " " (("results_are_" ^ used::ass_results) @ [meth_str])
          end;
        val lines = map print_one_line (#lines datum): strings
      in
        (first_line, lines)
      end;

    fun print_datum (datum:Smart_Induct.datum) =
      let
        val (header, contents) = gen_print_datum datum;
      in header ^ "\n" ^ (space_implode "\n" contents) end;

    fun print_datum_w_header (datum:Smart_Induct.datum) (m:Method.text_range): string =
      let
        val (header, contents) = gen_print_datum datum;
        val location = (Method.position (SOME m) |> Position.file_of |> string_some) ^
                       (Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " ";
        fun mk_a_line (content:string) = location ^ " " ^ header ^ " result: " ^ content ^ " result_end";
        val lines = map mk_a_line contents |> String.concatWith "\n";
      in (tracing lines; lines) end;

    fun get_mssg (meth_name:string) (m:Method.text_range) (pst:Proof.state) =
      if meth_name = "induct" orelse meth_name = "induction"
      then
        let
           val datum = Smart_Induct.mk_datapoint m pst: Smart_Induct.datum;
        in
          (Isabelle_System.bash ("echo -n '" ^ print_datum_w_header datum m ^ "\n' >> ~/TOBEREMOVED_in_one_file.txt");
          (print_datum datum))
        end
      else "TODO";

    fun bash_script (meth_name:string) (m: Method.text_range) (pst:Proof.state): int =
      if is_some (get_new_path meth_name)
      then
        Isabelle_System.bash
          ("echo -n '" ^
           (Method.position (SOME m) |> Position.file_of |> string_some) ^
           (Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " " ^
           meth_name ^ " " ^ (get_mssg meth_name m pst) ^ "\n" ^
           "' >> " ^ the (get_new_path meth_name))
      else 0;

    val _ =
      Outer_Syntax.command \<^command_keyword>\<open>apply\<close> "initial goal refinement step (unstructured)"
            (Method.parse >> (fn m => (Method.report m;
              let
                 val meth_name = (Isabelle_Utils.get_meth_name o fst) m: string;
              in
                Toplevel.proofs
                  (fn pst =>
                    (if meth_name = "\n" orelse is_none (get_new_path meth_name)
                     then 0 else bash_script meth_name m pst;
                     Isabelle_System.bash ("echo -n '" ^ meth_name ^ "\n' >> ~/TOBEREMOVED_from_apply.txt");
                     Proof.apply m pst))
              end)));


    val local_terminal_proof = Toplevel.proof o
          (fn m =>
            (fn state =>
             let
                val meth_text_range = (fst m): Method.text_range;
                val meth_name       = (Isabelle_Utils.get_meth_name o fst) meth_text_range: string;
             in
              (if meth_name = "\n"
               then 0
               else
                 bash_script meth_name meth_text_range state;
                 Isabelle_System.bash ("echo -n '" ^ meth_name ^ "\n' >> ~/TOBEREMOVED_from_by_local.txt");
                 Proof.local_future_terminal_proof m state)
             end));

    val global_terminal_proof =
        Toplevel.end_proof o
        K o
        (fn m =>
             let
                val meth_text_range = (fst m): Method.text_range;
                val meth_name       = (Isabelle_Utils.get_meth_name o fst) meth_text_range: string;
             in
              (fn state => (if meth_name = "\n"
                            then 0
                            else
                              bash_script meth_name meth_text_range state;
                              Isabelle_System.bash ("echo -n '" ^ meth_name ^ "\n' >> ~/TOBEREMOVED_from_by_global.txt");
                           Proof.global_future_terminal_proof m state))
             end);

    fun terminal_proof m trans = (local_terminal_proof m o global_terminal_proof m) trans;

    val _ =
      Outer_Syntax.command @{command_keyword by} "terminal backward proof"
        (Method.parse -- Scan.option Method.parse >> (fn (m1, m2) =>
         (Method.report m1;
          Option.map Method.report m2;
          terminal_proof (m1, m2))));

    val _ =
      Outer_Syntax.command \<^command_keyword>\<open>proof\<close> "backward proof step"
        (Scan.option Method.parse >> (fn m =>
          (Option.map Method.report m;
           Toplevel.proof (fn state =>
             let
               val meth_name = Option.map (Isabelle_Utils.get_meth_name o fst) m: string option;
               val _ = if is_some meth_name andalso is_some m
                       then
                        (if the meth_name = "\n" orelse is_none (get_new_path (the meth_name))
                         then 0 else bash_script (the meth_name) (the m) state;
                         Isabelle_System.bash ("echo -n '" ^ the meth_name ^ "\n' >> ~/TOBEREMOVED_from_proof.txt"))
                       else 0;
              val state' = state |> Proof.proof m |> Seq.the_result "";
              val _ =
                Output.information
                  (Proof_Context.print_cases_proof (Proof.context_of state) (Proof.context_of state'));
            in state' end))))

      in
        ()
      end;

end;