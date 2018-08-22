(*  Title:      FE_Interface.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CTU, CIIRC, University of Innsbruck

    Initiates the Feature Extraction system by overwritting Isar 
    keyword apply and by.
    
    Warning: Requires disabling the duplication check in outer_syntax.ML
    
    To generate Database, please do the following:

        1.Search and open outer_syntax.ML. (It usually resides in src/Pure/Isar/)
        2. a. Replace the return value of function err_dup_command by ()
           b. Re-define the "merge" function in the structure "Data" as following:
              fun merge data : T = data |> Symtab.join (fn name => fn (cmd1, cmd2) => cmd2);
        3.Search and open src/HOL/Main.thy
        4.import PSL/MiLkMaId/src/Build_Database.thy into src/HOL/Main.thy
        5.add a ML chunk of function call ML{*FE_Interface.FE_activate ()*} in src/HOL/Main.thy
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

  fun within_PSLs_scope (before:thm) = 90(*TODO*);

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

    fun just_trace (mssg:string) = (tracing mssg; mssg);

    fun get_mssg (meth_name:string) (m:Method.text_range) (pst:Proof.state) =
      if meth_name = "induct" orelse meth_name = "induction"
      then
        let
           val (in_scope, result_numb, nontac_numb) = Smart_Induct.psl_mk_right_mods m pst;
           val result_numb_str =  Int.toString result_numb;
           val nontac_numb_str =  Int.toString nontac_numb;
        in
          if in_scope
          then just_trace ("Within_the_scope_of_PSL "  ^ result_numb_str ^ " " ^ nontac_numb_str)
          else just_trace ("Outside_the_scope_of_PSL " ^ nontac_numb_str ^ " " ^ nontac_numb_str)
        end
      else "TODO";

    fun bash_script (meth_name:string) (m: Method.text_range) (pst:Proof.state): int =
      Isabelle_System.bash
        ("echo -n '" ^
         (Method.position (SOME m) |> Position.file_of |> string_some) ^
         (Method.position (SOME m) |> Position.line_of |> Option.map Int.toString |> string_some) ^ " " ^
         meth_name ^ " " ^ (get_mssg meth_name m pst) (*Assertions.eval_assertion pst*) ^ "\n" ^
         "' >> " ^ the (get_new_path meth_name));

    val _ =
      Outer_Syntax.command @{command_keyword apply2} "initial goal refinement step (unstructured)"
        (Method.parse >> (fn m => (Method.report m;
          let
             val meth_name = (Isabelle_Utils.get_meth_name o fst) m: string;
          in
            Toplevel.proofs
              (fn pst =>
                (if meth_name = "\n" orelse is_none (get_new_path meth_name)
                 then 0 else bash_script meth_name m pst;
                 Proof.apply m pst))
          end)));
  in
    ()
  end;
end;