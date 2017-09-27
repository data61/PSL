(*  Title:      PaMpeR_Interface.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    Enable the Proof_advice keyword.
    Using a built in bash egrep to search the trained recommendation database. Outputting most promising 9 methods.
*)

signature PAMPER_INTERFACE = 
sig
  val PaMpeR_activate : unit -> unit
end;
structure PaMpeR_Interface = 
struct
  fun PaMpeR_activate _ = 
  let
    val path:string = (Resources.master_directory @{theory} |> File.platform_path) ^ "/recommend";
    fun assert_advice str = (if str = "no subgoal" then writeln "no subgoal!" else 
                        (Isabelle_System.bash("egrep '" ^ str ^ "' " ^ path ^ " | cut -d ' ' -f 1-10");()))
    val simp_interface =                                                               
      Toplevel.keep_proof (fn Tstate =>                                       
    let
      val state = Toplevel.proof_of Tstate
    in
      assert_advice (Assertions.eval_assertion state)
    end  )
  val _ = Outer_Syntax.command @{command_keyword proof_advice} "Method recommender"
      (Scan.succeed simp_interface);
  in
    ()
  end;
end;
PaMpeR_Interface.PaMpeR_activate ();
