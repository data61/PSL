(* This file provides an interface of nitpick as an assertion tactic for PSL.             *)
(* This file does not include significant code duplication with the Isabelle source code. *)
theory Quickcheck_as_Tactic
imports "../Runtime/Dynamic_Tactic_Generation"
begin

ML{* signature QUICKCHECK2 =
sig
 val quickcheck_tac: Proof.state Dynamic_Utils.logtac;
end;
*}

ML{* structure Quickcheck2 : QUICKCHECK2 =
struct

fun quickcheck_tac (state:Proof.state) =
  let
    (* syntactic sugars *)
    type log            = Dynamic_Utils.log;
    type state          = Proof.state;
    val do_trace        = false; (* do_trace and show_trace are for debugging only. *)
    val quickcheck      = Quickcheck.quickcheck;

    (* function body *)
    fun show_trace text = if do_trace then tracing text else ();
    val single = Seq.single ([], state);
    fun trace_error str = show_trace ("Quickcheck did not work well because " ^ str);
    fun result _        =  (case quickcheck [] 1 state of
      NONE => single (* quickcheck found no counterexample *)
    | SOME (genuine, _) => if genuine
        then Seq.empty (* quickcheck found a counterexample *)
        else single    (* quickcheck found a potentially spurious counterexample
                          due to under-specified functions*));
  in result () handle ERROR msg => (trace_error msg; single) : (log * state) Seq.seq
  end;

end
*}

ML{* structure Quickcheck_Tactic : DIAGNOSTIC_TACTIC =
struct

fun nontac (state:Proof.state) =
  let
    (* do_trace and show_trace are for debugging only. *)
    val do_trace        = false;
    fun show_trace text = if do_trace then tracing text else ();
    val quickcheck      = Quickcheck.quickcheck;
    val single          = Seq.single state;
    fun trace_no_cexm _ = show_trace "Quickcheck.quickcheck found no counterexample";
    fun trace_cexm _    = show_trace "Quickcheck.quickcheck found a  counterexample";
    fun trace_scexn _   = show_trace ("Quickcheck.quickcheck found a potentially spurious " ^
                                      "counterexample due to underspecified functions");
    fun trace_error str = show_trace ("Quickcheck did not work well because " ^ str);
    fun result _        =  (case quickcheck [] 1 state of
      NONE => (trace_no_cexm (); single)
    | SOME (genuine, _) => if genuine then (trace_cexm (); Seq.empty) else (trace_scexn (); single));
  in 
    result () handle ERROR msg => (trace_error msg; single) : Proof.state Seq.seq
  end;

end
*}


end