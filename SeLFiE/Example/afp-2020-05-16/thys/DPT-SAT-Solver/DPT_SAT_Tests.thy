(*  Title:       Tests for DPTSAT
    Author:      Jasmin Blanchette <blanchette at in.tum.de>, 2009
    Maintainer:  Jasmin Blanchette <blanchette at in.tum.de>
*)

theory DPT_SAT_Tests
imports DPT_SAT_Solver
begin

ML \<open>
val path = File.tmp_path (Path.explode "sat.out")
val max_secs = 60

(*
val _ = File.write path ""
fun write_out s = (tracing s; File.append path (s ^ "\n"))
*)
val write_out = tracing

fun test name =
  let
    val solver = "dptsat"
    fun aux () =
      let
        val name = "cnf/" ^ name
        val timer1 = Timer.startRealTimer ()
        val formula =
          SAT_Solver.read_dimacs_cnf_file
            (Path.append (Resources.master_directory @{theory}) (Path.explode name))
        val timer2 = Timer.startRealTimer ()
        val res = SAT_Solver.invoke_solver solver formula
        val code = case res of
                     SAT_Solver.SATISFIABLE _ => "SAT"
                   | SAT_Solver.UNSATISFIABLE _ => "UNSAT"
                   | SAT_Solver.UNKNOWN => "UNKNOWN"
        fun show_time timer =
          signed_string_of_int (Time.toMilliseconds (Timer.checkRealTimer timer1)) ^ " ms"
      in
        write_out (solver ^ ":" ^ name ^ ": " ^ code ^ " " ^ show_time timer1 ^ " " ^
                  show_time timer2); code
      end
      handle Timeout.TIMEOUT _ => (write_out (solver ^ ":" ^ name ^ ": TIMEOUT"); "UNKNOWN")
  in
    Timeout.apply (Time.fromSeconds max_secs) aux ()
      handle Timeout.TIMEOUT _ => (write_out (solver ^ ":" ^ name ^ ": TIMEOUT"); "UNKNOWN")
  end

fun sat name = (test name = "SAT" orelse error "Expected SAT")
fun unsat name = (test name = "UNSAT" orelse error "Expected UNSAT")
\<close>

ML_val \<open>unsat "np.core.398356.cnf"\<close>
ML_val \<open>sat "np.core.398568.cnf"\<close>
ML_val \<open>unsat "np.core.398723.cnf"\<close>
ML_val \<open>unsat "np.core.398761.cnf"\<close>
ML_val \<open>unsat "np.core.398773.cnf"\<close>
ML_val \<open>unsat "np.core.398787.cnf"\<close>
ML_val \<open>unsat "np.core.398823.cnf"\<close>
ML_val \<open>unsat "np.core.398855.cnf"\<close>
ML_val \<open>unsat "np.core.398863.cnf"\<close>
ML_val \<open>unsat "np.core.398889.cnf"\<close>
ML_val \<open>unsat "np.core.398907.cnf"\<close>
ML_val \<open>sat "np.core.399306.cnf"\<close>
ML_val \<open>sat "np.core.399317.cnf"\<close>
ML_val \<open>sat "np.core.399458.cnf"\<close>
ML_val \<open>sat "np.core.399645.cnf"\<close>
ML_val \<open>unsat "np.core.399856.cnf"\<close>
ML_val \<open>unsat "np.core.399874.cnf"\<close>
ML_val \<open>unsat "np.core.399904.cnf"\<close>
ML_val \<open>unsat "np.core.399960.cnf"\<close>
ML_val \<open>unsat "np.core.400034.cnf"\<close>
ML_val \<open>unsat "np.core.400046.cnf"\<close>
ML_val \<open>unsat "np.core.400209.cnf"\<close>
ML_val \<open>unsat "np.core.400219.cnf"\<close>
ML_val \<open>unsat "np.core.400351.cnf"\<close>
ML_val \<open>unsat "np.core.400353.cnf"\<close>
ML_val \<open>unsat "np.core.400474.cnf"\<close>
ML_val \<open>unsat "np.core.400496.cnf"\<close>
ML_val \<open>sat "np.core.400660.cnf"\<close>
ML_val \<open>sat "np.core.400683.cnf"\<close>
ML_val \<open>unsat "np.core.400719.cnf"\<close>
ML_val \<open>unsat "np.core.400745.cnf"\<close>
ML_val \<open>unsat "np.core.400795.cnf"\<close>
ML_val \<open>unsat "np.core.401023.cnf"\<close>
ML_val \<open>sat "np.core.401292.cnf"\<close>
ML_val \<open>unsat "np.core.401685.cnf"\<close>
ML_val \<open>unsat "np.core.401784.cnf"\<close>
ML_val \<open>sat "np.core.402032.cnf"\<close>
ML_val \<open>unsat "np.core.402136.cnf"\<close>
ML_val \<open>unsat "np.core.402512.cnf"\<close>
ML_val \<open>sat "np.core.402547.cnf"\<close>
ML_val \<open>unsat "np.core.402722.cnf"\<close>
ML_val \<open>unsat "np.core.402730.cnf"\<close>
ML_val \<open>unsat "np.core.402742.cnf"\<close>
ML_val \<open>unsat "np.core.402772.cnf"\<close>
ML_val \<open>unsat "np.core.402774.cnf"\<close>
ML_val \<open>unsat "np.core.402778.cnf"\<close>
ML_val \<open>unsat "np.core.402794.cnf"\<close>
ML_val \<open>unsat "np.core.403005.cnf"\<close>
ML_val \<open>unsat "np.core.403015.cnf"\<close>
ML_val \<open>unsat "np.core.403051.cnf"\<close>
ML_val \<open>unsat "np.core.403079.cnf"\<close>
ML_val \<open>unsat "np.core.403559.cnf"\<close>
ML_val \<open>unsat "np.core.403586.cnf"\<close>
ML_val \<open>unsat "np.core.403624.cnf"\<close>
ML_val \<open>unsat "np.core.403642.cnf"\<close>
ML_val \<open>unsat "np.core.403836.cnf"\<close>
ML_val \<open>unsat "np.core.403838.cnf"\<close>
ML_val \<open>unsat "np.core.403862.cnf"\<close>
ML_val \<open>unsat "np.core.404160.cnf"\<close>
ML_val \<open>unsat "np.core.404182.cnf"\<close>
ML_val \<open>unsat "np.core.404186.cnf"\<close>
ML_val \<open>unsat "np.core.404196.cnf"\<close>
ML_val \<open>unsat "np.core.404200.cnf"\<close>
ML_val \<open>unsat "np.core.404234.cnf"\<close>
ML_val \<open>unsat "np.core.404238.cnf"\<close>
ML_val \<open>unsat "np.core.404246.cnf"\<close>
ML_val \<open>unsat "np.core.404266.cnf"\<close>
ML_val \<open>unsat "np.core.404318.cnf"\<close>
ML_val \<open>unsat "np.core.404326.cnf"\<close>
ML_val \<open>unsat "np.core.404334.cnf"\<close>
ML_val \<open>unsat "np.core.404344.cnf"\<close>
ML_val \<open>unsat "np.core.404368.cnf"\<close>
ML_val \<open>unsat "np.core.404388.cnf"\<close>
ML_val \<open>unsat "np.core.404394.cnf"\<close>
ML_val \<open>unsat "np.core.404414.cnf"\<close>
ML_val \<open>unsat "np.core.404460.cnf"\<close>
ML_val \<open>unsat "np.core.404506.cnf"\<close>
ML_val \<open>unsat "np.core.404510.cnf"\<close>
ML_val \<open>unsat "np.core.404534.cnf"\<close>
ML_val \<open>unsat "np.core.404592.cnf"\<close>
ML_val \<open>unsat "np.core.404596.cnf"\<close>
ML_val \<open>unsat "np.core.404866.cnf"\<close>
ML_val \<open>unsat "np.core.404876.cnf"\<close>
ML_val \<open>unsat "np.core.405031.cnf"\<close>
ML_val \<open>unsat "np.core.405035.cnf"\<close>
ML_val \<open>unsat "np.core.405052.cnf"\<close>
ML_val \<open>unsat "np.core.405056.cnf"\<close>
ML_val \<open>unsat "np.core.405095.cnf"\<close>
ML_val \<open>unsat "np.core.405097.cnf"\<close>
ML_val \<open>unsat "np.core.405100.cnf"\<close>
ML_val \<open>unsat "np.core.405125.cnf"\<close>
ML_val \<open>unsat "np.core.405155.cnf"\<close>
ML_val \<open>unsat "np.core.405184.cnf"\<close>
ML_val \<open>unsat "np.core.405205.cnf"\<close>
ML_val \<open>unsat "np.core.405217.cnf"\<close>
ML_val \<open>unsat "np.core.405254.cnf"\<close>
ML_val \<open>unsat "np.core.405286.cnf"\<close>
ML_val \<open>unsat "np.core.405296.cnf"\<close>
ML_val \<open>unsat "np.core.405314.cnf"\<close>
ML_val \<open>unsat "np.core.405343.cnf"\<close>
ML_val \<open>unsat "np.core.405362.cnf"\<close>
ML_val \<open>unsat "np.core.405372.cnf"\<close>
ML_val \<open>unsat "np.core.405391.cnf"\<close>
ML_val \<open>unsat "np.core.405443.cnf"\<close>
ML_val \<open>unsat "np.core.405445.cnf"\<close>
ML_val \<open>unsat "np.core.405455.cnf"\<close>
ML_val \<open>unsat "np.core.405464.cnf"\<close>
ML_val \<open>unsat "np.core.405536.cnf"\<close>
ML_val \<open>unsat "np.core.405571.cnf"\<close>
ML_val \<open>unsat "np.core.405579.cnf"\<close>
ML_val \<open>unsat "np.core.405588.cnf"\<close>
ML_val \<open>unsat "np.core.405647.cnf"\<close>
ML_val \<open>unsat "np.core.405649.cnf"\<close>
ML_val \<open>unsat "np.core.405657.cnf"\<close>
ML_val \<open>unsat "np.core.405687.cnf"\<close>
ML_val \<open>unsat "np.core.405701.cnf"\<close>
ML_val \<open>unsat "np.core.405703.cnf"\<close>
ML_val \<open>unsat "np.core.405721.cnf"\<close>
ML_val \<open>unsat "np.core.405740.cnf"\<close>
ML_val \<open>unsat "np.core.405811.cnf"\<close>
ML_val \<open>unsat "np.core.405817.cnf"\<close>
ML_val \<open>unsat "np.core.405823.cnf"\<close>
ML_val \<open>unsat "np.core.405869.cnf"\<close>
ML_val \<open>unsat "np.core.406136.cnf"\<close>
ML_val \<open>unsat "np.core.406138.cnf"\<close>
ML_val \<open>sat "np.core.406192.cnf"\<close>
ML_val \<open>sat "np.core.406216.cnf"\<close>
ML_val \<open>unsat "np.core.406290.cnf"\<close>
ML_val \<open>unsat "np.core.406294.cnf"\<close>
ML_val \<open>unsat "np.core.406310.cnf"\<close>
ML_val \<open>unsat "np.core.406355.cnf"\<close>
ML_val \<open>unsat "np.core.406411.cnf"\<close>
ML_val \<open>unsat "np.core.406413.cnf"\<close>
ML_val \<open>sat "np.core.406457.cnf"\<close>
ML_val \<open>sat "np.core.406541.cnf"\<close>
ML_val \<open>unsat "np.core.406599.cnf"\<close>
ML_val \<open>unsat "np.core.406601.cnf"\<close>
ML_val \<open>unsat "np.core.406609.cnf"\<close>
ML_val \<open>sat "np.core.406679.cnf"\<close>
ML_val \<open>unsat "np.core.406857.cnf"\<close>
ML_val \<open>unsat "np.core.406866.cnf"\<close>
ML_val \<open>unsat "np.core.406927.cnf"\<close>
ML_val \<open>unsat "np.core.406994.cnf"\<close>
ML_val \<open>unsat "np.core.407020.cnf"\<close>
ML_val \<open>unsat "np.core.407028.cnf"\<close>
ML_val \<open>sat "np.core.407044.cnf"\<close>
ML_val \<open>sat "np.core.407130.cnf"\<close>
ML_val \<open>unsat "np.core.407514.cnf"\<close>
ML_val \<open>unsat "np.core.407526.cnf"\<close>
ML_val \<open>unsat "np.huff.402973.cnf"\<close>
ML_val \<open>unsat "np.huff.403048.cnf"\<close>
ML_val \<open>unsat "np.huff.403214.cnf"\<close>
ML_val \<open>unsat "np.huff.403497.cnf"\<close>
ML_val \<open>unsat "np.huff.405095.cnf"\<close>
ML_val \<open>unsat "np.huff.405186.cnf"\<close>

end
