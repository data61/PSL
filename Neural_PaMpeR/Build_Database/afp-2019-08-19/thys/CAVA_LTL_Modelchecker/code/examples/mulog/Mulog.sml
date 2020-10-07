open Mulog

fun nth l 0 = hd l
  | nth l n = nth (tl l) (n-1)

fun getParameterString n default =
	if length (CommandLine.arguments ()) <= n
	then default
	else nth (CommandLine.arguments ()) n

fun getParameterInteger n default =
	if length (CommandLine.arguments ()) <= n
	then default
	else
		case Int.fromString (nth (CommandLine.arguments ()) n)
		of SOME k => k
		 | NONE => default

fun naturalNumbers 0 = []
  | naturalNumbers n = naturalNumbers (n - 1) @ [n - 1]

(* fun result_string r = case r of TY_ERR => "TY_ERR" | SAT => "SAT" | UNSAT => "UNSAT" | UNSAT_CE a => "UNSAT_CE" *)
fun result_string TY_ERR = "TY_ERR"
  | result_string SAT = "SAT"
  | result_string UNSAT = "UNSAT"
  | result_string (UNSAT_CE ce) = "UNSAT_CE" ^ "\n" ^ show_ce ce

fun run_test n =
(
	print (program_to_promela mulog_program ^ "\n");
	print (result_string (test n) ^ "\n");
	print (Statistics.pretty_stats (Statistics.get_active_stats ()) ^ "\n")
)

val _ = run_test (nat_of_integer (getParameterInteger 0 5))
