open Complementation
open Automaton

fun write_automaton path automaton =
let
	fun t (p, (a, q)) = Int.toString (integer_of_nat p) ^ " " ^ a ^ " " ^ Int.toString (integer_of_nat q) ^ "\n"
	val out = TextIO.openOut path
	fun write [] = () | write (x :: xs) = (TextIO.output (out, t x); write xs)
	val _ = write (transei automaton)
	val _ = TextIO.closeOut out
in
	()
end

val path = hd (CommandLine.arguments ())
(* TODO: maybe we want to optimize the representation, nbae_nba_impl includes list lookups *)
val _ = write_automaton path (complement_impl (nbaei_nbai automaton))
