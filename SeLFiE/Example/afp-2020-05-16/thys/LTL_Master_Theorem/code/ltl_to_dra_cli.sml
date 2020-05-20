(* Initialise Parser *)
structure LtlParser = Ltl(PropLtl)

(* Printers *)
fun println x = print (x ^ "\n")
fun println_err x = (TextIO.output (TextIO.stdErr, x ^ "\n"); TextIO.flushOut TextIO.stdErr)

(* Main *)
fun usage () = println ("Usage: " ^ CommandLine.name () ^ " ltlformula");

fun main () =
  let 
    val e = fn () => OS.Process.exit (OS.Process.failure)
    val u = fn () => (usage(); e())
    val input = case CommandLine.arguments () of [] => valOf (TextIO.inputLine TextIO.stdIn) | x :: _ => x
    val phi = LtlParser.compile_from_string input handle LtlParser.LtlError msg => (println_err ("LTL Error: " ^ msg); usage (); e ())
    val aut = LTL.ltlc_to_draei_literals LTL.PropUnfold phi
  in 
    println (HOA.serialize phi aut)
  end
