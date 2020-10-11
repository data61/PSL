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
    val phi = LtlParser.compile_from_string (hd (CommandLine.arguments ())) handle LtlParser.LtlError msg => (println_err ("LTL Error: " ^ msg); usage (); e ())
  in 
    (println (LtlParser.toString (Example.rewrite phi)))
  end
