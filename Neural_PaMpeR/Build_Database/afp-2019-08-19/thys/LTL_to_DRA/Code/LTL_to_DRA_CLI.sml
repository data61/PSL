(* Initialise Parser *)
structure LtlParser = Ltl(PropLtl)

(* Printers *)
fun println x = print (x ^ "\n")
fun println_err x = (TextIO.output (TextIO.stdErr, x ^ "\n"); TextIO.flushOut TextIO.stdErr)
fun fast_print x = TextIO.output (TextIO.stdOut, x)

open LTL;

fun print_ltl LTLTrue = fast_print "true"
  | print_ltl LTLFalse = fast_print "false"
  | print_ltl (LTLProp a) = fast_print a
  | print_ltl (LTLPropNeg a) = (fast_print "~"; fast_print a)
  | print_ltl (LTLAnd (x, y)) = (fast_print "("; print_ltl x; fast_print "&"; print_ltl y; fast_print ")")
  | print_ltl (LTLOr (x, y)) = (fast_print "("; print_ltl x; fast_print "|"; print_ltl y; fast_print ")")
  | print_ltl (LTLNext x) = (fast_print "X"; print_ltl x)
  | print_ltl (LTLGlobal x) = (fast_print "G"; print_ltl x)
  | print_ltl (LTLFinal x) = (fast_print "F"; print_ltl x)
  | print_ltl (LTLUntil (x, y)) = (fast_print "("; print_ltl x; fast_print "U"; print_ltl y; fast_print ")")

fun print_ltl_abs (Abs phi) = print_ltl phi

fun print_list p [] = ()
  | print_list p (x::[]) = (p x)
  | print_list p (x::xs) = (p x; fast_print ", "; print_list p xs)

fun print_set p (Set xs) = (fast_print "{"; print_list p xs; fast_print "}")
  | print_set p (Coset xs) = (fast_print "-{"; print_list p xs; fast_print "}")

fun print_mapping_list p1 p2 ([] : ('a * 'b) list) = ()
  | print_mapping_list p1 p2 ((a, b)::[]) = (p1 a; fast_print " -> "; p2 b)
  | print_mapping_list p1 p2 ((a, b)::xs) = (p1 a; fast_print " -> "; p2 b; fast_print ", "; print_mapping_list p1 p2 xs)

fun print_mapping p1 p2 (Mapping xs) = (fast_print "["; print_mapping_list p1 p2 xs; fast_print "]")

fun print_tuple p1 p2 (a, b) = (fast_print "("; p1 a; fast_print ", "; p2 b; fast_print ")")

fun print_triple p1 p2 p3 (a, (b, c)) = (fast_print "("; p1 a; fast_print ", "; p2 b; fast_print ", "; p3 c; fast_print ")")

fun print_state s = (print_tuple print_ltl_abs (print_mapping print_ltl (print_list print_ltl_abs))) s

fun print_transition s = print_triple print_state (print_set fast_print) print_state s

(* Main *)
fun usage () = println ("Usage: " ^ CommandLine.name () ^ " (-e|--eager) (-s|--simp=fast|--simp=slow) ltlformula");

fun main () =
  let 
    val e = fn () => OS.Process.exit (OS.Process.failure)
    val u = fn () => (usage(); e())
    val args = CommandLine.arguments ()
    val eager = List.exists (fn x => x = "-e" orelse x = "--eager") args
    val fast = List.exists (fn x => x = "--simp=fast") args
    val slow = List.exists (fn x => x = "-s" orelse x = "--simp=slow") args
    val ltl = List.last args
    val phi = LtlParser.compile_from_string ltl handle LtlParser.LtlError msg => (println_err ("LTL Error: " ^ msg); usage (); e ())
    val res = ltlc_to_rabin eager (if slow then Slow else (if fast then Fast else Nop)) phi
  in 
    (print_triple 
      (print_set print_transition)
      (print_state) 
      (print_set (print_tuple (print_set print_transition) (print_set (print_set print_transition)))) 
      res ; fast_print "\n"; TextIO.flushOut (TextIO.stdOut))
  end