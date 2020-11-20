open Heapmap

val scanInt = TextIO.scanStream (IntInf.scan StringCvt.DEC)

val input = ref TextIO.stdIn

fun read_int () = case scanInt (!input) of
          NONE => raise Fail "No integer"
        | SOME intVal => intVal

val read_nat = nat_of_integer o read_int
        
val print_int = print o IntInf.toString
val print_nat = print_int o integer_of_nat


local        
  fun iterate_aux 0 t _ = (print "\n"; t)
    | iterate_aux n t f = let
        val _ = MLton.GC.collect ();
        val _ = MLton.GC.unpack ();   
        
        val _ = print (IntInf.toString n)
        val ts = Time.now ()
        val _ = f ()
        val ts = Time.- (Time.now (), ts) 
        val t = Time.+ (t,ts)
        val _ = print ("(" ^ Time.toString ts ^ "s). ")
      in
        iterate_aux (n-1) t f
      end
in
  fun iterate n f = let
    val t = iterate_aux n Time.zeroTime f
    val t = Time.fromNanoseconds (Time.toNanoseconds t div n)
  in t end  
end

fun do_test_imp n num_iters = let    
  val _ = print "Heapmap Imp\n"
  val n = nat_of_integer n;
  val t = iterate num_iters (testsuite n)
  val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n");
  val _ = print ("Done t = " ^ Time.toString t ^ "s ("^ IntInf.toString num_iters ^ " iterations\n")
in () end  

fun do_test_fun n num_iters = let    
  val _ = print "Heapmap Fun\n"
  val n = nat_of_integer n;
  val t = iterate num_iters (fn () => ftestsuite n)
  val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n");
  val _ = print ("Done t = " ^ Time.toString t ^ "s ("^ IntInf.toString num_iters ^ " iterations\n")
in () end  


fun main () = let
  val args = CommandLine.arguments ();
  val args = map (fn x => (x, IntInf.fromString x)) args
in
  case args of
    [("fun",_),(_,SOME nn),(_,SOME ni)] => do_test_fun nn ni
  | [("imp",_),(_,SOME nn),(_,SOME ni)] => do_test_imp nn ni
  | _ => print ("Invalid command line\n")
end


val _ = if MLton.isMLton then main() else ()
