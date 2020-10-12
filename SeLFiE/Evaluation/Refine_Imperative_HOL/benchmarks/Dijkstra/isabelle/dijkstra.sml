open Dijkstra

val scanInt = TextIO.scanStream (IntInf.scan StringCvt.DEC)

val input = ref TextIO.stdIn

fun read_int () = case scanInt (!input) of
          NONE => raise Fail "No integer"
        | SOME intVal => intVal

val read_nat = nat_of_integer o read_int
        
val print_int = print o IntInf.toString
val print_nat = print_int o integer_of_nat

fun 
  get_edges 0 acc = acc
| get_edges n acc = 
    let  
      val u = read_nat ()
      val v = read_nat ()
      val w = read_nat ()
      val acc = (u,(v,w))::acc
    in 
      if n mod 1000000 = 0 then print "." else ();
    
      get_edges (n - 1) acc
    end

   
fun read_graph () =
  let
    val _ = print "Reading graph ..."
    val nn = read_nat ();
    val ne = read_nat ();
    val edges = get_edges (integer_of_nat ne) [];
    val _ = print " Done\n"
  in 
    (nn,ne,edges)
  end

fun write_graph (nn,ne,edges) = let
  val _ = (print_nat nn; print "\n")
  val _ = (print_nat ne; print "\n")

  fun prl [] = () | prl ((u,(w,v))::l) = (print_nat u; print " "; print_nat v; print " "; print_nat w; print "\n"; prl l)
  
  val _ = prl edges
in
  ()
end
        
fun conv_imp_graph (nn,_,edges) = (nat_cr_graph_imp nn edges (),nn)

fun conv_fun_graph (nn,_,edges) = nat_cr_graph_fun nn (map (fn (u,(v,w)) => (u,(w,v))) edges)

val ran_graph = fn nn => ran_graph nn (nat_of_integer 18789321)
        
fun cr_ran_graph nn = 
  let
    val _ = print "Creating graph ..."
    val (_,edges) = ran_graph nn
    val edges = map (fn (u,(w,v)) => (u,(v,w))) edges
    val _ = print " Done\n"
  in  
    (nn,nat_of_integer (length edges),edges)
  end

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
   
val read_imp = conv_imp_graph o read_graph
val read_fun = conv_fun_graph o read_graph

val cr_imp = conv_imp_graph o cr_ran_graph o nat_of_integer
val cr_fun = conv_fun_graph o cr_ran_graph o nat_of_integer

fun do_test_fun G num_iters = let    
  val _ = print "Dijkstra Fun\n"
  val t = iterate num_iters (fn () => nat_dijkstra G (nat_of_integer 0))
  
  val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n");
  
  val _ = print ("Done t = "^ Time.toString t ^"s ("^ IntInf.toString num_iters ^ " iterations\n")
in () end  

fun do_test_imp (G,n) num_iters = let    
  val _ = print "Dijkstra Imp\n"
  val t = iterate num_iters (nat_dijkstra_imp n G (nat_of_integer 0))
  val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n");
  val _ = print ("Done t = " ^ Time.toString t ^ "s ("^ IntInf.toString num_iters ^ " iterations\n")
in () end  

fun main () = let
  val args = CommandLine.arguments ();
  val args = map (fn x => (x, IntInf.fromString x)) args
in
  case args of
    [("imp",_),(_,SOME nn),(_,SOME ni)] => do_test_imp (cr_imp nn) ni
  | [("fun",_),(_,SOME nn),(_,SOME ni)] => do_test_fun (cr_fun nn) ni
  | [("imp",_),(_,SOME ni)] => do_test_imp (read_imp ()) ni
  | [("fun",_),(_,SOME ni)] => do_test_fun (read_fun ()) ni
  | [("write",_), (_,SOME nn)] => write_graph (cr_ran_graph (nat_of_integer nn))
  | _ => print ("Invalid command line\n")
end


val _ = if MLton.isMLton then main() else ()
