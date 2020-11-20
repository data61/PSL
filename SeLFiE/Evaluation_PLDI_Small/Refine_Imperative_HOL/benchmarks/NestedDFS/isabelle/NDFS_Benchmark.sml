
structure TIO = TextIO
val scanInt = TIO.scanStream (IntInf.scan StringCvt.DEC)

val input = ref TIO.stdIn

fun read_int () = case scanInt (!input) of
          NONE => raise Fail "No integer"
        | SOME intVal => intVal

fun get_acc () =
  let fun get_acc' acc =
    let val a = read_int () in
    if a = ~1 then acc
    else get_acc' (a::acc) end
  in get_acc' [] end

fun get_edges () =
  let fun get_edges' acc =
    let val a = read_int () in
    if a = ~1 then acc
    else get_edges' ((a, read_int())::acc) end
  in get_edges' [] end

fun create_graph() =
  let
    val num = read_int();
    val acc = get_acc();
    val edges = get_edges();
  in (num, acc, edges) end
        
        
local        
  fun iterate 0 t _ = t
    | iterate n t f = let
        val _ = MLton.GC.collect ();
        val _ = MLton.GC.unpack ();   
        
        val _ = print (IntInf.toString n)
        val ts = Time.now ()
        val _ = f ()
        val ts = Time.- (Time.now (), ts) 
        val t = Time.+ (t,ts)
        val _ = print ("(" ^ Time.toString ts ^ "s). ")
      in
        iterate (n-1) t f
      end
  
in  
  fun measure n { conv, run } = let
    val _ = print ("Converting graph ...");
    val G = conv ()  
    val _ = print ("Done\n");
    
    val _ = print ("DFS ");
    val t = iterate n Time.zeroTime (run G)
    val t = Time.fromNanoseconds (Time.toNanoseconds t div n)
    val _ = print ("\n");
    val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n")
  in () end

end
        
local open NDFS_Benchmark in
  fun bm_fun (_,acc,edges) = { 
    conv = (fn () => (fun_acc_of_list acc, fun_succ_of_list edges)), 
    run = (fn (acc,succ) => fn () => fun_ndfs_impl succ acc (nat_of_integer 0) ) 
  }

  fun bm_funs (_,acc,edges) = { 
    conv = (fn () => (funs_acc_of_list acc, funs_succ_of_list edges)), 
    run = (fn (acc,succ) => fn () => funs_ndfs_impl succ acc (nat_of_integer 0) ) 
  }

  fun bm_imp (n,acc,edges) = { 
    conv = (fn () => (imp_acc_of_list acc (), imp_graph_of_list n edges ())), 
    run = (fn (acc,succ) => fn () => imp_ndfs_impl succ acc (nat_of_integer 0) () ) 
  }

  fun bm_imps (n,acc,edges) = { 
    conv = (fn () => (imp_acc_of_list acc (), imp_graph_of_list n edges ())), 
    run = (fn (acc,succ) => fn () => imp_ndfs_sz_impl (nat_of_integer n) succ acc (nat_of_integer 0) () ) 
  }
  
end
  
  
fun test_fun (_,acc,edges) = let
  open NDFS_Benchmark
  val _ = print ("Converting graph ...");
  val acc = fun_acc_of_list acc
  val succ = fun_succ_of_list edges
  val _ = print ("Done\n");

  val _ = MLton.GC.collect ();
  
  val _ = print ("DFS ...");
  val t = Time.now ()
  val r = fun_ndfs_impl succ acc (nat_of_integer 0)
  val t = Time.- (Time.now (), t)
  val _ = print ("Done\n");
  val _ = case r of NONE => print "No counterexample\n" | _ => print "Counterexample\n"
  val _ = print ("Time: " ^ Time.toString t ^ "s\n")
in () end
        
fun test_funs (_,acc,edges) = let
  open NDFS_Benchmark
  val _ = print ("Converting graph ...");
  val acc = funs_acc_of_list acc
  val succ = funs_succ_of_list edges
  val _ = print ("Done\n");

  val _ = MLton.GC.collect ();

  val _ = print ("DFS ...");
  val t = Time.now ()
  val r = funs_ndfs_impl succ acc (nat_of_integer 0)
  val t = Time.- (Time.now (), t)
  val _ = print ("Done\n");
  val _ = case r of NONE => print "No counterexample\n" | _ => print "Counterexample\n"
  val _ = print ("Time: " ^ Time.toString t ^ "s\n")
in () end

fun test_imp (n,acc,edges) = let
  open NDFS_Benchmark
  val _ = print ("Converting graph ...");
  val acc = imp_acc_of_list acc ()
  val succ = imp_graph_of_list n edges ()
  val _ = print ("Done\n");

  val _ = MLton.GC.collect ();

  val _ = print ("DFS ...");
  val t = Time.now ()
  val r = imp_ndfs_impl succ acc (nat_of_integer 0) ()
  val t = Time.- (Time.now (), t)
  val _ = print ("Done\n");
  val _ = case r of NONE => print "No counterexample\n" | _ => print "Counterexample\n"
  val _ = print ("Time: " ^ Time.toString t ^ "s\n")
in () end

fun test_imps (n,acc,edges) = let
  open NDFS_Benchmark
  val _ = print ("Converting graph ...");
  val acc = imp_acc_of_list acc ()
  val succ = imp_graph_of_list n edges ()
  val _ = print ("Done\n");

  val _ = MLton.GC.collect ();
  val _ = MLton.GC.unpack ();   
  
  val _ = print ("DFS ...");
  val t = Time.now ()
  val r = imp_ndfs_sz_impl (nat_of_integer n) succ acc (nat_of_integer 0) ()
  val t = Time.- (Time.now (), t)
  val _ = print ("Done\n");
  val _ = case r of NONE => print "No counterexample\n" | _ => print "Counterexample\n"
  val _ = print ("Time: " ^ Time.toString t ^ "s\n")
in () end

fun main () = let
  val args = CommandLine.arguments ();
  val _ = print ("Reading graph ...");
  val G = create_graph ()
  val _ = print ("Done\n");
in 
  case args of 
      ["fun"] => measure 5 (bm_fun G)
    | ["funs"] => measure 5 (bm_funs G)
    | ["imp"] => measure 5 (bm_imp G)
    | ["imps"] => measure 5 (bm_imps G)
    | _ => print "Usage: NDFS_Benchmark {fun|funs|imp|imps}"
end

val _ = if MLton.isMLton then main() else ()
