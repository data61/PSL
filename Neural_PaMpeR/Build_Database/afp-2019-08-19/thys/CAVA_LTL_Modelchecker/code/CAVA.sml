(* set up *)
structure SC = SyntaxConverter(PromelaAST)
structure PromelaLtl = Ltl(PromelaLtl)
structure BPLtl = Ltl(BPLtl)

(* Auxiliaries *)
fun fst (x,y) = x
fun snd (x,y) = y
fun println x = print (x ^ "\n")
fun printlnErr x = (TextIO.output (TextIO.stdErr, x ^ "\n");
  TextIO.flushOut TextIO.stdErr)
val realStr = Real.fmt (StringCvt.FIX (SOME 2))
fun ratio x y = realStr(real x / real y * 100.0) ^ "%"
val nat_to_charlist = String.explode o Arith.nat_to_string
val int_to_charlist = String.explode o IntInf.toString

(* Print stuff *)
fun print_time t num =
  let
    val time = real t / 1000.0
    val ps = real num / time
  in
    println("Time used: " ^ realStr time ^ "s");
    println("States per s: " ^ realStr ps)
  end

fun print_list f sep s = 
    let 
        fun f' (s, str) = if str = "" then f s else str ^ sep ^ f s
    in "[" ^ (foldl f' "" s) ^ "]"
    end

fun print_vis_size visited = 
  let
    val size = CAVA_Support.objSize visited
    val sizeKB = real size / 1024.0
  in
    println("Size of the visited set: " ^ realStr sizeKB ^"KB")
  end

fun print_state_size i =
    println("Size of one state: " ^ IntInf.toString (CAVA_Support.objSize i) ^"B")

fun print_memory_size num =
  let 
    val size = CAVA_Support.max_rss ()
    val perS = real size / real (Arith.of_nat num)
    val sizeMB = real size / 1024.0
  in
    println("Maximum heap size: " ^ realStr sizeMB ^ "MB");
    println("Heap per State: " ^ realStr perS ^ "KB")
  end


fun write_dot_graph os (V,(V0,E)) =
let 
   val _ = TextIO.output (os, "digraph {\n")
   val _ = TextIO.output (os, "rankdir=LR;\n")
   val _ = TextIO.output (os, "\"\" [shape=none];\n")

   fun pr_node n = 
     "\"" ^ Arith.nat_to_string n ^ "\""
   (*fun get_node_shape f =
      if f then "doublecircle" else "circle"*)
   fun get_node_format _ = ("shape = circle")
   fun output_node n =
     TextIO.output (os, pr_node n ^ " ["^get_node_format n^"];\n")
   fun output_initial_node n =
      (TextIO.output (os, String.concat [
          "\"\" -> ", pr_node n, ";\n"]))
   val _ = map output_node V;
   val _ = map output_initial_node V0;

   fun output_edge (q0, q1) =
      (TextIO.output (os, String.concat [
          pr_node q0, " -> ", pr_node q1, ";\n"]))
   val _ = map output_edge E;
   val _ = TextIO.output (os, "}\n");   
in
   ()
end


datatype show_buchi = NoShow | Show | PDF of string

fun buchi_stats show_buchi phi =
  let
    val phi' = Rewriting.simplify IsaArith.equal_nat Rewriting.Slow (LTL.ltlc_to_ltln phi);
    val gba = LTL_to_GBA_impl.create_name_gba_code (IsaArith.equal_nat, IsaArith.linorder_nat) phi'
    val export = CAVA_Impl.frv_export_code (fn a => fn b => a=b) gba

    fun show opts =
      let
        val proc = Unix.execute ("/usr/bin/dot", opts)
        val os = Unix.textOutstreamOf proc
      in
        write_dot_graph os export;
        TextIO.closeOut os
      end
  in
    case show_buchi of
         Show => show ["-Tx11"]
       | PDF f => show ["-Tpdf", "-o"^f]
       | NoShow => ()
  end

  
(* Main part *)
fun bp_cava cfg (prog, phi) = fn () => CAVA_Impl.cava_bpc cfg prog phi

fun promela_cava cfg (prog, phi) = fn () => CAVA_Impl.cava_promela cfg prog phi

fun print_lasso (prints : 'a option -> 'a -> string) (pr : 'a list) (pc : 'a list) =
  let
    fun print_lasso_list ls start idx =
      let
        fun p (q1,(q2,idx)) = (
          println(IntInf.toString idx ^ ": " ^ prints q2 q1);
          (SOME q1,idx+1))
      in
        foldl p (start,idx) ls
      end

    val (last_reach, reach_idx) = (
      println("\nREACH: ");
      print_lasso_list pr NONE 1)
  in
    println("\nLOOP: ");
    print_lasso_list pc last_reach reach_idx;
    println ""
  end

fun measure_cava phi
  (cava : unit -> ('a, 'b) Lasso.lasso_ext option option) 
  (prints : 'a option -> 'a -> string)
  show_buchi =
  let
    (*val _ = CAVA_Statistics.init ();*)
    val st = Time.now()
    val res = cava ()
    val td = (Time.- (Time.now(), st))
  in
    case res of
        NONE => println("OK: Program satisfies formula")
      | SOME NONE => println("ERROR: Program does NOT satisfy formula. Checker did not return counterexample.")
      | SOME (SOME lasso) => (
        let
            val pr = Lasso.lasso_reach lasso
            val pc = Lasso.lasso_cycle lasso
        in
            println("ERROR: Program does NOT satisfy formula");
            print_lasso prints pr pc;
            println("CE Summary: (|pr|,|pc|) = (" 
                    ^ IntInf.toString (length pr) ^ ", " ^ IntInf.toString (length pc) ^ ")")
        end
        );

    println ("Overall time: " ^ Time.toString td ^ "s");

    println (Statistics.pretty_stats (Statistics.get_active_stats ()));

    (*let
      val phi' = (LTL_Rewrite.ltln_rewrite IsaArith.equal_nat (LTL.ltl_to_ltln (LTL.ltl_pushneg (LTL.ltlc_to_ltl phi))));
      val gba = LTL_to_GBA_impl.create_name_gba_code (IsaArith.equal_nat, IsaArith.linorder_nat) phi'
      val (nodes,(v0,E)) = CAVA.frv_export_code (fn a => fn b => a=b) gba
      fun print_edge (a,b) = Arith.nat_to_string a ^ " -> " ^ Arith.nat_to_string b
    in
      println (print_list Arith.nat_to_string "," nodes);
      println (print_list Arith.nat_to_string "," v0);
      println (print_list (print_edge) "," E);
      ()
    end;*)
    
    (* Print buchi stats *)
    (*println "";*)
    (*buchi_stats show_buchi phi;*)
    
    ()
  end

exception PreprocessError

fun preprocess args prog =
  let
    val opts = List.rev (List.map (fn d => "-D" ^ d) args)
    val proc = Unix.execute ("/usr/bin/cpp", ("-P"::opts) @ [prog])
    val is = Unix.textInstreamOf proc
    fun getString ins = case TextIO.inputLine ins of
                             SOME line => line ^ getString ins
                           | NONE => ""
    val progS = getString is
    val ex = Unix.fromStatus (Unix.reap proc)
  in
    case ex of
         Unix.W_EXITED => progS
       | _ => raise PreprocessError
  end

fun promela_get_params progF ltl fromFile fromPromela cppargs =
  let
    val progS = preprocess cppargs progF
    val _ = PromelaStatistics.start_parse()
    val ast = List.map SC.convert (PromelaParser.stringParse progS)
    val phi = fn _ => 
        let 
          val phi = if fromFile then PromelaLtl.compile_from_file ltl
                    else if fromPromela then 
                      (case Promela.lookupLTL ast ltl of 
                            SOME p => PromelaLtl.compile_from_string p
                          | NONE => raise PromelaLtl.LtlError ("No formula named '" ^ ltl ^ "'"))
                    else PromelaLtl.compile_from_string ltl
        in
           println "Chosen LTL-formula:";
           println(PromelaLtl.toString phi);
           PromelaLTLConv.ltl_conv phi
        end
  in
     (ast,phi ())
  end


fun bp_get_params p n ltl fromFile =
  let
    val pre_phi = if fromFile then BPLtl.compile_from_file ltl 
                  else BPLtl.compile_from_string ltl
    val (descr, (_, (prog, (consts, funs)))) = BoolProgs_Programs.chose_prog p n
    val phi = BoolProgs_LTL_Conv.ltl_conv consts funs pre_phi
  in
    case phi of
         Sum_Type.Inl p => (
           println("Running Program \"" ^ descr ^"\"");
           println "Chosen LTL-formula:";
           println(BPLtl.toString pre_phi);
           println "";
           ((prog, p),p))
       | Sum_Type.Inr s => raise BPLtl.LtlError s
  end

fun usage () =
  let
    open BoolProgs_Programs
  in
    println ("Usage:");
    println (CommandLine.name()^" [--pdf file|--show] [--ce-algo algo] [prog] size [-f file | ltl]\n");
    println (CommandLine.name()^" [--pdf file|--show] [--ce-algo algo] [-n n] [-D X=y] promela_file [-f file | ltl | -N name]\n");
    println ("--ce-algo algo   Specify algorithm for counterexample search. Default: scc");
    println ("    ndfs         Nested depth first search, HPY-optimization and early cycle detection.");
    println ("    scc          SCC-based, using Gabow's algorithm on GBAs");

    println ("--pdf file       print the GBA generated from the LTL-formula to file");
    println ("--show           Show the GBA generated from the LTL-formula");
    
    println ("\nThe first variant checks a builtin boolean program against the given LTL formula.");
    println ("    prog can be any of:");
    List.app (fn (k,(d,n)) => 
      println ("        '" ^ k ^ "' --> " ^ d
               ^ " (size = " ^ n ^ ")"))
      list_progs;
    println ("        default: " ^ default_prog);
    println ("    -f file      Read LTL-formula from file");
    

    println ("\nThe second variant checks a Promela model against the given LTL formula.");
    println ("    -D X=y       Preprocessor definition.");
    println ("    -n n         Shortcut for '-D N=n'.");
    println ("    -f file      Read LTL-formula from file");
    println ("    -N name      Use LTL formula specified in the model.");

    println ("\nIf no LTL formula is given, it defaults to 'G true'. This corresponds to complete state-graph exploration.")
  end

fun explain p =
  let
    val (descr, (ndescr, (_, (consts, funs)))) = BoolProgs_Programs.chose_prog p (Arith.nat 2)
  in
    println descr;
    println ("Size = " ^ ndescr);
    println ("\nConstants:");
    List.app (fn k =>
        println("  - " ^ k))
        (BoolProgs_Programs.keys_of_map consts);
    println ("\nFunctions:");
    List.app (fn k =>
        println("  - " ^ k))
        (BoolProgs_Programs.keys_of_map funs)
  end

exception ArgumentError of string;

fun parse_args args show cfg cppargs parseonly =
  let
    val default_ltl = "G true"
    fun is_pml_file f = not (List.null cppargs) orelse (OS.FileSys.access (f,[]))

    fun run_bp prog numStr ltl fromFile =
      case IntInf.fromString numStr of
          NONE => explain prog
        | SOME n => 
          if n <= 0 then 
              raise ArgumentError "Size <=0 not allowed."
          else 
            let val (params,phi) = bp_get_params prog (Arith.nat n) ltl fromFile
                fun print_graphq _ q = HOLString.implode (BoolProgs.print_config (HOLString.explode o Arith.nat_to_string) (HOLString.explode o IntInf.fmt StringCvt.HEX) q)
            in measure_cava phi (bp_cava cfg params) print_graphq show end

    fun run_promela prog ltl fromFile fromPromela =
      let val (ast, phi) = promela_get_params prog ltl fromFile fromPromela cppargs
          fun print_config q1 q2 = HOLString.implode (Promela.printConfigFromAST (HOLString.explode o IntInf.toString) ast q1 q2)
          fun print_prog p = (
            println("\nRunning Program \"" ^ prog ^"\"");
            List.app (println o HOLString.implode) (Promela.printProcesses (HOLString.explode o IntInf.toString) p)
            )
      in if not parseonly then
           measure_cava phi (promela_cava (cfg,print_prog) (ast,phi)) print_config show
         else ()
      end
  in
    case args of
     [] => raise ArgumentError ""
    | ["-h"] => usage()
    | ["--help"] => usage()
    | "--parse-only"::xs => parse_args xs show cfg cppargs true   (* For debugging only *)
    | "--show" :: xs => parse_args xs Show cfg cppargs parseonly
    | "--pdf" :: f :: xs => parse_args xs (PDF f) cfg cppargs parseonly
    | "-n" :: n :: xs => parse_args ("-D" :: "N=" ^ n :: xs) show cfg cppargs parseonly
    | ["-D"] => raise ArgumentError "missing Preprocessor option"
    | "-D" :: d :: xs => parse_args xs show cfg (d :: cppargs) parseonly
    | "--ce-algo" :: n :: xs => 
      let
          val (l2b,(int,ce)) = cfg
          val ce = 
              case n of 
                (*  "ndfs" => CAVA.CFG_CE_NDFS
                | "ndfs_hash" => CAVA.CFG_CE_NDFS_HASH
                | "ndfs_ahs" => CAVA.CFG_CE_NDFS_AHS
                | "scc" => CAVA.CFG_CE_SCC
                | "nndfs" => CAVA.CFG_CE_NNDFS*)
                  "ndfs" => CAVA_Impl.CFG_CE_NDFS
                | "scc" => CAVA_Impl.CFG_CE_SCC_GABOW
                | _ => raise ArgumentError ("Unknown ce algorithm: " ^ n)
          val cfg = (l2b,(int,ce))
      in
          parse_args xs show cfg cppargs parseonly
      end
    | x :: xs => 
        if String.isPrefix "-" x then raise ArgumentError ("Unknown argument: " ^ x)
        else (case xs of
            [] => (case IntInf.fromString x of
                        NONE => 
                          if is_pml_file x then run_promela x default_ltl false false
                          else run_bp x "" default_ltl false
                      | SOME _ => run_bp "" x default_ltl false)
          | ["-f"] => raise ArgumentError "no file specified"
          | ["-N"] => raise ArgumentError "no ltl name specified"
          | [y]=> (case IntInf.fromString x of
                        NONE => 
                          if is_pml_file x then run_promela x y false false
                          else run_bp x y default_ltl false
                      | SOME _ => run_bp "" x y false)
          | [y, "-f"] => raise ArgumentError "no file specified"
          | ["-f", f] => if is_pml_file x then run_promela x f true false
                         else run_bp "" x f true
          | ["-N", y] => run_promela x y false true
          | [num, ltl] => run_bp x num ltl false
          | [num, "-f", f] => run_bp x num f true
          | _ => raise ArgumentError "Too many arguments"
        )
  end

fun main () =
  let 
    val e = fn () => OS.Process.exit (OS.Process.failure)
    val u = fn () => (usage (); e())
  in 
    parse_args (CommandLine.arguments ()) NoShow CAVA_Impl.dflt_cfg [] false
    handle ArgumentError msg => if msg = "" then u ()
                                else (printlnErr ("Error in arguments: " ^ msg ^ "\n"); u ())
         | PromelaLtl.LtlError msg => (printlnErr ("LTL Error: " ^ msg); e())
         | BPLtl.LtlError msg => (printlnErr ("LTL Error: " ^ msg); e())
         | PromelaParser.ParseException msg => 
             (printlnErr ("Parsing Error: " ^ msg); e())
         | PromelaUtils.UnsupportedConstruct msg =>
             (printlnErr ("Unsupported Construct: " ^ msg); e())
         | PromelaUtils.StaticError msg =>
             (printlnErr ("Static Promela Error: " ^ msg); e())
         | PromelaUtils.RuntimeError msg =>
             (printlnErr ("Promela Runtime Error: " ^ msg); e())
  end

val _ = if CAVA_Support.isMLton then main() else ()
