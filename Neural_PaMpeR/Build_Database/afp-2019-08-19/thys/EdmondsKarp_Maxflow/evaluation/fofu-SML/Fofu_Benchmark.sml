open Fofu

structure Profile = MLton.Profile

val profData = Profile.Data.malloc ()

exception FAILED

fun fail msg = (print (msg ^ "\n"); raise FAILED)

fun 
  the_fail NONE msg = fail msg
| the_fail (SOME x) msg = x



fun readList (infile : string) = let
  val ins = TextIO.openIn infile
  fun loop ins =
   case TextIO.inputLine ins of
      NONE      => []
    | SOME line => line :: loop ins
in
  let 
    fun parse_integer s = case Int.fromString s of
      SOME i => i
    | NONE => fail ("Expected integer, but got '" ^ s ^"'")  

    val parse_int = Int_of_integer o parse_integer
    val parse_nat = nat_of_integer o parse_integer

    val tokenize = String.tokens (fn c => c = #" ")
    
    fun parse_edge s = let
      val l = tokenize s
    in
      case l of 
        [u,v,c] => (parse_nat u, (parse_nat v, parse_int c))
      | _ => fail ("Expected edge in format 'u v c', but got " ^ s)
    end
    
    fun parse_counts s = let 
      val l = tokenize s
    in
      case l of 
        [numV,numE] => (parse_integer numV, parse_integer numE)
      | _ => fail ("Expected counts in format 'numV numE', but got " ^ s)
    end    


    fun parse_graph (counts :: edges) = (parse_counts counts, map parse_edge edges)
      | parse_graph _ = fail "Empty graph file"
    

    val lines = (loop ins before TextIO.closeIn ins)
    val ((numV,numE),edges) = parse_graph lines
    
    
    (*  
    fun rem_opt i = 
    case i of
      NONE   => nat_of_integer (0)
    | SOME x => nat_of_integer (x) 

    fun rem_opti i = 
    case i of
      NONE   => Int_of_integer (0)
    | SOME x => Int_of_integer (x) 
    
    fun line_parse lines = 
     case lines of
        []        => []
      | (l :: ls) => let val toks = ((String.tokens (fn c => c = #" ")) l)
        in
          (rem_opt (Int.fromString(hd toks)),
           (rem_opt (Int.fromString(hd (tl toks))),
           rem_opti (Int.fromString(hd (tl (tl toks)))))) :: line_parse ls 
        end 
    *)      
  in
    (numV,edges)
  end
end





fun the (SOME x) = x

local        
  fun measure f = let
    val _ = MLton.GC.collect ();
    val _ = MLton.GC.unpack ();   
    val ts = Time.now ()
    val raw_res = Profile.withData (profData,f)
    val ts = Time.- (Time.now (), ts) 
  in (ts,raw_res) end  

  fun iterate n t f = let
      val _ = print (IntInf.toString n)
      val (ts, raw_res) = measure f
      val t = Time.+ (t,ts)
      val _ = print ("(" ^ Time.toString ts ^ "s). ")
    in 
      if n>1 then 
        iterate (n-1) t f
      else  
        (t,raw_res)
    end
  
in  
  fun measure n { prepare, run, compres } = let
    val _ = print ("Netcheck ...");
    val G = prepare ()  
    val G = the_fail G "Failed"
    val _ = print ("Done\n");
    
    val _ = print ("Fofu ");
    val (t,res) = iterate n Time.zeroTime (run G)
    val t = Time.fromNanoseconds (Time.toNanoseconds t div n)
    val res = compres res
    val _ = print ("\n");
    val _ = print ("@@@max-flow: " ^ res ^ "\n");
    val _ = print ("@@@time: " ^ IntInf.toString (Time.toMilliseconds t) ^ " ms\n")
    
  in () end

end


fun fofu_fun s t G = let
  val s = nat_of_integer s
  val t = nat_of_integer t
in
  {
    prepare = fn () => let 
      val (c,(ps,N)) = the_fail (prepareNet G s t) "prepareNet failed";
      val (ci,psi) = edka_imp_tabulate c N ps ()
    in
      SOME (c,ci,ps,psi,N)
    end  ,
    run = fn (c,ci,ps,psi,N) => fn () => (N,c,ps,edka_imp_run s t N ci psi ()),
    compres = fn (N,c,ps,f) => let
        val flow = compute_flow_val_imp c s t ps f ()
      in
        IntInf.toString (integer_of_int flow) 
      end  
  }
end



fun main () = let
  val args = CommandLine.arguments ();
  
  fun perform s t G = (
    measure 1 (fofu_fun s t G);
    print ("stat_outer_c = " ^ IntInf.toString (!stat.outer_c) ^ "\n");
    print ("stat_inner_c = " ^ IntInf.toString (!stat.inner_c) ^ "\n");
    Profile.Data.write(profData,"mlmon.prof.out");
    Profile.Data.free(profData)
  )
  
in 
  case args of 
    [s,t,gname] => let
      val s = the (Int.fromString s)
      val t = the (Int.fromString t)
      val (_,G) = readList gname
    in  
      perform s t G
    end
  | [gname] => let
      val (N,G) = readList gname
      val s = 0
      val t = N - 1
    in    
      perform s t G
    end
    | _ => print "Usage: Fofu [<s> <t>] <file-name>\n  If s and t not specified, nodes 0 and |V|-1 are taken."
end

val _ = if MLton.isMLton then main() else ()
