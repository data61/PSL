structure Heapmap = struct

  type T = {
    pq : int array,
    qp : int array,
    values : int array,
    N : int
  }

  fun empty N = {
    pq = Array.array (N, 0),
    qp = Array.array (N, ~1),
    values = Array.array (N, 0),
    N = 0
  }
  
  fun val_of (h:T) i = let
    val i = i - 1;
    val k = Array.sub (#pq h,i)
    val v = Array.sub (#values h,i)
  in v end
  
  fun xchg (h:T) i j = let
    val i = i - 1;
    val j = j - 1;
  
    val ki = Array.sub (#pq h,i)
    val kj = Array.sub (#pq h,j)
    val _ = Array.update (#pq h, i, kj)
    val _ = Array.update (#pq h, j, ki)
    val _ = Array.update (#qp h, ki, j)
    val _ = Array.update (#qp h, kj, i)
  in
    h
  end
  
  fun swim h i = let
    fun sr 1 = ()
      | sr i = if val_of h (i div 2) > val_of h i then (xchg h (i div 2) i; sr (i div 2)) else ()
  
  in 
    sr i
  end
  
  fun sink h i = let
    val N = #N h
  
    fun sr i = 
      if 2*i <= N then let
        val j = 2*i;
        val j = if j<N andalso val_of h j > val_of h (j+1) then j+1 else j
        val _ = 
          if val_of h i > val_of h j then 
            (xchg h i j; sr j)
          else ()
      in () end  
      else ()
  
  in
    sr i
  end
  
  
  fun updN (h:T) N : T = {pq = #pq h, qp = #qp h, values = #values h, N = N}
  
  fun insert (h:T) k v = let
    val N = #N h + 1
    
    val _ = Array.update (#pq h,N - 1,k)
    val _ = Array.update (#qp h,k,N)
    val _ = Array.update (#values h,k,v)
    
    val h = updN h N;
    
    val _ = swim h N
  in
    h
  end
  
  fun change (h:T) k v = let
    val _ = Array.update (#values h,k,v)
    val i = Array.sub (#qp h,k)
    val _ = swim h i
    val _ = sink h i
  in
    h
  end
  
  fun pop_min (h:T) = let
    val k = Array.sub (#pq h,0)
    val v = Array.sub (#values h,k)
    val N = #N h
    val _ = xchg h 1 N
    val N = N - 1
    val _ = Array.update (#qp h,k,~1)
    
    val h = updN h N
    
    val _ = sink h 1
  in
    (h,(k,v))
  end

  
  fun rrand s =
    Word32.andb (Word32.+ (Word32.* (s, Word32.fromLargeInt (IntInf.toLarge (1103515245 : IntInf.int))), Word32.fromLargeInt (IntInf.toLarge (12345 : IntInf.int))),
      Word32.fromLargeInt (IntInf.toLarge (2147483647 : IntInf.int)));

  fun rand s m =
    let
      val sa = rrand s;
      val r = Word32.toInt sa;
      val a = IntInf.toInt( IntInf.fromInt(r) * IntInf.fromInt(m) div (2147483648 : IntInf.int) );
    in
      (sa, a)
    end;
  
  
  fun rpt i N f s = 
    if i<N then 
      rpt (i+1) N f (f s i)
    else s  


  fun testsuite N = let
    fun tinsert (h:T,s:Word32.word) i = let
      val (s,v) = rand s (N div 2)
      val h = insert h i v 
    in 
      (h, s)
    end
  
    fun tchange (h,s) i = let
      val (s,v) = rand s (N div 2)
      val h = change h i v
    in 
      (h, s)
    end
  
    fun tpopmin h i = let
      val (h,_) = pop_min h
    in  
      h
    end  
  
    val h = empty N
    
    val (h,s) = rpt 0 N tinsert (h,Word32.fromInt 1)
    (*val (h,s) = rpt 0 N tchange (h,s)
    val h = rpt 0 N tpopmin h*)

  in 
    ()  
  end
  
  
  
  
end



local        
  fun iterate_aux 0 t _ = (print "\n"; t)
    | iterate_aux n t f = let
        val _ = MLton.GC.collect ();
        val _ = MLton.GC.unpack ();   
        
        val _ = print (Int.toString n)
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
    val t = Time.fromNanoseconds (Time.toNanoseconds t div (IntInf.fromInt n))
  in t end  
end

fun do_test_imp n num_iters = let    
  val _ = print "Heapmap Imp\n"
  val t = iterate num_iters (fn _ => Heapmap.testsuite n)
  val _ = print ("Time: " ^ IntInf.toString (Time.toMilliseconds t) ^ "ms\n");
  val _ = print ("Done t = " ^ Time.toString t ^ "s ("^ Int.toString num_iters ^ " iterations\n")
in () end  

fun main () = let
  val args = CommandLine.arguments ();
  val args = map (fn x => (x, Int.fromString x)) args
in
  case args of
    [("imp",_),(_,SOME nn),(_,SOME ni)] => do_test_imp nn ni
  | _ => print ("Invalid command line\n")
end


val _ = if MLton.isMLton then main() else ()
















