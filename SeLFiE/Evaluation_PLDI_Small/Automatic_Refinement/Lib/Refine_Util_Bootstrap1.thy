theory Refine_Util_Bootstrap1
imports Main
begin
ML \<open>
  infix 1 ##

  signature BASIC_REFINE_UTIL = sig
    val map_option: ('a -> 'b) -> 'a option -> 'b option

    val map_fold: ('a -> 'b -> 'c * 'b) -> 'a list -> 'b -> 'c list * 'b

    val split: ('a -> bool) -> 'a list -> 'a list * 'a list
    val split_matching: ('a -> 'b -> bool) -> 'a list -> 'b list -> ('b list * 'b list) option

    val yield_singleton2: ('a list -> 'b -> ('c * 'd list) * 'e) -> 'a -> 'b ->
      ('c * 'd) * 'e

    val ## : ('a -> 'c) * ('b -> 'd) -> ('a * 'b) -> ('c * 'd)

    val seq_is_empty: 'a Seq.seq -> bool * 'a Seq.seq

  end

  structure Basic_Refine_Util : BASIC_REFINE_UTIL = struct
    fun map_option _ NONE = NONE
      | map_option f (SOME x) = SOME (f x)

    fun map_fold _ [] s = ([],s)
      | map_fold f (x::xs) s = 
        let 
          val (x',s') = f x s
          val (xs',s') = map_fold f xs s'
        in
          (x'::xs',s')
        end


    fun yield_singleton2 f x y = case f [x] y of
      ((r1,[r2]),r3) => ((r1,r2),r3)
    | _ => error "INTERNAL: yield_singleton2"

    fun (f ## g) (a,b) = (f a, g b)
  
    fun seq_is_empty seq = case Seq.pull seq of
      NONE => (true, seq)
    | SOME (a,seq) => (false, Seq.cons a seq)

      fun split P l = (filter P l, filter_out P l)

      fun split_matching R xs ys = let
        exception EXC
    
        fun fs _ [] = raise EXC
          | fs x (y::ys) = 
              if R x y then (y,ys) 
              else let val (y',ys) = fs x ys in (y',y::ys) end
    
        fun fm [] ys = ([],ys)      
          | fm (x::xs) ys = let
              val (y,ys) = fs x ys
              val (ys1,ys2) = fm xs ys
            in
              (y::ys1,ys2)
            end
      in
        try (fm xs) ys
      end

  end

  open Basic_Refine_Util
\<close>  




end
