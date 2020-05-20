(* Modified by Frédéric Tuong
 * Isabelle/C
 * (c) 2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
 *)
(* ML-Yacc Parser Generator (c) 1989 Andrew W. Appel, David R. Tarditi *)

(* Stream: a structure implementing a lazy stream.  The signature STREAM
   is found in base.sig *)

structure Stream1 : STREAM1 =
struct
  datatype ('a, 'b) stream = Source of {buffer: 'a list, drain: 'b -> 'a * 'b}

  fun streamify drain = pair (Source {buffer = [], drain = drain})

  fun get (Source {buffer = [], drain}, info) =
        let val (x, info') = drain info
        in (x, (Source {buffer = [], drain = drain}, info')) end
    | get (Source {buffer = x :: buffer, drain}, info) =
            (x, (Source {buffer = buffer, drain = drain}, info))

  fun cons (x, (Source {buffer, drain}, info)) =
    (Source {buffer = x :: buffer, drain = drain}, info)
end;

structure Stream2 : STREAM2 =
struct
   open Unsynchronized

   datatype 'a str = EVAL of 'a * 'a str ref | UNEVAL of (unit->'a)

   type 'a stream = 'a str ref

   fun get(ref(EVAL t)) = t
     | get(s as ref(UNEVAL f)) =
            let val t = (f(), ref(UNEVAL f)) in s := EVAL t; t end

   fun streamify f = ref(UNEVAL f)
   fun cons(a,s) = ref(EVAL(a,s))

end;
