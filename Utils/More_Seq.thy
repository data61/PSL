(* This file contains useful functions defined on Seq.seq that do not appear the Isabelle source
 * code.
 * This file does not have significant duplication with the Isabelle source code. *)
theory More_Seq
imports Main
begin

ML{* signature SEQ2 =
sig
  val mk_pairs   : ('a -> 'b Seq.seq) * 'c -> 'a -> 'd -> ('c * ('b * 'd)) Seq.seq;
  val map_arg    : 'a -> ('a -> 'b) Seq.seq -> 'b Seq.seq;
  val pairs      : 'a Seq.seq -> 'b Seq.seq -> ('a * 'b) Seq.seq;
  val foldr      : ('a * 'b -> 'b) -> 'b -> 'a Seq.seq -> 'b;
  val foldr1     : ('a * 'a -> 'a) ->       'a Seq.seq -> 'a;
  val seq_number : 'a Seq.seq -> (int * 'a) Seq.seq;
  val same_seq   : ('a * 'a -> bool) -> 'a Seq.seq * 'a Seq.seq -> bool;
  val powerset   : 'a Seq.seq -> 'a Seq.seq Seq.seq;
end;
*}

ML{* structure Seq2 : SEQ2 =
struct

  open Seq;

  fun mk_pairs ((func, logs):(('a -> 'b seq) * 'c)) goal ctxt =
    let
      val seq   = func goal
      val pairs = map (fn x => (logs, (x, ctxt))) seq
    in 
      pairs
    end;

  fun map_arg para funcs = case pull funcs of
    NONE => empty
  | SOME (func, funcs_tl) => cons (func para) (map_arg para funcs_tl);

  fun pairs (seq1:'a seq) (seq2:'b seq) = case pull seq1 of
    NONE        => empty
  | SOME (x,xs) => cons (pair x (hd seq2)) (pairs xs (tl seq2)) : ('a * 'b) seq;

  fun foldr f b xs = case pull xs of
    NONE         => b
  | SOME (y, ys) => f (y, foldr f b ys);

  fun foldr1 func sq = case Seq.pull sq of
    NONE   => error "Empty seq in foldr1."
  | SOME _ =>
    let
      fun itr_seq st = case Seq.pull st of
        NONE                => error "Empty seq."
      | SOME (st_hd, st_tl) => case Seq.pull st_tl of
          NONE => st_hd
        | SOME _ => func (st_hd, itr_seq  st_tl)
    in
      itr_seq sq
    end;
  
  fun seq_number (xs:'a seq) : (int * 'a) seq =
    let
      fun seq_number' (xs : 'a seq) (n:int) (ys : (int * 'a) seq) = case pull xs of
        NONE              => ys : (int * 'a) seq
      | SOME (x:'a, tail) => 
         if   n < 0 then error "seq_number' in Utils failed. negative index!"
         else seq_number' tail (n + 1) ((append  ys (single (n, x))) : (int * 'a) seq);
    in
      seq_number' xs 0 Seq.empty
    end;
  
  (* For "same_seq test (xs, ys)" to be true, they have to be of the same length. *)
  fun same_seq (are_same : (('a * 'a) -> bool)) (xs : 'a seq,  ys : 'a seq) : bool = case pull xs of
    NONE => (case pull ys of 
      NONE   => true
    | SOME _ => false)
  | SOME (x, _) => (case pull ys of
      NONE   => false
    | SOME (y, _) => are_same (x, y) andalso same_seq are_same (tl xs, tl ys));

  (* Starts from smaller sets. *)
  fun powerset (xs:'a seq) =
    let
      fun poset (ys, base) = case pull ys of
        NONE => single base
      | SOME (head, tail) => append (poset (tail, base)) (poset (tail, cons head base))
    in
      poset (xs, empty)
    end;
end;
*}

end