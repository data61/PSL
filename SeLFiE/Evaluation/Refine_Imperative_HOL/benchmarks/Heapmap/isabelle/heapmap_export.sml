
structure Uint : sig
  val set_bit : Word.word -> IntInf.int -> bool -> Word.word
  val shiftl : Word.word -> IntInf.int -> Word.word
  val shiftr : Word.word -> IntInf.int -> Word.word
  val shiftr_signed : Word.word -> IntInf.int -> Word.word
  val test_bit : Word.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word.orb (x, mask)
     else Word.andb (x, Word.notb mask)
  end

fun shiftl x n =
  Word.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word.andb (x, Word.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word.fromInt 0

end; (* struct Uint *)

(* Test that words can handle numbers between 0 and 31 *)
val _ = if 5 <= Word.wordSize then () else raise (Fail ("wordSize less than 5"));

structure Uint32 : sig
  val set_bit : Word32.word -> IntInf.int -> bool -> Word32.word
  val shiftl : Word32.word -> IntInf.int -> Word32.word
  val shiftr : Word32.word -> IntInf.int -> Word32.word
  val shiftr_signed : Word32.word -> IntInf.int -> Word32.word
  val test_bit : Word32.word -> IntInf.int -> bool
end = struct

fun set_bit x n b =
  let val mask = Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))
  in if b then Word32.orb (x, mask)
     else Word32.andb (x, Word32.notb mask)
  end

fun shiftl x n =
  Word32.<< (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr x n =
  Word32.>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun shiftr_signed x n =
  Word32.~>> (x, Word.fromLargeInt (IntInf.toLarge n))

fun test_bit x n =
  Word32.andb (x, Word32.<< (0wx1, Word.fromLargeInt (IntInf.toLarge n))) <> Word32.fromInt 0

end; (* struct Uint32 *)


structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a

fun grow (aref, i, x) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x)
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

end;

end;

structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;

  fun grow (aref, inc, x) = case aref of
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x)
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:IntInf.int) = array (IntInf.toInt n, a);

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:IntInf.int) (x:'a) = grow (a, IntInf.toInt i, x);

fun array_shrink (a:'a ArrayType) (sz:IntInf.int) = shrink (a,IntInf.toInt sz);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;





   fun array_blit src si dst di len = (
      src=dst andalso raise Fail ("array_blit: Same arrays");
      ArraySlice.copy {
        di = IntInf.toInt di,
        src = ArraySlice.slice (src,IntInf.toInt si,SOME (IntInf.toInt len)),
        dst = dst})

    fun array_nth_oo v a i () = Array.sub(a,IntInf.toInt i) handle Subscript => v | Overflow => v
    fun array_upd_oo f i x a () = 
      (Array.update(a,IntInf.toInt i,x); a) handle Subscript => f () | Overflow => f ()



structure Bits_Integer : sig
  val set_bit : IntInf.int -> IntInf.int -> bool -> IntInf.int
  val shiftl : IntInf.int -> IntInf.int -> IntInf.int
  val shiftr : IntInf.int -> IntInf.int -> IntInf.int
  val test_bit : IntInf.int -> IntInf.int -> bool
end = struct

val maxWord = IntInf.pow (2, Word.wordSize);

fun set_bit x n b =
  if n < maxWord then
    if b then IntInf.orb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n)))
    else IntInf.andb (x, IntInf.notb (IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))))
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

fun shiftl x n =
  if n < maxWord then IntInf.<< (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun shiftr x n =
  if n < maxWord then IntInf.~>> (x, Word.fromLargeInt (IntInf.toLarge n))
  else raise (Fail ("Shift operand too large: " ^ IntInf.toString n));

fun test_bit x n =
  if n < maxWord then IntInf.andb (x, IntInf.<< (1, Word.fromLargeInt (IntInf.toLarge n))) <> 0
  else raise (Fail ("Bit index too large: " ^ IntInf.toString n));

end; (*struct Bits_Integer*)

structure Heapmap : sig
  type nat
  type num
  val integer_of_nat : nat -> IntInf.int
  type ('a, 'b) lp
  type ('b, 'a) fingerTree
  val nat_of_integer : IntInf.int -> nat
  val testsuite : nat -> (unit -> unit)
  val ftestsuite : nat -> unit
end = struct

datatype typerepa = Typerep of string * typerepa list;

datatype nat = Nat of IntInf.int;

datatype 'a itself = Type;

fun typerep_nata t = Typerep ("Nat.nat", []);

type 'a typerep = {typerep : 'a itself -> typerepa};
val typerep = #typerep : 'a typerep -> 'a itself -> typerepa;

type 'a countable = {};

type 'a heap = {countable_heap : 'a countable, typerep_heap : 'a typerep};
val countable_heap = #countable_heap : 'a heap -> 'a countable;
val typerep_heap = #typerep_heap : 'a heap -> 'a typerep;

val countable_nat = {} : nat countable;

val typerep_nat = {typerep = typerep_nata} : nat typerep;

val heap_nat = {countable_heap = countable_nat, typerep_heap = typerep_nat} :
  nat heap;

datatype num = One | Bit0 of num | Bit1 of num;

val one_nata : nat = Nat (1 : IntInf.int);

type 'a one = {one : 'a};
val one = #one : 'a one -> 'a;

val one_nat = {one = one_nata} : nat one;

fun integer_of_nat (Nat x) = x;

fun plus_nata m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

type 'a plus = {plus : 'a -> 'a -> 'a};
val plus = #plus : 'a plus -> 'a -> 'a -> 'a;

val plus_nat = {plus = plus_nata} : nat plus;

val zero_nata : nat = Nat (0 : IntInf.int);

type 'a zero = {zero : 'a};
val zero = #zero : 'a zero -> 'a;

val zero_nat = {zero = zero_nata} : nat zero;

val default_nata : nat = zero_nata;

type 'a default = {default : 'a};
val default = #default : 'a default -> 'a;

val default_nat = {default = default_nata} : nat default;

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype ('a, 'b) lp = Infty | LP of 'a * 'b;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun max A_ a b = (if less_eq A_ a b then b else a);

fun p_min A_ B_ Infty Infty = Infty
  | p_min A_ B_ Infty (LP (e, a)) = LP (e, a)
  | p_min A_ B_ (LP (e, a)) Infty = LP (e, a)
  | p_min A_ B_ (LP (e1, a)) (LP (e2, b)) =
    LP (max ((ord_preorder o preorder_order o order_linorder) A_) e1 e2,
         min ((ord_preorder o preorder_order o order_linorder) B_) a b);

fun plus_LPa A_ B_ a b = p_min A_ B_ a b;

fun plus_LP A_ B_ = {plus = plus_LPa A_ B_} : ('a, 'b) lp plus;

fun zero_LPa A_ B_ = Infty;

fun zero_LP A_ B_ = {zero = zero_LPa A_ B_} : ('a, 'b) lp zero;

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

fun semigroup_add_LP A_ B_ = {plus_semigroup_add = plus_LP A_ B_} :
  ('a, 'b) lp semigroup_add;

fun monoid_add_LP A_ B_ =
  {semigroup_add_monoid_add = semigroup_add_LP A_ B_,
    zero_monoid_add = zero_LP A_ B_}
  : ('a, 'b) lp monoid_add;

datatype ('a, 'b) node = Tip of 'a * 'b |
  Node2 of 'b * ('a, 'b) node * ('a, 'b) node |
  Node3 of 'b * ('a, 'b) node * ('a, 'b) node * ('a, 'b) node;

datatype ('a, 'b) digit = Onea of ('a, 'b) node |
  Two of ('a, 'b) node * ('a, 'b) node |
  Three of ('a, 'b) node * ('a, 'b) node * ('a, 'b) node |
  Four of ('a, 'b) node * ('a, 'b) node * ('a, 'b) node * ('a, 'b) node;

datatype ('a, 'b) fingerTreeStruc = Empty | Single of ('a, 'b) node |
  Deep of 'b * ('a, 'b) digit * ('a, 'b) fingerTreeStruc * ('a, 'b) digit;

datatype ('b, 'a) splitres =
  Abs_splitres of
    (('b, 'a) fingerTreeStruc * (('b * 'a) * ('b, 'a) fingerTreeStruc));

datatype ('b, 'a) fingerTree = Abs_FingerTree of ('b, 'a) fingerTreeStruc;

fun id x = (fn xa => xa) x;

fun suc n = plus_nata n one_nata;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

fun len A_ a =
  (fn () => let
              val i = (fn () => IntInf.fromInt (Array.length a)) ();
            in
              nat_of_integer i
            end);

fun new A_ =
  (fn a => fn b => (fn () => Array.array (IntInf.toInt a, b))) o integer_of_nat;

fun nth A_ a n = (fn () => Array.sub (a, IntInf.toInt (integer_of_nat n)));

fun upd A_ i x a =
  (fn () =>
    let
      val _ =
        (fn () => Array.update (a, IntInf.toInt (integer_of_nat i), x)) ();
    in
      a
    end);

fun rep (A1_, A2_, A3_) i n f s =
  (if less A3_ i n
    then (fn () => let
                     val x = f s i ();
                   in
                     rep (A1_, A2_, A3_) (plus A2_ i (one A1_)) n f x ()
                   end)
    else (fn () => s));

fun drep (A1_, A2_, A3_) i n f s =
  (if less A3_ i n then drep (A1_, A2_, A3_) (plus A2_ i (one A1_)) n f (f s i)
    else s);

fun apsnd f (x, y) = (x, f y);

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun fst (x1, x2) = x1;

fun divide_integer k l = fst (divmod_integer k l);

fun divide_nat m n = Nat (divide_integer (integer_of_nat m) (integer_of_nat n));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun nat_of_uint32 x =
  nat_of_integer (IntInf.fromLarge (Word32.toLargeInt x) : IntInf.int);

fun rrand s =
  Word32.andb (Word32.+ (Word32.* (s, Word32.fromLargeInt (IntInf.toLarge (1103515245 : IntInf.int))), Word32.fromLargeInt (IntInf.toLarge (12345 : IntInf.int))),
    Word32.fromLargeInt (IntInf.toLarge (2147483647 : IntInf.int)));

fun rand s m =
  let
    val sa = rrand s;
    val r = nat_of_uint32 sa;
    val a =
      divide_nat (times_nat r m) (nat_of_integer (2147483648 : IntInf.int));
  in
    (sa, a)
  end;

fun snd (x1, x2) = x2;

fun marl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
 end);

fun marl_get A_ = (fn (a, _) => nth A_ a);

fun ial_swap x =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () => let
                  val xa = marl_get heap_nat a1 bia ();
                  val x_a = marl_get heap_nat a1 bi ();
                  val x_b = marl_set heap_nat a1 bia x_a ();
                  val x_c = marl_set heap_nat x_b bi xa ();
                  val x_d = upd heap_nat x_a bia a2 ();
                  val x_e = upd heap_nat xa bi x_d ();
                in
                  (x_c, x_e)
                end)
    end)
    x;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun hm_exch_op_impl A_ =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val x =
            ial_swap a1 (minus_nat bia one_nata) (minus_nat bi one_nata) ();
        in
          (x, a2)
        end)
    end);

fun hm_swim_op_impl_0 A_ B_ prio x =
  let
    val (a1, a2) = x;
    val ((a1b, _), a2a) = a1;
    val (_, b) = a1b;
    val d2 =
      nat_of_integer
        (fst (IntInf.divMod (IntInf.abs (integer_of_nat a2),
               IntInf.abs (2 : IntInf.int))));
  in
    (if less_nat zero_nata d2 andalso less_eq_nat d2 b
      then (fn () =>
             let
               val xa = let
                          val (a, _) = a1b;
                        in
                          nth heap_nat a
                        end
                          (minus_nat d2 (suc zero_nata))
                          ();
               val xb = nth A_ a2a xa ();
               val xaa = let
                           val (a, _) = a1b;
                         in
                           nth heap_nat a
                         end
                           (minus_nat a2 (suc zero_nata))
                           ();
               val xab = nth A_ a2a xaa ();
             in
               (if less_eq ((ord_preorder o preorder_order o order_linorder) B_)
                     (prio xb) (prio xab)
                 then (fn () => a1)
                 else (fn f_ => fn () => f_ ((hm_exch_op_impl A_ a1 a2 d2) ())
                        ())
                        (fn x_g => hm_swim_op_impl_0 A_ B_ prio (x_g, d2)))
                 ()
             end)
      else (fn () => a1))
  end;

fun hm_swim_op_impl A_ B_ prio hm i = hm_swim_op_impl_0 A_ B_ prio (hm, i);

fun hm_sink_op_impl_0 A_ B_ prio x =
  let
    val (a1, a2) = x;
    val (((_, b), _), _) = a1;
  in
    (if less_eq_nat (times_nat (nat_of_integer (2 : IntInf.int)) a2) b
      then let
             val x_d = times_nat (nat_of_integer (2 : IntInf.int)) a2;
             val (a1a, a2a) = a1;
             val (a1aa, _) = a1a;
           in
             (fn () =>
               let
                 val xa =
                   let
                     val (a, _) = a1aa;
                   in
                     nth heap_nat a
                   end
                     (minus_nat x_d (suc zero_nata))
                     ();
                 val xb = nth A_ a2a xa ();
                 val x_g =
                   (if less_nat x_d b
                     then (fn f_ => fn () => f_ ((let
            val (a, _) = a1aa;
          in
            nth heap_nat a
          end
           x_d)
                            ()) ())
                            (fn xaa =>
                              (fn f_ => fn () => f_ ((nth A_ a2a xaa) ()) ())
                                (fn xab =>
                                  (fn () =>
                                    (if less
  ((ord_preorder o preorder_order o order_linorder) B_) (prio xab) (prio xb)
                                      then suc x_d else x_d))))
                     else (fn () => x_d))
                     ();
                 val xc =
                   let
                     val (a, _) = a1aa;
                   in
                     nth heap_nat a
                   end
                     (minus_nat x_g (suc zero_nata))
                     ();
                 val xd = nth A_ a2a xc ();
                 val xaa =
                   let
                     val (a, _) = a1aa;
                   in
                     nth heap_nat a
                   end
                     (minus_nat a2 (suc zero_nata))
                     ();
                 val xab = nth A_ a2a xaa ();
               in
                 (if less ((ord_preorder o preorder_order o order_linorder) B_)
                       (prio xd) (prio xab)
                   then (fn f_ => fn () => f_ ((hm_exch_op_impl A_ a1 a2 x_g)
                          ()) ())
                          (fn x_k => hm_sink_op_impl_0 A_ B_ prio (x_k, x_g))
                   else (fn () => a1))
                   ()
               end)
           end
      else (fn () => a1))
  end;

fun hm_sink_op_impl A_ B_ prio hm i = hm_sink_op_impl_0 A_ B_ prio (hm, i);

fun hm_repair_op_impl A_ B_ prio =
  (fn ai => fn bi => fn () => let
                                val x = hm_sink_op_impl A_ B_ prio ai bi ();
                              in
                                hm_swim_op_impl A_ B_ prio x bi ()
                              end);

fun hm_change_key_op_impl A_ B_ prio k v hm =
  let
    val (((a, b), ba), x2) = hm;
  in
    (fn () => let
                val x = nth heap_nat ba k ();
                val xa = nth heap_nat a x ();
                val xaa = upd A_ xa v x2 ();
              in
                hm_repair_op_impl A_ B_ prio (((a, b), ba), xaa) (suc x) ()
              end)
  end;

fun marl_butlast A_ = (fn (a, n) => (fn () => (a, minus_nat n one_nata)));

fun equal_nat m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

fun hm_pop_min_op_impl A_ B_ prio hm =
  let
    val (((_, b), _), _) = hm;
    val (a1, a2) = hm;
    val (a1a, _) = a1;
  in
    (fn () =>
      let
        val x = let
                  val (a, _) = a1a;
                in
                  nth heap_nat a
                end
                  zero_nata
                  ();
        val x_a = nth A_ a2 x ();
        val a = hm_exch_op_impl A_ hm (suc zero_nata) b ();
      in
        let
          val (a1b, a2a) = a;
          val (a1c, a2aa) = a1b;
          val (_, ba) = a1c;
        in
          (fn f_ => fn () => f_
            ((let
                val (aa, _) = a1c;
              in
                nth heap_nat aa
              end
               (minus_nat ba (suc zero_nata)))
            ()) ())
            (fn xa =>
              (fn f_ => fn () => f_ ((marl_butlast heap_nat a1c) ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_ ((len heap_nat a2aa) ()) ())
                    (fn xc =>
                      (fn f_ => fn () => f_ ((upd heap_nat xa xc a2aa) ()) ())
                        (fn xaa =>
                          (if equal_nat b (suc zero_nata)
                            then (fn () => ((x, x_a), ((xb, xaa), a2a)))
                            else (fn f_ => fn () => f_
                                   ((hm_sink_op_impl A_ B_ prio ((xb, xaa), a2a)
                                      (suc zero_nata))
                                   ()) ())
                                   (fn x_g => (fn () => ((x, x_a), x_g))))))))
        end
          ()
      end)
  end;

fun hm_insert_op_impl A_ B_ maxsize prio hm k v =
  let
    val (a1, a2) = v;
    val (a1a, a2a) = a1;
    val (_, b) = a1a;
  in
    (fn () =>
      let
        val x =
          let
            val (a, n) = a1a;
          in
            (fn x =>
              (fn f_ => fn () => f_ ((upd heap_nat n x a) ()) ())
                (fn aa => (fn () => (aa, suc n))))
          end
            hm
            ();
      in
        let
          val (_, ba) = x;
        in
          (fn f_ => fn () => f_ ((upd heap_nat hm b a2a) ()) ())
            (fn xa =>
              (fn f_ => fn () => f_ ((len A_ a2) ()) ())
                (fn xb =>
                  (fn f_ => fn () => f_
                    ((if equal_nat xb zero_nata then new A_ maxsize k
                       else (fn () => a2))
                    ()) ())
                    (fn xba =>
                      (fn f_ => fn () => f_ ((upd A_ hm k xba) ()) ())
                        (fn xbb =>
                          hm_swim_op_impl A_ B_ prio ((x, xa), xbb) ba))))
        end
          ()
      end)
  end;

fun marl_empty_sz (A1_, A2_) B_ maxsize =
  (fn () => let
              val a = new A2_ maxsize (default A1_) ();
            in
              (a, zero B_)
            end);

fun ial_empty maxsize =
  (fn () =>
    let
      val x = marl_empty_sz (default_nat, heap_nat) zero_nat maxsize ();
      val x_b = new heap_nat maxsize maxsize ();
    in
      (x, x_b)
    end);

fun hm_empty_op_impl A_ maxsize =
  (fn () => let
              val x = ial_empty maxsize ();
              val x_b = (fn () => Array.fromList []) ();
            in
              (x, x_b)
            end);

fun testsuite n =
  let
    val s = (Word32.fromInt 0);
    val n2 =
      nat_of_integer
        (fst (IntInf.divMod (IntInf.abs (integer_of_nat n),
               IntInf.abs (2 : IntInf.int))));
  in
    (fn () =>
      let
        val hm = hm_empty_op_impl heap_nat n ();
        val a =
          rep (one_nat, plus_nat, ord_nat) zero_nata n
            (fn (hma, sa) => fn i =>
              let
                val (sb, v) = rand sa n2;
              in
                (fn f_ => fn () => f_
                  ((hm_insert_op_impl heap_nat linorder_nat n id i v hma) ())
                  ())
                  (fn hmb => (fn () => (hmb, sb)))
              end)
            (hm, s) ();
      in
        let
          val (hma, sa) = a;
        in
          (fn f_ => fn () => f_
            ((rep (one_nat, plus_nat, ord_nat) zero_nata n
               (fn (hmb, sb) => fn i =>
                 let
                   val (sc, v) = rand sb n2;
                 in
                   (fn f_ => fn () => f_
                     ((hm_change_key_op_impl heap_nat linorder_nat id i v hmb)
                     ()) ())
                     (fn hmc => (fn () => (hmc, sc)))
                 end)
               (hma, sa))
            ()) ())
            (fn (hmb, _) =>
              (fn f_ => fn () => f_
                ((rep (one_nat, plus_nat, ord_nat) zero_nata n
                   (fn hmc => fn _ =>
                     (fn f_ => fn () => f_
                       ((hm_pop_min_op_impl heap_nat linorder_nat id hmc) ())
                       ())
                       (fn (_, aa) => (fn () => aa)))
                   hmb)
                ()) ())
                (fn _ => (fn () => ())))
        end
          ()
      end)
  end;

fun e_less_eq A_ B_ e Infty = false
  | e_less_eq A_ B_ ea (LP (e, uu)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) ea e;

fun p_unwrap (LP (e, a)) = (e, a);

fun aluprio_insert A_ B_ splits annot isEmpty app consr s e a =
  (if e_less_eq A_ B_ e (annot s) andalso not (isEmpty s)
    then let
           val b = splits (e_less_eq A_ B_ e) Infty s;
           val (l, ba) = b;
           val (bb, c) = ba;
         in
           let
             val (_, lp) = bb;
           in
             (fn r =>
               (if less ((ord_preorder o preorder_order o order_linorder) A_) e
                     (fst (p_unwrap lp))
                 then app (consr (consr l () (LP (e, a))) () lp) r
                 else app (consr l () (LP (e, a))) r))
           end
             c
         end
    else consr s () (LP (e, a)));

fun aluprio_empty empt = empt;

fun p_less_eq B_ (LP (e, a)) (LP (f, b)) =
  less_eq ((ord_preorder o preorder_order o order_linorder) B_) a b
  | p_less_eq B_ uu Infty = true
  | p_less_eq B_ Infty (LP (e, a)) = false;

fun less_eq_LP B_ = p_less_eq B_;

fun aluprio_pop A_ B_ splits annot app s =
  let
    val a = splits (fn x => less_eq_LP B_ x (annot s)) Infty s;
    val (l, aa) = a;
    val (ab, b) = aa;
  in
    let
      val (_, lp) = ab;
    in
      (fn r => let
                 val LP (e, ac) = lp;
               in
                 (e, (ac, app l r))
               end)
    end
      b
  end;

fun isEmptya t =
  (case t of Empty => true | Single _ => false | Deep (_, _, _, _) => false);

fun rep_FingerTree A_ (Abs_FingerTree x) = x;

fun isEmpty B_ t = isEmptya (rep_FingerTree B_ t);

fun ft_isEmpty B_ = isEmpty B_;

fun nodeToDigit (Tip (e, a)) = Onea (Tip (e, a))
  | nodeToDigit (Node2 (uu, a, b)) = Two (a, b)
  | nodeToDigit (Node3 (uv, a, b, c)) = Three (a, b, c);

fun gmn B_ (Tip (e, a)) = a
  | gmn B_ (Node2 (a, uu, uv)) = a
  | gmn B_ (Node3 (a, uw, ux, uy)) = a;

fun node3 B_ nd1 nd2 nd3 =
  Node3 (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
           (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
             (gmn B_ nd1) (gmn B_ nd2))
           (gmn B_ nd3),
          nd1, nd2, nd3);

fun gmft B_ Empty = zero (zero_monoid_add B_)
  | gmft B_ (Single nd) = gmn B_ nd
  | gmft B_ (Deep (a, uu, uv, uw)) = a;

fun gmd B_ (Onea a) = gmn B_ a
  | gmd B_ (Two (a, b)) =
    plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) (gmn B_ a)
      (gmn B_ b)
  | gmd B_ (Three (a, b, c)) =
    plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
      (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) (gmn B_ a)
        (gmn B_ b))
      (gmn B_ c)
  | gmd B_ (Four (a, b, c, d)) =
    plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
      (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
        (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) (gmn B_ a)
          (gmn B_ b))
        (gmn B_ c))
      (gmn B_ d);

fun deep B_ pr m sf =
  Deep (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_)
          (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) (gmd B_ pr)
            (gmft B_ m))
          (gmd B_ sf),
         pr, m, sf);

fun nlcons B_ a Empty = Single a
  | nlcons B_ a (Single b) = deep B_ (Onea a) Empty (Onea b)
  | nlcons B_ a (Deep (uu, Onea b, m, sf)) = deep B_ (Two (a, b)) m sf
  | nlcons B_ a (Deep (uv, Two (b, c), m, sf)) = deep B_ (Three (a, b, c)) m sf
  | nlcons B_ a (Deep (uw, Three (b, c, d), m, sf)) =
    deep B_ (Four (a, b, c, d)) m sf
  | nlcons B_ a (Deep (ux, Four (b, c, d, e), m, sf)) =
    deep B_ (Two (a, b)) (nlcons B_ (node3 B_ c d e) m) sf;

fun lconsNlist B_ [] t = t
  | lconsNlist B_ (x :: xs) t = nlcons B_ x (lconsNlist B_ xs t);

fun nlistToTree B_ xs = lconsNlist B_ xs Empty;

fun digitToNlist (Onea a) = [a]
  | digitToNlist (Two (a, b)) = [a, b]
  | digitToNlist (Three (a, b, c)) = [a, b, c]
  | digitToNlist (Four (a, b, c, d)) = [a, b, c, d];

fun splitNlist A_ p i [a] = ([], (a, []))
  | splitNlist A_ p i (a :: v :: va) =
    let
      val i2 =
        plus ((plus_semigroup_add o semigroup_add_monoid_add) A_) i (gmn A_ a);
    in
      (if p i2 then ([], (a, v :: va))
        else let
               val (l, (x, r)) = splitNlist A_ p i2 (v :: va);
             in
               (a :: l, (x, r))
             end)
    end;

fun splitDigit A_ p i d = splitNlist A_ p i (digitToNlist d);

fun nlistToDigit [a] = Onea a
  | nlistToDigit [a, b] = Two (a, b)
  | nlistToDigit [a, b, c] = Three (a, b, c)
  | nlistToDigit [a, b, c, d] = Four (a, b, c, d);

fun digitToTree B_ (Onea a) = Single a
  | digitToTree B_ (Two (a, b)) = deep B_ (Onea a) Empty (Onea b)
  | digitToTree B_ (Three (a, b, c)) = deep B_ (Two (a, b)) Empty (Onea c)
  | digitToTree B_ (Four (a, b, c, d)) =
    deep B_ (Two (a, b)) Empty (Two (c, d));

fun viewRn B_ Empty = NONE
  | viewRn B_ (Single a) = SOME (a, Empty)
  | viewRn B_ (Deep (uu, pr, m, Two (a, b))) = SOME (b, deep B_ pr m (Onea a))
  | viewRn B_ (Deep (uv, pr, m, Three (a, b, c))) =
    SOME (c, deep B_ pr m (Two (a, b)))
  | viewRn B_ (Deep (uw, pr, m, Four (a, b, c, d))) =
    SOME (d, deep B_ pr m (Three (a, b, c)))
  | viewRn B_ (Deep (ux, pr, m, Onea a)) =
    (case viewRn B_ m of NONE => SOME (a, digitToTree B_ pr)
      | SOME b => let
                    val (ba, m2) = b;
                  in
                    SOME (a, deep B_ pr m2 (nodeToDigit ba))
                  end);

fun deepR B_ pr m [] =
  (case viewRn B_ m of NONE => digitToTree B_ pr
    | SOME a => let
                  val (aa, m2) = a;
                in
                  deep B_ pr m2 (nodeToDigit aa)
                end)
  | deepR B_ pr m (v :: va) = deep B_ pr m (nlistToDigit (v :: va));

fun viewLn B_ Empty = NONE
  | viewLn B_ (Single a) = SOME (a, Empty)
  | viewLn B_ (Deep (uu, Two (a, b), m, sf)) = SOME (a, deep B_ (Onea b) m sf)
  | viewLn B_ (Deep (uv, Three (a, b, c), m, sf)) =
    SOME (a, deep B_ (Two (b, c)) m sf)
  | viewLn B_ (Deep (uw, Four (a, b, c, d), m, sf)) =
    SOME (a, deep B_ (Three (b, c, d)) m sf)
  | viewLn B_ (Deep (ux, Onea a, m, sf)) =
    (case viewLn B_ m of NONE => SOME (a, digitToTree B_ sf)
      | SOME b => let
                    val (ba, m2) = b;
                  in
                    SOME (a, deep B_ (nodeToDigit ba) m2 sf)
                  end);

fun deepL B_ [] m sf =
  (case viewLn B_ m of NONE => digitToTree B_ sf
    | SOME a => let
                  val (aa, m2) = a;
                in
                  deep B_ (nodeToDigit aa) m2 sf
                end)
  | deepL B_ (v :: va) m sf = deep B_ (nlistToDigit (v :: va)) m sf;

fun nsplitTree A_ p i Empty =
  (Empty, (Tip ((raise Fail "undefined"), (raise Fail "undefined")), Empty))
  | nsplitTree A_ p i (Single ea) = (Empty, (ea, Empty))
  | nsplitTree A_ p i (Deep (uu, pr, m, sf)) =
    let
      val vpr =
        plus ((plus_semigroup_add o semigroup_add_monoid_add) A_) i (gmd A_ pr);
      val vm =
        plus ((plus_semigroup_add o semigroup_add_monoid_add) A_) vpr
          (gmft A_ m);
    in
      (if p vpr then let
                       val (l, (x, r)) = splitDigit A_ p i pr;
                     in
                       (nlistToTree A_ l, (x, deepL A_ r m sf))
                     end
        else (if p vm
               then let
                      val (ml, (xs, mr)) = nsplitTree A_ p vpr m;
                      val (l, (x, r)) =
                        splitDigit A_ p
                          (plus ((plus_semigroup_add o semigroup_add_monoid_add)
                                  A_)
                            vpr (gmft A_ ml))
                          (nodeToDigit xs);
                    in
                      (deepR A_ pr ml l, (x, deepL A_ r mr sf))
                    end
               else let
                      val (l, (x, r)) = splitDigit A_ p vm sf;
                    in
                      (deepR A_ pr m l, (x, nlistToTree A_ r))
                    end))
    end;

fun n_unwrap (Tip (e, a)) = (e, a)
  | n_unwrap (Node2 (uu, a, b)) = (raise Fail "undefined")
  | n_unwrap (Node3 (uv, a, b, c)) = (raise Fail "undefined");

fun splitTreea A_ p i t = let
                            val (l, (x, r)) = nsplitTree A_ p i t;
                          in
                            (l, (n_unwrap x, r))
                          end;

fun annota B_ t = gmft B_ t;

fun annot B_ t = annota B_ (rep_FingerTree B_ t);

fun splitTree_aux B_ p i t =
  Abs_splitres
    (if not (p i) andalso
          p (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) i
              (annot B_ t))
      then splitTreea B_ p i (rep_FingerTree B_ t)
      else (Empty, ((raise Fail "undefined"), Empty)));

fun rep_splitres A_ (Abs_splitres x) = x;

fun extract_splitres_r B_ r =
  Abs_FingerTree let
                   val (_, (_, ra)) = rep_splitres B_ r;
                 in
                   ra
                 end;

fun extract_splitres_l B_ r =
  Abs_FingerTree let
                   val (l, (_, _)) = rep_splitres B_ r;
                 in
                   l
                 end;

fun extract_splitres_a B_ r = let
                                val (_, a) = rep_splitres B_ r;
                                val (aa, _) = a;
                              in
                                aa
                              end;

fun extract_splitres B_ r =
  (extract_splitres_l B_ r, (extract_splitres_a B_ r, extract_splitres_r B_ r));

fun splitTree A_ p i t = extract_splitres A_ (splitTree_aux A_ p i t);

fun ft_splits A_ = splitTree A_;

fun empty B_ = Abs_FingerTree Empty;

fun ft_empty B_ = (fn _ => empty B_);

fun nrcons B_ Empty a = Single a
  | nrcons B_ (Single b) a = deep B_ (Onea b) Empty (Onea a)
  | nrcons B_ (Deep (uu, pr, m, Onea b)) a = deep B_ pr m (Two (b, a))
  | nrcons B_ (Deep (uv, pr, m, Two (b, c))) a = deep B_ pr m (Three (b, c, a))
  | nrcons B_ (Deep (uw, pr, m, Three (b, c, d))) a =
    deep B_ pr m (Four (b, c, d, a))
  | nrcons B_ (Deep (ux, pr, m, Four (b, c, d, e))) a =
    deep B_ pr (nrcons B_ m (node3 B_ b c d)) (Two (e, a));

fun rconsa B_ t a = nrcons B_ t (Tip (fst a, snd a));

fun rcons B_ t a = Abs_FingerTree (rconsa B_ (rep_FingerTree B_ t) a);

fun ft_consr B_ s e a = rcons B_ s (e, a);

fun ft_annot B_ = annot B_;

fun rconsNlist B_ t [] = t
  | rconsNlist B_ t (x :: xs) = rconsNlist B_ (nrcons B_ t x) xs;

fun node2 B_ nd1 nd2 =
  Node2 (plus ((plus_semigroup_add o semigroup_add_monoid_add) B_) (gmn B_ nd1)
           (gmn B_ nd2),
          nd1, nd2);

fun nodes B_ [a, b] = [node2 B_ a b]
  | nodes B_ [a, b, c] = [node3 B_ a b c]
  | nodes B_ [a, b, c, d] = [node2 B_ a b, node2 B_ c d]
  | nodes B_ (a :: b :: c :: v :: vb :: vc) =
    node3 B_ a b c :: nodes B_ (v :: vb :: vc);

fun app3 B_ Empty xs t = lconsNlist B_ xs t
  | app3 B_ (Single v) xs Empty = rconsNlist B_ (Single v) xs
  | app3 B_ (Deep (v, va, vb, vc)) xs Empty =
    rconsNlist B_ (Deep (v, va, vb, vc)) xs
  | app3 B_ (Single x) xs (Single v) = nlcons B_ x (lconsNlist B_ xs (Single v))
  | app3 B_ (Single x) xs (Deep (v, va, vb, vc)) =
    nlcons B_ x (lconsNlist B_ xs (Deep (v, va, vb, vc)))
  | app3 B_ (Deep (v, va, vb, vc)) xs (Single x) =
    nrcons B_ (rconsNlist B_ (Deep (v, va, vb, vc)) xs) x
  | app3 B_ (Deep (uu, pr1, m1, sf1)) ts (Deep (uv, pr2, m2, sf2)) =
    deep B_ pr1
      (app3 B_ m1 (nodes B_ (digitToNlist sf1 @ ts @ digitToNlist pr2)) m2) sf2;

fun appa B_ t1 t2 = app3 B_ t1 [] t2;

fun app B_ s t =
  Abs_FingerTree (appa B_ (rep_FingerTree B_ s) (rep_FingerTree B_ t));

fun ft_app B_ = app B_;

fun ftestsuite n =
  let
    val s = (Word32.fromInt 0);
    val n2 =
      nat_of_integer
        (fst (IntInf.divMod (IntInf.abs (integer_of_nat n),
               IntInf.abs (2 : IntInf.int))));
    val hm =
      aluprio_empty (ft_empty (monoid_add_LP linorder_nat linorder_nat)) ();
    val (hma, sa) =
      drep (one_nat, plus_nat, ord_nat) zero_nata n
        (fn (hma, sa) => fn i =>
          let
            val (sb, v) = rand sa n2;
            val hmb =
              aluprio_insert linorder_nat linorder_nat
                (ft_splits (monoid_add_LP linorder_nat linorder_nat))
                (ft_annot (monoid_add_LP linorder_nat linorder_nat))
                (ft_isEmpty (monoid_add_LP linorder_nat linorder_nat))
                (ft_app (monoid_add_LP linorder_nat linorder_nat))
                (ft_consr (monoid_add_LP linorder_nat linorder_nat)) hma i v;
          in
            (hmb, sb)
          end)
        (hm, s);
    val (hmb, _) =
      drep (one_nat, plus_nat, ord_nat) zero_nata n
        (fn (hmb, sb) => fn i =>
          let
            val (sc, v) = rand sb n2;
            val hmc =
              aluprio_insert linorder_nat linorder_nat
                (ft_splits (monoid_add_LP linorder_nat linorder_nat))
                (ft_annot (monoid_add_LP linorder_nat linorder_nat))
                (ft_isEmpty (monoid_add_LP linorder_nat linorder_nat))
                (ft_app (monoid_add_LP linorder_nat linorder_nat))
                (ft_consr (monoid_add_LP linorder_nat linorder_nat)) hmb i v;
          in
            (hmc, sc)
          end)
        (hma, sa);
    val _ =
      drep (one_nat, plus_nat, ord_nat) zero_nata n
        (fn hmc => fn _ =>
          let
            val (_, (_, hmd)) =
              aluprio_pop linorder_nat linorder_nat
                (ft_splits (monoid_add_LP linorder_nat linorder_nat))
                (ft_annot (monoid_add_LP linorder_nat linorder_nat))
                (ft_app (monoid_add_LP linorder_nat linorder_nat)) hmc;
          in
            hmd
          end)
        hmb;
  in
    ()
  end;

end; (*struct Heapmap*)
