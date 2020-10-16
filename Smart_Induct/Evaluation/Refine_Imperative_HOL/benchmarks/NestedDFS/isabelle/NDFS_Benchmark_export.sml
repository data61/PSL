
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

structure NDFS_Benchmark : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  type ('a, 'b) rbt
  type 'a dres
  type 'a blue_witness
  val nat_of_integer : IntInf.int -> nat
  val imp_ndfs_impl :
    (nat list) array ->
      bool array -> nat -> (unit -> ((nat * (nat list * nat list)) option))
  val imp_acc_of_list : IntInf.int list -> (unit -> (bool array))
  val imp_ndfs_sz_impl :
    nat ->
      (nat list) array ->
        bool array -> nat -> (unit -> ((nat * (nat list * nat list)) option))
  val imp_graph_of_list :
    IntInf.int -> (IntInf.int * IntInf.int) list -> (unit -> ((nat list) array))
  val fun_ndfs_impl :
    (nat -> nat list) ->
      (nat, unit) rbt -> nat -> (nat * (nat list * nat list)) option
  val fun_acc_of_list : IntInf.int list -> (nat, unit) rbt
  val funs_ndfs_impl :
    (nat -> nat list) ->
      (unit option) FArray.IsabelleMapping.ArrayType ->
        nat -> (nat * (nat list * nat list)) option
  val fun_succ_of_list : (IntInf.int * IntInf.int) list -> nat -> nat list
  val funs_acc_of_list :
    IntInf.int list -> (unit option) FArray.IsabelleMapping.ArrayType
  val funs_succ_of_list : (IntInf.int * IntInf.int) list -> nat -> nat list
end = struct

datatype nat = Nat of IntInf.int;

fun integer_of_nat (Nat x) = x;

fun equal_nata m n = (((integer_of_nat m) : IntInf.int) = (integer_of_nat n));

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_nat = {equal = equal_nata} : nat equal;

datatype typerepa = Typerep of string * typerepa list;

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

fun less_eq_nat m n = IntInf.<= (integer_of_nat m, integer_of_nat n);

type 'a ord = {less_eq : 'a -> 'a -> bool, less : 'a -> 'a -> bool};
val less_eq = #less_eq : 'a ord -> 'a -> 'a -> bool;
val less = #less : 'a ord -> 'a -> 'a -> bool;

fun less_nat m n = IntInf.< (integer_of_nat m, integer_of_nat n);

val ord_nat = {less_eq = less_eq_nat, less = less_nat} : nat ord;

fun typerep_boola t = Typerep ("HOL.bool", []);

val countable_bool = {} : bool countable;

val typerep_bool = {typerep = typerep_boola} : bool typerep;

val heap_bool = {countable_heap = countable_bool, typerep_heap = typerep_bool} :
  bool heap;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

datatype num = One | Bit0 of num | Bit1 of num;

datatype color = R | B;

datatype ('a, 'b) rbt = Empty |
  Branch of color * ('a, 'b) rbt * 'a * 'b * ('a, 'b) rbt;

datatype 'a dres = DSUCCEEDi | DFAILi | DRETURN of 'a;

datatype 'a blue_witness = NO_CYC | REACH of 'a * 'a list * 'a * 'a list |
  CIRC of 'a * 'a list * 'a list;

fun eq A_ a b = equal A_ a b;

fun max A_ a b = (if less_eq A_ a b then b else a);

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

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun pairself f (a, b) = (f a, f b);

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun balance (Branch (R, a, w, x, b)) s t (Branch (R, c, y, z, d)) =
  Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z Empty =
    Branch (R, Branch (B, a, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance (Branch (R, Branch (R, a, w, x, b), s, t, c)) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, a, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z Empty =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance
    (Branch (R, Branch (B, va, vb, vc, vd), w, x, Branch (R, b, s, t, c))) y z
    Empty =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (R, Empty, w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance
    (Branch (R, Branch (B, ve, vf, vg, vh), w, x, Branch (R, b, s, t, c))) y z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, Branch (B, Branch (B, ve, vf, vg, vh), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance Empty w x (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, d))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, b, s, t, Branch (R, c, y, z, d))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, d))
  | balance Empty w x (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch (R, Branch (B, Empty, w, x, b), s, t, Branch (B, c, y, z, Empty))
  | balance Empty w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, va, vb, vc, vd))) =
    Branch
      (R, Branch (B, Empty, w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, va, vb, vc, vd)))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Empty)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Empty))
  | balance (Branch (B, va, vb, vc, vd)) w x
    (Branch (R, Branch (R, b, s, t, c), y, z, Branch (B, ve, vf, vg, vh))) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), w, x, b), s, t,
        Branch (B, c, y, z, Branch (B, ve, vf, vg, vh)))
  | balance Empty s t Empty = Branch (B, Empty, s, t, Empty)
  | balance Empty s t (Branch (B, va, vb, vc, vd)) =
    Branch (B, Empty, s, t, Branch (B, va, vb, vc, vd))
  | balance Empty s t (Branch (v, Empty, vb, vc, Empty)) =
    Branch (B, Empty, s, t, Branch (v, Empty, vb, vc, Empty))
  | balance Empty s t (Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty)) =
    Branch
      (B, Empty, s, t, Branch (v, Branch (B, ve, vf, vg, vh), vb, vc, Empty))
  | balance Empty s t (Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi))) =
    Branch
      (B, Empty, s, t, Branch (v, Empty, vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance Empty s t
    (Branch (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
    = Branch
        (B, Empty, s, t,
          Branch
            (v, Branch (B, ve, vj, vk, vl), vb, vc, Branch (B, vf, vg, vh, vi)))
  | balance (Branch (B, va, vb, vc, vd)) s t Empty =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Empty)
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (B, ve, vf, vg, vh)) =
    Branch (B, Branch (B, va, vb, vc, vd), s, t, Branch (B, ve, vf, vg, vh))
  | balance (Branch (B, va, vb, vc, vd)) s t (Branch (v, Empty, vf, vg, Empty))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t, Branch (v, Empty, vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty)) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Branch (B, vi, vj, vk, vl), vf, vg, Empty))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm))) =
    Branch
      (B, Branch (B, va, vb, vc, vd), s, t,
        Branch (v, Empty, vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (B, va, vb, vc, vd)) s t
    (Branch (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
    = Branch
        (B, Branch (B, va, vb, vc, vd), s, t,
          Branch
            (v, Branch (B, vi, vn, vo, vp), vf, vg, Branch (B, vj, vk, vl, vm)))
  | balance (Branch (v, Empty, vb, vc, Empty)) s t Empty =
    Branch (B, Branch (v, Empty, vb, vc, Empty), s, t, Empty)
  | balance (Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh))) s t Empty =
    Branch
      (B, Branch (v, Empty, vb, vc, Branch (B, ve, vf, vg, vh)), s, t, Empty)
  | balance (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty)) s t Empty =
    Branch
      (B, Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Empty), s, t, Empty)
  | balance
    (Branch (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)))
    s t Empty =
    Branch
      (B, Branch
            (v, Branch (B, vf, vg, vh, vi), vb, vc, Branch (B, ve, vj, vk, vl)),
        s, t, Empty)
  | balance (Branch (v, Empty, vf, vg, Empty)) s t (Branch (B, va, vb, vc, vd))
    = Branch
        (B, Branch (v, Empty, vf, vg, Empty), s, t, Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl))) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Empty, vf, vg, Branch (B, vi, vj, vk, vl)), s, t,
        Branch (B, va, vb, vc, vd))
  | balance (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty)) s t
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Empty), s, t,
        Branch (B, va, vb, vc, vd))
  | balance
    (Branch (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)))
    s t (Branch (B, va, vb, vc, vd)) =
    Branch
      (B, Branch
            (v, Branch (B, vj, vk, vl, vm), vf, vg, Branch (B, vi, vn, vo, vp)),
        s, t, Branch (B, va, vb, vc, vd));

fun balance_left (Branch (R, a, k, x, b)) s y c =
  Branch (R, Branch (B, a, k, x, b), s, y, c)
  | balance_left Empty k x (Branch (B, a, s, y, b)) =
    balance Empty k x (Branch (R, a, s, y, b))
  | balance_left (Branch (B, va, vb, vc, vd)) k x (Branch (B, a, s, y, b)) =
    balance (Branch (B, va, vb, vc, vd)) k x (Branch (R, a, s, y, b))
  | balance_left Empty k x (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch (R, Branch (B, Empty, k, x, a), s, y, balance b t z (paint R c))
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (B, a, s, y, b), t, z, c)) =
    Branch
      (R, Branch (B, Branch (B, va, vb, vc, vd), k, x, a), s, y,
        balance b t z (paint R c))
  | balance_left Empty k x Empty = Empty
  | balance_left Empty k x (Branch (R, Empty, vb, vc, vd)) = Empty
  | balance_left Empty k x (Branch (R, Branch (R, ve, vf, vg, vh), vb, vc, vd))
    = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x Empty = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Empty, vf, vg, vh)) = Empty
  | balance_left (Branch (B, va, vb, vc, vd)) k x
    (Branch (R, Branch (R, vi, vj, vk, vl), vf, vg, vh)) = Empty;

fun combine Empty x = x
  | combine (Branch (v, va, vb, vc, vd)) Empty = Branch (v, va, vb, vc, vd)
  | combine (Branch (R, a, k, x, b)) (Branch (R, c, s, y, d)) =
    (case combine b c
      of Empty => Branch (R, a, k, x, Branch (R, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (R, a, k, x, b2), t, z, Branch (R, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        Branch (R, a, k, x, Branch (R, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, a, k, x, b)) (Branch (B, c, s, y, d)) =
    (case combine b c
      of Empty => balance_left a k x (Branch (B, Empty, s, y, d))
      | Branch (R, b2, t, z, c2) =>
        Branch (R, Branch (B, a, k, x, b2), t, z, Branch (B, c2, s, y, d))
      | Branch (B, b2, t, z, c2) =>
        balance_left a k x (Branch (B, Branch (B, b2, t, z, c2), s, y, d)))
  | combine (Branch (B, va, vb, vc, vd)) (Branch (R, b, k, x, c)) =
    Branch (R, combine (Branch (B, va, vb, vc, vd)) b, k, x, c)
  | combine (Branch (R, a, k, x, b)) (Branch (B, va, vb, vc, vd)) =
    Branch (R, a, k, x, combine b (Branch (B, va, vb, vc, vd)));

fun dbind DFAILi f = DFAILi
  | dbind DSUCCEEDi f = DSUCCEEDi
  | dbind (DRETURN x) f = f x;

fun nth_oo A_ v a = (fn b => array_nth_oo v a b) o integer_of_nat;

fun upd_oo A_ f =
  (fn a => fn b => fn c => array_upd_oo f a b c) o integer_of_nat;

fun succ2 A_ =
  (fn ai => fn bi => fn () =>
    let
      val x = len (heap_list A_) ai ();
    in
      (if less_nat bi x then nth (heap_list A_) ai bi else (fn () => [])) ()
    end);

fun array_set a = FArray.IsabelleMapping.array_set a o integer_of_nat;

fun balance_right a k x (Branch (R, b, s, y, c)) =
  Branch (R, a, k, x, Branch (B, b, s, y, c))
  | balance_right (Branch (B, a, k, x, b)) s y Empty =
    balance (Branch (R, a, k, x, b)) s y Empty
  | balance_right (Branch (B, a, k, x, b)) s y (Branch (B, va, vb, vc, vd)) =
    balance (Branch (R, a, k, x, b)) s y (Branch (B, va, vb, vc, vd))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z Empty =
    Branch (R, balance (paint R a) k x b, s, y, Branch (B, c, t, z, Empty))
  | balance_right (Branch (R, a, k, x, Branch (B, b, s, y, c))) t z
    (Branch (B, va, vb, vc, vd)) =
    Branch
      (R, balance (paint R a) k x b, s, y,
        Branch (B, c, t, z, Branch (B, va, vb, vc, vd)))
  | balance_right Empty k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Empty)) k x Empty = Empty
  | balance_right (Branch (R, va, vb, vc, Branch (R, ve, vf, vg, vh))) k x Empty
    = Empty
  | balance_right Empty k x (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Empty)) k x
    (Branch (B, va, vb, vc, vd)) = Empty
  | balance_right (Branch (R, ve, vf, vg, Branch (R, vi, vj, vk, vl))) k x
    (Branch (B, va, vb, vc, vd)) = Empty;

fun rbt_del less x (Branch (c, a, y, s, b)) =
  (if less x y then rbt_del_from_left less x a y s b
    else (if less y x then rbt_del_from_right less x a y s b else combine a b))
  | rbt_del less x Empty = Empty
and rbt_del_from_left less x (Branch (R, va, vb, vc, vd)) y s b =
  Branch (R, rbt_del less x (Branch (R, va, vb, vc, vd)), y, s, b)
  | rbt_del_from_left less x Empty y s b =
    Branch (R, rbt_del less x Empty, y, s, b)
  | rbt_del_from_left less x (Branch (B, lt, z, v, rt)) y s b =
    balance_left (rbt_del less x (Branch (B, lt, z, v, rt))) y s b
and rbt_del_from_right less x a y s (Branch (R, va, vb, vc, vd)) =
  Branch (R, a, y, s, rbt_del less x (Branch (R, va, vb, vc, vd)))
  | rbt_del_from_right less x a y s Empty =
    Branch (R, a, y, s, rbt_del less x Empty)
  | rbt_del_from_right less x a y s (Branch (B, lt, z, v, rt)) =
    balance_right a y s (rbt_del less x (Branch (B, lt, z, v, rt)));

val zero_nat : nat = Nat (0 : IntInf.int);

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nat aa zero_nat l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

fun array_growa a = FArray.IsabelleMapping.array_grow a o integer_of_nat;

fun imp_nfoldli (x :: ls) c f s =
  (fn () =>
    let
      val b = c s ();
    in
      (if b then (fn f_ => fn () => f_ ((f x s) ()) ()) (imp_nfoldli ls c f)
        else (fn () => s))
        ()
    end)
  | imp_nfoldli [] c f s = (fn () => s);

fun cr_graph numV es =
  (fn () =>
    let
      val a = new (heap_list heap_nat) numV [] ();
      val x =
        imp_nfoldli es (fn _ => (fn () => true))
          (fn (u, v) => fn aa =>
            (fn f_ => fn () => f_ ((nth (heap_list heap_nat) aa u) ()) ())
              (fn l =>
                let
                  val la = v :: l;
                in
                  (fn f_ => fn () => f_ ((upd (heap_list heap_nat) u la aa) ())
                    ())
                    (fn ab => (fn () => ab))
                end))
          a ();
    in
      x
    end);

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun plus_nat m n = Nat (IntInf.+ (integer_of_nat m, integer_of_nat n));

val one_nat : nat = Nat (1 : IntInf.int);

fun ias_ins k a =
  upd_oo heap_bool
    (fn () =>
      let
        val l = len heap_bool a ();
      in
        let
          val newsz =
            max ord_nat (plus_nat k one_nat)
              (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
                (nat_of_integer (3 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((array_grow heap_bool a newsz false) ()) ())
            (upd heap_bool k true)
        end
          ()
      end)
    k true a;

val ias_initial_size : nat = nat_of_integer (8 : IntInf.int);

fun ias_new_sz sz = new heap_bool sz false;

val ias_new : (unit -> (bool array)) = ias_new_sz ias_initial_size;

fun extract_res cyc =
  (case cyc of NO_CYC => NONE | REACH (_, _, _, _) => NONE
    | CIRC (v, pc, pr) => SOME (v, (pc, pr)));

fun ias_memb k a = nth_oo heap_bool false a k;

fun array_get_oo x a = FArray.IsabelleMapping.array_get_oo x a o integer_of_nat;

fun array_length x = (nat_of_integer o FArray.IsabelleMapping.array_length) x;

fun array_set_oo f a = FArray.IsabelleMapping.array_set_oo f a o integer_of_nat;

fun prep_wit_red v NONE = NONE
  | prep_wit_red v (SOME (p, u)) = SOME (v :: p, u);

fun rbt_delete less k t = paint B (rbt_del less k t);

fun the_res (DRETURN x) = x;

fun map2set_memb l k s = (case l k s of NONE => false | SOME _ => true);

fun iam_empty x = (fn _ => FArray.IsabelleMapping.array_of_list []) x;

fun init_wit_blue A_ u0 NONE = NO_CYC
  | init_wit_blue A_ u0 (SOME (p, u)) =
    (if eq A_ u u0 then CIRC (u0, p, []) else REACH (u0, p, u, []));

fun prep_wit_blue A_ u0 NO_CYC = NO_CYC
  | prep_wit_blue A_ u0 (REACH (v, pa, u, p)) =
    (if eq A_ u0 u then CIRC (v, pa @ u :: p, u0 :: p)
      else REACH (v, pa, u, u0 :: p))
  | prep_wit_blue A_ u0 (CIRC (v, pc, pr)) = CIRC (v, pc, u0 :: pr);

fun is_None a = (case a of NONE => true | SOME _ => false);

fun red_init_witness u v = SOME ([u], v);

fun red_dfs_impl_0 bib ai x =
  let
    val (a1, a2) = x;
  in
    (fn () =>
      let
        val x_a = ias_ins a2 a1 ();
        val xa = succ2 heap_nat ai a2 ();
        val x_c =
          imp_nfoldli xa (fn sigma => (fn () => (is_None sigma)))
            (fn xe => fn _ =>
              (fn f_ => fn () => f_ ((ias_memb xe bib) ()) ())
                (fn x_f =>
                  (fn () => (if x_f then red_init_witness a2 xe else NONE))))
            NONE ();
      in
        (case x_c
          of NONE =>
            (fn f_ => fn () => f_ ((succ2 heap_nat ai a2) ()) ())
              (fn x_d =>
                imp_nfoldli x_d (fn (_, b) => (fn () => (is_None b)))
                  (fn xf => fn (a1a, _) =>
                    (fn f_ => fn () => f_ ((ias_memb xf a1a) ()) ())
                      (fn xb =>
                        (if not xb
                          then (fn f_ => fn () => f_
                                 ((red_dfs_impl_0 bib ai (a1a, xf)) ()) ())
                                 (fn (a1b, a2b) =>
                                   (fn () => (a1b, prep_wit_red a2 a2b)))
                          else (fn () => (a1a, NONE)))))
                  (x_a, NONE))
          | SOME _ => (fn () => (x_a, x_c)))
          ()
      end)
  end;

fun red_dfs_impl x =
  (fn ai => fn bib => fn bia => fn bi => red_dfs_impl_0 bib ai (bia, bi)) x;

fun ias_delete k a = upd_oo heap_bool (fn () => a) k false a;

fun from_list_ga_aux ins [] s = (fn () => s)
  | from_list_ga_aux ins (x :: l) s = (fn () => let
          val xa = ins x s ();
        in
          from_list_ga_aux ins l xa ()
        end);

fun from_list_ga e i l = (fn () => let
                                     val x = e ();
                                   in
                                     from_list_ga_aux i l x ()
                                   end);

fun iam_delete k a = array_set_oo (fn _ => a) a k NONE;

fun iam_alpha a i = array_get_oo NONE a i;

fun iam_lookup k a = iam_alpha a k;

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun iam_increment l idx =
  max ord_nat (minus_nat (plus_nat idx one_nat) l)
    (plus_nat (times_nat (nat_of_integer (2 : IntInf.int)) l)
      (nat_of_integer (3 : IntInf.int)));

fun iam_update k v a =
  array_set_oo
    (fn _ => let
               val l = array_length a;
             in
               array_set (array_growa a (iam_increment l k) NONE) k (SOME v)
             end)
    a k (SOME v);

fun equal_list A_ [] (x21 :: x22) = false
  | equal_list A_ (x21 :: x22) [] = false
  | equal_list A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_list A_ x22 y22
  | equal_list A_ [] [] = true;

fun equal_blue_witness A_ (REACH (x21, x22, x23, x24)) (CIRC (x31, x32, x33)) =
  false
  | equal_blue_witness A_ (CIRC (x31, x32, x33)) (REACH (x21, x22, x23, x24)) =
    false
  | equal_blue_witness A_ NO_CYC (CIRC (x31, x32, x33)) = false
  | equal_blue_witness A_ (CIRC (x31, x32, x33)) NO_CYC = false
  | equal_blue_witness A_ NO_CYC (REACH (x21, x22, x23, x24)) = false
  | equal_blue_witness A_ (REACH (x21, x22, x23, x24)) NO_CYC = false
  | equal_blue_witness A_ (CIRC (x31, x32, x33)) (CIRC (y31, y32, y33)) =
    eq A_ x31 y31 andalso (equal_list A_ x32 y32 andalso equal_list A_ x33 y33)
  | equal_blue_witness A_ (REACH (x21, x22, x23, x24))
    (REACH (y21, y22, y23, y24)) =
    eq A_ x21 y21 andalso
      (equal_list A_ x22 y22 andalso
        (eq A_ x23 y23 andalso equal_list A_ x24 y24))
  | equal_blue_witness A_ NO_CYC NO_CYC = true;

fun blue_dfs_impl_0 bia ai x =
  let
    val (a1, (a1a, (a1b, a2b))) = x;
  in
    (fn () =>
      let
        val x_a = ias_ins a2b a1 ();
        val x_c = ias_ins a2b a1b ();
        val xa = succ2 heap_nat ai a2b ();
        val a =
          imp_nfoldli xa
            (fn (_, (_, (_, a2e))) =>
              (fn () => (equal_blue_witness equal_nat a2e NO_CYC)))
            (fn xg => fn (a1c, (a1d, (a1e, a2e))) =>
              (fn f_ => fn () => f_ ((ias_memb xg a1c) ()) ())
                (fn xb =>
                  (if not xb
                    then (fn f_ => fn () => f_
                           ((blue_dfs_impl_0 bia ai (a1c, (a1d, (a1e, xg)))) ())
                           ())
                           (fn (a1f, (a1g, (a1h, a2h))) =>
                             (fn () =>
                               (a1f, (a1g, (a1h,
     prep_wit_blue equal_nat a2b a2h)))))
                    else (fn () => (a1c, (a1d, (a1e, a2e)))))))
            (x_a, (a1a, (x_c, NO_CYC))) ();
      in
        let
          val (a1c, (a1d, (a1e, a2e))) = a;
        in
          (fn f_ => fn () => f_ ((ias_memb a2b bia) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((if equal_blue_witness equal_nat a2e NO_CYC andalso xb
                   then (fn f_ => fn () => f_ ((red_dfs_impl ai a1e a1d a2b) ())
                          ())
                          (fn (a1f, a2f) =>
                            (fn () => (a1f, init_wit_blue equal_nat a2b a2f)))
                   else (fn () => (a1d, a2e)))
                ()) ())
                (fn (a1f, a2f) =>
                  (fn f_ => fn () => f_ ((ias_delete a2b a1e) ()) ())
                    (fn x_g => (fn () => (a1c, (a1f, (x_g, a2f)))))))
        end
          ()
      end)
  end;

fun blue_dfs_impl x =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val xa = ias_new ();
      val xaa = ias_new ();
      val xb = ias_new ();
      val a = blue_dfs_impl_0 bia ai (xa, (xaa, (xb, bi))) ();
    in
      let
        val (_, (_, (_, b))) = a;
      in
        (fn () => (extract_res b))
      end
        ()
    end)
    x;

fun ias_from_list x = from_list_ga ias_new ias_ins x;

fun map2set_insert i k s = i k () s;

fun glist_member eq x [] = false
  | glist_member eq x (y :: ys) = eq x y orelse glist_member eq x ys;

fun glist_insert eq x xs = (if glist_member eq x xs then xs else x :: xs);

fun rbt_ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_ins A_ f k v (Branch (B, l, x, y, r)) =
    (if less A_ k x then balance (rbt_ins A_ f k v l) x y r
      else (if less A_ x k then balance l x y (rbt_ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins A_ f k v (Branch (R, l, x, y, r)) =
    (if less A_ k x then Branch (R, rbt_ins A_ f k v l, x, y, r)
      else (if less A_ x k then Branch (R, l, x, y, rbt_ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun imp_ndfs_impl x = blue_dfs_impl x;

fun blue_dfs_impl_sz_0 bia ai x =
  let
    val (a1, (a1a, (a1b, a2b))) = x;
  in
    (fn () =>
      let
        val x_a = ias_ins a2b a1 ();
        val x_c = ias_ins a2b a1b ();
        val xa = succ2 heap_nat ai a2b ();
        val a =
          imp_nfoldli xa
            (fn (_, (_, (_, a2e))) =>
              (fn () => (equal_blue_witness equal_nat a2e NO_CYC)))
            (fn xg => fn (a1c, (a1d, (a1e, a2e))) =>
              (fn f_ => fn () => f_ ((ias_memb xg a1c) ()) ())
                (fn xb =>
                  (if not xb
                    then (fn f_ => fn () => f_
                           ((blue_dfs_impl_sz_0 bia ai (a1c, (a1d, (a1e, xg))))
                           ()) ())
                           (fn (a1f, (a1g, (a1h, a2h))) =>
                             (fn () =>
                               (a1f, (a1g, (a1h,
     prep_wit_blue equal_nat a2b a2h)))))
                    else (fn () => (a1c, (a1d, (a1e, a2e)))))))
            (x_a, (a1a, (x_c, NO_CYC))) ();
      in
        let
          val (a1c, (a1d, (a1e, a2e))) = a;
        in
          (fn f_ => fn () => f_ ((ias_memb a2b bia) ()) ())
            (fn xb =>
              (fn f_ => fn () => f_
                ((if equal_blue_witness equal_nat a2e NO_CYC andalso xb
                   then (fn f_ => fn () => f_ ((red_dfs_impl ai a1e a1d a2b) ())
                          ())
                          (fn (a1f, a2f) =>
                            (fn () => (a1f, init_wit_blue equal_nat a2b a2f)))
                   else (fn () => (a1d, a2e)))
                ()) ())
                (fn (a1f, a2f) =>
                  (fn f_ => fn () => f_ ((ias_delete a2b a1e) ()) ())
                    (fn x_g => (fn () => (a1c, (a1f, (x_g, a2f)))))))
        end
          ()
      end)
  end;

fun blue_dfs_impl_sz n =
  (fn ai => fn bia => fn bi => fn () =>
    let
      val x = ias_new_sz n ();
      val xa = ias_new_sz n ();
      val xb = ias_new_sz n ();
      val a = blue_dfs_impl_sz_0 bia ai (x, (xa, (xb, bi))) ();
    in
      let
        val (_, (_, (_, b))) = a;
      in
        (fn () => (extract_res b))
      end
        ()
    end);

fun rbt_insert_with_key A_ f k v t = paint B (rbt_ins A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun rbt_lookup A_ Empty k = NONE
  | rbt_lookup A_ (Branch (uu, l, x, y, r)) k =
    (if less A_ k x then rbt_lookup A_ l k
      else (if less A_ x k then rbt_lookup A_ r k else SOME y));

fun imp_acc_of_list l = ias_from_list (map nat_of_integer l);

fun imp_ndfs_sz_impl x = blue_dfs_impl_sz x;

fun imp_graph_of_list n l =
  cr_graph (nat_of_integer n) (map (pairself nat_of_integer) l);

fun red_dfs_impl_0a onstack e x =
  let
    val (a, b) = x;
    val xa = map2set_insert (rbt_insert ord_nat) b a;
  in
    dbind (foldli (e b)
            (fn aa =>
              (case aa of DSUCCEEDi => false | DFAILi => false
                | DRETURN ab => is_None ab))
            (fn xb => fn s =>
              dbind s
                (fn _ =>
                  (if map2set_memb (fn k => fn t => rbt_lookup ord_nat t k) xb
                        onstack
                    then DRETURN (red_init_witness b xb) else DRETURN NONE)))
            (DRETURN NONE))
      (fn xb =>
        (case xb
          of NONE =>
            foldli (e b)
              (fn aa =>
                (case aa of DSUCCEEDi => false | DFAILi => false
                  | DRETURN ab => let
                                    val (_, ac) = ab;
                                  in
                                    is_None ac
                                  end))
              (fn xc => fn s =>
                dbind s
                  (fn (aa, _) =>
                    (if not (map2set_memb
                              (fn k => fn t => rbt_lookup ord_nat t k) xc aa)
                      then dbind (red_dfs_impl_0a onstack e (aa, xc))
                             (fn (ab, bb) => DRETURN (ab, prep_wit_red b bb))
                      else DRETURN (aa, NONE))))
              (DRETURN (xa, NONE))
          | SOME _ => DRETURN (xa, xb)))
  end;

fun red_dfs_impla u v onstack e = the_res (red_dfs_impl_0a onstack e (v, u));

fun fun_ndfs_impl_0 succi ai x =
  let
    val (a, (aa, (ab, bb))) = x;
    val xa = map2set_insert (rbt_insert ord_nat) bb a;
    val xb = map2set_insert (rbt_insert ord_nat) bb ab;
  in
    dbind (foldli (succi bb)
            (fn ac =>
              (case ac of DSUCCEEDi => false | DFAILi => false
                | DRETURN (_, (_, (_, xh))) =>
                  equal_blue_witness equal_nat xh NO_CYC))
            (fn xc => fn s =>
              dbind s
                (fn (ac, (ad, (ae, be))) =>
                  (if not (map2set_memb (fn k => fn t => rbt_lookup ord_nat t k)
                            xc ac)
                    then dbind (fun_ndfs_impl_0 succi ai (ac, (ad, (ae, xc))))
                           (fn (af, (ag, (ah, bh))) =>
                             DRETURN
                               (af, (ag, (ah, prep_wit_blue equal_nat bb bh))))
                    else DRETURN (ac, (ad, (ae, be))))))
            (DRETURN (xa, (aa, (xb, NO_CYC)))))
      (fn (ac, (ad, (ae, be))) =>
        dbind (if equal_blue_witness equal_nat be NO_CYC andalso
                    map2set_memb (fn k => fn t => rbt_lookup ord_nat t k) bb ai
                then let
                       val (af, bf) = red_dfs_impla bb ad ae succi;
                     in
                       DRETURN (af, init_wit_blue equal_nat bb bf)
                     end
                else DRETURN (ad, be))
          (fn (af, bf) => let
                            val xe = rbt_delete less_nat bb ae;
                          in
                            DRETURN (ac, (af, (xe, bf)))
                          end))
  end;

fun fun_ndfs_impl succi ai s =
  the_res
    (dbind (fun_ndfs_impl_0 succi ai (Empty, (Empty, (Empty, s))))
      (fn (_, (_, (_, bb))) => DRETURN (extract_res bb)));

fun red_dfs_impl_0b onstack e x =
  let
    val (a, b) = x;
    val xa = map2set_insert iam_update b a;
  in
    dbind (foldli (e b)
            (fn aa =>
              (case aa of DSUCCEEDi => false | DFAILi => false
                | DRETURN ab => is_None ab))
            (fn xb => fn s =>
              dbind s
                (fn _ =>
                  (if map2set_memb iam_lookup xb onstack
                    then DRETURN (red_init_witness b xb) else DRETURN NONE)))
            (DRETURN NONE))
      (fn xb =>
        (case xb
          of NONE =>
            foldli (e b)
              (fn aa =>
                (case aa of DSUCCEEDi => false | DFAILi => false
                  | DRETURN ab => let
                                    val (_, ac) = ab;
                                  in
                                    is_None ac
                                  end))
              (fn xc => fn s =>
                dbind s
                  (fn (aa, _) =>
                    (if not (map2set_memb iam_lookup xc aa)
                      then dbind (red_dfs_impl_0b onstack e (aa, xc))
                             (fn (ab, bb) => DRETURN (ab, prep_wit_red b bb))
                      else DRETURN (aa, NONE))))
              (DRETURN (xa, NONE))
          | SOME _ => DRETURN (xa, xb)))
  end;

fun red_dfs_implb u v onstack e = the_res (red_dfs_impl_0b onstack e (v, u));

fun acc_of_list_impl x =
  (fn xa => fold (map2set_insert (rbt_insert ord_nat)) xa Empty) x;

fun fun_acc_of_list x = (acc_of_list_impl o map nat_of_integer) x;

fun funs_ndfs_impl_0 succi ai x =
  let
    val (a, (aa, (ab, bb))) = x;
    val xa = map2set_insert iam_update bb a;
    val xb = map2set_insert iam_update bb ab;
  in
    dbind (foldli (succi bb)
            (fn ac =>
              (case ac of DSUCCEEDi => false | DFAILi => false
                | DRETURN (_, (_, (_, xh))) =>
                  equal_blue_witness equal_nat xh NO_CYC))
            (fn xc => fn s =>
              dbind s
                (fn (ac, (ad, (ae, be))) =>
                  (if not (map2set_memb iam_lookup xc ac)
                    then dbind (funs_ndfs_impl_0 succi ai (ac, (ad, (ae, xc))))
                           (fn (af, (ag, (ah, bh))) =>
                             DRETURN
                               (af, (ag, (ah, prep_wit_blue equal_nat bb bh))))
                    else DRETURN (ac, (ad, (ae, be))))))
            (DRETURN (xa, (aa, (xb, NO_CYC)))))
      (fn (ac, (ad, (ae, be))) =>
        dbind (if equal_blue_witness equal_nat be NO_CYC andalso
                    map2set_memb iam_lookup bb ai
                then let
                       val (af, bf) = red_dfs_implb bb ad ae succi;
                     in
                       DRETURN (af, init_wit_blue equal_nat bb bf)
                     end
                else DRETURN (ad, be))
          (fn (af, bf) => let
                            val xe = iam_delete bb ae;
                          in
                            DRETURN (ac, (af, (xe, bf)))
                          end))
  end;

fun funs_ndfs_impl succi ai s =
  the_res
    (dbind
      (funs_ndfs_impl_0 succi ai
        (iam_empty (), (iam_empty (), (iam_empty (), s))))
      (fn (_, (_, (_, bb))) => DRETURN (extract_res bb)));

fun succ_of_list_impl x =
  (fn xa =>
    let
      val y =
        fold (fn (xaa, xb) => fn xc =>
               (case rbt_lookup ord_nat xc xaa
                 of NONE => rbt_insert ord_nat xaa [xb] xc
                 | SOME xd =>
                   rbt_insert ord_nat xaa (glist_insert equal_nata xb xd) xc))
          xa Empty;
    in
      (fn xaa => (case rbt_lookup ord_nat y xaa of NONE => [] | SOME xb => xb))
    end)
    x;

fun fun_succ_of_list x =
  (succ_of_list_impl o map (fn (u, v) => (nat_of_integer u, nat_of_integer v)))
    x;

fun acc_of_list_impla x =
  (fn xa => fold (map2set_insert iam_update) xa (iam_empty ())) x;

fun funs_acc_of_list x = (acc_of_list_impla o map nat_of_integer) x;

fun succ_of_list_impla x =
  (fn xa =>
    let
      val y =
        fold (fn (xaa, xb) => fn xc =>
               (case iam_alpha xc xaa of NONE => iam_update xaa [xb] xc
                 | SOME xd =>
                   iam_update xaa (glist_insert equal_nata xb xd) xc))
          xa (iam_empty ());
    in
      (fn xaa => (case iam_alpha y xaa of NONE => [] | SOME xb => xb))
    end)
    x;

fun funs_succ_of_list x =
  (succ_of_list_impla o map (fn (u, v) => (nat_of_integer u, nat_of_integer v)))
    x;

end; (*struct NDFS_Benchmark*)
