
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

structure Dijkstra : sig
  type nat
  val integer_of_nat : nat -> IntInf.int
  val nat_of_integer : IntInf.int -> nat
  type 'a infty
  type ('b, 'a) rbt
  type 'a dlist
  type ('b, 'a) hashmap
  val ran_graph : nat -> nat -> nat list * (nat * (nat * nat)) list
  val nat_dijkstra :
    (nat, (nat, nat dlist) hashmap) hashmap ->
      nat -> (nat, ((nat * (nat * nat)) list * nat)) rbt
  val nat_cr_graph_fun :
    nat -> (nat * (nat * nat)) list -> (nat, (nat, nat dlist) hashmap) hashmap
  val nat_cr_graph_imp :
    nat -> (nat * (nat * nat)) list -> (unit -> (((nat * nat) list) array))
  val nat_dijkstra_imp :
    nat ->
      ((nat * nat) list) array ->
        nat -> (unit -> ((((nat * (nat * nat)) list * nat) option) array))
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

type 'a semigroup_add = {plus_semigroup_add : 'a plus};
val plus_semigroup_add = #plus_semigroup_add : 'a semigroup_add -> 'a plus;

type 'a ab_semigroup_add = {semigroup_add_ab_semigroup_add : 'a semigroup_add};
val semigroup_add_ab_semigroup_add = #semigroup_add_ab_semigroup_add :
  'a ab_semigroup_add -> 'a semigroup_add;

type 'a preorder = {ord_preorder : 'a ord};
val ord_preorder = #ord_preorder : 'a preorder -> 'a ord;

type 'a order = {preorder_order : 'a preorder};
val preorder_order = #preorder_order : 'a order -> 'a preorder;

type 'a ordered_ab_semigroup_add =
  {ab_semigroup_add_ordered_ab_semigroup_add : 'a ab_semigroup_add,
    order_ordered_ab_semigroup_add : 'a order};
val ab_semigroup_add_ordered_ab_semigroup_add =
  #ab_semigroup_add_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a ab_semigroup_add;
val order_ordered_ab_semigroup_add = #order_ordered_ab_semigroup_add :
  'a ordered_ab_semigroup_add -> 'a order;

type 'a monoid_add =
  {semigroup_add_monoid_add : 'a semigroup_add, zero_monoid_add : 'a zero};
val semigroup_add_monoid_add = #semigroup_add_monoid_add :
  'a monoid_add -> 'a semigroup_add;
val zero_monoid_add = #zero_monoid_add : 'a monoid_add -> 'a zero;

type 'a comm_monoid_add =
  {ab_semigroup_add_comm_monoid_add : 'a ab_semigroup_add,
    monoid_add_comm_monoid_add : 'a monoid_add};
val ab_semigroup_add_comm_monoid_add = #ab_semigroup_add_comm_monoid_add :
  'a comm_monoid_add -> 'a ab_semigroup_add;
val monoid_add_comm_monoid_add = #monoid_add_comm_monoid_add :
  'a comm_monoid_add -> 'a monoid_add;

type 'a linorder = {order_linorder : 'a order};
val order_linorder = #order_linorder : 'a linorder -> 'a order;

type 'a weight =
  {comm_monoid_add_weight : 'a comm_monoid_add,
    ordered_ab_semigroup_add_weight : 'a ordered_ab_semigroup_add,
    linorder_weight : 'a linorder};
val comm_monoid_add_weight = #comm_monoid_add_weight :
  'a weight -> 'a comm_monoid_add;
val ordered_ab_semigroup_add_weight = #ordered_ab_semigroup_add_weight :
  'a weight -> 'a ordered_ab_semigroup_add;
val linorder_weight = #linorder_weight : 'a weight -> 'a linorder;

val semigroup_add_nat = {plus_semigroup_add = plus_nat} : nat semigroup_add;

val ab_semigroup_add_nat = {semigroup_add_ab_semigroup_add = semigroup_add_nat}
  : nat ab_semigroup_add;

val preorder_nat = {ord_preorder = ord_nat} : nat preorder;

val order_nat = {preorder_order = preorder_nat} : nat order;

val ordered_ab_semigroup_add_nat =
  {ab_semigroup_add_ordered_ab_semigroup_add = ab_semigroup_add_nat,
    order_ordered_ab_semigroup_add = order_nat}
  : nat ordered_ab_semigroup_add;

val monoid_add_nat =
  {semigroup_add_monoid_add = semigroup_add_nat, zero_monoid_add = zero_nat} :
  nat monoid_add;

val comm_monoid_add_nat =
  {ab_semigroup_add_comm_monoid_add = ab_semigroup_add_nat,
    monoid_add_comm_monoid_add = monoid_add_nat}
  : nat comm_monoid_add;

val linorder_nat = {order_linorder = order_nat} : nat linorder;

val weight_nat =
  {comm_monoid_add_weight = comm_monoid_add_nat,
    ordered_ab_semigroup_add_weight = ordered_ab_semigroup_add_nat,
    linorder_weight = linorder_nat}
  : nat weight;

fun max A_ a b = (if less_eq A_ a b then b else a);

val ord_integer =
  {less_eq = (fn a => fn b => IntInf.<= (a, b)),
    less = (fn a => fn b => IntInf.< (a, b))}
  : IntInf.int ord;

fun nat_of_integer k = Nat (max ord_integer (0 : IntInf.int) k);

datatype num = One | Bit0 of num | Bit1 of num;

fun def_hashmap_size_nat x = (fn _ => nat_of_integer (16 : IntInf.int)) x;

type 'a hashable =
  {hashcode : 'a -> Word32.word, def_hashmap_size : 'a itself -> nat};
val hashcode = #hashcode : 'a hashable -> 'a -> Word32.word;
val def_hashmap_size = #def_hashmap_size : 'a hashable -> 'a itself -> nat;

datatype int = Int_of_integer of IntInf.int;

fun int_of_nat n = Int_of_integer (integer_of_nat n);

fun integer_of_int (Int_of_integer k) = k;

fun uint32_of_int i = Word32.fromLargeInt (IntInf.toLarge (integer_of_int i));

fun hashcode_nat n = uint32_of_int (int_of_nat n);

val hashable_nat =
  {hashcode = hashcode_nat, def_hashmap_size = def_hashmap_size_nat} :
  nat hashable;

fun typerep_lista A_ t = Typerep ("List.list", [typerep A_ Type]);

fun countable_list A_ = {} : ('a list) countable;

fun typerep_list A_ = {typerep = typerep_lista A_} : ('a list) typerep;

fun heap_list A_ =
  {countable_heap = countable_list (countable_heap A_),
    typerep_heap = typerep_list (typerep_heap A_)}
  : ('a list) heap;

datatype 'a infty = Infty | Num of 'a;

fun typerep_inftya A_ t = Typerep ("Weight.infty", [typerep A_ Type]);

fun countable_infty A_ = {} : 'a infty countable;

fun typerep_infty A_ = {typerep = typerep_inftya A_} : 'a infty typerep;

fun heap_infty A_ =
  {countable_heap = countable_infty A_,
    typerep_heap = typerep_infty (typerep_heap A_)}
  : 'a infty heap;

fun less_eq_infty A_ Infty (Num uu) = false
  | less_eq_infty A_ uv Infty = true
  | less_eq_infty A_ (Num a) (Num b) =
    less_eq
      ((ord_preorder o preorder_order o order_linorder o linorder_weight) A_) a
      b;

fun less_infty A_ Infty uu = false
  | less_infty A_ (Num uv) Infty = true
  | less_infty A_ (Num a) (Num b) =
    less ((ord_preorder o preorder_order o order_linorder o linorder_weight) A_)
      a b;

fun ord_infty A_ = {less_eq = less_eq_infty A_, less = less_infty A_} :
  'a infty ord;

fun preorder_infty A_ = {ord_preorder = ord_infty A_} : 'a infty preorder;

fun order_infty A_ = {preorder_order = preorder_infty A_} : 'a infty order;

fun linorder_infty A_ = {order_linorder = order_infty A_} : 'a infty linorder;

fun typerep_optiona A_ t = Typerep ("Option.option", [typerep A_ Type]);

fun countable_option A_ = {} : ('a option) countable;

fun typerep_option A_ = {typerep = typerep_optiona A_} : ('a option) typerep;

fun heap_option A_ =
  {countable_heap = countable_option (countable_heap A_),
    typerep_heap = typerep_option (typerep_heap A_)}
  : ('a option) heap;

val ord_uint32 =
  {less_eq = (fn a => fn b => Word32.<= (a, b)),
    less = (fn a => fn b => Word32.< (a, b))}
  : Word32.word ord;

val preorder_uint32 = {ord_preorder = ord_uint32} : Word32.word preorder;

val order_uint32 = {preorder_order = preorder_uint32} : Word32.word order;

val linorder_uint32 = {order_linorder = order_uint32} : Word32.word linorder;

fun typerep_proda A_ B_ t =
  Typerep ("Product_Type.prod", [typerep A_ Type, typerep B_ Type]);

fun countable_prod A_ B_ = {} : ('a * 'b) countable;

fun typerep_prod A_ B_ = {typerep = typerep_proda A_ B_} : ('a * 'b) typerep;

fun heap_prod A_ B_ =
  {countable_heap = countable_prod (countable_heap A_) (countable_heap B_),
    typerep_heap = typerep_prod (typerep_heap A_) (typerep_heap B_)}
  : ('a * 'b) heap;

datatype ('a, 'b) lp = Inftya | LP of 'a * 'b;

fun min A_ a b = (if less_eq A_ a b then a else b);

fun p_min A_ B_ Inftya Inftya = Inftya
  | p_min A_ B_ Inftya (LP (e, a)) = LP (e, a)
  | p_min A_ B_ (LP (e, a)) Inftya = LP (e, a)
  | p_min A_ B_ (LP (e1, a)) (LP (e2, b)) =
    LP (max ((ord_preorder o preorder_order o order_linorder) A_) e1 e2,
         min ((ord_preorder o preorder_order o order_linorder) B_) a b);

fun plus_LPa A_ B_ a b = p_min A_ B_ a b;

fun plus_LP A_ B_ = {plus = plus_LPa A_ B_} : ('a, 'b) lp plus;

fun zero_LPa A_ B_ = Inftya;

fun zero_LP A_ B_ = {zero = zero_LPa A_ B_} : ('a, 'b) lp zero;

fun semigroup_add_LP A_ B_ = {plus_semigroup_add = plus_LP A_ B_} :
  ('a, 'b) lp semigroup_add;

fun monoid_add_LP A_ B_ =
  {semigroup_add_monoid_add = semigroup_add_LP A_ B_,
    zero_monoid_add = zero_LP A_ B_}
  : ('a, 'b) lp monoid_add;

datatype color = R | B;

datatype ('a, 'b) rbta = Empty |
  Branch of color * ('a, 'b) rbta * 'a * 'b * ('a, 'b) rbta;

datatype ('b, 'a) rbt = RBT of ('b, 'a) rbta;

datatype 'a dlist = Dlist of 'a list;

datatype ('a, 'b) node = Tip of 'a * 'b |
  Node2 of 'b * ('a, 'b) node * ('a, 'b) node |
  Node3 of 'b * ('a, 'b) node * ('a, 'b) node * ('a, 'b) node;

datatype ('b, 'a) assoc_list = Assoc_List of ('b * 'a) list;

datatype ('b, 'a) hashmap = RBT_HM of (Word32.word, ('b, 'a) assoc_list) rbt;

datatype ('a, 'b) digit = Onea of ('a, 'b) node |
  Two of ('a, 'b) node * ('a, 'b) node |
  Three of ('a, 'b) node * ('a, 'b) node * ('a, 'b) node |
  Four of ('a, 'b) node * ('a, 'b) node * ('a, 'b) node * ('a, 'b) node;

datatype ('a, 'b) fingerTreeStruc = Emptya | Single of ('a, 'b) node |
  Deep of 'b * ('a, 'b) digit * ('a, 'b) fingerTreeStruc * ('a, 'b) digit;

datatype ('b, 'a) splitres =
  Abs_splitres of
    (('b, 'a) fingerTreeStruc * (('b * 'a) * ('b, 'a) fingerTreeStruc));

datatype ('b, 'a) fingerTree = Abs_FingerTree of ('b, 'a) fingerTreeStruc;

fun eq A_ a b = equal A_ a b;

val one_nat : nat = Nat (1 : IntInf.int);

fun suc n = plus_nata n one_nat;

fun upt i j = (if less_nat i j then i :: upt (suc i) j else []);

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

fun empty A_ = RBT Empty;

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun map_of A_ ((l, v) :: ps) k = (if eq A_ l k then SOME v else map_of A_ ps k)
  | map_of A_ [] k = NONE;

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

fun rbt_ins A_ f k v Empty = Branch (R, Empty, k, v, Empty)
  | rbt_ins A_ f k v (Branch (B, l, x, y, r)) =
    (if less A_ k x then balance (rbt_ins A_ f k v l) x y r
      else (if less A_ x k then balance l x y (rbt_ins A_ f k v r)
             else Branch (B, l, x, f k y v, r)))
  | rbt_ins A_ f k v (Branch (R, l, x, y, r)) =
    (if less A_ k x then Branch (R, rbt_ins A_ f k v l, x, y, r)
      else (if less A_ x k then Branch (R, l, x, y, rbt_ins A_ f k v r)
             else Branch (R, l, x, f k y v, r)));

fun paint c Empty = Empty
  | paint c (Branch (uu, l, k, v, r)) = Branch (c, l, k, v, r);

fun rbt_insert_with_key A_ f k v t = paint B (rbt_ins A_ f k v t);

fun rbt_insert A_ = rbt_insert_with_key A_ (fn _ => fn _ => fn nv => nv);

fun impl_of B_ (RBT x) = x;

fun insert A_ xc xd xe =
  RBT (rbt_insert ((ord_preorder o preorder_order o order_linorder) A_) xc xd
        (impl_of A_ xe));

fun rbt_lookup A_ Empty k = NONE
  | rbt_lookup A_ (Branch (uu, l, x, y, r)) k =
    (if less A_ k x then rbt_lookup A_ l k
      else (if less A_ x k then rbt_lookup A_ r k else SOME y));

fun lookup A_ x =
  rbt_lookup ((ord_preorder o preorder_order o order_linorder) A_)
    (impl_of A_ x);

fun vala (Num d) = d;

val emptya : 'a dlist = Dlist [];

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun inserta A_ x xs = (if member A_ xs x then xs else x :: xs);

fun list_of_dlist (Dlist x) = x;

fun insertb A_ x dxs = Dlist (inserta A_ x (list_of_dlist dxs));

fun foldli [] c f sigma = sigma
  | foldli (x :: xs) c f sigma =
    (if c sigma then foldli xs c f (f x sigma) else sigma);

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

fun snd (x1, x2) = x2;

fun modulo_integer k l = snd (divmod_integer k l);

fun modulo_nat m n = Nat (modulo_integer (integer_of_nat m) (integer_of_nat n));

fun times_nat m n = Nat (IntInf.* (integer_of_nat m, integer_of_nat n));

fun lcg_next s =
  modulo_nat
    (plus_nata (times_nat (nat_of_integer (81 : IntInf.int)) s)
      (nat_of_integer (173 : IntInf.int)))
    (nat_of_integer (268435456 : IntInf.int));

fun whilea b c s = (if b s then whilea b c (c s) else s);

fun fst (x1, x2) = x1;

fun ran_graph vertices seed =
  (upt zero_nata vertices,
    fst (whilea (fn (_, (v, _)) => less_nat v vertices)
          (fn (g, (v, s)) =>
            let
              val (ga, (_, sa)) =
                whilea (fn (_, (va, _)) => less_nat va vertices)
                  (fn (ga, (va, sa)) =>
                    ((v, (sa, va)) :: ga, (plus_nata va one_nat, lcg_next sa)))
                  (g, (zero_nata, s));
            in
              (ga, (plus_nata v one_nat, sa))
            end)
          ([], (zero_nata, lcg_next seed))));

fun blit A_ src si dst di len =
  (fn () => 
    array_blit src (integer_of_nat
                     si) dst (integer_of_nat di) (integer_of_nat len));

fun mpath NONE = NONE
  | mpath (SOME (p, w)) = SOME p;

val emptyb : ('a, 'b) assoc_list = Assoc_List [];

fun emptyc A_ = (fn _ => empty linorder_uint32);

fun hm_empty_const A_ = RBT_HM (emptyc A_ ());

fun hm_empty A_ = (fn _ => hm_empty_const A_);

fun nth_oo A_ v a = (fn b => array_nth_oo v a b) o integer_of_nat;

fun upd_oo A_ f =
  (fn a => fn b => fn c => array_upd_oo f a b c) o integer_of_nat;

fun impl_ofa (Assoc_List x) = x;

fun lookupa A_ al = map_of A_ (impl_ofa al);

fun update_with_aux B_ v k f [] = [(k, f v)]
  | update_with_aux B_ v k f (p :: ps) =
    (if eq B_ (fst p) k then (k, f (snd p)) :: ps
      else p :: update_with_aux B_ v k f ps);

fun update_with A_ v k f al =
  Assoc_List (update_with_aux A_ v k f (impl_ofa al));

fun update A_ k v = update_with A_ v k (fn _ => v);

fun impl_of_RBT_HM B_ (RBT_HM x) = x;

fun lookupb (A1_, A2_) k m =
  (case lookup linorder_uint32 m (hashcode A2_ k) of NONE => NONE
    | SOME lm => lookupa A1_ lm k);

fun hm_lookup (A1_, A2_) k hm = lookupb (A1_, A2_) k (impl_of_RBT_HM A2_ hm);

fun updatea (A1_, A2_) k v m =
  let
    val hc = hashcode A2_ k;
  in
    (case lookup linorder_uint32 m hc
      of NONE => insert linorder_uint32 hc (update A1_ k v emptyb) m
      | SOME bm => insert linorder_uint32 hc (update A1_ k v bm) m)
  end;

fun hm_update (A1_, A2_) k v hm =
  RBT_HM (updatea (A1_, A2_) k v (impl_of_RBT_HM A2_ hm));

fun the (SOME x2) = x2;

fun set_iterator_image g it = (fn c => fn f => it c (fn x => f (g x)));

fun map_iterator_dom it = set_iterator_image fst it;

fun iteratei al c f = foldli (impl_ofa al) c f;

fun iteratei_map_op_list_it_lm_ops s = iteratei s;

fun rm_iterateoi Empty c f sigma = sigma
  | rm_iterateoi (Branch (col, l, k, v, r)) c f sigma =
    (if c sigma
      then let
             val sigmaa = rm_iterateoi l c f sigma;
           in
             (if c sigmaa then rm_iterateoi r c f (f (k, v) sigmaa) else sigmaa)
           end
      else sigma);

fun iteratei_map_op_list_it_rm_ops A_ s = rm_iterateoi (impl_of A_ s);

fun iterateia A_ m c f sigma_0 =
  iteratei_map_op_list_it_rm_ops A_ m c
    (fn (_, lm) => iteratei_map_op_list_it_lm_ops lm c f) sigma_0;

fun hm_iteratei A_ hm = iterateia linorder_uint32 (impl_of_RBT_HM A_ hm);

fun nodes_it_gop_nodes_list_it_hlg_ops A_ g =
  map_iterator_dom (hm_iteratei A_ g);

fun set_iterator_product it_a it_b =
  (fn c => fn f => it_a c (fn a => it_b a c (fn b => f (a, b))));

fun set_iterator_emp c f sigma_0 = sigma_0;

fun dlist_iteratei xs = foldli (list_of_dlist xs);

fun succ_it_gop_succ_list_it_hlg_ops (A1_, A2_) g v =
  (case hm_lookup (A1_, A2_) v g of NONE => set_iterator_emp
    | SOME m2 =>
      set_iterator_image (fn (a, b) => let
 val (va, _) = a;
                                       in
 (fn w => (w, va))
                                       end
 b)
        (set_iterator_product (hm_iteratei A2_ m2)
          (fn (_, a) => dlist_iteratei a)));

fun aluprio_isEmpty isEmpty = isEmpty;

fun e_less_eq A_ B_ e Inftya = false
  | e_less_eq A_ B_ ea (LP (e, uu)) =
    less_eq ((ord_preorder o preorder_order o order_linorder) A_) ea e;

fun p_unwrap (LP (e, a)) = (e, a);

fun aluprio_insert A_ B_ splits annot isEmpty app consr s e a =
  (if e_less_eq A_ B_ e (annot s) andalso not (isEmpty s)
    then let
           val b = splits (e_less_eq A_ B_ e) Inftya s;
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
  | p_less_eq B_ uu Inftya = true
  | p_less_eq B_ Inftya (LP (e, a)) = false;

fun less_eq_LP B_ = p_less_eq B_;

fun aluprio_pop A_ B_ splits annot app s =
  let
    val a = splits (fn x => less_eq_LP B_ x (annot s)) Inftya s;
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

fun plus_infty A_ uu Infty = Infty
  | plus_infty A_ Infty (Num v) = Infty
  | plus_infty A_ (Num a) (Num b) =
    Num (plus ((plus_semigroup_add o semigroup_add_monoid_add o
                 monoid_add_comm_monoid_add o comm_monoid_add_weight)
                A_)
          a b);

fun isEmptya t =
  (case t of Emptya => true | Single _ => false | Deep (_, _, _, _) => false);

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

fun gmft B_ Emptya = zero (zero_monoid_add B_)
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

fun nlcons B_ a Emptya = Single a
  | nlcons B_ a (Single b) = deep B_ (Onea a) Emptya (Onea b)
  | nlcons B_ a (Deep (uu, Onea b, m, sf)) = deep B_ (Two (a, b)) m sf
  | nlcons B_ a (Deep (uv, Two (b, c), m, sf)) = deep B_ (Three (a, b, c)) m sf
  | nlcons B_ a (Deep (uw, Three (b, c, d), m, sf)) =
    deep B_ (Four (a, b, c, d)) m sf
  | nlcons B_ a (Deep (ux, Four (b, c, d, e), m, sf)) =
    deep B_ (Two (a, b)) (nlcons B_ (node3 B_ c d e) m) sf;

fun lconsNlist B_ [] t = t
  | lconsNlist B_ (x :: xs) t = nlcons B_ x (lconsNlist B_ xs t);

fun nlistToTree B_ xs = lconsNlist B_ xs Emptya;

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
  | digitToTree B_ (Two (a, b)) = deep B_ (Onea a) Emptya (Onea b)
  | digitToTree B_ (Three (a, b, c)) = deep B_ (Two (a, b)) Emptya (Onea c)
  | digitToTree B_ (Four (a, b, c, d)) =
    deep B_ (Two (a, b)) Emptya (Two (c, d));

fun viewRn B_ Emptya = NONE
  | viewRn B_ (Single a) = SOME (a, Emptya)
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

fun viewLn B_ Emptya = NONE
  | viewLn B_ (Single a) = SOME (a, Emptya)
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

fun nsplitTree A_ p i Emptya =
  (Emptya, (Tip ((raise Fail "undefined"), (raise Fail "undefined")), Emptya))
  | nsplitTree A_ p i (Single ea) = (Emptya, (ea, Emptya))
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
      else (Emptya, ((raise Fail "undefined"), Emptya)));

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

fun emptyd B_ = Abs_FingerTree Emptya;

fun ft_empty B_ = (fn _ => emptyd B_);

fun nrcons B_ Emptya a = Single a
  | nrcons B_ (Single b) a = deep B_ (Onea b) Emptya (Onea a)
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

fun app3 B_ Emptya xs t = lconsNlist B_ xs t
  | app3 B_ (Single v) xs Emptya = rconsNlist B_ (Single v) xs
  | app3 B_ (Deep (v, va, vb, vc)) xs Emptya =
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

fun top_infty A_ = Infty;

fun mpath_weight B_ NONE = top_infty B_
  | mpath_weight B_ (SOME (p, w)) = Num w;

fun cdijkstra_hlg_ops_rm_ops_aluprioi_ops (A1_, A2_, A3_) B_ g v0 =
  let
    val x =
      let
        val x =
          nodes_it_gop_nodes_list_it_hlg_ops A2_ g (fn _ => true)
            (fn x => fn sigma =>
              aluprio_insert A3_ (linorder_infty B_)
                (ft_splits (monoid_add_LP A3_ (linorder_infty B_)))
                (ft_annot (monoid_add_LP A3_ (linorder_infty B_)))
                (ft_isEmpty (monoid_add_LP A3_ (linorder_infty B_)))
                (ft_app (monoid_add_LP A3_ (linorder_infty B_)))
                (ft_consr (monoid_add_LP A3_ (linorder_infty B_))) sigma x
                Infty)
            (aluprio_empty (ft_empty (monoid_add_LP A3_ (linorder_infty B_)))
              ());
      in
        (aluprio_insert A3_ (linorder_infty B_)
           (ft_splits (monoid_add_LP A3_ (linorder_infty B_)))
           (ft_annot (monoid_add_LP A3_ (linorder_infty B_)))
           (ft_isEmpty (monoid_add_LP A3_ (linorder_infty B_)))
           (ft_app (monoid_add_LP A3_ (linorder_infty B_)))
           (ft_consr (monoid_add_LP A3_ (linorder_infty B_))) x v0
           (Num (zero ((zero_monoid_add o monoid_add_comm_monoid_add o
                         comm_monoid_add_weight)
                        B_))),
          insert A3_ v0
            ([], zero ((zero_monoid_add o monoid_add_comm_monoid_add o
                         comm_monoid_add_weight)
                        B_))
            (empty A3_))
      end;
    val (_, b) =
      whilea
        (fn (xb, _) =>
          not (aluprio_isEmpty
                (ft_isEmpty (monoid_add_LP A3_ (linorder_infty B_))) xb))
        (fn xa =>
          let
            val a =
              let
                val a = xa;
                val (aa, b) = a;
                val (aaa, (ab, bb)) =
                  aluprio_pop A3_ (linorder_infty B_)
                    (ft_splits (monoid_add_LP A3_ (linorder_infty B_)))
                    (ft_annot (monoid_add_LP A3_ (linorder_infty B_)))
                    (ft_app (monoid_add_LP A3_ (linorder_infty B_))) aa;
              in
                (aaa, (ab, (bb, b)))
              end;
            val (ac, (aa, (ab, bb))) = a;
            val xd = mpath (lookup A3_ bb ac);
          in
            succ_it_gop_succ_list_it_hlg_ops (A1_, A2_) g ac (fn _ => true)
              (fn xe => fn sigma =>
                let
                  val (aca, bc) = xe;
                  val (ad, bd) = sigma;
                in
                  (if less_infty B_ (plus_infty B_ aa (Num aca))
                        (mpath_weight B_ (lookup A3_ bd bc))
                    then (aluprio_insert A3_ (linorder_infty B_)
                            (ft_splits (monoid_add_LP A3_ (linorder_infty B_)))
                            (ft_annot (monoid_add_LP A3_ (linorder_infty B_)))
                            (ft_isEmpty (monoid_add_LP A3_ (linorder_infty B_)))
                            (ft_app (monoid_add_LP A3_ (linorder_infty B_)))
                            (ft_consr (monoid_add_LP A3_ (linorder_infty B_)))
                            ad bc (plus_infty B_ aa (Num aca)),
                           insert A3_ bc
                             ((ac, (aca, bc)) :: the xd,
                               plus ((plus_semigroup_add o
                                       semigroup_add_monoid_add o
                                       monoid_add_comm_monoid_add o
                                       comm_monoid_add_weight)
                                      B_)
                                 (vala aa) aca)
                             bd)
                    else (ad, bd))
                end)
              (ab, bb)
          end)
        x;
  in
    b
  end;

fun hrf_dijkstra (A1_, A2_, A3_) B_ =
  cdijkstra_hlg_ops_rm_ops_aluprioi_ops (A1_, A2_, A3_) B_;

fun hrfn_dijkstra x =
  hrf_dijkstra (equal_nat, hashable_nat, linorder_nat) weight_nat x;

fun nat_dijkstra x = hrfn_dijkstra x;

fun succi A_ g v =
  (fn () =>
    let
      val l = len (heap_list (heap_prod A_ heap_nat)) g ();
    in
      (if less_nat v l
        then (fn f_ => fn () => f_
               ((nth (heap_list (heap_prod A_ heap_nat)) g v) ()) ())
               (fn a => (fn () => a))
        else (fn () => []))
        ()
    end);

fun array_grow A_ a s x =
  (fn () =>
    let
      val l = len A_ a ();
    in
      (if equal_nata l s then (fn () => a)
        else (fn f_ => fn () => f_ ((new A_ s x) ()) ())
               (fn aa =>
                 (fn f_ => fn () => f_ ((blit A_ a zero_nata aa zero_nata l) ())
                   ())
                   (fn _ => (fn () => aa))))
        ()
    end);

fun gga_from_list e a u l =
  let
    val (nl, el) = l;
    val g1 = foldl (fn g => fn v => a v g) (e ()) nl;
  in
    foldl (fn g => fn (v, (ea, va)) => u v ea va g) g1 el
  end;

val iam_initial_size : nat = nat_of_integer (8 : IntInf.int);

fun iam_new_sz A_ sz = new (heap_option A_) sz NONE;

fun iam_new A_ = iam_new_sz A_ iam_initial_size;

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

fun cr_graph A_ numV es =
  (fn () =>
    let
      val a = new (heap_list (heap_prod A_ heap_nat)) numV [] ();
      val x =
        imp_nfoldli es (fn _ => (fn () => true))
          (fn (u, (v, w)) => fn aa =>
            (fn f_ => fn () => f_
              ((nth (heap_list (heap_prod A_ heap_nat)) aa u) ()) ())
              (fn l =>
                let
                  val la = (w, v) :: l;
                in
                  (fn f_ => fn () => f_
                    ((upd (heap_list (heap_prod A_ heap_nat)) u la aa) ()) ())
                    (fn ab => (fn () => ab))
                end))
          a ();
    in
      x
    end);

fun g_sng_ls_basic_ops A_ x = insertb A_ x emptya;

fun g_sng_hm_basic_ops (A1_, A2_) k v =
  hm_update (A1_, A2_) k v (hm_empty A2_ ());

fun gbm_add_edge_hm_ops_hm_ops_ls_ops (A1_, A2_) B_ va e v g =
  let
    val ga =
      (case hm_lookup (A1_, A2_) v g
        of NONE => hm_update (A1_, A2_) v (hm_empty A2_ ()) g | SOME _ => g);
  in
    (case hm_lookup (A1_, A2_) va ga
      of NONE =>
        hm_update (A1_, A2_) va
          (g_sng_hm_basic_ops (A1_, A2_) v (g_sng_ls_basic_ops B_ e)) ga
      | SOME m2 =>
        (case hm_lookup (A1_, A2_) v m2
          of NONE =>
            hm_update (A1_, A2_) va
              (hm_update (A1_, A2_) v (g_sng_ls_basic_ops B_ e) m2) ga
          | SOME s3 =>
            hm_update (A1_, A2_) va
              (hm_update (A1_, A2_) v (insertb B_ e s3) m2) ga))
  end;

fun gbm_add_node_hm_ops_hm_ops (A1_, A2_) v g =
  (case hm_lookup (A1_, A2_) v g
    of NONE => hm_update (A1_, A2_) v (hm_empty A2_ ()) g | SOME _ => g);

fun gbm_empty_hm_ops A_ = hm_empty A_;

fun gbm_from_list_hm_ops_hm_ops_ls_ops (A1_, A2_) B_ =
  gga_from_list (gbm_empty_hm_ops A2_) (gbm_add_node_hm_ops_hm_ops (A1_, A2_))
    (gbm_add_edge_hm_ops_hm_ops_ls_ops (A1_, A2_) B_);

fun hlg_from_list_nat x =
  gbm_from_list_hm_ops_hm_ops_ls_ops (equal_nat, hashable_nat) equal_nat x;

fun nodes_impl A_ gi =
  (fn () => let
              val l = len (heap_list (heap_prod A_ heap_nat)) gi ();
            in
              upt zero_nata l
            end);

fun iam_lookup A_ k a = nth_oo (heap_option A_) NONE a k;

fun iam_update A_ k v a =
  upd_oo (heap_option A_)
    (fn () =>
      let
        val l = len (heap_option A_) a ();
      in
        let
          val newsz =
            max ord_nat (plus_nata k one_nat)
              (plus_nata (times_nat (nat_of_integer (2 : IntInf.int)) l)
                (nat_of_integer (3 : IntInf.int)));
        in
          (fn f_ => fn () => f_ ((array_grow (heap_option A_) a newsz NONE) ())
            ())
            (upd (heap_option A_) k (SOME v))
        end
          ()
      end)
    k (SOME v) a;

fun op_list_prepend x = (fn a => x :: a);

fun marl_get A_ = (fn (a, _) => nth A_ a);

fun marl_set A_ =
  (fn (a, n) => fn i => fn x => fn () => let
   val aa = upd A_ i x a ();
 in
   (aa, n)
 end);

fun minus_nat m n =
  Nat (max ord_integer (0 : IntInf.int)
        (IntInf.- (integer_of_nat m, integer_of_nat n)));

fun heap_WHILET b f s =
  (fn () =>
    let
      val bv = b s ();
    in
      (if bv then (fn f_ => fn () => f_ ((f s) ()) ()) (heap_WHILET b f)
        else (fn () => s))
        ()
    end);

fun marl_length A_ = (fn (_, a) => (fn () => a));

fun marl_butlast A_ = (fn (a, n) => (fn () => (a, minus_nat n one_nat)));

fun infty_less_impl lessi =
  (fn ai => fn bi =>
    (case ai of Infty => (fn () => false)
      | Num x1a =>
        (case bi of Infty => (fn () => true) | Num a => lessi x1a a)));

fun infty_plus_impl plusi =
  (fn ai => fn bi =>
    (case ai of Infty => (fn () => Infty)
      | Num x1a =>
        (case bi of Infty => (fn () => Infty)
          | Num x1aa => (fn () => let
                                    val x = plusi x1a x1aa ();
                                  in
                                    Num x
                                  end))));

fun ial_length x = (fn (a1, _) => marl_length heap_nat a1) x;

fun hm_length_impl A_ = (fn (a1, _) => ial_length a1);

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

fun hm_exch_op_impl A_ =
  (fn ai => fn bia => fn bi =>
    let
      val (a1, a2) = ai;
    in
      (fn () =>
        let
          val x = ial_swap a1 (minus_nat bia one_nat) (minus_nat bi one_nat) ();
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
                    ((if equal_nata xb zero_nata then new A_ maxsize k
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

fun hm_upd_op_impl A_ B_ maxsize prio hm k v =
  let
    val (a1, a2) = v;
    val (a1a, _) = a1;
    val ((_, a2a), _) = v;
  in
    (fn () =>
      let
        val x =
          (if less_nat hm maxsize
            then (fn f_ => fn () => f_ ((nth heap_nat a2a hm) ()) ())
                   (fn x_a => (fn () => (less_nat x_a maxsize)))
            else (fn () => false))
            ();
      in
        (if x then (fn f_ => fn () => f_ ((nth heap_nat a2a hm) ()) ())
                     (fn xa =>
                       (fn f_ => fn () => f_ ((let
         val (a, _) = a1a;
       in
         nth heap_nat a
       end
        xa)
                         ()) ())
                         (fn xaa =>
                           (fn f_ => fn () => f_ ((upd A_ xaa k a2) ()) ())
                             (fn xab =>
                               hm_repair_op_impl A_ B_ prio (a1, xab)
                                 (suc xa))))
          else hm_insert_op_impl A_ B_ maxsize prio hm k v)
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

fun nat_cr_graph_fun nn es = hlg_from_list_nat (upt zero_nata nn, es);

fun nat_cr_graph_imp x = cr_graph heap_nat x;

fun hm_is_empty_op_impl A_ =
  (fn xi => fn () => let
                       val x = hm_length_impl A_ xi ();
                     in
                       equal_nata x zero_nata
                     end);

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
                          (if equal_nata b (suc zero_nata)
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

fun nat_dijkstra_imp n =
  (fn ai => fn bi => fn () =>
    let
      val x = nodes_impl heap_nat ai ();
      val xa = hm_empty_op_impl (heap_infty heap_nat) n ();
      val xb =
        imp_nfoldli x (fn _ => (fn () => true))
          (fn xb =>
            hm_upd_op_impl (heap_infty heap_nat) (linorder_infty weight_nat) n
              (fn xc => xc) xb Infty)
          xa ();
      val xc =
        hm_upd_op_impl (heap_infty heap_nat) (linorder_infty weight_nat) n
          (fn xc => xc) bi (Num zero_nata) xb ();
      val xaa =
        iam_new
          (heap_prod
            (heap_list (heap_prod heap_nat (heap_prod heap_nat heap_nat)))
            heap_nat)
          ();
      val xab =
        iam_update
          (heap_prod
            (heap_list (heap_prod heap_nat (heap_prod heap_nat heap_nat)))
            heap_nat)
          bi ([], zero_nata) xaa ();
      val a =
        heap_WHILET
          (fn (a1, _) =>
            (fn f_ => fn () => f_
              ((hm_is_empty_op_impl (heap_infty heap_nat) a1) ()) ())
              (fn x_a => (fn () => (not x_a))))
          (fn s =>
            (fn f_ => fn () => f_
              (let
                 val (a1, a2) = s;
               in
                 (fn f_ => fn () => f_
                   ((hm_pop_min_op_impl (heap_infty heap_nat)
                      (linorder_infty weight_nat) (fn xd => xd) a1)
                   ()) ())
                   (fn xd =>
                     (fn () =>
                       let
                         val (a1a, (a1b, a2b)) = let
           val ((a1b, a2b), a2a) = xd;
         in
           (a1b, (a2b, a2a))
         end;
                       in
                         (a1a, (a1b, (a2b, a2)))
                       end))
               end
              ()) ())
              (fn (a1, (a1a, (a1b, a2b))) =>
                (fn f_ => fn () => f_
                  ((iam_lookup
                     (heap_prod
                       (heap_list
                         (heap_prod heap_nat (heap_prod heap_nat heap_nat)))
                       heap_nat)
                     a1 a2b)
                  ()) ())
                  (fn xd =>
                    (fn f_ => fn () => f_ ((succi heap_nat ai a1) ()) ())
                      (fn x_e =>
                        imp_nfoldli x_e (fn _ => (fn () => true))
                          (fn xg => fn sigma =>
                            let
                              val (a1c, a2c) = xg;
                              val (a1d, a2d) = sigma;
                            in
                              (fn f_ => fn () => f_
                                ((infty_plus_impl
                                   (fn xe =>
                                     (fn a => (fn () => a)) o plus_nata xe)
                                   a1a (Num a1c))
                                ()) ())
                                (fn xac =>
                                  (fn f_ => fn () => f_
                                    ((iam_lookup
                                       (heap_prod
 (heap_list (heap_prod heap_nat (heap_prod heap_nat heap_nat))) heap_nat)
                                       a2c a2d)
                                    ()) ())
                                    (fn xba =>
                                      (fn f_ => fn () => f_
((infty_less_impl (fn xe => (fn a => (fn () => a)) o less_nat xe) xac
   (mpath_weight weight_nat xba))
()) ())
(fn x_h =>
  (if x_h
    then (fn f_ => fn () => f_
           ((infty_plus_impl (fn xe => (fn a => (fn () => a)) o plus_nata xe)
              a1a (Num a1c))
           ()) ())
           (fn xad =>
             (fn f_ => fn () => f_
               ((hm_upd_op_impl (heap_infty heap_nat)
                  (linorder_infty weight_nat) n (fn xe => xe) a2c xad a1d)
               ()) ())
               (fn x_i =>
                 (fn f_ => fn () => f_
                   ((iam_update
                      (heap_prod
                        (heap_list
                          (heap_prod heap_nat (heap_prod heap_nat heap_nat)))
                        heap_nat)
                      a2c (op_list_prepend (a1, (a1c, a2c)) (the (mpath xd)),
                            plus_nata (vala a1a) a1c)
                      a2d)
                   ()) ())
                   (fn x_j => (fn () => (x_i, x_j)))))
    else (fn () => (a1d, a2d))))))
                            end)
                          (a1b, a2b)))))
          (xc, xab) ();
    in
      let
        val (_, aa) = a;
      in
        (fn () => aa)
      end
        ()
    end);

end; (*struct Dijkstra*)
