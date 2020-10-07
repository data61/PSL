(* Wrap around the Arith structure of isabelle
*
* Reason: Only one place to change things :)
* *)

structure Arith : sig
  type int
  type nat

  val of_nat : nat -> IntInf.int
  val of_int : int -> IntInf.int

  val nat : IntInf.int -> nat
  val int : IntInf.int -> int

  val nat_to_string : nat -> string
  val int_to_string : int -> string
end = struct
  type int = IsaArith.int
  type nat = IsaArith.nat

  val of_nat = IsaArith.integer_of_nat
  val of_int = IsaArith.integer_of_int
  val nat = IsaArith.nat_of_integer
  val int = IsaArith.Int_of_integer

  val nat_to_string = IntInf.toString o of_nat
  val int_to_string = IntInf.toString o of_int
end
