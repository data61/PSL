(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_regexp_RecSeq
imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype A = X | Y

datatype R
         = Nil | Eps | Atom "A" | Plus "R" "R" | Seq "R" "R" | Star "R"

fun split :: "'a => ((('a list), ('a list)) pair) list =>
              ((('a list), ('a list)) pair) list" where
"split x (nil2) = nil2"
| "split x (cons2 (pair2 xs ys) x2) =
     cons2 (pair2 (cons2 x xs) ys) (split x x2)"

fun split2 :: "'a list => ((('a list), ('a list)) pair) list" where
"split2 (nil2) = cons2 (pair2 (nil2) (nil2)) (nil2)"
| "split2 (cons2 y s) =
     cons2 (pair2 (nil2) (cons2 y s)) (split y (split2 s))"

fun seq :: "R => R => R" where
"seq x y =
   (case x of
      Nil => Nil
      | other =>
          (case y of
             Nil => Nil
             | other =>
                 (case x of
                    Eps => y
                    | other =>
                        (case y of
                           Eps => x
                           | other => Seq x y))))"

fun plus :: "R => R => R" where
"plus x y =
   (case x of
      Nil => y
      | other =>
          (case y of
             Nil => x
             | other => Plus x y))"

fun or2 :: "bool list => bool" where
"or2 (nil2) = False"
| "or2 (cons2 y xs) = (y | (or2 xs))"

fun eqA :: "A => A => bool" where
"eqA (X) (X) = True"
| "eqA (X) (Y) = False"
| "eqA (Y) (X) = False"
| "eqA (Y) (Y) = True"

fun eps :: "R => bool" where
"eps x =
   (case x of
      Eps => True
      | Plus p q => ((eps p) | (eps q))
      | Seq r q2 => ((eps r) & (eps q2))
      | Star y => True
      | other => False)"

fun epsR :: "R => R" where
"epsR x = (if eps x then Eps else Nil)"

fun step :: "R => A => R" where
"step x y =
   (case x of
      Atom a => (if eqA a y then Eps else Nil)
      | Plus p q => plus (step p y) (step q y)
      | Seq r q2 => plus (seq (step r y) q2) (seq (epsR r) (step q2 y))
      | Star p2 => seq (step p2 y) x
      | other => Nil)"

fun recognise :: "R => A list => bool" where
"recognise x (nil2) = eps x"
| "recognise x (cons2 z xs) = recognise (step x z) xs"

fun formula :: "R => R => (((A list), (A list)) pair) list =>
              bool list" where
"formula p q (nil2) = nil2"
| "formula p q (cons2 (pair2 s1 s2) z) =
     cons2 ((recognise p s1) & (recognise q s2)) (formula p q z)"

theorem property0 :
  "((recognise (Seq p q) s) = (or2 (formula p q (split2 s))))"
  oops

end
