(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_regexp_RecPlus
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype A = X | Y

datatype R
         = Nil | Eps | Atom "A" | Plus "R" "R" | Seq "R" "R" | Star "R"

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

theorem property0 :
  "((recognise (Plus p q) s) = ((recognise p s) | (recognise q s)))"
  oops

end
