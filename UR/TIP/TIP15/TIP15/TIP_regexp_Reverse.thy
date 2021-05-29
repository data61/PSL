(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.*)
  theory TIP_regexp_Reverse
imports "../../Test_Base"
begin

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype A = X | Y

datatype R
         = Nil | Eps | Atom "A" | Plus "R" "R" | Seq "R" "R" | Star "R"

fun x :: "'a list => 'a list => 'a list" where
"x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun seq :: "R => R => R" where
"seq y z =
   (case y of
      Nil => Nil
      | other =>
          (case z of
             Nil => Nil
             | other =>
                 (case y of
                    Eps => z
                    | other =>
                        (case z of
                           Eps => y
                           | other => Seq y z))))"

fun reverse :: "'a list => 'a list" where
"reverse (nil2) = nil2"
| "reverse (cons2 z xs) = x (reverse xs) (cons2 z (nil2))"

fun rev :: "R => R" where
"rev y =
   (case y of
      Plus a b => Plus (rev a) (rev b)
      | Seq c b2 => Seq (rev b2) (rev c)
      | Star a2 => Star (rev a2)
      | other => y)"

fun plus :: "R => R => R" where
"plus y z =
   (case y of
      Nil => z
      | other =>
          (case z of
             Nil => y
             | other => Plus y z))"

fun eqA :: "A => A => bool" where
"eqA (X) (X) = True"
| "eqA (X) (Y) = False"
| "eqA (Y) (X) = False"
| "eqA (Y) (Y) = True"

fun eps :: "R => bool" where
"eps y =
   (case y of
      Eps => True
      | Plus p q => ((eps p) | (eps q))
      | Seq r q2 => ((eps r) & (eps q2))
      | Star z => True
      | other => False)"

fun epsR :: "R => R" where
"epsR y = (if eps y then Eps else Nil)"

fun step :: "R => A => R" where
"step y z =
   (case y of
      Atom a => (if eqA a z then Eps else Nil)
      | Plus p q => plus (step p z) (step q z)
      | Seq r q2 => plus (seq (step r z) q2) (seq (epsR r) (step q2 z))
      | Star p2 => seq (step p2 z) y
      | other => Nil)"

fun recognise :: "R => A list => bool" where
"recognise y (nil2) = eps y"
| "recognise y (cons2 z2 xs) = recognise (step y z2) xs"

theorem property0 :
  "((recognise (rev r) s) = (recognise r (reverse s)))"
  oops

end
