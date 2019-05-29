(* This Isabelle theory is produced using the TIP tool offered at the following website: 
     https://github.com/tip-org/tools 
   This file was originally provided as part of TIP benchmark at the following website:
     https://github.com/tip-org/benchmarks 
   Yutaka Nagashima at CIIRC, CTU changed the TIP output theory file slightly 
   to make it compatible with Isabelle2017.
\:w
   Some proofs were added by Yutaka Nagashima.*)
  theory TIP_polyrec_seq_index
imports "../../Test_Base"
begin

datatype ('a, 'b) pair = pair2 "'a" "'b"

datatype 'a list = nil2 | cons2 "'a" "'a list"

datatype 'a Maybe = Nothing | Just "'a"

datatype 'a Seq = Nil | Cons "'a" "(('a, ('a Maybe)) pair) Seq"

fun y :: "('a => 'b) => 'a Maybe => 'b Maybe" where
"y z (Nothing) = Nothing"
| "y z (Just z2) = Just (z z2)"

fun x :: "('a => 'b Maybe) => 'a Maybe => 'b Maybe" where
"x z (Nothing) = Nothing"
| "x z (Just z2) = z z2"

fun pair3 :: "'a list => (('a, ('a Maybe)) pair) list" where
"pair3 (nil2) = nil2"
| "pair3 (cons2 y2 (nil2)) = cons2 (pair2 y2 (Nothing)) (nil2)"
| "pair3 (cons2 y2 (cons2 y22 xs)) =
     cons2 (pair2 y2 (Just y22)) (pair3 xs)"

fun lookup :: "int => 'a list => 'a Maybe" where
"lookup z (nil2) = Nothing"
| "lookup z (cons2 z2 x2) =
     (if (z = 0) then Just z2 else lookup (z - 1) x2)"

fun index :: "int => 'a Seq => 'a Maybe" where
"index z (Nil) = Nothing"
| "index z (Cons z2 x2) =
     (if (z = 0) then Just z2 else
        (if ((mod z 2) = 0) then
           (case index ((op div) (z - 1) 2) x2 of
              Nothing => Nothing
              | Just x5 => (case x5 of pair2 x6 y3 => y3))
           else
           (case index ((op div) (z - 1) 2) x2 of
              Nothing => Nothing
              | Just x3 => (case x3 of pair2 x4 y22 => Just x4))))"

fun fromList :: "'a list => 'a Seq" where
"fromList (nil2) = Nil"
| "fromList (cons2 y2 xs) = Cons y2 (fromList (pair3 xs))"

theorem property0 :
  "((n >= 0) ==> ((lookup n xs) = (index n (fromList xs))))"
  oops

end
