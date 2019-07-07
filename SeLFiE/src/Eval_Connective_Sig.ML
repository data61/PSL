(*  Title:      PSL/SeLFeE/src/Eval_Connective_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_CONNECTIVE =
sig

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert_connective =
  True
| False
| Not   of assert_connective
| And   of assert_connective * assert_connective
| Or    of assert_connective * assert_connective
| Nor   of assert_connective * assert_connective
| Imply of assert_connective * assert_connective;

val eval_connective: assert_connective -> assert_connective;

val bool_to_assert_connective: bool -> assert_connective;

end;