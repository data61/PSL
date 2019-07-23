(*  Title:      PSL/SeLFeE/src/Eval_Connective_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_CONNECTIVE =
sig

(*In principle, we only need NAND, and we can treat them as syntactic sugars.*)
datatype assert =
  True
| False
| Not   of assert
| And   of assert * assert
| Or    of assert * assert
| Nor   of assert * assert
| Imply of assert * assert
| Ands  of assert list
| Ors   of assert list;

val eval: assert -> assert;

val bool_to_assert_connective: bool -> assert;

end;