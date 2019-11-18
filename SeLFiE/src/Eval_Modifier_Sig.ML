(*  Title:      PSL/SeLFeE/src/Eval_Modifier_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)
signature EVAL_MODIFIER =
sig

type print         = LiFtEr_Util.print;
type prints        = LiFtEr_Util.prints;
type outer_unode   = unit (*TODO*);
type number        = Eval_Number.number;
datatype modifiers = Modifiers of {ons:   prints,
                                   arbs:  prints,
                                   rules: prints};

datatype assert =
  Is_Nth_Ind       of print   * number (*Counting starts with 0.*)
| Is_Nth_Arb       of print   * number (*Counting starts with 0.*);

val eval: modifiers -> assert -> Eval_Connective.assert;

end;