(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
signature LIFTER =
sig

type abs_pstate_w_aux;

datatype numb       = Nth         of int;
datatype subtrm     = Sub_Trm     of int;
datatype rule       = Rule        of int;
datatype subtrm_occ = Sub_Trm_Occ of int;
datatype hol_typ    = Fun | List | Nat | Set | Rec;(*commonly used HOL types*)
datatype pattern    = Pttrn (*TODO*)
datatype assrt      =
(*quantifiers*)
  All_Ind        of subtrm * assrt
| All_Arb        of subtrm * assrt
| All_Sub_Trm    of subtrm * assrt
| All_Rule       of rule   * assrt
| All_Nth        of numb   * assrt
| Some_Ind       of subtrm * assrt
| Some_Arb       of subtrm * assrt
| Some_Sub_Trm   of subtrm * assrt
| Some_Rule      of rule   * assrt
| Some_Nth       of numb   * assrt (*n must be smaller than or equal to the argument number of the variable/constant that has the maximum argument number.*)
(*quantifiers for occurrences*)
| All_Ind_Occ    of subtrm_occ * subtrm * assrt
| All_Arb_Occ    of subtrm_occ * subtrm * assrt
| Some_Ind_Occ   of subtrm_occ * subtrm * assrt
| Some_Arb_Occ   of subtrm_occ * subtrm * assrt
| Some_Rule_Occ  of rule       * rule   * assrt
(*combinators*)
| And            of assrt * assrt
| Or             of assrt * assrt
| Not            of assrt
| Imply          of assrt * assrt
(*atomic about proof goal*)
| Is_Numb_Arg_Of of subtrm_occ * numb * subtrm_occ (*sub-tree-1 is the numb-th argument of sub-tree-2*)
| Are_Same_Nth   of numb       * numb
| Are_Same_Str   of subtrm_occ * subtrm_occ (*subtrm*)
| Is_In_Trm_Loc  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 location-wise*)
| Is_In_Trm_Str  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_In_Trm_Sem  of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise but modulo lambda-abstraction*)
| Is_Typ         of subtrm_occ * typ
| Is_At_Deepest  of subtrm_occ
| Is_In_Chained  of subtrm_occ
| Is_In_Fst_Subg of subtrm_occ
| Is_In_Prems    of subtrm_occ
| Is_In_Cnclsn   of subtrm_occ
| Is_Atom        of subtrm_occ
| Is_Cnst        of subtrm_occ
| Is_Var         of subtrm_occ
| Is_Free        of subtrm_occ
| Is_Lambda      of subtrm_occ (*lambda abstraction corresponding to Abs in Term*)
| Is_App         of subtrm_occ (*function application corresponding to $ in Term*)
| Not_Fully_App  of subtrm_occ (*If subtrm is function application that is not fully applied returns true, otherwise returns false.*)
| Is_Nth_Arg_Of  of subtrm_occ * numb* subtrm_occ
| Less           of numb       * numb(* nth_1 < nth_2 *)
(*atomic about induct method*)
| Is_Nth_Ind     of subtrm * numb
| Is_Nth_Arb     of subtrm * numb
(* TODO: pattern *)
| Pattern        of numb* subtrm * pattern (*In the definition of subtrm, the numb-th argument has this pattern.*)
(*syntax sugars*)
| Are_Diff_Nth   of numb       * numb(*Not & Are_Same_Nth*)
| Are_Diff_Str   of numb       * numb(*Not & Are_Same_Str*)
| Has_Typ        of subtrm_occ * typ (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Not_Deepest    of subtrm_occ       (*Not & Is_At_Deepest*)

datatype rule_name       = Rule_Name of string;
type path;
type paths;
type pathss;

(*Note that the name_space specified here is the name_space within each assertion:
 *Different assertions have different name_spaces.*)
datatype name_space = Name_Space of
 {subtrm:     (int * paths    ) list,
  subtrm_occ: (int * path     ) list,
  rule:       (int * rule_name) list,
  numb:       (int * numb     ) list};

type name_spaces = name_space list;

datatype name_domain = Name_Domain of
  {ind_domain    : pathss,
   ind_occ_domain: paths,
   arb_domain    : pathss,
   arb_occ_domain: paths,
   rule_domain   : strings};

val no_overlad: assrt -> bool;
val eval      : name_domain * abs_pstate_w_aux * assrt -> bool;

end;