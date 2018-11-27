(*  Title:      PSL/LiFtEr_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
signature LIFTER =

sig
datatype nth        = Nth         of int;
datatype subtrm     = Sub_Trm     of int;
datatype rule       = Rule        of int;
datatype subtrm_occ = Sub_Trm_Occ of int;
datatype rule_occ   = Rule_Occ    of int;
datatype hol_typ    = Fun | List | Nat | Set | Rec;(*commonly used HOL types*)
datatype assrt      =
(*quantifiers*)
  All_Ind        of subtrm * assrt
| All_Arb        of subtrm * assrt
| All_Sub_Trm    of subtrm * assrt
| All_Rule       of rule   * assrt
| All_Nth        of nth    * assrt
| Some_Ind       of subtrm * assrt
| Some_Arb       of subtrm * assrt
| Some_Sub_Trm   of subtrm * assrt
| Some_Rule      of rule   * assrt
| Some_Nth       of nth    * assrt
(*quantifiers for occurrences*)
| All_Ind_Occ    of subtrm_occ * subtrm * assrt
| All_Arb_Occ    of subtrm_occ * subtrm * assrt
| All_Rule_Occ   of rule_occ   * rule   * assrt
| Some_Ind_Occ   of subtrm_occ * subtrm * assrt
| Some_Arb_Occ   of subtrm_occ * subtrm * assrt
| Some_Rule_Occ  of rule       * rule   * assrt
(*combinators*)
| And            of assrt * assrt
| Or             of assrt * assrt
| Not            of assrt * assrt
| Imply          of assrt * assrt
(*atomic*)
| Are_Same_Nth   of nth    * nth
| Are_Same_Str   of nth    * nth (*subtrm*)
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
| Is_Nth_Arg_Of  of subtrm_occ * nth * subtrm_occ
(*syntax sugars*)
| Are_Diff_Nth   of nth        * nth (*Not & Are_Same_Nth*)
| Are_Diff_Str   of nth        * nth (*Not & Are_Same_Str*)
| Has_Typ        of subtrm_occ * typ (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Not_Deepest    of subtrm_occ       (*Not & Is_At_Deepest*)

end;