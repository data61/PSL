(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Sig.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
signature LIFTER =
sig

include  PATTERN TEST_LIFTER;

type lifter_pst;

datatype numb       = Nth         of int;
datatype subtrm     = Sub_Trm     of int;
datatype rule       = Rule        of int;
datatype subtrm_occ = Sub_Trm_Occ of int;
datatype pattern    = All_Only_Var | All_Const | Mixed;(*TODO: This is not final.*)
datatype assrt      =
(*quantifiers*)
  All_Ind                 of subtrm * assrt
| All_Arb                 of subtrm * assrt
| All_Sub_Trm             of subtrm * assrt
| All_Rule                of rule   * assrt
| All_Numb                of numb   * assrt
| Some_Ind                of subtrm * assrt
| Some_Arb                of subtrm * assrt
| Some_Sub_Trm            of subtrm * assrt
| Some_Rule               of rule   * assrt
| Some_Numb               of numb   * assrt (*n must be smaller than or equal to the argument number of the variable/constant that has the maximum argument number.*)
(*quantifiers for occurrences*)
| All_Sub_Trm_Occ         of subtrm_occ * assrt
| Some_Sub_Trm_Occ        of subtrm_occ * assrt
(*combinators*)
| And                     of assrt * assrt
| Or                      of assrt * assrt
| Not                     of assrt
| Imply                   of assrt * assrt
(*atomic about proof goal*)
| Is_Rule_Of              of rule       * subtrm_occ
| Trm_Occ_Is_Of_Trm       of subtrm_occ * subtrm
| Are_Same_Numb           of numb       * numb
| Are_Same_Str            of subtrm_occ * subtrm_occ (*subtrm*)
| Is_In_Trm_Loc           of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 location-wise*)
| Is_In_Trm_Str           of subtrm_occ * subtrm_occ (*sub-tree-1 is within sub-tree-2 string-wise*)
| Is_Typ                  of subtrm_occ * hol_typ
| Is_In_Chained           of subtrm_occ
| Is_In_Fst_Subg          of subtrm_occ
| Is_In_Prems             of subtrm_occ
| Is_In_Cnclsn            of subtrm_occ
| Is_Atom                 of subtrm_occ
| Is_Cnst                 of subtrm_occ
| Is_Const_Of_Name        of subtrm_occ * string
| Is_Var                  of subtrm_occ
| Is_Free                 of subtrm_occ
| Is_Bound                of subtrm_occ (*corresponds to Bound in term*)
| Is_Lambda               of subtrm_occ (*lambda abstraction corresponding to Abs in Term*)
| Is_App                  of subtrm_occ (*function application corresponding to $ in Term*)
| Not_Fully_App           of subtrm_occ (*If subtrm is function application that is not fully applied returns true, otherwise returns false.*)
| Is_Less_Than            of numb       * numb (* nth_1 < nth_2 *)
| Is_Nth_Arg_Of           of subtrm_occ * numb * subtrm_occ
| Is_Nth_Ind              of subtrm     * numb
| Is_Nth_Arb              of subtrm     * numb
| Numb_Is                 of numb       * int
| Depth_Of_Sub_Trm_Occ_Is of subtrm_occ * numb
| Print_Is                of subtrm     * string
(* TODO: pattern *)
| Pattern                 of numb* subtrm_occ * pattern (*In the definition of subtrm, the numb-th argument has this pattern.*)
(*syntax sugars*)
| Are_Diff_Numb           of numb       * numb           (*Not & Are_Same_Numb*)
| Are_Diff_Str            of subtrm_occ * subtrm_occ     (*Not & Are_Same_Str*)
| Has_Typ                 of subtrm_occ * hol_typ        (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Is_At_Deepest           of subtrm_occ
| Is_More_Than            of numb       * numb           (*Not, Is_Less_Than, And, Are_Same_Numb*)
| For_Numb_N              of numb       * int * assrt    (*Some_Numb $ Numb_Is*)
| All_Sub_Trm_Occ_Of      of subtrm_occ * subtrm * assrt
| Some_Sub_Trm_Occ_Of     of subtrm_occ * subtrm * assrt

datatype rule_name = Rule_Name of string;
type rule_names    = rule_name list;
type paths;
type pathss;
type location;
type path_n_loc;
type path_n_locs;

datatype id =(*TODO: better name? FIXME: this is actually value type.*)
  ID_Subtrm     of print
| ID_Subtrm_Occ of path_n_loc
| ID_Rule       of rule_name
| ID_Numb       of int;

type ids = id list;(*TODO: better name?*)

type name_subspace = (int * id) list;

type name_subspaces = name_subspace list;

(*Note that the name_space specified here is the name_space within each assertion:
 *Different assertions have different name_spaces.*)
datatype name_space = Name_Space of
 {subtrm    : name_subspace,
  subtrm_occ: name_subspace,
  rule      : name_subspace,
  numb      : name_subspace};

type name_spaces = name_space list;

datatype domain = Dom_Subt_Occ of path_n_locs | Dom_Subt of prints | Dom_Rule of rule_names | Dom_Numb of ints;

datatype name_domains = Name_Domains of
  {subtrm_domain : domain,
   rule_domain   : domain,
   numb_domain   : domain};

val pst_to_name_domains       : Proof.state -> name_domains;
val pstate_to_abs_pstate_w_aux: Proof.state -> lifter_pst;

val no_overlad: assrt -> bool;
(*TODO: Double-check. It is possible to remove Proof.context from the signature of eval
 *      if we handle patterns before calling eval.
 *      But in that case, we have to pass the result of handling patterns to eval.
 *      So, it is easier to simply pass Proof.context.*)
val eval      : Proof.state * assrt * ind_mods -> bool;

end;