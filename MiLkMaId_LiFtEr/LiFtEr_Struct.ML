(*  Title:      PSL/MiLkMaId_LiFtEr/LiFtEr_Struct.ML
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

The syntax and interpreter of LiFtEr, Logical Feature Extractor for MiLkMaId.
*)
structure LiFtEr: LIFTER =
struct

type abs_pstate_w_aux = Term_Table.abs_pstate_w_aux;

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
(*atomic*)
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
| Is_Nth_Arg_Of  of subtrm_occ * numb * subtrm_occ
| Less           of numb       * numb (* nth_1 < nth_2 *)
(* TODO: pattern *)
| Pattern        of numb * subtrm * pattern (*In the definition of subtrm, the nth argument has this pattern.*)
(*syntax sugars*)
| Are_Diff_Nth   of numb       * numb (*Not & Are_Same_Nth*)
| Are_Diff_Str   of numb       * numb (*Not & Are_Same_Str*)
| Has_Typ        of subtrm_occ * typ (*Some_Sub_Trm, Is_In, & Is_Typ*)
| Not_Deepest    of subtrm_occ       (*Not & Is_At_Deepest*)

datatype rule_name       = Rule_Name of string;

(*TIP: use functions from AList, such as AList.update, for name_space.*)
datatype name_space = Name_Space of
 {subtrm:     (int * Unique_Node.paths) list,
  subtrm_occ: (int * Unique_Node.path)  list,
  rule:       (int * rule_name       )  list,
  numb:       (int * numb            )  list};

datatype name =
  Name_Nth        of numb
| Name_Subtrm     of subtrm
| Name_Rule       of rule
| Name_Subtrm_Occ of subtrm_occ;

datatype name_domain = Name_Domain of
  {subtrm_domain    : Unique_Node.paths list,
   subtrm_occ_domain: Unique_Node.paths,
   rule_domain      : strings};

fun no_name_collision (Name_Space name_space: name_space) (name: name) =
  let
    fun fsts (xs:('a * 'b) list) = map fst xs: 'a list;
    fun is_in_fsts (x:int) (xs:(int * 'b) list) = xs |> fsts |> (fn ints => member (op =) ints x): bool ;
    fun is_in_numbs       (x:int) = #numb       name_space |> is_in_fsts x: bool;
    fun is_in_subtrms     (x:int) = #subtrm     name_space |> is_in_fsts x: bool;
    fun is_in_rules       (x:int) = #rule       name_space |> is_in_fsts x: bool;
    fun is_in_subtrm_occs (x:int) = #subtrm_occ name_space |> is_in_fsts x: bool;
    fun no_name_collision' (Name_Nth          (Nth         i):name) = is_in_numbs       i
     |  no_name_collision' (Name_Subtrm       (Sub_Trm     i):name) = is_in_subtrms     i
     |  no_name_collision' (Name_Rule         (Rule        i):name) = is_in_rules       i
     |  no_name_collision' (Name_Subtrm_Occ   (Sub_Trm_Occ i):name) = is_in_subtrm_occs i;
  in
    no_name_collision' name
  end;

(*TODO: check name collisions before evaluation.*)
val no_overlad = undefined: assrt -> bool;

fun eval (Name_Domain name_domain: name_domain, abs_pst_w_aux, assert) = (*TODO*)
  let
    fun alist_add (alist: (int * 'a) list) (key:int, value:'a) = AList.update (op =) (key, value) alist: (int * 'a) list;
    val subtrm_name_domain = #subtrm_domain name_domain: Unique_Node.paths list;
    val empty_name_space = Name_Space
       {subtrm     = [],
        subtrm_occ = [],
        rule       = [],
        numb       = []};
    (*Note that we never modify abs_pst_w_aux.*)
    fun eval' (All_Ind ((Sub_Trm i), assrt), Name_Space name_space: name_space) =
          let
            val {subtrm, subtrm_occ, rule, numb}   = name_space;
            val new_elements_for_subtrm_name_space = map (fn paths => (i, paths)) subtrm_name_domain          : (int * Unique_Node.paths) list;
            val new_subtrm_entries_in_name_space   = map (alist_add subtrm) new_elements_for_subtrm_name_space: (int * Unique_Node.paths) list list;
            fun get_new_name_space new_subtrm      = Name_Space {subtrm = new_subtrm, subtrm_occ = subtrm_occ, rule = rule, numb = numb}: name_space;
            val new_name_spaces                    = map get_new_name_space new_subtrm_entries_in_name_space  : name_space list;
            fun eval_for_one_name_space (ns:name_space) = eval' (assrt, ns);
            fun eval_for_name_spaces (nss:name_space list) = forall eval_for_one_name_space nss: bool;
          in
            eval_for_name_spaces new_name_spaces
          end
      | eval' (And (assrt1, assrt2), name_space) =
          eval' (assrt1, name_space) andalso eval' (assrt2, name_space)
      | eval' (Or (assrt1, assrt2), name_space) =
          eval' (assrt1, name_space) orelse eval' (assrt2, name_space)
      | eval' (Not assrt, name_space) = not (eval' (assrt, name_space))
      | eval' (Imply (assrt1, assrt2), name_space) =
          if   eval' (assrt1, name_space)
          then eval' (assrt2, name_space)
          else true
      | eval' _ = true (*TODO*)
  in
    eval' (assert, empty_name_space)
  end;

end;