(*  Title:      TBC/Template_Based_Conjecturing.ML
    Author:     Yutaka Nagashima, Zijin Xu, Ningli Wang, and Daniel Goc Sebastian
    Author:     Huawei Technologies Research & Development (UK) Limited.

TEMPLATE_BASED_CONJECTURING: generates candidate conjectures for a constant by
instantiating a fixed library of algebraic/relational property templates
(associativity, commutativity, distributivity, transitivity, and so on).
*)

(*** signature TEMPLATE_BASED_CONJECTURING ***)
signature TEMPLATE_BASED_CONJECTURING =
sig

datatype property =
(* property_for_binary_function *)
  Associativity     (*f (f (x, y), z) = f (x, f (y, z))*)(*f (x, f (y, z)) = f (f (x, y), z)*)
                    (*Prod/11*)(*Prod/12*)
| Identity          (*left identity : f (e, x) = x*) (*right identity: f (x, e) = x for all x*)
                    (*Prod/11*)(*Prod/12*)
| (*TODO*)Invertibility
| Commutativity     (*f (x, y) = f (y, x)*)
| Idempotent_Element(*f (e, e) = e for some e*)
| Idempotency       (*f (x, x) = x *)
| Zero_Element      (*left zero : f (z, x) = z*) (*right zero: f (x, z) = z for all x*)
  (*TODO: Prod/09*) (*https://en.wikipedia.org/wiki/Absorbing_element*)
(* property_for_two_functions *)
| Distributivity      (*f (x, g (y, z)) = g(f (x, y), f (x, z))*)
                      (*f (g (x, y), z) = g (f (x, y), f (x, z))*)
| Ant_Distributivity  (*f (g (x, y)) = g (f (x), f(y))*) (*?*)
| Homomorphism_2      (*f (g (x, y)) = g (f (x), f(y))*)(*Prod/11*)
(* property_for_relations *)(*TODO: filter out functions whose return types are not Bool*)
| Transitivity (*x R y \<Longrightarrow> y R z \<Longrightarrow> x R z*)
| Symmetry     (*x R y \<Longrightarrow> y R x*)
| Connexity    (*x R y \<or> y R x \<or> (x = y)*)
| Reflexivity  (*x R x*)
(* bottom-up conjecturing for unary operators *)
| Involution   (*f (f x) = x for all x *) (*Prod/11*)
|(*TODO*) Square_Root (*f (f x) = x for some x*)
| Idempotence  (*f (f x) = f x for all x *) (*TIP15 sorts*)
(* non-algebraic bottom-up conjecturing *)
|(*TODO*) Swap_Constructor (*Prod/13*)(*Prod/15*)
| Swap_Unary (*f (x, g (y)) = f ( g (x), y )*)
| Composite_Commutativity (* f (g (x, y)) = f (g (y, x)) *)

val property_as_string: property -> string;

val pst_n_property_n_trm_to_pnode: Proof.state -> (property * term) -> TBC_Utils.pnode;

val ctxt_n_typ_to_consts_full:        Proof.context -> typ -> terms;
val ctxt_n_typ_to_nullary_const: Proof.context -> typ -> terms;
val ctxt_n_typ_to_unary_const:   Proof.context -> typ -> terms;
val ctxt_n_typ_to_binary_const:  Proof.context -> typ -> terms;

(*property_for_binary_function*)

val ctxt_n_const_to_associativity:       Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_identity:            Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_invertibility:       Proof.context -> term -> (property * term) list
val ctxt_n_const_to_commutativity:       Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_idempotent_element:  Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_idempotence:         Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_zero_element:        Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_distributivity:     Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_anti_distributivity:Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_homomorphism_2:     Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_involution:         Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_square_root:        Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_idempotence:         Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_swap_constructor:   Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_transitivity:       Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_symmetry:           Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_connexity:          Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_reflexibility:      Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_swap_unary:         Proof.context -> term -> (property * term) list;
val ctxt_n_consts_to_composite_commutativity: Proof.context -> term -> (property * term) list;
val ctxt_n_const_to_all_conjecture_term: Proof.context -> term -> (property * term) list;

end;

(*** structure Template_Based_Conjecturing ***)
structure Template_Based_Conjecturing: TEMPLATE_BASED_CONJECTURING =
struct

val strip_atyp        = Isabelle_Utils.strip_atyp;
val takes_n_arguments = Isabelle_Utils.takes_n_arguments;

datatype direction = Left | Right;

datatype property =
(* property_for_binary_function*)
  Associativity
| Identity
| Invertibility
| Commutativity
| Idempotent_Element
| Idempotency
| Zero_Element
(* property_for_two_functions *)
| Distributivity     (*2,2*)
| Ant_Distributivity (*1,2*)
| Homomorphism_2     (*1,2*)
(* property_for_relations *)
| Transitivity
| Symmetry
| Connexity
| Reflexivity
(* bottom-up conjecturing for unary operators *)
| Involution (*f (f x) = x for all x*) (*Prod/11*)
|(*TODO*) Square_Root (*f (f x) = x for some x*)
| Idempotence  (*f (f x) = f x for all x *) (*TIP15 sorts*)
(* non-algebraic bottom-up conjecturing *)
| Swap_Constructor
| Swap_Unary
| Composite_Commutativity;

fun property_as_string Associativity           = "associativity"
  | property_as_string Identity                = "identity"
  | property_as_string Invertibility           = "invertibility"
  | property_as_string Commutativity           = "commutativity"
  | property_as_string Idempotent_Element      = "idempotent_element"
  | property_as_string Idempotency             = "idempotency"
  | property_as_string Zero_Element            = "zero_element"
  | property_as_string Distributivity          = "distributivity"
  | property_as_string Ant_Distributivity      = "ant_distributivity"
  | property_as_string Homomorphism_2          = "homomorphism_2"
  | property_as_string Transitivity            = "transitivity"
  | property_as_string Symmetry                = "symmetry"
  | property_as_string Connexity               = "connexity"
  | property_as_string Reflexivity             = "reflexivity"
  | property_as_string Involution              = "involution"
  | property_as_string Square_Root             = "square_root"
  | property_as_string Idempotence             = "idempotence"
  | property_as_string Swap_Constructor        = "swap_constructor"
  | property_as_string Swap_Unary              = "swap_unary"
  | property_as_string Composite_Commutativity = "composite_commutativity";

fun pst_n_property_n_trm_to_pnode
      (pst:Proof.state) (property:property, conjecture_trm:term): TBC_Utils.pnode =
    let
      val lemma_name =
        TBC_Utils.mk_lemma_name (Proof.context_of pst) TBC_Utils.Bottom_Up
          (property_as_string property): string;
      val conjecture_as_string =
        Isabelle_Utils.trm_to_string (Proof.context_of pst) conjecture_trm: string;
    in
      {
        is_final_goal = false,
        lemma_name = lemma_name,
        lemma_term = TBC_Utils.as_prop conjecture_trm,
        proof_log = NONE,
        proof = NONE,
        proof_id = NONE,
        refuted = TBC_Utils.pst_n_conjecture_has_counterexample pst conjecture_as_string,
        proved_wo_assmng_cnjctr = false,
        proved_in_nth_round = NONE
      }: TBC_Utils.pnode
    end;


fun get_ancestors_of_main ctxt =
  let
    fun get_Main ctxt = SOME (Theory.check {long = true} ctxt ("Main", Position.none))
                        handle ERROR _ => NONE;
    fun ancestor_list ctxt = Theory.ancestors_of ctxt |> map (Context.theory_name {long=true})
    val maybe_main = get_Main ctxt
    val ancestors_list = case maybe_main of
              NONE   => []
            | SOME _ =>
                ancestor_list
                  (Context.get_theory {long = true} (Proof_Context.theory_of @{context}) "Main")
  in
    ancestors_list
  end

fun filter_out_invalid_names ctxt (const_names :strings) =
    let
      (* Isabelle sometimes creates redundant constants, we remove them by pattern matching
         with name *)
      val invalid_prefix = "partial_term_of_itself_inst"::"typerep_itself_inst"::
                           (get_ancestors_of_main ctxt)
      val invalid_suffix = ["_sumC", "_dom", "set_list"]
      val invalid_other_name = ["size", "term_of", "wit", "equal_"]
      val mild_exceptions = []
      val exceptions = ["HOL.True", "HOL.False", "HOL.conj", "HOL.disj", "HOL.Not"]
      fun notin _ [] = true | notin name (x::xs) = (name<>x) andalso notin name xs

      (* checking for prefix, suffix and other *)
      fun has_invalid_prefix name prefix  = name |> (String.isPrefix prefix)
      fun has_invalid_prefixes name =
        notin name mild_exceptions andalso List.exists (has_invalid_prefix name) invalid_prefix

      fun has_other_invalid_name name other_name =
        name |> Long_Name.base_name |> (String.isPrefix other_name)
      fun has_other_invalid_names name =
        List.exists (has_other_invalid_name name) invalid_other_name

      fun has_invalid_suffix name suffix = name |> (String.isSuffix suffix)
      fun has_invalid_suffixes name = List.exists (has_invalid_suffix name) invalid_suffix

      fun has_invalid_name name =
        has_invalid_prefixes name orelse has_invalid_suffixes name
        orelse has_other_invalid_names name
    in filter_out has_invalid_name const_names
    end;

fun ctxt_n_typ_to_consts_full ctxt typ =
    let
      fun ctxt_n_typ_to_consts_full' (ctxt:Proof.context) (typ:typ) =
        let
          val typ_as_string   = Syntax.string_of_typ ctxt typ
          |> YXML.parse_body
          |> XML.content_of : string;
          val const_typ_pairs =
            Pretty_Consts.pretty_consts ctxt [(true, Find_Consts.Strict typ_as_string)]
            : (string * typ) list;
          val const_names     = map fst const_typ_pairs: strings;
          val filtered_const_names = filter_out_invalid_names ctxt const_names
          val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) filtered_const_names
                       : terms;
        in
          consts_w_dummyT: terms
        end;
    in try (ctxt_n_typ_to_consts_full' ctxt) typ |> Utils.is_some_null end;

fun ctxt_n_typ_to_consts_full_with_arity ctxt arity typ =
    let
      fun ctxt_n_typ_to_consts_full_with_arity' (ctxt:Proof.context) (typ:typ) =
        let
          val typ_as_string   = Syntax.string_of_typ ctxt typ
          |> YXML.parse_body
          |> XML.content_of : string;
          val const_typ_pairs =
            Pretty_Consts.pretty_consts ctxt [(true, Find_Consts.Strict typ_as_string)]
            : (string * typ) list;
          val const_typ_pairs_with_arity =
            filter (fn (_, const_typ) => length (binder_types const_typ) = arity) const_typ_pairs;
          val const_names     = map fst const_typ_pairs_with_arity: strings;
          val filtered_const_names = filter_out_invalid_names ctxt const_names
          val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) filtered_const_names: terms;
        in
          consts_w_dummyT: terms
        end;
    in try (ctxt_n_typ_to_consts_full_with_arity' ctxt) typ |> Utils.is_some_null end;

fun ctxt_n_typ_to_consts_domain ctxt typ =
    let
      (* the 2 auxiliary functions are used to check if the domain type of the term is typ *)
      fun replace_tvars_with_dummyT typ' = map_atyps (K dummyT) typ'
      fun check_domain typ' = fst (dest_Type typ') = "fun" andalso
                              length (binder_types typ') = 1 andalso
                              replace_tvars_with_dummyT (domain_type typ')
                                = replace_tvars_with_dummyT typ
      fun ctxt_n_typ_to_consts_domain' (ctxt:Proof.context) (typ:typ) =
        let
          val typ_as_string   = Syntax.string_of_typ ctxt typ
          |> YXML.parse_body
          |> XML.content_of : string;
          val const_typ_pairs =
            Pretty_Consts.pretty_consts ctxt [(true, Find_Consts.Loose typ_as_string)]
            : (string * typ) list;
          val filtered_const_typ_pairs = filter (fn pair => check_domain (snd pair)) const_typ_pairs
          val const_names     = map fst filtered_const_typ_pairs: strings;
          val filtered_const_names = filter_out_invalid_names ctxt const_names
          val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) filtered_const_names
                       : terms;
        in
          consts_w_dummyT: terms
        end;
    in try (ctxt_n_typ_to_consts_domain' ctxt) typ |> Utils.is_some_null end;

(*to find candidates for the identity element*)
fun ctxt_n_typ_to_nullary_const ctxt typ = ctxt_n_typ_to_consts_full_with_arity ctxt 0 typ;

(*to find candidates for the inverse function*)
fun ctxt_n_typ_to_unary_const ctxt typ = ctxt_n_typ_to_consts_full_with_arity ctxt 1 (typ --> typ);

(* to find unary functions with specified domain *)
fun ctxt_n_domain_typ_to_unary_const ctxt typ = ctxt_n_typ_to_consts_domain ctxt typ;

(*to find candidates for the distributive property*)
fun ctxt_n_typ_to_binary_const ctxt typ =
  ctxt_n_typ_to_consts_full_with_arity ctxt 2 ([typ, typ] ---> typ);

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun mk_free_variable_of_dummyT (i:int) = mk_free_variable_of_typ dummyT i;

(*assume binary*)(*TODO: Do not assume.*)
val list_comb = Term.list_comb;

fun all_args_are_same_typ (funcs:terms) =
    let
      fun get_arg_typs (f:typ)      = snd (strip_type f)::fst (strip_type f)     : typ list;
      val typs                      = map (get_arg_typs o type_of) funcs |> flat : typ list;
      val numb_of_distinct_elements = distinct (op =) typs |> length             : int;
    in
      numb_of_distinct_elements = 1
    end;

fun all_domain_args_are_same_typ funcs =
  let
      fun get_arg_typs (f:typ)      = fst (strip_type f)     : typ list;
      val typs                      = map (get_arg_typs o type_of) funcs |> flat : typ list;
      val numb_of_distinct_elements = distinct (op =) typs |> length             : int;
    in
      numb_of_distinct_elements = 1
    end;



(*property_for_binary_function*)

fun mk_eq (lhs:term, rhs:term) = strip_atyp @{term "HOL.eq"} $ strip_atyp lhs $ strip_atyp rhs;

fun ctxt_n_const_to_associativity (ctxt:Proof.context) (func:term) =
(*f (f (x, y), z) = f (x, f (y, z))*)
(*f (x, f (y, z)) = f (f (x, y), z)*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
     (let
        val func_w_dummyT      = map_types (K dummyT) func                   : term;
        val [var1, var2, var3] = map mk_free_variable_of_dummyT [1,2,3]      : terms;
        val lhs                =
          list_comb (func_w_dummyT, [var1, list_comb (func_w_dummyT, [var2, var3])]) |> strip_atyp;
        val rhs                =
          list_comb (func_w_dummyT, [list_comb (func_w_dummyT, [var1, var2]), var3]) |> strip_atyp;
        val assocs             =
          map mk_eq [(lhs, rhs), (rhs, lhs)]
          |> map (TBC_Utils.type_check ctxt) |> Utils.somes: terms;
        val cnjctrs            = map (fn trm => (Associativity, trm)) assocs
      in
        cnjctrs: (property * term) list
      end)
    else [];

datatype zero_or_identity = Zero_Elem | Identity_Elem;

fun ctxt_n_const_to_zero_or_identity'
      (z_or_i:zero_or_identity) (ctxt:Proof.context) (direct:direction)
  (func as Const (cname, typ):term) =
(*left  identity: f (e, x) = x*)
(*right identity: f (x, e) = x*)
(*left  zero    : f (z, x) = z*)
(*right zero    : f (x, z) = z*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val typ_of_arg     = binder_types typ |> (case direct of
                              Left  =>  List.hd
                            | Right =>
                                (Utils.the'
                                   "ctxt_n_trm_to_identity in Bottom_Up_Conjecturing.ML failed"
                                 o try (fn args => nth args 1)))   : typ;
        val nullary_consts = ctxt_n_typ_to_nullary_const ctxt typ_of_arg: terms;
        val func_w_dummyT  = strip_atyp func                            : term;
        val free_var       = mk_free_variable_of_dummyT     1           : term;
        fun mk_equation (identity_element:term) =
          let
            val lhs = case direct of
                Left  => list_comb (func_w_dummyT, [identity_element, free_var]): term
              | Right => list_comb (func_w_dummyT, [free_var, identity_element]): term;
            val rhs = case z_or_i of
                      Zero_Elem     => identity_element
                    | Identity_Elem => free_var      : term;
            val eq = mk_eq (lhs, rhs)                : term;
          in
            eq: term
          end;
        val cnjctr_trms =
          map mk_equation nullary_consts |> map (TBC_Utils.type_check ctxt) |> Utils.somes: terms;
        val cnjctrs     = map (fn trm => (Identity, trm)) cnjctr_trms: (property * term) list;
      in
        cnjctrs
      end
    else []
  | ctxt_n_const_to_zero_or_identity' _ _ _ _ = [];

fun ctxt_n_const_to_identity ctxt trm: (property * term) list =
    ctxt_n_const_to_zero_or_identity' Identity_Elem ctxt Left trm
  @ ctxt_n_const_to_zero_or_identity' Identity_Elem ctxt Right trm;

val ctxt_n_const_to_invertibility = undefined; (*TODO*)

fun ctxt_n_const_to_commutativity (ctxt:Proof.context) (func:term) =
  (*f (x, y) = f (y, x)*)
    if takes_n_arguments func 2 andalso all_domain_args_are_same_typ [func]
    then
      let
        val func_w_dummyT = strip_atyp func                                : term;
        val (var1,var2)   = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val lhs           = list_comb (func_w_dummyT, [var1,var2])         : term;
        val rhs           = list_comb (func_w_dummyT, [var2,var1])         : term;
        val eq            = mk_eq (lhs, rhs)                               : term;
        val commutativity = TBC_Utils.type_check ctxt eq                      : term option;
      in
        case commutativity of SOME x => [(Commutativity, x)] | _ => []

      end
    else [];

fun ctxt_n_const_to_idempotent_element (ctxt:Proof.context) (func as Const (_, typ): term) =
  (*f (e, e) = e for some e*)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val typ_of_arg     = binder_types typ |> List.hd                : typ;
        val nullary_consts = ctxt_n_typ_to_nullary_const ctxt typ_of_arg: terms;
        val func_w_dummyT  = strip_atyp func                            : term;
        fun mk_equation (identity_element:term) =
          let
            val lhs = list_comb (func_w_dummyT, [identity_element, identity_element]): term;
            val eq  = mk_eq (lhs, identity_element)                                  : term;
          in
            TBC_Utils.type_check ctxt eq
          end;
        val idempotents = map mk_equation nullary_consts |> Utils.somes
      in
        map (fn trm => (Idempotent_Element, trm)) idempotents
      end
    else []
  | ctxt_n_const_to_idempotent_element _ _ = [];

fun ctxt_n_const_to_idempotence (ctxt:Proof.context) (func as Const(_, _)) =
    (* f (x, x) = x *)
    if takes_n_arguments func 2 andalso all_args_are_same_typ [func]
    then
      let
        val func_wo_typ = strip_atyp func                 : term;
        val var         = mk_free_variable_of_dummyT 1    : term;
        val idempotence =
          mk_eq (list_comb (func_wo_typ, [var, var]), var) |> TBC_Utils.type_check ctxt;
      in
        case idempotence of SOME x => [(Idempotency, x)] | _ => []

      end
    else []
 | ctxt_n_const_to_idempotence _ _ = [];

fun ctxt_n_const_to_zero_element ctxt trm: (property * term) list =
    ctxt_n_const_to_zero_or_identity' Zero_Elem ctxt Left trm
  @ ctxt_n_const_to_zero_or_identity' Zero_Elem ctxt Right trm;

(*property_for_two_functions*)
fun ctxt_n_consts_to_distributivity' (ctxt:Proof.context) (func1:term) (func2:term) =
    let
      val (func1_wo_typ, func2_wo_typ) = Utils.map_pair strip_atyp (func1, func2): (term * term);
      val [var1, var2, var3]           = map mk_free_variable_of_dummyT [1,2,3]  : terms;
      val (left_lhs, right_lhs)        =
        (list_comb (func1_wo_typ, [var1, list_comb (func2_wo_typ, [var2, var3])]),
         list_comb (func1_wo_typ, [list_comb (func2_wo_typ, [var1, var2]), var3])
        );
      val (left_rhs, right_rhs)        =  (list_comb
                                            (func2_wo_typ,
                                             [list_comb (func1_wo_typ, [var1, var2]),
                                              list_comb (func1_wo_typ, [var1, var3])
                                              ]
                                             ),
                                           list_comb
                                            (func2_wo_typ,
                                             [list_comb (func1_wo_typ, [var1, var3]),
                                              list_comb (func1_wo_typ, [var2, var3])
                                              ]
                                             )
                                           );
      val cnjctrs               = [mk_eq (left_lhs, left_rhs), mk_eq (right_lhs, right_rhs)]
                               |> map (TBC_Utils.type_check ctxt) |> Utils.somes;
    in
      cnjctrs
    end;

fun ctxt_n_consts_to_distributivity (ctxt:Proof.context) (func1 as Const (_, typ)) =
(* left-distributive:  f (x, g (y, z)) = g (f (x, y), f (x, z))
 * right-distributive: f (g (x, y), z) = g (f (x, y), f (x, z))
 *)
    if takes_n_arguments func1 2 andalso all_args_are_same_typ [func1]
    then
      let
        val return_typ = strip_type typ |> snd                  : typ;
        val b_funcs = ctxt_n_typ_to_binary_const ctxt return_typ: terms;
        val cnjctr_trms = map (ctxt_n_consts_to_distributivity' ctxt func1) b_funcs |> flat;
      in
        map (fn trm => (Distributivity, trm)) cnjctr_trms
      end
    else []
  | ctxt_n_consts_to_distributivity _ _ = [];

fun ctxt_n_consts_to_anti_distributivity' (ctxt:Proof.context) binary_func unary_func =
(*f (g (x, y)) = g (f (y), f (x))*)
    let

      val (unary_wo_typ, binary_wo_typ) =
        Utils.map_pair strip_atyp (unary_func, binary_func): (term * term);
      val (var1, var2)                  =
        Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
      val lhs                           =
        list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var1, var2])]): term;
      val rhs                           = list_comb
                                          (binary_wo_typ,
                                           [list_comb (unary_wo_typ, [var2]),
                                            list_comb (unary_wo_typ, [var1])
                                            ]
                                           )
                                          ;
      val anti_distributivity           = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt
    in
      case anti_distributivity of SOME x => [(Ant_Distributivity, x)] | _ => []
    end;

fun ctxt_n_consts_to_anti_distributivity (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_args_are_same_typ [binary_func]
    then
      let
        val return_typ = strip_type typ |> snd                 : typ;
        val u_funcs = ctxt_n_typ_to_unary_const ctxt return_typ: terms;
      in
        map (ctxt_n_consts_to_anti_distributivity' ctxt binary_func) u_funcs |> flat
      end
    else []
  | ctxt_n_consts_to_anti_distributivity _ _ = [];


fun ctxt_n_consts_to_composite_commutativity' (ctxt:Proof.context) binary_func unary_func =
(*f (g (x, y)) = f (g (y, x))*)
    let
      val (unary_wo_typ, binary_wo_typ) =
        Utils.map_pair strip_atyp (unary_func, binary_func): (term * term);
      val (var1, var2)                  =
        Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
      val lhs                           =
        list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var1, var2])]): term;
      val rhs                           =
        list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var2, var1])]): term;
      val composite_commutativity       = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt
    in
      case composite_commutativity of SOME x => [(Composite_Commutativity, x)] | _ => []
    end;

fun ctxt_n_consts_to_composite_commutativity
      (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_domain_args_are_same_typ [binary_func]
    then
      let
        val return_typ = strip_type typ |> snd                 : typ;
        val u_funcs = ctxt_n_domain_typ_to_unary_const ctxt return_typ: terms;
      in
        map (ctxt_n_consts_to_composite_commutativity' ctxt binary_func) u_funcs |> flat
      end
    else []
  | ctxt_n_consts_to_composite_commutativity _ _ = [];


fun ctxt_n_consts_to_swap_unary' (ctxt:Proof.context) (binary_func:term) (unary_func:term) =
    (* f (x, g (y)) = f (g (x), y)*)
     if all_args_are_same_typ [unary_func]
     then
       let
         fun build_eq _ =
           let
             val (var1, var2) = Utils.map_pair mk_free_variable_of_dummyT (1,2): term * term;
             val lhs = binary_func $ var1 $ (unary_func $ var2): term;
             val rhs = binary_func $ (unary_func $ var1) $ var2: term;
           in
             mk_eq (lhs, rhs): term
           end;
       in
         try build_eq ()
         >>= try (Syntax.check_term ctxt)
         <$> (fn trm => (Swap_Unary, trm))
         |> the_list
       end
     else [];

fun ctxt_n_consts_to_swap_unary (ctxt:Proof.context) (binary_func as (Const (_, typ))) =
    if takes_n_arguments binary_func 2 andalso
       all_domain_args_are_same_typ [binary_func]
    then
      let
        val domain_typ = domain_type typ                       : typ;
        val u_funcs = ctxt_n_typ_to_unary_const ctxt domain_typ: terms;
      in
        map (ctxt_n_consts_to_swap_unary' ctxt (strip_atyp binary_func)) (map strip_atyp u_funcs)
        |> flat
      end
    else []
  | ctxt_n_consts_to_swap_unary _ _ = [];

fun ctxt_n_consts_to_homomorphism_2
      (ctxt:Proof.context) (preserved_binary as (Const (_, typ)):term) =
(*f is homomorphism.*)
(*f (g (x, y)) = g (f (x), f (y))*)
    if takes_n_arguments preserved_binary 2 andalso
       all_args_are_same_typ [preserved_binary]
    then
      let
        val unaries                 = ctxt_n_typ_to_unary_const ctxt (strip_type typ |> snd): terms;
        val unaries_wo_typ          = map strip_atyp unaries                                : terms;
        val (var1, var2)            =
          Utils.map_pair mk_free_variable_of_dummyT (1,2): term * term;
        val preserved_binary_wo_typ = strip_atyp preserved_binary                           : term;
        fun get_cnjctr (homomorphism_wo_typ:term): (term option) =
          let
            val lhs       =
              homomorphism_wo_typ $ list_comb (strip_atyp preserved_binary, [var1, var2]): term;
            val rhs       =
              list_comb (preserved_binary_wo_typ,
                         [homomorphism_wo_typ $ var1, homomorphism_wo_typ $ var2])
              : term;
            val property = mk_eq (lhs, rhs) |> TBC_Utils.type_check ctxt: term option;
          in
            property
          end;
        val homos = map get_cnjctr unaries_wo_typ |> Utils.somes
      in
        map (fn trm => (Homomorphism_2, trm)) homos
      end
    else []
  | ctxt_n_consts_to_homomorphism_2 _ _ = [];

fun ctxt_n_consts_to_involution (ctxt:Proof.context) (func:term) =
(* f (f x) = x *)
    if takes_n_arguments func 1 andalso all_args_are_same_typ [func]
    then
      let
          val tracing' = if false then tracing else K ();
          val _ = tracing' "===  takes_n_arguments func 1 returned true."
          val var1 = mk_free_variable_of_dummyT 1;
          val _ = tracing' "===  before calling involution."
          val func_wo_typ = strip_atyp func;
          val involution =
                Const ("HOL.eq", dummyT )
                  $ (func_wo_typ $ (func_wo_typ $ var1))
                  $ var1
                |> (fn xyz => (tracing' "===  before calling Syntax.check_term"; xyz))
                |> (fn xyz => (tracing' "===  we pass this term sto Syntax.check_term:"; xyz))
                |> (fn xyz => (tracing' ("===  " ^ Isabelle_Utils.trm_to_string ctxt xyz); xyz))
                |> TBC_Utils.type_check ctxt:term option;
          val _ = tracing' " :) ctxt_n_consts_to_involution almost finished successfully."
      in if is_some involution then [(Involution, the involution)] else []
      end
    else []

val ctxt_n_consts_to_square_root = undefined; (*TODO*)

fun ctxt_n_consts_to_idempotence (ctxt:Proof.context) (func:term) =
(* f (f x) = f x *)
    if takes_n_arguments func 1 andalso all_args_are_same_typ [func]
    then
      let
          val var1 = mk_free_variable_of_dummyT 1;
          val func_wo_typ = strip_atyp func;
          val idempotence =
                Const ("HOL.eq", dummyT )
                  $ (func_wo_typ $ (func_wo_typ $ var1))
                  $ (func_wo_typ $ var1)
                |> TBC_Utils.type_check ctxt:term option;
      in if is_some idempotence then [(Idempotence, the idempotence)] else []
      end
    else []


val ctxt_n_consts_to_swap_constructor = undefined;(*TODO*)

(*property_for_relations*)
fun term_is_relation (Const (_, typ)) = body_type typ = @{typ "HOL.bool"}
  | term_is_relation  _               = false;


fun condition_for_relation (func:term) =
    term_is_relation func andalso
    takes_n_arguments func 2 andalso
    all_domain_args_are_same_typ [func]

fun list_implies (ctxt:Proof.context) (prems: terms, cncl) =
    Logic.list_implies (prems, cncl)
 |> TBC_Utils.type_check ctxt: term option;

fun ctxt_n_consts_to_transitivity
      (ctxt:Proof.context) (func as (Const _):term): (property * term) list =
(*x R y \<Longrightarrow> y R z \<Longrightarrow> x R z*)
    if condition_for_relation func
    then
      let
        val func_wo_typ        = strip_atyp func                         : term;
        val [var1, var2, var3] = map mk_free_variable_of_dummyT [1, 2, 3]: terms;
        val prem1              = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var2])): term;
        val prem2              = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var2, var3])): term;
        val cncl               = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var3])): term;
        val imply              = list_implies ctxt ([prem1, prem2], cncl): term option;
      in if is_some imply then [(Transitivity, the imply)] else [] end
    else []
  | ctxt_n_consts_to_transitivity _ _ = [];

fun mk_implies (ctxt:Proof.context) (prem, cncl) =
   Logic.mk_implies (prem, cncl)
|> TBC_Utils.type_check ctxt: term option;

fun ctxt_n_consts_to_symmetry
      (ctxt:Proof.context) (func as (Const _):term): (property * term) list =
(*x R y \<Longrightarrow> y R x*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                                : term;
        val (var1, var2) = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val premise      = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var1, var2])): term;
        val conclusion   = HOLogic.mk_Trueprop (list_comb (func_wo_typ, [var2, var1])): term;
        val imply        = mk_implies ctxt (premise, conclusion)          : term option;
      in if is_some imply then [(Symmetry, the imply)] else []  end
    else []
  | ctxt_n_consts_to_symmetry _ _ = [];

fun ctxt_n_consts_to_connexity (ctxt:Proof.context) (func as (Const _)): (property * term) list =
(*x R y \<or> y R x \<or> (x = y)*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                                : term;
        val (var1, var2) = Utils.map_pair mk_free_variable_of_dummyT (1,2): (term * term);
        val x_R_y        = list_comb (func_wo_typ, [var1, var2])          : term;
        val y_R_x        = list_comb (func_wo_typ, [var2, var1])          : term;
        val x_is_y       = HOLogic.mk_eq (var1, var2)                     : term;
        val disjuncts    = HOLogic.mk_disj (HOLogic.mk_disj (x_R_y, y_R_x), x_is_y)
                        |> TBC_Utils.type_check ctxt                         : term option;
      in if is_some disjuncts then [(Connexity, the disjuncts)] else [] end
    else []
  | ctxt_n_consts_to_connexity _ _ = [];

fun ctxt_n_consts_to_reflexibility (_:Proof.context) (func as (Const _):term) =
(*x R x*)
    if condition_for_relation func
    then
      let
        val func_wo_typ  = strip_atyp func                      : term;
        val fvar         = mk_free_variable_of_dummyT 1         : term;
        val reflex       = list_comb (func_wo_typ, [fvar, fvar]): term;
      in [(Reflexivity, reflex)] end
    else []
  | ctxt_n_consts_to_reflexibility _ _ = [];



(*TODO: name:
  FIXME: We only start with the binary function. This is strange.*)
fun ctxt_n_const_to_all_conjecture_term
      (ctxt:Proof.context) (func as (Const _)): (property * term) list =
  let
    fun safely_make_conjectures maker =
      try (maker ctxt) func |> Utils.is_some_null;
  in
    safely_make_conjectures ctxt_n_const_to_associativity
  @ safely_make_conjectures ctxt_n_const_to_identity
  @ safely_make_conjectures ctxt_n_const_to_commutativity
  @ safely_make_conjectures ctxt_n_const_to_idempotent_element
  @ safely_make_conjectures ctxt_n_const_to_idempotence
  @ safely_make_conjectures ctxt_n_const_to_zero_element
  @ safely_make_conjectures ctxt_n_consts_to_distributivity
  @ safely_make_conjectures ctxt_n_consts_to_anti_distributivity
  @ safely_make_conjectures ctxt_n_consts_to_homomorphism_2
  @ safely_make_conjectures ctxt_n_consts_to_idempotence
  @ safely_make_conjectures ctxt_n_consts_to_involution
  @ safely_make_conjectures ctxt_n_consts_to_symmetry
  @ safely_make_conjectures ctxt_n_consts_to_reflexibility
  @ safely_make_conjectures ctxt_n_consts_to_transitivity
  @ safely_make_conjectures ctxt_n_consts_to_connexity
  @ safely_make_conjectures ctxt_n_consts_to_swap_unary
  @ safely_make_conjectures ctxt_n_consts_to_composite_commutativity
  end

| ctxt_n_const_to_all_conjecture_term _ _ =
    error "ctxt_n_const_to_all_conjecture_term func. This term is not a constant.";

end;
