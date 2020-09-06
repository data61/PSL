(*  Title:      PSL/UR/Bottom_Up_Conjecturing.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck

A part of this file is copied from Pure/Tools/find_consts.ML.
The authors of that part are Timothy Bourke and Gerwin Klein, NICTA.
*)

theory Bottom_Up_Conjecturing
  imports "../PSL/PSL"
begin

ML\<open>(* Utility functions. Copy and paste from  Pure/Tools/find_consts.ML
Author: Timothy Bourke and Gerwin Klein, NICTA

ISABELLE COPYRIGHT NOTICE, LICENCE AND DISCLAIMER.

Copyright (c) 1986-2020,
  University of Cambridge,
  Technische Universitaet Muenchen,
  and contributors.

  All rights reserved.

Redistribution and use in source and binary forms, with or without 
modification, are permitted provided that the following conditions are 
met:

* Redistributions of source code must retain the above copyright 
notice, this list of conditions and the following disclaimer.

* Redistributions in binary form must reproduce the above copyright 
notice, this list of conditions and the following disclaimer in the 
documentation and/or other materials provided with the distribution.

* Neither the name of the University of Cambridge or the Technische
Universitaet Muenchen nor the names of their contributors may be used
to endorse or promote products derived from this software without
specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS 
IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED 
TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A 
PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT 
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, 
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT 
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, 
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY 
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT 
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE 
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*)

local

fun check_const pred (c, (ty, _)) = 
  if pred (c, ty) then SOME (Term.size_of_typ ty) else NONE;

fun matches_subtype thy typat =
  Term.exists_subtype (fn ty => Sign.typ_instance thy (ty, typat));

fun opt_not f (c as (_, (ty, _))) =
  if is_some (f c) then NONE else SOME (Term.size_of_typ ty);

fun filter_const _ _ NONE = NONE
  | filter_const c f (SOME rank) =
      (case f c of
        NONE => NONE
      | SOME i => SOME (Int.min (rank, i)));

in

fun pretty_consts ctxt raw_criteria =
  let
    val thy = Proof_Context.theory_of ctxt;
    val low_ranking = 10000;

    fun make_pattern crit =
      let
        val raw_T = Syntax.parse_typ ctxt crit;
        val t =
          Syntax.check_term
            (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)
            (Term.dummy_pattern raw_T);
      in Term.type_of t end;

    fun make_match (Find_Consts.Strict arg) =
          let val qty = make_pattern arg; in
            fn (_, (ty, _)) =>
              let
                val tye = Sign.typ_match thy (qty, ty) Vartab.empty;
                val sub_size =
                  Vartab.fold (fn (_, (_, t)) => fn n => Term.size_of_typ t + n) tye 0;
              in SOME sub_size end handle Type.TYPE_MATCH => NONE
          end
      | make_match (Find_Consts.Loose arg) =
          check_const (matches_subtype thy (make_pattern arg) o snd)
      | make_match (Find_Consts.Name arg) = check_const (match_string arg o fst);

    fun make_criterion (b, crit) = (if b then I else opt_not) (make_match crit);
    val criteria = map make_criterion raw_criteria;

    fun user_visible (c, _) =
      if Consts.is_concealed (Proof_Context.consts_of ctxt) c
      then NONE else SOME low_ranking;

    fun eval_entry c =
      fold (filter_const c) (user_visible :: criteria) (SOME low_ranking);

    val {constants, ...} = Consts.dest (Sign.consts_of thy);
    val matches =
      fold (fn c => (case eval_entry c of NONE => I | SOME rank => cons (rank, c))) constants []
      |> sort (prod_ord (rev_order o int_ord) (string_ord o apply2 fst))
      |> map (apsnd fst o snd);
in
  matches
end;

end;
\<close>

ML\<open> signature BOTTOM_UP_CONJECTURING =
sig

datatype direction = Left | Right;

datatype bottom_up_for_binary_function =
  Associativity
| Identity       of direction
| Invertibility  of direction
| Commutativity
| Idempotent_Element of direction
| Idempotency        of direction;

datatype bottom_up_for_two_functions =
  Distributivity     (*2,2*)
| Ant_Distributivity (*1,2*)
| Homomorphism_2;    (*1,2*)

datatype bottom_up_for_relations =
  Transitivity
| Symmetry
| Connexity
| Reflexivity;

val ctxt_n_typ_to_typs: Proof.context -> typ -> typ list;

val ctxt_n_typ_to_consts: Proof.context -> typ -> terms;

(*bottom_up_for_binary_function*)
val ctxt_n_const_to_associativity:       Proof.context -> term -> term;
val ctxt_n_const_to_left_identity:       Proof.context -> term -> term;
val ctxt_n_const_to_right_identity:      Proof.context -> term -> term;
val ctxt_n_const_to_left_invertibility:  Proof.context -> term -> term;
val ctxt_n_const_to_right_invertibility: Proof.context -> term -> term;
val ctxt_n_const_to_commutativity:       Proof.context -> term -> term;
val ctxt_n_const_to_idempotent_element:  Proof.context -> term -> term;
val ctxt_n_const_to_idempotency:         Proof.context -> term -> term;

(*bottom_up_for_two_functions*)
val ctxt_n_consts_to_distributivity:     Proof.context -> (term * term) -> (term * term);
val ctxt_n_consts_to_anti_distributivity:Proof.context -> (term * term) -> (term * term);
val ctxt_n_trms_to_homomorphism_2:      Proof.context -> (term * term) -> (term * term);

(*bottom_up_for_relations*)
val ctxt_n_consts_to_symmetry:           Proof.context -> term -> term;
val ctxt_n_consts_to_reflexibility:      Proof.context -> term -> term;
val ctxt_n_consts_to_transitivity:       Proof.context -> term -> term;
val ctxt_n_consts_to_connexity:          Proof.context -> term -> term;

end;
\<close>

datatype 'a list = nil2 | cons2 "'a" "'a list"

print_theorems

datatype Nat = Z | S "Nat"

fun qrev :: "'a list => 'a list => 'a list" where
  "qrev (nil2) y = y"
| "qrev (cons2 z xs) y = qrev xs (cons2 z y)"

fun x :: "'a list => 'a list => 'a list" where
  "x (nil2) z = z"
| "x (cons2 z2 xs) z = cons2 z2 (x xs z)"

fun rev :: "'a list => 'a list" where
  "rev (nil2) = nil2"
| "rev (cons2 z xs) = x (rev xs) (cons2 z (nil2))"

ML\<open> structure Bottom_Up_Conjecturing =
struct

end;

fun term_is_relation (Const (_, typ)) = body_type typ = @{typ "HOL.bool"}
  | term_is_relation _ = false;

fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun remove_typ_in_const (Const (cname, typ)) = Const (cname, map_atyps (K dummyT) typ)
  | remove_typ_in_const _ = error "remove_typ_in_const in Bottom_Up_Conjecturing failed.";

val strip_atype = Term.map_types (map_atyps (K dummyT)): term -> term
\<close>

ML\<open>
(*assume binary*)
val list_comb = Term.list_comb;
fun takes_n_arguments (n:int) (f:term) = length (fst (strip_type (type_of f))) = n;
fun all_args_are_same_typ (funcs:terms) =(*TODO: rename?*)
  let
    fun get_arg_typs (f:typ)      = (snd (strip_type f)::fst (strip_type f))   : typ list;
    val typs                      = map (get_arg_typs o type_of) funcs |> flat : typ list;
    val numb_of_distinct_elements = distinct (op =) typs |> length             : int;
  in
    numb_of_distinct_elements = 1
  end;
\<close>

ML\<open> fun ctxt_consts_string_trm_to_conjecture (ctxt:Proof.context) (consts:terms) (conj_typ:string) (conjecture_trm:term) =
let
  val consts_str = map (Long_Name.base_name o fst o dest_Const) consts |> String.concatWith "_": string;
  val lemma_name = conj_typ ^ "_" ^ consts_str: string;
  val conjecture_as_string = Isabelle_Utils.trm_to_string ctxt conjecture_trm: string;
in
   {lemma_name = lemma_name,  lemma_stmt = conjecture_as_string}
end;
\<close>

ML\<open> fun mk_eq (lhs:term, rhs:term) =
strip_atype @{term "HOL.eq"} $ strip_atype lhs $ strip_atype rhs;
\<close>

ML\<open> fun ctxt_n_trm_to_associativity (ctxt:Proof.context) (func:term) =
(*f (f (x, y), z) = f (x, f (y, z))*)
if takes_n_arguments 2 func andalso all_args_are_same_typ [func]
then
 (let
    val func_w_dummyT      = map_types (K dummyT) func                   : term;
    val [var1, var2, var3] = map (mk_free_variable_of_typ dummyT) [1,2,3]: terms;
    val lhs                = list_comb (func_w_dummyT, [var1, list_comb (func_w_dummyT, [var2, var3])]) |> strip_atype;
    val rhs                = list_comb (func_w_dummyT, [list_comb (func_w_dummyT, [var1, var2]), var3]) |> strip_atype;
    val assoc              = mk_eq (lhs, rhs): term;
  in
    [Syntax.check_term ctxt assoc |> ctxt_consts_string_trm_to_conjecture ctxt [func] "associativity"]
  end)
else []: {lemma_name: string, lemma_stmt: string} list
;
\<close>

ML\<open> fun ctxt_n_trm_to_commutativity (ctxt:Proof.context) (func:term) =
(*f (x, y) = f (y, x)*)
if takes_n_arguments 2 func andalso all_args_are_same_typ [func]
then
  let
    val func_w_dummyT = strip_atype func: term;
    val (var1,var2)   = Utils.map_pair (mk_free_variable_of_typ dummyT) (1,2): (term * term);
    val lhs           = list_comb (func_w_dummyT, [var1,var2]);
    val rhs           = list_comb (func_w_dummyT, [var2,var1]);
    val commutativity = mk_eq (lhs, rhs): term;
    val result = Syntax.check_term ctxt commutativity |> ctxt_consts_string_trm_to_conjecture ctxt [func] "commutativity";
  in [result] end
else [];
\<close>

ML\<open> fun ctxt_n_typ_to_nullary_const' (ctxt:Proof.context) (typ:typ) =
(*as a candidate for the identity element*)
let
  val typ_as_string   = Syntax.string_of_typ ctxt typ
      |> YXML.parse_body
      |> XML.content_of : string;
  val const_typ_pairs = pretty_consts ctxt [(true, Find_Consts.Strict typ_as_string)]: (string * typ) list;
  val const_names     = map fst const_typ_pairs                                      : strings;
  val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) const_names          : terms;
in
  consts_w_dummyT: terms
end;

fun ctxt_n_typ_to_nullary_const ctxt typ = try (ctxt_n_typ_to_nullary_const' ctxt) typ |> Utils.is_some_null;
\<close>

ML\<open> fun ctxt_n_typ_to_unary_const' (ctxt:Proof.context) (typ:typ) =
(*as a candidate for the identity element*)
let
  val func_typ = typ --> typ: typ;
  val typ_as_string   = Syntax.string_of_typ ctxt func_typ
      |> YXML.parse_body
      |> XML.content_of : string;
  val const_typ_pairs = pretty_consts ctxt [(true, Find_Consts.Strict typ_as_string)]: (string * typ) list;
  val const_names     = map fst const_typ_pairs                                      : strings;
  val consts_w_dummyT = map (fn cname => Const (cname, dummyT)) const_names          : terms;
in
  consts_w_dummyT: terms
end;

fun ctxt_n_typ_to_unary_const ctxt typ = try (ctxt_n_typ_to_unary_const' ctxt) typ |> Utils.is_some_null;
\<close>

ML\<open> ctxt_n_typ_to_unary_const @{context} @{typ "Nat"} \<close>

ML\<open>
datatype direction = Left | Right;
\<close>
(*We assume func is a binary function.*)
ML\<open> fun ctxt_n_direct_n_trm_to_identity (ctxt:Proof.context) (direct:direction) (func as Const (_, typ):term) =
(*left identity : f (e, x) = x*)
(*right identity: f (x, e) = x*)
  if takes_n_arguments 2 func andalso all_args_are_same_typ [func]
  then
    let
      val typ_of_arg     = binder_types typ |> (case direct of
                            Left  =>  List.hd
                          | Right => (Utils.the' "ctxt_n_trm_to_identity in Bottom_Up_Conjecturing.ML failed"
                                    o try (fn args => nth args 1)))   : typ;
      val nullary_consts = ctxt_n_typ_to_nullary_const ctxt typ_of_arg: terms;
      val func_w_dummyT  = strip_atype func                   : term;
      val free_var       = mk_free_variable_of_typ dummyT 1           : term;
      fun mk_equation (identity_element:term) =
        let
          val lhs = case direct of
              Left  => list_comb (func_w_dummyT, [identity_element, free_var]): term
            | Right => list_comb (func_w_dummyT, [free_var, identity_element]): term;
          val rhs = free_var                                                  : term;
          val eq  = mk_eq (lhs, rhs)                                  : term;
        in
          Syntax.check_term ctxt eq
        end;
    in
      map mk_equation nullary_consts
    end
  else []
  | ctxt_n_direct_n_trm_to_identity _ _ _ = [];
\<close>

ML\<open>ctxt_n_direct_n_trm_to_identity @{context} Right @{term "qrev"}
|> map (Isabelle_Utils.trm_to_string @{context})
|> map tracing;
\<close>

ML\<open> fun ctxt_n_trm_to_invertibility (ctxt:Proof.context) (identity_element as Const _:term) (func as Const _:term) =
(*f (x,y) = e: x is the left inverse of y and y is the right inverse of x*)
  if takes_n_arguments 2 func andalso all_args_are_same_typ [func]
  then
    let
      val func_w_dummyT           = strip_atype func                                     : term;
      val (var1, var2)            = Utils.map_pair (mk_free_variable_of_typ dummyT) (1,2): (term * term);
      val identity_element_wo_typ = strip_atype identity_element                         : term;
      val lhs                     = list_comb (func_w_dummyT, [var1, var2])              : term;
      val invertibility           = mk_eq (lhs, identity_element_wo_typ)                 : term;
    in
      [Syntax.check_term ctxt invertibility: term] |> map (ctxt_consts_string_trm_to_conjecture ctxt [identity_element, func] "invertibility")
    end
  else []
| ctxt_n_trm_to_invertibility _ _ _ = [];
\<close>

ML\<open> ctxt_n_trm_to_invertibility @{context} @{term "nil2"}  @{term "qrev"}
 |> map #lemma_stmt
 |> map tracing;
\<close>

(*TODO: check the input functions are constants and binary of the same type.*)
ML\<open> fun ctxt_n_trms_to_distributivity (ctxt:Proof.context) (func1, func2) =
(* left-distributive:  f (x, g (y, z)) = g (f (x, y), f (x, z))
 * right-distributive: f (g (x, y), z) = g (f (x, y), f (x, z))
 *)
  if takes_n_arguments 2 func1 andalso takes_n_arguments 2 func2 andalso all_args_are_same_typ [func1, func2]
  then
    let
      val (func1_wo_typ, func2_wo_typ) = Utils.map_pair strip_atype (func1, func2): (term * term);
      val [var1, var2, var3]           = map (mk_free_variable_of_typ dummyT) [1,2,3]     : terms;
      val (left_lhs, right_lhs)        =  (list_comb (func1_wo_typ, [var1,                                  list_comb (func2_wo_typ, [var2, var3])]),
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
      val (left, right)                = (mk_eq (left_lhs, left_rhs), mk_eq (right_lhs, right_rhs)) |> Utils.map_pair (Syntax.check_term ctxt);
    in
     [ctxt_consts_string_trm_to_conjecture ctxt [func1, func2] "left_distributivity"  left,
      ctxt_consts_string_trm_to_conjecture ctxt [func1, func2] "right_distributivity" right]
    end
  else [];
\<close>

ML\<open> ctxt_n_trms_to_distributivity @{context} (@{term "x"}, @{term "qrev"})
|> map #lemma_stmt
|> map tracing;
\<close>

ML\<open> fun ctxt_n_trms_to_anti_distributivity (ctxt:Proof.context) (unary_func, binary_func) =
(*distributivity of f on g*)
(*f (g (x, y)) = g (f (y), f (x))*)
if takes_n_arguments 1 unary_func  andalso
   takes_n_arguments 2 binary_func andalso
   all_args_are_same_typ [unary_func, binary_func]
then
  let
    val (unary_wo_typ, binary_wo_typ) = Utils.map_pair strip_atype (unary_func, binary_func): (term * term);
    val (var1, var2)                  = Utils.map_pair (mk_free_variable_of_typ dummyT) (1,2)       : (term * term);
    val lhs                           = list_comb (unary_wo_typ, [list_comb (binary_wo_typ, [var1, var2])]): term;
    val rhs                           = (list_comb
                                         (binary_wo_typ,
                                          [list_comb (unary_wo_typ, [var2]),
                                           list_comb (unary_wo_typ, [var1])
                                           ]
                                          )
                                        );
    val anti_distributivity           = mk_eq (lhs, rhs) |> Syntax.check_term ctxt;
  in
    [ctxt_consts_string_trm_to_conjecture ctxt [unary_func, binary_func] "left_distributivity" anti_distributivity]
  end
else [];
\<close>

ML\<open> ctxt_n_trms_to_anti_distributivity @{context} (@{term "rev"}, @{term "qrev"})
|> map #lemma_stmt
|> map tracing;
\<close>

ML\<open> fun ctxt_n_trms_to_homomorphism_2 (ctxt:Proof.context) (homomorphism:term, preserved_binary:term) =
(*f is homomorphism.*)
(*f (g (x, y)) = g (f (x), f (y))*)
if takes_n_arguments 1 homomorphism andalso
   takes_n_arguments 2 preserved_binary andalso
   all_args_are_same_typ [homomorphism, preserved_binary]
then
  let
    val (homomorphism_wo_typ, preserved_binary_wo_typ) = Utils.map_pair strip_atype (homomorphism, preserved_binary): term * term;
    val (var1, var2) = Utils.map_pair (mk_free_variable_of_typ dummyT) (1,2)                                                : (term * term);
    val lhs          = (homomorphism_wo_typ $ list_comb (preserved_binary_wo_typ, [var1, var2]))                            : term;
    val rhs          = list_comb (preserved_binary_wo_typ, [homomorphism_wo_typ $ var1, homomorphism_wo_typ $ var2])        : term;
    val proprerty    = mk_eq (lhs, rhs) |> Syntax.check_term ctxt                                                   : term;
  in
    [ctxt_consts_string_trm_to_conjecture ctxt [homomorphism,preserved_binary] "homomorphism"  proprerty]
  end
else [];
\<close>

end