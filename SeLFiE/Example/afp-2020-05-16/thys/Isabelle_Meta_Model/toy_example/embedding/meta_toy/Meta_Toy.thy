(******************************************************************************
 * HOL-TOY
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

section\<open>Toy Meta-Model aka. AST definition of Toy (I)\<close>

theory  Meta_Toy
imports "../../../meta_isabelle/Meta_Pure"
        "../Init_rbt"
begin

subsection\<open>Type Definition\<close>

datatype toy_collection = Set
                        | Sequence
                        | Ordered0 \<comment> \<open>ordered set\<close>
                        | Subsets0 \<comment> \<open>binding\<close>
                        | Union0
                        | Redefines0 \<comment> \<open>binding\<close>
                        | Derived0 \<comment> \<open>string\<close>
                        | Qualifier0 \<comment> \<open>binding \<open>\<times> use_toyty\<close>\<close>
                        | Nonunique0 \<comment> \<open>bag\<close>

datatype toy_multiplicity_single = Mult_nat nat
                                 | Mult_star
                                 | Mult_infinity

record toy_multiplicity = TyMult :: "(toy_multiplicity_single \<times> toy_multiplicity_single option) list"
                          TyRole :: "string option"
                          TyCollect :: "toy_collection list" \<comment> \<open>return type of the accessor (constrained by the above multiplicity)\<close>

record toy_ty_class_node =  TyObjN_ass_switch :: nat
                            TyObjN_role_multip :: toy_multiplicity
                            TyObjN_role_ty :: string
record toy_ty_class =       TyObj_name :: string
                            TyObj_ass_id :: nat
                            TyObj_ass_arity :: nat
                            TyObj_from :: toy_ty_class_node
                            TyObj_to :: toy_ty_class_node
datatype toy_ty_obj_core =  ToyTyCore_pre string \<comment> \<open>class name, untyped\<close> (* FIXME perform the typing separately *)
                          | ToyTyCore toy_ty_class \<comment> \<open>class name, typed\<close>
datatype toy_ty_obj =       ToyTyObj  toy_ty_obj_core
                                     "toy_ty_obj_core list \<comment> \<open>the \<^theory_text>\<open>and\<close> semantics\<close>
                                                           list \<comment> \<open>\<open>x # \<dots>\<close> means \<open>x < \<dots>\<close>\<close>" \<comment> \<open>superclass\<close>
datatype toy_ty =           ToyTy_base_void (* NOTE can be merged in a generic tuple *)
                          | ToyTy_base_boolean
                          | ToyTy_base_integer
                          | ToyTy_base_unlimitednatural
                          | ToyTy_base_real
                          | ToyTy_base_string
                          | ToyTy_object toy_ty_obj
                          | ToyTy_collection toy_multiplicity toy_ty
                          | ToyTy_pair toy_ty toy_ty (* NOTE can be merged in a generic tuple *)
                          | ToyTy_binding "string option \<comment> \<open>name\<close> \<times> toy_ty" (* NOTE can be merged in a generic tuple *)
                          | ToyTy_arrow toy_ty toy_ty
                          | ToyTy_class_syn string
                          | ToyTy_enum string
                          | ToyTy_raw string \<comment> \<open>denoting raw HOL-type\<close> (* FIXME to be removed *)


datatype toy_association_type = ToyAssTy_native_attribute
                              | ToyAssTy_association
                              | ToyAssTy_composition
                              | ToyAssTy_aggregation
datatype toy_association_relation = ToyAssRel "(toy_ty_obj \<times> toy_multiplicity) list"
record toy_association =        ToyAss_type     :: toy_association_type
                                ToyAss_relation :: toy_association_relation

datatype toy_ctxt_prefix = ToyCtxtPre | ToyCtxtPost

datatype toy_ctxt_term = T_pure "term"
                       | T_to_be_parsed string \<comment> \<open>raw, it includes extra quoting characters like DEL (char 127)\<close>
                                        string \<comment> \<open>same string but escaped without those quoting characters\<close>
                       | T_lambda string toy_ctxt_term
datatype toy_prop = ToyProp_ctxt "string option" \<comment> \<open>name\<close> toy_ctxt_term
                  (*| ToyProp_rel toy_ty_obj (* states that the constraint should be true *)
                  | ToyProp_ass toy_association_relation (* states the relation as true *)*)
datatype toy_ctxt_term_inv = T_inv bool \<comment> \<open>True: existential\<close> toy_prop
datatype toy_ctxt_term_pp = T_pp toy_ctxt_prefix toy_prop
                          | T_invariant toy_ctxt_term_inv

record toy_ctxt_pre_post = Ctxt_fun_name :: string \<comment> \<open>function name\<close>
                           Ctxt_fun_ty :: toy_ty
                           Ctxt_expr :: "toy_ctxt_term_pp list"

datatype toy_ctxt_clause = Ctxt_pp toy_ctxt_pre_post
                         | Ctxt_inv toy_ctxt_term_inv
record toy_ctxt = Ctxt_param :: "string list" \<comment> \<open>param\<close>
                  Ctxt_ty :: toy_ty_obj
                  Ctxt_clause :: "toy_ctxt_clause list"

datatype toy_class =   ToyClass
                         string \<comment> \<open>name of the class\<close>
                         "(string \<comment> \<open>name\<close> \<times> toy_ty) list" \<comment> \<open>attribute\<close>
                         "toy_class list" \<comment> \<open>link to subclasses\<close>

record toy_class_raw = ClassRaw_name :: toy_ty_obj
                       ClassRaw_own :: "(string \<comment> \<open>name\<close> \<times> toy_ty) list" \<comment> \<open>attribute\<close>
                       ClassRaw_clause :: "toy_ctxt_clause list"
                       ClassRaw_abstract :: bool \<comment> \<open>True: abstract\<close>

datatype toy_ass_class = ToyAssClass toy_association
                                     toy_class_raw

datatype toy_class_synonym = ToyClassSynonym string \<comment> \<open>name alias\<close> toy_ty

datatype toy_enum = ToyEnum string \<comment> \<open>name\<close> "string \<comment> \<open>constructor name\<close> list"

subsection\<open>Extending the Meta-Model\<close>

definition "T_lambdas = List.fold T_lambda"
definition "TyObjN_role_name = TyRole o TyObjN_role_multip"
definition "ToyTy_class c = ToyTy_object (ToyTyObj (ToyTyCore c) [])"
definition "ToyTy_class_pre c = ToyTy_object (ToyTyObj (ToyTyCore_pre c) [])"
definition "ToyAss_relation' l = (case ToyAss_relation l of ToyAssRel l \<Rightarrow> l)"

fun fold_pair_var where
   "fold_pair_var f t accu = (case t of
    ToyTy_pair t1 t2 \<Rightarrow> Option.bind (fold_pair_var f t1 accu) (fold_pair_var f t2)
  | ToyTy_binding (Some v, t) \<Rightarrow> fold_pair_var f t (f (v, t) accu)
  | ToyTy_binding (None, t) \<Rightarrow> fold_pair_var f t accu
  | ToyTy_collection _ t \<Rightarrow> fold_pair_var f t accu
  | ToyTy_arrow _ _ \<Rightarrow> None
  | _ \<Rightarrow> Some accu)"

definition "Ctxt_fun_ty_arg ctxt =
 (case 
    fold_pair_var
      Cons
      (case Ctxt_fun_ty ctxt of ToyTy_arrow t _ \<Rightarrow> t
                              | t \<Rightarrow> t)
      []
  of Some l \<Rightarrow> rev l)"

definition "Ctxt_fun_ty_out ctxt =
 (case Ctxt_fun_ty ctxt of ToyTy_arrow _ t \<Rightarrow> Some t
                         | _ \<Rightarrow> None)"

definition "map_pre_post f = 
             Ctxt_clause_update
               (L.map 
                  (\<lambda> Ctxt_pp ctxt \<Rightarrow>
                     Ctxt_pp (Ctxt_expr_update
                               (L.map
                                  (\<lambda> T_pp pref (ToyProp_ctxt n e) \<Rightarrow>
                                     T_pp pref (ToyProp_ctxt n (f pref ctxt e))
                                   | x \<Rightarrow> x))
                               ctxt)
                   | x \<Rightarrow> x))"

definition "map_invariant f_inv =
             Ctxt_clause_update
               (L.map 
                  (\<lambda> Ctxt_pp ctxt \<Rightarrow>
                     Ctxt_pp (Ctxt_expr_update
                               (L.map
                                 (\<lambda> T_invariant ctxt \<Rightarrow> T_invariant (f_inv ctxt)
                                  | x \<Rightarrow> x))
                               ctxt)
                   | Ctxt_inv ctxt \<Rightarrow> Ctxt_inv (f_inv ctxt)))"

fun remove_binding where
   "remove_binding e = (\<lambda> ToyTy_collection m ty \<Rightarrow> ToyTy_collection m (remove_binding ty)
                        | ToyTy_pair ty1 ty2 \<Rightarrow> ToyTy_pair (remove_binding ty1) (remove_binding ty2)
                        | ToyTy_binding (_, ty) \<Rightarrow> remove_binding ty
                        | ToyTy_arrow ty1 ty2 \<Rightarrow> ToyTy_arrow (remove_binding ty1) (remove_binding ty2)
                        | x \<Rightarrow> x) e"

subsection\<open>Class Translation Preliminaries\<close>

definition "const_oid = \<open>oid\<close>"
definition "var_ty_list = \<open>list\<close>"
definition "var_ty_prod = \<open>prod\<close>"
definition "const_toyany = \<open>ToyAny\<close>"

definition "single_multip = 
  List.list_all (\<lambda> (_, Some (Mult_nat n)) \<Rightarrow> n \<le> 1
                 | (Mult_nat n, None) \<Rightarrow> n \<le> 1
                 | _ \<Rightarrow> False) o TyMult"

fun fold_max_aux where
   "fold_max_aux f l l_acc accu = (case l of
      [] \<Rightarrow> accu
    | x # xs \<Rightarrow> fold_max_aux f xs (x # l_acc) (f x (L.flatten [rev l_acc, xs]) accu))"

definition "fold_max f l = fold_max_aux f (L.mapi Pair l) []"

locale RBTS
begin
definition "lookup m k = RBT.lookup m (String.to_list k)"
definition insert where "insert k = RBT.insert (String.to_list k)"
definition "map_entry k = RBT.map_entry (String.to_list k)"
definition "modify_def v k = RBT.modify_def v (String.to_list k)"
definition "keys m = L.map (\<lambda>s. \<lless>s\<ggreater>) (RBT.keys m)"
definition "lookup2 m = (\<lambda>(k1, k2). RBT.lookup2 m (String.to_list k1, String.to_list k2))"
definition "insert2 = (\<lambda>(k1, k2). RBT.insert2 (String.to_list k1, String.to_list k2))"
definition fold where "fold f = RBT.fold (\<lambda>c. f \<lless>c\<ggreater>)"
definition "entries m = L.map (map_prod (\<lambda>c. \<lless>c\<ggreater>) id) (RBT.entries m)"
end
lemmas [code] =
  \<comment> \<open>def\<close>
  RBTS.lookup_def
  RBTS.insert_def
  RBTS.map_entry_def
  RBTS.modify_def_def
  RBTS.keys_def
  RBTS.lookup2_def
  RBTS.insert2_def
  RBTS.fold_def
  RBTS.entries_def

syntax "_rbt_lookup" :: "_ \<Rightarrow> _" ("lookup") translations "lookup" \<rightleftharpoons> "CONST RBTS.lookup"
syntax "_rbt_insert" :: "_ \<Rightarrow> _" ("insert") translations "insert" \<rightleftharpoons> "CONST RBTS.insert"
syntax "_rbt_map_entry" :: "_ \<Rightarrow> _" ("map'_entry") translations "map_entry" \<rightleftharpoons> "CONST RBTS.map_entry"
syntax "_rbt_modify_def" :: "_ \<Rightarrow> _" ("modify'_def") translations "modify_def" \<rightleftharpoons> "CONST RBTS.modify_def"
syntax "_rbt_keys" :: "_ \<Rightarrow> _" ("keys") translations "keys" \<rightleftharpoons> "CONST RBTS.keys"
syntax "_rbt_lookup2" :: "_ \<Rightarrow> _" ("lookup2") translations "lookup2" \<rightleftharpoons> "CONST RBTS.lookup2"
syntax "_rbt_insert2" :: "_ \<Rightarrow> _" ("insert2") translations "insert2" \<rightleftharpoons> "CONST RBTS.insert2"
syntax "_rbt_fold" :: "_ \<Rightarrow> _" ("fold") translations "fold" \<rightleftharpoons> "CONST RBTS.fold"
syntax "_rbt_entries" :: "_ \<Rightarrow> _" ("entries") translations "entries" \<rightleftharpoons> "CONST RBTS.entries"

function (sequential) class_unflat_aux where
(* (* FIXME replace with this simplified form *)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_cycle r of (None \<comment> \<open>cycle detection\<close>) \<Rightarrow>
      ToyClass
        r
        (case lookup rbt r of Some l \<Rightarrow> l)
        (L.map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          (case lookup rbt_inv r of None \<Rightarrow> [] | Some l \<Rightarrow> l)))"
*)
   "class_unflat_aux rbt rbt_inv rbt_cycle r =
   (case lookup rbt_inv r of
  None \<Rightarrow>
(case lookup rbt_cycle r of (None \<comment> \<open>cycle detection\<close>) \<Rightarrow>
      ToyClass
        r
        (case lookup rbt r of Some l \<Rightarrow> l)
        ( ( [])))
| Some l \<Rightarrow>
(case lookup rbt_cycle r of (None \<comment> \<open>cycle detection\<close>) \<Rightarrow>
      ToyClass
        r
        (case lookup rbt r of Some l \<Rightarrow> l)
        (L.map
          (class_unflat_aux rbt rbt_inv (insert r () rbt_cycle))
          ( l))))"
by pat_completeness auto

termination
proof -
 have arith_diff: "\<And>a1 a2 (b :: Nat.nat). a1 = a2 \<Longrightarrow> a1 > b \<Longrightarrow> a1 - (b + 1) < a2 - b"
 by arith

 have arith_less: "\<And>(a:: Nat.nat) b c. b \<ge> max (a + 1) c \<Longrightarrow> a < b"
 by arith

 have rbt_length: "\<And>rbt_cycle r v. RBT.lookup rbt_cycle r = None \<Longrightarrow>
     length (RBT.keys (RBT.insert r v rbt_cycle)) = length (RBT.keys rbt_cycle) + 1"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
 by (metis card_insert_if domIff finite_dom_lookup)

 have rbt_fold_union'': "\<And>ab a x k. dom (\<lambda>b. if b = ab then Some a else k b) = {ab} \<union> dom k"
 by(auto)

 have rbt_fold_union': "\<And>l rbt_inv a.
       dom (RBT.lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (RBT.lookup rbt_inv)"
  apply(rule_tac P = "\<lambda>rbt_inv . dom (RBT.lookup (List.fold (\<lambda>(k, _). RBT.insert k a) l rbt_inv)) =
       dom (map_of l) \<union> dom (RBT.lookup rbt_inv)" in allE, simp_all)
  apply(induct_tac l, simp, rule allI)
  apply(case_tac aa, simp)
  apply(simp add: rbt_fold_union'')
 done

 have rbt_fold_union: "\<And>rbt_cycle rbt_inv a.
   dom (RBT.lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (RBT.lookup rbt_cycle) \<union> dom (RBT.lookup rbt_inv)"
  apply(simp add: fold_fold)
  apply(subst (2) map_of_entries[symmetric])
  apply(rule rbt_fold_union')
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv a b.
   dom (RBT.lookup (RBT.fold (\<lambda>k _. RBT.insert k a) rbt_cycle rbt_inv)) =
   dom (RBT.lookup (RBT.fold (\<lambda>k _. RBT.insert k b) rbt_inv rbt_cycle))"
 by(simp add: rbt_fold_union Un_commute)

 let ?len = "\<lambda>x. length (RBT.keys x)"
 let ?len_merge = "\<lambda>rbt_cycle rbt_inv. ?len (RBT.fold (\<lambda>k _. RBT.insert k []) rbt_cycle rbt_inv)"

 have rbt_fold_large: "\<And>rbt_cycle rbt_inv. ?len_merge rbt_cycle rbt_inv \<ge> max (?len rbt_cycle) (?len rbt_inv)"
  apply(subst (1 2 3) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric], simp)
  apply(subst (1 2) card_mono, simp_all)
  apply(simp add: rbt_fold_union)+
 done

 have rbt_fold_eq: "\<And>rbt_cycle rbt_inv r a.
     RBT.lookup rbt_inv r = Some a \<Longrightarrow>
     ?len_merge (RBT.insert r () rbt_cycle) rbt_inv = ?len_merge rbt_cycle rbt_inv"
  apply(subst (1 2) distinct_card[symmetric], (rule distinct_keys)+)
  apply(simp only: lookup_keys[symmetric])
  apply(simp add: rbt_fold_union)
 by (metis Un_insert_right insert_dom)

 show ?thesis
  apply(relation "measure (\<lambda>(_, rbt_inv, rbt_cycle, _).
                           ?len_merge rbt_cycle rbt_inv - ?len rbt_cycle)"
       , simp+)
  unfolding RBTS.lookup_def RBTS.insert_def
  apply(subst rbt_length, simp)
  apply(rule arith_diff)
  apply(rule rbt_fold_eq, simp)
  apply(rule arith_less)
  apply(subst rbt_length[symmetric], simp)
  apply(rule rbt_fold_large)
 done
qed
definition "ty_obj_to_string = (\<lambda>ToyTyObj (ToyTyCore_pre s) _ \<Rightarrow> s)"
definition "cl_name_to_string = ty_obj_to_string o ClassRaw_name"

definition "class_unflat = (\<lambda> (l_class, l_ass).
  let l =
    let const_toyany' = ToyTyCore_pre const_toyany
      ; rbt = \<comment> \<open>fold classes:\<close>
              \<comment> \<open>set \<open>ToyAny\<close> as default inherited class (for all classes linking to zero inherited classes)\<close>
              insert
                const_toyany
                (toy_class_raw.make (ToyTyObj const_toyany' []) [] [] False)
                (List.fold
                  (\<lambda> cflat \<Rightarrow>
                    insert (cl_name_to_string cflat) (cflat \<lparr> ClassRaw_name := case ClassRaw_name cflat of ToyTyObj n [] \<Rightarrow> ToyTyObj n [[const_toyany']] | x \<Rightarrow> x \<rparr>))
                  l_class
                  RBT.empty) in
    \<comment> \<open>fold associations:\<close>
    \<comment> \<open>add remaining 'object' attributes\<close>
    L.map snd (entries (List.fold (\<lambda> (ass_oid, ass) \<Rightarrow>
      let l_rel = ToyAss_relation' ass in
      fold_max
        (let n_rel = natural_of_nat (List.length l_rel) in
         (\<lambda> (cpt_to, (name_to, category_to)).
           case TyRole category_to of
             Some role_to \<Rightarrow>
               List.fold (\<lambda> (cpt_from, (name_from, mult_from)).
                 let name_from = ty_obj_to_string name_from in
                 map_entry name_from (\<lambda>cflat. cflat \<lparr> ClassRaw_own := (role_to,
                   ToyTy_class (toy_ty_class_ext const_oid ass_oid n_rel
                     (toy_ty_class_node_ext cpt_from mult_from name_from ())
                     (toy_ty_class_node_ext cpt_to category_to (ty_obj_to_string name_to) ())
                     ())) # ClassRaw_own cflat \<rparr>))
           | _ \<Rightarrow> \<lambda>_. id))
        l_rel) (L.mapi Pair l_ass) rbt)) in
  class_unflat_aux
    (List.fold (\<lambda> cflat. insert (cl_name_to_string cflat) (L.map (map_prod id remove_binding) (ClassRaw_own cflat))) l RBT.empty)
    (List.fold
      (\<lambda> cflat.
        case ClassRaw_name cflat of
          ToyTyObj n [] \<Rightarrow> id
        | ToyTyObj n l \<Rightarrow> case rev ([n] # l) of x0 # xs \<Rightarrow> \<lambda>rbt. 
            snd (List.fold
                  (\<lambda> x (x0, rbt).
                    (x, List.fold (\<lambda> ToyTyCore_pre k \<Rightarrow> modify_def [] k (\<lambda>l. L.flatten [L.map (\<lambda>ToyTyCore_pre s \<Rightarrow> s) x, l]))
                                  x0
                                  rbt))
                  xs
                  (x0, rbt)))
      l
      RBT.empty)
    RBT.empty
    const_toyany)"

definition "apply_optim_ass_arity ty_obj v =
  (if TyObj_ass_arity ty_obj \<le> 2 then None
   else Some v)"

definition "is_higher_order = (\<lambda> ToyTy_collection _ _ \<Rightarrow> True | ToyTy_pair _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition "parse_ty_raw = (\<lambda> ToyTy_raw s \<Rightarrow> if s = \<open>int\<close> then ToyTy_base_integer else ToyTy_raw s
                            | x \<Rightarrow> x)"

definition "is_sequence = list_ex (\<lambda> Sequence \<Rightarrow> True | _ \<Rightarrow> False) o TyCollect"

fun str_of_ty where "str_of_ty e =
 (\<lambda> ToyTy_base_void \<Rightarrow> \<open>Void\<close>
  | ToyTy_base_boolean \<Rightarrow> \<open>Boolean\<close>
  | ToyTy_base_integer \<Rightarrow> \<open>Integer\<close>
  | ToyTy_base_unlimitednatural \<Rightarrow> \<open>UnlimitedNatural\<close>
  | ToyTy_base_real \<Rightarrow> \<open>Real\<close>
  | ToyTy_base_string \<Rightarrow> \<open>String\<close>
  | ToyTy_object (ToyTyObj (ToyTyCore_pre s) _) \<Rightarrow> s
  \<^cancel>\<open>| ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _)\<close>
  | ToyTy_collection t toy_ty \<Rightarrow> (if is_sequence t then
                                    S.flatten [\<open>Sequence(\<close>, str_of_ty toy_ty,\<open>)\<close>]
                                  else
                                    S.flatten [\<open>Set(\<close>, str_of_ty toy_ty,\<open>)\<close>])
  | ToyTy_pair toy_ty1 toy_ty2 \<Rightarrow> S.flatten [\<open>Pair(\<close>, str_of_ty toy_ty1, \<open>,\<close>, str_of_ty toy_ty2,\<open>)\<close>]
  | ToyTy_binding (_, toy_ty) \<Rightarrow> str_of_ty toy_ty
  | ToyTy_class_syn s \<Rightarrow> s
  | ToyTy_enum s \<Rightarrow> s
  | ToyTy_raw s \<Rightarrow> S.flatten [\<open>\<acute>\<close>, s, \<open>\<acute>\<close>]) e"

definition "ty_void = str_of_ty ToyTy_base_void"
definition "ty_boolean = str_of_ty ToyTy_base_boolean"
definition "ty_integer = str_of_ty ToyTy_base_integer"
definition "ty_unlimitednatural = str_of_ty ToyTy_base_unlimitednatural"
definition "ty_real = str_of_ty ToyTy_base_real"
definition "ty_string = str_of_ty ToyTy_base_string"

definition "pref_ty_enum s = \<open>ty_enum\<close> @@ String.isub s"
definition "pref_ty_syn s = \<open>ty_syn\<close> @@ String.isub s"
definition "pref_constr_enum s = \<open>constr\<close> @@ String.isub s"

fun str_hol_of_ty_all where "str_hol_of_ty_all f b e =
 (\<lambda> ToyTy_base_void \<Rightarrow> b \<open>unit\<close>
  | ToyTy_base_boolean \<Rightarrow> b \<open>bool\<close>
  | ToyTy_base_integer \<Rightarrow> b \<open>int\<close>
  | ToyTy_base_unlimitednatural \<Rightarrow> b \<open>nat\<close>
  | ToyTy_base_real \<Rightarrow> b \<open>real\<close>
  | ToyTy_base_string \<Rightarrow> b \<open>string\<close>
  | ToyTy_object (ToyTyObj (ToyTyCore_pre s) _) \<Rightarrow> b const_oid
  | ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _) \<Rightarrow> f (b var_ty_list) [b (TyObj_name ty_obj)]
  | ToyTy_collection _ ty \<Rightarrow> f (b var_ty_list) [str_hol_of_ty_all f b ty]
  | ToyTy_pair ty1 ty2 \<Rightarrow> f (b var_ty_prod) [str_hol_of_ty_all f b ty1, str_hol_of_ty_all f b ty2]
  | ToyTy_binding (_, t) \<Rightarrow> str_hol_of_ty_all f b t
  | ToyTy_class_syn s \<Rightarrow> b (pref_ty_syn s)
  | ToyTy_enum s \<Rightarrow> b (pref_ty_enum s)
  | ToyTy_raw s \<Rightarrow> b s) e"

fun get_class_hierarchy_strict_aux where
   "get_class_hierarchy_strict_aux dataty l_res =
   (List.fold
     (\<lambda> ToyClass name l_attr dataty \<Rightarrow> \<lambda> l_res.
       get_class_hierarchy_strict_aux dataty (ToyClass name l_attr dataty # l_res))
     dataty
     l_res)"
definition "get_class_hierarchy_strict d = get_class_hierarchy_strict_aux d []"

fun get_class_hierarchy'_aux where
   "get_class_hierarchy'_aux l_res (ToyClass name l_attr dataty) =
   (let l_res = ToyClass name l_attr dataty # l_res in
    case dataty of [] \<Rightarrow> rev l_res
                 | dataty \<Rightarrow> List.fold (\<lambda>x acc. get_class_hierarchy'_aux acc x) dataty l_res)"
definition "get_class_hierarchy' = get_class_hierarchy'_aux []"

definition "get_class_hierarchy e = L.map (\<lambda> ToyClass n l _ \<Rightarrow> (n, l)) (get_class_hierarchy' e)"

definition "var_in_pre_state = \<open>in_pre_state\<close>"
definition "var_in_post_state = \<open>in_post_state\<close>"
definition "var_at_when_hol_post = \<open>\<close>"
definition "var_at_when_hol_pre = \<open>at_pre\<close>"
definition "var_at_when_toy_post = \<open>\<close>"
definition "var_at_when_toy_pre = \<open>@pre\<close>"

datatype 'a tmp_sub = Tsub 'a
record 'a inheritance =
  Inh :: 'a
  Inh_sib :: "('a \<times> 'a list \<comment> \<open>flat version of the 1st component\<close>) list" \<comment> \<open>sibling\<close>
  Inh_sib_unflat :: "'a list" \<comment> \<open>sibling\<close>
datatype 'a tmp_inh = Tinh 'a
datatype 'a tmp_univ = Tuniv 'a
definition "of_inh = (\<lambda>Tinh l \<Rightarrow> l)"
definition "of_linh = L.map Inh"
definition "of_sub = (\<lambda>Tsub l \<Rightarrow> l)"
definition "of_univ = (\<lambda>Tuniv l \<Rightarrow> l)"
definition "map_inh f = (\<lambda>Tinh l \<Rightarrow> Tinh (f l))"

fun fold_class_gen_aux where
   "fold_class_gen_aux l_inh f accu (ToyClass name l_attr dataty) =
 (let accu = f (\<lambda>s. s @@ String.isub name)
               name
               l_attr
               (Tinh l_inh)
               (Tsub (get_class_hierarchy_strict dataty)) \<comment> \<open>order: bfs or dfs (modulo reversing)\<close>
               dataty
               accu in
  case dataty of [] \<Rightarrow> accu
               | _ \<Rightarrow>
    fst (List.fold
       (\<lambda> node (accu, l_inh_l, l_inh_r).
         ( fold_class_gen_aux
             ( \<lparr> Inh = ToyClass name l_attr dataty
               , Inh_sib = L.flatten (L.map (L.map (\<lambda>l. (l, get_class_hierarchy' l))) [l_inh_l, tl l_inh_r])
               , Inh_sib_unflat = L.flatten [l_inh_l, tl l_inh_r] \<rparr>
             # l_inh)
             f accu node
         , hd l_inh_r # l_inh_l
         , tl l_inh_r))
      dataty
      (accu, [], dataty)))"

definition "fold_class_gen f accu expr =
 (let (l_res, accu) =
    fold_class_gen_aux
      []
      (\<lambda> isub_name name l_attr l_inh l_subtree next_dataty (l_res, accu).
        let (r, accu) = f isub_name name l_attr l_inh l_subtree next_dataty accu in
        (r # l_res, accu))
      ([], accu)
      expr in
  (L.flatten l_res, accu))"

definition "map_class_gen f = fst o fold_class_gen
  (\<lambda> isub_name name l_attr l_inh l_subtree last_d. \<lambda> () \<Rightarrow>
    (f isub_name name l_attr l_inh l_subtree last_d, ())) ()"

definition "add_hierarchy'''' f x = (\<lambda>isub_name name l_attr l_inh l_subtree _. f isub_name name (Tuniv (get_class_hierarchy x)) l_attr (map_inh (L.map (\<lambda> ToyClass _ l _ \<Rightarrow> l) o of_linh) l_inh) l_subtree)"
definition "map_class f = map_class_gen (\<lambda>isub_name name l_attr l_inh l_subtree next_dataty. [f isub_name name l_attr l_inh (Tsub (L.map (\<lambda> ToyClass n _ _ \<Rightarrow> n) (of_sub l_subtree))) next_dataty])"
definition "fold_class f = fold_class_gen (\<lambda>isub_name name l_attr l_inh l_subtree next_dataty accu. let (x, accu) = f isub_name name l_attr (map_inh of_linh l_inh) (Tsub (L.map (\<lambda> ToyClass n _ _ \<Rightarrow> n) (of_sub l_subtree))) next_dataty accu in ([x], accu))"
definition "map_class_gen_h'''' f x = map_class_gen (add_hierarchy'''' (\<lambda>isub_name name l_inherited l_attr l_inh l_subtree. f isub_name name l_inherited l_attr l_inh (Tsub (L.map (\<lambda> ToyClass n _ _ \<Rightarrow> n) (of_sub l_subtree)))) x) x"

definition "class_arity = RBT.keys o (\<lambda>l. List.fold (\<lambda>x. RBT.insert x ()) l RBT.empty) o
  L.flatten o L.flatten o map_class (\<lambda> _ _ l_attr _ _ _.
    L.map (\<lambda> (_, ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _)) \<Rightarrow> [TyObj_ass_arity ty_obj]
              | _ \<Rightarrow> []) l_attr)"

definition "map_class_inh l_inherited = L.map (\<lambda> ToyClass _ l _ \<Rightarrow> l) (of_inh (map_inh of_linh l_inherited))"

end
