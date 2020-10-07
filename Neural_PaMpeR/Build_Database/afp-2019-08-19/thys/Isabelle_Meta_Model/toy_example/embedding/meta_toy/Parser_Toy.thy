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

section\<open>Instantiating the Parser of Toy (I)\<close>

theory  Parser_Toy
imports Meta_Toy
        "../../../meta_isabelle/Parser_Pure"
begin

subsection\<open>Building Recursors for Records\<close> (* NOTE part to be automated *)

definition "toy_multiplicity_rec0 f toy = f
  (TyMult toy)
  (TyRole toy)
  (TyCollect toy)"

definition "toy_multiplicity_rec f toy = toy_multiplicity_rec0 f toy
  (toy_multiplicity.more toy)"

definition "toy_ty_class_node_rec0 f toy = f
  (TyObjN_ass_switch toy)
  (TyObjN_role_multip toy)
  (TyObjN_role_ty toy)"

definition "toy_ty_class_node_rec f toy = toy_ty_class_node_rec0 f toy
  (toy_ty_class_node.more toy)"

definition "toy_ty_class_rec0 f toy = f
  (TyObj_name toy)
  (TyObj_ass_id toy)
  (TyObj_ass_arity toy)
  (TyObj_from toy)
  (TyObj_to toy)"

definition "toy_ty_class_rec f toy = toy_ty_class_rec0 f toy
  (toy_ty_class.more toy)"

definition "toy_class_raw_rec0 f toy = f
  (ClassRaw_name toy)
  (ClassRaw_own toy)
  (ClassRaw_clause toy)
  (ClassRaw_abstract toy)"

definition "toy_class_raw_rec f toy = toy_class_raw_rec0 f toy
  (toy_class_raw.more toy)"

definition "toy_association_rec0 f toy = f
  (ToyAss_type toy)
  (ToyAss_relation toy)"

definition "toy_association_rec f toy = toy_association_rec0 f toy
  (toy_association.more toy)"

definition "toy_ctxt_pre_post_rec0 f toy = f
  (Ctxt_fun_name toy)
  (Ctxt_fun_ty toy)
  (Ctxt_expr toy)"

definition "toy_ctxt_pre_post_rec f toy = toy_ctxt_pre_post_rec0 f toy
  (toy_ctxt_pre_post.more toy)"

definition "toy_ctxt_rec0 f toy = f
  (Ctxt_param toy)
  (Ctxt_ty toy)
  (Ctxt_clause toy)"

definition "toy_ctxt_rec f toy = toy_ctxt_rec0 f toy
  (toy_ctxt.more toy)"

(* *)

lemma [code]: "toy_class_raw.extend = (\<lambda>toy v. toy_class_raw_rec0 (co4 (\<lambda>f. f v) toy_class_raw_ext) toy)"
by(intro ext, simp add: toy_class_raw_rec0_def
                        toy_class_raw.extend_def
                        co4_def K_def)
lemma [code]: "toy_class_raw.make = co4 (\<lambda>f. f ()) toy_class_raw_ext"
by(intro ext, simp add: toy_class_raw.make_def
                        co4_def)
lemma [code]: "toy_class_raw.truncate = toy_class_raw_rec (co4 K toy_class_raw.make)"
by(intro ext, simp add: toy_class_raw_rec0_def
                        toy_class_raw_rec_def
                        toy_class_raw.truncate_def
                        toy_class_raw.make_def
                        co4_def K_def)

lemma [code]: "toy_association.extend = (\<lambda>toy v. toy_association_rec0 (co2 (\<lambda>f. f v) toy_association_ext) toy)"
by(intro ext, simp add: toy_association_rec0_def
                        toy_association.extend_def
                        co2_def K_def)
lemma [code]: "toy_association.make = co2 (\<lambda>f. f ()) toy_association_ext"
by(intro ext, simp add: toy_association.make_def
                        co2_def)
lemma [code]: "toy_association.truncate = toy_association_rec (co2 K toy_association.make)"
by(intro ext, simp add: toy_association_rec0_def
                        toy_association_rec_def
                        toy_association.truncate_def
                        toy_association.make_def
                        co2_def K_def)

subsection\<open>Main\<close>

context Parse
begin

definition "of_toy_collection b = rec_toy_collection
  (b \<open>Set\<close>)
  (b \<open>Sequence\<close>)
  (b \<open>Ordered0\<close>)
  (b \<open>Subsets0\<close>)
  (b \<open>Union0\<close>)
  (b \<open>Redefines0\<close>)
  (b \<open>Derived0\<close>)
  (b \<open>Qualifier0\<close>)
  (b \<open>Nonunique0\<close>)"

definition "of_toy_multiplicity_single a b = rec_toy_multiplicity_single
  (ap1 a (b \<open>Mult_nat\<close>) (of_nat a b))
  (b \<open>Mult_star\<close>)
  (b \<open>Mult_infinity\<close>)"

definition "of_toy_multiplicity a b f = toy_multiplicity_rec
  (ap4 a (b (ext \<open>toy_multiplicity_ext\<close>))
    (of_list a b (of_pair a b (of_toy_multiplicity_single a b) (of_option a b (of_toy_multiplicity_single a b))))
    (of_option a b (of_string a b))
    (of_list a b (of_toy_collection b))
    (f a b))"

definition "of_toy_ty_class_node a b f = toy_ty_class_node_rec
  (ap4 a (b (ext \<open>toy_ty_class_node_ext\<close>))
    (of_nat a b)
    (of_toy_multiplicity a b (K of_unit))
    (of_string a b)
    (f a b))"

definition "of_toy_ty_class a b f = toy_ty_class_rec
  (ap6 a (b (ext \<open>toy_ty_class_ext\<close>))
    (of_string a b)
    (of_nat a b)
    (of_nat a b)
    (of_toy_ty_class_node a b (K of_unit))
    (of_toy_ty_class_node a b (K of_unit))
    (f a b))"

definition "of_toy_ty_obj_core a b = rec_toy_ty_obj_core
  (ap1 a (b \<open>ToyTyCore_pre\<close>) (of_string a b))
  (ap1 a (b \<open>ToyTyCore\<close>) (of_toy_ty_class a b (K of_unit)))"

definition "of_toy_ty_obj a b = rec_toy_ty_obj
  (ap2 a (b \<open>ToyTyObj\<close>) (of_toy_ty_obj_core a b) (of_list a b (of_list a b (of_toy_ty_obj_core a b))))"

definition "of_toy_ty a b = (\<lambda>f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15.
                                    rec_toy_ty f1 f2 f3 f4 f5 f6
                                               f7 (K o f8) (\<lambda>_ _. f9) (f10 o map_prod id snd) (\<lambda>_ _. f11) f12 f13 f14 f15)
  (b \<open>ToyTy_base_void\<close>)
  (b \<open>ToyTy_base_boolean\<close>)
  (b \<open>ToyTy_base_integer\<close>)
  (b \<open>ToyTy_base_unlimitednatural\<close>)
  (b \<open>ToyTy_base_real\<close>)
  (b \<open>ToyTy_base_string\<close>)
  (ap1 a (b \<open>ToyTy_object\<close>) (of_toy_ty_obj a b))
  (ar2 a (b \<open>ToyTy_collection\<close>) (of_toy_multiplicity a b (K of_unit)))
  (ar2 a (b \<open>ToyTy_pair\<close>) id)
  (ap1 a (b \<open>ToyTy_binding\<close>) (of_pair a b (of_option a b (of_string a b)) id))
  (ar2 a (b \<open>ToyTy_arrow\<close>) id)
  (ap1 a (b \<open>ToyTy_class_syn\<close>) (of_string a b))
  (ap1 a (b \<open>ToyTy_enum\<close>) (of_string a b))
  (ap1 a (b \<open>ToyTy_raw\<close>) (of_string a b))"

definition "of_toy_association_type a b = rec_toy_association_type
  (b \<open>ToyAssTy_native_attribute\<close>)
  (b \<open>ToyAssTy_association\<close>)
  (b \<open>ToyAssTy_composition\<close>)
  (b \<open>ToyAssTy_aggregation\<close>)"

definition "of_toy_association_relation a b = rec_toy_association_relation
  (ap1 a (b \<open>ToyAssRel\<close>)
    (of_list a b (of_pair a b (of_toy_ty_obj a b) (of_toy_multiplicity a b (K of_unit)))))"

definition "of_toy_association a b f = toy_association_rec
  (ap3 a (b (ext \<open>toy_association_ext\<close>))
    (of_toy_association_type a b)
    (of_toy_association_relation a b)
    (f a b))"

definition "of_toy_ctxt_prefix a b = rec_toy_ctxt_prefix
  (b \<open>ToyCtxtPre\<close>)
  (b \<open>ToyCtxtPost\<close>)"

definition "of_toy_ctxt_term a b = (\<lambda>f0 f1 f2. rec_toy_ctxt_term f0 f1 (co1 K f2))
  (ap1 a (b \<open>T_pure\<close>) (of_pure_term a b))
  (ap2 a (b \<open>T_to_be_parsed\<close>) (of_string a b) (of_string a b))
  (ar2 a (b \<open>T_lambda\<close>) (of_string a b))"

definition "of_toy_prop a b = rec_toy_prop
  (ap2 a (b \<open>ToyProp_ctxt\<close>) (of_option a b (of_string a b)) (of_toy_ctxt_term a b))"

definition "of_toy_ctxt_term_inv a b = rec_toy_ctxt_term_inv
  (ap2 a (b \<open>T_inv\<close>) (of_bool b) (of_toy_prop a b))"

definition "of_toy_ctxt_term_pp a b = rec_toy_ctxt_term_pp
  (ap2 a (b \<open>T_pp\<close>) (of_toy_ctxt_prefix a b) (of_toy_prop a b))
  (ap1 a (b \<open>T_invariant\<close>) (of_toy_ctxt_term_inv a b))"

definition "of_toy_ctxt_pre_post a b f = toy_ctxt_pre_post_rec
  (ap4 a (b (ext \<open>toy_ctxt_pre_post_ext\<close>))
    (of_string a b)
    (of_toy_ty a b)
    (of_list a b (of_toy_ctxt_term_pp a b))
    (f a b))"

definition "of_toy_ctxt_clause a b = rec_toy_ctxt_clause
  (ap1 a (b \<open>Ctxt_pp\<close>) (of_toy_ctxt_pre_post a b (K of_unit)))
  (ap1 a (b \<open>Ctxt_inv\<close>) (of_toy_ctxt_term_inv a b))"

definition "of_toy_ctxt a b f = toy_ctxt_rec
  (ap4 a (b (ext \<open>toy_ctxt_ext\<close>))
    (of_list a b (of_string a b))
    (of_toy_ty_obj a b)
    (of_list a b (of_toy_ctxt_clause a b))
    (f a b))"

definition "of_toy_class a b = (\<lambda>f0 f1 f2 f3. rec_toy_class (ap3 a f0 f1 f2 f3))
  (b \<open>ToyClass\<close>)
    (of_string a b)
    (of_list a b (of_pair a b (of_string a b) (of_toy_ty a b)))
    (of_list a b snd)"

definition "of_toy_class_raw a b f = toy_class_raw_rec
  (ap5 a (b (ext \<open>toy_class_raw_ext\<close>))
    (of_toy_ty_obj a b)
    (of_list a b (of_pair a b (of_string a b) (of_toy_ty a b)))
    (of_list a b (of_toy_ctxt_clause a b))
    (of_bool b)
    (f a b))"

definition "of_toy_ass_class a b = rec_toy_ass_class
  (ap2 a (b \<open>ToyAssClass\<close>)
    (of_toy_association a b (K of_unit))
    (of_toy_class_raw a b (K of_unit)))"

definition "of_toy_class_synonym a b = rec_toy_class_synonym
  (ap2 a (b \<open>ToyClassSynonym\<close>)
    (of_string a b)
    (of_toy_ty a b))"

definition "of_toy_enum a b = rec_toy_enum
  (ap2 a (b \<open>ToyEnum\<close>)
    (of_string a b)
    (of_list a b (of_string a b)))"

end

lemmas [code] =
  Parse.of_toy_collection_def
  Parse.of_toy_multiplicity_single_def
  Parse.of_toy_multiplicity_def
  Parse.of_toy_ty_class_node_def
  Parse.of_toy_ty_class_def
  Parse.of_toy_ty_obj_core_def
  Parse.of_toy_ty_obj_def
  Parse.of_toy_ty_def
  Parse.of_toy_association_type_def
  Parse.of_toy_association_relation_def
  Parse.of_toy_association_def
  Parse.of_toy_ctxt_prefix_def
  Parse.of_toy_ctxt_term_def
  Parse.of_toy_prop_def
  Parse.of_toy_ctxt_term_inv_def
  Parse.of_toy_ctxt_term_pp_def
  Parse.of_toy_ctxt_pre_post_def
  Parse.of_toy_ctxt_clause_def
  Parse.of_toy_ctxt_def
  Parse.of_toy_class_def
  Parse.of_toy_class_raw_def
  Parse.of_toy_ass_class_def
  Parse.of_toy_class_synonym_def
  Parse.of_toy_enum_def

end
