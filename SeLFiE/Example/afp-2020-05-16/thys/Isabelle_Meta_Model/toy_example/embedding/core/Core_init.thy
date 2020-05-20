(******************************************************************************
 * Citadelle
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

chapter\<open>Translating Meta-Models\<close>
section\<open>General Environment for the Translation: Introduction\<close>

theory  Core_init
imports "../../Toy_Library_Static"
        "../meta_toy/Meta_META"
begin

text\<open>This file regroups common utilities used by the embedding functions of Toy in Isabelle.\<close>

datatype opt_attr_type = OptInh | OptOwn
datatype opt_ident = OptIdent nat

instantiation internal_oid :: linorder
begin
 definition "n_of_internal_oid = (\<lambda> Oid n \<Rightarrow> n)"
 definition "n \<le> m \<longleftrightarrow> n_of_internal_oid n \<le> n_of_internal_oid m"
 definition "n < m \<longleftrightarrow> n_of_internal_oid n < n_of_internal_oid m"
 instance
   apply standard
   apply (metis less_eq_internal_oid_def less_imp_le less_internal_oid_def not_less)
   apply (metis less_eq_internal_oid_def order_refl)
   apply (metis less_eq_internal_oid_def order.trans)
   apply (simp add: less_eq_internal_oid_def n_of_internal_oid_def, case_tac x, case_tac y, simp)
   apply (metis le_cases less_eq_internal_oid_def)
   done
end



definition "var_oid_uniq = \<open>oid\<close>"
definition "var_deref_assocs_list = \<open>deref_assocs_list\<close>"
definition "var_inst_assoc = \<open>inst_assoc\<close>"
definition "var_choose = \<open>choose\<close>"
definition "var_switch = \<open>switch\<close>"
definition "var_assocs = \<open>assocs\<close>"
definition "var_map_of_list = \<open>map_of_list\<close>"
definition "var_self = \<open>self\<close>"
definition "var_result = \<open>result\<close>"


definition "find_class_ass env =
 (let (l_class, l_all_meta) =
    partition (let f = \<lambda>class. ClassRaw_clause class = [] in
               \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
               | META_association _ \<Rightarrow> True
               | META_ass_class Floor1 (ToyAssClass _ class) \<Rightarrow> f class
               | META_class_synonym _ \<Rightarrow> True
               | _ \<Rightarrow> False) (rev (D_input_meta env)) in
  ( L.flatten [l_class, List.map_filter (let f = \<lambda>class. class \<lparr> ClassRaw_clause := [] \<rparr> in
                                       \<lambda> META_class_raw Floor1 c \<Rightarrow> Some (META_class_raw Floor1 (f c))
                                       | META_ass_class Floor1 (ToyAssClass ass class) \<Rightarrow> Some (META_ass_class Floor1 (ToyAssClass ass (f class)))
                                       | _ \<Rightarrow> None) l_all_meta]
  , L.flatten (L.map
      (let f = \<lambda>class. [ META_ctxt Floor1 (toy_ctxt_ext [] (ClassRaw_name class) (ClassRaw_clause class) ()) ] in
       \<lambda> META_class_raw Floor1 class \<Rightarrow> f class
       | META_ass_class Floor1 (ToyAssClass _ class) \<Rightarrow> f class
       | x \<Rightarrow> [x]) l_all_meta)))"

definition "map_enum_syn l_enum l_syn =
 (\<lambda> ToyTy_object (ToyTyObj (ToyTyCore_pre s) []) \<Rightarrow> 
      if list_ex (\<lambda>syn. s \<triangleq> (case syn of ToyClassSynonym n _ \<Rightarrow> n)) l_syn then
        ToyTy_class_syn s
      else if list_ex (\<lambda>enum. s \<triangleq> (case enum of ToyEnum n _ \<Rightarrow> n)) l_enum then
        ToyTy_enum s
      else
        ToyTy_object (ToyTyObj (ToyTyCore_pre s) [])
  | x \<Rightarrow> x)"

definition "arrange_ass with_aggreg with_optim_ass l_c l_enum =
   (let l_syn = List.map_filter (\<lambda> META_class_synonym e \<Rightarrow> Some e
                                 | _ \<Rightarrow> None) l_c
      ; l_class = List.map_filter (\<lambda> META_class_raw Floor1 cflat \<Rightarrow> Some cflat
                                   | META_ass_class Floor1 (ToyAssClass _ cflat) \<Rightarrow> Some cflat
                                   | _ \<Rightarrow> None) l_c
      ; l_class = \<comment> \<open>map classes: change the (enumeration) type of every attributes to \<open>raw\<close>\<close>
                  \<comment> \<open>instead of the default \<open>object\<close> type\<close>
        L.map
          (\<lambda> cflat \<Rightarrow>
            cflat \<lparr> ClassRaw_own :=
                      L.map (map_prod id (map_enum_syn l_enum l_syn))
                               (ClassRaw_own cflat) \<rparr>) l_class
    ; l_ass = List.map_filter (\<lambda> META_association ass \<Rightarrow> Some ass
                                 | META_ass_class Floor1 (ToyAssClass ass _) \<Rightarrow> Some ass
                                 | _ \<Rightarrow> None) l_c
      ; ToyMult = \<lambda>l set. toy_multiplicity_ext l None set ()
      ; (l_class, l_ass0) = 
          if with_optim_ass then
            \<comment> \<open>move from classes to associations:\<close>
            \<comment> \<open>attributes of object types\<close>
            \<comment> \<open>+ those constructed with at most 1 recursive call to \<open>ToyTy_collection\<close>\<close>
            map_prod rev rev (List.fold
                  (\<lambda>c (l_class, l_ass).
                    let default = [Set]
                      ; f = \<lambda>role t mult_out. \<lparr> ToyAss_type = ToyAssTy_native_attribute
                                              , ToyAss_relation = ToyAssRel [(ClassRaw_name c, ToyMult [(Mult_star, None)] default)
                                                                            ,(t, mult_out \<lparr> TyRole := Some role \<rparr>)] \<rparr>
                      ; (l_own, l_ass) =
                        List.fold (\<lambda> (role, ToyTy_object t) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t (ToyMult [(Mult_nat 0, Some (Mult_nat 1))] default) # l)
                                   | (role, ToyTy_collection mult (ToyTy_object t)) \<Rightarrow>
                                          \<lambda> (l_own, l). (l_own, f role t mult # l)
                                   | x \<Rightarrow> \<lambda> (l_own, l). (x # l_own, l))
                                  (ClassRaw_own c)
                                  ([], l_ass) in
                    (c \<lparr> ClassRaw_own := rev l_own \<rparr> # l_class, l_ass))
                  l_class
                  ([], []))
          else
            (l_class, [])
      ; (l_class, l_ass) =
          if with_aggreg then
            \<comment> \<open>move from associations to classes:\<close>
            \<comment> \<open>attributes of aggregation form\<close>
            map_prod rev rev (List.fold
            (\<lambda>ass (l_class, l_ass).
              if ToyAss_type ass = ToyAssTy_aggregation then
                ( fold_max
                    (\<lambda> (cpt_to, (name_to, category_to)).
                      case TyRole category_to of
                        Some role_to \<Rightarrow>
                        List.fold (\<lambda> (cpt_from, (name_from, multip_from)).
                          L.map_find (\<lambda>cflat.
                            if cl_name_to_string cflat \<triangleq> ty_obj_to_string name_from then
                              Some (cflat \<lparr> ClassRaw_own :=
                                              L.flatten [ ClassRaw_own cflat
                                                           , [(role_to, let ty = ToyTy_object name_to in
                                                                        if single_multip category_to then 
                                                                          ty
                                                                        else
                                                                          ToyTy_collection category_to ty)]] \<rparr>)
                            else None))
                     | _ \<Rightarrow> \<lambda>_. id)
                    (ToyAss_relation' ass)
                    l_class
                , l_ass)
              else
                (l_class, ass # l_ass)) l_ass (l_class, []))
          else
            (l_class, l_ass) in
    ( l_class
    , L.flatten [l_ass, l_ass0]))"

definition "datatype_name = \<open>ty\<close>"
definition "datatype_ext_name = datatype_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype_constr_name = \<open>mk\<close>"
definition "datatype_ext_constr_name = datatype_constr_name @@ \<open>\<E>\<X>\<T>\<close>"
definition "datatype_in = \<open>in\<close>"

subsection\<open>Main Combinators for the Translation\<close>

text\<open>
As general remark, all the future translating steps 
(e.g., that will occur in @{file \<open>Floor1_access.thy\<close>})
will extensively use Isabelle expressions,
represented by its Meta-Model, for example lots of functions will use @{term "Term_app"}...
So the overall can be simplified by the use of polymorphic cartouches.
It looks feasible to add a new front-end for cartouches in @{theory Isabelle_Meta_Model.Init}
supporting the use of Isabelle syntax in cartouches,
then we could obtain at the end a parsed Isabelle Meta-Model in Isabelle.\<close>

definition "start_map f = L.mapM (\<lambda>x acc. (f x, acc))"
definition "start_map''' f fl = (\<lambda> env.
  let design_analysis = D_toy_semantics env
    ; base_attr = (if design_analysis = Gen_only_design then id else L.filter (\<lambda> (_, ToyTy_object (ToyTyObj (ToyTyCore _) _)) \<Rightarrow> False | _ \<Rightarrow> True))
    ; base_attr' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, L.map base_attr l_inh))
    ; base_attr'' = (\<lambda> (l_attr, l_inh). (base_attr l_attr, base_attr l_inh)) in
  start_map f (fl design_analysis base_attr base_attr' base_attr'') env)"
definition "start_map'' f fl e = start_map''' f (\<lambda>_. fl) e"
definition "start_map'''' f fl = (\<lambda> env. start_map f (fl (D_toy_semantics env)) env)"

definition "bootstrap_floor f_x l env =
 (let (l, env) = f_x l env
    ; l_setup = META_boot_setup_env (Boot_setup_env (env \<lparr> D_output_disable_thy := True
                                                        , D_output_header_thy := None
                                                        , D_output_position := (0, 0) \<rparr>) )
                # l
    ; l = if case D_input_meta env of [] \<Rightarrow> True | x # _ \<Rightarrow> ignore_meta_header x then
            l
          else
            l_setup in
  ( if D_output_auto_bootstrap env then
      l
    else
      META_boot_generation_syntax (Boot_generation_syntax (D_toy_semantics env))
      # l_setup
  , env \<lparr> D_output_auto_bootstrap := True \<rparr> ))"

definition "wrap_toyty x = \<open>\<cdot>\<close> @@ x"
definition "Term_annot_toy e s = Term_annot' e (wrap_toyty s)"
definition "Term_toyset l = (case l of [] \<Rightarrow> Term_basic [\<open>Set{}\<close>] | _ \<Rightarrow> Term_paren \<open>Set{\<close> \<open>}\<close> (term_binop \<open>,\<close> l))"
definition "Term_oid s = (\<lambda>Oid n \<Rightarrow> Term_basic [s @@ String.natural_to_digit10 n])"

subsection\<open>Preliminaries on: Enumeration\<close>

subsection\<open>Preliminaries on: Infrastructure\<close>

subsection\<open>Preliminaries on: Accessor\<close>

definition "print_access_oid_uniq_name' name_from_nat isub_name attr = S.flatten [ isub_name var_oid_uniq, \<open>_\<close>, String.natural_to_digit10 name_from_nat, \<open>_\<close>, attr ]"
definition "print_access_oid_uniq_name name_from_nat isub_name attr = print_access_oid_uniq_name' name_from_nat isub_name (String.isup attr)"

definition "print_access_choose_name n i j =
  S.flatten [var_switch, String.isub (String.natural_to_digit10 n), \<open>_\<close>, String.natural_to_digit10 i, String.natural_to_digit10 j]"

subsection\<open>Preliminaries on: Example (Floor 1)\<close>

datatype reporting = Warning
                   | Error
                   | Writeln

subsection\<open>Preliminaries on: Example (Floor 2)\<close>

subsection\<open>Preliminaries on: Context\<close>

definition "make_ctxt_free_var pref ctxt =
 (var_self # L.flatten [ L.map fst (Ctxt_fun_ty_arg ctxt)
                          , if pref = ToyCtxtPre then [] else [var_result] ])"

end
