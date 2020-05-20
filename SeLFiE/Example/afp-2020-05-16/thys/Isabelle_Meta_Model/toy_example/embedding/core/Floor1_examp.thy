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

section\<open>Main Translation for: Example (Floor 1)\<close>

theory  Floor1_examp
imports Core_init
begin

definition "list_bind f0 f l =
 (let l = L.map f0 l in
  if list_ex (\<lambda> None \<Rightarrow> True | _ \<Rightarrow> False) l then
    None
  else
    Some (f (List.map_filter id l)))"

definition "rbt_of_class env =
  (let rbt = (snd o fold_class_gen (\<lambda>_ name l_attr l_inh _ _ rbt.
     ( [()]
     , modify_def (RBT.empty, []) name
         (let f_fold = \<lambda>tag l rbt.
            let (rbt, _, n) = List.fold
                                   (\<lambda> (name_attr, ty) \<Rightarrow> \<lambda>(rbt, cpt, l_obj).
                                     (insert name_attr (ty, tag, OptIdent cpt) rbt, Succ cpt, (case ty of ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _) \<Rightarrow> Some ty_obj | _ \<Rightarrow> None) # l_obj))
                                   l
                                   (rbt, 0, []) in
            (rbt, (tag, n)) in
          (\<lambda>(rbt, _).
           let (rbt, info_own) = f_fold OptOwn l_attr rbt in
           let (rbt, info_inh) = f_fold OptInh (L.flatten (map_class_inh l_inh)) rbt in
           (rbt, [info_own, info_inh])))
         rbt)) RBT.empty) (case D_input_class env of Some c \<Rightarrow> c) in
   (\<lambda>name.
     let rbt = lookup rbt name in
     ( rbt = None
     , \<lambda> name_attr.
        Option.bind rbt (\<lambda>(rbt, _). lookup rbt name_attr)
     , \<lambda> v. Option.bind rbt (\<lambda>(_, l).
        map_option (\<lambda>l f accu.
          let (_, accu) =
            List.fold
              (let f_fold = \<lambda>b (n, accu). (Succ n, f b n accu) in
               if D_toy_semantics env = Gen_only_design then
                 f_fold
               else
                 \<lambda> Some _ \<Rightarrow> (\<lambda>(n, accu). (Succ n, accu))
                 | None \<Rightarrow> f_fold None) (rev l) (0, accu) in
          accu) (L.assoc v l)))))"

definition "inst_name toyi = (case Inst_name toyi of Some n \<Rightarrow> n)"

definition "init_map_class env l =
  (let (rbt_nat, rbt_str, _, _) =
     List.fold
       (\<lambda> toyi (rbt_nat, rbt_str, oid_start, accu).
         ( RBT.insert (Oid accu) oid_start rbt_nat
         , insert (inst_name toyi) oid_start rbt_str
         , oidSucInh oid_start
         , Succ accu))
       l
       ( RBT.empty
       , RBT.bulkload (L.map (\<lambda>(k, _, v). (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_list k, v)) (D_input_instance env))
       , D_toy_oid_start env
       , 0) in
   (rbt_of_class env, RBT.lookup rbt_nat, lookup rbt_str))"

definition "print_examp_def_st_assoc_build_rbt_gen f rbt map_self map_username l_assoc =
  List.fold
     (\<lambda> (toyi, cpt). fold_instance_single
       (\<lambda> ty l_attr.
         let (f_attr_ty, _) = rbt ty in
         f ty
         (List.fold (\<lambda>(_, name_attr, shall).
           case f_attr_ty name_attr of
             Some (ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _), _, _) \<Rightarrow>
               modify_def ([], ty_obj) name_attr
               (\<lambda>(l, accu). case let find_map = \<lambda> ShallB_str s \<Rightarrow> map_username s | ShallB_self s \<Rightarrow> map_self s | _ \<Rightarrow> None in
                                 case shall of
                                   ShallB_list l \<Rightarrow> if list_ex (\<lambda>x. find_map x = None) l then
                                                      None
                                                    else
                                                      Some (List.map_filter find_map l)
                                 | _ \<Rightarrow> map_option (\<lambda>x. [x]) (find_map shall) of
                      None \<Rightarrow> (l, accu)
                    | Some oid \<Rightarrow> (L.map (L.map oidGetInh) [[cpt], oid] # l, accu))
           | _ \<Rightarrow> id) l_attr)) toyi) l_assoc RBT.empty"

definition "print_examp_def_st_assoc_build_rbt = print_examp_def_st_assoc_build_rbt_gen (modify_def RBT.empty)"

definition "print_examp_def_st_assoc rbt map_self map_username l_assoc =
  (let b = \<lambda>s. Term_basic [s]
     ; rbt = print_examp_def_st_assoc_build_rbt rbt map_self map_username l_assoc in
   Term_app var_map_of_list [Term_list (fold (\<lambda>name. fold (\<lambda>name_attr (l_attr, ty_obj) l_cons.
         let cpt_from = TyObjN_ass_switch (TyObj_from ty_obj) in
         Term_pair
           (Term_basic [print_access_oid_uniq_name cpt_from (\<lambda>s. s @@ String.isub name) name_attr])
           (Term_app \<open>List.map\<close>
             [ Term_binop (let var_x = \<open>x\<close>
                             ; var_y = \<open>y\<close> in
                           Term_lambdas0
                             (Term_pair (b var_x) (b var_y))
                             (Term_list [b var_x, b var_y]))
                          \<open>o\<close>
                          (b (print_access_choose_name
                                (TyObj_ass_arity ty_obj)
                                cpt_from
                                (TyObjN_ass_switch (TyObj_to ty_obj))))
             , Term_list' (Term_list' (Term_list' (Term_oid var_oid_uniq))) l_attr ])
         # l_cons)) rbt [])])"

definition "print_examp_instance_oid thy_definition_hol l env = (L.map thy_definition_hol o L.flatten)
 (let (f1, f2) = (\<lambda> var_oid _ _. var_oid, \<lambda> _ _ cpt. Term_oid \<open>\<close> (oidGetInh cpt)) in
  L.map (\<lambda> (toyi, cpt).
    if List.fold (\<lambda>(_, _, cpt0) b. b | oidGetInh cpt0 = oidGetInh cpt) (D_input_instance env) False then
      []
    else
      let var_oid = Term_oid var_oid_uniq (oidGetInh cpt)
        ; isub_name = \<lambda>s. s @@ String.isub (inst_ty toyi) in
      [Definition (Term_rewrite (f1 var_oid isub_name toyi) \<open>=\<close> (f2 toyi isub_name cpt))]) l)"

definition "check_export_code f_writeln f_warning f_error f_raise l_report msg_last =
 (let l_err =
        List.fold
          (\<lambda> (Writeln, s) \<Rightarrow> \<lambda>acc. case f_writeln s of () \<Rightarrow> acc
           | (Warning, s) \<Rightarrow> \<lambda>acc. case f_warning s of () \<Rightarrow> acc
           | (Error, s) \<Rightarrow> \<lambda>acc. case f_error s of () \<Rightarrow> s # acc)
          l_report
          [] in
  if l_err = [] then
    ()
  else
    f_raise (String.nat_to_digit10 (length l_err) @@ msg_last))"

definition "print_examp_instance_defassoc_gen name l_toyi env =
 (case D_toy_semantics env of Gen_only_analysis \<Rightarrow> [] | Gen_default \<Rightarrow> [] | Gen_only_design \<Rightarrow>
  let a = \<lambda>f x. Term_app f [x]
    ; b = \<lambda>s. Term_basic [s]
    ; (rbt :: _ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> natural \<Rightarrow> _ \<Rightarrow> (toy_ty \<times> toy_data_shallow) option list) \<Rightarrow> _ \<Rightarrow> _) option)
      , (map_self, map_username)) =
        init_map_class env (fst (L.split l_toyi))
    ; l_toyi = if list_ex (\<lambda>(toyi, _). inst_ty0 toyi = None) l_toyi then [] else l_toyi in
  [Definition
     (Term_rewrite name
     \<open>=\<close>
     (let var_oid_class = \<open>oid_class\<close>
        ; var_to_from = \<open>to_from\<close>
        ; var_oid = \<open>oid\<close>
        ; a_l = \<lambda>s. Typ_apply (Typ_base var_ty_list) [s] in
      Term_lambdas
        [var_oid_class, var_to_from, var_oid]
        (Term_annot (Term_case
          (Term_app var_deref_assocs_list
            [ Term_annot (b var_to_from) (Ty_arrow
                                            (a_l (a_l (Typ_base const_oid)))
                                            (let t = a_l (Typ_base const_oid) in
                                             Ty_times t t))
            , Term_annot' (b var_oid) const_oid
            , a \<open>drop\<close>
              (Term_applys (print_examp_def_st_assoc (snd o rbt) map_self map_username l_toyi)
                           [Term_annot' (b var_oid_class) const_oid])])
          [ (b \<open>Nil\<close>, b \<open>None\<close>)
          , let b_l = b \<open>l\<close> in
            (b_l, a \<open>Some\<close> b_l)] ) (Typ_apply (Typ_base \<open>option\<close>) [a_l (Typ_base const_oid)]))))])"

definition "print_examp_instance_defassoc = (\<lambda> ToyInstance l \<Rightarrow> \<lambda> env.
  let l = L.flatten (fst (L.mapM (\<lambda>toyi cpt. ([(toyi, cpt)], oidSucInh cpt)) l (D_toy_oid_start env))) in
  (\<lambda>l_res.
    ( print_examp_instance_oid O.definition l env
      @@@@ L.map O.definition l_res
    , env))
  (print_examp_instance_defassoc_gen
    (Term_oid var_inst_assoc (oidGetInh (D_toy_oid_start env)))
    l
    env))"

definition "print_examp_instance_name = id"
definition "print_examp_instance = (\<lambda> ToyInstance l \<Rightarrow> \<lambda> env.
 (\<lambda> ((l_res, oid_start), instance_rbt).
    ((L.map O.definition o L.flatten) l_res, env \<lparr> D_toy_oid_start := oid_start, D_input_instance := instance_rbt \<rparr>))
  (let ( rbt :: _ \<Rightarrow> _ \<times> _ \<times> (_ \<Rightarrow> ((_ \<Rightarrow> nat \<Rightarrow> _ \<Rightarrow> _) \<Rightarrow> _ \<Rightarrow>
                (toy_ty_class option \<times>
                  (toy_ty \<times> (string \<times> string) option \<times> toy_data_shallow) option) list) option)
       , (map_self, map_username)) = init_map_class env l
     ; a = \<lambda>f x. Term_app f [x]
     ; b = \<lambda>s. Term_basic [s] in
   ( let var_inst_ass = \<open>inst_assoc\<close> in
     L.mapM
       (\<lambda> toyi cpt.
         ( []
         , oidSucInh cpt))
       l
       (D_toy_oid_start env)
   , List.fold (\<lambda>toyi instance_rbt.
       let n = inst_name toyi in
       (String.to_String\<^sub>b\<^sub>a\<^sub>s\<^sub>e n, toyi, case map_username n of Some oid \<Rightarrow> oid) # instance_rbt) l (D_input_instance env))))"

definition "print_examp_def_st1 = (\<lambda> ToyDefSt name l \<Rightarrow> bootstrap_floor
  (\<lambda>l env. (L.flatten [l], env))
  (L.map META_all_meta_embedding
     (let (l, _) = List.fold (\<lambda> (pos, core) (l, n).
                                          ((pos, pos - n, core) # l, 
                                            case core of ToyDefCoreAdd _ \<Rightarrow> n
                                            | ToyDefCoreBinding _ \<Rightarrow> Succ n))
                                 (L.mapi Pair l)
                                 ([], 0)
        ; (l_inst, l_defst) =
        List.fold (\<lambda> (pos, _, ToyDefCoreAdd toyi) \<Rightarrow> \<lambda>(l_inst, l_defst).
                     let i_name = case Inst_name toyi of Some x \<Rightarrow> x | None \<Rightarrow> S.flatten [name, \<open>_object\<close>, String.natural_to_digit10 pos] in
                       ( map_instance_single (map_prod id (map_prod id (map_data_shallow_self (\<lambda>Oid self \<Rightarrow>
                           (case L.assoc self l of
                              Some (_, ToyDefCoreBinding name) \<Rightarrow> ShallB_str name
                            | Some (p, _) \<Rightarrow> ShallB_self (Oid p)
                            | _ \<Rightarrow> ShallB_list []))))) toyi 
                         \<lparr> Inst_name := Some i_name \<rparr>
                       # l_inst
                       , ToyDefCoreBinding i_name # l_defst)
                   | (_, _, ToyDefCoreBinding name) \<Rightarrow> \<lambda>(l_inst, l_defst).
                       ( l_inst
                       , ToyDefCoreBinding name # l_defst))
                  l
                  ([], []) 
        ; l = [ META_def_state Floor2 (ToyDefSt name l_defst) ] in
      if l_inst = [] then
        l
      else
        META_instance (ToyInstance l_inst) # l)))"

definition "print_pre_post = (\<lambda> ToyDefPP name s_pre s_post \<Rightarrow> bootstrap_floor
  (\<lambda>f env. (L.flatten [f env], env))
  (\<lambda>env.
    let pref_name = case name of Some n \<Rightarrow> n
                               | None \<Rightarrow> \<open>WFF_\<close> @@ String.nat_to_digit10 (length (D_input_meta env))
      ; f_comp = \<lambda>None \<Rightarrow> id | Some (_, f) \<Rightarrow> f
      ; f_conv = \<lambda>msg.
          \<lambda> ToyDefPPCoreAdd toy_def_state \<Rightarrow>
              let n = pref_name @@ msg in
              (ToyDefPPCoreBinding n, Cons (META_def_state Floor1 (ToyDefSt n toy_def_state)))
          | s \<Rightarrow> (s, id) in
    L.map
      META_all_meta_embedding
      (let o_pre = Some (f_conv \<open>_pre\<close> s_pre)
         ; o_post = map_option (f_conv \<open>_post\<close>) s_post in
       (f_comp o_pre o f_comp o_post)
         [ META_def_pre_post Floor2 (ToyDefPP name
                                             (case o_pre of Some (n, _) \<Rightarrow> n)
                                             (map_option fst o_post)) ])))"

end
