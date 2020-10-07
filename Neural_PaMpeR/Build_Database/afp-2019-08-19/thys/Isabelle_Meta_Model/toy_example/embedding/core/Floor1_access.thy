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

section\<open>Main Translation for: Accessor\<close>

theory  Floor1_access
imports Core_init
begin

definition "print_access_oid_uniq_gen Thy_def D_toy_oid_start_upd def_rewrite =
  (\<lambda>expr env.
      (\<lambda>(l, oid_start). (L.map Thy_def l, D_toy_oid_start_upd env oid_start))
      (let (l, (acc, _)) = fold_class (\<lambda>isub_name name l_attr l_inh _ _ cpt.
         let l_inh = L.map (\<lambda> ToyClass _ l _ \<Rightarrow> l) (of_inh l_inh) in
         let (l, cpt) = L.mapM (L.mapM
           (\<lambda> (attr, ToyTy_object (ToyTyObj (ToyTyCore ty_obj) _)) \<Rightarrow>
                                            (let obj_oid = TyObj_ass_id ty_obj
                                               ; obj_name_from_nat = TyObjN_ass_switch (TyObj_from ty_obj) in \<lambda>(cpt, rbt) \<Rightarrow>
             let (cpt_obj, cpt_rbt) =
               case RBT.lookup rbt obj_oid of
                 None \<Rightarrow> (cpt, oidSucAssoc cpt, RBT.insert obj_oid cpt rbt)
               | Some cpt_obj \<Rightarrow> (cpt_obj, cpt, rbt) in
             ( [def_rewrite obj_name_from_nat name isub_name attr (oidGetAssoc cpt_obj)]
             , cpt_rbt))
            | _ \<Rightarrow> \<lambda>cpt. ([], cpt)))
           (l_attr # l_inh) cpt in
         (L.flatten (L.flatten l), cpt)) (D_toy_oid_start env, RBT.empty) expr in
       (L.flatten l, acc)))"
definition "print_access_oid_uniq =
  print_access_oid_uniq_gen
    O.definition
    (\<lambda>env oid_start. env \<lparr> D_toy_oid_start := oid_start \<rparr>)
    (\<lambda>obj_name_from_nat _ isub_name attr cpt_obj.
      Definition (Term_rewrite
                   (Term_basic [print_access_oid_uniq_name obj_name_from_nat isub_name attr])
                   \<open>=\<close>
                   (Term_oid \<open>\<close> cpt_obj)))"

definition "print_access_choose_switch
              lets mk_var expr
              print_access_choose_n
              sexpr_list sexpr_function sexpr_pair =
  L.flatten
       (L.map
          (\<lambda>n.
           let l = L.upto 0 (n - 1) in
           L.map (let l = sexpr_list (L.map mk_var l) in (\<lambda>(i,j).
             (lets
                (print_access_choose_n n i j)
                (sexpr_function [(l, (sexpr_pair (mk_var i) (mk_var j)))]))))
             ((L.flatten o L.flatten) (L.map (\<lambda>i. L.map (\<lambda>j. if i = j then [] else [(i, j)]) l) l)))
          (class_arity expr))"
definition "print_access_choose = start_map'''' O.definition o (\<lambda>expr _.
  (let a = \<lambda>f x. Term_app f [x]
     ; b = \<lambda>s. Term_basic [s]
     ; lets = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> exp)
     ; lets' = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> (b exp))
     ; lets'' = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> (Term_lam \<open>l\<close> (\<lambda>var_l. Term_binop (b var_l) \<open>!\<close> (b exp))))
     ; _\<comment> \<open>(ignored)\<close> =
        let l_flatten = \<open>L.flatten\<close> in
        [ lets l_flatten (let fun_foldl = \<lambda>f base.
                             Term_lam \<open>l\<close> (\<lambda>var_l. Term_app \<open>foldl\<close> [Term_lam \<open>acc\<close> f, base, a \<open>rev\<close> (b var_l)]) in
                           fun_foldl (\<lambda>var_acc.
                             fun_foldl (\<lambda>var_acc.
                               Term_lam \<open>l\<close> (\<lambda>var_l. Term_app \<open>Cons\<close> (L.map b [var_l, var_acc]))) (b var_acc)) (b \<open>Nil\<close>))
        , lets var_map_of_list (Term_app \<open>foldl\<close>
            [ Term_lam \<open>map\<close> (\<lambda>var_map.
                let var_x = \<open>x\<close>
                  ; var_l0 = \<open>l0\<close>
                  ; var_l1 = \<open>l1\<close>
                  ; f_map = a var_map in
                Term_lambdas0 (Term_pair (b var_x) (b var_l1))
                  (Term_case (f_map (b var_x))
                    (L.map (\<lambda>(pat, e). (pat, f_map (Term_binop (b var_x) \<open>\<mapsto>\<close> e)))
                      [ (b \<open>None\<close>, b var_l1)
                      , (Term_some (b var_l0), a l_flatten (Term_list (L.map b [var_l0, var_l1])))])))
            , b \<open>Map.empty\<close>])] in
  L.flatten
  [ let a = \<lambda>f x. Term_app f [x]
      ; b = \<lambda>s. Term_basic [s]
      ; lets = \<lambda>var exp. Definition (Term_rewrite (Term_basic [var]) \<open>=\<close> exp)
      ; mk_var = \<lambda>i. b (S.flatten [\<open>x\<close>, String.natural_to_digit10 i]) in
    print_access_choose_switch
      lets mk_var expr
      print_access_choose_name
      Term_list Term_function Term_pair
  , []] ))"

end
