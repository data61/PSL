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

section\<open>Main Translation for: Infrastructure\<close>

theory  Floor1_infra
imports Core_init
begin

definition "print_infra_datatype_class = start_map'' O.datatype o (\<lambda>expr _ base_attr' _. map_class_gen_h''''
  (\<lambda>isub_name name _ l_attr l_inherited l_cons.
    let (l_attr, l_inherited) = base_attr' (l_attr, of_inh l_inherited)
      ; map_ty = L.map ((\<lambda>x. Typ_apply (Typ_base \<open>option\<close>) [str_hol_of_ty_all Typ_apply Typ_base x]) o snd) in
    [ Datatype
        (isub_name datatype_ext_name)
        (  (L.rev_map (\<lambda>x. ( datatype_ext_constr_name @@ mk_constr_name name x
                         , [Raw (datatype_name @@ String.isub x)])) (of_sub l_cons))
        @@@@ [(isub_name datatype_ext_constr_name, Raw const_oid # L.maps map_ty l_inherited)])
    , Datatype
        (isub_name datatype_name)
        [ (isub_name datatype_constr_name, Raw (isub_name datatype_ext_name) # map_ty l_attr ) ] ]) expr)"

definition "print_infra_datatype_universe expr = start_map O.datatype
  [ Datatype \<open>\<AA>\<close>
      (map_class (\<lambda>isub_name _ _ _ _ _. (isub_name datatype_in, [Raw (isub_name datatype_name)])) expr) ]"

definition "print_infra_type_synonym_class_higher expr = start_map O.type_synonym
 (let option = Typ_apply_paren \<open>\<langle>\<close> \<open>\<rangle>\<^sub>\<bottom>\<close> in
  L.flatten
    (map_class
      (\<lambda>isub_name name _ _ _ _.
        [ Type_synonym' name
                       (option (option (Typ_base (isub_name datatype_name))))
        \<^cancel>\<open>, Type_synonym' name (Typ_apply_paren \<open>\<cdot>\<close> \<open>\<close> (Typ_base (name @@ \<open>'\<close>)))\<close>])
      expr))"

end
