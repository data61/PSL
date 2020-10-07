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

section\<open>Instantiating the Printer for Toy (II)\<close>

theory  Printer_Toy_extended
imports Meta_Toy_extended
        Printer_Toy
begin

context Print
begin

definition "To_oid = (\<lambda>Oid n \<Rightarrow> To_nat n)"

definition \<open>of_toy_def_base = (\<lambda> ToyDefInteger i \<Rightarrow> To_string i
                                | ToyDefReal (i1, i2) \<Rightarrow> \<open>%s.%s\<close> (To_string i1) (To_string i2)
                                | ToyDefString s \<Rightarrow> \<open>"%s"\<close> (To_string s))\<close>

fun of_toy_data_shallow where
   "of_toy_data_shallow e = (\<lambda> ShallB_term b \<Rightarrow> of_toy_def_base b
                             | ShallB_str s \<Rightarrow> To_string s
                             | ShallB_self s \<Rightarrow> \<open>self %d\<close> (To_oid s)
                             | ShallB_list l \<Rightarrow> \<open>[ %s ]\<close> (String_concat \<open>, \<close> (List.map of_toy_data_shallow l))) e"

fun of_toy_list_attr where
   "of_toy_list_attr f e = (\<lambda> ToyAttrNoCast x \<Rightarrow> f x
                            | ToyAttrCast ty (ToyAttrNoCast x) _ \<Rightarrow> \<open>(%s :: %s)\<close> (f x) (To_string ty)
                            | ToyAttrCast ty l _ \<Rightarrow> \<open>%s \<rightarrow> toyAsType( %s )\<close> (of_toy_list_attr f l) (To_string ty)) e"

definition \<open>of_toy_instance_single toyi =
 (let (s_left, s_right) =
    case Inst_name toyi of
      None \<Rightarrow> (case Inst_ty toyi of Some ty \<Rightarrow> (\<open>(\<close>, \<open> :: %s)\<close> (To_string ty)))
    | Some s \<Rightarrow>
        ( \<open>%s%s = \<close>
            (To_string s)
            (case Inst_ty toyi of None \<Rightarrow> \<open>\<close> | Some ty \<Rightarrow> \<open> :: %s\<close> (To_string ty))
        , \<open>\<close>) in
  \<open>%s%s%s\<close>
    s_left
    (of_toy_list_attr
      (\<lambda>l. \<open>[ %s ]\<close>
             (String_concat \<open>, \<close>
               (L.map (\<lambda>(pre_post, attr, v).
                            \<open>%s"%s" = %s\<close> (case pre_post of None \<Rightarrow> \<open>\<close>
                                                          | Some (s1, s2) \<Rightarrow> \<open>("%s", "%s") |= \<close> (To_string s1) (To_string s2))
                                          (To_string attr)
                                          (of_toy_data_shallow v))
                         l)))
      (Inst_attr toyi))
    s_right)\<close>

definition "of_toy_instance _ = (\<lambda> ToyInstance l \<Rightarrow>
  \<open>Instance %s\<close> (String_concat \<open>
     and \<close> (L.map of_toy_instance_single l)))"

definition "of_toy_def_state_core l =
  String_concat \<open>, \<close> (L.map (\<lambda> ToyDefCoreBinding s \<Rightarrow> To_string s
                             | ToyDefCoreAdd toyi \<Rightarrow> of_toy_instance_single toyi) l)"

definition "of_toy_def_state _ (floor :: \<comment> \<open>polymorphism weakening needed by \<^theory_text>\<open>code_reflect\<close>\<close>
                                         String.literal) = (\<lambda> ToyDefSt n l \<Rightarrow> 
  \<open>State%s %s = [ %s ]\<close>
    floor
    (To_string n)
    (of_toy_def_state_core l))"

definition "of_toy_def_pp_core = (\<lambda> ToyDefPPCoreBinding s \<Rightarrow> To_string s
                                  | ToyDefPPCoreAdd l \<Rightarrow> \<open>[ %s ]\<close> (of_toy_def_state_core l))"

definition "of_toy_def_pre_post _ (floor :: \<comment> \<open>polymorphism weakening needed by \<^theory_text>\<open>code_reflect\<close>\<close>
                                            String.literal) = (\<lambda> ToyDefPP n s_pre s_post \<Rightarrow>
  \<open>PrePost%s %s%s%s\<close>
    floor
    (case n of None \<Rightarrow> \<open>\<close> | Some n \<Rightarrow> \<open>%s = \<close> (To_string n))
    (of_toy_def_pp_core s_pre)
    (case s_post of None \<Rightarrow> \<open>\<close> | Some s_post \<Rightarrow> \<open> %s\<close> (of_toy_def_pp_core s_post)))"

end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.To_oid_def
  Print.of_toy_def_base_def
  Print.of_toy_instance_single_def
  Print.of_toy_instance_def
  Print.of_toy_def_state_core_def
  Print.of_toy_def_state_def
  Print.of_toy_def_pp_core_def
  Print.of_toy_def_pre_post_def

  \<comment> \<open>fun\<close>
  Print.of_toy_list_attr.simps
  Print.of_toy_data_shallow.simps

end
