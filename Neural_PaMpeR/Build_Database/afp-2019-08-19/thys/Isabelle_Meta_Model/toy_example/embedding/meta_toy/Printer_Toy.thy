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

section\<open>Instantiating the Printer for Toy (I)\<close>

theory  Printer_Toy
imports Meta_Toy
        "../../../meta_isabelle/Printer_Pure"
begin

context Print
begin

declare[[cartouche_type' = "abr_string"]]

definition "concatWith l =
 (if l = [] then
    id
  else
    sprint2 STR ''(%s. (%s))''\<acute> (To_string (String_concatWith \<open> \<close> (\<open>\<lambda>\<close> # rev l))))"

declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]

fun of_ctxt2_term_aux where "of_ctxt2_term_aux l e =
 (\<lambda> T_pure pure \<Rightarrow> concatWith l (of_pure_term [] pure)
  | T_to_be_parsed _ s \<Rightarrow> concatWith l (To_string s)
  | T_lambda s c \<Rightarrow> of_ctxt2_term_aux (s # l) c) e"
definition "of_ctxt2_term = of_ctxt2_term_aux []"

definition \<open>of_toy_ctxt _ (floor :: \<comment> \<open>polymorphism weakening needed by \<^theory_text>\<open>code_reflect\<close>\<close>
                                     String.literal) ctxt = 
 (let f_inv = \<lambda> T_inv b (ToyProp_ctxt n s) \<Rightarrow> \<open>  %sInv %s : "%s"\<close>
              (if b then \<open>Existential\<close> else \<open>\<close>)
              (case n of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> To_string s)
              (of_ctxt2_term s) in
  \<open>Context%s %s%s %s\<close>
        floor
        (case Ctxt_param ctxt of
           [] \<Rightarrow> \<open>\<close>
         | l \<Rightarrow> \<open>%s : \<close> (String_concat \<open>, \<close> (L.map To_string l)))
        (To_string (ty_obj_to_string (Ctxt_ty ctxt)))
        (String_concat \<open>
\<close> (L.map (\<lambda> Ctxt_pp ctxt \<Rightarrow>
                \<open>:: %s (%s) %s
%s\<close>
        (To_string (Ctxt_fun_name ctxt))
        (String_concat \<open>, \<close>
          (L.map
            (\<lambda> (s, ty). \<open>%s : %s\<close> (To_string s) (To_string (str_of_ty ty)))
            (Ctxt_fun_ty_arg ctxt)))
        (case Ctxt_fun_ty_out ctxt of None \<Rightarrow> \<open>\<close>
                                    | Some ty \<Rightarrow> \<open>: %s\<close> (To_string (str_of_ty ty)))
        (String_concat \<open>
\<close>
          (L.map
            (\<lambda> T_pp pref (ToyProp_ctxt n s) \<Rightarrow> \<open>  %s %s: "%s"\<close>
                (case pref of ToyCtxtPre \<Rightarrow> \<open>Pre\<close>
                            | ToyCtxtPost \<Rightarrow> \<open>Post\<close>)
                (case n of None \<Rightarrow> \<open>\<close> | Some s \<Rightarrow> To_string s)
                (of_ctxt2_term s)
             | T_invariant inva \<Rightarrow> f_inv inva)
            (Ctxt_expr ctxt)))
          | Ctxt_inv inva \<Rightarrow> f_inv inva)
         (Ctxt_clause ctxt))))\<close>

end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.concatWith_def
  Print.of_ctxt2_term_def
  Print.of_toy_ctxt_def
  \<comment> \<open>fun\<close>
  Print.of_ctxt2_term_aux.simps

end
