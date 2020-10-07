(******************************************************************************
 * A Meta-Model for the Isabelle API
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

section\<open>Instantiating the Printer for SML\<close>

theory  Printer_SML
imports Meta_SML
        Printer_init
begin

context Print
begin

definition "of_semi__val_fun = (\<lambda> Sval \<Rightarrow> \<open>val\<close>
                                | Sfun \<Rightarrow> \<open>fun\<close>)"

fun of_semi__term' where \<open>of_semi__term' e = (\<lambda>
    SML_string s \<Rightarrow> \<open>"%s"\<close> (To_string (escape_sml s))
  | SML_rewrite val_fun e1 symb e2 \<Rightarrow> \<open>%s %s %s %s\<close> (of_semi__val_fun val_fun) (of_semi__term' e1) (To_string symb) (of_semi__term' e2)
  | SML_basic l \<Rightarrow> \<open>%s\<close> (String_concat \<open> \<close> (L.map To_string l))
  | SML_binop e1 s e2 \<Rightarrow> \<open>%s %s %s\<close> (of_semi__term' e1) (of_semi__term' (SML_basic [s])) (of_semi__term' e2)
  | SML_annot e s \<Rightarrow> \<open>(%s:%s)\<close> (of_semi__term' e) (To_string s)
  | SML_function l \<Rightarrow> \<open>(fn %s)\<close> (String_concat \<open>
    | \<close> (List.map (\<lambda> (s1, s2) \<Rightarrow> \<open>%s => %s\<close> (of_semi__term' s1) (of_semi__term' s2)) l))
  | SML_apply e l \<Rightarrow> \<open>(%s %s)\<close> (of_semi__term' e) (String_concat \<open> \<close> (List.map (\<lambda> e \<Rightarrow> \<open>(%s)\<close> (of_semi__term' e)) l))
  | SML_paren p_left p_right e \<Rightarrow> \<open>%s%s%s\<close> (To_string p_left) (of_semi__term' e) (To_string p_right)
  | SML_let_open s e \<Rightarrow> \<open>let open %s in %s end\<close> (To_string s) (of_semi__term' e)) e\<close>

end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.of_semi__val_fun_def
  \<comment> \<open>fun\<close>
  Print.of_semi__term'.simps

end
