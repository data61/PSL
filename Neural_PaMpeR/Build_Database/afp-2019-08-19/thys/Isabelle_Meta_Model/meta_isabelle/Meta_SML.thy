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

section\<open>SML Meta-Model aka. AST definition of SML\<close>

theory  Meta_SML
imports "../Init"
begin

subsection\<open>Type Definition\<close>

text\<open>The following datatypes beginning with \verb|semi__| represent semi-concrete syntax,
       deliberately not minimal abstract syntax like (Pure) Term,
       this is for example to facilitate the pretty-printing process,
       or for manipulating recursively data-structures through an abstract and typed API.\<close>

datatype semi__val_fun = Sval
                       | Sfun

datatype semi__term' = SML_string string
                     | SML_rewrite semi__val_fun semi__term' \<comment> \<open>left\<close> string \<comment> \<open>symb rewriting\<close> semi__term' \<comment> \<open>right\<close>
                     | SML_basic "string list"
                     | SML_binop semi__term' string semi__term'
                     | SML_annot semi__term' string \<comment> \<open>type\<close>
                     | SML_function "(semi__term' \<comment> \<open>pattern\<close> \<times> semi__term' \<comment> \<open>to return\<close>) list"
                     | SML_apply semi__term' "semi__term' list"
                     | SML_paren string \<comment> \<open>left\<close> string \<comment> \<open>right\<close> semi__term'
                     | SML_let_open string semi__term'

subsection\<open>Extending the Meta-Model\<close>

locale SML
begin
no_type_notation abr_string ("string") definition "string = SML_string"
definition "rewrite = SML_rewrite"
definition "basic = SML_basic"
definition "binop = SML_binop"
definition "annot = SML_annot"
definition "function = SML_function"
definition "apply = SML_apply"
definition "paren = SML_paren"
definition "let_open = SML_let_open"

definition "app s = apply (basic [s])"
definition "none = basic [\<open>NONE\<close>]"
definition "some s = app \<open>SOME\<close> [s]"
definition "option' f l = (case map_option f l of None \<Rightarrow> none | Some s \<Rightarrow> some s)"
definition "option = option' id"
definition "parenthesis \<comment> \<open>mandatory parenthesis\<close> = paren \<open>(\<close> \<open>)\<close>"
definition "binop_l s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. binop x s) xs x)"
definition "list l = (case l of [] \<Rightarrow> basic [\<open>[]\<close>] | _ \<Rightarrow> paren \<open>[\<close> \<open>]\<close> (binop_l \<open>,\<close> l))"
definition "list' f l = list (L.map f l)"
definition "pair e1 e2 = parenthesis (binop e1 \<open>,\<close> e2)"
definition "pair' f1 f2 = (\<lambda> (e1, e2) \<Rightarrow> parenthesis (binop (f1 e1) \<open>,\<close> (f2 e2)))"
definition "rewrite_val = rewrite Sval"
definition "rewrite_fun = rewrite Sfun"
end

lemmas [code] =
  \<comment> \<open>def\<close>
  SML.string_def
  SML.rewrite_def
  SML.basic_def
  SML.binop_def
  SML.annot_def
  SML.function_def
  SML.apply_def
  SML.paren_def
  SML.let_open_def
  SML.app_def
  SML.none_def
  SML.some_def
  SML.option'_def
  SML.option_def
  SML.parenthesis_def
  SML.binop_l_def
  SML.list_def
  SML.list'_def
  SML.pair_def
  SML.pair'_def
  SML.rewrite_val_def
  SML.rewrite_fun_def

end
