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

section\<open>Instantiating the Parser of META\<close>

theory  Parser_META
imports Meta_META
        Parser_Toy
        Parser_Toy_extended
begin

subsection\<open>Building Recursors for Records\<close> (* NOTE part to be automated *)

definition "compiler_env_config_rec0 f env = f
  (D_output_disable_thy env)
  (D_output_header_thy env)
  (D_toy_oid_start env)
  (D_output_position env)
  (D_toy_semantics env)
  (D_input_class env)
  (D_input_meta env)
  (D_input_instance env)
  (D_input_state env)
  (D_output_header_force env)
  (D_output_auto_bootstrap env)
  (D_toy_accessor env)
  (D_toy_HO_type env)
  (D_output_sorry_dirty env)"

definition "compiler_env_config_rec f env = compiler_env_config_rec0 f env
  (compiler_env_config.more env)"

(* *)

lemma [code]: "compiler_env_config.extend = (\<lambda>env v. compiler_env_config_rec0 (co14 (\<lambda>f. f v) compiler_env_config_ext) env)"
by(intro ext, simp add: compiler_env_config_rec0_def
                        compiler_env_config.extend_def
                        co14_def K_def)
lemma [code]: "compiler_env_config.make = co14 (\<lambda>f. f ()) compiler_env_config_ext"
by(intro ext, simp add: compiler_env_config.make_def
                        co14_def)
lemma [code]: "compiler_env_config.truncate = compiler_env_config_rec (co14 K compiler_env_config.make)"
by(intro ext, simp add: compiler_env_config_rec0_def
                        compiler_env_config_rec_def
                        compiler_env_config.truncate_def
                        compiler_env_config.make_def
                        co14_def K_def)

subsection\<open>Main\<close>

context Parse
begin

definition "of_toy_flush_all a b = rec_toy_flush_all
  (b \<open>ToyFlushAll\<close>)"

definition "of_floor a b = rec_floor
  (b \<open>Floor1\<close>)
  (b \<open>Floor2\<close>)
  (b \<open>Floor3\<close>)"

definition "of_all_meta_embedding a b = rec_all_meta_embedding
  (ap1 a (b \<open>META_enum\<close>) (of_toy_enum a b))
  (ap2 a (b \<open>META_class_raw\<close>) (of_floor a b) (of_toy_class_raw a b (K of_unit)))
  (ap1 a (b \<open>META_association\<close>) (of_toy_association a b (K of_unit)))
  (ap2 a (b \<open>META_ass_class\<close>) (of_floor a b) (of_toy_ass_class a b))
  (ap2 a (b \<open>META_ctxt\<close>) (of_floor a b) (of_toy_ctxt a b (K of_unit)))

  (ap1 a (b \<open>META_class_synonym\<close>) (of_toy_class_synonym a b))
  (ap1 a (b \<open>META_instance\<close>) (of_toy_instance a b))
  (ap1 a (b \<open>META_def_base_l\<close>) (of_toy_def_base_l a b))
  (ap2 a (b \<open>META_def_state\<close>) (of_floor a b) (of_toy_def_state a b))
  (ap2 a (b \<open>META_def_pre_post\<close>) (of_floor a b) (of_toy_def_pre_post a b))
  (ap1 a (b \<open>META_flush_all\<close>) (of_toy_flush_all a b))"

definition "of_generation_semantics_toy a b = rec_generation_semantics_toy
  (b \<open>Gen_only_design\<close>)
  (b \<open>Gen_only_analysis\<close>)
  (b \<open>Gen_default\<close>)"

definition "of_generation_lemma_mode a b = rec_generation_lemma_mode
  (b \<open>Gen_sorry\<close>)
  (b \<open>Gen_no_dirty\<close>)"

definition "of_compiler_env_config a b f = compiler_env_config_rec
  (ap15 a (b (ext \<open>compiler_env_config_ext\<close>))
    (of_bool b)
    (of_option a b (of_pair a b (of_string a b) (of_pair a b (of_list a b (of_string a b)) (of_string a b))))
    (of_internal_oids a b)
    (of_pair a b (of_nat a b) (of_nat a b))
    (of_generation_semantics_toy a b)
    (of_option a b (of_toy_class a b))
    (of_list a b (of_all_meta_embedding a b))
    (of_list a b (of_pair a b (of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b) (of_pair a b (of_toy_instance_single a b (K of_unit)) (of_internal_oids a b))))
    (of_list a b (of_pair a b (of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b) (of_list a b (of_pair a b (of_internal_oids a b) (of_toy_def_state_core a b (of_pair a b (of_string a b) (of_toy_instance_single a b  (K of_unit))))))))
    (of_bool b)
    (of_bool b)
    (of_pair a b (of_list a b (of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b)) (of_list a b (of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b)))
    (of_list a b (of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b))
    (of_pair a b (of_option a b (of_generation_lemma_mode a b)) (of_bool b))
    (f a b))"

end

lemmas [code] =
  Parse.of_toy_flush_all_def
  Parse.of_floor_def
  Parse.of_all_meta_embedding_def
  Parse.of_generation_semantics_toy_def
  Parse.of_generation_lemma_mode_def
  Parse.of_compiler_env_config_def

section\<open>Finalizing the Parser\<close>

text\<open>It should be feasible to invent a meta-command (e.g., \<open>datatype'\<close>)
to automatically generate the previous recursors in \<open>Parse\<close>.

Otherwise as an extra check, one can also overload polymorphic cartouches in @{theory Isabelle_Meta_Model.Init}
to really check that all the given constructor exists at the time of editing
(similarly as writing @{verbatim "@{term ...}"},
when it is embedded in a @{verbatim "text"} command).\<close>

subsection\<open>Isabelle Syntax\<close>

locale Parse_Isabelle
begin

definition "Of_Pair = \<open>Pair\<close>"
definition "Of_Nil = \<open>Nil\<close>"
definition "Of_Cons = \<open>Cons\<close>"
definition "Of_None = \<open>None\<close>"
definition "Of_Some = \<open>Some\<close>"

\<comment> \<open>recursor types\<close>

definition "of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b Of_Pair) f1 f2)"

definition "of_list a b f = (\<lambda>f0. rec_list f0 o co1 K)
  (b Of_Nil)
  (ar2 a (b Of_Cons) f)"

definition "of_option a b f = rec_option
  (b Of_None)
  (ap1 a (b Of_Some) f)"

\<comment> \<open>ground types\<close>

definition "of_unit b = case_unit
  (b \<open>()\<close>)"

definition of_bool where "of_bool b = case_bool
  (b \<open>True\<close>)
  (b \<open>False\<close>)"

definition "of_string_gen s_flatten s_st0 s_st a b s = 
  b (let s = textstr_of_str (\<lambda>c. \<open>(\<close> @@ s_flatten @@ \<open> \<close> @@ c @@ \<open>)\<close>)
                            (\<lambda>c \<Rightarrow> s_st0 (S.flatten [\<open> 0x\<close>, String.integer_to_digit16 c]))
                            (\<lambda>c. s_st (S.flatten [\<open> (\<close>, c, \<open>)\<close>]))
                            s in
     S.flatten [ \<open>(\<close>, s, \<open>)\<close> ])"

definition "of_string = of_string_gen \<open>Init.S.flatten\<close>
                                          (\<lambda>s. S.flatten [\<open>(Init.ST0\<close>, s, \<open>)\<close>])
                                          (\<lambda>s. S.flatten [\<open>(Init.abr_string.SS_base (Init.string\<^sub>b\<^sub>a\<^sub>s\<^sub>e.ST\<close>, s, \<open>))\<close>])"
definition "of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b s = of_string_gen \<open>Init.String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.flatten\<close>
                                                   (\<lambda>s. S.flatten [\<open>(Init.ST0_base\<close>, s, \<open>)\<close>])
                                                   (\<lambda>s. S.flatten [\<open>(Init.string\<^sub>b\<^sub>a\<^sub>s\<^sub>e.ST\<close>, s, \<open>)\<close>])
                                                   a
                                                   b
                                                   (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String s)"

definition of_nat where "of_nat a b = b o String.natural_to_digit10"

end

sublocale Parse_Isabelle < Parse "id"
                              Parse_Isabelle.of_string
                              Parse_Isabelle.of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e
                              Parse_Isabelle.of_nat
                              Parse_Isabelle.of_unit
                              Parse_Isabelle.of_bool
                              Parse_Isabelle.Of_Pair
                              Parse_Isabelle.Of_Nil
                              Parse_Isabelle.Of_Cons
                              Parse_Isabelle.Of_None
                              Parse_Isabelle.Of_Some
done

context Parse_Isabelle begin
  definition "compiler_env_config a b =
    of_compiler_env_config a b (\<lambda> a b.
      of_pair a b
        (of_list a b (of_all_meta_embedding a b))
        (of_option a b (of_string a b)))"
end

definition "isabelle_of_compiler_env_config = Parse_Isabelle.compiler_env_config"

lemmas [code] =
  Parse_Isabelle.Of_Pair_def
  Parse_Isabelle.Of_Nil_def
  Parse_Isabelle.Of_Cons_def
  Parse_Isabelle.Of_None_def
  Parse_Isabelle.Of_Some_def
  Parse_Isabelle.of_pair_def
  Parse_Isabelle.of_list_def
  Parse_Isabelle.of_option_def
  Parse_Isabelle.of_unit_def
  Parse_Isabelle.of_bool_def
  Parse_Isabelle.of_string_gen_def
  Parse_Isabelle.of_string_def
  Parse_Isabelle.of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
  Parse_Isabelle.of_nat_def

  Parse_Isabelle.compiler_env_config_def

(* *)

definition "isabelle_apply s l = S.flatten [s, S.flatten (L.map (\<lambda> s. S.flatten [\<open> (\<close>, s, \<open>)\<close>]) l)]"

subsection\<open>SML Syntax\<close>

locale Parse_SML
begin

definition "Of_Pair = \<open>I\<close>"
definition "Of_Nil = \<open>nil\<close>"
definition "Of_Cons = \<open>uncurry cons\<close>" (* val cons2 = uncurry cons *)
definition "Of_None = \<open>NONE\<close>"
definition "Of_Some = \<open>SOME\<close>"

(* *)

definition "of_pair a b f1 f2 = (\<lambda>f. \<lambda>(c, d) \<Rightarrow> f c d)
  (ap2 a (b Of_Pair) f1 f2)"

definition "of_list a b f = (\<lambda>f0. rec_list f0 o co1 K)
  (b Of_Nil)
  (ar2 a (b Of_Cons) f)"

definition "of_option a b f = rec_option
  (b Of_None)
  (ap1 a (b Of_Some) f)"

(* *)

definition "of_unit b = case_unit
  (b \<open>()\<close>)"

definition of_bool where "of_bool b = case_bool
  (b \<open>true\<close>)
  (b \<open>false\<close>)"

definition \<open>sml_escape =
  String.replace_integers (\<lambda>x. if x = 0x0A then \<open>\n\<close>
                               else if x = 0x05 then \<open>\005\<close>
                               else if x = 0x06 then \<open>\006\<close>
                               else if x = 0x7F then \<open>\127\<close>
                               else \<degree>x\<degree>)\<close>

definition \<open>of_string a b =
 (\<lambda>x. b (S.flatten [ \<open>(META.SS_base (META.ST "\<close>
                  , sml_escape x
                  , \<open>"))\<close>]))\<close>

definition \<open>of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e a b =
 (\<lambda>x. b (S.flatten [ \<open>(META.ST "\<close>
                  , sml_escape (String\<^sub>b\<^sub>a\<^sub>s\<^sub>e.to_String x)
                  , \<open>")\<close>]))\<close>

definition of_nat where "of_nat a b = (\<lambda>x. b (S.flatten [\<open>(Code_Numeral.natural_of_integer \<close>, String.natural_to_digit10 x, \<open>)\<close>]))"

end

sublocale Parse_SML < Parse "\<lambda>c. case String.to_list c of x # xs \<Rightarrow> S.flatten [String.uppercase \<lless>[x]\<ggreater>, \<lless>xs\<ggreater>]"
                         Parse_SML.of_string
                         Parse_SML.of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e
                         Parse_SML.of_nat
                         Parse_SML.of_unit
                         Parse_SML.of_bool
                         Parse_SML.Of_Pair
                         Parse_SML.Of_Nil
                         Parse_SML.Of_Cons
                         Parse_SML.Of_None
                         Parse_SML.Of_Some
done

context Parse_SML begin
  definition "compiler_env_config a b = of_compiler_env_config a b (\<lambda> _. of_unit)"
end

definition "sml_of_compiler_env_config = Parse_SML.compiler_env_config"

lemmas [code] =
  Parse_SML.Of_Pair_def
  Parse_SML.Of_Nil_def
  Parse_SML.Of_Cons_def
  Parse_SML.Of_None_def
  Parse_SML.Of_Some_def

  Parse_SML.of_pair_def
  Parse_SML.of_list_def
  Parse_SML.of_option_def
  Parse_SML.of_unit_def
  Parse_SML.of_bool_def
  Parse_SML.of_string_def
  Parse_SML.of_string\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def
  Parse_SML.of_nat_def

  Parse_SML.sml_escape_def
  Parse_SML.compiler_env_config_def

(* *)

definition "sml_apply s l = S.flatten [s, \<open> (\<close>, case l of x # xs \<Rightarrow> S.flatten [x, S.flatten (L.map (\<lambda>s. S.flatten [\<open>, \<close>, s]) xs)], \<open>)\<close> ]"

end
