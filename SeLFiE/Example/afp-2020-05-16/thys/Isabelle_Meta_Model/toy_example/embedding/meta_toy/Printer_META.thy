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

section\<open>Instantiating the Printer for META\<close>

theory  Printer_META
imports Parser_META
        "../../../meta_isabelle/Printer_Isabelle"
        Printer_Toy_extended
begin

context Print
begin

definition "of\<^sub>e\<^sub>n\<^sub>v_section env =
 (if D_output_disable_thy env then
    \<lambda>_. \<open>\<close>
  else
    of_section env)"

definition "of\<^sub>e\<^sub>n\<^sub>v_semi__theory env =
            (\<lambda> Theory_section section_title \<Rightarrow> of\<^sub>e\<^sub>n\<^sub>v_section env section_title
             | x \<Rightarrow> of_semi__theory env x)"

definition \<open>of\<^sub>e\<^sub>n\<^sub>v_semi__theories env =
 (\<lambda> Theories_one t \<Rightarrow> of\<^sub>e\<^sub>n\<^sub>v_semi__theory env t
  | Theories_locale data l \<Rightarrow> 
      \<open>locale %s =
%s
begin
%s
end\<close>   (To_string (HolThyLocale_name data))
        (String_concat_map
           \<open>
\<close>
           (\<lambda> (l_fix, o_assum).
                \<open>%s%s\<close> (String_concat_map \<open>
\<close> (\<lambda>(e, ty). \<open>fixes "%s" :: "%s"\<close> (of_semi__term e) (of_semi__typ ty)) l_fix)
                                (case o_assum of None \<Rightarrow> \<open>\<close>
                                               | Some (name, e) \<Rightarrow> \<open>
assumes %s: "%s"\<close> (To_string name) (of_semi__term e)))
           (HolThyLocale_header data))
        (String_concat_map \<open>

\<close> (String_concat_map \<open>

\<close> (of\<^sub>e\<^sub>n\<^sub>v_semi__theory env)) l))\<close>

(* *)

definition "of_floor = (\<lambda> Floor1 \<Rightarrow> \<open>\<close> | Floor2 \<Rightarrow> \<open>[shallow]\<close> | Floor3 \<Rightarrow> \<open>[shallow_shallow]\<close>)"

definition "of_all_meta_embedding env =
 (\<lambda> META_ctxt floor ctxt \<Rightarrow> of_toy_ctxt env (of_floor floor) ctxt
  | META_instance i \<Rightarrow> of_toy_instance env i
  | META_def_state floor s \<Rightarrow> of_toy_def_state env (of_floor floor) s
  | META_def_pre_post floor p \<Rightarrow> of_toy_def_pre_post env (of_floor floor) p)"

definition "of_boot_generation_syntax _ = (\<lambda> Boot_generation_syntax mode \<Rightarrow>
  \<open>generation_syntax [ shallow%s ]\<close>
    (let f = \<open> (generation_semantics [ %s ])\<close> in
     case mode of Gen_only_design \<Rightarrow> f \<open>design\<close>
                | Gen_only_analysis \<Rightarrow> f \<open>analysis\<close>
                | Gen_default \<Rightarrow> \<open>\<close>))"

declare[[cartouche_type' = "abr_string"]]

definition "of_boot_setup_env env = (\<lambda> Boot_setup_env e \<Rightarrow>
  of_setup
    env
    (Setup
      (SML.app
        \<open>Generation_mode.update_compiler_config\<close>
        [ SML.app
            \<open>K\<close>
            [ SML_let_open
                \<open>META\<close>
                (\<comment> \<open>Instead of using\<close>
                 \<comment> \<open>\<open>sml_of_compiler_env_config SML_apply (\<lambda>x. SML_basic [x]) e\<close>\<close>
                 \<comment> \<open>the following allows to 'automatically' return an uncurried expression:\<close>
                 SML_basic [sml_of_compiler_env_config sml_apply id e])]])))"

declare[[cartouche_type' = "fun\<^sub>p\<^sub>r\<^sub>i\<^sub>n\<^sub>t\<^sub>f"]]

definition "of_all_meta env = (\<lambda>
    META_semi__theories thy \<Rightarrow> of\<^sub>e\<^sub>n\<^sub>v_semi__theories env thy
  | META_boot_generation_syntax generation_syntax \<Rightarrow> of_boot_generation_syntax env generation_syntax
  | META_boot_setup_env setup_env \<Rightarrow> of_boot_setup_env env setup_env
  | META_all_meta_embedding all_meta_embedding \<Rightarrow> of_all_meta_embedding env all_meta_embedding)"

definition "of_all_meta_lists env l_thy =
  (let (th_beg, th_end) = case D_output_header_thy env of None \<Rightarrow> ([], [])
   | Some (name, fic_import, fic_import_boot) \<Rightarrow>
       ( [ \<open>theory %s imports %s begin\<close>
             (To_string name)
             (of_semi__term (term_binop \<langle>STR '' ''\<rangle>
                                        (L.map Term_string
                                               (fic_import @@@@ (if D_output_header_force env
                                                                  | D_output_auto_bootstrap env then
                                                                   [fic_import_boot]
                                                                 else
                                                                   []))))) ]
       , [ \<open>\<close>, \<open>end\<close> ]) in
  L.flatten
        [ th_beg
        , L.flatten (fst (L.mapM (\<lambda>l (i, cpt).
            let (l_thy, lg) = L.mapM (\<lambda>l n. (of_all_meta env l, Succ n)) l 0 in
            (( \<open>\<close>
             # \<open>%s(* %d ************************************ %d + %d *)\<close>
                 (To_string (if compiler_env_config.more env then \<langle>STR ''''\<rangle> else \<degree>integer_escape\<degree>)) (To_nat (Succ i)) (To_nat cpt) (To_nat lg)
             # l_thy), Succ i, cpt + lg)) l_thy (D_output_position env)))
        , th_end ])"
end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.of\<^sub>e\<^sub>n\<^sub>v_section_def
  Print.of\<^sub>e\<^sub>n\<^sub>v_semi__theory_def
  Print.of\<^sub>e\<^sub>n\<^sub>v_semi__theories_def
  Print.of_floor_def
  Print.of_all_meta_embedding_def
  Print.of_boot_generation_syntax_def
  Print.of_boot_setup_env_def
  Print.of_all_meta_def
  Print.of_all_meta_lists_def

  \<comment> \<open>fun\<close>

end
