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

section\<open>Instantiating the Printer for Isabelle\<close>

theory  Printer_Isabelle
imports Meta_Isabelle
        Printer_Pure
        Printer_SML
begin

context Print
begin

fun of_semi__typ where "of_semi__typ e = (\<lambda>
    Typ_base s \<Rightarrow> To_string s
  | Typ_apply name l \<Rightarrow> \<open>%s %s\<close> (let s = String_concat \<open>, \<close> (List.map of_semi__typ l) in
                                 case l of [_] \<Rightarrow> s | _ \<Rightarrow> \<open>(%s)\<close> s)
                                (of_semi__typ name)
  | Typ_apply_bin s ty1 ty2 \<Rightarrow> \<open>%s %s %s\<close> (of_semi__typ ty1) (To_string s) (of_semi__typ ty2)
  | Typ_apply_paren s1 s2 ty \<Rightarrow> \<open>%s%s%s\<close> (To_string s1) (of_semi__typ ty) (To_string s2)) e"

definition "of_datatype _ = (\<lambda> Datatype n l \<Rightarrow>
  \<open>datatype %s = %s\<close>
    (To_string n)
    (String_concat \<open>
                        | \<close>
      (L.map
        (\<lambda>(n,l).
         \<open>%s %s\<close>
           (To_string n)
           (String_concat \<open> \<close> (L.map (\<lambda>x. \<open>\"%s\"\<close> (of_semi__typ x)) l))) l) ))"

definition "of_type_synonym _ = (\<lambda> Type_synonym n v l \<Rightarrow>
  \<open>type_synonym %s = \"%s\"\<close> (if v = [] then 
                                To_string n
                              else
                                of_semi__typ (Typ_apply (Typ_base n) (L.map Typ_base v)))
                             (of_semi__typ l))"

fun of_semi__term where "of_semi__term e = (\<lambda>
    Term_rewrite e1 symb e2 \<Rightarrow> \<open>%s %s %s\<close> (of_semi__term e1) (To_string symb) (of_semi__term e2)
  | Term_basic l \<Rightarrow> \<open>%s\<close> (String_concat \<open> \<close> (L.map To_string l))
  | Term_annot e s \<Rightarrow> \<open>(%s::%s)\<close> (of_semi__term e) (of_semi__typ s)
  | Term_bind symb e1 e2 \<Rightarrow> \<open>(%s%s. %s)\<close> (To_string symb) (of_semi__term e1) (of_semi__term e2)
  | Term_fun_case e_case l \<Rightarrow> \<open>(%s %s)\<close>
      (case e_case of None \<Rightarrow> \<open>\<lambda>\<close>
                    | Some e \<Rightarrow> \<open>case %s of\<close> (of_semi__term e))
      (String_concat \<open>
    | \<close> (List.map (\<lambda> (s1, s2) \<Rightarrow> \<open>%s \<Rightarrow> %s\<close> (of_semi__term s1) (of_semi__term s2)) l))
  | Term_apply e l \<Rightarrow> \<open>%s %s\<close> (of_semi__term e) (String_concat \<open> \<close> (List.map (\<lambda> e \<Rightarrow> \<open>%s\<close> (of_semi__term e)) l))
  | Term_paren p_left p_right e \<Rightarrow> \<open>%s%s%s\<close> (To_string p_left) (of_semi__term e) (To_string p_right)
  | Term_if_then_else e_if e_then e_else \<Rightarrow> \<open>if %s then %s else %s\<close> (of_semi__term e_if) (of_semi__term e_then) (of_semi__term e_else)
  | Term_term l pure \<Rightarrow> of_pure_term (L.map To_string l) pure) e"

definition "of_type_notation _ = (\<lambda> Type_notation n e \<Rightarrow>
  \<open>type_notation %s (\"%s\")\<close> (To_string n) (To_string e))"

definition "of_instantiation _ = (\<lambda> Instantiation n n_def expr \<Rightarrow>
  let name = To_string n in
  \<open>instantiation %s :: object
begin
  definition %s_%s_def : \"%s\"
  instance ..
end\<close>
    name
    (To_string n_def)
    name
    (of_semi__term expr))"

definition "of_overloading _ = (\<lambda> Overloading n_c e_c n e \<Rightarrow>
  \<open>overloading %s \<equiv> \"%s\"
begin
  definition %s : \"%s\"
end\<close> (To_string n_c) (of_semi__term e_c) (To_string n) (of_semi__term e))"

definition "of_consts _ = (\<lambda> Consts n ty symb \<Rightarrow>
  \<open>consts %s :: \"%s\" (\"%s %s\")\<close> (To_string n) (of_semi__typ ty) (To_string Consts_value) (To_string symb))"

definition "of_definition _ = (\<lambda>
    Definition e \<Rightarrow> \<open>definition \"%s\"\<close> (of_semi__term e)
  | Definition_where1 name (abbrev, prio) e \<Rightarrow> \<open>definition %s (\"(1%s)\" %d)
  where \"%s\"\<close> (To_string name) (of_semi__term abbrev) (To_nat prio) (of_semi__term e)
  | Definition_where2 name abbrev e \<Rightarrow> \<open>definition %s (\"%s\")
  where \"%s\"\<close> (To_string name) (of_semi__term abbrev) (of_semi__term e))"

definition "(of_semi__thm_attribute_aux_gen :: String.literal \<times> String.literal \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _) m lacc s = 
 (let s_base = (\<lambda>s lacc. \<open>%s[%s]\<close> (To_string s) (String_concat \<open>, \<close> (L.map (\<lambda>(s, x). \<open>%s %s\<close> s x) lacc))) in
  s_base s (m # lacc))"

definition "of_semi__thm_attribute_aux_gen_where l = 
 (\<open>where\<close>, String_concat \<open> and \<close> (L.map (\<lambda>(var, expr). \<open>%s = \"%s\"\<close>
                                                          (To_string var)
                                                          (of_semi__term expr)) l))"

definition "of_semi__thm_attribute_aux_gen_of l =
 (\<open>of\<close>, String_concat \<open> \<close> (L.map (\<lambda>expr. \<open>\"%s\"\<close> (of_semi__term expr)) l))"

(* NOTE all 'let' declarations can be put at the beginning *)
   (*let f_where = (\<lambda>l. (\<open>where\<close>, String_concat \<open> and \<close>
                                        (L.map (\<lambda>(var, expr). \<open>%s = \"%s\"\<close>
                                                        (To_string var)
                                                        (of_semi__term expr)) l)))
     ; f_of = (\<lambda>l. (\<open>of\<close>, String_concat \<open> \<close>
                                  (L.map (\<lambda>expr. \<open>\"%s\"\<close>
                                                        (of_semi__term expr)) l)))
     ; f_symmetric = (\<open>symmetric\<close>, \<open>\<close>)
     ; s_base = (\<lambda>s lacc. \<open>%s[%s]\<close> (To_string s) (String_concat \<open>, \<close> (L.map (\<lambda>(s, x). \<open>%s %s\<close> s x) lacc))) in
   *)
fun of_semi__thm_attribute_aux where "of_semi__thm_attribute_aux lacc e =
  (\<lambda> Thm_thm s \<Rightarrow> To_string s
   | Thm_thms s \<Rightarrow> To_string s

   | Thm_THEN (Thm_thm s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>THEN\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_THEN (Thm_thms s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>THEN\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_THEN e1 e2 \<Rightarrow> of_semi__thm_attribute_aux ((\<open>THEN\<close>, of_semi__thm_attribute_aux [] e2) # lacc) e1

   | Thm_simplified (Thm_thm s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>simplified\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_simplified (Thm_thms s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>simplified\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_simplified e1 e2 \<Rightarrow> of_semi__thm_attribute_aux ((\<open>simplified\<close>, of_semi__thm_attribute_aux [] e2) # lacc) e1

   | Thm_symmetric (Thm_thm s) \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>symmetric\<close>, \<open>\<close>) lacc s 
   | Thm_symmetric (Thm_thms s) \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>symmetric\<close>, \<open>\<close>) lacc s
   | Thm_symmetric e1 \<Rightarrow> of_semi__thm_attribute_aux ((\<open>symmetric\<close>, \<open>\<close>) # lacc) e1

   | Thm_where (Thm_thm s) l \<Rightarrow> of_semi__thm_attribute_aux_gen (of_semi__thm_attribute_aux_gen_where l) lacc s
   | Thm_where (Thm_thms s) l \<Rightarrow> of_semi__thm_attribute_aux_gen (of_semi__thm_attribute_aux_gen_where l) lacc s
   | Thm_where e1 l \<Rightarrow> of_semi__thm_attribute_aux (of_semi__thm_attribute_aux_gen_where l # lacc) e1

   | Thm_of (Thm_thm s) l \<Rightarrow> of_semi__thm_attribute_aux_gen (of_semi__thm_attribute_aux_gen_of l) lacc s
   | Thm_of (Thm_thms s) l \<Rightarrow> of_semi__thm_attribute_aux_gen (of_semi__thm_attribute_aux_gen_of l) lacc s
   | Thm_of e1 l \<Rightarrow> of_semi__thm_attribute_aux (of_semi__thm_attribute_aux_gen_of l # lacc) e1

   | Thm_OF (Thm_thm s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>OF\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_OF (Thm_thms s) e2 \<Rightarrow> of_semi__thm_attribute_aux_gen (\<open>OF\<close>, of_semi__thm_attribute_aux [] e2) lacc s
   | Thm_OF e1 e2 \<Rightarrow> of_semi__thm_attribute_aux ((\<open>OF\<close>, of_semi__thm_attribute_aux [] e2) # lacc) e1) e"

definition "of_semi__thm_attribute = of_semi__thm_attribute_aux []"

definition "of_semi__thm = (\<lambda> Thms_single thy \<Rightarrow> of_semi__thm_attribute thy
                         | Thms_mult thy \<Rightarrow> of_semi__thm_attribute thy)"

definition "of_semi__thm_attribute_l l = String_concat \<open>
                            \<close> (L.map of_semi__thm_attribute l)"
definition "of_semi__thm_attribute_l1 l = String_concat \<open> \<close> (L.map of_semi__thm_attribute l)"

definition "of_semi__thm_l l = String_concat \<open> \<close> (L.map of_semi__thm l)"

definition "of_lemmas _ = (\<lambda> Lemmas_simp_thm simp s l \<Rightarrow>
  \<open>lemmas%s%s = %s\<close>
    (if String.is_empty s then \<open>\<close> else \<open> %s\<close> (To_string s))
    (if simp then \<open>[simp,code_unfold]\<close> else \<open>\<close>)
    (of_semi__thm_attribute_l l)
                           | Lemmas_simp_thms s l \<Rightarrow>
  \<open>lemmas%s [simp,code_unfold] = %s\<close>
    (if String.is_empty s then \<open>\<close> else \<open> %s\<close> (To_string s))
    (String_concat \<open>
                            \<close> (L.map To_string l)))"

definition "(of_semi__attrib_genA :: (semi__thm list \<Rightarrow> String.literal)
   \<Rightarrow> String.literal \<Rightarrow> semi__thm list \<Rightarrow> String.literal) f attr l = \<comment> \<open>error reflection: to be merged\<close>
 (if l = [] then
    \<open>\<close>
  else
    \<open> %s: %s\<close> attr (f l))"

definition "(of_semi__attrib_genB :: (string list \<Rightarrow> String.literal)
   \<Rightarrow> String.literal \<Rightarrow> string list \<Rightarrow> String.literal) f attr l = \<comment> \<open>error reflection: to be merged\<close>
 (if l = [] then
    \<open>\<close>
  else
    \<open> %s: %s\<close> attr (f l))"

definition "of_semi__attrib = of_semi__attrib_genA of_semi__thm_l"
definition "of_semi__attrib1 = of_semi__attrib_genB (\<lambda>l. String_concat \<open> \<close> (L.map To_string l))"

definition "of_semi__method_simp (s :: \<comment> \<open>polymorphism weakening needed by \<^theory_text>\<open>code_reflect\<close>\<close>
                                       String.literal) =
 (\<lambda> Method_simp_only l \<Rightarrow> \<open>%s only: %s\<close> s (of_semi__thm_l l)
  | Method_simp_add_del_split l1 l2 [] \<Rightarrow> \<open>%s%s%s\<close>
      s
      (of_semi__attrib \<open>add\<close> l1)
      (of_semi__attrib \<open>del\<close> l2)
  | Method_simp_add_del_split l1 l2 l3 \<Rightarrow> \<open>%s%s%s%s\<close>
      s
      (of_semi__attrib \<open>add\<close> l1)
      (of_semi__attrib \<open>del\<close> l2)
      (of_semi__attrib \<open>split\<close> l3))"

fun of_semi__method where "of_semi__method expr = (\<lambda>
    Method_rule o_s \<Rightarrow> \<open>rule%s\<close> (case o_s of None \<Rightarrow> \<open>\<close>
                                           | Some s \<Rightarrow> \<open> %s\<close> (of_semi__thm_attribute s))
  | Method_drule s \<Rightarrow> \<open>drule %s\<close> (of_semi__thm_attribute s)
  | Method_erule s \<Rightarrow> \<open>erule %s\<close> (of_semi__thm_attribute s)
  | Method_intro l \<Rightarrow> \<open>intro %s\<close> (of_semi__thm_attribute_l1 l)
  | Method_elim s \<Rightarrow> \<open>elim %s\<close> (of_semi__thm_attribute s)
  | Method_subst asm l s =>
      let s_asm = if asm then \<open>(asm) \<close> else \<open>\<close> in
      if L.map String.meta_of_logic l = [STR ''0''] then
        \<open>subst %s%s\<close> s_asm (of_semi__thm_attribute s)
      else
        \<open>subst %s(%s) %s\<close> s_asm (String_concat \<open> \<close> (L.map To_string l)) (of_semi__thm_attribute s)
  | Method_insert l => \<open>insert %s\<close> (of_semi__thm_l l)
  | Method_plus t \<Rightarrow> \<open>(%s)+\<close> (String_concat \<open>, \<close> (List.map of_semi__method t))
  | Method_option t \<Rightarrow> \<open>(%s)?\<close> (String_concat \<open>, \<close> (List.map of_semi__method t))
  | Method_or t \<Rightarrow> \<open>(%s)\<close> (String_concat \<open> | \<close> (List.map of_semi__method t))
  | Method_one s \<Rightarrow> of_semi__method_simp \<open>simp\<close> s
  | Method_all s \<Rightarrow> of_semi__method_simp \<open>simp_all\<close> s
  | Method_auto_simp_add_split l_simp l_split \<Rightarrow> \<open>auto%s%s\<close>
      (of_semi__attrib \<open>simp\<close> l_simp)
      (of_semi__attrib1 \<open>split\<close> l_split)
  | Method_rename_tac l \<Rightarrow> \<open>rename_tac %s\<close> (String_concat \<open> \<close> (L.map To_string l))
  | Method_case_tac e \<Rightarrow> \<open>case_tac \"%s\"\<close> (of_semi__term e)
  | Method_blast None \<Rightarrow> \<open>blast\<close>
  | Method_blast (Some n) \<Rightarrow> \<open>blast %d\<close> (To_nat n)
  | Method_clarify \<Rightarrow> \<open>clarify\<close>
  | Method_metis l_opt l \<Rightarrow> \<open>metis %s%s\<close> (if l_opt = [] then \<open>\<close>
                                          else
                                            \<open>(%s) \<close> (String_concat \<open>, \<close> (L.map To_string l_opt))) (of_semi__thm_attribute_l1 l)) expr"

definition "of_semi__command_final = (\<lambda> Command_done \<Rightarrow> \<open>done\<close>
                                      | Command_by l_apply \<Rightarrow> \<open>by(%s)\<close> (String_concat \<open>, \<close> (L.map of_semi__method l_apply))
                                      | Command_sorry \<Rightarrow> \<open>sorry\<close>)"

definition "of_semi__command_state = (
  \<lambda> Command_apply_end [] \<Rightarrow> \<open>\<close>
  | Command_apply_end l_apply \<Rightarrow> \<open>  apply_end(%s)
\<close> (String_concat \<open>, \<close> (L.map of_semi__method l_apply)))"

definition \<open>of_semi__command_proof = (
  let thesis = \<open>?thesis\<close>
    ; scope_thesis_gen = \<lambda>proof show when. \<open>  proof - %s show %s%s
\<close> proof
  show
  (if when = [] then
     \<open>\<close>
   else
     \<open> when %s\<close> (String_concat \<open> \<close> (L.map (\<lambda>t. \<open>"%s"\<close> (of_semi__term t)) when)))
    ; scope_thesis = \<lambda>s. scope_thesis_gen s thesis [] in
  \<lambda> Command_apply [] \<Rightarrow> \<open>\<close>
  | Command_apply l_apply \<Rightarrow> \<open>  apply(%s)
\<close> (String_concat \<open>, \<close> (L.map of_semi__method l_apply))
  | Command_using l \<Rightarrow> \<open>  using %s
\<close> (of_semi__thm_l l)
  | Command_unfolding l \<Rightarrow> \<open>  unfolding %s
\<close> (of_semi__thm_l l)
  | Command_let e_name e_body \<Rightarrow> scope_thesis (\<open>let %s = "%s"\<close> (of_semi__term e_name) (of_semi__term e_body))
  | Command_have n b e e_last \<Rightarrow> scope_thesis (\<open>have %s%s: "%s" %s\<close> (To_string n) (if b then \<open>[simp]\<close> else \<open>\<close>) (of_semi__term e) (of_semi__command_final e_last))
  | Command_fix_let l l_let o_show _ \<Rightarrow>
      scope_thesis_gen
        (\<open>fix %s%s\<close> (String_concat \<open> \<close> (L.map To_string l))
                    (String_concat \<open>
\<close>                                  (L.map
                                     (\<lambda>(e_name, e_body).
                                       \<open>          let %s = "%s"\<close> (of_semi__term e_name) (of_semi__term e_body))
                                     l_let)))
        (case o_show of None \<Rightarrow> thesis
                      | Some (l_show, _) \<Rightarrow> \<open>"%s"\<close> (String_concat \<open> \<Longrightarrow> \<close> (L.map of_semi__term l_show)))
        (case o_show of None \<Rightarrow> [] | Some (_, l_when) \<Rightarrow> l_when))\<close>

definition "of_lemma _ =
 (\<lambda> Lemma n l_spec l_apply tactic_last \<Rightarrow>
    \<open>lemma %s : \"%s\"
%s%s\<close>
      (To_string n)
      (String_concat \<open> \<Longrightarrow> \<close> (L.map of_semi__term l_spec))
      (String_concat \<open>\<close> (L.map (\<lambda> [] \<Rightarrow> \<open>\<close> | l_apply \<Rightarrow> \<open>  apply(%s)
\<close>
                                                          (String_concat \<open>, \<close> (L.map of_semi__method l_apply)))
                               l_apply))
      (of_semi__command_final tactic_last)
  | Lemma_assumes n l_spec concl l_apply tactic_last \<Rightarrow>
    \<open>lemma %s : %s
%s%s %s\<close>
      (To_string n)
      (String_concat \<open>\<close> (L.map (\<lambda>(n, b, e).
          \<open>
assumes %s\"%s\"\<close>
            (let (n, b) = if b then (\<open>%s[simp]\<close> (To_string n), False) else (To_string n, String.is_empty n) in
             if b then \<open>\<close> else \<open>%s: \<close> n)
            (of_semi__term e)) l_spec
       @@@@
       [\<open>
shows \"%s\"\<close> (of_semi__term concl)]))
      (String_concat \<open>\<close> (L.map of_semi__command_proof l_apply))
      (of_semi__command_final tactic_last)
      (String_concat \<open> \<close>
        (L.map
          (\<lambda>l_apply_e.
            \<open>%sqed\<close>
              (if l_apply_e = [] then
                 \<open>\<close>
               else
                 \<open>
%s \<close>
                   (String_concat \<open>\<close> (L.map of_semi__command_state l_apply_e))))
          (List.map_filter
            (\<lambda> Command_let _ _ \<Rightarrow> Some [] | Command_have _ _ _ _ \<Rightarrow> Some [] | Command_fix_let _ _ _ l \<Rightarrow> Some l | _ \<Rightarrow> None)
            (rev l_apply)))))"


definition "of_axiomatization _ = (\<lambda> Axiomatization n e \<Rightarrow> \<open>axiomatization where %s:
\"%s\"\<close> (To_string n) (of_semi__term e))"

definition "of_section _ = (\<lambda> Section n section_title \<Rightarrow>
    \<open>%s \<open>%s\<close>\<close>
      (\<open>%ssection\<close> (if n = 0 then \<open>\<close>
                    else if n = 1 then \<open>sub\<close>
                    else \<open>subsub\<close>))
      (To_string section_title))"

definition "of_text _ = (\<lambda> Text s \<Rightarrow> \<open>text \<open>%s\<close>\<close> (To_string s))"

definition "of_ML _ = (\<lambda> SML e \<Rightarrow> \<open>ML \<open>%s\<close>\<close> (of_semi__term' e))"

definition "of_setup _ = (\<lambda> Setup e \<Rightarrow> \<open>setup \<open>%s\<close>\<close> (of_semi__term' e))"

definition "of_thm _ = (\<lambda> Thm thm \<Rightarrow> \<open>thm %s\<close> (of_semi__thm_attribute_l1 thm))"

definition \<open>of_interpretation _ = (\<lambda> Interpretation n loc_n loc_param tac \<Rightarrow>
  \<open>interpretation %s: %s%s
%s\<close> (To_string n)
    (To_string loc_n)
    (String_concat \<open>\<close> (L.map (\<lambda>s. \<open> "%s"\<close> (of_semi__term s)) loc_param))
    (of_semi__command_final tac))\<close>

definition "of_semi__theory env =
 (\<lambda> Theory_datatype dataty \<Rightarrow> of_datatype env dataty
  | Theory_type_synonym ty_synonym \<Rightarrow> of_type_synonym env ty_synonym
  | Theory_type_notation ty_notation \<Rightarrow> of_type_notation env ty_notation
  | Theory_instantiation instantiation_class \<Rightarrow> of_instantiation env instantiation_class
  | Theory_overloading overloading \<Rightarrow> of_overloading env overloading
  | Theory_consts consts_class \<Rightarrow> of_consts env consts_class
  | Theory_definition definition_hol \<Rightarrow> of_definition env definition_hol
  | Theory_lemmas lemmas_simp \<Rightarrow> of_lemmas env lemmas_simp
  | Theory_lemma lemma_by \<Rightarrow> of_lemma env lemma_by
  | Theory_axiomatization axiom \<Rightarrow> of_axiomatization env axiom
  | Theory_section section_title \<Rightarrow> of_section env section_title
  | Theory_text text \<Rightarrow> of_text env text
  | Theory_ML ml \<Rightarrow> of_ML env ml
  | Theory_setup setup \<Rightarrow> of_setup env setup
  | Theory_thm thm \<Rightarrow> of_thm env thm
  | Theory_interpretation thm \<Rightarrow> of_interpretation env thm)"

definition "String_concat_map s f l = String_concat s (L.map f l)"

definition \<open>of_semi__theories env =
 (\<lambda> Theories_one t \<Rightarrow> of_semi__theory env t
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

\<close> (of_semi__theory env)) l))\<close>

end

lemmas [code] =
  \<comment> \<open>def\<close>
  Print.of_datatype_def
  Print.of_type_synonym_def
  Print.of_type_notation_def
  Print.of_instantiation_def
  Print.of_overloading_def
  Print.of_consts_def
  Print.of_definition_def
  Print.of_semi__thm_attribute_aux_gen_def
  Print.of_semi__thm_attribute_aux_gen_where_def
  Print.of_semi__thm_attribute_aux_gen_of_def
  Print.of_semi__thm_attribute_def
  Print.of_semi__thm_def
  Print.of_semi__thm_attribute_l_def
  Print.of_semi__thm_attribute_l1_def
  Print.of_semi__thm_l_def
  Print.of_lemmas_def
  Print.of_semi__attrib_genA_def
  Print.of_semi__attrib_genB_def
  Print.of_semi__attrib_def
  Print.of_semi__attrib1_def
  Print.of_semi__method_simp_def
  Print.of_semi__command_final_def
  Print.of_semi__command_state_def
  Print.of_semi__command_proof_def
  Print.of_lemma_def
  Print.of_axiomatization_def
  Print.of_section_def
  Print.of_text_def
  Print.of_ML_def
  Print.of_setup_def
  Print.of_thm_def
  Print.of_interpretation_def
  Print.of_semi__theory_def
  Print.String_concat_map_def
  Print.of_semi__theories_def

  \<comment> \<open>fun\<close>
  Print.of_semi__typ.simps
  Print.of_semi__term.simps
  Print.of_semi__thm_attribute_aux.simps
  Print.of_semi__method.simps

end
