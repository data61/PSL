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

section\<open>Isabelle Meta-Model aka. AST definition of Isabelle\<close>

theory  Meta_Isabelle
imports Meta_Pure
        Meta_SML
begin

subsection\<open>Type Definition\<close>

text\<open>The following datatypes beginning with \verb|semi__| represent semi-concrete syntax,
       deliberately not minimal abstract syntax like (Pure) Term,
       this is for example to facilitate the pretty-printing process,
       or for manipulating recursively data-structures through an abstract and typed API.\<close>

datatype semi__typ = Typ_apply semi__typ "semi__typ list"
                   | Typ_apply_bin string \<comment> \<open>binop\<close> semi__typ semi__typ
                   | Typ_apply_paren string \<comment> \<open>left\<close> string \<comment> \<open>right\<close> semi__typ
                   | Typ_base string

datatype "datatype" = Datatype string \<comment> \<open>name\<close>
                               "(string \<comment> \<open>name\<close> \<times> semi__typ list \<comment> \<open>arguments\<close>) list" \<comment> \<open>constructors\<close>

datatype "type_synonym" = Type_synonym string \<comment> \<open>name\<close>
                                       "string list" \<comment> \<open>parametric variables\<close>
                                       semi__typ \<comment> \<open>content\<close>

datatype semi__term = Term_rewrite semi__term \<comment> \<open>left\<close> string \<comment> \<open>symb rewriting\<close> semi__term \<comment> \<open>right\<close>
                    | Term_basic "string list"
                    | Term_annot semi__term semi__typ
                    | Term_bind string \<comment> \<open>symbol\<close> semi__term \<comment> \<open>arg\<close> semi__term
                    | Term_fun_case "semi__term \<comment> \<open>value\<close> option" \<comment> \<open>none: function\<close> "(semi__term \<comment> \<open>pattern\<close> \<times> semi__term \<comment> \<open>to return\<close>) list"
                    | Term_apply semi__term "semi__term list"
                    | Term_paren string \<comment> \<open>left\<close> string \<comment> \<open>right\<close> semi__term
                    | Term_if_then_else semi__term semi__term semi__term
                    | Term_term "string list" \<comment> \<open>simulate a pre-initialized context (de bruijn variables under "lam")\<close>
                                "term" \<comment> \<open>usual continuation of inner syntax term\<close>

datatype "type_notation" = Type_notation string \<comment> \<open>name\<close>
                                         string \<comment> \<open>content\<close>

datatype "instantiation" = Instantiation string \<comment> \<open>name\<close>
                                         string \<comment> \<open>name in definition\<close>
                                         semi__term

datatype "overloading" = Overloading string \<comment> \<open>name consts\<close> semi__term
                                     string \<comment> \<open>name def\<close> semi__term \<comment> \<open>content\<close>

datatype "consts" = Consts string \<comment> \<open>name\<close>
                           semi__typ
                           string \<comment> \<open>expression in 'post' mixfix\<close>

datatype "definition" = Definition semi__term
                      | Definition_where1 string \<comment> \<open>name\<close> "semi__term \<comment> \<open>syntax extension\<close> \<times> nat \<comment> \<open>priority\<close>" semi__term
                      | Definition_where2 string \<comment> \<open>name\<close> semi__term \<comment> \<open>syntax extension\<close> semi__term

datatype semi__thm_attribute = Thm_thm string \<comment> \<open>represents a single thm\<close>
                             | Thm_thms string \<comment> \<open>represents several thms\<close>
                             | Thm_THEN semi__thm_attribute semi__thm_attribute
                             | Thm_simplified semi__thm_attribute semi__thm_attribute
                             | Thm_symmetric semi__thm_attribute
                             | Thm_where semi__thm_attribute "(string \<times> semi__term) list"
                             | Thm_of semi__thm_attribute "semi__term list"
                             | Thm_OF semi__thm_attribute semi__thm_attribute

datatype semi__thm = Thms_single semi__thm_attribute
                   | Thms_mult semi__thm_attribute

type_synonym semi__thm_l = "semi__thm list"

datatype "lemmas" = Lemmas_simp_thm bool \<comment> \<open>True : simp\<close>
                                    string \<comment> \<open>name\<close>
                                    "semi__thm_attribute list"
                  | Lemmas_simp_thms string \<comment> \<open>name\<close>
                                     "string \<comment> \<open>thms\<close> list"

datatype semi__method_simp = Method_simp_only semi__thm_l
                           | Method_simp_add_del_split semi__thm_l \<comment> \<open>add\<close> semi__thm_l \<comment> \<open>del\<close> semi__thm_l \<comment> \<open>split\<close>

datatype semi__method = Method_rule "semi__thm_attribute option"
                      | Method_drule semi__thm_attribute
                      | Method_erule semi__thm_attribute
                      | Method_intro "semi__thm_attribute list"
                      | Method_elim semi__thm_attribute
                      | Method_subst bool \<comment> \<open>asm\<close>
                                     "string \<comment> \<open>nat\<close> list" \<comment> \<open>pos\<close>
                                     semi__thm_attribute
                      | Method_insert semi__thm_l
                      | Method_plus "semi__method list"
                      | Method_option "semi__method list"
                      | Method_or "semi__method list"
                      | Method_one semi__method_simp
                      | Method_all semi__method_simp
                      | Method_auto_simp_add_split semi__thm_l "string list"
                      | Method_rename_tac "string list"
                      | Method_case_tac semi__term
                      | Method_blast "nat option"
                      | Method_clarify
                      | Method_metis "string list" \<comment> \<open>e.g. \<open>no_types\<close> (\<open>override_type_encs\<close>)\<close>
                                     "semi__thm_attribute list"

datatype semi__command_final = Command_done
                             | Command_by "semi__method list"
                             | Command_sorry

datatype semi__command_state = Command_apply_end "semi__method list" \<comment> \<open>\<^theory_text>\<open>apply_end (\<dots>, \<dots>)\<close>\<close>

datatype semi__command_proof = Command_apply "semi__method list" \<comment> \<open>\<^theory_text>\<open>apply (\<dots>, \<dots>)\<close>\<close>
                             | Command_using semi__thm_l \<comment> \<open>\<^theory_text>\<open>using \<dots>\<close>\<close>
                             | Command_unfolding semi__thm_l \<comment> \<open>\<^theory_text>\<open>unfolding \<dots>\<close>\<close>
                             | Command_let semi__term \<comment> \<open>name\<close> semi__term
                             | Command_have string \<comment> \<open>name\<close>
                                            bool \<comment> \<open>true: add \<open>[simp]\<close>\<close>
                                            semi__term
                                            semi__command_final
                             | Command_fix_let "string list"
                                               "(semi__term \<comment> \<open>name\<close> \<times> semi__term) list" \<comment> \<open>let statements\<close> (* TODO merge recursively *)
                                               "( semi__term list \<comment> \<open>\<^theory_text>\<open>show \<dots> \<Longrightarrow> \<dots> \<close>\<close>
                                                \<times> semi__term list \<comment> \<open>\<^theory_text>\<open>when \<dots> \<dots>\<close>\<close>) option" \<comment> \<open>\<open>None \<Rightarrow> ?thesis\<close>\<close>
                                               "semi__command_state list" \<comment> \<open>\<^theory_text>\<open>qed apply_end \<dots>\<close>\<close>

datatype "lemma" = Lemma string \<comment> \<open>name\<close> "semi__term list" \<comment> \<open>specification to prove\<close>
                         "semi__method list list" \<comment> \<open>tactics: \<^theory_text>\<open>apply (\<dots>, \<dots>) apply \<dots>\<close>\<close>
                         semi__command_final
                 | Lemma_assumes string \<comment> \<open>name\<close>
                                 "(string \<comment> \<open>name\<close> \<times> bool \<comment> \<open>true: add \<open>[simp]\<close>\<close> \<times> semi__term) list" \<comment> \<open>specification to prove (assms)\<close>
                                 semi__term \<comment> \<open>specification to prove (conclusion)\<close>
                                 "semi__command_proof list"
                                 semi__command_final

datatype "axiomatization" = Axiomatization string \<comment> \<open>name\<close>
                                           semi__term

datatype "section" = Section nat \<comment> \<open>nesting level\<close>
                             string \<comment> \<open>content\<close>

datatype "text" = Text string

datatype "ML" = SML semi__term'

datatype "setup" = Setup semi__term'

datatype "thm" = Thm "semi__thm_attribute list"

datatype "interpretation" = Interpretation string \<comment> \<open>name\<close>
                                           string \<comment> \<open>locale name\<close>
                                           "semi__term list" \<comment> \<open>locale param\<close>
                                           semi__command_final

datatype semi__theory = Theory_datatype "datatype"
                      | Theory_type_synonym "type_synonym"
                      | Theory_type_notation "type_notation"
                      | Theory_instantiation "instantiation"
                      | Theory_overloading "overloading"
                      | Theory_consts "consts"
                      | Theory_definition "definition"
                      | Theory_lemmas "lemmas"
                      | Theory_lemma "lemma"
                      | Theory_axiomatization "axiomatization"
                      | Theory_section "section"
                      | Theory_text "text"
                      | Theory_ML "ML"
                      | Theory_setup "setup"
                      | Theory_thm "thm"
                      | Theory_interpretation "interpretation"

record semi__locale = 
  HolThyLocale_name :: string
  HolThyLocale_header :: "( (semi__term \<comment> \<open>name\<close> \<times> semi__typ \<comment> \<open>\<^theory_text>\<open>fix\<close> statement\<close>) list
                          \<times> (string \<comment> \<open>name\<close> \<times> semi__term \<comment> \<open>\<^theory_text>\<open>assumes\<close> statement\<close>) option \<comment> \<open>None: no \<^theory_text>\<open>assumes\<close> to generate\<close>) list"

datatype semi__theories = Theories_one semi__theory
                        | Theories_locale semi__locale "semi__theory list \<comment> \<open>positioning comments can occur before and after this group of commands\<close> list"

subsection\<open>Extending the Meta-Model\<close>

locale T
begin
definition "thm = Thm_thm"
definition "thms = Thm_thms"
definition "THEN = Thm_THEN"
definition "simplified = Thm_simplified"
definition "symmetric = Thm_symmetric"
definition "where = Thm_where"
definition "of' = Thm_of"
definition "OF = Thm_OF"
definition "OF_l s l = List.fold (\<lambda>x acc. Thm_OF acc x) l s"
definition "simplified_l s l = List.fold (\<lambda>x acc. Thm_simplified acc x) l s"
end

lemmas [code] =
  \<comment> \<open>def\<close>
  T.thm_def
  T.thms_def
  T.THEN_def
  T.simplified_def
  T.symmetric_def
  T.where_def
  T.of'_def
  T.OF_def
  T.OF_l_def
  T.simplified_l_def

definition "Opt s = Typ_apply (Typ_base \<open>option\<close>) [Typ_base s]"
definition "Raw = Typ_base"
definition "Type_synonym' n = Type_synonym n []"
definition "Type_synonym'' n l f = Type_synonym n l (f l)"
definition "Term_annot' e s = Term_annot e (Typ_base s)"
definition "Term_lambdas s = Term_bind \<open>\<lambda>\<close> (Term_basic s)"
definition "Term_lambda x = Term_lambdas [x]"
definition "Term_lambdas0 = Term_bind \<open>\<lambda>\<close>"
definition "Term_lam x f = Term_lambdas0 (Term_basic [x]) (f x)"
definition "Term_some = Term_paren \<open>\<lfloor>\<close> \<open>\<rfloor>\<close>"
definition "Term_parenthesis \<comment> \<open>mandatory parenthesis\<close> = Term_paren \<open>(\<close> \<open>)\<close>"
definition "Term_warning_parenthesis \<comment> \<open>optional parenthesis that can be removed but a warning will be raised\<close> = Term_parenthesis"
definition "Term_pat b = Term_basic [\<open>?\<close> @@ b]"
definition "Term_And x f = Term_bind \<open>\<And>\<close> (Term_basic [x]) (f x)"
definition "Term_exists x f = Term_bind \<open>\<exists>\<close> (Term_basic [x]) (f x)"
definition "Term_binop = Term_rewrite"
definition "term_binop s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Term_binop x s) xs x)"
definition "term_binop' s l = (case rev l of x # xs \<Rightarrow> List.fold (\<lambda>x. Term_parenthesis o Term_binop x s) xs x)"
definition "Term_set l = (case l of [] \<Rightarrow> Term_basic [\<open>{}\<close>] | _ \<Rightarrow> Term_paren \<open>{\<close> \<open>}\<close> (term_binop \<open>,\<close> l))"
definition "Term_list l = (case l of [] \<Rightarrow> Term_basic [\<open>[]\<close>] | _ \<Rightarrow> Term_paren \<open>[\<close> \<open>]\<close> (term_binop \<open>,\<close> l))"
definition "Term_list' f l = Term_list (L.map f l)"
definition "Term_pair e1 e2 = Term_parenthesis (Term_binop e1 \<open>,\<close> e2)"
definition "Term_pair' l = (case l of [] \<Rightarrow> Term_basic [\<open>()\<close>] | _ \<Rightarrow> Term_paren \<open>(\<close> \<open>)\<close> (term_binop \<open>,\<close> l))"
definition \<open>Term_string s = Term_basic [S.flatten [\<open>"\<close>, s, \<open>"\<close>]]\<close>
definition "Term_applys0 e l = Term_parenthesis (Term_apply e (L.map Term_parenthesis l))"
definition "Term_applys e l = Term_applys0 (Term_parenthesis e) l"
definition "Term_app e = Term_applys0 (Term_basic [e])"
definition "Term_preunary e1 e2 = Term_apply e1 [e2]" \<comment> \<open>no parenthesis and separated with one space\<close>
definition "Term_postunary e1 e2 = Term_apply e1 [e2]" \<comment> \<open>no parenthesis and separated with one space\<close>
definition "Term_case = Term_fun_case o Some"
definition "Term_function = Term_fun_case None"
definition "Term_term' = Term_term []"
definition "Lemmas_simp = Lemmas_simp_thm True"
definition "Lemmas_nosimp = Lemmas_simp_thm False"
definition "Consts_value = \<open>(_)\<close>"
definition "Consts_raw0 s l e o_arg =
       Consts s l (String.replace_integers (\<lambda>n. if n = 0x5F then \<open>'_\<close> else \<degree>n\<degree>) e @@ (case o_arg of
         None \<Rightarrow> \<open>\<close>
       | Some arg \<Rightarrow>
           let ap = \<lambda>s. \<open>'(\<close> @@ s @@ \<open>')\<close> in
           ap (if arg = 0 then
                \<open>\<close>
              else
                Consts_value @@ (S.flatten (L.map (\<lambda>_. \<open>,\<close> @@ Consts_value) (L.upto 2 arg))))))"
definition "Ty_arrow = Typ_apply_bin \<open>\<Rightarrow>\<close>"
definition "Ty_times = Typ_apply_bin \<open>\<times>\<close>"
definition "Ty_arrow' x = Ty_arrow x (Typ_base \<open>_\<close>)"
definition "Ty_paren = Typ_apply_paren \<open>(\<close> \<open>)\<close>"
definition "Consts' s l e = Consts_raw0 s (Ty_arrow (Typ_base \<open>'\<alpha>\<close>) l) e None"
definition "Overloading' n ty = Overloading n (Term_annot (Term_basic [n]) ty)"

locale M
begin
definition "Method_simp_add_del l_a l_d = Method_simp_add_del_split l_a l_d []"
definition "Method_subst_l = Method_subst False"

definition "rule' = Method_rule None"
definition "rule = Method_rule o Some"
definition "drule = Method_drule"
definition "erule = Method_erule"
definition "intro = Method_intro"
definition "elim = Method_elim"
definition "subst_l0 = Method_subst"
definition "subst_l = Method_subst_l"
definition insert where "insert = Method_insert o L.map Thms_single"
definition plus where "plus = Method_plus"
definition "option = Method_option"
definition "or = Method_or"
definition "meth_gen_simp = Method_simp_add_del [] []"
definition "meth_gen_simp_add2 l1 l2 = Method_simp_add_del (L.flatten [ L.map Thms_mult l1
                                                    , L.map (Thms_single o Thm_thm) l2])
                                           []"
definition "meth_gen_simp_add_del l1 l2 = Method_simp_add_del (L.map (Thms_single o Thm_thm) l1)
                                              (L.map (Thms_single o Thm_thm) l2)"
definition "meth_gen_simp_add_del_split l1 l2 l3 = Method_simp_add_del_split (L.map Thms_single l1)
                                                             (L.map Thms_single l2)
                                                             (L.map Thms_single l3)"
definition "meth_gen_simp_add_split l1 l2 = Method_simp_add_del_split (L.map Thms_single l1)
                                                      []
                                                      (L.map Thms_single l2)"
definition "meth_gen_simp_only l = Method_simp_only (L.map Thms_single l)"
definition "meth_gen_simp_only' l = Method_simp_only (L.map Thms_mult l)"
definition "meth_gen_simp_add0 l = Method_simp_add_del (L.map Thms_single l) []"
definition "simp = Method_one meth_gen_simp"
definition "simp_add2 l1 l2 = Method_one (meth_gen_simp_add2 l1 l2)"
definition "simp_add_del l1 l2 = Method_one (meth_gen_simp_add_del l1 l2)"
definition "simp_add_del_split l1 l2 l3 = Method_one (meth_gen_simp_add_del_split l1 l2 l3)"
definition "simp_add_split l1 l2 = Method_one (meth_gen_simp_add_split l1 l2)"
definition "simp_only l = Method_one (meth_gen_simp_only l)"
definition "simp_only' l = Method_one (meth_gen_simp_only' l)"
definition "simp_add0 l = Method_one (meth_gen_simp_add0 l)"
definition "simp_add = simp_add2 []"
definition "simp_all = Method_all meth_gen_simp"
definition "simp_all_add l = Method_all (meth_gen_simp_add2 [] l)"
definition "simp_all_only l = Method_all (meth_gen_simp_only l)"
definition "simp_all_only' l = Method_all (meth_gen_simp_only' l)"
definition "auto_simp_add2 l1 l2 = Method_auto_simp_add_split (L.flatten [ L.map Thms_mult l1
                                                                , L.map (Thms_single o Thm_thm) l2]) []"
definition "auto_simp_add_split l = Method_auto_simp_add_split (L.map Thms_single l)"
definition "rename_tac = Method_rename_tac"
definition "case_tac = Method_case_tac"
definition "blast = Method_blast"
definition "clarify = Method_clarify"
definition "metis = Method_metis []"
definition "metis0 = Method_metis"

definition "subst_asm b = subst_l0 b [\<open>0\<close>]"
definition "subst = subst_l [\<open>0\<close>]"
definition "auto_simp_add = auto_simp_add2 []"
definition "auto = auto_simp_add []"
end

lemmas [code] =
  \<comment> \<open>def\<close>
  M.Method_simp_add_del_def
  M.Method_subst_l_def
  M.rule'_def
  M.rule_def
  M.drule_def
  M.erule_def
  M.intro_def
  M.elim_def
  M.subst_l0_def
  M.subst_l_def
  M.insert_def
  M.plus_def
  M.option_def
  M.or_def
  M.meth_gen_simp_def
  M.meth_gen_simp_add2_def
  M.meth_gen_simp_add_del_def
  M.meth_gen_simp_add_del_split_def
  M.meth_gen_simp_add_split_def
  M.meth_gen_simp_only_def
  M.meth_gen_simp_only'_def
  M.meth_gen_simp_add0_def
  M.simp_def
  M.simp_add2_def
  M.simp_add_del_def
  M.simp_add_del_split_def
  M.simp_add_split_def
  M.simp_only_def
  M.simp_only'_def
  M.simp_add0_def
  M.simp_add_def
  M.simp_all_def
  M.simp_all_add_def
  M.simp_all_only_def
  M.simp_all_only'_def
  M.auto_simp_add2_def
  M.auto_simp_add_split_def
  M.rename_tac_def
  M.case_tac_def
  M.blast_def
  M.clarify_def
  M.metis_def
  M.metis0_def
  M.subst_asm_def
  M.subst_def
  M.auto_simp_add_def
  M.auto_def

definition "ty_arrow l = (case rev l of x # xs \<Rightarrow> List.fold Ty_arrow xs x)"

locale C 
begin
definition "done = Command_done"
definition "by = Command_by"
definition "sorry = Command_sorry"
definition "apply_end = Command_apply_end"
definition "apply = Command_apply"
definition "using = Command_using o L.map Thms_single"
definition "unfolding = Command_unfolding o L.map Thms_single"
definition "let' = Command_let"
definition "fix_let = Command_fix_let"
definition "fix l = Command_fix_let l [] None []"
definition "have n = Command_have n False"
definition "have0 = Command_have"
end

lemmas [code] =
  \<comment> \<open>def\<close>
  C.done_def
  C.by_def
  C.sorry_def
  C.apply_end_def
  C.apply_def
  C.using_def
  C.unfolding_def
  C.let'_def
  C.fix_let_def
  C.fix_def
  C.have_def
  C.have0_def

fun cross_abs_aux where
   "cross_abs_aux f l x = (\<lambda> (Suc n, Abs s _ t) \<Rightarrow> f s (cross_abs_aux f (s # l) (n, t))
                         | (_, e) \<Rightarrow> Term_term l e)
                         x"

definition "cross_abs f n l = cross_abs_aux f [] (n, l)"

subsection\<open>Operations of Fold, Map, ..., on the Meta-Model\<close>

definition "map_lemma f = (\<lambda> Theory_lemma x \<Rightarrow> Theory_lemma (f x)
                           | x \<Rightarrow> x)"

end
