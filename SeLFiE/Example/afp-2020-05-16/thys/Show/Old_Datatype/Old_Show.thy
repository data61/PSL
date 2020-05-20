(*
Copyright 2009-2014 Christian Sternagel, René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Converting Values to Readable Strings\<close>

theory Old_Show
imports Main
keywords "standard_shows_list" :: thy_decl
begin

text \<open>
  A type class similar to Haskell's \texttt{Show} class, allowing for constant-time concatenation of
  @{type string}s using function composition.
\<close>

type_synonym
  "shows" = "string \<Rightarrow> string"

text \<open>
  Convert a string to a show-function that simply prepends the string unchanged.
\<close>
definition shows_string :: "string \<Rightarrow> shows"
where
  "shows_string = (@)"

class "show" =
  fixes shows_prec :: "nat \<Rightarrow> 'a \<Rightarrow> shows"
    and shows_list :: "'a list \<Rightarrow> shows"
  assumes assoc [simp]:
    "shows_prec d x r @ s = shows_prec d x (r @ s)"
    "shows_list xs r @ s = shows_list xs (r @ s)"
begin

abbreviation "shows" :: "'a \<Rightarrow> shows"
where
  "shows x \<equiv> shows_prec 0 x"

abbreviation "show" :: "'a \<Rightarrow> string"
where
  "show x \<equiv> shows x ''''"

end

abbreviation shows_cons :: "string \<Rightarrow> shows \<Rightarrow> shows" (infixr "+#+" 10)
where
  "s +#+ p \<equiv> shows_string s \<circ> p"

abbreviation (input) shows_append :: "shows \<Rightarrow> shows \<Rightarrow> shows" (infixr "+@+" 10)
where
  "s +@+ p \<equiv> s \<circ> p"

definition shows_between :: "shows \<Rightarrow> shows \<Rightarrow> shows \<Rightarrow> shows"
where
  "shows_between l p r = (l +@+ p +@+ r)"

fun shows_sep :: "('a \<Rightarrow> shows) \<Rightarrow> shows \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_sep s sep [] = shows_string ''''" |
  "shows_sep s sep [x] = s x" |
  "shows_sep s sep (x#xs) = (s x +@+ sep +@+ shows_sep s sep xs)"

lemma shows_sep_assoc [simp]:
  assumes "\<And>r s. \<forall>x\<in>set xs. elt x r @ s = elt x (r @ s)"
    and "\<And>r s. sep r @ s = sep (r @ s)"
  shows "shows_sep elt sep xs r @ s = shows_sep elt sep xs (r @ s)"
using assms
proof (induct xs)
  case (Cons x xs) then show ?case by (cases xs) (simp_all)
qed (simp add: shows_string_def)

lemma shows_string_assoc [simp]:
  "shows_string x r @ s = shows_string x (r @ s)"
  by (simp add: shows_string_def)

lemma shows_between_assoc [simp]:
  assumes "\<And>s t. l s @ t = l (s @ t)"
    and "\<And>s t. m s @ t = m (s @ t)"
    and "\<And>s t. r s @ t = r (s @ t)"
  shows "shows_between l m r s @ t = shows_between l m r (s @ t)"
  using assms by (simp add: shows_between_def)

definition
  shows_list_gen :: "('a \<Rightarrow> shows) \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_list_gen elt e l s r xs = (
    if xs = [] then shows_string e
    else shows_between (shows_string l) (shows_sep elt (shows_string s) xs) (shows_string r))"

lemma shows_list_gen_assoc [simp]:
  assumes "\<And>r s. \<forall>x\<in>set xs. elt x r @ s = elt x (r @ s)"
  shows "shows_list_gen elt e l sep r xs s @ t = shows_list_gen elt e l sep r xs (s @ t)"
  using assms by (cases xs) (simp_all add: shows_list_gen_def)

definition shows_list_aux :: "('a \<Rightarrow> shows) \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_list_aux s xs = shows_list_gen s ''[]'' ''['' '', '' '']'' xs"

lemma assoc_elt:
  "\<forall>x\<in>set xs. shows (x::'a::show) r @ s = shows x (r @ s)"
  by simp

lemma shows_list_aux_assoc:
  assumes "\<And>r s. \<forall>x\<in>set xs. elt x r @ s = elt x (r @ s)"
  shows "shows_list_aux elt xs r @ s = shows_list_aux elt xs (r @ s)"
  using assms by (simp add: shows_list_aux_def)

ML \<open>
(* FIXME export proper ML interfaces: define_shows_list, define_shows_list_cmd *)
let 
  fun define_shows_list assoc_thm_ref lthy =
    let
      val assoc_thm = singleton (Attrib.eval_thms lthy) assoc_thm_ref
      fun get_base_type thm =
        let
           val lhs = thm |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst
           fun get_ty (Const (@{const_name append}, _) $
             (Const (@{const_name shows_prec}, _) $ _ $ x $ _) $ _) = dest_Var x |> snd
             | get_ty t = raise TERM ("Expecting associativity lemma for 'shows_prec'", [t])
        in get_ty lhs end
      val base_ty = get_base_type assoc_thm
     
      val list_ty = Type (@{type_name "list"}, [base_ty])
      val shows_ty = @{typ "shows"}
      val shows = Abs ("x", base_ty, Const (@{const_name "shows_prec"},
        @{typ nat} --> base_ty --> shows_ty) $ @{term "0 :: nat"} $ Bound 0)
      val shows_list_aux = Const (@{const_name shows_list_aux},
        (base_ty --> shows_ty) --> list_ty --> shows_ty)
      val shows_list = Const (@{const_name shows_list}, list_ty --> shows_ty)
      val rhs = shows_list_aux $ shows
      val shows_list_eq = Logic.mk_equals (shows_list, rhs)
     
      val ((c, _), rhs) = Syntax.check_term lthy shows_list_eq |> Logic.dest_equals |>> dest_Free;
      val ((_, (_, def_thm')), lthy') =
        Local_Theory.define
          ((Binding.name c, NoSyn), ((Binding.name (c ^ "_def"), @{attributes [code]}), rhs))
          lthy
      val def_thm =
        Proof_Context.theory_of lthy'
        |> Proof_Context.init_global
        |> Proof_Context.export lthy'
        |> (fn x => singleton x def_thm')

      val lthy'' = Class.prove_instantiation_instance (fn ctxt =>
        Class.intro_classes_tac ctxt []
        THEN resolve_tac ctxt [assoc_thm] 1
        THEN unfold_tac ctxt [def_thm] 
        THEN resolve_tac ctxt @{thms shows_list_aux_assoc} 1
        THEN resolve_tac ctxt @{thms ballI} 1
        THEN resolve_tac ctxt [assoc_thm] 1
        ) lthy'
    in lthy'' end
in
  Outer_Syntax.local_theory @{command_keyword standard_shows_list}
    "use standard way to extend shows to shows_list, requires associativity lemma as parameter"
    (*standard way: "shows_list = shows_list_aux shows"*)
    (Parse.thm >> define_shows_list)
end
\<close>

instantiation char :: "show"
begin

definition "shows_prec d (c::char) = (#) c"

definition "shows_list (cs::string) = shows_string cs"

instance
  by (intro_classes,unfold shows_prec_char_def shows_list_char_def shows_string_def, simp) auto

end

instantiation list :: ("show") "show"
begin

definition "shows_prec d (l::'a::show list) = shows_list l"

lemma assoc_list:
  "shows_prec d (x::'a::show list) r @ s = shows_prec d x (r @ s)"
  by (simp add: shows_prec_list_def)

standard_shows_list assoc_list

end

definition "shows_nl = shows ''\<newline>''"

definition "shows_space = shows (CHR '' '')"

definition shows_paren :: "shows \<Rightarrow> shows"
where
  "shows_paren p = (shows (CHR ''('') +@+ p +@+ shows (CHR '')''))"

lemmas show_defs =
  shows_prec_char_def shows_nl_def shows_space_def
  shows_string_def shows_between_def shows_paren_def

definition shows_lines :: "'a::show list \<Rightarrow> shows"
where
  "shows_lines = shows_sep shows shows_nl"

definition shows_many :: "'a::show list \<Rightarrow> shows"
where
  "shows_many = shows_sep shows id"

definition shows_words :: "'a::show list \<Rightarrow> shows"
where
  "shows_words = shows_sep shows shows_space"

fun shows_map :: "('a \<Rightarrow> shows) \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_map s [] = id" |
  "shows_map s (x # xs) = (s x +@+ shows_map s xs)"

lemma shows_nl_assoc [simp]:
  "shows_nl r @ s = shows_nl (r @ s)"
  by (simp add: show_defs)

lemma shows_id_assoc [simp]:
  "id r @ s = id (r @ s)" by simp

lemma shows_space_assoc [simp]:
  "shows_space r @ s = shows_space (r @ s)"
  by (simp add: show_defs)

lemma shows_lines_assoc [simp]:
  "shows_lines xs r @ s = shows_lines xs (r @ s)"
  by (simp add: shows_lines_def)

lemma shows_many_assoc [simp]:
  "shows_many xs r @ s = shows_many xs (r @ s)"
  by (simp add: shows_many_def)

lemma shows_words_assoc [simp]:
  "shows_words xs r @ s = shows_words xs (r @ s)"
  by (simp add: shows_words_def)

lemma shows_map_assoc [simp]:
  assumes "\<And>r s.\<forall>x\<in>set xs. elt x r @ s = elt x (r @ s)"
  shows "shows_map elt xs r @ s = shows_map elt xs (r @ s)"
  using assms by (induct xs) auto

fun shows_concat :: "shows list \<Rightarrow> shows"
where
  "shows_concat [] = id" |
  "shows_concat (s # ss) = (s +@+ shows_concat ss)"

lemma shows_map_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "shows_map f xs = shows_map g ys"
  using assms by (induct xs arbitrary: ys) auto

lemma shows_sep_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "shows_sep f sep xs = shows_sep g sep ys"
  unfolding assms(1) using assms(2)
proof (induct ys)
  case (Cons y ys)
  thus ?case by (cases ys) auto
qed auto

lemma shows_list_gen_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "shows_list_gen f e l sep r xs = shows_list_gen g e l sep r ys"
  using shows_sep_cong [of xs ys f g] assms by (cases xs) (auto simp: shows_list_gen_def)

definition shows_quote :: "shows \<Rightarrow> shows"
where
  "shows_quote s = shows_between (shows (CHR 0x27)) s (shows (CHR 0x27))"

text \<open>
  Don't use Haskell's existing "Show" class for code-generation, since it is not compatible to the
  formalized class.
\<close>
code_reserved Haskell "Show"

end
