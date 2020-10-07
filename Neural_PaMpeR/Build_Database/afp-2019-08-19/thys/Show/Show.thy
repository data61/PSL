(*  Title:       Show
    Author:      Christian Sternagel <c.sternagel@gmail.com>
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  René Thiemann <rene.thiemann@uibk.ac.at>
*)

section \<open>Converting Arbitrary Values to Readable Strings\<close>

text \<open>
  A type class similar to Haskell's \texttt{Show} class, allowing for constant-time concatenation of
  strings using function composition.
\<close>

theory Show
imports
  Main
  Deriving.Generator_Aux
  Deriving.Derive_Manager
begin

type_synonym
  "shows" = "string \<Rightarrow> string"

\<comment> \<open>show-functions with precedence\<close>
type_synonym
  'a showsp = "nat \<Rightarrow> 'a \<Rightarrow> shows"


subsection \<open>The Show-Law\<close>

text \<open>
  The "show law", @{term "shows_prec p x (r @ s) = shows_prec p x r @ s"}, states that
  show-functions do not temper with or depend on output produced so far.
\<close>

named_theorems show_law_simps \<open>simplification rules for proving the "show law"\<close>
named_theorems show_law_intros \<open>introduction rules for proving the "show law"\<close>

definition show_law :: "'a showsp \<Rightarrow> 'a \<Rightarrow> bool"
where
  "show_law s x \<longleftrightarrow> (\<forall>p y z. s p x (y @ z) = s p x y @ z)"

lemma show_lawI:
  "(\<And>p y z. s p x (y @ z) = s p x y @ z) \<Longrightarrow> show_law s x"
  by (simp add: show_law_def)

lemma show_lawE:
  "show_law s x \<Longrightarrow> (s p x (y @ z) = s p x y @ z \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto simp: show_law_def)

lemma show_lawD:
  "show_law s x \<Longrightarrow> s p x (y @ z) = s p x y @ z"
  by (blast elim: show_lawE)

class "show" =
  fixes shows_prec :: "'a showsp"
    and shows_list :: "'a list \<Rightarrow> shows"
  assumes shows_prec_append [show_law_simps]: "shows_prec p x (r @ s) = shows_prec p x r @ s" and
    shows_list_append [show_law_simps]: "shows_list xs (r @ s) = shows_list xs r @ s"
begin

abbreviation "shows x \<equiv> shows_prec 0 x"
abbreviation "show x \<equiv> shows x ''''"

end

text \<open>Convert a string to a show-function that simply prepends the string unchanged.\<close>
definition shows_string :: "string \<Rightarrow> shows"
where
  "shows_string = (@)"

lemma shows_string_append [show_law_simps]:
  "shows_string x (r @ s) = shows_string x r @ s"
  by (simp add: shows_string_def)

fun shows_sep :: "('a \<Rightarrow> shows) \<Rightarrow> shows \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_sep s sep [] = shows_string ''''" |
  "shows_sep s sep [x] = s x" |
  "shows_sep s sep (x#xs) = s x o sep o shows_sep s sep xs"

lemma shows_sep_append [show_law_simps]:
  assumes "\<And>r s. \<forall>x \<in> set xs. showsx x (r @ s) = showsx x r @ s"
    and "\<And>r s. sep (r @ s) = sep r @ s"
  shows "shows_sep showsx sep xs (r @ s) = shows_sep showsx sep xs r @ s"
using assms
proof (induct xs)
  case (Cons x xs) then show ?case by (cases xs) (simp_all)
qed (simp add: show_law_simps)

lemma shows_sep_map:
  "shows_sep f sep (map g xs) = shows_sep (f o g) sep xs"
  by (induct xs) (simp, case_tac xs, simp_all)

definition
  shows_list_gen :: "('a \<Rightarrow> shows) \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> 'a list \<Rightarrow> shows"
where
  "shows_list_gen showsx e l s r xs =
    (if xs = [] then shows_string e
    else shows_string l o shows_sep showsx (shows_string s) xs o shows_string r)"

lemma shows_list_gen_append [show_law_simps]:
  assumes "\<And>r s. \<forall>x\<in>set xs. showsx x (r @ s) = showsx x r @ s"
  shows "shows_list_gen showsx e l sep r xs (s @ t) = shows_list_gen showsx e l sep r xs s @ t"
  using assms by (cases xs) (simp_all add: shows_list_gen_def show_law_simps)

lemma shows_list_gen_map:
  "shows_list_gen f e l sep r (map g xs) = shows_list_gen (f o g) e l sep r xs"
  by (simp_all add: shows_list_gen_def shows_sep_map)

definition pshowsp_list :: "nat \<Rightarrow> shows list \<Rightarrow> shows"
where
  "pshowsp_list p xs = shows_list_gen id ''[]'' ''['' '', '' '']'' xs"

definition showsp_list :: "'a showsp \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> shows"
where
  [code del]: "showsp_list s p = pshowsp_list p o map (s 0)"

lemma showsp_list_code [code]:
  "showsp_list s p xs = shows_list_gen (s 0) ''[]'' ''['' '', '' '']'' xs"
  by (simp add: showsp_list_def pshowsp_list_def shows_list_gen_map)

lemma show_law_list [show_law_intros]:
  "(\<And>x. x \<in> set xs \<Longrightarrow> show_law s x) \<Longrightarrow> show_law (showsp_list s) xs"
  by (simp add: show_law_def showsp_list_code show_law_simps)

lemma showsp_list_append [show_law_simps]:
  "(\<And>p y z. \<forall>x \<in> set xs. s p x (y @ z) = s p x y @ z) \<Longrightarrow>
    showsp_list s p xs (y @ z) = showsp_list s p xs y @ z"
  by (simp add: show_law_simps showsp_list_def pshowsp_list_def)


subsection \<open>Show-Functions for Characters and Strings\<close>

instantiation char :: "show"
begin

definition "shows_prec p (c::char) = (#) c"
definition "shows_list (cs::string) = shows_string cs"
instance
  by standard (simp_all add: shows_prec_char_def shows_list_char_def show_law_simps)

end

definition "shows_nl = shows (CHR ''\<newline>'')"
definition "shows_space = shows (CHR '' '')"
definition "shows_paren s = shows (CHR ''('') o s o shows (CHR '')'')"
definition "shows_quote s = shows (CHR 0x27) o s o shows (CHR 0x27)"
abbreviation "apply_if b s \<equiv> (if b then s else id)" \<comment> \<open>conditional function application\<close>
text \<open>Parenthesize only if precedence is greater than @{term "0::nat"}.\<close>
definition "shows_pl (p::nat) = apply_if (p > 0) (shows (CHR ''(''))"
definition "shows_pr (p::nat) = apply_if (p > 0) (shows (CHR '')''))"

lemma
  shows_nl_append [show_law_simps]: "shows_nl (x @ y) = shows_nl x @ y" and
  shows_space_append [show_law_simps]: "shows_space (x @ y) = shows_space x @ y" and
  shows_paren_append [show_law_simps]:
    "(\<And>x y. s (x @ y) = s x @ y) \<Longrightarrow> shows_paren s (x @ y) = shows_paren s x @ y" and
  shows_quote_append [show_law_simps]:
    "(\<And>x y. s (x @ y) = s x @ y) \<Longrightarrow> shows_quote s (x @ y) = shows_quote s x @ y" and
  shows_pl_append [show_law_simps]: "shows_pl p (x @ y) = shows_pl p x @ y" and
  shows_pr_append [show_law_simps]: "shows_pr p (x @ y) = shows_pr p x @ y"
  by (simp_all add: shows_nl_def shows_space_def shows_paren_def shows_quote_def shows_pl_def shows_pr_def show_law_simps)

lemma o_append:
  "(\<And>x y. f (x @ y) = f x @ y) \<Longrightarrow> g (x @ y) = g x @ y \<Longrightarrow> (f o g) (x @ y) = (f o g) x @ y"
  by simp

ML_file \<open>show_generator.ML\<close>

local_setup \<open>
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name "list"} 0
    @{term "pshowsp_list"}
    @{term "showsp_list"} (SOME @{thm showsp_list_def})
    @{term "map"} (SOME @{thm list.map_comp}) [true] @{thm show_law_list}
\<close>

instantiation list :: ("show") "show"
begin

definition "shows_prec (p :: nat) (xs :: 'a list) = shows_list xs"
definition "shows_list (xss :: 'a list list) = showsp_list shows_prec 0 xss"

instance
  by standard (simp_all add: show_law_simps shows_prec_list_def shows_list_list_def)

end

definition shows_lines :: "'a::show list \<Rightarrow> shows"
where
  "shows_lines = shows_sep shows shows_nl"

definition shows_many :: "'a::show list \<Rightarrow> shows"
where
  "shows_many = shows_sep shows id"

definition shows_words :: "'a::show list \<Rightarrow> shows"
where
  "shows_words = shows_sep shows shows_space"

lemma shows_lines_append [show_law_simps]:
  "shows_lines xs (r @ s) = shows_lines xs r @ s"
  by (simp add: shows_lines_def show_law_simps)

lemma shows_many_append [show_law_simps]:
  "shows_many xs (r @ s) = shows_many xs r @ s"
  by (simp add: shows_many_def show_law_simps)

lemma shows_words_append [show_law_simps]:
  "shows_words xs (r @ s) = shows_words xs r @ s"
  by (simp add: shows_words_def show_law_simps)

lemma shows_foldr_append [show_law_simps]:
  assumes "\<And>r s. \<forall>x \<in> set xs. showx x (r @ s) = showx x r @ s"
  shows "foldr showx xs (r @ s) = foldr showx xs r @ s"
  using assms by (induct xs) (simp_all)

lemma shows_sep_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "shows_sep f sep xs = shows_sep g sep ys"
using assms
proof (induct ys arbitrary: xs)
  case (Cons y ys)
  then show ?case by (cases ys) simp_all
qed simp

lemma shows_list_gen_cong [fundef_cong]:
  assumes "xs = ys" and "\<And>x. x \<in> set ys \<Longrightarrow> f x = g x"
  shows "shows_list_gen f e l sep r xs = shows_list_gen g e l sep r ys"
  using shows_sep_cong [of xs ys f g] assms by (cases xs) (auto simp: shows_list_gen_def)

lemma showsp_list_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> p = q \<Longrightarrow>
    (\<And>p x. x \<in> set ys \<Longrightarrow> f p x = g p x) \<Longrightarrow> showsp_list f p xs = showsp_list g q ys"
  by (simp add: showsp_list_code cong: shows_list_gen_cong)

abbreviation (input) shows_cons :: "string \<Rightarrow> shows \<Rightarrow> shows" (infixr "+#+" 10)
where
  "s +#+ p \<equiv> shows_string s \<circ> p"

abbreviation (input) shows_append :: "shows \<Rightarrow> shows \<Rightarrow> shows" (infixr "+@+" 10)
where
  "s +@+ p \<equiv> s \<circ> p"

instantiation String.literal :: "show"
begin

definition shows_prec_literal :: "nat \<Rightarrow> String.literal \<Rightarrow> string \<Rightarrow> string"
  where "shows_prec p s = shows_string (String.explode s)"

definition shows_list_literal :: "String.literal list \<Rightarrow> string \<Rightarrow> string"
  where "shows_list ss = shows_string (concat (map String.explode ss))"

lemma shows_list_literal_code [code]:
  "shows_list = foldr (\<lambda>s. shows_string (String.explode s))"
proof
  fix ss
  show "shows_list ss = foldr (\<lambda>s. shows_string (String.explode s)) ss"
    by (induct ss) (simp_all add: shows_list_literal_def shows_string_def)
qed

instance by standard
  (simp_all add: shows_prec_literal_def shows_list_literal_def shows_string_def)

end

text \<open>
  Don't use Haskell's existing "Show" class for code-generation, since it is not compatible to the
  formalized class.
\<close>
code_reserved Haskell "Show"

end
