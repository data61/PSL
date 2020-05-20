(*  Title:       Show
    Author:      Christian Sternagel <c.sternagel@gmail.com>
    Author:      René Thiemann <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel <c.sternagel@gmail.com>
    Maintainer:  René Thiemann <rene.thiemann@uibk.ac.at>
*)

section \<open>Instances of the Show Class for Standard Types\<close>

theory Show_Instances
imports
  Show
  HOL.Rat
begin

definition showsp_unit :: "unit showsp"
where
  "showsp_unit p x = shows_string ''()''"

lemma show_law_unit [show_law_intros]:
  "show_law showsp_unit x"
  by (rule show_lawI) (simp add: showsp_unit_def show_law_simps)

abbreviation showsp_char :: "char showsp"
where
  "showsp_char \<equiv> shows_prec"

lemma show_law_char [show_law_intros]:
  "show_law showsp_char x"
  by (rule show_lawI) (simp add: show_law_simps)

primrec showsp_bool :: "bool showsp"
where
  "showsp_bool p True = shows_string ''True''" |
  "showsp_bool p False = shows_string ''False''"

lemma show_law_bool [show_law_intros]:
  "show_law showsp_bool x"
  by (rule show_lawI, cases x) (simp_all add: show_law_simps)

primrec pshowsp_prod :: "(shows \<times> shows) showsp"
where
  "pshowsp_prod p (x, y) = shows_string ''('' o x o shows_string '', '' o y o shows_string '')''"

(*NOTE: in order to be compatible with automatically generated show funtions,
show-arguments of "map"-functions need to get precedence 1 (which may lead to
redundant parentheses in the output, but seems unavoidable in the current setup,
i.e., pshowsp via primrec followed by defining showsp via pshowsp composed with map).*)
definition showsp_prod :: "'a showsp \<Rightarrow> 'b showsp \<Rightarrow> ('a \<times> 'b) showsp"
where
  [code del]: "showsp_prod s1 s2 p = pshowsp_prod p o map_prod (s1 1) (s2 1)"

lemma showsp_prod_simps [simp, code]:
  "showsp_prod s1 s2 p (x, y) =
    shows_string ''('' o s1 1 x o shows_string '', '' o s2 1 y o shows_string '')''"
  by (simp add: showsp_prod_def)

lemma show_law_prod [show_law_intros]:
  "(\<And>x. x \<in> Basic_BNFs.fsts y \<Longrightarrow> show_law s1 x) \<Longrightarrow>
   (\<And>x. x \<in> Basic_BNFs.snds y \<Longrightarrow> show_law s2 x) \<Longrightarrow>
    show_law (showsp_prod s1 s2) y"
proof (induct y)
  case (Pair x y)
  note * = Pair [unfolded prod_set_simps]
  show ?case
    by (rule show_lawI)
       (auto simp del: o_apply intro!: o_append intro: show_lawD * simp: show_law_simps)
qed

fun string_of_digit :: "nat \<Rightarrow> string"
where
  "string_of_digit n =
    (if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

fun showsp_nat :: "nat showsp"
where
  "showsp_nat p n =
    (if n < 10 then shows_string (string_of_digit n)
    else showsp_nat p (n div 10) o shows_string (string_of_digit (n mod 10)))"
declare showsp_nat.simps [simp del]

lemma show_law_nat [show_law_intros]:
  "show_law showsp_nat n"
  by (rule show_lawI, induct n rule: nat_less_induct) (simp add: show_law_simps showsp_nat.simps)

lemma showsp_nat_append [show_law_simps]:
  "showsp_nat p n (x @ y) = showsp_nat p n x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_int :: "int showsp"
where
  "showsp_int p i =
    (if i < 0 then shows_string ''-'' o showsp_nat p (nat (- i)) else showsp_nat p (nat i))"

lemma show_law_int [show_law_intros]:
  "show_law showsp_int i"
  by (rule show_lawI, cases "i < 0") (simp_all add: showsp_int_def show_law_simps)

lemma showsp_int_append [show_law_simps]:
  "showsp_int p i (x @ y) = showsp_int p i x @ y"
  by (intro show_lawD show_law_intros)

definition showsp_rat :: "rat showsp"
where
  "showsp_rat p x =
    (case quotient_of x of (d, n) \<Rightarrow>
      if n = 1 then showsp_int p d else showsp_int p d o shows_string ''/'' o showsp_int p n)"

lemma show_law_rat [show_law_intros]:
  "show_law showsp_rat r"
  by (rule show_lawI, cases "quotient_of r") (simp add: showsp_rat_def show_law_simps)

lemma showsp_rat_append [show_law_simps]:
  "showsp_rat p r (x @ y) = showsp_rat p r x @ y"
  by (intro show_lawD show_law_intros)

text \<open>
  Automatic show functions are not used for @{type unit}, @{type prod}, and numbers:
  for @{type unit} and @{type prod}, we do not want to display @{term "''Unity''"} and
  @{term "''Pair''"}; for @{type nat}, we do not want to display
  @{term "''Suc (Suc (... (Suc 0) ...))''"}; and neither @{type int}
  nor @{type rat} are datatypes.
\<close>

local_setup \<open>
  Show_Generator.register_foreign_partial_and_full_showsp @{type_name prod} 0
       @{term "pshowsp_prod"}
       @{term "showsp_prod"} (SOME @{thm showsp_prod_def})
       @{term "map_prod"} (SOME @{thm prod.map_comp}) [true, true]
       @{thm show_law_prod}
  #> Show_Generator.register_foreign_showsp @{typ unit} @{term "showsp_unit"} @{thm show_law_unit}
  #> Show_Generator.register_foreign_showsp @{typ bool} @{term "showsp_bool"} @{thm show_law_bool}
  #> Show_Generator.register_foreign_showsp @{typ char} @{term "showsp_char"} @{thm show_law_char}
  #> Show_Generator.register_foreign_showsp @{typ nat} @{term "showsp_nat"} @{thm show_law_nat}
  #> Show_Generator.register_foreign_showsp @{typ int} @{term "showsp_int"} @{thm show_law_int}
  #> Show_Generator.register_foreign_showsp @{typ rat} @{term "showsp_rat"} @{thm show_law_rat}
\<close>

derive "show" option sum prod unit bool nat int rat

export_code
  "shows_prec :: 'a::show option showsp"
  "shows_prec :: ('a::show, 'b::show) sum showsp"
  "shows_prec :: ('a::show \<times> 'b::show) showsp"
  "shows_prec :: unit showsp"
  "shows_prec :: char showsp"
  "shows_prec :: bool showsp"
  "shows_prec :: nat showsp"
  "shows_prec :: int showsp"
  "shows_prec :: rat showsp"
  checking

end

