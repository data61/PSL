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

section \<open>Instances of the Show Class for Standard Types\<close>

theory Old_Show_Instances
imports
  Old_Show_Generator
  HOL.Rat
begin

text \<open>
  For several types, we just derive the show function.
\<close>

derive "show" bool option sum

text \<open>
  The derive-command is not used for @{type unit}, @{type prod}, and numbers: for @{type unit} and
  @{type prod}, we do not want to display ``Unity'' and ``Pair''; for @{type nat}, we do not want to
  display ``Suc (Suc ... Suc (0))''; and neither @{type int} nor @{type rat} are datatypes.
\<close>

instantiation unit :: "show"
begin

definition "shows_prec d (x::unit) = shows_string ''()''"

lemma assoc_unit:
  "shows_prec d (x::unit) r @ s = shows_prec d x (r @ s)"
  by (simp add: shows_prec_unit_def)

standard_shows_list assoc_unit

end

instantiation prod :: ("show", "show") "show"
begin

definition "shows_prec d (p :: 'a \<times> 'b) = shows_paren (shows (fst p) +@+ '','' +#+ shows (snd p))"

lemma assoc_prod:
  "shows_prec d (p::('a::show \<times> 'b::show)) r @ s = shows_prec d p (r @ s)"
  by (cases p) (simp add: shows_prec_prod_def show_defs)

standard_shows_list assoc_prod

end


instantiation nat :: "show"
begin

fun
  digit2string :: "nat \<Rightarrow> string"
where
  "digit2string n = (
    if n = 0 then ''0''
    else if n = 1 then ''1''
    else if n = 2 then ''2''
    else if n = 3 then ''3''
    else if n = 4 then ''4''
    else if n = 5 then ''5''
    else if n = 6 then ''6''
    else if n = 7 then ''7''
    else if n = 8 then ''8''
    else ''9'')"

fun shows_nat :: "nat \<Rightarrow> shows"
where
  "shows_nat (n::nat) = (
    if n < 10 then shows_string (digit2string n)
    else shows_nat (n div 10) \<circ> shows_string (digit2string (n mod 10)))"

definition "shows_prec (d::nat) (n::nat) = shows_nat n"

lemma assoc_nat: "shows_prec d (n::nat) r @ s = shows_prec d n (r @ s)"
proof (induct n arbitrary: r s rule: nat_less_induct)
  case (1 n)
  show ?case
  proof (cases "n < 10")
    case True thus ?thesis unfolding shows_prec_nat_def by simp
  next
    let ?m = "n div 10"
    case False
    hence "?m < n" by simp
    with 1 have "\<And>s t. shows_prec d ?m s @ t = shows_prec d ?m (s @ t)" by simp
    thus ?thesis unfolding shows_prec_nat_def by auto
  qed
qed

standard_shows_list assoc_nat

end

instantiation int :: "show"
begin

definition "shows_prec (d::nat) (i::int) = (
  if i < 0 then shows (CHR ''-'') \<circ> shows (nat (- i))
  else shows (nat i))"

lemma assoc_int:
  "shows_prec d (i::int) r @ s = shows_prec d i (r @ s)"
  by (simp add: shows_prec_int_def)

standard_shows_list assoc_int

end

instantiation rat :: "show"
begin

definition "shows_prec (d::nat) (x::rat) =
  (case quotient_of x of
    Pair den num \<Rightarrow>
    if num = 1 then shows den else shows den \<circ> shows (CHR ''/'') \<circ> shows num)"

lemma assoc_rat:
  "shows_prec d (x::rat) r @ s = shows_prec d x (r @ s)"
  unfolding shows_prec_rat_def by (cases "quotient_of x") auto

standard_shows_list assoc_rat

end

end

