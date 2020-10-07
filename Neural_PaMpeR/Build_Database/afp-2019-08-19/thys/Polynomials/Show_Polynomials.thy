(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann
    License:     LGPL
*)

section \<open>Displaying Polynomials\<close>

theory Show_Polynomials
imports 
  Polynomials
  Show.Show_Instances
begin

fun shows_monom_list :: "('v :: {linorder,show})monom_list \<Rightarrow> string \<Rightarrow> string" where 
  "shows_monom_list [(x,p)] = (if p = 1 then shows x else shows x +@+ shows_string ''^'' +@+ shows p)"
| "shows_monom_list ((x,p) # m) = ((if p = 1 then shows x else shows x +@+ shows_string ''^'' +@+ shows p) +@+ shows_string ''*'' +@+ shows_monom_list m)"
| "shows_monom_list [] = shows_string ''1''"

instantiation monom :: ("{linorder,show}") "show" 
begin

lift_definition shows_prec_monom :: "nat \<Rightarrow> 'a monom \<Rightarrow> shows" is "\<lambda> n. shows_monom_list" .

lemma shows_prec_monom_append [show_law_simps]:
  "shows_prec d (m :: 'a monom) (r @ s) = shows_prec d m r @ s"
proof (transfer fixing: d r s)
  fix m :: "'a monom_list"
  show "shows_monom_list m (r @ s) = shows_monom_list m r @ s"
    by (induct m arbitrary: r s rule: shows_monom_list.induct, auto simp: show_law_simps)
qed

definition "shows_list (ts :: 'a monom list) = showsp_list shows_prec 0 ts"

instance by (standard, auto simp: show_law_simps shows_list_monom_def)
end

fun shows_poly :: "('v :: {show,linorder},'a :: {one,show})poly \<Rightarrow> string \<Rightarrow> string" where 
  "shows_poly [] = shows_string ''0''"
| "shows_poly ((m,c) # p) = ((if c = 1 then shows m else if m = 1 then shows c else shows c +@+ 
     shows_string ''*'' +@+ shows m) +@+ (if p = [] then shows_string [] else shows_string '' + '' +@+ shows_poly p))"
end
