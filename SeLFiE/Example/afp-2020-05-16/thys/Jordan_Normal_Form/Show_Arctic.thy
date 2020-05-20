(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Converting Arctic Numbers to Strings\<close>

text \<open>We just instantiate arctic numbers in the show-class.\<close>

theory Show_Arctic
imports 
  "Abstract-Rewriting.SN_Order_Carrier"
  Show.Show_Instances
begin

instantiation arctic :: "show"
begin

fun shows_arctic :: "arctic \<Rightarrow> shows"
where
  "shows_arctic (Num_arc i) = shows i" |
  "shows_arctic (MinInfty) = shows ''-inf''"

definition "shows_prec (p :: nat) ai = shows_arctic ai"

lemma shows_prec_artic_append [show_law_simps]:
  "shows_prec p (a :: arctic) (r @ s) = shows_prec p a r @ s"
  by (cases a) (auto simp: shows_prec_arctic_def show_law_simps)

definition "shows_list (as :: arctic list) = showsp_list shows_prec 0 as"

instance
  by standard (simp_all add: shows_list_arctic_def show_law_simps)

end

instantiation arctic_delta :: ("show") "show"
begin

fun shows_arctic_delta :: "'a arctic_delta \<Rightarrow> shows"
where
  "shows_arctic_delta (Num_arc_delta i) = shows i" |
  "shows_arctic_delta (MinInfty_delta)  = shows ''-inf''"

definition "shows_prec (d :: nat) ari = shows_arctic_delta ari"

lemma shows_prec_arctic_delta_append [show_law_simps]:
  "shows_prec d (a :: 'a arctic_delta) (r @ s) = shows_prec d a r @ s"
  by (cases a) (auto simp: shows_prec_arctic_delta_def show_law_simps)

definition "shows_list (ps :: 'a arctic_delta list) = showsp_list shows_prec 0 ps"

instance
  by standard (simp_all add: shows_list_arctic_delta_def show_law_simps)

end

end
