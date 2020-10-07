(* Author: Dmitriy Traytel *)

section \<open>Normalization of WS1S Formulas\<close>

(*<*)
theory WS1S_Normalization
imports WS1S
begin
(*>*)

fun nNot where
  "nNot (FNot \<phi>) = \<phi>"
| "nNot (FAnd \<phi>1 \<phi>2) = FOr (nNot \<phi>1) (nNot \<phi>2)"
| "nNot (FOr \<phi>1 \<phi>2) = FAnd (nNot \<phi>1) (nNot \<phi>2)"
| "nNot \<phi> = FNot \<phi>"

primrec norm where
  "norm (FQ a m) = FQ a m"
| "norm (FLess m n) = FLess m n"
| "norm (FIn m M) = FIn m M"
| "norm (FOr \<phi> \<psi>) = FOr (norm \<phi>) (norm \<psi>)"
| "norm (FAnd \<phi> \<psi>) = FAnd (norm \<phi>) (norm \<psi>)"
| "norm (FNot \<phi>) = nNot (norm \<phi>)"
| "norm (FExists \<phi>) = FExists (norm \<phi>)"
| "norm (FEXISTS \<phi>) = FEXISTS (norm \<phi>)"

context formula
begin

lemma satisfies_nNot[simp]: "(w, I) \<Turnstile> nNot \<phi> \<longleftrightarrow> (w, I) \<Turnstile> FNot \<phi>"
  by (induct \<phi> rule: nNot.induct) auto

lemma FOV_nNot[simp]: "FOV (nNot \<phi>) = FOV (FNot \<phi>)"
  by (induct \<phi> rule: nNot.induct) auto

lemma SOV_nNot[simp]: "SOV (nNot \<phi>) = SOV (FNot \<phi>)"
  by (induct \<phi> rule: nNot.induct) auto

lemma pre_wf_formula_nNot[simp]: "pre_wf_formula n (nNot \<phi>) = pre_wf_formula n (FNot \<phi>)"
  by (induct \<phi> rule: nNot.induct) auto

lemma FOV_norm[simp]: "FOV (norm \<phi>) = FOV \<phi>"
  by (induct \<phi>) auto

lemma SOV_norm[simp]: "SOV (norm \<phi>) = SOV \<phi>"
  by (induct \<phi>) auto

lemma pre_wf_formula_norm[simp]: "pre_wf_formula n (norm \<phi>) = pre_wf_formula n \<phi>"
  by (induct \<phi> arbitrary: n) auto

lemma satisfies_norm[simp]: "wI \<Turnstile> norm \<phi> \<longleftrightarrow> wI \<Turnstile> \<phi>"
  by (induct \<phi> arbitrary: wI) auto

lemma lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_norm[simp]: "lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n (norm \<phi>) = lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S n \<phi>"
  unfolding lang\<^sub>W\<^sub>S\<^sub>1\<^sub>S_def by auto

end

(*<*)
end
(*>*)
