(* Author: Dmitriy Traytel *)

section \<open>Normalization of M2L Formulas\<close>

(*<*)
theory M2L_Normalization
imports M2L
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

lemma satisfies_nNot[simp]: "satisfies (w, I) (nNot \<phi>) = satisfies (w,I) (FNot \<phi>)"
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

lemma satisfies_norm[simp]: "satisfies (w, I) (norm \<phi>) = satisfies (w, I) \<phi>"
  by (induct \<phi> arbitrary: I) auto

lemma lang\<^sub>M\<^sub>2\<^sub>L_norm[simp]: "lang\<^sub>M\<^sub>2\<^sub>L n (norm \<phi>) = lang\<^sub>M\<^sub>2\<^sub>L n \<phi>"
  unfolding lang\<^sub>M\<^sub>2\<^sub>L_def by auto

end

(*<*)
end
(*>*)
