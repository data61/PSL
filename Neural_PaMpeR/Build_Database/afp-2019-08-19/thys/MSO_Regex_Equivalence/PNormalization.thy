(* Author: Dmitriy Traytel *)

section "Partial Derivatives-like Normalization"

(*<*)
theory PNormalization
imports Pi_Derivatives
begin
(*>*)

fun pnPlus :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "pnPlus Zero r = r"
| "pnPlus r Zero = r"
(*<*)
(*
| "pnPlus Full r = Full"
| "pnPlus r Full = Full"
*)
(*>*)
| "pnPlus (Plus r s) t = pnPlus r (pnPlus s t)"
| "pnPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if r \<le> s then Plus r (Plus s t)
     else Plus s (pnPlus r t))"
| "pnPlus r s =
     (if r = s then r
      else if r \<le> s then Plus r s
      else Plus s r)"

lemma (in alphabet) wf_pnPlus[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (pnPlus r s)"
  by (induct r s rule: pnPlus.induct) auto

lemma (in project) lang_pnPlus[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (pnPlus r s) = lang n (Plus r s)"
  by (induct r s rule: pnPlus.induct) (auto dest!: lang_subset_lists dest: project
      subsetD[OF star_subset_lists, unfolded in_lists_conv_set, rotated -1]
      subsetD[OF conc_subset_lists, unfolded in_lists_conv_set, rotated -1])

fun pnTimes :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "pnTimes Zero r = Zero"
| "pnTimes One r = r"
| "pnTimes (Plus r s) t = pnPlus (pnTimes r t) (pnTimes s t)"
| "pnTimes r s = Times r s"

lemma (in alphabet) wf_pnTimes[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (pnTimes r s)"
  by (induct r s rule: pnTimes.induct) auto

lemma (in project) lang_pnTimes[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (pnTimes r s) = lang n (Times r s)"
  by (induct r s rule: pnTimes.induct) auto

fun pnInter :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "pnInter Zero r = Zero"
| "pnInter r Zero = Zero"
| "pnInter Full r = r"
| "pnInter r Full = r"
| "pnInter (Plus r s) t = pnPlus (pnInter r t) (pnInter s t)"
| "pnInter r (Plus s t) = pnPlus (pnInter r s) (pnInter r t)"
| "pnInter (Inter r s) t = pnInter r (pnInter s t)"
| "pnInter r (Inter s t) =
     (if r = s then Inter s t
     else if r \<le> s then Inter r (Inter s t)
     else Inter s (pnInter r t))"
| "pnInter r s =
     (if r = s then s
      else if r \<le> s then Inter r s
      else Inter s r)"

lemma (in alphabet) wf_pnInter[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (pnInter r s)"
  by (induct r s rule: pnInter.induct) auto

lemma (in project) lang_pnInter[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (pnInter r s) = lang n (Inter r s)"
  by (induct r s rule: pnInter.induct) (auto, auto dest!: lang_subset_lists dest: project
      subsetD[OF star_subset_lists, unfolded in_lists_conv_set, rotated -1]
      subsetD[OF conc_subset_lists, unfolded in_lists_conv_set, rotated -1])

fun pnNot :: "'a::linorder rexp \<Rightarrow> 'a rexp" where
  "pnNot (Plus r s) = pnInter (pnNot r) (pnNot s)"
| "pnNot (Inter r s) = pnPlus (pnNot r) (pnNot s)"
| "pnNot Full = Zero"
| "pnNot Zero = Full"
| "pnNot (Not r) = r"
| "pnNot r = Not r"

lemma (in alphabet) wf_pnNot[simp]: "wf n r \<Longrightarrow> wf n (pnNot r)"
  by (induct r rule: pnNot.induct) auto

lemma (in project) lang_pnNot[simp]: "wf n r \<Longrightarrow> lang n (pnNot r) = lang n (Not r)"
  by (induct r rule: pnNot.induct) (auto dest: lang_subset_lists)

fun pnPr :: "'a::linorder rexp \<Rightarrow> 'a rexp" where
  "pnPr Zero = Zero"
| "pnPr One = One"
| "pnPr (Plus r s) = pnPlus (pnPr r) (pnPr s)"
| "pnPr r = Pr r"

lemma (in alphabet) wf_pnPr[simp]: "wf (Suc n) r \<Longrightarrow> wf n (pnPr r)"
  by (induct r rule: pnPr.induct) auto

lemma (in project) lang_pnPr[simp]: "wf (Suc n) r \<Longrightarrow> lang n (pnPr r) = lang n (Pr r)"
  by (induct r rule: pnPr.induct) auto

primrec pnorm :: "'a::linorder rexp \<Rightarrow> 'a rexp" where
  "pnorm Zero = Zero"
| "pnorm Full = Full"
| "pnorm One = One"
| "pnorm (Atom a) = Atom a"
| "pnorm (Plus r s) = pnPlus (pnorm r) (pnorm s)"
| "pnorm (Times r s) = pnTimes (pnorm r) s"
| "pnorm (Star r) = Star r"
| "pnorm (Inter r s) = pnInter (pnorm r) (pnorm s)"
| "pnorm (Not r) = pnNot (pnorm r)"
| "pnorm (Pr r) = pnPr (pnorm r)"

lemma (in alphabet) wf_pnorm[simp]: "wf n r \<Longrightarrow> wf n (pnorm r)"
  by (induct r arbitrary: n) auto

lemma (in project) lang_pnorm[simp]: "wf n r \<Longrightarrow> lang n (pnorm r) = lang n r"
  by (induct r arbitrary: n) auto

(*<*)
end
(*>*)
