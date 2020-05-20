(* Author: Dmitriy Traytel *)

section \<open>$\Pi$-Extended Dual Regular Expressions\<close>

(*<*)
theory Pi_Regular_Exp_Dual
imports Pi_Derivatives "HOL-Library.List_Lexorder" "HOL-Library.Code_Target_Nat"
begin
(*>*)
subsection \<open>Syntax of regular expressions\<close>

datatype 'a rexp_dual =
  CoZero (co: bool) |
  CoOne (co: bool) |
  CoAtom (co: bool) 'a |
  CoPlus (co: bool) "'a rexp_dual" "'a rexp_dual" |
  CoTimes (co: bool) "'a rexp_dual" "'a rexp_dual" |
  CoStar (co: bool) "'a rexp_dual" |
  CoPr (co: bool) "'a rexp_dual"
derive linorder rexp_dual

abbreviation "CoPLUS_dual b \<equiv> rexp_of_list (CoPlus b) (CoZero b)"
abbreviation "bool_unop_dual b \<equiv> (if b then id else HOL.Not)"
abbreviation "bool_binop_dual b \<equiv> (if b then (\<or>) else (\<and>))"
abbreviation "set_binop_dual b \<equiv> (if b then (\<union>) else (\<inter>))"

primrec final_dual :: "'a rexp_dual \<Rightarrow> bool"
where
  "final_dual (CoZero b) = (\<not> b)"
| "final_dual (CoOne b) = b"
| "final_dual (CoAtom b _) = (\<not> b)"
| "final_dual (CoPlus b r s) = bool_binop_dual b (final_dual r) (final_dual s)"
| "final_dual (CoTimes b r s) = bool_binop_dual (\<not> b) (final_dual r) (final_dual s)"
| "final_dual (CoStar b _) = b"
| "final_dual (CoPr _ r) = final_dual r"

context alphabet
begin

primrec wf_dual :: "nat \<Rightarrow> 'b rexp_dual \<Rightarrow> bool"
where
"wf_dual n (CoZero _) = True" |
"wf_dual n (CoOne _) = True" |
"wf_dual n (CoAtom _ a) = (wf_atom n a)" |
"wf_dual n (CoPlus _ r s) = (wf_dual n r \<and> wf_dual n s)" |
"wf_dual n (CoTimes _ r s) = (wf_dual n r \<and> wf_dual n s)" |
"wf_dual n (CoStar _ r) = wf_dual n r" |
"wf_dual n (CoPr _ r) = wf_dual (n + 1) r"

lemma wf_dual_PLUS_dual[simp]:
  "wf_dual n (CoPLUS_dual b xs) = (\<forall>r \<in> set xs. wf_dual n r)"
  by (induct xs rule: list_singleton_induct) auto

abbreviation "set_unop_dual n b A \<equiv> if b then A else lists (\<Sigma> n) - A"

end

context project
begin

primrec lang_dual :: "nat \<Rightarrow> 'b rexp_dual => 'a lang" where
"lang_dual n (CoZero b) = set_unop_dual n b {}" |
"lang_dual n (CoOne b) = set_unop_dual n b {[]}" |
"lang_dual n (CoAtom b a) = set_unop_dual n b {[x] | x. lookup a x \<and> x \<in> \<Sigma> n}" |
"lang_dual n (CoPlus b r s) = set_binop_dual b (lang_dual n r) (lang_dual n s)" |
"lang_dual n (CoTimes b r s) = set_unop_dual n b
   (set_unop_dual n b (lang_dual n r) @@ set_unop_dual n b (lang_dual n s))" |
"lang_dual n (CoStar b r) = set_unop_dual n b (star (set_unop_dual n b (lang_dual n r)))" |
"lang_dual n (CoPr b r) = set_unop_dual n b (map project ` (set_unop_dual (n + 1) b (lang_dual (n + 1) r)))"

lemma wf_dual_lang_dual_wf_word: "wf_dual n r \<Longrightarrow> \<forall>w \<in> lang_dual n r. wf_word n w"
  by (induct r arbitrary: n) (auto elim: rev_subsetD[OF _ conc_mono] star_induct
    intro: iffD2[OF wf_word] wf_word_map_project)

lemma lang_dual_subset_lists: "wf_dual n r \<Longrightarrow> lang_dual n r \<subseteq> lists (\<Sigma> n)"
proof (induct r arbitrary: n)
  case (CoPr b r) thus ?case by (cases b) (fastforce intro!: project)+
qed (auto simp: conc_subset_lists star_subset_lists)

lemma lang_dual_final_dual: "final_dual r = ([] \<in> lang_dual n r)"
  by (induct r arbitrary: n) (auto intro: concI[of "[]" _ "[]", simplified])

lemma lang_dual_PLUS_dual[simp]:
  "lang_dual n (CoPLUS_dual True xs) = (\<Union>r \<in> set xs. lang_dual n r)"
  by (induct xs rule: list_singleton_induct) auto

lemma lang_dual_CoPLUS_dual[simp]:
  "lang_dual n (CoPLUS_dual False xs) = (if xs = [] then lists (\<Sigma> n) else \<Inter>r \<in> set xs. lang_dual n r)"
  by (induct xs rule: list_singleton_induct) auto

end

context embed
begin

primrec lderiv_dual :: "'a \<Rightarrow> 'b rexp_dual \<Rightarrow> 'b rexp_dual" where
  "lderiv_dual _ (CoZero b) = (CoZero b)"
| "lderiv_dual _ (CoOne b) = (CoZero b)"
| "lderiv_dual a (CoAtom b c) = (if lookup c a then CoOne b else CoZero b)"
| "lderiv_dual a (CoPlus b r s) = CoPlus b (lderiv_dual a r) (lderiv_dual a s)"
| "lderiv_dual a (CoTimes b r s) =
    (let r's = CoTimes b (lderiv_dual a r) s
     in if bool_unop_dual b (final_dual r) then CoPlus b r's (lderiv_dual a s) else r's)"
| "lderiv_dual a (CoStar b r) = CoTimes b (lderiv_dual a r) (CoStar b r)"
| "lderiv_dual a (CoPr b r) = CoPr b (CoPLUS_dual b (map (\<lambda>a'. lderiv_dual a' r) (embed a)))"

primrec lderivs_dual where
  "lderivs_dual [] r = r"
| "lderivs_dual (w#ws) r = lderivs_dual ws (lderiv_dual w r)"

lemma wf_dual_lderiv_dual[simp]: "wf_dual n r \<Longrightarrow> wf_dual n (lderiv_dual w r)"
  by (induct r arbitrary: n w) (auto simp add: Let_def)

lemma wf_dual_lderivs_dual[simp]: "wf_dual n r \<Longrightarrow> wf_dual n (lderivs_dual ws r)"
  by (induct ws arbitrary: r) (auto intro: wf_dual_lderiv_dual)

lemma lang_dual_lderiv_dual: "\<lbrakk>wf_dual n r; w \<in> \<Sigma> n\<rbrakk> \<Longrightarrow>
  lang_dual n (lderiv_dual w r) = lQuot w (lang_dual n r)"
proof (induct r arbitrary: n w)
  case (CoPr b r)
  hence *: "wf_dual (Suc n) r" "\<And>w'. w' \<in> set (embed w) \<Longrightarrow>  w' \<in> \<Sigma> (Suc n)" by (auto simp: embed)
  then show ?case using lQuot_map_project[OF CoPr(3) lang_dual_subset_lists[OF *(1)]]
    lQuot_map_project[OF CoPr(3) Diff_subset, of "lang_dual (n + 1) r"]
    by (simp_all add: CoPr(1,3))
qed (auto 0 3 simp: Let_def lang_dual_final_dual[symmetric])

lemma lang_dual_lderivs_dual: "\<lbrakk>wf_dual n r; wf_word n ws\<rbrakk> \<Longrightarrow>
  lang_dual n (lderivs_dual ws r) = lQuots ws (lang_dual n r)"
  by (induct ws arbitrary: r) (auto simp: lang_dual_lderiv_dual)

corollary lderivs_dual_final_dual:
  assumes "wf_dual n r" "wf_word n ws"
  shows "final_dual (lderivs_dual ws r) \<longleftrightarrow> ws \<in> lang_dual n r"
  using lang_dual_lderivs_dual[OF assms] lang_dual_final_dual[of "lderivs_dual ws r" n] by auto

end

fun pnCoPlus :: "bool \<Rightarrow> 'a::linorder rexp_dual \<Rightarrow> 'a rexp_dual \<Rightarrow> 'a rexp_dual" where
  "pnCoPlus b1 (CoZero b2) r = (if b1 = b2 then r else CoZero b2)"
| "pnCoPlus b1 r (CoZero b2) = (if b1 = b2 then r else CoZero b2)"
| "pnCoPlus b1 (CoPlus b2 r s) t =
    (if b1 = b2 then pnCoPlus b2 r (pnCoPlus b2 s t) else CoPlus b1 (CoPlus b2 r s) t)"
| "pnCoPlus b1 r (CoPlus b2 s t) =
     (if b1 = b2 then
       (if r = s then (CoPlus b2 s t)
       else if r \<le> s then CoPlus b2 r (CoPlus b2 s t)
       else CoPlus b2 s (pnCoPlus b2 r t))
     else CoPlus b1 r (CoPlus b2 s t))"
| "pnCoPlus b r s =
     (if r = s then r
      else if r \<le> s then CoPlus b r s
      else CoPlus b s r)"

lemma (in alphabet) wf_dual_pnCoPlus[simp]: "\<lbrakk>wf_dual n r; wf_dual n s\<rbrakk> \<Longrightarrow> wf_dual n (pnCoPlus b r s)"
  by (induct b r s rule: pnCoPlus.induct) auto

lemma (in project) lang_dual_pnCoPlus[simp]: "\<lbrakk>wf_dual n r; wf_dual n s\<rbrakk> \<Longrightarrow>
  lang_dual n (pnCoPlus b r s) = lang_dual n (CoPlus b r s)"
proof (induct b r s rule: pnCoPlus.induct)
  case 1 thus ?case by (auto dest: lang_dual_subset_lists)
next
  case "2_1" thus ?case by auto
next
  case "2_2" thus ?case by auto
next
  case "2_3" thus ?case by (auto dest: lang_dual_subset_lists)
next
  case "2_4" thus ?case by (auto dest!: lang_dual_subset_lists dest:
    subsetD[OF conc_subset_lists, unfolded in_lists_conv_set, rotated -1])
next
  case "2_5" thus ?case by (auto dest!: lang_dual_subset_lists dest:
    subsetD[OF star_subset_lists, unfolded in_lists_conv_set, rotated -1])
next
  case "2_6" thus ?case by (auto 4 4 dest!: lang_dual_subset_lists intro: project)
next
  case "3_1" thus ?case by auto
next
  case "3_2" thus ?case by auto
next
  case "3_3" thus ?case by auto
next
  case "3_4" thus ?case by auto
next
  case "3_5" thus ?case by auto
next
  case "3_6" thus ?case by auto
next
  case "4_1" thus ?case by auto
next
  case "4_2" thus ?case by auto
next
  case "4_3" thus ?case by auto
next
  case "4_4" thus ?case by auto
next
  case "4_5" thus ?case by auto
next
  case "5_1" thus ?case by auto
next
  case "5_2" thus ?case by auto
next
  case "5_3" thus ?case by auto
next
  case "5_4" thus ?case by auto
next
  case "5_5" thus ?case by auto
next
  case "5_6" thus ?case by auto
next
  case "5_7" thus ?case by auto
next
  case "5_8" thus ?case by auto
next
  case "5_9" thus ?case by auto
next
  case "5_10" thus ?case
    by auto (metis (no_types, hide_lams) Cons_in_lists_iff Diff_iff imageI list.simps(8) list.simps(9) lists.Nil)+
next
  case "5_11" thus ?case by auto
next
  case "5_12" thus ?case by auto
next
  case "5_13" thus ?case by auto
next
  case "5_14" thus ?case by auto
next
  case "5_15" thus ?case by auto
next
  case "5_16" thus ?case by auto
next
  case "5_17" thus ?case by auto
next
  case "5_18" thus ?case by auto
next
  case "5_19" thus ?case by (auto dest!: lang_dual_subset_lists dest:
    subsetD[OF star_subset_lists, unfolded in_lists_conv_set, rotated -1])
next
  case "5_20" thus ?case by auto
next
  case "5_21" thus ?case by auto
next
  case "5_22" thus ?case
    by auto (metis (no_types, hide_lams) Cons_in_lists_iff Diff_iff imageI list.simps(8) list.simps(9) lists.Nil)+
next
  case "5_23" thus ?case by auto
next
  case "5_24" thus ?case by auto
next
  case "5_25" thus ?case by auto
qed

fun pnCoTimes :: "bool \<Rightarrow> 'a::linorder rexp_dual \<Rightarrow> 'a rexp_dual \<Rightarrow> 'a rexp_dual" where
  "pnCoTimes b1 (CoZero b2) r = (if b1 = b2 then CoZero b1 else CoTimes b1 (CoZero b2) r)"
| "pnCoTimes b1 (CoOne b2) r = (if b1 = b2 then r else CoTimes b1 (CoOne b2) r)"
| "pnCoTimes b1 (CoPlus b2 r s) t = (if b1 = b2 then pnCoPlus b2 (pnCoTimes b2 r t) (pnCoTimes b2 s t)
   else CoTimes b1 (CoPlus b2 r s) t)"
| "pnCoTimes b r s = CoTimes b r s"

lemma (in alphabet) wf_dual_pnCoTimes[simp]: "\<lbrakk>wf_dual n r; wf_dual n s\<rbrakk> \<Longrightarrow> wf_dual n (pnCoTimes b r s)"
  by (induct b r s rule: pnCoTimes.induct) auto

lemma (in project) lang_dual_pnCoTimes[simp]: "\<lbrakk>wf_dual n r; wf_dual n s\<rbrakk> \<Longrightarrow> lang_dual n (pnCoTimes b r s) = lang_dual n (CoTimes b r s)"
  apply (induct b r s rule: pnCoTimes.induct)
  apply (auto, auto dest!: lang_dual_subset_lists dest: project
      subsetD[OF star_subset_lists, unfolded in_lists_conv_set, rotated -1]
      subsetD[OF conc_subset_lists, unfolded in_lists_conv_set, rotated -1])
  by (metis (full_types) Diff_iff conc_epsilon(1) double_diff empty_subsetI in_listsI insert_subset lists.Nil subset_refl)

fun pnCoPr :: "bool \<Rightarrow> 'a::linorder rexp_dual \<Rightarrow> 'a rexp_dual" where
  "pnCoPr b1 (CoZero b2) = (if b1 = b2 then CoZero b2 else CoPr b1 (CoZero b2))"
| "pnCoPr b1 (CoOne b2) = (if b1 = b2 then CoOne b2 else CoPr b1 (CoOne b2))"
| "pnCoPr b1 (CoPlus b2 r s) = (if b1 = b2 then pnCoPlus b2 (pnCoPr b2 r) (pnCoPr b2 s)
    else CoPr b1 (CoPlus b2 r s))"
| "pnCoPr b r = CoPr b r"

lemma (in alphabet) wf_dual_pnCoPr[simp]: "wf_dual (Suc n) r \<Longrightarrow> wf_dual n (pnCoPr b r)"
  by (induct b r rule: pnCoPr.induct) auto

lemma (in project) lang_dual_pnCoPr[simp]: "wf_dual (Suc n) r \<Longrightarrow> lang_dual n (pnCoPr b r) = lang_dual n (CoPr b r)"
  by (induct b r rule: pnCoPr.induct) auto

primrec pnorm_dual :: "'a::linorder rexp_dual \<Rightarrow> 'a rexp_dual" where
  "pnorm_dual (CoZero b) = (CoZero b)"
| "pnorm_dual (CoOne b) = (CoOne b)"
| "pnorm_dual (CoAtom b a) = (CoAtom b a)"
| "pnorm_dual (CoPlus b r s) = pnCoPlus b (pnorm_dual r) (pnorm_dual s)"
| "pnorm_dual (CoTimes b r s) = pnCoTimes b (pnorm_dual r) s"
| "pnorm_dual (CoStar b r) = CoStar b r"
| "pnorm_dual (CoPr b r) = pnCoPr b (pnorm_dual r)"

lemma (in alphabet) wf_dual_pnorm_dual[simp]: "wf_dual n r \<Longrightarrow> wf_dual n (pnorm_dual r)"
  by (induct r arbitrary: n) auto

lemma (in project) lang_dual_pnorm_dual[simp]: "wf_dual n r \<Longrightarrow> lang_dual n (pnorm_dual r) = lang_dual n r"
  by (induct r arbitrary: n) auto

primrec CoNot where
  "CoNot (CoZero b) = CoZero (\<not> b)"
| "CoNot (CoOne b) = CoOne (\<not> b)"
| "CoNot (CoAtom b a) = CoAtom (\<not> b) a"
| "CoNot (CoPlus b r s) = CoPlus (\<not> b) (CoNot r) (CoNot s)"
| "CoNot (CoTimes b r s) = CoTimes (\<not> b) (CoNot r) (CoNot s)"
| "CoNot (CoStar b r) = CoStar (\<not> b) (CoNot r)"
| "CoNot (CoPr b r) = CoPr (\<not> b) (CoNot r)"

primrec rexp_dual_of where
  "rexp_dual_of Zero = CoZero True"
| "rexp_dual_of Full = CoZero False"
| "rexp_dual_of One = CoOne True"
| "rexp_dual_of (Atom a) = CoAtom True a"
| "rexp_dual_of (Plus r s) = CoPlus True (rexp_dual_of r) (rexp_dual_of s)"
| "rexp_dual_of (Times r s) = CoTimes True (rexp_dual_of r) (rexp_dual_of s)"
| "rexp_dual_of (Star r) = CoStar True (rexp_dual_of r)"
| "rexp_dual_of (Not r) = CoNot (rexp_dual_of r)"
| "rexp_dual_of (Inter r s) = CoPlus False (rexp_dual_of r) (rexp_dual_of s)"
| "rexp_dual_of (Pr r) = CoPr True (rexp_dual_of r)"

lemma (in alphabet) wf_dual_CoNot[simp]: "wf_dual n r \<Longrightarrow> wf_dual n (CoNot r)"
  by (induct r arbitrary: n) auto

lemma (in project) lang_dual_CoNot[simp]: "wf_dual n r \<Longrightarrow> lang_dual n (CoNot r) = lists (\<Sigma> n) - lang_dual n r"
  apply (induct r arbitrary: n)
  apply (auto dest!: lang_dual_subset_lists simp: double_diff intro!: project)
  apply force
  apply (metis (full_types) Diff_subset contra_subsetD in_listsD star_subset_lists)
  done

lemma (in alphabet) wf_dual_rexp_dual_of[simp]: "wf n r \<Longrightarrow> wf_dual n (rexp_dual_of r)"
  by (induct r arbitrary: n) auto

lemma (in project) lang_dual_rexp_dual_of[simp]: "wf n r \<Longrightarrow> lang_dual n (rexp_dual_of r) = lang n r"
  by (induct r arbitrary: n) auto

end
