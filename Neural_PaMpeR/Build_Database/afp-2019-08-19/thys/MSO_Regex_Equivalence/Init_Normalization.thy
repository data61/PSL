(* Author: Dmitriy Traytel *)

section "Initial Normalization of the Input"

(*<*)
theory Init_Normalization
imports Pi_Regular_Exp "HOL-Library.Simps_Case_Conv"
begin
(*>*)

fun toplevel_inters where
  "toplevel_inters (Inter r s) = toplevel_inters r \<union> toplevel_inters s"
| "toplevel_inters r = {r}"

lemma toplevel_inters_nonempty[simp]:
  "toplevel_inters r \<noteq> {}"
  by (induct r) auto

lemma toplevel_inters_finite[simp]:
  "finite (toplevel_inters r)"
  by (induct r) auto

context alphabet
begin

lemma toplevel_inters_wf:
  "wf n s = (\<forall>r\<in>toplevel_inters s. wf n r)"
  by (induct s) auto

end

context project
begin

lemma toplevel_inters_lang:
  "r \<in> toplevel_inters s \<Longrightarrow> lang n s \<subseteq> lang n r"
  by (induct s) auto

lemma toplevel_inters_lang_INT:
  "lang n s = (\<Inter>r\<in>toplevel_inters s. lang n r)"
  by (induct s) auto

lemma toplevel_inters_in_lang:
  "w \<in> lang n s = (\<forall>r\<in>toplevel_inters s. w \<in> lang n r)"
  by (induct s) auto

lemma lang_flatten_INTERSECT_finite[simp]:
  "finite X \<Longrightarrow> w \<in> lang n (flatten INTERSECT X) = 
    (if X = {} then w \<in> lists (\<Sigma> n) else (\<forall>r \<in> X. w \<in> lang n r))"
  unfolding lang_INTERSECT by auto

end

fun merge_distinct where
  "merge_distinct [] xs = xs"
| "merge_distinct xs [] = xs"
| "merge_distinct (a # xs) (b # ys) =
    (if a = b then merge_distinct xs (b # ys)
    else if a < b then a # merge_distinct xs (b # ys)
    else b # merge_distinct (a # xs) ys)"

lemma set_merge_distinct[simp]: "set (merge_distinct xs ys) = set xs \<union> set ys"
  by (induct xs ys rule: merge_distinct.induct) auto

lemma sorted_merge_distinct[simp]: "\<lbrakk>sorted xs; sorted ys\<rbrakk> \<Longrightarrow> sorted (merge_distinct xs ys)"
  by (induct xs ys rule: merge_distinct.induct) (auto)

lemma distinct_merge_distinct[simp]: "\<lbrakk>sorted xs; distinct xs; sorted ys; distinct ys\<rbrakk> \<Longrightarrow>
  distinct (merge_distinct xs ys)"
  by (induct xs ys rule: merge_distinct.induct) (auto)

lemma sorted_list_of_set_merge_distinct[simp]: "\<lbrakk>sorted xs; distinct xs; sorted ys; distinct ys\<rbrakk> \<Longrightarrow>
  merge_distinct xs ys = sorted_list_of_set (set xs \<union> set ys)"
  by (auto intro: sorted_distinct_set_unique)

fun zip_with_option where
  "zip_with_option f (Some a) (Some b) = Some (f a b)"
| "zip_with_option _ _ _ = None"

lemma zip_with_option_eq_Some[simp]:
  "zip_with_option f x y = Some z \<longleftrightarrow> (\<exists>a b. z = f a b \<and> x = Some a \<and> y = Some b)"
  by (induct f x y rule: zip_with_option.induct) auto

fun Pluss where
  "Pluss (Plus r s) = zip_with_option merge_distinct (Pluss r) (Pluss s)"
| "Pluss Zero = Some []"
| "Pluss Full = None"
| "Pluss r = Some [r]"

lemma Pluss_None[symmetric]: "Pluss r = None \<longleftrightarrow> Full \<in> toplevel_summands r"
  by (induct r) auto

lemma Pluss_Some: "Pluss r = Some xs \<longleftrightarrow>
  (Full \<notin> set xs \<and> xs = sorted_list_of_set (toplevel_summands r - {Zero}))"
proof (induct r arbitrary: xs)
  case (Plus r s)
  show ?case
  proof safe
    assume "Pluss (Plus r s) = Some xs"
    then obtain a b where *: "Pluss r = Some a" "Pluss s = Some b" "xs = merge_distinct a b" by auto
    with Plus(1)[of a] Plus(2)[of b]
      show "xs = sorted_list_of_set (toplevel_summands (Plus r s) - {Zero})" by (simp add: Un_Diff)
    assume "Full \<in> set xs" with Plus(1)[of a] Plus(2)[of b] * show False by (simp add: Pluss_None)
  next
    assume "Full \<notin> set (sorted_list_of_set (toplevel_summands (Plus r s) - {Zero}))"
    with Plus(1)[of "sorted_list_of_set (toplevel_summands r - {Zero})"]
      Plus(2)[of "sorted_list_of_set (toplevel_summands s - {Zero})"]
      show "Pluss (Plus r s) = Some (sorted_list_of_set (toplevel_summands (Plus r s) - {Zero}))"
        by (simp add: Un_Diff)
  qed
qed force+

fun Inters where
  "Inters (Inter r s) = zip_with_option merge_distinct (Inters r) (Inters s)"
| "Inters Zero = None"
| "Inters Full = Some []"
| "Inters r = Some [r]"

lemma Inters_None[symmetric]: "Inters r = None \<longleftrightarrow> Zero \<in> toplevel_inters r"
  by (induct r) auto

lemma Inters_Some: "Inters r = Some xs \<longleftrightarrow>
  (Zero \<notin> set xs \<and> xs = sorted_list_of_set (toplevel_inters r - {Full}))"
proof (induct r arbitrary: xs)
  case (Inter r s)
  show ?case
  proof safe
    assume "Inters (Inter r s) = Some xs"
    then obtain a b where *: "Inters r = Some a" "Inters s = Some b" "xs = merge_distinct a b" by auto
    with Inter(1)[of a] Inter(2)[of b]
      show "xs = sorted_list_of_set (toplevel_inters (Inter r s) - {Full})" by (simp add: Un_Diff)
    assume "Zero \<in> set xs" with Inter(1)[of a] Inter(2)[of b] * show False by (simp add: Inters_None)
  next
    assume "Zero \<notin> set (sorted_list_of_set (toplevel_inters (Inter r s) - {Full}))"
    with Inter(1)[of "sorted_list_of_set (toplevel_inters r - {Full})"]
      Inter(2)[of "sorted_list_of_set (toplevel_inters s - {Full})"]
      show "Inters (Inter r s) = Some (sorted_list_of_set (toplevel_inters (Inter r s) - {Full}))"
        by (simp add: Un_Diff)
  qed
qed force+

definition inPlus where
  "inPlus r s = (case Pluss (Plus r s) of None \<Rightarrow> Full | Some rs \<Rightarrow> PLUS rs)"

lemma inPlus_alt: "inPlus r s = (let X = toplevel_summands (Plus r s) - {Zero} in
  flatten PLUS (if Full \<in> X then {Full} else X))"
proof (cases "Pluss r" "Pluss s" rule: option.exhaust[case_product option.exhaust])
  case Some_Some then show ?thesis by (simp add: inPlus_def Pluss_None) (simp add: Pluss_Some Un_Diff)
qed (simp_all add: inPlus_def Pluss_None)

fun inTimes where
  "inTimes Zero _ = Zero"
| "inTimes _ Zero = Zero"
| "inTimes One r = r"
| "inTimes r One = r"
| "inTimes (Times r s) t = Times r (inTimes s t)"
| "inTimes r s = Times r s"

fun inStar where
  "inStar Zero = One"
| "inStar Full = Full"
| "inStar One = One"
| "inStar (Star r) = Star r"
| "inStar r = Star r"

definition inInter where
  "inInter r s = (case Inters (Inter r s) of None \<Rightarrow> Zero | Some rs \<Rightarrow> INTERSECT rs)"

lemma inInter_alt: "inInter r s = (let X = toplevel_inters (Inter r s) - {Full} in
  flatten INTERSECT (if Zero \<in> X then {Zero} else X))"
proof (cases "Inters r" "Inters s" rule: option.exhaust[case_product option.exhaust])
  case Some_Some then show ?thesis by (simp add: inInter_def Inters_None) (simp add: Inters_Some Un_Diff)
qed (simp_all add: inInter_def Inters_None)

fun inNot where
  "inNot Zero = Full"
| "inNot Full = Zero"
| "inNot (Not r) = r"
| "inNot (Plus r s) = Inter (inNot r) (inNot s)"
| "inNot (Inter r s) = Plus (inNot r) (inNot s)"
| "inNot r = Not r"

fun inPr where
  "inPr Zero = Zero"
| "inPr One = One"
| "inPr (Plus r s) = Plus (inPr r) (inPr s)"
| "inPr r = Pr r"

primrec inorm where
  "inorm Zero = Zero"
| "inorm Full = Full"
| "inorm One = One"
| "inorm (Atom a) = Atom a"
| "inorm (Plus r s) = Plus (inorm r) (inorm s)"
| "inorm (Times r s) = Times (inorm r) (inorm s)"
| "inorm (Star r) = inStar (inorm r)"
| "inorm (Not r) = inNot (inorm r)"
| "inorm (Inter r s) = inInter (inorm r) (inorm s)"
| "inorm (Pr r) = inPr (inorm r)"

context alphabet begin

lemma wf_inPlus[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (inPlus r s)"
  by (subst (asm) (1 2) toplevel_summands_wf) (auto simp: inPlus_alt)

lemma wf_inTimes[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (inTimes r s)"
  by (induct r s rule: inTimes.induct) auto

lemma wf_inStar[simp]: "wf n r \<Longrightarrow> wf n (inStar r)"
  by (induct r rule: inStar.induct) auto

lemma wf_inInter[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> wf n (inInter r s)"
  by (subst (asm) (1 2) toplevel_inters_wf) (auto simp: inInter_alt)

lemma wf_inNot[simp]: "wf n r \<Longrightarrow> wf n (inNot r)"
  by (induct r rule: inNot.induct) auto

lemma wf_inPr[simp]: "wf (Suc n) r \<Longrightarrow> wf n (inPr r)"
  by (induct r rule: inPr.induct) auto

lemma wf_inorm[simp]: "wf n r \<Longrightarrow> wf n (inorm r)"
  by (induct r arbitrary: n) auto

end

context project begin

lemma lang_inPlus[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (inPlus r s) = lang n (Plus r s)"
  by (auto 0 3 simp: inPlus_alt toplevel_summands_in_lang[of _ n r] toplevel_summands_in_lang[of _ n s]
    dest: lang_subset_lists intro: bexI[of _ Full])

lemma lang_inTimes[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (inTimes r s) = lang n (Times r s)"
  by (induct r s rule: inTimes.induct) (auto simp: conc_assoc)

lemma lang_inStar[simp]: "wf n r \<Longrightarrow> lang n (inStar r) = lang n (Star r)"
  by (induct r rule: inStar.induct)
    (auto intro: star_if_lang dest: subsetD[OF star_subset_lists, rotated])

lemma Zero_toplevel_inters[dest]: "Zero \<in> toplevel_inters r \<Longrightarrow> lang n r = {}"
  by (metis lang.simps(1) subset_empty toplevel_inters_lang)

lemma toplevel_inters_Full: "\<lbrakk>toplevel_inters r = {Full}; wf n r\<rbrakk> \<Longrightarrow> lang n r = lists (\<Sigma> n)"
  by (metis antisym lang.simps(2) subsetI toplevel_inters.simps(3) toplevel_inters_in_lang)

lemma toplevel_inters_subset_singleton[simp]: "toplevel_inters r \<subseteq> {s} \<longleftrightarrow> toplevel_inters r = {s}"
  by (metis subset_refl subset_singletonD toplevel_inters_nonempty)

lemma lang_inInter[simp]: "\<lbrakk>wf n r; wf n s\<rbrakk> \<Longrightarrow> lang n (inInter r s) = lang n (Inter r s)"
  using lang_subset_lists[of n, unfolded lang.simps(2)[symmetric]]
    toplevel_inters_nonempty[of r] toplevel_inters_nonempty[of s]
  apply (auto 0 2 simp: inInter_alt toplevel_inters_in_lang[of _ n r] toplevel_inters_in_lang[of _ n s]
     toplevel_inters_wf[of n r] toplevel_inters_wf[of n s] Ball_def simp del: toplevel_inters_nonempty
     dest!: toplevel_inters_Full[of _ n] split: if_splits)
  by fastforce+

lemma lang_inNot[simp]: "wf n r \<Longrightarrow> lang n (inNot r) = lang n (Not r)"
  by (induct r rule: inNot.induct) (auto dest: lang_subset_lists)

lemma lang_inPr[simp]: "wf (Suc n) r \<Longrightarrow> lang n (inPr r) = lang n (Pr r)"
  by (induct r rule: inPr.induct) auto

lemma lang_inorm[simp]: "wf n r \<Longrightarrow> lang n (inorm r) = lang n r"
  by (induct r arbitrary: n) auto

end

(*<*)
end
(*>*)
