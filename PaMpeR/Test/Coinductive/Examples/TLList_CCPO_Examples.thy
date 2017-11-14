(*  Title:       TLList_CCPO_Examples.thy
    Author:      Andreas Lochbihler, ETH Zurich
*)

section {* Example definitions using the CCPO structure on terminated lazy lists *}

theory TLList_CCPO_Examples imports
   "../TLList_CCPO"
begin

context fixes b :: 'b begin
interpretation tllist_pf b .

context fixes P :: "'a \<Rightarrow> bool"
  notes [[function_internals]]
begin

partial_function (tllist) tfilter :: "('a, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where
  "tfilter xs = (case xs of TNil b' \<Rightarrow> TNil b' | TCons x xs' \<Rightarrow> if P x then TCons x (tfilter xs') else tfilter xs')"

end

simps_of_case tfilter_simps [simp]: tfilter.simps

lemma is_TNil_tfilter: "is_TNil (tfilter P xs) \<longleftrightarrow> (\<forall>x \<in> tset xs. \<not> P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI ballI)+
  fix x
  assume "x \<in> tset xs" ?lhs
  thus "\<not> P x"
  proof(induct rule: tllist_set_induct)
    case (find xs)
    thus ?case by(cases xs)(simp_all split: if_split_asm)
  next
    case (step xs x)
    thus ?case by(cases xs)(simp_all split: if_split_asm)
  qed
next
  assume ?rhs
  thus ?lhs
    by(induct arbitrary: xs rule: tfilter.fixp_induct)(simp_all split: tllist.split)
qed

end

lemma mcont2mcont_tfilter[THEN tllist.mcont2mcont, simp, cont_intro]:
  shows mcont_tfilter: "mcont (tSup b) (tllist_ord b) (tSup b) (tllist_ord b) (tfilter b P)"
apply(rule tllist.fixp_preserves_mcont1[OF tfilter.mono tfilter_def])
apply(rule mcont_lprefix_case_aux)
apply simp_all
done

lemma tfilter_tfilter:
  "tfilter b P (tfilter b Q xs) = tfilter b (\<lambda>x. P x \<and> Q x) xs" (is "?lhs xs = ?rhs xs")
proof(rule tllist.leq_antisym)
  have "\<forall>xs. tllist_ord b (?lhs xs) (?rhs xs)"
    by(rule tfilter.fixp_induct[where Pa="\<lambda>f. \<forall>xs. tllist_ord b (tfilter b P (f xs)) (?rhs xs)"])(auto split: tllist.split)
  thus "tllist_ord b (?lhs xs) (?rhs xs)" ..

  have "\<forall>xs. tllist_ord b (?rhs xs) (?lhs xs)"
    by(rule tfilter.fixp_induct[where Pa="\<lambda>f. \<forall>xs. tllist_ord b (f xs) (?lhs xs)"])(auto split: tllist.split)
  thus "tllist_ord b (?rhs xs) (?lhs xs)" ..
qed

declare ccpo.admissible_leI[OF complete_lattice_ccpo, cont_intro, simp]

lemma tset_tfilter: "tset (tfilter b P xs) = {x\<in>tset xs. P x}"
proof(rule equalityI[OF _ subsetI])
  show "tset (tfilter b P xs) \<subseteq> {x \<in> tset xs. P x}"
    by(induct arbitrary: xs rule: tfilter.fixp_induct)(auto split: tllist.split)
  fix x
  assume "x \<in> {x \<in> tset xs. P x}"
  hence "x \<in> tset xs" "P x" by simp_all
  thus "x \<in> tset (tfilter b P xs)"
    by(induct rule: tset_induct) simp_all
qed

context fixes b :: 'b begin
interpretation tllist_pf b .

partial_function (tllist) tconcat :: "('a llist, 'b) tllist \<Rightarrow> ('a, 'b) tllist"
where
  "tconcat xs = (case xs of TNil b \<Rightarrow> TNil b | TCons x xs' \<Rightarrow> lappendt x (tconcat xs'))"

end

simps_of_case tconcat2_simps [simp]: tconcat.simps

end

