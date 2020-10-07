(*  Title:       Hamming_Stream.thy
    Author:      Andreas Lochbihler, ETH Zurich
*)

section {* The Hamming stream defined as a least fixpoint *}

theory Hamming_Stream imports
  "../Coinductive_List"
  "HOL-Computational_Algebra.Primes"
begin

lemma infinity_inf_enat [simp]:
  fixes n :: enat
  shows "\<infinity> \<sqinter> n = n" "n \<sqinter> \<infinity> = n"
by(simp_all add: inf_enat_def)

lemma eSuc_inf_eSuc [simp]: "eSuc n \<sqinter> eSuc m = eSuc (n \<sqinter> m)"
by(simp add: inf_enat_def)


lemma if_pull2: "(if b then f x x' else f y y') = f (if b then x else y) (if b then x' else y')"
by simp

context ord begin

primcorec lmerge :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where 
  "lmerge xs ys =
   (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow>
    case ys of LNil \<Rightarrow> LNil | LCons y ys' \<Rightarrow>
    if lhd xs < lhd ys then LCons x (lmerge xs' ys)
    else LCons y (if lhd ys < lhd xs then lmerge xs ys' else lmerge xs' ys'))"

lemma lnull_lmerge [simp]: "lnull (lmerge xs ys) \<longleftrightarrow> (lnull xs \<or> lnull ys)"
by(simp add: lmerge_def)

lemma lmerge_eq_LNil_iff: "lmerge xs ys = LNil \<longleftrightarrow> (xs = LNil \<or> ys = LNil)"
using lnull_lmerge unfolding lnull_def .

lemma lhd_lmerge: "\<lbrakk> \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> lhd (lmerge xs ys) = (if lhd xs < lhd ys then lhd xs else lhd ys)"
by(auto split: llist.split)

lemma ltl_lmerge:
  "\<lbrakk> \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> 
  ltl (lmerge xs ys) = 
  (if lhd xs < lhd ys then lmerge (ltl xs) ys 
   else if lhd ys < lhd xs then lmerge xs (ltl ys) 
   else lmerge (ltl xs) (ltl ys))"
by(auto split: llist.split)

declare lmerge.sel [simp del]

lemma lmerge_simps:
  "lmerge (LCons x xs) (LCons y ys) =
  (if x < y then LCons x (lmerge xs (LCons y ys))
   else if y < x then LCons y (lmerge (LCons x xs) ys)
   else LCons y (lmerge xs ys))"
by(rule llist.expand)(simp_all add: lhd_lmerge ltl_lmerge)

lemma lmerge_LNil [simp]:
  "lmerge LNil ys = LNil"
  "lmerge xs LNil = LNil"
by simp_all

lemma lprefix_lmergeI:
  "\<lbrakk> lprefix xs xs'; lprefix ys ys' \<rbrakk>
  \<Longrightarrow> lprefix (lmerge xs ys) (lmerge xs' ys')"
by(coinduction arbitrary: xs xs' ys ys')(fastforce simp add: lhd_lmerge ltl_lmerge dest: lprefix_lhdD lprefix_lnullD simp add: not_lnull_conv split: if_split_asm)

lemma [partial_function_mono]:
  assumes F: "mono_llist F" and G: "mono_llist G"
  shows "mono_llist (\<lambda>f. lmerge (F f) (G f))"
by(blast intro: monotoneI lprefix_lmergeI monotoneD[OF F] monotoneD[OF G])

lemma in_lset_lmergeD: "x \<in> lset (lmerge xs ys) \<Longrightarrow> x \<in> lset xs \<or> x \<in> lset ys"
by(induct zs\<equiv>"lmerge xs ys" arbitrary: xs ys rule: llist_set_induct)(auto simp add: lhd_lmerge ltl_lmerge split: if_split_asm dest: in_lset_ltlD)

lemma lset_lmerge: "lset (lmerge xs ys) \<subseteq> lset xs \<union> lset ys"
by(auto dest: in_lset_lmergeD)

lemma lfinite_lmergeD: "lfinite (lmerge xs ys) \<Longrightarrow> lfinite xs \<or> lfinite ys"
by(induct zs\<equiv>"lmerge xs ys" arbitrary: xs ys rule: lfinite_induct)(fastforce simp add: ltl_lmerge if_pull2 split: if_split_asm)+

lemma fixes F
  defines "F \<equiv> \<lambda>lmerge (xs, ys). case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> case ys of LNil \<Rightarrow> LNil | LCons y ys' \<Rightarrow> (if x < y then LCons x (curry lmerge xs' ys) else if y < x then LCons y (curry lmerge xs ys') else LCons y (curry lmerge xs' ys'))"
  shows lmerge_conv_fixp: "lmerge \<equiv> curry (ccpo.fixp (fun_lub lSup) (fun_ord lprefix) F)" (is "?lhs \<equiv> ?rhs")
  and lmerge_mono: "mono_llist (\<lambda>lmerge. F lmerge xs)" (is "?mono xs")
proof(intro eq_reflection ext)
  show mono: "\<And>xs. ?mono xs" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix xs ys
  show "lmerge xs ys = ?rhs xs ys"
  proof(coinduction arbitrary: xs ys)
    case Eq_llist thus ?case
      by(subst (1 3 4) llist.mono_body_fixp[OF mono])(auto simp add: F_def lmerge_simps split: llist.split)
  qed
qed

lemma monotone_lmerge: "monotone (rel_prod lprefix lprefix) lprefix (case_prod lmerge)"
apply(rule llist.fixp_preserves_mono2[OF lmerge_mono lmerge_conv_fixp])
apply(erule conjE|rule allI conjI cont_intro|simp|erule allE, erule llist.mono2mono)+
done

lemma mono2mono_lmerge1 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lmerge1: "monotone lprefix lprefix (\<lambda>xs. lmerge xs ys)"
by(simp add: monotone_lmerge[simplified])

lemma mono2mono_lmerge2 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lmerge2: "monotone lprefix lprefix (\<lambda>ys. lmerge xs ys)"
by(simp add: monotone_lmerge[simplified])

lemma mcont_lmerge: "mcont (prod_lub lSup lSup) (rel_prod lprefix lprefix) lSup lprefix (case_prod lmerge)"
apply(rule llist.fixp_preserves_mcont2[OF lmerge_mono lmerge_conv_fixp]) 
apply(erule conjE|rule allI conjI cont_intro|simp|erule allE, erule llist.mcont2mcont)+
done

lemma mcont2mcont_lmerge1 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lmerge1: "mcont lSup lprefix lSup lprefix (\<lambda>xs. lmerge xs ys)"
by(simp add: mcont_lmerge[simplified])

lemma mcont2mcont_lmerge2 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lmerge2: "mcont lSup lprefix lSup lprefix (\<lambda>ys. lmerge xs ys)"
by(simp add: mcont_lmerge[simplified])

lemma lfinite_lmergeI [simp]: "\<lbrakk> lfinite xs; lfinite ys \<rbrakk> \<Longrightarrow> lfinite (lmerge xs ys)"
proof(induction arbitrary: ys rule: lfinite_induct)
  case (LCons xs)
  from LCons.prems LCons.hyps LCons.IH
  show ?case by induct(clarsimp simp add: not_lnull_conv lmerge_simps)+
qed simp

lemma linfinite_lmerge [simp]: "\<lbrakk> \<not> lfinite xs; \<not> lfinite ys \<rbrakk> \<Longrightarrow> \<not> lfinite (lmerge xs ys)"
by(auto dest: lfinite_lmergeD)

lemma llength_lmerge_above: "llength xs \<sqinter> llength ys \<le> llength (lmerge xs ys)"
proof(induction xs arbitrary: ys)
  case (LCons x xs)
  show ?case
  proof(induct ys)
    case LCons thus ?case using LCons.IH
      by(fastforce simp add: bot_enat_def[symmetric] lmerge_simps le_infI1 le_infI2 intro: order_trans[rotated])
  qed(simp_all add: bot_enat_def[symmetric])
qed(simp_all add: bot_enat_def[symmetric])

end

context linorder begin

lemma in_lset_lmergeI1:
  "\<lbrakk> x \<in> lset xs; lsorted xs; \<not> lfinite ys; \<exists>y\<in>lset ys. x \<le> y \<rbrakk>
  \<Longrightarrow> x \<in> lset (lmerge xs ys)"
proof(induction arbitrary: ys rule: lset_induct)
  case (find xs)
  then obtain y where "y \<in> lset ys" "x \<le> y" by blast
  thus ?case by induct(auto simp add: lmerge_simps not_less)
next
  case (step x' xs)
  then obtain y where "y \<in> lset ys" "x \<le> y" by blast
  moreover from `lsorted (LCons x' xs)` `x \<in> lset xs` `x \<noteq> x'`
  have "x' < x" "lsorted xs" by(auto simp add: lsorted_LCons)
  ultimately show ?case using `\<not> lfinite ys` 
    by induct(auto 4 3 simp add: lmerge_simps `x \<noteq> x'` not_less intro: step.IH dest: in_lset_lmergeD)
qed

lemma in_lset_lmergeI2:
  "\<lbrakk> x \<in> lset ys; lsorted ys; \<not> lfinite xs; \<exists>y\<in>lset xs. x \<le> y \<rbrakk>
  \<Longrightarrow> x \<in> lset (lmerge xs ys)"
proof(induction arbitrary: xs rule: lset_induct)
  case (find ys)
  then obtain y where "y \<in> lset xs" "x \<le> y" by blast
  thus ?case by induct(auto simp add: lmerge_simps not_less)
next
  case (step x' ys)
  then obtain y where "y \<in> lset xs" "x \<le> y" by blast
  moreover from `lsorted (LCons x' ys)` `x \<in> lset ys` `x \<noteq> x'`
  have "x' < x" "lsorted ys" by(auto simp add: lsorted_LCons)
  ultimately show ?case using `\<not> lfinite xs` 
    by induct(auto 4 3 simp add: lmerge_simps `x \<noteq> x'` not_less intro: step.IH dest: in_lset_lmergeD)
qed

lemma lsorted_lmerge: "\<lbrakk> lsorted xs; lsorted ys \<rbrakk> \<Longrightarrow> lsorted (lmerge xs ys)"
proof(coinduction arbitrary: xs ys)
  case (lsorted xs ys)
  have ?lhd using lsorted
    by(auto 4 3 simp add: not_lnull_conv lsorted_LCons lhd_lmerge ltl_lmerge dest!: in_lset_lmergeD)
  moreover have ?ltl using lsorted by(auto simp add: ltl_lmerge intro: lsorted_ltlI)
  ultimately show ?case ..
qed

lemma ldistinct_lmerge: 
  "\<lbrakk> lsorted xs; lsorted ys; ldistinct xs; ldistinct ys \<rbrakk>
  \<Longrightarrow> ldistinct (lmerge xs ys)"
by(coinduction arbitrary: xs ys)(auto 4 3 simp add: lhd_lmerge ltl_lmerge not_lnull_conv lsorted_LCons not_less dest!: in_lset_lmergeD dest: antisym)

end


partial_function (llist) hamming' :: "unit \<Rightarrow> nat llist"
where
  "hamming' _ = 
   LCons 1 (lmerge (lmap (( * ) 2) (hamming' ())) (lmerge (lmap (( * ) 3) (hamming' ())) (lmap (( * ) 5) (hamming' ()))))"

definition hamming :: "nat llist"
where "hamming = hamming' ()"

lemma lnull_hamming [simp]: "\<not> lnull hamming"
unfolding hamming_def by(subst hamming'.simps) simp

lemma hamming_eq_LNil_iff [simp]: "hamming = LNil \<longleftrightarrow> False"
using lnull_hamming unfolding lnull_def by simp

lemma lhd_hamming [simp]: "lhd hamming = 1"
unfolding hamming_def by(subst hamming'.simps) simp

lemma ltl_hamming [simp]:
  "ltl hamming = lmerge (lmap (( * ) 2) hamming) (lmerge (lmap (( * ) 3) hamming) (lmap (( * ) 5) hamming))"
unfolding hamming_def by(subst hamming'.simps) simp

lemma hamming_unfold:
  "hamming = LCons 1 (lmerge (lmap (( * ) 2) hamming) (lmerge (lmap (( * ) 3) hamming) (lmap (( * ) 5) hamming)))"
by(rule llist.expand) simp_all

definition smooth :: "nat \<Rightarrow> bool"
where "smooth n \<longleftrightarrow> (\<forall>p. prime p \<longrightarrow> p dvd n \<longrightarrow> p \<le> 5)"

lemma smooth_0 [simp]: "\<not> smooth 0"
by(auto simp add: smooth_def intro: exI[where x=7])

lemma smooth_Suc0 [simp]: "smooth (Suc 0)"
by(auto simp add: smooth_def)

lemma smooth_gt0: "smooth n \<Longrightarrow> n > 0"
by(cases n) simp_all

lemma smooth_ge_Suc0: "smooth n \<Longrightarrow> n \<ge> Suc 0"
by(cases n) simp_all

lemma prime_nat_dvdD: "prime p \<Longrightarrow> (n :: nat) dvd p \<Longrightarrow> n = 1 \<or> n = p"
unfolding prime_nat_iff by simp

lemma smooth_times [simp]: "smooth (x * y) \<longleftrightarrow> smooth x \<and> smooth y"
by(auto simp add: smooth_def prime_dvd_mult_iff)

lemma smooth2 [simp]: "smooth 2"
by(auto simp add: smooth_def dest: prime_nat_dvdD[of 2, simplified])

lemma smooth3 [simp]: "smooth 3"
by(auto simp add: smooth_def dest: prime_nat_dvdD[of 3, simplified])

lemma smooth5 [simp]: "smooth 5"
by(auto simp add: smooth_def dest: prime_nat_dvdD[of 5, simplified])

lemma hamming_in_smooth: "lset hamming \<subseteq> {n. smooth n}"
unfolding hamming_def by(induct rule: hamming'.fixp_induct)(auto 6 6 dest: in_lset_lmergeD)

lemma lfinite_hamming [simp]: "\<not> lfinite hamming"
proof
  assume "lfinite hamming"
  then obtain n where n: "llength hamming = enat n" unfolding lfinite_conv_llength_enat by fastforce
  have "llength (lmap (( * ) 3) hamming) \<sqinter> llength (lmap (( * ) 5) hamming) \<le> llength (lmerge (lmap (( * ) 3) hamming) (lmap (( * ) 5) hamming))"
    by(rule llength_lmerge_above)
  hence "llength hamming \<le> \<dots>" by simp
  moreover have "llength (lmap (( * ) 2) hamming) \<sqinter> \<dots> \<le>
    llength (lmerge (lmap (( * ) 2) hamming) (lmerge (lmap (( * ) 3) hamming) (lmap (( * ) 5) hamming)))"
    by(rule llength_lmerge_above)
  ultimately have "llength hamming \<le> \<dots>" by(simp add: inf.absorb1)
  also from n have "\<dots> < enat n"
    by(subst (asm) hamming_unfold)(cases n, auto simp add: zero_enat_def[symmetric] eSuc_enat[symmetric])
  finally show False unfolding n by simp
qed

lemma lsorted_hamming [simp]: "lsorted hamming"
  and ldistinct_hamming [simp]: "ldistinct hamming"
proof -
  have "lsorted hamming \<and> ldistinct hamming \<and> lset hamming \<subseteq> {1..}"
    unfolding hamming_def
    by(induct rule: hamming'.fixp_induct)(auto 6 6 simp add: lsorted_LCons dest: in_lset_lmergeD intro: smooth_ge_Suc0 lsorted_lmerge lsorted_lmap monotoneI ldistinct_lmerge inj_onI)
  thus "lsorted hamming" "ldistinct hamming" by simp_all
qed

lemma smooth_hamming:
  assumes "smooth n"
  shows "n \<in> lset hamming"
using assms
proof(induction n rule: less_induct)
  have [simp]:
    "monotone (\<le>) (\<le>) (( * ) 2 :: nat \<Rightarrow> nat)" 
    "monotone (\<le>) (\<le>) (( * ) 3 :: nat \<Rightarrow> nat)" 
    "monotone (\<le>) (\<le>) (( * ) 5 :: nat \<Rightarrow> nat)" 
    by(simp_all add: monotone_def)

  case (less n)
  show ?case
  proof(cases "n > 1")
    case False
    moreover from `smooth n` have "n \<noteq> 0" by(rule contrapos_pn) simp
    ultimately have "n = 1" by(simp)
    thus ?thesis by(subst hamming_unfold) simp
  next
    case True
    hence "\<exists>p. prime p \<and> p dvd n" by(metis less_numeral_extra(4) prime_factor_nat)
    with `smooth n` obtain p where "prime p" "p dvd n" "p \<le> 5" by(auto simp add: smooth_def)
    from `p dvd n` obtain n' where n: "n = p * n'" by(auto simp add: dvd_def)
    with `smooth n` `prime p` have "smooth n'" by(simp add: smooth_def)
    with `prime p` n have "n' < n" by(simp add: smooth_gt0 prime_gt_Suc_0_nat)
    hence n': "n' \<in> lset hamming" using `smooth n'` by(rule less.IH)

    from \<open>p \<le> 5\<close> have "p = 0 \<or> p = 1 \<or> p = 2 \<or> p = 3 \<or> p = 4 \<or> p = 5"
      by presburger
    with `prime p` have "p = 2 \<or> p = 3 \<or> p = 5" by auto
    thus ?thesis
    proof(elim disjE)
      assume "p = 2"
      with n n' show ?thesis
        by(subst hamming_unfold)(simp_all add: in_lset_lmergeI1 not_less lsorted_lmap bexI[where x="n'"] bexI[where x="3*n'"])
    next
      assume "p = 3"
      moreover with n `smooth n'` have "2 * n' < n" by(simp add: smooth_gt0)
      hence "2 * n' \<in> lset hamming" by(rule less.IH)(simp add: `smooth n'`)
      ultimately show ?thesis using n n'
        by(subst hamming_unfold)(auto 4 4 simp add: not_less lsorted_lmap lsorted_lmerge intro: in_lset_lmergeI1 in_lset_lmergeI2 bexI[where x="4*n'"] bexI[where x="5*n'"])
    next
      assume "p = 5"
      moreover with n `smooth n'` have "2 * (2 * n') < n" by(simp add: smooth_gt0)
      hence "2 * (2 * n') \<in> lset hamming" by(rule less.IH)(simp only: smooth_times smooth2 `smooth n'` simp_thms)
      moreover from `p = 5` n `smooth n'` have "3 * n' < n" by(simp add: smooth_gt0)
      hence "3 * n' \<in> lset hamming" by(rule less.IH)(simp add: `smooth n'`)
      ultimately show ?thesis using n n'
        by(subst hamming_unfold)(auto 4 4 simp add: lsorted_lmap lsorted_lmerge intro: in_lset_lmergeI2 bexI[where x="9*n'"] bexI[where x="8 * n'"])
    qed
  qed
qed

corollary hamming_smooth: "lset hamming = {n. smooth n}"
using hamming_in_smooth by(blast intro: smooth_hamming)

lemma hamming_THE:
  "(THE xs. lsorted xs \<and> ldistinct xs \<and> lset xs = {n. smooth n}) = hamming"
by(rule the_equality)(simp_all add: hamming_smooth lsorted_ldistinct_lset_unique)

end
