(*  Title:      Coinductive_List.thy
    Author:     Andreas Lochbihler
*)

section {* Coinductive lists and their operations *}

theory Coinductive_List
imports
  "HOL-Library.Infinite_Set"
  "HOL-Library.Sublist"
  "HOL-Library.Simps_Case_Conv"
  Coinductive_Nat
begin

subsection {* Auxiliary lemmata *}

lemma funpow_Suc_conv [simp]: "(Suc ^^ n) m = m + n"
by(induct n arbitrary: m) simp_all

lemma wlog_linorder_le [consumes 0, case_names le symmetry]:
  assumes le: "\<And>a b :: 'a :: linorder. a \<le> b \<Longrightarrow> P a b"
  and sym: "P b a \<Longrightarrow> P a b"
  shows "P a b"
proof(cases "a \<le> b")
  case True thus ?thesis by(rule le)
next
  case False
  hence "b \<le> a" by simp
  hence "P b a" by(rule le)
  thus ?thesis by(rule sym)
qed

subsection {* Type definition *}

codatatype (lset: 'a) llist =
    lnull: LNil
  | LCons (lhd: 'a) (ltl: "'a llist")
for
  map: lmap
  rel: llist_all2
where
  "lhd LNil = undefined"
| "ltl LNil = LNil"


text {*
  Coiterator setup.
*}

primcorec unfold_llist :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b llist" where
  "p a \<Longrightarrow> unfold_llist p g21 g22 a = LNil" |
  "_ \<Longrightarrow> unfold_llist p g21 g22 a = LCons (g21 a) (unfold_llist p g21 g22 (g22 a))"

declare
  unfold_llist.ctr(1) [simp]
  llist.corec(1) [simp]

text {*
  The following setup should be done by the BNF package.
*}

text {* congruence rule *}

declare llist.map_cong [cong]

text {* Code generator setup *}

lemma corec_llist_never_stop: "corec_llist IS_LNIL LHD (\<lambda>_. False) MORE LTL x = unfold_llist IS_LNIL LHD LTL x"
by(coinduction arbitrary: x) auto

text {* lemmas about generated constants *}

lemma eq_LConsD: "xs = LCons y ys \<Longrightarrow> xs \<noteq> LNil \<and> lhd xs = y \<and> ltl xs = ys"
by auto

lemma
  shows LNil_eq_lmap: "LNil = lmap f xs \<longleftrightarrow> xs = LNil"
  and lmap_eq_LNil: "lmap f xs = LNil \<longleftrightarrow> xs = LNil"
by(cases xs,simp_all)+

declare llist.map_sel(1)[simp]

lemma ltl_lmap[simp]: "ltl (lmap f xs) = lmap f (ltl xs)"
by(cases xs, simp_all)

declare llist.map_ident[simp]

lemma lmap_eq_LCons_conv:
  "lmap f xs = LCons y ys \<longleftrightarrow>
  (\<exists>x xs'. xs = LCons x xs' \<and> y = f x \<and> ys = lmap f xs')"
by(cases xs)(auto)

lemma lmap_conv_unfold_llist:
  "lmap f = unfold_llist (\<lambda>xs. xs = LNil) (f \<circ> lhd) ltl" (is "?lhs = ?rhs")
proof
  fix x
  show "?lhs x = ?rhs x" by(coinduction arbitrary: x) auto
qed

lemma lmap_unfold_llist:
  "lmap f (unfold_llist IS_LNIL LHD LTL b) = unfold_llist IS_LNIL (f \<circ> LHD) LTL b"
by(coinduction arbitrary: b) auto

lemma lmap_corec_llist:
  "lmap f (corec_llist IS_LNIL LHD endORmore TTL_end TTL_more b) =
   corec_llist IS_LNIL (f \<circ> LHD) endORmore (lmap f \<circ> TTL_end) TTL_more b"
by(coinduction arbitrary: b rule: llist.coinduct_strong) auto

lemma unfold_llist_ltl_unroll:
  "unfold_llist IS_LNIL LHD LTL (LTL b) = unfold_llist (IS_LNIL \<circ> LTL) (LHD \<circ> LTL) LTL b"
by(coinduction arbitrary: b) auto

lemma ltl_unfold_llist:
  "ltl (unfold_llist IS_LNIL LHD LTL a) =
  (if IS_LNIL a then LNil else unfold_llist IS_LNIL LHD LTL (LTL a))"
by(simp)

lemma unfold_llist_eq_LCons [simp]:
  "unfold_llist IS_LNIL LHD LTL b = LCons x xs \<longleftrightarrow>
  \<not> IS_LNIL b \<and> x = LHD b \<and> xs = unfold_llist IS_LNIL LHD LTL (LTL b)"
by(subst unfold_llist.code) auto

lemma unfold_llist_id [simp]: "unfold_llist lnull lhd ltl xs = xs"
by(coinduction arbitrary: xs) simp_all

lemma lset_eq_empty [simp]: "lset xs = {} \<longleftrightarrow> lnull xs"
by(cases xs) simp_all

declare llist.set_sel(1)[simp]

lemma lset_ltl: "lset (ltl xs) \<subseteq> lset xs"
by(cases xs) auto

lemma in_lset_ltlD: "x \<in> lset (ltl xs) \<Longrightarrow> x \<in> lset xs"
using lset_ltl[of xs] by auto

text {* induction rules *}

theorem llist_set_induct[consumes 1, case_names find step]:
  assumes "x \<in> lset xs" and "\<And>xs. \<not> lnull xs \<Longrightarrow> P (lhd xs) xs"
  and "\<And>xs y. \<lbrakk>\<not> lnull xs; y \<in> lset (ltl xs); P y (ltl xs)\<rbrakk> \<Longrightarrow> P y xs"
  shows "P x xs"
using assms by(induct)(fastforce simp del: llist.disc(2) iff: llist.disc(2), auto)

text {* Test quickcheck setup *}

lemma "\<And>xs. xs = LNil"
quickcheck[random, expect=counterexample]
quickcheck[exhaustive, expect=counterexample]
oops

lemma "LCons x xs = LCons x xs"
quickcheck[narrowing, expect=no_counterexample]
oops

subsection {* Properties of predefined functions *}

lemmas lhd_LCons = llist.sel(1)
lemmas ltl_simps = llist.sel(2,3)

lemmas lhd_LCons_ltl = llist.collapse(2)

lemma lnull_ltlI [simp]: "lnull xs \<Longrightarrow> lnull (ltl xs)"
unfolding lnull_def by simp

lemma neq_LNil_conv: "xs \<noteq> LNil \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs')"
by(cases xs) auto

lemma not_lnull_conv: "\<not> lnull xs \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs')"
unfolding lnull_def by(simp add: neq_LNil_conv)

lemma lset_LCons:
  "lset (LCons x xs) = insert x (lset xs)"
by simp

lemma lset_intros:
  "x \<in> lset (LCons x xs)"
  "x \<in> lset xs \<Longrightarrow> x \<in> lset (LCons x' xs)"
by simp_all

lemma lset_cases [elim?]:
  assumes "x \<in> lset xs"
  obtains xs' where "xs = LCons x xs'"
  | x' xs' where "xs = LCons x' xs'" "x \<in> lset xs'"
using assms by(cases xs) auto

lemma lset_induct' [consumes 1, case_names find step]:
  assumes major: "x \<in> lset xs"
  and 1: "\<And>xs. P (LCons x xs)"
  and 2: "\<And>x' xs. \<lbrakk> x \<in> lset xs; P xs \<rbrakk> \<Longrightarrow> P (LCons x' xs)"
  shows "P xs"
using major apply(induct y\<equiv>"x" xs rule: llist_set_induct)
using 1 2 by(auto simp add: not_lnull_conv)

lemma lset_induct [consumes 1, case_names find step, induct set: lset]:
  assumes major: "x \<in> lset xs"
  and find: "\<And>xs. P (LCons x xs)"
  and step: "\<And>x' xs. \<lbrakk> x \<in> lset xs; x \<noteq> x'; P xs \<rbrakk> \<Longrightarrow> P (LCons x' xs)"
  shows "P xs"
using major
apply(induct rule: lset_induct')
 apply(rule find)
apply(case_tac "x'=x")
apply(simp_all add: find step)
done

lemmas lset_LNil = llist.set(1)

lemma lset_lnull: "lnull xs \<Longrightarrow> lset xs = {}"
by(auto dest: llist.collapse)

text {* Alternative definition of @{term lset} for nitpick *}

inductive lsetp :: "'a llist \<Rightarrow> 'a \<Rightarrow> bool"
where
  "lsetp (LCons x xs) x"
| "lsetp xs x \<Longrightarrow> lsetp (LCons x' xs) x"

lemma lset_into_lsetp:
  "x \<in> lset xs \<Longrightarrow> lsetp xs x"
by(induct rule: lset_induct)(blast intro: lsetp.intros)+

lemma lsetp_into_lset:
  "lsetp xs x \<Longrightarrow> x \<in> lset xs"
by(induct rule: lsetp.induct)(blast intro: lset_intros)+

lemma lset_eq_lsetp [nitpick_unfold]:
  "lset xs = {x. lsetp xs x}"
by(auto intro: lset_into_lsetp dest: lsetp_into_lset)

hide_const (open) lsetp
hide_fact (open) lsetp.intros lsetp.cases lsetp.induct lset_into_lsetp lset_eq_lsetp

text {* code setup for @{term lset} *}

definition gen_lset :: "'a set \<Rightarrow> 'a llist \<Rightarrow> 'a set"
where "gen_lset A xs = A \<union> lset xs"

lemma gen_lset_code [code]:
  "gen_lset A LNil = A"
  "gen_lset A (LCons x xs) = gen_lset (insert x A) xs"
by(auto simp add: gen_lset_def)

lemma lset_code [code]:
  "lset = gen_lset {}"
by(simp add: gen_lset_def fun_eq_iff)

definition lmember :: "'a \<Rightarrow> 'a llist \<Rightarrow> bool"
where "lmember x xs \<longleftrightarrow> x \<in> lset xs"

lemma lmember_code [code]:
  "lmember x LNil \<longleftrightarrow> False"
  "lmember x (LCons y ys) \<longleftrightarrow> x = y \<or> lmember x ys"
by(simp_all add: lmember_def)

lemma lset_lmember [code_unfold]:
  "x \<in> lset xs \<longleftrightarrow> lmember x xs"
by(simp add: lmember_def)

lemmas lset_lmap [simp] = llist.set_map

subsection {* The subset of finite lazy lists @{term "lfinite"} *}

inductive lfinite :: "'a llist \<Rightarrow> bool"
where
  lfinite_LNil:  "lfinite LNil"
| lfinite_LConsI: "lfinite xs \<Longrightarrow> lfinite (LCons x xs)"

declare lfinite_LNil [iff]

lemma lnull_imp_lfinite [simp]: "lnull xs \<Longrightarrow> lfinite xs"
by(auto dest: llist.collapse)

lemma lfinite_LCons [simp]: "lfinite (LCons x xs) = lfinite xs"
by(auto elim: lfinite.cases intro: lfinite_LConsI)

lemma lfinite_ltl [simp]: "lfinite (ltl xs) = lfinite xs"
by(cases xs) simp_all

lemma lfinite_code [code]:
  "lfinite LNil = True"
  "lfinite (LCons x xs) = lfinite xs"
by simp_all

lemma lfinite_induct [consumes 1, case_names LNil LCons]:
  assumes lfinite: "lfinite xs"
  and LNil: "\<And>xs. lnull xs \<Longrightarrow> P xs"
  and LCons: "\<And>xs. \<lbrakk> lfinite xs; \<not> lnull xs; P (ltl xs) \<rbrakk> \<Longrightarrow> P xs"
  shows "P xs"
using lfinite by(induct)(auto intro: LCons LNil)

lemma lfinite_imp_finite_lset:
  assumes "lfinite xs"
  shows "finite (lset xs)"
using assms by induct auto

subsection {* Concatenating two lists: @{term "lappend"} *}

primcorec lappend :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lappend xs ys = (case xs of LNil \<Rightarrow> ys | LCons x xs' \<Rightarrow> LCons x (lappend xs' ys))"

simps_of_case lappend_code [code, simp, nitpick_simp]: lappend.code

lemmas lappend_LNil_LNil = lappend_code(1)[where ys = LNil]

lemma lappend_simps [simp]:
  shows lhd_lappend: "lhd (lappend xs ys) = (if lnull xs then lhd ys else lhd xs)"
  and ltl_lappend: "ltl (lappend xs ys) = (if lnull xs then ltl ys else lappend (ltl xs) ys)"
by(case_tac [!] xs) simp_all

lemma lnull_lappend [simp]:
  "lnull (lappend xs ys) \<longleftrightarrow> lnull xs \<and> lnull ys"
by(auto simp add: lappend_def)

lemma lappend_eq_LNil_iff:
  "lappend xs ys = LNil \<longleftrightarrow> xs = LNil \<and> ys = LNil"
using lnull_lappend unfolding lnull_def .

lemma LNil_eq_lappend_iff:
  "LNil = lappend xs ys \<longleftrightarrow> xs = LNil \<and> ys = LNil"
by(auto dest: sym simp add: lappend_eq_LNil_iff)

lemma lappend_LNil2 [simp]: "lappend xs LNil = xs"
by(coinduction arbitrary: xs) simp_all

lemma shows lappend_lnull1: "lnull xs \<Longrightarrow> lappend xs ys = ys"
  and lappend_lnull2: "lnull ys \<Longrightarrow> lappend xs ys = xs"
unfolding lnull_def by simp_all

lemma lappend_assoc: "lappend (lappend xs ys) zs = lappend xs (lappend ys zs)"
by(coinduction arbitrary: xs rule: llist.coinduct_strong) auto

lemma lmap_lappend_distrib:
  "lmap f (lappend xs ys) = lappend (lmap f xs) (lmap f ys)"
by(coinduction arbitrary: xs rule: llist.coinduct_strong) auto

lemma lappend_snocL1_conv_LCons2:
  "lappend (lappend xs (LCons y LNil)) ys = lappend xs (LCons y ys)"
by(simp add: lappend_assoc)

lemma lappend_ltl: "\<not> lnull xs \<Longrightarrow> lappend (ltl xs) ys = ltl (lappend xs ys)"
by simp

lemma lfinite_lappend [simp]:
  "lfinite (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> lfinite ys"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs thus ?rhs
  proof(induct zs\<equiv>"lappend xs ys" arbitrary: xs ys)
    case lfinite_LNil
    thus ?case by(simp add: LNil_eq_lappend_iff)
  next
    case (lfinite_LConsI zs z)
    thus ?case by(cases xs)(cases ys, simp_all)
  qed
next
  assume ?rhs (is "?xs \<and> ?ys")
  then obtain ?xs ?ys ..
  thus ?lhs by induct simp_all
qed

lemma lappend_inf: "\<not> lfinite xs \<Longrightarrow> lappend xs ys = xs"
by(coinduction arbitrary: xs) auto

lemma lfinite_lmap [simp]:
  "lfinite (lmap f xs) = lfinite xs"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct zs\<equiv>"lmap f xs" arbitrary: xs rule: lfinite_induct) fastforce+
next
  assume ?rhs
  thus ?lhs by(induct) simp_all
qed

lemma lset_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lset (lappend xs ys) = lset xs \<union> lset ys"
by(induct rule: lfinite.induct) auto

lemma lset_lappend: "lset (lappend xs ys) \<subseteq> lset xs \<union> lset ys"
proof(cases "lfinite xs")
  case True
  thus ?thesis by simp
next
  case False
  thus ?thesis by(auto simp add: lappend_inf)
qed

lemma lset_lappend1: "lset xs \<subseteq> lset (lappend xs ys)"
by(rule subsetI)(erule lset_induct, simp_all)

lemma lset_lappend_conv: "lset (lappend xs ys) = (if lfinite xs then lset xs \<union> lset ys else lset xs)"
by(simp add: lappend_inf)

lemma in_lset_lappend_iff: "x \<in> lset (lappend xs ys) \<longleftrightarrow> x \<in> lset xs \<or> lfinite xs \<and> x \<in> lset ys"
by(simp add: lset_lappend_conv)

lemma split_llist_first:
  assumes "x \<in> lset xs"
  shows "\<exists>ys zs. xs = lappend ys (LCons x zs) \<and> lfinite ys \<and> x \<notin> lset ys"
using assms
proof(induct)
  case find thus ?case by(auto intro: exI[where x=LNil])
next
  case step thus ?case by(fastforce intro: exI[where x="LCons a b" for a b])
qed

lemma split_llist: "x \<in> lset xs \<Longrightarrow> \<exists>ys zs. xs = lappend ys (LCons x zs) \<and> lfinite ys"
by(blast dest: split_llist_first)

subsection {* The prefix ordering on lazy lists: @{term "lprefix"} *}

coinductive lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool" (infix "\<sqsubseteq>" 65)
where
  LNil_lprefix [simp, intro!]: "LNil \<sqsubseteq> xs"
| Le_LCons: "xs \<sqsubseteq> ys \<Longrightarrow> LCons x xs \<sqsubseteq> LCons x ys"

lemma lprefixI [consumes 1, case_names lprefix,
                case_conclusion lprefix LeLNil LeLCons]:
  assumes major: "(xs, ys) \<in> X"
  and step:
      "\<And>xs ys. (xs, ys) \<in> X
       \<Longrightarrow> lnull xs \<or> (\<exists>x xs' ys'. xs = LCons x xs' \<and> ys = LCons x ys' \<and>
                                   ((xs', ys') \<in> X \<or> xs' \<sqsubseteq> ys'))"
  shows "xs \<sqsubseteq> ys"
using major by(rule lprefix.coinduct)(auto dest: step)

lemma lprefix_coinduct [consumes 1, case_names lprefix, case_conclusion lprefix LNil LCons, coinduct pred: lprefix]:
  assumes major: "P xs ys"
  and step: "\<And>xs ys. P xs ys
    \<Longrightarrow> (lnull ys \<longrightarrow> lnull xs) \<and>
       (\<not> lnull xs \<longrightarrow> \<not> lnull ys \<longrightarrow> lhd xs = lhd ys \<and> (P (ltl xs) (ltl ys) \<or> ltl xs \<sqsubseteq> ltl ys))"
  shows "xs \<sqsubseteq> ys"
proof -
  from major have "(xs, ys) \<in> {(xs, ys). P xs ys}" by simp
  thus ?thesis
  proof(coinduct rule: lprefixI)
    case (lprefix xs ys)
    hence "P xs ys" by simp
    from step[OF this] show ?case
      by(cases xs)(auto simp add: not_lnull_conv)
  qed
qed

lemma lprefix_refl [intro, simp]: "xs \<sqsubseteq> xs"
by(coinduction arbitrary: xs) simp_all

lemma lprefix_LNil [simp]: "xs \<sqsubseteq> LNil \<longleftrightarrow> lnull xs"
unfolding lnull_def by(subst lprefix.simps)simp

lemma lprefix_lnull: "lnull ys \<Longrightarrow> xs \<sqsubseteq> ys \<longleftrightarrow> lnull xs"
unfolding lnull_def by auto

lemma lnull_lprefix: "lnull xs \<Longrightarrow> lprefix xs ys"
by(simp add: lnull_def)

lemma lprefix_LCons_conv:
  "xs \<sqsubseteq> LCons y ys \<longleftrightarrow>
   xs = LNil \<or> (\<exists>xs'. xs = LCons y xs' \<and> xs' \<sqsubseteq> ys)"
by(subst lprefix.simps) simp

lemma LCons_lprefix_LCons [simp]:
  "LCons x xs \<sqsubseteq> LCons y ys \<longleftrightarrow> x = y \<and> xs \<sqsubseteq> ys"
by(simp add: lprefix_LCons_conv)

lemma LCons_lprefix_conv:
  "LCons x xs \<sqsubseteq> ys \<longleftrightarrow> (\<exists>ys'. ys = LCons x ys' \<and> xs \<sqsubseteq> ys')"
by(cases ys)(auto)

lemma lprefix_ltlI: "xs \<sqsubseteq> ys \<Longrightarrow> ltl xs \<sqsubseteq> ltl ys"
by(cases ys)(auto simp add: lprefix_LCons_conv)

lemma lprefix_code [code]:
  "LNil \<sqsubseteq> ys \<longleftrightarrow> True"
  "LCons x xs \<sqsubseteq> LNil \<longleftrightarrow> False"
  "LCons x xs \<sqsubseteq> LCons y ys \<longleftrightarrow> x = y \<and> xs \<sqsubseteq> ys"
by simp_all

lemma lprefix_lhdD: "\<lbrakk> xs \<sqsubseteq> ys; \<not> lnull xs \<rbrakk> \<Longrightarrow> lhd xs = lhd ys"
by(clarsimp simp add: not_lnull_conv LCons_lprefix_conv)

lemma lprefix_lnullD: "\<lbrakk> xs \<sqsubseteq> ys; lnull ys \<rbrakk> \<Longrightarrow> lnull xs"
by(auto elim: lprefix.cases)

lemma lprefix_not_lnullD: "\<lbrakk> xs \<sqsubseteq> ys; \<not> lnull xs \<rbrakk> \<Longrightarrow> \<not> lnull ys"
by(auto elim: lprefix.cases)

lemma lprefix_expand:
  "(\<not> lnull xs \<Longrightarrow> \<not> lnull ys \<and> lhd xs = lhd ys \<and> ltl xs \<sqsubseteq> ltl ys) \<Longrightarrow> xs \<sqsubseteq> ys"
by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(simp_all)

lemma lprefix_antisym:
  "\<lbrakk> xs \<sqsubseteq> ys; ys \<sqsubseteq> xs \<rbrakk> \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv lprefix_lnull)

lemma lprefix_trans [trans]:
  "\<lbrakk> xs \<sqsubseteq> ys; ys \<sqsubseteq> zs \<rbrakk> \<Longrightarrow> xs \<sqsubseteq> zs"
by(coinduction arbitrary: xs ys zs)(auto 4 3 dest: lprefix_lnullD lprefix_lhdD intro: lprefix_ltlI)

lemma preorder_lprefix [cont_intro]:
  "class.preorder (\<sqsubseteq>) (mk_less (\<sqsubseteq>))"
by(unfold_locales)(auto simp add: mk_less_def intro: lprefix_trans)

lemma lprefix_lsetD:
  assumes "xs \<sqsubseteq> ys"
  shows "lset xs \<subseteq> lset ys"
proof
  fix x
  assume "x \<in> lset xs"
  thus "x \<in> lset ys" using assms
    by(induct arbitrary: ys)(auto simp add: LCons_lprefix_conv)
qed

lemma lprefix_lappend_sameI:
  assumes "xs \<sqsubseteq> ys"
  shows "lappend zs xs \<sqsubseteq> lappend zs ys"
proof(cases "lfinite zs")
  case True
  thus ?thesis using assms by induct auto
qed(simp add: lappend_inf)

lemma not_lfinite_lprefix_conv_eq:
  assumes nfin: "\<not> lfinite xs"
  shows "xs \<sqsubseteq> ys \<longleftrightarrow> xs = ys"
proof
  assume "xs \<sqsubseteq> ys"
  with nfin show "xs = ys"
    by(coinduction arbitrary: xs ys)(auto dest: lprefix_lnullD lprefix_lhdD intro: lprefix_ltlI)
qed simp

lemma lprefix_lappend: "xs \<sqsubseteq> lappend xs ys"
by(coinduction arbitrary: xs) auto

lemma lprefix_down_linear:
  assumes "xs \<sqsubseteq> zs" "ys \<sqsubseteq> zs"
  shows "xs \<sqsubseteq> ys \<or> ys \<sqsubseteq> xs"
proof(rule disjCI)
  assume "\<not> ys \<sqsubseteq> xs"
  with assms show "xs \<sqsubseteq> ys"
    by(coinduction arbitrary: xs ys zs)(auto simp add: not_lnull_conv LCons_lprefix_conv, simp add: lnull_def)
qed

lemma lprefix_lappend_same [simp]:
  "lappend xs ys \<sqsubseteq> lappend xs zs \<longleftrightarrow> (lfinite xs \<longrightarrow> ys \<sqsubseteq> zs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  show "?rhs"
  proof
    assume "lfinite xs"
    thus "ys \<sqsubseteq> zs" using `?lhs` by(induct) simp_all
  qed
next
  assume "?rhs"
  show ?lhs
  proof(cases "lfinite xs")
    case True
    hence yszs: "ys \<sqsubseteq> zs" by(rule `?rhs`[rule_format])
    from True show ?thesis by induct (simp_all add: yszs)
  next
    case False thus ?thesis by(simp add: lappend_inf)
  qed
qed

subsection {* Setup for partial\_function *}

primcorec lSup :: "'a llist set \<Rightarrow> 'a llist"
where
  "lSup A =
  (if \<forall>x\<in>A. lnull x then LNil
   else LCons (THE x. x \<in> lhd ` (A \<inter> {xs. \<not> lnull xs})) (lSup (ltl ` (A \<inter> {xs. \<not> lnull xs}))))"

declare lSup.simps[simp del]

lemma lnull_lSup [simp]: "lnull (lSup A) \<longleftrightarrow> (\<forall>x\<in>A. lnull x)"
by(simp add: lSup_def)

lemma lhd_lSup [simp]: "\<exists>x\<in>A. \<not> lnull x \<Longrightarrow> lhd (lSup A) = (THE x. x \<in> lhd ` (A \<inter> {xs. \<not> lnull xs}))"
by(auto simp add: lSup_def)

lemma ltl_lSup [simp]: "ltl (lSup A) = lSup (ltl ` (A \<inter> {xs. \<not> lnull xs}))"
by(cases "\<forall>xs\<in>A. lnull xs")(auto 4 3 simp add: lSup_def intro: llist.expand)

lemma lhd_lSup_eq:
  assumes chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
  shows "\<lbrakk> xs \<in> Y; \<not> lnull xs \<rbrakk> \<Longrightarrow> lhd (lSup Y) = lhd xs"
by(subst lhd_lSup)(auto 4 3 dest: chainD[OF chain] lprefix_lhdD intro!: the_equality)

lemma lSup_empty [simp]: "lSup {} = LNil"
by(simp add: lSup_def)

lemma lSup_singleton [simp]: "lSup {xs} = xs"
by(coinduction arbitrary: xs) simp_all

lemma LCons_image_Int_not_lnull: "(LCons x ` A \<inter> {xs. \<not> lnull xs}) = LCons x ` A"
by auto

lemma lSup_LCons: "A \<noteq> {} \<Longrightarrow> lSup (LCons x ` A) = LCons x (lSup A)"
by(rule llist.expand)(auto simp add: image_image lhd_lSup exI LCons_image_Int_not_lnull intro!: the_equality)

lemma lSup_eq_LCons_iff:
  "lSup Y = LCons x xs \<longleftrightarrow> (\<exists>x\<in>Y. \<not> lnull x) \<and> x = (THE x. x \<in> lhd ` (Y \<inter> {xs. \<not> lnull xs})) \<and> xs = lSup (ltl ` (Y \<inter> {xs. \<not> lnull xs}))"
by(auto dest: eq_LConsD simp add: lnull_def[symmetric] intro: llist.expand)

lemma lSup_insert_LNil: "lSup (insert LNil Y) = lSup Y"
by(rule llist.expand) simp_all

lemma lSup_minus_LNil: "lSup (Y - {LNil}) = lSup Y"
using lSup_insert_LNil[where Y="Y - {LNil}", symmetric]
by(cases "LNil \<in> Y")(simp_all add: insert_absorb)

lemma chain_lprefix_ltl:
  assumes chain: "Complete_Partial_Order.chain (\<sqsubseteq>) A"
  shows "Complete_Partial_Order.chain (\<sqsubseteq>) (ltl ` (A \<inter> {xs. \<not> lnull xs}))"
by(auto intro!: chainI dest: chainD[OF chain] intro: lprefix_ltlI)

lemma lSup_finite_prefixes: "lSup {ys. ys \<sqsubseteq> xs \<and> lfinite ys} = xs" (is "lSup (?C xs) = _")
proof(coinduction arbitrary: xs)
  case (Eq_llist xs)
  have ?lnull
    by(cases xs)(auto simp add: lprefix_LCons_conv)
  moreover
  have "\<not> lnull xs \<Longrightarrow> ltl ` ({ys. ys \<sqsubseteq> xs \<and> lfinite ys} \<inter> {xs. \<not> lnull xs}) = {ys. ys \<sqsubseteq> ltl xs \<and> lfinite ys}"
    by(auto 4 4 intro!: rev_image_eqI[where x="LCons (lhd xs) ys" for ys] intro: llist.expand lprefix_ltlI simp add: LCons_lprefix_conv)
  hence ?LCons by(auto 4 3 intro!: the_equality dest: lprefix_lhdD intro: rev_image_eqI)
  ultimately show ?case ..
qed

lemma lSup_finite_gen_prefixes:
  assumes "zs \<sqsubseteq> xs" "lfinite zs"
  shows "lSup {ys. ys \<sqsubseteq> xs \<and> zs \<sqsubseteq> ys \<and> lfinite ys} = xs"
using `lfinite zs` `zs \<sqsubseteq> xs`
proof(induction arbitrary: xs)
  case lfinite_LNil
  thus ?case by(simp add: lSup_finite_prefixes)
next
  case (lfinite_LConsI zs z)
  from `LCons z zs \<sqsubseteq> xs` obtain xs' where xs: "xs = LCons z xs'"
    and "zs \<sqsubseteq> xs'" by(auto simp add: LCons_lprefix_conv)
  show ?case (is "?lhs = ?rhs")
  proof(rule llist.expand)
    show "lnull ?lhs = lnull ?rhs" using xs lfinite_LConsI
      by(auto 4 3 simp add: lprefix_LCons_conv del: disjCI intro: disjI2)
  next
    assume lnull: "\<not> lnull ?lhs" "\<not> lnull ?rhs"
    have "lhd ?lhs = lhd ?rhs" using lnull xs
      by(auto intro!: rev_image_eqI simp add: LCons_lprefix_conv)
    moreover
    have "ltl ` ({ys. ys \<sqsubseteq> xs \<and> LCons z zs \<sqsubseteq> ys \<and> lfinite ys} \<inter> {xs. \<not> lnull xs}) =
          {ys. ys \<sqsubseteq> xs' \<and> zs \<sqsubseteq> ys \<and> lfinite ys}"
      using xs `\<not> lnull ?rhs`
      by(auto 4 3 simp add: lprefix_LCons_conv intro: rev_image_eqI del: disjCI intro: disjI2)
    hence "ltl ?lhs = ltl ?rhs" using lfinite_LConsI.IH[OF `zs \<sqsubseteq> xs'`] xs by simp
    ultimately show "lhd ?lhs = lhd ?rhs \<and> ltl ?lhs = ltl ?rhs" ..
  qed
qed

lemma lSup_strict_prefixes:
  "\<not> lfinite xs \<Longrightarrow> lSup {ys. ys \<sqsubseteq> xs \<and> ys \<noteq> xs} = xs"
  (is "_ \<Longrightarrow> lSup (?C xs) = _")
proof(coinduction arbitrary: xs)
  case (Eq_llist xs)
  then obtain x x' xs' where xs: "xs = LCons x (LCons x' xs')" "\<not> lfinite xs'"
    by(cases xs)(simp, rename_tac xs', case_tac xs', auto)
  hence ?lnull by(auto intro: exI[where x="LCons x (LCons x' LNil)"])
  moreover hence "\<not> lnull (lSup {ys. ys \<sqsubseteq> xs \<and> ys \<noteq> xs})" using xs by auto
  hence "lhd (lSup {ys. ys \<sqsubseteq> xs \<and> ys \<noteq> xs}) = lhd xs" using xs
    by(auto 4 3 intro!: the_equality intro: rev_image_eqI dest: lprefix_lhdD)
  moreover from xs
  have "ltl ` ({ys. ys \<sqsubseteq> xs \<and> ys \<noteq> xs} \<inter> {xs. \<not> lnull xs}) = {ys. ys \<sqsubseteq> ltl xs \<and> ys \<noteq> ltl xs}"
    by(auto simp add: lprefix_LCons_conv intro: image_eqI[where x="LCons x (LCons x' ys)" for ys] image_eqI[where x="LCons x LNil"])
  ultimately show ?case using Eq_llist by clarsimp
qed

lemma chain_lprefix_lSup:
  "\<lbrakk> Complete_Partial_Order.chain (\<sqsubseteq>) A; xs \<in> A \<rbrakk>
  \<Longrightarrow> xs \<sqsubseteq> lSup A"
proof(coinduction arbitrary: xs A)
  case (lprefix xs A)
  note chain = `Complete_Partial_Order.chain (\<sqsubseteq>) A`
  from `xs \<in> A` show ?case
    by(auto 4 3 dest: chainD[OF chain] lprefix_lhdD intro: chain_lprefix_ltl[OF chain] intro!: the_equality[symmetric])
qed

lemma chain_lSup_lprefix:
  "\<lbrakk> Complete_Partial_Order.chain (\<sqsubseteq>) A; \<And>xs. xs \<in> A \<Longrightarrow> xs \<sqsubseteq> zs \<rbrakk>
  \<Longrightarrow> lSup A \<sqsubseteq> zs"
proof(coinduction arbitrary: A zs)
  case (lprefix A zs)
  note chain = `Complete_Partial_Order.chain (\<sqsubseteq>) A`
  from `\<forall>xs. xs \<in> A \<longrightarrow> xs \<sqsubseteq> zs`
  show ?case
    by(auto 4 4 dest: lprefix_lnullD lprefix_lhdD intro: chain_lprefix_ltl[OF chain] lprefix_ltlI rev_image_eqI intro!: the_equality)
qed

lemma llist_ccpo [simp, cont_intro]: "class.ccpo lSup (\<sqsubseteq>) (mk_less (\<sqsubseteq>))"
by(unfold_locales)(auto dest: lprefix_antisym intro: lprefix_trans chain_lprefix_lSup chain_lSup_lprefix simp add: mk_less_def)

lemmas [cont_intro] = ccpo.admissible_leI[OF llist_ccpo]

lemma llist_partial_function_definitions:
  "partial_function_definitions (\<sqsubseteq>) lSup"
by(unfold_locales)(auto dest: lprefix_antisym intro: lprefix_trans chain_lprefix_lSup chain_lSup_lprefix)

interpretation llist: partial_function_definitions "(\<sqsubseteq>)" lSup
  rewrites "lSup {} \<equiv> LNil"
by(rule llist_partial_function_definitions)(simp)

abbreviation "mono_llist \<equiv> monotone (fun_ord (\<sqsubseteq>)) (\<sqsubseteq>)"

interpretation llist_lift: partial_function_definitions "fun_ord lprefix" "fun_lub lSup"
  rewrites "fun_lub lSup {} \<equiv> \<lambda>_. LNil"
by(rule llist_partial_function_definitions[THEN partial_function_lift])(simp)

abbreviation "mono_llist_lift \<equiv> monotone (fun_ord (fun_ord lprefix)) (fun_ord lprefix)"

lemma lprefixes_chain:
  "Complete_Partial_Order.chain (\<sqsubseteq>) {ys. lprefix ys xs}"
by(rule chainI)(auto dest: lprefix_down_linear)

lemma llist_gen_induct:
  assumes adm: "ccpo.admissible lSup (\<sqsubseteq>) P"
  and step: "\<exists>zs. zs \<sqsubseteq> xs \<and> lfinite zs \<and> (\<forall>ys. zs \<sqsubseteq> ys \<longrightarrow> ys \<sqsubseteq> xs \<longrightarrow> lfinite ys \<longrightarrow> P ys)"
  shows "P xs"
proof -
  from step obtain zs
    where zs: "zs \<sqsubseteq> xs" "lfinite zs"
    and ys: "\<And>ys. \<lbrakk> zs \<sqsubseteq> ys; ys \<sqsubseteq> xs; lfinite ys \<rbrakk> \<Longrightarrow> P ys" by blast
  let ?C = "{ys. ys \<sqsubseteq> xs \<and> zs \<sqsubseteq> ys \<and> lfinite ys}"
  from lprefixes_chain[of xs]
  have "Complete_Partial_Order.chain (\<sqsubseteq>) ?C"
    by(auto dest: chain_compr)
  with adm have "P (lSup ?C)"
    by(rule ccpo.admissibleD)(auto intro: ys zs)
  also have "lSup ?C  = xs"
    using lSup_finite_gen_prefixes[OF zs] by simp
  finally show ?thesis .
qed

lemma llist_induct [case_names adm LNil LCons, induct type: llist]:
  assumes adm: "ccpo.admissible lSup (\<sqsubseteq>) P"
  and LNil: "P LNil"
  and LCons: "\<And>x xs. \<lbrakk> lfinite xs; P xs \<rbrakk> \<Longrightarrow> P (LCons x xs)"
  shows "P xs"
proof -
  { fix ys :: "'a llist"
    assume "lfinite ys"
    hence "P ys" by(induct)(simp_all add: LNil LCons) }
  note [intro] = this
  show ?thesis using adm
    by(rule llist_gen_induct)(auto intro: exI[where x=LNil])
qed

lemma LCons_mono [partial_function_mono, cont_intro]:
  "mono_llist A \<Longrightarrow> mono_llist (\<lambda>f. LCons x (A f))"
by(rule monotoneI)(auto dest: monotoneD)

lemma mono2mono_LCons [THEN llist.mono2mono, simp, cont_intro]:
  shows monotone_LCons: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (LCons x)"
by(auto intro: monotoneI)

lemma mcont2mcont_LCons [THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_LCons: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (LCons x)"
by(simp add: mcont_def monotone_LCons lSup_LCons[symmetric] contI)

lemma mono2mono_ltl[THEN llist.mono2mono, simp, cont_intro]:
  shows monotone_ltl: "monotone (\<sqsubseteq>) (\<sqsubseteq>) ltl"
by(auto intro: monotoneI lprefix_ltlI)

lemma cont_ltl: "cont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) ltl"
proof(rule contI)
  fix Y :: "'a llist set"
  assume "Y \<noteq> {}"
  have "ltl (lSup Y) = lSup (insert LNil (ltl ` (Y \<inter> {xs. \<not> lnull xs})))"
    by(simp add: lSup_insert_LNil)
  also have "insert LNil (ltl ` (Y \<inter> {xs. \<not> lnull xs})) = insert LNil (ltl ` Y)" by auto
  also have "lSup \<dots> = lSup (ltl ` Y)" by(simp add: lSup_insert_LNil)
  finally show "ltl (lSup Y) = lSup (ltl ` Y)" .
qed

lemma mcont2mcont_ltl [THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_ltl: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) ltl"
by(simp add: mcont_def monotone_ltl cont_ltl)

lemma llist_case_mono [partial_function_mono, cont_intro]:
  assumes lnil: "monotone orda ordb lnil"
  and lcons: "\<And>x xs. monotone orda ordb (\<lambda>f. lcons f x xs)"
  shows "monotone orda ordb (\<lambda>f. case_llist (lnil f) (lcons f) x)"
by(rule monotoneI)(auto split: llist.split dest: monotoneD[OF lnil] monotoneD[OF lcons])

lemma mcont_llist_case [cont_intro, simp]:
  "\<lbrakk> mcont luba orda lubb ordb (\<lambda>x. f x); \<And>x xs. mcont luba orda lubb ordb (\<lambda>y. g x xs y) \<rbrakk>
  \<Longrightarrow> mcont luba orda lubb ordb (\<lambda>y. case xs of LNil \<Rightarrow> f y | LCons x xs' \<Rightarrow> g x xs' y)"
by(cases xs) simp_all

lemma monotone_lprefix_case [cont_intro, simp]:
  assumes mono: "\<And>x. monotone (\<sqsubseteq>) (\<sqsubseteq>) (\<lambda>xs. f x xs (LCons x xs))"
  shows "monotone (\<sqsubseteq>) (\<sqsubseteq>) (\<lambda>xs. case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> f x xs' xs)"
by(rule llist.monotone_if_bot[where f="\<lambda>xs. f (lhd xs) (ltl xs) xs" and bound=LNil])(auto 4 3 split: llist.split simp add: not_lnull_conv LCons_lprefix_conv dest: monotoneD[OF mono])

lemma mcont_lprefix_case_aux:
  fixes f bot
  defines "g \<equiv> \<lambda>xs. f (lhd xs) (ltl xs) (LCons (lhd xs) (ltl xs))"
  assumes mcont: "\<And>x. mcont lSup (\<sqsubseteq>) lub ord (\<lambda>xs. f x xs (LCons x xs))"
  and ccpo: "class.ccpo lub ord (mk_less ord)"
  and bot: "\<And>x. ord bot x"
  shows "mcont lSup (\<sqsubseteq>) lub ord (\<lambda>xs. case xs of LNil \<Rightarrow> bot | LCons x xs' \<Rightarrow> f x xs' xs)"
proof(rule llist.mcont_if_bot[where f=g and bound=LNil and bot=bot, OF ccpo bot])
  fix Y :: "'a llist set"
  assume chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
    and Y: "Y \<noteq> {}" "\<And>x. x \<in> Y \<Longrightarrow> \<not> x \<sqsubseteq> LNil"
  from Y have Y': "Y \<inter> {xs. \<not> lnull xs} \<noteq> {}" by auto
  from Y obtain x xs where "LCons x xs \<in> Y" by(fastforce simp add: not_lnull_conv)
  with Y(2) have eq: "Y = LCons x ` (ltl ` (Y \<inter> {xs. \<not> lnull xs}))"
    by(force dest: chainD[OF chain] simp add: LCons_lprefix_conv lprefix_LCons_conv intro: imageI rev_image_eqI)
  show "g (lSup Y) = lub (g ` Y)"
    by(subst (1 2) eq)(simp add: lSup_LCons Y' g_def mcont_contD[OF mcont] chain chain_lprefix_ltl, simp add: image_image)
qed(auto 4 3 split: llist.split simp add: not_lnull_conv LCons_lprefix_conv g_def intro: mcont_monoD[OF mcont])

lemma mcont_lprefix_case [cont_intro, simp]:
  assumes "\<And>x. mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (\<lambda>xs. f x xs (LCons x xs))"
  shows "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (\<lambda>xs. case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> f x xs' xs)"
using assms by(rule mcont_lprefix_case_aux)(simp_all add: llist_ccpo)

lemma monotone_lprefix_case_lfp [cont_intro, simp]:
  fixes f :: "_ \<Rightarrow> _ :: order_bot"
  assumes mono: "\<And>x. monotone (\<sqsubseteq>) (\<le>) (\<lambda>xs. f x xs (LCons x xs))"
  shows "monotone (\<sqsubseteq>) (\<le>) (\<lambda>xs. case xs of LNil \<Rightarrow> \<bottom> | LCons x xs \<Rightarrow> f x xs (LCons x xs))"
by(rule llist.monotone_if_bot[where bound=LNil and bot=\<bottom> and f="\<lambda>xs. f (lhd xs) (ltl xs) xs"])(auto 4 3 simp add: not_lnull_conv LCons_lprefix_conv dest: monotoneD[OF mono] split: llist.split)

lemma mcont_lprefix_case_lfp [cont_intro, simp]:
  fixes f :: "_ => _ :: complete_lattice"
  assumes "\<And>x. mcont lSup (\<sqsubseteq>) Sup (\<le>) (\<lambda>xs. f x xs (LCons x xs))"
  shows "mcont lSup (\<sqsubseteq>) Sup (\<le>) (\<lambda>xs. case xs of LNil \<Rightarrow> \<bottom> | LCons x xs \<Rightarrow> f x xs (LCons x xs))"
using assms by(rule mcont_lprefix_case_aux)(rule complete_lattice_ccpo', simp)

declaration {* Partial_Function.init "llist" @{term llist.fixp_fun}
  @{term llist.mono_body} @{thm llist.fixp_rule_uc} @{thm llist.fixp_strong_induct_uc} NONE *}

subsection {* Monotonicity and continuity of already defined functions *}

lemma fixes f F
  defines "F \<equiv> \<lambda>lmap xs. case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> LCons (f x) (lmap xs)"
  shows lmap_conv_fixp: "lmap f \<equiv> ccpo.fixp (fun_lub lSup) (fun_ord (\<sqsubseteq>)) F" (is "?lhs \<equiv> ?rhs")
  and lmap_mono: "\<And>xs. mono_llist (\<lambda>lmap. F lmap xs)" (is "PROP ?mono")
proof(intro eq_reflection ext)
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix xs
  show "?lhs xs = ?rhs xs"
  proof(coinduction arbitrary: xs)
    case Eq_llist
    show ?case by(subst (1 3 4) llist.mono_body_fixp[OF mono])(auto simp add: F_def split: llist.split)
  qed
qed

lemma mono2mono_lmap[THEN llist.mono2mono, simp, cont_intro]:
  shows monotone_lmap: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (lmap f)"
by(rule llist.fixp_preserves_mono1[OF lmap_mono lmap_conv_fixp]) simp

lemma mcont2mcont_lmap[THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_lmap: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (lmap f)"
by(rule llist.fixp_preserves_mcont1[OF lmap_mono lmap_conv_fixp]) simp

lemma [partial_function_mono]: "mono_llist F \<Longrightarrow> mono_llist (\<lambda>f. lmap g (F f))"
by(rule mono2mono_lmap)


lemma mono_llist_lappend2 [partial_function_mono]:
  "mono_llist A \<Longrightarrow> mono_llist (\<lambda>f. lappend xs (A f))"
by(auto intro!: monotoneI lprefix_lappend_sameI simp add: fun_ord_def dest: monotoneD)

lemma mono2mono_lappend2 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lappend2: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (lappend xs)"
by(rule monotoneI)(rule lprefix_lappend_sameI)

lemma mcont2mcont_lappend2 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lappend2: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (lappend xs)"
proof(cases "lfinite xs")
  case True
  thus ?thesis by induct(simp_all add: monotone_lappend2)
next
  case False
  hence "lappend xs = (\<lambda>_. xs)" by(simp add: fun_eq_iff lappend_inf)
  thus ?thesis by(simp add: ccpo.cont_const[OF llist_ccpo])
qed

lemma fixes f F
  defines "F \<equiv> \<lambda>lset xs. case xs of LNil \<Rightarrow> {} | LCons x xs \<Rightarrow> insert x (lset xs)"
  shows lset_conv_fixp: "lset \<equiv> ccpo.fixp (fun_lub Union) (fun_ord (\<subseteq>)) F" (is "_ \<equiv> ?fixp")
  and lset_mono: "\<And>x. monotone (fun_ord (\<subseteq>)) (\<subseteq>) (\<lambda>f. F f x)" (is "PROP ?mono")
proof(rule eq_reflection ext antisym subsetI)+
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix x xs
  show "?fixp xs \<subseteq> lset xs"
    by(induct arbitrary: xs rule: lfp.fixp_induct_uc[of "\<lambda>x. x" F "\<lambda>x. x", OF mono reflexive refl])(auto simp add: F_def split: llist.split)

  assume "x \<in> lset xs"
  thus "x \<in> ?fixp xs" by induct(subst lfp.mono_body_fixp[OF mono], simp add: F_def)+
qed

lemma mono2mono_lset [THEN lfp.mono2mono, cont_intro, simp]:
  shows monotone_lset: "monotone (\<sqsubseteq>) (\<subseteq>) lset"
by(rule lfp.fixp_preserves_mono1[OF lset_mono lset_conv_fixp]) simp

lemma mcont2mcont_lset[THEN mcont2mcont, cont_intro, simp]:
  shows mcont_lset: "mcont lSup (\<sqsubseteq>) Union (\<subseteq>) lset"
by(rule lfp.fixp_preserves_mcont1[OF lset_mono lset_conv_fixp]) simp

lemma lset_lSup: "Complete_Partial_Order.chain (\<sqsubseteq>) Y \<Longrightarrow> lset (lSup Y) = \<Union>(lset ` Y)"
by(cases "Y = {}")(simp_all add: mcont_lset[THEN mcont_contD])

lemma lfinite_lSupD: "lfinite (lSup A) \<Longrightarrow> \<forall>xs \<in> A. lfinite xs"
by(induct ys\<equiv>"lSup A" arbitrary: A rule: lfinite_induct) fastforce+

lemma monotone_enat_le_lprefix_case [cont_intro, simp]:
  "monotone (\<le>) (\<sqsubseteq>) (\<lambda>x. f x (eSuc x)) \<Longrightarrow> monotone (\<le>) (\<sqsubseteq>) (\<lambda>x. case x of 0 \<Rightarrow> LNil | eSuc x' \<Rightarrow> f x' x)"
by(erule monotone_enat_le_case) simp_all

lemma mcont_enat_le_lprefix_case [cont_intro, simp]:
  assumes "mcont Sup (\<le>) lSup (\<sqsubseteq>) (\<lambda>x. f x (eSuc x))"
  shows "mcont Sup (\<le>) lSup (\<sqsubseteq>) (\<lambda>x. case x of 0 \<Rightarrow> LNil | eSuc x' \<Rightarrow> f x' x)"
using llist_ccpo assms by(rule mcont_enat_le_case) simp

lemma compact_LConsI:
  assumes "ccpo.compact lSup (\<sqsubseteq>) xs"
  shows "ccpo.compact lSup (\<sqsubseteq>) (LCons x xs)"
using llist_ccpo
proof(rule ccpo.compactI)
  from assms have "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> xs \<sqsubseteq> ys)" by cases
  hence [cont_intro]: "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> xs \<sqsubseteq> ltl ys)"
    using mcont_ltl by(rule admissible_subst)
  have [cont_intro]: "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> lnull ys \<and> lhd ys \<noteq> x)"
  proof(rule ccpo.admissibleI)
    fix Y
    assume chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
      and *: "Y \<noteq> {}" "\<forall>ys\<in>Y. \<not> lnull ys \<and> lhd ys \<noteq> x"
    from * show "\<not> lnull (lSup Y) \<and> lhd (lSup Y) \<noteq> x"
      by(subst lhd_lSup)(auto 4 4 dest: chainD[OF chain] intro!: the_equality[symmetric] dest: lprefix_lhdD)
  qed

  have eq: "(\<lambda>ys. \<not> LCons x xs \<sqsubseteq> ys) = (\<lambda>ys. \<not> xs \<sqsubseteq> ltl ys \<or> ys = LNil \<or> \<not> lnull ys \<and> lhd ys \<noteq> x)"
    by(auto simp add: fun_eq_iff LCons_lprefix_conv neq_LNil_conv)
  show "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> LCons x xs \<sqsubseteq> ys)"
    by(simp add: eq)
qed

lemma compact_LConsD:
  assumes "ccpo.compact lSup (\<sqsubseteq>) (LCons x xs)"
  shows "ccpo.compact lSup (\<sqsubseteq>) xs"
using llist_ccpo
proof(rule ccpo.compactI)
  from assms have "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> LCons x xs \<sqsubseteq> ys)" by cases
  hence "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> LCons x xs \<sqsubseteq> LCons x ys)"
    by(rule admissible_subst)(rule mcont_LCons)
  thus "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> xs \<sqsubseteq> ys)" by simp
qed

lemma compact_LCons_iff [simp]:
  "ccpo.compact lSup (\<sqsubseteq>) (LCons x xs) \<longleftrightarrow> ccpo.compact lSup (\<sqsubseteq>) xs"
by(blast intro: compact_LConsI compact_LConsD)

lemma compact_lfiniteI:
  "lfinite xs \<Longrightarrow> ccpo.compact lSup (\<sqsubseteq>) xs"
by(induction rule: lfinite.induct) simp_all

lemma compact_lfiniteD:
  assumes "ccpo.compact lSup (\<sqsubseteq>) xs"
  shows "lfinite xs"
proof(rule ccontr)
  assume inf: "\<not> lfinite xs"

  from assms have "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>ys. \<not> xs \<sqsubseteq> ys)" by cases
  moreover let ?C = "{ys. ys \<sqsubseteq> xs \<and> ys \<noteq> xs}"
  have "Complete_Partial_Order.chain (\<sqsubseteq>) ?C"
    using lprefixes_chain[of xs] by(auto dest: chain_compr)
  moreover have "?C \<noteq> {}" using inf by(cases xs) auto
  ultimately have "\<not> xs \<sqsubseteq> lSup ?C"
    by(rule ccpo.admissibleD)(auto dest: lprefix_antisym)
  also have "lSup ?C = xs" using inf by(rule lSup_strict_prefixes)
  finally show False by simp
qed

lemma compact_eq_lfinite [simp]: "ccpo.compact lSup (\<sqsubseteq>) = lfinite"
by(blast intro: compact_lfiniteI compact_lfiniteD)

subsection {* More function definitions *}

primcorec iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a llist"
where "iterates f x = LCons x (iterates f (f x))"

primrec llist_of :: "'a list \<Rightarrow> 'a llist"
where
  "llist_of [] = LNil"
| "llist_of (x#xs) = LCons x (llist_of xs)"

definition list_of :: "'a llist \<Rightarrow> 'a list"
where [code del]: "list_of xs = (if lfinite xs then inv llist_of xs else undefined)"

definition llength :: "'a llist \<Rightarrow> enat"
where [code del]:
  "llength = enat_unfold lnull ltl"

primcorec ltake :: "enat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "n = 0 \<or> lnull xs \<Longrightarrow> lnull (ltake n xs)"
| "lhd (ltake n xs) = lhd xs"
| "ltl (ltake n xs) = ltake (epred n) (ltl xs)"

definition ldropn :: "nat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where "ldropn n xs = (ltl ^^ n) xs"

context notes [[function_internals]]
begin

partial_function (llist) ldrop :: "enat \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "ldrop n xs = (case n of 0 \<Rightarrow> xs | eSuc n' \<Rightarrow> case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldrop n' xs')"

end

primcorec ltakeWhile :: "('a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lnull xs \<or> \<not> P (lhd xs) \<Longrightarrow> lnull (ltakeWhile P xs)"
| "lhd (ltakeWhile P xs) = lhd xs"
| "ltl (ltakeWhile P xs) = ltakeWhile P (ltl xs)"

context fixes P :: "'a \<Rightarrow> bool"
  notes [[function_internals]]
begin

partial_function (llist) ldropWhile :: "'a llist \<Rightarrow> 'a llist"
where "ldropWhile xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> if P x then ldropWhile xs' else xs)"

partial_function (llist) lfilter :: "'a llist \<Rightarrow> 'a llist"
where "lfilter xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> if P x then LCons x (lfilter xs') else lfilter xs')"

end

primrec lnth :: "'a llist \<Rightarrow> nat \<Rightarrow> 'a"
where
  "lnth xs 0 = (case xs of LNil \<Rightarrow> undefined (0 :: nat) | LCons x xs' \<Rightarrow> x)"
| "lnth xs (Suc n) = (case xs of LNil \<Rightarrow> undefined (Suc n) | LCons x xs' \<Rightarrow> lnth xs' n)"

declare lnth.simps [simp del]

primcorec lzip :: "'a llist \<Rightarrow> 'b llist \<Rightarrow> ('a \<times> 'b) llist"
where
  "lnull xs \<or> lnull ys \<Longrightarrow> lnull (lzip xs ys)"
| "lhd (lzip xs ys) = (lhd xs, lhd ys)"
| "ltl (lzip xs ys) = lzip (ltl xs) (ltl ys)"

definition llast :: "'a llist \<Rightarrow> 'a"
where [nitpick_simp]:
  "llast xs = (case llength xs of enat n \<Rightarrow> (case n of 0 \<Rightarrow> undefined | Suc n' \<Rightarrow> lnth xs n') | \<infinity> \<Rightarrow> undefined)"

coinductive ldistinct :: "'a llist \<Rightarrow> bool"
where
  LNil [simp]: "ldistinct LNil"
| LCons: "\<lbrakk> x \<notin> lset xs; ldistinct xs \<rbrakk> \<Longrightarrow> ldistinct (LCons x xs)"

hide_fact (open) LNil LCons

definition inf_llist :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a llist"
where [code del]: "inf_llist f = lmap f (iterates Suc 0)"

abbreviation repeat :: "'a \<Rightarrow> 'a llist"
where "repeat \<equiv> iterates (\<lambda>x. x)"

definition lstrict_prefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where [code del]: "lstrict_prefix xs ys \<equiv> xs \<sqsubseteq> ys \<and> xs \<noteq> ys"

text {* longest common prefix *}
definition llcp :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> enat"
where [code del]:
  "llcp xs ys =
   enat_unfold (\<lambda>(xs, ys). lnull xs \<or> lnull ys \<or> lhd xs \<noteq> lhd ys) (map_prod ltl ltl) (xs, ys)"

coinductive llexord :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  llexord_LCons_eq: "llexord r xs ys \<Longrightarrow> llexord r (LCons x xs) (LCons x ys)"
| llexord_LCons_less: "r x y \<Longrightarrow> llexord r (LCons x xs) (LCons y ys)"
| llexord_LNil [simp, intro!]: "llexord r LNil ys"

context notes [[function_internals]]
begin

partial_function (llist) lconcat :: "'a llist llist \<Rightarrow> 'a llist"
where "lconcat xss = (case xss of LNil \<Rightarrow> LNil | LCons xs xss' \<Rightarrow> lappend xs (lconcat xss'))"

end

definition lhd' :: "'a llist \<Rightarrow> 'a option" where
"lhd' xs = (if lnull xs then None else Some (lhd xs))"

lemma lhd'_simps[simp]:
  "lhd' LNil = None"
  "lhd' (LCons x xs) = Some x"
unfolding lhd'_def by auto

definition ltl' :: "'a llist \<Rightarrow> 'a llist option" where
"ltl' xs = (if lnull xs then None else Some (ltl xs))"

lemma ltl'_simps[simp]:
  "ltl' LNil = None"
  "ltl' (LCons x xs) = Some xs"
unfolding ltl'_def by auto

definition lnths :: "'a llist \<Rightarrow> nat set \<Rightarrow> 'a llist"
where "lnths xs A = lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0)))"

definition (in monoid_add) lsum_list :: "'a llist \<Rightarrow> 'a"
where "lsum_list xs = (if lfinite xs then sum_list (list_of xs) else 0)"

subsection {* Converting ordinary lists to lazy lists: @{term "llist_of"} *}

lemma lhd_llist_of [simp]: "lhd (llist_of xs) = hd xs"
by(cases xs)(simp_all add: hd_def lhd_def)

lemma ltl_llist_of [simp]: "ltl (llist_of xs) = llist_of (tl xs)"
by(cases xs) simp_all

lemma lfinite_llist_of [simp]: "lfinite (llist_of xs)"
by(induct xs) auto

lemma lfinite_eq_range_llist_of: "lfinite xs \<longleftrightarrow> xs \<in> range llist_of"
proof
  assume "lfinite xs"
  thus "xs \<in> range llist_of"
    by(induct rule: lfinite.induct)(auto intro: llist_of.simps[symmetric])
next
  assume "xs \<in> range llist_of"
  thus "lfinite xs" by(auto intro: lfinite_llist_of)
qed

lemma lnull_llist_of [simp]: "lnull (llist_of xs) \<longleftrightarrow> xs = []"
by(cases xs) simp_all

lemma llist_of_eq_LNil_conv:
  "llist_of xs = LNil \<longleftrightarrow> xs = []"
by(cases xs) simp_all

lemma llist_of_eq_LCons_conv:
  "llist_of xs = LCons y ys \<longleftrightarrow> (\<exists>xs'. xs = y # xs' \<and> ys = llist_of xs')"
by(cases xs) auto

lemma lappend_llist_of_llist_of:
  "lappend (llist_of xs) (llist_of ys) = llist_of (xs @ ys)"
by(induct xs) simp_all

lemma lfinite_rev_induct [consumes 1, case_names Nil snoc]:
  assumes fin: "lfinite xs"
  and Nil: "P LNil"
  and snoc: "\<And>x xs. \<lbrakk> lfinite xs; P xs \<rbrakk> \<Longrightarrow> P (lappend xs (LCons x LNil))"
  shows "P xs"
proof -
  from fin obtain xs' where xs: "xs = llist_of xs'"
    unfolding lfinite_eq_range_llist_of by blast
  show ?thesis unfolding xs
    by(induct xs' rule: rev_induct)(auto simp add: Nil lappend_llist_of_llist_of[symmetric] dest: snoc[rotated])
qed

lemma lappend_llist_of_LCons:
  "lappend (llist_of xs) (LCons y ys) = lappend (llist_of (xs @ [y])) ys"
by(induct xs) simp_all

lemma lmap_llist_of [simp]:
  "lmap f (llist_of xs) = llist_of (map f xs)"
by(induct xs) simp_all

lemma lset_llist_of [simp]: "lset (llist_of xs) = set xs"
by(induct xs) simp_all

lemma llist_of_inject [simp]: "llist_of xs = llist_of ys \<longleftrightarrow> xs = ys"
proof
  assume "llist_of xs = llist_of ys"
  thus "xs = ys"
  proof(induct xs arbitrary: ys)
    case Nil thus ?case by(cases ys) auto
  next
    case Cons thus ?case by(cases ys) auto
  qed
qed simp

lemma inj_llist_of [simp]: "inj llist_of"
by(rule inj_onI) simp

subsection {* Converting finite lazy lists to ordinary lists: @{term "list_of"} *}

lemma list_of_llist_of [simp]: "list_of (llist_of xs) = xs"
by(fastforce simp add: list_of_def intro: inv_f_f inj_onI)

lemma llist_of_list_of [simp]: "lfinite xs \<Longrightarrow> llist_of (list_of xs) = xs"
unfolding lfinite_eq_range_llist_of by auto

lemma list_of_LNil [simp, nitpick_simp]: "list_of LNil = []"
using list_of_llist_of[of "[]"] by simp

lemma list_of_LCons [simp]: "lfinite xs \<Longrightarrow> list_of (LCons x xs) = x # list_of xs"
proof(induct arbitrary: x rule: lfinite.induct)
  case lfinite_LNil
  show ?case using list_of_llist_of[of "[x]"] by simp
next
  case (lfinite_LConsI xs' x')
  from `list_of (LCons x' xs') = x' # list_of xs'` show ?case
    using list_of_llist_of[of "x # x' # list_of xs'"]
      llist_of_list_of[OF `lfinite xs'`] by simp
qed

lemma list_of_LCons_conv [nitpick_simp]:
  "list_of (LCons x xs) = (if lfinite xs then x # list_of xs else undefined)"
by(auto)(auto simp add: list_of_def)

lemma list_of_lappend:
  assumes "lfinite xs" "lfinite ys"
  shows "list_of (lappend xs ys) = list_of xs @ list_of ys"
using `lfinite xs` by induct(simp_all add: `lfinite ys`)

lemma list_of_lmap [simp]:
  assumes "lfinite xs"
  shows "list_of (lmap f xs) = map f (list_of xs)"
using assms by induct simp_all

lemma set_list_of [simp]:
  assumes "lfinite xs"
  shows "set (list_of xs) = lset xs"
using assms by(induct)(simp_all)

lemma hd_list_of [simp]: "lfinite xs \<Longrightarrow> hd (list_of xs) = lhd xs"
by(clarsimp simp add: lfinite_eq_range_llist_of)

lemma tl_list_of: "lfinite xs \<Longrightarrow> tl (list_of xs) = list_of (ltl xs)"
by(auto simp add: lfinite_eq_range_llist_of)

text {* Efficient implementation via tail recursion suggested by Brian Huffman *}

definition list_of_aux :: "'a list \<Rightarrow> 'a llist \<Rightarrow> 'a list"
where "list_of_aux xs ys = (if lfinite ys then rev xs @ list_of ys else undefined)"

lemma list_of_code [code]: "list_of = list_of_aux []"
by(simp add: fun_eq_iff list_of_def list_of_aux_def)

lemma list_of_aux_code [code]:
  "list_of_aux xs LNil = rev xs"
  "list_of_aux xs (LCons y ys) = list_of_aux (y # xs) ys"
by(simp_all add: list_of_aux_def)

subsection {* The length of a lazy list: @{term "llength"} *}

lemma [simp, nitpick_simp]:
  shows llength_LNil: "llength LNil = 0"
  and llength_LCons: "llength (LCons x xs) = eSuc (llength xs)"
by(simp_all add: llength_def enat_unfold)

lemma llength_eq_0 [simp]: "llength xs = 0 \<longleftrightarrow> lnull xs"
by(cases xs) simp_all

lemma llength_lnull [simp]: "lnull xs \<Longrightarrow> llength xs = 0"
by simp

lemma epred_llength:
  "epred (llength xs) = llength (ltl xs)"
by(cases xs) simp_all

lemmas llength_ltl = epred_llength[symmetric]

lemma llength_lmap [simp]: "llength (lmap f xs) = llength xs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: epred_llength)

lemma llength_lappend [simp]: "llength (lappend xs ys) = llength xs + llength ys"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(simp_all add: iadd_is_0 epred_iadd1 split_paired_all epred_llength, auto)

lemma llength_llist_of [simp]:
  "llength (llist_of xs) = enat (length xs)"
by(induct xs)(simp_all add: zero_enat_def eSuc_def)

lemma length_list_of:
  "lfinite xs \<Longrightarrow> enat (length (list_of xs)) = llength xs"
apply(rule sym)
by(induct rule: lfinite.induct)(auto simp add: eSuc_enat zero_enat_def)

lemma length_list_of_conv_the_enat:
  "lfinite xs \<Longrightarrow> length (list_of xs) = the_enat (llength xs)"
unfolding lfinite_eq_range_llist_of by auto

lemma llength_eq_enat_lfiniteD: "llength xs = enat n \<Longrightarrow> lfinite xs"
proof(induct n arbitrary: xs)
  case [folded zero_enat_def]: 0
  thus ?case by simp
next
  case (Suc n)
  note len = `llength xs = enat (Suc n)`
  then obtain x xs' where "xs = LCons x xs'"
    by(cases xs)(auto simp add: zero_enat_def)
  moreover with len have "llength xs' = enat n"
    by(simp add: eSuc_def split: enat.split_asm)
  hence "lfinite xs'" by(rule Suc)
  ultimately show ?case by simp
qed

lemma lfinite_llength_enat:
  assumes "lfinite xs"
  shows "\<exists>n. llength xs = enat n"
using assms
by induct(auto simp add: eSuc_def zero_enat_def)

lemma lfinite_conv_llength_enat:
  "lfinite xs \<longleftrightarrow> (\<exists>n. llength xs = enat n)"
by(blast dest: llength_eq_enat_lfiniteD lfinite_llength_enat)

lemma not_lfinite_llength:
  "\<not> lfinite xs \<Longrightarrow> llength xs = \<infinity>"
by(simp add: lfinite_conv_llength_enat)

lemma llength_eq_infty_conv_lfinite:
  "llength xs = \<infinity> \<longleftrightarrow> \<not> lfinite xs"
by(simp add: lfinite_conv_llength_enat)

lemma lfinite_finite_index: "lfinite xs \<Longrightarrow> finite {n. enat n < llength xs}"
by(auto dest: lfinite_llength_enat)

text {* tail-recursive implementation for @{term llength} *}

definition gen_llength :: "nat \<Rightarrow> 'a llist \<Rightarrow> enat"
where "gen_llength n xs = enat n + llength xs"

lemma gen_llength_code [code]:
  "gen_llength n LNil = enat n"
  "gen_llength n (LCons x xs) = gen_llength (n + 1) xs"
by(simp_all add: gen_llength_def iadd_Suc eSuc_enat[symmetric] iadd_Suc_right)

lemma llength_code [code]: "llength = gen_llength 0"
by(simp add: gen_llength_def fun_eq_iff zero_enat_def)

lemma fixes F
  defines "F \<equiv> \<lambda>llength xs. case xs of LNil \<Rightarrow> 0 | LCons x xs \<Rightarrow> eSuc (llength xs)"
  shows llength_conv_fixp: "llength \<equiv> ccpo.fixp (fun_lub Sup) (fun_ord (\<le>)) F" (is "_ \<equiv> ?fixp")
  and llength_mono: "\<And>xs. monotone (fun_ord (\<le>)) (\<le>) (\<lambda>llength. F llength xs)" (is "PROP ?mono")
proof(intro eq_reflection ext)
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix xs
  show "llength xs = ?fixp xs"
    by(coinduction arbitrary: xs rule: enat_coinduct)(subst (1 2 3) lfp.mono_body_fixp[OF mono], fastforce simp add: F_def split: llist.split del: iffI)+
qed

lemma mono2mono_llength[THEN lfp.mono2mono, simp, cont_intro]:
  shows monotone_llength: "monotone (\<sqsubseteq>) (\<le>) llength"
by(rule lfp.fixp_preserves_mono1[OF llength_mono llength_conv_fixp])(fold bot_enat_def, simp)

lemma mcont2mcont_llength[THEN lfp.mcont2mcont, simp, cont_intro]:
  shows mcont_llength: "mcont lSup (\<sqsubseteq>) Sup (\<le>) llength"
by(rule lfp.fixp_preserves_mcont1[OF llength_mono llength_conv_fixp])(fold bot_enat_def, simp)

subsection {* Taking and dropping from lazy lists: @{term "ltake"}, @{term "ldropn"}, and @{term "ldrop"} *}

lemma ltake_LNil [simp, code, nitpick_simp]: "ltake n LNil = LNil"
by simp

lemma ltake_0 [simp]: "ltake 0 xs = LNil"
by(simp add: ltake_def)

lemma ltake_eSuc_LCons [simp]:
  "ltake (eSuc n) (LCons x xs) = LCons x (ltake n xs)"
by(rule llist.expand)(simp_all)

lemma ltake_eSuc:
  "ltake (eSuc n) xs =
  (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> LCons x (ltake n xs'))"
by(cases xs) simp_all

lemma lnull_ltake [simp]: "lnull (ltake n xs) \<longleftrightarrow> lnull xs \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltake_eq_LNil_iff: "ltake n xs = LNil \<longleftrightarrow> xs = LNil \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma LNil_eq_ltake_iff [simp]: "LNil = ltake n xs \<longleftrightarrow> xs = LNil \<or> n = 0"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltake_LCons [code, nitpick_simp]:
  "ltake n (LCons x xs) =
  (case n of 0 \<Rightarrow> LNil | eSuc n' \<Rightarrow> LCons x (ltake n' xs))"
by(rule llist.expand)(simp_all split: co.enat.split)

lemma lhd_ltake [simp]: "n \<noteq> 0 \<Longrightarrow> lhd (ltake n xs) = lhd xs"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemma ltl_ltake: "ltl (ltake n xs) = ltake (epred n) (ltl xs)"
by(cases n xs rule: enat_coexhaust[case_product llist.exhaust]) simp_all

lemmas ltake_epred_ltl = ltl_ltake [symmetric]

declare ltake.sel(2) [simp del]

lemma ltake_ltl: "ltake n (ltl xs) = ltl (ltake (eSuc n) xs)"
by(cases xs) simp_all

lemma llength_ltake [simp]: "llength (ltake n xs) = min n (llength xs)"
by(coinduction arbitrary: n xs rule: enat_coinduct)(auto 4 3 simp add: enat_min_eq_0_iff epred_llength ltl_ltake)

lemma ltake_lmap [simp]: "ltake n (lmap f xs) = lmap f (ltake n xs)"
by(coinduction arbitrary: n xs)(auto 4 3 simp add: ltl_ltake)

lemma ltake_ltake [simp]: "ltake n (ltake m xs) = ltake (min n m) xs"
by(coinduction arbitrary: n m xs)(auto 4 4 simp add: enat_min_eq_0_iff ltl_ltake)

lemma lset_ltake: "lset (ltake n xs) \<subseteq> lset xs"
proof(rule subsetI)
  fix x
  assume "x \<in> lset (ltake n xs)"
  thus "x \<in> lset xs"
  proof(induct "ltake n xs" arbitrary: xs n rule: lset_induct)
    case find thus ?case
      by(cases xs)(simp, cases n rule: enat_coexhaust, simp_all)
  next
    case step thus ?case
      by(cases xs)(simp, cases n rule: enat_coexhaust, simp_all)
  qed
qed

lemma ltake_all: "llength xs \<le> m \<Longrightarrow> ltake m xs = xs"
by(coinduction arbitrary: m xs)(auto simp add: epred_llength[symmetric] ltl_ltake intro: epred_le_epredI)

lemma ltake_llist_of [simp]:
  "ltake (enat n) (llist_of xs) = llist_of (take n xs)"
proof(induct n arbitrary: xs)
  case 0
  thus ?case unfolding zero_enat_def[symmetric]
    by(cases xs) simp_all
next
  case (Suc n)
  thus ?case unfolding eSuc_enat[symmetric]
    by(cases xs) simp_all
qed

lemma lfinite_ltake [simp]:
  "lfinite (ltake n xs) \<longleftrightarrow> lfinite xs \<or> n < \<infinity>"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct ys\<equiv>"ltake n xs" arbitrary: n xs rule: lfinite_induct)(fastforce simp add: zero_enat_def ltl_ltake)+
next
  assume ?rhs (is "?xs \<or> ?n")
  thus ?lhs
  proof
    assume ?xs thus ?thesis
      by(induct xs arbitrary: n)(simp_all add: ltake_LCons split: enat_cosplit)
  next
    assume ?n
    then obtain n' where "n = enat n'" by auto
    moreover have "lfinite (ltake (enat n') xs)"
      by(induct n' arbitrary: xs)
        (auto simp add: zero_enat_def[symmetric] eSuc_enat[symmetric] ltake_eSuc
              split: llist.split)
    ultimately show ?thesis by simp
  qed
qed

lemma ltake_lappend1:  "n \<le> llength xs \<Longrightarrow> ltake n (lappend xs ys) = ltake n xs"
by(coinduction arbitrary: n xs)(auto intro!: exI simp add: llength_ltl epred_le_epredI ltl_ltake)

lemma ltake_lappend2:
  "llength xs \<le> n \<Longrightarrow> ltake n (lappend xs ys) = lappend xs (ltake (n - llength xs) ys)"
by(coinduction arbitrary: n xs rule: llist.coinduct_strong)(auto intro!: exI simp add: llength_ltl epred_le_epredI ltl_ltake)

lemma ltake_lappend:
  "ltake n (lappend xs ys) = lappend (ltake n xs) (ltake (n - llength xs) ys)"
by(coinduction arbitrary: n xs ys rule: llist.coinduct_strong)(auto intro!: exI simp add: llength_ltl ltl_ltake)

lemma take_list_of:
  assumes "lfinite xs"
  shows "take n (list_of xs) = list_of (ltake (enat n) xs)"
using assms
by(induct arbitrary: n)
  (simp_all add: take_Cons zero_enat_def[symmetric] eSuc_enat[symmetric] split: nat.split)

lemma ltake_eq_ltake_antimono:
  "\<lbrakk> ltake n xs = ltake n ys; m \<le> n \<rbrakk> \<Longrightarrow> ltake m xs = ltake m ys"
by (metis ltake_ltake min_def)

lemma ltake_is_lprefix [simp, intro]: "ltake n xs \<sqsubseteq> xs"
by(coinduction arbitrary: xs n)(auto simp add: ltl_ltake)

lemma lprefix_ltake_same [simp]:
  "ltake n xs \<sqsubseteq> ltake m xs \<longleftrightarrow> n \<le> m \<or> llength xs \<le> m"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI disjCI)+
  assume ?lhs "\<not> llength xs \<le> m"
  thus "n \<le> m"
  proof(coinduction arbitrary: n m xs rule: enat_le_coinduct)
    case (le n m xs)
    thus ?case by(cases xs)(auto 4 3 simp add: ltake_LCons split: co.enat.splits)
  qed
next
  assume ?rhs
  thus ?lhs
  proof
    assume "n \<le> m"
    thus ?thesis
      by(coinduction arbitrary: n m xs)(auto 4 4 simp add: ltl_ltake epred_le_epredI)
  qed(simp add: ltake_all)
qed

lemma fixes f F
  defines "F \<equiv> \<lambda>ltake n xs. case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> case n of 0 \<Rightarrow> LNil | eSuc n \<Rightarrow> LCons x (ltake n xs)"
  shows ltake_conv_fixp: "ltake \<equiv> curry (ccpo.fixp (fun_lub lSup) (fun_ord (\<sqsubseteq>)) (\<lambda>ltake. case_prod (F (curry ltake))))" (is "?lhs \<equiv> ?rhs")
  and ltake_mono: "\<And>nxs. mono_llist (\<lambda>ltake. case nxs of (n, xs) \<Rightarrow> F (curry ltake) n xs)" (is "PROP ?mono")
proof(intro eq_reflection ext)
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix n xs
  show "?lhs n xs = ?rhs n xs"
  proof(coinduction arbitrary: n xs)
    case Eq_llist
    show ?case by(subst (1 3 4) llist.mono_body_fixp[OF mono])(auto simp add: F_def split: llist.split prod.split co.enat.split)
  qed
qed

lemma monotone_ltake: "monotone (rel_prod (\<le>) (\<sqsubseteq>)) (\<sqsubseteq>) (case_prod ltake)"
by(rule llist.fixp_preserves_mono2[OF ltake_mono ltake_conv_fixp]) simp

lemma mono2mono_ltake1[THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ltake1: "monotone (\<le>) (\<sqsubseteq>) (\<lambda>n. ltake n xs)"
using monotone_ltake by auto

lemma mono2mono_ltake2[THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ltake2: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (ltake n)"
using monotone_ltake by auto

lemma mcont_ltake: "mcont (prod_lub Sup lSup) (rel_prod (\<le>) (\<sqsubseteq>)) lSup (\<sqsubseteq>) (case_prod ltake)"
by(rule llist.fixp_preserves_mcont2[OF ltake_mono ltake_conv_fixp]) simp

lemma mcont2mcont_ltake1 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ltake1: "mcont Sup (\<le>) lSup (\<sqsubseteq>) (\<lambda>n. ltake n xs)"
using mcont_ltake by auto

lemma mcont2mcont_ltake2 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ltake2: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (ltake n)"
using mcont_ltake by auto

lemma [partial_function_mono]: "mono_llist F \<Longrightarrow> mono_llist (\<lambda>f. ltake n (F f))"
by(rule mono2mono_ltake2)

lemma llist_induct2:
  assumes adm: "ccpo.admissible (prod_lub lSup lSup) (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) (\<lambda>x. P (fst x) (snd x))"
  and LNil: "P LNil LNil"
  and LCons1: "\<And>x xs. \<lbrakk> lfinite xs; P xs LNil \<rbrakk> \<Longrightarrow> P (LCons x xs) LNil"
  and LCons2: "\<And>y ys. \<lbrakk> lfinite ys; P LNil ys \<rbrakk> \<Longrightarrow> P LNil (LCons y ys)"
  and LCons: "\<And>x xs y ys. \<lbrakk> lfinite xs; lfinite ys; P xs ys \<rbrakk> \<Longrightarrow> P (LCons x xs) (LCons y ys)"
  shows "P xs ys"
proof -
  let ?C = "(\<lambda>n. (ltake n xs, ltake n ys)) ` range enat"
  have "Complete_Partial_Order.chain (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) ?C"
    by(rule chainI) auto
  with adm have "P (fst (prod_lub lSup lSup ?C)) (snd (prod_lub lSup lSup ?C))"
  proof(rule ccpo.admissibleD)
    fix xsys
    assume "xsys \<in> ?C"
    then obtain n where "xsys = (ltake (enat n) xs, ltake (enat n) ys)" by auto
    moreover {
      fix xs :: "'a llist"
      assume "lfinite xs"
      hence "P xs LNil" by induct(auto intro: LNil LCons1) }
    note 1 = this
    { fix ys :: "'b llist"
      assume "lfinite ys"
      hence "P LNil ys" by induct(auto intro: LNil LCons2) }
    note 2 = this
    have "P (ltake (enat n) xs) (ltake (enat n) ys)"
      by(induct n arbitrary: xs ys)(auto simp add: zero_enat_def[symmetric] LNil eSuc_enat[symmetric] ltake_eSuc split: llist.split intro: LNil LCons 1 2)
    ultimately show "P (fst xsys) (snd xsys)" by simp
  qed simp
  also have "fst (prod_lub lSup lSup ?C) = xs"
    unfolding prod_lub_def fst_conv
    by(subst image_image)(simp add: mcont_contD[OF mcont_ltake1, symmetric] ltake_all)
  also have "snd (prod_lub lSup lSup ?C) = ys"
    unfolding prod_lub_def snd_conv
    by(subst image_image)(simp add: mcont_contD[OF mcont_ltake1, symmetric] ltake_all)
  finally show ?thesis .
qed

lemma ldropn_0 [simp]: "ldropn 0 xs = xs"
by(simp add: ldropn_def)

lemma ldropn_LNil [code, simp]: "ldropn n LNil = LNil"
by(induct n)(simp_all add: ldropn_def)

lemma ldropn_lnull: "lnull xs \<Longrightarrow> ldropn n xs = LNil"
by(simp add: lnull_def)

lemma ldropn_LCons [code]:
  "ldropn n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | Suc n' \<Rightarrow> ldropn n' xs)"
by(cases n)(simp_all add: ldropn_def funpow_swap1)

lemma ldropn_Suc: "ldropn (Suc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldropn n xs')"
by(simp split: llist.split)(simp add: ldropn_def funpow_swap1)

lemma ldropn_Suc_LCons [simp]: "ldropn (Suc n) (LCons x xs) = ldropn n xs"
by(simp add: ldropn_LCons)

lemma ltl_ldropn: "ltl (ldropn n xs) = ldropn n (ltl xs)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by simp
next
  case (Suc n)
  thus ?case
    by(cases xs)(simp_all add: ldropn_Suc split: llist.split)
qed

lemma ldrop_simps [simp]:
  shows ldrop_LNil: "ldrop n LNil = LNil"
  and ldrop_0: "ldrop 0 xs = xs"
  and ldrop_eSuc_LCons: "ldrop (eSuc n) (LCons x xs) = ldrop n xs"
by(simp_all add: ldrop.simps split: co.enat.split)

lemma ldrop_lnull: "lnull xs \<Longrightarrow> ldrop n xs = LNil"
by(simp add: lnull_def)

lemma fixes f F
  defines "F \<equiv> \<lambda>ldropn xs. case xs of LNil \<Rightarrow> \<lambda>_. LNil | LCons x xs \<Rightarrow> \<lambda>n. if n = 0 then LCons x xs else ldropn xs (n - 1)"
  shows ldrop_conv_fixp: "(\<lambda>xs n. ldropn n xs) \<equiv> ccpo.fixp (fun_lub (fun_lub lSup)) (fun_ord (fun_ord lprefix)) (\<lambda>ldrop. F ldrop)" (is "?lhs \<equiv> ?rhs")
  and ldrop_mono: "\<And>xs. mono_llist_lift (\<lambda>ldrop. F ldrop xs)" (is "PROP ?mono")
proof(intro eq_reflection ext)
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix n xs
  show "?lhs xs n = ?rhs xs n"
    by(induction n arbitrary: xs)
      (subst llist_lift.mono_body_fixp[OF mono], simp add: F_def split: llist.split)+
qed

lemma ldropn_fixp_case_conv:
  "(\<lambda>xs. case xs of LNil \<Rightarrow> \<lambda>_. LNil | LCons x xs \<Rightarrow> \<lambda>n. if n = 0 then LCons x xs else f xs (n - 1)) =
   (\<lambda>xs n. case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> if n = 0 then LCons x xs else f xs (n - 1))"
by(auto simp add: fun_eq_iff split: llist.split)

lemma monotone_ldropn_aux: "monotone lprefix (fun_ord lprefix) (\<lambda>xs n. ldropn n xs)"
by(rule llist_lift.fixp_preserves_mono1[OF ldrop_mono ldrop_conv_fixp])
  (simp add: ldropn_fixp_case_conv monotone_fun_ord_apply)

lemma mono2mono_ldropn[THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ldropn': "monotone lprefix lprefix (\<lambda>xs. ldropn n xs)"
using monotone_ldropn_aux by(auto simp add: monotone_def fun_ord_def)

lemma mcont_ldropn_aux: "mcont lSup lprefix (fun_lub lSup) (fun_ord lprefix) (\<lambda>xs n. ldropn n xs)"
by(rule llist_lift.fixp_preserves_mcont1[OF ldrop_mono ldrop_conv_fixp])
  (simp add: ldropn_fixp_case_conv mcont_fun_lub_apply)

lemma mcont2mcont_ldropn [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ldropn: "mcont lSup lprefix lSup lprefix (ldropn n)"
using mcont_ldropn_aux by(auto simp add: mcont_fun_lub_apply)

lemma monotone_enat_cocase [cont_intro, simp]:
  "\<lbrakk> \<And>n. monotone (\<le>) ord (\<lambda>n. f n (eSuc n));
    \<And>n. ord a (f n (eSuc n)); ord a a \<rbrakk>
  \<Longrightarrow> monotone (\<le>) ord (\<lambda>n. case n of 0 \<Rightarrow> a | eSuc n' \<Rightarrow> f n' n)"
by(rule monotone_enat_le_case)

lemma monotone_ldrop: "monotone (rel_prod (=) (\<sqsubseteq>)) (\<sqsubseteq>) (case_prod ldrop)"
by(rule llist.fixp_preserves_mono2[OF ldrop.mono ldrop_def]) simp

lemma mono2mono_ldrop2 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ldrop2: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (ldrop n)"
by(simp add: monotone_ldrop[simplified])

lemma mcont_ldrop: "mcont (prod_lub the_Sup lSup) (rel_prod (=) (\<sqsubseteq>)) lSup (\<sqsubseteq>) (case_prod ldrop)"
by(rule llist.fixp_preserves_mcont2[OF ldrop.mono ldrop_def]) simp

lemma mcont2monct_ldrop2 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ldrop2: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (ldrop n)"
by(simp add: mcont_ldrop[simplified])

lemma ldrop_eSuc_conv_ltl: "ldrop (eSuc n) xs = ltl (ldrop n xs)"
proof(induct xs arbitrary: n)
  case LCons thus ?case by(cases n rule: co.enat.exhaust) simp_all
qed simp_all

lemma ldrop_ltl: "ldrop n (ltl xs) = ldrop (eSuc n) xs"
proof(induct xs arbitrary: n)
  case LCons thus ?case by(cases n rule: co.enat.exhaust) simp_all
qed simp_all

lemma lnull_ldropn [simp]: "lnull (ldropn n xs) \<longleftrightarrow> llength xs \<le> enat n"
proof(induction n arbitrary: xs)
  case (Suc n)
  from Suc.IH[of "ltl xs"] show ?case
    by(cases xs)(simp_all add: eSuc_enat[symmetric])
qed(simp add: zero_enat_def[symmetric])

lemma ldrop_eq_LNil [simp]: "ldrop n xs = LNil \<longleftrightarrow> llength xs \<le> n"
proof(induction xs arbitrary: n)
  case (LCons x xs n)
  thus ?case by(cases n rule: co.enat.exhaust) simp_all
qed simp_all

lemma lnull_ldrop [simp]: "lnull (ldrop n xs) \<longleftrightarrow> llength xs \<le> n"
unfolding lnull_def by(fact ldrop_eq_LNil)

lemma ldropn_eq_LNil: "(ldropn n xs = LNil) = (llength xs \<le> enat n)"
using lnull_ldropn unfolding lnull_def .

lemma ldropn_all: "llength xs \<le> enat m \<Longrightarrow> ldropn m xs = LNil"
by(simp add: ldropn_eq_LNil)

lemma ldrop_all: "llength xs \<le> m \<Longrightarrow> ldrop m xs = LNil"
by(simp)

lemma ltl_ldrop: "ltl (ldrop n xs) = ldrop n (ltl xs)"
by(simp add: ldrop_eSuc_conv_ltl ldrop_ltl)

lemma ldrop_eSuc:
  "ldrop (eSuc n) xs = (case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> ldrop n xs')"
by(cases xs) simp_all

lemma ldrop_LCons:
  "ldrop n (LCons x xs) = (case n of 0 \<Rightarrow> LCons x xs | eSuc n' \<Rightarrow> ldrop n' xs)"
by(cases n rule: enat_coexhaust) simp_all

lemma ldrop_inf [code, simp]: "ldrop \<infinity> xs = LNil"
by(induction xs)(simp_all add: ldrop_LCons enat_cocase_inf)

lemma ldrop_enat [code]: "ldrop (enat n) xs = ldropn n xs"
proof(induct n arbitrary: xs)
  case Suc thus ?case
    by(cases xs)(simp_all add: eSuc_enat[symmetric])
qed(simp add: zero_enat_def[symmetric])

lemma lfinite_ldropn [simp]: "lfinite (ldropn n xs) = lfinite xs"
by(induct n arbitrary: xs)(simp_all add: ldropn_Suc split: llist.split)

lemma lfinite_ldrop [simp]:
  "lfinite (ldrop n xs) \<longleftrightarrow> lfinite xs \<or> n = \<infinity>"
by(cases n)(simp_all add: ldrop_enat)

lemma ldropn_ltl: "ldropn n (ltl xs) = ldropn (Suc n) xs"
by(simp add: ldropn_def funpow_swap1)

lemmas ldrop_eSuc_ltl = ldropn_ltl[symmetric]

lemma lset_ldropn_subset: "lset (ldropn n xs) \<subseteq> lset xs"
by(induct n arbitrary: xs)(fastforce simp add: ldropn_Suc split: llist.split_asm)+

lemma in_lset_ldropnD: "x \<in> lset (ldropn n xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldropn_subset[of n xs] by auto

lemma lset_ldrop_subset: "lset (ldrop n xs) \<subseteq> lset xs"
proof(induct xs arbitrary: n)
  case LCons thus ?case
    by(cases n rule: co.enat.exhaust) auto
qed simp_all

lemma in_lset_ldropD: "x \<in> lset (ldrop n xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldrop_subset[of n xs] by(auto)

lemma lappend_ltake_ldrop: "lappend (ltake n xs) (ldrop n xs) = xs"
by(coinduction arbitrary: n xs rule: llist.coinduct_strong)
  (auto simp add: ldrop_ltl ltl_ltake intro!: arg_cong2[where f=lappend])

lemma ldropn_lappend:
  "ldropn n (lappend xs ys) =
  (if enat n < llength xs then lappend (ldropn n xs) ys
   else ldropn (n - the_enat (llength xs)) ys)"
proof(induct n arbitrary: xs)
  case 0
  thus ?case by(simp add: zero_enat_def[symmetric] lappend_lnull1)
next
  case (Suc n)
  { fix zs
    assume "llength zs \<le> enat n"
    hence "the_enat (eSuc (llength zs)) = Suc (the_enat (llength zs))"
      by(auto intro!: the_enat_eSuc iff del: not_infinity_eq) }
  note eq = this
  from Suc show ?case
    by(cases xs)(auto simp add: not_less not_le eSuc_enat[symmetric] eq)
qed

lemma ldropn_lappend2:
  "llength xs \<le> enat n \<Longrightarrow> ldropn n (lappend xs ys) = ldropn (n - the_enat (llength xs)) ys"
by(auto simp add: ldropn_lappend)

lemma lappend_ltake_enat_ldropn [simp]: "lappend (ltake (enat n) xs) (ldropn n xs) = xs"
by(fold ldrop_enat)(rule lappend_ltake_ldrop)

lemma ldrop_lappend:
  "ldrop n (lappend xs ys) =
  (if n < llength xs then lappend (ldrop n xs) ys
   else ldrop (n - llength xs) ys)"
  \<comment> \<open>cannot prove this directly using fixpoint induction,
     because @{term "(-) :: enat \<Rightarrow> enat \<Rightarrow> enat"} is not a least fixpoint\<close>
by(cases n)(cases "llength xs", simp_all add: ldropn_lappend not_less ldrop_enat)

lemma ltake_plus_conv_lappend:
  "ltake (n + m) xs = lappend (ltake n xs) (ltake m (ldrop n xs))"
by(coinduction arbitrary: n m xs rule: llist.coinduct_strong)(auto intro!: exI simp add: iadd_is_0 ltl_ltake epred_iadd1 ldrop_ltl)

lemma ldropn_eq_LConsD:
  "ldropn n xs = LCons y ys \<Longrightarrow> enat n < llength xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n) thus ?case by(cases xs)(simp_all add: Suc_ile_eq)
qed

lemma ldrop_eq_LConsD:
  "ldrop n xs = LCons y ys \<Longrightarrow> n < llength xs"
by(rule ccontr)(simp add: not_less ldrop_all)

lemma ldropn_lmap [simp]: "ldropn n (lmap f xs) = lmap f (ldropn n xs)"
by(induct n arbitrary: xs)(simp_all add: ldropn_Suc split: llist.split)

lemma ldrop_lmap [simp]: "ldrop n (lmap f xs) = lmap f (ldrop n xs)"
proof(induct xs arbitrary: n)
  case LCons thus ?case by(cases n rule: co.enat.exhaust) simp_all
qed simp_all

lemma ldropn_ldropn [simp]:
  "ldropn n (ldropn m xs) = ldropn (n + m) xs"
by(induct m arbitrary: xs)(auto simp add: ldropn_Suc split: llist.split)

lemma ldrop_ldrop [simp]:
  "ldrop n (ldrop m xs) = ldrop (n + m) xs"
proof(induct xs arbitrary: m)
  case LCons thus ?case by(cases m rule: co.enat.exhaust)(simp_all add: iadd_Suc_right)
qed simp_all

lemma llength_ldropn [simp]: "llength (ldropn n xs) = llength xs - enat n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n) thus ?case by(cases xs)(simp_all add: eSuc_enat[symmetric])
qed

lemma enat_llength_ldropn:
  "enat n \<le> llength xs \<Longrightarrow> enat (n - m) \<le> llength (ldropn m xs)"
by(cases "llength xs") simp_all

lemma ldropn_llist_of [simp]: "ldropn n (llist_of xs) = llist_of (drop n xs)"
proof(induct n arbitrary: xs)
  case Suc thus ?case by(cases xs) simp_all
qed simp

lemma ldrop_llist_of: "ldrop (enat n) (llist_of xs) = llist_of (drop n xs)"
proof(induct xs arbitrary: n)
  case Cons thus ?case by(cases n)(simp_all add: zero_enat_def[symmetric] eSuc_enat[symmetric])
qed simp

lemma drop_list_of:
  "lfinite xs \<Longrightarrow> drop n (list_of xs) = list_of (ldropn n xs)"
by (metis ldropn_llist_of list_of_llist_of llist_of_list_of)

lemma llength_ldrop: "llength (ldrop n xs) = (if n = \<infinity> then 0 else llength xs - n)"
proof(induct xs arbitrary: n)
  case (LCons x xs)
  thus ?case by simp(cases n rule: co.enat.exhaust, simp_all)
qed simp_all

lemma ltake_ldropn: "ltake n (ldropn m xs) = ldropn m (ltake (n + enat m) xs)"
by(induct m arbitrary: n xs)(auto simp add: zero_enat_def[symmetric] ldropn_Suc eSuc_enat[symmetric] iadd_Suc_right split: llist.split)

lemma ldropn_ltake: "ldropn n (ltake m xs) = ltake (m - enat n) (ldropn n xs)"
by(induct n arbitrary: m xs)(auto simp add: zero_enat_def[symmetric] ltake_LCons ldropn_Suc eSuc_enat[symmetric] iadd_Suc_right split: llist.split co.enat.split_asm)

lemma ltake_ldrop: "ltake n (ldrop m xs) = ldrop m (ltake (n + m) xs)"
by(induct xs arbitrary: n m)(simp_all add: ldrop_LCons iadd_Suc_right split: co.enat.split)

lemma ldrop_ltake: "ldrop n (ltake m xs) = ltake (m - n) (ldrop n xs)"
by(induct xs arbitrary: n m)(simp_all add: ltake_LCons ldrop_LCons split: co.enat.split)

subsection {* Taking the $n$-th element of a lazy list: @{term "lnth" } *}

lemma lnth_LNil:
  "lnth LNil n = undefined n"
by(cases n)(simp_all add: lnth.simps)

lemma lnth_0 [simp]:
  "lnth (LCons x xs) 0 = x"
by(simp add: lnth.simps)

lemma lnth_Suc_LCons [simp]:
  "lnth (LCons x xs) (Suc n) = lnth xs n"
by(simp add: lnth.simps)

lemma lnth_LCons:
  "lnth (LCons x xs) n = (case n of 0 \<Rightarrow> x | Suc n' \<Rightarrow> lnth xs n')"
by(cases n) simp_all

lemma lnth_LCons': "lnth (LCons x xs) n = (if n = 0 then x else lnth xs (n - 1))"
by(simp add: lnth_LCons split: nat.split)

lemma lhd_conv_lnth:
  "\<not> lnull xs \<Longrightarrow> lhd xs = lnth xs 0"
by(auto simp add: lhd_def not_lnull_conv)

lemmas lnth_0_conv_lhd = lhd_conv_lnth[symmetric]

lemma lnth_ltl: "\<not> lnull xs \<Longrightarrow> lnth (ltl xs) n = lnth xs (Suc n)"
by(auto simp add: not_lnull_conv)

lemma lhd_ldropn:
  "enat n < llength xs \<Longrightarrow> lhd (ldropn n xs) = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `enat (Suc n) < llength xs`
  have "enat n < llength xs'" by(simp add: Suc_ile_eq)
  hence "lhd (ldropn n xs') = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma lhd_ldrop:
  assumes "n < llength xs"
  shows "lhd (ldrop n xs) = lnth xs (the_enat n)"
proof -
  from assms obtain n' where n: "n = enat n'" by(cases n) auto
  from assms show ?thesis unfolding n
  proof(induction n' arbitrary: xs)
    case 0 thus ?case
      by(simp add: zero_enat_def[symmetric] lhd_conv_lnth)
  next
    case (Suc n')
    thus ?case
      by(cases xs)(simp_all add: eSuc_enat[symmetric], simp add: eSuc_enat)
  qed
qed

lemma lnth_beyond:
  "llength xs \<le> enat n \<Longrightarrow> lnth xs n = undefined (n - (case llength xs of enat m \<Rightarrow> m))"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric] lnth_def lnull_def)
next
  case Suc thus ?case
    by(cases xs)(simp_all add: zero_enat_def lnth_def eSuc_enat[symmetric] split: enat.split, auto simp add: eSuc_enat)
qed

lemma lnth_lmap [simp]:
  "enat n < llength xs \<Longrightarrow> lnth (lmap f xs) n = f (lnth xs n)"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) simp_all
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where xs: "xs = LCons x xs'" and len: "enat n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lmap f xs') n = f (lnth xs' n)" by(rule Suc)
  with xs show ?case by simp
qed

lemma lnth_ldropn [simp]:
  "enat (n + m) < llength xs \<Longrightarrow> lnth (ldropn n xs) m = lnth xs (m + n)"
proof(induct n arbitrary: xs)
  case (Suc n)
  from `enat (Suc n + m) < llength xs`
  obtain x xs' where "xs = LCons x xs'" by(cases xs) auto
  moreover with `enat (Suc n + m) < llength xs`
  have "enat (n + m) < llength xs'" by(simp add: Suc_ile_eq)
  hence "lnth (ldropn n xs') m = lnth xs' (m + n)" by(rule Suc)
  ultimately show ?case by simp
qed simp

lemma lnth_ldrop [simp]:
  "n + enat m < llength xs \<Longrightarrow> lnth (ldrop n xs) m = lnth xs (m + the_enat n)"
by(cases n)(simp_all add: ldrop_enat)

lemma in_lset_conv_lnth:
  "x \<in> lset xs \<longleftrightarrow> (\<exists>n. enat n < llength xs \<and> lnth xs n = x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then obtain n where "enat n < llength xs" "lnth xs n = x" by blast
  thus ?lhs
  proof(induct n arbitrary: xs)
    case 0
    thus ?case
      by(auto simp add: zero_enat_def[symmetric] not_lnull_conv)
  next
    case (Suc n)
    thus ?case
      by(cases xs)(auto simp add: eSuc_enat[symmetric])
  qed
next
  assume ?lhs
  thus ?rhs
  proof(induct)
    case (find xs)
    show ?case by(auto intro: exI[where x=0] simp add: zero_enat_def[symmetric])
  next
    case (step x' xs)
    thus ?case
      by(auto 4 4 intro: exI[where x="Suc n" for n] ileI1 simp add: eSuc_enat[symmetric])
  qed
qed

lemma lset_conv_lnth: "lset xs = {lnth xs n|n. enat n < llength xs}"
by(auto simp add: in_lset_conv_lnth)

lemma lnth_llist_of [simp]: "lnth (llist_of xs) = nth xs"
proof(rule ext)
  fix n
  show "lnth (llist_of xs) n = xs ! n"
  proof(induct xs arbitrary: n)
    case Nil thus ?case by(cases n)(simp_all add: nth_def lnth_def)
  next
    case Cons thus ?case by(simp add: lnth_LCons split: nat.split)
  qed
qed

lemma nth_list_of [simp]:
  assumes "lfinite xs"
  shows "nth (list_of xs) = lnth xs"
using assms
by induct(auto intro: simp add: nth_def lnth_LNil nth_Cons split: nat.split)

lemma lnth_lappend1:
  "enat n < llength xs \<Longrightarrow> lnth (lappend xs ys) n = lnth xs n"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(auto simp add: zero_enat_def[symmetric] not_lnull_conv)
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" and len: "enat n < llength xs'"
    by(cases xs)(auto simp add: Suc_ile_eq)
  from len have "lnth (lappend xs' ys) n = lnth xs' n" by(rule Suc)
  thus ?case by simp
qed

lemma lnth_lappend_llist_of:
  "lnth (lappend (llist_of xs) ys) n =
  (if n < length xs then xs ! n else lnth ys (n - length xs))"
proof(induct xs arbitrary: n)
  case (Cons x xs) thus ?case by(cases n) auto
qed simp

lemma lnth_lappend2:
  "\<lbrakk> llength xs = enat k; k \<le> n \<rbrakk> \<Longrightarrow> lnth (lappend xs ys) n = lnth ys (n - k)"
proof(induct n arbitrary: xs k)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric] lappend_lnull1)
next
  case (Suc n) thus ?case
    by(cases xs)(auto simp add: eSuc_def zero_enat_def split: enat.split_asm)
qed

lemma lnth_lappend:
  "lnth (lappend xs ys) n = (if enat n < llength xs then lnth xs n else lnth ys (n - the_enat (llength xs)))"
by(cases "llength xs")(auto simp add: lnth_lappend1 lnth_lappend2)

lemma lnth_ltake:
  "enat m < n \<Longrightarrow> lnth (ltake n xs) m = lnth xs m"
proof(induct m arbitrary: xs n)
  case 0 thus ?case
    by(cases n rule: enat_coexhaust)(auto, cases xs, auto)
next
  case (Suc m)
  from `enat (Suc m) < n` obtain n' where "n = eSuc n'"
    by(cases n rule: enat_coexhaust) auto
  with `enat (Suc m) < n` have "enat m < n'" by(simp add: eSuc_enat[symmetric])
  with Suc `n = eSuc n'` show ?case by(cases xs) auto
qed

lemma ldropn_Suc_conv_ldropn:
  "enat n < llength xs \<Longrightarrow> LCons (lnth xs n) (ldropn (Suc n) xs) = ldropn n xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by(cases xs) auto
next
  case (Suc n)
  from `enat (Suc n) < llength xs` obtain x xs'
    where [simp]: "xs = LCons x xs'" by(cases xs) auto
  from `enat (Suc n) < llength xs`
  have "enat n < llength xs'" by(simp add: Suc_ile_eq)
  hence "LCons (lnth xs' n) (ldropn (Suc n) xs') = ldropn n xs'" by(rule Suc)
  thus ?case by simp
qed

lemma ltake_Suc_conv_snoc_lnth:
  "enat m < llength xs \<Longrightarrow> ltake (enat (Suc m)) xs = lappend (ltake (enat m) xs) (LCons (lnth xs m) LNil)"
by(metis eSuc_enat eSuc_plus_1 ltake_plus_conv_lappend ldrop_enat ldropn_Suc_conv_ldropn ltake_0 ltake_eSuc_LCons one_eSuc)

lemma lappend_eq_lappend_conv:
  assumes len: "llength xs = llength us"
  shows "lappend xs ys = lappend us vs \<longleftrightarrow>
         xs = us \<and> (lfinite xs \<longrightarrow> ys = vs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  thus ?lhs by(auto simp add: lappend_inf)
next
  assume eq: ?lhs
  show ?rhs
  proof(intro conjI impI)
    show "xs = us" using len eq
    proof(coinduction arbitrary: xs us)
      case (Eq_llist xs us)
      thus ?case
        by(cases xs us rule: llist.exhaust[case_product llist.exhaust]) auto
    qed
    assume "lfinite xs"
    then obtain xs' where "xs = llist_of xs'"
      by(auto simp add: lfinite_eq_range_llist_of)
    hence "lappend (llist_of xs') ys = lappend (llist_of xs') vs"
      using eq `xs = us` by blast
    thus "ys = vs"
      by (induct xs') simp_all
  qed
qed


subsection{* iterates *}

lemmas iterates [code, nitpick_simp] = iterates.ctr
  and lnull_iterates = iterates.simps(1)
  and lhd_iterates = iterates.simps(2)
  and ltl_iterates = iterates.simps(3)

lemma lfinite_iterates [iff]: "\<not> lfinite (iterates f x)"
proof
  assume "lfinite (iterates f x)"
  thus False
    by(induct zs\<equiv>"iterates f x" arbitrary: x rule: lfinite_induct) auto
qed

lemma lmap_iterates: "lmap f (iterates f x) = iterates f (f x)"
by(coinduction arbitrary: x) auto

lemma iterates_lmap: "iterates f x = LCons x (lmap f (iterates f x))"
by(simp add: lmap_iterates)(rule iterates)

lemma lappend_iterates: "lappend (iterates f x) xs = iterates f x"
by(coinduction arbitrary: x) auto

lemma [simp]:
  fixes f :: "'a \<Rightarrow> 'a"
  shows lnull_funpow_lmap: "lnull ((lmap f ^^ n) xs) \<longleftrightarrow> lnull xs"
  and lhd_funpow_lmap: "\<not> lnull xs \<Longrightarrow> lhd ((lmap f ^^ n) xs) = (f ^^ n) (lhd xs)"
  and ltl_funpow_lmap: "\<not> lnull xs \<Longrightarrow> ltl ((lmap f ^^ n) xs) = (lmap f ^^ n) (ltl xs)"
by(induct n) simp_all

lemma iterates_equality:
  assumes h: "\<And>x. h x = LCons x (lmap f (h x))"
  shows "h = iterates f"
proof -
  { fix x
    have "\<not> lnull (h x)" "lhd (h x) = x" "ltl (h x) = lmap f (h x)"
      by(subst h, simp)+ }
  note [simp] = this

  { fix x
    define n :: nat where "n = 0"
    have "(lmap f ^^ n) (h x) = (lmap f ^^ n) (iterates f x)"
      by(coinduction arbitrary: n)(auto simp add: funpow_swap1 lmap_iterates intro: exI[where x="Suc n" for n]) }
  thus ?thesis by auto
qed

lemma llength_iterates [simp]: "llength (iterates f x) = \<infinity>"
by(coinduction arbitrary: x rule: enat_coinduct)(auto simp add: epred_llength)

lemma ldropn_iterates: "ldropn n (iterates f x) = iterates f ((f ^^ n) x)"
proof(induct n arbitrary: x)
  case 0 thus ?case by simp
next
  case (Suc n)
  have "ldropn (Suc n) (iterates f x) = ldropn n (iterates f (f x))"
    by(subst iterates)simp
  also have "\<dots> = iterates f ((f ^^ n) (f x))" by(rule Suc)
  finally show ?case by(simp add: funpow_swap1)
qed

lemma ldrop_iterates: "ldrop (enat n) (iterates f x) = iterates f ((f ^^ n) x)"
proof(induct n arbitrary: x)
  case Suc thus ?case
    by(subst iterates)(simp add: eSuc_enat[symmetric] funpow_swap1)
qed(simp add: zero_enat_def[symmetric])

lemma lnth_iterates [simp]: "lnth (iterates f x) n = (f ^^ n) x"
proof(induct n arbitrary: x)
  case 0 thus ?case by(subst iterates) simp
next
  case (Suc n)
  hence "lnth (iterates f (f x)) n = (f ^^ n) (f x)" .
  thus ?case by(subst iterates)(simp add: funpow_swap1)
qed

lemma lset_iterates:
  "lset (iterates f x) = {(f ^^ n) x|n. True}"
by(auto simp add: lset_conv_lnth)

lemma lset_repeat [simp]: "lset (repeat x) = {x}"
by(simp add: lset_iterates id_def[symmetric])

subsection {*
  More on the prefix ordering on lazy lists: @{term "lprefix"} and @{term "lstrict_prefix"}
*}

lemma lstrict_prefix_code [code, simp]:
  "lstrict_prefix LNil LNil \<longleftrightarrow> False"
  "lstrict_prefix LNil (LCons y ys) \<longleftrightarrow> True"
  "lstrict_prefix (LCons x xs) LNil \<longleftrightarrow> False"
  "lstrict_prefix (LCons x xs) (LCons y ys) \<longleftrightarrow> x = y \<and> lstrict_prefix xs ys"
by(auto simp add: lstrict_prefix_def)

lemma lmap_lprefix: "xs \<sqsubseteq> ys \<Longrightarrow> lmap f xs \<sqsubseteq> lmap f ys"
by(rule monotoneD[OF monotone_lmap])

lemma lprefix_llength_eq_imp_eq:
  "\<lbrakk> xs \<sqsubseteq> ys; llength xs = llength ys \<rbrakk> \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv)

lemma lprefix_llength_le: "xs \<sqsubseteq> ys \<Longrightarrow> llength xs \<le> llength ys"
using monotone_llength by(rule monotoneD)

lemma lstrict_prefix_llength_less:
  assumes "lstrict_prefix xs ys"
  shows "llength xs < llength ys"
proof(rule ccontr)
  assume "\<not> llength xs < llength ys"
  moreover from `lstrict_prefix xs ys` have "xs \<sqsubseteq> ys" "xs \<noteq> ys"
    unfolding lstrict_prefix_def by simp_all
  from `xs \<sqsubseteq> ys` have "llength xs \<le> llength ys"
    by(rule lprefix_llength_le)
  ultimately have "llength xs = llength ys" by auto
  with `xs \<sqsubseteq> ys` have "xs = ys"
    by(rule lprefix_llength_eq_imp_eq)
  with `xs \<noteq> ys` show False by contradiction
qed

lemma lstrict_prefix_lfinite1: "lstrict_prefix xs ys \<Longrightarrow> lfinite xs"
by (metis lstrict_prefix_def not_lfinite_lprefix_conv_eq)

lemma wfP_lstrict_prefix: "wfP lstrict_prefix"
proof(unfold wfP_def)
  have "wf {(x :: enat, y). x < y}"
    unfolding wf_def by(blast intro: less_induct)
  hence "wf (inv_image {(x, y). x < y} llength)" by(rule wf_inv_image)
  moreover have "{(xs, ys). lstrict_prefix xs ys} \<subseteq> inv_image {(x, y). x < y} llength"
    by(auto intro: lstrict_prefix_llength_less)
  ultimately show "wf {(xs, ys). lstrict_prefix xs ys}" by(rule wf_subset)
qed

lemma llist_less_induct[case_names less]:
  "(\<And>xs. (\<And>ys. lstrict_prefix ys xs \<Longrightarrow> P ys) \<Longrightarrow> P xs) \<Longrightarrow> P xs"
by(rule wfP_induct[OF wfP_lstrict_prefix]) blast

lemma ltake_enat_eq_imp_eq: "(\<And>n. ltake (enat n) xs = ltake (enat n) ys) \<Longrightarrow> xs = ys"
by(coinduction arbitrary: xs ys)(auto simp add: zero_enat_def lnull_def neq_LNil_conv ltake_eq_LNil_iff eSuc_enat[symmetric] elim: allE[where x="Suc n" for n])

lemma ltake_enat_lprefix_imp_lprefix:
  assumes "\<And>n. lprefix (ltake (enat n) xs) (ltake (enat n) ys)"
  shows "lprefix xs ys"
proof -
  have "ccpo.admissible Sup (\<le>) (\<lambda>n. ltake n xs \<sqsubseteq> ltake n ys)" by simp
  hence "ltake (Sup (range enat)) xs \<sqsubseteq> ltake (Sup (range enat)) ys"
    by(rule ccpo.admissibleD)(auto intro: assms)
  thus ?thesis by(simp add: ltake_all)
qed

lemma lprefix_conv_lappend: "xs \<sqsubseteq> ys \<longleftrightarrow> (\<exists>zs. ys = lappend xs zs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  hence "ys = lappend xs (ldrop (llength xs) ys)"
    by(coinduction arbitrary: xs ys)(auto dest: lprefix_lnullD lprefix_lhdD intro: lprefix_ltlI simp add: not_lnull_conv lprefix_LCons_conv intro: exI[where x=LNil])
  thus ?rhs ..
next
  assume ?rhs
  thus ?lhs by(coinduct rule: lprefix_coinduct) auto
qed

lemma lappend_lprefixE:
  assumes "lappend xs ys \<sqsubseteq> zs"
  obtains zs' where "zs = lappend xs zs'"
using assms unfolding lprefix_conv_lappend by(auto simp add: lappend_assoc)

lemma lprefix_lfiniteD:
  "\<lbrakk> xs \<sqsubseteq> ys; lfinite ys \<rbrakk> \<Longrightarrow> lfinite xs"
unfolding lprefix_conv_lappend by auto

lemma lprefix_lappendD:
  assumes "xs \<sqsubseteq> lappend ys zs"
  shows "xs \<sqsubseteq> ys \<or> ys \<sqsubseteq> xs"
proof(rule ccontr)
  assume "\<not> (xs \<sqsubseteq> ys \<or> ys \<sqsubseteq> xs)"
  hence "\<not> xs \<sqsubseteq> ys" "\<not> ys \<sqsubseteq> xs" by simp_all
  from `xs \<sqsubseteq> lappend ys zs` obtain xs'
    where "lappend xs xs' = lappend ys zs"
    unfolding lprefix_conv_lappend by auto
  hence eq: "lappend (ltake (llength ys) xs) (lappend (ldrop (llength ys) xs) xs') =
             lappend ys zs"
    unfolding lappend_assoc[symmetric] by(simp only: lappend_ltake_ldrop)
  moreover have "llength xs \<ge> llength ys"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence "llength xs < llength ys" by simp
    hence "ltake (llength ys) xs = xs" by(simp add: ltake_all)
    hence "lappend xs (lappend (ldrop (llength ys) xs) xs') =
           lappend (ltake (llength xs) ys) (lappend (ldrop (llength xs) ys) zs)"
      unfolding lappend_assoc[symmetric] lappend_ltake_ldrop
      using eq by(simp add: lappend_assoc)
    hence xs: "xs = ltake (llength xs) ys" using `llength xs < llength ys`
      by(subst (asm) lappend_eq_lappend_conv)(auto simp add: min_def)
    have "xs \<sqsubseteq> ys" by(subst xs) auto
    with `\<not> xs \<sqsubseteq> ys` show False by contradiction
  qed
  ultimately have ys: "ys = ltake (llength ys) xs"
    by(subst (asm) lappend_eq_lappend_conv)(simp_all add: min_def)
  have "ys \<sqsubseteq> xs" by(subst ys) auto
  with `\<not> ys \<sqsubseteq> xs` show False by contradiction
qed

lemma lstrict_prefix_lappend_conv:
  "lstrict_prefix xs (lappend xs ys) \<longleftrightarrow> lfinite xs \<and> \<not> lnull ys"
proof -
  { assume "lfinite xs" "xs = lappend xs ys"
    hence "lnull ys" by induct auto }
  thus ?thesis
    by(auto simp add: lstrict_prefix_def lprefix_lappend lappend_inf lappend_lnull2
            elim: contrapos_np)
qed

lemma lprefix_llist_ofI:
  "\<exists>zs. ys = xs @ zs \<Longrightarrow> llist_of xs \<sqsubseteq> llist_of ys"
by(clarsimp simp add: lappend_llist_of_llist_of[symmetric] lprefix_lappend)

lemma lprefix_llist_of [simp]: "llist_of xs \<sqsubseteq> llist_of ys \<longleftrightarrow> prefix xs ys"
by(auto simp add: prefix_def lprefix_conv_lappend)(metis lfinite_lappend lfinite_llist_of list_of_lappend list_of_llist_of lappend_llist_of_llist_of)+

lemma llimit_induct [case_names LNil LCons limit]:
  \<comment> \<open>The limit case is just an instance of admissibility\<close>
  assumes LNil: "P LNil"
  and LCons: "\<And>x xs. \<lbrakk> lfinite xs; P xs \<rbrakk> \<Longrightarrow> P (LCons x xs)"
  and limit: "(\<And>ys. lstrict_prefix ys xs \<Longrightarrow> P ys) \<Longrightarrow> P xs"
  shows "P xs"
proof(rule limit)
  fix ys
  assume "lstrict_prefix ys xs"
  hence "lfinite ys" by(rule lstrict_prefix_lfinite1)
  thus "P ys" by(induct)(blast intro: LNil LCons)+
qed

lemma lmap_lstrict_prefix:
  "lstrict_prefix xs ys \<Longrightarrow> lstrict_prefix (lmap f xs) (lmap f ys)"
by (metis llength_lmap lmap_lprefix lprefix_llength_eq_imp_eq lstrict_prefix_def)

lemma lprefix_lnthD:
  assumes "xs \<sqsubseteq> ys" and "enat n < llength xs"
  shows "lnth xs n = lnth ys n"
using assms by (metis lnth_lappend1 lprefix_conv_lappend)

lemma lfinite_lSup_chain:
  assumes chain: "Complete_Partial_Order.chain (\<sqsubseteq>) A"
  shows "lfinite (lSup A) \<longleftrightarrow> finite A \<and> (\<forall>xs \<in> A. lfinite xs)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume ?lhs
  then obtain n where n: "llength (lSup A) = enat n" unfolding lfinite_conv_llength_enat ..
  have "llength ` A \<subseteq> {..<enat (Suc n)}"
    by(auto dest!: chain_lprefix_lSup[OF chain] lprefix_llength_le simp add: n intro: le_less_trans)
  hence "finite (llength ` A)" by(rule finite_subset)(simp add: finite_lessThan_enat_iff)
  moreover have "inj_on llength A" by(rule inj_onI)(auto 4 3 dest: chainD[OF chain] lprefix_llength_eq_imp_eq)
  ultimately show "finite A" by(rule finite_imageD)
next
  assume ?rhs
  hence "finite A" "\<forall>xs\<in>A. lfinite xs" by simp_all
  show ?lhs
  proof(cases "A = {}")
    case False
    with chain `finite A`
    have "lSup A \<in> A" by(rule ccpo.in_chain_finite[OF llist_ccpo])
    with `\<forall>xs\<in>A. lfinite xs` show ?thesis ..
  qed simp
qed(rule lfinite_lSupD)

text {* Setup for @{term "lprefix"} for Nitpick *}

definition finite_lprefix :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> bool"
where "finite_lprefix = (\<sqsubseteq>)"

lemma finite_lprefix_nitpick_simps [nitpick_simp]:
  "finite_lprefix xs LNil \<longleftrightarrow> xs = LNil"
  "finite_lprefix LNil xs \<longleftrightarrow> True"
  "finite_lprefix xs (LCons y ys) \<longleftrightarrow>
   xs = LNil \<or> (\<exists>xs'. xs = LCons y xs' \<and> finite_lprefix xs' ys)"
by(simp_all add: lprefix_LCons_conv finite_lprefix_def lnull_def)

lemma lprefix_nitpick_simps [nitpick_simp]:
  "xs \<sqsubseteq> ys = (if lfinite xs then finite_lprefix xs ys else xs = ys)"
by(simp add: finite_lprefix_def not_lfinite_lprefix_conv_eq)

hide_const (open) finite_lprefix
hide_fact (open) finite_lprefix_def finite_lprefix_nitpick_simps lprefix_nitpick_simps

subsection {* Length of the longest common prefix *}

lemma llcp_simps [simp, code, nitpick_simp]:
  shows llcp_LNil1: "llcp LNil ys = 0"
  and llcp_LNil2: "llcp xs LNil = 0"
  and llcp_LCons: "llcp (LCons x xs) (LCons y ys) = (if x = y then eSuc (llcp xs ys) else 0)"
by(simp_all add: llcp_def enat_unfold split: llist.split)

lemma llcp_eq_0_iff:
  "llcp xs ys = 0 \<longleftrightarrow> lnull xs \<or> lnull ys \<or> lhd xs \<noteq> lhd ys"
by(simp add: llcp_def)

lemma epred_llcp:
  "\<lbrakk> \<not> lnull xs; \<not> lnull ys; lhd xs = lhd ys \<rbrakk>
  \<Longrightarrow>  epred (llcp xs ys) = llcp (ltl xs) (ltl ys)"
by(simp add: llcp_def)

lemma llcp_commute: "llcp xs ys = llcp ys xs"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto simp add: llcp_eq_0_iff epred_llcp)

lemma llcp_same_conv_length [simp]: "llcp xs xs = llength xs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: llcp_eq_0_iff epred_llcp epred_llength)

lemma llcp_lappend_same [simp]:
  "llcp (lappend xs ys) (lappend xs zs) = llength xs + llcp ys zs"
by(coinduction arbitrary: xs rule: enat_coinduct)(auto simp add: iadd_is_0 llcp_eq_0_iff epred_iadd1 epred_llcp epred_llength)

lemma llcp_lprefix1 [simp]: "xs \<sqsubseteq> ys \<Longrightarrow> llcp xs ys = llength xs"
by (metis add_0_right lappend_LNil2 llcp_LNil1 llcp_lappend_same lprefix_conv_lappend)

lemma llcp_lprefix2 [simp]: "ys \<sqsubseteq> xs \<Longrightarrow> llcp xs ys = llength ys"
by (metis llcp_commute llcp_lprefix1)

lemma llcp_le_length: "llcp xs ys \<le> min (llength xs) (llength ys)"
proof -
  define m n where "m = llcp xs ys" and "n = min (llength xs) (llength ys)"
  hence "(m, n) \<in> {(llcp xs ys, min (llength xs) (llength ys)) |xs ys :: 'a llist. True}" by blast
  thus "m \<le> n"
  proof(coinduct rule: enat_leI)
    case (Leenat m n)
    then obtain xs ys :: "'a llist" where "m = llcp xs ys" "n = min (llength xs) (llength ys)" by blast
    thus ?case
      by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(auto 4 3 intro!: exI[where x="Suc 0"] simp add: eSuc_enat[symmetric] iadd_Suc_right zero_enat_def[symmetric])
  qed
qed

lemma llcp_ltake1: "llcp (ltake n xs) ys = min n (llcp xs ys)"
by(coinduction arbitrary: n xs ys rule: enat_coinduct)(auto simp add: llcp_eq_0_iff enat_min_eq_0_iff epred_llcp ltl_ltake)

lemma llcp_ltake2: "llcp xs (ltake n ys) = min n (llcp xs ys)"
by(metis llcp_commute llcp_ltake1)

lemma llcp_ltake [simp]: "llcp (ltake n xs) (ltake m ys) = min (min n m) (llcp xs ys)"
by(metis llcp_ltake1 llcp_ltake2 min.assoc)

subsection {* Zipping two lazy lists to a lazy list of pairs @{term "lzip" } *}

lemma lzip_simps [simp, code, nitpick_simp]:
  "lzip LNil ys = LNil"
  "lzip xs LNil = LNil"
  "lzip (LCons x xs) (LCons y ys) = LCons (x, y) (lzip xs ys)"
by(auto intro: llist.expand)

lemma lnull_lzip [simp]: "lnull (lzip xs ys) \<longleftrightarrow> lnull xs \<or> lnull ys"
by(simp add: lzip_def)

lemma lzip_eq_LNil_conv: "lzip xs ys = LNil \<longleftrightarrow> xs = LNil \<or> ys = LNil"
using lnull_lzip unfolding lnull_def .

lemmas lhd_lzip = lzip.sel(1)
  and ltl_lzip = lzip.sel(2)

lemma lzip_eq_LCons_conv:
  "lzip xs ys = LCons z zs \<longleftrightarrow>
   (\<exists>x xs' y ys'. xs = LCons x xs' \<and> ys = LCons y ys' \<and> z = (x, y) \<and> zs = lzip xs' ys')"
by(cases xs ys rule: llist.exhaust[case_product llist.exhaust]) auto

lemma lzip_lappend:
  "llength xs = llength us
  \<Longrightarrow> lzip (lappend xs ys) (lappend us vs) = lappend (lzip xs us) (lzip ys vs)"
by(coinduction arbitrary: xs ys us vs rule: llist.coinduct_strong)(auto 4 6 simp add: llength_ltl)

lemma llength_lzip [simp]:
  "llength (lzip xs ys) = min (llength xs) (llength ys)"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto simp add: enat_min_eq_0_iff epred_llength)

lemma ltake_lzip: "ltake n (lzip xs ys) = lzip (ltake n xs) (ltake n ys)"
by(coinduction arbitrary: xs ys n)(auto simp add: ltl_ltake)

lemma ldropn_lzip [simp]:
  "ldropn n (lzip xs ys) = lzip (ldropn n xs) (ldropn n ys)"
by(induct n arbitrary: xs ys)(simp_all add: ldropn_Suc split: llist.split)

lemma
  fixes F
  defines "F \<equiv> \<lambda>lzip (xs, ys). case xs of LNil \<Rightarrow> LNil | LCons x xs' \<Rightarrow> case ys of LNil \<Rightarrow> LNil | LCons y ys' \<Rightarrow> LCons (x, y) (curry lzip xs' ys')"
  shows lzip_conv_fixp: "lzip \<equiv> curry (ccpo.fixp (fun_lub lSup) (fun_ord (\<sqsubseteq>)) F)" (is "?lhs \<equiv> ?rhs")
  and lzip_mono: "mono_llist (\<lambda>lzip. F lzip xs)" (is "?mono xs")
proof(intro eq_reflection ext)
  show mono: "\<And>xs. ?mono xs" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix xs ys
  show "lzip xs ys = ?rhs xs ys"
  proof(coinduction arbitrary: xs ys)
    case Eq_llist show ?case
      by(subst (1 3 4) llist.mono_body_fixp[OF mono])(auto simp add: F_def split: llist.split)
  qed
qed

lemma monotone_lzip: "monotone (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) (\<sqsubseteq>) (case_prod lzip)"
by(rule llist.fixp_preserves_mono2[OF lzip_mono lzip_conv_fixp]) simp

lemma mono2mono_lzip1 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lzip1: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (\<lambda>xs. lzip xs ys)"
by(simp add: monotone_lzip[simplified])

lemma mono2mono_lzip2 [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lzip2: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (\<lambda>ys. lzip xs ys)"
by(simp add: monotone_lzip[simplified])

lemma mcont_lzip: "mcont (prod_lub lSup lSup) (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) lSup (\<sqsubseteq>) (case_prod lzip)"
by(rule llist.fixp_preserves_mcont2[OF lzip_mono lzip_conv_fixp]) simp

lemma mcont2mcont_lzip1 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lzip1: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (\<lambda>xs. lzip xs ys)"
by(simp add: mcont_lzip[simplified])

lemma mcont2mcont_lzip2 [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lzip2: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (\<lambda>ys. lzip xs ys)"
by(simp add: mcont_lzip[simplified])

lemma ldrop_lzip [simp]: "ldrop n (lzip xs ys) = lzip (ldrop n xs) (ldrop n ys)"
proof(induct xs arbitrary: ys n)
  case LCons
  thus ?case by(cases ys n rule: llist.exhaust[case_product co.enat.exhaust]) simp_all
qed simp_all

lemma lzip_iterates:
  "lzip (iterates f x) (iterates g y) = iterates (\<lambda>(x, y). (f x, g y)) (x, y)"
by(coinduction arbitrary: x y) auto

lemma lzip_llist_of [simp]:
  "lzip (llist_of xs) (llist_of ys) = llist_of (zip xs ys)"
proof(induct xs arbitrary: ys)
  case (Cons x xs')
  thus ?case by(cases ys) simp_all
qed simp

lemma lnth_lzip:
  "\<lbrakk> enat n < llength xs; enat n < llength ys \<rbrakk>
  \<Longrightarrow> lnth (lzip xs ys) n = (lnth xs n, lnth ys n)"
proof(induct n arbitrary: xs ys)
  case 0 thus ?case
    by(simp add: zero_enat_def[symmetric] lnth_0_conv_lhd)
next
  case (Suc n)
  thus ?case
    by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(auto simp add: eSuc_enat[symmetric])
qed

lemma lset_lzip:
  "lset (lzip xs ys) =
   {(lnth xs n, lnth ys n)|n. enat n < min (llength xs) (llength ys)}"
by(auto simp add: lset_conv_lnth lnth_lzip)(auto intro!: exI simp add: lnth_lzip)

lemma lset_lzipD1: "(x, y) \<in> lset (lzip xs ys) \<Longrightarrow> x \<in> lset xs"
proof(induct "lzip xs ys" arbitrary: xs ys rule: lset_induct)
  case [symmetric]: find
  thus ?case by(auto simp add: lzip_eq_LCons_conv)
next
  case (step z zs)
  thus ?case by -(drule sym, auto simp add: lzip_eq_LCons_conv)
qed

lemma lset_lzipD2: "(x, y) \<in> lset (lzip xs ys) \<Longrightarrow> y \<in> lset ys"
proof(induct "lzip xs ys" arbitrary: xs ys rule: lset_induct)
  case [symmetric]: find
  thus ?case by(auto simp add: lzip_eq_LCons_conv)
next
  case (step z zs)
  thus ?case by -(drule sym, auto simp add: lzip_eq_LCons_conv)
qed

lemma lset_lzip_same [simp]: "lset (lzip xs xs) = (\<lambda>x. (x, x)) ` lset xs"
by(auto 4 3 simp add: lset_lzip in_lset_conv_lnth)

lemma lfinite_lzip [simp]:
  "lfinite (lzip xs ys) \<longleftrightarrow> lfinite xs \<or> lfinite ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(induct zs\<equiv>"lzip xs ys" arbitrary: xs ys rule: lfinite_induct) fastforce+
next
  assume ?rhs (is "?xs \<or> ?ys")
  thus ?lhs
  proof
    assume ?xs
    thus ?thesis
    proof(induct arbitrary: ys)
      case (lfinite_LConsI xs x)
      thus ?case by(cases ys) simp_all
    qed simp
  next
    assume ?ys
    thus ?thesis
    proof(induct arbitrary: xs)
      case (lfinite_LConsI ys y)
      thus ?case by(cases xs) simp_all
    qed simp
  qed
qed

lemma lzip_eq_lappend_conv:
  assumes eq: "lzip xs ys = lappend us vs"
  shows "\<exists>xs' xs'' ys' ys''. xs = lappend xs' xs'' \<and> ys = lappend ys' ys'' \<and>
                             llength xs' = llength ys' \<and> us = lzip xs' ys' \<and>
                             vs = lzip xs'' ys''"
proof -
  let ?xs' = "ltake (llength us) xs"
  let ?xs'' = "ldrop (llength us) xs"
  let ?ys' = "ltake (llength us) ys"
  let ?ys'' = "ldrop (llength us) ys"

  from eq have "llength (lzip xs ys) = llength (lappend us vs)" by simp
  hence "min (llength xs) (llength ys) \<ge> llength us"
    by(auto simp add: enat_le_plus_same)
  hence len: "llength xs \<ge> llength us" "llength ys \<ge> llength us" by(auto)

  hence leneq: "llength ?xs' = llength ?ys'" by(simp add: min_def)
  have xs: "xs = lappend ?xs' ?xs''" and ys: "ys = lappend ?ys' ?ys''"
    by(simp_all add: lappend_ltake_ldrop)
  hence "lappend us vs = lzip (lappend ?xs' ?xs'') (lappend ?ys' ?ys'')"
    using eq by simp
  with len have "lappend us vs = lappend (lzip ?xs' ?ys') (lzip ?xs'' ?ys'')"
    by(simp add: lzip_lappend min_def)
  hence us: "us = lzip ?xs' ?ys'"
    and vs: "lfinite us \<longrightarrow> vs = lzip ?xs'' ?ys''" using len
    by(simp_all add: min_def lappend_eq_lappend_conv)
  show ?thesis
  proof(cases "lfinite us")
    case True
    with leneq xs ys us vs len show ?thesis by fastforce
  next
    case False
    let ?xs'' = "lmap fst vs"
    let ?ys'' = "lmap snd vs"
    from False have "lappend us vs = us" by(simp add: lappend_inf)
    moreover from False have "llength us = \<infinity>"
      by(rule not_lfinite_llength)
    moreover with len
    have "llength xs = \<infinity>" "llength ys = \<infinity>" by auto
    moreover with `llength us = \<infinity>`
    have "xs = ?xs'" "ys = ?ys'" by(simp_all add: ltake_all)
    from `llength us = \<infinity>` len
    have "\<not> lfinite ?xs'" "\<not> lfinite ?ys'"
      by(auto simp del: llength_ltake lfinite_ltake
             simp add: ltake_all dest: lfinite_llength_enat)
    with `xs = ?xs'` `ys = ?ys'`
    have "xs = lappend ?xs' ?xs''" "ys = lappend ?ys' ?ys''"
      by(simp_all add: lappend_inf)
    moreover have "vs = lzip ?xs'' ?ys''"
      by(coinduction arbitrary: vs) auto
    ultimately show ?thesis using eq by(fastforce simp add: ltake_all)
  qed
qed

lemma lzip_lmap [simp]:
  "lzip (lmap f xs) (lmap g ys) = lmap (\<lambda>(x, y). (f x, g y)) (lzip xs ys)"
by(coinduction arbitrary: xs ys) auto

lemma lzip_lmap1:
  "lzip (lmap f xs) ys = lmap (\<lambda>(x, y). (f x, y)) (lzip xs ys)"
by(subst (4) llist.map_ident[symmetric])(simp only: lzip_lmap)

lemma lzip_lmap2:
  "lzip xs (lmap f ys) = lmap (\<lambda>(x, y). (x, f y)) (lzip xs ys)"
by(subst (1) llist.map_ident[symmetric])(simp only: lzip_lmap)

lemma lmap_fst_lzip_conv_ltake:
  "lmap fst (lzip xs ys) = ltake (min (llength xs) (llength ys)) xs"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

lemma lmap_snd_lzip_conv_ltake:
  "lmap snd (lzip xs ys) = ltake (min (llength xs) (llength ys)) ys"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

lemma lzip_conv_lzip_ltake_min_llength:
  "lzip xs ys =
  lzip (ltake (min (llength xs) (llength ys)) xs)
       (ltake (min (llength xs) (llength ys)) ys)"
by(coinduction arbitrary: xs ys)(auto simp add: enat_min_eq_0_iff ltl_ltake epred_llength)

subsection {* Taking and dropping from a lazy list: @{term "ltakeWhile"} and @{term "ldropWhile"} *}

lemma ltakeWhile_simps [simp, code, nitpick_simp]:
  shows ltakeWhile_LNil: "ltakeWhile P LNil = LNil"
  and ltakeWhile_LCons: "ltakeWhile P (LCons x xs) = (if P x then LCons x (ltakeWhile P xs) else LNil)"
by(auto simp add: ltakeWhile_def intro: llist.expand)

lemma ldropWhile_simps [simp, code]:
  shows ldropWhile_LNil: "ldropWhile P LNil = LNil"
  and ldropWhile_LCons: "ldropWhile P (LCons x xs) = (if P x then ldropWhile P xs else LCons x xs)"
by(simp_all add: ldropWhile.simps)

lemma fixes f F P
  defines "F \<equiv> \<lambda>ltakeWhile xs. case xs of LNil \<Rightarrow> LNil | LCons x xs \<Rightarrow> if P x then LCons x (ltakeWhile xs) else LNil"
  shows ltakeWhile_conv_fixp: "ltakeWhile P \<equiv> ccpo.fixp (fun_lub lSup) (fun_ord lprefix) F" (is "?lhs \<equiv> ?rhs")
  and ltakeWhile_mono: "\<And>xs. mono_llist (\<lambda>ltakeWhile. F ltakeWhile xs)" (is "PROP ?mono")
proof(intro eq_reflection ext)
  show mono: "PROP ?mono" unfolding F_def by(tactic {* Partial_Function.mono_tac @{context} 1 *})
  fix xs
  show "?lhs xs = ?rhs xs"
  proof(coinduction arbitrary: xs)
    case Eq_llist
    show ?case by(subst (1 3 4) llist.mono_body_fixp[OF mono])(auto simp add: F_def split: llist.split prod.split co.enat.split)
  qed
qed

lemma mono2mono_ltakeWhile[THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ltakeWhile: "monotone lprefix lprefix (ltakeWhile P)"
by(rule llist.fixp_preserves_mono1[OF ltakeWhile_mono ltakeWhile_conv_fixp]) simp

lemma mcont2mcont_ltakeWhile [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ltakeWhile: "mcont lSup lprefix lSup lprefix (ltakeWhile P)"
by(rule llist.fixp_preserves_mcont1[OF ltakeWhile_mono ltakeWhile_conv_fixp]) simp

lemma mono_llist_ltakeWhile [partial_function_mono]:
  "mono_llist F \<Longrightarrow> mono_llist (\<lambda>f. ltakeWhile P (F f))"
by(rule mono2mono_ltakeWhile)

lemma mono2mono_ldropWhile [THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_ldropWhile: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (ldropWhile P)"
by(rule llist.fixp_preserves_mono1[OF ldropWhile.mono ldropWhile_def]) simp

lemma mcont2mcont_ldropWhile [THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_ldropWhile: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (ldropWhile P)"
by(rule llist.fixp_preserves_mcont1[OF ldropWhile.mono ldropWhile_def]) simp

lemma lnull_ltakeWhile [simp]: "lnull (ltakeWhile P xs) \<longleftrightarrow> (\<not> lnull xs \<longrightarrow> \<not> P (lhd xs))"
by(cases xs) simp_all

lemma ltakeWhile_eq_LNil_iff: "ltakeWhile P xs = LNil \<longleftrightarrow> (xs \<noteq> LNil \<longrightarrow> \<not> P (lhd xs))"
using lnull_ltakeWhile unfolding lnull_def .

lemmas lhd_ltakeWhile = ltakeWhile.sel(1)

lemma ltl_ltakeWhile:
  "ltl (ltakeWhile P xs) = (if P (lhd xs) then ltakeWhile P (ltl xs) else LNil)"
by(cases xs) simp_all

lemma lprefix_ltakeWhile: "ltakeWhile P xs \<sqsubseteq> xs"
by(coinduction arbitrary: xs)(auto simp add: ltl_ltakeWhile)

lemma llength_ltakeWhile_le: "llength (ltakeWhile P xs) \<le> llength xs"
by(rule lprefix_llength_le)(rule lprefix_ltakeWhile)

lemma ltakeWhile_nth: "enat i < llength (ltakeWhile P xs) \<Longrightarrow> lnth (ltakeWhile P xs) i = lnth xs i"
by(rule lprefix_lnthD[OF lprefix_ltakeWhile])

lemma ltakeWhile_all: "\<forall>x\<in>lset xs. P x \<Longrightarrow> ltakeWhile P xs = xs"
by(coinduction arbitrary: xs)(auto 4 3 simp add: ltl_ltakeWhile simp del: ltakeWhile.disc_iff dest: in_lset_ltlD)

lemma lset_ltakeWhileD:
  assumes "x \<in> lset (ltakeWhile P xs)"
  shows "x \<in> lset xs \<and> P x"
using assms
by(induct ys\<equiv>"ltakeWhile P xs" arbitrary: xs rule: llist_set_induct)(auto simp add: ltl_ltakeWhile dest: in_lset_ltlD)

lemma lset_ltakeWhile_subset:
  "lset (ltakeWhile P xs) \<subseteq> lset xs \<inter> {x. P x}"
by(auto dest: lset_ltakeWhileD)

lemma ltakeWhile_all_conv: "ltakeWhile P xs = xs \<longleftrightarrow> lset xs \<subseteq> {x. P x}"
by (metis Int_Collect Int_absorb2 le_infE lset_ltakeWhile_subset ltakeWhile_all)

lemma llength_ltakeWhile_all: "llength (ltakeWhile P xs) = llength xs \<longleftrightarrow> ltakeWhile P xs = xs"
by(auto intro: lprefix_llength_eq_imp_eq lprefix_ltakeWhile)

lemma ldropWhile_eq_LNil_iff: "ldropWhile P xs = LNil \<longleftrightarrow> (\<forall>x \<in> lset xs. P x)"
by(induct xs) simp_all

lemma lnull_ldropWhile [simp]:
  "lnull (ldropWhile P xs) \<longleftrightarrow> (\<forall>x \<in> lset xs. P x)" (is "?lhs \<longleftrightarrow> ?rhs")
unfolding lnull_def by(simp add: ldropWhile_eq_LNil_iff)

lemma lset_ldropWhile_subset:
  "lset (ldropWhile P xs) \<subseteq> lset xs"
by(induct xs) auto

lemma in_lset_ldropWhileD: "x \<in> lset (ldropWhile P xs) \<Longrightarrow> x \<in> lset xs"
using lset_ldropWhile_subset[of P xs] by auto

lemma ltakeWhile_lmap: "ltakeWhile P (lmap f xs) = lmap f (ltakeWhile (P \<circ> f) xs)"
by(coinduction arbitrary: xs)(auto simp add: ltl_ltakeWhile)

lemma ldropWhile_lmap: "ldropWhile P (lmap f xs) = lmap f (ldropWhile (P \<circ> f) xs)"
by(induct xs) simp_all

lemma llength_ltakeWhile_lt_iff: "llength (ltakeWhile P xs) < llength xs \<longleftrightarrow> (\<exists>x\<in>lset xs. \<not> P x)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "ltakeWhile P xs \<noteq> xs" by auto
  thus ?rhs by(auto simp add: ltakeWhile_all_conv)
next
  assume ?rhs
  hence "ltakeWhile P xs \<noteq> xs" by(auto simp add: ltakeWhile_all_conv)
  thus ?lhs unfolding llength_ltakeWhile_all[symmetric]
    using llength_ltakeWhile_le[of P xs] by(auto)
qed

lemma ltakeWhile_K_False [simp]: "ltakeWhile (\<lambda>_. False) xs = LNil"
by(simp add: ltakeWhile_def)

lemma ltakeWhile_K_True [simp]: "ltakeWhile (\<lambda>_. True) xs = xs"
by(coinduction arbitrary: xs) simp

lemma ldropWhile_K_False [simp]: "ldropWhile (\<lambda>_. False) = id"
proof
  fix xs
  show "ldropWhile (\<lambda>_. False) xs = id xs"
    by(induct xs) simp_all
qed

lemma ldropWhile_K_True [simp]: "ldropWhile (\<lambda>_. True) xs = LNil"
by(induct xs)(simp_all)

lemma lappend_ltakeWhile_ldropWhile [simp]:
  "lappend (ltakeWhile P xs) (ldropWhile P xs) = xs"
by(coinduction arbitrary: xs rule: llist.coinduct_strong)(auto 4 4 simp add: not_lnull_conv lset_lnull intro: ccontr)

lemma ltakeWhile_lappend:
  "ltakeWhile P (lappend xs ys) =
  (if \<exists>x\<in>lset xs. \<not> P x then ltakeWhile P xs
   else lappend xs (ltakeWhile P ys))"
proof(coinduction arbitrary: xs rule: llist.coinduct_strong)
  case (Eq_llist xs)
  have ?lnull by(auto simp add: lset_lnull)
  moreover have ?LCons
    by(clarsimp split: if_split_asm split del: if_split simp add: ltl_ltakeWhile)(auto 4 3 simp add: not_lnull_conv)
  ultimately show ?case ..
qed

lemma ldropWhile_lappend:
  "ldropWhile P (lappend xs ys) =
  (if \<exists>x\<in>lset xs. \<not> P x then lappend (ldropWhile P xs) ys
   else if lfinite xs then ldropWhile P ys else LNil)"
proof(cases "\<exists>x\<in>lset xs. \<not> P x")
  case True
  then obtain x where "x \<in> lset xs" "\<not> P x"  by blast
  thus ?thesis by induct simp_all
next
  case False
  note xs = this
  show ?thesis
  proof(cases "lfinite xs")
    case False
    thus ?thesis using xs by(simp add: lappend_inf)
  next
    case True
    thus ?thesis using xs by induct simp_all
  qed
qed

lemma lfinite_ltakeWhile:
  "lfinite (ltakeWhile P xs) \<longleftrightarrow> lfinite xs \<or> (\<exists>x \<in> lset xs. \<not> P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs by(auto simp add: ltakeWhile_all)
next
  assume "?rhs"
  thus ?lhs
  proof
    assume "lfinite xs"
    with lprefix_ltakeWhile show ?thesis by(rule lprefix_lfiniteD)
  next
    assume "\<exists>x\<in>lset xs. \<not> P x"
    then obtain x where "x \<in> lset xs" "\<not> P x" by blast
    thus ?thesis by(induct rule: lset_induct) simp_all
  qed
qed

lemma llength_ltakeWhile_eq_infinity:
  "llength (ltakeWhile P xs) = \<infinity> \<longleftrightarrow> \<not> lfinite xs \<and> ltakeWhile P xs = xs"
unfolding llength_ltakeWhile_all[symmetric] llength_eq_infty_conv_lfinite[symmetric]
by(auto)(auto simp add: llength_eq_infty_conv_lfinite lfinite_ltakeWhile intro: sym)

lemma llength_ltakeWhile_eq_infinity':
  "llength (ltakeWhile P xs) = \<infinity> \<longleftrightarrow> \<not> lfinite xs \<and> (\<forall>x\<in>lset xs. P x)"
by (metis lfinite_ltakeWhile llength_eq_infty_conv_lfinite)

lemma lzip_ltakeWhile_fst: "lzip (ltakeWhile P xs) ys = ltakeWhile (P \<circ> fst) (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: ltl_ltakeWhile simp del: simp del: ltakeWhile.disc_iff)

lemma lzip_ltakeWhile_snd: "lzip xs (ltakeWhile P ys) = ltakeWhile (P \<circ> snd) (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: ltl_ltakeWhile)

lemma ltakeWhile_lappend1:
  "\<lbrakk> x \<in> lset xs; \<not> P x \<rbrakk> \<Longrightarrow> ltakeWhile P (lappend xs ys) = ltakeWhile P xs"
by(induct rule: lset_induct) simp_all

lemma ltakeWhile_lappend2:
  "lset xs \<subseteq> {x. P x}
  \<Longrightarrow> ltakeWhile P (lappend xs ys) = lappend xs (ltakeWhile P ys)"
by(coinduction arbitrary: xs ys rule: llist.coinduct_strong)(auto 4 4 simp add: not_lnull_conv lappend_lnull1)

lemma ltakeWhile_cong [cong, fundef_cong]:
  assumes xs: "xs = ys"
  and PQ: "\<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x"
  shows "ltakeWhile P xs = ltakeWhile Q ys"
using PQ unfolding xs
by(coinduction arbitrary: ys)(auto simp add: ltl_ltakeWhile not_lnull_conv)

lemma lnth_llength_ltakeWhile:
  assumes len: "llength (ltakeWhile P xs) < llength xs"
  shows "\<not> P (lnth xs (the_enat (llength (ltakeWhile P xs))))"
proof
  assume P: "P (lnth xs (the_enat (llength (ltakeWhile P xs))))"
  from len obtain len where "llength (ltakeWhile P xs) = enat len"
    by(cases "llength (ltakeWhile P xs)") auto
  with P len show False apply simp
  proof(induct len arbitrary: xs)
    case 0 thus ?case by(simp add: zero_enat_def[symmetric] lnth_0_conv_lhd)
  next
    case (Suc len) thus ?case by(cases xs)(auto split: if_split_asm simp add: eSuc_enat[symmetric])
  qed
qed

lemma assumes "\<exists>x\<in>lset xs. \<not> P x"
  shows lhd_ldropWhile: "\<not> P (lhd (ldropWhile P xs))" (is ?thesis1)
  and lhd_ldropWhile_in_lset: "lhd (ldropWhile P xs) \<in> lset xs" (is ?thesis2)
proof -
  from assms obtain x where "x \<in> lset xs" "\<not> P x" by blast
  thus ?thesis1 ?thesis2 by induct simp_all
qed

lemma ldropWhile_eq_ldrop:
  "ldropWhile P xs = ldrop (llength (ltakeWhile P xs)) xs"
  (is "?lhs = ?rhs")
proof(rule lprefix_antisym)
  show "?lhs \<sqsubseteq> ?rhs"
    by(induct arbitrary: xs rule: ldropWhile.fixp_induct)(auto split: llist.split)
  show "?rhs \<sqsubseteq> ?lhs"
  proof(induct arbitrary: xs rule: ldrop.fixp_induct)
    case (3 ldrop xs)
    thus ?case by(cases xs) auto
  qed simp_all
qed

lemma ldropWhile_cong [cong]:
  "\<lbrakk> xs = ys; \<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x \<rbrakk> \<Longrightarrow> ldropWhile P xs = ldropWhile Q ys"
by(simp add: ldropWhile_eq_ldrop)

lemma ltakeWhile_repeat:
  "ltakeWhile P (repeat x) = (if P x then repeat x else LNil)"
by(coinduction arbitrary: x)(auto simp add: ltl_ltakeWhile)

lemma ldropWhile_repeat: "ldropWhile P (repeat x) = (if P x then LNil else repeat x)"
by(simp add: ldropWhile_eq_ldrop ltakeWhile_repeat)

lemma lfinite_ldropWhile: "lfinite (ldropWhile P xs) \<longleftrightarrow> (\<exists>x \<in> lset xs. \<not> P x) \<longrightarrow> lfinite xs"
by(auto simp add: ldropWhile_eq_ldrop llength_eq_infty_conv_lfinite lfinite_ltakeWhile)

lemma llength_ldropWhile:
  "llength (ldropWhile P xs) =
  (if \<exists>x\<in>lset xs. \<not> P x then llength xs - llength (ltakeWhile P xs) else 0)"
by(auto simp add: ldropWhile_eq_ldrop llength_ldrop llength_ltakeWhile_all ltakeWhile_all_conv llength_ltakeWhile_eq_infinity zero_enat_def dest!: lfinite_llength_enat)

lemma lhd_ldropWhile_conv_lnth:
  "\<exists>x\<in>lset xs. \<not> P x \<Longrightarrow> lhd (ldropWhile P xs) = lnth xs (the_enat (llength (ltakeWhile P xs)))"
by(simp add: ldropWhile_eq_ldrop lhd_ldrop llength_ltakeWhile_lt_iff)

subsection {* @{term "llist_all2"} *}

lemmas llist_all2_LNil_LNil = llist.rel_inject(1)
lemmas llist_all2_LNil_LCons = llist.rel_distinct(1)
lemmas llist_all2_LCons_LNil = llist.rel_distinct(2)
lemmas llist_all2_LCons_LCons = llist.rel_inject(2)

lemma llist_all2_LNil1 [simp]: "llist_all2 P LNil xs \<longleftrightarrow> xs = LNil"
by(cases xs) simp_all

lemma llist_all2_LNil2 [simp]: "llist_all2 P xs LNil \<longleftrightarrow> xs = LNil"
by(cases xs) simp_all

lemma llist_all2_LCons1:
  "llist_all2 P (LCons x xs) ys \<longleftrightarrow> (\<exists>y ys'. ys = LCons y ys' \<and> P x y \<and> llist_all2 P xs ys')"
by(cases ys) simp_all

lemma llist_all2_LCons2:
  "llist_all2 P xs (LCons y ys) \<longleftrightarrow> (\<exists>x xs'. xs = LCons x xs' \<and> P x y \<and> llist_all2 P xs' ys)"
by(cases xs) simp_all

lemma llist_all2_llist_of [simp]:
  "llist_all2 P (llist_of xs) (llist_of ys) = list_all2 P xs ys"
by(induct xs ys rule: list_induct2')(simp_all)

lemma llist_all2_conv_lzip:
  "llist_all2 P xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>(x, y) \<in> lset (lzip xs ys). P x y)"
by(auto 4 4 elim!: GrpE simp add:
  llist_all2_def lmap_fst_lzip_conv_ltake lmap_snd_lzip_conv_ltake ltake_all
  intro!: GrpI relcomppI[of _ xs _ _ ys])

lemma llist_all2_llengthD:
  "llist_all2 P xs ys \<Longrightarrow> llength xs = llength ys"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_lnullD: "llist_all2 P xs ys \<Longrightarrow> lnull xs \<longleftrightarrow> lnull ys"
unfolding lnull_def by auto

lemma llist_all2_all_lnthI:
  "\<lbrakk> llength xs = llength ys;
     \<And>n. enat n < llength xs \<Longrightarrow> P (lnth xs n) (lnth ys n) \<rbrakk>
  \<Longrightarrow> llist_all2 P xs ys"
by(auto simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_lnthD:
  "\<lbrakk> llist_all2 P xs ys; enat n < llength xs \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastforce simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_lnthD2:
  "\<lbrakk> llist_all2 P xs ys; enat n < llength ys \<rbrakk> \<Longrightarrow> P (lnth xs n) (lnth ys n)"
by(fastforce simp add: llist_all2_conv_lzip lset_lzip)

lemma llist_all2_conv_all_lnth:
  "llist_all2 P xs ys \<longleftrightarrow>
   llength xs = llength ys \<and>
   (\<forall>n. enat n < llength ys \<longrightarrow> P (lnth xs n) (lnth ys n))"
by(auto dest: llist_all2_llengthD llist_all2_lnthD2 intro: llist_all2_all_lnthI)

lemma llist_all2_True [simp]: "llist_all2 (\<lambda>_ _. True) xs ys \<longleftrightarrow> llength xs = llength ys"
by(simp add: llist_all2_conv_all_lnth)

lemma llist_all2_reflI:
  "(\<And>x. x \<in> lset xs \<Longrightarrow> P x x) \<Longrightarrow> llist_all2 P xs xs"
by(auto simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_lmap1:
  "llist_all2 P (lmap f xs) ys \<longleftrightarrow> llist_all2 (\<lambda>x. P (f x)) xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lmap2:
  "llist_all2 P xs (lmap g ys) \<longleftrightarrow> llist_all2 (\<lambda>x y. P x (g y)) xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lfiniteD:
  "llist_all2 P xs ys \<Longrightarrow> lfinite xs \<longleftrightarrow> lfinite ys"
by(drule llist_all2_llengthD)(simp add: lfinite_conv_llength_enat)

lemma llist_all2_coinduct[consumes 1, case_names LNil LCons, case_conclusion LCons lhd ltl, coinduct pred]:
  assumes major: "X xs ys"
  and step:
  "\<And>xs ys. X xs ys \<Longrightarrow> lnull xs \<longleftrightarrow> lnull ys"
  "\<And>xs ys. \<lbrakk> X xs ys; \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys) \<and> (X (ltl xs) (ltl ys) \<or> llist_all2 P (ltl xs) (ltl ys))"
  shows "llist_all2 P xs ys"
proof(rule llist_all2_all_lnthI)
  from major show "llength xs = llength ys"
    by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto 4 3 dest: step llist_all2_llengthD simp add: epred_llength)

  fix n
  assume "enat n < llength xs"
  thus "P (lnth xs n) (lnth ys n)"
    using major `llength xs = llength ys`
  proof(induct n arbitrary: xs ys)
    case 0 thus ?case
      by(cases "lnull xs")(auto dest: step simp add: zero_enat_def[symmetric] lnth_0_conv_lhd)
  next
    case (Suc n)
    from step[OF `X xs ys`] `enat (Suc n) < llength xs` Suc show ?case
      by(auto 4 3 simp add: not_lnull_conv Suc_ile_eq intro: Suc.hyps llist_all2_lnthD dest: llist_all2_llengthD)
  qed
qed

lemma llist_all2_cases[consumes 1, case_names LNil LCons, cases pred]:
  assumes "llist_all2 P xs ys"
  obtains (LNil) "xs = LNil" "ys = LNil"
  | (LCons) x xs' y ys'
    where "xs = LCons x xs'" and "ys = LCons y ys'"
    and "P x y" and "llist_all2 P xs' ys'"
using assms
by(cases xs)(auto simp add: llist_all2_LCons1)

lemma llist_all2_mono:
  "\<lbrakk> llist_all2 P xs ys; \<And>x y. P x y \<Longrightarrow> P' x y \<rbrakk> \<Longrightarrow> llist_all2 P' xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_left: "llist_all2 (\<lambda>x _. P x) xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>x\<in>lset xs. P x)"
by(fastforce simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_right: "llist_all2 (\<lambda>_. P) xs ys \<longleftrightarrow> llength xs = llength ys \<and> (\<forall>x\<in>lset ys. P x)"
by(fastforce simp add: llist_all2_conv_all_lnth lset_conv_lnth)

lemma llist_all2_lsetD1: "\<lbrakk> llist_all2 P xs ys; x \<in> lset xs \<rbrakk> \<Longrightarrow> \<exists>y\<in>lset ys. P x y"
by(auto 4 4 simp add: llist_all2_conv_lzip lset_lzip lset_conv_lnth split_beta lnth_lzip simp del: split_paired_All)

lemma llist_all2_lsetD2: "\<lbrakk> llist_all2 P xs ys; y \<in> lset ys \<rbrakk> \<Longrightarrow> \<exists>x\<in>lset xs. P x y"
by(auto 4 4 simp add: llist_all2_conv_lzip lset_lzip lset_conv_lnth split_beta lnth_lzip simp del: split_paired_All)

lemma llist_all2_conj:
  "llist_all2 (\<lambda>x y. P x y \<and> Q x y) xs ys \<longleftrightarrow> llist_all2 P xs ys \<and> llist_all2 Q xs ys"
by(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_lhdD:
  "\<lbrakk> llist_all2 P xs ys; \<not> lnull xs \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys)"
by(auto simp add: not_lnull_conv llist_all2_LCons1)

lemma llist_all2_lhdD2:
  "\<lbrakk> llist_all2 P xs ys; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys)"
by(auto simp add: not_lnull_conv llist_all2_LCons2)

lemma llist_all2_ltlI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ltl xs) (ltl ys)"
by(cases xs)(auto simp add: llist_all2_LCons1)

lemma llist_all2_lappendI:
  assumes 1: "llist_all2 P xs ys"
  and 2: "\<lbrakk> lfinite xs; lfinite ys \<rbrakk> \<Longrightarrow> llist_all2 P xs' ys'"
  shows "llist_all2 P (lappend xs xs') (lappend ys ys')"
proof(cases "lfinite xs")
  case True
  with 1 have "lfinite ys" by(auto dest: llist_all2_lfiniteD)
  from 1 2[OF True this] show ?thesis
    by(coinduction arbitrary: xs ys)(auto dest: llist_all2_lnullD llist_all2_lhdD intro: llist_all2_ltlI simp add: lappend_eq_LNil_iff)
next
  case False
  with 1 have "\<not> lfinite ys" by(auto dest: llist_all2_lfiniteD)
  with False 1 show ?thesis by(simp add: lappend_inf)
qed

lemma llist_all2_lappend1D:
  assumes "llist_all2 P (lappend xs xs') ys"
  shows "llist_all2 P xs (ltake (llength xs) ys)"
  and "lfinite xs \<Longrightarrow> llist_all2 P xs' (ldrop (llength xs) ys)"
proof -
  from assms have len: "llength xs + llength xs' = llength ys" by(auto dest: llist_all2_llengthD)
  hence len_xs: "llength xs \<le> llength ys" and len_xs': "llength xs' \<le> llength ys"
    by (metis enat_le_plus_same llength_lappend)+

  show "llist_all2 P xs (ltake (llength xs) ys)"
  proof(rule llist_all2_all_lnthI)
    show "llength xs = llength (ltake (llength xs) ys)"
      using len_xs by(simp add: min_def)
  next
    fix n
    assume n: "enat n < llength xs"
    also have "\<dots> \<le> llength (lappend xs xs')" by(simp add: enat_le_plus_same)
    finally have "P (lnth (lappend xs xs') n) (lnth ys n)"
      using assms by -(rule llist_all2_lnthD)
    also from n have "lnth ys n = lnth (ltake (llength xs) ys) n" by(rule lnth_ltake[symmetric])
    also from n have "lnth (lappend xs xs') n = lnth xs n" by(simp add: lnth_lappend1)
    finally show "P (lnth xs n) (lnth (ltake (llength xs) ys) n)" .
  qed

  assume "lfinite xs"
  thus "llist_all2 P xs' (ldrop (llength xs) ys)" using assms
    by(induct arbitrary: ys)(auto simp add: llist_all2_LCons1)
qed

lemma lmap_eq_lmap_conv_llist_all2:
  "lmap f xs = lmap g ys \<longleftrightarrow> llist_all2 (\<lambda>x y. f x = g y) xs ys" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
    by(coinduction arbitrary: xs ys)(auto simp add: neq_LNil_conv lnull_def LNil_eq_lmap lmap_eq_LNil)
next
  assume ?rhs
  thus ?lhs
    by(coinduction arbitrary: xs ys)(auto dest: llist_all2_lnullD llist_all2_lhdD llist_all2_ltlI)
qed

lemma llist_all2_expand:
  "\<lbrakk> lnull xs \<longleftrightarrow> lnull ys;
     \<lbrakk> \<not> lnull xs; \<not> lnull ys \<rbrakk> \<Longrightarrow> P (lhd xs) (lhd ys) \<and> llist_all2 P (ltl xs) (ltl ys) \<rbrakk>
   \<Longrightarrow> llist_all2 P xs ys"
by(cases xs)(auto simp add: not_lnull_conv)

lemma llist_all2_llength_ltakeWhileD:
  assumes major: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llength (ltakeWhile Q1 xs) = llength (ltakeWhile Q2 ys)"
using major
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto 4 3 simp add: not_lnull_conv llist_all2_LCons1 llist_all2_LCons2 dest!: Q)

lemma llist_all2_lzipI:
  "\<lbrakk> llist_all2 P xs ys; llist_all2 P' xs' ys' \<rbrakk>
  \<Longrightarrow> llist_all2 (rel_prod P P') (lzip xs xs') (lzip ys ys')"
by(coinduction arbitrary: xs xs' ys ys')(auto 6 6 dest: llist_all2_lhdD llist_all2_lnullD intro: llist_all2_ltlI)

lemma llist_all2_ltakeI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ltake n xs) (ltake n ys)"
by(auto simp add: llist_all2_conv_all_lnth lnth_ltake)

lemma llist_all2_ldropnI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ldropn n xs) (ldropn n ys)"
by(cases "llength ys")(auto simp add: llist_all2_conv_all_lnth)

lemma llist_all2_ldropI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (ldrop n xs) (ldrop n ys)"
by(cases "llength ys")(auto simp add: llist_all2_conv_all_lnth llength_ldrop)

lemma llist_all2_lSupI:
  assumes "Complete_Partial_Order.chain (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) Y" "\<forall>(xs, ys)\<in>Y. llist_all2 P xs ys"
  shows "llist_all2 P (lSup (fst ` Y)) (lSup (snd ` Y))"
using assms
proof(coinduction arbitrary: Y)
  case LNil
  thus ?case
    by(auto dest: llist_all2_lnullD simp add: split_beta)
next
  case (LCons Y)
  note chain = `Complete_Partial_Order.chain _ Y`
  from LCons have Y: "\<And>xs ys. (xs, ys) \<in> Y \<Longrightarrow> llist_all2 P xs ys" by blast
  from LCons obtain xs ys where xsysY: "(xs, ys) \<in> Y"
    and [simp]: "\<not> lnull xs" "\<not> lnull ys"
    by(auto 4 3 dest: llist_all2_lnullD simp add: split_beta)
  from xsysY have "lhd xs \<in> lhd ` (fst ` Y \<inter> {xs. \<not> lnull xs})"
    by(auto intro: rev_image_eqI)
  hence "(THE x. x \<in> lhd ` (fst ` Y \<inter> {xs. \<not> lnull xs})) = lhd xs"
    by(rule the_equality)(auto dest!: lprefix_lhdD chainD[OF chain xsysY])
  moreover from xsysY have "lhd ys \<in> lhd ` (snd ` Y \<inter> {xs. \<not> lnull xs})"
    by(auto intro: rev_image_eqI)
  hence "(THE x. x \<in> lhd ` (snd ` Y \<inter> {xs. \<not> lnull xs})) = lhd ys"
    by(rule the_equality)(auto dest!: lprefix_lhdD chainD[OF chain xsysY])
  moreover from xsysY have "llist_all2 P xs ys" by(rule Y)
  hence "P (lhd xs) (lhd ys)" by(rule llist_all2_lhdD) simp
  ultimately have ?lhd using LCons by simp
  moreover {
    let ?Y = "map_prod ltl ltl ` (Y \<inter> {(xs, ys). \<not> lnull xs \<and> \<not> lnull ys})"
    have "Complete_Partial_Order.chain (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) ?Y"
      by(rule chainI)(auto 4 3 dest: Y chainD[OF chain] intro: lprefix_ltlI)
    moreover
    have "ltl ` (fst ` Y \<inter> {xs. \<not> lnull xs}) = fst ` ?Y"
      and "ltl ` (snd ` Y \<inter> {xs. \<not> lnull xs}) = snd ` ?Y"
      by(fastforce simp add: image_image dest: Y llist_all2_lnullD intro: rev_image_eqI)+
    ultimately have ?ltl by(auto 4 3 intro: llist_all2_ltlI dest: Y) }
  ultimately show ?case ..
qed

lemma admissible_llist_all2 [cont_intro, simp]:
  assumes f: "mcont lub ord lSup (\<sqsubseteq>) (\<lambda>x. f x)"
  and g: "mcont lub ord lSup (\<sqsubseteq>) (\<lambda>x. g x)"
  shows "ccpo.admissible lub ord (\<lambda>x. llist_all2 P (f x) (g x))"
proof(rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ord Y"
    and Y: "\<forall>x\<in>Y. llist_all2 P (f x) (g x)"
    and "Y \<noteq> {}"
  from chain have "Complete_Partial_Order.chain (rel_prod (\<sqsubseteq>) (\<sqsubseteq>)) ((\<lambda>x. (f x, g x)) ` Y)"
    by(rule chain_imageI)(auto intro: mcont_monoD[OF f] mcont_monoD[OF g])
  from llist_all2_lSupI[OF this, of P] chain Y
  show "llist_all2 P (f (lub Y)) (g (lub Y))" using `Y \<noteq> {}`
    by(simp add: mcont_contD[OF f chain] mcont_contD[OF g chain] image_image)
qed

lemmas [cont_intro] =
  ccpo.mcont2mcont[OF llist_ccpo _ mcont_fst]
  ccpo.mcont2mcont[OF llist_ccpo _ mcont_snd]

lemmas ldropWhile_fixp_parallel_induct =
  parallel_fixp_induct_1_1[OF llist_partial_function_definitions llist_partial_function_definitions
    ldropWhile.mono ldropWhile.mono ldropWhile_def ldropWhile_def, case_names adm LNil step]

lemma llist_all2_ldropWhileI:
  assumes *: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llist_all2 P (ldropWhile Q1 xs) (ldropWhile Q2 ys)"
\<comment> \<open>cannot prove this with parallel induction over @{term xs} and @{term ys}
  because @{term "\<lambda>x. \<not> llist_all2 P (f x) (g x)"} is not admissible.\<close>
using * by(induction arbitrary: xs ys rule: ldropWhile_fixp_parallel_induct)(auto split: llist.split dest: Q)

lemma llist_all2_same [simp]: "llist_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>lset xs. P x x)"
by(auto simp add: llist_all2_conv_all_lnth in_lset_conv_lnth Ball_def)

lemma llist_all2_trans:
  "\<lbrakk> llist_all2 P xs ys; llist_all2 P ys zs; transp P \<rbrakk>
  \<Longrightarrow> llist_all2 P xs zs"
apply(rule llist_all2_all_lnthI)
 apply(simp add: llist_all2_llengthD)
apply(frule llist_all2_llengthD)
apply(drule (1) llist_all2_lnthD)
apply(drule llist_all2_lnthD)
 apply simp
apply(erule (2) transpD)
done

subsection {* The last element @{term "llast"} *}

lemma llast_LNil: "llast LNil = undefined"
by(simp add: llast_def zero_enat_def)

lemma llast_LCons: "llast (LCons x xs) = (if lnull xs then x else llast xs)"
by(cases "llength xs")(auto simp add: llast_def eSuc_def zero_enat_def not_lnull_conv split: enat.splits)

lemma llast_linfinite: "\<not> lfinite xs \<Longrightarrow> llast xs = undefined"
by(simp add: llast_def lfinite_conv_llength_enat)

lemma [simp, code]:
  shows llast_singleton: "llast (LCons x LNil) = x"
  and llast_LCons2: "llast (LCons x (LCons y xs)) = llast (LCons y xs)"
by(simp_all add: llast_LCons)

lemma llast_lappend:
  "llast (lappend xs ys) = (if lnull ys then llast xs else if lfinite xs then llast ys else undefined)"
proof(cases "lfinite xs")
  case True
  hence "\<not> lnull ys \<Longrightarrow> llast (lappend xs ys) = llast ys"
    by(induct rule: lfinite.induct)(simp_all add: llast_LCons)
  with True show ?thesis by(simp add: lappend_lnull2)
next
  case False thus ?thesis by(simp add: llast_linfinite)
qed

lemma llast_lappend_LCons [simp]:
  "lfinite xs \<Longrightarrow> llast (lappend xs (LCons y ys)) = llast (LCons y ys)"
by(simp add: llast_lappend)

lemma llast_ldropn: "enat n < llength xs \<Longrightarrow> llast (ldropn n xs) = llast xs"
proof(induct n arbitrary: xs)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by(cases xs)(auto simp add: Suc_ile_eq llast_LCons)
qed

lemma llast_ldrop:
  assumes "n < llength xs"
  shows "llast (ldrop n xs) = llast xs"
proof -
  from assms obtain n' where n: "n = enat n'" by(cases n) auto
  show ?thesis using assms unfolding n
  proof(induct n' arbitrary: xs)
    case 0 thus ?case by(simp add: zero_enat_def[symmetric])
  next
    case Suc thus ?case by(cases xs)(auto simp add: eSuc_enat[symmetric] llast_LCons)
  qed
qed

lemma llast_llist_of [simp]: "llast (llist_of xs) = last xs"
by(induct xs)(auto simp add: last_def zero_enat_def llast_LCons llast_LNil)

lemma llast_conv_lnth: "llength xs = eSuc (enat n) \<Longrightarrow> llast xs = lnth xs n"
by(clarsimp simp add: llast_def zero_enat_def[symmetric] eSuc_enat split: nat.split)

lemma llast_lmap:
  assumes "lfinite xs" "\<not> lnull xs"
  shows "llast (lmap f xs) = f (llast xs)"
using assms
proof induct
  case (lfinite_LConsI xs)
  thus ?case by(cases xs) simp_all
qed simp

subsection {* Distinct lazy lists @{term "ldistinct"} *}

inductive_simps ldistinct_LCons [code, simp]:
  "ldistinct (LCons x xs)"

lemma ldistinct_LNil_code [code]:
  "ldistinct LNil = True"
by simp

lemma ldistinct_llist_of [simp]:
  "ldistinct (llist_of xs) \<longleftrightarrow> distinct xs"
by(induct xs) auto

lemma ldistinct_coinduct [consumes 1, case_names ldistinct, case_conclusion ldistinct lhd ltl, coinduct pred: ldistinct]:
  assumes "X xs"
  and step: "\<And>xs. \<lbrakk> X xs; \<not> lnull xs \<rbrakk>
    \<Longrightarrow> lhd xs \<notin> lset (ltl xs) \<and> (X (ltl xs) \<or> ldistinct (ltl xs))"
  shows "ldistinct xs"
using `X xs`
proof(coinduct)
  case (ldistinct xs)
  thus ?case by(cases xs)(auto dest: step)
qed

lemma ldistinct_lhdD:
  "\<lbrakk> ldistinct xs; \<not> lnull xs \<rbrakk> \<Longrightarrow> lhd xs \<notin> lset (ltl xs)"
by(clarsimp simp add: not_lnull_conv)

lemma ldistinct_ltlI:
  "ldistinct xs \<Longrightarrow> ldistinct (ltl xs)"
by(cases xs) simp_all

lemma ldistinct_lSup:
  "\<lbrakk> Complete_Partial_Order.chain (\<sqsubseteq>) Y; \<forall>xs\<in>Y. ldistinct xs \<rbrakk>
  \<Longrightarrow> ldistinct (lSup Y)"
proof(coinduction arbitrary: Y)
  case (ldistinct Y)
  hence chain: "Complete_Partial_Order.chain (\<sqsubseteq>) Y"
    and distinct: "\<And>xs. xs \<in> Y \<Longrightarrow> ldistinct xs" by blast+
  have ?lhd using chain by(auto 4 4 simp add: lset_lSup chain_lprefix_ltl dest: distinct lhd_lSup_eq ldistinct_lhdD)
  moreover have ?ltl by(auto 4 3 simp add: chain_lprefix_ltl chain intro: ldistinct_ltlI distinct)
  ultimately show ?case ..
qed

lemma admissible_ldistinct [cont_intro, simp]:
  assumes mcont: "mcont lub ord lSup (\<sqsubseteq>) (\<lambda>x. f x)"
  shows "ccpo.admissible lub ord (\<lambda>x. ldistinct (f x))"
proof(rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ord Y"
    and distinct: "\<forall>x\<in>Y. ldistinct (f x)"
    and "Y \<noteq> {}"
  thus "ldistinct (f (lub Y))"
    by(simp add: mcont_contD[OF mcont] ldistinct_lSup chain_imageI mcont_monoD[OF mcont])
qed

lemma ldistinct_lappend:
  "ldistinct (lappend xs ys) \<longleftrightarrow> ldistinct xs \<and> (lfinite xs \<longrightarrow> ldistinct ys \<and> lset xs \<inter> lset ys = {})"
  (is "?lhs = ?rhs")
proof(intro iffI conjI strip)
  assume "?lhs"
  thus "ldistinct xs"
    by(coinduct)(auto simp add: not_lnull_conv in_lset_lappend_iff)

  assume "lfinite xs"
  thus "ldistinct ys" "lset xs \<inter> lset ys = {}"
    using `?lhs` by induct simp_all
next
  assume "?rhs"
  thus ?lhs
    by(coinduction arbitrary: xs)(auto simp add: not_lnull_conv in_lset_lappend_iff)
qed

lemma ldistinct_lprefix:
  "\<lbrakk> ldistinct xs; ys \<sqsubseteq> xs \<rbrakk> \<Longrightarrow> ldistinct ys"
by(clarsimp simp add: lprefix_conv_lappend ldistinct_lappend)

lemma admissible_not_ldistinct[THEN admissible_subst, cont_intro, simp]:
  "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>x. \<not> ldistinct x)"
by(rule ccpo.admissibleI)(auto dest: ldistinct_lprefix intro: chain_lprefix_lSup)

lemma ldistinct_ltake: "ldistinct xs \<Longrightarrow> ldistinct (ltake n xs)"
by (metis ldistinct_lprefix ltake_is_lprefix)

lemma ldistinct_ldropn:
  "ldistinct xs \<Longrightarrow> ldistinct (ldropn n xs)"
by(induct n arbitrary: xs)(simp, case_tac xs, simp_all)

lemma ldistinct_ldrop: "ldistinct xs \<Longrightarrow> ldistinct (ldrop n xs)"
proof(induct xs arbitrary: n)
  case (LCons x xs) thus ?case
    by(cases n rule: co.enat.exhaust) simp_all
qed simp_all

lemma ldistinct_conv_lnth:
  "ldistinct xs \<longleftrightarrow> (\<forall>i j. enat i < llength xs \<longrightarrow> enat j < llength xs \<longrightarrow> i \<noteq> j \<longrightarrow> lnth xs i \<noteq> lnth xs j)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI strip)
  assume "?rhs"
  thus "?lhs"
  proof(coinduct xs)
    case (ldistinct xs)
    from `\<not> lnull xs`
    obtain x xs' where LCons: "xs = LCons x xs'"
      by(auto simp add: not_lnull_conv)
    have "x \<notin> lset xs'"
    proof
      assume "x \<in> lset xs'"
      then obtain j where "enat j < llength xs'" "lnth xs' j = x"
        unfolding lset_conv_lnth by auto
      hence "enat 0 < llength xs" "enat (Suc j) < llength xs" "lnth xs (Suc j) = x" "lnth xs 0 = x"
        by(simp_all add: LCons Suc_ile_eq zero_enat_def[symmetric])
      thus False by(auto dest: ldistinct(1)[rule_format])
    qed
    moreover {
      fix i j
      assume "enat i < llength xs'" "enat j < llength xs'" "i \<noteq> j"
      hence "enat (Suc i) < llength xs" "enat (Suc j) < llength xs"
        by(simp_all add: LCons Suc_ile_eq)
      with `i \<noteq> j` have "lnth xs (Suc i) \<noteq> lnth xs (Suc j)"
        by(auto dest: ldistinct(1)[rule_format])
      hence "lnth xs' i \<noteq> lnth xs' j" unfolding LCons by simp }
    ultimately show ?case using LCons by simp
  qed
next
  assume "?lhs"
  fix i j
  assume "enat i < llength xs" "enat j < llength xs" "i \<noteq> j"
  thus "lnth xs i \<noteq> lnth xs j"
  proof(induct i j rule: wlog_linorder_le)
    case symmetry thus ?case by simp
  next
    case (le i j)
    from `?lhs` have "ldistinct (ldropn i xs)" by(rule ldistinct_ldropn)
    also note ldropn_Suc_conv_ldropn[symmetric]
    also from le have "i < j" by simp
    hence "lnth xs j \<in> lset (ldropn (Suc i) xs)" using le unfolding in_lset_conv_lnth
      by(cases "llength xs")(auto intro!: exI[where x="j - Suc i"])
    ultimately show ?case using `enat i < llength xs` by auto
  qed
qed

lemma ldistinct_lmap [simp]:
  "ldistinct (lmap f xs) \<longleftrightarrow> ldistinct xs \<and> inj_on f (lset xs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(intro iffI conjI)
  assume dist: ?lhs
  thus "ldistinct xs"
    by(coinduct)(auto simp add: not_lnull_conv)

  show "inj_on f (lset xs)"
  proof(rule inj_onI)
    fix x y
    assume "x \<in> lset xs" and "y \<in> lset xs" and "f x = f y"
    then obtain i j
      where "enat i < llength xs" "x = lnth xs i" "enat j < llength xs" "y = lnth xs j"
      unfolding lset_conv_lnth by blast
    with dist `f x = f y` show "x = y"
      unfolding ldistinct_conv_lnth by auto
  qed
next
  assume ?rhs
  thus ?lhs
    by(coinduction arbitrary: xs)(auto simp add: not_lnull_conv)
qed

lemma ldistinct_lzipI1: "ldistinct xs \<Longrightarrow> ldistinct (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto simp add: not_lnull_conv dest: lset_lzipD1)

lemma ldistinct_lzipI2: "ldistinct ys \<Longrightarrow> ldistinct (lzip xs ys)"
by(coinduction arbitrary: xs ys)(auto 4 3 simp add: not_lnull_conv dest: lset_lzipD2)

subsection {* Sortedness @{term lsorted} *}

context ord begin

coinductive lsorted :: "'a llist \<Rightarrow> bool"
where
  LNil [simp]: "lsorted LNil"
| Singleton [simp]: "lsorted (LCons x LNil)"
| LCons_LCons: "\<lbrakk> x \<le> y; lsorted (LCons y xs) \<rbrakk> \<Longrightarrow> lsorted (LCons x (LCons y xs))"

inductive_simps lsorted_LCons_LCons [simp]:
  "lsorted (LCons x (LCons y xs))"

inductive_simps lsorted_code [code]:
  "lsorted LNil"
  "lsorted (LCons x LNil)"
  "lsorted (LCons x (LCons y xs))"

lemma lsorted_coinduct' [consumes 1, case_names lsorted, case_conclusion lsorted lhd ltl, coinduct pred: lsorted]:
  assumes major: "X xs"
  and step: "\<And>xs. \<lbrakk> X xs; \<not> lnull xs; \<not> lnull (ltl xs) \<rbrakk> \<Longrightarrow> lhd xs \<le> lhd (ltl xs) \<and> (X (ltl xs) \<or> lsorted (ltl xs))"
  shows "lsorted xs"
using major by coinduct(subst disj_commute, auto 4 4 simp add: neq_LNil_conv dest: step)

lemma lsorted_ltlI: "lsorted xs \<Longrightarrow> lsorted (ltl xs)"
by(erule lsorted.cases) simp_all

lemma lsorted_lhdD:
  "\<lbrakk> lsorted xs; \<not> lnull xs; \<not> lnull (ltl xs) \<rbrakk> \<Longrightarrow> lhd xs \<le> lhd (ltl xs)"
by(auto elim: lsorted.cases)

lemma lsorted_LCons':
  "lsorted (LCons x xs) \<longleftrightarrow> (\<not> lnull xs \<longrightarrow> x \<le> lhd xs \<and> lsorted xs)"
by(cases xs) auto

lemma lsorted_lSup:
  "\<lbrakk> Complete_Partial_Order.chain (\<sqsubseteq>) Y; \<forall>xs \<in> Y. lsorted xs \<rbrakk>
  \<Longrightarrow> lsorted (lSup Y)"
proof(coinduction arbitrary: Y)
  case (lsorted Y)
  hence sorted: "\<And>xs. xs \<in> Y \<Longrightarrow> lsorted xs" by blast
  note chain = `Complete_Partial_Order.chain (\<sqsubseteq>) Y`
  from `\<not> lnull (lSup Y)` `\<not> lnull (ltl (lSup Y))`
  obtain xs where "xs \<in> Y" "\<not> lnull xs" "\<not> lnull (ltl xs)" by auto
  hence "lhd (lSup Y) = lhd xs" "lhd (ltl (lSup Y)) = lhd (ltl xs)" "lhd xs \<le> lhd (ltl xs)"
    using chain sorted by(auto intro: lhd_lSup_eq chain_lprefix_ltl lsorted_lhdD)
  hence ?lhd by simp
  moreover have ?ltl using chain sorted by(auto intro: chain_lprefix_ltl lsorted_ltlI)
  ultimately show ?case ..
qed

lemma lsorted_lprefixD:
  "\<lbrakk> xs \<sqsubseteq> ys; lsorted ys \<rbrakk> \<Longrightarrow> lsorted xs"
proof(coinduction arbitrary: xs ys)
  case (lsorted xs ys)
  hence "lhd xs = lhd ys" "lhd (ltl xs) = lhd (ltl ys)"
    by(auto dest: lprefix_lhdD lprefix_ltlI)
  moreover have "lhd ys \<le> lhd (ltl ys)" using lsorted
    by(auto intro: lsorted_lhdD dest: lprefix_lnullD lprefix_ltlI)
  ultimately have ?lhd by simp
  moreover have ?ltl using lsorted by(blast intro: lsorted_ltlI lprefix_ltlI)
  ultimately show ?case ..
qed

lemma admissible_lsorted [cont_intro, simp]:
  assumes mcont: "mcont lub ord lSup (\<sqsubseteq>) (\<lambda>x. f x)"
  and ccpo: "class.ccpo lub ord (mk_less ord)"
  shows "ccpo.admissible lub ord (\<lambda>x. lsorted (f x))"
proof(rule ccpo.admissibleI)
  fix Y
  assume chain: "Complete_Partial_Order.chain ord Y"
    and sorted: "\<forall>x\<in>Y. lsorted (f x)"
    and "Y \<noteq> {}"
  thus "lsorted (f (lub Y))"
    by(simp add: mcont_contD[OF mcont] lsorted_lSup chain_imageI mcont_monoD[OF mcont])
qed

lemma admissible_not_lsorted[THEN admissible_subst, cont_intro, simp]:
  "ccpo.admissible lSup (\<sqsubseteq>) (\<lambda>xs. \<not> lsorted xs)"
by(rule ccpo.admissibleI)(auto dest: lsorted_lprefixD[rotated] intro: chain_lprefix_lSup)

lemma lsorted_ltake [simp]: "lsorted xs \<Longrightarrow> lsorted (ltake n xs)"
by(rule lsorted_lprefixD)(rule ltake_is_lprefix)

lemma lsorted_ldropn [simp]: "lsorted xs \<Longrightarrow> lsorted (ldropn n xs)"
by(induct n arbitrary: xs)(fastforce simp add: ldropn_Suc lsorted_LCons' ldropn_lnull split: llist.split)+

lemma lsorted_ldrop [simp]: "lsorted xs \<Longrightarrow> lsorted (ldrop n xs)"
by(induct xs arbitrary: n)(auto simp add: ldrop_LCons lsorted_LCons' ldrop_lnull split: co.enat.split)

end

declare
  ord.lsorted_code [code]
  ord.admissible_lsorted [cont_intro, simp]
  ord.admissible_not_lsorted [THEN admissible_subst, cont_intro, simp]

context preorder begin

lemma lsorted_LCons:
  "lsorted (LCons x xs) \<longleftrightarrow> lsorted xs \<and> (\<forall>y\<in>lset xs. x \<le> y)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix y
    assume "y \<in> lset xs"
    hence "x \<le> y" using `?lhs`
      by(induct arbitrary: x)(auto intro: order_trans) }
  with `?lhs` show ?rhs by cases auto
next
  assume ?rhs
  thus ?lhs by(cases xs) simp_all
qed

lemma lsorted_coinduct [consumes 1, case_names lsorted, case_conclusion lsorted lhd ltl, coinduct pred: lsorted]:
  assumes major: "X xs"
  and step: "\<And>xs. \<lbrakk> X xs; \<not> lnull xs \<rbrakk> \<Longrightarrow> (\<forall>x \<in> lset (ltl xs). lhd xs \<le> x) \<and> (X (ltl xs) \<or> lsorted (ltl xs))"
  shows "lsorted xs"
using major by(coinduct rule: lsorted_coinduct')(auto dest: step)

lemma lsortedD: "\<lbrakk> lsorted xs; \<not> lnull xs; y \<in> lset (ltl xs) \<rbrakk> \<Longrightarrow> lhd xs \<le> y"
by(clarsimp simp add: not_lnull_conv lsorted_LCons)

end

lemma lsorted_lmap':
  assumes "ord.lsorted orda xs" "monotone orda ordb f"
  shows "ord.lsorted ordb (lmap f xs)"
using `ord.lsorted orda xs`
by(coinduction arbitrary: xs rule: ord.lsorted_coinduct')(auto intro: monotoneD[OF `monotone orda ordb f`] ord.lsorted_lhdD ord.lsorted_ltlI)

lemma lsorted_lmap:
  assumes "lsorted xs" "monotone (\<le>) (\<le>) f"
  shows "lsorted (lmap f xs)"
using `lsorted xs`
by(coinduction arbitrary: xs rule: lsorted_coinduct')(auto intro: monotoneD[OF `monotone (\<le>) (\<le>) f`] lsorted_lhdD lsorted_ltlI)

context linorder begin

lemma lsorted_ldistinct_lset_unique:
  "\<lbrakk> lsorted xs; ldistinct xs; lsorted ys; ldistinct ys; lset xs = lset ys \<rbrakk>
  \<Longrightarrow> xs = ys"
proof(coinduction arbitrary: xs ys)
  case (Eq_llist xs ys)
  hence ?lnull by(cases ys)(auto simp add: lset_lnull)
  moreover from Eq_llist have ?LCons
    by(auto 4 3 intro: lsorted_ltlI ldistinct_ltlI simp add: not_lnull_conv insert_eq_iff lsorted_LCons split: if_split_asm)
  ultimately show ?case ..
qed

end

lemma lsorted_llist_of[simp]: "lsorted (llist_of xs) \<longleftrightarrow> sorted xs"
by(induct xs)(auto simp: lsorted_LCons)

subsection {* Lexicographic order on lazy lists: @{term "llexord"} *}

lemma llexord_coinduct [consumes 1, case_names llexord, coinduct pred: llexord]:
  assumes X: "X xs ys"
  and step: "\<And>xs ys. \<lbrakk> X xs ys; \<not> lnull xs \<rbrakk>
    \<Longrightarrow> \<not> lnull ys \<and>
       (\<not> lnull ys \<longrightarrow> r (lhd xs) (lhd ys) \<or>
                     lhd xs = lhd ys \<and> (X (ltl xs) (ltl ys) \<or> llexord r (ltl xs) (ltl ys)))"
  shows "llexord r xs ys"
using X
proof(coinduct)
  case (llexord xs ys)
  thus ?case
    by(cases xs ys rule: llist.exhaust[case_product llist.exhaust])(auto dest: step)
qed

lemma llexord_refl [simp, intro!]:
  "llexord r xs xs"
proof -
  define ys where "ys = xs"
  hence "xs = ys" by simp
  thus "llexord r xs ys"
    by(coinduct xs ys) auto
qed

lemma llexord_LCons_LCons [simp]:
  "llexord r (LCons x xs) (LCons y ys) \<longleftrightarrow> (x = y \<and> llexord r xs ys \<or> r x y)"
by(auto intro: llexord.intros(1,2) elim: llexord.cases)

lemma lnull_llexord [simp]: "lnull xs \<Longrightarrow> llexord r xs ys"
unfolding lnull_def by simp

lemma llexord_LNil_right [simp]:
  "lnull ys \<Longrightarrow> llexord r xs ys \<longleftrightarrow> lnull xs"
by(auto elim: llexord.cases)

lemma llexord_LCons_left:
  "llexord r (LCons x xs) ys \<longleftrightarrow>
   (\<exists>y ys'. ys = LCons y ys' \<and> (x = y \<and> llexord r xs ys' \<or> r x y))"
by(cases ys)(auto elim: llexord.cases)

lemma lprefix_imp_llexord:
  assumes "xs \<sqsubseteq> ys"
  shows "llexord r xs ys"
using assms
by(coinduct)(auto simp add: not_lnull_conv LCons_lprefix_conv)

lemma llexord_empty:
  "llexord (\<lambda>x y. False) xs ys = xs \<sqsubseteq> ys"
proof
  assume "llexord (\<lambda>x y. False) xs ys"
  thus "xs \<sqsubseteq> ys"
    by(coinduct)(auto elim: llexord.cases)
qed(rule lprefix_imp_llexord)

lemma llexord_append_right:
  "llexord r xs (lappend xs ys)"
by(rule lprefix_imp_llexord)(auto simp add: lprefix_conv_lappend)

lemma llexord_lappend_leftI:
  assumes "llexord r ys zs"
  shows "llexord r (lappend xs ys) (lappend xs zs)"
proof(cases "lfinite xs")
  case True thus ?thesis by induct (simp_all add: assms)
next
  case False thus ?thesis by(simp add: lappend_inf)
qed

lemma llexord_lappend_leftD:
  assumes lex: "llexord r (lappend xs ys) (lappend xs zs)"
  and fin: "lfinite xs"
  and irrefl: "!!x. x \<in> lset xs \<Longrightarrow> \<not> r x x"
  shows "llexord r ys zs"
using fin lex irrefl by(induct) simp_all

lemma llexord_lappend_left:
  "\<lbrakk> lfinite xs; !!x. x \<in> lset xs \<Longrightarrow> \<not> r x x \<rbrakk>
  \<Longrightarrow> llexord r (lappend xs ys) (lappend xs zs) \<longleftrightarrow> llexord r ys zs"
by(blast intro: llexord_lappend_leftI llexord_lappend_leftD)

lemma antisym_llexord:
  assumes r: "antisymp r"
  and irrefl: "\<And>x. \<not> r x x"
  shows "antisymp (llexord r)"
proof(rule antisympI)
  fix xs ys
  assume "llexord r xs ys"
    and "llexord r ys xs"
  hence "llexord r xs ys \<and> llexord r ys xs" by auto
  thus "xs = ys"
    by (coinduct rule: llist.coinduct)
      (auto 4 3 simp add: not_lnull_conv irrefl dest: antisympD[OF r, simplified])
qed

lemma llexord_antisym:
  "\<lbrakk> llexord r xs ys; llexord r ys xs;
    !!a b. \<lbrakk> r a b; r b a \<rbrakk> \<Longrightarrow> False \<rbrakk>
  \<Longrightarrow> xs = ys"
using antisympD[OF antisym_llexord, of r xs ys]
by(auto intro: antisympI)

lemma llexord_trans:
  assumes 1: "llexord r xs ys"
  and 2: "llexord r ys zs"
  and trans: "!!a b c. \<lbrakk> r a b; r b c \<rbrakk> \<Longrightarrow> r a c"
  shows "llexord r xs zs"
proof -
  from 1 2 have "\<exists>ys. llexord r xs ys \<and> llexord r ys zs" by blast
  thus ?thesis
    by(coinduct)(auto 4 3 simp add: not_lnull_conv llexord_LCons_left dest: trans)
qed

lemma trans_llexord:
  "transp r \<Longrightarrow> transp (llexord r)"
  by(auto intro!: transpI elim: llexord_trans dest: transpD)

lemma llexord_linear:
  assumes linear: "!!x y. r x y \<or> x = y \<or> r y x"
  shows "llexord r xs ys \<or> llexord r ys xs"
proof(rule disjCI)
  assume "\<not> llexord r ys xs"
  thus "llexord r xs ys"
  proof(coinduct rule: llexord_coinduct)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis using llexord by simp
    next
      case (LCons x xs')
      with `\<not> llexord r ys xs` obtain y ys'
        where ys: "ys = LCons y ys'" "\<not> r y x" "y \<noteq> x \<or> \<not> llexord r ys' xs'"
        by(cases ys) auto
      with `\<not> r y x` linear[of x y] ys LCons show ?thesis by auto
    qed
  qed
qed

lemma llexord_code [code]:
  "llexord r LNil ys = True"
  "llexord r (LCons x xs) LNil = False"
  "llexord r (LCons x xs) (LCons y ys) = (r x y \<or> x = y \<and> llexord r xs ys)"
by auto

lemma llexord_conv:
 "llexord r xs ys \<longleftrightarrow>
  xs = ys \<or>
  (\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and> ys = lappend zs (LCons y ys') \<and>
                  (xs' = LNil \<or> r (lhd xs') y))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  show ?rhs (is "_ \<or> ?prefix")
  proof(rule disjCI)
    assume "\<not> ?prefix"
    with `?lhs` show "xs = ys"
    proof(coinduction arbitrary: xs ys)
      case (Eq_llist xs ys)
      hence "llexord r xs ys"
        and prefix: "\<And>zs xs' y ys'. \<lbrakk> lfinite zs; xs = lappend zs xs';
                                      ys = lappend zs (LCons y ys') \<rbrakk>
                                     \<Longrightarrow> xs' \<noteq> LNil \<and> \<not> r (lhd xs') y"
        by auto
      from `llexord r xs ys` show ?case
      proof(cases)
        case (llexord_LCons_eq xs' ys' x)
        { fix zs xs'' y ys''
          assume "lfinite zs" "xs' = lappend zs xs''"
            and "ys' = lappend zs (LCons y ys'')"
          hence "lfinite (LCons x zs)" "xs = lappend (LCons x zs) xs''"
            and "ys = lappend (LCons x zs) (LCons y ys'')"
            using llexord_LCons_eq by simp_all
          hence "xs'' \<noteq> LNil \<and> \<not> r (lhd xs'') y" by(rule prefix) }
        with llexord_LCons_eq show ?thesis by auto
      next
        case (llexord_LCons_less x y xs' ys')
        with prefix[of LNil xs y ys'] show ?thesis by simp
      next
        case llexord_LNil
        thus ?thesis using prefix[of LNil xs "lhd ys" "ltl ys"]
          by(cases ys) simp_all
      qed
    qed
  qed
next
  assume ?rhs
  thus ?lhs
  proof(coinduct xs ys)
    case (llexord xs ys)
    show ?case
    proof(cases xs)
      case LNil thus ?thesis using llexord by simp
    next
      case (LCons x xs')
      with llexord obtain y ys' where "ys = LCons y ys'"
        by(cases ys)(auto dest: sym simp add: LNil_eq_lappend_iff)
      show ?thesis
      proof(cases "x = y")
        case True
        from llexord(1) show ?thesis
        proof
          assume "xs = ys"
          with True LCons `ys = LCons y ys'` show ?thesis by simp
        next
          assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                                 ys = lappend zs (LCons y ys') \<and>
                                 (xs' = LNil \<or> r (lhd xs') y)"
          then obtain zs xs' y' ys''
            where "lfinite zs" "xs = lappend zs xs'"
            and "ys = lappend zs (LCons y' ys'')"
            and "xs' = LNil \<or> r (lhd xs') y'" by blast
          with True LCons `ys = LCons y ys'`
          show ?thesis by(cases zs) auto
        qed
      next
        case False
        with LCons llexord `ys = LCons y ys'`
        have "r x y" by(fastforce elim: lfinite.cases)
        with LCons `ys = LCons y ys'` show ?thesis by auto
      qed
    qed
  qed
qed

lemma llexord_conv_ltake_index:
  "llexord r xs ys \<longleftrightarrow>
   (llength xs \<le> llength ys \<and> ltake (llength xs) ys = xs) \<or>
   (\<exists>n. enat n < min (llength xs) (llength ys) \<and>
        ltake (enat n) xs = ltake (enat n) ys \<and> r (lnth xs n) (lnth ys n))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  thus ?rhs (is "?A \<or> ?B") unfolding llexord_conv
  proof
    assume "xs = ys" thus ?thesis by(simp add: ltake_all)
  next
    assume "\<exists>zs xs' y ys'. lfinite zs \<and> xs = lappend zs xs' \<and>
                           ys = lappend zs (LCons y ys') \<and>
                           (xs' = LNil \<or> r (lhd xs') y)"
    then obtain zs xs' y ys'
      where "lfinite zs" "xs' = LNil \<or> r (lhd xs') y"
      and [simp]: "xs = lappend zs xs'" "ys = lappend zs (LCons y ys')"
      by blast
    show ?thesis
    proof(cases xs')
      case LNil
      hence ?A by(auto intro: enat_le_plus_same simp add: ltake_lappend1 ltake_all)
      thus ?thesis ..
    next
      case LCons
      with `xs' = LNil \<or> r (lhd xs') y` have "r (lhd xs') y" by simp
      from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
        unfolding lfinite_eq_range_llist_of by blast
      with LCons have "enat (length zs') < min (llength xs) (llength ys)"
        by(auto simp add: less_enat_def eSuc_def split: enat.split)
      moreover have "ltake (enat (length zs')) xs = ltake (enat (length zs')) ys"
        by(simp add: ltake_lappend1)
      moreover have "r (lnth xs (length zs')) (lnth ys (length zs'))"
        using LCons `r (lhd xs') y`
        by(simp add: lappend_llist_of_LCons lnth_lappend1)
      ultimately have ?B by blast
      thus ?thesis ..
    qed
  qed
next
  assume ?rhs (is "?A \<or> ?B")
  thus ?lhs
  proof
    assume ?A thus ?thesis
    proof(coinduct)
      case (llexord xs ys)
      thus ?case by(cases xs, simp)(cases ys, auto)
    qed
  next
    assume "?B"
    then obtain n where len: "enat n < min (llength xs) (llength ys)"
      and takexs: "ltake (enat n) xs = ltake (enat n) ys"
      and r: "r (lnth xs n) (lnth ys n)" by blast
    have "xs = lappend (ltake (enat n) xs) (ldrop (enat n) xs)"
      by(simp only: lappend_ltake_ldrop)
    moreover from takexs len
    have "ys = lappend (ltake (enat n) xs) (LCons (lnth ys n) (ldrop (enat (Suc n)) ys))"
      by(simp add: ldropn_Suc_conv_ldropn ldrop_enat)
    moreover from r len
    have "r (lhd (ldrop (enat n) xs)) (lnth ys n)"
      by(simp add: lhd_ldrop)
    moreover have "lfinite (ltake (enat n) xs)" by simp
    ultimately show ?thesis unfolding llexord_conv by blast
  qed
qed

lemma llexord_llist_of:
  "llexord r (llist_of xs) (llist_of ys) \<longleftrightarrow>
   xs = ys \<or> (xs, ys) \<in> lexord {(x, y). r x y}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  { fix zs xs' y ys'
    assume "lfinite zs" "llist_of xs = lappend zs xs'"
      and "llist_of ys = lappend zs (LCons y ys')"
      and "xs' = LNil \<or> r (lhd xs') y"
    from `lfinite zs` obtain zs' where [simp]: "zs = llist_of zs'"
      unfolding lfinite_eq_range_llist_of by blast
    have "lfinite (llist_of xs)" by simp
    hence "lfinite xs'" unfolding `llist_of xs = lappend zs xs'` by simp
    then obtain XS' where [simp]: "xs' = llist_of XS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of xs = lappend zs xs'` have [simp]: "xs = zs' @ XS'"
      by(simp add: lappend_llist_of_llist_of)
    have "lfinite (llist_of ys)" by simp
    hence "lfinite ys'" unfolding `llist_of ys = lappend zs (LCons y ys')` by simp
    then obtain YS' where [simp]: "ys' = llist_of YS'"
      unfolding lfinite_eq_range_llist_of by blast
    from `llist_of ys = lappend zs (LCons y ys')` have [simp]: "ys = zs' @ y # YS'"
      by(auto simp add: llist_of.simps(2)[symmetric] lappend_llist_of_llist_of simp del: llist_of.simps(2))
    have "(\<exists>a ys'. ys = xs @ a # ys') \<or>
          (\<exists>zs a b. r a b \<and> (\<exists>xs'. xs = zs @ a # xs') \<and> (\<exists>ys'. ys = zs @ b # ys'))"
      (is "?A \<or> ?B")
    proof(cases xs')
      case LNil thus ?thesis by(auto simp add: llist_of_eq_LNil_conv)
    next
      case (LCons x xs'')
      with `xs' = LNil \<or> r (lhd xs') y`
      have "r (lhd xs') y" by(auto simp add: llist_of_eq_LCons_conv)
      with LCons have ?B by(auto simp add: llist_of_eq_LCons_conv) fastforce
      thus ?thesis ..
    qed
    hence "(xs, ys) \<in> {(x, y). \<exists>a v. y = x @ a # v \<or>
                                    (\<exists>u a b v w. (a, b) \<in> {(x, y). r x y} \<and>
                                                 x = u @ a # v \<and> y = u @ b # w)}"
      by auto }
  with `?lhs` show ?rhs
    unfolding lexord_def llexord_conv llist_of_inject by blast
next
  assume "?rhs"
  thus ?lhs
  proof
    assume "xs = ys" thus ?thesis by simp
  next
    assume "(xs, ys) \<in> lexord {(x, y). r x y}"
    thus ?thesis
      by(coinduction arbitrary: xs ys)(auto, auto simp add: neq_Nil_conv)
  qed
qed

subsection {* The filter functional on lazy lists: @{term "lfilter"} *}

lemma lfilter_code [simp, code]:
  shows lfilter_LNil: "lfilter P LNil = LNil"
  and lfilter_LCons: "lfilter P (LCons x xs) = (if P x then LCons x (lfilter P xs) else lfilter P xs)"
by(simp_all add: lfilter.simps)

declare lfilter.mono[cont_intro]

lemma mono2mono_lfilter[THEN llist.mono2mono, simp, cont_intro]:
  shows monotone_lfilter: "monotone (\<sqsubseteq>) (\<sqsubseteq>) (lfilter P)"
by(rule llist.fixp_preserves_mono1[OF lfilter.mono lfilter_def]) simp

lemma mcont2mcont_lfilter[THEN llist.mcont2mcont, simp, cont_intro]:
  shows mcont_lfilter: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) (lfilter P)"
by(rule llist.fixp_preserves_mcont1[OF lfilter.mono lfilter_def]) simp

lemma lfilter_mono [partial_function_mono]:
  "mono_llist A \<Longrightarrow> mono_llist (\<lambda>f. lfilter P (A f))"
by(rule mono2mono_lfilter)

lemma lfilter_LCons_seek: "~ (p x) ==> lfilter p (LCons x l) = lfilter p l"
by simp

lemma lfilter_LCons_found:
  "P x \<Longrightarrow> lfilter P (LCons x xs) = LCons x (lfilter P xs)"
by simp

lemma lfilter_eq_LNil: "lfilter P xs = LNil \<longleftrightarrow> (\<forall>x \<in> lset xs. \<not> P x)"
by(induction xs) simp_all

notepad begin
fix P xs
have "(lfilter P xs = LNil) \<longleftrightarrow> (\<forall>x \<in> lset xs. \<not> P x)"
proof(intro iffI strip)
  assume "\<forall>x \<in> lset xs. \<not> P x"
  hence "lfilter P xs \<sqsubseteq> LNil"
    by(induction arbitrary: xs rule: lfilter.fixp_induct)(simp_all split: llist.split del: lprefix_LNil)
  thus "lfilter P xs = LNil" by simp
next
  fix x
  assume "x \<in> lset xs" "lfilter P xs = LNil"
  thus "\<not> P x" by induction(simp_all split: if_split_asm)
qed
end

lemma diverge_lfilter_LNil [simp]: "\<forall>x\<in>lset xs. \<not> P x \<Longrightarrow> lfilter P xs = LNil"
by(simp add: lfilter_eq_LNil)

lemmas lfilter_False = diverge_lfilter_LNil

lemma lnull_lfilter [simp]: "lnull (lfilter P xs) \<longleftrightarrow> (\<forall>x\<in>lset xs. \<not> P x)"
unfolding lnull_def by(simp add: lfilter_eq_LNil)

lemmas lfilter_empty_conv = lfilter_eq_LNil

lemma lhd_lfilter [simp]: "lhd (lfilter P xs) = lhd (ldropWhile (Not \<circ> P) xs)"
proof(cases "\<exists>x\<in>lset xs. P x")
  case True
  then obtain x where "x \<in> lset xs" and "P x" by blast
  from `x \<in> lset xs` show ?thesis by induct(simp_all add: `P x`)
qed(simp add: o_def)

lemma ltl_lfilter: "ltl (lfilter P xs) = lfilter P (ltl (ldropWhile (Not \<circ> P) xs))"
by(induct xs) simp_all

lemma lfilter_eq_LCons:
  "lfilter P xs = LCons x xs' \<Longrightarrow>
   \<exists>xs''. xs' = lfilter P xs'' \<and> ldropWhile (Not \<circ> P) xs = LCons x xs''"
by(drule eq_LConsD)(auto intro!: exI simp add: ltl_lfilter o_def ldropWhile_eq_LNil_iff intro: llist.expand)

lemma lfilter_K_True [simp]: "lfilter (%_. True) xs = xs"
by(induct xs) simp_all

lemma lfitler_K_False [simp]: "lfilter (\<lambda>_. False) xs = LNil"
by simp

lemma lfilter_lappend_lfinite [simp]:
  "lfinite xs \<Longrightarrow> lfilter P (lappend xs ys) = lappend (lfilter P xs) (lfilter P ys)"
by(induct rule: lfinite.induct) auto

lemma lfinite_lfilterI [simp]: "lfinite xs \<Longrightarrow> lfinite (lfilter P xs)"
by(induct rule: lfinite.induct) simp_all

lemma lset_lfilter [simp]: "lset (lfilter P xs) = {x \<in> lset xs. P x}"
by induct(auto simp add: Collect_conj_eq)

notepad begin \<comment> \<open>show @{thm [source] lset_lfilter} by fixpoint induction\<close>
  note [simp del] = lset_lfilter
  fix P xs
  have "lset (lfilter P xs) = lset xs \<inter> {x. P x}" (is "?lhs = ?rhs")
  proof
    show "?lhs \<subseteq> ?rhs"
      by(induct arbitrary: xs rule: lfilter.fixp_induct)(auto split: llist.split)
    show "?rhs \<subseteq> ?lhs"
    proof
      fix x
      assume "x \<in> ?rhs"
      hence "x \<in> lset xs" "P x" by simp_all
      thus "x \<in> ?lhs" by induction simp_all
    qed
  qed
end

lemma lfilter_lfilter: "lfilter P (lfilter Q xs) = lfilter (\<lambda>x. P x \<and> Q x) xs"
by(induction xs) simp_all

notepad begin \<comment> \<open>show @{thm [source] lfilter_lfilter} by fixpoint induction\<close>
  fix P Q xs
  have "\<forall>xs. lfilter P (lfilter Q xs) \<sqsubseteq> lfilter (\<lambda>x. P x \<and> Q x) xs"
    by(rule lfilter.fixp_induct)(auto split: llist.split)
  moreover have "\<forall>xs. lfilter (\<lambda>x. P x \<and> Q x) xs \<sqsubseteq> lfilter P (lfilter Q xs)"
    by(rule lfilter.fixp_induct)(auto split: llist.split)
  ultimately have "lfilter P (lfilter Q xs) = lfilter (\<lambda>x. P x \<and> Q x) xs"
    by(blast intro: lprefix_antisym)
end

lemma lfilter_idem [simp]: "lfilter P (lfilter P xs) = lfilter P xs"
by(simp add: lfilter_lfilter)

lemma lfilter_lmap: "lfilter P (lmap f xs) = lmap f (lfilter (P o f) xs)"
by(induct xs) simp_all

lemma lfilter_llist_of [simp]:
  "lfilter P (llist_of xs) = llist_of (filter P xs)"
by(induct xs) simp_all

lemma lfilter_cong [cong]:
  assumes xsys: "xs = ys"
  and set: "\<And>x. x \<in> lset ys \<Longrightarrow> P x = Q x"
  shows "lfilter P xs = lfilter Q ys"
using set unfolding xsys
by(induction ys)(simp_all add: Bex_def[symmetric])

lemma llength_lfilter_ile:
  "llength (lfilter P xs) \<le> llength xs"
by(induct xs)(auto intro: order_trans)

lemma lfinite_lfilter:
  "lfinite (lfilter P xs) \<longleftrightarrow>
   lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}"
proof
  assume "lfinite (lfilter P xs)"
  { assume "\<not> lfinite xs"
    with `lfinite (lfilter P xs)`
    have "finite {n. enat n < llength xs \<and> P (lnth xs n)}"
    proof(induct ys\<equiv>"lfilter P xs" arbitrary: xs rule: lfinite_induct)
      case LNil
      hence "\<forall>x\<in>lset xs. \<not> P x" by(auto)
      hence eq: "{n. enat n < llength xs \<and> P (lnth xs n)} = {}"
        by(auto simp add: lset_conv_lnth)
      show ?case unfolding eq ..
    next
      case (LCons xs)
      from `\<not> lnull (lfilter P xs)`
      have exP: "\<exists>x\<in>lset xs. P x" by simp
      let ?xs = "ltl (ldropWhile (\<lambda>x. \<not> P x) xs)"
      let ?xs' = "ltakeWhile (\<lambda>x. \<not> P x) xs"
      from exP obtain n where n: "llength ?xs' = enat n"
        using lfinite_conv_llength_enat[of ?xs']
        by(auto simp add: lfinite_ltakeWhile)
      have "finite ({n. enat n < llength ?xs} \<inter> {n. P (lnth ?xs n)})" (is "finite ?A")
        using LCons [[simproc add: finite_Collect]] by(auto simp add: ltl_lfilter lfinite_ldropWhile)
      hence "finite ((\<lambda>m. n + 1 + m) ` ({n. enat n < llength ?xs} \<inter> {n. P (lnth ?xs n)}))"
        (is "finite (?f ` _)")
        by(rule finite_imageI)
      moreover have xs: "xs = lappend ?xs' (LCons (lhd (ldropWhile (\<lambda>x. \<not> P x) xs)) ?xs)"
        using exP by simp
      { fix m
        assume "m < n"
        hence "lnth ?xs' m \<in> lset ?xs'" using n
          unfolding in_lset_conv_lnth by auto
        hence "\<not> P (lnth ?xs' m)" by(auto dest: lset_ltakeWhileD) }
      hence "{n. enat n < llength xs \<and> P (lnth xs n)} \<subseteq> insert (the_enat (llength ?xs')) (?f ` ?A)"
        using n by(subst (1 2) xs)(cases "llength ?xs", auto simp add: lnth_lappend not_less not_le lnth_LCons' eSuc_enat split: if_split_asm intro!: rev_image_eqI)
      ultimately show ?case by(auto intro: finite_subset)
    qed }
  thus "lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}" by blast
next
  assume "lfinite xs \<or> finite {n. enat n < llength xs \<and> P (lnth xs n)}"
  moreover {
    assume "lfinite xs"
    with llength_lfilter_ile[of P xs] have "lfinite (lfilter P xs)"
      by(auto simp add: lfinite_eq_range_llist_of)
  } moreover {
    assume nfin: "\<not> lfinite xs"
    hence len: "llength xs = \<infinity>" by(rule not_lfinite_llength)
    assume fin: "finite {n. enat n < llength xs \<and> P (lnth xs n)}"
    then obtain m where "{n. enat n < llength xs \<and> P (lnth xs n)} \<subseteq> {..<m}"
      unfolding finite_nat_iff_bounded by auto
    hence "\<And>n. \<lbrakk> m \<le> n; enat n < llength xs \<rbrakk> \<Longrightarrow> \<not> P (lnth xs n)" by auto
    hence "lfinite (lfilter P xs)"
    proof(induct m arbitrary: xs)
      case 0
      hence "lnull (lfilter P xs)" by(auto simp add: in_lset_conv_lnth)
      thus ?case by simp
    next
      case (Suc m)
      { fix n
        assume "m \<le> n" "enat n < llength (ltl xs)"
        hence "Suc m \<le> Suc n" "enat (Suc n) < llength xs"
          by(case_tac [!] xs)(auto simp add: Suc_ile_eq)
        hence "\<not> P (lnth xs (Suc n))" by(rule Suc)
        hence "\<not> P (lnth (ltl xs) n)"
          using `enat n < llength (ltl xs)` by(cases xs) (simp_all) }
      hence "lfinite (lfilter P (ltl xs))" by(rule Suc)
      thus ?case by(cases xs) simp_all
    qed }
  ultimately show "lfinite (lfilter P xs)" by blast
qed

lemma lfilter_eq_LConsD:
  assumes "lfilter P ys = LCons x xs"
  shows "\<exists>us vs. ys = lappend us (LCons x vs) \<and> lfinite us \<and>
                      (\<forall>u\<in>lset us. \<not> P u) \<and> P x \<and> xs = lfilter P vs"
proof -
  let ?us = "ltakeWhile (Not \<circ> P) ys"
    and ?vs = "ltl (ldropWhile (Not \<circ> P) ys)"
  from assms have "\<not> lnull (lfilter P ys)" by auto
  hence exP: "\<exists>x\<in>lset ys. P x" by simp
  from eq_LConsD[OF assms]
  have x: "x = lhd (ldropWhile (Not \<circ> P) ys)"
    and xs: "xs = ltl (lfilter P ys)" by auto
  from exP
  have "ys = lappend ?us (LCons x ?vs)" unfolding x by simp
  moreover have "lfinite ?us" using exP by(simp add: lfinite_ltakeWhile)
  moreover have "\<forall>u\<in>lset ?us. \<not> P u" by(auto dest: lset_ltakeWhileD)
  moreover have "P x" unfolding x o_def
    using exP by(rule lhd_ldropWhile[where P="Not \<circ> P", simplified])
  moreover have "xs = lfilter P ?vs" unfolding xs by(simp add: ltl_lfilter)
  ultimately show ?thesis by blast
qed

lemma lfilter_eq_lappend_lfiniteD:
  assumes "lfilter P xs = lappend ys zs" and "lfinite ys"
  shows "\<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                      ys = lfilter P us \<and> zs = lfilter P vs"
using `lfinite ys` `lfilter P xs = lappend ys zs`
proof(induct arbitrary: xs zs)
  case lfinite_LNil
  hence "xs = lappend LNil xs" "LNil = lfilter P LNil" "zs = lfilter P xs"
    by simp_all
  thus ?case by blast
next
  case (lfinite_LConsI ys y)
  note IH = `\<And>xs zs. lfilter P xs = lappend ys zs \<Longrightarrow>
            \<exists>us vs. xs = lappend us vs \<and> lfinite us \<and>
                    ys = lfilter P us \<and> zs = lfilter P vs`
  from `lfilter P xs = lappend (LCons y ys) zs`
  have "lfilter P xs = LCons y (lappend ys zs)" by simp
  from lfilter_eq_LConsD[OF this] obtain us vs
    where xs: "xs = lappend us (LCons y vs)" "lfinite us"
              "P y" "\<forall>u\<in>lset us. \<not> P u"
    and vs: "lfilter P vs = lappend ys zs" by auto
  from IH[OF vs] obtain us' vs' where "vs = lappend us' vs'" "lfinite us'"
    and "ys = lfilter P us'" "zs = lfilter P vs'" by blast
  with xs show ?case
    by(fastforce simp add: lappend_snocL1_conv_LCons2[symmetric, where ys="lappend us' vs'"]
                           lappend_assoc[symmetric])
qed

lemma ldistinct_lfilterI: "ldistinct xs \<Longrightarrow> ldistinct (lfilter P xs)"
by(induction xs) simp_all

notepad begin
  fix P xs
  assume *: "ldistinct xs"
  from * have "ldistinct (lfilter P xs) \<and> lset (lfilter P xs) \<subseteq> lset xs"
    by(induction arbitrary: xs rule: lfilter.fixp_induct)(simp_all split: llist.split, fastforce)
  from * have "ldistinct (lfilter P xs)"
    \<comment> \<open>only works because we use strong fixpoint induction\<close>
    by(induction arbitrary: xs rule: lfilter.fixp_induct)(simp_all split: llist.split, auto 4 4 dest: monotone_lset[THEN monotoneD] simp add: fun_ord_def)
end

lemma ldistinct_lfilterD:
  "\<lbrakk> ldistinct (lfilter P xs); enat n < llength xs; enat m < llength xs; P a; lnth xs n = a; lnth xs m = a \<rbrakk> \<Longrightarrow> m = n"
proof(induct n m rule: wlog_linorder_le)
  case symmetry thus ?case by simp
next
  case (le n m)
  thus ?case
  proof(induct n arbitrary: xs m)
    case 0 thus ?case
    proof(cases m)
      case 0 thus ?thesis .
    next
      case (Suc m')
      with 0 show ?thesis
        by(cases xs)(simp_all add: Suc_ile_eq, auto simp add: lset_conv_lnth)
    qed
  next
    case (Suc n)
    from `Suc n \<le> m` obtain m' where m [simp]: "m = Suc m'" by(cases m) simp
    with `Suc n \<le> m` have "n \<le> m'" by simp
    moreover from `enat (Suc n) < llength xs`
    obtain x xs' where xs [simp]: "xs = LCons x xs'" by(cases xs) simp
    from `ldistinct (lfilter P xs)` have "ldistinct (lfilter P xs')" by(simp split: if_split_asm)
    moreover from `enat (Suc n) < llength xs` `enat m < llength xs`
    have "enat n < llength xs'" "enat m' < llength xs'" by(simp_all add: Suc_ile_eq)
    moreover note `P a`
    moreover have "lnth xs' n = a" "lnth xs' m' = a"
      using `lnth xs (Suc n) = a` `lnth xs m = a` by simp_all
    ultimately have "m' = n" by(rule Suc)
    thus ?case by simp
  qed
qed

lemmas lfilter_fixp_parallel_induct =
  parallel_fixp_induct_1_1[OF llist_partial_function_definitions llist_partial_function_definitions
    lfilter.mono lfilter.mono lfilter_def lfilter_def, case_names adm LNil step]

lemma llist_all2_lfilterI:
  assumes *: "llist_all2 P xs ys"
  and Q: "\<And>x y. P x y \<Longrightarrow> Q1 x \<longleftrightarrow> Q2 y"
  shows "llist_all2 P (lfilter Q1 xs) (lfilter Q2 ys)"
using * by(induction arbitrary: xs ys rule: lfilter_fixp_parallel_induct)(auto split: llist.split dest: Q)

lemma distinct_filterD:
  "\<lbrakk> distinct (filter P xs); n < length xs; m < length xs; P x; xs ! n = x; xs ! m = x \<rbrakk> \<Longrightarrow> m = n"
using ldistinct_lfilterD[of P "llist_of xs" n m x] by simp

lemma lprefix_lfilterI:
  "xs \<sqsubseteq> ys \<Longrightarrow> lfilter P xs \<sqsubseteq> lfilter P ys"
by(rule monotoneD[OF monotone_lfilter])

context preorder begin

lemma lsorted_lfilterI:
  "lsorted xs \<Longrightarrow> lsorted (lfilter P xs)"
by(induct xs)(simp_all add: lsorted_LCons)

lemma lsorted_lfilter_same:
  "lsorted (lfilter (\<lambda>x. x = c) xs)"
by(induct xs)(auto simp add: lsorted_LCons)

end

lemma lfilter_id_conv: "lfilter P xs = xs \<longleftrightarrow> (\<forall>x\<in>lset xs. P x)" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs thus ?lhs by(induct xs) auto
next
  assume ?lhs
  with lset_lfilter[of P xs] show ?rhs by auto
qed

lemma lfilter_repeat [simp]: "lfilter P (repeat x) = (if P x then repeat x else LNil)"
by(simp add: lfilter_id_conv)

subsection {* Concatenating all lazy lists in a lazy list: @{term "lconcat"} *}

lemma lconcat_simps [simp, code]:
  shows lconcat_LNil: "lconcat LNil = LNil"
  and lconcat_LCons: "lconcat (LCons xs xss) = lappend xs (lconcat xss)"
by(simp_all add: lconcat.simps)

declare lconcat.mono[cont_intro]

lemma mono2mono_lconcat[THEN llist.mono2mono, cont_intro, simp]:
  shows monotone_lconcat: "monotone (\<sqsubseteq>) (\<sqsubseteq>) lconcat"
by(rule llist.fixp_preserves_mono1[OF lconcat.mono lconcat_def]) simp

lemma mcont2mcont_lconcat[THEN llist.mcont2mcont, cont_intro, simp]:
  shows mcont_lconcat: "mcont lSup (\<sqsubseteq>) lSup (\<sqsubseteq>) lconcat"
by(rule llist.fixp_preserves_mcont1[OF lconcat.mono lconcat_def]) simp

lemma lconcat_eq_LNil: "lconcat xss = LNil \<longleftrightarrow> lset xss \<subseteq> {LNil}" (is "?lhs \<longleftrightarrow> ?rhs")
by(induction xss)(auto simp add: lappend_eq_LNil_iff)

lemma lnull_lconcat [simp]: "lnull (lconcat xss) \<longleftrightarrow> lset xss \<subseteq> {xs. lnull xs}"
unfolding lnull_def by(simp add: lconcat_eq_LNil)

lemma lconcat_llist_of:
  "lconcat (llist_of (map llist_of xs)) = llist_of (concat xs)"
by(induct xs)(simp_all add: lappend_llist_of_llist_of)

lemma lhd_lconcat [simp]:
  "\<lbrakk> \<not> lnull xss; \<not> lnull (lhd xss) \<rbrakk> \<Longrightarrow> lhd (lconcat xss) = lhd (lhd xss)"
by(clarsimp simp add: not_lnull_conv)

lemma ltl_lconcat [simp]:
  "\<lbrakk> \<not> lnull xss; \<not> lnull (lhd xss) \<rbrakk> \<Longrightarrow> ltl (lconcat xss) = lappend (ltl (lhd xss)) (lconcat (ltl xss))"
by(clarsimp simp add: not_lnull_conv)

lemma lmap_lconcat:
  "lmap f (lconcat xss) = lconcat (lmap (lmap f) xss)"
by(induct xss)(simp_all add: lmap_lappend_distrib)

lemma lconcat_lappend [simp]:
  assumes "lfinite xss"
  shows "lconcat (lappend xss yss) = lappend (lconcat xss) (lconcat yss)"
using assms
by induct (simp_all add: lappend_assoc)

lemma lconcat_eq_LCons_conv:
  "lconcat xss = LCons x xs \<longleftrightarrow>
  (\<exists>xs' xss' xss''. xss = lappend (llist_of xss') (LCons (LCons x xs') xss'') \<and>
                    xs = lappend xs' (lconcat xss'') \<and> set xss' \<subseteq> {xs. lnull xs})"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?rhs"
  then obtain xs' xss' xss''
    where "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and "xs = lappend xs' (lconcat xss'')"
    and "set xss' \<subseteq> {xs. lnull xs}" by blast
  moreover from `set xss' \<subseteq> {xs. lnull xs}`
  have "lnull (lconcat (llist_of xss'))" by simp
  ultimately show ?lhs by(simp add: lappend_lnull1)
next
  assume "?lhs"
  hence "\<not> lnull (lconcat xss)" by simp
  hence "\<not> lset xss \<subseteq> {xs. lnull xs}" by simp
  hence "\<not> lnull (lfilter (\<lambda>xs. \<not> lnull xs) xss)" by(auto)
  then obtain y ys where yys: "lfilter (\<lambda>xs. \<not> lnull xs) xss = LCons y ys"
    unfolding not_lnull_conv by auto
  from lfilter_eq_LConsD[OF this]
  obtain us vs where xss: "xss = lappend us (LCons y vs)"
    and "lfinite us"
    and "lset us \<subseteq> {xs. lnull xs}" "\<not> lnull y"
    and ys: "ys = lfilter (\<lambda>xs. \<not> lnull xs) vs" by blast
  from `lfinite us` obtain us' where [simp]: "us = llist_of us'"
    unfolding lfinite_eq_range_llist_of by blast
  from `lset us \<subseteq> {xs. lnull xs}` have us: "lnull (lconcat us)"
    unfolding lnull_lconcat .
  from `\<not> lnull y` obtain y' ys' where y: "y = LCons y' ys'"
    unfolding not_lnull_conv by blast
  from `?lhs` us have [simp]: "y' = x" "xs = lappend ys' (lconcat vs)"
    unfolding xss y by(simp_all add: lappend_lnull1)
  from `lset us \<subseteq> {xs. lnull xs}` ys show ?rhs unfolding xss y by simp blast
qed

lemma llength_lconcat_lfinite_conv_sum:
  assumes "lfinite xss"
  shows "llength (lconcat xss) = (\<Sum>i | enat i < llength xss. llength (lnth xss i))"
using assms
proof(induct)
  case lfinite_LNil thus ?case by simp
next
  case (lfinite_LConsI xss xs)
  have "{i. enat i \<le> llength xss} = insert 0 {Suc i|i. enat i < llength xss}"
    by(auto simp add: zero_enat_def[symmetric] Suc_ile_eq gr0_conv_Suc)
  also have "\<dots> = insert 0 (Suc ` {i. enat i < llength xss})" by auto
  also have "0 \<notin> Suc ` {i. enat i < llength xss}" by auto
  moreover from `lfinite xss` have "finite {i. enat i < llength xss}"
    by(rule lfinite_finite_index)
  ultimately show ?case using lfinite_LConsI
    by(simp add: sum.reindex)
qed

lemma lconcat_lfilter_neq_LNil:
  "lconcat (lfilter (\<lambda>xs. \<not> lnull xs) xss) = lconcat xss"
by(induct xss)(simp_all add: lappend_lnull1)

lemmas lconcat_fixp_parallel_induct =
  parallel_fixp_induct_1_1[OF llist_partial_function_definitions llist_partial_function_definitions
    lconcat.mono lconcat.mono lconcat_def lconcat_def, case_names adm LNil step]

lemma llist_all2_lconcatI:
  "llist_all2 (llist_all2 A) xss yss
  \<Longrightarrow> llist_all2 A (lconcat xss) (lconcat yss)"
by(induct arbitrary: xss yss rule: lconcat_fixp_parallel_induct)(auto split: llist.split intro: llist_all2_lappendI)

lemma llength_lconcat_eqI:
  fixes xss :: "'a llist llist" and yss :: "'b llist llist"
  assumes "llist_all2 (\<lambda>xs ys. llength xs = llength ys) xss yss"
  shows "llength (lconcat xss) = llength (lconcat yss)"
apply(rule llist_all2_llengthD[where P="\<lambda>_ _. True"])
apply(rule llist_all2_lconcatI)
apply(simp add: llist_all2_True[abs_def] assms)
done

lemma lset_lconcat_lfinite:
  "\<forall>xs \<in> lset xss. lfinite xs \<Longrightarrow> lset (lconcat xss) = (\<Union>xs\<in>lset xss. lset xs)"
by(induction xss) auto

lemma lconcat_ltake:
  "lconcat (ltake (enat n) xss) = ltake (\<Sum>i<n. llength (lnth xss i)) (lconcat xss)"
proof(induct n arbitrary: xss)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  show ?case
  proof(cases xss)
    case LNil thus ?thesis by simp
  next
    case (LCons xs xss')
    hence "lconcat (ltake (enat (Suc n)) xss) = lappend xs (lconcat (ltake (enat n) xss'))"
      by(simp add: eSuc_enat[symmetric])
    also have "lconcat (ltake (enat n) xss') = ltake (\<Sum>i<n. llength (lnth xss' i)) (lconcat xss')" by(rule Suc)
    also have "lappend xs \<dots> = ltake (llength xs + (\<Sum>i<n. llength (lnth xss' i))) (lappend xs (lconcat xss'))"
      by(cases "llength xs")(simp_all add: ltake_plus_conv_lappend ltake_lappend1 ltake_all ldropn_lappend2 lappend_inf lfinite_conv_llength_enat ldrop_enat)
    also have "(\<Sum>i<n. llength (lnth xss' i)) = (\<Sum>i=1..<Suc n. llength (lnth xss i))"
      by (rule sum.reindex_cong [symmetric, of Suc])
        (auto simp add: LCons image_iff less_Suc_eq_0_disj)
    also have "llength xs + \<dots> = (\<Sum>i<Suc n. llength (lnth xss i))"
      unfolding atLeast0LessThan[symmetric] LCons
      by(subst (2) sum_head_upt_Suc) simp_all
    finally show ?thesis using LCons by simp
  qed
qed

lemma lnth_lconcat_conv:
  assumes "enat n < llength (lconcat xss)"
  shows "\<exists>m n'. lnth (lconcat xss) n = lnth (lnth xss m) n' \<and> enat n' < llength (lnth xss m) \<and>
                enat m < llength xss \<and> enat n = (\<Sum>i<m . llength (lnth xss i)) + enat n'"
using assms
proof(induct n arbitrary: xss)
  case 0
  hence "\<not> lnull (lconcat xss)" by auto
  then obtain x xs where concat_xss: "lconcat xss = LCons x xs"
    unfolding not_lnull_conv by blast
  then obtain xs' xss' xss''
    where xss: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and xs: "xs = lappend xs' (lconcat xss'')"
    and LNil: "set xss' \<subseteq> {xs. lnull xs}"
    unfolding lconcat_eq_LCons_conv by blast
  from LNil have "lnull (lconcat (llist_of xss'))" by simp
  moreover have [simp]: "lnth xss (length xss') = LCons x xs'"
    unfolding xss by(simp add: lnth_lappend2)
  ultimately have "lnth (lconcat xss) 0 = lnth (lnth xss (length xss')) 0"
    using concat_xss xss by(simp)
  moreover have "enat 0 < llength (lnth xss (length xss'))"
    by(simp add: zero_enat_def[symmetric])
  moreover have "enat (length xss') < llength xss" unfolding xss
    by simp
  moreover have "(\<Sum>i < length xss'. llength (lnth xss i)) = (\<Sum>i < length xss'. 0)"
  proof(rule sum.cong)
    show "{..< length xss'} = {..< length xss'}" by simp
  next
    fix i
    assume "i \<in> {..< length xss'}"
    hence "xss' ! i \<in> set xss'" unfolding in_set_conv_nth by blast
    with LNil have "xss' ! i = LNil" by auto
    moreover from `i \<in> {..< length xss'}` have "lnth xss i = xss' ! i"
      unfolding xss by(simp add: lnth_lappend1)
    ultimately show "llength (lnth xss i) = 0" by simp
  qed
  hence "enat 0 = (\<Sum>i<length xss'. llength (lnth xss i)) + enat 0"
    by(simp add: zero_enat_def[symmetric])
  ultimately show ?case by blast
next
  case (Suc n)
  from `enat (Suc n) < llength (lconcat xss)`
  have "\<not> lnull (lconcat xss)" by auto
  then obtain x xs where concat_xss: "lconcat xss = LCons x xs"
    unfolding not_lnull_conv by blast
  then obtain xs' xss' xss'' where xss: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
    and xs: "xs = lappend xs' (lconcat xss'')"
    and LNil: "set xss' \<subseteq> {xs. lnull xs}"
    unfolding lconcat_eq_LCons_conv by blast
  from LNil have concat_xss': "lnull (lconcat (llist_of xss'))" by simp
  from xs have "xs = lconcat (LCons xs' xss'')" by simp
  with concat_xss `enat (Suc n) < llength (lconcat xss)`
  have "enat n < llength (lconcat (LCons xs' xss''))"
    by(simp add: Suc_ile_eq)
  from Suc.hyps[OF this] obtain m n'
    where nth_n: "lnth (lconcat (LCons xs' xss'')) n = lnth (lnth (LCons xs' xss'') m) n'"
    and n': "enat n' < llength (lnth (LCons xs' xss'') m)"
    and m': "enat m < llength (LCons xs' xss'')"
    and n_eq: "enat n = (\<Sum>i < m. llength (lnth (LCons xs' xss'') i)) + enat n'"
    by blast
  from n_eq obtain N where N: "(\<Sum>i < m. llength (lnth (LCons xs' xss'') i)) = enat N"
    and n: "n = N + n'"
    by(cases "\<Sum>i < m. llength (lnth (LCons xs' xss'') i)") simp_all


  { fix i
    assume i: "i < length xss'"
    hence "xss' ! i = LNil" using LNil unfolding set_conv_nth by auto
    hence "lnth xss i = LNil" using i unfolding xss
      by(simp add: lnth_lappend1) }
  note lnth_prefix = this

  show ?case
  proof(cases "m > 0")
    case True
    then obtain m' where [simp]: "m = Suc m'" by(cases m) auto
    have "lnth (lconcat xss) (Suc n) = lnth (lnth xss (m + length xss')) n'"
      using concat_xss' nth_n unfolding xss by(simp add: lnth_lappend2 lappend_lnull1)
    moreover have "enat n' < llength (lnth xss (m + length xss'))"
      using concat_xss' n' unfolding xss by(simp add: lnth_lappend2)
    moreover have "enat (m + length xss') < llength xss"
      using concat_xss' m' unfolding xss
      apply (simp add: Suc_ile_eq)
      apply (simp add: eSuc_enat[symmetric] eSuc_plus_1
        plus_enat_simps(1)[symmetric] del: plus_enat_simps(1))
      done
    moreover have "enat (m + length xss') < llength xss"
      using m' unfolding xss
      apply(simp add: Suc_ile_eq)
      apply (simp add: eSuc_enat[symmetric] eSuc_plus_1
        plus_enat_simps(1)[symmetric] del: plus_enat_simps(1))
      done
    moreover
    { have "(\<Sum>i < m + length xss'. llength (lnth xss i)) =
            (\<Sum>i < length xss'. llength (lnth xss i)) +
            (\<Sum>i = length xss'..<m + length xss'. llength (lnth xss i))"
        by(subst (1 2) atLeast0LessThan[symmetric])(subst sum_add_nat_ivl, simp_all)
      also from lnth_prefix have "(\<Sum>i < length xss'. llength (lnth xss i)) = 0" by simp
      also have "{length xss'..<m + length xss'} = {0+length xss'..<m+length xss'}" by auto
      also have "(\<Sum>i = 0 + length xss'..<m + length xss'. llength (lnth xss i)) =
                (\<Sum>i = 0..<m. llength (lnth xss (i + length xss')))"
        by(rule sum_shift_bounds_nat_ivl)
      also have "\<dots> = (\<Sum>i = 0..<m. llength (lnth (LCons (LCons x xs') xss'') i))"
        unfolding xss by(subst lnth_lappend2) simp+
      also have "\<dots> = eSuc (llength xs') + (\<Sum>i = Suc 0..<m. llength (lnth (LCons (LCons x xs') xss'') i))"
        by(subst sum_head_upt_Suc) simp_all
      also {
        fix i
        assume "i \<in> {Suc 0..<m}"
        then obtain i' where "i = Suc i'" by(cases i) auto
        hence "llength (lnth (LCons (LCons x xs') xss'') i) = llength (lnth (LCons xs' xss'') i)"
          by simp }
      hence "(\<Sum>i = Suc 0..<m. llength (lnth (LCons (LCons x xs') xss'') i)) =
             (\<Sum>i = Suc 0..<m. llength (lnth (LCons xs' xss'') i))" by(simp)
      also have "eSuc (llength xs') + \<dots> = 1 + (llength (lnth (LCons xs' xss'') 0) + \<dots>)"
        by(simp add: eSuc_plus_1 ac_simps)
      also note sum_head_upt_Suc[symmetric, OF `0 < m`]
      finally have "enat (Suc n) = (\<Sum>i<m + length xss'. llength (lnth xss i)) + enat n'"
        unfolding eSuc_enat[symmetric] n_eq by(simp add: eSuc_plus_1 ac_simps atLeast0LessThan) }
    ultimately show ?thesis by blast
  next
    case False
    hence [simp]: "m = 0" by auto
    have "lnth (lconcat xss) (Suc n) = lnth (lnth xss (length xss')) (Suc n')"
      using concat_xss n_eq xs n'
      unfolding xss by(simp add: lnth_lappend1 lnth_lappend2)
    moreover have "enat (Suc n') < llength (lnth xss (length xss'))"
      using concat_xss n' unfolding xss by(simp add: lnth_lappend2 Suc_ile_eq)
    moreover have "enat (length xss') < llength xss" unfolding xss
      by simp
    moreover from lnth_prefix have "(\<Sum>i<length xss'. llength (lnth xss i)) = 0" by simp
    hence "enat (Suc n) = (\<Sum>i<length xss'. llength (lnth xss i)) + enat (Suc n')"
      using n_eq by simp
    ultimately show ?thesis by blast
  qed
qed

lemma lprefix_lconcatI:
  "xss \<sqsubseteq> yss \<Longrightarrow> lconcat xss \<sqsubseteq> lconcat yss"
by(rule monotoneD[OF monotone_lconcat])

lemma lnth_lconcat_ltake:
  assumes "enat w < llength (lconcat (ltake (enat n) xss))"
  shows "lnth (lconcat (ltake (enat n) xss)) w = lnth (lconcat xss) w"
using assms by(auto intro: lprefix_lnthD lprefix_lconcatI)

lemma lfinite_lconcat [simp]:
  "lfinite (lconcat xss) \<longleftrightarrow> lfinite (lfilter (\<lambda>xs. \<not> lnull xs) xss) \<and> (\<forall>xs \<in> lset xss. lfinite xs)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume "?lhs"
  thus "?rhs" (is "?concl xss")
  proof(induct "lconcat xss" arbitrary: xss)
    case [symmetric]: lfinite_LNil
    moreover hence "lnull (lfilter (\<lambda>xs. \<not> lnull xs) xss)"
      by(auto simp add: lconcat_eq_LNil)
    ultimately show ?case by(auto)
  next
    case (lfinite_LConsI xs x)
    from `LCons x xs = lconcat xss`[symmetric]
    obtain xs' xss' xss'' where xss [simp]: "xss = lappend (llist_of xss') (LCons (LCons x xs') xss'')"
      and xs [simp]: "xs = lappend xs' (lconcat xss'')"
      and xss': "set xss' \<subseteq> {xs. lnull xs}" unfolding lconcat_eq_LCons_conv by blast
    have "xs = lconcat (LCons xs' xss'')" by simp
    hence "?concl (LCons xs' xss'')" by(rule lfinite_LConsI)
    thus ?case using `lfinite xs` xss' by(auto split: if_split_asm)
  qed
next
  assume "?rhs"
  then obtain "lfinite (lfilter (\<lambda>xs. \<not> lnull xs) xss)"
    and "\<forall>xs\<in>lset xss. lfinite xs" ..
  thus ?lhs
  proof(induct "lfilter (\<lambda>xs. \<not> lnull xs) xss" arbitrary: xss)
    case lfinite_LNil
    from `LNil = lfilter (\<lambda>xs. \<not> lnull xs) xss`[symmetric]
    have "lset xss \<subseteq> {xs. lnull xs}" unfolding lfilter_empty_conv by blast
    hence "lnull (lconcat xss)" by(simp)
    thus ?case by(simp)
  next
    case (lfinite_LConsI xs x)
    from lfilter_eq_LConsD[OF `LCons x xs = lfilter (\<lambda>xs. \<not> lnull xs) xss`[symmetric]]
    obtain xss' xss'' where xss [simp]: "xss = lappend xss' (LCons x xss'')"
      and xss': "lfinite xss'" "lset xss' \<subseteq> {xs. lnull xs}"
      and x: "\<not> lnull x"
      and xs [simp]: "xs = lfilter (\<lambda>xs. \<not> lnull xs) xss''" by blast
    moreover
    from `\<forall>xs\<in>lset xss. lfinite xs` xss' have "\<forall>xs\<in>lset xss''. lfinite xs" by auto
    with xs have "lfinite (lconcat xss'')" by(rule lfinite_LConsI)
    ultimately show ?case using `\<forall>xs\<in>lset xss. lfinite xs` by(simp)
  qed
qed

lemma list_of_lconcat:
  assumes "lfinite xss"
  and "\<forall>xs \<in> lset xss. lfinite xs"
  shows "list_of (lconcat xss) = concat (list_of (lmap list_of xss))"
using assms by induct(simp_all add: list_of_lappend)

lemma lfilter_lconcat_lfinite:
  "\<forall>xs\<in>lset xss. lfinite xs
  \<Longrightarrow> lfilter P (lconcat xss) = lconcat (lmap (lfilter P) xss)"
by(induct xss) simp_all

lemma lconcat_repeat_LNil [simp]: "lconcat (repeat LNil) = LNil"
by(simp add: lconcat_eq_LNil)

lemma lconcat_lmap_singleton [simp]: "lconcat (lmap (\<lambda>x. LCons (f x) LNil) xs) = lmap f xs"
by(induct xs) simp_all

lemma lset_lconcat_subset: "lset (lconcat xss) \<subseteq> (\<Union>xs\<in>lset xss. lset xs)"
by(induct xss)(auto dest: subsetD[OF lset_lappend])

lemma ldistinct_lconcat:
  "\<lbrakk> ldistinct xss; \<And>ys. ys \<in> lset xss \<Longrightarrow> ldistinct ys;
     \<And>ys zs. \<lbrakk> ys \<in> lset xss; zs \<in> lset xss; ys \<noteq> zs \<rbrakk> \<Longrightarrow> lset ys \<inter> lset zs = {} \<rbrakk>
  \<Longrightarrow> ldistinct (lconcat xss)"
apply(induction arbitrary: xss rule: lconcat.fixp_induct)
apply(auto simp add: ldistinct_lappend fun_ord_def split: llist.split)
apply(blast dest!: subsetD[OF lprefix_lsetD] subsetD[OF lset_lconcat_subset])
done

subsection {* Sublist view of a lazy list: @{term "lnths"} *}

lemma lnths_empty [simp]: "lnths xs {} = LNil"
by(auto simp add: lnths_def split_def lfilter_empty_conv)

lemma lnths_LNil [simp]: "lnths LNil A = LNil"
by(simp add: lnths_def)

lemma lnths_LCons:
  "lnths (LCons x xs) A =
  (if 0 \<in> A then LCons x (lnths xs {n. Suc n \<in> A}) else lnths xs {n. Suc n \<in> A})"
proof -
  let ?it = "iterates Suc"
  let ?f = "\<lambda>(x, y). (x, Suc y)"
  { fix n
    have "lzip xs (?it (Suc n)) = lmap ?f (lzip xs (?it n))"
      by(coinduction arbitrary: xs n)(auto)
    hence "lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (?it (Suc n)))) =
           lmap fst (lfilter (\<lambda>(x, y). Suc y \<in> A) (lzip xs (?it n)))"
      by(simp add: lfilter_lmap o_def split_def llist.map_comp) }
  thus ?thesis
    by(auto simp add: lnths_def)(subst iterates, simp)+
qed

lemma lset_lnths:
  "lset (lnths xs I) = {lnth xs i|i. enat i<llength xs \<and> i \<in> I}"
apply(auto simp add: lnths_def lset_lzip)
apply(rule_tac x="(lnth xs i, i)" in image_eqI)
apply auto
done

lemma lset_lnths_subset: "lset (lnths xs I) \<subseteq> lset xs"
by(auto simp add: lset_lnths in_lset_conv_lnth)

lemma lnths_singleton [simp]:
  "lnths (LCons x LNil) A = (if 0 : A then LCons x LNil else LNil)"
by (simp add: lnths_LCons)

lemma lnths_upt_eq_ltake [simp]:
  "lnths xs {..<n} = ltake (enat n) xs"
apply(rule sym)
proof(induct n arbitrary: xs)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  thus ?case
    by(cases xs)(simp_all add: eSuc_enat[symmetric] lnths_LCons lessThan_def)
qed

lemma lnths_llist_of [simp]:
  "lnths (llist_of xs) A = llist_of (nths xs A)"
by(induct xs arbitrary: A)(simp_all add: lnths_LCons nths_Cons)

lemma llength_lnths_ile: "llength (lnths xs A) \<le> llength xs"
proof -
  have "llength (lfilter (\<lambda>(x, y). y \<in> A) (lzip xs (iterates Suc 0))) \<le>
        llength (lzip xs (iterates Suc 0))"
    by(rule llength_lfilter_ile)
  thus ?thesis by(simp add: lnths_def)
qed

lemma lnths_lmap [simp]:
  "lnths (lmap f xs) A = lmap f (lnths xs A)"
by(simp add: lnths_def lzip_lmap1 llist.map_comp lfilter_lmap o_def split_def)

lemma lfilter_conv_lnths:
  "lfilter P xs = lnths xs {n. enat n < llength xs \<and> P (lnth xs n)}"
proof -
  have "lnths xs {n. enat n < llength xs \<and> P (lnth xs n)} =
        lmap fst (lfilter (\<lambda>(x, y). enat y < llength xs \<and> P (lnth xs y))
                          (lzip xs (iterates Suc 0)))"
    by(simp add: lnths_def)
  also have "\<forall>(x, y)\<in>lset (lzip xs (iterates Suc 0)). enat y < llength xs \<and> x = lnth xs y"
    by(auto simp add: lset_lzip)
  hence "lfilter (\<lambda>(x, y). enat y < llength xs \<and> P (lnth xs y)) (lzip xs (iterates Suc 0)) =
         lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))"
    by -(rule lfilter_cong[OF refl], auto)
  also have "lmap fst (lfilter (P \<circ> fst) (lzip xs (iterates Suc 0))) =
            lfilter P (lmap fst (lzip xs (iterates Suc 0)))"
    unfolding lfilter_lmap ..
  also have "lmap fst (lzip xs (iterates Suc 0)) = xs"
    by(simp add: lmap_fst_lzip_conv_ltake ltake_all)
  finally show ?thesis ..
qed

lemma ltake_iterates_Suc:
  "ltake (enat n) (iterates Suc m) = llist_of [m..<n + m]"
proof(induct n arbitrary: m)
  case 0 thus ?case by(simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  have "ltake (enat (Suc n)) (iterates Suc m) =
        LCons m (ltake (enat n) (iterates Suc (Suc m)))"
    by(subst iterates)(simp add: eSuc_enat[symmetric])
  also note Suc
  also have "LCons m (llist_of [Suc m..<n + Suc m]) = llist_of [m..<Suc n+m]"
    unfolding llist_of.simps[symmetric]
    by(auto simp del: llist_of.simps simp add: upt_conv_Cons)
  finally show ?case .
qed

lemma lnths_lappend_lfinite:
  assumes len: "llength xs = enat k"
  shows "lnths (lappend xs ys) A =
         lappend (lnths xs A) (lnths ys {n. n + k \<in> A})"
proof -
  let ?it = "iterates Suc"
  from assms have fin: "lfinite xs" by(rule llength_eq_enat_lfiniteD)
  have "lnths (lappend xs ys) A =
    lmap fst (lfilter (\<lambda>(x, y). y \<in> A) (lzip (lappend xs ys) (?it 0)))"
    by(simp add: lnths_def)
  also have "?it 0 = lappend (ltake (enat k) (?it 0)) (ldrop (enat k) (?it 0))"
    by(simp only: lappend_ltake_ldrop)
  also note lzip_lappend
  also note lfilter_lappend_lfinite
  also note lmap_lappend_distrib
  also have "lzip xs (ltake (enat k) (?it 0)) = lzip xs (?it 0)"
    using len by(subst (1 2) lzip_conv_lzip_ltake_min_llength) simp
  also note lnths_def[symmetric]
  also have "ldrop (enat k) (?it 0) = ?it k"
    by(simp add: ldrop_iterates)
  also { fix n m
    have "?it (n + m) = lmap (\<lambda>n. n + m) (?it n)"
      by(coinduction arbitrary: n)(force)+ }
  from this[of 0 k] have "?it k = lmap (\<lambda>n. n + k) (?it 0)" by simp
  also note lzip_lmap2
  also note lfilter_lmap
  also note llist.map_comp
  also have "fst \<circ> (\<lambda>(x, y). (x, y + k)) = fst"
    by(simp add: o_def split_def)
  also have "(\<lambda>(x, y). y \<in> A) \<circ> (\<lambda>(x, y). (x, y + k)) = (\<lambda>(x, y). y \<in> {n. n + k \<in> A})"
    by(simp add: fun_eq_iff)
  also note lnths_def[symmetric]
  finally show ?thesis using len by simp
qed

lemma lnths_split:
  "lnths xs A =
   lappend (lnths (ltake (enat n) xs) A) (lnths (ldropn n xs) {m. n + m \<in> A})"
proof(cases "enat n \<le> llength xs")
  case False thus ?thesis by(auto simp add: ltake_all ldropn_all)
next
  case True
  have "xs = lappend (ltake (enat n) xs) (ldrop (enat n) xs)"
    by(simp only: lappend_ltake_ldrop)
  hence "xs = lappend (ltake (enat n) xs) (ldropn n xs)" by simp
  hence "lnths xs A = lnths (lappend (ltake (enat n) xs) (ldropn n xs)) A"
    by(simp)
  also note lnths_lappend_lfinite[where k=n]
  finally show ?thesis using True by(simp add: min_def ac_simps)
qed

lemma lnths_cong:
  assumes "xs = ys" and A: "\<And>n. enat n < llength ys \<Longrightarrow> n \<in> A \<longleftrightarrow> n \<in> B"
  shows "lnths xs A = lnths ys B"
proof -
  have "lfilter (\<lambda>(x, y). y \<in> A) (lzip ys (iterates Suc 0)) =
        lfilter (\<lambda>(x, y). y \<in> B) (lzip ys (iterates Suc 0))"
    by(rule lfilter_cong[OF refl])(auto simp add: lset_lzip A)
  thus ?thesis unfolding `xs = ys` lnths_def by simp
qed

lemma lnths_insert:
  assumes n: "enat n < llength xs"
  shows "lnths xs (insert n A) =
         lappend (lnths (ltake (enat n) xs) A) (LCons (lnth xs n)
                 (lnths (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A}))"
proof -
  have "lnths xs (insert n A) =
        lappend (lnths (ltake (enat n) xs) (insert n A))
                (lnths (ldropn n xs) {m. n + m \<in> (insert n A)})"
    by(rule lnths_split)
  also have "lnths (ltake (enat n) xs) (insert n A) =
            lnths (ltake (enat n) xs) A"
    by(rule lnths_cong[OF refl]) simp
  also { from n obtain X XS where "ldropn n xs = LCons X XS"
      by(cases "ldropn n xs")(auto simp add: ldropn_eq_LNil)
    moreover have "lnth (ldropn n xs) 0 = lnth xs n"
      using n by(simp)
    moreover have "ltl (ldropn n xs) = ldropn (Suc n) xs"
      by(cases xs)(simp_all add: ltl_ldropn)
    ultimately have "ldropn n xs = LCons (lnth xs n) (ldropn (Suc n) xs)" by simp
    hence "lnths (ldropn n xs) {m. n + m \<in> insert n A} =
           LCons (lnth xs n) (lnths (ldropn (Suc n) xs) {m. Suc (n + m) \<in> A})"
      by(simp add: lnths_LCons) }
  finally show ?thesis .
qed

lemma lfinite_lnths [simp]:
  "lfinite (lnths xs A) \<longleftrightarrow> lfinite xs \<or> finite A"
proof
  assume "lfinite (lnths xs A)"
  hence "lfinite xs \<or>
         finite {n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)}"
    by(simp add: lnths_def lfinite_lfilter)
  also have "{n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
            {n. enat n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  finally show "lfinite xs \<or> finite A"
    by(auto simp add: not_lfinite_llength elim: contrapos_np)
next
  assume "lfinite xs \<or> finite A"
  moreover
  have "{n. enat n < llength xs \<and> (\<lambda>(x, y). y \<in> A) (lnth (lzip xs (iterates Suc 0)) n)} =
        {n. enat n < llength xs \<and> n \<in> A}" by(auto simp add: lnth_lzip)
  ultimately show "lfinite (lnths xs A)"
    by(auto simp add: lnths_def lfinite_lfilter)
qed

subsection {* @{const "lsum_list"} *}

context monoid_add begin

lemma lsum_list_0 [simp]: "lsum_list (lmap (\<lambda>_. 0) xs) = 0"
by(simp add: lsum_list_def)

lemma lsum_list_llist_of [simp]: "lsum_list (llist_of xs) = sum_list xs"
by(simp add: lsum_list_def)

lemma lsum_list_lappend: "\<lbrakk> lfinite xs; lfinite ys \<rbrakk> \<Longrightarrow> lsum_list (lappend xs ys) = lsum_list xs + lsum_list ys"
by(simp add: lsum_list_def list_of_lappend)

lemma lsum_list_LNil [simp]: "lsum_list LNil = 0"
by(simp add: lsum_list_def)

lemma lsum_list_LCons [simp]: "lfinite xs \<Longrightarrow> lsum_list (LCons x xs) = x + lsum_list xs"
by(simp add: lsum_list_def)

lemma lsum_list_inf [simp]: "\<not> lfinite xs \<Longrightarrow> lsum_list xs = 0"
by(simp add: lsum_list_def)

end

lemma lsum_list_mono:
  fixes f :: "'a \<Rightarrow> 'b :: {monoid_add, ordered_ab_semigroup_add}"
  assumes "\<And>x. x \<in> lset xs \<Longrightarrow> f x \<le> g x"
  shows "lsum_list (lmap f xs) \<le> lsum_list (lmap g xs)"
using assms
by(auto simp add: lsum_list_def intro: sum_list_mono)

subsection {*
  Alternative view on @{typ "'a llist"} as datatype
  with constructors @{term "llist_of"} and @{term "inf_llist"}
*}

lemma lnull_inf_llist [simp]: "\<not> lnull (inf_llist f)"
by(simp add: inf_llist_def)

lemma inf_llist_neq_LNil: "inf_llist f \<noteq> LNil"
using lnull_inf_llist unfolding lnull_def .

lemmas LNil_neq_inf_llist = inf_llist_neq_LNil[symmetric]

lemma lhd_inf_llist [simp]: "lhd (inf_llist f) = f 0"
by(simp add: inf_llist_def)

lemma ltl_inf_llist [simp]: "ltl (inf_llist f) = inf_llist (\<lambda>n. f (Suc n))"

by(simp add: inf_llist_def lmap_iterates[symmetric] llist.map_comp)

lemma inf_llist_rec [code, nitpick_simp]:
  "inf_llist f = LCons (f 0) (inf_llist (\<lambda>n. f (Suc n)))"
by(rule llist.expand) simp_all

lemma lfinite_inf_llist [iff]: "\<not> lfinite (inf_llist f)"
by(simp add: inf_llist_def)

lemma iterates_conv_inf_llist:
  "iterates f a = inf_llist (\<lambda>n. (f ^^ n) a)"
by(coinduction arbitrary: a)(auto simp add: funpow_swap1)

lemma inf_llist_neq_llist_of [simp]:
  "llist_of xs \<noteq> inf_llist f"
   "inf_llist f \<noteq> llist_of xs"
using lfinite_llist_of[of xs] lfinite_inf_llist[of f] by fastforce+

lemma lnth_inf_llist [simp]: "lnth (inf_llist f) n = f n"
proof(induct n arbitrary: f)
  case 0 thus ?case by(subst inf_llist_rec) simp
next
  case (Suc n)
  from Suc[of "\<lambda>n. f (Suc n)"] show ?case
    by(subst inf_llist_rec) simp
qed

lemma inf_llist_lprefix [simp]: "inf_llist f \<sqsubseteq> xs \<longleftrightarrow> xs = inf_llist f"
by(auto simp add: not_lfinite_lprefix_conv_eq)

lemma llength_inf_llist [simp]: "llength (inf_llist f) = \<infinity>"
by(simp add: inf_llist_def)

lemma lset_inf_llist [simp]: "lset (inf_llist f) = range f"
by(auto simp add: lset_conv_lnth)

lemma inf_llist_inj [simp]:
  "inf_llist f = inf_llist g \<longleftrightarrow> f = g"
unfolding inf_llist_def lmap_eq_lmap_conv_llist_all2
by(simp add: iterates_conv_inf_llist fun_eq_iff)

lemma inf_llist_lnth [simp]: "\<not> lfinite xs \<Longrightarrow> inf_llist (lnth xs) = xs"
by(coinduction arbitrary: xs)(auto simp add: lnth_0_conv_lhd fun_eq_iff lnth_ltl)

lemma llist_exhaust:
  obtains (llist_of) ys where "xs = llist_of ys"
       | (inf_llist) f where "xs = inf_llist f"
proof(cases "lfinite xs")
  case True
  then obtain ys where "xs = llist_of ys"
    unfolding lfinite_eq_range_llist_of by auto
  thus ?thesis by(rule that)
next
  case False
  hence "xs = inf_llist (lnth xs)" by simp
  thus thesis by(rule that)
qed

lemma lappend_inf_llist [simp]: "lappend (inf_llist f) xs = inf_llist f"
by(simp add: lappend_inf)

lemma lmap_inf_llist [simp]:
  "lmap f (inf_llist g) = inf_llist (f o g)"
by(simp add: inf_llist_def llist.map_comp)

lemma ltake_enat_inf_llist [simp]:
  "ltake (enat n) (inf_llist f) = llist_of (map f [0..<n])"
by(simp add: inf_llist_def ltake_iterates_Suc)

lemma ldropn_inf_llist [simp]:
  "ldropn n (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
unfolding inf_llist_def ldropn_lmap ldropn_iterates
by(simp add: iterates_conv_inf_llist o_def)

lemma ldrop_enat_inf_llist:
  "ldrop (enat n) (inf_llist f) = inf_llist (\<lambda>m. f (m + n))"
proof(induct n arbitrary: f)
  case Suc thus ?case by(subst inf_llist_rec)(simp add: eSuc_enat[symmetric])
qed(simp add: zero_enat_def[symmetric])

lemma lzip_inf_llist_inf_llist [simp]:
  "lzip (inf_llist f) (inf_llist g) = inf_llist (\<lambda>n. (f n, g n))"
by(coinduction arbitrary: f g) auto

lemma lzip_llist_of_inf_llist [simp]:
  "lzip (llist_of xs) (inf_llist f) = llist_of (zip xs (map f [0..<length xs]))"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma lzip_inf_llist_llist_of [simp]:
  "lzip (inf_llist f) (llist_of xs) = llist_of (zip (map f [0..<length xs]) xs)"
proof(induct xs arbitrary: f)
  case Nil thus ?case by simp
next
  case (Cons x xs)
  have "map f [0..<length (x # xs)] = f 0 # map (\<lambda>n. f (Suc n)) [0..<length xs]"
    by(simp add: upt_conv_Cons map_Suc_upt[symmetric] del: upt_Suc)
  with Cons[of "\<lambda>n. f (Suc n)"]
  show ?case by(subst inf_llist_rec)(simp)
qed

lemma llist_all2_inf_llist [simp]:
  "llist_all2 P (inf_llist f) (inf_llist g) \<longleftrightarrow> (\<forall>n. P (f n) (g n))"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_llist_of_inf_llist [simp]:
  "\<not> llist_all2 P (llist_of xs) (inf_llist f)"
by(simp add: llist_all2_conv_lzip)

lemma llist_all2_inf_llist_llist_of [simp]:
  "\<not> llist_all2 P (inf_llist f) (llist_of xs)"
by(simp add: llist_all2_conv_lzip)

lemma (in monoid_add) lsum_list_infllist: "lsum_list (inf_llist f) = 0"
by simp

subsection {* Setup for lifting and transfer *}

subsubsection {* Relator and predicator properties *}

abbreviation "llist_all == pred_llist"

subsubsection {* Transfer rules for the Transfer package *}

context includes lifting_syntax
begin

lemma set1_pre_llist_transfer [transfer_rule]:
  "(rel_pre_llist A B ===> rel_set A) set1_pre_llist set1_pre_llist"
by(auto simp add: rel_pre_llist_def vimage2p_def rel_fun_def set1_pre_llist_def rel_set_def collect_def sum_set_defs prod_set_defs elim: rel_sum.cases split: sum.split_asm)

lemma set2_pre_llist_transfer [transfer_rule]:
  "(rel_pre_llist A B ===> rel_set B) set2_pre_llist set2_pre_llist"
by(auto simp add: rel_pre_llist_def vimage2p_def rel_fun_def set2_pre_llist_def rel_set_def collect_def sum_set_defs prod_set_defs elim: rel_sum.cases split: sum.split_asm)

lemma LNil_transfer [transfer_rule]: "llist_all2 P LNil LNil"
by simp

lemma LCons_transfer [transfer_rule]:
  "(A ===> llist_all2 A ===> llist_all2 A) LCons LCons"
unfolding rel_fun_def by simp

lemma case_llist_transfer [transfer_rule]:
  "(B ===> (A ===> llist_all2 A ===> B) ===> llist_all2 A ===> B)
    case_llist case_llist"
unfolding rel_fun_def by (simp split: llist.split)

lemma unfold_llist_transfer [transfer_rule]:
  "((A ===> (=)) ===> (A ===> B) ===> (A ===> A) ===> A ===> llist_all2 B) unfold_llist unfold_llist"
proof(rule rel_funI)+
  fix IS_LNIL1 :: "'a \<Rightarrow> bool" and IS_LNIL2 LHD1 LHD2 LTL1 LTL2 x y
  assume rel: "(A ===> (=)) IS_LNIL1 IS_LNIL2" "(A ===> B) LHD1 LHD2" "(A ===> A) LTL1 LTL2"
    and "A x y"
  from `A x y`
  show "llist_all2 B (unfold_llist IS_LNIL1 LHD1 LTL1 x) (unfold_llist IS_LNIL2 LHD2 LTL2 y)"
    apply(coinduction arbitrary: x y)
    using rel by(auto 4 4 elim: rel_funE)
qed

lemma llist_corec_transfer [transfer_rule]:
  "((A ===> (=)) ===> (A ===> B) ===> (A ===> (=)) ===> (A ===> llist_all2 B) ===> (A ===> A) ===> A ===> llist_all2 B) corec_llist corec_llist"
proof(rule rel_funI)+
  fix IS_LNIL1 :: "'a \<Rightarrow> bool" and IS_LNIL2 LHD1 LHD2
    and STOP1 :: "'a \<Rightarrow> bool" and STOP2 MORE1 MORE2 LTL1 LTL2 x y
  assume [transfer_rule]: "(A ===> (=)) IS_LNIL1 IS_LNIL2 " "(A ===> B) LHD1 LHD2"
    "(A ===> (=)) STOP1 STOP2" "(A ===> llist_all2 B) MORE1 MORE2" "(A ===> A) LTL1 LTL2"
  assume "A x y"
  thus "llist_all2 B (corec_llist IS_LNIL1 LHD1 STOP1 MORE1 LTL1 x) (corec_llist IS_LNIL2 LHD2 STOP2 MORE2 LTL2 y)"
  proof(coinduction arbitrary: x y)
    case [transfer_rule]: (LNil x y)
    show ?case by simp transfer_prover
  next
    case (LCons x y)
    note [transfer_rule] = `A x y`
    have ?lhd by(simp add: LCons[simplified]) transfer_prover
    moreover
    have "STOP1 x = STOP2 y" "llist_all2 B (MORE1 x) (MORE2 y)" "A (LTL1 x) (LTL2 y)" by transfer_prover+
    hence ?ltl by(auto simp add: LCons[simplified])
    ultimately show ?case ..
  qed
qed

lemma ltl_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A) ltl ltl"
  unfolding ltl_def[abs_def] by transfer_prover

lemma lset_transfer [transfer_rule]:
  "(llist_all2 A ===> rel_set A) lset lset"
by (intro rel_funI rel_setI) (auto simp only: in_lset_conv_lnth llist_all2_conv_all_lnth Bex_def)

lemma lmap_transfer [transfer_rule]:
  "((A ===> B) ===> llist_all2 A ===> llist_all2 B) lmap lmap"
by(auto simp add: rel_fun_def llist_all2_lmap1 llist_all2_lmap2 elim: llist_all2_mono)

lemma lappend_transfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 A ===> llist_all2 A) lappend lappend"
by(auto simp add: rel_fun_def intro: llist_all2_lappendI)

lemma iterates_transfer [transfer_rule]:
  "((A ===> A) ===> A ===> llist_all2 A) iterates iterates"
unfolding iterates_def split_def corec_llist_never_stop by transfer_prover

lemma lfinite_transfer [transfer_rule]:
  "(llist_all2 A ===> (=)) lfinite lfinite"
by(auto dest: llist_all2_lfiniteD)

lemma llist_of_transfer [transfer_rule]:
  "(list_all2 A ===> llist_all2 A) llist_of llist_of"
unfolding llist_of_def by transfer_prover

lemma llength_transfer [transfer_rule]:
  "(llist_all2 A ===> (=)) llength llength"
by(auto dest: llist_all2_llengthD)

lemma ltake_transfer [transfer_rule]:
  "((=) ===> llist_all2 A ===> llist_all2 A) ltake ltake"
by(auto intro: llist_all2_ltakeI)

lemma ldropn_transfer [transfer_rule]:
  "((=) ===> llist_all2 A ===> llist_all2 A) ldropn ldropn"
unfolding ldropn_def[abs_def] by transfer_prover

lemma ldrop_transfer [transfer_rule]:
  "((=) ===> llist_all2 A ===> llist_all2 A) ldrop ldrop"
by(auto intro: llist_all2_ldropI)

lemma ltakeWhile_transfer [transfer_rule]:
  "((A ===> (=)) ===> llist_all2 A ===> llist_all2 A) ltakeWhile ltakeWhile"
proof(rule rel_funI)+
  fix P :: "'a \<Rightarrow> bool" and Q :: "'b \<Rightarrow> bool" and xs :: "'a llist" and ys :: "'b llist"
  assume PQ: "(A ===> (=)) P Q"
  assume "llist_all2 A xs ys"
  thus "llist_all2 A (ltakeWhile P xs) (ltakeWhile Q ys)"
    apply(coinduction arbitrary: xs ys)
    using PQ by(auto 4 4 elim: rel_funE simp add: not_lnull_conv llist_all2_LCons2 llist_all2_LCons1)
qed

lemma ldropWhile_transfer [transfer_rule]:
  "((A ===> (=)) ===> llist_all2 A ===> llist_all2 A) ldropWhile ldropWhile"
unfolding ldropWhile_eq_ldrop[abs_def] by transfer_prover

lemma lzip_ltransfer [transfer_rule]:
  "(llist_all2 A ===> llist_all2 B ===> llist_all2 (rel_prod A B)) lzip lzip"
by(auto intro: llist_all2_lzipI)

lemma inf_llist_transfer [transfer_rule]:
  "(((=) ===> A) ===> llist_all2 A) inf_llist inf_llist"
unfolding inf_llist_def[abs_def] by transfer_prover

lemma lfilter_transfer [transfer_rule]:
  "((A ===> (=)) ===> llist_all2 A ===> llist_all2 A) lfilter lfilter"
by(auto simp add: rel_fun_def intro: llist_all2_lfilterI)

lemma lconcat_transfer [transfer_rule]:
  "(llist_all2 (llist_all2 A) ===> llist_all2 A) lconcat lconcat"
by(auto intro: llist_all2_lconcatI)

lemma lnths_transfer [transfer_rule]:
  "(llist_all2 A ===> (=) ===> llist_all2 A) lnths lnths"
unfolding lnths_def[abs_def] by transfer_prover

lemma llist_all_transfer [transfer_rule]:
  "((A ===> (=)) ===> llist_all2 A ===> (=)) llist_all llist_all"
unfolding pred_llist_def[abs_def] by transfer_prover

lemma llist_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "llist_all2 R x y"
  and l2: "llist_all2 R a b"
  shows "llist_all2 S x a = llist_all2 T y b"
proof(cases "llength x = llength a")
  case True
  thus ?thesis using l1 l2
    by(simp add: llist_all2_conv_all_lnth)(blast dest: r[rule_format])
next
  case False
  with llist_all2_llengthD[OF l1] llist_all2_llengthD[OF l2]
  show ?thesis by(simp add: llist_all2_conv_all_lnth)
qed

lemma llist_all2_transfer [transfer_rule]:
  "((R ===> R ===> (=)) ===> llist_all2 R ===> llist_all2 R ===> (=)) llist_all2 llist_all2"
by (simp add: llist_all2_rsp rel_fun_def)

end

no_notation lprefix (infix "\<sqsubseteq>" 65)

end
