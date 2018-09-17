(*  Title:       Prefix ordering on coinductive lists as ordering for type class order
    Author:      Andreas Lochbihler
    Maintainer:  Andreas Lochbihler
*)

section {* Instantiation of the order type classes for lazy lists *}
theory Coinductive_List_Prefix imports
  Coinductive_List
  "HOL-Library.Prefix_Order"
begin

subsection {* Instantiation of the order type class *}

instantiation llist :: (type) order begin

definition [code_unfold]: "xs \<le> ys = lprefix xs ys"

definition [code_unfold]: "xs < ys = lstrict_prefix xs ys"

instance
proof(intro_classes)
  fix xs ys zs :: "'a llist"
  show "(xs < ys) = (xs \<le> ys \<and> \<not> ys \<le> xs)"
    unfolding less_llist_def less_eq_llist_def lstrict_prefix_def
    by(auto simp: lprefix_antisym)
  show "xs \<le> xs" unfolding less_eq_llist_def by(rule lprefix_refl)
  show "\<lbrakk>xs \<le> ys; ys \<le> zs\<rbrakk> \<Longrightarrow> xs \<le> zs"
    unfolding less_eq_llist_def by(rule lprefix_trans)
  show "\<lbrakk>xs \<le> ys; ys \<le> xs\<rbrakk> \<Longrightarrow> xs = ys"
    unfolding less_eq_llist_def by(rule lprefix_antisym)
qed

end

lemma le_llist_conv_lprefix [iff]: "(\<le>) = lprefix"
by(simp add: less_eq_llist_def fun_eq_iff)

lemma less_llist_conv_lstrict_prefix [iff]: "(<) = lstrict_prefix"
by(simp add: less_llist_def fun_eq_iff)

instantiation llist :: (type) order_bot begin

definition "bot = LNil"

instance
by(intro_classes)(simp add: bot_llist_def)

end

lemma llist_of_lprefix_llist_of [simp]:
  "lprefix (llist_of xs) (llist_of ys) \<longleftrightarrow> xs \<le> ys"
proof(induct xs arbitrary: ys)
  case (Cons x xs) thus ?case
    by(cases ys)(auto simp add: LCons_lprefix_conv)
qed simp

subsection {* Prefix ordering as a lower semilattice *}

instantiation llist :: (type) semilattice_inf begin

definition [code del]:
  "inf xs ys = 
   unfold_llist (\<lambda>(xs, ys). xs \<noteq> LNil \<longrightarrow> ys \<noteq> LNil \<longrightarrow> lhd xs \<noteq> lhd ys)
     (lhd \<circ> snd) (map_prod ltl ltl) (xs, ys)"

lemma llist_inf_simps [simp, code, nitpick_simp]:
  "inf LNil xs = LNil"
  "inf xs LNil = LNil"
  "inf (LCons x xs) (LCons y ys) = (if x = y then LCons x (inf xs ys) else LNil)"
unfolding inf_llist_def by simp_all

lemma llist_inf_eq_LNil [simp]:
  "lnull (inf xs ys) \<longleftrightarrow> (xs \<noteq> LNil \<longrightarrow> ys \<noteq> LNil \<longrightarrow> lhd xs \<noteq> lhd ys)"
by(simp add: inf_llist_def)

lemma [simp]: assumes "xs \<noteq> LNil" "ys \<noteq> LNil" "lhd xs = lhd ys"
  shows lhd_llist_inf: "lhd (inf xs ys) = lhd ys"
  and  ltl_llist_inf: "ltl (inf xs ys) = inf (ltl xs) (ltl ys)"
using assms by(simp_all add: inf_llist_def)

instance
proof
  fix xs ys zs :: "'a llist"
  show "inf xs ys \<le> xs" unfolding le_llist_conv_lprefix
    by(coinduction arbitrary: xs ys) auto

  show "inf xs ys \<le> ys" unfolding le_llist_conv_lprefix
    by(coinduction arbitrary: xs ys) auto

  assume "xs \<le> ys" "xs \<le> zs"
  thus "xs \<le> inf ys zs" unfolding le_llist_conv_lprefix
  proof(coinduction arbitrary: xs ys zs)
    case (lprefix xs ys zs)
    thus ?case by(cases xs)(auto 4 4 simp add: LCons_lprefix_conv)
  qed
qed

end

lemma llength_inf [simp]: "llength (inf xs ys) = llcp xs ys"
by(coinduction arbitrary: xs ys rule: enat_coinduct)(auto simp add: llcp_eq_0_iff epred_llength epred_llcp)

instantiation llist :: (type) ccpo
begin

definition "Sup A = lSup A"

instance
  by intro_classes
     (auto simp: Sup_llist_def less_eq_llist_def[abs_def] intro!: llist.lub_upper llist.lub_least)

end

end
