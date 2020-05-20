(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

(*<*)
theory FMap_Lemmas
  imports "HOL-Library.Finite_Map"
          Nominal2_Lemmas
begin
(*>*)

text \<open>Nominal setup for finite maps.\<close>

abbreviation fmap_update ("_'(_ $$:= _')" [1000,0,0] 1000)  where "fmap_update \<Gamma> x \<tau> \<equiv> fmupd x \<tau> \<Gamma>"
notation fmlookup (infixl "$$" 999)
notation fmempty ("{$$}")

instantiation fmap :: (pt, pt) pt
begin

unbundle fmap.lifting

lift_definition
  permute_fmap :: "perm \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap"
  is
  "permute :: perm \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"
proof -
  fix p and f :: "'a \<rightharpoonup> 'b"
  assume "finite (dom f)"
  then show "finite (dom (p \<bullet> f))"
  proof (rule finite_surj[of _ _ "permute p"]; unfold dom_def, safe)
    fix x y
    assume some: "(p \<bullet> f) x = Some y"
    show "x \<in> permute p ` {a. f a \<noteq> None}"
    proof (rule image_eqI[of _ _ "- p \<bullet> x"])
      from some show "- p \<bullet> x \<in> {a. f a \<noteq> None}"
        by (auto simp: permute_self pemute_minus_self
          dest: arg_cong[of _ _ "permute (- p)"] intro!: exI[of _ "- p \<bullet> y"])
    qed (simp only: permute_minus_cancel)
  qed
qed

instance
proof
  fix x :: "('a, 'b) fmap"
  show "0 \<bullet> x = x"
    by transfer simp
next
  fix p q and x :: "('a, 'b) fmap"
  show "(p + q) \<bullet> x = p \<bullet> q \<bullet> x"
    by transfer simp
qed

end

lemma fmempty_eqvt[eqvt]:
  shows "(p \<bullet> {$$}) = {$$}"
  by transfer simp

lemma fmap_update_eqvt[eqvt]:
  shows "(p \<bullet> f(a $$:= b)) = (p \<bullet> f)((p \<bullet> a) $$:= (p \<bullet> b))"
  by transfer (simp add: map_upd_def)

lemma fmap_apply_eqvt[eqvt]:
  shows "(p \<bullet> (f $$ b)) = (p \<bullet> f) $$ (p \<bullet> b)"
  by transfer simp

lemma fresh_fmempty[simp]:
  shows "a \<sharp> {$$}"
  unfolding fresh_def supp_def
  by transfer simp

lemma fresh_fmap_update:
  shows "\<lbrakk>a \<sharp> f; a \<sharp> x; a \<sharp> y\<rbrakk> \<Longrightarrow> a \<sharp> f(x $$:= y)"
  unfolding fresh_conv_MOST
  by (elim MOST_rev_mp) simp

lemma supp_fmempty[simp]:
  shows "supp {$$} = {}"
  by (simp add: supp_def)

lemma supp_fmap_update:
  shows "supp (f(x $$:= y)) \<subseteq> supp(f, x, y)"
  using fresh_fmap_update
  by (auto simp: fresh_def supp_Pair)

instance fmap :: (fs, fs) fs
proof
  fix x :: "('a, 'b) fmap"
  show "finite (supp x)"
    by (induct x rule: fmap_induct)
      (simp_all add: supp_Pair finite_supp finite_subset[OF supp_fmap_update])
qed

lemma fresh_transfer[transfer_rule]:
  "((=) ===> pcr_fmap (=) (=) ===> (=)) fresh fresh"
  unfolding fresh_def supp_def rel_fun_def pcr_fmap_def cr_fmap_def simp_thms
    option.rel_eq fun_eq_iff[symmetric]
  by (auto elim!: finite_subset[rotated] simp: fmap_ext)

lemma fmmap_eqvt[eqvt]: "p \<bullet> (fmmap f F) = fmmap (p \<bullet> f) (p \<bullet> F)"
  by (induct F arbitrary: f rule: fmap_induct) (auto simp add: fmap_update_eqvt fmmap_fmupd)

lemma fmap_freshness_lemma:
  fixes h :: "('a::at,'b::pt) fmap"
  assumes a: "\<exists>a. atom a \<sharp> (h, h $$ a)"
  shows  "\<exists>x. \<forall>a. atom a \<sharp> h \<longrightarrow> h $$ a = x"
  using assms unfolding fresh_Pair
  by transfer (simp add: fresh_Pair freshness_lemma)

lemma fmap_freshness_lemma_unique:
  fixes h :: "('a::at,'b::pt) fmap"
  assumes "\<exists>a. atom a \<sharp> (h, h $$ a)"
  shows "\<exists>!x. \<forall>a. atom a \<sharp> h \<longrightarrow> h $$ a = x"
  using assms unfolding fresh_Pair
  by transfer (rule freshness_lemma_unique, auto simp: fresh_Pair)

lemma fmdrop_fset_fmupd[simp]:
  "(fmdrop_fset A f)(x $$:= y) = fmdrop_fset (A |-| {|x|}) f(x $$:= y)"
  including fmap.lifting fset.lifting
  by transfer (auto simp: map_drop_set_def map_upd_def map_filter_def)

lemma fresh_fset_fminus:
  assumes "atom x \<sharp> A"
  shows   "A |-| {|x|} = A"
  using assms by (induct A) (simp_all add: finsert_fminus_if fresh_finsert)

lemma fresh_fun_app:
  shows "atom x \<sharp> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> F y = Some a \<Longrightarrow> atom x \<sharp> a"
  using supp_fun_app[of F y]
  by (auto simp: fresh_def supp_Some atom_not_fresh_eq)

lemma fresh_fmap_fresh_Some:
  "atom x \<sharp> F \<Longrightarrow> x \<noteq> y \<Longrightarrow> F $$ y = Some a \<Longrightarrow> atom x \<sharp> a"
  including fmap.lifting
  by (transfer) (auto elim: fresh_fun_app)

lemma fmdrop_eqvt: "p \<bullet> fmdrop x F = fmdrop (p \<bullet> x) (p \<bullet> F)"
  by transfer (auto simp: map_drop_def map_filter_def)

lemma fmfilter_eqvt: "p \<bullet> fmfilter Q F = fmfilter (p \<bullet> Q) (p \<bullet> F)"
  by transfer (auto simp: map_filter_def)

lemma fmdrop_eq_iff:
  "fmdrop x B = fmdrop y B \<longleftrightarrow> x = y \<or> (x \<notin> fmdom' B \<and> y \<notin> fmdom' B)"
  by transfer (auto simp: map_drop_def map_filter_def fun_eq_iff, metis)

lemma fresh_fun_upd:
  shows "\<lbrakk>a \<sharp> f; a \<sharp> x; a \<sharp> y\<rbrakk> \<Longrightarrow> a \<sharp> f(x := y)"
  unfolding fresh_conv_MOST by (elim MOST_rev_mp) simp

lemma supp_fun_upd:
  shows "supp (f(x := y)) \<subseteq> supp(f, x, y)"
  using fresh_fun_upd by (auto simp: fresh_def supp_Pair)

lemma map_drop_fun_upd: "map_drop x F = F(x := None)"
  unfolding map_drop_def map_filter_def by auto

lemma fresh_fmdrop_in_fmdom: "\<lbrakk> x \<in> fmdom' B; y \<sharp> B; y \<sharp> x \<rbrakk> \<Longrightarrow> y \<sharp> fmdrop x B"
  by transfer (auto simp: map_drop_fun_upd fresh_None intro!: fresh_fun_upd)

lemma fresh_fmdrop:
  assumes "x \<sharp> B" "x \<sharp> y"
  shows   "x \<sharp> fmdrop y B"
  using assms by (cases "y \<in> fmdom' B") (auto dest!: fresh_fmdrop_in_fmdom simp: fmdrop_idle')

lemma fresh_fmdrop_fset:
  fixes x :: atom and A :: "(_ :: at_base) fset"
  assumes "x \<sharp> A" "x \<sharp> B"
  shows   "x \<sharp> fmdrop_fset A B"
  using assms(1) by (induct A) (auto simp: fresh_fmdrop assms(2) fresh_finsert)

(*<*)
end
(*>*)