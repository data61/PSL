theory Nominal2_Abs
imports Nominal2_Base
        "HOL-Library.Quotient_List"
        "HOL-Library.Quotient_Product"
begin


section \<open>Abstractions\<close>

fun
  alpha_set
where
  alpha_set[simp del]:
  "alpha_set (bs, x) R f p (cs, y) \<longleftrightarrow>
     f x - bs = f y - cs \<and>
     (f x - bs) \<sharp>* p \<and>
     R (p \<bullet> x) y \<and>
     p \<bullet> bs = cs"

fun
  alpha_res
where
  alpha_res[simp del]:
  "alpha_res (bs, x) R f p (cs, y) \<longleftrightarrow>
     f x - bs = f y - cs \<and>
     (f x - bs) \<sharp>* p \<and>
     R (p \<bullet> x) y"

fun
  alpha_lst
where
  alpha_lst[simp del]:
  "alpha_lst (bs, x) R f p (cs, y) \<longleftrightarrow>
     f x - set bs = f y - set cs \<and>
     (f x - set bs) \<sharp>* p \<and>
     R (p \<bullet> x) y \<and>
     p \<bullet> bs = cs"

lemmas alphas = alpha_set.simps alpha_res.simps alpha_lst.simps

notation
  alpha_set ("_ \<approx>set _ _ _ _" [100, 100, 100, 100, 100] 100) and
  alpha_res ("_ \<approx>res _ _ _ _" [100, 100, 100, 100, 100] 100) and
  alpha_lst ("_ \<approx>lst _ _ _ _" [100, 100, 100, 100, 100] 100)

section \<open>Mono\<close>

lemma [mono]:
  shows "R1 \<le> R2 \<Longrightarrow> alpha_set bs R1 \<le> alpha_set bs R2"
  and   "R1 \<le> R2 \<Longrightarrow> alpha_res bs R1 \<le> alpha_res bs R2"
  and   "R1 \<le> R2 \<Longrightarrow> alpha_lst cs R1 \<le> alpha_lst cs R2"
  by (case_tac [!] bs, case_tac [!] cs)
     (auto simp: le_fun_def le_bool_def alphas)

section \<open>Equivariance\<close>

lemma alpha_eqvt[eqvt]:
  shows "(bs, x) \<approx>set R f q (cs, y) \<Longrightarrow> (p \<bullet> bs, p \<bullet> x) \<approx>set (p \<bullet> R) (p \<bullet> f) (p \<bullet> q) (p \<bullet> cs, p \<bullet> y)"
  and   "(bs, x) \<approx>res R f q (cs, y) \<Longrightarrow> (p \<bullet> bs, p \<bullet> x) \<approx>res (p \<bullet> R) (p \<bullet> f) (p \<bullet> q) (p \<bullet> cs, p \<bullet> y)"
  and   "(ds, x) \<approx>lst R f q (es, y) \<Longrightarrow> (p \<bullet> ds, p \<bullet> x) \<approx>lst (p \<bullet> R) (p \<bullet> f) (p \<bullet> q) (p \<bullet> es, p \<bullet> y)"
  unfolding alphas
  unfolding permute_eqvt[symmetric]
  unfolding set_eqvt[symmetric]
  unfolding permute_fun_app_eq[symmetric]
  unfolding Diff_eqvt[symmetric]
  unfolding eq_eqvt[symmetric]
  unfolding fresh_star_eqvt[symmetric]
  by (auto simp only: permute_bool_def)

section \<open>Equivalence\<close>

lemma alpha_refl:
  assumes a: "R x x"
  shows "(bs, x) \<approx>set R f 0 (bs, x)"
  and   "(bs, x) \<approx>res R f 0 (bs, x)"
  and   "(cs, x) \<approx>lst R f 0 (cs, x)"
  using a
  unfolding alphas
  unfolding fresh_star_def
  by (simp_all add: fresh_zero_perm)

lemma alpha_sym:
  assumes a: "R (p \<bullet> x) y \<Longrightarrow> R (- p \<bullet> y) x"
  shows "(bs, x) \<approx>set R f p (cs, y) \<Longrightarrow> (cs, y) \<approx>set R f (- p) (bs, x)"
  and   "(bs, x) \<approx>res R f p (cs, y) \<Longrightarrow> (cs, y) \<approx>res R f (- p) (bs, x)"
  and   "(ds, x) \<approx>lst R f p (es, y) \<Longrightarrow> (es, y) \<approx>lst R f (- p) (ds, x)"
  unfolding alphas fresh_star_def
  using a
  by (auto simp: fresh_minus_perm)

lemma alpha_trans:
  assumes a: "\<lbrakk>R (p \<bullet> x) y; R (q \<bullet> y) z\<rbrakk> \<Longrightarrow> R ((q + p) \<bullet> x) z"
  shows "\<lbrakk>(bs, x) \<approx>set R f p (cs, y); (cs, y) \<approx>set R f q (ds, z)\<rbrakk> \<Longrightarrow> (bs, x) \<approx>set R f (q + p) (ds, z)"
  and   "\<lbrakk>(bs, x) \<approx>res R f p (cs, y); (cs, y) \<approx>res R f q (ds, z)\<rbrakk> \<Longrightarrow> (bs, x) \<approx>res R f (q + p) (ds, z)"
  and   "\<lbrakk>(es, x) \<approx>lst R f p (gs, y); (gs, y) \<approx>lst R f q (hs, z)\<rbrakk> \<Longrightarrow> (es, x) \<approx>lst R f (q + p) (hs, z)"
  using a
  unfolding alphas fresh_star_def
  by (simp_all add: fresh_plus_perm)

lemma alpha_sym_eqvt:
  assumes a: "R (p \<bullet> x) y \<Longrightarrow> R y (p \<bullet> x)"
  and     b: "p \<bullet> R = R"
  shows "(bs, x) \<approx>set R f p (cs, y) \<Longrightarrow> (cs, y) \<approx>set R f (- p) (bs, x)"
  and   "(bs, x) \<approx>res R f p (cs, y) \<Longrightarrow> (cs, y) \<approx>res R f (- p) (bs, x)"
  and   "(ds, x) \<approx>lst R f p (es, y) \<Longrightarrow> (es, y) \<approx>lst R f (- p) (ds, x)"
apply(auto intro!: alpha_sym)
apply(drule_tac [!] a)
apply(rule_tac [!] p="p" in permute_boolE)
apply(simp_all add: b permute_self)
done

lemma alpha_set_trans_eqvt:
  assumes b: "(cs, y) \<approx>set R f q (ds, z)"
  and     a: "(bs, x) \<approx>set R f p (cs, y)"
  and     d: "q \<bullet> R = R"
  and     c: "\<lbrakk>R (p \<bullet> x) y; R y (- q \<bullet> z)\<rbrakk> \<Longrightarrow> R (p \<bullet> x) (- q \<bullet> z)"
  shows "(bs, x) \<approx>set R f (q + p) (ds, z)"
apply(rule alpha_trans(1)[OF _ a b])
apply(drule c)
apply(rule_tac p="q" in permute_boolE)
apply(simp add: d permute_self)
apply(rotate_tac -1)
apply(drule_tac p="q" in permute_boolI)
apply(simp add: d permute_self permute_eqvt[symmetric])
done

lemma alpha_res_trans_eqvt:
  assumes  b: "(cs, y) \<approx>res R f q (ds, z)"
  and     a: "(bs, x) \<approx>res R f p (cs, y)"
  and     d: "q \<bullet> R = R"
  and     c: "\<lbrakk>R (p \<bullet> x) y; R y (- q \<bullet> z)\<rbrakk> \<Longrightarrow> R (p \<bullet> x) (- q \<bullet> z)"
  shows "(bs, x) \<approx>res R f (q + p) (ds, z)"
apply(rule alpha_trans(2)[OF _ a b])
apply(drule c)
apply(rule_tac p="q" in permute_boolE)
apply(simp add: d permute_self)
apply(rotate_tac -1)
apply(drule_tac p="q" in permute_boolI)
apply(simp add: d permute_self permute_eqvt[symmetric])
done

lemma alpha_lst_trans_eqvt:
  assumes b: "(cs, y) \<approx>lst R f q (ds, z)"
  and     a: "(bs, x) \<approx>lst R f p (cs, y)"
  and     d: "q \<bullet> R = R"
  and     c: "\<lbrakk>R (p \<bullet> x) y; R y (- q \<bullet> z)\<rbrakk> \<Longrightarrow> R (p \<bullet> x) (- q \<bullet> z)"
  shows "(bs, x) \<approx>lst R f (q + p) (ds, z)"
apply(rule alpha_trans(3)[OF _ a b])
apply(drule c)
apply(rule_tac p="q" in permute_boolE)
apply(simp add: d permute_self)
apply(rotate_tac -1)
apply(drule_tac p="q" in permute_boolI)
apply(simp add: d permute_self permute_eqvt[symmetric])
done

lemmas alpha_trans_eqvt = alpha_set_trans_eqvt alpha_res_trans_eqvt alpha_lst_trans_eqvt


section \<open>General Abstractions\<close>

fun
  alpha_abs_set
where
  [simp del]:
  "alpha_abs_set (bs, x) (cs, y) \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>set ((=)) supp p (cs, y))"

fun
  alpha_abs_lst
where
  [simp del]:
  "alpha_abs_lst (bs, x) (cs, y) \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>lst ((=)) supp p (cs, y))"

fun
  alpha_abs_res
where
  [simp del]:
  "alpha_abs_res (bs, x) (cs, y) \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>res ((=)) supp p (cs, y))"

notation
  alpha_abs_set (infix "\<approx>abs'_set" 50) and
  alpha_abs_lst (infix "\<approx>abs'_lst" 50) and
  alpha_abs_res (infix "\<approx>abs'_res" 50)

lemmas alphas_abs = alpha_abs_set.simps alpha_abs_res.simps alpha_abs_lst.simps


lemma alphas_abs_refl:
  shows "(bs, x) \<approx>abs_set (bs, x)"
  and   "(bs, x) \<approx>abs_res (bs, x)"
  and   "(cs, x) \<approx>abs_lst (cs, x)"
  unfolding alphas_abs
  unfolding alphas
  unfolding fresh_star_def
  by (rule_tac [!] x="0" in exI)
     (simp_all add: fresh_zero_perm)

lemma alphas_abs_sym:
  shows "(bs, x) \<approx>abs_set (cs, y) \<Longrightarrow> (cs, y) \<approx>abs_set (bs, x)"
  and   "(bs, x) \<approx>abs_res (cs, y) \<Longrightarrow> (cs, y) \<approx>abs_res (bs, x)"
  and   "(ds, x) \<approx>abs_lst (es, y) \<Longrightarrow> (es, y) \<approx>abs_lst (ds, x)"
  unfolding alphas_abs
  unfolding alphas
  unfolding fresh_star_def
  by (erule_tac [!] exE, rule_tac [!] x="-p" in exI)
     (auto simp: fresh_minus_perm)

lemma alphas_abs_trans:
  shows "\<lbrakk>(bs, x) \<approx>abs_set (cs, y); (cs, y) \<approx>abs_set (ds, z)\<rbrakk> \<Longrightarrow> (bs, x) \<approx>abs_set (ds, z)"
  and   "\<lbrakk>(bs, x) \<approx>abs_res (cs, y); (cs, y) \<approx>abs_res (ds, z)\<rbrakk> \<Longrightarrow> (bs, x) \<approx>abs_res (ds, z)"
  and   "\<lbrakk>(es, x) \<approx>abs_lst (gs, y); (gs, y) \<approx>abs_lst (hs, z)\<rbrakk> \<Longrightarrow> (es, x) \<approx>abs_lst (hs, z)"
  unfolding alphas_abs
  unfolding alphas
  unfolding fresh_star_def
  apply(erule_tac [!] exE, erule_tac [!] exE)
  apply(rule_tac [!] x="pa + p" in exI)
  by (simp_all add: fresh_plus_perm)

lemma alphas_abs_eqvt:
  shows "(bs, x) \<approx>abs_set (cs, y) \<Longrightarrow> (p \<bullet> bs, p \<bullet> x) \<approx>abs_set (p \<bullet> cs, p \<bullet> y)"
  and   "(bs, x) \<approx>abs_res (cs, y) \<Longrightarrow> (p \<bullet> bs, p \<bullet> x) \<approx>abs_res (p \<bullet> cs, p \<bullet> y)"
  and   "(ds, x) \<approx>abs_lst (es, y) \<Longrightarrow> (p \<bullet> ds, p \<bullet> x) \<approx>abs_lst (p \<bullet> es, p \<bullet> y)"
  unfolding alphas_abs
  unfolding alphas
  unfolding set_eqvt[symmetric]
  unfolding supp_eqvt[symmetric]
  unfolding Diff_eqvt[symmetric]
  apply(erule_tac [!] exE)
  apply(rule_tac [!] x="p \<bullet> pa" in exI)
  by (auto simp only: fresh_star_permute_iff permute_eqvt[symmetric])


section \<open>Strengthening the equivalence\<close>

lemma disjoint_right_eq:
  assumes a: "A \<union> B1 = A \<union> B2"
  and     b: "A \<inter> B1 = {}" "A \<inter> B2 = {}"
  shows "B1 = B2"
using a b
by (metis Int_Un_distrib2 Int_absorb2 Int_commute Un_upper2)

lemma supp_property_res:
  assumes a: "(as, x) \<approx>res (=) supp p (as', x')"
  shows "p \<bullet> (supp x \<inter> as) = supp x' \<inter> as'"
proof -
  from a have "(supp x - as) \<sharp>* p" by  (auto simp only: alphas)
  then have *: "p \<bullet> (supp x - as) = (supp x - as)"
    by (simp add: atom_set_perm_eq)
  have "(supp x' - as') \<union> (supp x' \<inter> as') = supp x'" by auto
  also have "\<dots> = supp (p \<bullet> x)" using a by (simp add: alphas)
  also have "\<dots> = p \<bullet> (supp x)" by (simp add: supp_eqvt)
  also have "\<dots> = p \<bullet> ((supp x - as) \<union> (supp x \<inter> as))" by auto
  also have "\<dots> = (p \<bullet> (supp x - as)) \<union> (p \<bullet> (supp x \<inter> as))" by (simp add: union_eqvt)
  also have "\<dots> = (supp x - as) \<union> (p \<bullet> (supp x \<inter> as))" using * by simp
  also have "\<dots> = (supp x' - as') \<union> (p \<bullet> (supp x \<inter> as))" using a by (simp add: alphas)
  finally have "(supp x' - as') \<union> (supp x' \<inter> as') = (supp x' - as') \<union> (p \<bullet> (supp x \<inter> as))" .
  moreover
  have "(supp x' - as') \<inter> (supp x' \<inter> as') = {}" by auto
  moreover
  have "(supp x - as) \<inter> (supp x \<inter> as) = {}" by auto
  then have "p \<bullet> ((supp x - as) \<inter> (supp x \<inter> as) = {})" by (simp add: permute_bool_def)
  then have "(p \<bullet> (supp x - as)) \<inter> (p \<bullet> (supp x \<inter> as)) = {}" by (perm_simp) (simp)
  then have "(supp x - as) \<inter> (p \<bullet> (supp x \<inter> as)) = {}" using * by simp
  then have "(supp x' - as') \<inter> (p \<bullet> (supp x \<inter> as)) = {}" using a by (simp add: alphas)
  ultimately show "p \<bullet> (supp x \<inter> as) = supp x' \<inter> as'"
    by (auto dest: disjoint_right_eq)
qed

lemma alpha_abs_res_stronger1_aux:
  assumes asm: "(as, x) \<approx>res (=) supp p' (as', x')"
  shows "\<exists>p. (as, x) \<approx>res (=) supp p (as', x') \<and> supp p \<subseteq> (supp x \<inter> as) \<union> (supp x' \<inter> as')"
proof -
  from asm have 0: "(supp x - as) \<sharp>* p'" by  (auto simp only: alphas)
  then have #: "p' \<bullet> (supp x - as) = (supp x - as)"
    by (simp add: atom_set_perm_eq)
  obtain p where *: "\<forall>b \<in> supp x. p \<bullet> b = p' \<bullet> b" and **: "supp p \<subseteq> supp x \<union> p' \<bullet> supp x"
    using set_renaming_perm2 by blast
  from * have a: "p \<bullet> x = p' \<bullet> x" using supp_perm_perm_eq by auto
  from 0 have 1: "(supp x - as) \<sharp>* p" using *
    by (auto simp: fresh_star_def fresh_perm)
  then have 2: "(supp x - as) \<inter> supp p = {}"
    by (auto simp: fresh_star_def fresh_def)
  have b: "supp x = (supp x - as) \<union> (supp x \<inter> as)" by auto
  have "supp p \<subseteq> supp x \<union> p' \<bullet> supp x" using ** by simp
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> (p' \<bullet> ((supp x - as) \<union> (supp x \<inter> as)))"
    using b by simp
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> ((p' \<bullet> (supp x - as)) \<union> (p' \<bullet> (supp x \<inter> as)))"
    by (simp add: union_eqvt)
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> (p' \<bullet> (supp x \<inter> as))"
    using # by auto
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> (supp x' \<inter> as')" using asm
    by (simp add: supp_property_res)
  finally have "supp p \<subseteq> (supp x - as) \<union> (supp x \<inter> as) \<union> (supp x' \<inter> as')" .
  then
  have "supp p \<subseteq> (supp x \<inter> as) \<union> (supp x' \<inter> as')" using 2 by auto
  moreover
  have "(as, x) \<approx>res (=) supp p (as', x')" using asm 1 a by (simp add: alphas)
  ultimately
  show "\<exists>p. (as, x) \<approx>res (=) supp p (as', x') \<and> supp p \<subseteq> (supp x \<inter> as) \<union> (supp x' \<inter> as')" by blast
qed

lemma alpha_abs_res_minimal:
  assumes asm: "(as, x) \<approx>res (=) supp p (as', x')"
  shows "(as \<inter> supp x, x) \<approx>res (=) supp p (as' \<inter> supp x', x')"
  using asm unfolding alpha_res by (auto simp: Diff_Int)

lemma alpha_abs_res_abs_set:
  assumes asm: "(as, x) \<approx>res (=) supp p (as', x')"
  shows "(as \<inter> supp x, x) \<approx>set (=) supp p (as' \<inter> supp x', x')"
proof -
  have c: "p \<bullet> x = x'"
    using alpha_abs_res_minimal[OF asm] unfolding alpha_res by clarify
  then have a: "supp x - as \<inter> supp x = supp (p \<bullet> x) - as' \<inter> supp (p \<bullet> x)"
    using alpha_abs_res_minimal[OF asm] by (simp add: alpha_res)
  have b: "(supp x - as \<inter> supp x) \<sharp>* p"
    using alpha_abs_res_minimal[OF asm] unfolding alpha_res by clarify
  have "p \<bullet> (as \<inter> supp x) = as' \<inter> supp (p \<bullet> x)"
    by (metis Int_commute asm c supp_property_res)
  then show ?thesis using a b c unfolding alpha_set by simp
qed

lemma alpha_abs_set_abs_res:
  assumes asm: "(as \<inter> supp x, x) \<approx>set (=) supp p (as' \<inter> supp x', x')"
  shows "(as, x) \<approx>res (=) supp p (as', x')"
  using asm unfolding alphas by (auto simp: Diff_Int)

lemma alpha_abs_res_stronger1:
  assumes asm: "(as, x) \<approx>res (=) supp p' (as', x')"
  shows "\<exists>p. (as, x) \<approx>res (=) supp p (as', x') \<and> supp p \<subseteq> as \<union> as'"
using alpha_abs_res_stronger1_aux[OF asm] by auto

lemma alpha_abs_set_stronger1:
  assumes asm: "(as, x) \<approx>set (=) supp p' (as', x')"
  shows "\<exists>p. (as, x) \<approx>set (=) supp p (as', x') \<and> supp p \<subseteq> as \<union> as'"
proof -
  from asm have 0: "(supp x - as) \<sharp>* p'" by  (auto simp only: alphas)
  then have #: "p' \<bullet> (supp x - as) = (supp x - as)"
    by (simp add: atom_set_perm_eq)
  obtain p where *: "\<forall>b \<in> (supp x \<union> as). p \<bullet> b = p' \<bullet> b"
    and **: "supp p \<subseteq> (supp x \<union> as) \<union> p' \<bullet> (supp x \<union> as)"
    using set_renaming_perm2 by blast
  from * have "\<forall>b \<in> supp x. p \<bullet> b = p' \<bullet> b" by blast
  then have a: "p \<bullet> x = p' \<bullet> x" using supp_perm_perm_eq by auto
  from * have "\<forall>b \<in> as. p \<bullet> b = p' \<bullet> b" by blast
  then have zb: "p \<bullet> as = p' \<bullet> as"
    apply(auto simp: permute_set_def)
    apply(rule_tac x="xa" in exI)
    apply(simp)
    done
  have zc: "p' \<bullet> as = as'" using asm by (simp add: alphas)
  from 0 have 1: "(supp x - as) \<sharp>* p" using *
    by (auto simp: fresh_star_def fresh_perm)
  then have 2: "(supp x - as) \<inter> supp p = {}"
    by (auto simp: fresh_star_def fresh_def)
  have b: "supp x = (supp x - as) \<union> (supp x \<inter> as)" by auto
  have "supp p \<subseteq> supp x \<union> as \<union> p' \<bullet> supp x \<union> p' \<bullet> as" using ** using union_eqvt by blast
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> as \<union> (p' \<bullet> ((supp x - as) \<union> (supp x \<inter> as))) \<union> p' \<bullet> as"
    using b by simp
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> as \<union>
    ((p' \<bullet> (supp x - as)) \<union> (p' \<bullet> (supp x \<inter> as))) \<union> p' \<bullet> as" by (simp add: union_eqvt)
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> as \<union> (p' \<bullet> (supp x \<inter> as)) \<union> p' \<bullet> as"
    using # by auto
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> as \<union> p' \<bullet> ((supp x \<inter> as) \<union> as)" using union_eqvt
    by auto
  also have "\<dots> = (supp x - as) \<union> (supp x \<inter> as) \<union> as \<union> p' \<bullet> as"
    by (metis Int_commute Un_commute sup_inf_absorb)
  also have "\<dots> = (supp x - as) \<union> as \<union> p' \<bullet> as" by blast
  finally have "supp p \<subseteq> (supp x - as) \<union> as \<union> p' \<bullet> as" .
  then have "supp p \<subseteq> as \<union> p' \<bullet> as" using 2 by blast
  moreover
  have "(as, x) \<approx>set (=) supp p (as', x')" using asm 1 a zb by (simp add: alphas)
  ultimately
  show "\<exists>p. (as, x) \<approx>set (=) supp p (as', x') \<and> supp p \<subseteq> as \<union> as'" using zc by blast
qed

lemma alpha_abs_lst_stronger1:
  assumes asm: "(as, x) \<approx>lst (=) supp p' (as', x')"
  shows "\<exists>p. (as, x) \<approx>lst (=) supp p (as', x') \<and> supp p \<subseteq> set as \<union> set as'"
proof -
  from asm have 0: "(supp x - set as) \<sharp>* p'" by  (auto simp only: alphas)
  then have #: "p' \<bullet> (supp x - set as) = (supp x - set as)"
    by (simp add: atom_set_perm_eq)
  obtain p where *: "\<forall>b \<in> (supp x \<union> set as). p \<bullet> b = p' \<bullet> b"
    and **: "supp p \<subseteq> (supp x \<union> set as) \<union> p' \<bullet> (supp x \<union> set as)"
    using set_renaming_perm2 by blast
  from * have "\<forall>b \<in> supp x. p \<bullet> b = p' \<bullet> b" by blast
  then have a: "p \<bullet> x = p' \<bullet> x" using supp_perm_perm_eq by auto
  from * have "\<forall>b \<in> set as. p \<bullet> b = p' \<bullet> b" by blast
  then have zb: "p \<bullet> as = p' \<bullet> as" by (induct as) (auto)
  have zc: "p' \<bullet> set as = set as'" using asm by (simp add: alphas set_eqvt)
  from 0 have 1: "(supp x - set as) \<sharp>* p" using *
    by (auto simp: fresh_star_def fresh_perm)
  then have 2: "(supp x - set as) \<inter> supp p = {}"
    by (auto simp: fresh_star_def fresh_def)
  have b: "supp x = (supp x - set as) \<union> (supp x \<inter> set as)" by auto
  have "supp p \<subseteq> supp x \<union> set as \<union> p' \<bullet> supp x \<union> p' \<bullet> set as" using ** using union_eqvt by blast
  also have "\<dots> = (supp x - set as) \<union> (supp x \<inter> set as) \<union> set as \<union>
    (p' \<bullet> ((supp x - set as) \<union> (supp x \<inter> set as))) \<union> p' \<bullet> set as" using b by simp
  also have "\<dots> = (supp x - set as) \<union> (supp x \<inter> set as) \<union> set as \<union>
    ((p' \<bullet> (supp x - set as)) \<union> (p' \<bullet> (supp x \<inter> set as))) \<union> p' \<bullet> set as" by (simp add: union_eqvt)
  also have "\<dots> = (supp x - set as) \<union> (supp x \<inter> set as) \<union> set as \<union>
    (p' \<bullet> (supp x \<inter> set as)) \<union> p' \<bullet> set as" using # by auto
  also have "\<dots> = (supp x - set as) \<union> (supp x \<inter> set as) \<union> set as \<union> p' \<bullet> ((supp x \<inter> set as) \<union> set as)"
    using union_eqvt by auto
  also have "\<dots> = (supp x - set as) \<union> (supp x \<inter> set as) \<union> set as \<union> p' \<bullet> set as"
    by (metis Int_commute Un_commute sup_inf_absorb)
  also have "\<dots> = (supp x - set as) \<union> set as \<union> p' \<bullet> set as" by blast
  finally have "supp p \<subseteq> (supp x - set as) \<union> set as \<union> p' \<bullet> set as" .
  then have "supp p \<subseteq> set as \<union> p' \<bullet> set as" using 2 by blast
  moreover
  have "(as, x) \<approx>lst (=) supp p (as', x')" using asm 1 a zb by (simp add: alphas)
  ultimately
  show "\<exists>p. (as, x) \<approx>lst (=) supp p (as', x') \<and> supp p \<subseteq> set as \<union> set as'" using zc by blast
qed

lemma alphas_abs_stronger:
  shows "(as, x) \<approx>abs_set (as', x') \<longleftrightarrow> (\<exists>p. (as, x) \<approx>set (=) supp p (as', x') \<and> supp p \<subseteq> as \<union> as')"
  and   "(as, x) \<approx>abs_res (as', x') \<longleftrightarrow> (\<exists>p. (as, x) \<approx>res (=) supp p (as', x') \<and> supp p \<subseteq> as \<union> as')"
  and   "(bs, x) \<approx>abs_lst (bs', x') \<longleftrightarrow>
   (\<exists>p. (bs, x) \<approx>lst (=) supp p (bs', x') \<and> supp p \<subseteq> set bs \<union> set bs')"
apply(rule iffI)
apply(auto simp: alphas_abs alpha_abs_set_stronger1)[1]
apply(auto simp: alphas_abs)[1]
apply(rule iffI)
apply(auto simp: alphas_abs alpha_abs_res_stronger1)[1]
apply(auto simp: alphas_abs)[1]
apply(rule iffI)
apply(auto simp: alphas_abs alpha_abs_lst_stronger1)[1]
apply(auto simp: alphas_abs)[1]
done

lemma alpha_res_alpha_set:
  "(bs, x) \<approx>res (=) supp p (cs, y) \<longleftrightarrow> (bs \<inter> supp x, x) \<approx>set (=) supp p (cs \<inter> supp y, y)"
  using alpha_abs_set_abs_res alpha_abs_res_abs_set by blast

section \<open>Quotient types\<close>

quotient_type
    'a abs_set = "(atom set \<times> 'a::pt)" / "alpha_abs_set"
  apply(rule equivpI)
  unfolding reflp_def refl_on_def symp_def sym_def transp_def trans_def
  by (auto intro: alphas_abs_sym alphas_abs_refl alphas_abs_trans simp only:)

quotient_type
    'b abs_res = "(atom set \<times> 'b::pt)" / "alpha_abs_res"
  apply(rule equivpI)
  unfolding reflp_def refl_on_def symp_def sym_def transp_def trans_def
  by (auto intro: alphas_abs_sym alphas_abs_refl alphas_abs_trans simp only:)

quotient_type
   'c abs_lst = "(atom list \<times> 'c::pt)" / "alpha_abs_lst"
  apply(rule_tac [!] equivpI)
  unfolding reflp_def refl_on_def symp_def sym_def transp_def trans_def
  by (auto intro: alphas_abs_sym alphas_abs_refl alphas_abs_trans simp only:)

quotient_definition
  Abs_set ("[_]set. _" [60, 60] 60)
where
  "Abs_set::atom set \<Rightarrow> ('a::pt) \<Rightarrow> 'a abs_set"
is
  "Pair::atom set \<Rightarrow> ('a::pt) \<Rightarrow> (atom set \<times> 'a)" .

quotient_definition
  Abs_res ("[_]res. _" [60, 60] 60)
where
  "Abs_res::atom set \<Rightarrow> ('a::pt) \<Rightarrow> 'a abs_res"
is
  "Pair::atom set \<Rightarrow> ('a::pt) \<Rightarrow> (atom set \<times> 'a)" .

quotient_definition
  Abs_lst ("[_]lst. _" [60, 60] 60)
where
  "Abs_lst::atom list \<Rightarrow> ('a::pt) \<Rightarrow> 'a abs_lst"
is
  "Pair::atom list \<Rightarrow> ('a::pt) \<Rightarrow> (atom list \<times> 'a)" .

lemma [quot_respect]:
  shows "((=) ===> (=) ===> alpha_abs_set) Pair Pair"
  and   "((=) ===> (=) ===> alpha_abs_res) Pair Pair"
  and   "((=) ===> (=) ===> alpha_abs_lst) Pair Pair"
  unfolding rel_fun_def
  by (auto intro: alphas_abs_refl)

lemma [quot_respect]:
  shows "((=) ===> alpha_abs_set ===> alpha_abs_set) permute permute"
  and   "((=) ===> alpha_abs_res ===> alpha_abs_res) permute permute"
  and   "((=) ===> alpha_abs_lst ===> alpha_abs_lst) permute permute"
  unfolding rel_fun_def
  by (auto intro: alphas_abs_eqvt simp only: Pair_eqvt)

lemma Abs_eq_iff:
  shows "[bs]set. x = [bs']set. y \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>set (=) supp p (bs', y))"
  and   "[bs]res. x = [bs']res. y \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>res (=) supp p (bs', y))"
  and   "[cs]lst. x = [cs']lst. y \<longleftrightarrow> (\<exists>p. (cs, x) \<approx>lst (=) supp p (cs', y))"
  by (lifting alphas_abs)

lemma Abs_eq_iff2:
  shows "[bs]set. x = [bs']set. y \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>set ((=)) supp p (bs', y) \<and> supp p \<subseteq> bs \<union> bs')"
  and   "[bs]res. x = [bs']res. y \<longleftrightarrow> (\<exists>p. (bs, x) \<approx>res ((=)) supp p (bs', y) \<and> supp p \<subseteq> bs \<union> bs')"
  and   "[cs]lst. x = [cs']lst. y \<longleftrightarrow> (\<exists>p. (cs, x) \<approx>lst ((=)) supp p (cs', y) \<and> supp p \<subseteq> set cs \<union> set cs')"
  by (lifting alphas_abs_stronger)


lemma Abs_eq_res_set:
  shows "[bs]res. x = [cs]res. y \<longleftrightarrow> [bs \<inter> supp x]set. x = [cs \<inter> supp y]set. y"
  unfolding Abs_eq_iff alpha_res_alpha_set by rule

lemma Abs_eq_res_supp:
  assumes asm: "supp x \<subseteq> bs"
  shows "[as]res. x = [as \<inter> bs]res. x"
  unfolding Abs_eq_iff alphas
  apply (rule_tac x="0::perm" in exI)
  apply (simp add: fresh_star_zero)
  using asm by blast

lemma Abs_exhausts[cases type]:
  shows "(\<And>as (x::'a::pt). y1 = [as]set. x \<Longrightarrow> P1) \<Longrightarrow> P1"
  and   "(\<And>as (x::'a::pt). y2 = [as]res. x \<Longrightarrow> P2) \<Longrightarrow> P2"
  and   "(\<And>bs (x::'a::pt). y3 = [bs]lst. x \<Longrightarrow> P3) \<Longrightarrow> P3"
  by (lifting prod.exhaust[where 'a="atom set" and 'b="'a"]
              prod.exhaust[where 'a="atom set" and 'b="'a"]
              prod.exhaust[where 'a="atom list" and 'b="'a"])

instantiation abs_set :: (pt) pt
begin

quotient_definition
  "permute_abs_set::perm \<Rightarrow> ('a::pt abs_set) \<Rightarrow> 'a abs_set"
is
  "permute:: perm \<Rightarrow> (atom set \<times> 'a::pt) \<Rightarrow> (atom set \<times> 'a::pt)"
  by (auto intro: alphas_abs_eqvt simp only: Pair_eqvt)

lemma permute_Abs_set[simp]:
  fixes x::"'a::pt"
  shows "(p \<bullet> ([as]set. x)) = [p \<bullet> as]set. (p \<bullet> x)"
  by (lifting permute_prod.simps[where 'a="atom set" and 'b="'a"])

instance
  apply standard
  apply(case_tac [!] x)
  apply(simp_all)
  done

end

instantiation abs_res :: (pt) pt
begin

quotient_definition
  "permute_abs_res::perm \<Rightarrow> ('a::pt abs_res) \<Rightarrow> 'a abs_res"
is
  "permute:: perm \<Rightarrow> (atom set \<times> 'a::pt) \<Rightarrow> (atom set \<times> 'a::pt)"
  by (auto intro: alphas_abs_eqvt simp only: Pair_eqvt)

lemma permute_Abs_res[simp]:
  fixes x::"'a::pt"
  shows "(p \<bullet> ([as]res. x)) = [p \<bullet> as]res. (p \<bullet> x)"
  by (lifting permute_prod.simps[where 'a="atom set" and 'b="'a"])

instance
  apply standard
  apply(case_tac [!] x)
  apply(simp_all)
  done

end

instantiation abs_lst :: (pt) pt
begin

quotient_definition
  "permute_abs_lst::perm \<Rightarrow> ('a::pt abs_lst) \<Rightarrow> 'a abs_lst"
is
  "permute:: perm \<Rightarrow> (atom list \<times> 'a::pt) \<Rightarrow> (atom list \<times> 'a::pt)"
  by (auto intro: alphas_abs_eqvt simp only: Pair_eqvt)

lemma permute_Abs_lst[simp]:
  fixes x::"'a::pt"
  shows "(p \<bullet> ([as]lst. x)) = [p \<bullet> as]lst. (p \<bullet> x)"
  by (lifting permute_prod.simps[where 'a="atom list" and 'b="'a"])

instance
  apply standard
  apply(case_tac [!] x)
  apply(simp_all)
  done

end

lemmas permute_Abs[eqvt] = permute_Abs_set permute_Abs_res permute_Abs_lst


lemma Abs_swap1:
  assumes a1: "a \<notin> (supp x) - bs"
  and     a2: "b \<notin> (supp x) - bs"
  shows "[bs]set. x = [(a \<rightleftharpoons> b) \<bullet> bs]set. ((a \<rightleftharpoons> b) \<bullet> x)"
  and   "[bs]res. x = [(a \<rightleftharpoons> b) \<bullet> bs]res. ((a \<rightleftharpoons> b) \<bullet> x)"
  unfolding Abs_eq_iff
  unfolding alphas
  unfolding supp_eqvt[symmetric] Diff_eqvt[symmetric]
  unfolding fresh_star_def fresh_def
  unfolding swap_set_not_in[OF a1 a2]
  using a1 a2
  by (rule_tac [!] x="(a \<rightleftharpoons> b)" in exI)
     (auto simp: supp_perm swap_atom)

lemma Abs_swap2:
  assumes a1: "a \<notin> (supp x) - (set bs)"
  and     a2: "b \<notin> (supp x) - (set bs)"
  shows "[bs]lst. x = [(a \<rightleftharpoons> b) \<bullet> bs]lst. ((a \<rightleftharpoons> b) \<bullet> x)"
  unfolding Abs_eq_iff
  unfolding alphas
  unfolding supp_eqvt[symmetric] Diff_eqvt[symmetric] set_eqvt[symmetric]
  unfolding fresh_star_def fresh_def
  unfolding swap_set_not_in[OF a1 a2]
  using a1 a2
  by (rule_tac [!] x="(a \<rightleftharpoons> b)" in exI)
     (auto simp: supp_perm swap_atom)

lemma Abs_supports:
  shows "((supp x) - as) supports ([as]set. x)"
  and   "((supp x) - as) supports ([as]res. x)"
  and   "((supp x) - set bs) supports ([bs]lst. x)"
  unfolding supports_def
  unfolding permute_Abs
  by (simp_all add: Abs_swap1[symmetric] Abs_swap2[symmetric])

function
  supp_set  :: "('a::pt) abs_set \<Rightarrow> atom set" and
  supp_res :: "('a::pt) abs_res \<Rightarrow> atom set" and
  supp_lst :: "('a::pt) abs_lst \<Rightarrow> atom set"
where
  "supp_set ([as]set. x) = supp x - as"
| "supp_res ([as]res. x) = supp x - as"
| "supp_lst (Abs_lst cs x) = (supp x) - (set cs)"
apply(simp_all add: Abs_eq_iff alphas_abs alphas)
apply(case_tac x)
apply(case_tac a)
apply(simp)
apply(case_tac b)
apply(case_tac a)
apply(simp)
apply(case_tac ba)
apply(simp)
done

termination
  by lexicographic_order

lemma supp_funs_eqvt[eqvt]:
  shows "(p \<bullet> supp_set x) = supp_set (p \<bullet> x)"
  and   "(p \<bullet> supp_res y) = supp_res (p \<bullet> y)"
  and   "(p \<bullet> supp_lst z) = supp_lst (p \<bullet> z)"
  apply(case_tac x)
  apply(simp)
  apply(case_tac y)
  apply(simp)
  apply(case_tac z)
  apply(simp)
  done

lemma Abs_fresh_aux:
  shows "a \<sharp> [bs]set. x \<Longrightarrow> a \<sharp> supp_set ([bs]set. x)"
  and   "a \<sharp> [bs]res. x \<Longrightarrow> a \<sharp> supp_res ([bs]res. x)"
  and   "a \<sharp> [cs]lst. x \<Longrightarrow> a \<sharp> supp_lst ([cs]lst. x)"
  by (rule_tac [!] fresh_fun_eqvt_app)
     (auto simp only: eqvt_def eqvts_raw)

lemma Abs_supp_subset1:
  assumes a: "finite (supp x)"
  shows "(supp x) - as \<subseteq> supp ([as]set. x)"
  and   "(supp x) - as \<subseteq> supp ([as]res. x)"
  and   "(supp x) - (set bs) \<subseteq> supp ([bs]lst. x)"
  unfolding supp_conv_fresh
  by (auto dest!: Abs_fresh_aux)
     (simp_all add: fresh_def supp_finite_atom_set a)

lemma Abs_supp_subset2:
  assumes a: "finite (supp x)"
  shows "supp ([as]set. x) \<subseteq> (supp x) - as"
  and   "supp ([as]res. x) \<subseteq> (supp x) - as"
  and   "supp ([bs]lst. x) \<subseteq> (supp x) - (set bs)"
  by (rule_tac [!] supp_is_subset)
     (simp_all add: Abs_supports a)

lemma Abs_finite_supp:
  assumes a: "finite (supp x)"
  shows "supp ([as]set. x) = (supp x) - as"
  and   "supp ([as]res. x) = (supp x) - as"
  and   "supp ([bs]lst. x) = (supp x) - (set bs)"
using Abs_supp_subset1[OF a] Abs_supp_subset2[OF a]
  by blast+

lemma supp_Abs:
  fixes x::"'a::fs"
  shows "supp ([as]set. x) = (supp x) - as"
  and   "supp ([as]res. x) = (supp x) - as"
  and   "supp ([bs]lst. x) = (supp x) - (set bs)"
by (simp_all add: Abs_finite_supp finite_supp)

instance abs_set :: (fs) fs
  apply standard
  apply(case_tac x)
  apply(simp add: supp_Abs finite_supp)
  done

instance abs_res :: (fs) fs
  apply standard
  apply(case_tac x)
  apply(simp add: supp_Abs finite_supp)
  done

instance abs_lst :: (fs) fs
  apply standard
  apply(case_tac x)
  apply(simp add: supp_Abs finite_supp)
  done

lemma Abs_fresh_iff:
  fixes x::"'a::fs"
  shows "a \<sharp> [bs]set. x \<longleftrightarrow> a \<in> bs \<or> (a \<notin> bs \<and> a \<sharp> x)"
  and   "a \<sharp> [bs]res. x \<longleftrightarrow> a \<in> bs \<or> (a \<notin> bs \<and> a \<sharp> x)"
  and   "a \<sharp> [cs]lst. x \<longleftrightarrow> a \<in> (set cs) \<or> (a \<notin> (set cs) \<and> a \<sharp> x)"
  unfolding fresh_def
  unfolding supp_Abs
  by auto

lemma Abs_fresh_star_iff:
  fixes x::"'a::fs"
  shows "as \<sharp>* ([bs]set. x) \<longleftrightarrow> (as - bs) \<sharp>* x"
  and   "as \<sharp>* ([bs]res. x) \<longleftrightarrow> (as - bs) \<sharp>* x"
  and   "as \<sharp>* ([cs]lst. x) \<longleftrightarrow> (as - set cs) \<sharp>* x"
  unfolding fresh_star_def
  by (auto simp: Abs_fresh_iff)

lemma Abs_fresh_star:
  fixes x::"'a::fs"
  shows "as \<subseteq> as' \<Longrightarrow> as \<sharp>* ([as']set. x)"
  and   "as \<subseteq> as' \<Longrightarrow> as \<sharp>* ([as']res. x)"
  and   "bs \<subseteq> set bs' \<Longrightarrow> bs \<sharp>* ([bs']lst. x)"
  unfolding fresh_star_def
  by(auto simp: Abs_fresh_iff)

lemma Abs_fresh_star2:
  fixes x::"'a::fs"
  shows "as \<inter> bs = {} \<Longrightarrow> as \<sharp>* ([bs]set. x) \<longleftrightarrow> as \<sharp>* x"
  and   "as \<inter> bs = {} \<Longrightarrow> as \<sharp>* ([bs]res. x) \<longleftrightarrow> as \<sharp>* x"
  and   "cs \<inter> set ds = {} \<Longrightarrow> cs \<sharp>* ([ds]lst. x) \<longleftrightarrow> cs \<sharp>* x"
  unfolding fresh_star_def Abs_fresh_iff
  by auto


section \<open>Abstractions of single atoms\<close>


lemma Abs1_eq:
  fixes x y::"'a::fs"
  shows "[{atom a}]set. x = [{atom a}]set. y \<longleftrightarrow> x = y"
  and   "[{atom a}]res. x = [{atom a}]res. y \<longleftrightarrow> x = y"
  and   "[[atom a]]lst. x = [[atom a]]lst. y \<longleftrightarrow> x = y"
unfolding Abs_eq_iff2 alphas
by (auto simp: supp_perm_singleton fresh_star_def fresh_zero_perm)

lemma Abs1_eq_iff_fresh:
  fixes x y::"'a::fs"
  and a b c::"'b::at"
  assumes "atom c \<sharp> (a, b, x, y)"
  shows "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
  and   "[{atom a}]res. x = [{atom b}]res. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
  and   "[[atom a]]lst. x = [[atom b]]lst. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
proof -
  have "[{atom a}]set. x = (a \<leftrightarrow> c) \<bullet> ([{atom a}]set. x)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[{atom a}]set. x = [{atom c}]set. ((a \<leftrightarrow> c) \<bullet> x)" by simp
  moreover
  have "[{atom b}]set. y = (b \<leftrightarrow> c) \<bullet> ([{atom b}]set. y)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[{atom b}]set. y = [{atom c}]set. ((b \<leftrightarrow> c) \<bullet> y)" by simp
  ultimately
  show "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
    by (simp add: Abs1_eq)
next
  have "[{atom a}]res. x = (a \<leftrightarrow> c) \<bullet> ([{atom a}]res. x)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[{atom a}]res. x = [{atom c}]res. ((a \<leftrightarrow> c) \<bullet> x)" by simp
  moreover
  have "[{atom b}]res. y = (b \<leftrightarrow> c) \<bullet> ([{atom b}]res. y)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[{atom b}]res. y = [{atom c}]res. ((b \<leftrightarrow> c) \<bullet> y)" by simp
  ultimately
  show "[{atom a}]res. x = [{atom b}]res. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
    by (simp add: Abs1_eq)
next
  have "[[atom a]]lst. x = (a \<leftrightarrow> c) \<bullet> ([[atom a]]lst. x)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[[atom a]]lst. x = [[atom c]]lst. ((a \<leftrightarrow> c) \<bullet> x)" by simp
  moreover
  have "[[atom b]]lst. y = (b \<leftrightarrow> c) \<bullet> ([[atom b]]lst. y)"
    by (rule_tac flip_fresh_fresh[symmetric]) (simp_all add: Abs_fresh_iff assms)
  then have "[[atom b]]lst. y = [[atom c]]lst. ((b \<leftrightarrow> c) \<bullet> y)" by simp
  ultimately
  show "[[atom a]]lst. x = [[atom b]]lst. y \<longleftrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y"
    by (simp add: Abs1_eq)
qed

lemma Abs1_eq_iff_all:
  fixes x y::"'a::fs"
  and z::"'c::fs"
  and a b::"'b::at"
  shows "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (\<forall>c. atom c \<sharp> z \<longrightarrow> atom c \<sharp> (a, b, x, y) \<longrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y)"
  and   "[{atom a}]res. x = [{atom b}]res. y \<longleftrightarrow> (\<forall>c. atom c \<sharp> z \<longrightarrow> atom c \<sharp> (a, b, x, y) \<longrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y)"
  and   "[[atom a]]lst. x = [[atom b]]lst. y \<longleftrightarrow> (\<forall>c. atom c \<sharp> z \<longrightarrow> atom c \<sharp> (a, b, x, y) \<longrightarrow> (a \<leftrightarrow> c) \<bullet> x = (b \<leftrightarrow> c) \<bullet> y)"
apply(auto)
apply(simp add: Abs1_eq_iff_fresh(1)[symmetric])
apply(rule_tac ?'a="'b::at" and x="(a, b, x, y, z)" in obtain_fresh)
apply(drule_tac x="aa" in spec)
apply(simp)
apply(subst Abs1_eq_iff_fresh(1))
apply(auto simp: fresh_Pair)[2]
apply(simp add: Abs1_eq_iff_fresh(2)[symmetric])
apply(rule_tac ?'a="'b::at" and x="(a, b, x, y, z)" in obtain_fresh)
apply(drule_tac x="aa" in spec)
apply(simp)
apply(subst Abs1_eq_iff_fresh(2))
apply(auto simp: fresh_Pair)[2]
apply(simp add: Abs1_eq_iff_fresh(3)[symmetric])
apply(rule_tac ?'a="'b::at" and x="(a, b, x, y, z)" in obtain_fresh)
apply(drule_tac x="aa" in spec)
apply(simp)
apply(subst Abs1_eq_iff_fresh(3))
apply(auto simp: fresh_Pair)[2]
done

lemma Abs1_eq_iff:
  fixes x y::"'a::fs"
  and a b::"'b::at"
  shows "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
  and   "[{atom a}]res. x = [{atom b}]res. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
  and   "[[atom a]]lst. x = [[atom b]]lst. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
proof -
  { assume "a = b"
    then have "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a = b \<and> x = y)" by (simp add: Abs1_eq)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "[{atom a}]set. x = [{atom b}]set. y"
    have #: "atom a \<sharp> [{atom b}]set. y" by (simp add: **[symmetric] Abs_fresh_iff)
    have "[{atom a}]set. ((a \<leftrightarrow> b) \<bullet> y) = (a \<leftrightarrow> b) \<bullet> ([{atom b}]set. y)" by (simp)
    also have "\<dots> = [{atom b}]set. y"
      by (rule flip_fresh_fresh) (simp add: #, simp add: Abs_fresh_iff)
    also have "\<dots> = [{atom a}]set. x" using ** by simp
    finally have "a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y" using # * by (simp add: Abs1_eq Abs_fresh_iff)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y"
    have "[{atom a}]set. x = [{atom a}]set. ((a \<leftrightarrow> b) \<bullet> y)" using ** by simp
    also have "\<dots> = (a \<leftrightarrow> b) \<bullet> ([{atom b}]set. y)" by (simp add: permute_set_def)
    also have "\<dots> = [{atom b}]set. y"
      by (rule flip_fresh_fresh) (simp add: Abs_fresh_iff **, simp add: Abs_fresh_iff)
    finally have "[{atom a}]set. x = [{atom b}]set. y" .
  }
  ultimately
  show "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
    by blast
next
  { assume "a = b"
    then have "Abs_res {atom a} x = Abs_res {atom b} y \<longleftrightarrow> (a = b \<and> x = y)" by (simp add: Abs1_eq)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "Abs_res {atom a} x = Abs_res {atom b} y"
    have #: "atom a \<sharp> Abs_res {atom b} y" by (simp add: **[symmetric] Abs_fresh_iff)
    have "Abs_res {atom a} ((a \<leftrightarrow> b) \<bullet> y) = (a \<leftrightarrow> b) \<bullet> (Abs_res {atom b} y)" by simp
    also have "\<dots> = Abs_res {atom b} y"
      by (rule flip_fresh_fresh) (simp add: #, simp add: Abs_fresh_iff)
    also have "\<dots> = Abs_res {atom a} x" using ** by simp
    finally have "a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y" using # * by (simp add: Abs1_eq Abs_fresh_iff)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y"
    have "Abs_res {atom a} x = Abs_res {atom a} ((a \<leftrightarrow> b) \<bullet> y)" using ** by simp
    also have "\<dots> = (a \<leftrightarrow> b) \<bullet> Abs_res {atom b} y" by (simp add: permute_set_def)
    also have "\<dots> = Abs_res {atom b} y"
      by (rule flip_fresh_fresh) (simp add: Abs_fresh_iff **, simp add: Abs_fresh_iff)
    finally have "Abs_res {atom a} x = Abs_res {atom b} y" .
  }
  ultimately
  show "Abs_res {atom a} x = Abs_res {atom b} y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
    by blast
next
  { assume "a = b"
    then have "Abs_lst [atom a] x = Abs_lst [atom b] y \<longleftrightarrow> (a = b \<and> x = y)" by (simp add: Abs1_eq)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "Abs_lst [atom a] x = Abs_lst [atom b] y"
    have #: "atom a \<sharp> Abs_lst [atom b] y" by (simp add: **[symmetric] Abs_fresh_iff)
    have "Abs_lst [atom a] ((a \<leftrightarrow> b) \<bullet> y) = (a \<leftrightarrow> b) \<bullet> (Abs_lst [atom b] y)" by simp
    also have "\<dots> = Abs_lst [atom b] y"
      by (rule flip_fresh_fresh) (simp add: #, simp add: Abs_fresh_iff)
    also have "\<dots> = Abs_lst [atom a] x" using ** by simp
    finally have "a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y" using # * by (simp add: Abs1_eq Abs_fresh_iff)
  }
  moreover
  { assume *: "a \<noteq> b" and **: "x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y"
    have "Abs_lst [atom a] x = Abs_lst [atom a] ((a \<leftrightarrow> b) \<bullet> y)" using ** by simp
    also have "\<dots> = (a \<leftrightarrow> b) \<bullet> Abs_lst [atom b] y" by simp
    also have "\<dots> = Abs_lst [atom b] y"
      by (rule flip_fresh_fresh) (simp add: Abs_fresh_iff **, simp add: Abs_fresh_iff)
    finally have "Abs_lst [atom a] x = Abs_lst [atom b] y" .
  }
  ultimately
  show "Abs_lst [atom a] x = Abs_lst [atom b] y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> x = (a \<leftrightarrow> b) \<bullet> y \<and> atom a \<sharp> y)"
    by blast
qed

lemma Abs1_eq_iff':
  fixes x::"'a::fs"
  and a b::"'b::at"
  shows "[{atom a}]set. x = [{atom b}]set. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> (b \<leftrightarrow> a) \<bullet> x = y \<and> atom b \<sharp> x)"
  and   "[{atom a}]res. x = [{atom b}]res. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> (b \<leftrightarrow> a) \<bullet> x = y \<and> atom b \<sharp> x)"
  and   "[[atom a]]lst. x = [[atom b]]lst. y \<longleftrightarrow> (a = b \<and> x = y) \<or> (a \<noteq> b \<and> (b \<leftrightarrow> a) \<bullet> x = y \<and> atom b \<sharp> x)"
by (auto simp: Abs1_eq_iff fresh_permute_left)


ML \<open>
fun alpha_single_simproc thm _ ctxt ctrm =
  let
    val thy = Proof_Context.theory_of ctxt
    val _ $ (_ $ x) $ (_ $ y) = Thm.term_of ctrm
    val cvrs = union (op =) (Term.add_frees x []) (Term.add_frees y [])
      |> filter (fn (_, ty) => Sign.of_sort thy (ty, @{sort fs}))
      |> map Free
      |> HOLogic.mk_tuple
      |> Thm.cterm_of ctxt
    val cvrs_ty = Thm.ctyp_of_cterm cvrs
    val thm' = thm
      |> Thm.instantiate' [NONE, NONE, SOME cvrs_ty] [NONE, NONE, NONE, NONE, SOME cvrs]
  in
    SOME thm'
  end
\<close>

simproc_setup alpha_set ("[{atom a}]set. x = [{atom b}]set. y") =
  \<open>alpha_single_simproc @{thm Abs1_eq_iff_all(1)[THEN eq_reflection]}\<close>

simproc_setup alpha_res ("[{atom a}]res. x = [{atom b}]res. y") =
  \<open>alpha_single_simproc @{thm Abs1_eq_iff_all(2)[THEN eq_reflection]}\<close>

simproc_setup alpha_lst ("[[atom a]]lst. x = [[atom b]]lst. y") =
  \<open>alpha_single_simproc @{thm Abs1_eq_iff_all(3)[THEN eq_reflection]}\<close>


subsection \<open>Renaming of bodies of abstractions\<close>

lemma Abs_rename_set:
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> bs) \<sharp>* x"
  (*and     b: "finite bs"*)
  shows "\<exists>q. [bs]set. x = [p \<bullet> bs]set. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
proof -
  from set_renaming_perm2
  obtain q where *: "\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> bs \<union> (p \<bullet> bs)" by blast
  have ***: "q \<bullet> bs = p \<bullet> bs" using *
    unfolding permute_set_eq_image image_def by auto
  have "[bs]set. x =  q \<bullet> ([bs]set. x)"
    apply(rule perm_supp_eq[symmetric])
    using a **
    unfolding Abs_fresh_star_iff
    unfolding fresh_star_def
    by auto
  also have "\<dots> = [q \<bullet> bs]set. (q \<bullet> x)" by simp
  finally have "[bs]set. x = [p \<bullet> bs]set. (q \<bullet> x)" by (simp add: ***)
  then show "\<exists>q. [bs]set. x = [p \<bullet> bs]set. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs" using *** by metis
qed

lemma Abs_rename_res:
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> bs) \<sharp>* x"
  (*and     b: "finite bs"*)
  shows "\<exists>q. [bs]res. x = [p \<bullet> bs]res. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
proof -
  from set_renaming_perm2
  obtain q where *: "\<forall>b \<in> bs. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> bs \<union> (p \<bullet> bs)" by blast
  have ***: "q \<bullet> bs = p \<bullet> bs" using *
    unfolding permute_set_eq_image image_def by auto
  have "[bs]res. x =  q \<bullet> ([bs]res. x)"
    apply(rule perm_supp_eq[symmetric])
    using a **
    unfolding Abs_fresh_star_iff
    unfolding fresh_star_def
    by auto
  also have "\<dots> = [q \<bullet> bs]res. (q \<bullet> x)" by simp
  finally have "[bs]res. x = [p \<bullet> bs]res. (q \<bullet> x)" by (simp add: ***)
  then show "\<exists>q. [bs]res. x = [p \<bullet> bs]res. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs" using *** by metis
qed

lemma Abs_rename_lst:
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> (set bs)) \<sharp>* x"
  shows "\<exists>q. [bs]lst. x = [p \<bullet> bs]lst. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
proof -
  from list_renaming_perm
  obtain q where *: "\<forall>b \<in> set bs. q \<bullet> b = p \<bullet> b" and **: "supp q \<subseteq> set bs \<union> (p \<bullet> set bs)" by blast
  have ***: "q \<bullet> bs = p \<bullet> bs" using * by (induct bs) (simp_all add: insert_eqvt)
  have "[bs]lst. x =  q \<bullet> ([bs]lst. x)"
    apply(rule perm_supp_eq[symmetric])
    using a **
    unfolding Abs_fresh_star_iff
    unfolding fresh_star_def
    by auto
  also have "\<dots> = [q \<bullet> bs]lst. (q \<bullet> x)" by simp
  finally have "[bs]lst. x = [p \<bullet> bs]lst. (q \<bullet> x)" by (simp add: ***)
  then show "\<exists>q. [bs]lst. x = [p \<bullet> bs]lst. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs" using *** by metis
qed


text \<open>for deep recursive binders\<close>

lemma Abs_rename_set':
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> bs) \<sharp>* x"
  (*and     b: "finite bs"*)
  shows "\<exists>q. [bs]set. x = [q \<bullet> bs]set. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
using Abs_rename_set[OF a] by metis

lemma Abs_rename_res':
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> bs) \<sharp>* x"
  (*and     b: "finite bs"*)
  shows "\<exists>q. [bs]res. x = [q \<bullet> bs]res. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
using Abs_rename_res[OF a] by metis

lemma Abs_rename_lst':
  fixes x::"'a::fs"
  assumes a: "(p \<bullet> (set bs)) \<sharp>* x"
  shows "\<exists>q. [bs]lst. x = [q \<bullet> bs]lst. (q \<bullet> x) \<and> q \<bullet> bs = p \<bullet> bs"
using Abs_rename_lst[OF a] by metis

section \<open>Infrastructure for building tuples of relations and functions\<close>

fun
  prod_fv :: "('a \<Rightarrow> atom set) \<Rightarrow> ('b \<Rightarrow> atom set) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> atom set"
where
  "prod_fv fv1 fv2 (x, y) = fv1 x \<union> fv2 y"

definition
  prod_alpha :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool)"
where
 "prod_alpha = rel_prod"

lemma [quot_respect]:
  shows "((R1 ===> (=)) ===> (R2 ===> (=)) ===> rel_prod R1 R2 ===> (=)) prod_fv prod_fv"
  unfolding rel_fun_def
  by auto

lemma [quot_preserve]:
  assumes q1: "Quotient3 R1 abs1 rep1"
  and     q2: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> id) ---> (abs2 ---> id) ---> map_prod rep1 rep2 ---> id) prod_fv = prod_fv"
  by (simp add: fun_eq_iff Quotient3_abs_rep[OF q1] Quotient3_abs_rep[OF q2])

lemma [mono]:
  shows "A <= B \<Longrightarrow> C <= D ==> prod_alpha A C <= prod_alpha B D"
  unfolding prod_alpha_def
  by auto

lemma [eqvt]:
  shows "p \<bullet> prod_alpha A B x y = prod_alpha (p \<bullet> A) (p \<bullet> B) (p \<bullet> x) (p \<bullet> y)"
  unfolding prod_alpha_def
  unfolding rel_prod_conv
  by (perm_simp) (rule refl)

lemma [eqvt]:
  shows "p \<bullet> prod_fv A B (x, y) = prod_fv (p \<bullet> A) (p \<bullet> B) (p \<bullet> x, p \<bullet> y)"
  unfolding prod_fv.simps
  by (perm_simp) (rule refl)

lemma prod_fv_supp:
  shows "prod_fv supp supp = supp"
by (rule ext)
   (auto simp: supp_Pair)

lemma prod_alpha_eq:
  shows "prod_alpha ((=)) ((=)) = ((=))"
  unfolding prod_alpha_def
  by (auto intro!: ext)

end
