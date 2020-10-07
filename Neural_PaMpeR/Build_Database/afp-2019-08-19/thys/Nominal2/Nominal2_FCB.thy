theory Nominal2_FCB
imports Nominal2_Abs
begin


text \<open>
  A tactic which solves all trivial cases in function
  definitions, and leaves the others unchanged.
\<close>

ML \<open>
val all_trivials : (Proof.context -> Proof.method) context_parser =
Scan.succeed (fn ctxt =>
 let
   val tac = TRYALL (SOLVED' (full_simp_tac ctxt))
 in
   Method.SIMPLE_METHOD' (K tac)
 end)
\<close>

method_setup all_trivials = \<open>all_trivials\<close> \<open>solves trivial goals\<close>


lemma Abs_lst1_fcb:
  fixes x y :: "'a :: at"
    and S T :: "'b :: fs"
  assumes e: "[[atom x]]lst. T = [[atom y]]lst. S"
  and f1: "\<lbrakk>x \<noteq> y; atom y \<sharp> T; atom x \<sharp> (y \<leftrightarrow> x) \<bullet> T\<rbrakk> \<Longrightarrow> atom x \<sharp> f x T"
  and f2: "\<lbrakk>x \<noteq> y; atom y \<sharp> T; atom x \<sharp> (y \<leftrightarrow> x) \<bullet> T\<rbrakk> \<Longrightarrow> atom y \<sharp> f x T"
  and p: "\<lbrakk>S = (x \<leftrightarrow> y) \<bullet> T; x \<noteq> y; atom y \<sharp> T; atom x \<sharp> S\<rbrakk>
    \<Longrightarrow> (x \<leftrightarrow> y) \<bullet> (f x T) = f y S"
  shows "f x T = f y S"
  using e
  apply(case_tac "atom x \<sharp> S")
  apply(simp add: Abs1_eq_iff')
  apply(elim conjE disjE)
  apply(simp)
  apply(rule trans)
  apply(rule_tac p="(x \<leftrightarrow> y)" in supp_perm_eq[symmetric])
  apply(rule fresh_star_supp_conv)
  apply(simp add: flip_def supp_swap fresh_star_def f1 f2)
  apply(simp add: flip_commute p)
  apply(simp add: Abs1_eq_iff)
  done

lemma Abs_lst_fcb:
  fixes xs ys :: "'a :: fs"
    and S T :: "'b :: fs"
  assumes e: "(Abs_lst (ba xs) T) = (Abs_lst (ba ys) S)"
    and f1: "\<And>x. x \<in> set (ba xs) \<Longrightarrow> x \<sharp> f xs T"
    and f2: "\<And>x. \<lbrakk>supp T - set (ba xs) = supp S - set (ba ys); x \<in> set (ba ys)\<rbrakk> \<Longrightarrow> x \<sharp> f xs T"
    and eqv: "\<And>p. \<lbrakk>p \<bullet> T = S; p \<bullet> ba xs = ba ys; supp p \<subseteq> set (ba xs) \<union> set (ba ys)\<rbrakk>
      \<Longrightarrow> p \<bullet> (f xs T) = f ys S"
  shows "f xs T = f ys S"
  using e apply -
  apply(subst (asm) Abs_eq_iff2)
  apply(simp add: alphas)
  apply(elim exE conjE)
  apply(rule trans)
  apply(rule_tac p="p" in supp_perm_eq[symmetric])
  apply(rule fresh_star_supp_conv)
  apply(drule fresh_star_perm_set_conv)
  apply(rule finite_Diff)
  apply(rule finite_supp)
  apply(subgoal_tac "(set (ba xs) \<union> set (ba ys)) \<sharp>* f xs T")
  apply(metis Un_absorb2 fresh_star_Un)
  apply(subst fresh_star_Un)
  apply(rule conjI)
  apply(simp add: fresh_star_def f1)
  apply(simp add: fresh_star_def f2)
  apply(simp add: eqv)
  done

lemma Abs_set_fcb:
  fixes xs ys :: "'a :: fs"
    and S T :: "'b :: fs"
  assumes e: "(Abs_set (ba xs) T) = (Abs_set (ba ys) S)"
    and f1: "\<And>x. x \<in> ba xs \<Longrightarrow> x \<sharp> f xs T"
    and f2: "\<And>x. \<lbrakk>supp T - ba xs = supp S - ba ys; x \<in> ba ys\<rbrakk> \<Longrightarrow> x \<sharp> f xs T"
    and eqv: "\<And>p. \<lbrakk>p \<bullet> T = S; p \<bullet> ba xs = ba ys; supp p \<subseteq> ba xs \<union> ba ys\<rbrakk> \<Longrightarrow> p \<bullet> (f xs T) = f ys S"
  shows "f xs T = f ys S"
  using e apply -
  apply(subst (asm) Abs_eq_iff2)
  apply(simp add: alphas)
  apply(elim exE conjE)
  apply(rule trans)
  apply(rule_tac p="p" in supp_perm_eq[symmetric])
  apply(rule fresh_star_supp_conv)
  apply(drule fresh_star_perm_set_conv)
  apply(rule finite_Diff)
  apply(rule finite_supp)
  apply(subgoal_tac "(ba xs \<union> ba ys) \<sharp>* f xs T")
  apply(metis Un_absorb2 fresh_star_Un)
  apply(subst fresh_star_Un)
  apply(rule conjI)
  apply(simp add: fresh_star_def f1)
  apply(simp add: fresh_star_def f2)
  apply(simp add: eqv)
  done

lemma Abs_res_fcb:
  fixes xs ys :: "('a :: at_base) set"
    and S T :: "'b :: fs"
  assumes e: "(Abs_res (atom ` xs) T) = (Abs_res (atom ` ys) S)"
    and f1: "\<And>x. x \<in> atom ` xs \<Longrightarrow> x \<in> supp T \<Longrightarrow> x \<sharp> f xs T"
    and f2: "\<And>x. \<lbrakk>supp T - atom ` xs = supp S - atom ` ys; x \<in> atom ` ys; x \<in> supp S\<rbrakk> \<Longrightarrow> x \<sharp> f xs T"
    and eqv: "\<And>p. \<lbrakk>p \<bullet> T = S; supp p \<subseteq> atom ` xs \<inter> supp T \<union> atom ` ys \<inter> supp S;
      p \<bullet> (atom ` xs \<inter> supp T) = atom ` ys \<inter> supp S\<rbrakk> \<Longrightarrow> p \<bullet> (f xs T) = f ys S"
  shows "f xs T = f ys S"
  using e apply -
  apply(subst (asm) Abs_eq_res_set)
  apply(subst (asm) Abs_eq_iff2)
  apply(simp add: alphas)
  apply(elim exE conjE)
  apply(rule trans)
  apply(rule_tac p="p" in supp_perm_eq[symmetric])
  apply(rule fresh_star_supp_conv)
  apply(drule fresh_star_perm_set_conv)
  apply(rule finite_Diff)
  apply(rule finite_supp)
  apply(subgoal_tac "(atom ` xs \<inter> supp T \<union> atom ` ys \<inter> supp S) \<sharp>* f xs T")
  apply(metis Un_absorb2 fresh_star_Un)
  apply(subst fresh_star_Un)
  apply(rule conjI)
  apply(simp add: fresh_star_def f1)
  apply(subgoal_tac "supp T - atom ` xs = supp S - atom ` ys")
  apply(simp add: fresh_star_def f2)
  apply(blast)
  apply(simp add: eqv)
  done



lemma Abs_set_fcb2:
  fixes as bs :: "atom set"
    and x y :: "'b :: fs"
    and c::"'c::fs"
  assumes eq: "[as]set. x = [bs]set. y"
  and fin: "finite as" "finite bs"
  and fcb1: "as \<sharp>* f as x c"
  and fresh1: "as \<sharp>* c"
  and fresh2: "bs \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f as x c) = f (p \<bullet> as) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f bs y c) = f (p \<bullet> bs) (p \<bullet> y) c"
  shows "f as x c = f bs y c"
proof -
  have "supp (as, x, c) supports (f as x c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm1 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin1: "finite (supp (f as x c))"
    using fin by (auto intro: supports_finite simp add: finite_supp supp_of_finite_sets supp_Pair)
  have "supp (bs, y, c) supports (f bs y c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm2 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin2: "finite (supp (f bs y c))"
    using fin by (auto intro: supports_finite simp add: finite_supp supp_of_finite_sets supp_Pair)
  obtain q::"perm" where
    fr1: "(q \<bullet> as) \<sharp>* (x, c, f as x c, f bs y c)" and
    fr2: "supp q \<sharp>* ([as]set. x)" and
    inc: "supp q \<subseteq> as \<union> (q \<bullet> as)"
    using at_set_avoiding3[where xs="as" and c="(x, c, f as x c, f bs y c)" and x="[as]set. x"]
      fin1 fin2 fin
    by (auto simp add: supp_Pair finite_supp Abs_fresh_star dest: fresh_star_supp_conv)
  have "[q \<bullet> as]set. (q \<bullet> x) = q \<bullet> ([as]set. x)" by simp
  also have "\<dots> = [as]set. x"
    by (simp only: fr2 perm_supp_eq)
  finally have "[q \<bullet> as]set. (q \<bullet> x) = [bs]set. y" using eq by simp
  then obtain r::perm where
    qq1: "q \<bullet> x = r \<bullet> y" and
    qq2: "q \<bullet> as = r \<bullet> bs" and
    qq3: "supp r \<subseteq> (q \<bullet> as) \<union> bs"
    apply(drule_tac sym)
    apply(simp only: Abs_eq_iff2 alphas)
    apply(erule exE)
    apply(erule conjE)+
    apply(drule_tac x="p" in meta_spec)
    apply(simp add: set_eqvt)
    apply(blast)
    done
  have "as \<sharp>* f as x c" by (rule fcb1)
  then have "q \<bullet> (as \<sharp>* f as x c)"
    by (simp add: permute_bool_def)
  then have "(q \<bullet> as) \<sharp>* f (q \<bullet> as) (q \<bullet> x) c"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm1)
    using inc fresh1 fr1
    apply(auto simp add: fresh_star_def fresh_Pair)
    done
  then have "(r \<bullet> bs) \<sharp>* f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  then have "r \<bullet> (bs \<sharp>* f bs y c)"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm2[symmetric])
    using qq3 fresh2 fr1
    apply(auto simp add: set_eqvt fresh_star_def fresh_Pair)
    done
  then have fcb2: "bs \<sharp>* f bs y c" by (simp add: permute_bool_def)
  have "f as x c = q \<bullet> (f as x c)"
    apply(rule perm_supp_eq[symmetric])
    using inc fcb1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (q \<bullet> as) (q \<bullet> x) c"
    apply(rule perm1)
    using inc fresh1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  also have "\<dots> = r \<bullet> (f bs y c)"
    apply(rule perm2[symmetric])
    using qq3 fresh2 fr1 by (auto simp add: fresh_star_def)
  also have "... = f bs y c"
    apply(rule perm_supp_eq)
    using qq3 fr1 fcb2 by (auto simp add: fresh_star_def)
  finally show ?thesis by simp
qed


lemma Abs_res_fcb2:
  fixes as bs :: "atom set"
    and x y :: "'b :: fs"
    and c::"'c::fs"
  assumes eq: "[as]res. x = [bs]res. y"
  and fin: "finite as" "finite bs"
  and fcb1: "(as \<inter> supp x) \<sharp>* f (as \<inter> supp x) x c"
  and fresh1: "as \<sharp>* c"
  and fresh2: "bs \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f (as \<inter> supp x) x c) = f (p \<bullet> (as \<inter> supp x)) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f (bs \<inter> supp y) y c) = f (p \<bullet> (bs \<inter> supp y)) (p \<bullet> y) c"
  shows "f (as \<inter> supp x) x c = f (bs \<inter> supp y) y c"
proof -
  have "supp (as, x, c) supports (f (as \<inter> supp x) x c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm1 fresh_star_def supp_swap swap_fresh_fresh inter_eqvt supp_eqvt)
  then have fin1: "finite (supp (f (as \<inter> supp x) x c))"
    using fin by (auto intro: supports_finite simp add: finite_supp supp_of_finite_sets supp_Pair)
  have "supp (bs, y, c) supports (f (bs \<inter> supp y) y c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm2 fresh_star_def supp_swap swap_fresh_fresh inter_eqvt supp_eqvt)
  then have fin2: "finite (supp (f (bs \<inter> supp y) y c))"
    using fin by (auto intro: supports_finite simp add: finite_supp supp_of_finite_sets supp_Pair)
  obtain q::"perm" where
    fr1: "(q \<bullet> (as \<inter> supp x)) \<sharp>* (x, c, f (as \<inter> supp x) x c, f (bs \<inter> supp y) y c)" and
    fr2: "supp q \<sharp>* ([as \<inter> supp x]set. x)" and
    inc: "supp q \<subseteq> (as \<inter> supp x) \<union> (q \<bullet> (as \<inter> supp x))"
    using at_set_avoiding3[where xs="as \<inter> supp x" and c="(x, c, f (as \<inter> supp x) x c, f (bs \<inter> supp y) y c)"
      and x="[as \<inter> supp x]set. x"]
      fin1 fin2 fin
    apply (auto simp add: supp_Pair finite_supp Abs_fresh_star dest: fresh_star_supp_conv)
    done
  have "[q \<bullet> (as \<inter> supp x)]set. (q \<bullet> x) = q \<bullet> ([as \<inter> supp x]set. x)" by simp
  also have "\<dots> = [as \<inter> supp x]set. x"
    by (simp only: fr2 perm_supp_eq)
  finally have "[q \<bullet> (as \<inter> supp x)]set. (q \<bullet> x) = [bs \<inter> supp y]set. y" using eq
    by(simp add: Abs_eq_res_set)
  then obtain r::perm where
    qq1: "q \<bullet> x = r \<bullet> y" and
    qq2: "(q \<bullet> as \<inter> supp (q \<bullet> x)) = r \<bullet> (bs \<inter> supp y)" and
    qq3: "supp r \<subseteq> (bs \<inter> supp y) \<union> q \<bullet> (as \<inter> supp x)"
    apply(drule_tac sym)
    apply(simp only: Abs_eq_iff2 alphas)
    apply(erule exE)
    apply(erule conjE)+
    apply(drule_tac x="p" in meta_spec)
    apply(simp add: set_eqvt inter_eqvt supp_eqvt)
    done
  have "(as \<inter> supp x) \<sharp>* f (as \<inter> supp x) x c" by (rule fcb1)
  then have "q \<bullet> ((as \<inter> supp x) \<sharp>* f (as \<inter> supp x) x c)"
    by (simp add: permute_bool_def)
  then have "(q \<bullet> (as \<inter> supp x)) \<sharp>* f (q \<bullet> (as \<inter> supp x)) (q \<bullet> x) c"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm1)
    using inc fresh1 fr1
    apply(auto simp add: fresh_star_def fresh_Pair)
    done
  then have "(r \<bullet> (bs \<inter> supp y)) \<sharp>* f (r \<bullet> (bs \<inter> supp y)) (r \<bullet> y) c" using qq1 qq2
    apply(perm_simp)
    apply simp
    done
  then have "r \<bullet> ((bs \<inter> supp y) \<sharp>* f (bs \<inter> supp y) y c)"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm2[symmetric])
    using qq3 fresh2 fr1
    apply(auto simp add: set_eqvt fresh_star_def fresh_Pair)
    done
  then have fcb2: "(bs \<inter> supp y) \<sharp>* f (bs \<inter> supp y) y c" by (simp add: permute_bool_def)
  have "f (as \<inter> supp x) x c = q \<bullet> (f (as \<inter> supp x) x c)"
    apply(rule perm_supp_eq[symmetric])
    using inc fcb1 fr1
    apply (auto simp add: fresh_star_def)
    done
  also have "\<dots> = f (q \<bullet> (as \<inter> supp x)) (q \<bullet> x) c"
    apply(rule perm1)
    using inc fresh1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (r \<bullet> (bs \<inter> supp y)) (r \<bullet> y) c" using qq1 qq2
    apply(perm_simp)
    apply simp
    done
  also have "\<dots> = r \<bullet> (f (bs \<inter> supp y) y c)"
    apply(rule perm2[symmetric])
    using qq3 fresh2 fr1 by (auto simp add: fresh_star_def)
  also have "... = f (bs \<inter> supp y) y c"
    apply(rule perm_supp_eq)
    using qq3 fr1 fcb2 by (auto simp add: fresh_star_def)
  finally show ?thesis by simp
qed

lemma Abs_lst_fcb2:
  fixes as bs :: "atom list"
    and x y :: "'b :: fs"
    and c::"'c::fs"
  assumes eq: "[as]lst. x = [bs]lst. y"
  and fcb1: "(set as) \<sharp>* f as x c"
  and fresh1: "set as \<sharp>* c"
  and fresh2: "set bs \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f as x c) = f (p \<bullet> as) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f bs y c) = f (p \<bullet> bs) (p \<bullet> y) c"
  shows "f as x c = f bs y c"
proof -
  have "supp (as, x, c) supports (f as x c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm1 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin1: "finite (supp (f as x c))"
    by (auto intro: supports_finite simp add: finite_supp)
  have "supp (bs, y, c) supports (f bs y c)"
    unfolding  supports_def fresh_def[symmetric]
    by (simp add: fresh_Pair perm2 fresh_star_def supp_swap swap_fresh_fresh)
  then have fin2: "finite (supp (f bs y c))"
    by (auto intro: supports_finite simp add: finite_supp)
  obtain q::"perm" where
    fr1: "(q \<bullet> (set as)) \<sharp>* (x, c, f as x c, f bs y c)" and
    fr2: "supp q \<sharp>* Abs_lst as x" and
    inc: "supp q \<subseteq> (set as) \<union> q \<bullet> (set as)"
    using at_set_avoiding3[where xs="set as" and c="(x, c, f as x c, f bs y c)" and x="[as]lst. x"]
      fin1 fin2
    by (auto simp add: supp_Pair finite_supp Abs_fresh_star dest: fresh_star_supp_conv)
  have "Abs_lst (q \<bullet> as) (q \<bullet> x) = q \<bullet> Abs_lst as x" by simp
  also have "\<dots> = Abs_lst as x"
    by (simp only: fr2 perm_supp_eq)
  finally have "Abs_lst (q \<bullet> as) (q \<bullet> x) = Abs_lst bs y" using eq by simp
  then obtain r::perm where
    qq1: "q \<bullet> x = r \<bullet> y" and
    qq2: "q \<bullet> as = r \<bullet> bs" and
    qq3: "supp r \<subseteq> (q \<bullet> (set as)) \<union> set bs"
    apply(drule_tac sym)
    apply(simp only: Abs_eq_iff2 alphas)
    apply(erule exE)
    apply(erule conjE)+
    apply(drule_tac x="p" in meta_spec)
    apply(simp add: set_eqvt)
    apply(blast)
    done
  have "(set as) \<sharp>* f as x c" by (rule fcb1)
  then have "q \<bullet> ((set as) \<sharp>* f as x c)"
    by (simp add: permute_bool_def)
  then have "set (q \<bullet> as) \<sharp>* f (q \<bullet> as) (q \<bullet> x) c"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm1)
    using inc fresh1 fr1
    apply(auto simp add: fresh_star_def fresh_Pair)
    done
  then have "set (r \<bullet> bs) \<sharp>* f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  then have "r \<bullet> ((set bs) \<sharp>* f bs y c)"
    apply(simp only: fresh_star_eqvt set_eqvt)
    apply(subst (asm) perm2[symmetric])
    using qq3 fresh2 fr1
    apply(auto simp add: set_eqvt fresh_star_def fresh_Pair)
    done
  then have fcb2: "(set bs) \<sharp>* f bs y c" by (simp add: permute_bool_def)
  have "f as x c = q \<bullet> (f as x c)"
    apply(rule perm_supp_eq[symmetric])
    using inc fcb1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (q \<bullet> as) (q \<bullet> x) c"
    apply(rule perm1)
    using inc fresh1 fr1 by (auto simp add: fresh_star_def)
  also have "\<dots> = f (r \<bullet> bs) (r \<bullet> y) c" using qq1 qq2 by simp
  also have "\<dots> = r \<bullet> (f bs y c)"
    apply(rule perm2[symmetric])
    using qq3 fresh2 fr1 by (auto simp add: fresh_star_def)
  also have "... = f bs y c"
    apply(rule perm_supp_eq)
    using qq3 fr1 fcb2 by (auto simp add: fresh_star_def)
  finally show ?thesis by simp
qed

lemma Abs_lst1_fcb2:
  fixes a b :: "atom"
    and x y :: "'b :: fs"
    and c::"'c :: fs"
  assumes e: "[[a]]lst. x = [[b]]lst. y"
  and fcb1: "a \<sharp> f a x c"
  and fresh: "{a, b} \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f a x c) = f (p \<bullet> a) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f b y c) = f (p \<bullet> b) (p \<bullet> y) c"
  shows "f a x c = f b y c"
using e
apply(drule_tac Abs_lst_fcb2[where c="c" and f="\<lambda>(as::atom list) . f (hd as)"])
apply(simp_all)
using fcb1 fresh perm1 perm2
apply(simp_all add: fresh_star_def)
done

lemma Abs_lst1_fcb2':
  fixes a b :: "'a::at_base"
    and x y :: "'b :: fs"
    and c::"'c :: fs"
  assumes e: "[[atom a]]lst. x = [[atom b]]lst. y"
  and fcb1: "atom a \<sharp> f a x c"
  and fresh: "{atom a, atom b} \<sharp>* c"
  and perm1: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f a x c) = f (p \<bullet> a) (p \<bullet> x) c"
  and perm2: "\<And>p. supp p \<sharp>* c \<Longrightarrow> p \<bullet> (f b y c) = f (p \<bullet> b) (p \<bullet> y) c"
  shows "f a x c = f b y c"
using e
apply(drule_tac Abs_lst1_fcb2[where c="c" and f="\<lambda>a . f ((inv atom) a)"])
using  fcb1 fresh perm1 perm2
apply(simp_all add: fresh_star_def inv_f_f inj_on_def atom_eqvt)
done

end
