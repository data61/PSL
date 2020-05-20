theory "Nominal-Utils"
imports Nominal2.Nominal2 "HOL-Library.AList"
begin

subsubsection \<open>Lemmas helping with equivariance proofs\<close>

lemma perm_rel_lemma:
  assumes "\<And> \<pi> x y. r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<Longrightarrow> r x y"
  shows "r (\<pi> \<bullet> x) (\<pi> \<bullet> y) \<longleftrightarrow> r x y" (is "?l \<longleftrightarrow> ?r")
by (metis (full_types) assms permute_minus_cancel(2))

lemma perm_rel_lemma2:
  assumes "\<And> \<pi> x y. r x y \<Longrightarrow> r (\<pi> \<bullet> x) (\<pi> \<bullet> y)"
  shows "r x y \<longleftrightarrow> r (\<pi> \<bullet> x) (\<pi> \<bullet> y)" (is "?l \<longleftrightarrow> ?r")
by (metis (full_types) assms permute_minus_cancel(2))

lemma fun_eqvtI:
  assumes f_eqvt[eqvt]: "(\<And> p x. p \<bullet> (f x) = f (p \<bullet> x))"
  shows "p \<bullet> f = f" by perm_simp rule

lemma eqvt_at_apply:
  assumes "eqvt_at f x"
  shows "(p \<bullet> f) x = f x"
by (metis (hide_lams, no_types) assms eqvt_at_def permute_fun_def permute_minus_cancel(1))

lemma eqvt_at_apply':
  assumes "eqvt_at f x"
  shows "p \<bullet> f x = f (p \<bullet> x)"
by (metis (hide_lams, no_types) assms eqvt_at_def)

lemma eqvt_at_apply'':
  assumes "eqvt_at f x"
  shows "(p \<bullet> f) (p \<bullet> x) = f (p \<bullet> x)"
by (metis (hide_lams, no_types) assms eqvt_at_def permute_fun_def permute_minus_cancel(1))


lemma size_list_eqvt[eqvt]: "p \<bullet> size_list f x = size_list (p \<bullet> f) (p \<bullet> x)"
proof (induction x)
  case (Cons x xs)
  have "f x = p \<bullet> (f x)" by (simp add: permute_pure)
  also have "... = (p \<bullet> f) (p \<bullet> x)" by simp
  with Cons
  show ?case by (auto simp add: permute_pure)
qed simp

subsubsection \<open>Freshness via equivariance\<close>

lemma eqvt_fresh_cong1: "(\<And>p x. p \<bullet> (f x) = f (p \<bullet> x)) \<Longrightarrow> a \<sharp> x \<Longrightarrow> a \<sharp> f x "
  apply (rule fresh_fun_eqvt_app[of f])
  apply (rule eqvtI)
  apply (rule eq_reflection)
  apply (rule ext)
  apply (metis permute_fun_def permute_minus_cancel(1))
  apply assumption
  done

lemma eqvt_fresh_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y"
  shows "a \<sharp> f x y"
proof-
  have "eqvt (\<lambda> (x,y). f x y)"
    using eqvt
    apply -
    apply (auto simp add: eqvt_def)
    apply (rule ext)
    apply auto
    by (metis permute_minus_cancel(1))
  moreover
  have "a \<sharp> (x, y)" using fresh1 fresh2 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y). f x y) (x, y)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma eqvt_fresh_star_cong1:
  assumes eqvt: "(\<And>p x. p \<bullet> (f x) = f (p \<bullet> x))"
  and fresh1: "a \<sharp>* x"
  shows "a \<sharp>* f x"
  by (metis fresh_star_def eqvt_fresh_cong1 assms)

lemma eqvt_fresh_star_cong2:
  assumes eqvt: "(\<And>p x y. p \<bullet> (f x y) = f (p \<bullet> x) (p \<bullet> y))"
  and fresh1: "a \<sharp>* x" and fresh2: "a \<sharp>* y"
  shows "a \<sharp>* f x y"
  by (metis fresh_star_def eqvt_fresh_cong2 assms)

lemma eqvt_fresh_cong3:
  assumes eqvt: "(\<And>p x y z. p \<bullet> (f x y z) = f (p \<bullet> x) (p \<bullet> y) (p \<bullet> z))"
  and fresh1: "a \<sharp> x" and fresh2: "a \<sharp> y" and fresh3: "a \<sharp> z"
  shows "a \<sharp> f x y z"
proof-
  have "eqvt (\<lambda> (x,y,z). f x y z)"
    using eqvt
    apply -
    apply (auto simp add: eqvt_def)
    apply (rule ext)
    apply auto
    by (metis permute_minus_cancel(1))
  moreover
  have "a \<sharp> (x, y, z)" using fresh1 fresh2 fresh3 by auto
  ultimately
  have "a \<sharp> (\<lambda> (x,y,z). f x y z) (x, y, z)" by (rule fresh_fun_eqvt_app)
  thus ?thesis by simp
qed

lemma eqvt_fresh_star_cong3:
  assumes eqvt: "(\<And>p x y z. p \<bullet> (f x y z) = f (p \<bullet> x) (p \<bullet> y) (p \<bullet> z))"
  and fresh1: "a \<sharp>* x" and fresh2: "a \<sharp>* y" and fresh3: "a \<sharp>* z"
  shows "a \<sharp>* f x y z"
  by (metis fresh_star_def eqvt_fresh_cong3 assms)

subsubsection \<open>Additional simplification rules\<close>

lemma not_self_fresh[simp]: "atom x \<sharp> x \<longleftrightarrow> False"
  by (metis fresh_at_base(2))

lemma fresh_star_singleton: "{ x } \<sharp>* e \<longleftrightarrow> x \<sharp> e"
  by (simp add: fresh_star_def)

subsubsection \<open>Additional equivariance lemmas\<close>

lemma eqvt_cases:
  fixes f x \<pi>
  assumes eqvt: "\<And>x. \<pi> \<bullet> f x = f (\<pi> \<bullet> x)"
  obtains "f x" "f (\<pi> \<bullet> x)" | "\<not> f x " " \<not> f (\<pi> \<bullet> x)"
  using assms[symmetric]
   by (cases "f x") auto

lemma range_eqvt: "\<pi> \<bullet> range Y = range (\<pi> \<bullet> Y)"
  unfolding image_eqvt UNIV_eqvt ..

lemma case_option_eqvt[eqvt]:
  "\<pi> \<bullet> case_option d f x = case_option (\<pi> \<bullet> d) (\<pi> \<bullet> f) (\<pi> \<bullet> x)"
  by(cases x)(simp_all)

lemma supp_option_eqvt:
  "supp (case_option d f x) \<subseteq> supp d \<union> supp f \<union> supp x"
  apply (cases x)
  apply (auto simp add: supp_Some )
  apply (metis (mono_tags) Un_iff subsetCE supp_fun_app)
  done

lemma funpow_eqvt[simp,eqvt]:
  "\<pi> \<bullet> ((f :: 'a \<Rightarrow> 'a::pt) ^^ n) = (\<pi> \<bullet> f) ^^ (\<pi> \<bullet> n)"
 apply (induct n)
 apply simp
 apply (rule ext)
 apply simp
 apply perm_simp
 apply simp
 done

lemma delete_eqvt[eqvt]:
  "\<pi> \<bullet> AList.delete x \<Gamma> = AList.delete (\<pi> \<bullet> x) (\<pi> \<bullet> \<Gamma>)"
by (induct \<Gamma>, auto)

lemma restrict_eqvt[eqvt]:
  "\<pi> \<bullet> AList.restrict S \<Gamma> = AList.restrict (\<pi> \<bullet> S) (\<pi> \<bullet> \<Gamma>)"
unfolding AList.restrict_eq by perm_simp rule

lemma supp_restrict:
  "supp (AList.restrict S \<Gamma>) \<subseteq> supp \<Gamma>"
 by (induction \<Gamma>) (auto simp add: supp_Pair supp_Cons)

lemma clearjunk_eqvt[eqvt]:
  "\<pi> \<bullet> AList.clearjunk \<Gamma> = AList.clearjunk (\<pi> \<bullet> \<Gamma>)"
  by (induction \<Gamma> rule: clearjunk.induct) auto

lemma map_ran_eqvt[eqvt]:
  "\<pi> \<bullet> map_ran f \<Gamma> = map_ran (\<pi> \<bullet> f) (\<pi> \<bullet> \<Gamma>)"
by (induct \<Gamma>, auto)

lemma dom_perm:
  "dom (\<pi> \<bullet> f) = \<pi> \<bullet> (dom f)"
  unfolding dom_def by (perm_simp) (simp)

lemmas dom_perm_rev[simp,eqvt] = dom_perm[symmetric]

lemma ran_perm[simp]:
  "\<pi> \<bullet> (ran f) = ran (\<pi> \<bullet> f)"
  unfolding ran_def by (perm_simp) (simp)

lemma map_add_eqvt[eqvt]:
  "\<pi> \<bullet> (m1 ++ m2) = (\<pi> \<bullet> m1) ++ (\<pi> \<bullet> m2)"
  unfolding map_add_def
  by (perm_simp, rule)

lemma map_of_eqvt[eqvt]:
  "\<pi> \<bullet> map_of l = map_of (\<pi> \<bullet> l)"
  apply (induct l)
  apply (simp add: permute_fun_def)
  apply simp
  apply perm_simp
  apply auto
  done

lemma concat_eqvt[eqvt]: "\<pi> \<bullet> concat l = concat (\<pi> \<bullet> l)"
  by (induction l)(auto simp add: append_eqvt)

lemma tranclp_eqvt[eqvt]: "\<pi> \<bullet> tranclp P v\<^sub>1 v\<^sub>2 = tranclp (\<pi> \<bullet> P) (\<pi> \<bullet> v\<^sub>1) (\<pi> \<bullet> v\<^sub>2)" 
  unfolding tranclp_def by perm_simp rule

lemma rtranclp_eqvt[eqvt]: "\<pi> \<bullet> rtranclp P v\<^sub>1 v\<^sub>2 = rtranclp (\<pi> \<bullet> P) (\<pi> \<bullet> v\<^sub>1) (\<pi> \<bullet> v\<^sub>2)" 
  unfolding rtranclp_def by perm_simp rule

lemma Set_filter_eqvt[eqvt]: "\<pi> \<bullet> Set.filter P S = Set.filter (\<pi> \<bullet> P) (\<pi> \<bullet> S)"
  unfolding Set.filter_def
  by perm_simp rule

lemma Sigma_eqvt'[eqvt]: "\<pi> \<bullet> Sigma = Sigma"
  apply (rule ext)
  apply (rule ext)
  apply (subst permute_fun_def)
  apply (subst permute_fun_def)
  unfolding Sigma_def
  apply perm_simp
  apply (simp add: permute_self)
  done

lemma override_on_eqvt[eqvt]:
  "\<pi> \<bullet> (override_on m1 m2 S) = override_on (\<pi> \<bullet> m1) (\<pi> \<bullet> m2) (\<pi> \<bullet> S)"
  by (auto simp add: override_on_def )

lemma card_eqvt[eqvt]:
  "\<pi> \<bullet> (card S) = card (\<pi> \<bullet> S)"
by (cases "finite S", induct rule: finite_induct) (auto simp add: card_insert_if mem_permute_iff permute_pure)

(* Helper lemmas provided by Christian Urban *)

lemma Projl_permute:
  assumes a: "\<exists>y. f = Inl y"
  shows "(p \<bullet> (Sum_Type.projl f)) = Sum_Type.projl (p \<bullet> f)"
using a by auto

lemma Projr_permute:
  assumes a: "\<exists>y. f = Inr y"
  shows "(p \<bullet> (Sum_Type.projr f)) = Sum_Type.projr (p \<bullet> f)"
using a by auto


subsubsection \<open>Freshness lemmas\<close>

lemma fresh_list_elem:
  assumes "a \<sharp> \<Gamma>"
  and "e \<in> set \<Gamma>"
  shows "a \<sharp> e"
using assms
by(induct \<Gamma>)(auto simp add: fresh_Cons)

lemma set_not_fresh:
  "x \<in> set L \<Longrightarrow> \<not>(atom x \<sharp> L)"
  by (metis fresh_list_elem not_self_fresh)

lemma pure_fresh_star[simp]: "a \<sharp>* (x :: 'a :: pure)"
  by (simp add: fresh_star_def pure_fresh)

lemma supp_set_mem: "x \<in> set L \<Longrightarrow> supp x \<subseteq> supp L"
  by (induct L) (auto simp add: supp_Cons)

lemma set_supp_mono: "set L \<subseteq> set L2 \<Longrightarrow> supp L \<subseteq> supp L2"
  by (induct L)(auto simp add: supp_Cons supp_Nil dest:supp_set_mem)

lemma fresh_star_at_base:
  fixes x :: "'a :: at_base"
  shows "S \<sharp>* x \<longleftrightarrow> atom x \<notin> S"
  by (metis fresh_at_base(2) fresh_star_def)


subsubsection \<open>Freshness and support for subsets of variables\<close>

lemma supp_mono: "finite (B::'a::fs set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> supp A \<subseteq> supp B"
  by (metis infinite_super subset_Un_eq supp_of_finite_union)

lemma fresh_subset:
  "finite B \<Longrightarrow> x \<sharp> (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp> A"
  by (auto dest:supp_mono simp add: fresh_def)

lemma fresh_star_subset:
  "finite B \<Longrightarrow> x \<sharp>* (B :: 'a::at_base set) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_def fresh_subset)

lemma fresh_star_set_subset:
  "x \<sharp>* (B :: 'a::at_base list) \<Longrightarrow> set A \<subseteq> set B \<Longrightarrow> x \<sharp>* A"
  by (metis fresh_star_set fresh_star_subset[OF finite_set])

subsubsection \<open>The set of free variables of an expression\<close>

definition fv :: "'a::pt \<Rightarrow> 'b::at_base set"
  where "fv e = {v. atom v \<in> supp e}"

lemma fv_eqvt[simp,eqvt]: "\<pi> \<bullet> (fv e) = fv (\<pi> \<bullet> e)"
  unfolding fv_def by simp

lemma fv_Nil[simp]: "fv [] = {}"
  by (auto simp add: fv_def supp_Nil)
lemma fv_Cons[simp]: "fv (x # xs) = fv x \<union> fv xs"
  by (auto simp add: fv_def supp_Cons)
lemma fv_Pair[simp]: "fv (x, y) = fv x \<union> fv y"
  by (auto simp add: fv_def supp_Pair)
lemma fv_append[simp]: "fv (x @ y) = fv x \<union> fv y"
  by (auto simp add: fv_def supp_append)
lemma fv_at_base[simp]: "fv a = {a::'a::at_base}"
  by (auto simp add: fv_def supp_at_base)
lemma fv_pure[simp]: "fv (a::'a::pure) = {}"
  by (auto simp add: fv_def pure_supp)

lemma fv_set_at_base[simp]: "fv (l :: ('a :: at_base) list) = set l"
  by (induction l) auto

lemma flip_not_fv: "a \<notin> fv x \<Longrightarrow> b \<notin> fv x \<Longrightarrow> (a \<leftrightarrow> b) \<bullet> x = x"
  by (metis flip_def fresh_def fv_def mem_Collect_eq swap_fresh_fresh)

lemma fv_not_fresh: "atom x \<sharp> e \<longleftrightarrow> x \<notin> fv e"
  unfolding fv_def fresh_def by blast

lemma fresh_fv: "finite (fv e :: 'a set) \<Longrightarrow>  atom (x :: ('a::at_base)) \<sharp> (fv e :: 'a set) \<longleftrightarrow> atom x \<sharp> e"
  unfolding fv_def fresh_def
  by (auto simp add: supp_finite_set_at_base)

lemma finite_fv[simp]: "finite (fv (e::'a::fs) :: ('b::at_base) set)"
proof-
  have "finite (supp e)" by (metis finite_supp)
  hence "finite (atom -` supp e :: 'b set)" 
    apply (rule finite_vimageI)
    apply (rule inj_onI)
    apply (simp)
    done
  moreover
  have "(atom -` supp e  :: 'b set) = fv e"   unfolding fv_def by auto
  ultimately
  show ?thesis by simp
qed

definition fv_list :: "'a::fs \<Rightarrow> 'b::at_base list"
  where "fv_list e = (SOME l. set l = fv e)"

lemma set_fv_list[simp]: "set (fv_list e) = (fv e :: ('b::at_base) set)"
proof-
  have "finite (fv e :: 'b set)" by (rule finite_fv)
  from finite_list[OF finite_fv]
  obtain l where "set l = (fv e :: 'b set)"..
  thus ?thesis
    unfolding fv_list_def by (rule someI)
qed

lemma fresh_fv_list[simp]:
  "a \<sharp> (fv_list e :: 'b::at_base list) \<longleftrightarrow> a \<sharp> (fv e :: 'b::at_base set)"
proof-
  have "a \<sharp> (fv_list e :: 'b::at_base list) \<longleftrightarrow> a \<sharp> set (fv_list e :: 'b::at_base list)"
    by (rule fresh_set[symmetric])
  also have "\<dots> \<longleftrightarrow> a \<sharp> (fv e :: 'b::at_base set)" by simp
  finally show ?thesis.
qed


subsubsection \<open>Other useful lemmas\<close>

lemma pure_permute_id: "permute p = (\<lambda> x. (x::'a::pure))"
  by rule (simp add: permute_pure)

lemma supp_set_elem_finite:
  assumes "finite S"
  and "(m::'a::fs) \<in> S"
  and "y \<in> supp m"
  shows "y \<in> supp S"
  using assms supp_of_finite_sets
  by auto

lemmas fresh_star_Cons = fresh_star_list(2)

lemma mem_permute_set: 
  shows "x \<in> p \<bullet> S \<longleftrightarrow> (- p \<bullet> x) \<in> S"
  by (metis mem_permute_iff permute_minus_cancel(2))

lemma flip_set_both_not_in:
  assumes "x \<notin> S" and "x' \<notin> S"
  shows "((x' \<leftrightarrow> x) \<bullet> S) = S"
  unfolding permute_set_def
  by (auto) (metis assms flip_at_base_simps(3))+

lemma inj_atom: "inj atom" by (metis atom_eq_iff injI)

lemmas image_Int[OF inj_atom, simp]

lemma eqvt_uncurry: "eqvt f \<Longrightarrow> eqvt (case_prod f)"
  unfolding eqvt_def
  by perm_simp simp

lemma supp_fun_app_eqvt2:
  assumes a: "eqvt f"
  shows "supp (f x y) \<subseteq> supp x \<union> supp y"
proof-
  from supp_fun_app_eqvt[OF eqvt_uncurry [OF a]]
  have "supp (case_prod f (x,y)) \<subseteq> supp (x,y)".
  thus ?thesis by (simp add: supp_Pair)
qed

lemma supp_fun_app_eqvt3:
  assumes a: "eqvt f"
  shows "supp (f x y z) \<subseteq> supp x \<union> supp y \<union> supp z"
proof-
  from supp_fun_app_eqvt2[OF eqvt_uncurry [OF a]]
  have "supp (case_prod f (x,y) z) \<subseteq> supp (x,y) \<union> supp z".
  thus ?thesis by (simp add: supp_Pair)
qed

(* Fighting eta-contraction *)
lemma permute_0[simp]: "permute 0 = (\<lambda> x. x)"
  by auto
lemma permute_comp[simp]: "permute x \<circ> permute y = permute (x + y)" by auto

lemma map_permute: "map (permute p) = permute p"
  apply rule
  apply (induct_tac x)
  apply auto
  done

lemma fresh_star_restrictA[intro]: "a \<sharp>* \<Gamma> \<Longrightarrow> a \<sharp>* AList.restrict V \<Gamma>"
  by (induction \<Gamma>) (auto simp add: fresh_star_Cons)

 

(* Unused. Still submit? *)
lemma Abs_lst_Nil_eq[simp]: "[[]]lst. (x::'a::fs) = [xs]lst. x' \<longleftrightarrow> (([],x) = (xs, x'))"
  apply rule
  apply (frule Abs_lst_fcb2[where f = "\<lambda> x y _ . (x,y)" and as = "[]" and bs = "xs" and c = "()"])
  apply (auto simp add: fresh_star_def)
  done

(* Unused. Still submit? *)
lemma Abs_lst_Nil_eq2[simp]: "[xs]lst. (x::'a::fs) = [[]]lst. x' \<longleftrightarrow> ((xs,x) = ([], x'))"
  by (subst eq_commute) auto



end
