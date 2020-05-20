section \<open>Permutations as Products of Disjoint Cycles\<close>

theory Executable_Permutations
imports
  Graph_Theory.Funpow
  List_Aux
  "HOL-Library.Permutations"
  "HOL-Library.Rewrite"
begin

subsection \<open>Cyclic Permutations\<close>

definition list_succ :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "list_succ xs x = (if x \<in> set xs then xs ! ((index xs x + 1) mod length xs) else x)"

text \<open>
  We demonstrate the functions on the following simple lemmas

  @{lemma "list_succ [1 :: int, 2, 3] 1 = 2" by code_simp}
  @{lemma "list_succ [1 :: int, 2, 3] 2 = 3" by code_simp}
  @{lemma "list_succ [1 :: int, 2, 3] 3 = 1" by code_simp}
\<close>

lemma list_succ_altdef:
  "list_succ xs x = (let n = index xs x in if n + 1 = length xs then xs ! 0 else if n + 1 < length xs then xs ! (n + 1) else x)"
  using index_le_size[of xs x] unfolding list_succ_def index_less_size_conv[symmetric] by (auto simp: Let_def)

lemma list_succ_Nil:
  "list_succ [] = id"
  by (simp add: list_succ_def fun_eq_iff)

lemma list_succ_singleton:
  "list_succ [x] = list_succ []"
  by (simp add: fun_eq_iff list_succ_def)

lemma list_succ_short:
  assumes "length xs < 2" shows "list_succ xs = id"
  using assms
  by (cases xs) (rename_tac [2] y ys, case_tac [2] ys, auto simp: list_succ_Nil list_succ_singleton)

lemma list_succ_simps:
  "index xs x + 1 = length xs \<Longrightarrow> list_succ xs x = xs ! 0"
  "index xs x + 1 < length xs \<Longrightarrow> list_succ xs x = xs ! (index xs x + 1)"
  "length xs \<le> index xs x \<Longrightarrow> list_succ xs x = x"
  by (auto simp: list_succ_altdef)

lemma list_succ_not_in:
  assumes "x \<notin> set xs" shows "list_succ xs x = x"
  using assms by (auto simp: list_succ_def)

lemma list_succ_list_succ_rev:
  assumes "distinct xs" shows "list_succ (rev xs) (list_succ xs x) = x"
proof -
  { assume "index xs x + 1 < length xs"
    moreover then have "length xs - Suc (Suc (length xs - Suc (Suc (index xs x)))) = index xs x"
      by linarith
    ultimately have ?thesis using assms
      by (simp add: list_succ_def index_rev index_nth_id rev_nth)
  }
  moreover
  { assume A: "index xs x + 1 = length xs"
    moreover
    from A have "xs \<noteq> []" by auto
    moreover
    with A have "last xs = xs ! index xs x" by (cases "length xs") (auto simp: last_conv_nth)
    ultimately
    have ?thesis
      using assms
      by (auto simp add: list_succ_def rev_nth index_rev index_nth_id last_conv_nth)
  }
  moreover
  { assume A: "index xs x \<ge> length xs"
    then have "x \<notin> set xs" by (metis index_less less_irrefl)
    then have ?thesis by (auto simp: list_succ_def) }
  ultimately show ?thesis by (metis discrete le_less not_less) 
qed

lemma inj_list_succ: "distinct xs \<Longrightarrow> inj (list_succ xs)"
  by (metis injI list_succ_list_succ_rev)

lemma inv_list_succ_eq: "distinct xs \<Longrightarrow> inv (list_succ xs) = list_succ (rev xs)"
  by (metis distinct_rev inj_imp_inv_eq inj_list_succ list_succ_list_succ_rev)

lemma bij_list_succ: "distinct xs \<Longrightarrow> bij (list_succ xs)"
  by (metis bij_def inj_list_succ distinct_rev list_succ_list_succ_rev surj_def)

lemma list_succ_permutes:
  assumes "distinct xs" shows "list_succ xs permutes set xs"
  using assms by (auto simp: permutes_conv_has_dom bij_list_succ has_dom_def list_succ_def)

lemma permutation_list_succ:
  assumes "distinct xs" shows "permutation (list_succ xs)"
  using list_succ_permutes[OF assms] by (auto simp: permutation_permutes)

lemma list_succ_nth:
  assumes "distinct xs" "n < length xs" shows "list_succ xs (xs ! n) = xs ! (Suc n mod length xs)"
  using assms by (auto simp: list_succ_def index_nth_id)

lemma list_succ_last[simp]:
  assumes "distinct xs" "xs \<noteq> []" shows "list_succ xs (last xs) = hd xs"
  using assms by (auto simp: list_succ_def hd_conv_nth)

lemma list_succ_rotate1[simp]:
  assumes "distinct xs" shows "list_succ (rotate1 xs) = list_succ xs"
proof (rule ext)
  fix y show "list_succ (rotate1 xs) y = list_succ xs y"
    using assms
  proof (induct xs)
    case Nil then show ?case by simp
  next
    case (Cons x xs)
    show ?case
    proof (cases "x = y")
      case True
      then have "index (xs @ [y]) y = length xs"
        using \<open>distinct (x # xs)\<close> by (simp add: index_append)
      with True show ?thesis by (cases "xs=[]") (auto simp: list_succ_def nth_append)
    next
      case False
      then show ?thesis
        apply (cases "index xs y + 1 < length xs")
        apply (auto simp:list_succ_def index_append nth_append)
        by (metis Suc_lessI index_less_size_conv mod_self nth_Cons_0 nth_append nth_append_length)
    qed
  qed
qed
  
lemma list_succ_rotate[simp]:
  assumes "distinct xs" shows "list_succ (rotate n xs) = list_succ xs"
  using assms by (induct n) auto

lemma list_succ_in_conv:
  "list_succ xs x \<in> set xs \<longleftrightarrow> x \<in> set xs"
  by (auto simp: list_succ_def not_nil_if_in_set )

lemma list_succ_in_conv1:
  assumes "A \<inter> set xs = {}"
  shows "list_succ xs x \<in> A \<longleftrightarrow> x \<in> A"
  by (metis assms disjoint_iff_not_equal list_succ_in_conv list_succ_not_in)

lemma list_succ_commute:
  assumes "set xs \<inter> set ys = {}"
  shows "list_succ xs (list_succ ys x) = list_succ ys (list_succ xs x)"
proof -
  have "\<And>x. x \<in> set xs \<Longrightarrow> list_succ ys x = x"
     "\<And>x. x \<in> set ys \<Longrightarrow> list_succ xs x = x"
    using assms by (blast intro: list_succ_not_in)+
  then show ?thesis
    by (cases "x \<in> set xs \<union> set ys") (auto simp: list_succ_in_conv list_succ_not_in)
qed


subsection \<open>Arbitrary Permutations\<close>

fun lists_succ :: "'a list list \<Rightarrow> 'a \<Rightarrow> 'a" where
  "lists_succ [] x = x"
| "lists_succ (xs # xss) x = list_succ xs (lists_succ xss x)"

definition distincts ::  "'a list list \<Rightarrow> bool" where
  "distincts xss \<equiv> distinct xss \<and> (\<forall>xs \<in> set xss. distinct xs \<and> xs \<noteq> []) \<and> (\<forall>xs \<in> set xss. \<forall>ys \<in> set xss. xs \<noteq> ys \<longrightarrow> set xs \<inter> set ys = {})"

lemma distincts_distinct: "distincts xss \<Longrightarrow> distinct xss"
  by (auto simp: distincts_def)

lemma distincts_Nil[simp]: "distincts []"
  by (simp add: distincts_def)

lemma distincts_single: "distincts [xs] \<longleftrightarrow> distinct xs \<and> xs \<noteq> []"
  by (auto simp add: distincts_def)

lemma distincts_Cons: "distincts (xs # xss)
   \<longleftrightarrow> xs \<noteq> [] \<and> distinct xs \<and> distincts xss \<and> (set xs \<inter> (\<Union>ys \<in> set xss. set ys)) = {}" (is "?L \<longleftrightarrow> ?R")
proof 
  assume ?L then show ?R by (auto simp: distincts_def)
next
  assume ?R
  then have "distinct (xs # xss)"
    apply (auto simp: disjoint_iff_not_equal distincts_distinct)
    apply (metis length_greater_0_conv nth_mem)
    done
  moreover
  from \<open>?R\<close> have "\<forall>xs \<in> set (xs # xss). distinct xs \<and> xs \<noteq> []"
    by (auto simp: distincts_def)
  moreover
  from \<open>?R\<close> have "\<forall>xs' \<in> set (xs # xss). \<forall>ys \<in> set (xs # xss). xs' \<noteq> ys \<longrightarrow> set xs' \<inter> set ys = {}"
    by (simp add: distincts_def) blast
  ultimately show ?L unfolding distincts_def by (intro conjI)
qed

lemma distincts_Cons': "distincts (xs # xss)
   \<longleftrightarrow> xs \<noteq> [] \<and> distinct xs \<and> distincts xss \<and> (\<forall>ys \<in> set xss. set xs \<inter> set ys = {})" (is "?L \<longleftrightarrow> ?R")
 unfolding distincts_Cons by blast

lemma distincts_rev:
  "distincts (map rev xss) \<longleftrightarrow> distincts xss"
  by (simp add: distincts_def distinct_map)

lemma length_distincts:
  assumes "distincts xss"
  shows "length xss = card (set ` set xss)"
  using assms
proof (induct xss)
  case Nil then show ?case by simp
next
  case (Cons xs xss)
  then have "set xs \<notin> set ` set xss"
    using equals0I[of "set xs"] by (auto simp: distincts_Cons disjoint_iff_not_equal )
  with Cons show ?case by (auto simp add: distincts_Cons)
qed

lemma distincts_remove1: "distincts xss \<Longrightarrow> distincts (remove1 xs xss)"
  by (auto simp: distincts_def)

lemma distinct_Cons_remove1:
  "x \<in> set xs \<Longrightarrow> distinct (x # remove1 x xs) = distinct xs"
  by (induct xs) auto

lemma set_Cons_remove1:
  "x \<in> set xs \<Longrightarrow> set (x # remove1 x xs) = set xs"
  by (induct xs) auto

lemma distincts_Cons_remove1:
  "xs \<in> set xss \<Longrightarrow> distincts (xs # remove1 xs xss) = distincts xss"
  by (simp only: distinct_Cons_remove1 set_Cons_remove1 distincts_def)

lemma distincts_inj_on_set:
  assumes "distincts xss" shows "inj_on set (set xss)"
  by (rule inj_onI) (metis assms distincts_def inf.idem set_empty)

lemma distincts_distinct_set:
  assumes "distincts xss" shows "distinct (map set xss)"
  using assms by (auto simp: distinct_map distincts_distinct distincts_inj_on_set)

lemma distincts_distinct_nth:
  assumes "distincts xss" "n < length xss" shows "distinct (xss ! n)"
  using assms by (auto simp: distincts_def)

lemma lists_succ_not_in:
  assumes "x \<notin> (\<Union>xs\<in>set xss. set xs)" shows "lists_succ xss x = x"
  using assms by (induct xss) (auto simp: list_succ_not_in)

lemma lists_succ_in_conv:
  "lists_succ xss x \<in> (\<Union>xs\<in>set xss. set xs) \<longleftrightarrow> x \<in> (\<Union>xs\<in>set xss. set xs)"
  by (induct xss) (auto simp: list_succ_in_conv lists_succ_not_in list_succ_not_in)

lemma lists_succ_in_conv1:
  assumes "A \<inter> (\<Union>xs\<in>set xss. set xs) = {}"
  shows "lists_succ xss x \<in> A \<longleftrightarrow> x \<in> A"
  by (metis Int_iff assms emptyE lists_succ_in_conv lists_succ_not_in)

lemma lists_succ_Cons_pf: "lists_succ (xs # xss) = list_succ xs o lists_succ xss"
  by auto

lemma lists_succ_Nil_pf: "lists_succ [] = id"
  by (simp add: fun_eq_iff)

lemmas lists_succ_simps_pf = lists_succ_Cons_pf lists_succ_Nil_pf

lemma lists_succ_permutes:
  assumes "distincts xss"
  shows "lists_succ xss permutes (\<Union>xs \<in> set xss. set xs)"
  using assms
proof (induction xss)
  case Nil then show ?case by auto
next
  case (Cons xs xss)
  have "list_succ xs permutes (set xs)"
    using Cons by (intro list_succ_permutes) (simp add: distincts_def in_set_member)
  moreover
  have "lists_succ xss permutes (\<Union>ys \<in> set xss. set ys)"
    using Cons by (auto simp: Cons distincts_def)
  ultimately show "lists_succ (xs # xss) permutes (\<Union>ys \<in> set (xs # xss). set ys)"
    using Cons by (auto simp: lists_succ_Cons_pf intro: permutes_compose permutes_subset)
qed

lemma bij_lists_succ: "distincts xss \<Longrightarrow> bij (lists_succ xss)"
  by (induct xss) (auto simp: lists_succ_simps_pf bij_comp bij_list_succ distincts_Cons)

lemma lists_succ_snoc: "lists_succ (xss @ [xs]) = lists_succ xss o list_succ xs"
  by (induct xss) auto

lemma inv_lists_succ_eq:
  assumes "distincts xss"
  shows "inv (lists_succ xss) = lists_succ (rev (map rev xss))"
proof -
  have *: "\<And>f g. inv (\<lambda>b. f (g b)) = inv (f o g)" by (simp add: o_def)
  have **: "lists_succ [] = id" by auto
  show ?thesis
    using assms by (induct xss) (auto simp: * ** lists_succ_snoc lists_succ_Cons_pf o_inv_distrib
      inv_list_succ_eq distincts_Cons bij_list_succ bij_lists_succ)
qed

lemma lists_succ_remove1:
  assumes "distincts xss" "xs \<in> set xss"
  shows "lists_succ (xs # remove1 xs xss) = lists_succ xss"
  using assms
proof (induct xss)
  case Nil then show ?case by simp
next
  case (Cons ys xss)
  show ?case
  proof cases
    assume "xs = ys" then show ?case by simp
  next
    assume "xs \<noteq> ys"
    with Cons.prems have inter: "set xs \<inter> set ys = {}" and "xs \<in> set xss"
      by (auto simp: distincts_Cons)
    have dists:
        "distincts (xs # remove1 xs xss)"
        "distincts (xs # ys # remove1 xs xss)"
      using \<open>distincts (ys # xss)\<close> \<open>xs \<in> set xss\<close> by (auto simp: distincts_def)

    have "list_succ xs \<circ> (list_succ ys \<circ> lists_succ (remove1 xs xss))
        = list_succ ys \<circ> (list_succ xs \<circ> lists_succ (remove1 xs xss))"
      using inter unfolding fun_eq_iff comp_def
      by (subst list_succ_commute) auto
    also have "\<dots> = list_succ ys o (lists_succ (xs # remove1 xs xss))"
      using dists by (simp add: lists_succ_Cons_pf distincts_Cons)
    also have "\<dots> = list_succ ys o lists_succ xss"
      using \<open>xs \<in> set xss\<close> \<open>distincts (ys # xss)\<close>
      by (simp add: distincts_Cons Cons.hyps)
    finally
    show "lists_succ (xs # remove1 xs (ys # xss)) = lists_succ (ys # xss)"
      using Cons dists by (auto simp: lists_succ_Cons_pf distincts_Cons)
  qed
qed

lemma lists_succ_no_order:
  assumes "distincts xss" "distincts yss" "set xss = set yss"
  shows "lists_succ xss = lists_succ yss"
  using assms
proof (induct xss arbitrary: yss)
  case Nil then show ?case by simp
next
  case (Cons xs xss)
  have "xs \<notin> set xss" "xs \<in> set yss" using Cons.prems
    by (auto dest: distincts_distinct)
  have "lists_succ xss = lists_succ (remove1 xs yss)"
    using Cons.prems \<open>xs \<notin> _\<close>
    by (intro Cons.hyps) (auto simp add: distincts_Cons distincts_remove1 distincts_distinct)
  then have "lists_succ (xs # xss) = lists_succ (xs # remove1 xs yss)"
    using Cons.prems \<open>xs \<in> _\<close>
    by (simp add: lists_succ_Cons_pf distincts_Cons_remove1)
  then show ?case
    using Cons.prems \<open>xs \<in> _\<close> by (simp add: lists_succ_remove1)
qed



section \<open>List Orbits\<close>

text \<open>Computes the orbit of @{term x} under @{term f}\<close>
definition orbit_list :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "orbit_list f x \<equiv> iterate 0 (funpow_dist1 f x x) f x"

partial_function (tailrec)
  orbit_list_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "orbit_list_impl f s acc x = (let x' = f x in if x' = s then rev (x # acc) else orbit_list_impl f s (x # acc) x')"

context notes [simp] = length_fold_remove1_le begin
text \<open>Computes the list of orbits\<close>
fun orbits_list :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "orbits_list f [] = []"
| "orbits_list f (x # xs) =
     orbit_list f x # orbits_list f (fold remove1 (orbit_list f x) xs)"

fun orbits_list_impl :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "orbits_list_impl f [] = []"
| "orbits_list_impl f (x # xs) =
     (let fc = orbit_list_impl f x [] x in fc # orbits_list_impl f (fold remove1 fc xs))"

declare orbit_list_impl.simps[code]
end

abbreviation sset :: "'a list list \<Rightarrow> 'a set set" where
  "sset xss \<equiv> set ` set xss"

lemma iterate_funpow_step:
  assumes "f x \<noteq> y" "y \<in> orbit f x"
  shows "iterate 0 (funpow_dist1 f x y) f x = x # iterate 0 (funpow_dist1 f (f x) y) f (f x)"
proof -
  from assms have A: "y \<in> orbit f (f x)" by (simp add: orbit_step)
  have "iterate 0 (funpow_dist1 f x y) f x = x # iterate 1 (funpow_dist1 f x y) f x" (is "_ = _ # ?it")
    unfolding iterate_def by (rewrite in "\<hole> = _" upt_conv_Cons) auto
  also have "?it = map (\<lambda>n. (f ^^ n) x) (map Suc [0..<funpow_dist f (f x) y])"
    unfolding iterate_def map_Suc_upt by simp
  also have "\<dots> = map (\<lambda>n. (f ^^ n) (f x)) [0..<funpow_dist f (f x) y]"
    by (simp add: funpow_swap1)
  also have "\<dots> = iterate 0 (funpow_dist1 f (f x) y) f (f x)"
    unfolding iterate_def
    unfolding iterate_def by (simp add: funpow_dist_step[OF assms(1) A])
  finally show ?thesis .
qed

lemma orbit_list_impl_conv:
  assumes "y \<in> orbit f x"
  shows "orbit_list_impl f y acc x = rev acc @ iterate 0 (funpow_dist1 f x y) f x"
  using assms
proof (induct n\<equiv>"funpow_dist1 f x y" arbitrary: x acc)
  case (Suc x)

  show ?case
  proof cases
    assume "f x = y"
    then show ?thesis by (subst orbit_list_impl.simps) (simp add: Let_def iterate_def funpow_dist_0)
  next
    assume not_y :"f x \<noteq> y"

    have y_in_succ: "y \<in> orbit f (f x)"
      by (intro orbit_step Suc.prems not_y)

    have "orbit_list_impl f y acc x = orbit_list_impl f y (x # acc) (f x)"
      using not_y by (subst orbit_list_impl.simps) simp
    also have "\<dots> = rev (x # acc) @ iterate 0 (funpow_dist1 f (f x) y) f (f x)" (is "_ = ?rev @ ?it")
      by (intro Suc funpow_dist_step not_y y_in_succ)
    also have "\<dots> = rev acc @ iterate 0 (funpow_dist1 f x y) f x"
      using not_y Suc.prems by (simp add: iterate_funpow_step)
    finally show ?thesis .
  qed
qed

lemma orbit_list_conv_impl:
  assumes "x \<in> orbit f x"
  shows "orbit_list f x = orbit_list_impl f x [] x"
  unfolding orbit_list_impl_conv[OF assms] orbit_list_def by simp


lemma set_orbit_list:
  assumes "x \<in> orbit f x"
  shows "set (orbit_list f x) = orbit f x"
  by (simp add: orbit_list_def orbit_conv_funpow_dist1[OF assms] set_iterate)

lemma set_orbit_list':
  assumes "permutation f" shows "set (orbit_list f x) = orbit f x"
  using assms by (simp add: permutation_self_in_orbit set_orbit_list)

lemma distinct_orbit_list:
  assumes "x \<in> orbit f x"
  shows "distinct (orbit_list f x)"
  by (simp del: upt_Suc add: orbit_list_def iterate_def distinct_map inj_on_funpow_dist1[OF assms])

lemma distinct_orbit_list':
  assumes "permutation f" shows "distinct (orbit_list f x)"
  using assms by (simp add: permutation_self_in_orbit distinct_orbit_list)

lemma orbits_list_conv_impl:
  assumes "permutation f"
  shows "orbits_list f xs = orbits_list_impl f xs"
proof (induct "length xs" arbitrary: xs rule: less_induct)
  case less show ?case
    using assms by (cases xs) (auto simp: assms less less_Suc_eq_le length_fold_remove1_le
      orbit_list_conv_impl permutation_self_in_orbit Let_def)
qed

lemma orbit_list_not_nil[simp]: "orbit_list f x \<noteq> []"
  by (simp add: orbit_list_def)

lemma sset_orbits_list:
  assumes "permutation f" shows "sset (orbits_list f xs) = (orbit f) ` set xs"
proof (induct "length xs" arbitrary: xs rule: less_induct)
  case less
  show ?case
  proof (cases xs)
    case Nil then show ?thesis by simp
  next
    case (Cons x' xs')
    let ?xs'' = "fold remove1 (orbit_list f x') xs'"
    have A: "sset (orbits_list f ?xs'') = orbit f ` set ?xs''"
      using Cons by (simp add: less_Suc_eq_le length_fold_remove1_le less.hyps)
    have B: "set (orbit_list f x') = orbit f x'"
      by (rule set_orbit_list) (simp add: permutation_self_in_orbit assms)

    have "orbit f ` set (fold remove1 (orbit_list f x') xs') \<subseteq> orbit f ` set xs'"
      using set_fold_remove1[of _ xs'] by auto
    moreover
    have "orbit f ` set xs' - {orbit f x'} \<subseteq> (orbit f ` set (fold remove1 (orbit_list f x') xs'))" (is "?L \<subseteq> ?R")
    proof
      fix A assume "A \<in> ?L"
      then obtain y where "A = orbit f y" "y \<in> set xs'" by auto
      have "A \<noteq> orbit f x'" using \<open>A \<in> ?L\<close> by auto
      from \<open>A = _\<close> \<open>A \<noteq> _\<close> have "y \<notin> orbit f x'"
        by (meson assms cyclic_on_orbit orbit_cyclic_eq3 permutation_permutes)
      with \<open>y \<in> _\<close> have "y \<in> set (fold remove1 (orbit_list f x') xs')"
        by (auto simp: set_fold_remove1' set_orbit_list permutation_self_in_orbit assms)
      then show "A \<in> ?R" using \<open>A = _\<close> by auto
    qed
    ultimately
    show ?thesis by (auto simp: A B Cons)
  qed
qed



subsection \<open>Relation to @{term cyclic_on}\<close>

lemma list_succ_orbit_list:
  assumes "s \<in> orbit f s" "\<And>x. x \<notin> orbit f s \<Longrightarrow> f x = x"
  shows "list_succ (orbit_list f s) = f"
proof -
  have "distinct (orbit_list f s)" "\<And>x. x \<notin> set (orbit_list f s) \<Longrightarrow> x = f x"
    using assms by (simp_all add: distinct_orbit_list set_orbit_list)
  moreover
  have "\<And>i. i < length (orbit_list f s) \<Longrightarrow> orbit_list f s ! (Suc i mod length (orbit_list f s)) = f (orbit_list f s ! i)"
    using funpow_dist1_prop[OF \<open>s \<in> orbit f s\<close>] by (auto simp: orbit_list_def funpow_mod_eq)
  ultimately show ?thesis
    by (auto simp: list_succ_def fun_eq_iff)
qed

lemma list_succ_funpow_conv:
  assumes A: "distinct xs" "x \<in> set xs"
  shows "(list_succ xs ^^ n) x = xs ! ((index xs x + n) mod length xs)"
proof -
  have "xs \<noteq> []" using assms by auto
  then show ?thesis
    by (induct n) (auto simp: hd_conv_nth A index_nth_id list_succ_def mod_simps)
qed

lemma orbit_list_succ:
  assumes "distinct xs" "x \<in> set xs"
  shows "orbit (list_succ xs) x = set xs"
proof (intro set_eqI iffI)
  fix y assume "y \<in> orbit (list_succ xs) x"
  then show "y \<in> set xs"
    by induct (auto simp: list_succ_in_conv \<open>x \<in> set xs\<close>)
next
  fix y assume "y \<in> set xs"
  moreover
  { fix i j have "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> \<exists>n. xs ! j = xs ! ((i + n) mod length xs)"
      using assms by (auto simp: exI[where x="j + (length xs - i)"])
  }
  ultimately
  show "y \<in> orbit (list_succ xs) x"
    using assms by (auto simp: orbit_altdef_permutation permutation_list_succ list_succ_funpow_conv index_nth_id in_set_conv_nth)
qed

lemma cyclic_on_list_succ:
  assumes "distinct xs" "xs \<noteq> []" shows "cyclic_on (list_succ xs) (set xs)"
  using assms last_in_set by (auto simp: cyclic_on_def orbit_list_succ)

lemma obtain_orbit_list_func:
  assumes "s \<in> orbit f s" "\<And>x. x \<notin> orbit f s \<Longrightarrow> f x = x"
  obtains xs where "f = list_succ xs" "set xs = orbit f s" "distinct xs" "hd xs = s"
proof -
  { from assms have "f = list_succ (orbit_list f s)" by (simp add: list_succ_orbit_list)
    moreover
    have "set (orbit_list f s) = orbit f s" "distinct (orbit_list f s)"
      by (auto simp: set_orbit_list distinct_orbit_list assms)
    moreover have "hd (orbit_list f s) = s"
      by (simp add: orbit_list_def iterate_def hd_map del: upt_Suc)
    ultimately have "\<exists>xs. f = list_succ xs \<and> set xs = orbit f s \<and> distinct xs \<and> hd xs = s" by blast
  } then show ?thesis by (metis that)
qed

lemma cyclic_on_obtain_list_succ:
  assumes "cyclic_on f S" "\<And>x. x \<notin> S \<Longrightarrow> f x = x"
  obtains xs where "f = list_succ xs" "set xs = S" "distinct xs"
proof -
  from assms obtain s where s: "s \<in> orbit f s" "\<And>x. x \<notin> orbit f s \<Longrightarrow> f x = x"  "S = orbit f s"
    by (auto simp: cyclic_on_def)
  then show ?thesis by (metis that obtain_orbit_list_func)
qed

lemma cyclic_on_obtain_list_succ':
  assumes "cyclic_on f S" "f permutes S"
  obtains xs where "f = list_succ xs" "set xs = S" "distinct xs"
  using assms unfolding permutes_def by (metis cyclic_on_obtain_list_succ)

lemma list_succ_unique:
  assumes "s \<in> orbit f s" "\<And>x. x \<notin> orbit f s \<Longrightarrow> f x = x"
  shows "\<exists>!xs. f = list_succ xs \<and> distinct xs \<and> hd xs = s \<and> set xs = orbit f s"
proof -
  from assms obtain xs where xs: "f = list_succ xs" "distinct xs" "hd xs = s" "set xs = orbit f s" 
    by (rule obtain_orbit_list_func)
  moreover
  { fix zs
    assume A: "f = list_succ zs" "distinct zs" "hd zs = s" "set zs = orbit f s"
    then have "zs \<noteq> []" using \<open>s \<in> orbit f s\<close> by auto
    from \<open>distinct xs\<close> \<open>distinct zs\<close> \<open>set xs = orbit f s\<close> \<open>set zs = orbit f s\<close>
    have len: "length xs = length zs" by (metis distinct_card)

    { fix n assume "n < length xs"
      then have "zs ! n = xs ! n"
      proof (induct n)
        case 0 with A xs \<open>zs \<noteq> []\<close> show ?case by (simp add: hd_conv_nth nth_rotate_conv_nth)
      next
        case (Suc n)
        then have "list_succ zs (zs ! n) = list_succ xs (xs! n)"
          using \<open>f = list_succ xs\<close> \<open>f = list_succ zs\<close> by simp
        with \<open>Suc n < _\<close> show ?case
          by (simp add:list_succ_nth len \<open>distinct xs\<close> \<open>distinct zs\<close>)
      qed }
    then have "zs = xs" by (metis len nth_equalityI) }
  ultimately show ?thesis by metis
qed

lemma distincts_orbits_list:
  assumes "distinct as" "permutation f"
  shows "distincts (orbits_list f as)"
  using assms(1)
proof (induct "length as" arbitrary: as rule: less_induct)
  case less
  show ?case
  proof (cases as)
    case Nil then show ?thesis by simp
  next
    case (Cons a as')
    let ?as' = "fold remove1 (orbit_list f a) as'"
    from Cons less.prems have A: "distincts (orbits_list f (fold remove1 (orbit_list f a) as'))"
      by (intro less) (auto simp: distinct_fold_remove1 length_fold_remove1_le less_Suc_eq_le)

    have B: "set (orbit_list f a) \<inter> \<Union>(sset (orbits_list f (fold remove1 (orbit_list f a) as'))) = {}"
    proof -
      have "orbit f a \<inter> set (fold remove1 (orbit_list f a) as') = {}"
        using assms less.prems Cons by (simp add: set_fold_remove1_distinct set_orbit_list')
      then have "orbit f a \<inter> \<Union> (orbit f ` set (fold remove1 (orbit_list f a) as')) = {}"
        by auto (metis assms(2) cyclic_on_orbit disjoint_iff_not_equal permutation_self_in_orbit[OF assms(2)] orbit_cyclic_eq3 permutation_permutes)
      then show ?thesis using assms
      by (auto simp: set_orbit_list' sset_orbits_list disjoint_iff_not_equal)
    qed
    show ?thesis
      using A B assms by (auto simp: distincts_Cons Cons distinct_orbit_list')
  qed
qed

lemma cyclic_on_lists_succ':
  assumes "distincts xss"
  shows "A \<in> sset xss \<Longrightarrow> cyclic_on (lists_succ xss) A"
  using assms
proof (induction xss arbitrary: A)
  case Nil then show ?case by auto
next
  case (Cons xs xss A)
  then have inter: "set xs \<inter> (\<Union>ys\<in>set xss. set ys) = {}" by (auto simp: distincts_Cons)

  note pcp[OF _ _ inter] = permutes_comp_preserves_cyclic1 permutes_comp_preserves_cyclic2
  from Cons show "cyclic_on (lists_succ (xs # xss)) A"
    by (cases "A = set xs")
      (auto intro: pcp simp: cyclic_on_list_succ list_succ_permutes
        lists_succ_permutes lists_succ_Cons_pf distincts_Cons)
qed

lemma cyclic_on_lists_succ:
  assumes "distincts xss"
  shows "\<And>xs. xs \<in> set xss \<Longrightarrow> cyclic_on (lists_succ xss) (set xs)"
  using assms by (auto intro: cyclic_on_lists_succ')

lemma permutes_as_lists_succ:
  assumes "distincts xss"
  assumes ls_eq: "\<And>xs. xs \<in> set xss \<Longrightarrow> list_succ xs = perm_restrict f (set xs)"
  assumes "f permutes (\<Union>(sset xss))"
  shows "f = lists_succ xss"
  using assms
proof (induct xss arbitrary: f)
  case Nil then show ?case by simp
next
  case (Cons xs xss)
  let ?sets = "\<lambda>xss. \<Union>ys \<in> set xss. set ys"

  have xs: "distinct xs" "xs \<noteq> []" using Cons by (auto simp: distincts_Cons)

  have f_xs: "perm_restrict f (set xs) = list_succ xs"
    using Cons by simp

  have co_xs: "cyclic_on (perm_restrict f (set xs)) (set xs)"
    unfolding f_xs using xs by (rule cyclic_on_list_succ)

  have perm_xs: "perm_restrict f (set xs) permutes set xs"
    unfolding f_xs using \<open>distinct xs\<close> by (rule list_succ_permutes)

  have perm_xss: "perm_restrict f (?sets xss) permutes (?sets xss)"
  proof -
    have "perm_restrict f (?sets (xs # xss) - set xs) permutes (?sets (xs # xss) - set xs)"
      using Cons co_xs by (intro perm_restrict_diff_cyclic) (auto simp: cyclic_on_perm_restrict)
    also have "?sets (xs # xss) - set xs = ?sets xss"
      using Cons by (auto simp: distincts_Cons)
    finally show ?thesis .
  qed

  have f_xss: "perm_restrict f (?sets xss) = lists_succ xss"
  proof -
    have *: "\<And>xs. xs \<in> set xss \<Longrightarrow> ((\<Union>x\<in>set xss. set x) \<inter> set xs) = set xs"
      by blast
    with perm_xss Cons.prems show ?thesis
      by (intro Cons.hyps) (auto simp: distincts_Cons perm_restrict_perm_restrict *)
  qed

  from Cons.prems show "f = lists_succ (xs # xss)"
    by (simp add: lists_succ_Cons_pf distincts_Cons f_xss[symmetric]
      perm_restrict_union perm_xs perm_xss)
qed

lemma cyclic_on_obtain_lists_succ:
  assumes
    permutes: "f permutes S" and
    S: "S = \<Union>(sset css)" and
    dists: "distincts css" and
    cyclic: "\<And>cs. cs \<in> set css \<Longrightarrow> cyclic_on f (set cs)"
  obtains xss where "f = lists_succ xss" "distincts xss" "map set xss = map set css" "map hd xss = map hd css"
proof -
  let ?fc = "\<lambda>cs. perm_restrict f (set cs)"
  define some_list where "some_list cs = (SOME xs. ?fc cs = list_succ xs \<and> set xs = set cs \<and> distinct xs \<and> hd xs = hd cs)" for cs
  { fix cs assume "cs \<in> set css"
    then have "cyclic_on (?fc cs) (set cs)" "\<And>x. x \<notin> set cs \<Longrightarrow> ?fc cs x = x" "hd cs \<in> set cs"
      using cyclic dists by (auto simp add: cyclic_on_perm_restrict perm_restrict_def distincts_def)
    then have "hd cs \<in> orbit (?fc cs) (hd cs)"  "\<And>x. x \<notin> orbit (?fc cs) (hd cs) \<Longrightarrow> ?fc cs x = x" "hd cs \<in> set cs" "set cs = orbit (?fc cs) (hd cs)"
      by (auto simp: cyclic_on_alldef)
    then have "\<exists>xs. ?fc cs = list_succ xs \<and> set xs = set cs \<and> distinct xs \<and> hd xs = hd cs"
      by (metis obtain_orbit_list_func)
    then have "?fc cs = list_succ (some_list cs) \<and> set (some_list cs) = set cs \<and> distinct (some_list cs) \<and> hd (some_list cs) = hd cs"
      unfolding some_list_def by (rule someI_ex)
    then have "?fc cs = list_succ (some_list cs)" "set (some_list cs) = set cs" "distinct (some_list cs)" "hd (some_list cs) = hd cs"
      by auto
  } note sl_cs  = this

  have "\<And>cs. cs \<in> set css \<Longrightarrow> cs \<noteq> []" using dists by (auto simp: distincts_def)
  then have some_list_ne: "\<And>cs. cs \<in> set css \<Longrightarrow> some_list cs \<noteq> []"
    by (metis set_empty sl_cs(2))

  have set: "map set (map some_list css) = map set css" "map hd (map some_list css) = map hd css"
    using sl_cs(2,4) by (auto simp add: map_idI)

  have distincts: "distincts (map some_list css)"
  proof -
    have c_dist: "\<And>xs ys. \<lbrakk>xs\<in>set css; ys\<in>set css; xs \<noteq> ys\<rbrakk> \<Longrightarrow> set xs \<inter> set ys = {}"
      using dists by (auto simp: distincts_def)

    have "distinct (map some_list css)"
    proof -
      have "inj_on some_list (set css)"
        using sl_cs(2) c_dist by (intro inj_onI) (metis inf.idem set_empty) 
      with \<open>distincts css\<close> show ?thesis
        by (auto simp: distincts_distinct distinct_map)
    qed
    moreover
    have "\<forall>xs\<in>set (map some_list css). distinct xs \<and> xs \<noteq> []"
      using sl_cs(3) some_list_ne by auto
    moreover
    from c_dist have "(\<forall>xs\<in>set (map some_list css). \<forall>ys\<in>set (map some_list css). xs \<noteq> ys \<longrightarrow> set xs \<inter> set ys = {})"
      using sl_cs(2) by auto
    ultimately
    show ?thesis by (simp add: distincts_def)
  qed

  have f: "f = lists_succ (map some_list css)"
    using distincts
  proof (rule permutes_as_lists_succ)
    fix xs assume "xs \<in> set (map some_list css)"
    then show "list_succ xs = perm_restrict f (set xs)"
      using sl_cs(1) sl_cs(2) by auto
  next
    have "S = (\<Union>xs\<in>set (map some_list css). set xs)"
      using S sl_cs(2) by auto
    with permutes show "f permutes \<Union>(sset (map some_list css))"
      by simp
  qed

  from f distincts set  show ?thesis ..
qed


subsection \<open>Permutations of a List\<close>

lemma length_remove1_less:
  assumes "x \<in> set xs" shows "length (remove1 x xs) < length xs"
proof -
  from assms have "0 < length xs" by auto
  with assms show ?thesis by (auto simp: length_remove1)
qed
context notes [simp] = length_remove1_less begin
fun permutations :: "'a list \<Rightarrow> 'a list list" where
  permutations_Nil: "permutations [] = [[]]"
| permutations_Cons:
    "permutations xs = [y # ys. y <- xs, ys <- permutations (remove1 y xs)]"
end

declare permutations_Cons[simp del]

text \<open>
  The function above returns all permutations of a list. The function below computes
  only those which yield distinct cyclic permutation functions (cf. @{term list_succ}).
\<close>

fun cyc_permutations :: "'a list \<Rightarrow> 'a list list" where
  "cyc_permutations [] = [[]]"
| "cyc_permutations (x # xs) = map (Cons x) (permutations xs)"



lemma nil_in_permutations[simp]: "[] \<in> set (permutations xs) \<longleftrightarrow> xs = []"
  by (induct xs) (auto simp: permutations_Cons)

lemma permutations_not_nil:
  assumes "xs \<noteq> []"
  shows "permutations xs = concat (map (\<lambda>x. map ((#) x) (permutations (remove1 x xs))) xs)"
  using assms by (cases xs) (auto simp: permutations_Cons)

lemma set_permutations_step:
  assumes "xs \<noteq> []"
  shows "set (permutations xs) = (\<Union>x \<in> set xs. Cons x ` set (permutations (remove1 x xs)))"
  using assms by (cases xs) (auto simp: permutations_Cons)

lemma in_set_permutations:
  assumes "distinct xs"
  shows "ys \<in> set (permutations xs) \<longleftrightarrow> distinct ys \<and> set xs = set ys" (is "?L xs ys \<longleftrightarrow> ?R xs ys")
  using assms
proof (induct "length xs" arbitrary: xs ys)
  case 0 then show ?case by auto
next
  case (Suc n)
  then have "xs \<noteq> []" by auto

  show ?case
  proof
    assume "?L xs ys"
    then obtain y ys' where "ys = y # ys'" "y \<in> set xs" "ys' \<in> set (permutations (remove1 (hd ys) xs))"
      using \<open>xs \<noteq> []\<close> by (auto simp: permutations_not_nil)
    moreover
    then have "?R (remove1 y xs) ys'"
      using Suc.prems Suc.hyps(2) by (intro Suc.hyps(1)[THEN iffD1]) (auto simp: length_remove1)
    ultimately show "?R xs ys"
      using Suc by auto
  next
    assume "?R xs ys"
    with \<open>xs \<noteq> []\<close> obtain y ys' where "ys = y # ys'" "y \<in> set xs" by (cases ys) auto
    moreover
    then have "ys' \<in> set (permutations (remove1 y xs))"
      using Suc \<open>?R xs ys\<close> by (intro Suc.hyps(1)[THEN iffD2]) (auto simp: length_remove1)
    ultimately
    show "?L xs ys"
      using \<open>xs \<noteq> []\<close> by (auto simp: permutations_not_nil)
  qed
qed

lemma in_set_cyc_permutations:
  assumes "distinct xs"
  shows "ys \<in> set (cyc_permutations xs) \<longleftrightarrow> distinct ys \<and> set xs = set ys \<and> hd ys = hd xs" (is "?L xs ys \<longleftrightarrow> ?R xs ys")
proof (cases xs)
  case (Cons x xs) with assms show ?thesis
    by (cases ys) (auto simp: in_set_permutations intro!: imageI)
qed auto

lemma in_set_cyc_permutations_obtain:
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  obtains n where "rotate n ys \<in> set (cyc_permutations xs)"
proof (cases xs)
  case Nil with assms have "rotate 0 ys \<in> set (cyc_permutations xs)" by auto
  then show ?thesis ..
next
  case (Cons x xs')
  let ?ys' = "rotate (index ys x) ys"
  have "ys \<noteq> []" "x \<in> set ys"
    using Cons assms by auto
  then have "distinct ?ys' \<and> set xs = set ?ys' \<and> hd ?ys' = hd xs"
    using assms Cons by (auto simp add: hd_rotate_conv_nth)
  with \<open>distinct xs\<close> have "?ys' \<in> set (cyc_permutations xs)"
    by (rule in_set_cyc_permutations[THEN iffD2])
  then show ?thesis ..
qed

lemma list_succ_set_cyc_permutations:
  assumes "distinct xs" "xs \<noteq> []"
  shows "list_succ ` set (cyc_permutations xs) = {f. f permutes set xs \<and> cyclic_on f (set xs)}" (is "?L = ?R")
proof (intro set_eqI iffI)
  fix f assume "f \<in> ?L"
  moreover have "\<And>ys. set xs = set ys \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ys \<noteq> []" by auto
  ultimately show "f \<in> ?R"
    using assms by (auto simp: in_set_cyc_permutations list_succ_permutes cyclic_on_list_succ)
next
  fix f assume "f \<in> ?R"
  then obtain ys where ys: "list_succ ys = f" "distinct ys" "set ys = set xs"
    by (auto elim: cyclic_on_obtain_list_succ')
  moreover
  with \<open>distinct xs\<close> obtain n where "rotate n ys \<in> set (cyc_permutations xs)"
    by (auto elim: in_set_cyc_permutations_obtain)
  then have "list_succ (rotate n ys) \<in> ?L" by simp
  ultimately
  show "f \<in> ?L" by simp
qed


subsection \<open>Enumerating Permutations from List Orbits\<close>

definition cyc_permutationss :: "'a list list \<Rightarrow> 'a list list list" where
  "cyc_permutationss = product_lists o map cyc_permutations"

lemma cyc_permutationss_Nil[simp]: "cyc_permutationss [] = [[]]"
  by (auto simp: cyc_permutationss_def)

lemma in_set_cyc_permutationss:
  assumes "distincts xss"
  shows "yss \<in> set (cyc_permutationss xss) \<longleftrightarrow> distincts yss \<and> map set xss = map set yss \<and> map hd xss = map hd yss"
proof -
  { assume A: "list_all2 (\<lambda>x ys. x \<in> set ys) yss (map cyc_permutations xss)"
    then have "length yss = length xss" by (auto simp: list_all2_lengthD)
    then have "\<Union>(sset xss) = \<Union>(sset yss)" "distincts yss" "map set xss = map set yss" "map hd xss = map hd yss"
      using A assms
      by (induct yss xss rule: list_induct2) (auto simp: distincts_Cons in_set_cyc_permutations)
  } note X = this
  { assume A: "distincts yss" "map set xss = map set yss" "map hd xss = map hd yss"
    then have "length yss = length xss" by (auto dest: map_eq_imp_length_eq)
    then have "list_all2 (\<lambda>x ys. x \<in> set ys) yss (map cyc_permutations xss)"
      using A assms
      by (induct yss xss rule: list_induct2) (auto simp: distincts_Cons in_set_cyc_permutations)
  } note Y = this
  show "?thesis"
    unfolding cyc_permutationss_def
    by (auto simp: product_lists_set intro: X Y)
qed

lemma lists_succ_set_cyc_permutationss:
  assumes "distincts xss"
  shows "lists_succ ` set (cyc_permutationss xss) = {f. f permutes \<Union>(sset xss) \<and> (\<forall>c \<in> sset xss. cyclic_on f c)}" (is "?L = ?R")
  using assms
proof (intro set_eqI iffI)
  fix f assume "f \<in> ?L"
  then obtain yss where "yss \<in> set (cyc_permutationss xss)" "f = lists_succ yss" by (rule imageE)
  moreover
  from \<open>yss \<in> _\<close> assms have "set (map set xss) = set (map set yss)"
    by (auto simp: in_set_cyc_permutationss)
  then have "sset xss = sset yss" by simp
  ultimately
  show "f \<in> ?R"
    using assms
  by (auto simp: in_set_cyc_permutationss cyclic_on_lists_succ') (metis lists_succ_permutes)
next
  fix f assume "f \<in> ?R"
  then have "f permutes \<Union>(sset xss)" "\<And>cs. cs \<in> set xss \<Longrightarrow> cyclic_on f (set cs)"
    by auto
  from this(1) refl assms this(2)
  obtain yss where "f = lists_succ yss" "distincts yss" "map set yss = map set xss" "map hd yss = map hd xss"
    by (rule cyclic_on_obtain_lists_succ)
  with assms show "f \<in> ?L" by (auto intro!: imageI simp: in_set_cyc_permutationss)
qed


subsection \<open>Lists of Permutations\<close>

definition permutationss :: "'a list list \<Rightarrow> 'a list list list" where
  "permutationss = product_lists o map permutations"

lemma permutationss_Nil[simp]: "permutationss [] = [[]]"
  by (auto simp: permutationss_def)

lemma permutationss_Cons:
  "permutationss (xs # xss) = concat (map (\<lambda>ys. map (Cons ys) (permutationss xss)) (permutations xs))"
  by (auto simp: permutationss_def)

lemma in_set_permutationss:
  assumes "distincts xss"
  shows "yss \<in> set (permutationss xss) \<longleftrightarrow> distincts yss \<and> map set xss = map set yss"
proof -
  { assume A: "list_all2 (\<lambda>x ys. x \<in> set ys) yss (map permutations xss)"
    then have "length yss = length xss" by (auto simp: list_all2_lengthD)
    then have "\<Union>(sset xss) = \<Union>(sset yss)" "distincts yss" "map set xss = map set yss"
      using A assms
      by (induct yss xss rule: list_induct2) (auto simp: distincts_Cons in_set_permutations)
  } note X = this
  { assume A: "distincts yss" "map set xss = map set yss"
    then have "length yss = length xss" by (auto dest: map_eq_imp_length_eq)
    then have "list_all2 (\<lambda>x ys. x \<in> set ys) yss (map permutations xss)"
      using A assms
      by (induct yss xss rule: list_induct2) (auto simp: in_set_permutations distincts_Cons)
  } note Y = this
  show "?thesis"
    unfolding permutationss_def
    by (auto simp: product_lists_set intro: X Y)
qed

lemma set_permutationss:
  assumes "distincts xss"
  shows "set (permutationss xss) = {yss. distincts yss \<and> map set xss = map set yss}"
  using in_set_permutationss[OF assms] by blast

lemma permutationss_complete:
  assumes "distincts xss" "distincts yss" "xss \<noteq> []"
    and "set ` set xss = set ` set yss"
  shows "set yss \<in> set ` set (permutationss xss)"
proof -
  have "length xss = length yss"
    using assms by (simp add: length_distincts)
  from \<open>sset xss = _\<close>
  have "\<exists>yss'. set yss' = set yss \<and> map set yss' = map set xss"
    using assms(1-2)
  proof (induct xss arbitrary: yss)
    case Nil then show ?case by simp
  next
    case (Cons xs xss)
    from \<open>sset (xs # xss) = sset yss\<close>
    obtain ys where ys: "ys \<in> set yss" "set ys = set xs"
      by auto (metis imageE insertI1)
    with \<open>distincts yss\<close> have "set ys \<notin> sset (remove1 ys yss)"
      by (fastforce simp: distincts_def)
    moreover
    from \<open>distincts (xs # xss)\<close> have "set xs \<notin> sset xss"
      by (fastforce simp: distincts_def)
    ultimately have "sset xss = sset (remove1 ys yss)"
      using \<open>distincts yss\<close> \<open>sset (xs # xss) = sset yss\<close>
      apply (auto simp: distincts_distinct \<open>set ys = set xs\<close>[symmetric])
      apply (smt Diff_insert_absorb \<open>ys \<in> set yss\<close> image_insert insert_Diff rev_image_eqI)
      by (metis \<open>ys \<in> set yss\<close> image_eqI insert_Diff insert_iff)
    then obtain yss' where "set yss' = set (remove1 ys yss) \<and> map set yss' = map set xss"
      using Cons by atomize_elim (auto simp: distincts_Cons distincts_remove1)
    then have "set (ys # yss') = set yss \<and> map set (ys # yss') = map set (xs # xss)"
      using ys set_remove1_eq \<open>distincts yss\<close> by (auto simp: distincts_distinct)
    then show ?case ..
  qed
  then obtain yss' where "set yss' = set yss" "map set yss' = map set xss" by blast
  then have "distincts yss'" using \<open>distincts xss\<close> \<open>distincts yss\<close>
    unfolding distincts_def
    by simp_all (metis \<open>length xss = length yss\<close> card_distinct distinct_card length_map)
  then have "set yss' \<in> set ` set (permutationss xss)"
    using \<open>distincts xss\<close> \<open>map set yss' = _\<close>
    by (auto simp: set_permutationss)
  then show ?thesis using \<open>set yss' = _\<close> by auto
qed

lemma permutations_complete: (* could generalize with multi-sets *)
  assumes "distinct xs" "distinct ys" "set xs = set ys"
  shows "ys \<in> set (permutations xs)"
  using assms
proof (induct "length xs" arbitrary: xs ys)
  case 0 then show ?case by simp
next
  case (Suc n)
  from Suc.hyps have "xs \<noteq> []" by auto
  then obtain y ys' where [simp]: "ys = y # ys'" "y \<in> set xs" using Suc.prems by (cases ys) auto
  have "ys' \<in> set (permutations (remove1 y xs))"
    using Suc.prems \<open>Suc n = _\<close> by (intro Suc.hyps) (simp_all add: length_remove1 )
  then show ?case using \<open>xs \<noteq> []\<close> by (auto simp: set_permutations_step)
qed


end
