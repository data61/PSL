subsection Precomputation

text \<open>This theory contains precomputation functions, which take another function $f$ and a 
  finite set of inputs, and provide the same function $f$ as output, except that now all
  values $f\ i$ are precomputed if $i$ is contained in the set of finite inputs.\<close>

theory Precomputation
imports 
  Containers.RBT_Set2
  "HOL-Library.RBT_Mapping"
begin
  
lemma lookup_tabulate: "x \<in> set xs \<Longrightarrow> Mapping.lookup (Mapping.tabulate xs f) x = Some (f x)"
  by (transfer, simp add: map_of_map_Pair_key)

lemma lookup_tabulate2: "Mapping.lookup (Mapping.tabulate xs f) x = Some y \<Longrightarrow> y = f x"
  by transfer (metis map_of_map_Pair_key option.distinct(1) option.sel)

definition memo_int :: "int \<Rightarrow> int \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a)" where
  "memo_int low up f \<equiv> let m = Mapping.tabulate [low .. up] f
     in (\<lambda> x. if x \<ge> low \<and> x \<le> up then the (Mapping.lookup m x) else f x)"

lemma memo_int[simp]: "memo_int low up f = f"
proof (intro ext)
  fix x
  show "memo_int low up f x = f x"
  proof (cases "x \<ge> low \<and> x \<le> up")
    case False
    thus ?thesis unfolding memo_int_def by auto
  next
    case True
    from True have x: "x \<in> set [low .. up]" by auto
    with True lookup_tabulate[OF this, of f]
    show ?thesis unfolding memo_int_def by auto
  qed
qed

definition memo_nat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "memo_nat low up f \<equiv> let m = Mapping.tabulate [low ..< up] f
     in (\<lambda> x. if x \<ge> low \<and> x < up then the (Mapping.lookup m x) else f x)"

lemma memo_nat[simp]: "memo_nat low up f = f"
proof (intro ext)
  fix x
  show "memo_nat low up f x = f x"
  proof (cases "x \<ge> low \<and> x < up")
    case False
    thus ?thesis unfolding memo_nat_def by auto
  next
    case True
    from True have x: "x \<in> set [low ..< up]" by auto
    with True lookup_tabulate[OF this, of f]
    show ?thesis unfolding memo_nat_def by auto
  qed
qed

definition memo :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "memo xs f \<equiv> let m = Mapping.tabulate xs f
     in (\<lambda> x. case Mapping.lookup m x of None \<Rightarrow> f x | Some y \<Rightarrow> y)"

lemma memo[simp]: "memo xs f = f"
proof (intro ext)
  fix x
  show "memo xs f x = f x"
  proof (cases "Mapping.lookup (Mapping.tabulate xs f) x")
    case None
    thus ?thesis unfolding memo_def by auto
  next
    case (Some y)
    with lookup_tabulate2[OF this]
    show ?thesis unfolding memo_def by auto
  qed
qed


end
