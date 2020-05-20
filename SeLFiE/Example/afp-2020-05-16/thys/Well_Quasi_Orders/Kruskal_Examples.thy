theory Kruskal_Examples
imports Kruskal
begin

datatype 'a tree = Node 'a "'a tree list"

fun node
where
  "node (Node f ts) = (f, length ts)"

fun succs
where
  "succs (Node f ts) = ts"

inductive_set trees for A
where
  "f \<in> A \<Longrightarrow> \<forall>t \<in> set ts. t \<in> trees A \<Longrightarrow> Node f ts \<in> trees A"

lemma [simp]:
  "trees UNIV = UNIV"
proof -
  { fix t :: "'a tree"
    have "t \<in> trees UNIV"
      by (induct t) (auto intro: trees.intros) }
  then show ?thesis by auto
qed

interpretation kruskal_tree_tree: kruskal_tree "A \<times> UNIV" Node node succs "trees A" for A
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: trees.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_tree_tree.almost_full_on_trees
thm kruskal_tree_tree.kruskal

definition "tree_emb A P = kruskal_tree_tree.emb A (prod_le P (\<lambda>_ _. True))"

lemma wqo_on_trees:
  assumes "wqo_on P A"
  shows "wqo_on (tree_emb A P) (trees A)"
  using wqo_on_Sigma [OF assms wqo_on_UNIV, THEN kruskal_tree_tree.kruskal]
  by (simp add: tree_emb_def)

text \<open>
If the type @{typ "'a"} is well-quasi-ordered by \<open>P\<close>, then trees of type @{typ "'a tree"}
are well-quasi-ordered by the homeomorphic embedding relation.
\<close>
instantiation tree :: (wqo) wqo
begin
definition "s \<le> t \<longleftrightarrow> tree_emb UNIV (\<le>) s t"
definition "(s :: 'a tree) < t \<longleftrightarrow> s \<le> t \<and> \<not> (t \<le> s)"

instance
  by (rule class.wqo.of_class.intro)
     (auto simp: less_eq_tree_def [abs_def] less_tree_def [abs_def]
           intro: wqo_on_trees [of _ UNIV, simplified])
end

datatype ('f, 'v) "term" = Var 'v | Fun 'f "('f, 'v) term list"

fun root
where
  "root (Fun f ts) = (f, length ts)"

fun args
where
  "args (Fun f ts) = ts"

inductive_set gterms for F
where
  "(f, n) \<in> F \<Longrightarrow> length ts = n \<Longrightarrow> \<forall>s \<in> set ts. s \<in> gterms F \<Longrightarrow> Fun f ts \<in> gterms F"

interpretation kruskal_term: kruskal_tree F Fun root args "gterms F" for F
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: gterms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_term.almost_full_on_trees

inductive_set terms
where
  "\<forall>t \<in> set ts. t \<in> terms \<Longrightarrow> Fun f ts \<in> terms"

interpretation kruskal_variadic: kruskal_tree UNIV Fun root args terms
  apply (unfold_locales)
  apply auto
  apply (case_tac [!] t rule: terms.cases)
  apply auto
  by (metis less_not_refl not_less_eq size_list_estimation)

thm kruskal_variadic.almost_full_on_trees

datatype 'a exp = V 'a | C nat | Plus "'a exp" "'a exp"

datatype 'a symb = v 'a | c nat | p

fun mk
where
  "mk (v x) [] = V x" |
  "mk (c n) [] = C n" |
  "mk p [a, b] = Plus a b"

fun rt
where
  "rt (V x) = (v x, 0::nat)" |
  "rt (C n) = (c n, 0)" |
  "rt (Plus a b) = (p, 2)"

fun ags
where
  "ags (V x) = []" |
  "ags (C n) = []" |
  "ags (Plus a b) = [a, b]"

inductive_set exps
where
  "V x \<in> exps" |
  "C n \<in> exps" |
  "a \<in> exps \<Longrightarrow> b \<in> exps \<Longrightarrow> Plus a b \<in> exps"

lemma [simp]:
  assumes "length ts = 2"
  shows "rt (mk p ts) = (p, 2)"
  using assms by (induct ts) (auto, case_tac ts, auto)

lemma [simp]:
  assumes "length ts = 2"
  shows "ags (mk p ts) = ts"
  using assms by (induct ts) (auto, case_tac ts, auto)

interpretation kruskal_exp: kruskal_tree
  "{(v x, 0) | x. True} \<union> {(c n, 0) | n. True} \<union> {(p, 2)}"
  mk rt ags exps
apply (unfold_locales)
apply auto
apply (case_tac [!] t rule: exps.cases)
by auto

thm kruskal_exp.almost_full_on_trees

hide_const (open) tree_emb V C Plus v c p

end
