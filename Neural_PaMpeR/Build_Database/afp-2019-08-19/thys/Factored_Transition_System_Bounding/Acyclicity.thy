theory Acyclicity
  imports Main
begin


section \<open>Acyclicity\<close>

text \<open> Two of the discussed bounding algorithms ("top-down" and "bottom-up") exploit acyclicity
of the system under projection on sets of state variables closed under mutual variable dependency. 
[Abdulaziz et al., p.11] 

This specific notion of acyclicity is formalised using topologically sorted dependency graphs 
induced by the variable dependency relation. [Abdulaziz et al., p.14]\<close>


subsection "Topological Sorting of Dependency Graphs"

\<comment> \<open>NOTE name shortened.\<close>
\<comment> \<open>NOTE using 'fun' because of multiple defining equations.\<close> 
fun top_sorted_abs where
  "top_sorted_abs R [] = True"
| "top_sorted_abs R (h # l) = (list_all (\<lambda>x. \<not>R x h) l \<and> top_sorted_abs R l)"


lemma top_sorted_abs_mem: 
  assumes "(top_sorted_abs R (h # l))" "(ListMem x l)"
  shows "(\<not> R x h)"
  using assms
  by (auto simp add: ListMem_iff list.pred_set)


lemma top_sorted_cons: 
  assumes "top_sorted_abs R (h # l)"
  shows "(top_sorted_abs R l)"
  using assms
  by simp


subsection \<open>The Weightiest Path Function (wlp)\<close>

text \<open> The weightiest path function is a generalization of an algorithm which computes the
longest path in a DAG starting at a given vertex `v`. Its arguments are the relation `R` which
induces the graph, a weighing function `w` assigning weights to vertices, an accumulating functions
`f` and `g` which aggregate vertex weights into a path weight and the weights of different paths
respectively, the considered vertex and the graph represented as a topological sorted list. 
[Abdulaziz et al., p.18] 

Typical weight combining functions have the properties defined by `geq\_arg` and `increasing`. 
[Abdulaziz et al., p.18] \<close>

\<comment> \<open>NOTE name shortened.\<close>
fun wlp where
  "wlp R w g f x [] = w x"
| "wlp R w g f x (h # l) = (if R x h
    then g (f (w x) (wlp R w g f h l)) (wlp R w g f x l)
    else wlp R w g f x l
  )"


\<comment> \<open>NOTE name shortened.\<close>
definition geq_arg where 
  "geq_arg f \<equiv> (\<forall>x y. (x \<le> f x y) \<and> (y \<le> f x y))"


lemma individual_weight_less_eq_lp: 
  fixes w :: "'a \<Rightarrow> nat"
  assumes "geq_arg g"
  shows "(w x \<le> wlp R w g f x l)"
  using assms
  unfolding geq_arg_def
proof (induction l arbitrary: R w g f x)
  case (Cons a l)
  then show ?case
    using Cons.IH Cons.prems
  proof (cases "R x a")
    case True
    then show ?thesis 
      using Cons le_trans wlp.simps(2)
      by smt
  next
    case False
    then show ?thesis 
      using Cons
      by simp
  qed
qed simp


\<comment> \<open>NOTE Types of 'f' and 'g' had to be fixed to be able to use transitivity rule of the less-equal
relation.\<close>
lemma lp_geq_lp_from_successor:
  fixes vtx1 and f g :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  assumes "geq_arg f" "geq_arg g" "(\<forall>vtx. ListMem vtx G \<longrightarrow> \<not>R vtx vtx)" "R vtx2 vtx1" 
    "ListMem vtx1 G" "top_sorted_abs R G" 
  shows "(f (w vtx2) (wlp R w g f vtx1 G) \<le> (wlp R w g f vtx2 G))" 
  using assms
  unfolding geq_arg_def
proof (induction G arbitrary: vtx1 f g R vtx2)
  case Nil
  then show ?case 
    using ListMem_iff
    by fastforce
next
  case (Cons a G)
  show ?case 
  proof (auto)
    assume P1: "R vtx1 a" "R vtx2 a"
    then show "
        f (w vtx2) (g (f (w vtx1) (wlp R w g f a G)) (wlp R w g f vtx1 G))
        \<le> g (f (w vtx2) (wlp R w g f a G)) (wlp R w g f vtx2 G)"
      using Cons.prems(3, 5, 6)
      by (metis ListMem_iff set_ConsD top_sorted_abs_mem)
  next 
    assume P2: "R vtx1 a" "\<not> R vtx2 a" 
    then show "
        f (w vtx2) (g (f (w vtx1) (wlp R w g f a G)) (wlp R w g f vtx1 G)) 
        \<le> wlp R w g f vtx2 G"
      using Cons.prems(4, 5, 6)
      by (metis ListMem_iff set_ConsD top_sorted_abs_mem) 
  next 
    assume P3: "\<not> R vtx1 a" "R vtx2 a" 
    then show "
        f (w vtx2) (wlp R w g f vtx1 G) 
        \<le> g (f (w vtx2) (wlp R w g f a G)) (wlp R w g f vtx2 G)"
    proof -
      have f1: "\<forall>n na. n \<le> g n na \<and> na \<le> g n na"
        using Cons.prems(2) by blast
      have f2: "vtx1 = a \<or> vtx1 \<in> set G"
        by (meson Cons.prems(5) ListMem_iff set_ConsD)
      obtain aa :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a" where
        "\<forall>x2. (\<exists>v5. ListMem v5 G \<and> x2 v5 v5) = (ListMem (aa x2) G \<and> x2 (aa x2) (aa x2))"
        by moura
      then have "
          ListMem (aa R) G \<and> R (aa R) (aa R) 
          \<or> \<not> ListMem vtx1 G \<or> f (w vtx2) (wlp R w g f vtx1 G) \<le> wlp R w g f vtx2 G"
        using f1 by (metis (no_types) Cons.IH Cons.prems(1, 4, 6) top_sorted_cons)
      then show ?thesis
        using f2 f1 by (meson Cons.prems(3) ListMem_iff insert le_trans)
    qed
  next 
    assume P4: "\<not> R vtx1 a" "\<not> R vtx2 a"
    then show "f (w vtx2) (wlp R w g f vtx1 G) \<le> wlp R w g f vtx2 G"
    proof -
      have f1: "top_sorted_abs R G"
        using Cons.prems(6) by fastforce
      have "ListMem vtx1 G"
        by (metis Cons.prems(4) Cons.prems(5) ListMem_iff P4(2) set_ConsD)
      then show ?thesis
        using f1 by (simp add: Cons.IH Cons.prems(1, 2, 3, 4) insert)
    qed 
  qed
qed


definition increasing where
  "increasing f \<equiv> (\<forall>e b c d. (e \<le> c) \<and> (b \<le> d) \<longrightarrow> (f e b \<le> f c d))"


lemma weight_fun_leq_imp_lp_leq: "\<And>x.
  (increasing f)
  \<Longrightarrow> (increasing g)
  \<Longrightarrow> (\<forall>y. ListMem y l \<longrightarrow> w1 y \<le> w2 y) 
  \<Longrightarrow> (w1 x \<le> w2 x)
  \<Longrightarrow> (wlp R w1 g f x l \<le> wlp R w2 g f x l)
"
  unfolding increasing_def
  by (induction l) (auto simp add: elem insert)


\<comment> \<open>NOTE generalizing `f2`, `x1`, `x2` seems to break the prover.\<close>
lemma wlp_congruence_rule: 
  fixes l1 l2 R1 R2 w1 w2 g1 g2 f1 f2 x1 x2 
  assumes "(l1 = l2)" "(\<forall>y. ListMem y l2 \<longrightarrow> (R1 x1 y = R2 x2 y))"
    "(\<forall>y. ListMem y l2 \<longrightarrow> (R1 y x1 = R2 y x2))" "(w1 x1 = w2 x2)" 
    "(\<forall>y1 y2. (y1 = y2) \<longrightarrow> (f1 (w1 x1) y1 = f2 (w2 x2) y2))" 
    "(\<forall>y1 y2 z1 z2. (y1 = y2) \<and> (z1 = z2) \<longrightarrow> ((g1 (f1 (w1 x1) y1) z1) = (g2 (f2 (w2 x2) y2) z2)))"
    "(\<forall>x y. ListMem x l2 \<and> ListMem y l2 \<longrightarrow> (R1 x y = R2 x y))"
    "(\<forall>x. ListMem x l2 \<longrightarrow> (w1 x = w2 x))"
    "(\<forall>x y z. ListMem x l2 \<longrightarrow> (g1 (f1 (w1 x) y) z = g2 (f2 (w2 x) y) z))"
    "(\<forall>x y. ListMem x l2 \<longrightarrow> (f1 (w1 x) y = f2 (w1 x) y))"
  shows "((wlp R1 w1 g1 f1 x1 l1) = (wlp R2 w2 g2 f2 x2 l2))"
  using assms
proof (induction l2 arbitrary: l1 x1 x2)
  case (Cons a l2)
  then have "(wlp R1 w1 g1 f1 x1 l2) = (wlp R2 w2 g2 f2 x2 l2)"
    using Cons
    by (simp add: insert)
  moreover have "(wlp R1 w1 g1 f1 a l2) = (wlp R2 w2 g2 f2 a l2)"
    using Cons
    by (simp add: elem insert)
  ultimately show ?case
    by (simp add: Cons.prems(1,2, 6) elem)
qed auto


lemma wlp_ite_weights: 
  fixes x
  assumes "\<forall>y. ListMem y l1 \<longrightarrow> P y" "P x"
  shows "((wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x l1) = (wlp R w1 g f x l1))"
  using assms 

proof (induction l1 arbitrary: R P w1 w2 f g)
  case (Cons a l1)
  let ?w1="(\<lambda>y. if P y then w1 y else w2 y)"
  let ?w2="w1"
  {
    have "\<forall>y. ListMem y l1 \<longrightarrow> P y" 
      using Cons.prems(1) insert
      by fast
    then have "((wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x l1) = (wlp R w1 g f x l1))" 
      using Cons.prems(2) Cons.IH
      by blast
  }
  note 1 = this
  { 
    have "(if P x then w1 x else w2 x) = w1 x" 
      "\<forall>y1 y2. y1 = y2 \<longrightarrow> f (if P x then w1 x else w2 x) y1 = f (w1 x) y2"
      "\<forall>y1 y2 z1 z2. 
        y1 = y2 \<and> z1 = z2 
        \<longrightarrow> g (f (if P x then w1 x else w2 x) y1) z1 = g (f (w1 x) y2) z2"
      "\<forall>x. ListMem x (a # l1) \<longrightarrow> (if P x then w1 x else w2 x) = w1 x"
      "\<forall>x y z. 
        ListMem x (a # l1) 
        \<longrightarrow> g (f (if P x then w1 x else w2 x) y) z = g (f (w1 x) y) z"
      "\<forall>x y.
        ListMem x (a # l1) \<longrightarrow> f (if P x then w1 x else w2 x) y = f (if P x then w1 x else w2 x) y"
      using Cons.prems(1, 2)
      by simp+
    then have "wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x (a # l1) = wlp R w1 g f x (a # l1)"
      using Cons wlp_congruence_rule[of "a # l1" "a # l1" R x R x "?w1" "?w2" f f g g] 
      by blast
  }
  then show ?case
    by blast
qed auto


lemma map_wlp_ite_weights: "
  (\<forall>x. ListMem x l1 \<longrightarrow> P x) 
  \<Longrightarrow> (\<forall>x. ListMem x l2 \<longrightarrow> P x) 
  \<Longrightarrow> (
    map (\<lambda>x. wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x l1) l2 
    = map (\<lambda>x. wlp R w1 g f x l1) l2
  )
"
  apply(induction l2)
   apply(auto)
  subgoal by (simp add: elem wlp_congruence_rule)
  subgoal by (simp add: insert)
  done


lemma wlp_weight_lamda_exp: "\<And>x. wlp R w g f x l = wlp R (\<lambda>y. w y) g f x l"
proof -
  fix x
  show "wlp R w g f x l = wlp R (\<lambda>y. w y) g f x l" 
    by(induction l) auto
qed


lemma img_wlp_ite_weights: "
  (\<forall>x. ListMem x l \<longrightarrow> P x) 
  \<Longrightarrow> (\<forall>x. x \<in> s \<longrightarrow> P x) 
  \<Longrightarrow> (
    (\<lambda>x. wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x l) ` s 
    = (\<lambda>x. wlp R w1 g f x l) ` s
  )
"
proof -
  assume P1: "\<forall>x. ListMem x l \<longrightarrow> P x"
  assume P2: "\<forall>x. x \<in> s \<longrightarrow> P x"
  show "(
    (\<lambda>x. wlp R (\<lambda>y. if P y then w1 y else w2 y) g f x l) ` s 
    = (\<lambda>x. wlp R w1 g f x l) ` s
  )" 
    by (auto simp add:  P1 P2 image_iff wlp_ite_weights)
qed


end