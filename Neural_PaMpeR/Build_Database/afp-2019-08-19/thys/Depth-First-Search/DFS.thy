(*  Title:      Depth-First Search
    Author:     Toshiaki Nishihara and Yasuhiko Minamide
    Maintainer: Yasuhiko Minamide <minamide at cs.tsukuba.ac.jp>
*)

section "Depth-First Search"

theory DFS
imports Main
begin

subsection "Definition of Graphs"

typedecl node 
type_synonym graph = "(node * node) list"

primrec nexts :: "[graph, node] \<Rightarrow> node list"
where
  "nexts [] n = []"
| "nexts (e#es) n = (if fst e = n then snd e # nexts es n else nexts es n)"

definition nextss :: "[graph, node list] \<Rightarrow> node set"
  where "nextss g xs = set g `` set xs"

lemma nexts_set: "y \<in> set (nexts g x) = ((x,y) \<in> set g)"
  by (induct g) auto

lemma nextss_Cons: "nextss g (x#xs) = set (nexts g x) \<union> nextss g xs" 
  unfolding nextss_def by (auto simp add:Image_def nexts_set)

definition reachable :: "[graph, node list] \<Rightarrow> node set"
  where "reachable g xs = (set g)\<^sup>* `` set xs"


subsection "Depth-First Search with Stack" 

definition nodes_of :: "graph \<Rightarrow> node set"
  where "nodes_of g = set (map fst g @ map snd g)"

lemma [simp]: "x \<notin> nodes_of g \<Longrightarrow> nexts g x = []"
  by (induct g) (auto simp add: nodes_of_def)

lemma [simp]: "finite (nodes_of g - set ys)"  
proof(rule finite_subset)
  show "finite (nodes_of g)"
    by (auto simp add: nodes_of_def)
qed (auto)

function
  dfs :: "graph \<Rightarrow> node list \<Rightarrow> node list \<Rightarrow> node list"
where
  dfs_base: "dfs g [] ys = ys"
| dfs_inductive: "dfs g (x#xs) ys = (if List.member ys x then dfs g xs ys 
                        else dfs g (nexts g x@xs) (x#ys))"
by pat_completeness auto

termination
apply (relation "inv_image (finite_psubset <*lex*> less_than)  
                   (\<lambda>(g,xs,ys). (nodes_of g - set ys, size xs))")
apply auto[1]
apply (simp_all add: finite_psubset_def)
by (case_tac  "x \<in> nodes_of g") (auto simp add: List.member_def)

text \<open>
  \begin{itemize}
  \item The second argument of \isatext{\isastyle{dfs}} is a stack of nodes that will be
  visited.
  \item The third argument of \isatext{\isastyle{dfs}} is a list of nodes that have
  been visited already.
  \end{itemize}
\<close>


subsection "Depth-First Search with Nested-Recursion"

function
  dfs2 :: "graph \<Rightarrow> node list \<Rightarrow> node list \<Rightarrow> node list"
where
  "dfs2 g [] ys = ys"
|  dfs2_inductive: 
          "dfs2 g (x#xs) ys = (if List.member ys x then dfs2 g xs ys 
                               else dfs2 g xs (dfs2 g (nexts g x) (x#ys)))"
by pat_completeness auto

lemma dfs2_invariant: "dfs2_dom (g, xs, ys) \<Longrightarrow> set ys \<subseteq> set (dfs2 g xs ys)"
by (induct g xs ys rule: dfs2.pinduct) (force simp add: dfs2.psimps)+

termination dfs2
apply (relation "inv_image (finite_psubset <*lex*> less_than)  
                   (\<lambda>(g,xs,ys). (nodes_of g - set ys, size xs))")
apply auto[1]
apply (simp_all add: finite_psubset_def)
apply (case_tac  "x \<in> nodes_of g") 
apply (auto simp add: List.member_def)[2]
by (insert dfs2_invariant) force

(*lemma dfs2_induct[induct type]:
  assumes B: "\<And>g ys. P g [] ys" and
  H: "\<And>g x xs ys.
        \<lbrakk>\<not> x mem ys \<longrightarrow> P g xs (dfs2 (g, nexts g x, x # ys));
         \<not> x mem ys \<longrightarrow> P g (nexts g x) (x # ys); x mem ys \<longrightarrow> P g xs ys\<rbrakk>
         \<Longrightarrow> P g (x # xs) ys"
  shows "P u v w"

proof (induct u v w rule: dfs2.induct)
  case 1 show ?case by (rule B)
next
  case (2 g x xs ys)
  show ?case
  proof (rule H)
    show "\<not> x mem ys \<longrightarrow> P g xs (dfs2 (g, nexts g x, x # ys))"
    proof 
      assume *: "\<not> x mem ys"
      have "set (x#ys) \<subseteq> set (dfs2 (g, nexts g x, x # ys))"
        by (rule dfs2_inv)
      with 2 * show "P g xs (dfs2 (g, nexts g x, x # ys))"
        by auto
    qed
  qed (rule 2)+
qed
*)

lemma dfs_app: "dfs g (xs@ys) zs = dfs g ys (dfs g xs zs)"
  by (induct g xs zs rule: dfs.induct) auto

lemma "dfs2 g xs ys = dfs g xs ys" 
  by (induct g xs ys rule: dfs2.induct) (auto simp add: dfs_app)


subsection "Basic Properties"

lemma visit_subset_dfs: "set ys \<subseteq> set (dfs g xs ys)"
  by (induct g xs ys rule: dfs.induct) auto

lemma next_subset_dfs: "set xs \<subseteq> set (dfs g xs ys)"
proof(induct g xs ys rule:dfs.induct)
  case(2 g x xs ys) 
  show ?case
  proof(cases "x \<in> set ys")
    case True
    have "set ys \<subseteq> set (dfs g xs ys)"
      by (rule visit_subset_dfs)
    with 2 and True show ?thesis
      by (auto simp add: List.member_def)
  next
    case False
    have "set (x#ys) \<subseteq> set (dfs g (nexts g x @ xs) (x#ys))"
      by(rule visit_subset_dfs)
    with 2 and False show ?thesis
      by (auto simp add: List.member_def)
  qed
qed(simp)


lemma nextss_closed_dfs'[rule_format]: 
 "nextss g ys \<subseteq> set xs \<union> set ys \<longrightarrow> nextss g (dfs g xs ys) \<subseteq> set (dfs g xs ys)"
  by (induct g xs ys rule:dfs.induct, auto simp add:nextss_Cons List.member_def)

lemma nextss_closed_dfs: "nextss g (dfs g xs []) \<subseteq> set (dfs g xs [])"
  by (rule nextss_closed_dfs', simp add: nextss_def)

lemma Image_closed_trancl: assumes "r `` X \<subseteq> X" shows "r\<^sup>* `` X = X"
proof
  show "r\<^sup>* `` X \<subseteq> X"
  proof -
    {
      fix x y
      assume y: "y \<in> X"
      assume "(y,x) \<in> r\<^sup>*"
      then have "x \<in> X"
        by (induct) (insert assms y, auto simp add: Image_def)
    }
    then show ?thesis unfolding Image_def by auto
  qed
qed auto

lemma reachable_closed_dfs: "reachable g xs \<subseteq> set(dfs g xs [])"
proof -
  have "reachable g xs \<subseteq> reachable g (dfs g xs [])"
    unfolding reachable_def by (rule Image_mono) (auto simp add: next_subset_dfs)
  also have "\<dots> = set(dfs g xs [])"
    unfolding reachable_def
  proof (rule Image_closed_trancl)
    from nextss_closed_dfs
    show "set g `` set (dfs g xs []) \<subseteq> set (dfs g xs [])"
      by (simp add: nextss_def)
  qed
  finally show ?thesis .
qed

lemma reachable_nexts: "reachable g (nexts g x) \<subseteq> reachable g [x]"
  unfolding reachable_def
  by (auto intro: converse_rtrancl_into_rtrancl simp: nexts_set)

lemma reachable_append: "reachable g (xs @ ys) = reachable g xs \<union> reachable g ys"
  unfolding reachable_def by auto


lemma dfs_subset_reachable_visit_nodes: "set (dfs g xs ys) \<subseteq> reachable g xs \<union> set ys"
proof(induct g xs ys rule: dfs.induct)
  case 1
  then show ?case by simp
next
  case (2 g x xs ys)
  show ?case
  proof (cases "x \<in> set ys")
    case True
    with 2 show "set (dfs g (x#xs) ys) \<subseteq> reachable g (x#xs) \<union> set ys"
      by (auto simp add: reachable_def List.member_def)
  next
    case False
    have "reachable g (nexts g x) \<subseteq> reachable g [x]" 
      by (rule reachable_nexts)
    hence a: "reachable g (nexts g x @ xs) \<subseteq> reachable g (x#xs)"
      by(simp add: reachable_append, auto simp add: reachable_def)
    with False 2
    show "set (dfs g (x#xs) ys) \<subseteq> reachable g (x#xs) \<union> set ys"
      by (auto simp add: reachable_def List.member_def)
  qed
qed


subsection "Correctness"
    
theorem dfs_eq_reachable: "set (dfs g xs []) = reachable g xs"
proof
  have "set (dfs g xs []) \<subseteq> reachable g xs \<union> set []"
    by (rule dfs_subset_reachable_visit_nodes[of g xs "[]"])
 thus "set (dfs g xs []) \<subseteq> reachable g xs"
   by simp
qed(rule reachable_closed_dfs)

theorem "y \<in> set (dfs g [x] []) = ((x,y) \<in> (set g)\<^sup>*)"
  by(simp only:dfs_eq_reachable reachable_def, auto)


subsection "Executable Code"

consts Node :: "int \<Rightarrow> node"

code_datatype Node

instantiation node :: equal
begin

definition equal_node :: "node \<Rightarrow> node \<Rightarrow> bool"
where
  [code del]: "equal_node = HOL.eq"

instance proof
qed (simp add: equal_node_def)

end

declare [[code abort: "HOL.equal :: node \<Rightarrow> node \<Rightarrow> bool"]]

export_code dfs dfs2 in SML file \<open>dfs.ML\<close>

end
