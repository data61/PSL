section \<open>Weighted Directed Graphs\<close>
theory Directed_Graph
imports Common
begin

text \<open>
  A weighted graph is represented by a function from edges to weights.

  For simplicity, we use @{typ enat} as weights, @{term \<open>\<infinity>\<close>} meaning 
  that there is no edge.
\<close>

type_synonym ('v) wgraph = "('v \<times> 'v) \<Rightarrow> enat"

text \<open>We encapsulate weighted graphs into a locale that fixes a graph\<close>
locale WGraph = fixes w :: "'v wgraph"
begin
text \<open>Set of edges with finite weight\<close>
definition "edges \<equiv> {(u,v) . w (u,v) \<noteq> \<infinity>}"

subsection \<open>Paths\<close>
text \<open>A path between nodes \<open>u\<close> and \<open>v\<close> is a list of edge weights
  of a sequence of edges from \<open>u\<close> to \<open>v\<close>.
  
  Note that a path may also contain edges with weight \<open>\<infinity>\<close>.
\<close>

fun path :: "'v \<Rightarrow> enat list \<Rightarrow> 'v \<Rightarrow> bool" where
  "path u [] v \<longleftrightarrow> u=v"
| "path u (l#ls) v \<longleftrightarrow> (\<exists>uh. l = w (u,uh) \<and> path uh ls v)"

lemma path_append[simp]: 
  "path u (ls1@ls2) v \<longleftrightarrow> (\<exists>w. path u ls1 w \<and> path w ls2 v)"
  by (induction ls1 arbitrary: u) auto

text \<open>There is a singleton path between every two nodes 
  (it's weight might be \<open>\<infinity>\<close>).\<close>  
lemma triv_path: "path u [w (u,v)] v" by auto
  
text \<open>Shortcut for the set of all paths between two nodes\<close>    
definition "paths u v \<equiv> {p . path u p v}"

lemma paths_ne: "paths u v \<noteq> {}" using triv_path unfolding paths_def by blast

text \<open>If there is a path from a node inside a set \<open>S\<close>, to a node outside 
  a set \<open>S\<close>, this path must contain an edge from inside \<open>S\<close> to outside \<open>S\<close>.
\<close>
lemma find_leave_edgeE:
  assumes "path u p v"
  assumes "u\<in>S" "v\<notin>S"
  obtains p1 x y p2 
    where "p = p1@w (x,y)#p2" "x\<in>S" "y\<notin>S" "path u p1 x" "path y p2 v"
proof -
  have "\<exists>p1 x y p2. p = p1@w (x,y)#p2 \<and> x\<in>S \<and> y\<notin>S \<and> path u p1 x \<and> path y p2 v"
    using assms
  proof (induction p arbitrary: u)
    case Nil
    then show ?case by auto
  next
    case (Cons a p)
    from Cons.prems obtain x where [simp]: "a=w (u,x)" and PX: "path x p v" 
      by auto
    
    show ?case proof (cases "x\<in>S")
      case False with PX \<open>u\<in>S\<close> show ?thesis by fastforce
    next
      case True from Cons.IH[OF PX True \<open>v\<notin>S\<close>] show ?thesis
        by clarsimp (metis WGraph.path.simps(2) append_Cons)
    qed
  qed
  thus ?thesis by (fast intro: that) 
qed

subsection \<open>Distance\<close>

text \<open>The (minimum) distance between two nodes \<open>u\<close> and \<open>v\<close> is called \<open>\<delta> u v\<close>.\<close>

definition "\<delta> u v \<equiv> LEAST w::enat. w\<in>sum_list`paths u v"

lemma obtain_shortest_path: 
  obtains p where "path s p u" "\<delta> s u = sum_list p"
  unfolding \<delta>_def using paths_ne
  by (smt Collect_empty_eq LeastI_ex WGraph.paths_def imageI image_iff 
          mem_Collect_eq paths_def)

lemma shortest_path_least:  
  "path s p u \<Longrightarrow> \<delta> s u \<le> sum_list p"
  unfolding \<delta>_def paths_def
  by (simp add: Least_le)

lemma distance_refl[simp]: "\<delta> s s = 0"
  using shortest_path_least[of s "[]" s] by auto
  
lemma distance_direct: "\<delta> s u \<le> w (s, u)"  
  using shortest_path_least[of s "[w (s,u)]" u] by auto

text \<open>Triangle inequality: The distance from \<open>s\<close> to \<open>v\<close> is shorter than 
  the distance from \<open>s\<close> to \<open>u\<close> and the edge weight from \<open>u\<close> to \<open>v\<close>. \<close>  
lemma triangle: "\<delta> s v \<le> \<delta> s u + w (u,v)"
proof -
  have "path s (p@[w (u,v)]) v" if "path s p u" for p using that by auto
  then have "(+) (w (u,v)) ` sum_list ` paths s u \<subseteq> sum_list ` paths s v"
    by (fastforce simp: paths_def image_iff simp del: path.simps path_append) 
  from least_antimono[OF _ this] paths_ne have 
    "(LEAST y::enat. y \<in> sum_list ` paths s v) 
    \<le> (LEAST x::enat. x \<in> (+) (w (u,v)) ` sum_list ` paths s u)"
    by (auto simp: paths_def)
  also have "\<dots> = (LEAST x. x \<in> sum_list ` paths s u) + w (u,v)"
    apply (subst Least_mono[of "(+) (w (u,v))" "sum_list`paths s u"])
    subgoal by (auto simp: mono_def)
    subgoal by simp (metis paths_def mem_Collect_eq 
                          obtain_shortest_path shortest_path_least)
    subgoal by auto
    done
  finally show ?thesis unfolding \<delta>_def .
qed
  
text \<open>Any prefix of a shortest path is a shortest path itself.
  Note: The \<open>< \<infinity>\<close> conditions are required to avoid saturation in adding to \<open>\<infinity>\<close>!
\<close>
lemma shortest_path_prefix:
  assumes "path s p\<^sub>1 x" "path x p\<^sub>2 u" 
  and DSU: "\<delta> s u = sum_list p\<^sub>1 + sum_list p\<^sub>2" "\<delta> s u < \<infinity>"
  shows "\<delta> s x = sum_list p\<^sub>1" "\<delta> s x < \<infinity>"
proof -  
  have "\<delta> s x \<le> sum_list p\<^sub>1" using assms shortest_path_least by blast
  moreover have "\<not>\<delta> s x < sum_list p\<^sub>1" proof
    assume "\<delta> s x < sum_list p\<^sub>1"
    then obtain p\<^sub>1' where "path s p\<^sub>1' x" "sum_list p\<^sub>1' < sum_list p\<^sub>1"
      by (auto intro: obtain_shortest_path[of s x])
    with \<open>path x p\<^sub>2 u\<close> shortest_path_least[of s "p\<^sub>1'@p\<^sub>2" u] DSU show False
      by fastforce
  qed
  ultimately show "\<delta> s x = sum_list p\<^sub>1" by auto
  with DSU show "\<delta> s x < \<infinity>" using le_iff_add by fastforce
qed  
  
      
end

end
