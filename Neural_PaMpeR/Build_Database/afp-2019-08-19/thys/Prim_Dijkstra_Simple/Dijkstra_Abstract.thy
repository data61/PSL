section \<open>Abstract Dijkstra Algorithm\<close>
theory Dijkstra_Abstract
imports Directed_Graph
begin

subsection \<open>Abstract Algorithm\<close>

type_synonym 'v estimate = "'v \<Rightarrow> enat"
text \<open>We fix a start node and a weighted graph\<close>
locale Dijkstra = WGraph w for w :: "('v) wgraph" +
  fixes s :: 'v
begin

text \<open>Relax all outgoing edges of node \<open>u\<close>\<close>
definition relax_outgoing :: "'v \<Rightarrow> 'v estimate \<Rightarrow> 'v estimate"
  where "relax_outgoing u D \<equiv> \<lambda>v. min (D v) (D u + w (u,v))"

text \<open>Initialization\<close>
definition "initD \<equiv> (\<lambda>_. \<infinity>)(s:=0)"
definition "initS \<equiv> {}"  
  
      
text \<open>Relaxing will never increase estimates\<close>
lemma relax_mono: "relax_outgoing u D v \<le> D v"
  by (auto simp: relax_outgoing_def)


definition "all_dnodes \<equiv> Set.insert s { v . \<exists>u. w (u,v)\<noteq>\<infinity> }"
definition "unfinished_dnodes S \<equiv> all_dnodes - S "

lemma unfinished_nodes_subset: "unfinished_dnodes S \<subseteq> all_dnodes"
  by (auto simp: unfinished_dnodes_def)

end  

subsubsection \<open>Invariant\<close>
text \<open>The invariant is defined as locale\<close>
  
locale Dijkstra_Invar = Dijkstra w s for w and s :: 'v +
  fixes D :: "'v estimate" and S :: "'v set"
  assumes upper_bound: \<open>\<delta> s u \<le> D u\<close> \<comment> \<open>\<open>D\<close> is a valid estimate\<close>
  assumes s_in_S: \<open>s\<in>S \<or> (D=(\<lambda>_. \<infinity>)(s:=0) \<and> S={})\<close> \<comment> \<open>The start node is 
    finished, or we are in initial state\<close>  
  assumes S_precise: "u\<in>S \<Longrightarrow> D u = \<delta> s u" \<comment> \<open>Finished nodes have precise 
    estimate\<close>
  assumes S_relaxed: \<open>v\<in>S \<Longrightarrow> D u \<le> \<delta> s v + w (v,u)\<close> \<comment> \<open>Outgoing edges of 
    finished nodes have been relaxed, using precise distance\<close>
begin

abbreviation (in Dijkstra) "D_invar \<equiv> Dijkstra_Invar w s"

text \<open>The invariant holds for the initial state\<close>  
theorem (in Dijkstra) invar_init: "D_invar initD initS"
  apply unfold_locales
  unfolding initD_def initS_def
  by (auto simp: relax_outgoing_def distance_direct)


text \<open>Relaxing some edges maintains the upper bound property\<close>    
lemma maintain_upper_bound: "\<delta> s u \<le> (relax_outgoing v D) u"
  apply (clarsimp simp: relax_outgoing_def upper_bound split: prod.splits)
  using triangle upper_bound add_right_mono dual_order.trans by blast

text \<open>Relaxing edges will not affect nodes with already precise estimates\<close>
lemma relax_precise_id: "D v = \<delta> s v \<Longrightarrow> relax_outgoing u D v = \<delta> s v"
  using maintain_upper_bound upper_bound relax_mono
  by (metis antisym)

text \<open>In particular, relaxing edges will not affect finished nodes\<close>  
lemma relax_finished_id: "v\<in>S \<Longrightarrow> relax_outgoing u D v = D v"
  by (simp add: S_precise relax_precise_id)  
      
text \<open>The least (finite) estimate among all nodes \<open>u\<close> not in \<open>S\<close> is already precise.
  This will allow us to add the node \<open>u\<close> to \<open>S\<close>. \<close>
lemma maintain_S_precise_and_connected:  
  assumes UNS: "u\<notin>S"
  assumes MIN: "\<forall>v. v\<notin>S \<longrightarrow> D u \<le> D v"
  shows "D u = \<delta> s u"
  text \<open>We start with a case distinction whether we are in the first 
    step of the loop, where we process the start node, or in subsequent steps,
    where the start node has already been finished.\<close>
proof (cases "u=s")  
  assume [simp]: "u=s" \<comment> \<open>First step of loop\<close>
  then show ?thesis using \<open>u\<notin>S\<close> s_in_S by simp
next
  assume \<open>u\<noteq>s\<close> \<comment> \<open>Later step of loop\<close>
  text \<open>The start node has already been finished\<close>   
  with s_in_S MIN have \<open>s\<in>S\<close> apply clarsimp using infinity_ne_i0 by metis
  
  show ?thesis
  text \<open>Next, we handle the case that \<open>u\<close> is unreachable.\<close>
  proof (cases \<open>\<delta> s u < \<infinity>\<close>)
    assume "\<not>(\<delta> s u < \<infinity>)" \<comment> \<open>Node is unreachable (infinite distance)\<close>
    text \<open>By the upper-bound property, we get \<open>D u = \<delta> s u = \<infinity>\<close>\<close>
    then show ?thesis using upper_bound[of u] by auto
  next
    assume "\<delta> s u < \<infinity>" \<comment> \<open>Main case: Node has finite distance\<close>
 
    text \<open>Consider a shortest path from \<open>s\<close> to \<open>u\<close>\<close>        
    obtain p where "path s p u" and DSU: "\<delta> s u = sum_list p"
      by (rule obtain_shortest_path)
    text \<open>It goes from inside \<open>S\<close> to outside \<open>S\<close>, so there must be an edge at the border.
      Let \<open>(x,y)\<close> be such an edge, with \<open>x\<in>S\<close> and \<open>y\<notin>S\<close>.\<close>
    from find_leave_edgeE[OF \<open>path s p u\<close> \<open>s\<in>S\<close> \<open>u\<notin>S\<close>] obtain p1 x y p2 where
      [simp]: "p = p1 @ w (x, y) # p2" 
      and DECOMP: "x \<in> S" "y \<notin> S" "path s p1 x" "path y p2 u" .
    text \<open>As prefixes of shortest paths are again shortest paths, the shortest 
          path to \<open>y\<close> ends with edge \<open>(x,y)\<close> \<close>  
    have DSX: "\<delta> s x = sum_list p1" and DSY: "\<delta> s y = \<delta> s x + w (x, y)"
      using shortest_path_prefix[of s p1 x "w (x,y)#p2" u] 
        and shortest_path_prefix[of s "p1@[w (x,y)]" y p2 u]
        and \<open>\<delta> s u < \<infinity>\<close> DECOMP 
        by (force simp: DSU)+
    text \<open>Upon adding \<open>x\<close> to \<open>S\<close>, this edge has been relaxed with the precise
       estimate for \<open>x\<close>. At this point the estimate for \<open>y\<close> has become 
       precise, too\<close>  
    with \<open>x\<in>S\<close> have "D y = \<delta> s y"  
      by (metis S_relaxed antisym_conv upper_bound)
    moreover text \<open>The shortest path to \<open>y\<close> is a prefix of that to \<open>u\<close>, thus 
      it shorter or equal\<close>
    have "\<dots> \<le> \<delta> s u" using DSU by (simp add: DSX DSY)
    moreover text \<open>The estimate for \<open>u\<close> is an upper bound\<close>
    have "\<dots> \<le> D u" using upper_bound by (auto)
    moreover text \<open>\<open>u\<close> was a node with smallest estimate\<close>
    have "\<dots> \<le> D y" using \<open>u\<notin>S\<close> \<open>y\<notin>S\<close> MIN by auto
    ultimately text \<open>This closed a cycle in the inequation chain. Thus, by 
      antisymmetry, all items are equal. In particular, \<open>D u = \<delta> s u\<close>, qed.\<close>
    show "D u = \<delta> s u" by simp
  qed    
qed
  
text \<open>A step of Dijkstra's algorithm maintains the invariant.
  More precisely, in a step of Dijkstra's algorithm, 
  we pick a node \<open>u\<notin>S\<close> with least finite estimate, relax the outgoing 
  edges of \<open>u\<close>, and add \<open>u\<close> to \<open>S\<close>.\<close>    
theorem maintain_D_invar:
  assumes UNS: "u\<notin>S"
  assumes UNI: "D u < \<infinity>"
  assumes MIN: "\<forall>v. v\<notin>S \<longrightarrow> D u \<le> D v"
  shows "D_invar (relax_outgoing u D) (Set.insert u S)"
  apply (cases \<open>s\<in>S\<close>)
  subgoal
    apply (unfold_locales)
    subgoal by (simp add: maintain_upper_bound)
    subgoal by simp
    subgoal 
      using maintain_S_precise_and_connected[OF UNS MIN] S_precise        
      by (auto simp: relax_precise_id) 
    subgoal
      using maintain_S_precise_and_connected[OF UNS MIN]
      by (auto simp: relax_outgoing_def S_relaxed min.coboundedI1)
    done
  subgoal
    apply unfold_locales
    using s_in_S UNI distance_direct 
    by (auto simp: relax_outgoing_def split: if_splits)
  done
  

text \<open>When the algorithm is finished, i.e., when there are 
  no unfinished nodes with finite estimates left,
  then all estimates are accurate.\<close>  
lemma invar_finish_imp_correct:
  assumes F: "\<forall>u. u\<notin>S \<longrightarrow> D u = \<infinity>"
  shows "D u = \<delta> s u"
proof (cases "u\<in>S")
  assume "u\<in>S" text \<open>The estimates of finished nodes are accurate\<close>
  then show ?thesis using S_precise by simp
next
  assume \<open>u\<notin>S\<close> text \<open>\<open>D u\<close> is minimal, and minimal estimates are precise\<close>
  then show ?thesis 
    using F maintain_S_precise_and_connected[of u] by auto
  
qed  
  
  
text \<open>A step decreases the set of unfinished nodes.\<close>
lemma unfinished_nodes_decr:
  assumes UNS: "u\<notin>S"
  assumes UNI: "D u < \<infinity>"
  shows "unfinished_dnodes (Set.insert u S) \<subset> unfinished_dnodes S"
proof -
  text \<open>There is a path to \<open>u\<close>\<close>
  from UNI have "\<delta> s u < \<infinity>" using upper_bound[of u] leD by fastforce
  
  text \<open>Thus, \<open>u\<close> is among \<open>all_dnodes\<close>\<close>
  have "u\<in>all_dnodes" 
  proof -
    obtain p where "path s p u" "sum_list p < \<infinity>"
      apply (rule obtain_shortest_path[of s u])
      using \<open>\<delta> s u < \<infinity>\<close> by auto
    with \<open>u\<notin>S\<close> show ?thesis 
      apply (cases p rule: rev_cases) 
      by (auto simp: Dijkstra.all_dnodes_def)
  qed
  text \<open>Which implies the proposition\<close>
  with \<open>u\<notin>S\<close> show ?thesis by (auto simp: unfinished_dnodes_def)
qed
  
        
end  


subsection \<open>Refinement by Priority Map and Map\<close>
text \<open>
  In a second step, we implement \<open>D\<close> and \<open>S\<close> by a priority map \<open>Q\<close> and a map \<open>V\<close>.
  Both map nodes to finite weights, where \<open>Q\<close> maps unfinished nodes, and \<open>V\<close> 
  maps finished nodes.

  Note that this implementation is slightly non-standard: 
  In the standard implementation, \<open>Q\<close> contains also unfinished nodes with 
  infinite weight.
  
  We chose this implementation because it avoids enumerating all nodes of 
  the graph upon initialization of \<open>Q\<close>.
  However, on relaxing an edge to a node not in \<open>Q\<close>, we require an extra 
  lookup to check whether the node is finished. 
\<close>  

subsubsection \<open>Implementing \<open>enat\<close> by Option\<close>

text \<open>Our maps are functions to \<open>nat option\<close>,which are interpreted as \<open>enat\<close>,
  \<open>None\<close> being \<open>\<infinity>\<close>\<close>

fun enat_of_option :: "nat option \<Rightarrow> enat" where
  "enat_of_option None = \<infinity>" 
| "enat_of_option (Some n) = enat n"  
  
lemma enat_of_option_inj[simp]: "enat_of_option x = enat_of_option y \<longleftrightarrow> x=y"
  by (cases x; cases y; simp)

lemma enat_of_option_simps[simp]:
  "enat_of_option x = enat n \<longleftrightarrow> x = Some n"
  "enat_of_option x = \<infinity> \<longleftrightarrow> x = None"
  "enat n = enat_of_option x \<longleftrightarrow> x = Some n"
  "\<infinity> = enat_of_option x \<longleftrightarrow> x = None"
  by (cases x; auto; fail)+
  
lemma enat_of_option_le_conv: 
  "enat_of_option m \<le> enat_of_option n \<longleftrightarrow> (case (m,n) of 
      (_,None) \<Rightarrow> True
    | (Some a, Some b) \<Rightarrow> a\<le>b
    | (_, _) \<Rightarrow> False
  )"
  by (auto split: option.split)

  
  
subsubsection \<open>Implementing \<open>D,S\<close> by Priority Map and Map\<close>
context Dijkstra begin

text \<open>We define a coupling relation, that connects the concrete with the 
  abstract data. \<close>
definition "coupling Q V D S \<equiv> 
  D = enat_of_option o (V ++ Q)
\<and> S = dom V
\<and> dom V \<inter> dom Q = {}"

text \<open>Note that our coupling relation is functional.\<close>
(* TODO: Why not use functions instead? *)
lemma coupling_fun: "coupling Q V D S \<Longrightarrow> coupling Q V D' S' \<Longrightarrow> D'=D \<and> S'=S"
  by (auto simp: coupling_def)

text \<open>The concrete version of the invariant.\<close>  
definition "D_invar' Q V \<equiv>
  \<exists>D S. coupling Q V D S \<and> D_invar D S"

  
text \<open>Refinement of \<open>relax-outgoing\<close>\<close>

definition "relax_outgoing' u du V Q v \<equiv> 
  case w (u,v) of
    \<infinity> \<Rightarrow> Q v
  | enat d \<Rightarrow> (case Q v of
      None \<Rightarrow> if v\<in>dom V then None else Some (du+d)
    | Some d' \<Rightarrow> Some (min d' (du+d)))
"

  
text \<open>A step preserves the coupling relation.\<close>
lemma (in Dijkstra_Invar) coupling_step:
  assumes C: "coupling Q V D S"
  assumes UNS: "u\<notin>S"
  assumes UNI: "D u = enat du"
  
  shows "coupling 
    ((relax_outgoing' u du V Q)(u:=None)) (V(u\<mapsto>du)) 
    (relax_outgoing u D) (Set.insert u S)"
  using C unfolding coupling_def 
proof (intro ext conjI; elim conjE)
  assume \<alpha>: "D = enat_of_option \<circ> V ++ Q" "S = dom V" 
     and DD: "dom V \<inter> dom Q = {}"
   
  show "Set.insert u S = dom (V(u \<mapsto> du))"   
    by (auto simp: \<alpha>)
     
  have [simp]: "Q u = Some du" "V u = None" 
    using DD UNI UNS by (auto simp: \<alpha>)
    
  from DD 
  show "dom (V(u \<mapsto> du)) \<inter> dom ((relax_outgoing' u du V Q)(u := None)) = {}"
    by (auto 0 3 
          simp: relax_outgoing'_def dom_def 
          split: if_splits enat.splits option.splits)
  
  fix v
  
  show "relax_outgoing u D v 
    = (enat_of_option \<circ> V(u \<mapsto> du) ++ (relax_outgoing' u du V Q)(u := None)) v"
  proof (cases "v\<in>S")
    case True
    then show ?thesis using DD
      apply (simp add: relax_finished_id)
      by (auto 
        simp: relax_outgoing'_def map_add_apply \<alpha> min_def
        split: option.splits enat.splits)
  next
    case False
    then show ?thesis 
      by (auto 
        simp: relax_outgoing_def relax_outgoing'_def map_add_apply \<alpha> min_def
        split: option.splits enat.splits)
  qed
qed    
  
text \<open>Refinement of initial state\<close>
definition "initQ \<equiv> Map.empty(s\<mapsto>0)"
definition "initV \<equiv> Map.empty"
  
lemma coupling_init:
  "coupling initQ initV initD initS"    
  unfolding coupling_def initD_def initQ_def initS_def initV_def
  by (auto 
    simp: coupling_def relax_outgoing_def map_add_apply enat_0 
    split: option.split enat.split
    del: ext intro!: ext)
  
lemma coupling_cond:
  assumes "coupling Q V D S"
  shows "(Q = Map.empty) \<longleftrightarrow> (\<forall>u. u\<notin>S \<longrightarrow> D u = \<infinity>)"
  using assms
  by (fastforce simp add: coupling_def)

  
text \<open>Termination argument: Refinement of unfinished nodes.\<close>  
definition "unfinished_dnodes' V \<equiv> unfinished_dnodes (dom V)"

lemma coupling_unfinished: 
  "coupling Q V D S \<Longrightarrow> unfinished_dnodes' V = unfinished_dnodes S"
  by (auto simp: coupling_def unfinished_dnodes'_def unfinished_dnodes_def)

subsubsection \<open>Implementing graph by successor list\<close>  

definition "relax_outgoing'' l du V Q = fold (\<lambda>(d,v) Q.
  case Q v of None \<Rightarrow> if v\<in>dom V then Q else Q(v\<mapsto>du+d)
            | Some d' \<Rightarrow> Q(v\<mapsto>min (du+d) d')) l Q"


lemma relax_outgoing''_refine:
  assumes "set l = {(d,v). w (u,v) = enat d}"  
  shows "relax_outgoing'' l du V Q = relax_outgoing' u du V Q"
proof
  fix v
  
  have aux1:
     "relax_outgoing'' l du V Q v 
     = (if v\<in>snd`set l then relax_outgoing' u du V Q v else Q v)"
  if "set l \<subseteq> {(d,v). w (u,v) = enat d}"
    using that
    apply (induction l arbitrary: Q v)
    by (auto 
      simp: relax_outgoing''_def relax_outgoing'_def image_iff
      split!: if_splits option.splits)
  
  have aux2:  
    "relax_outgoing' u du V Q v = Q v" if "w (u,v) = \<infinity>"
    using that by (auto simp: relax_outgoing'_def)
  
  show "relax_outgoing'' l du V Q v = relax_outgoing' u du V Q v"
    using aux1
    apply (cases "w (u,v)")
    by (all \<open>force simp: aux2 assms\<close>)
qed
  
end

end
