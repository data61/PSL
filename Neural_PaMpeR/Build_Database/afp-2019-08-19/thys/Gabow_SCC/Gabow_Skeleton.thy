section \<open>Skeleton for Gabow's SCC Algorithm \label{sec:skel}\<close>
theory Gabow_Skeleton
imports CAVA_Automata.Digraph
begin

(* TODO: convenience locale, consider merging this with invariants *)
locale fr_graph =
  graph G
  for G :: "('v, 'more) graph_rec_scheme"
  +
  assumes finite_reachableE_V0[simp, intro!]: "finite (E\<^sup>* `` V0)"

text \<open>
  In this theory, we formalize a skeleton of Gabow's SCC algorithm. 
  The skeleton serves as a starting point to develop concrete algorithms,
  like enumerating the SCCs or checking emptiness of a generalized Büchi automaton.
\<close>

section \<open>Statistics Setup\<close>
text \<open>
  We define some dummy-constants that are included into the generated code,
  and may be mapped to side-effecting ML-code that records statistics and debug information
  about the execution. In the skeleton algorithm, we count the number of visited nodes,
  and include a timing for the whole algorithm.
\<close>

definition stat_newnode :: "unit => unit"   \<comment> \<open>Invoked if new node is visited\<close>
  where [code]: "stat_newnode \<equiv> \<lambda>_. ()"

definition stat_start :: "unit => unit"     \<comment> \<open>Invoked once if algorithm starts\<close>
  where [code]: "stat_start \<equiv> \<lambda>_. ()"

definition stat_stop :: "unit => unit"      \<comment> \<open>Invoked once if algorithm stops\<close>
  where [code]: "stat_stop \<equiv> \<lambda>_. ()"

lemma [autoref_rules]: 
  "(stat_newnode,stat_newnode) \<in> unit_rel \<rightarrow> unit_rel"
  "(stat_start,stat_start) \<in> unit_rel \<rightarrow> unit_rel"
  "(stat_stop,stat_stop) \<in> unit_rel \<rightarrow> unit_rel"
  by auto

abbreviation "stat_newnode_nres \<equiv> RETURN (stat_newnode ())"
abbreviation "stat_start_nres \<equiv> RETURN (stat_start ())"
abbreviation "stat_stop_nres \<equiv> RETURN (stat_stop ())"

lemma discard_stat_refine[refine]:
  "m1\<le>m2 \<Longrightarrow> stat_newnode_nres \<then> m1 \<le> m2"
  "m1\<le>m2 \<Longrightarrow> stat_start_nres \<then> m1 \<le> m2"
  "m1\<le>m2 \<Longrightarrow> stat_stop_nres \<then> m1 \<le> m2"
  by simp_all

section \<open>Abstract Algorithm\<close>
text \<open>
  In this section, we formalize an abstract version of a path-based SCC algorithm.
  Later, this algorithm will be refined to use Gabow's data structure.
\<close>

subsection \<open>Preliminaries\<close>
definition path_seg :: "'a set list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a set"
  \<comment> \<open>Set of nodes in a segment of the path\<close>
  where "path_seg p i j \<equiv> \<Union>{p!k|k. i\<le>k \<and> k<j}"

lemma path_seg_simps[simp]: 
  "j\<le>i \<Longrightarrow> path_seg p i j = {}"
  "path_seg p i (Suc i) = p!i"
  unfolding path_seg_def
  apply auto []
  apply (auto simp: le_less_Suc_eq) []
  done

lemma path_seg_drop:
  "\<Union>(set (drop i p)) = path_seg p i (length p)"
  unfolding path_seg_def
  by (fastforce simp: in_set_drop_conv_nth Bex_def)

lemma path_seg_butlast: 
  "p\<noteq>[] \<Longrightarrow> path_seg p 0 (length p - Suc 0) = \<Union>(set (butlast p))"
  apply (cases p rule: rev_cases, simp)
  apply (fastforce simp: path_seg_def nth_append in_set_conv_nth)
  done

definition idx_of :: "'a set list \<Rightarrow> 'a \<Rightarrow> nat"
  \<comment> \<open>Index of path segment that contains a node\<close>
  where "idx_of p v \<equiv> THE i. i<length p \<and> v\<in>p!i"

lemma idx_of_props:
  assumes 
    p_disjoint_sym: "\<forall>i j v. i<length p \<and> j<length p \<and> v\<in>p!i \<and> v\<in>p!j \<longrightarrow> i=j"
  assumes ON_STACK: "v\<in>\<Union>(set p)"
  shows 
    "idx_of p v < length p" and
    "v \<in> p ! idx_of p v"
proof -
  from ON_STACK obtain i where "i<length p" "v \<in> p ! i"
    by (auto simp add: in_set_conv_nth)
  moreover hence "\<forall>j<length p. v\<in>p ! j \<longrightarrow> i=j"
    using p_disjoint_sym by auto
  ultimately show "idx_of p v < length p" 
    and "v \<in> p ! idx_of p v" unfolding idx_of_def
    by (metis (lifting) theI')+
qed

lemma idx_of_uniq:
  assumes 
    p_disjoint_sym: "\<forall>i j v. i<length p \<and> j<length p \<and> v\<in>p!i \<and> v\<in>p!j \<longrightarrow> i=j"
  assumes A: "i<length p" "v\<in>p!i"
  shows "idx_of p v = i"
proof -
  from A p_disjoint_sym have "\<forall>j<length p. v\<in>p ! j \<longrightarrow> i=j" by auto
  with A show ?thesis
    unfolding idx_of_def
    by (metis (lifting) the_equality)
qed


subsection \<open>Invariants\<close>
text \<open>The state of the inner loop consists of the path \<open>p\<close> of
  collapsed nodes, the set \<open>D\<close> of finished (done) nodes, and the set
  \<open>pE\<close> of pending edges.\<close>
type_synonym 'v abs_state = "'v set list \<times> 'v set \<times> ('v\<times>'v) set"

context fr_graph
begin
  definition touched :: "'v set list \<Rightarrow> 'v set \<Rightarrow> 'v set" 
    \<comment> \<open>Touched: Nodes that are done or on path\<close>
    where "touched p D \<equiv> D \<union> \<Union>(set p)"

  definition vE :: "'v set list \<Rightarrow> 'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set"
    \<comment> \<open>Visited edges: No longer pending edges from touched nodes\<close>
    where "vE p D pE \<equiv> (E \<inter> (touched p D \<times> UNIV)) - pE"

  lemma vE_ss_E: "vE p D pE \<subseteq> E" \<comment> \<open>Visited edges are edges\<close>
    unfolding vE_def by auto

end

locale outer_invar_loc \<comment> \<open>Invariant of the outer loop\<close>
  = fr_graph G for G :: "('v,'more) graph_rec_scheme" +
  fixes it :: "'v set" \<comment> \<open>Remaining nodes to iterate over\<close>
  fixes D :: "'v set" \<comment> \<open>Finished nodes\<close>

  assumes it_initial: "it\<subseteq>V0"  \<comment> \<open>Only start nodes to iterate over\<close>

  assumes it_done: "V0 - it \<subseteq> D"  \<comment> \<open>Nodes already iterated over are visited\<close>
  assumes D_reachable: "D\<subseteq>E\<^sup>*``V0" \<comment> \<open>Done nodes are reachable\<close>
  assumes D_closed: "E``D \<subseteq> D" \<comment> \<open>Done is closed under transitions\<close>
begin

  lemma locale_this: "outer_invar_loc G it D" by unfold_locales

  definition (in fr_graph) "outer_invar \<equiv> \<lambda>it D. outer_invar_loc G it D"

  lemma outer_invar_this[simp, intro!]: "outer_invar it D"
    unfolding outer_invar_def apply simp by unfold_locales 
end

locale invar_loc \<comment> \<open>Invariant of the inner loop\<close>
  = fr_graph G
  for G :: "('v, 'more) graph_rec_scheme" +
  fixes v0 :: "'v"
  fixes D0 :: "'v set"
  fixes p :: "'v set list"
  fixes D :: "'v set"
  fixes pE :: "('v\<times>'v) set"

  assumes v0_initial[simp, intro!]: "v0\<in>V0"
  assumes D_incr: "D0 \<subseteq> D"

  assumes pE_E_from_p: "pE \<subseteq> E \<inter> (\<Union>(set p)) \<times> UNIV" 
    \<comment> \<open>Pending edges are edges from path\<close>
  assumes E_from_p_touched: "E \<inter> (\<Union>(set p) \<times> UNIV) \<subseteq> pE \<union> UNIV \<times> touched p D" 
    \<comment> \<open>Edges from path are pending or touched\<close>
  assumes D_reachable: "D\<subseteq>E\<^sup>*``V0" \<comment> \<open>Done nodes are reachable\<close>
  assumes p_connected: "Suc i<length p \<Longrightarrow> p!i \<times> p!Suc i \<inter> (E-pE) \<noteq> {}"
    \<comment> \<open>CNodes on path are connected by non-pending edges\<close>

  assumes p_disjoint: "\<lbrakk>i<j; j<length p\<rbrakk> \<Longrightarrow> p!i \<inter> p!j = {}" 
    \<comment> \<open>CNodes on path are disjoint\<close>
  assumes p_sc: "U\<in>set p \<Longrightarrow> U\<times>U \<subseteq> (vE p D pE \<inter> U\<times>U)\<^sup>*" 
    \<comment> \<open>Nodes in CNodes are mutually reachable by visited edges\<close>

  assumes root_v0: "p\<noteq>[] \<Longrightarrow> v0\<in>hd p" \<comment> \<open>Root CNode contains start node\<close>
  assumes p_empty_v0: "p=[] \<Longrightarrow> v0\<in>D" \<comment> \<open>Start node is done if path empty\<close>
  
  assumes D_closed: "E``D \<subseteq> D" \<comment> \<open>Done is closed under transitions\<close>
  (*assumes D_vis: "E\<inter>D\<times>D \<subseteq> vE" -- "All edges from done nodes are visited"*)

  assumes vE_no_back: "\<lbrakk>i<j; j<length p\<rbrakk> \<Longrightarrow> vE p D pE \<inter> p!j \<times> p!i = {}" 
  \<comment> \<open>Visited edges do not go back on path\<close>
  assumes p_not_D: "\<Union>(set p) \<inter> D = {}" \<comment> \<open>Path does not contain done nodes\<close>
begin
  abbreviation ltouched where "ltouched \<equiv> touched p D"
  abbreviation lvE where "lvE \<equiv> vE p D pE"

  lemma locale_this: "invar_loc G v0 D0 p D pE" by unfold_locales

  definition (in fr_graph) 
    "invar \<equiv> \<lambda>v0 D0 (p,D,pE). invar_loc G v0 D0 p D pE"

  lemma invar_this[simp, intro!]: "invar v0 D0 (p,D,pE)"
    unfolding invar_def apply simp by unfold_locales 

  lemma finite_reachableE_v0[simp, intro!]: "finite (E\<^sup>*``{v0})"
    apply (rule finite_subset[OF _ finite_reachableE_V0])
    using v0_initial by auto

  lemma D_vis: "E\<inter>D\<times>UNIV \<subseteq> lvE" \<comment> \<open>All edges from done nodes are visited\<close>
    unfolding vE_def touched_def using pE_E_from_p p_not_D by blast 

  lemma vE_touched: "lvE \<subseteq> ltouched \<times> ltouched" 
    \<comment> \<open>Visited edges only between touched nodes\<close>
    using E_from_p_touched D_closed unfolding vE_def touched_def by blast

  lemma lvE_ss_E: "lvE \<subseteq> E" \<comment> \<open>Visited edges are edges\<close>
    unfolding vE_def by auto


  lemma path_touched: "\<Union>(set p) \<subseteq> ltouched" by (auto simp: touched_def)
  lemma D_touched: "D \<subseteq> ltouched" by (auto simp: touched_def)

  lemma pE_by_vE: "pE = (E \<inter> \<Union>(set p) \<times> UNIV) - lvE"
    \<comment> \<open>Pending edges are edges from path not yet visited\<close>
    unfolding vE_def touched_def
    using pE_E_from_p
    by auto

  lemma pick_pending: "p\<noteq>[] \<Longrightarrow> pE \<inter> last p \<times> UNIV = (E-lvE) \<inter> last p \<times> UNIV"
    \<comment> \<open>Pending edges from end of path are non-visited edges from end of path\<close>
    apply (subst pE_by_vE)
    by auto

  lemma p_connected': 
    assumes A: "Suc i<length p" 
    shows "p!i \<times> p!Suc i \<inter> lvE \<noteq> {}" 
  proof -
    from A p_not_D have "p!i \<in> set p" "p!Suc i \<in> set p" by auto
    with p_connected[OF A] show ?thesis unfolding vE_def touched_def
      by blast
  qed

end

subsubsection \<open>Termination\<close>

context fr_graph 
begin
  text \<open>The termination argument is based on unprocessed edges: 
    Reachable edges from untouched nodes and pending edges.\<close>
  definition "unproc_edges v0 p D pE \<equiv> (E \<inter> (E\<^sup>*``{v0} - (D \<union> \<Union>(set p))) \<times> UNIV) \<union> pE"

  text \<open>
    In each iteration of the loop, either the number of unprocessed edges
    decreases, or the path length decreases.\<close>
  definition "abs_wf_rel v0 \<equiv> inv_image (finite_psubset <*lex*> measure length)
    (\<lambda>(p,D,pE). (unproc_edges v0 p D pE, p))"

  lemma abs_wf_rel_wf[simp, intro!]: "wf (abs_wf_rel v0)"
    unfolding abs_wf_rel_def
    by auto
end

subsection \<open>Abstract Skeleton Algorithm\<close>

context fr_graph
begin

  definition (in fr_graph) initial :: "'v \<Rightarrow> 'v set \<Rightarrow> 'v abs_state"
    where "initial v0 D \<equiv> ([{v0}], D, (E \<inter> {v0}\<times>UNIV))"

  definition (in -) collapse_aux :: "'a set list \<Rightarrow> nat \<Rightarrow> 'a set list"
    where "collapse_aux p i \<equiv> take i p @ [\<Union>(set (drop i p))]"

  definition (in -) collapse :: "'a \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" 
    where "collapse v PDPE \<equiv> 
    let 
      (p,D,pE)=PDPE; 
      i=idx_of p v;
      p = collapse_aux p i
    in (p,D,pE)"

  definition (in -) 
    select_edge :: "'a abs_state \<Rightarrow> ('a option \<times> 'a abs_state) nres"
    where
    "select_edge PDPE \<equiv> do {
      let (p,D,pE) = PDPE;
      e \<leftarrow> SELECT (\<lambda>e. e \<in> pE \<inter> last p \<times> UNIV);
      case e of
        None \<Rightarrow> RETURN (None,(p,D,pE))
      | Some (u,v) \<Rightarrow> RETURN (Some v, (p,D,pE - {(u,v)}))
    }"

  definition (in fr_graph) push :: "'v \<Rightarrow> 'v abs_state \<Rightarrow> 'v abs_state" 
    where "push v PDPE \<equiv> 
    let
      (p,D,pE) = PDPE;
      p = p@[{v}];
      pE = pE \<union> (E\<inter>{v}\<times>UNIV)
    in
      (p,D,pE)"

  definition (in -) pop :: "'v abs_state \<Rightarrow> 'v abs_state"
    where "pop PDPE \<equiv> let
      (p,D,pE) = PDPE;
      (p,V) = (butlast p, last p);
      D = V \<union> D
    in
      (p,D,pE)"

  text \<open>The following lemmas match the definitions presented in the paper:\<close>
  lemma "select_edge (p,D,pE) \<equiv> do {
      e \<leftarrow> SELECT (\<lambda>e. e \<in> pE \<inter> last p \<times> UNIV);
      case e of
        None \<Rightarrow> RETURN (None,(p,D,pE))
      | Some (u,v) \<Rightarrow> RETURN (Some v, (p,D,pE - {(u,v)}))
    }"
    unfolding select_edge_def by simp

  lemma "collapse v (p,D,pE) 
    \<equiv> let i=idx_of p v in (take i p @ [\<Union>(set (drop i p))],D,pE)"
    unfolding collapse_def collapse_aux_def by simp

  lemma "push v (p, D, pE) \<equiv> (p @ [{v}], D, pE \<union> E \<inter> {v} \<times> UNIV)"
    unfolding push_def by simp

  lemma "pop (p, D, pE) \<equiv> (butlast p, last p \<union> D, pE)"
    unfolding pop_def by auto

  thm pop_def[unfolded Let_def, no_vars]

  thm select_edge_def[unfolded Let_def]


  definition skeleton :: "'v set nres" 
    \<comment> \<open>Abstract Skeleton Algorithm\<close>
    where
    "skeleton \<equiv> do {
      let D = {};
      r \<leftarrow> FOREACHi outer_invar V0 (\<lambda>v0 D0. do {
        if v0\<notin>D0 then do {
          let s = initial v0 D0;

          (p,D,pE) \<leftarrow> WHILEIT (invar v0 D0)
            (\<lambda>(p,D,pE). p \<noteq> []) (\<lambda>(p,D,pE). 
          do {
            \<comment> \<open>Select edge from end of path\<close>
            (vo,(p,D,pE)) \<leftarrow> select_edge (p,D,pE);

            ASSERT (p\<noteq>[]);
            case vo of 
              Some v \<Rightarrow> do { \<comment> \<open>Found outgoing edge to node \<open>v\<close>\<close>
                if v \<in> \<Union>(set p) then do {
                  \<comment> \<open>Back edge: Collapse path\<close>
                  RETURN (collapse v (p,D,pE))
                } else if v\<notin>D then do {
                  \<comment> \<open>Edge to new node. Append to path\<close>
                  RETURN (push v (p,D,pE))
                } else do {
                  \<comment> \<open>Edge to done node. Skip\<close>
                  RETURN (p,D,pE)
                }
              }
            | None \<Rightarrow> do {
                ASSERT (pE \<inter> last p \<times> UNIV = {});
                \<comment> \<open>No more outgoing edges from current node on path\<close>
                RETURN (pop (p,D,pE))
              }
          }) s;
          ASSERT (p=[] \<and> pE={});
          RETURN D
        } else
          RETURN D0
      }) D;
      RETURN r
    }"

end

subsection \<open>Invariant Preservation\<close>

context fr_graph begin

  lemma set_collapse_aux[simp]: "\<Union>(set (collapse_aux p i)) = \<Union>(set p)"
    apply (subst (2) append_take_drop_id[of _ p,symmetric])
    apply (simp del: append_take_drop_id)
    unfolding collapse_aux_def by auto

  lemma touched_collapse[simp]: "touched (collapse_aux p i) D = touched p D"
    unfolding touched_def by simp

  lemma vE_collapse_aux[simp]: "vE (collapse_aux p i) D pE = vE p D pE"
    unfolding vE_def by simp

  lemma touched_push[simp]: "touched (p @ [V]) D = touched p D \<union> V"
    unfolding touched_def by auto

end

subsubsection \<open>Corollaries of the invariant\<close>
text \<open>In this section, we prove some more corollaries of the invariant,
  which are helpful to show invariant preservation\<close>

context invar_loc
begin
  lemma cnode_connectedI: 
    "\<lbrakk>i<length p; u\<in>p!i; v\<in>p!i\<rbrakk> \<Longrightarrow> (u,v)\<in>(lvE \<inter> p!i\<times>p!i)\<^sup>*"
    using p_sc[of "p!i"] by (auto simp: in_set_conv_nth)

  lemma cnode_connectedI': "\<lbrakk>i<length p; u\<in>p!i; v\<in>p!i\<rbrakk> \<Longrightarrow> (u,v)\<in>(lvE)\<^sup>*"
    by (metis inf.cobounded1 rtrancl_mono_mp cnode_connectedI)

  lemma p_no_empty: "{} \<notin> set p"
  proof 
    assume "{}\<in>set p"
    then obtain i where IDX: "i<length p" "p!i={}" 
      by (auto simp add: in_set_conv_nth)
    show False proof (cases i)
      case 0 with root_v0 IDX show False by (cases p) auto
    next
      case [simp]: (Suc j)
      from p_connected'[of j] IDX show False by simp
    qed
  qed

  corollary p_no_empty_idx: "i<length p \<Longrightarrow> p!i\<noteq>{}"
    using p_no_empty by (metis nth_mem)
  
  lemma p_disjoint_sym: "\<lbrakk>i<length p; j<length p; v\<in>p!i; v\<in>p!j\<rbrakk> \<Longrightarrow> i=j"
    by (metis disjoint_iff_not_equal linorder_neqE_nat p_disjoint)

  lemma pi_ss_path_seg_eq[simp]:
    assumes A: "i<length p" "u\<le>length p"
    shows "p!i\<subseteq>path_seg p l u \<longleftrightarrow> l\<le>i \<and> i<u"
  proof
    assume B: "p!i\<subseteq>path_seg p l u"
    from A obtain x where "x\<in>p!i" by (blast dest: p_no_empty_idx)
    with B obtain i' where C: "x\<in>p!i'" "l\<le>i'" "i'<u" 
      by (auto simp: path_seg_def)
    from p_disjoint_sym[OF \<open>i<length p\<close> _ \<open>x\<in>p!i\<close> \<open>x\<in>p!i'\<close>] \<open>i'<u\<close> \<open>u\<le>length p\<close>
    have "i=i'" by simp
    with C show "l\<le>i \<and> i<u" by auto
  qed (auto simp: path_seg_def)

  lemma path_seg_ss_eq[simp]:
    assumes A: "l1<u1" "u1\<le>length p" "l2<u2" "u2\<le>length p"
    shows "path_seg p l1 u1 \<subseteq> path_seg p l2 u2 \<longleftrightarrow> l2\<le>l1 \<and> u1\<le>u2"
  proof
    assume S: "path_seg p l1 u1 \<subseteq> path_seg p l2 u2"
    have "p!l1 \<subseteq> path_seg p l1 u1" using A by simp
    also note S finally have 1: "l2\<le>l1" using A by simp
    have "p!(u1 - 1) \<subseteq> path_seg p l1 u1" using A by simp
    also note S finally have 2: "u1\<le>u2" using A by auto
    from 1 2 show "l2\<le>l1 \<and> u1\<le>u2" ..
  next
    assume "l2\<le>l1 \<and> u1\<le>u2" thus "path_seg p l1 u1 \<subseteq> path_seg p l2 u2"
      using A
      apply (clarsimp simp: path_seg_def) []
      apply (metis dual_order.strict_trans1 dual_order.trans)
      done
  qed

  lemma pathI: 
    assumes "x\<in>p!i" "y\<in>p!j"
    assumes "i\<le>j" "j<length p"
    defines "seg \<equiv> path_seg p i (Suc j)"
    shows "(x,y)\<in>(lvE \<inter> seg\<times>seg)\<^sup>*"
    \<comment> \<open>We can obtain a path between cnodes on path\<close>
    using assms(3,1,2,4) unfolding seg_def
  proof (induction arbitrary: y rule: dec_induct)
    case base thus ?case by (auto intro!: cnode_connectedI)
  next
    case (step j)

    let ?seg = "path_seg p i (Suc j)"
    let ?seg' = "path_seg p i (Suc (Suc j))"

    have SSS: "?seg \<subseteq> ?seg'" 
      apply (subst path_seg_ss_eq)
      using step.hyps step.prems by auto

    from p_connected'[OF \<open>Suc j < length p\<close>] obtain u v where 
      UV: "(u,v)\<in>lvE" "u\<in>p!j" "v\<in>p!Suc j" by auto

    have ISS: "p!j \<subseteq> ?seg'" "p!Suc j \<subseteq> ?seg'" 
      using step.hyps step.prems by simp_all

    from p_no_empty_idx[of j] \<open>Suc j < length p\<close> obtain x' where "x'\<in>p!j" 
      by auto
    with step.IH[of x'] \<open>x\<in>p!i\<close> \<open>Suc j < length p\<close> 
    have t: "(x,x')\<in>(lvE\<inter>?seg\<times>?seg)\<^sup>*" by auto
    have "(x,x')\<in>(lvE\<inter>?seg'\<times>?seg')\<^sup>*" using SSS 
      by (auto intro: rtrancl_mono_mp[OF _ t])
    also 
    from cnode_connectedI[OF _ \<open>x'\<in>p!j\<close> \<open>u\<in>p!j\<close>] \<open>Suc j < length p\<close> have
      t: "(x', u) \<in> (lvE \<inter> p ! j \<times> p ! j)\<^sup>*" by auto
    have "(x', u) \<in> (lvE\<inter>?seg'\<times>?seg')\<^sup>*" using ISS
      by (auto intro: rtrancl_mono_mp[OF _ t])
    also have "(u,v)\<in>lvE\<inter>?seg'\<times>?seg'" using UV ISS by auto
    also from cnode_connectedI[OF \<open>Suc j < length p\<close> \<open>v\<in>p!Suc j\<close> \<open>y\<in>p!Suc j\<close>] 
    have t: "(v, y) \<in> (lvE \<inter> p ! Suc j \<times> p ! Suc j)\<^sup>*" by auto
    have "(v, y) \<in> (lvE\<inter>?seg'\<times>?seg')\<^sup>*" using ISS
      by (auto intro: rtrancl_mono_mp[OF _ t])
    finally show "(x,y)\<in>(lvE\<inter>?seg'\<times>?seg')\<^sup>*" .
  qed

  lemma p_reachable: "\<Union>(set p) \<subseteq> E\<^sup>*``{v0}" \<comment> \<open>Nodes on path are reachable\<close>
  proof 
    fix v
    assume A: "v\<in>\<Union>(set p)"
    then obtain i where "i<length p" and "v\<in>p!i" 
      by (metis UnionE in_set_conv_nth)
    moreover from A root_v0 have "v0\<in>p!0" by (cases p) auto
    ultimately have 
      t: "(v0,v)\<in>(lvE \<inter> path_seg p 0 (Suc i) \<times> path_seg p 0 (Suc i))\<^sup>*"
      by (auto intro: pathI)
    from lvE_ss_E have "(v0,v)\<in>E\<^sup>*" by (auto intro: rtrancl_mono_mp[OF _ t])
    thus "v\<in>E\<^sup>*``{v0}" by auto
  qed

  lemma touched_reachable: "ltouched \<subseteq> E\<^sup>*``V0" \<comment> \<open>Touched nodes are reachable\<close>
    unfolding touched_def using p_reachable D_reachable by blast

  lemma vE_reachable: "lvE \<subseteq> E\<^sup>*``V0 \<times> E\<^sup>*``V0"
    apply (rule order_trans[OF vE_touched])
    using touched_reachable by blast

  lemma pE_reachable: "pE \<subseteq> E\<^sup>*``{v0} \<times> E\<^sup>*``{v0}"
  proof safe
    fix u v
    assume E: "(u,v)\<in>pE"
    with pE_E_from_p p_reachable have "(v0,u)\<in>E\<^sup>*" "(u,v)\<in>E" by blast+
    thus "(v0,u)\<in>E\<^sup>*" "(v0,v)\<in>E\<^sup>*" by auto
  qed

  lemma D_closed_vE_rtrancl: "lvE\<^sup>*``D \<subseteq> D"
    by (metis D_closed Image_closed_trancl eq_iff reachable_mono lvE_ss_E)

  lemma D_closed_path: "\<lbrakk>path E u q w; u\<in>D\<rbrakk> \<Longrightarrow> set q \<subseteq> D"
  proof -
    assume a1: "path E u q w"
    assume "u \<in> D"
    hence f1: "{u} \<subseteq> D"
      using bot.extremum by force
    have "set q \<subseteq> E\<^sup>* `` {u}"
      using a1 by (metis insert_subset path_nodes_reachable)
    thus "set q \<subseteq> D"
      using f1 by (metis D_closed rtrancl_reachable_induct subset_trans)
  qed

  lemma D_closed_path_vE: "\<lbrakk>path lvE u q w; u\<in>D\<rbrakk> \<Longrightarrow> set q \<subseteq> D"
    by (metis D_closed_path path_mono lvE_ss_E)

  lemma path_in_lastnode:
    assumes P: "path lvE u q v"
    assumes [simp]: "p\<noteq>[]"
    assumes ND: "u\<in>last p" "v\<in>last p"
    shows "set q \<subseteq> last p"
    \<comment> \<open>A path from the last Cnode to the last Cnode remains in the last Cnode\<close>
    (* TODO: This can be generalized in two directions: 
      either 1) The path end anywhere. Due to vE_touched we can infer 
        that it ends in last cnode  
      or 2) We may use any cnode, not only the last one
    *)
    using P ND
  proof (induction)
    case (path_prepend u v l w) 
    from \<open>(u,v)\<in>lvE\<close> vE_touched have "v\<in>ltouched" by auto
    hence "v\<in>\<Union>(set p)"
      unfolding touched_def
    proof
      assume "v\<in>D"
      moreover from \<open>path lvE v l w\<close> have "(v,w)\<in>lvE\<^sup>*" by (rule path_is_rtrancl)
      ultimately have "w\<in>D" using D_closed_vE_rtrancl by auto
      with \<open>w\<in>last p\<close> p_not_D have False
        by (metis IntI Misc.last_in_set Sup_inf_eq_bot_iff assms(2) 
          bex_empty path_prepend.hyps(2))
      thus ?thesis ..
    qed
    then obtain i where "i<length p" "v\<in>p!i"
      by (metis UnionE in_set_conv_nth)
    have "i=length p - 1"
    proof (rule ccontr)
      assume "i\<noteq>length p - 1"
      with \<open>i<length p\<close> have "i < length p - 1" by simp
      with vE_no_back[of i "length p - 1"] \<open>i<length p\<close> 
      have "lvE \<inter> last p \<times> p!i = {}"
        by (simp add: last_conv_nth)
      with \<open>(u,v)\<in>lvE\<close> \<open>u\<in>last p\<close> \<open>v\<in>p!i\<close> show False by auto
    qed
    with \<open>v\<in>p!i\<close> have "v\<in>last p" by (simp add: last_conv_nth)
    with path_prepend.IH \<open>w\<in>last p\<close> \<open>u\<in>last p\<close> show ?case by auto
  qed simp

  lemma loop_in_lastnode:
    assumes P: "path lvE u q u"
    assumes [simp]: "p\<noteq>[]"
    assumes ND: "set q \<inter> last p \<noteq> {}"
    shows "u\<in>last p" and "set q \<subseteq> last p"
    \<comment> \<open>A loop that touches the last node is completely inside the last node\<close>
  proof -
    from ND obtain v where "v\<in>set q" "v\<in>last p" by auto
    then obtain q1 q2 where [simp]: "q=q1@v#q2" 
      by (auto simp: in_set_conv_decomp)
    from P have "path lvE v (v#q2@q1) v" 
      by (auto simp: path_conc_conv path_cons_conv)
    from path_in_lastnode[OF this \<open>p\<noteq>[]\<close> \<open>v\<in>last p\<close> \<open>v\<in>last p\<close>] 
    show "set q \<subseteq> last p" by simp
    from P show "u\<in>last p" 
      apply (cases q, simp)
      
      apply simp
      using \<open>set q \<subseteq> last p\<close>
      apply (auto simp: path_cons_conv)
      done
  qed


  lemma no_D_p_edges: "E \<inter> D \<times> \<Union>(set p) = {}"
    using D_closed p_not_D by auto

  lemma idx_of_props:
    assumes ON_STACK: "v\<in>\<Union>(set p)"
    shows 
      "idx_of p v < length p" and
      "v \<in> p ! idx_of p v"
    using idx_of_props[OF _ assms] p_disjoint_sym by blast+

end

subsubsection \<open>Auxiliary Lemmas Regarding the Operations\<close>

lemma (in fr_graph) vE_initial[simp]: "vE [{v0}] {} (E \<inter> {v0} \<times> UNIV) = {}"
  unfolding vE_def touched_def by auto

context invar_loc
begin
  lemma vE_push: "\<lbrakk> (u,v)\<in>pE; u\<in>last p; v\<notin>\<Union>(set p); v\<notin>D \<rbrakk> 
    \<Longrightarrow> vE (p @ [{v}]) D ((pE - {(u,v)}) \<union> E\<inter>{v}\<times>UNIV) = insert (u,v) lvE"
    unfolding vE_def touched_def using pE_E_from_p
    by auto

  lemma vE_remove[simp]: 
    "\<lbrakk>p\<noteq>[]; (u,v)\<in>pE\<rbrakk> \<Longrightarrow> vE p D (pE - {(u,v)}) = insert (u,v) lvE"
    unfolding vE_def touched_def using pE_E_from_p by blast

  lemma vE_pop[simp]: "p\<noteq>[] \<Longrightarrow> vE (butlast p) (last p \<union> D) pE = lvE"
    unfolding vE_def touched_def 
    by (cases p rule: rev_cases) auto


  lemma pE_fin: "p=[] \<Longrightarrow> pE={}"
    using pE_by_vE by auto

  lemma (in invar_loc) lastp_un_D_closed:
    assumes NE: "p \<noteq> []"
    assumes NO': "pE \<inter> (last p \<times> UNIV) = {}"
    shows "E``(last p \<union> D) \<subseteq> (last p \<union> D)"
    \<comment> \<open>On pop, the popped CNode and D are closed under transitions\<close>
  proof (intro subsetI, elim ImageE)
    from NO' have NO: "(E - lvE) \<inter> (last p \<times> UNIV) = {}"
      by (simp add: pick_pending[OF NE])

    let ?i = "length p - 1"
    from NE have [simp]: "last p = p!?i" by (metis last_conv_nth) 
    
    fix u v
    assume E: "(u,v)\<in>E"
    assume UI: "u\<in>last p \<union> D" hence "u\<in>p!?i \<union> D" by simp
    
    {
      assume "u\<in>last p" "v\<notin>last p" 
      moreover from E NO \<open>u\<in>last p\<close> have "(u,v)\<in>lvE" by auto
      ultimately have "v\<in>D \<or> v\<in>\<Union>(set p)" 
        using vE_touched unfolding touched_def by auto
      moreover {
        assume "v\<in>\<Union>(set p)"
        then obtain j where V: "j<length p" "v\<in>p!j" 
          by (metis UnionE in_set_conv_nth)
        with \<open>v\<notin>last p\<close> have "j<?i" by (cases "j=?i") auto
        from vE_no_back[OF \<open>j<?i\<close> _] \<open>(u,v)\<in>lvE\<close> V \<open>u\<in>last p\<close> have False by auto
      } ultimately have "v\<in>D" by blast
    } with E UI D_closed show "v\<in>last p \<union> D" by auto
  qed



end


subsubsection \<open>Preservation of Invariant by Operations\<close>

context fr_graph
begin
  lemma (in outer_invar_loc) invar_initial_aux: 
    assumes "v0\<in>it - D"
    shows "invar v0 D (initial v0 D)"
    unfolding invar_def initial_def
    apply simp
    apply unfold_locales
    apply simp_all
    using assms it_initial apply auto []
    using D_reachable it_initial assms apply auto []
    using D_closed apply auto []
    using assms apply auto []
    done

  lemma invar_initial: 
    "\<lbrakk>outer_invar it D0; v0\<in>it; v0\<notin>D0\<rbrakk> \<Longrightarrow> invar v0 D0 (initial v0 D0)"
    unfolding outer_invar_def
    apply (drule outer_invar_loc.invar_initial_aux) 
    by auto

  lemma outer_invar_initial[simp, intro!]: "outer_invar V0 {}"
    unfolding outer_invar_def
    apply unfold_locales
    by auto

  lemma invar_pop:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes NO': "pE \<inter> (last p \<times> UNIV) = {}"
    shows "invar v0 D0 (pop (p,D,pE))"
    unfolding invar_def pop_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp

    have [simp]: "set p = insert (last p) (set (butlast p))" 
      using NE by (cases p rule: rev_cases) auto

    from p_disjoint have lp_dj_blp: "last p \<inter> \<Union>(set (butlast p)) = {}"
      apply (cases p rule: rev_cases)
      apply simp
      apply (fastforce simp: in_set_conv_nth nth_append)
      done

    {
      fix i
      assume A: "Suc i < length (butlast p)"
      hence A': "Suc i < length p" by auto

      from nth_butlast[of i p] A have [simp]: "butlast p ! i = p ! i" by auto
      from nth_butlast[of "Suc i" p] A 
      have [simp]: "butlast p ! Suc i = p ! Suc i" by auto

      from p_connected[OF A'] 
      have "butlast p ! i \<times> butlast p ! Suc i \<inter> (E - pE) \<noteq> {}"
        by simp
    } note AUX_p_connected = this

    (*have [simp]: "(E \<inter> (last p \<union> D \<union> \<Union>set (butlast p)) \<times> UNIV - pE) = vE"
      unfolding vE_def touched_def by auto*)

    show "invar_loc G v0 D0 (butlast p) (last p \<union> D) pE"
      apply unfold_locales
  
      unfolding vE_pop[OF NE]

      apply simp

      using D_incr apply auto []

      using pE_E_from_p NO' apply auto []
  
      using E_from_p_touched apply (auto simp: touched_def) []
  
      using D_reachable p_reachable NE apply auto []

      apply (rule AUX_p_connected, assumption+) []

      using p_disjoint apply (simp add: nth_butlast)

      using p_sc apply simp

      using root_v0 apply (cases p rule: rev_cases) apply auto [2]

      using root_v0 p_empty_v0 apply (cases p rule: rev_cases) apply auto [2]

      apply (rule lastp_un_D_closed, insert NO', auto) []

      using vE_no_back apply (auto simp: nth_butlast) []

      using p_not_D lp_dj_blp apply auto []
      done
  qed

  thm invar_pop[of v_0 D_0, no_vars]

  lemma invar_collapse:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and "u\<in>last p"
    assumes BACK: "v\<in>\<Union>(set p)"
    defines "i \<equiv> idx_of p v"
    defines "p' \<equiv> collapse_aux p i"
    shows "invar v0 D0 (collapse v (p,D,pE - {(u,v)}))"
    unfolding invar_def collapse_def
    apply simp
    unfolding i_def[symmetric] p'_def[symmetric]
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp

    let ?thesis="invar_loc G v0 D0 p' D (pE - {(u,v)})"

    have SETP'[simp]: "\<Union>(set p') = \<Union>(set p)" unfolding p'_def by simp

    have IL: "i < length p" and VMEM: "v\<in>p!i" 
      using idx_of_props[OF BACK] unfolding i_def by auto

    have [simp]: "length p' = Suc i" 
      unfolding p'_def collapse_aux_def using IL by auto

    have P'_IDX_SS: "\<forall>j<Suc i. p!j \<subseteq> p'!j"
      unfolding p'_def collapse_aux_def using IL 
      by (auto simp add: nth_append path_seg_drop)

    from \<open>u\<in>last p\<close> have "u\<in>p!(length p - 1)" by (auto simp: last_conv_nth)

    have defs_fold: 
      "vE p' D (pE - {(u,v)}) = insert (u,v) lvE" 
      "touched p' D = ltouched"
      by (simp_all add: p'_def E)

    {
      fix j
      assume A: "Suc j < length p'" 
      hence "Suc j < length p" using IL by simp
      from p_connected[OF this] have "p!j \<times> p!Suc j \<inter> (E-pE) \<noteq> {}" .
      moreover from P'_IDX_SS A have "p!j\<subseteq>p'!j" and "p!Suc j \<subseteq> p'!Suc j"
        by auto
      ultimately have "p' ! j \<times> p' ! Suc j \<inter> (E - (pE - {(u, v)})) \<noteq> {}" 
        by blast
    } note AUX_p_connected = this

    have P_IDX_EQ[simp]: "\<forall>j. j < i \<longrightarrow> p'!j = p!j"
      unfolding p'_def collapse_aux_def using IL  
      by (auto simp: nth_append)

    have P'_LAST[simp]: "p'!i = path_seg p i (length p)" (is "_ = ?last_cnode")
      unfolding p'_def collapse_aux_def using IL 
      by (auto simp: nth_append path_seg_drop)

    {
      fix j k
      assume A: "j < k" "k < length p'" 
      have "p' ! j \<inter> p' ! k = {}"
      proof (safe, simp)
        fix v
        assume "v\<in>p'!j" and "v\<in>p'!k"
        with A have "v\<in>p!j" by simp
        show False proof (cases)
          assume "k=i"
          with \<open>v\<in>p'!k\<close> obtain k' where "v\<in>p!k'" "i\<le>k'" "k'<length p" 
            by (auto simp: path_seg_def)
          hence "p ! j \<inter> p ! k' = {}"
            using A by (auto intro!: p_disjoint)
          with \<open>v\<in>p!j\<close> \<open>v\<in>p!k'\<close> show False by auto
        next
          assume "k\<noteq>i" with A have "k<i" by simp
          hence "k<length p" using IL by simp
          note p_disjoint[OF \<open>j<k\<close> this] 
          also have "p!j = p'!j" using \<open>j<k\<close> \<open>k<i\<close> by simp
          also have "p!k = p'!k" using \<open>k<i\<close> by simp
          finally show False using \<open>v\<in>p'!j\<close> \<open>v\<in>p'!k\<close> by auto
        qed
      qed
    } note AUX_p_disjoint = this

    {
      fix U
      assume A: "U\<in>set p'"
      then obtain j where "j<Suc i" and [simp]: "U=p'!j"
        by (auto simp: in_set_conv_nth)
      hence "U \<times> U \<subseteq> (insert (u, v) lvE \<inter> U \<times> U)\<^sup>*" 
      proof cases
        assume [simp]: "j=i"
        show ?thesis proof (clarsimp)
          fix x y
          assume "x\<in>path_seg p i (length p)" "y\<in>path_seg p i (length p)"
          then obtain ix iy where 
            IX: "x\<in>p!ix" "i\<le>ix" "ix<length p" and
            IY: "y\<in>p!iy" "i\<le>iy" "iy<length p"
            by (auto simp: path_seg_def)
            

          from IX have SS1: "path_seg p ix (length p) \<subseteq> ?last_cnode"
            by (subst path_seg_ss_eq) auto

          from IY have SS2: "path_seg p i (Suc iy) \<subseteq> ?last_cnode"
            by (subst path_seg_ss_eq) auto

          let ?rE = "\<lambda>R. (lvE \<inter> R\<times>R)"
          let ?E = "(insert (u,v) lvE \<inter> ?last_cnode \<times> ?last_cnode)"

          from pathI[OF \<open>x\<in>p!ix\<close> \<open>u\<in>p!(length p - 1)\<close>] have
            "(x,u)\<in>(?rE (path_seg p ix (Suc (length p - 1))))\<^sup>*" using IX by auto
          hence "(x,u)\<in>?E\<^sup>*" 
            apply (rule rtrancl_mono_mp[rotated]) 
            using SS1
            by auto

          also have "(u,v)\<in>?E" using \<open>i<length p\<close>
            apply (clarsimp)
            apply (intro conjI)
            apply (rule rev_subsetD[OF \<open>u\<in>p!(length p - 1)\<close>])
            apply (simp)
            apply (rule rev_subsetD[OF VMEM])
            apply (simp)
            done
          also 
          from pathI[OF \<open>v\<in>p!i\<close> \<open>y\<in>p!iy\<close>] have
            "(v,y)\<in>(?rE (path_seg p i (Suc iy)))\<^sup>*" using IY by auto
          hence "(v,y)\<in>?E\<^sup>*"
            apply (rule rtrancl_mono_mp[rotated]) 
            using SS2
            by auto
          finally show "(x,y)\<in>?E\<^sup>*" .
        qed
      next
        assume "j\<noteq>i"
        with \<open>j<Suc i\<close> have [simp]: "j<i" by simp
        with \<open>i<length p\<close> have "p!j\<in>set p"
          by (metis Suc_lessD in_set_conv_nth less_trans_Suc) 

        thus ?thesis using p_sc[of U] \<open>p!j\<in>set p\<close>
          apply (clarsimp)
          apply (subgoal_tac "(a,b)\<in>(lvE \<inter> p ! j \<times> p ! j)\<^sup>*")
          apply (erule rtrancl_mono_mp[rotated])
          apply auto
          done
      qed
    } note AUX_p_sc = this

    { fix j k
      assume A: "j<k" "k<length p'"
      hence "j<i" by simp
      have "insert (u, v) lvE \<inter> p' ! k \<times> p' ! j = {}"
      proof -
        have "{(u,v)} \<inter> p' ! k \<times> p' ! j = {}" 
          apply auto
          by (metis IL P_IDX_EQ Suc_lessD VMEM \<open>j < i\<close> 
            less_irrefl_nat less_trans_Suc p_disjoint_sym)
        moreover have "lvE \<inter> p' ! k \<times> p' ! j = {}" 
        proof (cases "k<i")
          case True thus ?thesis
            using vE_no_back[of j k] A \<open>i<length p\<close> by auto
        next
          case False with A have [simp]: "k=i" by simp
          show ?thesis proof (rule disjointI, clarsimp simp: \<open>j<i\<close>)
            fix x y
            assume B: "(x,y)\<in>lvE" "x\<in>path_seg p i (length p)" "y\<in>p!j"
            then obtain ix where "x\<in>p!ix" "i\<le>ix" "ix<length p" 
              by (auto simp: path_seg_def)
            moreover with A have "j<ix" by simp
            ultimately show False using vE_no_back[of j ix] B by auto
          qed
        qed
        ultimately show ?thesis by blast
      qed
    } note AUX_vE_no_back = this

    show ?thesis
      apply unfold_locales
      unfolding defs_fold

      apply simp

      using D_incr apply auto []

      using pE_E_from_p apply auto []

      using E_from_p_touched BACK apply (simp add: touched_def) apply blast

      apply (rule D_reachable)

      apply (rule AUX_p_connected, assumption+) []

      apply (rule AUX_p_disjoint, assumption+) []

      apply (rule AUX_p_sc, assumption+) []

      using root_v0 
      apply (cases i) 
      apply (simp add: p'_def collapse_aux_def)
      apply (metis NE hd_in_set)
      apply (cases p, simp_all add: p'_def collapse_aux_def) []

      apply (simp add: p'_def collapse_aux_def)

      apply (rule D_closed)

      apply (drule (1) AUX_vE_no_back, auto) []

      using p_not_D apply simp
      done
  qed
  
  lemma invar_push:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and UIL: "u\<in>last p"
    assumes VNE: "v\<notin>\<Union>(set p)" "v\<notin>D"
    shows "invar v0 D0 (push v (p,D,pE - {(u,v)}))"
    unfolding invar_def push_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp

    let ?thesis 
      = "invar_loc G v0 D0 (p @ [{v}]) D (pE - {(u, v)} \<union> E \<inter> {v} \<times> UNIV)"

    note defs_fold = vE_push[OF E UIL VNE] touched_push

    {
      fix i
      assume SILL: "Suc i < length (p @ [{v}])"
      have "(p @ [{v}]) ! i \<times> (p @ [{v}]) ! Suc i 
             \<inter> (E - (pE - {(u, v)} \<union> E \<inter> {v} \<times> UNIV)) \<noteq> {}"
      proof (cases "i = length p - 1")
        case True thus ?thesis using SILL E pE_E_from_p UIL VNE
          by (simp add: nth_append last_conv_nth) fast
      next
        case False
        with SILL have SILL': "Suc i < length p" by simp
            
        with SILL' VNE have X1: "v\<notin>p!i" "v\<notin>p!Suc i" by auto
            
        from p_connected[OF SILL'] obtain a b where 
          "a\<in>p!i" "b\<in>p!Suc i" "(a,b)\<in>E" "(a,b)\<notin>pE" 
          by auto
        with X1 have "a\<noteq>v" "b\<noteq>v" by auto
        with \<open>(a,b)\<in>E\<close> \<open>(a,b)\<notin>pE\<close> have "(a,b)\<in>(E - (pE - {(u, v)} \<union> E \<inter> {v} \<times> UNIV))"
          by auto
        with \<open>a\<in>p!i\<close> \<open>b\<in>p!Suc i\<close>
        show ?thesis using  SILL'
          by (simp add: nth_append; blast) 
      qed
    } note AUX_p_connected = this

    {
      fix U
      assume A: "U \<in> set (p @ [{v}])"
      have "U \<times> U \<subseteq> (insert (u, v) lvE \<inter> U \<times> U)\<^sup>*"
      proof cases
        assume "U\<in>set p"
        with p_sc have "U\<times>U \<subseteq> (lvE \<inter> U\<times>U)\<^sup>*" .
        thus ?thesis
          by (metis (lifting, no_types) Int_insert_left_if0 Int_insert_left_if1 
            in_mono insert_subset rtrancl_mono_mp subsetI)
      next
        assume "U\<notin>set p" with A have "U={v}" by simp
        thus ?thesis by auto
      qed
    } note AUX_p_sc = this

    {
      fix i j
      assume A: "i < j" "j < length (p @ [{v}])"
      have "insert (u, v) lvE \<inter> (p @ [{v}]) ! j \<times> (p @ [{v}]) ! i = {}"
      proof (cases "j=length p")
        case False with A have "j<length p" by simp
        from vE_no_back \<open>i<j\<close> this VNE show ?thesis 
          by (auto simp add: nth_append)
      next
        from p_not_D A have PDDJ: "p!i \<inter> D = {}" 
          by (auto simp: Sup_inf_eq_bot_iff)
        case True thus ?thesis
          using A apply (simp add: nth_append)
          apply (rule conjI)
          using UIL A p_disjoint_sym
          apply (metis Misc.last_in_set NE UnionI VNE(1))

          using vE_touched VNE PDDJ apply (auto simp: touched_def) []
          done
      qed
    } note AUX_vE_no_back = this
        
    show ?thesis
      apply unfold_locales
      unfolding defs_fold

      apply simp

      using D_incr apply auto []

      using pE_E_from_p apply auto []

      using E_from_p_touched VNE apply (auto simp: touched_def) []

      apply (rule D_reachable)

      apply (rule AUX_p_connected, assumption+) []

      using p_disjoint \<open>v\<notin>\<Union>(set p)\<close> apply (auto simp: nth_append) []

      apply (rule AUX_p_sc, assumption+) []

      using root_v0 apply simp

      apply simp

      apply (rule D_closed)

      apply (rule AUX_vE_no_back, assumption+) []

      using p_not_D VNE apply auto []
      done
  qed

  lemma invar_skip:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" and UIL: "u\<in>last p"
    assumes VNP: "v\<notin>\<Union>(set p)" and VD: "v\<in>D"
    shows "invar v0 D0 (p,D,pE - {(u, v)})"
    unfolding invar_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp
    let ?thesis = "invar_loc G v0 D0 p D (pE - {(u, v)})"
    note defs_fold = vE_remove[OF NE E]

    show ?thesis
      apply unfold_locales
      unfolding defs_fold
      
      apply simp

      using D_incr apply auto []

      using pE_E_from_p apply auto []

      using E_from_p_touched VD apply (auto simp: touched_def) []

      apply (rule D_reachable)

      using p_connected apply auto []

      apply (rule p_disjoint, assumption+) []

      apply (drule p_sc)
      apply (erule order_trans)
      apply (rule rtrancl_mono)
      apply blast []

      apply (rule root_v0, assumption+) []

      apply (rule p_empty_v0, assumption+) []

      apply (rule D_closed)

      using vE_no_back VD p_not_D 
      apply clarsimp
      apply (metis Suc_lessD UnionI VNP less_trans_Suc nth_mem)

      apply (rule p_not_D)
      done
  qed


  lemma fin_D_is_reachable: 
    \<comment> \<open>When inner loop terminates, all nodes reachable from start node are
      finished\<close>
    assumes INV: "invar v0 D0 ([], D, pE)"
    shows "D \<supseteq> E\<^sup>*``{v0}"
  proof -
    from INV interpret invar_loc G v0 D0 "[]" D pE unfolding invar_def by auto

    from p_empty_v0 rtrancl_reachable_induct[OF order_refl D_closed] D_reachable
    show ?thesis by auto
  qed

  lemma fin_reachable_path: 
    \<comment> \<open>When inner loop terminates, nodes reachable from start node are
      reachable over visited edges\<close>
    assumes INV: "invar v0 D0 ([], D, pE)"
    assumes UR: "u\<in>E\<^sup>*``{v0}"
    shows "path (vE [] D pE) u q v \<longleftrightarrow> path E u q v"
  proof -
    from INV interpret invar_loc G v0 D0 "[]" D pE unfolding invar_def by auto
    
    show ?thesis
    proof
      assume "path lvE u q v"
      thus "path E u q v" using path_mono[OF lvE_ss_E] by blast
    next
      assume "path E u q v"
      thus "path lvE u q v" using UR
      proof induction
        case (path_prepend u v p w)
        with fin_D_is_reachable[OF INV] have "u\<in>D" by auto
        with D_closed \<open>(u,v)\<in>E\<close> have "v\<in>D" by auto
        from path_prepend.prems path_prepend.hyps have "v\<in>E\<^sup>*``{v0}" by auto
        with path_prepend.IH fin_D_is_reachable[OF INV] have "path lvE v p w" 
          by simp
        moreover from \<open>u\<in>D\<close> \<open>v\<in>D\<close> \<open>(u,v)\<in>E\<close> D_vis have "(u,v)\<in>lvE" by auto
        ultimately show ?case by (auto simp: path_cons_conv)
      qed simp
    qed
  qed

  lemma invar_outer_newnode: 
    assumes A: "v0\<notin>D0" "v0\<in>it" 
    assumes OINV: "outer_invar it D0"
    assumes INV: "invar v0 D0 ([],D',pE)"
    shows "outer_invar (it-{v0}) D'"
  proof -
    from OINV interpret outer_invar_loc G it D0 unfolding outer_invar_def .
    from INV interpret inv: invar_loc G v0 D0 "[]" D' pE 
      unfolding invar_def by simp
    
    from fin_D_is_reachable[OF INV] have [simp]: "v0\<in>D'" by auto

    show ?thesis
      unfolding outer_invar_def
      apply unfold_locales
      using it_initial apply auto []
      using it_done inv.D_incr apply auto []
      using inv.D_reachable apply assumption
      using inv.D_closed apply assumption
      done
  qed

  lemma invar_outer_Dnode:
    assumes A: "v0\<in>D0" "v0\<in>it" 
    assumes OINV: "outer_invar it D0"
    shows "outer_invar (it-{v0}) D0"
  proof -
    from OINV interpret outer_invar_loc G it D0 unfolding outer_invar_def .
    
    show ?thesis
      unfolding outer_invar_def
      apply unfold_locales
      using it_initial apply auto []
      using it_done A apply auto []
      using D_reachable apply assumption
      using D_closed apply assumption
      done
  qed

  lemma pE_fin': "invar x \<sigma> ([], D, pE) \<Longrightarrow> pE={}"
    unfolding invar_def by (simp add: invar_loc.pE_fin)

end

subsubsection \<open>Termination\<close>

context invar_loc 
begin
  lemma unproc_finite[simp, intro!]: "finite (unproc_edges v0 p D pE)"
    \<comment> \<open>The set of unprocessed edges is finite\<close>
  proof -
    have "unproc_edges v0 p D pE \<subseteq> E\<^sup>*``{v0} \<times> E\<^sup>*``{v0}"
      unfolding unproc_edges_def 
      using pE_reachable
      by auto
    thus ?thesis
      by (rule finite_subset) simp
  qed

  lemma unproc_decreasing: 
    \<comment> \<open>As effect of selecting a pending edge, the set of unprocessed edges
      decreases\<close>
    assumes [simp]: "p\<noteq>[]" and A: "(u,v)\<in>pE" "u\<in>last p"
    shows "unproc_edges v0 p D (pE-{(u,v)}) \<subset> unproc_edges v0 p D pE"
    using A unfolding unproc_edges_def
    by fastforce
end

context fr_graph 
begin

  lemma abs_wf_pop:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes NO: "pE \<inter> last aba \<times> UNIV = {}"
    shows "(pop (p,D,pE), (p, D, pE)) \<in> abs_wf_rel v0"
    unfolding pop_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp 
    let ?thesis = "((butlast p, last p \<union> D, pE), p, D, pE) \<in> abs_wf_rel v0"
    have "unproc_edges v0 (butlast p) (last p \<union> D) pE = unproc_edges v0 p D pE"
      unfolding unproc_edges_def
      apply (cases p rule: rev_cases, simp)
      apply auto
      done
    thus ?thesis
      by (auto simp: abs_wf_rel_def)
  qed

  lemma abs_wf_collapse:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" "u\<in>last p"
    shows "(collapse v (p,D,pE-{(u,v)}), (p, D, pE))\<in> abs_wf_rel v0"
    unfolding collapse_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp 
    define i where "i = idx_of p v"
    let ?thesis 
      = "((collapse_aux p i, D, pE-{(u,v)}), (p, D, pE)) \<in> abs_wf_rel v0"

    have "unproc_edges v0 (collapse_aux p i) D (pE-{(u,v)}) 
      = unproc_edges v0 p D (pE-{(u,v)})"
      unfolding unproc_edges_def by (auto)
    also note unproc_decreasing[OF NE E]
    finally show ?thesis
      by (auto simp: abs_wf_rel_def)
  qed
    
  lemma abs_wf_push:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" "u\<in>last p" and A: "v\<notin>D" "v\<notin>\<Union>(set p)"
    shows "(push v (p,D,pE-{(u,v)}), (p, D, pE)) \<in> abs_wf_rel v0"
    unfolding push_def
    apply simp
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp 
    let ?thesis 
      = "((p@[{v}], D, pE-{(u,v)} \<union> E\<inter>{v}\<times>UNIV), (p, D, pE)) \<in> abs_wf_rel v0"

    have "unproc_edges v0 (p@[{v}]) D (pE-{(u,v)} \<union> E\<inter>{v}\<times>UNIV) 
      = unproc_edges v0 p D (pE-{(u,v)})"
      unfolding unproc_edges_def
      using E A pE_reachable
      by auto
    also note unproc_decreasing[OF NE E]
    finally show ?thesis
      by (auto simp: abs_wf_rel_def)
  qed

  lemma abs_wf_skip:
    assumes INV: "invar v0 D0 (p,D,pE)"
    assumes NE[simp]: "p\<noteq>[]"
    assumes E: "(u,v)\<in>pE" "u\<in>last p"
    shows "((p, D, pE-{(u,v)}), (p, D, pE)) \<in> abs_wf_rel v0"
  proof -
    from INV interpret invar_loc G v0 D0 p D pE unfolding invar_def by simp 
    from unproc_decreasing[OF NE E] show ?thesis
      by (auto simp: abs_wf_rel_def)
  qed
end

subsubsection \<open>Main Correctness Theorem\<close>

context fr_graph 
begin
  lemmas invar_preserve = 
    invar_initial
    invar_pop invar_push invar_skip invar_collapse 
    abs_wf_pop abs_wf_collapse abs_wf_push abs_wf_skip 
    outer_invar_initial invar_outer_newnode invar_outer_Dnode

  text \<open>The main correctness theorem for the dummy-algorithm just states that
    it satisfies the invariant when finished, and the path is empty.
\<close>
  theorem skeleton_spec: "skeleton \<le> SPEC (\<lambda>D. outer_invar {} D)"
  proof -
    note [simp del] = Union_iff
    note [[goals_limit = 4]]

    show ?thesis
      unfolding skeleton_def select_edge_def select_def
      apply (refine_vcg WHILEIT_rule[OF abs_wf_rel_wf])
      apply (vc_solve solve: invar_preserve simp: pE_fin' finite_V0)
      apply auto
      done
  qed

  text \<open>Short proof, as presented in the paper\<close>
  context 
    notes [refine] = refine_vcg 
  begin
    theorem "skeleton \<le> SPEC (\<lambda>D. outer_invar {} D)"
      unfolding skeleton_def select_edge_def select_def
      by (refine_vcg WHILEIT_rule[OF abs_wf_rel_wf])
         (auto intro: invar_preserve simp: pE_fin' finite_V0)
  end

end

subsection "Consequences of Invariant when Finished"
context fr_graph
begin
  lemma fin_outer_D_is_reachable:
    \<comment> \<open>When outer loop terminates, exactly the reachable nodes are finished\<close>
    assumes INV: "outer_invar {} D"
    shows "D = E\<^sup>*``V0"
  proof -
    from INV interpret outer_invar_loc G "{}" D unfolding outer_invar_def by auto

    from it_done rtrancl_reachable_induct[OF order_refl D_closed] D_reachable
    show ?thesis by auto
  qed

end


section \<open>Refinement to Gabow's Data Structure\<close>text_raw\<open>\label{sec:algo-ds}\<close>

text \<open>
  The implementation due to Gabow \cite{Gabow2000} represents a path as
  a stack \<open>S\<close> of single nodes, and a stack \<open>B\<close> that contains the
  boundaries of the collapsed segments. Moreover, a map \<open>I\<close> maps nodes
  to their stack indices.

  As we use a tail-recursive formulation, we use another stack 
  \<open>P :: (nat \<times> 'v set) list\<close> to represent the pending edges. The
  entries in \<open>P\<close> are sorted by ascending first component,
  and \<open>P\<close> only contains entries with non-empty second component. 
  An entry \<open>(i,l)\<close> means that the edges from the node at 
  \<open>S[i]\<close> to the nodes stored in \<open>l\<close> are pending.
\<close>

subsection \<open>Preliminaries\<close>
primrec find_max_nat :: "nat \<Rightarrow> (nat\<Rightarrow>bool) \<Rightarrow> nat" 
  \<comment> \<open>Find the maximum number below an upper bound for which a predicate holds\<close>
  where
  "find_max_nat 0 _ = 0"
| "find_max_nat (Suc n) P = (if (P n) then n else find_max_nat n P)"

lemma find_max_nat_correct: 
  "\<lbrakk>P 0; 0<u\<rbrakk> \<Longrightarrow> find_max_nat u P = Max {i. i<u \<and> P i}"
  apply (induction u)
  apply auto

  apply (rule Max_eqI[THEN sym])
  apply auto [3]
  
  apply (case_tac u)
  apply simp
  apply clarsimp
  by (metis less_SucI less_antisym)

lemma find_max_nat_param[param]:
  assumes "(n,n')\<in>nat_rel"
  assumes "\<And>j j'. \<lbrakk>(j,j')\<in>nat_rel; j'<n'\<rbrakk> \<Longrightarrow> (P j,P' j')\<in>bool_rel"
  shows "(find_max_nat n P,find_max_nat n' P') \<in> nat_rel"
  using assms
  by (induction n arbitrary: n') auto

context begin interpretation autoref_syn .
  lemma find_max_nat_autoref[autoref_rules]:
    assumes "(n,n')\<in>nat_rel"
    assumes "\<And>j j'. \<lbrakk>(j,j')\<in>nat_rel; j'<n'\<rbrakk> \<Longrightarrow> (P j,P'$j')\<in>bool_rel"
    shows "(find_max_nat n P,
        (OP find_max_nat ::: nat_rel \<rightarrow> (nat_rel\<rightarrow>bool_rel) \<rightarrow> nat_rel) $n'$P'
      ) \<in> nat_rel"
    using find_max_nat_param[OF assms]
    by simp

end

subsection \<open>Gabow's Datastructure\<close>

subsubsection \<open>Definition and Invariant\<close>
datatype node_state = STACK nat | DONE

type_synonym 'v oGS = "'v \<rightharpoonup> node_state"

definition oGS_\<alpha> :: "'v oGS \<Rightarrow> 'v set" where "oGS_\<alpha> I \<equiv> {v. I v = Some DONE}"

locale oGS_invar = 
  fixes I :: "'v oGS"
  assumes I_no_stack: "I v \<noteq> Some (STACK j)"


type_synonym 'a GS 
  = "'a list \<times> nat list \<times> ('a \<rightharpoonup> node_state) \<times> (nat \<times> 'a set) list"
locale GS =  
  fixes SBIP :: "'a GS"
begin
  definition "S \<equiv> (\<lambda>(S,B,I,P). S) SBIP"
  definition "B \<equiv> (\<lambda>(S,B,I,P). B) SBIP"
  definition "I \<equiv> (\<lambda>(S,B,I,P). I) SBIP"
  definition "P \<equiv> (\<lambda>(S,B,I,P). P) SBIP"

  definition seg_start :: "nat \<Rightarrow> nat" \<comment> \<open>Start index of segment, inclusive\<close>
    where "seg_start i \<equiv> B!i" 

  definition seg_end :: "nat \<Rightarrow> nat"  \<comment> \<open>End index of segment, exclusive\<close>
    where "seg_end i \<equiv> if i+1 = length B then length S else B!(i+1)"

  definition seg :: "nat \<Rightarrow> 'a set" \<comment> \<open>Collapsed set at index\<close>
    where "seg i \<equiv> {S!j | j. seg_start i \<le> j \<and> j < seg_end i }"

  definition "p_\<alpha> \<equiv> map seg [0..<length B]" \<comment> \<open>Collapsed path\<close>

  definition "D_\<alpha> \<equiv> {v. I v = Some DONE}" \<comment> \<open>Done nodes\<close>
  
  definition "pE_\<alpha> \<equiv> { (u,v) . \<exists>j I. (j,I)\<in>set P \<and> u = S!j \<and> v\<in>I }" 
    \<comment> \<open>Pending edges\<close>

  definition "\<alpha> \<equiv> (p_\<alpha>,D_\<alpha>,pE_\<alpha>)" \<comment> \<open>Abstract state\<close>

end

lemma GS_sel_simps[simp]:
  "GS.S (S,B,I,P) = S"
  "GS.B (S,B,I,P) = B"
  "GS.I (S,B,I,P) = I"
  "GS.P (S,B,I,P) = P"
  unfolding GS.S_def GS.B_def GS.I_def GS.P_def
  by auto

context GS begin
  lemma seg_start_indep[simp]: "GS.seg_start (S',B,I',P') = seg_start"  
    unfolding GS.seg_start_def[abs_def] by (auto)
  lemma seg_end_indep[simp]: "GS.seg_end (S,B,I',P') = seg_end"  
    unfolding GS.seg_end_def[abs_def] by auto
  lemma seg_indep[simp]: "GS.seg (S,B,I',P') = seg"  
    unfolding GS.seg_def[abs_def] by auto
  lemma p_\<alpha>_indep[simp]: "GS.p_\<alpha> (S,B,I',P') = p_\<alpha>"
    unfolding GS.p_\<alpha>_def by auto

  lemma D_\<alpha>_indep[simp]: "GS.D_\<alpha> (S',B',I,P') = D_\<alpha>"
    unfolding GS.D_\<alpha>_def by auto

  lemma pE_\<alpha>_indep[simp]: "GS.pE_\<alpha> (S,B',I',P) = pE_\<alpha>" 
    unfolding GS.pE_\<alpha>_def by auto

  definition find_seg \<comment> \<open>Abs-path index for stack index\<close>
    where "find_seg j \<equiv> Max {i. i<length B \<and> B!i\<le>j}"

  definition S_idx_of \<comment> \<open>Stack index for node\<close>
    where "S_idx_of v \<equiv> case I v of Some (STACK i) \<Rightarrow> i"

end

locale GS_invar = GS +
  assumes B_in_bound: "set B \<subseteq> {0..<length S}"
  assumes B_sorted: "sorted B"
  assumes B_distinct: "distinct B"
  assumes B0: "S\<noteq>[] \<Longrightarrow> B\<noteq>[] \<and> B!0=0"
  assumes S_distinct: "distinct S"

  assumes I_consistent: "(I v = Some (STACK j)) \<longleftrightarrow> (j<length S \<and> v = S!j)"
  
  assumes P_sorted: "sorted (map fst P)"
  assumes P_distinct: "distinct (map fst P)"
  assumes P_bound: "set P \<subseteq> {0..<length S}\<times>Collect ((\<noteq>) {})"
begin
  lemma locale_this: "GS_invar SBIP" by unfold_locales

end

definition "oGS_rel \<equiv> br oGS_\<alpha> oGS_invar"
lemma oGS_rel_sv[intro!,simp,relator_props]: "single_valued oGS_rel"
  unfolding oGS_rel_def by auto

definition "GS_rel \<equiv> br GS.\<alpha> GS_invar"
lemma GS_rel_sv[intro!,simp,relator_props]: "single_valued GS_rel"
  unfolding GS_rel_def by auto

context GS_invar
begin
  lemma empty_eq: "S=[] \<longleftrightarrow> B=[]"
    using B_in_bound B0 by auto

  lemma B_in_bound': "i<length B \<Longrightarrow> B!i < length S"
    using B_in_bound nth_mem by fastforce

  lemma seg_start_bound:
    assumes A: "i<length B" shows "seg_start i < length S"
    using B_in_bound nth_mem[OF A] unfolding seg_start_def by auto

  lemma seg_end_bound:
    assumes A: "i<length B" shows "seg_end i \<le> length S"
  proof (cases "i+1=length B")
    case True thus ?thesis by (simp add: seg_end_def)
  next
    case False with A have "i+1<length B" by simp
    from nth_mem[OF this] B_in_bound have " B ! (i + 1) < length S" by auto
    thus ?thesis using False by (simp add: seg_end_def)
  qed

  lemma seg_start_less_end: "i<length B \<Longrightarrow> seg_start i < seg_end i"
    unfolding seg_start_def seg_end_def
    using B_in_bound' distinct_sorted_mono[OF B_sorted B_distinct]
    by auto

  lemma seg_end_less_start: "\<lbrakk>i<j; j<length B\<rbrakk> \<Longrightarrow> seg_end i \<le> seg_start j"
    unfolding seg_start_def seg_end_def
    by (auto simp: distinct_sorted_mono_iff[OF B_distinct B_sorted])

  lemma find_seg_bounds:
    assumes A: "j<length S"
    shows "seg_start (find_seg j) \<le> j" 
    and "j < seg_end (find_seg j)" 
    and "find_seg j < length B"
  proof -
    let ?M = "{i. i<length B \<and> B!i\<le>j}"
    from A have [simp]: "B\<noteq>[]" using empty_eq by (cases S) auto
    have NE: "?M\<noteq>{}" using A B0 by (cases B) auto

    have F: "finite ?M" by auto
    
    from Max_in[OF F NE]
    have LEN: "find_seg j < length B" and LB: "B!find_seg j \<le> j"
      unfolding find_seg_def
      by auto

    thus "find_seg j < length B" by -
    
    from LB show LB': "seg_start (find_seg j) \<le> j"
      unfolding seg_start_def by simp

    moreover show UB': "j < seg_end (find_seg j)"
      unfolding seg_end_def 
    proof (split if_split, intro impI conjI)
      show "j<length S" using A .
      
      assume "find_seg j + 1 \<noteq> length B" 
      with LEN have P1: "find_seg j + 1 < length B" by simp

      show "j < B ! (find_seg j + 1)"
      proof (rule ccontr, simp only: linorder_not_less)
        assume P2: "B ! (find_seg j + 1) \<le> j"
        with P1 Max_ge[OF F, of "find_seg j + 1", folded find_seg_def]
        show False by simp
      qed
    qed
  qed
    
  lemma find_seg_correct:
    assumes A: "j<length S"
    shows "S!j \<in> seg (find_seg j)" and "find_seg j < length B"
    using find_seg_bounds[OF A]
      unfolding seg_def by auto

  lemma set_p_\<alpha>_is_set_S:
    "\<Union>(set p_\<alpha>) = set S"
    apply rule
    unfolding p_\<alpha>_def seg_def[abs_def]
    using seg_end_bound apply fastforce []

    apply (auto simp: in_set_conv_nth)

    using find_seg_bounds
    apply (fastforce simp: in_set_conv_nth)
    done

  lemma S_idx_uniq: 
    "\<lbrakk>i<length S; j<length S\<rbrakk> \<Longrightarrow> S!i=S!j \<longleftrightarrow> i=j"
    using S_distinct
    by (simp add: nth_eq_iff_index_eq)

  lemma S_idx_of_correct: 
    assumes A: "v\<in>\<Union>(set p_\<alpha>)"
    shows "S_idx_of v < length S" and "S!S_idx_of v = v"
  proof -
    from A have "v\<in>set S" by (simp add: set_p_\<alpha>_is_set_S)
    then obtain j where G1: "j<length S" "v=S!j" by (auto simp: in_set_conv_nth)
    with I_consistent have "I v = Some (STACK j)" by simp
    hence "S_idx_of v = j" by (simp add: S_idx_of_def)
    with G1 show "S_idx_of v < length S" and "S!S_idx_of v = v" by simp_all
  qed

  lemma p_\<alpha>_disjoint_sym: 
    shows "\<forall>i j v. i<length p_\<alpha> \<and> j<length p_\<alpha> \<and> v\<in>p_\<alpha>!i \<and> v\<in>p_\<alpha>!j \<longrightarrow> i=j"
  proof (intro allI impI, elim conjE)
    fix i j v
    assume A: "i < length p_\<alpha>" "j < length p_\<alpha>" "v \<in> p_\<alpha> ! i" "v \<in> p_\<alpha> ! j"
    from A have LI: "i<length B" and LJ: "j<length B" by (simp_all add: p_\<alpha>_def)

    from A have B1: "seg_start j < seg_end i" and B2: "seg_start i < seg_end j"
      unfolding p_\<alpha>_def seg_def[abs_def]
      apply clarsimp_all
      apply (subst (asm) S_idx_uniq)
      apply (metis dual_order.strict_trans1 seg_end_bound)
      apply (metis dual_order.strict_trans1 seg_end_bound)
      apply simp
      apply (subst (asm) S_idx_uniq)
      apply (metis dual_order.strict_trans1 seg_end_bound)
      apply (metis dual_order.strict_trans1 seg_end_bound)
      apply simp
      done

    from B1 have B1: "(B!j < B!Suc i \<and> Suc i < length B) \<or> i=length B - 1"
      using LI unfolding seg_start_def seg_end_def by (auto split: if_split_asm)

    from B2 have B2: "(B!i < B!Suc j \<and> Suc j < length B) \<or> j=length B - 1"
      using LJ unfolding seg_start_def seg_end_def by (auto split: if_split_asm)

    from B1 have B1: "j<Suc i \<or> i=length B - 1"
      using LI LJ distinct_sorted_strict_mono_iff[OF B_distinct B_sorted]
      by auto

    from B2 have B2: "i<Suc j \<or> j=length B - 1"
      using LI LJ distinct_sorted_strict_mono_iff[OF B_distinct B_sorted]
      by auto

    from B1 B2 show "i=j"
      using LI LJ
      by auto
  qed

end


subsection \<open>Refinement of the Operations\<close>

definition GS_initial_impl :: "'a oGS \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a GS" where
  "GS_initial_impl I v0 succs \<equiv> (
    [v0],
    [0],
    I(v0\<mapsto>(STACK 0)),
    if succs={} then [] else [(0,succs)])"

context GS
begin
  definition "push_impl v succs \<equiv> 
    let
      _ = stat_newnode ();
      j = length S;
      S = S@[v];
      B = B@[j];
      I = I(v \<mapsto> STACK j);
      P = if succs={} then P else P@[(j,succs)]
    in
      (S,B,I,P)"

  
  definition mark_as_done 
    where "\<And>l u I. mark_as_done l u I \<equiv> do {
    (_,I)\<leftarrow>WHILET 
      (\<lambda>(l,I). l<u) 
      (\<lambda>(l,I). do { ASSERT (l<length S); RETURN (Suc l,I(S!l \<mapsto> DONE))}) 
      (l,I);
    RETURN I
  }"

  definition mark_as_done_abs where
    "\<And>l u I. mark_as_done_abs l u I 
    \<equiv> (\<lambda>v. if v\<in>{S!j | j. l\<le>j \<and> j<u} then Some DONE else I v)"

  lemma mark_as_done_aux:
    fixes l u I
    shows "\<lbrakk>l<u; u\<le>length S\<rbrakk> \<Longrightarrow> mark_as_done l u I 
    \<le> SPEC (\<lambda>r. r = mark_as_done_abs l u I)"
    unfolding mark_as_done_def mark_as_done_abs_def
    apply (refine_rcg 
      WHILET_rule[where 
        I="\<lambda>(l',I'). 
          I' = (\<lambda>v. if v\<in>{S!j | j. l\<le>j \<and> j<l'} then Some DONE else I v)
          \<and> l\<le>l' \<and> l'\<le>u"
        and R="measure (\<lambda>(l',_). u-l')" 
      ]
      refine_vcg)
    
    apply (auto intro!: ext simp: less_Suc_eq)
    done    

  definition "pop_impl \<equiv> 
    do {
      let lsi = length B - 1;
      ASSERT (lsi<length B);
      I \<leftarrow> mark_as_done (seg_start lsi) (seg_end lsi) I;
      ASSERT (B\<noteq>[]);
      let S = take (last B) S;
      ASSERT (B\<noteq>[]);
      let B = butlast B;
      RETURN (S,B,I,P)
    }"

  definition "sel_rem_last \<equiv> 
    if P=[] then 
      RETURN (None,(S,B,I,P))
    else do {
      let (j,succs) = last P;
      ASSERT (length B - 1 < length B);
      if j \<ge> seg_start (length B - 1) then do {
        ASSERT (succs\<noteq>{});
        v \<leftarrow> SPEC (\<lambda>x. x\<in>succs);
        let succs = succs - {v};
        ASSERT (P\<noteq>[] \<and> length P - 1 < length P);
        let P = (if succs={} then butlast P else P[length P - 1 := (j,succs)]);
        RETURN (Some v,(S,B,I,P))
      } else RETURN (None,(S,B,I,P))
    }" 


  definition "find_seg_impl j \<equiv> find_max_nat (length B) (\<lambda>i. B!i\<le>j)"

  lemma (in GS_invar) find_seg_impl:
    "j<length S \<Longrightarrow> find_seg_impl j = find_seg j"
    unfolding find_seg_impl_def
    thm find_max_nat_correct
    apply (subst find_max_nat_correct)
    apply (simp add: B0)
    apply (simp add: B0)
    apply (simp add: find_seg_def)
    done


  definition "idx_of_impl v \<equiv> do {
      ASSERT (\<exists>i. I v = Some (STACK i));
      let j = S_idx_of v;
      ASSERT (j<length S);
      let i = find_seg_impl j;
      RETURN i
    }"

  definition "collapse_impl v \<equiv> 
    do { 
      i\<leftarrow>idx_of_impl v;
      ASSERT (i+1 \<le> length B);
      let B = take (i+1) B;
      RETURN (S,B,I,P)
    }"

end

lemma (in -) GS_initial_correct: 
  assumes REL: "(I,D)\<in>oGS_rel"
  assumes A: "v0\<notin>D"
  shows "GS.\<alpha> (GS_initial_impl I v0 succs) = ([{v0}],D,{v0}\<times>succs)" (is ?G1)
  and "GS_invar (GS_initial_impl I v0 succs)" (is ?G2)
proof -
  from REL have [simp]: "D = oGS_\<alpha> I" and I: "oGS_invar I"
    by (simp_all add: oGS_rel_def br_def)

  from I have [simp]: "\<And>j v. I v \<noteq> Some (STACK j)"
    by (simp add: oGS_invar_def)

  show ?G1
    unfolding GS.\<alpha>_def GS_initial_impl_def
    apply (simp split del: if_split) apply (intro conjI)

    unfolding GS.p_\<alpha>_def GS.seg_def[abs_def] GS.seg_start_def GS.seg_end_def
    apply (auto) []

    using A unfolding GS.D_\<alpha>_def apply (auto simp: oGS_\<alpha>_def) []

    unfolding GS.pE_\<alpha>_def apply auto []
    done

  show ?G2
    unfolding GS_initial_impl_def
    apply unfold_locales
    apply auto
    done
qed

context GS_invar
begin
  lemma push_correct:
    assumes A: "v\<notin>\<Union>(set p_\<alpha>)" and B: "v\<notin>D_\<alpha>"
    shows "GS.\<alpha> (push_impl v succs) = (p_\<alpha>@[{v}],D_\<alpha>,pE_\<alpha> \<union> {v}\<times>succs)" 
      (is ?G1)
    and "GS_invar (push_impl v succs)" (is ?G2)
  proof -

    note [simp] = Let_def

    have A1: "GS.D_\<alpha> (push_impl v succs) = D_\<alpha>"
      using B
      by (auto simp: push_impl_def GS.D_\<alpha>_def)

    have iexI: "\<And>a b j P. \<lbrakk>a!j = b!j; P j\<rbrakk> \<Longrightarrow> \<exists>j'. a!j = b!j' \<and> P j'"
      by blast

    have A2: "GS.p_\<alpha> (push_impl v succs) = p_\<alpha> @ [{v}]"
      unfolding push_impl_def GS.p_\<alpha>_def GS.seg_def[abs_def] 
        GS.seg_start_def GS.seg_end_def
      apply (clarsimp split del: if_split)

      apply clarsimp
      apply safe
      apply (((rule iexI)?, 
        (auto  
          simp: nth_append nat_in_between_eq 
          dest: order.strict_trans[OF _ B_in_bound']
        )) []
      ) +
      done

    have iexI2: "\<And>j I Q. \<lbrakk>(j,I)\<in>set P; (j,I)\<in>set P \<Longrightarrow> Q j\<rbrakk> \<Longrightarrow> \<exists>j. Q j"
      by blast

    have A3: "GS.pE_\<alpha> (push_impl v succs) = pE_\<alpha> \<union> {v} \<times> succs"
      unfolding push_impl_def GS.pE_\<alpha>_def
      using P_bound
      apply (force simp: nth_append elim!: iexI2)
      done

    show ?G1
      unfolding GS.\<alpha>_def
      by (simp add: A1 A2 A3)

    show ?G2
      apply unfold_locales
      unfolding push_impl_def
      apply simp_all

      using B_in_bound B_sorted B_distinct apply (auto simp: sorted_append) [3]
      using B_in_bound B0 apply (cases S) apply (auto simp: nth_append) [2]

      using S_distinct A apply (simp add: set_p_\<alpha>_is_set_S)

      using A I_consistent 
      apply (auto simp: nth_append set_p_\<alpha>_is_set_S split: if_split_asm) []
      
      using P_sorted P_distinct P_bound apply (auto simp: sorted_append) [3]
      done
  qed

  lemma no_last_out_P_aux:
    assumes NE: "p_\<alpha>\<noteq>[]" and NS: "pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}"
    shows "set P \<subseteq> {0..<last B} \<times> UNIV"
  proof -
    {
      fix j I
      assume jII: "(j,I)\<in>set P"
        and JL: "last B\<le>j"
      with P_bound have JU: "j<length S" and INE: "I\<noteq>{}" by auto
      with JL JU have "S!j \<in> last p_\<alpha>"
        using NE
        unfolding p_\<alpha>_def 
        apply (auto 
          simp: last_map seg_def seg_start_def seg_end_def last_conv_nth) 
        done
      moreover from jII have "{S!j} \<times> I \<subseteq> pE_\<alpha>" unfolding pE_\<alpha>_def
        by auto
      moreover note INE NS
      ultimately have False by blast
    } thus ?thesis by fastforce
  qed

  lemma pop_correct:
    assumes NE: "p_\<alpha>\<noteq>[]" and NS: "pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}"
    shows "pop_impl 
      \<le> \<Down>GS_rel (SPEC (\<lambda>r. r=(butlast p_\<alpha>, D_\<alpha> \<union> last p_\<alpha>, pE_\<alpha>)))"
  proof -
    have iexI: "\<And>a b j P. \<lbrakk>a!j = b!j; P j\<rbrakk> \<Longrightarrow> \<exists>j'. a!j = b!j' \<and> P j'"
      by blast
    
    have [simp]: "\<And>n. n - Suc 0 \<noteq> n \<longleftrightarrow> n\<noteq>0" by auto

    from NE have BNE: "B\<noteq>[]"
      unfolding p_\<alpha>_def by auto

    {
      fix i j
      assume B: "j<B!i" and A: "i<length B"
      note B
      also from sorted_nth_mono[OF B_sorted, of i "length B - 1"] A 
      have "B!i \<le> last B"
        by (simp add: last_conv_nth)
      finally have "j < last B" .
      hence "take (last B) S ! j = S ! j" 
        and "take (B!(length B - Suc 0)) S !j = S!j"
        by (simp_all add: last_conv_nth BNE)
    } note AUX1=this

    {
      fix v j
      have "(mark_as_done_abs 
              (seg_start (length B - Suc 0))
              (seg_end (length B - Suc 0)) I v = Some (STACK j)) 
        \<longleftrightarrow> (j < length S \<and> j < last B \<and> v = take (last B) S ! j)"
        apply (simp add: mark_as_done_abs_def)
        apply safe []
        using I_consistent
        apply (clarsimp_all
          simp: seg_start_def seg_end_def last_conv_nth BNE
          simp: S_idx_uniq)

        apply (force)
        apply (subst nth_take)
        apply force
        apply force
        done
    } note AUX2 = this

    define ci where "ci = ( 
      take (last B) S, 
      butlast B,
      mark_as_done_abs 
        (seg_start (length B - Suc 0)) (seg_end (length B - Suc 0)) I,
      P)"

    have ABS: "GS.\<alpha> ci = (butlast p_\<alpha>, D_\<alpha> \<union> last p_\<alpha>, pE_\<alpha>)"
      apply (simp add: GS.\<alpha>_def ci_def)
      apply (intro conjI)
      apply (auto  
        simp del: map_butlast
        simp add: map_butlast[symmetric] butlast_upt
        simp add: GS.p_\<alpha>_def GS.seg_def[abs_def] GS.seg_start_def GS.seg_end_def
        simp: nth_butlast last_conv_nth nth_take AUX1
        cong: if_cong
        intro!: iexI
        dest: order.strict_trans[OF _ B_in_bound']
      ) []

      apply (auto 
        simp: GS.D_\<alpha>_def p_\<alpha>_def last_map BNE seg_def mark_as_done_abs_def) []

      using AUX1 no_last_out_P_aux[OF NE NS]
      apply (auto simp: GS.pE_\<alpha>_def mark_as_done_abs_def elim!: bex2I) []
      done

    have INV: "GS_invar ci"
      apply unfold_locales
      apply (simp_all add: ci_def)

      using B_in_bound B_sorted B_distinct 
      apply (cases B rule: rev_cases, simp) 
      apply (auto simp: sorted_append order.strict_iff_order) [] 

      using B_sorted BNE apply (auto simp: sorted_butlast) []

      using B_distinct BNE apply (auto simp: distinct_butlast) []

      using B0 apply (cases B rule: rev_cases, simp add: BNE) 
      apply (auto simp: nth_append split: if_split_asm) []
   
      using S_distinct apply (auto) []

      apply (rule AUX2)

      using P_sorted P_distinct 
      apply (auto) [2]

      using P_bound no_last_out_P_aux[OF NE NS]
      apply (auto simp: in_set_conv_decomp)
      done
      

    show ?thesis
      unfolding pop_impl_def
      apply (refine_rcg 
        SPEC_refine refine_vcg order_trans[OF mark_as_done_aux])
      apply (simp_all add: BNE seg_start_less_end seg_end_bound)
      apply (fold ci_def)
      unfolding GS_rel_def
      apply (rule brI)
      apply (simp_all add: ABS INV)
      done
  qed


  lemma sel_rem_last_correct:
    assumes NE: "p_\<alpha>\<noteq>[]"
    shows
    "sel_rem_last \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (select_edge (p_\<alpha>,D_\<alpha>,pE_\<alpha>))"
  proof -
    {
      fix l i a b b'
      have "\<lbrakk>i<length l; l!i=(a,b)\<rbrakk> \<Longrightarrow> map fst (l[i:=(a,b')]) = map fst l"
        by (induct l arbitrary: i) (auto split: nat.split)
    } note map_fst_upd_snd_eq = this

    from NE have BNE[simp]: "B\<noteq>[]" unfolding p_\<alpha>_def by simp

    have INVAR: "sel_rem_last \<le> SPEC (GS_invar o snd)"
      unfolding sel_rem_last_def
      apply (refine_rcg refine_vcg)
      using locale_this apply (cases SBIP) apply simp

      apply simp

      using P_bound apply (cases P rule: rev_cases, auto) []

      apply simp

      apply simp apply (intro impI conjI)

      apply (unfold_locales, simp_all) []
      using B_in_bound B_sorted B_distinct B0 S_distinct I_consistent 
      apply auto [6]

      using P_sorted P_distinct 
      apply (auto simp: map_butlast sorted_butlast distinct_butlast) [2]

      using P_bound apply (auto dest: in_set_butlastD) []

      apply (unfold_locales, simp_all) []
      using B_in_bound B_sorted B_distinct B0 S_distinct I_consistent 
      apply auto [6]

      using P_sorted P_distinct 
      apply (auto simp: last_conv_nth map_fst_upd_snd_eq) [2]

      using P_bound 
      apply (cases P rule: rev_cases, simp)
      apply (auto) []

      using locale_this apply (cases SBIP) apply simp
      done


    {
      assume NS: "pE_\<alpha>\<inter>last p_\<alpha>\<times>UNIV = {}"
      hence "sel_rem_last 
        \<le> SPEC (\<lambda>r. case r of (None,SBIP') \<Rightarrow> SBIP'=SBIP | _ \<Rightarrow> False)"
        unfolding sel_rem_last_def
        apply (refine_rcg refine_vcg)
        apply (cases SBIP)
        apply simp

        apply simp
        using P_bound apply (cases P rule: rev_cases, auto) []
        apply simp

        using no_last_out_P_aux[OF NE NS]
        apply (auto simp: seg_start_def last_conv_nth) []

        apply (cases SBIP)
        apply simp
        done
    } note SPEC_E = this

    {
      assume NON_EMPTY: "pE_\<alpha>\<inter>last p_\<alpha>\<times>UNIV \<noteq> {}"

      then obtain j succs P' where 
        EFMT: "P = P'@[(j,succs)]"
        unfolding pE_\<alpha>_def
        by (cases P rule: rev_cases) auto
        
      with P_bound have J_UPPER: "j<length S" and SNE: "succs\<noteq>{}" 
        by auto

      have J_LOWER: "seg_start (length B - Suc 0) \<le> j"
      proof (rule ccontr)
        assume "\<not>(seg_start (length B - Suc 0) \<le> j)"
        hence "j < seg_start (length B - 1)" by simp
        with P_sorted EFMT 
        have P_bound': "set P \<subseteq> {0..<seg_start (length B - 1)} \<times> UNIV"
          by (auto simp: sorted_append)
        hence "pE_\<alpha> \<inter> last p_\<alpha>\<times>UNIV = {}"
          by (auto 
            simp: p_\<alpha>_def last_conv_nth seg_def pE_\<alpha>_def S_idx_uniq seg_end_def)
        thus False using NON_EMPTY by simp
      qed

      from J_UPPER J_LOWER have SJL: "S!j\<in>last p_\<alpha>" 
        unfolding p_\<alpha>_def seg_def[abs_def] seg_end_def
        by (auto simp: last_map)

      from EFMT have SSS: "{S!j}\<times>succs\<subseteq>pE_\<alpha>"
        unfolding pE_\<alpha>_def
        by auto


      {
        fix v
        assume "v\<in>succs"
        with SJL SSS have G: "(S!j,v)\<in>pE_\<alpha> \<inter> last p_\<alpha>\<times>UNIV" by auto
        
        {
          fix j' succs'
          assume "S ! j' = S ! j" "(j', succs') \<in> set P'"
          with J_UPPER P_bound S_idx_uniq EFMT have "j'=j" by auto
          with P_distinct \<open>(j', succs') \<in> set P'\<close> EFMT have False by auto
        } note AUX3=this

        have G1: "GS.pE_\<alpha> (S,B,I,P' @ [(j, succs - {v})]) = pE_\<alpha> - {(S!j, v)}"
          unfolding GS.pE_\<alpha>_def using AUX3
          by (auto simp: EFMT)
        
        {
          assume "succs\<subseteq>{v}"
          hence "GS.pE_\<alpha> (S,B,I,P' @ [(j, succs - {v})]) = GS.pE_\<alpha> (S,B,I,P')"
            unfolding GS.pE_\<alpha>_def by auto

          with G1 have "GS.pE_\<alpha> (S,B,I,P') = pE_\<alpha> - {(S!j, v)}" by simp
        } note G2 = this

        note G G1 G2
      } note AUX3 = this

      have "sel_rem_last \<le> SPEC (\<lambda>r. case r of 
        (Some v,SBIP') \<Rightarrow> \<exists>u. 
            (u,v)\<in>(pE_\<alpha>\<inter>last p_\<alpha>\<times>UNIV) 
          \<and> GS.\<alpha> SBIP' = (p_\<alpha>,D_\<alpha>,pE_\<alpha>-{(u,v)})
      | _ \<Rightarrow> False)"
        unfolding sel_rem_last_def
        apply (refine_rcg refine_vcg)

        using SNE apply (vc_solve simp: J_LOWER EFMT)

        apply (frule AUX3(1))

        apply safe

        apply (drule (1) AUX3(3)) apply (auto simp: EFMT GS.\<alpha>_def) []
        apply (drule AUX3(2)) apply (auto simp: GS.\<alpha>_def) []
        done
    } note SPEC_NE=this

    have SPEC: "sel_rem_last \<le> SPEC (\<lambda>r. case r of 
        (None, SBIP') \<Rightarrow> SBIP' = SBIP \<and> pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {} \<and> GS_invar SBIP
      | (Some v, SBIP') \<Rightarrow> \<exists>u. (u, v) \<in> pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV 
                        \<and> GS.\<alpha> SBIP' = (p_\<alpha>, D_\<alpha>, pE_\<alpha> - {(u, v)})
                        \<and> GS_invar SBIP'
    )"  
      using INVAR
      apply (cases "pE_\<alpha> \<inter> last p_\<alpha> \<times> UNIV = {}") 
      apply (frule SPEC_E)
      apply (auto split: option.splits simp: pw_le_iff; blast; fail)
      apply (frule SPEC_NE)
      apply (auto split: option.splits simp: pw_le_iff; blast; fail)
      done    
      
      
    have X1: "(\<exists>y. (y=None \<longrightarrow> \<Phi> y) \<and> (\<forall>a b. y=Some (a,b) \<longrightarrow> \<Psi> y a b)) \<longleftrightarrow>
      (\<Phi> None \<or> (\<exists>a b. \<Psi> (Some (a,b)) a b))" for \<Phi> \<Psi>
      by auto
      

    show ?thesis
      apply (rule order_trans[OF SPEC])
      unfolding select_edge_def select_def 
      apply (simp 
        add: pw_le_iff refine_pw_simps prod_rel_sv 
        del: SELECT_pw
        split: option.splits prod.splits)
      apply (fastforce simp: br_def GS_rel_def GS.\<alpha>_def)
      done  
  qed

  lemma find_seg_idx_of_correct:
    assumes A: "v\<in>\<Union>(set p_\<alpha>)"
    shows "(find_seg (S_idx_of v)) = idx_of p_\<alpha> v"
  proof -
    note S_idx_of_correct[OF A] idx_of_props[OF p_\<alpha>_disjoint_sym A]
    from find_seg_correct[OF \<open>S_idx_of v < length S\<close>] have 
      "find_seg (S_idx_of v) < length p_\<alpha>" 
      and "S!S_idx_of v \<in> p_\<alpha>!find_seg (S_idx_of v)"
      unfolding p_\<alpha>_def by auto
    from idx_of_uniq[OF p_\<alpha>_disjoint_sym this] \<open>S ! S_idx_of v = v\<close> 
    show ?thesis by auto
  qed


  lemma idx_of_correct:
    assumes A: "v\<in>\<Union>(set p_\<alpha>)"
    shows "idx_of_impl v \<le> SPEC (\<lambda>x. x=idx_of p_\<alpha> v \<and> x<length B)"
    using assms
    unfolding idx_of_impl_def
    apply (refine_rcg refine_vcg)
    apply (metis I_consistent in_set_conv_nth set_p_\<alpha>_is_set_S)
    apply (erule S_idx_of_correct)
    apply (simp add: find_seg_impl find_seg_idx_of_correct)
    by (metis find_seg_correct(2) find_seg_impl)

  lemma collapse_correct:
    assumes A: "v\<in>\<Union>(set p_\<alpha>)"
    shows "collapse_impl v \<le>\<Down>GS_rel (SPEC (\<lambda>r. r=collapse v \<alpha>))"
  proof -
    {
      fix i
      assume "i<length p_\<alpha>"
      hence ILEN: "i<length B" by (simp add: p_\<alpha>_def)

      let ?SBIP' = "(S, take (Suc i) B, I, P)"

      {
        have [simp]: "GS.seg_start ?SBIP' i = seg_start i"
          by (simp add: GS.seg_start_def)

        have [simp]: "GS.seg_end ?SBIP' i = seg_end (length B - 1)"
          using ILEN by (simp add: GS.seg_end_def min_absorb2)

        {
          fix j
          assume B: "seg_start i \<le> j" "j < seg_end (length B - Suc 0)"
          hence "j<length S" using ILEN seg_end_bound 
          proof -
            note B(2)
            also from \<open>i<length B\<close> have "(length B - Suc 0) < length B" by auto
            from seg_end_bound[OF this] 
            have "seg_end (length B - Suc 0) \<le> length S" .
            finally show ?thesis .
          qed

          have "i \<le> find_seg j \<and> find_seg j < length B 
            \<and> seg_start (find_seg j) \<le> j \<and> j < seg_end (find_seg j)" 
          proof (intro conjI)
            show "i\<le>find_seg j"
              by (metis le_trans not_less B(1) find_seg_bounds(2) 
                seg_end_less_start ILEN \<open>j < length S\<close>)
          qed (simp_all add: find_seg_bounds[OF \<open>j<length S\<close>])
        } note AUX1 = this

        {
          fix Q and j::nat
          assume "Q j"
          hence "\<exists>i. S!j = S!i \<and> Q i"
            by blast
        } note AUX_ex_conj_SeqSI = this

        have "GS.seg ?SBIP' i = \<Union> (seg ` {i..<length B})"
          unfolding GS.seg_def[abs_def]
          apply simp
          apply (rule)
          apply (auto dest!: AUX1) []

          (* The following three lines complete the proof. AUX_ex_conj_SeqSI
            and all stuff 
            below would be unnecessary, if smt would be allowed for AFP.
          apply (auto simp: seg_start_def seg_end_def split: if_split_asm)
          apply (smt distinct_sorted_mono[OF B_sorted B_distinct])
          apply (smt distinct_sorted_mono[OF B_sorted B_distinct] B_in_bound')
          *)

          apply (auto 
            simp: seg_start_def seg_end_def 
            split: if_split_asm
            intro!: AUX_ex_conj_SeqSI
          )

         apply (metis diff_diff_cancel le_diff_conv le_eq_less_or_eq 
           lessI trans_le_add1 
           distinct_sorted_mono[OF B_sorted B_distinct, of i])

         apply (metis diff_diff_cancel le_diff_conv le_eq_less_or_eq 
           trans_le_add1 distinct_sorted_mono[OF B_sorted B_distinct, of i])
         
         apply (metis (hide_lams, no_types) Suc_lessD Suc_lessI less_trans_Suc
           B_in_bound')
         done
      } note AUX2 = this
      
      from ILEN have "GS.p_\<alpha> (S, take (Suc i) B, I, P) = collapse_aux p_\<alpha> i"
        unfolding GS.p_\<alpha>_def collapse_aux_def
        apply (simp add: min_absorb2 drop_map)
        apply (rule conjI)
        apply (auto 
          simp: GS.seg_def[abs_def] GS.seg_start_def GS.seg_end_def take_map) []

        apply (simp add: AUX2)
        done
    } note AUX1 = this

    from A obtain i where [simp]: "I v = Some (STACK i)"
      using I_consistent set_p_\<alpha>_is_set_S
      by (auto simp: in_set_conv_nth)

    {
      have "(collapse_aux p_\<alpha> (idx_of p_\<alpha> v), D_\<alpha>, pE_\<alpha>) =
        GS.\<alpha> (S, take (Suc (idx_of p_\<alpha> v)) B, I, P)"
      unfolding GS.\<alpha>_def
      using idx_of_props[OF p_\<alpha>_disjoint_sym A]
      by (simp add: AUX1)
    } note ABS=this

    {
      have "GS_invar (S, take (Suc (idx_of p_\<alpha> v)) B, I, P)"
        apply unfold_locales
        apply simp_all

        using B_in_bound B_sorted B_distinct
        apply (auto simp: sorted_take dest: in_set_takeD) [3]

        using B0 S_distinct apply auto [2]

        using I_consistent apply simp

        using P_sorted P_distinct P_bound apply auto [3]
        done
    } note INV=this

    show ?thesis
      unfolding collapse_impl_def
      apply (refine_rcg SPEC_refine refine_vcg order_trans[OF idx_of_correct])

      apply fact
      apply (metis discrete)

      apply (simp add: collapse_def \<alpha>_def find_seg_impl)
      unfolding GS_rel_def
      apply (rule brI)
        apply (rule ABS)
        apply (rule INV)
      done
  qed

end

text \<open>Technical adjustment for avoiding case-splits for definitions
  extracted from GS-locale\<close>
lemma opt_GSdef: "f \<equiv> g \<Longrightarrow> f s \<equiv> case s of (S,B,I,P) \<Rightarrow> g (S,B,I,P)" by auto

lemma ext_def: "f\<equiv>g \<Longrightarrow> f x \<equiv> g x" by auto

context fr_graph begin
  definition "push_impl v s \<equiv> GS.push_impl s v (E``{v})" 
  lemmas push_impl_def_opt = 
    push_impl_def[abs_def, 
    THEN ext_def, THEN opt_GSdef, unfolded GS.push_impl_def GS_sel_simps]

  text \<open>Definition for presentation\<close>
  lemma "push_impl v (S,B,I,P) \<equiv> (S@[v], B@[length S], I(v\<mapsto>STACK (length S)),
    if E``{v}={} then P else P@[(length S,E``{v})])"
    unfolding push_impl_def GS.push_impl_def GS.P_def GS.S_def
    by (auto simp: Let_def)

  lemma GS_\<alpha>_split: 
    "GS.\<alpha> s = (p,D,pE) \<longleftrightarrow> (p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s)"
    "(p,D,pE) = GS.\<alpha> s \<longleftrightarrow> (p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s)"
    by (auto simp add: GS.\<alpha>_def)

  lemma push_refine:
    assumes A: "(s,(p,D,pE))\<in>GS_rel" "(v,v')\<in>Id"
    assumes B: "v\<notin>\<Union>(set p)" "v\<notin>D"
    shows "(push_impl v s, push v' (p,D,pE))\<in>GS_rel"
  proof -
    from A have [simp]: "p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s" "v'=v" 
      and INV: "GS_invar s"
      by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)

    from INV B show ?thesis
      by (auto 
        simp: GS_rel_def br_def GS_invar.push_correct push_impl_def push_def)
  qed

  definition "pop_impl s \<equiv> GS.pop_impl s"
  lemmas pop_impl_def_opt = 
    pop_impl_def[abs_def, THEN opt_GSdef, unfolded GS.pop_impl_def
    GS.mark_as_done_def GS.seg_start_def GS.seg_end_def 
    GS_sel_simps]

  lemma pop_refine:
    assumes A: "(s,(p,D,pE))\<in>GS_rel"
    assumes B: "p \<noteq> []" "pE \<inter> last p \<times> UNIV = {}"
    shows "pop_impl s \<le> \<Down>GS_rel (RETURN (pop (p,D,pE)))"
  proof -
    from A have [simp]: "p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s" 
      and INV: "GS_invar s"
      by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)

    show ?thesis
      unfolding pop_impl_def[abs_def] pop_def
      apply (rule order_trans[OF GS_invar.pop_correct])
      using INV B
      apply (simp_all add: Un_commute RETURN_def) 
      done
  qed

  thm pop_refine[no_vars]

  definition "collapse_impl v s \<equiv> GS.collapse_impl s v"
  lemmas collapse_impl_def_opt = 
    collapse_impl_def[abs_def, 
    THEN ext_def, THEN opt_GSdef, unfolded GS.collapse_impl_def GS_sel_simps]

  lemma collapse_refine:
    assumes A: "(s,(p,D,pE))\<in>GS_rel" "(v,v')\<in>Id"
    assumes B: "v'\<in>\<Union>(set p)"
    shows "collapse_impl v s \<le>\<Down>GS_rel (RETURN (collapse v' (p,D,pE)))"
  proof -
    from A have [simp]: "p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s" "v'=v" 
      and INV: "GS_invar s"
      by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)

    show ?thesis
      unfolding collapse_impl_def[abs_def]
      apply (rule order_trans[OF GS_invar.collapse_correct])
      using INV B by (simp_all add: GS.\<alpha>_def RETURN_def)
  qed

  definition "select_edge_impl s \<equiv> GS.sel_rem_last s"
  lemmas select_edge_impl_def_opt = 
    select_edge_impl_def[abs_def, 
      THEN opt_GSdef, 
      unfolded GS.sel_rem_last_def GS.seg_start_def GS_sel_simps]

  lemma select_edge_refine: 
    assumes A: "(s,(p,D,pE))\<in>GS_rel"
    assumes NE: "p \<noteq> []"
    shows "select_edge_impl s \<le> \<Down>(Id \<times>\<^sub>r GS_rel) (select_edge (p,D,pE))"
  proof -
    from A have [simp]: "p=GS.p_\<alpha> s \<and> D=GS.D_\<alpha> s \<and> pE=GS.pE_\<alpha> s" 
      and INV: "GS_invar s"
      by (auto simp add: GS_rel_def br_def GS_\<alpha>_split)

    from INV NE show ?thesis
      unfolding select_edge_impl_def
      using GS_invar.sel_rem_last_correct[OF INV] NE
      by (simp)
  qed

  definition "initial_impl v0 I \<equiv> GS_initial_impl I v0 (E``{v0})"

  lemma initial_refine:
    "\<lbrakk>v0\<notin>D0; (I,D0)\<in>oGS_rel; (v0i,v0)\<in>Id\<rbrakk> 
    \<Longrightarrow> (initial_impl v0i I,initial v0 D0)\<in>GS_rel"
    unfolding initial_impl_def GS_rel_def br_def
    apply (simp_all add: GS_initial_correct)
    apply (auto simp: initial_def)
    done


  definition "path_is_empty_impl s \<equiv> GS.S s = []"
  lemma path_is_empty_refine: 
    "GS_invar s \<Longrightarrow> path_is_empty_impl s \<longleftrightarrow> GS.p_\<alpha> s=[]"
    unfolding path_is_empty_impl_def GS.p_\<alpha>_def GS_invar.empty_eq
    by auto

  definition (in GS) "is_on_stack_impl v 
    \<equiv> case I v of Some (STACK _) \<Rightarrow> True | _ \<Rightarrow> False"

  lemma (in GS_invar) is_on_stack_impl_correct:
    shows "is_on_stack_impl v \<longleftrightarrow> v\<in>\<Union>(set p_\<alpha>)"
    unfolding is_on_stack_impl_def
    using I_consistent[of v]
    apply (force 
      simp: set_p_\<alpha>_is_set_S in_set_conv_nth 
      split: option.split node_state.split)
    done

  definition "is_on_stack_impl v s \<equiv> GS.is_on_stack_impl s v"
  lemmas is_on_stack_impl_def_opt = 
    is_on_stack_impl_def[abs_def, THEN ext_def, THEN opt_GSdef, 
      unfolded GS.is_on_stack_impl_def GS_sel_simps]

  lemma is_on_stack_refine:
    "\<lbrakk> GS_invar s \<rbrakk> \<Longrightarrow> is_on_stack_impl v s \<longleftrightarrow> v\<in>\<Union>(set (GS.p_\<alpha> s))"
    unfolding is_on_stack_impl_def GS_rel_def br_def
    by (simp add: GS_invar.is_on_stack_impl_correct)


  definition (in GS) "is_done_impl v 
    \<equiv> case I v of Some DONE \<Rightarrow> True | _ \<Rightarrow> False"

  lemma (in GS_invar) is_done_impl_correct:
    shows "is_done_impl v \<longleftrightarrow> v\<in>D_\<alpha>"
    unfolding is_done_impl_def D_\<alpha>_def
    apply (auto split: option.split node_state.split)
    done

  definition "is_done_oimpl v I \<equiv> case I v of Some DONE \<Rightarrow> True | _ \<Rightarrow> False"

  definition "is_done_impl v s \<equiv> GS.is_done_impl s v"

  lemma is_done_orefine:
    "\<lbrakk> oGS_invar s \<rbrakk> \<Longrightarrow> is_done_oimpl v s \<longleftrightarrow> v\<in>oGS_\<alpha> s"
    unfolding is_done_oimpl_def oGS_rel_def br_def
    by (auto 
      simp: oGS_invar_def oGS_\<alpha>_def 
      split: option.splits node_state.split)

  lemma is_done_refine:
    "\<lbrakk> GS_invar s \<rbrakk> \<Longrightarrow> is_done_impl v s \<longleftrightarrow> v\<in>GS.D_\<alpha> s"
    unfolding is_done_impl_def GS_rel_def br_def
    by (simp add: GS_invar.is_done_impl_correct)

  lemma oinitial_refine: "(Map.empty, {}) \<in> oGS_rel"
    by (auto simp: oGS_rel_def br_def oGS_\<alpha>_def oGS_invar_def)

end

subsection \<open>Refined Skeleton Algorithm\<close>

context fr_graph begin

  lemma I_to_outer:
    assumes "((S, B, I, P), ([], D, {})) \<in> GS_rel"
    shows "(I,D)\<in>oGS_rel"
    using assms
    unfolding GS_rel_def oGS_rel_def br_def oGS_\<alpha>_def GS.\<alpha>_def GS.D_\<alpha>_def GS_invar_def oGS_invar_def
    apply (auto simp: GS.p_\<alpha>_def)
    done
  
  
  definition skeleton_impl :: "'v oGS nres" where
    "skeleton_impl \<equiv> do {
      stat_start_nres;
      let I=Map.empty;
      r \<leftarrow> FOREACHi (\<lambda>it I. outer_invar it (oGS_\<alpha> I)) V0 (\<lambda>v0 I0. do {
        if \<not>is_done_oimpl v0 I0 then do {
          let s = initial_impl v0 I0;

          (S,B,I,P)\<leftarrow>WHILEIT (invar v0 (oGS_\<alpha> I0) o GS.\<alpha>)
            (\<lambda>s. \<not>path_is_empty_impl s) (\<lambda>s.
          do {
            \<comment> \<open>Select edge from end of path\<close>
            (vo,s) \<leftarrow> select_edge_impl s;

            case vo of 
              Some v \<Rightarrow> do {
                if is_on_stack_impl v s then do {
                  collapse_impl v s
                } else if \<not>is_done_impl v s then do {
                  \<comment> \<open>Edge to new node. Append to path\<close>
                  RETURN (push_impl v s)
                } else do {
                  \<comment> \<open>Edge to done node. Skip\<close>
                  RETURN s
                }
              }
            | None \<Rightarrow> do {
                \<comment> \<open>No more outgoing edges from current node on path\<close>
                pop_impl s
              }
          }) s;
          RETURN I
        } else
          RETURN I0
      }) I;
      stat_stop_nres;
      RETURN r
    }"

  subsubsection \<open>Correctness Theorem\<close>

  lemma "skeleton_impl \<le> \<Down>oGS_rel skeleton"
    using [[goals_limit = 1]]
    unfolding skeleton_impl_def skeleton_def
    apply (refine_rcg
      bind_refine'
      select_edge_refine push_refine 
      pop_refine
      collapse_refine 
      initial_refine
      oinitial_refine
      inj_on_id
    )
    using [[goals_limit = 5]]
    apply refine_dref_type  

    apply (vc_solve (nopre) solve: asm_rl I_to_outer
      simp: GS_rel_def br_def GS.\<alpha>_def oGS_rel_def oGS_\<alpha>_def 
      is_on_stack_refine path_is_empty_refine is_done_refine is_done_orefine
    )

    done

  lemmas skeleton_refines 
    = select_edge_refine push_refine pop_refine collapse_refine 
      initial_refine oinitial_refine
  lemmas skeleton_refine_simps 
    = GS_rel_def br_def GS.\<alpha>_def oGS_rel_def oGS_\<alpha>_def 
      is_on_stack_refine path_is_empty_refine is_done_refine is_done_orefine

  text \<open>Short proof, for presentation\<close>
  context
    notes [[goals_limit = 1]]
    notes [refine] = inj_on_id bind_refine'
  begin
  lemma "skeleton_impl \<le> \<Down>oGS_rel skeleton"
    unfolding skeleton_impl_def skeleton_def
    by (refine_rcg skeleton_refines, refine_dref_type)
       (vc_solve (nopre) solve: asm_rl I_to_outer simp: skeleton_refine_simps)  

  end

end

end
