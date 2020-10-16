section \<open>General Priority Search Trees\<close>

theory PST_General
imports 
  "HOL-Data_Structures.Tree2"
  Prio_Map_Specs
begin

text \<open>\noindent
  We show how to implement priority maps
  by augmented binary search trees. That is, the basic data structure is some 
  arbitrary binary search tree, e.g.\ a red-black tree, implementing the map 
  from @{typ 'a} to @{typ 'b} by storing pairs \<open>(k,p)\<close> in each node. At this
  point we need to assume that the keys are also linearly ordered. To 
  implement \<open>getmin\<close> efficiently we annotate/augment each node with another pair
  \<open>(k',p')\<close>, the intended result of \<open>getmin\<close> when applied to that subtree. The 
  specification of \<open>getmin\<close> tells us that \<open>(k',p')\<close> must be in that subtree and
  that \<open>p'\<close> is the minimal priority in that subtree. Thus the annotation can be 
  computed by passing the \<open>(k',p')\<close> with the minimal \<open>p'\<close> up the tree. We will 
  now make this more precise for balanced binary trees in general.
  
  We assume that our trees are either leaves of the form @{term Leaf} or nodes 
  of the form @{term "Node l (kp, b) r"} where \<open>l\<close> and \<open>r\<close> are subtrees, \<open>kp\<close> is 
  the contents of the node (a key-priority pair) and \<open>b\<close> is some additional 
  balance information (e.g.\ colour, height, size, \dots). Augmented nodes are 
  of the form \<^term>\<open>Node l (kp, (b,kp')) r\<close>.
\<close>

type_synonym ('k,'p,'c) pstree = "(('k\<times>'p) \<times> ('c \<times> ('k \<times> 'p))) tree"
 
text \<open> 
  The following invariant states that a node annotation is actually a minimal 
  key-priority pair for the node's subtree.
\<close>

fun invpst :: "('k,'p::linorder,'c) pstree \<Rightarrow> bool" where
  "invpst Leaf = True"
| "invpst (Node l (x, _,mkp) r) \<longleftrightarrow> invpst l \<and> invpst r
    \<and> is_min2 mkp (set (inorder l @ x # inorder r))"

text \<open>The implementation of \<open>getmin\<close> is trivial:\<close>

fun pst_getmin where
"pst_getmin (Node _ (_, _,a) _) = a"

lemma pst_getmin_ismin: 
  "invpst t \<Longrightarrow> t\<noteq>Leaf \<Longrightarrow> is_min2 (pst_getmin t) (set_tree t)"
by (cases t rule: pst_getmin.cases) auto

  
text \<open>  
  It remains to upgrade the existing map operations to work with augmented nodes.
  Therefore we now show how to transform any function definition on un-augmented 
  trees into one on trees augmented with \<open>(k',p')\<close> pairs. A defining equation
  \<open>f pats = e\<close> for the original type of nodes is transformed into an equation
  \<open>f pats' = e'\<close> on the augmented type of nodes as follows:
  \<^item> Every pattern @{term "Node l (kp, b) r"} in \<open>pats\<close> and \<open>e\<close> is replaced by
    @{term "Node l (kp, (b,DUMMY)) r"} to obtain \<open>pats'\<close> and \<open>e\<^sub>2\<close>.
  \<^item> To obtain \<open>e'\<close>, every expression @{term "Node l (kp, b) r"} in \<open>e\<^sub>2\<close> is 
    replaced by \<open>mkNode l kp b r\<close> where:
\<close>
  
definition "min2 \<equiv> \<lambda>(k,p) (k',p'). if p\<le>p' then (k,p) else (k',p')"

definition "min_kp a l r \<equiv> case (l,r) of
  (Leaf,Leaf) \<Rightarrow> a
| (Leaf,Node _ (_, (_,kpr)) _) \<Rightarrow> min2 a kpr
| (Node _ (_, (_,kpl)) _,Leaf) \<Rightarrow> min2 a kpl
| (Node _ (_, (_,kpl)) _,Node _ (_, (_,kpr)) _) \<Rightarrow> min2 a (min2 kpl kpr)"

definition "mkNode c l a r \<equiv> Node l (a, (c,min_kp a l r)) r"

text \<open>  
  Note that this transformation does not affect the asymptotic complexity 
  of \<open>f\<close>. Therefore the priority search tree operations have the same complexity 
  as the underlying search tree operations, i.e.\ typically logarithmic 
  (\<open>update\<close>, \<open>delete\<close>, \<open>lookup\<close>) and constant time (\<open>empty\<close>, \<open>is_empty\<close>).
\<close>

text \<open>It is straightforward to show that @{const mkNode} preserves the invariant:\<close> 
  
lemma is_min2_Empty[simp]: "\<not>is_min2 x {}"
by (auto simp: is_min2_def)

lemma is_min2_singleton[simp]: "is_min2 a {b} \<longleftrightarrow> b=a"
by (auto simp: is_min2_def)

lemma is_min2_insert:
  "is_min2 x (insert y ys) 
  \<longleftrightarrow> (y=x \<and> (\<forall>z\<in>ys. snd x \<le> snd z)) \<or> (snd x \<le> snd y \<and> is_min2 x ys)"
by (auto simp: is_min2_def)

lemma is_min2_union:
  "is_min2 x (ys \<union> zs) 
  \<longleftrightarrow> (is_min2 x ys \<and> (\<forall>z\<in>zs. snd x \<le> snd z)) 
    \<or> ((\<forall>y\<in>ys. snd x \<le> snd y) \<and> is_min2 x zs)"
by (auto simp: is_min2_def)

lemma is_min2_min2_insI: "is_min2 y ys \<Longrightarrow> is_min2 (min2 x y) (insert x ys)"
by (auto simp: is_min2_def min2_def split: prod.split)

lemma is_min2_mergeI: 
  "is_min2 x xs \<Longrightarrow> is_min2 y ys \<Longrightarrow> is_min2 (min2 x y) (xs \<union> ys)"
by (auto simp: is_min2_def min2_def split: prod.split)

theorem invpst_mkNode[simp]: "invpst (mkNode c l a r) \<longleftrightarrow> invpst l \<and> invpst r"
apply (cases l rule: invpst.cases; 
       cases r rule: invpst.cases; 
       simp add: mkNode_def min_kp_def)
  subgoal using is_min2_min2_insI by blast
 subgoal by (auto intro!: is_min2_min2_insI simp: insert_commute)
subgoal by (smt Un_insert_left Un_insert_right is_min2_mergeI is_min2_min2_insI 
                sup_assoc)
done

end
