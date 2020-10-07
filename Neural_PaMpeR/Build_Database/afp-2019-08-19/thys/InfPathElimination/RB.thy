theory RB
imports LTS ArcExt SubExt
begin

section \<open>Red-Black Graphs\<close>

text \<open>In this section we define red\hyp{}black graphs and the five operators that perform over 
them. Then, we state and prove a number of intermediate lemmas about red\hyp{}black graphs 
built using only these five operators, in other words: invariants about our method of transformation 
of red\hyp{}black graphs.

Then, we define the notion of red\hyp{}black paths and state and prove the main properties of our 
method, namely its correctness and the fact that it preserves the set of feasible paths of the 
program under analysis.\<close>

subsection \<open>Basic Definitions\<close>

subsubsection \<open>The type of Red-Black Graphs\<close>

text \<open>We represent red-black graph with the following record. We detail its fields:
\begin{itemize}
  \item @{term "red"} is the red graph, called \emph{red part}, which represents the unfolding of 
the black part. Its vertices are indexed black vertices,
  \item @{term "black"} is the original LTS, the \emph{black part},
  \item @{term "subs"} is the subsumption relation over the vertices of @{term "red"},
  \item @{term "init_conf"} is the initial configuration,
  \item @{term "confs"} is a function associating configurations to the vertices of @{term "red"},
  \item @{term "marked"} is a function associating truth values to the vertices of @{term "red"}. 
We use it to represent the fact that a particular configuration (associated to a red location) is 
known to be unsatisfiable,
  \item @{term "strengthenings"} is a function associating boolean expressions over program 
variables to vertices of the red graph. Those boolean expressions can be seen as invariants that 
the configuration associated to the ``strengthened'' red vertex has to model.
\end{itemize}

We are only interested by red-black graphs obtained by the inductive relation 
@{term "RedBlack"}. From now on, we call ``red-black graphs" the @{term pre_RedBlack}'s 
obtained by @{term "RedBlack"} and ``pre-red-black graphs" all other ones.\<close>

record ('vert,'var,'d) pre_RedBlack =
  red            :: "('vert \<times> nat) rgraph"
  black          :: "('vert,'var,'d) lts"
  subs           :: "'vert sub_rel_t"
  init_conf      :: "('var,'d) conf"
  confs          :: "('vert \<times> nat) \<Rightarrow> ('var,'d) conf"
  marked         :: "('vert \<times> nat) \<Rightarrow> bool"
  strengthenings :: "('vert \<times> nat) \<Rightarrow> ('var,'d) bexp"


text\<open>We call \emph{red vertices} the set of vertices of the red graph.\<close>


abbreviation red_vertices :: 
  "('vert,'var,'d,'x) pre_RedBlack_scheme \<Rightarrow> ('vert \<times> nat) set" 
where
  "red_vertices lts \<equiv> Graph.vertices (red lts)"


text\<open>@{term "ui_edge"} is the operation of ``unindexing'' the ends of a red edge, thus giving the 
corresponding black edge.\<close>


abbreviation ui_edge :: 
  "('vert \<times> nat) edge \<Rightarrow> 'vert edge" 
where
  "ui_edge e \<equiv> \<lparr> src = fst (src e), tgt = fst (tgt e) \<rparr>"


text \<open>We extend this idea to sequences of edges.\<close>


abbreviation ui_es ::
  "('vert \<times> nat) edge list \<Rightarrow> 'vert edge list"
where
  "ui_es es \<equiv> map ui_edge es"



subsubsection \<open>Well-formed and finite red-black graphs\<close>

locale pre_RedBlack =
  fixes prb :: "('vert,'var,'d) pre_RedBlack" (structure)


text \<open>A pre-red-black graph is well-formed if :
\begin{itemize}
  \item its red and black parts are well-formed,
  \item the root of its red part is an indexed version of the root of its black part,
  \item all red edges are indexed versions of black edges. 
\end{itemize}\<close>

locale wf_pre_RedBlack = pre_RedBlack +
  assumes red_wf           : "wf_rgraph (red prb)"
  assumes black_wf         : "wf_lts (black prb)"
  assumes consistent_roots : "fst (root (red prb)) = root (black prb)"
  assumes ui_re_are_be     : "e \<in> edges (red prb) \<Longrightarrow> ui_edge e \<in> edges (black prb)"
begin
  lemmas wf_pre_RedBlack = red_wf black_wf consistent_roots ui_re_are_be
end


text\<open>We say that a pre-red-black graph is finite if :
\begin{itemize}
  \item the path predicate of its initial configuration contains a finite number of constraints,
  \item each of these constraints contains a finite number of variables,
  \item its black part is finite (cf. definition of @{term "finite_lts"}.).
\end{itemize}\<close>


locale finite_RedBlack = pre_RedBlack +
  assumes finite_init_pred         : "finite (pred (init_conf prb))"
  assumes finite_init_pred_symvars : "\<forall> e \<in> pred (init_conf prb). finite (Bexp.vars e)"
  assumes finite_lts               : "finite_lts (black prb)"
begin
  lemmas finite_RedBlack = finite_init_pred finite_init_pred_symvars finite_lts
end






subsection \<open>Extensions of Red-Black Graphs\<close>

text \<open>We now define the five basic operations that can be performed over red-black graphs. Since 
we do not want to model the heuristics part of our prototype, a number of conditions must be met 
for each operator to apply. For example, in our prototype abstractions are performed at nodes that 
actually have successors, and these abstractions must be propagated to these successors in order to 
keep the symbolic execution graph consistent. Propagation is a complex task, and it is hard to model 
in Isabelle/HOL. This is partially due to the fact that we model the red part as a graph, in which 
propagation might not terminate. Instead, we suppose that abstraction must be performed only at 
leaves of the red part. This is equivalent to implicitly assume the existence of an oracle that 
would tell that we will need to abstract some red vertex and how to abstract it, as soon as this red 
vertex is added to the red part.\<close>

text \<open>As in the previous theories, we use predicates instead of functions to model these 
transformations to ease writing and reading definitions, proofs, etc.\<close>

subsubsection \<open>Extension by symbolic execution\<close>

text\<open>The core abstract operation of symbolic execution: take a black edge and
turn it red, by symbolic execution of its label. In the following abbreviation, @{term re} is the 
red edge obtained from the (hypothetical) black edge @{term e} that we want to symbolically execute 
and @{term c} the configuration obtained by symbolic execution of the label of @{term e}. Note that 
this extension could have been defined as a 
predicate that takes only two @{term pre_RedBlack}s and evaluates to \emph{true} if and only if 
the second has been obtained by adding a red edge as a result of symbolic execution. However, 
making the red edge and the configuration explicit allows for lighter definitions, lemmas and proofs 
in the following.\<close>

abbreviation se_extends :: 
  "('vert,'var,'d) pre_RedBlack 
   \<Rightarrow> ('vert \<times> nat) edge 
   \<Rightarrow> ('var,'d) conf 
   \<Rightarrow> ('vert,'var,'d) pre_RedBlack \<Rightarrow> bool"
where
  "se_extends prb re c prb' \<equiv> 
     ui_edge re \<in> edges (black prb) 
   \<and> ArcExt.extends (red prb) re (red prb') 
   \<and> src re \<notin> subsumees (subs prb)
   \<and> se  (confs prb (src re)) (labelling (black prb) (ui_edge re)) c
   \<and> prb' = \<lparr> red       = red prb',
              black     = black prb,
              subs      = subs prb,
              init_conf = init_conf prb,
              confs     = (confs prb) (tgt re := c),
              marked    = (marked prb)(tgt re := marked prb (src re)),
              strengthenings = strengthenings prb \<rparr>"


text \<open>Hiding the new red edge (using an existential quantifier) and the new configuration makes 
the following abbreviation more 
intuitive. However, this would require using \verb?obtain? or \verb?let ... = ... in ...? constructs 
in the following lemmas and proofs, making them harder to read and write.\<close>

abbreviation se_extends2 :: 
  "('vert,'var,'d) pre_RedBlack \<Rightarrow> ('vert,'var,'d) pre_RedBlack \<Rightarrow> bool"
where
  "se_extends2 prb prb' \<equiv> 
   \<exists> re \<in> edges (red prb'). 
     ui_edge re \<in> edges (black prb)
   \<and> ArcExt.extends (red prb) re (red prb') 
   \<and> src re \<notin> subsumees (subs prb)
   \<and> se (confs prb (src re)) (labelling (black prb) (ui_edge re)) (confs prb' (tgt re))
   \<and> black prb' = black prb
   \<and> subs prb'  = subs prb
   \<and> init_conf prb' = init_conf prb
   \<and> confs prb' = (confs prb) (tgt re := confs prb' (tgt re))
   \<and> marked prb' = (marked prb)(tgt re := marked prb (src re))
   \<and> strengthenings prb' = strengthenings prb"


subsubsection \<open>Extension by marking\<close>

text\<open>The abstract operation of mark-as-unsat. It manages the information
- provided, for example, by an external automated prover -, that the 
configuration of the red vertex @{term rv} has been proved unsatisfiable.\<close>

abbreviation mark_extends ::
  "('vert,'var,'d) pre_RedBlack \<Rightarrow> ('vert \<times> nat) \<Rightarrow> ('vert,'var,'d) pre_RedBlack \<Rightarrow> bool"
where
  "mark_extends prb rv prb' \<equiv>  
     rv \<in> red_vertices prb
   \<and> out_edges (red prb) rv = {}
   \<and> rv \<notin> subsumees (subs prb)
   \<and> rv \<notin> subsumers (subs prb)
   \<and> \<not> sat (confs prb rv)
   \<and> prb' = \<lparr> red       = red prb,
              black     = black prb,
              subs      = subs prb,
              init_conf = init_conf prb,
              confs     = confs prb,
              marked    = (\<lambda> rv'. if rv' = rv then True else marked prb rv'),
              strengthenings = strengthenings prb,
              \<dots>        = more prb \<rparr> "


subsubsection \<open>Extension by subsumption\<close>

text\<open>The abstract operation of introducing a subsumption link.\<close>

abbreviation subsum_extends ::
  "('vert,'var,'d) pre_RedBlack \<Rightarrow> 'vert sub_t \<Rightarrow> ('vert,'var,'d) pre_RedBlack \<Rightarrow> bool"
where
  "subsum_extends prb sub prb' \<equiv>
     SubExt.extends (red prb) (subs prb) sub (subs prb')
   \<and> \<not> marked prb (subsumer sub)
   \<and> \<not> marked prb (subsumee sub)
   \<and> confs prb (subsumee sub) \<sqsubseteq> confs prb (subsumer sub)
   \<and> prb' = \<lparr> red       = red prb,
              black     = black prb,
              subs      = insert sub (subs prb),
              init_conf = init_conf prb,
              confs     = confs prb,
              marked    = marked prb,
              strengthenings = strengthenings prb,
              \<dots>        = more prb \<rparr>"


subsubsection \<open>Extension by abstraction\<close>

text\<open>This operation replaces the configuration of a red vertex @{term rv} by an abstraction of 
this configuration. The way the abstraction is computed is not specified. However, besides a number 
of side conditions, it must subsume the former configuration of @{term rv} and must entail its 
safeguard condition, if any.\<close>

abbreviation abstract_extends ::
  "('vert,'var,'d) pre_RedBlack 
    \<Rightarrow> ('vert \<times> nat) 
    \<Rightarrow> ('var,'d) conf 
    \<Rightarrow> ('vert,'var,'d) pre_RedBlack 
    \<Rightarrow> bool"
where
  "abstract_extends prb rv c\<^sub>a prb' \<equiv> 
     rv \<in> red_vertices prb
   \<and> \<not> marked prb rv  
   \<and> out_edges (red prb) rv = {} 
   \<and> rv \<notin> subsumees (subs prb)
   \<and> abstract (confs prb rv) c\<^sub>a
   \<and> c\<^sub>a \<Turnstile>\<^sub>c (strengthenings prb rv)
   \<and> finite (pred c\<^sub>a)
   \<and> (\<forall> e \<in> pred c\<^sub>a. finite (vars e))
   \<and> prb' =  \<lparr> red       = red prb, 
               black     = black prb, 
               subs      = subs prb, 
               init_conf = init_conf prb,
               confs     = (confs prb)(rv := c\<^sub>a),
               marked    = marked prb,
               strengthenings = strengthenings prb,
               \<dots>        = more prb \<rparr>"
      

subsubsection \<open>Extension by strengthening\<close>

text \<open>This operation consists in labeling a red vertex with a safeguard condition. It does not 
actually change the red part, but model the mechanism of preventing too crude abstractions.\<close>

abbreviation strengthen_extends ::
  "('vert,'var,'d) pre_RedBlack 
   \<Rightarrow> ('vert \<times> nat) 
   \<Rightarrow> ('var,'d) bexp 
   \<Rightarrow> ('vert,'var,'d) pre_RedBlack 
   \<Rightarrow> bool"
where
  "strengthen_extends prb rv e prb' \<equiv>  
     rv \<in> red_vertices prb
   \<and> rv \<notin> subsumees (subs prb)
   \<and> confs prb rv \<Turnstile>\<^sub>c e
   \<and> prb' =  \<lparr> red       = red prb, 
               black     = black prb, 
               subs      = subs prb, 
               init_conf = init_conf prb,
               confs     = confs prb,
               marked    = marked prb,
               strengthenings = (strengthenings prb)(rv := (\<lambda> \<sigma>. (strengthenings prb rv) \<sigma> \<and> e \<sigma>)),
               \<dots>        = more prb \<rparr>"



subsection \<open>Building Red-Black Graphs using Extensions\<close>


text\<open>Red-black graphs are pre-red-black graphs built with the following inductive relation, i.e.\ 
using only the five previous pre-red-black graphs transformation operators, starting from an 
empty red part.\<close>

inductive RedBlack ::
  "('vert,'var,'d) pre_RedBlack \<Rightarrow> bool"
where
  base : 
    "fst (root (red prb)) = init (black prb)      \<Longrightarrow>
     edges (red prb) = {}                         \<Longrightarrow>
     subs prb = {}                                \<Longrightarrow>
     (confs prb) (root (red prb)) = init_conf prb \<Longrightarrow>
     marked prb = (\<lambda> rv. False)                   \<Longrightarrow> 
     strengthenings prb = (\<lambda> rv. (\<lambda> \<sigma>. True))     \<Longrightarrow> RedBlack prb"

| se_step : 
    "RedBlack prb                                 \<Longrightarrow>
     se_extends prb re p' prb'                    \<Longrightarrow> RedBlack prb'"

| mark_step : 
    "RedBlack prb                                 \<Longrightarrow>
     mark_extends prb rv prb'                     \<Longrightarrow> RedBlack prb'"
                                                 
| subsum_step :                                  
    "RedBlack prb                                 \<Longrightarrow>
     subsum_extends prb sub prb'                  \<Longrightarrow> RedBlack prb'"
                                                 
| abstract_step :                                
    "RedBlack prb                                 \<Longrightarrow> 
     abstract_extends prb rv c\<^sub>a prb'             \<Longrightarrow> RedBlack prb'"

| strengthen_step :
    "RedBlack prb                                 \<Longrightarrow> 
     strengthen_extends prb rv e prb'             \<Longrightarrow> RedBlack prb'"


subsection \<open>Properties of Red-Black-Graphs\<close>

subsubsection\<open>Invariants of the Red\hyp{}Black Graphs\<close>


text\<open>The red part of a red-black graph is loop free.\<close>

lemma
  assumes "RedBlack prb"
  shows   "loop_free (red prb)"
using assms by (induct prb) auto


text\<open>A red edge can not lead to the (red) root.\<close>


lemma 
  assumes "RedBlack prb"
  assumes "re \<in> edges (red prb)"
  shows   "tgt re \<noteq> root (red prb)"
using assms by (induct prb) (auto simp add : vertices_def)


text\<open>Red edges are specific versions of black edges.\<close>

lemma ui_re_is_be :
  assumes "RedBlack prb"
  assumes "re \<in> edges (red prb)"
  shows   "ui_edge re \<in> edges (black prb)"
using assms by (induct rule : RedBlack.induct) auto


text\<open>The set of out-going edges from a red vertex is a subset of the set of out-going edges from 
the black location it represents.\<close>

lemma red_OA_subset_black_OA :
  assumes "RedBlack prb"
  shows   "ui_edge ` out_edges (red prb) rv \<subseteq> out_edges (black prb) (fst rv)"
using assms by (induct prb) (fastforce simp add : vertices_def)+


text \<open>The red root is an indexed version of the black initial location.\<close>

lemma consistent_roots :
  assumes "RedBlack prb"
  shows   "fst (root (red prb)) = init (black prb)"
using assms by (induct prb) auto



text\<open>The red part of a red-black graph is a tree.\<close>

lemma 
  assumes "RedBlack prb"
  shows   "is_tree (red prb)"
using assms 
by (induct prb) (auto simp add : empty_graph_is_tree ArcExt.extends_is_tree)

 
text \<open>A red-black graph whose black part is well-formed is also well-formed.\<close>

lemma
  assumes "RedBlack prb"
  assumes "wf_lts (black prb)"
  shows   "wf_pre_RedBlack prb"
proof -
  have "wf_rgraph (red prb)"
       using assms by (induct prb) (force simp add : vertices_def)+

  thus ?thesis 
       using assms consistent_roots ui_re_is_be 
       by (auto simp add : wf_pre_RedBlack_def)
qed


text \<open>Red locations of a red-black graph are indexed versions of its black locations.\<close>

lemma ui_rv_is_bv :
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "fst rv \<in> Graph.vertices (black prb)"
using assms consistent_roots ui_re_is_be 
by (auto simp add : vertices_def image_def Bex_def) fastforce+



text \<open>The subsumption of a red-black graph is a sub-relation of its red part.\<close>

lemma subs_sub_rel_of :
  assumes "RedBlack prb"
  shows   "sub_rel_of (red prb) (subs prb)"
using assms unfolding sub_rel_of_def
proof (induct prb)
  case base thus ?case by simp
next
  case se_step thus ?case by (elim conjE) (auto simp add : vertices_def)
next 
  case mark_step thus ?case by auto
next
  case subsum_step thus ?case by auto
next
  case abstract_step thus ?case by simp
next
  case strengthen_step thus ?case by simp
qed



text\<open>The subsumption relation of red-black graph is well-formed.\<close>

lemma subs_wf_sub_rel :
  assumes "RedBlack prb"
  shows   "wf_sub_rel (subs prb)"
using assms
proof (induct prb)
  case base thus ?case by (simp add : wf_sub_rel_def)
next
  case se_step thus ?case by force
next
  case mark_step thus ?case by (auto simp add : wf_sub_rel_def)
next
  case subsum_step thus ?case by (auto simp add : wf_sub_rel.extends_imp_wf_sub_rel)
next
  case abstract_step thus ?case by simp
next
  case strengthen_step thus ?case by simp
qed


text \<open>Using the two previous lemmas, we have that the subsumption relation of a red-black graph 
is a well-formed sub-relation of its red-part.\<close>

lemma subs_wf_sub_rel_of :
  assumes "RedBlack prb"
  shows   "wf_sub_rel_of (red prb) (subs prb)"
using assms subs_sub_rel_of subs_wf_sub_rel by (simp add : wf_sub_rel_of_def) fast


text\<open>Subsumptions only involve red locations representing the same black location.\<close>

lemma subs_to_same_BL :
  assumes "RedBlack prb"
  assumes "sub \<in> subs prb"
  shows   "fst (subsumee sub) = fst (subsumer sub)"
using assms subs_wf_sub_rel unfolding wf_sub_rel_def by fast


text\<open>If a red edge sequence @{term "res"} is consistent between red locations @{term "rv1"} and 
@{term "rv2"} with respect to the subsumption relation of a red-black graph, then its unindexed 
version is consistent between the black locations represented by @{term "rv1"} and @{term "rv2"}.\<close>

lemma rces_imp_bces :
  assumes "RedBlack prb"
  assumes "SubRel.ces rv1 res rv2 (subs prb)"                        
  shows   "Graph.ces (fst rv1) (ui_es res) (fst rv2)"
using assms
proof (induct res arbitrary : rv1)
  case (Nil rv1) thus ?case 
  using wf_sub_rel.in_trancl_imp[OF subs_wf_sub_rel] subs_to_same_BL
  by fastforce
next
  case (Cons re res rv1)

  hence 1 : "rv1 = src re \<or> (rv1, src re) \<in> (subs prb)\<^sup>+"
  and   2 : "ces (tgt re) res rv2 (subs prb)" by simp_all

  have "src (ui_edge re) = fst rv1"
        using 1  wf_sub_rel.in_trancl_imp[OF subs_wf_sub_rel[OF assms(1)], of rv1 "src re"]
              subs_to_same_BL[OF assms(1), of "(rv1,src re)"]
       by auto
  
  moreover 
  have "Graph.ces (tgt (ui_edge re)) (ui_es res) (fst rv2)" 
       using assms(1) Cons(1) 2 by simp

  ultimately
  show ?case by simp
qed


text\<open>The unindexed version of a subpath in the red part of a red-black graph is a subpath in its 
black part. This is an important fact: in the end, it helps proving that set of paths we consider 
in red-black graphs are paths of the original LTS. Thus, the same states are computed along 
these paths.\<close>

theorem red_sp_imp_black_sp :
  assumes "RedBlack prb"
  assumes "subpath (red prb) rv1 res rv2 (subs prb)"
  shows   "Graph.subpath (black prb) (fst rv1) (ui_es res) (fst rv2)"
using assms rces_imp_bces ui_rv_is_bv ui_re_is_be
unfolding subpath_def Graph.subpath_def by (intro conjI) (fast, fast, fastforce)


text\<open>Any constraint in the path predicate of a configuration associated to a red location of a 
red-black graph contains a finite number of variables.\<close>

lemma finite_pred_constr_symvars :
  assumes "RedBlack prb"
  assumes "finite_RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "\<forall> e \<in> pred (confs prb rv). finite (Bexp.vars e)"
using assms
proof (induct prb arbitrary : rv)
  case base thus ?case by (simp add : vertices_def finite_RedBlack_def)
next
  case (se_step prb re c' prb') 

  hence "rv \<in> red_vertices prb \<or> rv = tgt re" by (auto simp add : vertices_def)
  
  thus ?case 
  proof (elim disjE)
    assume "rv \<in> red_vertices prb"

    moreover
    have "finite_RedBlack prb" 
         using se_step(3,4) by (auto simp add : finite_RedBlack_def)

    ultimately
    show ?thesis 
         using se_step(2,3) by (elim conjE) (auto simp add : vertices_def)
  next
    assume "rv = tgt re"

    moreover
    have "finite_label (labelling (black prb) (ui_edge re))"
         using se_step by (auto simp add : finite_RedBlack_def)

    moreover
    have "\<forall> e \<in> pred (confs prb (src re)). finite (Bexp.vars e)"
           using se_step se_step(2)[of "src re"] unfolding finite_RedBlack_def 
    by (elim conjE) auto

    moreover
    have "se (confs prb (src re)) (labelling (black prb) (ui_edge re)) c'"
          using se_step by auto

    ultimately
    show ?thesis using se_step se_preserves_finiteness1 by fastforce
  qed
next
  case mark_step thus ?case by (simp add : finite_RedBlack_def)
next
  case subsum_step thus ?case by (simp add : finite_RedBlack_def)
next
  case abstract_step thus ?case by (auto simp add : finite_RedBlack_def)
next
  case strengthen_step thus ?case by (simp add : finite_RedBlack_def)
qed


text \<open>The path predicate of a configuration associated to a red location of a 
red-black graph contains a finite number of constraints.\<close>

lemma finite_pred :
  assumes "RedBlack prb"
  assumes "finite_RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "finite (pred (confs prb rv))"
using assms
proof (induct prb arbitrary : rv)
  case base thus ?case by (simp add : vertices_def finite_RedBlack_def)
next
  case (se_step prb re c' prb')

  hence "rv \<in> red_vertices prb \<or> rv = tgt re" 
        by (auto simp add : vertices_def)

  thus ?case 
  proof (elim disjE, goal_cases)
    case 1 thus ?thesis 
         using se_step(2)[of rv] se_step(3,4) 
         by (auto simp add : finite_RedBlack_def)
  next
    case 2
    moreover
    hence "src re \<in> red_vertices prb"
    and   "finite (pred (confs prb (src re)))" 
          using se_step(2)[of "src re"] se_step(3,4) 
          by (auto simp add : finite_RedBlack_def)
  
    ultimately
    show ?thesis
         using se_step(3) se_preserves_finiteness2 by auto
  qed
next
  case mark_step thus ?case by (simp add : finite_RedBlack_def)
next
  case subsum_step thus ?case by (simp add : finite_RedBlack_def)
next
  case abstract_step thus ?case by (simp add : finite_RedBlack_def)
next
  case strengthen_step thus ?case by (simp add : finite_RedBlack_def)
qed


text\<open>Hence, for a red location @{term "rv"} of a red-black graph and any label @{term "l"}, 
there exists a configuration that can be obtained by symbolic execution of @{term "l"} from the 
configuration associated to @{term "rv"}.\<close>

lemma (in finite_RedBlack) ex_se_succ :
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "\<exists> c'. se (confs prb rv) l c'"
using finite_RedBlack assms 
      finite_imp_ex_se_succ[of "confs prb rv"]
      finite_pred[of prb rv ]
      finite_pred_constr_symvars[of prb rv]
unfolding finite_RedBlack_def by fast



text\<open>Generalization of the previous lemma to a list of labels.\<close>

lemma (in finite_RedBlack) ex_se_star_succ :
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  assumes "finite_labels ls"
  shows   "\<exists> c'. se_star (confs prb rv) ls c'"
using finite_RedBlack assms 
      finite_imp_ex_se_star_succ[of "confs prb rv" ls]
      finite_pred[OF assms(1), of rv] 
      finite_pred_constr_symvars[OF assms(1), of rv]
unfolding finite_RedBlack_def by simp


text\<open>Hence, for any red sub-path, there exists a configuration that can be obtained by symbolic 
execution of its trace from the configuration associated to its source.\<close>

lemma (in finite_RedBlack) sp_imp_ex_se_star_succ :
  assumes "RedBlack prb"
  assumes "subpath (red prb) rv1 res rv2 (subs prb)"
  shows   "\<exists> c. se_star 
                  (confs prb rv1) 
                  (trace (ui_es res) (labelling (black prb))) 
                  c"
using finite_RedBlack assms ex_se_star_succ 
by (simp add : subpath_def finite_RedBlack_def)


text\<open>The configuration associated to a red location @{term "rl"} is update-able.\<close>

lemma (in finite_RedBlack)
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "updatable (confs prb rv)"
using finite_RedBlack assms 
      finite_conj[OF finite_pred[OF assms(1)] 
                     finite_pred_constr_symvars[OF assms(1)]]
      finite_pred_imp_se_updatable
unfolding finite_RedBlack_def by fast


text\<open>The configuration associated to the first member of a subsumption is subsumed by the 
configuration at its second member.\<close>

lemma sub_subsumed :
  assumes "RedBlack prb"
  assumes "sub \<in> subs prb"
  shows   "confs prb (subsumee sub) \<sqsubseteq> confs prb (subsumer sub)"
using assms
proof (induct prb)
  case base thus ?case by simp 
next
  case (se_step prb re c' prb')

  moreover
  hence "sub \<in> subs prb" by auto

  hence "subsumee sub \<in> red_vertices prb" 
  and   "subsumer sub \<in> red_vertices prb"
        using se_step(1) subs_sub_rel_of 
        unfolding sub_rel_of_def by fast+

  moreover
  have "tgt re \<notin> red_vertices prb" using se_step by auto

  ultimately
  show ?case by auto
next
  case mark_step thus ?case by simp
next
  case (subsum_step prb sub prb') thus ?case by auto
next
  case (abstract_step prb rv c\<^sub>a prb')

  hence "rv \<noteq> subsumee sub" by auto

  show ?case 
  proof (case_tac "rv = subsumer sub")
    assume "rv = subsumer sub"

    moreover
    hence  "confs prb (subsumer sub) \<sqsubseteq> confs prb' (subsumer sub)" 
           using abstract_step abstract_def by auto
  
    ultimately
    show ?thesis 
         using abstract_step
               subsums_trans[of "confs prb  (subsumee sub)" 
                                "confs prb  (subsumer sub)" 
                                "confs prb' (subsumer sub)"]
         by (simp add : subsums_refl)
  next
    assume "rv \<noteq> subsumer sub" thus ?thesis using abstract_step \<open>rv \<noteq> subsumee sub\<close> by simp
  qed
next
  case strengthen_step thus ?case by simp
qed

subsubsection\<open>Simplification lemmas for sub-paths of the red part.\<close>

lemma rb_Nil_sp :
  assumes "RedBlack prb"
  shows   "subpath (red prb) rv1 [] rv2 (subs prb) = 
           (rv1 \<in> red_vertices prb \<and> (rv1 = rv2 \<or> (rv1,rv2) \<in> (subs prb)))"
using assms subs_wf_sub_rel subs_sub_rel_of wf_sub_rel.Nil_sp by fast


lemma rb_sp_one :
  assumes "RedBlack prb"
  shows "subpath (red prb) rv1 [re] rv2 (subs prb) = 
         ( sub_rel_of (red prb) (subs prb)
         \<and> (rv1 = src re \<or> (rv1, src re) \<in> (subs prb)) 
         \<and> re \<in> edges (red prb) \<and> (tgt re = rv2 \<or> (tgt re, rv2) \<in> (subs prb)))"
using assms subs_wf_sub_rel_of wf_sub_rel_of.sp_one by fast


lemma rb_sp_Cons :
  assumes "RedBlack prb"
  shows   "subpath (red prb) rv1 (re # res) rv2 (subs prb) =
            ( sub_rel_of (red prb) (subs prb)
            \<and> (rv1 = src re \<or> (rv1, src re) \<in> subs prb) 
            \<and> re \<in> edges (red prb)                       
            \<and> subpath (red prb) (tgt re) res rv2 (subs prb))"
using assms subs_wf_sub_rel_of wf_sub_rel_of.sp_Cons by fast


lemma rb_sp_append_one :
  assumes "RedBlack prb"
  shows   "subpath (red prb) rv1 (res @ [re]) rv2 (subs prb) =
            ( subpath (red prb) rv1 res (src re) (subs prb) 
            \<and> re \<in> edges (red prb) 
            \<and> (tgt re = rv2 \<or> (tgt re, rv2) \<in> subs prb))"
using assms subs_wf_sub_rel wf_sub_rel.sp_append_one sp_append_one by fast


subsection \<open>Relation between red-vertices\<close>

text\<open>The following key-theorem describes the relation between two red locations that are linked by 
a red sub-path. In a classical symbolic execution tree, the configuration at the end should be the 
result of symbolic execution of the trace of the sub-path from the configuration at its source. 
Here, due to the facts that abstractions might have occurred and that we consider sub-paths going 
through subsumption links, the configuration at the end subsumes the configuration one would obtain 
by symbolic execution of the trace. Note however that this is only true for configurations computed 
during the analysis: concrete execution of the sub-paths would yield the same program states 
than their counterparts in the original LTS.\<close> 

thm RedBlack.induct[of x P]

theorem (in finite_RedBlack) SE_rel :
  assumes "RedBlack prb"
  assumes "subpath (red prb) rv1 res rv2 (subs prb)"
  assumes "se_star (confs prb rv1) (trace (ui_es res) (labelling (black prb))) c"
  shows   "c \<sqsubseteq> (confs prb rv2)"
using assms finite_RedBlack
proof (induct arbitrary : rv1 res rv2 c rule : RedBlack.induct) 
  (* If the red part is empty, then @{term "rv1 = rv2 = root (red prb)"}, and 
     @{term "confs prb rv1 = confs prb rv2"} which prooves the goal, subsumption 
     being reflexive. *) 
  case (base prb rv1 res rv2 c) thus ?case 
       by (force simp add : subpath_def Nil_sp subsums_refl)

next
  (* We split the goal into four cases :
     - rv1 and rv2 are vertices of the old red part,
     - rv1 is a vertex in the old red part, rv2 is the target of ra,
     - rv1 is the target of ra, rv2 is a vertex of the old red part,
     - rv1 are rv2 both equal to the target of ra. *)
  case (se_step prb re c' prb' rv1 res rv2 c)

       have "rv1 \<in> red_vertices prb'"
       and  "rv2 \<in> red_vertices prb'"
            using fst_of_sp_is_vert[OF se_step(4)]
                  lst_of_sp_is_vert[OF se_step(4)]
            by simp_all
           
       hence "rv1 \<in> red_vertices prb \<and> rv1 \<noteq> tgt re \<or> rv1 = tgt re"
       and   "rv2 \<in> red_vertices prb \<and> rv2 \<noteq> tgt re \<or> rv2 = tgt re"
             using se_step by (auto simp add : vertices_def)                             

  thus ?case
  proof (elim disjE conjE, goal_cases)
    (* rv1 are rv2 vertices of the old red part *)
    case 1

    (* hence res is also a subpath from rv1 to rv2 in the old red part *)
    moreover
    hence "subpath (red prb) rv1 res rv2 (subs prb)"
          using se_step(1,3,4)
                sub_rel_of.sp_from_old_verts_imp_sp_in_old 
                [OF subs_sub_rel_of, of prb re "red prb'" rv1 rv2 res]
          by auto

    (* thus, the IH can be used to conclude. *)
    ultimately
    show ?thesis using se_step 
         by (fastforce simp add : finite_RedBlack_def)

  next 
    (* rv1 is a vertex of the old red part, rv2 is the target of ra. *)
    case 2 

    (* hence res is empty or ra occurs only one time in res : at its end. *)
    hence  "\<exists> res'. res = res' @ [re]
                    \<and> re \<notin> set res'
                    \<and> subpath (red prb) rv1 res' (src re) (subs prb)"
           using se_step 
                 sub_rel_of.sp_to_new_edge_tgt_imp[OF subs_sub_rel_of, of prb re "red prb'" rv1 res]
           by auto 

    thus ?thesis
    proof (elim exE conjE)
      (* If res = res'@[ra], then there exists a configuration c' such that :
         - c' is obtained from (confs prb rv1) by symbolic execution of (the trace of) res,
         - c' is subsumed by (confs prb (src ra)) (by IH),
         - c is obtained from c' by symbolic execution of (the label of) ra.

         Moreover, we have :
         - (confs prb rv2) is obtained from (confs prb (src ra) by symbolic execution 
           of (the label of) ra.

         Ultimately, we proof the goal by monotonicity of symbolic execution wrt subsumption. *)  
      fix res'

      assume "res = res' @ [re]"
      and    "re \<notin> set res'"
      and    "subpath (red prb) rv1 res' (src re) (subs prb)"

      moreover
      then obtain c'
      where "se_star (confs prb rv1) (trace (ui_es res') (labelling (black prb))) c'"
      and   "se c' (labelling (black prb) (ui_edge re)) c"
            using se_step 2 se_star_append_one by auto blast
        
      ultimately
      have "c' \<sqsubseteq> (confs prb (src re))" using se_step by fastforce

      thus ?thesis 
           using se_step \<open>rv1 \<noteq> tgt re\<close> 2 
                 \<open>se c' (labelling (black prb) (ui_edge re)) c\<close>
           by (auto simp add : se_mono_for_sub)
    qed
  next
    (* rv1 is the target of ra. Hence res is empty and rv2 also equals (tgt ra), 
       which contradicts our hypothesis. *) 
    case 3 

    moreover
    have "rv1 = rv2"
    proof -      
      have  "(rv1,rv2) \<in> (subs prb')"
      using se_step 3 
            sub_rel_of.sp_from_tgt_in_extends_is_Nil
                [OF subs_sub_rel_of[OF se_step(1)], of re "red prb'" res rv2]
            rb_Nil_sp[OF RedBlack.se_step[OF se_step(1,3)], of rv1 rv2] 
      by auto

      hence "rv1 \<in> subsumees (subs prb)" using se_step(3) by force

      thus ?thesis 
           using se_step \<open>rv1 = tgt re\<close> subs_sub_rel_of[OF se_step(1)] 
           by (auto simp add  : sub_rel_of_def)
    qed

    ultimately
    show ?thesis by simp
  next
    (* Finally, if rv1 and rv2 both equal (tgt ra), then we conclude using the fact that 
       the subsumption is reflexive. *)
    case 4

    moreover
    hence "res = []"
          using se_step 
                sub_rel_of.sp_from_tgt_in_extends_is_Nil 
                    [OF subs_sub_rel_of[OF se_step(1)], of re "red prb'" res rv2]
          by auto

    ultimately
    show ?thesis using se_step by (simp add : subsums_refl)
  qed

next
  (* Marking a red vertex does not affect the configurations associated to red vertices,
     hence this case is trivial when observing that a subpath after marking is a subpath 
     before marking (which allows to apply the IH). *)
  case (mark_step prb rv prb') thus ?case by simp

next
  case (subsum_step prb sub prb' rv1 res rv2 c)

  (* The fact that prb' is also red-black will be needed several times in the following. *)
  have RB' : "RedBlack prb'" by (rule RedBlack.subsum_step[OF subsum_step(1,3)])

  (* First, we suppose that res starts at the newly subsumed red vertex. *)
  show ?case 
  proof (case_tac "rv1 = subsumee sub")

   (* In this case, res is either empty, or a subpath starting at the subsumer of the new 
       subsumption. *)

    assume "rv1 = subsumee sub"

    hence "res = [] \<or> subpath (red prb') (subsumer sub) res rv2 (subs prb')"
          using subsum_step(3,4) 
                wf_sub_rel_of.sp_in_extends_imp1 [ OF subs_wf_sub_rel_of[OF subsum_step(1)], 
                                                   of "subsumee sub" "subsumer sub" ]
          by simp

    thus ?thesis
    proof (elim disjE)
      (* If res is empty, then rv1 equals rv2 or (rv1,rv2) is in the new subsumption relation. *)
      assume "res = []"

      hence  "rv1 = rv2 \<or> (rv1,rv2) \<in> (subs prb')" 
             using subsum_step rb_Nil_sp[OF RB'] by fast

      thus ?thesis 
      proof (elim disjE)
        (* If rv1 = rv2, "their" configurations are also equal. Moreover, res being empty, c is the 
           configuration at rv1. We conclude using reflexivity of subsumption. *)
        assume "rv1 = rv2" 
        thus ?thesis 
             using subsum_step(5) \<open>res = []\<close> 
             by (simp add : subsums_refl)
      next
        (* If (rv1, rv2) is in the new subsumption relation, then the configuration at rv1 is 
           subsumed by the configuration at rv2. We conclude using the fact c is the configuration 
           at rv1. *) 
        assume "(rv1, rv2) \<in> (subs prb')" 
        thus ?thesis 
             using subsum_step(5) \<open>res = []\<close> 
                   sub_subsumed[OF RB', of "(rv1,rv2)"] 
             by simp
      qed
      
    next
      (* If res is also a subpath from the subsumer of the new subsumption, we show the goal 
         by (backward) induction on res *)
      assume "subpath (red prb') (subsumer sub) res rv2 (subs prb')"

      thus ?thesis 
      using subsum_step(5)
      proof (induct res arbitrary : rv2 c rule : rev_induct, goal_cases)
        (* If the red subpath is empty, then (rv1,rv2) is the new subsumption, which gives the goal 
           by definition of subsum_extends. *)
        case (1 rv2 c)

        have "rv2 = subsumer sub" 
        proof -
          have "(subsumer sub,rv2) \<notin> subs prb'"
          proof (intro notI)
            assume "(subsumer sub,rv2) \<in> subs prb'"

            hence "subsumer sub \<in> subsumees (subs prb')" by force

            moreover
            have  "subsumer sub \<in> subsumers (subs prb')" 
                  using subsum_step(3) by force

            ultimately
            show False 
                 using subs_wf_sub_rel[OF RB'] 
                 unfolding wf_sub_rel_def 
                 by auto
          qed

          thus ?thesis using 1(1) rb_Nil_sp[OF RB'] by auto
        qed

        thus ?case 
        using subsum_step(3) 1(2) \<open>rv1 = subsumee sub\<close> by simp

      next
        (* Inductive case : the red subpath has the form res@[ra]. *)
        case (2 re res rv2 c)

        (* We call :
           - c' the configuration obtained by symbolic execution of res from the configuration at 
             rv1,
           - c'' the configuration obtained by symbolic execution of ra from the configuration at 
             the source of ra.

           We show that c' is subsumed by the configuration at the source of ra (using "internal" 
           IH), hence c is subsumed by c'', by monotonicity of symbolic execution for subsumption.
           
           Moreover, we show that c'' is subsumed by the configuration at the target of ra, 
           using the fact that [ra] is subpath from the source of ra to its target in the old 
           red part with the "external" IH. 

           Finally, we show that the configuration at the target of ra is subsumed by the 
           configuration at rv2 by observing that the target of ra is either rv2, either subsumed 
           by rv2. 
           
           We conclude using transitivity of subsumption.  *)

        hence A : "subpath (red prb') (subsumer sub) res (src re) (subs prb')"
        and   B : "subpath (red prb') (src re) [re] (tgt re) (subs prb')"
        using subs_sub_rel_of[OF RB'] by (auto simp add : sp_append_one sp_one)

        obtain c' 
        where C : "se_star (confs prb' rv1) (trace (ui_es res) (labelling (black prb'))) c'"
        and   D : "se c' (labelling (black prb') (ui_edge re)) c"
        using 2 by (simp add : se_star_append_one) blast

        obtain c''
        where E : "se (confs prb' (src re)) (labelling (black prb') (ui_edge re)) c''"
        using subsum_step(6-8)
              \<open>subpath (red prb') (src re) [re] (tgt re) (subs prb')\<close>
              RB' finite_RedBlack.ex_se_succ[of prb' "src re"]
        unfolding finite_RedBlack_def
        by (simp add : se_star_one fst_of_sp_is_vert) blast        

        have "c \<sqsubseteq> c''"
        proof -
          have "c' \<sqsubseteq> confs prb' (src re)" using 2(1) A B C D by fast
          thus ?thesis using D E se_mono_for_sub by fast
        qed

        moreover
        have "c'' \<sqsubseteq> confs prb' (tgt re)" 
        proof -
          have "subpath (red prb) (src re) [re] (tgt re) (subs prb)"
          proof -
            have "src re \<in> red_vertices prb'"
            and  "tgt re \<in> red_vertices prb'" 
            and  "re \<in> edges (red prb')"
            using B by (auto simp add : vertices_def sp_one)

            hence "src re \<in> red_vertices prb"
            and   "tgt re \<in> red_vertices prb"
            and   "re \<in> edges (red prb)"
                  using subsum_step(3) by auto

            thus ?thesis 
                 using subs_sub_rel_of[OF subsum_step(1)] 
                 by (simp add : sp_one)
          qed

          thus ?thesis 
               using subsum_step(2,3,6-8) E 
               by (simp add : se_star_one)
        qed

        moreover
        have "confs prb' (tgt re) \<sqsubseteq> confs prb' rv2"
        proof -
          have "tgt re = rv2 \<or> (tgt re,rv2) \<in> subs prb'" 
               using 2(2) rb_sp_append_one[OF RB'] by auto

          thus ?thesis 
          proof (elim disjE)
            assume "tgt re = rv2" 
            thus ?thesis by (simp add : subsums_refl)
          next
            assume "(tgt re, rv2) \<in> (subs prb')" 
            thus ?thesis using sub_subsumed RB' by fastforce
          qed
        qed
              
        ultimately
        show ?case using subsums_trans subsums_trans by fast
      qed
    qed

  next
  
    (* If res does not start at the newly subsumed red vertex, then either res is a subpath in 
       the old red part, either it can be splitted into two parts res1 and res2 such that :
       - res1 is a subpath in the old red part from rv1 to the newly subsumed vertex, 
       - res2 is a subpath in the new red part from the newly subsumed vertex to rv2. *)

    assume "rv1 \<noteq> subsumee sub"

    hence  "subpath (red prb) rv1 res rv2 (subs prb) \<or> 
            (\<exists> res1 res2. res = res1 @ res2 
                        \<and> res1 \<noteq> [] 
                        \<and> subpath (red prb) rv1 res1 (subsumee sub) (subs prb) 
                        \<and> subpath (red prb') (subsumee sub) res2 rv2 (subs prb'))"
           using subsum_step(3,4) 
                 wf_sub_rel_of.sp_in_extends_imp2  [OF subs_wf_sub_rel_of[OF subsum_step(1)], 
                                                    of "subsumee sub" "subsumer sub"]
           by auto
    
    thus ?thesis
    proof (elim disjE exE conjE)
      (* In the first case, we conclude by "external" IH. *)
      assume "subpath (red prb) rv1 res rv2 (subs prb)" 
      thus ?thesis using subsum_step by simp

    next
      (* We call :
         - c1 the configuration obtained from the configuration at rv1 by symbolic execution 
           of res1 and such that c is obtained from c1 by symbolic execution of res2,
         - c2 the configuration obtained from the configuration at the newly subsumed red vertex 
           by symbolic execution of res2.

         We show that c is subsumed by c2 and that c2 is subsumed by the configuration at rv2.
         We conclude by transitivity of subsumption. *)
      fix res1 res2
       
      define t_res1 where "t_res1 = trace (ui_es res1) (labelling (black prb'))"
      define t_res2 where "t_res2 = trace (ui_es res2) (labelling (black prb'))"
      
      assume "res = res1 @ res2"
      and    "res1 \<noteq> []"
      and    "subpath (red prb) rv1 res1 (subsumee sub) (subs prb)"
      and    "subpath (red prb') (subsumee sub) res2 rv2 (subs prb')"
      
      then obtain c1 c2
      where "se_star (confs prb' rv1) t_res1 c1"
      and   "se_star c1 t_res2 c"
      and   "se_star (confs prb' (subsumee sub)) t_res2 c2"
            using subsum_step(1,3,5,6-8) RB'
                  finite_RedBlack.ex_se_star_succ[of prb rv1 t_res1]
                  finite_RedBlack.ex_se_star_succ[of prb' "subsumee sub" t_res2]
            unfolding finite_RedBlack_def t_res1_def t_res2_def
            by (simp  add : fst_of_sp_is_vert  se_star_append) blast

      then have "c \<sqsubseteq> c2"
      proof -
        have "c1 \<sqsubseteq> confs prb' (subsumee sub)" 
             using subsum_step(2,3,6-8) 
                   \<open>subpath (red prb) rv1 res1 (subsumee sub) (subs prb)\<close>
                   \<open>se_star (confs prb' rv1) t_res1 c1\<close>
             by (auto simp add : t_res1_def t_res2_def)
        
        thus ?thesis
             using \<open>se_star c1 t_res2 c\<close> 
                   \<open>se_star (confs prb' (subsumee sub)) t_res2 c2\<close>
                   se_star_mono_for_sub
             by fast
      qed

      moreover
      (* Here we have to proceed by beckward induction on res2. *)
      have "c2 \<sqsubseteq> confs prb' rv2"
           using \<open>subpath (red prb') (subsumee sub) res2 rv2 (subs prb')\<close>
                 \<open>se_star (confs prb' (subsumee sub)) t_res2 c2\<close>
           unfolding t_res2_def
           proof (induct res2 arbitrary : rv2 c2 rule : rev_induct, goal_cases)
           (* If the suffix is empty, then either subsumee sub equals rv2, either 
              (subsumee sub,rv2) is in the new subsumption relation. *)
        case (1 rv2 c2) 

           hence "subsumee sub = rv2 \<or> (subsumee sub, rv2)\<in>subs prb'" 
           using rb_Nil_sp[OF RB'] by simp

        thus ?case 
        proof (elim disjE)
          (* In the first case, we have : 
               c = confs prb' (subsumee sub) = confs prb' rv2.
             We conclude by reflexivity of the subsumption. *)
          assume "subsumee sub = rv2" 
          thus ?thesis 
               using 1(2) by (simp add : subsums_refl)
        next
          (* In the second case, we have : 
               c = confs prb' (subsumee sub) \<sqsubseteq> confs prb' rv2, 
             qed.  *)
          assume "(subsumee sub, rv2) \<in> subs prb'" 
          thus ?thesis 
                using 1(2) 
                sub_subsumed[OF RB', of "(subsumee sub, rv2)"] 
                by simp
        qed

      next 
        (* Inductive case : the suffix has the form res2@[ra]. *)
        case (2 re res2 rv2 c2)

        (* We call : 
           - c3 the configuration obtained from the configuration at the newly subsumed red 
             vertex. c2 is obtained from c3 by symbolic execution of ra,
           - c4 the configuration obtained from the configuration at the source of ra by 
             symbolic execution of ra.

           By internal IH, we first show that c3 is subsumed by the configuration at the source of 
           ra. Thus c2 is subsumed by c4, by monotonicity of symbolic execution for the 
           subsumption. 

           Then we show that c4 is subsumed by the configuration at the target of ra, using the 
           external IH.

           Finally, we show that the configuration at the target of ra is subsumed by the 
           configuration at rv2, by observing that either tgt ra = rv2, either (tgt ra,rv2) 
           is in the new subsumption relation. 

           We conclude by transitivity of the subsumption relation. *)

        have A : "subpath (red prb') (subsumee sub) res2 (src re) (subs prb')"
        and  B : "subpath (red prb') (src re) [re] rv2 (subs prb')"
                 using 2(2) subs_wf_sub_rel[OF RB'] subs_wf_sub_rel_of[OF RB']
                 by (simp_all only: wf_sub_rel.sp_append_one)
                    (simp add : wf_sub_rel_of.sp_one wf_sub_rel_of_def)

        obtain c3
        where C : "se_star (confs prb' (subsumee sub)) 
                           (trace (ui_es res2) (labelling (black prb'))) 
                           (c3)"
        and   D : "se c3 (labelling (black prb') (ui_edge re)) c2"
                  using 2(3) subsum_step(6-8) RB' 
                        finite_RedBlack.ex_se_succ[of prb' "src re"]
                  by (simp add : se_star_append_one) blast

        obtain c4 
        where E : "se (confs prb' (src re)) (labelling (black prb') (ui_edge re)) c4"
                  using subsum_step(6-8) RB' B 
                        finite_RedBlack.ex_se_succ[of prb' "src re"]
                  unfolding finite_RedBlack_def
                  by (simp  add : fst_of_sp_is_vert se_star_append) blast

        have "c2 \<sqsubseteq> c4" 
        proof -
          have "c3 \<sqsubseteq> confs prb' (src re)" using 2(1) A C by fast

          thus ?thesis using D E se_mono_for_sub by fast
        qed
        
        moreover
        have "c4 \<sqsubseteq> confs prb' (tgt re)"
        proof -
          have "subpath (red prb) (src re) [re] (tgt re) (subs prb)"
          proof -
            have "src re \<in> red_vertices prb'"
            and  "tgt re \<in> red_vertices prb'" 
            and  "re \<in> edges (red prb')"
            using B by (auto simp add : vertices_def sp_one)

            hence "src re \<in> red_vertices prb"
            and   "tgt re \<in> red_vertices prb"
            and   "re \<in> edges (red prb)"
            using subsum_step(3) by auto

            thus ?thesis 
                 using subs_sub_rel_of[OF subsum_step(1)] 
                 by (simp add : sp_one)
          qed

          thus  ?thesis 
                using subsum_step(2,3,6-8) E 
                by (simp add : se_star_one)
        qed

        moreover
        have "confs prb' (tgt re) \<sqsubseteq> confs prb' rv2"
        proof -
          have "tgt re = rv2 \<or> (tgt re, rv2) \<in> (subs prb')"
               using subsum_step 2 rb_sp_append_one[OF RB', of "subsumee sub" res2 re]
               by (auto simp add : vertices_def subpath_def)

          thus ?thesis 
          proof (elim disjE)
            assume "tgt re = rv2" 
            thus ?thesis by (simp add : subsums_refl)
          next
            assume "(tgt re, rv2) \<in> (subs prb')" 
            thus ?thesis 
                 using sub_subsumed RB' 
                 by fastforce
          qed
        qed

        ultimately
        show ?case using subsums_trans subsums_trans by fast
      qed

      ultimately
      show ?thesis by (rule subsums_trans)
    qed
  qed

next
  case (abstract_step prb rv c\<^sub>a prb' rv1 res rv2 c) 

  show ?case
  proof (case_tac "rv1 = rv", goal_cases) 
    (* We first suppose that rv1 is the red vertex where the abstraction took place. In this case, 
       we have that res is empty and rv2 = rv1. Hence c is the configuration at rv2 (after 
       abstraction). We conclude using reflexivity of subsumption. *)
    case 1

    moreover
    hence "res = []" 
          using abstract_step
                sp_from_de_empty[of rv1 "subs prb" "red prb" res rv2]
          by simp

    moreover
    have  "rv2 = rv" 
    proof -
      have "rv1 = rv2 \<or> (rv1, rv2) \<in> (subs prb)"
           using abstract_step \<open>res = []\<close> 
                 rb_Nil_sp[OF RedBlack.abstract_step[OF abstract_step(1,3)]]
           by simp 

      moreover
      have "(rv1, rv2) \<notin> (subs prb)"
           using abstract_step 1 
           unfolding Ball_def subsumees_conv
           by (intro notI) blast
      
      ultimately
      show ?thesis using 1 by simp
    qed

    ultimately
    show ?thesis using abstract_step(5) by (simp add : subsums_refl)
  next
    (* Suppose that rv1 is not the red vertex where the subsumption took place. *) 
    case 2

    show ?thesis
    proof (case_tac "rv2 = rv")
      (* We first suppose that rv2 is the newly abstracted red vertex. Then we have that the new 
         configuration at rv2 subsums the old configuration at this red vertex. We conclude 
         by use of IH and transitivity of subsumption. *)
      assume "rv2 = rv"

      hence  "confs prb rv2 \<sqsubseteq> confs prb' rv2" 
             using abstract_step by (simp add : abstract_def)

      moreover
      have   "c \<sqsubseteq> confs prb rv2" 
             using abstract_step 2 by auto

      ultimately
      show ?thesis using subsums_trans by fast
    next
      assume "rv2 \<noteq> rv" thus ?thesis using abstract_step 2 by simp 
    qed
  qed

next
  (* Strengthening a red vertex does not affect the red part, thus this case is trivial. *)
  case strengthen_step thus ?case by simp
qed









subsection\<open>Properties about marking.\<close>

text \<open>A configuration which is indeed satisfiable can not be marked.\<close>

lemma sat_not_marked :
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  assumes "sat (confs prb rv)"
  shows   "\<not> marked prb rv"
using assms
proof (induct prb arbitrary : rv)
  case base thus ?case by simp
next
  case (se_step prb re c prb')

  hence "rv \<in> red_vertices prb \<or> rv = tgt re" by (auto simp add : vertices_def)

  thus ?case
  proof (elim disjE, goal_cases)
    case 1 
    moreover
    hence "rv \<noteq> tgt re" using se_step(3) by (auto simp add : vertices_def)
    ultimately
    show ?thesis using se_step by (elim conjE) auto
  next
    case 2

    moreover
    hence "sat (confs prb (src re))" using se_step(3,5) se_sat_imp_sat by auto
    
    ultimately
    show ?thesis using se_step(2,3) by (elim conjE) auto
  qed
next
  case (mark_step prb rv' prb') 

  moreover
  hence "rv \<noteq> rv'" and "(rv,rv') \<notin> subs prb"
        using sub_subsumed[OF mark_step(1), of "(rv,rv')"] unsat_subs_unsat by auto
  
  ultimately
  show ?case by auto
next
  case subsum_step thus ?case by auto

next
  case (abstract_step prb rv' c\<^sub>a prb') thus ?case by (case_tac "rv' = rv") simp+

next
  case strengthen_step thus ?case by simp
qed


text\<open>On the other hand, a red-location which is marked unsat is indeed logically unsatisfiable.\<close>

lemma
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  assumes "marked prb rv"
  shows   "\<not> sat (confs prb rv)"
using assms
proof (induct prb arbitrary : rv)
  case base thus ?case by simp
next
  case (se_step prb re c prb')

  hence "rv \<in> red_vertices prb \<or> rv = tgt re" by (auto simp add : vertices_def)

  thus ?case 
  proof (elim disjE, goal_cases)
    case 1

    moreover
    hence "rv \<noteq> tgt re" using se_step(3) by auto
    hence "marked prb rv" using se_step by auto

    ultimately
    have "\<not> sat (confs prb rv)" by (rule se_step(2))

    thus ?thesis using se_step(3) \<open>rv \<noteq> tgt re\<close> by auto
  next
    case 2

    moreover
    hence "marked prb (src re)" using se_step(3,5) by auto

    ultimately
    have "\<not> sat (confs prb (src re))" using se_step(2,3) by auto

    thus ?thesis using se_step(3) \<open>rv = tgt re\<close> unsat_imp_se_unsat by (elim conjE) auto
  qed
next
  case (mark_step prb rv' prb') thus ?case by (case_tac "rv' = rv") auto
next
  case subsum_step thus ?case by simp

next
  case (abstract_step _ rv' _) thus ?case by (case_tac "rv' = rv") simp+

next
  case strengthen_step thus ?case by simp
qed




text\<open>Red vertices involved in subsumptions are not marked.\<close>


lemma subsumee_not_marked :
  assumes "RedBlack prb"
  assumes "sub \<in> subs prb"
  shows   "\<not> marked prb (subsumee sub)"
using assms
proof (induct prb)
  case base thus ?case by simp
next
  case (se_step prb re c prb')
  
  moreover
  hence "subsumee sub \<noteq> tgt re"
  using subs_wf_sub_rel_of[OF se_step(1)]
  by (elim conjE, auto simp add : wf_sub_rel_of_def sub_rel_of_def)

  ultimately
  show ?case by auto
next
  case mark_step thus ?case by auto
next
  case subsum_step thus ?case by auto

next
  case abstract_step thus ?case by auto

next
  case strengthen_step thus ?case by simp
qed


lemma subsumer_not_marked :
  assumes "RedBlack prb"
  assumes "sub \<in> subs prb"
  shows   "\<not> marked prb (subsumer sub)"
using assms
proof (induct prb)
  case base thus ?case by simp
next
  case (se_step prb re c prb')

  moreover
  hence "subsumer sub \<noteq> tgt re"
  using subs_wf_sub_rel_of[OF se_step(1)]
  by (elim conjE, auto simp add : wf_sub_rel_of_def sub_rel_of_def)

  ultimately
  show ?case by auto
next
  case (mark_step prb rv prb') thus ?case by auto
next
  case (subsum_step prb sub' prb') thus ?case by auto

next
  case abstract_step thus ?case by simp

next
  case strengthen_step thus ?case by simp
qed



text\<open>If the target of a red edge is not marked, then its source is also not marked.\<close>

lemma tgt_not_marked_imp :
  assumes "RedBlack prb"
  assumes "re \<in> edges (red prb)"
  assumes "\<not> marked prb (tgt re)"
  shows   "\<not> marked prb (src re)"
using assms
proof (induct prb arbitrary : re)
  case base thus ?case by simp
next
  case se_step thus ?case by (force simp add : vertices_def image_def)
next
  case (mark_step prb rv prb' re) thus ?case by (case_tac "tgt re = rv") auto
next
  case subsum_step thus ?case by simp

next
  case abstract_step thus ?case by simp

next
  case strengthen_step thus ?case by simp
qed

text\<open>Given a red subpath leading from red location @{term "rv1"} to red location @{term "rv2"},
if @{term "rv2"} is not marked, then @{term "rv1"} is also not marked (this
lemma is not used).\<close>

lemma
  assumes "RedBlack prb"
  assumes "subpath (red prb) rv1 res rv2 (subs prb)"
  assumes "\<not> marked prb rv2"
  shows   "\<not> marked prb rv1"
using assms
proof (induct res arbitrary : rv1)
  case Nil 
  
  hence "rv1 = rv2 \<or> (rv1,rv2) \<in> subs prb" by (simp add : rb_Nil_sp)
  
  thus ?case 
  proof (elim disjE, goal_cases)
    case 1 thus ?case using Nil by simp
  next
    case 2 show ?case using Nil subsumee_not_marked[OF Nil(1) 2] by simp
  qed
next
  case (Cons re res)  
  
  thus ?case 
  unfolding rb_sp_Cons[OF Cons(2), of rv1 re res rv2]
  proof (elim conjE disjE, goal_cases)
    case 1

    moreover
    hence "\<not> marked prb (tgt re)" by simp

    moreover
    have "re \<in> edges (red prb)" using Cons(3) rb_sp_Cons[OF Cons(2), of rv1 re res rv2] by fast
    
    ultimately
    show ?thesis using tgt_not_marked_imp[OF Cons(2)] by fast
  next
    case 2 thus ?thesis using subsumee_not_marked[OF Cons(2)] by fastforce
  qed
qed


subsection\<open>Fringe of a red-black graph\<close>

text \<open>We have stated and proved a number of properties of red-black graphs. In the end, we are 
mainly interested in proving that the set of paths of such red-black graphs are subsets of the set 
of feasible paths of their black part. Before defining the set of paths of red-black graphs, we 
first introduce the intermediate concept of \emph{fringe} of the red part. Intuitively, the fringe 
is the set of red vertices from which we can approximate more precisely the set of feasible paths of 
the black part. This includes red vertices that have not been subsumed yet, that are not marked and 
from which some black edges have not been yet symbolically executed (i.e.\ that have no red 
counterpart from these red vertices).\<close>

subsubsection \<open>Definition\<close>

text\<open>The fringe is the set of red locations from which there exist black edges that have not 
been followed yet.\<close>

definition fringe :: 
  "('vert, 'var, 'd, 'x) pre_RedBlack_scheme \<Rightarrow> ('vert \<times> nat) set"
where
  "fringe prb \<equiv> {rv \<in> red_vertices prb. 
                   rv \<notin> subsumees (subs prb) \<and> 
                   \<not> marked prb rv           \<and>
                   ui_edge ` out_edges (red prb) rv \<subset> out_edges (black prb) (fst rv)}"


subsubsection \<open>Fringe of an empty red-part\<close>

text\<open>At the beginning of the analysis, i.e.\ when the red part is empty, the fringe consists of the 
red root.\<close>

lemma fringe_of_empty_red1 :
  assumes "edges (red prb) = {}"
  assumes "subs prb = {}"
  assumes "marked prb = (\<lambda> rv. False)"
  assumes "out_edges (black prb) (fst (root (red prb))) \<noteq> {}"
  shows   "fringe prb = {root (red prb)}"
using assms by (auto simp add : fringe_def vertices_def)


subsubsection \<open>Evolution of the fringe after extension\<close>

text\<open>Simplification lemmas for the fringe of the new red-black graph after adding an edge by 
symbolic execution. If the configuration from which symbolic execution is performed is not marked 
yet, and if there exists black edges going out of the target of the executed edge, the target of 
the new red edge enters the fringe. Moreover, if there still exist black edges that have no red 
counterpart yet at the source of the new edge, then its source was and stays in the fringe.\<close>

lemma seE_fringe1 :
  assumes "sub_rel_of (red prb) (subs prb)"
  assumes "se_extends prb re c' prb'"
  assumes "\<not> marked prb (src re)"
  assumes "ui_edge ` (out_edges (red prb') (src re)) \<subset> out_edges (black prb) (fst (src re))"
  assumes "out_edges (black prb) (fst (tgt re)) \<noteq> {}"
  shows   "fringe prb' = fringe prb \<union> {tgt re}"
unfolding set_eq_iff Un_iff singleton_iff
proof (intro allI iffI, goal_cases)
  case (1 rv)

  moreover
  hence "rv \<in> red_vertices prb \<or> rv = tgt re"
  using assms(2) by (auto simp add : fringe_def vertices_def) 

  ultimately
  show ?case using assms(2) by (auto simp add : fringe_def)
next 
  case (2 rv)

  hence  "rv \<in> red_vertices prb'" using assms(2) by (auto simp add : fringe_def vertices_def)

  moreover
  have "rv \<notin> subsumees (subs prb')"
  using 2
  proof (elim disjE)
    assume "rv \<in> fringe prb" thus ?thesis using assms(2) by (auto simp add : fringe_def)
  next
    assume "rv = tgt re" thus ?thesis 
    using assms(1,2) unfolding sub_rel_of_def by force
  qed

  moreover
  have "ui_edge ` (out_edges (red prb') rv) \<subset> out_edges (black prb') (fst rv)"
  using 2
  proof (elim disjE)
    assume "rv \<in> fringe prb" 
    
    thus ?thesis 
    proof (case_tac "rv = src re")
      assume "rv = src re" thus ?thesis using assms(2,4) by auto
    next
      assume "rv \<noteq> src re" thus ?thesis 
      using assms(2) \<open>rv \<in> fringe prb\<close>
      by (auto simp add : fringe_def)
    qed
  next
    assume "rv = tgt re" thus ?thesis 
    using assms(2,5) extends_tgt_out_edges[of re "red prb" "red prb'"] by (elim conjE) auto
  qed

  moreover
  have "\<not> marked prb' rv" 
  using 2
  proof (elim disjE, goal_cases)
    case 1 

    moreover
    hence "rv \<noteq> tgt re" using assms(2) by (auto simp add : fringe_def)

    ultimately
    show ?thesis using assms(2) by (auto simp add : fringe_def)
  next
    case 2 thus ?thesis using assms(2,3) by auto
  qed

  ultimately
  show ?case by (simp add : fringe_def)
qed

text \<open>On the other hand, if all possible black edges have been executed from the source of the new 
edge after the extension, then the source is removed from the fringe.\<close>

lemma  seE_fringe4 :
  assumes "sub_rel_of (red prb) (subs prb)"
  assumes "se_extends prb re c' prb'"
  assumes "\<not> marked prb (src re)"
  assumes "\<not> (ui_edge ` (out_edges (red prb') (src re)) \<subset> out_edges (black prb) (fst (src re)))"
  assumes "out_edges (black prb) (fst (tgt re)) \<noteq> {}"
  shows   "fringe prb' = fringe prb - {src re} \<union> {tgt re}"
unfolding set_eq_iff Un_iff singleton_iff Diff_iff
proof (intro allI iffI, goal_cases)
  case (1 rv)

  hence "rv \<in> red_vertices prb \<or> rv = tgt re" 
  and   "rv \<noteq> src re" 
  using assms(2,3,4,5) by (auto simp add : fringe_def vertices_def) 

  with 1 show ?case using assms(2) by (auto simp add : fringe_def)

next
  case (2 rv)

  hence  "rv \<in> red_vertices prb'" using assms(2) by (auto simp add : fringe_def vertices_def)

  moreover
  have "rv \<notin> subsumees (subs prb')"
  using 2
  proof (elim disjE)
    assume "rv \<in> fringe prb \<and> rv \<noteq> src re" 
    thus ?thesis using assms(2) by (auto simp add : fringe_def)
  next
    assume "rv = tgt re" thus ?thesis 
    using assms(1,2) unfolding sub_rel_of_def by fastforce
  qed

  moreover
  have "ui_edge ` (out_edges (red prb') rv) \<subset> out_edges (black prb') (fst rv)"
  using 2
  proof (elim disjE)
    assume "rv \<in> fringe prb \<and> rv \<noteq> src re" thus ?thesis 
    using assms(2) by (auto simp add : fringe_def)
  next
    assume "rv = tgt re" thus ?thesis 
    using assms(2,5) extends_tgt_out_edges[of re "red prb" "red prb'"] by (elim conjE) auto
  qed

  moreover
  have "\<not> marked prb' rv"
  using 2
  proof (elim disjE, goal_cases)
    case 1 

    moreover
    hence "rv \<noteq> tgt re" using assms by (auto simp add : fringe_def)

    ultimately
    show ?thesis
    using assms 1 by (auto simp add : fringe_def)
  next
    case 2 thus ?thesis using assms by auto
  qed

  ultimately
  show ?case by (simp add : fringe_def)
qed

text \<open>If the source of the new edge is marked, then its target does not enter the fringe (and the 
source was not part of it in the first place).\<close>

lemma seE_fringe2 :
  assumes "se_extends prb re c prb'"
  assumes "marked prb (src re)"
  shows   "fringe prb' = fringe prb"
unfolding set_eq_iff Un_iff singleton_iff
proof (intro allI iffI, goal_cases)
  case (1 rv)

  thus ?case 
  unfolding fringe_def mem_Collect_eq
  using assms
  proof (intro conjI, goal_cases)
    case 1 thus ?case by (auto simp add : fringe_def vertices_def)
  next
    case 2 thus ?case by auto
  next
    case 3 

    moreover
    hence "rv \<noteq> tgt re" by auto

    ultimately
    show ?case by auto
  next
    case 4 thus ?case by auto
  qed
next
  case (2 rv)

  thus ?case unfolding fringe_def mem_Collect_eq
  using assms
  proof (intro conjI, goal_cases)
    case 1 thus ?case by (auto simp add : vertices_def)
  next
    case 2 thus ?case by auto
  next
    case 3 
    moreover
    hence "rv \<noteq> tgt re" by auto
    ultimately
    show ?case by auto
  next
    case 4 thus ?case by auto
  qed
qed

text \<open>If there exists no black edges going out of the target of the new edge, then this target 
does not enter the fringe.\<close>

lemma seE_fringe3 :
  assumes "se_extends prb re c' prb'"
  assumes "ui_edge ` (out_edges (red prb') (src re)) \<subset> out_edges (black prb) (fst (src re))"
  assumes "out_edges (black prb) (fst (tgt re)) = {}"
  shows   "fringe prb' = fringe prb"
unfolding set_eq_iff Un_iff singleton_iff
proof (intro allI iffI, goal_cases)
  case (1 rv)

  thus ?case using assms(1,3)
  unfolding fringe_def mem_Collect_eq
  proof (intro conjI, goal_cases)
    case 1 thus ?case by (auto simp add : fringe_def vertices_def) 
  next
    case 2 thus ?case by (auto simp add : fringe_def)
  next
    case 3 thus ?case by (case_tac "rv = tgt re") (auto simp add : fringe_def)
  next
    case 4 thus ?case by (auto simp add : fringe_def)
  qed

next 
  case (2 rv)

  moreover
  hence "rv \<in> red_vertices prb'"
  and   "rv \<noteq> tgt re" 
  using assms(1) by (auto simp add : fringe_def vertices_def)

  moreover
  have "ui_edge ` (out_edges (red prb') rv) \<subset> out_edges (black prb) (fst rv)"
  proof (case_tac "rv = src re")
    assume "rv = src re" thus ?thesis using assms(2) by simp
  next
    assume "rv \<noteq> src re" 
    thus ?thesis using assms(1) 2
    by (auto simp add : fringe_def)
  qed

  ultimately
  show ?case using assms(1) by (auto simp add : fringe_def)
qed


text \<open>Moreover, if all possible black edges have been executed from the source of the new edge 
after the extension, then this source is removed from the fringe.\<close>

lemma seE_fringe5 :
  assumes "se_extends prb re c' prb'"
  assumes "\<not> (ui_edge ` (out_edges (red prb') (src re)) \<subset> out_edges (black prb) (fst (src re)))"
  assumes "out_edges (black prb) (fst (tgt re)) = {}"
  shows   "fringe prb' = fringe prb - {src re}"
unfolding set_eq_iff Un_iff singleton_iff Diff_iff
proof (intro allI iffI, goal_cases)
  case (1 rv)

  moreover
  have "rv \<in> red_vertices prb" and "rv \<noteq> src re"
  using 1 assms by (auto simp add : fringe_def vertices_def)  (* slow *)

  moreover
  have "\<not> marked prb rv"
  proof (intro notI)
    assume "marked prb rv"

    have "marked prb' rv"
    proof -
      have "rv \<noteq> tgt re" using assms(1) \<open>rv \<in> red_vertices prb\<close> by auto
      
      thus ?thesis using assms(1) \<open>marked prb rv\<close> by auto
    qed
  
    thus False using 1 by (auto simp add : fringe_def)
  qed

  ultimately
  show ?case using assms(1) by (auto simp add : fringe_def)

next
  case (2 rv)

  hence  "rv \<in> red_vertices prb'" using assms(1) by (auto simp add : fringe_def vertices_def)

  moreover
  have "rv \<notin> subsumees (subs prb')" using 2 assms(1) by (auto simp add : fringe_def)

  moreover
  have "ui_edge ` (out_edges (red prb') rv) \<subset> out_edges (black prb') (fst rv)"
  using 2 assms(1) by (auto simp add : fringe_def)

  moreover
  have "\<not> marked prb' rv"
  proof -
    have "rv \<noteq> tgt re" using assms(1) 2 by (auto simp add : fringe_def)
    
    thus ?thesis using assms(1) 2 by (auto simp add : fringe_def)
  qed

  ultimately
  show ?case by (simp add : fringe_def)
qed


text\<open>Adding a subsumption to the subsumption relation removes the first member of the 
subsumption from the fringe.\<close>

lemma subsumE_fringe :
  assumes "subsum_extends prb sub prb'"
  shows   "fringe prb' = fringe prb - {subsumee sub}"
using assms by (auto simp add : fringe_def)



subsection\<open>Red-Black Sub-Paths and Paths\<close>

text\<open>The set of red-black subpaths starting in red location @{term "rv"} is the union of :
\begin{itemize}
  \item the set of black sub-paths that have a red counterpart starting at @{term "rv"} and leading 
to a non-marked red location,
  \item the set of black sub-paths that have a prefix represented in the red part starting 
at @{term "rv"} and leading to an element of the fringe. Moreover, the remainings of these black 
sub-paths must have no non-empty counterpart in the red part. Otherwise, the set of red-black paths 
would simply be the set of paths of the black part.
\end{itemize}
\<close>

definition RedBlack_subpaths_from ::
  "('vert, 'var, 'd, 'x) pre_RedBlack_scheme \<Rightarrow> ('vert \<times> nat) \<Rightarrow> 'vert edge list set"
where
  "RedBlack_subpaths_from prb rv \<equiv> 
     ui_es ` {res. \<exists> rv'. subpath (red prb) rv res rv' (subs prb) \<and> \<not> marked prb rv'}
   \<union> {ui_es res1 @ bes2 
      | res1 bes2. \<exists> rv1. rv1 \<in> fringe prb 
                        \<and> subpath (red prb) rv res1 rv1 (subs prb)
                        \<and> \<not> (\<exists> res21 bes22. bes2 = ui_es res21 @ bes22 
                                              \<and> res21 \<noteq> [] 
                                              \<and> subpath_from (red prb) rv1 res21 (subs prb))
                        \<and> Graph.subpath_from (black prb) (fst rv1) bes2}"



text\<open>Red-black paths are red-black subpaths starting at the root of the red part.\<close>

abbreviation RedBlack_paths :: 
  "('vert, 'var, 'd, 'x) pre_RedBlack_scheme \<Rightarrow> 'vert edge list set"
where 
  "RedBlack_paths prb \<equiv> RedBlack_subpaths_from prb (root (red prb))"


text\<open>When the red part is empty, the set of red-black subpaths starting at the red root is the set 
of black paths.\<close>

lemma (in finite_RedBlack) base_RedBlack_paths :
  assumes "fst (root (red prb)) = init (black prb)"
  assumes "edges (red prb) = {}"
  assumes "subs prb = {}"
  assumes "confs prb (root (red prb)) = init_conf prb"
  assumes "marked prb = (\<lambda> rv. False)"
  assumes "strengthenings prb = (\<lambda> rv. (\<lambda> \<sigma>. True))"
  
  shows   "RedBlack_paths prb = Graph.paths (black prb)"

proof -
  show ?thesis
  unfolding set_eq_iff
  proof (intro allI iffI)

     fix    bes   
     assume "bes \<in> RedBlack_subpaths_from prb (root (red prb))"   
     thus   "bes \<in> Graph.paths (black prb)" 
     unfolding  RedBlack_subpaths_from_def Un_iff
     proof (elim disjE exE conjE, goal_cases)
       case 1
       
       hence "bes = []" using assms by (auto simp add: subpath_def)
       
       thus ?thesis 
       by (auto simp add : Graph.subpath_def vertices_def)
     next
       case 2
   
       then obtain res1 bes2 rv where "bes = ui_es res1 @ bes2"
                                and   "rv \<in> fringe prb"
                                and   "subpath (red prb) (root (red prb)) res1 rv (subs prb)"
                                and   "Graph.subpath_from (black prb) (fst rv) bes2"
                   by blast
    
       moreover
       hence "res1 = []" using assms by (simp add : subpath_def)
   
       ultimately
       show ?thesis using assms \<open>rv \<in> fringe prb\<close> by (simp add : fringe_def vertices_def)
     qed
  next
    fix bes
    assume "bes \<in> Graph.paths (black prb)"
    show "bes \<in> RedBlack_subpaths_from prb (root (red prb))" 
    proof (case_tac "out_edges (black prb) (init (black prb)) = {}")
       assume "out_edges (black prb) (init (black prb)) = {}"
       show ?thesis
            unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
            apply (intro disjI1)
            apply (rule_tac ?x="[]" in exI)
            apply (intro conjI)
             apply (rule_tac ?x="root (red prb)" in exI)
             proof (intro conjI)
               show "subpath (red prb) (root (red prb)) [] (root (red prb)) (subs prb)" 
               using assms(3) by (simp add : sub_rel_of_def subpath_def vertices_def)
             next
               show "\<not> marked prb (root (red prb))" using assms(5) by simp
             next
               show "bes = ui_es []" 
               using \<open>bes \<in> Graph.paths (black prb)\<close> 
                     \<open>out_edges (black prb) (init (black prb)) = {}\<close>
               by (cases bes) (auto simp add : Graph.sp_Cons)
             qed
            next
              assume "out_edges (black prb) (init (black prb)) \<noteq> {}"
              show ?thesis
                 unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                 proof (intro disjI2, rule_tac ?x="[]" in exI, rule_tac ?x="bes" in exI, 
                        intro conjI, goal_cases)
                    case 1 show ?case by simp
                 next
                    case 2 show ?case
                         unfolding Bex_def
                         proof (rule_tac ?x="root (red prb)" in exI, intro conjI, goal_cases)          
                             show "root (red prb) \<in> fringe prb"
                                 using assms(1-3,5) \<open>out_edges (black prb) (init (black prb)) \<noteq> {}\<close> 
                                 fringe_of_empty_red1 
                                 by fastforce
                         next
                             show "subpath (red prb)(root (red prb))([])(root (red prb))(subs prb)"
                                using subs_sub_rel_of[OF RedBlack.base[OF assms(1-6)]]
                                by (simp add : subpath_def vertices_def sub_rel_of_def)
                         next 
                             case 3 show ?case
                                proof (intro notI, elim exE conjE)
                                   fix res21 bes22 rv
                                   assume "bes = ui_es res21 @ bes22"
                                   and    "res21 \<noteq> []" 
                                   and    "subpath (red prb) (root (red prb)) res21 rv (subs prb)"
                                   moreover
                                   hence "res21 = []" using assms by (simp add : subpath_def)
                                   ultimately  show False by (elim notE)
                                qed
                        next
                             case 4 show ?case 
                                using assms \<open>bes \<in> Graph.paths (black prb)\<close> by simp
                        qed
                 qed
            qed     
  qed
qed












text \<open>Red-black sub-paths and paths are sub-paths and paths of the black part.\<close>

lemma RedBlack_subpaths_are_black_subpaths :
  assumes "RedBlack prb"
  shows   "RedBlack_subpaths_from prb rv \<subseteq> Graph.subpaths_from (black prb) (fst rv)"
unfolding subset_iff mem_Collect_eq RedBlack_subpaths_from_def Un_iff image_def Bex_def
proof (intro allI impI, elim disjE exE conjE, goal_cases)
  case (1 bes res rv') thus ?case using assms red_sp_imp_black_sp by blast
next
  case (2 bes res1 bes2 rv1 bv2) thus ?case 
  using red_sp_imp_black_sp[OF assms, of rv  res1 rv1]
  by (rule_tac ?x="bv2" in exI) (auto simp add : Graph.sp_append)
qed

lemma RedBlack_paths_are_black_paths : 
  assumes "RedBlack prb"
  shows   "RedBlack_paths prb \<subseteq> Graph.paths (black prb)"
using assms 
      RedBlack_subpaths_are_black_subpaths[of prb "root (red prb)"]
      consistent_roots[of prb]
by simp




subsection \<open>Preservation of feasible paths\<close>


text\<open>The following theorem states that we do not loose feasible paths using
our five operators,
and moreover, configurations @{term "c"} at the end of feasible red paths in
some graph @{term "prb"} will have corresponding feasible red paths in
successors that
lead to configurations that subsume @{term "c"}. As a corollary, our calculus is correct
wrt. to execution.\<close>



theorem (in finite_RedBlack) feasible_subpaths_preserved :
  assumes "RedBlack prb"
  assumes "rv \<in> red_vertices prb"
  shows   "feasible_subpaths_from (black prb) (confs prb rv) (fst rv) 
           \<subseteq> RedBlack_subpaths_from prb rv"
using assms finite_RedBlack
proof (induct prb arbitrary : rv)

  (* Base case : the red part is empty. In this case, rl is the root of the red part. Hence, the 
     set of feasible subpaths starting at (fst rl) is the set of feasible paths of the black part.
     We conclude using the fact that when the red part is empty, the set of red-black subpaths is 
     the set of paths of the black part, which includes feasible paths. *)

  case (base prb rv) 

  moreover
  hence "rv = root (red prb)" by (simp add : vertices_def)

  moreover
  hence "feasible_subpaths_from (black prb) (confs prb rv) (fst rv) 
         = feasible_paths (black prb) (confs prb (root (red prb)))"
        using base by simp

  moreover
  have "out_edges (black prb) (fst (root (red prb))) = {} \<or>
        ui_edge `out_edges(red prb)(root (red prb)) \<subset> out_edges(black prb)(fst (root (red prb)))"
        using base by auto

  ultimately
  show ?case 
        using finite_RedBlack.base_RedBlack_paths[of prb]
        by (auto simp only : finite_RedBlack_def)

next

  (* Adding an edge by symbolic execution. *)
    
  case (se_step prb re c prb' rv)

  have RB' : "RedBlack prb'" by (rule RedBlack.se_step[OF se_step(1,3)])

  show ?case
  unfolding subset_iff
  proof (intro allI impI)
    
    fix bes 

    assume "bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)"

    have "rv \<in> red_vertices prb \<or> rv = tgt re" 
         using se_step(3,4) by (auto simp add : vertices_def)

    thus "bes \<in> RedBlack_subpaths_from prb' rv" 
    proof (elim disjE)
      (* We first suppose that bes does not start at the target of the new edge. In this case, we 
         can use the IH to show that bes is a red-black subpath in the old red-black graph. We then 
         proceed by case distinction. *)
      assume "rv \<in> red_vertices prb"

      moreover
      hence  "rv \<noteq> tgt re" using se_step by auto

      ultimately
      have  "bes \<in> RedBlack_subpaths_from prb rv"
            using se_step \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
            by fastforce

      thus ?thesis 
        apply (subst (asm) RedBlack_subpaths_from_def)
        unfolding Un_iff image_def Bex_def mem_Collect_eq
        proof (elim disjE exE conjE)
          (* Suppose that bes is entirely represented in the old red part. Then it is also entirely 
             represented in the new red part, qed. *)
          fix res rv'
        
          assume "bes = ui_es res"
          and    "subpath (red prb) rv res rv' (subs prb)"
          and    "\<not> marked prb rv'"
        
          moreover
          hence "\<not> marked prb' rv'" 
          using se_step(3) lst_of_sp_is_vert[of "red prb" rv res rv' "subs prb"]
          by (elim conjE) auto
        
          ultimately
          show ?thesis 
          using se_step(3) sp_in_extends_w_subs[of re "red prb" "red prb'" rv res rv' "subs prb"]
          unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
          by (intro disjI1, rule_tac ?x="res" in exI, intro conjI) 
             (rule_tac ?x="rv'" in exI, auto)
        
        next
          (* Suppose that bes is not entirely represented in the old red part, ie bes is of the form 
             ui_es res1 @ bes2 where res1 is a (maximal) red subpath (leading to a non-marked element 
             rv1 of the old fringe) and bes2 is black subpath (starting at the black vertex 
             represented by rv1. We then proceed by distinguishing the cases where the rv1 is the 
             source of the new edge or is an "old" red vertex. *)
          fix res1 bes2 rv1 bl
        
          assume A : "bes = ui_es res1 @ bes2"
          and    B : "rv1 \<in> fringe prb"
          and    C : "subpath (red prb) rv res1 rv1 (subs prb)"
          (*and    D : "\<not> marked prb rv1"*)
          and    E : "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                 \<and>  res21 \<noteq> [] 
                                 \<and> subpath_from (red prb) rv1 res21 (subs prb))"
          and    F : "Graph.subpath (black prb) (fst rv1) bes2 bl"
        
          hence "rv1 \<noteq> tgt re" using se_step by (auto simp add : fringe_def)
        
          show ?thesis 
          proof (case_tac "rv1 = src re")
            (* If rv1 is the source of the new edge, we proceed by cases on the black suffix. *)
            assume "rv1 = src re"
            
            show ?thesis 
            proof (case_tac "bes2 = []")
              (* If the black suffix is empty, then bes is in fact entirely represented in the old 
                 red part and also in the new red part, qed. *)
              assume "bes2 = []" 
              
              show ?thesis 
              unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
              apply (intro disjI1)
              apply (rule_tac ?x="res1" in exI)
              apply (intro conjI)
               apply (rule_tac ?x="rv1" in exI)
                apply (intro conjI)
                proof -
                  show "subpath (red prb') rv res1 rv1 (subs prb')" 
                  using se_step(3) C by (auto simp add : sp_in_extends_w_subs)
                next
                  have "rv1 \<noteq> tgt re" using se_step(3) \<open>rv1 = src re\<close> by auto
                  thus "\<not> marked prb' rv1" using se_step(3) B by (auto simp add : fringe_def)
                next
                  show "bes = ui_es res1" using A \<open>bes2 = []\<close> by simp
                qed
        
            next
              (* If the black suffix is not empty, we first suppose that its first edge is the new 
                 edge. *)
              assume "bes2 \<noteq> []"              
              then obtain be bes2' where "bes2 = be # bes2'" unfolding neq_Nil_conv by blast        
              show ?thesis 
              proof (case_tac "be = ui_edge re")
                (* If the first edge of the black suffix is represented by the new edge, then 
                   res1@[ra] is a red subpath leading to the target of the new edge, which is the 
                   fringe and not marked. Moreover, it is maximal, as there are no out-going edges 
                   from the target of the new edge in the new red part yet. Moreover, the tail of 
                   the black suffix is a suitable "new" black suffix, qed. *)
                assume "be = ui_edge re" 
        
                show ?thesis 
                proof (case_tac "out_edges (black prb) (fst (tgt re)) = {}")
        
                  assume "out_edges (black prb) (fst (tgt re)) = {}"        
                  show ?thesis

                    unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
                    apply (intro disjI1)
                    apply (rule_tac ?x="res1@[re]" in exI)
                    apply (intro conjI)
                     apply (rule_tac ?x="tgt re" in exI)
                     proof (intro conjI)
                       show "subpath (red prb') rv (res1 @ [re]) (tgt re) (subs prb')"
                       using se_step(3) \<open>rv1 = src re\<close> C
                             sp_in_extends_w_subs[of re "red prb" "red prb'" rv res1 rv1 "subs prb"]
                             rb_sp_append_one[OF RB', of rv res1 re "tgt re"]
                       by auto
                     next
                       show "\<not> marked prb' (tgt re)" 
                       using se_step(3) \<open>rv1 = src re\<close> B 
                       by (auto simp add : fringe_def)
                     next
                       have "bes2' = []"
                       using F \<open>bes2 = be # bes2'\<close> 
                             \<open>be = ui_edge re\<close> \<open>out_edges (black prb) (fst (tgt re)) = {}\<close>
                       by (cases bes2') (auto simp add:  Graph.sp_Cons)
                       
                       thus "bes = ui_es (res1 @ [re])"
                       using \<open>bes = ui_es res1 @ bes2\<close> \<open>bes2 = be # bes2'\<close> \<open>be = ui_edge re\<close> by simp
                     qed
        
                next
        
                  assume "out_edges (black prb) (fst (tgt re)) \<noteq> {}"                    
                  show ?thesis

                  unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                  apply (intro disjI2)
                  apply (rule_tac ?x="res1@[re]" in exI)
                  apply (rule_tac ?x="bes2'"     in exI)
                  proof (intro conjI, goal_cases)
                    show "bes = ui_es (res1 @ [re]) @ bes2'"
                    using \<open>bes = ui_es res1 @ bes2\<close> \<open>bes2 = be # bes2'\<close> \<open>be = ui_edge re\<close> 
                    by simp
                  next
                    case 2 show ?case 
                    proof (rule_tac ?x="tgt re" in exI, intro conjI)
                      have "\<not> marked prb (src re)" 
                           using B \<open>rv1 = src re\<close> by (simp add : fringe_def)        
                      thus "tgt re \<in> fringe prb'" 
                         using se_step(3) \<open>out_edges (black prb) (fst (tgt re)) \<noteq> {}\<close> 
                               seE_fringe1[OF subs_sub_rel_of[OF se_step(1)] se_step(3)] 
                               seE_fringe4[OF subs_sub_rel_of[OF se_step(1)] se_step(3)] 
                         by auto
                    next
                      show "subpath (red prb') rv (res1 @ [re]) (tgt re) (subs prb')" 
                         using se_step(3) \<open>rv1 = src re\<close> C
                               sp_in_extends_w_subs[of re "red prb" "red prb'" 
                                                       rv res1 rv1 "subs prb"]
                               rb_sp_append_one[OF RB', of rv res1 re "tgt re"]
                         by auto
                    next
                      show "\<not> (\<exists>res21 bes22. bes2' = ui_es res21 @ bes22 
                                           \<and> res21 \<noteq> [] 
                                           \<and> subpath_from (red prb') (tgt re) res21 (subs prb'))"
                      proof (intro notI, elim exE conjE)
                        fix res21 bes22 rv2
                        assume "bes2' = ui_es res21 @ bes22"
                        and    "res21 \<noteq> []"
                        and    "subpath (red prb') (tgt re) res21 rv2 (subs prb')"    
                        thus False 
                             using se_step(3) 
                                   sub_rel_of.sp_from_tgt_in_extends_is_Nil
                                   [OF subs_sub_rel_of[OF se_step(1)], of re "red prb'" res21 rv2]
                             by auto
                      qed
                    next
                      show "Graph.subpath_from (black prb') (fst (tgt re)) bes2'" 
                           using se_step(3) F \<open>bes2 = be # bes2'\<close> \<open>be = ui_edge re\<close> 
                           by (auto simp add : Graph.sp_Cons) 
                    qed
                  qed  
                qed
        
              next
                (* If the first edge of the black suffix is not represented by the new edge, then 
                   this first edge is still not represented in the new red part. Hence, the source 
                   of the new edge is in the fringe of the new red part (and not marked). We 
                   conclude by showing that res1 is a suitable red prefix, and bes2 a suitable 
                   black suffix. *)
                assume "be \<noteq> ui_edge re" 
        
                show ?thesis 
                unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                apply (intro disjI2)
                apply (rule_tac ?x="res1" in exI)
                apply (rule_tac ?x="bes2" in exI)
                apply (intro conjI)
                 apply (rule \<open>bes = ui_es res1 @ bes2\<close>)
                apply (rule_tac ?x="rv1" in exI)
                proof (intro conjI)
       
                  show "rv1 \<in> fringe prb'"
                       unfolding fringe_def mem_Collect_eq
                       proof (intro conjI)
                         show "rv1 \<in> red_vertices prb'" 
                         using se_step(3) B by (auto simp add : fringe_def vertices_def)
                       next
                         show "rv1 \<notin> subsumees (subs prb')" 
                         using se_step(3) B by (auto simp add : fringe_def)
                       next
                         show "\<not> marked prb' rv1" 
                         using B se_step(3) \<open>rv1 \<noteq> tgt re\<close> \<open>rv1 = src re\<close>
                         by (auto simp add : fringe_def)
                       next
                         have "be \<notin> ui_edge ` out_edges (red prb') rv1"
                              proof (intro notI)
                                assume "be \<in> ui_edge ` out_edges (red prb') rv1"
                            
                                then obtain re' where "be = ui_edge re'"
                                                and   "re' \<in> out_edges (red prb') rv1"
                                by blast
                            
                                show False 
                                using E
                                apply (elim notE)
                                apply (rule_tac ?x="[re']" in exI)
                                apply (rule_tac ?x="bes2'" in exI)
                                proof (intro conjI)
                                  show "bes2 = ui_es [re'] @ bes2'"
                                  using \<open>bes2 = be # bes2'\<close> \<open>be = ui_edge re'\<close> by simp
                                next
                                  show "[re'] \<noteq> []" by simp
                                next
                                  have "re' \<in> edges (red prb)" 
                                  using se_step(3) \<open>rv1 = src re\<close> \<open>re' \<in> out_edges (red prb') rv1\<close> 
                                        \<open>be \<noteq> ui_edge re\<close> \<open>be = ui_edge re'\<close> 
                                  by (auto simp add : vertices_def)
                            
                                  thus "subpath_from (red prb) rv1 [re'] (subs prb)"
                                  using \<open>re' \<in> out_edges (red prb') rv1\<close> 
                                        subs_sub_rel_of[OF se_step(1)]
                                  by (rule_tac ?x="tgt re'" in exI) 
                                     (simp add : rb_sp_one[OF se_step(1)])
                                qed
                              qed
                       
                         moreover
                         have "be \<in> out_edges (black prb) (fst rv1)" 
                              using F \<open>bes2 = be # bes2'\<close> by (simp add : Graph.sp_Cons)
                       
                         ultimately
                         show "ui_edge ` out_edges (red prb') rv1 \<subset> out_edges (black prb') (fst rv1)"
                              using se_step(3) red_OA_subset_black_OA[OF RB', of rv1] by auto
                       qed
                next
                  show "subpath (red prb') rv res1 rv1 (subs prb')" 
                        using se_step(3) C by (auto simp add : sp_in_extends_w_subs)
                (*next  show "\<not> marked prb' rv1" using se_step(3) D `rv1 \<noteq> tgt ra` by auto*)
                next
                  show "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                         \<and> res21 \<noteq> [] 
                                         \<and> subpath_from (red prb') rv1 res21 (subs prb'))"
                  apply (intro notI)
                  apply (elim exE conjE)
                  proof -
                    fix res21 bes22 rv3                    
                    assume "bes2 = ui_es res21 @ bes22"
                    and    "res21 \<noteq> []"
                    and    "subpath (red prb') rv1 res21 rv3 (subs prb')"        
                    moreover
                    then obtain re' res21' where "res21 = re' # res21'" 
                                           and   "be = ui_edge re'"
                         using \<open>bes2 = be # bes2'\<close> unfolding neq_Nil_conv   by (elim exE) simp        
                    ultimately
                    have "re' \<in> edges (red prb')" by (simp add : sp_Cons)       
                    moreover
                    have "re' \<notin> edges (red prb)" 
                         using E
                         apply (intro notI)
                         apply (elim notE)
                         apply (rule_tac ?x="[re']" in exI)
                         apply (rule_tac ?x="bes2'" in exI)
                         proof (intro conjI)
                           show "bes2 = ui_es [re'] @ bes2'" 
                           using \<open>bes2 = be # bes2'\<close> \<open>be = ui_edge re'\<close> by simp
                         next
                           show "[re'] \<noteq> []" by simp
                         next
                           assume "re' \<in> edges (red prb)"                           
                           thus   "subpath_from (red prb) rv1 [re'] (subs prb)"
                                  using  subs_sub_rel_of[OF se_step(1)]
                                        \<open>subpath (red prb') rv1 res21 rv3 (subs prb')\<close> 
                                        \<open>res21 = re' # res21'\<close>
                                  apply (rule_tac ?x="tgt re'" in exI)
                                  apply (simp add: rb_sp_Cons[OF RB'])
                                  apply (simp add : rb_sp_one[OF se_step(1)])
                                  using se_step(3) by auto
                         qed
        
                    ultimately
                    show False 
                         using se_step(3) \<open>be \<noteq> ui_edge re\<close> \<open>be = ui_edge re'\<close>   by auto
                  qed                           
                next
                  show "Graph.subpath_from (black prb') (fst rv1) bes2" 
                       using se_step(3) F by auto
                qed
              qed
            qed  
          next
            (* If rv1 is not the source of the new edge, then the out-going red edges of rv1 in the 
               new red part are the same as in the old red part. Thus res1 is a suitable red prefix, 
               and bes2 a suitable black suffix. *)
            assume "rv1 \<noteq> src re"
              
            show ?thesis
            unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
            apply (intro disjI2)
            apply (rule_tac ?x="res1" in exI)
            apply (rule_tac ?x="bes2" in exI)
             apply (intro conjI, goal_cases)
             proof -
               show "bes = ui_es res1 @ bes2" by (rule \<open>bes = ui_es res1 @ bes2\<close>)
             next
               case 2 show ?case 
               apply (rule_tac ?x="rv1" in exI)
               proof (intro conjI, goal_cases)      
                 show "rv1 \<in> fringe prb'" 
                      using se_step(3) B \<open>rv1 \<noteq> src re\<close> \<open>rv1 \<noteq> tgt re\<close>
                            seE_fringe1[OF subs_sub_rel_of[OF se_step(1)] se_step(3)]
                            seE_fringe2[OF se_step(3)]
                            seE_fringe3[OF se_step(3)]
                            seE_fringe4[OF subs_sub_rel_of[OF se_step(1)] se_step(3)] 
                            seE_fringe5[OF se_step(3)]
                      apply (case_tac "marked prb (src re)")
                       apply simp
                      apply (case_tac "ui_edge ` out_edges (red prb') (src re) \<subset> 
                                       out_edges (black prb) (fst (src re))") 
                       apply (case_tac "out_edges (black prb) (fst (tgt re)) = {}")
                        apply simp
                       apply simp   
                      apply (case_tac "out_edges (black prb) (fst (tgt re)) = {}")
                       apply simp
                      apply simp
                      done
               next
                 show "subpath (red prb') rv res1 rv1 (subs prb')"
                       using se_step(3) C by (auto simp add :sp_in_extends_w_subs)
                       (*next
                         show "\<not> marked prb' rv1" 
                         using se_step(3) B D by (elim conjE) (auto simp add : fringe_def)*)
               next
                 show "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                        \<and> res21 \<noteq> [] 
                                        \<and> subpath_from (red prb') rv1 res21 (subs prb'))" 
                 proof (intro notI, elim exE conjE)
                   fix res21 bes22 rv2             
                   assume "bes2 = ui_es res21 @ bes22"
                   and    "res21 \<noteq> []"
                   and    "subpath (red prb') rv1 res21 rv2 (subs prb')"             
                   then obtain re' res21' where "res21 = re' # res21'" 
                        using \<open>res21 \<noteq> []\<close> unfolding neq_Nil_conv by blast
             
                   have "rv1 = src re' \<or> (rv1,src re') \<in> subs prb"
                   and  "re' \<in> edges (red prb')"
                        using se_step(3) rb_sp_Cons[OF RB']
                             \<open>subpath (red prb') rv1 res21 rv2 (subs prb')\<close> \<open>res21 = re' # res21'\<close>
                        by auto
             
                   moreover
                   have "re' \<in> edges (red prb)"
                        proof -
                          have "re' \<noteq> re"
                               using \<open>rv1 = src re' \<or> (rv1,src re') \<in> subs prb\<close>
                               proof (elim disjE, goal_cases)
                                 case 1 thus ?thesis using \<open>rv1 \<noteq> src re\<close> by auto
                               next
                                 case 2 thus ?case 
                                             using B unfolding fringe_def subsumees_conv by fast
                               qed                              
                               thus ?thesis using se_step(3) \<open>re' \<in> edges (red prb')\<close> by simp
                        qed
                   
                   show False 
                        using E
                        apply (elim notE)
                        apply (rule_tac ?x="[re']" in exI)
                        apply (rule_tac ?x="ui_es res21' @ bes22" in exI)
                        proof (intro conjI)
                          show "bes2 = ui_es [re'] @ ui_es res21' @ bes22"
                               using \<open>bes2 = ui_es res21 @ bes22\<close> \<open>res21 = re' # res21'\<close> by simp
                        next
                         show "[re'] \<noteq> []" by simp
                        next
                          show "subpath_from (red prb) rv1 [re'] (subs prb)"
                               using se_step(1) 
                                     \<open>rv1 = src re' \<or> (rv1,src re') \<in> subs prb\<close> 
                                     \<open>re' \<in> edges (red prb)\<close>
                                     rb_sp_one subs_sub_rel_of 
                               by fast
                        qed
                 qed
               next
                 case 4 show ?case using se_step(3) F by auto
               qed
             qed
          qed
        
        qed

    next 
      (* If rl is the target of the new red edge, then we show that the empty (red) subpath is 
         suitable prefix and bes a suitable suffix, using the fact that the target of the new edge 
         is in the new fringe and can not be marked. *)
      assume "rv = tgt re"

      show ?thesis 
      proof (case_tac "out_edges (black prb) (fst (tgt re)) = {}")
        
        assume "out_edges (black prb) (fst (tgt re)) = {}"
        show ?thesis

           unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
           apply (intro disjI1)
           apply (rule_tac ?x="[]" in exI)
           proof (intro conjI, rule_tac ?x="tgt re" in exI, intro conjI)
             show "subpath (red prb') rv [] (tgt re) (subs prb')"
                  using se_step(3) \<open>rv = tgt re\<close> rb_Nil_sp[OF RB'] by (auto simp add : vertices_def)
           next
             have "sat (confs prb' (tgt re))" 
                  using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
                       \<open>rv = tgt re\<close> se_star_sat_imp_sat
                  by (auto simp add : feasible_def)
          
             thus "\<not> marked prb' (tgt re)" 
                  using se_step(3) sat_not_marked[OF RB', of "tgt re"]
                  by (auto simp add : vertices_def)
           next
             show "bes = ui_es []" 
                  using se_step(3) \<open>rv = tgt re\<close> \<open>out_edges (black prb) (fst (tgt re)) = {}\<close>
                        \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
                  by (cases bes) (auto simp add : Graph.sp_Cons)
           qed

      next
        assume "out_edges (black prb) (fst (tgt re)) \<noteq> {}"
        show ?thesis
        unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
        apply (intro disjI2)
        apply (rule_tac ?x="[]" in exI)
        apply (rule_tac ?x="bes" in exI)
        proof (intro conjI, goal_cases) 
          show "bes = ui_es [] @ bes" by simp
        next
          case 2   
          show ?case 
          apply (rule_tac ?x="rv" in exI)
          proof (intro conjI)
            have "\<not> marked prb (src re)" 
            proof -
              have "sat (confs prb' (tgt re))" 
                   using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
                         \<open>rv = tgt re\<close> se_star_sat_imp_sat
                   by (auto simp add : feasible_def)

              hence "sat (confs prb' (src re))" 
                    using se_step se_sat_imp_sat by auto

              moreover
              have "src re \<noteq> tgt re" using se_step by auto

              ultimately
              have "sat (confs prb (src re))" 
                   using se_step(3) by (auto simp add : vertices_def)

              thus ?thesis 
                   using se_step sat_not_marked[OF se_step(1), of "src re"]  by fast
            qed
  
            thus "rv \<in> fringe prb'" 
                 using se_step(3) \<open>rv = tgt re\<close> \<open>out_edges (black prb) (fst (tgt re)) \<noteq> {}\<close> 
                       seE_fringe1[OF subs_sub_rel_of[OF se_step(1)] se_step(3)] 
                       seE_fringe4[OF subs_sub_rel_of[OF se_step(1)]  se_step(3)] 
                 by auto
  
          next
  
            show "subpath (red prb') rv [] rv (subs prb')" 
                 using se_step(3) \<open>rv = tgt re\<close> subs_sub_rel_of[OF RB']
                 by (auto simp add : subpath_def vertices_def)
  
          next
  
            show "\<not> (\<exists>res21 bes22. bes = ui_es res21 @ bes22 
                                 \<and> res21 \<noteq> [] 
                                 \<and> subpath_from (red prb') rv res21 (subs prb'))"
  
            proof (intro notI, elim exE conjE)
              fix res1 bes22 rv'
  
              assume "bes = ui_es res1 @ bes22"
              and    "res1 \<noteq> []"
              and    "subpath (red prb') rv res1 rv' (subs prb')"
  
              have "out_edges (red prb') (tgt re) \<noteq> {} \<or> tgt re \<in> subsumees (subs prb')"
              proof -
                obtain re' res2 where "res1 = re'#res2" 
                       using \<open>res1 \<noteq> []\<close> unfolding neq_Nil_conv by blast
  
                hence "rv = src re' \<or> (rv,src re') \<in> subs prb"
                      using se_step(3) \<open>subpath (red prb') rv res1 rv' (subs prb')\<close>
                            rb_sp_Cons[OF RB', of rv re' res2 rv']
                      by auto
                
                thus ?thesis
                proof (elim disjE) 
                  assume "rv = src re'"
                  
                  moreover
                  hence "re' \<in> out_edges (red prb') (tgt re)" 
                        using \<open>subpath (red prb') rv res1 rv' (subs prb')\<close> 
                              \<open>res1 = re'#res2\<close> \<open>rv = tgt re\<close> 
                        by (auto simp add : sp_Cons)
                  
                  ultimately
                  show ?thesis using se_step(3) by auto
                next
                  assume "(rv,src re') \<in> subs prb"
  
                  hence "tgt re \<in> red_vertices prb" 
                        using se_step(3) \<open>rv = tgt re\<close> subs_sub_rel_of[OF se_step(1)]
                        unfolding sub_rel_of_def by force
  
                  thus ?thesis using se_step(3) by auto
                qed
              qed
  
              thus False 
              proof (elim disjE)
                assume "out_edges (red prb') (tgt re) \<noteq> {}" 
                thus ?thesis using se_step(3) 
                     by (auto simp add : vertices_def image_def)
              next
                assume "tgt re \<in> subsumees (subs prb')"
                
                hence "tgt re \<in> red_vertices prb" 
                       using se_step(3) subs_sub_rel_of[OF se_step(1)]
                       unfolding subsumees_conv sub_rel_of_def by fastforce
                
                thus ?thesis using se_step(3) by (auto simp add : vertices_def)
              qed
            qed
          next
            show "Graph.subpath_from (black prb') (fst rv) bes" 
                 using se_step(3) 
                       \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
                 by simp
          qed
        qed
      qed
    qed
  qed

next
  
  case (mark_step prb rv2 prb' rv1)
       have "finite_RedBlack prb" using mark_step by (auto simp add : finite_RedBlack_def)
  show ?case 
  unfolding subset_iff
  proof (intro allI impI) 
    (* Suppose that bes is a (black) feasible subpath starting at the black vertex represented by  
       red vertex rv1. Hence, by IH, bes is a red-black subpath starting at rv1 in the old red-black 
       graph. We proceed by case distinction. *)
    fix bes    
    assume "bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)"
    then obtain c where "se_star (confs prb rv1) (trace bes (labelling (black prb))) c"
                  and   "sat c"
         using mark_step(3) \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close>
         by (simp add : feasible_def) blast

    have "bes \<in> RedBlack_subpaths_from prb rv1" 
         using mark_step(2)[of rv1] mark_step(3-7) 
               \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close> 
         by auto
    
    thus "bes \<in> RedBlack_subpaths_from prb' rv1" 
    apply (subst (asm) RedBlack_subpaths_from_def)
    unfolding Un_iff image_def Bex_def mem_Collect_eq
    proof (elim disjE exE conjE)
      (* Suppose that bes is entirely represented in the old red part and let us call rv3 the red 
         vertex where it ends. We show that it is still fully represented in the new red-part and 
         that rv3 is still not marked in the new red-black graph. We call res the red subpath 
         representing bes in the old red part. *)
      fix res rv3
      assume "bes = ui_es res" 
      and    "subpath (red prb) rv1 res rv3 (subs prb)"
      and    "\<not> marked prb rv3"
      show ?thesis 

      unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
      proof (intro disjI1,rule_tac ?x="res" in exI,intro conjI)

        show "\<exists>rv'. subpath (red prb') rv1 res rv' (subs prb') \<and> \<not> marked prb' rv'" 
        apply (rule_tac ?x="rv3" in exI)
        proof (intro conjI)       
          show "subpath (red prb') rv1 res rv3 (subs prb')"
               using mark_step(3) \<open>subpath (red prb) rv1 res rv3 (subs prb)\<close>
               by auto
        next
          (* We then show that rv3 is not marked. *)
          show "\<not> marked prb' rv3" 
          proof -
            (* res being a red subpath from rv1 to rv3, and c being the configuration obtained 
               from the configuration at rv1 by symbolic execution of the trace of bes (and hence 
               res), we have that c is subsumed by the configuration at rv3. Hence, this 
               configuration is satisfiable, c being satisfiable. Thus, rv3 can not be marked. *)
            have "sat (confs prb rv3)"
                  proof -
                    have "c \<sqsubseteq> confs prb rv3"
                         using mark_step(1) 
                                 \<open>subpath (red prb) rv1 res rv3 (subs prb)\<close> 
                                 \<open>bes = ui_es res\<close>
                                 \<open>se_star (confs prb rv1) (trace bes (labelling (black prb))) c\<close>
                                 \<open>finite_RedBlack prb\<close>
                                 finite_RedBlack.SE_rel
                         by simp
                
                    thus ?thesis 
                         using \<open>se_star (confs prb rv1) (trace bes (labelling (black prb))) c\<close> 
                               \<open>sat c\<close>
                               sat_sub_by_sat
                         by fast
                  qed 
            thus ?thesis 
                 using mark_step(3) \<open>subpath (red prb) rv1 res rv3 (subs prb)\<close>
                       lst_of_sp_is_vert[of "red prb" rv1 res rv3 "subs prb"]
                       sat_not_marked[OF RedBlack.mark_step[OF mark_step(1,3)]]
                 by auto
          qed
        qed

      next
        (* By construction, res represents bes. *)
        show "bes = ui_es res" by (rule \<open>bes = ui_es res\<close>)
      qed

    next
      (* Suppose that bes has a maximal red prefix res1 leading to non-marked element rv3 of the old 
         fringe, and a black suffix bes2. We show that res1 and bes2 are still suitable red prefix 
         and black prefix, respectively, in the new red part. *)
      fix res1 bes2 rv3 bl

      assume A : "bes = ui_es res1 @ bes2"
      and    B : "rv3 \<in> fringe prb"
      and    C : "subpath (red prb) rv1 res1 rv3 (subs prb)" (*and    D : "\<not> marked prb rv3"*)
      and    E : "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                             \<and> res21 \<noteq> [] 
                             \<and> subpath_from (red prb) rv3 res21 (subs prb))"
      and    F : "Graph.subpath (black prb) (fst rv3) bes2 bl"

      show ?thesis 
      unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
      apply (intro disjI2)
      apply (rule_tac ?x="res1" in exI)
      apply (rule_tac ?x="bes2" in exI)
      proof (intro conjI, goal_cases)    
        show "bes = ui_es res1 @ bes2" by (rule \<open>bes = ui_es res1 @ bes2\<close>)
      next
        case 2 show ?case
        apply (rule_tac ?x="rv3" in exI)
        proof (intro conjI)
          (* Marking a red vertex does not change the fringe, so rv3 is in the new fringe. *)
          have "sat (confs prb rv3)" 
          proof -
            obtain c'
            where "se_star (confs prb rv1) (trace (ui_es res1) (labelling (black prb))) c'"
            and   "se_star c' (trace bes2 (labelling (black prb))) c"
            and   "sat c'"
                  using A \<open>se_star (confs prb rv1) (trace bes (labelling (black prb))) c\<close> \<open>sat c\<close>
                  by (simp add : se_star_append se_star_sat_imp_sat) blast
              
            moreover
            hence "c' \<sqsubseteq> confs prb rv3"
                  using \<open>finite_RedBlack prb\<close> mark_step(1) C finite_RedBlack.SE_rel by fast
  
            ultimately
            show ?thesis by (simp add : sat_sub_by_sat)
          qed

          thus "rv3 \<in> fringe prb'" using mark_step(3) B by (auto simp add : fringe_def)       
        next
          show "subpath (red prb') rv1 res1 rv3 (subs prb')"
               using mark_step(3) \<open>subpath (red prb) rv1 res1 rv3 (subs prb)\<close>
               by auto
        next
          (* We show that res1 is a maximal prefix, which is trivial because the new red part 
             contains less subpaths than the old, and res1 was already maximal. *)
          show "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                               \<and> res21 \<noteq> [] 
                               \<and> subpath_from (red prb') rv3 res21 (subs prb'))"
               proof (intro notI, elim exE conjE)
         
                 fix res21 bes22 rv4
         
                 assume "bes2 = ui_es res21 @ bes22"
                 and    "res21 \<noteq> []"
                 and    "subpath (red prb') rv3 res21 rv4 (subs prb')"
         
                 show False 
                      using E
                      proof (elim notE,rule_tac ?x="res21" in exI,
                             rule_tac ?x="bes22" in exI,intro conjI)
                        show "bes2 = ui_es res21 @ bes22" by (rule \<open>bes2 = ui_es res21 @ bes22\<close>)
                      next
                        show "res21 \<noteq> []" by (rule \<open>res21 \<noteq> []\<close>)
                      next
                        show "subpath_from (red prb) rv3 res21 (subs prb)"
                             using mark_step(3) 
                                   \<open>subpath (red prb') rv3 res21 rv4 (subs prb')\<close>
                             by (simp del : split_paired_Ex)  blast
                      qed
               qed

        next
          show "Graph.subpath_from (black prb') (fst rv3) bes2" using mark_step(3) F by simp blast  
        qed
      qed
    qed 
  qed

next

  case (subsum_step prb sub prb' rv)

  hence "finite_RedBlack prb" by (auto simp add : finite_RedBlack_def)
  
  have  RB' : "RedBlack prb'" by (rule RedBlack.subsum_step[OF subsum_step(1,3)])

  show ?case 
  unfolding subset_iff
  proof (intro allI impI)
    (* Let bes be a feasible subpath starting at a black vertex represented by rl. By IH, bes is 
       a red-black subpath in the old red-black graph. We proceed by case distinction. *)
    fix bes
    assume "bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)"

    hence  "bes \<in> RedBlack_subpaths_from prb rv" 
           using subsum_step(2)[of rv] subsum_step(3-7) by auto
    
    thus   "bes \<in> RedBlack_subpaths_from prb' rv"
    apply (subst (asm) RedBlack_subpaths_from_def)
    unfolding Un_iff image_def Bex_def mem_Collect_eq
    proof (elim disjE exE conjE)
      (* Suppose that bes is entirely represented in the old red part, then it is also entirely 
         represented in the new red part, qed. *)
      fix res rv'
      assume "bes = ui_es res"
      and    "subpath (red prb) rv res rv' (subs prb)"
      and    "\<not> marked prb rv'"
      thus   "bes \<in> RedBlack_subpaths_from prb' rv" 
             using subsum_step(3) sp_in_extends[of sub "red prb"]
             by (simp (no_asm) only : RedBlack_subpaths_from_def Un_iff image_def 
                                      Bex_def mem_Collect_eq,
                 intro disjI1, rule_tac ?x="res" in exI, intro conjI)
                (rule_tac ?x="rv'" in exI, auto)

    next
      (* Suppose that bes was of the form ui_es res1 @ bes2, with res1 ending in a red vertex that 
         we call rv'. *)
      fix res1 bes2 rv' bl
      assume A : "bes = ui_es res1 @ bes2"
      and    B : "rv' \<in> fringe prb"
      and    C : "subpath (red prb) rv res1 rv' (subs prb)"
      (*and    D : "\<not> marked prb rv'"*)
      and    E : "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                 \<and> res21 \<noteq> [] 
                                 \<and> subpath_from (red prb) rv' res21 (subs prb))"
      and    F : "Graph.subpath (black prb) (fst rv') bes2 bl"      
      show   "bes \<in> RedBlack_subpaths_from prb' rv" 
      proof (case_tac "rv' = subsumee sub")
        (* Suppose that rv' is the newly subsumed red vertex. The idea here is to show that 
           either bes2 is a suitable black suffix from the new subsumer, either it is of the form 
           ui_es res21 @ bes22 such that res21 is maximal and ends in a non-marked element of the 
           (new) fringe, making res1@res21 a suitable red prefix and bes22 a suitable black suffix 
           for bes to be a red-black subpath of the new red-black graph (note that bes2 and bes22 
           might be empty).

           However, assumptions from subsum_step and facts 1 to 6 are not sufficient to 
           to conclude. We proceed by beckward induction on bes2. *)

        assume "rv' = subsumee sub" 

        show ?thesis
             using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close> A C F
             proof (induct bes2 arbitrary : bes bl rule : rev_induct, goal_cases)
               (* Suppose that the black suffix is empty, then bes is entirely representend by res1 in 
                  the new red part and ends in rv' which is not marked, qed. *)
               case (1 bes bl) thus ?case
                    using subsum_step(3) B sp_in_extends[of sub "red prb"]
                    by (simp (no_asm) only : 
                          RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq,
                        intro disjI1, rule_tac ?x="res1" in exI, intro conjI)
                       (rule_tac ?x="rv'" in exI, auto simp add : fringe_def)
                    
        next
          (* Suppose that the black subpath is not empty. We call bes2 the prefix obtained from this
             subpath by removing its last edge, which we call be. 

             We first show that ui_es res1 @ bes2 is a red-black subpath in the old new-black graph.
             using our "internal" induction hypothesis. We then proceed by case distinction. *)
          case (2 be bes2 bes bl)
          then obtain c1 c2 c3 
               where "se_star (confs prb' rv) (trace (ui_es res1) (labelling (black prb))) c1"
               and   "se_star c1 (trace bes2 (labelling (black prb))) c2"
               and   "se c2 (labelling (black prb) be) c3"
               and   "sat c3"
               using subsum_step(3)
               by (simp add : feasible_def se_star_append se_star_append_one se_star_one) blast
             
          have "ui_es res1 @ bes2 \<in> RedBlack_subpaths_from prb' rv" 
          proof -
            have "ui_es res1 @ bes2 \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)" 
                 proof -
               
                   have "Graph.subpath_from (black prb') (fst rv) (ui_es res1 @ bes2)"
                   using subsum_step 2(5) red_sp_imp_black_sp[OF subsum_step(1) C]
                   by (simp add : Graph.sp_append) blast
               
                   moreover
                   have "feasible (confs prb' rv) 
                                  (trace (ui_es res1 @ bes2) (labelling (black prb')))"
                   proof -
                     have "se_star (confs prb' rv) 
                                   (trace (ui_es res1@bes2) (labelling (black prb'))) 
                                   c2"
                          using subsum_step 
                                \<open>se_star (confs prb' rv) (trace (ui_es res1) 
                                         (labelling (black prb))) (c1)\<close>
                                \<open>se_star c1 (trace bes2 (labelling (black prb))) c2\<close>
                     by (simp add : se_star_append) blast
               
                     moreover
                     have "sat c2" 
                          using \<open>se c2 (labelling (black prb) be) c3\<close> \<open>sat c3\<close>  
                          by (simp add : se_sat_imp_sat)
               
                     ultimately
                     show ?thesis by (simp add : feasible_def) blast
                   qed
               
                   ultimately
                   show ?thesis by simp
                 qed
  
            moreover
            have  "Graph.subpath_from (black prb) (fst rv') bes2"
                  using 2(5) by (auto simp add : Graph.sp_append_one)
  
            ultimately
            show ?thesis using 2(1,4) by(auto simp add : Graph.sp_append_one)
          qed

          thus ?case 
               apply (subst (asm) RedBlack_subpaths_from_def)
               unfolding Un_iff image_def Bex_def mem_Collect_eq
               proof (elim disjE exE conjE, goal_cases)
                 (* Suppose that ui_es res1 @ bes2 is entirely represented in the new red part by 
                    a red subpath that we call res, and ends in a red vertex that we call rv''. 
                    We conclude depending on the fact that be is represented by an out-going 
                    (red edge) from rv'' or not. *)
                 case (1 res rv'')  
                 show ?thesis 
                 proof (case_tac "be \<in> ui_edge ` out_edges (red prb') rv''")
                   (* If this is the case, then bes = ui_es res1 @ bes2 @ [be] is entirely 
                    represented in the new red part. We call ra the red edge representing be from 
                    rv''. 
               
                    Moreover, we showed earlier that the configuration c3 that is obtained from the 
                    configuration at rl by symbolic execution of (the trace of) 
                    bes = ui_es res1 @ bes2 @ [be] is satisfiable. As c3 is subsumed by the 
                    configuration at the target of ra, this last configuration is also satisfiable, 
                    and  thus not marked, qed. *)
                   assume "be \<in> ui_edge ` out_edges (red prb') rv''"
                   then obtain re where "be = ui_edge re"
                                  and   "re \<in> out_edges (red prb') rv''"
                        by blast
                                              
                   show ?thesis 
                        unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
                        apply (intro disjI1)
                        apply (rule_tac ?x="res@[re]" in exI)
                        proof (intro conjI,rule_tac ?x="tgt re" in exI,intro conjI)
                          show "subpath (red prb') rv (res@[re]) (tgt re) (subs prb')" 
                               using 1(2) \<open>re \<in> out_edges (red prb') rv''\<close> 
                               by (simp add : sp_append_one)
                        next
                          show "\<not> marked prb' (tgt re)" 
                          proof -
                            have "sat (confs prb' (tgt re))"
                            proof -
                              have "subpath (red prb') rv (res@[re]) (tgt re) (subs prb')" 
                                   using 1(2) \<open>re \<in> out_edges (red prb') rv''\<close> 
                                   by (simp add : sp_append_one)
                        
                              then obtain c 
                              where "se_star (confs prb' rv) 
                                             (trace (ui_es (res@[re])) (labelling (black prb))) 
                                             c"
                                    using subsum_step(3,5,6,7) RB'
                                          finite_RedBlack.sp_imp_ex_se_star_succ
                                                 [of prb' rv "res@[re]" "tgt re"]
                                    unfolding finite_RedBlack_def 
                                    by simp blast
                        
                              hence "sat c" 
                                    using 1(1)
                                          \<open>se_star (confs prb' rv) (trace (ui_es res1) 
                                                   (labelling (black prb))) (c1)\<close>
                                          \<open>se_star c1 (trace bes2 (labelling (black prb))) c2\<close>
                                          \<open>se c2 (labelling (black prb) be) c3\<close> 
                                          \<open>sat c3\<close> \<open>be = ui_edge re\<close>
                                          se_star_succs_states
                                                  [of "confs prb' rv" 
                                                      "trace(ui_es(res@[re]))(labelling(black prb))" 
                                                      c3]
                                    apply (subst (asm) eq_commute)
                                    by (auto simp add : se_star_append_one se_star_append 
                                                        se_star_one sat_eq)
                        
                              moreover
                              have "c \<sqsubseteq> confs prb' (tgt re)" 
                                   using subsum_step(3,5,6,7) 
                                         \<open>subpath (red prb') rv (res@[re]) (tgt re) (subs prb')\<close> 
                                         \<open>se_star (confs prb' rv)(trace (ui_es (res@[re])) 
                                                  (labelling (black prb)))(c)\<close>
                                         finite_RedBlack.SE_rel[of prb'] RB'
                                   by (simp add : finite_RedBlack_def)
                        
                              ultimately
                              show ?thesis by (simp add: sat_sub_by_sat)
                            qed
                        
                            thus ?thesis 
                                 using \<open>re \<in> out_edges (red prb') rv''\<close> 
                                       sat_not_marked[OF RB', of "tgt re"]
                                 by (auto simp add : vertices_def)
                          qed
                        next
                          show "bes = ui_es (res@[re])" using 1(1) 2(3) \<open>be = ui_edge re\<close> by simp
                        qed
                        
                 next
                   (* Suppose that be is not represented from rv''. We cannot conclude that [be] is 
                      a suitable suffix starting from rv'' for proving the goal, because rv'' might 
                      have been subsumed earlier. If this is the case, we have to show that [be] is 
                      a suitable suffix from the red vertex that subsums rv''. *)
                   assume "be \<notin> ui_edge ` out_edges (red prb') rv''"
               
                   show ?thesis
                   proof (case_tac "rv'' \<in> subsumees (subs prb')")
                     (* We suppose that rv'' is subsumed by a red vertex arv''. We conclude depen-
                        ding on the fact that be is represented in the out-going edges of arv'' or 
                        not. *)
                     assume "rv'' \<in> subsumees (subs prb')"
               
                     then obtain arv'' where "(rv'',arv'') \<in> (subs prb')" by auto
               
                     hence "subpath (red prb') rv res arv'' (subs prb')" 
                           using \<open>subpath (red prb') rv res rv'' (subs prb')\<close>
                           by (simp add : sp_append_sub)
               
                     show ?thesis
                     proof (case_tac "be \<in> ui_edge ` out_edges (red prb') arv''")
                       (* If be is represented in the out-going edges of arv'', then bes is entirely 
                          represented in the new red part, from rl to tgt ra. Moreover, the 
                          configuration at the target of ra subsums c, which is satisfiable, thus 
                          tgt ra can not be marked, qed. *)
                       assume "be \<in> ui_edge ` out_edges (red prb') arv''"
               
                       then obtain re where "re \<in> out_edges (red prb') arv''"
                                      and   "be = ui_edge re"
                            by blast
               
                       show ?thesis 
                            unfolding RedBlack_subpaths_from_def Un_iff image_def 
                                      Bex_def mem_Collect_eq
                            apply (intro disjI1)
                            apply (rule_tac ?x="res@[re]" in exI)
                            proof (intro conjI,rule_tac ?x="tgt re" in exI,intro conjI)
                            
                              show "subpath (red prb') rv (res @ [re]) (tgt re) (subs prb')"
                                   using \<open>subpath (red prb') rv res arv'' (subs prb')\<close> 
                                         \<open>re \<in> out_edges (red prb') arv''\<close>
                                   by (simp add : sp_append_one)
                            
                            next
                            
                              have "sat (confs prb' (tgt re))"
                              proof -
                                have "subpath (red prb') rv (res@[re]) (tgt re) (subs prb')" 
                                     using \<open>subpath (red prb') rv res arv'' (subs prb')\<close> 
                                             \<open>re \<in> out_edges (red prb') arv''\<close>
                                     by (simp add : sp_append_one)
                            
                                then obtain c 
                                where se : "se_star (confs prb' rv) (trace (ui_es (res@[re])) 
                                                    (labelling (black prb))) (c)"
                                      using subsum_step(3,5,6,7) RB'
                                            finite_RedBlack.sp_imp_ex_se_star_succ
                                                [of prb' rv "res@[re]" "tgt re"]
                                      unfolding finite_RedBlack_def 
                                      by simp blast
                            
                                hence "sat c" 
                                      using 1(1)
                                            \<open>se_star (confs prb' rv) (trace (ui_es res1) 
                                                     (labelling (black prb))) (c1)\<close>
                                            \<open>se_star c1 (trace bes2 (labelling (black prb))) c2\<close>
                                            \<open>se c2 (labelling (black prb) be) c3\<close> \<open>sat c3\<close> 
                                            \<open>be = ui_edge re\<close>
                                            se_star_succs_states
                                                    [of "confs prb' rv" 
                                                        "trace (ui_es(res@[re]))
                                                               (labelling (black prb))" 
                                                        "c3"]
                                      apply (subst (asm) eq_commute)
                                      by (auto simp add : se_star_append_one se_star_append 
                                                          se_star_one sat_eq)
                            
                                moreover
                                have "c \<sqsubseteq> confs prb' (tgt re)" 
                                     using subsum_step(3,5,6,7) se RB' 
                                           finite_RedBlack.SE_rel[of prb']
                                           \<open>subpath (red prb') rv (res@[re]) (tgt re) (subs prb')\<close>                          
                                     by (simp add : finite_RedBlack_def)
                            
                                ultimately
                                show ?thesis by (simp add: sat_sub_by_sat)
                              qed
                            
                              thus "\<not> marked prb' (tgt re)" 
                              using \<open>re \<in> out_edges (red prb') arv''\<close> 
                                    sat_not_marked[OF RB', of "tgt re"]
                              by (auto simp add : vertices_def)
                            
                            next
                            
                              show "bes = ui_es (res @ [re])" 
                              using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                    \<open>ui_es res1 @ bes2 = ui_es res\<close>
                                    \<open>be = ui_edge re\<close>
                              by simp
                            
                            qed
                            
                     next
                       (* Suppose that be is not represented in the out-going edges of arv''. We 
                          show that res is a suitable red prefix and [be] a suitable black prefix.*)
                       assume A : "be \<notin> ui_edge ` out_edges (red prb') arv''"
               
                       have "src be = fst arv''"
                       proof -
                         have "Graph.subpath (black prb') (fst rv) (ui_es res1 @ bes2) (fst arv'')"
                         using \<open>ui_es res1 @ bes2 = ui_es res\<close> 
                               \<open>subpath (red prb') rv res arv'' (subs prb')\<close> 
                               red_sp_imp_black_sp[OF RB']
                         by auto
               
                         moreover
                         have "Graph.subpath (black prb') (fst rv) (ui_es res1 @ bes2) (src be)"
                         using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv) (fst rv)\<close>
                               \<open>bes = ui_es res1 @ bes2 @ [be]\<close>
                         by (auto simp add : Graph.sp_append Graph.sp_append_one Graph.sp_one)
               
                         ultimately
                         show ?thesis 
                         using sp_same_src_imp_same_tgt by fast
                       qed
               
                       show ?thesis 
                       unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                       apply (intro disjI2)
                       apply (rule_tac ?x="res" in exI)
                       apply (rule_tac ?x="[be]" in exI)
                       proof (intro conjI, goal_cases)
                         
                         show "bes = ui_es res @ [be]" 
                         using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                               \<open>ui_es res1 @ bes2 = ui_es res\<close>
                         by simp
               
                       next
               
                         case 2 show ?case 
                         apply (rule_tac ?x="arv''" in exI)
                         proof (intro conjI) 
                           
                           show "arv'' \<in> fringe prb'" 
                           unfolding fringe_def mem_Collect_eq
                           proof (intro conjI)
                             show "arv'' \<in> red_vertices prb'" 
                             using \<open>subpath (red prb') rv res arv'' (subs prb')\<close>
                             by (simp add : lst_of_sp_is_vert)
                           next
                             show "arv'' \<notin> subsumees (subs prb')" 
                             using \<open>(rv'',arv'') \<in> subs prb'\<close> subs_wf_sub_rel[OF RB']
                             unfolding wf_sub_rel_def Ball_def
                             by (force simp del : split_paired_All)
                           next
                             show "\<not> marked prb' arv''"
                             using \<open>(rv'',arv'') \<in> (subs prb')\<close> subsumer_not_marked[OF RB']
                             by fastforce
                           next
                             have "be \<in> edges (black prb')" 
                             using subsum_step(3)
                                   \<open>Graph.subpath (black prb) (fst rv') (bes2 @ [be]) bl\<close>
                             by (simp add : Graph.sp_append_one)
               
                             thus "ui_edge ` out_edges (red prb') arv'' \<subset> out_edges (black prb') 
                                                                                    (fst arv'')"
                             using \<open>src be = fst arv''\<close> A  red_OA_subset_black_OA[OF RB', of arv'']
                             by auto
                           qed
               
                         next
               
                           show "subpath (red prb') rv res arv'' (subs prb')"
                           by (rule \<open>subpath (red prb') rv res arv'' (subs prb')\<close>)
               
                         next
               
                           show "\<not> (\<exists>res21 bes22. [be] = ui_es res21 @ bes22 
                                                \<and> res21 \<noteq> [] 
                                                \<and> subpath_from (red prb') arv'' res21 (subs prb'))"
                           proof (intro notI, elim exE conjE, goal_cases)
                             case (1 res21 bes22 rv''')
                               
                             have "be \<in> ui_edge ` out_edges (red prb') arv''" 
                             proof -
                               obtain re res21' where "res21 = re # res21'"
                               using 1(2) unfolding neq_Nil_conv by blast
               
                               have "be = ui_edge re" and  "re \<in> out_edges (red prb') arv''" 
                               proof -
                                 show "be = ui_edge re" using 1(1) \<open>res21 = re # res21'\<close> by simp
                               next
                                 have "re \<in> edges (red prb')"
                                      using 1(3) \<open>res21 = re # res21'\<close> by (simp add : sp_Cons)
                                 
                                 moreover
                                 have "src re = arv''"
                                 proof -
                                   have "(arv'',src re) \<notin> subs prb'" 
                                        using \<open>(rv'',arv'') \<in> subs prb'\<close> subs_wf_sub_rel[OF RB']
                                        unfolding wf_sub_rel_def Ball_def 
                                        by (force simp del : split_paired_All)
               
                                   thus ?thesis
                                        using 1(3) \<open>res21 = re # res21'\<close>
                                        by (simp add : rb_sp_Cons[OF RB'])
                                 qed
               
                                 ultimately
                                 show "re \<in> out_edges (red prb') arv''" by simp
                               qed
                               
                               thus ?thesis by auto
                             qed
               
                             thus False using A by (elim notE)
                           qed
               
                         next
               
                           show "Graph.subpath_from (black prb') (fst arv'') [be]" 
                                using subsum_step(3)
                                      \<open>Graph.subpath (black prb) (fst rv') (bes2 @ [be]) bl\<close>
                                      \<open>(rv'',arv'') \<in> subs prb'\<close>
                                      \<open>subpath (red prb') rv res arv'' (subs prb')\<close>
                                      \<open>src be = fst arv''\<close>
                                      RB' red_sp_imp_black_sp subs_to_same_BL
                                by (simp add : Graph.sp_append_one Graph.sp_one)
                         qed
                       qed
                     qed
               
                   next
                     (* Now suppose that rv'' is not subsumed in the new red-black graph. If be is 
                        represented in the out-going edges pf rv'', then ui_es res1 @ bes2 @ [be] 
                        is entirely represented in the new red part. Otherwise, res is a suitable 
                        red prefix and [be] a suitable black prefix. *)
                     assume "rv'' \<notin> subsumees (subs prb')"
                     
                     show ?thesis
                     proof (case_tac "be \<in> ui_edge ` out_edges (red prb') rv''")
               
                       assume "be \<in> ui_edge ` out_edges (red prb') rv''"
               
                       then obtain re where "be = ui_edge re"
                                      and   "re \<in> out_edges (red prb') rv''"
                            by blast
                       
                       show ?thesis 
                            unfolding RedBlack_subpaths_from_def Un_iff image_def 
                                      Bex_def mem_Collect_eq
                            apply (intro disjI1)
                            apply (rule_tac ?x="res @ [re]" in exI)
                            apply (intro conjI)
                            proof (rule_tac ?x="tgt re" in exI,intro conjI)
                              show "subpath (red prb') rv (res @ [re]) (tgt re) (subs prb')"
                                   using \<open>subpath (red prb') rv res rv'' (subs prb')\<close>
                                         \<open>re \<in> out_edges (red prb') rv''\<close>
                                   by (simp add : sp_append_one)
                            next
                              show "\<not> marked prb' (tgt re)"
                              proof -
                                have "sat (confs prb' (tgt re))"
                                proof -
                                  have "subpath (red prb') rv (res@[re]) (tgt re) (subs prb')" 
                                       using \<open>subpath (red prb') rv res rv'' (subs prb')\<close> 
                                               \<open>re \<in> out_edges (red prb') rv''\<close>
                                       by (simp add : sp_append_one)
                            
                                  then obtain c 
                                  where se : "se_star (confs prb' rv)(trace (ui_es (res@[re])) 
                                                      (labelling (black prb)))(c)"
                                        using subsum_step(3,5,6,7) RB'
                                            finite_RedBlack.sp_imp_ex_se_star_succ
                                                      [of prb' rv "res@[re]" "tgt re"]
                                        unfolding finite_RedBlack_def 
                                        by simp blast
                            
                                  hence "sat c" 
                                        using 1(1)
                                        \<open>se_star (confs prb' rv) (trace (ui_es res1) 
                                                 (labelling (black prb))) (c1)\<close>
                                        \<open>se_star c1 (trace bes2 (labelling (black prb))) c2\<close>
                                        \<open>se c2 (labelling (black prb) be) c3\<close> \<open>sat c3\<close> 
                                        \<open>be = ui_edge re\<close> 
                                        se_star_succs_states
                                              [of "confs prb' rv" 
                                                  "trace (ui_es (res@[re])) (labelling (black prb))" 
                                                  "c3"]
                                        apply (subst (asm) eq_commute)
                                        by (auto simp add : se_star_append_one se_star_append 
                                                            se_star_one sat_eq)
                            
                                  moreover
                                  have "c \<sqsubseteq> confs prb' (tgt re)" 
                                       using subsum_step(3,5,6,7) se RB' 
                                             finite_RedBlack.SE_rel[of prb']
                                             \<open>subpath (red prb') rv (res@[re]) (tgt re) (subs prb')\<close>  
                                       by (simp add : finite_RedBlack_def)
                            
                                  ultimately
                                  show ?thesis by (simp add: sat_sub_by_sat)
                                qed
                            
                                thus ?thesis
                                     using \<open>re \<in> out_edges (red prb') rv''\<close> 
                                           sat_not_marked[OF RB', of "tgt re"]
                                     by (auto simp add : vertices_def)
                              qed
                            next
                              show "bes = ui_es (res @ [re])" 
                                   using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                         \<open>ui_es res1 @ bes2 = ui_es res\<close>
                                         \<open>be = ui_edge re\<close>
                                   by simp
                            qed
                     
                     next
                       assume A : "be \<notin> ui_edge ` out_edges (red prb') rv''"
               
                       show ?thesis 
                            unfolding RedBlack_subpaths_from_def Un_iff Bex_def mem_Collect_eq
                            apply (intro disjI2)
                            apply (rule_tac ?x="res" in exI)
                            apply (rule_tac ?x="[be]" in exI)
                            proof (intro conjI, goal_cases)
                              show "bes = ui_es res @ [be]" 
                                   using \<open>ui_es res1 @ bes2 = ui_es res\<close> 
                                         \<open>bes = ui_es res1 @ bes2 @ [be]\<close>
                                   by simp
                            next
                            
                              case 2 
                            
                              have "src be = fst rv''"
                              proof -
                                have "Graph.subpath (black prb') (fst rv) (ui_es res) (src be)"
                                     using \<open>bes \<in> feasible_subpaths_from (black prb') 
                                                                         (confs prb' rv) (fst rv)\<close>
                                           \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                           \<open>ui_es res1 @ bes2 = ui_es res\<close>
                                           red_sp_imp_black_sp
                                               [OF RB' \<open>subpath (red prb') rv res rv'' (subs prb')\<close>]
                                     by (subst (asm)(2) eq_commute) 
                                        (auto simp add : Graph.sp_append Graph.sp_one)
                            
                                thus ?thesis 
                                using red_sp_imp_black_sp
                                          [OF RB' \<open>subpath (red prb') rv res rv'' (subs prb')\<close>]
                                by (rule sp_same_src_imp_same_tgt)
                              qed
                            
                              show ?case
                              apply (rule_tac ?x="rv''" in exI)
                              proof (intro conjI)
                            
                                show "rv'' \<in> fringe prb'" 
                                unfolding fringe_def mem_Collect_eq
                                proof (intro conjI)
                                  show "rv'' \<in> red_vertices prb'" 
                                       using \<open>subpath (red prb') rv res rv'' (subs prb')\<close>
                                       by (simp add : lst_of_sp_is_vert)
                                next
                                  show "rv'' \<notin> subsumees (subs prb')" 
                                  by (rule \<open>rv'' \<notin> subsumees (subs prb')\<close>)
                                next
                                  show "\<not> marked prb' rv''" by (rule \<open>\<not> marked prb' rv''\<close>)
                                next
                                  have "be \<in> edges (black prb')" 
                                       using subsum_step(3)
                                            \<open>Graph.subpath (black prb) (fst rv') (bes2 @ [be]) bl\<close>
                                       by (simp add : Graph.sp_append_one)
                            
                                  thus "ui_edge ` out_edges (red prb') rv'' \<subset> 
                                           out_edges (black prb') (fst rv'')"
                                       using \<open>src be = fst rv''\<close> A 
                                             red_OA_subset_black_OA[OF RB', of rv'']
                                       by auto
                                qed
                            
                              next
                            
                                show "subpath (red prb') rv res rv'' (subs prb')"
                                     by (rule \<open>subpath (red prb') rv res rv'' (subs prb')\<close>)
                            
                              next
                            
                                show "\<not> (\<exists>res21 bes22. [be] = ui_es res21 @ bes22 
                                                       \<and> res21 \<noteq> [] 
                                                       \<and> SubRel.subpath_from (red prb') (rv'') 
                                                                             (res21) (subs prb'))"
                                proof (intro notI, elim exE conjE, goal_cases)
                                  case (1 res21 bes22 rv''')
                                    
                                  have "be \<in> ui_edge ` out_edges (red prb') rv''" 
                                  proof -
                                    obtain re res21' where "res21 = re # res21'"
                                           using 1(2) unfolding neq_Nil_conv by blast
                            
                                    have "be = ui_edge re"
                                    and  "re \<in> out_edges (red prb') rv''" 
                                    proof -
                                      show "be = ui_edge re" using 1(1) \<open>res21 = re#res21'\<close> by simp
                                    next
                                      have "re \<in> edges (red prb')"
                                      using 1(3) \<open>res21 = re # res21'\<close> by (simp add : sp_Cons)
                                      
                                      moreover
                                      have "src re = rv''"
                                      proof -
                                        have "(rv'',src re) \<notin> subs prb'" 
                                             using \<open>rv'' \<notin> subsumees (subs prb')\<close> by force
                            
                                        thus ?thesis
                                              using 1(3) \<open>res21 = re # res21'\<close>
                                              by (simp add : rb_sp_Cons[OF RB'])
                                      qed
                            
                                      ultimately
                                      show "re \<in> out_edges (red prb') rv''" by simp
                                    qed
                                    
                                    thus ?thesis by auto
                                  qed
                            
                                  thus False using A by (elim notE)
                                qed
                            
                              next
                            
                                show "Graph.subpath_from (black prb') (fst rv'') [be]"
                                     using subsum_step(3) 
                                           \<open>Graph.subpath (black prb) (fst rv') (bes2 @ [be]) bl\<close> 
                                           \<open>src be = fst rv''\<close>
                                     by (rule_tac ?x="tgt be" in exI) 
                                        (simp add : Graph.sp_append_one Graph.sp_one)
                            
                              qed
                            qed
                     qed
                   qed
                 qed
               
               next
                 (* Now suppose that ui_es res1 @ bes2 is of the form ui_es res1' @ bes2'.
                    Then there exists a red vertex rv'' such that :
                    - res1' is a maximal red prefix ending in rv'', which is not marked and 
                      in the new  fringe,
                    - bes2' starts at the black vertex represented by rv''. 
               
                    Note that bes2' can be empty. If this is the case, then we conclude depending 
                    on the  fact that be is represented or not in the out-going edges of rv''.
               
                    If this is not the case, we show that bes2'@[be] is also a suitable black 
                    suffix. *)
                 case (2 res1' bes2' rv'' bl')
               
                 show ?thesis
                 proof (case_tac "bes2' = []")
                   (* Suppose that bes2' is empty. Then either be is represented in the 
                      out-going edges of rv'', either it is not. *)
                   assume "bes2' = []"
               
                   have "Graph.subpath (black prb') (fst rv) (ui_es res1' @ [be]) bl"
                   proof -
                     have "Graph.subpath (black prb') (fst rv) (ui_es res1') (src be)" 
                     proof -
                       have "Graph.subpath (black prb') (fst rv') bes2 (src be)"
                            using subsum_step(3) 
                                  \<open>Graph.subpath (black prb) (fst rv') (bes2@[be]) bl\<close>
                            by (simp add : Graph.sp_append_one)
               
                       moreover
                       have "subpath (red prb') rv res1 rv' (subs prb')"
                            using subsum_step(3) \<open>subpath (red prb) rv res1 rv' (subs prb)\<close>
                            by (auto simp add : sp_in_extends)
               
                       hence "Graph.subpath (black prb') (fst rv) (ui_es res1) (fst rv')"
                             using RB' by (simp add : red_sp_imp_black_sp)
               
                       ultimately
                       show ?thesis 
                            using \<open>ui_es res1 @ bes2 = ui_es res1' @ bes2'\<close> \<open>bes2' = []\<close>
                            by (subst (asm) eq_commute) (auto simp add : Graph.sp_append)
                     qed
               
                     moreover
                     have "Graph.subpath (black prb') (src be) [be] bl" 
                          using subsum_step(3) \<open>Graph.subpath (black prb) (fst rv') (bes2@[be]) bl\<close>
                          by (simp add : Graph.sp_append_one Graph.sp_one)
               
                     ultimately
                     show ?thesis by (auto simp add : Graph.sp_append)
                   qed
               
                   hence "Graph.subpath (black prb') (fst rv) (ui_es res1') (src be)"
                   and  "be \<in> edges (black prb')"
                   and  "tgt be = bl"
                        by (simp_all add : Graph.sp_append_one)
               
                   have "fst rv'' = src be"
                   proof -
                     have "Graph.subpath (black prb') (fst rv) (ui_es res1') (fst rv'')"
                          using \<open>subpath (red prb') rv res1' rv'' (subs prb')\<close> 
                                red_sp_imp_black_sp[OF RB']
                          by fast
               
                     thus ?thesis 
                          using \<open>Graph.subpath (black prb') (fst rv) (ui_es res1') (src be)\<close>
                          by (simp add : sp_same_src_imp_same_tgt)
                   qed
               
                   show ?thesis 
                   proof (case_tac "be \<in> ui_edge ` out_edges (red prb') rv''") 
                     (* If be is represented in the out-going edges of rv'' by a red edge that 
                        we call ra. Then ui_es res1'@[be] is entirely represented in the new 
                        red part. Moreover, the configuration at the target of ra subsums c 
                        which is satisfiable, and is in turn also satisfiable and thus not marked, 
                        qed. *)
                     assume "be \<in> ui_edge ` out_edges (red prb') rv''"
               
                     then obtain re where "be = ui_edge re"
                                    and   "re \<in> out_edges (red prb') rv''"
                          by blast
               
                     show ?thesis 
                          unfolding RedBlack_subpaths_from_def Un_iff 
                                    image_def Bex_def mem_Collect_eq
                          apply (intro disjI1)
                          apply (rule_tac ?x="res1'@[re]" in exI)
                          apply (intro conjI)
                          apply (rule_tac ?x="tgt re" in exI)
                          proof (intro conjI)
                            show "subpath (red prb') rv (res1' @ [re]) (tgt re) (subs prb')"
                                 using \<open>subpath (red prb') rv res1' rv'' (subs prb')\<close> 
                                       \<open>re \<in> out_edges (red prb') rv''\<close>
                                 by (simp add : sp_append_one)
                          next
                            show "\<not> marked prb' (tgt re)" 
                            proof -                    
                              have "sat (confs prb' (tgt re))" 
                                   proof -
                                     have "subpath (red prb') rv (res1'@[re]) (tgt re) (subs prb')" 
                                          using \<open>subpath (red prb') rv res1' rv'' (subs prb')\<close> 
                                                  \<open>re \<in> out_edges (red prb') rv''\<close>
                                          by (simp add : sp_append_one)
                                   
                                     then obtain c 
                                     where se : "se_star (confs prb' rv) (trace (ui_es (res1'@[re])) 
                                                         (labelling (black prb))) (c)"
                                         using subsum_step(3,5,6,7) RB'
                                               finite_RedBlack.sp_imp_ex_se_star_succ
                                                      [of prb' rv "res1'@[re]" "tgt re"]
                                         unfolding finite_RedBlack_def 
                                         by simp blast
                                   
                                     hence "sat c"
                                           proof -
                                             have "bes = ui_es (res1'@[re])" 
                                                  using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                                        \<open>be = ui_edge re\<close> \<open>bes2' = []\<close>
                                                        \<open>ui_es res1 @ bes2 = ui_es res1' @ bes2'\<close> 
                                                  by simp
                                           
                                             thus ?thesis 
                                                  using subsum_step(3) se_star_succs_states[OF se]
                                                        \<open>bes \<in> feasible_subpaths_from (black prb') 
                                                                                   (confs prb' rv) 
                                                                                   (fst rv)\<close>           
                                                  by (auto simp add : feasible_def sat_eq)
                                           qed
                                   
                                     moreover
                                     have "c \<sqsubseteq> confs prb' (tgt re)" 
                                          using subsum_step(3,5,6,7) se 
                                                finite_RedBlack.SE_rel[of prb'] RB'
                                                \<open>subpath (red prb') (rv) (res1'@[re]) 
                                                         (tgt re) (subs prb')\<close> 
                                          by (simp add : finite_RedBlack_def)
                                   
                                     ultimately
                                     show ?thesis by (simp add: sat_sub_by_sat)
                                   qed
                          
                              thus ?thesis 
                                   using \<open>re \<in> out_edges (red prb') rv''\<close> 
                                         sat_not_marked[OF RB', of "tgt re"]
                                   by (auto simp add : vertices_def)
                            qed
                          next
                            show "bes = ui_es (res1' @ [re])"
                            using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                  \<open>ui_es res1 @ bes2 = ui_es res1' @ bes2'\<close>
                                  \<open>bes2' = []\<close> \<open>be = ui_edge re\<close>
                            by simp
                          qed
                   
                   next
                     (* If be is not represented in the out-going edges of rv'', then we show that 
                        [be] is a suitable black suffix, res1' being known to be a suitable red 
                         prefix. *)
                     assume A : "be \<notin> ui_edge ` out_edges (red prb') rv''"
                     show ?thesis 
               
                          unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                          apply (intro disjI2)
                          apply (rule_tac ?x="res1'" in exI)
                          apply (rule_tac ?x="[be]"  in exI)
                          proof (intro conjI, goal_cases)
                          
                            show "bes = ui_es res1' @ [be]"
                                 using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                       \<open>ui_es res1 @ bes2 = ui_es res1' @ bes2'\<close>
                                       \<open>bes2' = []\<close> 
                                 by simp
                          
                          next
                          
                            case 2 show ?case 
                            apply (rule_tac ?x="rv''" in exI)
                            proof (intro conjI)
                          
                              show "rv'' \<in> fringe prb'" by (rule \<open>rv'' \<in> fringe prb'\<close>)
                          
                            next
                          
                              show "subpath (red prb') rv res1' rv'' (subs prb')"
                                   by (rule \<open>subpath (red prb') rv res1' rv'' (subs prb')\<close>)
                          
                            (*next
                          
                              show "\<not> marked prb' rv''" by (rule `\<not> marked prb' rv''`)*)
                          
                            next
                          
                              show "\<not> (\<exists>res21 bes22. [be] = ui_es res21 @ bes22 
                                                   \<and> res21 \<noteq> [] 
                                                   \<and> subpath_from (red prb') (rv'') 
                                                                  (res21) (subs prb'))"
                              proof (intro notI, elim exE conjE, goal_cases)
                                case (1 res21 bes22 rv''')
                          
                                then obtain re res21' where "be = ui_edge re"
                                                      and   "res21 = re # res21'"
                                     unfolding neq_Nil_conv by auto
                                
                                moreover
                                hence "re \<in> out_edges (red prb') rv''"
                                      using 1(3) \<open>rv'' \<in> fringe prb'\<close> RB'
                                      unfolding subsumees_conv by (force simp add : fringe_def 
                                                                                    rb_sp_Cons)
                                  
                                ultimately
                                show False using A by auto
                              qed
                          
                            next
                          
                              show "Graph.subpath_from (black prb') (fst rv'') [be]"
                                   using \<open>Graph.subpath (black prb') (fst rv)(ui_es res1'@[be]) bl\<close> 
                                         \<open>fst rv'' = src be\<close> 
                                   by (auto simp add : Graph.sp_append_one Graph.sp_one)
                          
                            qed
                          qed
                   qed
               
                 next
                   (* Suppose that bes2' is not empty. Then appending be at the end of bes2' gives a 
                      suitable black suffix, qed. *)
                   assume "bes2' \<noteq> []"
               
                   then obtain be' bes2'' where "bes2' = be' # bes2''"
                        unfolding neq_Nil_conv by blast
               
                   show ?thesis 
                        unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                        apply (intro disjI2)
                        apply (rule_tac ?x="res1'" in exI)
                        apply (rule_tac ?x="bes2'@[be]" in exI)
                        proof (intro conjI, goal_cases)
                        
                          show "bes = ui_es res1' @ bes2' @ [be]"
                          using \<open>bes = ui_es res1 @ bes2 @ [be]\<close> 
                                \<open>ui_es res1 @ bes2 = ui_es res1' @ bes2'\<close>
                          by simp
                        
                        next
                        
                          case 2 show ?case 
                              apply (rule_tac ?x="rv''" in exI)
                              proof (intro conjI)
                              
                                show " rv'' \<in> fringe prb'" by (rule \<open> rv'' \<in> fringe prb'\<close>)
                              
                              next
                              
                                show "subpath (red prb') rv res1' rv'' (subs prb')"
                                     by (rule \<open>subpath (red prb') rv res1' rv'' (subs prb')\<close>)
                              
                              next
                              
                                show "\<not> (\<exists>res21 bes22. bes2' @ [be] = ui_es res21 @ bes22 
                                                     \<and> res21 \<noteq> [] 
                                                     \<and> subpath_from (red prb') (rv'') 
                                                                    (res21) (subs prb'))"
                                proof (intro notI, elim exE conjE, goal_cases)
                                  case (1 res21 bes22 rv''')
                              
                                  then obtain re res21' where "res21 = re # res21'"
                                                        and   "be' = ui_edge re"
                                  using \<open>bes2' = be' # bes2''\<close> unfolding neq_Nil_conv by auto
                              
                                  show False 
                                       using \<open>\<not> (\<exists>res21 bes22. bes2' = ui_es res21 @ bes22 
                                                             \<and> res21 \<noteq> [] 
                                                             \<and> subpath_from (red prb') (rv'') 
                                                                             (res21) (subs prb'))\<close>
                                       apply (elim notE)
                                       apply (rule_tac ?x="[re]" in exI)
                                       apply (rule_tac ?x="bes2''" in exI)
                                       proof (intro conjI)
                                         show "bes2' = ui_es [re] @ bes2''"
                                              using \<open>bes2' @ [be] = ui_es res21 @ bes22\<close> 
                                                    \<open>bes2' = be' # bes2''\<close>
                                                    \<open>be' = ui_edge re\<close>
                                              by simp
                                       next
                                         show "[re] \<noteq> []" by simp
                                       next
                                         show "subpath_from (red prb') rv'' [re] (subs prb')"
                                              using \<open>subpath (red prb') rv'' res21 rv'''(subs prb')\<close> 
                                                    \<open>res21 = re # res21'\<close>
                                              by (fastforce simp add : sp_Cons Nil_sp vertices_def)
                                       qed
                                qed
                              
                              next
                              
                                show "Graph.subpath_from (black prb') (fst rv'') (bes2' @ [be])"
                                proof -
                                  have "Graph.subpath (black prb') (fst rv) 
                                                      (ui_es res1' @ bes2') (src be)"
                                  proof -
                                    have "Graph.subpath (black prb') (fst rv) 
                                                        (ui_es res1 @ bes2) (src be)"
                                         using \<open>bes \<in> feasible_subpaths_from (black prb') 
                                                                             (confs prb' rv) 
                                                                             (fst rv)\<close>
                                               \<open>bes = ui_es res1 @ bes2 @ [be]\<close>
                                         by (auto simp add : Graph.sp_append Graph.sp_one)
                              
                                    thus ?thesis using \<open>ui_es res1 @ bes2 = ui_es res1'@bes2'\<close> 
                                                 by simp
                                  qed
                              
                                  moreover
                                  have "Graph.subpath (black prb')(fst rv)(ui_es res1' @ bes2') bl'"
                                       using \<open>Graph.subpath (black prb') (fst rv'') bes2' bl'\<close>
                                             red_sp_imp_black_sp[OF RB' 
                                                                   \<open>subpath (red prb')(rv)(res1') 
                                                                            (rv'') (subs prb')\<close>]
                                       by (auto simp add : Graph.sp_append)
                                  
                                  ultimately
                                       have "src be = bl'" by (rule sp_same_src_imp_same_tgt)
                              
                                  moreover
                                  have "Graph.subpath (black prb') (src be) [be] (tgt be)" 
                                       using subsum_step(3) 
                                             \<open>Graph.subpath (black prb) (fst rv') (bes2@[be]) bl\<close> 
                                       by (auto simp add : Graph.sp_append_one Graph.sp_one)
                              
                                  ultimately
                                  show ?thesis 
                                       using \<open>Graph.subpath (black prb') (fst rv'') bes2' bl'\<close>
                                       by (simp add : Graph.sp_append_one Graph.sp_one)
                                qed
                              qed
                        qed
                 qed
               qed
        qed
          
      next
        (* Suppose that rv' is not the newly subsumed red vertex. Hence, rv' is still not marked 
           and in the fringe and res1 is still maximal, which makes res1 and bes2 suitable red 
           prefix and black suffix in the new red part. *)
        assume "rv' \<noteq> subsumee sub"
        
        show ?thesis
             unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
             apply (intro disjI2)
             apply (rule_tac ?x="res1" in exI)
             apply (rule_tac ?x="bes2" in exI)
             proof (intro conjI, goal_cases)
               show "bes = ui_es res1 @ bes2" by (rule \<open>bes = ui_es res1 @ bes2\<close>)
             next
             
               case 2 show ?case
               apply (rule_tac ?x="rv'" in exI)
               proof (intro conjI)
                 show "rv'\<in> fringe prb'" 
                 using subsum_step(3) subsumE_fringe[OF subsum_step(3)] B \<open>rv' \<noteq> subsumee sub\<close> 
                 by simp
               next
                 show "subpath (red prb') rv res1 rv' (subs prb')" 
                 using subsum_step(3) C by (auto simp add : sp_in_extends)
               (*next
                 show "\<not> marked prb' rv'" using subsum_step(3) D by auto*)
               next
                 show "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                      \<and> res21 \<noteq> [] 
                                      \<and> subpath_from (red prb') rv' res21 (subs prb'))"
                 proof (intro notI, elim exE conjE)
                   fix res21 bes22 rv''
             
                   assume "bes2 = ui_es res21 @ bes22"
                   and    "res21 \<noteq> []"
                   and    "subpath (red prb') rv' res21 rv'' (subs prb')"
             
                   then obtain re res21' where "res21 = re # res21'" 
                   unfolding neq_Nil_conv by blast
             
                   have "subpath (red prb) rv' [re] (tgt re) (subs prb)"
                   proof -
                     have "\<not> uses_sub rv' [re] (tgt re) sub" using \<open>rv' \<noteq> subsumee sub\<close> by auto
             
                     thus ?thesis 
                     using subsum_step(3)
                         \<open>subpath (red prb') rv' res21 rv'' (subs prb')\<close> \<open>res21 = re # res21'\<close>
                         wf_sub_rel_of.sp_in_extends_not_using_sub
                         [OF subs_wf_sub_rel_of[OF subsum_step(1)],
                          of "subsumee sub" "subsumer sub" "subs prb'" rv' "[re]" "tgt re"]
                         rb_sp_Cons[OF RB', of rv' re res21' rv'']
                         rb_sp_one[OF subsum_step(1), of rv' re "tgt re"]
                         subs_sub_rel_of[OF subsum_step(1)]
                     by auto
                   qed
             
                   show False
                   using E
                   apply (elim notE)
                   apply (rule_tac ?x="[re]" in exI)
                   apply (rule_tac ?x="ui_es res21'@bes22" in exI)
                   proof (intro conjI)
                     show "bes2 = ui_es [re] @ ui_es res21' @ bes22"
                     using \<open>bes2 = ui_es res21 @ bes22\<close> \<open>res21 = re # res21'\<close> by simp
                   next
                     show "[re] \<noteq> []" by simp
                   next
                     show "subpath_from (red prb) rv' [re] (subs prb)"
                     apply (rule_tac ?x="tgt re" in exI)
                     using subsum_step(3)
                         \<open>rv' \<noteq> subsumee sub\<close> \<open>subpath (red prb') rv' res21 rv'' (subs prb')\<close>
                         \<open>res21 = re # res21'\<close>
                         rb_sp_Cons[OF RB', of rv' re res21' rv'']
                         rb_sp_one[OF subsum_step(1), of rv' re "tgt re"]
                         subs_sub_rel_of[OF subsum_step(1)] subs_sub_rel_of[OF RB']
                     by fastforce
                   qed
                 qed
               next
                 show "Graph.subpath_from (black prb') (fst rv') bes2" 
                 using subsum_step(3) F by simp blast
               qed
             qed
      qed
    qed
  qed

next 

  case (abstract_step prb rv2 c\<^sub>a prb' rv1)
    have RB' : "RedBlack prb'" by (rule RedBlack.abstract_step[OF abstract_step(1,3)])
    have "finite_RedBlack prb" using abstract_step by (auto simp add : finite_RedBlack_def)
    show ?case
    unfolding subset_iff
    proof (intro allI impI)
      (* Suppose that bes is a feasible subpath starting at the black vertex represented by the red 
         vertex rv1. We proceed depending on the fact that rv1 is the red vertex where the abstrac-
         tion  took place or not. We have to make this distinction to be able to use our IH, in the 
         case where rv1 \<noteq> rv2. *)
      fix bes
    
      assume "bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)"
      
      show "bes \<in> RedBlack_subpaths_from prb' rv1" 
      proof (case_tac "rv2 = rv1")
        (* If this is the case, then the only possible red prefix is the empty edge sequence. By 
           definition of the abstraction operator, we have that the empty sequence is indeed a 
           suitable red prefix and that bes is suitable black prefix. *)
        assume "rv2 = rv1"
    
        show ?thesis 
             proof (case_tac "out_edges (black prb') (fst rv1) = {}")
               assume "out_edges (black prb') (fst rv1) = {}"
               show ?thesis
                     unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
                     apply (intro disjI1)
                     apply (rule_tac ?x="[]" in exI)
                     apply (intro conjI)
                      apply (rule_tac ?x="rv1" in exI)
                      proof (intro conjI)
                        show "subpath (red prb') rv1 [] rv1 (subs prb')"
                        using abstract_step(4) rb_Nil_sp[OF RB'] by fast
                      next
                        show "\<not> marked prb' rv1" using abstract_step(3) \<open>rv2 = rv1\<close> by simp
                      next
                        show "bes = ui_es []"
                        using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close>
                              \<open>out_edges (black prb') (fst rv1) = {}\<close>
                        by (cases bes) (auto simp add : Graph.sp_Cons)
                      qed
                
             next
               assume "out_edges (black prb') (fst rv1) \<noteq> {}"
               
               show ?thesis 
               unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
               apply (intro disjI2)
               apply (rule_tac ?x="[]"  in exI)
               apply (rule_tac ?x="bes" in exI)
               proof (intro conjI, goal_cases)
             
                 show "bes = ui_es [] @ bes" by simp
             
               next
             
                 case 2 show ?case 
                 apply (rule_tac ?x="rv1" in exI)
                 proof (intro conjI)
             
                   show "rv1 \<in> fringe prb'" 
                   using abstract_step(1,3) \<open>rv2 = rv1\<close> \<open>out_edges (black prb') (fst rv1) \<noteq> {}\<close>
                   by (auto simp add : fringe_def)
             
                 next
             
                   show "subpath (red prb') rv1 [] rv1 (subs prb')" 
                   using abstract_step(3) \<open>rv2 = rv1\<close> 
                         rb_Nil_sp[OF RedBlack.abstract_step[OF abstract_step(1,3)]]
                   by auto
             
                 (*next
             
                   show "\<not> marked prb' rv1"  using abstract_step(3) `rv2 = rv1` by simp*)
             
                 next
             
                   show "\<not> (\<exists>res21 bes22. bes = ui_es res21 @ bes22 
                                        \<and> res21 \<noteq> [] 
                                        \<and> subpath_from (red prb') rv1 res21 (subs prb'))"
                   proof (intro notI, elim exE conjE)
                     fix res21 rv3
             
                     assume "res21 \<noteq> []" 
                     and    "subpath (red prb') rv1 res21 rv3 (subs prb')"
             
                     moreover
                     then obtain re res21' where "res21 = re # res21'" 
                          unfolding neq_Nil_conv by blast
             
                     ultimately
                     have "re \<in> out_edges (red prb') rv1"
                     using abstract_step(3) \<open>rv2 = rv1\<close>
                           rb_sp_Cons[OF RedBlack.abstract_step[OF abstract_step(1,3)], 
                                      of rv1 re res21' rv3]
                     unfolding subsumees_conv by fastforce
             
                     thus False using abstract_step(3) \<open>rv2 = rv1\<close> by auto
                   qed
             
                 next
             
                   show "Graph.subpath_from (black prb') (fst rv1) bes"
                   using \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close>
                   by simp
             
                 qed
               qed
             qed
             
      next
        (* Suppose that rv1 is not the red vertex where the abstraction took place. Then, as 
           abstracting a configuration has no effect on the rest of the red tree, we can show by IH 
           that bes is red-black supbeth of the old red-black graph. We conclude by case 
            distinction. *)
        assume "rv2 \<noteq> rv1"
    
        moreover
        hence "feasible (confs prb rv1) (trace bes (labelling (black prb)))"
              using abstract_step(3) 
                    \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close>
              by simp 
    
        ultimately
        have "bes \<in> RedBlack_subpaths_from prb rv1"
              using abstract_step(2)[of rv1] abstract_step(3-7)
                    \<open>bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)\<close>
              by auto
    
        thus ?thesis 
             apply (subst (asm) RedBlack_subpaths_from_def)
             unfolding Un_iff image_def Bex_def mem_Collect_eq
             proof (elim disjE exE conjE)
             
               fix res rv3
             
               assume " bes = ui_es res"
               and    "subpath (red prb) rv1 res rv3 (subs prb)"
               and    "\<not> marked prb rv3"
             
               thus ?thesis 
               using abstract_step(3)
               unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
               by (intro disjI1, rule_tac ?x="res" in exI, intro conjI)
                  (rule_tac ?x="rv3" in exI, simp_all)
             next
             
               fix res1 bes2 rv3 bl
               assume A : "bes = ui_es res1 @ bes2"
               and    B : "rv3 \<in> fringe prb"
               and    C : "subpath (red prb) rv1 res1 rv3 (subs prb)"
               and    E : "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                      \<and> res21 \<noteq> [] 
                                      \<and> subpath_from (red prb) rv3 res21 (subs prb))"
               and    F : "Graph.subpath (black prb) (fst rv3) bes2 bl"
             
               show ?thesis 
                    unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                    apply (intro disjI2)
                    apply (rule_tac ?x="res1" in exI)
                    apply (rule_tac ?x="bes2" in exI)
                    proof (intro conjI, goal_cases)
                      show "bes = ui_es res1 @ bes2" by (rule \<open>bes = ui_es res1 @ bes2\<close>)
                    next
                      case 2 show ?case
                      using abstract_step(3) B C E F unfolding fringe_def
                      by (rule_tac ?x="rv3" in exI) auto
                    qed
             qed
      qed
    qed

next
  (* Strengthening a configuration with an invariant will help refuse "brutal" abstractions. As 
     all abstractions preserves the set of feasible paths, we conclude. *)
  case (strengthen_step prb rv2 e prb' rv1)
  show?case
       unfolding subset_iff
       proof (intro allI impI)
     
         fix bes 
         assume "bes \<in> feasible_subpaths_from (black prb') (confs prb' rv1) (fst rv1)"
         hence  "bes \<in> RedBlack_subpaths_from prb rv1"
                using strengthen_step(2)[of rv1] strengthen_step(3-7) by auto
     
         thus "bes \<in> RedBlack_subpaths_from prb' rv1"
         apply (subst (asm) RedBlack_subpaths_from_def)
         unfolding Un_iff image_def Bex_def mem_Collect_eq
         proof (elim disjE exE conjE)
     
           fix res rv2
           assume "bes = ui_es res"
           and    "subpath (red prb) rv1 res rv2 (subs prb)"
           and    "\<not> marked prb rv2"
           thus ?thesis 
                using strengthen_step(3)
                unfolding RedBlack_subpaths_from_def Un_iff image_def Bex_def mem_Collect_eq
                by (intro disjI1) fastforce
     
         next
     
           fix res1 bes2 rv3 bl
     
           assume A : "bes = ui_es res1 @ bes2"
           and    B : "rv3 \<in> fringe prb"
           and    C : "subpath (red prb) rv1 res1 rv3 (subs prb)"
           (*and    D : "\<not> marked prb rv3"*)
           and    E : "\<not> (\<exists>res21 bes22. bes2 = ui_es res21 @ bes22 
                                  \<and> res21 \<noteq> [] 
                                  \<and> subpath_from (red prb) rv3 res21 (subs prb))"
           and    F : "Graph.subpath (black prb) (fst rv3) bes2 bl"
     
           show ?thesis 
                unfolding RedBlack_subpaths_from_def Un_iff mem_Collect_eq
                apply (intro disjI2)
                apply (rule_tac ?x="res1" in exI)
                apply (rule_tac ?x="bes2" in exI)
                proof (intro conjI, goal_cases)
                  show "bes = ui_es res1 @ bes2" by (rule \<open>bes = ui_es res1 @ bes2\<close>)
                next
                  case 2 
                  show ?case
                       using strengthen_step(3) B C E F unfolding fringe_def 
                       by (rule_tac ?x="rv3" in exI) auto
                qed
     
         qed
       qed
qed


text \<open>Red-black paths being red-black sub-path starting from the red root, and feasible paths 
being feasible sub-paths starting at the black initial location, it follows from the previous 
theorem that the set of feasible paths when considering the configuration of the root is a 
subset of the set of red-black paths.\<close>

theorem (in finite_RedBlack) feasible_path_inclusion :
  assumes "RedBlack prb"
  shows   "feasible_paths (black prb) (confs prb (root (red prb))) \<subseteq> RedBlack_paths prb"
using feasible_subpaths_preserved[OF assms, of "root (red prb)"] consistent_roots[OF assms]
by (simp add : vertices_def)

text \<open>The configuration at the red root might have been abstracted. In this case, the initial 
configuration is subsumed by the current configuration at the root. Thus the set of feasible paths 
when considering the initial configuration is also a subset of the set of red-black paths.\<close>

lemma init_subsumed :
  assumes "RedBlack prb"
  shows   "init_conf prb \<sqsubseteq> confs prb (root (red prb))"
using assms
proof (induct prb)
  case base thus ?case by (simp add: subsums_refl)
next
  case se_step thus ?case by (force simp add : vertices_def)
next
  case mark_step thus ?case by simp
next
  case subsum_step thus ?case by simp
next
  case (abstract_step prb rv c\<^sub>a prb')
  thus ?case by (auto simp add : abstract_def subsums_trans)
next
  case strengthen_step thus ?case by simp
qed


theorem (in finite_RedBlack) feasible_path_inclusion_from_init :
  assumes "RedBlack prb"
  shows   "feasible_paths (black prb) (init_conf prb) \<subseteq> RedBlack_paths prb"
unfolding subset_iff mem_Collect_eq
proof (intro allI impI, elim exE conjE, goal_cases)
  case (1 es bl)

  hence "es \<in> feasible_subpaths_from (black prb) (init_conf prb) (fst (root (red prb)))"
        using consistent_roots[OF assms] by simp blast

  hence "es \<in> feasible_subpaths_from (black prb) (confs prb (root (red prb))) (fst(root(red prb)))"
        unfolding mem_Collect_eq
        proof (elim exE conjE, goal_cases)
          case (1 bl')
       
          show ?case 
          proof (rule_tac ?x="bl'" in exI, intro conjI)
            show "Graph.subpath (black prb) (fst (root (red prb))) es bl'" by (rule 1(1))
          next
            have "finite_labels (trace es (labelling (black prb)))"
                 using finite_RedBlack by auto
       
            moreover
            have "finite (pred (confs prb (root (red prb))))"
                 using finite_RedBlack finite_pred[OF assms]
                 by (auto simp add : vertices_def finite_RedBlack_def)
            
            moreover
            have "finite (pred (init_conf prb))"
                 using assms by (intro finite_init_pred)
       
            moreover
            have "\<forall>e\<in>pred (confs prb (root (red prb))). finite (Bexp.vars e)"
                 using finite_RedBlack finite_pred_constr_symvars[OF assms]
                 by (fastforce simp add : finite_RedBlack_def vertices_def)
       
            moreover
                 have "\<forall>e\<in>pred (init_conf prb). finite (Bexp.vars e)"
                 using assms by (intro finite_init_pred_symvars)
       
            moreover
                 have "init_conf prb \<sqsubseteq> confs prb (root (red prb))"
                 using assms by (rule init_subsumed)
       
            ultimately
            show "feasible (confs prb (root (red prb))) (trace es (labelling (black prb)))" 
                 using 1(2) by (rule subsums_imp_feasible)
          qed
        qed
      
  thus ?case 
       using feasible_subpaths_preserved[OF assms, of "root (red prb)"]
       by (auto simp add : vertices_def)
qed

end
