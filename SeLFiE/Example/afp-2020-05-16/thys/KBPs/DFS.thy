(*  Title:      Presburger-Automata/DFS.thy
    Author:     Toshiaki Nishihara and Yasuhiko Minamide
    Author:     Stefan Berghofer and Alex Krauss, TU Muenchen, 2008-2009
    Author:     Peter Gammie (data refinement futz), 2010
*)

(*<*)
theory DFS
imports Main
begin
(*>*)

subsection\<open>Generic DFS\<close>

text\<open>

\label{sec:dfs}

We use a generic DFS to construct the transitions and action function
of the implementation of the JKBP. This theory is largely due to
Stefan Berghofer and Alex Krauss
\citep{DBLP:conf/tphol/BerghoferR09}. All proofs are elided as the
fine details of how we explore the state space are inessential to the
synthesis algorithm.

The DFS itself is defined in the standard tail-recursive way:

\<close>

partial_function (tailrec) gen_dfs where
  "gen_dfs succs ins memb S wl = (case wl of
     [] \<Rightarrow> S
   | (x # xs) \<Rightarrow>
       if memb x S then gen_dfs succs ins memb S xs
       else gen_dfs succs ins memb (ins x S) (succs x @ xs))"
(*<*)
lemma gen_dfs_simps[code, simp]:
  "gen_dfs succs ins memb S [] = S"
  "gen_dfs succs ins memb S (x # xs) =
    (if memb x S then gen_dfs succs ins memb S xs
     else gen_dfs succs ins memb (ins x S) (succs x @ xs))"
  by (simp_all add: gen_dfs.simps)
(*>*)

text_raw\<open>
\begin{figure}
\begin{isabellebody}%
\<close>
locale DFS =
  fixes succs :: "'a \<Rightarrow> 'a list"
  and isNode :: "'a \<Rightarrow> bool"
  and invariant :: "'b \<Rightarrow> bool"
  and ins :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
  and memb :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  and empt :: 'b
  and nodeAbs :: "'a \<Rightarrow> 'c"
  assumes ins_eq: "\<And>x y S. \<lbrakk> isNode x; isNode y; invariant S; \<not> memb y S \<rbrakk>
                       \<Longrightarrow> memb x (ins y S)
                       \<longleftrightarrow> ((nodeAbs x = nodeAbs y) \<or> memb x S)"
  and succs: "\<And>x y. \<lbrakk> isNode x; isNode y; nodeAbs x = nodeAbs y \<rbrakk>
                       \<Longrightarrow> nodeAbs ` set (succs x) = nodeAbs ` set (succs y)"
  and empt: "\<And>x. isNode x \<Longrightarrow> \<not> memb x empt"
  and succs_isNode: "\<And>x. isNode x \<Longrightarrow> list_all isNode (succs x)"
  and empt_invariant: "invariant empt"
  and ins_invariant: "\<And>x S. \<lbrakk> isNode x; invariant S; \<not> memb x S \<rbrakk>
                        \<Longrightarrow> invariant (ins x S)"
  and graph_finite: "finite (nodeAbs ` { x . isNode x})"
text_raw\<open>
\end{isabellebody}%
\begin{isamarkuptext}%
\caption{The \<open>DFS\<close> locale.}
\label{fig:kbps-theory-dfs-locale}
\end{isamarkuptext}%
\end{figure}
\<close>

text\<open>

The proofs are carried out in the locale of
Figure~\ref{fig:kbps-theory-dfs-locale}, which details our
requirements on the parameters for the DFS to behave as one would
expect. Intuitively we are traversing a graph defined by @{term
"succs"} from some initial work list @{term "wl"}, constructing an
object of type @{typ "'b"} as we go. The function @{term "ins"}
integrates the current node into this construction. The predicate
@{term "isNode"} is invariant over the set of states reachable from
the initial work list, and is respected by @{term "empt"} and @{term
"ins"}. We can also supply an invariant for the constructed object
(@{term "invariant"}). Inside the locale, @{term "dfs"} abbreviates
@{term "gen_dfs"} partially applied to the fixed parameters.

To support our data refinement
(\S\ref{sec:kbps-automata-synthesis-alg}) we also require that the
representation of nodes be adequate via the abstraction function
@{term "nodeAbs"}, which the transition relation @{term "succs"} and
visited predicate @{term "memb"} must respect. To ensure termination
it must be the case that there are only a finite number of states,
though there might be an infinity of representations.

We characterise the DFS traversal using the reflexive
transitive closure operator:

\<close>

definition (in DFS) reachable :: "'a set \<Rightarrow> 'a set" where
  "reachable xs \<equiv> {(x, y). y \<in> set (succs x)}\<^sup>* `` xs"
(*<*)

context DFS
begin

definition
  "succss xs \<equiv> \<Union>x\<in>xs. set (succs x)"

definition
  "set_of S \<equiv> {x. isNode x \<and> memb x S}"

abbreviation
  "dfs \<equiv> gen_dfs succs ins memb"

definition rel where
  "rel = inv_image finite_psubset (\<lambda>S. nodeAbs ` {n.  isNode n \<and> \<not> memb n S})"

(* Yuck, something to do with Skolems broke. *)
lemma nodeAbs_subset_grot:
  "\<lbrakk>invariant S; isNode x; list_all isNode xs; \<not>memb x S\<rbrakk>
     \<Longrightarrow> nodeAbs ` {n . isNode n \<and> \<not> memb n (ins x S)}
       \<subset> nodeAbs ` {n . isNode n \<and> \<not> memb n S}"
  apply rule
   apply (auto simp add: ins_eq cong: conj_cong)
  apply (subgoal_tac "nodeAbs x \<in> nodeAbs ` {n. isNode n \<and> \<not> memb n S}")
   apply (subgoal_tac "nodeAbs x \<notin> nodeAbs ` {n. isNode n \<and> nodeAbs n \<noteq> nodeAbs x \<and> \<not> memb n S}")
    apply blast
   apply rule
   apply (erule imageE) back
   apply auto[1]
  apply auto[1]
  done

lemma psubsetI2: "\<lbrakk> A \<subseteq> B; x \<in> A; x \<notin> B\<rbrakk> \<Longrightarrow> A \<subset> B"
  by (unfold less_le) blast

lemma dfs_induct[consumes 2, case_names base step]:
  assumes S: "invariant S"
  and xs: "list_all isNode xs"
  and I1: "\<And>S. invariant S \<Longrightarrow> P S []"
  and I2: "\<And>S x xs. invariant S \<Longrightarrow> isNode x \<Longrightarrow> list_all isNode xs \<Longrightarrow>
    (memb x S \<Longrightarrow> P S xs) \<Longrightarrow> (\<not> memb x S \<Longrightarrow> P (ins x S) (succs x @ xs)) \<Longrightarrow> P S (x # xs)"
  shows "P S xs" using I1 I2 S xs
  apply induction_schema
  apply atomize_elim
  apply (case_tac xs, simp+)
  apply atomize_elim
  apply (rule conjI)
  apply (rule ins_invariant, assumption+)
  apply (rule succs_isNode, assumption)
  apply (relation "rel <*lex*> measure length")
  apply (simp add: wf_lex_prod rel_def)
  apply simp
  apply simp
  apply (rule disjI1)
  apply (simp add: rel_def finite_psubset_def)
  apply (rule conjI)
  apply (erule (3) nodeAbs_subset_grot)
  apply (rule finite_subset[OF _ graph_finite])
  apply auto
  done

lemma visit_subset_dfs: "invariant S \<Longrightarrow> list_all isNode xs \<Longrightarrow>
  isNode y \<Longrightarrow> memb y S \<Longrightarrow> memb y (dfs S xs)"
  by (induct S xs rule: dfs_induct) (simp_all add: ins_eq)

lemma next_subset_dfs: "invariant S \<Longrightarrow> list_all isNode xs \<Longrightarrow>
  x \<in> set xs \<Longrightarrow> memb x (dfs S xs)"
proof (induct S xs rule: dfs_induct)
  case (step S y xs)
  then show ?case
    by (auto simp add: visit_subset_dfs ins_eq ins_invariant succs_isNode)
qed simp

lemma succss_closed_dfs':
  "invariant ys \<Longrightarrow> list_all isNode xs \<Longrightarrow>
   nodeAbs ` succss (set_of ys) \<subseteq> nodeAbs ` (set xs \<union> set_of ys) \<Longrightarrow> nodeAbs ` succss (set_of (dfs ys xs)) \<subseteq> nodeAbs ` set_of (dfs ys xs)"
proof(induct ys xs rule: dfs_induct)
  case (base S) thus ?case by simp
next
  case (step S x xs) thus ?case
    apply (auto simp add: succss_def set_of_def cong: conj_cong)
     apply (subgoal_tac "nodeAbs xa \<in> nodeAbs ` (\<Union>x\<in>{x. isNode x \<and> memb x (dfs S xs)}. set (succs x))")
      apply blast
     apply blast
    apply (subgoal_tac "nodeAbs ` (\<Union>x\<in>{xa. isNode xa \<and> memb xa (ins x S)}. set (succs x)) \<subseteq> nodeAbs ` (set (succs x) \<union> set xs \<union> {xa. isNode xa \<and> memb xa (ins x S)})")
     apply blast
    apply (auto simp add: ins_eq succss_def set_of_def cong: conj_cong)
    apply (subgoal_tac "\<exists>xc'. xc' \<in> set (succs x) \<and> nodeAbs xc' = nodeAbs xc")
     apply clarsimp
     apply (rule_tac x=xc' in image_eqI)
      apply simp
     apply simp
    apply (cut_tac x=xd and y=x in succs)
     apply simp_all
    apply (subgoal_tac "nodeAbs xc \<in> nodeAbs ` set (succs x)")
     apply auto[1]
    apply auto[1]
   apply (subgoal_tac "nodeAbs ` set (succs xd) \<subseteq> nodeAbs ` (\<Union>x\<in>{x. isNode x \<and> memb x S}. set (succs x))")
    defer
    apply auto[1]
   apply (subgoal_tac "nodeAbs xc \<in> nodeAbs ` set (succs xd)")
    defer
    apply auto[1]
   apply (subgoal_tac "nodeAbs xc \<in> insert (nodeAbs x) (nodeAbs ` (set xs \<union> {x. isNode x \<and> memb x S}))")
    defer
    apply (erule rev_subsetD)
    apply (erule subset_trans)
    apply blast
   apply auto
   done
qed

lemma succss_closed_dfs: "list_all isNode xs \<Longrightarrow>
  nodeAbs ` succss (set_of (dfs empt xs)) \<subseteq> nodeAbs ` set_of (dfs empt xs)"
  apply (rule succss_closed_dfs')
  apply (rule empt_invariant)
  apply assumption
  apply (simp add: succss_def)
  apply (rule subsetI)
  apply clarsimp
  unfolding set_of_def
  using empt
  apply clarsimp
  done

definition
  "succsr \<equiv> {(x, y). y \<in> set (succs x)}"

theorem succsr_isNode:
  assumes xy: "(x, y) \<in> succsr\<^sup>*"
  shows "isNode x \<Longrightarrow> isNode y" using xy
proof induct
  case (step y z)
  then have "isNode y" by simp
  then have "list_all isNode (succs y)"
    by (rule succs_isNode)
  with step show ?case
    by (simp add: succsr_def list_all_iff)
qed

lemma succss_closed:
  assumes inc: "nodeAbs ` succss X \<subseteq> nodeAbs ` X"
      and X: "X \<subseteq> { x . isNode x }"
  shows "nodeAbs ` reachable X = nodeAbs ` X"
proof
  show "nodeAbs ` X \<subseteq> nodeAbs ` reachable X"
    unfolding reachable_def by auto
next
  show "nodeAbs ` reachable X \<subseteq> nodeAbs ` X"
  proof(unfold reachable_def, auto)
    fix x y
    assume y: "y \<in> X"
    assume "(y, x) \<in> {(x, y). y \<in> set (succs x)}\<^sup>*"
    thus "nodeAbs x \<in> nodeAbs ` X" using y
    proof induct
      case base thus ?case by simp
    next
      case (step r s)
      from X step have "isNode r"
        using succsr_isNode[where x=y and y=r]
        unfolding succsr_def by fastforce
      with inc step show ?case
        apply clarsimp
        apply (subgoal_tac "isNode x")
         apply (cut_tac x=r and y=x in succs)
         apply auto
         apply (subgoal_tac "nodeAbs s \<in> nodeAbs ` set (succs x)")
         using X
         apply (auto simp: succss_def)
         done
     qed
   qed
qed

lemma dfs_isNode:
  assumes S: "invariant S"
      and xs: "list_all isNode xs"
  shows "set_of (dfs S xs) \<subseteq> {x . isNode x}"
  using assms
  by (induct S xs rule: dfs_induct) (auto simp: set_of_def)

lemma reachable_closed_dfs:
  assumes xs: "list_all isNode xs"
  shows "nodeAbs ` reachable (set xs) \<subseteq> nodeAbs ` set_of (dfs empt xs)"
proof -
  from xs have "reachable (set xs) \<subseteq> reachable (set_of (dfs empt xs))"
    apply (unfold reachable_def)
    apply (rule Image_mono)
    apply (auto simp add: set_of_def next_subset_dfs empt_invariant list_all_iff)
    done
  hence "nodeAbs ` reachable (set xs) \<subseteq> nodeAbs ` reachable (set_of (dfs empt xs))"
    by auto
  also from succss_closed_dfs[OF xs] have "\<dots> = nodeAbs ` set_of (dfs empt xs)"
    apply (rule succss_closed)
    apply (rule dfs_isNode[OF empt_invariant xs])
    done
  finally show ?thesis .
qed

lemma reachable_succs: "reachable (set (succs x)) \<subseteq> reachable {x}"
  by (auto simp add: reachable_def intro: converse_rtrancl_into_rtrancl)

lemma dfs_subset_reachable_visit_nodes:
  "invariant ys \<Longrightarrow> list_all isNode xs \<Longrightarrow>
   nodeAbs ` set_of (dfs ys xs) \<subseteq> nodeAbs ` (reachable (set xs) \<union> set_of ys)"
proof(induct ys xs rule: dfs_induct)
  case (step S x xs)
  show ?case
  proof (cases "memb x S")
    case True
    with step show ?thesis by (auto simp add: reachable_def)
  next
    case False
    have "reachable (set (succs x)) \<subseteq> reachable {x}"
      by (rule reachable_succs)
    then have "reachable (set (succs x @ xs)) \<subseteq> reachable (set (x # xs))"
      by (auto simp add: reachable_def)
    then show ?thesis using step
      apply (auto simp add: reachable_def set_of_def cong: conj_cong)
       apply (subgoal_tac "nodeAbs xa \<in> nodeAbs `
            ({(x, y). y \<in> set (succs x)}\<^sup>* `` set xs \<union>
             {x. isNode x \<and> memb x S})")
        apply auto[1]
       apply auto[1]
      apply (subgoal_tac "nodeAbs xa \<in> nodeAbs `
            ({(x, y). y \<in> set (succs x)}\<^sup>* `` (set (succs x) \<union> set xs) \<union>
             {xa. isNode xa \<and> memb xa (ins x S)})")
       defer
       apply auto[1]
      apply auto[1]
       apply (rule_tac x=xb in image_eqI)
        apply auto[1]
       apply auto[1]
      apply (auto iff: ins_eq)
      done
(* by (auto simp add: reachable_def ins_eq set_of_def cong: conj_cong) *)
  qed
qed (simp add: reachable_def)

theorem dfs_imp_reachable:
  assumes y: "isNode y"
      and xs: "list_all isNode xs"
      and m: "memb y (dfs empt xs)"
  shows "\<exists>y'. nodeAbs y' = nodeAbs y \<and> y' \<in> reachable (set xs)"
proof -
  from m dfs_subset_reachable_visit_nodes [OF empt_invariant xs] y
  obtain y'
    where "nodeAbs y' = nodeAbs y"
      and "y' \<in> reachable (set xs)"
    by (auto simp add: empt set_of_def)
  thus ?thesis by blast
qed

(*>*)
text\<open>

We make use of two results about the traversal. Firstly, that some
representation of each reachable node has been incorporated into the
final construction:

\<close>

theorem (in DFS) reachable_imp_dfs:
  assumes y: "isNode y"
      and xs: "list_all isNode xs"
      and m: "y \<in> reachable (set xs)"
  shows "\<exists>y'. nodeAbs y' = nodeAbs y \<and> memb y' (dfs empt xs)"
(*<*)
  using y m reachable_closed_dfs[OF xs]
  apply (auto simp add: set_of_def)
  apply (drule subsetD[where c="nodeAbs y"])
   apply simp
  apply auto
  done

theorem dfs_invariant' [consumes 2, case_names base step]:
  assumes S: "invariant S"
  and xs: "list_all isNode xs"
  and H: "I S"
  and I: "\<And>S x. \<not> memb x S \<Longrightarrow> isNode x \<Longrightarrow> invariant S \<Longrightarrow> I S \<Longrightarrow> I (ins x S)"
  shows "I (dfs S xs)"
proof -
  from S xs H
  have "I (dfs S xs) \<and> invariant (dfs S xs)"
  proof (induct S xs rule: dfs_induct)
    case (step S x xs)
    show ?case
    proof (cases "memb x S")
      case False
      then show ?thesis
        apply simp
        apply (rule step)
        apply assumption
        apply (rule I)
        apply assumption
        apply (rule step)+
        done
    qed (simp add: step)
  qed simp
  then show ?thesis ..
qed

end (* context DFS *)
(*>*)

text\<open>

Secondly, that if an invariant holds on the initial object then it
holds on the final one:

\<close>

theorem (in DFS) dfs_invariant:
  assumes "invariant S"
  assumes "list_all isNode xs"
  shows "invariant (dfs S xs)"
(*<*)
  using assms
  by (induct S xs rule: dfs_induct) auto
(*>*)

text\<open>

\FloatBarrier

\<close>

(*<*)
end
(*>*)
