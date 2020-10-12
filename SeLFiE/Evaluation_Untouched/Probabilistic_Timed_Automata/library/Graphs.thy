(* Author: Simon Wimmer *)
theory Graphs
  imports
    More_List Stream_More
    "HOL-Library.Rewrite"
    Instantiate_Existentials
begin

section \<open>Graphs\<close>

subsection \<open>Basic Definitions and Theorems\<close>

locale Graph_Defs =
  fixes E :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

inductive steps where
  Single: "steps [x]" |
  Cons: "steps (x # y # xs)" if "E x y" "steps (y # xs)"

lemmas [intro] = steps.intros

lemma steps_append:
  "steps (xs @ tl ys)" if "steps xs" "steps ys" "last xs = hd ys"
  using that by induction (auto 4 4 elim: steps.cases)

lemma steps_append':
  "steps xs" if "steps as" "steps bs" "last as = hd bs" "as @ tl bs = xs"
  using steps_append that by blast

coinductive run where
  "run (x ## y ## xs)" if "E x y" "run (y ## xs)"

lemmas [intro] = run.intros

lemma steps_appendD1:
  "steps xs" if "steps (xs @ ys)" "xs \<noteq> []"
  using that proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by - (cases xs; auto elim: steps.cases)
qed

lemma steps_appendD2:
  "steps ys" if "steps (xs @ ys)" "ys \<noteq> []"
  using that by (induction xs) (auto elim: steps.cases)

lemma steps_appendD3:
  "steps (xs @ [x]) \<and> E x y" if "steps (xs @ [x, y])"
  using that proof (induction xs)
  case Nil
  then show ?case by (auto elim!: steps.cases)
next
  case prems: (Cons a xs)
  then show ?case by (cases xs) (auto elim: steps.cases)
qed

lemma steps_ConsD:
  "steps xs" if "steps (x # xs)" "xs \<noteq> []"
  using that by (auto elim: steps.cases)

lemmas stepsD = steps_ConsD steps_appendD1 steps_appendD2

lemma steps_alt_induct[consumes 1, case_names Single Snoc]:
  assumes
    "steps x" "(\<And>x. P [x])"
    "\<And>y x xs. E y x \<Longrightarrow> steps (xs @ [y]) \<Longrightarrow> P (xs @ [y]) \<Longrightarrow> P (xs @ [y,x])"
  shows "P x"
  using assms(1)
  proof (induction rule: rev_induct)
    case Nil
    then show ?case by (auto elim: steps.cases)
  next
    case prems: (snoc x xs)
    then show ?case by (cases xs rule: rev_cases) (auto intro: assms(2,3) dest!: steps_appendD3)
  qed

lemma steps_appendI:
  "steps (xs @ [x, y])" if "steps (xs @ [x])" "E x y"
  using that
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by (cases xs; auto elim: steps.cases)
qed

lemma steps_append_single:
  assumes
    "steps xs" "E (last xs) x" "xs \<noteq> []"
  shows "steps (xs @ [x])"
  using assms(3,1,2) by (induction xs rule: list_nonempty_induct) (auto 4 4 elim: steps.cases)

lemma extend_run:
  assumes
    "steps xs" "E (last xs) x" "run (x ## ys)" "xs \<noteq> []"
  shows "run (xs @- x ## ys)"
  using assms(4,1-3) by (induction xs rule: list_nonempty_induct) (auto 4 3 elim: steps.cases)

lemma run_cycle:
  assumes "steps xs" "E (last xs) (hd xs)" "xs \<noteq> []"
  shows "run (cycle xs)"
  using assms proof (coinduction arbitrary: xs)
  case run
  then show ?case
    apply (rewrite at \<open>cycle xs\<close> stream.collapse[symmetric])
    apply (rewrite at \<open>stl (cycle xs)\<close> stream.collapse[symmetric])
    apply clarsimp
    apply (erule steps.cases)
    subgoal for x
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials xs)
         apply (simp, metis cycle_Cons[of x "[]", simplified])
      by auto
    subgoal for x y xs'
      apply (rule conjI)
       apply (simp; fail)
      apply (rule disjI1)
      apply (inst_existentials "y # xs' @ [x]")
      using steps_append_single[of "y # xs'" x]
         apply (auto elim: steps.cases split: if_split_asm)
       apply (subst (2) cycle_Cons, simp) (* XXX Automate forward reasoning *)
      apply (subst cycle_Cons, simp)
      done
    done
qed

lemma run_stl:
  "run (stl xs)" if "run xs"
  using that by (auto elim: run.cases)

lemma run_sdrop:
  "run (sdrop n xs)" if "run xs"
  using that by (induction n arbitrary: xs) (auto intro: run_stl)

lemma run_reachable':
  assumes "run (x ## xs)" "E\<^sup>*\<^sup>* x\<^sub>0 x"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  using assms by (coinduction arbitrary: x xs) (auto 4 3 elim: run.cases)

lemma run_reachable:
  assumes "run (x\<^sub>0 ## xs)"
  shows "pred_stream (\<lambda> x. E\<^sup>*\<^sup>* x\<^sub>0 x) xs"
  by (rule run_reachable'[OF assms]) blast

lemma run_decomp:
  assumes "run (xs @- ys)" "xs \<noteq> []"
  shows "steps xs \<and> run ys \<and> E (last xs) (shd ys)"
using assms(2,1) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: run.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: run.cases)
qed

lemma steps_decomp:
  assumes "steps (xs @ ys)" "xs \<noteq> []" "ys \<noteq> []"
  shows "steps xs \<and> steps ys \<and> E (last xs) (hd ys)"
using assms(2,1,3) proof (induction xs rule: list_nonempty_induct)
  case (single x)
  then show ?case by (auto elim: steps.cases)
next
  case (cons x xs)
  then show ?case by (cases xs; auto 4 4 elim: steps.cases)
qed

lemma steps_rotate:
  assumes "steps (x # xs @ y # ys @ [x])"
  shows "steps (y # ys @ x # xs @ [y])"
proof -
  from steps_decomp[of "x # xs" "y # ys @ [x]"] assms have
    "steps (x # xs)" "steps (y # ys @ [x])" "E (last (x # xs)) y"
    by auto
  then have "steps ((x # xs) @ [y])" by (blast intro: steps_append_single)
  from steps_append[OF \<open>steps (y # ys @ [x])\<close> this] show ?thesis by auto
qed

lemma run_shift_coinduct[case_names run_shift, consumes 1]:
  assumes "R w"
      and "\<And> w. R w \<Longrightarrow> \<exists> u v x y. w = u @- x ## y ## v \<and> steps (u @ [x]) \<and> E x y \<and> R (y ## v)"
  shows "run w"
  using assms(2)[OF \<open>R w\<close>] proof (coinduction arbitrary: w)
  case (run w)
  then obtain u v x y where "w = u @- x ## y ## v" "steps (u @ [x])" "E x y" "R (y ## v)"
    by auto
  then show ?case
    apply -
    apply (drule assms(2))
    apply (cases u)
     apply force
    subgoal for z zs
      apply (cases zs)
      subgoal
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          by (inst_existentials "x # u'") (cases u'; auto)
        done
      subgoal for a as
        apply simp
        apply safe
         apply (force elim: steps.cases)
        subgoal for u' v' x' y'
          apply (inst_existentials "a # as @ x # u'")
          using steps_append[of "a # as @ [x, y]" "u' @ [x']"]
          apply simp
          apply (drule steps_appendI[of "a # as" x, rotated])
          by (cases u'; force elim: steps.cases)+
        done
      done
    done
qed

lemma run_flat_coinduct[case_names run_shift, consumes 1]:
  assumes "R xss"
    and
    "\<And> xs ys xss.
    R (xs ## ys ## xss) \<Longrightarrow> xs \<noteq> [] \<and> steps xs \<and> E (last xs) (hd ys) \<and> R (ys ## xss)"
  shows "run (flat xss)"
proof -
  obtain xs ys xss' where "xss = xs ## ys ## xss'" by (metis stream.collapse)
  with assms(2)[OF assms(1)[unfolded this]] show ?thesis
  proof (coinduction arbitrary: xs ys xss' xss rule: run_shift_coinduct)
    case (run_shift xs ys xss' xss)
    from run_shift show ?case
      apply (cases xss')
      apply clarify
      apply (drule assms(2))
      apply (inst_existentials "butlast xs" "tl ys @- flat xss'" "last xs" "hd ys")
         apply (cases ys)
          apply (simp; fail)
      subgoal premises prems for x1 x2 z zs
      proof (cases "xs = []")
        case True
        with prems show ?thesis
          by auto
      next
        case False
        then have "xs = butlast xs @ [last xs]" by auto
        then have "butlast xs @- last xs ## tail = xs @- tail" for tail
          by (metis shift.simps(1,2) shift_append)
        with prems show ?thesis by simp
      qed
        apply (simp; fail)
       apply assumption
      subgoal for ws wss
        by (inst_existentials ys ws wss) (cases ys, auto)
      done
  qed
qed

lemma steps_non_empty[simp]:
  "\<not> steps []"
  by (auto elim: steps.cases)

lemma steps_non_empty'[simp]:
  "xs \<noteq> []" if "steps xs"
  using that by auto

(* XXX Generalize *)
lemma steps_replicate:
  "steps (hd xs # concat (replicate n (tl xs)))" if "last xs = hd xs" "steps xs" "n > 0"
  using that
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases n)
    case 0
    with Suc.prems show ?thesis by (cases xs; auto)
  next
    case prems: (Suc nat)
    from Suc.prems have [simp]: "hd xs # tl xs @ ys = xs @ ys" for ys
      by (cases xs; auto)
    from Suc.prems have **: "tl xs @ ys = tl (xs @ ys)" for ys
      by (cases xs; auto)
    from prems Suc show ?thesis
      by (fastforce intro: steps_append')
  qed
qed

notation E ("_ \<rightarrow> _" [100, 100] 40)

abbreviation reaches ("_ \<rightarrow>* _" [100, 100] 40) where "reaches x y \<equiv> E\<^sup>*\<^sup>* x y"

abbreviation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40) where "reaches1 x y \<equiv> E\<^sup>+\<^sup>+ x y"

lemma steps_reaches:
  "hd xs \<rightarrow>* last xs" if "steps xs"
  using that by (induction xs) auto

lemma steps_reaches':
  "x \<rightarrow>* y" if "steps xs" "hd xs = x" "last xs = y"
  using that steps_reaches by auto

lemma reaches_steps:
  "\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs" if "x \<rightarrow>* y"
  using that
  apply (induction)
   apply force
  apply clarsimp
  subgoal for z xs
    by (inst_existentials "xs @ [z]", (cases xs; simp), auto intro: steps_append_single)
  done

lemma reaches_steps_iff:
  "x \<rightarrow>* y \<longleftrightarrow> (\<exists> xs. hd xs = x \<and> last xs = y \<and> steps xs)"
  using steps_reaches reaches_steps by fast

lemma steps_reaches1:
  "x \<rightarrow>\<^sup>+ y" if "steps (x # xs @ [y])"
  by (metis list.sel(1,3) rtranclp_into_tranclp2 snoc_eq_iff_butlast steps.cases steps_reaches that)

lemma stepsI:
  "steps (x # xs)" if "x \<rightarrow> hd xs" "steps xs"
  using that by (cases xs) auto

lemma reaches1_steps:
  "\<exists> xs. steps (x # xs @ [y])" if "x \<rightarrow>\<^sup>+ y"
proof -
  from that obtain z where "x \<rightarrow> z" "z \<rightarrow>* y"
    by atomize_elim (simp add: tranclpD)
  from reaches_steps[OF this(2)] obtain xs where *: "hd xs = z" "last xs = y" "steps xs"
    by auto
  then obtain xs' where [simp]: "xs = xs' @ [y]"
    by atomize_elim (auto 4 3 intro: append_butlast_last_id[symmetric])
  with \<open>x \<rightarrow> z\<close> * show ?thesis
    by (auto intro: stepsI)
qed

lemma reaches1_steps_iff:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> xs. steps (x # xs @ [y]))"
  using steps_reaches1 reaches1_steps by fast

lemma reaches1_reaches_iff1:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow> z \<and> z \<rightarrow>* y)"
  by (auto dest: tranclpD)

lemma reaches1_reaches_iff2:
  "x \<rightarrow>\<^sup>+ y \<longleftrightarrow> (\<exists> z. x \<rightarrow>* z \<and> z \<rightarrow> y)"
  apply safe
   apply (metis Nitpick.rtranclp_unfold tranclp.cases)
  by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>* y" "y \<rightarrow>\<^sup>+ z"
  using that by auto

lemma
  "x \<rightarrow>\<^sup>+ z" if "x \<rightarrow>\<^sup>+ y" "y \<rightarrow>* z"
  using that by auto

lemma steps_append2:
  "steps (xs @ x # ys)" if "steps (xs @ [x])" "steps (x # ys)"
  using that by (auto dest: steps_append)

lemma reaches1_steps_append:
  assumes "a \<rightarrow>\<^sup>+ b" "steps xs" "hd xs = b"
  shows "\<exists> ys. steps (a # ys @ xs)"
  using assms by (fastforce intro: steps_append' dest: reaches1_steps)

lemma steps_last_step:
  "\<exists> a. a \<rightarrow> last xs" if "steps xs" "length xs > 1"
  using that by induction auto

lemmas graphI =
  steps.intros
  steps_append_single
  steps_reaches'
  stepsI

end (* Graph Defs *)


subsection \<open>Graphs with a Start Node\<close>

locale Graph_Start_Defs = Graph_Defs +
  fixes s\<^sub>0 :: 'a
begin

definition reachable where
  "reachable = E\<^sup>*\<^sup>* s\<^sub>0"

lemma start_reachable[intro!, simp]:
  "reachable s\<^sub>0"
  unfolding reachable_def by auto

lemma reachable_step:
  "reachable b" if "reachable a" "E a b"
  using that unfolding reachable_def by auto

lemma reachable_reaches:
  "reachable b" if "reachable a" "a \<rightarrow>* b"
  using that(2,1) by induction (auto intro: reachable_step)

lemma reachable_steps_append:
  assumes "reachable a" "steps xs" "hd xs = a" "last xs = b"
  shows "reachable b"
  using assms by (auto intro: graphI reachable_reaches)

lemmas steps_reachable = reachable_steps_append[of s\<^sub>0, simplified]

lemma reachable_steps_elem:
  "reachable y" if "reachable x" "steps xs" "y \<in> set xs" "hd xs = x"
proof -
  from \<open>y \<in> set xs\<close> obtain as bs where [simp]: "xs = as @ y # bs"
    by (auto simp: in_set_conv_decomp)
  show ?thesis
  proof (cases "as = []")
    case True
    with that show ?thesis
      by simp
  next
    case False
    (* XXX *)
    from \<open>steps xs\<close> have "steps (as @ [y])"
      by (auto intro: stepsD)
    with \<open>as \<noteq> []\<close> \<open>hd xs = x\<close> \<open>reachable x\<close> show ?thesis
      by (auto 4 3 intro: reachable_reaches graphI)
  qed
qed

lemma reachable_steps:
  "\<exists> xs. steps xs \<and> hd xs = s\<^sub>0 \<and> last xs = x" if "reachable x"
  using that unfolding reachable_def
proof induction
  case base
  then show ?case by (inst_existentials "[s\<^sub>0]"; force)
next
  case (step y z)
  from step.IH guess xs by clarify
  with step.hyps show ?case
    apply (inst_existentials "xs @ [z]")
    apply (force intro: graphI)
    by (cases xs; auto)+
qed

lemma reachable_cycle_iff:
  "reachable x \<and> x \<rightarrow>\<^sup>+ x \<longleftrightarrow> (\<exists> ws xs. steps (s\<^sub>0 # ws @ [x] @ xs @ [x]))"
proof (safe, goal_cases)
  case (2 ws)
  then show ?case
    by (auto intro: steps_reachable stepsD)
next
  case (3 ws xs)
  then show ?case
    by (auto intro: stepsD steps_reaches1)
next
  case prems: 1
  from \<open>reachable x\<close> prems(2) have "s\<^sub>0 \<rightarrow>\<^sup>+ x"
    unfolding reachable_def by auto
  with \<open>x \<rightarrow>\<^sup>+ x\<close> show ?case
    by (fastforce intro: steps_append' dest: reaches1_steps)
qed

lemma reachable_induct[consumes 1, case_names start step, induct pred: reachable]:
  assumes "reachable x"
    and "P s\<^sub>0"
    and "\<And> a b. reachable a \<Longrightarrow> P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
  shows "P x"
  using assms(1) unfolding reachable_def
  by induction (auto intro: assms(2-)[unfolded reachable_def])

lemmas graphI_aggressive =
  tranclp_into_rtranclp
  rtranclp.rtrancl_into_rtrancl
  tranclp.trancl_into_trancl
  rtranclp_into_tranclp2

lemmas graphI_aggressive1 =
  graphI_aggressive
  steps_append'

lemmas graphI_aggressive2 =
  graphI_aggressive
  stepsD
  steps_reaches1
  steps_reachable

lemmas graphD =
  reaches1_steps

lemmas graphD_aggressive =
  tranclpD

lemmas graph_startI =
  reachable_reaches
  start_reachable

end (* Graph Start Defs *)


subsection \<open>Subgraphs\<close>

subsubsection \<open>Edge-induced Subgraphs\<close>

locale Subgraph_Defs = G: Graph_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Defs E' .

end (* Subgraph Defs *)

locale Subgraph_Start_Defs = G: Graph_Start_Defs +
  fixes E' :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

sublocale G': Graph_Start_Defs E' s\<^sub>0 .

end (* Subgraph Start Defs *)

locale Subgraph = Subgraph_Defs +
  assumes subgraph[intro]: "E' a b \<Longrightarrow> E a b"
begin

lemma non_subgraph_cycle_decomp:
  "\<exists> c d. G.reaches a c \<and> E c d \<and> \<not> E' c d \<and> G.reaches d b" if
  "G.reaches1 a b" "\<not> G'.reaches1 a b" for a b
    using that
  proof induction
    case (base y)
    then show ?case
      by auto
  next
    case (step y z)
    show ?case
    proof (cases "E' y z")
      case True
      with step have "\<not> G'.reaches1 a y"
        by (auto intro: tranclp.trancl_into_trancl) (* XXX *)
      with step obtain c d where
        "G.reaches a c" "E c d" "\<not> E' c d" "G.reaches d y"
        by auto
      with \<open>E' y z\<close> show ?thesis
        by (blast intro: rtranclp.rtrancl_into_rtrancl) (* XXX *)
    next
      case False
      with step show ?thesis
        by (intro exI conjI) auto
    qed
  qed

lemma reaches:
  "G.reaches a b" if "G'.reaches a b"
  using that by induction (auto intro: rtranclp.intros(2))

lemma reaches1:
  "G.reaches1 a b" if "G'.reaches1 a b"
  using that by induction (auto intro: tranclp.intros(2))

end (* Subgraph *)

locale Subgraph_Start = Subgraph_Start_Defs + Subgraph
begin

lemma reachable_subgraph[intro]: "G.reachable b" if \<open>G.reachable a\<close> \<open>G'.reaches a b\<close> for a b
  using that by (auto intro: G.graph_startI mono_rtranclp[rule_format, of E'])

lemma reachable:
  "G.reachable x" if "G'.reachable x"
  using that by (fastforce simp: G.reachable_def G'.reachable_def)

end (* Subgraph Start *)

subsubsection \<open>Node-induced Subgraphs\<close>

locale Subgraph_Node_Defs = Graph_Defs +
  fixes V :: "'a \<Rightarrow> bool"
begin

definition E' where "E' x y \<equiv> E x y \<and> V x \<and> V y"

sublocale Subgraph E E' by standard (auto simp: E'_def)

lemma subgraph':
  "E' x y" if "E x y" "V x" "V y"
  using that unfolding E'_def by auto

lemma E'_V1:
  "V x" if "E' x y"
  using that unfolding E'_def by auto

lemma E'_V2:
  "V y" if "E' x y"
  using that unfolding E'_def by auto

lemma G'_reaches_V:
  "V y" if "G'.reaches x y" "V x"
  using that by (cases) (auto intro: E'_V2)

lemma G'_steps_V_all:
  "list_all V xs" if "G'.steps xs" "V (hd xs)"
  using that by induction (auto intro: E'_V2)

lemma G'_steps_V_last:
  "V (last xs)" if "G'.steps xs" "V (hd xs)"
  using that by induction (auto dest: E'_V2)

lemmas subgraphI = E'_V1 E'_V2 G'_reaches_V

lemmas subgraphD = E'_V1 E'_V2 G'_reaches_V

end (* Subgraph Node *)


locale Subgraph_Node_Defs_Notation = Subgraph_Node_Defs
begin

no_notation E ("_ \<rightarrow> _" [100, 100] 40)
notation E' ("_ \<rightarrow> _" [100, 100] 40)
no_notation reaches ("_ \<rightarrow>* _" [100, 100] 40)
notation G'.reaches ("_ \<rightarrow>* _" [100, 100] 40)
no_notation reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)
notation G'.reaches1 ("_ \<rightarrow>\<^sup>+ _" [100, 100] 40)

end (* Subgraph_Node_Defs_Notation *)


subsubsection \<open>The Reachable Subgraph\<close>

context Graph_Start_Defs
begin

interpretation Subgraph_Node_Defs_Notation E reachable .

sublocale reachable_subgraph: Subgraph_Node_Defs E reachable .

lemma reachable_supgraph:
  "x \<rightarrow> y" if "E x y" "reachable x"
  using that unfolding E'_def by (auto intro: graph_startI)

lemma reachable_reaches_equiv: "reaches x y \<longleftrightarrow> x \<rightarrow>* y" if "reachable x" for x y
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: reachable_supgraph intro: graph_startI graphI_aggressive)
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: subgraph)
  done

lemma reachable_reaches1_equiv: "reaches1 x y \<longleftrightarrow> x \<rightarrow>\<^sup>+ y" if "reachable x" for x y
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: reachable_supgraph intro: graph_startI graphI_aggressive)
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by induction (auto dest: subgraph)
  done

lemma reachable_steps_equiv:
  "steps (x # xs) \<longleftrightarrow> G'.steps (x # xs)" if "reachable x"
  apply standard
  subgoal premises prems
    using prems \<open>reachable x\<close>
    by (induction "x # xs" arbitrary: x xs) (auto dest: reachable_supgraph intro: graph_startI)
  subgoal premises prems
    using prems by induction auto
  done

end (* Graph Start Defs *)


subsection \<open>Bundles\<close>

bundle graph_automation
begin

lemmas [intro] = Graph_Defs.graphI Graph_Start_Defs.graph_startI
lemmas [dest]  = Graph_Start_Defs.graphD

end (* Bundle *)

bundle reaches_steps_iff =
  Graph_Defs.reaches1_steps_iff [iff]
  Graph_Defs.reaches_steps_iff  [iff]

bundle graph_automation_aggressive
begin

unbundle graph_automation

lemmas [intro] = Graph_Start_Defs.graphI_aggressive
lemmas [dest]  = Graph_Start_Defs.graphD_aggressive

end (* Bundle *)

bundle subgraph_automation
begin

unbundle graph_automation

lemmas [intro] = Subgraph_Node_Defs.subgraphI
lemmas [dest]  = Subgraph_Node_Defs.subgraphD

end (* Bundle *)


subsection \<open>Simulations and Bisimulations\<close>

locale Graph_Invariant = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> P b"
begin

lemma invariant_steps:
  "list_all P as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma invariant_reaches:
  "P b" if "a \<rightarrow>* b" "P a"
  using that by (induction; blast intro: invariant)

lemma invariant_run:
  assumes run: "run (x ## xs)" and P: "P x"
  shows "pred_stream P (x ## xs)"
  using run P by (coinduction arbitrary: x xs) (auto 4 3 elim: invariant run.cases)

end (* Graph Invariant *)

locale Graph_Invariants = Graph_Defs +
  fixes P Q :: "'a \<Rightarrow> bool"
  assumes invariant: "P a \<Longrightarrow> a \<rightarrow> b \<Longrightarrow> Q b" and Q_P: "Q a \<Longrightarrow> P a"
begin

sublocale Pre: Graph_Invariant E P
  by standard (blast intro: invariant Q_P)

sublocale Post: Graph_Invariant E Q
  by standard (blast intro: invariant Q_P)

lemma invariant_steps:
  "list_all Q as" if "steps (a # as)" "P a"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant Q_P)

lemma invariant_run:
  assumes run: "run (x ## xs)" and P: "P x"
  shows "pred_stream Q xs"
  using run P by (coinduction arbitrary: x xs) (auto 4 4 elim: invariant run.cases intro: Q_P)

lemma invariant_reaches1:
  "Q b" if "a \<rightarrow>\<^sup>+ b" "P a"
  using that by (induction; blast intro: invariant Q_P)

end (* Graph Invariants *)

locale Graph_Invariant_Start = Graph_Start_Defs + Graph_Invariant +
  assumes P_s\<^sub>0: "P s\<^sub>0"
begin

lemma invariant_steps:
  "list_all P as" if "steps (s\<^sub>0 # as)"
  using that P_s\<^sub>0 by (rule invariant_steps)

lemma invariant_reaches:
  "P b" if "s\<^sub>0 \<rightarrow>* b"
  using invariant_reaches[OF that P_s\<^sub>0] .

lemmas invariant_run = invariant_run[OF _ P_s\<^sub>0]

end (* Graph Invariant Start *)

locale Graph_Invariant_Strong = Graph_Defs +
  fixes P :: "'a \<Rightarrow> bool"
  assumes invariant: "a \<rightarrow> b \<Longrightarrow> P b"
begin

sublocale inv: Graph_Invariant by standard (rule invariant)

lemma P_invariant_steps:
  "list_all P as" if "steps (a # as)"
  using that by (induction "a # as" arbitrary: as a) (auto intro: invariant)

lemma steps_last_invariant:
  "P (last xs)" if "steps (x # xs)" "xs \<noteq> []"
  using steps_last_step[of "x # xs"] that by (auto intro: invariant)

lemmas invariant_reaches = inv.invariant_reaches

lemma invariant_reaches1:
  "P b" if "a \<rightarrow>\<^sup>+ b"
  using that by (induction; blast intro: invariant)

end (* Graph Invariant *)

locale Simulation_Defs =
  fixes A :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and B :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
    and sim :: "'a \<Rightarrow> 'b \<Rightarrow> bool" (infixr "\<sim>" 60)
begin

sublocale A: Graph_Defs A .

sublocale B: Graph_Defs B .

end (* Simulation Defs *)

locale Simulation = Simulation_Defs +
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
begin

lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b"
  using that by (induction rule: rtranclp_induct) (auto intro: rtranclp.intros(2) dest: A_B_step)

lemma simulation_reaches1:
  "\<exists> b'. B\<^sup>+\<^sup>+ b b' \<and> a' \<sim> b'" if "A\<^sup>+\<^sup>+ a a'" "a \<sim> b"
  using that by (induction rule: tranclp_induct) (auto 4 3 intro: tranclp.intros(2) dest: A_B_step)

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs" if "A.steps (a # as)" "a \<sim> b"
  using that
  apply (induction "a # as" arbitrary: a b as)
   apply force
  apply (frule A_B_step, auto)
  done

lemma simulation_run:
  "\<exists> ys. B.run (y ## ys) \<and> stream_all2 (\<sim>) xs ys" if "A.run (x ## xs)" "x \<sim> y"
proof -
  let ?ys = "sscan (\<lambda> a' b. SOME b'. B b b' \<and> a' \<sim> b') xs y"
  have "B.run (y ## ?ys)"
    using that by (coinduction arbitrary: x y xs) (force dest!: someI_ex A_B_step elim: A.run.cases)
  moreover have "stream_all2 (\<sim>) xs ?ys"
    using that by (coinduction arbitrary: x y xs) (force dest!: someI_ex A_B_step elim: A.run.cases)
  ultimately show ?thesis by blast
qed

end (* Simulation *)

lemma (in Subgraph) Subgraph_Simulation:
  "Simulation E' E (=)"
  by standard auto

locale Simulation_Invariant = Simulation_Defs +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> PB b"
begin

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale Simulation A B equiv' by standard (auto dest: A_B_step simp: equiv'_def)

sublocale PA_invariant: Graph_Invariant A PA by standard blast

lemma simulation_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b' \<and> PA a' \<and> PB b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b" "PA a" "PB b"
  using simulation_reaches[of a a' b] that unfolding equiv'_def by simp

lemma simulation_steps:
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b \<and> PA a \<and> PB b) as bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[of a as b] that unfolding equiv'_def by simp

lemma simulation_steps':
  "\<exists> bs. B.steps (b # bs) \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
  using simulation_steps[OF that]
  by (metis (mono_tags, lifting) list_all2_conv_all_nth list_all_length)

context
  fixes f
  assumes eq: "a \<sim> b \<Longrightarrow> b = f a"
begin

lemma simulation_steps'_map:
  "\<exists> bs.
    B.steps (b # bs) \<and> bs = map f as
    \<and> list_all2 (\<lambda> a b. a \<sim> b) as bs
    \<and> list_all PA as \<and> list_all PB bs"
  if "A.steps (a # as)" "a \<sim> b" "PA a" "PB b"
proof -
  from simulation_steps'[OF that] guess bs by clarify
  note guessed = this
  from this(2) have "bs = map f as"
    by (induction; simp add: eq)
  with guessed show ?thesis
    by auto
qed

end (* Context for Equality Relation *)

end (* Simulation Invariant *)

locale Simulation_Invariants = Simulation_Defs +
  fixes PA QA :: "'a \<Rightarrow> bool" and PB QB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> QA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> QB b"
  assumes PA_QA[intro]: "\<And> a. QA a \<Longrightarrow> PA a" and PB_QB[intro]: "\<And> a. QB a \<Longrightarrow> PB a"
begin

sublocale Pre: Simulation_Invariant A B "(\<sim>)" PA PB
  by standard (auto intro: A_B_step)

sublocale Post: Simulation_Invariant A B "(\<sim>)" QA QB
  by standard (auto intro: A_B_step)

sublocale A_invs: Graph_Invariants A PA QA
  by standard auto

sublocale B_invs: Graph_Invariants B PB QB
  by standard auto

lemma simulation_reaches1:
  "\<exists> b2. B.reaches1 b1 b2 \<and> a2 \<sim> b2 \<and> QB b2" if "A.reaches1 a1 a2" "a1 \<sim> b1" "PA a1" "PB b1"
  using that
  by - (drule Pre.simulation_reaches1, auto intro: B_invs.invariant_reaches1 simp: Pre.equiv'_def)

lemma reaches1_unique:
  assumes unique: "\<And> b2. a \<sim> b2 \<Longrightarrow> QB b2 \<Longrightarrow> b2 = b"
    and that: "A.reaches1 a a" "a \<sim> b" "PA a" "PB b"
  shows "B.reaches1 b b"
  using that by (auto dest: unique simulation_reaches1)

end (* Simualation Invariants *)

locale Bisimulation = Simulation_Defs +
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> a a' b'. B a' b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> (\<exists> b. A a b \<and> b \<sim> b')"
begin

sublocale A_B: Simulation A B "(\<sim>)" by standard (rule A_B_step)

sublocale B_A: Simulation B A "\<lambda> x y. y \<sim> x" by standard (rule B_A_step)

lemma A_B_reaches:
  "\<exists> b'. B\<^sup>*\<^sup>* b b' \<and> a' \<sim> b'" if "A\<^sup>*\<^sup>* a a'" "a \<sim> b"
  using A_B.simulation_reaches[OF that] .

lemma B_A_reaches:
  "\<exists> b'. A\<^sup>*\<^sup>* b b' \<and> b' \<sim> a'" if "B\<^sup>*\<^sup>* a a'" "b \<sim> a"
  using B_A.simulation_reaches[OF that] .

end (* Bisim *)

locale Bisimulation_Invariant = Simulation_Defs +
  fixes PA :: "'a \<Rightarrow> bool" and PB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> a a' b'. B a' b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b. A a b \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> PA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> PB b"
begin

sublocale PA_invariant: Graph_Invariant A PA by standard blast

sublocale PB_invariant: Graph_Invariant B PB by standard blast

lemmas B_steps_invariant[intro] = PB_invariant.invariant_reaches

definition "equiv' \<equiv> \<lambda> a b. a \<sim> b \<and> PA a \<and> PB b"

sublocale bisim: Bisimulation A B equiv'
  by standard (clarsimp simp add: equiv'_def, frule A_B_step B_A_step, assumption; auto)+

sublocale A_B: Simulation_Invariant A B "(\<sim>)" PA PB
  by (standard; blast intro: A_B_step B_A_step)

sublocale B_A: Simulation_Invariant B A "\<lambda> x y. y \<sim> x" PB PA
  by (standard; blast intro: A_B_step B_A_step)

context
  fixes f
  assumes eq: "a \<sim> b \<longleftrightarrow> b = f a"
    and inj: "\<forall> a b. PB (f a) \<and> PA b \<and> f a = f b \<longrightarrow> a = b"
begin

lemma list_all2_inj_map_eq:
  "as = bs" if "list_all2 (\<lambda>a b. a = f b) (map f as) bs" "list_all PB (map f as)" "list_all PA bs"
  using that inj
  by (induction "map f as" bs arbitrary: as rule: list_all2_induct) (auto simp: inj_on_def)

lemma steps_map_equiv:
  "A.steps (a # as) \<longleftrightarrow> B.steps (b # map f as)" if "a \<sim> b" "PA a" "PB b"
  using A_B.simulation_steps'_map[of f a as b] B_A.simulation_steps'[of b "map f as" a] that eq
  by (auto dest: list_all2_inj_map_eq)

lemma steps_map:
  "\<exists> as. bs = map f as" if "B.steps (f a # bs)" "PA a" "PB (f a)"
proof -
  have "a \<sim> f a" unfolding eq ..
  from B_A.simulation_steps'[OF that(1) this \<open>PB _\<close> \<open>PA _\<close>] guess as by clarify
  from this(2) show ?thesis
    unfolding eq by (inst_existentials as, induction rule: list_all2_induct, auto)
qed

lemma reaches_equiv:
  "A.reaches a a' \<longleftrightarrow> B.reaches (f a) (f a')" if "PA a" "PB (f a)"
  apply safe
   apply (drule A_B.simulation_reaches[of a a' "f a"]; simp add: eq that)
  apply (drule B_A.simulation_reaches)
     defer
     apply (rule that | clarsimp simp: eq | metis inj)+
  done

end (* Context for Equality Relation *)

lemma equiv'_D:
  "a \<sim> b" if "A_B.equiv' a b"
  using that unfolding A_B.equiv'_def by auto

lemma equiv'_rotate_1:
  "B_A.equiv' b a" if "A_B.equiv' a b"
  using that by (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma equiv'_rotate_2:
  "A_B.equiv' a b" if "B_A.equiv' b a"
  using that by (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma stream_all2_equiv'_D:
  "stream_all2 (\<sim>) xs ys" if "stream_all2 A_B.equiv' xs ys"
  using stream_all2_weaken[OF that equiv'_D] by fast

lemma stream_all2_equiv'_D2:
  "stream_all2 B_A.equiv' ys xs \<Longrightarrow> stream_all2 (\<sim>)\<inverse>\<inverse> ys xs"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def)

lemma stream_all2_rotate_1:
  "stream_all2 B_A.equiv' ys xs \<Longrightarrow> stream_all2 A_B.equiv' xs ys"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def A_B.equiv'_def)

lemma stream_all2_rotate_2:
  "stream_all2 A_B.equiv' xs ys \<Longrightarrow> stream_all2 B_A.equiv' ys xs"
  by (coinduction arbitrary: xs ys) (auto simp: B_A.equiv'_def A_B.equiv'_def)

end (* Bisim Invariant *)

locale Bisimulation_Invariants = Simulation_Defs +
  fixes PA QA :: "'a \<Rightarrow> bool" and PB QB :: "'b \<Rightarrow> bool"
  assumes A_B_step: "\<And> a b a'. A a b \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b'. B a' b' \<and> b \<sim> b')"
  assumes B_A_step: "\<And> a a' b'. B a' b' \<Longrightarrow> a \<sim> a' \<Longrightarrow> PA a \<Longrightarrow> PB a' \<Longrightarrow> (\<exists> b. A a b \<and> b \<sim> b')"
  assumes A_invariant[intro]: "\<And> a b. PA a \<Longrightarrow> A a b \<Longrightarrow> QA b"
  assumes B_invariant[intro]: "\<And> a b. PB a \<Longrightarrow> B a b \<Longrightarrow> QB b"
  assumes PA_QA[intro]: "\<And> a. QA a \<Longrightarrow> PA a" and PB_QB[intro]: "\<And> a. QB a \<Longrightarrow> PB a"
begin

sublocale PA_invariant: Graph_Invariant A PA by standard blast

sublocale PB_invariant: Graph_Invariant B PB by standard blast

sublocale QA_invariant: Graph_Invariant A QA by standard blast

sublocale QB_invariant: Graph_Invariant B QB by standard blast

sublocale Pre_Bisim: Bisimulation_Invariant A B "(\<sim>)" PA PB
  by standard (auto intro: A_B_step B_A_step)

sublocale Post_Bisim: Bisimulation_Invariant A B "(\<sim>)" QA QB
  by standard (auto intro: A_B_step B_A_step)

sublocale A_B: Simulation_Invariants A B "(\<sim>)" PA QA PB QB
  by standard (blast intro: A_B_step)+

sublocale B_A: Simulation_Invariants B A "\<lambda> x y. y \<sim> x" PB QB PA QA
  by standard (blast intro: B_A_step)+

context
  fixes f
  assumes eq[simp]: "a \<sim> b \<longleftrightarrow> b = f a"
    and inj: "\<forall> a b. QB (f a) \<and> QA b \<and> f a = f b \<longrightarrow> a = b"
begin

lemmas list_all2_inj_map_eq = Post_Bisim.list_all2_inj_map_eq[OF eq inj]
lemmas steps_map_equiv' = Post_Bisim.steps_map_equiv[OF eq inj]

lemma list_all2_inj_map_eq':
  "as = bs" if "list_all2 (\<lambda>a b. a = f b) (map f as) bs" "list_all QB (map f as)" "list_all QA bs"
  using that by (rule list_all2_inj_map_eq)

lemma steps_map_equiv:
  "A.steps (a # as) \<longleftrightarrow> B.steps (b # map f as)" if "a \<sim> b" "PA a" "PB b"
proof
  assume "A.steps (a # as)"
  then show "B.steps (b # map f as)"
  proof cases
    case Single
    then show ?thesis by auto
  next
    case prems: (Cons a' xs)
    from A_B_step[OF \<open>A a a'\<close> \<open>a \<sim> b\<close> \<open>PA a\<close> \<open>PB b\<close>] obtain b' where "B b b'" "a' \<sim> b'"
      by auto
    with steps_map_equiv'[OF \<open>a' \<sim> b'\<close>, of xs] prems that show ?thesis
      by auto
  qed
next
  assume "B.steps (b # map f as)"
  then show "A.steps (a # as)"
  proof cases
    case Single
    then show ?thesis by auto
  next
    case prems: (Cons b' xs)
    from B_A_step[OF \<open>B b b'\<close> \<open>a \<sim> b\<close> \<open>PA a\<close> \<open>PB b\<close>] obtain a' where "A a a'" "a' \<sim> b'"
      by auto
    with that prems have "QA a'" "QB b'"
      by auto
    with \<open>A a a'\<close> \<open>a' \<sim> b'\<close> steps_map_equiv'[OF \<open>a' \<sim> b'\<close>, of "tl as"] prems that show ?thesis
      apply clarsimp
      subgoal for z zs
        using inj[rule_format, of z a'] by auto
      done
  qed
qed

lemma steps_map:
  "\<exists> as. bs = map f as" if "B.steps (f a # bs)" "PA a" "PB (f a)"
  using that proof cases
  case Single
  then show ?thesis by simp
next
  case prems: (Cons b' xs)
  from B_A_step[OF \<open>B _ b'\<close> _ \<open>PA a\<close> \<open>PB (f a)\<close>] obtain a' where "A a a'" "a' \<sim> b'"
    by auto
  with that prems have "QA a'" "QB b'"
    by auto
  with Post_Bisim.steps_map[OF eq inj, of a' xs] prems \<open>a' \<sim> b'\<close> obtain ys where "xs = map f ys"
    by auto
  with \<open>bs = _\<close> \<open>a' \<sim> b'\<close> show ?thesis
    by (inst_existentials "a' # ys") auto
qed

text \<open>
  @{thm Post_Bisim.reaches_equiv} cannot be lifted directly:
  injectivity cannot be applied for the reflexive case.
\<close>
lemma reaches1_equiv:
  "A.reaches1 a a' \<longleftrightarrow> B.reaches1 (f a) (f a')" if "PA a" "PB (f a)"
proof safe
  assume "A.reaches1 a a'"
  then obtain a'' where prems: "A a a''" "A.reaches a'' a'"
    including graph_automation_aggressive by blast
  from A_B_step[OF \<open>A a _\<close> _ that] obtain b where "B (f a) b" "a'' \<sim> b"
    by auto
  with that prems have "QA a''" "QB b"
    by auto
  with Post_Bisim.reaches_equiv[OF eq inj, of a'' a'] prems \<open>B (f a) b\<close> \<open>a'' \<sim> b\<close>
  show "B.reaches1 (f a) (f a')"
    by auto
next
  assume "B.reaches1 (f a) (f a')"
  then obtain b where prems: "B (f a) b" "B.reaches b (f a')"
    including graph_automation_aggressive by blast
  from B_A_step[OF \<open>B _ b\<close> _ \<open>PA a\<close> \<open>PB (f a)\<close>] obtain a'' where "A a a''" "a'' \<sim> b"
    by auto
  with that prems have "QA a''" "QB b"
    by auto
  with Post_Bisim.reaches_equiv[OF eq inj, of a'' a'] prems \<open>A a a''\<close> \<open>a'' \<sim> b\<close>
  show "A.reaches1 a a'"
    by auto
qed

end (* Context for Equality Relation *)

end (* Bisim Invariant *)

lemma Bisimulation_Invariant_composition:
  assumes
    "Bisimulation_Invariant A B sim1 PA PB"
    "Bisimulation_Invariant B C sim2 PB PC"
  shows
    "Bisimulation_Invariant A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA PC"
proof -
  interpret A: Bisimulation_Invariant A B sim1 PA PB
    by (rule assms(1))
  interpret B: Bisimulation_Invariant B C sim2 PB PC
    by (rule assms(2))
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step | blast dest: A.B_A_step B.B_A_step))
qed

lemma Bisimulation_Invariant_filter:
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> a b. sim a b \<Longrightarrow> PA a \<Longrightarrow> PB b \<Longrightarrow> FA a \<longleftrightarrow> FB b"
    "\<And> a b. A a b \<and> FA b \<longleftrightarrow> A' a b"
    "\<And> a b. B a b \<and> FB b \<longleftrightarrow> B' a b"
  shows
    "Bisimulation_Invariant A' B' sim PA PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms(1))
  have unfold:
    "A' = (\<lambda> a b. A a b \<and> FA b)" "B' = (\<lambda> a b. B a b \<and> FB b)"
    using assms(3,4) by auto
  show ?thesis
    unfolding unfold
    apply standard
    using assms(2) apply (blast dest: A_B_step)
    using assms(2) apply (blast dest: B_A_step)
    by blast+
qed

lemma Bisimulation_Invariants_filter:
  assumes
    "Bisimulation_Invariants A B sim PA QA PB QB"
    "\<And> a b. QA a \<Longrightarrow> QB b \<Longrightarrow> FA a \<longleftrightarrow> FB b"
    "\<And> a b. A a b \<and> FA b \<longleftrightarrow> A' a b"
    "\<And> a b. B a b \<and> FB b \<longleftrightarrow> B' a b"
  shows
    "Bisimulation_Invariants A' B' sim PA QA PB QB"
proof -
  interpret Bisimulation_Invariants A B sim PA QA PB QB
    by (rule assms(1))
  have unfold:
    "A' = (\<lambda> a b. A a b \<and> FA b)" "B' = (\<lambda> a b. B a b \<and> FB b)"
    using assms(3,4) by auto
  show ?thesis
    unfolding unfold
    apply standard
    using assms(2) apply (blast dest: A_B_step)
    using assms(2) apply (blast dest: B_A_step)
    by blast+
qed

lemma Bisimulation_Invariants_composition:
  assumes
    "Bisimulation_Invariants A B sim1 PA QA PB QB"
    "Bisimulation_Invariants B C sim2 PB QB PC QC"
  shows
    "Bisimulation_Invariants A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA QA PC QC"
proof -
  interpret A: Bisimulation_Invariants A B sim1 PA QA PB QB
    by (rule assms(1))
  interpret B: Bisimulation_Invariants B C sim2 PB QB PC QC
    by (rule assms(2))
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step | blast dest: A.B_A_step B.B_A_step))
qed

lemma Bisimulation_Invariant_Invariants_composition:
  assumes
    "Bisimulation_Invariant A B sim1 PA PB"
    "Bisimulation_Invariants B C sim2 PB QB PC QC"
  shows
    "Bisimulation_Invariants A C (\<lambda> a c. \<exists> b. PB b \<and> sim1 a b \<and> sim2 b c) PA PA PC QC"
proof -
  interpret Bisimulation_Invariant A B sim1 PA PB
    by (rule assms(1))
  interpret B: Bisimulation_Invariants B C sim2 PB QB PC QC
    by (rule assms(2))
  interpret A: Bisimulation_Invariants A B sim1 PA PA PB QB
    by (standard; blast intro: A_B_step B_A_step)+
  show ?thesis
    by (standard; (blast dest: A.A_B_step B.A_B_step | blast dest: A.B_A_step B.B_A_step))
qed

lemma Bisimulation_Invariant_Bisimulation_Invariants:
  assumes "Bisimulation_Invariant A B sim PA PB"
  shows "Bisimulation_Invariants A B sim PA PA PB PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step)
qed

lemma Bisimulation_Invariant_strengthen_post:
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> a b. PA' a \<Longrightarrow> PA b \<Longrightarrow> A a b \<Longrightarrow> PA' b"
    "\<And> a. PA' a \<Longrightarrow> PA a"
  shows "Bisimulation_Invariant A B sim PA' PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step assms)
qed

lemma Bisimulation_Invariant_strengthen_post':
  assumes
    "Bisimulation_Invariant A B sim PA PB"
    "\<And> a b. PB' a \<Longrightarrow> PB b \<Longrightarrow> B a b \<Longrightarrow> PB' b"
    "\<And> a. PB' a \<Longrightarrow> PB a"
  shows "Bisimulation_Invariant A B sim PA PB'"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step B_A_step assms)
qed

lemma Simulation_Invariant_strengthen_post:
  assumes
    "Simulation_Invariant A B sim PA PB"
    "\<And> a b. PA a \<Longrightarrow> PA b \<Longrightarrow> A a b \<Longrightarrow> PA' b"
    "\<And> a. PA' a \<Longrightarrow> PA a"
  shows "Simulation_Invariant A B sim PA' PB"
proof -
  interpret Simulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariant_strengthen_post':
  assumes
    "Simulation_Invariant A B sim PA PB"
    "\<And> a b. PB a \<Longrightarrow> PB b \<Longrightarrow> B a b \<Longrightarrow> PB' b"
    "\<And> a. PB' a \<Longrightarrow> PB a"
  shows "Simulation_Invariant A B sim PA PB'"
proof -
  interpret Simulation_Invariant A B sim PA PB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariants_strengthen_post:
  assumes
    "Simulation_Invariants A B sim PA QA PB QB"
    "\<And> a b. PA a \<Longrightarrow> QA b \<Longrightarrow> A a b \<Longrightarrow> QA' b"
    "\<And> a. QA' a \<Longrightarrow> QA a"
  shows "Simulation_Invariants A B sim PA QA' PB QB"
proof -
  interpret Simulation_Invariants A B sim PA QA PB QB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Simulation_Invariants_strengthen_post':
  assumes
    "Simulation_Invariants A B sim PA QA PB QB"
    "\<And> a b. PB a \<Longrightarrow> QB b \<Longrightarrow> B a b \<Longrightarrow> QB' b"
    "\<And> a. QB' a \<Longrightarrow> QB a"
  shows "Simulation_Invariants A B sim PA QA PB QB'"
proof -
  interpret Simulation_Invariants A B sim PA QA PB QB
    by (rule assms)
  show ?thesis
    by (standard; blast intro: A_B_step assms)
qed

lemma Bisimulation_Invariant_sim_replace:
  assumes "Bisimulation_Invariant A B sim PA PB"
      and "\<And> a b. PA a \<Longrightarrow> PB b \<Longrightarrow> sim a b \<longleftrightarrow> sim' a b"
    shows "Bisimulation_Invariant A B sim' PA PB"
proof -
  interpret Bisimulation_Invariant A B sim PA PB
    by (rule assms(1))
  show ?thesis
    apply standard
    using assms(2) apply (blast dest: A_B_step)
    using assms(2) apply (blast dest: B_A_step)
    by blast+
qed

end (* Theory *)
