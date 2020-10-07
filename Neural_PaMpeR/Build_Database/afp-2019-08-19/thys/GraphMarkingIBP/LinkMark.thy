
section \<open>Generalization of Deutsch-Schorr-Waite Algorithm\<close>

theory LinkMark
imports StackMark
begin

text \<open>
In the third step the stack diagram is refined to a diagram where no extra 
memory is used. The relation $next$  is replaced by two new variables $link$ and $label$. 
The variable $\mathit{label}:\mathit{node}\to \mathit{index}$ associates a label to every node and the variable
$\mathit{link}: \mathit{index}\to \mathit{node}\to \mathit{node}$ is a collection of pointer functions indexed by the set  
$\mathit{index}$ of labels. For $x\in \mathit{node}$, $\mathit{link} \ i \ x$ is the successor node of $x$  along 
the function $\mathit{link} \ i$. In this context a node $x$ is reachable if there exists a path 
from the root to $x$  along the links $\mathit{link} \ i$  such that all nodes in this path are 
not $\mathit{nil}$ and they are labeled by a special label $\mathit{none}\in \mathit{index}$.

The stack variable $S$ is replaced by two new variables $p$ and $t$ ranging over nodes. Variable $p$ 
stores the head of $S$,  $t$ stores the head of the tail of $S$, and the rest of $S$ 
is stored by temporarily modifying the variables $\mathit{link}$ and $\mathit{label}$.

This algorithm is a generalization of the Deutsch-Schorr-Waite graph marking algorithm because
we have a collection of pointer functions instead of left and right only.
\<close>

locale pointer = node +
  fixes none :: "'index"
  fixes link0::"'index \<Rightarrow> 'node \<Rightarrow> 'node"
  fixes label0 :: "'node \<Rightarrow> 'index"
  (* next assume is used to bind the type variable 'node introduced in this locale to the 
    type variable 'node introduced in the locale node. *)
  assumes "(nil::'node) = nil"
begin
  definition "next =  {(a, b) . (\<exists> i . link0 i a = b) \<and> a \<noteq> nil \<and> b \<noteq> nil \<and> label0 a = none}"
end

sublocale pointer \<subseteq> link?: graph "nil" "root" "next"
  apply unfold_locales
  apply (unfold next_def)
  by auto

text\<open>
The locale pointer fixes the initial values for the variables $ \mathit{link}$ and $ \mathit{label}$ and
it defines the relation next as the union of all $ \mathit{link} \ i$ functions, excluding
the mappings to $ \mathit{nil}$, the mappings from $ \mathit{nil}$ as well as the mappings from elements which
are not labeled by $ \mathit{none}$.
\<close>

text\<open>
The next two recursive functions, $ \mathit{label}\_0$, $ \mathit{link}\_0$ are used to compute
the initial values of the variables $ \mathit{label}$ and $ \mathit{link}$ from their current
values.
\<close>

context pointer
begin
primrec
  label_0:: "('node \<Rightarrow> 'index) \<Rightarrow> ('node list) \<Rightarrow> ('node \<Rightarrow> 'index)" where 
   "label_0 lbl []      = lbl" |
   "label_0 lbl (x # l) = label_0 (lbl(x := none)) l"

lemma label_cong [cong]: "f = g \<Longrightarrow> xs = ys \<Longrightarrow> pointer.label_0 n f xs = pointer.label_0 n g ys"
by simp

primrec
  link_0:: "('index \<Rightarrow> 'node \<Rightarrow> 'node) \<Rightarrow> ('node \<Rightarrow> 'index) \<Rightarrow> 'node \<Rightarrow> ('node list) \<Rightarrow> ('index \<Rightarrow> 'node \<Rightarrow> 'node)" where
  "link_0 lnk lbl p []       = lnk" |
  "link_0 lnk lbl p (x # l)  = link_0 (lnk((lbl x) := ((lnk (lbl x))(x := p)))) lbl x l"

text\<open>
The function $ \mathit{stack}$ defined bellow is the main data refinement relation connecting
the stack from the abstract algorithm to its concrete representation by temporarily
modifying the variable $ \mathit{link}$ and $ \mathit{label}$.
\<close>

primrec
  stack:: "('index \<Rightarrow> 'node \<Rightarrow> 'node) \<Rightarrow> ('node \<Rightarrow> 'index) \<Rightarrow> 'node \<Rightarrow> ('node list) \<Rightarrow> bool" where
  "stack lnk lbl x []       = (x = nil)" |
  "stack lnk lbl x (y # l)  = 
      (x \<noteq> nil \<and> x = y \<and> \<not> x \<in> set l \<and> stack lnk lbl (lnk (lbl x) x) l)"


lemma label_out_range0 [simp]:
  "\<not> x \<in> set S \<Longrightarrow> label_0 lbl S x = lbl x"
  apply (rule_tac P="\<forall> label . \<not> x \<in> set S \<longrightarrow> label_0 label S x = label x" in mp)
  by (simp, induct_tac S, auto)

lemma link_out_range0 [simp]:
  "\<not> x \<in> set S \<Longrightarrow> link_0 link label p S i x = link i x"
  apply (rule_tac P="\<forall> link p . \<not> x \<in> set S \<longrightarrow> link_0 link label p S i x = link i x" in mp)
  by (simp, induct_tac S, auto)

lemma link_out_range [simp]: "\<not> x \<in> set S \<Longrightarrow> link_0 link (label(x := y)) p S = link_0 link label p S"
  apply (rule_tac P="\<forall> link p . \<not> x \<in> set S \<longrightarrow> link_0 link (label(x := y)) p S = link_0 link label p S" in mp)
  by (simp, induct_tac S, auto)

lemma empty_stack [simp]: "stack link label nil S = (S = [])"
  by (case_tac S, simp_all)

lemma stack_out_link_range [simp]: "\<not> p \<in> set S \<Longrightarrow> stack (link(i := (link i)(p := q))) label x S = stack link label x S"
  apply (rule_tac P = "\<forall> link x . \<not> p \<in> set S \<longrightarrow> stack (link(i := (link i)(p := q))) label x S = stack link label x S" in mp)
  by (simp, induct_tac S, auto)

lemma stack_out_label_range [simp]: "\<not> p \<in> set S \<Longrightarrow> stack link (label(p := q)) x S = stack link label x S"
  apply (rule_tac P = "\<forall> link x . \<not> p \<in> set S \<longrightarrow> stack link (label(p := q)) x S = stack link label x S" in mp)
  by (simp, induct_tac S, auto)

definition
  "g mrk lbl ptr x \<equiv> ptr x \<noteq> nil \<and> ptr x \<notin> mrk \<and> lbl x = none"

lemma g_cong [cong]: "mrk = mrk1 \<Longrightarrow> lbl = lbl1 \<Longrightarrow> ptr = ptr1 \<Longrightarrow> x = x1 ==> 
       pointer.g n m mrk lbl ptr x = pointer.g n m mrk1 lbl1 ptr1 x1"
by simp

subsection \<open>Transitions\<close>

definition
  "Q1''_a \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' .
      root = nil \<and> p' = nil \<and> t' = nil \<and> lnk' = lnk \<and> lbl' = lbl \<and> mrk' = mrk:]"

definition
  "Q2''_a \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' .
      root \<noteq> nil \<and> p' = root \<and> t' = nil \<and> lnk' = lnk \<and> lbl' = lbl \<and> mrk' = mrk \<union> {root} :]"

definition
  "Q3''_a \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' .
         p \<noteq> nil \<and> 
         (\<exists> i . g mrk lbl (lnk i) p \<and> 
            p' = lnk i p \<and> t' =  p \<and> lnk' =  lnk(i := (lnk i)(p := t)) \<and> lbl' = lbl(p := i) \<and>
            mrk' = mrk \<union> {lnk i p}) :]"

definition
  "Q4''_a  \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' .
          p \<noteq> nil \<and> 
          (\<forall> i . \<not> g mrk lbl (lnk i) p) \<and> t \<noteq> nil \<and> 
          p' = t \<and> t' = lnk (lbl t) t \<and> lnk' = lnk(lbl t := (lnk (lbl t))(t := p)) 
          \<and> lbl' = lbl(t := none) \<and> mrk' = mrk:]"

definition
  "Q5''_a \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' .
           p \<noteq> nil \<and> 
          (\<forall> i . \<not> g mrk lbl (lnk i) p) \<and> t = nil \<and>
           p' = nil \<and> t' = t \<and> lnk' =  lnk \<and> lbl' = lbl \<and> mrk' = mrk:]"

definition
  "Q6''_a \<equiv> [: p, t, lnk, lbl, mrk \<leadsto> p', t', lnk', lbl', mrk' . p = nil \<and>  
         p' = p \<and> t' = t \<and> lnk' = lnk \<and> lbl' =  lbl \<and> mrk' = mrk :]"

subsection \<open>Invariants\<close>

definition
  "Init'' \<equiv> { (p, t, lnk, lbl, mrk) . lnk = link0 \<and> lbl = label0}"

definition
  "Loop'' \<equiv> UNIV"

definition
  "Final'' \<equiv> Init''"

subsection \<open>Data refinement relations\<close>

definition 
  "R1'_a \<equiv> {: p, t, lnk, lbl, mrk \<leadsto> stk, mrk' . (p, t, lnk, lbl, mrk) \<in> Init'' \<and> mrk' = mrk:}"

definition  
  "R2'_a \<equiv> {: p, t, lnk, lbl, mrk \<leadsto> stk, mrk' .  
       p = head stk \<and>  
       t = head (tail stk) \<and>  
       stack lnk lbl t (tail stk) \<and> 
       link0 = link_0 lnk lbl p (tail stk) \<and> 
       label0 = label_0 lbl (tail stk) \<and>
       \<not> nil \<in> set stk \<and> 
       mrk' = mrk :}"

lemma [simp]: "R1'_a \<in> Apply.Disjunctive" by (simp add: R1'_a_def)

lemma [simp]: "R2'_a \<in> Apply.Disjunctive" by (simp add: R2'_a_def)

definition [simp]:
  "R'_a i = (case i of
      I.init  \<Rightarrow> R1'_a |
      I.loop  \<Rightarrow> R2'_a |
      I.final \<Rightarrow> R1'_a)"

lemma [simp]: "Disjunctive_fun R'_a" by (simp add: Disjunctive_fun_def)

subsection\<open>Diagram\<close>

definition 
  "LinkMark = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> Q1''_a \<sqinter>  Q2''_a |
      (I.loop, I.loop)  \<Rightarrow> Q3''_a \<sqinter> (Q4''_a \<sqinter> Q5''_a) |
      (I.loop, I.final) \<Rightarrow> Q6''_a |
       _ \<Rightarrow> \<top>))"

definition [simp]:
  "LinkMarkInv i = (case i of
      I.init  \<Rightarrow> Init'' |
      I.loop  \<Rightarrow> Loop'' |
      I.final \<Rightarrow> Final'')"

subsection \<open>Data refinement of the transitions\<close>

theorem init1_a [simp]:
  "DataRefinement ({.Init'.} o Q1'_a) R1'_a R2'_a Q1''_a"
  by (simp add: data_refinement_hoare hoare_demonic Q1''_a_def Init'_def Init''_def 
       Loop''_def R1'_a_def R2'_a_def Q1'_a_def tail_def head_def angelic_def subset_eq)

theorem init2_a [simp]:
  "DataRefinement ({.Init'.} o Q2'_a) R1'_a R2'_a Q2''_a"
  by (simp add: data_refinement_hoare hoare_demonic Q2''_a_def Init'_def Init''_def 
       Loop''_def R1'_a_def R2'_a_def Q2'_a_def tail_def head_def angelic_def subset_eq)

theorem step1_a [simp]:
  "DataRefinement ({.Loop'.} o Q3'_a) R2'_a R2'_a Q3''_a"
  apply (simp add: data_refinement_hoare hoare_demonic Q3''_a_def Init'_def Init''_def 
       Loop'_def R1'_a_def Q3'_a_def tail_def head_def angelic_def subset_eq)
  apply (unfold next_def)
  apply (simp add: R2'_a_def)
  apply (simp add: data_refinement_hoare)
  apply (simp_all add: R2'_a_def angelic_def hoare_demonic simp_eq_emptyset)
  apply auto
  apply (rule_tac x = "aa i (hd a) # a" in exI)
  apply safe
  apply simp_all
  apply (simp add: g_def  neq_Nil_conv)
  apply clarify
  apply (simp add: g_def  neq_Nil_conv)
  apply (case_tac a)
  apply (simp_all add: g_def  neq_Nil_conv)
  apply (case_tac a)
  apply simp_all
  apply (case_tac a)
  by auto


lemma neqif [simp]: "x \<noteq> y \<Longrightarrow> (if y = x then a else b) = b"
  apply (case_tac "y \<noteq> x")
  apply simp_all
  done

theorem step2_a [simp]:
  "DataRefinement ({.Loop'.} o Q4'_a) R2'_a R2'_a Q4''_a"
  apply (simp add: data_refinement_hoare hoare_demonic Q4''_a_def Init'_def Init''_def 
       Loop'_def Q4'_a_def tail_def head_def angelic_def subset_eq)
  apply (unfold next_def)
  apply (simp add: R2'_a_def)
  apply (simp add: data_refinement_hoare)
  apply (simp_all add: R2'_a_def angelic_def hoare_demonic simp_eq_emptyset)
  apply (simp_all add: neq_Nil_conv)
  apply (unfold g_def)
  apply (simp add: head_def)
  apply safe
  apply auto [1]
  apply auto [1]
  apply (case_tac ysa)
  apply simp_all
  apply safe
  apply (case_tac "ab ya = i")
  by auto


lemma setsimp: "a = c \<Longrightarrow> (x \<in> a) = (x \<in> c)" 
  apply simp
  done

theorem step3_a [simp]:
  "DataRefinement ({.Loop'.} o Q4'_a) R2'_a R2'_a Q5''_a"
  apply (simp add: data_refinement_hoare hoare_demonic Q5''_a_def Init'_def Init''_def 
       Loop'_def Q4'_a_def angelic_def subset_eq)
  apply (unfold R2'_a_def)
  apply (unfold next_def)
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def subset_eq 
           simp_eq_emptyset g_def head_def tail_def)
  by auto

theorem final_a [simp]:
  "DataRefinement ({.Loop'.} o Q5'_a) R2'_a R1'_a Q6''_a"
   apply (simp add: data_refinement_hoare hoare_demonic Q6''_a_def Init'_def Init''_def 
       Loop'_def R2'_a_def R1'_a_def Q5'_a_def angelic_def subset_eq neq_Nil_conv tail_def head_def)
   apply (simp add: simp_eq_emptyset)
   apply safe
   by simp_all

subsection \<open>Diagram data refinement\<close>

lemma apply_fun_index [simp]: "(r .. P) i = (r i) (P i)" by (simp add: apply_fun_def)

lemma [simp]: "Disjunctive_fun (r::('c \<Rightarrow> 'a::complete_lattice \<Rightarrow> 'b::complete_lattice)) 
        \<Longrightarrow> mono_fun r"
  by (simp add: Disjunctive_fun_def mono_fun_def)

theorem LinkMark_DataRefinement_a [simp]:
 "DgrDataRefinement2 (R_a .. SetMarkInv) StackMark_a R'_a LinkMark"
  apply (rule_tac P = "StackMarkInv" in DgrDataRefinement_mono)
  apply (simp add: le_fun_def SetMarkInv_def angelic_def 
               R1_a_def R2_a_def Init'_def Final'_def)
  apply safe
  apply simp
  apply (simp add: DgrDataRefinement2_def dgr_demonic_def LinkMark_def 
    StackMark_a_def demonic_sup_inf data_refinement_choice2 assert_comp_choice)
  apply (rule data_refinement_choice2)
  apply simp_all
  apply (rule data_refinement_choice1)
  by simp_all

lemma [simp]: "mono Q1'_a" by (simp add: Q1'_a_def)
lemma [simp]: "mono Q2'_a" by (simp add: Q2'_a_def)
lemma [simp]: "mono Q3'_a" by (simp add: Q3'_a_def)
lemma [simp]: "mono Q4'_a" by (simp add: Q4'_a_def)
lemma [simp]: "mono Q5'_a" by (simp add: Q5'_a_def)

lemma [simp]: "dmono StackMark_a"
  apply (unfold dmono_def StackMark_a_def)
  by simp

subsection \<open>Diagram correctness\<close>

theorem LinkMark_correct:
  "Hoare_dgr (R'_a .. (R_a .. SetMarkInv)) LinkMark ((R'_a .. (R_a .. SetMarkInv)) \<sqinter> (- grd (step LinkMark)))"
  apply (rule_tac D = "StackMark_a" in Diagram_DataRefinement2)
  apply simp_all
  by (rule StackMark_correct)

end
end
