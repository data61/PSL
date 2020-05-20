section \<open>Deutsch-Schorr-Waite Marking Algorithm\<close>

theory DSWMark
imports LinkMark
begin

text\<open>
Finally, we construct the Deutsch-Schorr-Waite marking algorithm by assuming that there 
are only two pointers ($\mathit{left}$, $\mathit{right}$) from every node. There is also a new variable,
$\mathit{atom}: \mathit{node} \to  \mathit{bool}$ which associates to every node a Boolean value.
The data invariant of this refinement step requires that $\mathit{index}$ has exactly two distinct 
elements $none$  and $\mathit{some}$, $\mathit{left} = \mathit{link}\ \mathit{none}$, 
$\mathit{right}=\mathit{link}\  \mathit{some}$, and $\mathit{atom}\ x$ is true 
if and only if $\mathit{label}\ x = \mathit{some}$.

We use a new locale which fixes the initial values of the variables $\mathit{left}$, $\mathit{right}$, and
$\mathit{atom}$ in $\mathit{left0}$, $\mathit{right0}$, and $\mathit{atom0}$ respectively.
\<close>

datatype Index = none | some

locale classical = node +
  fixes left0  :: "'node \<Rightarrow> 'node"
  fixes right0 :: "'node \<Rightarrow> 'node"
  fixes atom0  :: "'node \<Rightarrow> bool"
  assumes "(nil::'node) = nil"
  begin
    definition
      "link0 i = (if i = (none::Index) then left0 else right0)"

    definition
      "label0 x = (if atom0 x then (some::Index) else none)"
  end

sublocale classical \<subseteq> dsw?: pointer "nil" "root" "none::Index" "link0" "label0"
proof qed auto

context classical
begin

lemma [simp]:
  "(label0 = (\<lambda> x . if atom x then some else none)) = (atom0 = atom)"
  apply (simp add: fun_eq_iff label0_def)
  by auto

definition
  "gg mrk atom ptr x \<equiv> ptr x \<noteq> nil \<and> ptr x \<notin> mrk \<and> \<not> atom x"

subsection \<open>Transitions\<close>

definition
  "QQ1_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
         root = nil \<and>  p' = nil \<and> t' = nil \<and> mrk' = mrk \<and> left' = left 
         \<and> right' = right \<and> atom' = atom :]"
  
definition
  "QQ2_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
         root \<noteq> nil \<and>  p' = root \<and> t' = nil \<and> mrk' = mrk \<union> {root} 
         \<and> left' = left \<and> right' = right \<and> atom' = atom :]"

definition
  "QQ3_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
      p \<noteq> nil \<and> gg mrk atom left p \<and>
      p' = left p \<and> t' = p \<and> mrk' = mrk \<union> {left p} \<and> 
      left' = left(p := t) \<and> right' = right \<and> atom' = atom:]"

definition
  "QQ4_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
      p \<noteq> nil \<and> gg mrk atom right p \<and>
      p' = right p \<and> t' = p \<and> mrk' = mrk \<union> {right p} \<and> 
      left' = left \<and> right' = right(p := t) \<and> atom' = atom(p := True) :]"

definition
  "QQ5_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
      p \<noteq> nil \<and> \<comment> \<open>not needed in the proof\<close>
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t \<noteq> nil \<and> \<not> atom t \<and>
      p' = t \<and> t' = left t \<and> mrk' = mrk \<and> 
      left' = left(t := p) \<and> right' = right \<and> atom' = atom :]"


definition
  "QQ6_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
      p \<noteq> nil \<and> \<comment> \<open>not needed in the proof\<close>
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t \<noteq> nil \<and> atom t \<and>
      p' = t \<and> t' = right t \<and> mrk' = mrk \<and> 
      left' = left \<and> right' = right(t := p) \<and> atom' = atom(t := False) :]"

definition
  "QQ7_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
      p \<noteq> nil \<and>
      \<not> gg mrk atom left p \<and> \<not> gg mrk atom right p \<and>
      t = nil \<and>
      p' = nil \<and> t' = t \<and> mrk' = mrk \<and> 
      left' = left \<and> right' = right \<and> atom' = atom :]"

definition
  "QQ8_a \<equiv> [: p, t, left, right, atom, mrk \<leadsto> p', t', left', right', atom', mrk' . 
     p = nil \<and> p' = p \<and> t' = t \<and> mrk' = mrk \<and> left' = left \<and> right' = right \<and> atom' = atom:]"

section \<open>Data refinement relation\<close>

definition
  "RR_a \<equiv> {: p, t, left, right, atom, mrk \<leadsto> p', t', lnk, lbl, mrk' .
          lnk none = left \<and> lnk some = right \<and>
          lbl = (\<lambda> x . if atom x then some else none) \<and>
          p' = p \<and> t' = t \<and> mrk' = mrk :}"

definition [simp]:
  "R''_a i = RR_a"

definition
  "ClassicMark = (\<lambda> (i, j) . (case (i, j) of
      (I.init, I.loop)  \<Rightarrow> QQ1_a \<sqinter> QQ2_a |
      (I.loop, I.loop)  \<Rightarrow> (QQ3_a \<sqinter> QQ4_a) \<sqinter> ((QQ5_a \<sqinter> QQ6_a) \<sqinter> QQ7_a) |
      (I.loop, I.final) \<Rightarrow> QQ8_a |
       _ \<Rightarrow> \<top>))"

subsection \<open>Data refinement of the transitions\<close>

theorem init1_a [simp]:
  "DataRefinement ({.Init''.} o Q1''_a) RR_a RR_a QQ1_a"
  by (simp add: data_refinement_hoare hoare_demonic angelic_def QQ1_a_def Q1''_a_def RR_a_def
       Init''_def subset_eq)

theorem init2_a [simp]:
  "DataRefinement ({.Init''.} o Q2''_a) RR_a RR_a QQ2_a"
  by (simp add: data_refinement_hoare hoare_demonic angelic_def QQ2_a_def Q2''_a_def RR_a_def
       Init''_def subset_eq)

lemma index_simp: 
  "(u = v) = (u none = v none \<and> u some = v some)"
  by (safe, rule ext, case_tac "x", auto)


theorem step1_a [simp]:
  "DataRefinement ({.Loop''.} o Q3''_a) RR_a RR_a QQ3_a"
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def QQ3_a_def  Q3''_a_def RR_a_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset)
  apply safe
  apply (rule_tac x="\<lambda> x . if x = some then ab some else (ab none)(a := aa)" in exI)
  apply simp
  apply (rule_tac x="none" in exI)
  apply (simp add: index_simp)
  done

theorem step2_a[simp]:
  "DataRefinement ({.Loop''.} o Q3''_a) RR_a RR_a QQ4_a"
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def QQ4_a_def Q3''_a_def RR_a_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset)
  apply safe
  apply (rule_tac x="\<lambda> x . if x = none then ab none else (ab some)(a := aa)" in exI)
  apply simp
  apply (rule_tac x="some" in exI)
  apply (simp add: index_simp)
  apply (rule ext)
  apply auto
  done

theorem step3_a [simp]:
  "DataRefinement ({.Loop''.} o Q4''_a) RR_a RR_a QQ5_a"
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def QQ5_a_def Q4''_a_def RR_a_def
       Loop''_def subset_eq g_def gg_def simp_eq_emptyset)
  apply clarify
  apply (case_tac "i")
  apply auto
  done

lemma if_set_elim: "(x \<in> (if b then A else B)) = ((b \<and> x \<in> A) \<or> (\<not> b \<and> x \<in> B))"
  by auto

theorem step4_a [simp]:
  "DataRefinement ({.Loop''.} o  Q4''_a) RR_a RR_a QQ6_a"
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def RR_a_def QQ6_a_def Q4''_a_def
       Loop''_def subset_eq simp_eq_emptyset g_def gg_def if_set_elim)
  apply (simp add: ext)
  apply safe
  apply (case_tac "i")
  apply simp_all
  apply (case_tac "i")
  apply simp_all
  apply (case_tac "i")
  apply simp_all
  apply (case_tac "i")
  by simp_all

theorem step5_a [simp]:
  "DataRefinement ({.Loop''.} o Q5''_a) RR_a RR_a QQ7_a"
  apply (simp add: data_refinement_hoare hoare_demonic angelic_def Q5''_a_def QQ7_a_def 
       Loop''_def subset_eq RR_a_def simp_eq_emptyset)
  apply safe
  apply (simp_all add: g_def gg_def)
  apply (case_tac "i")
  by auto

theorem final_step_a [simp]:
  "DataRefinement ({.Loop''.} o Q6''_a) RR_a RR_a QQ8_a"
  by (simp add: data_refinement_hoare hoare_demonic angelic_def Q6''_a_def QQ8_a_def 
       Loop''_def subset_eq RR_a_def simp_eq_emptyset)


subsection \<open>Diagram data refinement\<close>

lemma [simp]: "mono RR_a" by (simp add: RR_a_def)
lemma [simp]: "RR_a \<in> Apply.Disjunctive" by (simp add: RR_a_def)
lemma [simp]: "Disjunctive_fun R''_a" by (simp add: Disjunctive_fun_def)

lemma [simp]: "mono_fun R''_a" by simp

lemma [simp]: "mono Q1''_a" by (simp add: Q1''_a_def)
lemma [simp]: "mono Q2''_a" by (simp add: Q2''_a_def)
lemma [simp]: "mono Q3''_a" by (simp add: Q3''_a_def)
lemma [simp]: "mono Q4''_a" by (simp add: Q4''_a_def)
lemma [simp]: "mono Q5''_a" by (simp add: Q5''_a_def)
lemma [simp]: "mono Q6''_a" by (simp add: Q6''_a_def)

lemma [simp]: "dmono LinkMark"
  apply (unfold dmono_def LinkMark_def)
  by simp

theorem ClassicMark_DataRefinement_a [simp]:
 "DgrDataRefinement2 (R'_a .. (R_a .. SetMarkInv)) LinkMark R''_a ClassicMark"
  apply (rule_tac P = "LinkMarkInv" in DgrDataRefinement_mono)
  apply (simp add: le_fun_def SetMarkInv_def 
    angelic_def R1'_a_def R2'_a_def Init''_def Loop''_def Final''_def)
  apply auto
  apply (simp add: DgrDataRefinement2_def dgr_demonic_def ClassicMark_def LinkMark_def 
    demonic_sup_inf data_refinement_choice2 assert_comp_choice)
  apply (rule data_refinement_choice2)
  apply simp
  apply (rule data_refinement_choice1)
  apply simp_all
  apply (rule data_refinement_choice2)
  apply simp_all
  apply (rule data_refinement_choice1)
  by simp_all

subsection \<open>Diagram corectness\<close>

theorem ClassicMark_correct_a [simp]:
  "Hoare_dgr  (R''_a .. (R'_a .. (R_a .. SetMarkInv)))  ClassicMark 
         ((R''_a .. (R'_a ..(R_a .. SetMarkInv))) \<sqinter> (- grd (step ClassicMark)))"
  apply (rule_tac D = "LinkMark" in Diagram_DataRefinement2)
  apply auto
  by (rule LinkMark_correct)

text \<open>
We have proved the correctness of the final algorithm, but the pre and the post conditions
involve the angelic choice operator and they depend on all data refinement steps we 
have used to prove the final diagram. We simplify these conditions and we show that
we obtained indead the corectness of the marking algorithm. 

The predicate $\mathit{ClassicInit}$ which is true for the $\mathit{init}$ situation states that initially 
the variables $\mathit{left}$, $\mathit{right}$, and $\mathit{atom}$ are equal to their initial values and also 
that no node is marked.

The predicate $\mathit{ClassicFinal}$ which is true for the $final$ situation states that at the end
the values of the variables $\mathit{left}$, $\mathit{right}$, and $\mathit{atom}$ are again equal to their initial values
and the variable $mrk$ records all reachable nodes. The reachable nodes are defined using our initial 
$\mathit{next}$ relation, however if we unfold all locale interpretations and definitions we see easeily
that a node $x$ is reachable if there is a path from $root$ to $x$ along $\mathit{left}$ and $\mathit{right}$ functions,
and all nodes in this path have the atom bit false.
\<close>

definition 
  "ClassicInit = {(p, t, left, right, atom, mrk) .
      atom = atom0 \<and> left = left0 \<and> right = right0 \<and> 
      finite (- mrk) \<and> mrk = {}}"

definition 
  "ClassicFinal = {(p, t, left, right, atom, mrk) . 
       atom = atom0 \<and> left = left0 \<and> right = right0 \<and> 
       mrk = reach root}"

theorem [simp]:
  "ClassicInit \<subseteq> (RR_a (R1'_a (R1_a (SetMarkInv init))))"
  apply (simp add: SetMarkInv_def)
  apply (simp add: ClassicInit_def angelic_def RR_a_def R1'_a_def R1_a_def Init_def Init''_def)
  apply safe
  apply (unfold simp_eq_emptyset)
  apply (simp add: link0_def label0_def)
  apply (simp add: fun_eq_iff)
  by (simp add: label0_def)

theorem [simp]:
  "(RR_a (R1'_a (R1_a (SetMarkInv final)))) \<le> ClassicFinal"
  apply (simp add: SetMarkInv_def)
  apply (simp add: ClassicFinal_def angelic_def RR_a_def R1'_a_def R1_a_def 
    Final_def Final''_def Init''_def label0_def link0_def)
  apply (simp add: simp_eq_emptyset inf_fun_def)
  apply auto
  by (simp_all add: link0_def)

text\<open>
The indexed predicate $\mathit{ClassicPre}$ is the precondition of the diagram, and since we are only interested
in starting the marking diagram in the $init$ situation we set 
$\mathit{ClassicPre} \ loop = \mathit{ClassicPre} \ \mathit{final} = \emptyset$. 
\<close>

definition [simp]:
  "ClassicPre i =  (case i of
      I.init  \<Rightarrow> ClassicInit |
      I.loop  \<Rightarrow> {} |
      I.final \<Rightarrow> {})"

text\<open>
We are interested on the other hand that the marking diagram terminates only in the $\mathit{final}$ situation. In order to
achieve this we define the postcondition of the diagram as the indexed predicate $\mathit{ClassicPost}$ which is empty
on every situation except $final$. 
\<close>

definition [simp]:
  "ClassicPost i =  (case i of
      I.init  \<Rightarrow> {} |
      I.loop  \<Rightarrow> {} |
      I.final \<Rightarrow> ClassicFinal)"

lemma exists_or:
  "(\<exists> x . p x \<or> q x) = ((\<exists> x . p x) \<or> (\<exists> x . q x))"
  by auto

lemma [simp]:
  "(- grd (step  ClassicMark)) init = {}"
  apply (simp add: grd_def step_def)
  apply safe
  apply simp
  apply (drule_tac x = loop in spec)
  by (simp add: ClassicMark_def QQ1_a_def QQ2_a_def demonic_def)

lemma [simp]: "grd \<top> = \<bottom>"
  by (simp add: grd_def top_fun_def)

lemma [simp]:
  "(- grd (step  ClassicMark)) loop = {}"
  apply safe
  apply simp
  apply (frule_tac x = "final" in spec)
  apply (drule_tac x = "loop" in spec)
  apply (unfold ClassicMark_def QQ1_a_def QQ2_a_def QQ3_a_def QQ4_a_def QQ5_a_def QQ6_a_def QQ7_a_def QQ8_a_def)
  apply simp
  apply (case_tac "a \<noteq> nil")
  by auto

text \<open>
The final theorem states the correctness of the marking diagram with respect to the precondition
$\mathit{ClassicPre}$ and the postcondition $\mathit{ClassicPost}$, that is, if the diagram starts in the initial 
situation, then it will terminate in the final situation, and it will mark all reachable nodes.
\<close>

lemma [simp]: "mono QQ1_a" by (simp add: QQ1_a_def)
lemma [simp]: "mono QQ2_a" by (simp add: QQ2_a_def)
lemma [simp]: "mono QQ3_a" by (simp add: QQ3_a_def)
lemma [simp]: "mono QQ4_a" by (simp add: QQ4_a_def)
lemma [simp]: "mono QQ5_a" by (simp add: QQ5_a_def)
lemma [simp]: "mono QQ6_a" by (simp add: QQ6_a_def)
lemma [simp]: "mono QQ7_a" by (simp add: QQ7_a_def)
lemma [simp]: "mono QQ8_a" by (simp add: QQ8_a_def)

lemma [simp]: "dmono ClassicMark"
  apply (unfold dmono_def ClassicMark_def)
  by simp

theorem "\<Turnstile> ClassicPre {| pt ClassicMark |} ClassicPost"
  apply (rule_tac P = "(R''_a .. (R'_a .. (R_a ..SetMarkInv)))" in hoare_pre)
  apply (subst le_fun_def)
  apply simp
  apply (rule_tac Q = "((R''_a .. (R'_a .. (R_a .. SetMarkInv))) \<sqinter> (- grd (step ((ClassicMark)))))" in hoare_mono)
  apply (simp_all add: hoare_dgr_correctness)
  apply (rule le_funI)
  apply (case_tac x)
  apply (simp_all add: inf_fun_def del: uminus_apply)
  apply (rule_tac y = "RR_a (R1'_a (R1_a (SetMarkInv final)))" in order_trans)
  by auto

end

end

