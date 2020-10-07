theory Roy_Floyd_Warshall
imports Main
begin

section \<open>Transitive closure algorithm\<close>

text \<open>
  The Roy-Floyd-Warshall algorithm takes a finite relation as input and
  produces its transitive closure as output. It iterates over all elements of
  the field of the relation and maintains a cumulative approximation of the
  result: step \<open>0\<close> starts with the original relation, and step \<open>Suc n\<close>
  connects all paths over the intermediate element \<open>n\<close>. The final
  approximation coincides with the full transitive closure.

  This algorithm is often named after ``Floyd'', ``Warshall'', or
  ``Floyd-Warshall'', but the earliest known description is due to B. Roy
  @{cite "Roy:1959"}.

  \<^medskip>
  Subsequently we use a direct mathematical model of the relation, bypassing
  matrices and arrays that are usually seen in the literature. This is more
  efficient for sparse relations: only the adjacency for immediate
  predecessors and successors needs to be maintained, not the square of all
  possible combinations. Moreover we do not have to worry about mutable data
  structures in a multi-threaded environment. See also the graph
  implementation in the Isabelle sources @{file
  \<open>$ISABELLE_HOME/src/Pure/General/graph.ML\<close>} and @{file
  \<open>$ISABELLE_HOME/src/Pure/General/graph.scala\<close>}.
\<close>

type_synonym relation = "(nat \<times> nat) set"

fun steps :: "relation \<Rightarrow> nat \<Rightarrow> relation"
where
  "steps rel 0 = rel"
| "steps rel (Suc n) =
    steps rel n \<union> {(x, y). (x, n) \<in> steps rel n \<and> (n, y) \<in> steps rel n}"


text \<open>Implementation view on the relation:\<close>

definition preds :: "relation \<Rightarrow> nat \<Rightarrow> nat set"
  where "preds rel y = {x. (x, y) \<in> rel}"

definition succs :: "relation \<Rightarrow> nat \<Rightarrow> nat set"
  where "succs rel x = {y. (x, y) \<in> rel}"

lemma
  "steps rel (Suc n) =
    steps rel n \<union> {(x, y). x \<in> preds (steps rel n) n \<and> y \<in> succs (steps rel n) n}"
  by (simp add: preds_def succs_def)

text \<open>
  The main function requires an upper bound for the iteration, which is left
  unspecified here (via Hilbert's choice).
\<close>

definition is_bound :: "relation \<Rightarrow> nat \<Rightarrow> bool"
  where "is_bound rel n \<longleftrightarrow> (\<forall>m \<in> Field rel. m < n)"

definition "transitive_closure rel = steps rel (SOME n. is_bound rel n)"


section \<open>Correctness proof\<close>

subsection \<open>Miscellaneous lemmas\<close>

lemma finite_bound:
  assumes "finite rel"
  shows "\<exists>n. is_bound rel n"
  using assms
proof induct
  case empty
  then show ?case by (simp add: is_bound_def)
next
  case (insert p rel)
  then obtain n where n: "\<forall>m \<in> Field rel. m < n"
    unfolding is_bound_def by blast
  obtain x y where "p = (x, y)" by (cases p)
  then have "\<forall>m \<in> Field (insert p rel). m < max (Suc x) (max (Suc y) n)"
    using n by auto
  then show ?case
    unfolding is_bound_def by blast
qed

lemma steps_Suc: "(x, y) \<in> steps rel (Suc n) \<longleftrightarrow>
  (x, y) \<in> steps rel n \<or> (x, n) \<in> steps rel n \<and> (n, y) \<in> steps rel n"
  by auto

lemma steps_cases:
  assumes "(x, y) \<in> steps rel (Suc n)"
  obtains (copy) "(x, y) \<in> steps rel n"
    | (step) "(x, n) \<in> steps rel n" and "(n, y) \<in> steps rel n"
  using assms by auto

lemma steps_rel: "(x, y) \<in> rel \<Longrightarrow> (x, y) \<in> steps rel n"
  by (induct n) auto


subsection \<open>Bounded closure\<close>

text \<open>
  The bounded closure connects all transitive paths over elements below a
  given bound. For an upper bound of the relation, this coincides with the
  full transitive closure.
\<close>

inductive_set Clos :: "relation \<Rightarrow> nat \<Rightarrow> relation"
  for rel :: relation and n :: nat
where
  base: "(x, y) \<in> Clos rel n" if "(x, y) \<in> rel"
| step: "(x, y) \<in> Clos rel n" if "(x, z) \<in> Clos rel n" and "(z, y) \<in> Clos rel n" and "z < n"

theorem Clos_closure:
  assumes "is_bound rel n"
  shows "(x, y) \<in> Clos rel n \<longleftrightarrow> (x, y) \<in> rel\<^sup>+"
proof
  show "(x, y) \<in> rel\<^sup>+" if "(x, y) \<in> Clos rel n"
    using that by induct simp_all
  show "(x, y) \<in> Clos rel n" if "(x, y) \<in> rel\<^sup>+"
    using that
  proof (induct rule: trancl_induct)
    case (base y)
    then show ?case by (rule Clos.base)
  next
    case (step y z)
    from \<open>(y, z) \<in> rel\<close> have 1: "(y, z) \<in> Clos rel n" by (rule base)
    from \<open>(y, z) \<in> rel\<close> and \<open>is_bound rel n\<close> have 2: "y < n"
      unfolding is_bound_def Field_def by blast
    from step(3) 1 2 show ?case by (rule Clos.step)
  qed
qed

lemma Clos_Suc:
  assumes "(x, y) \<in> Clos rel n"
  shows "(x, y) \<in> Clos rel (Suc n)"
  using assms by induct (auto intro: Clos.intros)

text \<open>
  In each step of the algorithm the approximated relation is exactly the
  bounded closure.
\<close>

theorem steps_Clos_equiv: "(x, y) \<in> steps rel n \<longleftrightarrow> (x, y) \<in> Clos rel n"
proof (induct n arbitrary: x y)
  case 0
  show ?case
  proof
    show "(x, y) \<in> Clos rel 0" if "(x, y) \<in> steps rel 0"
    proof -
      from that have "(x, y) \<in> rel" by simp
      then show ?thesis by (rule Clos.base)
    qed
    show "(x, y) \<in> steps rel 0" if "(x, y) \<in> Clos rel 0"
      using that by cases simp_all
  qed
next
  case (Suc n)
  show ?case
  proof
    show "(x, y) \<in> Clos rel (Suc n)" if "(x, y) \<in> steps rel (Suc n)"
      using that
    proof (cases rule: steps_cases)
      case copy
      with Suc(1) have "(x, y) \<in> Clos rel n" ..
      then show ?thesis by (rule Clos_Suc)
    next
      case step
      with Suc have "(x, n) \<in> Clos rel n" and "(n, y) \<in> Clos rel n"
        by simp_all
      then have "(x, n) \<in> Clos rel (Suc n)" and "(n, y) \<in> Clos rel (Suc n)"
        by (simp_all add: Clos_Suc)
      then show ?thesis by (rule Clos.step) simp
    qed
    show "(x, y) \<in> steps rel (Suc n)" if "(x, y) \<in> Clos rel (Suc n)"
      using that
    proof induct
      case (base x y)
      then show ?case by (simp add: steps_rel)
    next
      case (step x z y)
      with Suc show ?case
        by (auto simp add: steps_Suc less_Suc_eq intro: Clos.step)
    qed
  qed
qed


subsection \<open>Main theorem\<close>

text \<open>
  The main theorem follows immediately from the key observations above. Note
  that the assumption of finiteness gives a bound for the iteration, although
  the details are left unspecified. A concrete implementation could choose the
  the maximum element + 1, or iterate directly over the data structures for
  the @{term preds} and @{term succs} implementation.
\<close>

theorem transitive_closure_correctness:
  assumes "finite rel"
  shows "transitive_closure rel = rel\<^sup>+"
proof -
  let ?N = "SOME n. is_bound rel n"
  have is_bound: "is_bound rel ?N"
    by (rule someI_ex) (rule finite_bound [OF \<open>finite rel\<close>])
  have "(x, y) \<in> steps rel ?N \<longleftrightarrow> (x, y) \<in> rel\<^sup>+" for x y
  proof -
    have "(x, y) \<in> steps rel ?N \<longleftrightarrow> (x, y) \<in> Clos rel ?N"
      by (rule steps_Clos_equiv)
    also have "\<dots> \<longleftrightarrow> (x, y) \<in> rel\<^sup>+"
      using is_bound by (rule Clos_closure)
    finally show ?thesis .
  qed
  then show ?thesis unfolding transitive_closure_def by auto
qed


section \<open>Alternative formulation\<close>

text \<open>
  The core of the algorithm may be expressed more declaratively as follows,
  using an inductive definition to imitate a logic-program. This is equivalent
  to the function specification @{term steps} from above.
\<close>

inductive Steps :: "relation \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<Rightarrow> bool"
  for rel :: relation
where
  base: "Steps rel 0 (x, y)" if "(x, y) \<in> rel"
| copy: "Steps rel (Suc n) (x, y)" if "Steps rel n (x, y)"
| step: "Steps rel (Suc n) (x, y)" if "Steps rel n (x, n)" and "Steps rel n (n, y)"

lemma steps_equiv: "(x, y) \<in> steps rel n \<longleftrightarrow> Steps rel n (x, y)"
proof
  show "Steps rel n (x, y)" if "(x, y) \<in> steps rel n"
    using that
  proof (induct n arbitrary: x y)
    case 0
    then have "(x, y) \<in> rel" by simp
    then show ?case by (rule base)
  next
    case (Suc n)
    from Suc(2) show ?case
    proof (cases rule: steps_cases)
      case copy
      with Suc(1) have "Steps rel n (x, y)" .
      then show ?thesis by (rule Steps.copy)
    next
      case step
      with Suc(1) have "Steps rel n (x, n)" and "Steps rel n (n, y)"
        by simp_all
      then show ?thesis by (rule Steps.step)
    qed
  qed
  show "(x, y) \<in> steps rel n" if "Steps rel n (x, y)"
    using that by induct simp_all
qed

end
