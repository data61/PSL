(*
  Copyright (c) 2014-2019 by Clemens Ballarin
  This file is licensed under the 3-clause BSD license.
*)

theory Set_Theory imports "HOL-Library.FuncSet" begin

hide_const map
hide_const partition

no_notation divide (infixl "'/" 70)
no_notation inverse_divide (infixl "'/" 70)

text \<open>
  Each statement in the formal text is annotated with the location of the originating statement
  in Jacobson's text @{cite Jacobson1985}.  Each fact that Jacobson states explicitly is marked
  as @{command theorem} unless it is translated to a @{command sublocale} declaration.
  Literal quotations from Jacobson's text are reproduced in double quotes.

  Auxiliary results needed for the formalisation that cannot be found in Jacobson's text are marked
  as @{command lemma} or are @{command interpretation}s.  Such results are annotated with the
  location of a related statement.  For example, the introduction rule of a constant is annotated
  with the location of the definition of the corresponding operation.
\<close>


section \<open>Concepts from Set Theory.  The Integers\<close>

subsection \<open>The Cartesian Product Set.  Maps\<close>

text \<open>Maps as extensional HOL functions\<close>
text \<open>p 5, ll 21--25\<close>
locale map =
  fixes \<alpha> and S and T
  assumes graph [intro, simp]: "\<alpha> \<in> S \<rightarrow>\<^sub>E T"
begin

text \<open>p 5, ll 21--25\<close>
lemma map_closed [intro, simp]:
  "a \<in> S \<Longrightarrow> \<alpha> a \<in> T"
using graph by fast
  
text \<open>p 5, ll 21--25\<close>
lemma map_undefined [intro, simp]:
  "a \<notin> S \<Longrightarrow> \<alpha> a = undefined"
using graph by fast

end (* map *)

text \<open>p 7, ll 7--8\<close>
locale surjective_map = map + assumes surjective [intro]: "\<alpha> ` S = T"

text \<open>p 7, ll 8--9\<close>
locale injective_map = map + assumes injective [intro, simp]: "inj_on \<alpha> S"

text \<open>Enables locale reasoning about the inverse @{term "restrict (inv_into S \<alpha>) T"} of @{term \<alpha>}.\<close>
text \<open>p 7, ll 9--10\<close>
locale bijective =
  fixes \<alpha> and S and T
  assumes bijective [intro, simp]: "bij_betw \<alpha> S T"

text \<open>
  Exploit existing knowledge about @{term bij_betw} rather than extending @{locale surjective_map}
  and @{locale injective_map}.
\<close>
text \<open>p 7, ll 9--10\<close>
locale bijective_map = map + bijective begin

text \<open>p 7, ll 9--10\<close>
sublocale surjective_map by unfold_locales (simp add: bij_betw_imp_surj_on)

text \<open>p 7, ll 9--10\<close>
sublocale injective_map using bij_betw_def by unfold_locales fast

text \<open>p 9, ll 12--13\<close>
sublocale inverse: map "restrict (inv_into S \<alpha>) T" T S
  by unfold_locales (simp add: inv_into_into surjective)

text \<open>p 9, ll 12--13\<close>
sublocale inverse: bijective "restrict (inv_into S \<alpha>) T" T S
  by unfold_locales (simp add: bij_betw_inv_into surjective)

end (* bijective_map *)

text \<open>p 8, ll 14--15\<close>
abbreviation "identity S \<equiv> (\<lambda>x \<in> S. x)"

context map begin

text \<open>p 8, ll 18--20; p 9, ll 1--8\<close>
theorem bij_betw_iff_has_inverse:
  "bij_betw \<alpha> S T \<longleftrightarrow> (\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. compose S \<beta> \<alpha> = identity S \<and> compose T \<alpha> \<beta> = identity T)"
    (is "_ \<longleftrightarrow> (\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>)")
proof
  let ?inv = "restrict (inv_into S \<alpha>) T"
  assume "bij_betw \<alpha> S T"
  then have "?INV ?inv" and "?inv \<in> T \<rightarrow>\<^sub>E S"
    by (simp_all add: compose_inv_into_id bij_betw_imp_surj_on compose_id_inv_into bij_betw_imp_funcset bij_betw_inv_into)
  then show "\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>" ..
next
  assume "\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>"
  then obtain \<beta> where "\<alpha> \<in> S \<rightarrow> T" "\<beta> \<in> T \<rightarrow> S" "\<And>x. x \<in> S \<Longrightarrow> \<beta> (\<alpha> x) = x" "\<And>y. y \<in> T \<Longrightarrow> \<alpha> (\<beta> y) = y"
    by (metis PiE_restrict compose_eq graph restrict_PiE restrict_apply)
  then show "bij_betw \<alpha> S T" by (rule bij_betwI) 
qed

end (* map *)


subsection \<open>Equivalence Relations.  Factoring a Map Through an Equivalence Relation\<close>

text \<open>p 11, ll 6--11\<close>
locale equivalence =
  fixes S and E
  assumes closed [intro, simp]: "E \<subseteq> S \<times> S"
    and reflexive [intro, simp]: "a \<in> S \<Longrightarrow> (a, a) \<in> E"
    and symmetric [sym]: "(a, b) \<in> E \<Longrightarrow> (b, a) \<in> E"
    and transitive [trans]: "\<lbrakk> (a, b) \<in> E; (b, c) \<in> E \<rbrakk> \<Longrightarrow> (a, c) \<in> E"
begin

text \<open>p 11, ll 6--11\<close>
lemma left_closed [intro]: (* inefficient as a simp rule *)
  "(a, b) \<in> E \<Longrightarrow> a \<in> S"
  using closed by blast
  
text \<open>p 11, ll 6--11\<close>
lemma right_closed [intro]: (* inefficient as a simp rule *)
  "(a, b) \<in> E \<Longrightarrow> b \<in> S"
  using closed by blast

end (* equivalence *)

text \<open>p 11, ll 16--20\<close>
locale partition =
  fixes S and P
  assumes subset: "P \<subseteq> Pow S"
    and non_vacuous: "{} \<notin> P"
    and complete: "\<Union>P = S"
    and disjoint: "\<lbrakk> A \<in> P; B \<in> P; A \<noteq> B \<rbrakk> \<Longrightarrow> A \<inter> B = {}"

context equivalence begin

text \<open>p 11, ll 24--26\<close>
definition "Class = (\<lambda>a \<in> S. {b \<in> S. (b, a) \<in> E})"

text \<open>p 11, ll 24--26\<close>
lemma Class_closed [dest]:
  "\<lbrakk> a \<in> Class b; b \<in> S \<rbrakk> \<Longrightarrow> a \<in> S"
  unfolding Class_def by auto

text \<open>p 11, ll 24--26\<close>
lemma Class_closed2 [intro, simp]:
  "a \<in> S \<Longrightarrow> Class a \<subseteq> S"
  unfolding Class_def by auto

text \<open>p 11, ll 24--26\<close>
lemma Class_undefined [intro, simp]:
  "a \<notin> S \<Longrightarrow> Class a = undefined"
  unfolding Class_def by simp

text \<open>p 11, ll 24--26\<close>
lemma ClassI [intro, simp]:
  "(a, b) \<in> E \<Longrightarrow> a \<in> Class b"
  unfolding Class_def by (simp add: left_closed right_closed)
  
text \<open>p 11, ll 24--26\<close>
lemma Class_revI [intro, simp]:
  "(a, b) \<in> E \<Longrightarrow> b \<in> Class a"
  by (blast intro: symmetric)

text \<open>p 11, ll 24--26\<close>
lemma ClassD [dest]:
  "\<lbrakk> b \<in> Class a; a \<in> S \<rbrakk> \<Longrightarrow> (b, a) \<in> E"
  unfolding Class_def by simp

text \<open>p 11, ll 30--31\<close>
theorem Class_self [intro, simp]:
  "a \<in> S \<Longrightarrow> a \<in> Class a"
  unfolding Class_def by simp

text \<open>p 11, l 31; p 12, l 1\<close>
theorem Class_Union [simp]:
  "(\<Union>a\<in>S. Class a) = S"
  by blast

text \<open>p 11, ll 2--3\<close>
theorem Class_subset:
  "(a, b) \<in> E \<Longrightarrow> Class a \<subseteq> Class b"
proof
  fix a and b and c
  assume "(a, b) \<in> E" and "c \<in> Class a"
  then have "(c, a) \<in> E" by auto
  also note `(a, b) \<in> E`
  finally have "(c, b) \<in> E" by simp
  then show "c \<in> Class b" by auto
qed

text \<open>p 11, ll 3--4\<close>
theorem Class_eq:
  "(a, b) \<in> E \<Longrightarrow> Class a = Class b"
  by (auto intro!: Class_subset intro: symmetric)

text \<open>p 12, ll 1--5\<close>
theorem Class_equivalence:
  "\<lbrakk> a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> Class a = Class b \<longleftrightarrow> (a, b) \<in> E"
proof
  fix a and b
  assume "a \<in> S" "b \<in> S" "Class a = Class b"
  then have "a \<in> Class a" by auto
  also note `Class a = Class b`
  finally show "(a, b) \<in> E" by (fast intro: `b \<in> S`)
qed (rule Class_eq)

text \<open>p 12, ll 5--7\<close>
theorem not_disjoint_implies_equal:
  assumes not_disjoint: "Class a \<inter> Class b \<noteq> {}"
  assumes closed: "a \<in> S" "b \<in> S"
  shows "Class a = Class b"
proof -
  from not_disjoint and closed obtain c where witness: "c \<in> Class a \<inter> Class b" by fast
  with closed have "(a, c) \<in> E" by (blast intro: symmetric)
  also from witness and closed have "(c, b) \<in> E" by fast
  finally show ?thesis by (rule Class_eq)
qed

text \<open>p 12, ll 7--8\<close>
definition "Partition = {Class a | a. a \<in> S}"

text \<open>p 12, ll 7--8\<close>
lemma Class_in_Partition [intro, simp]:
  "a \<in> S \<Longrightarrow> Class a \<in> Partition"
  unfolding Partition_def by fast

text \<open>p 12, ll 7--8\<close>
theorem partition:
  "partition S Partition"
proof
  fix A and B
  assume closed: "A \<in> Partition" "B \<in> Partition"
  then obtain a and b where eq: "A = Class a" "B = Class b" and ab: "a \<in> S" "b \<in> S"
  unfolding Partition_def by auto
  assume distinct: "A \<noteq> B"
  then show "A \<inter> B = {}"
  proof (rule contrapos_np)
    assume not_disjoint: "A \<inter> B \<noteq> {}"
    then show "A = B" by (simp add: eq) (metis not_disjoint_implies_equal ab)
  qed
qed (auto simp: Partition_def)

end (* equivalence *)

context partition begin

text \<open>p 12, ll 9--10\<close>
theorem block_exists:
  "a \<in> S \<Longrightarrow> \<exists>A. a \<in> A \<and> A \<in> P"
  using complete by blast

text \<open>p 12, ll 9--10\<close>
theorem block_unique:
  "\<lbrakk> a \<in> A; A \<in> P; a \<in> B; B \<in> P \<rbrakk> \<Longrightarrow> A = B"
  using disjoint by blast

text \<open>p 12, ll 9--10\<close>
lemma block_closed [intro]: (* inefficient as a simp rule *)
  "\<lbrakk> a \<in> A; A \<in> P \<rbrakk> \<Longrightarrow> a \<in> S"
  using complete by blast

text \<open>p 12, ll 9--10\<close>
lemma element_exists:
  "A \<in> P \<Longrightarrow> \<exists>a \<in> S. a \<in> A"
  by (metis non_vacuous block_closed all_not_in_conv)

text \<open>p 12, ll 9--10\<close>
definition "Block = (\<lambda>a \<in> S. THE A. a \<in> A \<and> A \<in> P)"

text \<open>p 12, ll 9--10\<close>
lemma Block_closed [intro, simp]:
  assumes [intro]: "a \<in> S" shows "Block a \<in> P"
proof -
  obtain A where "a \<in> A" "A \<in> P" using block_exists by blast
  then show ?thesis
    apply (auto simp: Block_def)
    apply (rule theI2)
      apply (auto dest: block_unique)
    done
qed
  
text \<open>p 12, ll 9--10\<close>
lemma Block_undefined [intro, simp]:
  "a \<notin> S \<Longrightarrow> Block a = undefined"
  unfolding Block_def by simp

text \<open>p 12, ll 9--10\<close>
lemma Block_self:
  "\<lbrakk> a \<in> A; A \<in> P \<rbrakk> \<Longrightarrow> Block a = A"
  apply (simp add: Block_def block_closed)
  apply (rule the_equality)
   apply (auto dest: block_unique)
  done

text \<open>p 12, ll 10--11\<close>
definition "Equivalence = {(a, b) . \<exists>A \<in> P. a \<in> A \<and> b \<in> A}"

text \<open>p 12, ll 11--12\<close>
theorem equivalence: "equivalence S Equivalence"
proof
  show "Equivalence \<subseteq> S \<times> S" unfolding Equivalence_def using subset by auto
next
  fix a
  assume "a \<in> S"
  then show "(a, a) \<in> Equivalence" unfolding Equivalence_def using complete by auto
next
  fix a and b
  assume "(a, b) \<in> Equivalence"
  then show "(b, a) \<in> Equivalence" unfolding Equivalence_def by auto
next
  fix a and b and c
  assume "(a, b) \<in> Equivalence" "(b, c) \<in> Equivalence"
  then show "(a, c) \<in> Equivalence" unfolding Equivalence_def using disjoint by auto
qed

text \<open>Temporarily introduce equivalence associated to partition.\<close>
text \<open>p 12, ll 12--14\<close>
interpretation equivalence S Equivalence by (rule equivalence)

text \<open>p 12, ll 12--14\<close>
theorem Class_is_Block:
  assumes "a \<in> S" shows "Class a = Block a"
proof -
  from `a \<in> S` and block_exists obtain A where block: "a \<in> A \<and> A \<in> P" by blast
  show ?thesis
    apply (simp add: Block_def Class_def)
    apply (rule theI2)
      apply (rule block)
     apply (metis block block_unique)
    apply (auto dest: block_unique simp: Equivalence_def)
    done
qed

text \<open>p 12, l 14\<close>
lemma Class_equals_Block:
  "Class = Block"
proof
  fix x show "Class x = Block x"
  by (cases "x \<in> S") (auto simp: Class_is_Block)
qed

text \<open>p 12, l 14\<close>
theorem partition_of_equivalence:
  "Partition = P"
  by (auto simp add: Partition_def Class_equals_Block) (metis Block_self element_exists)

end (* partition *)

context equivalence begin

text \<open>p 12, ll 14--17\<close>
interpretation partition S Partition by (rule partition)

text \<open>p 12, ll 14--17\<close>
theorem equivalence_of_partition:
  "Equivalence = E"
  unfolding Equivalence_def unfolding Partition_def by auto (metis ClassD Class_closed Class_eq)

end (* equivalence *)

text \<open>p 12, l 14\<close>
sublocale partition \<subseteq> equivalence S Equivalence
  rewrites "equivalence.Partition S Equivalence = P" and "equivalence.Class S Equivalence = Block"
    apply (rule equivalence)
   apply (rule partition_of_equivalence)
  apply (rule Class_equals_Block)
  done

text \<open>p 12, ll 14--17\<close>
sublocale equivalence \<subseteq> partition S Partition
  rewrites "partition.Equivalence Partition = E" and "partition.Block S Partition = Class"
    apply (rule partition)
   apply (rule equivalence_of_partition)
  apply (metis equivalence_of_partition partition partition.Class_equals_Block)
  done

text \<open>Unfortunately only effective on input\<close>
text \<open>p 12, ll 18--20\<close>
notation equivalence.Partition (infixl "'/" 75)

context equivalence begin

text \<open>p 12, ll 18--20\<close>
lemma representant_exists [dest]: "A \<in> S / E \<Longrightarrow> \<exists>a\<in>S. a \<in> A \<and> A = Class a"
  by (metis Block_self element_exists)

text \<open>p 12, ll 18--20\<close>
lemma quotient_ClassE: "A \<in> S / E \<Longrightarrow> (\<And>a. a \<in> S \<Longrightarrow> P (Class a)) \<Longrightarrow> P A"
  using representant_exists by blast

end (* equivalence *)

text \<open>p 12, ll 21--23\<close>
sublocale equivalence \<subseteq> natural: surjective_map Class S "S / E"
  by unfold_locales force+

text \<open>Technical device to achieve Jacobson's syntax; context where @{text \<alpha>} is not a parameter.\<close>
text \<open>p 12, ll 25--26\<close>
locale fiber_relation_notation = fixes S :: "'a set" begin

text \<open>p 12, ll 25--26\<close>
definition Fiber_Relation ("E'(_')") where "Fiber_Relation \<alpha> = {(x, y). x \<in> S \<and> y \<in> S \<and> \<alpha> x = \<alpha> y}"

end (* fiber_relation_notation *)

text \<open>
  Context where classes and the induced map are defined through the fiber relation.
  This will be the case for monoid homomorphisms but not group homomorphisms.
\<close>
text \<open>Avoids infinite interpretation chain.\<close>
text \<open>p 12, ll 25--26\<close>
locale fiber_relation = map begin

text \<open>Install syntax\<close>
text \<open>p 12, ll 25--26\<close>
sublocale fiber_relation_notation .

text \<open>p 12, ll 26--27\<close>
sublocale equivalence where E = "E(\<alpha>)"
  unfolding Fiber_Relation_def by unfold_locales auto

text \<open>``define $\bar{\alpha}$ by $\bar{\alpha}(\bar{a}) = \alpha(a)$''\<close>
text \<open>p 13, ll 8--9\<close>
definition "induced = (\<lambda>A \<in> S / E(\<alpha>). THE b. \<exists>a \<in> A. b = \<alpha> a)"

text \<open>p 13, l 10\<close>
theorem Fiber_equality:
  "\<lbrakk> a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> Class a = Class b \<longleftrightarrow> \<alpha> a = \<alpha> b"
  unfolding Class_equivalence unfolding Fiber_Relation_def by simp

text \<open>p 13, ll 8--9\<close>
theorem induced_Fiber_simp [simp]:
  assumes [intro, simp]: "a \<in> S" shows "induced (Class a) = \<alpha> a"
proof -
  have "(THE b. \<exists>a\<in>Class a. b = \<alpha> a) = \<alpha> a"
    by (rule the_equality) (auto simp: Fiber_equality [symmetric] Block_self block_closed)
  then show ?thesis unfolding induced_def by simp
qed

text \<open>p 13, ll 10--11\<close>
interpretation induced: map induced "S / E(\<alpha>)" T
proof (unfold_locales, rule)
  fix A
  assume [intro, simp]: "A \<in> S / E(\<alpha>)"
  obtain a where a: "a \<in> S" "a \<in> A" using element_exists by auto
  have "(THE b. \<exists>a\<in>A. b = \<alpha> a) \<in> T"
    apply (rule theI2)
    using a apply (auto simp: Fiber_equality [symmetric] Block_self block_closed)
    done
  then show "induced A \<in> T" unfolding induced_def by simp
qed (simp add: induced_def)

text \<open>p 13, ll 12--13\<close>
sublocale induced: injective_map induced "S / E(\<alpha>)" T
  apply unfold_locales
  apply (rule inj_onI)
  apply (metis Fiber_equality Block_self element_exists induced_Fiber_simp)
  done

text \<open>p 13, ll 16--19\<close>
theorem factorization_lemma:
  "a \<in> S \<Longrightarrow> compose S induced Class a = \<alpha> a"
  by (simp add: compose_eq)

text \<open>p 13, ll 16--19\<close>
theorem factorization [simp]: "compose S induced Class = \<alpha>"
  by (rule ext) (simp add: compose_def)

text \<open>p 14, ll 2--4\<close>
theorem uniqueness:
  assumes map: "\<beta> \<in> S / E(\<alpha>) \<rightarrow>\<^sub>E T"
    and factorization: "compose S \<beta> Class = \<alpha>"
  shows "\<beta> = induced"
proof
  fix A
  show "\<beta> A = induced A"
  proof (cases "A \<in> S / E(\<alpha>)")
    case True
    then obtain a where [simp]: "A = Class a" "a \<in> S" by fast
    then have "\<beta> (Class a) = \<alpha> a" by (metis compose_eq factorization)
    also have "\<dots> = induced (Class a)" by simp
    finally show ?thesis by simp
  qed (simp add: induced_def PiE_arb [OF map])
qed

end (* fiber_relation *)

end
