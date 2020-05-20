section \<open>Library Additions\<close>
theory Analysis_More
  imports "HOL-Analysis.Equivalence_Lebesgue_Henstock_Integration"
    "HOL-Library.Function_Algebras"
    "HOL-Types_To_Sets.Linear_Algebra_On"
begin


lemma openin_open_Int'[intro]:
  "open S \<Longrightarrow> openin (top_of_set U) (S \<inter> U)"
  by (auto simp: openin_open)

subsection \<open>Parametricity rules for topology\<close>

text \<open>TODO: also check with theory \<open>Transfer_Euclidean_Space_Vector\<close> in AFP/ODE...\<close>

context includes lifting_syntax begin

lemma Sigma_transfer[transfer_rule]:
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set (rel_prod A B)) Sigma Sigma"
  unfolding Sigma_def
  by transfer_prover

lemma filterlim_transfer[transfer_rule]:
  "((A ===> B) ===> rel_filter B ===> rel_filter A ===> (=)) filterlim filterlim"
  if [transfer_rule]: "bi_unique B"
  unfolding filterlim_iff
  by transfer_prover

lemma nhds_transfer[transfer_rule]:
  "(A ===> rel_filter A) nhds nhds"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
  unfolding nhds_def
  by transfer_prover

lemma at_within_transfer[transfer_rule]:
  "(A ===> rel_set A ===> rel_filter A) at_within at_within"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
  unfolding at_within_def
  by transfer_prover

lemma continuous_on_transfer[transfer_rule]:
  "(rel_set A ===> (A ===> B) ===> (=)) continuous_on continuous_on"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
    "bi_unique B" "bi_total B" "(rel_set B ===> (=)) open open"
  unfolding continuous_on_def
  by transfer_prover

lemma continuous_on_transfer_right_total[transfer_rule]:
  "(rel_set A ===> (A ===> B) ===> (=)) (\<lambda>X::'a::t2_space set. continuous_on (X \<inter> Collect AP)) (\<lambda>Y::'b::t2_space set. continuous_on Y)"
  if DomainA: "Domainp A = AP"
    and [folded DomainA, transfer_rule]: "bi_unique A" "right_total A" "(rel_set A ===> (=)) (openin (top_of_set (Collect AP))) open"
    "bi_unique B" "bi_total B" "(rel_set B ===> (=)) open open"
  unfolding DomainA[symmetric]
proof (intro rel_funI)
  fix X Y f g
  assume H[transfer_rule]: "rel_set A X Y" "(A ===> B) f g"
  from H(1) have XA: "x \<in> X \<Longrightarrow> Domainp A x" for x
    by (auto simp: rel_set_def)
  then have *: "X \<inter> Collect (Domainp A) = X" by auto
  have "openin (top_of_set (Collect (Domainp A))) (Collect (Domainp A))" by auto
  show " continuous_on (X \<inter> Collect (Domainp A)) f = continuous_on Y g"
    unfolding continuous_on_eq_continuous_within continuous_within_topological *
    apply transfer
    apply safe
    subgoal for x B
      apply (drule bspec, assumption, drule spec, drule mp, assumption, drule mp, assumption)
      apply clarsimp
      subgoal for AA
        apply (rule exI[where x="AA \<inter> Collect (Domainp A)"])
        by (auto intro: XA)
      done
    subgoal using XA by (force simp: openin_subtopology)
    done
qed

lemma continuous_on_transfer_right_total2[transfer_rule]:
  "(rel_set A ===> (A ===> B) ===> (=)) (\<lambda>X::'a::t2_space set. continuous_on X) (\<lambda>Y::'b::t2_space set. continuous_on Y)"
  if DomainB: "Domainp B = BP"
  and [folded DomainB, transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
    "bi_unique B" "right_total B" "(rel_set B ===> (=)) ((openin (top_of_set (Collect BP)))) open"
  unfolding DomainB[symmetric]
proof (intro rel_funI)
  fix X Y f g
  assume H[transfer_rule]: "rel_set A X Y" "(A ===> B) f g"
  show "continuous_on X f = continuous_on Y g"
    unfolding continuous_on_eq_continuous_within continuous_within_topological
    apply transfer
    apply safe
    subgoal for x C
      apply (clarsimp simp: openin_subtopology)
      apply (drule bspec, assumption, drule spec, drule mp, assumption, drule mp, assumption)
      apply clarsimp
      by (meson Domainp_applyI H(1) H(2) rel_setD1)
    subgoal for x C
    proof -
      let ?sub = "top_of_set (Collect (Domainp B))"
      assume cont: "\<forall>x\<in>X. \<forall>Ba\<in>{A. Ball A (Domainp B)}.
          openin (top_of_set (Collect (Domainp B))) Ba \<longrightarrow> f x \<in> Ba \<longrightarrow> (\<exists>Aa.  open Aa \<and> x \<in> Aa \<and> (\<forall>y\<in>X. y \<in> Aa \<longrightarrow> f y \<in> Ba))"
        and x: "x \<in> X" "open C" "f x \<in> C"
      let ?B = "C \<inter> Collect (Domainp B)"
      have "?B \<in> {A. Ball A (Domainp B)}" by auto
      have "openin ?sub (Collect (Domainp B))" by auto
      then have "openin ?sub ?B" using \<open>open C\<close> by auto
      moreover have "f x \<in> ?B" using x
        apply transfer apply auto
        by (meson Domainp_applyI H(1) H(2) rel_setD1)
      ultimately obtain D where "open D \<and> x \<in> D \<and> (\<forall>y\<in>X. y \<in> D \<longrightarrow> f y \<in> ?B)"
        using cont x
        by blast
      then show "\<exists>A. open A \<and> x \<in> A \<and> (\<forall>y\<in>X. y \<in> A \<longrightarrow> f y \<in> C)" by auto
    qed
    done
qed


lemma generate_topology_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows "(rel_set (rel_set A) ===> rel_set A ===> (=)) (generate_topology o (insert (Collect (Domainp A)))) generate_topology"
proof (intro rel_funI)
  fix B C X Y assume t[transfer_rule]: "rel_set (rel_set A) B C" "rel_set A X Y"
  then have "X \<subseteq> Collect (Domainp A)" by (auto simp: rel_set_def)
  with t have rI: "rel_set A (X \<inter> Collect (Domainp A)) Y"
    by (auto simp: inf_absorb1)
  have eq_UNIV_I: "Z = UNIV" if [transfer_rule]: "rel_set A {a. Domainp A a} Z" for Z
    using that assms
    apply (auto simp: right_total_def rel_set_def)
    using bi_uniqueDr by fastforce
  show "(generate_topology \<circ> insert (Collect (Domainp A))) B X = generate_topology C Y"
    unfolding o_def
  proof (rule iffI)
    fix x
    assume "generate_topology (insert (Collect (Domainp A)) B) X"
    then show "generate_topology C Y" unfolding o_def
      using rI
    proof (induction X arbitrary: Y)
      case [transfer_rule]: UNIV
      with eq_UNIV_I[of Y] show ?case
        by (simp add: generate_topology.UNIV)
    next
      case (Int a b)
      note [transfer_rule] = Int(5)
      obtain a' where a'[transfer_rule]: "rel_set A (a \<inter> Collect (Domainp A)) a'"
        by (metis Domainp_iff Domainp_set Int_Collect)
      obtain b' where b'[transfer_rule]: "rel_set A (b \<inter> Collect (Domainp A)) b'"
        by (metis Domainp_iff Domainp_set Int_Collect)
      from Int.IH(1)[OF a'] Int.IH(2)[OF b']
      have "generate_topology C a'" "generate_topology C b'" by auto
      from generate_topology.Int[OF this] have "generate_topology C (a' \<inter> b')" .
      also have "a' \<inter> b' = Y"
        by transfer auto
      finally show ?case
        by (simp add: generate_topology.Int)
    next
      case (UN K)
      note [transfer_rule] = UN(3)
      have "\<exists>K'. \<forall>k. rel_set A (k \<inter> Collect (Domainp A)) (K' k)"
        by (rule choice) (metis Domainp_iff Domainp_set Int_Collect)
      then obtain K' where K': "\<And>k. rel_set A (k \<inter> Collect (Domainp A)) (K' k)" by metis
      from UN.IH[OF _ this] have "generate_topology C k'" if "k' \<in> K'`K" for k' using that by auto
      from generate_topology.UN[OF this] have "generate_topology C (\<Union>(K' ` K))" .
      also
      from K' have [transfer_rule]: "(rel_set (=) ===> rel_set A) (\<lambda>x. x \<inter> Collect (Domainp A)) K'"
        by (fastforce simp: rel_fun_def rel_set_def)
      have "\<Union>(K' ` K) = Y"
        by transfer auto
      finally show ?case
        by (simp add: generate_topology.UN)
    next
      case (Basis s)
      from this(1) show ?case
      proof
        assume "s = Collect (Domainp A)" 
        with eq_UNIV_I[of Y] Basis(2)
        show ?case
          by (simp add: generate_topology.UNIV)
      next
        assume "s \<in> B"
        with Basis(2) obtain t where [transfer_rule]: "rel_set A (s \<inter> Collect (Domainp A)) t" by auto
        from Basis(1) t(1) have s: "s \<inter> Collect (Domainp A) = s"
          by (force simp: rel_set_def)
        have "t \<in> C" using \<open>s \<in> B\<close> s
          by transfer auto
        also note [transfer_rule] = Basis(2)
        have "t = Y"
          by transfer auto
        finally show ?case
          by (rule generate_topology.Basis)
      qed
    qed
  next
    assume "generate_topology C Y"
    then show "generate_topology (insert (Collect (Domainp A)) B) X"
      using \<open>rel_set A X Y\<close>
    proof (induction arbitrary: X)
      case [transfer_rule]: UNIV
      have "UNIV = (UNIV::'b set)" by auto
      then have "X = {a. Domainp A a}" by transfer
      then show ?case by (intro generate_topology.Basis) auto
    next
      case (Int a b)
      obtain a' b' where [transfer_rule]: "rel_set A a' a" "rel_set A b' b"
        by (meson assms(1) right_total_def right_total_rel_set)
      from generate_topology.Int[OF Int.IH(1)[OF this(1)] Int.IH(2)[OF this(2)]]
      have "generate_topology (insert {a. Domainp A a} B) (a' \<inter> b')" by simp
      also
      define I where "I = a \<inter> b"
      from \<open>rel_set A X (a \<inter> b)\<close> have [transfer_rule]: "rel_set A X I" by (simp add: I_def)
      from I_def
      have "a' \<inter> b' = X" by transfer simp
      finally show ?case .
    next
      case (UN K)
      have "\<exists>K'. \<forall>k. rel_set A (K' k) k"
        by (rule choice) (meson assms(1) right_total_def right_total_rel_set)
      then obtain K' where K': "\<And>k. rel_set A (K' k) k" by metis
      from UN.IH[OF _ this] have "generate_topology (insert {a. Domainp A a} B) k"
        if "k \<in> K'`K" for k using that by auto
      from generate_topology.UN[OF this]
      have "generate_topology (insert {a. Domainp A a} B) (\<Union>(K'`K))" by auto
      also
      from K' have [transfer_rule]: "(rel_set (=) ===> rel_set A) K' id"
        by (fastforce simp: rel_fun_def rel_set_def)
      define U where "U =  (\<Union>(id ` K))"
      from \<open>rel_set A X _\<close> have [transfer_rule]: "rel_set A X U" by (simp add: U_def)
      from U_def have "\<Union>(K' ` K) = X" by transfer simp
      finally show ?case .
    next
      case (Basis s)
      note [transfer_rule] = \<open>rel_set A X s\<close>
      from \<open>s \<in> C\<close> have "X \<in> B" by transfer
      then show ?case by (intro generate_topology.Basis) auto
    qed
  qed
qed

end


subsection \<open>Miscellaneous\<close>

lemmas [simp del] = mem_ball

lemma in_closureI[intro, simp]: "x \<in> X \<Longrightarrow> x \<in> closure X"
  using closure_subset by auto

lemmas open_continuous_vimage = continuous_on_open_vimage[THEN iffD1, rule_format]
lemma open_continuous_vimage': "open s \<Longrightarrow> continuous_on s f \<Longrightarrow> open B \<Longrightarrow> open (s \<inter> f -` B)"
  using open_continuous_vimage[of s f B] by (auto simp: Int_commute)

lemma support_on_mono: "support_on carrier f \<subseteq> support_on carrier g"
  if "\<And>x. x \<in> carrier \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> g x \<noteq> 0"
  using that
  by (auto simp: support_on_def)


lemma image_prod: "(\<lambda>(x, y). (f x, g y)) ` (A \<times> B) = f ` A \<times> g ` B" by auto


subsection \<open>Closed support\<close>

definition "csupport_on X S = closure (support_on X S)"

lemma closed_csupport_on[intro, simp]: "closed (csupport_on carrier \<phi>)"
  by (auto simp: csupport_on_def)

lemma not_in_csupportD: "x \<notin> csupport_on carrier \<phi> \<Longrightarrow> x \<in> carrier \<Longrightarrow> \<phi> x = 0"
  by (auto simp: csupport_on_def support_on_def)

lemma csupport_on_mono: "csupport_on carrier f \<subseteq> csupport_on carrier g"
  if "\<And>x. x \<in> carrier \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> g x \<noteq> 0"
  unfolding csupport_on_def
  apply (rule closure_mono)
  using that
  by (rule support_on_mono)

subsection \<open>Homeomorphism\<close>

lemma homeomorphism_empty[simp]:
  "homeomorphism {} t f f' \<longleftrightarrow> t = {}"
  "homeomorphism s {} f f' \<longleftrightarrow> s = {}"
  by (auto simp: homeomorphism_def)

lemma homeomorphism_add:
  "homeomorphism UNIV UNIV (\<lambda>x. x + c) (\<lambda>x. x - c)"
  for c::"_::real_normed_vector"
  unfolding homeomorphism_def
  by (auto simp: algebra_simps continuous_intros intro!: image_eqI[where x="x - c" for x])

lemma in_range_scaleR_iff: "x \<in> range ((*\<^sub>R) c) \<longleftrightarrow> c = 0 \<longrightarrow> x = 0"
  for x::"_::real_vector"
  by (auto simp: intro!: image_eqI[where x="x /\<^sub>R c"])

lemma homeomorphism_scaleR:
  "homeomorphism UNIV UNIV (\<lambda>x. c *\<^sub>R x::_::real_normed_vector) (\<lambda>x. x /\<^sub>R c)"
  if "c \<noteq> 0"
  using that
  unfolding homeomorphism_def
  by (auto simp: in_range_scaleR_iff algebra_simps intro!: continuous_intros)


lemma homeomorphism_prod:
  "homeomorphism (a \<times> b) (c \<times> d) (\<lambda>(x, y). (f x, g y)) (\<lambda>(x, y). (f' x, g' y))"
  if "homeomorphism a c f f'"
     "homeomorphism b d g g'"
  using that by (simp add: homeomorphism_def image_prod)
    (auto simp add: split_beta intro!: continuous_intros elim: continuous_on_compose2)


subsection \<open>Generalizations\<close>

lemma openin_subtopology_eq_generate_topology:
  "openin (top_of_set S) x = generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) x"
  if open_gen: "open = generate_topology BB" and subset: "x \<subseteq> S"
proof -
  have "generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) (T \<inter> S)"
    if "generate_topology BB T"
    for T
    using that
  proof (induction)
    case UNIV
    then show ?case by (auto intro!: generate_topology.Basis)
  next
    case (Int a b)
    have "generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) (a \<inter> S \<inter> (b \<inter> S))"
      by (rule generate_topology.Int) (use Int in auto)
    then show ?case by (simp add: ac_simps)
  next
    case (UN K)
    then have "generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) (\<Union>k\<in>K. k \<inter> S)"
      by (intro generate_topology.UN) auto
    then show ?case by simp
  next
    case (Basis s)
    then show ?case
      by (intro generate_topology.Basis) auto
  qed
  moreover
  have "\<exists>T. generate_topology BB T \<and> x = T \<inter> S"
    if "generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) x" "x \<noteq> UNIV"
    using that
  proof (induction)
    case UNIV
    then show ?case by simp
  next
    case (Int a b)
    then show ?case
      using generate_topology.Int 
      by auto
  next
    case (UN K)
    from UN.IH have "\<forall>k\<in>K-{UNIV}. \<exists>T. generate_topology BB T \<and> k = T \<inter> S" by auto
    from this[THEN bchoice] obtain T where T: "\<And>k. k \<in> T ` (K - {UNIV}) \<Longrightarrow> generate_topology BB k" "\<And>k. k \<in> K - {UNIV} \<Longrightarrow> k = (T k) \<inter> S"
      by auto
    from generate_topology.UN[OF T(1)]
    have "generate_topology BB (\<Union>(T ` (K - {UNIV})))" by auto
    moreover have "\<Union>K = (\<Union>(T ` (K - {UNIV}))) \<inter> S" if "UNIV \<notin> K" using T(2) UN that by auto
    ultimately show ?case
      apply (cases "UNIV \<in> K") subgoal using UN by auto
      subgoal by auto
      done
  next
    case (Basis s)
    then show ?case
      using generate_topology.UNIV generate_topology.Basis by blast
  qed
  moreover
  have "\<exists>T. generate_topology BB T \<and> UNIV = T \<inter> S" if "generate_topology (insert S ((\<lambda>B. B \<inter> S) ` BB)) x"
     "x = UNIV"
  proof -
    have "S = UNIV"
      using that \<open>x \<subseteq> S\<close>
      by auto
    then show ?thesis by (simp add: generate_topology.UNIV)
  qed
  ultimately show ?thesis
    by (metis open_gen open_openin openin_open_Int' openin_subtopology)
qed

subsection \<open>Equal topologies\<close>

lemma topology_eq_iff: "t = s \<longleftrightarrow> (topspace t = topspace s \<and>
  (\<forall>x\<subseteq>topspace t. openin t x = openin s x))"
  by (metis (full_types) openin_subset topology_eq)


subsection \<open>Finer topologies\<close>

definition finer_than (infix "(finer'_than)" 50)
  where "T1 finer_than T2 \<longleftrightarrow> continuous_map T1 T2 (\<lambda>x. x)"

lemma finer_than_iff_nhds:
  "T1 finer_than T2 \<longleftrightarrow> (\<forall>X. openin T2 X \<longrightarrow> openin T1 (X \<inter> topspace T1)) \<and> (topspace T1 \<subseteq> topspace T2)"
  by (auto simp: finer_than_def continuous_map_alt)

lemma continuous_on_finer_topo:
  "continuous_map s t f"
  if "continuous_map s' t f" "s finer_than s'"
  using that
  by (auto simp: finer_than_def o_def dest: continuous_map_compose)

lemma continuous_on_finer_topo2:
  "continuous_map s t f"
  if "continuous_map s t' f" "t' finer_than t"
  using that
  by (auto simp: finer_than_def o_def dest: continuous_map_compose)

lemma antisym_finer_than: "S = T" if "S finer_than T" "T finer_than S"
  using that
  apply (auto simp: finer_than_def topology_eq_iff continuous_map_alt)
  apply (metis inf.orderE)+
  done

lemma subtopology_finer_than[simp]: "top_of_set X finer_than euclidean"
  by (auto simp: finer_than_iff_nhds openin_subtopology)

subsection \<open>Support\<close>

lemma support_on_nonneg_sum:
  "support_on X (\<lambda>x. \<Sum>i\<in>S. f i x) = (\<Union>i\<in>S. support_on X (f i))"
  if "finite S" "\<And>x i . x \<in> X \<Longrightarrow> i \<in> S \<Longrightarrow> f i x \<ge> 0"
  for f::"_\<Rightarrow>_\<Rightarrow>_::ordered_comm_monoid_add"
  using that by (auto simp: support_on_def sum_nonneg_eq_0_iff)

lemma support_on_nonneg_sum_subset:
  "support_on X (\<lambda>x. \<Sum>i\<in>S. f i x) \<subseteq> (\<Union>i\<in>S. support_on X (f i))"
  for f::"_\<Rightarrow>_\<Rightarrow>_::ordered_comm_monoid_add"
by (cases "finite S") (auto simp: support_on_def, meson sum.neutral)

lemma support_on_nonneg_sum_subset':
  "support_on X (\<lambda>x. \<Sum>i\<in>S x. f i x) \<subseteq> (\<Union>x\<in>X. (\<Union>i\<in>S x. support_on X (f i)))"
  for f::"_\<Rightarrow>_\<Rightarrow>_::ordered_comm_monoid_add"
  by (auto simp: support_on_def, meson sum.neutral)

subsection \<open>Final topology (Bourbaki, General Topology I, 4.)\<close>

definition "final_topology X Y f =
  topology (\<lambda>U. U \<subseteq> X \<and>
    (\<forall>i. openin (Y i) (f i -` U \<inter> topspace (Y i))))"

lemma openin_final_topology:
  "openin (final_topology X Y f) =
    (\<lambda>U. U \<subseteq> X \<and> (\<forall>i. openin (Y i) (f i -` U \<inter> topspace (Y i))))"
  unfolding final_topology_def
  apply (rule topology_inverse')
  unfolding istopology_def
proof safe
  fix S T i
  assume "\<forall>i. openin (Y i) (f i -` S \<inter> topspace (Y i))"
    "\<forall>i. openin (Y i) (f i -` T \<inter> topspace (Y i))"
  then have "openin (Y i) (f i -` S \<inter> topspace (Y i) \<inter> (f i -` T \<inter> topspace (Y i)))"
    (is "openin _ ?I")
    by auto
  also have "?I = f i -` (S \<inter> T) \<inter> topspace (Y i)"
    (is "_ = ?R")
    by auto
  finally show "openin (Y i) ?R" .
next
  fix K i
  assume "\<forall>U\<in>K. U \<subseteq> X \<and> (\<forall>i. openin (Y i) (f i -` U \<inter> topspace (Y i)))"
  then have "openin (Y i) (\<Union>X\<in>K. f i -` X \<inter> topspace (Y i))"
    by (intro openin_Union) auto
  then show "openin (Y i) (f i -` \<Union>K \<inter> topspace (Y i))"
    by (auto simp: vimage_Union)
qed force+

lemma topspace_final_topology:
  "topspace (final_topology X Y f) = X"
  if "\<And>i. f i \<in> topspace (Y i) \<rightarrow> X"
proof -
  have *: "f i -` X \<inter> topspace (Y i) = topspace (Y i)" for i
    using that
    by auto
  show ?thesis
    unfolding topspace_def
    unfolding openin_final_topology
    apply (rule antisym)
     apply force
    apply (rule subsetI)
    apply (rule UnionI[where X=X])
    using that
    by (auto simp: *)
qed

lemma continuous_on_final_topologyI2:
  "continuous_map (Y i) (final_topology X Y f) (f i)"
  if "\<And>i. f i \<in> topspace (Y i) \<rightarrow> X"
  using that
  by (auto simp: openin_final_topology continuous_map_alt topspace_final_topology)

lemma continuous_on_final_topologyI1:
  "continuous_map (final_topology X Y f) Z g"
  if hyp: "\<And>i. continuous_map (Y i) Z (g o f i)"
    and that: "\<And>i. f i \<in> topspace (Y i) \<rightarrow> X" "g \<in> X \<rightarrow> topspace Z"
  unfolding continuous_map_alt
proof safe
  fix V assume V: "openin Z V"
  have oV: "openin (Y i) (f i -` g -` V \<inter> topspace (Y i))"
    for i
    using hyp[rule_format, of i] V
    by (auto simp: continuous_map_alt vimage_comp dest!: spec[where x=V])
  have *: "f i -` g -` V \<inter> f i -` X \<inter> topspace (Y i) =
      f i -` g -` V \<inter> topspace (Y i)"
    (is "_ = ?rhs i")
    for i using that
    by auto
  show "openin (final_topology X Y f) (g -` V \<inter> topspace (final_topology X Y f))"
    by (auto simp: openin_final_topology oV topspace_final_topology that *)
qed (use that in \<open>auto simp: topspace_final_topology\<close>)


lemma continuous_on_final_topology_iff:
  "continuous_map (final_topology X Y f) Z g \<longleftrightarrow> (\<forall>i. continuous_map (Y i) Z (g o f i))"
  if "\<And>i. f i \<in> topspace (Y i) \<rightarrow> X" "g \<in> X \<rightarrow> topspace Z"
  using that
  by (auto intro!: continuous_on_final_topologyI1[OF _ that]
      intro: continuous_map_compose[OF continuous_on_final_topologyI2[OF that(1)]])


subsection \<open>Quotient topology\<close>

definition map_topology :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a topology \<Rightarrow> 'b topology" where
  "map_topology p X = final_topology (p ` topspace X) (\<lambda>_. X) (\<lambda>(_::unit). p)"

lemma openin_map_topology:
  "openin (map_topology p X) = (\<lambda>U. U \<subseteq> p ` topspace X \<and> openin X (p -` U \<inter> topspace X))"
  by (auto simp: map_topology_def openin_final_topology)

lemma topspace_map_topology[simp]: "topspace (map_topology f T) = f ` topspace T"
  unfolding map_topology_def
  by (subst topspace_final_topology) auto

lemma continuous_on_map_topology:
  "continuous_map T (map_topology f T) f"
  unfolding continuous_map_alt openin_map_topology
  by auto

lemma continuous_map_composeD:
  "continuous_map T X (g \<circ> f) \<Longrightarrow> g \<in> f ` topspace T \<rightarrow> topspace X"
  by (auto simp: continuous_map_def)

lemma continuous_on_map_topology2:
  "continuous_map T X (g \<circ> f) \<longleftrightarrow> continuous_map (map_topology f T) X g"
  unfolding map_topology_def
  apply safe
  subgoal
    apply (rule continuous_on_final_topologyI1)
    subgoal by assumption
    subgoal by force
    subgoal by (rule continuous_map_composeD)
    done
  subgoal
    apply (erule continuous_map_compose[rotated])
    apply (rule continuous_on_final_topologyI2)
    by force
  done

lemma map_sub_finer_than_commute:
  "map_topology f (subtopology T (f -` X)) finer_than subtopology (map_topology f T) X"
  by (auto simp: finer_than_def continuous_map_def openin_subtopology openin_map_topology
      topspace_subtopology)

lemma sub_map_finer_than_commute:
  "subtopology (map_topology f T) X finer_than map_topology f (subtopology T (f -` X))"
  if "openin T (f -` X)"\<comment> \<open>this is more or less the condition from
    \<^url>\<open>https://math.stackexchange.com/questions/705840/quotient-topology-vs-subspace-topology\<close>\<close>
  unfolding finer_than_def continuous_map_alt
proof (rule conjI, clarsimp)
  fix U
  assume "openin (map_topology f (subtopology T (f -` X))) U"
  then obtain W where W: "U \<subseteq> f ` (topspace T \<inter> f -` X)" "openin T W" "f -` U \<inter> (topspace T \<inter> f -` X) = W \<inter> f -` X"
    by (auto simp: topspace_subtopology openin_subtopology openin_map_topology)
  have "(f -` f ` W \<inter> f -` X) \<inter> topspace T = W \<inter> topspace T \<inter> f -` X"
    apply auto
    by (metis Int_iff W(3) vimage_eq)
  also have "openin T \<dots>"
    by (auto intro!: W that)
  finally show "openin (subtopology (map_topology f T) X) (U \<inter> (f ` topspace T \<inter> X))"
    using W
    unfolding topspace_subtopology topspace_map_topology openin_subtopology openin_map_topology
    by (intro exI[where x="(f ` W \<inter> X)"]) auto
qed auto

lemma subtopology_map_topology:
  "subtopology (map_topology f T) X = map_topology f (subtopology T (f -` X))"
  if "openin T (f -` X)"
  apply (rule antisym_finer_than)
  using sub_map_finer_than_commute[OF that] map_sub_finer_than_commute[of f T X]
  by auto

lemma quotient_map_map_topology:
  "quotient_map X (map_topology f X) f"
  by (auto simp: quotient_map_def openin_map_topology ac_simps)
    (simp_all add: vimage_def Int_def)

lemma topological_space_quotient: "class.topological_space (openin (map_topology f euclidean))"
  if "surj f"
  apply standard
    apply (auto simp: )
  using that
  by (auto simp: openin_map_topology)

lemma t2_space_quotient: "class.t2_space (open::'b set \<Rightarrow> bool)"
  if open_def: "open = (openin (map_topology (p::'a::t2_space\<Rightarrow>'b::topological_space) euclidean))"
    "surj p" and open_p: "\<And>X. open X \<Longrightarrow> open (p ` X)" and "closed {(x, y). p x = p y}" (is "closed ?R")
  apply (rule class.t2_space.intro)
  subgoal by (unfold open_def, rule topological_space_quotient; fact)
proof standard
  fix a b::'b
  obtain x y where a_def: "a = p x" and b_def: "b = p y" using \<open>surj p\<close> by fastforce
  assume "a \<noteq> b"
  with \<open>closed ?R\<close> have "open (-?R)" "(x, y) \<in> -?R" by (auto simp add: a_def b_def)
  from open_prod_elim[OF this]
  obtain N\<^sub>x N\<^sub>y where "open N\<^sub>x" "open N\<^sub>y" "(x, y) \<in> N\<^sub>x \<times> N\<^sub>y" "N\<^sub>x \<times> N\<^sub>y \<subseteq> -?R" .
  then have "p ` N\<^sub>x \<inter> p ` N\<^sub>y = {}" by auto
  moreover
  from \<open>open N\<^sub>x\<close> \<open>open N\<^sub>y\<close> have "open (p ` N\<^sub>x)" "open (p ` N\<^sub>y)"
    using open_p by blast+
  moreover have "a \<in> p ` N\<^sub>x" "b \<in> p ` N\<^sub>y" using \<open>(x, y) \<in> _ \<times> _\<close> by (auto simp: a_def b_def)
  ultimately show "\<exists>U V. open U \<and> open V \<and> a \<in> U \<and> b \<in> V \<and> U \<inter> V = {}" by blast
qed

lemma second_countable_topology_quotient: "class.second_countable_topology (open::'b set \<Rightarrow> bool)"
  if open_def: "open = (openin (map_topology (p::'a::second_countable_topology\<Rightarrow>'b::topological_space) euclidean))"
    "surj p" and open_p: "\<And>X. open X \<Longrightarrow> open (p ` X)"
  apply (rule class.second_countable_topology.intro)
  subgoal by (unfold open_def, rule topological_space_quotient; fact)
proof standard
  have euclidean_def: "euclidean = map_topology p euclidean"
    by (simp add: openin_inverse open_def)
  have continuous_on: "continuous_on UNIV p"
    using continuous_map_iff_continuous2 continuous_on_map_topology euclidean_def by fastforce
  from ex_countable_basis[where 'a='a] obtain A::"'a set set" where "countable A" "topological_basis A"
    by auto
  define B where "B = (\<lambda>X. p ` X) ` A"
  have "countable (B::'b set set)"
    by (auto simp: B_def intro!: \<open>countable A\<close>)
  moreover have "topological_basis B"
  proof (rule topological_basisI)
    fix B' assume "B' \<in> B" then show "open B'" using \<open>topological_basis A\<close>
      by (auto simp: B_def topological_basis_open intro!: open_p)
  next
    fix x::'b and O' assume "open O'" "x \<in> O'"
    have "open (p -` O')"
      using \<open>open O'\<close>
      by (rule open_vimage) (auto simp: continuous_on)
    obtain y where y: "y \<in> p -` {x}"
      using \<open>x \<in> O'\<close>
      by auto (metis UNIV_I open_def(2) rangeE)
    then have "y \<in> p -` O'" using \<open>x \<in> O'\<close> by auto
    from topological_basisE[OF \<open>topological_basis A\<close> \<open>open (p -` O')\<close> this]
    obtain C where "C \<in> A" "y \<in> C" "C \<subseteq> p -` O'" .
    let ?B' = "p ` C"
    have "?B' \<in> B"
      using \<open>C \<in> A\<close> by (auto simp: B_def)
    moreover
    have "x \<in> ?B'" using y \<open>y \<in> C\<close> \<open>x \<in> O'\<close>
      by auto
    moreover
    have "?B' \<subseteq> O'"
      using \<open>C \<subseteq> _\<close> by auto
    ultimately show "\<exists>B'\<in>B. x \<in> B' \<and> B' \<subseteq> O'" by metis
  qed
  ultimately show "\<exists>B::'b set set. countable B \<and> open = generate_topology B"
    by (auto simp: topological_basis_imp_subbasis)
qed


subsection \<open>Closure\<close>

lemma closure_Union: "closure (\<Union>X) = (\<Union>x\<in>X. closure x)" if "finite X"
  using that
  by (induction X) auto

subsection \<open>Compactness\<close>

lemma compact_if_closed_subset_of_compact:
  "compact S" if "closed S" "compact T" "S \<subseteq> T"
proof (rule compactI)
  fix UU assume UU: "\<forall>t\<in>UU. open t" "S \<subseteq> \<Union>UU"
  have "T \<subseteq> \<Union>(insert (- S) (UU))" "\<And>B. B \<in> insert (- S) UU \<Longrightarrow> open B"
    using UU \<open>S \<subseteq> T\<close>
    by (auto simp: open_Compl \<open>closed S\<close>)
  from compactE[OF \<open>compact T\<close> this]
  obtain \<T>' where \<T>: "\<T>' \<subseteq> insert (- S) UU" "finite \<T>'" "T \<subseteq> \<Union>\<T>'"
    by metis
  show "\<exists>C'\<subseteq>UU. finite C' \<and> S \<subseteq> \<Union>C'"
    apply (rule exI[where x="\<T>' - {-S}"])
    using \<T> UU
    apply auto
  proof -
    fix x assume "x \<in> S"
    with \<T> \<open>S \<subseteq> T\<close> obtain U where "x \<in> U" "U \<in> \<T>'" using \<T>
      by auto
    then show "\<exists>X\<in>\<T>' - {- S}. x \<in> X"
      using \<T> UU \<open>x \<in> S\<close>
      apply -
      apply (rule bexI[where x=U])
      by auto
  qed
qed

subsection \<open>Locally finite\<close>

definition "locally_finite_on X I U \<longleftrightarrow> (\<forall>p\<in>X. \<exists>N. p\<in>N \<and> open N \<and> finite {i\<in>I. U i \<inter> N \<noteq> {}})"

lemmas locally_finite_onI = locally_finite_on_def[THEN iffD2, rule_format]

lemma locally_finite_onE:
  assumes "locally_finite_on X I U"
  assumes "p \<in> X"
  obtains N where "p \<in> N" "open N" "finite {i\<in>I. U i \<inter> N \<noteq> {}}"
  using assms
  by (auto simp: locally_finite_on_def)

lemma locally_finite_onD:
  assumes "locally_finite_on X I U"
  assumes "p \<in> X"
  shows "finite {i\<in>I. p \<in> U i}"
  apply (rule locally_finite_onE[OF assms])
  apply (rule finite_subset)
  by auto

lemma locally_finite_on_open_coverI: "locally_finite_on X I U"
  if fin: "\<And>j. j \<in> I \<Longrightarrow> finite {i\<in>I. U i \<inter> U j \<noteq> {}}"
    and open_cover: "X \<subseteq> (\<Union>i\<in>I. U i)" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
proof (rule locally_finite_onI)
  fix p assume "p \<in> X"
  then obtain i where i: "i \<in> I" "p \<in> U i" "open (U i)"
    using open_cover
    by blast
  show "\<exists>N. p \<in> N \<and> open N \<and> finite {i \<in> I. U i \<inter> N \<noteq> {}}"
    by (intro exI[where x="U i"] conjI i fin)
qed

lemma locally_finite_compactD:
  "finite {i\<in>I. U i \<inter> V \<noteq> {}}"
  if lf: "locally_finite_on X I U"
    and compact: "compact V"
    and subset: "V \<subseteq> X"
proof -
  have "\<exists>N. \<forall>p \<in> X. p \<in> N p \<and> open (N p) \<and> finite {i\<in>I. U i \<inter> N p \<noteq> {}}"
    by (rule bchoice) (auto elim!: locally_finite_onE[OF lf, rule_format])
  then obtain N where N: "\<And>p. p \<in> X \<Longrightarrow> p \<in> N p"
    "\<And>p. p \<in> X \<Longrightarrow> open (N p)"
    "\<And>p. p \<in> X \<Longrightarrow> finite {i\<in>I. U i \<inter> N p \<noteq> {}}"
    by blast
  have "V \<subseteq> (\<Union>p\<in>X. N p)" "\<And>B. B \<in> N ` X \<Longrightarrow> open B"
    using N subset by force+
  from compactE[OF compact this]
  obtain C where C: "C \<subseteq> X" "finite C" "V \<subseteq> \<Union>(N ` C)"
    by (metis finite_subset_image)
  then have "{i\<in>I. U i \<inter> V \<noteq> {}} \<subseteq> {i\<in>I. U i \<inter> \<Union>(N ` C) \<noteq> {}}"
    by force
  also have "\<dots> \<subseteq> (\<Union>c\<in>C. {i\<in>I. U i \<inter> N c \<noteq> {}})"
    by force
  also have "finite \<dots>"
    apply (rule finite_Union)
    using C by (auto intro!: C N)
  finally (finite_subset) show ?thesis .
qed

lemma closure_Int_open_eq_empty: "open S \<Longrightarrow> (closure T \<inter> S) = {} \<longleftrightarrow> T \<inter> S = {}"
  by (auto simp: open_Int_closure_eq_empty ac_simps)

lemma locally_finite_on_subset:
  assumes "locally_finite_on X J U"
  assumes "\<And>i. i \<in> I \<Longrightarrow> V i \<subseteq> U i" "I \<subseteq> J"
  shows "locally_finite_on X I V"
proof (rule locally_finite_onI)
  fix p assume "p \<in> X"
  from locally_finite_onE[OF assms(1) this]
  obtain N where "p \<in> N" "open N" "finite {i \<in> J. U i \<inter> N \<noteq> {}}" .
  then show "\<exists>N. p \<in> N \<and> open N \<and> finite {i \<in> I. V i \<inter> N \<noteq> {}}"
    apply (intro exI[where x=N])
    using assms
    by (auto elim!: finite_subset[rotated])
qed

lemma locally_finite_on_closure:
  "locally_finite_on X I (\<lambda>x. closure (U x))"
  if "locally_finite_on X I U"
proof (rule locally_finite_onI)
  fix p assume "p \<in> X"
  from locally_finite_onE[OF that this] obtain N
    where "p \<in> N" "open N" "finite {i \<in> I. U i \<inter> N \<noteq> {}}" .
  then show "\<exists>N. p \<in> N \<and> open N \<and> finite {i \<in> I. closure (U i) \<inter> N \<noteq> {}}"
    by (auto intro!: exI[where x=N] simp: closure_Int_open_eq_empty)
qed


lemma locally_finite_on_closedin_Union_closure:
  "closedin (top_of_set X) (\<Union>i\<in>I. closure (U i))"
  if "locally_finite_on X I U" "\<And>i. i \<in> I \<Longrightarrow> closure (U i) \<subseteq> X"
  unfolding closedin_def
  apply safe
  subgoal using that(2) by auto
  subgoal
    apply (subst openin_subopen)
  proof clarsimp
    fix x
    assume x: "x \<in> X" "\<forall>i\<in>I. x \<notin> closure (U i)"
    from locally_finite_onE[OF that(1) \<open>x \<in> X\<close>]
    obtain N where N: "x \<in> N" "open N" "finite {i \<in> I. U i \<inter> N \<noteq> {}}" (is "finite ?I").
    define N' where "N' = N - (\<Union>i \<in> ?I. closure (U i))"
    have "open N'"
      by (auto simp: N'_def intro!: N)
    then have "openin (top_of_set X) (X \<inter> N')"
      by (rule openin_open_Int)
    moreover
    have "x \<in> X \<inter> N'" using x
      by (auto simp: N'_def N)
    moreover
    have "X \<inter> N' \<subseteq> X - (\<Union>i\<in>I. closure (U i))"
      using x that(2)
      apply (auto simp: N'_def)
      by (meson N(2) closure_iff_nhds_not_empty dual_order.refl)
    ultimately show "\<exists>T. openin (top_of_set X) T \<and> x \<in> T \<and> T \<subseteq> X - (\<Union>i\<in>I. closure (U i))"
      by auto
  qed
  done

lemma closure_subtopology_minimal:
  "S \<subseteq> T \<Longrightarrow> closedin (top_of_set X) T \<Longrightarrow> closure S \<inter> X \<subseteq> T"
  apply (auto simp: closedin_closed)
  using closure_minimal by blast

lemma locally_finite_on_closure_Union:
  "(\<Union>i\<in>I. closure (U i)) = closure (\<Union>i\<in>I. (U i)) \<inter> X"
  if "locally_finite_on X I U" "\<And>i. i \<in> I \<Longrightarrow> closure (U i) \<subseteq> X"
proof (rule antisym)
  show "(\<Union>i\<in>I. closure (U i)) \<subseteq> closure (\<Union>i\<in>I. U i) \<inter> X"
    using that
    apply auto
    by (metis (no_types, lifting) SUP_le_iff closed_closure closure_minimal closure_subset subsetCE)
  show "closure (\<Union>i\<in>I. U i) \<inter> X \<subseteq> (\<Union>i\<in>I. closure (U i))"
    apply (rule closure_subtopology_minimal)
    apply auto
    using that
    by (auto intro!: locally_finite_on_closedin_Union_closure)
qed


subsection \<open>Refinement of cover\<close>

definition refines :: "'a set set \<Rightarrow> 'a set set \<Rightarrow> bool" (infix "refines" 50)
  where "A refines B \<longleftrightarrow> (\<forall>s\<in>A. (\<exists>t. t \<in> B \<and> s \<subseteq> t))"

lemma refines_subset: "x refines y" if "z refines y" "x \<subseteq> z"
  using that by (auto simp: refines_def)

subsection \<open>Functions as vector space\<close>

instantiation "fun" :: (type, scaleR) scaleR begin

definition scaleR_fun :: "real \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
  "scaleR_fun r f = (\<lambda>x. r *\<^sub>R f x)"

lemma scaleR_fun_beta[simp]: "(r *\<^sub>R f) x = r *\<^sub>R f x"
  by (simp add: scaleR_fun_def)

instance ..

end

instance "fun" :: (type, real_vector) real_vector
  by standard (auto simp: scaleR_fun_def algebra_simps)


subsection \<open>Additional lemmas\<close>

lemmas [simp del] = vimage_Un vimage_Int

lemma finite_Collect_imageI: "finite {U \<in> f ` X. P U}" if "finite {x\<in>X. P (f x)}"
proof -
  have "{d \<in> f ` X. P d} \<subseteq> f ` {c \<in> X. P (f c)}"
    by blast
  then show ?thesis
    using finite_surj that by blast
qed

lemma plus_compose: "(x + y) \<circ> f = (x \<circ> f) + (y \<circ> f)"
  by auto

lemma mult_compose: "(x * y) \<circ> f = (x \<circ> f) * (y \<circ> f)"
  by auto

lemma scaleR_compose: "(c *\<^sub>R x) \<circ> f = c *\<^sub>R (x \<circ> f)"
  by (auto simp:)

lemma image_scaleR_ball:
  fixes a :: "'a::real_normed_vector"
  shows "c \<noteq> 0 \<Longrightarrow> (*\<^sub>R) c ` ball a r = ball (c *\<^sub>R a) (abs c *\<^sub>R r)"
proof (auto simp: mem_ball dist_norm, goal_cases)
  case (1 b)
  have "norm (c *\<^sub>R a - c *\<^sub>R b)  = abs c * norm (a - b)"
    by (auto simp: norm_scaleR[symmetric] algebra_simps simp del: norm_scaleR)
  also have "\<dots> < abs c * r"
    apply (rule mult_strict_left_mono)
    using 1 by auto
  finally show ?case .
next
  case (2 x)
  have "norm (a - x /\<^sub>R c) < r"
  proof -
    have "norm (a - x /\<^sub>R c) = abs c *\<^sub>R norm (a - x /\<^sub>R c) /\<^sub>R abs c"
      using 2 by auto
    also have "abs c *\<^sub>R norm (a - x /\<^sub>R c) = norm (c *\<^sub>R a - x)"
      using 2
      by (auto simp: norm_scaleR[symmetric] algebra_simps simp del: norm_scaleR)
    also have "\<dots> < \<bar>c\<bar> * r"
      by fact
    also have "\<bar>c\<bar> * r /\<^sub>R \<bar>c\<bar> = r" using 2 by auto
    finally show ?thesis using 2 by auto
  qed
  then have xdc: "x /\<^sub>R c \<in> ball a r"
    by (auto simp: mem_ball dist_norm)
  show ?case
    apply (rule image_eqI[OF _ xdc])
    using 2 by simp
qed


subsection \<open>Continuity\<close>

lemma continuous_within_topologicalE:
  assumes "continuous (at x within s) f"
    "open B" "f x \<in> B"
  obtains A where "open A" "x \<in> A" "\<And>y. y \<in> s \<Longrightarrow> y \<in> A \<Longrightarrow> f y \<in> B"
  using assms continuous_within_topological by metis

lemma continuous_within_topologicalE':
  assumes "continuous (at x) f"
    "open B" "f x \<in> B"
  obtains A where "open A" "x \<in> A" "f ` A \<subseteq> B"
  using assms continuous_within_topologicalE[OF assms]
  by (metis UNIV_I image_subsetI)

lemma continuous_on_inverse: "continuous_on S f \<Longrightarrow> 0 \<notin> f ` S \<Longrightarrow> continuous_on S (\<lambda>x. inverse (f x))"
  for f::"_\<Rightarrow>_::real_normed_div_algebra"
  by (auto simp: continuous_on_def intro!: tendsto_inverse)


subsection \<open>@{term "(has_derivative)"}\<close>

lemma has_derivative_plus_fun[derivative_intros]:
  "(x + y has_derivative x' + y') (at a within A)"
  if [derivative_intros]:
    "(x has_derivative x') (at a within A)"
    "(y has_derivative y') (at a within A)"
  by (auto simp: plus_fun_def intro!: derivative_eq_intros)

lemma has_derivative_scaleR_fun[derivative_intros]:
  "(x *\<^sub>R y has_derivative x *\<^sub>R y') (at a within A)"
  if [derivative_intros]:
    "(y has_derivative y') (at a within A)"
  by (auto simp: scaleR_fun_def intro!: derivative_eq_intros)

lemma has_derivative_times_fun[derivative_intros]:
  "(x * y has_derivative (\<lambda>h. x a * y' h + x' h * y a)) (at a within A)"
  if [derivative_intros]:
    "(x has_derivative x') (at a within A)"
    "(y has_derivative y') (at a within A)"
  for x y::"_\<Rightarrow>'a::real_normed_algebra"
  by (auto simp: times_fun_def intro!: derivative_eq_intros)

lemma real_sqrt_has_derivative_generic:
  "x \<noteq> 0 \<Longrightarrow> (sqrt has_derivative (*) ((if x > 0 then 1 else -1) * inverse (sqrt x) / 2)) (at x within S)"
  apply (rule has_derivative_at_withinI)
  using DERIV_real_sqrt_generic[of x "(if x > 0 then 1 else -1) * inverse (sqrt x) / 2"] at_within_open[of x "UNIV - {0}"]
  by (auto simp: has_field_derivative_def open_delete ac_simps split: if_splits)

lemma sqrt_has_derivative:
  "((\<lambda>x. sqrt (f x)) has_derivative (\<lambda>xa. (if 0 < f x then 1 else - 1) / (2 * sqrt (f x)) * f' xa)) (at x within S)"
  if "(f has_derivative f') (at x within S)" "f x \<noteq> 0"
  by (rule has_derivative_eq_rhs[OF has_derivative_compose[OF that(1) real_sqrt_has_derivative_generic, OF that(2)]])
    (auto simp: divide_simps)

lemmas has_derivative_norm_compose[derivative_intros] = has_derivative_compose[OF _ has_derivative_norm]

subsection \<open>Differentiable\<close>

lemmas differentiable_on_empty[simp]

lemma differentiable_transform_eventually: "f differentiable (at x within X)"
  if "g differentiable (at x within X)"
    "f x = g x"
    "\<forall>\<^sub>F x in (at x within X). f x = g x"
  using that
  apply (auto simp: differentiable_def)
  subgoal for D
    apply (rule exI[where x=D])
    apply (auto simp: has_derivative_within)
    by (simp add: eventually_mono Lim_transform_eventually)
  done

lemma differentiable_within_eqI: "f differentiable at x within X"
  if "g differentiable at x within X" "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
    "x \<in> X" "open X"
  apply (rule differentiable_transform_eventually)
    apply (rule that)
   apply (auto simp: that)
proof -
  have "\<forall>\<^sub>F x in at x within X. x \<in> X"
    using \<open>open X\<close>
    using eventually_at_topological by blast
  then show " \<forall>\<^sub>F x in at x within X. f x = g x"
    by eventually_elim (auto simp: that)
qed

lemma differentiable_eqI: "f differentiable at x"
  if "g differentiable at x" "\<And>x. x \<in> X \<Longrightarrow> f x = g x" "x \<in> X" "open X"
  using that
  unfolding at_within_open[OF that(3,4), symmetric]
  by (rule differentiable_within_eqI)

lemma differentiable_on_eqI:
  "f differentiable_on S"
  if "g differentiable_on S" "\<And>x. x \<in> S \<Longrightarrow> f x = g x" "open S"
  using that differentiable_eqI[of g _ S f]
  by (auto simp: differentiable_on_eq_differentiable_at)

lemma differentiable_on_comp: "(f o g) differentiable_on S"
  if "g differentiable_on S" "f differentiable_on (g ` S)"
  using that
  by (auto simp: differentiable_on_def intro: differentiable_chain_within)

lemma differentiable_on_comp2: "(f o g) differentiable_on S"
  if  "f differentiable_on T" "g differentiable_on S" "g ` S \<subseteq> T"
  apply (rule differentiable_on_comp)
   apply (rule that)
  apply (rule differentiable_on_subset)
  apply (rule that)
  apply (rule that)
  done

lemmas differentiable_on_compose2 = differentiable_on_comp2[unfolded o_def]

lemma differentiable_on_openD: "f differentiable at x"
  if "f differentiable_on X" "open X" "x \<in> X"
  using differentiable_on_eq_differentiable_at that by blast

lemma differentiable_on_add_fun[intro, simp]:
  "x differentiable_on UNIV \<Longrightarrow> y differentiable_on UNIV \<Longrightarrow> x + y differentiable_on UNIV"
  by (auto simp: plus_fun_def)

lemma differentiable_on_mult_fun[intro, simp]:
  "x differentiable_on UNIV \<Longrightarrow> y differentiable_on UNIV \<Longrightarrow> x * y differentiable_on UNIV"
  for x y::"_\<Rightarrow>'a::real_normed_algebra"
  by (auto simp: times_fun_def)

lemma differentiable_on_scaleR_fun[intro, simp]:
  "y differentiable_on UNIV \<Longrightarrow> x *\<^sub>R y differentiable_on UNIV"
  by (auto simp: scaleR_fun_def)

lemma sqrt_differentiable:
  "(\<lambda>x. sqrt (f x)) differentiable (at x within S)"
  if "f differentiable (at x within S)" "f x \<noteq> 0"
  using that
  using sqrt_has_derivative[of f _ x S]
  by (auto simp: differentiable_def)

lemma sqrt_differentiable_on: "(\<lambda>x. sqrt (f x)) differentiable_on S"
  if "f differentiable_on S" "0 \<notin> f ` S"
  using sqrt_differentiable[of f _ S] that
  by (force simp: differentiable_on_def)

lemma differentiable_on_inverse: "f differentiable_on S \<Longrightarrow> 0 \<notin> f ` S \<Longrightarrow> (\<lambda>x. inverse (f x)) differentiable_on S"
  for f::"_\<Rightarrow>_::real_normed_field"
  by (auto simp: differentiable_on_def intro!: differentiable_inverse)

lemma differentiable_on_openI:
  "f differentiable_on S"
  if "open S" "\<And>x. x \<in> S \<Longrightarrow> \<exists>f'. (f has_derivative f') (at x)"
  using that
  by (auto simp: differentiable_on_def at_within_open[where S=S] differentiable_def)

lemmas differentiable_norm_compose_at = differentiable_compose[OF differentiable_norm_at]

lemma differentiable_on_Pair:
  "f differentiable_on S \<Longrightarrow> g differentiable_on S \<Longrightarrow> (\<lambda>x. (f x, g x)) differentiable_on S"
  unfolding differentiable_on_def
  using differentiable_Pair[of f _ S g] by auto

lemma differentiable_at_fst:
  "(\<lambda>x. fst (f x)) differentiable at x within X" if "f differentiable at x within X"
  using that
  by (auto simp: differentiable_def dest!: has_derivative_fst)

lemma differentiable_at_snd:
  "(\<lambda>x. snd (f x)) differentiable at x within X" if "f differentiable at x within X"
  using that
  by (auto simp: differentiable_def dest!: has_derivative_snd)

lemmas frechet_derivative_worksI = frechet_derivative_works[THEN iffD1]

lemma sin_differentiable_at: "(\<lambda>x. sin (f x::real)) differentiable at x within X"
  if "f differentiable at x within X"
  using differentiable_def has_derivative_sin that by blast

lemma cos_differentiable_at: "(\<lambda>x. cos (f x::real)) differentiable at x within X"
  if "f differentiable at x within X"
  using differentiable_def has_derivative_cos that by blast


subsection \<open>Frechet derivative\<close>

lemmas frechet_derivative_transform_within_open_ext =
  fun_cong[OF frechet_derivative_transform_within_open]

lemmas frechet_derivative_at' = frechet_derivative_at[symmetric]

lemma frechet_derivative_plus_fun:
  "x differentiable at a \<Longrightarrow> y differentiable at a \<Longrightarrow>
  frechet_derivative (x + y) (at a) =
    frechet_derivative x (at a) + frechet_derivative y (at a)"
  by (rule frechet_derivative_at')
    (auto intro!: derivative_eq_intros frechet_derivative_worksI)

lemmas frechet_derivative_plus = frechet_derivative_plus_fun[unfolded plus_fun_def]

lemma frechet_derivative_zero_fun: "frechet_derivative 0 (at a) = 0"
  by (auto simp: frechet_derivative_const zero_fun_def)

lemma frechet_derivative_sin:
  "frechet_derivative (\<lambda>x. sin (f x)) (at x) = (\<lambda>xa. frechet_derivative f (at x) xa * cos (f x))"
  if "f differentiable (at x)"
  for f::"_\<Rightarrow>real"
  by (rule frechet_derivative_at'[OF has_derivative_sin[OF frechet_derivative_worksI[OF that]]])

lemma frechet_derivative_cos:
  "frechet_derivative (\<lambda>x. cos (f x)) (at x) = (\<lambda>xa. frechet_derivative f (at x) xa * - sin (f x))"
  if "f differentiable (at x)"
  for f::"_\<Rightarrow>real"
  by (rule frechet_derivative_at'[OF has_derivative_cos[OF frechet_derivative_worksI[OF that]]])

lemma differentiable_sum_fun:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i differentiable at a)) \<Longrightarrow> sum f I differentiable at a"
  by (induction I rule: infinite_finite_induct) (auto simp: zero_fun_def plus_fun_def)

lemma frechet_derivative_sum_fun:
  "(\<And>i. i \<in> I \<Longrightarrow> (f i differentiable at a)) \<Longrightarrow>
  frechet_derivative (\<Sum>i\<in>I. f i) (at a) = (\<Sum>i\<in>I. frechet_derivative (f i) (at a))"
  by (induction I rule: infinite_finite_induct)
    (auto simp: frechet_derivative_zero_fun frechet_derivative_plus_fun differentiable_sum_fun)

lemma sum_fun_def: "(\<Sum>i\<in>I. f i) = (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induction I rule: infinite_finite_induct) auto

lemmas frechet_derivative_sum = frechet_derivative_sum_fun[unfolded sum_fun_def]


lemma frechet_derivative_times_fun:
  "f differentiable at a \<Longrightarrow> g differentiable at a \<Longrightarrow>
  frechet_derivative (f * g) (at a) =
  (\<lambda>x. f a * frechet_derivative g (at a) x + frechet_derivative f (at a) x * g a)"
  for f g::"_\<Rightarrow>'a::real_normed_algebra"
  by (rule frechet_derivative_at') (auto intro!: derivative_eq_intros frechet_derivative_worksI)

lemmas frechet_derivative_times = frechet_derivative_times_fun[unfolded times_fun_def]

lemma frechet_derivative_scaleR_fun:
  "y differentiable at a \<Longrightarrow>
  frechet_derivative (x *\<^sub>R y) (at a) =
    x *\<^sub>R frechet_derivative y (at a)"
  by (rule frechet_derivative_at')
    (auto intro!: derivative_eq_intros frechet_derivative_worksI)

lemmas frechet_derivative_scaleR = frechet_derivative_scaleR_fun[unfolded scaleR_fun_def]

lemma frechet_derivative_compose:
  "frechet_derivative (f o g) (at x) = frechet_derivative (f) (at (g x)) o frechet_derivative g (at x)"
  if "g differentiable at x" "f differentiable at (g x)"
  by (meson diff_chain_at frechet_derivative_at' frechet_derivative_works that)

lemma frechet_derivative_compose_eucl:
  "frechet_derivative (f o g) (at x) =
    (\<lambda>v. \<Sum>i\<in>Basis. ((frechet_derivative g (at x) v) \<bullet> i) *\<^sub>R frechet_derivative f (at (g x)) i)"
  (is "?l = ?r")
  if "g differentiable at x" "f differentiable at (g x)"
proof (rule ext)
  fix v
  interpret g: linear "frechet_derivative g (at x)"
    using that(1)
    by (rule linear_frechet_derivative)
  interpret f: linear "frechet_derivative f (at (g x))"
    using that(2)
    by (rule linear_frechet_derivative)
  have "frechet_derivative (f o g) (at x) v =
    frechet_derivative f (at (g x)) (\<Sum>i\<in>Basis. (frechet_derivative g (at x) v \<bullet> i) *\<^sub>R i)"
    unfolding frechet_derivative_compose[OF that] o_apply
    by (simp add: euclidean_representation)
  also have "\<dots> = ?r v"
    by (auto simp: g.sum g.scaleR f.sum f.scaleR)
  finally show "?l v = ?r v" .
qed


lemma frechet_derivative_works_on_open:
  "f differentiable_on X \<Longrightarrow> open X \<Longrightarrow> x \<in> X \<Longrightarrow>
    (f has_derivative frechet_derivative f (at x)) (at x)"
  and frechet_derivative_works_on:
  "f differentiable_on X \<Longrightarrow> x \<in> X \<Longrightarrow>
    (f has_derivative frechet_derivative f (at x within X)) (at x within X)"
  by (auto simp: differentiable_onD differentiable_on_openD frechet_derivative_worksI)

lemma frechet_derivative_inverse: "frechet_derivative (\<lambda>x. inverse (f x)) (at x) =
    (\<lambda>h. - 1 / (f x)\<^sup>2 * frechet_derivative f (at x) h)"
  if "f differentiable at x" "f x \<noteq> 0" for f::"_\<Rightarrow>_::real_normed_field"
  apply (rule frechet_derivative_at')
  using that
  by (auto intro!: derivative_eq_intros frechet_derivative_worksI
      simp: divide_simps algebra_simps power2_eq_square)

lemma frechet_derivative_sqrt: "frechet_derivative (\<lambda>x. sqrt (f x)) (at x) =
  (\<lambda>v. (if f x > 0 then 1 else -1) / (2 * sqrt (f x)) * frechet_derivative f (at x) v)"
  if "f differentiable at x" "f x \<noteq> 0" 
  apply (rule frechet_derivative_at')
  apply (rule sqrt_has_derivative[THEN has_derivative_eq_rhs])
  by (auto intro!: frechet_derivative_worksI that simp: divide_simps)

lemma frechet_derivative_norm: "frechet_derivative (\<lambda>x. norm (f x)) (at x) =
    (\<lambda>v. frechet_derivative f (at x) v \<bullet> sgn (f x))"
  if "f differentiable at x" "f x \<noteq> 0" 
  for f::"_\<Rightarrow>_::real_inner"
  apply (rule frechet_derivative_at')
  by (auto intro!: derivative_eq_intros frechet_derivative_worksI that simp: divide_simps)

lemma (in bounded_linear) frechet_derivative:
  "frechet_derivative f (at x) = f"
  apply (rule frechet_derivative_at')
  apply (rule has_derivative_eq_rhs)
   apply (rule has_derivative)
  by (auto intro!: derivative_eq_intros)

bundle no_matrix_mult begin
no_notation matrix_matrix_mult (infixl "**" 70)
end

lemma (in bounded_bilinear) frechet_derivative:
  includes no_matrix_mult
  shows
    "x differentiable at a \<Longrightarrow> y differentiable at a \<Longrightarrow>
      frechet_derivative (\<lambda>a. x a ** y a) (at a) =
        (\<lambda>h. x a ** frechet_derivative y (at a) h + frechet_derivative x (at a) h ** y a)"
  by (rule frechet_derivative_at') (auto intro!: FDERIV frechet_derivative_worksI)

lemma frechet_derivative_divide: "frechet_derivative (\<lambda>x. f x / g x) (at x) =
    (\<lambda>h. frechet_derivative f (at x) h / (g x) -frechet_derivative g (at x) h * f x / (g x)\<^sup>2)"
  if "f differentiable at x" "g differentiable at x" "g x \<noteq> 0" for f::"_\<Rightarrow>_::real_normed_field"
  using that
  by (auto simp: divide_inverse_commute bounded_bilinear.frechet_derivative[OF bounded_bilinear_mult]
      frechet_derivative_inverse)

lemma frechet_derivative_pair:
  "frechet_derivative (\<lambda>x. (f x, g x)) (at x) = (\<lambda>v. (frechet_derivative f (at x) v, frechet_derivative g (at x) v))"
  if "f differentiable (at x)" "g differentiable (at x)"
  apply (rule frechet_derivative_at')
  apply (rule derivative_eq_intros)
    apply (rule frechet_derivative_worksI) apply fact    
    apply (rule frechet_derivative_worksI) apply fact
  ..

lemma frechet_derivative_fst:
  "frechet_derivative (\<lambda>x. fst (f x)) (at x) = (\<lambda>xa. fst (frechet_derivative f (at x) xa))"
  if "(f differentiable at x)"
  for f::"_\<Rightarrow>(_::real_normed_vector \<times> _::real_normed_vector)"
  apply (rule frechet_derivative_at')
  using that
  by (auto intro!: derivative_eq_intros frechet_derivative_worksI)

lemma frechet_derivative_snd:
  "frechet_derivative (\<lambda>x. snd (f x)) (at x) = (\<lambda>xa. snd (frechet_derivative f (at x) xa))"
  if "(f differentiable at x)"
  for f::"_\<Rightarrow>(_::real_normed_vector \<times> _::real_normed_vector)"
  apply (rule frechet_derivative_at')
  using that
  by (auto intro!: derivative_eq_intros frechet_derivative_worksI)

lemma frechet_derivative_eq_vector_derivative_1:
  assumes "f differentiable at t"
  shows "frechet_derivative f (at t) 1 = vector_derivative f (at t)"
  apply (subst frechet_derivative_eq_vector_derivative)
   apply (rule assms) by auto


subsection \<open>Linear algebra\<close>

lemma (in vector_space) dim_pos_finite_dimensional_vector_spaceE:
  assumes "dim (UNIV::'b set) > 0"
  obtains basis where "finite_dimensional_vector_space scale basis"
proof -
  from assms obtain b where b: "local.span b = local.span UNIV" "local.independent b"
    by (auto simp: dim_def split: if_splits)
  then have "dim UNIV = card b"
    by (rule dim_eq_card)
  with assms have "finite b" by (auto simp: card_ge_0_finite)
  then have "finite_dimensional_vector_space scale b"
    by unfold_locales (auto simp: b)
  then show ?thesis ..
qed

context vector_space_on begin

context includes lifting_syntax assumes "\<exists>(Rep::'s \<Rightarrow> 'b) (Abs::'b \<Rightarrow> 's). type_definition Rep Abs S" begin

interpretation local_typedef_vector_space_on S scale "TYPE('s)" by unfold_locales fact

lemmas_with [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
    OF type.ab_group_add_axioms type_vector_space_on_with,
    folded dim_S_def,
    untransferred,
    var_simplified implicit_ab_group_add]:
    lt_dim_pos_finite_dimensional_vector_spaceE = vector_space.dim_pos_finite_dimensional_vector_spaceE

end

lemmas_with [cancel_type_definition,
    OF S_ne,
    folded subset_iff',
    simplified pred_fun_def, folded finite_dimensional_vector_space_on_with,
    simplified\<comment>\<open>too much?\<close>]:
    dim_pos_finite_dimensional_vector_spaceE = lt_dim_pos_finite_dimensional_vector_spaceE

end


subsection \<open>Extensional function space\<close>

text \<open>f is zero outside A. We use such functions to canonically represent
  functions whose domain is A\<close>
definition extensional0 :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero) \<Rightarrow> bool"
  where "extensional0 A f = (\<forall>x. x \<notin> A \<longrightarrow> f x = 0)"

lemma extensional0_0[intro, simp]: "extensional0 X 0"
  by (auto simp: extensional0_def)

lemma extensional0_UNIV[intro, simp]: "extensional0 UNIV f"
  by (auto simp: extensional0_def)

lemma ext_extensional0:
  "f = g" if "extensional0 S f" "extensional0 S g" "\<And>x. x \<in> S \<Longrightarrow> f x = g x"
  using that by (force simp: extensional0_def fun_eq_iff)

lemma extensional0_add[intro, simp]:
  "extensional0 S f \<Longrightarrow> extensional0 S g \<Longrightarrow> extensional0 S (f + g::_\<Rightarrow>'a::comm_monoid_add)"
  by (auto simp: extensional0_def)

lemma extensinoal0_mult[intro, simp]:
  "extensional0 S x \<Longrightarrow> extensional0 S y \<Longrightarrow> extensional0 S (x * y)"
  for x y::"_\<Rightarrow>'a::mult_zero"
  by (auto simp: extensional0_def)

lemma extensional0_scaleR[intro, simp]: "extensional0 S f \<Longrightarrow> extensional0 S (c *\<^sub>R f::_\<Rightarrow>'a::real_vector)"
  by (auto simp: extensional0_def)

lemma extensional0_outside: "x \<notin> S \<Longrightarrow> extensional0 S f \<Longrightarrow> f x = 0"
  by (auto simp: extensional0_def)

lemma subspace_extensional0: "subspace (Collect (extensional0 X))"
  by (auto simp: subspace_def)

text \<open>Send the function f to its canonical representative as a function with domain A\<close>
definition restrict0 :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict0 A f x = (if x \<in> A then f x else 0)"

lemma restrict0_UNIV[simp]: "restrict0 UNIV = (\<lambda>x. x)"
  by (intro ext) (auto simp: restrict0_def)

lemma extensional0_restrict0[intro, simp]: "extensional0 A (restrict0 A f)"
  by (auto simp: extensional0_def restrict0_def)

lemma restrict0_times: "restrict0 A (x * y) = restrict0 A x * restrict0 A y"
  for x::"'a\<Rightarrow>'b::mult_zero"
  by (auto simp: restrict0_def[abs_def])

lemma restrict0_apply_in[simp]: "x \<in> A \<Longrightarrow> restrict0 A f x = f x"
  by (auto simp: restrict0_def)

lemma restrict0_apply_out[simp]: "x \<notin> A \<Longrightarrow> restrict0 A f x = 0"
  by (auto simp: restrict0_def)

lemma restrict0_scaleR: "restrict0 A (c *\<^sub>R f::_\<Rightarrow>'a::real_vector) = c *\<^sub>R restrict0 A f"
  by (auto simp: restrict0_def[abs_def])

lemma restrict0_add: "restrict0 A (f + g::_\<Rightarrow>'a::real_vector) = restrict0 A f + restrict0 A g"
  by (auto simp: restrict0_def[abs_def])

lemma restrict0_restrict0: "restrict0 X (restrict0 Y f) = restrict0 (X \<inter> Y) f"
  by (auto simp: restrict0_def)

end
