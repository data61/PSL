section \<open>Lifting Lemma\<close>

theory Completeness imports Resolution begin

locale unification =
  assumes unification: "\<And>\<sigma> L. finite L \<Longrightarrow> unifier\<^sub>l\<^sub>s \<sigma> L \<Longrightarrow> \<exists>\<theta>. mgu\<^sub>l\<^sub>s \<theta> L"
begin
text \<open>
  A proof of this assumption is available in @{file \<open>Unification_Theorem.thy\<close>} and used in
  @{file \<open>Completeness_Instance.thy\<close>}.
\<close>

lemma lifting:
  assumes fin: "finite C\<^sub>1 \<and> finite C\<^sub>2"
  assumes apart: "vars\<^sub>l\<^sub>s C\<^sub>1 \<inter> vars\<^sub>l\<^sub>s C\<^sub>2 = {}"
  assumes inst: "instance_of\<^sub>l\<^sub>s C\<^sub>1' C\<^sub>1 \<and> instance_of\<^sub>l\<^sub>s C\<^sub>2' C\<^sub>2"
  assumes appl: "applicable C\<^sub>1' C\<^sub>2' L\<^sub>1' L\<^sub>2' \<sigma>"
  shows "\<exists>L\<^sub>1 L\<^sub>2 \<tau>. applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau> \<and>
                instance_of\<^sub>l\<^sub>s (resolution C\<^sub>1' C\<^sub>2' L\<^sub>1' L\<^sub>2' \<sigma>) (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>)"
proof -
  \<comment> \<open>Obtaining the subsets we resolve upon:\<close>
  let ?R\<^sub>1' = "C\<^sub>1' - L\<^sub>1'" and ?R\<^sub>2' = "C\<^sub>2' - L\<^sub>2'"

  from inst obtain \<gamma> \<mu> where "C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<gamma> = C\<^sub>1' \<and> C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<mu> = C\<^sub>2'"
    unfolding instance_of\<^sub>l\<^sub>s_def by auto
  then obtain \<eta> where \<eta>_p: "C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta> = C\<^sub>1' \<and> C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<eta> = C\<^sub>2'"
    using apart merge_sub by force

  from \<eta>_p obtain L\<^sub>1 where L\<^sub>1_p: "L\<^sub>1 \<subseteq> C\<^sub>1 \<and> L\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta> = L\<^sub>1' \<and> (C\<^sub>1 - L\<^sub>1) \<cdot>\<^sub>l\<^sub>s \<eta> = ?R\<^sub>1'"
    using appl project_sub using applicable_def by metis
  let ?R\<^sub>1 = "C\<^sub>1 - L\<^sub>1"
  from \<eta>_p obtain L\<^sub>2 where L\<^sub>2_p: "L\<^sub>2 \<subseteq> C\<^sub>2 \<and> L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<eta> = L\<^sub>2' \<and> (C\<^sub>2 - L\<^sub>2) \<cdot>\<^sub>l\<^sub>s \<eta> = ?R\<^sub>2'"
    using appl project_sub using applicable_def by metis
  let ?R\<^sub>2 = "C\<^sub>2 - L\<^sub>2"

  \<comment> \<open>Obtaining substitutions:\<close>
  from appl have "mgu\<^sub>l\<^sub>s \<sigma> (L\<^sub>1' \<union> L\<^sub>2'\<^sup>C)" using applicable_def by auto
  then have "mgu\<^sub>l\<^sub>s \<sigma> ((L\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta>) \<union> (L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<eta>)\<^sup>C)" using L\<^sub>1_p L\<^sub>2_p by auto
  then have "mgu\<^sub>l\<^sub>s \<sigma> ((L\<^sub>1  \<union> L\<^sub>2\<^sup>C) \<cdot>\<^sub>l\<^sub>s \<eta>)" using compls_subls subls_union by auto
  then have "unifier\<^sub>l\<^sub>s \<sigma> ((L\<^sub>1  \<union> L\<^sub>2\<^sup>C) \<cdot>\<^sub>l\<^sub>s \<eta>)" using mgu\<^sub>l\<^sub>s_def by auto
  then have \<eta>\<sigma>uni: "unifier\<^sub>l\<^sub>s (\<eta> \<cdot> \<sigma>) (L\<^sub>1  \<union> L\<^sub>2\<^sup>C)"
    using unifier\<^sub>l\<^sub>s_def composition_conseq2l by auto
  then obtain \<tau> where \<tau>_p: "mgu\<^sub>l\<^sub>s \<tau> (L\<^sub>1  \<union> L\<^sub>2\<^sup>C)"
    using unification fin L\<^sub>1_p L\<^sub>2_p by (meson finite_UnI finite_imageI rev_finite_subset)
  then obtain \<phi> where \<phi>_p: "\<tau> \<cdot> \<phi> = \<eta> \<cdot> \<sigma>" using \<eta>\<sigma>uni mgu\<^sub>l\<^sub>s_def by auto

  \<comment> \<open>Showing that we have the desired resolvent:\<close>
  let ?C = "((C\<^sub>1 - L\<^sub>1)  \<union> (C\<^sub>2 - L\<^sub>2)) \<cdot>\<^sub>l\<^sub>s \<tau>"
  have "?C \<cdot>\<^sub>l\<^sub>s \<phi>  = (?R\<^sub>1 \<union> ?R\<^sub>2 ) \<cdot>\<^sub>l\<^sub>s (\<tau> \<cdot> \<phi>)"
    using subls_union composition_conseq2ls by auto
  also have "... = (?R\<^sub>1 \<union> ?R\<^sub>2 ) \<cdot>\<^sub>l\<^sub>s (\<eta> \<cdot> \<sigma>)" using \<phi>_p by auto
  also have "... = ((?R\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta>) \<union> (?R\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<eta>)) \<cdot>\<^sub>l\<^sub>s \<sigma>"
    using subls_union composition_conseq2ls by auto
  also have "... = (?R\<^sub>1' \<union> ?R\<^sub>2') \<cdot>\<^sub>l\<^sub>s \<sigma>" using \<eta>_p L\<^sub>1_p L\<^sub>2_p by auto
  finally have "?C \<cdot>\<^sub>l\<^sub>s \<phi> = ((C\<^sub>1' - L\<^sub>1') \<union> (C\<^sub>2' - L\<^sub>2')) \<cdot>\<^sub>l\<^sub>s \<sigma>" by auto
  then have ins: "instance_of\<^sub>l\<^sub>s (resolution C\<^sub>1' C\<^sub>2' L\<^sub>1' L\<^sub>2' \<sigma>) (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>)"
    using resolution_def instance_of\<^sub>l\<^sub>s_def by metis

  \<comment> \<open>Showing that the resolution rule is applicable:\<close>
  have "C\<^sub>1' \<noteq> {} \<and> C\<^sub>2' \<noteq> {} \<and> L\<^sub>1' \<noteq> {} \<and> L\<^sub>2' \<noteq> {}"
    using appl applicable_def by auto
  then have "C\<^sub>1 \<noteq> {} \<and> C\<^sub>2 \<noteq> {} \<and> L\<^sub>1 \<noteq> {} \<and> L\<^sub>2 \<noteq> {}" using \<eta>_p L\<^sub>1_p L\<^sub>2_p by auto
  then have appli: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>"
    using apart L\<^sub>1_p L\<^sub>2_p \<tau>_p applicable_def by auto

  from ins appli show ?thesis by auto
qed


section \<open>Completeness\<close>

lemma falsifies\<^sub>g_empty:
  assumes "falsifies\<^sub>g [] C"
  shows "C = {}"
proof -
  have "\<forall>l \<in> C. False"
    proof
      fix l
      assume "l\<in>C"
      then have "falsifies\<^sub>l [] l" using assms by auto
      then show False unfolding falsifies\<^sub>l_def by (cases l) auto
    qed
  then show ?thesis by auto
qed

lemma falsifies\<^sub>c\<^sub>s_empty:
  assumes "falsifies\<^sub>c [] C"
  shows "C = {}"
proof -
  from assms obtain C' where C'_p: "instance_of\<^sub>l\<^sub>s C' C \<and> falsifies\<^sub>g [] C'" by auto
  then have "C'= {}" using falsifies\<^sub>g_empty by auto
  then show "C = {}" using C'_p unfolding instance_of\<^sub>l\<^sub>s_def by auto
qed

lemma complements_do_not_falsify':
  assumes l1C1': "l\<^sub>1 \<in> C\<^sub>1'"
  assumes l\<^sub>2C1': "l\<^sub>2 \<in> C\<^sub>1'"
  assumes comp: "l\<^sub>1 = l\<^sub>2\<^sup>c"
  assumes falsif: "falsifies\<^sub>g G C\<^sub>1'"
  shows "False"
proof (cases l\<^sub>1)
  case (Pos p ts)
  let ?i1 = "nat_of_fatom (p, ts)"

  from assms have gr: "ground\<^sub>l l\<^sub>1" unfolding falsifies\<^sub>l_def by auto
  then have Neg: "l\<^sub>2 = Neg p ts" using comp Pos by (cases l\<^sub>2) auto

  from falsif have "falsifies\<^sub>l G l\<^sub>1" using l1C1' by auto
  then have "G ! ?i1 = False" using l1C1' Pos unfolding falsifies\<^sub>l_def by (induction "Pos p ts") auto
  moreover
  let ?i2 = "nat_of_fatom (get_atom l\<^sub>2)"
  from falsif have "falsifies\<^sub>l G l\<^sub>2" using l\<^sub>2C1' by auto
  then have "G ! ?i2 = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
  then have "G ! ?i1 = (\<not>sign l\<^sub>2)" using Pos Neg comp by simp
  then have "G ! ?i1 = True" using Neg by auto
  ultimately show ?thesis by auto
next
  case (Neg p ts)
  let ?i1 = "nat_of_fatom (p,ts)"

  from assms have gr: "ground\<^sub>l l\<^sub>1" unfolding falsifies\<^sub>l_def by auto
  then have Pos: "l\<^sub>2 = Pos p ts" using comp Neg by (cases l\<^sub>2) auto

  from falsif have "falsifies\<^sub>l G l\<^sub>1" using l1C1' by auto
  then have "G ! ?i1 = True" using l1C1' Neg unfolding falsifies\<^sub>l_def by (metis get_atom.simps(2) literal.disc(2)) 
  moreover
  let ?i2 = "nat_of_fatom (get_atom l\<^sub>2)"
  from falsif have "falsifies\<^sub>l G l\<^sub>2" using l\<^sub>2C1' by auto
  then have "G ! ?i2 = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
  then have "G ! ?i1 = (\<not>sign l\<^sub>2)" using Pos Neg comp by simp
  then have "G ! ?i1 = False" using Pos using literal.disc(1) by blast
  ultimately show ?thesis by auto
qed

lemma complements_do_not_falsify:
  assumes l1C1': "l\<^sub>1 \<in> C\<^sub>1'"
  assumes l\<^sub>2C1': "l\<^sub>2 \<in> C\<^sub>1'"
  assumes fals: "falsifies\<^sub>g G C\<^sub>1'"
  shows "l\<^sub>1 \<noteq> l\<^sub>2\<^sup>c"
using assms complements_do_not_falsify' by blast

lemma other_falsified:
  assumes C1'_p: "ground\<^sub>l\<^sub>s C\<^sub>1' \<and> falsifies\<^sub>g (B@[d]) C\<^sub>1'" 
  assumes l_p: "l \<in> C\<^sub>1'" "nat_of_fatom (get_atom l) = length B"
  assumes other: "lo \<in> C\<^sub>1'" "lo \<noteq> l"
  shows "falsifies\<^sub>l B lo"
proof -
  let ?i = "nat_of_fatom (get_atom lo)"
  have ground_l\<^sub>2: "ground\<^sub>l l" using l_p C1'_p by auto
  \<comment> \<open>They are, of course, also ground:\<close>
  have ground_lo: "ground\<^sub>l lo" using C1'_p other by auto
  from C1'_p have "falsifies\<^sub>g (B@[d]) (C\<^sub>1' - {l})" by auto
  \<comment> \<open>And indeed, falsified by @{term "B@[d]"}:\<close>
  then have loB\<^sub>2: "falsifies\<^sub>l (B@[d]) lo" using other by auto
  then have "?i < length (B @ [d])" unfolding falsifies\<^sub>l_def by meson
  \<comment> \<open>And they have numbers in the range of @{term "B@[d]"}, i.e. less than @{term "length B + 1"}:\<close>
  then have "nat_of_fatom (get_atom lo) < length B + 1" using undiag_diag_fatom by (cases lo) auto
  moreover
  have l_lo: "l\<noteq>lo" using other by auto
  \<comment> \<open>The are not the complement of @{term l }, since then the clause could not be falsified:\<close>
  have lc_lo: "lo \<noteq> l\<^sup>c" using C1'_p l_p other complements_do_not_falsify[of lo C\<^sub>1' l "(B@[d])"] by auto
  from l_lo lc_lo have "get_atom l \<noteq> get_atom lo" using sign_comp_atom by metis
  then have "nat_of_fatom (get_atom lo) \<noteq> nat_of_fatom (get_atom l)" 
    using nat_of_fatom_bij ground_lo ground_l\<^sub>2 ground\<^sub>l_ground_fatom 
    unfolding bij_betw_def inj_on_def by metis
  \<comment> \<open>Therefore they have different numbers:\<close>
  then have "nat_of_fatom (get_atom lo) \<noteq> length B" using l_p by auto
  ultimately 
  \<comment> \<open>So their numbers are in the range of @{term B}:\<close>
  have "nat_of_fatom (get_atom lo) < length B" by auto
  \<comment> \<open>So we did not need the last index of @{term "B@[d]"} to falsify them, i.e. @{term B} suffices:\<close>
  then show "falsifies\<^sub>l B lo" using loB\<^sub>2 shorter_falsifies\<^sub>l by blast
qed

theorem completeness':
  assumes "closed_tree T Cs"
  assumes "\<forall>C\<in>Cs. finite C"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
using assms proof (induction T arbitrary: Cs rule: measure_induct_rule[of treesize])
  fix T :: tree
  fix Cs :: "fterm clause set"
  assume ih: "\<And>T' Cs. treesize T' < treesize T \<Longrightarrow> closed_tree T' Cs \<Longrightarrow> 
                            \<forall>C\<in>Cs. finite C \<Longrightarrow> \<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
  assume clo: "closed_tree T Cs"
  assume finite_Cs: "\<forall>C\<in>Cs. finite C"
  { \<comment> \<open>Base case:\<close>
    assume "treesize T = 0"
    then have "T=Leaf" using treesize_Leaf by auto
    then have "closed_branch [] Leaf Cs" using branch_inv_Leaf clo unfolding closed_tree_def by auto
    then have "falsifies\<^sub>c\<^sub>s [] Cs" by auto
    then have "{} \<in> Cs" using falsifies\<^sub>c\<^sub>s_empty by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" 
      unfolding resolution_deriv_def by auto
  }
  moreover
  { \<comment> \<open>Induction case:\<close>
    assume "treesize T > 0"
    then have "\<exists>l r. T=Branching l r" by (cases T) auto
    
    \<comment> \<open>Finding sibling branches and their corresponding clauses:\<close>
    then obtain B where b_p: "internal B T \<and> branch (B@[True]) T \<and> branch (B@[False]) T"
      using internal_branch[of _ "[]" _ T] Branching_Leaf_Leaf_Tree by fastforce 
    let ?B\<^sub>1 = "B@[True]"
    let ?B\<^sub>2 = "B@[False]"

    obtain C\<^sub>1o where C\<^sub>1o_p: "C\<^sub>1o \<in> Cs \<and> falsifies\<^sub>c ?B\<^sub>1 C\<^sub>1o" using b_p clo unfolding closed_tree_def by metis 
    obtain C\<^sub>2o where C\<^sub>2o_p: "C\<^sub>2o \<in> Cs \<and> falsifies\<^sub>c ?B\<^sub>2 C\<^sub>2o" using b_p clo unfolding closed_tree_def by metis

    \<comment> \<open>Standardizing the clauses apart:\<close>
    let ?C\<^sub>1 = "std\<^sub>1 C\<^sub>1o"
    let ?C\<^sub>2 = "std\<^sub>2 C\<^sub>2o"
    have C\<^sub>1_p: "falsifies\<^sub>c ?B\<^sub>1 ?C\<^sub>1" using std\<^sub>1_falsifies C\<^sub>1o_p by auto
    have C\<^sub>2_p: "falsifies\<^sub>c ?B\<^sub>2 ?C\<^sub>2" using std\<^sub>2_falsifies C\<^sub>2o_p by auto

    have fin: "finite ?C\<^sub>1 \<and> finite ?C\<^sub>2" using C\<^sub>1o_p C\<^sub>2o_p finite_Cs by auto

    \<comment> \<open>We go down to the ground world.\<close>
    \<comment> \<open>Finding the falsifying ground instance @{term C\<^sub>1'} of @{term ?C\<^sub>1}, and proving properties about it:\<close>
    
    \<comment> \<open>@{term C\<^sub>1'} is falsified by @{term ?B\<^sub>1}:\<close>
    from C\<^sub>1_p  obtain C\<^sub>1' where C\<^sub>1'_p: "ground\<^sub>l\<^sub>s C\<^sub>1' \<and> instance_of\<^sub>l\<^sub>s C\<^sub>1' ?C\<^sub>1 \<and> falsifies\<^sub>g ?B\<^sub>1 C\<^sub>1'" by metis

    have "\<not>falsifies\<^sub>c B C\<^sub>1o" using C\<^sub>1o_p b_p clo unfolding closed_tree_def by metis
    then have "\<not>falsifies\<^sub>c B ?C\<^sub>1" using std\<^sub>1_falsifies using prod.exhaust_sel by blast
    \<comment> \<open>@{term C\<^sub>1'} is not falsified by @{term B}:\<close>
    then have l_B: "\<not>falsifies\<^sub>g B C\<^sub>1'" using C\<^sub>1'_p by auto

    \<comment> \<open>@{term C\<^sub>1'} contains a literal @{term l\<^sub>1} that is falsified by @{term ?B\<^sub>1}, but not @{term B}:\<close>
    from C\<^sub>1'_p l_B obtain l\<^sub>1 where l\<^sub>1_p: "l\<^sub>1 \<in> C\<^sub>1' \<and> falsifies\<^sub>l (B@[True]) l\<^sub>1 \<and> \<not>(falsifies\<^sub>l B l\<^sub>1)" by auto
    let ?i = "nat_of_fatom (get_atom l\<^sub>1)"

    \<comment> \<open>@{term l\<^sub>1} is of course ground:\<close>
    have ground_l\<^sub>1: "ground\<^sub>l l\<^sub>1" using C\<^sub>1'_p l\<^sub>1_p by auto

    from l\<^sub>1_p have "\<not>(?i < length B \<and> B ! ?i = (\<not>sign l\<^sub>1))" using ground_l\<^sub>1 unfolding falsifies\<^sub>l_def by meson
    then have "\<not>(?i < length B \<and> (B@[True]) ! ?i = (\<not>sign l\<^sub>1))" by (metis nth_append) \<comment> \<open>Not falsified by @{term B}.\<close>
    moreover
    from l\<^sub>1_p have "?i < length (B @ [True]) \<and> (B @ [True]) ! ?i = (\<not>sign l\<^sub>1)" unfolding falsifies\<^sub>l_def by meson
    ultimately
    have l\<^sub>1_sign_no: "?i = length B \<and> (B @ [True]) ! ?i = (\<not>sign l\<^sub>1)" by auto

    \<comment> \<open>@{term l\<^sub>1} is negative:\<close>
    from l\<^sub>1_sign_no have l\<^sub>1_sign: "sign l\<^sub>1 = False" by auto
    from l\<^sub>1_sign_no have l\<^sub>1_no: "nat_of_fatom (get_atom l\<^sub>1) = length B" by auto

    \<comment> \<open>All the other literals in @{term C\<^sub>1'} must be falsified by B, since they are falsified by @{term ?B\<^sub>1}, but not @{term l\<^sub>1}.\<close>
    from C\<^sub>1'_p l\<^sub>1_no l\<^sub>1_p have B_C\<^sub>1'l\<^sub>1: "falsifies\<^sub>g B (C\<^sub>1' - {l\<^sub>1})" (* This should be a lemma *)
      using other_falsified by blast

    \<comment> \<open>We do the same exercise for @{term ?C\<^sub>2}, @{term C\<^sub>2'}, @{term ?B\<^sub>2}, @{term l\<^sub>2}:\<close>
    from C\<^sub>2_p obtain C\<^sub>2' where C\<^sub>2'_p: "ground\<^sub>l\<^sub>s C\<^sub>2' \<and> instance_of\<^sub>l\<^sub>s C\<^sub>2' ?C\<^sub>2 \<and> falsifies\<^sub>g ?B\<^sub>2 C\<^sub>2'" by metis

    have "\<not>falsifies\<^sub>c B C\<^sub>2o" using C\<^sub>2o_p b_p clo unfolding closed_tree_def by metis
    then have "\<not>falsifies\<^sub>c B ?C\<^sub>2" using std\<^sub>2_falsifies using prod.exhaust_sel by blast
    then have l_B: "\<not>falsifies\<^sub>g B C\<^sub>2'" using C\<^sub>2'_p by auto (* I already had something called l_B... I could give it a new name *)
    
    \<comment> \<open>@{term C\<^sub>2'} contains a literal @{term l\<^sub>2} that is falsified by @{term ?B\<^sub>2}, but not B:\<close>
    from C\<^sub>2'_p l_B obtain l\<^sub>2 where l\<^sub>2_p: "l\<^sub>2 \<in> C\<^sub>2' \<and> falsifies\<^sub>l (B@[False]) l\<^sub>2 \<and> \<not>falsifies\<^sub>l B l\<^sub>2" by auto
    let ?i = "nat_of_fatom (get_atom l\<^sub>2)"

    have ground_l\<^sub>2: "ground\<^sub>l l\<^sub>2" using C\<^sub>2'_p l\<^sub>2_p by auto

    from l\<^sub>2_p have "\<not>(?i < length B \<and> B ! ?i = (\<not>sign l\<^sub>2))" using ground_l\<^sub>2 unfolding falsifies\<^sub>l_def by meson
    then have "\<not>(?i < length B \<and> (B@[False]) ! ?i = (\<not>sign l\<^sub>2))" by (metis nth_append) \<comment> \<open>Not falsified by @{term B}.\<close>
    moreover
    from l\<^sub>2_p have "?i < length (B @ [False]) \<and> (B @ [False]) ! ?i = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
    ultimately
    have l\<^sub>2_sign_no: "?i = length B \<and> (B @ [False]) ! ?i = (\<not>sign l\<^sub>2)" by auto

    \<comment> \<open>@{term l\<^sub>2} is negative:\<close>
    from l\<^sub>2_sign_no have l\<^sub>2_sign: "sign l\<^sub>2 = True" by auto
    from l\<^sub>2_sign_no have l\<^sub>2_no: "nat_of_fatom (get_atom l\<^sub>2) = length B" by auto

    \<comment> \<open>All the other literals in @{term C\<^sub>2'} must be falsified by B, since they are falsified by 
          @{term ?B\<^sub>2}, but not @{term l\<^sub>2}.\<close>
    from C\<^sub>2'_p l\<^sub>2_no l\<^sub>2_p have B_C\<^sub>2'l\<^sub>2: "falsifies\<^sub>g B (C\<^sub>2' - {l\<^sub>2})"
      using other_falsified by blast

    \<comment> \<open>Proving some properties about @{term C\<^sub>1'} and @{term C\<^sub>2'}, @{term l\<^sub>1} and @{term l\<^sub>2}, as well as 
          the resolvent of @{term C\<^sub>1'} and @{term C\<^sub>2'}:\<close>
    have l\<^sub>2cisl\<^sub>1: "l\<^sub>2\<^sup>c = l\<^sub>1" (* Could perhaps be a lemma *)
      proof -
        from l\<^sub>1_no l\<^sub>2_no ground_l\<^sub>1 ground_l\<^sub>2 have "get_atom l\<^sub>1 = get_atom l\<^sub>2"
              using nat_of_fatom_bij ground\<^sub>l_ground_fatom 
              unfolding bij_betw_def inj_on_def by metis
        then show "l\<^sub>2\<^sup>c = l\<^sub>1" using l\<^sub>1_sign l\<^sub>2_sign using sign_comp_atom by metis 
      qed
    
    have "applicable C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>" unfolding applicable_def
      using l\<^sub>1_p l\<^sub>2_p C\<^sub>1'_p ground\<^sub>l\<^sub>s_vars\<^sub>l\<^sub>s l\<^sub>2cisl\<^sub>1 empty_comp2 unfolding mgu\<^sub>l\<^sub>s_def unifier\<^sub>l\<^sub>s_def by auto
    \<comment> \<open>Lifting to get a resolvent of @{term ?C\<^sub>1} and @{term ?C\<^sub>2}:\<close>
    then obtain L\<^sub>1 L\<^sub>2 \<tau> where L\<^sub>1L\<^sub>2\<tau>_p: "applicable ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>  \<and> instance_of\<^sub>l\<^sub>s (resolution C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>) (resolution ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>)"
      using std_apart_apart C\<^sub>1'_p C\<^sub>2'_p lifting[of ?C\<^sub>1 ?C\<^sub>2 C\<^sub>1' C\<^sub>2' "{l\<^sub>1}" "{l\<^sub>2}" Resolution.\<epsilon>] fin by auto


    \<comment> \<open>Defining the clause to be derived, the new clausal form and the new tree:\<close>
    \<comment> \<open>We name the resolvent @{term C}.\<close>
    obtain C where C_p: "C = resolution ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>" by auto
    obtain CsNext where CsNext_p: "CsNext = Cs \<union> {?C\<^sub>1, ?C\<^sub>2, C}" by auto
    obtain T'' where T''_p: "T'' = delete B T" by auto 
        \<comment> \<open>Here we delete the two branch children @{term ?B\<^sub>1} and @{term ?B\<^sub>2} of @{term B}.\<close>
    
    \<comment> \<open>Our new clause is falsified by the branch @{term B} of our new tree:\<close>
    have "falsifies\<^sub>g B ((C\<^sub>1' - {l\<^sub>1}) \<union> (C\<^sub>2' - {l\<^sub>2}))" using B_C\<^sub>1'l\<^sub>1 B_C\<^sub>2'l\<^sub>2 by cases auto
    then have "falsifies\<^sub>g B (resolution C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>)" unfolding resolution_def empty_subls by auto
    then have falsifies_C: "falsifies\<^sub>c B C" using C_p L\<^sub>1L\<^sub>2\<tau>_p by auto

    have T''_smaller: "treesize T'' < treesize T" using treezise_delete T''_p b_p by auto
    have T''_bran: "anybranch T'' (\<lambda>b. closed_branch b T'' CsNext)"
      proof (rule allI; rule impI)
        fix b
        assume br: "branch b T''"
        from br have "b = B \<or> branch b T" using branch_delete T''_p by auto
        then show "closed_branch b T'' CsNext"
          proof
            assume "b=B"
            then show "closed_branch b T'' CsNext" using falsifies_C br CsNext_p by auto
          next
            assume "branch b T"
            then show "closed_branch b T'' CsNext" using clo br T''_p CsNext_p unfolding closed_tree_def by auto
          qed
      qed
    then have T''_bran2: "anybranch T'' (\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext)" by auto (* replace T''_bran with this maybe? *)

    \<comment> \<open>We cut the tree even smaller to ensure only the branches are falsified, i.e. it is a closed tree:\<close>
    obtain T' where T'_p: "T' = cutoff (\<lambda>G. falsifies\<^sub>c\<^sub>s G CsNext) [] T''" by auto
    have T'_smaller: "treesize T' < treesize T" using treesize_cutoff[of "\<lambda>G. falsifies\<^sub>c\<^sub>s G CsNext" "[]" T''] T''_smaller unfolding T'_p by auto

    from T''_bran2 have "anybranch T' (\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext)" using cutoff_branch[of T'' "\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext"] T'_p by auto
    then have T'_bran: "anybranch T' (\<lambda>b. closed_branch b T' CsNext)" by auto
    have T'_intr: "anyinternal T' (\<lambda>p. \<not>falsifies\<^sub>c\<^sub>s p CsNext)" using T'_p cutoff_internal[of T'' "\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext"] T''_bran2 by blast
    have T'_closed: "closed_tree T' CsNext" using T'_bran T'_intr unfolding closed_tree_def by auto
    have finite_CsNext: "\<forall>C\<in>CsNext. finite C" unfolding CsNext_p C_p resolution_def using finite_Cs fin by auto

    \<comment> \<open>By induction hypothesis we get a resolution derivation of @{term "{}"} from our new clausal form:\<close>
    from T'_smaller T'_closed have "\<exists>Cs''. resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" using ih[of T' CsNext] finite_CsNext by blast
    then obtain Cs'' where Cs''_p: "resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" by auto
    moreover
    { \<comment> \<open>Proving that we can actually derive the new clausal form:\<close>
      have "resolution_step Cs (Cs \<union> {?C\<^sub>1})" using std\<^sub>1_renames standardize_apart C\<^sub>1o_p by (metis Un_insert_right)
      moreover
      have "resolution_step (Cs \<union> {?C\<^sub>1}) (Cs \<union> {?C\<^sub>1} \<union> {?C\<^sub>2})" using std\<^sub>2_renames[of C\<^sub>2o] standardize_apart[of C\<^sub>2o _ ?C\<^sub>2] C\<^sub>2o_p by auto 
      then have "resolution_step (Cs \<union> {?C\<^sub>1}) (Cs \<union> {?C\<^sub>1,?C\<^sub>2})" by (simp add: insert_commute)
      moreover
      then have "resolution_step (Cs \<union> {?C\<^sub>1,?C\<^sub>2}) (Cs \<union> {?C\<^sub>1,?C\<^sub>2} \<union> {C})" 
        using L\<^sub>1L\<^sub>2\<tau>_p resolution_rule[of ?C\<^sub>1 "Cs \<union> {?C\<^sub>1,?C\<^sub>2}" ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau> ] using C_p by auto
      then have "resolution_step (Cs \<union> {?C\<^sub>1,?C\<^sub>2}) CsNext" using CsNext_p by (simp add:  Un_commute)
      ultimately
      have "resolution_deriv Cs CsNext"  unfolding resolution_deriv_def by auto
    }
    \<comment> \<open>Combining the two derivations, we get the desired derivation from @{term Cs} of @{term "{}"}:\<close>
    ultimately have "resolution_deriv Cs Cs''"  unfolding resolution_deriv_def by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using Cs''_p by auto
  }
  ultimately show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" by auto
qed

theorem completeness:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::hterm fun_denot) (G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof -
  from unsat have "\<forall>(G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s HFun G Cs" by auto
  then obtain T where "closed_tree T Cs" using herbrand assms by blast
  then show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using completeness' assms by auto
qed 

definition E_conv :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a var_denot \<Rightarrow> 'b var_denot" where
  "E_conv b_of_a E \<equiv> \<lambda>x. (b_of_a (E x))"

definition F_conv :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fun_denot \<Rightarrow> 'b fun_denot" where
  "F_conv b_of_a F \<equiv> \<lambda>f bs. b_of_a (F f (map (inv b_of_a) bs))"

definition G_conv :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a pred_denot \<Rightarrow> 'b pred_denot" where
  "G_conv b_of_a G \<equiv> \<lambda>p bs. (G p (map (inv b_of_a) bs))"
  
lemma eval\<^sub>t_bij:
  assumes "bij (b_of_a::'a \<Rightarrow> 'b)"
  shows"eval\<^sub>t (E_conv b_of_a E) (F_conv b_of_a F) t = b_of_a (eval\<^sub>t E F t)"
proof (induction t)
  case (Fun f ts)
  then have "map (inv b_of_a \<circ> eval\<^sub>t (E_conv b_of_a E) (F_conv b_of_a F)) ts = eval\<^sub>t\<^sub>s E F ts"
    unfolding E_conv_def F_conv_def
    using assms bij_is_inj by fastforce
  then have "b_of_a (F f (map (inv b_of_a \<circ> eval\<^sub>t (E_conv b_of_a E) ((F_conv b_of_a F))) ts)) = b_of_a (F f (eval\<^sub>t\<^sub>s E F ts))" by metis
  then show ?case using assms unfolding E_conv_def F_conv_def by auto
next
  case (Var x)
  then show ?case using assms unfolding E_conv_def by auto
qed

lemma eval\<^sub>t\<^sub>s_bij:
  assumes "bij (b_of_a::'a \<Rightarrow> 'b)"
  shows "G_conv b_of_a G p (eval\<^sub>t\<^sub>s (E_conv b_of_a E) (F_conv b_of_a F) ts) = G p (eval\<^sub>t\<^sub>s E F ts)" 
  using assms using eval\<^sub>t_bij
proof -
  have "map (inv b_of_a \<circ> eval\<^sub>t (E_conv b_of_a E) (F_conv b_of_a F)) ts = eval\<^sub>t\<^sub>s E F ts"
    using eval\<^sub>t_bij assms bij_is_inj by fastforce
  then show ?thesis
    by (metis (no_types) G_conv_def map_map)
qed
   
  
lemma eval\<^sub>l_bij:
  assumes "bij (b_of_a::'a \<Rightarrow> 'b)"
  shows "eval\<^sub>l (E_conv b_of_a E) (F_conv b_of_a F) (G_conv b_of_a G) l = eval\<^sub>l E F G l"
  using assms eval\<^sub>t\<^sub>s_bij 
proof (cases l)
  case (Pos p ts)
  then show ?thesis
    by (simp add: eval\<^sub>t\<^sub>s_bij assms) 
next
  case (Neg p ts)
  then show ?thesis
    by (simp add: eval\<^sub>t\<^sub>s_bij assms)
qed 
            
lemma eval\<^sub>c_bij:
  assumes "bij (b_of_a::'a \<Rightarrow> 'b)"
  shows "eval\<^sub>c (F_conv b_of_a F) (G_conv b_of_a G) C = eval\<^sub>c F G C"
proof -
  {
    fix E :: "char list \<Rightarrow> 'b"
    assume bij_b_of_a: "bij b_of_a"
    assume C_sat: "\<forall>E :: char list \<Rightarrow> 'a. \<exists>l\<in>C. eval\<^sub>l E F G l" 
    have E_p: "E = E_conv b_of_a (E_conv (inv b_of_a) E)" 
      unfolding E_conv_def using bij_b_of_a
      using bij_betw_inv_into_right by fastforce 
    have "\<exists>l\<in>C. eval\<^sub>l (E_conv b_of_a (E_conv (inv b_of_a) E)) (F_conv b_of_a F) (G_conv b_of_a G) l"
      using eval\<^sub>l_bij bij_b_of_a C_sat by blast
    then have "\<exists>l\<in>C. eval\<^sub>l E (F_conv b_of_a F) (G_conv b_of_a G) l" using E_p by auto 
  }
  then show ?thesis
    by (meson eval\<^sub>l_bij assms eval\<^sub>c_def) 
qed

lemma eval\<^sub>c\<^sub>s_bij:
  assumes "bij (b_of_a::'a \<Rightarrow> 'b)"
  shows "eval\<^sub>c\<^sub>s (F_conv b_of_a F) (G_conv b_of_a G) Cs \<longleftrightarrow> eval\<^sub>c\<^sub>s F G Cs"
    by (meson eval\<^sub>c_bij assms eval\<^sub>c\<^sub>s_def)
    
lemma countably_inf_bij:
  assumes inf_a_uni: "infinite (UNIV :: ('a ::countable) set)"
  assumes inf_b_uni: "infinite (UNIV :: ('b ::countable) set)"
  shows "\<exists>b_of_a :: 'a \<Rightarrow> 'b. bij b_of_a"
proof -
  let ?S = "UNIV :: (('a::countable)) set"
  have "countable ?S" by auto
  moreover
  have "infinite ?S" using inf_a_uni by auto
  ultimately
  obtain nat_of_a where QWER: "bij (nat_of_a :: 'a \<Rightarrow> nat)" using countableE_infinite[of ?S] by blast
      
  let ?T = "UNIV :: (('b::countable)) set"
  have "countable ?T" by auto
  moreover
  have "infinite ?T" using inf_b_uni by auto
  ultimately
  obtain nat_of_b where TYUI: "bij (nat_of_b :: 'b \<Rightarrow> nat)" using countableE_infinite[of ?T] by blast
      
  let ?b_of_a = "\<lambda>a. (inv nat_of_b) (nat_of_a a)"
    
  have bij_nat_of_b: "\<forall>n. nat_of_b (inv nat_of_b n) = n"
    using TYUI bij_betw_inv_into_right by fastforce
  have "\<forall>a. inv nat_of_a (nat_of_a a) = a"
    by (meson QWER UNIV_I bij_betw_inv_into_left) 
  then have "inj (\<lambda>a. inv nat_of_b (nat_of_a a))"
    using bij_nat_of_b injI by (metis (no_types))
  moreover
  have "range (\<lambda>a. inv nat_of_b (nat_of_a a)) = UNIV"
    by (metis QWER TYUI bij_def image_image inj_imp_surj_inv)
  ultimately
  have "bij ?b_of_a"
    unfolding bij_def by auto
      
  then show ?thesis by auto
qed
  
lemma infinite_hterms: "infinite (UNIV :: hterm set)"
proof -
  let ?diago = "\<lambda>n. HFun (string_of_nat n) []"
  let ?undiago = "\<lambda>a. nat_of_string (case a of HFun f ts \<Rightarrow> f)"
  have "\<forall>n. ?undiago (?diago n) = n" using nat_of_string_string_of_nat by auto
  moreover
  have "\<forall>n. ?diago n \<in> UNIV" by auto
  ultimately show "infinite (UNIV :: hterm set)" using infinity[of ?undiago ?diago UNIV] by simp
qed

theorem completeness_countable:
  assumes inf_uni: "infinite (UNIV :: ('u :: countable) set)"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::'u fun_denot) (G::'u pred_denot). \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof -
  have "\<forall>(F::hterm fun_denot) (G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  proof (rule; rule)
    fix F :: "hterm fun_denot"
    fix G :: "hterm pred_denot"
      
    obtain u_of_hterm :: "hterm \<Rightarrow> 'u" where p_u_of_hterm: "bij u_of_hterm"
      using countably_inf_bij inf_uni infinite_hterms by auto
        
    let ?F = "F_conv u_of_hterm F"
    let ?G = "G_conv u_of_hterm G"
    
    have "\<not> eval\<^sub>c\<^sub>s ?F ?G Cs" using unsat by auto
    then show "\<not> eval\<^sub>c\<^sub>s F G Cs" using eval\<^sub>c\<^sub>s_bij using p_u_of_hterm by auto
  qed
  then show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using finite_cs completeness by auto
qed
  
theorem completeness_nat:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::nat fun_denot) (G::nat pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
  using assms completeness_countable by blast

end \<comment> \<open>unification locale\<close>

end
