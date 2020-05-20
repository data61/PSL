theory ASC_Example
  imports ASC_Hoare
begin


section \<open> Example product machines and properties \<close>

text \<open>
This section provides example FSMs and shows that the assumptions on the inputs of the adaptive
state counting algorithm are not vacuous.
\<close>


subsection \<open> Constructing FSMs from transition relations \<close>

text \<open>
This subsection provides a function to more easily create FSMs, only requiring a set of
transition-tuples and an initial state.
\<close>


fun from_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) FSM" where
"from_rel rel q0 = \<lparr> succ = \<lambda> io p . { q . (p,io,q) \<in> rel },
                    inputs = image (fst \<circ> fst \<circ> snd) rel,
                    outputs = image (snd \<circ> fst \<circ> snd) rel,
                    initial = q0 \<rparr>"



lemma nodes_from_rel : "nodes (from_rel rel q0) \<subseteq> insert q0 (image (snd \<circ> snd) rel)"
  (is "nodes ?M \<subseteq> insert q0 (image (snd \<circ> snd) rel)")
proof -
  have "\<And> q io p . q \<in> succ ?M io p \<Longrightarrow> q \<in> image (snd \<circ> snd) rel"
    by force
  have "\<And> q . q \<in> nodes ?M \<Longrightarrow> q = q0 \<or> q \<in> image (snd \<circ> snd) rel"
  proof -
    fix q assume "q \<in> nodes ?M"
    then show "q = q0 \<or> q \<in> image (snd \<circ> snd) rel"
    proof (cases rule: FSM.nodes.cases)
      case initial
      then show ?thesis by auto
    next
      case (execute p a)
      then show ?thesis
        using \<open>\<And> q io p . q \<in> succ ?M io p \<Longrightarrow> q \<in> image (snd \<circ> snd) rel\<close> by blast
    qed
  qed
  then show "nodes ?M \<subseteq> insert q0 (image (snd \<circ> snd) rel)"
    by blast
qed



fun well_formed_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> bool" where
  "well_formed_rel rel = (finite rel
                          \<and> (\<forall> s1 x y . (x \<notin> image (fst \<circ> fst \<circ> snd) rel
                                            \<or> y \<notin> image (snd \<circ> fst \<circ> snd) rel)
                                        \<longrightarrow> \<not>(\<exists> s2 . (s1,(x,y),s2) \<in> rel))
                          \<and> rel \<noteq> {})"

lemma well_formed_from_rel :
  assumes "well_formed_rel rel"
  shows "well_formed (from_rel rel q0)"  (is "well_formed ?M")
proof -
  have "nodes ?M \<subseteq> insert q0 (image (snd \<circ> snd) rel)"
    using nodes_from_rel[of rel q0] by auto
  moreover have "finite (insert q0 (image (snd \<circ> snd) rel))"
    using assms by auto
  ultimately have "finite (nodes ?M)"
    by (simp add: Finite_Set.finite_subset)
  moreover have "finite (inputs ?M)" "finite (outputs ?M)"
    using assms by auto
  ultimately have "finite_FSM ?M"
    by auto

  moreover have "inputs ?M \<noteq> {}"
    using assms by auto
  moreover have "outputs ?M \<noteq> {}"
    using assms by auto
  moreover have "\<And> s1 x y . (x \<notin> inputs ?M \<or> y \<notin> outputs ?M) \<longrightarrow> succ ?M (x,y) s1 = {}"
    using assms by auto

  ultimately show ?thesis
    by auto
qed




fun completely_specified_rel_over :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> 'state set \<Rightarrow> bool"
  where
  "completely_specified_rel_over rel nods = (\<forall> s1 \<in> nods .
                                                \<forall> x \<in> image (fst \<circ> fst \<circ> snd) rel .
                                                  \<exists> y \<in> image (snd \<circ> fst \<circ> snd) rel .
                                                    \<exists> s2 . (s1,(x,y),s2) \<in> rel)"

lemma completely_specified_from_rel :
  assumes "completely_specified_rel_over rel (nodes ((from_rel rel q0)))"
  shows "completely_specified (from_rel rel q0)"  (is "completely_specified ?M")
  unfolding completely_specified.simps
proof
  fix s1 assume "s1 \<in> nodes (from_rel rel q0)"
  show  "\<forall>x\<in>inputs ?M. \<exists>y\<in>outputs ?M. \<exists>s2. s2 \<in> succ ?M (x, y) s1"
  proof
    fix x assume "x \<in> inputs (from_rel rel q0)"
    then have "x \<in>  image (fst \<circ> fst \<circ> snd) rel"
      using assms by auto

    obtain y s2 where "y \<in> image (snd \<circ> fst \<circ> snd) rel" "(s1,(x,y),s2) \<in> rel"
      using assms \<open>s1 \<in> nodes (from_rel rel q0)\<close> \<open>x \<in>  image (fst \<circ> fst \<circ> snd) rel\<close>
      by (meson completely_specified_rel_over.elims(2))

    then have "y \<in> outputs (from_rel rel q0)" "s2 \<in> succ (from_rel rel q0) (x, y) s1"
      by auto

    then show "\<exists>y\<in>outputs (from_rel rel q0). \<exists>s2. s2 \<in> succ (from_rel rel q0) (x, y) s1"
      by blast
  qed
qed





fun observable_rel :: "('state \<times> ('in \<times> 'out) \<times> 'state) set \<Rightarrow> bool" where
  "observable_rel rel = (\<forall> io s1 . { s2 . (s1,io,s2) \<in> rel } = {}
                                    \<or> (\<exists> s2 . { s2' . (s1,io,s2') \<in> rel } = {s2}))"

lemma observable_from_rel :
  assumes "observable_rel rel"
  shows "observable (from_rel rel q0)"  (is "observable ?M")
proof -
  have "\<And> io s1 . { s2 . (s1,io,s2) \<in> rel } = succ ?M io s1"
    by auto
  then show ?thesis using assms by auto
qed





abbreviation "OFSM_rel rel q0 \<equiv> well_formed_rel rel
                                \<and> completely_specified_rel_over rel (nodes (from_rel rel q0))
                                \<and> observable_rel rel"

lemma OFMS_from_rel :
  assumes "OFSM_rel rel q0"
  shows "OFSM (from_rel rel q0)"
  by (metis assms completely_specified_from_rel observable_from_rel well_formed_from_rel)




subsection \<open> Example FSMs and properties \<close>



abbreviation "M\<^sub>S_rel :: (nat\<times>(nat\<times>nat)\<times>nat) set \<equiv> {(0,(0,0),1), (0,(0,1),1), (1,(0,2),1)}"
abbreviation "M\<^sub>S :: (nat,nat,nat) FSM \<equiv> from_rel M\<^sub>S_rel 0"

abbreviation "M\<^sub>I_rel :: (nat\<times>(nat\<times>nat)\<times>nat) set \<equiv> {(0,(0,0),1), (0,(0,1),1), (1,(0,2),0)}"
abbreviation "M\<^sub>I :: (nat,nat,nat) FSM \<equiv> from_rel M\<^sub>I_rel 0"

lemma example_nodes :
  "nodes M\<^sub>S = {0,1}" "nodes M\<^sub>I = {0,1}"
proof -
  have "0 \<in> nodes M\<^sub>S" by auto
  have "1 \<in> succ M\<^sub>S (0,0) 0" by auto
  have "1 \<in> nodes M\<^sub>S"
    by (meson \<open>0 \<in> nodes M\<^sub>S\<close> \<open>1 \<in> succ M\<^sub>S (0, 0) 0\<close> succ_nodes)

  have "{0,1} \<subseteq> nodes M\<^sub>S"
    using \<open>0 \<in> nodes M\<^sub>S\<close> \<open>1 \<in> nodes M\<^sub>S\<close> by auto
  moreover have "nodes M\<^sub>S \<subseteq> {0,1}"
    using nodes_from_rel[of M\<^sub>S_rel 0] by auto
  ultimately show "nodes M\<^sub>S = {0,1}"
    by blast
next
  have "0 \<in> nodes M\<^sub>I" by auto
  have "1 \<in> succ M\<^sub>I (0,0) 0" by auto
  have "1 \<in> nodes M\<^sub>I"
    by (meson \<open>0 \<in> nodes M\<^sub>I\<close> \<open>1 \<in> succ M\<^sub>I (0, 0) 0\<close> succ_nodes)

  have "{0,1} \<subseteq> nodes M\<^sub>I"
    using \<open>0 \<in> nodes M\<^sub>I\<close> \<open>1 \<in> nodes M\<^sub>I\<close> by auto
  moreover have "nodes M\<^sub>I \<subseteq> {0,1}"
    using nodes_from_rel[of M\<^sub>I_rel 0] by auto
  ultimately show "nodes M\<^sub>I = {0,1}"
    by blast
qed



lemma example_OFSM :
  "OFSM M\<^sub>S" "OFSM M\<^sub>I"
proof -
  have "well_formed_rel M\<^sub>S_rel"
    unfolding well_formed_rel.simps by auto

  moreover have "completely_specified_rel_over M\<^sub>S_rel (nodes (from_rel M\<^sub>S_rel 0))"
    unfolding completely_specified_rel_over.simps
  proof
    fix s1 assume "(s1::nat) \<in> nodes (from_rel M\<^sub>S_rel 0)"
    then have "s1 \<in> (insert 0 (image (snd \<circ> snd) M\<^sub>S_rel))"
      using nodes_from_rel[of M\<^sub>S_rel 0] by blast
    moreover have "completely_specified_rel_over M\<^sub>S_rel (insert 0 (image (snd \<circ> snd) M\<^sub>S_rel))"
      unfolding completely_specified_rel_over.simps by auto
    ultimately show "\<forall>x\<in>(fst \<circ> fst \<circ> snd) ` M\<^sub>S_rel.
                      \<exists>y\<in>(snd \<circ> fst \<circ> snd) ` M\<^sub>S_rel. \<exists>s2. (s1, (x, y), s2) \<in> M\<^sub>S_rel"
      by simp
  qed

  moreover have "observable_rel M\<^sub>S_rel"
    by auto

  ultimately have "OFSM_rel M\<^sub>S_rel 0"
    by auto

  then show "OFSM M\<^sub>S"
    using OFMS_from_rel[of M\<^sub>S_rel 0] by linarith
next
  have "well_formed_rel M\<^sub>I_rel"
    unfolding well_formed_rel.simps by auto

  moreover have "completely_specified_rel_over M\<^sub>I_rel (nodes (from_rel M\<^sub>I_rel 0))"
    unfolding completely_specified_rel_over.simps
  proof
    fix s1 assume "(s1::nat) \<in> nodes (from_rel M\<^sub>I_rel 0)"
    then have "s1 \<in> (insert 0 (image (snd \<circ> snd) M\<^sub>I_rel))"
      using nodes_from_rel[of M\<^sub>I_rel 0] by blast
    have "completely_specified_rel_over M\<^sub>I_rel (insert 0 (image (snd \<circ> snd) M\<^sub>I_rel))"
      unfolding completely_specified_rel_over.simps by auto
    show "\<forall>x\<in>(fst \<circ> fst \<circ> snd) ` M\<^sub>I_rel.
            \<exists>y\<in>(snd \<circ> fst \<circ> snd) ` M\<^sub>I_rel. \<exists>s2. (s1, (x, y), s2) \<in> M\<^sub>I_rel"
      by (meson \<open>completely_specified_rel_over M\<^sub>I_rel (insert 0 ((snd \<circ> snd) ` M\<^sub>I_rel))\<close>
          \<open>s1 \<in> insert 0 ((snd \<circ> snd) ` M\<^sub>I_rel)\<close> completely_specified_rel_over.elims(2))
  qed

  moreover have "observable_rel M\<^sub>I_rel"
    by auto

  ultimately have "OFSM_rel M\<^sub>I_rel 0"
    by auto

  then show "OFSM M\<^sub>I"
    using OFMS_from_rel[of M\<^sub>I_rel 0] by linarith
qed



lemma example_fault_domain : "asc_fault_domain M\<^sub>S M\<^sub>I 2"
proof -
  have "inputs M\<^sub>S = inputs M\<^sub>I"
    by auto
  moreover have "card (nodes M\<^sub>I) \<le> 2"
    using example_nodes(2) by auto
  ultimately show "asc_fault_domain M\<^sub>S M\<^sub>I 2"
    by auto
qed

abbreviation "FAIL\<^sub>I :: (nat\<times>nat) \<equiv> (3,3)"
abbreviation "PM\<^sub>I :: (nat, nat, nat\<times>nat) FSM \<equiv> \<lparr>
            succ = (\<lambda> a (p1,p2) . (if (p1 \<in> nodes M\<^sub>S \<and> p2 \<in> nodes M\<^sub>I \<and> (fst a \<in> inputs M\<^sub>S)
                                        \<and> (snd a \<in> outputs M\<^sub>S \<union> outputs M\<^sub>I))
                                    then (if (succ M\<^sub>S a p1 = {} \<and> succ M\<^sub>I a p2 \<noteq> {})
                                      then {FAIL\<^sub>I}
                                      else (succ M\<^sub>S a p1 \<times> succ M\<^sub>I a p2))
                                    else {})),
            inputs = inputs M\<^sub>S,
            outputs = outputs M\<^sub>S \<union> outputs M\<^sub>I,
            initial = (initial M\<^sub>S, initial M\<^sub>I)
          \<rparr>"

lemma example_productF : "productF M\<^sub>S M\<^sub>I FAIL\<^sub>I PM\<^sub>I"
proof -
  have "inputs M\<^sub>S = inputs M\<^sub>I"
    by auto
  moreover have "fst FAIL\<^sub>I \<notin> nodes M\<^sub>S"
    using example_nodes(1) by auto
  moreover have "snd FAIL\<^sub>I \<notin> nodes M\<^sub>I"
    using example_nodes(2) by auto
  ultimately show ?thesis
    unfolding productF.simps by blast
qed



abbreviation "V\<^sub>I :: nat list set \<equiv> {[],[0]}"

lemma example_det_state_cover : "is_det_state_cover M\<^sub>S V\<^sub>I"
proof -
  have "d_reaches M\<^sub>S (initial M\<^sub>S) [] (initial M\<^sub>S)"
    by auto
  then have "initial M\<^sub>S \<in> d_reachable M\<^sub>S (initial M\<^sub>S)"
    unfolding d_reachable.simps by blast

  have "d_reached_by M\<^sub>S (initial M\<^sub>S) [0] 1 [1] [0]"
  proof
    show "length [0] = length [0] \<and>
    length [0] = length [1] \<and> path M\<^sub>S (([0] || [0]) || [1]) (initial M\<^sub>S)
                            \<and> target (([0] || [0]) || [1]) (initial M\<^sub>S) = 1"
      by auto

    have "\<And>ys2 tr2.
       length [0] = length ys2
          \<and> length [0] = length tr2
          \<and> path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)
            \<longrightarrow> target (([0] || ys2) || tr2) (initial M\<^sub>S) = 1"
    proof
      fix ys2 tr2 assume "length [0] = length ys2 \<and> length [0] = length tr2
                            \<and> path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)"
      then have "length ys2 = 1" "length tr2 = 1" "path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)"
        by auto
      moreover obtain y2 where "ys2 = [y2]"
        using \<open>length ys2 = 1\<close>
        by (metis One_nat_def \<open>length [0] = length ys2 \<and> length [0] = length tr2
            \<and> path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)\<close> append.simps(1) append_butlast_last_id
            butlast_snoc length_butlast length_greater_0_conv list.size(3) nat.simps(3))
      moreover obtain t2 where "tr2 = [t2]"
        using \<open>length tr2 = 1\<close>
        by (metis One_nat_def \<open>length [0] = length ys2 \<and> length [0] = length tr2
            \<and> path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)\<close> append.simps(1) append_butlast_last_id
            butlast_snoc length_butlast length_greater_0_conv list.size(3) nat.simps(3))
      ultimately have "path M\<^sub>S [((0,y2),t2)] (initial M\<^sub>S)"
        by auto
      then have "t2 \<in> succ M\<^sub>S (0,y2) (initial M\<^sub>S)"
        by auto
      moreover have "\<And> y . succ M\<^sub>S (0,y) (initial M\<^sub>S) \<subseteq> {1}"
        by auto
      ultimately have "t2 = 1"
        by blast

      show "target (([0] || ys2) || tr2) (initial M\<^sub>S) = 1"
        using \<open>ys2 = [y2]\<close> \<open>tr2 = [t2]\<close> \<open>t2 = 1\<close> by auto
    qed
    then show "\<forall>ys2 tr2.
       length [0] = length ys2 \<and> length [0] = length tr2
          \<and> path M\<^sub>S (([0] || ys2) || tr2) (initial M\<^sub>S)
            \<longrightarrow> target (([0] || ys2) || tr2) (initial M\<^sub>S) = 1"
      by auto
  qed

  then have "d_reaches M\<^sub>S (initial M\<^sub>S) [0] 1"
    unfolding d_reaches.simps by blast
  then have "1 \<in> d_reachable M\<^sub>S (initial M\<^sub>S)"
    unfolding d_reachable.simps by blast

  then have "{0,1} \<subseteq> d_reachable M\<^sub>S (initial M\<^sub>S)"
    using \<open>initial M\<^sub>S \<in> d_reachable M\<^sub>S (initial M\<^sub>S)\<close> by auto
  moreover have "d_reachable M\<^sub>S (initial M\<^sub>S) \<subseteq> nodes M\<^sub>S"
  proof
    fix s assume "s\<in>d_reachable M\<^sub>S (initial M\<^sub>S)"
    then have "s \<in> reachable M\<^sub>S (initial M\<^sub>S)"
      using d_reachable_reachable by auto
    then show "s \<in> nodes M\<^sub>S"
      by blast
  qed
  ultimately have "d_reachable M\<^sub>S (initial M\<^sub>S) = {0,1}"
    using example_nodes(1) by blast



  fix f' :: "nat \<Rightarrow> nat list"
  let ?f = "f'( 0 := [], 1 := [0])"

  have "is_det_state_cover_ass M\<^sub>S ?f"
    unfolding is_det_state_cover_ass.simps
  proof
    show "?f (initial M\<^sub>S) = []" by auto
    show "\<forall>s\<in>d_reachable M\<^sub>S (initial M\<^sub>S). d_reaches M\<^sub>S (initial M\<^sub>S) (?f s) s"
    proof
      fix s assume "s\<in>d_reachable M\<^sub>S (initial M\<^sub>S)"
      then have "s \<in> reachable M\<^sub>S (initial M\<^sub>S)"
        using d_reachable_reachable by auto
      then have "s \<in> nodes M\<^sub>S"
        by blast
      then have "s = 0 \<or> s = 1"
        using example_nodes(1) by blast
      then show "d_reaches M\<^sub>S (initial M\<^sub>S) (?f s) s"
      proof
        assume "s = 0"
        then show "d_reaches M\<^sub>S (initial M\<^sub>S) (?f s) s"
          using \<open>d_reaches M\<^sub>S (initial M\<^sub>S) [] (initial M\<^sub>S)\<close> by auto
      next
        assume "s = 1"
        then show "d_reaches M\<^sub>S (initial M\<^sub>S) (?f s) s"
          using \<open>d_reaches M\<^sub>S (initial M\<^sub>S) [0] 1\<close> by auto
      qed
    qed
  qed

  moreover have "V\<^sub>I = image ?f (d_reachable M\<^sub>S (initial M\<^sub>S))"
    using \<open>d_reachable M\<^sub>S (initial M\<^sub>S) = {0,1}\<close> by auto

  ultimately show ?thesis
    unfolding is_det_state_cover.simps by blast
qed



abbreviation "\<Omega>\<^sub>I::(nat,nat) ATC set \<equiv> { Node 0 (\<lambda> y . Leaf) }"

lemma "applicable_set M\<^sub>S \<Omega>\<^sub>I"
  by auto


lemma example_test_tools : "test_tools M\<^sub>S M\<^sub>I FAIL\<^sub>I PM\<^sub>I V\<^sub>I \<Omega>\<^sub>I"
  using example_productF example_det_state_cover by auto




lemma OFSM_not_vacuous :
  "\<exists> M :: (nat,nat,nat) FSM . OFSM M"
  using example_OFSM(1) by blast


lemma fault_domain_not_vacuous :
  "\<exists> (M2::(nat,nat,nat) FSM) (M1::(nat,nat,nat) FSM) m . asc_fault_domain M2 M1 m"
  using example_fault_domain by blast


lemma test_tools_not_vacuous :
  "\<exists> (M2::(nat,nat,nat) FSM)
     (M1::(nat,nat,nat) FSM)
     (FAIL::(nat\<times>nat))
     (PM::(nat,nat,nat\<times>nat) FSM)
     (V::(nat list set))
     (\<Omega>::(nat,nat) ATC set) . test_tools M2 M1 FAIL PM V \<Omega>"
proof (rule exI, rule exI)
  show "\<exists> FAIL PM V \<Omega>. test_tools M\<^sub>S M\<^sub>I FAIL PM V \<Omega>"
    using example_test_tools by blast
qed

lemma precondition_not_vacuous :
  shows "\<exists> (M2::(nat,nat,nat) FSM)
           (M1::(nat,nat,nat) FSM)
           (FAIL::(nat\<times>nat))
           (PM::(nat,nat,nat\<times>nat) FSM)
           (V::(nat list set))
           (\<Omega>::(nat,nat) ATC set)
           (m :: nat) .
              OFSM M1 \<and> OFSM M2 \<and> asc_fault_domain M2 M1 m \<and> test_tools M2 M1 FAIL PM V \<Omega>"
proof (intro exI)
  show "OFSM M\<^sub>I \<and> OFSM M\<^sub>S \<and> asc_fault_domain M\<^sub>S M\<^sub>I 2 \<and> test_tools M\<^sub>S M\<^sub>I FAIL\<^sub>I PM\<^sub>I V\<^sub>I \<Omega>\<^sub>I"
    using example_OFSM(2,1) example_fault_domain example_test_tools by linarith
qed

end
