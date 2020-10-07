theory "Value"
  imports HOLCF
begin

subsubsection \<open>The semantic domain for values and environments\<close>

domain Value = Fn (lazy "Value \<rightarrow> Value") | B (lazy "bool discr")

fixrec Fn_project :: "Value \<rightarrow> Value \<rightarrow> Value"
 where "Fn_project\<cdot>(Fn\<cdot>f) = f"

abbreviation Fn_project_abbr (infix "\<down>Fn" 55)
  where "f \<down>Fn v \<equiv> Fn_project\<cdot>f\<cdot>v"

lemma [simp]:
  "\<bottom> \<down>Fn x = \<bottom>"
  "(B\<cdot>b) \<down>Fn x = \<bottom>"
  by (fixrec_simp)+

fixrec B_project :: "Value \<rightarrow> Value \<rightarrow> Value \<rightarrow> Value" where
  "B_project\<cdot>(B\<cdot>db)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if undiscr db then v\<^sub>1 else v\<^sub>2)"

lemma [simp]:
  "B_project\<cdot>(B\<cdot>(Discr b))\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = (if b then v\<^sub>1 else v\<^sub>2)"
  "B_project\<cdot>\<bottom>\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
  "B_project\<cdot>(Fn\<cdot>f)\<cdot>v\<^sub>1\<cdot>v\<^sub>2 = \<bottom>"
by fixrec_simp+

text \<open>
A chain in the domain @{typ Value} is either always bottom, or eventually @{term "Fn"} of another
chain
\<close>

lemma Value_chainE[consumes 1, case_names bot B Fn]:
  assumes "chain Y"
  obtains "Y = (\<lambda> _ . \<bottom>)" |
          n b where "Y = (\<lambda> m. (if m < n then \<bottom> else B\<cdot>b))" |
          n Y' where "Y = (\<lambda> m. (if m < n then \<bottom> else Fn\<cdot>(Y' (m-n))))" "chain Y'"
proof(cases "Y = (\<lambda> _ . \<bottom>)")
  case True
  thus ?thesis by (rule that(1))
next
  case False
  hence "\<exists> i. Y i \<noteq> \<bottom>" by auto
  hence "\<exists> n. Y n \<noteq> \<bottom> \<and> (\<forall>m. Y m \<noteq> \<bottom> \<longrightarrow> m \<ge> n)"
    by (rule exE)(rule ex_has_least_nat)
  then obtain n where "Y n \<noteq> \<bottom>" and "\<forall>m. m < n \<longrightarrow> Y m = \<bottom>" by fastforce
  hence "(\<exists> f. Y n = Fn\<cdot>f) \<or> (\<exists> b. Y n = B\<cdot>b)" by (metis Value.exhaust)
  thus ?thesis
  proof
    assume "(\<exists> f. Y n = Fn\<cdot>f)"
    then obtain f where "Y n = Fn \<cdot> f" by blast
    {
      fix i
      from \<open>chain Y\<close> have "Y n \<sqsubseteq> Y (i+n)" by (metis chain_mono le_add2)
      with \<open>Y n = _\<close>
      have "\<exists> g. (Y (i+n) = Fn \<cdot> g)"
        by (metis Value.dist_les(1) Value.exhaust below_bottom_iff)
    }
    then obtain Y' where Y': "\<And> i. Y (i + n) = Fn \<cdot> (Y' i)" by metis

    have "Y = (\<lambda>m. if m < n then \<bottom> else Fn\<cdot>(Y' (m - n)))"
        using \<open>\<forall>m. _\<close> Y' by (metis add_diff_inverse add.commute)
    moreover
    have"chain Y'" using \<open>chain Y\<close>
      by (auto intro!:chainI elim: chainE  simp add: Value.inverts[symmetric] Y'[symmetric] simp del: Value.inverts)
    ultimately
    show ?thesis by (rule that(3))
  next
    assume "(\<exists> b. Y n = B\<cdot>b)"
    then obtain b where "Y n = B\<cdot>b" by blast
    {
      fix i
      from \<open>chain Y\<close> have "Y n \<sqsubseteq> Y (i+n)" by (metis chain_mono le_add2)
      with \<open>Y n = _\<close>
      have "Y (i+n) = B\<cdot>b"
        by (metis Value.dist_les(2) Value.exhaust Value.inverts(2) below_bottom_iff discrete_cpo)
    }
    hence  Y': "\<And> i. Y (i + n) = B\<cdot>b" by metis

    have "Y = (\<lambda>m. if m < n then \<bottom> else B\<cdot>b)"
        using \<open>\<forall>m. _\<close> Y' by (metis add_diff_inverse add.commute)
    thus ?thesis by (rule that(2))
  qed
qed


end
