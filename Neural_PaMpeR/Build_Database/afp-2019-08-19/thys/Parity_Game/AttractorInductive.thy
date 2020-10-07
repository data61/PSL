section \<open>Defining the Attractor with \texttt{inductive\_set}\<close>

theory AttractorInductive
imports
  Main
  Attractor
begin

context ParityGame begin

text \<open>
  In section \ref{sec:attractor} we defined @{const attractor} manually via @{const lfp}.
  We can also define it with \texttt{inductive\_set}.  In this section, we do exactly this and
  prove that the new definition yields the same set as the old definition.
\<close>

subsection \<open>@{term attractor_inductive}\<close>

text \<open>The attractor set of a given set of nodes, defined inductively.\<close>
inductive_set attractor_inductive :: "Player \<Rightarrow> 'a set \<Rightarrow> 'a set"
  for p :: Player and W :: "'a set" where
  Base [intro!]: "v \<in> W \<Longrightarrow> v \<in> attractor_inductive p W"
| VVp: "\<lbrakk> v \<in> VV p; \<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W \<rbrakk>
    \<Longrightarrow> v \<in> attractor_inductive p W"
| VVpstar: "\<lbrakk> v \<in> VV p**; \<not>deadend v; \<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> attractor_inductive p W \<rbrakk>
    \<Longrightarrow> v \<in> attractor_inductive p W"

text \<open>
  We show that the inductive definition and the definition via least fixed point are the same.
\<close>
lemma attractor_inductive_is_attractor:
  assumes "W \<subseteq> V"
  shows "attractor_inductive p W = attractor p W"
proof
  show "attractor_inductive p W \<subseteq> attractor p W" proof
    fix v assume "v \<in> attractor_inductive p W"
    thus "v \<in> attractor p W" proof (induct rule: attractor_inductive.induct)
      case (Base v) thus ?case using attractor_set_base by auto
    next
      case (VVp v) thus ?case using attractor_set_VVp by auto
    next
      case (VVpstar v) thus ?case using attractor_set_VVpstar by auto
    qed
  qed
  show "attractor p W \<subseteq> attractor_inductive p W"
  proof-
    define P where "P S \<longleftrightarrow> S \<subseteq> attractor_inductive p W" for S
    from \<open>W \<subseteq> V\<close> have "P (attractor p W)" proof (induct rule: attractor_set_induction)
      case (step S)
      hence "S \<subseteq> attractor_inductive p W" using P_def by simp
      have "W \<union> S \<union> directly_attracted p S \<subseteq> attractor_inductive p W" proof
        fix v assume "v \<in> W \<union> S \<union> directly_attracted p S"
        moreover
        { assume "v \<in> W" hence "v \<in> attractor_inductive p W" by blast }
        moreover
        { assume "v \<in> S" hence "v \<in> attractor_inductive p W"
            by (meson \<open>S \<subseteq> attractor_inductive p W\<close> rev_subsetD) }
        moreover
        { assume v_attracted: "v \<in> directly_attracted p S"
          hence "v \<in> V" using \<open>S \<subseteq> V\<close> attractor_step_bounded_by_V by blast
          hence "v \<in> attractor_inductive p W" proof (cases rule: VV_cases)
            assume "v \<in> VV p"
            hence "\<exists>w. v\<rightarrow>w \<and> w \<in> S" using v_attracted directly_attracted_def by blast
            hence "\<exists>w. v\<rightarrow>w \<and> w \<in> attractor_inductive p W"
              using \<open>S \<subseteq> attractor_inductive p W\<close> by blast
            thus ?thesis by (simp add: \<open>v \<in> VV p\<close> attractor_inductive.VVp)
          next
            assume "v \<in> VV p**"
            hence *: "\<forall>w. v\<rightarrow>w \<longrightarrow> w \<in> S" using v_attracted directly_attracted_def by blast
            have "\<not>deadend v" using v_attracted directly_attracted_def by blast
            show ?thesis proof (rule ccontr)
              assume "v \<notin> attractor_inductive p W"
              hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> attractor_inductive p W"
                by (metis attractor_inductive.VVpstar \<open>v \<in> VV p**\<close> \<open>\<not>deadend v\<close>)
              hence "\<exists>w. v\<rightarrow>w \<and> w \<notin> S" using \<open>S \<subseteq> attractor_inductive p W\<close> by (meson subsetCE)
              thus False using * by blast
            qed
          qed
        }
        ultimately show "v \<in> attractor_inductive p W" by (meson UnE)
      qed
      thus "P (W \<union> S \<union> directly_attracted p S)" using P_def by simp
    qed (simp add: P_def Sup_least)
    thus ?thesis using P_def by simp
  qed
qed

end

end
