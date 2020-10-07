theory SC_Cut
imports SC
begin
  
subsubsection\<open>Contraction\<close>
  
text\<open>First, we need contraction:\<close>
lemma contract:
  "(F,F,\<Gamma> \<Rightarrow> \<Delta> \<longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta>) \<and> (\<Gamma> \<Rightarrow> F,F,\<Delta> \<longrightarrow> \<Gamma> \<Rightarrow> F,\<Delta>)"
proof(induction F arbitrary: \<Gamma> \<Delta>)
  case (Atom k)
  have "Atom k, Atom k, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> Atom k, \<Gamma> \<Rightarrow> \<Delta>"
    by(induction "Atom k, Atom k, \<Gamma>" \<Delta> arbitrary: \<Gamma> rule: SCp.induct)
      (auto dest!: multi_member_split intro!: SCp.intros(3-) simp add: lem2 lem1 SCp.intros)  
  moreover have "\<Gamma> \<Rightarrow> Atom k, Atom k, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Atom k, \<Delta>"
    by(induction "\<Gamma>" "Atom k, Atom k, \<Delta>" arbitrary: \<Delta> rule: SCp.induct)
      (auto dest!: multi_member_split intro!: SCp.intros(3-) simp add: lem2 lem1 SCp.intros)
  ultimately show ?case by blast
next
  case Bot
  have "\<bottom>, \<bottom>, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<bottom>, \<Gamma> \<Rightarrow> \<Delta>" by(induction "\<bottom>, \<bottom>, \<Gamma>" \<Delta> rule: SCp.induct; blast)
  moreover have "(\<Gamma> \<Rightarrow> \<bottom>, \<bottom>, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<bottom>, \<Delta>)"    
    using Bot_delR by fastforce
  ultimately show ?case by blast
next
  case (Not F)
  then show ?case by (meson NotL_inv NotR_inv SCp.NotL SCp.NotR)
next
  case (And F1 F2) then show ?case by(auto intro!: SCp.intros(3-) dest!: AndR_inv AndL_inv) (metis add_mset_commute)
next
  case (Or F1 F2) then show ?case by(auto intro!: SCp.intros(3-) dest!: OrR_inv OrL_inv) (metis add_mset_commute)
next
  (* Okay, so the induction hypothesis is poison for the simplifier. 
     For some reason, this didn't cause trouble for the other two cases, but here, it does. *)
  case (Imp F1 F2) show ?case by(auto dest!: ImpR_inv ImpL_inv intro!: SCp.intros(3-)) (insert Imp.IH; blast)+
qed
corollary
  shows contractL: "F, F, \<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> F, \<Gamma> \<Rightarrow> \<Delta>"
  and contractR:   "\<Gamma> \<Rightarrow> F, F, \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> F, \<Delta>"
  using contract by blast+
    
subsubsection\<open>Cut\<close>
  
text\<open>Which cut rule we show is up to us:\<close>
lemma cut_cs_cf:
  assumes context_sharing_Cut: "\<And>(A::'a formula) \<Gamma> \<Delta>. \<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
  shows context_free_Cut: "\<Gamma> \<Rightarrow> (A::'a formula),\<Delta> \<Longrightarrow> A,\<Gamma>' \<Rightarrow> \<Delta>' \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  by(intro context_sharing_Cut[of "\<Gamma> + \<Gamma>'" A "\<Delta> + \<Delta>'"])
    (metis add.commute union_mset_add_mset_left weakenL_set weakenR_set)+
lemma cut_cf_cs:
  assumes context_free_Cut: "\<And>(A::'a formula) \<Gamma> \<Gamma>' \<Delta> \<Delta>'. \<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma>' \<Rightarrow> \<Delta>' \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  shows context_sharing_Cut: "\<Gamma> \<Rightarrow> (A::'a formula),\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof - 
  have contract\<Gamma>\<Gamma>: "\<Gamma>+\<Gamma>' \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>' \<subseteq># \<Gamma> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>" for \<Gamma> \<Gamma>' \<Delta>
  proof(induction "\<Gamma>'" arbitrary: \<Gamma>)
    case empty thus ?case using weakenL_set by force
  next
    case (add x \<Gamma>' \<Gamma>)
    from add.prems(2) have "x \<in># \<Gamma>" by (simp add: insert_subset_eq_iff)
    then obtain \<Gamma>'' where \<Gamma>[simp]: "\<Gamma> = x,\<Gamma>''" by (meson multi_member_split)
    from add.prems(1) have "x,x,\<Gamma>'' + \<Gamma>' \<Rightarrow> \<Delta>" by simp
    with contractL have "x, \<Gamma>'' + \<Gamma>' \<Rightarrow> \<Delta>" .
    with add.IH[of \<Gamma>] show ?case using \<Gamma>  add.prems(2) subset_mset.order.trans by force
  qed
  have contract\<Delta>\<Delta>: "\<Gamma> \<Rightarrow> \<Delta>+\<Delta>' \<Longrightarrow> \<Delta>' \<subseteq># \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>" for \<Gamma> \<Delta> \<Delta>'
  proof(induction "\<Delta>'" arbitrary: \<Delta>)
    case empty thus ?case using weakenL_set by force
  next
    case (add x \<Delta>' \<Delta>)
    from add.prems(2) have "x \<in># \<Delta>" by (simp add: insert_subset_eq_iff)
    then obtain \<Delta>'' where \<Delta>[simp]: "\<Delta> = x,\<Delta>''" by (metis multi_member_split)
    from add.prems(1) have "\<Gamma> \<Rightarrow> x,x,\<Delta>'' + \<Delta>'" by simp
    with contractR have "\<Gamma> \<Rightarrow> x, \<Delta>'' + \<Delta>'" .
    with add.IH[of \<Delta>] show ?case using \<Delta> add.prems(2) subset_mset.order.trans by force
  qed
  show "\<Gamma> \<Rightarrow> A,\<Delta> \<Longrightarrow> A,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
    using context_free_Cut[of \<Gamma> A \<Delta> \<Gamma> \<Delta>] contract\<Gamma>\<Gamma> contract\<Delta>\<Delta>
    by blast
qed
(* since these are the only lemmas that need contraction on sets, I've decided to transfer those in place *)
text\<open>According to Troelstra and Schwichtenberg~\cite{troelstra2000basic}, the sharing variant is the one we want to prove.\<close>
  
lemma Cut_Atom_pre: "Atom k,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> Atom k,\<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction "Atom k,\<Gamma>" "\<Delta>" arbitrary: \<Gamma> rule: SCp.induct)
  case BotL
  hence "\<bottom> \<in># \<Gamma>" by simp
  thus ?case using SCp.BotL by blast
next
  case (Ax l \<Delta>)
  show ?case proof cases
    assume "l = k"
    with \<open>Atom l \<in># \<Delta>\<close> obtain \<Delta>' where "\<Delta> = Atom k, \<Delta>'" by (meson multi_member_split)
    with \<open>\<Gamma> \<Rightarrow> Atom k, \<Delta>\<close> have "\<Gamma> \<Rightarrow> \<Delta>" using contractR by blast
    thus ?thesis by auto
  next
    assume "l \<noteq> k"
    with \<open>Atom l \<in># Atom k, \<Gamma>\<close> have "Atom l \<in># \<Gamma>" by simp
    with \<open>Atom l \<in># \<Delta>\<close> show ?thesis using SCp.Ax[of l] by blast
  qed
next
  case NotL
  thus ?case by(auto simp: add_eq_conv_ex intro!: SCp.NotL dest!: NotL_inv)
next
  case NotR
  then show ?case by(auto intro!: SCp.NotR dest!: NotR_inv)
next
  case AndL
  thus ?case by(auto simp: add_eq_conv_ex intro!: SCp.AndL dest!: AndL_inv)
next
  case AndR
  then show ?case by(auto intro!: SCp.AndR dest!: AndR_inv)
next
  case OrL
  thus ?case by(auto simp: add_eq_conv_ex intro!: SCp.OrL dest!: OrL_inv)
next
  case OrR
  thus ?case by(auto intro!: SCp.OrR dest!: OrR_inv)
next
  case ImpL
  thus ?case by(auto simp: add_eq_conv_ex intro!: SCp.ImpL dest!: ImpL_inv)
next
  case ImpR
  then show ?case by (auto dest!: ImpR_inv intro!: SCp.ImpR)
qed
  
text\<open>We can show the admissibility of the cut rule by induction on the cut formula 
(or, if you will, as a procedure that splits the cut into smaller formulas that get cut).
The only mildly complicated case is that of cutting in an @{term "Atom k"}.
It is, contrary to the general case, only mildly complicated, since the cut formula can only appear principal in the axiom rules.\<close>

theorem cut: "\<Gamma> \<Rightarrow> F,\<Delta> \<Longrightarrow> F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma> \<Rightarrow> \<Delta>"
proof(induction F arbitrary: \<Gamma> \<Delta>)
  case Atom thus ?case using Cut_Atom_pre by metis
next
  case Bot thus ?case using Bot_delR by fastforce 
next
  case Not with  NotL_inv NotR_inv show ?case by blast
next
  case And thus ?case by (meson AndL_inv AndR_inv weakenL)
next
  case Or thus ?case by (metis OrL_inv OrR_inv weakenR)
next
  case (Imp F G)
(* an automatic proof:
  thus ?case by (meson ImpL_inv ImpR_inv weakenR)
   a readable one: *)
  from ImpR_inv \<open>\<Gamma> \<Rightarrow> F \<^bold>\<rightarrow> G, \<Delta>\<close> have R: "F, \<Gamma> \<Rightarrow> G, \<Delta>" by blast
  from ImpL_inv \<open>F \<^bold>\<rightarrow> G, \<Gamma> \<Rightarrow> \<Delta>\<close> have L: "\<Gamma> \<Rightarrow> F, \<Delta>" "G, \<Gamma> \<Rightarrow> \<Delta>" by blast+
  from L(1) have "\<Gamma> \<Rightarrow> F, G, \<Delta>" using weakenR add_ac(3) by blast
  with R have "\<Gamma> \<Rightarrow> G, \<Delta>" using Imp.IH(1) by simp
  with L(2) show "\<Gamma> \<Rightarrow> \<Delta>" using Imp.IH(2) by clarsimp
qed
  (* For this proof to work with FOL, I think we would need very special inversion rules.
  For example, for \<forall>R, we would need that there's a (finite!) multiset of substitutions S, such that
  instead of having \<forall>x.F,\<Delta>, having {F[s/x] | s \<in> S} + \<Delta> is enough. I don't think that holds,
  but we may be able to cheat ourselves around it\<dots> *)
  
corollary cut_cf: "\<lbrakk> \<Gamma> \<Rightarrow> A, \<Delta>; A, \<Gamma>' \<Rightarrow> \<Delta>'\<rbrakk> \<Longrightarrow> \<Gamma> + \<Gamma>' \<Rightarrow> \<Delta> + \<Delta>'"
  using cut_cs_cf cut by metis

lemma assumes cut: "\<And> \<Gamma>' \<Delta>' (A::'a formula). \<lbrakk>\<Gamma>' \<Rightarrow> A, \<Delta>'; A, \<Gamma>' \<Rightarrow> \<Delta>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<Rightarrow> \<Delta>'"
  shows contraction_admissibility: "F,F,\<Gamma> \<Rightarrow> \<Delta> \<Longrightarrow> (F::'a formula),\<Gamma> \<Rightarrow> \<Delta>"
  by(rule cut[of "F,\<Gamma>" F \<Delta>, OF extended_Ax]) simp_all
(* yes, unpublished Chapman p 2/5, second to last paragraph. that's right. we can prove contraction with cut. but what's that good for? *)
  
end
