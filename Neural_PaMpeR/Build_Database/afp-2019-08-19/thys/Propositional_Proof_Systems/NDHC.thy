subsection\<open>ND to HC\<close>
theory NDHC
imports ND HC
begin

text\<open>The fundamental difference between the two is that Natural Deduction updates its set of assumptions while Hilbert Calculus does not.
The Deduction Theorem @{thm Deduction_theorem} helps with this.\<close>
theorem NDHC: "\<Gamma> \<turnstile> F \<Longrightarrow> AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F"
proof(induction rule: ND.induct)
  case Ax thus ?case by(auto intro: HC.Ax)
next
  case NotE thus ?case by (meson AX10.intros(9) HC.simps subsetCE sup_ge1)
next
  case (NotI  F \<Gamma>)
  from HC_intros(11) have HC_NotI: "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H A \<^bold>\<rightarrow> \<bottom> \<Longrightarrow> AX10 \<union> \<Gamma> \<turnstile>\<^sub>H \<^bold>\<not> A" for A 
    using MP HC_mono by (metis sup_ge1)
  from NotI show ?case using Deduction_theorem[where \<Gamma>="AX10 \<union> \<Gamma>"] HC_NotI by (metis AX100 Un_assoc Un_insert_right)
next
  case (CC F \<Gamma>)
  hence "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H \<^bold>\<not> F \<^bold>\<rightarrow> \<bottom>" using Deduction_theorem[where \<Gamma>="AX10 \<union> \<Gamma>"] by (metis AX100 Un_assoc Un_insert_right)
  thus "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F" using AX10.intros(10) by (metis HC.simps UnCI)
next
  case (AndE1 \<Gamma> F G) thus ?case by (meson AX10.intros(5) HC.simps UnCI)
next
  case (AndE2 \<Gamma> F G) thus ?case by (meson AX10.intros(6) HC.simps UnCI)
next
  case (AndI \<Gamma> F G) thus ?case by (meson HC_intros(10) HC_mono HC.simps sup_ge1)
next
  case (OrE \<Gamma> F G H)
  from \<open>AX10 \<union> (F \<triangleright> \<Gamma>) \<turnstile>\<^sub>H H\<close> \<open>AX10 \<union> (G \<triangleright> \<Gamma>) \<turnstile>\<^sub>H H\<close> have
       "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> H" "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H G \<^bold>\<rightarrow> H"
    using Deduction_theorem[where \<Gamma>="AX10 \<union> \<Gamma>"] by (metis AX100 Un_assoc Un_insert_right)+
  with HC_intros(7)[THEN HC_mono[OF _ sup_ge1]] MP
  have "AX10 \<union> \<Gamma> \<turnstile>\<^sub>H  (F \<^bold>\<or> G) \<^bold>\<rightarrow> H" by metis
  with MP \<open>AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<or> G\<close> show ?case  .
next
  case (OrI1 \<Gamma> F G) thus ?case by (meson AX10.intros(2) HC.simps UnCI)
next
  case (OrI2 \<Gamma> F G) thus ?case by (meson AX10.intros(3) HC.simps UnCI)
next
  case (ImpE \<Gamma> F G) 
  from MP  \<open>AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F\<close>  \<open>AX10 \<union> \<Gamma> \<turnstile>\<^sub>H F \<^bold>\<rightarrow> G\<close> show ?case .
next
  case (ImpI F \<Gamma> G) thus ?case using Deduction_theorem[where \<Gamma>="AX10 \<union> \<Gamma>"] by (metis AX100 Un_assoc Un_insert_right)
qed

end
