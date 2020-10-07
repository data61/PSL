theory "Bound_Effect"
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Frechet_Correctness"
  "Static_Semantics"
  "Coincidence"
begin
section \<open>Bound Effect Theorem\<close>
text \<open>The bound effect lemma says that a program can only modify its bound variables and nothing else.
  This is one of the major lemmas for showing correctness of uniform substitution. \<close>

context ids begin
lemma bound_effect:
  fixes I::"('sf,'sc,'sz) interp"
  assumes good_interp:"is_interp I"
  shows "\<And>\<nu> :: 'sz state. \<And>\<omega> ::'sz state. hpsafe \<alpha> \<Longrightarrow> (\<nu>, \<omega>) \<in> prog_sem I \<alpha> \<Longrightarrow> Vagree \<nu> \<omega> (- (BVP \<alpha>))"
proof (induct rule: hp_induct)
  case Var then show "?case" 
    using agree_nil Compl_UNIV_eq BVP.simps(1) by fastforce
next
  case Test then show "?case"
    by auto(simp add: agree_refl Compl_UNIV_eq Vagree_def)
next
  case (Choice a b \<nu> \<omega>)
  assume IH1:"\<And>\<nu>'. \<And>\<omega>'. hpsafe a \<Longrightarrow>((\<nu>', \<omega>') \<in> prog_sem I a \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP a))"
  assume IH2:"\<And>\<nu>'. \<And>\<omega>'. hpsafe b \<Longrightarrow>((\<nu>', \<omega>') \<in> prog_sem I b \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP b))"
  assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (a \<union>\<union> b)"
  assume safe:"hpsafe (Choice a b)"
  from safe have safes:"hpsafe a" "hpsafe b" by (auto dest: hpsafe.cases)
  have sems:"(\<nu>, \<omega>) \<in> prog_sem I (a) \<or> (\<nu>, \<omega>) \<in> prog_sem I (b)" using sem by auto
  have agrees:"Vagree \<nu> \<omega> (- BVP a) \<or> Vagree \<nu> \<omega> (- BVP b)" using IH1 IH2 sems safes by blast
  have sub1:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
  have sub2:"-(BVP a) \<supseteq> (- BVP a \<inter> - BVP b)" by auto
  have res:"Vagree \<nu> \<omega> (- BVP a \<inter> - BVP b)" using agrees sub1 sub2 agree_supset by blast
  then show "?case" by auto
next
  case (Compose a b \<nu> \<omega>) 
  assume IH1:"\<And>\<nu>'. \<And>\<omega>'. hpsafe a \<Longrightarrow> (\<nu>', \<omega>') \<in> prog_sem I a \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP a)"
  assume IH2:"\<And>\<nu>'. \<And>\<omega>'. hpsafe b \<Longrightarrow> (\<nu>', \<omega>') \<in> prog_sem I b \<Longrightarrow> Vagree \<nu>' \<omega>' (- BVP b)"
  assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (a ;; b)"
  assume safe:"hpsafe (a ;; b)"
  from safe have safes:"hpsafe a" "hpsafe b" by (auto dest: hpsafe.cases)  
  then show "?case" 
    using agree_trans IH1 IH2 sem safes by fastforce
next
  fix ODE::"('sf,'sz) ODE" and P::"('sf,'sc,'sz) formula" and \<nu> \<omega>
  assume safe:"hpsafe (EvolveODE ODE P)"
  from safe have osafe:"osafe ODE" and fsafe:"fsafe P" by (auto dest: hpsafe.cases)
  show "(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P) \<Longrightarrow> Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))"
  proof -
    assume sem:"(\<nu>, \<omega>) \<in> prog_sem I (EvolveODE ODE P)"
    from sem have agree:"Vagree \<nu> \<omega> (- BVO ODE)"
      apply(simp only: prog_sem.simps(8) mem_Collect_eq osafe fsafe)
      apply(erule exE)+
    proof -
      fix \<nu>' sol t  
      assume assm:
        "(\<nu>, \<omega>) = (\<nu>', mk_v I ODE \<nu>' (sol t)) \<and>
         0 \<le> t \<and>
         (sol solves_ode (\<lambda>_. ODE_sem I ODE)) {0..t} {x. mk_v I ODE \<nu>' x \<in> fml_sem I P} \<and>  (sol 0) = (fst \<nu>')"
      have semBV:"-BVO ODE \<subseteq> -semBV I ODE"
        by(induction ODE, auto)
      from assm have "Vagree \<omega> \<nu> (- BVO ODE)" using mk_v_agree[of I ODE \<nu> "(sol t)"] 
        using agree_sub[OF semBV] by auto
      thus  "Vagree \<nu> \<omega> (- BVO ODE)" by (rule agree_comm)
    qed 
    thus "Vagree \<nu> \<omega> (- BVP (EvolveODE ODE P))" by auto
  qed
next
  case (Star a \<nu> \<omega>) then
  have IH:"(\<And>\<nu> \<omega>. hpsafe a \<Longrightarrow> (\<nu>, \<omega>) \<in> prog_sem I a \<Longrightarrow> Vagree \<nu> \<omega> (- BVP a))"
    and safe:"hpsafe a**"
    and sem:"(\<nu>, \<omega>) \<in> prog_sem I a**"
    by auto
  from safe have asafe:"hpsafe a" by (auto dest: hpsafe.cases)
  show "Vagree \<nu> \<omega> (- BVP a**)" 
    using sem apply (simp only: prog_sem.simps)
    apply (erule converse_rtrancl_induct)
     subgoal by(rule agree_refl)
    subgoal for y z using IH[of y z, OF asafe] sem by (auto simp add: Vagree_def)
    done
qed (auto simp add: Vagree_def)
end end
