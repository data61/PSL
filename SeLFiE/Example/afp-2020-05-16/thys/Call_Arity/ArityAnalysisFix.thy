theory ArityAnalysisFix
imports ArityAnalysisSig ArityAnalysisAbinds
begin

context ArityAnalysis
begin

definition Afix ::  "heap \<Rightarrow> (AEnv \<rightarrow> AEnv)"
  where "Afix \<Gamma> = (\<Lambda> ae. (\<mu>  ae'. ABinds \<Gamma> \<cdot> ae' \<squnion> ae))"

lemma Afix_eq: "Afix \<Gamma>\<cdot>ae = (\<mu> ae'. (ABinds \<Gamma>\<cdot>ae') \<squnion> ae)"
  unfolding Afix_def by simp

lemma Afix_strict[simp]: "Afix \<Gamma>\<cdot>\<bottom> = \<bottom>"
  unfolding Afix_eq
  by (rule fix_eqI) auto

lemma Afix_least_below: "ABinds \<Gamma> \<cdot> ae' \<sqsubseteq> ae' \<Longrightarrow> ae \<sqsubseteq> ae' \<Longrightarrow> Afix \<Gamma> \<cdot> ae \<sqsubseteq> ae'"
  unfolding Afix_eq
  by (auto intro: fix_least_below)

lemma Afix_unroll: "Afix \<Gamma>\<cdot>ae = ABinds \<Gamma> \<cdot> (Afix \<Gamma>\<cdot>ae) \<squnion> ae"
  unfolding Afix_eq
  apply (subst fix_eq)
  by simp

lemma Abinds_below_Afix: "ABinds \<Delta> \<sqsubseteq> Afix \<Delta>"
  apply (rule cfun_belowI)
  apply (simp add: Afix_eq)
  apply (subst fix_eq, simp)
  apply (rule below_trans[OF _ join_above2])
  apply (rule monofun_cfun_arg)
  apply (subst fix_eq, simp)
  done

lemma Afix_above_arg: "ae \<sqsubseteq> Afix \<Gamma> \<cdot> ae"
  by (subst Afix_unroll) simp

lemma Abinds_Afix_below[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) \<sqsubseteq> Afix \<Gamma>\<cdot>ae"
  apply (subst Afix_unroll) back
  apply simp
  done


(*lemma Abinds_Afix[simp]: "ABinds \<Gamma>\<cdot>(Afix \<Gamma>\<cdot>ae) = Afix \<Gamma>\<cdot>ae"
  unfolding Afix_eq
  apply (subst fix_eq) back apply simp
  apply (rule below_trans[OF ABinds_above_arg monofun_cfun_arg])
  apply (subst fix_eq) apply simp
  done
*)

lemma Afix_reorder: "map_of \<Gamma> = map_of \<Delta> \<Longrightarrow> Afix \<Gamma> = Afix \<Delta>"
  by (intro cfun_eqI)(simp add: Afix_eq cong: Abinds_reorder)

lemma Afix_repeat_singleton: "(\<mu> xa. Afix \<Gamma>\<cdot>(esing x\<cdot>(n \<squnion> xa x) \<squnion> ae)) = Afix \<Gamma>\<cdot>(esing x\<cdot>n \<squnion> ae)"
  apply (rule below_antisym)
  defer
  apply (subst fix_eq, simp)
  apply (intro monofun_cfun_arg join_mono below_refl join_above1)

  apply (rule fix_least_below, simp)
  apply (rule Afix_least_below, simp)
  apply (intro join_below below_refl iffD2[OF esing_below_iff] below_trans[OF _ fun_belowD[OF Afix_above_arg]]  below_trans[OF _ Afix_above_arg] join_above1)
  apply simp
  done

lemma Afix_join_fresh: "ae' ` (domA \<Delta>) \<subseteq> {\<bottom>}  \<Longrightarrow>  Afix \<Delta>\<cdot>(ae \<squnion> ae') = (Afix \<Delta>\<cdot>ae) \<squnion> ae'"
  apply (rule below_antisym)
  apply (rule Afix_least_below)
  apply (subst Abinds_join_fresh, simp)
  apply (rule below_trans[OF Abinds_Afix_below join_above1])
  apply (rule join_below)
  apply (rule below_trans[OF Afix_above_arg join_above1])
  apply (rule join_above2)
  apply (rule join_below[OF monofun_cfun_arg [OF join_above1]])
  apply (rule below_trans[OF join_above2 Afix_above_arg])
  done


lemma Afix_restr_fresh:
  assumes "atom ` S \<sharp>* \<Gamma>"
  shows "Afix \<Gamma>\<cdot>ae f|` (- S) = Afix \<Gamma>\<cdot>(ae  f|` (- S)) f|` (- S)"
  unfolding Afix_eq
proof (rule parallel_fix_ind[where P = "\<lambda> x y . x f|` (- S) = y  f|` (- S)"], goal_cases)
  case 1
  show ?case by simp
next
  case 2
  show ?case ..
next
  case prems: (3 aeL aeR)
  have "(ABinds \<Gamma>\<cdot>aeL \<squnion> ae) f|` (- S) = ABinds \<Gamma>\<cdot>aeL  f|` (- S) \<squnion> ae  f|` (- S)" by (simp add: env_restr_join)
  also have "\<dots> = ABinds \<Gamma>\<cdot>(aeL  f|` (- S)) f|` (- S) \<squnion> ae  f|` (- S)" by (rule arg_cong[OF ABinds_restr_fresh[OF assms]])
  also have "\<dots> = ABinds \<Gamma>\<cdot>(aeR  f|` (- S)) f|` (- S) \<squnion> ae  f|` (- S)" unfolding prems ..
  also have "\<dots> = ABinds \<Gamma>\<cdot>aeR f|` (- S) \<squnion> ae  f|` (- S)" by (rule arg_cong[OF ABinds_restr_fresh[OF assms, symmetric]])
  also have "\<dots> = (ABinds \<Gamma>\<cdot>aeR \<squnion> ae f|` (- S)) f|` (- S)" by (simp add: env_restr_join)
  finally show ?case by simp
qed

lemma Afix_restr:
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae  f|` S) f|` S"
  unfolding Afix_eq
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . x f|`S = y  f|` S"])
  apply simp
  apply rule
  apply (auto   simp add: env_restr_join)
  apply (metis  ABinds_restr[OF assms, symmetric])
  done

lemma Afix_restr_subst':
  assumes "\<And> x' e a. (x',e) \<in> set \<Gamma> \<Longrightarrow> Aexp e[x::=y]\<cdot>a f|` S = Aexp e\<cdot>a f|` S"
  assumes "x \<notin> S"
  assumes "y \<notin> S"
  assumes "domA \<Gamma> \<subseteq> S"
  shows "Afix \<Gamma>[x::h=y]\<cdot>ae f|` S = Afix \<Gamma>\<cdot>(ae f|` S) f|` S"
  unfolding Afix_eq
  apply (rule parallel_fix_ind[where P = "\<lambda> x y . x f|`S = y  f|` S"])
  apply simp
  apply rule
  apply (auto   simp add: env_restr_join)
  apply (subst ABinds_restr_subst[OF assms]) apply assumption
  apply (subst ABinds_restr[OF assms(4)]) back
  apply simp
  done

 
lemma Afix_subst_approx:
  assumes "\<And> v n. v \<in> domA \<Gamma> \<Longrightarrow> Aexp (the (map_of \<Gamma> v))[y::=x]\<cdot>n \<sqsubseteq> (Aexp (the (map_of \<Gamma> v))\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"
  assumes "x \<notin> domA \<Gamma>"
  assumes "y \<notin> domA \<Gamma>"
  shows "Afix \<Gamma>[y::h= x]\<cdot>(ae(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (Afix \<Gamma>\<cdot>ae)(y := \<bottom>, x := up\<cdot>0)"
  unfolding Afix_eq
proof (rule parallel_fix_ind[where P = "\<lambda> aeL aeR . aeL \<sqsubseteq> aeR(y := \<bottom>, x := up\<cdot>0)"], goal_cases)
  case 1
  show ?case by simp
next
  case 2
  show ?case..
next
  case (3 aeL aeR)
  hence "ABinds \<Gamma>[y::h=x]\<cdot>aeL \<sqsubseteq> ABinds \<Gamma>[y::h=x]\<cdot>(aeR (y := \<bottom>, x := up\<cdot>0))" by (rule monofun_cfun_arg)
  also have "\<dots>  \<sqsubseteq> (ABinds \<Gamma>\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
    using assms
  proof (induction rule: ABinds.induct, goal_cases)
    case 1
    thus ?case by simp
  next
    case prems: (2 v e \<Gamma>)
    have "\<And>n. Aexp e[y::=x]\<cdot>n \<sqsubseteq> (Aexp e\<cdot>n)(y := \<bottom>, x := up\<cdot>0)" using prems(2)[where v = v] by auto
    hence IH1: "\<And> n. fup\<cdot>(Aexp e[y::=x])\<cdot>n \<sqsubseteq> (fup\<cdot>(Aexp e)\<cdot>n)(y := \<bottom>, x := up\<cdot>0)"  by (case_tac n) auto

    have "ABinds (delete v \<Gamma>)[y::h=x]\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
      apply (rule prems) using prems(2,3,4) by fastforce+
    hence IH2: "ABinds (delete v \<Gamma>[y::h=x])\<cdot>(aeR(y := \<bottom>, x := up\<cdot>0)) \<sqsubseteq> (ABinds (delete v \<Gamma>)\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
       unfolding subst_heap_delete.
    
    have [simp]: "(aeR(y := \<bottom>, x := up\<cdot>0)) v = aeR v" using prems(3,4) by auto
   
    show ?case by (simp del: fun_upd_apply join_comm) (rule join_mono[OF IH1 IH2])
  qed
  finally have "ABinds \<Gamma>[y::h=x]\<cdot>aeL \<sqsubseteq> (ABinds \<Gamma>\<cdot>aeR)(y := \<bottom>, x := up\<cdot>0)"
    by this simp
  thus ?case
    by (auto simp add: join_below_iff elim: below_trans)
qed

end

lemma Afix_eqvt[eqvt]: "\<pi> \<bullet> (ArityAnalysis.Afix Aexp \<Gamma>) = ArityAnalysis.Afix  (\<pi> \<bullet> Aexp) (\<pi> \<bullet> \<Gamma>)"
  unfolding ArityAnalysis.Afix_def
  by perm_simp (simp add: Abs_cfun_eqvt)


lemma Afix_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> aexp1 e = aexp2 e); heap1 = heap2 \<rbrakk>
      \<Longrightarrow> ArityAnalysis.Afix aexp1 heap1 = ArityAnalysis.Afix aexp2 heap2"
   unfolding ArityAnalysis.Afix_def by (metis Abinds_cong)


context EdomArityAnalysis
begin

lemma Afix_edom: "edom (Afix \<Gamma> \<cdot> ae) \<subseteq> fv \<Gamma> \<union> edom ae"
  unfolding Afix_eq
  by (rule fix_ind[where P = "\<lambda> ae' . edom ae' \<subseteq> fv \<Gamma> \<union> edom ae"] )
     (auto dest: subsetD[OF edom_AnalBinds])

lemma ABinds_lookup_fresh:
  "atom v \<sharp> \<Gamma> \<Longrightarrow> (ABinds \<Gamma>\<cdot>ae) v = \<bottom>"
by (induct \<Gamma> rule: ABinds.induct) (auto simp add: fresh_Cons fresh_Pair fup_Aexp_lookup_fresh fresh_delete)

lemma Afix_lookup_fresh:
  assumes "atom v \<sharp> \<Gamma>"
  shows "(Afix \<Gamma>\<cdot>ae) v = ae v"
  apply (rule below_antisym)
  apply (subst Afix_eq)
  apply (rule fix_ind[where  P = "\<lambda> ae'. ae' v \<sqsubseteq> ae v"])
  apply (auto simp add: ABinds_lookup_fresh[OF assms] fun_belowD[OF Afix_above_arg])
  done

lemma Afix_comp2join_fresh:
  "atom ` (domA \<Delta>) \<sharp>* \<Gamma> \<Longrightarrow> ABinds \<Delta>\<cdot>(Afix \<Gamma>\<cdot>ae) = ABinds \<Delta>\<cdot>ae"
proof (induct \<Delta> rule: ABinds.induct)
  case 1 show ?case by (simp add: Afix_above_arg del: fun_meet_simp)
next
  case (2 v e \<Delta>)
  from 2(2)
  have "atom v \<sharp> \<Gamma>" and  "atom ` domA (delete v \<Delta>) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from 2(1)[OF this(2)]
  show ?case by (simp del: fun_meet_simp add: Afix_lookup_fresh[OF \<open>atom v \<sharp> \<Gamma>\<close>])
qed

lemma Afix_append_fresh:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>"
  shows "Afix (\<Delta> @ \<Gamma>)\<cdot>ae = Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
proof (rule below_antisym)
  show *: "Afix (\<Delta> @ \<Gamma>)\<cdot>ae \<sqsubseteq> Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae)"
  apply (rule Afix_least_below)
  apply (simp add: Abinds_append_disjoint[OF fresh_distinct[OF assms]] Afix_comp2join_fresh[OF assms])
  apply (rule below_trans[OF join_mono[OF Abinds_Afix_below Abinds_Afix_below]])
  apply (simp_all add: Afix_above_arg  below_trans[OF Afix_above_arg Afix_above_arg])
  done
next
  show "Afix \<Gamma>\<cdot>(Afix \<Delta>\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
  proof (rule Afix_least_below)
    show "ABinds \<Gamma>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule below_trans[OF _ Abinds_Afix_below])
      apply (subst Abinds_append_disjoint[OF fresh_distinct[OF assms]])
      apply simp
      done
    have "ABinds \<Delta>\<cdot>(Afix (\<Delta> @ \<Gamma>)\<cdot>ae) \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule below_trans[OF _ Abinds_Afix_below])
      apply (subst Abinds_append_disjoint[OF fresh_distinct[OF assms]])
      apply simp
      done
    thus "Afix \<Delta>\<cdot>ae \<sqsubseteq> Afix (\<Delta> @ \<Gamma>)\<cdot>ae"
      apply (rule Afix_least_below)
      apply (rule Afix_above_arg)
      done
  qed
qed


lemma Afix_e_to_heap:
   "Afix (delete x \<Gamma>)\<cdot>(fup\<cdot>(Aexp e)\<cdot>n \<squnion> ae) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(esing x\<cdot>n \<squnion> ae)"
    apply (simp add: Afix_eq)
    apply (rule fix_least_below, simp)
    apply (intro join_below)
    apply (subst fix_eq, simp)
    apply (subst fix_eq, simp)

    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule below_trans[OF _ join_above2])
    apply (rule monofun_cfun_arg)
    apply (subst fix_eq, simp)
      
    apply (subst fix_eq, simp) back apply (simp add: below_trans[OF _ join_above2])
    done

lemma Afix_e_to_heap':
   "Afix (delete x \<Gamma>)\<cdot>(Aexp e\<cdot>n) \<sqsubseteq> Afix ((x, e) # delete x \<Gamma>)\<cdot>(esing x\<cdot>(up\<cdot>n))"
using Afix_e_to_heap[where ae = \<bottom> and n = "up\<cdot>n"] by simp

end


end

