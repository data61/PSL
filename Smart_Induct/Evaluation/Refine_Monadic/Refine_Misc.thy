section \<open>Miscellanneous Lemmas and Tools\<close>
theory Refine_Misc
imports 
  Automatic_Refinement.Automatic_Refinement
  Refine_Mono_Prover
begin

text \<open>Basic configuration for monotonicity prover:\<close>
lemmas [refine_mono] = monoI monotoneI[of "(\<le>)" "(\<le>)"]
lemmas [refine_mono] = TrueI le_funI order_refl

lemma case_prod_mono[refine_mono]: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> f a b \<le> f' a b\<rbrakk> \<Longrightarrow> case_prod f p \<le> case_prod f' p"
  by (auto split: prod.split)

lemma case_option_mono[refine_mono]:
  assumes "fn \<le> fn'"
  assumes "\<And>v. x=Some v \<Longrightarrow> fs v \<le> fs' v"
  shows "case_option fn fs x \<le> case_option fn' fs' x"
  using assms by (auto split: option.split)

lemma case_list_mono[refine_mono]:
  assumes "fn \<le> fn'"
  assumes "\<And>x xs. l=x#xs \<Longrightarrow> fc x xs \<le> fc' x xs"
  shows "case_list fn fc l \<le> case_list fn' fc' l"
  using assms by (auto split: list.split)

lemma if_mono[refine_mono]:
  assumes "b \<Longrightarrow> m1 \<le> m1'"
  assumes "\<not>b \<Longrightarrow> m2 \<le> m2'"
  shows "(if b then m1 else m2) \<le> (if b then m1' else m2')"
  using assms by auto

lemma let_mono[refine_mono]:
  "f x \<le> f' x' \<Longrightarrow> Let x f \<le> Let x' f'" by auto


subsection \<open>Uncategorized Lemmas\<close>
lemma all_nat_split_at: "\<forall>i::'a::linorder<k. P i \<Longrightarrow> P k \<Longrightarrow> \<forall>i>k. P i 
  \<Longrightarrow> \<forall>i. P i"
  by (metis linorder_neq_iff)

subsection \<open>Well-Foundedness\<close>

lemma wf_no_infinite_down_chainI:
  assumes "\<And>f. \<lbrakk>\<And>i. (f (Suc i), f i)\<in>r\<rbrakk> \<Longrightarrow> False"
  shows "wf r"
  by (metis assms wf_iff_no_infinite_down_chain)

text \<open>This lemma transfers well-foundedness over a simulation relation.\<close>
lemma sim_wf:
  assumes WF: "wf (S'\<inverse>)"
  assumes STARTR: "(x0,x0')\<in>R"
  assumes SIM: "\<And>s s' t. \<lbrakk> (s,s')\<in>R; (s,t)\<in>S; (x0',s')\<in>S'\<^sup>* \<rbrakk> 
    \<Longrightarrow> \<exists>t'. (s',t')\<in>S' \<and> (t,t')\<in>R"
  assumes CLOSED: "Domain S  \<subseteq> S\<^sup>*``{x0}"
  shows "wf (S\<inverse>)"
proof (rule wf_no_infinite_down_chainI, simp)
  txt \<open>
    Informal proof:
    Assume there is an infinite chain in \<open>S\<close>.
    Due to the closedness property of \<open>S\<close>, it can be extended to 
    start at \<open>x0\<close>.
    Now, we inductively construct an infinite chain in \<open>S'\<close>, such that
    each element of the new chain is in relation with the corresponding 
    element of the original chain:
      The first element is \<open>x0'\<close>. 
      For any element \<open>i+1\<close>, the simulation property yields the next
      element.
    This chain contradicts well-foundedness of \<open>S'\<close>.
\<close>

  fix f
  assume CHAIN: "\<And>i. (f i, f (Suc i))\<in>S"
  txt \<open>Extend to start with \<open>x0\<close>\<close>
  obtain f' where CHAIN': "\<And>i. (f' i, f' (Suc i))\<in>S" and [simp]: "f' 0 = x0"
  proof -
    {
      fix x
      assume S: "x = f 0"
      from CHAIN have "f 0 \<in> Domain S" by auto
      with CLOSED have "(x0,x)\<in>S\<^sup>*" by (auto simp: S)
      then obtain g k where G0: "g 0 = x0" and X: "x = g k" 
        and CH: "(\<forall>i<k. (g i, g (Suc i))\<in>S)"
      proof induct
        case base thus ?case by force
      next
        case (step y z) show ?case proof (rule step.hyps(3))
          fix g k 
          assume "g 0 = x0" and "y = g k" 
            and "\<forall>i<k. (g i, g (Suc i))\<in>S"
          thus ?case using \<open>(y,z)\<in>S\<close>
            by (rule_tac step.prems[where g="g(Suc k := z)" and k="Suc k"])
              auto
        qed
      qed
      define f' where "f' i = (if i<k then g i else f (i-k))" for i
      have "\<exists>f'. f' 0 = x0 \<and> (\<forall>i. (f' i, f' (Suc i))\<in>S)"
        apply (rule_tac x=f' in exI)
        apply (unfold f'_def)
        apply (rule conjI)
        using S X G0 apply (auto) []
        apply (rule_tac k=k in all_nat_split_at)
        apply (auto)
        apply (simp add: CH)
        apply (subgoal_tac "k = Suc i")
        apply (simp add: S[symmetric] CH X)
        apply simp
        apply (simp add: CHAIN)
        apply (subgoal_tac "Suc i - k = Suc (i-k)")
        using CHAIN apply simp
        apply simp
        done
    }
    then obtain f' where "\<forall>i. (f' i,f' (Suc i))\<in>S" and "f' 0 = x0" by blast
    thus ?thesis by (blast intro!: that)
  qed

  txt \<open>Construct chain in \<open>S'\<close>\<close>
  define g' where "g' = rec_nat x0' (\<lambda>i x. SOME x'. 
          (x,x')\<in>S' \<and> (f' (Suc i),x')\<in>R \<and> (x0', x')\<in>S'\<^sup>* )"
  {
    fix i
    note [simp] = g'_def
    have "(g' i, g' (Suc i))\<in>S' \<and> (f' (Suc i),g' (Suc i))\<in>R 
      \<and> (x0',g' (Suc i))\<in>S'\<^sup>*"
    proof (induct i)
      case 0 
      from SIM[OF STARTR] CHAIN'[of 0] obtain t' where 
        "(x0',t')\<in>S'" and "(f' (Suc 0),t')\<in>R" by auto
      moreover hence "(x0',t')\<in>S'\<^sup>*" by auto
      ultimately show ?case
        by (auto intro: someI2 simp: STARTR)
    next
      case (Suc i)
      with SIM[OF _ CHAIN'[of "Suc i"]] 
      obtain t' where LS: "(g' (Suc i),t')\<in>S'" and "(f' (Suc (Suc i)),t')\<in>R"
        by auto
      moreover from LS Suc have "(x0', t')\<in>S'\<^sup>*" by auto
      ultimately show ?case
        apply simp
        apply (rule_tac a="t'" in someI2)
        apply auto
        done
    qed
  } hence S'CHAIN: "\<forall>i. (g' i, g'(Suc i))\<in>S'" by simp
  txt \<open>This contradicts well-foundedness\<close>
  with WF show False 
    by (erule_tac wf_no_infinite_down_chainE[where f=g']) simp
qed

text \<open>Well-founded relation that approximates a finite set from below.\<close>
definition "finite_psupset S \<equiv> { (Q',Q). Q\<subset>Q' \<and> Q' \<subseteq> S }"
lemma finite_psupset_wf[simp, intro]: "finite S \<Longrightarrow> wf (finite_psupset S)"
  unfolding finite_psupset_def by (blast intro: wf_bounded_supset)

definition "less_than_bool \<equiv> {(a,b). a<(b::bool)}"
lemma wf_less_than_bool[simp, intro!]: "wf (less_than_bool)"
  unfolding less_than_bool_def
  by (auto simp: wf_def)
lemma less_than_bool_iff[simp]:
  "(x,y)\<in>less_than_bool \<longleftrightarrow> x=False \<and> y=True"  
  by (auto simp: less_than_bool_def)

definition "greater_bounded N \<equiv> inv_image less_than (\<lambda>x. N-x)" 
lemma wf_greater_bounded[simp, intro!]: "wf (greater_bounded N)" by (auto simp: greater_bounded_def)

lemma greater_bounded_Suc_iff[simp]: "(Suc x,x)\<in>greater_bounded N \<longleftrightarrow> Suc x \<le> N"
  by (auto simp: greater_bounded_def)

    
    
subsection \<open>Monotonicity and Orderings\<close>

lemma mono_const[simp, intro!]: "mono (\<lambda>_. c)" by (auto intro: monoI)
lemma mono_if: "\<lbrakk>mono S1; mono S2\<rbrakk> \<Longrightarrow>
  mono (\<lambda>F s. if b s then S1 F s else S2 F s)"
  apply rule
  apply (rule le_funI)
  apply (auto dest: monoD[THEN le_funD])
  done

lemma mono_infI: "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (inf f g)"
  unfolding inf_fun_def
  apply (rule monoI)
  apply (metis inf_mono monoD)
  done

lemma mono_infI': 
  "mono f \<Longrightarrow> mono g \<Longrightarrow> mono (\<lambda>x. inf (f x) (g x) :: 'b::lattice)"
  by (rule mono_infI[unfolded inf_fun_def])

lemma mono_infArg: 
  fixes f :: "'a::lattice \<Rightarrow> 'b::order"
  shows "mono f \<Longrightarrow> mono (\<lambda>x. f (inf x X))"
  apply (rule monoI)
  apply (erule monoD)
  apply (metis inf_mono order_refl) 
  done

lemma mono_Sup:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> Sup (f`S) \<le> f (Sup S)"
  apply (rule Sup_least)
  apply (erule imageE)
  apply simp
  apply (erule monoD)
  apply (erule Sup_upper)
  done

lemma mono_SupI:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes "mono f"
  assumes "S'\<subseteq>f`S"
  shows "Sup S' \<le> f (Sup S)"
  by (metis Sup_subset_mono assms mono_Sup order_trans)

lemma mono_Inf:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "mono f \<Longrightarrow> f (Inf S) \<le> Inf (f`S)"
  apply (rule Inf_greatest)
  apply (erule imageE)
  apply simp
  apply (erule monoD)
  apply (erule Inf_lower)
  done

lemma mono_funpow: "mono (f::'a::order \<Rightarrow> 'a) \<Longrightarrow> mono (f^^i)"
  apply (induct i)
  apply (auto intro!: monoI) 
  apply (auto dest: monoD)
  done

lemma mono_id[simp, intro!]:
  "mono id"
  "mono (\<lambda>x. x)"
  by (auto intro: monoI)

declare SUP_insert[simp]

lemma (in semilattice_inf) le_infD1:
  "a \<le> inf b c \<Longrightarrow> a \<le> b" by (rule le_infE)
lemma (in semilattice_inf) le_infD2:
  "a \<le> inf b c \<Longrightarrow> a \<le> c" by (rule le_infE)
lemma (in semilattice_inf) inf_leI:
  "\<lbrakk> \<And>x. \<lbrakk> x\<le>a; x\<le>b \<rbrakk> \<Longrightarrow> x\<le>c \<rbrakk> \<Longrightarrow> inf a b \<le> c"
  by (metis inf_le1 inf_le2)

lemma top_Sup: "(top::'a::complete_lattice)\<in>A \<Longrightarrow> Sup A = top"
  by (metis Sup_upper top_le)
lemma bot_Inf: "(bot::'a::complete_lattice)\<in>A \<Longrightarrow> Inf A = bot"
  by (metis Inf_lower le_bot)

lemma mono_compD: "mono f \<Longrightarrow> x\<le>y \<Longrightarrow> f o x \<le> f o y"
  apply (rule le_funI)
  apply (auto dest: monoD le_funD)
  done


subsubsection \<open>Galois Connections\<close>
locale galois_connection =
  fixes \<alpha>::"'a::complete_lattice \<Rightarrow> 'b::complete_lattice" and \<gamma>
  assumes galois: "c \<le> \<gamma>(a) \<longleftrightarrow> \<alpha>(c) \<le> a"
begin
  lemma \<alpha>\<gamma>_defl: "\<alpha>(\<gamma>(x)) \<le> x"
  proof -
    have "\<gamma> x \<le> \<gamma> x" by simp
    with galois show "\<alpha>(\<gamma>(x)) \<le> x" by blast
  qed
  lemma \<gamma>\<alpha>_infl: "x \<le> \<gamma>(\<alpha>(x))"
  proof -
    have "\<alpha> x \<le> \<alpha> x" by simp
    with galois show "x \<le> \<gamma>(\<alpha>(x))" by blast
  qed
    
  lemma \<alpha>_mono: "mono \<alpha>"
  proof 
    fix x::'a and y::'a
    assume "x\<le>y"
    also note \<gamma>\<alpha>_infl[of y]
    finally show "\<alpha> x \<le> \<alpha> y" by (simp add: galois)
  qed

  lemma \<gamma>_mono: "mono \<gamma>"
    by rule (metis \<alpha>\<gamma>_defl galois inf_absorb1 le_infE)

  lemma dist_\<gamma>[simp]: 
    "\<gamma> (inf a b) = inf (\<gamma> a) (\<gamma> b)"
    apply (rule order_antisym)
    apply (rule mono_inf[OF \<gamma>_mono])
    apply (simp add: galois)
    apply (simp add: galois[symmetric])
    done

  lemma dist_\<alpha>[simp]: 
    "\<alpha> (sup a b) = sup (\<alpha> a) (\<alpha> b)"
    by (metis (no_types) \<alpha>_mono galois mono_sup order_antisym 
      sup_ge1 sup_ge2 sup_least)

end

subsubsection \<open>Fixed Points\<close>
lemma mono_lfp_eqI:
  assumes MONO: "mono f"
  assumes FIXP: "f a \<le> a"
  assumes LEAST: "\<And>x. f x = x \<Longrightarrow> a\<le>x"
  shows "lfp f = a"
  apply (rule antisym)
  apply (rule lfp_lowerbound)
  apply (rule FIXP)
  by (metis LEAST MONO lfp_unfold)

lemma mono_gfp_eqI:
  assumes MONO: "mono f"
  assumes FIXP: "a \<le> f a"
  assumes GREATEST: "\<And>x. f x = x \<Longrightarrow> x\<le>a"
  shows "gfp f = a"
  apply (rule antisym)
  apply (metis GREATEST MONO gfp_unfold)
  apply (rule gfp_upperbound)
  apply (rule FIXP)
  done

lemma lfp_le_gfp': "mono f \<Longrightarrow> lfp f x \<le> gfp f x"
  by (rule le_funD[OF lfp_le_gfp])

(* Just a reformulation of lfp_induct *)
lemma lfp_induct':
  assumes M: "mono f"
  assumes IS: "\<And>m. \<lbrakk> m \<le> lfp f; m \<le> P \<rbrakk> \<Longrightarrow> f m \<le> P"
  shows "lfp f \<le> P"
  apply (rule lfp_induct[OF M])
  apply (rule IS)
  by simp_all

lemma lfp_gen_induct:
  \<comment> \<open>Induction lemma for generalized lfps\<close>
  assumes M: "mono f"
  notes MONO'[refine_mono] = monoD[OF M]
  assumes I0: "m0 \<le> P"
  assumes IS: "\<And>m. \<lbrakk>
      m \<le> lfp (\<lambda>s. sup m0 (f s));  \<comment> \<open>Assume already established invariants\<close>
      m \<le> P;                       \<comment> \<open>Assume invariant\<close>
      f m \<le> lfp (\<lambda>s. sup m0 (f s)) \<comment> \<open>Assume that step preserved est. invars\<close>
    \<rbrakk> \<Longrightarrow> f m \<le> P"                 \<comment> \<open>Show that step preserves invariant\<close>
  shows "lfp (\<lambda>s. sup m0 (f s)) \<le> P"
  apply (rule lfp_induct')
  apply (meson MONO' monoI order_mono_setup.refl sup_mono)
  apply (rule sup_least)
  apply (rule I0)
  apply (rule IS, assumption+)
  apply (subst lfp_unfold)
  apply (meson MONO' monoI order_mono_setup.refl sup_mono)
  apply (rule le_supI2)
  apply (rule monoD[OF M])
  .



subsubsection \<open>Connecting Complete Lattices and 
  Chain-Complete Partial Orders\<close>
(* Note: Also connected by subclass now. However, we need both directions
  of embedding*)
lemma (in complete_lattice) is_ccpo: "class.ccpo Sup (\<le>) (<)"
  apply unfold_locales
  apply (erule Sup_upper)
  apply (erule Sup_least)
  done

lemma (in complete_lattice) is_dual_ccpo: "class.ccpo Inf (\<ge>) (>)"
  apply unfold_locales
  apply (rule less_le_not_le)
  apply (rule order_refl)
  apply (erule (1) order_trans)
  apply (erule (1) antisym)
  apply (erule Inf_lower)
  apply (erule Inf_greatest)
  done
  
  
lemma ccpo_mono_simp: "monotone (\<le>) (\<le>) f \<longleftrightarrow> mono f"
  unfolding monotone_def mono_def by simp
lemma ccpo_monoI: "mono f \<Longrightarrow> monotone (\<le>) (\<le>) f" 
  by (simp add: ccpo_mono_simp) 
lemma ccpo_monoD: "monotone (\<le>) (\<le>) f \<Longrightarrow> mono f" 
  by (simp add: ccpo_mono_simp) 

lemma dual_ccpo_mono_simp: "monotone (\<ge>) (\<ge>) f \<longleftrightarrow> mono f"
  unfolding monotone_def mono_def by auto
lemma dual_ccpo_monoI: "mono f \<Longrightarrow> monotone (\<ge>) (\<ge>) f" 
  by (simp add: dual_ccpo_mono_simp) 
lemma dual_ccpo_monoD: "monotone (\<ge>) (\<ge>) f \<Longrightarrow> mono f" 
  by (simp add: dual_ccpo_mono_simp) 

lemma ccpo_lfp_simp: "\<And>f. mono f \<Longrightarrow> ccpo.fixp Sup (\<le>) f = lfp f"
  apply (rule antisym)
  defer
  apply (rule lfp_lowerbound)
  apply (drule ccpo.fixp_unfold[OF is_ccpo ccpo_monoI, symmetric])
  apply simp

  apply (rule ccpo.fixp_lowerbound[OF is_ccpo ccpo_monoI], assumption)
  apply (simp add: lfp_unfold[symmetric])
  done

lemma ccpo_gfp_simp: "\<And>f. mono f \<Longrightarrow> ccpo.fixp Inf (\<ge>) f = gfp f"
  apply (rule antisym)
  apply (rule gfp_upperbound)
  apply (drule ccpo.fixp_unfold[OF is_dual_ccpo dual_ccpo_monoI, symmetric])
  apply simp

  apply (rule ccpo.fixp_lowerbound[OF is_dual_ccpo dual_ccpo_monoI], assumption)
  apply (simp add: gfp_unfold[symmetric])
  done

abbreviation "chain_admissible P \<equiv> ccpo.admissible Sup (\<le>) P"
abbreviation "is_chain \<equiv> Complete_Partial_Order.chain (\<le>)"
lemmas chain_admissibleI[intro?] = ccpo.admissibleI[where lub=Sup and ord="(\<le>)"]


abbreviation "dual_chain_admissible P \<equiv> ccpo.admissible Inf (\<lambda>x y. y\<le>x) P"
abbreviation "is_dual_chain \<equiv> Complete_Partial_Order.chain (\<lambda>x y. y\<le>x)"
lemmas dual_chain_admissibleI[intro?] = 
  ccpo.admissibleI[where lub=Inf and ord="(\<lambda>x y. y\<le>x)"]

lemma dual_chain_iff[simp]: "is_dual_chain C = is_chain C"
  unfolding chain_def
  apply auto
  done

lemmas chain_dualI = iffD1[OF dual_chain_iff]
lemmas dual_chainI = iffD2[OF dual_chain_iff]

lemma is_chain_empty[simp, intro!]: "is_chain {}"
  by (rule chainI) auto
lemma is_dual_chain_empty[simp, intro!]: "is_dual_chain {}"
  by (rule dual_chainI) auto

lemma point_chainI: "is_chain M \<Longrightarrow> is_chain ((\<lambda>f. f x)`M)"
  by (auto intro: chainI le_funI dest: chainD le_funD)


text \<open>We transfer the admissible induction lemmas to complete
  lattices.\<close>
lemma lfp_cadm_induct:
  "\<lbrakk>chain_admissible P; P (Sup {}); mono f; \<And>x. P x \<Longrightarrow> P (f x)\<rbrakk> \<Longrightarrow> P (lfp f)"
  by (simp only: ccpo_mono_simp[symmetric] ccpo_lfp_simp[symmetric])
     (rule ccpo.fixp_induct[OF is_ccpo])

lemma gfp_cadm_induct:
  "\<lbrakk>dual_chain_admissible P; P (Inf {}); mono f; \<And>x. P x \<Longrightarrow> P (f x)\<rbrakk> \<Longrightarrow> P (gfp f)"
  by (simp only: dual_ccpo_mono_simp[symmetric] ccpo_gfp_simp[symmetric])
     (rule ccpo.fixp_induct[OF is_dual_ccpo])

subsubsection \<open>Continuity and Kleene Fixed Point Theorem\<close>
definition "cont f \<equiv> \<forall>C. C\<noteq>{} \<longrightarrow> f (Sup C) = Sup (f`C)"
definition "strict f \<equiv> f bot = bot"
definition "inf_distrib f \<equiv> strict f \<and> cont f"

lemma contI[intro?]: "\<lbrakk>\<And>C. C\<noteq>{} \<Longrightarrow> f (Sup C) = Sup (f`C)\<rbrakk> \<Longrightarrow> cont f" 
  unfolding cont_def by auto
lemma contD: "cont f \<Longrightarrow> C\<noteq>{} \<Longrightarrow> f (Sup C) = Sup (f ` C)"
  unfolding cont_def by auto
lemma contD': "cont f \<Longrightarrow> C\<noteq>{} \<Longrightarrow> f (Sup C) = Sup (f ` C)"
  by (fact contD)

lemma strictD[dest]: "strict f \<Longrightarrow> f bot = bot" 
  unfolding strict_def by auto
\<comment> \<open>We only add this lemma to the simpset for functions on the same type. 
    Otherwise, the simplifier tries it much too often.\<close>
lemma strictD_simp[simp]: "strict f \<Longrightarrow> f (bot::'a::bot) = (bot::'a)" 
  unfolding strict_def by auto

lemma strictI[intro?]: "f bot = bot \<Longrightarrow> strict f"
  unfolding strict_def by auto

lemma inf_distribD[simp]: 
  "inf_distrib f \<Longrightarrow> strict f"
  "inf_distrib f \<Longrightarrow> cont f"
  unfolding inf_distrib_def by auto

lemma inf_distribI[intro?]: "\<lbrakk>strict f; cont f\<rbrakk> \<Longrightarrow> inf_distrib f"
  unfolding inf_distrib_def by auto

lemma inf_distribD'[simp]:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "inf_distrib f \<Longrightarrow> f (Sup C) = Sup (f`C)"
  apply (cases "C={}")
  apply (auto dest: inf_distribD contD')
  done

lemma inf_distribI':
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  assumes B: "\<And>C. f (Sup C) = Sup (f`C)"
  shows "inf_distrib f"
  apply (rule)
  apply (rule)
  apply (rule B[of "{}", simplified])
  apply (rule)
  apply (rule B)
  done
  
lemma cont_is_mono[simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "cont f \<Longrightarrow> mono f"
  apply (rule monoI)
  apply (drule_tac C="{x,y}" in contD)
  apply (auto simp: le_iff_sup)
  done

lemma inf_distrib_is_mono[simp]: 
  fixes f :: "'a::complete_lattice \<Rightarrow> 'b::complete_lattice"
  shows "inf_distrib f \<Longrightarrow> mono f"
  by simp

text \<open>Only proven for complete lattices here. Also holds for CCPOs.\<close>

theorem gen_kleene_lfp:
  fixes f:: "'a::complete_lattice \<Rightarrow> 'a"
  assumes CONT: "cont f"
  shows "lfp (\<lambda>x. sup m (f x)) = (SUP i. (f^^i) m)"
proof (rule antisym)
  let ?f = "(\<lambda>x. sup m (f x))"
  let ?K="{ (f^^i) m | i . True}"
  note MONO=cont_is_mono[OF CONT]
  note MONO'[refine_mono] = monoD[OF MONO]
  {
    fix i
    have "(f^^i) m \<le> lfp ?f"
      apply (induct i)
      apply simp
      apply (subst lfp_unfold)
      apply (meson MONO' monoI order_mono_setup.refl sup_mono) 
      apply simp
      
      apply (subst lfp_unfold)
      apply (meson MONO' monoI order_mono_setup.refl sup_mono) 
      apply simp
      by (metis MONO' le_supI2)
  } thus "(SUP i. (f^^i) m) \<le> lfp ?f" by (blast intro: SUP_least)
next
  let ?f = "(\<lambda>x. sup m (f x))"
  show "lfp ?f \<le> (SUP i. (f^^i) m)"
    apply (rule lfp_lowerbound)
    apply (rule sup_least)
    apply (rule order_trans[OF _ SUP_upper[where i=0]], simp_all) []
    apply (simp add: contD [OF CONT])
    apply (rule Sup_subset_mono)
    apply (auto)
    apply (rule_tac x="Suc i" in range_eqI)
    apply simp
    done
qed

theorem kleene_lfp:
  fixes f:: "'a::complete_lattice \<Rightarrow> 'a"
  assumes CONT: "cont f"
  shows "lfp f = (SUP i. (f^^i) bot)"
  using gen_kleene_lfp[OF CONT,where m=bot] by simp

theorem (* Detailed proof *)
  fixes f:: "'a::complete_lattice \<Rightarrow> 'a"
  assumes CONT: "cont f"
  shows "lfp f = (SUP i. (f^^i) bot)"
proof (rule antisym)
  let ?K="{ (f^^i) bot | i . True}"
  note MONO=cont_is_mono[OF CONT]
  {
    fix i
    have "(f^^i) bot \<le> lfp f"
      apply (induct i)
      apply simp
      apply simp
      by (metis MONO lfp_unfold monoD)
  } thus "(SUP i. (f^^i) bot) \<le> lfp f" by (blast intro: SUP_least)
next
  show "lfp f \<le> (SUP i. (f^^i) bot)"
    apply (rule lfp_lowerbound)
    apply (simp add: contD [OF CONT])
    apply (rule Sup_subset_mono)
    apply auto
    apply (rule_tac x="Suc i" in range_eqI)
    apply auto
    done
qed

(* Alternative proof of gen_kleene_lfp that re-uses standard Kleene, but is more tedious *)
lemma SUP_funpow_contracting:
  fixes f :: "'a \<Rightarrow> ('a::complete_lattice)"
  assumes C: "cont f" 
  shows "f (SUP i. (f^^i) m) \<le> (SUP i. (f^^i) m)"
proof -
  have 1: "\<And>i x. f ((f^^i) x) = (f^^(Suc i)) x"
    by simp

  have "f (SUP i. (f^^i) m) = (SUP i. f ((f ^^ i) m))"
    by (subst contD[OF C]) (simp_all add: image_comp)
  also have "\<dots> \<le> (SUP i. (f^^i) m)"
    apply (rule SUP_least)
    apply (simp, subst 1)
    apply (rule SUP_upper)
    ..
  finally show ?thesis .
qed

lemma gen_kleene_chain_conv:
  fixes f :: "'a::complete_lattice \<Rightarrow> 'a"
  assumes C: "cont f"
  shows "(SUP i. (f^^i) m) = (SUP i. ((\<lambda>x. sup m (f x))^^i) bot)"
proof -
  let ?f' = "\<lambda>x. sup m (f x)"
  show ?thesis
  proof (intro antisym SUP_least)
    from C have C': "cont ?f'"
      unfolding cont_def
      by (simp add: SUP_sup_distrib[symmetric])
  
    fix i
    show "(f ^^ i) m \<le> (SUP i. (?f' ^^ i) bot)"
    proof (induction i)
      case 0 show ?case
        by (rule order_trans[OF _ SUP_upper[where i=1]]) auto
    next
      case (Suc i)
      from cont_is_mono[OF C, THEN monoD, OF Suc]
      have "(f ^^ (Suc i)) m \<le> f (SUP i. ((\<lambda>x. sup m (f x)) ^^ i) bot)"
        by simp
      also have "\<dots> \<le> sup m \<dots>" by simp
      also note SUP_funpow_contracting[OF C']
      finally show ?case .
    qed
  next
    fix i
    show "(?f'^^i) bot \<le> (SUP i. (f^^i) m)"
    proof (induction i)
      case 0 thus ?case by simp
    next
      case (Suc i)
      from monoD[OF cont_is_mono[OF C] Suc]
      have "(?f'^^Suc i) bot \<le> sup m (f (SUP i. (f ^^ i) m))" 
        by (simp add: le_supI2)
      also have "\<dots> \<le> (SUP i. (f ^^ i) m)"
        apply (rule sup_least)
        apply (rule order_trans[OF _ SUP_upper[where i=0]], simp_all) []
        apply (rule SUP_funpow_contracting[OF C])
        done
      finally show ?case .
    qed
  qed
qed
   
theorem 
  assumes C: "cont f"
  shows "lfp (\<lambda>x. sup m (f x)) = (SUP i. (f^^i) m)"
  apply (subst gen_kleene_chain_conv[OF C])
  apply (rule kleene_lfp)
    using C
    unfolding cont_def
    apply (simp add: SUP_sup_distrib[symmetric])
  done



lemma (in galois_connection) dual_inf_dist_\<gamma>: "\<gamma> (Inf C) = Inf (\<gamma>`C)"
  apply (rule antisym)
  apply (rule Inf_greatest)
  apply clarify
  apply (rule monoD[OF \<gamma>_mono])
  apply (rule Inf_lower)
  apply simp

  apply (subst galois)
  apply (rule Inf_greatest)
  apply (subst galois[symmetric])
  apply (rule Inf_lower)
  apply simp
  done

lemma (in galois_connection) inf_dist_\<alpha>: "inf_distrib \<alpha>"
  apply (rule inf_distribI')
  apply (rule antisym)

  apply (subst galois[symmetric])
  apply (rule Sup_least)
  apply (subst galois)
  apply (rule Sup_upper)
  apply simp

  apply (rule Sup_least)
  apply clarify
  apply (rule monoD[OF \<alpha>_mono])
  apply (rule Sup_upper)
  apply simp
  done

subsection \<open>Maps\<close>
subsubsection \<open>Key-Value Set\<close>
  
  lemma map_to_set_simps[simp]: 
    "map_to_set Map.empty = {}"
    "map_to_set [a\<mapsto>b] = {(a,b)}"
    "map_to_set (m|`K) = map_to_set m \<inter> K\<times>UNIV"
    "map_to_set (m(x:=None)) = map_to_set m - {x}\<times>UNIV"
    "map_to_set (m(x\<mapsto>v)) = map_to_set m - {x}\<times>UNIV \<union> {(x,v)}"
    "map_to_set m \<inter> dom m\<times>UNIV = map_to_set m"
    "m k = Some v \<Longrightarrow> (k,v)\<in>map_to_set m"
    "single_valued (map_to_set m)"
    apply (simp_all)
    by (auto simp: map_to_set_def restrict_map_def split: if_split_asm
      intro: single_valuedI)
      
  lemma map_to_set_inj:     
    "(k,v)\<in>map_to_set m \<Longrightarrow> (k,v')\<in>map_to_set m \<Longrightarrow> v = v'"
    by (auto simp: map_to_set_def)


end
