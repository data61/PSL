section \<open>General Domain Theory\<close>
theory RefineG_Domain
imports "../Refine_Misc"
begin

  subsection \<open>General Order Theory Tools\<close>
  lemma chain_f_apply: "Complete_Partial_Order.chain (fun_ord le) F
    \<Longrightarrow> Complete_Partial_Order.chain le {y . \<exists>f\<in>F. y = f x}"
    unfolding Complete_Partial_Order.chain_def 
    by (auto simp: fun_ord_def)

  lemma ccpo_lift:
    assumes "class.ccpo lub le lt"
    shows "class.ccpo (fun_lub lub) (fun_ord le) (mk_less (fun_ord le))"
  proof -
    interpret ccpo: ccpo lub le lt by fact
    show ?thesis
      apply unfold_locales
      apply (simp_all only: mk_less_def fun_ord_def fun_lub_def)
      apply simp
      using ccpo.order_trans apply blast
      using ccpo.antisym apply blast
      using ccpo.ccpo_Sup_upper apply (blast intro: chain_f_apply)
      using ccpo.ccpo_Sup_least apply (blast intro: chain_f_apply)
      done
  qed
  
  (* TODO: Move *)
  lemma fun_lub_simps[simp]: 
    "fun_lub lub {} = (\<lambda>x. lub {})"
    "fun_lub lub {f} = (\<lambda>x. lub {f x})"
    unfolding fun_lub_def by auto

  subsection \<open>Flat Ordering\<close>
  lemma flat_ord_chain_cases: 
    assumes A: "Complete_Partial_Order.chain (flat_ord b) C"
    obtains "C={}" 
    | "C={b}" 
    | x where "x\<noteq>b" and "C={x}" 
    | x where "x\<noteq>b" and "C={b,x}"
  proof -
    have "\<exists>m1 m2. C \<subseteq> {m1,m2} \<and> (m1 = b \<or> m2 = b)"
      apply (rule ccontr)
    proof clarsimp
      assume "\<forall>m1 m2. C \<subseteq> {m1, m2} \<longrightarrow> m1\<noteq>b \<and> m2\<noteq>b"
      then obtain m1 m2 where "m1\<in>C" "m2\<in>C" 
        "m1\<noteq>m2" "m1\<noteq>b" "m2\<noteq>b"
        by blast
      with A show False
        unfolding Complete_Partial_Order.chain_def flat_ord_def
        by auto
    qed
    then obtain m where "C \<subseteq> {m,b}" by blast
    thus ?thesis 
      apply (cases "m=b") 
      using that
      apply blast+
      done
  qed
    
  lemma flat_lub_simps[simp]:
    "flat_lub b {} = b"
    "flat_lub b {x} = x"
    "flat_lub b (insert b X) = flat_lub b X"
    unfolding flat_lub_def
    by auto

  lemma flat_ord_simps[simp]:
    "flat_ord b b x" 
    by (simp add: flat_ord_def)

  interpretation flat_ord: ccpo "flat_lub b" "flat_ord b" "mk_less (flat_ord b)"
    apply unfold_locales
    apply (simp_all only: mk_less_def flat_ord_def) apply auto [4]
    apply (erule flat_ord_chain_cases, auto) []
    apply (erule flat_ord_chain_cases, auto) []
    done

  interpretation flat_le_mono_setup: mono_setup_loc "flat_ord b"
    by standard auto

  subsubsection \<open>Flat function Ordering\<close>
  abbreviation "flatf_ord b == fun_ord (flat_ord b)"
  abbreviation "flatf_lub b == fun_lub (flat_lub b)"

  interpretation flatf_ord: ccpo "flatf_lub b" "flatf_ord b" "mk_less (flatf_ord b)"
    apply (rule ccpo_lift)
    apply unfold_locales
    done

  subsubsection \<open>Fixed Points in Flat Ordering\<close>
  text \<open>
    Fixed points in a flat ordering are used to express recursion.
    The bottom element is interpreted as non-termination.
\<close>  

  abbreviation "flat_mono b == monotone (flat_ord b) (flat_ord b)"
  abbreviation "flatf_mono b == monotone (flatf_ord b) (flatf_ord b)"
  abbreviation "flatf_fp b \<equiv> flatf_ord.fixp b"

  lemma flatf_fp_mono[refine_mono]:
    \<comment> \<open>The fixed point combinator is monotonic\<close>
    assumes "flatf_mono b f"
      and "flatf_mono b g"
      and "\<And>Z x. flat_ord b (f Z x) (g Z x)"
    shows "flat_ord b (flatf_fp b f x) (flatf_fp b g x)"
  proof -
    have "flatf_ord b (flatf_fp b f) (flatf_fp b g)"
      apply (rule flatf_ord.fixp_mono[OF assms(1,2)])
      using assms(3) by (simp add: fun_ord_def)
    thus ?thesis unfolding fun_ord_def by blast
  qed

  lemma flatf_admissible_pointwise:
    "(\<And>x. P x b) \<Longrightarrow> 
      ccpo.admissible (flatf_lub b) (flatf_ord b) (\<lambda>g. \<forall>x. P x (g x))"
    apply (intro ccpo.admissibleI allI impI)
    apply (drule_tac x=x in chain_f_apply)
    apply (erule flat_ord_chain_cases)
    apply (auto simp add: fun_lub_def) [2]
    apply (force simp add: fun_lub_def) []
    apply (auto simp add: fun_lub_def) []
    done

  text \<open>
    If a property is defined pointwise, and holds for the bottom element,
    we can use fixed-point induction for it. 

    In the induction step, we can assume that the function is less or equal
    to the fixed-point.

    This rule covers refinement and transfer properties, 
    such as: Refinement of fixed-point combinators and transfer of 
    fixed-point combinators to different domains.
\<close>
  lemma flatf_fp_induct_pointwise:
    \<comment> \<open>Fixed-point induction for pointwise properties\<close>
    fixes a :: 'a
    assumes cond_bot: "\<And>a x. pre a x \<Longrightarrow> post a x b"
    assumes MONO: "flatf_mono b B"
    assumes PRE0: "pre a x"
    assumes STEP: "\<And>f a x. 
      \<lbrakk>\<And>a' x'. pre a' x' \<Longrightarrow> post a' x' (f x'); pre a x; 
        flatf_ord b f (flatf_fp b B) \<rbrakk> 
      \<Longrightarrow> post a x (B f x)"
    shows "post a x (flatf_fp b B x)"
  proof -
    define ub where "ub = flatf_fp b B"

    have "(\<forall>x a. pre a x \<longrightarrow> post a x (flatf_fp b B x)) 
      \<and> flatf_ord b (flatf_fp b B) ub"
      apply (rule flatf_ord.fixp_induct[OF _ MONO])
      apply (rule admissible_conj)
      apply (rule flatf_admissible_pointwise)
      apply (blast intro: cond_bot)
      apply (rule ccpo.admissibleI)
      apply (blast intro: flatf_ord.ccpo_Sup_least)

      apply (auto intro: cond_bot simp: fun_ord_def flat_ord_def) []

      apply (rule conjI)
      unfolding ub_def

      apply (blast intro: STEP)

      apply (subst flatf_ord.fixp_unfold[OF MONO])
      apply (blast intro: monotoneD[OF MONO])
      done
    with PRE0 show ?thesis by blast
  qed
  
  text \<open>
    The next rule covers transfer between fixed points.
    It allows to lift a pointwise transfer condition 
    \<open>P x y \<longrightarrow> tr (f x) (f y)\<close> to fixed points.
    Note that one of the fixed points may be an arbitrary fixed point.
\<close>
  lemma flatf_fixp_transfer:
    \<comment> \<open>Transfer rule for fixed points\<close>
    assumes TR_BOT[simp]: "\<And>x'. tr b x'"
    assumes MONO: "flatf_mono b B"
    assumes FP': "fp' = B' fp'"
    assumes R0: "P x x'"
    assumes RS: "\<And>f f' x x'.
       \<lbrakk>\<And>x x'. P x x' \<Longrightarrow> tr (f x) (f' x'); P x x'; fp' = f'\<rbrakk>
       \<Longrightarrow> tr (B f x) (B' f' x')"
    shows "tr (flatf_fp b B x) (fp' x')"
    apply (rule flatf_fp_induct_pointwise[where pre="\<lambda>x y. P y x", OF _ MONO])
    apply simp
    apply (rule R0)
    apply (subst FP')
    apply (blast intro: RS)
    done

  subsubsection \<open>Relation of Flat Ordering to Complete Lattices\<close>
  text \<open>
    In this section, we establish the relation between flat orderings 
    and complete lattices. This relation is exploited to show properties
    of fixed points wrt. a refinement ordering.
\<close>

  abbreviation "flat_le \<equiv> flat_ord bot"
  abbreviation "flat_ge \<equiv> flat_ord top"
  abbreviation "flatf_le \<equiv> flatf_ord bot"
  abbreviation "flatf_ge \<equiv> flatf_ord top"

  text \<open>The flat ordering implies the lattice ordering\<close>
  lemma flat_ord_compat: 
    fixes x y :: "'a :: complete_lattice"
    shows 
    "flat_le x y \<Longrightarrow> x \<le> y"
    "flat_ge x y \<Longrightarrow> x \<ge> y"
    unfolding flat_ord_def by auto

  lemma flatf_ord_compat: 
    fixes x y :: "'a \<Rightarrow> ('b :: complete_lattice)"
    shows 
    "flatf_le x y \<Longrightarrow> x \<le> y"
    "flatf_ge x y \<Longrightarrow> x \<ge> y"
    by (auto simp: flat_ord_compat le_fun_def fun_ord_def)
  
  abbreviation "flat_mono_le \<equiv> flat_mono bot"
  abbreviation "flat_mono_ge \<equiv> flat_mono top"

  abbreviation "flatf_mono_le \<equiv> flatf_mono bot"
  abbreviation "flatf_mono_ge \<equiv> flatf_mono top"

  abbreviation "flatf_gfp \<equiv> flatf_ord.fixp top"
  abbreviation "flatf_lfp \<equiv> flatf_ord.fixp bot"

  text \<open>If a functor is monotonic wrt. both the flat and the 
    lattice ordering, the fixed points wrt. these orderings coincide. 
\<close>
  lemma lfp_eq_flatf_lfp:
    assumes FM: "flatf_mono_le B" and M: "mono B"
    shows "lfp B = flatf_lfp B"
  proof -
    from lfp_unfold[OF M, symmetric] have "B (lfp B) = lfp B" .
    hence "flatf_le (B (lfp B)) (lfp B)" by simp
    with flatf_ord.fixp_lowerbound[OF FM] have "flatf_le (flatf_lfp B) (lfp B)" .
    with flatf_ord_compat have "flatf_lfp B \<le> lfp B" by blast
    also
    from flatf_ord.fixp_unfold[OF FM, symmetric] have "B (flatf_lfp B) = flatf_lfp B" .
    hence "B (flatf_lfp B) \<le> flatf_lfp B" by simp
    with lfp_lowerbound[where A="flatf_lfp B"] have "lfp B \<le> flatf_lfp B" .
    finally show "lfp B = flatf_lfp B" ..
  qed

  lemma gfp_eq_flatf_gfp:
    assumes FM: "flatf_mono_ge B" and M: "mono B"
    shows "gfp B = flatf_gfp B"
  proof -
    from gfp_unfold[OF M, symmetric] have "B (gfp B) = gfp B" .
    hence "flatf_ge (B (gfp B)) (gfp B)" by simp
    with flatf_ord.fixp_lowerbound[OF FM] have "flatf_ge (flatf_gfp B) (gfp B)" .
    with flatf_ord_compat have "gfp B \<le> flatf_gfp B" by blast
    also
    from flatf_ord.fixp_unfold[OF FM, symmetric] have "B (flatf_gfp B) = flatf_gfp B" .
    hence "flatf_gfp B \<le> B (flatf_gfp B)" by simp
    with gfp_upperbound[where X="flatf_gfp B"] have "flatf_gfp B \<le> gfp B" .
    finally show "gfp B = flatf_gfp B" .
  qed
  

  (* TODO: This belongs to "General Recursion"*)
  text \<open>
    The following lemma provides a well-founded induction scheme for arbitrary 
    fixed point combinators.
\<close>
  lemma wf_fixp_induct:
    \<comment> \<open>Well-Founded induction for arbitrary fixed points\<close>
    fixes a :: 'a
    assumes fixp_unfold: "fp B = B (fp B)"
    assumes WF: "wf V"
    assumes P0: "pre a x"
    assumes STEP: "\<And>f a x. \<lbrakk> 
      \<And>a' x'. \<lbrakk> pre a' x'; (x',x)\<in>V \<rbrakk> \<Longrightarrow> post a' x' (f x'); fp B = f; pre a x 
    \<rbrakk> \<Longrightarrow> post a x (B f x)"
    shows "post a x (fp B x)"
  proof -
    have "\<forall>a. pre a x \<longrightarrow> post a x (fp B x)"
      using WF
      apply (induct x rule: wf_induct_rule)
      apply (intro allI impI)
      apply (subst fixp_unfold)
      apply (rule STEP)
      apply (simp)
      apply (simp)
      apply (simp)
      done
    with P0 show ?thesis by blast
  qed


  lemma flatf_lfp_transfer:
    \<comment> \<open>Transfer rule for least fixed points\<close>
    fixes B::"(_ \<Rightarrow> 'a::order_bot) \<Rightarrow> _"
    assumes TR_BOT[simp]: "\<And>x. tr bot x"
    assumes MONO: "flatf_mono_le B"
    assumes MONO': "flatf_mono_le B'"
    assumes R0: "P x x'"
    assumes RS: "\<And>f f' x x'.
       \<lbrakk>\<And>x x'. P x x' \<Longrightarrow> tr (f x) (f' x'); P x x'; flatf_lfp B' = f'\<rbrakk>
       \<Longrightarrow> tr (B f x) (B' f' x')"
    shows "tr (flatf_lfp B x) (flatf_lfp B' x')"
    apply (rule flatf_fixp_transfer[where tr=tr and fp'="flatf_lfp B'" and P=P])
    apply (fact|rule flatf_ord.fixp_unfold[OF MONO'])+
    done

  lemma flatf_gfp_transfer:
    \<comment> \<open>Transfer rule for greatest fixed points\<close>
    fixes B::"(_ \<Rightarrow> 'a::order_top) \<Rightarrow> _"
    assumes TR_TOP[simp]: "\<And>x. tr x top"
    assumes MONO: "flatf_mono_ge B"
    assumes MONO': "flatf_mono_ge B'"
    assumes R0: "P x x'"
    assumes RS: "\<And>f f' x x'.
       \<lbrakk>\<And>x x'. P x x' \<Longrightarrow> tr (f x) (f' x'); P x x'; flatf_gfp B = f\<rbrakk>
       \<Longrightarrow> tr (B f x) (B' f' x')"
    shows "tr (flatf_gfp B x) (flatf_gfp B' x')"
    apply (rule flatf_fixp_transfer[where 
        tr="\<lambda>x y. tr y x" and fp'="flatf_gfp B" and P="\<lambda>x y. P y x"])
    apply (fact|assumption|rule flatf_ord.fixp_unfold[OF MONO] RS)+
    done

  lemma meta_le_everything_if_top: "(m=top) \<Longrightarrow> (\<And>x. x \<le> (m::'a::order_top))"
    by auto

  lemmas flatf_lfp_refine = flatf_lfp_transfer[
    where tr = "\<lambda>a b. a \<le> cf b" for cf, OF bot_least]
  lemmas flatf_gfp_refine = flatf_gfp_transfer[
    where tr = "\<lambda>a b. a \<le> cf b" for cf, OF meta_le_everything_if_top]


  lemma flat_ge_sup_mono[refine_mono]: "\<And>a a'::'a::complete_lattice. 
    flat_ge a a' \<Longrightarrow> flat_ge b b' \<Longrightarrow> flat_ge (sup a b) (sup a' b')"
    by (auto simp: flat_ord_def)
  
  declare sup_mono[refine_mono]


end

