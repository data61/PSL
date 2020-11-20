section \<open>\isaheader{Fold-Combinator}\<close>
theory Refine_Fold
imports Collections.Refine_Dflt_Only_ICF
begin
  text \<open>
    In this theory, we explore the usage of the partial-function package, and
    define a function with a higher-order argument. As example, we choose a
    nondeterministic fold-operation on lists.
\<close>

  text \<open>
    Note that the function @{const nfoldli}, which is included in the 
    refinement framework by default, is similar to this function.
    Also, the parametricity based proof technique used there should
    be prefered to this example.
\<close>

  partial_function (nrec) rfoldl where
    "rfoldl f s l = (case l of 
        [] \<Rightarrow> RETURN s 
      | x#ls \<Rightarrow> do { s\<leftarrow>f s x; rfoldl f s ls}
    )"

  text \<open>Currently, we have to manually state the standard simplification 
    lemmas:\<close>
  lemma rfoldl_simps[simp]: 
    "rfoldl f s [] = RETURN s"
    "rfoldl f s (x#ls) = do { s\<leftarrow>f s x; rfoldl f s ls}"
    apply (subst rfoldl.simps, simp)+
    done

  lemma rfoldl_refines[refine]:
    assumes REFF: "\<And>x x' s s'. \<lbrakk> (s,s')\<in>Rs; (x,x')\<in>Rl \<rbrakk> 
      \<Longrightarrow> f s x \<le> \<Down>Rs (f' s' x')"
    assumes REF0: "(s0,s0')\<in>Rs"
    assumes REFL: "(l,l')\<in>\<langle>Rl\<rangle>list_rel"
    shows "rfoldl f s0 l \<le> \<Down>Rs (rfoldl f' s0' l')"
    using REFL[unfolded list_rel_def, simplified] REF0
    apply (induct arbitrary: s0 s0' rule: list_all2_induct)
    apply (simp add: REF0 RETURN_refine)
    apply (simp only: rfoldl_simps)
    apply (refine_rcg)
    apply (rule REFF)
    apply simp_all
    done

  lemma transfer_rfoldl[refine_transfer]:
    assumes "\<And>s x. RETURN (f s x) \<le> F s x"
    shows "RETURN (foldl f s l) \<le> rfoldl F s l"
    using assms
    apply (induct l arbitrary: s)
    apply simp
    apply (simp only: foldl_Nil foldl_append rfoldl_simps)
    apply simp
    apply (rule order_trans[rotated])
    apply (rule refine_transfer)
    apply assumption
    apply assumption
    apply simp
    done

  subsection \<open>Example\<close>
  text \<open>
    As example application, we define a program that takes as input a list
    of non-empty sets of natural numbers, picks some number of each list,
    and adds up the picked numbers.
\<close>
  definition "pick_sum (s0::nat) l \<equiv>
    rfoldl (\<lambda>s x. do {
      ASSERT (x\<noteq>{});
      y\<leftarrow>SPEC (\<lambda>y. y\<in>x);
      RETURN (s+y)
    }) s0 l
    "

  lemma [simp]: 
    "pick_sum s [] = RETURN s"
    "pick_sum s (x#l) = do {
      ASSERT (x\<noteq>{}); y\<leftarrow>SPEC (\<lambda>y. y\<in>x); pick_sum (s+y) l
    }"
    unfolding pick_sum_def
    apply simp_all
    done

  lemma foldl_mono:
    assumes "\<And>x. mono (\<lambda>s. f s x)"
    shows "mono (\<lambda>s. foldl f s l)"
    apply (rule monoI)
    using assms
    apply (induct l)
    apply (auto dest: monoD)
    done

  lemma pick_sum_correct:
    assumes NE: "{}\<notin>set l"  
    assumes FIN: "\<forall>x\<in>set l. finite x"
    shows "pick_sum s0 l \<le> SPEC (\<lambda>s. s \<le> foldl (\<lambda>s x. s+Max x) s0 l)"
    using NE FIN
    apply (induction l arbitrary: s0)
    apply (simp)
    apply (simp)
    apply (intro refine_vcg)
    apply blast
    apply simp
    apply (rule order_trans)
    apply assumption
    apply (rule SPEC_rule)
    apply (erule order_trans)
    apply (rule monoD[OF foldl_mono])
    apply (auto intro: monoI)
    done

  definition "pick_sum_impl s0 l \<equiv>
    rfoldl (\<lambda>s x. do {
      y\<leftarrow>RETURN (the (ls.sel x (\<lambda>_. True)));
      RETURN (s+y)
    }) (s0::nat) l"
    
  lemma pick_sum_impl_refine:
    assumes A: "(l,l')\<in>\<langle>br ls.\<alpha> ls.invar\<rangle>list_rel"
    shows "pick_sum_impl s0 l \<le> \<Down>Id (pick_sum s0 l')"
    unfolding pick_sum_def pick_sum_impl_def
    using A
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (simp_all add: refine_hsimp refine_rel_defs)
    done

  schematic_goal pick_sum_code_aux: "RETURN ?f \<le> pick_sum_impl s0 l"
    unfolding pick_sum_impl_def
    apply refine_transfer
    done

  concrete_definition pick_sum_code for ?s0.0 l uses pick_sum_code_aux

  lemma pick_sum_code_refines: 
    "RETURN (pick_sum_code s l) \<le> pick_sum_impl s l"
    by (rule pick_sum_code.refine)

  value 
    "pick_sum_code 0 [list_to_ls [3,2,1], list_to_ls [1,2,3], list_to_ls[2,1]]"

end

