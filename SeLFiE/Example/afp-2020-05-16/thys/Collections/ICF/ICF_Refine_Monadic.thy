section \<open>\isaheader{Refine-Monadci setup for ICF}\<close>
theory ICF_Refine_Monadic
imports ICF_Impl
begin
text \<open>
  This theory sets up some lemmas that automate refinement proofs using
  the Isabelle Collection Framework (ICF).
\<close>

subsection \<open>General Setup\<close>

lemma (in set) drh[refine_dref_RELATES]: 
  "RELATES (build_rel \<alpha> invar)" by (simp add: RELATES_def)
lemma (in map) drh[refine_dref_RELATES]: 
  "RELATES (build_rel \<alpha> invar)" by (simp add: RELATES_def)

lemma (in uprio) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)" 
  by (simp add: RELATES_def)
lemma (in prio) drh[refine_dref_RELATES]: "RELATES (build_rel \<alpha> invar)" 
  by (simp add: RELATES_def)


lemmas (in StdSet) [refine_hsimp] = correct
lemmas (in StdMap) [refine_hsimp] = correct

lemma (in set_sel') pick_ref[refine_hsimp]:
  "\<lbrakk> invar s; \<alpha> s \<noteq> {}\<rbrakk> \<Longrightarrow> the (sel' s (\<lambda>_. True)) \<in> \<alpha> s"
  by (auto elim!: sel'E)

(*text {* Wrapper to prevent higher-order unification problems *}
definition [simp, code_unfold]: "IT_tag x \<equiv> x"

lemma (in set_iteratei) it_is_iterator[refine_transfer]:
  "invar s \<Longrightarrow> set_iterator (IT_tag iteratei s) (\<alpha> s)"
  unfolding IT_tag_def by (rule iteratei_rule)

lemma (in map_iteratei) it_is_iterator[refine_transfer]:
  "invar m \<Longrightarrow> set_iterator (IT_tag iteratei m) (map_to_set (\<alpha> m))"
  unfolding IT_tag_def by (rule iteratei_rule)
*)

text \<open>
  This definition is handy to be used on the abstract level.
\<close>
definition "prio_pop_min q \<equiv> do {
    ASSERT (dom q \<noteq> {});
    SPEC (\<lambda>(e,w,q'). 
      q'=q(e:=None) \<and> 
      q e = Some w \<and> 
      (\<forall> e' w'. q e' = Some w' \<longrightarrow> w\<le>w')
    )
  }"

lemma (in uprio_pop) prio_pop_min_refine[refine]:
  "(q,q')\<in>build_rel \<alpha> invar \<Longrightarrow> RETURN (pop q) 
    \<le> \<Down> (\<langle>Id,\<langle>Id,br \<alpha> invar\<rangle>prod_rel\<rangle>prod_rel) (prio_pop_min q')"
  unfolding prio_pop_min_def
  apply refine_rcg
  apply (clarsimp simp: prod_rel_def br_def)
  apply (erule (1) popE)
  apply (rule pw_leI)
  apply (auto simp: refine_pw_simps intro: ranI)
  done


subsection "Iterators"
lemmas (in poly_map_iteratei) [refine_transfer] = iteratei_correct
lemmas (in poly_map_iterateoi) [refine_transfer] = iterateoi_correct
lemmas (in map_no_invar) [refine_transfer] = invar

lemmas (in poly_set_iteratei) [refine_transfer] = iteratei_correct
lemmas (in poly_set_iterateoi) [refine_transfer] = iterateoi_correct
lemmas (in set_no_invar) [refine_transfer] = invar

lemma (in poly_set_iteratei) dres_ne_bot_iterate[refine_transfer]:
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "iteratei r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  unfolding iteratei_def it_to_list_def it_to_it_def
  apply (rule dres_foldli_ne_bot)
  by (simp_all add: A)
lemma (in poly_set_iterateoi) dres_ne_bot_iterateo[refine_transfer]:
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "iterateoi r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  unfolding iterateoi_def it_to_list_def it_to_it_def
  apply (rule dres_foldli_ne_bot)
  by (simp_all add: A)

lemma (in poly_map_iteratei) dres_ne_bot_map_iterate[refine_transfer]:
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "iteratei r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  unfolding iteratei_def it_to_list_def it_to_it_def
  apply (rule dres_foldli_ne_bot)
  by (simp_all add: A)
lemma (in poly_set_iterateoi) dres_ne_bot_map_iterateo[refine_transfer]:
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "iterateoi r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  unfolding iterateoi_def it_to_list_def it_to_it_def
  apply (rule dres_foldli_ne_bot)
  by (simp_all add: A)





subsection "Alternative FOREACH-transfer"
text \<open>Required for manual refinements\<close>
lemma transfer_FOREACHoci_plain[refine_transfer]:
  assumes A: "set_iterator_genord iterate s ordR"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate c fi \<sigma>) \<le> FOREACHoci ordR I s c f \<sigma>"
proof -
  from A obtain l where [simp]:
    "distinct l" 
    "s = set l" 
    "sorted_wrt ordR l"
    "iterate = foldli l" 
    unfolding set_iterator_genord_def by blast
  
  have "RETURN (foldli l c fi \<sigma>) \<le> nfoldli l c f \<sigma>"
    by (rule nfoldli_transfer_plain[OF R])
  also have "\<dots> = do { l \<leftarrow> RETURN l; nfoldli l c f \<sigma> }" by simp
  also have "\<dots> \<le> FOREACHoci ordR I s c f \<sigma>"
    apply (rule refine_IdD)
    unfolding FOREACHoci_def
    apply refine_rcg
    apply simp
    apply simp
    apply (rule nfoldli_while)
    done
  finally show ?thesis by simp
qed

lemma transfer_FOREACHoi_plain[refine_transfer]:
  assumes A: "set_iterator_genord iterate s ordR"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACHoi ordR I s f \<sigma>"
  using assms unfolding FOREACHoi_def by (rule transfer_FOREACHoci_plain)

lemma transfer_FOREACHci_plain[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate c fi \<sigma>) \<le> FOREACHci I s c f \<sigma>"
  using assms unfolding FOREACHci_def set_iterator_def
  by (rule transfer_FOREACHoci_plain)

lemma transfer_FOREACHi_plain[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACHi I s f \<sigma>"
  using assms unfolding FOREACHi_def
  by (rule transfer_FOREACHci_plain)

lemma transfer_FOREACHc_plain[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate c fi \<sigma>) \<le> FOREACHc s c f \<sigma>"
  using assms unfolding FOREACHc_def
  by (rule transfer_FOREACHci_plain)

lemma transfer_FOREACH_plain[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. RETURN (fi x \<sigma>) \<le> f x \<sigma>"
  shows "RETURN (iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACH s f \<sigma>"
  using assms unfolding FOREACH_def
  by (rule transfer_FOREACHc_plain)

abbreviation "dres_it iterate c (fi::'a \<Rightarrow> 'b \<Rightarrow> 'b dres) \<sigma> \<equiv> 
  iterate (case_dres False False c) (\<lambda>x s. s\<bind>fi x) (dRETURN \<sigma>)"

lemma transfer_FOREACHoci_nres[refine_transfer]:
  assumes A: "set_iterator_genord iterate s ordR"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate c fi \<sigma>) \<le> FOREACHoci ordR I s c f \<sigma>"
proof -
  from A obtain l where [simp]:
    "distinct l" 
    "s = set l" 
    "sorted_wrt ordR l"
    "iterate = foldli l" 
    unfolding set_iterator_genord_def by blast
  
  have "nres_of (dres_it (foldli l) c fi \<sigma>) \<le> nfoldli l c f \<sigma>"
    by (rule nfoldli_transfer_dres[OF R])
  also have "\<dots> = do { l \<leftarrow> RETURN l; nfoldli l c f \<sigma> }" by simp
  also have "\<dots> \<le> FOREACHoci ordR I s c f \<sigma>"
    apply (rule refine_IdD)
    unfolding FOREACHoci_def
    apply refine_rcg
    apply simp
    apply simp
    apply (rule nfoldli_while)
    done
  finally show ?thesis by simp
qed

lemma transfer_FOREACHoi_nres[refine_transfer]:
  assumes A: "set_iterator_genord iterate s ordR"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACHoi ordR I s f \<sigma>"
  using assms unfolding FOREACHoi_def by (rule transfer_FOREACHoci_nres)

lemma transfer_FOREACHci_nres[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate c fi \<sigma>) \<le> FOREACHci I s c f \<sigma>"
  using assms unfolding FOREACHci_def set_iterator_def
  by (rule transfer_FOREACHoci_nres)

lemma transfer_FOREACHi_nres[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACHi I s f \<sigma>"
  using assms unfolding FOREACHi_def
  by (rule transfer_FOREACHci_nres)

lemma transfer_FOREACHc_nres[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate c fi \<sigma>) \<le> FOREACHc s c f \<sigma>"
  using assms unfolding FOREACHc_def
  by (rule transfer_FOREACHci_nres)

lemma transfer_FOREACH_nres[refine_transfer]:
  assumes A: "set_iterator iterate s"
  assumes R: "\<And>x \<sigma>. nres_of (fi x \<sigma>) \<le> f x \<sigma>"
  shows "nres_of (dres_it iterate (\<lambda>_. True) fi \<sigma>) \<le> FOREACH s f \<sigma>"
  using assms unfolding FOREACH_def
  by (rule transfer_FOREACHc_nres)


(*
lemma dres_ne_bot_iterate[refine_transfer]:
  assumes B: "set_iterator (IT_tag it r) S"
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "IT_tag it r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
  apply (rule_tac I="\<lambda>_ s. s\<noteq>dSUCCEED" in set_iterator_rule_P[OF B])
  apply (rule dres_ne_bot_basic A | assumption)+
  done
*)

(*
subsubsection {* Monotonicity for Iterators *}

lemma it_mono_aux:
  assumes COND: "\<And>\<sigma> \<sigma>'. \<sigma>\<le>\<sigma>' \<Longrightarrow> c \<sigma> \<noteq> c \<sigma>' \<Longrightarrow> \<sigma>=bot \<or> \<sigma>'=top "
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes B: "\<sigma>\<le>\<sigma>'"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l c f \<sigma> \<le> foldli l c f' \<sigma>'"
proof -
  { fix l 
    have "foldli l c f bot = bot" by (induct l) (auto simp: STRICT)
  } note [simp] = this
  { fix l 
    have "foldli l c f' top = top" by (induct l) (auto simp: STRICT)
  } note [simp] = this

  show ?thesis
    using B
    apply (induct l arbitrary: \<sigma> \<sigma>')
    apply simp_all
    apply (metis assms foldli_not_cond)
    done
qed


lemma it_mono_aux_dres':
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l (case_dres True True c) f \<sigma> 
    \<le> foldli l (case_dres True True c) f' \<sigma>"
  apply (rule it_mono_aux)
  apply (simp_all split: dres.split_asm add: STRICT A)
  done

lemma it_mono_aux_dres:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "foldli l (case_dres True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> foldli l (case_dres True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
  apply (rule it_mono_aux_dres')
  apply (simp_all)
  apply (rule dbind_mono)
  apply (simp_all add: A)
  done
  
lemma iteratei_mono':
  assumes L: "set_iteratei \<alpha> invar it"
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  assumes I: "invar s"
  shows "IT_tag it s (case_dres True True c) f \<sigma> 
    \<le> IT_tag it s (case_dres True True c) f' \<sigma>"
  proof -
    from set_iteratei.iteratei_rule[OF L, OF I, unfolded set_iterator_foldli_conv]
    obtain l0 where l0_props: "distinct l0" "\<alpha> s = set l0" "it s = foldli l0" by blast
 
    from it_mono_aux_dres' [of f f' l0 c \<sigma>]
    show ?thesis
      unfolding IT_tag_def l0_props(3)
      by (simp add: STRICT A)
  qed

lemma iteratei_mono:
  assumes L: "set_iteratei \<alpha> invar it"
  assumes A: "\<And>a x. f a x \<le> f' a x"
  assumes I: "invar s"
  shows "IT_tag it s (case_dres True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> IT_tag it s (case_dres True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
 proof -
    from set_iteratei.iteratei_rule[OF L, OF I, unfolded set_iterator_foldli_conv]
    obtain l0 where l0_props: "distinct l0" "\<alpha> s = set l0" "it s = foldli l0" by blast
 
    from it_mono_aux_dres [of f f' l0 c \<sigma>]
    show ?thesis
      unfolding IT_tag_def l0_props(3)
      by (simp add: A)
  qed

lemmas [refine_mono] = iteratei_mono[OF ls_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF lsi_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF rs_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ahs_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ias_iteratei_impl]
lemmas [refine_mono] = iteratei_mono[OF ts_iteratei_impl]
*)
(* Do not require the invariant for lsi_iteratei. 

This is kind of a hack -- the real fix comes with the new Collection/Refinement-Framework. *)
(*
lemma dres_ne_bot_iterate_lsi[refine_transfer]:
  fixes s :: "'a"
  assumes A: "\<And>x s. f x s \<noteq> dSUCCEED"
  shows "IT_tag lsi_iteratei r c (\<lambda>x s. dbind s (f x)) (dRETURN s) \<noteq> dSUCCEED"
proof -
  {
    fix l and s :: "'a dres"
    assume "s\<noteq>dSUCCEED" 
    hence "foldli l c (\<lambda>x s. s\<bind>f x) s \<noteq> dSUCCEED"
      apply (induct l arbitrary: s)
      using A
      apply simp_all
      apply (intro impI)
      apply (metis dres_ne_bot_basic)
      done
  } note R=this
  with A show ?thesis
    unfolding lsi_iteratei_def
    by simp
qed


lemma iteratei_mono_lsi[refine_mono]:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "IT_tag lsi_iteratei s (case_dres True True c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> IT_tag lsi_iteratei s (case_dres True True c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
 proof -
    from it_mono_aux_dres [of f f' s c \<sigma>]
    show ?thesis
      unfolding IT_tag_def lsi_iteratei_def
      by (simp add: A)
 qed
*)
end
