section \<open>Setup for Foreach Combinator\<close>
theory Sepref_Foreach
imports Sepref_HOL_Bindings "Lib/Pf_Add" "HOL-Library.Rewrite"
begin

subsection "Foreach Loops"

subsubsection "Monadic Version of Foreach"

text \<open>
  In a first step, we define a version of foreach where the continuation condition
  is also monadic, and show that it is equal to the standard version for
  continuation conditions of the form \<open>\<lambda>x. RETURN (c x)\<close>
\<close>

definition "FOREACH_inv xs \<Phi> s \<equiv> 
  case s of (it, \<sigma>) \<Rightarrow> \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>"

definition "monadic_FOREACH R \<Phi> S c f \<sigma>0 \<equiv> do {
  ASSERT (finite S);
  xs0 \<leftarrow> it_to_sorted_list R S;
  (_,\<sigma>) \<leftarrow> RECT (\<lambda>W (xs,\<sigma>). do {
    ASSERT (FOREACH_inv xs0 \<Phi> (xs,\<sigma>));
    if xs\<noteq>[] then do {
      b \<leftarrow> c \<sigma>;
      if b then
        FOREACH_body f (xs,\<sigma>) \<bind> W
      else
        RETURN (xs,\<sigma>)
    } else RETURN (xs,\<sigma>)
  }) (xs0,\<sigma>0);
  RETURN \<sigma>
}"

lemma FOREACH_oci_to_monadic:
  "FOREACHoci R \<Phi> S c f \<sigma>0 = monadic_FOREACH R \<Phi> S (\<lambda>\<sigma>. RETURN (c \<sigma>)) f \<sigma>0"
  unfolding FOREACHoci_def monadic_FOREACH_def WHILEIT_def WHILEI_body_def
  unfolding it_to_sorted_list_def FOREACH_cond_def FOREACH_inv_def
  apply simp
  apply (fo_rule arg_cong[THEN cong] | rule refl ext)+
  apply (simp split: prod.split)
  apply (rule refl)+
  done


text \<open>Next, we define a characterization w.r.t. \<open>nfoldli\<close>\<close>
definition "monadic_nfoldli l c f s \<equiv> RECT (\<lambda>D (l,s). case l of 
    [] \<Rightarrow> RETURN s
  | x#ls \<Rightarrow> do {
      b \<leftarrow> c s;
      if b then do { s'\<leftarrow>f x s; D (ls,s')} else RETURN s
    }
  ) (l,s)"

lemma monadic_nfoldli_eq:
  "monadic_nfoldli l c f s = (
    case l of 
      [] \<Rightarrow> RETURN s 
    | x#ls \<Rightarrow> do {
        b\<leftarrow>c s; 
        if b then f x s \<bind> monadic_nfoldli ls c f else RETURN s
      }
  )"
  apply (subst monadic_nfoldli_def)
  apply (subst RECT_unfold)
  apply (tagged_solver)
  apply (subst monadic_nfoldli_def[symmetric])
  apply simp
  done
  
lemma monadic_nfoldli_simp[simp]:
  "monadic_nfoldli [] c f s = RETURN s"
  "monadic_nfoldli (x#ls) c f s = do {
    b\<leftarrow>c s;
    if b then f x s \<bind> monadic_nfoldli ls c f else RETURN s
  }"
  apply (subst monadic_nfoldli_eq, simp)
  apply (subst monadic_nfoldli_eq, simp)
  done

lemma nfoldli_to_monadic:
  "nfoldli l c f = monadic_nfoldli l (\<lambda>x. RETURN (c x)) f"
  apply (induct l)
  apply auto
  done

definition "nfoldli_alt l c f s \<equiv> RECT (\<lambda>D (l,s). case l of 
    [] \<Rightarrow> RETURN s
  | x#ls \<Rightarrow> do {
      let b = c s;
      if b then do { s'\<leftarrow>f x s; D (ls,s')} else RETURN s
    }
  ) (l,s)"

lemma nfoldli_alt_eq:
  "nfoldli_alt l c f s = (
    case l of 
      [] \<Rightarrow> RETURN s 
    | x#ls \<Rightarrow> do {let b=c s; if b then f x s \<bind> nfoldli_alt ls c f else RETURN s}
  )"
  apply (subst nfoldli_alt_def)
  apply (subst RECT_unfold)
  apply (tagged_solver)
  apply (subst nfoldli_alt_def[symmetric])
  apply simp
  done
  
lemma nfoldli_alt_simp[simp]:
  "nfoldli_alt [] c f s = RETURN s"
  "nfoldli_alt (x#ls) c f s = do {
    let b = c s;
    if b then f x s \<bind> nfoldli_alt ls c f else RETURN s
  }"
  apply (subst nfoldli_alt_eq, simp)
  apply (subst nfoldli_alt_eq, simp)
  done


lemma nfoldli_alt:
  "(nfoldli::'a list \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b \<Rightarrow> 'b nres)
  = nfoldli_alt"
proof (intro ext)
  fix l::"'a list" and c::"'b \<Rightarrow> bool" and f::"'a \<Rightarrow> 'b \<Rightarrow> 'b nres" and s :: 'b
  have "nfoldli l c f = nfoldli_alt l c f"
    by (induct l) auto
  thus "nfoldli l c f s = nfoldli_alt l c f s" by simp
qed

lemma monadic_nfoldli_rec:
  "monadic_nfoldli x' c f \<sigma>
          \<le>\<Down>Id (REC\<^sub>T
             (\<lambda>W (xs, \<sigma>).
                 ASSERT (FOREACH_inv xs0 I (xs, \<sigma>)) \<bind>
                 (\<lambda>_. if xs = [] then RETURN (xs, \<sigma>)
                      else c \<sigma> \<bind>
                           (\<lambda>b. if b then FOREACH_body f (xs, \<sigma>) \<bind> W
                                else RETURN (xs, \<sigma>))))
             (x', \<sigma>) \<bind>
            (\<lambda>(_, y). RETURN y))"
  apply (induct x' arbitrary: \<sigma>)

  apply (subst RECT_unfold, refine_mono)
  apply (simp)
  apply (rule le_ASSERTI)
  apply simp

  apply (subst RECT_unfold, refine_mono)
  apply (subst monadic_nfoldli_simp)
  apply (simp del: conc_Id cong: if_cong)
  apply refine_rcg
  apply simp
  apply (clarsimp simp add: FOREACH_body_def)
  apply (rule_tac R="br (Pair x') (\<lambda>_. True)" in intro_prgR)
  apply (simp add: pw_le_iff refine_pw_simps br_def)

  apply (rule order_trans)
  apply rprems
  apply (simp add: br_def)
  done

lemma monadic_nfoldli_arities[sepref_monadify_arity]:
  "monadic_nfoldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (monadic_nfoldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma monadic_nfoldli_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (monadic_nfoldli)$s$c$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (monadic_nfoldli)$s$c$f$\<sigma>
    ))"
  by (simp_all)

lemma list_rel_congD: 
  assumes A: "(li,l)\<in>\<langle>S\<rangle>list_rel" 
  shows "(li,l)\<in>\<langle>S\<inter>(set li\<times>set l)\<rangle>list_rel"
proof -
  {
    fix Si0 S0
    assume "set li \<subseteq> Si0" "set l \<subseteq> S0"
    with A have "(li,l)\<in>\<langle>S\<inter>(Si0\<times>S0)\<rangle>list_rel"
      by (induction rule: list_rel_induct) auto  
  } from this[OF order_refl order_refl] show ?thesis .
qed      
    
lemma monadic_nfoldli_refine[refine]:
  assumes L: "(li, l) \<in> \<langle>S\<rangle>list_rel"
    and  [simp]: "(si, s) \<in> R"
    and CR[refine]: "\<And>si s. (si,s)\<in>R \<Longrightarrow> ci si \<le>\<Down>bool_rel (c s)"
    and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; x\<in>set l; (si,s)\<in>R; inres (c s) True \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  shows "monadic_nfoldli li ci fi si \<le> \<Down> R (monadic_nfoldli l c f s)"
    
  supply RELATESI[of "S\<inter>(set li\<times>set l)", refine_dref_RELATES]
  supply RELATESI[of R, refine_dref_RELATES]
  unfolding monadic_nfoldli_def  
  apply (refine_rcg bind_refine')
  apply refine_dref_type  
  apply (vc_solve simp: list_rel_congD[OF L]) 
  done
    
    
lemma monadic_FOREACH_itsl:
  fixes R I tsl
  shows 
    "do { l \<leftarrow> it_to_sorted_list R s; monadic_nfoldli l c f \<sigma> } 
     \<le> monadic_FOREACH R I s c f \<sigma>"
    apply (rule refine_IdD)
    unfolding monadic_FOREACH_def it_to_sorted_list_def
    apply (refine_rcg)
    apply simp
    apply (rule monadic_nfoldli_rec[simplified])
    done

lemma FOREACHoci_itsl:
  fixes R I tsl
  shows 
    "do { l \<leftarrow> it_to_sorted_list R s; nfoldli l c f \<sigma> } 
     \<le> FOREACHoci R I s c f \<sigma>"
    apply (rule refine_IdD)
    unfolding FOREACHoci_def it_to_sorted_list_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done

lemma [def_pat_rules]:
  "FOREACHc \<equiv> PR_CONST (FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True))"
  "FOREACHci$I \<equiv> PR_CONST (FOREACHoci (\<lambda>_ _. True) I)"
  "FOREACHi$I \<equiv> \<lambda>\<^sub>2s. PR_CONST (FOREACHoci (\<lambda>_ _. True) I)$s$(\<lambda>\<^sub>2x. True)"
  "FOREACH \<equiv> FOREACHi$(\<lambda>\<^sub>2_ _. True)"
  by (simp_all add: 
    FOREACHci_def FOREACHi_def[abs_def] FOREACHc_def FOREACH_def[abs_def])
  
term "FOREACHoci R I"
lemma id_FOREACHoci[id_rules]: "PR_CONST (FOREACHoci R I) ::\<^sub>i 
  TYPE('c set \<Rightarrow> ('d \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> 'd nres) \<Rightarrow> 'd \<Rightarrow> 'd nres)"
  by simp

text \<open>We set up the monadify-phase such that all FOREACH-loops get
  rewritten to the monadic version of FOREACH\<close>
lemma FOREACH_arities[sepref_monadify_arity]:
  (*"FOREACHc \<equiv> FOREACHoci$(\<lambda>\<^sub>2_ _. True)$(\<lambda>\<^sub>2_ _. True)"
  "FOREACHci \<equiv> FOREACHoci$(\<lambda>\<^sub>2_ _. True)"
  "FOREACHi \<equiv> \<lambda>\<^sub>2I s. FOREACHci$I$s$(\<lambda>\<^sub>2x. True)"
  "FOREACH \<equiv> FOREACHi$(\<lambda>\<^sub>2_ _. True)"*)
  "PR_CONST (FOREACHoci R I) \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (PR_CONST (FOREACHoci R I))$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma FOREACHoci_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (PR_CONST (FOREACHoci R I))$s$(\<lambda>\<^sub>2x. c x)$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (PR_CONST (monadic_FOREACH R I))$s$(\<lambda>\<^sub>2x. (EVAL$(c x)))$f$\<sigma>
    ))"
  by (simp_all add: FOREACH_oci_to_monadic)

subsubsection "Imperative Version of nfoldli"
text \<open>We define an imperative version of \<open>nfoldli\<close>. It is the
  equivalent to the monadic version in the nres-monad\<close>

definition "imp_nfoldli l c f s \<equiv> heap.fixp_fun (\<lambda>D (l,s). case l of 
    [] \<Rightarrow> return s
  | x#ls \<Rightarrow> do {
      b\<leftarrow>c s;
      if b then do { s'\<leftarrow>f x s; D (ls,s')} else return s
    }
  ) (l,s)"

declare imp_nfoldli_def[code del]

lemma imp_nfoldli_simps[simp,code]:
  "imp_nfoldli [] c f s = return s"
  "imp_nfoldli (x#ls) c f s = (do {
    b \<leftarrow> c s;
    if b then do { 
      s'\<leftarrow>f x s; 
      imp_nfoldli ls c f s'
    } else return s
  })"
  apply -
  unfolding imp_nfoldli_def
  apply (subst heap.mono_body_fixp)
  apply pf_mono
  apply simp
  apply (subst heap.mono_body_fixp)
  apply pf_mono
  apply simp
  done



lemma monadic_nfoldli_refine_aux:
  assumes c_ref: "\<And>s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s) 
    (c s) 
    (\<Gamma> * hn_ctxt Rs s' s) 
    bool_assn
    (c' s')"
  assumes f_ref: "\<And>x x' s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rl x' x * hn_ctxt Rs s' s)
    (f x s)
    (\<Gamma> * hn_invalid Rl x' x * hn_invalid Rs s' s) Rs
    (f' x' s')"

  shows "hn_refine 
    (\<Gamma> * hn_ctxt (list_assn Rl) l' l * hn_ctxt Rs s' s) 
    (imp_nfoldli l c f s) 
    (\<Gamma> * hn_invalid (list_assn Rl) l' l * hn_invalid Rs s' s) Rs
    (monadic_nfoldli l' c' f' s')"
  applyF (induct p\<equiv>Rl l' l 
    arbitrary: s s'
    rule: list_assn.induct)

    applyF simp
    apply (rule hn_refine_cons_post)
    apply (rule hn_refine_frame[OF hnr_RETURN_pass])
    apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    apply (simp add: hn_ctxt_def ent_true_drop invalid_assn_const)
    solved

    apply1 weaken_hnr_post
    apply1 (simp only: imp_nfoldli_simps monadic_nfoldli_simp)
    applyF (rule hnr_bind)
      apply1 (rule hn_refine_frame[OF c_ref])
      applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)

      applyF (rule hnr_If)
        applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
        applyF (rule hnr_bind)
          apply1 (rule hn_refine_frame[OF f_ref])
          apply1 (simp add: assn_assoc)
          
          apply1 (rule ent_imp_entt)
          apply1 (fr_rot 1, rule fr_refl)
          apply1 (fr_rot 2, rule fr_refl)
          apply1 (fr_rot 1, rule fr_refl)
          applyS (rule ent_refl)

          applyF (rule hn_refine_frame)
            applyS rprems

            apply1 (simp add: assn_assoc)
            apply1 (rule ent_imp_entt)
            apply (rule fr_refl)
            apply1 (fr_rot 3, rule fr_refl)
            apply1 (fr_rot 3, rule fr_refl)
            applyS (rule ent_refl)
          solved  
  
          apply simp

          applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
        solved  

        apply1 (rule hn_refine_frame[OF hnr_RETURN_pass])
        applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)

        apply1 (simp add: assn_assoc)
        applyS (tactic \<open>Sepref_Frame.merge_tac (K (K no_tac)) @{context} 1\<close>)
      solved  

      apply (rule enttI)
      apply (fr_rot_rhs 1)
      apply (fr_rot 3, rule fr_refl)
      applyS (fr_rot 3, rule ent_star_mono[rotated]; sep_auto simp: hn_ctxt_def)
    solved  
    
    applyS (simp add: hn_ctxt_def invalid_assn_def)

    applyS (rule, sep_auto)
  solved  
  done


lemma hn_monadic_nfoldli:
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt (list_assn Rl) l' l * hn_ctxt Rs s' s"
  assumes c_ref: "\<And>s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s) 
    (c s) 
    (\<Gamma> * hn_ctxt Rs s' s)
    bool_assn 
    (c'$s')"
  assumes f_ref: "\<And>x x' s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rl x' x * hn_ctxt Rs s' s)
    (f x s)
    (\<Gamma> * hn_invalid Rl x' x * hn_invalid Rs s' s) Rs
    (f'$x'$s')"
  shows "hn_refine 
    P 
    (imp_nfoldli l c f s) 
    (\<Gamma> * hn_invalid (list_assn Rl) l' l * hn_invalid Rs s' s)
    Rs
    (monadic_nfoldli$l'$c'$f'$s')
    "
  apply (rule hn_refine_cons_pre[OF FR])
  unfolding APP_def
  apply (rule monadic_nfoldli_refine_aux)
  apply (rule c_ref[unfolded APP_def])
  apply (rule f_ref[unfolded APP_def])
  done  

definition 
  imp_foreach :: "('b \<Rightarrow> 'c list Heap) \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> ('c \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap"
  where
    "imp_foreach tsl s c f \<sigma> \<equiv> do { l \<leftarrow> tsl s; imp_nfoldli l c f \<sigma>}"

lemma heap_fixp_mono[partial_function_mono]:
  assumes [partial_function_mono]: 
    "\<And>x d. mono_Heap (\<lambda>xa. B x xa d)"
    "\<And>Z xa. mono_Heap (\<lambda>a. B a Z xa)" 
  shows "mono_Heap (\<lambda>x. heap.fixp_fun (\<lambda>D \<sigma>. B x D \<sigma>) \<sigma>)"
  apply rule
  apply (rule ccpo.fixp_mono[OF heap.ccpo, THEN fun_ordD])
  apply (rule mono_fun_fun_cnv, erule thin_rl, pf_mono)+
  apply (rule fun_ordI)
  apply (erule monotoneD[of "fun_ord Heap_ord" Heap_ord, rotated])
  apply pf_mono
  done

lemma imp_nfoldli_mono[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>x \<sigma>. mono_Heap (\<lambda>fa. f fa x \<sigma>)"
  shows "mono_Heap (\<lambda>x. imp_nfoldli l c (f x) \<sigma>)"
  unfolding imp_nfoldli_def
  by pf_mono

lemma imp_foreach_mono[partial_function_mono]:
  assumes [partial_function_mono]: "\<And>x \<sigma>. mono_Heap (\<lambda>fa. f fa x \<sigma>)"
  shows "mono_Heap (\<lambda>x. imp_foreach tsl l c (f x) \<sigma>)"
  unfolding imp_foreach_def
  by pf_mono

(* Inline foreach and nfoldli as fixed-points *)
lemmas [sepref_opt_simps] = imp_foreach_def (*imp_nfoldli_def*)

definition  
  "IS_TO_SORTED_LIST \<Omega> Rs Rk tsl \<equiv> (tsl,it_to_sorted_list \<Omega>) \<in> (Rs)\<^sup>k \<rightarrow>\<^sub>a list_assn Rk"

lemma IS_TO_SORTED_LISTI:
  assumes "(tsl,PR_CONST (it_to_sorted_list \<Omega>)) \<in> (Rs)\<^sup>k \<rightarrow>\<^sub>a list_assn Rk"
  shows "IS_TO_SORTED_LIST \<Omega> Rs Rk tsl"
  using assms unfolding IS_TO_SORTED_LIST_def PR_CONST_def .

lemma hn_monadic_FOREACH[sepref_comb_rules]:
  assumes "INDEP Rk" "INDEP Rs" "INDEP R\<sigma>"
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s * hn_ctxt R\<sigma> \<sigma>' \<sigma>"
  assumes STL: "GEN_ALGO tsl (IS_TO_SORTED_LIST ordR Rs Rk)"
  assumes c_ref: "\<And>\<sigma> \<sigma>'. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s * hn_ctxt R\<sigma> \<sigma>' \<sigma>) 
    (c \<sigma>) 
    (\<Gamma>c \<sigma>' \<sigma>) 
    bool_assn 
    (c' \<sigma>')"
  assumes C_FR: 
    "\<And>\<sigma>' \<sigma>. TERM monadic_FOREACH \<Longrightarrow> 
      \<Gamma>c \<sigma>' \<sigma> \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt Rs s' s * hn_ctxt R\<sigma> \<sigma>' \<sigma>"

  assumes f_ref: "\<And>x' x \<sigma>' \<sigma>. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s * hn_ctxt Rk x' x * hn_ctxt R\<sigma> \<sigma>' \<sigma>)
    (f x \<sigma>)
    (\<Gamma>f x' x \<sigma>' \<sigma>) R\<sigma>
    (f' x' \<sigma>')"
  assumes F_FR: "\<And>x' x \<sigma>' \<sigma>. TERM monadic_FOREACH \<Longrightarrow> \<Gamma>f x' x \<sigma>' \<sigma> \<Longrightarrow>\<^sub>t 
    \<Gamma> * hn_ctxt Rs s' s * hn_ctxt Pfx x' x * hn_ctxt Pf\<sigma> \<sigma>' \<sigma>"

  shows "hn_refine 
    P 
    (imp_foreach tsl s c f \<sigma>) 
    (\<Gamma> * hn_ctxt Rs s' s * hn_invalid R\<sigma> \<sigma>' \<sigma>)
    R\<sigma>
    ((PR_CONST (monadic_FOREACH ordR I))
      $s'$(\<lambda>\<^sub>2\<sigma>'. c' \<sigma>')$(\<lambda>\<^sub>2x' \<sigma>'. f' x' \<sigma>')$\<sigma>'
    )"
proof -
  from STL have STL: "(tsl,it_to_sorted_list ordR) \<in> (Rs)\<^sup>k \<rightarrow>\<^sub>a list_assn Rk"
    unfolding GEN_ALGO_def IS_TO_SORTED_LIST_def by simp

  show ?thesis
    apply (rule hn_refine_cons_pre[OF FR])
    apply weaken_hnr_post
    unfolding APP_def PROTECT2_def PR_CONST_def imp_foreach_def
    apply (rule hn_refine_ref[OF monadic_FOREACH_itsl])
    apply (rule hn_refine_guessI)
    apply (rule hnr_bind)
    apply (rule hn_refine_frame)
    apply (rule STL[to_hnr, unfolded APP_def])
    apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    apply (rule hn_monadic_nfoldli[unfolded APP_def])
    apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    apply (rule hn_refine_cons_post)
    apply (rule c_ref[unfolded APP_def])
    apply (rule C_FR)
    apply (rule TERMI)
    apply weaken_hnr_post
    apply (rule hn_refine_cons_post)
    apply (rule f_ref[unfolded APP_def])
    apply (rule entt_trans[OF F_FR])
    apply (rule TERMI)
    applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)

    apply simp
    done

qed

lemma monadic_nfoldli_assert_aux:
  assumes "set l \<subseteq> S"
  shows "monadic_nfoldli l c (\<lambda>x s. ASSERT (x\<in>S)\<then>f x s) s = monadic_nfoldli l c f s"
  using assms
  apply (induction l arbitrary: s)
  apply (auto simp: pw_eq_iff refine_pw_simps)
  done
  
lemmas monadic_nfoldli_assert = monadic_nfoldli_assert_aux[OF order_refl]



(* Refinement Setup for nfoldli  *)
lemma nfoldli_arities[sepref_monadify_arity]:
  "nfoldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (nfoldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma nfoldli_comb[sepref_monadify_comb]:
  "\<And>s c f \<sigma>. (nfoldli)$s$(\<lambda>\<^sub>2x. c x)$f$\<sigma> \<equiv> 
    Refine_Basic.bind$(EVAL$s)$(\<lambda>\<^sub>2s. Refine_Basic.bind$(EVAL$\<sigma>)$(\<lambda>\<^sub>2\<sigma>. 
      SP (monadic_nfoldli)$s$(\<lambda>\<^sub>2x. (EVAL$(c x)))$f$\<sigma>
    ))"
  by (simp_all add: nfoldli_to_monadic)


lemma monadic_nfoldli_refine_aux':
  assumes SS: "set l' \<subseteq> S"
  assumes c_ref: "\<And>s s'. hn_refine 
    (\<Gamma> * hn_ctxt Rs s' s) 
    (c s) 
    (\<Gamma> * hn_ctxt Rs s' s) 
    bool_assn
    (c' s')"
  assumes f_ref: "\<And>x x' s s'. \<lbrakk>x' \<in> S\<rbrakk> \<Longrightarrow> hn_refine 
    (\<Gamma> * hn_ctxt Rl x' x * hn_ctxt Rs s' s)
    (f x s)
    (\<Gamma> * hn_ctxt Rl' x' x * hn_invalid Rs s' s) Rs
    (f' x' s')"

  assumes merge[sepref_frame_merge_rules]: "\<And>x x'. hn_ctxt Rl' x' x \<or>\<^sub>A hn_ctxt Rl x' x \<Longrightarrow>\<^sub>t hn_ctxt Rl'' x' x"
  notes [sepref_frame_merge_rules] = merge_sat2[OF merge]

  shows "hn_refine 
    (\<Gamma> * hn_ctxt (list_assn Rl) l' l * hn_ctxt Rs s' s) 
    (imp_nfoldli l c f s) 
    (\<Gamma> * hn_ctxt (list_assn Rl'') l' l * hn_invalid Rs s' s) Rs
    (monadic_nfoldli l' c' f' s')"


  apply1 (subst monadic_nfoldli_assert_aux[OF SS,symmetric])  

  applyF (induct p\<equiv>Rl l' l 
    arbitrary: s s'
    rule: list_assn.induct)

  applyF simp
  apply (rule hn_refine_cons_post)
  apply (rule hn_refine_frame[OF hnr_RETURN_pass])
  apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
  apply (simp add: hn_ctxt_def ent_true_drop)
  solved

  apply (simp only: imp_nfoldli_simps monadic_nfoldli_simp)
  apply (rule hnr_bind)
  apply (rule hn_refine_frame[OF c_ref])
  apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)

  apply (rule hnr_If)
  apply (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
  apply (simp only: nres_monad_laws)
  apply (rule hnr_ASSERT)
  apply (rule hnr_bind)
  apply (rule hn_refine_frame[OF f_ref])
  apply assumption
  apply (simp add: assn_aci)
  apply (rule ent_imp_entt)
  apply (fr_rot_rhs 1)
  apply (fr_rot 2)
  apply (rule fr_refl)
  apply (rule fr_refl)
  apply (rule fr_refl)
  apply (rule ent_refl)

  applyF (rule hn_refine_frame)
    applyS rprems

    focus
      apply (simp add: assn_aci)
      apply (rule ent_imp_entt)
    
      apply (fr_rot_rhs 1, rule fr_refl)
      apply (fr_rot 2, rule fr_refl)
      apply (fr_rot 1, rule fr_refl)
      apply (rule ent_refl)
    solved
  solved  

  focus (simp add: assn_assoc)
    apply (rule ent_imp_entt)
    apply (rule fr_refl)
    apply (rule ent_refl)
  solved  

  apply1 (rule hn_refine_frame[OF hnr_RETURN_pass])
  applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)

  apply1 (simp add: assn_assoc)
  applyS (tactic \<open>Sepref_Frame.merge_tac (K (K no_tac)) @{context} 1\<close>)

  apply simp
  apply (rule ent_imp_entt)
  apply solve_entails
  apply (rule, sep_auto)
  apply (rule, sep_auto)
  solved
  done

lemma hn_monadic_nfoldli_rl'[sepref_comb_rules]:
  assumes "INDEP Rk" "INDEP R\<sigma>"
  assumes FR: "P \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt (list_assn Rk) s' s * hn_ctxt R\<sigma> \<sigma>' \<sigma>"
  assumes c_ref: "\<And>\<sigma> \<sigma>'. hn_refine 
    (\<Gamma> * hn_ctxt R\<sigma> \<sigma>' \<sigma>) 
    (c \<sigma>) 
    (\<Gamma>c \<sigma>' \<sigma>) 
    bool_assn 
    (c' \<sigma>')"
  assumes C_FR: 
    "\<And>\<sigma>' \<sigma>. TERM monadic_nfoldli \<Longrightarrow> 
      \<Gamma>c \<sigma>' \<sigma> \<Longrightarrow>\<^sub>t \<Gamma> * hn_ctxt R\<sigma> \<sigma>' \<sigma>"

  assumes f_ref: "\<And>x' x \<sigma>' \<sigma>. \<lbrakk>x'\<in>set s'\<rbrakk> \<Longrightarrow> hn_refine 
    (\<Gamma> * hn_ctxt Rk x' x * hn_ctxt R\<sigma> \<sigma>' \<sigma>)
    (f x \<sigma>)
    (\<Gamma>f x' x \<sigma>' \<sigma>) R\<sigma>
    (f' x' \<sigma>')"
  assumes F_FR: "\<And>x' x \<sigma>' \<sigma>. TERM monadic_nfoldli \<Longrightarrow> \<Gamma>f x' x \<sigma>' \<sigma> \<Longrightarrow>\<^sub>t 
    \<Gamma> * hn_ctxt Rk' x' x * hn_ctxt Pf\<sigma> \<sigma>' \<sigma>"

  assumes MERGE: "\<And>x x'. hn_ctxt Rk' x' x \<or>\<^sub>A hn_ctxt Rk x' x \<Longrightarrow>\<^sub>t hn_ctxt Rk'' x' x"  

  shows "hn_refine 
    P 
    (imp_nfoldli s c f \<sigma>) 
    (\<Gamma> * hn_ctxt (list_assn Rk'') s' s * hn_invalid R\<sigma> \<sigma>' \<sigma>)
    R\<sigma>
    ((monadic_nfoldli)
      $s'$(\<lambda>\<^sub>2\<sigma>'. c' \<sigma>')$(\<lambda>\<^sub>2x' \<sigma>'. f' x' \<sigma>')$\<sigma>'
    )"
  unfolding APP_def PROTECT2_def PR_CONST_def
  apply1 (rule hn_refine_cons_pre[OF FR])
  apply1 weaken_hnr_post
  applyF (rule hn_refine_cons[rotated])
    applyF (rule monadic_nfoldli_refine_aux'[OF order_refl])
      focus
        apply (rule hn_refine_cons_post)
        applyS (rule c_ref)
        apply1 (rule entt_trans[OF C_FR[OF TERMI]])
        applyS (rule entt_refl)
      solved  

      apply1 weaken_hnr_post
      applyF (rule hn_refine_cons_post)
        applyS (rule f_ref; simp)

        apply1 (rule entt_trans[OF F_FR[OF TERMI]])
        applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
      solved

      apply (rule MERGE)
    solved  

    applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
    applyS (tactic \<open>Sepref_Frame.frame_tac (K (K no_tac)) @{context} 1\<close>)
  solved  
  done

lemma nfoldli_assert:
  assumes "set l \<subseteq> S"
  shows "nfoldli l c (\<lambda> x s. ASSERT (x \<in> S) \<then> f x s) s = nfoldli l c f s"
  using assms by (induction l arbitrary: s) (auto simp: pw_eq_iff refine_pw_simps)

lemmas nfoldli_assert' = nfoldli_assert[OF order.refl]

lemma fold_eq_nfoldli:
  "RETURN (fold f l s) = nfoldli l (\<lambda>_. True) (\<lambda>x s. RETURN (f x s)) s"
  apply (induction l arbitrary: s) apply (auto) done

lemma fold_eq_nfoldli_assert:
  "RETURN (fold f l s) = nfoldli l (\<lambda>_. True) (\<lambda>x s. ASSERT (x\<in>set l) \<then> RETURN (f x s)) s"
  by (simp add: nfoldli_assert' fold_eq_nfoldli)

lemma fold_arity[sepref_monadify_arity]: "fold \<equiv> \<lambda>\<^sub>2f l s. SP fold$(\<lambda>\<^sub>2x s. f$x$s)$l$s" by auto

lemma monadify_plain_fold[sepref_monadify_comb]: 
  "EVAL$(fold$(\<lambda>\<^sub>2x s. f x s)$l$s) \<equiv> (\<bind>)$(EVAL$l)$(\<lambda>\<^sub>2l. (\<bind>)$(EVAL$s)$(\<lambda>\<^sub>2s. nfoldli$l$(\<lambda>\<^sub>2_. True)$(\<lambda>\<^sub>2x s. EVAL$(f x s))$s))"
  by (simp add: fold_eq_nfoldli)


lemma monadify_plain_fold_old_rl: 
  "EVAL$(fold$(\<lambda>\<^sub>2x s. f x s)$l$s) \<equiv> (\<bind>)$(EVAL$l)$(\<lambda>\<^sub>2l. (\<bind>)$(EVAL$s)$(\<lambda>\<^sub>2s. nfoldli$l$(\<lambda>\<^sub>2_. True)$(\<lambda>\<^sub>2x s. PR_CONST (op_ASSERT_bind (x\<in>set l))$(EVAL$(f x s)))$s))"
  by (simp add: fold_eq_nfoldli_assert)

text \<open>foldli\<close>

lemma foldli_eq_nfoldli:
  "RETURN (foldli l c f s) = nfoldli l c (\<lambda>x s. RETURN (f x s)) s"
by (induction l arbitrary: s) auto

lemma foldli_arities[sepref_monadify_arity]:
  "foldli \<equiv> \<lambda>\<^sub>2s c f \<sigma>. SP (foldli)$s$(\<lambda>\<^sub>2x. c$x)$(\<lambda>\<^sub>2x \<sigma>. f$x$\<sigma>)$\<sigma>"
  by (simp_all)

lemma monadify_plain_foldli[sepref_monadify_comb]: 
  "EVAL$(foldli$l$c$(\<lambda>\<^sub>2x s. f x s)$s) \<equiv>
    (\<bind>)$(EVAL$l)$
     (\<lambda>\<^sub>2l. (\<bind>)$(EVAL$s)$
      (\<lambda>\<^sub>2s. nfoldli$l$c$(\<lambda>\<^sub>2x s. (EVAL$(f x s)))$s))"
by (simp add: foldli_eq_nfoldli)

subsubsection \<open>Deforestation\<close>
lemma nfoldli_filter_deforestation: 
  "nfoldli (filter P xs) c f s = nfoldli xs c (\<lambda>x s. if P x then f x s else RETURN s) s"
  apply (induction xs arbitrary: s)
  by (auto simp: pw_eq_iff refine_pw_simps) 
    
lemma extend_list_of_filtered_set:
  assumes [simp, intro!]: "finite S" 
    and A: "distinct xs'" "set xs' = {x \<in> S. P x}"
  obtains xs where "xs' = filter P xs" "distinct xs" "set xs = S"
proof -
  obtain xs2 where "{x\<in>S. \<not>P x} = set xs2" "distinct xs2"
    using finite_distinct_list[where A="{x\<in>S. \<not>P x}"] by auto
  with A have "xs' = filter P (xs'@xs2)" "distinct (xs'@xs2)" "set (xs'@xs2) = S"  
    by (auto simp: filter_empty_conv)
  from that[OF this] show ?thesis .
qed    

    
lemma FOREACHc_filter_deforestation:
  assumes FIN[simp, intro!]: "finite S"
  shows "(FOREACHc {x\<in>S. P x} c f s) 
    = FOREACHc S c (\<lambda>x s. if P x then f x s else RETURN s) s"
  unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH LIST_FOREACH'_eq
      LIST_FOREACH'_def it_to_sorted_list_def
  subgoal       
  proof (induction rule: antisym[consumes 0, case_names 1 2])
    case 1
    then show ?case
      apply (rule le_ASSERTI)  
      apply (rule ASSERT_leI, simp)  
      apply (rule intro_spec_refine[where R=Id, simplified]; clarsimp)
      apply (rule extend_list_of_filtered_set[OF FIN _ sym], assumption, assumption)
      subgoal for xs' xs
        apply (rule rhs_step_bind_SPEC[where R=Id and x'="xs", simplified])
        applyS simp  
        applyS (simp add: nfoldli_filter_deforestation)
        done
      done
  next
    case 2
    then show ?case
    apply (rule le_ASSERTI)  
    apply (rule ASSERT_leI, (simp; fail))  
    apply (rule intro_spec_refine[where R=Id, simplified]; clarsimp)
    subgoal for xs  
      apply (rule rhs_step_bind_SPEC[where R=Id and x'="filter P xs", simplified])
      apply simp  
      apply (simp add: nfoldli_filter_deforestation)
      done
    done  
  qed
  done    

lemma FOREACHc_filter_deforestation2:
  assumes [simp]: "distinct xs"
  shows "(FOREACHc (set (filter P xs)) c f s) 
    = FOREACHc (set xs) c (\<lambda>x s. if P x then f x s else RETURN s) s"
  using FOREACHc_filter_deforestation[of "set xs", simplified, folded set_filter]
  .  
  
  
  
subsection \<open>For Loops\<close>

partial_function (heap) imp_for :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for i u c f s = (if i \<ge> u then return s else do {ctn <- c s; if ctn then f i s \<bind> imp_for (i + 1) u c f else return s})"

declare imp_for.simps[code]

lemma [simp]:
  "i \<ge> u \<Longrightarrow> imp_for i u c f s = return s"
  "i < u \<Longrightarrow> imp_for i u c f s = do {ctn <- c s; if ctn then f i s \<bind> imp_for (i + 1) u c f else return s}"
by (auto simp: imp_for.simps)

lemma imp_nfoldli_deforest[sepref_opt_simps]:
  "imp_nfoldli [l..<u] c = imp_for l u c"
 apply (intro ext)
 subgoal for f s
  apply (induction "u - l" arbitrary: l u s)
  apply (simp add: upt_conv_Cons; fail)
  apply (simp add: upt_conv_Cons)
  apply (fo_rule arg_cong)
 by (auto cong: if_cong)
done

partial_function (heap) imp_for' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for' i u f s = (if i \<ge> u then return s else f i s \<bind> imp_for' (i + 1) u f)"

declare imp_for'.simps[code]

lemma [simp]:
  "i \<ge> u \<Longrightarrow> imp_for' i u f s = return s"
  "i < u \<Longrightarrow> imp_for' i u f s = f i s \<bind> imp_for' (i + 1) u f"
by (auto simp: imp_for'.simps)

lemma imp_for_imp_for'[sepref_opt_simps]:
  "imp_for i u (\<lambda> _. return True) = imp_for' i u"
apply (intro ext)
subgoal for f s
  apply (induction "u - i" arbitrary: i u s)
  apply (simp; fail)
  apply simp
  apply (fo_rule arg_cong)
  by auto
done

partial_function (heap) imp_for_down :: "nat \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> bool Heap) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for_down l i c f s = do {
    let i = i - 1;
    ctn \<leftarrow> c s;
    if ctn then do {
      s \<leftarrow> f i s;
      if i>l then imp_for_down l i c f s else return s
    } else return s
  }"  

declare imp_for_down.simps[code]

lemma imp_nfoldli_deforest_down[sepref_opt_simps]:
  "imp_nfoldli (rev [l..<u]) c = 
    (\<lambda>f s. if u\<le>l then return s else imp_for_down l u c f s)"
proof (intro ext)
  fix f s
  show "imp_nfoldli (rev [l..<u]) c f s =
          (if l \<ge> u then return s else imp_for_down l u c f s)"
  proof cases
    assume "l\<ge>u" thus ?thesis by auto
  next
    assume "\<not>(l\<ge>u)" hence "l<u" by auto
    thus ?thesis 
      apply simp
    proof (induction "u - l" arbitrary: u s)
      case 0 thus ?case by auto
    next
      case (Suc u')
        from Suc.prems Suc.hyps(2) have [simp]: "rev [l..<u] = (u-1)#rev [l..<u-1]"
          apply simp
          apply (subst upt_Suc_append[symmetric])
          apply auto
          done
        show ?case using Suc.hyps(1)[of "u-1"] Suc.hyps(2) Suc.prems
          apply (subst imp_for_down.simps)
          apply (cases "l < u - Suc 0")
          apply (auto simp: Let_def cong: if_cong)
          done
      qed    
    qed  
  qed            

context begin

private fun imp_for_down_induction_scheme :: "nat \<Rightarrow> nat \<Rightarrow> unit" where
  "imp_for_down_induction_scheme l i = (
    let i=i-1 in 
    if i>l then 
      imp_for_down_induction_scheme l i
    else ()  
  )"

partial_function (heap) imp_for_down' :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'a Heap) \<Rightarrow> 'a \<Rightarrow> 'a Heap" where
  "imp_for_down' l i f s = do {
    let i = i - 1;
    s \<leftarrow> f i s;
    if i>l then imp_for_down' l i f s else return s
  }"  
declare imp_for_down'.simps[code]

lemma imp_for_down_no_cond[sepref_opt_simps]:
  "imp_for_down l u (\<lambda>_. return True) = imp_for_down' l u"
  apply (induction l u rule: imp_for_down_induction_scheme.induct)
  apply (intro ext)
  apply (subst imp_for_down.simps)
  apply (subst imp_for_down'.simps)
  apply (simp cong: if_cong)
  done
  
end

(* TODO: Move. Add rule for imp_for! *)    
lemma imp_for'_rule:
  assumes LESS: "l\<le>u"
  assumes PRE: "P \<Longrightarrow>\<^sub>A I l s"
  assumes STEP: "\<And>i s. \<lbrakk> l\<le>i; i<u \<rbrakk> \<Longrightarrow> <I i s> f i s <I (i+1)>"
  shows "<P> imp_for' l u f s <I u>"
  apply (rule Hoare_Triple.cons_pre_rule[OF PRE])  
  using LESS 
proof (induction arbitrary: s rule: inc_induct)  
  case base thus ?case by sep_auto  
next
  case (step k)
  show ?case using step.hyps 
    by (sep_auto heap: STEP step.IH)  
qed 
  
  
text \<open>This lemma is used to manually convert a fold to a loop over indices. \<close>
lemma fold_idx_conv: "fold f l s = fold (\<lambda>i. f (l!i)) [0..<length l] s"
proof (induction l arbitrary: s rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x l) 
  { fix x s
    have "fold (\<lambda>a. f ((l @ [x]) ! a)) [0..<length l] s = fold (\<lambda>a. f (l ! a)) [0..<length l] s"
      by (rule fold_cong) (simp_all add: nth_append)
  } 
  with snoc show ?case by simp
qed    


end

