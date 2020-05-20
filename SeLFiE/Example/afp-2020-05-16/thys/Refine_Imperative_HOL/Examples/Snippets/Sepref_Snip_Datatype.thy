section \<open>Non-Recursive Algebraic Datatype\<close>
theory Sepref_Snip_Datatype
imports "../../IICF/IICF"
begin
  text \<open>We define a non-recursive datatype\<close>
  datatype 'a enum = E1 'a | E2 'a | E3 | E4 'a 'a | E5 bool 'a

  subsection \<open>Refinement Assertion\<close>
  fun enum_assn where
    "enum_assn A (E1 x) (E1 x') = A x x'"
  | "enum_assn A (E2 x) (E2 x') = A x x'"
  | "enum_assn A (E3) (E3) = emp"
  | "enum_assn A (E4 x y) (E4 x' y') = A x x' * A y y'"
  | "enum_assn A (E5 x y) (E5 x' y') = bool_assn x x' * A y y'"
  | "enum_assn _ _ _ = false"

  text \<open>You might want to prove some properties\<close>

  text \<open>A pure-rule is required to enable recovering of invalidated data that was not stored on the heap\<close>
  lemma enum_assn_pure[safe_constraint_rules]: "is_pure A \<Longrightarrow> is_pure (enum_assn A)"
    apply (auto simp: is_pure_iff_pure_assn)
    apply (rename_tac x x')
    apply (case_tac x; case_tac x'; simp add: pure_def)
    done

  text \<open>An identitiy rule is required to easily prove trivial refinement theorems\<close>    
  lemma enum_assn_id[simp]: "enum_assn id_assn = id_assn"
    apply (intro ext)
    subgoal for x y by (cases x; cases y; simp add: pure_def)
    done

  text \<open>Structural rules. \<close>  

  text \<open>Without congruence condition\<close>
  lemma enum_match_nocong: "\<lbrakk>\<And>x y. hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y\<rbrakk> \<Longrightarrow> hn_ctxt (enum_assn A) e e' \<Longrightarrow>\<^sub>t hn_ctxt (enum_assn A') e e'"
    by (cases e; cases e'; simp add: hn_ctxt_def entt_star_mono)

  lemma enum_merge_nocong:
    assumes "\<And>x y. hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>A hn_ctxt Am x y"
    shows "hn_ctxt (enum_assn A) e e' \<or>\<^sub>A hn_ctxt (enum_assn A') e e' \<Longrightarrow>\<^sub>A hn_ctxt (enum_assn Am) e e'"
    using assms
    by (cases e; cases e'; simp add: hn_ctxt_def ent_disj_star_mono)
    
    
  text \<open>With congruence condition\<close>  
  lemma enum_match_cong[sepref_frame_match_rules]: 
    "\<lbrakk>\<And>x y. \<lbrakk>x\<in>set_enum e; y\<in>set_enum e'\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<Longrightarrow>\<^sub>t hn_ctxt A' x y\<rbrakk> \<Longrightarrow> hn_ctxt (enum_assn A) e e' \<Longrightarrow>\<^sub>t hn_ctxt (enum_assn A') e e'"
    by (cases e; cases e'; simp add: hn_ctxt_def entt_star_mono)
      

  lemma enum_merge_cong[sepref_frame_merge_rules]:
    assumes "\<And>x y. \<lbrakk>x\<in>set_enum e; y\<in>set_enum e'\<rbrakk> \<Longrightarrow> hn_ctxt A x y \<or>\<^sub>A hn_ctxt A' x y \<Longrightarrow>\<^sub>t hn_ctxt Am x y"
    shows "hn_ctxt (enum_assn A) e e' \<or>\<^sub>A hn_ctxt (enum_assn A') e e' \<Longrightarrow>\<^sub>t hn_ctxt (enum_assn Am) e e'"
    apply (blast intro: entt_disjE enum_match_cong entt_disjD1[OF assms] entt_disjD2[OF assms])
    done

  text \<open>Propagating invalid\<close>  
  lemma entt_invalid_enum: "hn_invalid (enum_assn A) e e' \<Longrightarrow>\<^sub>t hn_ctxt (enum_assn (invalid_assn A)) e e'"
    apply (simp add: hn_ctxt_def invalid_assn_def[abs_def])
    apply (rule enttI)
    apply clarsimp
    apply (cases e; cases e'; auto simp: mod_star_conv pure_def) 
    done

  lemmas invalid_enum_merge[sepref_frame_merge_rules] = gen_merge_cons[OF entt_invalid_enum]


  subsection \<open>Constructors\<close>  
  text \<open>Constructors need to be registered\<close>
  sepref_register E1 E2 E3 E4 E5  
  
  text \<open>Refinement rules can be proven straightforwardly on the separation logic level (method @{method sepref_to_hoare})\<close>
  lemma [sepref_fr_rules]: "(return o E1,RETURN o E1) \<in> A\<^sup>d \<rightarrow>\<^sub>a enum_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(return o E2,RETURN o E2) \<in> A\<^sup>d \<rightarrow>\<^sub>a enum_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry0 (return E3),uncurry0 (RETURN E3)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a enum_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo E4),uncurry (RETURN oo E4)) \<in> A\<^sup>d*\<^sub>aA\<^sup>d \<rightarrow>\<^sub>a enum_assn A"
    by sepref_to_hoare sep_auto
  lemma [sepref_fr_rules]: "(uncurry (return oo E5),uncurry (RETURN oo E5)) \<in> bool_assn\<^sup>k*\<^sub>aA\<^sup>d \<rightarrow>\<^sub>a enum_assn A"
    by sepref_to_hoare (sep_auto simp: pure_def)

  subsection \<open>Destructor\<close>  
  text \<open>There is currently no automation for destructors, so all the registration boilerplate 
    needs to be done manually\<close>

  text \<open>Set ups operation identification heuristics\<close>
  sepref_register case_enum 

  text \<open>In the monadify phase, this eta-expands to make visible all required arguments\<close>
  lemma [sepref_monadify_arity]: "case_enum \<equiv> \<lambda>\<^sub>2f1 f2 f3 f4 f5 x. SP case_enum$(\<lambda>\<^sub>2x. f1$x)$(\<lambda>\<^sub>2x. f2$x)$f3$(\<lambda>\<^sub>2x y. f4$x$y)$(\<lambda>\<^sub>2x y. f5$x$y)$x"
    by simp

  text \<open>This determines an evaluation order for the first-order operands\<close>  
  lemma [sepref_monadify_comb]: "case_enum$f1$f2$f3$f4$f5$x \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_enum$f1$f2$f3$f4$f5$x)" by simp

  text \<open>This enables translation of the case-distinction in a non-monadic context.\<close>  
  lemma [sepref_monadify_comb]: "EVAL$(case_enum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$f3$(\<lambda>\<^sub>2x y. f4 x y)$(\<lambda>\<^sub>2x y. f5 x y)$x) 
    \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_enum$(\<lambda>\<^sub>2x. EVAL $ f1 x)$(\<lambda>\<^sub>2x. EVAL $ f2 x)$(EVAL $ f3)$(\<lambda>\<^sub>2x y. EVAL $ f4 x y)$(\<lambda>\<^sub>2x y. EVAL $ f5 x y)$x)"
    apply (rule eq_reflection)
    by (simp split: enum.splits)

  text \<open>Auxiliary lemma, to lift simp-rule over \<open>hn_ctxt\<close>\<close>  
  lemma enum_assn_ctxt: "enum_assn A x y = z \<Longrightarrow> hn_ctxt (enum_assn A) x y = z"
    by (simp add: hn_ctxt_def)

  text \<open>The cases lemma first extracts the refinement for the datatype from the precondition.
    Next, it generate proof obligations to refine the functions for every case. 
    Finally the postconditions of the refinement are merged. 

    Note that we handle the
    destructed values separately, to allow reconstruction of the original datatype after the case-expression.

    Moreover, we provide (invalidated) versions of the original compound value to the cases,
    which allows access to pure compound values from inside the case.
    \<close>  
  lemma enum_cases_hnr:
    fixes A e e'
    defines [simp]: "INVe \<equiv> hn_invalid (enum_assn A) e e'"
    assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (enum_assn A) e e' * F"
    assumes E1: "\<And>x1 x1a. \<lbrakk>e = E1 x1; e' = E1 x1a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x1 x1a * INVe * F) (f1' x1a) (hn_ctxt A1' x1 x1a * hn_ctxt XX1 e e' * \<Gamma>1') R (f1 x1)"
    assumes E2: "\<And>x2 x2a. \<lbrakk>e = E2 x2; e' = E2 x2a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x2 x2a * INVe * F) (f2' x2a) (hn_ctxt A2' x2 x2a * hn_ctxt XX2 e e' * \<Gamma>2') R (f2 x2)"
    assumes E3: "\<lbrakk>e = E3; e' = E3\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt (enum_assn A) e e' * F) f3' (hn_ctxt XX3 e e' * \<Gamma>3') R f3"
    assumes E4: "\<And>x41 x42 x41a x42a.
       \<lbrakk>e = E4 x41 x42; e' = E4 x41a x42a\<rbrakk>
       \<Longrightarrow> hn_refine (hn_ctxt A x41 x41a * hn_ctxt A x42 x42a * INVe * F) (f4' x41a x42a) (hn_ctxt A4a' x41 x41a * hn_ctxt A4b' x42 x42a * hn_ctxt XX4 e e' * \<Gamma>4') R
            (f4 x41 x42)"
    assumes E5: "\<And>x51 x52 x51a x52a.
       \<lbrakk>e = E5 x51 x52; e' = E5 x51a x52a\<rbrakk>
       \<Longrightarrow> hn_refine (hn_ctxt bool_assn x51 x51a * hn_ctxt A x52 x52a * INVe * F) (f5' x51a x52a)
            (hn_ctxt bool_assn x51 x51a * hn_ctxt A5' x52 x52a * hn_ctxt XX5 e e' * \<Gamma>5') R (f5 x51 x52)"
    assumes MERGE1[unfolded hn_ctxt_def]: "\<And>x x'. hn_ctxt A1' x x' \<or>\<^sub>A hn_ctxt A2' x x' \<or>\<^sub>A hn_ctxt A3' x x' \<or>\<^sub>A hn_ctxt A4a' x x' \<or>\<^sub>A hn_ctxt A4b' x x' \<or>\<^sub>A hn_ctxt A5' x x' \<Longrightarrow>\<^sub>t hn_ctxt A' x x'"
    assumes MERGE2[unfolded hn_ctxt_def]: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<or>\<^sub>A \<Gamma>3' \<or>\<^sub>A \<Gamma>4' \<or>\<^sub>A \<Gamma>5' \<Longrightarrow>\<^sub>t \<Gamma>'"
    shows "hn_refine \<Gamma> (case_enum f1' f2' f3' f4' f5' e') (hn_ctxt (enum_assn A') e e' * \<Gamma>') R (case_enum$(\<lambda>\<^sub>2x. f1 x)$(\<lambda>\<^sub>2x. f2 x)$f3$(\<lambda>\<^sub>2x y. f4 x y)$(\<lambda>\<^sub>2x y. f5 x y)$e)"
    apply (rule hn_refine_cons_pre[OF FR])
    apply1 extract_hnr_invalids
    apply (cases e; cases e'; simp add: enum_assn.simps[THEN enum_assn_ctxt])
    subgoal
      apply (rule hn_refine_cons[OF _ E1 _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def) \<comment> \<open>Match precondition for case, get \<open>enum_assn\<close> from assumption generated by \<open>extract_hnr_invalids\<close>\<close>
      apply (rule entt_star_mono) \<comment> \<open>Split postcondition into pairs for compounds and frame, drop \<open>hn_ctxt XX\<close>\<close>
      apply1 (rule entt_fr_drop)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done
    subgoal 
      apply (rule hn_refine_cons[OF _ E2 _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')
      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done    
    subgoal 
      apply (rule hn_refine_cons[OF _ E3 _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (subst mult.commute, rule entt_fr_drop)
      apply (rule entt_trans[OF _ MERGE2])
      apply (simp add: entt_disjI1' entt_disjI2')
    done  
    subgoal 
      apply (rule hn_refine_cons[OF _ E4 _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done    
    subgoal 
      apply (rule hn_refine_cons[OF _ E5 _ entt_refl]; assumption?)
      applyS (simp add: hn_ctxt_def)
      apply (rule entt_star_mono)
      apply1 (rule entt_fr_drop)
      apply (rule entt_star_mono)

      apply1 (rule ent_imp_entt)
      applyS (simp add: hn_ctxt_def)

      apply1 (rule entt_trans[OF _ MERGE1])
      applyS (simp add: hn_ctxt_def entt_disjI1' entt_disjI2')

      apply1 (rule entt_trans[OF _ MERGE2])
      applyS (simp add: entt_disjI1' entt_disjI2')
    done    
  done  

  text \<open>After some more preprocessing (adding extra frame-rules for non-atomic postconditions, 
    and splitting the merge-terms into binary merges), this rule can be registered\<close>
  lemmas [sepref_comb_rules] = enum_cases_hnr[sepref_prep_comb_rule]

  subsection \<open>Regression Test\<close>

  definition "test1 (e::bool enum) \<equiv> RETURN e"
  sepref_definition test1_impl is "test1" :: "(enum_assn bool_assn)\<^sup>d \<rightarrow>\<^sub>a enum_assn bool_assn"
    unfolding test1_def[abs_def] by sepref
  sepref_register test1
  lemmas [sepref_fr_rules] = test1_impl.refine

  definition "test \<equiv> do {
    let x = E1 True;

    _ \<leftarrow> case x of
      E1 a \<Rightarrow> RETURN (Some a)  \<comment> \<open>Access and invalidate compound inside case\<close>
    | _ \<Rightarrow> RETURN (Some True);  

    _ \<leftarrow> test1 x; \<comment> \<open>Rely on structure being there, with valid compound\<close>

    \<comment> \<open>Same thing again, with merge\<close>
    _ \<leftarrow> if True then
      case x of
        E1 a \<Rightarrow> RETURN (Some a)  \<comment> \<open>Access and invalidate compound inside case\<close>
      | _ \<Rightarrow> RETURN (Some True)
     else RETURN None; 
    _ \<leftarrow> test1 x; \<comment> \<open>Rely on structure being there, with valid compound\<close>
    
    \<comment> \<open>Now test with non-pure\<close>
    let a = op_array_replicate 4 (3::nat);
    let x = E5 False a;
    
    _ \<leftarrow> case x of
      E1 _ \<Rightarrow> RETURN (0::nat)
    | E2 _ \<Rightarrow> RETURN 1
    | E3 \<Rightarrow> RETURN 0
    | E4 _ _ \<Rightarrow> RETURN 0
    | E5 _ a \<Rightarrow> mop_list_get a 0;

    \<comment> \<open>Rely on that compound still exists (it's components are only read in the case above)\<close>
    case x of
      E1 a \<Rightarrow> do {mop_list_set a 0 0; RETURN (0::nat)}
    | E2 _ \<Rightarrow> RETURN 1
    | E3 \<Rightarrow> RETURN 0
    | E4 _ _ \<Rightarrow> RETURN 0
    | E5 _ _ \<Rightarrow> RETURN 0
  }"

  lemmas [safe_constraint_rules] = CN_FALSEI[of is_pure "invalid_assn A" for A]


  sepref_definition foo is "uncurry0 test" :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
    unfolding test_def
    supply [[goals_limit=1]]
    by sepref

end
