section \<open>Utilities for Interface Specifications and Implementations\<close>
theory Sepref_Intf_Util
imports Sepref_Rules Sepref_Translate "Lib/Term_Synth" Sepref_Combinator_Setup
  "Lib/Concl_Pres_Clarification"
keywords "sepref_decl_op" :: thy_goal
     and "sepref_decl_impl" :: thy_goal
begin

subsection \<open>Relation Interface Binding\<close>
  definition INTF_OF_REL :: "('a\<times>'b) set \<Rightarrow> 'c itself \<Rightarrow> bool"
    where [simp]: "INTF_OF_REL R I \<equiv> True"

  lemma intf_of_relI: "INTF_OF_REL (R::(_\<times>'a) set) TYPE('a)" by simp
  declare intf_of_relI[synth_rules] \<comment> \<open>Declare as fallback rule\<close>

  lemma [synth_rules]:
    "INTF_OF_REL unit_rel TYPE(unit)"
    "INTF_OF_REL nat_rel TYPE(nat)"
    "INTF_OF_REL int_rel TYPE(int)"
    "INTF_OF_REL bool_rel TYPE(bool)"

    "INTF_OF_REL R TYPE('a) \<Longrightarrow> INTF_OF_REL (\<langle>R\<rangle>option_rel) TYPE('a option)"
    "INTF_OF_REL R TYPE('a) \<Longrightarrow> INTF_OF_REL (\<langle>R\<rangle>list_rel) TYPE('a list)"
    "INTF_OF_REL R TYPE('a) \<Longrightarrow> INTF_OF_REL (\<langle>R\<rangle>nres_rel) TYPE('a nres)"
    "\<lbrakk>INTF_OF_REL R TYPE('a); INTF_OF_REL S TYPE('b)\<rbrakk> \<Longrightarrow> INTF_OF_REL (R\<times>\<^sub>rS) TYPE('a\<times>'b)"
    "\<lbrakk>INTF_OF_REL R TYPE('a); INTF_OF_REL S TYPE('b)\<rbrakk> \<Longrightarrow> INTF_OF_REL (\<langle>R,S\<rangle>sum_rel) TYPE('a+'b)"
    "\<lbrakk>INTF_OF_REL R TYPE('a); INTF_OF_REL S TYPE('b)\<rbrakk> \<Longrightarrow> INTF_OF_REL (R\<rightarrow>S) TYPE('a\<Rightarrow>'b)"
    by simp_all

  lemma synth_intf_of_relI: "INTF_OF_REL R I \<Longrightarrow> SYNTH_TERM R I" by simp


subsection \<open>Operations with Precondition\<close>
  definition mop :: "('a\<Rightarrow>bool) \<Rightarrow> ('a\<Rightarrow>'b nres) \<Rightarrow> 'a \<Rightarrow> 'b nres"
    \<comment> \<open>Package operation with precondition\<close>
    where [simp]: "mop P f \<equiv> \<lambda>x. ASSERT (P x) \<then> f x"
  
  lemma param_op_mop_iff:
    assumes "(Q,P)\<in>R\<rightarrow>bool_rel"
    shows 
    "(f, g) \<in> [P]\<^sub>f R \<rightarrow> \<langle>S\<rangle>nres_rel
    \<longleftrightarrow> 
    (mop Q f, mop P g) \<in> R \<rightarrow>\<^sub>f \<langle>S\<rangle>nres_rel
    "
    using assms
    by (auto 
      simp: mop_def fref_def pw_nres_rel_iff refine_pw_simps
      dest: fun_relD)

  lemma param_mopI:
    assumes "(f,g) \<in> [P]\<^sub>f R \<rightarrow> \<langle>S\<rangle>nres_rel"  
    assumes "(Q,P) \<in> R \<rightarrow> bool_rel"
    shows "(mop Q f, mop P g) \<in> R \<rightarrow>\<^sub>f \<langle>S\<rangle>nres_rel"
    using assms by (simp add: param_op_mop_iff)

  lemma mop_spec_rl: "P x \<Longrightarrow> mop P f x \<le> f x" by simp

  lemma mop_spec_rl_from_def:  
    assumes "f \<equiv> mop P g"
    assumes "P x"
    assumes "g x \<le> z"
    shows "f x \<le> z"
    using assms mop_spec_rl by simp

  lemma mop_leof_rl_from_def:  
    assumes "f \<equiv> mop P g"
    assumes "P x \<Longrightarrow> g x \<le>\<^sub>n z"
    shows "f x \<le>\<^sub>n z"
    using assms 
    by (simp add: pw_leof_iff refine_pw_simps)


  lemma assert_true_bind_conv: "ASSERT True \<then> m = m" by simp 

  lemmas mop_alt_unfolds = curry_def curry0_def mop_def uncurry_apply uncurry0_apply o_apply assert_true_bind_conv

subsection \<open>Constraints\<close>
lemma add_is_pure_constraint: "\<lbrakk>PROP P; CONSTRAINT is_pure A\<rbrakk> \<Longrightarrow> PROP P" .
lemma sepref_relpropI: "P R = CONSTRAINT P R" by simp

subsubsection \<open>Purity\<close>
lemmas [constraint_simps] = the_pure_pure
definition [constraint_abbrevs]: "IS_PURE P R \<equiv> is_pure R \<and> P (the_pure R)"
lemma IS_PURE_pureI: 
  "P R \<Longrightarrow> IS_PURE P (pure R)"
  by (auto simp: IS_PURE_def)

lemma [fcomp_norm_simps]: "CONSTRAINT (IS_PURE \<Phi>) P \<Longrightarrow> pure (the_pure P) = P" 
  by (simp add: IS_PURE_def)
 
lemma [fcomp_norm_simps]: "CONSTRAINT (IS_PURE P) A \<Longrightarrow> P (the_pure A)"
  by (auto simp: IS_PURE_def)

lemma handle_purity1: 
  "CONSTRAINT (IS_PURE \<Phi>) A \<Longrightarrow> CONSTRAINT \<Phi> (the_pure A)"
  by (auto simp: IS_PURE_def)

lemma handle_purity2:
  "CONSTRAINT (IS_PURE \<Phi>) A \<Longrightarrow> CONSTRAINT is_pure A"
  by (auto simp: IS_PURE_def)




subsection \<open>Composition\<close>
(* TODO/FIXME: Overlaps with FCOMP! *)

  subsubsection \<open>Preconditions\<close>
  definition [simp]: "tcomp_pre Q T P \<equiv> \<lambda>a. Q a \<and> (\<forall>a'. (a', a) \<in> T \<longrightarrow> P a')"
  definition "and_pre P1 P2 \<equiv> \<lambda>x. P1 x \<and> P2 x"
  definition "imp_pre P1 P2 \<equiv> \<lambda>x. P1 x \<longrightarrow> P2 x"

  lemma and_pre_beta: "PP \<longrightarrow> P x \<and> Q x \<Longrightarrow> PP \<longrightarrow> and_pre P Q x" by (auto simp: and_pre_def)
  lemma imp_pre_beta: "PP \<longrightarrow> P x \<longrightarrow> Q x \<Longrightarrow> PP \<longrightarrow> imp_pre P Q x" by (auto simp: imp_pre_def)



  definition "IMP_PRE P1 P2 \<equiv> \<forall>x. P1 x \<longrightarrow> P2 x"
  lemma IMP_PRED: "IMP_PRE P1 P2 \<Longrightarrow> P1 x \<Longrightarrow> P2 x" unfolding IMP_PRE_def by auto
  lemma IMP_PRE_refl: "IMP_PRE P P" unfolding IMP_PRE_def by auto

  definition "IMP_PRE_CUSTOM \<equiv> IMP_PRE"
  lemma IMP_PRE_CUSTOMD: "IMP_PRE_CUSTOM P1 P2 \<Longrightarrow> IMP_PRE P1 P2" by (simp add: IMP_PRE_CUSTOM_def)
  lemma IMP_PRE_CUSTOMI: "\<lbrakk>\<And>x. P1 x \<Longrightarrow> P2 x\<rbrakk> \<Longrightarrow> IMP_PRE_CUSTOM P1 P2" 
    by (simp add: IMP_PRE_CUSTOM_def IMP_PRE_def)


  lemma imp_and_triv_pre: "IMP_PRE P (and_pre (\<lambda>_. True) P)"
    unfolding IMP_PRE_def and_pre_def by auto


subsubsection \<open>Premises\<close>    
  definition "ALL_LIST A \<equiv> (\<forall>x\<in>set A. x)"  
  definition "IMP_LIST A B \<equiv> ALL_LIST A \<longrightarrow> B"

  lemma to_IMP_LISTI:
    "P \<Longrightarrow> IMP_LIST [] P" 
    by (auto simp: IMP_LIST_def)

  lemma to_IMP_LIST: "(P \<Longrightarrow> IMP_LIST Ps Q) \<equiv> Trueprop (IMP_LIST (P#Ps) Q)"
    by (auto simp: IMP_LIST_def ALL_LIST_def intro!: equal_intr_rule)
    
  lemma from_IMP_LIST:
    "Trueprop (IMP_LIST As B) \<equiv> (ALL_LIST As \<Longrightarrow> B)"
    "(ALL_LIST [] \<Longrightarrow> B) \<equiv> Trueprop B"
    "(ALL_LIST (A#As) \<Longrightarrow> B) \<equiv> (A \<Longrightarrow> ALL_LIST As \<Longrightarrow> B)"
    by (auto simp: IMP_LIST_def ALL_LIST_def intro!: equal_intr_rule)
    
  lemma IMP_LIST_trivial: "IMP_LIST A B \<Longrightarrow> IMP_LIST A B" .



subsubsection \<open>Composition Rules\<close>
  lemma hfcomp_tcomp_pre:
    assumes B: "(g,h) \<in> [Q]\<^sub>f T \<rightarrow> \<langle>U\<rangle>nres_rel"
    assumes A: "(f,g) \<in> [P]\<^sub>a RR' \<rightarrow> S"
    shows "(f,h) \<in> [tcomp_pre Q T P]\<^sub>a hrp_comp RR' T \<rightarrow> hr_comp S U"
    using hfcomp[OF A B] by simp

  lemma transform_pre_param:
    assumes A: "IMP_LIST Cns ((f, h) \<in> [tcomp_pre Q T P]\<^sub>a hrp_comp RR' T \<rightarrow> hr_comp S U)"
    assumes P: "IMP_LIST Cns ((P,P') \<in> T \<rightarrow> bool_rel)"
    assumes C: "IMP_PRE PP' (and_pre P' Q)"
    shows "IMP_LIST Cns ((f,h) \<in> [PP']\<^sub>a hrp_comp RR' T \<rightarrow> hr_comp S U)"
    unfolding from_IMP_LIST
    apply (rule hfref_cons) 
    apply (rule A[unfolded from_IMP_LIST])
    apply assumption
    apply (drule IMP_PRED[OF C])
    using P[unfolded from_IMP_LIST] unfolding and_pre_def
    apply (auto dest: fun_relD) []
    by simp_all
 
  lemma hfref_mop_conv: "((g,mop P f) \<in> [Q]\<^sub>a R \<rightarrow> S) \<longleftrightarrow> (g,f) \<in> [\<lambda>x. P x \<and> Q x]\<^sub>a R \<rightarrow> S"
    apply (simp add: hfref_to_ASSERT_conv)
    apply (fo_rule arg_cong fun_cong)+
    by (auto intro!: ext simp: pw_eq_iff refine_pw_simps)
  
  lemma hfref_op_to_mop:
    assumes R: "(impl,f) \<in> [Q]\<^sub>a R \<rightarrow> S"
    assumes DEF: "mf \<equiv> mop P f"
    assumes C: "IMP_PRE PP' (imp_pre P Q)"
    shows "(impl,mf) \<in> [PP']\<^sub>a R \<rightarrow> S"
    unfolding DEF hfref_mop_conv
    apply (rule hfref_cons[OF R])
    using C
    by (auto simp: IMP_PRE_def imp_pre_def)
  
  lemma hfref_mop_to_op:
    assumes R: "(impl,mf) \<in> [Q]\<^sub>a R \<rightarrow> S"
    assumes DEF: "mf \<equiv> mop P f"
    assumes C: "IMP_PRE PP' (and_pre Q P)"
    shows "(impl,f) \<in> [PP']\<^sub>a R \<rightarrow> S"
    using R unfolding DEF hfref_mop_conv 
    apply (rule hfref_cons)
    using C
    apply (auto simp: and_pre_def IMP_PRE_def)
    done

  subsubsection \<open>Precondition Simplification\<close>

  lemma IMP_PRE_eqI:
    assumes "\<And>x. P x \<longrightarrow> Q x"
    assumes "CNV P P'"
    shows "IMP_PRE P' Q"
    using assms by (auto simp: IMP_PRE_def)

  lemma simp_and1:
    assumes "Q \<Longrightarrow> CNV P P'"
    assumes "PP \<longrightarrow> P' \<and> Q"
    shows "PP \<longrightarrow> P \<and> Q"  
    using assms by auto

  lemma simp_and2:
    assumes "P \<Longrightarrow> CNV Q Q'"
    assumes "PP \<longrightarrow> P \<and> Q'"
    shows "PP \<longrightarrow> P \<and> Q"  
    using assms by auto

  lemma triv_and1: "Q \<longrightarrow> True \<and> Q" by blast

  lemma simp_imp:
    assumes "P \<Longrightarrow> CNV Q Q'"
    assumes "PP \<longrightarrow> Q'"
    shows "PP \<longrightarrow> (P \<longrightarrow> Q)"
    using assms by auto

  lemma CNV_split:
    assumes "CNV A A'"
    assumes "CNV B B'"
    shows "CNV (A \<and> B) (A' \<and> B')"  
    using assms by auto

  lemma CNV_prove:
    assumes "P"  
    shows "CNV P True"
    using assms by auto

  lemma simp_pre_final_simp:   
    assumes "CNV P P'"
    shows "P' \<longrightarrow> P"
    using assms by auto

  lemma auto_weaken_pre_uncurry_step':
    assumes "PROTECT f a \<equiv> f'"
    shows "PROTECT (uncurry f) (a,b) \<equiv> f' b" 
    using assms
    by (auto simp: curry_def dest!: meta_eq_to_obj_eq intro!: eq_reflection)


subsection \<open>Protected Constants\<close>
lemma add_PR_CONST_to_def: "x\<equiv>y \<Longrightarrow> PR_CONST x \<equiv> y" by simp

subsection \<open>Rule Collections\<close>
named_theorems_rev sepref_mop_def_thms \<open>Sepref: mop - definition theorems\<close>

named_theorems_rev sepref_fref_thms \<open>Sepref: fref-theorems\<close>

named_theorems sepref_relprops_transform \<open>Sepref: Simp-rules to transform relator properties\<close>
named_theorems sepref_relprops \<open>Sepref: Simp-rules to add CONSTRAINT-tags to relator properties\<close>
named_theorems sepref_relprops_simps \<open>Sepref: Simp-rules to simplify relator properties\<close>

subsubsection \<open>Default Setup\<close>



subsection \<open>ML-Level Declarations\<close>

  ML \<open>
    signature SEPREF_INTF_UTIL = sig
      (* Miscellaneous*)
      val list_filtered_subterms: (term -> 'a option) -> term -> 'a list


      (* Interface types for relations *)
      val get_intf_of_rel: Proof.context -> term -> typ

      (* Constraints *)
      (* Convert relations to pure assertions *)
      val to_assns_rl: bool -> Proof.context -> thm -> thm
      (* Recognize, summarize and simplify CONSTRAINT - premises *)
      val cleanup_constraints: Proof.context -> thm -> thm

      (* Preconditions *)
      (* Simplify precondition. Goal must be in IMP_PRE or IMP_PRE_CUSTOM form. *)
      val simp_precond_tac: Proof.context -> tactic'


      (* Configuration options *)
      val cfg_def: bool Config.T       (* decl_op: Define constant *)
      val cfg_ismop: bool Config.T     (* decl_op: Specified term is mop *)
      val cfg_mop: bool Config.T       (* decl_op, decl_impl: Derive mop *) 
      val cfg_rawgoals: bool Config.T  (* decl_op, decl_impl: Do not pre-process/solve goals *)


      (* TODO: Make do_cmd usable from ML-level! *)

    end

    structure Sepref_Intf_Util: SEPREF_INTF_UTIL = struct
  
      val cfg_debug = 
        Attrib.setup_config_bool @{binding sepref_debug_intf_util} (K false)
      
      val dbg_trace = Sepref_Debugging.dbg_trace_msg cfg_debug  
      val dbg_msg_tac = Sepref_Debugging.dbg_msg_tac cfg_debug  


      fun list_filtered_subterms f t = let
        fun r t = case f t of 
          SOME a => [a]
        | NONE => (
            case t of 
              t1$t2 => r t1 @ r t2
            | Abs (_,_,t) => r t
            | _ => []
          )
      in
        r t
      end
  
      fun get_intf_of_rel ctxt R = 
        Term_Synth.synth_term @{thms synth_intf_of_relI} ctxt R
          |> fastype_of 
          |> Refine_Util.dest_itselfT
  
      local
        fun add_is_pure_constraint ctxt v thm = let
          val v = Thm.cterm_of ctxt v
          val rl = Drule.infer_instantiate' ctxt [NONE, SOME v] @{thm add_is_pure_constraint}
        in
          thm RS rl
        end
      in  
        fun to_assns_rl add_pure_constr ctxt thm = let
          val orig_ctxt = ctxt
      
          val (thm,ctxt) = yield_singleton (apfst snd oo Variable.importT) thm ctxt
      
          val (R,S) = case Thm.concl_of thm of @{mpat "Trueprop (_\<in>fref _ ?R ?S)"} => (R,S)
            | _ => raise THM("to_assns_rl: expected fref-thm",~1,[thm])
      
          fun mk_cn_subst (fname,(iname,C,A)) = 
            let
              val T' = A --> C --> @{typ assn}
              val v' = Free (fname,T')
              val ct' = @{mk_term "the_pure ?v'"} |> Thm.cterm_of ctxt
            in
              (v',(iname,ct'))
            end
      
          fun relation_flt (name,Type (@{type_name set},[Type (@{type_name prod},[C,A])])) = SOME (name,C,A)
            | relation_flt _ = NONE  
      
            
          val vars = []
            |> Term.add_vars R 
            |> Term.add_vars S
            |> map_filter (relation_flt) 
          val (names,ctxt) = Variable.variant_fixes (map (#1 #> fst) vars) ctxt
          
          val cn_substs = map mk_cn_subst (names ~~ vars)
      
      
          val thm = Drule.infer_instantiate ctxt (map snd cn_substs) thm
      
          val thm = thm |> add_pure_constr ? fold (fn (v,_) => fn thm => add_is_pure_constraint ctxt v thm) cn_substs
      
          val thm = singleton (Variable.export ctxt orig_ctxt) thm
        in
          thm
        end
      
        fun cleanup_constraints ctxt thm = let
          val orig_ctxt = ctxt
      
          val (thm, ctxt) = yield_singleton (apfst snd oo Variable.import true) thm ctxt
      
          val xform_thms = Named_Theorems.get ctxt @{named_theorems sepref_relprops_transform}
          val rprops_thms = Named_Theorems.get ctxt @{named_theorems sepref_relprops}
          val simp_thms = Named_Theorems.get ctxt @{named_theorems sepref_relprops_simps}
      
          fun simp thms = Conv.fconv_rule (
                  Simplifier.asm_full_rewrite 
                    (put_simpset HOL_basic_ss ctxt addsimps thms))
      
          (* Check for pure (the_pure R) - patterns *)
      
          local
            val (_,R,S) = case Thm.concl_of thm of
              @{mpat "Trueprop (_\<in>hfref ?P ?R ?S)"} => (P,R,S)
            | @{mpat "Trueprop (_\<in>fref ?P ?R ?S)"} => (P,R,S)
            | _ => raise THM("cleanup_constraints: Expected hfref or fref-theorem",~1,[thm])  
      
      
            fun flt_pat @{mpat "pure (the_pure ?A)"} = SOME A | flt_pat _ = NONE
      
            val purify_terms = 
              (list_filtered_subterms flt_pat R @ list_filtered_subterms flt_pat S)
              |> distinct op aconv
       
            val thm = fold (add_is_pure_constraint ctxt) purify_terms thm
          in
            val thm = thm
          end
      
          val thm = thm
            |> Local_Defs.unfold0 ctxt xform_thms
            |> Local_Defs.unfold0 ctxt rprops_thms
      
          val insts = map (fn 
              @{mpat "Trueprop (CONSTRAINT _ (the_pure _))"} => @{thm handle_purity1}
            | _ => asm_rl  
            ) (Thm.prems_of thm)  
      
          val thm = (thm OF insts)
            |> Conv.fconv_rule Thm.eta_conversion
            |> simp @{thms handle_purity2}
            |> simp simp_thms
      
          val thm = singleton (Variable.export ctxt orig_ctxt) thm  
      
        in
          thm
        end
      end  
  
      fun simp_precond_tac ctxt = let
        fun simp_only thms = asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps thms)
        val rtac = resolve_tac ctxt
    
        val cnv_ss = ctxt delsimps @{thms CNV_def}
    
        (*val uncurry_tac = SELECT_GOAL (ALLGOALS (DETERM o SOLVED' (
          REPEAT' (rtac @{thms auto_weaken_pre_uncurry_step'}) 
          THEN' rtac @{thms auto_weaken_pre_uncurry_finish}
        )))*)
    
        val prove_cnv_tac = SOLVED' (rtac @{thms CNV_prove} THEN' SELECT_GOAL (auto_tac ctxt))
    
        val do_cnv_tac = 
          (cp_clarsimp_tac cnv_ss) THEN_ALL_NEW
          (TRY o REPEAT_ALL_NEW (match_tac ctxt @{thms CNV_split}))
          THEN_ALL_NEW (prove_cnv_tac ORELSE' rtac @{thms CNV_I})
    
        val final_simp_tac = 
          rtac @{thms simp_pre_final_simp} 
          THEN' cp_clarsimp_tac cnv_ss
          THEN' dbg_msg_tac (Sepref_Debugging.msg_subgoal "final_simp_tac: Before CNV_I") ctxt
          THEN' rtac @{thms CNV_I}
          THEN' dbg_msg_tac (Sepref_Debugging.msg_text "Final-Simp done") ctxt
    
        (*val curry_tac = let open Conv in
          CONVERSION (Refine_Util.HOL_concl_conv (fn ctxt => arg1_conv (
            top_conv ( fn _ => try_conv (rewr_conv @{thm uncurry_def})) ctxt)) ctxt)
          THEN' REPEAT' (EqSubst.eqsubst_tac ctxt [1] @{thms case_prod_eta})
          THEN' rtac @{thms CNV_I}
          end*)

        val simp_tupled_pre_tac = 
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms prod_casesK uncurry0_hfref_post})
          THEN' REPEAT' (EqSubst.eqsubst_tac ctxt [1] @{thms case_prod_eta})
          THEN' rtac @{thms CNV_I}

        val unfold_and_tac = rtac @{thms and_pre_beta} THEN_ALL_NEW simp_only @{thms split}
    
        val simp_and1_tac =  
          rtac @{thms simp_and1} THEN' do_cnv_tac
    
        val simp_and2_tac =  
          rtac @{thms simp_and2} THEN' do_cnv_tac
    
        val and_plan_tac =   
          simp_and1_tac 
          THEN' dbg_msg_tac (Sepref_Debugging.msg_subgoal "State after and1") ctxt
          THEN' (
            rtac @{thms triv_and1}
            ORELSE' 
            dbg_msg_tac (Sepref_Debugging.msg_subgoal "Invoking and2 on") ctxt
            THEN' simp_and2_tac 
            THEN' dbg_msg_tac (Sepref_Debugging.msg_subgoal "State before final_simp_tac") ctxt
            THEN' final_simp_tac
          )
    
        val unfold_imp_tac = rtac @{thms imp_pre_beta} THEN_ALL_NEW simp_only @{thms split}
        val simp_imp1_tac =  
          rtac @{thms simp_imp} THEN' do_cnv_tac
    
        val imp_plan_tac = simp_imp1_tac THEN' final_simp_tac 
    
        val imp_pre_tac = APPLY_LIST [
            simp_only @{thms split_tupled_all}
            THEN' Refine_Util.instantiate_tuples_subgoal_tac ctxt
            THEN' CASES' [
              (unfold_and_tac, ALLGOALS and_plan_tac),
              (unfold_imp_tac, ALLGOALS imp_plan_tac)
            ]
          ,
            simp_tupled_pre_tac
          ]  
    
        val imp_pre_custom_tac = 
          SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms and_pre_def}) THEN'
          TRY o SOLVED' (SELECT_GOAL (auto_tac ctxt))
    
      in
        CASES' [
          (rtac @{thms IMP_PRE_eqI}, imp_pre_tac 1),
          (rtac @{thms IMP_PRE_CUSTOMI}, ALLGOALS imp_pre_custom_tac)
        ]
      end




      local
        fun inf_bn_aux name = 
          case String.tokens (fn c => c = #".") name of
            [] => NONE
          | [a] => SOME (Binding.name a)
          | (_::a::_) => SOME (Binding.name a)
      in
        fun infer_basename (Const ("_type_constraint_",_)$t) = infer_basename t
          | infer_basename (Const (name,_)) = inf_bn_aux name
          | infer_basename (Free (name,_)) = inf_bn_aux name
          | infer_basename _ = NONE
      end    
  
      val cfg_mop = Attrib.setup_config_bool @{binding sepref_register_mop} (K true)
      val cfg_ismop = Attrib.setup_config_bool @{binding sepref_register_ismop} (K false)
      val cfg_rawgoals = Attrib.setup_config_bool @{binding sepref_register_rawgoals} (K false)
      val cfg_transfer = Attrib.setup_config_bool @{binding sepref_decl_impl_transfer} (K true)
      val cfg_def = Attrib.setup_config_bool @{binding sepref_register_def} (K true)
      val cfg_register = Attrib.setup_config_bool @{binding sepref_decl_impl_register} (K true)
  
      local 
        open Refine_Util
        val flags = 
             parse_bool_config' "mop" cfg_mop
          || parse_bool_config' "ismop" cfg_ismop
          || parse_bool_config' "rawgoals" cfg_rawgoals
          || parse_bool_config' "def" cfg_def
        val parse_flags = parse_paren_list' flags  

        val parse_name = Scan.option (Parse.binding --| @{keyword ":"})
        val parse_relconds = Scan.optional (@{keyword "where"} |-- Parse.and_list1 (Scan.repeat1 Parse.prop) >> flat) []
      in

        val do_parser = parse_flags -- parse_name -- Parse.term --| @{keyword "::"} -- Parse.term -- parse_relconds
      end  
  
  
      fun do_cmd ((((flags,name),opt_raw), relt_raw),relconds_raw) lthy = let
        local
          val ctxt = Refine_Util.apply_configs flags lthy
        in
          val flag_ismop = Config.get ctxt cfg_ismop
          val flag_mop = Config.get ctxt cfg_mop andalso not flag_ismop
          val flag_rawgoals = Config.get ctxt cfg_rawgoals
          val flag_def = Config.get ctxt cfg_def
        end
  
        open Sepref_Basic Sepref_Rules

        val relt = Syntax.parse_term lthy relt_raw
        val relconds = map (Syntax.parse_prop lthy) relconds_raw 

        val _ = dbg_trace lthy "Parse relation and relation conditions together"
        val relt = Const (@{const_name "Pure.term"}, dummyT) $ relt
        local
          val l = Syntax.check_props lthy (relt::relconds)
        in
          val (relt, relconds) = (hd l, tl l) 
        end
        val relt = Logic.dest_term relt

        val opt_pre = Syntax.parse_term lthy opt_raw
  

        val _ = dbg_trace lthy "Infer basename"
        val name = case name of 
          SOME name => name
        | NONE => (
            case infer_basename opt_pre of 
              NONE => (error "Could not infer basename: You have to specify a basename"; Binding.empty)
            | SOME name => name
          )
          
  
        fun qname s n = Binding.qualify true (Binding.name_of n) (Binding.name s)
        fun def name t_pre attribs lthy = let
          val t = Syntax.check_term lthy t_pre
            (*|> Thm.cterm_of lthy
            |> Drule.mk_term
            |> Local_Defs.unfold0 lthy @{thms PR_CONST_def}
            |> Drule.dest_term
            |> Thm.term_of*)
  
          val (_,lthy) = Local_Theory.open_target lthy 
          val ((dt,(_,thm)),lthy) = Local_Theory.define 
            ((name,Mixfix.NoSyn),((Thm.def_binding name,@{attributes [code]}@attribs),t)) lthy;
          val (lthy, lthy_old) = `Local_Theory.close_target lthy
          val phi = Proof_Context.export_morphism lthy_old lthy
          val thm = Morphism.thm phi thm
          val dt = Morphism.term phi dt
  
        in
          ((dt,thm),lthy)
        end
  
        val _ = dbg_trace lthy "Analyze Relation"
        val (pre,args,res) = analyze_rel relt
        val specified_pre = is_some pre
        val pre = the_default (mk_triv_precond args) pre
  
        val def_thms = @{thms PR_CONST_def}
  
        val _ = dbg_trace lthy "Define op"
        val op_name = Binding.prefix_name (if flag_ismop then "mop_" else "op_") name
        val (def_thms,opc,lthy) = 
          if flag_def then let
              val ((opc,op_def_thm),lthy) = def op_name opt_pre @{attributes [simp]} lthy
              val opc = Refine_Util.dummify_tvars opc
              val def_thms = op_def_thm::def_thms
            in
              (def_thms,opc,lthy)
            end
          else let
              val _ = dbg_trace lthy "Refine type of opt_pre to get opc"
              val opc = Syntax.check_term lthy opt_pre
              val new_ctxt = Variable.declare_term opc lthy
              val opc = singleton (Variable.export_terms new_ctxt lthy) opc
                |> Refine_Util.dummify_tvars
            in 
              (def_thms,opc,lthy)
            end
  
            
        (* PR_CONST Heuristics *)    
        fun pr_const_heuristics basename c_pre lthy = let
          val _ = dbg_trace lthy ("PR_CONST heuristics " ^ @{make_string} c_pre)

          val c = Syntax.check_term lthy c_pre
        in
          case c of
            @{mpat "PR_CONST _"} => ((c_pre,false),lthy)
          | Const _ => ((c_pre,false),lthy)
          | _ => let
              val (f,args) = strip_comb c
  
              val lthy = case f of Const _ => let
                  val ctxt = Variable.declare_term c lthy
                  val lhs = Autoref_Tagging.list_APP (f,args)
                  val rhs = @{mk_term "UNPROTECT ?c"}
                  val goal = Logic.mk_equals (lhs,rhs) |> Thm.cterm_of ctxt
                  val tac = 
                    Local_Defs.unfold0_tac ctxt @{thms APP_def UNPROTECT_def}
                    THEN ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt))
                  val thm = Goal.prove_internal ctxt [] goal (K tac)
                    |> singleton (Variable.export ctxt lthy)
  
                  val (_,lthy) = Local_Theory.note 
                    ((Binding.suffix_name "_def_pat" basename,@{attributes [def_pat_rules]}),[thm]) lthy
  
                  val _ = Thm.pretty_thm lthy thm |> Pretty.string_of |> writeln
                in
                  lthy
                end
              | _ => (
                Pretty.block [
                  Pretty.str "Complex operation pattern. Added PR_CONST but no pattern rules:",
                  Pretty.brk 1,Syntax.pretty_term lthy c]
                |> Pretty.string_of |> warning  
                ; lthy)
  
              val c_pre = Const(@{const_name PR_CONST},dummyT)$c_pre
            in
              ((c_pre,true),lthy)
            end
        end  

        val ((opc,_),lthy) = pr_const_heuristics op_name opc lthy

        (* Register *)
        val arg_intfs = map (get_intf_of_rel lthy) args
        val res_intf = get_intf_of_rel lthy res
  

        fun register basename c lthy = let
          val _ = dbg_trace lthy "Register"
          open Sepref_Basic
          val c = Syntax.check_term lthy c
  
          val ri = case (is_nresT (body_type (fastype_of c)), is_nresT res_intf) of
            (true,false) => mk_nresT res_intf
          | (false,true) => dest_nresT res_intf
          | _ => res_intf
  
          val iT = arg_intfs ---> ri
  
          val ((_,itype_thm),lthy) = Sepref_Combinator_Setup.sepref_register_single (Binding.name_of basename) c iT lthy
          val _ = Thy_Output.pretty_thm lthy itype_thm |> Pretty.string_of |> writeln
  
        in
          lthy
        end
  
        val lthy = register op_name opc lthy
  
        val _ = dbg_trace lthy "Define pre"
        val pre_name = Binding.prefix_name "pre_" name
        val ((prec,pre_def_thm),lthy) = def pre_name pre @{attributes [simp]} lthy
        val prec = Refine_Util.dummify_tvars prec
        val def_thms = pre_def_thm::def_thms
  
        (* Re-integrate pre-constant into type-context of relation. TODO: This is probably not clean/robust *)
        val pre = constrain_type_pre (fastype_of pre) prec |> Syntax.check_term lthy

  
        val _ = dbg_trace lthy "Convert both, relation and operation to uncurried form, and add nres"
        val _ = dbg_trace lthy "Convert relation (arguments have already been separated by analyze-rel)"
        val res = case res of @{mpat "\<langle>_\<rangle>nres_rel"} => res | _ => @{mk_term "\<langle>?res\<rangle>nres_rel"}
        val relt = mk_rel (SOME pre,args,res)
  
        val _ = dbg_trace lthy "Convert operation"
        val opcT = fastype_of (Syntax.check_term lthy opc)
        val op_is_nres = Sepref_Basic.is_nresT (body_type opcT)
        val (opcu, op_ar) = let
          val arity = binder_types #> length
          (* Arity of operation is number of arguments before result (which may be a fun-type! )*)
          val res_ar = arity (Relators.rel_absT res |> not op_is_nres ? dest_nresT)

          val op_ar = arity opcT - res_ar
          
          val _ = op_ar = length args orelse 
            raise TERM("Operation/relation arity mismatch: " ^ string_of_int op_ar ^ " vs " ^ string_of_int (length args),[opc,relt])
  
          (* Add RETURN o...o if necessary*)
          val opc = 
            if op_is_nres then opc
            else mk_compN_pre op_ar (Const(@{const_name Refine_Basic.RETURN},dummyT)) opc
  
          (* Add uncurry if necessary *)  
          val opc = mk_uncurryN_pre op_ar opc
        in 
          (opc, op_ar)
        end
  
        (* Build mop-variant *)
        val declare_mop = (specified_pre orelse not op_is_nres) andalso flag_mop
  
        val (mop_data,lthy) = if declare_mop then let
            val _ = dbg_trace lthy "mop definition"
            val mop_rhs = Const(@{const_name mop},dummyT) $ prec $ opcu
              |> mk_curryN_pre op_ar
            val mop_name = Binding.prefix_name "mop_" name
            val ((mopc,mop_def_thm),lthy) = def mop_name mop_rhs [] lthy
            val mopc = Refine_Util.dummify_tvars mopc
  
            val ((mopc,added_pr_const),lthy) = pr_const_heuristics mop_name mopc lthy

            val mop_def_thm' = if added_pr_const then 
                mop_def_thm RS @{thm add_PR_CONST_to_def}
              else mop_def_thm

            val (_,lthy) = Local_Theory.note ((Binding.empty, @{attributes [sepref_mop_def_thms]}),[mop_def_thm']) lthy

            val _ = dbg_trace lthy "mop alternative definition"
            val alt_unfolds = @{thms mop_alt_unfolds}
              |> not specified_pre ? curry op :: pre_def_thm

            val mop_alt_thm = Local_Defs.unfold0 lthy alt_unfolds mop_def_thm
              |> Refine_Util.shift_lambda_leftN op_ar
            val (_,lthy) = Local_Theory.note ((Binding.suffix_name "_alt" mop_name,@{attributes [simp]}),[mop_alt_thm]) lthy
  
            val _ = dbg_trace lthy "mop: register"
            val lthy = register mop_name mopc lthy
  
            val _ = dbg_trace lthy "mop: vcg theorem"
            local
              val Ts = map Relators.rel_absT args
              val ctxt = Variable.declare_thm mop_def_thm lthy
              val ctxt = fold Variable.declare_typ Ts ctxt
              val (x,ctxt) = Refine_Util.fix_left_tuple_from_Ts "x" Ts ctxt
              
              val mop_def_thm = mop_def_thm
                |> Local_Defs.unfold0 ctxt @{thms curry_shl}
              
              fun prep_thm thm = (thm OF [mop_def_thm])
                |> Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt x)]
                |> Local_Defs.unfold0 ctxt @{thms uncurry_apply uncurry0_apply o_apply}
                |> Local_Defs.unfold0 ctxt (def_thms @
                    @{thms Product_Type.split HOL.True_implies_equals})
                |> singleton (Variable.export ctxt lthy)

              val thms = map prep_thm @{thms mop_spec_rl_from_def mop_leof_rl_from_def}  

            in
              val (_,lthy) = Local_Theory.note ((qname "vcg" mop_name,@{attributes [refine_vcg]}),thms) lthy
            end
  
          in 
            (SOME (mop_name,mopc,mop_def_thm),lthy)
          end
        else (NONE,lthy)
  
  
        val _ = dbg_trace lthy "Build Parametricity Theorem"
        val param_t = mk_pair_in_pre opcu opcu relt 
          |> Syntax.check_term lthy 
          |> HOLogic.mk_Trueprop
          |> curry Logic.list_implies relconds
        
        val _ = dbg_trace lthy "Build Parametricity Theorem for Precondition"
        val param_pre_t = 
          let
            val pre_relt = Relators.mk_fun_rel (Relators.list_prodrel_left args) @{term bool_rel}
  
            val param_pre_t = mk_pair_in_pre prec prec pre_relt 
              |> Syntax.check_term lthy
              |> HOLogic.mk_Trueprop
              |> curry Logic.list_implies relconds
          in
            param_pre_t
          end
        
        
        val _ = dbg_trace lthy "Build goals"
        val goals = [[ (param_t, []), (param_pre_t, []) ]]
  
        fun after_qed [[p_thm, pp_thm]] _ (*ctxt*) = 
          let
            val _ = dbg_trace lthy "after_qed"
            val p_thm' = p_thm |> not specified_pre ? Local_Defs.unfold0 lthy [pre_def_thm]

            val (_,lthy) = Local_Theory.note ((qname "fref" op_name,@{attributes [sepref_fref_thms]}), [p_thm']) lthy
            val (_,lthy) = Local_Theory.note ((qname "param" pre_name,@{attributes [param]}), [pp_thm]) lthy

            val p'_unfolds = pre_def_thm :: @{thms True_implies_equals}
            val (_,lthy) = Local_Theory.note ((qname "fref'" op_name,[]), [Local_Defs.unfold0 lthy p'_unfolds p_thm]) lthy

  
            val lthy = case mop_data of NONE => lthy | 
              SOME (mop_name,mopc,mop_def_thm) => let
                val _ = dbg_trace lthy "Build and prove mop-stuff"
                (* mop - parametricity theorem: (uncurry\<^sup>n mopc,uncurry\<^sup>n mopc) \<in> args \<rightarrow>\<^sub>f res *)
                val mopcu = mk_uncurryN_pre op_ar mopc
                val param_mop_t = mk_pair_in_pre mopcu mopcu (mk_rel (NONE,args,res))
                  |> Syntax.check_term lthy
                  |> HOLogic.mk_Trueprop
                  |> curry Logic.list_implies relconds
  
                val ctxt = Variable.auto_fixes param_mop_t lthy 
                
                val tac = let
                  val p_thm = Local_Defs.unfold0 ctxt @{thms PR_CONST_def} p_thm
                in
                  Local_Defs.unfold0_tac ctxt (mop_def_thm :: @{thms PR_CONST_def uncurry_curry_id uncurry_curry0_id})
                  THEN FIRSTGOAL (
                    dbg_msg_tac (Sepref_Debugging.msg_subgoal "Mop-param thm goal after unfolding") ctxt THEN'
                    resolve_tac ctxt @{thms param_mopI}
                      THEN' SOLVED' (resolve_tac ctxt [p_thm] THEN_ALL_NEW assume_tac ctxt)
                      THEN' SOLVED' (resolve_tac ctxt [pp_thm] THEN_ALL_NEW assume_tac ctxt)
                  )
                end
  
                val pm_thm = Goal.prove_internal lthy [] (Thm.cterm_of ctxt param_mop_t) (K tac)
                  |> singleton (Variable.export ctxt lthy)
  
                val (_,lthy) = Local_Theory.note ((qname "fref" mop_name,@{attributes [sepref_fref_thms]}), [pm_thm]) lthy
                val (_,lthy) = Local_Theory.note ((qname "fref'" mop_name,[]), [Local_Defs.unfold0 lthy p'_unfolds pm_thm]) lthy
  
  
              in
                lthy
              end
  
  
          in
            lthy
          end
          | after_qed thmss _ = raise THM ("After-qed: Wrong thmss structure",~1,flat thmss)    
          
        fun std_tac ctxt = let
          val ptac = REPEAT_ALL_NEW_FWD (Parametricity.net_tac (Parametricity.get_dflt ctxt) ctxt)
  
          (* Massage simpset a bit *)
          val ctxt = ctxt
            |> Context_Position.set_visible false
            |> Context.proof_map (Thm.attribute_declaration Clasimp.iff_del @{thm pair_in_Id_conv})

        in
          if flag_rawgoals then
            all_tac
          else
            Local_Defs.unfold0_tac ctxt def_thms THEN ALLGOALS (
              TRY o SOLVED' (
                TRY o resolve_tac ctxt @{thms frefI}
                THEN' TRY o REPEAT_ALL_NEW (ematch_tac ctxt @{thms prod_relE})
                THEN' simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms split uncurry_apply uncurry0_apply})
                THEN' (
                  SOLVED' (ptac THEN_ALL_NEW asm_full_simp_tac ctxt)
                  ORELSE' SOLVED' (cp_clarsimp_tac ctxt THEN_ALL_NEW_FWD ptac THEN_ALL_NEW SELECT_GOAL (auto_tac ctxt))
                )
              )
            )
  
        end  
  
        val rf_std = Proof.refine (Method.Basic (fn ctxt => SIMPLE_METHOD (std_tac ctxt)))
          #> Seq.the_result "do_cmd: Standard proof tactic returned empty result sequence"

      in
        Proof.theorem NONE after_qed goals lthy
        |> rf_std
      end

      val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "sepref_decl_op"}
        "" (do_parser >> do_cmd)
  



      local
      
        fun unfold_PR_CONST_tac ctxt = SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms PR_CONST_def})

        fun transfer_precond_rl ctxt t R = let
          (*val tfrees = Term.add_tfreesT (fastype_of t) [] 
          val t' = map_types (map_type_tfree (fn x => if member op= tfrees x then dummyT else TFree x)) t
          *) (* TODO: Brute force approach, that may generalize too much! *)
          val t' = map_types (K dummyT) t
        
          val goal = Sepref_Basic.mk_pair_in_pre t t' R 
            |> Syntax.check_term ctxt
            |> Thm.cterm_of ctxt
                                    
          val thm = Drule.infer_instantiate' ctxt [NONE,SOME goal] @{thm IMP_LIST_trivial}

        in
          thm
        end
      
      
        (* Generate a hnr-thm for mop given one for op *)
        fun generate_mop_thm ctxt op_thm = let
          val orig_ctxt = ctxt
      
          val (op_thm, ctxt) = yield_singleton (apfst snd oo Variable.import true) op_thm ctxt
      
          (* Convert mop_def_thms to form uncurry^n f \<equiv> mop P g *)
          val mop_def_thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_mop_def_thms}
            |> map (Local_Defs.unfold0 ctxt @{thms curry_shl})
      
          fun fail_hnr_tac _ _ = raise THM("Invalid hnr-theorem",~1,[op_thm]) 
          fun fail_mop_def_tac i st = let
            val g = nth (Thm.prems_of st) (i-1)
          in
            raise TERM("Found no matching mop-definition",[g])
          end
      
          (* Tactic to solve preconditions of hfref_op_to_mop *)
          val tac = APPLY_LIST [
            resolve_tac ctxt [op_thm] ORELSE' fail_hnr_tac,
            ((*unfold_PR_CONST_tac ctxt THEN'*) resolve_tac ctxt mop_def_thms) ORELSE' fail_mop_def_tac,
            simp_precond_tac ctxt ORELSE' Sepref_Debugging.error_tac' "precond simplification failed" ctxt
          ] 1
      
          (* Do synthesis *)
          val st = @{thm hfref_op_to_mop}
          val st = Goal.protect (Thm.nprems_of st) st
          val mop_thm = tac st |> Seq.hd |> Goal.conclude
      
          val mop_thm = singleton (Variable.export ctxt orig_ctxt) mop_thm
            |> Sepref_Rules.norm_fcomp_rule orig_ctxt
        in mop_thm end  
      
        (* Generate a hnr-thm for op given one for mop *)
        fun generate_op_thm ctxt mop_thm = let (* TODO: Almost-clone of generate_mop_thm *)
          val orig_ctxt = ctxt
      
          val (mop_thm, ctxt) = yield_singleton (apfst snd oo Variable.import true) mop_thm ctxt
      
          (* Convert mop_def_thms to form uncurry^n f \<equiv> mop P g *)
          val mop_def_thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_mop_def_thms}
            |> map (Local_Defs.unfold0 ctxt @{thms curry_shl})
      
          fun fail_hnr_tac _ _ = raise THM("Invalid hnr-theorem",~1,[mop_thm]) 
          fun fail_mop_def_tac i st = let
            val g = nth (Thm.prems_of st) (i-1)
          in
            raise TERM("Found no matching mop-definition",[g])
          end
      
          (* Tactic to solve preconditions of hfref_mop_to_op *)
          val tac = APPLY_LIST [
            resolve_tac ctxt [mop_thm] ORELSE' fail_hnr_tac,
            ((*unfold_PR_CONST_tac ctxt THEN'*) resolve_tac ctxt mop_def_thms) ORELSE' fail_mop_def_tac,
            simp_precond_tac ctxt ORELSE' Sepref_Debugging.error_tac' "precond simplification failed" ctxt
          ] 1
      
          (* Do synthesis *)
          val st = @{thm hfref_mop_to_op}
          val st = Goal.protect (Thm.nprems_of st) st
          val op_thm = tac st |> Seq.hd |> Goal.conclude
      
          val op_thm = singleton (Variable.export ctxt orig_ctxt) op_thm
            |> Sepref_Rules.norm_fcomp_rule orig_ctxt
        in op_thm end  


      
        fun chk_result ctxt thm = let
          val (_,R,S) = case Thm.concl_of thm of
            @{mpat "Trueprop (_\<in>hfref ?P ?R ?S)"} => (P,R,S)
          | _ => raise THM("chk_result: Expected hfref-theorem",~1,[thm])  
      
          fun err t = let
            val ts = Syntax.pretty_term ctxt t |> Pretty.string_of
          in
            raise THM ("chk_result: Invalid pattern left in assertions: " ^ ts,~1,[thm])
          end  
          fun check_invalid (t as @{mpat "hr_comp _ _"}) = err t 
            | check_invalid (t as @{mpat "hrp_comp _ _"}) = err t
            | check_invalid (t as @{mpat "pure (the_pure _)"}) = err t
            | check_invalid (t as @{mpat "_ O _"}) = err t
            | check_invalid _ = false
            
      
          val _ = exists_subterm check_invalid R 
          val _ = exists_subterm check_invalid S
        in
          ()
        end

        fun to_IMP_LIST ctxt thm =    
          (thm RS @{thm to_IMP_LISTI}) |> Local_Defs.unfold0 ctxt @{thms to_IMP_LIST}
  
        fun from_IMP_LIST ctxt thm = thm |> Local_Defs.unfold0 ctxt @{thms from_IMP_LIST}  

      in
    
        local
          open Refine_Util
          val flags = 
               parse_bool_config' "mop" cfg_mop
            || parse_bool_config' "ismop" cfg_ismop
            || parse_bool_config' "transfer" cfg_transfer
            || parse_bool_config' "rawgoals" cfg_rawgoals
            || parse_bool_config' "register" cfg_register
          val parse_flags = parse_paren_list' flags  
      
          val parse_precond = Scan.option (@{keyword "["} |-- Parse.term --| @{keyword "]"})
      
          val parse_fref_thm = Scan.option (@{keyword "uses"} |-- Parse.thm)
      
        in
          val di_parser = parse_flags -- Scan.optional (Parse.binding --| @{keyword ":"}) Binding.empty -- parse_precond -- Parse.thm -- parse_fref_thm
        end  
      
        fun di_cmd ((((flags,name), precond_raw), i_thm_raw), p_thm_raw) lthy = let
          val i_thm = singleton (Attrib.eval_thms lthy) i_thm_raw
          val p_thm = map_option (singleton (Attrib.eval_thms lthy)) p_thm_raw
      
          local
            val ctxt = Refine_Util.apply_configs flags lthy
          in
            val flag_mop = Config.get ctxt cfg_mop
            val flag_ismop = Config.get ctxt cfg_ismop
            val flag_rawgoals = Config.get ctxt cfg_rawgoals
            val flag_transfer = Config.get ctxt cfg_transfer
            val flag_register = Config.get ctxt cfg_register
          end
      
          val fr_attribs = if flag_register then @{attributes [sepref_fr_rules]} else []


          val ctxt = lthy
      
          (* Compose with fref-theorem *)
          val _ = dbg_trace lthy "Compose with fref"

          local
            val hf_tcomp_pre = @{thm hfcomp_tcomp_pre} OF [asm_rl,i_thm]
            fun compose p_thm = let
              val p_thm = p_thm |> to_assns_rl false lthy 
            in
              hf_tcomp_pre OF [p_thm]
            end
      
          in  
            val thm = case p_thm of
              SOME p_thm => compose p_thm
            | NONE => let
                val p_thms = Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_fref_thms}
        
                fun err () = let
                  val prem_s = nth (Thm.prems_of hf_tcomp_pre) 0 |> Syntax.pretty_term ctxt |> Pretty.string_of
                in
                  error ("Found no fref-theorem matching " ^ prem_s)
                end
        
              in
                case get_first (try compose) p_thms of
                  NONE => err ()
                | SOME thm => thm  
        
              end
          end  
      
          val (thm,ctxt) = yield_singleton (apfst snd oo Variable.import true) thm ctxt

          val _ = dbg_trace lthy "Transfer Precond"
          val thm = to_IMP_LIST ctxt thm
          val thm = thm RS @{thm transform_pre_param}
      
          local
            val (pre,R,pp_name,pp_type) = case Thm.prems_of thm of
              [@{mpat "Trueprop (IMP_LIST _ ((?pre,_)\<in>?R))"}, @{mpat "Trueprop (IMP_PRE (mpaq_STRUCT (mpaq_Var ?pp_name ?pp_type)) _)"}] => (pre,R,pp_name,pp_type)
            | _ => raise THM("di_cmd: Cannot recognize first prems of transform_pre_param: ", ~1,[thm])
      
          in
            val thm = if flag_transfer then thm OF [transfer_precond_rl ctxt pre R] else thm
      
            val thm = case precond_raw of 
              NONE => thm
            | SOME precond_raw => let
                val precond = Syntax.parse_term ctxt precond_raw
                  |> Sepref_Basic.constrain_type_pre pp_type
                  |> Syntax.check_term ctxt
                  |> Thm.cterm_of ctxt
      
                val thm = Drule.infer_instantiate ctxt [(pp_name,precond)] thm
                val thm = thm OF [asm_rl,@{thm IMP_PRE_CUSTOMD}]
              in
                thm
              end
      
          end

          val _ = dbg_trace lthy "Build goals"
          val goals = [map (fn x => (x,[])) (Thm.prems_of thm)]

          fun after_qed thmss _ = let
            val _ = dbg_trace lthy "After QED"
            val prems_thms = hd thmss
      
            val thm = thm OF prems_thms

            val thm = from_IMP_LIST ctxt thm

            (* Two rounds of cleanup-constraints, norm_fcomp *)
            val _ = dbg_trace lthy "Cleanup"
            val thm = thm
              |> cleanup_constraints ctxt
              |> Sepref_Rules.norm_fcomp_rule ctxt
              |> cleanup_constraints ctxt
              |> Sepref_Rules.norm_fcomp_rule ctxt
      
            val thm = thm  
              |> singleton (Variable.export ctxt lthy)
              |> zero_var_indexes
      
            val _ = dbg_trace lthy "Check Result"
            val _ = chk_result lthy thm  
      
      
            fun qname suffix = if Binding.is_empty name then name else Binding.suffix_name suffix name 
      
            val thm_name = if flag_ismop then qname "_hnr_mop" else qname "_hnr"
            val (_,lthy) = Local_Theory.note ((thm_name,fr_attribs),[thm]) lthy

            val _ = Thm.pretty_thm lthy thm |> Pretty.string_of |> writeln

            (* Create mop theorem from op-theorem *)
            val cr_mop_thm = flag_mop andalso not flag_ismop
            val lthy = 
              if cr_mop_thm then 
                let 
                  val _ = dbg_trace lthy "Create mop-thm"
                  val mop_thm = thm
                    |> generate_mop_thm lthy
                    |> zero_var_indexes

                  val (_,lthy) = Local_Theory.note ((qname "_hnr_mop",fr_attribs),[mop_thm]) lthy
                  val _ = Thm.pretty_thm lthy mop_thm |> Pretty.string_of |> writeln
                in lthy end 
              else lthy

            (* Create op theorem from mop-theorem *)
            val cr_op_thm = flag_ismop
            val lthy = 
              if cr_op_thm then 
                let 
                  val _ = dbg_trace lthy "Create op-thm"
                  val op_thm = thm
                    |> generate_op_thm lthy
                    |> zero_var_indexes

                  val (_,lthy) = Local_Theory.note ((qname "_hnr",fr_attribs),[op_thm]) lthy
                  val _ = Thm.pretty_thm lthy op_thm |> Pretty.string_of |> writeln
                in lthy end 
              else lthy

      
          in 
            lthy 
          end
      
          fun std_tac ctxt = let 
            val ptac = REPEAT_ALL_NEW_FWD ( 
              Parametricity.net_tac (Parametricity.get_dflt ctxt) ctxt ORELSE' assume_tac ctxt
              )
          in
            if flag_rawgoals orelse not flag_transfer then
              all_tac
            else
              APPLY_LIST [
                SELECT_GOAL (Local_Defs.unfold0_tac ctxt @{thms from_IMP_LIST}) THEN' TRY o SOLVED' ptac,
                simp_precond_tac ctxt
              ] 1
            
          end
      
          val rf_std = Proof.refine (Method.Basic (fn ctxt => SIMPLE_METHOD (std_tac ctxt)))
            #> Seq.the_result "di_cmd: Standard proof tactic returned empty result sequence"

        in
          Proof.theorem NONE after_qed goals ctxt
          |> rf_std
      
        end
      
        val _ = Outer_Syntax.local_theory_to_proof @{command_keyword "sepref_decl_impl"}
          "" (di_parser >> di_cmd)
      end

    end  
  \<close>  

subsection \<open>Obsolete Manual Specification Helpers\<close>

  (* Generate VCG-rules for operations *)
  lemma vcg_of_RETURN_np:  
    assumes "f \<equiv> RETURN r"
    shows "SPEC (\<lambda>x. x=r) \<le> m \<Longrightarrow> f \<le> m"
      and "SPEC (\<lambda>x. x=r) \<le>\<^sub>n m \<Longrightarrow> f \<le>\<^sub>n m"
    using assms
    by (auto simp: pw_le_iff pw_leof_iff)

  lemma vcg_of_RETURN:
    assumes "f \<equiv> do { ASSERT \<Phi>; RETURN r }"
    shows "\<lbrakk>\<Phi>; SPEC (\<lambda>x. x=r) \<le> m\<rbrakk> \<Longrightarrow> f \<le> m"
      and "\<lbrakk>\<Phi> \<Longrightarrow> SPEC (\<lambda>x. x=r) \<le>\<^sub>n m\<rbrakk> \<Longrightarrow> f \<le>\<^sub>n m"
    using assms
    by (auto simp: pw_le_iff pw_leof_iff refine_pw_simps)

  lemma vcg_of_SPEC:  
    assumes "f \<equiv> do { ASSERT pre; SPEC post }"
    shows "\<lbrakk>pre; SPEC post \<le> m\<rbrakk> \<Longrightarrow> f \<le> m"
      and "\<lbrakk>pre \<Longrightarrow> SPEC post \<le>\<^sub>n m\<rbrakk> \<Longrightarrow> f \<le>\<^sub>n m"
    using assms
    by (auto simp: pw_le_iff pw_leof_iff refine_pw_simps)

  lemma vcg_of_SPEC_np:  
    assumes "f \<equiv> SPEC post"
    shows "SPEC post \<le> m \<Longrightarrow> f \<le> m"
      and "SPEC post \<le>\<^sub>n m \<Longrightarrow> f \<le>\<^sub>n m"
    using assms
    by auto 




  (* Generate parametricity rules to generalize 
    plain operations to monadic ones. Use with FCOMP.
  *)  
  lemma mk_mop_rl1:
    assumes "\<And>x. mf x \<equiv> ASSERT (P x) \<then> RETURN (f x)"
    shows "(RETURN o f, mf) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl2:
    assumes "\<And>x y. mf x y \<equiv> ASSERT (P x y) \<then> RETURN (f x y)"
    shows "(RETURN oo f, mf) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl3:
    assumes "\<And>x y z. mf x y z \<equiv> ASSERT (P x y z) \<then> RETURN (f x y z)"
    shows "(RETURN ooo f, mf) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl0_np:
    assumes "mf \<equiv> RETURN f"
    shows "(RETURN f, mf) \<in> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl1_np:
    assumes "\<And>x. mf x \<equiv> RETURN (f x)"
    shows "(RETURN o f, mf) \<in> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl2_np:
    assumes "\<And>x y. mf x y \<equiv> RETURN (f x y)"
    shows "(RETURN oo f, mf) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)

  lemma mk_mop_rl3_np:
    assumes "\<And>x y z. mf x y z \<equiv> RETURN (f x y z)"
    shows "(RETURN ooo f, mf) \<in> Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    unfolding assms[abs_def]
    by (auto intro!: nres_relI simp: pw_le_iff refine_pw_simps)



  lemma mk_op_rl0_np:
    assumes "mf \<equiv> RETURN f"
    shows "(uncurry0 mf, uncurry0 (RETURN f)) \<in> unit_rel \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl1:
    assumes "\<And>x. mf x \<equiv> ASSERT (P x) \<then> RETURN (f x)"
    shows "(mf, RETURN o f) \<in> [P]\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl1_np:
    assumes "\<And>x. mf x \<equiv> RETURN (f x)"
    shows "(mf, (RETURN o f)) \<in> Id \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl2:
    assumes "\<And>x y. mf x y \<equiv> ASSERT (P x y) \<then> RETURN (f x y)"
    shows "(uncurry mf, uncurry (RETURN oo f)) \<in> [uncurry P]\<^sub>f Id\<times>\<^sub>rId \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl2_np:
    assumes "\<And>x y. mf x y \<equiv> RETURN (f x y)"
    shows "(uncurry mf, uncurry (RETURN oo f)) \<in> Id\<times>\<^sub>rId \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl3:
    assumes "\<And>x y z. mf x y z \<equiv> ASSERT (P x y z) \<then> RETURN (f x y z)"
    shows "(uncurry2 mf, uncurry2 (RETURN ooo f)) \<in> [uncurry2 P]\<^sub>f (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow> \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done

  lemma mk_op_rl3_np:
    assumes "\<And>x y z. mf x y z \<equiv> RETURN (f x y z)"
    shows "(uncurry2 mf, uncurry2 (RETURN ooo f)) \<in> (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel"
    apply (intro frefI nres_relI)
    apply (auto simp: assms)
    done








end
