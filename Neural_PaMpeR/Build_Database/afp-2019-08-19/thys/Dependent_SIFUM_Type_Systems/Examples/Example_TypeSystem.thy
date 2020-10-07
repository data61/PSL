(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
theory Example_TypeSystem
imports 
  "../TypeSystem" 
  TypeSystemTactics
begin

datatype addr = low_var | high_var | control_var | buffer | temp
type_synonym val = nat
type_synonym mem = "addr \<Rightarrow> val"

datatype aexp = Load "addr"

fun 
  ev\<^sub>A :: "mem \<Rightarrow> aexp \<Rightarrow> val"
where
  "ev\<^sub>A mem (Load x) = mem x"
 
fun
  aexp_vars :: "aexp \<Rightarrow> addr set"
where
  "aexp_vars (Load x) = {x}"
  
datatype bexp = Same "addr" "addr" |
                NotSame "addr" "addr" |
                Eq "addr" "val" |
                Neq "addr" "val" |
                TT | FF

fun
  ev\<^sub>B :: "mem \<Rightarrow> bexp \<Rightarrow> bool"
where
  "ev\<^sub>B mem (Same x y) = ((mem x) = (mem y))" | 
  "ev\<^sub>B mem (NotSame x y) = ((mem x) \<noteq> (mem y))" |
  "ev\<^sub>B mem (Eq x c) = ((mem x) = c)" | 
  "ev\<^sub>B mem (Neq x c) = ((mem x) \<noteq> c)" |
  "ev\<^sub>B mem TT = True" |
  "ev\<^sub>B mem FF = False"

fun
  bexp_vars :: "bexp \<Rightarrow> addr set"
where
  "bexp_vars (Neq x c) = {x}" |
  "bexp_vars (Eq x c) = {x}" |
  "bexp_vars (Same x y) = {x,y}" |
  "bexp_vars (NotSame x y) = {x,y}" |
  "bexp_vars _ = {}"
  
fun
  bexp_neg :: "bexp \<Rightarrow> bexp"
where
  "bexp_neg (Neq x y) = (Eq x y)" |
  "bexp_neg (Eq x y) = (Neq x y)" |
  "bexp_neg (Same x y) = (NotSame x y)" |
  "bexp_neg (NotSame x y) = (Same x y)" |
  "bexp_neg TT = FF" |
  "bexp_neg FF = TT"
  
fun
   bexp_assign :: "addr \<Rightarrow> aexp \<Rightarrow> bexp"
where
  "bexp_assign x (Load y)  = (Same x y)"
    
definition
  dma_control_var :: "val \<Rightarrow> Sec"
where
  "dma_control_var v \<equiv> if v = 0 then Low else High"

definition
  dma :: "mem \<Rightarrow> addr \<Rightarrow> Sec"
where
  "dma m x \<equiv> if x = buffer then dma_control_var (m control_var) else if x = high_var then High else Low"

definition
  \<C>_vars :: "addr \<Rightarrow> addr set"
where
  "\<C>_vars x \<equiv> if x = buffer then {control_var} else {}"

definition
  mds\<^sub>s :: "Mode \<Rightarrow> 'Var set"
where 
  "mds\<^sub>s \<equiv> \<lambda>_. {}"

locale sifum_example =
  sifum_lang_no_dma ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars +
  assumes eval_det: "(lc, lc') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<Longrightarrow> (lc, lc'') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<Longrightarrow> lc' = lc''"

definition
  \<C> :: "addr set"
where
  "\<C> \<equiv> \<Union>x. \<C>_vars x"

fun
  dma_type :: "addr \<Rightarrow> bexp set"
where
  "dma_type high_var = {FF}" |
  "dma_type buffer = {Eq control_var 0}" |
  "dma_type _ = {}"

sublocale sifum_example \<subseteq> sifum_types_assign ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars dma \<C>_vars \<C> bexp_neg dma_type FF bexp_assign
  apply(unfold_locales)
              apply(blast intro: eval_det)
             apply(rule Var_finite)
            apply(auto simp: \<C>_vars_def dma_def \<C>_def split: if_splits)[3]
         apply(rename_tac mem e, case_tac e, auto)[1]
        apply(case_tac x, auto simp: dma_def dma_control_var_def)[1]
       apply(case_tac x, auto simp: \<C>_vars_def)[1]
      apply(simp+)[2]
    apply(case_tac e, auto)[1]
   apply(case_tac e, simp)
  apply(auto simp: \<C>_def)
  done

context sifum_example begin

definition
  read_buffer :: "(addr, aexp, bexp) Stmt"
where
  "read_buffer \<equiv> 
     ModeDecl Skip (Acq control_var AsmNoWrite) ;; 
     ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))"


lemma \<C>_simp[simp]:
  "\<C> = {control_var}"
  by(auto simp: \<C>_def \<C>_vars_def split: if_splits)

  
lemma type_aexpr_Load:
  "v \<notin> dom \<Gamma> \<Longrightarrow> type_aexpr \<Gamma> (Load v) (dma_type v)"
  apply(insert type_aexpr[of \<Gamma> "Load v", simplified])
  apply(simp add: to_total_def)
  done

lemma type_aexpr_Load':
  "v \<in> dom \<Gamma> \<Longrightarrow> t = (the (\<Gamma> v)) \<Longrightarrow> type_aexpr \<Gamma> (Load v) t"
  apply(insert type_aexpr[of \<Gamma> "Load v", simplified])
  apply(simp add: to_total_def)
  done


declare restrict_preds_to_vars_def [simp]
declare add_pred_def [simp]
declare stable_def [simp]
declare to_total_def [simp]
declare \<C>_vars_def [simp]
declare anno_type_stable_def [simp]
declare anno_type_sec_def [simp]
declare assign_post_def [simp]

lemma [simp]: "pred_entailment P {}" by(simp add: pred_entailment_def pred_def)
lemma [simp]: "e \<in> P \<Longrightarrow> pred_entailment P {e}" by(blast intro: subset_entailment)
lemma [simp]: "FF \<in> P \<Longrightarrow> pred_entailment P Q" by(auto simp: pred_entailment_def pred_def)

lemma read_buffer_typed:
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P read_buffer \<Gamma>' \<S>' P'"
  apply(intro exI)
  apply(simp add: read_buffer_def)
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply simp
    apply simp
   apply simp
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply simp
    apply simp
   apply simp
  apply(rule seq_type)
   apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Load)
     apply simp
    apply simp    
   apply simp
  apply(rule if_type')
      apply(rule type_bexprI)
      apply simp
     apply(clarsimp)
    apply(rule assign\<^sub>1)
        apply simp
       apply(simp)
      apply(rule type_aexpr_Load')
       apply simp
      apply simp
     apply(simp add: subtype_def)
    apply(simp)
   apply(rule assign\<^sub>1)
       apply simp
      apply simp
     apply(rule type_aexpr_Load')
      apply simp
     apply simp
    apply(simp add: subtype_def)
   apply(simp)
  apply clarsimp
  apply fastforce
  done

lemma read_buffer_com_sifum_secure:
  "com_sifum_secure (read_buffer,(\<lambda>_. {}))"
  apply(insert read_buffer_typed[OF HOL.refl HOL.refl HOL.refl])
  apply clarify
  apply(rule typed_secure)
   apply(fastforce simp: \<Gamma>_of_mds_def \<S>_of_mds_def)
  apply(auto simp: mds_yields_stable_types_def)
  done

definition
  write_buffer :: "(addr, aexp, bexp) Stmt"
where
  "write_buffer \<equiv> 
     ModeDecl Skip (Acq control_var AsmNoWrite) ;; 
     ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     If (Eq control_var 0) (Assign temp (Load low_var)) (Assign temp (Load high_var)) ;;
     Assign buffer (Load temp)"

lemma restrict_preds_to_vars_empty[simp]:
  "restrict_preds_to_vars {} V = {}"
  apply(simp add: restrict_preds_to_vars_def)
  done

lemma restrict_preds_to_vars_idemp[simp]:
  "restrict_preds_to_vars (restrict_preds_to_vars P V) V = 
   restrict_preds_to_vars P V"
  apply(simp add: restrict_preds_to_vars_def)
  done

lemma restrict_preds_to_vars_insert1[simp]:
  "(\<forall>x\<in>bexp_vars a. x \<in> V) \<Longrightarrow> restrict_preds_to_vars (insert a P) V = (insert a (restrict_preds_to_vars P V))"
  apply(simp add: restrict_preds_to_vars_def)
  apply fastforce
  done

lemma restrict_preds_to_vars_insert2[simp]:
  "(\<exists>x\<in>bexp_vars a. x \<notin> V) \<Longrightarrow> restrict_preds_to_vars (insert a P) V = ((restrict_preds_to_vars P V))"
  apply(simp add: restrict_preds_to_vars_def)
  apply fastforce
  done
  
lemma [simp]:
  "Eq a b \<in> P \<Longrightarrow> Neq a b \<in> P \<Longrightarrow> pred_entailment P Q"
  apply(clarsimp simp: pred_entailment_def pred_def)
  apply(frule bspec, assumption)
  apply(drule bspec, assumption, fastforce)
  done
  
declare restrict_preds_to_vars_def[simp del]

lemma write_buffer_typed:
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P write_buffer \<Gamma>' \<S>' P'"
  apply(intro exI)
  apply(simp add: write_buffer_def)
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply simp
    apply simp
   apply simp
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply simp
    apply simp
   apply simp
  apply(rule seq_type)
   apply(rule if_type[where \<Gamma>'''="[temp \<mapsto> dma_type buffer]" and P'''="{}"])
            apply(rule type_bexprI)        
            apply simp
           apply simp
          apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
             apply simp
            apply(rule type_aexpr_Load)
            apply simp
           apply simp 
          apply simp
         apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
            apply simp
           apply(rule type_aexpr_Load)
           apply simp
          apply(simp)
         apply simp
        apply(clarsimp simp: context_equiv_def  type_equiv_def subtype_def)
       apply(clarsimp simp: context_equiv_def type_equiv_def subtype_def)
      apply(blast intro: subset_entailment)
     apply(blast intro: subset_entailment)
    (* need to be careful how we unfold here as otherwise the tactics get overwhelmed *)
    apply clarsimp
    apply(subst tyenv_wellformed_def) 
    apply(clarsimp simp: mds_consistent_def types_wellformed_def type_wellformed_def types_stable_def)
    apply(simp add: tyenv_wellformed_def mds_consistent_def)
    apply blast
   apply clarsimp
   apply(subst tyenv_wellformed_def) 
   apply(clarsimp simp: mds_consistent_def types_wellformed_def type_wellformed_def types_stable_def)
   apply(simp add: tyenv_wellformed_def mds_consistent_def)
   apply blast
  apply(rule assign\<^sub>1)
      apply simp+
    apply(rule type_aexpr_Load')
     apply simp
    apply simp
   apply simp
  apply blast
  done


lemma read_buffer_typed':
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P read_buffer \<Gamma>' \<S>' P'"
  by (has_type_tac prog: read_buffer_def 
       aexpr:type_aexpr_Load' type_aexpr_Load 
       bexpr:type_bexprI)
 
 
lemma write_buffer_typed':
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P write_buffer \<Gamma>' \<S>' P'"
  apply (has_type_tac prog: write_buffer_def aexpr:type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
  apply (if_type_tac bexpr: type_bexprI
          custom_if: if_type[where \<Gamma>'''="[temp \<mapsto> dma_type buffer]" and P'''="{}"])
  apply (has_type_tac' aexpr:type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
  done

end

end
