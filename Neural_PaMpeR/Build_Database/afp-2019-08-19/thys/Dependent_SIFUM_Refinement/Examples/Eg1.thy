theory Eg1
imports Dependent_SIFUM_Type_Systems.Compositionality
        Dependent_SIFUM_Type_Systems.Language
        Dependent_SIFUM_Type_Systems.TypeSystemTactics
begin

datatype var = control_var | buffer | high_var | low_var | temp

type_synonym addr = var
type_synonym val = nat
type_synonym mem = "addr \<Rightarrow> val"

(* Address expression evaluation *)
datatype aexp = Const "val" |
                Load "addr"

fun 
  ev\<^sub>A :: "mem \<Rightarrow> aexp \<Rightarrow> val"
where
  "ev\<^sub>A mem (Const v) = v" |
  "ev\<^sub>A mem (Load x) = mem x"

(* Boolean expression evaluation *)
datatype bexp = Same "addr" "addr" |
                NotSame "addr" "addr" |
                Eq "addr" "val" |
                Neq "addr" "val" | TT | FF

fun
  ev\<^sub>B :: "mem \<Rightarrow> bexp \<Rightarrow> bool"
where
  "ev\<^sub>B mem (Same x y) = ((mem x) = (mem y))" | 
  "ev\<^sub>B mem (NotSame x y) = ((mem x) \<noteq> (mem y))" |
  "ev\<^sub>B mem (Eq x c) = ((mem x) = c)" | 
  "ev\<^sub>B mem (Neq x c) = ((mem x) \<noteq> c)" |
  "ev\<^sub>B mem TT = True" |
  "ev\<^sub>B mem FF = False"


(* NB: dma ~ "domain assignment"
 * Domain assignment function based on the value of a control variable,
 * Low if 0, High otherwise. *)
definition
  dma_control_var :: "val \<Rightarrow> Sec"
where
  "dma_control_var v \<equiv> if v = 0 then Low else High"

(* buffer's security level is controlled by control_var.
 * high_var's is High.
 * All other memory's security level is Low. *)
definition
  dma :: "mem \<Rightarrow> addr \<Rightarrow> Sec"
where
  "dma m x \<equiv> if x = buffer then dma_control_var (m control_var) else if x = high_var then High else Low"

(* Function that gives the control variables of a given variable.
 * Only buffer is controlled by a control variable, control_var *)
definition
  \<C>_vars :: "addr \<Rightarrow> addr set"
where
  "\<C>_vars x \<equiv> if x = buffer then {control_var} else {}"

(* NB: mds ~ "mode state"
 * mds\<^sub>s is the initial mode state - start with it empty. *)
definition
  mds\<^sub>s :: "Mode \<Rightarrow> var set"
where 
  "mds\<^sub>s \<equiv> \<lambda>m. {}"

primrec
  aexp_vars :: "aexp \<Rightarrow> var set"
where
  "aexp_vars (Const _) = {}" |
  "aexp_vars (Load v) = {v}"
  
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
  "bexp_assign x (Const y) = (Eq x y)" |
  "bexp_assign x (Load y)  = (Same x y)"

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


sublocale sifum_example \<subseteq>  sifum_types_assign ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars dma \<C>_vars \<C>  bexp_neg dma_type FF bexp_assign
  apply(unfold_locales)
              apply(blast intro: eval_det)
             apply(rule Var_finite)
            apply(auto simp: \<C>_vars_def dma_def \<C>_def split: if_splits)[3]
         apply(rename_tac mem e, case_tac e, auto)[1]
        apply(case_tac x, auto simp: dma_def dma_control_var_def)[1]
       apply(case_tac x, auto simp: \<C>_vars_def)[1]
      apply(simp+)[2]
    apply(case_tac e, auto)[1]
   apply(case_tac e, simp+)
  apply(auto simp: \<C>_def)
  done

sublocale sifum_example \<subseteq>  sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  by (unfold_locales)


context sifum_example begin


definition
  read_buffer :: "(addr, aexp, bexp) Stmt"
where
  "read_buffer \<equiv> 
     ModeDecl Skip (Acq control_var AsmNoWrite) ;; 
     ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)) ;;
     Assign temp (Const 0) ;;
     ModeDecl Skip (Rel temp AsmNoReadOrWrite)"
thm read_buffer_def

(* PROOF VIA TYPESYSTEM BELOW - adapted from Example_TypeSystem *)

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

lemma type_aexpr_Const:
  "type_aexpr \<Gamma> (Const c) {}"
  apply(insert type_aexpr[of \<Gamma> "Const c", simplified])
  apply(simp)
  done


declare restrict_preds_to_vars_def [simp]
declare add_pred_def [simp]
declare stable_def [simp]
declare to_total_def [simp]
declare \<C>_vars_def [simp]
declare anno_type_stable_def [simp]
declare anno_type_sec_def [simp]

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
  apply clarsimp
  apply(rule seq_type)
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
      apply(clarsimp simp: subtype_def pred_def)
     apply(simp)
    apply(rule assign\<^sub>1)
        apply simp
       apply simp
      apply(rule type_aexpr_Load')
       apply simp
      apply simp
     apply(clarsimp simp: subtype_def pred_def)
    apply(simp)
   apply clarsimp
  apply fastforce
  apply(rule seq_type)
   apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Const)
    apply simp
   apply simp
  apply clarsimp
  apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
      apply clarsimp
      apply(rule skip_type)
     apply simp
    apply(clarsimp simp: add_anno_def subtype_def pred_def bot_Sec_def[symmetric] pred_entailment_def)
   apply simp
  apply simp
  done



lemma read_buffer_typed_auto:
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P read_buffer \<Gamma>' \<S>' P'"
  by (has_type_tac 
            prog: read_buffer_def 
            aexpr: type_aexpr_Load type_aexpr_Load' type_aexpr_Const
            bexpr: type_bexprI)


lemma read_buffer_com_sifum_secure:
  "com_sifum_secure (read_buffer,(\<lambda>m. {}))"
  apply(insert read_buffer_typed[OF HOL.refl HOL.refl HOL.refl])
  apply clarify
  apply(rule typed_secure)
   apply(fastforce simp: \<Gamma>_of_mds_def \<S>_of_mds_def)
  apply(auto simp: mds_yields_stable_types_def)
  done

(* Toby: removed manual bisimulation proof since we now use the type system
   and the manual proofs take quite a while to process. See git log to recover them. *)
end
end
