(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
theory Example_Swap_Add
imports 
  "../TypeSystem" 
  TypeSystemTactics
begin

text \<open>
  Use upper-case variable names to avoid clashing with one-letter free variables
\<close>
datatype addr = X | control_X | Y | control_Y | Z | control_Z
type_synonym val = nat
type_synonym mem = "addr \<Rightarrow> val"

datatype aexp = Load "addr" | Const "val" | Add "addr" "addr" 

fun 
  ev\<^sub>A :: "mem \<Rightarrow> aexp \<Rightarrow> val"
where
  "ev\<^sub>A mem (Load x) = mem x" |
  "ev\<^sub>A mem (Const c) = c" |
  "ev\<^sub>A mem (Add x y) = mem x + mem y"
 
fun
  aexp_vars :: "aexp \<Rightarrow> addr set"
where
  "aexp_vars (Load x) = {x}" |
  "aexp_vars (Const c) = {}" |
  "aexp_vars (Add x y) = {x,y}"
  
datatype bexp = Same "addr" "aexp" |
                Eq "addr" "val" |
                Not bexp |
                Imp bexp bexp |
                And bexp bexp |
                Or bexp bexp | TT | FF

fun
  ev\<^sub>B :: "mem \<Rightarrow> bexp \<Rightarrow> bool"
where
  "ev\<^sub>B mem (Same x e) = ((mem x) = (ev\<^sub>A mem e))" | 
  "ev\<^sub>B mem (Eq x c) = ((mem x) = c)" | 
  "ev\<^sub>B mem (Not e) = (\<not> ev\<^sub>B mem e)" |
  "ev\<^sub>B mem (Imp e f) = (ev\<^sub>B mem e \<longrightarrow> ev\<^sub>B mem f)" |
  "ev\<^sub>B mem (And e f) = (ev\<^sub>B mem e \<and> ev\<^sub>B mem f)" |
  "ev\<^sub>B mem (Or e f) = (ev\<^sub>B mem e \<or> ev\<^sub>B mem f)" |
  "ev\<^sub>B mem TT = True" |
  "ev\<^sub>B mem FF = False"


fun
  bexp_vars :: "bexp \<Rightarrow> addr set"
where
  "bexp_vars (Eq x c) = {x}" |
  "bexp_vars (Same x e) = {x} \<union> aexp_vars e" |
  "bexp_vars (Not e) = bexp_vars e" |
  "bexp_vars (Imp e f) = bexp_vars e \<union> bexp_vars f" |
  "bexp_vars (And e f) = bexp_vars e \<union> bexp_vars f" |
  "bexp_vars (Or e f) = bexp_vars e \<union> bexp_vars f" |
  "bexp_vars _ = {}"

  
fun
  bexp_neg :: "bexp \<Rightarrow> bexp"
where
  "bexp_neg e = (Not e)"
  
fun
   bexp_assign :: "addr \<Rightarrow> aexp \<Rightarrow> bexp"
where
  "bexp_assign x e  = (Same x e)"

definition
  dma_control_var :: "val \<Rightarrow> Sec"
where
  "dma_control_var v \<equiv> if v = 0 then Low else High"

fun
  control_var_of :: "addr \<Rightarrow> addr"
where
  "control_var_of X = control_X" |
  "control_var_of Y = control_Y" |
  "control_var_of Z = control_Z"
  
definition
  dma :: "mem \<Rightarrow> addr \<Rightarrow> Sec"
where
  "dma m x \<equiv> if x \<in> {X,Y,Z} then dma_control_var (m (control_var_of x)) else Low"

definition
  \<C>_vars :: "addr \<Rightarrow> addr set"
where
  "\<C>_vars x \<equiv> if x \<in> {X,Y,Z} then {control_var_of x} else {}"

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
  "dma_type X = {Eq control_X 0}" |
  "dma_type Z = {Eq control_Z 0}" |
  "dma_type Y = {Eq control_Y 0}" |
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
  
lemma if_type'': 
  "\<lbrakk>type_bexpr \<Gamma> e t; pred_entailment P t;
    has_type  \<Gamma> \<S> (add_pred P \<S> e) c\<^sub>1 \<Gamma>' \<S>' P';
    has_type \<Gamma> \<S> (add_pred P \<S> (bexp_neg e)) c\<^sub>2 \<Gamma>' \<S>' P'';
    pred_entailment P' {e}; pred_entailment P'' {bexp_neg e};  
    P''' = restrict_preds_to_vars (((Imp e) ` (P' - {e})) \<union> ((Imp (bexp_neg e)) ` (P'' - {bexp_neg e}))) {v. stable \<S>' v}\<rbrakk>
\<Longrightarrow> has_type \<Gamma> \<S> P (Stmt.If e c\<^sub>1 c\<^sub>2) \<Gamma>' \<S>' P'''"
  apply(erule (3) if_type,simp+)
     apply(auto simp: pred_entailment_def pred_def image_def restrict_preds_to_vars_def)[1]
    apply(auto simp: pred_entailment_def pred_def image_def restrict_preds_to_vars_def)[1]
   apply(clarsimp simp: tyenv_wellformed_def mds_consistent_def stable_def image_def restrict_preds_to_vars_def)
   apply fastforce
  apply(clarsimp simp: tyenv_wellformed_def mds_consistent_def stable_def image_def restrict_preds_to_vars_def)
  apply fastforce
  done
  

definition
  swap_vars :: "(addr, aexp, bexp) Stmt"
where
  "swap_vars \<equiv> 
     ModeDecl Skip (Acq control_X AsmNoWrite) ;; 
     ModeDecl Skip (Acq control_Y AsmNoWrite) ;;
     ModeDecl Skip (Acq control_Z AsmNoWrite) ;;
     ModeDecl Skip (Acq X AsmNoReadOrWrite) ;; 
     ModeDecl Skip (Acq Y AsmNoReadOrWrite) ;;
     ModeDecl Skip (Acq Z AsmNoReadOrWrite) ;;
     Assign Z (Load X) ;;
     Assign X (Load Y) ;;
     Assign Y (Load Z) ;;
     Assign control_Z (Load control_X) ;;
     Assign control_X (Load control_Y) ;;
     Assign control_Y (Load control_Z) ;;
     ModeDecl Skip (Rel X AsmNoReadOrWrite) ;;
     ModeDecl Skip (Rel Y AsmNoReadOrWrite) ;;
     ModeDecl Skip (Rel Z AsmNoReadOrWrite) ;;
     ModeDecl Skip (Rel control_X AsmNoWrite) ;; 
     ModeDecl Skip (Rel control_Y AsmNoWrite) ;;
     ModeDecl Skip (Rel control_Z AsmNoWrite) ;;
     Skip"

lemma \<C>_simp[simp]:
  "\<C> = {control_X, control_Y, control_Z}"
proof -
  have "\<C> = control_var_of ` {x. x = X \<or> x = Y \<or> x = Z}"
    by (simp add: \<C>_def \<C>_vars_def UNION_singleton_eq_range)
  also have "{x. x = X \<or> x = Y \<or> x = Z} = {X, Y, Z}"
    by auto
  finally show ?thesis
    by simp
qed

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

lemma type_aexpr_Add:
  "x \<notin> dom \<Gamma> \<Longrightarrow> y \<notin> dom \<Gamma> \<Longrightarrow> 
   type_aexpr \<Gamma> (Add x y) (\<Union> {dma_type x, dma_type y})"
  apply(insert type_aexpr[of \<Gamma> "Add x y", simplified])
  apply(simp add: to_total_def)
  done

lemma type_aexpr_Add':
  "x \<notin> dom \<Gamma> \<Longrightarrow> y \<in> dom \<Gamma> \<Longrightarrow> t = (the (\<Gamma> y)) \<Longrightarrow>
   type_aexpr \<Gamma> (Add x y) (\<Union> {dma_type x, t})"
  apply(insert type_aexpr[of \<Gamma> "Add x y", simplified])
  apply(simp add: to_total_def)
  done

lemma type_aexpr_Add'':
  "x \<in> dom \<Gamma> \<Longrightarrow> y \<notin> dom \<Gamma> \<Longrightarrow> t = (the (\<Gamma> x)) \<Longrightarrow>
   type_aexpr \<Gamma> (Add x y) (\<Union> {t, dma_type y})"
  apply(insert type_aexpr[of \<Gamma> "Add x y", simplified])
  apply(simp add: to_total_def)
  done

lemma type_aexpr_Add''':
  "x \<in> dom \<Gamma> \<Longrightarrow> y \<in> dom \<Gamma> \<Longrightarrow> t = (the (\<Gamma> x)) \<Longrightarrow> t' = (the (\<Gamma> y)) \<Longrightarrow>
   type_aexpr \<Gamma> (Add x y) (\<Union> {t, t'})"
  apply(insert type_aexpr[of \<Gamma> "Add x y", simplified])
  apply(simp add: to_total_def)
  done


lemma type_aexpr_Const[simp]:
  "type_aexpr \<Gamma> (Const c) {}"
  apply(insert type_aexpr[of \<Gamma> "Const c", simplified],simp)
  done


declare restrict_preds_to_vars_def [simp]
declare add_pred_def [simp]
declare stable_def [simp]
declare to_total_def [simp]
declare \<C>_vars_def [simp]
declare anno_type_stable_def [simp]
declare anno_type_sec_def [simp]
declare assign_post_def [simp]


lemma control_vars_cases:
  "control_X \<in> \<C>_vars v \<Longrightarrow> v = X"
  "control_Y \<in> \<C>_vars v \<Longrightarrow> v = Y"
  "control_Z \<in> \<C>_vars v \<Longrightarrow> v = Z"
  by(case_tac v, auto)+

lemma mem_is_different[simp, intro]:
  "mem x = A \<Longrightarrow> mem y \<noteq> A \<Longrightarrow> \<not> ev\<^sub>B  mem (Same y (Load x))"
  "mem x = A \<Longrightarrow> mem y \<noteq> A \<Longrightarrow> \<not> ev\<^sub>B  mem (Same x (Load y))"
  by fastforce+

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
  
declare restrict_preds_to_vars_def[simp del]

lemma [simp]: "pred_entailment P {}" by(simp add: pred_entailment_def pred_def)
lemma [simp]: "e \<in> P \<Longrightarrow> pred_entailment P {e}" by(blast intro: subset_entailment)
lemma [simp]: "FF \<in> P \<Longrightarrow> pred_entailment P Q" by(auto simp: pred_entailment_def pred_def)

lemma swap_vars_typed:
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P swap_vars \<Gamma>' \<S>' P'"
  apply(intro exI)
  apply(simp add: swap_vars_def)
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
        apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply(simp+)[4]

  apply(rule seq_type)
   apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Load')
     apply(simp+)[4]

  apply(rule seq_type)
   apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Load')
     apply(simp+)[4]

  apply(rule seq_type)
   apply(rule assign\<^sub>2[OF _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Load')
     apply(simp+)[4]

  apply(rule seq_type)
   apply(rule assign\<^sub>\<C>[OF _ _ _ _ HOL.refl])
      apply simp
     apply(rule type_aexpr_Load)
     apply (simp+)[4]
  apply simp
 
  apply(rule seq_type)
   apply(rule conc'[where x="Z" and t="dma_type Z", OF _ HOL.refl])
       apply(rule conc'[where x=Y and t="dma_type Z", OF _ HOL.refl])
           apply(rule assign\<^sub>\<C>[OF _ _ _ _ HOL.refl])
                apply simp
               apply(rule type_aexpr_Load)
               apply simp+
         apply(clarsimp simp: type_equiv_def subtype_def pred_entailment_def pred_def)
        apply(fastforce simp: type_wellformed_def)
       apply simp
      apply simp
     apply(clarsimp simp: type_equiv_def subtype_def pred_entailment_def pred_def)
    apply(fastforce simp: type_wellformed_def)
   apply simp

  apply simp
  apply(rule seq_type)
   apply(rule conc'[where x=X and t="dma_type X" , OF _ HOL.refl])
       apply(rule assign\<^sub>\<C>[OF _ _ _ _ HOL.refl])
           apply simp
          apply(rule type_aexpr_Load)
          apply simp+
     apply(clarsimp simp: type_equiv_def subtype_def pred_entailment_def pred_def)
    apply(clarsimp simp: type_wellformed_def)
   apply simp
  
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def pred_entailment_def pred_def)
    apply simp
   apply simp

  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def pred_entailment_def pred_def)
    apply simp
   apply simp
 
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def pred_entailment_def pred_def)
    apply simp
   apply simp

  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def)
     apply (simp add: add_anno_def) 
    apply simp 

  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def)
     apply (simp add: add_anno_def) 
    apply simp 

  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply clarsimp
       apply(rule skip_type)
      apply simp
     apply(fastforce simp: add_anno_def subtype_def)
     apply (simp add: add_anno_def) 
    apply simp 

  apply(rule skip_type)
  done

lemma swap_vars_sifum_secure:
  "com_sifum_secure (swap_vars,(\<lambda>_. {}))"
  apply(insert swap_vars_typed[OF HOL.refl HOL.refl HOL.refl])
  apply clarify
  apply(rule typed_secure)
   apply(fastforce simp: \<Gamma>_of_mds_def \<S>_of_mds_def)
  apply(auto simp: mds_yields_stable_types_def)
  done

definition
  add_vars :: "(addr, aexp, bexp) Stmt"
where
  "add_vars \<equiv> 
     ModeDecl Skip (Acq control_X AsmNoWrite) ;; 
     ModeDecl Skip (Acq control_Y AsmNoWrite) ;;
     ModeDecl Skip (Acq control_Z AsmNoWrite) ;;
     ModeDecl Skip (Acq Z AsmNoReadOrWrite) ;;
     Assign Z (Add X Y) ;;
     If (Eq control_X 0)
        (If (Eq control_Y 0)
            (Assign control_Z (Const 0))
            (Assign control_Z (Const 1)))
        (Assign control_Z (Const 1)) ;;
     ModeDecl Skip (Rel Z AsmNoReadOrWrite) ;;
     ModeDecl Skip (Rel control_X AsmNoWrite) ;; 
     ModeDecl Skip (Rel control_Y AsmNoWrite) ;;
     ModeDecl Skip (Rel control_Z AsmNoWrite) ;;
     Skip"

lemma pred_entailment_singleton_by_case_distinction:
  "Imp e f \<in> P \<Longrightarrow> Imp (bexp.Not e) f \<in> P \<Longrightarrow> pred_entailment P {f}"
  apply(clarsimp simp: pred_entailment_def pred_def)
  apply(case_tac "ev\<^sub>B mem e")
   apply fastforce+
  done


lemma restrict_preds_to_vars_nest [simp]:
  "restrict_preds_to_vars (restrict_preds_to_vars P V) V' = restrict_preds_to_vars P (V \<inter> V')"
  apply(auto simp: restrict_preds_to_vars_def)
  done

lemma restrict_preds_to_vars_imp_image1 [simp]:
  "\<not> bexp_vars e \<subseteq> V \<Longrightarrow> restrict_preds_to_vars (Imp e ` P) V = {}"
  apply(auto simp: restrict_preds_to_vars_def)
  done

lemma restrict_preds_to_vars_imp_image2 [simp]:
  "bexp_vars e \<subseteq> V \<Longrightarrow> restrict_preds_to_vars (Imp e ` P) V = ((Imp e) ` (restrict_preds_to_vars P V))"
  apply(auto simp: restrict_preds_to_vars_def)
  done

  
lemma insert_minus1 [simp]:
  "x = y \<Longrightarrow> (insert x A) - {y} = (A - {y})"
  by auto
  
lemma insert_minus2 [simp]:
  "x \<noteq> y \<Longrightarrow> (insert x A) - {y} = insert x (A - {y})"
  by auto
  
lemma add_vars_typed:
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P add_vars \<Gamma>' \<S>' P'"
  apply(intro exI)
  apply(simp add: add_vars_def)
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp+
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp+
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp+
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp+

  apply(rule seq_type)
   apply(rule assign\<^sub>2)
       apply simp
      apply (rule type_aexpr_Add type_aexpr_Add' type_aexpr_Add'' type_aexpr_Add'''; simp)
     apply(simp)
    apply(simp)
   apply simp
 
  apply(clarsimp)
  apply(rule seq_type)
   apply(rule if_type''[OF _ _ _ _ _ _ HOL.refl])
        apply(rule type_bexprI)
        apply(clarsimp)
        apply(rule HOL.refl)
       apply simp
      apply(rule if_type''[OF _ _ _ _ _ _ HOL.refl])
           apply(rule type_bexprI)
           apply(clarsimp simp: to_total_def)
           apply(rule HOL.refl)
          apply simp
         apply(rule assign\<^sub>\<C>)
              apply simp
             apply(rule type_aexpr_Const)
            apply simp 
           apply (clarsimp, fast)
          apply(simp)
         apply simp
        apply(rule assign\<^sub>\<C>)
             apply simp
            apply(rule type_aexpr_Const)
           apply simp 
          apply auto[1]
         apply(simp)
        apply clarsimp
       apply(clarsimp simp: subset_entailment)
      apply(clarsimp simp: subset_entailment)
             
     apply(rule assign\<^sub>\<C>)
          apply simp
         apply(rule type_aexpr_Const)
        apply simp 
       apply clarsimp 
       apply fast
      apply(simp)
     apply simp
    apply(fastforce intro: pred_entailment_singleton_by_case_distinction simp: image_def)
   apply(fastforce intro: subset_entailment)
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp
     apply(clarsimp simp: subtype_def pred_def add_anno_def pred_entailment_def)
    apply simp+
 
 apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply simp
     apply(clarsimp simp: subtype_def pred_def add_anno_def)
    apply (simp add: add_anno_def)
   apply simp+
 
  apply(rule seq_type)
   apply(rule anno_type[OF HOL.refl HOL.refl HOL.refl])
       apply(rule skip_type)
      apply fastforce+
  done
  

method post_conc_tac 
  declares aexpr bexpr =
  ( simp,
   clarsimp simp: type_equiv_def subtype_def pred_entailment_def pred_def,
   clarsimp simp: type_wellformed_def,
   simp, 
   has_type_tac')

method conc_tac for x :: addr and y :: addr  =
  (rule conc'[where  x="x" and t="dma_type y", OF _ HOL.refl])


lemma swap_vars_typed':
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P swap_vars \<Gamma>' \<S>' P'"
  apply (has_type_tac prog: swap_vars_def aexpr: type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
   apply(conc_tac Z Z)
       apply(conc_tac Y Z)  
           apply (has_type_tac' aexpr:type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
          apply post_conc_tac
      apply post_conc_tac
   apply (has_type_tac' aexpr:type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
   apply(conc_tac X X)
       apply (has_type_tac' aexpr:type_aexpr_Load' type_aexpr_Load bexpr:type_bexprI)
      apply  (post_conc_tac)
  done



lemma add_vars_typed':
  "\<Gamma> = (\<lambda>_. None) \<Longrightarrow> \<S> = ({},{}) \<Longrightarrow> P = {} \<Longrightarrow> 
  \<exists>\<Gamma>' \<S>' P'. has_type \<Gamma> \<S> P add_vars \<Gamma>' \<S>' P'"
  apply (has_type_no_if_tac
          prog: add_vars_def
          aexpr: type_aexpr_Load' type_aexpr_Load type_aexpr_Add 
           type_aexpr_Add' type_aexpr_Add''  type_aexpr_Const
          bexpr:type_bexprI) 
   apply(rule if_type''[OF _ _ _ _ _ _ HOL.refl])
        apply(rule type_bexprI)
        apply(clarsimp)
        apply(rule HOL.refl)
       apply simp
      apply(rule if_type''[OF _ _ _ _ _ _ HOL.refl])
           apply(rule type_bexprI)
           apply(clarsimp)
           apply(rule HOL.refl)
          apply simp
         apply (has_type_tac' aexpr: type_aexpr_Const)
        apply (has_type_tac' aexpr: type_aexpr_Const)
       apply(clarsimp simp: subset_entailment)
      apply(clarsimp simp: subset_entailment)     
     apply (has_type_tac' aexpr: type_aexpr_Const)
    apply simp
    apply(fastforce intro: pred_entailment_singleton_by_case_distinction simp: image_def)
   apply(fastforce intro: subset_entailment)
  apply (has_type_tac')
  done 

end

end
