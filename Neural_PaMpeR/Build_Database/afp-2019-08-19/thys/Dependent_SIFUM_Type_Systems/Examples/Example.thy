(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
theory Example
imports "../Compositionality" "../Language" 
begin

datatype addr = control_var | buffer | high_var | low_var | temp
type_synonym val = nat
type_synonym mem = "addr \<Rightarrow> val"


datatype aexp = Const val |
                Load addr

fun 
  ev\<^sub>A :: "mem \<Rightarrow> aexp \<Rightarrow> val"
where
  "ev\<^sub>A mem (Const v) = v" |
  "ev\<^sub>A mem (Load x) = mem x"
 

datatype bexp = Cmp "addr" "addr" |
                Eq "addr" "val" |
                Neq "addr" "val"

fun
  ev\<^sub>B :: "mem \<Rightarrow> bexp \<Rightarrow> bool"
where
  "ev\<^sub>B mem (Cmp x y) = ((mem x) = (mem y))" | 
  "ev\<^sub>B mem (Eq x v) = ((mem x) = v)"

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
  sifum_lang_no_dma ev\<^sub>A ev\<^sub>B +
  assumes eval_det: "(lc, lc') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<Longrightarrow> (lc, lc'') \<in> sifum_lang_no_dma.eval\<^sub>w ev\<^sub>A ev\<^sub>B \<Longrightarrow> lc' = lc''"
 

definition
  \<C> :: "addr set"
where
  "\<C> \<equiv> \<Union>x. \<C>_vars x"

sublocale sifum_example \<subseteq> sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  apply(unfold_locales)
      apply(blast intro: eval_det)
     apply(rule Var_finite)
    apply(auto simp: \<C>_vars_def dma_def \<C>_def split: if_splits)
  done

context sifum_example begin


definition
  read_buffer :: "(addr, aexp, bexp) Stmt"
where
  "read_buffer \<equiv> 
     ModeDecl Skip (Acq buffer AsmNoWrite) ;; 
     ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))"


(* Note: this invariant ends up tracking mode changes, plus the values of
         variables with an AsmNoWrite assumption --- in this case
         control_var. Thus it feels like it is the sort of thing a 
         flow-sensitive type system should be able to track *)
inductive 
  inv :: "(((addr, aexp, bexp) Stmt, addr, val) LocalConf) \<Rightarrow> bool"
where
  inv\<^sub>1: "\<lbrakk>c = read_buffer; mds AsmNoReadOrWrite = {}; mds AsmNoWrite = {}\<rbrakk> \<Longrightarrow> inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>1': "\<lbrakk>c = (Stop ;; 
     ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>2: "\<lbrakk>c = (ModeDecl Skip (Acq temp AsmNoReadOrWrite) ;;
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite;  buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>2': "\<lbrakk>c = (Stop ;; 
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite;  buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>3: "\<lbrakk>c = ( 
     Assign temp (Load buffer) ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite; buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |

  inv\<^sub>3': "\<lbrakk>c = (
     Stop ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite;  buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>4: "\<lbrakk>c = (
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite; buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>5: "\<lbrakk>c = (
     (Assign low_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite; mem control_var = 0; buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>6: "\<lbrakk>c = (
     (Assign high_var (Load temp)));
     buffer \<in> mds AsmNoWrite; temp \<in> mds AsmNoReadOrWrite; mem control_var \<noteq> 0; buffer \<notin> mds AsmNoReadOrWrite\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>" |
  inv\<^sub>7: "\<lbrakk>c = Stop\<rbrakk> \<Longrightarrow>
   inv \<langle>c, mds, mem\<rangle>"

(* Note: this relational invariant is tracking equalities on AsmNoRead
         variables, based on classification in formation which here we
         have encoded as ahead-of-time information about control_var but
         could be written instead as assertions about "dma buffer".
         Again it feels like something a flow-sensitive type system should
         be able to track, assuming we can accurately track changes to dma,
         which feels like it should be possible *)
inductive_set 
  rel_inv :: "(((addr, aexp, bexp) Stmt, addr, val) LocalConf) rel"
where
  "\<lbrakk>c = ( Stop ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))); mem control_var = 0; mem temp = mem' temp\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  "\<lbrakk>c = ( Stop ;;
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))); mem control_var \<noteq> 0\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  "\<lbrakk>c = (
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))); mem control_var = 0; mem temp = mem' temp\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
     "\<lbrakk>c = (
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))); mem control_var \<noteq> 0\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  "\<lbrakk>c = (Assign low_var (Load temp)); mem control_var = 0; 
      mem temp = mem' temp\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv" |
  "\<lbrakk>c \<noteq> (Stop ;; (
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp)))); c \<noteq> (
     If (Eq control_var 0) (Assign low_var (Load temp)) (Assign high_var (Load temp))); c \<noteq> (Assign low_var (Load temp))\<rbrakk> \<Longrightarrow>
      (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv"

(* the bisimulation is phrased as a conjunction of a global invariant and a 
   relational invariant, defined above, plus the background requirement
   of low-equivalence modulo modes *)
inductive_set  
  R :: "(((addr, aexp, bexp) Stmt, addr, val) LocalConf) rel"
where
  "\<lbrakk>c = c'; mds = mds'; low_mds_eq mds mem mem'; inv \<langle>c,mds,mem\<rangle>;
    (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv\<rbrakk> \<Longrightarrow>
   (\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> R"

lemma [simp]:
  "control_var \<in> \<C>"
  apply(simp add: \<C>_def)
  apply(rule_tac x=buffer in exI)
  apply(simp add: \<C>_vars_def)
  done

lemma low_mds_eq_control_var_eq:
  "low_mds_eq mds mem mem' \<Longrightarrow> mem control_var = mem' control_var"
  apply(auto simp: low_mds_eq_def dma_def)
  done

  
lemma inv_low_mds_eq:
  "\<lbrakk>c = c'; mds = mds'; low_mds_eq mds mem mem'; inv \<langle>c,mds,mem\<rangle>\<rbrakk>  \<Longrightarrow>
   inv \<langle>c',mds',mem'\<rangle>"
  apply(erule inv.cases)
  apply(auto intro: inv.intros dest!: low_mds_eq_control_var_eq)
  done

lemma rel_inv_sym:
  "low_mds_eq mds mem mem' \<Longrightarrow> (\<langle>c, mds, mem\<rangle>, \<langle>c, mds, mem'\<rangle>) \<in> rel_inv \<Longrightarrow>
    (\<langle>c, mds, mem'\<rangle>, \<langle>c, mds, mem\<rangle>) \<in> rel_inv"
  apply(auto elim!: rel_inv.cases intro: rel_inv.intros simp: low_mds_eq_control_var_eq)
  done

lemma R_sym':
  "(\<langle>c, mds, mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> R \<Longrightarrow>
   (\<langle>c', mds', mem'\<rangle>, \<langle>c, mds, mem\<rangle>) \<in> R"
  apply(rule R.intros)
    apply(blast elim: R.cases dest: low_mds_eq_sym intro: inv_low_mds_eq dest: rel_inv_sym)+
  done

lemma R_sym:
  "sym R"
  by(rule symI, clarify, erule R_sym')


lemma inv_closed_glob_consistent:
  "inv \<langle>c', mds', mem\<rangle> \<Longrightarrow>
       \<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem x \<noteq> v \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x  \<Longrightarrow>
       inv \<langle>c', mds', mem [\<parallel>\<^sub>1 A]\<rangle>"
  apply(erule inv.cases)
  apply(fastforce intro: inv.intros)+
    apply(clarsimp simp: apply_adaptation_def split: option.splits)
    apply(drule_tac x=control_var in spec)
    apply clarsimp
    apply(drule_tac x=buffer in spec)
    apply(clarsimp simp: dma_def dma_control_var_def split: if_splits)
    apply(auto intro: inv.intros simp: var_asm_not_written_def)[2]
  apply(drule_tac x=control_var in spec)
  apply(drule_tac x=buffer in spec)
  apply(clarsimp simp: dma_def dma_control_var_def split: if_splits option.splits)
  apply(auto intro: inv.intros simp: var_asm_not_written_def)
  done

lemma updates_to_control_var:
  "\<forall>x. dma mem [\<parallel>\<^sub>1 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x  \<Longrightarrow>
    buffer \<in> mds' AsmNoWrite \<Longrightarrow>
    case A control_var of Some (x, y) \<Rightarrow> (x = 0) = (mem control_var = 0) | _ \<Rightarrow> True"
  apply(drule_tac x=buffer in spec)
  apply(auto simp: apply_adaptation_def split: option.splits simp: dma_def dma_control_var_def split: if_splits simp: var_asm_not_written_def)
  done

lemma blah:
  "\<forall>x a b. A x = Some (a, b) \<longrightarrow> (mem x = a \<longrightarrow> mem' x \<noteq> b) \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
    mem x = mem' x \<Longrightarrow>
    x \<in> mds' AsmNoReadOrWrite \<or> x \<in> mds' AsmNoWrite \<Longrightarrow>  mem [\<parallel>\<^sub>1 A] x = mem' [\<parallel>\<^sub>2 A] x"
  apply(auto simp: apply_adaptation_def split: option.splits simp: var_asm_not_written_def)
  done

lemma rel_inv_closed_glob_consistent:
  "inv \<langle>c', mds', mem\<rangle> \<Longrightarrow> (\<langle>c', mds', mem\<rangle>, \<langle>c', mds', mem'\<rangle>) \<in> rel_inv \<Longrightarrow>
       \<forall>x a b.
          A x = Some (a, b) \<longrightarrow>
          (mem x = a \<longrightarrow> mem' x \<noteq> b) \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x \<noteq> dma mem x \<longrightarrow> \<not> var_asm_not_written mds' x \<Longrightarrow>
       \<forall>x. dma mem [\<parallel>\<^sub>1 A] x = Low \<and> (x \<in> mds' AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow>
           mem [\<parallel>\<^sub>1 A] x = mem' [\<parallel>\<^sub>2 A] x \<Longrightarrow>
       (\<langle>c', mds', mem [\<parallel>\<^sub>1 A]\<rangle>, \<langle>c', mds', mem' [\<parallel>\<^sub>2 A]\<rangle>) \<in> rel_inv"
  apply(safe elim!: rel_inv.cases elim!: inv.cases)
  apply(unfold read_buffer_def)
  apply(simp_all)
       (* there are actually 14 goals at this point but 8 are solved at the end by auto, so
          we indent as if there were 6 *)
       apply(rule rel_inv.intros(1), simp+)
        apply(drule updates_to_control_var, simp+)
        apply(fastforce split: option.splits simp: apply_adaptation_def)
       apply(fastforce intro!: blah)
      apply(rule rel_inv.intros(2), simp+)
      apply(drule updates_to_control_var, simp+)
      apply(fastforce split: option.splits simp: apply_adaptation_def)
     apply(rule rel_inv.intros(3), simp+)
      apply(drule updates_to_control_var, simp+)
      apply(fastforce split: option.splits simp: apply_adaptation_def)
     apply(fastforce intro!: blah)
    apply(rule rel_inv.intros(4), simp+)
    apply(drule updates_to_control_var, simp+)
    apply(fastforce split: option.splits simp: apply_adaptation_def)
   apply(rule rel_inv.intros(5), simp+)
    apply(drule updates_to_control_var, simp+)
    apply(fastforce split: option.splits simp: apply_adaptation_def)
   apply(fastforce intro!: blah)
  apply(rule rel_inv.intros(6), simp+)
  apply(drule updates_to_control_var, simp+)
  by (auto intro: rel_inv.intros)

lemma R_closed_glob_consistent:
  "closed_glob_consistent R"
  unfolding closed_glob_consistent_def  
  apply(auto elim!: R.cases intro!: R.intros simp: low_mds_eq_def intro!: inv_closed_glob_consistent split: option.splits intro: rel_inv_closed_glob_consistent) 
  done

lemma R_low_mds_eq:
  "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R \<Longrightarrow>
        low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
  apply(blast elim: R.cases)
  done

lemma decl_eval\<^sub>w':
  assumes mem_unchanged: "mem' = mem"
  assumes upd: "mds' = update_modes upd mds"
  shows "(\<langle>Skip@[upd], mds, mem\<rangle>, \<langle>Stop, mds', mem'\<rangle>) \<in> eval\<^sub>w"
  using decl[OF unannotated, OF skip, where E="[]", simplified, where E1="[]", simplified]
  assms by auto


lemmas decl_eval\<^sub>w = decl[OF unannotated, OF skip, where E="[]", simplified, where E1="[]", simplified]
lemmas seq_stop_eval\<^sub>w = unannotated[OF seq_stop, where E="[]", simplified]
lemmas assign_eval\<^sub>w = unannotated[OF assign, where E="[]", simplified]
lemmas if_eval\<^sub>w = unannotated[OF cond, where E="[]", simplified]
lemmas if_false_eval\<^sub>w = unannotated[OF if_false, where E="[]", simplified]

lemma \<C>_simp [simp]:
  "\<C> = {control_var}"
  apply(auto simp: \<C>_def \<C>_vars_def split: if_splits)
  done

lemma buffer_eq:
  "mem\<^sub>1 control_var = 0 \<Longrightarrow> buffer \<notin> mds' AsmNoReadOrWrite \<Longrightarrow> low_mds_eq mds' mem\<^sub>1 mem\<^sub>2  \<Longrightarrow>
  mem\<^sub>1 buffer = mem\<^sub>2 buffer"
  apply(clarsimp simp: low_mds_eq_def)
  apply(drule spec, erule mp)
  apply(clarsimp simp: dma_def dma_control_var_def)
  done

lemma rel_inv_init:
  "buffer \<notin> mds' AsmNoReadOrWrite \<Longrightarrow> low_mds_eq mds' mem\<^sub>1 mem\<^sub>2 \<Longrightarrow>
    (\<langle>Stop ;;
      Stmt.If (Eq control_var 0) (low_var \<leftarrow> Load temp)
       (high_var \<leftarrow> Load temp), mds', mem\<^sub>1
     (temp := ev\<^sub>A mem\<^sub>1 (Load buffer))\<rangle>,
     \<langle>Stop ;;
      Stmt.If (Eq control_var 0) (low_var \<leftarrow> Load temp)
       (high_var \<leftarrow> Load temp), mds', mem\<^sub>2
     (temp := ev\<^sub>A mem\<^sub>2 (Load buffer))\<rangle>)
    \<in> rel_inv"
  apply(case_tac "mem\<^sub>1 control_var = 0")
   apply(frule (2) buffer_eq)    
  apply(fastforce intro: rel_inv.intros simp: ev\<^sub>A.simps)+
  done

lemma R_inv:
  notes ev\<^sub>A.simps[simp del]
  shows  "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R \<Longrightarrow>
       (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>) \<in> eval\<^sub>w \<Longrightarrow>
       \<exists>c\<^sub>2' mem\<^sub>2'.
          (\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> eval\<^sub>w \<and>
          (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> R"
  apply(erule R.cases)
  apply clarsimp
  apply(erule inv.cases)
           apply clarsimp
           apply(rule_tac x=c\<^sub>1' in exI)
           apply(rule_tac x=mem\<^sub>2 in exI)
           apply(unfold read_buffer_def)
           apply(drule seq_elim, simp)
           apply clarsimp
           apply(drule upd_elim, drule skip_elim, simp)
           apply clarsimp
           apply(rule conjI)
            apply(rule eval\<^sub>w.seq)
            apply(rule decl_eval\<^sub>w', simp+)
           apply(rule R.intros, simp+)
             apply(fastforce simp: low_mds_eq_def)
            apply(rule inv\<^sub>1', simp+)
           apply(fastforce intro: rel_inv.intros)
          apply clarsimp
          apply(drule seq_stop_elim, clarsimp)
          apply(rule exI)+
          apply(intro conjI)
           apply(rule seq_stop_eval\<^sub>w)
          apply(rule R.intros, simp+)
           apply(blast intro: inv.intros)
          apply(fastforce intro: rel_inv.intros)
         apply clarsimp
         apply(rule_tac x=c\<^sub>1' in exI)
         apply(rule_tac x=mem\<^sub>2 in exI)
         apply(drule seq_elim, simp)
         apply clarsimp
         apply(drule upd_elim, drule skip_elim, simp)
         apply clarsimp
         apply(rule conjI)
          apply(rule eval\<^sub>w.seq)
          apply(rule decl_eval\<^sub>w', simp+)
         apply(rule R.intros, simp+)
           apply(fastforce simp: low_mds_eq_def)
          apply(rule inv\<^sub>2', simp+)
         apply(fastforce intro: rel_inv.intros)
        apply clarsimp
        apply(drule seq_stop_elim, clarsimp)
        apply(rule exI)+
        apply(intro conjI)
         apply(rule seq_stop_eval\<^sub>w)
        apply(rule R.intros, simp+)
         apply(blast intro: inv.intros)
        apply(fastforce intro: rel_inv.intros)
       apply clarsimp
       apply(rule exI)+
       apply(drule seq_elim, simp)
       apply clarsimp
       apply(drule assign_elim)
       apply clarsimp
       apply(rule conjI)
        apply(rule eval\<^sub>w.seq)
        apply(rule assign_eval\<^sub>w)
       apply(rule R.intros, simp+)
         apply(clarsimp simp: low_mds_eq_def ev\<^sub>A.simps)
         apply(fastforce simp: dma_def split: if_splits)[1]
        apply(rule inv\<^sub>3', simp+)
       apply(fastforce intro: rel_inv_init)
      apply clarsimp
      apply(drule seq_stop_elim, clarsimp)
      apply(rule exI)+
      apply(intro conjI)
       apply(rule seq_stop_eval\<^sub>w)
      apply(rule R.intros, simp+)
       apply(blast intro: inv.intros)
      apply(auto intro: rel_inv.intros elim!: rel_inv.cases)[1]    
     apply clarsimp
     apply(rule exI)+
     apply(erule if_elim)
      apply(rule conjI)
       apply simp
       apply(rule if_eval\<^sub>w)
      apply simp
      apply(rule conjI)
       apply(rule impI)
       apply(rule R.intros, simp+)
        apply(blast intro: inv.intros)
       apply(auto intro: rel_inv.intros elim!: rel_inv.cases)[1]
      apply(simp add: low_mds_eq_control_var_eq)+
     apply(rule conjI)
      apply(rule if_false_eval\<^sub>w, simp)
     apply(rule R.intros, simp+)
      apply(rule inv\<^sub>6, (simp add: low_mds_eq_control_var_eq)+)
     apply(fastforce intro: rel_inv.intros)
    apply clarsimp
    apply(rule exI)+
    apply(drule assign_elim)
    apply(rule conjI)
     apply simp
     apply(rule assign_eval\<^sub>w)
      apply(simp add: low_mds_eq_control_var_eq)
     apply(rule R.intros, simp+)
      apply(clarsimp simp: low_mds_eq_def dma_def)
      apply(simp add: ev\<^sub>A.simps)
      apply(clarsimp split: if_splits)[1]
      apply(fastforce elim: rel_inv.cases)
     apply(fastforce intro: inv.intros)
    apply(fastforce intro: rel_inv.intros)
   apply clarsimp
   apply(rule exI)+
   apply(drule assign_elim)
   apply(rule conjI)
    apply simp
    apply(rule assign_eval\<^sub>w)
     apply(simp add: low_mds_eq_control_var_eq)
    apply(rule R.intros, simp+)
     apply(clarsimp simp: low_mds_eq_def dma_def)
     apply(simp add: ev\<^sub>A.simps)
     apply(clarsimp split: if_splits)[1]
    apply(fastforce intro: inv.intros)
   apply(fastforce intro: rel_inv.intros)
  using stop_no_eval by fastforce

lemma strong_low_bisim_mm_R:
  "strong_low_bisim_mm R"
unfolding strong_low_bisim_mm_def
proof(safe)
  show "sym R" by(rule R_sym)
next
  show "closed_glob_consistent R" by(rule R_closed_glob_consistent)
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2  mem\<^sub>2
  assume "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R"
  thus "low_mds_eq mds mem\<^sub>1 mem\<^sub>2"
  by(rule R_low_mds_eq)
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2  mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
  assume "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> R"
     and "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>) \<in> eval\<^sub>w"
  thus "\<exists>c\<^sub>2' mem\<^sub>2'.
        (\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> eval\<^sub>w \<and>
        (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> R"
    by(rule R_inv)
qed
    
lemma read_buffer_secure':
  "low_mds_eq mds\<^sub>s mem\<^sub>1 mem\<^sub>2 \<Longrightarrow>
       (\<langle>read_buffer, mds\<^sub>s, mem\<^sub>1\<rangle>, \<langle>read_buffer, mds\<^sub>s, mem\<^sub>2\<rangle>) \<in> R"
  apply(rule R.intros)
  apply simp_all
   apply(rule inv\<^sub>1)
     apply (simp_all add: mds\<^sub>s_def)
  unfolding read_buffer_def by(fastforce intro: rel_inv.intros)

lemma "com_sifum_secure (read_buffer,mds\<^sub>s)"
  unfolding com_sifum_secure_def low_indistinguishable_def
  apply clarify
  apply(rule mm_equiv_intro)
   apply(rule strong_low_bisim_mm_R)
  by(rule read_buffer_secure')  

end
 
end
