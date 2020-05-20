(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou.
 *)

theory Sparc_Properties

imports Main Sparc_Execution

begin

(*********************************************************************)

section\<open>Single step theorem\<close>

(*********************************************************************)

text \<open>The following shows that, if the pre-state satisfies certain 
  conditions called \<open>good_context\<close>, there must be a defined post-state 
  after a single step execution.\<close>

method save_restore_proof =
((simp add: save_restore_instr_def),
 (simp add: Let_def simpler_gets_def bind_def h1_def h2_def),
 (simp add: case_prod_unfold),
 (simp add: raise_trap_def simpler_modify_def),
 (simp add: simpler_gets_def bind_def h1_def h2_def),
 (simp add: save_retore_sub1_def),
 (simp add: write_cpu_def simpler_modify_def),
 (simp add: write_reg_def simpler_modify_def),
 (simp add: get_curr_win_def),
 (simp add: simpler_gets_def bind_def h1_def h2_def))

method select_trap_proof0 = 
((simp add: select_trap_def exec_gets return_def),
 (simp add: DetMonad.bind_def h1_def h2_def simpler_modify_def),
 (simp add: write_cpu_tt_def write_cpu_def),
 (simp add: DetMonad.bind_def h1_def h2_def simpler_modify_def),
 (simp add: return_def simpler_gets_def))

method select_trap_proof1 =
((simp add: select_trap_def exec_gets return_def),
 (simp add: DetMonad.bind_def h1_def h2_def simpler_modify_def),
 (simp add: write_cpu_tt_def write_cpu_def),
 (simp add: DetMonad.bind_def h1_def h2_def simpler_modify_def),
 (simp add: return_def simpler_gets_def),
 (simp add: emp_trap_set_def err_mode_val_def cpu_reg_mod_def))

method dispatch_instr_proof1 =
((simp add: dispatch_instruction_def),
 (simp add: simpler_gets_def bind_def h1_def h2_def),
 (simp add: Let_def))

method exe_proof_to_decode =
((simp add: execute_instruction_def),
 (simp add: exec_gets bind_def h1_def h2_def Let_def return_def),
 clarsimp,
 (simp add: simpler_gets_def bind_def h1_def h2_def Let_def simpler_modify_def),
 (simp add: return_def))

method exe_proof_dispatch_rett =
((simp add: dispatch_instruction_def),
 (simp add: simpler_gets_def bind_def h1_def h2_def Let_def),
 (simp add: rett_instr_def),
 (simp add: simpler_gets_def bind_def h1_def h2_def Let_def))

lemma write_cpu_result: "snd (write_cpu w r s) = False"
by (simp add: write_cpu_def simpler_modify_def)

lemma set_annul_result: "snd (set_annul b s) = False"
by (simp add: set_annul_def simpler_modify_def)

lemma raise_trap_result : "snd (raise_trap t s) = False"
by (simp add: raise_trap_def simpler_modify_def)

lemma rett_instr_result: "(fst i) = ctrl_type RETT \<and> 
  (get_ET (cpu_reg_val PSR s) \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s)) = 0 \<and>
  (bitAND (get_addr (snd i) s) (0b00000000000000000000000000000011::word32)) = 0) \<Longrightarrow>
  snd (rett_instr i s) = False"
apply (simp add: rett_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: raise_trap_def simpler_modify_def)
by (simp add: return_def)

lemma call_instr_result: "(fst i) = call_type CALL \<Longrightarrow>
  snd (call_instr i s) = False"
apply (simp add: call_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def case_prod_unfold)
apply (simp add: write_cpu_def write_reg_def)
apply (simp add: get_curr_win_def get_CWP_def)
by (simp add: simpler_modify_def simpler_gets_def)

lemma branch_instr_result: "(fst i) \<in> {bicc_type BE,bicc_type BNE,bicc_type BGU,
 bicc_type BLE,bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
 bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,bicc_type BN}  \<Longrightarrow>
  snd (branch_instr i s) = False" 
proof (cases "eval_icc (fst i) (get_icc_N ((cpu_reg s) PSR)) (get_icc_Z ((cpu_reg s) PSR))
                           (get_icc_V ((cpu_reg s) PSR)) (get_icc_C ((cpu_reg s) PSR)) = 1")
  case True
  then have f1: "eval_icc (fst i) (get_icc_N ((cpu_reg s) PSR)) (get_icc_Z ((cpu_reg s) PSR))
                           (get_icc_V ((cpu_reg s) PSR)) (get_icc_C ((cpu_reg s) PSR)) = 1" 
    by auto
  then show ?thesis
  proof (cases "(fst i) = bicc_type BA \<and> get_operand_flag ((snd i)!0) = 1")
    case True
    then show ?thesis using f1
    apply (simp add: branch_instr_def)
    apply (simp add: Let_def simpler_gets_def bind_def h1_def h2_def)    
    apply (simp add: set_annul_def case_prod_unfold)
    apply (simp add: write_cpu_def simpler_modify_def)
    by (simp add: return_def)   
  next
    case False
    then have f2: "\<not> (fst i = bicc_type BA \<and> get_operand_flag (snd i ! 0) = 1)" by auto
    then show ?thesis using f1
    apply (simp add: branch_instr_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: write_cpu_def simpler_modify_def)
    apply (simp add: branch_instr_sub1_def)
    apply (simp add: Let_def)
    apply auto
    apply (simp add: write_cpu_def simpler_modify_def)    
    by (simp add: write_cpu_def simpler_modify_def)
  qed
next
  case False
  then show ?thesis
  apply (simp add: branch_instr_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: write_cpu_def simpler_modify_def)
  apply (simp add: branch_instr_sub1_def)
  apply (simp add: Let_def)
  apply auto
   apply (simp add: Let_def bind_def h1_def h2_def)
   apply (simp add: write_cpu_def simpler_modify_def)
   apply (simp add: cpu_reg_mod_def set_annul_def simpler_modify_def)
  by (simp add: write_cpu_def simpler_modify_def)
qed

lemma nop_instr_result: "(fst i) = nop_type NOP \<Longrightarrow>
  snd (nop_instr i s) = False"
apply (simp add: nop_instr_def)
by (simp add: returnOk_def return_def)

lemma sethi_instr_result: "(fst i) = sethi_type SETHI \<Longrightarrow>
  snd (sethi_instr i s) = False"
apply (simp add: sethi_instr_def)
apply (simp add: Let_def)
apply (simp add: get_curr_win_def get_CWP_def cpu_reg_val_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: write_reg_def simpler_modify_def)
by (simp add: return_def)

lemma jmpl_instr_result: "(fst i) = ctrl_type JMPL \<Longrightarrow>
  snd (jmpl_instr i s) = False"
apply (simp add: jmpl_instr_def)
apply (simp add: get_curr_win_def get_CWP_def cpu_reg_val_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: write_cpu_def simpler_modify_def)
by (simp add: raise_trap_def simpler_modify_def)

lemma save_restore_instr_result: "(fst i) \<in> {ctrl_type SAVE,ctrl_type RESTORE} \<Longrightarrow>
  snd (save_restore_instr i s) = False"
proof (cases "(fst i) = ctrl_type SAVE")
  case True
  then show ?thesis
  by save_restore_proof
next
  case False
  then show ?thesis
  by save_restore_proof
qed

lemma flush_instr_result: "(fst i) = load_store_type FLUSH  \<Longrightarrow>
  snd (flush_instr i s) = False" 
apply (simp add: flush_instr_def)
by (simp add: simpler_gets_def bind_def h1_def h2_def simpler_modify_def)

lemma read_state_reg_instr_result: "(fst i) \<in> {sreg_type RDY,sreg_type RDPSR,
  sreg_type RDWIM,sreg_type RDTBR} \<Longrightarrow>
  snd (read_state_reg_instr i s) = False"
apply (simp add: read_state_reg_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: simpler_gets_def bind_def)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: raise_trap_def simpler_modify_def return_def)
apply (simp add: bind_def h1_def h2_def)
by (simp add: get_curr_win_def simpler_gets_def)

lemma write_state_reg_instr_result: "(fst i) \<in> {sreg_type WRY,sreg_type WRPSR,
  sreg_type WRWIM,sreg_type WRTBR} \<Longrightarrow>
  snd (write_state_reg_instr i s) = False" 
apply (simp add: write_state_reg_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: simpler_modify_def)
apply (simp add: raise_trap_def simpler_modify_def return_def)
apply (simp add: bind_def h1_def h2_def)
apply (simp add: simpler_gets_def)
apply (simp add: write_cpu_def simpler_modify_def)
by (simp add: get_curr_win_def simpler_gets_def)

lemma logical_instr_result: "(fst i) \<in> {logic_type ANDs,logic_type ANDcc,
  logic_type ANDN,logic_type ANDNcc,logic_type ORs,logic_type ORcc,
  logic_type ORN,logic_type XORs,logic_type XNOR} \<Longrightarrow>
  snd (logical_instr i s) = False"
apply (simp add: logical_instr_def)
apply (simp add: Let_def simpler_gets_def)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: logical_instr_sub1_def)
apply (simp add: return_def)
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: bind_def h1_def h2_def)
apply (simp add: case_prod_unfold)
apply (simp add: simpler_gets_def)
by (simp add: get_curr_win_def simpler_gets_def)

lemma shift_instr_result: "(fst i) \<in> {shift_type SLL,shift_type 
  SRL,shift_type SRA} \<Longrightarrow>
  snd (shift_instr i s) = False"
apply (simp add: shift_instr_def)
apply (simp add: Let_def)
apply (simp add: get_curr_win_def simpler_gets_def bind_def h1_def h2_def)
apply (simp add: return_def)
apply (simp add: bind_def h1_def h2_def)
by (simp add: write_reg_def simpler_modify_def)

method add_sub_instr_proof =
((simp add: Let_def),
 auto,
 (simp add: write_reg_def simpler_modify_def),
 (simp add: simpler_gets_def bind_def),
 (simp add: get_curr_win_def simpler_gets_def),
 (simp add: write_reg_def write_cpu_def simpler_modify_def),
 (simp add: bind_def),
 (simp add: case_prod_unfold),
 (simp add: simpler_gets_def),
 (simp add: get_curr_win_def simpler_gets_def),
 (simp add: write_reg_def simpler_modify_def),
 (simp add: simpler_gets_def bind_def),
 (simp add: get_curr_win_def simpler_gets_def))

lemma add_instr_result: "(fst i) \<in> {arith_type ADD,arith_type 
  ADDcc,arith_type ADDX} \<Longrightarrow>
  snd (add_instr i s) = False"
apply (simp add: add_instr_def)
apply (simp add: Let_def)
apply auto
  apply (simp add: add_instr_sub1_def)
  apply (simp add: write_reg_def simpler_modify_def)
  apply (simp add: bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: simpler_gets_def)
  apply (simp add: get_curr_win_def simpler_gets_def)
 apply (simp add: add_instr_sub1_def)
 apply (simp add: write_reg_def simpler_modify_def)
 apply (simp add: simpler_gets_def bind_def h1_def h2_def)
 apply (simp add: get_curr_win_def simpler_gets_def)
 apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: add_instr_sub1_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: get_curr_win_def simpler_gets_def)
by (simp add: write_reg_def simpler_modify_def)

lemma sub_instr_result: "(fst i) \<in> {arith_type SUB,arith_type SUBcc,
  arith_type SUBX} \<Longrightarrow>
  snd (sub_instr i s) = False"
apply (simp add: sub_instr_def)
apply (simp add: Let_def)
apply auto
  apply (simp add: sub_instr_sub1_def)
  apply (simp add: write_reg_def simpler_modify_def)
  apply (simp add: bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: simpler_gets_def)
  apply (simp add: get_curr_win_def simpler_gets_def)
 apply (simp add: sub_instr_sub1_def)
 apply (simp add: write_reg_def simpler_modify_def)
 apply (simp add: simpler_gets_def bind_def h1_def h2_def)
 apply (simp add: get_curr_win_def simpler_gets_def)
 apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: sub_instr_sub1_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: get_curr_win_def simpler_gets_def)
by (simp add: write_reg_def simpler_modify_def)

lemma mul_instr_result: "(fst i) \<in> {arith_type UMUL,arith_type SMUL,
  arith_type SMULcc} \<Longrightarrow>
  snd (mul_instr i s) = False"
apply (simp add: mul_instr_def)
apply (simp add: Let_def)
apply auto
  apply (simp add: mul_instr_sub1_def)
  apply (simp add: write_reg_def simpler_modify_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: get_curr_win_def simpler_gets_def)
  apply (simp add: write_reg_def write_cpu_def simpler_modify_def)
 apply (simp add: mul_instr_sub1_def)
 apply (simp add: simpler_gets_def)
 apply (simp add: write_cpu_def write_reg_def simpler_modify_def)
 apply (simp add: bind_def h1_def h2_def Let_def)
 apply (simp add: get_curr_win_def simpler_gets_def)
apply (simp add: mul_instr_sub1_def)
apply (simp add: simpler_gets_def)
apply (simp add: write_cpu_def write_reg_def simpler_modify_def)
apply (simp add: bind_def h1_def h2_def)
by (simp add: get_curr_win_def simpler_gets_def)

lemma div_write_new_val_result: "snd (div_write_new_val i result temp_V s) = False"
apply (simp add: div_write_new_val_def)
apply (simp add: return_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
by (simp add: write_cpu_def simpler_modify_def)

lemma div_result: "snd (div_comp instr rs1 rd operand2 s) = False"
apply (simp add: div_comp_def)
apply (simp add: simpler_gets_def)
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: get_curr_win_def simpler_gets_def)
by (simp add: div_write_new_val_result)

lemma div_instr_result: "(fst i) \<in> {arith_type UDIV,arith_type UDIVcc,
  arith_type SDIV} \<Longrightarrow>
  snd (div_instr i s) = False"
apply (simp add: div_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: return_def bind_def)
by (simp add: div_result)

lemma load_sub2_result: "snd (load_sub2 address asi rd curr_win word0 s) = False"
apply (simp add: load_sub2_def)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: bind_def h1_def h2_def)
apply (simp add: write_reg_def simpler_modify_def)
by (simp add: simpler_gets_def)

lemma load_sub3_result: "snd (load_sub3 instr curr_win rd asi address s) = False"
apply (simp add: load_sub3_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: case_prod_unfold)
apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
apply (simp add: write_reg_def simpler_modify_def)
apply (simp add: load_sub2_result)
by (simp add: raise_trap_def simpler_modify_def)

lemma load_sub1_result: "snd (load_sub1 i rd s_val s) = False"
apply (simp add: load_sub1_def)
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: get_curr_win_def simpler_gets_def)
by (simp add: load_sub3_result)

lemma load_instr_result: "(fst i) \<in> {load_store_type LDSB,load_store_type LDUB,
  load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
  load_store_type LDA,load_store_type LDD} \<Longrightarrow>
  snd (load_instr i s) = False"
apply (simp add: load_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: return_def)
by (simp add: load_sub1_result)

lemma store_sub2_result: "snd (store_sub2 instr curr_win rd asi address s) = False"
apply (simp add: store_sub2_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: return_def)
apply (simp add: raise_trap_def simpler_modify_def)
by (simp add: bind_def h1_def h2_def)

lemma store_sub1_result: "snd (store_sub1 instr rd s_val s) = False"
apply (simp add: store_sub1_def)
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: get_curr_win_def)
apply (simp add: simpler_gets_def)
by (simp add: store_sub2_result)

lemma store_instr_result: "(fst i) \<in> {load_store_type STB,load_store_type STH,
  load_store_type ST,load_store_type STA,load_store_type STD} \<Longrightarrow>
  snd (store_instr i s) = False"
apply (simp add: store_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: raise_trap_def simpler_modify_def)
apply (simp add: return_def)
by (simp add: store_sub1_result)

lemma supported_instr_set: "supported_instruction i = True \<Longrightarrow> 
  i \<in> {load_store_type LDSB,load_store_type LDUB,load_store_type LDUBA,
              load_store_type LDUH,load_store_type LD,load_store_type LDA,
              load_store_type LDD,
              load_store_type STB,load_store_type STH,load_store_type ST,
              load_store_type STA,load_store_type STD,
              sethi_type SETHI,
              nop_type NOP,
              logic_type ANDs,logic_type ANDcc,logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR,
              shift_type SLL,shift_type SRL,shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              ctrl_type RETT,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
apply (simp add: supported_instruction_def)
by presburger

lemma dispatch_instr_result: 
assumes a1: "supported_instruction (fst i) = True \<and> (fst i) \<noteq> ctrl_type RETT"
shows "snd (dispatch_instruction i s) = False"
proof (cases "get_trap_set s = {}")
  case True
  then have f1: "get_trap_set s = {}" by auto
  then show ?thesis 
  proof (cases "(fst i) \<in> {load_store_type LDSB,load_store_type LDUB,
    load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
    load_store_type LDA,load_store_type LDD}")
    case True
    then show ?thesis using f1 
    apply dispatch_instr_proof1
    by (simp add: load_instr_result)
  next
    case False
    then have f2: "(fst i) \<in> {load_store_type STB,load_store_type STH,load_store_type ST,
              load_store_type STA,load_store_type STD,
              sethi_type SETHI,
              nop_type NOP,
              logic_type ANDs,logic_type ANDcc,logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR,
              shift_type SLL,shift_type SRL,shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
     using a1 
     apply (simp add: supported_instruction_def)
     by presburger
     then show ?thesis 
     proof (cases "(fst i) \<in> {load_store_type STB,load_store_type STH,
       load_store_type ST,
       load_store_type STA,load_store_type STD}")
      case True
      then show ?thesis using f1
      apply dispatch_instr_proof1      
      by (auto simp add: store_instr_result)
     next
      case False
      then have f3: "(fst i) \<in> {sethi_type SETHI,
              nop_type NOP,
              logic_type ANDs,logic_type ANDcc,logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR,
              shift_type SLL,shift_type SRL,shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
      using f2 by auto
      then show ?thesis 
      proof (cases "(fst i) = sethi_type SETHI")
        case True
        then show ?thesis using f1
        apply dispatch_instr_proof1
        by (simp add: sethi_instr_result)
      next
        case False
        then have f4: "(fst i) \<in> {nop_type NOP,
              logic_type ANDs,logic_type ANDcc,logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR,
              shift_type SLL,shift_type SRL,shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
        using f3 by auto         
        then show ?thesis 
        proof (cases "fst i = nop_type NOP")
          case True
          then show ?thesis using f1
          apply dispatch_instr_proof1
          by (simp add: nop_instr_result)
        next
          case False
          then have f5: "(fst i) \<in> {logic_type ANDs,logic_type ANDcc,
              logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR,
              shift_type SLL,shift_type SRL,shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
          using f4 by auto
          then show ?thesis 
          proof (cases "(fst i) \<in> {logic_type ANDs,logic_type ANDcc,
              logic_type ANDN,logic_type ANDNcc,
              logic_type ORs,logic_type ORcc,logic_type ORN,logic_type XORs,
              logic_type XNOR}")
            case True
            then show ?thesis using f1
            apply dispatch_instr_proof1
            by (auto simp add: logical_instr_result)
          next
            case False
            then have f6: "(fst i) \<in> {shift_type SLL,shift_type SRL,
              shift_type SRA,
              arith_type ADD,arith_type ADDcc,arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
            using f5 by auto
            then show ?thesis 
            proof (cases "(fst i) \<in> {shift_type SLL,shift_type SRL,
              shift_type SRA}")
              case True
              then show ?thesis using f1
              apply dispatch_instr_proof1
              by (auto simp add: shift_instr_result)
            next 
              case False
              then have f7: "(fst i) \<in> {arith_type ADD,arith_type ADDcc,
              arith_type ADDX,
              arith_type SUB,arith_type SUBcc,arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}" 
              using f6 by auto
              then show ?thesis 
              proof (cases "(fst i) \<in> {arith_type ADD,arith_type ADDcc,
              arith_type ADDX}")
                case True
                then show ?thesis using f1
                apply dispatch_instr_proof1
                by (auto simp add: add_instr_result)
              next
                case False
                then have f8: "(fst i) \<in> {arith_type SUB,arith_type SUBcc,
                arith_type SUBX,
              arith_type UMUL,arith_type SMUL,arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                using f7 by auto
                then show ?thesis 
                proof (cases "(fst i) \<in> {arith_type SUB,arith_type SUBcc,
                arith_type SUBX}")
                  case True
                  then show ?thesis using f1
                  apply dispatch_instr_proof1
                  by (auto simp add: sub_instr_result)
                next
                  case False
                  then have f9: "(fst i) \<in> {arith_type UMUL,arith_type SMUL,
                  arith_type SMULcc,
              arith_type UDIV,arith_type UDIVcc,arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                  using f8 by auto
                  then show ?thesis 
                  proof (cases "(fst i) \<in> {arith_type UMUL,arith_type SMUL,
                  arith_type SMULcc}")
                    case True
                    then show ?thesis using f1
                    apply dispatch_instr_proof1
                    by (auto simp add: mul_instr_result)
                  next
                    case False
                    then have f10: "(fst i) \<in> {arith_type UDIV,arith_type UDIVcc,
                    arith_type SDIV,
              ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                    using f9 by auto
                    then show ?thesis 
                    proof (cases "(fst i) \<in> {arith_type UDIV,arith_type UDIVcc,
                    arith_type SDIV}")
                      case True
                      then show ?thesis 
                      apply dispatch_instr_proof1 using f1
                      by (auto simp add: div_instr_result)
                    next
                      case False
                      then have f11: "(fst i) \<in> {ctrl_type SAVE,ctrl_type RESTORE,
              call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                      using f10 by auto
                      then show ?thesis 
                      proof (cases "(fst i) \<in> {ctrl_type SAVE,ctrl_type RESTORE}")
                        case True
                        then show ?thesis using f1
                        apply dispatch_instr_proof1 
                        by (auto simp add: save_restore_instr_result)
                      next
                        case False
                        then have f12: "(fst i) \<in> {call_type CALL,
              ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                        using f11 by auto
                        then show ?thesis 
                        proof (cases "(fst i) = call_type CALL")
                          case True
                          then show ?thesis using f1
                          apply dispatch_instr_proof1
                          by (auto simp add: call_instr_result)
                        next
                          case False
                          then have f13: "(fst i) \<in> {ctrl_type JMPL,
              sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                          using f12 by auto
                          then show ?thesis 
                          proof (cases "(fst i) = ctrl_type JMPL")
                            case True
                            then show ?thesis using f1
                            apply dispatch_instr_proof1
                            by (auto simp add: jmpl_instr_result)
                          next
                            case False
                            then have f14: "(fst i) \<in> {
                            sreg_type RDY,
                            sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR,
              sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                            using f13 by auto
                            then show ?thesis 
                            proof (cases "(fst i) \<in> {sreg_type RDY,
                            sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR}")
                              case True
                              then show ?thesis using f1
                              apply dispatch_instr_proof1
                              by (auto simp add: read_state_reg_instr_result)
                            next
                              case False
                              then have f15: "(fst i) \<in> {
                              sreg_type WRY,
                              sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR,
              load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                              using f14 by auto
                              then show ?thesis 
                              proof (cases "(fst i) \<in> {sreg_type WRY,
                              sreg_type WRPSR,sreg_type WRWIM,sreg_type WRTBR}")
                                case True
                                then show ?thesis using f1
                                apply dispatch_instr_proof1
                                by (auto simp add: write_state_reg_instr_result)
                              next
                                case False
                                then have f16: "(fst i) \<in> {
                                load_store_type FLUSH,
              bicc_type BE,bicc_type BNE,bicc_type BGU,bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                                using f15 by auto
                                then show ?thesis 
                                proof (cases "(fst i) = load_store_type FLUSH")
                                  case True
                                  then show ?thesis using f1
                                  apply dispatch_instr_proof1
                                  by (auto simp add: flush_instr_result)
                                next
                                  case False
                                  then have f17: "(fst i) \<in>
                                  {
                                  bicc_type BE,bicc_type BNE,bicc_type BGU,
                                  bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,
              bicc_type BN}"
                                  using f16 by auto
                                  then show ?thesis using f1
                                  proof (cases "(fst i) \<in> {bicc_type BE,
                                    bicc_type BNE,bicc_type BGU,
                                  bicc_type BLE,
              bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
              bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA
              }")
                                    case True
                                    then show ?thesis using f1
                                    apply dispatch_instr_proof1
                                    apply auto
                                               by (auto simp add: branch_instr_result)
                                  next
                                    case False
                                    then have f18: "(fst i) \<in> {bicc_type BN}" 
                                    using f17 by auto
                                    then show ?thesis using f1
                                    apply dispatch_instr_proof1
                                    apply auto
                                    by (auto simp add: branch_instr_result)
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
     qed
  qed
next
  case False
  then show ?thesis
  apply (simp add: dispatch_instruction_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: Let_def)
  by (simp add: returnOk_def return_def)
qed

lemma dispatch_instr_result_rett: 
assumes a1: "(fst i) = ctrl_type RETT \<and> (get_ET (cpu_reg_val PSR s) \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s)) = 0 \<and>
  (bitAND (get_addr (snd i) s) (0b00000000000000000000000000000011::word32)) = 0)"
shows "snd (dispatch_instruction i s) = False"
proof (cases "get_trap_set s = {}")
  case True
  then show ?thesis using a1
  apply (simp add: dispatch_instruction_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (simp add: rett_instr_result)
next
  case False
  then show ?thesis using a1
  apply (simp add: dispatch_instruction_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (simp add: return_def)
qed

lemma execute_instr_sub1_result: "snd (execute_instr_sub1 i s) = False"
proof (cases "get_trap_set s = {} \<and> (fst i) \<in> {call_type CALL,ctrl_type RETT,
  ctrl_type JMPL}")
  case True
  then show ?thesis 
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: write_cpu_def simpler_modify_def)
  apply auto
     by (auto simp add: return_def)
next
  case False
  then show ?thesis
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: write_cpu_def simpler_modify_def)
  by (auto simp add: return_def)
qed

lemma next_match : "snd (execute_instruction () s) = False \<Longrightarrow>
  NEXT s = Some (snd (fst (execute_instruction () s)))"
apply (simp add: NEXT_def)
by (simp add: case_prod_unfold)

lemma exec_ss1 : "\<exists>s'. (execute_instruction () s = (s', False)) \<Longrightarrow> 
  \<exists>s''. (execute_instruction() s = (s'', False))"
proof -
  assume "\<exists>s'. (execute_instruction () s = (s', False))"
  hence "(snd (execute_instruction() s)) = False" 
         by (auto simp add: execute_instruction_def case_prod_unfold)         
  hence "(execute_instruction() s) = 
        ((fst (execute_instruction() s)),False)"
         by (metis (full_types) prod.collapse) 
  hence "\<exists>s''. (execute_instruction() s = (s'', False))" 
        by blast
  thus ?thesis by assumption
qed

lemma exec_ss2 : "snd (execute_instruction() s) = False \<Longrightarrow>
  snd (execute_instruction () s) = False"
proof -
  assume "snd (execute_instruction() s) = False"
  hence "snd (execute_instruction () s) = False" 
    by (auto simp add:execute_instruction_def)
  thus ?thesis by assumption
qed

lemma good_context_1 : "good_context s \<and> s' = s \<and>
  (get_trap_set s') \<noteq> {} \<and> (reset_trap_val s') = False \<and> get_ET (cpu_reg_val PSR s') = 0 
  \<Longrightarrow> False"
proof -
  assume asm: "good_context s \<and> s' = s \<and>
    (get_trap_set s') \<noteq> {} \<and> (reset_trap_val s') = False \<and> get_ET (cpu_reg_val PSR s') = 0"
  then have  "(get_trap_set s') \<noteq> {} \<and> (reset_trap_val s') = False \<and> 
  get_ET (cpu_reg_val PSR s') = 0 \<Longrightarrow> False" 
    by (simp add: good_context_def get_ET_def cpu_reg_val_def) 
  then show ?thesis using asm by auto 
qed

lemma fetch_instr_result_1 : "\<not> (\<exists>e. fetch_instruction s' = Inl e) \<Longrightarrow>
  (\<exists>v. fetch_instruction s' = Inr v)"
by (meson sumE)

lemma fetch_instr_result_2 : "(\<exists>v. fetch_instruction s' = Inr v) \<Longrightarrow>
  \<not> (\<exists>e. fetch_instruction s' = Inl e)"
by force

lemma fetch_instr_result_3 : "(\<exists>e. fetch_instruction s' = Inl e) \<Longrightarrow>
  \<not> (\<exists>v. fetch_instruction s' = Inr v)"
by auto

lemma decode_instr_result_1 : 
"\<not>(\<exists>v2. ((decode_instruction v1)::(Exception list + instruction)) = Inr v2) \<Longrightarrow>
  (\<exists>e. ((decode_instruction v1)::(Exception list + instruction)) = Inl e)"
by (meson sumE)

lemma decode_instr_result_2 : 
"(\<exists>e. ((decode_instruction v1)::(Exception list + instruction)) = Inl e) \<Longrightarrow>
  \<not>(\<exists>v2. ((decode_instruction v1)::(Exception list + instruction)) = Inr v2)"
by force

lemma decode_instr_result_3 : "x = decode_instruction v1 \<and> y = decode_instruction v2 
  \<and> v1 = v2 \<Longrightarrow> x = y"
by auto

lemma decode_instr_result_4 : 
"\<not> (\<exists>e. ((decode_instruction v1)::(Exception list + instruction)) = Inl e) \<Longrightarrow>
  (\<exists>v2. ((decode_instruction v1)::(Exception list + instruction)) = Inr v2)"
by (meson sumE)

lemma good_context_2 : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 fetch_instruction (delayed_pool_write s) = Inr v1  \<and> 
 \<not>(\<exists>v2. (decode_instruction v1::(Exception list + instruction)) = Inr v2) 
 \<Longrightarrow> False"
proof -
  assume "good_context s \<and> 
    fetch_instruction (delayed_pool_write s) = Inr v1 \<and> 
    \<not>(\<exists>v2. ((decode_instruction v1)::(Exception list + instruction)) = Inr v2)"
  hence fact1: "good_context s \<and> 
    fetch_instruction (delayed_pool_write s) = Inr v1 \<and> 
    (\<exists>e. ((decode_instruction v1)::(Exception list + instruction)) = Inl e)" 
    using decode_instr_result_1 by auto
  hence fact2: "\<not>(\<exists>e. fetch_instruction (delayed_pool_write s) = Inl e)" 
    using fetch_instr_result_2 by auto
  then have "fetch_instruction (delayed_pool_write s) = Inr v1 \<and> 
            (\<exists>e. ((decode_instruction v1)::(Exception list + instruction)) = Inl e) 
            \<Longrightarrow> False"
    proof (cases "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
      get_ET (cpu_reg_val PSR s) = 0") 
      case True 
      from this fact1 show ?thesis using good_context_1 by blast
    next
      case False
        then have fact3: "(get_trap_set s) = {} \<or> (reset_trap_val s) \<noteq> False 
        \<or> get_ET (cpu_reg_val PSR s) \<noteq> 0"
          by auto
        then show ?thesis 
          using fact1 decode_instr_result_3
          by (metis (no_types, lifting) good_context_def sum.case(1) sum.case(2))        
    qed
  thus ?thesis using fact1 by auto
qed

lemma good_context_3 : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 s'' = delayed_pool_write s \<and>
 fetch_instruction s'' = Inr v1  \<and> 
 (decode_instruction v1::(Exception list + instruction)) = Inr v2 \<and>
 annul_val s'' = False \<and> supported_instruction (fst v2) = False
 \<Longrightarrow> False"
proof -
  assume asm: "good_context (s::(('a::len0) sparc_state)) \<and> 
  s'' = delayed_pool_write s \<and>
  fetch_instruction s'' = Inr v1  \<and> 
  (decode_instruction v1::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> supported_instruction (fst v2) = False"
  then have "annul_val s'' = False \<and> supported_instruction (fst v2) = False
    \<Longrightarrow> False"
    proof (cases "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
      get_ET (cpu_reg_val PSR s) = 0")
      case True
      from this asm show ?thesis using good_context_1 by blast
    next 
      case False
      then have fact3: "(get_trap_set s) = {} \<or> (reset_trap_val s) \<noteq> False \<or> 
      get_ET (cpu_reg_val PSR s) \<noteq> 0"
        by auto
      thus ?thesis using asm by (auto simp add: good_context_def)
    qed
  thus ?thesis using asm by auto
qed

lemma good_context_4 : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 s'' = delayed_pool_write s \<and>
 fetch_instruction s'' = Inr v1 \<and> 
 ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
 annul_val s'' = False \<and> 
 supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
 (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
 ((ucast (get_S (cpu_reg_val PSR s'')))::word1) = 0
 \<Longrightarrow> False"
proof -
  assume asm: "good_context (s::(('a::len0) sparc_state)) \<and> 
  s'' = delayed_pool_write s \<and>
  fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> 
  supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) = 0"
  then have "(fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) = 0 \<Longrightarrow> False"
    proof (cases "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
      get_ET (cpu_reg_val PSR s) = 0")
      case True
      from this asm show ?thesis using good_context_1 by blast
    next 
      case False
      then have fact3: "(get_trap_set s) = {} \<or> (reset_trap_val s) \<noteq> False \<or> 
      get_ET (cpu_reg_val PSR s) \<noteq> 0"
        by auto
      thus ?thesis using asm by (auto simp add: good_context_def)
    qed
  thus ?thesis using asm by auto
qed

lemma good_context_5 : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 s'' = delayed_pool_write s \<and>
 fetch_instruction s'' = Inr v1 \<and> 
 ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
 annul_val s'' = False \<and> 
 supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
 (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
 ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
 (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
  (cpu_reg_val WIM s'')) \<noteq> 0
 \<Longrightarrow> False"
proof -
  assume asm: "good_context (s::(('a::len0) sparc_state)) \<and> 
  s'' = delayed_pool_write s \<and>
  fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> 
  supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) \<noteq> 0"
  then have "(fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) \<noteq> 0
  \<Longrightarrow> False"
    proof (cases "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
      get_ET (cpu_reg_val PSR s) = 0")
      case True
      from this asm show ?thesis using good_context_1 by blast
    next 
      case False
      then have fact3: "(get_trap_set s) = {} \<or> (reset_trap_val s) \<noteq> False \<or>
      get_ET (cpu_reg_val PSR s) \<noteq> 0"
        by auto
      thus ?thesis using asm by (auto simp add: good_context_def)
    qed
  thus ?thesis using asm by auto
qed

lemma good_context_6 : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 s'' = delayed_pool_write s \<and>
 fetch_instruction s'' = Inr v1 \<and> 
 ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
 annul_val s'' = False \<and> 
 supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
 (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
 ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
 (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
  (cpu_reg_val WIM s'')) = 0 \<and>
 (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) \<noteq> 0
 \<Longrightarrow> False"
proof -
  assume asm: "good_context (s::(('a::len0) sparc_state)) \<and> 
  s'' = delayed_pool_write s \<and>
  fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> 
  supported_instruction (fst v2) = True \<and> \<comment> \<open>This line is redundant\<close>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) = 0 \<and>
  (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) \<noteq> 0"
  then have "(fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) = 0 \<and>
  (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) \<noteq> 0
  \<Longrightarrow> False"
    proof (cases "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
      get_ET (cpu_reg_val PSR s) = 0")
      case True
      from this asm show ?thesis using good_context_1 by blast
    next 
      case False
      then have fact3: "(get_trap_set s) = {} \<or> (reset_trap_val s) \<noteq> False \<or>
      get_ET (cpu_reg_val PSR s) \<noteq> 0"
        by auto
      thus ?thesis using asm by (auto simp add: good_context_def)
    qed
  thus ?thesis using asm by auto
qed

lemma good_context_all : 
"good_context (s::(('a::len0) sparc_state)) \<and> 
 s'' = delayed_pool_write s \<Longrightarrow>
 (get_trap_set s = {} \<or> (reset_trap_val s) \<noteq> False \<or> get_ET (cpu_reg_val PSR s) \<noteq> 0) \<and>
 ((\<exists>e. fetch_instruction s'' = Inl e) \<or> 
  (\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
   ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
   (annul_val s'' = True \<or>
    (annul_val s'' = False \<and> 
     (\<forall>v1' v2'. fetch_instruction s'' = Inr v1' \<and> 
      ((decode_instruction v1')::(Exception list + instruction)) = Inr v2' \<longrightarrow>
      supported_instruction (fst v2') = True) \<and>
     ((fst v2) \<noteq> ctrl_type RETT \<or>
      ((fst v2) = ctrl_type RETT \<and> 
       (get_ET (cpu_reg_val PSR s'') = 1 \<or>
        (get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
        ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
        (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
          (cpu_reg_val WIM s'')) = 0 \<and>
        (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) = 0))))))))"
proof -
 assume asm: "good_context s \<and> s'' = delayed_pool_write s"
 from asm have "(get_trap_set s) \<noteq> {} \<and> (reset_trap_val s) = False \<and> 
 get_ET (cpu_reg_val PSR s) = 0 \<Longrightarrow> False"
  using good_context_1 by blast  
 hence fact1: "(get_trap_set s = {} \<or> (reset_trap_val s) \<noteq> False \<or> 
 get_ET (cpu_reg_val PSR s) \<noteq> 0)" by auto
 have fact2: "\<not>(\<exists>e. fetch_instruction s'' = Inl e) \<and> \<not> (\<exists>v1. fetch_instruction s'' = Inr v1) 
  \<Longrightarrow> False" using fetch_instr_result_1 by blast
 from asm have fact3: "\<exists>v1. fetch_instruction s'' = Inr v1 \<and>
  \<not>(\<exists>v2.((decode_instruction v1)::(Exception list + instruction)) = Inr v2)
  \<Longrightarrow> False"
  using good_context_2 by blast
 from asm have fact4: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> supported_instruction (fst v2) = False
  \<Longrightarrow> False"
  using good_context_3 by blast
 from asm have fact5: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> supported_instruction (fst v2) = True \<and>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) = 0
  \<Longrightarrow> False"
  using good_context_4 by blast
 from asm have fact6: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> supported_instruction (fst v2) = True \<and>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) \<noteq> 0
  \<Longrightarrow> False" 
  using good_context_5 by blast
 from asm have fact7: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
  ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
  annul_val s'' = False \<and> supported_instruction (fst v2) = True \<and>
  (fst v2) = ctrl_type RETT \<and> get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and>
  ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0 \<and>
  (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) mod NWINDOWS)) 
    (cpu_reg_val WIM s'')) = 0 \<and>
  (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) \<noteq> 0
  \<Longrightarrow> False"
    using good_context_6 by blast
 from asm show ?thesis 
  proof (cases "(\<exists>e. fetch_instruction s'' = Inl e)")
    case True
    then show ?thesis using fact1 by auto
  next 
    case False
    then have fact8: "\<exists>v1. fetch_instruction s'' = Inr v1 \<and> 
    (\<exists>v2.((decode_instruction v1)::(Exception list + instruction)) = Inr v2)"
      using fact2 fact3 by auto
    then show ?thesis 
      proof (cases "annul_val s'' = True")
        case True
        then show ?thesis using fact1 fact8 by auto
      next 
        case False
        then have fact9: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
        ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
        annul_val s'' = False \<and> supported_instruction (fst v2) = True"
          using fact4 fact8 by blast
        then show ?thesis 
          proof (cases "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
            (fst v2) \<noteq> ctrl_type RETT")
            case True
            then show ?thesis using fact1 fact9 by auto  
          next
            case False
            then have fact10: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
            annul_val s'' = False \<and> supported_instruction (fst v2) = True \<and> 
              (fst v2) = ctrl_type RETT"
              using fact9 by auto
            then show ?thesis 
              proof (cases "get_ET (cpu_reg_val PSR s'') = 1")
                case True
                then show ?thesis using fact1 fact9 by auto
              next
                case False
                then have fact11: "get_ET (cpu_reg_val PSR s'') \<noteq> 1 \<and> 
                ((ucast (get_S (cpu_reg_val PSR s'')))::word1) \<noteq> 0"
                  using fact10 fact5 by auto
                then have fact12: "(get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR s''))) + 1) 
                  mod NWINDOWS)) (cpu_reg_val WIM s'')) = 0" 
                  using fact10 fact6 by auto
                then have fact13: "\<exists>v1 v2. fetch_instruction s'' = Inr v1 \<and> 
                ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
                (bitAND (get_addr (snd v2) s'') (0b00000000000000000000000000000011::word32)) = 0"
                  using fact10 fact11 fact7 by blast
                thus ?thesis using fact1 fact10 fact11 fact12 by auto
              qed
          qed
      qed
  qed
qed

lemma select_trap_result1 : "(reset_trap_val s) = True \<Longrightarrow>
  snd (select_trap() s) = False"   
apply (simp add: select_trap_def exec_gets return_def)
by (simp add: bind_def  h1_def h2_def simpler_modify_def)

lemma select_trap_result2 : 
assumes a1: "\<not>(reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) = 0)"
shows  "snd (select_trap() s) = False"
proof (cases "reset_trap_val s = True") 
  case True
  then show ?thesis using select_trap_result1 
  by blast
next
  case False
  then have f1: "reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) \<noteq> 0"
    using a1 by auto
    then show ?thesis
    proof (cases "data_store_error \<in> get_trap_set s")
      case True
      then show ?thesis using f1
      by select_trap_proof0
    next
      case False
      then have f2: "data_store_error \<notin> get_trap_set s" by auto
      then show ?thesis 
      proof (cases "instruction_access_error \<in> get_trap_set s")
        case True
        then show ?thesis using f1 f2
        by select_trap_proof0
      next
        case False
        then have f3: "instruction_access_error \<notin> get_trap_set s" by auto
        then show ?thesis 
        proof (cases "r_register_access_error \<in> get_trap_set s")
          case True
          then show ?thesis using f1 f2 f3
          by select_trap_proof0
        next
          case False
          then have f4: "r_register_access_error \<notin> get_trap_set s" by auto
          then show ?thesis 
          proof (cases "instruction_access_exception \<in> get_trap_set s")
            case True
            then show ?thesis using f1 f2 f3 f4
            by select_trap_proof0
          next
            case False
            then have f5: "instruction_access_exception \<notin> get_trap_set s" by auto
            then show ?thesis 
            proof (cases "privileged_instruction \<in> get_trap_set s")
              case True
              then show ?thesis using f1 f2 f3 f4 f5
              by select_trap_proof0
            next  
              case False
              then have f6: "privileged_instruction \<notin> get_trap_set s" by auto
              then show ?thesis 
              proof (cases "illegal_instruction \<in> get_trap_set s")
                case True
                then show ?thesis using f1 f2 f3 f4 f5 f6
                by select_trap_proof0
              next
                case False
                then have f7: "illegal_instruction \<notin> get_trap_set s" by auto
                then show ?thesis
                proof (cases "fp_disabled \<in> get_trap_set s")
                  case True
                  then show ?thesis using f1 f2 f3 f4 f5 f6 f7
                  by select_trap_proof0
                next
                  case False
                  then have f8: "fp_disabled \<notin> get_trap_set s" by auto
                  then show ?thesis 
                  proof (cases "cp_disabled \<in> get_trap_set s")
                    case True
                    then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8
                    by select_trap_proof0
                  next
                    case False
                    then have f9: "cp_disabled \<notin> get_trap_set s" by auto
                    then show ?thesis 
                    proof (cases "unimplemented_FLUSH \<in> get_trap_set s")
                      case True
                      then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9
                      by select_trap_proof0
                    next
                      case False
                      then have f10: "unimplemented_FLUSH \<notin> get_trap_set s" by auto
                      then show ?thesis 
                      proof (cases "window_overflow \<in> get_trap_set s")
                        case True
                        then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
                        by select_trap_proof0
                      next 
                        case False
                        then have f11: "window_overflow \<notin> get_trap_set s" by auto
                        then show ?thesis 
                        proof (cases "window_underflow \<in> get_trap_set s")
                          case True
                          then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
                          by select_trap_proof0
                        next
                          case False
                          then have f12: "window_underflow \<notin> get_trap_set s" by auto
                          then show ?thesis 
                          proof (cases "mem_address_not_aligned \<in> get_trap_set s")
                            case True
                            then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
                            by select_trap_proof0
                          next
                            case False
                            then have f13: "mem_address_not_aligned \<notin> get_trap_set s" by auto
                            then show ?thesis 
                            proof (cases "fp_exception \<in> get_trap_set s")
                              case True
                              then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                              by select_trap_proof0
                            next
                              case False
                              then have f14: "fp_exception \<notin> get_trap_set s" by auto
                              then show ?thesis 
                              proof (cases "cp_exception \<in> get_trap_set s")
                                case True
                                then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                f14 
                                by select_trap_proof0
                              next
                                case False
                                then have f15: "cp_exception \<notin> get_trap_set s" by auto
                                then show ?thesis 
                                proof (cases "data_access_error \<in> get_trap_set s")
                                  case True
                                  then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                f14 f15 
                                by select_trap_proof0
                                next
                                  case False
                                  then have f16: "data_access_error \<notin> get_trap_set s" by auto
                                  then show ?thesis 
                                  proof (cases "data_access_exception \<in> get_trap_set s")
                                    case True
                                    then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                    f13 f14 f15 f16
                                    by select_trap_proof0
                                  next
                                    case False
                                    then have f17: "data_access_exception \<notin> get_trap_set s" by auto
                                    then show ?thesis 
                                    proof (cases "tag_overflow \<in> get_trap_set s")
                                      case True
                                      then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                      f13 f14 f15 f16 f17
                                      by select_trap_proof0
                                    next
                                      case False
                                      then have f18: "tag_overflow \<notin> get_trap_set s" by auto
                                      then show ?thesis 
                                      proof (cases "division_by_zero \<in> get_trap_set s")
                                        case True
                                        then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                        f12 f13 f14 f15 f16 f17 f18 
                                        by select_trap_proof0
                                      next
                                        case False
                                        then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                        f12 f13 f14 f15 f16 f17 f18
                                        apply (simp add: select_trap_def exec_gets return_def)
                                        apply (simp add: DetMonad.bind_def h1_def h2_def simpler_modify_def)
                                        apply (simp add: return_def simpler_gets_def)
                                        apply (simp add: case_prod_unfold)
                                        apply (simp add: return_def)
                                        apply (simp add: write_cpu_tt_def write_cpu_def)
                                        by (simp add: simpler_gets_def bind_def h1_def h2_def simpler_modify_def)
                                      qed
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
qed

lemma emp_trap_set_err_mode : "err_mode_val s = err_mode_val (emp_trap_set s)"
by (auto simp add: emp_trap_set_def err_mode_val_def)

lemma write_cpu_tt_err_mode : "err_mode_val s = err_mode_val (snd (fst (write_cpu_tt w s)))"
apply (simp add: write_cpu_tt_def err_mode_val_def write_cpu_def)  
apply (simp add: exec_gets return_def)
apply (simp add: bind_def simpler_modify_def)
by (simp add: cpu_reg_mod_def)

lemma select_trap_monad : "snd (select_trap() s) = False \<Longrightarrow> 
  err_mode_val s = err_mode_val (snd (fst (select_trap () s)))"
proof -
  assume a1: "snd (select_trap() s) = False"
  then have f0: "reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) = 0 \<Longrightarrow> False" 
    apply (simp add: select_trap_def exec_gets return_def)
    apply (simp add: bind_def h1_def h2_def simpler_modify_def)
    by (simp add: fail_def split_def)  
  then show ?thesis
    proof (cases "reset_trap_val s = True")
      case True
      from a1 f0 this show ?thesis 
      apply (simp add: select_trap_def exec_gets return_def)
      apply (simp add: bind_def h1_def h2_def simpler_modify_def)
      by (simp add: emp_trap_set_def err_mode_val_def)
    next
      case False
      then have f1: "reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) \<noteq> 0" using f0 by auto
      then show ?thesis using f1 a1
      proof (cases "data_store_error \<in> get_trap_set s")
        case True
        then show ?thesis using f1 a1
        by select_trap_proof1
      next 
        case False
        then have f2: "data_store_error \<notin> get_trap_set s" by auto
        then show ?thesis 
        proof (cases "instruction_access_error \<in> get_trap_set s")
          case True
          then show ?thesis using f1 f2 a1
          by select_trap_proof1
        next
          case False
          then have f3: "instruction_access_error \<notin> get_trap_set s" by auto
          then show ?thesis 
          proof (cases "r_register_access_error \<in> get_trap_set s")
            case True
            then show ?thesis using f1 f2 f3 a1
            by select_trap_proof1
          next
            case False
            then have f4: "r_register_access_error \<notin> get_trap_set s" by auto
            then show ?thesis 
            proof (cases "instruction_access_exception \<in> get_trap_set s")
              case True
              then show ?thesis using f1 f2 f3 f4 a1
              by select_trap_proof1
            next
              case False
              then have f5: "instruction_access_exception \<notin> get_trap_set s" by auto
              then show ?thesis 
              proof (cases "privileged_instruction \<in> get_trap_set s")
                case True
                then show ?thesis using f1 f2 f3 f4 f5 a1
                by select_trap_proof1
              next  
                case False
                then have f6: "privileged_instruction \<notin> get_trap_set s" by auto
                then show ?thesis 
                proof (cases "illegal_instruction \<in> get_trap_set s")
                  case True
                  then show ?thesis using f1 f2 f3 f4 f5 f6 a1
                  by select_trap_proof1
                next
                  case False
                  then have f7: "illegal_instruction \<notin> get_trap_set s" by auto
                  then show ?thesis
                  proof (cases "fp_disabled \<in> get_trap_set s")
                    case True
                    then show ?thesis using f1 f2 f3 f4 f5 f6 f7 a1
                    by select_trap_proof1
                  next
                    case False
                    then have f8: "fp_disabled \<notin> get_trap_set s" by auto
                    then show ?thesis 
                    proof (cases "cp_disabled \<in> get_trap_set s")
                      case True
                      then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 a1
                      by select_trap_proof1
                    next
                      case False
                      then have f9: "cp_disabled \<notin> get_trap_set s" by auto
                      then show ?thesis 
                      proof (cases "unimplemented_FLUSH \<in> get_trap_set s")
                        case True
                        then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 a1
                        by select_trap_proof1
                      next
                        case False
                        then have f10: "unimplemented_FLUSH \<notin> get_trap_set s" by auto
                        then show ?thesis 
                        proof (cases "window_overflow \<in> get_trap_set s")
                          case True
                          then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 a1
                          by select_trap_proof1
                        next 
                          case False
                          then have f11: "window_overflow \<notin> get_trap_set s" by auto
                          then show ?thesis 
                          proof (cases "window_underflow \<in> get_trap_set s")
                            case True
                            then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 a1
                            by select_trap_proof1
                          next
                            case False
                            then have f12: "window_underflow \<notin> get_trap_set s" by auto
                            then show ?thesis 
                            proof (cases "mem_address_not_aligned \<in> get_trap_set s")
                              case True
                              then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 a1
                              by select_trap_proof1
                            next
                              case False
                              then have f13: "mem_address_not_aligned \<notin> get_trap_set s" by auto
                              then show ?thesis 
                              proof (cases "fp_exception \<in> get_trap_set s")
                                case True
                                then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                a1
                                by select_trap_proof1
                              next
                                case False
                                then have f14: "fp_exception \<notin> get_trap_set s" by auto
                                then show ?thesis 
                                proof (cases "cp_exception \<in> get_trap_set s")
                                  case True
                                  then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                  f14 a1
                                  by select_trap_proof1
                                next
                                  case False
                                  then have f15: "cp_exception \<notin> get_trap_set s" by auto
                                  then show ?thesis 
                                  proof (cases "data_access_error \<in> get_trap_set s")
                                    case True
                                    then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                    f14 f15 a1
                                    by select_trap_proof1
                                  next
                                    case False
                                    then have f16: "data_access_error \<notin> get_trap_set s" by auto
                                    then show ?thesis 
                                    proof (cases "data_access_exception \<in> get_trap_set s")
                                      case True
                                      then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                      f13 f14 f15 f16 a1
                                      by select_trap_proof1
                                    next
                                      case False
                                      then have f17: "data_access_exception \<notin> get_trap_set s" by auto
                                      then show ?thesis 
                                      proof (cases "tag_overflow \<in> get_trap_set s")
                                        case True
                                        then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                        f13 f14 f15 f16 f17 a1
                                        by select_trap_proof1
                                      next
                                        case False
                                        then have f18: "tag_overflow \<notin> get_trap_set s" by auto
                                        then show ?thesis 
                                        proof (cases "division_by_zero \<in> get_trap_set s")
                                          case True
                                          then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                          f12 f13 f14 f15 f16 f17 f18 a1
                                          by select_trap_proof1
                                        next
                                          case False
                                          then show ?thesis using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                          f12 f13 f14 f15 f16 f17 f18 a1
                                          apply (simp add: select_trap_def exec_gets return_def)
                                          apply (simp add: bind_def h1_def h2_def simpler_modify_def)
                                          apply (simp add: return_def simpler_gets_def)
                                          apply (simp add: emp_trap_set_def err_mode_val_def
                                            cpu_reg_mod_def)
                                          apply (simp add: case_prod_unfold)
                                          apply (simp add: return_def)
                                          apply clarsimp                                          
                                          apply (simp add: write_cpu_tt_def write_cpu_def write_tt_def)
                                          apply (simp add: simpler_gets_def bind_def h1_def h2_def)
                                          apply (simp add: simpler_modify_def)
                                          by (simp add: cpu_reg_val_def cpu_reg_mod_def)
                                        qed
                                      qed
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
qed

lemma exe_trap_st_pc_result : "snd (exe_trap_st_pc() s) = False"
proof (cases "annul_val s = True")
  case True
  then show ?thesis 
  apply (simp add: exe_trap_st_pc_def get_curr_win_def)
  apply (simp add: exec_gets return_def)
  apply (simp add: DetMonad.bind_def h1_def h2_def)
  by (simp add: set_annul_def write_reg_def simpler_modify_def)
next
  case False
  then show ?thesis
  apply (simp add: exe_trap_st_pc_def get_curr_win_def)
  apply (simp add: exec_gets return_def)
  apply (simp add: DetMonad.bind_def h1_def h2_def)
  by (simp add: write_reg_def simpler_modify_def)
qed

lemma exe_trap_wr_pc_result : "snd (exe_trap_wr_pc() s) = False"
proof (cases "reset_trap_val s = True")
  case True
  then show ?thesis 
  apply (simp add: exe_trap_wr_pc_def get_curr_win_def)
  apply (simp add: exec_gets return_def)
  apply (simp add: DetMonad.bind_def h1_def h2_def)
  apply (simp add: write_cpu_def simpler_modify_def)
  apply (simp add: simpler_gets_def)
  apply (simp add: cpu_reg_val_def update_S_def cpu_reg_mod_def reset_trap_val_def)
  apply (simp add: write_cpu_def simpler_modify_def DetMonad.bind_def h1_def h2_def)
  apply (simp add: return_def)
  by (simp add: set_reset_trap_def simpler_modify_def DetMonad.bind_def h1_def h2_def return_def)
next
  case False
  then show ?thesis
  apply (simp add: exe_trap_wr_pc_def get_curr_win_def)
  apply (simp add: exec_gets return_def)
  apply (simp add: DetMonad.bind_def h1_def h2_def)
  apply (simp add: write_cpu_def simpler_modify_def)
  apply (simp add: simpler_gets_def)
  apply (simp add: cpu_reg_val_def update_S_def cpu_reg_mod_def reset_trap_val_def)
  apply (simp add: write_cpu_def simpler_modify_def DetMonad.bind_def h1_def h2_def)
  by (simp add: return_def)
qed

lemma execute_trap_result : "\<not>(reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) = 0) \<Longrightarrow>
  snd (execute_trap() s) = False"
proof -
  assume "\<not>(reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) = 0)"
  then have fact1: "snd (select_trap() s) = False" using select_trap_result2 by blast
  then show ?thesis 
    proof (cases "err_mode_val s = True")
      case True
      then show ?thesis using fact1 
        apply (simp add: execute_trap_def exec_gets return_def)
        apply (simp add: DetMonad.bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        by (simp add: in_gets return_def select_trap_monad simpler_gets_def)
    next 
      case False
      then show ?thesis using fact1 select_trap_monad
      apply (simp add: execute_trap_def exec_gets return_def)
      apply (simp add: DetMonad.bind_def h1_def h2_def)
      apply (simp add: case_prod_unfold)
      apply (simp add: simpler_gets_def)
      apply (auto simp add: select_trap_monad)
      apply (simp add: DetMonad.bind_def h1_def h2_def get_curr_win_def)
      apply (simp add: get_CWP_def cpu_reg_val_def)
      apply (simp add: simpler_gets_def return_def write_cpu_def)
      apply (simp add: simpler_modify_def DetMonad.bind_def h1_def h2_def)
      apply (simp add: exe_trap_st_pc_result)
      by (simp add: case_prod_unfold exe_trap_wr_pc_result)
    qed
qed

lemma execute_trap_result2 : "\<not>(reset_trap_val s = False \<and> get_ET (cpu_reg_val PSR s) = 0) \<Longrightarrow>
  snd (execute_trap() s) = False"
using execute_trap_result
by blast

lemma exe_instr_all : 
"good_context (s::(('a::len0) sparc_state)) \<Longrightarrow> 
  snd (execute_instruction() s) = False"
proof -
  assume asm1: "good_context s"
  let ?s' = "delayed_pool_write s"
  from asm1 have f1 : "(get_trap_set s = {} \<or> (reset_trap_val s) \<noteq> False \<or> 
  get_ET (cpu_reg_val PSR s) \<noteq> 0) \<and>
  ((\<exists>e. fetch_instruction ?s' = Inl e) \<or> 
  (\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
   ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
   (annul_val ?s' = True \<or>
    (annul_val ?s' = False \<and> 
     (\<forall>v1' v2'. fetch_instruction ?s' = Inr v1' \<and> 
      ((decode_instruction v1')::(Exception list + instruction)) = Inr v2' \<longrightarrow>
      supported_instruction (fst v2') = True) \<and>
     ((fst v2) \<noteq> ctrl_type RETT \<or>
      ((fst v2) = ctrl_type RETT \<and> 
       (get_ET (cpu_reg_val PSR ?s') = 1 \<or>
        (get_ET (cpu_reg_val PSR ?s') \<noteq> 1 \<and>
        ((ucast (get_S (cpu_reg_val PSR ?s')))::word1) \<noteq> 0 \<and>
        (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR ?s'))) + 1) mod NWINDOWS)) 
          (cpu_reg_val WIM ?s')) = 0 \<and>
        (bitAND (get_addr (snd v2) ?s') (0b00000000000000000000000000000011::word32)) = 0))))))))"
       using good_context_all by blast
   from f1 have f2: "get_trap_set s \<noteq> {} \<Longrightarrow> 
   (reset_trap_val s) \<noteq> False \<or> get_ET (cpu_reg_val PSR s) \<noteq> 0" 
    by auto
   show ?thesis 
   proof (cases "get_trap_set s = {}")
    case True
    then have f3: "get_trap_set s = {}" by auto
    then show ?thesis
    proof (cases "exe_mode_val s = True")
      case True
      then have f4: "exe_mode_val s = True" by auto
      then show ?thesis 
      proof (cases "\<exists>e1. fetch_instruction ?s' = Inl e1")
        case True
        then show ?thesis using f3
        apply exe_proof_to_decode
        apply (simp add: raise_trap_def simpler_modify_def)
        by (simp add: bind_def h1_def h2_def return_def)
      next
        case False
        then have f5: "\<exists> v1. fetch_instruction ?s' = Inr v1" using fetch_instr_result_1 by blast
        then have f6: "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
          ((decode_instruction v1)::(Exception list + instruction)) = Inr v2"
        using f1 fetch_instr_result_2 by blast
        then show ?thesis 
        proof (cases "annul_val ?s' = True")
          case True
          then show ?thesis using f3 f4 f6
          apply exe_proof_to_decode
          apply (simp add: set_annul_def annul_mod_def simpler_modify_def bind_def h1_def h2_def)
          apply (simp add: return_def simpler_gets_def)
          by (simp add: write_cpu_def simpler_modify_def)
        next
          case False
          then have f7: "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
          ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and> 
          (\<forall>v1' v2'. fetch_instruction ?s' = Inr v1' \<and> 
          ((decode_instruction v1')::(Exception list +  instruction)) = Inr v2' \<longrightarrow>
          supported_instruction (fst v2') = True) \<and> annul_val ?s' = False"
          using f1 f6 fetch_instr_result_2 by auto
          then have f7': "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
          ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and> 
          supported_instruction (fst v2) = True \<and> annul_val ?s' = False"
          by auto
          then show ?thesis 
          proof (cases "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
          ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and> 
          (fst v2) = ctrl_type RETT")
            case True
            then have f8: "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and> 
            (fst v2) = ctrl_type RETT" by auto
            then show ?thesis 
            proof (cases "get_trap_set ?s' = {}")
              case True
              then have f9: "get_trap_set ?s' = {}" by auto
              then show ?thesis 
              proof (cases "get_ET (cpu_reg_val PSR ?s') = 1")
                case True
                then have f10: "get_ET (cpu_reg_val PSR ?s') = 1" by auto
                then show ?thesis 
                proof (cases "((ucast (get_S (cpu_reg_val PSR ?s')))::word1) = 0")
                  case True
                  then show ?thesis using f3 f4 f7 f8 f9 f10
                  apply exe_proof_to_decode              
                  apply exe_proof_dispatch_rett
                  apply (simp add: raise_trap_def simpler_modify_def)
                  apply (auto simp add: execute_instr_sub1_result return_def)
                  by (simp add: case_prod_unfold)
                next
                  case False
                  then show ?thesis using f3 f4 f7 f8 f9 f10
                  apply exe_proof_to_decode
                  apply exe_proof_dispatch_rett
                  apply (simp add: raise_trap_def simpler_modify_def)
                  apply (auto simp add: execute_instr_sub1_result return_def)
                  by (simp add: case_prod_unfold)
                qed
              next
                case False
                then have f11: "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
                ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
                annul_val ?s' = False \<and>
                (fst v2) = ctrl_type RETT \<and>
                (get_ET (cpu_reg_val PSR ?s') \<noteq> 1 \<and>
                ((ucast (get_S (cpu_reg_val PSR ?s')))::word1) \<noteq> 0 \<and>
                (get_WIM_bit (nat (((uint (get_CWP (cpu_reg_val PSR ?s'))) + 1) mod NWINDOWS)) 
                  (cpu_reg_val WIM ?s')) = 0 \<and>
                (bitAND (get_addr (snd v2) ?s') (0b00000000000000000000000000000011::word32)) = 0)"
                using f1 fetch_instr_result_2 f7' f8 by auto
                then show ?thesis using f3 f4
                proof (cases "get_trap_set ?s' = {}")
                  case True
                  then show ?thesis using f3 f4 f11
                  apply (simp add: execute_instruction_def)
                  apply (simp add: simpler_gets_def bind_def h1_def h2_def simpler_modify_def)
                  apply clarsimp
                  apply (simp add: return_def)
                  apply (simp add: bind_def h1_def h2_def Let_def)
                  apply (simp add: case_prod_unfold)   
                  apply auto
                   apply (simp add: execute_instr_sub1_result)                
                  apply (simp add: dispatch_instruction_def)
                  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)  
                  by (simp add: rett_instr_result)
                next
                  case False
                  then show ?thesis using f3 f4 f11
                  apply (simp add: execute_instruction_def)
                  apply (simp add: simpler_gets_def bind_def h1_def h2_def simpler_modify_def)
                  apply clarsimp
                  apply (simp add: return_def)
                  apply (simp add: bind_def h1_def h2_def)
                  apply (simp add: case_prod_unfold)   
                  apply (simp add: execute_instr_sub1_result)
                  apply (simp add: dispatch_instruction_def)
                  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
                  by (simp add: return_def)
                qed             
              qed
            next
              case False
              then show ?thesis using f3 f4 f7 f8
              apply exe_proof_to_decode
              apply (simp add: dispatch_instruction_def)
              apply (simp add: simpler_gets_def bind_def h1_def h2_def)
              apply (simp add: case_prod_unfold)
              by (auto simp add: execute_instr_sub1_result return_def Let_def)
            qed
          next
            case False \<comment> \<open>Instruction is not \<open>RETT\<close>.\<close>
            then have "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and> 
            (fst v2) \<noteq> ctrl_type RETT" using f7 by auto
            then have "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
            (fst v2) \<noteq> ctrl_type RETT \<and>
            supported_instruction (fst v2) = True \<and> annul_val ?s' = False"
            using f7 by auto            
            then have "\<exists>v1 v2. fetch_instruction ?s' = Inr v1 \<and> 
            ((decode_instruction v1)::(Exception list + instruction)) = Inr v2 \<and>
            (fst v2) \<noteq> ctrl_type RETT \<and>
            supported_instruction (fst v2) = True \<and> annul_val ?s' = False \<and>
            snd (dispatch_instruction v2 ?s') = False"
            by (auto simp add: dispatch_instr_result)                   
            then show ?thesis using f3 f4
              apply exe_proof_to_decode
              apply (simp add: bind_def h1_def h2_def)
              apply (simp add: case_prod_unfold)
              by (simp add: execute_instr_sub1_result)            
          qed
        qed
      qed
    next
      case False
      then show ?thesis using f3
      apply (simp add: execute_instruction_def)
      by (simp add: exec_gets return_def)
    qed
   next
    case False
    then have "get_trap_set s \<noteq> {} \<and> 
    ((reset_trap_val s) \<noteq> False \<or> get_ET (cpu_reg_val PSR s) \<noteq> 0)" 
      using f2 by auto
    then show ?thesis
    apply (simp add: execute_instruction_def exec_gets)
    by (simp add: execute_trap_result2)
   qed
qed

lemma dispatch_fail: 
"snd (execute_instruction() (s::(('a::len0) sparc_state))) = False \<and>
  get_trap_set s = {} \<and>
  exe_mode_val s \<and>
  fetch_instruction (delayed_pool_write s) = Inr v  \<and> 
  ((decode_instruction v)::(Exception list + instruction)) = Inl e
 \<Longrightarrow> False"
using decode_instr_result_2
apply (simp add: execute_instruction_def)
apply (simp add: exec_gets bind_def)
apply clarsimp
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: simpler_modify_def return_def)
by (simp add: fail_def)

lemma no_error : "good_context s \<Longrightarrow> snd (execute_instruction () s) = False"
proof -
  assume "good_context s"
  hence "snd (execute_instruction() s) = False" 
    using exe_instr_all by auto
  hence "snd (execute_instruction () s) = False" by (simp add: exec_ss2)
  thus ?thesis by assumption
qed

theorem single_step : "good_context s \<Longrightarrow> NEXT s = Some (snd (fst (execute_instruction () s)))"
by (simp add: no_error next_match)

(*********************************************************************)

section \<open>Privilege safty\<close>

(*********************************************************************)

text \<open>The following shows that, if the pre-state is under user mode,
  then after a singel step execution, the post-state is aslo under user mode.\<close>

lemma write_cpu_pc_privilege: "s' = snd (fst (write_cpu w PC s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: cpu_reg_mod_def)
by (simp add: cpu_reg_val_def)

lemma write_cpu_npc_privilege: "s' = snd (fst (write_cpu w nPC s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: cpu_reg_mod_def)
by (simp add: cpu_reg_val_def)

lemma write_cpu_y_privilege: "s' = snd (fst (write_cpu w Y s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: cpu_reg_mod_def)
by (simp add: cpu_reg_val_def)

lemma cpu_reg_mod_y_privilege: "s' = cpu_reg_mod w Y s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
by (simp add: cpu_reg_mod_def cpu_reg_val_def)

lemma cpu_reg_mod_asr_privilege: "s' = cpu_reg_mod w (ASR r) s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
by (simp add: cpu_reg_mod_def cpu_reg_val_def)

lemma global_reg_mod_privilege: "s' = global_reg_mod w1 n w2 s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (induction n arbitrary:s)
 apply (clarsimp)
apply (auto)
apply (simp add: Let_def)
by (simp add: cpu_reg_val_def)

lemma out_reg_mod_privilege: "s' = out_reg_mod a w r s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: out_reg_mod_def Let_def)
by (simp add: cpu_reg_val_def)

lemma in_reg_mod_privilege: "s' = in_reg_mod a w r s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: in_reg_mod_def Let_def)
by (simp add: cpu_reg_val_def)

lemma user_reg_mod_privilege: 
assumes a1: " s' = user_reg_mod d (w::(('a::len0) window_size)) r 
  (s::(('a::len0) sparc_state)) \<and> 
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "r = 0")
  case True
  then show ?thesis using a1
  by (simp add: user_reg_mod_def)  
next
  case False
  then have f1: "r \<noteq> 0" by auto
  then show ?thesis
  proof (cases "0 < r \<and> r < 8")
    case True
    then show ?thesis using a1 f1
    apply (simp add: user_reg_mod_def)
    by (auto intro: global_reg_mod_privilege)
  next
    case False
    then have f2: "\<not>(0 < r \<and> r < 8)" by auto
    then show ?thesis 
    proof (cases "7 < r \<and> r < 16")
      case True
      then show ?thesis using a1 f1 f2
      apply (simp add: user_reg_mod_def)
      by (auto intro: out_reg_mod_privilege)
    next
      case False
      then have f3: "\<not> (7 < r \<and> r < 16)" by auto
      then show ?thesis
      proof (cases "15 < r \<and> r < 24")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: user_reg_mod_def)
        by (simp add: cpu_reg_val_def)
      next
        case False
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: user_reg_mod_def)
        by (auto intro: in_reg_mod_privilege)
      qed
    qed
  qed
qed

lemma write_reg_privilege: "s' = snd (fst (write_reg w1 w2 w3 
  (s::(('a::len0) sparc_state)))) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: write_reg_def simpler_modify_def)
by (auto intro: user_reg_mod_privilege)

lemma set_annul_privilege: "s' = snd (fst (set_annul b s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: set_annul_def simpler_modify_def)
apply (simp add: annul_mod_def write_annul_def)
by (simp add: cpu_reg_val_def)

lemma set_reset_trap_privilege: "s' = snd (fst (set_reset_trap b s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: set_reset_trap_def simpler_modify_def)
apply (simp add: reset_trap_mod_def write_annul_def)
by (simp add: cpu_reg_val_def)

lemma empty_delayed_pool_write_privilege: "get_delayed_pool s = [] \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<and>
  s' = delayed_pool_write s \<Longrightarrow> 
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: delayed_pool_write_def)
by (simp add: get_delayed_write_def delayed_write_all_def delayed_pool_rm_list_def)

lemma raise_trap_privilege: 
"((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<and>
  s' = snd (fst (raise_trap t s)) \<Longrightarrow> 
  ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: raise_trap_def)
apply (simp add: simpler_modify_def add_trap_set_def)
by (simp add: cpu_reg_val_def)

lemma write_cpu_tt_privilege: "s' = snd (fst (write_cpu_tt w s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: write_cpu_tt_def)
apply (simp add: exec_gets)
apply (simp add: write_cpu_def cpu_reg_mod_def write_tt_def)
apply (simp add: simpler_modify_def)
by (simp add: cpu_reg_val_def)

lemma emp_trap_set_privilege: "s' = emp_trap_set s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: emp_trap_set_def)
by (simp add: cpu_reg_val_def)

lemma sys_reg_mod_privilege: "s' = sys_reg_mod w r s 
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: sys_reg_mod_def)
by (simp add: cpu_reg_val_def)

lemma mem_mod_privilege: 
assumes a1: "s' = mem_mod a1 a2 v s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "(uint a1) = 8 \<or> (uint a1) = 10")
  case True
  then show ?thesis using a1
  apply (simp add: mem_mod_def)
  apply (simp add: Let_def)
  by (simp add: cpu_reg_val_def)
next
  case False
  then have f1: "\<not>((uint a1) = 8 \<or> (uint a1) = 10)" by auto
  then show ?thesis 
  proof (cases "(uint a1) = 9 \<or> (uint a1) = 11")
    case True
    then show ?thesis using a1 f1
    apply (simp add: mem_mod_def)
    apply (simp add: Let_def)
    by (simp add: cpu_reg_val_def)
  next
    case False
    then show ?thesis using a1 f1
    apply (simp add: mem_mod_def)
    by (simp add: cpu_reg_val_def)
  qed
qed

lemma mem_mod_w32_privilege: "s' = mem_mod_w32 a1 a2 b d s \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: mem_mod_w32_def)
apply (simp add: Let_def)
by (auto intro: mem_mod_privilege)

lemma add_instr_cache_privilege: "s' = add_instr_cache s addr y m \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: add_instr_cache_def)
apply (simp add: Let_def)
by (simp add: icache_mod_def cpu_reg_val_def)

lemma add_data_cache_privilege: "s' = add_data_cache s addr y m \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: add_data_cache_def)
apply (simp add: Let_def)
by (simp add: dcache_mod_def cpu_reg_val_def)

lemma memory_read_privilege: 
assumes a1: "s' = snd (memory_read asi addr s) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "uint asi = 1")
  case True
  then show ?thesis using a1 
  apply (simp add: memory_read_def)
  by (simp add: Let_def)
next
  case False
  then have f1: "uint asi \<noteq> 1" by auto
  then show ?thesis  
  proof (cases "uint asi = 2")
    case True 
    then show ?thesis using a1 f1
    by (simp add: memory_read_def)    
  next
    case False
    then have f2: "uint asi \<noteq> 2" by auto
    then show ?thesis 
    proof (cases "uint asi \<in> {8,9}")
      case True
      then have f3: "uint asi \<in> {8,9}" by auto
      then show ?thesis
      proof (cases "load_word_mem s addr asi = None")
        case True
        then have f4: "load_word_mem s addr asi = None" by auto
        then show ?thesis 
        using a1 f1 f2 f3 f4
        by (simp add: memory_read_def)
      next
        case False
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: memory_read_def)      
        apply auto
         apply (simp add: add_instr_cache_privilege)
        by (simp add: add_instr_cache_privilege)
      qed
    next
      case False
      then have f5: "uint asi \<notin> {8, 9}" by auto
      then show ?thesis 
        proof (cases "uint asi \<in> {10,11}")
          case True
          then have f6: "uint asi \<in> {10,11}" by auto
          then show ?thesis
          proof (cases "load_word_mem s addr asi = None")
            case True
            then have f7: "load_word_mem s addr asi = None" by auto
            then show ?thesis 
            using a1 f1 f2 f5 f6 f7
            by (simp add: memory_read_def)
          next
            case False
            then show ?thesis using a1 f1 f2 f5 f6
            apply (simp add: memory_read_def)      
            apply auto
             apply (simp add: add_data_cache_privilege)
            by (simp add: add_data_cache_privilege)
          qed
      next
        case False
        then have f8: "uint asi \<notin> {10,11}" by auto
        then show ?thesis
        proof (cases "uint asi = 13")
          case True
          then have f9: "uint asi = 13" by auto
          then show ?thesis 
          proof (cases "read_instr_cache s addr = None")
            case True
            then show ?thesis using a1 f1 f2 f5 f8 f9
            by (simp add: memory_read_def) 
          next
            case False
            then show ?thesis using a1 f1 f2 f5 f8 f9
            apply (simp add: memory_read_def)
            by auto
          qed
        next
          case False
          then have f10: "uint asi \<noteq> 13" by auto
          then show ?thesis 
          proof (cases "uint asi = 15")
            case True
            then show ?thesis using a1 f1 f2 f5 f8 f10
            apply (simp add: memory_read_def)
            apply (cases "read_data_cache s addr = None")
             by auto
          next
            case False
            then show ?thesis using a1 f1 f2 f5 f8 f10
            apply (simp add: memory_read_def) \<comment> \<open>The rest cases are easy.\<close>
            by (simp add: Let_def)
          qed
        qed
      qed      
    qed
  qed
qed

lemma get_curr_win_privilege: "s' = snd (fst (get_curr_win() s)) \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: get_curr_win_def)
by (simp add: simpler_gets_def)

lemma load_sub2_privilege: 
assumes a1: "s' = snd (fst (load_sub2 addr asi r win w s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "fst (memory_read asi (addr + 4)
                        (snd (fst (write_reg w win (r AND 30) s)))) =
                  None")
  case True
  then show ?thesis using a1
  apply (simp add: load_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  by (auto intro: raise_trap_privilege write_reg_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: load_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: case_prod_unfold)
  apply clarsimp
  apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
  by (auto intro: write_reg_privilege memory_read_privilege)
qed

lemma load_sub3_privilege: 
assumes a1: "s' = snd (fst (load_sub3 instr curr_win rd asi address s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "fst (memory_read asi address s) = None")
  case True
  then show ?thesis using a1
  apply (simp add: load_sub3_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: case_prod_unfold)
  by (auto intro: raise_trap_privilege)
next
  case False
  then have f1: "fst (memory_read asi address s) \<noteq> None " by auto
  then show ?thesis 
  proof (cases "rd \<noteq> 0 \<and>
                          (fst instr = load_store_type LD \<or>
                           fst instr = load_store_type LDA \<or>
                           fst instr = load_store_type LDUH \<or>
                           fst instr = load_store_type LDSB \<or>
                           fst instr = load_store_type LDUB \<or>
                           fst instr = load_store_type LDUBA \<or>
                           fst instr = load_store_type LDSH \<or>
                           fst instr = load_store_type LDSHA \<or>
                           fst instr = load_store_type LDUHA \<or>
                           fst instr = load_store_type LDSBA)")
    case True
    then show ?thesis using a1 f1
    apply (simp add: load_sub3_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: case_prod_unfold)
    apply clarsimp
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    by (auto intro: write_reg_privilege memory_read_privilege)
  next 
    case False
    then show ?thesis using a1 f1
    apply (simp add: load_sub3_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: case_prod_unfold)
    apply auto
     apply (simp add: simpler_modify_def bind_def h1_def h2_def)
     apply (auto intro: load_sub2_privilege memory_read_privilege)
    apply (simp add: simpler_modify_def bind_def h1_def h2_def)
    by (auto intro: load_sub2_privilege memory_read_privilege)
  qed
qed

lemma load_sub1_privilege: 
assumes a1: "s' = snd (fst (load_sub1 instr rd s_val s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: load_sub1_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply auto
               by (auto intro: get_curr_win_privilege raise_trap_privilege load_sub3_privilege)

lemma load_instr_privilege: "s' = snd (fst (load_instr i s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: load_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: Let_def)
apply clarsimp
by (auto intro: get_curr_win_privilege raise_trap_privilege load_sub1_privilege)

lemma store_barrier_pending_mod_privilege: "s' = store_barrier_pending_mod b s
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0
  \<Longrightarrow> ((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: store_barrier_pending_mod_def)
apply (simp add: write_store_barrier_pending_def)
by (simp add: cpu_reg_val_def)

lemma store_word_mem_privilege: 
assumes a1: "store_word_mem s addr data byte_mask asi = Some s' \<and> 
((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1 apply (simp add: store_word_mem_def)
apply (case_tac "virt_to_phys addr (mmu s) (mem s) = None")
apply auto
apply (case_tac "mmu_writable (get_acc_flag b) asi")
apply auto
by (simp add: mem_mod_w32_privilege)

lemma flush_instr_cache_privilege: "((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
s' = flush_instr_cache s \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: flush_instr_cache_def)
by (simp add: cpu_reg_val_def)

lemma flush_data_cache_privilege: "((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
s' = flush_data_cache s \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: flush_data_cache_def)
by (simp add: cpu_reg_val_def)

lemma flush_cache_all_privilege: "((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0 \<Longrightarrow>
s' = flush_cache_all s \<Longrightarrow>
((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
apply (simp add: flush_cache_all_def)
by (simp add: cpu_reg_val_def)

lemma memory_write_asi_privilege: 
assumes a1: "r = memory_write_asi asi addr byte_mask data s \<and>
  r = Some s' \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "uint asi = 1")
  case True
  then show ?thesis using a1
  apply (simp add: memory_write_asi_def)
  by (auto intro: store_word_mem_privilege)
next
  case False
  then have f1: "uint asi \<noteq> 1" by auto
  then show ?thesis
  proof (cases "uint asi = 2")
    case True
    then have f01: "uint asi = 2" by auto 
    then show ?thesis 
    proof (cases "uint addr = 0")
      case True
      then show ?thesis using a1 f1 f01      
      apply (simp add: memory_write_asi_def)
      apply (simp add: ccr_flush_def)
      apply (simp add: Let_def)
      apply auto
         apply (metis flush_data_cache_privilege flush_instr_cache_privilege sys_reg_mod_privilege)
        apply (metis flush_instr_cache_privilege sys_reg_mod_privilege)
       apply (metis flush_data_cache_privilege sys_reg_mod_privilege)
      by (simp add: sys_reg_mod_privilege)
    next
      case False
      then show ?thesis using a1 f1 f01
      apply (simp add: memory_write_asi_def)
      apply clarsimp
      by (metis option.distinct(1) option.sel sys_reg_mod_privilege)      
    qed      
  next
    case False
    then have f2: "uint asi \<noteq> 2" by auto
    then show ?thesis
    proof (cases "uint asi \<in> {8,9}")
      case True
      then show ?thesis using a1 f1 f2
      apply (simp add: memory_write_asi_def)
      using store_word_mem_privilege add_instr_cache_privilege
      by blast    
    next
      case False
      then have f3: "uint asi \<notin> {8,9}" by auto
      then show ?thesis 
      proof (cases "uint asi \<in> {10,11}")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: memory_write_asi_def)
        using store_word_mem_privilege add_data_cache_privilege
        by blast 
      next
        case False
        then have f4: "uint asi \<notin> {10,11}" by auto
        then show ?thesis 
        proof (cases "uint asi = 13")
          case True
          then show ?thesis using a1 f1 f2 f3 f4
          apply (simp add: memory_write_asi_def)
          by (auto simp add: add_instr_cache_privilege)
        next
          case False
          then have f5: "uint asi \<noteq> 13" by auto
          then show ?thesis
          proof (cases "uint asi = 15")
            case True
            then show ?thesis using a1 f1 f2 f3 f4 f5
            apply (simp add: memory_write_asi_def)
            by (auto simp add: add_data_cache_privilege)
          next
            case False
            then have f6: "uint asi \<noteq> 15" by auto
            then show ?thesis
            proof (cases "uint asi = 16")
              case True
              then show ?thesis using a1
              apply (simp add: memory_write_asi_def)
              by (auto simp add: flush_instr_cache_privilege)
            next
              case False
              then have f7: "uint asi \<noteq> 16" by auto
              then show ?thesis
              proof (cases "uint asi = 17")
                case True
                then show ?thesis using a1
                apply (simp add: memory_write_asi_def)
                by (auto simp add: flush_data_cache_privilege)
              next
                case False
                then have f8: "uint asi \<noteq> 17" by auto
                then show ?thesis
                proof (cases "uint asi = 24")
                  case True
                  then show ?thesis using a1
                  apply (simp add: memory_write_asi_def)
                  by (auto simp add: flush_cache_all_privilege)
                next
                  case False
                  then have f9: "uint asi \<noteq> 24" by auto
                  then show ?thesis
                  proof (cases "uint asi = 25")
                    case True
                    then show ?thesis using a1
                    apply (simp add: memory_write_asi_def)
                    apply (case_tac "mmu_reg_mod (mmu s) addr data = None")
                     apply auto
                    by (simp add: cpu_reg_val_def)
                  next
                    case False
                    then have f10: "uint asi \<noteq> 25" by auto
                    then show ?thesis
                    proof (cases "uint asi = 28")
                      case True
                      then show ?thesis using a1
                      apply (simp add: memory_write_asi_def)
                      by (auto simp add: mem_mod_w32_privilege)
                    next
                      case False \<comment> \<open>The remaining cases are easy.\<close>
                      then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
                      apply (simp add: memory_write_asi_def)
                      apply (auto simp add: Let_def)
                      apply (case_tac "uint asi = 20 \<or> uint asi = 21")
                       by auto                  
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma memory_write_privilege: 
assumes a1: "r = memory_write asi addr byte_mask data 
  (s::(('a::len0) sparc_state)) \<and>
  r = Some s' \<and>
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR 
  (s'::(('a::len0) sparc_state)))))::word1) = 0"
proof -
  have "\<forall>x. Some x \<noteq> None" by auto
  then have "r \<noteq> None" using a1
    by (simp add: \<open>r = memory_write asi addr byte_mask data s \<and> 
        r = Some s' \<and> ucast (get_S (cpu_reg_val PSR s)) = 0\<close>)  
  then have "\<exists>s''. r = Some (store_barrier_pending_mod False s'')" using a1
    by (metis (no_types, lifting) memory_write_def option.case_eq_if) 
  then have "\<exists>s''. s' = store_barrier_pending_mod False s''" using a1
    by blast    
  then have "\<exists>s''. memory_write_asi asi addr byte_mask data s = Some s'' \<and> 
             s' = store_barrier_pending_mod False s''"
    by (metis (no_types, lifting) assms memory_write_def not_None_eq option.case_eq_if option.sel)
  then show ?thesis using a1
    using memory_write_asi_privilege store_barrier_pending_mod_privilege by blast   
qed

lemma store_sub2_privilege: 
assumes a1: "s' = snd (fst (store_sub2 instr curr_win rd asi address s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "memory_write asi address (st_byte_mask instr address)
                        (st_data0 instr curr_win rd address s) s =
                       None")
  case True
  then show ?thesis using a1
  apply (simp add: store_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  by (metis fst_conv raise_trap_privilege return_def snd_conv)
next
  case False
  then have f1: "\<not>(memory_write asi address (st_byte_mask instr address)
                        (st_data0 instr curr_win rd address s) s =
                       None)" 
    by auto
  then show ?thesis  
  proof (cases "(fst instr) \<in> {load_store_type STD,load_store_type STDA}")
    case True
    then have f2: "(fst instr) \<in> {load_store_type STD,load_store_type STDA}" by auto
    then show ?thesis using a1 f1
    apply (simp add: store_sub2_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    apply (simp add: return_def)
    apply (simp add: bind_def case_prod_unfold)
    apply (simp add: simpler_modify_def)
    apply clarsimp
    apply (simp add: case_prod_unfold bind_def h1_def h2_def Let_def simpler_modify_def)
    apply (simp add: simpler_gets_def)
    apply auto
       using memory_write_privilege raise_trap_privilege apply blast
      apply (simp add: simpler_modify_def simpler_gets_def bind_def)
      apply (meson memory_write_privilege)
     using memory_write_privilege raise_trap_privilege apply blast
    by (meson memory_write_privilege)    
  next
    case False
    then show ?thesis using a1 f1
    apply (simp add: store_sub2_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply clarsimp
    apply (simp add: simpler_modify_def return_def)
    by (auto intro: memory_write_privilege)
  qed
qed

lemma store_sub1_privilege: 
assumes a1: "s' = snd (fst (store_sub1 instr rd s_val 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR 
  (s'::(('a::len0) sparc_state)))))::word1) = 0"
proof (cases "(fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s)))))::word1) \<noteq> 0")
  case True
  then show ?thesis using a1
  apply (simp add: store_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  using get_curr_win_privilege raise_trap_privilege by blast                
next
  case False
  then have f1: "\<not>((fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s)))))::word1) \<noteq> 0)"
    by auto
  then show ?thesis 
  proof (cases "(fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s)))))::word2) \<noteq> 0")
    case True
    then show ?thesis using a1 f1
    apply (simp add: store_sub1_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply (simp add: case_prod_unfold)    
    using get_curr_win_privilege raise_trap_privilege by blast
  next
    case False
    then have f2: "\<not>((fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s)))))::word2) \<noteq> 0)"
      by auto
    then show ?thesis
    proof (cases "(fst instr \<in> {load_store_type STD,load_store_type STDA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s)))))::word3) \<noteq> 0")
      case True
      then show ?thesis using a1 f1 f2
      apply (simp add: store_sub1_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: case_prod_unfold) 
      using get_curr_win_privilege raise_trap_privilege by blast
    next
      case False
      then show ?thesis using a1 f1 f2
      apply (simp add: store_sub1_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: case_prod_unfold)
      by (meson get_curr_win_privilege store_sub2_privilege)       
    qed
  qed
qed

lemma store_instr_privilege: 
assumes a1: "s' = snd (fst (store_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR 
  (s'::(('a::len0) sparc_state)))))::word1) = 0"
using a1
apply (simp add: store_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def)
apply (simp add: Let_def)
using raise_trap_privilege store_sub1_privilege by blast

lemma sethi_instr_privilege: 
assumes a1: "s' = snd (fst (sethi_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: sethi_instr_def)
apply (simp add: Let_def)
apply auto
 apply (simp add: bind_def h1_def h2_def Let_def)
 apply (simp add: case_prod_unfold)
 using get_curr_win_privilege write_reg_privilege apply blast
by (simp add: return_def)

lemma nop_instr_privilege: 
assumes a1: "s' = snd (fst (nop_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: nop_instr_def)
by (simp add: return_def)

lemma ucast_0: "((ucast (get_S w))::word1) = 0 \<Longrightarrow> get_S w = 0"
by (simp add: ucast_id)

lemma ucast_02: "get_S w = 0 \<Longrightarrow> ((ucast (get_S w))::word1) = 0"
by simp

lemma ucast_s: "((ucast (get_S w))::word1) = 0 \<Longrightarrow> 
  bitAND w (0b00000000000000000000000010000000::word32) = 0"
apply (simp add: get_S_def)
by (metis (mono_tags) ucast_id zero_neq_one)

lemma ucast_s2: "bitAND w 0b00000000000000000000000010000000 = 0
  \<Longrightarrow> ((ucast (get_S w))::word1) = 0"
by (simp add: get_S_def)

lemma update_PSR_icc_1: "w' = bitAND w (0b11111111000011111111111111111111::word32)
  \<and> ((ucast (get_S w))::word1) = 0
  \<Longrightarrow> ((ucast (get_S w'))::word1) = 0"
by (simp add: get_S_def word_bw_assocs(1))

lemma and_num_1048576_128: "bitAND (0b00000000000100000000000000000000::word32)
  (0b00000000000000000000000010000000::word32) = 0"
by simp

lemma and_num_2097152_128: "bitAND (0b00000000001000000000000000000000::word32)
  (0b00000000000000000000000010000000::word32) = 0"
by simp

lemma and_num_4194304_128: "bitAND (0b00000000010000000000000000000000::word32)
  (0b00000000000000000000000010000000::word32) = 0"
by simp

lemma and_num_8388608_128: "bitAND (0b00000000100000000000000000000000::word32)
  (0b00000000000000000000000010000000::word32) = 0"
by simp

lemma or_and_s: "bitAND w1 (0b00000000000000000000000010000000::word32) = 0
  \<and> bitAND w2 (0b00000000000000000000000010000000::word32) = 0
  \<Longrightarrow> bitAND (bitOR w1 w2) (0b00000000000000000000000010000000::word32) = 0"
by (simp add: word_ao_dist)

lemma and_or_s: 
assumes a1: "((ucast (get_S w1))::word1) = 0 \<and> 
  bitAND w2 (0b00000000000000000000000010000000::word32) = 0"
shows "((ucast (get_S (bitOR (bitAND w1 
  (0b11111111000011111111111111111111::word32)) w2)))::word1) = 0"
by (metis (full_types) assms ucast_s ucast_s2 word_ao_absorbs(8) word_bool_alg.conj_disj_distrib2)

lemma and_or_or_s:
assumes a1: "((ucast (get_S w1))::word1) = 0 \<and> 
  bitAND w2 (0b00000000000000000000000010000000::word32) = 0 \<and>  
  bitAND w3 (0b00000000000000000000000010000000::word32) = 0"
shows "((ucast (get_S (bitOR (bitOR (bitAND w1 
  (0b11111111000011111111111111111111::word32)) w2) w3)))::word1) = 0"
using and_or_s assms or_and_s ucast_s ucast_s2 by blast 

lemma and_or_or_or_s:
assumes a1: "((ucast (get_S w1))::word1) = 0 \<and> 
  bitAND w2 (0b00000000000000000000000010000000::word32) = 0 \<and>  
  bitAND w3 (0b00000000000000000000000010000000::word32) = 0 \<and>
  bitAND w4 (0b00000000000000000000000010000000::word32) = 0"
shows "((ucast (get_S (bitOR (bitOR (bitOR (bitAND w1 
  (0b11111111000011111111111111111111::word32)) w2) w3) w4)))::word1) = 0"
using and_or_or_s assms or_and_s ucast_s ucast_s2 
by (meson word_bool_alg.conj.commute word_bool_alg.conj_zero_left word_bw_assocs(1))

lemma and_or_or_or_or_s:
assumes a1: "((ucast (get_S w1))::word1) = 0 \<and> 
  bitAND w2 (0b00000000000000000000000010000000::word32) = 0 \<and>  
  bitAND w3 (0b00000000000000000000000010000000::word32) = 0 \<and>
  bitAND w4 (0b00000000000000000000000010000000::word32) = 0 \<and> 
  bitAND w5 (0b00000000000000000000000010000000::word32) = 0"
shows "((ucast (get_S (bitOR (bitOR (bitOR (bitOR (bitAND w1 
  (0b11111111000011111111111111111111::word32)) w2) w3) w4) w5)))::word1) = 0"
using and_or_or_or_s assms or_and_s ucast_s ucast_s2
by (meson word_ao_absorbs(8) word_bool_alg.conj_disj_distrib2) 

lemma write_cpu_PSR_icc_privilege: 
assumes a1: "s' = snd (fst (write_cpu (update_PSR_icc n_val z_val v_val c_val 
                                        (cpu_reg_val PSR s)) 
                                      PSR 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: write_cpu_def)
apply (simp add: simpler_modify_def)
apply (simp add: cpu_reg_mod_def update_PSR_icc_def)
apply (simp add: cpu_reg_val_def)
apply auto
               using update_PSR_icc_1 apply blast
              using update_PSR_icc_1 and_num_1048576_128 and_or_s apply blast
             using update_PSR_icc_1 and_num_2097152_128 and_or_s apply blast
            using update_PSR_icc_1 and_num_1048576_128 and_num_2097152_128 
            and_or_or_s apply blast
           using update_PSR_icc_1 and_num_4194304_128 and_or_s apply blast
          using update_PSR_icc_1 and_num_1048576_128 and_num_4194304_128 
          and_or_or_s apply blast
         using update_PSR_icc_1 and_num_2097152_128 and_num_4194304_128 
         and_or_or_s apply blast
        using update_PSR_icc_1 and_num_1048576_128 and_num_2097152_128 and_num_4194304_128
        and_or_or_or_s apply blast 
       using update_PSR_icc_1 and_num_8388608_128 and_or_s apply blast
      using update_PSR_icc_1 and_num_1048576_128 and_num_8388608_128 
      and_or_or_s apply blast
     using update_PSR_icc_1 and_num_2097152_128 and_num_8388608_128 
     and_or_or_s apply blast
    using update_PSR_icc_1 and_num_1048576_128 and_num_2097152_128 and_num_8388608_128
    and_or_or_or_s apply blast 
   using update_PSR_icc_1 and_num_4194304_128 and_num_8388608_128 
   and_or_or_s apply blast
  using update_PSR_icc_1 and_num_1048576_128 and_num_4194304_128 and_num_8388608_128
  and_or_or_or_s apply blast 
 using update_PSR_icc_1 and_num_2097152_128 and_num_4194304_128 and_num_8388608_128
 and_or_or_or_s apply blast 
using update_PSR_icc_1 and_num_1048576_128 and_num_2097152_128 and_num_4194304_128 
and_num_8388608_128 and_or_or_or_or_s by blast 

lemma and_num_4294967167_128: "bitAND (0b11111111111111111111111101111111::word32)
  (0b00000000000000000000000010000000::word32) = 0"
by simp

lemma s_0_word: "((ucast (get_S (bitAND w 
  (0b11111111111111111111111101111111::word32))))::word1) = 0"
apply (simp add: get_S_def)
using and_num_4294967167_128
by (simp add: word_bool_alg.conj.commute word_bw_lcs(1)) 

lemma update_PSR_CWP_1: "w' = bitAND w (0b11111111111111111111111111100000::word32)
  \<and> ((ucast (get_S w))::word1) = 0
  \<Longrightarrow> ((ucast (get_S w'))::word1) = 0"
by (simp add: get_S_def word_bw_assocs(1))

lemma write_cpu_PSR_CWP_privilege: 
assumes a1: "s' = snd (fst (write_cpu (update_CWP cwp_val 
                                        (cpu_reg_val PSR s)) 
                                      PSR 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: write_cpu_def)
apply (simp add: simpler_modify_def)
apply (simp add: cpu_reg_mod_def)
apply (simp add: update_CWP_def)
apply (simp add: Let_def)
apply auto
apply (simp add: cpu_reg_val_def)
using s_0_word by blast

lemma logical_instr_sub1_privilege: 
assumes a1: "s' = snd (fst (logical_instr_sub1 instr_name result 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "instr_name = logic_type ANDcc \<or>
              instr_name = logic_type ANDNcc \<or>
              instr_name = logic_type ORcc \<or>
              instr_name = logic_type ORNcc \<or>
              instr_name = logic_type XORcc \<or> instr_name = logic_type XNORcc")
  case True
  then show ?thesis using a1
  apply (simp add: logical_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: logical_new_psr_val_def)
  using write_cpu_PSR_icc_privilege by blast
next
  case False
  then show ?thesis using a1
  apply (simp add: logical_instr_sub1_def)
  by (simp add: return_def)
qed

lemma logical_instr_privilege: 
assumes a1: "s' = snd (fst (logical_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: logical_instr_def)
apply (simp add: Let_def simpler_gets_def bind_def h1_def h2_def)
apply (simp add: case_prod_unfold)
apply auto
 apply (meson get_curr_win_privilege logical_instr_sub1_privilege write_reg_privilege)
by (meson get_curr_win_privilege logical_instr_sub1_privilege write_reg_privilege)

method shift_instr_privilege_proof = (
(simp add: shift_instr_def),
(simp add: Let_def), 
(simp add: simpler_gets_def),
(simp add: bind_def h1_def h2_def Let_def case_prod_unfold),
auto,
(blast intro: get_curr_win_privilege write_reg_privilege),
(blast intro: get_curr_win_privilege write_reg_privilege)
)

lemma shift_instr_privilege: 
assumes a1: "s' = snd (fst (shift_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "(fst instr = shift_type SLL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
  case True
  then show ?thesis using a1
  by shift_instr_privilege_proof
next
  case False
  then have f1: "\<not>((fst instr = shift_type SLL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0))"
    by auto
  then show ?thesis
  proof (cases "(fst instr = shift_type SRL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
    case True
    then show ?thesis using a1 f1
    by shift_instr_privilege_proof
  next
    case False
    then have f2: "\<not>((fst instr = shift_type SRL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0))"
      by auto
    then show ?thesis 
    proof (cases "(fst instr = shift_type SRA) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
      case True
      then show ?thesis using a1 f1 f2
      by shift_instr_privilege_proof
    next
      case False
      then show ?thesis using a1 f1 f2
      apply (simp add: shift_instr_def)
      apply (simp add: Let_def) 
      apply (simp add: simpler_gets_def)
      apply (simp add: bind_def h1_def h2_def Let_def case_prod_unfold)
      apply (simp add: return_def)
      using get_curr_win_privilege by blast
    qed
  qed
qed

lemma add_instr_sub1_privilege: 
assumes a1: "s' = snd (fst (add_instr_sub1 instr_name result rs1_val operand2 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "instr_name = arith_type ADDcc \<or> instr_name = arith_type ADDXcc")
  case True
  then show ?thesis using a1
  apply (simp add: add_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (blast intro: write_cpu_PSR_icc_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: add_instr_sub1_def)
  by (simp add: return_def)
qed

lemma add_instr_privilege: 
assumes a1: "s' = snd (fst (add_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: add_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson add_instr_sub1_privilege get_curr_win_privilege write_reg_privilege)

lemma sub_instr_sub1_privilege: 
assumes a1: "s' = snd (fst (sub_instr_sub1 instr_name result rs1_val operand2 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "instr_name = arith_type SUBcc \<or> instr_name = arith_type SUBXcc")
  case True
  then show ?thesis using a1
  apply (simp add: sub_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (blast intro: write_cpu_PSR_icc_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: sub_instr_sub1_def)
  by (simp add: return_def)
qed

lemma sub_instr_privilege: 
assumes a1: "s' = snd (fst (sub_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: sub_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson sub_instr_sub1_privilege get_curr_win_privilege write_reg_privilege)

lemma mul_instr_sub1_privilege: 
assumes a1: "s' = snd (fst (mul_instr_sub1 instr_name result  
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "instr_name \<in> {arith_type SMULcc,arith_type UMULcc}")
  case True
  then show ?thesis using a1
  apply (simp add: mul_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (blast intro: write_cpu_PSR_icc_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: mul_instr_sub1_def)
  by (simp add: return_def)
qed

lemma mul_instr_privilege: 
assumes a1: "s' = snd (fst (mul_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: mul_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson get_curr_win_privilege mul_instr_sub1_privilege write_cpu_y_privilege write_reg_privilege)

lemma div_write_new_val_privilege: 
assumes a1: "s' = snd (fst (div_write_new_val i result temp_V  
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "(fst i) \<in> {arith_type UDIVcc,arith_type SDIVcc}")
  case True
  then show ?thesis using a1
  apply (simp add: div_write_new_val_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (blast intro: write_cpu_PSR_icc_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: div_write_new_val_def)
  by (simp add: return_def)
qed

lemma div_comp_privilege: 
assumes a1: "s' = snd (fst (div_comp instr rs1 rd operand2  
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: div_comp_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson get_curr_win_privilege div_write_new_val_privilege write_reg_privilege)

lemma div_instr_privilege: 
assumes a1: "s' = snd (fst (div_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: div_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: return_def)
apply auto
 using raise_trap_privilege apply blast
using div_comp_privilege by blast

lemma save_retore_sub1_privilege: 
assumes a1: "s' = snd (fst (save_retore_sub1 result new_cwp rd 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: save_retore_sub1_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
using write_cpu_PSR_CWP_privilege write_reg_privilege by blast

method save_restore_instr_privilege_proof = (
(simp add: save_restore_instr_def),
(simp add: Let_def),
(simp add: simpler_gets_def bind_def h1_def h2_def Let_def),
(simp add: case_prod_unfold),
auto,
(blast intro: get_curr_win_privilege raise_trap_privilege),
(simp add: simpler_gets_def bind_def h1_def h2_def Let_def case_prod_unfold),
(blast intro: get_curr_win_privilege save_retore_sub1_privilege)
)

lemma save_restore_instr_privilege: 
assumes a1: "s' = snd (fst (save_restore_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "fst instr = ctrl_type SAVE")
  case True
  then have f1: "fst instr = ctrl_type SAVE" by auto
  then show ?thesis using a1
  by save_restore_instr_privilege_proof
next
  case False
  then show ?thesis using a1
  by save_restore_instr_privilege_proof
qed

lemma call_instr_privilege: 
assumes a1: "s' = snd (fst (call_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: call_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson get_curr_win_privilege write_cpu_npc_privilege write_cpu_pc_privilege write_reg_privilege)

lemma jmpl_instr_privilege: 
assumes a1: "s' = snd (fst (jmpl_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: jmpl_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply auto
 using get_curr_win_privilege raise_trap_privilege apply blast
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
by (meson get_curr_win_privilege write_cpu_npc_privilege write_cpu_pc_privilege write_reg_privilege)

lemma rett_instr_privilege: 
assumes a1: "snd (rett_instr i s) = False \<and>
  s' = snd (fst (rett_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: rett_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply auto
 apply (simp add: case_prod_unfold)
 apply (simp add: return_def)
 apply (blast intro: raise_trap_privilege)
apply (simp add: bind_def h1_def h2_def Let_def)
by (simp add: case_prod_unfold fail_def)

method read_state_reg_instr_privilege_proof = (
(simp add: read_state_reg_instr_def),
(simp add: Let_def),
(simp add: simpler_gets_def bind_def h1_def h2_def Let_def),
(simp add: case_prod_unfold)
)

lemma read_state_reg_instr_privilege: 
assumes a1: "s' = snd (fst (read_state_reg_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "(fst instr \<in> {sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR} \<or> 
        (fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 ((snd instr)!0))))")
  case True
  then have "(fst instr \<in> {sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR} \<or> 
        (fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 ((snd instr)!0))))
        \<and> ((ucast (get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s))))))::word1) = 0"
    by (metis assms get_curr_win_privilege)    
  then show ?thesis using a1
  apply read_state_reg_instr_privilege_proof
  by (blast intro: raise_trap_privilege get_curr_win_privilege)
next
  case False
  then have f1: "\<not>((fst instr = sreg_type RDPSR \<or>
                    fst instr = sreg_type RDWIM \<or>
                    fst instr = sreg_type RDTBR \<or>
                    fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 (snd instr ! 0))) \<and>
                   ucast (get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s))))) = 0)"
    by blast 
  then show ?thesis 
  proof (cases "illegal_instruction_ASR (get_operand_w5 ((snd instr)!0))")
    case True
    then show ?thesis using a1 f1
    apply read_state_reg_instr_privilege_proof
    by (simp add: illegal_instruction_ASR_def)    
  next
    case False
    then have f2: "\<not>(illegal_instruction_ASR (get_operand_w5 ((snd instr)!0)))" 
      by auto
    then show ?thesis 
    proof (cases "(get_operand_w5 ((snd instr)!1)) \<noteq> 0")
      case True
      then have f3: "(get_operand_w5 ((snd instr)!1)) \<noteq> 0" 
        by auto
      then show ?thesis 
      proof (cases "fst instr = sreg_type RDY")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: read_state_reg_instr_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        by (blast intro: get_curr_win_privilege write_reg_privilege)        
      next
        case False
        then have f4: "\<not>(fst instr = sreg_type RDY)" by auto
        then show ?thesis 
        proof (cases "fst instr = sreg_type RDASR")
          case True
          then show ?thesis using a1 f1 f2 f3 f4
          apply read_state_reg_instr_privilege_proof
          apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
          by (blast intro: get_curr_win_privilege write_reg_privilege) 
        next
          case False
          then have f5: "\<not>(fst instr = sreg_type RDASR)" by auto
          then show ?thesis 
          proof (cases "fst instr = sreg_type RDPSR")
            case True
            then show ?thesis using a1 f1 f2 f3 f4 f5
            apply read_state_reg_instr_privilege_proof
            by (blast intro: get_curr_win_privilege write_reg_privilege) 
          next
            case False
            then show ?thesis using a1 f1 f2 f3 f4 f5
            apply read_state_reg_instr_privilege_proof
            apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
            by (blast intro: get_curr_win_privilege write_reg_privilege) 
          qed
        qed
      qed
    next
      case False
      then show ?thesis using a1 
      apply read_state_reg_instr_privilege_proof
      apply (simp add: return_def) 
      using f1 f2 get_curr_win_privilege by blast     
    qed
  qed
qed

method write_state_reg_instr_privilege_proof = (
(simp add: write_state_reg_instr_def),
(simp add: Let_def),
(simp add: simpler_gets_def bind_def h1_def h2_def Let_def),
(simp add: case_prod_unfold)
)

lemma write_state_reg_instr_privilege: 
assumes a1: "s' = snd (fst (write_state_reg_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "fst instr = sreg_type WRY")
  case True
  then show ?thesis using a1
  apply write_state_reg_instr_privilege_proof
  apply (simp add: simpler_modify_def)
  apply (simp add: delayed_pool_add_def DELAYNUM_def)
  by (blast intro: cpu_reg_mod_y_privilege get_curr_win_privilege)
next
  case False
  then have f1: "\<not>(fst instr = sreg_type WRY)" by auto
  then show ?thesis
  proof (cases "fst instr = sreg_type WRASR")
    case True
    then show ?thesis
     using a1 f1
    apply write_state_reg_instr_privilege_proof
    apply (simp add: simpler_modify_def)
    apply auto
         using illegal_instruction_ASR_def apply blast
        using illegal_instruction_ASR_def apply blast
       using illegal_instruction_ASR_def apply blast
      using raise_trap_privilege get_curr_win_privilege apply blast
     apply (simp add: simpler_modify_def delayed_pool_add_def DELAYNUM_def)
     using cpu_reg_mod_asr_privilege get_curr_win_privilege apply blast
    apply (simp add: simpler_modify_def delayed_pool_add_def DELAYNUM_def)
    using cpu_reg_mod_asr_privilege get_curr_win_privilege by blast
  next
    case False
    then have f2: "\<not>(fst instr = sreg_type WRASR)" by auto
    have f3: "get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s)))) = 0"
      using get_curr_win_privilege a1 by (metis ucast_id)
    then show ?thesis 
    proof (cases "fst instr = sreg_type WRPSR")
      case True
      then show ?thesis using a1 f1 f2 f3
      apply write_state_reg_instr_privilege_proof
      by (metis raise_trap_privilege ucast_0)      
    next
      case False
      then have f4: "\<not>(fst instr = sreg_type WRPSR)" by auto
      then show ?thesis 
      proof (cases "fst instr = sreg_type WRWIM")  
        case True
        then show ?thesis using a1 f1 f2 f3 f4
        apply write_state_reg_instr_privilege_proof
        by (metis raise_trap_privilege ucast_0)  
      next
        case False
        then have f5: "\<not>(fst instr = sreg_type WRWIM)" by auto
        then show ?thesis using a1 f1 f2 f3 f4 f5
        apply write_state_reg_instr_privilege_proof
        by (metis raise_trap_privilege ucast_0)        
      qed
    qed
  qed
qed

lemma flush_instr_privilege: 
assumes a1: "s' = snd (fst (flush_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: flush_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def simpler_modify_def)
by (auto simp add: flush_cache_all_privilege)

lemma branch_instr_privilege: 
assumes a1: "s' = snd (fst (branch_instr instr 
  (s::(('a::len0) sparc_state))))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
using a1
apply (simp add: branch_instr_def)
apply (simp add: Let_def simpler_gets_def bind_def h1_def h2_def)
apply (simp add: case_prod_unfold return_def)
by (meson set_annul_privilege write_cpu_npc_privilege write_cpu_pc_privilege)

method dispath_instr_privilege_proof = (
(simp add: dispatch_instruction_def),
(simp add: simpler_gets_def bind_def h1_def h2_def Let_def),
(simp add: Let_def)
)

lemma dispath_instr_privilege: 
assumes a1: "snd (dispatch_instruction instr s) = False \<and>
  s' = snd (fst (dispatch_instruction instr s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "get_trap_set s = {}")
  case True
  then have f1: "get_trap_set s = {}" by auto
  show ?thesis
  proof (cases "fst instr \<in> {load_store_type LDSB,load_store_type LDUB,
        load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
        load_store_type LDA,load_store_type LDD}")
    case True
    then show ?thesis using a1 f1
    apply dispath_instr_privilege_proof
    by (blast intro: load_instr_privilege)    
  next
    case False
    then have f2: "\<not>(fst instr \<in> {load_store_type LDSB,load_store_type LDUB,
        load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
        load_store_type LDA,load_store_type LDD})"
      by auto
    then show ?thesis 
    proof (cases "fst instr \<in> {load_store_type STB,load_store_type STH,
        load_store_type ST,load_store_type STA,load_store_type STD}")
      case True
      then show ?thesis using a1 f1 f2
      apply dispath_instr_privilege_proof
      by (blast intro: store_instr_privilege) 
    next
      case False
      then have f3: "\<not>(fst instr \<in> {load_store_type STB,load_store_type STH,
        load_store_type ST,load_store_type STA,load_store_type STD})"
        by auto
      then show ?thesis 
      proof (cases "fst instr \<in> {sethi_type SETHI}")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply dispath_instr_privilege_proof
        by (blast intro: sethi_instr_privilege) 
      next
        case False
        then have f4: "\<not>(fst instr \<in> {sethi_type SETHI})"
          by auto
        then show ?thesis
        proof (cases "fst instr \<in> {nop_type NOP}")
          case True
          then show ?thesis using a1 f1 f2 f3 f4
          apply dispath_instr_privilege_proof
          by (blast intro: nop_instr_privilege)
        next
          case False
          then have f5: "\<not>(fst instr \<in> {nop_type NOP})" 
            by auto
          then show ?thesis
          proof (cases "fst instr \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
            logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
            logic_type XORs,logic_type XNOR}")
            case True
            then show ?thesis using a1 f1 f2 f3 f4 f5
            apply dispath_instr_privilege_proof
            by (blast intro: logical_instr_privilege)
          next
            case False
            then have f6: "\<not>(fst instr \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
            logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
            logic_type XORs,logic_type XNOR})"
              by auto
            show ?thesis
            proof (cases "fst instr \<in> {shift_type SLL,shift_type SRL,shift_type SRA}")
              case True
              then show ?thesis using a1 f1 f2 f3 f4 f5 f6
              apply dispath_instr_privilege_proof
              by (blast intro: shift_instr_privilege)
            next
              case False
              then have f7: "\<not>(fst instr \<in> {shift_type SLL,shift_type SRL,shift_type SRA})"
                by auto
              then show ?thesis 
              proof (cases "fst instr \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX}")
                case True
                then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7
                apply dispath_instr_privilege_proof
                by (blast intro: add_instr_privilege)
              next
                case False
                then have f8: "\<not>(fst instr \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX})"
                  by auto
                then show ?thesis
                proof (cases "fst instr \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX}")
                  case True
                  then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8
                  apply dispath_instr_privilege_proof
                  by (blast intro: sub_instr_privilege)
                next
                  case False
                  then have f9: "\<not>(fst instr \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX})"
                    by auto
                  then show ?thesis
                  proof (cases "fst instr \<in> {arith_type UMUL,arith_type SMUL,arith_type SMULcc}")
                    case True
                    then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9
                    apply dispath_instr_privilege_proof
                    by (blast intro: mul_instr_privilege)
                  next
                    case False
                    then have f10: "\<not>(fst instr \<in> {arith_type UMUL,arith_type SMUL,
                      arith_type SMULcc})"
                      by auto
                    then show ?thesis 
                    proof (cases "fst instr \<in> {arith_type UDIV,arith_type UDIVcc,arith_type SDIV}")
                      case True
                      then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
                      apply dispath_instr_privilege_proof
                      by (blast intro: div_instr_privilege)
                    next
                      case False
                      then have f11: "\<not>(fst instr \<in> {arith_type UDIV,
                        arith_type UDIVcc,arith_type SDIV})"
                        by auto
                      then show ?thesis 
                      proof (cases "fst instr \<in> {ctrl_type SAVE,ctrl_type RESTORE}")
                        case True
                        then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
                        apply dispath_instr_privilege_proof
                        by (blast intro: save_restore_instr_privilege)
                      next
                        case False
                        then have f12: "\<not>(fst instr \<in> {ctrl_type SAVE,ctrl_type RESTORE})"
                          by auto
                        then show ?thesis 
                        proof (cases "fst instr \<in> {call_type CALL}")
                          case True
                          then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
                          apply dispath_instr_privilege_proof
                          by (blast intro: call_instr_privilege)
                        next
                          case False
                          then have f13: "\<not>(fst instr \<in> {call_type CALL})" by auto
                          then show ?thesis
                          proof (cases "fst instr \<in> {ctrl_type JMPL}")
                            case True
                            then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                            apply dispath_instr_privilege_proof
                            by (blast intro: jmpl_instr_privilege)
                          next
                            case False
                            then have f14: "\<not>(fst instr \<in> {ctrl_type JMPL})" by auto
                            then show ?thesis 
                            proof (cases "fst instr \<in> {ctrl_type RETT}")
                              case True
                              then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13
                                f14
                              apply dispath_instr_privilege_proof
                              by (blast intro: rett_instr_privilege)
                            next
                              case False
                              then have f15: "\<not>(fst instr \<in> {ctrl_type RETT})" by auto
                              then show ?thesis 
                              proof (cases "fst instr \<in> {sreg_type RDY,sreg_type RDPSR,
                                sreg_type RDWIM, sreg_type RDTBR}")
                                case True
                                then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                f13 f14 f15
                                apply dispath_instr_privilege_proof
                                by (blast intro: read_state_reg_instr_privilege)
                              next
                                case False
                                then have f16: "\<not>(fst instr \<in> {sreg_type RDY,sreg_type RDPSR,
                                sreg_type RDWIM, sreg_type RDTBR})" by auto
                                then show ?thesis
                                proof (cases "fst instr \<in> {sreg_type WRY,sreg_type WRPSR,
                                  sreg_type WRWIM, sreg_type WRTBR}")
                                  case True
                                  then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 
                                  f13 f14 f15 f16
                                  apply dispath_instr_privilege_proof
                                  by (blast intro: write_state_reg_instr_privilege)
                                next
                                  case False
                                  then have f17: "\<not>(fst instr \<in> {sreg_type WRY,sreg_type WRPSR,
                                  sreg_type WRWIM, sreg_type WRTBR})" by auto
                                  then show ?thesis
                                  proof (cases "fst instr \<in> {load_store_type FLUSH}")
                                    case True
                                    then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                    f12 f13 f14 f15 f16 f17
                                    apply dispath_instr_privilege_proof
                                    by (blast intro: flush_instr_privilege)
                                  next
                                    case False
                                    then have f18: "\<not>(fst instr \<in> {load_store_type FLUSH})" by auto
                                    then show ?thesis 
                                    proof (cases "fst instr \<in> {bicc_type BE,bicc_type BNE,
                                      bicc_type BGU,bicc_type BLE,bicc_type BL,bicc_type BGE,
                                      bicc_type BNEG,bicc_type BG,bicc_type BCS,bicc_type BLEU,
                                      bicc_type BCC,bicc_type BA,bicc_type BN}")
                                      case True
                                      then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                      f12 f13 f14 f15 f16 f17 f18
                                      apply dispath_instr_privilege_proof
                                      by (blast intro: branch_instr_privilege)
                                    next
                                      case False
                                      then show ?thesis using a1 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 
                                      f12 f13 f14 f15 f16 f17 f18
                                      apply dispath_instr_privilege_proof
                                      by (simp add: fail_def)
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case False
  then show ?thesis using a1
  apply (simp add: dispatch_instruction_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: Let_def)
  by (simp add: return_def)
qed

lemma execute_instr_sub1_privilege: 
assumes a1: "snd (execute_instr_sub1 i s) = False \<and>
  s' = snd (fst (execute_instr_sub1 i s))
  \<and> ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "get_trap_set s = {} \<and> fst i \<notin> {call_type CALL,ctrl_type RETT,ctrl_type JMPL,
                                   bicc_type BE,bicc_type BNE,bicc_type BGU,
                                   bicc_type BLE,bicc_type BL,bicc_type BGE,
                                   bicc_type BNEG,bicc_type BG,
                                   bicc_type BCS,bicc_type BLEU,bicc_type BCC,
                                   bicc_type BA,bicc_type BN}")
  case True
  then show ?thesis using a1
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold return_def)
  by (auto intro: write_cpu_pc_privilege write_cpu_npc_privilege)
next
  case False
  then show ?thesis using a1
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold return_def)
  by auto
qed

text \<open>
  Assume that there is no \<open>delayed_write\<close> and 
  there is no traps to be executed.
  If an instruction is executed as a user,
  the privilege will not be changed to supervisor after 
  the execution.\<close>
theorem safe_privilege : 
assumes a1: "get_delayed_pool s = [] \<and> get_trap_set s = {} \<and>
  snd (execute_instruction() s) = False \<and>
  s' = snd (fst (execute_instruction() s)) \<and> 
  ((ucast (get_S (cpu_reg_val PSR s)))::word1) = 0"
shows "((ucast (get_S (cpu_reg_val PSR s')))::word1) = 0"
proof (cases "exe_mode_val s")
  case True   
  then have f2: "exe_mode_val s = True" by auto
  then show ?thesis
  proof (cases "\<exists>e. fetch_instruction (delayed_pool_write s) = Inl e")
    case True
    then have f3: "\<exists>e. fetch_instruction (delayed_pool_write s) = Inl e"
      by auto
    then have f4: "\<not> (\<exists>v. fetch_instruction (delayed_pool_write s) = Inr v)" 
      using fetch_instr_result_3 by auto
    then show ?thesis using a1 f2 f3 raise_trap_result empty_delayed_pool_write_privilege raise_trap_privilege        
    apply (simp add: execute_instruction_def)
    apply (simp add: exec_gets return_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply (simp add: simpler_modify_def)
    apply clarsimp
    apply (simp add: case_prod_unfold)
    by (blast intro: empty_delayed_pool_write_privilege raise_trap_privilege)      
  next
    case False
    then have f5: "\<exists>v. fetch_instruction (delayed_pool_write s) = Inr v"
      using fetch_instr_result_1 by blast
    then have f6: "\<exists>v. fetch_instruction (delayed_pool_write s) = Inr v \<and>
    \<not> (\<exists>e. ((decode_instruction v)::(Exception list + instruction)) = Inl e)"
      using a1 f2 dispatch_fail by blast 
    then have f7: "\<exists>v. fetch_instruction (delayed_pool_write s) = Inr v \<and>
    (\<exists>v1. ((decode_instruction v)::(Exception list + instruction)) = Inr v1)"
      using decode_instr_result_4 by auto 
    then show ?thesis
    proof (cases "annul_val (delayed_pool_write s)")
      case True
      then show ?thesis using  a1 f2 f7           
      apply (simp add: execute_instruction_def)
      apply (simp add: exec_gets return_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: simpler_modify_def)
      apply clarsimp
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: case_prod_unfold)
      by (auto intro: empty_delayed_pool_write_privilege 
      set_annul_privilege write_cpu_npc_privilege write_cpu_pc_privilege)
    next 
      case False
      then show ?thesis using  a1 f2 f7 
      apply (simp add: execute_instruction_def)
      apply (simp add: exec_gets return_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: simpler_modify_def)
      apply clarsimp
      apply (simp add: bind_def h1_def h2_def Let_def)
      apply (simp add: case_prod_unfold)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: simpler_modify_def return_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: case_prod_unfold)
      by (auto intro: empty_delayed_pool_write_privilege dispath_instr_privilege 
         execute_instr_sub1_privilege)        
    qed
  qed    
next
  case False
  then show ?thesis using a1 
  apply (simp add: execute_instruction_def)
  by (simp add: simpler_gets_def bind_def h1_def h2_def Let_def return_def) 
qed

(*********************************************************************)

section \<open>Single step non-interference property.\<close>

(*********************************************************************)

definition user_accessible:: "('a::len0) sparc_state \<Rightarrow> phys_address \<Rightarrow> bool" where
"user_accessible s pa \<equiv> \<exists>va p. (virt_to_phys va (mmu s) (mem s)) = Some p \<and>
  mmu_readable (get_acc_flag (snd p)) 10 \<and>
  (fst p) = pa" \<comment> \<open>Passing \<open>asi = 8\<close> is the same.\<close>

lemma user_accessible_8: 
assumes a1: "mmu_readable (get_acc_flag (snd p)) 8"
shows "mmu_readable (get_acc_flag (snd p)) 10"
using a1 by (simp add: mmu_readable_def)

definition mem_equal:: "('a) sparc_state \<Rightarrow> ('a) sparc_state \<Rightarrow> 
  phys_address \<Rightarrow> bool" where
"mem_equal s1 s2 pa \<equiv>
  (mem s1) 8 (pa AND 68719476732) = (mem s2) 8 (pa AND 68719476732) \<and>
  (mem s1) 8 ((pa AND 68719476732) + 1) = (mem s2) 8 ((pa AND 68719476732) + 1) \<and>
  (mem s1) 8 ((pa AND 68719476732) + 2) = (mem s2) 8 ((pa AND 68719476732) + 2) \<and>
  (mem s1) 8 ((pa AND 68719476732) + 3) = (mem s2) 8 ((pa AND 68719476732) + 3) \<and>
  (mem s1) 9 (pa AND 68719476732) = (mem s2) 9 (pa AND 68719476732) \<and>
  (mem s1) 9 ((pa AND 68719476732) + 1) = (mem s2) 9 ((pa AND 68719476732) + 1) \<and>
  (mem s1) 9 ((pa AND 68719476732) + 2) = (mem s2) 9 ((pa AND 68719476732) + 2) \<and>
  (mem s1) 9 ((pa AND 68719476732) + 3) = (mem s2) 9 ((pa AND 68719476732) + 3) \<and>
  (mem s1) 10 (pa AND 68719476732) = (mem s2) 10 (pa AND 68719476732) \<and>
  (mem s1) 10 ((pa AND 68719476732) + 1) = (mem s2) 10 ((pa AND 68719476732) + 1) \<and>
  (mem s1) 10 ((pa AND 68719476732) + 2) = (mem s2) 10 ((pa AND 68719476732) + 2) \<and>
  (mem s1) 10 ((pa AND 68719476732) + 3) = (mem s2) 10 ((pa AND 68719476732) + 3) \<and>
  (mem s1) 11 (pa AND 68719476732) = (mem s2) 11 (pa AND 68719476732) \<and>
  (mem s1) 11 ((pa AND 68719476732) + 1) = (mem s2) 11 ((pa AND 68719476732) + 1) \<and>
  (mem s1) 11 ((pa AND 68719476732) + 2) = (mem s2) 11 ((pa AND 68719476732) + 2) \<and>
  (mem s1) 11 ((pa AND 68719476732) + 3) = (mem s2) 11 ((pa AND 68719476732) + 3)"

text \<open>\<open>low_equal\<close> defines the equivalence relation over two sparc
states that is an analogy to the \<open>=\<^sub>L\<close> relation over memory contexts
in the traditional non-interference theorem.\<close>

definition low_equal:: "('a::len0) sparc_state \<Rightarrow> ('a) sparc_state \<Rightarrow> bool" where
"low_equal s1 s2 \<equiv> 
  (cpu_reg s1) = (cpu_reg s2) \<and>
  (user_reg s1) = (user_reg s2) \<and>
  (sys_reg s1) = (sys_reg s2) \<and>  
  (\<forall>va. (virt_to_phys va (mmu s1) (mem s1)) = (virt_to_phys va (mmu s2) (mem s2))) \<and>
  (\<forall>pa. (user_accessible s1 pa) \<longrightarrow> mem_equal s1 s2 pa) \<and>  
  (mmu s1) = (mmu s2) \<and> 
  (state_var s1) = (state_var s2) \<and>
  (traps s1) = (traps s2) \<and>
  (undef s1) = (undef s2)
" 

lemma low_equal_com: "low_equal s1 s2 \<Longrightarrow> low_equal s2 s1"
apply (simp add: low_equal_def)
apply (simp add: mem_equal_def user_accessible_def)
by metis

lemma non_exe_mode_equal: "exe_mode_val s = False \<and>
get_trap_set s = {} \<and>
Some t = NEXT s \<Longrightarrow> 
t = s"
apply (simp add: NEXT_def execute_instruction_def)
apply auto
by (simp add: simpler_gets_def bind_def h1_def h2_def Let_def return_def)

lemma exe_mode_low_equal:
assumes a1: "low_equal s1 s2"
shows " exe_mode_val s1 =  exe_mode_val s2"
using a1 apply (simp add: low_equal_def)
by (simp add: exe_mode_val_def)

lemma mem_val_mod_state: "mem_val_alt asi a s = mem_val_alt asi a 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>)"
apply (simp add: mem_val_alt_def)
by (simp add: Let_def)

lemma mem_val_w32_mod_state: "mem_val_w32 asi a s = mem_val_w32 asi a 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>)"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
by (metis mem_val_mod_state)

lemma load_word_mem_mod_state: "load_word_mem s addr asi = load_word_mem 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi"
apply (simp add: load_word_mem_def)
apply (case_tac "virt_to_phys addr (mmu s) (mem s) = None")
 apply auto
by (auto simp add: mem_val_w32_mod_state)

lemma load_word_mem2_mod_state: 
"fst (case load_word_mem s addr asi of None \<Rightarrow> (None, s)
      | Some w \<Rightarrow> (Some w, add_data_cache s addr w 15)) =
 fst (case load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi of
         None \<Rightarrow> (None, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>))
      | Some w \<Rightarrow> (Some w, add_data_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr w 15))"
proof (cases "load_word_mem s addr asi = None")
  case True
  then have "load_word_mem s addr asi = None \<and>
    load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi = None"
    using load_word_mem_mod_state by metis
  then show ?thesis by auto
next
  case False
  then have "\<exists>w. load_word_mem s addr asi = Some w" by auto
  then have "\<exists>w. load_word_mem s addr asi = Some w \<and> 
    load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi = Some w"
  using load_word_mem_mod_state by metis
  then show ?thesis by auto
qed

lemma load_word_mem3_mod_state: 
"fst (case load_word_mem s addr asi of None \<Rightarrow> (None, s)
      | Some w \<Rightarrow> (Some w, add_instr_cache s addr w 15)) =
 fst (case load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi of
         None \<Rightarrow> (None, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>))
      | Some w \<Rightarrow> (Some w, add_instr_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr w 15))"
proof (cases "load_word_mem s addr asi = None")
  case True
  then have "load_word_mem s addr asi = None \<and>
    load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi = None"
    using load_word_mem_mod_state by metis
  then show ?thesis by auto
next
  case False
  then have "\<exists>w. load_word_mem s addr asi = Some w" by auto
  then have "\<exists>w. load_word_mem s addr asi = Some w \<and> 
    load_word_mem (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr asi = Some w"
  using load_word_mem_mod_state by metis
  then show ?thesis by auto
qed

lemma read_dcache_mod_state: "read_data_cache s addr = read_data_cache 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr"
apply (simp add: read_data_cache_def)
by (simp add: dcache_val_def)

lemma read_dcache2_mod_state: 
"fst (case read_data_cache s addr of None \<Rightarrow> (None, s)
      | Some w \<Rightarrow> (Some w, s)) =
 fst (case read_data_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr of
         None \<Rightarrow> (None, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>))
      | Some w \<Rightarrow> (Some w, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>)))"
proof (cases "read_data_cache s addr = None")
  case True
  then have "read_data_cache s addr = None \<and>
    read_data_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr = None"
    using read_dcache_mod_state by metis
  then show ?thesis by auto    
next
  case False
  then have "\<exists>w. read_data_cache s addr = Some w" by auto
  then have "\<exists>w. read_data_cache s addr = Some w \<and> 
    read_data_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr = Some w"
    using read_dcache_mod_state by metis
  then show ?thesis by auto
qed

lemma read_icache_mod_state: "read_instr_cache s addr = read_instr_cache 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr"
apply (simp add: read_instr_cache_def)
by (simp add: icache_val_def)

lemma read_icache2_mod_state: 
"fst (case read_instr_cache s addr of None \<Rightarrow> (None, s)
      | Some w \<Rightarrow> (Some w, s)) =
 fst (case read_instr_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr of
         None \<Rightarrow> (None, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>))
      | Some w \<Rightarrow> (Some w, (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>)))"
proof (cases "read_instr_cache s addr = None")
  case True
  then have "read_instr_cache s addr = None \<and>
    read_instr_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr = None"
    using read_icache_mod_state by metis
  then show ?thesis by auto    
next
  case False
  then have "\<exists>w. read_instr_cache s addr = Some w" by auto
  then have "\<exists>w. read_instr_cache s addr = Some w \<and> 
    read_instr_cache (s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) addr = Some w"
    using read_icache_mod_state by metis
  then show ?thesis by auto
qed

lemma mem_read_mod_state: "fst (memory_read asi addr s) =
fst (memory_read asi addr 
(s\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>))"
apply (simp add: memory_read_def)
apply (case_tac "uint asi = 1")
 apply (simp add: Let_def)
 apply (metis load_word_mem_mod_state option.distinct(1))
apply (case_tac "uint asi = 2")
 apply (simp add: Let_def)
 apply (simp add: sys_reg_val_def)
apply (case_tac "uint asi \<in> {8,9}")
 apply (simp add: Let_def)
 apply (simp add: load_word_mem3_mod_state)
 apply (simp add: load_word_mem_mod_state)
apply (case_tac "uint asi \<in> {10,11}")
 apply (simp add: Let_def)
 apply (simp add: load_word_mem2_mod_state)
 apply (simp add: load_word_mem_mod_state)
apply (case_tac "uint asi = 13")
 apply (simp add: Let_def)
 apply (simp add: read_icache2_mod_state)
apply (case_tac "uint asi = 15")
 apply (simp add: Let_def)
 apply (simp add: read_dcache2_mod_state)
apply (case_tac "uint asi = 25")
 apply (simp add: Let_def)
apply (case_tac "uint asi = 28")
 apply (simp add: Let_def)
 apply (simp add: mem_val_w32_mod_state)
by (simp add: Let_def)

lemma insert_trap_mem: "fst (memory_read asi addr s) =
fst (memory_read asi addr (s\<lparr>traps := new_traps\<rparr>))"
proof -
  have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := (cpu_reg s),
         user_reg := (user_reg s),
         dwrite := (dwrite s),
         state_var := (state_var s),
         traps := new_traps,
         undef := (undef s)\<rparr>))"
    using mem_read_mod_state by blast
    then show ?thesis by auto
qed

lemma cpu_reg_mod_mem: "fst (memory_read asi addr s) =
fst (memory_read asi addr (s\<lparr>cpu_reg := new_cpu_reg\<rparr>))"
proof -
  have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := new_cpu_reg,
         user_reg := (user_reg s),
         dwrite := (dwrite s),
         state_var := (state_var s),
         traps := (traps s),
         undef := (undef s)\<rparr>))"
    using mem_read_mod_state by blast
    then show ?thesis by auto
qed

lemma user_reg_mod_mem: "fst (memory_read asi addr s) =
fst (memory_read asi addr (s\<lparr>user_reg := new_user_reg\<rparr>))"
proof -
  have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := (cpu_reg s),
         user_reg := new_user_reg,
         dwrite := (dwrite s),
         state_var := (state_var s),
         traps := (traps s),
         undef := (undef s)\<rparr>))"
    using mem_read_mod_state by blast
    then show ?thesis by auto
qed

lemma annul_mem: "fst (memory_read asi addr s) =
fst (memory_read asi addr 
(s\<lparr>state_var := new_state_var,
   cpu_reg := new_cpu_reg\<rparr>))"
proof -
  have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := new_cpu_reg,
         user_reg := (user_reg s),
         dwrite := (dwrite s),
         state_var := new_state_var,
         traps := (traps s),
         undef := (undef s)\<rparr>))"
    using mem_read_mod_state by blast
  then have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := new_cpu_reg,
         state_var := new_state_var\<rparr>))"
    by auto        
  then show ?thesis 
    by (metis Sparc_State.sparc_state.surjective Sparc_State.sparc_state.update_convs(1) Sparc_State.sparc_state.update_convs(8))
qed

lemma state_var_mod_mem: "fst (memory_read asi addr s) =
fst (memory_read asi addr (s\<lparr>state_var := new_state_var\<rparr>))"
proof -
  have "fst (memory_read asi addr s) =
    fst (memory_read asi addr 
      (s\<lparr>cpu_reg := (cpu_reg s),
         user_reg := (user_reg s),
         dwrite := (dwrite s),
         state_var := new_state_var,
         traps := (traps s),
         undef := (undef s)\<rparr>))"
    using mem_read_mod_state by blast
    then show ?thesis by auto
qed

lemma mod_state_low_equal: "low_equal s1 s2 \<and>
t1 = (s1\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) \<and>
t2 = (s2\<lparr>cpu_reg := new_cpu_reg,
   user_reg := new_user_reg,
   dwrite := new_dwrite,
   state_var := new_state_var,
   traps := new_traps,
   undef := new_undef\<rparr>) \<Longrightarrow>
low_equal t1 t2"
apply (simp add: low_equal_def)
apply clarsimp
apply (simp add: mem_equal_def)
by (simp add: user_accessible_def)

lemma user_reg_state_mod_low_equal: 
assumes a1: "low_equal s1 s2 \<and>           
t1 = (s1\<lparr>user_reg := new_user_reg\<rparr>) \<and>
t2 = (s2\<lparr>user_reg := new_user_reg\<rparr>)"
shows "low_equal t1 t2"
proof -
  have "low_equal s1 s2 \<and>
t1 = (s1\<lparr>cpu_reg := (cpu_reg s1),
   user_reg := new_user_reg,
   dwrite := (dwrite s1),
   state_var := (state_var s1),
   traps := (traps s1),
   undef := (undef s1)\<rparr>) \<and>
t2 = (s2\<lparr>cpu_reg := (cpu_reg s2),
   user_reg := new_user_reg,
   dwrite := (dwrite s2),
   state_var := (state_var s2),
   traps := (traps s2),
   undef := (undef s2)\<rparr>) \<Longrightarrow>
low_equal t1 t2"
    using mod_state_low_equal apply (simp add: low_equal_def)    
    apply (simp add: user_accessible_def mem_equal_def)
    by clarsimp
  then show ?thesis using a1
  by clarsimp
qed

lemma mod_trap_low_equal: 
assumes a1: "low_equal s1 s2 \<and>           
t1 = (s1\<lparr>traps := new_traps\<rparr>) \<and>
t2 = (s2\<lparr>traps := new_traps\<rparr>)"
shows "low_equal t1 t2"
proof -
  have "low_equal s1 s2 \<and>
t1 = (s1\<lparr>cpu_reg := (cpu_reg s1),
   user_reg := (user_reg s1),
   dwrite := (dwrite s1),
   state_var := (state_var s1),
   traps := new_traps,
   undef := (undef s1)\<rparr>) \<and>
t2 = (s2\<lparr>cpu_reg := (cpu_reg s2),
   user_reg := (user_reg s2),
   dwrite := (dwrite s2),
   state_var := (state_var s2),
   traps := new_traps,
   undef := (undef s2)\<rparr>) \<Longrightarrow>
low_equal t1 t2"
    using mod_state_low_equal apply (simp add: low_equal_def)
    apply (simp add: user_accessible_def mem_equal_def)
    by clarsimp
  then show ?thesis using a1
  by clarsimp
qed

lemma state_var_low_equal: "low_equal s1 s2 \<Longrightarrow>
state_var s1 = state_var s2"
by (simp add: low_equal_def)

lemma state_var2_low_equal: 
assumes a1: "low_equal s1 s2 \<and>           
t1 = (s1\<lparr>state_var := new_state_var\<rparr>) \<and>
t2 = (s2\<lparr>state_var := new_state_var\<rparr>)"
shows "low_equal t1 t2"
proof -
  have "low_equal s1 s2 \<and>
t1 = (s1\<lparr>cpu_reg := (cpu_reg s1),
   user_reg := (user_reg s1),
   dwrite := (dwrite s1),
   state_var := new_state_var,
   traps := (traps s1),
   undef := (undef s1)\<rparr>) \<and>
t2 = (s2\<lparr>cpu_reg := (cpu_reg s2),
   user_reg := (user_reg s2),
   dwrite := (dwrite s2),
   state_var := new_state_var,
   traps := (traps s2),
   undef := (undef s2)\<rparr>) \<Longrightarrow>
low_equal t1 t2"
    using mod_state_low_equal apply (simp add: low_equal_def)
    apply (simp add: user_accessible_def mem_equal_def)
    by clarsimp   
  then show ?thesis using a1
  by clarsimp
qed

lemma traps_low_equal: "low_equal s1 s2 \<Longrightarrow> traps s1 = traps s2"
by (simp add: low_equal_def)

lemma s_low_equal: "low_equal s1 s2 \<Longrightarrow>
(get_S (cpu_reg_val PSR s1)) = (get_S (cpu_reg_val PSR s2))"
by (simp add: low_equal_def cpu_reg_val_def)

lemma cpu_reg_val_low_equal: "low_equal s1 s2 \<Longrightarrow>
(cpu_reg_val cr s1) = (cpu_reg_val cr s2)"
by (simp add: cpu_reg_val_def low_equal_def)

lemma get_curr_win_low_equal: "low_equal s1 s2 \<Longrightarrow>
(fst (fst (get_curr_win () s1))) = (fst (fst (get_curr_win () s2)))"
apply (simp add: low_equal_def)
apply (simp add: get_curr_win_def cpu_reg_val_def get_CWP_def)
by (simp add: simpler_gets_def)

lemma get_curr_win2_low_equal: "low_equal s1 s2 \<Longrightarrow>
t1 = (snd (fst (get_curr_win () s1))) \<Longrightarrow>
t2 = (snd (fst (get_curr_win () s2))) \<Longrightarrow>
low_equal t1 t2"
apply (simp add: low_equal_def)
apply (simp add: get_curr_win_def cpu_reg_val_def get_CWP_def)
by (auto simp add: simpler_gets_def)

lemma get_curr_win3_low_equal: "low_equal s1 s2 \<Longrightarrow>
(traps (snd (fst (get_curr_win () s1)))) =
(traps (snd (fst (get_curr_win () s2))))"
using low_equal_def get_curr_win2_low_equal by blast

lemma get_addr_low_equal: "low_equal s1 s2 \<Longrightarrow>
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) =
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<and>
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) =
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<and>
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) =
((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word1)"
apply (simp add: low_equal_def)
apply (simp add: get_curr_win_def cpu_reg_val_def get_CWP_def)
apply (simp add: simpler_gets_def get_addr_def user_reg_val_def)
apply (simp add: Let_def )
apply (simp add: get_CWP_def cpu_reg_val_def get_operand2_def)
by (simp add: user_reg_val_def)

lemma get_addr2_low_equal: "low_equal s1 s2 \<Longrightarrow>
get_addr (snd instr) (snd (fst (get_curr_win () s1))) =
get_addr (snd instr) (snd (fst (get_curr_win () s2)))"
apply (simp add: low_equal_def)
apply (simp add: get_curr_win_def cpu_reg_val_def get_CWP_def)
apply (simp add: simpler_gets_def get_addr_def user_reg_val_def)
apply (simp add: Let_def )
apply (simp add: get_CWP_def cpu_reg_val_def get_operand2_def)
by (simp add: user_reg_val_def)

lemma sys_reg_low_equal: "low_equal s1 s2 \<Longrightarrow>
sys_reg s1 = sys_reg s2"
by (simp add: low_equal_def)

lemma user_reg_low_equal: "low_equal s1 s2 \<Longrightarrow>
user_reg s1 = user_reg s2"
by (simp add: low_equal_def)

lemma user_reg_val_low_equal: "low_equal s1 s2 \<Longrightarrow>
user_reg_val win ur s1 = user_reg_val win ur s2"
apply (simp add: user_reg_val_def)
by (simp add: user_reg_low_equal)

lemma get_operand2_low_equal: "low_equal s1 s2 \<Longrightarrow>
get_operand2 op_list s1 = get_operand2 op_list s2"
apply (simp add: get_operand2_def)
apply (simp add: cpu_reg_val_low_equal)
apply auto
apply (simp add: user_reg_val_def)
using user_reg_low_equal by fastforce

lemma mem_val_mod_cache: "mem_val_alt asi a s = 
mem_val_alt asi a (s\<lparr>cache := new_cache\<rparr>)"
apply (simp add: mem_val_alt_def)
by (simp add: Let_def)

lemma mem_val_w32_mod_cache: "mem_val_w32 asi a s = 
mem_val_w32 asi a (s\<lparr>cache := new_cache\<rparr>)"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
by (metis mem_val_mod_cache)

lemma load_word_mem_mod_cache: 
"load_word_mem s addr asi =
load_word_mem (s\<lparr>cache := new_cache\<rparr>) addr asi"
apply (simp add: load_word_mem_def)
apply (case_tac "virt_to_phys addr (mmu s) (mem s) = None")
 apply auto
by (simp add: mem_val_w32_mod_cache)

lemma memory_read_8_mod_cache:
"fst (memory_read 8 addr s) = fst (memory_read 8 addr (s\<lparr>cache := new_cache\<rparr>))"
apply (simp add: memory_read_def)
apply (case_tac "sys_reg s CCR AND 1 \<noteq> 0")
 apply auto
 apply (simp add: option.case_eq_if load_word_mem_mod_cache)
 apply (auto intro: load_word_mem_mod_cache)
 apply (metis load_word_mem_mod_cache option.distinct(1))
by (metis load_word_mem_mod_cache option.distinct(1))

lemma memory_read_10_mod_cache:
"fst (memory_read 10 addr s) = fst (memory_read 10 addr (s\<lparr>cache := new_cache\<rparr>))"
apply (simp add: memory_read_def)
apply (case_tac "sys_reg s CCR AND 1 \<noteq> 0")
 apply auto
 apply (simp add: option.case_eq_if load_word_mem_mod_cache)
 apply (auto intro: load_word_mem_mod_cache)
 apply (metis load_word_mem_mod_cache option.distinct(1))
by (metis load_word_mem_mod_cache option.distinct(1))

lemma mem_equal_mod_cache: "mem_equal s1 s2 pa \<Longrightarrow>
mem_equal (s1\<lparr>cache := new_cache1\<rparr>) (s2\<lparr>cache := new_cache2\<rparr>) pa"
by (simp add: mem_equal_def)

lemma user_accessible_mod_cache: "user_accessible (s\<lparr>cache := new_cache\<rparr>) pa =
user_accessible s pa"
by (simp add: user_accessible_def)

lemma mem_equal_mod_user_reg: "mem_equal s1 s2 pa \<Longrightarrow>
mem_equal (s1\<lparr>user_reg := new_user_reg1\<rparr>) (s2\<lparr>user_reg := user_reg2\<rparr>) pa"
by (simp add: mem_equal_def)

lemma user_accessible_mod_user_reg: "user_accessible (s\<lparr>user_reg := new_user_reg\<rparr>) pa =
user_accessible s pa"
by (simp add: user_accessible_def)

lemma mem_equal_mod_cpu_reg: "mem_equal s1 s2 pa \<Longrightarrow>
mem_equal (s1\<lparr>cpu_reg := new_cpu1\<rparr>) (s2\<lparr>cpu_reg := cpu_reg2\<rparr>) pa"
by (simp add: mem_equal_def)

lemma user_accessible_mod_cpu_reg: "user_accessible (s\<lparr>cpu_reg := new_cpu_reg\<rparr>) pa =
user_accessible s pa"
by (simp add: user_accessible_def)

lemma mem_equal_mod_trap: "mem_equal s1 s2 pa \<Longrightarrow>
mem_equal (s1\<lparr>traps := new_traps1\<rparr>) (s2\<lparr>traps := traps2\<rparr>) pa"
by (simp add: mem_equal_def)

lemma user_accessible_mod_trap: "user_accessible (s\<lparr>traps := new_traps\<rparr>) pa =
user_accessible s pa"
by (simp add: user_accessible_def)

lemma mem_equal_annul: "mem_equal s1 s2 pa \<Longrightarrow>
mem_equal (s1\<lparr>state_var := new_state_var,
   cpu_reg := new_cpu_reg\<rparr>) (s2\<lparr>state_var := new_state_var2,
   cpu_reg := new_cpu_reg2\<rparr>) pa"
by (simp add: mem_equal_def)

lemma user_accessible_annul: "user_accessible (s\<lparr>state_var := new_state_var, 
  cpu_reg := new_cpu_reg\<rparr>) pa =
user_accessible s pa"
by (simp add: user_accessible_def)

lemma mem_val_alt_10_mem_equal_0: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 10 (pa AND 68719476732) s1 = mem_val_alt 10 (pa AND 68719476732) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_mem_equal_1: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 10 ((pa AND 68719476732) + 1) s1 = mem_val_alt 10 ((pa AND 68719476732) + 1) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_mem_equal_2: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 10 ((pa AND 68719476732) + 2) s1 = mem_val_alt 10 ((pa AND 68719476732) + 2) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_mem_equal_3: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 10 ((pa AND 68719476732) + 3) s1 = mem_val_alt 10 ((pa AND 68719476732) + 3) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_mem_equal: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 (pa AND 68719476732) s1 = mem_val_alt 10 (pa AND 68719476732) s2 \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 1) s1 = mem_val_alt 10 ((pa AND 68719476732) + 1) s2 \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 2) s1 = mem_val_alt 10 ((pa AND 68719476732) + 2) s2 \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 3) s1 = mem_val_alt 10 ((pa AND 68719476732) + 3) s2"
using mem_val_alt_10_mem_equal_0 mem_val_alt_10_mem_equal_1
mem_val_alt_10_mem_equal_2 mem_val_alt_10_mem_equal_3 a1
by blast

lemma mem_val_w32_10_mem_equal: 
assumes a1: "mem_equal s1 s2 a"
shows "mem_val_w32 10 a s1 = mem_val_w32 10 a s2"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
using mem_val_alt_10_mem_equal a1 apply auto
        apply fastforce 
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
 apply fastforce
by fastforce

lemma mem_val_alt_8_mem_equal_0: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 8 (pa AND 68719476732) s1 = mem_val_alt 8 (pa AND 68719476732) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_mem_equal_1: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 8 ((pa AND 68719476732) + 1) s1 = mem_val_alt 8 ((pa AND 68719476732) + 1) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_mem_equal_2: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 8 ((pa AND 68719476732) + 2) s1 = mem_val_alt 8 ((pa AND 68719476732) + 2) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_mem_equal_3: "mem_equal s1 s2 pa \<Longrightarrow>
mem_val_alt 8 ((pa AND 68719476732) + 3) s1 = mem_val_alt 8 ((pa AND 68719476732) + 3) s2"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_mem_equal: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 (pa AND 68719476732) s1 = mem_val_alt 8 (pa AND 68719476732) s2 \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 1) s1 = mem_val_alt 8 ((pa AND 68719476732) + 1) s2 \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 2) s1 = mem_val_alt 8 ((pa AND 68719476732) + 2) s2 \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 3) s1 = mem_val_alt 8 ((pa AND 68719476732) + 3) s2"
using mem_val_alt_8_mem_equal_0 mem_val_alt_8_mem_equal_1
mem_val_alt_8_mem_equal_2 mem_val_alt_8_mem_equal_3 a1
by blast

lemma mem_val_w32_8_mem_equal: 
assumes a1: "mem_equal s1 s2 a"
shows "mem_val_w32 8 a s1 = mem_val_w32 8 a s2"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
using mem_val_alt_8_mem_equal a1 apply auto
        apply fastforce 
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
 apply fastforce
by fastforce

lemma load_word_mem_10_low_equal: 
assumes a1: "low_equal s1 s2"
shows "load_word_mem s1 address 10 = load_word_mem s2 address 10"
using a1 apply (simp add: low_equal_def load_word_mem_def)
apply clarsimp
apply (case_tac "virt_to_phys address (mmu s2) (mem s2) = None")
 apply auto
 apply (simp add: user_accessible_def)
 using mem_val_w32_10_mem_equal apply blast 
apply (simp add: user_accessible_def)
using mem_val_w32_10_mem_equal by blast 

lemma load_word_mem_8_low_equal: 
assumes a1: "low_equal s1 s2"
shows "load_word_mem s1 address 8 = load_word_mem s2 address 8"
using a1 apply (simp add: low_equal_def load_word_mem_def)
apply clarsimp
apply (case_tac "virt_to_phys address (mmu s2) (mem s2) = None")
 apply auto
 apply (simp add: user_accessible_def)
 using mem_val_w32_8_mem_equal user_accessible_8 apply fastforce
apply (simp add: user_accessible_def)
using mem_val_w32_8_mem_equal user_accessible_8 by fastforce

lemma mem_read_low_equal: 
assumes a1: "low_equal s1 s2 \<and> asi \<in> {8,10}"
shows "fst (memory_read asi address s1) = fst (memory_read asi address s2)"
proof (cases "asi = 8")
  case True
  then show ?thesis using a1 
  apply (simp add: low_equal_def)
  apply (simp add: memory_read_def)
  using a1 load_word_mem_8_low_equal apply auto
  apply (simp add: option.case_eq_if)
  by (simp add: option.case_eq_if)
next
  case False
  then have "asi = 10" using a1 by auto
  then show ?thesis using a1
  apply (simp add: low_equal_def)
  apply (simp add: memory_read_def)
  using a1 load_word_mem_10_low_equal apply auto
  apply (simp add: option.case_eq_if)
  by (simp add: option.case_eq_if)
qed 

lemma read_mem_pc_low_equal: 
assumes a1: "low_equal s1 s2"
shows "fst (memory_read 8 (cpu_reg_val PC s1) s1) = 
fst (memory_read 8 (cpu_reg_val PC s2) s2)"
proof -
  have f2: "cpu_reg_val PC s1 = cpu_reg_val PC s2" using a1 
    by (simp add: low_equal_def cpu_reg_val_def)
  then show ?thesis using a1 f2 mem_read_low_equal
    by auto
qed

lemma dcache_mod_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = dcache_mod c v s1 \<and>
t2 = dcache_mod c v s2"
shows "low_equal t1 t2"
using a1 apply (simp add: low_equal_def)
apply (simp add: dcache_mod_def)
apply auto
 apply (simp add: user_accessible_mod_cache mem_equal_mod_cache)
by (simp add: user_accessible_mod_cache mem_equal_mod_cache)

lemma add_data_cache_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = add_data_cache s1 address w bm \<and>
t2 = add_data_cache s2 address w bm"
shows "low_equal t1 t2"
using a1 apply (simp add: add_data_cache_def)
apply (case_tac "bm AND 8 >> 3 = 1")
 apply auto
 apply (case_tac "bm AND 4 >> 2 = 1")
  apply auto
  apply (case_tac "bm AND 2 >> Suc 0 = 1")
   apply auto
   apply (case_tac "bm AND 1 = 1")
    apply auto
    apply (meson dcache_mod_low_equal)
   apply (meson dcache_mod_low_equal)
  apply (case_tac "bm AND 1 = 1")
   apply auto
   apply (meson dcache_mod_low_equal)
  apply (meson dcache_mod_low_equal)
 apply (case_tac "bm AND 2 >> Suc 0 = 1")
  apply auto
  apply (case_tac "bm AND 1 = 1")
   apply auto
   apply (meson dcache_mod_low_equal)
  apply (meson dcache_mod_low_equal)
 apply (case_tac "bm AND 1 = 1")
  apply auto
  apply (meson dcache_mod_low_equal)
 apply (meson dcache_mod_low_equal)
apply (case_tac "bm AND 4 >> 2 = 1")
 apply auto
 apply (case_tac "bm AND 2 >> Suc 0 = 1")
  apply auto
  apply (case_tac "bm AND 1 = 1")
   apply auto
   apply (meson dcache_mod_low_equal)
  apply (meson dcache_mod_low_equal)
 apply (case_tac "bm AND 1 = 1")
  apply auto
  apply (meson dcache_mod_low_equal)
 apply (meson dcache_mod_low_equal)
apply (case_tac "bm AND 2 >> Suc 0 = 1")
 apply auto
 apply (case_tac "bm AND 1 = 1")
  apply auto
  apply (meson dcache_mod_low_equal)
 apply (meson dcache_mod_low_equal)
by (meson dcache_mod_low_equal)

lemma mem_read2_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (memory_read (10::word8) address s1) \<and>
t2 = snd (memory_read (10::word8) address s2)"
shows "low_equal t1 t2"
using a1 apply (simp add: memory_read_def)
using a1 apply (auto simp add: sys_reg_low_equal)
using a1 apply (simp add: load_word_mem_10_low_equal)
by (metis (no_types, lifting) add_data_cache_low_equal option.case_eq_if snd_conv)

lemma mem_read_delayed_write_low_equal:
assumes a1: "low_equal s1 s2 \<and> get_delayed_pool s1 = [] \<and> get_delayed_pool s2 = []"
shows "fst (memory_read 8 (cpu_reg_val PC (delayed_pool_write s1)) (delayed_pool_write s1)) =
fst (memory_read 8 (cpu_reg_val PC (delayed_pool_write s2)) (delayed_pool_write s2))"
using a1 apply (simp add: delayed_pool_write_def)
apply (simp add: Let_def)
apply (simp add: get_delayed_write_def)
by (simp add: read_mem_pc_low_equal)

lemma global_reg_mod_low_equal: 
assumes a1: "low_equal s1 s2\<and>
t1 = (global_reg_mod w n rd s1) \<and>
t2 = (global_reg_mod w n rd s2)"
shows "low_equal t1 t2"
using a1 apply (induction n arbitrary: s1 s2)
 apply clarsimp
apply auto
apply (simp add: Let_def)
apply (simp add: user_reg_low_equal)
using user_reg_state_mod_low_equal by blast

lemma out_reg_mod_low_equal: 
assumes a1: "low_equal s1 s2\<and>
t1 = (out_reg_mod w curr_win rd s1) \<and>
t2 = (out_reg_mod w curr_win rd s2)"
shows "low_equal t1 t2"
using a1 apply (simp add: out_reg_mod_def Let_def)
apply auto
 apply (simp add: user_reg_low_equal)
 using user_reg_state_mod_low_equal apply fastforce
apply (simp add: user_reg_low_equal)
using user_reg_state_mod_low_equal by blast

lemma in_reg_mod_low_equal: 
assumes a1: "low_equal s1 s2\<and>
t1 = (in_reg_mod w curr_win rd s1) \<and>
t2 = (in_reg_mod w curr_win rd s2)"
shows "low_equal t1 t2"
using a1 apply (simp add: in_reg_mod_def Let_def)
apply auto
 apply (simp add: user_reg_low_equal)
 using user_reg_state_mod_low_equal apply fastforce
apply (simp add: user_reg_low_equal)
using user_reg_state_mod_low_equal by blast

lemma user_reg_mod_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = user_reg_mod w curr_win rd s1 \<and> t2 = user_reg_mod w curr_win rd s2"
shows "low_equal t1 t2"
proof (cases "rd = 0")
  case True
  then show ?thesis using a1
  by (simp add: user_reg_mod_def)
next
  case False
  then have f1: "rd \<noteq> 0" by auto
  then show ?thesis 
  proof (cases "0 < rd \<and> rd < 8")
    case True
    then show ?thesis using a1 f1
    apply (simp add: user_reg_mod_def)
    using global_reg_mod_low_equal by blast    
  next
    case False
    then have f2: "\<not> (0 < rd \<and> rd < 8)" by auto
    then show ?thesis  
    proof (cases "7 < rd \<and> rd < 16")
      case True
      then show ?thesis using a1 f1 f2
      apply (simp add: user_reg_mod_def)
      by (auto intro: out_reg_mod_low_equal)
    next
      case False
      then have f3: "\<not> (7 < rd \<and> rd < 16)" by auto      
      then show ?thesis 
      proof (cases "15 < rd \<and> rd < 24")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: user_reg_mod_def)
        apply (simp add: low_equal_def)
        apply clarsimp
        by (simp add: user_accessible_mod_user_reg mem_equal_mod_user_reg)     
      next
        case False
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: user_reg_mod_def)
        by (auto intro: in_reg_mod_low_equal)
      qed
    qed
  qed
qed

lemma virt_to_phys_low_equal: "low_equal s1 s2 \<Longrightarrow>
virt_to_phys addr (mmu s1) (mem s1) = virt_to_phys addr (mmu s2) (mem s2)"
by (auto simp add: low_equal_def)

lemma write_reg_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = (snd (fst (write_reg w curr_win rd s1))) \<and>
t2 = (snd (fst (write_reg w curr_win rd s2)))"
shows "low_equal t1 t2"
using a1 apply (simp add: write_reg_def)
apply (simp add: simpler_modify_def)
by (auto intro: user_reg_mod_low_equal)

lemma write_cpu_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (write_cpu w cr s1)) \<and>
t2 = (snd (fst (write_cpu w cr s2)))"
shows "low_equal t1 t2"
using a1
apply (simp add: write_cpu_def simpler_modify_def)
apply (simp add: cpu_reg_mod_def)
apply (simp add: low_equal_def)
using user_accessible_mod_cpu_reg mem_equal_mod_cpu_reg
by metis

lemma cpu_reg_mod_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = cpu_reg_mod w cr s1 \<and>
t2 = cpu_reg_mod w cr s2"
shows "low_equal t1 t2"
using a1
apply (simp add: cpu_reg_mod_def)
apply (simp add: low_equal_def)
using user_accessible_mod_cpu_reg mem_equal_mod_cpu_reg
by metis

lemma load_sub2_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = (snd (fst (load_sub2 address 10 rd curr_win w s1))) \<and>
t2 = (snd (fst (load_sub2 address 10 rd curr_win w s2)))"
shows "low_equal t1 t2"
proof (cases "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) = None")
  case True
  then have f0: "fst (memory_read 10 (address + 4) 
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) = None" by auto
  have f1: "low_equal (snd (fst (write_reg w curr_win (rd AND 30) s1)))
          (snd (fst (write_reg w curr_win (rd AND 30) s2)))"
    using a1 by (auto intro: write_reg_low_equal)
  then have "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) = None \<and>
        fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) =
        fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s2))))"
    using f0 by (blast intro: mem_read_low_equal)
  then have "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) = None \<and>
        fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s2)))) = None"
    by auto
  then show ?thesis using a1
  apply (simp add: load_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  using f1 apply (simp add: traps_low_equal)
  using f1 by (auto intro: mod_trap_low_equal)
next
  case False
  then have f2: "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) \<noteq> None"
    by auto
  have f3: "low_equal (snd (fst (write_reg w curr_win (rd AND 30) s1)))
          (snd (fst (write_reg w curr_win (rd AND 30) s2)))"
    using a1 by (auto intro: write_reg_low_equal)
  then have f4: "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) =
        fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s2))))"
    using f2 by (blast intro: mem_read_low_equal)
  then have "fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s1)))) \<noteq> None \<and>
        fst (memory_read 10 (address + 4)
        (snd (fst (write_reg w curr_win (rd AND 30) s2)))) \<noteq> None"
    using f2 by auto
  then show ?thesis using a1
  apply (simp add: load_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply clarsimp
  apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
  using f4 apply clarsimp
  using f3 by (auto intro: mem_read2_low_equal write_reg_low_equal)
qed

lemma load_sub3_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (load_sub3 instr curr_win rd (10::word8) address s1)) \<and>
t2 = snd (fst (load_sub3 instr curr_win rd (10::word8) address s2))"
shows "low_equal t1 t2"
proof (cases "fst (memory_read 10 address s1) = None")
  case True
  then have "fst (memory_read 10 address s1) = None \<and>
    fst (memory_read 10 address s2) = None"
    using a1 by (auto simp add: mem_read_low_equal)
  then show ?thesis using a1
  apply (simp add: load_sub3_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  apply (auto simp add: traps_low_equal)
  by (auto intro: mod_trap_low_equal)
next
  case False
  then have f1: "fst (memory_read 10 address s1) \<noteq> None \<and> 
    fst (memory_read 10 address s2) \<noteq> None"
    using a1 by (auto simp add: mem_read_low_equal)  
  then show ?thesis 
  proof (cases "rd \<noteq> 0 \<and>
                          (fst instr = load_store_type LD \<or>
                           fst instr = load_store_type LDA \<or>
                           fst instr = load_store_type LDUH \<or>
                           fst instr = load_store_type LDSB \<or>
                           fst instr = load_store_type LDUB \<or>
                           fst instr = load_store_type LDUBA \<or>
                           fst instr = load_store_type LDSH \<or>
                           fst instr = load_store_type LDSHA \<or>
                           fst instr = load_store_type LDUHA \<or>
                           fst instr = load_store_type LDSBA)")
    case True
    then show ?thesis using a1 f1
    apply (simp add: load_sub3_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: case_prod_unfold)
    apply clarsimp
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    apply (simp add: mem_read_low_equal)
    by (meson mem_read2_low_equal write_reg_low_equal)
  next
    case False
    then show ?thesis using a1 f1
    apply (simp add: load_sub3_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: case_prod_unfold)
    apply clarsimp
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    apply (simp add: mem_read_low_equal)
    by (meson load_sub2_low_equal mem_read2_low_equal)
  qed
qed

lemma ld_asi_user:
"(fst instr = load_store_type LDSB \<or>
fst instr = load_store_type LDUB \<or>
fst instr = load_store_type LDUH \<or> 
fst instr = load_store_type LD \<or> 
fst instr = load_store_type LDD) \<Longrightarrow> 
ld_asi instr 0 = 10"
apply (simp add: ld_asi_def)
by auto

lemma load_sub1_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
(fst instr = load_store_type LDSB \<or>
fst instr = load_store_type LDUB \<or>
fst instr = load_store_type LDUH \<or>
fst instr = load_store_type LD \<or> 
fst instr = load_store_type LDD) \<and>
t1 = snd (fst (load_sub1 instr rd 0 s1)) \<and> 
t2 = snd (fst (load_sub1 instr rd 0 s2))" 
shows "low_equal t1 t2"
proof (cases "(fst instr = load_store_type LDD \<or> fst instr = load_store_type LDDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0 \<or>
                       (fst instr = load_store_type LD \<or> fst instr = load_store_type LDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0 \<or>
                       (fst instr = load_store_type LDUH \<or>
                        fst instr = load_store_type LDUHA \<or>
                        fst instr = load_store_type LDSH \<or> fst instr = load_store_type LDSHA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0")
  case True
  then have "((fst instr = load_store_type LDD \<or> fst instr = load_store_type LDDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0 \<or>
                       (fst instr = load_store_type LD \<or> fst instr = load_store_type LDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0 \<or>
                       (fst instr = load_store_type LDUH \<or>
                        fst instr = load_store_type LDUHA \<or>
                        fst instr = load_store_type LDSH \<or> fst instr = load_store_type LDSHA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0) \<and>
            ((fst instr = load_store_type LDD \<or> fst instr = load_store_type LDDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<noteq> 0 \<or>
                       (fst instr = load_store_type LD \<or> fst instr = load_store_type LDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<noteq> 0 \<or>
                       (fst instr = load_store_type LDUH \<or>
                        fst instr = load_store_type LDUHA \<or>
                        fst instr = load_store_type LDSH \<or> fst instr = load_store_type LDSHA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word1) \<noteq> 0)"
    by (metis (mono_tags, lifting) assms get_addr_low_equal)    
  then show ?thesis using a1
  apply (simp add: load_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  apply clarsimp
  apply (simp add: get_curr_win3_low_equal)
  by (auto intro: get_curr_win2_low_equal mod_trap_low_equal)
next
  case False
  then have f1: "\<not> ((fst instr = load_store_type LDD \<or> fst instr = load_store_type LDDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0 \<or>
                       (fst instr = load_store_type LD \<or> fst instr = load_store_type LDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0 \<or>
                       (fst instr = load_store_type LDUH \<or>
                        fst instr = load_store_type LDUHA \<or>
                        fst instr = load_store_type LDSH \<or> fst instr = load_store_type LDSHA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0) \<and>
            \<not> ((fst instr = load_store_type LDD \<or> fst instr = load_store_type LDDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<noteq> 0 \<or>
                       (fst instr = load_store_type LD \<or> fst instr = load_store_type LDA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<noteq> 0 \<or>
                       (fst instr = load_store_type LDUH \<or>
                        fst instr = load_store_type LDUHA \<or>
                        fst instr = load_store_type LDSH \<or> fst instr = load_store_type LDSHA) \<and>
                       ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word1) \<noteq> 0)"
    by (metis assms get_addr_low_equal)    
  show ?thesis  
  proof -
    have "low_equal s1 s2 \<Longrightarrow> 
          low_equal (snd (fst (get_curr_win () s1))) 
                    (snd (fst (get_curr_win () s2)))"
      using get_curr_win2_low_equal by auto
    then have f2: "low_equal s1 s2 \<Longrightarrow>
      low_equal (snd (fst (load_sub3 instr (fst (fst (get_curr_win () s2))) rd 10
                    (get_addr (snd instr) (snd (fst (get_curr_win () s2))))
                    (snd (fst (get_curr_win () s1)))))) 
                (snd (fst (load_sub3 instr (fst (fst (get_curr_win () s2))) rd 10
                    (get_addr (snd instr) (snd (fst (get_curr_win () s2))))
                    (snd (fst (get_curr_win () s2))))))"
      using load_sub3_low_equal by blast 
    show ?thesis using a1
    unfolding load_sub1_def simpler_gets_def bind_def h1_def h2_def Let_def case_prod_unfold
    using f1 f2 apply clarsimp
    by (simp add: get_addr2_low_equal get_curr_win_low_equal ld_asi_user)
  qed
qed

lemma load_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
(fst instr = load_store_type LDSB \<or>
fst instr = load_store_type LDUB \<or>
fst instr = load_store_type LDUBA \<or>
fst instr = load_store_type LDUH \<or>
fst instr = load_store_type LD \<or> 
fst instr = load_store_type LDA \<or> 
fst instr = load_store_type LDD) \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
t1 = snd (fst (load_instr instr s1)) \<and> t2 = snd (fst (load_instr instr s2))"
shows "low_equal t1 t2"
proof -
  have "get_S (cpu_reg_val PSR s1) = 0 \<and> get_S (cpu_reg_val PSR s2) = 0"
    using a1 by (simp add: ucast_id) 
  then show ?thesis using a1
  apply (simp add: load_instr_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: Let_def)
  apply clarsimp
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  apply (simp add: traps_low_equal)
  by (auto intro: mod_trap_low_equal load_sub1_low_equal)
qed

lemma st_data0_low_equal: "low_equal s1 s2 \<Longrightarrow>
st_data0 instr curr_win rd addr s1 = st_data0 instr curr_win rd addr s2"
apply (simp add: st_data0_def)
by (simp add: user_reg_val_def low_equal_def)

lemma store_word_mem_low_equal_none: "low_equal s1 s2 \<Longrightarrow>
store_word_mem (add_data_cache s1 addr data bm) addr data bm 10 = None \<Longrightarrow>
store_word_mem (add_data_cache s2 addr data bm) addr data bm 10 = None"
apply (simp add: store_word_mem_def)
proof -
  assume a1: "low_equal s1 s2"
  assume a2: "(case virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) of None \<Rightarrow> None | Some pair \<Rightarrow> if mmu_writable (get_acc_flag (snd pair)) 10 then Some (mem_mod_w32 10 (fst pair) bm data (add_data_cache s1 addr data bm)) else None) = None"
  have f3: "(if mmu_writable (get_acc_flag (snd (v1_2 (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (v1_2 (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s2 addr data bm)) else None) = (case Some (v1_2 (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) of None \<Rightarrow> if mmu_writable (get_acc_flag (snd (v1_2 (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (v1_2 (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None)"
    by auto
  obtain pp :: "(word36 \<times> word8) option \<Rightarrow> word36 \<times> word8" where
    f4: "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = None \<or> virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = Some (pp (virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm))))"
    by (metis (no_types) option.exhaust)
  have f5: "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))"
    using a1 by (meson add_data_cache_low_equal virt_to_phys_low_equal)
  { assume "Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) \<noteq> (case Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s1 addr data bm)) else None)"
    then have "None = (if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s2 addr data bm)) else None)"
      by fastforce
    moreover
    { assume "(if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s2 addr data bm)) else None) \<noteq> (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None)"
      then have "(case Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) of None \<Rightarrow> if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) \<noteq> (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None)"
        using f3 by simp
      then have "Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<noteq> virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) \<or> (if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None) \<noteq> None"
      proof -
        have "(case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) = (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) \<or> Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<noteq> virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) \<or> (if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None) \<noteq> None"
          by simp
        then show ?thesis
          using \<open>(case Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) of None \<Rightarrow> if mmu_writable (get_acc_flag (snd (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))))) 10 then Some (mem_mod_w32 10 (fst (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))))) bm data (add_data_cache s1 addr data bm)) else None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) \<noteq> (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None)\<close> by force
      qed
      moreover
      { assume "Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<noteq> virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm))"
        then have "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) \<noteq> Some (pp (virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm))))"
          using f5 by simp }
      ultimately have "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) \<noteq> Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<or> virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) \<noteq> Some (pp (virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm))))"
        using a2 by force }
    ultimately have "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = Some (pp (virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)))) \<and> virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<longrightarrow> (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) = None"
      by fastforce }
  then have "virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = Some (pp (virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)))) \<and> virt_to_phys addr (mmu (add_data_cache s1 addr data bm)) (mem (add_data_cache s1 addr data bm)) = Some (pp (virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)))) \<longrightarrow> (case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) = None"
    using a2 by force
  then show "(case virt_to_phys addr (mmu (add_data_cache s2 addr data bm)) (mem (add_data_cache s2 addr data bm)) of None \<Rightarrow> None | Some p \<Rightarrow> if mmu_writable (get_acc_flag (snd p)) 10 then Some (mem_mod_w32 10 (fst p) bm data (add_data_cache s2 addr data bm)) else None) = None"
    using f5 f4 by force
qed

lemma memory_write_asi_low_equal_none: "low_equal s1 s2 \<Longrightarrow>
memory_write_asi 10 addr bm data s1 = None \<Longrightarrow>
memory_write_asi 10 addr bm data s2 = None"
apply (simp add: memory_write_asi_def)
by (simp add: store_word_mem_low_equal_none)

lemma memory_write_low_equal_none: "low_equal s1 s2 \<Longrightarrow>
memory_write 10 addr bm data s1 = None \<Longrightarrow>
memory_write 10 addr bm data s2 = None"
apply (simp add: memory_write_def)
by (metis map_option_case memory_write_asi_low_equal_none option.map_disc_iff)

lemma memory_write_low_equal_none2: "low_equal s1 s2 \<Longrightarrow>
memory_write 10 addr bm data s2 = None \<Longrightarrow>
memory_write 10 addr bm data s1 = None"
apply (simp add: memory_write_def)
by (metis low_equal_com memory_write_def memory_write_low_equal_none)

lemma mem_context_val_9_unchanged:
"mem_context_val 9 addr1 (mem s1) =
mem_context_val 9 addr1
              ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))"
apply (simp add: mem_context_val_def)
by (simp add: Let_def)

lemma mem_context_val_w32_9_unchanged:
"mem_context_val_w32 9 addr1 (mem s1) =
mem_context_val_w32 9 addr1
              ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))"
apply (simp add: mem_context_val_w32_def)
apply (simp add: Let_def)
by (metis mem_context_val_9_unchanged)

lemma ptd_lookup_unchanged_4: 
"ptd_lookup va ptp (mem s1) 4 = 
ptd_lookup va ptp ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                            11 := (mem s1 11)(addr := None))) 4"
by auto

lemma ptd_lookup_unchanged_3: 
"ptd_lookup va ptp (mem s1) 3 = 
ptd_lookup va ptp ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                            11 := (mem s1 11)(addr := None))) 3"
proof (cases "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) (mem s1) = None")
  case True
  then have "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) (mem s1) = None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36)
           ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = None"
    using mem_context_val_w32_9_unchanged by metis    
  then show ?thesis 
  by auto  
next
  case False
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None"
    using mem_context_val_w32_9_unchanged by metis
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None \<and>
    (\<forall>y. (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) (mem s1) = Some y) \<longrightarrow> 
    (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 12))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))= Some y))"
    using mem_context_val_w32_9_unchanged by metis
  then show ?thesis 
  apply auto
  by (simp add: Let_def)
qed

lemma ptd_lookup_unchanged_2: 
"ptd_lookup va ptp (mem s1) 2 = 
ptd_lookup va ptp ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                            11 := (mem s1 11)(addr := None))) 2"
proof (cases "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) (mem s1) = None")
  case True
  then have "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) (mem s1) = None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36)
           ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = None"
    using mem_context_val_w32_9_unchanged by metis    
  then show ?thesis 
  by auto  
next
  case False
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None"
    using mem_context_val_w32_9_unchanged by metis
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None \<and>
    (\<forall>y. (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) (mem s1) = Some y) \<longrightarrow> 
    (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 18))::word6))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))= Some y))"
    using mem_context_val_w32_9_unchanged by metis
  then show ?thesis 
  apply auto
  using ptd_lookup_unchanged_3   
  unfolding Let_def
  by auto
qed

lemma ptd_lookup_unchanged_1: 
"ptd_lookup va ptp (mem s1) 1 = 
ptd_lookup va ptp ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                            11 := (mem s1 11)(addr := None))) 1"
proof (cases "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) (mem s1) = None")
  case True
  then have "mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) (mem s1) = None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36)
           ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = None"
    using mem_context_val_w32_9_unchanged by metis    
  then show ?thesis 
  by auto  
next
  case False
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None"
    using mem_context_val_w32_9_unchanged by metis
  then have "mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) (mem s1) \<noteq> None \<and>
    mem_context_val_w32 9 ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None \<and>
    (\<forall>y. (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) (mem s1) = Some y) \<longrightarrow> 
    (mem_context_val_w32 9 
    ((ucast (ptp OR ((ucast ((ucast (va >> 24))::word8))::word32)))::word36) 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))= Some y))"
    using mem_context_val_w32_9_unchanged by metis
  then show ?thesis 
  apply auto
  using ptd_lookup_unchanged_2   
  unfolding Let_def
  proof -
    fix y :: word32
    have "(y AND 3 \<noteq> 0 \<or> y AND 3 = 0 \<or> (y AND 3 \<noteq> 1 \<or> ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) = None) \<and> (y AND 3 = 1 \<or> y AND 3 \<noteq> 2 \<or> None = Some ((ucast (ucast (y >> 8)::word24) << 12) OR (ucast (ucast va::word12)::word36), ucast y::word8))) \<and> (y AND 3 = 0 \<or> (y AND 3 \<noteq> 1 \<or> (y AND 3 \<noteq> 0 \<or> ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) = None) \<and> (y AND 3 = 0 \<or> (y AND 3 \<noteq> 1 \<or> ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) = ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1)) \<and> (y AND 3 = 1 \<or> (y AND 3 \<noteq> 2 \<or> ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) = Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y)) \<and> (y AND 3 = 2 \<or> ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) = None)))) \<and> (y AND 3 = 1 \<or> (y AND 3 \<noteq> 2 \<or> (y AND 3 \<noteq> 0 \<or> None = Some ((ucast (ucast (y >> 8)::word24) << 12) OR (ucast (ucast va::word12)::word36), ucast y::word8)) \<and> (y AND 3 = 0 \<or> (y AND 3 \<noteq> 1 \<or> ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) = Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y)) \<and> (y AND 3 = 1 \<or> y AND 3 = 2 \<or> None = Some ((ucast (ucast (y >> 8)::word24) << 12) OR (ucast (ucast va::word12)::word36), ucast y::word8)))) \<and> (y AND 3 = 2 \<or> y AND 3 = 0 \<or> (y AND 3 \<noteq> 1 \<or> ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) = None) \<and> (y AND 3 = 1 \<or> y AND 3 \<noteq> 2 \<or> None = Some ((ucast (ucast (y >> 8)::word24) << 12) OR (ucast (ucast va::word12)::word36), ucast y::word8))))) \<or> (\<forall>w. mem s1 w = ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) w)"
      by (metis (no_types) One_nat_def Suc_1 Suc_eq_plus1 ptd_lookup_unchanged_2)
    then show "(if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) = (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None)"
    proof -
      have f1: "2 = Suc 0 + 1"
        by (metis One_nat_def Suc_1 Suc_eq_plus1)
      { assume "y AND 3 = 1"
        moreover
        { assume "y AND 3 = 1 \<and> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) \<noteq> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None)"
          have "y AND 3 = 1 \<and> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) \<noteq> ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) \<or> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) = (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None)"
            by presburger
          moreover
          { assume "y AND 3 = 1 \<and> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) \<noteq> ptd_lookup va (y AND 4294967292) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) (Suc 0 + 1)"
            then have "y AND 3 = 1 \<and> (if y AND 3 = 0 then None else if y AND 3 = 1 then ptd_lookup va (y AND 4294967292) (mem s1) (Suc 0 + 1) else if y AND 3 = 2 then Some ((ucast (ucast (y >> 8)::word24) << 12) OR ucast (ucast va::word12), ucast y) else None) \<noteq> ptd_lookup va (y AND 4294967292) (mem s1) 2"
              by (metis One_nat_def Suc_1 Suc_eq_plus1 ptd_lookup_unchanged_2)
            then have ?thesis
              using f1 by auto }
          ultimately have ?thesis
            by blast }
        ultimately have ?thesis
          by blast }
      then show ?thesis
        by presburger
    qed  
  qed
qed

lemma virt_to_phys_unchanged_sub1: 
assumes a1: "(let context_table_entry = (v1 >> 11 << 11) OR (v2 AND 511 << 2)
  in Let (mem_context_val_w32 (word_of_int 9) (ucast context_table_entry) (mem s1))
    (case_option None (\<lambda>lvl1_page_table. ptd_lookup va lvl1_page_table (mem s1) 1))) =
 (let context_table_entry = (v1 >> 11 << 11) OR (v2 AND 511 << 2)
  in Let (mem_context_val_w32 (word_of_int 9) (ucast context_table_entry) (mem s2))
    (case_option None (\<lambda>lvl1_page_table. ptd_lookup va lvl1_page_table (mem s2) 1)))"
shows "(let context_table_entry = (v1 >> 11 << 11) OR (v2 AND 511 << 2)
  in Let (mem_context_val_w32 (word_of_int 9) (ucast context_table_entry)
    ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))))
     (case_option None (\<lambda>lvl1_page_table. ptd_lookup va lvl1_page_table
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1))) =
 (let context_table_entry = (v1 >> 11 << 11) OR (v2 AND 511 << 2)
  in Let (mem_context_val_w32 (word_of_int 9) (ucast context_table_entry)
    ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))))
     (case_option None (\<lambda>lvl1_page_table. ptd_lookup va lvl1_page_table
      ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) 1)))"
proof -
  from a1 have 
   "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s1) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s1) 1) =
    (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1)" 
     unfolding Let_def by auto
  then have "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) 
     ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s1) 1) =
    (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) 
     ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1)"
    using mem_context_val_w32_9_unchanged
    by (metis word_numeral_alt) 
 then have "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) 
     ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table 
      ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1) =
    (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) 
     ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of
     None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table 
     ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) 1)"   
    using ptd_lookup_unchanged_1
    proof -
      obtain ww :: "word32 option \<Rightarrow> word32" where
        f1: "\<forall>z. (z = None \<or> z = Some (ww z)) \<and> (z \<noteq> None \<or> (\<forall>w. z \<noteq> Some w))"
        by moura
      then have f2: "(mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = None \<or> mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = Some (ww (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None)))))) \<and> (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None \<or> (\<forall>w. mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> Some w))"
        by blast
      then have f3: "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1) \<noteq> None \<longrightarrow> (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1) = (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w (mem s1) 1)"
        by (metis (no_types) \<open>\<And>val va s1 ptp addr. ptd_lookup va ptp (mem s1) 1 = ptd_lookup va ptp ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1\<close> option.case(2) option.simps(4))
      have f4: "mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) = Some (ww (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))))) \<and> mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) = Some (ww (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))))) \<longrightarrow> (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1) = (case Some (ww (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) 1)"
        by (metis (no_types) \<open>(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s1) 1) = (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1)\<close> \<open>\<And>val va s1 ptp addr. ptd_lookup va ptp (mem s1) 1 = ptd_lookup va ptp ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1\<close> option.case(2))
      have f5: "(mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) = None \<or> mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) = Some (ww (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None)))))) \<and> (mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) \<noteq> None \<or> (\<forall>w. mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) \<noteq> Some w))"
        using f1 by blast
      { assume "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1) \<noteq> (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) 1)"
        { assume "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w (mem s2) 1) \<noteq> None \<and> (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w (mem s2) 1) \<noteq> None"
          then have "(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some w \<Rightarrow> ptd_lookup va w (mem s2) 1) \<noteq> None \<and> mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) \<noteq> None"
            by (metis (no_types) \<open>(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s1) 1) = (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1)\<close> option.simps(4))
          then have ?thesis
            using f5 f4 f2 by force }
        then have ?thesis
          using f5 f3 by (metis (no_types) \<open>(case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s1) 1) = (case mem_context_val_w32 (word_of_int 9) (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2) (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1)\<close> \<open>\<And>val va s1 ptp addr. ptd_lookup va ptp (mem s1) 1 = ptd_lookup va ptp ((mem s1) (10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) 1\<close> option.case(2) option.simps(4)) }
      then show ?thesis
        by blast
    qed
 then show ?thesis 
  unfolding Let_def by auto 
qed

lemma virt_to_phys_unchanged: 
assumes a1: "(\<forall>va. virt_to_phys va (mmu s2) (mem s1) = virt_to_phys va (mmu s2) (mem s2))"
shows "(\<forall>va. virt_to_phys va (mmu s2) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                         11 := (mem s1 11)(addr := None))) =
             virt_to_phys va (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                         11 := (mem s2 11)(addr := None))))"
proof (cases "registers (mmu s2) CR AND 1 \<noteq> 0")
  case True
  then have f1: "registers (mmu s2) CR AND 1 \<noteq> 0" by auto
  then show ?thesis 
  proof (cases "mmu_reg_val (mmu s2) 256 = None")
    case True
    then show ?thesis 
    by (simp add: virt_to_phys_def)
  next
    case False
    then have f2: "mmu_reg_val (mmu s2) 256 \<noteq> None" by auto
    then show ?thesis 
    proof (cases "mmu_reg_val (mmu s2) 512 = None")
      case True
      then show ?thesis using f1 f2
      apply (simp add: virt_to_phys_def)
      by auto
    next
      case False
      then show ?thesis using f1 f2 a1
      apply (simp add: virt_to_phys_def)
      apply clarify
      using virt_to_phys_unchanged_sub1 by fastforce
    qed
  qed
next
  case False
  then show ?thesis 
  by (simp add: virt_to_phys_def)
qed

lemma virt_to_phys_unchanged2_sub1: 
"(case mem_context_val_w32 (word_of_int 9) 
  (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) of
  None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table (mem s2) 1) =
(case mem_context_val_w32 (word_of_int 9) 
  (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2)
    (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) of
  None \<Rightarrow> None | Some lvl1_page_table \<Rightarrow> ptd_lookup va lvl1_page_table ((mem s2)
    (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) 1)"
proof (cases "mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) = None")
  case True
  then have "mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) = None \<and>
    mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2)
    (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) = None"
    using mem_context_val_w32_9_unchanged by metis
  then show ?thesis 
  by auto
next
  case False
  then have "mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) \<noteq> None \<and> 
    (\<forall>y. mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) (mem s2) = Some y \<longrightarrow>
         mem_context_val_w32 9 (ucast ((v1 >> 11 << 11) OR (v2 AND 511 << 2))) ((mem s2)
         (10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))) = Some y)"
    using mem_context_val_w32_9_unchanged by metis 
  then show ?thesis
  using ptd_lookup_unchanged_1 by fastforce 
qed

lemma virt_to_phys_unchanged2: 
"virt_to_phys va (mmu s2) (mem s2) =
virt_to_phys va (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                         11 := (mem s2 11)(addr := None)))"
proof (cases "registers (mmu s2) CR AND 1 \<noteq> 0")
  case True
  then have f1: "registers (mmu s2) CR AND 1 \<noteq> 0" by auto
  then show ?thesis 
  proof (cases "mmu_reg_val (mmu s2) 256 = None")
    case True
    then show ?thesis 
    by (simp add: virt_to_phys_def)
  next
    case False
    then have f2: "mmu_reg_val (mmu s2) 256 \<noteq> None" by auto
    then show ?thesis 
    proof (cases "mmu_reg_val (mmu s2) 512 = None")
      case True
      then show ?thesis using f1 f2
      apply (simp add: virt_to_phys_def)
      by auto
    next
      case False
      then show ?thesis 
      using f1 f2
      apply (simp add: virt_to_phys_def)
      apply clarify
      unfolding Let_def
      using virt_to_phys_unchanged2_sub1
      by auto      
    qed
  qed
next
  case False
  then show ?thesis 
  by (simp add: virt_to_phys_def)
qed

lemma virt_to_phys_unchanged_low_equal: 
assumes a1: "low_equal s1 s2"
shows "(\<forall>va. virt_to_phys va (mmu s2) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                         11 := (mem s1 11)(addr := None))) =
             virt_to_phys va (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                         11 := (mem s2 11)(addr := None))))"
using a1 apply (simp add: low_equal_def)
using virt_to_phys_unchanged
by metis 

lemma mmu_low_equal: "low_equal s1 s2 \<Longrightarrow> mmu s1 = mmu s2"
by (simp add: low_equal_def)

lemma mem_val_alt_8_unchanged0: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 (pa AND 68719476732) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 (pa AND 68719476732) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_unchanged1: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 ((pa AND 68719476732) + 1) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 1) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_unchanged2: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 ((pa AND 68719476732) + 2) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 2) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_unchanged3: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 ((pa AND 68719476732) + 3) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 3) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_8_unchanged: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 8 (pa AND 68719476732) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 (pa AND 68719476732) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 1) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 1) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 2) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 2) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 8 ((pa AND 68719476732) + 3) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 8 ((pa AND 68719476732) + 3) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
using a1 mem_val_alt_8_unchanged0 mem_val_alt_8_unchanged1
mem_val_alt_8_unchanged2 mem_val_alt_8_unchanged3
by blast

lemma mem_val_w32_8_unchanged: 
assumes a1: "mem_equal s1 s2 a"
shows "mem_val_w32 8 a (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) =
mem_val_w32 8 a (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
using mem_val_alt_8_unchanged a1 apply auto
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
 apply fastforce
by fastforce

lemma load_word_mem_8_unchanged: 
assumes a1: "low_equal s1 s2 \<and> 
load_word_mem s1 addra 8 = load_word_mem s2 addra 8"
shows "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                         11 := (mem s1 11)(addr := None))\<rparr>) addra 8 =
       load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                         11 := (mem s2 11)(addr := None))\<rparr>) addra 8"
proof (cases "virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = None")
  case True
  then have "virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = None \<and>
             virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = None"
    using a1 apply (auto simp add: mmu_low_equal)
    using a1 virt_to_phys_unchanged_low_equal by metis
  then show ?thesis
  by (simp add: load_word_mem_def)
next
  case False
  then have "\<exists>p. virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = Some p \<and>
             virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = Some p"
    using a1 apply (auto simp add: mmu_low_equal)
    using a1 virt_to_phys_unchanged_low_equal by metis
  then have "\<exists>p. virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = Some p \<and>
            virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = Some p \<and> 
            virt_to_phys addra (mmu s1) (mem s1) = Some p \<and>
            virt_to_phys addra (mmu s2) (mem s2) = Some p"
    using virt_to_phys_unchanged2 by metis
  then show ?thesis using a1  
  apply (simp add: load_word_mem_def)
  apply auto
  apply (simp add: low_equal_def)
  apply (simp add: user_accessible_def)
  using mem_val_w32_8_unchanged a1 user_accessible_8
  by (metis snd_conv)
qed

lemma load_word_mem_select_8: 
assumes a1: "fst (case load_word_mem s1 addra 8 of None \<Rightarrow> (None, s1)
  | Some w \<Rightarrow> (Some w, add_instr_cache s1 addra w 15)) =
fst (case load_word_mem s2 addra 8 of None \<Rightarrow> (None, s2)
  | Some w \<Rightarrow> (Some w, add_instr_cache s2 addra w 15))"
shows "load_word_mem s1 addra 8 = load_word_mem s2 addra 8"
using a1
by (metis (mono_tags, lifting) fst_conv not_None_eq option.simps(4) option.simps(5))

lemma memory_read_8_unchanged: 
assumes a1: "low_equal s1 s2 \<and>
fst (memory_read 8 addra s1) = fst (memory_read 8 addra s2)"
shows "fst (memory_read 8 addra
                   (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                       11 := (mem s1 11)(addr := None))\<rparr>)) =
         fst (memory_read 8 addra
                   (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                       11 := (mem s2 11)(addr := None))\<rparr>))"
proof (cases "sys_reg s1 CCR AND 1 = 0")
  case True
  then have "sys_reg s1 CCR AND 1 = 0 \<and> sys_reg s2 CCR AND 1 = 0"
    using a1 sys_reg_low_equal by fastforce
  then show ?thesis using a1
  apply (simp add: memory_read_def)
  using load_word_mem_8_unchanged by blast
next
  case False
  then have f1: "sys_reg s1 CCR AND 1 \<noteq> 0 \<and> sys_reg s2 CCR AND 1 \<noteq> 0"
    using a1 sys_reg_low_equal by fastforce
  then show ?thesis using a1
  proof (cases "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 8 = None")
    case True
    then have "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 8 = None \<and> 
      load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
      11 := (mem s2 11)(addr := None))\<rparr>) addra 8 = None"
      using a1 f1  
      apply (simp add: memory_read_def)
      apply clarsimp
      using load_word_mem_select_8 load_word_mem_8_unchanged
      by fastforce      
    then show ?thesis
    by (simp add: memory_read_def)
  next
    case False
    then have "\<exists>y. load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 8 = Some y" by auto
    then have "\<exists>y. load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 8 = Some y \<and> 
                   load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
      11 := (mem s2 11)(addr := None))\<rparr>) addra 8 = Some y"
      using a1 f1
      apply (simp add: memory_read_def)
      apply clarsimp
      using load_word_mem_select_8 load_word_mem_8_unchanged by fastforce
    then show ?thesis using a1 f1
    apply (simp add: memory_read_def)
    by auto
  qed
qed

lemma mem_val_alt_mod: 
assumes a1: "addr1 \<noteq> addr2"
shows "mem_val_alt 10 addr1 s = 
mem_val_alt 10 addr1 (s\<lparr>mem := (mem s)(10 := mem s 10(addr2 \<mapsto> val), 
  11 := (mem s 11)(addr2 := None))\<rparr>)"
using a1 apply (simp add: mem_val_alt_def)
by (simp add: Let_def)

lemma mem_val_alt_mod2: 
"mem_val_alt 10 addr (s\<lparr>mem := (mem s)(10 := mem s 10(addr \<mapsto> val), 
  11 := (mem s 11)(addr := None))\<rparr>) = Some val"
by (simp add: mem_val_alt_def)

lemma mem_val_alt_10_unchanged0: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 (pa AND 68719476732) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 (pa AND 68719476732) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_unchanged1: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 ((pa AND 68719476732) + 1) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 1) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_unchanged2: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 ((pa AND 68719476732) + 2) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 2) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_unchanged3: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 ((pa AND 68719476732) + 3) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 3) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_alt_def)
apply (simp add: Let_def)
using a1 apply (simp add: mem_equal_def)
by (metis option.distinct(1))

lemma mem_val_alt_10_unchanged: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_val_alt 10 (pa AND 68719476732) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 (pa AND 68719476732) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 1) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 1) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 2) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 2) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>) \<and>
  mem_val_alt 10 ((pa AND 68719476732) + 3) (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) = 
  mem_val_alt 10 ((pa AND 68719476732) + 3) (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
using a1 mem_val_alt_10_unchanged0 mem_val_alt_10_unchanged1
mem_val_alt_10_unchanged2 mem_val_alt_10_unchanged3
by blast

lemma mem_val_w32_10_unchanged: 
assumes a1: "mem_equal s1 s2 a"
shows "mem_val_w32 10 a (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>) =
mem_val_w32 10 a (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)"
apply (simp add: mem_val_w32_def)
apply (simp add: Let_def)
using mem_val_alt_10_unchanged a1 apply auto
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  apply fastforce
 apply fastforce
by fastforce

lemma is_accessible: "low_equal s1 s2 \<Longrightarrow>
virt_to_phys addra (mmu s1) (mem s1) = Some (a, b) \<Longrightarrow>
virt_to_phys addra (mmu s2) (mem s2) = Some (a, b) \<Longrightarrow>
mmu_readable (get_acc_flag b) 10 \<Longrightarrow>
mem_equal s1 s2 a"
apply (simp add: low_equal_def)
apply (simp add: user_accessible_def)
by fastforce

lemma load_word_mem_10_unchanged: 
assumes a1: "low_equal s1 s2 \<and> 
load_word_mem s1 addra 10 = load_word_mem s2 addra 10"
shows "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                         11 := (mem s1 11)(addr := None))\<rparr>) addra 10 =
       load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                         11 := (mem s2 11)(addr := None))\<rparr>) addra 10"
proof (cases "virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = None")
  case True
  then have "virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = None \<and>
             virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = None"
    using a1 apply (auto simp add: mmu_low_equal)
    using a1 virt_to_phys_unchanged_low_equal by metis
  then show ?thesis
  by (simp add: load_word_mem_def)
next
  case False
  then have "\<exists>p. virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = Some p \<and>
             virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = Some p"
    using a1 apply (auto simp add: mmu_low_equal)
    using a1 virt_to_phys_unchanged_low_equal by metis
  then have "\<exists>p. virt_to_phys addra (mmu s1) ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 
          11 := (mem s1 11)(addr := None))) = Some p \<and>
            virt_to_phys addra (mmu s2) ((mem s2)(10 := mem s2 10(addr \<mapsto> val), 
          11 := (mem s2 11)(addr := None))) = Some p \<and> 
            virt_to_phys addra (mmu s1) (mem s1) = Some p \<and>
            virt_to_phys addra (mmu s2) (mem s2) = Some p"
    using virt_to_phys_unchanged2 by metis
  then show ?thesis using a1  
  apply (simp add: load_word_mem_def)
  apply auto
  apply (simp add: low_equal_def)
  apply (simp add: user_accessible_def)
  using mem_val_w32_10_unchanged a1 by metis
qed

lemma load_word_mem_select_10: 
assumes a1: "fst (case load_word_mem s1 addra 10 of None \<Rightarrow> (None, s1)
  | Some w \<Rightarrow> (Some w, add_data_cache s1 addra w 15)) =
fst (case load_word_mem s2 addra 10 of None \<Rightarrow> (None, s2)
  | Some w \<Rightarrow> (Some w, add_data_cache s2 addra w 15))"
shows "load_word_mem s1 addra 10 = load_word_mem s2 addra 10"
using a1
by (metis (mono_tags, lifting) fst_conv not_None_eq option.simps(4) option.simps(5))

lemma memory_read_10_unchanged: 
assumes a1: "low_equal s1 s2 \<and>
fst (memory_read 10 addra s1) = fst (memory_read 10 addra s2)"
shows "fst (memory_read 10 addra
                   (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
                                       11 := (mem s1 11)(addr := None))\<rparr>)) =
         fst (memory_read 10 addra
                   (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
                                       11 := (mem s2 11)(addr := None))\<rparr>))"
proof (cases "sys_reg s1 CCR AND 1 = 0")
  case True
  then have "sys_reg s1 CCR AND 1 = 0 \<and> sys_reg s2 CCR AND 1 = 0"
    using a1 sys_reg_low_equal by fastforce
  then show ?thesis using a1
  apply (simp add: memory_read_def)
  using load_word_mem_10_unchanged by blast
next
  case False
  then have f1: "sys_reg s1 CCR AND 1 \<noteq> 0 \<and> sys_reg s2 CCR AND 1 \<noteq> 0"
    using a1 sys_reg_low_equal by fastforce
  then show ?thesis using a1
  proof (cases "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 10 = None")
    case True
    then have "load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 10 = None \<and> 
      load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
      11 := (mem s2 11)(addr := None))\<rparr>) addra 10 = None"
      using a1 f1  
      apply (simp add: memory_read_def)
      apply clarsimp
      using load_word_mem_select_10 load_word_mem_10_unchanged by fastforce
    then show ?thesis
    by (simp add: memory_read_def)
  next
    case False
    then have "\<exists>y. load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 10 = Some y" by auto
    then have "\<exists>y. load_word_mem (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
      11 := (mem s1 11)(addr := None))\<rparr>) addra 10 = Some y \<and> 
                   load_word_mem (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
      11 := (mem s2 11)(addr := None))\<rparr>) addra 10 = Some y"
      using a1 f1
      apply (simp add: memory_read_def)
      apply clarsimp
      using load_word_mem_select_10 load_word_mem_10_unchanged by fastforce
    then show ?thesis using a1 f1
    apply (simp add: memory_read_def)
    by auto
  qed
qed

lemma state_mem_mod_1011_low_equal_sub1: 
assumes a1: "(\<forall>va. virt_to_phys va (mmu s2) (mem s1) =
            virt_to_phys va (mmu s2) (mem s2)) \<and>
  (\<forall>pa. (\<exists>va b. virt_to_phys va (mmu s2) (mem s2) = Some (pa, b) \<and>
  mmu_readable (get_acc_flag b) 10) \<longrightarrow>
  mem_equal s1 s2 pa) \<and>
  mmu s1 = mmu s2 \<and>
  virt_to_phys va (mmu s2)
  ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) =
  Some (pa, b) \<and>
  mmu_readable (get_acc_flag b) 10"
shows "mem_equal s1 s2 pa"
proof -
  have "virt_to_phys va (mmu s1)
  ((mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))) =
  Some (pa, b)"
    using a1 by auto
  then have "virt_to_phys va (mmu s1) (mem s1) = Some (pa, b)"
    using virt_to_phys_unchanged2 by metis
  then have "virt_to_phys va (mmu s2) (mem s2) = Some (pa, b)"
    using a1 by auto
  then show ?thesis using a1 by auto
qed

lemma mem_equal_unchanged: 
assumes a1: "mem_equal s1 s2 pa"
shows "mem_equal (s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 
  11 := (mem s1 11)(addr := None))\<rparr>)
 (s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 
  11 := (mem s2 11)(addr := None))\<rparr>)
 pa"
using a1 apply (simp add: mem_equal_def)
by auto

lemma state_mem_mod_1011_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = s1\<lparr>mem := (mem s1)(10 := mem s1 10(addr \<mapsto> val), 11 := (mem s1 11)(addr := None))\<rparr> \<and>
t2 = s2\<lparr>mem := (mem s2)(10 := mem s2 10(addr \<mapsto> val), 11 := (mem s2 11)(addr := None))\<rparr>"
shows "low_equal t1 t2"
using a1
apply (simp add: low_equal_def)
apply (simp add: user_accessible_def)
apply auto
   apply (simp add: assms virt_to_phys_unchanged_low_equal)
  using state_mem_mod_1011_low_equal_sub1 mem_equal_unchanged
  apply metis
 apply (metis virt_to_phys_unchanged2)
using state_mem_mod_1011_low_equal_sub1 mem_equal_unchanged
by metis

lemma mem_mod_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = (mem_mod 10 addr val s1) \<and>
t2 = (mem_mod 10 addr val s2)"
shows "low_equal t1 t2"
using a1
apply (simp add: mem_mod_def)
by (auto intro: state_mem_mod_1011_low_equal)

lemma mem_mod_w32_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = mem_mod_w32 10 a bm data s1 \<and>
t2 = mem_mod_w32 10 a bm data s2"
shows "low_equal t1 t2"
using a1
apply (simp add: mem_mod_w32_def)
apply (simp add: Let_def)
by (meson mem_mod_low_equal)

lemma store_word_mem_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
Some t1 = store_word_mem s1 addr data bm 10 \<and>
Some t2 = store_word_mem s2 addr data bm 10" 
shows "low_equal t1 t2" using a1
apply (simp add: store_word_mem_def)
apply (auto simp add: virt_to_phys_low_equal)
apply (case_tac "virt_to_phys addr (mmu s2) (mem s2) = None")
 apply auto
apply (case_tac "mmu_writable (get_acc_flag b) 10")
 apply auto
using mem_mod_w32_low_equal by blast

lemma memory_write_asi_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
Some t1 = memory_write_asi 10 addr bm data s1 \<and>
Some t2 = memory_write_asi 10 addr bm data s2"
shows "low_equal t1 t2"
using a1 apply (simp add: memory_write_asi_def)
by (meson add_data_cache_low_equal store_word_mem_low_equal)

lemma store_barrier_pending_mod_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = store_barrier_pending_mod False s1 \<and>
t2 = store_barrier_pending_mod False s2"
shows "low_equal t1 t2"
using a1 apply (simp add: store_barrier_pending_mod_def)
apply clarsimp
using a1 apply (auto simp add: state_var_low_equal)
by (auto intro: state_var2_low_equal)

lemma memory_write_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
Some t1 = memory_write 10 addr bm data s1 \<and>
Some t2 = memory_write 10 addr bm data s2"
shows "low_equal t1 t2"
apply (case_tac "memory_write_asi 10 addr bm data s1 = None")
 using a1 apply (simp add: memory_write_def)
apply (case_tac "memory_write_asi 10 addr bm data s2 = None")
 apply (meson assms low_equal_com memory_write_asi_low_equal_none)
using a1 apply (simp add: memory_write_def)
apply auto
by (metis memory_write_asi_low_equal store_barrier_pending_mod_low_equal)

lemma memory_write_low_equal2: 
assumes a1: "low_equal s1 s2 \<and>
Some t1 = memory_write 10 addr bm data s1"
shows "\<exists>t2. Some t2 = memory_write 10 addr bm data s2"
using a1
apply (simp add: memory_write_def)
apply auto
by (metis (full_types) memory_write_def memory_write_low_equal_none2 not_None_eq) 

lemma store_sub2_low_equal_sub1:
assumes a1: "low_equal s1 s2 \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s1 = Some y \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s2 = Some ya"
shows "low_equal (y\<lparr>traps := insert data_access_exception (traps y)\<rparr>)
        (ya\<lparr>traps := insert data_access_exception (traps ya)\<rparr>)"
proof -
  from a1 have f1: "low_equal y ya" using memory_write_low_equal by metis
  then have "traps y = traps ya" by (simp add: low_equal_def)
  then show ?thesis using f1 mod_trap_low_equal by fastforce
qed

lemma store_sub2_low_equal_sub2:
assumes a1: "low_equal s1 s2 \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s1 = Some y \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s2 = Some ya \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) y) y = None \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) ya) ya = Some yb"
shows "False"
proof -
  from a1 have f1: "low_equal y ya" using memory_write_low_equal by metis
  then have "(user_reg_val curr_win (rd OR 1) y) = 
    (user_reg_val curr_win (rd OR 1) ya)" 
    by (simp add: low_equal_def user_reg_val_def)
  then show ?thesis using a1
  using f1 memory_write_low_equal_none by fastforce  
qed

lemma store_sub2_low_equal_sub3:
assumes a1: "low_equal s1 s2 \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s1 = Some y \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s2 = Some ya \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) y) y = Some yb \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) ya) ya = None"
shows "False"
proof -
  from a1 have f1: "low_equal y ya" using memory_write_low_equal by metis
  then have "(user_reg_val curr_win (rd OR 1) y) = 
    (user_reg_val curr_win (rd OR 1) ya)" 
    by (simp add: low_equal_def user_reg_val_def)
  then show ?thesis using a1
  using f1 memory_write_low_equal_none2 by fastforce  
qed

lemma store_sub2_low_equal_sub4:
assumes a1: "low_equal s1 s2 \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s1 = Some y \<and>
memory_write 10 addr (st_byte_mask instr addr)
  (st_data0 instr curr_win rd addr s2) s2 = Some ya \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) y) y = Some yb \<and>
memory_write 10 (addr + 4) 15 (user_reg_val curr_win (rd OR 1) ya) ya = Some yc" 
shows "low_equal yb yc"
proof -
  from a1 have f1: "low_equal y ya" using memory_write_low_equal by metis
  then have "(user_reg_val curr_win (rd OR 1) y) = 
    (user_reg_val curr_win (rd OR 1) ya)" 
    by (simp add: low_equal_def user_reg_val_def)
  then show ?thesis using a1 f1
  by (metis memory_write_low_equal)  
qed

lemma store_sub2_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (store_sub2 instr curr_win rd 10 addr s1)) \<and>
t2 = snd (fst (store_sub2 instr curr_win rd 10 addr s2))"
shows "low_equal t1 t2"
proof (cases "memory_write 10 addr (st_byte_mask instr addr)
        (st_data0 instr curr_win rd addr s1) s1 = None")
  case True
  then have "memory_write 10 addr (st_byte_mask instr addr)
        (st_data0 instr curr_win rd addr s1) s1 = None \<and>
        memory_write 10 addr (st_byte_mask instr addr)
        (st_data0 instr curr_win rd addr s2) s2 = None"
    using a1 by (metis memory_write_low_equal_none st_data0_low_equal) 
  then show ?thesis using a1
  apply (simp add: store_sub2_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold return_def)
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  using mod_trap_low_equal traps_low_equal by fastforce  
next
  case False
  then have f1: "memory_write 10 addr (st_byte_mask instr addr) 
    (st_data0 instr curr_win rd addr s1) s1 \<noteq> None \<and>
    memory_write 10 addr (st_byte_mask instr addr) 
    (st_data0 instr curr_win rd addr s2) s2 \<noteq> None"
    using a1 by (metis memory_write_low_equal_none2 st_data0_low_equal)     
  then show ?thesis 
  proof (cases "(fst instr) \<in> {load_store_type STD,load_store_type STDA}")
    case True
    then show ?thesis using a1 f1
    apply (simp add: store_sub2_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    apply (simp add: return_def)
    apply (simp add: bind_def case_prod_unfold)
    apply (simp add: simpler_modify_def)
    apply clarsimp
    apply (simp add: case_prod_unfold bind_def h1_def h2_def Let_def simpler_modify_def)
    apply (simp add: simpler_gets_def)
    apply auto
           apply (simp add: raise_trap_def add_trap_set_def)
           apply (simp add: simpler_modify_def)
           apply (simp add: st_data0_low_equal)    
           apply (simp add: store_sub2_low_equal_sub1)
          apply (simp add: st_data0_low_equal)
          using store_sub2_low_equal_sub2 apply blast
         apply (simp add: st_data0_low_equal)
         using store_sub2_low_equal_sub3 apply blast
        apply (simp add: st_data0_low_equal)
        using store_sub2_low_equal_sub4 apply blast
       apply (simp add: st_data0_low_equal)
       apply (simp add: raise_trap_def add_trap_set_def)
       apply (simp add: simpler_modify_def)
       using store_sub2_low_equal_sub1 apply blast
      apply (simp add: st_data0_low_equal)
      using store_sub2_low_equal_sub2 apply blast
     apply (simp add: st_data0_low_equal)
     using store_sub2_low_equal_sub3 apply blast
    apply (simp add: st_data0_low_equal)
    using store_sub2_low_equal_sub4 by blast
  next
    case False
    then show ?thesis using a1 f1
    apply (simp add: store_sub2_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def)
    apply (simp add: simpler_modify_def bind_def h1_def h2_def Let_def)
    apply (simp add: return_def)
    apply (simp add: bind_def case_prod_unfold)
    apply clarsimp
    apply (simp add: simpler_modify_def)
    apply (simp add: st_data0_low_equal)
    using memory_write_low_equal by metis
  qed
qed

lemma store_sub1_low_equal:
assumes a1: "low_equal s1 s2 \<and>
(fst instr = load_store_type STB \<or>
fst instr = load_store_type STH \<or>
fst instr = load_store_type ST \<or> 
fst instr = load_store_type STD) \<and>
t1 = snd (fst (store_sub1 instr rd 0 s1)) \<and>
t2 = snd (fst (store_sub1 instr rd 0 s2))"
shows "low_equal t1 t2"
proof (cases "(fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0")
  case True
  then have "((fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0) \<and> 
             ((fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word1) \<noteq> 0)"
    by (metis (mono_tags, lifting) assms get_addr_low_equal) 
  then show ?thesis using a1
  apply (simp add: store_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  apply clarsimp
  apply (simp add: get_curr_win3_low_equal)
  by (auto intro: get_curr_win2_low_equal mod_trap_low_equal)
next
  case False
  then have f1: "\<not> ((fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
      ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word1) \<noteq> 0) \<and>
      \<not> ((fst instr = load_store_type STH \<or> fst instr = load_store_type STHA) \<and>
      ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word1) \<noteq> 0)"
    by (metis (mono_tags, lifting) assms get_addr_low_equal) 
  then show ?thesis 
  proof (cases "(fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0")
    case True
    then have "(fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0 \<and>
              (fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<noteq> 0"
      by (metis (mono_tags, lifting) assms get_addr_low_equal) 
    then show ?thesis using a1 f1
    apply (simp add: store_sub1_def)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply (simp add: case_prod_unfold) 
    apply (simp add: raise_trap_def add_trap_set_def)
    apply (simp add: simpler_modify_def)
    apply clarsimp
    apply (simp add: get_curr_win3_low_equal)
    by (auto intro: get_curr_win2_low_equal mod_trap_low_equal)
  next
    case False
    then have "\<not>((fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0) \<and>
              \<not>((fst instr \<in> {load_store_type ST,load_store_type STA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<noteq> 0)"
      by (metis (mono_tags, lifting) assms get_addr_low_equal) 
    then have f2: "\<not>((fst instr = load_store_type ST \<or> fst instr = load_store_type STA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word2) \<noteq> 0) \<and>
              \<not>((fst instr = load_store_type ST \<or> fst instr = load_store_type STA) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word2) \<noteq> 0)"
      by auto
    then show ?thesis 
    proof (cases "(fst instr \<in> {load_store_type STD,load_store_type STDA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0")
      case True
      then have "(fst instr \<in> {load_store_type STD,load_store_type STDA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0 \<and>
              (fst instr \<in> {load_store_type STD,load_store_type STDA}) \<and>
              ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<noteq> 0"
        by (metis (mono_tags, lifting) assms get_addr_low_equal) 
      then show ?thesis using a1 
      apply (simp add: store_sub1_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply auto
      apply (simp add: case_prod_unfold) 
      apply (simp add: raise_trap_def add_trap_set_def)
      apply (simp add: simpler_modify_def)
      apply (simp add: get_curr_win3_low_equal)
      by (auto intro: get_curr_win2_low_equal mod_trap_low_equal)         
    next
      case False
      then have "\<not> (fst instr \<in> {load_store_type STD, load_store_type STDA} \<and>
        ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0) \<and>
        \<not> (fst instr \<in> {load_store_type STD, load_store_type STDA} \<and>
        ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<noteq> 0)"
        by (metis (mono_tags, lifting) assms get_addr_low_equal)
      then have f3: "\<not> ((fst instr = load_store_type STD \<or> fst instr = load_store_type STDA) \<and>
        ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s1)))))::word3) \<noteq> 0) \<and>
        \<not> ((fst instr = load_store_type STD \<or> fst instr = load_store_type STDA) \<and>
        ((ucast (get_addr (snd instr) (snd (fst (get_curr_win () s2)))))::word3) \<noteq> 0)"
        by auto
      show ?thesis using a1
      apply (simp add: store_sub1_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (unfold case_prod_beta)
      apply (simp add: f1 f2 f3)
      apply (simp_all add: st_asi_def)
      using a1 apply clarsimp
      apply (simp add: get_curr_win_low_equal get_addr2_low_equal)
      by (metis store_sub2_low_equal get_curr_win2_low_equal)      
    qed
  qed
qed

lemma store_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
(fst instr = load_store_type STB \<or>
fst instr = load_store_type STH \<or>
fst instr = load_store_type ST \<or> 
fst instr = load_store_type STA \<or> 
fst instr = load_store_type STD) \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
t1 = snd (fst (store_instr instr s1)) \<and> t2 = snd (fst (store_instr instr s2))"
shows "low_equal t1 t2"
proof -
  have "get_S (cpu_reg_val PSR s1) = 0 \<and> get_S (cpu_reg_val PSR s2) = 0"
    using a1 by (simp add: ucast_id) 
  then show ?thesis using a1
  apply (simp add: store_instr_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: Let_def)
  apply clarsimp
  apply (simp add: raise_trap_def add_trap_set_def)
  apply (simp add: simpler_modify_def)
  apply (simp add: traps_low_equal)
  by (auto intro: mod_trap_low_equal store_sub1_low_equal)
qed

lemma sethi_low_equal: "low_equal s1 s2 \<and>
t1 = snd (fst (sethi_instr instr s1)) \<and> t2 = snd (fst (sethi_instr instr s2)) \<Longrightarrow>
low_equal t1 t2"
apply (simp add: sethi_instr_def)
apply (simp add: Let_def)
apply (case_tac "get_operand_w5 (snd instr ! Suc 0) \<noteq> 0")
 apply auto
 apply (simp add: bind_def h1_def h2_def Let_def)
 apply (simp add: case_prod_unfold)
 apply (simp add: get_curr_win_low_equal)
 using get_curr_win2_low_equal write_reg_low_equal
 apply metis
by (simp add: return_def)

lemma nop_low_equal: "low_equal s1 s2 \<and>
t1 = snd (fst (nop_instr instr s1)) \<and> t2 = snd (fst (nop_instr instr s2)) \<Longrightarrow>
low_equal t1 t2"
apply (simp add: nop_instr_def)
by (simp add: return_def)

lemma logical_instr_sub1_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (logical_instr_sub1 instr_name result s1)) \<and> 
t2 = snd (fst (logical_instr_sub1 instr_name result s2))"
shows "low_equal t1 t2"
proof (cases "instr_name = logic_type ANDcc \<or>
              instr_name = logic_type ANDNcc \<or>
              instr_name = logic_type ORcc \<or>
              instr_name = logic_type ORNcc \<or>
              instr_name = logic_type XORcc \<or> instr_name = logic_type XNORcc")
  case True
  then show ?thesis using a1
  apply (simp add: logical_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: logical_new_psr_val_def)    
  using write_cpu_low_equal cpu_reg_val_low_equal
  by fastforce  
next
  case False
  then show ?thesis using a1
  apply (simp add: logical_instr_sub1_def)
  by (simp add: return_def)
qed

lemma logical_instr_low_equal: "low_equal s1 s2 \<and>
t1 = snd (fst (logical_instr instr s1)) \<and> t2 = snd (fst (logical_instr instr s2)) \<Longrightarrow>
low_equal t1 t2"
apply (simp add: logical_instr_def)
apply (simp add: Let_def simpler_gets_def bind_def h1_def h2_def)
apply (simp add: case_prod_unfold)
apply auto
 apply (simp_all add: get_curr_win_low_equal)
 apply (simp_all add: get_operand2_low_equal)
 using logical_instr_sub1_low_equal get_operand2_low_equal
 get_curr_win2_low_equal write_reg_low_equal user_reg_val_low_equal
 proof -
  assume a1: "low_equal s1 s2"
  assume "t2 = snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))))"
  assume "t1 = snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))"
  have "\<And>w wa. user_reg_val w wa (snd (fst (get_curr_win () s2))) = user_reg_val w wa (snd (fst (get_curr_win () s1)))"
    using a1 by (metis (no_types) get_curr_win2_low_equal user_reg_val_low_equal)
  then show "low_equal (snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))) (snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))))"
    using a1 by (metis (no_types) get_curr_win2_low_equal logical_instr_sub1_low_equal write_reg_low_equal)
 next
  assume a2: "low_equal s1 s2"
  assume "t1 = snd (fst (logical_instr_sub1 (fst instr)
                    (logical_result (fst instr)
                      (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                        (snd (fst (get_curr_win () s1))))
                      (get_operand2 (snd instr) s2))
                    (snd (fst (write_reg
                                (user_reg_val (fst (fst (get_curr_win () s2))) 0
                                  (snd (fst (get_curr_win () s1))))
                                (fst (fst (get_curr_win () s2))) 0
                                (snd (fst (get_curr_win () s1))))))))"
  assume "t2 = snd (fst (logical_instr_sub1 (fst instr)
                    (logical_result (fst instr)
                      (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                        (snd (fst (get_curr_win () s2))))
                      (get_operand2 (snd instr) s2))
                    (snd (fst (write_reg
                                (user_reg_val (fst (fst (get_curr_win () s2))) 0
                                  (snd (fst (get_curr_win () s2))))
                                (fst (fst (get_curr_win () s2))) 0
                                (snd (fst (get_curr_win () s2))))))))"
  have "\<And>w wa. user_reg_val w wa (snd (fst (get_curr_win () s2))) = user_reg_val w wa (snd (fst (get_curr_win () s1)))"
    using a2 by (metis (no_types) get_curr_win2_low_equal user_reg_val_low_equal)
  then show "low_equal
     (snd (fst (logical_instr_sub1 (fst instr)
                 (logical_result (fst instr)
                   (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                     (snd (fst (get_curr_win () s1))))
                   (get_operand2 (snd instr) s2))
                 (snd (fst (write_reg
                             (user_reg_val (fst (fst (get_curr_win () s2))) 0
                               (snd (fst (get_curr_win () s1))))
                             (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))))))))
     (snd (fst (logical_instr_sub1 (fst instr)
                 (logical_result (fst instr)
                   (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                     (snd (fst (get_curr_win () s2))))
                   (get_operand2 (snd instr) s2))
                 (snd (fst (write_reg
                             (user_reg_val (fst (fst (get_curr_win () s2))) 0
                               (snd (fst (get_curr_win () s2))))
                             (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
  proof -
    have "low_equal (snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (logical_instr_sub1 (fst instr) (logical_result (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s2)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
      by (meson a2 get_curr_win2_low_equal logical_instr_sub1_low_equal write_reg_low_equal)
    then show ?thesis
      using \<open>\<And>wa w. user_reg_val w wa (snd (fst (get_curr_win () s2))) = user_reg_val w wa (snd (fst (get_curr_win () s1)))\<close> by presburger
  qed   
 qed

lemma shift_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (shift_instr instr s1)) \<and> t2 = snd (fst (shift_instr instr s2))"
shows "low_equal t1 t2"
proof (cases "(fst instr = shift_type SLL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
  case True
  then show ?thesis using a1
  apply (simp add: shift_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def)
  apply (simp add: bind_def h1_def h2_def Let_def case_prod_unfold)
  apply auto
    apply (simp_all add: get_curr_win_low_equal)
    proof -
      assume a1: "low_equal s1 s2"
      assume "t2 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) << unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))"
      assume "t1 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) << unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))"
      have "\<And>w wa wb. low_equal (snd (fst (write_reg w wa wb s1))) (snd (fst (write_reg w wa wb s2)))"
        using a1 by (metis write_reg_low_equal)
      then show "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) << unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) << unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
        using a1 by (simp add: get_curr_win_def simpler_gets_def user_reg_val_low_equal)
    next
      assume a2: "low_equal s1 s2"
      assume "t1 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s1))) <<
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s1)))))"
      assume "t2 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s2))) <<
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s2)))))"
      have "\<And>w wa wb. low_equal (snd (fst (write_reg w wa wb s1))) (snd (fst (write_reg w wa wb s2)))"
        using a2 by (metis write_reg_low_equal)
      then show "low_equal
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s1))) <<
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s1))))))
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s2))) <<
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s2))))))"
      proof -
        assume a1: "\<And>w wa wb. low_equal (snd (fst (write_reg w wa wb s1))) (snd (fst (write_reg w wa wb s2)))"
        have "\<And>u s. fst (get_curr_win u s) = (ucast (get_CWP (cpu_reg_val PSR s))::'a word, s)"
          by (simp add: get_curr_win_def simpler_gets_def)
        then show ?thesis
          using a1 assms user_reg_val_low_equal by fastforce
      qed      
    qed
next
  case False
  then have f1: "\<not>((fst instr = shift_type SLL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0))"
    by auto
  then show ?thesis
  proof (cases "(fst instr = shift_type SRL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
    case True
    then show ?thesis using a1 f1
    apply (simp add: shift_instr_def)
    apply (simp add: Let_def)
    apply (simp add: simpler_gets_def)
    apply (simp add: bind_def h1_def h2_def Let_def case_prod_unfold)
    apply auto
      apply (simp_all add: get_curr_win_low_equal)
      proof -
        assume a1: "low_equal s1 s2"
        assume "t2 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) >> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))"
        assume "t1 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) >> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))"
        have "\<And>u s. fst (get_curr_win u s) = (ucast (get_CWP (cpu_reg_val PSR s))::'a word, s)"
          by (simp add: get_curr_win_def simpler_gets_def)
        then show "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) >> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) >> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
          using a1 user_reg_val_low_equal write_reg_low_equal by fastforce
      next
        assume a2: "low_equal s1 s2"
        assume "t1 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s1))) >>
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s1)))))" 
        assume "t2 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s2))) >>
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s2)))))"
        have "\<And>u s. fst (get_curr_win u s) = (ucast (get_CWP (cpu_reg_val PSR s))::'a word, s)"
          by (simp add: get_curr_win_def simpler_gets_def)
        then show "low_equal
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s1))) >>
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s1))))))
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s2))) >>
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s2))))))"
          using a2 user_reg_val_low_equal write_reg_low_equal by fastforce
      qed  
  next
    case False
    then have f2: "\<not>((fst instr = shift_type SRL) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0))"
      by auto
    then show ?thesis 
    proof (cases "(fst instr = shift_type SRA) \<and> (get_operand_w5 ((snd instr)!3) \<noteq> 0)")
      case True
      then show ?thesis using a1 f1 f2
      apply (simp add: shift_instr_def)
      apply (simp add: Let_def)
      apply (simp add: simpler_gets_def)
      apply (simp add: bind_def h1_def h2_def Let_def case_prod_unfold)
      apply auto
       apply (simp_all add: get_curr_win_low_equal)
       proof -
        assume a1: "low_equal s1 s2"
        assume "t1 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) >>> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))"
        assume "t2 = snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) >>> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))"
        have "\<forall>w wa. user_reg_val wa w (snd (fst (get_curr_win () s1))) = user_reg_val wa w (snd (fst (get_curr_win () s2)))"
          using a1 by (meson get_curr_win2_low_equal user_reg_val_low_equal)
        then show "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) >>> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s1))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) >>> unat (ucast (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 2)) (snd (fst (get_curr_win () s2))))::word5)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
          using a1 by (metis (no_types) get_curr_win2_low_equal write_reg_low_equal)
       next
        assume a2: "low_equal s1 s2"
        assume "t1 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s1))) >>>
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s1)))))"
        assume "t2 = snd (fst (write_reg
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s2))) >>>
                     unat (get_operand_w5 (snd instr ! 2)))
                    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                    (snd (fst (get_curr_win () s2)))))"
        have "\<forall>w wa. user_reg_val wa w (snd (fst (get_curr_win () s1))) = user_reg_val wa w (snd (fst (get_curr_win () s2)))"
          using a2 by (meson get_curr_win2_low_equal user_reg_val_low_equal)
        then show "low_equal
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s1))) >>>
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s1))))))
                (snd (fst (write_reg
                 (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s2))) >>>
                  unat (get_operand_w5 (snd instr ! 2)))
                 (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                 (snd (fst (get_curr_win () s2))))))"
           using a2 get_curr_win2_low_equal write_reg_low_equal by fastforce         
       qed
    next
      case False
      then show ?thesis using a1 f1 f2
      apply (simp add: shift_instr_def)
      apply (simp add: Let_def) 
      apply (simp add: simpler_gets_def)
      apply (simp add: bind_def h1_def h2_def Let_def case_prod_unfold)
      apply (simp add: return_def)
      using get_curr_win2_low_equal by blast
    qed
  qed
qed

lemma add_instr_sub1_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (add_instr_sub1 instr_name result rs1_val operand2 s1)) \<and>
t2 = snd (fst (add_instr_sub1 instr_name result rs1_val operand2 s2))"
shows "low_equal t1 t2"
proof (cases "instr_name = arith_type ADDcc \<or> instr_name = arith_type ADDXcc")
  case True
  then show ?thesis using a1
  apply (simp add: add_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (clarsimp simp add: cpu_reg_val_low_equal)
  using write_cpu_low_equal by blast
next
  case False
  then show ?thesis using a1
  apply (simp add: add_instr_sub1_def)
  by (simp add: return_def)
qed

lemma add_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (add_instr instr s1)) \<and> t2 = snd (fst (add_instr instr s2))"
shows "low_equal t1 t2"
proof -
  have f1: "low_equal s1 s2 \<and>
        t1 = snd (fst (add_instr_sub1 (fst instr)
                    (if fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc
                     then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s1))) +
                          get_operand2 (snd instr) s1
                     else user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s1))) +
                          get_operand2 (snd instr) s1 +
                          ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1))))))
                    (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s1))))
                    (get_operand2 (snd instr) s1)
                    (snd (fst (write_reg
                                (if get_operand_w5 (snd instr ! 3) \<noteq> 0
                                 then if fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc
                                      then user_reg_val (fst (fst (get_curr_win () s1)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s1))) +
                                           get_operand2 (snd instr) s1
                                      else user_reg_val (fst (fst (get_curr_win () s1)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s1))) +
                                           get_operand2 (snd instr) s1 +
                                           ucast (get_icc_C
                                                   (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))
                                 else user_reg_val (fst (fst (get_curr_win () s1)))
                                       (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))
                                (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3))
                                (snd (fst (get_curr_win () s1)))))))) \<and>
    t2 = snd (fst (add_instr_sub1 (fst instr)
                    (if fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc
                     then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s2))) +
                          get_operand2 (snd instr) s2
                     else user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s2))) +
                          get_operand2 (snd instr) s2 +
                          ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2))))))
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s2))))
                    (get_operand2 (snd instr) s2)
                    (snd (fst (write_reg
                                (if get_operand_w5 (snd instr ! 3) \<noteq> 0
                                 then if fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc
                                      then user_reg_val (fst (fst (get_curr_win () s2)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s2))) +
                                           get_operand2 (snd instr) s2
                                      else user_reg_val (fst (fst (get_curr_win () s2)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s2))) +
                                           get_operand2 (snd instr) s2 +
                                           ucast (get_icc_C
                                                   (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))
                                 else user_reg_val (fst (fst (get_curr_win () s2)))
                                       (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))
                                (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                                (snd (fst (get_curr_win () s2))))))))"
  using a1 apply (simp add: add_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (simp add: case_prod_unfold)
  then show ?thesis
  proof (cases "get_operand_w5 (snd instr ! 3) \<noteq> 0")
    case True
    then have f2: "get_operand_w5 (snd instr ! 3) \<noteq> 0" by auto
    then show ?thesis
    proof (cases "fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc")
      case True
      then show ?thesis 
      using f1 f2 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        assume "t1 = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))"
        assume a2: "t2 = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))))"
        have f3: "\<forall>is. get_operand2 is s1 = get_operand2 is s2"
          using a1 by (metis get_operand2_low_equal)
        have f4: "fst (fst (get_curr_win () s1)) = fst (fst (get_curr_win () s2))"
          using a1 by (meson get_curr_win_low_equal)
        have "\<forall>s. snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s + get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s + get_operand2 (snd instr) s2) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))) = t2 \<or> \<not> low_equal s (snd (fst (get_curr_win () s2)))"
          using a2 user_reg_val_low_equal by fastforce
        then show "low_equal (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))) (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))))"
          using f4 f3 a2 a1 by (metis (no_types) add_instr_sub1_low_equal get_curr_win2_low_equal write_reg_low_equal)
      qed
    next
      case False
      then show ?thesis
      using f1 f2 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        have f2: "\<forall>s sa sb w wa wb sc. (\<not> low_equal s sa \<or> sb \<noteq> snd (fst (write_reg w (wa::'a word) wb s)) \<or> sc \<noteq> snd (fst (write_reg w wa wb sa))) \<or> low_equal sb sc"
          by (meson write_reg_low_equal)
        have f3: "gets (\<lambda>s. ucast (get_CWP (cpu_reg_val PSR s))::'a word) = get_curr_win ()"
          by (simp add: get_curr_win_def)
        then have "((ucast (get_CWP (cpu_reg_val PSR s1)), s1), False) = (fst (get_curr_win () s1), snd (get_curr_win () s1))"
          by (metis (no_types) prod.collapse simpler_gets_def)
        then have "(ucast (get_CWP (cpu_reg_val PSR s1)), s1) = fst (get_curr_win () s1) \<and> \<not> snd (get_curr_win () s1)"
          by blast
        then have f4: "ucast (get_CWP (cpu_reg_val PSR s1)) = fst (fst (get_curr_win () s1)) \<and> s1 = snd (fst (get_curr_win () s1))"
          by (metis (no_types) prod.collapse prod.simps(1))
        have "((ucast (get_CWP (cpu_reg_val PSR s2)), s2), False) = (fst (get_curr_win () s2), snd (get_curr_win () s2))"
          using f3 by (metis (no_types) prod.collapse simpler_gets_def)
        then have "(ucast (get_CWP (cpu_reg_val PSR s2)), s2) = fst (get_curr_win () s2) \<and> \<not> snd (get_curr_win () s2)"
          by blast
        then have f5: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2)) \<and> s2 = snd (fst (get_curr_win () s2))"
          by (metis prod.collapse prod.simps(1))
        then have f6: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2))) = low_equal s1 s2"
          using f4 by presburger
        have f7: "fst (fst (get_curr_win () s1)) = ucast (get_CWP (cpu_reg_val PSR s1))"
          using f4 by presburger
        have f8: "cpu_reg_val PSR s1 = cpu_reg_val PSR s2"
          using a1 by (meson cpu_reg_val_low_equal)
        have f9: "user_reg_val (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) = user_reg_val (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))"
          using f6 a1 by (meson user_reg_val_low_equal)
        have f10: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2))"
          using f5 by meson
        have f11: "\<forall>s sa is. \<not> low_equal (s::'a sparc_state) sa \<or> get_operand2 is s = get_operand2 is sa"
          using get_operand2_low_equal by blast
        then have f12: "user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1))))) = user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))"
          using f9 f8 f5 f4 a1 by auto
        then have "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
          using f10 f8 f6 f4 f2 a1 by simp
        then show "low_equal (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))) (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))))"
          using f12 f11 f10 f9 f8 f7 a1 add_instr_sub1_low_equal by fastforce
      qed      
    qed
  next
    case False
    then have f3: "\<not> get_operand_w5 (snd instr ! 3) \<noteq> 0" by auto
    then show ?thesis
    proof (cases "fst instr = arith_type ADD \<or> fst instr = arith_type ADDcc")
      case True
      then show ?thesis
      using f1 f3 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        assume "t1 = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))"
        assume "t2 = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))"
        have f2: "\<forall>is. get_operand2 is s1 = get_operand2 is s2"
          using a1 by (meson get_operand2_low_equal)
        have f3: "fst (fst (get_curr_win () s1)) = fst (fst (get_curr_win () s2))"
          using a1 by (meson get_curr_win_low_equal)
        have "\<forall>w wa. user_reg_val wa w (snd (fst (get_curr_win () s1))) = user_reg_val wa w (snd (fst (get_curr_win () s2)))"
          using a1 by (meson get_curr_win2_low_equal user_reg_val_low_equal)
        then show "low_equal (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
          using f3 f2 a1 by (metis (no_types) add_instr_sub1_low_equal get_curr_win2_low_equal write_reg_low_equal)
      qed      
    next
      case False
      then show ?thesis
      using f1 f3 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        have f2: "gets (\<lambda>s. ucast (get_CWP (cpu_reg_val PSR s))::'a word) = get_curr_win ()"
          by (simp add: get_curr_win_def)
        then have "((ucast (get_CWP (cpu_reg_val PSR s1)), s1), False) = (fst (get_curr_win () s1), snd (get_curr_win () s1))"
          by (metis (no_types) prod.collapse simpler_gets_def)
        then have "(ucast (get_CWP (cpu_reg_val PSR s1)), s1) = fst (get_curr_win () s1) \<and> \<not> snd (get_curr_win () s1)"
          by fastforce
        then have f3: "ucast (get_CWP (cpu_reg_val PSR s1)) = fst (fst (get_curr_win () s1)) \<and> s1 = snd (fst (get_curr_win () s1))"
          by (metis prod.collapse prod.simps(1))
        have "((ucast (get_CWP (cpu_reg_val PSR s2)), s2), False) = (fst (get_curr_win () s2), snd (get_curr_win () s2))"
          using f2 by (metis (no_types) prod.collapse simpler_gets_def)
        then have "(ucast (get_CWP (cpu_reg_val PSR s2)), s2) = fst (get_curr_win () s2) \<and> \<not> snd (get_curr_win () s2)"
          by fastforce
        then have f4: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2)) \<and> s2 = snd (fst (get_curr_win () s2))"
          by (metis (no_types) prod.collapse prod.simps(1))
        then have f5: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2))) = low_equal s1 s2"
          using f3 by presburger
        have f6: "fst (fst (get_curr_win () s1)) = ucast (get_CWP (cpu_reg_val PSR s1))"
          using f3 by auto
        have f7: "cpu_reg_val PSR s1 = cpu_reg_val PSR s2"
          using a1 by (meson cpu_reg_val_low_equal)
        have f8: "\<forall>s sa w wa. \<not> low_equal s sa \<or> user_reg_val (w::'a word) wa s = user_reg_val w wa sa"
          by (meson user_reg_val_low_equal)
        have f9: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2))"
          using f4 by meson
        have "\<forall>s sa is. \<not> low_equal (s::'a sparc_state) sa \<or> get_operand2 is s = get_operand2 is sa"
          using get_operand2_low_equal by blast
        then have f10: "get_operand2 (snd instr) s1 = get_operand2 (snd instr) s2"
          using a1 by meson
        have f11: "cpu_reg_val PSR (snd (fst (get_curr_win () s2))) = cpu_reg_val PSR s1"
          using f4 a1 by (simp add: cpu_reg_val_low_equal)
        have f12: "user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))) = 0"
          by (meson user_reg_val_def)
        have "user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))) = 0"
          by (meson user_reg_val_def)
        then have "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))"
          using f12 f9 f7 f5 f3 a1 write_reg_low_equal by fastforce
        then have "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))) \<and> snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))))))) = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (if get_operand_w5 (snd instr ! Suc 0) = 0 then 0 else user_reg (snd (fst (get_curr_win () s2))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))))))) \<and> snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))) = snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (if get_operand_w5 (snd instr ! Suc 0) = 0 then 0 else user_reg (snd (fst (get_curr_win () s2))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))"
          using f11 f10 f9 f8 f7 f6 f5 f3 a1 by (simp add: user_reg_val_def)
        then show "low_equal (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) + get_operand2 (snd instr) s1 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (add_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) + get_operand2 (snd instr) s2 + ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
          using add_instr_sub1_low_equal by blast
      qed      
    qed
  qed
qed

lemma sub_instr_sub1_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (sub_instr_sub1 instr_name result rs1_val operand2 s1)) \<and> 
t2 = snd (fst (sub_instr_sub1 instr_name result rs1_val operand2 s2))"
shows "low_equal t1 t2"
proof (cases "instr_name = arith_type SUBcc \<or> instr_name = arith_type SUBXcc")
  case True
  then show ?thesis using a1
  apply (simp add: sub_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (clarsimp simp add: cpu_reg_val_low_equal)
  using write_cpu_low_equal by blast
next
  case False
  then show ?thesis using a1
  apply (simp add: sub_instr_sub1_def)
  by (simp add: return_def)
qed

lemma sub_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (sub_instr instr s1)) \<and> t2 = snd (fst (sub_instr instr s2))"
shows "low_equal t1 t2"
proof -
  have f1: "low_equal s1 s2 \<and>
    t1 = snd (fst (sub_instr_sub1 (fst instr)
                    (if fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc
                     then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s1))) -
                          get_operand2 (snd instr) s1
                     else user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s1))) -
                          get_operand2 (snd instr) s1 -
                          ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1))))))
                    (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s1))))
                    (get_operand2 (snd instr) s1)
                    (snd (fst (write_reg
                                (if get_operand_w5 (snd instr ! 3) \<noteq> 0
                                 then if fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc
                                      then user_reg_val (fst (fst (get_curr_win () s1)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s1))) -
                                           get_operand2 (snd instr) s1
                                      else user_reg_val (fst (fst (get_curr_win () s1)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s1))) -
                                           get_operand2 (snd instr) s1 -
                                           ucast (get_icc_C
                                                   (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))
                                 else user_reg_val (fst (fst (get_curr_win () s1)))
                                       (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))
                                (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3))
                                (snd (fst (get_curr_win () s1)))))))) \<and>
    t2 = snd (fst (sub_instr_sub1 (fst instr)
                    (if fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc
                     then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s2))) -
                          get_operand2 (snd instr) s2
                     else user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                           (snd (fst (get_curr_win () s2))) -
                          get_operand2 (snd instr) s2 -
                          ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2))))))
                    (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                      (snd (fst (get_curr_win () s2))))
                    (get_operand2 (snd instr) s2)
                    (snd (fst (write_reg
                                (if get_operand_w5 (snd instr ! 3) \<noteq> 0
                                 then if fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc
                                      then user_reg_val (fst (fst (get_curr_win () s2)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s2))) -
                                           get_operand2 (snd instr) s2
                                      else user_reg_val (fst (fst (get_curr_win () s2)))
                                            (get_operand_w5 (snd instr ! Suc 0))
                                            (snd (fst (get_curr_win () s2))) -
                                           get_operand2 (snd instr) s2 -
                                           ucast (get_icc_C
                                                   (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))
                                 else user_reg_val (fst (fst (get_curr_win () s2)))
                                       (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))
                                (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
                                (snd (fst (get_curr_win () s2))))))))"
  using a1 apply (simp add: sub_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (simp add: case_prod_unfold)
  then show ?thesis
  proof (cases "get_operand_w5 (snd instr ! 3) \<noteq> 0")
    case True
    then have f2: "get_operand_w5 (snd instr ! 3) \<noteq> 0" by auto
    then show ?thesis
    proof (cases "fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc")
      case True
      then show ?thesis
      using f1 f2 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        assume a2: "t1 = snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))"
        assume a3: "t2 = snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))))"
        then have f4: "snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))) = t2"
          using a1 by (simp add: get_operand2_low_equal)
        have "\<forall>s. \<not> low_equal (snd (fst (get_curr_win () s1))) s \<or> snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) s - get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))))) = t1"
          using a2 a1 by (simp add: get_curr_win_low_equal user_reg_val_low_equal)
        then show "low_equal (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))) (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))))"
          using f4 a3 a2 a1 by (metis (no_types) get_curr_win2_low_equal sub_instr_sub1_low_equal write_reg_low_equal)
      qed      
    next
      case False
      then show ?thesis
      using f1 f2 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        have f2: "fst (get_curr_win () s1) = (ucast (get_CWP (cpu_reg_val PSR s1)), s1)"
          by (simp add: get_curr_win_def simpler_gets_def)
        have f3: "cpu_reg_val PSR s1 = cpu_reg_val PSR s2"
          using a1 by (meson cpu_reg_val_low_equal)
        then have f4: "user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) = user_reg_val (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! Suc 0)) s1"
          using f2 by simp
        have f5: "\<forall>s sa is. \<not> low_equal (s::'a sparc_state) sa \<or> get_operand2 is s = get_operand2 is sa"
          using get_operand2_low_equal by blast
        then have f6: "sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! Suc 0)) s2) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) = sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))"
          using f4 a1 by (simp add: user_reg_val_low_equal)
        have f7: "fst (get_curr_win () s2) = (ucast (get_CWP (cpu_reg_val PSR s2)), s2)"
          by (simp add: get_curr_win_def simpler_gets_def)
        then have f8: "user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2))))) = user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))"
          using f5 f2 a1 by (simp add: cpu_reg_val_low_equal user_reg_val_low_equal)
        then have f9: "sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! Suc 0)) s2) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))) = sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
          using f7 by fastforce
        have "write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (ucast (get_CWP (cpu_reg_val PSR s2))) (get_operand_w5 (snd instr ! 3)) s2 = write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))"
          using f8 f7 by simp
        then have "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2))))))"
          using f3 f2 a1 by (metis (no_types) prod.sel(1) prod.sel(2) write_reg_low_equal)
        then show "low_equal (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s1))))))))) (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (get_curr_win () s2)))))))))"
          using f9 f6 by (metis (no_types) sub_instr_sub1_low_equal)
      qed      
    qed
  next
    case False
    then have f3: "\<not> get_operand_w5 (snd instr ! 3) \<noteq> 0" by auto
    then show ?thesis
    proof (cases "fst instr = arith_type SUB \<or> fst instr = arith_type SUBcc")
      case True
      then show ?thesis
      using f1 f3 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        assume "t1 = snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))"
        assume "t2 = snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))"
        have f2: "\<forall>is. get_operand2 is s1 = get_operand2 is s2"
          using a1 get_operand2_low_equal by blast
        have f3: "fst (fst (get_curr_win () s1)) = fst (fst (get_curr_win () s2))"
          using a1 by (meson get_curr_win_low_equal)
        have "\<forall>w wa. user_reg_val wa w (snd (fst (get_curr_win () s1))) = user_reg_val wa w (snd (fst (get_curr_win () s2)))"
          using a1 by (metis (no_types) get_curr_win2_low_equal user_reg_val_low_equal)
        then show "low_equal (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
          using f3 f2 a1 by (metis (no_types) get_curr_win2_low_equal sub_instr_sub1_low_equal write_reg_low_equal)
      qed      
    next
      case False
      then show ?thesis
      using f1 f3 apply clarsimp
      proof -
        assume a1: "low_equal s1 s2"
        have f2: "\<forall>s sa sb w wa wb sc. (\<not> low_equal s sa \<or> sb \<noteq> snd (fst (write_reg w (wa::'a word) wb s)) \<or> sc \<noteq> snd (fst (write_reg w wa wb sa))) \<or> low_equal sb sc"
          by (meson write_reg_low_equal)
        have "((ucast (get_CWP (cpu_reg_val PSR s1)), s1), False) = get_curr_win () s1"
          by (simp add: get_curr_win_def simpler_gets_def)
        then have f3: "ucast (get_CWP (cpu_reg_val PSR s1)) = fst (fst (get_curr_win () s1)) \<and> s1 = snd (fst (get_curr_win () s1))"
          by (metis (no_types) prod.collapse prod.simps(1))
        have "((ucast (get_CWP (cpu_reg_val PSR s2)), s2), False) = get_curr_win () s2"
          by (simp add: get_curr_win_def simpler_gets_def)
        then have f4: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2)) \<and> s2 = snd (fst (get_curr_win () s2))"
          by (metis (no_types) prod.collapse prod.simps(1))
        have f5: "\<forall>s sa sb sc w wa wb sd. (\<not> low_equal (s::'a sparc_state) sa \<or> sb \<noteq> snd (fst (sub_instr_sub1 sc w wa wb s)) \<or> sd \<noteq> snd (fst (sub_instr_sub1 sc w wa wb sa))) \<or> low_equal sb sd"
          by (meson sub_instr_sub1_low_equal)
        have "low_equal (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))"
          using f4 f3 f2 a1 by (simp add: cpu_reg_val_low_equal user_reg_val_low_equal)
        then show "low_equal (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) - get_operand2 (snd instr) s1 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))))) (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) (get_operand2 (snd instr) s1) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (sub_instr_sub1 (fst instr) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) - get_operand2 (snd instr) s2 - ucast (get_icc_C (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))))) (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) (get_operand2 (snd instr) s2) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))))))))"
          using f5 f4 f3 a1 by (simp add: cpu_reg_val_low_equal get_operand2_low_equal user_reg_val_low_equal)
      qed      
    qed
  qed
qed

lemma mul_instr_sub1_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (mul_instr_sub1 instr_name result s1)) \<and>
t2 = snd (fst (mul_instr_sub1 instr_name result s2))"
shows "low_equal t1 t2"
proof (cases "instr_name \<in> {arith_type SMULcc,arith_type UMULcc}")
  case True
  then show ?thesis using a1
  apply (simp add: mul_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (clarsimp simp add: cpu_reg_val_low_equal)
  using write_cpu_low_equal by blast
next
  case False
  then show ?thesis using a1
  apply (simp add: mul_instr_sub1_def)
  by (simp add: return_def)
qed

lemma mul_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (mul_instr instr s1)) \<and> t2 = snd (fst (mul_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: mul_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
proof -
  assume a1: "low_equal s1 s2 \<and> t1 = snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) \<noteq> 0 then ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) else user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))))) \<and> t2 = snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) \<noteq> 0 then ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) else user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))"
  have f2: "\<forall>s sa sb sc w sd. \<not> low_equal (s::'a sparc_state) sa \<or> sb \<noteq> snd (fst (mul_instr_sub1 sc w s)) \<or> sd \<noteq> snd (fst (mul_instr_sub1 sc w sa)) \<or> low_equal sb sd"
    using mul_instr_sub1_low_equal by blast
  have f3: "\<forall>s sa sb w wa wb sc. \<not> low_equal s sa \<or> sb \<noteq> snd (fst (write_reg w (wa::'a word) wb s)) \<or> sc \<noteq> snd (fst (write_reg w wa wb sa)) \<or> low_equal sb sc"
    by (meson write_reg_low_equal)
  have f4: "\<forall>s sa sb w c sc. \<not> low_equal (s::'a sparc_state) sa \<or> sb \<noteq> snd (fst (write_cpu w c s)) \<or> sc \<noteq> snd (fst (write_cpu w c sa)) \<or> low_equal sb sc"
    by (meson write_cpu_low_equal)
  have f5: "low_equal s1 s2 \<and> t1 = snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))))) \<and> t2 = snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))"
    using a1 by presburger
  have f6: "((ucast (get_CWP (cpu_reg_val PSR s1)), s1), False) = (fst (get_curr_win () s1), snd (get_curr_win () s1))"
    by (simp add: get_curr_win_def simpler_gets_def)
  have f7: "fst (fst (get_curr_win () s1)) = fst (fst (get_curr_win () s2))"
    using f5 by (meson get_curr_win_low_equal)
  have "((ucast (get_CWP (cpu_reg_val PSR s2)), s2), False) = (fst (get_curr_win () s2), snd (get_curr_win () s2))"
    by (simp add: get_curr_win_def simpler_gets_def)
  then have f8: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2)) \<and> s2 = snd (fst (get_curr_win () s2))"
    by (metis prod.collapse prod.simps(1))
  then have f9: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
    using f6 f5 by (metis (no_types) prod.collapse prod.simps(1))
  have f10: "\<forall>s sa w wa. \<not> low_equal s sa \<or> user_reg_val (w::'a word) wa s = user_reg_val w wa sa"
    using user_reg_val_low_equal by blast
  have f11: "get_operand2 (snd instr) s1 = get_operand2 (snd instr) (snd (fst (get_curr_win () s2)))"
    using f9 f6 by (metis (no_types) get_operand2_low_equal prod.collapse prod.simps(1))
  then have f12: "uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2) = uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)"
    using f10 f9 f8 f7 by presburger
  then have f13: "(word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) \<noteq> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<or> (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) \<noteq> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) \<or> low_equal (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))"
    using f9 f4 by presburger
  have "get_operand_w5 (snd instr ! 3) = 0 \<and> low_equal (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<longrightarrow> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) = write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))"
    using f10 f7 by force
  then have f14: "get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> low_equal (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))) \<or> \<not> low_equal (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))"
    using f3 by metis 
  then have f15: "low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<or> fst instr \<noteq> arith_type UMULcc \<or> get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) \<noteq> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<or> (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) \<noteq> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))"
    using f13 f12 f2 by fastforce
  have f16: "user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) = user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))"
    using f10 f9 f7 by presburger
  { assume "fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
    moreover
    { assume "\<not> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
      moreover
      { assume "low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<noteq> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
        moreover
        { assume "mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))))) \<noteq> mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))"
          then have "write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<or> fst instr \<noteq> arith_type UMULcc"
            by fastforce }
        moreover
        { assume "mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))) \<noteq> mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))"
          then have "write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<or> fst instr \<noteq> arith_type UMULcc"
            by fastforce }
        ultimately have "write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<or> write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<or> fst instr \<noteq> arith_type UMULcc"
          by force }
      ultimately have "write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<or> write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<or> \<not> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<or> fst instr \<noteq> arith_type UMULcc"
        by fastforce }
    ultimately have "fst instr = arith_type UMULcc \<and> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<and> write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))) = write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) \<and> write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))) = write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))"
      by blast }
  moreover
  { assume "\<not> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
    moreover
    { assume "\<not> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<and> snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))))) = snd (fst (mul_instr_sub1 (arith_type UMULcc) (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))))) \<and> snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))) = snd (fst (mul_instr_sub1 (arith_type UMULcc) (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))"
      then have "\<not> low_equal (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))"
        using f2 by blast
      moreover
      { assume "(if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) \<noteq> (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))))"
        moreover
        { assume "(if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) \<noteq> ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))"
          then have "(if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) = (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
            by (metis f11 f16 f8) }
        ultimately have "(if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) = (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
          by fastforce }
      ultimately have "fst instr = arith_type UMULcc \<and> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) = (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
        using f13 f7 f3 by fastforce }
    moreover
    { assume "mul_instr_sub1 (arith_type UMULcc) (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))) \<noteq> mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))"
      moreover
      { assume "(if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) \<noteq> ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))"
        then have "(if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) = (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
          by (metis f11 f16 f8) }
      ultimately have "fst instr = arith_type UMULcc \<and> (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) = (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1)) else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
        by fastforce }
    ultimately have "fst instr = arith_type UMULcc \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
      using f12 by fastforce }
  moreover
  { assume "write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))) \<noteq> write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))"
    then have "fst instr = arith_type UMULcc \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0"
      by presburger }
  ultimately have "fst instr = arith_type UMULcc \<longrightarrow> get_operand_w5 (snd instr ! 3) = 0 \<or> get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))"
    by force
  moreover
  { assume "fst instr \<noteq> arith_type UMULcc"
    { assume "fst instr \<noteq> arith_type UMULcc \<and> low_equal (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))"
      moreover
      { assume "fst instr \<noteq> arith_type UMULcc \<and> low_equal (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1))))))))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))) \<and> snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))) = snd (fst (mul_instr_sub1 (arith_type UMUL) (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))"
        then have "(fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> fst instr \<noteq> arith_type UMUL \<and> fst instr \<noteq> arith_type UMULcc \<or> (get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<or> get_operand_w5 (snd instr ! 3) = 0"
          using f2 by presburger }
      ultimately have "fst instr \<noteq> arith_type UMULcc \<and> (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) \<noteq> ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) \<or> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> fst instr \<noteq> arith_type UMUL \<and> fst instr \<noteq> arith_type UMULcc \<or> (get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<or> get_operand_w5 (snd instr ! 3) = 0"
        by fastforce }
    then have "(get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<or> get_operand_w5 (snd instr ! 3) = 0"
      using f16 f11 f9 f8 f7 f4 f3 f2 by force }
  moreover
  { assume "get_operand_w5 (snd instr ! 3) = 0"
    moreover
    { assume "(fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0"
      moreover
      { assume "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> \<not> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
        moreover
        { assume "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<noteq> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))"
          then have "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> arith_type UMUL \<noteq> arith_type UMULcc \<or> fst instr \<noteq> arith_type UMULcc \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0"
            by fastforce
          then have "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<or> fst instr \<noteq> arith_type UMULcc \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0"
            by force }
        ultimately have "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<or> ((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> \<not> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<or> fst instr \<noteq> arith_type UMULcc \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0"
          by simp }
      ultimately have "((fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0) \<and> \<not> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1)))) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (snd (fst (write_reg (if get_operand_w5 (snd instr ! 3) = 0 then user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))) else ucast (if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((if fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc then word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64 else word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))) \<or> fst instr \<noteq> arith_type UMULcc \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0 \<or> (get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<and> (get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))))"
        by auto
      then have "fst instr \<noteq> arith_type UMULcc \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc) \<and> get_operand_w5 (snd instr ! 3) = 0 \<or> (get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<and> (get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))))"
        using f15 by presburger
      then have "(get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<and> (get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))))"
        using f14 f13 f12 f2 by force }
    ultimately have "(get_operand_w5 (snd instr ! 3) = 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<and> (get_operand_w5 (snd instr ! 3) \<noteq> 0 \<or> (fst instr \<noteq> arith_type UMUL \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMUL \<or> fst instr = arith_type UMULcc \<or> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))))"
      using f16 f14 f11 f9 f8 f4 f2 by fastforce }
  ultimately show "(get_operand_w5 (snd instr ! 3) \<noteq> 0 \<longrightarrow> (fst instr = arith_type UMUL \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMULcc \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMUL \<and> fst instr \<noteq> arith_type UMULcc \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3)) (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2)))))))))))))) \<and> (get_operand_w5 (snd instr ! 3) = 0 \<longrightarrow> (fst instr = arith_type UMUL \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMUL) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr = arith_type UMULcc \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * uint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (arith_type UMULcc) (ucast (word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (uint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * uint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))) \<and> (fst instr \<noteq> arith_type UMUL \<and> fst instr \<noteq> arith_type UMULcc \<longrightarrow> low_equal (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1))))))) (fst (fst (get_curr_win () s1))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s1))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))) * sint (get_operand2 (snd instr) s1))::word64) >> 32)) Y (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (mul_instr_sub1 (fst instr) (ucast (word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64)) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (write_cpu (ucast ((word_of_int (sint (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))) * sint (get_operand2 (snd instr) s2))::word64) >> 32)) Y (snd (fst (get_curr_win () s2))))))))))))))"
    by blast
qed

lemma div_write_new_val_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (div_write_new_val i result temp_V s1)) \<and>
t2 = snd (fst (div_write_new_val i result temp_V s2))"
shows "low_equal t1 t2"
proof (cases "(fst i) \<in> {arith_type UDIVcc,arith_type SDIVcc}")
  case True
  then show ?thesis using a1
  apply (simp add: div_write_new_val_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (clarsimp simp add: cpu_reg_val_low_equal)
  using write_cpu_low_equal by blast
next
  case False
  then show ?thesis using a1
  apply (simp add: div_write_new_val_def)
  by (simp add: return_def)
qed

lemma div_comp_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (div_comp instr rs1 rd operand2 s1)) \<and>
t2 = snd (fst (div_comp instr rs1 rd operand2 s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: div_comp_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (clarsimp simp add: get_curr_win_low_equal)
proof -
  assume a1: "low_equal s1 s2"
  have f2: "\<forall>s sa sb w wa wb sc. \<not> low_equal s sa \<or> sb \<noteq> snd (fst (write_reg w (wa::'a word) wb s)) \<or> sc \<noteq> snd (fst (write_reg w wa wb sa)) \<or> low_equal sb sc"
    by (meson write_reg_low_equal)
  have f3: "gets (\<lambda>s. ucast (get_CWP (cpu_reg_val PSR s))::'a word) = get_curr_win ()"
    by (simp add: get_curr_win_def)
  then have "((ucast (get_CWP (cpu_reg_val PSR s1)), s1), False) = (fst (get_curr_win () s1), snd (get_curr_win () s1))"
    by (metis (no_types) prod.collapse simpler_gets_def)
  then have f4: "ucast (get_CWP (cpu_reg_val PSR s1)) = fst (fst (get_curr_win () s1)) \<and> s1 = snd (fst (get_curr_win () s1))"
    by (metis prod.collapse prod.simps(1))
  have "((ucast (get_CWP (cpu_reg_val PSR s2)), s2), False) = (fst (get_curr_win () s2), snd (get_curr_win () s2))"
    using f3 by (metis (no_types) prod.collapse simpler_gets_def)
  then have f5: "ucast (get_CWP (cpu_reg_val PSR s2)) = fst (fst (get_curr_win () s2)) \<and> s2 = snd (fst (get_curr_win () s2))"
    by (metis (no_types) prod.collapse prod.simps(1))
  then have f6: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
    using f4 a1 by presburger
  have f7: "\<forall>s sa sb p w wa sc. \<not> low_equal (s::'a sparc_state) sa \<or> sb \<noteq> snd (fst (div_write_new_val p w wa s)) \<or> sc \<noteq> snd (fst (div_write_new_val p w wa sa)) \<or> low_equal sb sc"
    by (meson div_write_new_val_low_equal)
  have f8: "cpu_reg_val PSR s2 = cpu_reg_val PSR s1"
    using a1 by (simp add: cpu_reg_val_def low_equal_def)
  then have "fst (fst (get_curr_win () s2)) = ucast (get_CWP (cpu_reg_val PSR s1))"
    using f5 by presburger
  then have f9: "fst (fst (get_curr_win () s2)) = fst (fst (get_curr_win () s1))"
    using f4 by presburger
  have f10: "fst (fst (get_curr_win () s1)) = fst (fst (get_curr_win () s2))"
    using f8 f5 f4 by presburger
  have f11: "(word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))::word64) = word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))"
    using f5 f4 a1 by (metis (no_types) cpu_reg_val_def low_equal_def user_reg_val_low_equal)
  have f12: "ucast (get_CWP (cpu_reg_val PSR s1)) = fst (fst (get_curr_win () s2))"
    using f8 f5 by presburger
  then have "rd = 0 \<longrightarrow> (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) = user_reg_val (ucast (get_CWP (cpu_reg_val PSR s1))) 0 (snd (fst (get_curr_win () s1)))"
    using f6 user_reg_val_low_equal by fastforce
  then have f13: "rd = 0 \<longrightarrow> write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) 0 (snd (fst (get_curr_win () s1))) = write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1)))"
    using f12 f10 by presburger
  have f14: "write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) rd (snd (fst (get_curr_win () s2))) = write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))"
    using f12 f11 by auto
  have "write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) rd (snd (fst (get_curr_win () s1))) = write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))) \<and> write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) rd (snd (fst (get_curr_win () s2))) = write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) \<longrightarrow> low_equal (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))))))"
    using f6 f2 by metis
  moreover
  { assume "low_equal (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))))))"
    then have "low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))"
      using f11 f9 f7 by metis 
    moreover
    { assume "low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))))))))) \<noteq> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))"
      then have "div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2) = (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) \<longrightarrow> rd = 0"
        by fastforce }
    ultimately have "div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2) = (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) \<longrightarrow> rd = 0 \<or> (rd \<noteq> 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))) \<and> (rd = 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))))"
      by fastforce }
  moreover
  { assume "write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) rd (snd (fst (get_curr_win () s1))) \<noteq> write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1)))"
    then have "div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2) \<noteq> (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2))"
      using f12 f9 by fastforce }
  moreover
  { assume "write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (ucast (get_CWP (cpu_reg_val PSR s1))) rd (snd (fst (get_curr_win () s2))) \<noteq> write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))"
    then have "rd = 0"
      using f14 by presburger }
  moreover
  { assume "rd = 0"
    then have "rd = 0 \<and> low_equal (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))))))"
      using f13 f12 f6 f2 by metis 
    then have "rd = 0 \<and> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s1))) rd (snd (fst (get_curr_win () s1))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s1))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (if rd = 0 then user_reg_val (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2))) else div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))"
      using f11 f9 f7 by metis 
    then have "(rd \<noteq> 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))) \<and> (rd = 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))))"
      using f10 by fastforce }
  ultimately show "(rd \<noteq> 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (fst (fst (get_curr_win () s2))) rd (snd (fst (get_curr_win () s2)))))))))) \<and> (rd = 0 \<longrightarrow> low_equal (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s1))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s1))))))))) (snd (fst (div_write_new_val instr (div_comp_result instr (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2)) (div_comp_temp_V instr (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 32)) (ucast (div_comp_temp_64bit instr (word_cat (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (user_reg_val (fst (fst (get_curr_win () s2))) rs1 (snd (fst (get_curr_win () s2))))) operand2 >> 31))) (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0 (snd (fst (get_curr_win () s2))))))))))"
    using f9 by fastforce
qed

lemma div_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (div_instr instr s1)) \<and> t2 = snd (fst (div_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: div_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp add: return_def)
apply (auto simp add: get_operand2_low_equal)
 apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
 apply (auto simp add: traps_low_equal)
 apply (blast intro: mod_trap_low_equal)
using div_comp_low_equal by blast

lemma get_curr_win_traps_low_equal: 
assumes a1: "low_equal s1 s2"
shows "low_equal
(snd (fst (get_curr_win () s1))
  \<lparr>traps := insert some_trap (traps (snd (fst (get_curr_win () s1))))\<rparr>)
(snd (fst (get_curr_win () s2))
  \<lparr>traps := insert some_trap (traps (snd (fst (get_curr_win () s2))))\<rparr>)"
proof -
  from a1 have f1: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
    using get_curr_win2_low_equal by auto
  then have f2: "(traps (snd (fst (get_curr_win () s1)))) = 
    (traps (snd (fst (get_curr_win () s2))))"
    using traps_low_equal by auto
  then show ?thesis using f1 f2 mod_trap_low_equal
  by fastforce
qed

lemma save_restore_instr_sub1_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (save_retore_sub1 result new_cwp rd s1)) \<and> 
t2 = snd (fst (save_retore_sub1 result new_cwp rd s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: save_retore_sub1_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (auto simp add: cpu_reg_val_low_equal)
using write_cpu_low_equal write_reg_low_equal
by fastforce

lemma get_WIM_bit_low_equal: 
assumes a1: "low_equal s1 s2"
shows "get_WIM_bit (unat (((word_of_int ((uint (fst (fst (get_curr_win () s1))) - 1) mod NWINDOWS)))::word5))
 (cpu_reg_val WIM (snd (fst (get_curr_win () s1)))) =
get_WIM_bit (unat (((word_of_int ((uint (fst (fst (get_curr_win () s2))) -1) mod NWINDOWS)))::word5))
  (cpu_reg_val WIM (snd (fst (get_curr_win () s2))))"
proof -
  from a1 have f1: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
  using get_curr_win2_low_equal by blast
  then have f2: "(cpu_reg_val WIM (snd (fst (get_curr_win () s1)))) =
    (cpu_reg_val WIM (snd (fst (get_curr_win () s2))))"
  using cpu_reg_val_low_equal by auto
  from a1 have "(fst (fst (get_curr_win () s1))) = (fst (fst (get_curr_win () s2)))"
  using get_curr_win_low_equal by auto
  then show ?thesis using f1 f2
  by auto 
qed

lemma get_WIM_bit_low_equal2: 
assumes a1: "low_equal s1 s2"
shows "get_WIM_bit (unat (((word_of_int ((uint (fst (fst (get_curr_win () s1))) + 1) mod NWINDOWS)))::word5))
 (cpu_reg_val WIM (snd (fst (get_curr_win () s1)))) =
get_WIM_bit (unat (((word_of_int ((uint (fst (fst (get_curr_win () s2))) + 1) mod NWINDOWS)))::word5))
  (cpu_reg_val WIM (snd (fst (get_curr_win () s2))))"
proof -
  from a1 have f1: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
  using get_curr_win2_low_equal by blast
  then have f2: "(cpu_reg_val WIM (snd (fst (get_curr_win () s1)))) =
    (cpu_reg_val WIM (snd (fst (get_curr_win () s2))))"
  using cpu_reg_val_low_equal by auto
  from a1 have "(fst (fst (get_curr_win () s1))) = (fst (fst (get_curr_win () s2)))"
  using get_curr_win_low_equal by auto
  then show ?thesis using f1 f2
  by auto 
qed

lemma save_restore_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (save_restore_instr instr s1)) \<and> t2 = snd (fst (save_restore_instr instr s2))"
shows "low_equal t1 t2"
proof (cases "fst instr = ctrl_type SAVE")
  case True
  then have f1: "fst instr = ctrl_type SAVE" by auto
  then show ?thesis using a1
  apply (simp add: save_restore_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply auto
     apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
     apply (simp add: get_curr_win_traps_low_equal)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply (simp add: get_WIM_bit_low_equal)
   apply (simp add: get_WIM_bit_low_equal)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: get_curr_win_low_equal)
  using get_curr_win2_low_equal save_restore_instr_sub1_low_equal get_addr2_low_equal
  by metis 
next
  case False
  then show ?thesis using a1
  apply (simp add: save_restore_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply auto
     apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
     apply (simp add: get_curr_win_traps_low_equal)
    apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
    apply (simp add: get_WIM_bit_low_equal2)
   apply (simp add: get_WIM_bit_low_equal2)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: get_curr_win_low_equal)
  using get_curr_win2_low_equal save_restore_instr_sub1_low_equal get_addr2_low_equal
  by metis 
qed

lemma call_instr_low_equal: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (call_instr instr s1)) \<and> t2 = snd (fst (call_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: call_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (auto simp add: get_curr_win_low_equal)
using cpu_reg_val_low_equal get_curr_win2_low_equal
write_cpu_low_equal write_reg_low_equal
proof -
  assume a1: "low_equal s1 s2"
  assume "t1 = snd (fst (write_cpu (cpu_reg_val PC (snd (fst (get_curr_win () s1))) + (ucast (get_operand_w30 (snd instr ! 0)) << 2)) nPC (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (get_curr_win () s1)))) PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 15 (snd (fst (get_curr_win () s1)))))))))))"
  assume "t2 = snd (fst (write_cpu (cpu_reg_val PC (snd (fst (get_curr_win () s2))) + (ucast (get_operand_w30 (snd instr ! 0)) << 2)) nPC (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (get_curr_win () s2)))) PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 15 (snd (fst (get_curr_win () s2)))))))))))"
  have "\<forall>c. cpu_reg_val c (snd (fst (get_curr_win () s1))) = cpu_reg_val c (snd (fst (get_curr_win () s2)))"
    using a1 by (meson cpu_reg_val_low_equal get_curr_win2_low_equal)
  then show "low_equal (snd (fst (write_cpu (cpu_reg_val PC (snd (fst (get_curr_win () s1))) + (ucast (get_operand_w30 (snd instr ! 0)) << 2)) nPC (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (get_curr_win () s1)))) PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 15 (snd (fst (get_curr_win () s1)))))))))))) (snd (fst (write_cpu (cpu_reg_val PC (snd (fst (get_curr_win () s2))) + (ucast (get_operand_w30 (snd instr ! 0)) << 2)) nPC (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (get_curr_win () s2)))) PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 15 (snd (fst (get_curr_win () s2))))))))))))"
    using a1 by (metis (no_types) get_curr_win2_low_equal write_cpu_low_equal write_reg_low_equal)
qed

lemma jmpl_instr_low_equal_sub1: 
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (write_cpu (get_addr (snd instr) (snd (fst (get_curr_win () s2)))) nPC
  (snd (fst (write_cpu (cpu_reg_val nPC 
  (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
  (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
  (snd (fst (get_curr_win () s1)))))))
  PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
  (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
  (snd (fst (get_curr_win () s1))))))))))) \<and>
t2 = snd (fst (write_cpu (get_addr (snd instr) (snd (fst (get_curr_win () s2)))) nPC
  (snd (fst (write_cpu (cpu_reg_val nPC
  (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
  (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
  (snd (fst (get_curr_win () s2)))))))
  PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
  (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
  (snd (fst (get_curr_win () s2)))))))))))"
shows "low_equal t1 t2"
proof -
  from a1 have f1: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
  using get_curr_win2_low_equal by blast
  then have f2: "(cpu_reg_val PC (snd (fst (get_curr_win () s1)))) =
    (cpu_reg_val PC (snd (fst (get_curr_win () s2))))"
  using cpu_reg_val_low_equal by blast
  then have f3: "low_equal 
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s1))))))
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s2))))))"
  using f1 write_reg_low_equal by fastforce
  then have "(cpu_reg_val nPC 
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s1))))))) =
    (cpu_reg_val nPC
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s2)))))))"
  using cpu_reg_val_low_equal by auto
  then have f4: "low_equal
    (snd (fst (write_cpu (cpu_reg_val nPC 
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s1)))))))
    PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s1))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s1)))))))))
    (snd (fst (write_cpu (cpu_reg_val nPC
    (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s2)))))))
    PC (snd (fst (write_reg (cpu_reg_val PC (snd (fst (get_curr_win () s2))))
    (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! 3))
    (snd (fst (get_curr_win () s2)))))))))"
  using f3 write_cpu_low_equal by fastforce
  then show ?thesis using write_cpu_low_equal
  using assms by blast  
qed

lemma jmpl_instr_low_equal_sub2:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (write_cpu (get_addr (snd instr) (snd (fst (get_curr_win () s2)))) nPC
  (snd (fst (write_cpu (cpu_reg_val nPC
  (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s1))))))) PC (snd (fst (write_reg
  (user_reg_val (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s1))))))))))) \<and>
t2 = snd (fst (write_cpu (get_addr (snd instr) (snd (fst (get_curr_win () s2)))) nPC
  (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (write_reg
  (user_reg_val (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s2))))))) PC (snd (fst (write_reg
  (user_reg_val (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
  (snd (fst (get_curr_win () s2)))))))))))"
shows "low_equal t1 t2"
proof -
  from a1 have f1: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
  using get_curr_win2_low_equal by blast
  then have f2: "(user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))) = 
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2))))"
  using user_reg_val_low_equal by blast
  then have f3: "low_equal 
    (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1))))))
    (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2))))))"
  using f1 write_reg_low_equal by fastforce
  then have "(cpu_reg_val nPC
    (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1))))))) = 
    (cpu_reg_val nPC (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))))))"
  using cpu_reg_val_low_equal by blast
  then have "low_equal 
    (snd (fst (write_cpu (cpu_reg_val nPC
    (snd (fst (write_reg (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1))))))) PC (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s1)))))))))
    (snd (fst (write_cpu (cpu_reg_val nPC (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2))))))) PC (snd (fst (write_reg
    (user_reg_val (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) 0
    (snd (fst (get_curr_win () s2)))))))))"
  using f1 f2 f3 write_cpu_low_equal by fastforce
  then show ?thesis 
  using write_cpu_low_equal
  using assms by blast 
qed

lemma jmpl_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (jmpl_instr instr s1)) \<and> t2 = snd (fst (jmpl_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: jmpl_instr_def)
apply (simp add: Let_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply auto
   apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
   apply (simp add: get_curr_win_traps_low_equal)
  apply (simp add: get_addr2_low_equal)
 apply (simp add: get_addr2_low_equal)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (simp_all add: get_addr2_low_equal)
apply (simp_all add: get_curr_win_low_equal)
apply (case_tac "get_operand_w5 (snd instr ! 3) \<noteq> 0")
apply auto
 using jmpl_instr_low_equal_sub1 apply blast
apply (simp_all add: get_curr_win_low_equal)
using jmpl_instr_low_equal_sub2 by blast

lemma rett_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
\<not> snd (rett_instr instr s1) \<and>
\<not> snd (rett_instr instr s2) \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
t1 = snd (fst (rett_instr instr s1)) \<and> t2 = snd (fst (rett_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: rett_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
apply auto
   apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
   apply (simp add: return_def)
   using mod_trap_low_equal traps_low_equal apply fastforce
  using cpu_reg_val_low_equal apply fastforce
 using cpu_reg_val_low_equal apply fastforce
apply (simp add: bind_def h1_def h2_def Let_def)
by (simp add: case_prod_unfold fail_def)

lemma read_state_reg_low_equal:
assumes a1: "low_equal s1 s2 \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
t1 = snd (fst (read_state_reg_instr instr s1)) \<and> 
t2 = snd (fst (read_state_reg_instr instr s2))"
shows "low_equal t1 t2"
proof (cases "(fst instr \<in> {sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR} \<or> 
        (fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 ((snd instr)!0))))")
  case True   
  then have "(fst instr \<in> {sreg_type RDPSR,sreg_type RDWIM,sreg_type RDTBR} \<or> 
        (fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 ((snd instr)!0))))
        \<and> ((ucast (get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s1))))))::word1) = 0
        \<and> ((ucast (get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2))))))::word1) = 0"
    by (metis assms get_curr_win_privilege)
  then show ?thesis using a1
  apply (simp add: read_state_reg_instr_def)
  apply (simp add: Let_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (simp add: case_prod_unfold)
  apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
  apply clarsimp
  using get_curr_win_traps_low_equal
  by auto  
next
  case False
  then have f1: "\<not>((fst instr = sreg_type RDPSR \<or>
                    fst instr = sreg_type RDWIM \<or>
                    fst instr = sreg_type RDTBR \<or>
                    fst instr = sreg_type RDASR \<and> privileged_ASR (get_operand_w5 (snd instr ! 0))))"
    by blast 
  then show ?thesis 
  proof (cases "illegal_instruction_ASR (get_operand_w5 ((snd instr)!0))")
    case True
    then show ?thesis using a1 f1
    apply read_state_reg_instr_privilege_proof
    by (simp add: illegal_instruction_ASR_def)    
  next
    case False
    then have f2: "\<not>(illegal_instruction_ASR (get_operand_w5 ((snd instr)!0)))" 
      by auto
    then show ?thesis 
    proof (cases "(get_operand_w5 ((snd instr)!1)) \<noteq> 0")
      case True
      then have f3: "(get_operand_w5 ((snd instr)!1)) \<noteq> 0" 
        by auto
      then show ?thesis 
      proof (cases "fst instr = sreg_type RDY")
        case True
        then show ?thesis using a1 f1 f2 f3
        apply (simp add: read_state_reg_instr_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        apply (auto simp add: get_curr_win_low_equal)
        using cpu_reg_val_low_equal get_curr_win2_low_equal write_reg_low_equal
        proof -
          assume "low_equal s1 s2"
          then have "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
            by (meson get_curr_win2_low_equal)
          then show "low_equal (snd (fst (write_reg (cpu_reg_val Y (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (cpu_reg_val Y (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))))))"
            using cpu_reg_val_low_equal write_reg_low_equal by fastforce
        qed
      next
        case False
        then have f4: "\<not>(fst instr = sreg_type RDY)" by auto
        then show ?thesis 
        proof (cases "fst instr = sreg_type RDASR")
          case True
          then show ?thesis using a1 f1 f2 f3 f4
          apply read_state_reg_instr_privilege_proof
          apply (clarsimp simp add: get_curr_win_low_equal)
          using cpu_reg_val_low_equal get_curr_win2_low_equal write_reg_low_equal
          proof -
            assume a1: "low_equal s1 s2"
            then have "cpu_reg_val (ASR (get_operand_w5 (snd instr ! 0))) (snd (fst (get_curr_win () s1))) = cpu_reg_val (ASR (get_operand_w5 (snd instr ! 0))) (snd (fst (get_curr_win () s2)))"
              by (meson cpu_reg_val_low_equal get_curr_win2_low_equal)
            then show "low_equal (snd (fst (write_reg (cpu_reg_val (ASR (get_operand_w5 (snd instr ! 0))) (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (cpu_reg_val (ASR (get_operand_w5 (snd instr ! 0))) (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))))))"
              using a1 by (metis (no_types) get_curr_win2_low_equal write_reg_low_equal)
          qed
        next
          case False
          then have f5: "\<not>(fst instr = sreg_type RDASR)" by auto
          then show ?thesis using a1 f1 f2 f3 f4 f5
          apply read_state_reg_instr_privilege_proof
          apply (clarsimp simp add: get_curr_win_low_equal)
          using cpu_reg_val_low_equal get_curr_win2_low_equal write_reg_low_equal
          proof -
            assume a1: "low_equal s1 s2"
            assume a2: "t1 = snd (fst (write_reg (cpu_reg_val TBR (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))))"
            assume "t2 = snd (fst (write_reg (cpu_reg_val TBR (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2)))))"
            have "\<forall>s. \<not> low_equal (snd (fst (get_curr_win () s1))) s \<or> snd (fst (write_reg (cpu_reg_val TBR s) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))))) = t1"
              using a2 by (simp add: cpu_reg_val_low_equal)
            then show "low_equal (snd (fst (write_reg (cpu_reg_val TBR (snd (fst (get_curr_win () s1)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1)))))) (snd (fst (write_reg (cpu_reg_val TBR (snd (fst (get_curr_win () s2)))) (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))))))"
              using a2 a1 by (metis (no_types) get_curr_win2_low_equal write_reg_low_equal)
          qed
        qed
      qed
    next
      case False
      then show ?thesis using a1 f1 f2
      apply (simp add: read_state_reg_instr_def)
      apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
      apply (simp add: return_def) 
      apply clarsimp
      apply (simp add: case_prod_unfold)
      using get_curr_win2_low_equal by auto
    qed
  qed
qed

lemma get_s_get_curr_win:
assumes a1: "low_equal s1 s2"
shows "get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))) =
get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2))))"
proof - 
  from a1 have "low_equal (snd (fst (get_curr_win () s1))) 
    (snd (fst (get_curr_win () s2)))"
  using get_curr_win2_low_equal by blast
  then show ?thesis
  using cpu_reg_val_low_equal
  by fastforce  
qed

lemma write_state_reg_low_equal:
assumes a1: "low_equal s1 s2 \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
t1 = snd (fst (write_state_reg_instr instr s1)) \<and>
t2 = snd (fst (write_state_reg_instr instr s2))"
shows "low_equal t1 t2"
proof (cases "fst instr = sreg_type WRY")
  case True
  then show ?thesis using a1
  apply write_state_reg_instr_privilege_proof
  apply (simp add: simpler_modify_def)
  apply (simp add: delayed_pool_add_def DELAYNUM_def)
  apply (auto simp add: get_curr_win_low_equal)
  using get_curr_win2_low_equal cpu_reg_mod_low_equal
  user_reg_val_low_equal get_operand2_low_equal
  proof -
    assume a1: "low_equal s1 s2"
    assume "t2 = cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s2)))) Y (snd (fst (get_curr_win () s2)))"
    assume "t1 = cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s1)))) Y (snd (fst (get_curr_win () s1)))"
    have f2: "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
      using a1 by (meson get_curr_win2_low_equal)
    then have f3: "\<And>w wa. user_reg_val w wa (snd (fst (get_curr_win () s2))) = user_reg_val w wa (snd (fst (get_curr_win () s1)))"
      by (simp add: user_reg_val_low_equal)
    have "\<And>is. get_operand2 is (snd (fst (get_curr_win () s2))) = get_operand2 is (snd (fst (get_curr_win () s1)))"
      using f2 by (simp add: get_operand2_low_equal)
    then show "low_equal (cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s1)))) Y (snd (fst (get_curr_win () s1)))) (cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s2)))) Y (snd (fst (get_curr_win () s2))))"
      using f3 f2 by (metis cpu_reg_mod_low_equal)
  qed
next
  case False
  then have f1: "\<not>(fst instr = sreg_type WRY)" by auto
  then show ?thesis
  proof (cases "fst instr = sreg_type WRASR")
    case True
    then have f1_1: "fst instr = sreg_type WRASR" by auto
    then show ?thesis
    proof (cases "privileged_ASR (get_operand_w5 (snd instr ! 3)) \<and>
                  get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))) = 0")
      case True
      then show ?thesis using a1 f1 f1_1
      apply write_state_reg_instr_privilege_proof
      apply (clarsimp simp add: get_s_get_curr_win)
      apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
      apply (clarsimp simp add: get_curr_win3_low_equal)
      using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
      by fastforce
    next
      case False
      then have f1_2: "\<not> (privileged_ASR (get_operand_w5 (snd instr ! 3)) \<and>
      get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))) = 0)"
      by auto
      then show ?thesis
      proof (cases "illegal_instruction_ASR (get_operand_w5 (snd instr ! 3))")
        case True
        then show ?thesis using a1 f1 f1_1 f1_2
        apply write_state_reg_instr_privilege_proof
        apply (clarsimp simp add: get_s_get_curr_win)
        apply auto
         apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
         apply (clarsimp simp add: get_curr_win3_low_equal)
         using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
         apply fastforce
        apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
        apply (clarsimp simp add: get_curr_win3_low_equal)
        using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
        by fastforce
      next
        case False
        then show ?thesis using a1 f1 f1_1 f1_2
        apply write_state_reg_instr_privilege_proof
        apply (clarsimp simp add: get_s_get_curr_win)
        apply auto
         apply (simp add: simpler_modify_def)
         apply (simp add: delayed_pool_add_def DELAYNUM_def)
         apply (auto simp add: get_curr_win_low_equal)      
         using get_curr_win2_low_equal cpu_reg_mod_low_equal
         user_reg_val_low_equal get_operand2_low_equal
         proof -
           assume a1: "low_equal s1 s2"
           assume "t2 = cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s2)))) (ASR (get_operand_w5 (snd instr ! 3))) (snd (fst (get_curr_win () s2)))"
           assume "t1 = cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s1)))) (ASR (get_operand_w5 (snd instr ! 3))) (snd (fst (get_curr_win () s1)))"
           have "low_equal (snd (fst (get_curr_win () s1))) (snd (fst (get_curr_win () s2)))"
            using a1 by (meson get_curr_win2_low_equal)
           then show "low_equal (cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s1))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s1)))) (ASR (get_operand_w5 (snd instr ! 3))) (snd (fst (get_curr_win () s1)))) (cpu_reg_mod (user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0)) (snd (fst (get_curr_win () s2))) XOR get_operand2 (snd instr) (snd (fst (get_curr_win () s2)))) (ASR (get_operand_w5 (snd instr ! 3))) (snd (fst (get_curr_win () s2))))"
            using cpu_reg_mod_low_equal get_operand2_low_equal user_reg_val_low_equal by fastforce
         next
           assume f1: "\<not> illegal_instruction_ASR (get_operand_w5 (snd instr ! 3))"
           assume f2: "fst instr = sreg_type WRASR"
           assume f3: "snd (fst (write_state_reg_instr instr s1)) =
    snd (fst (modify
               (delayed_pool_add
                 (DELAYNUM,
                  user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s1))) XOR
                  get_operand2 (snd instr) (snd (fst (get_curr_win () s1))),
                  ASR (get_operand_w5 (snd instr ! 3))))
               (snd (fst (get_curr_win () s1))))) "
           assume f4: "snd (fst (write_state_reg_instr instr s2)) =
    snd (fst (modify
               (delayed_pool_add
                 (DELAYNUM,
                  user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                   (snd (fst (get_curr_win () s2))) XOR
                  get_operand2 (snd instr) (snd (fst (get_curr_win () s2))),
                  ASR (get_operand_w5 (snd instr ! 3))))
               (snd (fst (get_curr_win () s2)))))"
           assume f5: "low_equal s1 s2"
           assume f6: "ucast (get_S (cpu_reg_val PSR s1)) = 0"
           assume f7: "ucast (get_S (cpu_reg_val PSR s2)) = 0"
           assume f8: "t1 = snd (fst (modify
                    (delayed_pool_add
                      (DELAYNUM,
                       user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                        (snd (fst (get_curr_win () s1))) XOR
                       get_operand2 (snd instr) (snd (fst (get_curr_win () s1))),
                       ASR (get_operand_w5 (snd instr ! 3))))
                    (snd (fst (get_curr_win () s1)))))"
           assume f9: "t2 = snd (fst (modify
                    (delayed_pool_add
                      (DELAYNUM,
                       user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                        (snd (fst (get_curr_win () s2))) XOR
                       get_operand2 (snd instr) (snd (fst (get_curr_win () s2))),
                       ASR (get_operand_w5 (snd instr ! 3))))
                    (snd (fst (get_curr_win () s2)))))"
           assume f10: "get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))) \<noteq> 0"
           assume f11: "(\<And>s1 s2 t1 t2.
            low_equal s1 s2 \<Longrightarrow>
            t1 = snd (fst (get_curr_win () s1)) \<Longrightarrow> t2 = snd (fst (get_curr_win () s2)) \<Longrightarrow> low_equal t1 t2)"
           assume f12: "(\<And>s1 s2 t1 w cr t2.
            low_equal s1 s2 \<and> t1 = cpu_reg_mod w cr s1 \<and> t2 = cpu_reg_mod w cr s2 \<Longrightarrow> low_equal t1 t2)"
           assume f13: "(\<And>s1 s2 win ur. low_equal s1 s2 \<Longrightarrow> user_reg_val win ur s1 = user_reg_val win ur s2)"
           assume f14: "(\<And>s1 s2 op_list. low_equal s1 s2 \<Longrightarrow> get_operand2 op_list s1 = get_operand2 op_list s2)"
           show "low_equal
     (snd (fst (modify
                 (delayed_pool_add
                   (DELAYNUM,
                    user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                     (snd (fst (get_curr_win () s1))) XOR
                    get_operand2 (snd instr) (snd (fst (get_curr_win () s1))),
                    ASR (get_operand_w5 (snd instr ! 3))))
                 (snd (fst (get_curr_win () s1))))))
     (snd (fst (modify
                 (delayed_pool_add
                   (DELAYNUM,
                    user_reg_val (fst (fst (get_curr_win () s2))) (get_operand_w5 (snd instr ! Suc 0))
                     (snd (fst (get_curr_win () s2))) XOR
                    get_operand2 (snd instr) (snd (fst (get_curr_win () s2))),
                    ASR (get_operand_w5 (snd instr ! 3))))
                 (snd (fst (get_curr_win () s2))))))"
           using f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
           using Sparc_Properties.ucast_0 assms get_curr_win_privilege by blast            
         qed
      qed
    qed
  next
    case False
    then have f2: "\<not>(fst instr = sreg_type WRASR)" by auto
    have f3: "get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s1)))) = 0 \<and>
      get_S (cpu_reg_val PSR (snd (fst (get_curr_win () s2)))) = 0"
      using get_curr_win_privilege a1 by (metis ucast_id)
    then show ?thesis 
    proof (cases "fst instr = sreg_type WRPSR")
      case True
      then show ?thesis using a1 f1 f2 f3
      apply write_state_reg_instr_privilege_proof
      apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
      apply (clarsimp simp add: get_curr_win3_low_equal)
      using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
      by fastforce      
    next
      case False
      then have f4: "\<not>(fst instr = sreg_type WRPSR)" by auto
      then show ?thesis 
      proof (cases "fst instr = sreg_type WRWIM")  
        case True
        then show ?thesis using a1 f1 f2 f3 f4
        apply write_state_reg_instr_privilege_proof
        apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
        apply (clarsimp simp add: get_curr_win3_low_equal)
        using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
        by fastforce 
      next
        case False
        then have f5: "\<not>(fst instr = sreg_type WRWIM)" by auto
        then show ?thesis using a1 f1 f2 f3 f4 f5
        apply write_state_reg_instr_privilege_proof
        apply (simp add: raise_trap_def add_trap_set_def simpler_modify_def)
        apply (clarsimp simp add: get_curr_win3_low_equal)
        using traps_low_equal mod_trap_low_equal get_curr_win2_low_equal
        by fastforce        
      qed
    qed
  qed
qed

lemma flush_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (flush_instr instr s1)) \<and>
t2 = snd (fst (flush_instr instr s2))"
shows "low_equal t1 t2"
using a1
apply (simp add: flush_instr_def)
apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def simpler_modify_def)
apply (simp add: flush_cache_all_def)
apply (simp add: low_equal_def)
apply (simp add: user_accessible_def)
apply (simp add: mem_equal_def)
by auto

lemma branch_instr_sub1_low_equal:
assumes a1: "low_equal s1 s2"
shows "branch_instr_sub1 instr_name s1 = branch_instr_sub1 instr_name s2"
using a1 apply (simp add: branch_instr_sub1_def)
by (simp add: low_equal_def)

lemma set_annul_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (set_annul True s1)) \<and>
t2 = snd (fst (set_annul True s2))"
shows "low_equal t1 t2"
using a1 apply (simp add: set_annul_def)
apply (simp add: simpler_modify_def annul_mod_def)
using state_var2_low_equal state_var_low_equal 
by fastforce

lemma branch_instr_low_equal_sub0:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (write_cpu (cpu_reg_val PC s2 +
  sign_ext24 (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
  nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1))))) \<and>
t2 = snd (fst (write_cpu (cpu_reg_val PC s2 +
  sign_ext24 (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
  nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2)))))"
shows "low_equal t1 t2"
proof -
  from a1 have "low_equal
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1)))
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2)))"
  using write_cpu_low_equal by blast
  then show ?thesis
  using a1 write_cpu_low_equal by blast
qed

lemma branch_instr_low_equal_sub1:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (set_annul True (snd (fst (write_cpu
  (cpu_reg_val PC s2 + sign_ext24
  (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
  nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1)))))))) \<and>
t2 = snd (fst (set_annul True (snd (fst (write_cpu
  (cpu_reg_val PC s2 + sign_ext24
  (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
  nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2))))))))"
shows "low_equal t1 t2"
proof -
  from a1 have "low_equal 
    (snd (fst (write_cpu
    (cpu_reg_val PC s2 + sign_ext24
    (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
    nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1))))))
    (snd (fst (write_cpu
    (cpu_reg_val PC s2 + sign_ext24
    (ucast (get_operand_w22 (snd instr ! Suc 0)) << 2))
    nPC (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2))))))"
  using branch_instr_low_equal_sub0 by blast  
  then show ?thesis using a1
  using set_annul_low_equal by blast  
qed

lemma branch_instr_low_equal_sub2:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (set_annul True
  (snd (fst (write_cpu (cpu_reg_val nPC s2 + 4) nPC
  (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1)))))))) \<and>
t2 = snd (fst (set_annul True
  (snd (fst (write_cpu (cpu_reg_val nPC s2 + 4) nPC
   (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2))))))))"
shows "low_equal t1 t2"
proof -
  from a1 have "low_equal
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1)))
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2)))"
  using write_cpu_low_equal by blast
  then have "low_equal 
    (snd (fst (write_cpu (cpu_reg_val nPC s2 + 4) nPC
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s1))))))
    (snd (fst (write_cpu (cpu_reg_val nPC s2 + 4) nPC
    (snd (fst (write_cpu (cpu_reg_val nPC s2) PC s2))))))"
  using write_cpu_low_equal by blast
  then show ?thesis using a1
  using set_annul_low_equal by blast
qed

lemma branch_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
t1 = snd (fst (branch_instr instr s1)) \<and>
t2 = snd (fst (branch_instr instr s2))"
shows "low_equal t1 t2"
using a1 
apply (simp add: branch_instr_def)
apply (simp add: Let_def simpler_gets_def bind_def h1_def h2_def)
apply (simp add: case_prod_unfold return_def)
apply clarsimp
apply (simp add: branch_instr_sub1_low_equal)
apply (simp_all add: cpu_reg_val_low_equal)
apply (cases "branch_instr_sub1 (fst instr) s2 = 1")
 apply clarsimp
 apply (simp add: bind_def h1_def h2_def Let_def)
 apply (simp_all add: cpu_reg_val_low_equal)
 apply (simp add: case_prod_unfold)
 apply (cases "fst instr = bicc_type BA \<and> get_operand_flag (snd instr ! 0) = 1")
  apply clarsimp
  using branch_instr_low_equal_sub1 apply blast
 apply clarsimp
 apply (simp add: return_def)
 using branch_instr_low_equal_sub0 apply fastforce
apply (simp add: bind_def h1_def h2_def Let_def)
apply (simp add: case_prod_unfold)
apply (cases "get_operand_flag (snd instr ! 0) = 1")
 apply clarsimp
 apply (simp_all add: cpu_reg_val_low_equal)
 using branch_instr_low_equal_sub2 apply metis
apply (simp add: return_def)
using write_cpu_low_equal by metis

lemma dispath_instr_low_equal:
assumes a1: "low_equal s1 s2 \<and>
((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
\<not> snd (dispatch_instruction instr s1) \<and>
\<not> snd (dispatch_instruction instr s2) \<and>
t1 = (snd (fst (dispatch_instruction instr s1))) \<and>
t2 = (snd (fst (dispatch_instruction instr s2)))"
shows "low_equal t1 t2"
proof (cases "get_trap_set s1 = {}")
  case True
  then have f_no_traps: "get_trap_set s1 = {} \<and> get_trap_set s2 = {}"
    using a1 by (simp add: low_equal_def get_trap_set_def)
  then show ?thesis
  proof (cases "fst instr \<in> {load_store_type LDSB,load_store_type LDUB,
        load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
        load_store_type LDA,load_store_type LDD}")
    case True
    then show ?thesis using a1 f_no_traps
    apply dispath_instr_privilege_proof
    by (blast intro: load_instr_low_equal)
  next
    case False
    then have f1: "fst instr \<notin> {load_store_type LDSB, load_store_type LDUB, 
      load_store_type LDUBA, load_store_type LDUH,
      load_store_type LD, load_store_type LDA, load_store_type LDD}" 
      by auto
    then show ?thesis 
    proof (cases "fst instr \<in> {load_store_type STB,load_store_type STH,
        load_store_type ST,load_store_type STA,load_store_type STD}")
      case True
      then show ?thesis using a1 f_no_traps f1
      apply dispath_instr_privilege_proof
      using store_instr_low_equal by blast      
    next
      case False
      then have f2: "\<not>(fst instr \<in> {load_store_type STB,load_store_type STH,
        load_store_type ST,load_store_type STA,load_store_type STD})"
        by auto
      then show ?thesis 
      proof (cases "fst instr \<in> {sethi_type SETHI}")
        case True
        then show ?thesis using a1 f_no_traps f1 f2
        apply dispath_instr_privilege_proof
        by (auto intro: sethi_low_equal)        
      next
        case False
        then have f3: "\<not>(fst instr \<in> {sethi_type SETHI})"
          by auto
        then show ?thesis 
        proof (cases "fst instr \<in> {nop_type NOP}")
          case True
          then show ?thesis using a1 f_no_traps f1 f2 f3
          apply dispath_instr_privilege_proof
          by (auto intro: nop_low_equal)
        next
          case False
          then have f4: "\<not>(fst instr \<in> {nop_type NOP})" 
            by auto
          then show ?thesis 
          proof (cases "fst instr \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
            logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
            logic_type XORs,logic_type XNOR}")
            case True
            then show ?thesis using a1 f_no_traps f1 f2 f3 f4
            apply dispath_instr_privilege_proof
            using logical_instr_low_equal by blast
          next
            case False
            then have f5: "\<not>(fst instr \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
            logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
            logic_type XORs,logic_type XNOR})"
              by auto
            then show ?thesis 
            proof (cases "fst instr \<in> {shift_type SLL,shift_type SRL,shift_type SRA}")
              case True
              then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 
              apply dispath_instr_privilege_proof
              using shift_instr_low_equal by blast
            next
              case False
              then have f6: "\<not>(fst instr \<in> {shift_type SLL,shift_type SRL,shift_type SRA})"
                by auto
              then show ?thesis 
              proof (cases "fst instr \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX}")
                case True
                then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6
                apply dispath_instr_privilege_proof
                using add_instr_low_equal by blast
              next
                case False
                then have f7: "\<not>(fst instr \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX})"
                  by auto
                then show ?thesis
                proof (cases "fst instr \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX}")
                  case True
                  then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 
                  apply dispath_instr_privilege_proof
                  using sub_instr_low_equal by blast
                next
                  case False
                  then have f8: "\<not>(fst instr \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX})"
                    by auto
                  then show ?thesis
                  proof (cases "fst instr \<in> {arith_type UMUL,arith_type SMUL,arith_type SMULcc}")
                    case True
                    then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8
                    apply dispath_instr_privilege_proof
                    using mul_instr_low_equal by blast
                  next
                    case False
                    then have f9: "\<not>(fst instr \<in> {arith_type UMUL,arith_type SMUL,
                      arith_type SMULcc})"
                      by auto
                    then show ?thesis 
                    proof (cases "fst instr \<in> {arith_type UDIV,arith_type UDIVcc,arith_type SDIV}")
                      case True
                      then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9
                      apply dispath_instr_privilege_proof
                      using div_instr_low_equal by blast
                    next
                      case False
                      then have f10: "\<not>(fst instr \<in> {arith_type UDIV,
                        arith_type UDIVcc,arith_type SDIV})"
                        by auto
                      then show ?thesis 
                      proof (cases "fst instr \<in> {ctrl_type SAVE,ctrl_type RESTORE}")
                        case True
                        then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 f10
                        apply dispath_instr_privilege_proof
                        using save_restore_instr_low_equal by blast
                      next
                        case False
                        then have f11: "\<not>(fst instr \<in> {ctrl_type SAVE,ctrl_type RESTORE})"
                          by auto
                        then show ?thesis 
                        proof (cases "fst instr \<in> {call_type CALL}")
                          case True
                          then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11
                          apply dispath_instr_privilege_proof
                          using call_instr_low_equal by blast                          
                        next
                          case False
                          then have f12: "\<not>(fst instr \<in> {call_type CALL})" by auto
                          then show ?thesis
                          proof (cases "fst instr \<in> {ctrl_type JMPL}")
                            case True
                            then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12
                            apply dispath_instr_privilege_proof
                            using jmpl_instr_low_equal by blast
                          next
                            case False
                            then have f13: "\<not>(fst instr \<in> {ctrl_type JMPL})" by auto
                            then show ?thesis 
                            proof (cases "fst instr \<in> {ctrl_type RETT}")
                              case True
                              then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 
                                f11 f12 f13
                              apply dispath_instr_privilege_proof
                              using rett_instr_low_equal by blast
                            next
                              case False
                              then have f14: "\<not>(fst instr \<in> {ctrl_type RETT})" by auto
                              then show ?thesis 
                              proof (cases "fst instr \<in> {sreg_type RDY,sreg_type RDPSR,
                                sreg_type RDWIM, sreg_type RDTBR}")
                                case True
                                then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 
                                  f11 f12 f13 f14
                                apply dispath_instr_privilege_proof
                                using read_state_reg_low_equal by blast
                              next
                                case False
                                then have f15: "\<not>(fst instr \<in> {sreg_type RDY,sreg_type RDPSR,
                                sreg_type RDWIM, sreg_type RDTBR})" by auto
                                then show ?thesis
                                proof (cases "fst instr \<in> {sreg_type WRY,sreg_type WRPSR,
                                  sreg_type WRWIM, sreg_type WRTBR}")
                                  case True
                                  then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 
                                    f10 f11 f12 f13 f14 f15 
                                  apply dispath_instr_privilege_proof
                                  using write_state_reg_low_equal by blast
                                next
                                  case False
                                  then have f16: "\<not>(fst instr \<in> {sreg_type WRY,sreg_type WRPSR,
                                  sreg_type WRWIM, sreg_type WRTBR})" by auto
                                  then show ?thesis
                                  proof (cases "fst instr \<in> {load_store_type FLUSH}")
                                    case True
                                    then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 f9 
                                      f10 f11 f12 f13 f14 f15 f16 
                                    apply dispath_instr_privilege_proof
                                    using flush_instr_low_equal by blast
                                  next
                                    case False
                                    then have f17: "\<not>(fst instr \<in> {load_store_type FLUSH})" by auto
                                    then show ?thesis 
                                    proof (cases "fst instr \<in> {bicc_type BE,bicc_type BNE,
                                      bicc_type BGU,bicc_type BLE,bicc_type BL,bicc_type BGE,
                                      bicc_type BNEG,bicc_type BG,bicc_type BCS,bicc_type BLEU,
                                      bicc_type BCC,bicc_type BA,bicc_type BN}")
                                      case True
                                      then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 
                                        f9 f10 f11 f12 f13 f14 f15 f16 f17
                                      apply dispath_instr_privilege_proof
                                      using branch_instr_low_equal by blast
                                    next
                                      case False
                                      then show ?thesis using a1 f_no_traps f1 f2 f3 f4 f5 f6 f7 f8 
                                        f9 f10 f11 f12 f13 f14 f15 f16 f17
                                      apply dispath_instr_privilege_proof
                                      by (simp add: fail_def)
                                    qed
                                  qed
                                qed
                              qed
                            qed
                          qed
                        qed
                      qed
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
next
  case False
  then have "get_trap_set s1 \<noteq> {} \<and> get_trap_set s2 \<noteq> {}" 
    using a1 by (simp add: low_equal_def get_trap_set_def)
  then show ?thesis using a1
  apply (simp add: dispatch_instruction_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def)
  apply (simp add: Let_def)
  by (simp add: return_def)
qed

lemma execute_instr_sub1_low_equal:
assumes a1: "low_equal s1 s2 \<and>
\<not> snd (execute_instr_sub1 instr s1) \<and>
\<not> snd (execute_instr_sub1 instr s2) \<and>
t1 = (snd (fst (execute_instr_sub1 instr s1))) \<and>
t2 = (snd (fst (execute_instr_sub1 instr s2)))"
shows "low_equal t1 t2"
proof (cases "get_trap_set s1 = {}")
  case True
  then have "get_trap_set s1 = {} \<and> get_trap_set s2 = {}"
    using a1 by (simp add: low_equal_def get_trap_set_def)
  then show ?thesis using a1
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  apply (case_tac "fst instr \<noteq> call_type CALL \<and>
                fst instr \<noteq> ctrl_type RETT \<and>
                fst instr \<noteq> ctrl_type JMPL \<and>
                fst instr \<noteq> bicc_type BE \<and>
                fst instr \<noteq> bicc_type BNE \<and>
                fst instr \<noteq> bicc_type BGU \<and>
                fst instr \<noteq> bicc_type BLE \<and>
                fst instr \<noteq> bicc_type BL \<and>
                fst instr \<noteq> bicc_type BGE \<and>
                fst instr \<noteq> bicc_type BNEG \<and>
                fst instr \<noteq> bicc_type BG \<and>
                fst instr \<noteq> bicc_type BCS \<and>
                fst instr \<noteq> bicc_type BLEU \<and>
                fst instr \<noteq> bicc_type BCC \<and>
                fst instr \<noteq> bicc_type BA \<and> fst instr \<noteq> bicc_type BN")
   apply clarsimp
   apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
   apply (simp add: case_prod_unfold)
   apply (simp add: low_equal_def)
   apply (simp add: cpu_reg_val_def write_cpu_def cpu_reg_mod_def)
   apply (simp add: simpler_modify_def return_def)
   apply (simp add: user_accessible_mod_cpu_reg mem_equal_mod_cpu_reg)
   apply clarsimp
  by (auto simp add: return_def)
next
  case False
  then have "get_trap_set s1 \<noteq> {} \<and> get_trap_set s2 \<noteq> {}" 
    using a1 by (simp add: low_equal_def get_trap_set_def)
  then show ?thesis using a1
  apply (simp add: execute_instr_sub1_def)
  apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
  by (simp add: return_def)
qed

theorem non_interference_step: 
assumes a1: "((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
good_context s1 \<and>
get_delayed_pool s1 = [] \<and> get_trap_set s1 = {} \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
get_delayed_pool s2 = [] \<and> get_trap_set s2 = {} \<and>
good_context s2 \<and>
low_equal s1 s2"
shows "\<exists>t1 t2. Some t1 = NEXT s1 \<and> Some t2 = NEXT s2 \<and> 
((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and>
low_equal t1 t2"
proof -
  from a1 have "good_context s1 \<and> good_context s2" by auto
  then have "NEXT s1 = Some (snd (fst (execute_instruction () s1))) \<and>
             NEXT s2 = Some (snd (fst (execute_instruction () s2)))"
       by (simp add: single_step)
  then have "\<exists>t1 t2. Some t1 = NEXT s1 \<and> Some t2 = NEXT s2" 
       by auto
  then have f0: "snd (execute_instruction() s1) = False \<and>
             snd (execute_instruction() s2) = False"
       by (auto simp add: NEXT_def case_prod_unfold)
  then have f1: "\<exists>t1 t2. Some t1 = NEXT s1 \<and>
      Some t2 = NEXT s2 \<and>
      ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
      ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0"
      using a1
      apply (auto simp add: NEXT_def case_prod_unfold)
       by (auto simp add: safe_privilege)
  then show ?thesis 
  proof (cases "exe_mode_val s1")
    case True
    then have f_exe0: "exe_mode_val s1" by auto
    then have f_exe: "exe_mode_val s1 \<and> exe_mode_val s2"
      proof -
        have "low_equal s1 s2" using a1 by auto
        then have "state_var s1 = state_var s2" by (simp add: low_equal_def)
        then have "exe_mode_val s1 = exe_mode_val s2" by (simp add: exe_mode_val_def)
        then show ?thesis using f_exe0 by auto
      qed
    then show ?thesis
    proof (cases "\<exists>e. fetch_instruction (delayed_pool_write s1) = Inl e")
      case True
      then have f_fetch_error: "\<exists>e. fetch_instruction (delayed_pool_write s1) = Inl e" by auto
      then have f_fetch_error2: "(\<exists>e. fetch_instruction (delayed_pool_write s1) = Inl e) \<and> 
                 (\<exists>e. fetch_instruction (delayed_pool_write s2) = Inl e)"
        proof -
          have "cpu_reg s1 = cpu_reg s2" 
            using a1 by (simp add: low_equal_def)
          then have "cpu_reg_val PC s1 = cpu_reg_val PC s2" 
            by (simp add: cpu_reg_val_def)
          then have "cpu_reg_val PC s1 = cpu_reg_val PC s2 \<and>
                     ((ucast (get_S (cpu_reg_val PSR (delayed_pool_write s1))))::word1) = 0 \<and>
                     ((ucast (get_S (cpu_reg_val PSR (delayed_pool_write s2))))::word1) = 0"
            using a1 
            by (auto simp add: empty_delayed_pool_write_privilege)  
          then show ?thesis using a1 f_fetch_error
          apply (simp add: fetch_instruction_def)
          apply (simp add: Let_def ucast_def)         
          apply clarsimp
          apply (case_tac "uint (3 AND cpu_reg_val PC (delayed_pool_write s1)) = 0")
           apply auto
           apply (case_tac "fst (memory_read 8 (cpu_reg_val PC (delayed_pool_write s1)) 
           (delayed_pool_write s1)) = None")
            apply auto
            apply (simp add: case_prod_unfold)
            using a1 apply (auto simp add: mem_read_delayed_write_low_equal)
           apply (simp add: case_prod_unfold)
           using a1 apply (auto simp add: mem_read_delayed_write_low_equal)
          apply (simp add: delayed_pool_write_def)
          by (simp add: Let_def get_delayed_write_def)
        qed
      then show ?thesis 
      proof (cases "exe_mode_val s1")
        case True
        then have "exe_mode_val s1 \<and> exe_mode_val s2" using exe_mode_low_equal a1 by auto
        then show ?thesis using f1
        apply (simp add: NEXT_def execute_instruction_def)
        apply (simp add: bind_def h1_def h2_def Let_def simpler_gets_def)
        using a1 apply clarsimp
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: simpler_modify_def)
        using f_fetch_error2 apply clarsimp
        apply (simp add: raise_trap_def simpler_modify_def return_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: return_def simpler_modify_def)
        apply (simp add: raise_trap_def simpler_modify_def return_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: return_def)
        apply (simp add: delayed_pool_write_def get_delayed_write_def Let_def)
        apply (simp add: low_equal_def)
        apply (simp add: add_trap_set_def)
        apply (simp add: cpu_reg_val_def)
        apply clarsimp
        by (simp add: mem_equal_mod_trap user_accessible_mod_trap)       
      next
        case False
        then have "\<not> (exe_mode_val s1) \<and> \<not> (exe_mode_val s2)" 
          using exe_mode_low_equal a1 by auto
        then show ?thesis using f1
        apply (simp add: NEXT_def execute_instruction_def)
        apply (simp add: bind_def h1_def h2_def Let_def simpler_gets_def)
        using a1 apply clarsimp
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        by (simp add: return_def)
      qed
    next
      case False
      then have f_fetch_suc: "(\<exists>v. fetch_instruction (delayed_pool_write s1) = Inr v)" 
        using fetch_instr_result_1 by auto
      then have "(\<exists>v. fetch_instruction (delayed_pool_write s1) = Inr v \<and>
                      fetch_instruction (delayed_pool_write s2) = Inr v)"
        proof -
          have "cpu_reg s1 = cpu_reg s2" 
            using a1 by (simp add: low_equal_def)
          then have "cpu_reg_val PC s1 = cpu_reg_val PC s2" 
            by (simp add: cpu_reg_val_def)
          then have "cpu_reg_val PC s1 = cpu_reg_val PC s2 \<and>
                     ((ucast (get_S (cpu_reg_val PSR (delayed_pool_write s1))))::word1) = 0 \<and>
                     ((ucast (get_S (cpu_reg_val PSR (delayed_pool_write s2))))::word1) = 0"
            using a1 
            by (auto simp add: empty_delayed_pool_write_privilege)  
          then show ?thesis using a1 f_fetch_suc
          apply (simp add: fetch_instruction_def)
          apply (simp add: Let_def ucast_def) 
          apply clarsimp
          apply (case_tac "uint (3 AND cpu_reg_val PC (delayed_pool_write s1)) = 0")
           apply auto
           apply (case_tac "fst (memory_read 8 (cpu_reg_val PC (delayed_pool_write s1)) 
           (delayed_pool_write s1)) = None")
            apply auto
            apply (simp add: case_prod_unfold)
           using a1 apply (auto simp add: mem_read_delayed_write_low_equal)
           apply (simp add: case_prod_unfold)
           using a1 apply (auto simp add: mem_read_delayed_write_low_equal)
          apply (simp add: delayed_pool_write_def)
          by (simp add: Let_def get_delayed_write_def)
        qed
      then have "(\<exists>v. fetch_instruction (delayed_pool_write s1) = Inr v \<and>
                      fetch_instruction (delayed_pool_write s2) = Inr v \<and>
                      \<not> (\<exists>e. (decode_instruction v) = Inl e))"
        using dispatch_fail f0 a1 f_exe by auto
      then have f_fetch_dec: "(\<exists>v. fetch_instruction (delayed_pool_write s1) = Inr v \<and>
                      fetch_instruction (delayed_pool_write s2) = Inr v \<and>
                      (\<exists>v1. (decode_instruction v) = Inr v1))"
        using decode_instr_result_4 by auto      
      then show ?thesis 
      proof (cases "annul_val (delayed_pool_write s1)")
        case True
        then have "annul_val (delayed_pool_write s1) \<and> annul_val (delayed_pool_write s2)"
          using a1 
          apply (simp add: low_equal_def)
          by (simp add: delayed_pool_write_def get_delayed_write_def annul_val_def)
        then show ?thesis using a1 f1 f_exe f_fetch_dec
        apply (simp add: NEXT_def execute_instruction_def)
        apply (simp add: exec_gets return_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: simpler_modify_def)
        apply clarsimp
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        apply (simp add: write_cpu_def cpu_reg_val_def set_annul_def)
        apply (simp add: simpler_modify_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: write_cpu_def cpu_reg_val_def set_annul_def)
        apply (simp add: simpler_modify_def)
        apply (simp add: cpu_reg_mod_def annul_mod_def)
        apply (simp add: delayed_pool_write_def get_delayed_write_def)
        apply (simp add: write_annul_def)
        apply clarsimp
        apply (simp add: low_equal_def)
        apply (simp add: user_accessible_annul mem_equal_annul)
        by (metis)        
      next
        case False
        then have "\<not> annul_val (delayed_pool_write s1) \<and>
          \<not> annul_val (delayed_pool_write s2)"
          using a1 apply (simp add: low_equal_def)
          apply (simp add: delayed_pool_write_def get_delayed_write_def)
          by (simp add: annul_val_def)
        then show ?thesis using a1 f1 f_exe f_fetch_dec
        apply (simp add: NEXT_def execute_instruction_def)
        apply (simp add: exec_gets return_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: simpler_modify_def)
        apply clarsimp
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        apply (case_tac "snd (execute_instr_sub1 (a, b)
                   (snd (fst (dispatch_instruction (a, b)
                               (delayed_pool_write s1))))) \<or>
             snd (dispatch_instruction (a, b) (delayed_pool_write s1))")
         apply auto
        apply (case_tac "snd (execute_instr_sub1 (a, b)
                   (snd (fst (dispatch_instruction (a, b)
                               (delayed_pool_write s2))))) \<or>
             snd (dispatch_instruction (a, b) (delayed_pool_write s2))")
         apply auto
        apply (simp add: simpler_modify_def)
        apply (simp add: simpler_gets_def bind_def h1_def h2_def Let_def)
        apply (simp add: case_prod_unfold)
        apply (simp add: delayed_pool_write_def get_delayed_write_def)
        by (meson dispath_instr_low_equal dispath_instr_privilege execute_instr_sub1_low_equal)        
      qed
    qed
  next
    case False
    then have f_non_exe: "exe_mode_val s1 = False" by auto
    then have "exe_mode_val s1 = False \<and> exe_mode_val s2 = False"        
      proof -
        have "low_equal s1 s2" using a1 by auto
        then have "state_var s1 = state_var s2" by (simp add: low_equal_def)
        then have "exe_mode_val s1 = exe_mode_val s2" by (simp add: exe_mode_val_def)
        then show ?thesis using f_non_exe by auto
      qed
    then show ?thesis using f1 a1    
    apply (simp add: NEXT_def execute_instruction_def)
    by (simp add: simpler_gets_def bind_def h1_def h2_def Let_def return_def)
  qed
qed

function (sequential) SEQ:: "nat \<Rightarrow> ('a::len0) sparc_state \<Rightarrow> ('a) sparc_state option"
where "SEQ 0 s = Some s"
|"SEQ n s = (
  case SEQ (n-1) s of None \<Rightarrow> None
  | Some t \<Rightarrow> NEXT t
)"
by pat_completeness auto
termination by lexicographic_order

lemma SEQ_suc: "SEQ n s = Some t \<Longrightarrow> SEQ (Suc n) s = NEXT t"
apply (induction n)
 apply clarsimp
by (simp add: option.case_eq_if)

definition user_seq_exe:: "nat \<Rightarrow> ('a::len0) sparc_state \<Rightarrow> bool" where
"user_seq_exe n s \<equiv> \<forall>i t. (i \<le> n \<and> SEQ i s = Some t) \<longrightarrow>
  (good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {})"

text \<open>NIA is short for non-interference assumption.\<close>
definition "NIA t1 t2 \<equiv> 
    ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and>
    good_context t1 \<and> get_delayed_pool t1 = [] \<and> get_trap_set t1 = {} \<and>
    good_context t2 \<and> get_delayed_pool t2 = [] \<and> get_trap_set t2 = {} \<and>
    low_equal t1 t2"

text \<open>NIC is short for non-interference conclusion.\<close>
definition "NIC t1 t2 \<equiv> (\<exists>u1 u2. Some u1 = NEXT t1 \<and> Some u2 = NEXT t2 \<and> 
    ((ucast (get_S (cpu_reg_val PSR u1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR u2)))::word1) = 0 \<and>
    low_equal u1 u2)"

lemma NIS_short: "\<forall>t1 t2. NIA t1 t2 \<longrightarrow> NIC t1 t2"
apply (simp add: NIA_def NIC_def)
using non_interference_step by auto

lemma non_interference_induct_case_sub1:
assumes a1: "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    NIA t1 t2))"
shows "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    NIA t1 t2 \<and>
    NIC t1 t2))"
using NIS_short
using assms by auto 

lemma non_interference_induct_case: 
assumes a1: 
"((\<forall>i t. i \<le> n \<and> SEQ i s1 = Some t \<longrightarrow>
                 good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {}) \<and>
          (\<forall>i t. i \<le> n \<and> SEQ i s2 = Some t \<longrightarrow>
                 good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {}) \<longrightarrow>
          (\<exists>t1. Some t1 = SEQ n s1 \<and>
               (\<exists>t2. Some t2 = SEQ n s2 \<and>
                     ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and> low_equal t1 t2))) \<and>
(\<forall>i t. i \<le> Suc n \<and> SEQ i s1 = Some t \<longrightarrow>
               good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {}) \<and>
         (\<forall>i t. i \<le> Suc n \<and> SEQ i s2 = Some t \<longrightarrow>
               good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {})"
shows "\<exists>t1. Some t1 = (case SEQ n s1 of None \<Rightarrow> None | Some x \<Rightarrow> NEXT x) \<and>
              (\<exists>t2. Some t2 = (case SEQ n s2 of None \<Rightarrow> None | Some x \<Rightarrow> NEXT x) \<and>
                    ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and> low_equal t1 t2)"
proof -
  from a1 have f1: "((\<forall>i t. i \<le> n \<and> SEQ i s1 = Some t \<longrightarrow>
  good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {}) \<and>
  (\<forall>i t. i \<le> n \<and> SEQ i s2 = Some t \<longrightarrow>
  good_context t \<and> get_delayed_pool t = [] \<and> get_trap_set t = {}))"
  by (metis le_SucI)
  then have f2: "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and>
    low_equal t1 t2))"
  using a1 by auto
  then have f3: "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    NIA t1 t2))"
  using f1 NIA_def by (metis (full_types) dual_order.refl)  
  then have "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    NIA t1 t2 \<and>
    NIC t1 t2))"
  using non_interference_induct_case_sub1 by blast
  then have "(\<exists>t1. Some t1 = SEQ n s1 \<and>
    (\<exists>t2. Some t2 = SEQ n s2 \<and>
    (((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and>
    good_context t1 \<and> get_delayed_pool t1 = [] \<and> get_trap_set t1 = {} \<and>
    good_context t2 \<and> get_delayed_pool t2 = [] \<and> get_trap_set t2 = {} \<and>
    low_equal t1 t2) \<and>
    (\<exists>u1 u2. Some u1 = NEXT t1 \<and> Some u2 = NEXT t2 \<and> 
    ((ucast (get_S (cpu_reg_val PSR u1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR u2)))::word1) = 0 \<and>
    low_equal u1 u2)))"
  using NIA_def NIC_def by fastforce
  then show ?thesis
  by (metis option.simps(5))
qed

lemma non_interference_induct_case_sub2: 
assumes a1: 
"(user_seq_exe n s1 \<and>
          user_seq_exe n s2 \<longrightarrow>
          (\<exists>t1. Some t1 = SEQ n s1 \<and>
               (\<exists>t2. Some t2 = SEQ n s2 \<and>
                     ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and> low_equal t1 t2))) \<and>
user_seq_exe (Suc n) s1 \<and>
         user_seq_exe (Suc n) s2"
shows "\<exists>t1. Some t1 = (case SEQ n s1 of None \<Rightarrow> None | Some x \<Rightarrow> NEXT x) \<and>
              (\<exists>t2. Some t2 = (case SEQ n s2 of None \<Rightarrow> None | Some x \<Rightarrow> NEXT x) \<and>
                    ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
    ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and> low_equal t1 t2)"
using a1
by (simp add: non_interference_induct_case user_seq_exe_def)

theorem non_interference:
assumes a1: 
"((ucast (get_S (cpu_reg_val PSR s1)))::word1) = 0 \<and>
good_context s1 \<and>
get_delayed_pool s1 = [] \<and> get_trap_set s1 = {} \<and>
((ucast (get_S (cpu_reg_val PSR s2)))::word1) = 0 \<and>
get_delayed_pool s2 = [] \<and> get_trap_set s2 = {} \<and>
good_context s2 \<and>
user_seq_exe n s1 \<and> user_seq_exe n s2 \<and>
low_equal s1 s2"
shows "(\<exists>t1 t2. Some t1 = SEQ n s1 \<and> Some t2 = SEQ n s2 \<and>
  ((ucast (get_S (cpu_reg_val PSR t1)))::word1) = 0 \<and>
  ((ucast (get_S (cpu_reg_val PSR t2)))::word1) = 0 \<and>
  low_equal t1 t2)"
using a1
apply (induction n)
 apply (simp add: user_seq_exe_def)
apply clarsimp
by (simp add: non_interference_induct_case_sub2)

end
