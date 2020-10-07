(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
 *)

theory Sparc_Execution
imports Main Sparc_Instruction Sparc_State Sparc_Types 
"HOL-Eisbach.Eisbach_Tools"
begin

primrec sum :: "nat \<Rightarrow> nat" where
"sum 0 = 0" |
"sum (Suc n) = Suc n + sum n"

definition select_trap :: "unit \<Rightarrow> ('a,unit) sparc_state_monad"
where "select_trap _ \<equiv>
  do
    traps \<leftarrow> gets (\<lambda>s. (get_trap_set s));
    rt_val \<leftarrow> gets (\<lambda>s. (reset_trap_val s));
    psr_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val PSR s));
    et_val \<leftarrow> gets (\<lambda>s. (get_ET psr_val));
    modify (\<lambda>s. (emp_trap_set s));
    if rt_val = True then \<comment> \<open>ignore \<open>ET\<close>, and leave \<open>tt\<close> unchaged\<close>
      return ()
    else if et_val = 0 then \<comment> \<open>go to error mode, machine needs reset\<close>
      do
        set_err_mode True;
        set_exe_mode False;
        fail ()
      od
    \<comment> \<open>By the SPARCv8 manual only 1 of the following traps could be in traps.\<close>
    else if data_store_error \<in> traps  then
      do
        write_cpu_tt (0b00101011::word8);
        return ()
      od
    else if instruction_access_error \<in> traps then
      do
        write_cpu_tt (0b00100001::word8);
        return ()
      od
    else if r_register_access_error \<in> traps then
      do
        write_cpu_tt (0b00100000::word8);
        return ()
      od
    else if instruction_access_exception \<in> traps then
      do
        write_cpu_tt (0b00000001::word8);
        return ()
      od
    else if privileged_instruction \<in> traps then  
      do
        write_cpu_tt (0b00000011::word8);
        return ()
      od
    else if illegal_instruction \<in> traps then
      do
        write_cpu_tt (0b00000010::word8);
        return ()
      od
    else if fp_disabled \<in> traps then
      do
        write_cpu_tt (0b00000100::word8);
        return ()
      od
    else if cp_disabled \<in> traps then
      do
        write_cpu_tt (0b00100100::word8);
        return ()
      od
    else if unimplemented_FLUSH \<in> traps then
      do
        write_cpu_tt (0b00100101::word8);
        return ()
      od
    else if window_overflow \<in> traps then
      do
        write_cpu_tt (0b00000101::word8);
        return ()
      od
    else if window_underflow \<in> traps then
      do
        write_cpu_tt (0b00000110::word8);
        return ()
      od  
    else if mem_address_not_aligned \<in> traps then
      do
        write_cpu_tt (0b00000111::word8);
        return ()
      od
    else if fp_exception \<in> traps then
      do  
        write_cpu_tt (0b00001000::word8);
        return ()
      od
    else if cp_exception \<in> traps then
      do
        write_cpu_tt (0b00101000::word8);
        return ()
      od
    else if data_access_error \<in> traps then
      do
        write_cpu_tt (0b00101001::word8);
        return ()
      od
    else if data_access_exception \<in> traps then
      do
        write_cpu_tt (0b00001001::word8);
        return ()
      od  
    else if tag_overflow \<in> traps then
      do
        write_cpu_tt (0b00001010::word8);
        return ()
      od
    else if division_by_zero \<in> traps then
      do
        write_cpu_tt (0b00101010::word8);
        return ()
      od
    else if trap_instruction \<in> traps then
      do 
        ticc_trap_type \<leftarrow> gets (\<lambda>s. (ticc_trap_type_val s));
        write_cpu_tt (word_cat (1::word1) ticc_trap_type);
        return ()
      od
    \<^cancel>\<open>else if interrupt_level > 0 then\<close>
    \<comment> \<open>We don't consider \<open>interrupt_level\<close>\<close>
    else return ()
  od"

definition exe_trap_st_pc :: "unit \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "exe_trap_st_pc _ \<equiv>
  do
    annul \<leftarrow> gets (\<lambda>s. (annul_val s));
    pc_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val PC s));
    npc_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val nPC s));
    curr_win \<leftarrow> get_curr_win();
    if annul = False then
      do
        write_reg pc_val curr_win (word_of_int 17);
        write_reg npc_val curr_win (word_of_int 18);
        return ()
      od
    else \<comment> \<open>\<open>annul = True\<close>\<close>
      do
        write_reg npc_val curr_win (word_of_int 17);
        write_reg (npc_val + 4) curr_win (word_of_int 18);
        set_annul False;
        return ()
      od
  od"

definition exe_trap_wr_pc :: "unit \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "exe_trap_wr_pc _ \<equiv>
  do
    psr_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val PSR s));
    new_psr_val \<leftarrow> gets (\<lambda>s. (update_S (1::word1) psr_val));
    write_cpu new_psr_val PSR;
    reset_trap \<leftarrow> gets (\<lambda>s. (reset_trap_val s));
    tbr_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val TBR s));
    if reset_trap = False then
      do
        write_cpu tbr_val PC;
        write_cpu (tbr_val + 4) nPC;
        return ()
      od
    else \<comment> \<open>\<open>reset_trap = True\<close>\<close>
      do
        write_cpu 0 PC;
        write_cpu 4 nPC;
        set_reset_trap False;
        return ()
      od
  od"
  
definition execute_trap :: "unit \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "execute_trap _ \<equiv>
  do
    select_trap();
    err_mode \<leftarrow> gets (\<lambda>s. (err_mode_val s));
    if err_mode = True then 
      \<comment> \<open>The SparcV8 manual doesn't say what to do.\<close>
      return ()
    else
      do
        psr_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val PSR s));
        s_val \<leftarrow> gets (\<lambda>s. ((ucast (get_S psr_val))::word1));
        curr_win \<leftarrow> get_curr_win();
        new_cwp \<leftarrow> gets (\<lambda>s. ((word_of_int (((uint curr_win) - 1) mod NWINDOWS)))::word5);
        new_psr_val \<leftarrow> gets (\<lambda>s. (update_PSR_exe_trap new_cwp (0::word1) s_val psr_val));
        write_cpu new_psr_val PSR;          
        exe_trap_st_pc();         
        exe_trap_wr_pc();
        return ()
      od  
  od"

definition dispatch_instruction :: "instruction \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "dispatch_instruction instr \<equiv> 
  let instr_name = fst instr in
  do
    traps \<leftarrow> gets (\<lambda>s. (get_trap_set s));
    if traps = {} then 
      if instr_name \<in> {load_store_type LDSB,load_store_type LDUB,
        load_store_type LDUBA,load_store_type LDUH,load_store_type LD,
        load_store_type LDA,load_store_type LDD} then
        load_instr instr
      else if instr_name \<in> {load_store_type STB,load_store_type STH,
        load_store_type ST,load_store_type STA,load_store_type STD} then
        store_instr instr
      else if instr_name \<in> {sethi_type SETHI} then
        sethi_instr instr
      else if instr_name \<in> {nop_type NOP} then
        nop_instr instr
      else if instr_name \<in> {logic_type ANDs,logic_type ANDcc,logic_type ANDN,
        logic_type ANDNcc,logic_type ORs,logic_type ORcc,logic_type ORN,
        logic_type XORs,logic_type XNOR} then
        logical_instr instr
      else if instr_name \<in> {shift_type SLL,shift_type SRL,shift_type SRA} then
        shift_instr instr
      else if instr_name \<in> {arith_type ADD,arith_type ADDcc,arith_type ADDX} then
        add_instr instr
      else if instr_name \<in> {arith_type SUB,arith_type SUBcc,arith_type SUBX} then
        sub_instr instr
      else if instr_name \<in> {arith_type UMUL,arith_type SMUL,arith_type SMULcc} then
        mul_instr instr
      else if instr_name \<in> {arith_type UDIV,arith_type UDIVcc,arith_type SDIV} then
        div_instr instr
      else if instr_name \<in> {ctrl_type SAVE,ctrl_type RESTORE} then
        save_restore_instr instr
      else if instr_name \<in> {call_type CALL} then
        call_instr instr
      else if instr_name \<in> {ctrl_type JMPL} then
        jmpl_instr instr
      else if instr_name \<in> {ctrl_type RETT} then
        rett_instr instr
      else if instr_name \<in> {sreg_type RDY,sreg_type RDPSR,sreg_type RDWIM,
        sreg_type RDTBR} then
        read_state_reg_instr instr
      else if instr_name \<in> {sreg_type WRY,sreg_type WRPSR,sreg_type WRWIM,
        sreg_type WRTBR} then 
        write_state_reg_instr instr
      else if instr_name \<in> {load_store_type FLUSH} then
        flush_instr instr
      else if instr_name \<in> {bicc_type BE,bicc_type BNE,bicc_type BGU,
        bicc_type BLE,bicc_type BL,bicc_type BGE,bicc_type BNEG,bicc_type BG,
        bicc_type BCS,bicc_type BLEU,bicc_type BCC,bicc_type BA,bicc_type BN} then
        branch_instr instr
      else fail ()
    else return ()
  od"

definition supported_instruction :: "sparc_operation \<Rightarrow> bool"
where "supported_instruction instr \<equiv>
  if instr \<in> {load_store_type LDSB,load_store_type LDUB,load_store_type LDUBA,
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
              bicc_type BN} 
    then True
  else False
"

definition execute_instr_sub1 :: "instruction \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "execute_instr_sub1 instr \<equiv>
  do
    instr_name \<leftarrow> gets (\<lambda>s. (fst instr));
    traps2 \<leftarrow> gets (\<lambda>s. (get_trap_set s));
    if traps2 = {} \<and> instr_name \<notin> {call_type CALL,ctrl_type RETT,ctrl_type JMPL,
                                   bicc_type BE,bicc_type BNE,bicc_type BGU,
                                   bicc_type BLE,bicc_type BL,bicc_type BGE,
                                   bicc_type BNEG,bicc_type BG,
                                   bicc_type BCS,bicc_type BLEU,bicc_type BCC,
                                   bicc_type BA,bicc_type BN} then
    do
      npc_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val nPC s));
      write_cpu npc_val PC;
      write_cpu (npc_val + 4) nPC;
      return ()
    od
    else return ()
  od"

definition execute_instruction :: "unit \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "execute_instruction _ \<equiv> 
  do
    traps \<leftarrow> gets (\<lambda>s. (get_trap_set s));
    if traps = {} then 
    do
      exe_mode \<leftarrow> gets (\<lambda>s. (exe_mode_val s));
      if exe_mode = True then
      do
        modify (\<lambda>s. (delayed_pool_write s));
        fetch_result \<leftarrow> gets (\<lambda>s. (fetch_instruction s));
        case fetch_result of 
        Inl e1 \<Rightarrow> (do \<comment> \<open>Memory address in PC is not aligned.\<close>
                      \<comment> \<open>Actually, SparcV8 manual doens't check alignment here.\<close>
                    raise_trap instruction_access_exception;
                    return ()
                  od) 
        | Inr v1 \<Rightarrow> (do
          dec \<leftarrow> gets (\<lambda>s. (decode_instruction v1));
          case dec of 
            Inl e2 \<Rightarrow> (\<comment> \<open>Instruction is ill-formatted.\<close>
                        fail ()
                      )
            | Inr v2 \<Rightarrow> (do
              instr \<leftarrow> gets (\<lambda>s. (v2));
              annul \<leftarrow> gets (\<lambda>s. (annul_val s));
              if annul = False then 
              do
                dispatch_instruction instr;
                execute_instr_sub1 instr;
                return ()
              od
              else \<comment> \<open>\<open>annul \<noteq> False\<close>\<close>
              do
                set_annul False;
                npc_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val nPC s));
                write_cpu npc_val PC;
                write_cpu (npc_val + 4) nPC;
                return ()
              od
            od)
        od) 
      od
      else return () \<comment> \<open>Not in \<open>execute_mode\<close>.\<close>
    od
    else \<comment> \<open>traps is not empty, which means \<open>trap = 1\<close>.\<close>
    do
      execute_trap();
      return ()
    od
  od"

definition NEXT :: "('a::len0)sparc_state \<Rightarrow> ('a)sparc_state option"
where "NEXT s \<equiv> case execute_instruction () s of (_,True) \<Rightarrow> None
| (s',False) \<Rightarrow> Some (snd s')"

definition good_context :: "('a::len0) sparc_state \<Rightarrow> bool"
where "good_context s \<equiv> 
  let traps = get_trap_set s;
      psr_val = cpu_reg_val PSR s;
      et_val = get_ET psr_val;
      rt_val = reset_trap_val s
  in
  if traps \<noteq> {} \<and> rt_val = False \<and> et_val = 0 then False \<comment> \<open>enter \<open>error_mode\<close> in \<open>select_traps\<close>.\<close>
  else
    let s' = delayed_pool_write s in
    case fetch_instruction s' of
    \<comment> \<open>\<open>instruction_access_exception\<close> is handled in the next state.\<close>
    Inl _ \<Rightarrow> True 
    |Inr v \<Rightarrow> (
      case decode_instruction v of 
      Inl _ \<Rightarrow> False 
      |Inr instr \<Rightarrow> (
        let annul = annul_val s' in
        if annul = True then True
        else \<comment> \<open>\<open>annul = False\<close>\<close>
          if supported_instruction (fst instr) then
            \<comment> \<open>The only instruction that could fail is \<open>RETT\<close>.\<close>
            if (fst instr) = ctrl_type RETT then
              let curr_win_r = (get_CWP (cpu_reg_val PSR s'));
                  new_cwp_int_r = (((uint curr_win_r) + 1) mod NWINDOWS);
                  wim_val_r = cpu_reg_val WIM s';
                  psr_val_r = cpu_reg_val PSR s';
                  et_val_r = get_ET psr_val_r;
                  s_val_r = (ucast (get_S psr_val_r))::word1;
                  op_list_r = snd instr;
                  addr_r = get_addr (snd instr) s'
              in
              if et_val_r = 1 then True
              else if s_val_r = 0 then False
              else if (get_WIM_bit (nat new_cwp_int_r) wim_val_r) \<noteq> 0 then False
              else if (bitAND addr_r (0b00000000000000000000000000000011::word32)) \<noteq> 0 then False
              else True
            else True
          else False \<comment> \<open>Unsupported instruction.\<close>
      )  
    )
"

function (sequential) seq_exec:: "nat \<Rightarrow> ('a::len0,unit) sparc_state_monad"
where "seq_exec 0 = return ()"
 |
"seq_exec n =  (do execute_instruction();
                  (seq_exec (n-1))
               od)
"
by pat_completeness auto
termination by lexicographic_order

type_synonym leon3_state = "(word_length5) sparc_state"

type_synonym ('e) leon3_state_monad = "(leon3_state, 'e) det_monad"

definition execute_leon3_instruction:: "unit \<Rightarrow> (unit) leon3_state_monad"
where "execute_leon3_instruction \<equiv> execute_instruction"

definition seq_exec_leon3:: "nat \<Rightarrow> (unit) leon3_state_monad"
where "seq_exec_leon3 \<equiv> seq_exec"

end
