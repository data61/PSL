(*  Title:     Memory.thy
    Author:    David Sanán, Trinity College Dublin, 2012
               Zhe Hou, NTU, 2016.
*)


section \<open>Memory Management Unit (MMU)\<close>

theory MMU
imports Main RegistersOps Sparc_Types
begin

section \<open>MMU  Sizing\<close> 

text\<open>
  We need some citation here for documentation about the MMU.
\<close>
text\<open>The MMU uses the Address Space Identifiers (ASI) to control memory access.
ASI = 8, 10 are for user; ASI = 9, 11 are for supervisor.\<close>

subsection "MMU Types"

type_synonym word_PTE_flags = word8
type_synonym word_length_PTE_flags = word_length8

subsection "MMU length values"

text\<open>Definitions for the length of the virtua address, page size,  
virtual translation tables indexes, virtual address offset and Page protection flags\<close>


definition length_entry_type :: "nat" 
where "length_entry_type \<equiv> LENGTH(word_length_entry_type)" 
definition length_phys_address:: "nat" 
where "length_phys_address \<equiv> LENGTH(word_length_phys_address)"
definition length_virtua_address:: "nat" 
where "length_virtua_address \<equiv> LENGTH(word_length_virtua_address)"
definition length_page:: "nat" where "length_page \<equiv> LENGTH(word_length_page)"
definition length_t1:: "nat" where "length_t1 \<equiv> LENGTH(word_length_t1)"
definition length_t2:: "nat" where "length_t2 \<equiv> LENGTH(word_length_t2)"
definition length_t3:: "nat" where "length_t3 \<equiv> LENGTH(word_length_t3)"
definition length_offset:: "nat" where "length_offset \<equiv> LENGTH(word_length_offset)"
definition length_PTE_flags :: "nat" where 
"length_PTE_flags \<equiv> LENGTH(word_length_PTE_flags)"

subsection "MMU index values"

definition va_t1_index :: "nat" where "va_t1_index \<equiv> length_virtua_address - length_t1"
definition va_t2_index :: "nat" where "va_t2_index \<equiv> va_t1_index - length_t2"
definition va_t3_index :: "nat" where "va_t3_index \<equiv> va_t2_index - length_t3"
definition va_offset_index :: "nat" where "va_offset_index \<equiv> va_t3_index - length_offset"
definition pa_page_index :: "nat" 
where "pa_page_index \<equiv> length_phys_address - length_page"
definition pa_offset_index :: "nat" where 
"pa_offset_index \<equiv> pa_page_index -length_page"

section \<open>MMU Definition\<close>

record MMU_state =
   registers :: "MMU_context"
(*   contexts:: context_table*)

text \<open>The following functions access MMU registers via addresses. 
  See UT699LEON3FT manual page 35.\<close>

definition mmu_reg_val:: "MMU_state \<Rightarrow> virtua_address \<Rightarrow> machine_word option"
where "mmu_reg_val mmu_state addr \<equiv>
  if addr = 0x000 then \<comment> \<open>MMU control register\<close>
    Some ((registers mmu_state) CR)
  else if addr = 0x100 then \<comment> \<open>Context pointer register\<close>
    Some ((registers mmu_state) CTP)
  else if addr = 0x200 then \<comment> \<open>Context register\<close>
    Some ((registers mmu_state) CNR)
  else if addr = 0x300 then \<comment> \<open>Fault status register\<close>
    Some ((registers mmu_state) FTSR)
  else if addr = 0x400 then \<comment> \<open>Fault address register\<close>
    Some ((registers mmu_state) FAR)
  else None"

definition mmu_reg_mod:: "MMU_state \<Rightarrow> virtua_address \<Rightarrow> machine_word \<Rightarrow>
  MMU_state option" where
"mmu_reg_mod mmu_state addr w \<equiv>
  if addr = 0x000 then \<comment> \<open>MMU control register\<close>
    Some (mmu_state\<lparr>registers := (registers mmu_state)(CR := w)\<rparr>)
  else if addr = 0x100 then \<comment> \<open>Context pointer register\<close>
    Some (mmu_state\<lparr>registers := (registers mmu_state)(CTP := w)\<rparr>)
  else if addr = 0x200 then \<comment> \<open>Context register\<close>
    Some (mmu_state\<lparr>registers := (registers mmu_state)(CNR := w)\<rparr>)
  else if addr = 0x300 then \<comment> \<open>Fault status register\<close>
    Some (mmu_state\<lparr>registers := (registers mmu_state)(FTSR := w)\<rparr>)
  else if addr = 0x400 then \<comment> \<open>Fault address register\<close>
    Some (mmu_state\<lparr>registers := (registers mmu_state)(FAR := w)\<rparr>)
  else None"

section \<open>Virtual Memory\<close>

subsection \<open>MMU Auxiliary Definitions\<close>

definition getCTPVal:: "MMU_state \<Rightarrow> machine_word"
where "getCTPVal mmu \<equiv>  (registers mmu) CTP"

definition getCNRVal::"MMU_state \<Rightarrow> machine_word"
where "getCNRVal mmu \<equiv>  (registers mmu) CNR"


text\<open>
 The physical context table address is got from the ConText Pointer register (CTP) and the 
Context Register (CNR) MMU registers. 
 The CTP is shifted to align it with 
the physical address (36 bits) and we add the table index given on CNR.
CTP is right shifted 2 bits, cast to phys address and left shifted 6 bytes 
to be aligned with the context register.  
CNR is 2 bits left shifted for alignment with the context table.
\<close>

definition compose_context_table_addr :: "machine_word \<Rightarrow>machine_word 
                                          \<Rightarrow> phys_address"
where 
 "compose_context_table_addr ctp cnr 
    \<equiv> ((ucast (ctp >> 2)) << 6) + (ucast cnr << 2)"

subsection \<open>Virtual Address Translation\<close>

text\<open>Get the context table phys address from the MMU registers\<close>
definition get_context_table_addr :: "MMU_state \<Rightarrow> phys_address"
where 
 "get_context_table_addr mmu 
     \<equiv> compose_context_table_addr (getCTPVal mmu) (getCNRVal mmu)"

definition va_list_index :: "nat list" where
"va_list_index \<equiv> [va_t1_index,va_t2_index,va_t3_index,0]"

definition offset_index :: "nat list" where
"offset_index 
  \<equiv> [ length_machine_word
    , length_machine_word-length_t1
    , length_machine_word-length_t1-length_t2
    , length_machine_word-length_t1-length_t2-length_t3
    ]"

definition index_len_table :: "nat list" where "index_len_table \<equiv> [8,6,6,0]"

definition n_context_tables :: "nat" where "n_context_tables \<equiv> 3"

text \<open>The following are basic physical memory read functions. 
At this level we don't need the write memory yet.\<close>

definition mem_context_val:: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                      mem_context \<Rightarrow> mem_val_type option"
where
"mem_context_val asi add m \<equiv> 
  let asi8 = word_of_int 8;
      r1 = m asi add 
  in
  if r1 = None then
    m asi8 add
  else r1
"

text \<open>Given an ASI (word8), an address (word32) addr, 
        read the 32bit value from the memory addresses 
        starting from address addr' where addr' = addr 
        exception that the last two bits are 0's. 
        That is, read the data from 
        addr', addr'+1, addr'+2, addr'+3.\<close>
definition mem_context_val_w32 :: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                           mem_context \<Rightarrow> word32 option"
where
"mem_context_val_w32 asi addr m \<equiv>
  let addr' = bitAND addr 0b111111111111111111111111111111111100;
      addr0 = bitOR addr' 0b000000000000000000000000000000000000;
      addr1 = bitOR addr' 0b000000000000000000000000000000000001;
      addr2 = bitOR addr' 0b000000000000000000000000000000000010;
      addr3 = bitOR addr' 0b000000000000000000000000000000000011;
      r0 = mem_context_val asi addr0 m;
      r1 = mem_context_val asi addr1 m;
      r2 = mem_context_val asi addr2 m;
      r3 = mem_context_val asi addr3 m
  in
  if r0 = None \<or> r1 = None \<or> r2 = None \<or> r3 = None then
    None
  else
    let byte0 = case r0 of Some v \<Rightarrow> v;
        byte1 = case r1 of Some v \<Rightarrow> v;
        byte2 = case r2 of Some v \<Rightarrow> v;
        byte3 = case r3 of Some v \<Rightarrow> v 
    in
    Some (bitOR (bitOR (bitOR ((ucast(byte0)) << 24) 
                              ((ucast(byte1)) << 16)) 
                       ((ucast(byte2)) << 8)) 
                (ucast(byte3)))
"

text \<open>
  @{term "get_addr_from_table"} browses the page description tables  
  until it finds a PTE (bits==suc (suc 0).

  If it is a PTE it aligns the 24 most significant bits of the entry
  with the most significant bits of the phys address and or-ed with the offset,
   which will vary depending on the entry level. 
 In the case we are looking at the last table level (level 3),
   the offset is aligned to 0 otherwise it will be 2.
  
 If the table entry is a PTD (bits== Suc 0),
  the index is obtained from the virtual address depending on the current level and or-ed with the PTD. 
\<close>

function ptd_lookup:: "virtua_address \<Rightarrow> virtua_address \<Rightarrow>
mem_context \<Rightarrow> nat \<Rightarrow> (phys_address \<times> PTE_flags) option" 
where "ptd_lookup va pt m lvl = (
  if lvl > 3 then None
  else 
    let thislvl_offset = (
      if lvl = 1 then (ucast ((ucast (va >> 24))::word8))::word32
      else if lvl = 2 then (ucast ((ucast (va >> 18))::word6))::word32
      else (ucast ((ucast (va >> 12))::word6))::word32);
        thislvl_addr = bitOR pt thislvl_offset;
        thislvl_data = mem_context_val_w32 (word_of_int 9) (ucast thislvl_addr) m
    in
    case thislvl_data of 
    Some v \<Rightarrow> (
      let et_val = bitAND v 0b00000000000000000000000000000011 in
      if et_val = 0 then \<comment> \<open>Invalid\<close>
        None
      else if et_val = 1 then \<comment> \<open>Page Table Descriptor\<close>
        let ptp = bitAND v 0b11111111111111111111111111111100 in
        ptd_lookup va ptp m (lvl+1)
      else if et_val = 2 then \<comment> \<open>Page Table Entry\<close>
        let ppn = (ucast (v >> 8))::word24;
            va_offset = (ucast ((ucast va)::word12))::word36
        in
        Some ((bitOR (((ucast ppn)::word36) << 12) va_offset), 
              ((ucast v)::word8))
      else \<comment> \<open>\<open>et_val = 3\<close>, reserved.\<close>
        None
    )
    |None \<Rightarrow> None)
"
by pat_completeness auto
termination  
by (relation "measure (\<lambda> (va, (pt, (m, lvl))). 4 - lvl)") auto

definition get_acc_flag:: "PTE_flags \<Rightarrow> word3" where
"get_acc_flag w8 \<equiv> (ucast (w8 >> 2))::word3"

definition mmu_readable:: "word3 \<Rightarrow> asi_type \<Rightarrow> bool" where
"mmu_readable f asi \<equiv>
  if uint asi \<in> {8, 10} then
    if uint f \<in> {0,1,2,3,5} then True
    else False
  else if uint asi \<in> {9, 11} then
    if uint f \<in> {0,1,2,3,5,6,7} then True
    else False
  else False
"

definition mmu_writable:: "word3 \<Rightarrow> asi_type \<Rightarrow> bool" where
"mmu_writable f asi \<equiv>
  if uint asi \<in> {8, 10} then
    if uint f \<in> {1,3} then True
    else False
  else if uint asi \<in> {9, 11} then
    if uint f \<in> {1,3,5,7} then True
    else False
  else False
"

definition virt_to_phys :: "virtua_address \<Rightarrow> MMU_state  \<Rightarrow> mem_context \<Rightarrow> 
                            (phys_address \<times> PTE_flags) option"
where 
 "virt_to_phys va mmu m \<equiv> 
    let ctp_val = mmu_reg_val mmu (0x100);
        cnr_val = mmu_reg_val mmu (0x200);
        mmu_cr_val = (registers mmu) CR
    in
    if bitAND mmu_cr_val 1 \<noteq> 0 then \<comment> \<open>MMU enabled.\<close>
      case (ctp_val,cnr_val) of
      (Some v1, Some v2) \<Rightarrow>
        let context_table_entry = bitOR ((v1 >> 11) << 11)
            ((bitAND v2 0b00000000000000000000000111111111) << 2);
            context_table_data = mem_context_val_w32 (word_of_int 9) 
              (ucast context_table_entry) m
        in (
        case context_table_data of
        Some lvl1_page_table \<Rightarrow>
          ptd_lookup va lvl1_page_table m 1
        |None \<Rightarrow> None)
      |_ \<Rightarrow> None
    else Some ((ucast va), ((0b11101111)::word8)) 
"

text \<open>
\newpage

The below function gives the initial values of MMU registers.
In particular, the MMU context register CR is 0 because:
We don't know the bits for IMPL, VER, and SC;
the bits for PSO are 0s because we use TSO;
the reserved bits are 0s;
we assume NF bits are 0s;
and most importantly, the E bit is 0 because when the machine 
starts up, MMU is disabled. 
An initial boot procedure (bootloader or something like that) should 
configure the MMU and then enable it if the OS uses MMU.\<close>

definition MMU_registers_init :: "MMU_context"
where "MMU_registers_init r \<equiv> 0" 

definition mmu_setup :: "MMU_state"
where "mmu_setup \<equiv> \<lparr>registers=MMU_registers_init\<rparr>"

end
