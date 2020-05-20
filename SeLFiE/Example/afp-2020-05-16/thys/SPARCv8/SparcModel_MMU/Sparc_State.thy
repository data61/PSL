(*
 * Copyright 2016, NTU
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * Author: Zhe Hou, David Sanan.
 *)

section \<open>SPARC V8 state model\<close>
theory Sparc_State
imports Main Sparc_Types  "../lib/wp/DetMonadLemmas" MMU
begin                                                                    
section \<open>state as a function\<close>

record cpu_cache = 
dcache:: cache_context
icache:: cache_context

text\<open>
The state @{term sparc_state} is defined as a tuple @{term cpu_context}, 
@{term user_context}, @{term mem_context}, defining the state of the CPU registers, 
user registers, memory, cache, and delayed write pool respectively. 
Additionally, a boolean indicates whether the state is 
undefined or not.
\<close>

record (overloaded) ('a) sparc_state =
cpu_reg:: cpu_context
user_reg:: "('a) user_context"
sys_reg:: sys_context
mem:: mem_context
mmu:: MMU_state
cache:: cpu_cache
dwrite:: delayed_write_pool
state_var:: sparc_state_var
traps:: "Trap set"
undef:: bool

section\<open>functions for state member access\<close>

definition cpu_reg_val:: "CPU_register \<Rightarrow> ('a) sparc_state \<Rightarrow> reg_type"
where
"cpu_reg_val reg state \<equiv> (cpu_reg state) reg"

definition cpu_reg_mod :: "word32 \<Rightarrow> CPU_register \<Rightarrow> ('a) sparc_state \<Rightarrow> 
                           ('a) sparc_state"
where "cpu_reg_mod data_w32 cpu state \<equiv> 
  state\<lparr>cpu_reg := ((cpu_reg state)(cpu := data_w32))\<rparr>"

text \<open>r[0] = 0. Otherwise read the actual value.\<close>
definition user_reg_val:: "('a) window_size \<Rightarrow> user_reg_type \<Rightarrow> ('a) sparc_state \<Rightarrow> reg_type"
where
"user_reg_val window ur state \<equiv> 
  if ur = 0 then 0
  else (user_reg state) window ur"

text \<open>Write a global register. win should be initialised as NWINDOWS.\<close>
fun (sequential) global_reg_mod :: "word32 \<Rightarrow> nat \<Rightarrow> user_reg_type \<Rightarrow> 
  ('a::len0) sparc_state \<Rightarrow> ('a) sparc_state"
where
"global_reg_mod data_w32 0 ur state = state"
|
"global_reg_mod data_w32 win ur state = (
    let win_word = word_of_int (int (win-1));
        ns = state\<lparr>user_reg := 
          (user_reg state)(win_word := ((user_reg state) win_word)(ur := data_w32))\<rparr> 
    in
    global_reg_mod data_w32 (win-1) ur ns
)"

text \<open>Compute the next window.\<close>
definition next_window :: "('a::len0) window_size \<Rightarrow> ('a) window_size"
where
"next_window win \<equiv>
  if (uint win) < (NWINDOWS - 1) then (win + 1)
  else 0
"

text \<open>Compute the previous window.\<close>
definition pre_window :: "('a::len0) window_size \<Rightarrow> ('a::len0) window_size"
where
"pre_window win \<equiv>
  if (uint win) > 0 then (win - 1)
  else (word_of_int (NWINDOWS - 1))
"

text \<open>write an output register. 
  Also write ur+16 of the previous window.\<close>
definition out_reg_mod :: "word32 \<Rightarrow> ('a::len0) window_size \<Rightarrow> user_reg_type \<Rightarrow> 
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"out_reg_mod data_w32 win ur state \<equiv>
  let state' = state\<lparr>user_reg :=
        (user_reg state)(win := ((user_reg state) win)(ur := data_w32))\<rparr>;
      win' = pre_window win;
      ur' = ur + 16
  in
  state'\<lparr>user_reg := 
    (user_reg state')(win' := ((user_reg state') win')(ur' := data_w32))\<rparr>
"

text \<open>Write a input register.
  Also write ur-16 of the next window.\<close>
definition in_reg_mod :: "word32 \<Rightarrow> ('a::len0) window_size \<Rightarrow> user_reg_type \<Rightarrow>
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"in_reg_mod data_w32 win ur state \<equiv>
  let state' = state\<lparr>user_reg :=
    (user_reg state)(win := ((user_reg state) win)(ur := data_w32))\<rparr>;
      win' = next_window win;
      ur' = ur - 16
  in
  state'\<lparr>user_reg :=
    (user_reg state')(win' := ((user_reg state') win')(ur' := data_w32))\<rparr>
"

text \<open>Do not modify r[0].\<close>
definition user_reg_mod :: "word32 \<Rightarrow> ('a::len0) window_size \<Rightarrow> user_reg_type \<Rightarrow> 
 ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"user_reg_mod data_w32 win ur state \<equiv>
  if ur = 0 then state
  else if 0 < ur \<and> ur < 8 then
    global_reg_mod data_w32 (nat NWINDOWS) ur state
  else if 7 < ur \<and> ur < 16 then 
    out_reg_mod data_w32 win ur state
  else if 15 < ur \<and> ur < 24 then
    state\<lparr>user_reg := 
      (user_reg state)(win := ((user_reg state) win)(ur := data_w32))\<rparr>
  else \<^cancel>\<open>if 23 < ur \<and> ur < 32 then\<close>
    in_reg_mod data_w32 win ur state
  \<^cancel>\<open>else state\<close>
"

definition sys_reg_val :: "sys_reg \<Rightarrow> ('a) sparc_state \<Rightarrow> reg_type"
where
"sys_reg_val reg state \<equiv> (sys_reg state) reg"

definition sys_reg_mod :: "word32 \<Rightarrow> sys_reg \<Rightarrow> 
                          ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"sys_reg_mod data_w32 sys state \<equiv> state\<lparr>sys_reg := (sys_reg state)(sys := data_w32)\<rparr>"

text \<open>The following fucntions deal with physical memory. 
N.B. Physical memory address in SPARCv8 is 36-bit.\<close>

text \<open>LEON3 doesn't distinguish ASI 8 and 9; 10 and 11 for read access
  for both user and supervisor. 
We recently discovered that the compiled machine code by
the sparc-elf compiler often reads asi = 10 (user data) 
when the actual content is store in asi = 8 (user instruction).
For testing purposes, we don't distinguish asi = 8,9,10,11
for reading access.\<close>

definition mem_val:: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                      ('a) sparc_state \<Rightarrow> mem_val_type option"
where
"mem_val asi add state \<equiv> 
  let asi8 = word_of_int 8;
      asi9 = word_of_int 9;
      asi10 = word_of_int 10;
      asi11 = word_of_int 11;
      r1 = (mem state) asi8 add
  in
  if r1 = None then
    let r2 = (mem state) asi9 add in
    if r2 = None then
      let r3 = (mem state) asi10 add in
      if r3 = None then 
        (mem state) asi11 add
      else r3
    else r2
  else r1
"

text \<open>An alternative way to read values from memory. 
Some implementations may use this definition.\<close>

definition mem_val_alt:: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                      ('a) sparc_state \<Rightarrow> mem_val_type option"
where
"mem_val_alt asi add state \<equiv> 
  let r1 = (mem state) asi add; 
      asi8 = word_of_int 8;
      asi9 = word_of_int 9;
      asi10 = word_of_int 10;
      asi11 = word_of_int 11
  in
  if r1 = None \<and> (uint asi) = 8 then
    let r2 = (mem state) asi9 add in
    r2
  else if r1 = None \<and> (uint asi) = 9 then
    let r2 = (mem state) asi8 add in
    r2
  else if r1 = None \<and> (uint asi) = 10 then
    let r2 = (mem state) asi11 add in
    if r2 = None then
      let r3 = (mem state) asi8 add in
      if r3 = None then
        (mem state) asi9 add        
      else r3
    else r2
  else if r1 = None \<and> (uint asi) = 11 then
    let r2 = (mem state) asi10 add in
    if r2 = None then
      let r3 = (mem state) asi8 add in
      if r3 = None then
        (mem state) asi9 add        
      else r3
    else r2
  else r1"

definition mem_mod :: "asi_type \<Rightarrow> phys_address \<Rightarrow> mem_val_type \<Rightarrow> 
                         ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"mem_mod asi addr val state \<equiv>
  let state1 = state\<lparr>mem := (mem state)
    (asi := ((mem state) asi)(addr := Some val))\<rparr>
  in \<comment> \<open>Only allow one of \<open>asi\<close> 8 and 9 (10 and 11) to have value.\<close>
  if (uint asi) = 8 \<or> (uint asi) = 10 then
    let asi2 = word_of_int ((uint asi) + 1) in
    state1\<lparr>mem := (mem state1)
      (asi2 := ((mem state1) asi2)(addr := None))\<rparr>
  else if (uint asi) = 9 \<or> (uint asi) = 11 then
    let asi2 = word_of_int ((uint asi) - 1) in
    state1\<lparr>mem := (mem state1)(asi2 := ((mem state1) asi2)(addr := None))\<rparr>
  else state1
"

text \<open>An alternative way to write memory. This method insists that 
for each address, it can only hold a value in one of ASI = 8,9,10,11.\<close>

definition mem_mod_alt :: "asi_type \<Rightarrow> phys_address \<Rightarrow> mem_val_type \<Rightarrow> 
                         ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"mem_mod_alt asi addr val state \<equiv>
  let state1 = state\<lparr>mem := (mem state)
    (asi := ((mem state) asi)(addr := Some val))\<rparr>;
    asi8 = word_of_int 8;
    asi9 = word_of_int 9;
    asi10 = word_of_int 10;
    asi11 = word_of_int 11
  in 
  \<comment> \<open>Only allow one of \<open>asi\<close> 8, 9, 10, 11 to have value.\<close>
  if (uint asi) = 8 then 
    let state2 = state1\<lparr>mem := (mem state1)
      (asi9 := ((mem state1) asi9)(addr := None))\<rparr>;
     state3 = state2\<lparr>mem := (mem state2)
      (asi10 := ((mem state2) asi10)(addr := None))\<rparr>;
     state4 = state3\<lparr>mem := (mem state3)
      (asi11 := ((mem state3) asi11)(addr := None))\<rparr>
    in
    state4
  else if (uint asi) = 9 then 
    let state2 = state1\<lparr>mem := (mem state1)
      (asi8 := ((mem state1) asi8)(addr := None))\<rparr>;  
     state3 = state2\<lparr>mem := (mem state2)
      (asi10 := ((mem state2) asi10)(addr := None))\<rparr>;
     state4 = state3\<lparr>mem := (mem state3)
      (asi11 := ((mem state3) asi11)(addr := None))\<rparr>
    in
    state4  
  else if (uint asi) = 10 then 
    let state2 = state1\<lparr>mem := (mem state1)
      (asi9 := ((mem state1) asi9)(addr := None))\<rparr>;
     state3 = state2\<lparr>mem := (mem state2)
      (asi8 := ((mem state2) asi8)(addr := None))\<rparr>;
     state4 = state3\<lparr>mem := (mem state3)
      (asi11 := ((mem state3) asi11)(addr := None))\<rparr>
    in
    state4
  else if (uint asi) = 11 then 
    let state2 = state1\<lparr>mem := (mem state1)
      (asi9 := ((mem state1) asi9)(addr := None))\<rparr>;
     state3 = state2\<lparr>mem := (mem state2)
      (asi10 := ((mem state2) asi10)(addr := None))\<rparr>;
     state4 = state3\<lparr>mem := (mem state3)
      (asi8 := ((mem state3) asi8)(addr := None))\<rparr>
    in
    state4
  else state1
"

text \<open>Given an ASI (word8), an address (word32) addr, 
        read the 32bit value from the memory addresses 
        starting from address addr' where addr' = addr 
        exception that the last two bits are 0's. 
        That is, read the data from 
        addr', addr'+1, addr'+2, addr'+3.\<close>
definition mem_val_w32 :: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                           ('a) sparc_state \<Rightarrow> word32 option"
where
"mem_val_w32 asi addr state \<equiv>
  let addr' = bitAND addr 0b111111111111111111111111111111111100;
      addr0 = addr';
      addr1 = addr' + 1;
      addr2 = addr' + 2;
      addr3 = addr' + 3;
      r0 = mem_val_alt asi addr0 state;
      r1 = mem_val_alt asi addr1 state;
      r2 = mem_val_alt asi addr2 state;
      r3 = mem_val_alt asi addr3 state
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
  Let \<open>addr'\<close> be \<open>addr\<close> with last two bits set to 0's.
  Write the 32bit data in the memory address \<open>addr'\<close>
  (and the following 3 addresses). 
  \<open>byte_mask\<close> decides which byte of the 32bits are written.
\<close>
definition mem_mod_w32 :: "asi_type \<Rightarrow> phys_address \<Rightarrow> word4 \<Rightarrow> word32 \<Rightarrow> 
                           ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"mem_mod_w32 asi addr byte_mask data_w32 state \<equiv>
  let addr' = bitAND addr 0b111111111111111111111111111111111100;
      addr0 = bitOR addr' 0b000000000000000000000000000000000000;
      addr1 = bitOR addr' 0b000000000000000000000000000000000001;
      addr2 = bitOR addr' 0b000000000000000000000000000000000010;
      addr3 = bitOR addr' 0b000000000000000000000000000000000011;
      byte0 = (ucast (data_w32 >> 24))::mem_val_type;
      byte1 = (ucast (data_w32 >> 16))::mem_val_type;
      byte2 = (ucast (data_w32 >> 8))::mem_val_type;
      byte3 = (ucast data_w32)::mem_val_type;
      s0 = if ((bitAND byte_mask (0b1000::word4)) >> 3) = 1 then
              mem_mod asi addr0 byte0 state 
           else state;
      s1 = if ((bitAND byte_mask (0b0100::word4)) >> 2) = 1 then
              mem_mod asi addr1 byte1 s0 
           else s0;
      s2 = if ((bitAND byte_mask (0b0010::word4)) >> 1) = 1 then
              mem_mod asi addr2 byte2 s1 
           else s1;
      s3 = if (bitAND byte_mask (0b0001::word4)) = 1 then
              mem_mod asi addr3 byte3 s2 
           else s2
  in
  s3
"

text \<open>The following functions deal with virtual addresses. 
These are based on functions written by David Sanan.\<close>

definition load_word_mem :: "('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> asi_type \<Rightarrow> 
                             machine_word option"
where "load_word_mem state va asi \<equiv> 
let pair = (virt_to_phys va (mmu state) (mem state)) in 
case pair of
  Some pair \<Rightarrow> ( 
    if mmu_readable (get_acc_flag (snd pair)) asi then 
      (mem_val_w32 asi (fst pair) state)
    else None)
  | None \<Rightarrow> None"

definition store_word_mem ::"('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> machine_word \<Rightarrow> 
                             word4 \<Rightarrow> asi_type \<Rightarrow> ('a) sparc_state option"
where "store_word_mem state va wd byte_mask asi \<equiv> 
let pair = (virt_to_phys va (mmu state) (mem state)) in 
case pair of
  Some pair \<Rightarrow> ( 
    if mmu_writable (get_acc_flag (snd pair)) asi then 
      Some (mem_mod_w32 asi (fst pair) byte_mask wd state)
    else None)
  | None \<Rightarrow> None"

definition icache_val:: "cache_type \<Rightarrow> ('a) sparc_state \<Rightarrow> mem_val_type option"
where "icache_val c state \<equiv> icache (cache state) c"

definition dcache_val:: "cache_type \<Rightarrow> ('a) sparc_state \<Rightarrow> mem_val_type option"
where "dcache_val c state \<equiv> dcache (cache state) c"

definition icache_mod :: "cache_type \<Rightarrow> mem_val_type \<Rightarrow> 
                           ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "icache_mod c val state \<equiv> 
  state\<lparr>cache := ((cache state)
    \<lparr>icache := (icache (cache state))(c := Some val)\<rparr>)\<rparr>
"

definition dcache_mod :: "cache_type \<Rightarrow> mem_val_type \<Rightarrow> 
                           ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "dcache_mod c val state \<equiv> 
  state\<lparr>cache := ((cache state)
    \<lparr>dcache := (dcache (cache state))(c := Some val)\<rparr>)\<rparr>
"

text \<open>Check if the memory address is in the cache or not.\<close>
definition icache_miss :: "virtua_address \<Rightarrow> ('a) sparc_state \<Rightarrow> bool"
where
"icache_miss addr state \<equiv>
  let line_len = 12;
      tag = (ucast (addr >> line_len))::cache_tag;
      line = (ucast (0b0::word1))::cache_line_size 
  in
  if (icache_val (tag,line) state) = None then True 
  else False    
"

text \<open>Check if the memory address is in the cache or not.\<close>
definition dcache_miss :: "virtua_address \<Rightarrow> ('a) sparc_state \<Rightarrow> bool"
where
"dcache_miss addr state \<equiv>
  let line_len = 12;
      tag = (ucast (addr >> line_len))::cache_tag;
      line = (ucast (0b0::word1))::cache_line_size 
  in
  if (dcache_val (tag,line) state) = None then True 
  else False    
"

definition read_data_cache:: "('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> machine_word option"
where "read_data_cache state va \<equiv>
  let tag = (ucast (va >> 12))::word20;
       offset0 = bitAND ((ucast va)::word12) 0b111111111100;
       offset1 = bitOR offset0 0b000000000001;
       offset2 = bitOR offset0 0b000000000010;
       offset3 = bitOR offset0 0b000000000011;
       r0 = dcache_val (tag,offset0) state;
       r1 = dcache_val (tag,offset1) state;
       r2 = dcache_val (tag,offset2) state;
       r3 = dcache_val (tag,offset3) state
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

definition read_instr_cache:: "('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> machine_word option"
where "read_instr_cache state va \<equiv>
  let tag = (ucast (va >> 12))::word20;
       offset0 = bitAND ((ucast va)::word12) 0b111111111100;
       offset1 = bitOR offset0 0b000000000001;
       offset2 = bitOR offset0 0b000000000010;
       offset3 = bitOR offset0 0b000000000011;
       r0 = icache_val (tag,offset0) state;
       r1 = icache_val (tag,offset1) state;
       r2 = icache_val (tag,offset2) state;
       r3 = icache_val (tag,offset3) state
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

definition add_data_cache :: "('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> machine_word \<Rightarrow> 
  word4 \<Rightarrow> ('a) sparc_state"
where 
 "add_data_cache state va word byte_mask \<equiv> 
   let tag = (ucast (va >> 12))::word20;
       offset0 = bitAND ((ucast va)::word12) 0b111111111100;
       offset1 = bitOR offset0 0b000000000001;
       offset2 = bitOR offset0 0b000000000010;
       offset3 = bitOR offset0 0b000000000011;
       byte0 = (ucast (word >> 24))::mem_val_type;
       byte1 = (ucast (word >> 16))::mem_val_type;
       byte2 = (ucast (word >> 8))::mem_val_type;
       byte3 = (ucast word)::mem_val_type;
       s0 = if ((bitAND byte_mask (0b1000::word4)) >> 3) = 1 then
              dcache_mod (tag,offset0) byte0 state
            else state;
       s1 = if ((bitAND byte_mask (0b0100::word4)) >> 2) = 1 then
              dcache_mod (tag,offset1) byte1 s0
            else s0;
       s2 = if ((bitAND byte_mask (0b0010::word4)) >> 1) = 1 then
              dcache_mod (tag,offset2) byte2 s1
            else s1;
       s3 = if (bitAND byte_mask (0b0001::word4)) = 1 then
              dcache_mod (tag,offset3) byte3 s2
            else s2
   in s3
"

definition add_instr_cache :: "('a) sparc_state \<Rightarrow> virtua_address \<Rightarrow> machine_word \<Rightarrow> 
  word4 \<Rightarrow> ('a) sparc_state"
where 
 "add_instr_cache state va word byte_mask \<equiv> 
   let tag = (ucast (va >> 12))::word20;
       offset0 = bitAND ((ucast va)::word12) 0b111111111100;
       offset1 = bitOR offset0 0b000000000001;
       offset2 = bitOR offset0 0b000000000010;
       offset3 = bitOR offset0 0b000000000011;
       byte0 = (ucast (word >> 24))::mem_val_type;
       byte1 = (ucast (word >> 16))::mem_val_type;
       byte2 = (ucast (word >> 8))::mem_val_type;
       byte3 = (ucast word)::mem_val_type;
       s0 = if ((bitAND byte_mask (0b1000::word4)) >> 3) = 1 then
              icache_mod (tag,offset0) byte0 state
            else state;
       s1 = if ((bitAND byte_mask (0b0100::word4)) >> 2) = 1 then
              icache_mod (tag,offset1) byte1 s0
            else s0;
       s2 = if ((bitAND byte_mask (0b0010::word4)) >> 1) = 1 then
              icache_mod (tag,offset2) byte2 s1
            else s1;
       s3 = if (bitAND byte_mask (0b0001::word4)) = 1 then
              icache_mod (tag,offset3) byte3 s2
            else s2
   in s3
"

definition empty_cache ::"cache_context" where "empty_cache c \<equiv> None"

definition flush_data_cache:: "('a) sparc_state \<Rightarrow> ('a) sparc_state" where
"flush_data_cache state \<equiv> state\<lparr>cache := ((cache state)\<lparr>dcache := empty_cache\<rparr>)\<rparr>"

definition flush_instr_cache:: "('a) sparc_state \<Rightarrow> ('a) sparc_state" where
"flush_instr_cache state \<equiv> state\<lparr>cache := ((cache state)\<lparr>icache := empty_cache\<rparr>)\<rparr>"

definition flush_cache_all:: "('a) sparc_state \<Rightarrow> ('a) sparc_state" where
"flush_cache_all state \<equiv> state\<lparr>cache := ((cache state)\<lparr>
  icache := empty_cache, dcache := empty_cache\<rparr>)\<rparr>"

text \<open>Check if the FI or FD bit of CCR is 1. 
If FI is 1 then flush instruction cache. 
If FD is 1 then flush data cache.\<close>
definition ccr_flush :: "('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"ccr_flush state \<equiv>
  let ccr_val = sys_reg_val CCR state;
      \<comment> \<open>\<open>FI\<close> is bit 21 of \<open>CCR\<close>\<close>
      fi_val = (bitAND ccr_val (0b00000000001000000000000000000000)) >> 21;
      fd_val = (bitAND ccr_val (0b00000000010000000000000000000000)) >> 22;
      state1 = (if fi_val = 1 then flush_instr_cache state else state)
  in
  if fd_val = 1 then flush_data_cache state1 else state1"

definition get_delayed_pool :: "('a) sparc_state \<Rightarrow> delayed_write_pool"
where "get_delayed_pool state \<equiv> dwrite state"

definition exe_pool :: "(int \<times> reg_type \<times> CPU_register) \<Rightarrow> (int \<times> reg_type \<times> CPU_register)"
where "exe_pool w \<equiv> case w of (n,v,c) \<Rightarrow> ((n-1),v,c)"

text \<open>Minus 1 to the delayed count for all the members in the set. 
        Assuming all members have delay > 0.\<close>
primrec delayed_pool_minus :: "delayed_write_pool \<Rightarrow> delayed_write_pool"
where
"delayed_pool_minus [] = []"
|
"delayed_pool_minus (x#xs) = (exe_pool x)#(delayed_pool_minus xs)"

text \<open>Add a delayed-write to the pool.\<close>
definition delayed_pool_add :: "(int \<times> reg_type \<times> CPU_register) \<Rightarrow> 
                                ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where 
"delayed_pool_add dw s \<equiv>
  let (i,v,cr) = dw in
  if i = 0 then \<comment> \<open>Write the value to the register immediately.\<close>
    cpu_reg_mod v cr s
  else \<comment> \<open>Add to delayed write pool.\<close>
    let curr_pool = get_delayed_pool s in
    s\<lparr>dwrite := curr_pool@[dw]\<rparr>"

text \<open>Remove a delayed-write from the pool. 
        Assume that the delayed-write to be removed has delay 0.
        i.e., it has been executed.\<close>
definition delayed_pool_rm :: "(int \<times> reg_type \<times> CPU_register) \<Rightarrow> 
                               ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where
"delayed_pool_rm dw s \<equiv>
  let curr_pool = get_delayed_pool s in
  case dw of (n,v,cr) \<Rightarrow> 
    (if n = 0 then
      s\<lparr>dwrite := List.remove1 dw curr_pool\<rparr>
     else s)
"

text \<open>Remove all the entries with delay = 0, i.e., those that are written.\<close>
primrec delayed_pool_rm_written :: "delayed_write_pool \<Rightarrow> delayed_write_pool"
where
"delayed_pool_rm_written [] = []"
|
"delayed_pool_rm_written (x#xs) = 
  (if fst x = 0 then delayed_pool_rm_written xs else x#(delayed_pool_rm_written xs))    
"

definition annul_val :: "('a) sparc_state \<Rightarrow> bool"
where "annul_val state \<equiv> get_annul (state_var state)"

definition annul_mod :: "bool \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "annul_mod b s \<equiv> s\<lparr>state_var := write_annul b (state_var s)\<rparr>"

definition reset_trap_val :: "('a) sparc_state \<Rightarrow> bool"
where "reset_trap_val state \<equiv> get_reset_trap (state_var state)"

definition reset_trap_mod :: "bool \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "reset_trap_mod b s \<equiv> s\<lparr>state_var := write_reset_trap b (state_var s)\<rparr>"

definition exe_mode_val :: "('a) sparc_state \<Rightarrow> bool"
where "exe_mode_val state \<equiv> get_exe_mode (state_var state)"

definition exe_mode_mod :: "bool \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "exe_mode_mod b s \<equiv> s\<lparr>state_var := write_exe_mode b (state_var s)\<rparr>"

definition reset_mode_val :: "('a) sparc_state \<Rightarrow> bool"
where "reset_mode_val state \<equiv> get_reset_mode (state_var state)"

definition reset_mode_mod :: "bool \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "reset_mode_mod b s \<equiv> s\<lparr>state_var := write_reset_mode b (state_var s)\<rparr>"

definition err_mode_val :: "('a) sparc_state \<Rightarrow> bool"
where "err_mode_val state \<equiv> get_err_mode (state_var state)"

definition err_mode_mod :: "bool \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "err_mode_mod b s \<equiv> s\<lparr>state_var := write_err_mode b (state_var s)\<rparr>"

definition ticc_trap_type_val :: "('a) sparc_state \<Rightarrow> word7"
where "ticc_trap_type_val state \<equiv> get_ticc_trap_type (state_var state)"

definition ticc_trap_type_mod :: "word7 \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "ticc_trap_type_mod w s \<equiv> s\<lparr>state_var := write_ticc_trap_type w (state_var s)\<rparr>"

definition interrupt_level_val :: "('a) sparc_state \<Rightarrow> word3"
where "interrupt_level_val state \<equiv> get_interrupt_level (state_var state)"

definition interrupt_level_mod :: "word3 \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "interrupt_level_mod w s \<equiv> s\<lparr>state_var := write_interrupt_level w (state_var s)\<rparr>"

definition store_barrier_pending_val :: "('a) sparc_state \<Rightarrow> bool"
where "store_barrier_pending_val state \<equiv> 
  get_store_barrier_pending (state_var state)"

definition store_barrier_pending_mod :: "bool \<Rightarrow> 
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "store_barrier_pending_mod w s \<equiv>
  s\<lparr>state_var := write_store_barrier_pending w (state_var s)\<rparr>"

definition pb_block_ldst_byte_val :: "virtua_address \<Rightarrow> ('a) sparc_state
  \<Rightarrow> bool"
where "pb_block_ldst_byte_val add state \<equiv>
  (atm_ldst_byte (state_var state)) add"

definition pb_block_ldst_byte_mod :: "virtua_address \<Rightarrow> bool \<Rightarrow> 
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "pb_block_ldst_byte_mod add b s \<equiv>
  s\<lparr>state_var := ((state_var s)
    \<lparr>atm_ldst_byte := (atm_ldst_byte (state_var s))(add := b)\<rparr>)\<rparr>"

text \<open>We only read the address such that add mod 4 = 0. 
  add mod 4 represents the current word.\<close>
definition pb_block_ldst_word_val :: "virtua_address \<Rightarrow> ('a) sparc_state
  \<Rightarrow> bool"
where "pb_block_ldst_word_val add state \<equiv>
  let add0 = (bitAND add (0b11111111111111111111111111111100::word32)) in
  (atm_ldst_word (state_var state)) add0"

text \<open>We only write the address such that add mod 4 = 0.
  add mod 4 represents the current word.\<close>
definition pb_block_ldst_word_mod :: "virtua_address \<Rightarrow> bool \<Rightarrow> 
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "pb_block_ldst_word_mod add b s \<equiv>
  let add0 = (bitAND add (0b11111111111111111111111111111100::word32)) in
  s\<lparr>state_var := ((state_var s)
    \<lparr>atm_ldst_word := (atm_ldst_word (state_var s))(add0 := b)\<rparr>)\<rparr>"

definition get_trap_set :: "('a) sparc_state \<Rightarrow> Trap set"
where "get_trap_set state \<equiv> (traps state)"

definition add_trap_set :: "Trap \<Rightarrow> ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "add_trap_set t s \<equiv> s\<lparr>traps := (traps s) \<union> {t}\<rparr>"

definition emp_trap_set :: "('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "emp_trap_set s \<equiv> s\<lparr>traps := {}\<rparr>"

definition state_undef:: "('a) sparc_state \<Rightarrow> bool"
where "state_undef state \<equiv> (undef state)"

text \<open>The \<open>memory_read\<close> interface that conforms with the SPARCv8 manual.\<close>
definition memory_read :: "asi_type \<Rightarrow> virtua_address \<Rightarrow> 
                           ('a) sparc_state \<Rightarrow> 
                           ((word32 option) \<times> ('a) sparc_state)"
where "memory_read asi addr state \<equiv>
  let asi_int = uint asi in \<comment> \<open>See Page 25 and 35 for ASI usage in LEON 3FT.\<close>
  if asi_int = 1 then \<comment> \<open>Forced cache miss.\<close>
    \<comment> \<open>Directly read from memory.\<close>
    let r1 = load_word_mem state addr (word_of_int 8) in
    if r1 = None then
      let r2 = load_word_mem state addr (word_of_int 10) in
      if r2 = None then
        (None,state)
      else (r2,state)
    else (r1,state)
  else if asi_int = 2 then \<comment> \<open>System registers.\<close>
    \<comment> \<open>See Table 19, Page 34 for System Register address map in LEON 3FT.\<close>
    if uint addr = 0 then \<comment> \<open>Cache control register.\<close>
      ((Some (sys_reg_val CCR state)), state)
    else if uint addr = 8 then \<comment> \<open>Instruction cache configuration register.\<close>
      ((Some (sys_reg_val ICCR state)), state)
    else if uint addr = 12 then \<comment> \<open>Data cache configuration register.\<close>
      ((Some (sys_reg_val DCCR state)), state)
    else \<comment> \<open>Invalid address.\<close>
      (None, state)
  else if asi_int \<in> {8,9} then \<comment> \<open>Access instruction memory.\<close>
    let ccr_val = (sys_reg state) CCR in
    if ccr_val AND 1 \<noteq> 0 then \<comment> \<open>Cache is enabled. Update cache.\<close>
    \<comment> \<open>We don't go through the tradition, i.e., read from cache first,\<close>
    \<comment> \<open>if the address is not cached, then read from memory,\<close>
    \<comment> \<open>because performance is not an issue here.\<close>
    \<comment> \<open>Thus we directly read from memory and update the cache.\<close>
      let data = load_word_mem state addr asi in
      case data of
      Some w \<Rightarrow> (Some w,(add_instr_cache state addr w (0b1111::word4)))
      |None \<Rightarrow> (None, state)
    else \<comment> \<open>Cache is disabled. Just read from memory.\<close>
      ((load_word_mem state addr asi),state)
  else if asi_int \<in> {10,11} then \<comment> \<open>Access data memory.\<close>
    let ccr_val = (sys_reg state) CCR in
    if ccr_val AND 1 \<noteq> 0 then \<comment> \<open>Cache is enabled. Update cache.\<close>
    \<comment> \<open>We don't go through the tradition, i.e., read from cache first,\<close>
    \<comment> \<open>if the address is not cached, then read from memory,\<close>
    \<comment> \<open>because performance is not an issue here.\<close>
    \<comment> \<open>Thus we directly read from memory and update the cache.\<close>
      let data = load_word_mem state addr asi in
      case data of
      Some w \<Rightarrow> (Some w,(add_data_cache state addr w (0b1111::word4)))
      |None \<Rightarrow> (None, state)
    else \<comment> \<open>Cache is disabled. Just read from memory.\<close>
      ((load_word_mem state addr asi),state)
  \<comment> \<open>We don't access instruction cache tag. i.e., \<open>asi = 12\<close>.\<close>
  else if asi_int = 13 then \<comment> \<open>Read instruction cache data.\<close>
    let cache_result = read_instr_cache state addr in
    case cache_result of
    Some w \<Rightarrow> (Some w, state)
    |None \<Rightarrow> (None, state)
  \<comment> \<open>We don't access data cache tag. i.e., \<open>asi = 14\<close>.\<close>
  else if asi_int = 15 then \<comment> \<open>Read data cache data.\<close>
    let cache_result = read_data_cache state addr in
    case cache_result of
    Some w \<Rightarrow> (Some w, state)
    |None \<Rightarrow> (None, state)
  else if asi_int \<in> {16,17} then \<comment> \<open>Flush entire instruction/data cache.\<close>
    (None, state) \<comment> \<open>Has no effect for memory read.\<close>
  else if asi_int \<in> {20,21} then \<comment> \<open>MMU diagnostic cache access.\<close>
    (None, state) \<comment> \<open>Not considered in this model.\<close>
  else if asi_int = 24 then \<comment> \<open>Flush cache and TLB in LEON3.\<close>
    \<comment> \<open>But is not used for memory read.\<close>
    (None, state)
  else if asi_int = 25 then \<comment> \<open>MMU registers.\<close>
    \<comment> \<open>Treat MMU registers as memory addresses that are not in the main memory.\<close>
    ((mmu_reg_val (mmu state) addr), state) 
  else if asi_int = 28 then \<comment> \<open>MMU bypass.\<close>
    \<comment> \<open>Directly use addr as a physical address.\<close>
    \<comment> \<open>Append 0000 in the front of addr.\<close>
    \<comment> \<open>In this case, (ucast addr) suffices.\<close>
    ((mem_val_w32 asi (ucast addr) state), state)
  else if asi_int = 29 then \<comment> \<open>MMU diagnostic access.\<close>
    (None, state) \<comment> \<open>Not considered in this model.\<close>
  else \<comment> \<open>Not considered in this model.\<close>
    (None, state)
"

text \<open>Get the value of a memory address and an ASI.\<close>
definition mem_val_asi:: "asi_type \<Rightarrow> phys_address \<Rightarrow> 
                      ('a) sparc_state \<Rightarrow> mem_val_type option"
where "mem_val_asi asi add state \<equiv> (mem state) asi add"

text \<open>Check if an address is used in ASI 9 or 11.\<close>
definition sup_addr :: "phys_address \<Rightarrow> ('a) sparc_state \<Rightarrow> bool"
where
"sup_addr addr state \<equiv>
  let addr' = bitAND addr 0b111111111111111111111111111111111100;
      addr0 = bitOR addr' 0b000000000000000000000000000000000000;
      addr1 = bitOR addr' 0b000000000000000000000000000000000001;
      addr2 = bitOR addr' 0b000000000000000000000000000000000010;
      addr3 = bitOR addr' 0b000000000000000000000000000000000011;
      r0 = mem_val_asi 9 addr0 state;
      r1 = mem_val_asi 9 addr1 state;
      r2 = mem_val_asi 9 addr2 state;
      r3 = mem_val_asi 9 addr3 state;
      r4 = mem_val_asi 11 addr0 state;
      r5 = mem_val_asi 11 addr1 state;
      r6 = mem_val_asi 11 addr2 state;
      r7 = mem_val_asi 11 addr3 state
  in
  if r0 = None \<and> r1 = None \<and> r2 = None \<and> r3 = None \<and>
     r4 = None \<and> r5 = None \<and> r6 = None \<and> r7 = None
  then False
  else True
"

text \<open>The \<open>memory_write\<close> interface that conforms with SPARCv8 manual.\<close>
text \<open>LEON3 forbids user to write an address in ASI 9 and 11.\<close>
definition memory_write_asi :: "asi_type \<Rightarrow> virtua_address \<Rightarrow> word4 \<Rightarrow> word32 \<Rightarrow> 
                            ('a) sparc_state \<Rightarrow> 
                            ('a) sparc_state option"
where
"memory_write_asi asi addr byte_mask data_w32 state \<equiv> 
  let asi_int = uint asi; \<comment> \<open>See Page 25 and 35 for ASI usage in LEON 3FT.\<close>
      psr_val = cpu_reg_val PSR state;
      s_val = get_S psr_val
  in 
  if asi_int = 1 then \<comment> \<open>Forced cache miss.\<close>
    \<comment> \<open>Directly write to memory.\<close>
    \<comment> \<open>Assuming writing into \<open>asi = 10\<close>.\<close>
    store_word_mem state addr data_w32 byte_mask (word_of_int 10) 
  else if asi_int = 2 then \<comment> \<open>System registers.\<close>
    \<comment> \<open>See Table 19, Page 34 for System Register address map in LEON 3FT.\<close>
    if uint addr = 0 then \<comment> \<open>Cache control register.\<close>
      let s1 = (sys_reg_mod data_w32 CCR state) in
      \<comment> \<open>Flush the instruction cache if FI of CCR is 1;\<close>
      \<comment> \<open>flush the data cache if FD of CCR is 1.\<close>
      Some (ccr_flush s1)
    else if uint addr = 8 then \<comment> \<open>Instruction cache configuration register.\<close>
      Some (sys_reg_mod data_w32 ICCR state)
    else if uint addr = 12 then \<comment> \<open>Data cache configuration register.\<close>
      Some (sys_reg_mod data_w32 DCCR state)
    else \<comment> \<open>Invalid address.\<close>
      None
  else if asi_int \<in> {8,9} then \<comment> \<open>Access instruction memory.\<close>
    \<comment> \<open>Write to memory. LEON3 does write-through. Both cache and the memory are updated.\<close>
    let ns = add_instr_cache state addr data_w32 byte_mask in
    store_word_mem ns addr data_w32 byte_mask asi
  else if asi_int \<in> {10,11} then \<comment> \<open>Access data memory.\<close>
    \<comment> \<open>Write to memory. LEON3 does write-through. Both cache and the memory are updated.\<close>
    let ns = add_data_cache state addr data_w32 byte_mask in
    store_word_mem ns addr data_w32 byte_mask asi
  \<comment> \<open>We don't access instruction cache tag. i.e., \<open>asi = 12\<close>.\<close>
  else if asi_int = 13 then \<comment> \<open>Write instruction cache data.\<close>
    Some (add_instr_cache state addr data_w32 (0b1111::word4))
  \<comment> \<open>We don't access data cache tag. i.e., asi = 14.\<close>
  else if asi_int = 15 then \<comment> \<open>Write data cache data.\<close>
    Some (add_data_cache state addr data_w32 (0b1111::word4))
  else if asi_int = 16 then \<comment> \<open>Flush instruction cache.\<close>
    Some (flush_instr_cache state)
  else if asi_int = 17 then \<comment> \<open>Flush data cache.\<close>
    Some (flush_data_cache state)
  else if asi_int \<in> {20,21} then \<comment> \<open>MMU diagnostic cache access.\<close>
    None \<comment> \<open>Not considered in this model.\<close>
  else if asi_int = 24 then \<comment> \<open>Flush TLB and cache in LEON3.\<close>
    \<comment> \<open>We don't consider TLB here.\<close>
    Some (flush_cache_all state)
  else if asi_int = 25 then \<comment> \<open>MMU registers.\<close>
    \<comment> \<open>Treat MMU registers as memory addresses that are not in the main memory.\<close>
    let mmu_state' = mmu_reg_mod (mmu state) addr data_w32 in
    case mmu_state' of
    Some mmus \<Rightarrow> Some (state\<lparr>mmu := mmus\<rparr>)
    |None \<Rightarrow> None 
  else if asi_int = 28 then \<comment> \<open>MMU bypass.\<close>
    \<comment> \<open>Write to virtual address as physical address.\<close>
    \<comment> \<open>Append 0000 in front of addr.\<close>
    Some (mem_mod_w32 asi (ucast addr) byte_mask data_w32 state)
  else if asi_int = 29 then \<comment> \<open>MMU diagnostic access.\<close>
    None \<comment> \<open>Not considered in this model.\<close>
  else \<comment> \<open>Not considered in this model.\<close>
    None
"

definition memory_write :: "asi_type \<Rightarrow> virtua_address \<Rightarrow> word4 \<Rightarrow> word32 \<Rightarrow> 
                            ('a) sparc_state \<Rightarrow> 
                            ('a) sparc_state option"
where
"memory_write asi addr byte_mask data_w32 state \<equiv> 
  let result = memory_write_asi asi addr byte_mask data_w32 state in
  case result of 
  None \<Rightarrow> None
  | Some s1 \<Rightarrow> Some (store_barrier_pending_mod False s1)"

text \<open>monad for sequential operations over the register representation\<close>
type_synonym ('a,'e) sparc_state_monad = "(('a) sparc_state,'e) det_monad" 

text \<open>Given a word32 value, a cpu register, 
        write the value in the cpu register.\<close>
definition write_cpu :: "word32 \<Rightarrow> CPU_register \<Rightarrow> ('a,unit) sparc_state_monad"
where "write_cpu w cr \<equiv>
  do
    modify (\<lambda>s. (cpu_reg_mod w cr s));
    return ()
  od"

definition write_cpu_tt :: "word8 \<Rightarrow> ('a,unit) sparc_state_monad"
where "write_cpu_tt w \<equiv>
  do
    tbr_val \<leftarrow> gets (\<lambda>s. (cpu_reg_val TBR s));
    new_tbr_val \<leftarrow> gets (\<lambda>s. (write_tt w tbr_val));
    write_cpu new_tbr_val TBR;
    return ()
  od"

text \<open>Given a word32 value, a word4 window, a user register, 
        write the value in the user register. 
        N.B. CWP is a 5 bit value, but we only use the last 4 bits,
        since there are only 16 windows.\<close>
definition write_reg :: "word32 \<Rightarrow> ('a::len0) word \<Rightarrow> user_reg_type \<Rightarrow> 
  ('a,unit) sparc_state_monad"
where "write_reg w win ur \<equiv>
  do
    modify (\<lambda>s.(user_reg_mod w win ur s));
    return ()
  od"

definition set_annul :: "bool \<Rightarrow> ('a,unit) sparc_state_monad"
where "set_annul b \<equiv>
  do
    modify (\<lambda>s. (annul_mod b s));
    return ()
  od"

definition set_reset_trap :: "bool \<Rightarrow> ('a,unit) sparc_state_monad"
where "set_reset_trap b \<equiv>
  do
    modify (\<lambda>s. (reset_trap_mod b s));
    return ()
  od"

definition set_exe_mode :: "bool \<Rightarrow> ('a,unit) sparc_state_monad"
where "set_exe_mode b \<equiv>
  do
    modify (\<lambda>s. (exe_mode_mod b s));
    return ()
  od"

definition set_reset_mode :: "bool \<Rightarrow> ('a,unit) sparc_state_monad"
where "set_reset_mode b \<equiv>
  do
    modify (\<lambda>s. (reset_mode_mod b s));
    return ()
  od" 

definition set_err_mode :: "bool \<Rightarrow> ('a,unit) sparc_state_monad"
where "set_err_mode b \<equiv>
  do
    modify (\<lambda>s. (err_mode_mod b s));
    return ()
  od"

fun get_delayed_0 :: "(int \<times> reg_type \<times> CPU_register) list \<Rightarrow> 
  (int \<times> reg_type \<times> CPU_register) list"
where
"get_delayed_0 [] = []"
|
"get_delayed_0 (x # xs) = 
  (if fst x = 0 then x # (get_delayed_0 xs)
  else get_delayed_0 xs)"

text \<open>Get a list of delayed-writes with delay 0.\<close>
definition get_delayed_write :: "delayed_write_pool \<Rightarrow> (int \<times> reg_type \<times> CPU_register) list"
where
"get_delayed_write dwp \<equiv> get_delayed_0 dwp"

definition delayed_write :: "(int \<times> reg_type \<times> CPU_register) \<Rightarrow> ('a) sparc_state \<Rightarrow>
  ('a) sparc_state"
where "delayed_write dw s \<equiv>
  let (n,v,r) = dw in
  if n = 0 then
    cpu_reg_mod v r s
  else s"

primrec delayed_write_all :: "(int \<times> reg_type \<times> CPU_register) list \<Rightarrow>
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "delayed_write_all [] s = s"
|"delayed_write_all (x # xs) s =
  delayed_write_all xs (delayed_write x s)"

primrec delayed_pool_rm_list :: "(int \<times> reg_type \<times> CPU_register) list\<Rightarrow> 
  ('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "delayed_pool_rm_list [] s = s"
|"delayed_pool_rm_list (x # xs) s =
  delayed_pool_rm_list xs (delayed_pool_rm x s)"

definition delayed_pool_write :: "('a) sparc_state \<Rightarrow> ('a) sparc_state"
where "delayed_pool_write s \<equiv>
  let dwp0 = get_delayed_pool s;
      dwp1 = delayed_pool_minus dwp0;
      wl = get_delayed_write dwp1;
      s1 = delayed_write_all wl s;
      s2 = delayed_pool_rm_list wl s1 
  in s2"

definition raise_trap :: "Trap \<Rightarrow> ('a,unit) sparc_state_monad"
where "raise_trap t \<equiv>
  do
    modify (\<lambda>s. (add_trap_set t s));
    return ()
  od"

end

