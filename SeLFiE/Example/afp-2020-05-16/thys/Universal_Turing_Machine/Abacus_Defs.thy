(* Title: thys/Abacus.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Alternative Definitions for Translating Abacus Machines to TMs\<close>

theory Abacus_Defs
  imports Abacus
begin

abbreviation
  "layout \<equiv> layout_of"

fun address :: "abc_prog \<Rightarrow> nat \<Rightarrow> nat"
  where
    "address p x = (Suc (sum_list (take x (layout p)))) "

abbreviation
  "TMGoto \<equiv> [(Nop, 1), (Nop, 1)]"

abbreviation 
  "TMInc \<equiv> [(W1, 1), (R, 2), (W1, 3), (R, 2), (W1, 3), (R, 4), 
            (L, 7), (W0, 5), (R, 6), (W0, 5), (W1, 3), (R, 6),
            (L, 8), (L, 7), (R, 9), (L, 7), (R, 10), (W0, 9)]"

abbreviation
  "TMDec \<equiv> [(W1, 1), (R, 2), (L, 14), (R, 3), (L, 4), (R, 3),
             (R, 5), (W0, 4), (R, 6), (W0, 5), (L, 7), (L, 8),
             (L, 11), (W0, 7), (W1, 8), (R, 9), (L, 10), (R, 9),
             (R, 5), (W0, 10), (L, 12), (L, 11), (R, 13), (L, 11),
             (R, 17), (W0, 13), (L, 15), (L, 14), (R, 16), (L, 14),
             (R, 0), (W0, 16)]"

abbreviation
  "TMFindnth \<equiv> findnth"

fun compile_goto :: "nat \<Rightarrow> instr list" 
  where
    "compile_goto s = shift TMGoto (s - 1)"

fun compile_inc :: "nat \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "compile_inc s n = (shift (TMFindnth n) (s - 1)) @ (shift (shift TMInc (2 * n)) (s - 1))"

fun compile_dec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "compile_dec s n e = (shift (TMFindnth n) (s - 1)) @ (adjust (shift (shift TMDec (2 * n)) (s - 1)) e)"

fun compile :: "abc_prog \<Rightarrow> nat \<Rightarrow> abc_inst \<Rightarrow> instr list"
  where
    "compile ap s (Inc n) = compile_inc s n"
  | "compile ap s (Dec n e) = compile_dec s n (address ap e)"
  | "compile ap s (Goto e) = compile_goto (address ap e)"

lemma
  "compile ap s i = ci (layout ap) s i"
  apply(cases i)
    apply(simp add: ci.simps shift.simps start_of.simps tinc_b_def)
   apply(simp add: ci.simps shift.simps start_of.simps tdec_b_def)
  apply(simp add: ci.simps shift.simps start_of.simps)
  done


end