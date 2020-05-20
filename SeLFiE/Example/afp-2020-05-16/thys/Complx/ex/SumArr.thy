(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Case-study\<close>

theory SumArr
imports
  "../OG_Syntax"
  Word_Lib.Word_Lemmas_32
begin

type_synonym routine = nat
type_synonym word32 = "32 word"
type_synonym funcs = "string \<times> nat"
datatype faults = Overflow | InvalidMem
type_synonym 'a array = "'a list"
 
text \<open>Sumarr computes the combined sum of all the elements of
multiple arrays. It does this by running a number of threads in
parallel, each computing the sum of elements of one of the arrays,
and then adding the result to a global variable gsum shared by all threads.
\<close>
record sumarr_state =
 \<comment> \<open>local variables of threads\<close>
  tarr :: "routine \<Rightarrow> word32 array"
  tid :: "routine \<Rightarrow> word32"
  ti :: "routine \<Rightarrow> word32"
  tsum :: "routine \<Rightarrow> word32"
 \<comment> \<open>global variables\<close>
  glock :: nat
  gsum :: word32
  gdone :: word32
  garr :: "(word32 array) array"
 \<comment> \<open>ghost variables\<close>
  ghost_lock :: "routine \<Rightarrow> bool"

definition
 NSUM :: word32
where
 "NSUM = 10"

definition
 MAXSUM :: word32
where
 "MAXSUM = 1500"

definition
 array_length :: "'a array \<Rightarrow> word32"
where
 "array_length arr \<equiv> of_nat (length arr)"

definition
 array_nth :: "'a array \<Rightarrow> word32 \<Rightarrow>'a"
where
 "array_nth arr n \<equiv> arr ! unat n"

definition
 array_in_bound :: "'a array \<Rightarrow> word32 \<Rightarrow> bool"
where
 "array_in_bound arr idx \<equiv> unat idx < (length arr)"

definition
  array_nat_sum :: "('a :: len0) word array \<Rightarrow> nat"
where
  "array_nat_sum arr \<equiv> sum_list (map unat arr)"

definition
  "local_sum arr \<equiv> of_nat (min (unat MAXSUM) (array_nat_sum arr))"

definition
  "global_sum arr \<equiv> sum_list (map local_sum arr)"

definition
  "tarr_inv s i \<equiv>
    length (tarr s i) = unat NSUM \<and> tarr s i = garr s ! i"

abbreviation
  "sumarr_inv_till_lock s i \<equiv> \<not>gdone s !! i \<and> ((\<not> (ghost_lock s) (1 - i)) \<longrightarrow> ((gdone s = 0 \<and> gsum s = 0) \<or>
    (gdone s !! (1 - i) \<and> gsum s = local_sum (garr s !(1 - i)))))"

abbreviation
  "lock_inv s \<equiv>
    (glock s = fromEnum (ghost_lock s 0) + fromEnum (ghost_lock s 1)) \<and>
    (\<not>(ghost_lock s) 0 \<or> \<not>(ghost_lock s) 1)"

abbreviation
  "garr_inv s i \<equiv> (\<exists>a b. garr s = [a, b]) \<and>
    length (garr s ! (1-i)) = unat NSUM"

abbreviation
  "sumarr_inv s i \<equiv> lock_inv s \<and> tarr_inv s i \<and> garr_inv s i \<and>
    tid s i = (of_nat i + 1)"

definition
  lock :: "routine \<Rightarrow> (sumarr_state, funcs, faults) ann_com"
where
  "lock i \<equiv>
    \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
    AWAIT \<acute>glock = 0
    THEN \<acute>glock:=1,, \<acute>ghost_lock:=\<acute>ghost_lock (i:= True)
    END"

definition
 "sumarr_in_lock1 s i \<equiv> \<not>gdone s !! i \<and> ((gdone s = 0 \<and> gsum s = local_sum (tarr s i)) \<or>
   (gdone s !! (1 - i) \<and> \<not> gdone s !! i \<and> gsum s = global_sum (garr s)))"

definition
 "sumarr_in_lock2 s i \<equiv> (gdone s !! i \<and> \<not> gdone s !! (1 - i) \<and> gsum s = local_sum (tarr s i)) \<or>
   (gdone s !! i \<and> gdone s !! (1 - i) \<and> gsum s = global_sum (garr s))"

definition
  unlock :: "routine \<Rightarrow> (sumarr_state, funcs, faults) ann_com"
where
  "unlock i \<equiv>
    \<lbrace>  \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>glock = 1 \<and>
    \<acute>ghost_lock i \<and> \<acute>gdone !! (unat (\<acute>tid i - 1)) \<and> \<acute>sumarr_in_lock2 i \<rbrace>
    \<langle>\<acute>glock := 0,, \<acute>ghost_lock:=\<acute>ghost_lock (i:= False)\<rangle>"

definition
 "local_postcond s i \<equiv> (\<not> (ghost_lock s) (1 - i) \<longrightarrow> gsum s = (if gdone s !! 0 \<and> gdone s !! 1
              then global_sum (garr s)
              else local_sum (garr s ! i))) \<and> gdone s !! i \<and> \<not>ghost_lock s i"

definition
  sumarr :: "routine \<Rightarrow> (sumarr_state, funcs, faults) ann_com"
where
  "sumarr i \<equiv> 
  \<lbrace>\<acute>sumarr_inv i \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
  \<acute>tsum:=\<acute>tsum(i:=0) ;;
  \<lbrace> \<acute>tsum i = 0 \<and> \<acute>sumarr_inv i \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
  \<acute>ti:=\<acute>ti(i:=0) ;;
  TRY
    \<lbrace> \<acute>tsum i = 0 \<and> \<acute>sumarr_inv i \<and> \<acute>ti i = 0 \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
    WHILE \<acute>ti i < NSUM
    INV \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i \<le> NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
          \<acute>tsum i = local_sum (take (unat (\<acute>ti i)) (\<acute>tarr i)) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
    DO
     \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
       \<acute>tsum i = local_sum (take (unat (\<acute>ti i)) (\<acute>tarr i)) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
     (InvalidMem, \<lbrace> array_in_bound (\<acute>tarr i)  (\<acute>ti i) \<rbrace>) \<longmapsto>
       \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
         \<acute>tsum i = local_sum (take (unat (\<acute>ti i)) (\<acute>tarr i)) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
       \<acute>tsum:=\<acute>tsum(i:=\<acute>tsum i + array_nth (\<acute>tarr i) (\<acute>ti i));;
     \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and>
         local_sum (take (unat (\<acute>ti i)) (\<acute>tarr i)) \<le> MAXSUM \<and>
         (\<acute>tsum i < MAXSUM \<and> array_nth (\<acute>tarr i) (\<acute>ti i) < MAXSUM \<longrightarrow>
       \<acute>tsum i = local_sum (take (Suc (unat (\<acute>ti i))) (\<acute>tarr i))) \<and>
         (array_nth (\<acute>tarr i) (\<acute>ti i) \<ge> MAXSUM \<or> \<acute>tsum i \<ge> MAXSUM\<longrightarrow>
           local_sum (\<acute>tarr i) = MAXSUM)  \<and>
       \<acute>sumarr_inv_till_lock i \<rbrace>
     (InvalidMem, \<lbrace> array_in_bound (\<acute>tarr i)  (\<acute>ti i) \<rbrace>) \<longmapsto>
       \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and>
         (\<acute>tsum i < MAXSUM \<and> array_nth (\<acute>tarr i) (\<acute>ti i) < MAXSUM \<longrightarrow>
           \<acute>tsum i = local_sum (take (Suc (unat (\<acute>ti i))) (\<acute>tarr i))) \<and>
         (array_nth (\<acute>tarr i) (\<acute>ti i) \<ge> MAXSUM \<or> \<acute>tsum i \<ge> MAXSUM \<longrightarrow>
           local_sum (\<acute>tarr i) = MAXSUM) \<and>
         \<acute>sumarr_inv_till_lock i\<rbrace>
       IF array_nth (\<acute>tarr i) (\<acute>ti i) \<ge> MAXSUM \<or> \<acute>tsum i \<ge> MAXSUM 
       THEN
         \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> local_sum (\<acute>tarr i) = MAXSUM \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
         \<acute>tsum:=\<acute>tsum(i:=MAXSUM);;
         \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
           \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>sumarr_inv_till_lock i \<rbrace>
         THROW
       ELSE
         \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
           \<acute>tsum i = local_sum (take (Suc (unat (\<acute>ti i))) (\<acute>tarr i)) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
         SKIP
       FI;;
     \<lbrace> \<acute>sumarr_inv i \<and> \<acute>ti i < NSUM \<and> \<acute>tsum i \<le> MAXSUM \<and>
       \<acute>tsum i = local_sum (take (Suc (unat (\<acute>ti i))) (\<acute>tarr i)) \<and> \<acute>sumarr_inv_till_lock i \<rbrace>
     \<acute>ti:=\<acute>ti(i:=\<acute>ti i + 1)
    OD
  CATCH
    \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>sumarr_inv_till_lock i\<rbrace> SKIP
  END;;
  \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
  SCALL (''lock'', i) 0;;
  \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>glock = 1 \<and>
    \<acute>ghost_lock i \<and> \<acute>sumarr_inv_till_lock i \<rbrace>
  \<acute>gsum:=\<acute>gsum + \<acute>tsum i ;;
  \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>glock = 1 \<and>
    \<acute>ghost_lock i \<and> \<acute>sumarr_in_lock1 i \<rbrace>
  \<acute>gdone:=(\<acute>gdone OR \<acute>tid i) ;;
  \<lbrace> \<acute>sumarr_inv i \<and> \<acute>tsum i = local_sum (\<acute>tarr i) \<and> \<acute>glock = 1 \<and>
    \<acute>ghost_lock i \<and> \<acute>gdone !! (unat (\<acute>tid i - 1)) \<and> \<acute>sumarr_in_lock2 i \<rbrace>
  SCALL (''unlock'', i) 0"

definition
 precond
where
 "precond s \<equiv> (glock s) = 0 \<and> (gsum s) = 0\<and> (gdone s) = 0 \<and>
               (\<exists>a b. garr s = [a, b]) \<and>
               (\<forall>xs\<in>set (garr s). length xs = unat NSUM) \<and>
               (ghost_lock s) 0 = False \<and> (ghost_lock s) 1 = False"

definition
 postcond
where
 "postcond s \<equiv> (gsum s) = global_sum (garr s) \<and>
               (\<forall>i < 2. (gdone s) !! i)"

definition
  "call_sumarr i \<equiv>
    \<lbrace>length (\<acute>garr ! i) = unat NSUM \<and> \<acute>lock_inv \<and> \<acute>garr_inv i \<and>
     \<acute>sumarr_inv_till_lock i\<rbrace>
    CALLX (\<lambda>s. s\<lparr>tarr:=(tarr s)(i:=garr s ! i),
                 tid:=(tid s)(i:=of_nat i+1),
                 ti:=(ti s)(i:=undefined),
                 tsum:=(tsum s)(i:=undefined)\<rparr>)
          \<lbrace>\<acute>sumarr_inv i \<and> \<acute>sumarr_inv_till_lock i\<rbrace>
          (''sumarr'', i) 0
          (\<lambda>s t. t\<lparr>tarr:= (tarr t)(i:=(tarr s) i),
                   tid:=(tid t)(i:=(tid s i)),
                   ti:=(ti t)(i:=(ti s i)),
                   tsum:=(tsum t)(i:=(tsum s i))\<rparr>)
          (\<lambda>_ _. Skip)
          \<lbrace>\<acute>local_postcond i\<rbrace> \<lbrace>\<acute>local_postcond i\<rbrace>
          \<lbrace>False\<rbrace> \<lbrace>False\<rbrace>"

definition
  "\<Gamma> \<equiv> map_of (map (\<lambda>i. ((''sumarr'', i), com (sumarr i))) [0..<2]) ++
  map_of (map (\<lambda>i. ((''lock'', i), com (lock i))) [0..<2]) ++
  map_of (map (\<lambda>i. ((''unlock'', i), com (unlock i))) [0..<2])"

definition
  "\<Theta> \<equiv> map_of (map (\<lambda>i. ((''sumarr'', i), [ann (sumarr i)])) [0..<2]) ++
  map_of (map (\<lambda>i. ((''lock'', i), [ann (lock i)])) [0..<2]) ++
  map_of (map (\<lambda>i. ((''unlock'', i), [ann (unlock i)])) [0..<2])"

declare [[goals_limit = 10]]

lemma [simp]:
  "local_sum [] = 0"
  by (simp add: local_sum_def array_nat_sum_def)

lemma MAXSUM_le_plus:
  "x < MAXSUM \<Longrightarrow> MAXSUM \<le> MAXSUM + x"
  unfolding MAXSUM_def
  apply (rule word_le_plus[rotated], assumption)
  apply clarsimp
 done

lemma local_sum_Suc:
  "\<lbrakk>n < length arr; local_sum (take n arr) + arr ! n < MAXSUM;
    arr ! n < MAXSUM\<rbrakk> \<Longrightarrow>
    local_sum (take n arr) + arr ! n =
      local_sum (take (Suc n) arr)"
  apply (subst take_Suc_conv_app_nth)
   apply clarsimp
  apply (clarsimp simp: local_sum_def array_nat_sum_def )
   apply (subst (asm) min_def, clarsimp split: if_splits)
   apply (clarsimp simp: MAXSUM_le_plus word_not_le[symmetric])
  apply (subst min_absorb2)
   apply (subst of_nat_mono_maybe_le[where 'a=32])
     apply (clarsimp simp: MAXSUM_def)
    apply (clarsimp simp: MAXSUM_def)
    apply unat_arith
   apply (clarsimp simp: MAXSUM_def)
   apply unat_arith
  apply clarsimp
 done

lemma local_sum_MAXSUM:
  "k < length arr \<Longrightarrow> MAXSUM \<le> arr ! k \<Longrightarrow> local_sum arr = MAXSUM"
  apply (clarsimp simp: local_sum_def array_nat_sum_def)
  apply (rule word_unat.Rep_inverse')
  apply (rule min_absorb1[symmetric])
  apply (subst (asm) word_le_nat_alt)
  apply (rule le_trans[rotated])
   apply (rule elem_le_sum_list)
   apply simp
  apply clarsimp
 done

lemma local_sum_MAXSUM':
  "k < length arr \<Longrightarrow>
  MAXSUM \<le> local_sum (take k arr) + arr ! k \<Longrightarrow>
  local_sum (take k arr) \<le> MAXSUM \<Longrightarrow> arr ! k \<le> MAXSUM \<Longrightarrow>
  local_sum arr = MAXSUM"
  apply (clarsimp simp: local_sum_def array_nat_sum_def)
  apply (rule word_unat.Rep_inverse')
  apply (rule min_absorb1[symmetric])
  apply (subst (asm) word_le_nat_alt)
  apply (subst (asm) unat_plus_simple[THEN iffD1])
   apply (rule word_add_le_mono2[where i=0, simplified])
   apply (clarsimp simp: MAXSUM_def)
   apply unat_arith
  apply (rule le_trans, assumption)
  apply (subst unat_of_nat_eq)
   apply (clarsimp simp: MAXSUM_def min.strict_coboundedI1)
  by (subst id_take_nth_drop[where i=k], simp,
         clarsimp simp: trans_le_add1)

lemma word_min_0[simp]:
 "min (x::'a::len0 word) 0 = 0"
 "min 0 (x::'a::len0 word) = 0"
 by (simp add:min_def)+

ML \<open>fun TRY' tac i = TRY (tac i)\<close>


lemma imp_disjL_context':
  "((P \<longrightarrow> R) \<and> (Q \<longrightarrow> R)) = ((P \<longrightarrow> R) \<and> (\<not>P \<and> Q \<longrightarrow> R))"
by auto

lemma map_of_prod_1[simp]:
  "i < n \<Longrightarrow>
    map_of (map (\<lambda>i. ((p, i), g i)) [0..<n])
       (p, i) = Some (g i)"
  apply (rule map_of_is_SomeI)
   apply (clarsimp simp: distinct_map o_def)
   apply (meson inj_onI prod.inject)
  apply clarsimp
  done

lemma map_of_prod_2[simp]:
  "i < n \<Longrightarrow> p \<noteq> q \<Longrightarrow>
    (m ++
    map_of (map (\<lambda>i. ((p, i), g i)) [0..<n]))
       (q, i) = m (q, i)"
  apply (rule map_add_dom_app_simps)
  apply (subst dom_map_of_conv_image_fst)
  apply clarsimp
  done

lemma sumarr_proc_simp[unfolded oghoare_simps]:
 "n < 2 \<Longrightarrow> \<Gamma> (''sumarr'',n) = Some (com (sumarr n))"
 "n < 2 \<Longrightarrow> \<Theta> (''sumarr'',n) = Some ([ann (sumarr n)])"
 "n < 2 \<Longrightarrow> \<Gamma> (''lock'',n) = Some (com (lock n))"
 "n < 2 \<Longrightarrow> \<Theta> (''lock'',n) = Some ([ann (lock n)])"
 "n < 2 \<Longrightarrow> \<Gamma> (''unlock'',n) = Some (com (unlock n))"
 "n < 2 \<Longrightarrow> \<Theta> (''unlock'',n) = Some ([ann (unlock n)])"
 "[ann (sumarr n)]!0 = ann (sumarr n)"
 "[ann (lock n)]!0 = ann (lock n)"
 "[ann (unlock n)]!0 = ann (unlock n)"
 by (simp add: \<Gamma>_def \<Theta>_def)+

lemmas sumarr_proc_simp_unfolded = sumarr_proc_simp[unfolded sumarr_def unlock_def lock_def oghoare_simps]

lemma oghoare_sumarr:
notes sumarr_proc_simp_unfolded[proc_simp add]
shows
 "i < 2 \<Longrightarrow>
  \<Gamma>, \<Theta>
    |\<turnstile>\<^bsub>/F\<^esub> sumarr i \<lbrace>\<acute>local_postcond i\<rbrace>, \<lbrace>False\<rbrace>"
  unfolding sumarr_def unlock_def lock_def
    ann_call_def call_def block_def
  apply simp
  apply oghoare (*23*)
  unfolding tarr_inv_def array_length_def array_nth_def array_in_bound_def
    sumarr_in_lock1_def sumarr_in_lock2_def
  apply (tactic "PARALLEL_ALLGOALS ((TRY' o SOLVED')
          (clarsimp_tac (@{context} addsimps
                @{thms local_postcond_def global_sum_def ex_in_conv[symmetric]}) 
          THEN_ALL_NEW fast_force_tac
             (@{context} addSDs @{thms less_2_cases}
                         addIs @{thms local_sum_Suc unat_mono}
                        )
          ))") (*2*)
   apply clarsimp
   apply (rule conjI)
    apply (fastforce intro!: local_sum_Suc unat_mono)
   apply (subst imp_disjL_context')
   apply (rule conjI)
    apply clarsimp
    apply (erule local_sum_MAXSUM[rotated])
    apply unat_arith
   apply (clarsimp simp: not_le)
   apply (erule (1) local_sum_MAXSUM'[rotated] ; unat_arith)
  apply clarsimp
  apply unat_arith
 done

lemma less_than_two_2[simp]:
  "i < 2 \<Longrightarrow> Suc 0 - i < 2"
  by arith

lemma oghoare_call_sumarr:
notes sumarr_proc_simp[proc_simp add]
shows
  "i < 2 \<Longrightarrow>
  \<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub> call_sumarr i \<lbrace>\<acute>local_postcond i\<rbrace>, \<lbrace>False\<rbrace>"
  unfolding call_sumarr_def ann_call_def call_def block_def
    tarr_inv_def
  apply oghoare (*10*)

  apply (clarsimp; fail | ((simp only: pre.simps)?, rule  oghoare_sumarr))+
  apply (clarsimp simp: sumarr_def tarr_inv_def)
  apply (clarsimp simp: local_postcond_def; fail)+
  done

lemma less_than_two_inv[simp]:
  "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> i \<noteq> j \<Longrightarrow> Suc 0 - i = j"
  by simp
 
lemma inter_aux_call_sumarr[simplified]:
notes  sumarr_proc_simp_unfolded[proc_simp add] com.simps[oghoare_simps add]
shows
  "i < 2 \<Longrightarrow> j < 2 \<Longrightarrow> i \<noteq> j \<Longrightarrow> interfree_aux \<Gamma> \<Theta>
     F (com (call_sumarr i), (ann (call_sumarr i), \<lbrace>\<acute>local_postcond i\<rbrace>, \<lbrace>False\<rbrace>),
        com (call_sumarr j), ann (call_sumarr j))"
  unfolding call_sumarr_def ann_call_def call_def block_def
    tarr_inv_def sumarr_def lock_def unlock_def
  apply oghoare_interfree_aux (*650*)
  unfolding 
    tarr_inv_def local_postcond_def sumarr_in_lock1_def
    sumarr_in_lock2_def
  by (tactic "PARALLEL_ALLGOALS (
                  TRY' (remove_single_Bound_mem @{context}) THEN'
                  (TRY' o SOLVED')
                  (clarsimp_tac @{context} THEN_ALL_NEW
                    fast_force_tac (@{context} addSDs @{thms less_2_cases})
                  ))") (* 2 minutes *)

lemma pre_call_sumarr:
  "i < 2 \<Longrightarrow> precond x \<Longrightarrow> x \<in> pre (ann (call_sumarr i))"
  unfolding precond_def call_sumarr_def ann_call_def
  by (fastforce dest: less_2_cases simp: array_length_def)

lemma post_call_sumarr:
  "local_postcond x 0 \<Longrightarrow> local_postcond x 1 \<Longrightarrow> postcond x"
  unfolding postcond_def local_postcond_def
  by (fastforce dest: less_2_cases split: if_splits)

lemma sumarr_correct: 
  "\<Gamma>, \<Theta> |\<tturnstile>\<^bsub>/F\<^esub> \<lbrace>\<acute>precond\<rbrace>
    COBEGIN
      SCHEME [0 \<le> m < 2]
      call_sumarr m
      \<lbrace>\<acute>local_postcond m\<rbrace>,\<lbrace>False\<rbrace>
    COEND
   \<lbrace>\<acute>postcond\<rbrace>, \<lbrace>False\<rbrace>"
  apply oghoare (* 5 subgoals *)
      apply (fastforce simp: pre_call_sumarr)
     apply (rule oghoare_call_sumarr, simp)
    apply (clarsimp simp: post_call_sumarr)
   apply (simp add: inter_aux_call_sumarr)
  apply clarsimp
 done

end
