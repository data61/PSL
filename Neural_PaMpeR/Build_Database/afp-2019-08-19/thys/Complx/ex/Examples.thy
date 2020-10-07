(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
section \<open>Examples\<close>

theory Examples
imports
  "../OG_Syntax"
begin

record test =
  x :: nat
  y :: nat

text \<open>This is a sequence of two commands, the first being an assign
  protected by two guards. The guards use booleans as their faults.\<close>
definition
  "test_guard \<equiv> \<lbrace>True\<rbrace> (True, \<lbrace>\<acute>x=0\<rbrace>),
                       (False, \<lbrace>(0::nat)=0\<rbrace>) \<longmapsto> \<lbrace>True\<rbrace> \<acute>y := 0;;
                      \<lbrace>True\<rbrace> \<acute>x := 0"

lemma
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{True}\<^esub>
    COBEGIN test_guard \<lbrace>True\<rbrace>,\<lbrace>True\<rbrace>
         \<parallel> \<lbrace>True\<rbrace> \<acute>y:=0 \<lbrace>True\<rbrace>, \<lbrace>True\<rbrace>
    COEND \<lbrace>True\<rbrace>,\<lbrace>True\<rbrace>"
  unfolding test_guard_def
  apply oghoare (*11 subgoals*)
           apply simp_all
  done

definition
  "test_try_throw \<equiv> TRY \<lbrace>True\<rbrace> \<acute>y := 0;;
                      \<lbrace>True\<rbrace> THROW
                     CATCH \<lbrace>True\<rbrace> \<acute>x := 0
                     END"


subsection \<open>Parameterized Examples\<close>

subsubsection \<open>Set Elements of an Array to Zero\<close>

record Example1 =
  ex1_a :: "nat \<Rightarrow> nat"

lemma Example1: 
 "\<Gamma>, \<Theta>|\<tturnstile>\<^bsub>/F\<^esub>\<lbrace>True\<rbrace>
   COBEGIN SCHEME [0\<le>i<n] \<lbrace>True\<rbrace> \<acute>ex1_a:=\<acute>ex1_a (i:=0) \<lbrace>\<acute>ex1_a i=0\<rbrace>, \<lbrace>False\<rbrace> COEND 
  \<lbrace>\<forall>i < n. \<acute>ex1_a i = 0\<rbrace>, X"
  apply oghoare (* 7 subgoals *)
        apply (simp ; fail)+
 done

text \<open>Same example but with a Call.\<close>
definition
   "Example1'a \<equiv> \<lbrace>True\<rbrace> \<acute>ex1_a:=\<acute>ex1_a (0:=0)"

definition
   "Example1'b \<equiv> \<lbrace>True\<rbrace> \<acute>ex1_a:=\<acute>ex1_a (1:=0)"

definition "Example1' \<equiv>
  COBEGIN Example1'a \<lbrace>\<acute>ex1_a 0=0\<rbrace>, \<lbrace>False\<rbrace>
         \<parallel> 
         \<lbrace>True\<rbrace> SCALL 0 0
         \<lbrace>\<acute>ex1_a 1=0\<rbrace>, \<lbrace>False\<rbrace>
  COEND"

definition "\<Gamma>' = Map.empty(0 \<mapsto> com Example1'b)"
definition "\<Theta>' = Map.empty(0 :: nat \<mapsto> [ann Example1'b])"

lemma Example1_proc_simp[unfolded Example1'b_def oghoare_simps]:
 "\<Gamma>' 0 = Some (com (Example1'b))"
 "\<Theta>' 0 = Some ([ ann(Example1'b)])"
 "[ ann(Example1'b)]!0 = ann(Example1'b)"
 by (simp add: \<Gamma>'_def \<Theta>'_def)+

lemma Example1':
notes Example1_proc_simp[proc_simp]
shows
 "\<Gamma>', \<Theta>' |\<turnstile>\<^bsub>/F\<^esub> Example1' \<lbrace>\<forall>i < 2. \<acute>ex1_a i = 0\<rbrace>, \<lbrace>False\<rbrace>"
  unfolding Example1'_def 
  apply simp
  unfolding Example1'a_def Example1'b_def
  apply oghoare (*12 subgoals*)
             apply simp+
   using less_2_cases apply blast
  apply simp
  apply (erule disjE ; clarsimp)
done

type_synonym routine = nat

text \<open>Same example but with a Call.\<close>
record Example2 =
  ex2_n :: "routine \<Rightarrow> nat"
  ex2_a :: "nat \<Rightarrow> string"

definition
  Example2'n :: "routine \<Rightarrow> (Example2, string \<times> nat, 'f) ann_com"
where
  "Example2'n i \<equiv> \<lbrace>\<acute>ex2_n i= i\<rbrace> \<acute>ex2_a:=\<acute>ex2_a((\<acute>ex2_n i):='''')"

lemma Example2'n_map_of_simps[simp]:
  "i < n \<Longrightarrow>
    map_of (map (\<lambda>i. ((p, i), g i)) [0..<n])
       (p, i) = Some (g i)"
  apply (rule map_of_is_SomeI)
   apply (clarsimp simp: distinct_map o_def)
   apply (meson inj_onI prod.inject)
  apply clarsimp
  done

definition "\<Gamma>'' n \<equiv>
  map_of (map (\<lambda>i. ((''f'', i), com (Example2'n i))) [0..<n])"

definition "\<Theta>'' n \<equiv>
  map_of (map (\<lambda>i. ((''f'', i), [ann (Example2'n i)])) [0..<n])"

lemma  Example2'n_proc_simp[unfolded Example2'n_def oghoare_simps]:
 "i<n \<Longrightarrow> \<Gamma>'' n (''f'',i) = Some ( com(Example2'n i))"
 "i<n \<Longrightarrow> \<Theta>'' n (''f'',i) = Some ([ ann(Example2'n i)])"
 "[ ann(Example2'n i)]!0 = ann(Example2'n i)"
 by (simp add: \<Gamma>''_def \<Theta>''_def)+

lemmas Example2'n_proc_simp[proc_simp add]

lemma Example2:
notes Example2'n_proc_simp[proc_simp]
shows
 "\<Gamma>'' n, \<Theta>'' n
 |\<tturnstile>\<^bsub>/F\<^esub>\<lbrace>True\<rbrace>
   COBEGIN SCHEME [0\<le>i<n]
     \<lbrace>True\<rbrace>
       CALLX (\<lambda>s. s\<lparr>ex2_n:=(ex2_n s)(i:=i)\<rparr>) \<lbrace>\<acute>ex2_n i = i\<rbrace> (''f'', i) 0
       (\<lambda>s t. t\<lparr>ex2_n:= (ex2_n t)(i:=(ex2_n s) i)\<rparr>) (\<lambda>x y. Skip)
       \<lbrace>\<acute>ex2_a (\<acute>ex2_n i)='''' \<and> \<acute>ex2_n i = i\<rbrace> \<lbrace>\<acute>ex2_a i=''''\<rbrace> \<lbrace>False\<rbrace>  \<lbrace>False\<rbrace>
     \<lbrace>\<acute>ex2_a i=''''\<rbrace>, \<lbrace>False\<rbrace>
   COEND 
  \<lbrace>\<forall>i < n. \<acute>ex2_a i = ''''\<rbrace>, \<lbrace>False\<rbrace>"
  unfolding Example2'n_def ann_call_def call_def block_def 
  apply oghoare (* 113 subgoals *)
  apply (clarsimp ; fail)+
 done

lemmas Example2'n_proc_simp[proc_simp del]

text \<open>Same example with lists as auxiliary variables.\<close>

record Example2_list =
  ex2_A :: "nat list"

lemma Example2_list: 
 "\<Gamma>, \<Theta> |\<tturnstile>\<^bsub>/F\<^esub>\<lbrace>n < length \<acute>ex2_A\<rbrace> 
   COBEGIN 
     SCHEME [0\<le>i<n] \<lbrace>n < length \<acute>ex2_A\<rbrace> \<acute>ex2_A:=\<acute>ex2_A[i:=0] \<lbrace>\<acute>ex2_A!i=0\<rbrace>,\<lbrace>False\<rbrace> 
   COEND 
    \<lbrace>\<forall>i < n. \<acute>ex2_A!i = 0\<rbrace>, X"
  apply oghoare (*7 subgoals*)
        apply force+
 done


lemma exceptions_example:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub> 
   TRY 
   \<lbrace>True \<rbrace> \<acute>y := 0;;
   \<lbrace> \<acute>y = 0 \<rbrace> THROW
   CATCH 
     \<lbrace>\<acute>y = 0\<rbrace> \<acute>x := \<acute>y + 1
   END
   \<lbrace> \<acute>x = 1 \<and> \<acute>y = 0\<rbrace>, \<lbrace>False\<rbrace>"
  by oghoare simp_all

lemma guard_example:
  "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/{42,66}\<^esub> 
  \<lbrace>True\<rbrace> (42, \<lbrace>\<acute>x=0\<rbrace>),
   (66, \<lbrace>\<acute>y=0\<rbrace>) \<longmapsto> \<lbrace>\<acute>x = 0\<rbrace> 
   \<acute>y := 0;;
   \<lbrace>True\<rbrace> \<acute>x := 0
  \<lbrace> \<acute>x = 0\<rbrace>, \<lbrace>False\<rbrace>"
  apply oghoare (*6 subgoals*)
       apply simp_all
 done

subsubsection \<open>Peterson's mutex algorithm I (from Hoare-Parallel) \<close>

text \<open>Eike Best. "Semantics of Sequential and Parallel Programs", page 217.\<close>

record Petersons_mutex_1 =
 pr1 :: nat
 pr2 :: nat
 in1 :: bool
 in2 :: bool
 hold :: nat

lemma peterson_thread_1:
 "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub> \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>  WHILE True INV \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>
  DO
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace> \<langle>\<acute>in1:=True,, \<acute>pr1:=1 \<rangle>;;
  \<lbrace>\<acute>pr1=1 \<and> \<acute>in1\<rbrace>  \<langle>\<acute>hold:=1,, \<acute>pr1:=2 \<rangle>;;
  \<lbrace>\<acute>pr1=2 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)\<rbrace>
  AWAIT (\<not>\<acute>in2 \<or> \<not>(\<acute>hold=1)) THEN
     \<acute>pr1:=3
  END;;
  \<lbrace>\<acute>pr1=3 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)\<rbrace>
   \<langle>\<acute>in1:=False,,\<acute>pr1:=0\<rangle>
  OD \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>,\<lbrace>False\<rbrace>
"
  apply oghoare (*7 subgoals*)
        apply (((auto)[1]) ; fail)+
 done


lemma peterson_thread_2:
 "\<Gamma>, \<Theta> |\<turnstile>\<^bsub>/F\<^esub>  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  WHILE True INV \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  DO
  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace> \<langle>\<acute>in2:=True,, \<acute>pr2:=1 \<rangle>;;
  \<lbrace>\<acute>pr2=1 \<and> \<acute>in2\<rbrace> \<langle> \<acute>hold:=2,, \<acute>pr2:=2 \<rangle> ;;
  \<lbrace>\<acute>pr2=2 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
  AWAIT (\<not>\<acute>in1 \<or> \<not>(\<acute>hold=2)) THEN \<acute>pr2:=3 END;;
  \<lbrace>\<acute>pr2=3 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
    \<langle>\<acute>in2:=False,, \<acute>pr2:=0\<rangle>
  OD \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>,\<lbrace>False\<rbrace>
 "
  apply oghoare (*7 subgoals*)
        apply (((auto simp: )[1]) ; fail)+
  done

lemma Petersons_mutex_1:
  "\<Gamma>, \<Theta> |\<tturnstile>\<^bsub>/F\<^esub> \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2 \<rbrace>
  COBEGIN
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1 \<rbrace>  WHILE True INV \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>
  DO
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace> \<langle> \<acute>in1:=True,, \<acute>pr1:=1 \<rangle>;;
  \<lbrace>\<acute>pr1=1 \<and> \<acute>in1\<rbrace>  \<langle> \<acute>hold:=1,,  \<acute>pr1:=2 \<rangle>;;
  \<lbrace>\<acute>pr1=2 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> (\<acute>hold=2 \<and> \<acute>pr2=2))\<rbrace>
  AWAIT (\<not>\<acute>in2 \<or> \<not>(\<acute>hold=1)) THEN \<acute>pr1:=3  END;;
  \<lbrace>\<acute>pr1=3 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> (\<acute>hold=2 \<and> \<acute>pr2=2))\<rbrace>
   \<langle> \<acute>in1:=False,, \<acute>pr1:=0\<rangle>
  OD \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1\<rbrace>,\<lbrace>False\<rbrace>
  \<parallel>
  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  WHILE True INV \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>
  DO
  \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace> \<langle> \<acute>in2:=True,, \<acute>pr2:=1 \<rangle>;;
  \<lbrace>\<acute>pr2=1 \<and> \<acute>in2\<rbrace> \<langle> \<acute>hold:=2,, \<acute>pr2:=2 \<rangle> ;;
  \<lbrace>\<acute>pr2=2 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
  AWAIT (\<not>\<acute>in1 \<or> \<not>(\<acute>hold=2)) THEN \<acute>pr2:=3 END;;
  \<lbrace>\<acute>pr2=3 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))\<rbrace>
    \<langle> \<acute>in2:=False,, \<acute>pr2:=0\<rangle>
  OD \<lbrace>\<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>,\<lbrace>False\<rbrace>
  COEND
  \<lbrace>\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2\<rbrace>,\<lbrace>False\<rbrace>"
  apply oghoare
\<comment> \<open>81 verification conditions.\<close>
  apply (((auto)[1]) ; fail)+
 done

end

