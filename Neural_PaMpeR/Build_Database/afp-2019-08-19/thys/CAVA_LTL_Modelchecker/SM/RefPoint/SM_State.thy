section \<open>State for SM\<close>
theory SM_State
imports SM_Syntax "HOL-Word.Word" "HOL-Library.Multiset"
begin

section \<open>Values\<close>
  text \<open>The primitive values are fixed-size signed integers\<close>
  type_synonym word_size = 32   \<comment> \<open>Word size\<close>
  type_synonym signed = "word_size Word.word"  \<comment> \<open>Signed integer\<close>
  
  text \<open>Currently, we only have signed integer values. 
    This may change if we extend the language, and allow, 
    i.e., channel pointers, pids or process references\<close>
  type_synonym val = signed  \<comment> \<open>Value type\<close>

section \<open>Configurations\<close>
  type_synonym valuation = "ident \<rightharpoonup> val"

  record local_state = 
    variables :: valuation

  record global_state = 
    variables :: valuation

  text \<open>The effect of actions is on focused states\<close>
  type_synonym focused_state = "local_state \<times> global_state"

section \<open>Utilities\<close>
  abbreviation "word_len \<equiv> LENGTH(word_size)"
  abbreviation "signeds \<equiv> sints (LENGTH(word_size))"

  definition min_signed :: int where "min_signed \<equiv> -(2^(word_len - 1))"
  definition max_signed :: int where "max_signed \<equiv> 2^(word_len - 1) - 1"

  definition signed_of_int :: "int \<Rightarrow> signed" 
    where "signed_of_int i \<equiv> word_of_int i"

  definition int_of_signed :: "signed \<Rightarrow> int"
    where "int_of_signed i == sint i"

  lemma si_inv[simp]: "signed_of_int (int_of_signed i) = i"
    unfolding signed_of_int_def int_of_signed_def
    by simp

  lemma int_of_signed_in_range[simp]: 
    "int_of_signed i \<ge> min_signed"
    "int_of_signed i \<le> max_signed"
    unfolding int_of_signed_def min_signed_def max_signed_def
    apply -
    apply (rule sint_ge)
    using sint_lt[of i]
    by simp

  lemma is_inv[simp]: 
    "\<lbrakk> i\<ge>min_signed; i\<le>max_signed \<rbrakk> \<Longrightarrow> (int_of_signed (signed_of_int i)) = i"
    unfolding int_of_signed_def signed_of_int_def min_signed_def max_signed_def
    by (simp add: sints_num word_sint.Abs_inverse)

  
  primrec val_of_bool :: "bool \<Rightarrow> val" where
    "val_of_bool False = 0" | "val_of_bool True = 1"

  definition bool_of_val :: "val \<Rightarrow> bool" where
    "bool_of_val v \<equiv> v\<noteq>0"

  lemma bool_of_val_invs[simp]: 
    "bool_of_val (val_of_bool b) = b"  
    "val_of_bool (bool_of_val v) = (if v=0 then 0 else 1)"
    unfolding bool_of_val_def
    by (cases b) auto

end
