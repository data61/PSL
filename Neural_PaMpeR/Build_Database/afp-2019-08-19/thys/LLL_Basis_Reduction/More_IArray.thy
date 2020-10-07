(*
    Authors:    Ralph Bottesch
                Maximilian Haslbeck
                René Thiemann
    License:    BSD
*)
section \<open>Auxiliary Lemmas and Definitions for Immutable Arrays\<close>

text \<open>We define some definitions on immutable arrays, and modify the simplication
  rules so that IArrays will mainly operate pointwise, and not as lists.
  To be more precise, IArray.of-fun will become the main constructor.\<close>
theory More_IArray
  imports "HOL-Library.IArray" 
begin

definition iarray_update :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a iarray" where
  "iarray_update a i x = IArray.of_fun (\<lambda> j. if j = i then x else a !! j) (IArray.length a)" 

lemma iarray_cong: "n = m \<Longrightarrow> (\<And> i. i < m \<Longrightarrow> f i = g i) \<Longrightarrow> IArray.of_fun f n = IArray.of_fun g m" 
  by auto

lemma iarray_cong': "(\<And> i. i < n \<Longrightarrow> f i = g i) \<Longrightarrow> IArray.of_fun f n = IArray.of_fun g n" 
  by (rule iarray_cong, auto)

lemma iarray_update_length[simp]: "IArray.length (iarray_update a i x) = IArray.length a" 
  unfolding iarray_update_def by simp

lemma iarray_length_of_fun[simp]: "IArray.length (IArray.of_fun f n) = n" by simp

lemma iarray_update_of_fun[simp]: "iarray_update (IArray.of_fun f n) i x = IArray.of_fun (f (i := x)) n" 
  unfolding iarray_update_def iarray_length_of_fun
  by (rule iarray_cong, auto)

fun iarray_append where "iarray_append (IArray xs) x = IArray (xs @ [x])" 

lemma iarray_append_code[code]: "iarray_append xs x = IArray (IArray.list_of xs @ [x])"
  by (cases xs, auto)

lemma iarray_append_of_fun[simp]: "iarray_append (IArray.of_fun f n) x = IArray.of_fun (f (n := x)) (Suc n)" 
  by auto

declare iarray_append.simps[simp del]

lemma iarray_of_fun_sub[simp]: "i < n \<Longrightarrow> IArray.of_fun f n !! i = f i" 
  by auto

lemma IArray_of_fun_conv: "IArray xs = IArray.of_fun (\<lambda> i. xs ! i) (length xs)" 
  by (auto intro!: nth_equalityI)

declare IArray.of_fun_def[simp del]
declare IArray.sub_def[simp del]

lemmas iarray_simps = iarray_update_of_fun iarray_append_of_fun IArray_of_fun_conv iarray_of_fun_sub

end
