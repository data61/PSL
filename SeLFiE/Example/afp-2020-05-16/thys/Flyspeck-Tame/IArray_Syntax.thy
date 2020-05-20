(*  Author:     Gertrud Bauer, Tobias Nipkow
*)

section \<open>Syntax for operations on immutable arrays\<close>

theory IArray_Syntax
imports Main "HOL-Library.IArray"
begin

subsection \<open>Tabulation\<close>

definition tabulate :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a iarray"
where
  "tabulate n f = IArray.of_fun f n"

definition tabulate2 :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a iarray iarray"
where
  "tabulate2 m n f = IArray.of_fun (\<lambda>i .IArray.of_fun (f i) n) m "

definition tabulate3 :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
  (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> 'a iarray iarray iarray" where
  "tabulate3 l m n f \<equiv> IArray.of_fun (\<lambda>i. IArray.of_fun (\<lambda>j. IArray.of_fun (\<lambda>k. f i j k) n) m) l"

syntax 
 "_tabulate" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 'a iarray"  ("(\<lbrakk>_. _ < _\<rbrakk>)") 
 "_tabulate2" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 'a iarray"
   ("(\<lbrakk>_. _ < _, _ < _\<rbrakk>)")
 "_tabulate3" :: "'a \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> pttrn \<Rightarrow> nat \<Rightarrow> 'a iarray"
   ("(\<lbrakk>_. _ < _, _ < _, _ < _ \<rbrakk>)")

translations 
  "\<lbrakk>f. x < n\<rbrakk>" == "CONST tabulate n (\<lambda>x. f)"
  "\<lbrakk>f. x < m, y < n\<rbrakk>" == "CONST tabulate2 m n (\<lambda>x y. f)"
  "\<lbrakk>f. x < l, y < m, z < n\<rbrakk>" == "CONST tabulate3 l m n (\<lambda>x y z. f)"


subsection \<open>Access\<close>

abbreviation sub1_syntax :: "'a iarray \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_\<rbrakk>)" [1000] 999)
where
  "a\<lbrakk>n\<rbrakk> \<equiv> IArray.sub a n"

abbreviation sub2_syntax :: "'a iarray iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_,_\<rbrakk>)" [1000] 999)
where
  "as\<lbrakk>m, n\<rbrakk> \<equiv> IArray.sub (IArray.sub as m) n"

abbreviation sub3_syntax :: "'a iarray iarray iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a"  ("(_\<lbrakk>_,_,_\<rbrakk>)" [1000] 999)
where
  "as\<lbrakk>l, m, n\<rbrakk> \<equiv> IArray.sub (IArray.sub (IArray.sub as l) m) n"

text \<open>examples:  @{term "\<lbrakk>0. i < 5\<rbrakk>"}, @{term "\<lbrakk>i. i < 5, j < 3\<rbrakk>"}\<close>

end

