(*  
    Title:      IArray_Addenda_QR.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>IArray Addenda QR\<close>

theory IArray_Addenda_QR
imports
  "HOL-Library.IArray"
begin

text\<open>The new file about Iarrays, with different instantiations from the presented ones in the 
Gauss-Jordan algorithm.

In order to make the formalisation of the QR algorithm easier, we have decided to present here some
alternative instantiatons for immutable arrays. 

Let see an example. The following definition is the one presented in the Gauss-Jordan AFP entry to
sum two vectors:

\<open>plus_iarray A B =  IArray.of_fun (\<lambda>n. A!!n + B !! n) (IArray.length A)\<close>

While the following is the one we will present in this development:

@{text [display] "plus_iarray A B =
  (let length_A = (IArray.length A);
  length_B= (IArray.length B);
  n=max length_A length_B ;
  A'= IArray.of_fun (\<lambda>a. if a < length_A then A!!a else 0) n;
  B'=IArray.of_fun (\<lambda>a. if a < length_B then B!!a else 0) n
  in IArray.of_fun (\<lambda>a. A' !! a + B' !! a) n)"}

Now the sum is done up to the length of the shortest vector and it is completed with zeros up to
the length of the largest vector. This allows us to prove that iarray is an instance of
\<open>comm_monoid_add\<close>, which is quite useful for the QR algorithm (we will be able to do
sums involving immutable arrays).

These are just alternative definitions of the main operations over immutable arrays. They have the 
advantage of being an instance of \<open>comm_monoid_add\<close>; nevertheless, the performance is slower
and proofs become more cumbersome. The user should decide what definitions to use (the presented 
here or the presented ones in the Gauss-Jordan AFP entry) depending on the algorithm to formalise.
\<close>

lemma iarray_exhaust2: 
  "(xs = ys) = (IArray.list_of xs = IArray.list_of ys)"
  by (metis iarray.exhaust list_of.simps)

lemma of_fun_nth:
  assumes i: "i<n"
  shows "(IArray.of_fun f n) !! i = f i"
  unfolding IArray.of_fun_def using map_nth i by auto

subsection\<open>Some previous instances\<close>

instantiation iarray :: ("{plus,zero}") plus
begin

definition plus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "plus_iarray A B = 
  (let length_A = (IArray.length A);
  length_B= (IArray.length B);
  n=max length_A length_B ; 
  A'= IArray.of_fun (\<lambda>a. if a < length_A then A!!a else 0) n;
  B'=IArray.of_fun (\<lambda>a. if a < length_B then B!!a else 0) n
  in
  IArray.of_fun (\<lambda>a. A' !! a + B' !! a) n)"

instance proof qed
end

instantiation iarray :: (zero) zero
begin
definition "zero_iarray = (IArray[]::'a iarray)"
instance proof qed 
end

instantiation iarray :: (comm_monoid_add) comm_monoid_add
begin

instance 
proof
  fix a b c::"'a iarray"
  have max_eq: "(max (IArray.length 0) (IArray.length a)) =(IArray.length a) "
  proof -
    have "max (length (IArray.list_of (0::'a iarray))) (length (IArray.list_of a)) = length (IArray.list_of a)"
      by (metis list.size(3) list_of.simps max_0L zero_iarray_def)
    thus "max (IArray.length 0) (IArray.length a) = IArray.length a"
      by (metis IArray.length_def list.size(3) list_of.simps zero_iarray_def)
  qed
  have length0: "IArray.length 0 = 0" unfolding zero_iarray_def by auto
  show "0 + a = a" 
  proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, auto, unfold IArray.length_def[symmetric] IArray.sub_def[symmetric])
    show length_eq: "IArray.length (0 + a) = IArray.length a" unfolding plus_iarray_def Let_def using max_eq by auto
    fix i assume i: "i < IArray.length (0 + a)"
    have i2: "i < IArray.length a" by (metis length_eq i)
    have "(0 + a) !! i = (\<lambda>aa. IArray.of_fun (\<lambda>a. if a < 0 then 0 !! a else 0) (IArray.length a) !! aa +
      IArray.of_fun (\<lambda>aa. if aa < IArray.length a then a !! aa else 0) (IArray.length a) !! aa) i"
      unfolding plus_iarray_def Let_def 
      unfolding max_eq unfolding length0 unfolding sub_def[symmetric]
      by (rule of_fun_nth[OF i2])   
    also have "... = (\<lambda>aa. 0 + IArray.of_fun (\<lambda>aa. if aa < IArray.length a then a !! aa else 0) (IArray.length a) !! aa) i"    
      using i2 by auto  
    also have "... =  a !! i" using i2 by simp
    finally show "(0 + a) !! i =  a !! i" .
  qed
  show "a + b = b + a"
  proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, auto, unfold IArray.length_def[symmetric] IArray.sub_def[symmetric])
    have max_eq: "(max (IArray.length a) (IArray.length b)) = IArray.length (a + b)" 
      unfolding plus_iarray_def Let_def by auto
    show length_eq: "IArray.length (a + b) = IArray.length (b + a)"
      unfolding plus_iarray_def Let_def by auto
    fix i assume i: "i < IArray.length (a + b)"
    have i2: "i < IArray.length (b+a)" using i unfolding length_eq .
    have i3: "i < (max (IArray.length a) (IArray.length b))" by (metis i max_eq)
    have i4: "i < (max (IArray.length b) (IArray.length a))" by (metis i3 max.commute)
    show "(a + b) !! i = (b + a) !! i"
      unfolding plus_iarray_def Let_def 
      unfolding of_fun_nth[OF i3]
      unfolding of_fun_nth[OF i4]
      by (simp only: add.commute)
  qed
  show "a + b + c = a + (b + c)"
  proof (unfold iarray_exhaust2 list_eq_iff_nth_eq, auto, unfold IArray.length_def[symmetric] IArray.sub_def[symmetric])
    show length_eq: "IArray.length (a + b + c) = IArray.length (a + (b + c))"
      unfolding plus_iarray_def Let_def by auto
    fix i assume i: "i < IArray.length (a + b + c)"
    have i2: "i<(max (IArray.length (IArray.of_fun (\<lambda>aa. IArray.of_fun 
      (\<lambda>aa. if aa < IArray.length a then a !! aa else 0) (max (IArray.length a) (IArray.length b)) !! aa +
      IArray.of_fun (\<lambda>a. if a < IArray.length b then b !! a else 0) (max (IArray.length a) (IArray.length b)) !! aa)
      (max (IArray.length a) (IArray.length b))))
      (IArray.length c))" using i unfolding plus_iarray_def Let_def by auto
    have i3: "i< (max (IArray.length a) (IArray.length (IArray.of_fun
      (\<lambda>a. IArray.of_fun (\<lambda>a. if a < IArray.length b then b !! a else 0) (max (IArray.length b) (IArray.length c)) !! a +
      IArray.of_fun (\<lambda>a. if a < IArray.length c then c !! a else 0) (max (IArray.length b) (IArray.length c)) !! a)
      (max (IArray.length b) (IArray.length c)))))" 
      using i unfolding plus_iarray_def Let_def by auto
    show "(a + b + c) !! i = (a + (b + c)) !! i"
      unfolding plus_iarray_def unfolding Let_def
      unfolding of_fun_nth[OF i2]
      unfolding of_fun_nth[OF i3]
      using i2 i3
      by (auto simp add: add.assoc)
  qed 
qed
end

instantiation iarray :: (uminus) uminus
begin
definition uminus_iarray :: "'a iarray  \<Rightarrow> 'a iarray"
  where "uminus_iarray A  =  IArray.of_fun (\<lambda>n. - A!!n) (IArray.length A)"
instance proof qed
end

instantiation iarray :: ("{minus,zero}") minus
begin

definition minus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "minus_iarray A B = 
  (let length_A= (IArray.length A);
  length_B= (IArray.length B);
  n=max length_A length_B ; 
  A'= IArray.of_fun (\<lambda>a. if a < length_A then A!!a else 0) n;
  B'=IArray.of_fun (\<lambda>a. if a < length_B then B!!a else 0) n
  in
  IArray.of_fun (\<lambda>a. A' !! a - B' !! a) n)"

instance proof qed
end

subsection\<open>Some previous definitions and properties for IArrays\<close>

subsubsection\<open>Lemmas\<close>

subsubsection\<open>Definitions\<close>

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool"
  where "all p (IArray as) = (ALL a : set as. p a)"
hide_const (open) all

fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool"
  where "exists p (IArray as) = (EX a : set as. p a)"
hide_const (open) exists

subsection\<open>Code generation\<close>

code_printing 
  constant "IArray_Addenda_QR.exists" \<rightharpoonup> (SML) "Vector.exists"
  | constant "IArray_Addenda_QR.all" \<rightharpoonup> (SML) "Vector.all"

end
