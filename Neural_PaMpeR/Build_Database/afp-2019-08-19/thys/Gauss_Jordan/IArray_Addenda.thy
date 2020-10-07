(*  
    Title:      IArray_Addenda.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section\<open>IArrays Addenda\<close>

theory IArray_Addenda
  imports 
  "HOL-Library.IArray"
begin

subsection\<open>Some previous instances\<close>

instantiation iarray :: (plus) plus
begin
definition plus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "plus_iarray A B =  IArray.of_fun (\<lambda>n. A!!n + B !! n) (IArray.length A)"
instance proof qed
end

instantiation iarray :: (minus) minus
begin
definition minus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "minus_iarray A B =  IArray.of_fun (\<lambda>n. A!!n - B !! n) (IArray.length A)"
instance proof qed
end

subsection\<open>Some previous definitions and properties for IArrays\<close>

(*
fun find :: "('a => bool) => 'a iarray => 'a option"
  where "find f (IArray as) = List.find f as"
hide_const (open) find

primrec findi_acc_list :: "(nat \<times> 'a => bool) => 'a list => nat => (nat \<times> 'a) option" where
  "findi_acc_list _ [] aux = None" |
  "findi_acc_list P (x#xs) aux = (if P (aux,x) then Some (aux,x) else findi_acc_list P xs (Suc aux))"

definition "findi_list P x = findi_acc_list P x 0"

fun findi :: "(nat \<times> 'a \<Rightarrow> bool) => 'a iarray => (nat \<times> 'a) option"
  where "findi f (IArray as) = findi_list f as"
hide_const (open) findi

fun foldl :: "(('a \<times> 'b) \<Rightarrow> 'b) => 'b => 'a iarray =>'b"
  where "foldl f a (IArray as) = List.foldl (\<lambda>x y. f (y,x)) a as"
hide_const (open) foldl

fun filter :: "('a \<Rightarrow> bool) => 'a iarray => 'a iarray"
  where "filter f (IArray as) = IArray (List.filter f as)"
hide_const (open) filter
*)

subsection\<open>Code generation\<close>

(*
code_printing
  constant "IArray_Addenda.find"  \<rightharpoonup> (SML) "Vector.find"
| constant "IArray_Addenda.findi" \<rightharpoonup> (SML) "Vector.findi"
| constant "IArray_Addenda.foldl" \<rightharpoonup> (SML) "Vector.foldl"
*)

end
