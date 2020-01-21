(*  Title:      PSL/Smart_Induct/Test_Smart_Induct.thy
 *  An author:  Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
 *
 * Many example definitions, theories, and proofs in this file "Test_Smart_Induct.thy"
 * were originally developed by Tobias Nipkow and Gerwin Klein,
 * as Isabelle theory files accompanying their book "Concrete Semantics".
 * 
 * The PDF file of the book and the original Isabelle theory files are available 
 * at the following website:
 *   http://concrete-semantics.org/index.html
 *
 *)
theory Test_Smart_Induct
imports Smart_Induct
begin

primrec rev :: "'a list \<Rightarrow> 'a list" where
 "rev []       = []" |
 "rev (x # xs) = rev xs @ [x]"
print_theorems

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
 "itrev []     ys = ys" |
 "itrev (x#xs) ys = itrev xs (x#ys)"
print_theorems

lemma "itrev xs ys = rev xs @ ys"
  oops

lemma "itrev xs ys = rev xs @ ys"
  assert_LiFtEr heuristic_11  [on["xs", "ys"],arb[],rule["Smart_Induct.itrev.induct"]]
  assert_LiFtEr only_one_rule [on["xs", "ys"],arb[],rule["Smart_Induct.itrev.induct"]]
  (*This should fail:
   assert_LiFtEr heuristic_11 [on["xs"],      arb[],rule["Smart_Induct.itrev.induct"]]*)
  assert_LiFtEr no_arb_should_be_at_the_same_loc_as_ind [on["xs"],arb["ys"],rule[]]
  oops

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  smart_induct
  assert_LiFtEr no_arb_should_be_at_the_same_loc_as_ind [on["xs"],arb["a"],rule[]]
  oops

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

datatype aexp = N int | V vname | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
  "aval (N n) s = n" |
  "aval (V x) s = s x" |
  "aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s"

value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text {* The same state more concisely: *}
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text {* A little syntax magic to write larger states compactly: *}

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
  "asimp_const (N n) = N n" |
  "asimp_const (V x) = V x" |
  "asimp_const (Plus a\<^sub>1 a\<^sub>2) =
  (case (asimp_const a\<^sub>1, asimp_const a\<^sub>2) of
    (N n\<^sub>1, N n\<^sub>2) \<Rightarrow> N(n\<^sub>1+n\<^sub>2) |
    (b\<^sub>1,b\<^sub>2) \<Rightarrow> Plus b\<^sub>1 b\<^sub>2)"

theorem aval_asimp_const:
  "aval (asimp_const a) s = aval a s"
  smart_induct
  apply(induction a)
    apply (auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
  "plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
  "plus (N i) a = (if i=0 then a else Plus (N i) a)" |
  "plus a (N i) = (if i=0 then a else Plus a (N i))" |
  "plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"

lemma aval_plus [simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
              apply auto
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
  "asimp (N n) = N n" |
  "asimp (V x) = V x" |
  "asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
  smart_induct
  apply(induction a)
    apply auto
  done

datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec1 (LOADI n) _ stk  =  n # stk" |
  "exec1 (LOAD x) s stk  =  s(x) # stk" |
  "exec1  ADD _ (j#i#stk)  =  (i + j) # stk"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack" where
  "exec [] _ stk = stk" |
  "exec (i#is) s stk = exec is s (exec1 i s stk)"

lemma exec_append_model_prf[simp]:
  "exec (is1 @ is2) s stk = exec is2 s (exec is1 s stk)"
  smart_induct
  oops

end