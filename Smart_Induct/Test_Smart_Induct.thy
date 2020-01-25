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
  smart_induct
  apply(induct ys)
   apply(subgoal_tac "\<And> xs ys. itrev xs ys = rev xs @ ys")
    apply fastforce
   apply(subgoal_tac "\<And>xs. \<forall> ys. itrev xs ys = Test_Smart_Induct.rev xs @ ys")
    apply fastforce
   apply (induct_tac xsa)
    apply fastforce+
  apply(subgoal_tac "\<And>xs ys. itrev xs ys = Test_Smart_Induct.rev xs @ ys")
   apply fastforce+
  apply(subgoal_tac "\<And>xs. \<forall> ys. itrev xs ys = Test_Smart_Induct.rev xs @ ys")
   apply fastforce
  apply(induct_tac xsaa)
   apply auto
  oops

fun sep :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sep a [] = []" |
  "sep a [x] = [x]" |
  "sep a (x#y#zs) = x # a # sep a (y#zs)"

lemma "map f (sep a xs) = sep (f a) (map f xs)"
  smart_induct
  apply (induct a xs rule: Test_Smart_Induct.sep.induct)
    apply auto
    done 

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
  smart_induct
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
(* schematic variable introduction
   apply(induct rule: Test_Smart_Induct.aval.induct )*)
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
smart_induct  apply (induct is1 s stk rule: Test_Smart_Induct.exec.induct)
   apply auto
  done

subsection{*Inductive definition of the even numbers*}

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev (Suc(Suc n))"
print_theorems

thm ev0 evSS
thm ev.intros

text{* Using the introduction rules: *}
lemma "ev (Suc(Suc(Suc(Suc 0))))"
apply(rule evSS)
apply(rule evSS)
apply(rule ev0)
done

thm evSS[OF evSS[OF ev0]]

text{* A recursive definition of evenness: *}
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

text{*A simple example of rule induction: *}
lemma "ev n \<Longrightarrow> evn n"
  smart_induct
  assert_LiFtEr heuristic_20 [on[],arb[],rule["Test_Smart_Induct.ev.induct"]]
apply(induction rule: ev.induct)
 apply(simp)
apply(simp)
done

text{* An induction on the computation of evn: *}
lemma "evn n \<Longrightarrow> ev n"
  smart_induct
  assert_LiFtEr heuristic_20 [on[],arb[],rule["Test_Smart_Induct.ev.induct"]]
apply(induction n rule: evn.induct)
  apply (simp add: ev0)
 apply simp
apply(simp add: evSS)
done

text{* No problem with termination because the premises are always smaller
than the conclusion: *}
declare ev.intros[simp,intro]

text{* A shorter proof: *}
lemma "evn n \<Longrightarrow> ev n"
  smart_induct
apply(induction n rule: evn.induct)
apply(simp_all)
done

text{* The power of arith: *}
lemma "ev n \<Longrightarrow> \<exists>k. n = 2*k"
  smart_induct 
apply(induction rule: ev.induct)
 apply(simp)
apply arith
done

subsection{*Inductive definition of the reflexive transitive closure *}

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
apply(induction rule: star.induct)
apply(assumption)
apply(rename_tac u x y)
apply(metis step)
done


end