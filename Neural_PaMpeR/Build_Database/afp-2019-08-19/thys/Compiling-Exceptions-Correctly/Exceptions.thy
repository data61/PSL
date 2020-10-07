(*  Author:     Tobias Nipkow
    Copyright   2004 TU Muenchen
*)

section \<open>Compiling exception handling\<close>

theory Exceptions
imports Main
begin

subsection\<open>The source language\<close>

datatype expr = Val int | Add expr expr | Throw | Catch expr expr

primrec eval :: "expr \<Rightarrow> int option"
where
  "eval (Val i) = Some i"
| "eval (Add x y) =
   (case eval x of None \<Rightarrow> None
    | Some i \<Rightarrow> (case eval y of None \<Rightarrow> None
                 | Some j \<Rightarrow> Some(i+j)))"
| "eval Throw = None"
| "eval (Catch x h) = (case eval x of None \<Rightarrow> eval h | Some i \<Rightarrow> Some i)"

subsection\<open>The target language\<close>

datatype instr =
  Push int | ADD | THROW | Mark nat | Unmark | Label nat | Jump nat

datatype item = VAL int | HAN nat

type_synonym code = "instr list"
type_synonym stack = "item list"

fun jump where
  "jump l [] = []"
| "jump l (Label l' # cs) = (if l = l' then cs else jump l cs)"
| "jump l (c # cs) = jump l cs"

lemma size_jump1: "size (jump l cs) < Suc (size cs)"
apply(induct cs)
 apply simp
apply(case_tac a)
apply auto
done

lemma size_jump2: "size (jump l cs) < size cs \<or> jump l cs = cs"
apply(induct cs)
 apply simp
apply(case_tac a)
apply auto
done

function (sequential) exec2 :: "bool \<Rightarrow> code \<Rightarrow> stack \<Rightarrow> stack" where
  "exec2 True [] s = s"
| "exec2 True (Push i#cs) s = exec2 True cs (VAL i # s)"
| "exec2 True (ADD#cs) (VAL j # VAL i # s) = exec2 True cs (VAL(i+j) # s)"
| "exec2 True (THROW#cs) s = exec2 False cs s"
| "exec2 True (Mark l#cs) s = exec2 True cs (HAN l # s)"
| "exec2 True (Unmark#cs) (v # HAN l # s) = exec2 True cs (v # s)"
| "exec2 True (Label l#cs) s = exec2 True cs s"
| "exec2 True (Jump l#cs) s = exec2 True (jump l cs) s"

| "exec2 False cs [] = []"
| "exec2 False cs (VAL i # s) = exec2 False cs s"
| "exec2 False cs (HAN l # s) = exec2 True (jump l cs) s"
by pat_completeness auto

termination by (relation
  "inv_image (measure(%cs. size cs) <*lex*> measure(%s. size s)) (%(b,cs,s). (cs,s))")
    (auto simp add: size_jump1 size_jump2)

abbreviation "exec \<equiv> exec2 True"
abbreviation "unwind \<equiv> exec2 False"

subsection\<open>The compiler\<close>

primrec compile :: "nat \<Rightarrow> expr \<Rightarrow> code * nat"
where
  "compile l (Val i) = ([Push i], l)"
| "compile l (Add x y) = (let (xs,m) = compile l x; (ys,n) = compile m y
                       in (xs @ ys @ [ADD], n))"
| "compile l Throw = ([THROW],l)"
| "compile l (Catch x h) =
    (let (xs,m) = compile (l+2) x; (hs,n) = compile m h
     in (Mark l # xs @ [Unmark, Jump (l+1), Label l] @ hs @ [Label(l+1)], n))"

abbreviation
  cmp :: "nat \<Rightarrow> expr \<Rightarrow> code" where
  "cmp l e == fst(compile l e)"

primrec isFresh :: "nat \<Rightarrow> stack \<Rightarrow> bool"
where
  "isFresh l [] = True"
| "isFresh l (it#s) = (case it of VAL i \<Rightarrow> isFresh l s
                       | HAN l' \<Rightarrow> l' < l \<and> isFresh l s)"

definition
  conv :: "code \<Rightarrow> stack \<Rightarrow> int option \<Rightarrow> stack" where
  "conv cs s io = (case io of None \<Rightarrow> unwind cs s
                  | Some i \<Rightarrow> exec cs (VAL i # s))"

subsection\<open>The proofs\<close>

text\<open>Lemma numbers are the same as in the paper.\<close>

declare
  conv_def[simp] option.splits[split] Let_def[simp]

lemma 3:
  "(\<And>l. c = Label l \<Longrightarrow> isFresh l s) \<Longrightarrow> unwind (c#cs) s = unwind cs s"
apply(induct s)
 apply simp
apply(auto)
apply(case_tac a)
apply auto
apply(case_tac c)
apply auto
done

corollary [simp]:
  "(!!l. c \<noteq> Label l) \<Longrightarrow> unwind (c#cs) s = unwind cs s"
by(blast intro: 3)

corollary [simp]:
  "isFresh l s \<Longrightarrow> unwind (Label l#cs) s = unwind cs s"
by(blast intro: 3)


lemma 5: "\<lbrakk> isFresh l s; l \<le> m \<rbrakk> \<Longrightarrow> isFresh m s"
apply(induct s)
 apply simp
apply(auto split:item.split)
done

corollary [simp]: "isFresh l s \<Longrightarrow> isFresh (Suc l) s"
by(auto intro:5)


lemma 6: "\<And>l. l \<le> snd(compile l e)"
proof(induct e)
  case Val thus ?case by simp
next
  case (Add x y)
  from \<open>l \<le> snd (compile l x)\<close>
   and \<open>snd (compile l x) \<le> snd (compile (snd (compile l x)) y)\<close>
  show ?case by(simp_all add:split_def)
next
  case Throw thus ?case by simp
next
  case (Catch x h)
  from \<open>l+2 \<le> snd (compile (l+2) x)\<close>
   and \<open>snd (compile (l+2) x) \<le> snd (compile (snd (compile (l+2) x)) h)\<close>
  show ?case by(simp_all add:split_def)
qed

corollary [simp]: "l < m \<Longrightarrow> l < snd(compile m e)"
using 6[where l = m and e = e] by auto

corollary [simp]: "isFresh l s \<Longrightarrow> isFresh (snd(compile l e)) s"
using 5 6 by blast


text\<open>Contrary to what the paper says, the proof of lemma 4 does not
just need lemma 3 but also the above corollary of 5 and 6. Hence the
strange order of the lemmas in our proof.\<close>

lemma 4 [simp]: "\<And>l cs. isFresh l s \<Longrightarrow> unwind (cmp l e @ cs) s = unwind cs s"
by (induct e) (auto simp add:split_def)


lemma 7 [simp]: "l < m \<Longrightarrow> jump l (cmp m e @ cs) = jump l cs"
by (induct e arbitrary: m cs) (simp_all add:split_def)

text\<open>The compiler correctness theorem:\<close>

theorem comp_corr:
  "\<And>l s cs. isFresh l s \<Longrightarrow> exec (cmp l e @ cs) s = conv cs s (eval e)"
by(induct e)(auto simp add:split_def)

text\<open>The specialized and more readable version (omitted in the paper):\<close>

corollary "exec (cmp l e) [] = (case eval e of None \<Rightarrow> [] | Some n \<Rightarrow> [VAL n])"
by (simp add: comp_corr[where cs = "[]", simplified])

end
