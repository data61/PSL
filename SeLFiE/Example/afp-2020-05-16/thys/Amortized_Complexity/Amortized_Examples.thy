section "Simple Examples"

theory Amortized_Examples
imports Amortized_Framework
begin

text\<open>
This theory applies the amortized analysis framework to a number
of simple classical examples.\<close>

subsection "Binary Counter"

locale Bin_Counter
begin

datatype op = Empty | Incr

fun arity :: "op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity Incr = 1"

fun incr :: "bool list \<Rightarrow> bool list" where
"incr [] = [True]" |
"incr (False#bs) = True # bs" |
"incr (True#bs) = False # incr bs"

fun t\<^sub>i\<^sub>n\<^sub>c\<^sub>r :: "bool list \<Rightarrow> nat" where
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r [] = 1" |
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r (False#bs) = 1" |
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r (True#bs) = t\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs + 1"

definition \<Phi> :: "bool list \<Rightarrow> real" where
"\<Phi> bs = length(filter id bs)"

lemma a_incr: "t\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs + \<Phi>(incr bs) - \<Phi> bs = 2"
apply(induction bs rule: incr.induct)
apply (simp_all add: \<Phi>_def)
done

fun exec :: "op \<Rightarrow> bool list list \<Rightarrow> bool list" where
"exec Empty [] = []" |
"exec Incr [bs] = incr bs"

fun cost :: "op \<Rightarrow> bool list list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost Incr [bs] = t\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs"

interpretation Amortized
where exec = exec and arity = arity and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = \<Phi> and U = "\<lambda>f _. case f of Empty \<Rightarrow> 1 | Incr \<Rightarrow> 2"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by(simp add: \<Phi>_def)
next
  case 3 thus ?case using a_incr by(auto simp: \<Phi>_def split: op.split)
qed

end (* Bin_Counter *)


subsection "Stack with multipop"

locale Multipop
begin

datatype 'a op = Empty | Push 'a | Pop nat

fun arity :: "'a op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Push _) = 1" |
"arity (Pop _) = 1"

fun exec :: "'a op \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
"exec Empty [] = []" |
"exec (Push x) [xs] = x # xs" |
"exec (Pop n) [xs] = drop n xs"

fun cost :: "'a op \<Rightarrow> 'a list list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost (Push x) _ = 1" |
"cost (Pop n) [xs] = min n (length xs)"


interpretation Amortized
where arity = arity and exec = exec and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = "length"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 1 | Push _ \<Rightarrow> 2 | Pop _ \<Rightarrow> 0"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by simp
next
  case 3 thus ?case by (auto split: op.split)
qed

end (* Multipop *)


subsection "Dynamic tables: insert only"

locale Dyn_Tab1
begin

type_synonym tab = "nat \<times> nat"

datatype op = Empty | Ins

fun arity :: "op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity Ins = 1"

fun exec :: "op \<Rightarrow> tab list \<Rightarrow> tab" where
"exec Empty [] = (0::nat,0::nat)" |
"exec Ins [(n,l)] = (n+1, if n<l then l else if l=0 then 1 else 2*l)"

fun cost :: "op \<Rightarrow> tab list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost Ins [(n,l)] = (if n<l then 1 else n+1)"

interpretation Amortized
where exec = exec and arity = arity
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> l < 2*n"
and cost = cost and \<Phi> = "\<lambda>(n,l). 2*n - l"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 1 | Ins \<Rightarrow> 3"
proof (standard, goal_cases)
  case (1 _ f) thus ?case by(cases f) (auto split: if_splits)
next
  case 2 thus ?case by(auto split: prod.splits)
next
  case 3 thus ?case by (auto split: op.split) linarith
qed

end (* Dyn_Tab1 *)

locale Dyn_Tab2 =
fixes a :: real
fixes c :: real
assumes c1[arith]: "c > 1" 
assumes ac2: "a \<ge> c/(c - 1)"
begin

lemma ac: "a \<ge> 1/(c - 1)"
using ac2 by(simp add: field_simps)

lemma a0[arith]: "a>0"
proof-
  have "1/(c - 1) > 0" using ac by simp
  thus ?thesis by (metis ac dual_order.strict_trans1)
qed

definition "b = 1/(c - 1)"

lemma b0[arith]: "b > 0"
using ac by (simp add: b_def)

type_synonym tab = "nat \<times> nat"

datatype op = Empty | Ins

fun arity :: "op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity Ins = 1"

fun "ins" :: "tab \<Rightarrow> tab" where
"ins(n,l) = (n+1, if n<l then l else if l=0 then 1 else nat(ceiling(c*l)))"

fun exec :: "op \<Rightarrow> tab list \<Rightarrow> tab" where
"exec Empty [] = (0::nat,0::nat)" |
"exec Ins [s] = ins s" |
"exec _ _ = (0,0)" (* otherwise fun goes wrong with odd error msg *)

fun cost :: "op \<Rightarrow> tab list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost Ins [(n,l)] = (if n<l then 1 else n+1)"

fun \<Phi> :: "tab \<Rightarrow> real" where
"\<Phi>(n,l) = a*n - b*l"

interpretation Amortized
where exec = exec and arity = arity
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> (b/a)*l \<le> n"
and cost = cost and \<Phi> = \<Phi> and U = "\<lambda>f _. case f of Empty \<Rightarrow> 1 | Ins \<Rightarrow> a + 1"
proof (standard, goal_cases)
  case (1 ss f)
  show ?case
  proof (cases f)
    case Empty thus ?thesis using 1 by auto
  next
    case [simp]: Ins
    obtain n l where [simp]: "ss = [(n,l)]" using 1(2) by (auto)
    show ?thesis
    proof cases
      assume "l=0" thus ?thesis using 1 ac
        by (simp add: b_def field_simps)
    next
      assume "l\<noteq>0"
      show ?thesis
      proof cases
        assume "n<l"
        thus ?thesis using 1 by(simp add: algebra_simps)
      next
        assume "\<not> n<l"
        hence [simp]: "n=l" using 1 \<open>l\<noteq>0\<close> by simp
        have 1: "(b/a) * ceiling(c * l) \<le> real l + 1"
        proof-
          have "(b/a) * ceiling(c * l) = ceiling(c * l)/(a*(c - 1))"
            by(simp add: b_def)
          also have "ceiling(c * l) \<le> c*l + 1" by simp
          also have "\<dots> \<le> c*(real l+1)" by (simp add: algebra_simps)
          also have "\<dots> / (a*(c - 1)) = (c/(a*(c - 1))) * (real l + 1)" by simp
          also have "c/(a*(c - 1)) \<le> 1" using ac2 by (simp add: field_simps)
          finally show ?thesis by (simp add: divide_right_mono)
        qed
        have 2: "real l + 1 \<le> ceiling(c * real l)"
        proof-
          have "real l + 1 = of_int(int(l)) + 1" by simp
          also have "... \<le> ceiling(c * real l)" using \<open>l \<noteq> 0\<close>
            by(simp only: int_less_real_le[symmetric] less_ceiling_iff)
              (simp add: mult_less_cancel_right1)
          finally show ?thesis .
        qed
        from \<open>l\<noteq>0\<close> 1 2 show ?thesis by simp (simp add: not_le zero_less_mult_iff)
      qed
    qed
  qed
next
  case 2 thus ?case by(auto simp: field_simps split: if_splits prod.splits)
next
  case (3 ss f)
  show ?case
  proof (cases f)
    case Empty thus ?thesis using 3(2) by simp
  next
    case [simp]: Ins
    obtain n l where [simp]: "ss = [(n,l)]" using 3(2) by (auto)
    show ?thesis
    proof cases
      assume "l=0" thus ?thesis using 3 by (simp)
    next
      assume [arith]: "l\<noteq>0"
      show ?thesis
      proof cases
        assume "n<l"
        thus ?thesis using 3 ac by(simp add: algebra_simps b_def)
      next
        assume "\<not> n<l"
        hence [simp]: "n=l" using 3 by simp
        have "cost Ins [(n,l)] + \<Phi> (ins (n,l)) - \<Phi>(n,l) = l + a + 1 + (- b*ceiling(c*l)) + b*l"
          using \<open>l\<noteq>0\<close>
          by(simp add: algebra_simps less_trans[of "-1::real" 0])
        also have "- b * ceiling(c*l) \<le> - b * (c*l)" by (simp add: ceiling_correct)
        also have "l + a + 1 + - b*(c*l) + b*l = a + 1 + l*(1 - b*(c - 1))"
          by (simp add: algebra_simps)
        also have "b*(c - 1) = 1" by(simp add: b_def)
        also have "a + 1 + (real l)*(1 - 1) = a+1" by simp
        finally show ?thesis by simp
      qed
    qed
  qed
qed

end (* Dyn_Tab2 *)


subsection "Dynamic tables: insert and delete"

locale Dyn_Tab3
begin

type_synonym tab = "nat \<times> nat"

datatype op = Empty | Ins | Del

fun arity :: "op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity Ins = 1" |
"arity Del = 1"

fun exec :: "op \<Rightarrow> tab list \<Rightarrow> tab" where
"exec Empty [] = (0::nat,0::nat)" |
"exec Ins [(n,l)] = (n+1, if n<l then l else if l=0 then 1 else 2*l)" |
"exec Del [(n,l)] = (n-1, if n\<le>1 then 0 else if 4*(n - 1)<l then l div 2 else l)"

fun cost :: "op \<Rightarrow> tab list \<Rightarrow> nat" where
"cost Empty _ = 1" |
"cost Ins [(n,l)] = (if n<l then 1 else n+1)" |
"cost Del [(n,l)] = (if n\<le>1 then 1 else if 4*(n - 1)<l then n else 1)"

interpretation Amortized
where arity = arity and exec = exec
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> l \<le> 4*n"
and cost = cost and \<Phi> = "(\<lambda>(n,l). if 2*n < l then l/2 - n else 2*n - l)"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 1 | Ins \<Rightarrow> 3 | Del \<Rightarrow> 2"
proof (standard, goal_cases)
  case (1 _ f) thus ?case by (cases f) (auto split: if_splits)
next
  case 2 thus ?case by(auto split: prod.splits)
next
  case (3 _ f) thus ?case
    by (cases f)(auto simp: field_simps split: prod.splits)
qed

end (* Dyn_Tab3 *)


subsection "Queue"

text\<open>See, for example, the book by Okasaki~\cite{Okasaki}.\<close>

locale Queue
begin

datatype 'a op = Empty | Enq 'a | Deq

type_synonym 'a queue = "'a list * 'a list"

fun arity :: "'a op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Enq _) = 1" |
"arity Deq = 1"

fun exec :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> 'a queue" where
"exec Empty [] = ([],[])" |
"exec (Enq x) [(xs,ys)] = (x#xs,ys)" |
"exec Deq [(xs,ys)] = (if ys = [] then ([], tl(rev xs)) else (xs,tl ys))"

fun cost :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> nat" where
"cost Empty _ = 0" |
"cost (Enq x) [(xs,ys)] = 1" |
"cost Deq [(xs,ys)] = (if ys = [] then length xs else 0)"

interpretation Amortized
where arity = arity and exec = exec and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = "\<lambda>(xs,ys). length xs"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 0 | Enq _ \<Rightarrow> 2 | Deq \<Rightarrow> 0"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 thus ?case by (auto split: prod.splits)
next
  case 3 thus ?case by(auto split: op.split)
qed

end (* Queue *)

locale Queue2
begin

datatype 'a op = Empty | Enq 'a | Deq

type_synonym 'a queue = "'a list * 'a list"

fun arity :: "'a op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Enq _) = 1" |
"arity Deq = 1"

fun adjust :: "'a queue \<Rightarrow> 'a queue" where
"adjust(xs,ys) = (if ys = [] then ([], rev xs) else (xs,ys))"

fun exec :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> 'a queue" where
"exec Empty [] = ([],[])" |
"exec (Enq x) [(xs,ys)] = adjust(x#xs,ys)" |
"exec Deq [(xs,ys)] = adjust (xs, tl ys)"

fun cost :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> nat" where
"cost Empty _ = 0" |
"cost (Enq x) [(xs,ys)] = 1 + (if ys = [] then size xs + 1 else 0)" |
"cost Deq [(xs,ys)] = (if tl ys = [] then size xs else 0)"

interpretation Amortized
where arity = arity and exec = exec
and inv = "\<lambda>_. True"
and cost = cost and \<Phi> = "\<lambda>(xs,ys). size xs"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 0 | Enq _ \<Rightarrow> 2 | Deq \<Rightarrow> 0"
proof (standard, goal_cases)
  case (1 _ f) thus ?case by (cases f) (auto split: if_splits)
next
  case 2 thus ?case by (auto)
next
  case (3 _ f) thus ?case by(cases f) (auto split: if_splits)
qed

end (* Queue2 *)

locale Queue3
begin

datatype 'a op = Empty | Enq 'a | Deq

type_synonym 'a queue = "'a list * 'a list"

fun arity :: "'a op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Enq _) = 1" |
"arity Deq = 1"

fun balance :: "'a queue \<Rightarrow> 'a queue" where
"balance(xs,ys) = (if size xs \<le> size ys then (xs,ys) else ([], ys @ rev xs))"

fun exec :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> 'a queue" where
"exec Empty [] = ([],[])" |
"exec (Enq x) [(xs,ys)] = balance(x#xs,ys)" |
"exec Deq [(xs,ys)] = balance (xs, tl ys)"

fun cost :: "'a op \<Rightarrow> 'a queue list \<Rightarrow> nat" where
"cost Empty _ = 0" |
"cost (Enq x) [(xs,ys)] = 1 + (if size xs + 1 \<le> size ys then 0 else size xs + 1 + size ys)" |
"cost Deq [(xs,ys)] = (if size xs \<le> size ys - 1 then 0 else size xs + (size ys - 1))"

interpretation Amortized
where arity = arity and exec = exec
and inv = "\<lambda>(xs,ys). size xs \<le> size ys"
and cost = cost and \<Phi> = "\<lambda>(xs,ys). 2 * size xs"
and U = "\<lambda>f _. case f of Empty \<Rightarrow> 0 | Enq _ \<Rightarrow> 3 | Deq \<Rightarrow> 0"
proof (standard, goal_cases)
  case (1 _ f) thus ?case by (cases f) (auto split: if_splits)
next
  case 2 thus ?case by (auto)
next
  case (3 _ f) thus ?case by(cases f) (auto split: prod.splits)
qed

end (* Queue3 *)

end
