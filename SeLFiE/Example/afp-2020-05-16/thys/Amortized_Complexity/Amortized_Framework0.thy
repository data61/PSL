section "Amortized Complexity (Unary Operations)"

theory Amortized_Framework0
imports Complex_Main
begin

text\<open>
This theory provides a simple amortized analysis framework where all operations
act on a single data type, i.e. no union-like operations. This is the basis of
the ITP 2015 paper by Nipkow. Although it is superseded by the model in
\<open>Amortized_Framework\<close> that allows arbitrarily many parameters, it is still
of interest because of its simplicity.\<close>

locale Amortized =
fixes init :: "'s"
fixes nxt :: "'o \<Rightarrow> 's \<Rightarrow> 's"
fixes inv :: "'s \<Rightarrow> bool"
fixes t :: "'o \<Rightarrow> 's \<Rightarrow> real"
fixes \<Phi> :: "'s \<Rightarrow> real"
fixes U :: "'o \<Rightarrow> 's \<Rightarrow> real"
assumes inv_init: "inv init"
assumes inv_nxt: "inv s \<Longrightarrow> inv(nxt f s)"
assumes ppos: "inv s \<Longrightarrow> \<Phi> s \<ge> 0"
assumes p0: "\<Phi> init = 0"
assumes U: "inv s \<Longrightarrow> t f s + \<Phi>(nxt f s) - \<Phi> s \<le> U f s"
begin

fun state :: "(nat \<Rightarrow> 'o) \<Rightarrow> nat \<Rightarrow> 's" where
"state f 0 = init" |
"state f (Suc n) = nxt (f n) (state f n)"

lemma inv_state: "inv(state f n)"
by(induction n)(simp_all add: inv_init inv_nxt)

definition a :: "(nat \<Rightarrow> 'o) \<Rightarrow> nat \<Rightarrow> real" where
"a f i = t (f i) (state f i) + \<Phi>(state f (i+1)) - \<Phi>(state f i)"

lemma aeq: "(\<Sum>i<n. t (f i) (state f i)) = (\<Sum>i<n. a f i) - \<Phi>(state f n)"
apply(induction n)
apply (simp add: p0)
apply (simp add: a_def)
done

corollary ta: "(\<Sum>i<n. t (f i) (state f i)) \<le> (\<Sum>i<n. a f i)"
by (metis add.commute aeq diff_add_cancel le_add_same_cancel2 ppos[OF inv_state])

lemma aa1: "a f i \<le> U (f i) (state f i)"
by(simp add: a_def U inv_state)

lemma ub: "(\<Sum>i<n. t (f i) (state f i)) \<le> (\<Sum>i<n. U (f i) (state f i))"
by (metis (mono_tags) aa1 order.trans sum_mono ta)

end


subsection "Binary Counter"

fun incr where
"incr [] = [True]" |
"incr (False#bs) = True # bs" |
"incr (True#bs) = False # incr bs"

fun t\<^sub>i\<^sub>n\<^sub>c\<^sub>r :: "bool list \<Rightarrow> real" where
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r [] = 1" |
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r (False#bs) = 1" |
"t\<^sub>i\<^sub>n\<^sub>c\<^sub>r (True#bs) = t\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs + 1"

definition p_incr :: "bool list \<Rightarrow> real" ("\<Phi>\<^sub>i\<^sub>n\<^sub>c\<^sub>r") where
"\<Phi>\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs = length(filter id bs)"

lemma a_incr: "t\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs + \<Phi>\<^sub>i\<^sub>n\<^sub>c\<^sub>r(incr bs) - \<Phi>\<^sub>i\<^sub>n\<^sub>c\<^sub>r bs = 2"
apply(induction bs rule: incr.induct)
apply (simp_all add: p_incr_def)
done

interpretation incr: Amortized
where init = "[]" and nxt = "%_. incr" and inv = "\<lambda>_. True"
and t = "\<lambda>_. t\<^sub>i\<^sub>n\<^sub>c\<^sub>r" and \<Phi> = \<Phi>\<^sub>i\<^sub>n\<^sub>c\<^sub>r and U = "\<lambda>_ _. 2"
proof (standard, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by simp
next
  case 3 show ?case by(simp add: p_incr_def)
next
  case 4 show ?case by(simp add: p_incr_def)
next
  case 5 show ?case by(simp add: a_incr)
qed

thm incr.ub


subsection "Dynamic tables: insert only"

fun t\<^sub>i\<^sub>n\<^sub>s :: "nat \<times> nat \<Rightarrow> real" where
"t\<^sub>i\<^sub>n\<^sub>s (n,l) = (if n<l then 1 else n+1)"

interpretation ins: Amortized
where init = "(0::nat,0::nat)"
and nxt = "\<lambda>_ (n,l). (n+1, if n<l then l else if l=0 then 1 else 2*l)"
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> l < 2*n"
and t = "\<lambda>_. t\<^sub>i\<^sub>n\<^sub>s" and \<Phi> = "\<lambda>(n,l). 2*n - l" and U = "\<lambda>_ _. 3"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s) thus ?case by(cases s) auto
next
  case (3 s) thus ?case by(cases s)(simp split: if_splits)
next
  case 4 show ?case by(simp)
next
  case (5 s) thus ?case by(cases s) auto
qed

locale table_insert =
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

fun "ins" :: "nat * nat \<Rightarrow> nat * nat" where
"ins(n,l) = (n+1, if n<l then l else if l=0 then 1 else nat(ceiling(c*l)))"

fun pins :: "nat * nat => real" where
"pins(n,l) = a*n - b*l"

interpretation ins: Amortized
where init = "(0,0)" and nxt = "%_. ins"
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> (b/a)*l \<le> n"
and t = "\<lambda>_. t\<^sub>i\<^sub>n\<^sub>s" and \<Phi> = pins and U = "\<lambda>_ _. a + 1"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s)
  show ?case
  proof (cases s)
    case [simp]: (Pair n l)
    show ?thesis
    proof cases
      assume "l=0" thus ?thesis using 2 ac
        by (simp add: b_def field_simps)
    next
      assume "l\<noteq>0"
      show ?thesis
      proof cases
        assume "n<l"
        thus ?thesis using 2 by(simp add: algebra_simps)
      next
        assume "\<not> n<l"
        hence [simp]: "n=l" using 2 \<open>l\<noteq>0\<close> by simp
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
  case (3 s) thus ?case by(cases s)(simp add: field_simps split: if_splits)
next
  case 4 show ?case by(simp)
next
  case (5 s)
  show ?case
  proof (cases s)
    case [simp]: (Pair n l)
    show ?thesis
    proof cases
      assume "l=0" thus ?thesis using 5 by (simp)
    next
      assume [arith]: "l\<noteq>0"
      show ?thesis
      proof cases
        assume "n<l"
        thus ?thesis using 5 ac by(simp add: algebra_simps b_def)
      next
        assume "\<not> n<l"
        hence [simp]: "n=l" using 5 by simp
        have "t\<^sub>i\<^sub>n\<^sub>s s + pins (ins s) - pins s = l + a + 1 + (- b*ceiling(c*l)) + b*l"
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

thm ins.ub

end

subsection "Stack with multipop"

datatype 'a op\<^sub>s\<^sub>t\<^sub>k = Push 'a | Pop nat

fun nxt\<^sub>s\<^sub>t\<^sub>k :: "'a op\<^sub>s\<^sub>t\<^sub>k \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"nxt\<^sub>s\<^sub>t\<^sub>k (Push x) xs = x # xs" |
"nxt\<^sub>s\<^sub>t\<^sub>k (Pop n) xs = drop n xs"

fun t\<^sub>s\<^sub>t\<^sub>k:: "'a op\<^sub>s\<^sub>t\<^sub>k \<Rightarrow> 'a list \<Rightarrow> real" where
"t\<^sub>s\<^sub>t\<^sub>k (Push x) xs = 1" |
"t\<^sub>s\<^sub>t\<^sub>k (Pop n) xs = min n (length xs)"


interpretation stack: Amortized
where init = "[]" and nxt = nxt\<^sub>s\<^sub>t\<^sub>k and inv = "\<lambda>_. True"
and t = t\<^sub>s\<^sub>t\<^sub>k and \<Phi> = "length" and U = "\<lambda>f _. case f of Push _ \<Rightarrow> 2 | Pop _ \<Rightarrow> 0"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s) thus ?case by(cases s) auto
next
  case 3 thus ?case by simp
next
  case 4 show ?case by(simp)
next
  case (5 _ f) thus ?case by (cases f) auto
qed


subsection "Queue"

text\<open>See, for example, the book by Okasaki~\cite{Okasaki}.\<close>

datatype 'a op\<^sub>q = Enq 'a | Deq

type_synonym 'a queue = "'a list * 'a list"

fun nxt\<^sub>q :: "'a op\<^sub>q \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"nxt\<^sub>q (Enq x) (xs,ys) = (x#xs,ys)" |
"nxt\<^sub>q Deq (xs,ys) = (if ys = [] then ([], tl(rev xs)) else (xs,tl ys))"

fun t\<^sub>q :: "'a op\<^sub>q \<Rightarrow> 'a queue \<Rightarrow> real" where
"t\<^sub>q (Enq x) (xs,ys) = 1" |
"t\<^sub>q Deq (xs,ys) = (if ys = [] then length xs else 0)"


interpretation queue: Amortized
where init = "([],[])" and nxt = nxt\<^sub>q and inv = "\<lambda>_. True"
and t = t\<^sub>q and \<Phi> = "\<lambda>(xs,ys). length xs" and U = "\<lambda>f _. case f of Enq _ \<Rightarrow> 2 | Deq \<Rightarrow> 0"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s) thus ?case by(cases s) auto
next
  case (3 s) thus ?case by(cases s) auto
next
  case 4 show ?case by(simp)
next
  case (5 s f) thus ?case
    apply(cases s)
    apply(cases f)
    by auto
qed


fun balance :: "'a queue \<Rightarrow> 'a queue" where
"balance(xs,ys) = (if size xs \<le> size ys then (xs,ys) else ([], ys @ rev xs))"

fun nxt_q2 :: "'a op\<^sub>q \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"nxt_q2 (Enq a) (xs,ys) = balance (a#xs,ys)" |
"nxt_q2 Deq (xs,ys) = balance (xs, tl ys)"

fun t_q2 :: "'a op\<^sub>q \<Rightarrow> 'a queue \<Rightarrow> real" where
"t_q2 (Enq _) (xs,ys) = 1 + (if size xs + 1 \<le> size ys then 0 else size xs + 1 + size ys)" |
"t_q2 Deq (xs,ys) = (if size xs \<le> size ys - 1 then 0 else size xs + (size ys - 1))"


interpretation queue2: Amortized
where init = "([],[])" and nxt = nxt_q2
and inv = "\<lambda>(xs,ys). size xs \<le> size ys"
and t = t_q2 and \<Phi> = "\<lambda>(xs,ys). 2 * size xs"
and U = "\<lambda>f _. case f of Enq _ \<Rightarrow> 3 | Deq \<Rightarrow> 0"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s f) thus ?case by(cases s) (cases f, auto)
next
  case (3 s) thus ?case by(cases s) auto
next
  case 4 show ?case by(simp)
next
  case (5 s f) thus ?case
    apply(cases s)
    apply(cases f)
    by (auto simp: split: prod.splits)
qed


subsection "Dynamic tables: insert and delete"

datatype op\<^sub>t\<^sub>b = Ins | Del

fun nxt\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> nat*nat" where
"nxt\<^sub>t\<^sub>b Ins (n,l) = (n+1, if n<l then l else if l=0 then 1 else 2*l)" |
"nxt\<^sub>t\<^sub>b Del (n,l) = (n - 1, if n=1 then 0 else if 4*(n - 1)<l then l div 2 else l)"

fun t\<^sub>t\<^sub>b :: "op\<^sub>t\<^sub>b \<Rightarrow> nat*nat \<Rightarrow> real" where
"t\<^sub>t\<^sub>b Ins (n,l) = (if n<l then 1 else n+1)" |
"t\<^sub>t\<^sub>b Del (n,l) = (if n=1 then 1 else if 4*(n - 1)<l then n else 1)"

interpretation tb: Amortized
where init = "(0,0)" and nxt = nxt\<^sub>t\<^sub>b
and inv = "\<lambda>(n,l). if l=0 then n=0 else n \<le> l \<and> l \<le> 4*n"
and t = t\<^sub>t\<^sub>b and \<Phi> = "(\<lambda>(n,l). if 2*n < l then l/2 - n else 2*n - l)"
and U = "\<lambda>f _. case f of Ins \<Rightarrow> 3 | Del \<Rightarrow> 2"
proof (standard, goal_cases)
  case 1 show ?case by auto
next
  case (2 s f) thus ?case by(cases s, cases f) (auto split: if_splits)
next
  case (3 s) thus ?case by(cases s)(simp split: if_splits)
next
  case 4 show ?case by(simp)
next
  case (5 s f) thus ?case apply(cases s) apply(cases f)
    by (auto simp: field_simps)
qed

end
