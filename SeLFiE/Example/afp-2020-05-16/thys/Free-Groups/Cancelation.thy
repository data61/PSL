section \<open>Cancelation of words of generators and their inverses\<close>

theory Cancelation
imports
  "HOL-Proofs-Lambda.Commutation"
begin

text \<open>
This theory defines cancelation via relations. The one-step relation @{term
"cancels_to_1 a b"} describes that @{term b} is obtained from @{term a} by removing
exactly one pair of generators, while @{term cancels_to} is the reflexive
transitive hull of that relation. Due to confluence, this relation has a normal
form, allowing for the definition of @{term normalize}.
\<close>

subsection \<open>Auxiliary results\<close>

text \<open>Some lemmas that would be useful in a more general setting are
collected beforehand.\<close>

subsubsection \<open>Auxiliary results about relations\<close>

text \<open>
These were helpfully provided by Andreas Lochbihler.
\<close>

theorem lconfluent_confluent:
  "\<lbrakk> wfP (R^--1); \<And>a b c. R a b \<Longrightarrow> R a c \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d  \<rbrakk> \<Longrightarrow> confluent R"
by(auto simp add: diamond_def commute_def square_def intro: newman)

lemma confluentD:
  "\<lbrakk> confluent R; R^** a b; R^** a c  \<rbrakk> \<Longrightarrow> \<exists>d. R^** b d \<and> R^** c d"
by(auto simp add: commute_def diamond_def square_def)

lemma tranclp_DomainP: "R^++ a b \<Longrightarrow> Domainp R a"
by(auto elim: converse_tranclpE)

lemma confluent_unique_normal_form:
  "\<lbrakk> confluent R; R^** a b; R^** a c; \<not> Domainp R b; \<not> Domainp R c  \<rbrakk> \<Longrightarrow> b = c"
by(fastforce dest!: confluentD[of R a b c] dest: tranclp_DomainP rtranclpD[where a=b] rtranclpD[where a=c])

subsection \<open>Definition of the @{term "canceling"} relation\<close>

type_synonym 'a "g_i" = "(bool \<times> 'a)" (* A generator or its inverse *)
type_synonym 'a "word_g_i" = "'a g_i list" (* A word in the generators or their inverses *)

text \<open>
These type aliases encode the notion of a ``generator or its inverse''
(@{typ "'a g_i"}) and the notion of a ``word in generators and their inverses''
(@{typ "'a word_g_i"}), which form the building blocks of Free Groups.
\<close>

definition canceling :: "'a g_i \<Rightarrow> 'a g_i \<Rightarrow> bool"
 where "canceling a b = ((snd a = snd b) \<and> (fst a \<noteq> fst b))"

subsubsection \<open>Simple results about canceling\<close>

text \<open>
A generators cancels with its inverse, either way. The relation is symmetic.
\<close>

lemma cancel_cancel: "\<lbrakk> canceling a b; canceling b c \<rbrakk> \<Longrightarrow> a = c"
by (auto intro: prod_eqI simp add:canceling_def)

lemma cancel_sym: "canceling a b \<Longrightarrow> canceling b a"
by (simp add:canceling_def)

lemma cancel_sym_neg: "\<not>canceling a b \<Longrightarrow> \<not>canceling b a"
by (rule classical, simp add:canceling_def)

subsection \<open>Definition of the @{term "cancels_to"} relation\<close>

text \<open>
First, we define the function that removes the @{term i}th and \<open>(i+1)\<close>st
element from a word of generators, together with basic properties.
\<close>

definition cancel_at :: "nat \<Rightarrow> 'a word_g_i \<Rightarrow> 'a word_g_i"
where "cancel_at i l = take i l @ drop (2+i) l"

lemma cancel_at_length[simp]:
  "1+i < length l \<Longrightarrow> length (cancel_at i l) = length l - 2"
by(auto simp add: cancel_at_def)

lemma cancel_at_nth1[simp]:
  "\<lbrakk> n < i; 1+i < length l  \<rbrakk> \<Longrightarrow> (cancel_at i l) ! n = l ! n"
by(auto simp add: cancel_at_def nth_append)

lemma cancel_at_nth2[simp]:
  assumes "n \<ge> i" and "n < length l - 2"
  shows "(cancel_at i l) ! n = l ! (n + 2)"
proof-
  from \<open>n \<ge> i\<close> and \<open>n < length l - 2\<close>
  have "i = min (length l) i"
    by auto
  with \<open>n \<ge> i\<close> and \<open>n < length l - 2\<close>
  show "(cancel_at i l) ! n = l ! (n + 2)" 
    by(auto simp add: cancel_at_def nth_append nth_via_drop)
qed

text \<open>
Then we can define the relation @{term "cancels_to_1_at i a b"} which specifies
that @{term b} can be obtained by @{term a} by canceling the @{term i}th and
\<open>(i+1)\<close>st position.

Based on that, we existentially quantify over the position \<open>i\<close> to obtain
the relation \<open>cancels_to_1\<close>, of which \<open>cancels_to\<close> is the
reflexive and transitive closure.

A word is \<open>canceled\<close> if it can not be canceled any futher.
\<close>

definition cancels_to_1_at ::  "nat \<Rightarrow> 'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where  "cancels_to_1_at i l1 l2 = (0\<le>i \<and> (1+i) < length l1
                              \<and> canceling (l1 ! i) (l1 ! (1+i))
                              \<and> (l2 = cancel_at i l1))"

definition cancels_to_1 :: "'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where "cancels_to_1 l1 l2 = (\<exists>i. cancels_to_1_at i l1 l2)"

definition cancels_to  :: "'a word_g_i \<Rightarrow> 'a word_g_i \<Rightarrow> bool"
where "cancels_to = cancels_to_1^**"

lemma cancels_to_trans [trans]:
  "\<lbrakk> cancels_to a b; cancels_to b c \<rbrakk> \<Longrightarrow> cancels_to a c"
by (auto simp add:cancels_to_def)

definition canceled :: "'a word_g_i \<Rightarrow> bool"
 where "canceled l = (\<not> Domainp cancels_to_1 l)"

(* Alternative view on cancelation, sometimes easier to work with *)
lemma cancels_to_1_unfold:
  assumes "cancels_to_1 x y"
  obtains xs1 x1 x2 xs2
  where "x = xs1 @ x1 # x2 # xs2"
    and "y = xs1 @ xs2"
    and "canceling x1 x2"
proof-
  assume a: "(\<And>xs1 x1 x2 xs2. \<lbrakk>x = xs1 @ x1 # x2 # xs2; y = xs1 @ xs2; canceling x1 x2\<rbrakk> \<Longrightarrow> thesis)"
  from \<open>cancels_to_1 x y\<close>
  obtain i where "cancels_to_1_at i x y"
    unfolding cancels_to_1_def by auto
  hence "canceling (x ! i) (x ! Suc i)"
    and "y = (take i x) @ (drop (Suc (Suc i)) x)"
    and "x = (take i x) @ x ! i # x ! Suc i # (drop (Suc (Suc i)) x)"
    unfolding cancel_at_def and cancels_to_1_at_def by (auto simp add: Cons_nth_drop_Suc)
  with a show thesis by blast
qed

(* And the reverse direction *)
lemma cancels_to_1_fold:
  "canceling x1 x2 \<Longrightarrow> cancels_to_1 (xs1 @ x1 # x2 # xs2) (xs1 @ xs2)"
unfolding cancels_to_1_def and cancels_to_1_at_def and cancel_at_def
by (rule_tac x="length xs1" in exI, auto simp add:nth_append)

subsubsection \<open>Existence of the normal form\<close>

text \<open>
One of two steps to show that we have a normal form is the following lemma,
guaranteeing that by canceling, we always end up at a fully canceled word.
\<close>

lemma canceling_terminates: "wfP (cancels_to_1^--1)"
proof-
  have "wf (measure length)" by auto
  moreover
  have "{(x, y). cancels_to_1 y x} \<subseteq> measure length"
    by (auto simp add: cancels_to_1_def cancel_at_def cancels_to_1_at_def)
  ultimately
  have "wf {(x, y). cancels_to_1 y x}"
    by(rule wf_subset)
  thus ?thesis by (simp add:wfP_def)
qed

text \<open>
The next two lemmas prepare for the proof of confluence. It does not matter in
which order we cancel, we can obtain the same result.
\<close>

lemma canceling_neighbor:
  assumes "cancels_to_1_at i l a" and "cancels_to_1_at (Suc i) l b"
  shows "a = b"
proof-
  from \<open>cancels_to_1_at i l a\<close>
    have "canceling (l ! i) (l ! Suc i)" and "i < length l"
    by (auto simp add: cancels_to_1_at_def)
  
  from \<open>cancels_to_1_at (Suc i) l b\<close>
    have "canceling (l ! Suc i) (l ! Suc (Suc i))" and "Suc (Suc i) < length l"
    by (auto simp add: cancels_to_1_at_def)

  from \<open>canceling (l ! i) (l ! Suc i)\<close> and \<open>canceling (l ! Suc i) (l ! Suc (Suc i))\<close>
    have "l ! i = l ! Suc (Suc i)" by (rule cancel_cancel)

  from \<open>cancels_to_1_at (Suc i) l b\<close>
    have "b = take (Suc i) l @ drop (Suc (Suc (Suc i))) l"
    by (simp add: cancels_to_1_at_def cancel_at_def)
  also from \<open>i < length l\<close>
  have "\<dots> = take i l @ [l ! i] @ drop (Suc (Suc (Suc i))) l"
    by(auto simp add: take_Suc_conv_app_nth)
  also from \<open>l ! i = l ! Suc (Suc i)\<close>
  have "\<dots> = take i l @ [l ! Suc (Suc i)] @ drop (Suc (Suc (Suc i))) l"
    by simp
  also from \<open>Suc (Suc i) < length l\<close>
  have "\<dots> = take i l @ drop (Suc (Suc i)) l"
    by (simp add: Cons_nth_drop_Suc)
  also from \<open>cancels_to_1_at i l a\<close> have "\<dots> = a"
    by (simp add: cancels_to_1_at_def cancel_at_def)
  finally show "a = b" by(rule sym)
qed

lemma canceling_indep:
  assumes "cancels_to_1_at i l a" and "cancels_to_1_at j l b" and "j > Suc i"
  obtains c where "cancels_to_1_at (j - 2) a c" and "cancels_to_1_at i b c"
proof(atomize_elim)
  from \<open>cancels_to_1_at i l a\<close>
    have "Suc i < length l"
     and "canceling (l ! i) (l ! Suc i)"
     and "a = cancel_at i l"
     and "length a = length l - 2"
     and "min (length l) i = i"
    by (auto simp add:cancels_to_1_at_def)
  from \<open>cancels_to_1_at j l b\<close>
    have "Suc j < length l"
     and "canceling (l ! j) (l ! Suc j)"
     and "b = cancel_at j l"
     and "length b = length l - 2"
    by (auto simp add:cancels_to_1_at_def)

  let ?c = "cancel_at (j - 2) a"
  from \<open>j > Suc i\<close>
  have "Suc (Suc (j - 2)) = j"
    and "Suc (Suc (Suc j - 2)) = Suc j"
    by auto
  with \<open>min (length l) i = i\<close> and \<open>j > Suc i\<close> and \<open>Suc j < length l\<close>
  have "(l ! j) = (cancel_at i l ! (j - 2))"
    and "(l ! (Suc j)) = (cancel_at i l ! Suc (j - 2))"
    by(auto simp add:cancel_at_def simp add:nth_append)
  
  with \<open>cancels_to_1_at i l a\<close>
    and \<open>cancels_to_1_at j l b\<close>
  have "canceling (a ! (j - 2)) (a ! Suc (j - 2))"
    by(auto simp add:cancels_to_1_at_def)
  
  with \<open>j > Suc i\<close> and \<open>Suc j < length l\<close> and \<open>length a = length l - 2\<close>
  have "cancels_to_1_at (j - 2) a ?c" by (auto simp add: cancels_to_1_at_def)

  from \<open>length b = length l - 2\<close> and \<open>j > Suc i\<close> and \<open>Suc j < length l\<close>
  have "Suc i < length b" by auto
  
  moreover from \<open>b = cancel_at j l\<close> and \<open>j > Suc i\<close> and \<open>Suc i < length l\<close>
  have "(b ! i) = (l ! i)" and "(b ! Suc i) = (l ! Suc i)"
    by (auto simp add:cancel_at_def nth_append)
  with \<open>canceling (l ! i) (l ! Suc i)\<close>
  have "canceling (b ! i) (b ! Suc i)" by simp
  
  moreover from \<open>j > Suc i\<close> and \<open>Suc j < length l\<close>
  have "min i j = i"
    and "min (j - 2) i = i"
    and "min (length l) j = j"
    and "min (length l) i = i"
    and "Suc (Suc (j - 2)) = j"
    by auto
  with \<open>a = cancel_at i l\<close> and \<open>b = cancel_at j l\<close> and \<open>Suc (Suc (j - 2)) = j\<close>
  have "cancel_at (j - 2) a = cancel_at i b"
    by (auto simp add:cancel_at_def take_drop)
  
  ultimately have "cancels_to_1_at i b (cancel_at (j - 2) a)"
    by (auto simp add:cancels_to_1_at_def)

  with \<open>cancels_to_1_at (j - 2) a ?c\<close>
  show "\<exists>c. cancels_to_1_at (j - 2) a c \<and> cancels_to_1_at i b c" by blast
qed

text \<open>This is the confluence lemma\<close>
lemma confluent_cancels_to_1: "confluent cancels_to_1"
proof(rule lconfluent_confluent)
  show "wfP cancels_to_1\<inverse>\<inverse>" by (rule canceling_terminates)
next
  fix a b c
  assume "cancels_to_1 a b"
  then obtain i where "cancels_to_1_at i a b"
    by(simp add: cancels_to_1_def)(erule exE)
  assume "cancels_to_1 a c"
  then obtain j where "cancels_to_1_at j a c"
    by(simp add: cancels_to_1_def)(erule exE)

  show "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d"
  proof (cases "i=j")
    assume "i=j"
    from \<open>cancels_to_1_at i a b\<close>
      have "b = cancel_at i a" by (simp add:cancels_to_1_at_def)
    moreover from \<open>i=j\<close>
      have "\<dots> = cancel_at j a" by (clarify)
    moreover from \<open>cancels_to_1_at j a c\<close>
      have "\<dots> = c" by (simp add:cancels_to_1_at_def)
    ultimately have "b = c" by (simp)
    hence "cancels_to_1\<^sup>*\<^sup>* b b"
      and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
    thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
  next 
    assume "i \<noteq> j"
    show ?thesis
    proof (cases "j = Suc i")
      assume "j = Suc i"
        with \<open>cancels_to_1_at i a b\<close> and \<open>cancels_to_1_at j a c\<close>
        have "b = c" by (auto elim: canceling_neighbor)
      hence "cancels_to_1\<^sup>*\<^sup>* b b"
        and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
      thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
    next
      assume "j \<noteq> Suc i"
      show ?thesis
      proof (cases "i = Suc j")
        assume "i = Suc j"
          with \<open>cancels_to_1_at i a b\<close> and \<open>cancels_to_1_at j a c\<close>
          have "c = b" by (auto elim: canceling_neighbor)
        hence "cancels_to_1\<^sup>*\<^sup>* b b"
          and "cancels_to_1\<^sup>*\<^sup>* c b" by auto
        thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by blast
      next
        assume "i \<noteq> Suc j"
        show ?thesis
        proof (cases "i < j")
          assume "i < j"
            with \<open>j \<noteq> Suc i\<close> have "Suc i < j" by auto
          with \<open>cancels_to_1_at i a b\<close> and \<open>cancels_to_1_at j a c\<close>
          obtain d where "cancels_to_1_at (j - 2) b d" and "cancels_to_1_at i c d"
            by(erule canceling_indep)
          hence "cancels_to_1 b d" and "cancels_to_1 c d" 
            by (auto simp add:cancels_to_1_def)
          thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by (auto)
        next
          assume "\<not> i < j"
          with \<open>j \<noteq> Suc i\<close> and \<open>i \<noteq> j\<close> and \<open>i \<noteq> Suc j\<close> have "Suc j < i" by auto
          with \<open>cancels_to_1_at i a b\<close> and \<open>cancels_to_1_at j a c\<close>
          obtain d where "cancels_to_1_at (i - 2) c d" and "cancels_to_1_at j b d"
            by -(erule canceling_indep)
          hence "cancels_to_1 b d" and "cancels_to_1 c d" 
            by (auto simp add:cancels_to_1_def)
          thus "\<exists>d. cancels_to_1\<^sup>*\<^sup>* b d \<and> cancels_to_1\<^sup>*\<^sup>* c d" by (auto)
        qed
      qed
    qed
  qed
qed

text \<open>
And finally, we show that there exists a unique normal form for each word.
\<close>

(*
lemma inv_rtrcl: "R^**^--1 = R^--1^**" (* Did I overlook this in the standard libs? *)
by (auto simp add:fun_eq_iff intro: dest:rtranclp_converseD intro:rtranclp_converseI)
*)
lemma norm_form_uniq:
  assumes "cancels_to a b"
      and "cancels_to a c"
      and "canceled b"
      and "canceled c"
  shows "b = c"
proof-
  have "confluent cancels_to_1" by (rule confluent_cancels_to_1)
  moreover 
  from \<open>cancels_to a b\<close> have "cancels_to_1^** a b" by (simp add: cancels_to_def)
  moreover
  from \<open>cancels_to a c\<close> have "cancels_to_1^** a c" by (simp add: cancels_to_def)
  moreover
  from \<open>canceled b\<close> have "\<not> Domainp cancels_to_1 b" by (simp add: canceled_def)
  moreover
  from \<open>canceled c\<close> have "\<not> Domainp cancels_to_1 c" by (simp add: canceled_def)
  ultimately
  show "b = c"
    by (rule confluent_unique_normal_form)
qed

subsubsection \<open>Some properties of cancelation\<close>

text \<open>
Distributivity rules of cancelation and \<open>append\<close>.
\<close>

lemma cancel_to_1_append:
  assumes "cancels_to_1 a b"
  shows "cancels_to_1 (l@a@l') (l@b@l')"
proof-
  from \<open>cancels_to_1 a b\<close> obtain i where "cancels_to_1_at i a b"
    by(simp add: cancels_to_1_def)(erule exE)
  hence "cancels_to_1_at (length l + i) (l@a@l') (l@b@l')"
    by (auto simp add:cancels_to_1_at_def nth_append cancel_at_def)
  thus "cancels_to_1 (l@a@l') (l@b@l')"
    by (auto simp add: cancels_to_1_def)
qed

lemma cancel_to_append:
  assumes "cancels_to a b"
  shows "cancels_to (l@a@l') (l@b@l')"
using assms
unfolding cancels_to_def
proof(induct)
  case base show ?case by (simp add:cancels_to_def)
next
  case (step b c)
  from \<open>cancels_to_1 b c\<close>
  have "cancels_to_1 (l @ b @ l') (l @ c @ l')" by (rule cancel_to_1_append)
  with \<open>cancels_to_1^** (l @ a @ l') (l @ b @ l')\<close> show ?case
    by (auto simp add:cancels_to_def)
qed

lemma cancels_to_append2:
  assumes "cancels_to a a'"
      and "cancels_to b b'"
  shows "cancels_to (a@b) (a'@b')"
using \<open>cancels_to a a'\<close>
unfolding cancels_to_def
proof(induct)
  case base
  from \<open>cancels_to b b'\<close> have "cancels_to (a@b@[]) (a@b'@[])"
    by (rule cancel_to_append)
  thus ?case unfolding cancels_to_def by simp
next
  case (step ba c)
  from \<open>cancels_to_1 ba c\<close> have "cancels_to_1 ([]@ba@b') ([]@c@b')"
    by(rule cancel_to_1_append)
  with \<open>cancels_to_1^** (a @ b) (ba @ b')\<close>
  show ?case unfolding cancels_to_def by simp
qed

text \<open>
The empty list is canceled, a one letter word is canceled and a word is
trivially cancled from itself.
\<close>

lemma empty_canceled[simp]: "canceled []"
by(auto simp add: canceled_def cancels_to_1_def cancels_to_1_at_def)

lemma singleton_canceled[simp]: "canceled [a]"
by(auto simp add: canceled_def cancels_to_1_def cancels_to_1_at_def)

lemma cons_canceled:
  assumes "canceled (a#x)"
  shows   "canceled x"
proof(rule ccontr)
  assume "\<not> canceled x"
  hence "Domainp cancels_to_1 x" by (simp add:canceled_def)
  then obtain x' where "cancels_to_1 x x'" by auto
  then obtain xs1 x1 x2 xs2
    where x: "x = xs1 @ x1 # x2 # xs2"
    and   "canceling x1 x2" by (rule cancels_to_1_unfold)
  hence "cancels_to_1 ((a#xs1) @ x1 # x2 # xs2) ( (a#xs1) @ xs2)"
    by (auto intro:cancels_to_1_fold simp del:append_Cons)
  with x
  have "cancels_to_1 (a#x) (a#xs1 @ xs2)"
    by simp
  hence "\<not> canceled (a#x)" by (auto simp add:canceled_def)
  thus False using \<open>canceled (a#x)\<close> by contradiction
qed

lemma cancels_to_self[simp]: "cancels_to l l"
by (simp add:cancels_to_def)

subsection \<open>Definition of normalization\<close>

text \<open>
Using the THE construct, we can define the normalization function
\<open>normalize\<close> as the unique fully cancled word that the argument cancels
to.
\<close>

definition normalize :: "'a word_g_i \<Rightarrow> 'a word_g_i"
where "normalize l = (THE l'. cancels_to l l' \<and> canceled l')"

text \<open>
Some obvious properties of the normalize function, and other useful lemmas.
\<close>

lemma
  shows normalized_canceled[simp]: "canceled (normalize l)"
  and   normalized_cancels_to[simp]: "cancels_to l (normalize l)"
proof-
  let ?Q = "{l'. cancels_to_1^** l l'}"
  have "l \<in> ?Q" by (auto) hence "\<exists>x. x \<in> ?Q" by (rule exI)

  have "wfP cancels_to_1^--1"
    by (rule canceling_terminates)
  hence "\<forall>Q. (\<exists>x. x \<in> Q) \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. cancels_to_1 z y \<longrightarrow> y \<notin> Q)"
    by (simp add:wfP_eq_minimal)
  hence "(\<exists>x. x \<in> ?Q) \<longrightarrow> (\<exists>z\<in>?Q. \<forall>y. cancels_to_1 z y \<longrightarrow> y \<notin> ?Q)"
    by (erule_tac x="?Q" in allE)
  then obtain l' where "l' \<in> ?Q" and minimal: "\<And>y. cancels_to_1 l' y \<Longrightarrow> y \<notin> ?Q"
    by auto
  
  from \<open>l' \<in> ?Q\<close> have "cancels_to l l'" by (auto simp add: cancels_to_def)

  have "canceled l'"
  proof(rule ccontr)
    assume "\<not> canceled l'" hence "Domainp cancels_to_1 l'" by (simp add: canceled_def)
    then obtain y where "cancels_to_1 l' y" by auto
    with \<open>cancels_to l l'\<close> have "cancels_to l y" by (auto simp add: cancels_to_def)
    from \<open>cancels_to_1 l' y\<close> have "y \<notin> ?Q" by(rule minimal)
    hence "\<not> cancels_to_1^** l y" by auto
    hence "\<not> cancels_to l y" by (simp add: cancels_to_def)
    with \<open>cancels_to l y\<close> show False by contradiction
  qed

  from \<open>cancels_to l l'\<close> and \<open>canceled l'\<close>
  have "cancels_to l l' \<and> canceled l'" by simp 
  hence "cancels_to l (normalize l) \<and> canceled (normalize l)"
    unfolding normalize_def
  proof (rule theI)
    fix l'a
    assume "cancels_to l l'a \<and> canceled l'a"
    thus "l'a = l'" using \<open>cancels_to l l' \<and> canceled l'\<close> by (auto elim:norm_form_uniq)
  qed
  thus "canceled (normalize l)" and "cancels_to l (normalize l)" by auto
qed

lemma normalize_discover:
  assumes "canceled l'"
      and "cancels_to l l'"
  shows "normalize l = l'"
proof-
  from \<open>canceled l'\<close> and \<open>cancels_to l l'\<close>
  have "cancels_to l l' \<and> canceled l'" by auto
  thus ?thesis unfolding normalize_def by (auto elim:norm_form_uniq)
qed

text \<open>Words, related by cancelation, have the same normal form.\<close>

lemma normalize_canceled[simp]:
  assumes "cancels_to l l'"
  shows   "normalize l = normalize l'"
proof(rule normalize_discover)
  show "canceled (normalize l')" by (rule normalized_canceled)
next
  have "cancels_to l' (normalize l')" by (rule normalized_cancels_to)
  with \<open>cancels_to l l'\<close>
  show "cancels_to l (normalize l')" by (rule cancels_to_trans)
qed

text \<open>Normalization is idempotent.\<close>

lemma normalize_idemp[simp]:
  assumes "canceled l"
  shows "normalize l = l"
using assms
by(rule normalize_discover)(rule cancels_to_self)

text \<open>
This lemma lifts the distributivity results from above to the normalize
function.
\<close>

lemma normalize_append_cancel_to:
  assumes "cancels_to l1 l1'"
  and     "cancels_to l2 l2'"
  shows "normalize (l1 @ l2) = normalize (l1' @ l2')"
proof(rule normalize_discover)
  show "canceled (normalize (l1' @ l2'))" by (rule normalized_canceled)
next
  from \<open>cancels_to l1 l1'\<close> and \<open>cancels_to l2 l2'\<close>
  have "cancels_to (l1 @ l2) (l1' @ l2')" by (rule cancels_to_append2)
  also
  have "cancels_to (l1' @ l2') (normalize (l1' @ l2'))" by (rule normalized_cancels_to)
  finally
  show "cancels_to (l1 @ l2) (normalize (l1' @ l2'))".
qed

subsection \<open>Normalization preserves generators\<close>

text \<open>
Somewhat obvious, but still required to formalize Free Groups, is the fact that
canceling a word of generators of a specific set (and their inverses) results
in a word in generators from that set.
\<close>

lemma cancels_to_1_preserves_generators:
  assumes "cancels_to_1 l l'"
      and "l \<in> lists (UNIV \<times> gens)"
  shows "l' \<in> lists (UNIV \<times> gens)"
proof-
  from assms obtain i where "l' = cancel_at i l" 
    unfolding cancels_to_1_def and cancels_to_1_at_def by auto
  hence "l' = take i l @ drop (2 + i) l" unfolding cancel_at_def .
  hence "set l' = set (take i l @ drop (2 + i) l)" by simp
  moreover
  have "\<dots> = set (take i l @ drop (2 + i) l)" by auto
  moreover
  have "\<dots> \<subseteq> set (take i l) \<union> set (drop (2 + i) l)" by auto
  moreover
  have "\<dots> \<subseteq> set l" by (auto dest: in_set_takeD in_set_dropD)
  ultimately
  have "set l' \<subseteq> set l" by simp
  thus ?thesis using assms(2) by auto
qed

lemma cancels_to_preserves_generators:
  assumes "cancels_to l l'"
      and "l \<in> lists (UNIV \<times> gens)"
  shows "l' \<in> lists (UNIV \<times> gens)"
using assms unfolding cancels_to_def by (induct, auto dest:cancels_to_1_preserves_generators)

lemma normalize_preserves_generators:
  assumes "l \<in> lists (UNIV \<times> gens)"
    shows "normalize l \<in> lists (UNIV \<times> gens)"
proof-
  have "cancels_to l (normalize l)" by simp
  thus ?thesis using assms by(rule cancels_to_preserves_generators)
qed

text \<open>
Two simplification lemmas about lists.
\<close>

lemma empty_in_lists[simp]:
  "[] \<in> lists A" by auto

lemma lists_empty[simp]: "lists {} = {[]}"
  by auto

subsection \<open>Normalization and renaming generators\<close>

text \<open>
Renaming the generators, i.e. mapping them through an injective function, commutes
with normalization. Similarly, replacing generators by their inverses and
vica-versa commutes with normalization. Both operations are similar enough to be
handled at once here.
\<close>

lemma rename_gens_cancel_at: "cancel_at i (map f l) = map f (cancel_at i l)"
unfolding "cancel_at_def" by (auto simp add:take_map drop_map)

lemma rename_gens_cancels_to_1:
  assumes "inj f"
      and "cancels_to_1 l l'"
    shows "cancels_to_1 (map (map_prod f g) l) (map (map_prod f g) l')"
proof-
  from \<open>cancels_to_1 l l'\<close>
  obtain ls1 l1 l2 ls2
    where "l = ls1 @ l1 # l2 # ls2"
      and "l' = ls1 @ ls2"
      and "canceling l1 l2"
  by (rule cancels_to_1_unfold)

  from \<open>canceling l1 l2\<close>
  have "fst l1 \<noteq> fst l2" and "snd l1 = snd l2"
    unfolding canceling_def by auto
  from \<open>fst l1 \<noteq> fst l2\<close> and \<open>inj f\<close>
  have "f (fst l1) \<noteq> f (fst l2)" by(auto dest!:inj_on_contraD)
  hence "fst (map_prod f g l1) \<noteq> fst (map_prod f g l2)" by auto
  moreover
  from \<open>snd l1 = snd l2\<close>
  have "snd (map_prod f g l1) = snd (map_prod f g l2)" by auto
  ultimately
  have "canceling (map_prod f g (l1)) (map_prod f g (l2))"
    unfolding canceling_def by auto
  hence "cancels_to_1 (map (map_prod f g) ls1 @ map_prod f g l1 # map_prod f g l2 # map (map_prod f g) ls2) (map (map_prod f g) ls1 @ map (map_prod f g) ls2)"
   by(rule cancels_to_1_fold)
  with \<open>l = ls1 @ l1 # l2 # ls2\<close> and \<open>l' = ls1 @ ls2\<close>
  show "cancels_to_1 (map (map_prod f g) l) (map (map_prod f g) l')"
   by simp
qed

lemma rename_gens_cancels_to:
  assumes "inj f"
      and "cancels_to l l'"
    shows "cancels_to (map (map_prod f g) l) (map (map_prod f g) l')"
using \<open>cancels_to l l'\<close>
unfolding cancels_to_def
proof(induct rule:rtranclp_induct)
  case (step x z)
    from \<open>cancels_to_1 x z\<close> and \<open>inj f\<close>
    have "cancels_to_1 (map (map_prod f g) x) (map (map_prod f g) z)"
      by -(rule rename_gens_cancels_to_1)
    with \<open>cancels_to_1^** (map (map_prod f g) l) (map (map_prod f g) x)\<close>
    show "cancels_to_1^** (map (map_prod f g) l) (map (map_prod f g) z)" by auto
qed(auto)

   
lemma rename_gens_canceled:
  assumes "inj_on g (snd`set l)"
      and "canceled l"
  shows "canceled (map (map_prod f g) l)"
unfolding canceled_def
proof
  (* This statement is needed explicitly later in this proof *)
  have different_images: "\<And> f a b. f a \<noteq> f b \<Longrightarrow> a \<noteq> b" by auto

  assume "Domainp cancels_to_1 (map (map_prod f g) l)"
  then obtain l' where "cancels_to_1 (map (map_prod f g) l) l'" by auto
  then obtain i where "Suc i < length l"
    and "canceling (map (map_prod f g) l ! i) (map (map_prod f g) l ! Suc i)"
    by(auto simp add:cancels_to_1_def cancels_to_1_at_def)
  hence "f (fst (l ! i)) \<noteq> f (fst (l ! Suc i))"
    and "g (snd (l ! i)) = g (snd (l ! Suc i))"
    by(auto simp add:canceling_def)
  from \<open>f (fst (l ! i)) \<noteq> f (fst (l ! Suc i))\<close>
  have "fst (l ! i) \<noteq> fst (l ! Suc i)" by -(erule different_images)
  moreover
  from \<open>Suc i < length l\<close>
  have "snd (l ! i) \<in> snd ` set l" and "snd (l ! Suc i) \<in> snd ` set l" by auto
  with \<open>g (snd (l ! i)) = g (snd (l ! Suc i))\<close>
  have "snd (l ! i) = snd (l ! Suc i)" 
    using \<open>inj_on g (image snd (set l))\<close>
    by (auto dest: inj_onD)
  ultimately
  have "canceling (l ! i) (l ! Suc i)" unfolding canceling_def by simp
  with \<open>Suc i < length l\<close>
  have "cancels_to_1_at i l (cancel_at i l)" 
    unfolding cancels_to_1_at_def by auto
  hence "cancels_to_1 l (cancel_at i l)"
    unfolding cancels_to_1_def by auto
  hence "\<not>canceled l"
    unfolding canceled_def by auto
  with \<open>canceled l\<close> show False by contradiction
qed

lemma rename_gens_normalize:
  assumes "inj f"
  and "inj_on g (snd ` set l)"
  shows "normalize (map (map_prod f g) l) = map (map_prod f g) (normalize l)"
proof(rule normalize_discover)
  from \<open>inj_on g (image snd (set l))\<close>
  have "inj_on g (image snd (set (normalize l)))"
  proof (rule subset_inj_on)
    
    have UNIV_snd: "\<And>A. A \<subseteq> UNIV \<times> snd ` A"
      proof fix A and x::"'c\<times>'d" assume "x\<in>A"
        hence "(fst x,snd x)\<in> (UNIV \<times> snd ` A)"
          by -(rule, auto)
        thus "x\<in> (UNIV \<times> snd ` A)" by simp
      qed

    have "l \<in> lists (set l)" by auto
    hence "l \<in> lists (UNIV \<times> snd ` set l)"
      by (rule subsetD[OF lists_mono[OF UNIV_snd], of l "set l"])
    hence "normalize l \<in> lists (UNIV \<times> snd ` set l)"
      by (rule normalize_preserves_generators[of _ "snd ` set l"])
    thus "snd ` set (normalize l) \<subseteq> snd ` set l"
      by (auto simp add: lists_eq_set)
   qed
  thus "canceled (map (map_prod f g) (normalize l))" by(rule rename_gens_canceled,simp)
next
  from \<open>inj f\<close>
  show "cancels_to (map (map_prod f g) l) (map (map_prod f g) (normalize l))"
    by (rule rename_gens_cancels_to, simp)
qed

end
