(*<*)
theory Basis
imports
  "HOL-Library.While_Combinator"
begin

(*>*)
section\<open> Point-free notation \<close>

text\<open>

We adopt point-free notation for our assertions over program states.

\<close>

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_not :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("\<^bold>\<not>") where
  "\<^bold>\<not>a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<and>" 35) where
  "a \<^bold>\<and> b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_implies :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "\<^bold>\<longrightarrow>" 25) where
  "a \<^bold>\<longrightarrow> b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_eq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>=" 40) where
  "a \<^bold>= b \<equiv> \<lambda>s. a s = b s"

abbreviation (input)
  pred_member :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<in>" 40) where
  "a \<^bold>\<in> b \<equiv> \<lambda>s. a s \<in> b s"

abbreviation (input)
  pred_neq :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<noteq>" 40) where
  "a \<^bold>\<noteq> b \<equiv> \<lambda>s. a s \<noteq> b s"

abbreviation (input)
  pred_If :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("(\<^bold>if (_)/ \<^bold>then (_)/ \<^bold>else (_))" [0, 0, 10] 10) where
  "\<^bold>if P \<^bold>then x \<^bold>else y \<equiv> \<lambda>s. if P s then x s else y s"

abbreviation (input)
  pred_less :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold><" 40) where
  "a \<^bold>< b \<equiv> \<lambda>s. a s < b s"

abbreviation (input)
  pred_le :: "('a \<Rightarrow> 'b::ord) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<^bold>\<le>" 40) where
  "a \<^bold>\<le> b \<equiv> \<lambda>s. a s \<le> b s"

abbreviation (input)
  pred_plus :: "('a \<Rightarrow> 'b::plus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>+" 65) where
  "a \<^bold>+ b \<equiv> \<lambda>s. a s + b s"

abbreviation (input)
  pred_minus :: "('a \<Rightarrow> 'b::minus) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "\<^bold>-" 65) where
  "a \<^bold>- b \<equiv> \<lambda>s. a s - b s"

abbreviation (input)
  fun_fanout :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'c" (infix "\<^bold>\<bowtie>" 35) where
  "f \<^bold>\<bowtie> g \<equiv> \<lambda>x. (f x, g x)"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "\<^bold>\<forall>" 10) where
  "\<^bold>\<forall>x. P x \<equiv> \<lambda>s. \<forall>x. P x s"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "\<^bold>\<exists>" 10) where
  "\<^bold>\<exists>x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

section\<open> ``Monoidal'' Hoare logic \<close>

text\<open>

In the absence of a general-purpose development of Hoare Logic for
total correctness in Isabelle/HOL\footnote{At the time of writing the
distribution contains several for partial correctness, and one for
total correctness over a language with restricted expressions.  SIMPL
(@{cite "DBLP:journals/afp/Schirmer08"}) is overkill for our present
purposes.}, we adopt the following syntactic contrivance that eases
making multiple assertions about function results. ``Programs''
consist of the state-transformer semantics of statements.

\<close>

definition valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>") where
  "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> Q (c s)"

notation (input) id ("SKIP")
notation fcomp (infixl ";;" 60)

named_theorems wp_intro "weakest precondition intro rules"

lemma seqI[wp_intro]:
  assumes "\<lbrace>Q\<rbrace> d \<lbrace>R\<rbrace>"
  assumes "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> c ;; d \<lbrace>R\<rbrace>"
using assms by (simp add: valid_def)

lemma iteI[wp_intro]:
  assumes "\<lbrace>P'\<rbrace> x \<lbrace>Q\<rbrace>"
  assumes "\<lbrace>P''\<rbrace> y \<lbrace>Q\<rbrace>"
  shows "\<lbrace>\<^bold>if b \<^bold>then P' \<^bold>else P''\<rbrace> \<^bold>if b \<^bold>then x \<^bold>else y \<lbrace>Q\<rbrace>"
using assms by (simp add: valid_def)

lemma assignI[wp_intro]:
  shows "\<lbrace>Q \<circ> f\<rbrace> f \<lbrace>Q\<rbrace>"
by (simp add: valid_def)

lemma whileI:
  assumes "\<lbrace>I'\<rbrace> c \<lbrace>I\<rbrace>"
  assumes "\<And>s. I s \<Longrightarrow> if b s then I' s else Q s"
  assumes "wf r"
  assumes "\<And>s. \<lbrakk> I s; b s \<rbrakk> \<Longrightarrow> (c s, s) \<in> r"
  shows "\<lbrace>I\<rbrace> while b c \<lbrace>Q\<rbrace>"
using assms by (simp add: while_rule valid_def)

lemma hoare_pre:
  assumes "\<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes "\<And>s. P s \<Longrightarrow> R s"
  shows "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
using assms by (simp add: valid_def)

lemma hoare_post_imp:
  assumes "\<lbrace>P\<rbrace> a \<lbrace>Q\<rbrace>"
  assumes "\<And>s. Q s \<Longrightarrow> R s"
  shows "\<lbrace>P\<rbrace> a \<lbrace>R\<rbrace>"
using assms by (simp add: valid_def)

text\<open>

Note that the @{thm[source] assignI} rule applies to all state
transformers, and therefore the order in which we attempt to use the
@{thm[source] wp_intro} rules matters.

\<close>


section\<open> Properties of iterated functions on finite sets \<close>

text\<open>

We begin by fixing the @{term "f"} and @{term "x0"} under
consideration in a locale, and establishing Knuth's properties.

The sequence is modelled as a function \<open>seq :: nat
\<Rightarrow> 'a\<close> in the obvious way.

\<close>

locale fx0 =
  fixes f :: "'a::finite \<Rightarrow> 'a"
  fixes x0 :: "'a"
begin

definition seq' :: "'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "seq' x i \<equiv> (f ^^ i) x"

abbreviation "seq \<equiv> seq' x0"
(*<*)

declare (in -) fx0.seq'_def[code]

lemma seq'_simps[simp]:
  "seq' x 0 = x"
  "seq' x (Suc i) = f (seq' x i)"
  "seq' (f x) i \<in> range (seq' x)"
by (auto intro: range_eqI[where x="Suc i"] simp: seq'_def funpow_swap1)

lemma seq_inj:
  "\<lbrakk> seq' x i = seq' x j; p = i + n; q = j + n \<rbrakk> \<Longrightarrow> seq' x p = seq' x q"
apply hypsubst_thin
by (induct n) simp_all
(*>*)
text\<open>

The parameters \<open>lambda\<close> and \<open>mu\<close> must exist by the
pigeonhole principle.

\<close>

lemma seq'_not_inj_on_card_UNIV:
  shows "\<not>inj_on (seq' x) {0 .. card (UNIV::'a set)}"
by (simp add: inj_on_iff_eq_card)
   (metis UNIV_I card_mono finite lessI not_less subsetI)

definition properties :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "properties lambda mu \<equiv>
     0 < lambda
   \<and> inj_on seq {0 ..< mu + lambda}
   \<and> (\<forall>i\<ge>mu. \<forall>j. seq (i + j * lambda) = seq i)"

lemma properties_existence:
  obtains lambda mu
  where "properties lambda mu"
proof -
  obtain l where l: "inj_on seq {0..l} \<and> \<not>inj_on seq {0..Suc l}"
    using ex_least_nat_less[where P="\<lambda>ub. \<not>inj_on seq {0..ub}" and n="card (UNIV :: 'a set)"]
          seq'_not_inj_on_card_UNIV
    by fastforce
  moreover
  from l obtain mu where mu: "mu \<le> l \<and> seq (Suc l) = seq mu"
    by (fastforce simp: atLeastAtMostSuc_conv)
  moreover
  define lambda where "lambda = l - mu + 1"
  have "seq (i + j * lambda) = seq i" if "mu \<le> i" for i j
  using that proof (induct j)
    case (Suc j)
    from l mu have F: "seq (l + j + 1) = seq (mu + j)" for j
      by (fastforce elim: seq_inj)
    from mu Suc F[where j="i + j * lambda - mu"] show ?case
      by (simp add: lambda_def field_simps)
  qed simp
  ultimately have "properties lambda mu"
    by (auto simp: properties_def lambda_def atLeastLessThanSuc_atLeastAtMost)
  then show thesis ..
qed

end

text\<open>

To ease further reasoning, we define a new locale that fixes @{term
"lambda"} and @{term "mu"}, and assume these properties hold. We then
derive further rules that are easy to apply.

\<close>

locale properties = fx0 +
  fixes lambda mu :: "nat"
  assumes P: "properties lambda mu"
begin

lemma properties_lambda_gt_0:
  shows "0 < lambda"
using P by (simp add: properties_def)

lemma properties_loop:
  assumes "mu \<le> i"
  shows "seq (i + j * lambda) = seq i"
using P assms by (simp add: properties_def)

lemma properties_mod_lambda:
  assumes "mu \<le> i"
  shows "seq i = seq (mu + (i - mu) mod lambda)"
using properties_loop[where i="mu + (i - mu) mod lambda" and j="(i - mu) div lambda"] assms
by simp

lemma properties_distinct:
  assumes "j \<in> {0 <..< lambda}"
  shows "seq (i + j) \<noteq> seq i"
proof(cases "mu \<le> i")
  case True
  from assms have A: "(i + j) mod lambda \<noteq> i mod lambda" for i
    using nat_mod_eq_lemma by fastforce
  from \<open>mu \<le> i\<close>
  have "seq (i + j) = seq (mu + (i + j - mu) mod lambda)"
       "seq i = seq (mu + (i - mu) mod lambda)"
    by (auto intro: properties_mod_lambda)
  with P \<open>mu \<le> i\<close> assms A[where i="i-mu"] show ?thesis
    by (clarsimp simp: properties_def inj_on_eq_iff)
next
  case False with P assms show ?thesis
    by (clarsimp simp: properties_def inj_on_eq_iff)
qed

lemma properties_distinct_contrapos:
  assumes "seq (i + j) = seq i"
  shows "j \<notin> {0 <..< lambda}"
using assms by (rule contrapos_pp) (simp add: properties_distinct)

lemma properties_loops_ge_mu:
  assumes "seq (i + j) = seq i"
  assumes "0 < j"
  shows "mu \<le> i"
proof(rule classical)
  assume X: "\<not>?thesis" show ?thesis
  proof(cases "mu \<le> i + j")
    case True with P X assms show ?thesis
      by (fastforce simp: properties_def inj_on_eq_iff
                    dest: properties_mod_lambda)
  next
    case False with P assms show ?thesis
      by (fastforce simp add: properties_def inj_on_eq_iff)
  qed
qed

end
(*<*)

end
(*>*)
