(*
  File:      Epistemic_Logic.thy
  Author:    Asta Halkjær From

  This work is a formalization of epistemic logic with countably many agents.
  It includes proofs of soundness and completeness for the axiom system K.
  The completeness proof is based on the textbook "Reasoning About Knowledge"
  by Fagin, Halpern, Moses and Vardi (MIT Press 1995).
*)

theory Epistemic_Logic imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

type_synonym id = string

datatype 'i fm
  = FF ("\<^bold>\<bottom>")
  | Pro id
  | Dis \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<or>" 30)
  | Con \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<and>" 35)
  | Imp \<open>'i fm\<close> \<open>'i fm\<close> (infixr "\<^bold>\<longrightarrow>" 25)
  | K 'i \<open>'i fm\<close>

abbreviation TT ("\<^bold>\<top>") where
  \<open>TT \<equiv> \<^bold>\<bottom> \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

abbreviation Neg ("\<^bold>\<not> _" [40] 40) where
  \<open>Neg p \<equiv> p \<^bold>\<longrightarrow> \<^bold>\<bottom>\<close>

section \<open>Semantics\<close>

datatype ('i, 's) kripke = Kripke (\<pi>: \<open>'s \<Rightarrow> id \<Rightarrow> bool\<close>) (\<K>: \<open>'i \<Rightarrow> 's \<Rightarrow> 's set\<close>)

primrec semantics :: \<open>('i, 's) kripke \<Rightarrow> 's \<Rightarrow> 'i fm \<Rightarrow> bool\<close>
  ("_, _ \<Turnstile> _" [50,50] 50) where
  \<open>(_, _ \<Turnstile> \<^bold>\<bottom>) = False\<close>
| \<open>(M, s \<Turnstile> Pro i) = \<pi> M s i\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<or> q)) = ((M, s \<Turnstile> p) \<or> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<and> q)) = ((M, s \<Turnstile> p) \<and> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> (p \<^bold>\<longrightarrow> q)) = ((M, s \<Turnstile> p) \<longrightarrow> (M, s \<Turnstile> q))\<close>
| \<open>(M, s \<Turnstile> K i p) = (\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p)\<close>

section \<open>Utility\<close>

abbreviation reflexive :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>i s. s \<in> \<K> M i s\<close>

abbreviation symmetric :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>i s t. t \<in> \<K> M i s \<longleftrightarrow> s \<in> \<K> M i t\<close>

abbreviation transitive :: \<open>('i, 's) kripke \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>i s t u. t \<in> \<K> M i s \<and> u \<in> \<K> M i t \<longrightarrow> u \<in> \<K> M i s\<close>

lemma Imp_intro: \<open>(M, s \<Turnstile> p \<Longrightarrow> M, s \<Turnstile> q) \<Longrightarrow> M, s \<Turnstile> Imp p q\<close>
  by simp

section \<open>S5 Axioms\<close>

theorem distribution: \<open>M, s \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
proof (rule Imp_intro)
  assume \<open>M, s \<Turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q))\<close>
  then have \<open>M, s \<Turnstile> K i p\<close> \<open>M, s \<Turnstile> K i (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close> \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    by simp_all
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> q\<close>
    by simp
  then show \<open>M, s \<Turnstile> K i q\<close>
    by simp
qed

theorem generalization:
  assumes valid: \<open>\<forall>(M :: ('i, 's) kripke) s. M, s \<Turnstile> p\<close>
  shows \<open>(M :: ('i, 's) kripke), s \<Turnstile> K i p\<close>
proof -
  have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    using valid by blast
  then show \<open>M, s \<Turnstile> K i p\<close>
    by simp
qed

theorem truth:
  assumes \<open>reflexive M\<close>
  shows \<open>M, s \<Turnstile> (K i p \<^bold>\<longrightarrow> p)\<close>
proof (rule Imp_intro)
  assume \<open>M, s \<Turnstile> K i p\<close>
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    by simp
  moreover have \<open>s \<in> \<K> M i s\<close>
    using \<open>reflexive M\<close> by blast
  ultimately show \<open>M, s \<Turnstile> p\<close>
    by blast
qed

theorem pos_introspection:
  assumes \<open>transitive M\<close>
  shows \<open>M, s \<Turnstile> (K i p \<^bold>\<longrightarrow> K i (K i p))\<close>
proof (rule Imp_intro)
  assume \<open>M,s \<Turnstile> K i p\<close>
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> p\<close>
    by simp
  then have \<open>\<forall>t \<in> \<K> M i s. \<forall>u \<in> \<K> M i t. M, u \<Turnstile> p\<close>
    using \<open>transitive M\<close> by blast
  then have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> K i p\<close>
    by simp
  then show \<open>M, s \<Turnstile> K i (K i p)\<close>
    by simp
qed

theorem neg_introspection:
  assumes \<open>symmetric M\<close> \<open>transitive M\<close>
  shows \<open>M, s \<Turnstile> (\<^bold>\<not> K i p \<^bold>\<longrightarrow> K i (\<^bold>\<not> K i p))\<close>
proof (rule Imp_intro)
  assume \<open>M,s \<Turnstile> \<^bold>\<not> (K i p)\<close>
  then obtain u where \<open>u \<in> \<K> M i s\<close> \<open>\<not> (M, u \<Turnstile> p)\<close>
    by auto
  moreover have \<open>\<forall>t \<in> \<K> M i s. u \<in> \<K> M i t\<close>
    using \<open>u \<in> \<K> M i s\<close> \<open>symmetric M\<close> \<open>transitive M\<close> by blast
  ultimately have \<open>\<forall>t \<in> \<K> M i s. M, t \<Turnstile> \<^bold>\<not> K i p\<close>
    by auto
  then show \<open>M, s \<Turnstile> K i (\<^bold>\<not> K i p)\<close>
    by simp
qed

section \<open>Axiom System K\<close>

primrec eval :: \<open>(id \<Rightarrow> bool) \<Rightarrow> ('i fm \<Rightarrow> bool) \<Rightarrow> 'i fm \<Rightarrow> bool\<close> where
  \<open>eval _ _ \<^bold>\<bottom> = False\<close>
| \<open>eval g _ (Pro i) = g i\<close>
| \<open>eval g h (p \<^bold>\<or> q) = (eval g h p \<or> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<and> q) = (eval g h p \<and> eval g h q)\<close>
| \<open>eval g h (p \<^bold>\<longrightarrow> q) = (eval g h p \<longrightarrow> eval g h q)\<close>
| \<open>eval _ h (K i p) = h (K i p)\<close>

abbreviation \<open>tautology p \<equiv> \<forall>g h. eval g h p\<close>

inductive SystemK :: \<open>'i fm \<Rightarrow> bool\<close> ("\<turnstile> _" [50] 50) where
  A1: \<open>tautology p \<Longrightarrow> \<turnstile> p\<close>
| A2: \<open>\<turnstile> (K i p \<^bold>\<and> K i (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> K i q)\<close>
| R1: \<open>\<turnstile> p \<Longrightarrow> \<turnstile> (p \<^bold>\<longrightarrow> q) \<Longrightarrow> \<turnstile> q\<close>
| R2: \<open>\<turnstile> p \<Longrightarrow> \<turnstile> K i p\<close>

section \<open>Soundness\<close>

lemma eval_semantics: \<open>eval (pi s) (\<lambda>q. Kripke pi r, s \<Turnstile> q) p = (Kripke pi r, s \<Turnstile> p)\<close>
  by (induct p) simp_all

theorem tautology: \<open>tautology p \<Longrightarrow> M, s \<Turnstile> p\<close>
proof -
  assume \<open>tautology p\<close>
  then have \<open>eval (g s) (\<lambda>q. Kripke g r, s \<Turnstile> q) p\<close> for g r
    by simp
  then have \<open>Kripke g r, s \<Turnstile> p\<close> for g r
    using eval_semantics by metis
  then show \<open>M, s \<Turnstile> p\<close>
    by (metis kripke.collapse)
qed

theorem soundness: \<open>\<turnstile> p \<Longrightarrow> M, s \<Turnstile> p\<close>
  by (induct p arbitrary: s rule: SystemK.induct) (simp_all add: tautology)

section \<open>Derived rules\<close>

lemma K_FFI: \<open>\<turnstile> (p \<^bold>\<longrightarrow> (\<^bold>\<not> p) \<^bold>\<longrightarrow> \<^bold>\<bottom>)\<close>
  by (simp add: A1)

primrec conjoin :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> where
  \<open>conjoin [] q = q\<close>
| \<open>conjoin (p # ps) q = (p \<^bold>\<and> conjoin ps q)\<close>

primrec imply :: \<open>'i fm list \<Rightarrow> 'i fm \<Rightarrow> 'i fm\<close> where
  \<open>imply [] q = q\<close>
| \<open>imply (p # ps) q = (p \<^bold>\<longrightarrow> imply ps q)\<close>

lemma K_imply_head: \<open>\<turnstile> imply (p # ps) p\<close>
proof -
  have \<open>tautology (imply (p # ps) p)\<close>
    by (induct ps) simp_all
  then show ?thesis
    using A1 by blast
qed

lemma K_imply_Cons:
  assumes \<open>\<turnstile> imply ps q\<close>
  shows \<open>\<turnstile> imply (p # ps) q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    by simp
  then have \<open>\<turnstile> (imply ps q \<^bold>\<longrightarrow> imply (p # ps) q)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_imply_member: \<open>p \<in> set ps \<Longrightarrow> \<turnstile> imply ps p\<close>
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ps)
  then show ?case
  proof (cases \<open>a = p\<close>)
    case True
    then show ?thesis
      using Cons K_imply_head by blast
  next
    case False
    then show ?thesis
      using Cons K_imply_Cons by simp
  qed
qed

lemma K_right_mp:
  assumes \<open>\<turnstile> imply ps p\<close> \<open>\<turnstile> imply ps (p \<^bold>\<longrightarrow> q)\<close>
  shows \<open>\<turnstile> imply ps q\<close>
proof -
  have \<open>tautology (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    by (induct ps) simp_all
  then have \<open>\<turnstile> (imply ps p \<^bold>\<longrightarrow> imply ps (p \<^bold>\<longrightarrow> q) \<^bold>\<longrightarrow> imply ps q)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma tautology_imply_superset:
  assumes \<open>set ps \<subseteq> set qs\<close>
  shows \<open>tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
proof (rule ccontr)
  assume \<open>\<not> tautology (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
  then obtain g h where \<open>\<not> eval g h (imply ps r \<^bold>\<longrightarrow> imply qs r)\<close>
    by blast
  then have \<open>eval g h (imply ps r)\<close> \<open>\<not> eval g h (imply qs r)\<close>
    by simp_all
  then consider (np) \<open>\<exists>p \<in> set ps. \<not> eval g h p\<close> | (r) \<open>\<forall>p \<in> set ps. eval g h p\<close> \<open>eval g h r\<close>
    by (induct ps) auto
  then show False
  proof cases
    case np
    then have \<open>\<exists>p \<in> set qs. \<not> eval g h p\<close>
      using \<open>set ps \<subseteq> set qs\<close> by blast
    then have \<open>eval g h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (imply qs r)\<close> by blast
  next
    case r
    then have \<open>eval g h (imply qs r)\<close>
      by (induct qs) simp_all
    then show ?thesis
      using \<open>\<not> eval g h (imply qs r)\<close> by blast
  qed
qed

lemma tautology_imply: \<open>tautology q \<Longrightarrow> tautology (imply ps q)\<close>
  by (induct ps) simp_all

theorem K_imply_weaken:
  assumes \<open>\<turnstile> imply ps q\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>\<turnstile> imply ps' q\<close>
proof -
  have \<open>tautology (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using \<open>set ps \<subseteq> set ps'\<close>
  proof (induct ps arbitrary: ps')
    case Nil
    then show ?case
      by (induct ps') simp_all
  next
    case (Cons a G)
    then show ?case
      using tautology_imply_superset by blast
  qed
  then have \<open>\<turnstile> (imply ps q \<^bold>\<longrightarrow> imply ps' q)\<close>
    using A1 by blast
  then show ?thesis
    using \<open>\<turnstile> imply ps q\<close> R1 by blast
qed

lemma imply_append: \<open>imply (ps @ ps') q = imply ps (imply ps' q)\<close>
  by (induct ps) simp_all

lemma K_ImpI:
  assumes \<open>\<turnstile> imply (p # G) q\<close>
  shows \<open>\<turnstile> imply G (p \<^bold>\<longrightarrow> q)\<close>
proof -
  have \<open>set (p # G) \<subseteq> set (G @ [p])\<close>
    by simp
  then have \<open>\<turnstile> imply (G @ [p]) q\<close>
    using assms K_imply_weaken by blast
  then have \<open>\<turnstile> imply G (imply [p] q)\<close>
    using imply_append by metis
  then show ?thesis
    by simp
qed

lemma cut: \<open>\<turnstile> imply G p \<Longrightarrow> \<turnstile> imply (p # G) q \<Longrightarrow> \<turnstile> imply G q\<close>
  using K_ImpI K_right_mp by blast

lemma K_Boole: \<open>\<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom> \<Longrightarrow> \<turnstile> imply G p\<close>
proof -
  assume \<open>\<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>
  then have \<open>\<turnstile> imply G (\<^bold>\<not> \<^bold>\<not> p)\<close>
    using K_ImpI by blast
  moreover have \<open>tautology (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>\<turnstile> (imply G (\<^bold>\<not> \<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  ultimately show ?thesis
    using R1 by blast
qed

lemma K_DisE:
  assumes \<open>\<turnstile> imply (A # G) C\<close> \<open>\<turnstile> imply (B # G) C\<close> \<open>\<turnstile> imply G (A \<^bold>\<or> B)\<close>
  shows \<open>\<turnstile> imply G C\<close>
proof -
  have \<open>tautology (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    by (induct G) auto
  then have \<open>\<turnstile> (imply (A # G) C \<^bold>\<longrightarrow> imply (B # G) C \<^bold>\<longrightarrow> imply G (A \<^bold>\<or> B) \<^bold>\<longrightarrow> imply G C)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_conjoin_imply:
  assumes \<open>\<turnstile> (\<^bold>\<not> conjoin G (\<^bold>\<not> p))\<close>
  shows \<open>\<turnstile> imply G p\<close>
proof -
  have \<open>tautology (\<^bold>\<not> conjoin G (\<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    by (induct G) simp_all
  then have \<open>\<turnstile> (\<^bold>\<not> conjoin G (\<^bold>\<not> p) \<^bold>\<longrightarrow> imply G p)\<close>
    using A1 by blast
  then show ?thesis
    using assms R1 by blast
qed

lemma K_distrib_K_imp:
  assumes \<open>\<turnstile> K i (imply G q)\<close>
  shows \<open>\<turnstile> imply (map (K i) G) (K i q)\<close>
proof -
  have \<open>\<turnstile> (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
  proof (induct G)
    case Nil
    then show ?case
      by (simp add: A1)
  next
    case (Cons a G)
    have \<open>\<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q))\<close>
      by (simp add: A2)
    moreover have
      \<open>\<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> K i (imply G q)) \<^bold>\<longrightarrow>
        (K i (imply G q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>\<turnstile> (K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using Cons R1 by blast
    moreover have
      \<open>\<turnstile> ((K i a \<^bold>\<and> K i (imply (a # G) q) \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)) \<^bold>\<longrightarrow>
        (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q)))\<close>
      by (simp add: A1)
    ultimately have \<open>\<turnstile> (K i (imply (a # G) q) \<^bold>\<longrightarrow> K i a \<^bold>\<longrightarrow> imply (map (K i) G) (K i q))\<close>
      using R1 by blast
    then show ?case
      by simp
  qed
  then show ?thesis
    using assms R1 by blast
qed

section \<open>Consistency\<close>

definition consistency :: \<open>'i fm set set \<Rightarrow> bool\<close> where
  \<open>consistency C \<equiv> \<forall>S \<in> C.
    (\<forall>p. \<not> (Pro p \<in> S \<and> (\<^bold>\<not> Pro p) \<in> S)) \<and>
    \<^bold>\<bottom> \<notin> S \<and>
    (\<forall>Z. (\<^bold>\<not> (\<^bold>\<not> Z)) \<in> S \<longrightarrow> S \<union> {Z} \<in> C) \<and>
    (\<forall>A B. (A \<^bold>\<and> B) \<in> S \<longrightarrow> S \<union> {A, B} \<in> C) \<and>
    (\<forall>A B. (\<^bold>\<not> (A \<^bold>\<or> B)) \<in> S \<longrightarrow> S \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> C) \<and>
    (\<forall>A B. (A \<^bold>\<or> B) \<in> S \<longrightarrow> S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
    (\<forall>A B. (\<^bold>\<not> (A \<^bold>\<and> B)) \<in> S \<longrightarrow> S \<union> {\<^bold>\<not> A} \<in> C \<or> S \<union> {\<^bold>\<not> B} \<in> C) \<and>
    (\<forall>A B. (A \<^bold>\<longrightarrow> B) \<in> S \<longrightarrow> S \<union> {\<^bold>\<not> A} \<in> C \<or> S \<union> {B} \<in> C) \<and>
    (\<forall>A B. (\<^bold>\<not> (A \<^bold>\<longrightarrow> B)) \<in> S \<longrightarrow> S \<union> {A, \<^bold>\<not> B} \<in> C) \<and>
    (\<forall>A. tautology A \<longrightarrow> S \<union> {A} \<in> C) \<and>
    (\<forall>A i. \<not> (K i A \<in> S \<and> (\<^bold>\<not> K i A) \<in> S))\<close>

subsection \<open>Closure under subsets\<close>

definition close :: \<open>'i fm set set \<Rightarrow> 'i fm set set\<close> where
  \<open>close C \<equiv> {S. \<exists>S' \<in> C. S \<subseteq> S'}\<close>

definition subset_closed :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>subset_closed C \<equiv> (\<forall>S' \<in> C. \<forall>S. S \<subseteq> S' \<longrightarrow> S \<in> C)\<close>

lemma subset_in_close:
  assumes \<open>S' \<subseteq> S\<close> \<open>S \<union> x \<in> C\<close>
  shows \<open>S' \<union> x \<in> close C\<close>
proof -
  have \<open>S \<union> x \<in> close C\<close>
    unfolding close_def using \<open>S \<union> x \<in> C\<close> by blast
  then show ?thesis
    unfolding close_def using \<open>S' \<subseteq> S\<close> by blast
qed

theorem close_consistency:
  fixes C :: \<open>'i fm set set\<close>
  assumes \<open>consistency C\<close>
  shows \<open>consistency (close C)\<close>
  unfolding consistency_def
proof (intro ballI allI impI conjI)
  fix S' :: \<open>'i fm set\<close>
  assume \<open>S' \<in> close C\<close>
  then obtain S where \<open>S \<in> C\<close> \<open>S' \<subseteq> S\<close>
    unfolding close_def by blast

  { fix p
    have \<open>\<not> (Pro p \<in> S \<and> (\<^bold>\<not> Pro p) \<in> S)\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>\<not> (Pro p \<in> S' \<and> (\<^bold>\<not> Pro p) \<in> S')\<close>
      using \<open>S' \<subseteq> S\<close> by blast }

  { have \<open>\<^bold>\<bottom> \<notin> S\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by blast
    then show \<open>\<^bold>\<bottom> \<notin> S'\<close>
      using \<open>S' \<subseteq> S\<close> by blast }

  { fix Z
    assume \<open>(\<^bold>\<not> (\<^bold>\<not> Z)) \<in> S'\<close>
    then have \<open>(\<^bold>\<not> (\<^bold>\<not> Z)) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {Z} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {Z} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(A \<^bold>\<and> B) \<in> S'\<close>
    then have \<open>(A \<^bold>\<and> B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A, B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {A, B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<or> B)) \<in> S'\<close>
    then have \<open>(\<^bold>\<not> (A \<^bold>\<or> B)) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<longrightarrow> B)) \<in> S'\<close>
    then have \<open>(\<^bold>\<not> (A \<^bold>\<longrightarrow> B)) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A, \<^bold>\<not> B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by metis
    then show \<open>S' \<union> {A, \<^bold>\<not> B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(A \<^bold>\<or> B) \<in> S'\<close>
    then have \<open>(A \<^bold>\<or> B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {A} \<in> C \<or> S \<union> {B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {A} \<in> close C \<or> S' \<union> {B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<and> B)) \<in> S'\<close>
    then have \<open>(\<^bold>\<not> (A \<^bold>\<and> B)) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {\<^bold>\<not> A} \<in> C \<or> S \<union> {\<^bold>\<not> B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {\<^bold>\<not> A} \<in> close C \<or> S' \<union> {\<^bold>\<not> B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A B
    assume \<open>(A \<^bold>\<longrightarrow> B) \<in> S'\<close>
    then have \<open>(A \<^bold>\<longrightarrow> B) \<in> S\<close>
      using \<open>S' \<subseteq> S\<close> by blast
    then have \<open>S \<union> {\<^bold>\<not> A} \<in> C \<or> S \<union> {B} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {\<^bold>\<not> A} \<in> close C \<or> S' \<union> {B} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A :: \<open>'i fm\<close>
    assume \<open>tautology A\<close>
    then have \<open>S \<union> {A} \<in> C\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>S' \<union> {A} \<in> close C\<close>
      using \<open>S' \<subseteq> S\<close> subset_in_close by blast }

  { fix A i
    have \<open>\<not> (K i A \<in> S \<and> (\<^bold>\<not> K i A) \<in> S)\<close>
      using \<open>S \<in> C\<close> \<open>consistency C\<close> unfolding consistency_def by simp
    then show \<open>\<not> (K i A \<in> S' \<and> (\<^bold>\<not> K i A) \<in> S')\<close>
      using \<open>S' \<subseteq> S\<close> by blast }

qed

theorem close_closed: \<open>subset_closed (close C)\<close>
  unfolding close_def subset_closed_def by blast

theorem close_subset: \<open>C \<subseteq> close C\<close>
  unfolding close_def by blast

subsection \<open>Finite character\<close>

definition finite_char :: \<open>'a set set \<Rightarrow> bool\<close> where
  \<open>finite_char C \<equiv> (\<forall>S. S \<in> C = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C))\<close>

definition mk_finite_char :: \<open>'a set set \<Rightarrow> 'a set set\<close> where
  \<open>mk_finite_char C \<equiv> {S. \<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C}\<close>

theorem finite_char: \<open>finite_char (mk_finite_char C)\<close>
  unfolding finite_char_def mk_finite_char_def by blast

theorem finite_char_closed: \<open>finite_char C \<Longrightarrow> subset_closed C\<close>
  unfolding finite_char_def subset_closed_def
proof (intro ballI allI impI)
  fix S S'
  assume *: \<open>\<forall>S. (S \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C)\<close>
    and \<open>S' \<in> C\<close> \<open>S \<subseteq> S'\<close>
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> C\<close>
    by blast
  then show \<open>S \<in> C\<close>
    using * by blast
qed

theorem finite_char_subset: \<open>subset_closed C \<Longrightarrow> C \<subseteq> mk_finite_char C\<close>
  unfolding mk_finite_char_def subset_closed_def by blast

theorem finite_consistency:
  fixes C :: \<open>'i fm set set\<close>
  assumes \<open>consistency C\<close> \<open>subset_closed C\<close>
  shows \<open>consistency (mk_finite_char C)\<close>
  unfolding consistency_def
proof (intro ballI allI impI conjI)
  fix S
  assume \<open>S \<in> mk_finite_char C\<close>
  then have finc: \<open>\<forall>S' \<subseteq> S. finite S' \<longrightarrow> S' \<in> C\<close>
    unfolding mk_finite_char_def by blast

  have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by blast
  then have sc: \<open>\<forall>S' x. S' \<union> x \<in> C \<longrightarrow> (\<forall>S \<subseteq> S' \<union> x. S \<in> C)\<close>
    by blast

  { fix i
    show \<open>\<not> (Pro i \<in> S \<and> (\<^bold>\<not> Pro i) \<in> S)\<close>
    proof
      assume \<open>Pro i \<in> S \<and> (\<^bold>\<not> Pro i) \<in> S\<close>
      then have \<open>{Pro i, (\<^bold>\<not> Pro i)} \<in> C\<close>
        using finc by simp
      then show False
        using \<open>consistency C\<close> unfolding consistency_def by fast
    qed }

  show \<open>\<^bold>\<bottom> \<notin> S\<close>
  proof
    assume \<open>\<^bold>\<bottom> \<in> S\<close>
    then have \<open>{\<^bold>\<bottom>} \<in> C\<close>
      using finc by simp
    then show False
      using \<open>consistency C\<close> unfolding consistency_def by fast
  qed

  { fix Z
    assume *: \<open>(\<^bold>\<not> \<^bold>\<not> Z) \<in> S\<close>
    show \<open>S \<union> {Z} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {Z} \<union> {\<^bold>\<not> \<^bold>\<not> Z}\<close>

      assume \<open>S' \<subseteq> S \<union> {Z}\<close> \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {Z} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>(A \<^bold>\<and> B) \<in> S\<close>
    show \<open>S \<union> {A, B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, B} \<union> {A \<^bold>\<and> B}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, B}\<close> \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>(\<^bold>\<not> (A \<^bold>\<or> B)) \<in> S\<close>
    show \<open>S \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {\<^bold>\<not> A, \<^bold>\<not> B} \<union> {\<^bold>\<not> (A \<^bold>\<or> B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {\<^bold>\<not> A, \<^bold>\<not> B}\<close> \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>(\<^bold>\<not> (A \<^bold>\<longrightarrow> B)) \<in> S\<close>
    show \<open>S \<union> {A, \<^bold>\<not> B} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A, \<^bold>\<not> B} \<union> {\<^bold>\<not> (A \<^bold>\<longrightarrow> B)}\<close>

      assume \<open>S' \<subseteq> S \<union> {A, \<^bold>\<not> B}\<close> \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A, \<^bold>\<not> B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A B
    assume *: \<open>(A \<^bold>\<or> B) \<in> S\<close>
    show \<open>S \<union> {A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa Sb
        where \<open>Sa \<subseteq> S \<union> {A}\<close> \<open>finite Sa\<close> \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> \<open>finite Sb\<close> \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {A}) \<union> (Sb - {B}) \<union> {A \<^bold>\<or> B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>(\<^bold>\<not> (A \<^bold>\<and> B)) \<in> S\<close>
    show \<open>S \<union> {\<^bold>\<not> A} \<in> mk_finite_char C \<or> S \<union> {\<^bold>\<not> B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa Sb
        where \<open>Sa \<subseteq> S \<union> {\<^bold>\<not> A}\<close> \<open>finite Sa\<close> \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {\<^bold>\<not> B}\<close> \<open>finite Sb\<close> \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {\<^bold>\<not> A}) \<union> (Sb - {\<^bold>\<not> B}) \<union> {\<^bold>\<not> (A \<^bold>\<and> B)}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {\<^bold>\<not> A}\<close> \<open>Sb \<subseteq> S \<union> {\<^bold>\<not> B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {\<^bold>\<not> A} \<in> C \<or> ?S' \<union> {\<^bold>\<not> B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A B
    assume *: \<open>(A \<^bold>\<longrightarrow> B) \<in> S\<close>
    show \<open>S \<union> {\<^bold>\<not> A} \<in> mk_finite_char C \<or> S \<union> {B} \<in> mk_finite_char C\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain Sa Sb
        where \<open>Sa \<subseteq> S \<union> {\<^bold>\<not> A}\<close> \<open>finite Sa\<close> \<open>Sa \<notin> C\<close>
          and \<open>Sb \<subseteq> S \<union> {B}\<close> \<open>finite Sb\<close> \<open>Sb \<notin> C\<close>
        unfolding mk_finite_char_def by blast

      let ?S' = \<open>(Sa - {\<^bold>\<not> A}) \<union> (Sb - {B}) \<union> {A \<^bold>\<longrightarrow> B}\<close>

      have \<open>?S' \<subseteq> S\<close>
        using \<open>Sa \<subseteq> S \<union> {\<^bold>\<not> A}\<close> \<open>Sb \<subseteq> S \<union> {B}\<close> * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite Sa\<close> \<open>finite Sb\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {\<^bold>\<not> A} \<in> C \<or> ?S' \<union> {B} \<in> C\<close>
        using \<open>consistency C\<close> unfolding consistency_def by simp
      then have \<open>Sa \<in> C \<or> Sb \<in> C\<close>
        using sc by blast
      then show False
        using \<open>Sa \<notin> C\<close> \<open>Sb \<notin> C\<close> by blast
    qed }

  { fix A :: \<open>'i fm\<close>
    assume *: \<open>tautology A\<close>
    show \<open>S \<union> {A} \<in> mk_finite_char C\<close>
      unfolding mk_finite_char_def
    proof (intro allI impI CollectI)
      fix S'
      let ?S' = \<open>S' - {A}\<close>

      assume \<open>S' \<subseteq> S \<union> {A}\<close> \<open>finite S'\<close>
      then have \<open>?S' \<subseteq> S\<close>
        using * by blast
      moreover have \<open>finite ?S'\<close>
        using \<open>finite S'\<close> by blast
      ultimately have \<open>?S' \<in> C\<close>
        using finc by blast
      then have \<open>?S' \<union> {A} \<in> C\<close>
        using * \<open>consistency C\<close> unfolding consistency_def by metis
      then show \<open>S' \<in> C\<close>
        using sc by blast
    qed }

  { fix A i
    assume \<open>S \<in> mk_finite_char C\<close>
    show \<open>\<not> (K i A \<in> S \<and> (\<^bold>\<not> K i A) \<in> S)\<close>
    proof
      assume \<open>K i A \<in> S \<and> (\<^bold>\<not> K i A) \<in> S\<close>
      then have \<open>{K i A, (\<^bold>\<not> K i A)} \<in> C\<close>
        using finc by simp
      then show False
        using \<open>consistency C\<close> unfolding consistency_def by auto
    qed }

qed

subsection \<open>Maximal extension\<close>

instantiation fm :: (countable) countable begin
instance by countable_datatype
end

definition is_chain :: \<open>(nat \<Rightarrow> 'a set) \<Rightarrow> bool\<close> where
  \<open>is_chain f \<equiv> \<forall>n. f n \<subseteq> f (Suc n)\<close>

lemma is_chainD: \<open>is_chain f \<Longrightarrow> x \<in> f m \<Longrightarrow> x \<in> f (m + n)\<close>
  by (induct n) (auto simp: is_chain_def)

lemma is_chainD':
  assumes \<open>is_chain f\<close> \<open>x \<in> f m\<close> \<open>m \<le> k\<close>
  shows \<open>x \<in> f k\<close>
proof -
  obtain n where \<open>k = m + n\<close>
    using \<open>m \<le> k\<close> le_iff_add
    by metis
  then show \<open>x \<in> f k\<close>
    using \<open>is_chain f\<close> \<open>x \<in> f m\<close> is_chainD
    by metis
qed

lemma chain_index:
  assumes \<open>is_chain f\<close> \<open>finite F\<close>
  shows \<open>F \<subseteq> (\<Union>n. f n) \<Longrightarrow> \<exists>n. F \<subseteq> f n\<close>
  using \<open>finite F\<close>
proof (induct F rule: finite_induct)
  case empty
  then show ?case
    by blast
next
  case (insert x F)
  then have \<open>\<exists>n. F \<subseteq> f n\<close> \<open>\<exists>m. x \<in> f m\<close> \<open>F \<subseteq> (\<Union>x. f x)\<close>
    using \<open>is_chain f\<close> by simp_all
  then obtain n and m where \<open>F \<subseteq> f n\<close> \<open>x \<in> f m\<close>
    by blast
  have \<open>m \<le> max n m\<close> \<open>n \<le> max n m\<close>
    by simp_all
  have \<open>x \<in> f (max n m)\<close>
    using is_chainD' \<open>is_chain f\<close> \<open>x \<in> f m\<close> \<open>m \<le> max n m\<close>
    by fast
  moreover have \<open>F \<subseteq> f (max n m)\<close>
    using is_chainD' \<open>is_chain f\<close> \<open>F \<subseteq> f n\<close> \<open>n \<le> max n m\<close>
    by fast
  ultimately show ?case
    by blast
qed

lemma chain_union_closed':
  assumes \<open>is_chain f\<close> \<open>\<forall>n. f n \<in> C\<close> \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close> \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>S' \<in> C\<close>
proof -
  obtain n where \<open>S' \<subseteq> f n\<close>
    using chain_index \<open>is_chain f\<close> \<open>finite S'\<close> \<open>S' \<subseteq> (\<Union>n. f n)\<close>
    by blast
  moreover have \<open>f n \<in> C\<close>
    using \<open>\<forall>n. f n \<in> C\<close>
    by blast
  ultimately show \<open>S' \<in> C\<close>
    using \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    by blast
qed

lemma chain_union_closed:
  assumes \<open>finite_char C\<close> \<open>is_chain f\<close> \<open>\<forall>n. f n \<in> C\<close>
  shows \<open>(\<Union>n. f n) \<in> C\<close>
proof -
  have \<open>subset_closed C\<close>
    using finite_char_closed \<open>finite_char C\<close>
    by blast
  then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
    unfolding subset_closed_def
    by blast
  then have \<open>\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C\<close>
    using chain_union_closed' assms
    by blast
  moreover have \<open>((\<Union>n. f n) \<in> C) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> (\<Union>n. f n) \<longrightarrow> S' \<in> C)\<close>
    using \<open>finite_char C\<close> unfolding finite_char_def
    by blast
  ultimately show ?thesis
    by blast
qed

primrec extend :: \<open>'i fm set \<Rightarrow> 'i fm set set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> nat \<Rightarrow> 'i fm set\<close> where
  \<open>extend S C f 0 = S\<close> |
  \<open>extend S C f (Suc n) =
    (if extend S C f n \<union> {f n} \<in> C
     then extend S C f n \<union> {f n}
     else extend S C f n)\<close>

definition Extend :: \<open>'i fm set \<Rightarrow> 'i fm set set \<Rightarrow> (nat \<Rightarrow> 'i fm) \<Rightarrow> 'i fm set\<close> where
  \<open>Extend S C f \<equiv> \<Union>n. extend S C f n\<close>

lemma is_chain_extend: \<open>is_chain (extend S C f)\<close>
  by (simp add: is_chain_def) blast

lemma extend_in_C: \<open>consistency C \<Longrightarrow> S \<in> C \<Longrightarrow> extend S C f n \<in> C\<close>
  by (induct n) simp_all

theorem Extend_in_C: \<open>consistency C \<Longrightarrow> finite_char C \<Longrightarrow> S \<in> C \<Longrightarrow> Extend S C f \<in> C\<close>
  using chain_union_closed is_chain_extend extend_in_C unfolding Extend_def
  by blast

theorem Extend_subset: \<open>S \<subseteq> Extend S C f\<close>
  unfolding Extend_def using Union_upper extend.simps(1) range_eqI
  by metis

definition maximal :: \<open>'a set \<Rightarrow> 'a set set \<Rightarrow> bool\<close> where
  \<open>maximal S C \<equiv> \<forall>S' \<in> C. S \<subseteq> S' \<longrightarrow> S = S'\<close>

theorem Extend_maximal:
  assumes \<open>\<forall>y :: 'i fm. \<exists>n. y = f n\<close> \<open>finite_char C\<close>
  shows \<open>maximal (Extend S C f) C\<close>
  unfolding maximal_def Extend_def
proof (intro ballI impI)
  fix S'
  assume \<open>S' \<in> C\<close> \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close>
  moreover have \<open>S' \<subseteq> (\<Union>x. extend S C f x)\<close>
  proof (rule ccontr)
    assume \<open>\<not> S' \<subseteq> (\<Union>x. extend S C f x)\<close>
    then obtain z where \<open>z \<in> S'\<close> \<open>z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
    then obtain n where \<open>z = f n\<close>
      using \<open>\<forall>y. \<exists>n. y = f n\<close>
      by blast

    have \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close>
      using \<open>(\<Union>x. extend S C f x) \<subseteq> S'\<close> \<open>z = f n\<close> \<open>z \<in> S'\<close>
      by blast

    have \<open>subset_closed C\<close>
      using \<open>finite_char C\<close> finite_char_closed
      by blast
    then have \<open>\<forall>S' \<in> C. \<forall>S \<subseteq> S'. S \<in> C\<close>
      unfolding subset_closed_def
      by simp
    then have \<open>\<forall>S \<subseteq> S'. S \<in> C\<close>
      using \<open>S' \<in> C\<close>
      by blast
    then have \<open>extend S C f n \<union> {f n} \<in> C\<close>
      using \<open>extend S C f n \<union> {f n} \<subseteq> S'\<close>
      by blast
    then have \<open>z \<in> extend S C f (Suc n)\<close>
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close> \<open>z = f n\<close>
      by simp
    then show False
      using \<open>z \<notin> (\<Union>x. extend S C f x)\<close>
      by blast
  qed
  ultimately show \<open>(\<Union>x. extend S C f x) = S'\<close>
    by simp
qed

subsection \<open>K consistency\<close>

theorem K_consistency: \<open>consistency {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>}\<close>
  unfolding consistency_def
proof (intro conjI ballI allI impI notI)
  fix S :: \<open>'i fm set\<close>
  assume \<open>S \<in> {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>}\<close> (is \<open>S \<in> ?C\<close>)
  then obtain G where *: \<open>S = set G\<close> and \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close>
    by blast

  { fix i
    assume \<open>Pro i \<in> S \<and> (\<^bold>\<not> Pro i) \<in> S\<close>
    then have \<open>\<turnstile> imply G (Pro i)\<close> \<open>\<turnstile> imply G (\<^bold>\<not> Pro i)\<close>
      using K_imply_member * by blast+
    then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
      using K_FFI K_right_mp by blast
    then show False
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }

  { assume \<open>\<^bold>\<bottom> \<in> S\<close>
    then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
      using K_imply_member * by blast
    then show False
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }

  { fix Z
    assume \<open>(\<^bold>\<not> \<^bold>\<not> Z) \<in> S\<close>
    then have \<open>\<turnstile> imply G (\<^bold>\<not> \<^bold>\<not> Z)\<close>
      using K_imply_member * by simp
    then have \<open>\<not> \<turnstile> imply (Z # G) \<^bold>\<bottom>\<close>
      using K_ImpI K_right_mp \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast
    moreover have \<open>S \<union> {Z} = set (Z # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {Z} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(A \<^bold>\<and> B) \<in> S\<close>
    then have \<open>\<turnstile> imply G (A \<^bold>\<and> B)\<close>
      using K_imply_member * by simp
    moreover have \<open>\<turnstile> ((A \<^bold>\<and> B) \<^bold>\<longrightarrow> A)\<close> \<open>\<turnstile> ((A \<^bold>\<and> B) \<^bold>\<longrightarrow> B)\<close>
      using A1 by force+
    ultimately have \<open>\<turnstile> imply G A\<close> \<open>\<turnstile> imply G B\<close>
      using K_right_mp K_imply_head R1 by (metis imply.simps(2))+
    then have \<open>\<not> \<turnstile> imply (A # B # G) \<^bold>\<bottom>\<close>
      using K_imply_Cons \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> cut by metis
    moreover have \<open>S \<union> {A, B} = set (A # B # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<or> B)) \<in> S\<close>
    then have \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) (\<^bold>\<not> (A \<^bold>\<or> B))\<close> \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<or> B))\<close>
      using * K_imply_Cons K_imply_member by blast+
    moreover have \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) (\<^bold>\<not> (A \<^bold>\<or> B) \<^bold>\<longrightarrow> \<^bold>\<not> A)\<close> \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<or> B) \<^bold>\<longrightarrow> \<^bold>\<not> B)\<close>
      by (simp_all add: A1 tautology_imply)
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) (\<^bold>\<not> A)\<close> \<open>\<turnstile> imply G (\<^bold>\<not> B)\<close>
      using K_right_mp by blast+

    then have \<open>\<not> \<turnstile> imply ((\<^bold>\<not> A) # (\<^bold>\<not> B) # G) \<^bold>\<bottom>\<close>
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> cut by blast
    moreover have \<open>S \<union> {\<^bold>\<not> A, \<^bold>\<not> B} = set ((\<^bold>\<not> A) # (\<^bold>\<not> B) # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {\<^bold>\<not> A, \<^bold>\<not> B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<longrightarrow> B)) \<in> S\<close>
    then have \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) (\<^bold>\<not> (A \<^bold>\<longrightarrow> B))\<close> \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<longrightarrow> B))\<close>
      using * K_imply_member K_imply_Cons by blast+
    moreover have
      \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) (\<^bold>\<not> (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> A)\<close>
      \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> \<^bold>\<not> B)\<close>
      by (simp_all add: A1 tautology_imply)
    ultimately have \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) A\<close> \<open>\<turnstile> imply G (\<^bold>\<not> B)\<close>
      using K_right_mp by blast+

    then have \<open>\<not> \<turnstile> imply (A # (\<^bold>\<not> B) # G) \<^bold>\<bottom>\<close>
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> cut by blast
    moreover have \<open>S \<union> {A, \<^bold>\<not> B} = set (A # (\<^bold>\<not> B) # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A, \<^bold>\<not> B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(A \<^bold>\<or> B) \<in> S\<close>
    then have \<open>\<turnstile> imply G (A \<^bold>\<or> B)\<close>
      using * K_imply_member by simp

    { assume \<open>(\<forall>G'. set G' = S \<union> {A} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
      then have \<open>\<turnstile> imply (A # G) \<^bold>\<bottom>\<close> \<open>\<turnstile> imply (B # G) \<^bold>\<bottom>\<close>
        using * by (metis Un_insert_right list.simps(15) sup_bot.right_neutral)+
      then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
        using \<open>\<turnstile> imply G (A \<^bold>\<or> B)\<close> K_DisE by blast
      then have False
        using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }
    then show \<open>S \<union> {A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(\<^bold>\<not> (A \<^bold>\<and> B)) \<in> S\<close>
    then have \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<and> B))\<close>
      using * K_imply_member by blast
    moreover have \<open>\<turnstile> imply G (\<^bold>\<not> (A \<^bold>\<and> B) \<^bold>\<longrightarrow> (\<^bold>\<not> A) \<^bold>\<or> (\<^bold>\<not> B))\<close>
      by (simp add: A1 tautology_imply)
    ultimately have \<open>\<turnstile> imply G ((\<^bold>\<not> A) \<^bold>\<or> (\<^bold>\<not> B))\<close>
      using K_right_mp by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {\<^bold>\<not> A} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {\<^bold>\<not> B} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
      then have \<open>\<turnstile> imply ((\<^bold>\<not> A) # G) \<^bold>\<bottom>\<close> \<open>\<turnstile> imply ((\<^bold>\<not> B) # G) \<^bold>\<bottom>\<close>
        using * by (metis Un_insert_right list.simps(15) sup_bot.right_neutral)+
      then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
        using K_DisE \<open>\<turnstile> imply G ((\<^bold>\<not> A) \<^bold>\<or> (\<^bold>\<not> B))\<close> by blast
      then have False
        using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }
    then show \<open>S \<union> {\<^bold>\<not> A} \<in> ?C \<or> S \<union> {\<^bold>\<not> B} \<in> ?C\<close>
      by blast }

  { fix A B
    assume \<open>(A \<^bold>\<longrightarrow> B) \<in> S\<close>
    then have \<open>\<turnstile> imply G (A \<^bold>\<longrightarrow> B)\<close>
      using * K_imply_member by blast
    moreover have \<open>\<turnstile> imply G ((A \<^bold>\<longrightarrow> B) \<^bold>\<longrightarrow> (\<^bold>\<not> A) \<^bold>\<or> B)\<close>
      by (simp add: A1 tautology_imply)
    ultimately have \<open>\<turnstile> imply G ((\<^bold>\<not> A) \<^bold>\<or> B)\<close>
      using K_right_mp by blast

    { assume \<open>(\<forall>G'. set G' = S \<union> {\<^bold>\<not> A} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
        and \<open>(\<forall>G'. set G' = S \<union> {B} \<longrightarrow> \<turnstile> imply G' \<^bold>\<bottom>)\<close>
      then have \<open>\<turnstile> imply ((\<^bold>\<not> A) # G) \<^bold>\<bottom>\<close> \<open>\<turnstile> imply (B # G) \<^bold>\<bottom>\<close>
        using * by (metis Un_insert_right list.simps(15) sup_bot.right_neutral)+
      then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
        using K_DisE \<open>\<turnstile> imply G ((\<^bold>\<not> A) \<^bold>\<or> B)\<close> by blast
      then have False
        using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }
    then show \<open>S \<union> {\<^bold>\<not> A} \<in> ?C \<or> S \<union> {B} \<in> ?C\<close>
      by blast }

  { fix A :: \<open>'i fm\<close>
    assume \<open>tautology A\<close>
    then have \<open>\<turnstile> imply G A\<close>
      using tautology_imply A1 by blast
    then have \<open>\<turnstile> imply (A # G) \<^bold>\<bottom> \<Longrightarrow> \<turnstile> imply G \<^bold>\<bottom>\<close>
      using cut by blast
    moreover have \<open>S \<union> {A} = set (A # G)\<close>
      using * by simp
    ultimately show \<open>S \<union> {A} \<in> ?C\<close>
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }

  { fix A i
    assume \<open>K i A \<in> S \<and> (\<^bold>\<not> K i A) \<in> S\<close>
    then have \<open>\<turnstile> imply G (K i A)\<close> \<open>\<turnstile> imply G (\<^bold>\<not> K i A)\<close>
      using K_imply_member * by blast+
    then have \<open>\<turnstile> imply G \<^bold>\<bottom>\<close>
      using K_FFI K_right_mp by blast
    then show False
      using \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close> by blast }

qed

theorem K_finite_consistency: \<open>consistency (mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>}))\<close>
  using K_consistency finite_consistency close_closed close_consistency by blast

theorem K_concrete_finite_consistency:
  defines \<open>C \<equiv> mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  assumes \<open>set G \<in> C\<close>
  shows \<open>\<not> \<turnstile> imply G \<^bold>\<bottom>\<close>
  using assms unfolding C_def mk_finite_char_def close_def
  using K_imply_weaken by fastforce

section \<open>Model existence\<close>

lemma at_least_one_in_maximal:
  assumes \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>p \<in> V \<or> (\<^bold>\<not> p) \<in> V\<close>
proof -
  have \<open>V \<union> {p} \<in> C \<or> V \<union> {\<^bold>\<not> p} \<in> C\<close>
  proof (rule ccontr)
    assume \<open>\<not> (V \<union> {p} \<in> C \<or> V \<union> {\<^bold>\<not> p} \<in> C)\<close>
    then have \<open>V \<union> {p \<^bold>\<or> \<^bold>\<not> p} \<notin> C\<close>
      using assms unfolding consistency_def maximal_def
      by (metis (no_types, hide_lams) insert_iff subset_iff sup.absorb_iff1 sup.cobounded1)
    then show False
      using assms unfolding consistency_def maximal_def
      by simp
  qed
  then show ?thesis
    using \<open>maximal V C\<close> unfolding maximal_def
    by fast
qed

lemma at_most_one_in_maximal:
  assumes \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>\<not> (p \<in> V \<and> (\<^bold>\<not> p) \<in> V)\<close>
proof (induct p)
  case FF
  then show ?case
    using assms unfolding consistency_def by blast
next
  case (Pro x)
  then show ?case
    using assms unfolding consistency_def by simp
next
  case (Dis p q)
  show ?case
  proof
    assume \<open>(p \<^bold>\<or> q) \<in> V \<and> (\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V\<close>
    then have \<open>V \<union> {p} \<in> C \<or> V \<union> {q} \<in> C\<close> \<open>V \<union> {\<^bold>\<not> p, \<^bold>\<not> q} \<in> C\<close>
      using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp_all
    then have \<open>p \<in> V \<or> q \<in> V\<close> \<open>(\<^bold>\<not> p) \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V C\<close> unfolding maximal_def by fast+
    then show False
      using Dis by blast
  qed
next
  case (Con p q)
  show ?case
  proof
    assume \<open>(p \<^bold>\<and> q) \<in> V \<and> (\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V\<close>
    then have \<open>V \<union> {p, q} \<in> C\<close> \<open>V \<union> {\<^bold>\<not> p} \<in> C \<or> V \<union> {\<^bold>\<not> q} \<in> C\<close>
      using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp_all
    then have \<open>p \<in> V\<close> \<open>q \<in> V\<close> \<open>(\<^bold>\<not> p) \<in> V \<or> (\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V C\<close> unfolding maximal_def by fast+
    then show False
      using Con by blast
  qed
next
  case (Imp p q)
  show ?case
  proof
    assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V \<and> (\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V\<close>
    then have \<open>V \<union> {\<^bold>\<not> p} \<in> C \<or> V \<union> {q} \<in> C\<close> \<open>V \<union> {p, \<^bold>\<not> q} \<in> C\<close>
      using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp_all
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> q \<in> V\<close> \<open>p \<in> V\<close> \<open>(\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V C\<close> unfolding maximal_def by fast+
    then show False
      using Imp by blast
  qed
next
  case (K i p)
  then show ?case
    using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def
    by simp
qed

theorem exactly_one_in_maximal:
  assumes \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>(p \<in> V) \<noteq> ((\<^bold>\<not> p) \<in> V)\<close>
  using assms at_least_one_in_maximal at_most_one_in_maximal by blast

theorem conjuncts_in_maximal:
  assumes \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>(p \<^bold>\<and> q) \<in> V \<longleftrightarrow> p \<in> V \<and> q \<in> V\<close>
proof
  assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
  have \<open>V \<union> {p, q} \<in> C\<close>
    using \<open>(p \<^bold>\<and> q) \<in> V\<close> \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def
    by simp
  then show \<open>p \<in> V \<and> q \<in> V\<close>
    using \<open>maximal V C\<close> unfolding maximal_def
    by fast
next
  assume \<open>p \<in> V \<and> q \<in> V\<close>
  show \<open>(p \<^bold>\<and> q) \<in> V\<close>
  proof (rule ccontr)
    assume \<open>(p \<^bold>\<and> q) \<notin> V\<close>
    then have \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V\<close>
      using at_least_one_in_maximal assms by blast
    then have \<open>V \<union> {\<^bold>\<not> p} \<in> C \<or> V \<union> {\<^bold>\<not> q} \<in> C\<close>
      using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def
      by simp
    then have \<open>(\<^bold>\<not> p) \<in> V \<or> (\<^bold>\<not> q) \<in> V\<close>
      using \<open>maximal V C\<close> unfolding maximal_def
      by fast
    then show False
      using \<open>p \<in> V \<and> q \<in> V\<close> assms at_most_one_in_maximal
      by metis
  qed
qed

theorem consequent_in_maximal:
  assumes \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close> \<open>p \<in> V\<close> \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
  shows \<open>q \<in> V\<close>
proof -
  consider (np) \<open>V \<union> {\<^bold>\<not> p} \<in> C\<close> | (q) \<open>V \<union> {q} \<in> C\<close>
    using \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close> \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def
    by metis
  then show ?thesis
  proof cases
    case np
    then have \<open>(\<^bold>\<not> p) \<in> V\<close>
      using \<open>maximal V C\<close> unfolding maximal_def
      by fast
    then show ?thesis
      using assms at_most_one_in_maximal
      by blast
  next
    case q
    then show ?thesis
      using \<open>maximal V C\<close> unfolding maximal_def
      by fast
  qed
qed

lemma K_not_neg_in_consistency: \<open>\<not> \<turnstile> (\<^bold>\<not> p) \<Longrightarrow> {p} \<in> {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>}\<close>
proof -
  assume \<open>\<not> \<turnstile> (\<^bold>\<not> p)\<close>
  moreover have \<open>set [p] = {p}\<close>
    by simp
  moreover have \<open>imply [p] \<^bold>\<bottom> = (\<^bold>\<not> p)\<close>
    by simp
  ultimately show ?thesis
    by fastforce
qed

lemma K_inconsistent_neg:
  defines \<open>C \<equiv> mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  assumes \<open>{p} \<notin> C\<close>
  shows \<open>\<turnstile> (\<^bold>\<not> p)\<close>
  using assms unfolding C_def mk_finite_char_def close_def
  using K_not_neg_in_consistency by fastforce

lemma conjuncts_in_consistency:
  assumes \<open>consistency C\<close> \<open>subset_closed C\<close> \<open>S \<union> {p \<^bold>\<and> q} \<in> C\<close>
  shows \<open>S \<union> {p, q} \<in> C\<close>
proof -
  let ?S = \<open>S \<union> {p \<^bold>\<and> q}\<close>
  have \<open>?S \<in> C\<close>
    using assms by blast
  moreover have \<open>(p \<^bold>\<and> q) \<in> ?S\<close>
    by simp
  ultimately have \<open>?S \<union> {p, q} \<in> C\<close>
    using assms unfolding consistency_def by simp
  moreover have \<open>S \<union> {p, q} \<subseteq> ?S \<union> {p, q}\<close>
    by blast
  ultimately show \<open>S \<union> {p, q} \<in> C\<close>
    using \<open>subset_closed C\<close> unfolding subset_closed_def by simp
qed

lemma conjoined_in_consistency:
  assumes \<open>consistency C\<close> \<open>subset_closed C\<close> \<open>S \<union> {conjoin ps q} \<in> C\<close>
  shows \<open>S \<union> set ps \<union> {q} \<in> C\<close>
  using \<open>S \<union> {conjoin ps q} \<in> C\<close>
proof (induct ps arbitrary: S)
  case Nil
  then show ?case
    using \<open>subset_closed C\<close> unfolding subset_closed_def by simp
next
  case (Cons p ps)
  then have \<open>S \<union> {p, conjoin ps q} \<in> C\<close>
    using assms conjuncts_in_consistency by auto
  then have \<open>S \<union> {p} \<union> {conjoin ps q} \<in> C\<close>
    by (metis insert_is_Un sup_assoc)
  then show ?case
    using Cons by fastforce
qed

lemma inconsistent_conjoin:
  defines \<open>C \<equiv> mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  assumes \<open>set G \<union> {p} \<notin> C\<close>
  shows \<open>\<turnstile> (\<^bold>\<not> conjoin G p)\<close>
proof (rule ccontr)
  have \<open>consistency C\<close>
    unfolding C_def using K_finite_consistency by auto
  have \<open>subset_closed C\<close>
    unfolding C_def by (simp add: finite_char finite_char_closed)

  assume \<open>\<not> \<turnstile> (\<^bold>\<not> conjoin G p)\<close>
  then have \<open>{conjoin G p} \<in> C\<close>
    unfolding C_def using K_inconsistent_neg by blast
  then have \<open>set G \<union> {p} \<in> C\<close>
    using conjoined_in_consistency \<open>consistency C\<close> \<open>subset_closed C\<close> by fastforce
  then show False
    using assms(2) by blast
qed

theorem K_in_maximal:
  defines \<open>C \<equiv> mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  assumes \<open>\<turnstile> p\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>p \<in> V\<close>
proof -
  have \<open>consistency C\<close>
    unfolding C_def using K_finite_consistency by auto
  have \<open>subset_closed C\<close>
    unfolding C_def by (simp add: finite_char finite_char_closed)

  have \<open>\<turnstile> (p \<^bold>\<longrightarrow> \<^bold>\<not> \<^bold>\<not> p)\<close>
    by (simp add: A1)
  then have \<open>\<turnstile> (\<^bold>\<not> \<^bold>\<not> p)\<close>
    using \<open>\<turnstile> p\<close> R1 by blast

  show ?thesis
  proof (rule ccontr)
    assume \<open>p \<notin> V\<close>
    then have \<open>(\<^bold>\<not> p) \<in> V\<close>
      using at_least_one_in_maximal \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close> by blast
    then have \<open>set [\<^bold>\<not> p] \<in> C\<close>
      using \<open>V \<in> C\<close> \<open>subset_closed C\<close> unfolding subset_closed_def by simp
    then have \<open>\<not> \<turnstile> (\<^bold>\<not> \<^bold>\<not> p)\<close>
      using C_def K_concrete_finite_consistency by fastforce
    then show False
      using \<open>\<turnstile> (\<^bold>\<not> \<^bold>\<not> p)\<close> by blast
  qed
qed

lemma exists_finite_inconsistent:
  fixes C :: \<open>'i fm set set\<close>
  assumes \<open>finite_char C\<close> \<open>V \<union> {\<^bold>\<not> p} \<notin> C\<close>
  shows \<open>\<exists>W. W \<union> {\<^bold>\<not> p} \<subseteq> V \<union> {\<^bold>\<not> p} \<and> (\<^bold>\<not> p) \<notin> W \<and> finite W \<and> W \<union> {\<^bold>\<not> p} \<notin> C\<close>
  using assms unfolding finite_char_def
  by (smt Un_insert_right Un_subset_iff finite_insert inf_sup_ord(4)
      mk_disjoint_insert sup_bot.comm_neutral sup_ge1)

theorem exists_maximal_superset:
  fixes C :: \<open>('i :: countable) fm set set\<close>
  assumes \<open>consistency C\<close> \<open>finite_char C\<close> \<open>V \<in> C\<close>
  obtains W where \<open>V \<subseteq> W\<close> \<open> W \<in> C\<close> \<open>maximal W C\<close>
proof -
  let ?W = \<open>Extend V C from_nat\<close>

  have \<open>V \<subseteq> ?W\<close>
    using Extend_subset by blast
  moreover have \<open>?W \<in> C\<close>
    using assms Extend_in_C by blast
  moreover have \<open>maximal ?W C\<close>
    using assms Extend_maximal
    by (metis from_nat_to_nat)
  ultimately show ?thesis
    using that by blast
qed

type_synonym 'i s_max = \<open>'i fm set\<close>

abbreviation pi :: \<open>'i s_max \<Rightarrow> id \<Rightarrow> bool\<close> where
  \<open>pi s i \<equiv> Pro i \<in> s\<close>

abbreviation partition :: \<open>'i fm set \<Rightarrow> 'i \<Rightarrow> 'i fm set\<close> where
  \<open>partition V i \<equiv> {p. K i p \<in> V}\<close>

abbreviation reach :: \<open>'i fm set set \<Rightarrow> 'i \<Rightarrow> 'i s_max \<Rightarrow> 'i s_max set\<close> where
  \<open>reach C i V \<equiv> {W. partition V i \<subseteq> W \<and> W \<in> C \<and> maximal W C}\<close>

theorem model_existence:
  fixes p :: \<open>('i :: countable) fm\<close>
  defines \<open>C \<equiv> mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  assumes \<open>V \<in> C\<close> \<open>maximal V C\<close>
  shows \<open>(p \<in> V \<longleftrightarrow> Kripke pi (reach C), V \<Turnstile> p) \<and>
    ((\<^bold>\<not> p) \<in> V \<longleftrightarrow> Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> p)\<close>
proof -
  have \<open>consistency C\<close>
    unfolding C_def using K_finite_consistency by auto
  have \<open>finite_char C\<close>
    unfolding C_def by (simp add: finite_char)
  have \<open>subset_closed C\<close>
    unfolding C_def by (simp add: finite_char finite_char_closed)

  show ?thesis
    using \<open>V \<in> C\<close> \<open>maximal V C\<close>
  proof (induct p arbitrary: V)
    case FF
    then show ?case
    proof (intro conjI impI iffI)
      assume \<open>\<^bold>\<bottom> \<in> V\<close>
      then have False
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by blast
      then show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<bottom>\<close> ..
    next
      assume \<open>(\<^bold>\<not> \<^bold>\<bottom>) \<in> V\<close>
      show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> \<^bold>\<bottom>\<close>
        by simp
    next
      assume \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<bottom>\<close>
      then show \<open>\<^bold>\<bottom> \<in> V\<close>
        by simp
    next
      assume \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> \<^bold>\<bottom>\<close>
      have \<open>\<^bold>\<bottom> \<notin> V\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def
        by blast
      then show \<open>(\<^bold>\<not> \<^bold>\<bottom>) \<in> V\<close>
        using at_least_one_in_maximal FF \<open>consistency C\<close>
        by blast
    qed
  next
    case (Pro i)
    then show ?case
    proof (intro conjI impI iffI)
      assume \<open>Pro i \<in> V\<close>
      then have \<open>pi V i\<close>
        using \<open>maximal V C\<close> by blast
      then show \<open>Kripke pi (reach C), V \<Turnstile> Pro i\<close>
        by simp
    next
      assume \<open>(\<^bold>\<not> Pro i) \<in> V\<close>
      then have \<open>Pro i \<notin> V\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by fast
      then have \<open>\<not> (pi V i)\<close>
        using \<open>maximal V C\<close> by blast
      then show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> Pro i\<close>
        by simp
    next
      assume \<open>Kripke pi (reach C), V \<Turnstile> Pro i\<close>
      then show \<open>Pro i \<in> V\<close>
        by simp
    next
      assume \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> Pro i\<close>
      then have \<open>Pro i \<notin> V\<close>
        by simp
      then show \<open>(\<^bold>\<not> Pro i) \<in> V\<close>
        using at_least_one_in_maximal Pro \<open>consistency C\<close>
        by blast
    qed
  next
    case (Dis p q)
    have \<open>(p \<^bold>\<or> q) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<or> q)\<close>
    proof
      assume \<open>(p \<^bold>\<or> q) \<in> V\<close>
      then have \<open>V \<union> {p} \<in> C \<or> V \<union> {q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then consider \<open>p \<in> V\<close> | \<open>q \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast
      then show \<open>Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<or> q)\<close>
        using Dis by cases simp_all
    qed
    moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
    proof
      assume \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) \<in> V\<close>
      then have \<open>V \<union> {\<^bold>\<not> p, \<^bold>\<not> q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then have \<open>(\<^bold>\<not> p) \<in> V \<and> (\<^bold>\<not> q) \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast
      then show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<or> q)\<close>
        using Dis by simp
    qed
    ultimately show ?case
      using at_least_one_in_maximal Dis \<open>consistency C\<close>
      by auto
  next
    case (Con p q)
    have \<open>(p \<^bold>\<and> q) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<and> q)\<close>
    proof
      assume \<open>(p \<^bold>\<and> q) \<in> V\<close>
      then have \<open>V \<union> {p, q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then have \<open>p \<in> V\<close> \<open>q \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast+
      then show \<open>Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<and> q)\<close>
        using Con by simp
    qed
    moreover have \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
    proof
      assume \<open>(\<^bold>\<not> (p \<^bold>\<and> q)) \<in> V\<close>
      then have \<open>V \<union> {\<^bold>\<not> p} \<in> C \<or> V \<union> {\<^bold>\<not> q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then consider \<open>(\<^bold>\<not> p) \<in> V\<close> | \<open>(\<^bold>\<not> q) \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast
      then show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<and> q)\<close>
        using Con by cases simp_all
    qed
    ultimately show ?case
      using at_least_one_in_maximal Con \<open>consistency C\<close>
      by auto
  next
    case (Imp p q)
    have \<open>(p \<^bold>\<longrightarrow> q) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
    proof
      assume \<open>(p \<^bold>\<longrightarrow> q) \<in> V\<close>
      then have \<open>V \<union> {\<^bold>\<not> p} \<in> C \<or> V \<union> {q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then consider \<open>(\<^bold>\<not> p) \<in> V\<close> | \<open>q \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast
      then show \<open>Kripke pi (reach C), V \<Turnstile> (p \<^bold>\<longrightarrow> q)\<close>
        using Imp by cases simp_all
    qed
    moreover have \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
    proof
      assume \<open>(\<^bold>\<not> (p \<^bold>\<longrightarrow> q)) \<in> V\<close>
      then have \<open>V \<union> {p, \<^bold>\<not> q} \<in> C\<close>
        using \<open>consistency C\<close> \<open>V \<in> C\<close> unfolding consistency_def by simp
      then have \<open>p \<in> V \<and> (\<^bold>\<not> q) \<in> V\<close>
        using \<open>maximal V C\<close> unfolding maximal_def by fast
      then show \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> (p \<^bold>\<longrightarrow> q)\<close>
        using Imp by simp
    qed
    ultimately show ?case
      using at_least_one_in_maximal Imp \<open>consistency C\<close>
      by auto
  next
    case (K i p)
    have \<open>K i p \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> K i p\<close>
    proof
      assume \<open>K i p \<in> V\<close>
      then have \<open>\<forall>W \<in> reach C i V. p \<in> W \<and> W \<in> C \<and> maximal W C\<close>
        using \<open>consistency C\<close> by blast
      then have \<open>\<forall>W \<in> reach C i V. Kripke pi (reach C), W \<Turnstile> p\<close>
        using K by simp
      then show \<open>Kripke pi (reach C), V \<Turnstile> K i p\<close>
        by simp
    qed
    moreover have \<open>(Kripke pi (reach C), V \<Turnstile> K i p) \<longrightarrow> K i p \<in> V\<close>
    proof (intro allI impI)
      assume \<open>Kripke pi (reach C), V \<Turnstile> K i p\<close>

      have \<open>partition V i \<union> {\<^bold>\<not> p} \<notin> C\<close>
      proof
        assume \<open>partition V i \<union> {\<^bold>\<not> p} \<in> C\<close>
        then obtain W where \<open>partition V i \<union> {\<^bold>\<not> p} \<subseteq> W\<close> \<open>W \<in> C\<close> \<open>maximal W C\<close>
          using \<open>consistency C\<close> \<open>finite_char C\<close> exists_maximal_superset by blast
        then have \<open>Kripke pi (reach C), W \<Turnstile> \<^bold>\<not> p\<close>
          using K \<open>consistency C\<close> \<open>finite_char C\<close> by blast
        moreover have \<open>W \<in> reach C i V\<close>
          using \<open>partition V i \<union> {\<^bold>\<not> p} \<subseteq> W\<close> \<open>W \<in> C\<close> \<open>maximal W C\<close>
          by simp
        ultimately have \<open>Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> K i p\<close>
          by auto
        then show False
          using \<open>Kripke pi (reach C), V \<Turnstile> K i p\<close>
          by auto
      qed

      then obtain W where
        \<open>W \<union> {\<^bold>\<not> p} \<subseteq> partition V i \<union> {\<^bold>\<not> p}\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close> \<open>finite W\<close> \<open>W \<union> {\<^bold>\<not> p} \<notin> C\<close>
        using \<open>finite_char C\<close> exists_finite_inconsistent by force

      obtain L where \<open>set L = W\<close>
        using \<open>finite W\<close> finite_list by blast

      then have \<open>\<turnstile> (\<^bold>\<not> conjoin L (\<^bold>\<not> p))\<close>
        using inconsistent_conjoin \<open>W \<union> {\<^bold>\<not> p} \<notin> C\<close> C_def by blast
      then have \<open>\<turnstile> imply L p\<close>
        using K_conjoin_imply by blast
      then have \<open>\<turnstile> K i (imply L p)\<close>
        using R2 by fast
      then have \<open>\<turnstile> imply (map (K i) L) (K i p)\<close>
        using K_distrib_K_imp by fast
      then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
        using K_in_maximal K.prems(1, 2) unfolding C_def by blast
      then show \<open>K i p \<in> V\<close>
        using \<open>set L = W\<close> \<open>W \<union> {\<^bold>\<not> p} \<subseteq> partition V i \<union> {\<^bold>\<not> p}\<close> \<open>(\<^bold>\<not> p) \<notin> W\<close>
      proof (induct L arbitrary: W)
        case Nil
        then show ?case
          by simp
      next
        case (Cons a L)
        then have \<open>K i a \<in> V\<close>
          by auto
        then have \<open>imply (map (K i) L) (K i p) \<in> V\<close>
          using Cons(2) \<open>consistency C\<close> \<open>V \<in> C\<close> \<open>maximal V C\<close> consequent_in_maximal by auto
        then show ?case
          using Cons by auto
      qed
    qed
    moreover have \<open>(Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> K i p) \<longrightarrow> (\<^bold>\<not> K i p) \<in> V\<close>
      using K.prems(1) \<open>consistency C\<close> \<open>maximal V C\<close> at_least_one_in_maximal calculation(1) by auto
    moreover have \<open>(\<^bold>\<not> K i p) \<in> V \<longrightarrow> Kripke pi (reach C), V \<Turnstile> \<^bold>\<not> K i p\<close>
      using K.prems(1) \<open>consistency C\<close> \<open>maximal V C\<close> calculation(2) exactly_one_in_maximal by auto
    ultimately show ?case
      by blast
  qed
qed

subsection \<open>Completeness\<close>

lemma imply_completeness:
  assumes valid: \<open>\<forall>(M :: ('i, ('i :: countable) fm set) kripke) s.
    list_all (\<lambda>q. M, s \<Turnstile> q) G \<longrightarrow> M, s \<Turnstile> p\<close>
  shows \<open>\<turnstile> imply G p\<close>
proof (rule K_Boole, rule ccontr)
  assume \<open>\<not> \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close>

  let ?S = \<open>set ((\<^bold>\<not> p) # G)\<close>
  let ?C = \<open>mk_finite_char (close {set G | G. \<not> \<turnstile> imply G \<^bold>\<bottom>})\<close>
  let ?V = \<open>Extend ?S ?C from_nat\<close>
  let ?M = \<open>Kripke pi (reach ?C)\<close>

  have \<open>consistency ?C\<close>
    by (simp add: K_finite_consistency)
  have \<open>subset_closed ?C\<close>
    using finite_char finite_char_closed by blast
  have \<open>finite_char ?C\<close>
    using finite_char by blast

  have \<open>?S \<in> ?C\<close>
    using \<open>\<not> \<turnstile> imply ((\<^bold>\<not> p) # G) \<^bold>\<bottom>\<close> close_closed close_subset finite_char_subset
    by fast
  then have \<open>?V \<in> ?C\<close>
    using Extend_in_C K_finite_consistency \<open>finite_char ?C\<close> by blast

  have \<open>\<forall>y :: 'i fm. \<exists>n. y = from_nat n\<close>
    by (metis from_nat_to_nat)
  then have \<open>maximal ?V ?C\<close>
    using Extend_maximal \<open>finite_char ?C\<close> by blast

  { fix x
    assume \<open>x \<in> ?S\<close>
    then have \<open>x \<in> ?V\<close>
      using Extend_subset by blast
    then have \<open>?M, ?V \<Turnstile> x\<close>
      using model_existence \<open>?V \<in> ?C\<close> \<open>maximal ?V ?C\<close> by blast }
  then have \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> \<open>list_all (\<lambda>p. ?M, ?V \<Turnstile> p) G\<close>
    unfolding list_all_def by fastforce+
  then have \<open>?M, ?V \<Turnstile> p\<close>
    using valid by blast
  then show False
    using \<open>?M, ?V \<Turnstile> (\<^bold>\<not> p)\<close> by simp
qed

theorem completeness:
  assumes \<open>\<forall>(M :: ('i :: countable, 'i fm set) kripke) s. M, s \<Turnstile> p\<close>
  shows \<open>\<turnstile> p\<close>
  using assms imply_completeness[where G=\<open>[]\<close>] by auto

section \<open>Main Result\<close> \<comment> \<open>System K is sound and complete\<close>

abbreviation \<open>valid p \<equiv> \<forall>(M :: (nat, nat s_max) kripke) s. M, s \<Turnstile> p\<close>

theorem main: \<open>valid p \<longleftrightarrow> \<turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  with completeness show \<open>\<turnstile> p\<close>
    by blast
next
  assume \<open>\<turnstile> p\<close>
  with soundness show \<open>valid p\<close>
    by (intro allI)
qed

corollary \<open>valid p \<longrightarrow> M, s \<Turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  then have \<open>\<turnstile> p\<close>
    unfolding main .
  with soundness show \<open>M, s \<Turnstile> p\<close> .
qed

section \<open>Acknowledgements\<close>

text \<open>
The definition of a consistency property, subset closure, finite character and maximally consistent
sets is based on work by Berghofer, but has been adapted from first-order logic to epistemic logic.

  \<^item> Stefan Berghofer:
  First-Order Logic According to Fitting.
  \<^url>\<open>https://www.isa-afp.org/entries/FOL-Fitting.shtml\<close>
\<close>

end
