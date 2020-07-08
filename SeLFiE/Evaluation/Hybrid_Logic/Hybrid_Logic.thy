theory Hybrid_Logic imports "HOL-Library.Countable" begin

section \<open>Syntax\<close>

datatype ('a, 'b) fm
  = Pro 'a
  | Nom 'b
  | Neg \<open>('a, 'b) fm\<close> (\<open>\<^bold>\<not> _\<close> [40] 40)
  | Dis \<open>('a, 'b) fm\<close> \<open>('a, 'b) fm\<close> (infixr \<open>\<^bold>\<or>\<close> 30)
  | Dia \<open>('a, 'b) fm\<close> (\<open>\<^bold>\<diamond> _\<close> 10)
  | Sat 'b \<open>('a, 'b) fm\<close> (\<open>\<^bold>@ _ _\<close> 10)

text \<open>We can give other connectives as abbreviations.\<close>

abbreviation Top (\<open>\<^bold>\<top>\<close>) where
  \<open>\<^bold>\<top> \<equiv> (undefined \<^bold>\<or> \<^bold>\<not> undefined)\<close>

abbreviation Con (infixr \<open>\<^bold>\<and>\<close> 35) where
  \<open>p \<^bold>\<and> q \<equiv> \<^bold>\<not> (\<^bold>\<not> p \<^bold>\<or> \<^bold>\<not> q)\<close>

abbreviation Imp (infixr \<open>\<^bold>\<longrightarrow>\<close> 25) where
  \<open>p \<^bold>\<longrightarrow> q \<equiv> \<^bold>\<not> (p \<^bold>\<and> \<^bold>\<not> q)\<close>

abbreviation Box (\<open>\<^bold>\<box> _\<close> 10) where
  \<open>\<^bold>\<box> p \<equiv> \<^bold>\<not> (\<^bold>\<diamond> \<^bold>\<not> p)\<close>

primrec nominals :: \<open>('a, 'b) fm \<Rightarrow> 'b set\<close> where
  \<open>nominals (Pro x) = {}\<close>
| \<open>nominals (Nom i) = {i}\<close>
| \<open>nominals (\<^bold>\<not> p) = nominals p\<close>
| \<open>nominals (p \<^bold>\<or> q) = nominals p \<union> nominals q\<close>
| \<open>nominals (\<^bold>\<diamond> p) = nominals p\<close>
| \<open>nominals (\<^bold>@ i p) = {i} \<union> nominals p\<close>

primrec sub :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'c) fm\<close> where
  \<open>sub _ (Pro x) = Pro x\<close>
| \<open>sub f (Nom i) = Nom (f i)\<close>
| \<open>sub f (\<^bold>\<not> p) = (\<^bold>\<not> sub f p)\<close>
| \<open>sub f (p \<^bold>\<or> q) = (sub f p \<^bold>\<or> sub f q)\<close>
| \<open>sub f (\<^bold>\<diamond> p) = (\<^bold>\<diamond> sub f p)\<close>
| \<open>sub f (\<^bold>@ i p) = (\<^bold>@ (f i) (sub f p))\<close>

lemma sub_nominals: \<open>nominals (sub f p) = f ` nominals p\<close>
  by (induct p) auto

lemma sub_id: \<open>sub id p = p\<close>
  by (induct p) simp_all

lemma sub_upd_fresh: \<open>i \<notin> nominals p \<Longrightarrow> sub (f(i := j)) p = sub f p\<close>
  by (induct p) auto

section \<open>Semantics\<close>

text \<open>
  Type variable \<open>'w\<close> stands for the set of worlds and \<open>'a\<close> for the set of propositional symbols.
  The accessibility relation is given by \<open>R\<close> and the valuation by \<open>V\<close>.
  The mapping from nominals to worlds is an extra argument \<open>g\<close> to the semantics.\<close>

datatype ('w, 'a) model =
  Model (R: \<open>'w \<Rightarrow> 'w set\<close>) (V: \<open>'w \<Rightarrow> 'a \<Rightarrow> bool\<close>)

primrec semantics
  :: \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> 'w \<Rightarrow> ('a, 'b) fm \<Rightarrow> bool\<close>
  (\<open>_, _, _ \<Turnstile> _\<close> [50, 50, 50] 50) where
  \<open>(M, _, w \<Turnstile> Pro x) = V M w x\<close>
| \<open>(_, g, w \<Turnstile> Nom i) = (w = g i)\<close>
| \<open>(M, g, w \<Turnstile> \<^bold>\<not> p) = (\<not> M, g, w \<Turnstile> p)\<close>
| \<open>(M, g, w \<Turnstile> (p \<^bold>\<or> q)) = ((M, g, w \<Turnstile> p) \<or> (M, g, w \<Turnstile> q))\<close>
| \<open>(M, g, w \<Turnstile> \<^bold>\<diamond> p) = (\<exists>v \<in> R M w. M, g, v \<Turnstile> p)\<close>
| \<open>(M, g, _ \<Turnstile> \<^bold>@ i p) = (M, g, g i \<Turnstile> p)\<close>

lemma \<open>M, g, w \<Turnstile> \<^bold>\<top>\<close>
  by simp

lemma semantics_fresh:
  \<open>i \<notin> nominals p \<Longrightarrow> (M, g, w \<Turnstile> p) = (M, g(i := v), w \<Turnstile> p)\<close>
  by (induct p arbitrary: w) auto

subsection \<open>Examples\<close>

abbreviation is_named :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>is_named M \<equiv> \<forall>w. \<exists>a. V M a = w\<close>

abbreviation reflexive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>reflexive M \<equiv> \<forall>w. w \<in> R M w\<close>

abbreviation irreflexive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>irreflexive M \<equiv> \<forall>w. w \<notin> R M w\<close>

abbreviation symmetric :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>symmetric M \<equiv> \<forall>v w. w \<in> R M v \<longleftrightarrow> v \<in> R M w\<close>

abbreviation asymmetric :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>asymmetric M \<equiv> \<forall>v w. \<not> (w \<in> R M v \<and> v \<in> R M w)\<close>

abbreviation transitive :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>transitive M \<equiv> \<forall>v w x. w \<in> R M v \<and> x \<in> R M w \<longrightarrow> x \<in> R M v\<close>

abbreviation universal :: \<open>('w, 'b) model \<Rightarrow> bool\<close> where
  \<open>universal M \<equiv> \<forall>v w. v \<in> R M w\<close>

lemma \<open>irreflexive M \<Longrightarrow> M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
proof -
  assume \<open>irreflexive M\<close>
  then have \<open>g i \<notin> R M (g i)\<close>
    by simp
  then have \<open>\<not> (\<exists>v \<in> R M (g i). g i = v)\<close>
    by simp
  then have \<open>\<not> M, g, g i \<Turnstile> \<^bold>\<diamond> Nom i\<close>
    by simp
  then have \<open>M, g, g i \<Turnstile> \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
    by simp
  then show \<open>M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i)\<close>
    by simp
qed

text \<open>We can automatically show some characterizations of frames by pure axioms.\<close>

lemma \<open>irreflexive M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>@ i \<^bold>\<not> (\<^bold>\<diamond> Nom i))\<close>
  by auto

lemma \<open>asymmetric M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>@ i (\<^bold>\<box> \<^bold>\<not> (\<^bold>\<diamond> Nom i)))\<close>
  by auto

lemma \<open>universal M = (\<forall>g w. M, g, w \<Turnstile> \<^bold>\<diamond> Nom i)\<close>
  by auto

section \<open>Tableau\<close>

text \<open>
  A block is defined as a list of formulas and an opening nominal.
  The opening nominal is not necessarily in the list.
  A branch is a list of blocks.
  All blocks have an opening nominal; there is no possibility of an unnamed initial block.
\<close>

type_synonym ('a, 'b) block = \<open>('a, 'b) fm list \<times> 'b\<close>
type_synonym ('a, 'b) branch = \<open>('a, 'b) block list\<close>

abbreviation member_list :: \<open>'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> (\<open>_ \<in>. _\<close> [51, 51] 50) where
  \<open>x \<in>. xs \<equiv> x \<in> set xs\<close>

text \<open>The predicate \<open>on\<close> accounts for the opening nominal when checking if a formula is on a block.\<close>

primrec on :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) block \<Rightarrow> bool\<close> (\<open>_ on _\<close> [51, 51] 50) where
  \<open>p on (ps, i) = (p \<in>. ps \<or> p = Nom i)\<close>

syntax
  "_Ballon" :: \<open>pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close> (\<open>(3\<forall>(_/on_)./ _)\<close> [0, 0, 10] 10)
  "_Bexon" :: \<open>pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool\<close> (\<open>(3\<exists>(_/on_)./ _)\<close> [0, 0, 10] 10)

translations
  "\<forall>p on A. P" \<rightharpoonup> "\<forall>p. p on A \<longrightarrow> P"
  "\<exists>p on A. P" \<rightharpoonup> "\<exists>p. p on A \<and> P"

abbreviation list_nominals :: \<open>('a, 'b) fm list \<Rightarrow> 'b set\<close> where
  \<open>list_nominals ps \<equiv> (\<Union>p \<in> set ps. nominals p)\<close>

primrec block_nominals :: \<open>('a, 'b) block \<Rightarrow> 'b set\<close> where
  \<open>block_nominals (ps, i) = {i} \<union> list_nominals ps\<close>

definition branch_nominals :: \<open>('a, 'b) branch \<Rightarrow> 'b set\<close> where
  \<open>branch_nominals branch \<equiv> (\<Union>block \<in> set branch. block_nominals block)\<close>

abbreviation at_in :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close>
  (\<open>_ at _ in _\<close> [51, 51, 51] 50) where
  \<open>p at a in branch \<equiv> \<exists>ps. (ps, a) \<in>. branch \<and> p on (ps, a)\<close>

definition new :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close> where
  \<open>new p a branch \<equiv> \<not> p at a in branch\<close>

definition witnessed :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close> where
  \<open>witnessed p a branch \<equiv> \<exists>i. (\<^bold>@ i p) at a in branch \<and> (\<^bold>\<diamond> Nom i) at a in branch\<close>

text \<open>
  A branch has a closing tableau iff it is contained in the following inductively defined set.
  In that case I call the branch closeable.
  The number in front of the turnstile is the number of available coins to spend on GoTo.
\<close>

inductive ST :: \<open>nat \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close> (\<open>_ \<turnstile> _\<close> [50, 50] 50) where
  Close:
  \<open>p at i in branch \<Longrightarrow> (\<^bold>\<not> p) at i in branch \<Longrightarrow>
   n \<turnstile> branch\<close>
| Neg:
  \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # branch \<Longrightarrow>
   new p a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> (p # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| DisP:
  \<open>(p \<^bold>\<or> q) at a in (ps, a) # branch \<Longrightarrow>
   new p a ((ps, a) # branch) \<Longrightarrow> new q a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> (p # ps, a) # branch \<Longrightarrow> Suc n \<turnstile> (q # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| DisN:
  \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps, a) # branch \<Longrightarrow>
   new (\<^bold>\<not> p) a ((ps, a) # branch) \<or> new (\<^bold>\<not> q) a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| DiaP:
  \<open>(\<^bold>\<diamond> p) at a in (ps, a) # branch \<Longrightarrow>
   i \<notin> branch_nominals ((ps, a) # branch) \<Longrightarrow>
   \<nexists>a. p = Nom a \<Longrightarrow> \<not> witnessed p a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| DiaN:
  \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps, a) # branch \<Longrightarrow>
   (\<^bold>\<diamond> Nom i) at a in (ps, a) # branch \<Longrightarrow>
   new (\<^bold>\<not> (\<^bold>@ i p)) a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| SatP:
  \<open>(\<^bold>@ a p) at b in (ps, a) # branch \<Longrightarrow>
   new p a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> (p # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| SatN:
  \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps, a) # branch \<Longrightarrow>
   new (\<^bold>\<not> p) a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> ((\<^bold>\<not> p) # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>
| GoTo:
  \<open>i \<in> branch_nominals branch \<Longrightarrow>
   n \<turnstile> ([], i) # branch \<Longrightarrow>
   Suc n \<turnstile> branch\<close>
| Nom:
  \<open>p at b in (ps, a) # branch \<Longrightarrow> Nom i at b in (ps, a) # branch \<Longrightarrow>
   Nom i at a in (ps, a) # branch \<Longrightarrow>
   new p a ((ps, a) # branch) \<Longrightarrow>
   Suc n \<turnstile> (p # ps, a) # branch \<Longrightarrow>
   n \<turnstile> (ps, a) # branch\<close>

abbreviation ST_ex :: \<open>('a, 'b) branch \<Rightarrow> bool\<close> (\<open>\<turnstile> _\<close> [50] 50) where
  \<open>\<turnstile> branch \<equiv> \<exists>n. n \<turnstile> branch\<close>

lemma ST_Suc: \<open>n \<turnstile> branch \<Longrightarrow> Suc n \<turnstile> branch\<close>
  by (induct n branch rule: ST.induct) (simp_all add: ST.intros)

text \<open>A verified derivation in the calculus.\<close>

lemma
  fixes i
  defines \<open>p \<equiv> \<^bold>\<not> (\<^bold>@ i (Nom i))\<close>
  shows \<open>Suc n \<turnstile> [([p], a)]\<close>
proof -
  have \<open>i \<in> branch_nominals [([p], a)]\<close>
    unfolding p_def branch_nominals_def by simp
  then have ?thesis if \<open>n \<turnstile> [([], i), ([p], a)]\<close>
    using that GoTo by fast
  moreover have \<open>new (\<^bold>\<not> Nom i) i [([], i), ([p], a)]\<close>
    unfolding p_def new_def by auto
  moreover have \<open>(\<^bold>\<not> (\<^bold>@ i (Nom i))) at a in [([], i), ([p], a)]\<close>
    unfolding p_def by fastforce
  ultimately have ?thesis if \<open>Suc n \<turnstile> [([\<^bold>\<not> Nom i], i), ([p], a)]\<close>
    using that SatN by fast
  then show ?thesis
    by (meson Close list.set_intros(1) on.simps)
qed

section \<open>Soundness\<close>

text \<open>
  An \<open>i\<close>-block is satisfied by a model \<open>M\<close> and assignment \<open>g\<close> if all formulas on the block
    are true under \<open>M\<close> at the world \<open>g i\<close>
  A branch is satisfied by a model and assignment if all blocks on it are.
\<close>

primrec block_sat :: \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> ('a, 'b) block \<Rightarrow> bool\<close>
  (\<open>_, _ \<Turnstile>\<^sub>B _\<close> [50, 50] 50) where
  \<open>(M, g \<Turnstile>\<^sub>B (ps, i)) = (\<forall>p on (ps, i). M, g, g i \<Turnstile> p)\<close>

abbreviation branch_sat ::
  \<open>('w, 'a) model \<Rightarrow> ('b \<Rightarrow> 'w) \<Rightarrow> ('a, 'b) branch \<Rightarrow> bool\<close>
  (\<open>_, _ \<Turnstile>\<^sub>\<Theta> _\<close> [50, 50] 50) where
  \<open>M, g \<Turnstile>\<^sub>\<Theta> branch \<equiv> \<forall>(ps, i) \<in> set branch. M, g \<Turnstile>\<^sub>B (ps, i)\<close>

lemma block_nominals:
  \<open>p on block \<Longrightarrow> i \<in> nominals p \<Longrightarrow> i \<in> block_nominals block\<close>
  by (induct block) auto

lemma block_sat_fresh:
  assumes \<open>M, g \<Turnstile>\<^sub>B block\<close> \<open>i \<notin> block_nominals block\<close>
  shows \<open>M, g(i := v) \<Turnstile>\<^sub>B block\<close>
  using assms
proof (induct block)
  case (Pair ps a)
  then have \<open>\<forall>p on (ps, a). i \<notin> nominals p\<close>
    using block_nominals by fast
  moreover have \<open>i \<noteq> a\<close>
    using calculation by simp
  ultimately have \<open>\<forall>p on (ps, a). M, g(i := v), (g(i := v)) a \<Turnstile> p\<close>
    using Pair semantics_fresh by fastforce
  then show ?case
    by (meson block_sat.simps)
qed

lemma branch_sat_fresh:
  assumes \<open>M, g \<Turnstile>\<^sub>\<Theta> branch\<close> \<open>i \<notin> branch_nominals branch\<close>
  shows \<open>M, g(i := v) \<Turnstile>\<^sub>\<Theta> branch\<close>
  using assms using block_sat_fresh unfolding branch_nominals_def by fast

text \<open>If a branch has a derivation then it cannot be satisfied.\<close>

lemma soundness': \<open>n \<turnstile> branch \<Longrightarrow> M, g \<Turnstile>\<^sub>\<Theta> branch \<Longrightarrow> False\<close>
proof (induct branch arbitrary: g rule: ST.induct)
  case (Close p i branch)
  then have \<open>M, g, g i \<Turnstile> p\<close> \<open>M, g, g i \<Turnstile> \<^bold>\<not> p\<close>
    by fastforce+
  then show ?case
    by simp
next
  case (Neg p a ps branch)
  have \<open>M, g, g a \<Turnstile> p\<close>
    using Neg(1, 5) by fastforce
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> (p # ps, a) # branch\<close>
    using Neg(5) by simp
  then show ?case
    using Neg(4) by blast
next
  case (DisP p q a ps branch)
  consider \<open>M, g, g a \<Turnstile> p\<close> | \<open>M, g, g a \<Turnstile> q\<close>
    using DisP(1, 8) by fastforce
  then consider
    \<open>M, g \<Turnstile>\<^sub>\<Theta> (p # ps, a) # branch\<close> |
    \<open>M, g \<Turnstile>\<^sub>\<Theta> (q # ps, a) # branch\<close>
    using DisP(8) by auto
  then show ?case
    using DisP(5, 7) by metis
next
  case (DisN p q a ps branch)
  have \<open>M, g, g a \<Turnstile> \<^bold>\<not> p\<close> \<open>M, g, g a \<Turnstile> \<^bold>\<not> q\<close>
    using DisN(1, 5) by fastforce+
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch\<close>
    using DisN(5) by simp
  then show ?case
    using DisN(4) by blast
next
  case (DiaP p a ps branch i)
  then have *: \<open>M, g \<Turnstile>\<^sub>B (ps, a)\<close>
    by simp

  have \<open>i \<notin> nominals p\<close>
    using DiaP(1-2) unfolding branch_nominals_def by fastforce

  have \<open>M, g, g a \<Turnstile> \<^bold>\<diamond> p\<close>
    using DiaP(1, 7) by fastforce
  then obtain v where \<open>v \<in> R M (g a)\<close> \<open>M, g, v \<Turnstile> p\<close>
    by auto
  then have \<open>M, g(i := v), v \<Turnstile> p\<close>
    using \<open>i \<notin> nominals p\<close> semantics_fresh by metis
  then have \<open>M, g(i := v), g a \<Turnstile> \<^bold>@ i p\<close>
    by simp
  moreover have \<open>M, g(i := v), g a \<Turnstile> \<^bold>\<diamond> Nom i\<close>
    using \<open>v \<in> R M (g a)\<close> by simp
  moreover have \<open>M, g(i := v) \<Turnstile>\<^sub>\<Theta> (ps, a) # branch\<close>
    using DiaP(2, 7) branch_sat_fresh by fast
  moreover have \<open>i \<notin> block_nominals (ps, a)\<close>
    using DiaP(2) unfolding branch_nominals_def by simp
  then have \<open>\<forall>p on (ps, a). M, g(i := v), g a \<Turnstile> p\<close>
    using * semantics_fresh by fastforce
  ultimately have
    \<open>M, g(i := v) \<Turnstile>\<^sub>\<Theta> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch\<close>
    by auto
  then show ?case
    using DiaP by blast
next
  case (DiaN p a ps branch i)
  have \<open>M, g, g a \<Turnstile> \<^bold>\<not> (\<^bold>\<diamond> p)\<close> \<open>M, g, g a \<Turnstile> \<^bold>\<diamond> Nom i\<close>
    using DiaN(1-2, 6) by fastforce+
  then have \<open>M, g, g a \<Turnstile> \<^bold>\<not> (\<^bold>@ i p)\<close>
    by simp
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch\<close>
    using DiaN(6) by simp
  then show ?thesis
    using DiaN(5) by blast
next
  case (SatP a p b ps branch)
  have \<open>M, g, g a \<Turnstile> p\<close>
    using SatP(1, 5) by fastforce
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> (p # ps, a) # branch\<close>
    using SatP(5) by simp
  then show ?case
    using SatP(4) by blast
next
  case (SatN a p b ps branch)
  have \<open>M, g, g a \<Turnstile> \<^bold>\<not> p\<close>
    using SatN(1, 5) by fastforce
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> ((\<^bold>\<not> p) # ps, a) # branch\<close>
    using SatN(5) by simp
  then show ?case
    using SatN(4) by blast
next
  case (GoTo i branch)
  then show ?case
    by auto
next
  case (Nom p b ps a branch i g)
  have \<open>M, g, g b \<Turnstile> p\<close> \<open>M, g, g b \<Turnstile> Nom i\<close>
    using Nom(1-2, 7) by fastforce+
  then have \<open>M, g, g i \<Turnstile> p\<close>
    by simp
  moreover have \<open>M, g, g a \<Turnstile> Nom i\<close>
    using Nom(3, 7) by fastforce
  moreover have \<open>M, g \<Turnstile>\<^sub>B (ps, a)\<close>
    using Nom(7) by simp
  ultimately have \<open>M, g \<Turnstile>\<^sub>B (p # ps, a)\<close>
    by simp
  then have \<open>M, g \<Turnstile>\<^sub>\<Theta> (p # ps, a) # branch\<close>
    using Nom(7) by simp
  then show ?case
    using Nom(6) by blast
qed

lemma block_sat: \<open>\<forall>p on block. M, g, w \<Turnstile> p \<Longrightarrow> M, g \<Turnstile>\<^sub>B block\<close>
  by (induct block) auto

lemma branch_sat:
  assumes \<open>\<forall>(ps, i) \<in> set branch. \<forall>p on (ps, i). M, g, w \<Turnstile> p\<close>
  shows \<open>M, g \<Turnstile>\<^sub>\<Theta> branch\<close>
  using assms block_sat by fast

lemma soundness:
  assumes \<open>n \<turnstile> branch\<close>
  shows \<open>\<exists>block \<in> set branch. \<exists>p on block. \<not> M, g, w \<Turnstile> p\<close>
  using assms soundness' branch_sat by fast

corollary \<open>\<not> n \<turnstile> []\<close>
  using soundness by fastforce

theorem soundness_fresh:
  assumes \<open>n \<turnstile> [([\<^bold>\<not> p], i)]\<close> \<open>i \<notin> nominals p\<close>
  shows \<open>M, g, w \<Turnstile> p\<close>
proof -
  from assms(1) have \<open>M, g, g i \<Turnstile> p\<close> for g
    using soundness by fastforce
  then have \<open>M, g(i := w), (g(i := w)) i \<Turnstile> p\<close>
    by blast
  then have \<open>M, g(i := w), w \<Turnstile> p\<close>
    by simp
  then have \<open>M, g(i := g i), w \<Turnstile> p\<close>
    using assms(2) semantics_fresh by metis
  then show ?thesis
    by simp
qed

section \<open>No Detours\<close>

text \<open>
  We only need to spend initial coins when we apply GoTo twice in a row.
  Otherwise another rule will have been applied in-between that justifies the GoTo.
  Therefore by avoiding detours we can close any closeable branch starting from 1 coin.
\<close>

primrec nonempty :: \<open>('a, 'b) block \<Rightarrow> bool\<close> where
  \<open>nonempty (ps, i) = (ps \<noteq> [])\<close>

lemma nonempty_Suc:
  assumes
    \<open>n \<turnstile> (ps, a) # filter nonempty left @ right\<close>
    \<open>q at a in (ps, a) # filter nonempty left @ right\<close> \<open>q \<noteq> Nom a\<close>
  shows \<open>Suc n \<turnstile> filter nonempty ((ps, a) # left) @ right\<close>
proof (cases ps)
  case Nil
  then have \<open>a \<in> branch_nominals (filter nonempty left @ right)\<close>
    unfolding branch_nominals_def using assms(2-3) by fastforce
  then show ?thesis
    using assms(1) Nil GoTo by auto
next
  case Cons
  then show ?thesis
    using assms(1) ST_Suc by auto
qed

lemma ST_nonempty:
  \<open>n \<turnstile> left @ right \<Longrightarrow> Suc m \<turnstile> filter nonempty left @ right\<close>
proof (induct n \<open>left @ right\<close> arbitrary: left right rule: ST.induct)
  case (Close p i n)
  have \<open>(\<^bold>\<not> p) at i in filter nonempty left @ right\<close>
    using Close(2) by fastforce
  moreover from this have \<open>p at i in filter nonempty left @ right\<close>
    using Close(1) by fastforce
  ultimately show ?case
    using ST.Close by fast
next
  case (Neg p a ps branch n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> (p # ps, a) # branch\<close>
      using Neg(4) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using Neg(1-2) ST.Neg by fast
    then show ?thesis
      using Nil Neg(5) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> (p # ps, a) # filter nonempty left' @ right\<close>
      using Neg(4)[where left=\<open>_ # left'\<close>] Neg(5) by fastforce
    moreover have *: \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons Neg(1, 5) by fastforce
    moreover have \<open>new p a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons Neg(2, 5) unfolding new_def by auto
    ultimately have \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.Neg by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
      using * nonempty_Suc by fast
    then show ?thesis
      using Cons Neg(5) by auto
  qed
next
  case (DisP p q a ps branch n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> (p # ps, a) # branch\<close> \<open>Suc m \<turnstile> (q # ps, a) # branch\<close>
      using DisP(5, 7) by fastforce+
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using DisP(1-3) ST.DisP by fast
    then show ?thesis
      using Nil DisP(8) ST_Suc by auto
  next
    case (Cons _ left')
    then have
      \<open>Suc m \<turnstile> (p # ps, a) # filter nonempty left' @ right\<close>
      \<open>Suc m \<turnstile> (q # ps, a) # filter nonempty left' @ right\<close>
      using DisP(5, 7)[where left=\<open>_ # left'\<close>] DisP(8) by fastforce+
    moreover have *: \<open>(p \<^bold>\<or> q) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons DisP(1, 8) by fastforce
    moreover have
      \<open>new p a ((ps, a) # filter nonempty left' @ right)\<close>
      \<open>new q a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons DisP(2-3, 8) unfolding new_def by auto
    ultimately have \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.DisP by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
      using * nonempty_Suc by fast
    then show ?thesis
      using Cons DisP(8) by auto
  qed
next
  case (DisN p q a ps branch n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch\<close>
      using DisN(4) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using DisN(1-2) ST.DisN by fast
    then show ?thesis
      using Nil DisN(5) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # filter nonempty left' @ right\<close>
      using DisN(4)[where left=\<open>_ # left'\<close>] DisN(5) by fastforce
    moreover have *: \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons DisN(1, 5) by fastforce
    moreover consider
      \<open>new (\<^bold>\<not> p) a ((ps, a) # filter nonempty left' @ right)\<close> |
      \<open>new (\<^bold>\<not> q) a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons DisN(2, 5) unfolding new_def by auto
    ultimately have \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.DisN by metis
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
      using * nonempty_Suc by fast
    then show ?thesis
      using Cons DisN(5) by auto
  qed
next
  case (DiaP p a ps branch i n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch\<close>
      using DiaP(6) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using DiaP(1-4) ST.DiaP by fast
    then show ?thesis
      using Nil DiaP(7) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # filter nonempty left' @ right\<close>
      using DiaP(6)[where left=\<open>_ # left'\<close>] DiaP(7) by fastforce
    moreover have *: \<open>(\<^bold>\<diamond> p) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons DiaP(1, 7) by fastforce
    moreover have \<open>i \<notin> branch_nominals ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons DiaP(2, 7) unfolding branch_nominals_def by auto
    moreover have \<open>\<not> witnessed p a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons DiaP(4, 7) unfolding witnessed_def by auto
    ultimately have \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using DiaP(3) ST.DiaP by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
      using * nonempty_Suc by fast
    then show ?thesis
      using Cons DiaP(7) by auto
  qed
next
  case (DiaN p a ps branch i n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch\<close>
      using DiaN(5) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using DiaN(1-3) ST.DiaN by fast
    then show ?thesis
      using Nil DiaN(6) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # filter nonempty left' @ right\<close>
      using DiaN(5)[where left=\<open>_ # left'\<close>] DiaN(6) by fastforce
    moreover have *: \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons DiaN(1, 6) by fastforce
    moreover have *: \<open>(\<^bold>\<diamond> Nom i) at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons DiaN(2, 6) by fastforce
    moreover have \<open>new (\<^bold>\<not> (\<^bold>@ i p)) a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons DiaN(3, 6) unfolding new_def by auto
    ultimately have \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.DiaN by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
      using * nonempty_Suc by fast
    then show ?thesis
      using Cons DiaN(6) by auto
  qed
next
  case (SatP a p b ps branch n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> (p # ps, a) # branch\<close>
      using SatP(4) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using SatP(1-2) ST.SatP by fast
    then show ?thesis
      using Nil SatP(5) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> (p # ps, a) # filter nonempty left' @ right\<close>
      using SatP(4)[where left=\<open>_ # left'\<close>] SatP(5) by fastforce
    moreover have \<open>(\<^bold>@ a p) at b in (ps, a) # filter nonempty left' @ right\<close>
      using Cons SatP(1, 5) by fastforce
    moreover have \<open>new p a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons SatP(2, 5) unfolding new_def by auto
    ultimately have *: \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.SatP by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
    proof (cases ps)
      case Nil
      then have \<open>a \<in> branch_nominals (filter nonempty left' @ right)\<close>
        unfolding branch_nominals_def using SatP(1, 5) Cons by fastforce
      then show ?thesis
        using * Nil GoTo by fastforce
    next
      case Cons
      then show ?thesis
        using * ST_Suc by auto
    qed
    then show ?thesis
      using Cons SatP(5) by auto
  qed
next
  case (SatN a p b ps branch n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> p) # ps, a) # branch\<close>
      using SatN(4) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using SatN(1-2) ST.SatN by fast
    then show ?thesis
      using Nil SatN(5) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> ((\<^bold>\<not> p) # ps, a) # filter nonempty left' @ right\<close>
      using SatN(4)[where left=\<open>_ # left'\<close>] SatN(5) by fastforce
    moreover have \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps, a) # filter nonempty left' @ right\<close>
      using Cons SatN(1, 5) by fastforce
    moreover have \<open>new (\<^bold>\<not> p) a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons SatN(2, 5) unfolding new_def by auto
    ultimately have *: \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.SatN by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
    proof (cases ps)
      case Nil
      then have \<open>a \<in> branch_nominals (filter nonempty left' @ right)\<close>
        unfolding branch_nominals_def using SatN(1, 5) Cons by fastforce
      then show ?thesis
        using * Nil GoTo by fastforce
    next
      case Cons
      then show ?thesis
        using * ST_Suc by auto
    qed
    then show ?thesis
      using Cons SatN(5) by auto
  qed
next
  case (GoTo i n)
  show ?case
    using GoTo(3)[where left=\<open>([], i) # left\<close>] by simp
next
  case (Nom p b ps a branch i n)
  then show ?case
  proof (cases left)
    case Nil
    then have \<open>Suc m \<turnstile> (p # ps, a) # branch\<close>
      using Nom(6) by fastforce
    then have \<open>m \<turnstile> (ps, a) # branch\<close>
      using Nom(1-4) ST.Nom by fast
    then show ?thesis
      using Nil Nom(7) ST_Suc by auto
  next
    case (Cons _ left')
    then have \<open>Suc m \<turnstile> (p # ps, a) # filter nonempty left' @ right\<close>
      using Nom(6)[where left=\<open>_ # left'\<close>] Nom(7) by fastforce
    moreover have
      \<open>p at b in (ps, a) # filter nonempty left' @ right\<close>
      \<open>Nom i at b in (ps, a) # filter nonempty left' @ right\<close>
      \<open>Nom i at a in (ps, a) # filter nonempty left' @ right\<close>
      using Cons Nom(1-4, 7) unfolding new_def by simp_all (metis empty_iff empty_set)+
    moreover have \<open>new p a ((ps, a) # filter nonempty left' @ right)\<close>
      using Cons Nom(4, 7) unfolding new_def by auto
    ultimately have *: \<open>m \<turnstile> (ps, a) # filter nonempty left' @ right\<close>
      using ST.Nom by fast
    then have \<open>Suc m \<turnstile> filter nonempty ((ps, a) # left') @ right\<close>
    proof (cases ps)
      case Nil
      moreover have \<open>a \<noteq> b\<close>
        using Nom(1, 4) unfolding new_def by blast
      ultimately have \<open>a \<in> branch_nominals (filter nonempty left' @ right)\<close>
      proof (cases \<open>i = a\<close>)
        case True
        then have \<open>Nom a at b in left' @ right\<close>
          using \<open>a \<noteq> b\<close> Nom(2, 7) Cons by auto
        then show ?thesis
          unfolding branch_nominals_def using \<open>a \<noteq> b\<close> by fastforce
      next
        case False
        then have \<open>Nom i at a in left' @ right\<close>
          using Nom(3, 7) Nil Cons by auto
        then show ?thesis
          unfolding branch_nominals_def using False by fastforce
      qed
      then show ?thesis
        using * Nil GoTo by auto
    next
      case Cons
      then show ?thesis
        using * ST_Suc by auto
    qed
    then show ?thesis
      using Cons Nom(7) by auto
  qed
qed

theorem ST_coins: \<open>n \<turnstile> branch \<Longrightarrow> Suc m \<turnstile> branch\<close>
  using ST_nonempty[where left=\<open>[]\<close>] by auto

corollary ST_one: \<open>n \<turnstile> branch \<Longrightarrow> 1 \<turnstile> branch\<close>
  using ST_coins by auto

subsection \<open>Free GoTo\<close>

text \<open>The above result allows us to derive a version of GoTo that works "for free."\<close>

lemma GoTo':
  assumes \<open>Suc n \<turnstile> ([], i) # branch\<close> \<open>i \<in> branch_nominals branch\<close>
  shows \<open>Suc n \<turnstile> branch\<close>
  using assms GoTo ST_coins by fast

section \<open>Indexed Mapping\<close>

text \<open>This section contains some machinery for deriving rules.\<close>

subsection \<open>Indexing\<close>

text \<open>
  We use pairs of natural numbers to index into the branch.
  The first component specifies the block and the second specifies the formula in that block.
  We index from the back to ensure that indices are stable
    under the addition of new formulas and blocks.
\<close>

primrec rev_nth :: \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a option\<close> (infixl \<open>!.\<close> 100) where
  \<open>[] !. v = None\<close>
| \<open>(x # xs) !. v = (if length xs = v then Some x else xs !. v)\<close>

lemma rev_nth_last: \<open>xs !. 0 = Some x \<Longrightarrow> last xs = x\<close>
  by (induct xs) auto

lemma rev_nth_zero: \<open>(xs @ [x]) !. 0 = Some x\<close>
  by (induct xs) auto

lemma rev_nth_snoc: \<open>(xs @ [x]) !. Suc v = Some y \<Longrightarrow> xs !. v = Some y\<close>
  by (induct xs) auto

lemma rev_nth_Suc: \<open>(xs @ [x]) !. Suc v = xs !. v\<close>
  by (induct xs) auto

lemma rev_nth_bounded: \<open>v < length xs \<Longrightarrow> \<exists>x. xs !. v = Some x\<close>
  by (induct xs) simp_all

lemma rev_nth_Cons: \<open>xs !. v = Some y \<Longrightarrow> (x # xs) !. v = Some y\<close>
proof (induct xs arbitrary: v rule: rev_induct)
  case (snoc a xs)
  then show ?case
  proof (induct v)
    case (Suc v)
    then have \<open>xs !. v = Some y\<close>
      using rev_nth_snoc by fast
    then have \<open>(x # xs) !. v = Some y\<close>
      using Suc(2) by blast
    then show ?case
      using Suc(3) by auto
  qed simp
qed simp

lemma rev_nth_append: \<open>xs !. v = Some y \<Longrightarrow> (ys @ xs) !. v = Some y\<close>
  using rev_nth_Cons[where xs=\<open>_ @ xs\<close>] by (induct ys) simp_all

lemma rev_nth_mem: \<open>block \<in>. branch \<longleftrightarrow> (\<exists>v. branch !. v = Some block)\<close>
proof
  assume \<open>block \<in>. branch\<close>
  then show \<open>\<exists>v. branch !. v = Some block\<close>
  proof (induct branch)
    case (Cons block' branch)
    then show ?case
    proof (cases \<open>block = block'\<close>)
      case False
      then have \<open>\<exists>v. branch !. v = Some block\<close>
        using Cons by simp
      then show ?thesis
        using rev_nth_Cons by fast
    qed auto
  qed simp
next
  assume \<open>\<exists>v. branch !. v = Some block\<close>
  then show \<open>block \<in>. branch\<close>
  proof (induct branch)
    case (Cons block' branch)
    then show ?case
      by simp (metis option.sel)
  qed simp
qed

lemma rev_nth_on: \<open>p on (ps, i) \<longleftrightarrow> (\<exists>v. ps !. v = Some p) \<or> p = Nom i\<close>
  by (simp add: rev_nth_mem)

lemma rev_nth_Some: \<open>xs !. v = Some y \<Longrightarrow> v < length xs\<close>
proof (induct xs arbitrary: v rule: rev_induct)
  case (snoc x xs)
  then show ?case
    by (induct v) (simp_all, metis rev_nth_snoc)
qed simp

lemma index_Cons:
  assumes \<open>((ps, a) # branch) !. v = Some (qs, b)\<close> \<open>qs !. v' = Some q\<close>
  shows \<open>\<exists>qs'. ((p # ps, a) # branch) !. v = Some (qs', b) \<and> qs' !. v' = Some q\<close>
proof -
  have
    \<open>((p # ps, a) # branch) !. v = Some (qs, b) \<or>
     ((p # ps, a) # branch) !. v = Some (p # qs, b)\<close>
    using assms(1) by auto
  moreover have \<open>qs !. v' = Some q\<close> \<open>(p # qs) !. v' = Some q\<close>
    using assms(2) rev_nth_Cons by fast+
  ultimately show ?thesis
    by fastforce
qed

subsection \<open>Mapping\<close>

primrec mapi :: \<open>(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
  \<open>mapi f [] = []\<close>
| \<open>mapi f (x # xs) = f (length xs) x # mapi f xs\<close>

primrec mapi_block ::
  \<open>(nat \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm) \<Rightarrow> (('a, 'b) block \<Rightarrow> ('a, 'b) block)\<close> where
  \<open>mapi_block f (ps, i) = (mapi f ps, i)\<close>

definition mapi_branch ::
  \<open>(nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm) \<Rightarrow> (('a, 'b) branch \<Rightarrow> ('a, 'b) branch)\<close> where
  \<open>mapi_branch f branch \<equiv> mapi (\<lambda>v. mapi_block (f v)) branch\<close>

abbreviation mapper ::
  \<open>(('a, 'b) fm \<Rightarrow> ('a, 'b) fm) \<Rightarrow>
   (nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm\<close> where
  \<open>mapper f xs v v' p \<equiv> (if (v, v') \<in> xs then f p else p)\<close>

lemma mapi_block_add_oob:
  assumes \<open>length ps \<le> v'\<close>
  shows
    \<open>mapi_block (mapper f ({(v, v')} \<union> xs) v) (ps, i) =
     mapi_block (mapper f xs v) (ps, i)\<close>
  using assms by (induct ps) simp_all

lemma mapi_branch_add_oob:
  assumes \<open>length branch \<le> v\<close>
  shows
    \<open>mapi_branch (mapper f ({(v, v')} \<union> xs)) branch =
     mapi_branch (mapper f xs) branch\<close>
  unfolding mapi_branch_def using assms by (induct branch) simp_all

lemma mapi_branch_head_add_oob:
  \<open>mapi_branch (mapper f ({(length branch, length ps)} \<union> xs)) ((ps, a) # branch) =
   mapi_branch (mapper f xs) ((ps, a) # branch)\<close>
  using mapi_branch_add_oob[where branch=branch] unfolding mapi_branch_def
  using mapi_block_add_oob[where ps=ps] by simp

lemma mapi_branch_mem:
  assumes \<open>(ps, i) \<in>. branch\<close>
  shows \<open>\<exists>v. (mapi (f v) ps, i) \<in>. mapi_branch f branch\<close>
  unfolding mapi_branch_def using assms by (induct branch) auto

lemma rev_nth_mapi_branch:
  assumes \<open>branch !. v = Some (ps, a)\<close>
  shows \<open>(mapi (f v) ps, a) \<in>. mapi_branch f branch\<close>
  unfolding mapi_branch_def using assms
  by (induct branch) (simp_all, metis mapi_block.simps option.inject)

lemma rev_nth_mapi_block:
  assumes \<open>ps !. v' = Some p\<close>
  shows \<open>f v' p on (mapi f ps, a)\<close>
  using assms by (induct ps) (simp_all, metis option.sel)

lemma mapi_append:
  \<open>mapi f (xs @ ys) = mapi (\<lambda>v. f (v + length ys)) xs @ mapi f ys\<close>
  by (induct xs) simp_all

lemma mapi_block_id: \<open>mapi_block (mapper f {} v) (ps, i) = (ps, i)\<close>
  by (induct ps) auto

lemma mapi_branch_id: \<open>mapi_branch (mapper f {}) branch = branch\<close>
  unfolding mapi_branch_def using mapi_block_id by (induct branch) auto

lemma length_mapi: \<open>length (mapi f xs) = length xs\<close>
  by (induct xs) auto

lemma mapi_rev_nth:
  assumes \<open>xs !. v = Some x\<close>
  shows \<open>mapi f xs !. v = Some (f v x)\<close>
  using assms
proof (induct xs arbitrary: v)
  case (Cons y xs)
  have *: \<open>mapi f (y # xs) = f (length xs) y # mapi f xs\<close>
    by simp
  show ?case
  proof (cases \<open>v = length xs\<close>)
    case True
    then have \<open>mapi f (y # xs) !. v = Some (f (length xs) y)\<close>
      using length_mapi * by (metis rev_nth.simps(2))
    then show ?thesis
      using Cons.prems True by auto
  next
    case False
    then show ?thesis
      using * Cons length_mapi by (metis rev_nth.simps(2))
  qed
qed simp

section \<open>Duplicate Formulas\<close>

subsection \<open>Removable indices\<close>

abbreviation \<open>proj \<equiv> Equiv_Relations.proj\<close>

definition all_is :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) fm list \<Rightarrow> nat set \<Rightarrow> bool\<close> where
  \<open>all_is p ps xs \<equiv> \<forall>v \<in> xs. ps !. v = Some p\<close>

definition is_at :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>is_at p i branch v v' \<equiv> \<exists>ps. branch !. v = Some (ps, i) \<and> ps !. v' = Some p\<close>

text \<open>This definition is slightly complicated by the inability to index the opening nominal.\<close>

definition is_elsewhere :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool\<close> where
  \<open>is_elsewhere p i branch xs \<equiv> \<exists>w w' ps. (w, w') \<notin> xs \<and>
    branch !. w = Some (ps, i) \<and> (p = Nom i \<or> ps !. w' = Some p)\<close>

definition Dup :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool\<close> where
  \<open>Dup p i branch xs \<equiv> \<forall>(v, v') \<in> xs.
    is_at p i branch v v' \<and> is_elsewhere p i branch xs\<close>

lemma Dup_all_is:
  assumes \<open>Dup p i branch xs\<close> \<open>branch !. v = Some (ps, a)\<close>
  shows \<open>all_is p ps (proj xs v)\<close>
  using assms unfolding Dup_def is_at_def all_is_def proj_def by auto

lemma Dup_branch:
  \<open>Dup p i branch xs \<Longrightarrow> Dup p i (extra @ branch) xs\<close>
  unfolding Dup_def is_at_def is_elsewhere_def using rev_nth_append by fast

lemma Dup_block:
  assumes \<open>Dup p i ((ps, a) # branch) xs\<close>
  shows \<open>Dup p i ((ps' @ ps, a) # branch) xs\<close>
  unfolding Dup_def
proof safe
  fix v v'
  assume \<open>(v, v') \<in> xs\<close>
  then show \<open>is_at p i ((ps' @ ps, a) # branch) v v'\<close>
    using assms rev_nth_append unfolding Dup_def is_at_def by fastforce
next
  fix v v'
  assume \<open>(v, v') \<in> xs\<close>
  then obtain w w' qs where
    \<open>(w, w') \<notin> xs\<close> \<open>((ps, a) # branch) !. w = Some (qs, i)\<close>
    \<open>p = Nom i \<or> qs !. w' = Some p\<close>
    using assms unfolding Dup_def is_elsewhere_def by blast
  then have
    \<open>\<exists>qs. ((ps' @ ps, a) # branch) !. w = Some (qs, i) \<and>
     (p = Nom i \<or> qs !. w' = Some p)\<close>
    using rev_nth_append by fastforce
  then show \<open>is_elsewhere p i ((ps' @ ps, a) # branch) xs\<close>
    unfolding is_elsewhere_def using \<open>(w, w') \<notin> xs\<close> by blast
qed

lemma Dup_opening:
  assumes \<open>Dup p i branch xs\<close> \<open>(v, v') \<in> xs\<close> \<open>branch !. v = Some (ps, a)\<close>
  shows \<open>i = a\<close>
  using assms unfolding Dup_def is_at_def by auto

lemma Dup_head:
  \<open>Dup p i ((ps, a) # branch) xs \<Longrightarrow> Dup p i ((q # ps, a) # branch) xs\<close>
  using Dup_block[where ps'=\<open>[_]\<close>] by simp

lemma Dup_head_oob':
  assumes \<open>Dup p i ((ps, a) # branch) xs\<close>
  shows \<open>(length branch, k + length ps) \<notin> xs\<close>
  using assms rev_nth_Some unfolding Dup_def is_at_def by fastforce

lemma Dup_head_oob:
  assumes \<open>Dup p i ((ps, a) # branch) xs\<close>
  shows \<open>(length branch, length ps) \<notin> xs\<close>
  using assms Dup_head_oob'[where k=0] by fastforce

subsection \<open>Omitting formulas\<close>

primrec omit :: \<open>nat set \<Rightarrow> ('a, 'b) fm list \<Rightarrow> ('a, 'b) fm list\<close> where
  \<open>omit xs [] = []\<close>
| \<open>omit xs (p # ps) = (if length ps \<in> xs then omit xs ps else p # omit xs ps)\<close>

primrec omit_block :: \<open>nat set \<Rightarrow> ('a, 'b) block \<Rightarrow> ('a, 'b) block\<close> where
  \<open>omit_block xs (ps, a) = (omit xs ps, a)\<close>

definition omit_branch :: \<open>(nat \<times> nat) set \<Rightarrow> ('a, 'b) branch \<Rightarrow> ('a, 'b) branch\<close> where
  \<open>omit_branch xs branch \<equiv> mapi (\<lambda>v. omit_block (proj xs v)) branch\<close>

lemma omit_mem: \<open>ps !. v = Some p \<Longrightarrow> v \<notin> xs \<Longrightarrow> p \<in>. omit xs ps\<close>
proof (induct ps)
  case (Cons q ps)
  then show ?case
    by (cases \<open>v = length ps\<close>) simp_all
qed simp

lemma omit_id: \<open>omit {} ps = ps\<close>
  by (induct ps) auto

lemma omit_block_id: \<open>omit_block {} block = block\<close>
  using omit_id by (cases block) simp

lemma omit_branch_id: \<open>omit_branch {} branch = branch\<close>
  unfolding omit_branch_def proj_def using omit_block_id
  by (induct branch) fastforce+

lemma omit_branch_mem_diff_opening:
  assumes \<open>Dup p i branch xs\<close> \<open>(ps, a) \<in>. branch\<close> \<open>i \<noteq> a\<close>
  shows \<open>(ps, a) \<in>. omit_branch xs branch\<close>
proof -
  obtain v where v: \<open>branch !. v = Some (ps, a)\<close>
    using assms(2) rev_nth_mem by fast
  then have \<open>omit_branch xs branch !. v = Some (omit (proj xs v) ps, a)\<close>
    unfolding omit_branch_def by (simp add: mapi_rev_nth)
  then have *: \<open>(omit (proj xs v) ps, a) \<in>. omit_branch xs branch\<close>
    using rev_nth_mem by fast
  moreover have \<open>proj xs v = {}\<close>
    unfolding proj_def using assms(1, 3) v Dup_opening by fast
  then have \<open>omit (proj xs v) ps = ps\<close>
    using omit_id by auto
  ultimately show ?thesis
    by simp
qed

lemma omit_branch_mem_same_opening:
  assumes \<open>Dup p i branch xs\<close> \<open>p at i in branch\<close>
  shows \<open>p at i in omit_branch xs branch\<close>
proof -
  obtain ps where ps: \<open>(ps, i) \<in>. branch\<close> \<open>p on (ps, i)\<close>
    using assms(2) by blast
  then obtain v where v: \<open>branch !. v = Some (ps, i)\<close>
    using rev_nth_mem by fast
  then have \<open>omit_branch xs branch !. v = Some (omit (proj xs v) ps, i)\<close>
    unfolding omit_branch_def by (simp add: mapi_rev_nth)
  then have *: \<open>(omit (proj xs v) ps, i) \<in>. omit_branch xs branch\<close>
    using rev_nth_mem by fast

  consider
    v' where \<open>ps !. v' = Some p\<close> \<open>(v, v') \<in> xs\<close> |
    v' where \<open>ps !. v' = Some p\<close> \<open>(v, v') \<notin> xs\<close> |
    \<open>p = Nom i\<close>
    using ps v rev_nth_mem by fastforce
  then show ?thesis
  proof cases
    case (1 v')
    then obtain qs w w' where qs:
      \<open>(w, w') \<notin> xs\<close> \<open>branch !. w = Some (qs, i)\<close> \<open>p = Nom i \<or> qs !. w' = Some p\<close>
      using assms(1) unfolding Dup_def is_elsewhere_def by blast
    then have \<open>omit_branch xs branch !. w = Some (omit (proj xs w) qs, i)\<close>
      unfolding omit_branch_def by (simp add: mapi_rev_nth)
    then have \<open>(omit (proj xs w) qs, i) \<in>. omit_branch xs branch\<close>
      using rev_nth_mem by fast
    moreover have \<open>p on (omit (proj xs w) qs, i)\<close>
      unfolding proj_def using qs(1, 3) omit_mem by fastforce
    ultimately show ?thesis
      by blast
  next
    case (2 v')
    then show ?thesis
      using * omit_mem unfolding proj_def
      by (metis Image_singleton_iff on.simps)
  next
    case 3
    then show ?thesis
      using * by auto
  qed
qed

lemma omit_del:
  assumes \<open>p \<in>. ps\<close> \<open>p \<notin> set (omit xs ps)\<close>
  shows \<open>\<exists>v. ps !. v = Some p \<and> v \<in> xs\<close>
  using assms omit_mem rev_nth_mem by metis

lemma omit_all_is:
  assumes \<open>all_is p ps xs\<close> \<open>q \<in>. ps\<close> \<open>q \<notin> set (omit xs ps)\<close>
  shows \<open>q = p\<close>
  using assms omit_del unfolding all_is_def by fastforce

lemma omit_branch_mem_diff_formula:
  assumes \<open>Dup p i branch xs\<close> \<open>q at i in branch\<close> \<open>p \<noteq> q\<close>
  shows \<open>q at i in omit_branch xs branch\<close>
proof -
  obtain ps where ps: \<open>(ps, i) \<in>. branch\<close> \<open>q on (ps, i)\<close>
    using assms(2) by blast
  then obtain v where v: \<open>branch !. v = Some (ps, i)\<close>
    using rev_nth_mem by fast
  then have \<open>omit_branch xs branch !. v = Some (omit (proj xs v) ps, i)\<close>
    unfolding omit_branch_def by (simp add: mapi_rev_nth)
  then have *: \<open>(omit (proj xs v) ps, i) \<in>. omit_branch xs branch\<close>
    using rev_nth_mem by fast
  moreover have \<open>all_is p ps (proj xs v)\<close>
    using assms(1) Dup_all_is v by fast
  then have \<open>q on (omit (proj xs v) ps, i)\<close>
    using ps assms(3) omit_all_is by auto
  ultimately show ?thesis
    by blast
qed

lemma omit_branch_mem:
  assumes \<open>Dup p i branch xs\<close> \<open>q at a in branch\<close>
  shows \<open>q at a in omit_branch xs branch\<close>
  using assms omit_branch_mem_diff_opening omit_branch_mem_same_opening
    omit_branch_mem_diff_formula by fast

lemma omit_set: \<open>set (omit xs ps) \<subseteq> set ps\<close>
  by (induct ps) auto

lemma on_omit: \<open>p on (omit xs ps, i) \<Longrightarrow> p on (ps, i)\<close>
  using omit_set by auto

lemma Dup_set:
  assumes \<open>all_is p ps xs\<close>
  shows \<open>{p} \<union> set (omit xs ps) = {p} \<union> set ps\<close>
  using assms omit_all_is omit_set unfolding all_is_def by fast

lemma Dup_list_nominals:
  assumes \<open>all_is p ps xs\<close>
  shows \<open>nominals p \<union> list_nominals (omit xs ps) = nominals p \<union> list_nominals ps\<close>
  using assms Dup_set by fastforce

lemma Dup_block_nominals:
  assumes \<open>all_is p ps xs\<close>
  shows
    \<open>nominals p \<union> block_nominals (omit xs ps, i) =
     nominals p \<union> block_nominals (ps, i)\<close>
  using assms by (simp add: Dup_list_nominals)

lemma Dup_branch_nominals':
  assumes \<open>Dup p i branch xs\<close>
  shows
    \<open>nominals p \<union> branch_nominals (omit_branch xs branch) =
     nominals p \<union> branch_nominals branch\<close>
proof -
  have \<open>\<forall>(v, v') \<in> xs. v < length branch \<longrightarrow> is_at p i branch v v'\<close>
    using assms unfolding Dup_def by auto
  then show ?thesis
  proof (induct branch)
    case Nil
    then show ?case
      unfolding omit_branch_def by simp
  next
    case (Cons block branch)
    then show ?case
    proof (cases block)
      case (Pair ps a)
      have \<open>\<forall>(v, v') \<in> xs. v < length branch \<longrightarrow> is_at p i branch v v'\<close>
        using Cons(2) rev_nth_Cons unfolding is_at_def by auto
      then have
        \<open>nominals p \<union> branch_nominals (omit_branch xs branch) =
         nominals p \<union> branch_nominals branch\<close>
        using Cons(1) by blast
      then have
        \<open>nominals p \<union> branch_nominals (omit_branch xs ((ps, a) # branch)) =
         nominals p \<union> block_nominals (omit (proj xs (length branch)) ps, a) \<union>
          branch_nominals branch\<close>
        unfolding branch_nominals_def omit_branch_def by auto
      moreover have \<open>all_is p ps (proj xs (length branch))\<close>
        using Cons(2) Pair unfolding proj_def all_is_def is_at_def by auto
      then have
        \<open>nominals p \<union> block_nominals (omit (proj xs (length branch)) ps, a) =
         nominals p \<union> block_nominals (ps, a)\<close>
        using Dup_block_nominals by fast
      then have
        \<open>nominals p \<union> block_nominals (omit_block (proj xs (length branch)) (ps, a)) =
         nominals p \<union> block_nominals (ps, a)\<close>
        by simp
      ultimately have
        \<open>nominals p \<union> branch_nominals (omit_branch xs ((ps, a) # branch)) =
          nominals p \<union> block_nominals (ps, a) \<union> branch_nominals branch\<close>
        by auto
      then show ?thesis
        unfolding branch_nominals_def using Pair by auto
    qed
  qed
qed

lemma Dup_branch_nominals:
  assumes \<open>Dup p i branch xs\<close>
  shows \<open>branch_nominals (omit_branch xs branch) = branch_nominals branch\<close>
proof (cases \<open>xs = {}\<close>)
  case True
  then show ?thesis
    using omit_branch_id by metis
next
  case False
  with assms obtain ps w w' where
    \<open>(w, w') \<notin> xs\<close> \<open>branch !. w = Some (ps, i)\<close> \<open>p = Nom i \<or> ps !. w' = Some p\<close>
    unfolding Dup_def is_elsewhere_def by fast
  then have *: \<open>(ps, i) \<in>. branch\<close> \<open>p on (ps, i)\<close>
    using rev_nth_mem rev_nth_on by fast+
  then have \<open>nominals p \<subseteq> branch_nominals branch\<close>
    unfolding branch_nominals_def using block_nominals by fast
  moreover obtain ps' where
    \<open>(ps', i) \<in>. omit_branch xs branch\<close> \<open>p on (ps', i)\<close>
    using assms * omit_branch_mem by fast
  then have \<open>nominals p \<subseteq> branch_nominals (omit_branch xs branch)\<close>
    unfolding branch_nominals_def using block_nominals by fast
  moreover have
    \<open>nominals p \<union> branch_nominals (omit_branch xs branch) =
     nominals p \<union> branch_nominals branch\<close>
    using assms Dup_branch_nominals' by fast
  ultimately show ?thesis
    by blast
qed

lemma omit_branch_mem_dual:
  assumes \<open>p at i in omit_branch xs branch\<close>
  shows \<open>p at i in branch\<close>
proof -
  obtain ps where ps: \<open>(ps, i) \<in>. omit_branch xs branch\<close> \<open>p on (ps, i)\<close>
    using assms(1) by blast
  then obtain v where v: \<open>omit_branch xs branch !. v = Some (ps, i)\<close>
    using rev_nth_mem unfolding omit_branch_def by fast
  then have \<open>v < length (omit_branch xs branch)\<close>
    using rev_nth_Some by fast
  then have \<open>v < length branch\<close>
    unfolding omit_branch_def using length_mapi by metis
  then obtain ps' i' where ps': \<open>branch !. v = Some (ps', i')\<close>
    using rev_nth_bounded by (metis surj_pair)
  then have \<open>omit_branch xs branch !. v = Some (omit (proj xs v) ps', i')\<close>
    unfolding omit_branch_def by (simp add: mapi_rev_nth)
  then have \<open>ps = omit (proj xs v) ps'\<close> \<open>i = i'\<close>
    using v by simp_all
  then have \<open>p on (ps', i)\<close>
    using ps omit_set by auto
  moreover have \<open>(ps', i) \<in>. branch\<close>
    using ps' \<open>i = i'\<close> rev_nth_mem by fast
  ultimately show ?thesis
    using \<open>ps = omit (proj xs v) ps'\<close> by blast
qed

lemma witnessed_omit_branch:
  assumes \<open>witnessed p a (omit_branch xs branch)\<close>
  shows \<open>witnessed p a branch\<close>
proof -
  obtain ps qs i where
    ps: \<open>(ps, a) \<in>. omit_branch xs branch\<close> \<open>(\<^bold>@ i p) on (ps, a)\<close> and
    qs: \<open>(qs, a) \<in>. omit_branch xs branch\<close> \<open>(\<^bold>\<diamond> Nom i) on (qs, a)\<close>
    using assms unfolding witnessed_def by blast
  from ps obtain ps' where
    \<open>(ps', a) \<in>. branch\<close> \<open>(\<^bold>@ i p) on (ps', a)\<close>
    using omit_branch_mem_dual by fast
  moreover from qs obtain qs' where
    \<open>(qs', a) \<in>. branch\<close> \<open>(\<^bold>\<diamond> Nom i) on (qs', a)\<close>
    using omit_branch_mem_dual by fast
  ultimately show ?thesis
    unfolding witnessed_def by blast
qed

lemma new_omit_branch:
  assumes \<open>new p a branch\<close>
  shows \<open>new p a (omit_branch xs branch)\<close>
  using assms omit_branch_mem_dual unfolding new_def by fast

lemma omit_oob:
  assumes \<open>length ps \<le> v\<close>
  shows \<open>omit ({v} \<union> xs) ps = omit xs ps\<close>
  using assms by (induct ps) simp_all

lemma omit_branch_oob:
  assumes \<open>length branch \<le> v\<close>
  shows \<open>omit_branch ({(v, v')} \<union> xs) branch = omit_branch xs branch\<close>
  using assms
proof (induct branch)
  case Nil
  then show ?case
    unfolding omit_branch_def by simp
next
  case (Cons block branch)
  let ?xs = \<open>({(v, v')} \<union> xs)\<close>
  show ?case
  proof (cases block)
    case (Pair ps a)
    then have
      \<open>omit_branch ?xs ((ps, a) # branch) =
        (omit (proj ?xs (length branch)) ps, a) # omit_branch xs branch\<close>
      using Cons unfolding omit_branch_def by simp
    moreover have \<open>proj ?xs (length branch) = proj xs (length branch)\<close>
      using Cons(2) unfolding proj_def by auto
    ultimately show ?thesis
      unfolding omit_branch_def by simp
  qed
qed

subsection \<open>Induction\<close>

lemma ST_Dup:
  assumes \<open>n \<turnstile> branch\<close> \<open>Dup q i branch xs\<close>
  shows \<open>n \<turnstile> omit_branch xs branch\<close>
  using assms
proof (induct n branch)
  case (Close p i' branch n)
  have \<open>p at i' in omit_branch xs branch\<close>
    using Close(1, 3) omit_branch_mem by fast
  moreover have \<open>(\<^bold>\<not> p) at i' in omit_branch xs branch\<close>
    using Close(2, 3) omit_branch_mem by fast
  ultimately show ?case
    using ST.Close by fast
next
  case (Neg p a ps branch n)
  have \<open>Suc n \<turnstile> omit_branch xs ((p # ps, a) # branch)\<close>
    using Neg(4-) Dup_head by fast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using Neg(5) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> (p # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in omit_branch xs ((ps, a) # branch)\<close>
    using Neg(1, 5) omit_branch_mem by fast
  moreover have \<open>new p a (omit_branch xs ((ps, a) # branch))\<close>
    using Neg(2) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.Neg)
next
  case (DisP p q a ps branch n)
  have
    \<open>Suc n \<turnstile> omit_branch xs ((p # ps, a) # branch)\<close>
    \<open>Suc n \<turnstile> omit_branch xs ((q # ps, a) # branch)\<close>
    using DisP(4-) Dup_head by fast+
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DisP(8) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> (p # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    \<open>Suc n \<turnstile> (q # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp_all
  moreover have \<open>(p \<^bold>\<or> q) at a in omit_branch xs ((ps, a) # branch)\<close>
    using DisP(1, 8) omit_branch_mem by fast
  moreover have \<open>new p a (omit_branch xs ((ps, a) # branch))\<close>
    using DisP(2) new_omit_branch by fast
  moreover have \<open>new q a (omit_branch xs ((ps, a) # branch))\<close>
    using DisP(3) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.DisP)
next
  case (DisN p q a ps branch n)
  have \<open>Suc n \<turnstile> omit_branch xs (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch)\<close>
    using DisN(4-) Dup_block[where ps'=\<open>[_, _]\<close>] by fastforce
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DisN(5) Dup_head_oob by fast
  moreover have \<open>(length branch, 1 + length ps) \<notin> xs\<close>
    using DisN(5) Dup_head_oob' by fast
  ultimately have
    \<open>Suc n \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # omit (proj xs (length branch)) ps, a) #
      omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in omit_branch xs ((ps, a) # branch)\<close>
    using DisN(1, 5) omit_branch_mem by fast
  moreover have
    \<open>new (\<^bold>\<not> p) a (omit_branch xs ((ps, a) # branch)) \<or>
     new (\<^bold>\<not> q) a (omit_branch xs ((ps, a) # branch))\<close>
    using DisN(2) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.DisN)
next
  case (DiaP p a ps branch i n)
  have \<open>Suc n \<turnstile> omit_branch xs (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch)\<close>
    using DiaP(4-) Dup_block[where ps'=\<open>[_, _]\<close>] by fastforce
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DiaP(7) Dup_head_oob by fast
  moreover have \<open>(length branch, 1+ length ps) \<notin> xs\<close>
    using DiaP(7) Dup_head_oob' by fast
  ultimately have
    \<open>Suc n \<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # omit (proj xs (length branch)) ps, a) #
      omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>\<diamond> p) at a in omit_branch xs ((ps, a) # branch)\<close>
    using DiaP(1, 7) omit_branch_mem by fast
  moreover have \<open>i \<notin> branch_nominals (omit_branch xs ((ps, a) # branch))\<close>
    using DiaP(2, 7) Dup_branch_nominals by fast
  moreover have \<open>\<not> witnessed p a (omit_branch xs ((ps, a) # branch))\<close>
    using DiaP(4) witnessed_omit_branch by fast
  ultimately show ?case
    using DiaP(3) by (simp add: omit_branch_def ST.DiaP)
next
  case (DiaN p a ps branch i n)
  have \<open>Suc n \<turnstile> omit_branch xs (((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch)\<close>
    using DiaN(4-) Dup_head by fast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DiaN(6) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # omit (proj xs (length branch)) ps, a) #
      omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in omit_branch xs ((ps, a) # branch)\<close>
    using DiaN(1, 6) omit_branch_mem by fast
  moreover have \<open>(\<^bold>\<diamond> Nom i) at a in omit_branch xs ((ps, a) # branch)\<close>
    using DiaN(2, 6) omit_branch_mem by fast
  moreover have \<open>new (\<^bold>\<not> (\<^bold>@ i p)) a (omit_branch xs ((ps, a) # branch))\<close>
    using DiaN(3) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.DiaN)
next
  case (SatP a p b ps branch n)
  have \<open>Suc n \<turnstile> omit_branch xs ((p # ps, a) # branch)\<close>
    using SatP(4-) Dup_head by fast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using SatP(5) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> (p # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>@ a p) at b in omit_branch xs ((ps, a) # branch)\<close>
    using SatP(1, 5) omit_branch_mem by fast
  moreover have \<open>new p a (omit_branch xs ((ps, a) # branch))\<close>
    using SatP(2) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.SatP)
next
  case (SatN a p b ps branch n)
  have \<open>Suc n \<turnstile> omit_branch xs (((\<^bold>\<not> p) # ps, a) # branch)\<close>
    using SatN(4-) Dup_head by fast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using SatN(5) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> ((\<^bold>\<not> p) # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in omit_branch xs ((ps, a) # branch)\<close>
    using SatN(1, 5) omit_branch_mem by fast
  moreover have \<open>new (\<^bold>\<not> p) a (omit_branch xs ((ps, a) # branch))\<close>
    using SatN(2) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.SatN)
next
  case (GoTo i branch n)
  then have \<open>n \<turnstile> omit_branch xs (([], i) # branch)\<close>
    using Dup_branch[where extra=\<open>[([], i)]\<close>] by fastforce
  then have \<open>n \<turnstile> ([], i) # omit_branch xs branch\<close>
    unfolding omit_branch_def by simp
  moreover have \<open>i \<in> branch_nominals (omit_branch xs branch)\<close>
    using GoTo(1, 4) Dup_branch_nominals by fast
  ultimately show ?case
    unfolding omit_branch_def by (simp add: ST.GoTo)
next
  case (Nom p b ps a branch i' n)
  have \<open>Suc n \<turnstile> omit_branch xs ((p # ps, a) # branch)\<close>
    using Nom(4-) Dup_head by fast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using Nom(7) Dup_head_oob by fast
  ultimately have
    \<open>Suc n \<turnstile> (p # omit (proj xs (length branch)) ps, a) # omit_branch xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>p at b in omit_branch xs ((ps, a) # branch)\<close>
    using Nom(1, 7) omit_branch_mem by fast
  moreover have \<open>Nom i' at b in omit_branch xs ((ps, a) # branch)\<close>
    using Nom(2, 7) omit_branch_mem by fast
  moreover have \<open>Nom i' at a in omit_branch xs ((ps, a) # branch)\<close>
    using Nom(3, 7) omit_branch_mem by fast
  moreover have \<open>new p a (omit_branch xs ((ps, a) # branch))\<close>
    using Nom(4) new_omit_branch by fast
  ultimately show ?case
    by (simp add: omit_branch_def ST.Nom)
qed

theorem Dup:
  assumes \<open>n \<turnstile> (p # ps, a) # branch\<close> \<open>\<not> new p a ((ps, a) # branch)\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
proof -
  obtain qs where qs:
    \<open>(qs, a) \<in>. (ps, a) # branch\<close> \<open>p on (qs, a)\<close>
    using assms(2) unfolding new_def by blast

  let ?xs = \<open>{(length branch, length ps)}\<close>

  have *: \<open>is_at p a ((p # ps, a) # branch) (length branch) (length ps)\<close>
    unfolding is_at_def by simp

  have \<open>Dup p a ((p # ps, a) # branch) ?xs\<close>
  proof (cases \<open>p = Nom a\<close>)
    case True
    moreover have \<open>((p # ps, a) # branch) !. length branch = Some (p # ps, a)\<close>
      by simp
    moreover have \<open>p on (p # ps, a)\<close>
      by simp
    ultimately have \<open>is_elsewhere p a ((p # ps, a) # branch) ?xs\<close>
      unfolding is_elsewhere_def using assms(2) rev_nth_Some
      by (metis (mono_tags, lifting) Pair_inject less_le singletonD)
    then show ?thesis
      unfolding Dup_def using * by blast
  next
    case false: False
    then show ?thesis
    proof (cases \<open>ps = qs\<close>)
      case True
      then obtain w' where w': \<open>qs !. w' = Some p\<close>
        using qs(2) false rev_nth_mem by fastforce
      then have \<open>(p # ps) !. w' = Some p\<close>
        using True rev_nth_Cons by fast
      moreover have \<open>((p # ps, a) # branch) !. length branch = Some (p # ps, a)\<close>
        by simp
      moreover have \<open>(length branch, w') \<notin> ?xs\<close>
        using True w' rev_nth_Some by fast
      ultimately have \<open>is_elsewhere p a ((p # ps, a) # branch) ?xs\<close>
        unfolding is_elsewhere_def by fast
      then show ?thesis
        unfolding Dup_def using * by fast
    next
      case False
      then obtain w where w: \<open>branch !. w = Some (qs, a)\<close>
        using qs(1) rev_nth_mem by fastforce
      moreover obtain w' where w': \<open>qs !. w' = Some p\<close>
        using qs(2) false rev_nth_mem by fastforce
      moreover have \<open>(w, w') \<notin> ?xs\<close>
        using rev_nth_Some w by fast
      ultimately have \<open>is_elsewhere p a ((p # ps, a) # branch) ?xs\<close>
        unfolding is_elsewhere_def using rev_nth_Cons by fast
      then show ?thesis
        unfolding Dup_def using * by fast
    qed
  qed

  then have \<open>n \<turnstile> omit_branch ?xs ((p # ps, a) # branch)\<close>
    using assms(1) ST_Dup by fast
  then have \<open>n \<turnstile> (omit (proj ?xs (length branch)) ps, a) # omit_branch ?xs branch\<close>
    unfolding omit_branch_def proj_def by simp
  moreover have \<open>omit_branch ?xs branch = omit_branch {} branch\<close>
    using omit_branch_oob by auto
  then have \<open>omit_branch ?xs branch = branch\<close>
    using omit_branch_id by simp
  moreover have \<open>proj ?xs (length branch) = {length ps}\<close>
    unfolding proj_def by blast
  then have \<open>omit (proj ?xs (length branch)) ps = omit {} ps\<close>
    using omit_oob by auto
  then have \<open>omit (proj ?xs (length branch)) ps = ps\<close>
    using omit_id by simp
  ultimately show ?thesis
    by simp
qed

subsection \<open>Unrestricted rules\<close>

lemma ST_add: \<open>n \<turnstile> branch \<Longrightarrow> m + n \<turnstile> branch\<close>
  using ST_Suc by (induct m) auto

lemma ST_le: \<open>n \<turnstile> branch \<Longrightarrow> n \<le> m \<Longrightarrow> m \<turnstile> branch\<close>
  using ST_add by (metis le_add_diff_inverse2)

lemma Neg':
  assumes
    \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> (p # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
  using assms Neg Dup ST_Suc by metis

lemma DisP':
  assumes
    \<open>(p \<^bold>\<or> q) at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> (p # ps, a) # branch\<close> \<open>n \<turnstile> (q # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
proof (cases \<open>new p a ((ps, a) # branch) \<and> new q a ((ps, a) # branch)\<close>)
  case True
  then show ?thesis
    using assms DisP ST_Suc by fast
next
  case False
  then show ?thesis
    using assms Dup by fast
qed

lemma DisP'':
  assumes
    \<open>(p \<^bold>\<or> q) at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> (p # ps, a) # branch\<close> \<open>m \<turnstile> (q # ps, a) # branch\<close>
  shows \<open>max n m \<turnstile> (ps, a) # branch\<close>
proof (cases \<open>n \<le> m\<close>)
  case True
  then have \<open>m \<turnstile> (p # ps, a) # branch\<close>
    using assms(2) ST_le by blast
  then show ?thesis
    using assms True by (simp add: DisP' max.absorb2)
next
  case False
  then have \<open>n \<turnstile> (q # ps, a) # branch\<close>
    using assms(3) ST_le by fastforce
  then show ?thesis
    using assms False by (simp add: DisP' max.absorb1)
qed

lemma DisN':
  assumes
    \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
proof (cases \<open>new (\<^bold>\<not> q) a ((ps, a) # branch) \<or> new (\<^bold>\<not> p) a ((ps, a) # branch)\<close>)
  case True
  then show ?thesis
    using assms DisN ST_Suc by fast
next
  case False
  then show ?thesis
    using assms Dup
    by (metis (no_types, lifting) list.set_intros(1-2) new_def on.simps set_ConsD)
qed

lemma DiaN':
  assumes
    \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps, a) # branch\<close>
    \<open>(\<^bold>\<diamond> Nom i) at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
  using assms DiaN Dup ST_Suc by fast

lemma SatP':
  assumes
    \<open>(\<^bold>@ a p) at b in (ps, a) # branch\<close>
    \<open>n \<turnstile> (p # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
  using assms SatP Dup ST_Suc by fast

lemma SatN':
  assumes
    \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps, a) # branch\<close>
    \<open>n \<turnstile> ((\<^bold>\<not> p) # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
  using assms SatN Dup ST_Suc by fast

lemma Nom':
  assumes
    \<open>p at b in (ps, a) # branch\<close>
    \<open>Nom i at b in (ps, a) # branch\<close>
    \<open>Nom i at a in (ps, a) # branch\<close>
    \<open>n \<turnstile> (p # ps, a) # branch\<close>
  shows \<open>n \<turnstile> (ps, a) # branch\<close>
  using assms Nom Dup ST_Suc by fast

section \<open>Substitution\<close>

lemma finite_nominals: \<open>finite (nominals p)\<close>
  by (induct p) simp_all

lemma finite_block_nominals: \<open>finite (block_nominals block)\<close>
  using finite_nominals by (induct block) auto

lemma finite_branch_nominals: \<open>finite (branch_nominals branch)\<close>
  unfolding branch_nominals_def by (induct branch) (auto simp: finite_block_nominals)

abbreviation sub_list :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) fm list \<Rightarrow> ('a, 'c) fm list\<close> where
  \<open>sub_list f ps \<equiv> map (sub f) ps\<close>

primrec sub_block :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) block \<Rightarrow> ('a, 'c) block\<close> where
  \<open>sub_block f (ps, i) = (sub_list f ps, f i)\<close>

definition sub_branch :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a, 'b) branch \<Rightarrow> ('a, 'c) branch\<close> where
  \<open>sub_branch f blocks \<equiv> map (sub_block f) blocks\<close>

lemma sub_block_mem: \<open>p on block \<Longrightarrow> sub f p on sub_block f block\<close>
  by (induct block) auto

lemma sub_branch_mem:
  assumes \<open>(ps, i) \<in>. branch\<close>
  shows \<open>(sub_list f ps, f i) \<in>. sub_branch f branch\<close>
  unfolding sub_branch_def using assms image_iff by fastforce

lemma sub_block_nominals: \<open>block_nominals (sub_block f block) = f ` block_nominals block\<close>
  by (induct block) (auto simp: sub_nominals)

lemma sub_branch_nominals:
  \<open>branch_nominals (sub_branch f branch) = f ` branch_nominals branch\<close>
  unfolding branch_nominals_def sub_branch_def
  by (induct branch) (auto simp: sub_block_nominals)

lemma sub_list_id: \<open>sub_list id ps = ps\<close>
  using sub_id by (induct ps) auto

lemma sub_block_id: \<open>sub_block id block = block\<close>
  using sub_list_id by (induct block) auto

lemma sub_branch_id: \<open>sub_branch id branch = branch\<close>
  unfolding sub_branch_def using sub_block_id by (induct branch) auto

lemma sub_block_upd_fresh:
  assumes \<open>i \<notin> block_nominals block\<close>
  shows \<open>sub_block (f(i := j)) block = sub_block f block\<close>
  using assms by (induct block) (auto simp add: sub_upd_fresh)

lemma sub_branch_upd_fresh:
  assumes \<open>i \<notin> branch_nominals branch\<close>
  shows \<open>sub_branch (f(i := j)) branch = sub_branch f branch\<close>
  using assms unfolding branch_nominals_def sub_branch_def
  by (induct branch) (auto simp: sub_block_upd_fresh)

lemma sub_comp: \<open>sub f (sub g p) = sub (f o g) p\<close>
  by (induct p) simp_all

lemma sub_list_comp: \<open>sub_list f (sub_list g ps) = sub_list (f o g) ps\<close>
  using sub_comp by (induct ps) auto

lemma sub_block_comp: \<open>sub_block f (sub_block g block) = sub_block (f o g) block\<close>
  using sub_list_comp by (induct block) simp_all

lemma sub_branch_comp:
  \<open>sub_branch f (sub_branch g branch) = sub_branch (f o g) branch\<close>
  unfolding sub_branch_def using sub_block_comp by (induct branch) fastforce+

lemma swap_id: \<open>(id(i := j, j := i)) o (id(i := j, j := i)) = id\<close>
  by auto

lemma at_in_sub_branch:
  assumes \<open>p at i in (ps, a) # branch\<close>
  shows \<open>sub f p at f i in (sub_list f ps, f a) # sub_branch f branch\<close>
  using assms sub_branch_mem by fastforce

text \<open>
  If a branch has a closing tableau then so does any branch obtained by renaming nominals.
  Since some formulas on the renamed branch may no longer be new, they do not contribute
    any fuel and so we existentially quantify over the fuel needed to close the new branch.
\<close>

lemma ST_sub':
  fixes f :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>\<And>(f :: 'b \<Rightarrow> 'c) i A. finite A \<Longrightarrow> i \<notin> A \<Longrightarrow> \<exists>j. j \<notin> f ` A\<close>
  shows \<open>n \<turnstile> branch \<Longrightarrow> \<turnstile> sub_branch f branch\<close>
proof (induct branch arbitrary: f rule: ST.induct)
  case (Close p i branch)
  have \<open>sub f p at f i in sub_branch f branch\<close>
    using Close(1) sub_branch_mem by fastforce
  moreover have \<open>(\<^bold>\<not> sub f p) at f i in sub_branch f branch\<close>
    using Close(2) sub_branch_mem by force
  ultimately show ?case
    using ST.Close by fast
next
  case (Neg p a ps branch n)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(\<^bold>\<not> \<^bold>\<not> sub f p) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using Neg(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(3))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using Neg' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (DisP p q a ps branch n)
  then have
    \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    \<open>\<turnstile> (sub f q # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp_all
  moreover have \<open>(sub f p \<^bold>\<or> sub f q) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using DisP(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(4))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using DisP'' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (DisN p q a ps branch n)
  then have \<open>\<turnstile> ((\<^bold>\<not> sub f q) # (\<^bold>\<not> sub f p) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(\<^bold>\<not> (sub f p \<^bold>\<or> sub f q)) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using DisN(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(3-4))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using DisN' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (DiaP p a ps branch i n)
  show ?case
  proof (cases \<open>witnessed (sub f p) (f a) (sub_branch f ((ps, a) # branch))\<close>)
    case True
    then obtain i' where
      rs: \<open>(\<^bold>@ i' (sub f p)) at f a in (sub_list f ps, f a) # sub_branch f branch\<close> and
      ts: \<open>(\<^bold>\<diamond> Nom i') at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
      unfolding sub_branch_def witnessed_def by auto
    from rs have rs':
      \<open>(\<^bold>@ i' (sub f p)) at f a in ((\<^bold>\<diamond> Nom i') # sub_list f ps, f a) # sub_branch f branch\<close>
      by fastforce

    let ?f = \<open>f(i := i')\<close>
    let ?branch = \<open>sub_branch ?f branch\<close>
    have \<open>sub_branch ?f ((ps, a) # branch) = sub_branch f ((ps, a) # branch)\<close>
      using DiaP(2) sub_branch_upd_fresh by fast
    then have **: \<open>sub_list ?f ps = sub_list f ps\<close> \<open>?f a = f a\<close> \<open>?branch = sub_branch f branch\<close>
      unfolding sub_branch_def by simp_all

    have p: \<open>sub ?f p = sub f p\<close>
      using DiaP(1-2) sub_upd_fresh unfolding branch_nominals_def by fastforce

    have \<open>\<turnstile> ((\<^bold>@ (?f i) (sub ?f p)) # (\<^bold>\<diamond> Nom (?f i)) # sub_list ?f ps, ?f a) # ?branch\<close>
      using DiaP(6)[where f=\<open>?f\<close>] unfolding sub_branch_def by simp
    then have \<open>\<turnstile> ((\<^bold>@ i' (sub f p)) # (\<^bold>\<diamond> Nom i') # sub_list f ps, f a) # sub_branch f branch\<close>
      using p ** by simp
    then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom i') # sub_list f ps, f a) # sub_branch f branch\<close>
      using rs' by (meson Nom' on.simps)
    then have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
      using ts by (meson Nom' on.simps)
    then show ?thesis
      unfolding sub_branch_def by auto
  next
    case False
    have \<open>finite (branch_nominals ((ps, a) # branch))\<close>
      by (simp add: finite_branch_nominals)
    then obtain j where *: \<open>j \<notin> f ` branch_nominals ((ps, a) # branch)\<close>
      using DiaP(2) assms by blast

    let ?f = \<open>f(i := j)\<close>
    let ?branch = \<open>sub_branch ?f branch\<close>
    have **: \<open>sub_branch ?f ((ps, a) # branch) = sub_branch f ((ps, a) # branch)\<close>
      using DiaP(2) sub_branch_upd_fresh by fast
    then have ***: \<open>sub_list ?f ps = sub_list f ps\<close> \<open>?f a = f a\<close> \<open>?branch = sub_branch f branch\<close>
      unfolding sub_branch_def by simp_all
    moreover have p: \<open>sub ?f p = sub f p\<close>
      using DiaP(1-2) sub_upd_fresh unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<not> witnessed (sub ?f p) (?f a) (sub_branch ?f ((ps, a) # branch))\<close>
      using False ** by simp
    then have w: \<open>\<not> witnessed (sub ?f p) (?f a) ((sub_list ?f ps, ?f a) # ?branch)\<close>
      unfolding sub_branch_def by simp

    have \<open>\<turnstile> ((\<^bold>@ (?f i) (sub ?f p)) # (\<^bold>\<diamond> Nom (?f i)) # sub_list ?f ps, ?f a) # ?branch\<close>
      using DiaP(6)[where f=\<open>?f\<close>] ST_Suc unfolding sub_branch_def by simp
    moreover have \<open>sub ?f (\<^bold>\<diamond> p) at ?f a in (sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
      using DiaP(1) at_in_sub_branch by fast
    then have \<open>(\<^bold>\<diamond> sub ?f p) at ?f a in (sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
      by simp
    moreover have \<open>\<nexists>a. sub ?f p = Nom a\<close>
      using DiaP(3) by (cases p) simp_all
    moreover have \<open>?f i \<notin> branch_nominals ((sub_list ?f ps, ?f a) # ?branch)\<close>
      using * ** sub_branch_nominals unfolding sub_branch_def
      by (metis fun_upd_same list.simps(9) sub_block.simps)
    ultimately have \<open>\<turnstile> (sub_list ?f ps, ?f a) # ?branch\<close>
      using w ST.DiaP ST_Suc by fast
    then show ?thesis
      using *** unfolding sub_branch_def by simp
  qed
next
  case (DiaN p a ps branch i n)
  then have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ (f i) (sub f p))) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(\<^bold>\<not> (\<^bold>\<diamond> sub f p)) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using DiaN(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(3, 5))
  moreover have \<open>(\<^bold>\<diamond> Nom (f i)) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using DiaN(2) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(2, 5))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using DiaN' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (SatP a p b ps branch n)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(\<^bold>@ (f a) (sub f p)) at f b in (sub_list f ps, f a) # sub_branch f branch\<close>
    using SatP(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(6))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using SatP' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (SatN a p b ps branch n)
  then have \<open>\<turnstile> ((\<^bold>\<not> sub f p) # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>(\<^bold>\<not> (\<^bold>@ (f a) (sub f p))) at f b in (sub_list f ps, f a) # sub_branch f branch\<close>
    using SatN(1) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(3, 6))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using SatN' by fast
  then show ?case
    unfolding sub_branch_def by simp
next
  case (GoTo i branch n)
  then have \<open>\<turnstile> ([], f i) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>f i \<in> branch_nominals (sub_branch f branch)\<close>
    using GoTo(1) sub_branch_nominals by fast
  ultimately show ?case
    using ST.GoTo by fast
next
  case (Nom p b ps a branch i n)
  then have \<open>\<turnstile> (sub f p # sub_list f ps, f a) # sub_branch f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>sub f p at f b in (sub_list f ps, f a) # sub_branch f branch\<close>
    using Nom(1) at_in_sub_branch by fast
  moreover have \<open>Nom (f i) at f b in (sub_list f ps, f a) # sub_branch f branch\<close>
    using Nom(2) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(2))
  moreover have \<open>Nom (f i) at f a in (sub_list f ps, f a) # sub_branch f branch\<close>
    using Nom(3) at_in_sub_branch by (metis (no_types, hide_lams) sub.simps(2))
  ultimately have \<open>\<turnstile> (sub_list f ps, f a) # sub_branch f branch\<close>
    using Nom' by fast
  then show ?case
    unfolding sub_branch_def by simp
qed

lemma ex_fresh_gt:
  fixes f :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>\<exists>g :: 'c \<Rightarrow> 'b. surj g\<close> \<open>finite A\<close> \<open>i \<notin> A\<close>
  shows \<open>\<exists>j. j \<notin> f ` A\<close>
proof (rule ccontr)
  assume \<open>\<nexists>j. j \<notin> f ` A\<close>
  moreover obtain g :: \<open>'c \<Rightarrow> 'b\<close> where \<open>surj g\<close>
    using assms(1) by blast
  ultimately show False
    using assms(2-3)
    by (metis UNIV_I UNIV_eq_I card_image_le card_seteq finite_imageI image_comp subsetI)
qed

corollary ST_sub_gt:
  fixes f :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>\<exists>g :: 'c \<Rightarrow> 'b. surj g\<close> \<open>\<turnstile> branch\<close>
  shows \<open>\<turnstile> sub_branch f branch\<close>
  using assms ex_fresh_gt ST_sub' by metis

corollary ST_sub_inf:
  fixes f :: \<open>'b \<Rightarrow> 'c\<close>
  assumes \<open>infinite (UNIV :: 'c set)\<close> \<open>n \<turnstile> branch\<close>
  shows \<open>\<turnstile> sub_branch f branch\<close>
proof -
  have \<open>finite A \<Longrightarrow> \<exists>j. j \<notin> f ` A\<close> for A and f :: \<open>'b \<Rightarrow> 'c\<close>
    using assms(1) ex_new_if_finite by blast
  then show ?thesis
    using assms(2) ST_sub' by metis
qed

corollary ST_sub:
  fixes f :: \<open>'b \<Rightarrow> 'b\<close>
  assumes \<open>\<turnstile> branch\<close>
  shows \<open>\<turnstile> sub_branch f branch\<close>
proof -
  have \<open>finite A \<Longrightarrow> i \<notin> A \<Longrightarrow> \<exists>j. j \<notin> f ` A\<close> for i A and f :: \<open>'b \<Rightarrow> 'b\<close>
    by (metis card_image_le card_seteq finite_imageI subsetI)
  then show ?thesis
    using assms ST_sub' by metis
qed

subsection \<open>Unrestricted \<open>(\<^bold>\<diamond>)\<close> rule\<close>

lemma DiaP':
  assumes
    \<open>(\<^bold>\<diamond> p) at a in (ps, a) # branch\<close>
    \<open>\<nexists>a. p = Nom a\<close> \<open>i \<notin> branch_nominals ((ps, a) # branch)\<close>
    \<open>\<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch\<close>
  shows \<open>\<turnstile> (ps, a) # branch\<close>
proof (cases \<open>witnessed p a ((ps, a) # branch)\<close>)
  case True
  then obtain i' where
    rs: \<open>(\<^bold>@ i' p) at a in (ps, a) # branch\<close> and
    ts: \<open>(\<^bold>\<diamond> Nom i') at a in (ps, a) # branch\<close>
    unfolding witnessed_def by blast
  then have rs':
    \<open>(\<^bold>@ i' p) at a in ((\<^bold>\<diamond> Nom i') # ps, a) # branch\<close>
    by fastforce

  let ?f = \<open>id(i := i')\<close>
  have \<open>\<turnstile> sub_branch ?f (((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # branch)\<close>
    using assms(4) ST_sub by blast
  then have \<open>\<turnstile> ((\<^bold>@ i' (sub ?f p)) # (\<^bold>\<diamond> Nom i') # sub_list ?f ps, ?f a) # sub_branch ?f branch\<close>
    unfolding sub_branch_def by simp
  moreover have \<open>i \<notin> nominals p\<close> \<open>i \<notin> list_nominals ps\<close> \<open>i \<noteq> a\<close> \<open>i \<notin> branch_nominals branch\<close>
    using assms(1-3) unfolding branch_nominals_def by fastforce+
  then have \<open>sub ?f p = p\<close>
    by (simp add: sub_id sub_upd_fresh)
  moreover have \<open>sub_list ?f ps = ps\<close>
    using \<open>i \<notin> list_nominals ps\<close> by (simp add: map_idI sub_id sub_upd_fresh)
  moreover have \<open>?f a = a\<close>
    using \<open>i \<noteq> a\<close> by simp
  moreover have \<open>sub_branch ?f branch = branch\<close>
    using \<open>i \<notin> branch_nominals branch\<close> by (simp add: sub_branch_id sub_branch_upd_fresh)
  ultimately have \<open>\<turnstile> ((\<^bold>@ i' p) # (\<^bold>\<diamond> Nom i') # ps, a) # branch\<close>
    by simp
  then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom i') # ps, a) # branch\<close>
    using rs' by (meson Nom' on.simps)
  then show ?thesis
    using ts by (meson Nom' on.simps)
next
  case False
  then show ?thesis
    using assms DiaP ST_Suc by fast
qed

section \<open>Structural Properties\<close>

lemma block_nominals_branch:
  assumes \<open>block \<in>. branch\<close>
  shows \<open>block_nominals block \<subseteq> branch_nominals branch\<close>
  unfolding branch_nominals_def using assms by blast

lemma sub_block_fresh:
  assumes \<open>i \<notin> branch_nominals branch\<close> \<open>block \<in>. branch\<close>
  shows \<open>sub_block (f(i := j)) block = sub_block f block\<close>
  using assms block_nominals_branch sub_block_upd_fresh by fast

lemma list_down_induct [consumes 1, case_names Start Cons]:
  assumes \<open>\<forall>y \<in> set ys. Q y\<close> \<open>P (ys @ xs)\<close>
    \<open>\<And>y xs. Q y \<Longrightarrow> P (y # xs) \<Longrightarrow> P xs\<close>
  shows \<open>P xs\<close>
  using assms by (induct ys) auto

text \<open>
  If the last block on a branch has opening nominal \<open>a\<close> and the last formulas on that block
   occur on another block alongside nominal \<open>a\<close>, then we can drop those formulas.
\<close>

lemma ST_drop_prefix:
  assumes \<open>set ps \<subseteq> set qs\<close> \<open>(qs, a) \<in>. branch\<close> \<open>n \<turnstile> (ps @ ps', a) # branch\<close>
  shows \<open>n \<turnstile> (ps', a) # branch\<close>
proof -
  have \<open>\<forall>p \<in> set ps. p on (qs, a)\<close>
    using assms(1) by auto
  then show ?thesis
  proof (induct ps' rule: list_down_induct)
    case Start
    then show ?case
      using assms(3) .
  next
    case (Cons p ps)
    then show ?case
      using assms(2) by (meson Nom' list.set_intros(2) on.simps)
  qed
qed

text \<open>We can drop a block if it is subsumed by another block.\<close>

lemma ST_drop_block:
  assumes
    \<open>set ps \<subseteq> set ps'\<close> \<open>(ps', a) \<in>. branch\<close>
    \<open>n \<turnstile> (ps, a) # branch\<close>
  shows \<open>Suc n \<turnstile> branch\<close>
  using assms
proof (induct branch)
  case Nil
  then show ?case
    by simp
next
  case (Cons block branch)
  then show ?case
  proof (cases block)
    case (Pair qs b)
    then have \<open>n \<turnstile> ([], a) # (qs, b) # branch\<close>
      using Cons(2-4) ST_drop_prefix[where branch=\<open>(qs, b) # branch\<close>] by simp
    moreover have \<open>a \<in> branch_nominals ((qs, b) # branch)\<close>
      unfolding branch_nominals_def using Cons(3) Pair by fastforce
    ultimately have \<open>Suc n \<turnstile> (qs, b) # branch\<close>
      by (simp add: GoTo)
    then show ?thesis
      using Pair Dup by fast
  qed
qed

lemma ST_drop_block':
  assumes \<open>n \<turnstile> (ps, a) # branch\<close> \<open>(ps, a) \<in>. branch\<close>
  shows \<open>Suc n \<turnstile> branch\<close>
  using assms ST_drop_block by fastforce

lemma sub_branch_image: \<open>set (sub_branch f branch) = sub_block f ` set branch\<close>
  unfolding sub_branch_def by simp

lemma sub_block_repl:
  assumes \<open>j \<notin> block_nominals block\<close>
  shows \<open>i \<notin> block_nominals (sub_block (id(i := j, j := i)) block)\<close>
  using assms by (simp add: image_iff sub_block_nominals)

lemma sub_branch_repl:
  assumes \<open>j \<notin> branch_nominals branch\<close>
  shows \<open>i \<notin> branch_nominals (sub_branch (id(i := j, j := i)) branch)\<close>
  using assms by (simp add: image_iff sub_branch_nominals)

text \<open>If a finite set of blocks has a closing tableau then so does any finite superset.\<close>

lemma ST_struct:
  fixes branch :: \<open>('a, 'b) branch\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>n \<turnstile> branch\<close> \<open>set branch \<subseteq> set branch'\<close>
  shows \<open>\<turnstile> branch'\<close>
  using assms(2-3)
proof (induct n branch arbitrary: branch' rule: ST.induct)
  case (Close p i branch)
  then show ?case
    using ST.Close by fast
next
  case (Neg p a ps branch n)
  have \<open>\<turnstile> (p # ps, a) # branch'\<close>
    using Neg(4-5) by (simp add: subset_code(1))
  moreover have \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps, a) # branch'\<close>
    using Neg(1, 5) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using Neg' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using Neg(5) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (DisP p q a ps branch)
  have \<open>\<turnstile> (p # ps, a) # branch'\<close> \<open>\<turnstile> (q # ps, a) # branch'\<close>
    using DisP(5, 7-8) by (simp_all add: subset_code(1))
  moreover have \<open>(p \<^bold>\<or> q) at a in (ps, a) # branch'\<close>
    using DisP(1, 8) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using DisP'' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using DisP(8) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (DisN p q a ps branch n)
  have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a)# branch'\<close>
    using DisN(4-5) by (simp add: subset_code(1))
  moreover have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps, a) # branch'\<close>
    using DisN(1, 5) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using DisN' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using DisN(5) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (DiaP p a ps branch i n)
  have \<open>finite (branch_nominals branch')\<close>
    by (simp add: finite_branch_nominals)
  then obtain j where j: \<open>j \<notin> branch_nominals branch'\<close>
    using assms ex_new_if_finite by blast
  then have j': \<open>j \<notin> branch_nominals ((ps, a) # branch)\<close>
    using DiaP(7) unfolding branch_nominals_def by blast

  let ?f = \<open>id(i := j, j := i)\<close>
  let ?branch' = \<open>sub_branch ?f branch'\<close>
  have branch': \<open>sub_branch ?f ?branch' = branch'\<close>
    using sub_branch_comp sub_branch_id swap_id by metis

  have branch: \<open>sub_branch ?f ((ps, a) # branch) = (ps, a) # branch\<close>
    using DiaP(2) j' sub_branch_id sub_branch_upd_fresh by metis
  moreover have
    \<open>set (sub_branch ?f ((ps, a) # branch)) \<subseteq> set ?branch'\<close>
    using DiaP(7) sub_branch_image by blast
  ultimately have *: \<open>set ((ps, a) # branch) \<subseteq> set ?branch'\<close>
    unfolding sub_branch_def by auto

  have \<open>i \<notin> block_nominals (ps, a)\<close>
    using DiaP unfolding branch_nominals_def by simp
  moreover have \<open>i \<notin> branch_nominals ?branch'\<close>
    using j sub_branch_repl by metis
  ultimately have i: \<open>i \<notin> branch_nominals ((ps, a) # ?branch')\<close>
    unfolding branch_nominals_def by simp

  have \<open>\<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ps, a) # ?branch'\<close>
    using DiaP(6) *
    by (metis (no_types, lifting) subset_code(1) insert_mono list.set(2) set_subset_Cons)
  moreover have \<open>(\<^bold>\<diamond> p) at a in (ps, a) # ?branch'\<close>
    using DiaP(1, 7) * by (meson set_subset_Cons subset_code(1))
  ultimately have \<open>\<turnstile> (ps, a) # ?branch'\<close>
    using inf DiaP(3) i DiaP' by metis
  then have \<open>\<turnstile> sub_branch ?f ((ps, a) # ?branch')\<close>
    using ST_sub by blast
  then have \<open>\<turnstile> (ps, a) # branch'\<close>
    using branch' branch unfolding sub_branch_def by simp
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using \<open>set ((ps, a) # branch) \<subseteq> set branch'\<close> by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (DiaN p a ps branch i n)
  have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps, a) # branch'\<close>
    using DiaN(5-6) by (simp add: subset_code(1))
  moreover have
    \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps, a) # branch'\<close>
    \<open>(\<^bold>\<diamond> Nom i) at a in (ps, a) # branch'\<close>
    using DiaN(1-2, 6) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using DiaN' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using DiaN(6) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (SatP a p b ps branch n)
  have \<open>\<turnstile> (p # ps, a) # branch'\<close>
    using SatP(4-5) by (simp add: subset_code(1))
  moreover have \<open>(\<^bold>@ a p) at b in (ps, a) # branch'\<close>
    using SatP(1, 5) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using SatP' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using SatP(5) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (SatN a p b ps branch n)
  have\<open>\<turnstile> ((\<^bold>\<not> p) # ps, a) # branch'\<close>
    using SatN(4-5) by (simp add: subset_code(1))
  moreover have \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps, a) # branch'\<close>
    using SatN(1, 5) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using SatN' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using SatN(5) by simp
  ultimately show ?case
    using ST_drop_block' by fast
next
  case (GoTo i branch n)
  then have \<open>\<turnstile> ([], i) # branch'\<close>
    by (simp add: subset_code(1))
  moreover have \<open>i \<in> branch_nominals branch'\<close>
    using GoTo(1, 4) unfolding branch_nominals_def by auto
  ultimately show ?case
    using GoTo(2) ST.GoTo by fast
next
  case (Nom p b ps a branch i n)
  have \<open>\<turnstile> (p # ps, a) # branch'\<close>
    using Nom(6-7) by (simp add: subset_code(1))
  moreover have \<open>p at b in (ps, a) # branch'\<close>
    using Nom(1, 7) by auto
  moreover have \<open>Nom i at b in (ps, a) # branch'\<close>
    using Nom(2, 7) by auto
  moreover have \<open>Nom i at a in (ps, a) # branch'\<close>
    using Nom(3, 7) by auto
  ultimately have \<open>\<turnstile> (ps, a) # branch'\<close>
    using Nom' by fast
  moreover have \<open>(ps, a) \<in>. branch'\<close>
    using Nom(7) by simp
  ultimately show ?case
    using ST_drop_block' by fast
qed

text \<open>
  If a branch has a closing tableau then we can replace the formulas of the last block
  on that branch with any finite superset and still obtain a closing tableau.
\<close>

lemma ST_struct_block:
  fixes branch :: \<open>('a, 'b) branch\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>n \<turnstile> (ps, a) # branch\<close> \<open>set ps \<subseteq> set ps'\<close>
  shows \<open>\<turnstile> (ps', a) # branch\<close>
  using assms(2-3)
proof (induct \<open>(ps, a) # branch\<close> arbitrary: ps ps' rule: ST.induct)
  case (Close p i n ts ts')
  then have \<open>p at i in (ts', a) # branch\<close> \<open>(\<^bold>\<not> p) at i in (ts', a) # branch\<close>
    by auto
  then show ?case
    using ST.Close by fast
next
  case (Neg p ps n)
  then have \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> (p # ps', a) # branch\<close>
    using Neg(4-5) by (simp add: subset_code(1))
  ultimately show ?case
    using Neg' by fast
next
  case (DisP p q ps n)
  then have \<open>(p \<^bold>\<or> q) at a in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> (p # ps', a) # branch\<close> \<open>\<turnstile> (q # ps', a) # branch\<close>
    using DisP(5, 7-8) by (simp_all add: subset_code(1))
  ultimately show ?case
    using DisP'' by fast
next
  case (DisN p q ps n)
  then have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps', a) # branch\<close>
    using DisN(4-5) by (simp add: subset_code(1))
  ultimately show ?case
    using DisN' by fast
next
  case (DiaP p ps i n)
  have \<open>finite (branch_nominals ((ps', a) # branch))\<close>
    using finite_branch_nominals by blast
  then obtain j where j: \<open>j \<notin> branch_nominals ((ps', a) # branch)\<close>
    using assms ex_new_if_finite by blast
  then have j': \<open>j \<notin> block_nominals (ps, a)\<close>
    using DiaP.prems unfolding branch_nominals_def by auto

  let ?f = \<open>id(i := j, j := i)\<close>
  let ?ps' = \<open>sub_list ?f ps'\<close>
  have ps': \<open>sub_list ?f ?ps' = ps'\<close>
    using sub_list_comp sub_list_id swap_id by metis

  have \<open>i \<notin> block_nominals (ps, a)\<close>
    using DiaP(1-2) unfolding branch_nominals_def by simp
  then have ps: \<open>sub_block ?f (ps, a) = (ps, a)\<close>
    using j' sub_block_id sub_block_upd_fresh by metis
  moreover have \<open>set (sub_list ?f ps) \<subseteq> set (sub_list ?f ps')\<close>
    using \<open>set ps \<subseteq> set ps'\<close> by auto
  ultimately have *: \<open>set ps \<subseteq> set ?ps'\<close>
    by simp

  have \<open>i \<notin> branch_nominals branch\<close>
    using DiaP unfolding branch_nominals_def by simp
  moreover have \<open>j \<notin> branch_nominals branch\<close>
    using j unfolding branch_nominals_def by simp
  ultimately have branch: \<open>sub_branch ?f branch = branch\<close>
    using sub_branch_id sub_branch_upd_fresh by metis

  have \<open>i \<noteq> a\<close> \<open>j \<noteq> a\<close>
    using DiaP j unfolding branch_nominals_def by simp_all
  then have \<open>?f a = a\<close>
    by simp
  moreover have \<open>j \<notin> block_nominals (ps', a)\<close>
    using j unfolding branch_nominals_def by simp
  ultimately have \<open>i \<notin> block_nominals (?ps', a)\<close>
    using sub_block_repl[where block=\<open>(ps', a)\<close> and i=i and j=j] by simp

  have \<open>(\<^bold>\<diamond> p) at a in (?ps', a) # branch\<close>
    using DiaP(1) * by fastforce
  moreover have \<open>\<turnstile> ((\<^bold>@ i p) # (\<^bold>\<diamond> Nom i) # ?ps', a) # branch\<close>
    using * DiaP(6) by (simp add: subset_code(1))
  moreover have \<open>i \<notin> branch_nominals ((?ps', a) # branch)\<close>
    using DiaP(2) \<open>i \<notin> block_nominals (?ps', a)\<close> unfolding branch_nominals_def by simp
  ultimately have \<open>\<turnstile> (?ps', a) # branch\<close>
    using DiaP(3) DiaP' by fast
  then have \<open>\<turnstile> sub_branch ?f ((?ps', a) # branch)\<close>
    using ST_sub by blast
  then have \<open>\<turnstile> (sub_list ?f ?ps', ?f a) # sub_branch ?f branch\<close>
    unfolding sub_branch_def by simp
  then show ?case
    using \<open>?f a = a\<close> ps' branch by simp
next
  case (DiaN p ps i n)
  then have
    \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (ps', a) # branch\<close>
    \<open>(\<^bold>\<diamond> Nom i) at a in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ i p)) # ps', a) # branch\<close>
    using DiaN(5-6) by (simp add: subset_code(1))
  ultimately show ?case
    using DiaN' by fast
next
  case (SatP p b ps n)
  then have \<open>(\<^bold>@ a p) at b in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> (p # ps', a) # branch\<close>
    using SatP(4-5) by (simp add: subset_code(1))
  ultimately show ?case
    using SatP' by fast
next
  case (SatN p b ps n)
  then have \<open>(\<^bold>\<not> (\<^bold>@ a p)) at b in (ps', a) # branch\<close>
    by auto
  moreover have \<open>\<turnstile> ((\<^bold>\<not> p) # ps', a) # branch\<close>
    using SatN(4-5) by (simp add: subset_code(1))
  ultimately show ?case
    using SatN' by fast
next
  case (GoTo i n ps)
  then have \<open>Suc n \<turnstile> (ps, a) # branch\<close>
    using ST.GoTo by fast
  then obtain m where \<open>m \<turnstile> (ps, a) # (ps', a) # branch\<close>
    using inf ST_struct[where branch'=\<open>(ps, a) # _ # _\<close>] by fastforce
  then have \<open>Suc m \<turnstile> (ps', a) # branch\<close>
    using GoTo(4) by (simp add: ST_drop_block[where a=a])
  then show ?case
    by blast
next
  case (Nom p b ps i)
  have \<open>p at b in (ps', a) # branch\<close>
    using Nom(1, 7) by auto
  moreover have \<open>Nom i at b in (ps', a) # branch\<close>
    using Nom(2, 7) by auto
  moreover have \<open>Nom i at a in (ps', a) # branch\<close>
    using Nom(3, 7) by auto
  moreover have \<open>\<turnstile> (p # ps', a) # branch\<close>
    using Nom(6-7) by (simp add: subset_code(1))
  ultimately show ?case
    using Nom' by fast
qed

section \<open>Unrestricted \<open>(\<^bold>@)\<close> and \<open>(\<^bold>\<not> \<^bold>@)\<close> rules\<close>

text \<open>We can derive more general versions of the \<open>(\<^bold>@)\<close> and \<open>(\<^bold>\<not> \<^bold>@)\<close> rules using weakening and \<open>Nom\<close>.\<close>

lemma SatP'':
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>(\<^bold>@ i p) at b in (ps, a) # branch\<close>
    \<open>Nom i at a in (ps, a) # branch\<close>
    \<open>\<turnstile> (p # ps, a) # branch\<close>
  shows \<open>\<turnstile> (ps, a) # branch\<close>
proof -
  have \<open>i \<in> branch_nominals ((ps, a) # branch)\<close>
    using assms(2) unfolding branch_nominals_def by fastforce
  then have ?thesis if \<open>\<turnstile> ([], i) # (ps, a) # branch\<close>
    using that GoTo by fast
  then have ?thesis if \<open>\<turnstile> ([Nom a], i) # (ps, a) # branch\<close>
    using that assms(3) by (meson Nom' list.set_intros(1) on.simps set_subset_Cons subsetD)
  then have ?thesis if \<open>\<turnstile> ([p, Nom a], i) # (ps, a) # branch\<close>
    using that assms(2) by (meson SatP' set_subset_Cons subsetD)
  then have ?thesis if \<open>\<turnstile> (ps, a) # ([p, Nom a], i) # branch\<close>
    using that inf ST_struct[where branch'=\<open>([p, Nom a], i) # (ps, a) # branch\<close>] by fastforce
  then have ?thesis if \<open>\<turnstile> (p # ps, a) # ([p, Nom a], i) # branch\<close>
    using that by (meson Nom' list.set_intros(1) on.simps set_subset_Cons subsetD)
  then show ?thesis
    using inf assms(4) ST_struct[where branch'=\<open>(p # ps, a) # ([p, Nom a], i) # branch\<close>]
    by fastforce
qed

lemma SatN'':
  fixes i :: 'b
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>(\<^bold>\<not> (\<^bold>@ i p)) at b in (ps, a) # branch\<close>
    \<open>Nom i at a in (ps, a) # branch\<close>
    \<open>\<turnstile> ((\<^bold>\<not> p) # ps, a) # branch\<close>
  shows \<open>\<turnstile> (ps, a) # branch\<close>
proof -
  have \<open>i \<in> branch_nominals ((ps, a) # branch)\<close>
    using assms(2) unfolding branch_nominals_def by fastforce
  then have ?thesis if \<open>\<turnstile> ([], i) # (ps, a) # branch\<close>
    using that GoTo by fast
  then have ?thesis if \<open>\<turnstile> ([Nom a], i) # (ps, a) # branch\<close>
    using that assms(3) by (meson Nom' list.set_intros(1) on.simps set_subset_Cons subsetD)
  then have ?thesis if \<open>\<turnstile> ([\<^bold>\<not> p, Nom a], i) # (ps, a) # branch\<close>
    using that assms(2) by (meson SatN' set_subset_Cons subsetD)
  then have ?thesis if \<open>\<turnstile> (ps, a) # ([\<^bold>\<not> p, Nom a], i) # branch\<close>
    using that inf ST_struct[where branch'=\<open>([\<^bold>\<not> p, Nom a], i) # (ps, a) # branch\<close>] by fastforce
  then have ?thesis if \<open>\<turnstile> ((\<^bold>\<not> p) # ps, a) # ([\<^bold>\<not> p, Nom a], i) # branch\<close>
    using that by (meson Nom' list.set_intros(1) on.simps set_subset_Cons subsetD)
  then show ?thesis
    using inf assms(4) ST_struct[where branch'=\<open>((\<^bold>\<not> p) # ps, a) # ([\<^bold>\<not> p, Nom a], i) # branch\<close>]
    by fastforce
qed

section \<open>Bridge\<close>

text \<open>
  We are going to define a \<open>descendants k i branch\<close> relation on sets of indices.
  The sets are built on the index of a \<open>\<^bold>\<diamond> Nom k\<close> on an \<open>i\<close>-block in \<open>branch\<close> and can be extended
    by indices of formula occurrences that can be thought of as descending from
    that \<open>\<^bold>\<diamond> Nom k\<close> by application of either the \<open>(\<^bold>\<not> \<^bold>\<diamond>)\<close> or \<open>Nom\<close> rule.

  We will show that if we have nominals \<open>j\<close> and \<open>k\<close> on the same block in a closeable branch,
  then the branch obtained by the following transformation is also closeable:
  For every index \<open>v\<close>, if the formula at \<open>v\<close> is \<open>\<^bold>\<diamond> Nom k\<close>, replace it by \<open>\<^bold>\<diamond> Nom j\<close> and
    if it is \<open>\<^bold>\<not> (\<^bold>@ k p)\<close> replace it by \<open>\<^bold>\<not> (\<^bold>@ j p)\<close>.
  There are no other cases.

  From this transformation we can derive the Bridge rule.
\<close>

subsection \<open>Replacing\<close>

abbreviation bridge' :: \<open>'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm\<close> where
  \<open>bridge' k j p \<equiv> case p of
    (\<^bold>\<diamond> Nom k') \<Rightarrow> (if k = k' then (\<^bold>\<diamond> Nom j) else (\<^bold>\<diamond> Nom k'))
  | (\<^bold>\<not> (\<^bold>@ k' q)) \<Rightarrow> (if k = k' then (\<^bold>\<not> (\<^bold>@ j q)) else (\<^bold>\<not> (\<^bold>@ k' q)))
  | p \<Rightarrow> p\<close>

abbreviation bridge ::
  \<open>'b \<Rightarrow> 'b \<Rightarrow> (nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) fm \<Rightarrow> ('a, 'b) fm\<close> where
  \<open>bridge k j \<equiv> mapper (bridge' k j)\<close>

lemma bridge_on_Nom:
  \<open>Nom i on (ps, a) \<Longrightarrow> Nom i on (mapi (bridge k j xs v) ps, a)\<close>
  by (induct ps) auto

lemma bridge'_nominals:
  \<open>nominals (bridge' k j p) \<union> {k, j} = nominals p \<union> {k, j}\<close>
proof (induct p)
  case (Neg p)
  then show ?case by (cases p) auto
next
  case (Dia p)
  then show ?case by (cases p) auto
qed auto

lemma bridge_nominals:
  \<open>nominals (bridge k j xs v v' p) \<union> {k, j} = nominals p \<union> {k, j}\<close>
proof (cases \<open>(v, v') \<in> xs\<close>)
  case True
  then have \<open>nominals (bridge k j xs v v' p) = nominals (bridge' k j p)\<close>
    by simp
  then show ?thesis
    using bridge'_nominals by metis
qed simp

lemma bridge_block_nominals:
  \<open>block_nominals (mapi_block (bridge k j xs v) (ps, a)) \<union> {k, j} =
   block_nominals (ps, a) \<union> {k, j}\<close>
proof (induct ps)
  case Nil
  then show ?case
    by simp
next
  case (Cons p ps)
  have \<open>?case \<longleftrightarrow>
    (nominals (bridge k j xs v (length ps) p)) \<union>
    (block_nominals (mapi_block (bridge k j xs v) (ps, a)) \<union> {k, j}) =
    (nominals p) \<union> (block_nominals (ps, a) \<union> {k, j})\<close>
    by simp
  also have \<open>\<dots> \<longleftrightarrow>
    (nominals (bridge k j xs v (length ps) p) \<union> {k, j}) \<union>
    (block_nominals (mapi_block (bridge k j xs v) (ps, a)) \<union> {k, j}) =
    (nominals p \<union> {k, j}) \<union> (block_nominals (ps, a) \<union> {k, j})\<close>
    by blast
  moreover have
    \<open>nominals (bridge k j xs v (length ps) p) \<union> {k, j} = nominals p \<union> {k, j}\<close>
    using bridge_nominals by metis
  moreover note Cons
  ultimately show ?case
    by argo
qed

lemma bridge_branch_nominals:
  \<open>branch_nominals (mapi_branch (bridge k j xs) branch) \<union> {k, j} =
   branch_nominals branch \<union> {k, j}\<close>
proof (induct branch)
  case Nil
  then show ?case
    unfolding branch_nominals_def mapi_branch_def
    by simp
next
  case (Cons block branch)
  have \<open>?case \<longleftrightarrow>
    (block_nominals (mapi_block (bridge k j xs (length branch)) block)) \<union>
    (branch_nominals (mapi_branch (bridge k j xs) branch) \<union> {k, j}) =
    (block_nominals block) \<union> (branch_nominals branch \<union> {k, j})\<close>
    unfolding branch_nominals_def mapi_branch_def by simp
  also have \<open>\<dots> \<longleftrightarrow>
    (block_nominals (mapi_block (bridge k j xs (length branch)) block) \<union> {k, j}) \<union>
    (branch_nominals (mapi_branch (bridge k j xs) branch) \<union> {k, j}) =
    (block_nominals block \<union> {k, j}) \<union> (branch_nominals branch \<union> {k, j})\<close>
    by blast
  moreover have
    \<open>block_nominals (mapi_block (bridge k j xs (length branch)) block) \<union> {k, j} =
     block_nominals block \<union> {k, j}\<close>
    using bridge_block_nominals[where ps=\<open>fst block\<close> and a=\<open>snd block\<close>] by simp
  ultimately show ?case
    using Cons by argo
qed

lemma at_in_mapi_branch:
  assumes \<open>p at a in branch\<close> \<open>p \<noteq> Nom a\<close>
  shows \<open>\<exists>v v'. f v v' p at a in mapi_branch f branch\<close>
  using assms by (meson mapi_branch_mem rev_nth_mapi_block rev_nth_on)

lemma nom_at_in_bridge:
  fixes k j xs
  defines \<open>f \<equiv> bridge k j xs\<close>
  assumes \<open>Nom i at a in branch\<close>
  shows \<open>Nom i at a in mapi_branch f branch\<close>
proof -
  obtain qs where qs: \<open>(qs, a) \<in>. branch\<close> \<open>Nom i on (qs, a)\<close>
    using assms(2) by blast
  then obtain l where \<open>(mapi (f l) qs, a) \<in>. mapi_branch f branch\<close>
    using mapi_branch_mem by fast
  moreover have \<open>Nom i on (mapi (f l) qs, a)\<close>
    unfolding f_def using qs(2) by (induct qs) auto
  ultimately show ?thesis
    by blast
qed

lemma nominals_mapi_branch_bridge:
  assumes \<open>Nom j at a in branch\<close> \<open>Nom k at a in branch\<close>
  shows \<open>branch_nominals (mapi_branch (bridge k j xs) branch) = branch_nominals branch\<close>
proof -
  let ?f = \<open>bridge k j xs\<close>
  have \<open>Nom j at a in mapi_branch ?f branch\<close>
    using assms(1) nom_at_in_bridge by fast
  then have \<open>j \<in> branch_nominals (mapi_branch ?f branch)\<close>
    unfolding branch_nominals_def by fastforce
  moreover have \<open>Nom k at a in mapi_branch ?f branch\<close>
    using assms(2) nom_at_in_bridge by fast
  then have \<open>k \<in> branch_nominals (mapi_branch ?f branch)\<close>
    unfolding branch_nominals_def by fastforce
  moreover have \<open>j \<in> branch_nominals branch\<close> \<open>k \<in> branch_nominals branch\<close>
    using assms(1-2) unfolding branch_nominals_def by fastforce+
  moreover have
    \<open>branch_nominals (mapi_branch ?f branch) \<union> {k, j} = branch_nominals branch \<union> {k, j}\<close>
    using bridge_branch_nominals by metis
  ultimately show ?thesis
    by blast
qed

lemma bridge_proper_dia:
  assumes \<open>\<nexists>a. p = Nom a\<close>
  shows \<open>bridge k j xs v v' (\<^bold>\<diamond> p) = (\<^bold>\<diamond> p)\<close>
  using assms by (induct p) simp_all

lemma bridge_compl_cases:
  fixes k j xs v v' w w' p
  defines \<open>q \<equiv> bridge k j xs v v' p\<close> and \<open>q' \<equiv> bridge k j xs w w' (\<^bold>\<not> p)\<close>
  shows
    \<open>(q = (\<^bold>\<diamond> Nom j) \<and> q' = (\<^bold>\<not> (\<^bold>\<diamond> Nom k))) \<or>
 (\<exists>r. q = (\<^bold>\<not> (\<^bold>@ j r)) \<and> q' = (\<^bold>\<not> \<^bold>\<not> (\<^bold>@ k r))) \<or>
 (\<exists>r. q = (\<^bold>@ k r) \<and> q' = (\<^bold>\<not> (\<^bold>@ j r))) \<or>
     (q = p \<and> q' = (\<^bold>\<not> p))\<close>
proof (cases p)
  case (Neg p)
  then show ?thesis
    by (cases p) (simp_all add: q_def q'_def)
next
  case (Dia p)
  then show ?thesis
    by (cases p) (simp_all add: q_def q'_def)
qed (simp_all add: q_def q'_def)

subsection \<open>Descendants\<close>

inductive descendants :: \<open>'b \<Rightarrow> 'b \<Rightarrow> ('a, 'b) branch \<Rightarrow> (nat \<times> nat) set \<Rightarrow> bool\<close> where
  Initial:
  \<open>branch !. v = Some (qs, i) \<Longrightarrow> qs !. v' = Some (\<^bold>\<diamond> Nom k) \<Longrightarrow>
    descendants k i branch {(v, v')}\<close>
| Derived:
  \<open>branch !. v = Some (qs, a) \<Longrightarrow> qs !. v' = Some (\<^bold>\<not> (\<^bold>@ k p)) \<Longrightarrow>
    descendants k i branch xs \<Longrightarrow> (w, w') \<in> xs \<Longrightarrow>
    branch !. w = Some (rs, a) \<Longrightarrow> rs !. w' = Some (\<^bold>\<diamond> Nom k) \<Longrightarrow>
    descendants k i branch ({(v, v')} \<union> xs)\<close>
| Copied:
  \<open>branch !. v = Some (qs, a) \<Longrightarrow> qs !. v' = Some p \<Longrightarrow>
    descendants k i branch xs \<Longrightarrow> (w, w') \<in> xs \<Longrightarrow>
    branch !. w = Some (rs, b) \<Longrightarrow> rs !. w' = Some p \<Longrightarrow>
    Nom j at b in branch \<Longrightarrow> Nom j at a in branch \<Longrightarrow>
    descendants k i branch ({(v, v')} \<union> xs)\<close>

lemma descendants_initial:
  assumes \<open>descendants k i branch xs\<close>
  shows \<open>\<exists>(v, v') \<in> xs. \<exists>ps.
    branch !. v = Some (ps, i) \<and> ps !. v' = Some (\<^bold>\<diamond> Nom k)\<close>
  using assms by (induct k i branch xs rule: descendants.induct) simp_all

lemma descendants_bounds_fst:
  assumes \<open>descendants k i branch xs\<close> \<open>(v, v') \<in> xs\<close>
  shows \<open>v < length branch\<close>
  using assms rev_nth_Some
  by (induct k i branch xs rule: descendants.induct) fast+

lemma descendants_bounds_snd:
  assumes \<open>descendants k i branch xs\<close> \<open>(v, v') \<in> xs\<close> \<open>branch !. v = Some (ps, a)\<close>
  shows \<open>v' < length ps\<close>
  using assms
  by (induct k i branch xs rule: descendants.induct) (auto simp: rev_nth_Some)

lemma descendants_branch:
  \<open>descendants k i branch xs \<Longrightarrow> descendants k i (extra @ branch) xs\<close>
proof (induct k i branch xs rule: descendants.induct)
  case (Initial branch v qs i v' k)
  then show ?case
    using rev_nth_append descendants.Initial by fast
next
  case (Derived branch v qs a v' k p i xs w w' rs)
  then have
    \<open>(extra @ branch) !. v = Some (qs, a)\<close>
    \<open>(extra @ branch) !. w = Some (rs, a)\<close>
    using rev_nth_append by fast+
  then show ?case
    using Derived(2, 4-5, 7) descendants.Derived by fast
next
  case (Copied branch v qs a v' p k i xs w w' rs b j)
  then have
    \<open>(extra @ branch) !. v = Some (qs, a)\<close>
    \<open>(extra @ branch) !. w = Some (rs, b)\<close>
    using rev_nth_append by fast+
  moreover have \<open>Nom j at b in (extra @ branch)\<close> \<open>Nom j at a in (extra @ branch)\<close>
    using Copied(8-9) by auto
  ultimately show ?case
    using Copied(2-4, 5-7, 9) descendants.Copied by fast
qed

lemma descendants_block:
  assumes \<open>descendants k i ((ps, a) # branch) xs\<close>
  shows \<open>descendants k i ((ps' @ ps, a) # branch) xs\<close>
  using assms
proof (induct k i \<open>(ps, a) # branch\<close> xs arbitrary: ps a branch rule: descendants.induct)
  case (Initial v qs i v' k)
  have
    \<open>((ps' @ ps, a) # branch) !. v = Some (qs, i) \<or>
     ((ps' @ ps, a) # branch) !. v = Some (ps' @ qs, i)\<close>
    using Initial(1) by auto
  moreover have
    \<open>qs !. v' = Some (\<^bold>\<diamond> Nom k)\<close> \<open>(ps' @ qs) !. v' = Some (\<^bold>\<diamond> Nom k)\<close>
    using Initial(2) rev_nth_append by simp_all
  ultimately show ?case
    using descendants.Initial by fast
next
  case (Derived v qs a' v' k p i xs w w' rs)
  have
    \<open>((ps' @ ps, a) # branch) !. v = Some (qs, a') \<or>
     ((ps' @ ps, a) # branch) !. v = Some (ps' @ qs, a')\<close>
    using Derived(1) by auto
  moreover have
    \<open>qs !. v' = Some (\<^bold>\<not> (\<^bold>@ k p))\<close> \<open>(ps' @ qs) !. v' = Some (\<^bold>\<not> (\<^bold>@ k p))\<close>
    using Derived(2) rev_nth_append by simp_all
  moreover have
    \<open>((ps' @ ps, a) # branch) !. w = Some (rs, a') \<or>
     ((ps' @ ps, a) # branch) !. w = Some (ps' @ rs, a')\<close>
    using \<open>((ps, a) # branch) !. w = Some (rs, a')\<close> by auto
  moreover have
    \<open>rs !. w' = Some (\<^bold>\<diamond> Nom k)\<close> \<open>(ps' @ rs) !. w' = Some (\<^bold>\<diamond> Nom k)\<close>
    using Derived(7) rev_nth_append by simp_all
  ultimately show ?case
    using Derived(4-5) descendants.Derived by fast
next
  case (Copied v qs a' v' p k i xs w w' rs b j)
  have
    \<open>((ps' @ ps, a) # branch) !. v = Some (qs, a') \<or>
     ((ps' @ ps, a) # branch) !. v = Some (ps' @ qs, a')\<close>
    using Copied(1) by auto
  moreover have \<open>qs !. v' = Some p\<close> \<open>(ps' @ qs) !. v' = Some p\<close>
    using Copied(2) rev_nth_append by simp_all
  moreover have
    \<open>((ps' @ ps, a) # branch) !. w = Some (rs, b) \<or>
     ((ps' @ ps, a) # branch) !. w = Some (ps' @ rs, b)\<close>
    using Copied(6) by auto
  moreover have \<open>rs !. w' = Some p\<close> \<open>(ps' @ rs) !. w' = Some p\<close>
    using Copied(7) rev_nth_append by simp_all
  moreover have
    \<open>((ps' @ ps, a) # branch) !. w = Some (rs, b) \<or>
     ((ps' @ ps, a) # branch) !. w = Some (ps' @ rs, b)\<close>
    using Copied(6) by auto
  moreover have \<open>rs !. w' = Some p\<close> \<open>(ps' @ rs) !. w' = Some p\<close>
    using Copied(7) rev_nth_append by simp_all
  moreover have \<open>Nom j at b in (ps' @ ps, a) # branch\<close>
    using Copied(8) by fastforce
  moreover have \<open>Nom j at a' in (ps' @ ps, a) # branch\<close>
    using Copied(9) by fastforce
  ultimately show ?case
    using Copied(4-5) descendants.Copied[where branch=\<open>(ps' @ ps, a) # branch\<close>]
    by blast
qed

lemma descendants_no_head:
  assumes \<open>descendants k i ((ps, a) # branch) xs\<close>
  shows \<open>descendants k i ((p # ps, a) # branch) xs\<close>
  using assms descendants_block[where ps'=\<open>[_]\<close>] by simp

lemma descendants_types:
  assumes
    \<open>descendants k i branch xs\<close> \<open>(v, v') \<in> xs\<close>
    \<open>branch !. v = Some (ps, a)\<close> \<open>ps !. v' = Some p\<close>
  shows \<open>p = (\<^bold>\<diamond> Nom k) \<or> (\<exists>q. p = (\<^bold>\<not> (\<^bold>@ k q)))\<close>
  using assms by (induct k i branch xs arbitrary: v v' ps a) fastforce+

lemma descendants_oob_head':
  assumes \<open>descendants k i ((ps, a) # branch) xs\<close>
  shows \<open>(length branch, m + length ps) \<notin> xs\<close>
  using assms descendants_bounds_snd by fastforce

lemma descendants_oob_head:
  assumes \<open>descendants k i ((ps, a) # branch) xs\<close>
  shows \<open>(length branch, length ps) \<notin> xs\<close>
  using assms descendants_oob_head'[where m=0] by fastforce

subsection \<open>Induction\<close>

text \<open>
  We induct over an arbitrary set of indices.
  That way, we can determine in each case whether the extension gets replaced or not
    by manipulating the set before applying the induction hypothesis.
\<close>

lemma ST_bridge':
  fixes a :: 'b
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>n \<turnstile> (ps, a) # branch\<close>
    \<open>descendants k i ((ps, a) # branch) xs\<close>
    \<open>Nom j at c in branch\<close> \<open>Nom k at c in branch\<close>
  shows \<open>\<turnstile> mapi_branch (bridge k j xs) ((ps, a) # branch)\<close>
  using assms(2-)
proof (induct n \<open>(ps, a) # branch\<close> arbitrary: ps a branch xs rule: ST.induct)
  case (Close p i')
  let ?f = \<open>bridge k j xs\<close>
  let ?branch = \<open>mapi_branch ?f ((ps, a) # branch)\<close>

  obtain qs where qs: \<open>(qs, i') \<in>. (ps, a) # branch\<close> \<open>p on (qs, i')\<close>
    using Close(1) by blast
  obtain rs where rs: \<open>(rs, i') \<in>. (ps, a) # branch\<close> \<open>(\<^bold>\<not> p) on (rs, i')\<close>
    using Close(2) by blast

  obtain v where v: \<open>(mapi (?f v) qs, i') \<in>. ?branch\<close>
    using qs mapi_branch_mem by fast
  obtain w where w: \<open>(mapi (?f w) rs, i') \<in>. ?branch\<close>
    using rs mapi_branch_mem by fast

  have j: \<open>Nom j at c in ?branch\<close>
    using Close(4) nom_at_in_bridge unfolding mapi_branch_def by fastforce
  have k: \<open>Nom k at c in ?branch\<close>
    using Close(5) nom_at_in_bridge unfolding mapi_branch_def by fastforce

  show ?case
  proof (cases \<open>\<exists>a. p = Nom a\<close>)
    case True
    then have \<open>p on (mapi (?f v) qs, i')\<close>
      using qs bridge_on_Nom by fast
    moreover have \<open>(\<^bold>\<not> p) on (mapi (?f w) rs, i')\<close>
      using rs(2) True by (induct rs) auto
    ultimately show ?thesis
      using v w ST.Close by fast
  next
    case False
    then obtain v' where \<open>qs !. v' = Some p\<close>
      using qs rev_nth_on by fast
    then have qs': \<open>(?f v v' p) on (mapi (?f v) qs, i')\<close>
      using rev_nth_mapi_block by fast

    then obtain w' where \<open>rs !. w' = Some (\<^bold>\<not> p)\<close>
      using rs rev_nth_on by fast
    then have rs': \<open>(?f w w' (\<^bold>\<not> p)) on (mapi (?f w) rs, i')\<close>
      using rev_nth_mapi_block by fast

    obtain q q' where q: \<open>?f v v' p = q\<close> and q': \<open>?f w w' (\<^bold>\<not> p) = q'\<close>
      by simp_all
    then consider
      (dia) \<open>q = (\<^bold>\<diamond> Nom j)\<close> \<open>q' = (\<^bold>\<not> (\<^bold>\<diamond> Nom k))\<close> |
      (satn)\<open>\<exists>r. q = (\<^bold>\<not> (\<^bold>@ j r)) \<and> q' = (\<^bold>\<not> \<^bold>\<not> (\<^bold>@ k r))\<close> |
      (sat) \<open>\<exists>r. q = (\<^bold>@ k r) \<and> q' = (\<^bold>\<not> (\<^bold>@ j r))\<close> |
      (old) \<open>q = p\<close> \<open>q' = (\<^bold>\<not> p)\<close>
      using bridge_compl_cases by fast
    then show ?thesis
    proof cases
      case dia
      then have *:
        \<open>(\<^bold>\<diamond> Nom j) on (mapi (?f v) qs, i')\<close>
        \<open>(\<^bold>\<not> (\<^bold>\<diamond> Nom k)) on (mapi (?f w) rs, i')\<close>
        using q qs' q' rs' by simp_all

      have \<open>i' \<in> branch_nominals ?branch\<close>
        unfolding branch_nominals_def using v by fastforce
      then have ?thesis if \<open>\<turnstile> ([], i') # ?branch\<close>
        using that GoTo by fast
      moreover have \<open>(mapi (?f v) qs, i') \<in>. ([], i') # ?branch\<close>
        using v by simp
      moreover have \<open>(mapi (?f w) rs, i') \<in>. ([], i') # ?branch\<close>
        using w by simp
      ultimately have ?thesis if \<open>\<turnstile> ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using that * by (meson DiaN')
      moreover have \<open>j \<in> branch_nominals (([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch)\<close>
        unfolding branch_nominals_def by simp
      ultimately have ?thesis if \<open>\<turnstile> ([], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using that GoTo by fast
      moreover have \<open>Nom j at c in ([], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using j by auto
      moreover have \<open>Nom k at c in ([], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using k by auto
      ultimately have ?thesis if \<open>\<turnstile> ([Nom k], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using that by (meson Nom' list.set_intros(1) on.simps)
      moreover have \<open>(\<^bold>\<not> (\<^bold>@ j (Nom k))) at i' in ([Nom k], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        by fastforce
      ultimately have ?thesis if \<open>\<turnstile> ([\<^bold>\<not> Nom k, Nom k], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        using that SatN' by fast
      moreover have \<open>Nom k at j in ([\<^bold>\<not> Nom k, Nom k], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        by fastforce
      moreover have \<open>(\<^bold>\<not> Nom k) at j in ([\<^bold>\<not> Nom k, Nom k], j) # ([\<^bold>\<not> (\<^bold>@ j (Nom k))], i') # ?branch\<close>
        by fastforce
      ultimately show ?thesis
        using ST.Close by fast
    next
      case satn
      then obtain r where *:
        \<open>(\<^bold>\<not> (\<^bold>@ j r)) on (mapi (?f v) qs, i')\<close>
        \<open>(\<^bold>\<not> \<^bold>\<not> (\<^bold>@ k r)) on (mapi (?f w) rs, i')\<close>
        using q qs' q' rs' by auto

      have \<open>i' \<in> branch_nominals ?branch\<close>
        unfolding branch_nominals_def using v by fastforce
      then have ?thesis if \<open>\<turnstile> ([], i') # ?branch\<close>
        using that GoTo by fast
      moreover have \<open>(mapi (?f w) rs, i') \<in>. ([], i') # ?branch\<close>
        using w by simp
      ultimately have ?thesis if \<open>\<turnstile> ([\<^bold>@ k r], i') # ?branch\<close>
        using that *(2) by (meson Neg')
      moreover have \<open>j \<in> branch_nominals (([\<^bold>@ k r], i') # ?branch)\<close>
        unfolding branch_nominals_def using j by fastforce
      ultimately have ?thesis if \<open>\<turnstile> ([], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using that j GoTo by fast
      moreover have
        \<open>Nom j at c in ([], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        \<open>Nom k at c in ([], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using j k by auto
      ultimately have ?thesis if \<open>\<turnstile> ([Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using that by (meson Nom' list.set_intros(1) on.simps)
      then have ?thesis if \<open>\<turnstile> ([r, Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using that inf by (meson SatP'' list.set_intros(1) list.set_intros(2) on.simps)
      moreover have \<open>(mapi (?f v) qs, i') \<in>. ([r, Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using v by simp
      ultimately have ?thesis if \<open>\<turnstile> ([\<^bold>\<not> r, r, Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        using that *(1) by (meson SatN')
      moreover have \<open>r at j in ([\<^bold>\<not> r, r, Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        by fastforce
      moreover have \<open>(\<^bold>\<not> r) at j in ([\<^bold>\<not> r, r, Nom k], j) # ([\<^bold>@ k r], i') # ?branch\<close>
        by fastforce
      ultimately show ?thesis
        using ST.Close by fast
    next
      case sat
      then obtain r where *:
        \<open>(\<^bold>@ k r) on (mapi (?f v) qs, i')\<close>
        \<open>(\<^bold>\<not> (\<^bold>@ j r)) on (mapi (?f w) rs, i')\<close>
        using q qs' q' rs' by auto

      have \<open>j \<in> branch_nominals ?branch\<close>
        unfolding branch_nominals_def using j by fastforce
      then have ?thesis if \<open>\<turnstile> ([], j) # ?branch\<close>
        using that GoTo by fast
      moreover have \<open>Nom j at c in ([], j) # ?branch\<close> \<open>Nom k at c in ([], j) # ?branch\<close>
        using j k by auto
      ultimately have ?thesis if \<open>\<turnstile> ([Nom k], j) # ?branch\<close>
        using that by (meson Nom' list.set_intros(1) on.simps)
      moreover have \<open>(mapi (?f v) qs, i') \<in>. ([Nom k], j) # ?branch\<close>
        using v by simp
      ultimately have ?thesis if \<open>\<turnstile> ([r, Nom k], j) # ?branch\<close>
        using that *(1) inf by (meson SatP'' list.set_intros(1) on.simps)
      moreover have \<open>(mapi (?f w) rs, i') \<in>. ([r, Nom k], j) # ?branch\<close>
        using w by simp
      ultimately have ?thesis if \<open>\<turnstile> ([\<^bold>\<not> r, r, Nom k], j) # ?branch\<close>
        using that *(2) by (meson SatN')
      moreover have \<open>r at j in ([\<^bold>\<not> r, r, Nom k], j) # ?branch\<close>
        by fastforce
      moreover have \<open>(\<^bold>\<not> r) at j in ([\<^bold>\<not> r, r, Nom k], j) # ?branch\<close>
        by fastforce
      ultimately show ?thesis
        using ST.Close by fast
    next
      case old
      then have \<open>p on (mapi (?f v) qs, i')\<close> \<open>(\<^bold>\<not> p) on (mapi (?f w) rs, i')\<close>
        using q qs' q' rs' by simp_all
      then show ?thesis
        using v w ST.Close[where p=p and i=i'] by fast
    qed
  qed
next
  case (Neg p a ps branch)
  let ?f = \<open>bridge k j xs\<close>
  have p: \<open>?f l l' (\<^bold>\<not> \<^bold>\<not> p) = (\<^bold>\<not> \<^bold>\<not> p)\<close> for l l'
    by simp

  have \<open>descendants k i ((p # ps, a) # branch) xs\<close>
    using Neg(5) descendants_no_head by fast
  then have \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
    using Neg(4-) by blast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using Neg(5) descendants_oob_head by fast
  ultimately have \<open>\<turnstile> (p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def by simp
  moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>\<not> \<^bold>\<not> p) at a in mapi_branch ?f ((ps, a) # branch)\<close>
    using Neg(1) at_in_mapi_branch by fast
  then have \<open>(\<^bold>\<not> \<^bold>\<not> p) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using p by simp
  ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    using Neg' by fast
  then show ?case
    unfolding mapi_branch_def by auto
next
  case (DisP p q a ps branch)
  let ?f = \<open>bridge k j xs\<close>
  have p: \<open>?f l l' (p \<^bold>\<or> q) = (p \<^bold>\<or> q)\<close> for l l'
    by simp

  have
    \<open>descendants k i ((p # ps, a) # branch) xs\<close>
    \<open>descendants k i ((q # ps, a) # branch) xs\<close>
    using DisP(8) descendants_no_head by fast+
  then have
    \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
    \<open>\<turnstile> mapi_branch ?f ((q # ps, a) # branch)\<close>
    using DisP(5-) by blast+
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DisP(8) descendants_oob_head by fast
  ultimately have
    \<open>\<turnstile> (p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    \<open>\<turnstile> (q # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def by simp_all
  moreover have \<open>\<exists>l l'. ?f l l' (p \<^bold>\<or> q) at a in mapi_branch ?f ((ps, a) # branch)\<close>
    using DisP(1) at_in_mapi_branch by fast
  then have \<open>(p \<^bold>\<or> q) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using p by simp
  ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    using DisP'' by fast
  then show ?case
    unfolding mapi_branch_def by auto
next
  case (DisN p q a ps branch)
  let ?f = \<open>bridge k j xs\<close>
  have p: \<open>?f l l' (\<^bold>\<not> (p \<^bold>\<or> q)) = (\<^bold>\<not> (p \<^bold>\<or> q))\<close> for l l'
    by simp

  have \<open>descendants k i (((\<^bold>\<not> p) # ps, a) # branch) xs\<close>
    using DisN(5) descendants_no_head by fast
  then have \<open>descendants k i (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch) xs\<close>
    using descendants_no_head by fast
  then have \<open>\<turnstile> mapi_branch ?f (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, a) # branch)\<close>
    using DisN(4-) by blast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using DisN(5) descendants_oob_head by fast
  moreover have \<open>(length branch, 1 + length ps) \<notin> xs\<close>
    using DisN(5) descendants_oob_head' by fast
  ultimately have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def by simp
  moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>\<not> (p \<^bold>\<or> q)) at a in mapi_branch ?f ((ps, a) # branch)\<close>
    using DisN(1) at_in_mapi_branch by fast
  then have \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using p by simp
  ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    using DisN' by fast
  then show ?case
    unfolding mapi_branch_def by auto
next
  case (DiaP p a ps branch i')
  let ?f = \<open>bridge k j xs\<close>
  have p: \<open>?f l l' (\<^bold>\<diamond> p) = (\<^bold>\<diamond> p)\<close> for l l'
    using DiaP(3) bridge_proper_dia by fast

  have \<open>branch_nominals (mapi_branch ?f ((ps, a) # branch)) = branch_nominals ((ps, a) # branch)\<close>
    using DiaP(8-) nominals_mapi_branch_bridge[where j=j and k=k and branch=\<open>(ps, a) # branch\<close>]
    by auto
  then have i': \<open>i' \<notin> branch_nominals ((mapi (?f (length branch)) ps, a) # mapi_branch ?f branch)\<close>
    unfolding mapi_branch_def using DiaP(2) by simp

  have 1: \<open>?f (length branch) (1 + length ps) (\<^bold>@ i' p) = (\<^bold>@ i' p)\<close>
    by simp
  have \<open>i' \<noteq> k\<close>
    using DiaP(2, 8-) unfolding branch_nominals_def by fastforce
  then have 2: \<open>?f (length branch) (length ps) (\<^bold>\<diamond> Nom i') = (\<^bold>\<diamond> Nom i')\<close>
    by simp

  have \<open>descendants k i (((\<^bold>@ i' p) # (\<^bold>\<diamond> Nom i') # ps, a) # branch) xs\<close>
    using DiaP(7) descendants_block[where ps'=\<open>[_, _]\<close>] by fastforce
  then have \<open>\<turnstile> mapi_branch ?f (((\<^bold>@ i' p) # (\<^bold>\<diamond> Nom i') # ps, a) # branch)\<close>
    using DiaP(4-) by blast
  then have \<open>\<turnstile> ((\<^bold>@ i' p) # (\<^bold>\<diamond> Nom i') # mapi (?f (length branch)) ps, a) #
      mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using 1 by (simp add: 2)
  moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>\<diamond> p) at a in mapi_branch ?f ((ps, a) # branch)\<close>
    using DiaP(1) at_in_mapi_branch by fast
  then have \<open>(\<^bold>\<diamond> p) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using p by simp
  ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    using i' DiaP(3) DiaP' by fast
  then show ?case
    unfolding mapi_branch_def by simp
next
  case (DiaN p a ps branch i')
  have p: \<open>bridge k j xs l l' (\<^bold>\<not> (\<^bold>\<diamond> p)) = (\<^bold>\<not> (\<^bold>\<diamond> p))\<close> for xs l l'
    by simp

  obtain rs where rs: \<open>(rs, a) \<in>. (ps, a) # branch\<close> \<open>(\<^bold>\<diamond> Nom i') on (rs, a)\<close>
    using DiaN(2) by fast
  obtain v where v: \<open>((ps, a) # branch) !. v = Some (rs, a)\<close>
    using rs(1) rev_nth_mem by fast
  obtain v' where v': \<open>rs !. v' = Some (\<^bold>\<diamond> Nom i')\<close>
    using rs(2) rev_nth_on by fast

  show ?case
  proof (cases \<open>(v, v') \<in> xs\<close>)
    case True
    then have \<open>i' = k\<close>
      using DiaN(6) v v' descendants_types by fast

    let ?xs = \<open>{(length branch, length ps)} \<union> xs\<close>
    let ?f = \<open>bridge k j ?xs\<close>
    let ?branch = \<open>((\<^bold>\<not> (\<^bold>@ i' p)) # ps, a) # branch\<close>

    obtain rs' where
      \<open>(((\<^bold>\<not> (\<^bold>@ k p)) # ps, a) # branch) !. v = Some (rs', a)\<close>
      \<open>rs' !. v' = Some (\<^bold>\<diamond> Nom i')\<close>
      using v v' index_Cons by fast
    moreover have \<open>descendants k i (((\<^bold>\<not> (\<^bold>@ k p)) # ps, a) # branch) xs\<close>
      using DiaN(6) descendants_block[where ps'=\<open>[_]\<close>] by fastforce
    moreover have \<open>?branch !. length branch = Some ((\<^bold>\<not> (\<^bold>@ k p)) # ps, a)\<close>
      using \<open>i' = k\<close> by simp
    moreover have \<open>((\<^bold>\<not> (\<^bold>@ k p)) # ps) !. length ps = Some (\<^bold>\<not> (\<^bold>@ k p))\<close>
      by simp
    ultimately have \<open>descendants k i (((\<^bold>\<not> (\<^bold>@ k p)) # ps, a) # branch) ?xs\<close>
      using True \<open>i' = k\<close> Derived[where branch=\<open>_ # branch\<close>] by simp

    then have \<open>\<turnstile> mapi_branch ?f (((\<^bold>\<not> (\<^bold>@ k p)) # ps, a) # branch)\<close>
      using \<open>i' = k\<close> DiaN(5-) by blast
    then have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ j p)) # mapi (?f (length branch)) ps, a) #
        mapi_branch (bridge k j ?xs) branch\<close>
      unfolding mapi_branch_def using \<open>i' = k\<close> by simp
    moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>\<not> (\<^bold>\<diamond> p)) at a in mapi_branch ?f ((ps, a) # branch)\<close>
      using DiaN(1) at_in_mapi_branch by fast
    then have \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def using p[where xs=\<open>?xs\<close>] by simp
    moreover have \<open>(mapi (?f v) rs, a) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
      using v rev_nth_mapi_branch by fast
    then have \<open>(mapi (?f v) rs, a) \<in>
        set ((mapi (?f (length branch)) ps, a) # mapi_branch ?f branch)\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>?f v v' (\<^bold>\<diamond> Nom i') on (mapi (?f v) rs, a)\<close>
      using v' rev_nth_mapi_block by fast
    then have \<open>(\<^bold>\<diamond> Nom j) on (mapi (?f v) rs, a)\<close>
      using True \<open>i' = k\<close> by simp
    ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      by (meson DiaN')
    then have \<open>\<turnstile> (mapi (bridge k j xs (length branch)) ps, a) #
        mapi_branch (bridge k j xs) branch\<close>
      using mapi_branch_head_add_oob[where branch=branch and ps=ps] unfolding mapi_branch_def
      by simp
    then show ?thesis
      unfolding mapi_branch_def by simp
  next
    case False
    let ?f = \<open>bridge k j xs\<close>

    have \<open>descendants k i (((\<^bold>\<not> (\<^bold>@ i' p)) # ps, a) # branch) xs\<close>
      using DiaN(6) descendants_no_head by fast
    then have \<open>\<turnstile> mapi_branch ?f (((\<^bold>\<not> (\<^bold>@ i' p)) # ps, a) # branch)\<close>
      using DiaN(5-) by blast
    moreover have \<open>(length branch, length ps) \<notin> xs\<close>
      using DiaN(6) descendants_oob_head by fast
    ultimately have \<open>\<turnstile> ((\<^bold>\<not> (\<^bold>@ i' p)) # mapi (?f (length branch)) ps, a) #
        mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>\<not> (\<^bold>\<diamond> p)) at a in mapi_branch ?f ((ps, a) # branch)\<close>
      using DiaN(1) at_in_mapi_branch by fast
    then have \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def using p[where xs=\<open>xs\<close>] by simp
    moreover have \<open>(mapi (?f v) rs, a) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
      using v rev_nth_mapi_branch by fast
    then have \<open>(mapi (?f v) rs, a) \<in>
        set ((mapi (?f (length branch)) ps, a) # mapi_branch ?f branch)\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>?f v v' (\<^bold>\<diamond> Nom i') on (mapi (?f v) rs, a)\<close>
      using v' rev_nth_mapi_block by fast
    then have \<open>(\<^bold>\<diamond> Nom i') on (mapi (?f v) rs, a)\<close>
      using False by simp
    ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      by (meson DiaN')
    then show ?thesis
      unfolding mapi_branch_def by simp
  qed
next
  case (SatP a p b ps branch)
  let ?f = \<open>bridge k j xs\<close>
  have p: \<open>?f l l' (\<^bold>@ a p) = (\<^bold>@ a p)\<close> for l l'
    by simp

  have \<open>descendants k i ((p # ps, a) # branch) xs\<close>
    using SatP(5) descendants_no_head by fast
  then have \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
    using SatP(4-) by blast
  moreover have \<open>(length branch, length ps) \<notin> xs\<close>
    using SatP(5) descendants_oob_head by fast
  ultimately have \<open>\<turnstile> (p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def by simp
  moreover have \<open>\<exists>l l'. ?f l l' (\<^bold>@ a p) at b in mapi_branch ?f ((ps, a) # branch)\<close>
    using SatP(1) at_in_mapi_branch by fast
  then have \<open>(\<^bold>@ a p) at b in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    unfolding mapi_branch_def using p by simp
  ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
    using SatP' by fast
  then show ?case
    unfolding mapi_branch_def by simp
next
  case (SatN a p b ps branch)
  obtain qs where qs: \<open>(qs, b) \<in>. (ps, a) # branch\<close> \<open>(\<^bold>\<not> (\<^bold>@ a p)) on (qs, b)\<close>
    using SatN(1) by fast
  obtain v where v: \<open>((ps, a) # branch) !. v = Some (qs, b)\<close>
    using qs(1) rev_nth_mem by fast
  obtain v' where v': \<open>qs !. v' = Some (\<^bold>\<not> (\<^bold>@ a p))\<close>
    using qs(2) rev_nth_on by fast

  show ?case
  proof (cases \<open>(v, v') \<in> xs\<close>)
    case True
    then have \<open>a = k\<close>
      using SatN(5) v v' descendants_types by fast

    let ?f = \<open>bridge k j xs\<close>
    let ?branch = \<open>((\<^bold>\<not> p) # ps, a) # branch\<close>
    have p: \<open>?f v v' (\<^bold>\<not> (\<^bold>@ k p)) = (\<^bold>\<not> (\<^bold>@ j p))\<close>
      using True by simp

    obtain rs' where
      \<open>?branch !. v = Some (rs', b)\<close>
      \<open>rs' !. v' = Some (\<^bold>\<not> (\<^bold>@ k p))\<close>
      using v v' \<open>a = k\<close> index_Cons by fast
    have \<open>descendants k i ?branch xs\<close>
      using SatN(5) descendants_no_head by fast
    then have \<open>\<turnstile> mapi_branch ?f ?branch\<close>
      using \<open>a = k\<close> SatN(4-) by blast
    moreover have \<open>(length branch, length ps) \<notin> xs\<close>
      using SatN(5) descendants_oob_head by fast
    ultimately have \<open>\<turnstile> ((\<^bold>\<not> p) # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def using \<open>a = k\<close> by simp
    then have *: \<open>\<turnstile> ((\<^bold>\<not> p) # Nom j # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using inf ST_struct_block[where ps'=\<open>(\<^bold>\<not> p) # Nom j # _\<close>] by fastforce

    have \<open>(mapi (?f v) qs, b) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
      using v rev_nth_mapi_branch by fast
    then have \<open>(mapi (?f v) qs, b) \<in>
        set ((mapi (?f (length branch)) ps, a) # mapi_branch ?f branch)\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>?f v v' (\<^bold>\<not> (\<^bold>@ k p)) on (mapi (?f v) qs, b)\<close>
      using v' \<open>a = k\<close> rev_nth_mapi_block by fast
    then have \<open>(\<^bold>\<not> (\<^bold>@ j p)) on (mapi (?f v) qs, b)\<close>
      using p by simp
    ultimately obtain qs' where
      \<open>(qs', b) \<in>. (Nom j # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      \<open>(\<^bold>\<not> (\<^bold>@ j p)) on (qs', b)\<close>
      by fastforce
    then have \<open>\<turnstile> (Nom j # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using * inf by (meson SatN'' list.set_intros(1) on.simps)

    moreover have \<open>Nom j at c in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using SatN(6) nom_at_in_bridge unfolding mapi_branch_def by fastforce
    moreover have \<open>Nom k at c in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using SatN(7) nom_at_in_bridge unfolding mapi_branch_def by fastforce
    ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using \<open>a = k\<close> by (meson Nom' list.set_intros(1) on.simps)
    then show ?thesis
      unfolding mapi_branch_def by simp
  next
    case False
    let ?f = \<open>bridge k j xs\<close>

    have \<open>descendants k i (((\<^bold>\<not> p) # ps, a) # branch) xs\<close>
      using SatN(5) descendants_no_head by fast
    then have \<open>\<turnstile> mapi_branch (bridge k j xs) (((\<^bold>\<not> p) # ps, a) # branch)\<close>
      using SatN(4-) by blast
    moreover have \<open>(length branch, length ps) \<notin> xs\<close>
      using SatN(5) descendants_oob_head by fast
    ultimately have \<open>\<turnstile> ((\<^bold>\<not> p) # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>(mapi (?f v) qs, b) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
      using v rev_nth_mapi_branch by fast
    then have \<open>(mapi (?f v) qs, b) \<in>
        set ((mapi (?f (length branch)) ps, a) # mapi_branch ?f branch)\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>?f v v' (\<^bold>\<not> (\<^bold>@ a p)) on (mapi (?f v) qs, b)\<close>
      using v' rev_nth_mapi_block by fast
    then have \<open>(\<^bold>\<not> (\<^bold>@ a p)) on (mapi (?f v) qs, b)\<close>
      using False by simp
    ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      by (meson SatN')
    then show ?thesis
      unfolding mapi_branch_def by simp
  qed
next
  case (GoTo i' n ps a branch)
  let ?f = \<open>bridge k j xs\<close>

  have \<open>descendants k i (([], i') # (ps, a) # branch) xs\<close>
    using GoTo(4) descendants_branch[where extra=\<open>[_]\<close>] by simp
  then have \<open>\<turnstile> mapi_branch ?f (([], i') # (ps, a) # branch)\<close>
    using GoTo(3, 5-) by auto
  then have \<open>\<turnstile> ([], i') # mapi_branch ?f ((ps, a) # branch)\<close>
    unfolding mapi_branch_def by simp
  moreover have
    \<open>branch_nominals (mapi_branch ?f ((ps, a) # branch)) = branch_nominals ((ps, a) # branch)\<close>
    using GoTo(5-) nominals_mapi_branch_bridge[where j=j and k=k and branch=\<open>(ps, a) # branch\<close>]
    by auto
  then have \<open>i' \<in> branch_nominals (mapi_branch (bridge k j xs) ((ps, a) # branch))\<close>
    using GoTo(1) by blast
  ultimately show ?case
    using ST.GoTo by fast
next
  case (Nom p b ps a branch i')
  show ?case
  proof (cases \<open>\<exists>j. p = Nom j\<close>)
    case True
    let ?f = \<open>bridge k j xs\<close>

    have \<open>descendants k i ((p # ps, a) # branch) xs\<close>
      using Nom(7) descendants_block[where ps'=\<open>[p]\<close>] by simp
    then have \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
      using Nom(6-) by blast
    moreover have \<open>?f (length branch) (length ps) p = p\<close>
      using True by auto
    ultimately have \<open>\<turnstile> (p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>p at b in mapi_branch ?f ((ps, a) # branch)\<close>
      using Nom(1) True nom_at_in_bridge by fast
    then have \<open>p at b in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>Nom i' at b in mapi_branch ?f ((ps, a) # branch)\<close>
      using Nom(2) True nom_at_in_bridge by fast
    then have \<open>Nom i' at b in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    moreover have \<open>Nom i' at a in mapi_branch ?f ((ps, a) # branch)\<close>
      using Nom(3) True nom_at_in_bridge by fast
    then have \<open>Nom i' at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      unfolding mapi_branch_def by simp
    ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
      using Nom' by fast
    then show ?thesis
      unfolding mapi_branch_def by simp
  next
    case False
    obtain qs where qs: \<open>(qs, b) \<in>. (ps, a) # branch\<close> \<open>p on (qs, b)\<close>
      using Nom(1) by blast
    obtain v where v: \<open>((ps, a) # branch) !. v = Some (qs, b)\<close>
      using qs(1) rev_nth_mem by fast
    obtain v' where v': \<open>qs !. v' = Some p\<close>
      using qs(2) False rev_nth_on by fast

    show ?thesis
    proof (cases \<open>(v, v') \<in> xs\<close>)
      case True
      let ?xs = \<open>{(length branch, length ps)} \<union> xs\<close>
      let ?f = \<open>bridge k j ?xs\<close>

      let ?p = \<open>bridge' k j p\<close>
      have p: \<open>?f v v' p = ?p\<close>
        using True by simp

      obtain qs' where
        \<open>((p # ps, a) # branch) !. v = Some (qs', b)\<close>
        \<open>qs' !. v' = Some p\<close>
        using v v' index_Cons by fast
      moreover have \<open>Nom i' at b in (p # ps, a) # branch\<close>
        using Nom(2) by fastforce
      moreover have \<open>descendants k i ((p # ps, a) # branch) xs\<close>
        using Nom(7) descendants_block[where ps'=\<open>[p]\<close>] by simp
      moreover have
        \<open>((p # ps, a) # branch) !. length branch = Some (p # ps, a)\<close>
        \<open>(p # ps) !. length ps = Some p\<close>
        by simp_all
      moreover have \<open>Nom i' at a in (p # ps, a) # branch\<close>
        using Nom(3) by fastforce
      ultimately have \<open>descendants k i ((p # ps, a) # branch) ?xs\<close>
        using True Copied by fast
      then have \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
        using Nom(6-) by blast
      then have \<open>\<turnstile> (?p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp

      moreover have \<open>(mapi (?f v) qs, b) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
        using v rev_nth_mapi_branch by fast
      then have \<open>(mapi (?f v) qs, b) \<in>. (mapi (?f (length branch)) ps, a) #
          mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      moreover have \<open>?f v v' p on (mapi (?f v) qs, b)\<close>
        using v v' rev_nth_mapi_block by fast
      then have \<open>?p on (mapi (?f v) qs, b)\<close>
        using p by simp

      moreover have \<open>Nom i' at b in mapi_branch ?f ((ps, a) # branch)\<close>
        using Nom(2) nom_at_in_bridge by fast
      then have \<open>Nom i' at b in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      moreover have \<open>Nom i' at a in mapi_branch ?f ((ps, a) # branch)\<close>
        using Nom(3) nom_at_in_bridge by fast
      then have \<open>Nom i' at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        using Nom' by fast
      then have \<open>\<turnstile> (mapi (bridge k j xs (length branch)) ps, a) #
          mapi_branch (bridge k j xs) branch\<close>
        using mapi_branch_head_add_oob[where branch=branch and ps=ps]
        unfolding mapi_branch_def by simp
      then show ?thesis
        unfolding mapi_branch_def by simp
    next
      case False
      let ?f = \<open>bridge k j xs\<close>

      have \<open>descendants k i ((p # ps, a) # branch) xs\<close>
        using Nom(7) descendants_no_head by fast
      then have \<open>\<turnstile> mapi_branch ?f ((p # ps, a) # branch)\<close>
        using Nom(6-) by blast
      moreover have \<open>(length branch, length ps) \<notin> xs\<close>
        using Nom(7) descendants_oob_head by fast
      ultimately have \<open>\<turnstile> (p # mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp

      moreover have \<open>(mapi (?f v) qs, b) \<in>. mapi_branch ?f ((ps, a) # branch)\<close>
        using v rev_nth_mapi_branch by fast
      then have \<open>(mapi (?f v) qs, b) \<in>. (mapi (?f (length branch)) ps, a) #
          mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      moreover have \<open>?f v v' p on (mapi (?f v) qs, b)\<close>
        using v v' rev_nth_mapi_block by fast
      then have \<open>p on (mapi (?f v) qs, b)\<close>
        using False by simp
      moreover have \<open>Nom i' at b in mapi_branch ?f ((ps, a) # branch)\<close>
        using Nom(2) nom_at_in_bridge by fast
      then have \<open>Nom i' at b in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      moreover have \<open>Nom i' at a in mapi_branch ?f ((ps, a) # branch)\<close>
        using Nom(3) nom_at_in_bridge by fast
      then have \<open>Nom i' at a in (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        unfolding mapi_branch_def by simp
      ultimately have \<open>\<turnstile> (mapi (?f (length branch)) ps, a) # mapi_branch ?f branch\<close>
        using Nom' by fast
      then show ?thesis
        unfolding mapi_branch_def by simp
    qed
  qed
qed

lemma ST_bridge:
  fixes i :: 'b
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>\<turnstile> branch\<close> \<open>descendants k i branch xs\<close>
    \<open>Nom j at c in branch\<close> \<open>Nom k at c in branch\<close>
  shows \<open>\<turnstile> mapi_branch (bridge k j xs) branch\<close>
proof -
  have \<open>\<turnstile> ([], j) # branch\<close>
    using inf assms(2) ST_struct[where branch'=\<open>([], j) # branch\<close>] by auto
  moreover have \<open>descendants k i (([], j) # branch) xs\<close>
    using assms(3) descendants_branch[where extra=\<open>[_]\<close>] by fastforce
  ultimately have \<open>\<turnstile> mapi_branch (bridge k j xs) (([], j) # branch)\<close>
    using ST_bridge' inf assms(3-) by fast
  then have *: \<open>\<turnstile> ([], j) # mapi_branch (bridge k j xs) branch\<close>
    unfolding mapi_branch_def by simp
  have \<open>branch_nominals (mapi_branch (bridge k j xs) branch) = branch_nominals branch\<close>
    using nominals_mapi_branch_bridge assms(4-) by fast
  moreover have \<open>j \<in> branch_nominals branch\<close>
    using assms(4) unfolding branch_nominals_def by fastforce
  ultimately have \<open>j \<in> branch_nominals (mapi_branch (bridge k j xs) branch)\<close>
    by simp
  then show ?thesis
    using * GoTo by fast
qed

subsection \<open>Derivation\<close>

theorem Bridge:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>Nom i at b in branch\<close> \<open>(\<^bold>\<diamond> Nom j) at b in branch\<close> \<open>Nom i at a in branch\<close>
    \<open>Nom j at c in branch\<close> \<open>Nom k at c in branch\<close>
    \<open>\<turnstile> ((\<^bold>\<diamond> Nom k) # ps, a) # branch\<close>
  shows \<open>\<turnstile> (ps, a) # branch\<close>
proof -
  let ?xs = \<open>{(length branch, length ps)}\<close>

  have \<open>descendants k a (((\<^bold>\<diamond> Nom k) # ps, a) # branch) ?xs\<close>
    using Initial by force
  moreover have
    \<open>Nom j at c in ((\<^bold>\<diamond> Nom k) # ps, a) # branch\<close>
    \<open>Nom k at c in ((\<^bold>\<diamond> Nom k) # ps, a) # branch\<close>
    using assms(5-6) by auto
  ultimately have
    \<open>\<turnstile> mapi_branch (bridge k j ?xs) (((\<^bold>\<diamond> Nom k) # ps, a) # branch)\<close>
    using ST_bridge inf assms(7) by fast
  then have \<open>\<turnstile> ((\<^bold>\<diamond> Nom j) # mapi (bridge k j ?xs (length branch)) ps, a) #
      mapi_branch (bridge k j ?xs) branch\<close>
    unfolding mapi_branch_def by simp
  moreover have \<open>mapi_branch (bridge k j {(length branch, length ps)}) branch =
      mapi_branch (bridge k j {}) branch\<close>
    using mapi_branch_add_oob[where xs=\<open>{}\<close>] by fastforce
  moreover have \<open>mapi (bridge k j ?xs (length branch)) ps =
    mapi (bridge k j {} (length branch)) ps\<close>
    using mapi_block_add_oob[where xs=\<open>{}\<close> and ps=ps] by simp
  ultimately have \<open>\<turnstile> ((\<^bold>\<diamond> Nom j) # ps, a) # branch\<close>
    using mapi_block_id[where ps=ps] mapi_branch_id[where branch=branch] by simp
  then show ?thesis
    using assms(2-5) by (meson Nom' set_subset_Cons subsetD)
qed

section \<open>Completeness\<close>

subsection \<open>Hintikka\<close>

abbreviation at_in' :: \<open>('a, 'b) fm \<Rightarrow> 'b \<Rightarrow> ('a, 'b) block set \<Rightarrow> bool\<close>
  (\<open>_ at _ in'' _\<close> [51, 51, 51] 50) where
  \<open>p at a in' branch \<equiv> \<exists>ps. (ps, a) \<in> branch \<and> p on (ps, a)\<close>

text \<open>
  A set of blocks is Hintikka if it satisfies the following requirements.
  Intuitively, if it corresponds to an exhausted open branch.
\<close>

definition hintikka :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>hintikka H \<equiv>
    (\<forall>x i j. Nom j at i in' H \<longrightarrow> Pro x at j in' H \<longrightarrow>
      \<not> (\<^bold>\<not> Pro x) at i in' H) \<and>
    (\<forall>a i. Nom a at i in' H \<longrightarrow>
      \<not> (\<^bold>\<not> Nom a) at i in' H) \<and>
    (\<forall>i j. (\<^bold>\<diamond> Nom j) at i in' H \<longrightarrow>
      \<not> (\<^bold>\<not> (\<^bold>\<diamond> Nom j)) at i in' H) \<and>
    (\<forall>p i. i \<in> nominals p \<longrightarrow> (\<exists>block \<in> H. p on block) \<longrightarrow>
      (\<exists>ps. (ps, i) \<in> H)) \<and>
    (\<forall>i j. Nom j at i in' H \<longrightarrow>
      Nom i at j in' H) \<and>
    (\<forall>i j k. Nom j at i in' H \<longrightarrow> Nom k at j in' H \<longrightarrow>
      Nom k at i in' H) \<and>
    (\<forall>i j k. (\<^bold>\<diamond> Nom j) at i in' H \<longrightarrow> Nom k at j in' H \<longrightarrow>
      (\<^bold>\<diamond> Nom k) at i in' H) \<and>
    (\<forall>i j k. (\<^bold>\<diamond> Nom j) at i in' H \<longrightarrow> Nom k at i in' H \<longrightarrow>
      (\<^bold>\<diamond> Nom j) at k in' H) \<and>
    (\<forall>p q i. (p \<^bold>\<or> q) at i in' H \<longrightarrow>
      p at i in' H \<or> q at i in' H) \<and>
    (\<forall>p q i. (\<^bold>\<not> (p \<^bold>\<or> q)) at i in' H \<longrightarrow>
      (\<^bold>\<not> p) at i in' H \<and> (\<^bold>\<not> q) at i in' H) \<and>
    (\<forall>p i. (\<^bold>\<not> \<^bold>\<not> p) at i in' H \<longrightarrow>
      p at i in' H) \<and>
    (\<forall>p i a. (\<^bold>@ i p) at a in' H \<longrightarrow>
      p at i in' H) \<and>
    (\<forall>p i a. (\<^bold>\<not> (\<^bold>@ i p)) at a in' H \<longrightarrow>
      (\<^bold>\<not> p) at i in' H) \<and>
    (\<forall>p i. (\<nexists>a. p = Nom a) \<longrightarrow> (\<^bold>\<diamond> p) at i in' H \<longrightarrow>
      (\<exists>j. (\<^bold>\<diamond> Nom j) at i in' H \<and> (\<^bold>@ j p) at i in' H)) \<and>
    (\<forall>p i j. (\<^bold>\<not> (\<^bold>\<diamond> p)) at i in' H \<longrightarrow> (\<^bold>\<diamond> Nom j) at i in' H \<longrightarrow>
      (\<^bold>\<not> (\<^bold>@ j p)) at i in' H)\<close>

text \<open>
  Two nominals \<open>i\<close> and \<open>j\<close> are equivalent in respect to a Hintikka set \<open>H\<close> if
    \<open>H\<close> contains an \<open>i\<close>-block with \<open>j\<close> on it.
  This is shown to be an equivalence relation.
\<close>

definition hequiv :: \<open>('a, 'b) block set \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool\<close> where
  \<open>hequiv H i j \<equiv> Nom j at i in' H\<close>

abbreviation hequiv_rel :: \<open>('a, 'b) block set \<Rightarrow> ('b \<times> 'b) set\<close> where
  \<open>hequiv_rel H \<equiv> {(i, j) |i j. hequiv H i j}\<close>

definition names :: \<open>('a, 'b) block set \<Rightarrow> 'b set\<close> where
  \<open>names H \<equiv> {i |ps i. (ps, i) \<in> H}\<close>

lemma hequiv_refl: \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> hequiv H i i\<close>
  unfolding hintikka_def hequiv_def names_def by auto

lemma hequiv_refl': \<open>hintikka H \<Longrightarrow> (ps, i) \<in> H \<Longrightarrow> hequiv H i i\<close>
  using hequiv_refl unfolding names_def by fast

lemma hequiv_sym: \<open>hintikka H \<Longrightarrow> hequiv H i j = hequiv H j i\<close>
  unfolding hintikka_def hequiv_def by meson

lemma hequiv_trans:
  \<open>hintikka H \<Longrightarrow> hequiv H i j \<Longrightarrow> hequiv H j k \<Longrightarrow> hequiv H i k\<close>
  unfolding hintikka_def hequiv_def by meson

lemma hequiv_names: \<open>hequiv H i j \<Longrightarrow> i \<in> names H\<close>
  unfolding hequiv_def names_def by blast

lemma hequiv_names_rel: \<open>hintikka H \<Longrightarrow> hequiv_rel H \<subseteq> names H \<times> names H\<close>
  using hequiv_sym hequiv_names by fast

lemma hequiv_refl_rel: \<open>hintikka H \<Longrightarrow> refl_on (names H) (hequiv_rel H)\<close>
  unfolding refl_on_def using hequiv_refl hequiv_names_rel by fast

lemma hequiv_sym_rel: \<open>hintikka H \<Longrightarrow> sym (hequiv_rel H)\<close>
  unfolding sym_def using hequiv_sym by fast

lemma hequiv_trans_rel: \<open>hintikka H \<Longrightarrow> trans (hequiv_rel H)\<close>
  unfolding trans_def using hequiv_trans by fast

lemma hequiv_rel: \<open>hintikka H \<Longrightarrow> equiv (names H) (hequiv_rel H)\<close>
  using hequiv_refl_rel hequiv_sym_rel hequiv_trans_rel by (rule equivI)

subsubsection \<open>Named model\<close>

text \<open>
  Given a Hintikka set \<open>H\<close> and a formula \<open>p\<close> on a block in \<open>H\<close>
    we will construct a model that satisfies \<open>p\<close>.

  The worlds of our model are sets of equivalent nominals and
    nominals are assigned to their equivalence class.

  From a world \<open>is\<close>, we can reach a world \<open>js\<close> iff there is an \<open>i \<in> is\<close> and a \<open>j \<in> js\<close> s.t.
    there is an \<open>i\<close>-block in \<open>H\<close> with \<open>\<^bold>\<diamond> Nom j\<close> on it.

  A propositional symbol \<open>p\<close> is true in a world \<open>is\<close> if there exists an \<open>i \<in> is\<close> s.t.
    \<open>p\<close> occurs on an \<open>i\<close>-block in \<open>H\<close>.
 \<close>

definition assign :: \<open>('a, 'b) block set \<Rightarrow> 'b \<Rightarrow> 'b set\<close> where
  \<open>assign H i \<equiv> proj (hequiv_rel H) i\<close>

definition reach :: \<open>('a, 'b) block set \<Rightarrow> 'b set \<Rightarrow> 'b set set\<close> where
  \<open>reach H is \<equiv> {assign H j |i j. i \<in> is \<and> (\<^bold>\<diamond> Nom j) at i in' H}\<close>

definition val :: \<open>('a, 'b) block set \<Rightarrow> 'b set \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>val H is x \<equiv> \<exists>i \<in> is. Pro x at i in' H\<close>

lemma hequiv_assign: \<open>hintikka H \<Longrightarrow> hequiv H i j \<Longrightarrow> assign H i = assign H j\<close>
  unfolding proj_def assign_def using equiv_class_eq hequiv_rel by fast

lemma hequiv_model:
  assumes \<open>hintikka H\<close> \<open>hequiv H i j\<close>
  shows
    \<open>(Model (reach H) (val H), assign H, assign H i \<Turnstile> p) =
     (Model (reach H) (val H), assign H, assign H j \<Turnstile> p)\<close>
  using assms hequiv_assign by fastforce

lemma assign_refl: \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> i \<in> assign H i\<close>
  unfolding proj_def assign_def using hequiv_refl by fastforce

lemma assign_refl': \<open>hintikka H \<Longrightarrow> (ps, i) \<in> H \<Longrightarrow> i \<in> assign H i\<close>
  using assign_refl unfolding names_def by fast

lemma assign_named:
  \<open>hintikka H \<Longrightarrow> i \<in> names H \<Longrightarrow> \<forall>j \<in> assign H i. \<exists>ps. (ps, j) \<in> H\<close>
  using hequiv_sym unfolding proj_def assign_def hequiv_def by fast

lemma nominal_in_names:
  assumes \<open>hintikka H\<close> \<open>\<exists>block \<in> H. i \<in> block_nominals block\<close>
  shows \<open>i \<in> names H\<close>
proof -
  have \<open>(\<forall>p. i \<in> nominals p \<and> (\<exists>block \<in> H. p on block) \<longrightarrow> (\<exists>br. (br, i) \<in> H))\<close>
    using \<open>hintikka H\<close> unfolding hintikka_def by meson
  then show ?thesis
    unfolding names_def using assms(2) by fastforce
qed

lemma assign_sym: \<open>hintikka H \<Longrightarrow> j \<in> assign H i \<longleftrightarrow> i \<in> assign H j\<close>
  unfolding proj_def assign_def using hequiv_sym by fast

lemma hintikka_model:
  assumes \<open>hintikka H\<close>
  shows
    \<open>p at i in' H \<Longrightarrow> Model (reach H) (val H), assign H, assign H i \<Turnstile> p\<close>
    \<open>(\<^bold>\<not> p) at i in' H \<Longrightarrow> \<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> p\<close>
proof (induct p arbitrary: i)
  fix i
  case (Pro x)
  assume \<open>Pro x at i in' H\<close>
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> Pro x\<close>
    using assms(1) assign_refl' unfolding val_def by fastforce
next
  fix i
  case (Pro x)
  assume \<open>(\<^bold>\<not> Pro x) at i in' H\<close>
  then have \<open>\<not> Pro x at j in' H\<close> if \<open>Nom j at i in' H\<close> for j
    using that assms(1) unfolding hintikka_def by meson
  then have \<open>\<not> Pro x at j in' H\<close> if \<open>hequiv H i j\<close> for j
    using that unfolding hequiv_def by simp
  then have \<open>\<not> val H (assign H i) x\<close>
    unfolding proj_def val_def assign_def by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> Pro x\<close>
    by simp
next
  fix i
  case (Nom a)
  assume \<open>Nom a at i in' H\<close>
  then have \<open>assign H a = assign H i\<close>
    using assms(1) hequiv_assign hequiv_sym unfolding hequiv_def by fast
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> Nom a\<close>
    by simp
next
  fix i
  case (Nom a)
  assume \<open>(\<^bold>\<not> Nom a) at i in' H\<close>
  then have \<open>\<not> Nom a at i in' H\<close>
    using assms(1) unfolding hintikka_def by meson
  then have \<open>\<not> hequiv H i a\<close>
    unfolding hequiv_def by blast
  then have \<open>\<not> hequiv H a i\<close>
    using assms(1) hequiv_sym by fast
  moreover have \<open>hequiv H i i\<close>
    using assms(1) \<open>(\<^bold>\<not> Nom a) at i in' H\<close> hequiv_refl' by fast
  ultimately have \<open>assign H a \<noteq> assign H i\<close>
    unfolding proj_def assign_def by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> Nom a\<close>
    by simp
next
  fix i
  case (Neg p)
  moreover assume \<open>(\<^bold>\<not> p) at i in' H\<close>
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<not> p\<close>
    using assms(1) by simp
next
  fix i
  case (Neg p)
  moreover assume \<open>(\<^bold>\<not> \<^bold>\<not> p) at i in' H\<close>
  then have \<open>p at i in' H\<close>
    using assms(1) unfolding hintikka_def by meson
  ultimately show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<not> p\<close>
    using assms(1) by auto
next
  fix i
  case (Dis p q)
  moreover assume \<open>(p \<^bold>\<or> q) at i in' H\<close>
  then have \<open>p at i in' H \<or> q at i in' H\<close>
    using assms(1) unfolding hintikka_def by meson
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> (p \<^bold>\<or> q)\<close>
    by (meson semantics.simps(4))
next
  fix i
  case (Dis p q)
  moreover assume \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) at i in' H\<close>
  then have \<open>(\<^bold>\<not> p) at i in' H\<close> \<open>(\<^bold>\<not> q) at i in' H\<close>
    using assms(1) unfolding hintikka_def by meson+
  ultimately show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> (p \<^bold>\<or> q)\<close>
    by auto
next
  fix i
  case (Dia p)
  moreover assume \<open>(\<^bold>\<diamond> p) at i in' H\<close>
  ultimately show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
  proof (cases \<open>\<exists>j. p = Nom j\<close>)
    case True
    then obtain j where \<open>p = Nom j\<close>
      by blast
    have \<open>i \<in> assign H i\<close>
      using assms(1) \<open>(\<^bold>\<diamond> p) at i in' H\<close> assign_refl' by fast
    moreover have \<open>j \<in> nominals (\<^bold>\<diamond> p)\<close>
      using \<open>p = Nom j\<close> by simp
    then have \<open>(\<exists>block \<in> H. (\<^bold>\<diamond> p) on block) \<longrightarrow> (\<exists>qs. (qs, j) \<in> H)\<close>
      using assms(1) unfolding hintikka_def by meson
    then have \<open>\<exists>bl. (bl, j) \<in> H\<close>
      using \<open>(\<^bold>\<diamond> p) at i in' H\<close> by blast
    then have \<open>j \<in> assign H j\<close>
      using assms(1) \<open>(\<^bold>\<diamond> p) at i in' H\<close> assign_refl' by fast
    moreover have \<open>(\<^bold>\<diamond> Nom j) at i in' H\<close>
      using \<open>p = Nom j\<close> \<open>(\<^bold>\<diamond> p) at i in' H\<close> by blast
    ultimately have \<open>assign H j \<in> reach H (assign H i)\<close>
      using \<open>(\<^bold>\<diamond> p) at i in' H\<close> unfolding reach_def by auto
    then show ?thesis
      using \<open>p = Nom j\<close> by simp
  next
    case False
    then have \<open>\<exists>j. (\<^bold>\<diamond> Nom j) at i in' H \<and> (\<^bold>@ j p) at i in' H\<close>
      using assms \<open>(\<^bold>\<diamond> p) at i in' H\<close> unfolding hintikka_def by blast
    then obtain j where *: \<open>(\<^bold>\<diamond> Nom j) at i in' H\<close> \<open>(\<^bold>@ j p) at i in' H\<close>
      by blast

    from *(2) have \<open>p at j in' H\<close>
      using assms(1) unfolding hintikka_def by blast
    then have \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      using Dia by blast

    have \<open>i \<in> assign H i\<close>
      using assms(1) assign_refl' \<open>(\<^bold>\<diamond> p) at i in' H\<close> by fast
    moreover have \<open>j \<in> assign H j\<close>
      using assms(1) assign_refl' \<open>p at j in' H\<close> by fast
    ultimately have \<open>assign H j \<in> reach H (assign H i)\<close>
      using *(1) unfolding reach_def by auto
    then show ?thesis
      using \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close> by auto
  qed
next
  fix i
  case (Dia p)
  assume \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at i in' H\<close>
  show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
  proof
    assume \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>\<diamond> p\<close>
    then obtain i' j where
      \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      \<open>i' \<in> assign H i\<close> \<open>(\<^bold>\<diamond> Nom j) at i' in' H\<close>
      unfolding reach_def by auto

    have \<open>Nom i' at i in' H\<close>
      using \<open>i' \<in> assign H i\<close> \<open>(\<^bold>\<diamond> Nom j) at i' in' H\<close>
      unfolding hequiv_def proj_def assign_def by auto
    then have \<open>Nom i at i' in' H\<close>
      using assms(1) unfolding hintikka_def by meson
    then have \<open>(\<^bold>\<diamond> Nom j) at i in' H\<close>
      using assms(1) \<open>(\<^bold>\<diamond> Nom j) at i' in' H\<close>
      unfolding hintikka_def by meson
    then have \<open>(\<^bold>\<not> (\<^bold>@ j p)) at i in' H\<close>
      using assms(1) \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) at i in' H\<close>
      unfolding hintikka_def by meson
    moreover have \<open>(\<^bold>\<not> p) at j in' H\<close> if \<open>\<exists>a. (\<^bold>\<not> (\<^bold>@ j p)) at a in' H\<close>
      using that assms(1) unfolding hintikka_def by blast
    ultimately have \<open>(\<^bold>\<not> p) at j in' H\<close>
      by blast
    then have \<open>\<not> Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close>
      using Dia by blast
    then show False
      using \<open>Model (reach H) (val H), assign H, assign H j \<Turnstile> p\<close> by blast
  qed
next
  fix i
  case (Sat j p)
  assume \<open>(\<^bold>@ j p) at i in' H\<close>
  moreover have \<open>p at j in' H\<close> if \<open>\<exists>a. (\<^bold>@ j p) at a in' H\<close>
    using that assms(1) unfolding hintikka_def by meson
  ultimately have \<open>p at j in' H\<close>
    by blast
  then show \<open>Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>@ j p\<close>
    using Sat by simp
next
  fix i
  case (Sat j p)
  assume \<open>(\<^bold>\<not> (\<^bold>@ j p)) at i in' H\<close>
  moreover have \<open>(\<^bold>\<not> p) at j in' H\<close> if \<open>\<exists>a. (\<^bold>\<not> (\<^bold>@ j p)) at a in' H\<close>
    using that assms(1) unfolding hintikka_def by meson
  ultimately have \<open>(\<^bold>\<not> p) at j in' H\<close>
    by blast
  then show \<open>\<not> Model (reach H) (val H), assign H, assign H i \<Turnstile> \<^bold>@ j p\<close>
    using Sat by simp
qed

subsection \<open>Lindenbaum-Henkin\<close>

text \<open>
  A set of blocks is consistent if no finite subset can be derived.
  Given a consistent set of blocks we are going to extend it to be
    saturated and maximally consistent and show that is then Hintikka.
\<close>

definition consistent :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>consistent S \<equiv> \<nexists>S'. set S' \<subseteq> S \<and> \<turnstile> S'\<close>

instance fm :: (countable, countable) countable
  by countable_datatype

definition proper_dia :: \<open>('a, 'b) fm \<Rightarrow> ('a, 'b) fm option\<close> where
  \<open>proper_dia p \<equiv>
    case p of (\<^bold>\<diamond> p) \<Rightarrow> (if \<nexists>a. p = Nom a then Some p else None) | _ \<Rightarrow> None\<close>

lemma proper_dia: \<open>proper_dia p = Some q \<Longrightarrow> p = (\<^bold>\<diamond> q) \<and> (\<nexists>a. q = Nom a)\<close>
  unfolding proper_dia_def by (cases p) (simp_all, metis option.discI option.inject)

text \<open>The following function witnesses each \<open>\<^bold>\<diamond> p\<close> in a fresh world.\<close>

primrec witness_list :: \<open>('a, 'b) fm list \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) fm list\<close> where
  \<open>witness_list [] _ = []\<close>
| \<open>witness_list (p # ps) used =
    (case proper_dia p of
      None \<Rightarrow> witness_list ps used
    | Some q \<Rightarrow>
        let i = SOME i. i \<notin> used
        in (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) # witness_list ps ({i} \<union> used))\<close>

primrec witness :: \<open>('a, 'b) block \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) block\<close> where
  \<open>witness (ps, a) used = (witness_list ps used, a)\<close>

lemma witness_list:
  \<open>proper_dia p = Some q \<Longrightarrow> witness_list (p # ps) used =
    (let i = SOME i. i \<notin> used in
      (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) # witness_list ps ({i} \<union> used))\<close>
  by simp

primrec extend ::
  \<open>('a, 'b) block set \<Rightarrow> (nat \<Rightarrow> ('a, 'b) block) \<Rightarrow> nat \<Rightarrow> ('a, 'b) block set\<close> where
  \<open>extend S f 0 = S\<close>
| \<open>extend S f (Suc n) =
    (if \<not> consistent ({f n} \<union> extend S f n)
     then extend S f n
     else
      let used = (\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block)
      in {f n, witness (f n) used} \<union> extend S f n)\<close>

definition Extend ::
  \<open>('a, 'b) block set \<Rightarrow> (nat \<Rightarrow> ('a, 'b) block) \<Rightarrow> ('a, 'b) block set\<close> where
  \<open>Extend S f \<equiv> (\<Union>n. extend S f n)\<close>

lemma extend_chain: \<open>extend S f n \<subseteq> extend S f (Suc n)\<close>
  by auto

lemma extend_mem: \<open>S \<subseteq> extend S f n\<close>
  by (induct n) auto

lemma Extend_mem: \<open>S \<subseteq> Extend S f\<close>
  unfolding Extend_def using extend_mem by blast

subsubsection \<open>Consistency\<close>

lemma split_list:
  \<open>set A \<subseteq> {x} \<union> X \<Longrightarrow> x \<in>. A \<Longrightarrow> \<exists>B. set (x # B) = set A \<and> x \<notin> set B\<close>
  by simp (metis Diff_insert_absorb mk_disjoint_insert set_removeAll)

lemma consistent_drop_single:
  fixes a :: 'b
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    cons: \<open>consistent ({(p # ps, a)} \<union> S)\<close>
  shows \<open>consistent ({(ps, a)} \<union> S)\<close>
  unfolding consistent_def
proof
  assume \<open>\<exists>S'. set S' \<subseteq> {(ps, a)} \<union> S \<and> (\<exists>n. n \<turnstile> S')\<close>
  then obtain S' n where \<open>set S' \<subseteq> {(ps, a)} \<union> S\<close> \<open>(ps, a) \<in>. S'\<close> \<open>n \<turnstile> S'\<close>
    using assms unfolding consistent_def by blast
  then obtain S'' where \<open>set ((ps, a) # S'') = set S'\<close> \<open>(ps, a) \<notin> set S''\<close>
    using split_list by metis
  then have \<open>\<turnstile> (ps, a) # S''\<close>
    using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
  then have \<open>\<turnstile> (p # ps, a) # S''\<close>
    using inf ST_struct_block[where ps'=\<open>p # ps\<close>] by fastforce
  moreover have \<open>set ((p # ps, a) # S'') \<subseteq> {(p # ps, a)} \<union> S\<close>
    using \<open>(ps, a) \<notin> set S''\<close> \<open>set ((ps, a) # S'') = set S'\<close> \<open>set S' \<subseteq> {(ps, a)} \<union> S\<close> by auto
  ultimately show False
    using cons unfolding consistent_def by blast
qed

lemma consistent_drop_block: \<open>consistent ({block} \<union> S) \<Longrightarrow> consistent S\<close>
  unfolding consistent_def by blast

lemma inconsistent_weaken: \<open>\<not> consistent S \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> \<not> consistent S'\<close>
  unfolding consistent_def by blast

lemma finite_nominals_set: \<open>finite S \<Longrightarrow> finite (\<Union>block \<in> S. block_nominals block)\<close>
  by (induct S rule: finite_induct) (simp_all add: finite_block_nominals)

lemma witness_list_used:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>finite used\<close> \<open>i \<notin> list_nominals ps\<close>
  shows \<open>i \<notin> list_nominals (witness_list ps ({i} \<union> used))\<close>
  using assms(2-)
proof (induct ps arbitrary: used)
  case (Cons p ps)
  then show ?case
  proof (cases \<open>proper_dia p\<close>)
    case (Some q)
    let ?j = \<open>SOME j. j \<notin> {i} \<union> used\<close>
    have \<open>finite ({i} \<union> used)\<close>
      using \<open>finite used\<close> by simp
    then have \<open>\<exists>j. j \<notin> {i} \<union> used\<close>
      using inf ex_new_if_finite by metis
    then have j: \<open>?j \<notin> {i} \<union> used\<close>
      using someI_ex by metis

    have \<open>witness_list (p # ps) ({i} \<union> used) =
        (\<^bold>@ ?j q) # (\<^bold>\<diamond> Nom ?j) # witness_list ps ({?j} \<union> ({i} \<union> used))\<close>
      using Some witness_list by metis
    then have *: \<open>list_nominals (witness_list (p # ps) ({i} \<union> used)) =
        {?j} \<union> nominals q \<union> list_nominals (witness_list ps ({?j} \<union> ({i} \<union> used)))\<close>
      by simp

    have \<open>finite ({?j} \<union> used)\<close>
      using \<open>finite used\<close> by simp
    moreover have \<open>i \<notin> list_nominals ps\<close>
      using \<open>i \<notin> list_nominals (p # ps)\<close> by simp
    ultimately have \<open>i \<notin> list_nominals (witness_list ps ({i} \<union> ({?j} \<union> used)))\<close>
      using Cons by metis
    moreover have \<open>{i} \<union> ({?j} \<union> used) = {?j} \<union> ({i} \<union> used)\<close>
      by blast
    moreover have \<open>i \<noteq> ?j\<close>
      using j by auto
    ultimately have \<open>i \<in> list_nominals (witness_list (p # ps) ({i} \<union> used)) \<longleftrightarrow> i \<in> nominals q\<close>
      using * by simp
    moreover have \<open>i \<notin> nominals q\<close>
      using Cons(3) Some proper_dia by fastforce
    ultimately show ?thesis
      by blast
  qed simp
qed simp

lemma witness_used:
  fixes i :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>finite used\<close> \<open>i \<notin> block_nominals block\<close>
  shows \<open>i \<notin> block_nominals (witness block ({i} \<union> used))\<close>
  using assms witness_list_used by (induct block) fastforce

lemma consistent_witness_list:
  fixes a :: 'b
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close>
    \<open>(ps, a) \<in> S\<close> \<open>finite used\<close> \<open>(\<Union> (block_nominals ` S)) \<subseteq> used\<close>
  shows \<open>consistent ({(witness_list ps used, a)} \<union> S)\<close>
  using assms(2-)
proof (induct ps arbitrary: used S)
  case Nil
  then have \<open>{(witness_list [] used, a)} \<union> S = S\<close>
    by auto
  then show ?case
    using \<open>consistent S\<close> by simp
next
  case (Cons p ps)
  have \<open>{(p # ps, a)} \<union> S = S\<close>
    using \<open>(p # ps, a) \<in> S\<close> by blast
  then have \<open>consistent ({(p # ps, a)} \<union> S)\<close>
    using \<open>consistent S\<close> by simp
  then have \<open>consistent ({(ps, a)} \<union> S)\<close>
    using inf consistent_drop_single by fast
  moreover have \<open>(ps, a) \<in> {(ps, a)} \<union> S\<close>
    by simp
  moreover have \<open>\<Union> (block_nominals ` ({(ps, a)} \<union> S)) \<subseteq> extra \<union> used\<close> for extra
    using \<open>(p # ps, a) \<in> S\<close> \<open>\<Union> (block_nominals ` S) \<subseteq> used\<close> by fastforce
  moreover have \<open>finite (extra \<union> used)\<close> if \<open>finite extra\<close> for extra
    using that \<open>finite used\<close> by blast
  ultimately have cons:
    \<open>consistent ({(witness_list ps (extra \<union> used), a)} \<union> ({(ps, a)} \<union> S))\<close>
    if \<open>finite extra\<close> for extra
    using that Cons by metis

  show ?case
  proof (cases \<open>proper_dia p\<close>)
    case None
    then have \<open>witness_list (p # ps) used = witness_list ps used\<close>
      by auto
    moreover have \<open>consistent ({(witness_list ps used, a)} \<union> ({(ps, a)} \<union> S))\<close>
      using cons[where extra=\<open>{}\<close>] by simp
    then have \<open>consistent ({(witness_list ps used, a)} \<union> S)\<close>
      using consistent_drop_block[where block=\<open>(ps, a)\<close>] by simp
    ultimately show ?thesis
      by simp
  next
    case (Some q)
    let ?i = \<open>SOME i. i \<notin> used\<close>
    have \<open>\<exists>i. i \<notin> used\<close>
      using \<open>finite used\<close> inf ex_new_if_finite by metis
    then have \<open>?i \<notin> used\<close>
      using someI_ex by metis
    then have i: \<open>?i \<notin> \<Union> (block_nominals ` S)\<close>
      using Cons by blast
    then have \<open>?i \<notin> block_nominals (p # ps, a)\<close>
      using Cons by blast

    let ?tail = \<open>witness_list ps ({?i} \<union> used)\<close>

    have \<open>consistent ({(?tail, a)} \<union> ({(ps, a)} \<union> S))\<close>
      using cons[where extra=\<open>{?i}\<close>] by simp
    then have *: \<open>consistent ({(?tail, a)} \<union> S)\<close>
      using consistent_drop_block[where block=\<open>(ps, a)\<close>] by simp

    have \<open>witness_list (p # ps) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail\<close>
      using Some witness_list by metis
    moreover have \<open>consistent ({((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S)\<close>
      unfolding consistent_def
    proof
      assume \<open>\<exists>S'. set S' \<subseteq> {((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S \<and> (\<exists>n. n \<turnstile> S')\<close>
      then obtain S' n where
        \<open>n \<turnstile> S'\<close> and S':
        \<open>set S' \<subseteq> {((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)} \<union> S\<close>
        \<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) \<in>. S'\<close>
        using * unfolding consistent_def by blast
      then obtain S'' where S'':
        \<open>set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S'') = set S'\<close>
        \<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) \<notin> set S''\<close>
        using split_list[where x=\<open>((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a)\<close>] by blast
      then have \<open>\<turnstile> ((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S''\<close>
        using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
      moreover have \<open>set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # S'') \<subseteq>
        set (((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # (p # ps, a) # S'')\<close>
        by auto
      ultimately have **:
        \<open>\<turnstile> ((\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # ?tail, a) # (p # ps, a) # S''\<close>
        using inf ST_struct by blast

      have \<open>?i \<notin> block_nominals (?tail, a)\<close>
        using inf \<open>finite used\<close> \<open>?i \<notin> block_nominals (p # ps, a)\<close> witness_used
        by fastforce
      moreover have \<open>?i \<notin> branch_nominals S''\<close>
        unfolding branch_nominals_def using i S' S'' by auto
      ultimately have \<open>?i \<notin> branch_nominals ((?tail, a) # (p # ps, a) # S'')\<close>
        using \<open>?i \<notin> block_nominals (p # ps, a)\<close> unfolding branch_nominals_def
        by simp

      moreover have \<open>\<nexists>a. q = Nom a\<close>
        using Some proper_dia by blast
      moreover have \<open>(p # ps, a) \<in>. (?tail, a) # (p # ps, a) # S''\<close>
        by simp
      moreover have \<open>p = (\<^bold>\<diamond> q)\<close>
        using Some proper_dia by blast
      then have \<open>(\<^bold>\<diamond> q) on (p # ps, a)\<close>
        by simp
      ultimately have \<open>\<turnstile> (?tail, a) # (p # ps, a) # S''\<close>
        using ** DiaP' by fast
      moreover have \<open>set ((p # ps, a) # S'') \<subseteq> S\<close>
        using Cons S' S'' by auto
      ultimately show False
        using * unfolding consistent_def by (simp add: subset_Un_eq)
    qed
    ultimately show ?thesis
      by simp
  qed
qed

lemma consistent_witness:
  fixes block :: \<open>('a, 'b) block\<close>
  assumes \<open>infinite (UNIV :: 'b set)\<close>
    \<open>consistent S\<close> \<open>finite (\<Union> (block_nominals ` S))\<close> \<open>block \<in> S\<close>
  shows \<open>consistent ({witness block (\<Union> (block_nominals ` S))} \<union> S)\<close>
  using assms consistent_witness_list by (cases block) fastforce

lemma consistent_extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>consistent (extend S f n)\<close> \<open>finite (\<Union> (block_nominals ` extend S f n))\<close>
  shows \<open>consistent (extend S f (Suc n))\<close>
proof -
  consider
    (inconsistent) \<open>\<not> consistent ({f n} \<union> extend S f n)\<close> |
    (consistent) \<open>consistent ({f n} \<union> extend S f n)\<close>
    by blast
  then show ?thesis
  proof cases
    case inconsistent
    then show ?thesis
      using assms by simp
  next
    case consistent
    let ?used = \<open>\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block\<close>
    have *: \<open>extend S f (n + 1) = {f n, witness (f n) ?used} \<union> extend S f n\<close>
      using consistent by simp

    have \<open>consistent ({f n} \<union> extend S f n)\<close>
      using consistent by simp
    moreover have \<open>finite ((\<Union> (block_nominals ` ({f n} \<union> extend S f n))))\<close>
      using \<open>finite (\<Union> (block_nominals ` extend S f n))\<close> finite_nominals_set by force
    moreover have \<open>f n \<in> {f n} \<union> extend S f n\<close>
      by simp
    ultimately have \<open>consistent ({witness (f n) ?used} \<union> ({f n} \<union> extend S f n))\<close>
      using inf consistent_witness by blast
    then show ?thesis
      using * by simp
  qed
qed

lemma finite_nominals_extend:
  assumes \<open>finite (\<Union> (block_nominals ` S))\<close>
  shows \<open>finite (\<Union> (block_nominals ` extend S f n))\<close>
  using assms by (induct n) (simp_all add: finite_block_nominals)

lemma consistent_extend':
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and \<open>consistent S\<close> \<open>finite (\<Union> (block_nominals ` S))\<close>
  shows \<open>consistent (extend S f n)\<close>
  using assms by (induct n) (simp, metis consistent_extend finite_nominals_extend)

lemma UN_finite_bound:
  assumes \<open>finite A\<close> \<open>A \<subseteq> (\<Union>n. f n)\<close>
  shows \<open>\<exists>m :: nat. A \<subseteq> (\<Union>n \<le> m. f n)\<close>
  using assms
proof (induct A rule: finite_induct)
  case (insert x A)
  then obtain m where \<open>A \<subseteq> (\<Union>n \<le> m. f n)\<close>
    by fast
  then have \<open>A \<subseteq> (\<Union>n \<le> (m + k). f n)\<close> for k
    by fastforce
  moreover obtain m' where \<open>x \<in> f m'\<close>
    using insert(4) by blast
  ultimately have \<open>{x} \<union> A \<subseteq> (\<Union>n \<le> m + m'. f n)\<close>
    by auto
  then show ?case
    by blast
qed simp

lemma extend_bound: \<open>(\<Union>n \<le> m. extend S f n) = extend S f m\<close>
proof (induct m)
  case (Suc m)
  have \<open>\<Union> (extend S f ` {..Suc m}) = \<Union> (extend S f ` {..m}) \<union> extend S f (Suc m)\<close>
    using atMost_Suc by auto
  also have \<open>\<dots> = extend S f m \<union> extend S f (Suc m)\<close>
    using Suc by blast
  also have \<open>\<dots> = extend S f (Suc m)\<close>
    using extend_chain by blast
  finally show ?case
    by simp
qed simp

lemma consistent_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>consistent S\<close> \<open>finite (\<Union> (block_nominals ` S))\<close>
  shows \<open>consistent (Extend S f)\<close>
  unfolding Extend_def
proof (rule ccontr)
  assume \<open>\<not> consistent (\<Union> (range (extend S f)))\<close>
  then obtain S' n where
    \<open>n \<turnstile> S'\<close>
    \<open>set S' \<subseteq> (\<Union>n. extend S f n)\<close>
    unfolding consistent_def by blast
  moreover have \<open>finite (set S')\<close>
    by simp
  ultimately obtain m where \<open>set S' \<subseteq> (\<Union>n \<le> m. extend S f n)\<close>
    using UN_finite_bound by metis
  then have \<open>set S' \<subseteq> extend S f m\<close>
    using extend_bound by blast
  moreover have \<open>consistent (extend S f m)\<close>
    using assms consistent_extend' by blast
  ultimately show False
    unfolding consistent_def using \<open>n \<turnstile> S'\<close> by blast
qed

subsubsection \<open>Maximality\<close>

text \<open>A set of blocks is maximally consistent if any proper extension makes it inconsistent.\<close>

definition maximal :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>maximal S \<equiv> consistent S \<and>
    (\<forall>block. block \<notin> S \<longrightarrow> \<not> consistent ({block} \<union> S))\<close>

lemma extend_not_mem:
  \<open>f n \<notin> extend S f (Suc n) \<Longrightarrow> \<not> consistent ({f n} \<union> extend S f n)\<close>
  by (metis Un_insert_left extend.simps(2) insertI1)

lemma maximal_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>consistent S\<close> \<open>finite (\<Union> (block_nominals ` S))\<close> \<open>surj f\<close>
  shows \<open>maximal (Extend S f)\<close>
proof (rule ccontr)
  assume \<open>\<not> maximal (Extend S f)\<close>
  then obtain block where
    \<open>block \<notin> Extend S f\<close> \<open>consistent ({block} \<union> Extend S f)\<close>
    unfolding maximal_def using assms consistent_Extend by blast
  obtain n where n: \<open>f n = block\<close>
    using \<open>surj f\<close> unfolding surj_def by metis
  then have \<open>block \<notin> extend S f (Suc n)\<close>
    using \<open>block \<notin> Extend S f\<close> extend_chain unfolding Extend_def by blast
  then have \<open>\<not> consistent ({block} \<union> extend S f n)\<close>
    using n extend_not_mem by blast
  moreover have \<open>block \<notin> extend S f n\<close>
    using \<open>block \<notin> extend S f (Suc n)\<close> extend_chain by auto
  then have \<open>{block} \<union> extend S f n \<subseteq> {block} \<union> Extend S f\<close>
    unfolding Extend_def by blast
  ultimately have \<open>\<not> consistent ({block} \<union> Extend S f)\<close>
    using inconsistent_weaken by blast
  then show False
    using \<open>consistent ({block} \<union> Extend S f)\<close> by blast
qed

subsubsection \<open>Saturation\<close>

text \<open>A set of blocks is saturated if every \<open>\<^bold>\<diamond> p\<close> is witnessed.\<close>

definition saturated :: \<open>('a, 'b) block set \<Rightarrow> bool\<close> where
  \<open>saturated S \<equiv> \<forall>p i. (\<^bold>\<diamond> p) at i in' S \<longrightarrow> (\<nexists>a. p = Nom a) \<longrightarrow>
    (\<exists>j. (\<^bold>@ j p) at i in' S \<and> (\<^bold>\<diamond> Nom j) at i in' S)\<close>

lemma witness_list_append:
  \<open>\<exists>extra. witness_list (ps @ qs) used = witness_list ps used @ witness_list qs (extra \<union> used)\<close>
proof (induct ps arbitrary: used)
  case Nil
  then show ?case
    by (metis Un_absorb append_self_conv2 witness_list.simps(1))
next
  case (Cons p ps)
  show ?case
  proof (cases \<open>\<exists>q. proper_dia p = Some q\<close>)
    case True
    let ?i = \<open>SOME i. i \<notin> used\<close>
    from True obtain q where q: \<open>proper_dia p = Some q\<close>
      by blast
    moreover have \<open>(p # ps) @ qs = p # (ps @ qs)\<close>
      by simp
    ultimately have
      \<open>witness_list ((p # ps) @ qs) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) #
       witness_list (ps @ qs) ({?i} \<union> used)\<close>
      using witness_list by metis
    then have
      \<open>\<exists>extra. witness_list ((p # ps) @ qs) used = (\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) #
        witness_list ps ({?i} \<union> used) @ witness_list qs (extra \<union> ({?i} \<union> used))\<close>
      using Cons by metis
    moreover have \<open>(\<^bold>@ ?i q) # (\<^bold>\<diamond> Nom ?i) # witness_list ps ({?i} \<union> used) =
        witness_list (p # ps) used\<close>
      using q witness_list by metis
    ultimately have \<open>\<exists>extra. witness_list ((p # ps) @ qs) used =
        witness_list (p # ps) used @ witness_list qs (extra \<union> ({?i} \<union> used))\<close>
      by (metis append_Cons)
    then have \<open>\<exists>extra. witness_list ((p # ps) @ qs) used =
        witness_list (p # ps) used @ witness_list qs (({?i} \<union> extra) \<union> used)\<close>
      by simp
    then show ?thesis
      by blast
  qed (simp add: Cons)
qed

lemma ex_witness_list:
  assumes \<open>p \<in>. ps\<close> \<open>proper_dia p = Some q\<close>
  shows \<open>\<exists>i. {\<^bold>@ i q, \<^bold>\<diamond> Nom i} \<subseteq> set (witness_list ps used)\<close>
  using \<open>p \<in>. ps\<close>
proof (induct ps arbitrary: used)
  case (Cons a ps)
  then show ?case
  proof (induct \<open>a = p\<close>)
    case True
    then have
      \<open>\<exists>i. witness_list (a # ps) used = (\<^bold>@ i q) # (\<^bold>\<diamond> Nom i) #
        witness_list ps ({i} \<union> used)\<close>
      using \<open>proper_dia p = Some q\<close> witness_list by metis
    then show ?case
      by auto
  next
    case False
    then have \<open>\<exists>i. {\<^bold>@ i q, \<^bold>\<diamond> Nom i} \<subseteq> set (witness_list ps (extra \<union> used))\<close> for extra
      by simp
    moreover have \<open>\<exists>extra. witness_list (a # ps) used =
        witness_list [a] used @ witness_list ps (extra \<union> used)\<close>
      using witness_list_append[where ps=\<open>[_]\<close>] by simp
    ultimately show ?case
      by fastforce
  qed
qed simp

lemma saturated_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>consistent S\<close> \<open>finite (\<Union> (block_nominals ` S))\<close> \<open>surj f\<close>
  shows \<open>saturated (Extend S f)\<close>
  unfolding saturated_def
proof safe
  fix ps i p
  assume \<open>(ps, i) \<in> Extend S f\<close> \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> \<open>\<nexists>a. p = Nom a\<close>
  obtain n where n: \<open>f n = (ps, i)\<close>
    using \<open>surj f\<close> unfolding surj_def by metis

  let ?used = \<open>(\<Union>block \<in> {f n} \<union> extend S f n. block_nominals block)\<close>

  have \<open>extend S f n \<subseteq> Extend S f\<close>
    unfolding Extend_def by auto
  moreover have \<open>consistent (Extend S f)\<close>
    using assms consistent_Extend by blast
  ultimately have \<open>consistent ({(ps, i)} \<union> extend S f n)\<close>
    using \<open>(ps, i) \<in> Extend S f\<close> inconsistent_weaken by blast
  then have \<open>extend S f (Suc n) = {f n, witness (f n) ?used} \<union> extend S f n\<close>
    using n \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> by auto
  then have \<open>witness (f n) ?used \<in> Extend S f\<close>
    unfolding Extend_def by blast
  then have *: \<open>(witness_list ps ?used, i) \<in> Extend S f\<close>
    using n by simp

  have \<open>(\<^bold>\<diamond> p) \<in>. ps\<close>
    using \<open>(\<^bold>\<diamond> p) on (ps, i)\<close> by simp
  moreover have \<open>proper_dia (\<^bold>\<diamond> p) = Some p\<close>
    unfolding proper_dia_def using \<open>\<nexists>a. p = Nom a\<close> by simp
  ultimately have \<open>\<exists>j.
      (\<^bold>@ j p) on (witness_list ps ?used, i) \<and>
      (\<^bold>\<diamond> Nom j) on (witness_list ps ?used, i)\<close>
    using ex_witness_list by fastforce
  then show \<open>\<exists>j.
      (\<exists>qs. (qs, i) \<in> Extend S f \<and> (\<^bold>@ j p) on (qs, i)) \<and>
      (\<exists>rs. (rs, i) \<in> Extend S f \<and> (\<^bold>\<diamond> Nom j) on (rs, i))\<close>
    using * by blast
qed

subsection \<open>Smullyan-Fitting\<close>

lemma hintikka_Extend:
  fixes S :: \<open>('a, 'b) block set\<close>
  assumes inf: \<open>infinite (UNIV :: 'b set)\<close> and
    \<open>maximal S\<close> \<open>consistent S\<close> \<open>saturated S\<close>
  shows \<open>hintikka S\<close>
  unfolding hintikka_def
proof safe
  fix x i j ps qs rs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Pro x on (qs, j)\<close> and
    rs: \<open>(rs, i) \<in> S\<close> \<open>(\<^bold>\<not> Pro x) on (rs, i)\<close>
  then have \<open>\<not> n \<turnstile> [(ps, i), (qs, j), (rs, i)]\<close> for n
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>n \<turnstile> [(Pro x # ps, i), (qs, j), (rs, i)]\<close> for n
    using ps(2) rs(2) by (meson Close list.set_intros(1) on.simps set_subset_Cons subsetD)
  then have \<open>n \<turnstile> [(ps, i), (qs, j), (rs, i)]\<close> for n
    using ps qs rev_nth_on
    by (meson Nom' list.set_intros(1) rev_nth_on set_subset_Cons subsetD)
  ultimately show False
    by blast
next
  fix a i ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom a on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<not> Nom a) on (qs, i)\<close>
  then have \<open>\<not> n \<turnstile> [(ps, i), (qs, i)]\<close> for n
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>n \<turnstile> [(ps, i), (qs, i)]\<close> for n
    using ps(2) qs(2) by (meson Close list.set_intros(1) set_subset_Cons subset_code(1))
  ultimately show False
    by blast
next
  fix i j ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>\<diamond> Nom j)) on (qs, i)\<close>
  then have \<open>\<not> n \<turnstile> [(ps, i), (qs, i)]\<close> for n
    using \<open>consistent S\<close> unfolding consistent_def by simp
  moreover have \<open>n \<turnstile> [(ps, i), (qs, i)]\<close> for n
    using ps(2) qs(2) Close[where p=\<open>\<^bold>\<diamond> Nom j\<close> and i=i] by force
  ultimately show False
    by blast
next
  fix p i ps a
  assume i: \<open>i \<in> nominals p\<close> and ps: \<open>(ps, a) \<in> S\<close> \<open>p on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([], i)} \<union> S\<close> and \<open>([], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un subset_insert)
    then obtain S'' where S'':
      \<open>set (([], i) # S'') = set S'\<close> \<open>([], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([], i)\<close>] by blast
    then have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using inf ST_struct[where branch'=\<open>([], i) # (ps, a) # S''\<close>] \<open>n \<turnstile> S'\<close> by fastforce
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using i ps unfolding branch_nominals_def by auto
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, j) \<in> S \<and> Nom i on (qs, j)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, j) \<in> S \<and> Nom i on (qs, j)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([Nom i], j)} \<union> S\<close> and \<open>([Nom i], j) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([Nom i], j) # S'') = set S'\<close> \<open>([Nom i], j) \<notin> set S''\<close>
      using split_list[where x=\<open>([Nom i], j)\<close>] by blast
    then have \<open>\<turnstile> ([Nom i], j) # (ps, i) # S''\<close>
      using inf ST_struct[where branch'=\<open>([Nom i], j) # (ps, i) # S''\<close>] \<open>n \<turnstile> S'\<close> by fastforce
    then have \<open>\<turnstile> ([], j) # (ps, i) # S''\<close>
      using \<open>Nom j on (ps, i)\<close> by (meson Nom' list.set_intros(1) list.set_intros(2) on.simps)
    moreover have \<open>j \<in> branch_nominals ((ps, i) # S'')\<close>
      using \<open>Nom j on (ps, i)\<close> unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, i) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>Nom j on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Nom k on (qs, j)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> Nom k on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, i) \<in> S \<and> Nom k on (rs, i)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([Nom k], i)} \<union> S\<close> and \<open>([Nom k], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([Nom k], i) # S'') = set S'\<close> \<open>([Nom k], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([Nom k], i)\<close>] by blast
    then have \<open>\<turnstile> ([Nom k], i) # (Nom k # ps, i) # (qs, j) # S''\<close>
      using inf ST_struct[where branch'=\<open>([Nom k], i) # (Nom k # ps, i) # (qs, j) # S''\<close>] \<open>n \<turnstile> S'\<close>
      by fastforce
    then have \<open>\<turnstile> ([], i) # (Nom k # ps, i) # (qs, j) # S''\<close>
      by (meson Nom' list.set_intros(1-2) on.simps)
    moreover have \<open>i \<in> branch_nominals ((Nom k # ps, i) # (qs, j) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (Nom k # ps, i) # (qs, j) # S''\<close>
      using GoTo by fast
    then have \<open>\<turnstile> (ps, i) # (qs, j) # S''\<close>
      using ps qs by (meson Nom' list.set_intros(1-2) on.simps)
    moreover have \<open>set ((ps, i) # (qs, j) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, j) \<in> S\<close> \<open>Nom k on (qs, j)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>\<diamond> Nom k) on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, i) \<in> S \<and> (\<^bold>\<diamond> Nom k) on (rs, i)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<diamond> Nom k], i)} \<union> S\<close> and \<open>([\<^bold>\<diamond> Nom k], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([\<^bold>\<diamond> Nom k], i) # S'') = set S'\<close> \<open>([\<^bold>\<diamond> Nom k], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<diamond> Nom k], i)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<diamond> Nom k], i) # (ps, i) # (qs, j) # S''\<close>
      using inf ST_struct[where branch'=\<open>([\<^bold>\<diamond> Nom k], i) # (ps, i) # (qs, j) # S''\<close>] \<open>n \<turnstile> S'\<close>
      by fastforce
    then have \<open>\<turnstile> ([], i) # (ps, i) # (qs, j) # S''\<close>
      using ps(2) qs(2) inf by (meson Bridge list.set_intros(1) on.simps set_subset_Cons subset_iff)
    moreover have \<open>i \<in> branch_nominals ((ps, i) # (qs, j) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, i) # (qs, j) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, i) # (qs, j) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix i j k ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>Nom k on (qs, i)\<close>
  show \<open>\<exists>rs. (rs, k) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (rs, k)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>rs. (rs, k) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (rs, k)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<diamond> Nom j], k)} \<union> S\<close> and \<open>([\<^bold>\<diamond> Nom j], k) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([\<^bold>\<diamond> Nom j], k) # S'') = set S'\<close> \<open>([\<^bold>\<diamond> Nom j], k) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<diamond> Nom j], k)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<diamond> Nom j], k) # (Nom k # ps, i) # (qs, i) # S''\<close>
      using inf ST_struct[where branch'=\<open>([\<^bold>\<diamond> Nom j], k) # (Nom k # ps, i) # (qs, i) # S''\<close>] \<open>n \<turnstile> S'\<close>
      by fastforce
    then have \<open>\<turnstile> ([], k) # (Nom k # ps, i) # (qs, i) # S''\<close>
      using ps(2) by (meson Nom' fm.simps(22) list.set_intros(1-2) on.simps)
    moreover have \<open>k \<in> branch_nominals ((Nom k # ps, i) # (qs, i) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (Nom k # ps, i) # (qs, i) # S''\<close>
      using GoTo by fast
    then have \<open>\<turnstile> (ps, i) # (qs, i) # S''\<close>
      using ps(2) qs(2) by (meson Nom' list.set_intros(1-2) on.simps)
    moreover have \<open>set ((ps, i) # (qs, i) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p q i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(p \<^bold>\<or> q) on (ps, i)\<close> and *: \<open>\<not> q at i in' S\<close>
  show \<open>p at i in' S\<close>
  proof (rule ccontr)
    assume \<open>\<not> p at i in' S\<close>
    then obtain Sp' np where
      \<open>np \<turnstile> Sp'\<close> and Sp': \<open>set Sp' \<subseteq> {(p # ps, i)} \<union> S\<close> and \<open>(p # ps, i) \<in>. Sp'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain Sp'' where Sp'':
      \<open>set ((p # ps, i) # Sp'') = set Sp'\<close> \<open>(p # ps, i) \<notin> set Sp''\<close>
      using split_list[where x=\<open>(p # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (p # ps, i) # Sp''\<close>
      using \<open>np \<turnstile> Sp'\<close> inf ST_struct by blast

    obtain Sq' nq where
      \<open>nq \<turnstile> Sq'\<close> and Sq': \<open>set Sq' \<subseteq> {(q # ps, i)} \<union> S\<close> and \<open>(q # ps, i) \<in>. Sq'\<close>
      using * \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain Sq'' where Sq'':
      \<open>set ((q # ps, i) # Sq'') = set Sq'\<close> \<open>(q # ps, i) \<notin> set Sq''\<close>
      using split_list[where x=\<open>(q # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (q # ps, i) # Sq''\<close>
      using \<open>nq \<turnstile> Sq'\<close> inf ST_struct by blast

    obtain S'' where S'': \<open>set S'' = set Sp'' \<union> set Sq''\<close>
      by (meson set_union)
    then have
      \<open>set ((p # ps, i) # Sp'') \<subseteq> set ((p # ps, i) # S'')\<close>
      \<open>set ((q # ps, i) # Sq'') \<subseteq> set ((q # ps, i) # S'')\<close>
      by auto
    then have \<open>\<turnstile> (p # ps, i) # S''\<close> \<open>\<turnstile> (q # ps, i) # S''\<close>
      using \<open>\<turnstile> (p # ps, i) # Sp''\<close> \<open>\<turnstile> (q # ps, i) # Sq''\<close> inf ST_struct by blast+
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps by (meson DisP'' list.set_intros(1))
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using ps Sp' Sp'' Sq' Sq'' S'' by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p q i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (ps, i)\<close>
  show \<open>(\<^bold>\<not> p) at i in' S\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<^bold>\<not> p) at i in' S\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and
      S': \<open>set S' \<subseteq> {((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)} \<union> S\<close> and
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis (mono_tags, lifting) insert_is_Un insert_subset list.simps(15) on.simps
          set_subset_Cons subset_insert)
    then obtain S'' where S'':
      \<open>set (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S'') = set S'\<close>
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<notin> set S''\<close>
      using split_list[where x=\<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)\<close>] by blast
    then have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S''\<close>
      using inf ST_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps by (meson DisN' list.set_intros(1))
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p q i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> (p \<^bold>\<or> q)) on (ps, i)\<close>
  show \<open>(\<^bold>\<not> q) at i in' S\<close>
  proof (rule ccontr)
    assume \<open>\<not> (\<^bold>\<not> q) at i in' S\<close>
    then obtain S' where
      \<open>\<turnstile> S'\<close> and
      S': \<open>set S' \<subseteq> {((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)} \<union> S\<close> and
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis (mono_tags, lifting) insert_is_Un insert_subset list.simps(15) on.simps
          set_subset_Cons subset_insert)
    then obtain S'' where S'':
      \<open>set (((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S'') = set S'\<close>
      \<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) \<notin> set S''\<close>
      using split_list[where x=\<open>((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i)\<close>] by blast
    then have \<open>\<turnstile> ((\<^bold>\<not> q) # (\<^bold>\<not> p) # ps, i) # S''\<close>
      using inf ST_struct \<open>\<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps by (meson DisN' list.set_intros(1))
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps
  assume ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> \<^bold>\<not> p) on (ps, i)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {(p # ps, i)} \<union> S\<close> and \<open>(p # ps, i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set ((p # ps, i) # S'') = set S'\<close> \<open>(p # ps, i) \<notin> set S''\<close>
      using split_list[where x=\<open>(p # ps, i)\<close>] by blast
    then have \<open>\<turnstile> (p # ps, i) # S''\<close>
      using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> (ps, i) # S''\<close>
      using ps by (meson Neg' list.set_intros(1))
    moreover have \<open>set ((ps, i) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps a
  assume ps: \<open>(ps, a) \<in> S\<close> \<open>(\<^bold>@ i p) on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> p on (qs, i)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([p], i)} \<union> S\<close> and \<open>([p], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([p], i) # S'') = set S'\<close> \<open>([p], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([p], i)\<close>] by blast
    then have \<open>\<turnstile> ([p], i) # S''\<close>
      using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
    moreover have \<open>set (([p], i) # S'') \<subseteq> set (([p], i) # (ps, a) # S'')\<close>
      by auto
    ultimately have \<open>\<turnstile> ([p], i) # (ps, a) # S''\<close>
      using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using ps by (metis SatP' insert_iff list.simps(15))
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps a
  assume ps: \<open>(ps, a) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>@ i p)) on (ps, a)\<close>
  show \<open>\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> p) on (qs, i)\<close>
    then obtain S' n where
      \<open>n \<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<not> p], i)} \<union> S\<close> and \<open>([\<^bold>\<not> p], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([\<^bold>\<not> p], i) # S'') = set S'\<close> \<open>([\<^bold>\<not> p], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<not> p], i)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> p], i) # S''\<close>
      using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> p], i) # (ps, a) # S''\<close>
      using inf ST_struct[where branch'=\<open>([\<^bold>\<not> p], i) # _ # S''\<close>] \<open>n \<turnstile> S'\<close>
      by fastforce
    then have \<open>\<turnstile> ([], i) # (ps, a) # S''\<close>
      using ps by (metis SatN' insert_iff list.simps(15))
    moreover have \<open>i \<in> branch_nominals ((ps, a) # S'')\<close>
      using ps unfolding branch_nominals_def by fastforce
    ultimately have \<open>\<turnstile> (ps, a) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, a) # S'') \<subseteq> S\<close>
      using S' S'' ps by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
next
  fix p i ps
  assume
    \<open>\<nexists>a. p = Nom a\<close> and
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<diamond> p) on (ps, i)\<close>
  then show \<open>\<exists>j.
      (\<exists>qs. (qs, i) \<in> S \<and> (\<^bold>\<diamond> Nom j) on (qs, i)) \<and>
      (\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>@ j p) on (rs, i))\<close>
    using \<open>saturated S\<close> unfolding saturated_def by blast
next
  fix p i j ps qs
  assume
    ps: \<open>(ps, i) \<in> S\<close> \<open>(\<^bold>\<not> (\<^bold>\<diamond> p)) on (ps, i)\<close> and
    qs: \<open>(qs, i) \<in> S\<close> \<open>(\<^bold>\<diamond> Nom j) on (qs, i)\<close>
  show \<open>\<exists>rs. (rs, i) \<in> S \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (rs, i)\<close>
  proof (rule ccontr)
    assume \<open>\<nexists>qs. (qs, i) \<in> S \<and> (\<^bold>\<not> (\<^bold>@ j p)) on (qs, i)\<close>
    then obtain S' n where
      \<open>n\<turnstile> S'\<close> and S': \<open>set S' \<subseteq> {([\<^bold>\<not> (\<^bold>@ j p)], i)} \<union> S\<close> and \<open>([\<^bold>\<not> (\<^bold>@ j p)], i) \<in>. S'\<close>
      using \<open>maximal S\<close> unfolding maximal_def consistent_def
      by (metis insert_is_Un list.set_intros(1) on.simps subset_insert)
    then obtain S'' where S'':
      \<open>set (([\<^bold>\<not> (\<^bold>@ j p)], i) # S'') = set S'\<close> \<open>([\<^bold>\<not> (\<^bold>@ j p)], i) \<notin> set S''\<close>
      using split_list[where x=\<open>([\<^bold>\<not> (\<^bold>@ j p)], i)\<close>] by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> (\<^bold>@ j p)], i) # S''\<close>
      using inf ST_struct \<open>n \<turnstile> S'\<close> by blast
    then have \<open>\<turnstile> ([\<^bold>\<not> (\<^bold>@ j p)], i) # (ps, i) # (qs, i) # S''\<close>
      using inf ST_struct[where branch'=\<open>([_], _) # (ps, i) # (qs, i) # S''\<close>] \<open>n \<turnstile> S'\<close>
      by fastforce
    then have \<open>\<turnstile> ([], i) # (ps, i) # (qs, i) # S''\<close>
      using ps(2) qs(2) by (meson DiaN' list.set_intros(1) set_subset_Cons subset_iff)
    moreover have \<open>i \<in> branch_nominals ((ps, i) # (qs, i) # S'')\<close>
      unfolding branch_nominals_def by simp
    ultimately have \<open>\<turnstile> (ps, i) # (qs, i) # S''\<close>
      using GoTo by fast
    moreover have \<open>set ((ps, i) # (qs, i) # S'') \<subseteq> S\<close>
      using S' S'' ps qs by auto
    ultimately show False
      using \<open>consistent S\<close> unfolding consistent_def by blast
  qed
qed

subsection \<open>Result\<close>

theorem completeness:
  fixes p :: \<open>('a :: countable, 'b :: countable) fm\<close>
  assumes
    inf: \<open>infinite (UNIV :: 'b set)\<close> and
    valid: \<open>\<forall>(M :: ('b set, 'a) model) g w. M, g, w \<Turnstile> p\<close>
  shows \<open>1 \<turnstile> [([\<^bold>\<not> p], i)]\<close>
proof -
  have \<open>\<turnstile> [([\<^bold>\<not> p], i)]\<close>
  proof (rule ccontr)
    assume \<open>\<not> \<turnstile> [([\<^bold>\<not> p], i)]\<close>
    then have *: \<open>consistent {([\<^bold>\<not> p], i)}\<close>
      unfolding consistent_def using ST_struct inf
      by (metis empty_set list.simps(15))

    let ?S = \<open>Extend {([\<^bold>\<not> p], i)} from_nat\<close>
    have \<open>finite {([\<^bold>\<not> p], i)}\<close>
      by simp
    then have fin: \<open>finite (\<Union> (block_nominals ` {([\<^bold>\<not> p], i)}))\<close>
      using finite_nominals_set by blast

    have \<open>consistent ?S\<close>
      using consistent_Extend inf * fin by blast
    moreover have \<open>maximal ?S\<close>
      using maximal_Extend inf * fin by fastforce
    moreover have \<open>saturated ?S\<close>
      using saturated_Extend inf * fin by fastforce
    ultimately have \<open>hintikka ?S\<close>
      using hintikka_Extend inf by blast
    moreover have \<open>([\<^bold>\<not> p], i) \<in> ?S\<close>
      using Extend_mem by blast
    moreover have \<open>(\<^bold>\<not> p) on ([\<^bold>\<not> p], i)\<close>
      by simp
    ultimately have \<open>\<not> Model (reach ?S) (val ?S), assign ?S, assign ?S i \<Turnstile> p\<close>
      using hintikka_model by fast
    then show False
      using valid by blast
  qed
  then show ?thesis
    using ST_one by blast
qed

text \<open>
  We arbitrarily fix nominal and propositional symbols to be natural numbers
  (any countably infinite type suffices) and
  define validity as truth in all models with sets of natural numbers as worlds.
  We show below that this implies validity for any type of worlds.
\<close>

abbreviation
  \<open>valid p \<equiv> \<forall>(M :: (nat set, nat) model) (g :: nat \<Rightarrow> _) w. M, g, w \<Turnstile> p\<close>

text \<open>A formula is valid iff its negation has a closing tableau from a fresh world.\<close>

theorem main:
  assumes \<open>i \<notin> nominals p\<close>
  shows \<open>valid p \<longleftrightarrow> 1 \<turnstile> [([\<^bold>\<not> p], i)]\<close>
proof
  assume \<open>valid p\<close>
  then show \<open>1 \<turnstile> [([\<^bold>\<not> p], i)]\<close>
    using completeness by blast
next
  assume \<open>1 \<turnstile> [([\<^bold>\<not> p], i)]\<close>
  then show \<open>valid p\<close>
    using assms soundness_fresh by fast
qed

text \<open>The restricted validity implies validity in general.\<close>

theorem valid_semantics:
  \<open>valid p \<longrightarrow> M, g, w \<Turnstile> p\<close>
proof
  assume \<open>valid p\<close>
  then have \<open>i \<notin> nominals p \<Longrightarrow> \<turnstile> [([\<^bold>\<not> p], i)]\<close> for i
    using main by blast
  moreover have \<open>\<exists>i. i \<notin> nominals p\<close>
    by (simp add: finite_nominals ex_new_if_finite)
  ultimately show \<open>M, g, w \<Turnstile> p\<close>
    using soundness_fresh by fast
qed

end
