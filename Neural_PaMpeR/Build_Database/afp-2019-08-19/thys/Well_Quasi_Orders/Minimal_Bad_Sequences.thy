(*  Title:      Well-Quasi-Orders
    Author:     Christian Sternagel <c.sternagel@gmail.com>
    Maintainer: Christian Sternagel
    License:    LGPL
*)

section \<open>Constructing Minimal Bad Sequences\<close>

theory Minimal_Bad_Sequences
imports
  Almost_Full
  Minimal_Elements
begin

text \<open>
  A locale capturing the construction of minimal bad sequences over values from @{term "A"}. Where
  minimality is to be understood w.r.t.\ @{term size} of an element.
\<close>
locale mbs =
  fixes A :: "('a :: size) set"
begin

text \<open>
  Since the @{term size} is a well-founded measure, whenever some element satisfies a property
  @{term P}, then there is a size-minimal such element.
\<close>
lemma minimal:
  assumes "x \<in> A" and "P x"
  shows "\<exists>y \<in> A. size y \<le> size x \<and> P y \<and> (\<forall>z \<in> A. size z < size y \<longrightarrow> \<not> P z)"
using assms
proof (induction x taking: size rule: measure_induct)
  case (1 x)
  then show ?case
  proof (cases "\<forall>y \<in> A. size y < size x \<longrightarrow> \<not> P y")
    case True
    with 1 show ?thesis by blast
  next
    case False
    then obtain y where "y \<in> A" and "size y < size x" and "P y" by blast
    with "1.IH" show ?thesis by (fastforce elim!: order_trans)
  qed
qed

lemma less_not_eq [simp]:
  "x \<in> A \<Longrightarrow> size x < size y \<Longrightarrow> x = y \<Longrightarrow> False"
  by simp

text \<open>
  The set of all bad sequences over @{term A}.
\<close>
definition "BAD P = {f \<in> SEQ A. bad P f}"

lemma BAD_iff [iff]:
  "f \<in> BAD P \<longleftrightarrow> (\<forall>i. f i \<in> A) \<and> bad P f"
  by (auto simp: BAD_def)

text \<open>
  A partial order on infinite bad sequences.
\<close>
definition geseq :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set"
where
  "geseq =
    {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j)))}"

text \<open>
  The strict part of the above order.
\<close>
definition gseq :: "((nat \<Rightarrow> 'a) \<times> (nat \<Rightarrow> 'a)) set" where
  "gseq = {(f, g). f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j))}"

lemma geseq_iff:
  "(f, g) \<in> geseq \<longleftrightarrow>
    f \<in> SEQ A \<and> g \<in> SEQ A \<and> (f = g \<or> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j)))"
  by (auto simp: geseq_def)

lemma gseq_iff:
  "(f, g) \<in> gseq \<longleftrightarrow> f \<in> SEQ A \<and> g \<in> SEQ A \<and> (\<exists>i. size (g i) < size (f i) \<and> (\<forall>j < i. f j = g j))"
  by (auto simp: gseq_def)

lemma geseqE:
  assumes "(f, g) \<in> geseq"
    and "\<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; f = g\<rbrakk> \<Longrightarrow> Q"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; size (g i) < size (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: geseq_iff)

lemma gseqE:
  assumes "(f, g) \<in> gseq"
    and "\<And>i. \<lbrakk>\<forall>i. f i \<in> A; \<forall>i. g i \<in> A; size (g i) < size (f i); \<forall>j < i. f j = g j\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
  using assms by (auto simp: gseq_iff)

interpretation min_elt_size?: minimal_element "measure_on size UNIV" A
rewrites "measure_on size UNIV \<equiv> \<lambda>x y. size x < size y"
apply (unfold_locales)
apply (auto simp: po_on_def irreflp_on_def transp_on_def simp del: wfp_on_UNIV intro: wfp_on_subset)
apply (auto simp: measure_on_def inv_image_betw_def)
done

context
  fixes P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
begin

text \<open>
  A lower bound to all sequences in a set of sequences @{term B}.
\<close>
abbreviation "lb \<equiv> lexmin (BAD P)"

lemma eq_upto_BAD_mem:
  assumes "f \<in> eq_upto (BAD P) g i"
  shows "f j \<in> A"
  using assms by (auto)

text \<open>
  Assume that there is some infinite bad sequence @{term h}.
\<close>
context
  fixes h :: "nat \<Rightarrow> 'a"
  assumes BAD_ex: "h \<in> BAD P"
begin

text \<open>
  When there is a bad sequence, then filtering @{term "BAD P"} w.r.t.~positions in @{term lb} never
  yields an empty set of sequences.
\<close>
lemma eq_upto_BAD_non_empty:
  "eq_upto (BAD P) lb i \<noteq> {}"
using eq_upto_lexmin_non_empty [of "BAD P"] and BAD_ex by auto

lemma non_empty_ith:
  shows "ith (eq_upto (BAD P) lb i) i \<subseteq> A"
  and "ith (eq_upto (BAD P) lb i) i \<noteq> {}"
  using eq_upto_BAD_non_empty [of i] by auto

lemmas
  lb_minimal = min_elt_minimal [OF non_empty_ith, folded lexmin] and
  lb_mem = min_elt_mem [OF non_empty_ith, folded lexmin]

text \<open>
  @{term "lb"} is a infinite bad sequence.
\<close>
lemma lb_BAD:
  "lb \<in> BAD P"
proof -
  have *: "\<And>j. lb j \<in> ith (eq_upto (BAD P) lb j) j" by (rule lb_mem)
  then have "\<forall>i. lb i \<in> A" by (auto simp: ith_conv) (metis eq_upto_BAD_mem)
  moreover
  { assume "good P lb"
    then obtain i j where "i < j" and "P (lb i) (lb j)" by (auto simp: good_def)
    from * have "lb j \<in> ith (eq_upto (BAD P) lb j) j" by (auto)
    then obtain g where "g \<in> eq_upto (BAD P) lb j" and "g j = lb j" by force
    then have "\<forall>k \<le> j. g k = lb k" by (auto simp: order_le_less)
    with \<open>i < j\<close> and \<open>P (lb i) (lb j)\<close> have "P (g i) (g j)" by auto
    with \<open>i < j\<close> have "good P g" by (auto simp: good_def)
    with \<open>g \<in> eq_upto (BAD P) lb j\<close> have False by auto }
  ultimately show ?thesis by blast
qed

text \<open>
  There is no infinite bad sequence that is strictly smaller than @{term lb}.
\<close>
lemma lb_lower_bound:
  "\<forall>g. (lb, g) \<in> gseq \<longrightarrow> g \<notin> BAD P"
proof (intro allI impI)
  fix g
  assume "(lb, g) \<in> gseq"
  then obtain i where "g i \<in> A" and "size (g i) < size (lb i)"
    and "\<forall>j < i. lb j = g j" by (auto simp: gseq_iff)
  moreover with lb_minimal
    have "g i \<notin> ith (eq_upto (BAD P) lb i) i" by auto
  ultimately show "g \<notin> BAD P" by blast
qed

text \<open>
  If there is at least one bad sequence, then there is also a minimal one.
\<close>
lemma lower_bound_ex:
  "\<exists>f \<in> BAD P. \<forall>g. (f, g) \<in> gseq \<longrightarrow> g \<notin> BAD P"
  using lb_BAD and lb_lower_bound by blast

lemma gseq_conv:
  "(f, g) \<in> gseq \<longleftrightarrow> f \<noteq> g \<and> (f, g) \<in> geseq"
  by (auto simp: gseq_def geseq_def dest: less_not_eq)

text \<open>There is a minimal bad sequence.\<close>
lemma mbs:
  "\<exists>f \<in> BAD P. \<forall>g. (f, g) \<in> gseq \<longrightarrow> good P g"
  using lower_bound_ex by (auto simp: gseq_conv geseq_iff)

end

end

end

end
