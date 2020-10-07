(*
 * May's Theorem, following Sen.
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced October 2008.
 * License: BSD
 *)

(*<*)
theory May

imports SCFs

begin
(*>*)

section\<open>May's Theorem\<close>

text \<open>May's Theorem \cite{May:1952} provides a characterisation of
majority voting in terms of four conditions that appear quite natural for
\emph{a priori} unbiased social choice scenarios. It can be seen as a
refinement of some earlier work by Arrow \cite[Chapter V.1]{Arrow:1963}.

The following is a mechanisation of Sen's generalisation
\cite[Chapter~5*]{Sen:70a}; originally Arrow and May consider only two
alternatives, whereas Sen's model maps profiles of full RPRs to a possibly
intransitive relation that does at least generate a choice set that
satisfies May's conditions.\<close>

subsection\<open>May's Conditions\<close>

text \<open>The condition of \emph{anonymity} asserts that the individuals'
identities are not considered by the choice rule. Rather than talk about
permutations we just assert the result of the SCF is the same when the
profile is composed with an arbitrary bijection on the set of
individuals.\<close>

definition anonymous :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "anonymous scf A Is \<equiv>
    (\<forall>P f x y. profile A Is P \<and> bij_betw f Is Is \<and> x \<in> A \<and> y \<in> A
      \<longrightarrow> (x \<^bsub>(scf P)\<^esub>\<preceq> y) = (x \<^bsub>(scf (P \<circ> f))\<^esub>\<preceq> y))"

lemma anonymousI[intro]:
  "(\<And>P f x y. \<lbrakk> profile A Is P; bij_betw f Is Is;
                  x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow> (x \<^bsub>(scf P)\<^esub>\<preceq> y) = (x \<^bsub>(scf (P \<circ> f))\<^esub>\<preceq> y))
  \<Longrightarrow> anonymous scf A Is"
  unfolding anonymous_def by simp

lemma anonymousD:
  "\<lbrakk> anonymous scf A Is; profile A Is P; bij_betw f Is Is; x \<in> A; y \<in> A \<rbrakk>
  \<Longrightarrow> (x \<^bsub>(scf P)\<^esub>\<preceq> y) = (x \<^bsub>(scf (P \<circ> f))\<^esub>\<preceq> y)"
  unfolding anonymous_def by simp

text \<open>Similarly, an SCF is \emph{neutral} if it is insensitive to the
identity of the alternatives. This is Sen's characterisation
\cite[p72]{Sen:70a}.\<close>

definition neutral :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "neutral scf A Is \<equiv>
    (\<forall>P P' x y z w. profile A Is P \<and> profile A Is P' \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A \<and> w \<in> A
      \<and> (\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(P' i)\<^esub>\<preceq> w) \<and> (\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(P' i)\<^esub>\<preceq> z)
   \<longrightarrow> ((x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(scf P')\<^esub>\<preceq> w) \<and> (y \<^bsub>(scf P)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(scf P')\<^esub>\<preceq> z)))"

lemma neutralI[intro]:
  "(\<And>P P' x y z w.
    \<lbrakk> profile A Is P; profile A Is P'; {x,y,z,w} \<subseteq> A;
      \<And>i. i \<in> Is \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(P' i)\<^esub>\<preceq> w;
      \<And>i. i \<in> Is \<Longrightarrow> y \<^bsub>(P i)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(P' i)\<^esub>\<preceq> z \<rbrakk>
     \<Longrightarrow> ((x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(scf P')\<^esub>\<preceq> w) \<and> (y \<^bsub>(scf P)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(scf P')\<^esub>\<preceq> z)))
  \<Longrightarrow> neutral scf A Is"
  unfolding neutral_def by simp

lemma neutralD:
  "\<lbrakk> neutral scf A Is;
     profile A Is P; profile A Is P'; {x,y,z,w} \<subseteq> A;
     \<And>i. i \<in> Is \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(P' i)\<^esub>\<preceq> w;
     \<And>i. i \<in> Is \<Longrightarrow> y \<^bsub>(P i)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(P' i)\<^esub>\<preceq> z \<rbrakk>
  \<Longrightarrow> (x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> z \<^bsub>(scf P')\<^esub>\<preceq> w) \<and> (y \<^bsub>(scf P)\<^esub>\<preceq> x \<longleftrightarrow> w \<^bsub>(scf P')\<^esub>\<preceq> z)"
  unfolding neutral_def by simp

text \<open>Neutrality implies independence of irrelevant alternatives.\<close>

lemma neutral_iia: "neutral scf A Is \<Longrightarrow> iia scf A Is"
  unfolding neutral_def by (rule, auto)

text \<open>\emph{Positive responsiveness} is a bit like non-manipulability: if
one individual improves their opinion of $x$, then the result should shift
in favour of $x$.\<close>

definition positively_responsive :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "positively_responsive scf A Is \<equiv>
    (\<forall>P P' x y. profile A Is P \<and> profile A Is P' \<and> x \<in> A \<and> y \<in> A
      \<and> (\<forall>i \<in> Is. (x \<^bsub>(P i)\<^esub>\<prec> y \<longrightarrow> x \<^bsub>(P' i)\<^esub>\<prec> y) \<and> (x \<^bsub>(P i)\<^esub>\<approx> y \<longrightarrow> x \<^bsub>(P' i)\<^esub>\<preceq> y))
      \<and> (\<exists>k \<in> Is. (x \<^bsub>(P k)\<^esub>\<approx> y \<and> x \<^bsub>(P' k)\<^esub>\<prec> y) \<or> (y \<^bsub>(P k)\<^esub>\<prec> x \<and> x \<^bsub>(P' k)\<^esub>\<preceq> y))
      \<longrightarrow> x \<^bsub>(scf P)\<^esub>\<preceq> y \<longrightarrow> x \<^bsub>(scf P')\<^esub>\<prec> y)"

lemma positively_responsiveI[intro]:
  assumes I: "\<And>P P' x y.
    \<lbrakk> profile A Is P; profile A Is P'; x \<in> A; y \<in> A;
      \<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(P i)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<prec> y;
      \<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(P i)\<^esub>\<approx> y \<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<preceq> y;
      \<exists>k \<in> Is. (x \<^bsub>(P k)\<^esub>\<approx> y \<and> x \<^bsub>(P' k)\<^esub>\<prec> y) \<or> (y \<^bsub>(P k)\<^esub>\<prec> x \<and> x \<^bsub>(P' k)\<^esub>\<preceq> y);
      x \<^bsub>(scf P)\<^esub>\<preceq> y \<rbrakk>
     \<Longrightarrow> x \<^bsub>(scf P')\<^esub>\<prec> y"
  shows "positively_responsive scf A Is"
  unfolding positively_responsive_def
  by (blast intro: I)

lemma positively_responsiveD:
  "\<lbrakk> positively_responsive scf A Is;
     profile A Is P; profile A Is P'; x \<in> A; y \<in> A;
     \<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(P i)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<prec> y;
     \<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(P i)\<^esub>\<approx> y \<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<preceq> y;
     \<exists>k \<in> Is. (x \<^bsub>(P k)\<^esub>\<approx> y \<and> x \<^bsub>(P' k)\<^esub>\<prec> y) \<or> (y \<^bsub>(P k)\<^esub>\<prec> x \<and> x \<^bsub>(P' k)\<^esub>\<preceq> y);
     x \<^bsub>(scf P)\<^esub>\<preceq> y \<rbrakk>
       \<Longrightarrow> x \<^bsub>(scf P')\<^esub>\<prec> y"
  unfolding positively_responsive_def
  apply clarsimp
  apply (erule allE[where x=P])
  apply (erule allE[where x=P'])
  apply (erule allE[where x=x])
  apply (erule allE[where x=y])
  by auto

subsection\<open>The Method of Majority Decision satisfies May's conditions\<close>

text \<open>The \emph{method of majority decision} (MMD) says that if the number
of individuals who strictly prefer $x$ to $y$ is larger than or equal to
those who strictly prefer the converse, then $x\ R\ y$. Note that this
definition only makes sense for a finite population.\<close>

definition MMD :: "'i set \<Rightarrow> ('a, 'i) SCF" where
  "MMD Is P \<equiv> { (x, y) . card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } \<ge> card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x } }"

text \<open>The first part of May's Theorem establishes that the conditions are
consistent, by showing that they are satisfied by MMD.\<close>

lemma MMD_l2r:
  fixes A :: "'a set"
    and Is :: "'i set"
  assumes finiteIs: "finite Is"
  shows "SCF (MMD Is) A Is universal_domain"
    and "anonymous (MMD Is) A Is"
    and "neutral (MMD Is) A Is"
    and "positively_responsive (MMD Is) A Is"
proof -
  show "SCF (MMD Is) A Is universal_domain"
  proof
    fix P show "complete A (MMD Is P)"
      by (rule completeI, unfold MMD_def, simp, arith)
  qed
  show "anonymous (MMD Is) A Is"
  proof
    fix P
    fix x y :: "'a"
    fix f assume bijf: "bij_betw f Is Is"
    show "(x \<^bsub>(MMD Is P)\<^esub>\<preceq> y) = (x \<^bsub>(MMD Is (P \<circ> f))\<^esub>\<preceq> y)"
      using card_compose_bij[OF bijf, where P="\<lambda>i. x \<^bsub>(P i)\<^esub>\<prec> y"]
            card_compose_bij[OF bijf, where P="\<lambda>i. y \<^bsub>(P i)\<^esub>\<prec> x"]
      unfolding MMD_def by simp
  qed
next
  show "neutral (MMD Is) A Is"
  proof
    fix P P'
    fix x y z w assume xyzwA: "{x,y,z,w} \<subseteq> A"
    assume xyzw: "\<And>i. i \<in> Is \<Longrightarrow> (x \<^bsub>(P i)\<^esub>\<preceq> y) = (z \<^bsub>(P' i)\<^esub>\<preceq> w)"
       and yxwz: "\<And>i. i \<in> Is \<Longrightarrow> (y \<^bsub>(P i)\<^esub>\<preceq> x) = (w \<^bsub>(P' i)\<^esub>\<preceq> z)"
    from xyzwA xyzw yxwz
    have "{ i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } = { i \<in> Is. z \<^bsub>(P' i)\<^esub>\<prec> w }"
     and "{ i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x } = { i \<in> Is. w \<^bsub>(P' i)\<^esub>\<prec> z }"
      unfolding strict_pref_def by auto
    thus "(x \<^bsub>(MMD Is P)\<^esub>\<preceq> y) = (z \<^bsub>(MMD Is P')\<^esub>\<preceq> w) \<and>
          (y \<^bsub>(MMD Is P)\<^esub>\<preceq> x) = (w \<^bsub>(MMD Is P')\<^esub>\<preceq> z)"
      unfolding MMD_def by simp
  qed
next
  show "positively_responsive (MMD Is) A Is"
  proof
    fix P P' assume profileP: "profile A Is P"
    fix x y assume xyA: "x \<in> A" "y \<in> A"
    assume xPy: "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P i)\<^esub>\<prec> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<prec> y"
       and xIy: "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P i)\<^esub>\<approx> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<preceq> y"
       and k: "\<exists>k\<in>Is. x \<^bsub>(P k)\<^esub>\<approx> y \<and> x \<^bsub>(P' k)\<^esub>\<prec> y \<or> y \<^bsub>(P k)\<^esub>\<prec> x \<and> x \<^bsub>(P' k)\<^esub>\<preceq> y"
       and xRSCFy: "x \<^bsub>(MMD Is P)\<^esub>\<preceq> y"
    from k obtain k
      where kIs: "k \<in> Is"
        and kcond: "(x \<^bsub>(P k)\<^esub>\<approx> y \<and> x \<^bsub>(P' k)\<^esub>\<prec> y) \<or> (y \<^bsub>(P k)\<^esub>\<prec> x \<and> x \<^bsub>(P' k)\<^esub>\<preceq> y)"
      by blast
    let ?xPy = "{ i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y }"
    let ?xP'y = "{ i \<in> Is. x \<^bsub>(P' i)\<^esub>\<prec> y }"
    let ?yPx = "{ i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
    let ?yP'x = "{ i \<in> Is. y \<^bsub>(P' i)\<^esub>\<prec> x }"
    from profileP xyA xPy xIy have yP'xyPx: "?yP'x \<subseteq> ?yPx"
      unfolding strict_pref_def indifferent_pref_def
      by (blast dest: rpr_complete)
    with finiteIs have yP'xyPxC: "card ?yP'x \<le> card ?yPx"
      by (blast intro: card_mono finite_subset)
    from finiteIs xPy have xPyxP'yC: "card ?xPy \<le> card ?xP'y"
      by (blast intro: card_mono finite_subset)
    show "x \<^bsub>(MMD Is P')\<^esub>\<prec> y"
    proof
      from xRSCFy xPyxP'yC yP'xyPxC show "x \<^bsub>(MMD Is P')\<^esub>\<preceq> y"
        unfolding MMD_def by auto
    next
      {
        assume xIky: "x \<^bsub>(P k)\<^esub>\<approx> y" and xP'ky: "x \<^bsub>(P' k)\<^esub>\<prec> y"
        have "card ?xPy < card ?xP'y"
        proof -
          from xIky have knP: "k \<notin> ?xPy"
            unfolding indifferent_pref_def strict_pref_def by blast
          from kIs xP'ky have kP': "k \<in> ?xP'y" by simp
          from finiteIs xPy knP kP' show ?thesis
            by (blast intro: psubset_card_mono finite_subset)
        qed
        with xRSCFy yP'xyPxC have "card ?yP'x < card ?xP'y"
          unfolding MMD_def by auto
      }
      moreover
      {
        assume yPkx: "y \<^bsub>(P k)\<^esub>\<prec> x" and xR'ky: "x \<^bsub>(P' k)\<^esub>\<preceq> y"
        have "card ?yP'x < card ?yPx"
        proof -
          from kIs yPkx have kP: "k \<in> ?yPx" by simp
          from kIs xR'ky have knP': "k \<notin> ?yP'x"
            unfolding strict_pref_def by blast
          from yP'xyPx kP knP' have "?yP'x \<subset> ?yPx" by blast
          with finiteIs show ?thesis
            by (blast intro: psubset_card_mono finite_subset)
        qed
        with xRSCFy xPyxP'yC have "card ?yP'x < card ?xP'y"
          unfolding MMD_def by auto
      }
      moreover note kcond
      ultimately show "\<not>(y \<^bsub>(MMD Is P')\<^esub>\<preceq> x)"
        unfolding MMD_def by auto
    qed
  qed
qed

subsection\<open>Everything satisfying May's conditions is the Method of Majority Decision\<close>

text\<open>Now show that MMD is the only SCF that satisfies these conditions.\<close>

text \<open>Firstly develop some theory about exchanging alternatives $x$ and
$y$ in profile $P$.\<close>

definition swapAlts :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "swapAlts a b u \<equiv> if u = a then b else if u = b then a else u"

lemma swapAlts_in_set_iff: "{a, b} \<subseteq> A \<Longrightarrow> swapAlts a b u \<in> A \<longleftrightarrow> u \<in> A"
  unfolding swapAlts_def by (simp split: if_split)

definition swapAltsP :: "('a, 'i) Profile \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a, 'i) Profile" where
  "swapAltsP P a b \<equiv> (\<lambda>i. { (u, v) . (swapAlts a b u, swapAlts a b v) \<in> P i })"

lemma swapAltsP_ab: "a \<^bsub>(P i)\<^esub>\<preceq> b \<longleftrightarrow> b \<^bsub>(swapAltsP P a b i)\<^esub>\<preceq> a" "b \<^bsub>(P i)\<^esub>\<preceq> a \<longleftrightarrow> a \<^bsub>(swapAltsP P a b i)\<^esub>\<preceq> b"
  unfolding swapAltsP_def swapAlts_def by simp_all

lemma profile_swapAltsP:
  assumes profileP: "profile A Is P"
      and abA: "{a,b} \<subseteq> A"
  shows "profile A Is (swapAltsP P a b)"
proof(rule profileI)
  from profileP show "Is \<noteq> {}" by (rule profile_non_empty)
next
  fix i assume iIs: "i \<in> Is"
  show "rpr A (swapAltsP P a b i)"
  proof(rule rprI)
    show "refl_on A (swapAltsP P a b i)"
    proof(rule refl_onI)
      from profileP iIs abA show "swapAltsP P a b i \<subseteq> A \<times> A"
        unfolding swapAltsP_def by (blast dest: swapAlts_in_set_iff)
      from profileP iIs abA show "\<And>x. x \<in> A \<Longrightarrow> x \<^bsub>(swapAltsP P a b i)\<^esub>\<preceq> x"
        unfolding swapAltsP_def swapAlts_def by auto
    qed
  next
    from profileP iIs abA show "complete A (swapAltsP P a b i)"
      unfolding swapAltsP_def
      by - (rule completeI, simp, rule rpr_complete[where A=A],
            auto iff: swapAlts_in_set_iff)
  next
    from profileP iIs show "trans (swapAltsP P a b i)"
      unfolding swapAltsP_def by (blast dest: rpr_le_trans intro: transI)
  qed
qed

lemma profile_bij_profile:
  assumes profileP: "profile A Is P"
      and bijf: "bij_betw f Is Is"
  shows "profile A Is (P \<circ> f)"
  using bij_betw_onto[OF bijf] profileP
  by - (rule, auto dest: profile_non_empty)

text\<open>The locale keeps the conditions in scope for the next few
lemmas. Note how weak the constraints on the sets of alternatives and
individuals are; clearly there needs to be at least two alternatives and two
individuals for conflict to occur, but it is pleasant that the proof
uniformly handles the degenerate cases.\<close>

locale May =
  fixes A :: "'a set"

  fixes Is :: "'i set"
  assumes finiteIs: "finite Is"

  fixes scf :: "('a, 'i) SCF"
  assumes SCF: "SCF scf A Is universal_domain"
      and anonymous: "anonymous scf A Is"
      and neutral: "neutral scf A Is"
      and positively_responsive: "positively_responsive scf A Is"
begin

text\<open>Anonymity implies that, for any pair of alternatives, the social
choice rule can only depend on the number of individuals who express any
given preference between them. Note we also need @{term "iia"}, implied by
neutrality, to restrict attention to alternatives $x$ and $y$.\<close>

lemma anonymous_card:
  assumes profileP: "profile A Is P"
      and profileP': "profile A Is P'"
      and xyA: "hasw [x,y] A"
      and xytally: "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } = card { i \<in> Is. x \<^bsub>(P' i)\<^esub>\<prec> y }"
      and yxtally: "card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x } = card { i \<in> Is. y \<^bsub>(P' i)\<^esub>\<prec> x }"
  shows "x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> x \<^bsub>(scf P')\<^esub>\<preceq> y"
proof -
  let ?xPy = "{ i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y }"
  let ?xP'y = "{ i \<in> Is. x \<^bsub>(P' i)\<^esub>\<prec> y }"
  let ?yPx = "{ i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  let ?yP'x = "{ i \<in> Is. y \<^bsub>(P' i)\<^esub>\<prec> x }"
  have disjPxy: "(?xPy \<union> ?yPx) - ?xPy = ?yPx"
    unfolding strict_pref_def by blast
  have disjP'xy: "(?xP'y \<union> ?yP'x) - ?xP'y = ?yP'x"
    unfolding strict_pref_def by blast
  from finiteIs xytally
  obtain f where bijf: "bij_betw f ?xPy ?xP'y"
    by - (drule card_eq_bij, auto)
  from finiteIs yxtally
  obtain g where bijg: "bij_betw g ?yPx ?yP'x"
    by - (drule card_eq_bij, auto)
  from bijf bijg disjPxy disjP'xy
  obtain h
    where bijh: "bij_betw h (?xPy \<union> ?yPx) (?xP'y \<union> ?yP'x)"
      and hf: "\<And>j. j \<in> ?xPy \<Longrightarrow> h j = f j"
      and hg: "\<And>j. j \<in> (?xPy \<union> ?yPx) - ?xPy \<Longrightarrow> h j = g j"
    using bij_combine[where f=f and g=g and A="?xPy" and B ="?xPy \<union> ?yPx" and C="?xP'y" and D="?xP'y \<union> ?yP'x"]
    by auto
  from bijh finiteIs
  obtain h' where bijh': "bij_betw h' Is Is"
              and hh': "\<And>j. j \<in> (?xPy \<union> ?yPx) \<Longrightarrow> h' j = h j"
              and hrest: "\<And>j. j \<in> Is - (?xPy \<union> ?yPx) \<Longrightarrow> h' j \<in> Is - (?xP'y \<union> ?yP'x)"
    by - (drule bij_complete, auto)
  from neutral_iia[OF neutral]
  have "x \<^bsub>(scf (P' \<circ> h'))\<^esub>\<preceq> y \<longleftrightarrow> x \<^bsub>(scf P)\<^esub>\<preceq> y"
  proof(rule iiaE)
    from xyA show "{x, y} \<subseteq> A" by simp
  next
    fix i assume iIs: "i \<in> Is"
    fix a b assume ab: "a \<in> {x, y}" "b \<in> {x, y}"
    from profileP iIs have completePi: "complete A (P i)" by (auto dest: rprD)
    from completePi xyA
    show "(a \<^bsub>(P i)\<^esub>\<preceq> b) \<longleftrightarrow> (a \<^bsub>((P' \<circ> h') i)\<^esub>\<preceq> b)"
    proof(cases rule: complete_exh)
      case xPy with profileP profileP' xyA iIs ab hh' hf bijf show ?thesis
        unfolding strict_pref_def bij_betw_def by (simp, blast)
    next
      case yPx with profileP profileP' xyA iIs ab hh' hg bijg show ?thesis
        unfolding strict_pref_def bij_betw_def by (simp, blast)
    next
      case xIy with profileP profileP' xyA iIs ab hrest[where j=i] show ?thesis
        unfolding indifferent_pref_def strict_pref_def bij_betw_def
        by (simp, blast dest: rpr_complete)
    qed
  qed (simp_all add: profileP profile_bij_profile[OF profileP' bijh'])
  moreover
  from anonymousD[OF anonymous profileP' bijh'] xyA
  have "x \<^bsub>(scf P')\<^esub>\<preceq> y \<longleftrightarrow> x \<^bsub>(scf (P' \<circ> h'))\<^esub>\<preceq> y" by simp
  ultimately show ?thesis by simp
qed

text \<open>Using the previous result and neutrality, it must be the case that
if the tallies are tied for alternatives $x$ and $y$ then the social choice
function is indifferent between those two alternatives.\<close>

lemma anonymous_neutral_indifference:
  assumes profileP: "profile A Is P"
      and xyA: "hasw [x,y] A"
      and tallyP: "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  shows "x \<^bsub>(scf P)\<^esub>\<approx> y"
proof -
    \<comment> \<open>Neutrality insists the results for @{term "P"} are symmetrical to those for @{term "swapAltsP P"}.\<close>
  from xyA
  have symPP': "(x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> y \<^bsub>(scf (swapAltsP P x y))\<^esub>\<preceq> x)
              \<and> (y \<^bsub>(scf P)\<^esub>\<preceq> x \<longleftrightarrow> x \<^bsub>(scf (swapAltsP P x y))\<^esub>\<preceq> y)"
    by - (rule neutralD[OF neutral profileP profile_swapAltsP[OF profileP]],
          simp_all, (rule swapAltsP_ab)+)
      \<comment> \<open>Anonymity and neutrality insist the results for @{term "P"} are identical to those for @{term "swapAltsP P"}.\<close>
  from xyA tallyP have "card {i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y} = card { i \<in> Is. x \<^bsub>(swapAltsP P x y i)\<^esub>\<prec> y }"
                   and "card {i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x} = card { i \<in> Is. y \<^bsub>(swapAltsP P x y i)\<^esub>\<prec> x }"
    unfolding swapAltsP_def swapAlts_def strict_pref_def by simp_all
  with profileP xyA have idPP': "x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> x \<^bsub>(scf (swapAltsP P x y))\<^esub>\<preceq> y"
                            and "y \<^bsub>(scf P)\<^esub>\<preceq> x \<longleftrightarrow> y \<^bsub>(scf (swapAltsP P x y))\<^esub>\<preceq> x"
    by - (rule anonymous_card[OF profileP profile_swapAltsP], clarsimp+)+
  from xyA SCF_completeD[OF SCF] profileP symPP' idPP' show "x \<^bsub>(scf P)\<^esub>\<approx> y" by (simp, blast)
qed

text\<open>Finally, if the tallies are not equal then the social choice function
must lean towards the one with the higher count due to positive
responsiveness.\<close>

lemma positively_responsive_prefer_witness:
  assumes profileP: "profile A Is P"
      and xyA: "hasw [x,y] A"
      and tallyP: "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } > card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  obtains P' k
    where "profile A Is P'"
      and "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P' i)\<^esub>\<prec> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y"
      and "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P' i)\<^esub>\<approx> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<preceq> y"
      and "k \<in> Is \<and> x \<^bsub>(P' k)\<^esub>\<approx> y \<and> x \<^bsub>(P k)\<^esub>\<prec> y"
      and "card { i \<in> Is. x \<^bsub>(P' i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(P' i)\<^esub>\<prec> x }"
proof -
  from tallyP obtain C
    where tallyP': "card ({ i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } - C) = card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
      and C: "C \<noteq> {}" "C \<subseteq> Is"
      and CxPy: "C \<subseteq> { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y }"
    by - (drule card_greater[OF finiteIs], auto)
      \<comment> \<open>Add $(b, a)$ and close under transitivity.\<close>
  let ?P' = "\<lambda>i. if i \<in> C
                   then P i \<union> { (y, x) }
                            \<union> { (y, u) |u. x \<^bsub>(P i)\<^esub>\<preceq> u }
                            \<union> { (u, x) |u. u \<^bsub>(P i)\<^esub>\<preceq> y }
                            \<union> { (v, u) |u v. x \<^bsub>(P i)\<^esub>\<preceq> u \<and> v \<^bsub>(P i)\<^esub>\<preceq> y }
                   else P i"
  have "profile A Is ?P'"
  proof
    fix i assume iIs: "i \<in> Is"
    show "rpr A (?P' i)"
    proof
      from profileP iIs show "complete A (?P' i)"
        unfolding complete_def by (simp, blast dest: rpr_complete)
      from profileP iIs xyA show "refl_on A (?P' i)"
        by - (rule refl_onI, auto)
      show "trans (?P' i)"
      proof(cases "i \<in> C")
        case False with profileP iIs show ?thesis
          by (simp, blast dest: rpr_le_trans intro: transI)
      next
        case True with profileP iIs C CxPy xyA show ?thesis
          unfolding strict_pref_def
          by - (rule transI, simp, blast dest: rpr_le_trans rpr_complete)
      qed
    qed
  next
    from C show "Is \<noteq> {}" by blast
  qed
  moreover
  have "\<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(?P' i)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y"
    unfolding strict_pref_def by (simp split: if_split_asm)
  moreover
  from profileP C xyA
  have "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(?P' i)\<^esub>\<approx> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<preceq> y"
    unfolding indifferent_pref_def by (simp split: if_split_asm)
  moreover
  from C CxPy obtain k where kC: "k \<in> C" and xPky: "x \<^bsub>(P k)\<^esub>\<prec> y" by blast
  hence "x \<^bsub>(?P' k)\<^esub>\<approx> y" by auto
  with C kC xPky have "k \<in> Is \<and> x \<^bsub>(?P' k)\<^esub>\<approx> y \<and> x \<^bsub>(P k)\<^esub>\<prec> y" by blast
  moreover
  have "card { i \<in> Is. x \<^bsub>(?P' i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(?P' i)\<^esub>\<prec> x }"
  proof -
    have "{ i \<in> Is. x \<^bsub>(?P' i)\<^esub>\<prec> y } = { i \<in> Is. x \<^bsub>(?P' i)\<^esub>\<prec> y } - C"
    proof -
      from C have "\<And>i. \<lbrakk> i \<in> Is; x \<^bsub>(?P' i)\<^esub>\<prec> y \<rbrakk> \<Longrightarrow> i \<in> Is - C"
        unfolding indifferent_pref_def strict_pref_def by auto
      thus ?thesis by blast
    qed
    also have "\<dots> = { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } - C" by auto
    finally have "card { i \<in> Is. x \<^bsub>(?P' i)\<^esub>\<prec> y } = card ({ i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } - C)"
      by simp
    with tallyP' have "card { i \<in> Is. x \<^bsub>(?P' i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
      by simp
    also have "\<dots> = card { i \<in> Is. y \<^bsub>(?P' i)\<^esub>\<prec> x }" (is "card ?lhs = card ?rhs")
    proof -
      from profileP xyA have "\<And>i. \<lbrakk> i \<in> Is; y \<^bsub>(?P' i)\<^esub>\<prec> x \<rbrakk> \<Longrightarrow> y \<^bsub>(P i)\<^esub>\<prec> x"
        unfolding strict_pref_def by (simp split: if_split_asm, blast dest: rpr_complete)
      hence "?rhs \<subseteq> ?lhs" by blast
      moreover
      from profileP xyA have "\<And>i. \<lbrakk> i \<in> Is; y \<^bsub>(P i)\<^esub>\<prec> x \<rbrakk> \<Longrightarrow> y \<^bsub>(?P' i)\<^esub>\<prec> x"
        unfolding strict_pref_def by simp
      hence "?lhs \<subseteq> ?rhs" by blast
      ultimately show ?thesis by simp
    qed
    finally show ?thesis .
  qed
  ultimately show thesis ..
qed

lemma positively_responsive_prefer:
  assumes profileP: "profile A Is P"
      and xyA: "hasw [x,y] A"
      and tallyP: "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } > card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  shows "x \<^bsub>(scf P)\<^esub>\<prec> y"
proof -
  from assms obtain P' k
    where profileP': "profile A Is P'"
      and F: "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P' i)\<^esub>\<prec> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> y"
      and G: "\<And>i. \<lbrakk>i \<in> Is; x \<^bsub>(P' i)\<^esub>\<approx> y\<rbrakk> \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<preceq> y"
      and pivot: "k \<in> Is \<and> x \<^bsub>(P' k)\<^esub>\<approx> y \<and> x \<^bsub>(P k)\<^esub>\<prec> y"
      and cardP': "card { i \<in> Is. x \<^bsub>(P' i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(P' i)\<^esub>\<prec> x }"
    by - (drule positively_responsive_prefer_witness, auto)
  from profileP' xyA cardP' have "x \<^bsub>(scf P')\<^esub>\<approx> y"
    by - (rule anonymous_neutral_indifference, auto)
  with xyA F G pivot show ?thesis
    by - (rule positively_responsiveD[OF positively_responsive profileP' profileP], auto)
qed

lemma MMD_r2l:
  assumes profileP: "profile A Is P"
      and xyA: "hasw [x,y] A"
  shows "x \<^bsub>(scf P)\<^esub>\<preceq> y \<longleftrightarrow> x \<^bsub>(MMD Is P)\<^esub>\<preceq> y"
proof(cases rule: linorder_cases)
  assume "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } = card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  with profileP xyA show ?thesis
    using anonymous_neutral_indifference
    unfolding indifferent_pref_def MMD_def by simp
next
  assume "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } > card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  with profileP xyA show ?thesis
    using positively_responsive_prefer
    unfolding strict_pref_def MMD_def by simp
next
  assume "card { i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y } < card { i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x }"
  with profileP xyA show ?thesis
    using positively_responsive_prefer
    unfolding strict_pref_def MMD_def by clarsimp
qed

end

text\<open>May's original paper \cite{May:1952} goes on to show that the
conditions are independent by exhibiting choice rules that differ from
@{term "MMD"} and satisfy the conditions remaining after any particular one
is removed. I leave this to future work.

May also wrote a later article \cite{May:1953} where he shows that the
conditions are completely independent, i.e. for every partition of the
conditions into two sets, there is a voting rule that satisfies one and not
the other.

There are many later papers that characterise MMD with different sets of
conditions.

\<close>

subsection\<open>The Plurality Rule\<close>

text\<open>Goodin and List \cite{GoodinList:2006} show that May's original
result can be generalised to characterise plurality voting. The following
shows that this result is a short step from Sen's much earlier
generalisation.

\emph{Plurality voting} is a choice function that returns the alternative
that receives the most votes, or the set of such alternatives in the case of
a tie. Profiles are restricted to those where each individual casts a vote
in favour of a single alternative.\<close>

type_synonym ('a, 'i) SVProfile = "'i \<Rightarrow> 'a"

definition svprofile :: "'a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) SVProfile \<Rightarrow> bool" where
  "svprofile A Is F \<equiv> Is \<noteq> {} \<and> F ` Is \<subseteq> A"

definition plurality_rule :: "'a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) SVProfile \<Rightarrow> 'a set" where
  "plurality_rule A Is F
     \<equiv> { x \<in> A . \<forall>y \<in> A. card { i \<in> Is . F i = x } \<ge> card { i \<in> Is . F i = y } }"

text\<open>By translating single-vote profiles into RPRs in the obvious way, the
choice function arising from @{term "MMD"} coincides with traditional
plurality voting.\<close>

definition MMD_plurality_rule :: "'a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> 'a set" where
  "MMD_plurality_rule A Is P \<equiv> choiceSet A (MMD Is P)"

definition single_vote_to_RPR :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a RPR" where
  "single_vote_to_RPR A a \<equiv> { (a, x) |x. x \<in> A } \<union> (A - {a}) \<times> (A - {a})"

lemma single_vote_to_RPR_iff:
  "\<lbrakk> a \<in> A; x \<in> A; a \<noteq> x \<rbrakk> \<Longrightarrow> (a \<^bsub>(single_vote_to_RPR A b)\<^esub>\<prec> x) \<longleftrightarrow> (b = a)"
  unfolding single_vote_to_RPR_def strict_pref_def by auto

lemma plurality_rule_equiv:
  "plurality_rule A Is F = MMD_plurality_rule A Is (single_vote_to_RPR A \<circ> F)"
proof -
  {
    fix x y
    have "\<lbrakk> x \<in> A; y \<in> A \<rbrakk> \<Longrightarrow>
      (card {i \<in> Is. F i = y} \<le> card {i \<in> Is. F i = x}) =
      (card {i \<in> Is. y \<^bsub>(single_vote_to_RPR A (F i))\<^esub>\<prec> x}
        \<le> card {i \<in> Is. x \<^bsub>(single_vote_to_RPR A (F i))\<^esub>\<prec> y})"
      by (cases "x=y", auto iff: single_vote_to_RPR_iff)
  }
  thus ?thesis
    unfolding plurality_rule_def MMD_plurality_rule_def choiceSet_def MMD_def
    by auto
qed

text\<open>Thus it is clear that Sen's generalisation of May's result applies to
this case as well.

Their paper goes on to show how strengthening the anonymity condition gives
rise to a characterisation of approval voting that strictly generalises
May's original theorem. As this requires some rearrangement of the proof I
leave it to future work.\<close>

(*<*)
end
(*>*)
