(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Late_Step_Semantics
  imports Late_Tau_Chain
begin

definition inputTransition :: "pi \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>l_ in _\<rightarrow>_<_> \<prec> _" [80, 80, 80, 80, 80] 80)
where "P \<Longrightarrow>\<^sub>lu in P'' \<rightarrow>a<x> \<prec> P' \<equiv> \<exists>P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<x> \<prec> P'' \<and> P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"

definition transition :: "(pi \<times> Late_Semantics.residual) set" where
  "transition \<equiv> {x. \<exists>P P' \<alpha> P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P' \<and> P' \<longmapsto>\<alpha> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P''' \<and> x = (P, \<alpha> \<prec> P''')}  \<union>
                {x. \<exists>P P' a y P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P' \<and> (P' \<longmapsto>(a<\<nu>y> \<prec> P'')) \<and> P'' \<Longrightarrow>\<^sub>\<tau> P''' \<and> x = (P, (a<\<nu>y> \<prec> P'''))}"

abbreviation weakTransition_judge :: "pi \<Rightarrow> Late_Semantics.residual \<Rightarrow> bool" ("_ \<Longrightarrow>\<^sub>l _" [80, 80] 80)
  where "P \<Longrightarrow>\<^sub>l Rs \<equiv> (P, Rs) \<in> transition"

lemma weakNonInput[dest]:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>la<x> \<prec> P'"
 
  shows False
using assms
by(auto simp add: transition_def residual.inject)

lemma transitionI:
  fixes P    :: pi
  and   P''' :: pi
  and   \<alpha>    :: freeRes
  and   P''  :: pi
  and   P'   :: pi
  and   a    :: name
  and   x    :: name
  and   u    :: name

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'''; P''' \<longmapsto>\<alpha> \<prec> P''; P'' \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'''; P''' \<longmapsto>a<\<nu>x> \<prec> P''; P'' \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'''; P''' \<longmapsto>a<x> \<prec> P''; P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>\<tau> P'''" and "P''' \<longmapsto> \<alpha> \<prec> P''" and "P'' \<Longrightarrow>\<^sub>\<tau> P'"
  thus "P \<Longrightarrow>\<^sub>l \<alpha> \<prec> P'"
    by(force simp add: transition_def)
next
  assume "P \<Longrightarrow>\<^sub>\<tau> P'''" and "P''' \<longmapsto>a<\<nu>x> \<prec> P''" and "P'' \<Longrightarrow>\<^sub>\<tau> P'"
  thus "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
    by(force simp add: transition_def)
next
  assume "P \<Longrightarrow>\<^sub>\<tau> P'''" and "P''' \<longmapsto>a<x> \<prec> P''" and "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
  thus "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'" 
    by(force simp add: inputTransition_def)
qed

lemma transitionE:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P'  :: pi
  and   P'' :: pi
  and   a   :: name
  and   u   :: name
  and   x   :: name

  shows "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P' \<Longrightarrow> \<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P'' \<and> P'' \<longmapsto>\<alpha> \<prec> P''' \<and> P''' \<Longrightarrow>\<^sub>\<tau> P'" (is "_ \<Longrightarrow> ?thesis1")
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'; x \<sharp> P\<rbrakk> \<Longrightarrow> \<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<\<nu>x> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P'"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'\<rbrakk> \<Longrightarrow> \<exists>P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<x> \<prec> P'' \<and> P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
  thus ?thesis1 by(auto simp add: transition_def residual.inject)
next
  assume "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'" and "x \<sharp> P"
  thus "\<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<\<nu>x> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P'"
  using [[hypsubst_thin = true]]
    apply(auto simp add: transition_def residualInject name_abs_eq)
    apply(rule_tac x="[(x, y)] \<bullet> P''" in exI)
    apply(rule_tac x=P' in exI)
    apply(clarsimp)
    apply(auto)
    apply(subgoal_tac "x \<sharp> P''")
    apply(simp add: alphaBoundResidual name_swap)
    using freshChain
    apply(force dest: freshBoundDerivative)
    using eqvtChainI
    by simp
next
  assume PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  thus "\<exists>P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto> a<x> \<prec> P'' \<and> P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(auto simp add: inputTransition_def)
qed

lemma alphaInput:
  fixes P   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi
  and   y   :: name

  assumes PTrans:  "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  and     yFreshP: "y \<sharp> P"

  shows "P \<Longrightarrow>\<^sub>lu in ([(x, y)] \<bullet> P'')\<rightarrow>a<y> \<prec> P'"
proof(cases "x=y")
  assume "x=y"
  with PTrans show ?thesis by simp
next
  assume xineqy: "x\<noteq>y"
  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain yFreshP have "y \<sharp> P'''" by(rule freshChain)
  with P'''Trans xineqy have yFreshP'': "y \<sharp> P''" by(blast dest: freshBoundDerivative)

  with P'''Trans have "P''' \<longmapsto>a<y> \<prec> [(x, y)] \<bullet> P''" by(simp add: alphaBoundResidual)
  moreover from P''Chain yFreshP'' have "([(x, y)] \<bullet> P'')[y::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(simp add: renaming name_swap)
  ultimately show ?thesis using PChain by(blast intro: transitionI)
qed

lemma tauActionChain:
  fixes P  :: pi
  and   P' :: pi
  
  shows "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>\<tau> P'"
  and   "P \<noteq> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
  then obtain P'' P''' where "P \<Longrightarrow>\<^sub>\<tau> P''"
                         and "P'' \<longmapsto>\<tau> \<prec> P'''"
                         and "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  thus "P \<Longrightarrow>\<^sub>\<tau> P'" by auto
next
  assume "P \<Longrightarrow>\<^sub>\<tau> P'" and "P \<noteq> P'" 
  thus "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
  proof(induct rule: tauChainInduct)
    case id
    thus ?case by simp
  next
    case(ih P'' P''')
    have "P \<Longrightarrow>\<^sub>\<tau> P''" and "P'' \<longmapsto> \<tau> \<prec> P'''" by fact+
    moreover have "P''' \<Longrightarrow>\<^sub>\<tau> P'''" by simp
    ultimately show ?case by(rule transitionI)
  qed
qed

lemma singleActionChain:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   \<alpha>  :: freeRes
  and   u  :: name
 
  shows "P \<longmapsto>a<\<nu>x> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  and   "\<lbrakk>P \<longmapsto>a<x> \<prec> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<^sub>lu in P'\<rightarrow>a<x> \<prec> P'[x::=u]"
  and   "P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
proof -  
  assume "P \<longmapsto>a<\<nu>x> \<prec> P'"
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  moreover have "P' \<Longrightarrow>\<^sub>\<tau> P'" by simp
  ultimately show "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'" by(blast intro: transitionI)
next
  assume "P \<longmapsto>a<x> \<prec> P'"
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  moreover have "P'[x::=u] \<Longrightarrow>\<^sub>\<tau> P'[x::=u]" by simp
  ultimately show "P \<Longrightarrow>\<^sub>lu in P'\<rightarrow>a<x> \<prec> P'[x::=u]" by(blast intro: transitionI)
next
  assume "P \<longmapsto>\<alpha> \<prec> P'"
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  moreover have "P' \<Longrightarrow>\<^sub>\<tau> P'" by simp
  ultimately show "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"  by(blast intro: transitionI)
qed

lemma Tau:
  fixes P :: pi

  shows "\<tau>.(P) \<Longrightarrow>\<^sub>l \<tau> \<prec>  P"
proof -
  have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> \<tau>.(P)" by simp
  moreover have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule transitions.Tau)
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  ultimately show ?thesis by(rule transitionI)
qed

lemma Input:
  fixes a :: name
  and   x :: name
  and   u :: name
  and   P :: pi

  shows "a<x>.P \<Longrightarrow>\<^sub>lu in P\<rightarrow>a<x> \<prec> P[x::=u]"
proof -
  have "a<x>.P \<Longrightarrow>\<^sub>\<tau> a<x>.P" by simp
  moreover have "a<x>.P \<longmapsto> a<x> \<prec> P" by(rule Input)
  moreover have "P[x::=u] \<Longrightarrow>\<^sub>\<tau> P[x::=u]" by simp
  ultimately show ?thesis by(rule transitionI)
qed

lemma Output:
  fixes a :: name
  and   b :: name
  and   P :: pi

  shows "a{b}.P \<Longrightarrow>\<^sub>la[b] \<prec> P"
proof -
  have "a{b}.P \<Longrightarrow>\<^sub>\<tau> a{b}.P" by simp
  moreover have "a{b}.P \<longmapsto>a[b] \<prec> P" by(rule transitions.Output)
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  ultimately show ?thesis by(rule transitionI)
qed

lemma Match:
  fixes P  :: pi
  and   Rs :: residual
  and   a  :: name
  and   u  :: name
  and   b  :: name
  and   x  :: name
  and   P' :: pi

  shows "P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>\<^sub>l Rs"
  and   "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P' \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
proof -
  assume PTrans: "P \<Longrightarrow>\<^sub>l Rs"
  thus "[a\<frown>a]P \<Longrightarrow>\<^sub>l Rs"
  proof(nominal_induct avoiding: P rule: residual.strong_inducts)
    case(BoundR b x P')
    have PTrans: "P \<Longrightarrow>\<^sub>l b\<guillemotleft>x\<guillemotright> \<prec> P'" and xFreshP: "x \<sharp> P" by fact+
    from PTrans obtain b' where beq: "b = BoundOutputS b'" by(cases b) auto
    with PTrans xFreshP obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>b'<\<nu>x> \<prec> P'''"
                                          and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> [a\<frown>a]P" by simp
      moreover from P''Trans have "[a\<frown>a]P'' \<longmapsto> b'<\<nu>x> \<prec> P'''" by(rule Match)
      ultimately show ?thesis using beq P'''Trans by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> P''" by(rule matchChain)
      thus ?thesis using beq P''Trans P'''Trans by(blast intro: transitionI)
    qed
  next
    case(FreeR \<alpha> P')
    have "P \<Longrightarrow>\<^sub>l \<alpha> \<prec> P'" by fact

    then obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                           and P''Trans: "P'' \<longmapsto> \<alpha> \<prec> P'''"
                           and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> [a\<frown>a]P" by simp
      moreover from P''Trans have "[a\<frown>a]P'' \<longmapsto> \<alpha> \<prec> P'''" by(rule transitions.Match)
      ultimately show ?thesis using P'''Trans by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> P''" by(rule matchChain)
      thus ?thesis using P''Trans P'''Trans by(rule transitionI)
    qed
  qed
next
  assume "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
  then obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                     and P'''Trans: "P''' \<longmapsto>b<x> \<prec> P''"
                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  show "[a\<frown>a]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
  proof(cases "P=P'''")
    assume "P=P'''"
    moreover have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> [a\<frown>a]P" by simp
    moreover from P'''Trans have "[a\<frown>a]P''' \<longmapsto>b<x> \<prec> P''" by(rule Late_Semantics.Match)
    ultimately show ?thesis using P''Chain by(blast intro: transitionI)
  next
    assume "P \<noteq> P'''"
    with PChain have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule matchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
qed

lemma Mismatch:
  fixes P  :: pi
  and   Rs :: residual
  and   a  :: name
  and   c  :: name
  and   u  :: name
  and   b  :: name
  and   x  :: name
  and   P' :: pi

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>l Rs; a \<noteq> c\<rbrakk> \<Longrightarrow> [a\<noteq>c]P \<Longrightarrow>\<^sub>l Rs"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'; a \<noteq> c\<rbrakk> \<Longrightarrow> [a\<noteq>c]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
proof -
  assume PTrans: "P \<Longrightarrow>\<^sub>l Rs"
     and aineqc: "a \<noteq> c"
  thus "[a\<noteq>c]P \<Longrightarrow>\<^sub>l Rs"
  proof(nominal_induct avoiding: P rule: residual.strong_inducts)
    case(BoundR b x P')
    have PTrans: "P \<Longrightarrow>\<^sub>l b\<guillemotleft>x\<guillemotright> \<prec> P'" and xFreshP: "x \<sharp> P" by fact+
    from PTrans obtain b' where beq: "b = BoundOutputS b'" by(cases b, auto)
    with PTrans xFreshP obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>b'<\<nu>x> \<prec> P'''"
                                          and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> [a\<noteq>c]P" by simp
      moreover from P''Trans aineqc have "[a\<noteq>c]P'' \<longmapsto>b'<\<nu>x> \<prec> P'''" by(rule transitions.Mismatch)
      ultimately show ?thesis using beq P'''Trans by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans aineqc have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> P''" by(rule mismatchChain)
      thus ?thesis using beq P''Trans P'''Trans by(blast intro: transitionI)
    qed
  next
    case(FreeR \<alpha> P')
    have "P \<Longrightarrow>\<^sub>l \<alpha> \<prec> P'" by fact

    then obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                           and P''Trans: "P'' \<longmapsto> \<alpha> \<prec> P'''"
                           and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> [a\<noteq>c]P" by simp
      moreover from P''Trans \<open>a \<noteq> c\<close> have "[a\<noteq>c]P'' \<longmapsto> \<alpha> \<prec> P'''" by(rule transitions.Mismatch)
      ultimately show ?thesis using P'''Trans by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans aineqc have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> P''" by(rule mismatchChain)
      thus ?thesis using P''Trans P'''Trans by(rule transitionI)
    qed
  qed
next
  assume aineqc: "a \<noteq> c"
  assume "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
  then obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                     and P'''Trans: "P''' \<longmapsto>b<x> \<prec> P''"
                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  show "[a\<noteq>c]P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>b<x> \<prec> P'"
  proof(cases "P=P'''")
    assume "P=P'''"
    moreover have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> [a\<noteq>c]P" by simp
    moreover from P'''Trans aineqc have "[a\<noteq>c]P''' \<longmapsto>b<x> \<prec> P''" by(rule Late_Semantics.Mismatch)
    ultimately show ?thesis using P''Chain by(blast intro: transitionI)
  next
    assume "P \<noteq> P'''"
    with PChain aineqc have "[a\<noteq>c]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule mismatchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
qed

lemma Open:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes Trans:  "P \<Longrightarrow>\<^sub>la[b] \<prec> P'"
  and     aInEqb: "a \<noteq> b"

  shows "<\<nu>b>P \<Longrightarrow>\<^sub>la<\<nu>b> \<prec> P'"
proof -
  from Trans obtain P'' P''' where A: "P \<Longrightarrow>\<^sub>\<tau> P''"
                               and B: "P'' \<longmapsto>a[b] \<prec> P'''"
                               and C: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  from A have "<\<nu>b>P \<Longrightarrow>\<^sub>\<tau> <\<nu>b>P''" by(rule ResChain)
  moreover from B aInEqb have "<\<nu>b>P'' \<longmapsto>a<\<nu>b> \<prec> P'''" by(rule Open)
  ultimately show ?thesis using C by(force simp add: transition_def)
qed

lemma Sum1:
  fixes P   :: pi
  and   Rs  :: residual
  and   Q   :: pi
  and   u   :: name
  and   P'' :: pi
  and   a   :: name
  and   x   :: name
  and   P'  :: pi

  shows "P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<^sub>l Rs"
  and   "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>l Rs"
  thus "P \<oplus> Q \<Longrightarrow>\<^sub>l Rs"
  proof(nominal_induct avoiding: P rule: residual.strong_inducts)
    case(BoundR a x P' P)
    have PTrans: "P \<Longrightarrow>\<^sub>la\<guillemotleft>x\<guillemotright> \<prec> P'"
     and xFreshP: "x \<sharp> P" by fact+
    from PTrans obtain a' where aeq: "a = BoundOutputS a'" by(cases a, auto)
    with PTrans xFreshP obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>a'<\<nu>x> \<prec> P'''"
                                          and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
      moreover from P''Trans have "P'' \<oplus> Q \<longmapsto>a'<\<nu>x> \<prec> P'''" by(rule transitions.Sum1)
      ultimately show ?thesis using P'''Trans aeq by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P''" by(rule sum1Chain)
      thus ?thesis using P''Trans P'''Trans aeq by(blast intro: transitionI)
    qed
  next
    case(FreeR \<alpha> P')
    have "P \<Longrightarrow>\<^sub>l \<alpha> \<prec> P'" by fact

    then obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                           and P''Trans: "P'' \<longmapsto> \<alpha> \<prec> P'''"
                           and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "P = P''")
      assume "P = P''"
      moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
      moreover from P''Trans have "P'' \<oplus> Q \<longmapsto> \<alpha> \<prec> P'''" by(rule transitions.Sum1)
      ultimately show ?thesis using P'''Trans by(blast intro: transitionI)
    next
      assume "P \<noteq> P''"
      with PTrans have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P''" by(rule sum1Chain)
      thus ?thesis using P''Trans P'''Trans by(rule transitionI)
    qed
  qed
next
  assume "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  then obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                     and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  proof(cases "P = P'''")
    assume "P = P'''"
    moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from P'''Trans have "P''' \<oplus> Q \<longmapsto>a<x> \<prec> P''" by(rule transitions.Sum1)
    ultimately show ?thesis using P''Chain by(blast intro: transitionI)
  next
    assume "P \<noteq> P'''"
    with PChain have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P'''" by(rule sum1Chain)
    thus ?thesis using P'''Trans P''Chain by(blast intro: transitionI)
  qed
qed

lemma Sum2:
  fixes Q  :: pi
  and   Rs :: residual
  and   P  :: pi
  and   u  :: name
  and   Q'' :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi

  shows "Q \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<^sub>l Rs"
  and   "Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q'"
proof -
  assume "Q \<Longrightarrow>\<^sub>l Rs"
  thus "P \<oplus> Q \<Longrightarrow>\<^sub>l Rs"
  proof(nominal_induct avoiding: Q rule: residual.strong_inducts)
    case(BoundR a x Q' Q)
    have QTrans: "Q \<Longrightarrow>\<^sub>la\<guillemotleft>x\<guillemotright> \<prec> Q'"
     and xFreshQ: "x \<sharp> Q" by fact+
    from QTrans obtain a' where aeq: "a = BoundOutputS a'" by(cases a, auto)
    with QTrans xFreshQ obtain Q'' Q''' where QTrans: "Q \<Longrightarrow>\<^sub>\<tau> Q''"
                                          and Q''Trans: "Q'' \<longmapsto>a'<\<nu>x> \<prec> Q'''"
                                          and Q'''Trans: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "Q = Q''")
      assume "Q = Q''"
      moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
      moreover from Q''Trans have "P \<oplus> Q'' \<longmapsto>a'<\<nu>x> \<prec> Q'''" by(rule transitions.Sum2)
      ultimately show ?thesis using Q'''Trans aeq by(blast intro: transitionI)
    next
      assume "Q \<noteq> Q''"
      with QTrans have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q''" by(rule sum2Chain)
      thus ?thesis using Q''Trans Q'''Trans aeq by(blast intro: transitionI)
    qed
  next
    case(FreeR \<alpha> Q')
    have "Q \<Longrightarrow>\<^sub>l \<alpha> \<prec> Q'" by fact

    then obtain Q'' Q''' where QTrans: "Q \<Longrightarrow>\<^sub>\<tau> Q''"
                           and Q''Trans: "Q'' \<longmapsto> \<alpha> \<prec> Q'''"
                           and Q'''Trans: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
      by(blast dest: transitionE)
    show ?case
    proof(cases "Q = Q''")
      assume "Q = Q''"
      moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
      moreover from Q''Trans have "P \<oplus> Q'' \<longmapsto> \<alpha> \<prec> Q'''" by(rule transitions.Sum2)
      ultimately show ?thesis using Q'''Trans by(blast intro: transitionI)
    next
      assume "Q \<noteq> Q''"
      with QTrans have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q''" by(rule sum2Chain)
      thus ?thesis using Q''Trans Q'''Trans by(rule transitionI)
    qed
  qed
next
  assume "Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q'"
  then obtain Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                     and Q'''Trans: "Q''' \<longmapsto>a<x> \<prec> Q''"
                     and Q''Chain: "Q''[x::=u] \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q'"
  proof(cases "Q = Q'''")
    assume "Q = Q'''"
    moreover have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from Q'''Trans have "P \<oplus> Q''' \<longmapsto>a<x> \<prec> Q''" by(rule transitions.Sum2)
    ultimately show ?thesis using Q''Chain by(blast intro: transitionI)
  next
    assume "Q \<noteq> Q'''"
    with QChain have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q'''" by(rule sum2Chain)
    thus ?thesis using Q'''Trans Q''Chain by(blast intro: transitionI)
  qed
qed

lemma Par1B:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   u  :: name
  and   P'' :: pi

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'; x \<sharp> Q\<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P' \<parallel> Q)"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'; x \<sharp> Q\<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>lu in (P'' \<parallel> Q)\<rightarrow>a<x> \<prec> P' \<parallel> Q"
proof -
  assume PTrans: "P \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> P'"
  assume xFreshQ: "x \<sharp> Q"

  have Goal: "\<And>P a x P' Q. \<lbrakk>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'; x \<sharp> P; x \<sharp> Q\<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P' \<parallel> Q)"
  proof -
    fix P a x P' Q
    assume PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
    assume xFreshP: "x \<sharp> P"
    assume xFreshQ: "x \<sharp> (Q::pi)"

    from PTrans xFreshP obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>a<\<nu>x> \<prec> P'''"
                                          and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)
    from PTrans have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> Q" by(rule Par1Chain)
    moreover from P''Trans xFreshQ have "P'' \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> (P''' \<parallel> Q)" by(rule Par1B)
    moreover from P'''Trans have "P''' \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q" by(rule Par1Chain)
    ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P' \<parallel> Q)" by(rule transitionI)
  qed
  
  have "\<exists>c::name. c \<sharp> (P, P', Q)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshP: "c \<sharp> P" and cFreshP': "c \<sharp> P'" and cFreshQ: "c \<sharp> Q"
    by(force simp add: fresh_prod)

  from cFreshP' have "a<\<nu>x> \<prec> P' = a<\<nu>c> \<prec> ([(x, c)] \<bullet> P')" by(rule alphaBoundResidual)
  moreover have "a<\<nu>x> \<prec> (P' \<parallel> Q) = a<\<nu>c> \<prec> (([(x, c)] \<bullet> P') \<parallel> Q)"
  proof -
    from cFreshP' cFreshQ have "c \<sharp> P' \<parallel> Q" by simp
    hence "a<\<nu>x> \<prec> (P' \<parallel> Q) = a<\<nu>c> \<prec> ([(x, c)] \<bullet> (P' \<parallel> Q))" by(rule alphaBoundResidual)
    with cFreshQ xFreshQ show ?thesis by(simp add: name_fresh_fresh)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> P' \<parallel> Q" using PTrans cFreshP cFreshQ by(force intro: Goal)
next
  assume PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
     and xFreshQ: "x \<sharp> Q"
  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from PChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q" by(rule Par1Chain)
  moreover from P'''Trans xFreshQ have "P''' \<parallel> Q \<longmapsto>a<x> \<prec> (P'' \<parallel> Q)" by(rule Par1B)
  moreover have "(P'' \<parallel> Q)[x::=u] \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q"
  proof - 
    from P''Chain have "P''[x::=u] \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q" by(rule Par1Chain)
    with xFreshQ show ?thesis by(simp add: forget)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>lu in (P'' \<parallel> Q)\<rightarrow>a<x> \<prec> (P' \<parallel> Q)" by(rule transitionI)
qed

lemma Par1F:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<alpha> \<prec> (P' \<parallel> Q)"
proof -
  from PTrans obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                and P''Trans: "P'' \<longmapsto>\<alpha> \<prec> P'''"
                                and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from PTrans have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P'' \<parallel> Q" by(rule Par1Chain)
  moreover from P''Trans have "P'' \<parallel> Q \<longmapsto>\<alpha> \<prec> (P''' \<parallel> Q)" by(rule transitions.Par1F)
  moreover from P'''Trans have "P''' \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q" by(rule Par1Chain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Par2B:
  fixes Q  :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi
  and   P  :: pi
  and   u  :: name
  and   Q'' :: pi

  shows "Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P \<parallel> Q')"
  and   "Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>lu in (P \<parallel> Q'')\<rightarrow>a<x> \<prec> P \<parallel> Q'"
proof -
  assume QTrans: "Q \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> Q'"
  assume xFreshP: "x \<sharp> P"

  have Goal: "\<And>Q a x Q' P. \<lbrakk>Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> Q'; x \<sharp> Q; x \<sharp> P\<rbrakk> \<Longrightarrow> P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P \<parallel> Q')"
  proof -
    fix Q a x Q' P
    assume QTrans: "Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> Q'"
    assume xFreshQ: "x \<sharp> Q"
    assume xFreshP: "x \<sharp> (P::pi)"

    from QTrans xFreshQ obtain Q'' Q''' where QTrans: "Q \<Longrightarrow>\<^sub>\<tau> Q''"
                                          and Q''Trans: "Q'' \<longmapsto>a<\<nu>x> \<prec> Q'''"
                                          and Q'''Trans: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
      by(blast dest: transitionE)
    from QTrans have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q''" by(rule Par2Chain)
    moreover from Q''Trans xFreshP have "P \<parallel> Q'' \<longmapsto>a<\<nu>x> \<prec> (P \<parallel> Q''')" by(rule Par2B)
    moreover from Q'''Trans have "P \<parallel> Q''' \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'" by(rule Par2Chain)
    ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (P \<parallel> Q')" by(rule transitionI)
  qed
  
  have "\<exists>c::name. c \<sharp> (Q, Q', P)" by(blast intro: name_exists_fresh)
  then obtain c::name where cFreshQ: "c \<sharp> Q" and cFreshQ': "c \<sharp> Q'" and cFreshP: "c \<sharp> P"
    by(force simp add: fresh_prod)

  from cFreshQ' have "a<\<nu>x> \<prec> Q' = a<\<nu>c> \<prec> ([(x, c)] \<bullet> Q')" by(rule alphaBoundResidual)
  moreover have "a<\<nu>x> \<prec> (P \<parallel> Q') = a<\<nu>c> \<prec> (P \<parallel> ([(x, c)] \<bullet> Q'))"
  proof -
    from cFreshQ' cFreshP have "c \<sharp> P \<parallel> Q'" by simp
    hence "a<\<nu>x> \<prec> (P \<parallel> Q') = a<\<nu>c> \<prec> ([(x, c)] \<bullet> (P \<parallel> Q'))" by(rule alphaBoundResidual)
    with cFreshP xFreshP show ?thesis by(simp add: name_fresh_fresh)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> P \<parallel> Q'" using QTrans cFreshQ cFreshP by(force intro: Goal)
next
  assume QTrans: "Q \<Longrightarrow>\<^sub>lu in Q''\<rightarrow>a<x> \<prec> Q'"
     and xFreshP: "x \<sharp> P"
  from QTrans obtain Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                            and Q'''Trans: "Q''' \<longmapsto>a<x> \<prec> Q''"
                            and Q''Chain: "Q''[x::=u] \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  from QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'''" by(rule Par2Chain)
  moreover from Q'''Trans xFreshP have "P \<parallel> Q''' \<longmapsto>a<x> \<prec> (P \<parallel> Q'')" by(rule Par2B)
  moreover have "(P \<parallel> Q'')[x::=u] \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'"
  proof - 
    from Q''Chain have "P \<parallel> (Q''[x::=u]) \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'" by(rule Par2Chain)
    with xFreshP show ?thesis by(simp add: forget)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>lu in (P \<parallel> Q'')\<rightarrow>a<x> \<prec> (P \<parallel> Q')" by(rule transitionI)
qed

lemma Par2F:
  fixes Q :: pi
  and   \<alpha>  :: freeRes
  and   Q' :: pi

  assumes QTrans: "Q \<Longrightarrow>\<^sub>l\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<alpha> \<prec> (P \<parallel> Q')"
proof -
  from QTrans obtain Q'' Q''' where QTrans: "Q \<Longrightarrow>\<^sub>\<tau> Q''"
                                and Q''Trans: "Q'' \<longmapsto>\<alpha> \<prec> Q'''"
                                and Q'''Trans: "Q''' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  from QTrans have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q''" by(rule Par2Chain)
  moreover from Q''Trans have "P \<parallel> Q'' \<longmapsto>\<alpha> \<prec> (P \<parallel> Q''')" by(rule transitions.Par2F)
  moreover from Q'''Trans have "P \<parallel> Q''' \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'" by(rule Par2Chain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Comm1:
  fixes P  :: pi
  and   b  :: name
  and   P'' :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>lb in P'' \<rightarrow>a<x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>la[b] \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> P' \<parallel> Q'"
proof -
  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=b] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a[b] \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> P''[x::=b] \<parallel> Q''"
    by(rule Comm1)
  moreover from P''Chain Q''Chain have "P''[x::=b] \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Comm2:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   Q  :: pi
  and   x  :: name
  and   Q'' :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>la[b] \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>lb in Q''\<rightarrow>a<x> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> P' \<parallel> Q'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a[b] \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                            and Q'''Trans: "Q''' \<longmapsto>a<x> \<prec> Q''"
                            and Q''Chain: "Q''[x::=b] \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> P'' \<parallel> (Q''[x::=b])"
    by(rule Comm2)
  moreover from P''Chain Q''Chain have "P'' \<parallel> (Q''[x::=b]) \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Close1:
  fixes P  :: pi
  and   y  :: name
  and   P'' :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>ly in P''\<rightarrow>a<x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>la<\<nu>y> \<prec> Q'"
  and     yFreshP: "y \<sharp> P"
  and     yFreshQ: "y \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')"
proof -
  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=y] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans yFreshQ obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                        and Q'''Trans: "Q''' \<longmapsto>a<\<nu>y> \<prec> Q''"
                                        and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  
  from PChain yFreshP have yFreshP''': "y \<sharp> P'''" by(rule freshChain)
  
  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans yFreshP''' have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> <\<nu>y>(P''[x::=y] \<parallel> Q'')"
    by(rule Close1)
  moreover have "<\<nu>y>(P''[x::=y] \<parallel> Q'') \<Longrightarrow>\<^sub>\<tau> <\<nu>y>(P' \<parallel> Q')"
  proof -
    from P''Chain Q''Chain have "P''[x::=y] \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
    thus ?thesis by(rule ResChain)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')" by(rule transitionI)
qed

lemma Close2:
  fixes P  :: pi
  and   y  :: name
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q'' :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>y> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>\<^sub>ly in Q''\<rightarrow>a<x> \<prec> Q'"
  and     yFreshP: "y \<sharp> P"
  and     yFreshQ: "y \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')"
proof -
  from PTrans yFreshP obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                        and P'''Trans: "P''' \<longmapsto>a<\<nu>y> \<prec> P''"
                                        and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from QTrans obtain Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                            and Q'''Trans: "Q''' \<longmapsto>a<x> \<prec> Q''"
                            and Q''Chain: "Q''[x::=y] \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  
  from QChain yFreshQ have yFreshQ''': "y \<sharp> Q'''" by(rule freshChain)
  
  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans yFreshQ''' have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> <\<nu>y>(P'' \<parallel> (Q''[x::=y]))"
    by(rule Close2)
  moreover have "<\<nu>y>(P'' \<parallel> (Q''[x::=y])) \<Longrightarrow>\<^sub>\<tau> <\<nu>y>(P' \<parallel> Q')"
  proof -
    from P''Chain Q''Chain have "P'' \<parallel> (Q''[x::=y]) \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
    thus ?thesis by(rule ResChain)
  qed
  ultimately show "P \<parallel> Q \<Longrightarrow>\<^sub>l\<tau> \<prec> <\<nu>y>(P' \<parallel> Q')" by(rule transitionI)
qed

lemma ResF:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   x  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
  and     xFreshAlpha: "x \<sharp> \<alpha>"

  shows "<\<nu>x>P \<Longrightarrow>\<^sub>l\<alpha> \<prec> <\<nu>x>P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                and P''Trans: "P'' \<longmapsto>\<alpha> \<prec> P'''"
                                and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "<\<nu>x>P \<Longrightarrow>\<^sub>\<tau> <\<nu>x>P''" by(rule ResChain)
  moreover from P''Trans xFreshAlpha have "<\<nu>x>P'' \<longmapsto>\<alpha> \<prec> <\<nu>x>P'''"
    by(rule transitions.ResF)
  moreover from P'''Chain have "<\<nu>x>P''' \<Longrightarrow>\<^sub>\<tau> <\<nu>x>P'" by(rule ResChain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma ResB:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   y  :: name
  and   u  :: name
  and   P'' :: pi

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'; y \<noteq> a; y \<noteq> x; x \<sharp> P\<rbrakk> \<Longrightarrow> <\<nu>y>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> (<\<nu>y>P')"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'; y \<noteq> a; y \<noteq> x; y \<noteq> u\<rbrakk> \<Longrightarrow> <\<nu>y>P \<Longrightarrow>\<^sub>lu in (<\<nu>y>P'')\<rightarrow>a<x> \<prec> (<\<nu>y>P')"
proof -
  assume PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
     and yineqa: "y \<noteq> a"
     and yineqx: "y \<noteq> x"
     and xFreshP: "x \<sharp> P"

  from PTrans xFreshP obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                        and P''Trans: "P'' \<longmapsto>a<\<nu>x> \<prec> P'''"
                                        and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "<\<nu>y>P \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P''" by(rule ResChain)
  moreover from P''Trans yineqa yineqx have "<\<nu>y>P'' \<longmapsto>a<\<nu>x> \<prec> (<\<nu>y>P''')"
    by(force intro: ResB)
  moreover from P'''Chain have "<\<nu>y>P''' \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'" by(rule ResChain)
  ultimately show "<\<nu>y>P \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> <\<nu>y>P'" by(rule transitionI)
next
  assume PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
     and yineqa: "y \<noteq> a"
     and yineqx: "y \<noteq> x"
     and yinequ: "y \<noteq> u" 

  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "<\<nu>y>P \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'''" by(rule ResChain)
  moreover from P'''Trans yineqa yineqx have "<\<nu>y>P''' \<longmapsto>a<x> \<prec> (<\<nu>y>P'')"
    by(force intro: ResB)
  moreover have "(<\<nu>y>P'')[x::=u] \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'"
  proof -
    from P''Chain have "<\<nu>y>(P''[x::=u]) \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'" by(rule ResChain)
    with yineqx yinequ show ?thesis by(simp add: eqvt_subs[THEN sym])
  qed
  ultimately show "<\<nu>y>P \<Longrightarrow>\<^sub>lu in (<\<nu>y>P'')\<rightarrow>a<x> \<prec> <\<nu>y>P'" by(rule transitionI)
qed

lemma Bang:
  fixes P  :: pi
  and   Rs :: residual
  and   u  :: name
  and   P'' :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi

  shows "P \<parallel> !P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> !P \<Longrightarrow>\<^sub>l Rs"
  and   "P \<parallel> !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<Longrightarrow> !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
proof -
  assume "P \<parallel> !P \<Longrightarrow>\<^sub>l Rs"
  thus "!P \<Longrightarrow>\<^sub>l Rs"
  proof(nominal_induct avoiding: P rule: residual.strong_inducts)
    case(BoundR a x P' P)
    assume xFreshP: "x \<sharp> P"
    assume PTrans: "P \<parallel> !P \<Longrightarrow>\<^sub>la\<guillemotleft>x\<guillemotright> \<prec> P'"
    from PTrans obtain a' where aeq: "a = BoundOutputS a'" by(cases a, auto)

    with PTrans xFreshP obtain P'' P''' where PChain: "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>a'<\<nu>x> \<prec> P'''"
                                          and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(force dest: transitionE)

    show "!P \<Longrightarrow>\<^sub>la\<guillemotleft>x\<guillemotright> \<prec> P'"
    proof(cases "P'' = P \<parallel> !P")
      assume "P'' = P \<parallel> !P"
      moreover with P''Trans have "!P \<longmapsto>a'<\<nu>x> \<prec> P'''" by(blast intro: transitions.Bang)
      ultimately show ?thesis using PChain P'''Chain aeq by(simp, rule_tac transitionI, auto)
    next
      assume "P'' \<noteq> P \<parallel> !P"
      with PChain have "!P \<Longrightarrow>\<^sub>\<tau> P''" by(rule bangChain)
      with P''Trans P'''Chain aeq show ?thesis by(blast intro: transitionI)
    qed
  next
    fix \<alpha> P' P
    assume "P \<parallel> !P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
    
    then obtain P'' P''' where PChain: "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P''"
                           and P''Trans: "P'' \<longmapsto>\<alpha> \<prec> P'''"
                           and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(force dest: transitionE)


    show "!P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
    proof(cases "P'' = P \<parallel> !P")
      assume "P'' = P \<parallel> !P"
      moreover with P''Trans have "!P \<longmapsto>\<alpha> \<prec> P'''" by(blast intro: transitions.Bang)
      ultimately show ?thesis using PChain P'''Chain by(rule_tac transitionI, auto)
    next
      assume "P'' \<noteq> P \<parallel> !P"
      with PChain have "!P \<Longrightarrow>\<^sub>\<tau> P''" by(rule bangChain)
      with P''Trans P'''Chain show ?thesis by(blast intro: transitionI)
    qed
  qed
next
  assume "P \<parallel> !P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"

  then obtain P''' where PChain: "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'''"
                     and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  
  show "!P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  proof(cases "P''' = P \<parallel> !P")
    assume "P''' = P \<parallel> !P"
    moreover with P'''Trans have "!P \<longmapsto>a<x> \<prec> P''" by(blast intro: transitions.Bang)
    ultimately show ?thesis using PChain P''Chain by(rule_tac transitionI, auto)
  next
    assume "P''' \<noteq> P \<parallel> !P"
    with PChain have "!P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule bangChain)
    with P'''Trans P''Chain show ?thesis by(blast intro: transitionI)
  qed
qed

lemma tauTransitionChain:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(auto simp add: transition_def residualInject)

lemma chainTransitionAppend:
  fixes P   :: pi
  and   P'  :: pi
  and   Rs  :: residual
  and   a   :: name
  and   x   :: name
  and   P'' :: pi
  and   u   :: name
  and   P''' :: pi
  and   \<alpha>   :: freeRes

  shows "P \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P' \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> P \<Longrightarrow>\<^sub>l Rs"
  and   "P \<Longrightarrow>\<^sub>\<tau> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> x \<sharp> P \<Longrightarrow> P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'"
proof -
  assume "P \<Longrightarrow>\<^sub>\<tau> P'" and "P' \<Longrightarrow>\<^sub>l Rs"
  thus "P \<Longrightarrow>\<^sub>l Rs"
    by(auto simp add: transition_def residualInject) (blast dest: rtrancl_trans)+
next
  assume "P \<Longrightarrow>\<^sub>\<tau> P''" and "P'' \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'"
  thus "P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'"
    apply(auto simp add: inputTransition_def residualInject)
    by(blast dest: rtrancl_trans)+
next
  assume PTrans: "P \<Longrightarrow>\<^sub>l a<\<nu>x> \<prec> P''" 
  assume P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
  assume xFreshP: "x \<sharp> P"

  from PTrans xFreshP obtain P''' P'''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                          and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''''"
                                          and P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P''"
    by(blast dest: transitionE)

  from P''''Chain P''Chain have "P'''' \<Longrightarrow>\<^sub>\<tau> P'" by auto
  with PChain P'''Trans show "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'" by(rule transitionI)
next
  assume PTrans: "P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P''" 
  assume P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"

  from PTrans obtain P'''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''''"
                             and P''''Trans: "P'''' \<longmapsto>a<x> \<prec> P'''"
                             and P'''Chain: "P'''[x::=u] \<Longrightarrow>\<^sub>\<tau> P''"
    by(blast dest: transitionE)

  from P'''Chain P''Chain have "P'''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'" by auto
  with PChain P''''Trans show "P \<Longrightarrow>\<^sub>lu in P'''\<rightarrow>a<x> \<prec> P'" by(blast intro: transitionI)
next
  assume PTrans: "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P''" 
  assume P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"

  from PTrans obtain P''' P'''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                  and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''''"
                                  and P''''Chain: "P'''' \<Longrightarrow>\<^sub>\<tau> P''"
    by(blast dest: transitionE)

  from P''''Chain P''Chain have "P'''' \<Longrightarrow>\<^sub>\<tau> P'" by auto
  with PChain P'''Trans show "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by(rule transitionI)
qed

lemma freshInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   u  :: name
  and   P'' :: pi
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"
  and     cFreshP: "c \<sharp> P"
  and     cinequ: "c \<noteq> u"

  shows "c \<sharp> P'"
proof -

  from PTrans obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                            and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                            and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain cFreshP have cFreshP''': "c \<sharp> P'''" by(rule freshChain)
  show "c \<sharp> P'"
  proof(cases "x=c")
    assume xeqc: "x=c"
    from cinequ have "c \<sharp> P''[c::=u]" apply - by(rule fresh_fact2)
    with P''Chain xeqc show ?thesis by(force intro: freshChain)
  next
    assume xineqc: "x\<noteq>c"
    with P'''Trans cFreshP''' have "c \<sharp> P''" by(blast dest: freshBoundDerivative)
    with cinequ have "c \<sharp> P''[x::=u]"
      apply -
      apply(rule fresh_fact1)
      by simp
    with P''Chain show ?thesis by(rule freshChain)
  qed
qed

lemma freshBoundOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
  and     cFreshP: "c \<sharp> P"
  and     cineqx: "c \<noteq> x"

  shows "c \<sharp> P'"
proof -
  have Goal: "\<And>P a x P' c. \<lbrakk>P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'; x \<sharp> P; c \<sharp> P; c \<noteq> x\<rbrakk> \<Longrightarrow> c \<sharp> P'"
  proof -
    fix P a x P' c
    assume PTrans: "P \<Longrightarrow>\<^sub>la<\<nu>x> \<prec> P'"
    assume xFreshP: "x \<sharp> P"
    assume cFreshP: "(c::name) \<sharp> P"
    assume cineqx: "c \<noteq> x"

    from PTrans xFreshP obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                          and P''Trans: "P'' \<longmapsto>a<\<nu>x> \<prec> P'''"
                                          and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PTrans cFreshP have "c \<sharp> P''" by(rule freshChain)
    with P''Trans cineqx have "c \<sharp> P'''" by(blast dest: Late_Semantics.freshBoundDerivative)
    with P'''Trans show "c \<sharp> P'" by(rule freshChain)
  qed

  have "\<exists>d::name. d \<sharp> (P, P', c)" by(blast intro: name_exists_fresh)
  then obtain d::name where dFreshP: "d \<sharp> P" and dFreshP': "d \<sharp> P'" and cineqd: "c \<noteq> d"
    by(force simp add: fresh_prod)

  from PTrans dFreshP' have "P \<Longrightarrow>\<^sub>la<\<nu>d> \<prec> ([(x, d)] \<bullet> P')" by(simp add: alphaBoundResidual)
  hence "c \<sharp> [(x, d)] \<bullet> P'" using dFreshP cFreshP cineqd by(rule Goal)
  with cineqd cineqx show ?thesis by(simp add: name_fresh_left name_calc)
qed

lemma freshTauTransition:
  fixes P :: pi
  and   c :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>l\<tau> \<prec> P'"
  and     cFreshP: "c \<sharp> P"

  shows "c \<sharp> P'"
proof -
  from PTrans have "P \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauTransitionChain)
  thus ?thesis using cFreshP by(rule freshChain)
qed

lemma freshOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>\<^sub>la[b] \<prec> P'"
  and     cFreshP: "c \<sharp> P"

  shows "c \<sharp> P'"
proof -
  from PTrans obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                                and P''Trans: "P'' \<longmapsto>a[b] \<prec> P'''"
                                and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PTrans cFreshP have "c \<sharp> P''" by(rule freshChain)
    with P''Trans have "c \<sharp> P'''" by(blast dest: Late_Semantics.freshFreeDerivative)
    with P'''Trans show ?thesis by(rule freshChain)
qed

lemma eqvtI:
  fixes P    :: pi
  and   Rs   :: residual
  and   perm :: "name prm"
  and   u    :: name
  and   P''  :: pi
  and   a    :: name
  and   x    :: name
  and   P'   :: pi

  shows "P \<Longrightarrow>\<^sub>l Rs \<Longrightarrow> (perm \<bullet> P) \<Longrightarrow>\<^sub>l (perm \<bullet> Rs)"
  and   "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P' \<Longrightarrow> (perm \<bullet> P) \<Longrightarrow>\<^sub>l(perm \<bullet> u) in (perm \<bullet> P'')\<rightarrow>(perm \<bullet> a)<(perm \<bullet> x)> \<prec> (perm \<bullet> P')"
proof -
  assume "P \<Longrightarrow>\<^sub>l Rs"
  thus "(perm \<bullet> P) \<Longrightarrow>\<^sub>l (perm \<bullet> Rs)"
  proof(nominal_induct Rs avoiding: P rule: residual.strong_inducts)
    case(BoundR a x P' P)
    have PTrans: "P \<Longrightarrow>\<^sub>la\<guillemotleft>x\<guillemotright> \<prec> P'" by fact
    moreover then obtain b where aeqb: "a = BoundOutputS b" by(cases a, auto)
    moreover have "x \<sharp> P" by fact
    ultimately obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                               and P''Trans: "P'' \<longmapsto>b<\<nu>x> \<prec> P'''"
                              and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PTrans have "(perm \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P'')" by(rule eqvtChainI)
    moreover from P''Trans have "(perm \<bullet> P'') \<longmapsto> (perm \<bullet> (b<\<nu>x> \<prec> P'''))"
      by(rule eqvts)
    moreover from P'''Trans have "(perm \<bullet> P''') \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P')" by(rule eqvtChainI)
    ultimately show ?case using aeqb by(force intro: transitionI)
  next
    case(FreeR \<alpha> P' P)
    have "P \<Longrightarrow>\<^sub>l\<alpha> \<prec> P'" by fact
    then obtain P'' P''' where PTrans: "P \<Longrightarrow>\<^sub>\<tau> P''"
                           and P''Trans: "P'' \<longmapsto>\<alpha> \<prec> P'''"
                           and P'''Trans: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PTrans have "(perm \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P'')" by(rule eqvtChainI)
    moreover from P''Trans have "(perm \<bullet> P'') \<longmapsto> (perm \<bullet> (\<alpha> \<prec> P'''))"
      by(rule eqvts)
    moreover from P'''Trans have "(perm \<bullet> P''') \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P')" by(rule eqvtChainI)
    ultimately show ?case by(force intro: transitionI)
  qed
next
  assume "P \<Longrightarrow>\<^sub>lu in P''\<rightarrow>a<x> \<prec> P'"

  then obtain P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                     and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                     and P''Chain: "P''[x::=u] \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PChain have "(perm \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P''')" by(rule eqvtChainI)
    moreover from P'''Trans have "(perm \<bullet> P''') \<longmapsto> (perm \<bullet> (a<x> \<prec> P''))"
      by(rule eqvts)
    moreover from P''Chain have "(perm \<bullet> P''[x::=u]) \<Longrightarrow>\<^sub>\<tau> (perm \<bullet> P')" by(rule eqvtChainI)
    ultimately show "(perm \<bullet> P) \<Longrightarrow>\<^sub>l(perm \<bullet> u) in (perm \<bullet> P'')\<rightarrow>(perm \<bullet> a)<(perm \<bullet> x)> \<prec> (perm \<bullet> P')"
      by(force intro: transitionI simp add: eqvt_subs[THEN sym] perm_bij)
qed

lemmas freshTransition = freshBoundOutputTransition freshOutputTransition
                         freshInputTransition freshTauTransition


end
