(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Weak_Early_Step_Semantics
  imports Early_Tau_Chain
begin

lemma inputSupportDerivative:
  assumes "P \<longmapsto>a<x> \<prec> P'"

  shows "(supp P') - {x} \<subseteq> supp P"
using assms
apply(nominal_induct rule: inputInduct)
apply(auto simp add: pi.supp abs_supp supp_atm)
apply(rule ccontr)
apply(simp add: fresh_def[symmetric])
apply(drule_tac fresh_fact1)
apply(rotate_tac 4)
apply assumption
apply(simp add: fresh_def)
apply force
apply(case_tac "x \<sharp> P")
apply(drule_tac fresh_fact1)
apply(rotate_tac 2)
apply assumption
apply(simp add: fresh_def)
apply force
apply(rotate_tac 2)
apply(drule_tac fresh_fact2)
apply(simp add: fresh_def)
by force

lemma outputSupportDerivative:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<longmapsto>a[b] \<prec> P'"

  shows "(supp P') \<subseteq> ((supp P)::name set)"
using assms
by(nominal_induct rule: outputInduct) (auto simp add: pi.supp abs_supp)

lemma boundOutputSupportDerivative:
  assumes "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and     "x \<sharp> P"

  shows "(supp P') - {x} \<subseteq> supp P"
using assms
by(nominal_induct rule: boundOutputInduct) (auto simp add: pi.supp abs_supp supp_atm dest: outputSupportDerivative)

lemma tauSupportDerivative: 

  assumes "P \<longmapsto>\<tau> \<prec> P'"

  shows "((supp P')::name set) \<subseteq> supp P"
using assms
proof(nominal_induct rule: tauInduct)
  case(Tau P)
  thus ?case by(force simp add: pi.supp)
next
  case(Match P)
  thus ?case by(force simp add: pi.supp)
next
  case(Mismatch P)
  thus ?case by(force simp add: pi.supp)
next
  case(Sum1 P)
  thus ?case by(force simp add: pi.supp)
next
  case(Sum2 P)
  thus ?case by(force simp add: pi.supp)
next
  case(Par1 P)
  thus ?case by(force simp add: pi.supp)
next
  case(Par2 P)
  thus ?case by(force simp add: pi.supp)
next
  case(Comm1 P a b P' Q Q')
  from \<open>P \<longmapsto>a<b> \<prec> P'\<close> have "(supp P') - {b} \<subseteq> supp P" by(rule inputSupportDerivative)
  moreover from \<open>Q \<longmapsto> a[b] \<prec> Q'\<close> have "((supp Q')::name set) \<subseteq> supp Q" by(rule outputSupportDerivative)
  moreover from \<open>Q \<longmapsto> a[b] \<prec> Q'\<close> have "b \<in> supp Q"
    by(nominal_induct rule: outputInduct) (auto simp add: pi.supp abs_supp supp_atm)
  ultimately show ?case by(auto simp add: pi.supp)
next
  case(Comm2 P a b P' Q Q')
  from \<open>P \<longmapsto> a[b] \<prec> P'\<close> have "((supp P')::name set) \<subseteq> supp P" by(rule outputSupportDerivative)
  moreover from \<open>Q \<longmapsto>a<b> \<prec> Q'\<close> have "(supp Q') - {b} \<subseteq> supp Q" by(rule inputSupportDerivative)
  moreover from \<open>P \<longmapsto> a[b] \<prec> P'\<close> have "b \<in> supp P"
    by(nominal_induct rule: outputInduct) (auto simp add: pi.supp abs_supp supp_atm)
  ultimately show ?case by(auto simp add: pi.supp)
next
  case(Close1 P a x P' Q Q')
  thus ?case by(auto dest: inputSupportDerivative boundOutputSupportDerivative simp add: abs_supp pi.supp)
next
  case(Close2 P a x P' Q Q')
  thus ?case by(auto dest: inputSupportDerivative boundOutputSupportDerivative simp add: abs_supp pi.supp)
next
  case(Res P P' x)
  thus ?case by(force simp add: pi.supp abs_supp)
next
  case(Bang P P')
  thus ?case by(force simp add: pi.supp)
qed

lemma tauChainSupportDerivative:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<^sub>\<tau> P'"

  shows "((supp P')::name set) \<subseteq> (supp P)"
using assms
by(induct rule: tauChainInduct) (auto dest: tauSupportDerivative)

definition outputTransition :: "pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool" ("_ \<Longrightarrow>_<\<nu>_> \<prec> _" [80, 80, 80, 80] 80)
  where "P \<Longrightarrow>a<\<nu>x> \<prec> P' \<equiv> \<exists>P''' P''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<\<nu>x> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P'"

definition freeTransition :: "pi \<Rightarrow> freeRes\<Rightarrow> pi \<Rightarrow> bool" ("_ \<Longrightarrow>_ \<prec> _" [80, 80, 80] 80)
  where "P \<Longrightarrow>\<alpha> \<prec> P' \<equiv> \<exists>P''' P''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>\<alpha> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P'"

lemma transitionI:
  fixes P    :: pi
  and   P''' :: pi
  and   \<alpha>    :: freeRes
  and   P''  :: pi
  and   P'   :: pi
  and   a    :: name
  and   x    :: name

  shows "\<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'''; P''' \<longmapsto>\<alpha> \<prec> P''; P'' \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>\<alpha> \<prec> P'"
  and   "\<lbrakk>P \<Longrightarrow>\<^sub>\<tau> P'''; P''' \<longmapsto>a<\<nu>x> \<prec> P''; P'' \<Longrightarrow>\<^sub>\<tau> P'\<rbrakk> \<Longrightarrow> P \<Longrightarrow>a<\<nu>x> \<prec> P'"
by(auto simp add: outputTransition_def freeTransition_def)

lemma transitionE:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   a  :: name
  and   x  :: name

  shows "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> (\<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P'' \<and> P'' \<longmapsto>\<alpha> \<prec> P''' \<and> P''' \<Longrightarrow>\<^sub>\<tau> P')" 
  and   "P \<Longrightarrow>a<\<nu>x> \<prec> P' \<Longrightarrow> \<exists>P'' P'''. P \<Longrightarrow>\<^sub>\<tau> P''' \<and> P''' \<longmapsto>a<\<nu>x> \<prec> P'' \<and> P'' \<Longrightarrow>\<^sub>\<tau> P'"
by(auto simp add: outputTransition_def freeTransition_def)

lemma weakTransitionAlpha:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   y  :: name

  assumes PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and     "y \<sharp> P"

  shows "P \<Longrightarrow>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')"
proof(cases "y=x")
  case True
  with PTrans show ?thesis by simp
next
  case False
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  note PChain 
  moreover from PChain \<open>y \<sharp> P\<close> have "y \<sharp> P'''" by(rule freshChain)
  with P'''Trans have "y \<sharp> P''" using \<open>y \<noteq> x\<close> by(rule freshTransition)
  with P'''Trans have "P''' \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P'')" by(simp add: alphaBoundOutput name_swap)
  moreover from P''Chain have "([(x, y)] \<bullet> P'') \<Longrightarrow>\<^sub>\<tau> ([(x, y)] \<bullet> P')"
    by(rule eqvtChainI)
  ultimately show ?thesis by(rule transitionI)
qed

lemma singleActionChain:
  fixes P  :: pi
  and   Rs :: residual

  shows "P \<longmapsto>a<\<nu>x> \<prec> P' \<Longrightarrow> P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and   "P \<longmapsto>\<alpha> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  moreover assume "P \<longmapsto>a<\<nu>x> \<prec> P'"
  moreover have "P' \<Longrightarrow>\<^sub>\<tau> P'" by simp
  ultimately show "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
    by(rule transitionI)
next
  have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  moreover assume "P \<longmapsto>\<alpha> \<prec> P'"
  moreover have "P' \<Longrightarrow>\<^sub>\<tau> P'" by simp
  ultimately show "P \<Longrightarrow>\<alpha> \<prec> P'"
    by(rule transitionI)
qed

lemma Tau:
  fixes P :: pi

  shows "\<tau>.(P) \<Longrightarrow> \<tau> \<prec>  P"
proof -
  have "\<tau>.(P) \<Longrightarrow>\<^sub>\<tau> \<tau>.(P)" by simp
  moreover have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P" by(rule Early_Semantics.Tau)
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  ultimately show ?thesis by(rule transitionI)
qed

lemma Input:
  fixes a :: name
  and   x :: name
  and   u :: name
  and   P :: pi

  shows "a<x>.P \<Longrightarrow> a<u> \<prec> P[x::=u]"
proof -
  have "a<x>.P \<Longrightarrow>\<^sub>\<tau> a<x>.P" by simp
  moreover have "a<x>.P \<longmapsto> a<u> \<prec> P[x::=u]" by(rule Early_Semantics.Input)
  moreover have "P[x::=u] \<Longrightarrow>\<^sub>\<tau> P[x::=u]" by simp
  ultimately show ?thesis by(rule transitionI)
qed
  
lemma Output:
  fixes a :: name
  and   b :: name
  and   P :: pi

  shows "a{b}.P \<Longrightarrow>a[b] \<prec> P"
proof -
  have "a{b}.P \<Longrightarrow>\<^sub>\<tau> a{b}.P" by simp
  moreover have "a{b}.P \<longmapsto>a[b] \<prec> P" by(rule Early_Semantics.Output)
  moreover have "P \<Longrightarrow>\<^sub>\<tau> P" by simp
  ultimately show ?thesis by(rule transitionI)
qed

lemma Match:
  fixes P  :: pi
  and   b  :: name
  and   x  :: name
  and   a  :: name
  and   P' :: pi
  and   \<alpha> :: freeRes

  shows "P \<Longrightarrow>b<\<nu>x> \<prec> P' \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>b<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> [a\<frown>a]P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  assume "P \<Longrightarrow> b<\<nu>x> \<prec> P'" 
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>b<\<nu>x> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  show "[a\<frown>a]P \<Longrightarrow>b<\<nu>x> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> [a\<frown>a]P" by simp
    moreover from \<open>P = P'''\<close> P'''Trans have "[a\<frown>a]P \<longmapsto> b<\<nu>x> \<prec> P''"
      by(rule_tac Early_Semantics.Match) auto
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>P \<noteq> P'''\<close> have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule matchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
next
  assume "P \<Longrightarrow>\<alpha> \<prec> P'" 
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  show "[a\<frown>a]P \<Longrightarrow>\<alpha> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> [a\<frown>a]P" by simp
    moreover from \<open>P = P'''\<close> P'''Trans have "[a\<frown>a]P \<longmapsto>\<alpha> \<prec> P''"
      by(rule_tac Early_Semantics.Match) auto
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>P \<noteq> P'''\<close> have "[a\<frown>a]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule matchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
qed
                              
lemma Mismatch:
  fixes P  :: pi
  and   c  :: name
  and   x  :: name
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   \<alpha> :: freeRes

  shows "\<lbrakk>P \<Longrightarrow>c<\<nu>x> \<prec> P'; a \<noteq> b\<rbrakk> \<Longrightarrow> [a\<noteq>b]P \<Longrightarrow>c<\<nu>x> \<prec> P'"
  and   "\<lbrakk>P \<Longrightarrow>\<alpha> \<prec> P'; a \<noteq> b\<rbrakk> \<Longrightarrow> [a\<noteq>b]P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  assume "P \<Longrightarrow>c<\<nu>x> \<prec> P'" 
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>c<\<nu>x> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  assume "a \<noteq> b"
  show "[a\<noteq>b]P \<Longrightarrow>c<\<nu>x> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "[a\<noteq>b]P \<Longrightarrow>\<^sub>\<tau> [a\<noteq>b]P" by simp
    moreover from \<open>P = P'''\<close> \<open>a \<noteq> b\<close> P'''Trans have "[a\<noteq>b]P \<longmapsto> c<\<nu>x> \<prec> P''"
      by(rule_tac Early_Semantics.Mismatch) auto
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>a \<noteq> b\<close> \<open>P \<noteq> P'''\<close> have "[a\<noteq>b]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule mismatchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
next
  assume "P \<Longrightarrow>\<alpha> \<prec> P'" 
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  assume "a \<noteq> b"
  show "[a\<noteq>b]P \<Longrightarrow>\<alpha> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "[a\<noteq>b]P \<Longrightarrow>\<^sub>\<tau> [a\<noteq>b]P" by simp
    moreover from \<open>P = P'''\<close> \<open>a \<noteq> b\<close> P'''Trans have "[a\<noteq>b]P \<longmapsto>\<alpha> \<prec> P''"
      by(rule_tac Early_Semantics.Mismatch) auto
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>a \<noteq> b\<close> \<open>P \<noteq> P'''\<close> have "[a\<noteq>b]P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule mismatchChain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
qed
                              
lemma Open:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes PTrans:  "P \<Longrightarrow>a[b] \<prec> P'"
  and     "a \<noteq> b"

  shows "<\<nu>b>P \<Longrightarrow>a<\<nu>b> \<prec> P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a[b] \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  from PChain have "<\<nu>b>P \<Longrightarrow>\<^sub>\<tau> <\<nu>b>P'''" by(rule ResChain)
  moreover from P'''Trans \<open>a \<noteq> b\<close> have "<\<nu>b>P''' \<longmapsto>a<\<nu>b> \<prec> P''" by(rule Open)
  ultimately show ?thesis using P''Chain by(rule transitionI)
qed

lemma Sum1:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   \<alpha>  :: freeRes

  shows "P \<Longrightarrow>a<\<nu>x> \<prec> P' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  assume "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>a<\<nu>x> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from P'''Trans \<open>P = P'''\<close> have "P \<oplus> Q \<longmapsto> a<\<nu>x> \<prec> P''" by(blast intro: Sum1)
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>P \<noteq> P'''\<close> have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P'''" by(rule sum1Chain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
next
  assume "P \<Longrightarrow>\<alpha> \<prec> P'"
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> P'"
  proof(cases "P = P'''")
    case True
    have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from P'''Trans \<open>P = P'''\<close> have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> P''" by(blast intro: Sum1)
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>P \<noteq> P'''\<close> have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P'''" by(rule sum1Chain)
    thus ?thesis using P'''Trans P''Chain by(rule transitionI)
  qed
qed

lemma Sum2:
  fixes Q  :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi
  and   P  :: pi
  and   \<alpha>  :: freeRes

  shows "Q \<Longrightarrow>a<\<nu>x> \<prec> Q' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  and   "Q \<Longrightarrow>\<alpha> \<prec> Q' \<Longrightarrow> P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> Q'"
proof -
  assume "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  then obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                         and Q'''Trans: "Q''' \<longmapsto>a<\<nu>x> \<prec> Q''"
                         and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(force dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  proof(cases "Q = Q'''")
    case True
    have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from Q'''Trans \<open>Q = Q'''\<close> have "P \<oplus> Q \<longmapsto>a<\<nu>x> \<prec> Q''" by(blast intro: Sum2)
    ultimately show ?thesis using Q''Chain by(rule transitionI)
  next
    case False
    from QChain \<open>Q \<noteq> Q'''\<close> have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q'''" by(rule sum2Chain)
    thus ?thesis using Q'''Trans Q''Chain by(rule transitionI)
  qed
next
  assume "Q \<Longrightarrow>\<alpha> \<prec> Q'"
  then obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                         and Q'''Trans: "Q''' \<longmapsto>\<alpha> \<prec> Q''"
                         and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(force dest: transitionE)
  show "P \<oplus> Q \<Longrightarrow>\<alpha> \<prec> Q'"
  proof(cases "Q = Q'''")
    case True
    have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> P \<oplus> Q" by simp
    moreover from Q'''Trans \<open>Q = Q'''\<close> have "P \<oplus> Q \<longmapsto>\<alpha> \<prec> Q''" by(blast intro: Sum2)
    ultimately show ?thesis using Q''Chain by(rule transitionI)
  next
    case False
    from QChain \<open>Q \<noteq> Q'''\<close> have "P \<oplus> Q \<Longrightarrow>\<^sub>\<tau> Q'''" by(rule sum2Chain)
    thus ?thesis using Q'''Trans Q''Chain by(rule transitionI)
  qed
qed

lemma Par1B:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi

  assumes PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and     "x \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>a<\<nu>x> \<prec> (P' \<parallel> Q)"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from PChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q" by(rule Par1Chain)
  moreover from P'''Trans \<open>x \<sharp> Q\<close> have "P''' \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> (P'' \<parallel> Q)" by(rule Early_Semantics.Par1B)
  moreover from P''Chain have "P'' \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q" by(rule Par1Chain)
  ultimately show "P \<parallel> Q \<Longrightarrow>a<\<nu>x> \<prec> (P' \<parallel> Q)" by(rule transitionI)
qed

lemma Par1F:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   Q  :: pi

  assumes PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'"

  shows "P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> (P' \<parallel> Q)"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from PChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q" by(rule Par1Chain)
  moreover from P'''Trans have "P''' \<parallel> Q \<longmapsto>\<alpha> \<prec> (P'' \<parallel> Q)" by(rule Early_Semantics.Par1F)
  moreover from P''Chain have "P'' \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q" by(rule Par1Chain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Par2B:
  fixes Q  :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi
  and   P  :: pi

  assumes QTrans: "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  and     "x \<sharp> P"

  shows "P \<parallel> Q \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> Q')"
proof -
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a<\<nu>x> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  from QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'''" by(rule Par2Chain)
  moreover from Q'''Trans \<open>x \<sharp> P\<close> have "P \<parallel> Q''' \<longmapsto>a<\<nu>x> \<prec> (P \<parallel> Q'')" by(rule Early_Semantics.Par2B)
  moreover from Q''Chain have "P \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'" by(rule Par2Chain)
  ultimately show "P \<parallel> Q \<Longrightarrow>a<\<nu>x> \<prec> (P \<parallel> Q')" by(rule transitionI)
qed

lemma Par2F:
  fixes Q  :: pi
  and   \<alpha>  :: freeRes
  and   Q' :: pi
  and   P  :: pi

  assumes QTrans: "Q \<Longrightarrow>\<alpha> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<alpha> \<prec> (P \<parallel> Q')"
proof -
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>\<alpha> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)
  from QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'''" by(rule Par2Chain)
  moreover from Q'''Trans have "P \<parallel> Q''' \<longmapsto>\<alpha> \<prec> (P \<parallel> Q'')" by(rule Early_Semantics.Par2F)
  moreover from Q''Chain have "P \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P \<parallel> Q'" by(rule Par2Chain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Comm1:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>a<b> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>a[b] \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<tau> \<prec> P' \<parallel> Q'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<b> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a[b] \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> P'' \<parallel> Q''"
    by(rule Early_Semantics.Comm1)
  moreover from P''Chain Q''Chain have "P'' \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Comm2:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>a[b] \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>a<b> \<prec> Q'"

  shows "P \<parallel> Q \<Longrightarrow>\<tau> \<prec> P' \<parallel> Q'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a[b] \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a<b> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> P'' \<parallel> Q''"
    by(rule Early_Semantics.Comm2)
  moreover from P''Chain Q''Chain have "P'' \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Close1:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>a<x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>a<\<nu>x> \<prec> Q'"
  and     "x \<sharp> P"

  shows "P \<parallel> Q \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"
proof -
  from PTrans obtain P''' P'' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a<\<nu>x> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)


  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from PChain \<open>x \<sharp> P\<close> have "x \<sharp> P'''" by(rule freshChain)
  with P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> <\<nu>x>(P'' \<parallel> Q'')"
    by(rule Early_Semantics.Close1)
  moreover from P''Chain Q''Chain have "P'' \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
  hence "<\<nu>x>(P'' \<parallel> Q'') \<Longrightarrow>\<^sub>\<tau> <\<nu>x>(P' \<parallel> Q')" by(rule ResChain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Close2:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi
  
  assumes PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and     QTrans: "Q \<Longrightarrow>a<x> \<prec> Q'"
  and     xFreshQ: "x \<sharp> Q"

  shows "P \<parallel> Q \<Longrightarrow>\<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  from QTrans obtain Q'' Q''' where QChain: "Q \<Longrightarrow>\<^sub>\<tau> Q'''"
                                and Q'''Trans: "Q''' \<longmapsto>a<x> \<prec> Q''"
                                and Q''Chain: "Q'' \<Longrightarrow>\<^sub>\<tau> Q'"
    by(blast dest: transitionE)

  from PChain QChain have "P \<parallel> Q \<Longrightarrow>\<^sub>\<tau> P''' \<parallel> Q'''" by(rule chainPar)
  moreover from QChain \<open>x \<sharp> Q\<close> have "x \<sharp> Q'''" by(rule freshChain)

  with P'''Trans Q'''Trans have "P''' \<parallel> Q''' \<longmapsto>\<tau> \<prec> <\<nu>x>(P'' \<parallel> Q'')"
    by(rule Early_Semantics.Close2)
  moreover from P''Chain Q''Chain have "P'' \<parallel> Q'' \<Longrightarrow>\<^sub>\<tau> P' \<parallel> Q'" by(rule chainPar)
 hence "<\<nu>x>(P'' \<parallel> Q'') \<Longrightarrow>\<^sub>\<tau> <\<nu>x>(P' \<parallel> Q')" by(rule ResChain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma ResF:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   x  :: name

  assumes PTrans: "P \<Longrightarrow>\<alpha> \<prec> P'"
  and     "x \<sharp> \<alpha>"

  shows "<\<nu>x>P \<Longrightarrow>\<alpha> \<prec> <\<nu>x>P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "<\<nu>x>P \<Longrightarrow>\<^sub>\<tau> <\<nu>x>P'''" by(rule ResChain)
  moreover from P'''Trans \<open>x \<sharp> \<alpha>\<close> have "<\<nu>x>P''' \<longmapsto>\<alpha> \<prec> <\<nu>x>P''"
    by(rule Early_Semantics.ResF)
  moreover from P''Chain have "<\<nu>x>P'' \<Longrightarrow>\<^sub>\<tau> <\<nu>x>P'" by(rule ResChain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma ResB:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   y  :: name

  assumes PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and     "y \<noteq> a"
  and     "y \<noteq> x"

  shows "<\<nu>y>P \<Longrightarrow>a<\<nu>x> \<prec> (<\<nu>y>P')"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "<\<nu>y>P \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'''" by(rule ResChain)
  moreover from P'''Trans  \<open>y \<noteq> a\<close> \<open>y \<noteq> x\<close> have "<\<nu>y>P''' \<longmapsto>a<\<nu>x> \<prec> (<\<nu>y>P'')"
    by(rule Early_Semantics.ResB)
  moreover from P''Chain have "<\<nu>y>P'' \<Longrightarrow>\<^sub>\<tau> <\<nu>y>P'" by(rule ResChain)
  ultimately show ?thesis by(rule transitionI)
qed

lemma Bang:
  fixes P  :: pi
  and   Rs :: residual


  shows "P \<parallel> !P \<Longrightarrow>a<\<nu>x> \<prec> P' \<Longrightarrow> !P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and   "P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> !P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  assume PTrans: "P \<parallel> !P \<Longrightarrow> a<\<nu>x> \<prec> P'"

  from PTrans obtain P'' P''' where PChain: "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)
  
  show "!P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  proof(cases "P''' = P \<parallel> !P")
    case True
    have "!P \<Longrightarrow>\<^sub>\<tau> !P" by simp
    moreover from P'''Trans \<open>P''' = P \<parallel> !P\<close> have "!P \<longmapsto>a<\<nu>x> \<prec> P''" by(blast intro: Early_Semantics.Bang)
    ultimately show ?thesis using P''Chain by(rule transitionI)
  next
    case False
    from PChain \<open>P''' \<noteq> P \<parallel> !P\<close> have "!P \<Longrightarrow>\<^sub>\<tau> P'''" by(rule bangChain)
    with P'''Trans P''Chain show ?thesis by(blast intro: transitionI)
  qed
next
  fix \<alpha> P' P
  assume "P \<parallel> !P \<Longrightarrow>\<alpha> \<prec> P'"
    
  then obtain P'' P''' where PChain: "P \<parallel> !P \<Longrightarrow>\<^sub>\<tau> P''"
                         and P''Trans: "P'' \<longmapsto>\<alpha> \<prec> P'''"
                         and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(force dest: transitionE)

  show "!P \<Longrightarrow>\<alpha> \<prec> P'"
  proof(cases "P'' = P \<parallel> !P")
    assume "P'' = P \<parallel> !P"
    moreover with P''Trans have "!P \<longmapsto>\<alpha> \<prec> P'''" by(blast intro: Bang)
    ultimately show ?thesis using PChain P'''Chain by(rule_tac transitionI, auto)
  next
    assume "P'' \<noteq> P \<parallel> !P"
    with PChain have "!P \<Longrightarrow>\<^sub>\<tau> P''" by(rule bangChain)
    with P''Trans P'''Chain show ?thesis by(blast intro: transitionI)
  qed
qed

lemma tauTransitionChain:
  fixes P  :: pi
  and   P' :: pi

  assumes "P \<Longrightarrow>\<tau> \<prec> P'"

  shows "P \<Longrightarrow>\<^sub>\<tau> P'"
using assms
by(force dest: transitionE tauActTauChain)

lemma chainTransitionAppend:
  fixes P   :: pi
  and   P'  :: pi
  and   Rs  :: residual
  and   a   :: name
  and   x   :: name
  and   P'' :: pi
  and   \<alpha>   :: freeRes

  shows "P \<Longrightarrow>a<\<nu>x> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<alpha> \<prec> P'' \<Longrightarrow> P'' \<Longrightarrow>\<^sub>\<tau> P' \<Longrightarrow> P \<Longrightarrow>\<alpha> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>\<tau> P'' \<Longrightarrow> P'' \<Longrightarrow>a<\<nu>x> \<prec> P' \<Longrightarrow> P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and   "P \<Longrightarrow>\<^sub>\<tau> P'' \<Longrightarrow> P'' \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> P \<Longrightarrow>\<alpha> \<prec> P'"
proof -
  assume PTrans: "P \<Longrightarrow> a<\<nu>x> \<prec> P''" 
  assume P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"

  from PTrans obtain P''' P'''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''''"
                                  and P''''Trans: "P'''' \<longmapsto>a<\<nu>x> \<prec> P'''"
                                  and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P''"
    by(blast dest: transitionE)

  from P'''Chain P''Chain have "P''' \<Longrightarrow>\<^sub>\<tau> P'" by auto
  with PChain P''''Trans show "P \<Longrightarrow>a<\<nu>x> \<prec> P'" by(rule transitionI)
next
  assume PTrans: "P \<Longrightarrow>\<alpha> \<prec> P''" 
  assume P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"

  from PTrans obtain P''' P'''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P''''"
                                  and P''''Trans: "P'''' \<longmapsto>\<alpha> \<prec> P'''"
                                  and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P''"
    by(blast dest: transitionE)

  from P'''Chain P''Chain have "P''' \<Longrightarrow>\<^sub>\<tau> P'" by auto
  with PChain P''''Trans show "P \<Longrightarrow>\<alpha> \<prec> P'" by(rule transitionI)
next
  assume PChain: "P \<Longrightarrow>\<^sub>\<tau> P''"
  assume P''Trans: "P'' \<Longrightarrow> a<\<nu>x> \<prec> P'" 

  from P''Trans obtain P''' P'''' where P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P''''"
                                    and P''''Trans: "P'''' \<longmapsto>a<\<nu>x> \<prec> P'''"
                                    and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain P''Chain have "P \<Longrightarrow>\<^sub>\<tau> P''''" by auto
  thus "P \<Longrightarrow>a<\<nu>x> \<prec> P'" using P''''Trans P'''Chain by(rule transitionI)
next
  assume PChain: "P \<Longrightarrow>\<^sub>\<tau> P''"
  assume P''Trans: "P'' \<Longrightarrow>\<alpha> \<prec> P'" 

  from P''Trans obtain P''' P'''' where P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P''''"
                                    and P''''Trans: "P'''' \<longmapsto>\<alpha> \<prec> P'''"
                                    and P'''Chain: "P''' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain P''Chain have "P \<Longrightarrow>\<^sub>\<tau> P''''" by auto
  thus "P \<Longrightarrow>\<alpha> \<prec> P'" using P''''Trans P'''Chain by(rule transitionI)
qed

lemma freshBoundOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<noteq> x"

  shows "c \<sharp> P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain \<open>c \<sharp> P\<close> have "c \<sharp> P'''" by(rule freshChain)
  with P'''Trans have "c \<sharp> P''" using \<open>c \<noteq> x\<close> by(rule Early_Semantics.freshTransition)
  with P''Chain show "c \<sharp> P'" by(rule freshChain)
qed

lemma freshTauTransition:
  fixes P :: pi
  and   c :: name

  assumes PTrans: "P \<Longrightarrow>\<tau> \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<sharp> P'"
proof -
  from PTrans have "P \<Longrightarrow>\<^sub>\<tau> P'" by(rule tauTransitionChain)
  thus ?thesis using \<open>c \<sharp> P\<close> by(rule freshChain)
qed

lemma freshOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>a[b] \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<sharp> P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a[b] \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
      by(blast dest: transitionE)

    from PChain \<open>c \<sharp> P\<close> have "c \<sharp> P'''" by(rule freshChain)
    with P'''Trans have "c \<sharp> P''" by(rule Early_Semantics.freshTransition)
    with P''Chain show ?thesis by(rule freshChain)
qed

lemma eqvtI[eqvt]:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   p :: "name prm"
  and   \<alpha> :: freeRes

  shows "P \<Longrightarrow>a<\<nu>x> \<prec> P' \<Longrightarrow> (p \<bullet> P) \<Longrightarrow>(p \<bullet> a)<\<nu>(p \<bullet> x)> \<prec> (p \<bullet> P')"
  and   "P \<Longrightarrow>\<alpha> \<prec> P' \<Longrightarrow> (p \<bullet> P) \<Longrightarrow>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
proof -
  assume "P \<Longrightarrow>a<\<nu>x> \<prec> P'"
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>a<\<nu>x> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain have "(p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P''')" by(rule eqvtChainI)
  moreover from P'''Trans have "(p \<bullet> P''') \<longmapsto> (p \<bullet> (a<\<nu>x> \<prec> P''))"
    by(rule TransitionsEarly.eqvt)
  hence "(p \<bullet> P''') \<longmapsto> (p \<bullet> a)<\<nu>(p \<bullet> x)> \<prec> (p \<bullet> P'')"
    by(simp add: eqvts)
  moreover from P''Chain have "(p \<bullet> P'') \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')" by(rule eqvtChainI)
  ultimately show "(p \<bullet> P) \<Longrightarrow>(p \<bullet> a)<\<nu>(p \<bullet> x)> \<prec> (p \<bullet> P')"
    by(rule transitionI)
next
  assume "P \<Longrightarrow>\<alpha> \<prec> P'"
  then obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                         and P'''Trans: "P''' \<longmapsto>\<alpha> \<prec> P''"
                         and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)
  
  from PChain have "(p \<bullet> P) \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P''')" by(rule eqvtChainI)
  moreover from P'''Trans have "(p \<bullet> P''') \<longmapsto> (p \<bullet> (\<alpha> \<prec> P''))"
    by(rule TransitionsEarly.eqvt)
  hence "(p \<bullet> P''') \<longmapsto> (p \<bullet> \<alpha>) \<prec> (p \<bullet> P'')"
    by(simp add: eqvts)
  moreover from P''Chain have "(p \<bullet> P'') \<Longrightarrow>\<^sub>\<tau> (p \<bullet> P')" by(rule eqvtChainI)
  ultimately show "(p \<bullet> P) \<Longrightarrow>(p \<bullet> \<alpha>) \<prec> (p \<bullet> P')"
    by(rule transitionI)
qed
    
lemma freshInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes PTrans: "P \<Longrightarrow>a<b> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<noteq> b"

  shows "c \<sharp> P'"
proof -
  from PTrans obtain P'' P''' where PChain: "P \<Longrightarrow>\<^sub>\<tau> P'''"
                                and P'''Trans: "P''' \<longmapsto>a<b> \<prec> P''"
                                and P''Chain: "P'' \<Longrightarrow>\<^sub>\<tau> P'"
    by(blast dest: transitionE)

  from PChain \<open>c \<sharp> P\<close> have "c \<sharp> P'''" by(rule freshChain)
  with P'''Trans have "c \<sharp> P''" using \<open>c \<noteq> b\<close> by(rule Early_Semantics.freshInputTransition)
  with P''Chain show ?thesis by(rule freshChain)
qed

lemmas freshTransition = freshBoundOutputTransition freshOutputTransition
                         freshInputTransition freshTauTransition

end
