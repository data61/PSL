(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Early_Sim
  imports Early_Semantics Rel
begin

definition "strongSimEarly" :: "pi \<Rightarrow> (pi \<times> pi) set \<Rightarrow> pi \<Rightarrow> bool" ("_ \<leadsto>[_] _" [80, 80, 80] 80) where
  "P \<leadsto>[Rel] Q \<equiv> (\<forall>a y Q'. Q \<longmapsto>a<\<nu>y> \<prec> Q' \<longrightarrow> y \<sharp> P \<longrightarrow> (\<exists>P'. P \<longmapsto>a<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel)) \<and>
                 (\<forall>\<alpha> Q'. Q \<longmapsto>\<alpha> \<prec> Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>\<alpha> \<prec> P' \<and> (P', Q') \<in> Rel))"

lemma monotonic: 
  fixes A  :: "(pi \<times> pi) set"
  and   B  :: "(pi \<times> pi) set"
  and   P  :: pi
  and   P' :: pi

  assumes "P \<leadsto>[A] P'"
  and     "A \<subseteq> B"

  shows "P \<leadsto>[B] P'"
using assms
by(fastforce simp add: strongSimEarly_def)

lemma freshUnit[simp]:
  fixes y :: name

  shows "y \<sharp> ()"
by(auto simp add: fresh_def supp_unit)

lemma simCasesCont[consumes 1, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes Eqvt:  "eqvt Rel"
  and     Bound: "\<And>a y Q'. \<lbrakk>Q \<longmapsto> a<\<nu>y> \<prec> Q'; y \<sharp> P; y \<sharp> Q; y \<sharp> C\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto> a<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>[Rel] Q"
proof -
  from Free show ?thesis
  proof(auto simp add: strongSimEarly_def)
    fix Q' a y
    assume yFreshP: "(y::name) \<sharp> P"
    assume Trans: "Q \<longmapsto> a<\<nu>y> \<prec> Q'"
    have "\<exists>c::name. c \<sharp> (P, Q', y, Q, C)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshP: "c \<sharp> P" and cFreshQ': "c \<sharp> Q'" and cFreshC: "c \<sharp> C"
                          and cineqy: "c \<noteq> y" and "c \<sharp> Q"
      by(force simp add: fresh_prod name_fresh)

    from Trans cFreshQ' have "Q \<longmapsto> a<\<nu>c> \<prec> ([(y, c)] \<bullet> Q')" by(simp add: alphaBoundOutput)
    hence "\<exists>P'. P \<longmapsto> a<\<nu>c> \<prec> P' \<and> (P', [(y, c)] \<bullet> Q') \<in> Rel" using \<open>c \<sharp> P\<close> \<open>c \<sharp> Q\<close> \<open>c \<sharp> C\<close>
      by(rule Bound)
    then obtain P' where PTrans: "P \<longmapsto> a<\<nu>c> \<prec> P'" and P'RelQ': "(P', [(y, c)] \<bullet> Q') \<in> Rel"
      by blast

    from PTrans yFreshP cineqy have yFreshP': "y \<sharp> P'" by(force intro: freshTransition)
    with PTrans have "P \<longmapsto> a<\<nu>y> \<prec> ([(y, c)] \<bullet> P')" by(simp add: alphaBoundOutput name_swap)
    moreover have "([(y, c)] \<bullet> P', Q') \<in> Rel" (is "?goal")
    proof -
      from Eqvt P'RelQ' have "([(y, c)] \<bullet> P', [(y, c)] \<bullet> [(y, c)] \<bullet> Q') \<in> Rel"
        by(rule eqvtRelI)
      with cineqy show ?goal by(simp add: name_calc)
    qed
    ultimately show "\<exists>P'. P \<longmapsto>a<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel" by blast
  qed
qed

lemma simCases[consumes 0, case_names Bound Free]:
  fixes P   :: pi
  and   Q   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   C   :: "'a::fs_name"

  assumes Bound: "\<And>a y Q'. \<lbrakk>Q \<longmapsto> a<\<nu>y> \<prec> Q'; y \<sharp> P\<rbrakk> \<Longrightarrow> \<exists>P'. P \<longmapsto> a<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel"
  and     Free:  "\<And>\<alpha> Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"

  shows "P \<leadsto>[Rel] Q"
using assms
by(auto simp add: strongSimEarly_def)

lemma elim:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   Q'  :: pi

  assumes "P \<leadsto>[Rel] Q"

  shows "Q \<longmapsto> a<\<nu>x> \<prec> Q' \<Longrightarrow> x \<sharp> P \<Longrightarrow> \<exists>P'. P \<longmapsto> a<\<nu>x> \<prec> P' \<and> (P', Q') \<in> Rel"
  and   "Q \<longmapsto> \<alpha> \<prec> Q' \<Longrightarrow> \<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel"
using assms by(simp add: strongSimEarly_def)+

lemma eqvtI:
  fixes P    :: pi
  and   Q    :: pi
  and   Rel  :: "(pi \<times> pi) set"
  and   perm :: "name prm"

  assumes Sim: "P \<leadsto>[Rel] Q"
  and     RelRel': "Rel \<subseteq> Rel'"
  and     EqvtRel': "eqvt Rel'"

  shows "(perm \<bullet> P) \<leadsto>[Rel'] (perm \<bullet> Q)"
proof(induct rule: simCases)
  case(Bound a y Q')
  have Trans: "(perm \<bullet> Q) \<longmapsto> a<\<nu>y> \<prec> Q'" by fact
  have yFreshP: "y \<sharp> perm \<bullet> P" by fact
  
  from Trans have "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (a<\<nu>y> \<prec> Q')"
    by(rule TransitionsEarly.eqvt)
  hence "Q \<longmapsto> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> y)> \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  moreover from yFreshP have "(rev perm \<bullet> y) \<sharp> P" by(simp add: name_fresh_left)
  ultimately have "\<exists>P'. P \<longmapsto> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> y)> \<prec> P' \<and> (P', rev perm \<bullet> Q') \<in> Rel" using Sim
    by(force intro: elim)
  then obtain P' where PTrans: "P \<longmapsto> (rev perm \<bullet> a)<\<nu>(rev perm \<bullet> y)> \<prec> P'" and P'RelQ': "(P', rev perm \<bullet> Q') \<in> Rel"
    by blast
  
  from PTrans have "(perm \<bullet> P) \<longmapsto> perm \<bullet> ((rev perm \<bullet> a)<\<nu>(rev perm \<bullet> y)> \<prec> P')" by(rule TransitionsEarly.eqvt)
  hence L1: "(perm \<bullet> P) \<longmapsto> a<\<nu>y> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from P'RelQ' RelRel' have "(P', rev perm \<bullet> Q') \<in> Rel'" by blast
  with EqvtRel' have "(perm \<bullet> P', perm \<bullet> (rev perm \<bullet> Q')) \<in> Rel'"
    by(rule eqvtRelI)
  hence "(perm \<bullet> P', Q') \<in> Rel'" by(simp add: name_per_rev)
  with L1 show ?case by blast
next
  case(Free \<alpha> Q')
  have Trans: "(perm \<bullet> Q) \<longmapsto> \<alpha> \<prec> Q'" by fact

  from Trans have "(rev perm \<bullet> (perm \<bullet> Q)) \<longmapsto> rev perm \<bullet> (\<alpha> \<prec> Q')"
    by(rule TransitionsEarly.eqvt)
  hence "Q \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> (rev perm \<bullet> Q')" 
    by(simp add: name_rev_per)
  with Sim have "\<exists>P'. P \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> P' \<and> (P', (rev perm \<bullet> Q')) \<in> Rel"
    by(force intro: elim)
  then obtain P' where PTrans: "P \<longmapsto> (rev perm \<bullet> \<alpha>) \<prec> P'" and PRel: "(P', (rev perm \<bullet> Q')) \<in> Rel" by blast
  
  from PTrans have "(perm \<bullet> P) \<longmapsto> perm \<bullet> ((rev perm \<bullet> \<alpha>)\<prec> P')" by(rule TransitionsEarly.eqvt)
  hence L1: "(perm \<bullet> P) \<longmapsto> \<alpha> \<prec> (perm \<bullet> P')" by(simp add: name_per_rev)
  from PRel EqvtRel' RelRel'  have "((perm \<bullet> P'), (perm \<bullet> (rev perm \<bullet> Q'))) \<in> Rel'"
    by(force intro: eqvtRelI)
  hence "((perm \<bullet> P'), Q') \<in> Rel'" by(simp add: name_per_rev)
  with L1 show ?case by blast
qed


(*****************Reflexivity and transitivity*********************)

lemma reflexive:
  fixes P   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes "Id \<subseteq> Rel"

  shows "P \<leadsto>[Rel] P"
using assms
by(auto simp add: strongSimEarly_def)

lemmas fresh_prod[simp]

lemma transitive:
  fixes P     :: pi
  and   Q     :: pi
  and   R     :: pi
  and   Rel   :: "(pi \<times> pi) set"
  and   Rel'  :: "(pi \<times> pi) set"
  and   Rel'' :: "(pi \<times> pi) set"

  assumes PSimQ: "P \<leadsto>[Rel] Q"
  and     QSimR: "Q \<leadsto>[Rel'] R"
  and     Eqvt': "eqvt Rel''"
  and     Trans: "Rel O Rel' \<subseteq> Rel''"

  shows "P \<leadsto>[Rel''] R"
proof -
  from Eqvt' show ?thesis
  proof(induct rule: simCasesCont[where C=Q])
    case(Bound a y R')
    have RTrans: "R \<longmapsto> a<\<nu>y> \<prec> R'" by fact

    from QSimR RTrans \<open>y \<sharp> Q\<close> have "\<exists>Q'. Q \<longmapsto> a<\<nu>y> \<prec> Q' \<and> (Q', R') \<in> Rel'"
      by(rule elim)
    then obtain Q' where QTrans: "Q \<longmapsto> a<\<nu>y> \<prec> Q'" and Q'Rel'R': "(Q', R') \<in> Rel'" by blast
    from PSimQ QTrans \<open>y \<sharp> P\<close> have "\<exists>P'. P \<longmapsto> a<\<nu>y> \<prec> P' \<and> (P', Q') \<in> Rel"
      by(rule elim)
    then obtain P' where PTrans: "P \<longmapsto> a<\<nu>y> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast

    moreover from P'RelQ' Q'Rel'R' Trans have "(P', R') \<in> Rel''" by blast

    ultimately show ?case by blast
  next
    case(Free \<alpha> R')
    have RTrans: "R \<longmapsto> \<alpha> \<prec> R'" by fact
    with QSimR have "\<exists>Q'. Q \<longmapsto> \<alpha> \<prec> Q' \<and> (Q', R') \<in> Rel'" by(rule elim)
    then obtain Q' where QTrans: "Q \<longmapsto> \<alpha> \<prec> Q'" and Q'RelR': "(Q', R') \<in> Rel'" by blast
    from PSimQ QTrans have "\<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', Q') \<in> Rel" by(rule elim)
    then obtain P' where PTrans: "P \<longmapsto> \<alpha> \<prec> P'" and P'RelQ': "(P', Q') \<in> Rel" by blast
    from P'RelQ' Q'RelR' Trans have "(P', R') \<in> Rel''" by blast
    with PTrans show "\<exists>P'. P \<longmapsto> \<alpha> \<prec> P' \<and> (P', R') \<in> Rel''" by blast
  qed
qed

end
