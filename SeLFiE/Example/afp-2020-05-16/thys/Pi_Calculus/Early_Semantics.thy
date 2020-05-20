(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Early_Semantics
  imports Agent
begin

declare name_fresh[simp del]

nominal_datatype freeRes = InputR name name              ("_<_>" [110, 110] 110)
                         | OutputR name name             ("_[_]" [110, 110] 110)
                         | TauR                          ("\<tau>" 110)

nominal_datatype residual = BoundOutputR name "\<guillemotleft>name\<guillemotright> pi" ("_<\<nu>_> \<prec> _" [110, 110, 110] 110)
                          | FreeR freeRes pi

lemma alphaBoundOutput:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   x' :: name

  assumes A1: "x' \<sharp> P"

  shows "a<\<nu>x> \<prec> P = a<\<nu>x'> \<prec> ([(x, x')] \<bullet> P)"
proof(cases "x=x'")
  assume "x=x'"
  thus ?thesis by simp
next
  assume "x \<noteq> x'"
  with A1 show ?thesis
    by(simp add: residual.inject alpha name_fresh_left name_calc)
qed

declare name_fresh[simp]

abbreviation Transitions_Freejudge ("_ \<prec> _" [80, 80] 80) where "\<alpha> \<prec> P' \<equiv> (FreeR \<alpha> P')"

inductive "TransitionsEarly" :: "pi \<Rightarrow> residual \<Rightarrow> bool" ("_ \<longmapsto> _" [80, 80] 80)
where
  Tau:               "\<tau>.(P) \<longmapsto> \<tau> \<prec> P"
| Input:             "\<lbrakk>x \<noteq> a; x \<noteq> u\<rbrakk> \<Longrightarrow> a<x>.P \<longmapsto> a<u> \<prec> (P[x::=u])"
| Output:            "a{b}.P \<longmapsto> a[b] \<prec>  P"

| Match:             "\<lbrakk>P \<longmapsto> V\<rbrakk> \<Longrightarrow> [b\<frown>b]P \<longmapsto> V"
| Mismatch:          "\<lbrakk>P \<longmapsto> V; a \<noteq> b\<rbrakk> \<Longrightarrow> [a\<noteq>b]P \<longmapsto> V"

| Open:              "\<lbrakk>P \<longmapsto> a[b] \<prec> P'; a \<noteq> b\<rbrakk> \<Longrightarrow> <\<nu>b>P \<longmapsto> a<\<nu>b> \<prec> P'"
| Sum1:              "\<lbrakk>P \<longmapsto> V\<rbrakk> \<Longrightarrow> (P \<oplus> Q) \<longmapsto> V"
| Sum2:              "\<lbrakk>Q \<longmapsto> V\<rbrakk> \<Longrightarrow> (P \<oplus> Q) \<longmapsto> V"

| Par1B:             "\<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; x \<sharp> P; x \<sharp> Q; x \<noteq> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> a<\<nu>x> \<prec> (P' \<parallel> Q)"
| Par1F:             "\<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<alpha> \<prec> (P' \<parallel> Q)"
| Par2B:             "\<lbrakk>Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> a<\<nu>x> \<prec> (P \<parallel> Q')"
| Par2F:             "\<lbrakk>Q \<longmapsto> \<alpha> \<prec> Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<alpha> \<prec> (P \<parallel> Q')"

| Comm1:             "\<lbrakk>P \<longmapsto> a<b> \<prec> P'; Q \<longmapsto> a[b] \<prec> Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> Q'"
| Comm2:             "\<lbrakk>P \<longmapsto> a[b] \<prec> P'; Q \<longmapsto> a<b> \<prec> Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> Q'"
| Close1:            "\<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"
| Close2:            "\<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"

| ResB:              "\<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; y \<noteq> a; y \<noteq> x; x \<sharp> P; x \<noteq> a\<rbrakk> \<Longrightarrow> <\<nu>y>P \<longmapsto> a<\<nu>x> \<prec> (<\<nu>y>P')"
| ResF:              "\<lbrakk>P \<longmapsto> \<alpha> \<prec> P'; y \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> <\<nu>y>P \<longmapsto> \<alpha> \<prec> <\<nu>y>P'"

| Bang:              "\<lbrakk>P \<parallel> !P \<longmapsto> V\<rbrakk> \<Longrightarrow> !P \<longmapsto> V"

equivariance TransitionsEarly
nominal_inductive TransitionsEarly
by(auto simp add: abs_fresh fresh_fact2)

lemmas [simp] = freeRes.inject

lemma freshOutputAction:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto> a[b] \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<noteq> a" and "c \<noteq> b" and "c \<sharp> P'"
proof -
  from assms have "c \<noteq> a \<and> c \<noteq> b \<and> c \<sharp> P'"
    by(nominal_induct x2=="a[b] \<prec> P'" arbitrary: P' rule: TransitionsEarly.strong_induct) (fastforce simp add: residual.inject abs_fresh freeRes.inject)+
  thus "c \<noteq> a" and "c \<noteq> b" and "c \<sharp> P'"
    by blast+
qed

lemma freshInputAction:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto> a<b> \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<noteq> a"
using assms
by(nominal_induct x2=="a<b> \<prec> P'" arbitrary: P' rule: TransitionsEarly.strong_induct) (auto simp add: residual.inject abs_fresh)

lemma freshBoundOutputAction:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   c  :: name
  
  assumes "P \<longmapsto> a<\<nu>x> \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<noteq> a"
using assms
by(nominal_induct x2=="a<\<nu>x> \<prec> P'" avoiding: x arbitrary: P' rule: TransitionsEarly.strong_induct) (auto simp add: residual.inject abs_fresh fresh_left calc_atm dest: freshOutputAction)

lemmas freshAction = freshOutputAction freshInputAction freshBoundOutputAction

lemma freshInputTransition:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto> a<u> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<noteq> u"

  shows "c \<sharp> P'"
using assms
by(nominal_induct x2=="a<u> \<prec> P'" arbitrary: P' rule: TransitionsEarly.strong_induct)
  (fastforce simp add: residual.inject name_fresh_abs fresh_fact1 fresh_fact2)+
   
lemma freshBoundOutputTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto> a<\<nu>x> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<noteq> x"

  shows "c \<sharp> P'"
using assms
apply(nominal_induct x2=="a<\<nu>x> \<prec> P'" avoiding: x arbitrary: P' rule: TransitionsEarly.strong_induct)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(force simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction | simp | auto simp add: abs_fresh residual.inject alpha' calc_atm)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction)
apply(fastforce simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction)
apply(auto simp add: residual.inject name_fresh_abs alpha' fresh_left calc_atm dest: freshOutputAction)
apply force
done

lemma freshTauTransition:
  fixes P  :: pi
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto> \<tau> \<prec> P'"
  and     "c \<sharp> P"

  shows "c \<sharp> P'"
using assms
apply(nominal_induct x2=="\<tau> \<prec> P'" arbitrary: P' rule: TransitionsEarly.strong_induct)
by(fastforce simp add: residual.inject abs_fresh dest: freshOutputAction freshInputTransition freshBoundOutputTransition)+

lemma freshFreeTransition:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   c  :: name

  assumes "P \<longmapsto>\<alpha> \<prec> P'"
  and     "c \<sharp> P"
  and     "c \<sharp> \<alpha>"

  shows "c \<sharp> P'"
using assms
by(nominal_induct \<alpha> rule: freeRes.strong_inducts)
  (auto dest: freshInputTransition freshOutputAction freshTauTransition)

lemmas freshTransition = freshInputTransition freshOutputAction freshFreeTransition
                         freshBoundOutputTransition freshTauTransition

lemma substTrans[simp]: "b \<sharp> P \<Longrightarrow> ((P::pi)[a::=b])[b::=c] = P[a::=c]"
apply(simp add: injPermSubst[THEN sym])
apply(simp add: renaming)
by(simp add: pt_swap[OF pt_name_inst, OF at_name_inst])

lemma Input:
  fixes a :: name
  and   x :: name
  and   u :: name
  and   P :: pi

  shows "a<x>.P \<longmapsto>a<u> \<prec> P[x::=u]"
proof -
  obtain y::name where "y \<noteq> a" and "y \<noteq> u" and "y \<sharp> P"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>y \<noteq> a\<close> \<open>y \<noteq> u\<close> have "a<y>.([(x, y)] \<bullet> P) \<longmapsto>a<u> \<prec> ([(x, y)] \<bullet> P)[y::=u]"
    by(rule Input)
  with \<open>y \<sharp> P\<close> show ?thesis by(simp add: alphaInput renaming name_swap) 
qed

lemma Par1B:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi

  assumes "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and     "x \<sharp> Q"

  shows "P \<parallel> Q \<longmapsto> a<\<nu>x> \<prec> (P' \<parallel> Q)"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<noteq> a" and "y \<sharp> P'"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>P \<longmapsto>a<\<nu>x> \<prec> P'\<close> \<open>y \<sharp> P'\<close> have "P \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')"
    by(simp add: alphaBoundOutput)
  hence "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> (([(x, y)] \<bullet> P') \<parallel> Q)" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close>
    by(rule Par1B)
  with \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> P'\<close> show ?thesis
    by(subst alphaBoundOutput) (auto simp add: name_fresh_fresh)
qed

lemma Par2B:
  fixes Q  :: pi
  and   a  :: name
  and   x  :: name
  and   Q' :: pi
  and   P  :: pi

  assumes "Q \<longmapsto>a<\<nu>x> \<prec> Q'"
  and     "x \<sharp> P"

  shows "P \<parallel> Q \<longmapsto> a<\<nu>x> \<prec> (P \<parallel> Q')"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<noteq> a" and "y \<sharp> Q'"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>Q \<longmapsto>a<\<nu>x> \<prec> Q'\<close> \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q')"
    by(simp add: alphaBoundOutput)
  hence "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> (P \<parallel> ([(x, y)] \<bullet> Q'))" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close>
    by(rule Par2B)
  with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> \<open>y \<sharp> Q'\<close> show ?thesis
    by(subst alphaBoundOutput[of y]) (auto simp add: name_fresh_fresh)
qed

lemma inputInduct[consumes 1, case_names cInput cMatch cMismatch cSum1 cSum2 cPar1 cPar2 cRes cBang]:
  fixes P  :: pi
  and   a  :: name
  and   u  :: name
  and   P' :: pi
  and   F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes Trans:  "P \<longmapsto>a<u> \<prec> P'"
  and     "\<And>a x P u C. \<lbrakk>x \<sharp> C; x \<noteq> u; x \<noteq> a\<rbrakk> \<Longrightarrow> F C (a<x>.P) a u (P[x::=u])"
  and     "\<And>P a u P' b C. \<lbrakk>P \<longmapsto>a<u> \<prec> P'; \<And>C. F C P a u P'\<rbrakk> \<Longrightarrow> F C ([b\<frown>b]P) a u P'"
  and     "\<And>P a u P' b c C. \<lbrakk>P \<longmapsto>a<u> \<prec> P'; \<And>C. F C P a u P'; b\<noteq>c\<rbrakk> \<Longrightarrow> F C ([b\<noteq>c]P) a u P'"
  and     "\<And>P a u P' Q C. \<lbrakk>P \<longmapsto>a<u> \<prec> P'; \<And>C. F C P a u P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a u P'"
  and     "\<And>Q a u Q' P C. \<lbrakk>Q \<longmapsto>a<u> \<prec> Q'; \<And>C. F C Q a u Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a u Q'"
  and     "\<And>P a u P' Q C. \<lbrakk>P \<longmapsto>a<u> \<prec> P'; \<And>C. F C P a u P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a u (P' \<parallel> Q)"
  and     "\<And>Q a u Q' P C. \<lbrakk>Q \<longmapsto>a<u> \<prec> Q'; \<And>C. F C Q a u Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a u (P \<parallel> Q')"
  and     "\<And>P a u P' x C. \<lbrakk>P \<longmapsto>a<u> \<prec> P'; x \<noteq> a; x \<noteq> u; x \<sharp> C; \<And>C. F C P a u P'\<rbrakk> \<Longrightarrow> F C (<\<nu>x>P) a u (<\<nu>x>P')"
  and     "\<And>P a u P' C. \<lbrakk>P \<parallel> !P \<longmapsto>a<u> \<prec> P'; \<And>C. F C (P \<parallel> !P) a u P'\<rbrakk> \<Longrightarrow> F C (!P) a u P'"

  shows "F C P a u P'"
using assms
by(nominal_induct x2=="a<u> \<prec> P'" avoiding: C arbitrary: P' rule: TransitionsEarly.strong_induct)
  (auto simp add: residual.inject)

lemma inputAlpha:
  assumes "P \<longmapsto>a<u> \<prec> P'"
  and     "u \<sharp> P"
  and     "r \<sharp> P'"

  shows "P \<longmapsto>a<r> \<prec> ([(u, r)] \<bullet> P')"
using assms
proof(nominal_induct avoiding: r rule: inputInduct)
  case(cInput a x P u r)
  from \<open>x \<noteq> u\<close> \<open>u \<sharp> a<x>.P\<close>have "u \<noteq> a" and "u \<sharp> P" by(simp add: abs_fresh)+
  have "a<x>.P \<longmapsto>a<r> \<prec> P[x::=r]"
    by(rule Input)
  thus ?case using \<open>r \<sharp> P[x::=u]\<close> \<open>u \<sharp> P\<close>
    by(simp add: injPermSubst substTrans)
next
  case(cMatch P a u P' b r)
  thus ?case by(force intro: Match) 
next
  case(cMismatch P a u P' b c r)
  thus ?case by(force intro: Mismatch)
next
  case(cSum1 P a u P' Q r)
  thus ?case by(force intro: Sum1)
next
  case(cSum2 Q a u Q' P r)
  thus ?case by(force intro: Sum2)
next
  case(cPar1 P a u P' Q r)
  thus ?case by(force intro: Par1F simp add: eqvts name_fresh_fresh) 
next
  case(cPar2 Q a u Q' P r)
  thus ?case by(force intro: Par2F simp add: eqvts name_fresh_fresh) 
next
  case(cRes P a u P' x r)
  thus ?case by(force intro: ResF simp add: eqvts calc_atm abs_fresh) 
next
  case(cBang P a u P' R)
  thus ?case by(force intro: Bang)
qed

lemma Close1:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi

  assumes "P \<longmapsto>a<x> \<prec> P'"
  and     "Q \<longmapsto>a<\<nu>x> \<prec> Q'"
  and     "x \<sharp> P"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<noteq> a" and "y \<sharp> Q'" and "y \<sharp> P'"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>P \<longmapsto>a<x> \<prec> P'\<close> \<open>x \<sharp> P\<close> \<open>y \<sharp> P'\<close> have "P \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P')"
    by(rule inputAlpha)
  moreover from \<open>Q \<longmapsto>a<\<nu>x> \<prec> Q'\<close> \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> Q')"
    by(simp add: alphaBoundOutput)
  
  ultimately have "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close>
    by(rule Close1)
  with \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> show ?thesis by(subst alphaRes) (auto simp add: name_fresh_fresh)
qed

lemma Close2:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   Q' :: pi

  assumes "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and     "Q \<longmapsto>a<x> \<prec> Q'"
  and     "x \<sharp> Q"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>x>(P' \<parallel> Q')"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<noteq> a" and "y \<sharp> Q'" and "y \<sharp> P'"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>P \<longmapsto>a<\<nu>x> \<prec> P'\<close> \<open>y \<sharp> P'\<close> have "P \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')"
    by(simp add: alphaBoundOutput)
  moreover from \<open>Q \<longmapsto>a<x> \<prec> Q'\<close> \<open>x \<sharp> Q\<close> \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> Q')"
    by(rule inputAlpha)
  
  ultimately have "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(([(x, y)] \<bullet> P') \<parallel> ([(x, y)] \<bullet> Q'))" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close>
    by(rule Close2)
  with \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q'\<close> show ?thesis by(subst alphaRes) (auto simp add: name_fresh_fresh)
qed

lemma ResB:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   y  :: name

  assumes "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and     "y \<noteq> a"
  and     "y \<noteq> x"

  shows "<\<nu>y>P \<longmapsto>a<\<nu>x> \<prec> (<\<nu>y>P')"
proof -
  obtain z :: name where "z \<sharp> P" and "z \<sharp> P'" and "z \<noteq> a" and "z \<noteq> y"
    by(generate_fresh "name") (auto simp add: fresh_prod)
  from \<open>P \<longmapsto>a<\<nu>x> \<prec> P'\<close> \<open>z \<sharp> P'\<close> have "P \<longmapsto>a<\<nu>z> \<prec> ([(x, z)] \<bullet> P')"
    by(simp add: alphaBoundOutput)
  hence "<\<nu>y>P \<longmapsto>a<\<nu>z> \<prec> (<\<nu>y>([(x, z)] \<bullet> P'))" using \<open>y \<noteq> a\<close> \<open>z \<noteq> y\<close> \<open>z \<sharp> P\<close> \<open>z \<noteq> a\<close>
    by(rule_tac ResB) auto
  thus ?thesis using \<open>z \<noteq> y\<close> \<open>y \<noteq> x\<close> \<open>z \<sharp> P'\<close>
    by(subst alphaBoundOutput[where x'=z]) (auto simp add: eqvts calc_atm abs_fresh)
qed

lemma outputInduct[consumes 1, case_names Output Match Mismatch Sum1 Sum2 Par1 Par2 Res Bang]:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes Trans:  "P \<longmapsto>a[b] \<prec> P'"
  and     "\<And>a b P C. F C (a{b}.P) a b P"
  and     "\<And>P a b P' c C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow> F C ([c\<frown>c]P) a b P'"
  and     "\<And>P a b P' c d C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'; c\<noteq>d\<rbrakk> \<Longrightarrow> F C ([c\<noteq>d]P) a b P'"
  and     "\<And>P a b P' Q C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a b P'"
  and     "\<And>Q a b Q' P C. \<lbrakk>Q \<longmapsto>OutputR a b \<prec> Q'; \<And>C. F C Q a b Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a b Q'"
  and     "\<And>P a b P' Q C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a b (P' \<parallel> Q)"
  and     "\<And>Q a b Q' P C. \<lbrakk>Q \<longmapsto>OutputR a b \<prec> Q'; \<And>C. F C Q a b Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a b (P \<parallel> Q')"
  and     "\<And>P a b P' x C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; x \<noteq> a; x \<noteq> b; x \<sharp> C; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow>
                            F C (<\<nu>x>P) a b (<\<nu>x>P')"
  and     "\<And>P a b P' C. \<lbrakk>P \<parallel> !P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C (P \<parallel> !P) a b P'\<rbrakk> \<Longrightarrow> F C (!P) a b P'"

  shows "F C P a b P'"
using assms
by(nominal_induct x2=="a[b] \<prec> P'" avoiding: C arbitrary: P' rule: TransitionsEarly.strong_induct)
  (auto simp add: residual.inject)

lemma boundOutputInduct[consumes 2, case_names Match Mismatch Open Sum1 Sum2 Par1 Par2 Res Bang]:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   F  :: "('a::fs_name) \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes a: "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and     xFreshP:  "x \<sharp> P"
  and     cMatch:   "\<And>P a x P' b C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C ([b\<frown>b]P) a x P'"
  and     cMismatch:   "\<And>P a x P' b c C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'; b \<noteq> c\<rbrakk> \<Longrightarrow> F C ([b\<noteq>c]P) a x P'"
  and     cOpen:    "\<And>P a x P' C.   \<lbrakk>P \<longmapsto>(OutputR a x) \<prec> P'; a \<noteq> x\<rbrakk> \<Longrightarrow> F C (<\<nu>x>P) a x P'"
  and     cSum1:    "\<And>P Q a x P' C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x P'" 
  and     cSum2:    "\<And>P Q a x Q' C. \<lbrakk>Q \<longmapsto>a<\<nu>x> \<prec> Q'; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x Q'" 
  and     cPar1B:   "\<And>P P' Q a x C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; x \<sharp> Q; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow>
                                  F C (P \<parallel> Q) a x (P' \<parallel> Q)" 
  and     cPar2B:   "\<And>P Q Q' a x C. \<lbrakk>Q \<longmapsto>a<\<nu>x> \<prec> Q'; x \<sharp> P; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow>
                                  F C (P \<parallel> Q) a x (P \<parallel> Q')"
  and     cResB:    "\<And>P P' a x y C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; y \<noteq> a; y \<noteq> x; y \<sharp> C;
                                      \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (<\<nu>y>P) a x (<\<nu>y>P')"
  and     cBang:    "\<And>P a x P' C. \<lbrakk>P \<parallel> !P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C (P \<parallel> !P) a x P'\<rbrakk> \<Longrightarrow>
                                    F C (!P) a x P'"
  shows "F C P a x P'"
using assms
proof -
  have Goal: "\<And>P Rs a x P' C. \<lbrakk>P \<longmapsto> Rs; Rs = a<\<nu>x> \<prec> P'; x \<sharp> P\<rbrakk> \<Longrightarrow> F C P a x P'"
  proof -
    fix P Rs a x P' C
    assume "P \<longmapsto> Rs" and "Rs = a<\<nu>x> \<prec> P'" and "x \<sharp> P"
    thus "F C P a x P'"
    proof(nominal_induct avoiding: C a x P' rule: TransitionsEarly.strong_induct)
      case(Tau P)
      thus ?case by(simp add: residual.inject)
    next
      case(Input P a x)
      thus ?case by(simp add: residual.inject)
    next
      case(Output P a b)
      thus ?case by(simp add: residual.inject)
    next
      case(Match P Rs b C a x P')
      thus ?case 
        by(force intro: cMatch simp add: residual.inject) 
    next
      case(Mismatch P Rs b c C a x P')
      thus ?case 
        by(force intro: cMismatch simp add: residual.inject) 
    next
      case(Sum1 P Q Rs C)
      thus ?case by(force intro: cSum1)
    next
      case(Sum2 P Q Rs C)
      thus ?case by(force intro: cSum2)
    next
      case(Open P a b P' C a' x P'')
      have "b \<sharp> x" by fact hence bineqx: "b \<noteq> x" by simp
      moreover have "a<\<nu>b> \<prec> P' = a'<\<nu>x> \<prec> P''" by fact
      ultimately have aeqa': "a=a'" and P'eqP'': "P'' = [(b, x)] \<bullet> P'"
        by(simp add: residual.inject name_abs_eq)+
      have "x \<sharp> <\<nu>b>P" by fact 
      with bineqx have xFreshP: "x \<sharp> P" by(simp add: name_fresh_abs)
      have aineqb: "a \<noteq> b" by fact

      have PTrans: "P \<longmapsto>a[b] \<prec> P'" by fact
      with xFreshP have xineqa: "x \<noteq> a" by(force dest: freshAction)
      from PTrans have "([(b, x)] \<bullet> P) \<longmapsto>[(b, x)] \<bullet> (a[b] \<prec> P')" by(rule TransitionsEarly.eqvt)
      with P'eqP'' xineqa aineqb have Trans: "([(b, x)] \<bullet> P) \<longmapsto>a[x] \<prec> P''"
        by(auto simp add: name_calc)
      hence "F C (<\<nu>x>([(b, x)] \<bullet> P)) a x P''" using xineqa by(blast intro: cOpen)
      with xFreshP aeqa' show ?case by(simp add: alphaRes)
    next
      case(Par1B P  a x P' Q C a' x' P'')
      have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
      moreover have Eq: "a<\<nu>x> \<prec> (P' \<parallel> Q) = a'<\<nu>x'> \<prec> P''" by fact
      hence aeqa': "a = a'" by(simp add: residual.inject)
      have xFreshQ: "x \<sharp> Q" by fact
      have "x' \<sharp> P \<parallel> Q" by fact
      hence x'FreshP: "x' \<sharp> P" and x'FreshQ: "x' \<sharp> Q" by simp+
      have P''eq: "P'' = ([(x, x')] \<bullet> P') \<parallel> Q"
      proof -
        from Eq xineqx' have "(P' \<parallel> Q) = [(x, x')] \<bullet> P''"
          by(simp add: residual.inject name_abs_eq)
        hence "([(x, x')] \<bullet> (P' \<parallel> Q)) = P''" by simp
        with x'FreshQ xFreshQ show ?thesis by(simp add: name_fresh_fresh)
      qed

      have "x \<sharp> P''" by fact
      with P''eq have x'FreshP': "x' \<sharp> P'" by(simp add: name_fresh_left name_calc)

      have "P \<longmapsto>a<\<nu>x> \<prec> P'" by fact
      with x'FreshP' aeqa' have "P \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: alphaBoundOutput)
      moreover have "\<And>C. F C P a x' ([(x, x')] \<bullet> P')"
      proof -
        fix C
        have "\<And>C a' x' P''. \<lbrakk>a<\<nu>x> \<prec> P' = a'<\<nu>x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
        moreover with aeqa' xineqx' x'FreshP' have "a<\<nu>x> \<prec> P' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
          by(simp add: residual.inject name_abs_eq name_fresh_left name_calc)
        ultimately show "F C P a x' ([(x, x')] \<bullet> P')" using x'FreshP aeqa' by blast 
      qed
      ultimately have "F C (P \<parallel> Q) a' x' (([(x, x')] \<bullet> P') \<parallel> Q)" using x'FreshQ aeqa'
        by(blast intro: cPar1B)
      with P''eq show ?case by simp
    next
      case(Par1F P P' Q \<alpha>)
      thus ?case by(simp add: residual.inject)
    next
      case(Par2B Q a x Q' P C a' x' Q'')
      have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
      moreover have Eq: "a<\<nu>x> \<prec> (P \<parallel> Q') = a'<\<nu>x'> \<prec> Q''" by fact
      hence aeqa': "a = a'" by(simp add: residual.inject)
      have xFreshP: "x \<sharp> P" by fact
      have "x' \<sharp> P \<parallel> Q" by fact
      hence x'FreshP: "x' \<sharp> P" and x'FreshQ: "x' \<sharp> Q" by simp+
      have Q''eq: "Q'' = P \<parallel> ([(x, x')] \<bullet> Q')"
      proof -
        from Eq xineqx' have "(P \<parallel> Q') = [(x, x')] \<bullet> Q''"
          by(simp add: residual.inject name_abs_eq)
        hence "([(x, x')] \<bullet> (P \<parallel> Q')) = Q''" by simp
        with x'FreshP xFreshP show ?thesis by(simp add: name_fresh_fresh)
      qed

      have "x \<sharp> Q''" by fact
      with Q''eq have x'FreshQ': "x' \<sharp> Q'" by(simp add: name_fresh_left name_calc)

      have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
      with x'FreshQ' aeqa' have "Q \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> Q')"
        by(simp add: alphaBoundOutput)
      moreover have "\<And>C. F C Q a x' ([(x, x')] \<bullet> Q')"
      proof -
        fix C
        have "\<And>C a' x' Q''. \<lbrakk>a<\<nu>x> \<prec> Q' = a'<\<nu>x'> \<prec> Q''; x' \<sharp> Q\<rbrakk> \<Longrightarrow> F C Q a' x' Q''" by fact
        moreover with aeqa' xineqx' x'FreshQ' have "a<\<nu>x> \<prec> Q' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> Q')"
          by(simp add: residual.inject name_abs_eq name_fresh_left name_calc)
        ultimately show "F C Q a x' ([(x, x')] \<bullet> Q')" using x'FreshQ aeqa' by blast 
      qed
      ultimately have "F C (P \<parallel> Q) a' x' (P \<parallel> ([(x, x')] \<bullet> Q'))" using x'FreshP aeqa'
        by(blast intro: cPar2B)
      with Q''eq show ?case by simp
    next
      case(Par2F P P' Q \<alpha>)
      thus ?case by(simp add: residual.inject)
    next
      case(Comm1 P P' Q Q' a b x)
      thus ?case by(simp add: residual.inject)
    next
      case(Comm2 P P' Q Q' a b x)
      thus ?case by(simp add: residual.inject)
    next
      case(Close1 P P' Q Q' a x y)
      thus ?case by(simp add: residual.inject)
    next
      case(Close2 P P' Q Q' a x y)
      thus ?case by(simp add: residual.inject)
    next
      case(ResB P a x P' y C a' x' P'')
      have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
      moreover have Eq: "a<\<nu>x> \<prec> (<\<nu>y>P') = a'<\<nu>x'> \<prec> P''" by fact
      hence aeqa': "a = a'" by(simp add: residual.inject)
      have "y \<sharp> x'" by fact hence yineqx': "y \<noteq> x'" by simp
      moreover have "x' \<sharp> <\<nu>y>P" by fact
      ultimately have x'FreshP: "x' \<sharp> P" by(simp add: name_fresh_abs)
      have yineqx: "y \<noteq> x" and yineqa: "y \<noteq> a" and yFreshC: "y \<sharp> C" by fact+

      have P''eq: "P'' = <\<nu>y>([(x, x')] \<bullet> P')"
      proof -
        from Eq xineqx' have "<\<nu>y>P' = [(x, x')] \<bullet> P''"
          by(simp add: residual.inject name_abs_eq)
        hence "([(x, x')] \<bullet> (<\<nu>y>P')) = P''" by simp
        with yineqx' yineqx show ?thesis by(simp add: name_fresh_fresh)
      qed

      have "x \<sharp> P''" by fact
      with P''eq yineqx  have x'FreshP': "x' \<sharp> P'" by(simp add: name_fresh_left name_calc name_fresh_abs)

      have "P \<longmapsto>a<\<nu>x> \<prec> P'" by fact
      with x'FreshP' aeqa' have "P \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: alphaBoundOutput)
      moreover have "\<And>C. F C P a x' ([(x, x')] \<bullet> P')"
      proof -
        fix C
        have "\<And>C a' x' P''. \<lbrakk>a<\<nu>x> \<prec> P' = a'<\<nu>x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
        moreover with aeqa' xineqx' x'FreshP' have "a<\<nu>x> \<prec> P' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
          by(simp add: residual.inject name_abs_eq name_fresh_left name_calc)
        ultimately show "F C P a x' ([(x, x')] \<bullet> P')" using x'FreshP aeqa' by blast 
      qed
      ultimately have "F C (<\<nu>y>P) a' x' (<\<nu>y>([(x, x')] \<bullet> P'))" using yineqx' yineqa yFreshC aeqa'
        by(force intro: cResB)
      with P''eq show ?case by simp
    next
      case(ResF P P' \<alpha> y)
      thus ?case by(simp add: residual.inject)
    next
      case(Bang P Rs)
      thus ?case by(force intro: cBang)
    qed
  qed
    
  with a xFreshP show ?thesis by simp
qed

lemma tauInduct[consumes 1, case_names Tau Match Mismatch Sum1 Sum2 Par1 Par2 Comm1 Comm2 Close1 Close2 Res Bang]:
  fixes P  :: pi
  and   P' :: pi
  and   F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes Trans:  "P \<longmapsto>\<tau> \<prec> P'"
  and     "\<And>P C. F C (\<tau>.(P)) P"
  and     "\<And>P P' a C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C ([a\<frown>a]P) P'"
  and     "\<And>P P' a b C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'; a \<noteq> b\<rbrakk> \<Longrightarrow> F C ([a\<noteq>b]P) P'"
  and     "\<And>P P' Q C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) P'"
  and     "\<And>Q Q' P C. \<lbrakk>Q \<longmapsto>\<tau> \<prec> Q'; \<And>C. F C Q Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) Q'"
  and     "\<And>P P' Q C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P' \<parallel> Q)"
  and     "\<And>Q Q' P C. \<lbrakk>Q \<longmapsto>\<tau> \<prec> Q'; \<And>C. F C Q Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P \<parallel> Q')"
  and     "\<And>P a b P' Q Q' C. \<lbrakk>P \<longmapsto>a<b> \<prec> P'; Q \<longmapsto>OutputR a b \<prec> Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P' \<parallel> Q')"
  and     "\<And>P a b P' Q Q' C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; Q \<longmapsto>a<b> \<prec> Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P' \<parallel> Q')"
  and     "\<And>P a x P' Q Q' C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; Q \<longmapsto>a<\<nu>x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<sharp> C\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (<\<nu>x>(P' \<parallel> Q'))"
  and     "\<And>P a x P' Q Q' C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; Q \<longmapsto>a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<sharp> C\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (<\<nu>x>(P' \<parallel> Q'))"
  and     "\<And>P P' x C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; x \<sharp> C; \<And>C. F C P P'\<rbrakk> \<Longrightarrow>
                        F C (<\<nu>x>P) (<\<nu>x>P')"
  and     "\<And>P P' C. \<lbrakk>P \<parallel> !P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C (P \<parallel> !P) P'\<rbrakk> \<Longrightarrow> F C (!P) P'"

  shows "F C P P'"
using \<open>P \<longmapsto>\<tau> \<prec> P'\<close>
by(nominal_induct x2=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: TransitionsEarly.strong_induct)
  (auto simp add: residual.inject intro: assms)+

inductive bangPred :: "pi \<Rightarrow> pi \<Rightarrow> bool"
where
  aux1: "bangPred P (!P)"
| aux2: "bangPred P (P \<parallel> !P)"

inductive_cases tauCases'[simplified pi.distinct residual.distinct]: "\<tau>.(P) \<longmapsto> Rs"
inductive_cases inputCases'[simplified pi.inject residual.inject]: "a<b>.P \<longmapsto> Rs"
inductive_cases outputCases'[simplified pi.inject residual.inject]: "a{b}.P \<longmapsto> Rs"
inductive_cases matchCases'[simplified pi.inject residual.inject]: "[a\<frown>b]P \<longmapsto> Rs"
inductive_cases mismatchCases'[simplified pi.inject residual.inject]: "[a\<noteq>b]P \<longmapsto> Rs"
inductive_cases sumCases'[simplified pi.inject residual.inject]: "P \<oplus> Q \<longmapsto> Rs"
inductive_cases parCasesB'[simplified pi.distinct residual.distinct]: "A \<parallel> B \<longmapsto> b<\<nu>y> \<prec> A'"
inductive_cases parCasesF'[simplified pi.distinct residual.distinct]: "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P'"
inductive_cases resCasesB'[simplified pi.distinct residual.distinct]: "<\<nu>x'>A \<longmapsto> a<\<nu>y'> \<prec> A'"
inductive_cases resCasesF'[simplified pi.distinct residual.distinct]: "<\<nu>x>A \<longmapsto> \<alpha> \<prec> A'"

lemma tauCases:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "\<tau>.(P) \<longmapsto>\<alpha> \<prec> P'"
  and     "Prop (\<tau>) P"

  shows "Prop \<alpha> P'"
using assms
by(cases rule: tauCases') (auto simp add: pi.inject residual.inject)

lemma inputCases[consumes 1, case_names cInput]:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   P' :: pi

  assumes Input: "a<x>.P \<longmapsto>\<alpha> \<prec> P'"
  and     A: "\<And>u. Prop (a<u>) (P[x::=u])"

  shows "Prop \<alpha> P'"
proof -
  {
    fix x P
    assume "a<x>.P \<longmapsto>\<alpha> \<prec> P'"
    moreover assume "(x::name) \<sharp> \<alpha>" and "x \<sharp> P'" and "x \<noteq> a"
    moreover assume "\<And>u. Prop (a<u>) (P[x::=u])"
    moreover obtain z::name where "z \<noteq> x" and "z \<sharp> P" and "z \<sharp> \<alpha>" and "z \<sharp> P'"  and "z \<noteq> a"
      by(generate_fresh "name", auto simp add: fresh_prod)
    moreover obtain z'::name where "z' \<noteq> x" and "z' \<noteq> z" and "z' \<sharp> P" and "z' \<sharp> \<alpha>" and "z' \<sharp> P'" and "z' \<noteq> a"
      by(generate_fresh "name", auto simp add: fresh_prod)
    ultimately have "Prop \<alpha> P'"
      by(cases rule: TransitionsEarly.strong_cases[where x=x and b=z and xa=z and xb=z and xc=z and xd=z and xe=z
                                                   and y=z' and ya=z'])
        (auto simp add: pi.inject residual.inject abs_fresh alpha)
   }
   note Goal = this
   obtain y::name where "y \<sharp> P" and "y \<sharp> \<alpha>" and "y \<sharp> P'" and "y \<noteq> a"
     by(generate_fresh "name") (auto simp add: fresh_prod)
   from Input \<open>y \<sharp> P\<close> have "a<y>.([(x, y)] \<bullet> P) \<longmapsto>\<alpha> \<prec> P'" by(simp add: alphaInput)
   moreover note \<open>y \<sharp> \<alpha>\<close> \<open>y \<sharp> P'\<close> \<open>y \<noteq> a\<close>
   moreover from A \<open>y \<sharp> P\<close> have "\<And>u. Prop (a<u>) (([(x, y)] \<bullet> P)[y::=u])"
     by(simp add: renaming name_swap)
   ultimately show ?thesis by(rule Goal)
qed

lemma outputCases:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>\<alpha> \<prec> P'"
  and     "Prop (OutputR a b) P"

  shows "Prop \<alpha> P'"
using assms
by(cases rule: outputCases') (auto simp add: pi.inject residual.inject)

lemma zeroTrans[dest]:
  fixes Rs :: residual

  assumes "\<zero> \<longmapsto> e Rs"

  shows "False"
using assms
by - (ind_cases "\<zero> \<longmapsto> e Rs")

lemma mismatchTrans[dest]:
  fixes a   :: name
  and   P   :: pi
  and   Rs  :: residual

  assumes "[a\<noteq>a]P \<longmapsto> Rs"

  shows "False"
using assms
by(erule_tac mismatchCases') auto

lemma matchCases[consumes 1, case_names Match]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   Rs :: residual
  and   F  :: "name \<Rightarrow> name \<Rightarrow> bool"

  assumes Trans:  "[a\<frown>b]P \<longmapsto> Rs"
  and     cMatch: "P \<longmapsto> Rs \<Longrightarrow> F a a"

  shows "F a b"
using assms
by(erule_tac matchCases', auto)

lemma mismatchCases[consumes 1, case_names Mismatch]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   Rs :: residual
  and   F  :: "name \<Rightarrow> name \<Rightarrow> bool"

  assumes Trans:  "[a\<noteq>b]P \<longmapsto> Rs"
  and     cMatch: "\<lbrakk>P \<longmapsto> Rs; a \<noteq> b\<rbrakk> \<Longrightarrow> F a b"

  shows "F a b"
using assms  
by(erule_tac mismatchCases') auto

lemma sumCases[consumes 1, case_names Sum1 Sum2]:
  fixes P  :: pi
  and   Q  :: pi
  and   Rs :: residual

  assumes Trans: "P \<oplus> Q \<longmapsto> Rs"
  and     cSum1: "P \<longmapsto> Rs \<Longrightarrow> F"
  and     cSum2: "Q \<longmapsto> Rs \<Longrightarrow> F"

  shows F
using assms
by(erule_tac sumCases') auto

lemma parCasesB[consumes 1, case_names cPar1 cPar2]:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: name
  and   x   :: name
  and   PQ' :: pi
  
  assumes Trans: "P \<parallel> Q \<longmapsto> a<\<nu>x> \<prec> PQ'"
  and     icPar1B: "\<And>P'. \<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; x \<sharp> Q\<rbrakk> \<Longrightarrow> F (P' \<parallel> Q)"
  and     icPar2B: "\<And>Q'. \<lbrakk>Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P\<rbrakk> \<Longrightarrow> F (P \<parallel> Q')"

  shows "F PQ'"
proof -
  from Trans show ?thesis
  proof(induct rule: parCasesB', auto simp add: pi.inject residual.inject)
    fix P' y
    assume PTrans: "P \<longmapsto> a<\<nu>y> \<prec> P'"
    assume yFreshQ: "y \<sharp> (Q::pi)"
    assume absEq: "[x].PQ' = [y].(P' \<parallel> Q)"

    have "\<exists>c::name. c \<sharp> (P', x, y, Q)" by(blast intro: name_exists_fresh)
    then obtain c where cFreshP': "c \<sharp> P'" and cineqx: "x \<noteq> c" and cineqy: "c \<noteq> y" and cFreshQ: "c \<sharp> Q"
      by(force simp add: fresh_prod name_fresh)

    from cFreshP' PTrans have Trans: "P \<longmapsto> a<\<nu>c> \<prec> ([(y, c)] \<bullet> P')" by(simp add: alphaBoundOutput)

    from cFreshP' cFreshQ have "c \<sharp> P' \<parallel> Q" by simp
    hence "[y].(P' \<parallel> Q) = [c].([(y, c)] \<bullet> (P' \<parallel> Q))"
      by(auto simp add: alpha fresh_left calc_atm)
    with yFreshQ cFreshQ have "[y].(P' \<parallel> Q) = [c].(([(y, c)] \<bullet> P') \<parallel> Q)"
      by(simp add: name_fresh_fresh)

    with cineqx absEq have L1: "PQ' = [(x, c)] \<bullet> (([(y, c)] \<bullet> P') \<parallel> Q)" and L2: "x \<sharp> ([(y, c)] \<bullet> P') \<parallel> Q"
      by(simp add: name_abs_eq)+
    
    from L2 have xFreshQ: "x \<sharp> Q" and xFreshP': "x \<sharp> [(y, c)] \<bullet> P'" by simp+
    with cFreshQ L1 have L3: "PQ' = ([(x, c)] \<bullet> [(y, c)] \<bullet> P') \<parallel> Q" by(simp add: name_fresh_fresh)

    from Trans xFreshP' have "P \<longmapsto> a<\<nu>x> \<prec> ([(x, c)] \<bullet> [(y, c)] \<bullet> P')" by(simp add: alphaBoundOutput name_swap)

    thus ?thesis using xFreshQ L3
      by(blast intro: icPar1B)
  next
    fix Q' y
    assume QTrans: "Q \<longmapsto> a<\<nu>y> \<prec> Q'"
    assume yFreshP: "y \<sharp> (P::pi)"
    assume absEq: "[x].PQ' = [y].(P \<parallel> Q')"

    have "\<exists>c::name. c \<sharp> (Q', x, y, P)" by(blast intro: name_exists_fresh)
    then obtain c where cFreshQ': "c \<sharp> Q'" and cineqx: "x \<noteq> c" and cineqy: "c \<noteq> y" and cFreshP: "c \<sharp> P"
      by(force simp add: fresh_prod name_fresh)

    from cFreshQ' QTrans have Trans: "Q \<longmapsto> a<\<nu>c> \<prec> ([(y, c)] \<bullet> Q')" by(simp add: alphaBoundOutput)

    from cFreshQ' cFreshP have "c \<sharp> P \<parallel> Q'" by simp
    hence "[y].(P \<parallel> Q') = [c].([(y, c)] \<bullet> (P \<parallel> Q'))"
      by(auto simp add: alpha fresh_left calc_atm)
    with yFreshP cFreshP have "[y].(P \<parallel> Q') = [c].(P \<parallel> ([(y, c)] \<bullet> Q'))"
      by(simp add: name_fresh_fresh)

    with cineqx absEq have L1: "PQ' = [(x, c)] \<bullet> (P \<parallel> ([(y, c)] \<bullet> Q'))" and L2: "x \<sharp> P \<parallel> ([(y, c)] \<bullet> Q')"
      by(simp add: name_abs_eq)+
    
    from L2 have xFreshP: "x \<sharp> P" and xFreshQ': "x \<sharp> [(y, c)] \<bullet> Q'" by simp+
    with cFreshP L1 have L3: "PQ' = P \<parallel> ([(x, c)] \<bullet> [(y, c)] \<bullet> Q')" by(simp add: name_fresh_fresh)

    from Trans xFreshQ' have "Q \<longmapsto> a<\<nu>x> \<prec> ([(x, c)] \<bullet> [(y, c)] \<bullet> Q')" by(simp add: alphaBoundOutput name_swap)

    thus ?thesis using xFreshP L3
      by(blast intro: icPar2B)
  qed
qed

lemma parCasesOutput[consumes 1, case_names Par1 Par2]:
  fixes P  :: pi
  and   Q  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "P \<parallel> Q \<longmapsto>a[b] \<prec> PQ'"
  and     "\<And>P'. \<lbrakk>P \<longmapsto>a[b] \<prec> P'\<rbrakk> \<Longrightarrow> F (P' \<parallel> Q)"
  and     "\<And>Q'. \<lbrakk>Q \<longmapsto>a[b] \<prec> Q'\<rbrakk> \<Longrightarrow> F (P \<parallel> Q')"

  shows "F PQ'"
using assms
by(erule_tac parCasesF', auto simp add: pi.inject residual.inject)

lemma parCasesInput[consumes 1, case_names Par1 Par2]:
  fixes P  :: pi
  and   Q  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes Trans: "P \<parallel> Q \<longmapsto>a<b> \<prec> PQ'"
  and     icPar1F: "\<And>P'. \<lbrakk>P \<longmapsto>a<b> \<prec> P'\<rbrakk> \<Longrightarrow> F (P' \<parallel> Q)"
  and     icPar2F: "\<And>Q'. \<lbrakk>Q \<longmapsto>a<b> \<prec> Q'\<rbrakk> \<Longrightarrow> F (P \<parallel> Q')"

  shows "F PQ'"
using assms
by(erule_tac parCasesF') (auto simp add: pi.inject residual.inject)

lemma parCasesF[consumes 1, case_names cPar1 cPar2 cComm1 cComm2 cClose1 cClose2]:
  fixes P  :: pi
  and   Q  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes Trans: "P \<parallel> Q \<longmapsto> \<alpha> \<prec> PQ'"
  and     icPar1F: "\<And>P'. \<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> F \<alpha> (P' \<parallel> Q)"
  and     icPar2F: "\<And>Q'. \<lbrakk>Q \<longmapsto> \<alpha> \<prec> Q'\<rbrakk> \<Longrightarrow> F \<alpha> (P \<parallel> Q')"
  and     icComm1: "\<And>P' Q' a b. \<lbrakk>P \<longmapsto> a<b> \<prec> P'; Q \<longmapsto> a[b] \<prec> Q'\<rbrakk> \<Longrightarrow> F (\<tau>) (P' \<parallel> Q')"
  and     icComm2: "\<And>P' Q' a b. \<lbrakk>P \<longmapsto> a[b] \<prec> P'; Q \<longmapsto> a<b> \<prec> Q'\<rbrakk> \<Longrightarrow> F (\<tau>) (P' \<parallel> Q')"
  and     icClose1: "\<And>P' Q' a x. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a<\<nu>x> \<prec> Q'; x \<sharp> P; x \<sharp> C\<rbrakk> \<Longrightarrow> F (\<tau>) (<\<nu>x>(P' \<parallel> Q'))"
  and     icClose2: "\<And>P' Q' a x. \<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> Q; x \<sharp> C\<rbrakk> \<Longrightarrow> F (\<tau>) (<\<nu>x>(P' \<parallel> Q'))"

  shows "F \<alpha> PQ'"
proof -
  from Trans show ?thesis
  proof(rule parCasesF', auto)
    fix Pa Pa' Qa \<alpha>'
    assume Trans': "Pa \<longmapsto> \<alpha>' \<prec> Pa'"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<alpha>' \<prec> Pa' \<parallel> Qa"

    from Eq have "P = Pa" and "Q = Qa"
      by(simp add: pi.inject)+
    
    moreover with Eq' have "\<alpha> = \<alpha>'" and "PQ' = Pa' \<parallel> Q"
      by(simp add: residual.inject)+

    ultimately show ?thesis using icPar1F Trans'
      by simp
  next
    fix Pa Qa Qa' \<alpha>'
    assume Trans': "Qa \<longmapsto> \<alpha>' \<prec> Qa'"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<alpha>' \<prec> Pa \<parallel> Qa'"

    from Eq have "P = Pa" and "Q = Qa"
      by(simp add: pi.inject)+
    
    moreover with Eq' have "\<alpha> = \<alpha>'" and "PQ' = P \<parallel> Qa'"
      by(simp add: residual.inject)+

    ultimately show ?thesis using icPar2F Trans'
      by simp
  next
    fix Pa Pa' Qa Qa' a b
    assume TransP: "Pa \<longmapsto> a<b> \<prec> Pa'"
    assume TransQ: "Qa \<longmapsto> a[b] \<prec> Qa'"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<tau> \<prec> Pa' \<parallel> Qa'"

    from TransP TransQ Eq Eq' icComm1 show ?thesis
      by(simp add: pi.inject residual.inject)
  next
    fix Pa Pa' Qa Qa' a b x
    assume TransP: "Pa \<longmapsto> (a::name)[b] \<prec> Pa'"
    assume TransQ: "Qa \<longmapsto> a<b> \<prec> Qa'"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<tau> \<prec> Pa' \<parallel> Qa'"

    from TransP TransQ Eq Eq' icComm2 show ?thesis
      by(simp add: pi.inject residual.inject)
  next
    fix Pa Pa' Qa Qa' a x
    assume TransP: "Pa \<longmapsto> a<x> \<prec> Pa'"
    assume TransQ: "Qa \<longmapsto> a<\<nu>x> \<prec> Qa'"
    assume xFreshPa: "x \<sharp> Pa"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<tau> \<prec> <\<nu>x>(Pa' \<parallel> Qa')"

    have "\<exists>(c::name). c \<sharp> (Pa, Pa', x, Qa', a, C)"
      by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshPa: "c \<sharp> Pa" and cFreshPa': "c \<sharp> Pa'" and cineqy: "c \<noteq> x" and cFreshQa': "c \<sharp> Qa'" and cFreshC: "c \<sharp> C" and cineqa: "c \<noteq> a"
      by(force simp add: fresh_prod name_fresh)

    from cFreshQa' have L1: "a<\<nu>x> \<prec> Qa' = a<\<nu>c> \<prec> ([(x, c)] \<bullet> Qa')"
      by(simp add: alphaBoundOutput)
    with cFreshQa' cFreshPa' have "c \<sharp> (Pa' \<parallel> Qa')"
      by simp
    then have L4: "<\<nu>x>(Pa' \<parallel> Qa') = <\<nu>c>(([(x, c)] \<bullet> Pa') \<parallel> ([(x, c)] \<bullet> Qa'))"
      by(simp add: alphaRes)

    have TransP: "Pa \<longmapsto> a<c> \<prec> [(x, c)] \<bullet> Pa'"
    proof -
      from xFreshPa TransP have xineqa: "x\<noteq>a" by(force dest: freshAction)
      from TransP have "([(x, c)] \<bullet> Pa) \<longmapsto> [(x, c)] \<bullet> (a<x> \<prec> Pa')"
        by(rule TransitionsEarly.eqvt)
      with xineqa xFreshPa cFreshPa cineqa show ?thesis
        by(simp add: name_fresh_fresh name_calc)
    qed

    with TransQ L1 L4 icClose1 Eq Eq' cFreshPa cFreshC show ?thesis
      by(simp add: residual.inject, simp add: pi.inject)
  next
    fix Pa Pa' Qa Qa' a x
    assume TransP: "Pa \<longmapsto> a<\<nu>x> \<prec> Pa'"
    assume TransQ: "Qa \<longmapsto> a<x> \<prec> Qa'"
    assume xFreshQa: "x \<sharp> Qa"
    assume Eq: "P \<parallel> Q = Pa \<parallel> Qa"
    assume Eq': "\<alpha> \<prec> PQ' = \<tau> \<prec> <\<nu>x>(Pa' \<parallel> Qa')"

    have "\<exists>(c::name). c \<sharp> (Qa, Pa', x, Qa', a, C)"
      by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshQa: "c \<sharp> Qa" and cFreshPa': "c \<sharp> Pa'" and cineqy: "c \<noteq> x" and cFreshQa': "c \<sharp> Qa'" and cFreshC: "c \<sharp> C" and cineqa: "c \<noteq> a"
      by(force simp add: fresh_prod name_fresh)

    from cFreshPa' have L1: "a<\<nu>x> \<prec> Pa' = a<\<nu>c> \<prec> ([(x, c)] \<bullet> Pa')"
      by(simp add: alphaBoundOutput)
    with cFreshQa' cFreshPa' have "c \<sharp> (Pa' \<parallel> Qa')"
      by simp
    then have L4: "<\<nu>x>(Pa' \<parallel> Qa') = <\<nu>c>(([(x, c)] \<bullet> Pa') \<parallel> ([(x, c)] \<bullet> Qa'))"
      by(simp add: alphaRes)

    have TransQ: "Qa \<longmapsto> a<c> \<prec> [(x, c)] \<bullet> Qa'"
    proof -
      from xFreshQa TransQ have xineqa: "x\<noteq>a" by(force dest: freshAction)
      from TransQ have "([(x, c)] \<bullet> Qa) \<longmapsto> [(x, c)] \<bullet> (a<x> \<prec> Qa')"
        by(rule TransitionsEarly.eqvt)
      with xineqa xFreshQa cFreshQa cineqa show ?thesis
        by(simp add: name_fresh_fresh name_calc)
    qed

    with TransP L1 L4 icClose2 Eq Eq' cFreshQa cFreshC show ?thesis
      by(simp add: residual.inject, simp add: pi.inject)
  qed
qed

lemma resCasesF[consumes 2, case_names Res]:
  fixes x :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes Trans: "<\<nu>x>P \<longmapsto> \<alpha> \<prec> RP'"
  and     xFreshAlpha: "x \<sharp> \<alpha>"
  and     rcResF: " \<And>P'. P \<longmapsto> \<alpha> \<prec> P' \<Longrightarrow> F (<\<nu>x>P')"

  shows "F RP'"
proof -
  from Trans show ?thesis
  proof(induct rule: resCasesF', auto)
    fix Pa Pa' \<beta> y
    assume PTrans: "Pa \<longmapsto> \<beta> \<prec> Pa'"
    assume yFreshBeta: "(y::name) \<sharp> \<beta>"
    assume TermEq: "<\<nu>x>P = <\<nu>y>Pa"
    assume ResEq: "\<alpha> \<prec> RP' = \<beta> \<prec> <\<nu>y>Pa'"

    hence alphaeqbeta: "\<alpha> = \<beta>" and L2: "RP' = <\<nu>y>Pa'" by(simp add: residual.inject)+

    have "\<exists>(c::name). c \<sharp> (Pa, \<alpha>, Pa', x, y)" by(blast intro: name_exists_fresh)
    then obtain c::name where cFreshPa: "c \<sharp> Pa" and cFreshAlpha: "c \<sharp> \<alpha>" and cFreshPa': "c \<sharp> Pa'" and cineqx: "x \<noteq> c" and cineqy: "c \<noteq> y"
      by(force simp add: fresh_prod name_fresh)

    from cFreshPa have "<\<nu>y>Pa = <\<nu>c>([(y, c)] \<bullet> Pa)" by(rule alphaRes)
    with TermEq cineqx have Peq: "P = [(x, c)] \<bullet> [(y, c)] \<bullet> Pa" and xeq: "x \<sharp> [(y, c)] \<bullet> Pa"
      by(simp add: pi.inject name_abs_eq)+

    from PTrans have "([(y, c)] \<bullet> Pa) \<longmapsto> [(y, c)] \<bullet> (\<beta> \<prec> Pa')" by(rule TransitionsEarly.eqvt)
    with yFreshBeta cFreshAlpha alphaeqbeta have PTrans': "([(y, c)] \<bullet> Pa) \<longmapsto> \<alpha> \<prec> ([(y, c)] \<bullet> Pa')" 
      by(simp add: name_fresh_fresh)

    from PTrans' have "([(x, c)] \<bullet> [(y, c)] \<bullet> Pa) \<longmapsto> [(x, c)] \<bullet> (\<alpha> \<prec> [(y, c)] \<bullet> Pa')"
      by(rule TransitionsEarly.eqvt)
    with xFreshAlpha cFreshAlpha Peq have PTrans'': "P \<longmapsto> \<alpha> \<prec> [(x, c)] \<bullet> [(y, c)] \<bullet> Pa'"
      by(simp add: name_fresh_fresh)

    from PTrans' xeq xFreshAlpha have xeq': "x \<sharp> [(y, c)] \<bullet> Pa'"
      by(nominal_induct \<alpha> rule: freeRes.strong_induct)
        (auto simp add: fresh_left calc_atm eqvts dest: freshTransition)

    from cFreshPa' have "<\<nu>y>Pa' = <\<nu>c>([(y, c)] \<bullet> Pa')" by(rule alphaRes)
    moreover from xeq' have "<\<nu>c>([(y, c)] \<bullet> Pa') = <\<nu>x>([(c, x)] \<bullet> [(y, c)] \<bullet> Pa')"
      by(rule alphaRes)
    ultimately have "RP' = <\<nu>x>([(x, c)] \<bullet> [(y, c)] \<bullet> Pa')" using ResEq
      by(simp add: residual.inject name_swap)

    with PTrans'' xFreshAlpha show ?thesis
      by(blast intro: rcResF)
  qed
qed

lemma resCasesB[consumes 2, case_names Open Res]:
  fixes x :: name
  and   P  :: pi
  and   a  :: name
  and   y :: name
  and   RP' :: pi

  assumes Trans:  "<\<nu>y>P \<longmapsto> a<\<nu>x> \<prec> RP'"
  and     xineqy: "x \<noteq> y"
  and     rcOpen: "\<And>P'. \<lbrakk>P \<longmapsto>(OutputR a y) \<prec> P'; a \<noteq> y\<rbrakk> \<Longrightarrow> F ([(x, y)] \<bullet> P')"
  and     rcResB: "\<And>P'. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; y \<noteq> a\<rbrakk> \<Longrightarrow> F (<\<nu>y>P')"

  shows "F RP'"
proof -
  from Trans show ?thesis
  proof(induct rule: resCasesB', auto)
    fix Pa Pa' aa b
    assume PTrans: "Pa \<longmapsto> (aa::name)[b] \<prec> Pa'"
    assume aaineqb: "aa\<noteq>b"
    assume TermEq: "<\<nu>y>P = <\<nu>b>Pa"
    assume ResEq: "a<\<nu>x> \<prec> RP' = aa<\<nu>b> \<prec> Pa'"

    have "\<exists>(c::name). c \<sharp> (x, a, aa, y, Pa, Pa', b)" by(blast intro: name_exists_fresh)
    then obtain c where cineqx: "c\<noteq>x" and cFresha: "c \<sharp> a" and cineqy: "c \<noteq> y" and cineqaa: "c \<noteq> aa" and cFreshPa: "c \<sharp> Pa" and cFreshPa': "c \<sharp> Pa'" and cineqb: "c \<noteq> b"
      by(force simp add: fresh_prod name_fresh)

    from cFreshPa have "<\<nu>b>Pa = <\<nu>c>([(b, c)] \<bullet> Pa)" by(rule alphaRes)
    with cineqy TermEq have PEq: "P = [(y, c)] \<bullet> [(b, c)] \<bullet> Pa" and yFreshPa: "y \<sharp> [(b, c)] \<bullet> Pa"
      by(simp add: pi.inject name_abs_eq)+

    from PTrans have "([(b, c)] \<bullet> Pa) \<longmapsto> ([(b, c)] \<bullet> (aa[b] \<prec> Pa'))" by(rule TransitionsEarly.eqvt)
    with aaineqb cineqaa have L1: "([(b, c)] \<bullet> Pa) \<longmapsto> aa[c] \<prec> [(b, c)] \<bullet> Pa'" by(simp add: name_calc)
    with yFreshPa have yineqaa: "y \<noteq> aa" by(force dest: freshAction)
    from L1 yFreshPa cineqy have yFreshPa': "y \<sharp> [(b, c)] \<bullet> Pa'" by(force intro: freshTransition)

    from L1 have "([(y, c)] \<bullet> [(b, c)] \<bullet> Pa) \<longmapsto> [(y, c)] \<bullet> (aa[c] \<prec> [(b, c)] \<bullet> Pa')"
      by(rule TransitionsEarly.eqvt)
    with cineqaa yineqaa cineqy PEq have PTrans: "P \<longmapsto> aa[y] \<prec> [(y, c)] \<bullet> [(b, c)] \<bullet> Pa'"
      by(simp add: name_calc)
    moreover from cFreshPa' have "aa<\<nu>b> \<prec> Pa' = aa<\<nu>c> \<prec> ([(b, c)] \<bullet> Pa')" by(rule alphaBoundOutput)
    with ResEq cineqx have ResEq': "RP' = [(x, c)] \<bullet> [(b, c)] \<bullet> Pa'" and "x \<sharp> [(b, c)] \<bullet> Pa'"
      by(simp add: residual.inject name_abs_eq)+
    with xineqy cineqy cineqx yFreshPa' have "RP' = [(x, y)] \<bullet> [(y, c)] \<bullet> [(b, c)] \<bullet> Pa'"
      by(subst pt_perm_compose[OF pt_name_inst, OF at_name_inst], simp add: name_calc name_fresh_fresh)
    moreover from ResEq have "a=aa" by(simp add: residual.inject)
    ultimately show ?thesis using yineqaa rcOpen
      by blast
  next
    fix Pa Pa' aa xa ya
    assume PTrans: "Pa \<longmapsto> aa<\<nu>xa> \<prec> Pa'"
    assume yaFreshaa: "(ya::name) \<noteq> aa"
    assume yaineqxa: "ya \<noteq> xa"
    assume EqTrans: "<\<nu>y>P = <\<nu>ya>Pa"
    assume EqRes: "a<\<nu>x> \<prec> RP' = aa<\<nu>xa> \<prec> (<\<nu>ya>Pa')"
    
    hence aeqaa: "a = aa" by(simp add: residual.inject)
    with yaFreshaa have yaFresha: "ya \<sharp> a" by simp

    have "\<exists>(c::name). c \<sharp> (Pa', y, xa, ya, x, Pa, aa)" by(blast intro: name_exists_fresh)
    then obtain c where cFreshPa': "c \<sharp> Pa'" and cineqy: "c \<noteq> y" and cineqxa: "c \<noteq> xa" and cineqya: "c \<noteq> ya" and cineqx: "c \<noteq> x" and cFreshP: "c \<sharp> Pa" and cFreshaa: "c \<sharp> aa"
      by(force simp add: fresh_prod name_fresh)

    have "\<exists>(d::name). d \<sharp> (Pa, a, x, Pa', c, xa, ya, y)" by(blast intro: name_exists_fresh)
    then obtain d where dFreshPa: "d \<sharp> Pa" and dFresha: "d \<sharp> a" and dineqx: "d \<noteq> x" and dFreshPa': "d \<sharp> Pa'" and dineqc: "d\<noteq>c" and dineqxa: "d \<noteq> xa" and dineqya: "d \<noteq> ya" and dineqy: "d \<noteq> y"
      by(force simp add: fresh_prod name_fresh)

    from dFreshPa have "<\<nu>ya>Pa = <\<nu>d>([(ya, d)] \<bullet> Pa)" by(rule alphaRes)
    with EqTrans dineqy have PEq: "P = [(y, d)] \<bullet> [(ya, d)] \<bullet> Pa"
                         and yFreshPa: "y \<sharp> [(ya, d)] \<bullet> Pa"
      by(simp add: pi.inject name_abs_eq)+

    from dFreshPa' have L1: "<\<nu>ya>Pa' = <\<nu>d>([(ya, d)] \<bullet> Pa')" by(rule alphaRes)
    from cFreshPa' dineqc cineqya have "c \<sharp> <\<nu>d>([(ya, d)] \<bullet> Pa')"
      by(simp add: name_fresh_abs name_calc name_fresh_left)
    hence "aa<\<nu>xa> \<prec> (<\<nu>d>([(ya, d)] \<bullet> Pa')) = aa<\<nu>c> \<prec> ([(xa, c)] \<bullet> <\<nu>d>([(ya, d)] \<bullet> Pa'))" (is "?LHS = _")
      by(rule alphaBoundOutput)
    with dineqxa dineqc have "?LHS = aa<\<nu>c> \<prec> (<\<nu>d>([(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa'))"
      by(simp add: name_calc)
    with L1 EqRes cineqx dineqc dineqx have
          RP'Eq: "RP' = <\<nu>d>([(x, c)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa')"
      and xFreshPa': "x \<sharp> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa'"
      by(simp add: residual.inject name_abs_eq name_fresh_abs name_calc)+

    from PTrans aeqaa have "([(ya, d)] \<bullet> Pa) \<longmapsto> [(ya, d)] \<bullet> (a<\<nu>xa> \<prec> Pa')"
      by(blast intro: TransitionsEarly.eqvt)
    with yaineqxa yaFresha dineqxa dFresha have L1:
      "([(ya, d)] \<bullet> Pa) \<longmapsto> a<\<nu>xa> \<prec> ([(ya, d)] \<bullet> Pa')" by(simp add: name_calc name_fresh_fresh)
    with yFreshPa have yineqa: "y \<noteq> a" by(force dest: freshAction)    
    from dineqc cineqya cFreshPa' have "c \<sharp> [(ya, d)] \<bullet> Pa'"
      by(simp add: name_fresh_left name_calc)
    hence "a<\<nu>xa> \<prec> ([(ya, d)] \<bullet> Pa') = a<\<nu>c> \<prec> ([(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa')" (is "?LHS = _")
      by(rule alphaBoundOutput)
    with xFreshPa' have L2: "?LHS = a<\<nu>x> \<prec> ([(c, x)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa')"
      by(simp add: alphaBoundOutput)
    with L1 PEq have "P \<longmapsto> [(y, d)] \<bullet> (a<\<nu>x> \<prec> ([(c, x)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa'))"
      by(force intro: TransitionsEarly.eqvt simp del: residual.perm)
    with yineqa dFresha xineqy dineqx have Trans: "P \<longmapsto> a<\<nu>x> \<prec> ([(y, d)] \<bullet> [(c, x)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa')"
      by(simp add: name_calc name_fresh_fresh)

    from L1 L2 yFreshPa xineqy have "y \<sharp> [(c, x)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa'"
      by(force intro: freshTransition)
    with RP'Eq have "RP' = <\<nu>y>([(y, d)] \<bullet> [(c, x)] \<bullet> [(xa, c)] \<bullet> [(ya, d)] \<bullet> Pa')"
      by(simp add: alphaRes name_swap)

    with Trans yineqa show ?thesis
      by(blast intro: rcResB)
  qed
qed

lemma bangInduct[consumes 1, case_names Par1B Par1F Par2B Par2F Comm1 Comm2 Close1 Close2 Bang]:
  fixes F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> residual \<Rightarrow> bool"
  and   P  :: pi
  and   Rs :: residual
  and   C  :: "'a::fs_name"

  assumes Trans:  "!P \<longmapsto> Rs"
  and     cPar1B: "\<And>a x P' C. \<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; x \<sharp> P; x \<sharp> C\<rbrakk> \<Longrightarrow> F  C (P \<parallel> !P) (a<\<nu>x> \<prec> (P' \<parallel> !P))"
  and     cPar1F: "\<And>(\<alpha>::freeRes) (P'::pi) C. \<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> F  C (P \<parallel> !P) (\<alpha> \<prec> P' \<parallel> !P)"
  and     cPar2B: "\<And>a x P' C. \<lbrakk>!P \<longmapsto> a<\<nu>x> \<prec> P'; x \<sharp> P; x \<sharp> C; \<And>C. F C (!P) (a<\<nu>x> \<prec> P')\<rbrakk> \<Longrightarrow> F  C (P \<parallel> !P) (a<\<nu>x> \<prec> (P \<parallel> P'))"
  and     cPar2F: "\<And>\<alpha> P' C. \<lbrakk>!P \<longmapsto> \<alpha> \<prec> P'; \<And>C. F C (!P) (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> F C (P \<parallel> !P) (\<alpha> \<prec> P \<parallel> P')"
  and     cComm1: "\<And>a P' b P'' C. \<lbrakk>P \<longmapsto> a<b> \<prec> P'; !P \<longmapsto> (OutputR a b) \<prec> P''; \<And>C. F C (!P) ((OutputR a b) \<prec> P'')\<rbrakk> \<Longrightarrow>
                                     F C (P \<parallel> !P) (\<tau> \<prec> P' \<parallel> P'')"
  and     cComm2: "\<And>a b P' P'' C. \<lbrakk>P \<longmapsto> (OutputR a b) \<prec> P'; !P \<longmapsto> a<b> \<prec> P''; \<And>C. F C (!P) (a<b> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                     F C (P \<parallel> !P) (\<tau> \<prec> P' \<parallel> P'')"
  and     cClose1: "\<And>a x P' P'' C. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; !P \<longmapsto> a<\<nu>x> \<prec> P''; x \<sharp> P; x \<sharp> C; \<And>C. F C (!P) (a<\<nu>x> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                     F C (P \<parallel> !P) (\<tau> \<prec> <\<nu>x>(P' \<parallel> P''))"
  and     cClose2: "\<And>a x P' P'' C. \<lbrakk>P \<longmapsto> a<\<nu>x> \<prec> P'; !P \<longmapsto> a<x> \<prec> P''; x \<sharp> P; x \<sharp> C; \<And>C. F C (!P) (a<x> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                     F C (P \<parallel> !P) (\<tau> \<prec> <\<nu>x>(P' \<parallel> P''))"
  and     cBang: "\<And>Rs C. \<lbrakk>P \<parallel> !P \<longmapsto> Rs; \<And>C. F C (P \<parallel> !P) Rs\<rbrakk> \<Longrightarrow> F C (!P) Rs"

  shows "F C (!P) Rs"
proof -
  have "\<And>X Y C. \<lbrakk>X \<longmapsto> Y; bangPred P X\<rbrakk> \<Longrightarrow> F C X Y"
  proof -
    fix X Y C
    assume "X \<longmapsto> Y" and "bangPred P X"
    thus "F C X Y"
    proof(nominal_induct avoiding: C rule: TransitionsEarly.strong_induct)
      case(Tau Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (\<tau>.(Pa))")
    next
      case(Input x a u Pa C)
      thus ?case
        by - (ind_cases "bangPred P (a<x>.Pa)")
    next
      case(Output a b Pa C)
      thus ?case
        by - (ind_cases "bangPred P (a{b}.Pa)")
    next
      case(Match Pa Rs b C)
      thus ?case
        by - (ind_cases "bangPred P ([b\<frown>b]Pa)")
    next
      case(Mismatch Pa Rs a b C)
      thus ?case
        by - (ind_cases "bangPred P ([a \<noteq> b]Pa)")
    next
      case(Open Pa a b Pa')
      thus ?case
        by - (ind_cases "bangPred P (<\<nu>b>Pa)")
    next
      case(Sum1 Pa Rs Q)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<oplus> Q)")
    next
      case(Sum2 Q Rs Pa)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<oplus> Q)")
    next
      case(Par1B Pa a x P' Q C)
      thus ?case 
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject cPar1B)
    next
      case(Par1F Pa \<alpha> P' Q C)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject cPar1F)
    next
      case(Par2B Q a x Q' Pa)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject aux1 cPar2B)
    next
      case(Par2F Q \<alpha> Q' Pa)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject intro: cPar2F aux1)
    next
      case(Comm1 Pa a b Pa' Q Q' C)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject intro: cComm1 aux1)
    next
      case(Comm2 Pa a b Pa' Q P'' C)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject intro: cComm2 aux1)
    next
      case(Close1 Pa a x Pa' Q Q'' C)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject aux1 cClose1)
    next
      case(Close2 Pa a x Pa' Q Q' C)
      thus ?case
        by - (ind_cases "bangPred P (Pa \<parallel> Q)", auto simp add: pi.inject aux1 cClose2)
    next
      case(ResB Pa a x Pa' y)
      thus ?case
        by - (ind_cases "bangPred P (<\<nu>y>Pa)")
    next
      case(ResF Pa \<alpha> Pa' y)
      thus ?case
        by - (ind_cases "bangPred P (<\<nu>y>Pa)")
    next
      case(Bang Pa Rs)
      thus ?case
        by - (ind_cases "bangPred P (!Pa)", auto simp add: pi.inject intro: aux2 cBang)
    qed
  qed
  with Trans show ?thesis by(force intro: bangPred.aux1)
qed

end
