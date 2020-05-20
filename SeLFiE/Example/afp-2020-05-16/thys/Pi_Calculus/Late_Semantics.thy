(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Late_Semantics
  imports Agent
begin
 
nominal_datatype subject = InputS name
                         | BoundOutputS name

nominal_datatype freeRes = OutputR name name             ("_[_]" [130, 130] 110)
                         | TauR                          ("\<tau>" 130)

nominal_datatype residual = BoundR subject "\<guillemotleft>name\<guillemotright> pi" ("_\<guillemotleft>_\<guillemotright> \<prec> _" [80, 80, 80] 80)
                          | FreeR freeRes pi           ("_ \<prec> _" [80, 80] 80)

lemmas residualInject = residual.inject freeRes.inject subject.inject

abbreviation "Transitions_Inputjudge" :: "name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> residual" ("_<_> \<prec> _" [80, 80, 80] 80)
where "a<x> \<prec> P' \<equiv> ((InputS a)\<guillemotleft>x\<guillemotright> \<prec> P')"

abbreviation "Transitions_BoundOutputjudge" :: "name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> residual" ("_<\<nu>_> \<prec> _" [80, 80, 80] 80)
where "a<\<nu>x> \<prec> P' \<equiv> (BoundR (BoundOutputS a) x P')"

inductive transitions :: "pi \<Rightarrow> residual \<Rightarrow> bool"      ("_ \<longmapsto> _" [80, 80] 80)
where
  Tau:               "\<tau>.(P) \<longmapsto> \<tau> \<prec> P"
| Input:             "x \<noteq> a \<Longrightarrow> a<x>.P \<longmapsto> a<x> \<prec> P"
| Output:            "a{b}.P \<longmapsto> a[b] \<prec>  P"
 
| Match:             "\<lbrakk>P \<longmapsto> Rs\<rbrakk> \<Longrightarrow> [b\<frown>b]P \<longmapsto> Rs"
| Mismatch:          "\<lbrakk>P \<longmapsto> Rs; a \<noteq> b\<rbrakk> \<Longrightarrow> [a\<noteq>b]P \<longmapsto> Rs"

| Open:              "\<lbrakk>P \<longmapsto> a[b] \<prec> P'; a \<noteq> b\<rbrakk> \<Longrightarrow> <\<nu>b>P \<longmapsto> a<\<nu>b> \<prec> P'"
| Sum1:              "\<lbrakk>P \<longmapsto> Rs\<rbrakk> \<Longrightarrow> (P \<oplus> Q) \<longmapsto> Rs"
| Sum2:              "\<lbrakk>Q \<longmapsto> Rs\<rbrakk> \<Longrightarrow> (P \<oplus> Q) \<longmapsto> Rs"

| Par1B:             "\<lbrakk>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'; x \<sharp> P; x \<sharp> Q; x \<sharp> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> Q)"
| Par1F:             "\<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<alpha> \<prec> (P' \<parallel> Q)"
| Par2B:             "\<lbrakk>Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<sharp> a\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q')"
| Par2F:             "\<lbrakk>Q \<longmapsto> \<alpha> \<prec> Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<alpha> \<prec> (P \<parallel> Q')"

| Comm1:             "\<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a[b] \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<noteq> b; x \<sharp> Q'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> P'[x::=b] \<parallel> Q'"
| Comm2:             "\<lbrakk>P \<longmapsto> a[b] \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<noteq> b; x \<sharp> P'\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> P' \<parallel> Q'[x::=b]"
| Close1:            "\<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a<\<nu>y> \<prec> Q'; x \<sharp> P; x \<sharp> Q; y \<sharp> P; 
                       y \<sharp> Q; x \<noteq> a; x \<sharp> Q'; y \<noteq> a; y \<sharp> P'; x \<noteq> y\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> Q')"
| Close2:            "\<lbrakk>P \<longmapsto> a<\<nu>y> \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; y \<sharp> P;
                       y \<sharp> Q; x \<noteq> a; x \<sharp> P'; y \<noteq> a; y \<sharp> Q'; x \<noteq> y\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto> \<tau> \<prec> <\<nu>y>(P' \<parallel> Q'[x::=y])"

| ResB:              "\<lbrakk>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'; y \<sharp> a; y \<noteq> x; x \<sharp> P; x \<sharp> a\<rbrakk> \<Longrightarrow> <\<nu>y>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> <\<nu>y>P'"
| ResF:              "\<lbrakk>P \<longmapsto> \<alpha> \<prec> P'; y \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> <\<nu>y>P \<longmapsto> \<alpha> \<prec> <\<nu>y>P'"

| Bang:              "\<lbrakk>P \<parallel> !P \<longmapsto> Rs\<rbrakk> \<Longrightarrow> !P \<longmapsto> Rs"

equivariance transitions
nominal_inductive transitions
by(auto simp add: abs_fresh fresh_fact2)

lemma alphaBoundResidual:
  fixes a  :: subject
  and   x  :: name
  and   P  :: pi
  and   x' :: name

  assumes A1: "x' \<sharp> P"

  shows "a\<guillemotleft>x\<guillemotright> \<prec> P = a\<guillemotleft>x'\<guillemotright> \<prec> ([(x, x')] \<bullet> P)"
proof(cases "x=x'")
  assume "x=x'"
  thus ?thesis by simp
next
  assume "x \<noteq> x'"
  with A1 show ?thesis
    by(simp add: residualInject alpha name_fresh_left name_calc)
qed

lemma freshResidual:
  fixes P  :: pi
  and   Rs :: residual
  and   x  :: name
  
  assumes "P \<longmapsto> Rs"
  and     "x \<sharp> P"

  shows "x \<sharp> Rs"
using assms
by(nominal_induct rule: transitions.strong_induct)
  (auto simp add: abs_fresh fresh_fact2 fresh_fact1)

lemma freshBoundDerivative:
  assumes "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'"
  and     "y \<sharp> P"

  shows "y \<sharp> a"
  and   "y \<noteq> x \<Longrightarrow> y \<sharp> P'"
apply -
using assms
by(fastforce dest: freshResidual simp add: abs_fresh)+

lemma freshFreeDerivative:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   y  :: name

  assumes "P \<longmapsto>\<alpha> \<prec> P'"
  and     "y \<sharp> P"

  shows "y \<sharp> \<alpha>"
  and   "y \<sharp> P'"
apply -
using assms
by(fastforce dest: freshResidual)+

lemma substTrans[simp]: 
  fixes b :: name
  and   P :: pi
  and   a :: name
  and   c :: name

  assumes "b \<sharp> P"

  shows "(P[a::=b])[b::=c] = P[a::=c]"
using assms
apply(simp add: injPermSubst[THEN sym])
apply(simp add: renaming)
by(simp add: pt_swap[OF pt_name_inst, OF at_name_inst])

lemma Input:
  fixes a :: name
  and   x :: name
  and   P :: pi

  shows "a<x>.P \<longmapsto>a<x> \<prec> P"
proof -
  obtain y::name where "y \<noteq> a" and "y \<sharp> P"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from \<open>y \<sharp> P\<close> have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" and "a<x> \<prec> P = a<y> \<prec> ([(x, y)] \<bullet> P)"
    by(auto simp add: alphaBoundResidual alphaInput)
  with \<open>y \<noteq> a\<close> show ?thesis by(force intro: Input)
qed

declare perm_fresh_fresh[simp] name_swap[simp] fresh_prod[simp]

lemma Par1B:
  fixes P  :: pi
  and   a  :: subject
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi

  assumes "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'"
  and     "x \<sharp> Q"

  shows "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> Q"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> Q" and "y \<sharp> a"
    by(generate_fresh "name", auto)
  from \<open>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'\<close> \<open>y \<sharp> P'\<close> have "P \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> ([(x, y)] \<bullet> P')"
    by(simp add: alphaBoundResidual)
  hence "P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> ([(x, y)] \<bullet> P') \<parallel> Q" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> a\<close>
    by(rule Par1B)
  with \<open>x \<sharp> Q\<close> \<open>y \<sharp> P'\<close> \<open>y \<sharp> Q\<close> show ?thesis
    by(subst alphaBoundResidual[where x'=y]) auto
qed

lemma Par2B:
  fixes Q  :: pi
  and   a  :: subject
  and   x  :: name
  and   Q' :: pi
  and   P  :: pi

  assumes QTrans: "Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q'"
  and     "x \<sharp> P"

  shows "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'"
proof -
  obtain y::name where "y \<sharp> Q" and "y \<sharp> Q'" and "y \<sharp> P" and "y \<sharp> a"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> ([(x, y)] \<bullet> Q')"
    by(simp add:alphaBoundResidual)
  hence "P \<parallel> Q \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> ([(x, y)] \<bullet> Q')" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<sharp> a\<close>
    by(rule Par2B)
  moreover have "a\<guillemotleft>y\<guillemotright> \<prec> P \<parallel> ([(x, y)] \<bullet> Q') = a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> Q'"
  proof -
    from \<open>y \<sharp> Q'\<close> \<open>x \<sharp> P\<close> have "x \<sharp> P \<parallel> ([(x, y)] \<bullet> Q')" by(auto simp add: calc_atm fresh_left)
    with \<open>x \<sharp> P\<close> \<open>y \<sharp> P\<close> show ?thesis by(simp only: alphaBoundResidual, auto simp add: name_swap name_fresh_fresh)
  qed
  ultimately show ?thesis by simp
qed

lemma Comm1:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   b  :: name
  and   Q' :: pi

  assumes PTrans: "P \<longmapsto>a<x> \<prec> P'"
  and     QTrans: "Q \<longmapsto>a[b] \<prec> Q'"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> P'[x::=b] \<parallel> Q'"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> Q" and "y \<noteq> a" and "y \<noteq> b" and "y \<sharp> Q'"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from PTrans \<open>y \<sharp> P'\<close> have "P \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P')"
    by(simp add: alphaBoundResidual)
  hence "P \<parallel> Q \<longmapsto>\<tau> \<prec> ([(x, y)] \<bullet> P')[y::=b] \<parallel> Q'" 
    using QTrans \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close> \<open>y \<noteq> b\<close> \<open>y \<sharp> Q'\<close> 
    by(rule Comm1)
  with \<open>y \<sharp> P'\<close> show ?thesis by(simp add: renaming name_swap)
qed

lemma Comm2:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi
  and   Q  :: pi
  and   x  :: name
  and   Q' :: pi

  assumes PTrans: "P \<longmapsto>a[b] \<prec> P'"
  and     QTrans: "Q \<longmapsto>a<x> \<prec> Q'"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> P' \<parallel> (Q'[x::=b])"
proof -
  obtain y::name where "y \<sharp> P" and "y \<sharp> P'" and "y \<sharp> Q" and "y \<noteq> a" and "y \<noteq> b" and "y \<sharp> Q'"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from QTrans \<open>y \<sharp> Q'\<close> have "Q \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> Q')"
    by(simp add: alphaBoundResidual)
  with PTrans have "P \<parallel> Q \<longmapsto>\<tau> \<prec> P' \<parallel> (([(x, y)] \<bullet> Q')[y::=b])"
  using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close> \<open>y \<noteq> b\<close> \<open>y \<sharp> P'\<close>
    by(rule Comm2)
  with \<open>y \<sharp> Q'\<close> show ?thesis by(simp add: renaming name_swap)
qed

lemma Close1:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   Q  :: pi
  and   y  :: name
  and   Q' :: pi

  assumes PTrans: "P \<longmapsto>a<x> \<prec> P'"
  and     QTrans: "Q \<longmapsto>a<\<nu>y> \<prec> Q'"
  and     "y \<sharp> P"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> Q')"
proof - 
  obtain x'::name where "x' \<sharp> P" and "x' \<sharp> P'" and "x' \<sharp> Q" and "x' \<sharp> Q'" and "x' \<noteq> a"
    by(generate_fresh "name", auto simp add: fresh_prod)
  obtain y'::name where "y' \<sharp> P" and "y' \<sharp> Q'" and "y' \<sharp> Q"
                    and "y' \<sharp> P'" and "y' \<noteq> x'" and "y' \<noteq> y" and "y' \<noteq> a"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from PTrans \<open>x' \<sharp> P'\<close> have "P \<longmapsto>a<x'> \<prec> ([(x, x')] \<bullet> P')"
    by(simp add: alphaBoundResidual)
  moreover from QTrans \<open>y' \<sharp> Q'\<close> have "Q \<longmapsto>a<\<nu>y'> \<prec> ([(y, y')] \<bullet> Q')"
    by(simp add: alphaBoundResidual)
  ultimately have "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y'>(([(x, x')] \<bullet> P')[x'::=y'] \<parallel> ([(y, y')] \<bullet> Q'))"
    using \<open>y' \<sharp> P\<close> \<open>y' \<sharp> Q\<close> \<open>x' \<sharp> P\<close> \<open>x' \<sharp> Q\<close> \<open>y' \<noteq> x'\<close> \<open>y' \<noteq> a\<close> \<open>x' \<noteq> a\<close>
          \<open>y' \<sharp> P'\<close> \<open>y' \<sharp> Q'\<close> \<open>x' \<sharp> P'\<close> \<open>x' \<sharp> Q'\<close>
    apply(rule_tac Close1)
    by assumption (auto simp add: fresh_left calc_atm)
  moreover have "<\<nu>y'>(([(x, x')] \<bullet> P')[x'::=y'] \<parallel> ([(y, y')] \<bullet> Q')) = <\<nu>y>(P'[x::=y] \<parallel> Q')"
  proof -
    from \<open>x' \<sharp> P'\<close> have "([(x, x')] \<bullet> P')[x'::=y'] = P'[x::=y']" by(simp add: renaming name_swap)
    moreover have "y \<sharp> (P'[x::=y'] \<parallel> ([(y, y')] \<bullet> Q'))"
    proof(case_tac "y = x")
      assume "y = x"
      with \<open>y' \<sharp> Q'\<close> \<open>y' \<noteq> y\<close> show ?thesis by(auto simp add: fresh_fact2 fresh_left calc_atm)
    next
      assume "y \<noteq> x"
      with \<open>y \<sharp> P\<close> PTrans have "y \<sharp> P'" by(force dest: freshBoundDerivative)
      with \<open>y' \<sharp> Q'\<close> \<open>y' \<noteq> y\<close> show ?thesis by(auto simp add: fresh_left calc_atm fresh_fact1)
    qed
    ultimately show ?thesis using \<open>y' \<sharp> P'\<close> apply(simp only: alphaRes)
      by(auto simp add: name_swap eqvt_subs calc_atm renaming)
  qed
  ultimately show ?thesis by simp
qed

lemma Close2:
  fixes P  :: pi
  and   a  :: name
  and   y  :: name
  and   P' :: pi
  and   Q  :: pi
  and   x  :: name
  and   Q' :: pi

  assumes PTrans: "P \<longmapsto>a<\<nu>y> \<prec> P'"
  and     QTrans: "Q \<longmapsto>a<x> \<prec> Q'"
  and     "y \<sharp> Q"

  shows "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(P' \<parallel> (Q'[x::=y]))"
proof -
  obtain x'::name where "x' \<sharp> P" and "x' \<sharp> Q'" and "x' \<sharp> Q" and "x' \<sharp> P'" and "x' \<noteq> a"
    by(generate_fresh "name", auto simp add: fresh_prod)
  obtain y'::name where "y' \<sharp> P" and "y' \<sharp> P'" and "y' \<sharp> Q"
                    and "y' \<sharp> Q'" and "y' \<noteq> x'" and "y' \<noteq> y" and "y' \<noteq> a"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from PTrans \<open>y' \<sharp> P'\<close> have "P \<longmapsto>a<\<nu>y'> \<prec> ([(y, y')] \<bullet> P')"
    by(simp add: alphaBoundResidual)
  moreover from QTrans \<open>x' \<sharp> Q'\<close> have "Q \<longmapsto>a<x'> \<prec> ([(x, x')] \<bullet> Q')"
    by(simp add: alphaBoundResidual)
  ultimately have "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y'>(([(y, y')] \<bullet> P') \<parallel> (([(x, x')] \<bullet> Q')[x'::=y']))"
    using \<open>y' \<sharp> P\<close> \<open>y' \<sharp> Q\<close> \<open>x' \<sharp> P\<close> \<open>x' \<sharp> Q\<close> \<open>y' \<noteq> x'\<close> \<open>x' \<noteq> a\<close> \<open>y' \<noteq> a\<close>
          \<open>x' \<sharp> P'\<close> \<open>x' \<sharp> Q'\<close> \<open>y' \<sharp> P'\<close> \<open>y' \<sharp> Q'\<close>
    by(rule_tac Close2) (assumption | auto simp add: fresh_left calc_atm)+
  moreover have "<\<nu>y'>(([(y, y')] \<bullet> P') \<parallel> (([(x, x')] \<bullet> Q')[x'::=y'])) = <\<nu>y>(P' \<parallel> (Q'[x::=y]))"
  proof -
    from \<open>x' \<sharp> Q'\<close> have "([(x, x')] \<bullet> Q')[x'::=y'] = Q'[x::=y']" by(simp add: renaming name_swap)
    moreover have "y \<sharp> (([(y, y')] \<bullet> P') \<parallel> (Q'[x::=y']))"
    proof(case_tac "y = x")
      assume "y = x"
      with \<open>y' \<sharp> P'\<close> \<open>y' \<noteq> y\<close> show ?thesis by(auto simp add: fresh_fact2 fresh_left calc_atm)
    next
      assume "y \<noteq> x"
      with \<open>y \<sharp> Q\<close> QTrans have "y \<sharp> Q'" by(force dest: freshBoundDerivative)
      with \<open>y' \<sharp> P'\<close> \<open>y' \<noteq> y\<close> show ?thesis by(auto simp add: fresh_left calc_atm fresh_fact1)
    qed
    ultimately show ?thesis using \<open>y' \<sharp> Q'\<close> apply(simp only: alphaRes)
      by(auto simp add: name_swap eqvt_subs calc_atm renaming)
  qed
  ultimately show ?thesis by simp
qed

lemma ResB: 
  fixes P  :: pi
  and   a  :: subject
  and   x  :: name
  and   P' :: pi
  and   y  :: name

  assumes PTrans: "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'"
  and     "y \<sharp> a"
  and     "y \<noteq> x"

  shows "<\<nu>y>P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> <\<nu>y>P'"
proof -
  obtain z where "z \<sharp> P" and "z \<sharp> a" and "z \<noteq> y" and "z \<sharp> P'"
    by(generate_fresh "name", auto simp add: fresh_prod)
  from PTrans \<open>z \<sharp> P'\<close>  have "P \<longmapsto>a\<guillemotleft>z\<guillemotright> \<prec> ([(x, z)] \<bullet> P')" by(simp add: alphaBoundResidual)
  with \<open>z \<sharp> P\<close> \<open>z \<sharp> a\<close> \<open>z \<noteq> y\<close> \<open>y \<sharp> a\<close> have "<\<nu>y>P \<longmapsto>a\<guillemotleft>z\<guillemotright> \<prec> <\<nu>y>([(x, z)] \<bullet> P')" by(rule_tac ResB) auto
  moreover have "a\<guillemotleft>z\<guillemotright> \<prec> <\<nu>y>([(x, z)] \<bullet> P') = a\<guillemotleft>x\<guillemotright> \<prec> <\<nu>y>P'"
  proof -
    from \<open>z \<sharp> P'\<close> \<open>y \<noteq> x\<close> have "x \<sharp> <\<nu>y>([(x, z)] \<bullet> P')" by(auto simp add: abs_fresh fresh_left calc_atm)
    with \<open>y \<noteq> x\<close> \<open>z \<noteq> y\<close> show ?thesis by(simp add: alphaBoundResidual name_swap calc_atm)
  qed
  ultimately show ?thesis by simp
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
  and     "\<And>P a b P' c d C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'; c \<noteq> d\<rbrakk> \<Longrightarrow> F C ([c\<noteq>d]P) a b P'"
  and     "\<And>P a b P' Q C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a b P'"
  and     "\<And>Q a b Q' P C. \<lbrakk>Q \<longmapsto>OutputR a b \<prec> Q'; \<And>C. F C Q a b Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a b Q'"
  and     "\<And>P a b P' Q C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a b (P' \<parallel> Q)"
  and     "\<And>Q a b Q' P C. \<lbrakk>Q \<longmapsto>OutputR a b \<prec> Q'; \<And>C. F C Q a b Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) a b (P \<parallel> Q')"
  and     "\<And>P a b P' x C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; x \<noteq> a; x \<noteq> b; x \<sharp> C; \<And>C. F C P a b P'\<rbrakk> \<Longrightarrow>
                            F C (<\<nu>x>P) a b (<\<nu>x>P')"
  and     "\<And>P a b P' C. \<lbrakk>P \<parallel> !P \<longmapsto>OutputR a b \<prec> P'; \<And>C. F C (P \<parallel> !P) a b P'\<rbrakk> \<Longrightarrow> F C (!P) a b P'"

  shows "F C P a b P'"
proof -
  from Trans show ?thesis
  by(nominal_induct x2 == "OutputR a b \<prec> P'" avoiding: C arbitrary: P' rule: transitions.strong_induct,
     auto simp add: residualInject freeRes.inject intro: assms)
qed

lemma inputInduct[consumes 2, case_names Input Match Mismatch Sum1 Sum2 Par1 Par2 Res Bang]:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   F  :: "('a::fs_name) \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes a: "P \<longmapsto>a<x> \<prec> P'"
  and       "x \<sharp> P"
  and     cInput:    "\<And>a x P C. F C (a<x>.P) a x P"
  and     cMatch:    "\<And>P a x P' b C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C ([b\<frown>b]P) a x P'"
  and     cMismatch: "\<And>P a x P' b  c C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; \<And>C. F C P a x P'; b \<noteq> c\<rbrakk> \<Longrightarrow> F C ([b\<noteq>c]P) a x P'"
  and     cSum1:     "\<And>P Q a x P' C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x P'" 
  and     cSum2:     "\<And>P Q a x Q' C. \<lbrakk>Q \<longmapsto>a<x> \<prec> Q'; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x Q'" 
  and     cPar1B:    "\<And>P P' Q a x C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow>
                                       F C (P \<parallel> Q) a x (P' \<parallel> Q)" 
  and     cPar2B:    "\<And>P Q Q' a x C. \<lbrakk>Q \<longmapsto>a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow>
                                       F C (P \<parallel> Q) a x (P \<parallel> Q')"
  and     cResB:     "\<And>P P' a x y C. \<lbrakk>P \<longmapsto>a<x> \<prec> P'; y \<noteq> a; y \<noteq> x; y \<sharp> C;
                                      \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (<\<nu>y>P) a x (<\<nu>y>P')"
  and     cBang:     "\<And>P a x P' C. \<lbrakk>P \<parallel> !P \<longmapsto>a<x> \<prec> P'; \<And>C. F C (P \<parallel> !P) a x P'\<rbrakk> \<Longrightarrow>
                                     F C (!P) a x P'"
  shows "F C P a x P'"
proof -
  from a \<open>x \<sharp> P\<close> show ?thesis
  proof(nominal_induct x2 == "a<x> \<prec> P'" avoiding: C a x P' rule: transitions.strong_induct)
    case(Tau P)
    thus ?case by(simp add: residualInject)
  next
    case(Input x a P C a' x' P')
    have "x \<sharp> x'" by fact hence "x \<noteq> x'" by simp
    moreover have "a<x> \<prec> P = a'<x'> \<prec> P'" by fact
    ultimately have aeqa': "a = a'" and PeqP': "P = [(x, x')] \<bullet> P'"
      by(simp add: residualInject freeRes.inject subject.inject name_abs_eq)+
    
    have "F C (a<x'>.([(x, x')] \<bullet> P)) a x' ([(x, x')] \<bullet> P)" by(rule cInput)
    moreover have "x \<sharp> P'" by fact
    ultimately show ?case using PeqP' aeqa' by(simp add: alphaInput name_swap)
  next
    case(Output P a b)
    thus ?case by(simp add: residualInject)
  next
    case(Match P b Rs a x)
    thus ?case 
      by(force intro: cMatch simp add: residualInject) 
  next
    case(Mismatch P Rs a b C a x)
    thus ?case 
      by(force intro: cMismatch simp add: residualInject) 
  next
    case(Open P P' a b C a' x P')
    thus ?case by(simp add: residualInject)
  next
    case(Sum1 P Q Rs C)
    thus ?case by(force intro: cSum1)
  next
    case(Sum2 P Q Rs C)
    thus ?case by(force intro: cSum2)
  next
    case(Par1B P a x P' Q C a' x' P'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> Q) = a'<x'> \<prec> P''" by fact
    hence aeqa': "a = InputS a'" by(simp add: residualInject)
    have "x' \<sharp> P \<parallel> Q" by fact
    hence "x' \<sharp> P" and "x' \<sharp> Q" by simp+
    have P''eq: "P'' = ([(x, x')] \<bullet> P') \<parallel> Q"
    proof -
      from Eq xineqx' have "(P' \<parallel> Q) = [(x, x')] \<bullet> P''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (P' \<parallel> Q)) = P''" by simp
      with \<open>x' \<sharp> Q\<close>\<open>x \<sharp> Q\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed
    
    have "x \<sharp> P''" by fact
    with P''eq \<open>x \<noteq> x'\<close> have "x' \<sharp> P'" by(simp add: name_fresh_left name_calc)
    
    have PTrans: "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'" by fact
    with \<open>x' \<sharp> P'\<close> aeqa' have "P \<longmapsto>a'<x'> \<prec> ([(x, x')] \<bullet> P')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C P a' x' ([(x, x')] \<bullet> P')"
    proof -
      fix C
      have "\<And>C a' x' P''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> P'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C P a' x' ([(x, x')] \<bullet> P')" using \<open>x' \<sharp> P\<close> by blast 
    qed
    moreover from PTrans \<open>x' \<sharp> P\<close> have "x' \<sharp> a" by(auto dest: freshBoundDerivative)
    ultimately have "F C (P \<parallel> Q) a' x' (([(x, x')] \<bullet> P') \<parallel> Q)" using \<open>x' \<sharp> Q\<close>aeqa' \<open>x' \<sharp> P\<close>
      by(rule_tac cPar1B) auto
    with P''eq show ?case by simp
  next
    case(Par1F P P' Q \<alpha>)
    thus ?case by(simp add: residualInject)
  next
    case(Par2B Q a x Q' P C a' x' Q'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q') = a'<x'> \<prec> Q''" by fact
    hence aeqa': "a = InputS a'" by(simp add: residualInject)
    have "x \<sharp> P" by fact
    have "x' \<sharp> P \<parallel> Q" by fact
    hence "x' \<sharp> P" and "x' \<sharp> Q" by simp+
    have Q''eq: "Q'' = P \<parallel> ([(x, x')] \<bullet> Q')"
    proof -
      from Eq xineqx' have "(P \<parallel> Q') = [(x, x')] \<bullet> Q''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (P \<parallel> Q')) = Q''" by simp
      with \<open>x' \<sharp> P\<close> \<open>x \<sharp> P\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed
    
    have "x \<sharp> Q''" by fact
    with Q''eq \<open>x \<noteq> x'\<close> have "x' \<sharp> Q'" by(simp add: name_fresh_left name_calc)
    
    have QTrans: "Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    with \<open>x' \<sharp> Q'\<close> aeqa' have "Q \<longmapsto>a'<x'> \<prec> ([(x, x')] \<bullet> Q')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C Q a' x' ([(x, x')] \<bullet> Q')"
    proof -
      fix C
      have "\<And>C a' x' Q''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> Q' = a'<x'> \<prec> Q''; x' \<sharp> Q\<rbrakk> \<Longrightarrow> F C Q a' x' Q''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> Q'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> Q' = a'<x'> \<prec> ([(x, x')] \<bullet> Q')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C Q a' x' ([(x, x')] \<bullet> Q')" using \<open>x' \<sharp> Q\<close>aeqa' by blast 
    qed
    moreover from QTrans \<open>x' \<sharp> Q\<close> have "x' \<sharp> a" by(force dest: freshBoundDerivative)
    ultimately have "F C (P \<parallel> Q) a' x' (P \<parallel> ([(x, x')] \<bullet> Q'))" using \<open>x' \<sharp> P\<close> aeqa' \<open>x' \<sharp> Q\<close>
      by(rule_tac cPar2B) auto
    with Q''eq show ?case by simp
  next
    case(Par2F P P' Q \<alpha>)
    thus ?case by(simp add: residualInject)
  next
    case(Comm1 P P' Q Q' a b x)
    thus ?case by(simp add: residualInject)
  next
    case(Comm2 P P' Q Q' a b x)
    thus ?case by(simp add: residualInject)
  next
    case(Close1 P P' Q Q' a x y)
    thus ?case by(simp add: residualInject)
  next
    case(Close2 P P' Q Q' a x y)
    thus ?case by(simp add: residualInject)
  next
    case(ResB P a x P' y C a' x' P'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (<\<nu>y>P') = a'<x'> \<prec> P''" by fact
    hence aeqa': "a = InputS a'" by(simp add: residualInject)
    have "y \<sharp> x'" by fact hence yineqx': "y \<noteq> x'" by simp
    moreover have "x' \<sharp> <\<nu>y>P" by fact
    ultimately have "x' \<sharp> P" by(simp add: name_fresh_abs)
    have "y \<noteq> x" and yineqa: "y \<sharp> a" and yFreshC: "y \<sharp> C" by fact+
    
    have P''eq: "P'' = <\<nu>y>([(x, x')] \<bullet> P')"
    proof -
      from Eq xineqx' have "<\<nu>y>P' = [(x, x')] \<bullet> P''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (<\<nu>y>P')) = P''" by simp
      with yineqx' \<open>y \<noteq> x\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed
    
    have "x \<sharp> P''" by fact
    with P''eq \<open>y \<noteq> x\<close> \<open>x \<noteq> x'\<close> have "x' \<sharp> P'" by(simp add: name_fresh_left name_calc name_fresh_abs)
    
    have "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'" by fact
    with \<open>x' \<sharp> P'\<close> aeqa' have "P \<longmapsto>a'<x'> \<prec> ([(x, x')] \<bullet> P')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C P a' x' ([(x, x')] \<bullet> P')"
    proof -
      fix C
      have "\<And>C a' x' P''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> P'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C P a' x' ([(x, x')] \<bullet> P')" using \<open>x' \<sharp> P\<close> aeqa' by blast 
    qed
    ultimately have "F C (<\<nu>y>P) a' x' (<\<nu>y>([(x, x')] \<bullet> P'))" using yineqx' yineqa yFreshC aeqa'
      by(force intro: cResB)
    with P''eq show ?case by simp
  next
    case(ResF P P' \<alpha> y)
    thus ?case by(simp add: residualInject)
  next
    case(Bang P Rs)
    thus ?case by(force intro: cBang)
  qed
qed

lemma boundOutputInduct[consumes 2, case_names Match Mismatch Open Sum1 Sum2 Par1 Par2 Res Bang]:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   P' :: pi
  and   F  :: "('a::fs_name) \<Rightarrow> pi \<Rightarrow> name \<Rightarrow> name \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes a: "P \<longmapsto>a<\<nu>x> \<prec> P'"
  and       "x \<sharp> P"
  and     cMatch:    "\<And>P a x P' b C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C ([b\<frown>b]P) a x P'"
  and     cMismatch: "\<And>P a x P' b c C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'; b \<noteq> c\<rbrakk> \<Longrightarrow> F C ([b\<noteq>c]P) a x P'"
  and     cOpen:     "\<And>P a x P' C.   \<lbrakk>P \<longmapsto>(OutputR a x) \<prec> P'; a \<noteq> x\<rbrakk> \<Longrightarrow> F C (<\<nu>x>P) a x P'"
  and     cSum1:     "\<And>P Q a x P' C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x P'" 
  and     cSum2:     "\<And>P Q a x Q' C. \<lbrakk>Q \<longmapsto>a<\<nu>x> \<prec> Q'; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) a x Q'" 
  and     cPar1B:    "\<And>P P' Q a x C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; x \<sharp> Q; \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow>
                                       F C (P \<parallel> Q) a x (P' \<parallel> Q)" 
  and     cPar2B:    "\<And>P Q Q' a x C. \<lbrakk>Q \<longmapsto>a<\<nu>x> \<prec> Q'; x \<sharp> P; \<And>C. F C Q a x Q'\<rbrakk> \<Longrightarrow>
                                       F C (P \<parallel> Q) a x (P \<parallel> Q')"
  and     cResB:     "\<And>P P' a x y C. \<lbrakk>P \<longmapsto>a<\<nu>x> \<prec> P'; y \<noteq> a; y \<noteq> x; y \<sharp> C;
                                       \<And>C. F C P a x P'\<rbrakk> \<Longrightarrow> F C (<\<nu>y>P) a x (<\<nu>y>P')"
  and     cBang:     "\<And>P a x P' C. \<lbrakk>P \<parallel> !P \<longmapsto>a<\<nu>x> \<prec> P'; \<And>C. F C (P \<parallel> !P) a x P'\<rbrakk> \<Longrightarrow>
                                     F C (!P) a x P'"
  shows "F C P a x P'"
proof -
  from a \<open>x \<sharp> P\<close> show ?thesis
  proof(nominal_induct x2 == "a<\<nu>x> \<prec> P'" avoiding: C a x P' rule: transitions.strong_induct)
    case(Tau P)
    thus ?case by(simp add: residualInject)
  next
    case(Input P a x)
    thus ?case by(simp add: residualInject)
  next
    case(Output P a b)
    thus ?case by(simp add: residualInject)
  next
    case(Match P Rs b C a x)
    thus ?case 
      by(force intro: cMatch simp add: residualInject) 
  next
    case(Mismatch P Rs a b C c x)
    thus ?case 
      by(force intro: cMismatch simp add: residualInject) 
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
      by(simp add: residualInject name_abs_eq)+
    have "x \<sharp> <\<nu>b>P" by fact 
    with bineqx have "x \<sharp> P" by(simp add: name_fresh_abs)
    have aineqb: "a \<noteq> b" by fact
    
    have PTrans: "P \<longmapsto>a[b] \<prec> P'" by fact
    with \<open>x \<sharp> P\<close> have xineqa: "x \<noteq> a" by(force dest: freshFreeDerivative)
    from PTrans have "([(b, x)] \<bullet> P) \<longmapsto>[(b, x)] \<bullet> (a[b] \<prec> P')" by(rule transitions.eqvt)
    with P'eqP'' xineqa aineqb have Trans: "([(b, x)] \<bullet> P) \<longmapsto>a[x] \<prec> P''"
      by(auto simp add: name_calc)
    hence "F C (<\<nu>x>([(b, x)] \<bullet> P)) a x P''" using xineqa by(blast intro: cOpen)
    with \<open>x \<sharp> P\<close> aeqa' show ?case by(simp add: alphaRes)
  next
    case(Par1B P a x P' Q C a' x' P'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (P' \<parallel> Q) = a'<\<nu>x'> \<prec> P''" by fact
    hence aeqa': "a = BoundOutputS a'" by(simp add: residualInject)
    have "x \<sharp> Q" by fact
    have "x' \<sharp> P \<parallel> Q" by fact
    hence "x' \<sharp> P" and "x' \<sharp> Q" by simp+
    have P''eq: "P'' = ([(x, x')] \<bullet> P') \<parallel> Q"
    proof -
      from Eq xineqx' have "(P' \<parallel> Q) = [(x, x')] \<bullet> P''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (P' \<parallel> Q)) = P''" by simp
      with \<open>x' \<sharp> Q\<close>\<open>x \<sharp> Q\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed
    
    have "x \<sharp> P''" by fact
    with P''eq \<open>x \<noteq> x'\<close> have "x' \<sharp> P'" by(simp add: name_fresh_left name_calc)

    have "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'" by fact
    with \<open>x' \<sharp> P'\<close> aeqa' have "P \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C P a' x' ([(x, x')] \<bullet> P')"
    proof -
      fix C
      have "\<And>C a' x' P''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<\<nu>x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> P'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C P a' x' ([(x, x')] \<bullet> P')" using \<open>x' \<sharp> P\<close> aeqa' by blast 
    qed
    ultimately have "F C (P \<parallel> Q) a' x' (([(x, x')] \<bullet> P') \<parallel> Q)" using \<open>x' \<sharp> Q\<close>aeqa'
      by(blast intro: cPar1B)
    with P''eq show ?case by simp
  next
    case(Par1F P P' Q \<alpha>)
    thus ?case by(simp add: residualInject)
  next
    case(Par2B Q a x Q' P C a' x' Q'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (P \<parallel> Q') = a'<\<nu>x'> \<prec> Q''" by fact
    hence aeqa': "a = BoundOutputS a'" by(simp add: residualInject)
    have "x \<sharp> P" by fact
    have "x' \<sharp> P \<parallel> Q" by fact
    hence "x' \<sharp> P" and "x' \<sharp> Q" by simp+
    have Q''eq: "Q'' = P \<parallel> ([(x, x')] \<bullet> Q')"
    proof -
      from Eq xineqx' have "(P \<parallel> Q') = [(x, x')] \<bullet> Q''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (P \<parallel> Q')) = Q''" by simp
      with \<open>x' \<sharp> P\<close> \<open>x \<sharp> P\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed
    
    have "x \<sharp> Q''" by fact
    with Q''eq \<open>x \<noteq> x'\<close> have "x' \<sharp> Q'" by(simp add: name_fresh_left name_calc)

    have "Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> Q'" by fact
    with \<open>x' \<sharp> Q'\<close> aeqa' have "Q \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> Q')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C Q a' x' ([(x, x')] \<bullet> Q')"
    proof -
      fix C
      have "\<And>C a' x' Q''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> Q' = a'<\<nu>x'> \<prec> Q''; x' \<sharp> Q\<rbrakk> \<Longrightarrow> F C Q a' x' Q''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> Q'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> Q' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> Q')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C Q a' x' ([(x, x')] \<bullet> Q')" using \<open>x' \<sharp> Q\<close>aeqa' by blast 
    qed
    ultimately have "F C (P \<parallel> Q) a' x' (P \<parallel> ([(x, x')] \<bullet> Q'))" using \<open>x' \<sharp> P\<close>
      by(blast intro: cPar2B)
    with Q''eq show ?case by simp
  next
    case(Par2F P P' Q \<alpha>)
    thus ?case by(simp add: residualInject)
  next
    case(Comm1 P P' Q Q' a b x)
    thus ?case by(simp add: residualInject)
  next
    case(Comm2 P P' Q Q' a b x)
    thus ?case by(simp add: residualInject)
  next
    case(Close1 P P' Q Q' a x y)
    thus ?case by(simp add: residualInject)
  next
    case(Close2 P P' Q Q' a x y)
    thus ?case by(simp add: residualInject)
  next
    case(ResB P a x P' y C a' x' P'')
    have "x \<sharp> x'" by fact hence xineqx': "x \<noteq> x'" by simp
    moreover have Eq: "a\<guillemotleft>x\<guillemotright> \<prec> (<\<nu>y>P') = a'<\<nu>x'> \<prec> P''" by fact
    hence aeqa': "a = BoundOutputS a'" by(simp add: residualInject)
    have "y \<sharp> x'" by fact hence yineqx': "y \<noteq> x'" by simp
    moreover have "x' \<sharp> <\<nu>y>P" by fact
    ultimately have "x' \<sharp> P" by(simp add: name_fresh_abs)
    have "y \<noteq> x" and "y \<sharp> a" and yFreshC: "y \<sharp> C" by fact+

    have P''eq: "P'' = <\<nu>y>([(x, x')] \<bullet> P')"
    proof -
      from Eq xineqx' have "<\<nu>y>P' = [(x, x')] \<bullet> P''"
        by(simp add: residualInject name_abs_eq)
      hence "([(x, x')] \<bullet> (<\<nu>y>P')) = P''" by simp
      with yineqx' \<open>y \<noteq> x\<close> show ?thesis by(simp add: name_fresh_fresh)
    qed

    have "x \<sharp> P''" by fact
    with P''eq \<open>y \<noteq> x\<close> \<open>x \<noteq> x'\<close> have "x' \<sharp> P'" by(simp add: name_fresh_left name_calc name_fresh_abs)

    have "P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'" by fact
    with \<open>x' \<sharp> P'\<close> aeqa' have "P \<longmapsto>a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
      by(simp add: alphaBoundResidual)
    moreover have "\<And>C. F C P a' x' ([(x, x')] \<bullet> P')"
    proof -
      fix C
      have "\<And>C a' x' P''. \<lbrakk>a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<\<nu>x'> \<prec> P''; x' \<sharp> P\<rbrakk> \<Longrightarrow> F C P a' x' P''" by fact
      moreover with aeqa' xineqx' \<open>x' \<sharp> P'\<close> have "a\<guillemotleft>x\<guillemotright> \<prec> P' = a'<\<nu>x'> \<prec> ([(x, x')] \<bullet> P')"
        by(simp add: residualInject name_abs_eq name_fresh_left name_calc)
      ultimately show "F C P a' x' ([(x, x')] \<bullet> P')" using \<open>x' \<sharp> P\<close> aeqa' by blast 
    qed
    ultimately have "F C (<\<nu>y>P) a' x' (<\<nu>y>([(x, x')] \<bullet> P'))" using yineqx' \<open>y \<sharp> a\<close> yFreshC aeqa'
      by(force intro: cResB)
    with P''eq show ?case by simp
  next
    case(ResF P P' \<alpha> y)
    thus ?case by(simp add: residualInject)
  next
    case(Bang P Rs)
    thus ?case by(force intro: cBang)
  qed
qed

lemma tauInduct[consumes 1, case_names Tau Match Mismatch Sum1 Sum2 Par1 Par2 Comm1 Comm2 Close1 Close2 Res Bang]:
  fixes P  :: pi
  and   P' :: pi
  and   F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> pi \<Rightarrow> bool"
  and   C  :: "'a::fs_name"

  assumes Trans:  "P \<longmapsto>\<tau> \<prec> P'"
  and     "\<And>P C. F C (\<tau>.(P)) P"
  and     "\<And>P P' c C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C ([c\<frown>c]P) P'"
  and     "\<And>P P' c d C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'; c \<noteq> d\<rbrakk> \<Longrightarrow> F C ([c\<noteq>d]P) P'"
  and     "\<And>P P' Q C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) P'"
  and     "\<And>Q Q' P C. \<lbrakk>Q \<longmapsto>\<tau> \<prec> Q'; \<And>C. F C Q Q'\<rbrakk> \<Longrightarrow> F C (P \<oplus> Q) Q'"
  and     "\<And>P P' Q C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C P P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P' \<parallel> Q)"
  and     "\<And>Q Q' P C. \<lbrakk>Q \<longmapsto>\<tau> \<prec> Q'; \<And>C. F C Q Q'\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P \<parallel> Q')"
  and     "\<And>P a x P' Q b Q' C. \<lbrakk>P \<longmapsto>(BoundR (InputS a) x P'); Q \<longmapsto>OutputR a b \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<sharp> C\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P'[x::=b] \<parallel> Q')"
  and     "\<And>P a b P' Q x Q' C. \<lbrakk>P \<longmapsto>OutputR a b \<prec> P'; Q \<longmapsto>(BoundR (InputS a) x Q'); x \<sharp> P; x \<sharp> Q; x \<sharp> C\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (P' \<parallel> Q'[x::=b])"
  and     "\<And>P a x P' Q y Q' C. \<lbrakk>P \<longmapsto>(BoundR (InputS a) x P'); Q \<longmapsto>a<\<nu>y> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<sharp> C; y \<sharp> P; y \<sharp> Q; y \<sharp> C; x \<noteq> y\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (<\<nu>y>(P'[x::=y] \<parallel> Q'))"
  and     "\<And>P a y P' Q x Q' C. \<lbrakk>P \<longmapsto>a<\<nu>y> \<prec> P'; Q \<longmapsto>(BoundR (InputS a) x Q'); x \<sharp> P; x \<sharp> Q; x \<sharp> C; y \<sharp> P; y \<sharp> Q; y \<sharp> C; x \<noteq> y\<rbrakk> \<Longrightarrow> F C (P \<parallel> Q) (<\<nu>y>(P' \<parallel> Q'[x::=y]))"
  and     "\<And>P P' x C. \<lbrakk>P \<longmapsto>\<tau> \<prec> P'; x \<sharp> C; \<And>C. F C P P'\<rbrakk> \<Longrightarrow>
                        F C (<\<nu>x>P) (<\<nu>x>P')"
  and     "\<And>P P' C. \<lbrakk>P \<parallel> !P \<longmapsto>\<tau> \<prec> P'; \<And>C. F C (P \<parallel> !P) P'\<rbrakk> \<Longrightarrow> F C (!P) P'"

  shows "F C P P'"
proof -
  from Trans show ?thesis
    by(nominal_induct x2=="\<tau> \<prec> P'" avoiding: C arbitrary: P' rule: transitions.strong_induct,
       auto simp add: residualInject intro: assms)
qed

inductive bangPred :: "pi \<Rightarrow> pi \<Rightarrow> bool"
where
  aux1: "bangPred P (!P)"
| aux2: "bangPred P (P \<parallel> !P)"

inductive_cases nilCases'[simplified pi.distinct residual.distinct]: "\<zero> \<longmapsto> Rs"
inductive_cases tauCases'[simplified pi.distinct residual.distinct]: "\<tau>.(P) \<longmapsto> Rs"
inductive_cases inputCases'[simplified pi.inject residualInject]: "a<b>.P \<longmapsto> Rs"
inductive_cases outputCases'[simplified pi.inject residualInject]: "a{b}.P \<longmapsto> Rs"
inductive_cases matchCases'[simplified pi.inject residualInject]: "[a\<frown>b]P \<longmapsto> Rs"
inductive_cases mismatchCases'[simplified pi.inject residualInject]: "[a\<noteq>b]P \<longmapsto> Rs"
inductive_cases sumCases'[simplified pi.inject residualInject]: "P \<oplus> Q \<longmapsto> Rs"
inductive_cases parCasesB'[simplified pi.distinct residual.distinct]: "P \<parallel> Q \<longmapsto> b\<guillemotleft>y\<guillemotright> \<prec> P'"
inductive_cases parCasesF'[simplified pi.distinct residual.distinct]: "P \<parallel> Q \<longmapsto> \<alpha> \<prec> P'"
inductive_cases resCases'[simplified pi.distinct residual.distinct]: "<\<nu>x>P \<longmapsto> Rs"
inductive_cases resCasesB'[simplified pi.distinct residual.distinct]: "<\<nu>x'>P \<longmapsto> a\<guillemotleft>y'\<guillemotright> \<prec> P'"
inductive_cases resCasesF'[simplified pi.distinct residual.distinct]: "<\<nu>x>P \<longmapsto> \<alpha> \<prec> P'"
inductive_cases bangCases[simplified pi.distinct residual.distinct]: "!P \<longmapsto> Rs"

lemma tauCases[consumes 1, case_names cTau]:
  fixes P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "\<tau>.(P) \<longmapsto>\<alpha> \<prec> P'"
  and "\<lbrakk>\<alpha> = \<tau>; P = P'\<rbrakk> \<Longrightarrow> Prop (\<tau>) P"

  shows "Prop \<alpha> P'"
using assms
by(erule_tac tauCases', auto simp add: pi.inject residualInject)

lemma outputCases[consumes 1, case_names cOutput]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>\<alpha> \<prec> P'"
  and "\<lbrakk>\<alpha> = a[b]; P = P'\<rbrakk> \<Longrightarrow> Prop (a[b]) P"

  shows "Prop \<alpha> P'"
using assms
by(erule_tac outputCases', auto simp add: residualInject)

lemma zeroTrans[dest]:
  fixes Rs :: residual

  assumes "\<zero> \<longmapsto> Rs"

  shows "False"
using assms
by(induct rule: nilCases', auto)

lemma resZeroTrans[dest]:
  fixes x  :: name
  and   Rs :: residual

  assumes "<\<nu>x>\<zero> \<longmapsto> Rs"

  shows "False"
using assms
by(induct rule: resCases', auto simp add: pi.inject alpha')

lemma matchTrans[dest]:
  fixes a   :: name
  and   b   :: name
  and   P   :: pi
  and   Rs  :: residual

  assumes "[a\<frown>b]P \<longmapsto> Rs"
  and     "a\<noteq>b"

  shows "False"
using assms
by(induct rule: matchCases', auto)

lemma mismatchTrans[dest]:
  fixes a   :: name
  and   P   :: pi
  and   Rs  :: residual

  assumes "[a\<noteq>a]P \<longmapsto> Rs"

  shows "False"
using assms
by(induct rule: mismatchCases', auto)

lemma inputCases[consumes 4, case_names cInput]:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   P' :: pi

  assumes Input: "a<x>.P \<longmapsto> b\<guillemotleft>y\<guillemotright> \<prec> yP'"
  and     "y \<noteq> a"
  and     "y \<noteq> x"
  and     "y \<sharp> P"
  and     A:     "\<lbrakk>b = InputS a; yP' = ([(x, y)] \<bullet> P)\<rbrakk>  \<Longrightarrow> Prop (InputS a) y ([(x, y)] \<bullet> P)"

  shows "Prop b y yP'"
proof -
  note assms
  moreover from Input \<open>y \<noteq> a\<close> \<open>y \<noteq> x\<close> \<open>y \<sharp> P\<close> have "y \<sharp> b"
    by(force dest: freshBoundDerivative simp add: abs_fresh)
  moreover obtain z::name where "z \<noteq> y" and "z \<noteq> x" and "z \<sharp> P" and "z \<noteq> a" and "z \<sharp> b" and "z \<sharp> yP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  moreover obtain z'::name where "z' \<noteq> y" and "z' \<noteq> x" and "z' \<noteq> z" and "z' \<sharp> P" and "z' \<noteq> a" and "z' \<sharp> b" and "z' \<sharp> yP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  ultimately show ?thesis
    by(cases rule: transitions.strong_cases[where x=y and b=z and xa=z and xb=z and xc=z and xd=z and xe=z
                                            and xf=z and xg=z and y=z' and ya=z' and yb=y and yc=z'])
      (auto simp add: pi.inject residualInject alpha abs_fresh fresh_prod fresh_left calc_atm)+
qed

lemma tauBoundTrans[dest]:
  fixes P  :: pi
  and   a  :: subject
  and   x  :: name
  and   P' :: pi

  assumes "\<tau>.(P) \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'"

  shows False
using assms
by - (ind_cases "\<tau>.(P) \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> P'") 

lemma tauOutputTrans[dest]:
  fixes P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "\<tau>.(P) \<longmapsto>a[b] \<prec> P'"

  shows False
using assms
by - (ind_cases "\<tau>.(P) \<longmapsto>a[b] \<prec> P'", auto simp add: residualInject) 

lemma inputFreeTrans[dest]:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  
  assumes "a<x>.P \<longmapsto>\<alpha> \<prec> P'"

  shows False
using assms
by - (ind_cases "a<x>.P \<longmapsto>\<alpha> \<prec> P'")

lemma inputBoundOutputTrans[dest]:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   b  :: name
  and   y  :: name
  and   P' :: pi

  assumes "a<x>.P \<longmapsto>b<\<nu>y> \<prec> P'"

  shows False
using assms
by - (ind_cases "a<x>.P \<longmapsto>b<\<nu>y> \<prec> P'", auto simp add: residualInject)

lemma outputTauTrans[dest]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>\<tau> \<prec> P'"

  shows False
using assms
by - (ind_cases "a{b}.P \<longmapsto>\<tau> \<prec> P'", auto simp add: residualInject)

lemma outputBoundTrans[dest]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   c  :: subject
  and   x  :: name
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'"

  shows False
using assms
by - (ind_cases "a{b}.P \<longmapsto>c\<guillemotleft>x\<guillemotright> \<prec> P'")

lemma outputIneqTrans[dest]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   c  :: name
  and   d  :: name
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>c[d] \<prec> P'"
  and     "a \<noteq> c \<or> b \<noteq> d"

  shows "False"
using assms
by - (ind_cases "a{b}.P \<longmapsto>c[d] \<prec> P'", auto simp add: residualInject pi.inject alpha')

lemma outputFreshTrans[dest]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi

  assumes "a{b}.P \<longmapsto>\<alpha> \<prec> P'"
  and     "a \<sharp> \<alpha> \<or> b \<sharp> \<alpha>"

  shows "False"
using assms
by - (ind_cases "a{b}.P \<longmapsto>\<alpha> \<prec> P'", auto simp add: residualInject pi.inject alpha')

lemma inputIneqTrans[dest]:
  fixes a  :: name
  and   x  :: name
  and   P  :: pi
  and   b  :: subject
  and   y  :: name
  and   P' :: pi

  assumes "a<x>.P \<longmapsto>b\<guillemotleft>y\<guillemotright> \<prec> P'"
  and     "a \<sharp> b"

  shows "False"
using assms
by - (ind_cases "a<x>.P \<longmapsto>b\<guillemotleft>y\<guillemotright> \<prec> P'", auto simp add: residualInject pi.inject)

lemma resTauBoundTrans[dest]:
  fixes x  :: name
  and   P  :: pi
  and   a  :: subject
  and   y  :: name
  and   P' :: pi

  assumes "<\<nu>x>\<tau>.(P) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>\<tau>.(P) \<longmapsto>a\<guillemotleft>y\<guillemotright> \<prec> P'", auto simp add: residualInject pi.inject alpha')

lemma resTauOutputTrans[dest]:
  fixes x  :: name
  and   P  :: pi
  and   a  :: name
  and   b  :: name
  and   P' :: pi

  assumes "<\<nu>x>\<tau>.(P) \<longmapsto>a[b] \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>\<tau>.(P) \<longmapsto>a[b] \<prec> P'", auto simp add: residualInject pi.inject alpha')

lemma resInputFreeTrans[dest]:
  fixes x  :: name
  fixes a  :: name
  and   y  :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  
  assumes "<\<nu>x>a<y>.P \<longmapsto>\<alpha> \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>a<y>.P \<longmapsto>\<alpha> \<prec> P'", auto simp add: pi.inject residualInject alpha')

lemma resInputBoundOutputTrans[dest]:
  fixes x  :: name
  and   a  :: name
  and   y  :: name
  and   P  :: pi
  and   b  :: name
  and   z  :: name
  and   P' :: pi

  assumes "<\<nu>x>a<y>.P \<longmapsto>b<\<nu>z> \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>a<y>.P \<longmapsto>b<\<nu>z> \<prec> P'", auto simp add: pi.inject residualInject alpha')

lemma resOutputTauTrans[dest]:
  fixes x  :: name
  and   a  :: name
  and   b  :: name
  and   P  :: pi
  and   P' :: pi

  assumes "<\<nu>x>a{b}.P \<longmapsto>\<tau> \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>a{b}.P \<longmapsto>\<tau> \<prec> P'", auto simp add: residualInject pi.inject alpha')

lemma resOutputInputTrans[dest]:
  fixes x  :: name
  and   a  :: name
  and   b  :: name
  and   P  :: pi
  and   c  :: name
  and   y  :: name
  and   P' :: pi

  assumes "<\<nu>x>a{b}.P \<longmapsto>c<y> \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>a{b}.P \<longmapsto>c<y> \<prec> P'", auto simp add: pi.inject residualInject alpha')

lemma resOutputOutputTrans[dest]:
  fixes x  :: name
  and   a  :: name
  and   P  :: pi
  and   b  :: name
  and   y  :: name
  and   P' :: pi
  
  assumes "<\<nu>x>a{x}.P \<longmapsto>b[y] \<prec> P'"

  shows False
using assms
by - (ind_cases "<\<nu>x>a{x}.P \<longmapsto>b[y] \<prec> P'", auto simp add: pi.inject residualInject alpha' calc_atm)

lemma resTrans[dest]:
  fixes x  :: name
  and   b  :: name
  and   Rs :: residual
  and   y  :: name

  shows "<\<nu>x>x{b}.P \<longmapsto> Rs \<Longrightarrow> False"
  and   "<\<nu>x>x<y>.P \<longmapsto> Rs \<Longrightarrow> False"
apply(ind_cases "<\<nu>x>x{b}.P \<longmapsto> Rs", auto simp add: pi.inject alpha' calc_atm)
by(ind_cases "<\<nu>x>x<y>.P \<longmapsto> Rs", auto simp add: pi.inject alpha' calc_atm abs_fresh fresh_left)

lemma matchCases[consumes 1, case_names cMatch]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   Rs :: residual
  and   F  :: "name \<Rightarrow> name \<Rightarrow> bool"

  assumes "[a\<frown>b]P \<longmapsto> Rs"
  and     "\<lbrakk>P \<longmapsto> Rs; a = b\<rbrakk> \<Longrightarrow> F a a"

  shows "F a b"
using assms
by(induct rule: matchCases', auto)

lemma mismatchCases[consumes 1, case_names cMismatch]:
  fixes a  :: name
  and   b  :: name
  and   P  :: pi
  and   Rs :: residual
  and   F  :: "name \<Rightarrow> name \<Rightarrow> bool"

  assumes Trans:  "[a\<noteq>b]P \<longmapsto> Rs"
  and     cMatch: "\<lbrakk>P \<longmapsto> Rs; a \<noteq> b\<rbrakk> \<Longrightarrow> F a b"

  shows "F a b"
using assms
by(induct rule: mismatchCases', auto)

lemma sumCases[consumes 1, case_names cSum1 cSum2]:
  fixes P  :: pi
  and   Q  :: pi
  and   Rs :: residual

  assumes Trans: "P \<oplus> Q \<longmapsto> Rs"
  and     cSum1: "P \<longmapsto> Rs \<Longrightarrow> Prop"
  and     cSum2: "Q \<longmapsto> Rs \<Longrightarrow> Prop"

  shows Prop
using assms
by(induct rule: sumCases', auto)

lemma name_abs_alpha:
  fixes a :: name
  and   b :: name
  and   P :: pi
  
  assumes "b \<sharp> P"

  shows "[a].P = [b].([(a, b)] \<bullet> P)"
proof(cases "a=b", auto)
  assume "a \<noteq> b"
  with assms show ?thesis
    by(force intro: abs_fun_eq3[OF pt_name_inst, OF at_name_inst]
             simp add: name_swap name_calc name_fresh_left)
qed

lemma parCasesB[consumes 3, case_names cPar1 cPar2]:
  fixes P   :: pi
  and   Q   :: pi
  and   a   :: subject
  and   x   :: name
  and   PQ' :: pi
  and   C   :: "'a::fs_name"
  
  assumes "P \<parallel> Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> PQ'"
  and     "x \<sharp> P"
  and     "x \<sharp> Q"
  and     "\<And>P'. P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P' \<Longrightarrow> Prop (P' \<parallel> Q)"
  and     "\<And>Q'. Q \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> Q' \<Longrightarrow> Prop (P \<parallel> Q')"

  shows "Prop PQ'"
proof -
  note assms
  moreover from \<open>P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> PQ'\<close> \<open>x \<sharp> P\<close> \<open>x \<sharp> Q\<close> have "x \<sharp> a"
    by(force dest: freshBoundDerivative)
  moreover obtain y::name where "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> a" and "y \<sharp> PQ'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  moreover obtain z::name where "z \<noteq> y" and "z \<noteq> x" and "z \<sharp> P" and "z \<sharp> Q" and "z \<sharp> a" and "z \<sharp> PQ'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  ultimately show ?thesis
    by(cases rule: transitions.strong_cases[where x=y and b=y and xa=x and xb=x and xc=y and xd=y and xe=y
                                              and xf=y and xg=y and y=z and ya = z and yb=z and yc=z])
      (auto simp add: pi.inject residualInject alpha abs_fresh fresh_prod)+
qed


lemma parCasesF[consumes 1, case_names cPar1 cPar2 cComm1 cComm2 cClose1 cClose2]:
  fixes P  :: pi
  and   Q  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   C  :: "'a::fs_name"
  and   F  :: "freeRes \<Rightarrow> pi \<Rightarrow> bool"

  assumes Trans: "P \<parallel> Q \<longmapsto> \<alpha> \<prec> PQ'"
  and     icPar1F: "\<And>P'. \<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> F \<alpha> (P' \<parallel> Q)"
  and     icPar2F: "\<And>Q'. \<lbrakk>Q \<longmapsto> \<alpha> \<prec> Q'\<rbrakk> \<Longrightarrow> F \<alpha> (P \<parallel> Q')"
  and     icComm1: "\<And>P' Q' a b x. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a[b] \<prec> Q'; x \<sharp> P; x\<sharp> Q; x \<noteq> a; x \<noteq> b; x \<sharp> Q'; x \<sharp> C; \<alpha> = \<tau>\<rbrakk> \<Longrightarrow> F (\<tau>) (P'[x::=b] \<parallel> Q')"
  and     icComm2: "\<And>P' Q' a b x. \<lbrakk>P \<longmapsto> a[b] \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<noteq> b; x \<sharp> P'; x \<sharp> C; \<alpha> = \<tau>\<rbrakk> \<Longrightarrow> F (\<tau>) (P' \<parallel> Q'[x::=b])"
  and     icClose1: "\<And>P' Q' a x y. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; Q \<longmapsto> a<\<nu>y> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<noteq> y; x \<sharp> Q'; y \<sharp> P; y \<sharp> Q; y \<noteq> a; y \<sharp> P'; x \<sharp> C; y \<sharp> C; \<alpha> = \<tau>\<rbrakk> \<Longrightarrow> 
                                     F (\<tau>) (<\<nu>y>(P'[x::=y] \<parallel> Q'))"
  and     icClose2: "\<And>P' Q' a x y. \<lbrakk>P \<longmapsto> a<\<nu>y> \<prec> P'; Q \<longmapsto> a<x> \<prec> Q'; x \<sharp> P; x \<sharp> Q; x \<noteq> a; x \<noteq> y; x \<sharp> P'; y \<sharp> P; y \<sharp> Q; y \<noteq> a; y \<sharp> Q'; x \<sharp> C; y \<sharp> C; \<alpha> = \<tau>\<rbrakk> \<Longrightarrow>
                                      F (\<tau>) (<\<nu>y>(P' \<parallel> Q'[x::=y]))"

  shows "F \<alpha> PQ'"
proof -
  note assms
  moreover obtain x::name where "x \<sharp> P" and "x \<sharp> Q" and "x \<sharp> \<alpha>" and "x \<sharp> PQ'" and "x \<sharp> C"
    by(generate_fresh "name", auto simp add: fresh_prod)
  moreover obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> \<alpha>" and "y \<sharp> PQ'" and "y \<sharp> C" and "x \<noteq> y"
    by(generate_fresh "name", auto simp add: fresh_prod)
  ultimately show ?thesis
    by(cases rule: transitions.strong_cases[where x=x and b=x and xa=x and xb=x and xc=x and xd=x and xe=x
                                              and xf=x and xg=x and y=y and ya=y and yb=y and yc=y])
      (auto simp add: pi.inject residualInject alpha abs_fresh fresh_prod)+
qed

lemma resCasesF[consumes 1, case_names cRes]:
  fixes x  :: name
  and   P  :: pi
  and   \<alpha>  :: freeRes
  and   P' :: pi
  and   C  :: "'a::fs_name"

  assumes "<\<nu>x>P \<longmapsto> \<alpha> \<prec> xP'"
  and     "\<And>P'. \<lbrakk>P \<longmapsto> \<alpha> \<prec> P'; x \<sharp> \<alpha>\<rbrakk> \<Longrightarrow> F (<\<nu>x>P')"

  shows "F xP'"
proof -
  note assms
  moreover from \<open><\<nu>x>P \<longmapsto>\<alpha> \<prec> xP'\<close> have "x \<sharp> \<alpha>" and "x \<sharp> xP'"
    by(force dest: freshFreeDerivative simp add: abs_fresh)+
  moreover obtain y::name where "y \<noteq> x" and "y \<sharp> P" and "y \<sharp> \<alpha>" and "y \<sharp> xP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  moreover obtain z::name where "z \<noteq> y" and "z \<noteq> x" and "z \<sharp> P" and "z \<sharp> \<alpha>" and "z \<sharp> xP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  ultimately show ?thesis
    by(cases rule: transitions.strong_cases[where x=y and b=y and xa=y and xb=y and xc=y and xd=y and xe=y
                                              and xf=y and xg=y and y=z and ya=z and yb=z and yc=x])
      (auto simp add: pi.inject residualInject alpha abs_fresh fresh_prod)+
qed

lemma resCasesB[consumes 3, case_names cOpen cRes]:
  fixes x :: name
  and   P  :: pi
  and   a  :: subject
  and   y :: name
  and   yP' :: pi
  and   C  :: "'a::fs_name"

  assumes Trans:  "<\<nu>y>P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> yP'"
  and     xineqy: "x \<noteq> y"
  and     xineqy: "x \<sharp> P"
  and     rcOpen: "\<And>b P'. \<lbrakk>P \<longmapsto>b[y] \<prec> P'; b \<noteq> y; a = BoundOutputS b\<rbrakk> \<Longrightarrow> F (BoundOutputS b) ([(x, y)] \<bullet> P')"
  and     rcResB: "\<And>P'. \<lbrakk>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'; y \<sharp> a\<rbrakk> \<Longrightarrow> F a (<\<nu>y>P')"

  shows "F a yP'"
proof -
  note assms
  moreover from \<open><\<nu>y>P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> yP'\<close> \<open>x \<noteq> y\<close> have "y \<sharp> a" and "y \<sharp> yP'"
    by(force dest: freshBoundDerivative simp add: abs_fresh)+
  moreover from  \<open><\<nu>y>P \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> yP'\<close> \<open>x \<sharp> P\<close> have "x \<sharp> a"
    by(force dest: freshBoundDerivative simp add: abs_fresh)+
  moreover obtain z::name where "z \<noteq> y" and "z \<noteq> x" and "z \<sharp> P" and "z \<sharp> a" and "z \<sharp> yP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  moreover obtain z'::name where "z' \<noteq> y" and "z' \<noteq> x" and "z' \<noteq> z" and "z' \<sharp> P" and "z' \<sharp> a" and "z' \<sharp> yP'" 
    by(generate_fresh "name", auto simp add: fresh_prod)
  ultimately show ?thesis
    by(cases rule: transitions.strong_cases[where x=z and b=y and xa=z and xb=z and xc=z and xd=z and xe=z
                                              and xf=z and xg=x and y=z' and ya=z' and yb=y and yc=z'])
      (auto simp add: pi.inject residualInject alpha abs_fresh fresh_prod fresh_left calc_atm)+
qed

lemma bangInduct[consumes 1, case_names cPar1B cPar1F cPar2B cPar2F cComm1 cComm2 cClose1 cClose2 cBang]:
  fixes F  :: "'a::fs_name \<Rightarrow> pi \<Rightarrow> residual \<Rightarrow> bool"
  and   P  :: pi
  and   Rs :: residual
  and   C  :: "'a::fs_name"

  assumes Trans:  "!P \<longmapsto> Rs"
  and     cPar1B: "\<And>a x P' C. \<lbrakk>P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'; x \<sharp> P; x \<sharp> C\<rbrakk> \<Longrightarrow> F C (P \<parallel> !P) (a\<guillemotleft>x\<guillemotright> \<prec> P' \<parallel> !P)"
  and     cPar1F: "\<And>\<alpha> P' C. \<lbrakk>P \<longmapsto> \<alpha> \<prec> P'\<rbrakk> \<Longrightarrow> F C (P \<parallel> !P) (\<alpha> \<prec> P' \<parallel> !P)"
  and     cPar2B: "\<And>a x P' C. \<lbrakk>!P \<longmapsto> a\<guillemotleft>x\<guillemotright> \<prec> P'; x \<sharp> P; x \<sharp> C; \<And>C. F C (!P) (a\<guillemotleft>x\<guillemotright> \<prec> P')\<rbrakk> \<Longrightarrow> 
                               F C (P \<parallel> !P) (a\<guillemotleft>x\<guillemotright> \<prec> P \<parallel> P')"
  and     cPar2F: "\<And>\<alpha> P' C. \<lbrakk>!P \<longmapsto> \<alpha> \<prec> P'; \<And>C. F C (!P) (\<alpha> \<prec> P')\<rbrakk> \<Longrightarrow> F C (P \<parallel> !P) (\<alpha> \<prec> P \<parallel> P')"
  and     cComm1: "\<And>a x P' b P'' C. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; !P \<longmapsto> (OutputR a b) \<prec> P''; x \<sharp> C;
                                      \<And>C. F C (!P) ((OutputR a b) \<prec> P'')\<rbrakk> \<Longrightarrow>
                                      F C (P \<parallel> !P) (\<tau> \<prec> (P'[x::=b]) \<parallel> P'')"
  and     cComm2: "\<And>a b P' x P'' C. \<lbrakk>P \<longmapsto> (OutputR a b) \<prec> P'; !P \<longmapsto> a<x> \<prec> P''; x \<sharp> C; 
                                      \<And>C. F C (!P) (a<x> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                      F C (P \<parallel> !P) (\<tau> \<prec> P' \<parallel> (P''[x::=b]))"
  and     cClose1: "\<And>a x P' y P'' C. \<lbrakk>P \<longmapsto> a<x> \<prec> P'; !P \<longmapsto> a<\<nu>y> \<prec> P''; y \<sharp> P; x \<sharp> C; y \<sharp> C;
                                      \<And>C. F C (!P) (a<\<nu>y> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                      F C (P \<parallel> !P) (\<tau> \<prec> <\<nu>y>((P'[x::=y]) \<parallel> P''))"
  and     cClose2: "\<And>a y P' x P'' C. \<lbrakk>P \<longmapsto> a<\<nu>y> \<prec> P'; !P \<longmapsto> a<x> \<prec> P''; y \<sharp> P; x \<sharp> C; y \<sharp> C;
                                       \<And>C. F C (!P) (a<x> \<prec> P'')\<rbrakk> \<Longrightarrow>
                                       F C (P \<parallel> !P) (\<tau> \<prec> <\<nu>y>(P' \<parallel> (P''[x::=y])))"
  and     cBang: "\<And>Rs C. \<lbrakk>P \<parallel> !P \<longmapsto> Rs; \<And>C. F C (P \<parallel> !P) Rs\<rbrakk> \<Longrightarrow> F C (!P) Rs"

  shows "F C (!P) Rs"
proof -
  have "\<And>X Y C. \<lbrakk>X \<longmapsto> Y; bangPred P X\<rbrakk> \<Longrightarrow> F C X Y"
  proof -
    fix X Y C
    assume "X \<longmapsto> Y" and "bangPred P X"
    thus "F C X Y"
    proof(nominal_induct avoiding: C rule: transitions.strong_induct)
      case(Tau Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (\<tau>.(Pa))")
    next
      case(Input x a Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (a<x>.Pa)")
    next
      case(Output a b Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (a{b}.Pa)")
    next
      case(Match Pa Rs b)
      thus ?case
        apply -
        by(ind_cases "bangPred P ([b\<frown>b]Pa)")
    next
      case(Mismatch Pa Rs a b)
      thus ?case
        apply -
        by(ind_cases "bangPred P ([a\<noteq>b]Pa)")
    next
      case(Open Pa a b Pa')
      thus ?case
        apply -
        by(ind_cases "bangPred P (<\<nu>b>Pa)")
    next
      case(Sum1 Pa Rs Q)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<oplus> Q)")
    next
      case(Sum2 Q Rs Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<oplus> Q)")
    next
      case(Par1B Pa a x Pa' Q )
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cPar1B simp add: pi.inject)
    next
      case(Par1F Pa \<alpha> Pa' Q)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cPar1F simp add: pi.inject)
    next
      case(Par2B Qa a x Qa' Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Qa)", auto intro: cPar2B aux1 simp add: pi.inject)
    next
      case(Par2F Qa \<alpha> Qa' Pa)
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Qa)", auto intro: cPar2F aux1 simp add: pi.inject)
    next
      case(Comm1 Pa a x Pa' Q b Q')
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cComm1 aux1 simp add: pi.inject)
    next
      case(Comm2 Pa a b Pa' Q x Q')
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cComm2 aux1 simp add: pi.inject)
    next
      case(Close1 Pa a x Pa' Q y Q')
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cClose1 aux1 simp add: pi.inject)
    next
      case(Close2 Pa a y Pa' Q x Q')
      thus ?case
        apply -
        by(ind_cases "bangPred P (Pa \<parallel> Q)", auto intro: cClose2 aux1 simp add: pi.inject)
    next
      case(ResB Pa a x P' y)
      thus ?case
        apply -
        by(ind_cases "bangPred P (<\<nu>y>Pa)")
    next
      case(ResF Pa \<alpha> P' y)
      thus ?case
        apply -
        by(ind_cases "bangPred P (<\<nu>y>Pa)")
    next
      case(Bang Pa Rs)
      thus ?case
        apply -
        by(ind_cases "bangPred P (!Pa)", auto intro: cBang aux2 simp add: pi.inject)
    qed
  qed

  with Trans show ?thesis by(force intro: bangPred.aux1)
qed

end

