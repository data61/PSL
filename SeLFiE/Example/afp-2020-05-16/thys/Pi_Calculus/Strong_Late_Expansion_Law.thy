(* 
   Title: The pi-calculus   
   Author/Maintainer: Jesper Bengtson (jebe.dk), 2012
*)
theory Strong_Late_Expansion_Law
  imports Strong_Late_Bisim_SC
begin

nominal_primrec summands :: "pi \<Rightarrow> pi set" where 
  "summands \<zero> = {}"
| "summands (\<tau>.(P)) = {\<tau>.(P)}"
| "x \<sharp> a \<Longrightarrow> summands (a<x>.P) = {a<x>.P}"
| "summands (a{b}.P) = {a{b}.P}"
| "summands ([a\<frown>b]P) = {}"
| "summands ([a\<noteq>b]P) = {}"
| "summands (P \<oplus> Q) = (summands P) \<union> (summands Q)"
| "summands (P \<parallel> Q) = {}"
| "summands (<\<nu>x>P) = (if (\<exists>a P'. a \<noteq> x \<and> P = a{x}.P') then ({<\<nu>x>P}) else {})"
| "summands (!P) = {}"
apply(auto simp add: fresh_singleton name_fresh_abs fresh_set_empty fresh_singleton pi.fresh)
apply(finite_guess)+
by(fresh_guess)+

lemma summandsInput[simp]:
  fixes a :: name
  and   x :: name
  and   P :: pi

  shows "summands (a<x>.P) = {a<x>.P}"
proof -
  obtain y where yineqa: "y \<noteq> a" and yFreshP: "y \<sharp> P"
    by(force intro: name_exists_fresh[of "(a, P)"] simp add: fresh_prod)
  from yFreshP have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(simp add: alphaInput)
  with yineqa show ?thesis by simp
qed

lemma finiteSummands:
  fixes P :: pi
  
  shows "finite(summands P)"
by(induct P rule: pi.induct) auto

lemma boundSummandDest[dest]:
  fixes x  :: name
  and   y  :: name
  and   P' :: pi
  and   P  :: pi

  assumes "<\<nu>x>x{y}.P' \<in> summands P"
  
  shows False
using assms
by(induct P rule: pi.induct, auto simp add: if_split pi.inject name_abs_eq name_calc)

lemma summandFresh:
  fixes P :: pi
  and   Q :: pi
  and   x :: name

  assumes "P \<in> summands Q"
  and     "x \<sharp> Q"
  
  shows "x \<sharp> P"
using assms
by(nominal_induct Q avoiding: P rule: pi.strong_induct, auto simp add: if_split)

nominal_primrec hnf :: "pi \<Rightarrow> bool" where
  "hnf \<zero> = True"
| "hnf (\<tau>.(P)) = True"
| "x \<sharp> a \<Longrightarrow> hnf (a<x>.P) = True"
| "hnf (a{b}.P) = True"
| "hnf ([a\<frown>b]P) = False"
| "hnf ([a\<noteq>b]P) = False"
| "hnf (P \<oplus> Q) = ((hnf P) \<and> (hnf Q) \<and> P \<noteq> \<zero> \<and> Q \<noteq> \<zero>)"
| "hnf (P \<parallel> Q) = False"
| "hnf (<\<nu>x>P) = (\<exists>a P'. a \<noteq> x \<and> P = a{x}.P')"
| "hnf (!P) = False"
apply(auto simp add: fresh_bool)
apply(finite_guess)+
by(fresh_guess)+

lemma hnfInput[simp]:
  fixes a :: name
  and   x :: name
  and   P :: pi

  shows "hnf (a<x>.P)"
proof -
  obtain y where yineqa: "y \<noteq> a" and yFreshP: "y \<sharp> P"
    by(force intro: name_exists_fresh[of "(a, P)"] simp add: fresh_prod)
  from yFreshP have "a<x>.P = a<y>.([(x, y)] \<bullet> P)" by(simp add: alphaInput)
  with yineqa show ?thesis by simp
qed

lemma summandTransition:
  fixes P  :: pi
  and   a  :: name
  and   x  :: name
  and   b  :: name
  and   P' :: pi

  assumes "hnf P"

  shows "P \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands P)"
  and   "P \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands P)"
  and   "P \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands P)"
  and   "a \<noteq> x \<Longrightarrow> P \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands P)"
proof -
  from assms show "P \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands P)"
  proof(induct P rule: pi.induct)
    case PiNil
    show ?case by auto
  next
    case(Output a b P)
    show ?case by auto
  next
    case(Tau P)
    have "\<tau>.(P) \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> \<tau>.(P') \<in> summands (\<tau>.(P))"
      by(auto elim: tauCases simp add: pi.inject residual.inject)
    moreover have "\<tau>.(P') \<in> summands (\<tau>.(P)) \<Longrightarrow> \<tau>.(P) \<longmapsto>\<tau> \<prec> P'"
      by(auto simp add: pi.inject intro: transitions.Tau)
    ultimately show ?case by blast
  next
    case(Input a x P)
    show ?case by auto
  next
    case(Match a b P)
    have "hnf ([a\<frown>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Mismatch a b P)
    have "hnf ([a\<noteq>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Sum P Q) 
    have "hnf (P \<oplus> Q)" by fact
    hence Phnf: "hnf P" and Qhnf: "hnf Q" by simp+
    
    have IHP: "P \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands P)"
    proof -
      have "hnf P \<Longrightarrow> P \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands P)" by fact
      with Phnf show ?thesis by simp
    qed
    
    have IHQ: "Q \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands Q)"
    proof -
      have "hnf Q \<Longrightarrow> Q \<longmapsto>\<tau> \<prec> P' = (\<tau>.(P') \<in> summands Q)" by fact
      with Qhnf show ?thesis by simp
    qed

    from IHP IHQ have "P \<oplus> Q \<longmapsto>\<tau> \<prec> P' \<Longrightarrow> \<tau>.(P') \<in> summands (P \<oplus> Q)"
      by(erule_tac sumCases, auto)
    moreover from IHP IHQ have "\<tau>.(P') \<in> summands (P \<oplus> Q) \<Longrightarrow> P \<oplus> Q \<longmapsto>\<tau> \<prec> P'"
      by(auto dest: Sum1 Sum2)
    ultimately show ?case by blast
  next
    case(Par P Q)
    have "hnf (P \<parallel> Q)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Res x P)
    thus ?case by(auto elim: resCasesF)
  next
    case(Bang P)
    have "hnf (!P)" by fact
    hence False by simp
    thus ?case by simp
  qed
next
  from assms show "P \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands P)"
  proof(induct P rule: pi.induct)
    case PiNil
    show ?case by auto
  next
    case(Output c b P)
    show ?case by auto
  next
    case(Tau P)
    show ?case by auto
  next
    case(Input b y P)
    have "b<y>.P \<longmapsto>a<x> \<prec> P' \<Longrightarrow> a<x>.P' \<in> summands (b<y>.P)"
      by(auto elim: inputCases' simp add: pi.inject residual.inject)
    moreover have "a<x>.P' \<in> summands (b<y>.P) \<Longrightarrow> b<y>.P \<longmapsto>a<x> \<prec> P'"
      apply(auto simp add: pi.inject name_abs_eq intro: Late_Semantics.Input)
      apply(subgoal_tac "b<x> \<prec> [(x, y)] \<bullet> P = (b<y> \<prec> [(x, y)] \<bullet> [(x, y)] \<bullet> P)")
      apply(auto intro: Late_Semantics.Input)
      by(simp add: alphaBoundResidual name_swap)
    ultimately show ?case by blast
  next
    case(Match a b P)
    have "hnf ([a\<frown>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Mismatch a b P)
    have "hnf ([a\<noteq>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Sum P Q) 
    have "hnf (P \<oplus> Q)" by fact
    hence Phnf: "hnf P" and Qhnf: "hnf Q" by simp+
    
    have IHP: "P \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands P)"
    proof -
      have "hnf P \<Longrightarrow> P \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands P)" by fact
      with Phnf show ?thesis by simp
    qed
    
    have IHQ: "Q \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands Q)"
    proof -
      have "hnf Q \<Longrightarrow> Q \<longmapsto>a<x> \<prec> P' = (a<x>.P' \<in> summands Q)" by fact
      with Qhnf show ?thesis by simp
    qed

    from IHP IHQ have "P \<oplus> Q \<longmapsto>a<x> \<prec> P' \<Longrightarrow> a<x>.P' \<in> summands (P \<oplus> Q)"
      by(erule_tac sumCases, auto)
    moreover from IHP IHQ have "a<x>.P' \<in> summands (P \<oplus> Q) \<Longrightarrow> P \<oplus> Q \<longmapsto>a<x> \<prec> P'"
      by(auto dest: Sum1 Sum2)
    ultimately show ?case by blast
  next
    case(Par P Q)
    have "hnf (P \<parallel> Q)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Res y P)
    have "hnf(<\<nu>y>P)" by fact
    thus ?case by(auto simp add: if_split)
  next
    case(Bang P)
    have "hnf (!P)" by fact
    hence False by simp
    thus ?case by simp
  qed
next
  from assms show "P \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands P)"
  proof(induct P rule: pi.induct)
    case PiNil
    show ?case by auto
  next
    case(Output c d P)
    have "c{d}.P \<longmapsto>a[b] \<prec> P' \<Longrightarrow> a{b}.P' \<in> summands (c{d}.P)"
      by(auto elim: outputCases simp add: residual.inject pi.inject)
    moreover have "a{b}.P' \<in> summands (c{d}.P) \<Longrightarrow> c{d}.P \<longmapsto>a[b] \<prec> P'"
      by(auto simp add: pi.inject intro: transitions.Output)
    ultimately show ?case by blast
  next
    case(Tau P)
    show ?case by auto
  next
    case(Input c x P)
    show ?case by auto
  next
    case(Match a b P)
    have "hnf ([a\<frown>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Mismatch a b P)
    have "hnf ([a\<noteq>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Sum P Q) 
    have "hnf (P \<oplus> Q)" by fact
    hence Phnf: "hnf P" and Qhnf: "hnf Q" by simp+
    
    have IHP: "P \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands P)"
    proof -
      have "hnf P \<Longrightarrow> P \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands P)" by fact
      with Phnf show ?thesis by simp
    qed
    
    have IHQ: "Q \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands Q)"
    proof -
      have "hnf Q \<Longrightarrow> Q \<longmapsto>a[b] \<prec> P' = (a{b}.P' \<in> summands Q)" by fact
      with Qhnf show ?thesis by simp
    qed

    from IHP IHQ have "P \<oplus> Q \<longmapsto>a[b] \<prec> P' \<Longrightarrow> a{b}.P' \<in> summands (P \<oplus> Q)"
      by(erule_tac sumCases, auto)
    moreover from IHP IHQ have "a{b}.P' \<in> summands (P \<oplus> Q) \<Longrightarrow> P \<oplus> Q \<longmapsto>a[b] \<prec> P'"
      by(auto dest: Sum1 Sum2)
    ultimately show ?case by blast
  next
    case(Par P Q)
    have "hnf (P \<parallel> Q)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Res x P)
    have "hnf (<\<nu>x>P)" by fact
    thus ?case by(force elim: resCasesF outputCases simp add: if_split residual.inject)
  next
    case(Bang P)
    have "hnf (!P)" by fact
    hence False by simp
    thus ?case by simp
  qed
next
  assume "a\<noteq>x"
  with assms show "P \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands P)"
  proof(nominal_induct P avoiding: x P' rule: pi.strong_induct)
    case PiNil
    show ?case by auto
  next
    case(Output a b P)
    show ?case by auto 
  next
    case(Tau P)
    show ?case by auto
  next
    case(Input a x P)
    show ?case by auto
  next
    case(Match a b P)
    have "hnf ([a\<frown>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Mismatch a b P)
    have "hnf ([a\<noteq>b]P)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Sum P Q) 
    have "hnf (P \<oplus> Q)" by fact
    hence Phnf: "hnf P" and Qhnf: "hnf Q" by simp+
    have aineqx: "a \<noteq> x" by fact

    have IHP: "P \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands P)"
    proof -
      have "\<And>x P'. \<lbrakk>hnf P; a \<noteq> x\<rbrakk> \<Longrightarrow> P \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands P)" by fact
      with Phnf aineqx show ?thesis by simp
    qed
    
    have IHQ: "Q \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands Q)"
    proof -
      have "\<And>x Q'. \<lbrakk>hnf Q; a \<noteq> x\<rbrakk> \<Longrightarrow> Q \<longmapsto>a<\<nu>x> \<prec> P' = (<\<nu>x>a{x}.P' \<in> summands Q)" by fact
      with Qhnf aineqx show ?thesis by simp
    qed

    from IHP IHQ have "P \<oplus> Q \<longmapsto>a<\<nu>x> \<prec> P' \<Longrightarrow> <\<nu>x>a{x}.P' \<in> summands (P \<oplus> Q)"
      by(erule_tac sumCases, auto)
    moreover from IHP IHQ have "<\<nu>x>a{x}.P' \<in> summands (P \<oplus> Q) \<Longrightarrow> P \<oplus> Q \<longmapsto>a<\<nu>x> \<prec> P'"
      by(auto dest: Sum1 Sum2)
    ultimately show ?case by blast
  next
    case(Par P Q)
    have "hnf (P \<parallel> Q)" by fact
    hence False by simp
    thus ?case by simp
  next
    case(Res y P)
    have Phnf: "hnf (<\<nu>y>P)" by fact
    then obtain b P'' where bineqy: "b \<noteq> y" and PeqP'': "P = b{y}.P''"
      by auto
    have "y \<sharp> x" by fact hence xineqy:  "x \<noteq> y" by simp
    have yFreshP': "y \<sharp> P'" by fact
    have aineqx: "a\<noteq>x" by fact
    have "<\<nu>y>P \<longmapsto>a<\<nu>x> \<prec> P' \<Longrightarrow> (<\<nu>x>a{x}.P' \<in> summands (<\<nu>y>P))"
    proof -
      assume Trans: "<\<nu>y>P \<longmapsto>a<\<nu>x> \<prec> P'"
      hence  aeqb: "a = b" using xineqy bineqy PeqP''
        by(induct rule: resCasesB', auto elim: outputCases simp add: residual.inject alpha' abs_fresh pi.inject)

      have Goal: "\<And>x P'. \<lbrakk><\<nu>y>b{y}.P'' \<longmapsto>b<\<nu>x> \<prec> P'; x \<noteq> y; x \<noteq> b; x \<sharp> P''\<rbrakk> \<Longrightarrow>
                           <\<nu>x>b{x}.P' \<in> summands(<\<nu>y>b{y}.P'')"
      proof -
        fix x P'
        assume xFreshP'': "(x::name) \<sharp> P''" and xineqb: "x \<noteq> b"
        assume "<\<nu>y>b{y}.P'' \<longmapsto>b<\<nu>x> \<prec> P'" and xineqy: "x \<noteq> y"
        moreover from \<open>x \<noteq> b\<close> \<open>x \<sharp> P''\<close> \<open>x \<noteq> y\<close> have "x \<sharp> b{y}.P''" by simp
        ultimately show "<\<nu>x>b{x}.P' \<in> summands (<\<nu>y>b{y}.P'')"
        proof(induct rule: resCasesB)
          case(cOpen a P''')
          have "BoundOutputS b = BoundOutputS a" by fact hence beqa: "b = a" by simp
          have Trans: "b{y}.P'' \<longmapsto>a[y] \<prec> P'''" by fact
          with PeqP'' have P''eqP''': "P'' = P'''"
            by(force elim: outputCases simp add: residual.inject)
          with bineqy xineqy xFreshP'' have "y \<sharp> b{x}.([(x, y)] \<bullet> P''')"
            by(simp add: name_fresh_abs name_calc name_fresh_left)
          with bineqy Phnf PeqP'' P''eqP''' xineqb show ?case 
            by(simp only: alphaRes, simp add: name_calc)
        next
          case(cRes P''')
          have "b{y}.P'' \<longmapsto>b<\<nu>x> \<prec> P'''" by fact
          hence False by auto
          thus ?case by simp
        qed     
      qed
      obtain z where zineqx: "z \<noteq> x" and zineqy: "z \<noteq> y" and zFreshP'': "z \<sharp> P''" 
                 and zineqb: "z \<noteq> b" and zFreshP': "z \<sharp> P'"
        by(force intro: name_exists_fresh[of "(x, y, b, P'', P')"] simp add: fresh_prod)

      from zFreshP' aeqb PeqP'' Trans have Trans': "<\<nu>y>b{y}.P'' \<longmapsto>b<\<nu>z> \<prec> [(z, x)] \<bullet> P'"
        by(simp add: alphaBoundResidual name_swap)
      hence "<\<nu>z>b{z}.([(z, x)] \<bullet> P') \<in> summands (<\<nu>y>b{y}.P'')" using zineqy zineqb zFreshP''
        by(rule Goal)
      moreover from bineqy zineqx zFreshP' aineqx aeqb have "x \<sharp> b{z}.([(z, x)] \<bullet> P')"
        by(simp add: name_fresh_left name_calc)
      ultimately have "<\<nu>x>b{x}.P' \<in> summands (<\<nu>y>b{y}.P'')" using zineqb
        by(simp add: alphaRes name_calc)
      with aeqb PeqP'' show ?thesis by blast
    qed
    moreover have "<\<nu>x>a{x}.P' \<in> summands(<\<nu>y>P) \<Longrightarrow> <\<nu>y>P \<longmapsto>a<\<nu>x> \<prec> P'"
    proof -
      assume "<\<nu>x>a{x}.P' \<in> summands(<\<nu>y>P)"
      with PeqP'' have Summ: "<\<nu>x>a{x}.P' \<in> summands(<\<nu>y>b{y}.P'')" by simp
      moreover with bineqy xineqy have aeqb: "a = b" 
        by(auto simp add: if_split pi.inject name_abs_eq name_fresh_fresh)
      from bineqy xineqy yFreshP' have "y \<sharp> b{x}.P'" by(simp add: name_calc)
      with Summ aeqb bineqy aineqx have "<\<nu>y>b{y}.([(x, y)] \<bullet> P') \<in> summands(<\<nu>y>b{y}.P'')"
        by(simp only: alphaRes, simp add: name_calc)
      with aeqb PeqP'' have "<\<nu>y>P \<longmapsto>a<\<nu>y> \<prec> [(x, y)] \<bullet> P'"
        by(auto intro: Open Output simp add: if_split pi.inject name_abs_eq)
      moreover from yFreshP' have "x \<sharp> [(x, y)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
      ultimately show ?thesis by(simp add: alphaBoundResidual name_swap)
    qed
    ultimately show ?case by blast
  next
    case(Bang P)
    have "hnf (!P)" by fact
    hence False by simp
    thus ?case by simp
  qed
qed

definition "expandSet" :: "pi \<Rightarrow> pi \<Rightarrow> pi set" where
          "expandSet P Q \<equiv> {\<tau>.(P' \<parallel> Q) | P'. \<tau>.(P') \<in> summands P} \<union> 
                           {\<tau>.(P \<parallel> Q') | Q'. \<tau>.(Q') \<in> summands Q} \<union> 
                           {a{b}.(P' \<parallel> Q) | a b P'. a{b}.P' \<in> summands P} \<union>
                           {a{b}.(P \<parallel> Q') | a b Q'. a{b}.Q' \<in> summands Q} \<union>
                           {a<x>.(P' \<parallel> Q) | a x P'. a<x>.P' \<in> summands P \<and> x \<sharp> Q} \<union>
                           {a<x>.(P \<parallel> Q') | a x Q'. a<x>.Q' \<in> summands Q \<and> x \<sharp> P} \<union>
                           {<\<nu>x>a{x}.(P' \<parallel> Q) | a x P'. <\<nu>x>a{x}.P' \<in> summands P \<and> x \<sharp> Q} \<union> 
                           {<\<nu>x>a{x}.(P \<parallel> Q') | a x Q'. <\<nu>x>a{x}.Q' \<in> summands Q \<and> x \<sharp> P} \<union> 
                           {\<tau>.(P'[x::=b] \<parallel> Q') | x P' b Q'. \<exists>a. a<x>.P' \<in> summands P \<and> a{b}.Q' \<in> summands Q} \<union> 
                           {\<tau>.(P' \<parallel> (Q'[x::=b])) | b P' x Q'. \<exists>a. a{b}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q} \<union> 
                           {\<tau>.(<\<nu>y>(P'[x::=y] \<parallel> Q')) | x P' y Q'. \<exists>a. a<x>.P' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P} \<union>
                           {\<tau>.(<\<nu>y>(P' \<parallel> (Q'[x::=y]))) | y P' x Q'. \<exists>a. <\<nu>y>a{y}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q \<and> y \<sharp> Q}"

lemma finiteExpand:
  fixes P :: pi
  and   Q :: pi

  shows "finite(expandSet P Q)"
proof -
  have "finite {\<tau>.(P' \<parallel> Q) | P'. \<tau>.(P') \<in> summands P}"
    by(induct P rule: pi.induct, auto simp add: pi.inject Collect_ex_eq conj_disj_distribL
                                                           Collect_disj_eq UN_Un_distrib)
  moreover have "finite {\<tau>.(P \<parallel> Q') | Q'. \<tau>.(Q') \<in> summands Q}"
    by(induct Q rule: pi.induct, auto simp add: pi.inject Collect_ex_eq conj_disj_distribL
                                                           Collect_disj_eq UN_Un_distrib)
  moreover have "finite {a{b}.(P' \<parallel> Q) | a b P'. a{b}.P' \<in> summands P}"
    by(induct P rule: pi.induct, auto simp add: pi.inject Collect_ex_eq conj_disj_distribL
                                                           Collect_disj_eq UN_Un_distrib)
  moreover have "finite {a{b}.(P \<parallel> Q') | a b Q'. a{b}.Q' \<in> summands Q}"
    by(induct Q rule: pi.induct, auto simp add: pi.inject Collect_ex_eq conj_disj_distribL
                                                           Collect_disj_eq UN_Un_distrib)
  moreover have "finite {a<x>.(P' \<parallel> Q) | a x P'. a<x>.P' \<in> summands P \<and> x \<sharp> Q}"
  proof -
    have Aux: "\<And>a x P Q. (x::name) \<sharp> Q \<Longrightarrow> {a'<x'>.(P' \<parallel> Q) |a' x' P'. a'<x'>.P' = a<x>.P \<and> x' \<sharp> Q} = {a<x>.(P \<parallel> Q)}"
      by(auto simp add: pi.inject name_abs_eq name_fresh_fresh)
    thus ?thesis
      by(nominal_induct P avoiding: Q rule: pi.strong_induct,
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib)
  qed
  moreover have "finite {a<x>.(P \<parallel> Q') | a x Q'. a<x>.Q' \<in> summands Q \<and> x \<sharp> P}"
  proof -
    have Aux: "\<And>a x P Q. (x::name) \<sharp> P \<Longrightarrow> {a'<x'>.(P \<parallel> Q') |a' x' Q'. a'<x'>.Q' = a<x>.Q \<and> x' \<sharp> P} = {a<x>.(P \<parallel> Q)}"
      by(auto simp add: pi.inject name_abs_eq name_fresh_fresh)
    thus ?thesis
      by(nominal_induct Q avoiding: P rule: pi.strong_induct,
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib)
  qed
  moreover have "finite {<\<nu>x>a{x}.(P' \<parallel> Q) | a x P'. <\<nu>x>a{x}.P' \<in> summands P \<and> x \<sharp> Q}"
  proof -
    have Aux: "\<And>a x P Q. \<lbrakk>x \<sharp> Q; a \<noteq> x\<rbrakk> \<Longrightarrow> {<\<nu>x'>a'{x'}.(P' \<parallel> Q) |a' x' P'. <\<nu>x'>a'{x'}.P' = <\<nu>x>a{x}.P \<and> x' \<sharp> Q} = 
                                             {<\<nu>x>a{x}.(P \<parallel> Q)}"
      by(auto simp add: pi.inject name_abs_eq name_fresh_fresh)
    thus ?thesis
      by(nominal_induct P avoiding: Q rule: pi.strong_induct, 
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib)
  qed
  moreover have "finite {<\<nu>x>a{x}.(P \<parallel> Q') | a x Q'. <\<nu>x>a{x}.Q' \<in> summands Q \<and> x \<sharp> P}"
  proof -
    have Aux: "\<And>a x P Q. \<lbrakk>x \<sharp> P; a \<noteq> x\<rbrakk> \<Longrightarrow> {<\<nu>x'>a'{x'}.(P \<parallel> Q') |a' x' Q'. <\<nu>x'>a'{x'}.Q' = <\<nu>x>a{x}.Q \<and> x' \<sharp> P} = 
                                             {<\<nu>x>a{x}.(P \<parallel> Q)}"
      by(auto simp add: pi.inject name_abs_eq name_fresh_fresh)
    thus ?thesis
      by(nominal_induct Q avoiding: P rule: pi.strong_induct, 
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib)
  qed
  moreover have "finite {\<tau>.(P'[x::=b] \<parallel> Q') | x P' b Q'. \<exists>a. a<x>.P' \<in> summands P \<and> a{b}.Q' \<in> summands Q}"
  proof -
    have Aux: "\<And>a x P b Q. {\<tau>.(P'[x'::=b'] \<parallel> Q') | a' x' P' b' Q'. a'<x'>.P' = a<x>.P \<and> a'{b'}.Q' = a{b}.Q} = {\<tau>.(P[x::=b] \<parallel> Q)}"
      by(auto simp add: name_abs_eq pi.inject renaming)
    have "\<And>a x P Q b::'a::{}. finite {\<tau>.(P'[x'::=b] \<parallel> Q') | a' x' P' b Q'. a'<x'>.P' = a<x>.P \<and> a'{b}.Q' \<in> summands Q}"
      apply(induct rule: pi.induct, simp_all)
      apply(case_tac "a=name1")
      apply(simp add: Aux)
      apply(simp add: pi.inject)
      by(simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                   Collect_disj_eq UN_Un_distrib)
    hence "finite {\<tau>.(P'[x::=b] \<parallel> Q') | a x P' b Q'. a<x>.P' \<in> summands P \<and> a{b}.Q' \<in> summands Q}"
      by(nominal_induct P avoiding: Q rule: pi.strong_induct,
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib name_abs_eq)
    thus ?thesis 
      apply(rule_tac finite_subset)
      defer
      by blast+
  qed
  moreover have "finite {\<tau>.(P' \<parallel> (Q'[x::=b])) | b P' x Q'. \<exists>a. a{b}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q}"
  proof -
      have Aux: "\<And>a x P b Q. {\<tau>.(P' \<parallel> (Q'[x'::=b'])) | a' b' P' x' Q'. a'{b'}.P' = a{b}.P \<and> a'<x'>.Q' = a<x>.Q} = {\<tau>.(P \<parallel> (Q[x::=b]))}"
        by(auto simp add: name_abs_eq pi.inject renaming)
      have "\<And>a b P Q x::'a::{}. finite {\<tau>.(P' \<parallel> (Q'[x::=b'])) | a' b' P' x Q'. a'{b'}.P' = a{b}.P \<and> a'<x>.Q' \<in> summands Q}"
      apply(induct rule: pi.induct, simp_all)
      apply(case_tac "a=name1")
      apply(simp add: Aux)
      apply(simp add: pi.inject)
      by(simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                     Collect_disj_eq UN_Un_distrib)
    hence "finite {\<tau>.(P' \<parallel> (Q'[x::=b])) | a b P' x Q'. a{b}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q}"
      by(nominal_induct P avoiding: Q rule: pi.strong_induct,
         auto simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib name_abs_eq)
    thus ?thesis
      apply(rule_tac finite_subset) defer by blast+
  qed
  moreover have "finite {\<tau>.(<\<nu>y>(P'[x::=y] \<parallel> Q')) | x P' y Q'. \<exists>a. a<x>.P' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P}"
  proof -
    have Aux: "\<And>a x P y Q. y \<sharp> P \<and> y \<noteq> a \<Longrightarrow> {\<tau>.(<\<nu>y'>(P'[x'::=y'] \<parallel> Q')) | a' x' P' y' Q'. a'<x'>.P' = a<x>.P \<and> <\<nu>y'>a'{y'}.Q' = <\<nu>y>a{y}.Q \<and> y' \<sharp> a<x>.P} = {\<tau>.(<\<nu>y>(P[x::=y] \<parallel> Q))}"
      apply(auto simp add: pi.inject name_abs_eq name_fresh_abs name_calc fresh_fact2 fresh_fact1 eqvts forget)
      apply(subst name_swap, simp add: injPermSubst fresh_fact1 fresh_fact2)+
      by(simp add: name_swap injPermSubst)+

    have BC: "\<And>a x P Q. finite {\<tau>.(<\<nu>y>(P'[x'::=y] \<parallel> Q')) | a' x' P' y Q'. a'<x'>.P' = a<x>.P \<and> <\<nu>y>a'{y}.Q' \<in> summands Q \<and> y \<sharp> a<x>.P}"
    proof -
      fix a x P Q
      show "finite {\<tau>.(<\<nu>y>(P'[x'::=y] \<parallel> Q')) | a' x' P' y Q'. a'<x'>.P' = a<x>.P \<and> <\<nu>y>a'{y}.Q' \<in> summands Q \<and> y \<sharp> a<x>.P}"
        apply(nominal_induct Q avoiding: a P rule: pi.strong_induct, simp_all)
        apply(simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR
                        Collect_disj_eq UN_Un_distrib)
        apply(clarsimp)
        apply(case_tac "a=aa")
        apply(insert Aux, auto)
        by(simp add: pi.inject name_abs_eq name_calc)
    qed

    have IH: "\<And>P P' Q. {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. (a<x>.P'' \<in> summands P \<or> a<x>.P'' \<in> summands P') \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P \<and> y \<sharp> P'} = {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P \<and> y \<sharp> P'} \<union> {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P' \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P \<and> y \<sharp> P'}"
      by blast
    have IH': "\<And>P Q P'. {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P \<and> y \<sharp> P'} \<subseteq> {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P}"
      by blast
    have IH'': "\<And>P Q P'. {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P' \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P \<and> y \<sharp> P'} \<subseteq> {\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) | a x P'' y Q'. a<x>.P'' \<in> summands P' \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P'}"
      by blast
    have "finite {\<tau>.(<\<nu>y>(P'[x::=y] \<parallel> Q')) | a x P' y Q'. a<x>.P' \<in> summands P \<and> <\<nu>y>a{y}.Q' \<in> summands Q \<and> y \<sharp> P}"
      apply(nominal_induct P avoiding: Q rule: pi.strong_induct, simp_all)
      apply(insert BC, force)
      apply(insert IH, auto)
      apply(blast intro: finite_subset[OF IH'])
      by(blast intro: finite_subset[OF IH''])
    thus ?thesis
      apply(rule_tac finite_subset) defer by(blast)+
  qed
  moreover have "finite {\<tau>.(<\<nu>y>(P' \<parallel> (Q'[x::=y]))) | y P' x Q'. \<exists>a. <\<nu>y>a{y}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q \<and> y \<sharp> Q}"
  proof -
    have Aux: "\<And>a y P x Q. \<lbrakk>y \<sharp> Q; y \<noteq> a\<rbrakk> \<Longrightarrow> {\<tau>.(<\<nu>y'>(P' \<parallel> (Q'[x'::=y']))) | a' y' P' x' Q'. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x'>.Q' = a<x>.Q \<and> y' \<sharp> a<x>.Q} = {\<tau>.(<\<nu>y>(P \<parallel> (Q[x::=y])))}"
      apply(auto simp add: pi.inject name_abs_eq name_fresh_abs name_calc fresh_fact2 fresh_fact1 forget eqvts fresh_left renaming[symmetric])
      apply(subst name_swap, simp add: injPermSubst fresh_fact1 fresh_fact2)+
      by(simp add: name_swap injPermSubst)+

    have IH: "\<And>P y a Q Q'. {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> (a'<x>.Q'' \<in> summands Q \<or> a'<x>.Q'' \<in> summands Q') \<and> y' \<sharp> Q \<and> y' \<sharp> Q'} = {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q \<and> y' \<sharp> Q \<and> y' \<sharp> Q'} \<union> {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q' \<and> y' \<sharp> Q \<and> y' \<sharp> Q'}"
      by blast
    have IH': "\<And>a y P Q Q'. {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q \<and> y' \<sharp> Q \<and> y' \<sharp> Q'} \<subseteq> {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q \<and> y' \<sharp> Q}"
      by blast
    have IH'': "\<And>a y P Q Q'. {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q' \<and> y' \<sharp> Q \<and> y' \<sharp> Q'} \<subseteq> {\<tau>.(<\<nu>y'>(P' \<parallel> (Q''[x::=y']))) | a' y' P' x Q''. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q'' \<in> summands Q' \<and> y' \<sharp> Q'}"
      by blast

    have BC: "\<And>a y P Q. \<lbrakk>y \<sharp> Q; y \<noteq> a\<rbrakk> \<Longrightarrow> finite {\<tau>.(<\<nu>y'>(P' \<parallel> (Q'[x::=y']))) | a' y' P' x Q'. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q' \<in> summands Q \<and> y' \<sharp> Q}"
    proof -
      fix a y P Q
      assume "(y::name) \<sharp> (Q::pi)" and "y \<noteq> a"
      thus "finite {\<tau>.(<\<nu>y'>(P' \<parallel> (Q'[x::=y']))) | a' y' P' x Q'. <\<nu>y'>a'{y'}.P' = <\<nu>y>a{y}.P \<and> a'<x>.Q' \<in> summands Q \<and> y' \<sharp> Q}"
        apply(nominal_induct Q avoiding: y rule: pi.strong_induct, simp_all)
        apply(case_tac "a=name1")
        apply auto
        apply(subgoal_tac "ya \<sharp> (pi::pi)")
        apply(insert Aux)
        apply auto
        apply(simp add: name_fresh_abs)
        apply(simp add: pi.inject name_abs_eq name_calc)
        apply(insert IH)
        apply auto
        apply(blast intro: finite_subset[OF IH'])
        by(blast intro: finite_subset[OF IH''])
    qed
    have "finite {\<tau>.(<\<nu>y>(P' \<parallel> (Q'[x::=y]))) | a y P' x Q'. <\<nu>y>a{y}.P' \<in> summands P \<and> a<x>.Q' \<in> summands Q \<and> y \<sharp> Q}"

      apply(nominal_induct P avoiding: Q rule: pi.strong_induct, simp_all)
      apply(simp add: Collect_ex_eq conj_disj_distribL conj_disj_distribR name_fresh_abs
                      Collect_disj_eq UN_Un_distrib)
      by(auto intro: BC)
    thus ?thesis
      apply(rule_tac finite_subset) defer by blast+
  qed

  ultimately show ?thesis
    by(simp add: expandSet_def)
qed

lemma expandHnf:
  fixes P :: pi
  and   Q :: pi

  shows "\<forall>R \<in> (expandSet P Q). hnf R"
by(force simp add: expandSet_def)

inductive_set sumComposeSet :: "(pi \<times> pi set) set"
where
  empty:  "(\<zero>, {}) \<in> sumComposeSet"
| insert: "\<lbrakk>Q \<in> S; (P, S - {Q}) \<in> sumComposeSet\<rbrakk> \<Longrightarrow> (P \<oplus> Q, S) \<in> sumComposeSet"

lemma expandAction:
  fixes P :: pi
  and   Q :: pi
  and   S :: "pi set"

  assumes "(P, S) \<in> sumComposeSet"
  and     "Q \<in> S"
  and     "Q \<longmapsto> Rs"

  shows "P \<longmapsto> Rs"
using assms
proof(induct arbitrary: Q rule: sumComposeSet.induct)
  case empty
  have "Q \<in> {}" by fact
  hence False by simp
  thus ?case by simp
next
  case(insert Q' S P Q)
  have QTrans: "Q \<longmapsto> Rs" by fact
  show ?case
  proof(case_tac "Q = Q'")
    assume "Q = Q'"
    with QTrans show "P \<oplus> Q' \<longmapsto> Rs" by(blast intro: Sum2)
  next
    assume QineqQ': "Q \<noteq> Q'"
    have IH: "\<And>Q. \<lbrakk>Q \<in> S - {Q'}; Q \<longmapsto> Rs\<rbrakk> \<Longrightarrow> P \<longmapsto> Rs" by fact
    have QinS: "Q \<in> S" by fact
    with QineqQ' have "Q \<in> S - {Q'}" by simp
    hence "P \<longmapsto> Rs" using QTrans by(rule IH)
    thus ?case by(rule Sum1)
  qed
qed

lemma expandAction':
  fixes P :: pi
  and   Q :: pi
  and   R :: pi

  assumes "(R, S) \<in> sumComposeSet"
  and     "R \<longmapsto> Rs"

  shows "\<exists>P \<in> S. P \<longmapsto> Rs"
using assms
proof(induct rule: sumComposeSet.induct)
  case empty
  have "\<zero> \<longmapsto> Rs" by fact
  hence False by blast
  thus ?case by simp
next
  case(insert Q S P)
  have QinS: "Q \<in> S" by fact
  have "P \<oplus> Q \<longmapsto> Rs" by fact
  thus ?case
  proof(induct rule: sumCases)
    case cSum1
    have "P \<longmapsto> Rs" by fact
    moreover have "P \<longmapsto> Rs \<Longrightarrow> \<exists>P \<in> (S - {Q}). P \<longmapsto> Rs" by fact
    ultimately obtain P where PinS: "P \<in> (S - {Q})" and PTrans: "P \<longmapsto> Rs" by blast
    show ?case
    proof(case_tac "P = Q")
      assume "P = Q"
      with PTrans QinS show ?case by blast
    next
      assume PineqQ: "P \<noteq> Q"
      from PinS have "P \<in> S" by simp
      with PTrans show ?thesis by blast
    qed
  next
    case cSum2
    have "Q \<longmapsto> Rs" by fact
    with QinS show ?case by blast
  qed
qed

lemma expandTrans:
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  and   a :: name
  and   b :: name
  and   x :: name

  assumes Exp: "(R, expandSet P Q) \<in> sumComposeSet"
  and     Phnf: "hnf P"
  and     Qhnf: "hnf Q"

  shows "(P \<parallel> Q \<longmapsto>\<tau> \<prec> P') = (R \<longmapsto>\<tau> \<prec> P')"
  and   "(P \<parallel> Q \<longmapsto>a[b] \<prec> P') = (R \<longmapsto>a[b] \<prec> P')"
  and   "(P \<parallel> Q \<longmapsto>a<x> \<prec> P') = (R \<longmapsto>a<x> \<prec> P')"
  and   "(P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P') = (R \<longmapsto>a<\<nu>x> \<prec> P')"
proof -
  show "P \<parallel> Q \<longmapsto> \<tau> \<prec> P' = R \<longmapsto> \<tau> \<prec> P'"
  proof(rule iffI)
    assume "P \<parallel> Q \<longmapsto>\<tau> \<prec> P'"
    thus "R \<longmapsto>\<tau> \<prec> P'"
    proof(induct rule: parCasesF[of _ _ _ _ _ "(P, Q)"])
      case(cPar1 P')
      have "P \<longmapsto>\<tau> \<prec> P'" by fact
      with Phnf have "\<tau>.(P') \<in> summands P" by(simp add: summandTransition)
      hence "\<tau>.(P' \<parallel> Q) \<in> expandSet P Q" by(auto simp add: expandSet_def)
      moreover have "\<tau>.(P' \<parallel> Q) \<longmapsto>\<tau> \<prec> (P' \<parallel> Q)" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cPar2 Q')
      have "Q \<longmapsto>\<tau> \<prec> Q'" by fact
      with Qhnf have "\<tau>.(Q') \<in> summands Q" by(simp add: summandTransition)
      hence "\<tau>.(P \<parallel> Q') \<in> expandSet P Q" by(auto simp add: expandSet_def)
      moreover have "\<tau>.(P \<parallel> Q') \<longmapsto>\<tau> \<prec> (P \<parallel> Q')" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cComm1 P' Q' a b x)
      have "P \<longmapsto>a<x> \<prec> P'" and "Q \<longmapsto>a[b] \<prec> Q'" by fact+
      with Phnf Qhnf have "a<x>.P' \<in> summands P" and "a{b}.Q' \<in> summands Q" by(simp add: summandTransition)+
      hence "\<tau>.(P'[x::=b] \<parallel> Q') \<in> expandSet P Q" by(simp add: expandSet_def, blast)
      moreover have "\<tau>.(P'[x::=b] \<parallel> Q') \<longmapsto>\<tau> \<prec> (P'[x::=b] \<parallel> Q')" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cComm2 P' Q' a b x)
      have "P \<longmapsto>a[b] \<prec> P'" and "Q \<longmapsto>a<x> \<prec> Q'" by fact+
      with Phnf Qhnf have "a{b}.P' \<in> summands P" and "a<x>.Q' \<in> summands Q" by(simp add: summandTransition)+
      hence "\<tau>.(P' \<parallel> (Q'[x::=b])) \<in> expandSet P Q" by(simp add: expandSet_def, blast)
      moreover have "\<tau>.(P' \<parallel> (Q'[x::=b])) \<longmapsto>\<tau> \<prec> (P' \<parallel> (Q'[x::=b]))" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cClose1 P' Q' a x y)
      have "y \<sharp> (P, Q)" by fact
      hence yFreshP: "y \<sharp> P" by(simp add: fresh_prod)
      have PTrans: "P \<longmapsto>a<x> \<prec> P'" by fact
      with Phnf have PSumm: "a<x>.P' \<in> summands P" by(simp add: summandTransition)
      have "Q \<longmapsto>a<\<nu>y> \<prec> Q'" by fact
      moreover from PTrans yFreshP have "y \<noteq> a" by(force dest: freshBoundDerivative)
      ultimately have "<\<nu>y>a{y}.Q' \<in> summands Q" using Qhnf by(simp add: summandTransition)
      with PSumm yFreshP have "\<tau>.(<\<nu>y>(P'[x::=y] \<parallel> Q')) \<in> expandSet P Q"
        by(auto simp add: expandSet_def)
      moreover have "\<tau>.(<\<nu>y>(P'[x::=y] \<parallel> Q')) \<longmapsto>\<tau> \<prec> <\<nu>y>(P'[x::=y] \<parallel> Q')" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cClose2 P' Q' a x y)
      have "y \<sharp> (P, Q)" by fact
      hence yFreshQ: "y \<sharp> Q" by(simp add: fresh_prod)
      have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" by fact
      with Qhnf have QSumm: "a<x>.Q' \<in> summands Q" by(simp add: summandTransition)
      have "P \<longmapsto>a<\<nu>y> \<prec> P'" by fact
      moreover from QTrans yFreshQ have "y \<noteq> a" by(force dest: freshBoundDerivative)
      ultimately have "<\<nu>y>a{y}.P' \<in> summands P" using Phnf by(simp add: summandTransition)
      with QSumm yFreshQ have "\<tau>.(<\<nu>y>(P' \<parallel> (Q'[x::=y]))) \<in> expandSet P Q"
        by(simp add: expandSet_def, blast)
      moreover have "\<tau>.(<\<nu>y>(P' \<parallel> (Q'[x::=y]))) \<longmapsto>\<tau> \<prec> <\<nu>y>(P' \<parallel> (Q'[x::=y]))" by(rule Tau)
      ultimately show ?case using Exp by(blast intro: expandAction)
    qed
  next
    assume "R \<longmapsto>\<tau> \<prec> P'"
    with Exp obtain R where "R \<in> expandSet P Q" and "R \<longmapsto>\<tau> \<prec> P'" by(blast dest: expandAction')
    thus "P \<parallel> Q \<longmapsto>\<tau> \<prec> P'"
    proof(auto simp add: expandSet_def)
      fix P''
      assume "\<tau>.(P'') \<in> summands P"
      with Phnf have "P \<longmapsto>\<tau> \<prec> P''" by(simp add: summandTransition)
      hence PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> P'' \<parallel> Q" by(rule Par1F)
      assume "\<tau>.(P'' \<parallel> Q) \<longmapsto>\<tau> \<prec> P'"
      hence "P' = P'' \<parallel> Q" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    next
      fix Q'
      assume "\<tau>.(Q') \<in> summands Q"
      with Qhnf have "Q \<longmapsto>\<tau> \<prec> Q'" by(simp add: summandTransition)
      hence PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> P \<parallel> Q'" by(rule Par2F)
      assume "\<tau>.(P \<parallel> Q') \<longmapsto>\<tau> \<prec> P'"
      hence "P' = P \<parallel> Q'" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    next
      fix a x P'' b Q'
      assume "a<x>.P'' \<in> summands P" and "a{b}.Q' \<in> summands Q"
      with Phnf Qhnf have "P \<longmapsto>a<x> \<prec> P''" and "Q \<longmapsto>a[b] \<prec> Q'" by(simp add: summandTransition)+
      hence PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> P''[x::=b] \<parallel> Q'" by(rule Comm1)
      assume "\<tau>.(P''[x::=b] \<parallel> Q') \<longmapsto>\<tau> \<prec> P'"
      hence "P' = P''[x::=b] \<parallel> Q'" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    next
      fix a b P'' x Q'
      assume "a{b}.P'' \<in> summands P" and "a<x>.Q' \<in> summands Q"
      with Phnf Qhnf have "P \<longmapsto>a[b] \<prec> P''" and "Q \<longmapsto>a<x> \<prec> Q'" by(simp add: summandTransition)+
      hence PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> P'' \<parallel> (Q'[x::=b])" by(rule Comm2)
      assume "\<tau>.(P'' \<parallel> (Q'[x::=b])) \<longmapsto>\<tau> \<prec> P'"
      hence "P' = P'' \<parallel> (Q'[x::=b])" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    next
      fix a x P'' y Q'
      assume yFreshP: "(y::name) \<sharp> P"
      assume "a<x>.P'' \<in> summands P" 
      with Phnf have PTrans: "P \<longmapsto>a<x> \<prec> P''" by(simp add: summandTransition)
      assume "<\<nu>y>a{y}.Q' \<in> summands Q"
      moreover from yFreshP PTrans have "y \<noteq> a" by(force dest: freshBoundDerivative)
      ultimately have "Q \<longmapsto>a<\<nu>y> \<prec> Q'" using Qhnf by(simp add: summandTransition)
      with PTrans have PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(P''[x::=y] \<parallel> Q')" using yFreshP by(rule Close1)
      assume "\<tau>.(<\<nu>y>(P''[x::=y] \<parallel> Q')) \<longmapsto>\<tau> \<prec> P'"
      hence "P' = <\<nu>y>(P''[x::=y] \<parallel> Q')" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    next
      fix a y P'' x Q'
      assume yFreshQ: "(y::name) \<sharp> Q"
      assume "a<x>.Q' \<in> summands Q" 
      with Qhnf have QTrans: "Q \<longmapsto>a<x> \<prec> Q'" by(simp add: summandTransition)
      assume "<\<nu>y>a{y}.P'' \<in> summands P"
      moreover from yFreshQ QTrans have "y \<noteq> a" by(force dest: freshBoundDerivative)
      ultimately have "P \<longmapsto>a<\<nu>y> \<prec> P''" using Phnf by(simp add: summandTransition)
      hence PQTrans: "P \<parallel> Q \<longmapsto>\<tau> \<prec> <\<nu>y>(P'' \<parallel> Q'[x::=y])" using QTrans yFreshQ by(rule Close2)
      assume "\<tau>.(<\<nu>y>(P'' \<parallel> Q'[x::=y])) \<longmapsto>\<tau> \<prec> P'"
      hence "P' = <\<nu>y>(P'' \<parallel> Q'[x::=y])" by(erule_tac tauCases, auto simp add: pi.inject residual.inject)
      with PQTrans show ?thesis by simp
    qed
  qed
next
  show "P \<parallel> Q \<longmapsto> a[b] \<prec> P' = R \<longmapsto> a[b] \<prec> P'"
  proof(rule iffI)
    assume "P \<parallel> Q \<longmapsto>a[b] \<prec> P'"
    thus "R \<longmapsto>a[b] \<prec> P'"
    proof(induct rule: parCasesF[where C="()"])
      case(cPar1 P')
      have "P \<longmapsto>a[b] \<prec> P'" by fact
      with Phnf have "a{b}.P' \<in> summands P" by(simp add: summandTransition)
      hence "a{b}.(P' \<parallel> Q) \<in> expandSet P Q" by(auto simp add: expandSet_def)
      moreover have "a{b}.(P' \<parallel> Q) \<longmapsto>a[b] \<prec> (P' \<parallel> Q)" by(rule Output)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next
      case(cPar2 Q')
      have "Q \<longmapsto>a[b] \<prec> Q'" by fact
      with Qhnf have "a{b}.Q' \<in> summands Q" by(simp add: summandTransition)
      hence "a{b}.(P \<parallel> Q') \<in> expandSet P Q" by(simp add: expandSet_def, blast)
      moreover have "a{b}.(P \<parallel> Q') \<longmapsto>a[b] \<prec> (P \<parallel> Q')" by(rule Output)
      ultimately show ?case using Exp by(blast intro: expandAction)
    next 
      case cComm1
      thus ?case by auto
    next 
      case cComm2
      thus ?case by auto
    next 
      case cClose1
      thus ?case by auto
    next 
      case cClose2
      thus ?case by auto
    qed
  next
    assume "R \<longmapsto>a[b] \<prec> P'"
    with Exp obtain R where "R \<in> expandSet P Q" and "R \<longmapsto>a[b] \<prec> P'" by(blast dest: expandAction')
    thus "P \<parallel> Q \<longmapsto>a[b] \<prec> P'"
    proof(auto simp add: expandSet_def)
      fix a' b' P''
      assume "a'{b'}.P'' \<in> summands P"
      with Phnf have "P \<longmapsto>a'[b'] \<prec> P''" by(simp add: summandTransition)
      hence PQTrans: "P \<parallel> Q \<longmapsto>a'[b'] \<prec> P'' \<parallel> Q" by(rule Par1F)
      assume "a'{b'}.(P'' \<parallel> Q) \<longmapsto>a[b] \<prec> P'"
      hence "P' = P'' \<parallel> Q" and "a = a'" and "b = b'"
        by(erule_tac outputCases, auto simp add: pi.inject residual.inject)+
      with PQTrans show ?thesis by simp
    next
      fix a' b' Q'
      assume "a'{b'}.Q' \<in> summands Q"
      with Qhnf have "Q \<longmapsto>a'[b'] \<prec> Q'" by(simp add: summandTransition)
      hence PQTrans: "P \<parallel> Q \<longmapsto>a'[b'] \<prec> P \<parallel> Q'" by(rule Par2F)
      assume "a'{b'}.(P \<parallel> Q') \<longmapsto>a[b] \<prec> P'"
      hence "P' = P \<parallel> Q'" and "a = a'" and "b = b'"
        by(erule_tac outputCases, auto simp add: pi.inject residual.inject)+
      with PQTrans show ?thesis by simp
    qed
  qed
next
  show "P \<parallel> Q \<longmapsto> a<x> \<prec> P' = R \<longmapsto> a<x> \<prec> P'"
  proof(rule iffI)
    {
      fix x P'
      assume "P \<parallel> Q \<longmapsto>a<x> \<prec> P'" and "x \<sharp> P" and "x \<sharp> Q"
      hence "R \<longmapsto>a<x> \<prec> P'"
      proof(induct rule: parCasesB)
        case(cPar1 P')
        have "P \<longmapsto>a<x> \<prec> P'" by fact
        with Phnf have "a<x>.P' \<in> summands P" by(simp add: summandTransition)
        moreover have "x \<sharp> Q" by fact
        ultimately have "a<x>.(P' \<parallel> Q) \<in> expandSet P Q" by(auto simp add: expandSet_def)
        moreover have "a<x>.(P' \<parallel> Q) \<longmapsto>a<x> \<prec> (P' \<parallel> Q)" by(rule Input)
        ultimately show ?case using Exp by(blast intro: expandAction)
      next
        case(cPar2 Q')
        have "Q \<longmapsto>a<x> \<prec> Q'" by fact
        with Qhnf have "a<x>.Q' \<in> summands Q" by(simp add: summandTransition)
        moreover have "x \<sharp> P" by fact
        ultimately have "a<x>.(P \<parallel> Q') \<in> expandSet P Q" by(simp add: expandSet_def, blast)
        moreover have "a<x>.(P \<parallel> Q') \<longmapsto>a<x> \<prec> (P \<parallel> Q')" by(rule Input)
        ultimately show ?case using Exp by(blast intro: expandAction)
      qed
    }
    moreover obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> P'"
      by(generate_fresh "name") auto
    assume "P \<parallel> Q \<longmapsto>a<x> \<prec> P'"
    with \<open>y \<sharp> P'\<close> have "P \<parallel> Q \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P')"
      by(simp add: alphaBoundResidual)
    ultimately have "R \<longmapsto>a<y> \<prec> ([(x, y)] \<bullet> P')" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close>
      by auto
    thus "R \<longmapsto>a<x> \<prec> P'" using \<open>y \<sharp> P'\<close> by(simp add: alphaBoundResidual)
  next
    assume "R \<longmapsto>a<x> \<prec> P'"
    with Exp obtain R where "R \<in> expandSet P Q" and "R \<longmapsto>a<x> \<prec> P'" by(blast dest: expandAction')
    thus "P \<parallel> Q \<longmapsto>a<x> \<prec> P'"
    proof(auto simp add: expandSet_def)
      fix a' y P''
      assume "a'<y>.P'' \<in> summands P"
      with Phnf have "P \<longmapsto>a'<y> \<prec> P''" by(simp add: summandTransition)
      moreover assume "y \<sharp> Q"
      ultimately have PQTrans: "P \<parallel> Q \<longmapsto>a'<y> \<prec> P'' \<parallel> Q" by(rule Par1B)
      assume "a'<y>.(P'' \<parallel> Q) \<longmapsto>a<x> \<prec> P'"
      hence "a<x> \<prec> P' = a'<y> \<prec> P'' \<parallel> Q" and "a = a'"
        by(erule_tac inputCases', auto simp add: pi.inject residual.inject)+
      with PQTrans show ?thesis by simp
    next
      fix a' y Q'
      assume "a'<y>.Q' \<in> summands Q"
      with Qhnf have "Q \<longmapsto>(a'::name)<y> \<prec> Q'" by(simp add: summandTransition)
      moreover assume "y \<sharp> P"
      ultimately have PQTrans: "P \<parallel> Q \<longmapsto>a'<y> \<prec> P \<parallel> Q'" by(rule Par2B)
      assume "a'<y>.(P \<parallel> Q') \<longmapsto>a<x> \<prec> P'"
      hence "a<x> \<prec> P' = a'<y> \<prec> P \<parallel> Q'" and "a = a'"
        by(erule_tac inputCases', auto simp add: pi.inject residual.inject)+
      with PQTrans show ?thesis by simp
    qed
  qed
next
  have Goal: "\<And>P Q a x P' R. \<lbrakk>(R, expandSet P Q) \<in> sumComposeSet; hnf P; hnf Q; a \<noteq> x\<rbrakk> \<Longrightarrow> P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P' = R \<longmapsto>a<\<nu>x> \<prec> P'"
  proof -
    fix P Q a x P' R
    assume aineqx: "(a::name) \<noteq> x"
    assume Exp: "(R, expandSet P Q) \<in> sumComposeSet"
    assume Phnf: "hnf P"
    assume Qhnf: "hnf Q"
    show "P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P' = R \<longmapsto> a<\<nu>x> \<prec> P'"
    proof(rule iffI)
      {
        fix x P'
        assume "P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P'" and "x \<sharp> P" and "x \<sharp> Q" and "a \<noteq> x"
        hence "R \<longmapsto>a<\<nu>x> \<prec> P'"
        proof(induct rule: parCasesB)
          case(cPar1 P')
          have "P \<longmapsto>a<\<nu>x> \<prec> P'" by fact
          with Phnf \<open>a \<noteq> x\<close> have "<\<nu>x>a{x}.P' \<in> summands P" by(simp add: summandTransition)
          moreover have "x \<sharp> Q" by fact
          ultimately have "<\<nu>x>a{x}.(P' \<parallel> Q) \<in> expandSet P Q" by(auto simp add: expandSet_def)
          moreover have "<\<nu>x>a{x}.(P' \<parallel> Q) \<longmapsto>a<\<nu>x> \<prec> (P' \<parallel> Q)" using \<open>a \<noteq> x\<close>
            by(blast intro: Open Output)
          ultimately show ?case using Exp by(blast intro: expandAction)
        next
          case(cPar2 Q')
          have "Q \<longmapsto>a<\<nu>x> \<prec> Q'" by fact
          with Qhnf \<open>a \<noteq> x\<close> have "<\<nu>x>a{x}.Q' \<in> summands Q" by(simp add: summandTransition)
          moreover have "x \<sharp> P" by fact
          ultimately have "<\<nu>x>a{x}.(P \<parallel> Q') \<in> expandSet P Q" by(simp add: expandSet_def, blast)
          moreover have "<\<nu>x>a{x}.(P \<parallel> Q') \<longmapsto>a<\<nu>x> \<prec> (P \<parallel> Q')" using \<open>a \<noteq> x\<close>
            by(blast intro: Open Output)
          ultimately show ?case using Exp by(blast intro: expandAction)
        qed
      }
      moreover obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> P'" and "y \<noteq> a"
        by(generate_fresh "name") auto
      assume "P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P'"
      with \<open>y \<sharp> P'\<close> have "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')"
        by(simp add: alphaBoundResidual)
      ultimately have "R \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')" using \<open>y \<sharp> P\<close> \<open>y \<sharp> Q\<close> \<open>y \<noteq> a\<close>
        by auto
      thus "R \<longmapsto>a<\<nu>x> \<prec> P'" using \<open>y \<sharp> P'\<close> by(simp add: alphaBoundResidual)
    next
      {
        fix R x P'
        assume "R \<longmapsto>a<\<nu>x> \<prec> P'" and "R \<in> expandSet P Q" and "x \<sharp> R" and "x \<sharp> P" and "x \<sharp> Q"
        hence "P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P'" 
        proof(auto simp add: expandSet_def)
          fix a' y P''
          assume "<\<nu>y>a'{y}.P'' \<in> summands P"
          moreover hence "a' \<noteq> y" by auto
          ultimately have "P \<longmapsto>a'<\<nu>y> \<prec> P''" using Phnf by(simp add: summandTransition)
          moreover assume "y \<sharp> Q"
          ultimately have PQTrans: "P \<parallel> Q \<longmapsto>a'<\<nu>y> \<prec> P'' \<parallel> Q" by(rule Par1B)
          assume ResTrans: "<\<nu>y>a'{y}.(P'' \<parallel> Q) \<longmapsto>a<\<nu>x> \<prec> P'" and "x \<sharp> [y].a'{y}.(P'' \<parallel> Q)"
          with ResTrans \<open>a' \<noteq> y\<close> \<open>x \<sharp> P\<close> \<open>x \<sharp> Q\<close> have "a<\<nu>x> \<prec> P' = a'<\<nu>y> \<prec> P'' \<parallel> Q"
            apply(case_tac "x=y")
            defer
            apply(erule_tac resCasesB)
            apply simp
            apply(simp add: abs_fresh)
            apply(auto simp add: residual.inject alpha' calc_atm fresh_left abs_fresh elim: outputCases)
            apply(ind_cases "<\<nu>y>a'{y}.(P'' \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> P'")
            apply(simp add: pi.inject alpha' residual.inject abs_fresh eqvts calc_atm)
            apply(auto elim: outputCases)
            apply(simp add: pi.inject residual.inject alpha' calc_atm)
            apply auto
            apply(ind_cases "<\<nu>y>a'{y}.(P'' \<parallel> Q) \<longmapsto> a<\<nu>y> \<prec> P'")
            apply(auto simp add: pi.inject alpha' residual.inject abs_fresh eqvts calc_atm)
            apply(auto elim: outputCases)
            apply(erule_tac outputCases)
            apply(auto simp add: freeRes.inject)
            apply hypsubst_thin
            apply(drule_tac pi="[(b, y)]" in pt_bij3)
            by simp
        with PQTrans show ?thesis by simp
      next
        fix a' y Q'
        assume "<\<nu>y>a'{y}.Q' \<in> summands Q"
        moreover hence "a' \<noteq> y" by auto
        ultimately have "Q \<longmapsto>a'<\<nu>y> \<prec> Q'" using Qhnf by(simp add: summandTransition)
        moreover assume "y \<sharp> P"
        ultimately have PQTrans: "P \<parallel> Q \<longmapsto>a'<\<nu>y> \<prec> P \<parallel> Q'" by(rule Par2B)
        assume ResTrans: "<\<nu>y>a'{y}.(P \<parallel> Q') \<longmapsto>a<\<nu>x> \<prec> P'" and "x \<sharp> [y].a'{y}.(P \<parallel> Q')"
        with ResTrans \<open>a' \<noteq> y\<close> have "a<\<nu>x> \<prec> P' = a'<\<nu>y> \<prec> P \<parallel> Q'"
          apply(case_tac "x=y")
          defer
          apply(erule_tac resCasesB)
            apply simp
            apply(simp add: abs_fresh)
            apply(auto simp add: residual.inject alpha' calc_atm fresh_left abs_fresh elim: outputCases)
            apply(ind_cases "<\<nu>y>a'{y}.(P \<parallel> Q') \<longmapsto> a<\<nu>y> \<prec> P'")
            apply(simp add: pi.inject alpha' residual.inject abs_fresh eqvts calc_atm)
            apply(auto elim: outputCases)
            apply(simp add: pi.inject residual.inject alpha' calc_atm)
            apply auto
            apply(ind_cases "<\<nu>y>a'{y}.(P \<parallel> Q') \<longmapsto> a<\<nu>y> \<prec> P'")
            apply(auto simp add: pi.inject alpha' residual.inject abs_fresh eqvts calc_atm)
            apply(auto elim: outputCases)
            apply(erule_tac outputCases)
            apply(auto simp add: freeRes.inject)
            apply hypsubst_thin
            apply(drule_tac pi="[(b, y)]" in pt_bij3)
            by simp
        with PQTrans show ?thesis by simp
      qed
    }
    moreover assume "R \<longmapsto>a<\<nu>x> \<prec> P'"
    with Exp obtain R where "R \<in> expandSet P Q" and "R \<longmapsto>a<\<nu>x> \<prec> P'" 
      apply(drule_tac expandAction') by auto
    moreover obtain y::name where "y \<sharp> P" and "y \<sharp> Q" and "y \<sharp> R" and "y \<sharp> P'"
      by(generate_fresh "name") auto
    moreover with \<open>y \<sharp> P'\<close> \<open>R \<longmapsto>a<\<nu>x> \<prec> P'\<close> have "R \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')" by(simp add: alphaBoundResidual)
    ultimately have "P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> ([(x, y)] \<bullet> P')" by auto
    thus "P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P'" using \<open>y \<sharp> P'\<close> by(simp add: alphaBoundResidual)
    qed
  qed

  obtain y where yineqx: "a \<noteq> y" and yFreshP': "y \<sharp> P'"
    by(force intro: name_exists_fresh[of "(a, P')"] simp add: fresh_prod)
  from Exp Phnf Qhnf yineqx have "(P \<parallel> Q \<longmapsto>a<\<nu>y> \<prec> [(x, y)] \<bullet> P') = (R \<longmapsto>a<\<nu>y> \<prec> [(x, y)] \<bullet> P')"
    by(rule Goal)
  moreover with yFreshP' have "x \<sharp> [(x, y)] \<bullet> P'" by(simp add: name_fresh_left name_calc)
  ultimately show "(P \<parallel> Q \<longmapsto>a<\<nu>x> \<prec> P') = (R \<longmapsto>a<\<nu>x> \<prec> P')"
    by(simp add: alphaBoundResidual name_swap)
qed

lemma expandLeft:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Exp: "(R, expandSet P Q) \<in> sumComposeSet"
  and     Phnf: "hnf P"
  and     Qhnf: "hnf Q"
  and     Id: "Id \<subseteq> Rel"

  shows "P \<parallel> Q \<leadsto>[Rel] R"
proof(induct rule: simCases)
  case(Bound a x R')
  have "R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> R'" by fact
  with Exp Phnf Qhnf have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> R'" by(cases a, auto simp add: expandTrans)
  moreover from Id have "derivative R' R' a x Rel" by(cases a, auto simp add: derivative_def)
  ultimately show ?case by blast
next
  case(Free \<alpha> R')
  have "R \<longmapsto>\<alpha> \<prec> R'" by fact
  with Exp Phnf Qhnf have "P \<parallel> Q \<longmapsto>\<alpha> \<prec> R'" by(cases \<alpha>, auto simp add: expandTrans)
  moreover from Id have "(R', R') \<in> Rel" by blast
  ultimately show ?case by blast
qed

lemma expandRight:
  fixes P   :: pi
  and   Q   :: pi
  and   R   :: pi
  and   Rel :: "(pi \<times> pi) set"

  assumes Exp: "(R, expandSet P Q) \<in> sumComposeSet"
  and     Phnf: "hnf P"
  and     Qhnf: "hnf Q"
  and     Id: "Id \<subseteq> Rel"

  shows "R \<leadsto>[Rel] P \<parallel> Q"
proof(induct rule: simCases)
  case(Bound a x R')
  have "P \<parallel> Q \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> R'" by fact
  with Exp Phnf Qhnf have "R \<longmapsto>a\<guillemotleft>x\<guillemotright> \<prec> R'" by(cases a, auto simp add: expandTrans)
  moreover from Id have "derivative R' R' a x Rel" by(cases a, auto simp add: derivative_def)
  ultimately show ?case by blast
next
  case(Free \<alpha> R')
  have "P \<parallel> Q \<longmapsto>\<alpha> \<prec> R'" by fact
  with Exp Phnf Qhnf have "R \<longmapsto>\<alpha> \<prec> R'" by(cases \<alpha>, auto simp add: expandTrans)
  moreover from Id have "(R', R') \<in> Rel" by blast
  ultimately show ?case by blast
qed

lemma expandSC: 
  fixes P :: pi
  and   Q :: pi
  and   R :: pi
  
  assumes "(R, expandSet P Q) \<in> sumComposeSet"
  and     "hnf P"
  and     "hnf Q"

  shows "P \<parallel> Q \<sim> R"
proof -
  let ?X = "{(P \<parallel> Q, R) | P Q R. (R, expandSet P Q) \<in> sumComposeSet \<and> hnf P \<and> hnf Q} \<union> {(R, P \<parallel> Q) | P Q R. (R, expandSet P Q) \<in> sumComposeSet \<and> hnf P \<and> hnf Q}"
  from assms have "(P \<parallel> Q, R) \<in> ?X" by auto
  thus ?thesis
  proof(coinduct rule: bisimCoinduct)
    case(cSim P Q)
    thus ?case
      by(blast intro: reflexive expandLeft expandRight)
  next
    case(cSym P Q)
     thus ?case by auto
   qed
 qed

end
