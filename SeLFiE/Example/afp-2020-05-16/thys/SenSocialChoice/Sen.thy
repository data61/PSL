(*
 * Sen's SDF results and Liberal Paradox.
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced July 2006.
 * License: BSD
 *)

(*<*)
theory Sen

imports SCFs

begin
(*>*)

section\<open>Sen's Liberal Paradox\<close>

subsection\<open>Social Decision Functions (SDFs)\<close>

text\<open>To make progress in the face of Arrow's Theorem, the demands placed
on the social choice function need to be weakened. One approach is to only
require that the set of alternatives that society ranks highest (and is
otherwise indifferent about) be non-empty.

Following \cite[Chapter~4*]{Sen:70a}, a \emph{Social Decision Function}
(SDF) yields a choice function for every profile.\<close>

definition
  SDF :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> ('a set \<Rightarrow> 'i set \<Rightarrow> ('a, 'i) Profile \<Rightarrow> bool) \<Rightarrow> bool"
where
  "SDF sdf A Is Pcond \<equiv> (\<forall>P. Pcond A Is P \<longrightarrow> choiceFn A (sdf P))"

lemma SDFI[intro]:
  "(\<And>P. Pcond A Is P \<Longrightarrow> choiceFn A (sdf P)) \<Longrightarrow> SDF sdf A Is Pcond"
  unfolding SDF_def by simp

lemma SWF_SDF:
  assumes finiteA: "finite A"
  shows "SWF scf A Is universal_domain \<Longrightarrow> SDF scf A Is universal_domain"
  unfolding SDF_def SWF_def by (blast dest: rpr_choiceFn[OF finiteA])

text\<open>In contrast to SWFs, there are SDFs satisfying Arrow's (relevant)
requirements. The lemma uses a witness to show the absence of a
dictatorship.\<close>

lemma SDF_nodictator_witness:
  assumes has2A: "hasw [x,y] A"
      and has2Is: "hasw [i,j] Is"
  obtains P
  where "profile A Is P"
    and "x \<^bsub>(P i)\<^esub>\<prec> y"
    and "y \<^bsub>(P j)\<^esub>\<prec> x"
proof
  let ?P = "\<lambda>k. (if k = i then ({ (x, u) | u. u \<in> A }
                               \<union> { (y, u) | u. u \<in> A - {x} })
                          else ({ (y, u) | u. u \<in> A }
                               \<union> { (x, u) | u. u \<in> A - {y} }))
                      \<union> (A - {x,y}) \<times> (A - {x,y})"
  show "profile A Is ?P"
  proof
    fix i assume iis: "i \<in> Is"
    from has2A show "rpr A (?P i)"
      by - (rule rprI, simp_all add: trans_def, blast+)
  next
    from has2Is show "Is \<noteq> {}" by auto
  qed
  from has2A has2Is
  show "x \<^bsub>(?P i)\<^esub>\<prec> y"
   and "y \<^bsub>(?P j)\<^esub>\<prec> x"
    unfolding strict_pref_def by auto
qed

lemma SDF_possibility:
  assumes finiteA: "finite A"
      and has2A: "has 2 A"
      and has2Is: "has 2 Is"
  obtains sdf
  where "weak_pareto sdf A Is universal_domain"
    and "iia sdf A Is"
    and "\<not>(\<exists>j. dictator sdf A Is j)"
    and "SDF sdf A Is universal_domain"
proof -
  let ?sdf = "\<lambda>P. { (x, y) . x \<in> A \<and> y \<in> A
                             \<and> \<not> ((\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<preceq> x)
                                \<and> (\<exists>i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> x)) }"
  have "weak_pareto ?sdf A Is universal_domain"
    by (rule, unfold strict_pref_def, auto dest: profile_non_empty)
  moreover
  have "iia ?sdf A Is" unfolding strict_pref_def by auto
  moreover
  have "\<not>(\<exists>j. dictator ?sdf A Is j)"
  proof
    assume "\<exists>j. dictator ?sdf A Is j"
    then obtain j where jIs: "j \<in> Is"
                    and jD: "\<forall>x \<in> A. \<forall>y \<in> A. decisive ?sdf A Is {j} x y"
      unfolding dictator_def decisive_def by auto
    from jIs has_witness_two[OF has2Is] obtain i where ijIs: "hasw [i,j] Is"
      by auto
    from has_witness_two[OF has2A] obtain x y where xyA: "hasw [x,y] A" by auto
    from xyA ijIs obtain P
      where profileP: "profile A Is P"
        and yPix: "x \<^bsub>(P i)\<^esub>\<prec> y"
        and yPjx: "y \<^bsub>(P j)\<^esub>\<prec> x"
      by (rule SDF_nodictator_witness)
    from profileP jD jIs xyA yPjx have "y \<^bsub>(?sdf P)\<^esub>\<prec> x"
      unfolding decisive_def by simp
    moreover
    from ijIs xyA yPjx yPix have "x \<^bsub>(?sdf P)\<^esub>\<preceq> y"
      unfolding strict_pref_def by auto
    ultimately show False
      unfolding strict_pref_def by blast
  qed
  moreover
  have "SDF ?sdf A Is universal_domain"
  proof
    fix P assume ud: "universal_domain A Is P"
    show "choiceFn A (?sdf P)"
    proof(rule r_c_qt_imp_cf[OF finiteA])
      show "complete A (?sdf P)" and "refl_on A (?sdf P)"
        unfolding strict_pref_def by auto
      show "quasi_trans (?sdf P)"
      proof
        fix x y z assume xy: "x \<^bsub>(?sdf P)\<^esub>\<prec> y" and yz: "y \<^bsub>(?sdf P)\<^esub>\<prec> z"
        from xy yz have xyzA: "x \<in> A" "y \<in> A" "z \<in> A"
          unfolding strict_pref_def by auto
        from xy yz have AxRy: "\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<preceq> y"
                    and ExPy: "\<exists>i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> y"
                    and AyRz: "\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<preceq> z"
          unfolding strict_pref_def by auto
        from AxRy AyRz ud have AxRz: "\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<preceq> z"
          by - (unfold universal_domain_def, blast dest: rpr_le_trans)
        from ExPy AyRz ud have ExPz: "\<exists>i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> z"
          by - (unfold universal_domain_def, blast dest: rpr_less_le_trans)
        from xyzA AxRz ExPz show "x \<^bsub>(?sdf P)\<^esub>\<prec> z" unfolding strict_pref_def by auto
      qed
    qed
  qed
  ultimately show thesis ..
qed

text \<open>Sen makes several other stronger statements about SDFs later in the
chapter. I leave these for future work.\<close>

(* **************************************** *)

subsection\<open>Sen's Liberal Paradox\<close>

text\<open>Having side-stepped Arrow's Theorem, Sen proceeds to other conditions
one may ask of an SCF. His analysis of \emph{liberalism}, mechanised in this
section, has attracted much criticism over the years
\cite{AnalyseKritik:1996}.

Following \cite[Chapter~6*]{Sen:70a}, a \emph{liberal} social choice rule is
one that, for each individual, there is a pair of alternatives that she is
decisive over.\<close>

definition liberal :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "liberal scf A Is \<equiv>
    (\<forall>i \<in> Is. \<exists>x \<in> A. \<exists>y \<in> A. x \<noteq> y
      \<and> decisive scf A Is {i} x y \<and> decisive scf A Is {i} y x)"

lemma liberalE:
  "\<lbrakk> liberal scf A Is; i \<in> Is \<rbrakk>
   \<Longrightarrow> \<exists>x \<in> A. \<exists>y \<in> A. x \<noteq> y
         \<and> decisive scf A Is {i} x y \<and> decisive scf A Is {i} y x"
  by (simp add: liberal_def)

text\<open>This condition can be weakened to require just two such decisive
individuals; if we required just one, we would allow dictatorships, which
are clearly not liberal.\<close>

definition minimally_liberal :: "('a, 'i) SCF \<Rightarrow> 'a set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "minimally_liberal scf A Is \<equiv>
    (\<exists>i \<in> Is. \<exists>j \<in> Is. i \<noteq> j
      \<and> (\<exists>x \<in> A. \<exists>y \<in> A. x \<noteq> y
         \<and> decisive scf A Is {i} x y \<and> decisive scf A Is {i} y x)
      \<and> (\<exists>x \<in> A. \<exists>y \<in> A. x \<noteq> y
         \<and> decisive scf A Is {j} x y \<and> decisive scf A Is {j} y x))"

lemma liberal_imp_minimally_liberal:
  assumes has2Is: "has 2 Is"
      and L: "liberal scf A Is"
  shows "minimally_liberal scf A Is"
proof -
  from has_extend_witness[where xs="[]", OF has2Is]
  obtain i where i: "i \<in> Is" by auto
  with has_extend_witness[where xs="[i]", OF has2Is]
  obtain j where j: "j \<in> Is" "i \<noteq> j" by auto
  from L i j show ?thesis
    unfolding minimally_liberal_def by (blast intro: liberalE)
qed

text\<open>

The key observation is that once we have at least two decisive individuals
we can complete the Condorcet (paradox of voting) cycle using the weak
Pareto assumption. The details of the proof don't give more insight.

Firstly we need three types of profile witnesses (one of which we saw
previously). The main proof proceeds by case distinctions on which
alternatives the two liberal agents are decisive for.

\<close>

lemmas liberal_witness_two = SDF_nodictator_witness

lemma liberal_witness_three:
  assumes threeA: "hasw [x,y,v] A"
      and twoIs: "hasw [i,j] Is"
  obtains P
    where "profile A Is P"
      and "x \<^bsub>(P i)\<^esub>\<prec> y"
      and "v \<^bsub>(P j)\<^esub>\<prec> x"
      and "\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> v"
proof -
  let ?P =
    "\<lambda>a. if a = i then { (x, u) | u. u \<in> A }
                     \<union> { (y, u) | u. u \<in> A - {x} }
                     \<union> (A - {x,y}) \<times> (A - {x,y})
                  else { (y, u) | u. u \<in> A }
                     \<union> { (v, u) | u. u \<in> A - {y} }
                     \<union> (A - {v,y}) \<times> (A - {v,y})"
  have "profile A Is ?P"
  proof
    fix i assume iis: "i \<in> Is"
    show "rpr A (?P i)"
    proof
      show "complete A (?P i)" by (simp, blast)
      from threeA iis show "refl_on A (?P i)" by (simp, blast)
      from threeA iis show "trans (?P i)" by (clarsimp simp add: trans_def)
    qed
  next
    from twoIs show "Is \<noteq> {}" by auto
  qed
  moreover
  from threeA twoIs have "x \<^bsub>(?P i)\<^esub>\<prec> y" "v \<^bsub>(?P j)\<^esub>\<prec> x" "\<forall>i \<in> Is. y \<^bsub>(?P i)\<^esub>\<prec> v"
    unfolding strict_pref_def by auto
  ultimately show ?thesis ..
qed

lemma liberal_witness_four:
  assumes fourA: "hasw [x,y,u,v] A"
      and twoIs: "hasw [i,j] Is"
  obtains P
    where "profile A Is P"
      and "x \<^bsub>(P i)\<^esub>\<prec> y"
      and "u \<^bsub>(P j)\<^esub>\<prec> v"
      and "\<forall>i \<in> Is. v \<^bsub>(P i)\<^esub>\<prec> x \<and> y \<^bsub>(P i)\<^esub>\<prec> u"
proof -
  let ?P =
    "\<lambda>a. if a = i then { (v, w) | w. w \<in> A }
                     \<union> { (x, w) | w. w \<in> A - {v} }
                     \<union> { (y, w) | w. w \<in> A - {v,x} }
                     \<union> (A - {v,x,y}) \<times> (A - {v,x,y})
                  else { (y, w) | w. w \<in> A }
                     \<union> { (u, w) | w. w \<in> A - {y} }
                     \<union> { (v, w) | w. w \<in> A - {u,y} }
                     \<union> (A - {u,v,y}) \<times> (A - {u,v,y})"
  have "profile A Is ?P"
  proof
    fix i assume iis: "i \<in> Is"
    show "rpr A (?P i)"
    proof
      show "complete A (?P i)" by (simp, blast)
      from fourA iis show "refl_on A (?P i)" by (simp, blast)
      from fourA iis show "trans (?P i)" by (clarsimp simp add: trans_def)
    qed
  next
    from twoIs show "Is \<noteq> {}" by auto
  qed
  moreover
  from fourA twoIs have "x \<^bsub>(?P i)\<^esub>\<prec> y" "u \<^bsub>(?P j)\<^esub>\<prec> v" "\<forall>i \<in> Is. v \<^bsub>(?P i)\<^esub>\<prec> x \<and> y \<^bsub>(?P i)\<^esub>\<prec> u"
    by (unfold strict_pref_def, auto)
  ultimately show thesis ..
qed

text\<open>The Liberal Paradox: having two decisive individuals, an SDF and the
weak pareto assumption is inconsistent.\<close>

theorem LiberalParadox:
  assumes SDF: "SDF sdf A Is universal_domain"
      and ml: "minimally_liberal sdf A Is"
      and wp: "weak_pareto sdf A Is universal_domain"
  shows False
proof -
  from ml obtain i j x y u v 
    where i: "i \<in> Is" and j: "j \<in> Is" and ij: "i \<noteq> j"
      and x: "x \<in> A" and y: "y \<in> A" and u: "u \<in> A" and v: "v \<in> A"
      and xy: "x \<noteq> y"
      and dixy: "decisive sdf A Is {i} x y"
      and diyx: "decisive sdf A Is {i} y x"
      and uv: "u \<noteq> v"
      and djuv: "decisive sdf A Is {j} u v"
      and djvu: "decisive sdf A Is {j} v u"
    by (unfold minimally_liberal_def, auto)
  from i j ij have twoIs: "hasw [i,j] Is" by simp
  {
    assume xu: "x = u" and yv: "y = v"
    from xy x y have twoA: "hasw [x,y] A" by simp
    obtain P
      where "profile A Is P" "x \<^bsub>(P i)\<^esub>\<prec> y" "y \<^bsub>(P j)\<^esub>\<prec> x"
      using liberal_witness_two[OF twoA twoIs] by blast
    with i j dixy djvu xu yv have False
      by (unfold decisive_def strict_pref_def, blast)
  }
  moreover
  {
    assume xu: "x = u" and yv: "y \<noteq> v"
    with xy uv xu x y v have threeA: "hasw [x,y,v] A" by simp
    obtain P
      where profileP: "profile A Is P"
        and xPiy: "x \<^bsub>(P i)\<^esub>\<prec> y"
        and vPjx: "v \<^bsub>(P j)\<^esub>\<prec> x"
        and AyPv: "\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> v"
      using liberal_witness_three[OF threeA twoIs] by blast
    from vPjx j djvu xu profileP have vPx: "v \<^bsub>(sdf P)\<^esub>\<prec> x"
      by (unfold decisive_def strict_pref_def, auto)
    from xPiy i dixy profileP have xPy: "x \<^bsub>(sdf P)\<^esub>\<prec> y"
      by (unfold decisive_def strict_pref_def, auto)
    from AyPv weak_paretoD[OF wp _ y v] profileP have yPv: "y \<^bsub>(sdf P)\<^esub>\<prec> v"
      by auto
    from threeA profileP SDF have "choiceSet {x,y,v} (sdf P) \<noteq> {}"
      by (simp add: SDF_def choiceFn_def)
    with vPx xPy yPv have False
      by (unfold choiceSet_def strict_pref_def, blast)
  }
  moreover
  {
    assume xv: "x = v" and yu: "y = u"
    from xy x y have twoA: "hasw [x,y] A" by auto
    obtain P
      where "profile A Is P" "x \<^bsub>(P i)\<^esub>\<prec> y" "y \<^bsub>(P j)\<^esub>\<prec> x"
      using liberal_witness_two[OF twoA twoIs] by blast
    with i j dixy djuv xv yu have False
      by (unfold decisive_def strict_pref_def, blast)
  }
  moreover
  {
    assume xv: "x = v" and yu: "y \<noteq> u"
    with xy uv u x y have threeA: "hasw [x,y,u] A" by simp
    obtain P
      where profileP: "profile A Is P"
        and xPiy: "x \<^bsub>(P i)\<^esub>\<prec> y"
        and uPjx: "u \<^bsub>(P j)\<^esub>\<prec> x"
        and AyPu: "\<forall>i \<in> Is. y \<^bsub>(P i)\<^esub>\<prec> u"
      using liberal_witness_three[OF threeA twoIs] by blast
    from uPjx j djuv xv profileP have uPx: "u \<^bsub>(sdf P)\<^esub>\<prec> x"
      by (unfold decisive_def strict_pref_def, auto)
    from xPiy i dixy profileP have xPy: "x \<^bsub>(sdf P)\<^esub>\<prec> y"
      by (unfold decisive_def strict_pref_def, auto)
    from AyPu weak_paretoD[OF wp _ y u] profileP have yPu: "y \<^bsub>(sdf P)\<^esub>\<prec> u"
      by auto
    from threeA profileP SDF have "choiceSet {x,y,u} (sdf P) \<noteq> {}"
      by (simp add: SDF_def choiceFn_def)
    with uPx xPy yPu have False
      by (unfold choiceSet_def strict_pref_def, blast)
  }
  moreover
  {
    assume xu: "x \<noteq> u" and xv: "x \<noteq> v" and yu: "y = u"
    with v x y xy uv xu have threeA: "hasw [y,x,v] A" by simp
    obtain P
      where profileP: "profile A Is P"
        and yPix: "y \<^bsub>(P i)\<^esub>\<prec> x"
        and vPjy: "v \<^bsub>(P j)\<^esub>\<prec> y"
        and AxPv: "\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> v"
      using liberal_witness_three[OF threeA twoIs] by blast
    from yPix i diyx profileP have yPx: "y \<^bsub>(sdf P)\<^esub>\<prec> x"
      by (unfold decisive_def strict_pref_def, auto)
    from vPjy j djvu yu profileP have vPy: "v \<^bsub>(sdf P)\<^esub>\<prec> y"
      by (unfold decisive_def strict_pref_def, auto)
    from AxPv weak_paretoD[OF wp _ x v] profileP have xPv: "x \<^bsub>(sdf P)\<^esub>\<prec> v"
      by auto
    from threeA profileP SDF have "choiceSet {x,y,v} (sdf P) \<noteq> {}"
      by (simp add: SDF_def choiceFn_def)
    with yPx vPy xPv have False
      by (unfold choiceSet_def strict_pref_def, blast)
  }
  moreover
  {
    assume xu: "x \<noteq> u" and xv: "x \<noteq> v" and yv: "y = v"
    with u x y xy uv xu have threeA: "hasw [y,x,u] A" by simp
    obtain P
      where profileP: "profile A Is P"
        and yPix: "y \<^bsub>(P i)\<^esub>\<prec> x"
        and uPjy: "u \<^bsub>(P j)\<^esub>\<prec> y"
        and AxPu: "\<forall>i \<in> Is. x \<^bsub>(P i)\<^esub>\<prec> u"
      using liberal_witness_three[OF threeA twoIs] by blast
    from yPix i diyx profileP have yPx: "y \<^bsub>(sdf P)\<^esub>\<prec> x"
      by (unfold decisive_def strict_pref_def, auto)
    from uPjy j djuv yv profileP have uPy: "u \<^bsub>(sdf P)\<^esub>\<prec> y"
      by (unfold decisive_def strict_pref_def, auto)
    from AxPu weak_paretoD[OF wp _ x u] profileP have xPu: "x \<^bsub>(sdf P)\<^esub>\<prec> u"
      by auto
    from threeA profileP SDF have "choiceSet {x,y,u} (sdf P) \<noteq> {}"
      by (simp add: SDF_def choiceFn_def)
    with yPx uPy xPu have False
      by (unfold choiceSet_def strict_pref_def, blast)
  }
  moreover
  {
    assume xu: "x \<noteq> u" and xv: "x \<noteq> v" and yu: "y \<noteq> u" and yv: "y \<noteq> v"
    with u v x y xy uv xu have fourA: "hasw [x,y,u,v] A" by simp
    obtain P
      where profileP: "profile A Is P"
        and xPiy: "x \<^bsub>(P i)\<^esub>\<prec> y"
        and uPjv: "u \<^bsub>(P j)\<^esub>\<prec> v"
        and AvPxAyPu: "\<forall>i \<in> Is. v \<^bsub>(P i)\<^esub>\<prec> x \<and> y \<^bsub>(P i)\<^esub>\<prec> u"
      using liberal_witness_four[OF fourA twoIs] by blast
    from xPiy i dixy profileP have xPy: "x \<^bsub>(sdf P)\<^esub>\<prec> y"
      by (unfold decisive_def strict_pref_def, auto)
    from uPjv j djuv profileP have uPv: "u \<^bsub>(sdf P)\<^esub>\<prec> v"
      by (unfold decisive_def strict_pref_def, auto)
    from AvPxAyPu weak_paretoD[OF wp] profileP x y u v
    have vPx: "v \<^bsub>(sdf P)\<^esub>\<prec> x" and yPu: "y \<^bsub>(sdf P)\<^esub>\<prec> u" by auto
    from fourA profileP SDF have "choiceSet {x,y,u,v} (sdf P) \<noteq> {}"
      by (simp add: SDF_def choiceFn_def)
    with xPy uPv vPx yPu have False
      by (unfold choiceSet_def strict_pref_def, blast)
  }
  ultimately show False by blast
qed

(*<*)
end
(*>*)
