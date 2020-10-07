(*
 * Arrow's General Possibility Theorem, following Sen.
 * (C)opyright Peter Gammie, peteg42 at gmail.com, commenced July 2006.
 * License: BSD
 *)

(*<*)
theory Arrow

imports SCFs

begin
(*>*)

section\<open>Arrow's General Possibility Theorem\<close>

text\<open>

The proof falls into two parts: showing that a semi-decisive individual is
in fact a dictator, and that a semi-decisive individual exists. I take them
in that order.

It might be good to do some of this in a locale. The complication is
untangling where various witnesses need to be quantified over.

\<close>

(* **************************************** *)

subsection\<open>Semi-decisiveness Implies Decisiveness\<close>

text\<open>

I follow \cite[Chapter~3*]{Sen:70a} quite closely here. Formalising his
appeal to the @{term "iia"} assumption is the main complication here.

\<close>

text\<open>The witness for the first lemma: in the profile $P'$, special agent
$j$ strictly prefers $x$ to $y$ to $z$, and doesn't care about the other
alternatives. Everyone else strictly prefers $y$ to each of $x$ to $z$, and
inherits the relative preferences between $x$ and $z$ from profile $P$.

The model has to be specific about ordering all the other alternatives, but
these are immaterial in the proof that uses this witness. Note also that the
following lemma is used with different instantiations of $x$, $y$ and $z$,
so we need to quantify over them here. This happens implicitly, but in a
locale we would have to be more explicit.

This is just tedious.\<close>

lemma decisive1_witness:
  assumes has3A: "hasw [x,y,z] A"
      and profileP: "profile A Is P"
      and jIs: "j \<in> Is"
  obtains P'
  where "profile A Is P'"
    and "x \<^bsub>(P' j)\<^esub>\<prec> y \<and> y \<^bsub>(P' j)\<^esub>\<prec> z"
    and "\<And>i. i \<noteq> j \<Longrightarrow> y \<^bsub>(P' i)\<^esub>\<prec> x \<and> y \<^bsub>(P' i)\<^esub>\<prec> z \<and> ((x \<^bsub>(P' i)\<^esub>\<preceq> z) = (x \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(P' i)\<^esub>\<preceq> x) = (z \<^bsub>(P i)\<^esub>\<preceq> x))"
proof
  let ?P' = "\<lambda>i. (if i = j then ({ (x, u) | u. u \<in> A }
                               \<union> { (y, u) | u. u \<in> A - {x} }
                               \<union> { (z, u) | u. u \<in> A - {x,y} })
                           else ({ (y, u) | u. u \<in> A }
                               \<union> { (x, u) | u. u \<in> A - {y,z} }
                               \<union> { (z, u) | u. u \<in> A - {x,y} }
                               \<union> (if x \<^bsub>(P i)\<^esub>\<preceq> z then {(x,z)} else {})
                               \<union> (if z \<^bsub>(P i)\<^esub>\<preceq> x then {(z,x)} else {})))
                      \<union> (A - {x,y,z}) \<times> (A - {x,y,z})"
  show "profile A Is ?P'"
  proof
    fix i assume iIs: "i \<in> Is"
    show "rpr A (?P' i)"
    proof(cases "i = j")
      case True with has3A show ?thesis
        by - (rule rprI, simp_all add: trans_def, blast+)
    next
      case False hence ij: "i \<noteq> j" .
      show ?thesis
      proof
        from iIs profileP have "complete A (P i)" by (blast dest: rpr_complete)
        with ij show "complete A (?P' i)" by (simp add: complete_def, blast)
        from iIs profileP have "refl_on A (P i)" by (auto simp add: rpr_def)
        with has3A ij show "refl_on A (?P' i)" by (simp, blast)
        from ij has3A show "trans (?P' i)" by (clarsimp simp add: trans_def)
      qed
    qed
  next
    from profileP show "Is \<noteq> {}" by (rule profile_non_empty)
  qed
  from has3A
  show "x \<^bsub>(?P' j)\<^esub>\<prec> y \<and> y \<^bsub>(?P' j)\<^esub>\<prec> z"
   and "\<And>i. i \<noteq> j \<Longrightarrow> y \<^bsub>(?P' i)\<^esub>\<prec> x \<and> y \<^bsub>(?P' i)\<^esub>\<prec> z \<and> ((x \<^bsub>(?P' i)\<^esub>\<preceq> z) = (x \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(?P' i)\<^esub>\<preceq> x) = (z \<^bsub>(P i)\<^esub>\<preceq> x))"
    unfolding strict_pref_def by auto
qed

text \<open>The key lemma: in the presence of Arrow's assumptions, an individual
who is semi-decisive for $x$ and $y$ is actually decisive for $x$ over any
other alternative $z$. (This is where the quantification becomes important.) 
\<close>

lemma decisive1:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x y"
  shows "decisive swf A Is {j} x z"
proof
  from sd show jIs: "{j} \<subseteq> Is" by blast
  fix P
  assume profileP: "profile A Is P"
     and jxzP: "\<And>i. i \<in> {j} \<Longrightarrow> x \<^bsub>(P i)\<^esub>\<prec> z"
  from has3A profileP jIs
  obtain P'
    where profileP': "profile A Is P'"
      and jxyzP': "x \<^bsub>(P' j)\<^esub>\<prec> y" "y \<^bsub>(P' j)\<^esub>\<prec> z"
      and ixyzP': "\<And>i. i \<noteq> j \<longrightarrow> y \<^bsub>(P' i)\<^esub>\<prec> x \<and> y \<^bsub>(P' i)\<^esub>\<prec> z \<and> ((x \<^bsub>(P' i)\<^esub>\<preceq> z) = (x \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(P' i)\<^esub>\<preceq> x) = (z \<^bsub>(P i)\<^esub>\<preceq> x))"
    by - (rule decisive1_witness, blast+)
  from iia have "\<And>a b. \<lbrakk> a \<in> {x, z}; b \<in> {x, z} \<rbrakk> \<Longrightarrow> (a \<^bsub>(swf P)\<^esub>\<preceq> b) = (a \<^bsub>(swf P')\<^esub>\<preceq> b)"
  proof(rule iiaE)
    from has3A show "{x,z} \<subseteq> A" by simp
  next
    fix i assume iIs: "i \<in> Is"
    fix a b assume ab: "a \<in> {x, z}" "b \<in> {x, z}"
    show "(a \<^bsub>(P' i)\<^esub>\<preceq> b) = (a \<^bsub>(P i)\<^esub>\<preceq> b)"
    proof(cases "i = j")
      case False
      with ab iIs ixyzP' profileP profileP' has3A
      show ?thesis unfolding profile_def by auto
    next
      case True
      from profileP' jIs jxyzP' have "x \<^bsub>(P' j)\<^esub>\<prec> z"
        by (auto dest: rpr_less_trans)
      with True ab iIs jxzP profileP profileP' has3A
      show ?thesis unfolding profile_def strict_pref_def by auto
    qed
  qed (simp_all add: profileP profileP')
  moreover have "x \<^bsub>(swf P')\<^esub>\<prec> z"
  proof -
    from profileP' sd jxyzP' ixyzP' have "x \<^bsub>(swf P')\<^esub>\<prec> y" by (simp add: semidecisive_def)
    moreover
    from jxyzP' ixyzP' have "\<And>i. i \<in> Is \<Longrightarrow> y \<^bsub>(P' i)\<^esub>\<prec> z" by (case_tac "i=j", auto)
    with wp profileP' has3A have "y \<^bsub>(swf P')\<^esub>\<prec> z" by (auto dest: weak_paretoD)
    moreover note SWF_rpr[OF swf] profileP'
    ultimately show "x \<^bsub>(swf P')\<^esub>\<prec> z"
      unfolding universal_domain_def by (blast dest: rpr_less_trans)
  qed
  ultimately show "x \<^bsub>(swf P)\<^esub>\<prec> z" unfolding strict_pref_def by blast
qed

text\<open>The witness for the second lemma: special agent $j$ strictly prefers
$z$ to $x$ to $y$, and everyone else strictly prefers $z$ to $x$ and $y$ to
$x$. (In some sense the last part is upside-down with respect to the first
witness.)\<close>

lemma decisive2_witness:
  assumes has3A: "hasw [x,y,z] A"
      and profileP: "profile A Is P"
      and jIs: "j \<in> Is"
  obtains P'
    where "profile A Is P'"
      and "z \<^bsub>(P' j)\<^esub>\<prec> x \<and> x \<^bsub>(P' j)\<^esub>\<prec> y"
      and "\<And>i. i \<noteq> j \<Longrightarrow> z \<^bsub>(P' i)\<^esub>\<prec> x \<and> y \<^bsub>(P' i)\<^esub>\<prec> x \<and> ((y \<^bsub>(P' i)\<^esub>\<preceq> z) = (y \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(P' i)\<^esub>\<preceq> y) = (z \<^bsub>(P i)\<^esub>\<preceq> y))"
proof
  let ?P' = "\<lambda>i. (if i = j then ({ (z, u) | u. u \<in> A }
                               \<union> { (x, u) | u. u \<in> A - {z} }
                               \<union> { (y, u) | u. u \<in> A - {x,z} })
                           else ({ (z, u) | u. u \<in> A - {y} }
                               \<union> { (y, u) | u. u \<in> A - {z} }
                               \<union> { (x, u) | u. u \<in> A - {y,z} }
                               \<union> (if y \<^bsub>(P i)\<^esub>\<preceq> z then {(y,z)} else {})
                               \<union> (if z \<^bsub>(P i)\<^esub>\<preceq> y then {(z,y)} else {})))
                      \<union> (A - {x,y,z}) \<times> (A - {x,y,z})"
  show "profile A Is ?P'"
  proof
    fix i assume iIs: "i \<in> Is"
    show "rpr A (?P' i)"
    proof(cases "i = j")
      case True with has3A show ?thesis
        by - (rule rprI, simp_all add: trans_def, blast+)
    next
      case False hence ij: "i \<noteq> j" .
      show ?thesis
      proof
        from iIs profileP have "complete A (P i)" by (auto simp add: rpr_def)
        with ij show "complete A (?P' i)" by (simp add: complete_def, blast)
        from iIs profileP have "refl_on A (P i)" by (auto simp add: rpr_def)
        with has3A ij show "refl_on A (?P' i)" by (simp, blast)
        from ij has3A show "trans (?P' i)" by (clarsimp simp add: trans_def)
      qed
    qed
  next
    show "Is \<noteq> {}" by (rule profile_non_empty[OF profileP])
  qed
  from has3A
  show "z \<^bsub>(?P' j)\<^esub>\<prec> x \<and> x \<^bsub>(?P' j)\<^esub>\<prec> y"
   and "\<And>i. i \<noteq> j \<Longrightarrow> z \<^bsub>(?P' i)\<^esub>\<prec> x \<and> y \<^bsub>(?P' i)\<^esub>\<prec> x \<and> ((y \<^bsub>(?P' i)\<^esub>\<preceq> z) = (y \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(?P' i)\<^esub>\<preceq> y) = (z \<^bsub>(P i)\<^esub>\<preceq> y))"
    unfolding strict_pref_def by auto
qed

lemma decisive2:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x y"
  shows "decisive swf A Is {j} z y"
proof
  from sd show jIs: "{j} \<subseteq> Is" by blast
  fix P
  assume profileP: "profile A Is P"
     and jyzP: "\<And>i. i \<in> {j} \<Longrightarrow> z \<^bsub>(P i)\<^esub>\<prec> y"
  from has3A profileP jIs
  obtain P'
    where profileP': "profile A Is P'"
      and jxyzP': "z \<^bsub>(P' j)\<^esub>\<prec> x" "x \<^bsub>(P' j)\<^esub>\<prec> y"
      and ixyzP': "\<And>i. i \<noteq> j \<longrightarrow> z \<^bsub>(P' i)\<^esub>\<prec> x \<and> y \<^bsub>(P' i)\<^esub>\<prec> x \<and> ((y \<^bsub>(P' i)\<^esub>\<preceq> z) = (y \<^bsub>(P i)\<^esub>\<preceq> z)) \<and> ((z \<^bsub>(P' i)\<^esub>\<preceq> y) = (z \<^bsub>(P i)\<^esub>\<preceq> y))"
    by - (rule decisive2_witness, blast+)
  from iia have "\<And>a b. \<lbrakk> a \<in> {y, z}; b \<in> {y, z} \<rbrakk> \<Longrightarrow> (a \<^bsub>(swf P)\<^esub>\<preceq> b) = (a \<^bsub>(swf P')\<^esub>\<preceq> b)"
  proof(rule iiaE)
    from has3A show "{y,z} \<subseteq> A" by simp
  next
    fix i assume iIs: "i \<in> Is"
    fix a b assume ab: "a \<in> {y, z}" "b \<in> {y, z}"
    show "(a \<^bsub>(P' i)\<^esub>\<preceq> b) = (a \<^bsub>(P i)\<^esub>\<preceq> b)"
    proof(cases "i = j")
      case False
      with ab iIs ixyzP' profileP profileP' has3A
      show ?thesis unfolding profile_def by auto
    next
      case True
      from profileP' jIs jxyzP' have "z \<^bsub>(P' j)\<^esub>\<prec> y"
        by (auto dest: rpr_less_trans)
      with True ab iIs jyzP profileP profileP' has3A
      show ?thesis unfolding profile_def strict_pref_def by auto
    qed
  qed (simp_all add: profileP profileP')
  moreover have "z \<^bsub>(swf P')\<^esub>\<prec> y"
  proof -
    from profileP' sd jxyzP' ixyzP' have "x \<^bsub>(swf P')\<^esub>\<prec> y" by (simp add: semidecisive_def)
    moreover
    from jxyzP' ixyzP' have "\<And>i. i \<in> Is \<Longrightarrow> z \<^bsub>(P' i)\<^esub>\<prec> x" by (case_tac "i=j", auto)
    with wp profileP' has3A have "z \<^bsub>(swf P')\<^esub>\<prec> x" by (auto dest: weak_paretoD)
    moreover note SWF_rpr[OF swf] profileP'
    ultimately show "z \<^bsub>(swf P')\<^esub>\<prec> y"
      unfolding universal_domain_def by (blast dest: rpr_less_trans)
  qed
  ultimately show "z \<^bsub>(swf P)\<^esub>\<prec> y" unfolding strict_pref_def by blast
qed

text \<open>The following results permute $x$, $y$ and $z$ to show how
decisiveness can be obtained from semi-decisiveness in all cases. Again,
quite tedious.\<close>

lemma decisive3:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x z"
  shows "decisive swf A Is {j} y z"
  using has3A decisive2[OF _ iia swf wp sd] by (simp, blast)

lemma decisive4:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} y z"
  shows "decisive swf A Is {j} y x"
  using has3A decisive1[OF _ iia swf wp sd] by (simp, blast)

lemma decisive5:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x y"
  shows "decisive swf A Is {j} y x"
proof -
  from sd
  have "decisive swf A Is {j} x z" by (rule decisive1[OF has3A iia swf wp])
  hence "semidecisive swf A Is {j} x z" by (rule d_imp_sd)
  hence "decisive swf A Is {j} y z" by (rule decisive3[OF has3A iia swf wp])
  hence "semidecisive swf A Is {j} y z" by (rule d_imp_sd)
  thus "decisive swf A Is {j} y x" by (rule decisive4[OF has3A iia swf wp])
qed

lemma decisive6:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} y x"
  shows "decisive swf A Is {j} y z" "decisive swf A Is {j} z x" "decisive swf A Is {j} x y"
proof -
  from has3A have has3A': "hasw [y,x,z] A" by auto
  show "decisive swf A Is {j} y z" by (rule decisive1[OF has3A' iia swf wp sd])
  show "decisive swf A Is {j} z x" by (rule decisive2[OF has3A' iia swf wp sd])
  show "decisive swf A Is {j} x y" by (rule decisive5[OF has3A' iia swf wp sd])
qed

lemma decisive7:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x y"
  shows "decisive swf A Is {j} y z" "decisive swf A Is {j} z x" "decisive swf A Is {j} x y"
proof -
  from sd
  have "decisive swf A Is {j} y x" by (rule decisive5[OF has3A iia swf wp])
  hence "semidecisive swf A Is {j} y x" by (rule d_imp_sd)
  thus "decisive swf A Is {j} y z" "decisive swf A Is {j} z x" "decisive swf A Is {j} x y"
    by (rule decisive6[OF has3A iia swf wp])+
qed

lemma j_decisive_xy:
  assumes has3A: "hasw [x,y,z] A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and sd: "semidecisive swf A Is {j} x y"
      and uv: "hasw [u,v] {x,y,z}"
  shows "decisive swf A Is {j} u v"
  using uv decisive1[OF has3A iia swf wp sd]
           decisive2[OF has3A iia swf wp sd]
           decisive5[OF has3A iia swf wp sd]
           decisive7[OF has3A iia swf wp sd]
  by (simp, blast)

lemma j_decisive:
  assumes has3A: "has 3 A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and xyA: "hasw [x,y] A"
      and sd: "semidecisive swf A Is {j} x y"
      and uv: "hasw [u,v] A"
  shows "decisive swf A Is {j} u v"
proof -
  from has_extend_witness'[OF has3A xyA]
  obtain z where xyzA: "hasw [x,y,z] A" by auto
  {
    assume ux: "u = x" and vy: "v = y"
    with xyzA iia swf wp sd have ?thesis by (auto intro: j_decisive_xy)
  }
  moreover
  {
    assume ux: "u = x" and vNEy: "v \<noteq> y"
    with uv xyA iia swf wp sd have ?thesis by(auto intro: j_decisive_xy[of x y])
  }
  moreover
  {
    assume uy: "u = y" and vx: "v = x"
    with xyzA iia swf wp sd have ?thesis by (auto intro: j_decisive_xy)
  }
  moreover
  {
    assume uy: "u = y" and vNEx: "v \<noteq> x"
    with uv xyA iia swf wp sd have ?thesis by (auto intro: j_decisive_xy)
  }
  moreover
  {
    assume uNExy: "u \<notin> {x,y}" and vx: "v = x"
    with uv xyA iia swf wp sd have ?thesis by (auto intro: j_decisive_xy[of x y])
  }
  moreover
  {
    assume uNExy: "u \<notin> {x,y}" and vy: "v = y"
    with uv xyA iia swf wp sd have ?thesis by (auto intro: j_decisive_xy[of x y])
  }
  moreover
  {
    assume uNExy: "u \<notin> {x,y}" and vNExy: "v \<notin> {x,y}"
    with uv xyA iia swf wp sd
    have "decisive swf A Is {j} x u" by (auto intro: j_decisive_xy[where x=x and z=u])
    hence sdxu: "semidecisive swf A Is {j} x u" by (rule d_imp_sd)
    with uNExy vNExy uv xyA iia swf wp have ?thesis by (auto intro: j_decisive_xy[of x])
  }
  ultimately show ?thesis by blast
qed

text \<open>The first result: if $j$ is semidecisive for some alternatives $u$
and $v$, then they are actually a dictator.\<close>

lemma sd_imp_dictator:
  assumes has3A: "has 3 A"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
      and uv: "hasw [u,v] A"
      and sd: "semidecisive swf A Is {j} u v"
  shows "dictator swf A Is j"
proof
  fix x y assume x: "x \<in> A" and y: "y \<in> A"
  show "decisive swf A Is {j} x y"
  proof(cases "x = y")
    case True with sd show "decisive swf A Is {j} x y" by (blast intro: d_refl)
  next
    case False
    with x y iia swf wp has3A uv sd show "decisive swf A Is {j} x y"
      by (auto intro: j_decisive)
  qed
next
  from sd show "j \<in> Is" by blast
qed

(* **************************************** *)

subsection\<open>The Existence of a Semi-decisive Individual\<close>

text\<open>The second half of the proof establishes the existence of a
semi-decisive individual. The required witness is essentially an encoding of
the Condorcet pardox (aka "the paradox of voting" that shows we get tied up
in knots if a certain agent didn't have dictatorial powers.\<close>

lemma sd_exists_witness:
  assumes has3A: "hasw [x,y,z] A"
      and Vs: "Is = V1 \<union> V2 \<union> V3
                \<and> V1 \<inter> V2 = {} \<and> V1 \<inter> V3 = {} \<and> V2 \<inter> V3 = {}"
      and Is: "Is \<noteq> {}"
  obtains P
    where "profile A Is P"
      and "\<forall>i \<in> V1. x \<^bsub>(P i)\<^esub>\<prec> y \<and> y \<^bsub>(P i)\<^esub>\<prec> z"
      and "\<forall>i \<in> V2. z \<^bsub>(P i)\<^esub>\<prec> x \<and> x \<^bsub>(P i)\<^esub>\<prec> y"
      and "\<forall>i \<in> V3. y \<^bsub>(P i)\<^esub>\<prec> z \<and> z \<^bsub>(P i)\<^esub>\<prec> x"
proof
  let ?P =
    "\<lambda>i. (if i \<in> V1 then  ({ (x, u) | u. u \<in> A }
                         \<union> { (y, u) | u. u \<in> A \<and> u \<noteq> x }
                         \<union> { (z, u) | u. u \<in> A \<and> u \<noteq> x \<and> u \<noteq> y })
                    else 
          if i \<in> V2 then ({ (z, u) | u. u \<in> A }
                        \<union> { (x, u) | u. u \<in> A \<and> u \<noteq> z }
                        \<union> { (y, u) | u. u \<in> A \<and> u \<noteq> x \<and> u \<noteq> z }) 
                   else  ({ (y, u) | u. u \<in> A }
                        \<union> { (z, u) | u. u \<in> A \<and> u \<noteq> y }
                        \<union> { (x, u) | u. u \<in> A \<and> u \<noteq> y \<and> u \<noteq> z }))
                      \<union> { (u, v) | u v. u \<in> A - {x,y,z} \<and> v \<in> A - {x,y,z}}"
  show "profile A Is ?P"
  proof
    fix i assume iIs: "i \<in> Is"
    show "rpr A (?P i)"
    proof
      show "complete A (?P i)" by (simp add: complete_def, blast)
      from has3A iIs show "refl_on A (?P i)" by - (simp, blast)
      from has3A iIs show "trans (?P i)" by (clarsimp simp add: trans_def)
    qed
  next
    from Is show "Is \<noteq> {}" .
  qed
  from has3A Vs
  show "\<forall>i \<in> V1. x \<^bsub>(?P i)\<^esub>\<prec> y \<and> y \<^bsub>(?P i)\<^esub>\<prec> z"
   and "\<forall>i \<in> V2. z \<^bsub>(?P i)\<^esub>\<prec> x \<and> x \<^bsub>(?P i)\<^esub>\<prec> y"
   and "\<forall>i \<in> V3. y \<^bsub>(?P i)\<^esub>\<prec> z \<and> z \<^bsub>(?P i)\<^esub>\<prec> x"
    unfolding strict_pref_def by auto
qed

text \<open>This proof is unfortunately long. Many of the statements rely on a
lot of context, making it difficult to split it up.\<close>

lemma sd_exists:
  assumes has3A: "has 3 A"
      and finiteIs: "finite Is"
      and twoIs: "has 2 Is"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
  shows "\<exists>j u v. hasw [u,v] A \<and> semidecisive swf A Is {j} u v"
proof -
  let ?P = "\<lambda>S. S \<subseteq> Is \<and> S \<noteq> {} \<and> (\<exists>u v. hasw [u,v] A \<and> semidecisive swf A Is S u v)"
  obtain u v where uvA: "hasw [u,v] A" 
    using has_witness_two[OF has3A] by auto
      \<comment> \<open>The weak pareto requirement implies that the set of all
      individuals is decisive between any given alternatives.\<close>
  hence "decisive swf A Is Is u v"
    by - (rule, auto intro: weak_paretoD[OF wp])
  hence "semidecisive swf A Is Is u v" by (rule d_imp_sd)
  with uvA twoIs has_suc_notempty[where n=1] nat_2[symmetric]
  have "?P Is" by auto
      \<comment> \<open>Obtain a minimally-sized semi-decisive set.\<close>
  from ex_has_least_nat[where P="?P" and m="card", OF this]
  obtain V x y where VIs: "V \<subseteq> Is"
    and Vnotempty: "V \<noteq> {}"
    and xyA: "hasw [x,y] A"
    and Vsd: "semidecisive swf A Is V x y"
    and Vmin: "\<And>V'. ?P V' \<Longrightarrow> card V \<le> card V'"
    by blast
  from VIs finiteIs have Vfinite: "finite V" by (rule finite_subset)
      \<comment> \<open>Show that minimal set contains a single individual.\<close>
  from Vfinite Vnotempty have "\<exists>j. V = {j}"
  proof(rule finite_set_singleton_contra)
    assume Vcard: "1 < card V"
    then obtain j where jV: "{j} \<subseteq> V"
      using has_extend_witness[where xs="[]", OF card_has[where n="card V"]] by auto
        \<comment> \<open>Split an individual from the "minimal" set.\<close>
    let ?V1 = "{j}"
    let ?V2 = "V - ?V1"
    let ?V3 = "Is - V"
    from jV card_Diff_singleton[OF Vfinite] Vcard
    have V2card: "card ?V2 > 0" "card ?V2 < card V" by auto
    hence V2notempty: "{} \<noteq> ?V2" by auto
    from jV VIs
    have jV2V3: "Is = ?V1 \<union> ?V2 \<union> ?V3 \<and> ?V1 \<inter> ?V2 = {} \<and> ?V1 \<inter> ?V3 = {} \<and> ?V2 \<inter> ?V3 = {}"
      by auto
        \<comment> \<open>Show that that individual is semi-decisive for $x$ over $z$.\<close>
    from has_extend_witness'[OF has3A xyA]
    obtain z where threeDist: "hasw [x,y,z] A" by auto
    from sd_exists_witness[OF threeDist jV2V3] VIs Vnotempty
    obtain P where profileP: "profile A Is P"
               and V1xyzP: "x \<^bsub>(P j)\<^esub>\<prec> y \<and> y \<^bsub>(P j)\<^esub>\<prec> z"
               and V2xyzP: "\<forall>i \<in> ?V2. z \<^bsub>(P i)\<^esub>\<prec> x \<and> x \<^bsub>(P i)\<^esub>\<prec> y"
               and V3xyzP: "\<forall>i \<in> ?V3. y \<^bsub>(P i)\<^esub>\<prec> z \<and> z \<^bsub>(P i)\<^esub>\<prec> x"
      by (simp, blast)
    have xPz: "x \<^bsub>(swf P)\<^esub>\<prec> z"
    proof(rule rpr_less_le_trans[where y="y"])
      from profileP swf show "rpr A (swf P)" by auto
    next
        \<comment> \<open>V2 is semi-decisive, and everyone else opposes their choice. Ergo they prevail.\<close>
      show "x \<^bsub>(swf P)\<^esub>\<prec> y"
      proof -
        from profileP V3xyzP
        have "\<forall>i \<in> ?V3. y \<^bsub>(P i)\<^esub>\<prec> x" by (blast dest: rpr_less_trans)
        with profileP V1xyzP V2xyzP Vsd
        show ?thesis unfolding semidecisive_def by auto
      qed
    next
      \<comment> \<open>This result is unfortunately quite tortuous.\<close>
      from SWF_rpr[OF swf] show "y \<^bsub>(swf P)\<^esub>\<preceq> z"
      proof(rule rpr_less_not[OF _ _ notI])
        from threeDist show "hasw [z, y] A" by auto
      next
        assume zPy: "z \<^bsub>(swf P)\<^esub>\<prec> y"
        have "semidecisive swf A Is ?V2 z y"
        proof
          from VIs show "V - {j} \<subseteq> Is" by blast
        next
          fix P'
          assume profileP': "profile A Is P'"
            and V2yz': "\<And>i. i \<in> ?V2 \<Longrightarrow> z \<^bsub>(P' i)\<^esub>\<prec> y"
            and nV2yz': "\<And>i. i \<in> Is - ?V2 \<Longrightarrow> y \<^bsub>(P' i)\<^esub>\<prec> z"
          from iia have "\<And>a b. \<lbrakk> a \<in> {y, z}; b \<in> {y, z} \<rbrakk> \<Longrightarrow> (a \<^bsub>(swf P)\<^esub>\<preceq> b) = (a \<^bsub>(swf P')\<^esub>\<preceq> b)"
          proof(rule iiaE)
            from threeDist show yzA: "{y,z} \<subseteq> A" by simp
          next
            fix i assume iIs: "i \<in> Is"
            fix a b assume ab: "a \<in> {y, z}" "b \<in> {y, z}"
            with VIs profileP V2xyzP
            have V2yzP: "\<forall>i \<in> ?V2. z \<^bsub>(P i)\<^esub>\<prec> y" by (blast dest: rpr_less_trans)
            show "(a \<^bsub>(P' i)\<^esub>\<preceq> b) = (a \<^bsub>(P i)\<^esub>\<preceq> b)"
            proof(cases "i \<in> ?V2")
              case True
              with VIs profileP profileP' ab V2yz' V2yzP threeDist
              show ?thesis unfolding strict_pref_def profile_def by auto
            next
              case False
              from V1xyzP V3xyzP
              have "\<forall>i \<in> Is - ?V2. y \<^bsub>(P i)\<^esub>\<prec> z" by auto
              with iIs False VIs jV profileP profileP' ab nV2yz' threeDist
              show ?thesis unfolding profile_def strict_pref_def by auto
            qed
          qed (simp_all add: profileP profileP')
          with zPy show "z \<^bsub>(swf P')\<^esub>\<prec> y" unfolding strict_pref_def by blast
        qed
        with VIs Vsd Vmin[where V'="?V2"] V2card V2notempty threeDist show False
          by auto
      qed (simp add: profileP threeDist)
    qed
    have "semidecisive swf A Is ?V1 x z"
    proof
      from jV VIs show "{j} \<subseteq> Is" by blast
    next
      \<comment> \<open>Use @{term "iia"} to show the SWF must allow the individual to prevail.\<close>
      fix P'
      assume profileP': "profile A Is P'"
         and V1yz': "\<And>i. i \<in> ?V1 \<Longrightarrow> x \<^bsub>(P' i)\<^esub>\<prec> z"
         and nV1yz': "\<And>i. i \<in> Is - ?V1 \<Longrightarrow> z \<^bsub>(P' i)\<^esub>\<prec> x"
      from iia have "\<And>a b. \<lbrakk> a \<in> {x, z}; b \<in> {x, z} \<rbrakk> \<Longrightarrow> (a \<^bsub>(swf P)\<^esub>\<preceq> b) = (a \<^bsub>(swf P')\<^esub>\<preceq> b)"
      proof(rule iiaE)
        from threeDist show xzA: "{x,z} \<subseteq> A" by simp
      next
        fix i assume iIs: "i \<in> Is"
        fix a b assume ab: "a \<in> {x, z}" "b \<in> {x, z}"
        show "(a \<^bsub>(P' i)\<^esub>\<preceq> b) = (a \<^bsub>(P i)\<^esub>\<preceq> b)"
        proof(cases "i \<in> ?V1")
          case True
          with jV VIs profileP V1xyzP
          have "\<forall>i \<in> ?V1. x \<^bsub>(P i)\<^esub>\<prec> z" by (blast dest: rpr_less_trans)
          with True jV VIs profileP profileP' ab V1yz' threeDist
          show ?thesis unfolding strict_pref_def profile_def by auto
        next
          case False
          from V2xyzP V3xyzP
          have "\<forall>i \<in> Is - ?V1. z \<^bsub>(P i)\<^esub>\<prec> x" by auto
          with iIs False VIs jV profileP profileP' ab nV1yz' threeDist
          show ?thesis unfolding strict_pref_def profile_def by auto
        qed
      qed (simp_all add: profileP profileP')
      with xPz show "x \<^bsub>(swf P')\<^esub>\<prec> z" unfolding strict_pref_def by blast
    qed
    with jV VIs Vsd Vmin[where V'="?V1"] V2card threeDist show False
      by auto
  qed
  with xyA Vsd show ?thesis by blast
qed

(* **************************************** *)

subsection\<open>Arrow's General Possibility Theorem\<close>

text\<open>

Finally we conclude with the celebrated ``possibility'' result. Note that we
assume the set of individuals is finite; \cite{Routley:79} relaxes this with
some fancier set theory. Having an infinite set of alternatives doesn't
matter, though the result is a bit more plausible if we assume finiteness
\cite[p54]{Sen:70a}.

\<close>

theorem ArrowGeneralPossibility:
  assumes has3A: "has 3 A"
      and finiteIs: "finite Is"
      and has2Is: "has 2 Is"
      and iia: "iia swf A Is"
      and swf: "SWF swf A Is universal_domain"
      and wp: "weak_pareto swf A Is universal_domain"
  obtains j where "dictator swf A Is j"
  using sd_imp_dictator[OF has3A iia swf wp]
        sd_exists[OF has3A finiteIs has2Is iia swf wp]
  by blast

(*<*)
end
(*>*)
