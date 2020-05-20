section \<open>Shallow embedding of HyperCTL*\<close>

(*<*)
theory Shallow
imports Prelim
begin
(*>*)

text\<open>We define a notion of ``shallow'' HyperCTL* formula (sfmla) that captures
HyperCTL* binders as meta-level HOL binders. We also define a proof system for this
shallow embedding.\<close>


subsection\<open>Kripke structures and paths\<close>

type_synonym ('state,'aprop) path = "('state \<times> 'aprop set) stream"

abbreviation stateOf where "stateOf \<pi> \<equiv> fst (shd \<pi>)"
abbreviation apropsOf where "apropsOf \<pi> \<equiv> snd (shd \<pi>)"

locale Kripke =
  fixes S :: "'state set" and s0 :: 'state and \<delta> :: "'state \<Rightarrow> 'state set"
  and AP :: "'aprop set" and L :: "'state \<Rightarrow> 'aprop set"
  assumes s0: "s0 \<in> S" and \<delta>: "\<And> s. s \<in> S \<Longrightarrow> \<delta> s \<subseteq> S"
  and L : "\<And> s. s \<in> S \<Longrightarrow> L s \<subseteq> AP"
begin

text\<open>Well-formed paths\<close>

coinductive wfp :: "'aprop set \<Rightarrow> ('state,'aprop) path \<Rightarrow> bool"
for AP' :: "'aprop set"
where
intro:
"\<lbrakk>s \<in> S; A \<subseteq> AP'; A \<inter> AP = L s; stateOf \<pi> \<in> \<delta> s; wfp AP' \<pi>\<rbrakk>
 \<Longrightarrow>
 wfp AP' ((s,A) ## \<pi>)"

lemma wfp:
"wfp AP' \<pi> \<longleftrightarrow>
 (\<forall> i. fst (\<pi> !! i) \<in> S \<and> snd (\<pi> !! i) \<subseteq> AP' \<and>
       snd (\<pi> !! i) \<inter> AP = L (fst (\<pi> !! i)) \<and>
       fst (\<pi> !! (Suc i)) \<in> \<delta> (fst (\<pi> !! i))
 )"
(is "?L \<longleftrightarrow> (\<forall> i. ?R i)")
proof (intro iffI allI)
  fix i assume ?L thus "?R i"
  apply(induction i arbitrary: \<pi>)
  by (metis snth.simps fst_conv snd_conv stream.sel wfp.cases)+
next
  assume R: "\<forall> i. ?R i"  thus ?L
  apply (coinduct)
  using s0 fst_conv snd_conv snth.simps stream.sel 
  by (metis inf_commute stream.collapse surj_pair)
qed

lemma wfp_sdrop[simp]:
"wfp AP' \<pi> \<Longrightarrow> wfp AP' (sdrop i \<pi>)"
unfolding wfp by simp (metis sdrop_add sdrop_simps(1))

(*<*)
end (* context Kripke *)
(*>*)

text\<open>end-of-context Kripke\<close>


subsection\<open>Shallow representations of formulas\<close>

text\<open>A shallow (representation of a) HyperCTL* formula will be a predicate on lists of paths.  
The atomic formulas (operator $\textit{atom}$) are parameterized by atomic propositions (as customary in temporal logic), 
and additionally by a number indicating the position, in the list of paths, of the path to which the atomic proposition 
refers -- for example, $\textit{atom}\;a\;i$ holds for the list of paths $\pi l$ just in case proposition $a$ holds 
at the first state of $\pi l!i$, the $i$'th path in $\pi l$.  The temporal operators $\textit{next}$ and $\textit{until}$ act on all the paths of the argument 
list $\pi l$ synchronously.  Finally, the existential quantifier refers to the existence of a path whose origin state is that of 
the last path in $\pi l$.  

As an example: $\textit{exi}\; (\textit{exi}\; (\textit{until}\; (\textit{atom}\;a\;0)\;(\textit{atom}\;b\;1)))$ holds for the empty list 
iff there exist two paths $\rho_0$ and $\rho_1$ such that, synchronously,  
$a$ holds on $\rho_0$ until $b$ holds on $\rho_1$.  Another example will be the formula encoding Goguen-Meseguer noninterference.   
\<close>

text\<open>Shallow HyperCTL* formulas:\<close>

type_synonym ('state,'aprop) sfmla = "('state,'aprop) path list \<Rightarrow> bool"


locale Shallow = Kripke S "s0" \<delta> AP L
  for S :: "'state set" and s0 :: 'state and \<delta> :: "'state \<Rightarrow> 'state set"
  and AP :: "'aprop set" and L :: "'state \<Rightarrow> 'aprop set"
+
  fixes AP' assumes AP_AP': "AP \<subseteq> AP'"
begin

text\<open>Primitive operators\<close>

(* I include false as a primitive since otherwise I would have to assume nonemptyness of
  the atomic propositions *)
definition fls :: "('state,'aprop) sfmla" where
"fls \<pi>l \<equiv> False"

definition atom :: "'aprop \<Rightarrow> nat \<Rightarrow> ('state,'aprop) sfmla" where
"atom a i \<pi>l \<equiv> a \<in> apropsOf (\<pi>l!i)"

definition neg :: "('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla" where
"neg \<phi> \<pi>l \<equiv> \<not> \<phi> \<pi>l"

definition dis :: "('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla" where
"dis \<phi> \<psi> \<pi>l \<equiv> \<phi> \<pi>l \<or> \<psi> \<pi>l"

definition "next" :: "('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla" where
"next \<phi> \<pi>l \<equiv> \<phi> (map stl \<pi>l)"

definition until :: "('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla" where
"until \<phi> \<psi> \<pi>l \<equiv>
 \<exists> i. \<psi> (map (sdrop i) \<pi>l) \<and> (\<forall> j \<in>{0..<i}. \<phi> (map (sdrop j) \<pi>l))"

definition exii :: "('state,'aprop) sfmla \<Rightarrow> ('state,'aprop) sfmla" where
"exii \<phi> \<pi>l \<equiv>
 \<exists> \<pi>. wfp AP' \<pi> \<and> stateOf \<pi> = (if \<pi>l \<noteq> [] then stateOf (last \<pi>l) else s0)
      \<and> \<phi> (\<pi>l @ [\<pi>])"

definition exi :: "(('state,'aprop) path \<Rightarrow> ('state,'aprop) sfmla) \<Rightarrow> ('state,'aprop) sfmla" where
"exi F \<pi>l \<equiv>
 \<exists> \<pi>. wfp AP' \<pi> \<and> stateOf \<pi> = (if \<pi>l \<noteq> [] then stateOf (last \<pi>l) else s0)
      \<and> F \<pi> \<pi>l"

text\<open>Derived operators\<close>

definition "tr \<equiv> neg fls"
definition "con \<phi> \<psi> \<equiv> neg (dis (neg \<phi>) (neg \<psi>))"
definition "imp \<phi> \<psi> \<equiv> dis (neg \<phi>) \<psi>"
definition "eq \<phi> \<psi> \<equiv> con (imp \<phi> \<psi>) (imp \<psi> \<phi>) "
definition "fall F \<equiv> neg (exi (\<lambda> \<pi>. neg (F \<pi>)))"
definition "ev \<phi> \<equiv> until tr \<phi>"
definition "alw \<phi> \<equiv> neg (ev (neg \<phi>))"
definition "wuntil \<phi> \<psi> \<equiv> dis (until \<phi> \<psi>) (alw \<phi>)"

lemmas main_op_defs =
fls_def atom_def neg_def dis_def next_def until_def exi_def

lemmas der_op_defs =
tr_def con_def imp_def eq_def ev_def alw_def wuntil_def fall_def

lemmas op_defs = main_op_defs der_op_defs


subsection\<open>Reasoning rules\<close>

text\<open>We provide introduction, elimination, unfolding and (co)induction rules
for the connectives and quantifiers.\<close>

text\<open>Boolean operators\<close>

lemma fls_elim[elim!]:
assumes "fls \<pi>l" shows \<phi>
using assms unfolding op_defs by auto

lemma tr_intro[intro!, simp]: "tr \<pi>l"
unfolding op_defs by auto

lemma dis_introL[intro]:
assumes "\<phi> \<pi>l" shows "dis \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma dis_introR[intro]:
assumes "\<psi> \<pi>l" shows "dis \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma dis_elim[elim]:
assumes "dis \<phi> \<psi> \<pi>l" and "\<phi> \<pi>l \<Longrightarrow> \<chi>" and "\<psi> \<pi>l \<Longrightarrow> \<chi>"
shows \<chi>
using assms unfolding op_defs by auto

lemma con_intro[intro!]:
assumes "\<phi> \<pi>l" and "\<psi> \<pi>l" shows "con \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma con_elim[elim]:
assumes "con \<phi> \<psi> \<pi>l" and "\<phi> \<pi>l \<Longrightarrow> \<psi> \<pi>l \<Longrightarrow> \<chi>" shows \<chi>
using assms unfolding op_defs by auto

lemma neg_intro[intro!]:
assumes "\<phi> \<pi>l \<Longrightarrow> False"  shows "neg \<phi> \<pi>l"
using assms unfolding op_defs by auto

lemma neg_elim[elim]:
assumes "neg \<phi> \<pi>l" and "\<phi> \<pi>l"  shows \<chi>
using assms unfolding op_defs by auto

lemma imp_intro[intro!]:
assumes "\<phi> \<pi>l \<Longrightarrow> \<psi> \<pi>l"  shows "imp \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma imp_elim[elim]:
assumes "imp \<phi> \<psi> \<pi>l" and "\<phi> \<pi>l" and "\<psi> \<pi>l \<Longrightarrow> \<chi>" shows \<chi>
using assms unfolding op_defs by auto

lemma imp_mp[elim]:
assumes "imp \<phi> \<psi> \<pi>l" and "\<phi> \<pi>l" shows "\<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma eq_intro[intro!]:
assumes "\<phi> \<pi>l \<Longrightarrow> \<psi> \<pi>l" and "\<psi> \<pi>l \<Longrightarrow> \<phi> \<pi>l" shows "eq \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by auto

lemma eq_elimL[elim]:
assumes "eq \<phi> \<psi> \<pi>l" and "\<phi> \<pi>l" and "\<psi> \<pi>l \<Longrightarrow> \<chi>" shows \<chi>
using assms unfolding op_defs by auto

lemma eq_elimR[elim]:
assumes "eq \<phi> \<psi> \<pi>l" and "\<psi> \<pi>l" and "\<phi> \<pi>l \<Longrightarrow> \<chi>" shows \<chi>
using assms unfolding op_defs by auto

lemma eq_equals: "eq \<phi> \<psi> \<pi>l \<longleftrightarrow> \<phi> \<pi>l = \<psi> \<pi>l"
by (metis eq_elimL eq_elimR eq_intro)


text\<open>Quantifiers\<close>

lemma exi_intro[intro]:
assumes "wfp AP' \<pi>"
and "\<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l)"
and "\<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0"
and "F \<pi> \<pi>l"
shows "exi F \<pi>l"
using assms unfolding exi_def by auto

lemma exi_elim[elim]:
assumes "exi F \<pi>l"
and
"\<And> \<pi>. \<lbrakk>wfp AP' \<pi>; \<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l); \<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0; F \<pi> \<pi>l\<rbrakk> \<Longrightarrow> \<chi>"
shows \<chi>
using assms unfolding exi_def by auto

lemma fall_intro[intro]:
assumes
"\<And> \<pi>. \<lbrakk>wfp AP' \<pi>; \<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l) ; \<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0\<rbrakk>
       \<Longrightarrow>  F \<pi> \<pi>l"
shows "fall F \<pi>l"
using assms unfolding fall_def by (metis exi_def neg_def)

lemma fall_elim[elim]:
assumes "fall F \<pi>l"
and
"(\<And>\<pi>. \<lbrakk>wfp AP' \<pi>; \<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l); \<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0\<rbrakk>
        \<Longrightarrow> F \<pi> \<pi>l)
  \<Longrightarrow> \<chi>"
shows \<chi>
using assms unfolding fall_def
by (metis exi_def neg_elim neg_intro)


text\<open>Temporal connectives\<close>

lemma next_intro[intro]:
assumes "\<phi> (map stl \<pi>l)"  shows "next \<phi> \<pi>l"
using assms unfolding op_defs by auto

lemma next_elim[elim]:
assumes "next \<phi> \<pi>l" and "\<phi> (map stl \<pi>l) \<Longrightarrow> \<chi>"  shows \<chi>
using assms unfolding op_defs by auto

lemma until_introR[intro]:
assumes "\<psi> \<pi>l" shows "until \<phi> \<psi> \<pi>l"
using assms unfolding op_defs by (auto intro: exI[of _ 0])

lemma until_introL[intro]:
assumes \<phi>: "\<phi> \<pi>l" and u: "until \<phi> \<psi> (map stl \<pi>l)"
shows "until \<phi> \<psi> \<pi>l"
proof-
  obtain i where \<psi>: "\<psi> (map (sdrop (Suc i)) \<pi>l)" and 1: "\<forall>j\<in>{0..<i}. \<phi> (map (sdrop (Suc j)) \<pi>l)"
  using u unfolding op_defs by auto
  {fix j assume "j \<in> {0..<Suc i}"
   hence "\<phi> (map (sdrop j) \<pi>l)" using 1 \<phi> by (cases j) auto
  }
  thus ?thesis using \<psi> unfolding op_defs by auto
qed

text\<open>The elimination rules for until and eventually are induction rules.\<close>

lemma until_induct[induct pred: until, consumes 1, case_names Base Step]:
assumes u: "until \<phi> \<psi> \<pi>l"
and b: "\<And> \<pi>l. \<psi> \<pi>l \<Longrightarrow> \<chi> \<pi>l"
and i: "\<And> \<pi>l. \<lbrakk>\<phi> \<pi>l; until \<phi> \<psi> (map stl \<pi>l); \<chi> (map stl \<pi>l)\<rbrakk> \<Longrightarrow> \<chi> \<pi>l"
shows "\<chi> \<pi>l"
proof-
  obtain i where \<psi>: "\<psi> (map (sdrop i) \<pi>l)" and 1:  "\<forall>j\<in>{0..<i}. \<phi> (map (sdrop j) \<pi>l)"
  using u unfolding until_def next_def by auto
  {fix k assume k: "k \<le> i"
   hence "until \<phi> \<psi> (map (sdrop k) \<pi>l) \<and> \<chi> (map (sdrop k) \<pi>l)"
   proof (induction "i-k" arbitrary: k)
     case 0 hence "k=i" by auto
     with b[OF \<psi>] u \<psi> show ?case by (auto intro: until_introR)
   next
     case (Suc ii)  let ?\<pi>l' = "map (sdrop k) \<pi>l"
     have "until \<phi> \<psi>  (map stl ?\<pi>l') \<and> \<chi> (map stl ?\<pi>l')" using Suc by auto
     moreover have "\<phi> ?\<pi>l'" using 1 Suc by auto
     ultimately show ?case using i by auto
   qed
  }
  from this[of 0] show ?thesis by simp
qed

lemma until_unfold:
"until \<phi> \<psi> \<pi>l = (\<psi> \<pi>l \<or> \<phi> \<pi>l \<and> until \<phi> \<psi> (map stl \<pi>l))" (is "?L = ?R")
proof
  assume ?L thus ?R by induct auto
qed auto

lemma ev_introR[intro]:
assumes "\<phi> \<pi>l" shows "ev \<phi> \<pi>l"
using assms unfolding ev_def by (auto intro: until_introR)

lemma ev_introL[intro]:
assumes "ev \<phi> (map stl \<pi>l)"  shows "ev \<phi> \<pi>l"
using assms unfolding ev_def by (auto intro: until_introL)

lemma ev_induct[induct pred: ev, consumes 1, case_names Base Step]:
assumes "ev \<phi> \<pi>l" and "\<And> \<pi>l. \<phi> \<pi>l \<Longrightarrow> \<chi> \<pi>l"
and "\<And> \<pi>l. \<lbrakk>ev \<phi> (map stl \<pi>l); \<chi> (map stl \<pi>l)\<rbrakk> \<Longrightarrow> \<chi> \<pi>l"
shows "\<chi> \<pi>l"
using assms unfolding ev_def by induct (auto simp: assms)

lemma ev_unfold:
"ev \<phi> \<pi>l = (\<phi> \<pi>l \<or> ev \<phi> (map stl \<pi>l))"
unfolding ev_def by (metis tr_intro until_unfold)

lemma ev: "ev \<phi> \<pi>l \<longleftrightarrow> (\<exists> i. \<phi> (map (sdrop i) \<pi>l))"
unfolding ev_def until_def by auto


text\<open>The introduction rules for always and weak until are coinduction rules.\<close>

lemma alw_coinduct[coinduct pred: alw, consumes 1, case_names Hyp]:
assumes "\<chi> \<pi>l"
and "\<And> \<pi>l. \<chi> \<pi>l \<Longrightarrow> alw \<phi> \<pi>l \<or> (\<phi> \<pi>l \<and> \<chi> (map stl \<pi>l))"
shows "alw \<phi> \<pi>l"
proof-
  {assume "ev (neg \<phi>) \<pi>l"
   hence "\<not> \<chi> \<pi>l"
   apply induct
   using assms unfolding op_defs by auto (metis assms alw_def ev_def neg_def until_introR)
  }
  thus ?thesis using assms unfolding op_defs by auto
qed

lemma alw_elim[elim]:
assumes "alw \<phi> \<pi>l"
and "\<lbrakk>\<phi> \<pi>l; alw \<phi> (map stl \<pi>l)\<rbrakk> \<Longrightarrow> \<chi>"
shows "\<chi>"
using assms unfolding alw_def by(auto elim: ev_introR simp: neg_def)

lemma alw_destL: "alw \<phi> \<pi>l \<Longrightarrow> \<phi> \<pi>l" by auto
lemma alw_destR: "alw \<phi> \<pi>l \<Longrightarrow> alw \<phi> (map stl \<pi>l)" by auto

lemma alw_unfold:
"alw \<phi> \<pi>l = (\<phi> \<pi>l \<and> alw \<phi> (map stl \<pi>l))"
by (metis alw_def ev_unfold neg_elim neg_intro)

lemma alw: "alw \<phi> \<pi>l \<longleftrightarrow> (\<forall> i. \<phi> (map (sdrop i) \<pi>l))"
unfolding alw_def ev neg_def by simp

lemma sdrop_imp_alw:
assumes "\<And> i. (\<And>j. j \<le> i \<Longrightarrow> \<phi> [sdrop j \<pi>, sdrop j \<pi>']) \<Longrightarrow> \<psi> [sdrop i \<pi>, sdrop i \<pi>']"
shows "imp (alw \<phi>) (alw \<psi>) [\<pi>, \<pi>']"
using assms by(auto simp: alw)

lemma wuntil_coinduct[coinduct pred: wuntil, consumes 1, case_names Hyp]:
assumes \<chi>: "\<chi> \<pi>l"
and 0: "\<And> \<pi>l. \<chi> \<pi>l \<Longrightarrow> \<psi> \<pi>l \<or> (\<phi> \<pi>l \<and> \<chi> (map stl \<pi>l))"
shows "wuntil \<phi> \<psi> \<pi>l"
proof-
  {assume "\<not> until \<phi> \<psi> \<pi>l \<and> \<chi> \<pi>l"
   hence "alw \<phi> \<pi>l"
   apply coinduct using 0 by (auto intro: until_introL until_introR)
  }
  thus ?thesis using \<chi> unfolding wuntil_def dis_def by auto
qed

lemma wuntil_elim[elim]:
assumes w: "wuntil \<phi> \<psi> \<pi>l"
and 1: "\<psi> \<pi>l \<Longrightarrow> \<chi>"
and 2: "\<lbrakk>\<phi> \<pi>l; wuntil \<phi> \<psi> (map stl \<pi>l)\<rbrakk> \<Longrightarrow> \<chi>"
shows \<chi>
proof(cases "alw \<phi> \<pi>l")
  case True
  thus ?thesis apply standard using 2 unfolding wuntil_def by auto
next
  case False
  hence "until \<phi> \<psi> \<pi>l" using w unfolding wuntil_def dis_def by auto
  thus ?thesis by (metis assms dis_introL until_unfold wuntil_def)
qed

lemma wuntil_unfold:
"wuntil \<phi> \<psi> \<pi>l = (\<psi> \<pi>l \<or> \<phi> \<pi>l \<and> wuntil \<phi> \<psi> (map stl \<pi>l))"
by (metis alw_unfold dis_def until_unfold wuntil_def)


subsection\<open>More derived operators\<close>

text\<open>The conjunction of an arbitrary set of formulas:\<close>

definition scon ::
"('state,'aprop) sfmla set \<Rightarrow> ('state,'aprop) sfmla" where
"scon \<phi>s \<pi>l \<equiv> \<forall> \<phi> \<in> \<phi>s. \<phi> \<pi>l"

lemma mcon_intro[intro!]:
assumes "\<And> \<phi>. \<phi> \<in> \<phi>s \<Longrightarrow> \<phi> \<pi>l" shows "scon \<phi>s \<pi>l"
using assms unfolding scon_def by auto

lemma scon_elim[elim]:
assumes "scon \<phi>s \<pi>l" and "(\<And> \<phi>. \<phi> \<in> \<phi>s \<Longrightarrow> \<phi> \<pi>l) \<Longrightarrow> \<chi>"
shows \<chi>
using assms unfolding scon_def by auto

text\<open>Double-binding forall:\<close>

definition "fall2 F \<equiv> fall (\<lambda> \<pi>. fall (F \<pi>))"

lemma fall2_intro[intro]:
assumes
"\<And> \<pi> \<pi>'. \<lbrakk>wfp AP' \<pi>; wfp AP' \<pi>';
           \<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l);
           \<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0;
           stateOf \<pi>' = stateOf \<pi>
          \<rbrakk>
       \<Longrightarrow>  F \<pi> \<pi>' \<pi>l"
shows "fall2 F \<pi>l"
using assms unfolding fall2_def by (auto intro!: fall_intro)

lemma fall2_elim[elim]:
assumes "fall2 F \<pi>l"
and
"(\<And>\<pi> \<pi>'. \<lbrakk>wfp AP' \<pi>; wfp AP' \<pi>';
           \<pi>l \<noteq> [] \<Longrightarrow> stateOf \<pi> = stateOf (last \<pi>l); \<pi>l = [] \<Longrightarrow> stateOf \<pi> = s0;
           stateOf \<pi>' = stateOf \<pi>
          \<rbrakk>
          \<Longrightarrow> F \<pi> \<pi>' \<pi>l)
  \<Longrightarrow> \<chi>"
shows \<chi>
using assms unfolding fall2_def by (auto elim!: fall_elim) (metis fall_elim)

(*<*)
end (* context Shallow *)
(*>*)

text\<open>end-of-context Shallow\<close>


(*<*)
end
(*>*)
