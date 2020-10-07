section \<open>Noninterference \`{a} la Goguen and Meseguer\<close>

(*<*)
theory Noninterference
imports Shallow
begin
(*>*)

subsection\<open>Goguen-Meseguer noninterference\<close>

text\<open>Definition\<close>

locale GM_sec_model =
  fixes st0 :: 'St
  and do :: "'St \<Rightarrow> 'U \<Rightarrow> 'C \<Rightarrow> 'St"
  and out :: "'St \<Rightarrow> 'U \<Rightarrow> 'Out"
  and GH :: "'U set"
  and GL :: "'U set"
begin

text\<open>Extension of ``do'' to sequences of pairs (user, command):\<close>

fun doo :: "'St \<Rightarrow> ('U \<times> 'C) list \<Rightarrow> 'St" where
 "doo st [] = st"
|"doo st ((u,c) # ucl) = (doo (do st u c ) ucl)"

definition purge :: "'U set \<Rightarrow> ('U \<times> 'C) list \<Rightarrow> ('U \<times> 'C) list" where
"purge G ucl \<equiv> filter (\<lambda> (u,c). u \<notin> G) ucl"

lemma purge_Nil[simp]: "purge G [] = []"
and purge_Cons_in[simp]: "u \<notin> G \<Longrightarrow> purge G ((u,c) # ucl) = (u,c) # purge G ucl"
and purge_Cons_notIn[simp]: "u \<in> G \<Longrightarrow> purge G ((u,c) # ucl) = purge G ucl"
unfolding purge_def by auto

lemma purge_append:
"purge G (ucl1 @ ucl2) = purge G ucl1 @ purge G ucl2"
unfolding purge_def by (metis filter_append)

definition nonint :: bool where
"nonint \<equiv> \<forall> ucl. \<forall> u \<in> GL. out (doo st0 ucl) u = out (doo st0 (purge GH ucl)) u"


(*<*)
end (* context GM_sec_model *)
(*>*)

text\<open>end-of-context GM-sec-model\<close>


subsection\<open>Specialized Kripke structures\<close>

text\<open>As a preparation for representing noninterference in HyperCTL*,
we define a specialized notion of Kripke structure.  It is enriched
with the following date: 
two binary state predicates f and g, intuitively capturing high-input
and low-output equivalence, respectively; 
a set Sink of
states immediately accessible from any state and such that, for the states in Sink,
there exist self-transitions and f holds.

This specialized structure, represented by the locale Shallow-Idle, is an auxiliary that streamlines our proofs, 
easing the connection
between finite paths (specific to Goguen-Meseguer noninterference) and
infinite paths (specific to the HyperCTL* semantics).
The desired Kripke structure produced from a Goguen-Meseguer model 
will actually be such a specialized structure.
\<close>

locale Shallow_Idle = Shallow S "s0" \<delta> AP
  for S :: "'state set" and s0 :: 'state and \<delta> :: "'state \<Rightarrow> 'state set"
  and AP :: "'aprop set"
  and f :: "'state \<Rightarrow> 'state \<Rightarrow> bool" and g :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
  and Sink :: "'state set"
  +
  assumes Sink_S: "Sink \<subseteq> S"
  and Sink: "\<And> s. s \<in> S \<Longrightarrow> \<exists> s'. s' \<in> \<delta> s \<inter> Sink"
  and Sink_idle: "\<And> s. s \<in> Sink \<Longrightarrow> s \<in> \<delta> s"
  and Sink_f: "\<And> s1 s2. {s1,s2} \<subseteq> Sink \<Longrightarrow> f s1 s2"
begin

definition "toSink s \<equiv> SOME s'. s' \<in> \<delta> s \<inter> Sink"

lemma toSink: "s \<in> S \<Longrightarrow> toSink s \<in> \<delta> s \<inter> Sink"
unfolding toSink_def by (metis Sink someI)

lemma fall2_imp_alw:
"fall2 (\<lambda> \<pi>' \<pi> \<pi>l. imp (alw (\<phi> \<pi>l)) (alw (\<psi> \<pi>l)) (\<pi>l @ [\<pi>,\<pi>'])) []
 \<longleftrightarrow>
 (\<forall> \<pi> \<pi>'. wfp AP' \<pi> \<and> wfp AP' \<pi>' \<and> stateOf \<pi> = s0 \<and> stateOf \<pi>' = s0
           \<longrightarrow> imp (alw (\<phi> [])) (alw (\<psi> [])) [\<pi>,\<pi>']
 )"
by (auto intro!: fall2_intro imp_intro elim!: fall2_elim imp_elim) (metis imp_elim)+


lemma wfp_stateOf_shift_stake_sconst:
fixes \<pi> i
defines "\<pi>1 \<equiv> shift (stake (Suc i) \<pi>) (sconst (toSink (fst (\<pi> !! i)), L (toSink (fst (\<pi> !! i)))))"
assumes \<pi>: "wfp AP' \<pi>"
shows "wfp AP' \<pi>1 \<and> stateOf \<pi>1 = stateOf \<pi>"
proof
  have \<pi>1_less[simp]: "\<And> k. k < Suc i \<Longrightarrow> \<pi>1 !! k = \<pi> !! k"
   and \<pi>1_geq[simp]: "\<And> k. k > i \<Longrightarrow> \<pi>1 !! k = (toSink (fst (\<pi> !! i)) , L (toSink (fst (\<pi> !! i))))"
  unfolding \<pi>1_def by (auto simp del: stake.simps)
  {fix k have "fst (\<pi>1 !! Suc k) \<in> \<delta> (fst (\<pi>1 !! k))"
   proof(cases "k < Suc i")
     case True
     hence 0: "\<pi>1 !! k = \<pi> !! k" by simp
     show ?thesis
     proof(cases "k < i")
       case True hence 1: "Suc k < Suc i" by simp
       show ?thesis using \<pi> unfolding \<pi>1_less[OF 1] 0 wfp by auto
     next
       case False hence 1: "Suc k > i" and k: "k = i" using True by simp_all
       show ?thesis using \<pi> unfolding \<pi>1_geq[OF 1] 0 wfp unfolding k by (metis IntD1 fstI toSink)
     qed
   next
     case False
     hence k: "k > i" and sk: "Suc k > i" by auto
     show ?thesis unfolding \<pi>1_geq[OF k] \<pi>1_geq[OF sk] using \<pi> wfp Sink_idle toSink by auto
   qed
  }
  moreover
  {fix k have "fst (\<pi>1 !! k) \<in> S \<and> snd (\<pi>1 !! k) \<subseteq> AP' \<and> snd (\<pi>1 !! k) \<inter> AP = L (fst (\<pi>1 !! k))"
   apply(cases "k < Suc i",simp_all)
   by (metis (lifting, no_types) \<pi> wfp AP_AP' IntD1 L \<delta> inf.orderE order_trans rev_subsetD toSink)+
  }
  ultimately show "wfp AP' \<pi>1" unfolding wfp by auto
  show "stateOf \<pi>1 = stateOf \<pi>"
  by (metis \<pi>1_def shift.simps(2) stake.simps(2) stream.sel(1))
qed

lemma fall2_imp_alw_index:
assumes 0: "\<And> \<pi> \<pi>'. wfp AP' \<pi> \<and> wfp AP' \<pi>' \<longrightarrow>
                     \<phi> [] [\<pi>,\<pi>'] = f (stateOf \<pi>) (stateOf \<pi>') \<and>
                     \<psi> [] [\<pi>,\<pi>'] = g (stateOf \<pi>) (stateOf \<pi>')"
shows
"fall2 (\<lambda> \<pi>' \<pi> \<pi>l. imp (alw (\<phi> \<pi>l)) (alw (\<psi> \<pi>l)) (\<pi>l @ [\<pi>,\<pi>'])) []
 \<longleftrightarrow>
 (\<forall> \<pi> \<pi>'. wfp AP' \<pi> \<and> wfp AP' \<pi>' \<and> stateOf \<pi> = s0 \<and> stateOf \<pi>' = s0
           \<longrightarrow>
           (\<forall> i. (\<forall> j \<le> i. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))) \<longrightarrow> g (fst (\<pi> !! i)) (fst (\<pi>' !! i)))
 )"
(is "?L \<longleftrightarrow> ?R")
proof-
  have 1: "\<And> i \<pi> \<pi>'. wfp AP' \<pi> \<and> wfp AP' \<pi>' \<longrightarrow>
                      f (fst (\<pi> !! i)) (fst (\<pi>' !! i)) = \<phi> [] [sdrop i \<pi>, sdrop i \<pi>'] \<and>
                      g (fst (\<pi> !! i)) (fst (\<pi>' !! i)) = \<psi> [] [sdrop i \<pi>, sdrop i \<pi>']"
  using 0 by auto
  show ?thesis unfolding fall2_imp_alw proof(intro iffI allI impI, elim conjE)
    fix \<pi> \<pi>' i
    assume L: "\<forall> \<pi> \<pi>'. wfp AP' \<pi> \<and> wfp AP' \<pi>' \<and> stateOf \<pi> = s0 \<and> stateOf \<pi>' = s0
                       \<longrightarrow> imp (alw (\<phi> [])) (alw (\<psi> [])) [\<pi>,\<pi>']"
    and \<pi>\<pi>'[simp]: "wfp AP' \<pi>" "wfp AP' \<pi>'" "stateOf \<pi> = s0" "stateOf \<pi>' = s0"
    and \<phi>: "\<forall>j\<le>i. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))"
    have \<pi>\<pi>'i[simp]: "\<And> i. wfp AP' (sdrop i \<pi>) \<and> wfp AP' (sdrop i \<pi>')" by (metis \<pi>\<pi>' wfp_sdrop)
    define \<pi>1 where "\<pi>1 = shift (stake (Suc i) \<pi>) (sconst (toSink (fst (\<pi> !! i)), L (toSink (fst (\<pi> !! i)))))"
    define \<pi>1' where "\<pi>1' = shift (stake (Suc i) \<pi>') (sconst (toSink (fst (\<pi>' !! i)), L (toSink (fst (\<pi>' !! i)))))"
    have \<pi>1\<pi>1': "wfp AP' \<pi>1 \<and> stateOf \<pi>1 = s0 \<and> wfp AP' \<pi>1' \<and> stateOf \<pi>1' = s0"
    using wfp_stateOf_shift_stake_sconst unfolding \<pi>1_def \<pi>1'_def by auto
    hence \<pi>1\<pi>1'i: "\<And> i. wfp AP' (sdrop i \<pi>1) \<and> wfp AP' (sdrop i \<pi>1')" by (metis \<pi>\<pi>' wfp_sdrop)
    have imp: "imp (alw (\<phi> [])) (alw (\<psi> [])) [\<pi>1,\<pi>1']" using L  \<pi>1\<pi>1' by auto
    moreover have "alw (\<phi> []) [\<pi>1,\<pi>1']" unfolding alw proof
      fix k
      have a: "fst (\<pi> !! i) \<in> S" and b: "fst (\<pi>' !! i) \<in> S" using \<pi>\<pi>' unfolding wfp by auto
      thus "\<phi> [] (map (sdrop k) [\<pi>1, \<pi>1'])"
      using \<phi> 0 \<pi>1\<pi>1'i unfolding \<pi>1_def \<pi>1'_def
      apply(cases "k < Suc i", simp_all del: stake.simps)
      using toSink[OF a] toSink[OF b] Sink_f by auto
    qed
    ultimately have "alw (\<psi> []) [\<pi>1,\<pi>1']" by auto
    hence "\<psi> [] [sdrop i \<pi>1, sdrop i \<pi>1']" unfolding alw by simp
    hence "g (fst (\<pi>1 !! i)) (fst (\<pi>1' !! i))" using 0 \<pi>1\<pi>1'i by simp
    thus "g (fst (\<pi> !! i)) (fst (\<pi>' !! i))"
    unfolding \<pi>1_def \<pi>1'_def by (auto simp del: stake.simps)
  qed(auto simp: sdrop_imp_alw 1)
qed



(*<*)
end (* context Shallow-Idle *)
(*>*)

text\<open>end-of-context Shallow-Idle\<close>


subsection\<open>Faithful representation as a HyperCTL* property\<close>

text\<open>Starting with a Goguen-Meseguer model, we will produce a specialized
Kripke structure and a shallow HyperCTL* formula.
Then we we will prove that the structure satisfies the formula iff the
Goguen-Meseguer model satisfies noninterference.\<close>

text\<open>
The Kripke structure has two kinds of states: ``idle'' states storing Goguen-Meseguer states,
and normal states storing Goguen-Meseguer states, users and commands: the former 
will be used for synchronization and the latter for Goguen-Meseguer steps.
The Kripke labels store user-command actions and user-output observations.

\<close>

datatype ('St,'U,'C) state =
  isIdle: Idle (getGMState: 'St) | isState: State (getGMState: 'St) (getGMUser: 'U) (getGMCom: 'C)

datatype ('U,'C,'Out) aprop = Last 'U 'C | Obs 'U 'Out

definition getGMUserCom where "getGMUserCom s = (getGMUser s, getGMCom s)"

lemma getGMUserCom[simp]: "getGMUserCom (State st u c) = (u,c)"
unfolding getGMUserCom_def by auto

context GM_sec_model
begin

primrec L :: "('St,'U,'C) state \<Rightarrow> ('U,'C,'Out) aprop set" where
 "L (Idle st) = {Obs u' (out st u') | u'. True}"
|"L (State st u c) = {Last u c} \<union> {Obs u' (out st u') | u'. True}"

text\<open>Get the Goguen-Meseguer state:\<close>

primrec getGMState where
 "getGMState (Idle st) = st"
|"getGMState (State st u c) = st"

lemma Last_in_L[simp]: "Last u c \<in> L s \<longleftrightarrow> (\<exists> st. s = State st u c)"
by (cases s) auto

lemma Obs_in_L[simp]: "Obs u ou \<in> L s \<longleftrightarrow> ou = out (getGMState s) u"
by (cases s) auto

primrec \<delta> :: "('St,'U,'C) state \<Rightarrow> ('St,'U,'C) state set" where
 "\<delta> (Idle st) = {Idle st} \<union> {State (do st u' c') u' c' | u' c'. True}"
|"\<delta> (State st u c) = {Idle st} \<union> {State (do st u' c') u' c' | u' c'. True}"

abbreviation s0 where "s0 \<equiv> State st0 any any"

definition f :: "('a, 'U, 'b) state \<Rightarrow> ('c, 'U, 'b) state \<Rightarrow> bool"
where
"f s s' \<equiv>
 \<forall> u c. u \<notin> GH \<longrightarrow> ((\<exists> st. s = State st u c) \<longleftrightarrow> (\<exists> st'. s' = State st' u c))"

definition g :: "('St, 'a, 'b) state \<Rightarrow> ('St, 'c, 'd) state \<Rightarrow> bool"
where
"g s s' \<equiv> \<forall> u1. u1 \<in> GL \<longrightarrow> out (getGMState s) u1 = out (getGMState s') u1"

lemma f_id[simp,intro!]: "f s s" unfolding f_def by auto

definition Sink :: "('St,'U,'C) state set"
where
"Sink = {Idle st | st . True}"

end (* context GM_sec_model *)


sublocale GM_sec_model < Shallow_Idle
where S = "UNIV::('St,'U,'C) state set"
and AP = "UNIV :: ('U,'C,'Out) aprop set" and AP' = "UNIV :: ('U,'C,'Out) aprop set"
and s0 = s0 and L = L and \<delta> = \<delta> and f = f and g = g and Sink = Sink
proof
  fix s show "\<exists>s'. s' \<in> \<delta> s \<inter> Sink"
  by (rule exI[of _ "Idle (getGMState s)"]) (cases s, auto simp: Sink_def)
next
  fix s assume "s \<in> Sink" thus "s \<in> \<delta> s" unfolding Sink_def by (cases s) auto
next
  fix s1 s2 assume "{s1, s2} \<subseteq> Sink" thus "f s1 s2"
  unfolding Sink_def f_def by auto
qed auto

context GM_sec_model
begin

lemma apropsOf_L_stateOf[simp]:
"wfp AP' \<pi> \<Longrightarrow> apropsOf \<pi> = L (stateOf \<pi>)"
unfolding wfp by (metis Int_UNIV_right snth.simps(1))

text\<open>The equality of two states w.r.t.\ a given ``last'' user-command pair:\<close>

definition eqOnUC ::
"nat \<Rightarrow> nat \<Rightarrow> 'U \<Rightarrow> 'C \<Rightarrow> (('St,'U,'C) state,('U,'C,'Out) aprop) sfmla"
where
"eqOnUC i i' u c \<equiv> eq (atom (Last u c) i) (atom (Last u c) i')"

text\<open>The equality of two states w.r.t.\ all their ``last'' user-command pairs with
the user not in GH:\<close>

definition eqButGH ::
"nat \<Rightarrow> nat \<Rightarrow> (('St,'U,'C) state,('U,'C,'Out) aprop) sfmla"
where
"eqButGH i i' \<equiv> scon {eqOnUC i i' u c | u c. (u,c) \<in> (UNIV - GH) \<times> UNIV}"

text\<open>The equality of two states w.r.t.\ a given ``observed'' user-observation pair:\<close>

definition eqOnUOut ::
"nat \<Rightarrow> nat \<Rightarrow> 'U \<Rightarrow> 'Out \<Rightarrow> (('St,'U,'C) state,('U,'C,'Out) aprop) sfmla"
where
"eqOnUOut i i' u ou \<equiv> eq (atom (Obs u ou) i) (atom (Obs u ou) i')"

text\<open>The equality of two states w.r.t.\ all their ``observed'' user-observation pairs with
the user in GL:\<close>

definition eqOnGL ::
"nat \<Rightarrow> nat \<Rightarrow> (('St,'U,'C) state,('U,'C,'Out) aprop) sfmla"
where
"eqOnGL i i' \<equiv> scon {eqOnUOut i i' u ou | u ou. (u,ou) \<in> GL \<times> UNIV}"

lemma eqOnUC_0_Suc0[simp]:
assumes "wfp AP' \<pi>" and "wfp AP' \<pi>'"
shows
"eqOnUC 0 (Suc 0) u c [\<pi>, \<pi>']
 \<longleftrightarrow>
 ((\<exists>st. stateOf \<pi> = State st u c) =
  (\<exists>st'. stateOf \<pi>' = State st' u c)
 )"
using assms unfolding eqOnUC_def atom_def[abs_def] eq_equals by simp

lemma eqOnUOut_0_Suc0[simp]:
assumes "wfp AP' \<pi>" and "wfp AP' \<pi>'"
shows
"eqOnUOut 0 (Suc 0) u ou [\<pi>, \<pi>']
 \<longleftrightarrow>
 (ou = out (getGMState (stateOf \<pi>)) u \<longleftrightarrow>
  ou = out (getGMState (stateOf \<pi>')) u
 )"
using assms unfolding eqOnUOut_def atom_def[abs_def] eq_equals by simp

text\<open>The (shallow) noninterference formula -- it will be proved equivalent to nonint,
the original statement of noninterference.\<close>

definition nonintSfmla :: "(('St,'U,'C) state,('U,'C,'Out) aprop) sfmla" where
"nonintSfmla \<equiv>
 fall2 (\<lambda> \<pi>' \<pi> \<pi>l.
        imp (alw (eqButGH (length \<pi>l) (Suc (length \<pi>l))))
            (alw (eqOnGL (length \<pi>l) (Suc (length \<pi>l))))
        (\<pi>l @ [\<pi>,\<pi>'])
       )"

text\<open>First, we show that nonintSfmla is equivalent to nonintSI, a variant of noninterference
that speaks about Synchronized Infinite paths.\<close>

definition nonintSI :: bool where
"nonintSI \<equiv>
 \<forall> \<pi> \<pi>'. wfp UNIV \<pi> \<and> wfp UNIV \<pi>' \<and> stateOf \<pi> = s0 \<and> stateOf \<pi>' = s0
           \<longrightarrow>
          (\<forall> i. (\<forall> j \<le> i. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))) \<longrightarrow> g (fst (\<pi> !! i)) (fst (\<pi>' !! i)))"

lemma nonintSfmla_nonintSI: "nonintSfmla [] \<longleftrightarrow> nonintSI"
proof-
  define \<phi> where "\<phi> \<pi>l = eqButGH (length \<pi>l) (Suc (length \<pi>l))"
    for \<pi>l :: "(('St,'U,'C) state,('U,'C,'Out) aprop) path list"
  define \<psi> where "\<psi> \<pi>l = eqOnGL (length \<pi>l) (Suc (length \<pi>l))"
    for \<pi>l :: "(('St,'U,'C) state,('U,'C,'Out) aprop) path list"
  have "\<And> \<pi> \<pi>'. wfp UNIV \<pi> \<and> wfp UNIV \<pi>' \<longrightarrow>
                 \<phi> [] [\<pi>,\<pi>'] = f (stateOf \<pi>) (stateOf \<pi>') \<and>
                 \<psi> [] [\<pi>,\<pi>'] = g (stateOf \<pi>) (stateOf \<pi>')"
  unfolding \<phi>_def \<psi>_def f_def g_def eqButGH_def eqOnGL_def
  by (fastforce simp add: scon_def eqOnUC_0_Suc0)
  from fall2_imp_alw_index[of \<phi> \<psi>, OF this]
  show ?thesis unfolding nonintSfmla_def nonintSI_def \<phi>_def \<psi>_def .
qed

text\<open>In turn, nonintSI will be shown equivalent to nonintS, a variant speaking about
Synchronized finite paths. To this end, we introduce a notion of well-formed finite path (wffp) -- besides
finiteness, another difference from the previously defined infinite paths is that, thanks to
the fact that here AP coincides with AP', paths are mere sequences of states as opposed
to pairs (state,set of atomic predicates).\<close>

inductive wffp :: "('St,'U,'C) state list \<Rightarrow> bool"
where
Singl[simp,intro!]: "wffp [s]"
|
Cons[intro]:
"\<lbrakk>s' \<in> \<delta> s; wffp (s' # sl)\<rbrakk>
 \<Longrightarrow>
 wffp (s # s' # sl)"

lemma wffp_induct2[consumes 1, case_names Singl Cons]:
assumes "wffp sl"
and "\<And> s. P [s]"
and "\<And> s sl. \<lbrakk>hd sl \<in> \<delta> s; wffp sl; P sl\<rbrakk> \<Longrightarrow> P (s # sl)"
shows "P sl"
using assms by induct auto

definition nonintS :: bool where
"nonintS \<equiv>
 \<forall> sl sl'. wffp sl \<and> wffp sl' \<and> hd sl = s0 \<and> hd sl' = s0 \<and>
            list_all2 f sl sl' \<longrightarrow> g (last sl) (last sl')"

lemma wffp_NE: assumes "wffp sl" shows "sl \<noteq> []"
using assms by induct auto

lemma wffp:
"wffp sl \<longleftrightarrow> sl \<noteq> [] \<and> (\<forall> i. Suc i < length sl \<longrightarrow> sl!(Suc i) \<in> \<delta>(sl!i))"
(is "?L \<longleftrightarrow> ?A \<and> (\<forall> i. ?R i)")
proof (intro iffI allI conjI)
  fix i assume ?L thus "?R i"
  proof (induct arbitrary: i)
    case (Cons s' s sl i) thus ?case by(cases i) auto
  qed auto
next
  assume "?A \<and> (\<forall> i. ?R i)" thus ?L proof(induct sl)
    case (Cons s sl) thus ?case apply safe
    by (cases sl) (force intro!: wffp.intros)+
  qed(auto intro: wffp.intros)
qed (auto simp: wffp_NE)

lemma wffp_hdI[intro]:
assumes "wffp sl" and "hd sl \<in> \<delta> s"
shows "wffp (s # sl)"
using assms by (cases sl) auto

lemma wffp_append:
assumes sl: "wffp sl" and sl1: "wffp sl1" and h: "hd sl1 \<in> \<delta> (last sl)"
shows "wffp (sl @ sl1)"
using sl h by (induct sl) (auto simp: sl1)

lemma wffp_append_iff:
"wffp (sl @ sl1) \<longleftrightarrow>
 (wffp sl \<and> sl1 = []) \<or>
 (sl = [] \<and> wffp sl1) \<or>
 (wffp sl \<and> wffp sl1 \<and> hd sl1 \<in> \<delta> (last sl))"
(is "_ \<longleftrightarrow> ?R")
proof
  assume "wffp (sl @ sl1)"
  thus ?R proof(induction "sl @ sl1" arbitrary: sl sl1 rule: list.induct)
    case (Cons s sl sl1 sl2) note C = Cons
    show ?case proof(cases "sl1 = [] \<or> sl2 = []")
      case False then obtain sll1 where sl1: "sl1 = s # sll1" and sl : "sl = sll1 @  sl2"
      using C(2) by(cases sl1) auto
      have wsl: "wffp sl" by (metis C False append_is_Nil_conv list.inject sl wffp.simps)
      show ?thesis using C(1)[OF sl, unfolded sl[symmetric], OF wsl]
      by (metis (no_types) C False wffp_hdI append_is_Nil_conv list.sel(1) hd_append
                last.simps list.inject sl sl1 wffp.simps)
    qed(insert C, auto)
  qed auto
qed (auto simp: wffp_append)

lemma wffp_to_wfp:
assumes \<pi>_def: "\<pi> = map (\<lambda> s. (s, L s)) sl @- sconst (toSink (last sl), L (toSink (last sl)))"
assumes sl: "wffp sl"
shows
"wfp UNIV \<pi> \<and>
 (\<forall> i < length sl. sl ! i = fst (\<pi> !! i)) \<and>
 (\<forall> i \<ge> length sl. fst (\<pi> !! i) = toSink (last sl)) \<and>
 stateOf \<pi> = hd sl"
unfolding wfp proof safe
  fix i s
  {assume "s \<in> snd (\<pi> !! i)" thus "s \<in> L (fst (\<pi> !! i))"
   unfolding \<pi>_def wffp  by (cases "i < length sl") auto
  }
  {assume "s \<in> L (fst (\<pi> !! i))" thus "s \<in> snd (\<pi> !! i)"
   unfolding \<pi>_def wffp  by (cases "i < length sl") auto
  }
  {fix j assume "j < length sl" thus "sl!j = fst (\<pi> !! j)"
   unfolding \<pi>_def apply (cases sl, simp) by (cases j) auto
  } note 1 = this
  {fix j assume "j \<ge> length sl" thus "fst (\<pi> !! j) = toSink (last sl)"
   using sl unfolding \<pi>_def by auto
  } note 2 = this
  show "fst (\<pi> !! Suc i) \<in> \<delta> (fst (\<pi> !! i))"
  proof(cases "length sl \<le> Suc i")
    case False hence "Suc i < length sl" by simp
    hence "fst (\<pi> !! Suc i) = sl!(Suc i) \<and> fst (\<pi> !! i) = sl!i"
    using 1 by fastforce
    thus ?thesis using sl False unfolding wffp by auto
  next
    case True note sl = True
    hence 22: "fst (\<pi> !! Suc i) = toSink (last sl)" using 2 by blast
    show ?thesis
    proof(cases "length sl \<le> i")
      case True
      hence "fst (\<pi> !! i) = toSink (last sl)" using 2 by auto
      thus ?thesis using 22 by (metis IntD2 Sink_idle UNIV_I toSink)
    next
      case False
      hence "last sl = sl!i" using sl
      by (metis Suc_eq_plus1 diff_add_inverse2 last_conv_nth le0 le_Suc_eq length_0_conv)
      moreover have "fst (\<pi> !! i) = sl!i" using False 1 by auto
      ultimately show ?thesis using 22 by (metis IntD1 UNIV_I toSink)
    qed
  qed
  show "stateOf \<pi> = hd sl" using wffp_NE[OF sl] unfolding \<pi>_def by (cases sl) auto
qed auto

lemma wffp_imp_appendL: "wffp (sl1 @ sl2) \<Longrightarrow> sl1 \<noteq> [] \<Longrightarrow> wffp sl1"
by (metis wffp_append_iff)

lemma wffp_imp_appendR: "wffp (sl1 @ sl2) \<Longrightarrow> sl2 \<noteq> [] \<Longrightarrow> wffp sl2"
by (metis wffp_append_iff)

lemma wffp_iff_map_Idle:
assumes "wffp sl"
shows
"\<exists> n st.
   (n > 0 \<and> sl = map Idle (replicate n st)) \<or>
   (\<exists> st1 u1 c1 sl1. sl = map Idle (replicate n st) @ [State st1 u1 c1] @ sl1)"
using assms proof (induction rule: wffp_induct2)
  case (Singl s) show ?case proof (cases s)
    case (Idle st)
    show ?thesis unfolding Idle by (intro exI[of _ "Suc 0"] exI[of _ st]) auto
  next
    case (State st1 u1 c1)
    show ?thesis unfolding State by (intro exI[of _ 0] exI[of _ st]) auto
  qed
next
  case (Cons s sl)
  {fix n st
   assume n: "n > 0" and sl: "sl = map Idle (replicate n st)"
   then obtain n' where n: "n = Suc n'" by (cases n) auto
   hence sl': "sl = (Idle st) # map Idle (replicate n' st)" using sl by auto
   have ?case proof(cases s)
     case (Idle st1)
     have st1: "st1 = st" using \<open>hd sl \<in> \<delta> s\<close> unfolding sl' Idle by auto
     show ?thesis apply (intro exI[of _ "Suc n"] exI[of _ st]) using n unfolding sl Idle st1 by auto
   next
     case (State st1 u1 c1)
     hence "s # sl = map Idle (replicate 0 st) @ [State st1 u1 c1] @ sl" by simp
     thus ?thesis by blast
   qed
  }
  moreover
  {fix n st st1 u1 c1 sl1 assume sl: "sl = map Idle (replicate n st) @ [State st1 u1 c1] @ sl1"
   have ?case proof(cases s)
     case (Idle st2)
     show ?thesis
     proof(cases n)
       case 0
       have "s # sl = map Idle (replicate (Suc 0) st2) @ [State st1 u1 c1] @ sl1"
       unfolding sl Idle 0 by simp
       thus ?thesis by blast
     next
       case (Suc n')
       hence sl': "sl = (Idle st) # map Idle (replicate n' st) @ [State st1 u1 c1] @ sl1" using sl by auto
       have st2: "st2 = st" using \<open>hd sl \<in> \<delta> s\<close> unfolding sl' Idle by auto
       have "s # sl = map Idle (replicate (Suc n) st) @ [State st1 u1 c1] @ sl1"
       unfolding sl Idle st2 by auto
       thus ?thesis by blast
     qed
   next
     case (State st1 u1 c1)
     hence "s # sl = map Idle (replicate 0 st) @ [State st1 u1 c1] @ sl" by simp
     thus ?thesis by blast
   qed
  }
  ultimately show ?case using Cons(3) by auto
qed

lemma wffp_cases3[elim, consumes 1, case_names Idle State Idle_State]:
assumes "wffp sl"
obtains
n st where
"n > 0" and "sl = map Idle (replicate n st)"
|
st u c sl1 where
"sl = State st u c # sl1" and "sl1 \<noteq> [] \<Longrightarrow> wffp sl1 \<and> hd sl1 \<in> \<delta> (State st u c)"
|
n st u c sl1 where
"n > 0" and "sl = map Idle (replicate n st) @ [State (do st u c) u c] @ sl1"
and "sl1 \<noteq> [] \<Longrightarrow> wffp sl1 \<and> hd sl1 \<in> \<delta> (State (do st u c) u c)"
proof-
  {fix n st
   assume n: "n > 0" and sl: "sl = map Idle (replicate n st)"
   hence thesis using that by auto
  }
  moreover
  {fix n st st1 u1 c1 sl1 assume sl: "sl = map Idle (replicate n st) @ [State st1 u1 c1] @ sl1"
   have 1: "sl1 \<noteq> [] \<Longrightarrow> wffp sl1 \<and> hd sl1 \<in> \<delta> (State st1 u1 c1)"
   by (metis append_is_Nil_conv assms last.simps not_Cons_self2 sl wffp_append_iff)
   have thesis
   proof(cases n)
     case 0
     have "sl = State st1 u1 c1 # sl1" using sl unfolding 0 by auto
     thus thesis using that 1 by blast
   next
     case (Suc n')
     hence 2: "replicate n st = replicate n' st @ [st]" by (metis replicate_Suc replicate_append_same)
     have "wffp (map Idle [st] @ [State st1 u1 c1])"
     using assms unfolding sl 2 unfolding map_append append_assoc
      by (metis (no_types) append_assoc append_is_Nil_conv append_self_conv
                 append_singl_rev neq_Nil_conv wffp_imp_appendL wffp_imp_appendR)
     hence st1: "st1 = do st u1 c1" by (auto elim!: wffp.cases)
     have "n > 0" using Suc by auto
     thus ?thesis using that 1 by (metis sl st1)
   qed
  }
  ultimately show thesis
  using wffp_iff_map_Idle[OF assms] by auto
qed

lemma wffp_cases2[elim, consumes 1, case_names Idle State]:
assumes "wffp sl"
obtains
n st where
"n > 0" and "sl = map Idle (replicate n st)"
|
n st st1 u c sl1 where
"sl = map Idle (replicate n st) @ [State st1 u c] @ sl1"
and "sl1 \<noteq> [] \<Longrightarrow> wffp sl1 \<and> hd sl1 \<in> \<delta> (State st1 u c)"
using assms apply(cases sl rule: wffp_cases3)
  apply metis
 apply (metis append_Cons append_Nil list.map(1) replicate_0)
apply (metis append_Cons append_Nil)
done

lemma wffp_Idle_Idle:
assumes "wffp (sl1 @ [Idle st1] @ [Idle st2] @ sl2)"
shows "st2 = st1"
proof-
  have "wffp [Idle st1, Idle st2]" using assms
  by (metis wffp_imp_appendR append_assoc append_singl_rev list.distinct(1) wffp_imp_appendL)
  thus ?thesis unfolding wffp by auto
qed

lemma wffp_Idle_State:
assumes "wffp (sl1 @ [Idle st1] @ [State st2 u2 c2] @ sl2)"
shows "st2 = st1 \<or> st2 = do st1 u2 c2"
proof-
  have "wffp [Idle st1, State st2 u2 c2]" using assms
  by (metis wffp_imp_appendR append_assoc append_singl_rev list.distinct(1) wffp_imp_appendL)
  thus ?thesis unfolding wffp by auto
qed

lemma wffp_State_Idle:
assumes "wffp (sl1 @ [State st1 u1 c1] @ [Idle st2] @ sl2)"
shows "st2 = st1"
proof-
  have "wffp [State st1 u1 c1, Idle st2]" using assms
  by (metis wffp_imp_appendR append_assoc append_singl_rev list.distinct(1) wffp_imp_appendL)
  thus ?thesis unfolding wffp by auto
qed

lemma wffp_State_State:
assumes "wffp (sl1 @ [State st1 u1 c1] @ [State st2 u2 c2] @ sl2)"
shows "st2 = do st1 u2 c2"
proof-
  have "wffp [State st1 u1 c1, State st2 u2 c2]" using assms
  by (metis wffp_imp_appendR append_assoc append_singl_rev list.distinct(1) wffp_imp_appendL)
  thus ?thesis unfolding wffp by auto
qed

lemma wfp_to_wffp:
assumes sl_def: "sl = map fst (stake i \<pi>)" and i: "i > 0" and \<pi>: "wfp UNIV \<pi>"
shows
"wffp sl \<and>
 (\<forall> j < length sl. fst (\<pi> !! j) = sl ! j) \<and>
 stateOf \<pi> = hd sl"
unfolding wffp proof(intro conjI allI impI)
  fix j
  have 1: "stake i \<pi> \<noteq> []" using i by auto
  show "stateOf \<pi> = hd sl" unfolding sl_def hd_map[OF 1] using i by simp
qed(insert assms, unfold sl_def wfp, auto)

lemma nonintSI_nonintS: "nonintSI \<longleftrightarrow> nonintS"
proof(unfold nonintS_def nonintSI_def, safe)
  fix sl sl' i
  obtain \<pi> \<pi>' where
  \<pi>: "\<pi> = map (\<lambda> s. (s, L s)) sl @- sconst (toSink (last sl), L (toSink (last sl)))" and
  \<pi>': "\<pi>' = map (\<lambda> s. (s, L s)) sl' @- sconst (toSink (last sl'), L (toSink (last sl')))"
  by blast
  assume 0: "\<forall> \<pi> \<pi>'.
    wfp UNIV \<pi> \<and> wfp UNIV \<pi>' \<and> stateOf \<pi> = s0 \<and> stateOf \<pi>' = s0
    \<longrightarrow>
    (\<forall> i. (\<forall> j \<le> i. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))) \<longrightarrow> g (fst (\<pi> !! i)) (fst (\<pi>' !! i)))"
  and slsl': "wffp sl" "wffp sl'" "hd sl = s0" "hd sl' = s0"
  and "list_all2 f sl sl'"
  hence l: "length sl = length sl'" and i: "\<forall> i < length sl. f (sl ! i) (sl' ! i)"
  unfolding list_all2_conv_all_nth by auto
  define i0 where "i0 = length sl - 1"
  have slsl'_NE: "sl \<noteq> [] \<and> sl' \<noteq> []" using slsl' wffp_NE by auto
  hence last: "last sl = sl!i0" "last sl' = sl'!i0"
  by (metis i0_def l slsl' last_conv_nth)+
  have i0: "i0 < length sl" "i0 < length sl'" unfolding i0_def using l slsl' slsl'_NE by auto
  have j: "\<forall> j \<le> i0. f (sl ! j) (sl' ! j)" using i slsl'_NE unfolding i0_def
  by (metis Suc_diff_eq_diff_pred Suc_diff_le Zero_neq_Suc diff_is_0_eq'
            le_less_linear length_greater_0_conv)
  show "g (last sl) (last sl')"
  unfolding last using 0 slsl' j i0
  using wffp_to_wfp[OF \<pi>] wffp_to_wfp[OF \<pi>'] by auto
next
  fix \<pi> \<pi>' i assume
  "\<forall> sl sl'. wffp sl \<and> wffp sl' \<and> hd sl = s0 \<and> hd sl' = s0 \<and> list_all2 f sl sl' \<longrightarrow> g (last sl) (last sl')"
  and \<pi>\<pi>': "wfp UNIV \<pi>" "wfp UNIV \<pi>'" and state: "stateOf \<pi> = s0" "stateOf \<pi>' = s0"
  and f: "\<forall>j\<le>i. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))"
  hence R:
  "\<forall> sl sl'. wffp sl \<and> wffp sl' \<and> hd sl = s0 \<and> hd sl' = s0 \<and> length sl = length sl'
            \<longrightarrow>
            ((\<forall> i < length sl. f (sl!i) (sl'!i)) \<longrightarrow> g (last sl) (last sl'))"
  unfolding list_all2_conv_all_nth by auto
  define i0 where "i0 = Suc i"
  have i0_ge: "i0 > 0" unfolding i0_def by auto
  have ii0: "i < i0" unfolding i0_def by auto
  have f: "\<forall>j<i0. f (fst (\<pi> !! j)) (fst (\<pi>' !! j))" using f unfolding i0_def by auto
  obtain sl sl' where
  sl_def: "sl = map fst (stake i0 \<pi>)" and sl'_def: "sl' = map fst (stake i0 \<pi>')"
  by blast
  have i0: "i0 = length sl" "length sl' = length sl" unfolding i0_def sl_def sl'_def by auto
  have 1: "sl!i = last sl" "sl'!i = last sl'"
  using i0 unfolding i0_def using last_conv_nth length_greater_0_conv by (metis diff_Suc_1 i0 i0_ge)+
  show "g (fst (\<pi> !! i)) (fst (\<pi>' !! i))"
  using wfp_to_wffp[OF sl_def i0_ge \<pi>\<pi>'(1)] wfp_to_wffp[OF sl'_def i0_ge \<pi>\<pi>'(2)]
  using R state f ii0 by (simp add: 1 i0)
qed


text\<open>Finally, we show that nonintS is equivalent to standard
noninterference (predicate nonint).\<close>

text\<open>purgeIdle removes the idle steps from a finite path:\<close>

definition purgeIdle :: "('St, 'U, 'C) state list \<Rightarrow> ('St, 'U, 'C) state list"
where "purgeIdle \<equiv> filter isState"

lemma purgeIdle_simps[simp]:
"purgeIdle [] = []"
"purgeIdle ((Idle st) # sl) = purgeIdle sl"
"purgeIdle ((State st u c) # sl) = (State st u c) # purgeIdle sl"
unfolding purgeIdle_def by auto

lemma purgeIdle_append:
"purgeIdle (sl1 @ sl2) = purgeIdle sl1 @ purgeIdle sl2"
unfolding purgeIdle_def by (metis filter_append)

lemma purgeIdle_set_isState:
assumes "s \<in> set (purgeIdle sl)"
shows "isState s"
using assms unfolding purgeIdle_def by (metis filter_set member_filter)

lemma purgeIdle_Nil_iff:
"purgeIdle sl = [] \<longleftrightarrow> (\<forall>s\<in>set sl. \<not> isState s)"
unfolding purgeIdle_def filter_empty_conv by auto

lemma purgeIdle_Cons_iff:
"purgeIdle sl = s # sll
 \<longleftrightarrow>
 (\<exists> sl1 sl2. sl = sl1 @ s # sl2 \<and>
            (\<forall>s1\<in>set sl1. \<not> isState s1) \<and> isState s \<and> purgeIdle sl2 = sll)"
unfolding purgeIdle_def filter_eq_Cons_iff by auto

lemma purgeIdle_map_Idle[simp]:
"purgeIdle (map Idle s) = []"
unfolding purgeIdle_def by auto

lemma purgeIdle_replicate_Idle[simp]:
"purgeIdle (replicate n (Idle st)) = []"
unfolding purgeIdle_def by auto

lemma wffp_purgeIdle_Nil:
assumes "wffp sl" and "purgeIdle sl = []"
shows "\<exists> n st. n > 0 \<and> sl = replicate n (Idle st)"
using assms proof(induction sl rule: wffp_induct2)
  case (Singl s) thus ?case
  by (cases s) (auto intro: exI[of _ "Suc 0"])
next
  case (Cons s sl)
  then obtain n st where sl: "sl = replicate n (Idle st)" by (cases s) auto
  obtain st1 where s: "s = Idle st1" using Cons by (cases s) auto
  have 1: "hd (replicate n (Idle st)) = Idle st" by (metis Cons.hyps(2) hd_replicate replicate_empty sl wffp)
  show ?case using Cons(1) by (auto intro: exI[of _ "Suc n"] exI[of _ st] simp: sl 1 s)
qed

lemma wffp_hd_purgeIdle:
assumes wsl: "wffp sl" and psl: "purgeIdle sl \<noteq> []"
and ist: "isState s" and hsl: "hd sl \<in> \<delta> s"
shows "hd (purgeIdle sl) \<in> \<delta> s"
using wsl proof(cases rule: wffp_cases3)
  case (Idle n st)
  show ?thesis using psl unfolding Idle by simp
next
  case (State st u c sl1)
  show ?thesis using psl hsl unfolding State by simp
next
  case (Idle_State n st u c sl1)
  show ?thesis using psl \<open>n > 0\<close> ist hsl unfolding Idle_State purgeIdle_append
  by (cases s) auto
qed

lemma wffp_purgeIdle:
assumes "wffp sl" and "purgeIdle sl \<noteq> []"
shows "wffp (purgeIdle sl)"
using assms proof(induction sl rule: length_induct)
  case (1 sl) note IH = 1
  from \<open>wffp sl\<close> show ?case proof(cases sl rule: wffp_cases2)
    case (Idle n st)
    have "purgeIdle sl = []" unfolding Idle by auto
    thus ?thesis using \<open>purgeIdle sl \<noteq> []\<close> by auto
  next
    case (State n st st1 u c sl1)
    hence 1: "purgeIdle sl = State st1 u c # purgeIdle sl1"
    by (auto simp del: map_replicate simp add: purgeIdle_append)
    show ?thesis
    proof(cases "purgeIdle sl1 = []")
      case True note psl1 = True
      show ?thesis unfolding 1 psl1 by auto
    next
      case False hence sl1NE: "sl1 \<noteq> []" by (cases sl1) auto
      hence sl1: "wffp sl1" and hsl1: "hd sl1 \<in> \<delta> (State st1 u c)" by (metis State(2))+
      have "length sl1 < length sl" using State by auto
      hence sl1: "wffp (purgeIdle sl1)" using IH(1) sl1 False by auto
      moreover have "hd (purgeIdle sl1) \<in> \<delta> (State st1 u c)"
      by (metis False GM_sec_model.wffp_hd_purgeIdle State(2) sl1NE state.discI(2))
      ultimately show ?thesis unfolding 1 by auto
    qed
  qed
qed

lemma isState_purgeIdle:
"(\<exists> sl. purgeIdle sl = sll) \<longleftrightarrow> list_all isState sll"
unfolding purgeIdle_def
by (metis Ball_set_list_all purgeIdle_def purgeIdle_set_isState filter_True)

lemma wffp_last_purgeIdle:
assumes "wffp sl" and "purgeIdle sl \<noteq> []"
shows "getGMState (last (purgeIdle sl)) = getGMState (last sl)"
using assms proof(induction sl rule: wffp_induct2)
  case (Singl s) thus ?case by (cases s) auto
next
  case (Cons s sl)
  hence slNE: "sl \<noteq> []" by (metis wffp_NE)
  show ?case
  proof(cases "purgeIdle sl = []")
    case True then obtain n st where sl: "sl = replicate n (Idle st)" by (metis Cons.hyps wffp_purgeIdle_Nil)
    hence n: "n > 0" using slNE by auto
    hence hsl: "hd sl = Idle st" and lsl: "last sl = Idle st" unfolding sl by auto
    have s: "isState s" using True Cons by (cases s) auto
    have 1: "getGMState s = st" using \<open>hd sl \<in> \<delta> s\<close> unfolding hsl by(cases s) auto
    show ?thesis using slNE n 1 hsl lsl s unfolding sl purgeIdle_replicate_Idle by (cases s) auto
  next
    case False
    thus ?thesis using Cons by (cases s) auto
  qed
qed

lemma wffp_isState_doo:
assumes "wffp sl" and "list_all isState sl"
shows "doo (getGMState (hd sl)) (map getGMUserCom (tl sl)) = getGMState (last sl)"
using assms proof(induction sl rule: wffp_induct2)
  case (Cons s sl)
  then obtain st u c where s: "s = State st u c" by(cases s ) auto
  have sl: "sl \<noteq> []" and sl1: "sl = hd sl # tl sl" using wffp_NE[OF \<open>wffp sl\<close>] by auto
  with Cons obtain st1 u1 c1 where hsl: "hd sl = State st1 u1 c1"
  by (metis isState_purgeIdle isState_def purgeIdle_Cons_iff)
  have 1: "getGMState (hd sl) = do st u1 c1" using \<open>hd sl \<in> \<delta> s\<close> unfolding hsl s by simp
  have "doo st (map getGMUserCom sl) = doo (do st u1 c1) (map getGMUserCom (tl sl))"
  by (subst sl1) (simp add: 1 hsl)
  thus ?case using sl Cons unfolding 1 s by auto
qed auto

lemma isState_hd_purgeIdle:
assumes wsl: "wffp sl" and ist: "isState (hd sl)"
shows "purgeIdle sl \<noteq> [] \<and> hd (purgeIdle sl) = hd sl"
using ist
by (intro conjI) (subst hd_Cons_tl[OF wffp_NE[OF wsl], symmetric], cases "hd sl", cases sl, auto)+

lemma wffp_isState_doo_purgeIdle:
fixes sl defines sll: "sll \<equiv> purgeIdle sl"
assumes wsl: "wffp sl" and ist: "isState (hd sl)"
shows "doo (getGMState (hd sl)) (map getGMUserCom (tl sll)) = getGMState (last sl)"
proof-
  note 1 = isState_hd_purgeIdle[OF wsl ist]
  hence wsll: "wffp sll" by (metis sll wffp_purgeIdle wsl)
  hence "doo (getGMState (hd sll)) (map getGMUserCom (tl sll)) = getGMState (last sll)"
  by (metis wffp_isState_doo isState_purgeIdle sll)
  thus ?thesis by (metis 1 sll wffp_last_purgeIdle wsl)
 qed

lemma map_getGMUserCom_surj:
assumes "isState s"
shows "\<exists> sl. wffp sl \<and> list_all isState sl \<and> hd sl = s \<and> map getGMUserCom (tl sl) = ucl"
using assms proof(induction ucl arbitrary: s rule: list_pair_induct)
  case Nil thus ?case apply(intro exI[of _ "[s]"]) by auto
next
  case (Cons u c ucl s)
  then obtain st1 u1 c1 where s: "s = State st1 u1 c1" by (cases s) auto
  define s1 where "s1 = State (do st1 u c) u c"
  obtain sl where sl: "wffp sl \<and> list_all isState sl" and hsl: "hd sl = s1"
  and msl: "map getGMUserCom (tl sl) = ucl" using Cons(1)[of s1] unfolding s1_def by auto
  thus ?case using s s1_def by (intro exI[of _ "s # sl"]) auto
qed

lemma purgeIdle_purge_ex:
assumes "wffp sl" and "list_all isState sl" and "map getGMUserCom (tl sl) = ucl"
shows "\<exists> sl'. hd sl' = ss' \<and> wffp sl' \<and>
              list_all2 f (tl sl) (tl sl') \<and>
              map getGMUserCom (purgeIdle (tl sl')) = purge GH ucl"
using assms proof(induction sl arbitrary: ucl ss' rule: wffp_induct2)
  case (Singl s ucl)
  thus ?case apply (intro exI[of _ "[ss']"]) by (cases ss') auto
next
  case (Cons ss sl ucl ss') note wsl = \<open>wffp sl\<close>
  hence slNE: "sl \<noteq> []" by (metis wffp_NE)
  obtain s sl1 where sl: "sl = s # sl1" using wffp_NE[OF \<open>wffp sl\<close>] by (cases sl) auto
  then obtain st u c where s: "s = State st u c" using Cons by (cases s) auto
  define ucl1 where "ucl1 = tl ucl"
  have ucl: "ucl = (u,c) # ucl1" and hsl: "hd sl = s" using Cons(5) unfolding s ucl1_def sl by auto
  have 1: "list_all isState sl" and 2: "map getGMUserCom (tl sl) = ucl1"
  using Cons unfolding ucl1_def s by auto
  define st' where "st' = getGMState ss'"
  show ?case
  proof(cases "u \<in> GH")
    case True note u = True
    define s' :: "('St, 'U, 'C) state" where "s' = Idle st'"
    obtain sl' where hsl': "hd sl' = s'" and wsl': "wffp sl'"
    and slsl': "list_all2 f (tl sl) (tl sl')" and m: "map getGMUserCom (purgeIdle (tl sl')) = purge GH ucl1"
    using Cons(3)[OF 1 2, of s'] by auto
    hence sl'NE: "sl' \<noteq> []" by (metis wffp_NE)
    have "wffp (ss' # sl')" using wsl' hsl' unfolding s'_def st'_def by (cases ss') auto
    moreover
    {have "f s s'" using u unfolding s'_def st'_def s f_def by blast
     hence "list_all2 f sl sl'" using slsl' hsl hsl' slNE sl'NE
     by (metis list.sel(1,3) list_all2_Cons neq_Nil_conv)
    }
    moreover have "map getGMUserCom (purgeIdle sl') = purge GH ucl"
    by (subst hd_Cons_tl[OF sl'NE, symmetric]) (auto simp: hsl' ucl s'_def u m)
    ultimately show ?thesis by (intro exI[of _ "ss' # sl'"]) auto
  next
    case False note u = False
    define s' where "s' = State (do st' u c) u c"
    obtain sl' where hsl': "hd sl' = s'" and wsl': "wffp sl'"
    and slsl': "list_all2 f (tl sl) (tl sl')" and m: "map getGMUserCom (purgeIdle (tl sl')) = purge GH ucl1"
    using Cons(3)[OF 1 2, of s'] by auto
    hence sl'NE: "sl' \<noteq> []" by (metis wffp_NE)
    have "wffp (ss' # sl')" using wsl' hsl' unfolding s'_def st'_def by (cases ss') auto
    moreover
    {have "f s s'" unfolding s'_def st'_def s f_def by simp
     hence "list_all2 f sl sl'" using slsl' hsl hsl' slNE sl'NE
     by (metis list.sel(1,3) list_all2_Cons neq_Nil_conv)
    }
    moreover have "map getGMUserCom (purgeIdle sl') = purge GH ucl"
    by (subst hd_Cons_tl[OF sl'NE, symmetric]) (auto simp: hsl' ucl s'_def u m)
    ultimately show ?thesis by (intro exI[of _ "ss' # sl'"]) auto
  qed
qed

lemma purgeIdle_getGMUserCom_purge:
fixes sl sl'
defines "ucl \<equiv> map getGMUserCom (purgeIdle (tl sl))"
    and "ucl' \<equiv> map getGMUserCom (purgeIdle (tl sl'))"
assumes wsl: "wffp sl" and wsl': "wffp sl'" and f: "list_all2 f sl sl'"
shows "purge GH ucl = purge GH ucl'"
proof-
  have "length sl = length sl'" using f by (metis list_all2_lengthD)
  thus ?thesis using assms proof(induction arbitrary: ucl ucl' rule: list_induct2)
    case Nil
    thus ?case by auto
  next
    case (Cons s sl s' sl')
    show ?case
    proof(cases "sl = []")
      case True hence "sl' = []" using Cons by auto
      thus ?thesis using True by auto
    next
      case False hence sl: "sl = hd sl # tl sl" by (cases sl) auto
      hence sl': "sl' = hd sl' # tl sl'" using \<open>length sl = length sl'\<close> by (cases sl') auto
      hence wsl[simp]: "wffp sl" and wsl'[simp]: "wffp sl'" using sl Cons
      by (metis Cons.prems append_singl_rev list.distinct sl' wffp_imp_appendR)+
      have f: "f (hd sl) (hd sl')" using \<open>list_all2 f (s # sl) (s' # sl')\<close> sl sl'
      by (metis list_all2_Cons)
      show ?thesis proof(cases "hd sl")
        case (Idle st) note hsl = Idle
        show ?thesis proof(cases "hd sl'")
          case (Idle st') note hsl' = Idle
          show ?thesis apply(subst sl, subst sl') using Cons unfolding hsl hsl' by auto
        next
          case (State st' u' c') note hsl' = State
          have u': "u' \<in> GH" using f unfolding hsl hsl' by (auto simp: f_def)
          show ?thesis apply(subst sl, subst sl') using Cons u' unfolding hsl hsl' by auto
        qed
      next
        case (State st u c) note hsl = State
        show ?thesis proof(cases "hd sl'")
          case (Idle st') note hsl' = Idle
          have u: "u \<in> GH" using f unfolding hsl hsl' by (auto simp: f_def)
          show ?thesis apply(subst sl, subst sl') using Cons u unfolding hsl hsl' by auto
        next
          case (State st' u' c') note hsl' = State
          have uu': "(u' \<in> GH \<longleftrightarrow> u \<in> GH) \<and> (u \<notin> GH \<longrightarrow> u' = u \<and> c' = c)"
          using f unfolding hsl hsl' by (auto simp: f_def)
          show ?thesis
          apply(subst sl, subst sl') using Cons uu' unfolding hsl hsl' by (cases "u \<in> GH") auto
        qed
      qed
    qed
  qed
qed

lemma nonintS_iff_nonint:
"nonintS \<longleftrightarrow> nonint"
unfolding nonintS_def nonint_def proof safe
  fix ucl u
  assume
  1: "\<forall>sl sl'. wffp sl \<and> wffp sl' \<and> hd sl = s0 \<and> hd sl' = s0 \<and> list_all2 f sl sl' \<longrightarrow>
               g (last sl) (last sl')"
  and u: "u \<in> GL"
  obtain sl where wsl: "wffp sl" and l: "list_all isState sl" and hsl: "hd sl = s0"
  and m: "map getGMUserCom (tl sl) = ucl" using map_getGMUserCom_surj[of s0] by auto
  then obtain sl' where hsl': "hd sl' = hd sl" and wsl': "wffp sl'" and f: "list_all2 f (tl sl) (tl sl')"
  and m': "map getGMUserCom (purgeIdle (tl sl')) = purge GH ucl"
  by (metis purgeIdle_purge_ex)
  have slNE: "sl \<noteq> []" and sl'NE: "sl' \<noteq> []" using wsl wsl' by (metis wffp_NE)+
  have 2: "getGMState (hd sl) = st0" unfolding hsl by auto
  have 3: "tl (purgeIdle sl') = purgeIdle (tl sl')"
  apply(subst hd_Cons_tl[OF sl'NE, symmetric], rule sym, subst hd_Cons_tl[OF sl'NE, symmetric])
  unfolding hsl hsl' by auto
  have f: "list_all2 f sl sl'"
  apply (subst hd_Cons_tl[OF slNE, symmetric], subst hd_Cons_tl[OF sl'NE, symmetric])
  using f hsl' unfolding f_def by auto
  hence g: "g (last sl) (last sl')" using 1 wsl wsl' hsl hsl' by auto
  moreover have "getGMState (last sl) = doo st0 ucl"
  unfolding m[symmetric] 2[symmetric] using wffp_isState_doo[OF wsl l] by simp
  moreover have "getGMState (last sl') = doo st0 (purge GH ucl)"
  using wffp_isState_doo_purgeIdle[OF wsl'] unfolding hsl' hsl m' 3 by auto
  ultimately show "out (doo st0 ucl) u = out (doo st0 (purge GH ucl)) u"
  unfolding g_def using u by auto
next
  fix sl sl'
  assume 1: "\<forall>ucl. \<forall>u\<in>GL. out (doo st0 ucl) u = out (doo st0 (purge GH ucl)) u"
  and wsl: "wffp sl" and wsl': "wffp sl'" and hsl: "hd sl = s0" and hsl': "hd sl' = s0"
  and f: "list_all2 f sl sl'"
  define ucl where "ucl = map getGMUserCom (tl (purgeIdle sl))"
  define ucl' where "ucl' = map getGMUserCom (tl (purgeIdle sl'))"
  have 2: "tl (purgeIdle sl) = purgeIdle (tl sl)" "tl (purgeIdle sl') = purgeIdle (tl sl')"
  by (subst hd_Cons_tl[OF wffp_NE[OF wsl], symmetric, unfolded hsl], auto)[]
     (subst hd_Cons_tl[OF wffp_NE[OF wsl'], symmetric, unfolded hsl'], auto)
  have "purge GH ucl = purge GH ucl'"
  unfolding ucl_def ucl'_def 2 by (metis purgeIdle_getGMUserCom_purge f wsl wsl')
  moreover have "getGMState (last sl) = doo st0 ucl \<and> getGMState (last sl') = doo st0 ucl'"
  using wffp_isState_doo_purgeIdle[OF wsl] wffp_isState_doo_purgeIdle[OF wsl']
  unfolding hsl hsl' ucl_def ucl'_def by auto
  ultimately show "g (last sl) (last sl')" unfolding g_def using 1 by metis
qed

theorem nonintSfmla_iff_nonint:
"nonintSfmla [] \<longleftrightarrow> nonint"
by (metis nonintSI_nonintS nonintS_iff_nonint nonintSfmla_nonintSI)


(*<*)
end (* context GM_sec_model *)
(*>*)

text\<open>end-of-context GM-sec-model\<close>


(*<*)
end
(*>*)
