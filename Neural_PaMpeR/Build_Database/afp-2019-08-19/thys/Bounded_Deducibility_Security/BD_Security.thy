section \<open>BD Security\<close>

(*<*)
theory BD_Security
imports IO_Automaton
begin
(*>*)


subsection\<open>Definition\<close>

declare Let_def[simp]

no_notation relcomp (infixr "O" 75)

abbreviation never :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where "never U \<equiv> list_all (\<lambda> a. \<not> U a)"

function filtermap ::
"(('state,'act,'out) trans \<Rightarrow> bool) \<Rightarrow> (('state,'act,'out) trans \<Rightarrow> 'a) \<Rightarrow> ('state,'act,'out) trace \<Rightarrow> 'a list"
where
"filtermap pred func [] = []"
|
"\<not> pred trn \<Longrightarrow> filtermap pred func (trn # tr) = filtermap pred func tr"
|
"pred trn \<Longrightarrow> filtermap pred func (trn # tr) = func trn # filtermap pred func tr"
by auto (metis list.exhaust)
termination by lexicographic_order

locale BD_Security = IO_Automaton istate step
 for istate :: 'state and step :: "'state \<Rightarrow> 'act \<Rightarrow> 'out \<times> 'state"
+
fixes (* value filtering and production:  *)
   \<phi> :: "('state,'act,'out) trans => bool" and f :: "('state,'act,'out) trans \<Rightarrow> 'value"
 and (* observation filtering and production: *)
   \<gamma> :: "('state,'act,'out) trans => bool" and g :: "('state,'act,'out) trans \<Rightarrow> 'obs"
 and (* declassification trigger:  *)
   T :: "('state,'act,'out) trans \<Rightarrow> bool"
 and (* declassification bound: *)
   B :: "'value list \<Rightarrow> 'value list \<Rightarrow> bool"
begin

(* The value function: *)
definition V :: "('state,'act,'out) trace \<Rightarrow> 'value list" where "V \<equiv> filtermap \<phi> f"
(* The observation function: *)
definition O :: "('state,'act,'out) trace \<Rightarrow> 'obs list" where "O \<equiv> filtermap \<gamma> g"

lemma V_simps[simp]:
"V [] = []"  "\<not> \<phi> trn \<Longrightarrow> V (trn # tr) = V tr"  "\<phi> trn \<Longrightarrow> V (trn # tr) = f trn # V tr"
unfolding V_def by auto

lemma O_simps[simp]:
"O [] = []"  "\<not> \<gamma> trn \<Longrightarrow> O (trn # tr) = O tr"  "\<gamma> trn \<Longrightarrow> O (trn # tr) = g trn # O tr"
unfolding O_def by auto

(* Reachable states by transitions satisfying T: *)
inductive reachNT:: "'state \<Rightarrow> bool" where
Istate: "reachNT istate"
|
Step:
"\<lbrakk>reachNT (srcOf trn); step (srcOf trn) (actOf trn) = (outOf trn, tgtOf trn); \<not> T trn\<rbrakk>
 \<Longrightarrow> reachNT (tgtOf trn)"

lemma reachNT_PairI:
assumes "reachNT s" and "step s a = (ou, s')" and "\<not> T (Trans s a ou s')"
shows "reachNT s'"
by (metis BD_Security.reachNT.simps assms trans.sel)

lemma reachNT_reach: assumes "reachNT s"  shows "reach s"
using assms by induct (auto intro: reach.intros, metis reach.Step snd_conv validTrans)

lemma reachNT_stateO_aux:
assumes "reachNT s"
shows "s = istate \<or> (\<exists>sh a ou. reach sh \<and> step sh a = (ou,s) \<and> \<not>T (Trans sh a ou s))"
using assms by induct (clarsimp, metis BD_Security.reachNT_reach trans.exhaust_sel)

lemma reachNT_state_cases[cases set,consumes 1, case_names init step]:
assumes "reachNT s"
obtains "s = istate"
| sh a ou where "reach sh" "step sh a = (ou,s)" "\<not>T (Trans sh a ou s)"
by (metis reachNT_stateO_aux[OF assms])

(* This is assumed to be an invariant only modulo non T  *)
definition invarNT where
"invarNT Inv \<equiv> \<forall> s a ou s'. reachNT s \<and> Inv s \<and> \<not> T (Trans s a ou s') \<and> step s a = (ou,s') \<longrightarrow> Inv s'"

lemma invarNT_disj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<or> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma invarNT_conj:
assumes "invarNT Inv1" and "invarNT Inv2"
shows "invarNT (\<lambda> s. Inv1 s \<and> Inv2 s)"
using assms unfolding invarNT_def by blast

lemma holdsIstate_invarNT:
assumes h: "holdsIstate Inv" and i: "invarNT Inv" and a: "reachNT s"
shows "Inv s"
using a using h i unfolding holdsIstate_def invarNT_def
by (induct rule: reachNT.induct) (metis i invarNT_def trans.exhaust_sel)+

(* BD security: *)
definition secure :: bool where
"secure \<equiv>
 \<forall> tr vl vl1.
   validFrom istate tr \<and> never T tr \<and> B vl vl1 \<and> V tr = vl \<longrightarrow>
   (\<exists> tr1. validFrom istate tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1)"

lemma V_iff_non_\<phi>[simp]: "V (trn # tr) = V tr \<longleftrightarrow> \<not> \<phi> trn"
by (cases "\<phi> trn") auto

lemma V_imp_\<phi>: "V (trn # tr) = v # V tr \<Longrightarrow> \<phi> trn"
by (cases "\<phi> trn") auto

lemma V_imp_Nil: "V (trn # tr) = [] \<Longrightarrow> V tr = []"
by (metis V_simps list.distinct trans.exhaust)

lemma V_iff_Nil[simp]: "V (trn # tr) = [] \<longleftrightarrow> \<not> \<phi> trn \<and> V tr = []"
by (metis V_iff_non_\<phi> V_imp_Nil)

end (* context BD_Security *)


subsection\<open>Unwinding proof method\<close>

context BD_Security
begin

definition consume :: "('state,'act,'out) trans \<Rightarrow> 'value list \<Rightarrow> 'value list \<Rightarrow> bool" where
"consume trn vl vl' \<equiv>
 if \<phi> trn then vl \<noteq> [] \<and> f trn = hd vl \<and> vl' = tl vl
 else vl' = vl"

lemma length_consume[simp]:
"consume trn vl vl' \<Longrightarrow> length vl' < Suc (length vl)"
unfolding consume_def by (auto split: if_splits)

lemma ex_consume_\<phi>:
assumes "\<not> \<phi> trn"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by auto

lemma ex_consume_NO:
assumes "vl \<noteq> []" and "f trn = hd vl"
obtains vl' where "consume trn vl vl'"
using assms unfolding consume_def by (cases "\<phi> trn") auto

(* independent action: *)
definition iaction where
"iaction \<Delta> s vl s1 vl1 \<equiv>
 \<exists> a1 ou1 s1' vl1'.
   let trn1 = Trans s1 a1 ou1 s1' in
   validTrans trn1 \<and>
   \<phi> trn1 \<and> consume trn1 vl1 vl1' \<and>
   \<not> \<gamma> trn1
   \<and>
   \<Delta> s vl s1' vl1'"

lemma iactionI[intro?]:
assumes "step s1 a1 = (ou1, s1')" and "\<phi> (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'"
and "\<not> \<gamma> (Trans s1 a1 ou1 s1')" and "\<Delta> s vl s1' vl1'"
shows "iaction \<Delta> s vl s1 vl1"
unfolding iaction_def using assms by auto

definition match where
"match \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<exists> a1 ou1 s1' vl1'.
    let trn = Trans s a ou s'; trn1 = Trans s1 a1 ou1 s1' in
    validTrans trn1 \<and>
    consume trn1 vl1 vl1' \<and>
    \<gamma> trn = \<gamma> trn1 \<and> (\<gamma> trn \<longrightarrow> g trn = g trn1) \<and>
    \<Delta> s' vl' s1' vl1'"

lemma matchI[intro?]:
assumes "validTrans (Trans s1 a1 ou1 s1')"
and "consume (Trans s1 a1 ou1 s1') vl1 vl1'" and "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a1 ou1 s1')"
and "\<gamma> (Trans s a ou s') \<Longrightarrow> g (Trans s a ou s') = g (Trans s1 a1 ou1 s1')"
and "\<Delta> s' vl' s1' vl1'"
shows "match \<Delta> s s1 vl1 a ou s' vl'"
unfolding match_def using assms by auto

definition ignore where
"ignore \<Delta> s s1 vl1 a ou s' vl' \<equiv>
 \<not> \<gamma> (Trans s a ou s') \<and>
 \<Delta> s' vl' s1 vl1"

lemma ignoreI[intro?]:
assumes "\<not> \<gamma> (Trans s a ou s')" and "\<Delta> s' vl' s1 vl1"
shows "ignore \<Delta> s s1 vl1 a ou s' vl'"
unfolding ignore_def using assms by auto

(* reaction: *)
definition reaction where
"reaction \<Delta> s vl s1 vl1 \<equiv>
 \<forall> a ou s' vl'.
   let trn = Trans s a ou s' in
   validTrans trn \<and> \<not> T trn \<and>
   consume trn vl vl'
   \<longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl'
   \<or>
   ignore \<Delta> s s1 vl1 a ou s' vl'"

lemma reactionI[intro?]:
assumes
"\<And>a ou s' vl'.
   \<lbrakk>step s a = (ou, s'); \<not> T (Trans s a ou s');
    consume (Trans s a ou s') vl vl'\<rbrakk>
   \<Longrightarrow>
   match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'"
shows "reaction \<Delta> s vl s1 vl1"
using assms unfolding reaction_def by auto

definition "exit" :: "'state \<Rightarrow> 'value \<Rightarrow> bool" where
"exit s v \<equiv> \<forall> tr trn. validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn \<longrightarrow> f trn \<noteq> v"

lemma exit_coind:
assumes K: "K s"
and I: "\<And> trn. \<lbrakk>K (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
        \<Longrightarrow> (\<phi> trn \<longrightarrow> f trn \<noteq> v) \<and> K (tgtOf trn)"
shows "exit s v"
using K unfolding exit_def proof(intro allI conjI impI)
  fix tr trn assume "K s" and "validFrom s (tr ## trn) \<and> never T (tr ## trn) \<and> \<phi> trn"
  thus "f trn \<noteq> v"
  using I unfolding validFrom_def by (induction tr arbitrary: s trn)
  (auto, metis neq_Nil_conv rotate1.simps(2) rotate1_is_Nil_conv valid_ConsE)
qed

definition noVal where
"noVal K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal_disj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<or> Inv2 s) v"
using assms unfolding noVal_def by metis

lemma noVal_conj:
assumes "noVal Inv1 v" and "noVal Inv2 v"
shows "noVal (\<lambda> s. Inv1 s \<and> Inv2 s) v"
using assms unfolding noVal_def by blast

(* Often encountered sufficient criterion for noVal: *)
definition no\<phi> where
"no\<phi> K \<equiv> \<forall> s a ou s'. reachNT s \<and> K s \<and> step s a = (ou,s') \<longrightarrow> \<not> \<phi> (Trans s a ou s')"

lemma no\<phi>_noVal: "no\<phi> K \<Longrightarrow> noVal K v"
unfolding no\<phi>_def noVal_def by auto

(* intro rule for quick inline checks: *)
lemma exitI[consumes 2, induct pred: "exit"]:
assumes rs: "reachNT s" and K: "K s"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s'"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms by (intro exit_coind[of ?K])
  (metis BD_Security.reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* intro rule for more elaborate checks: *)
lemma exitI2:
assumes rs: "reachNT s" and K: "K s"
and "invarNT K" and "noVal K v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s"
  show ?thesis using assms unfolding invarNT_def noVal_def apply(intro exit_coind[of ?K])
  by metis (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)
qed

(* Binary version of the invariant: *)
definition noVal2 where
"noVal2 K v \<equiv>
 \<forall> s a ou s'. reachNT s \<and> K s v \<and> step s a = (ou,s') \<and> \<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v"

lemma noVal2_disj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<or> Inv2 s v) v"
using assms unfolding noVal2_def by metis

lemma noVal2_conj:
assumes "noVal2 Inv1 v" and "noVal2 Inv2 v"
shows "noVal2 (\<lambda> s v. Inv1 s v \<and> Inv2 s v) v"
using assms unfolding noVal2_def by blast

lemma noVal_noVal2: "noVal K v \<Longrightarrow> noVal2 (\<lambda> s v. K s) v"
unfolding noVal_def noVal2_def by auto

lemma exitI_noVal2[consumes 2, induct pred: "exit"]:
assumes rs: "reachNT s" and K: "K s v"
and I:
"\<And> s a ou s'.
   \<lbrakk>reach s; reachNT s; step s a = (ou,s'); K s v\<rbrakk>
   \<Longrightarrow> (\<phi> (Trans s a ou s') \<longrightarrow> f (Trans s a ou s') \<noteq> v) \<and> K s' v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms by (intro exit_coind[of ?K])
  (metis BD_Security.reachNT_reach IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

lemma exitI2_noVal2:
assumes rs: "reachNT s" and K: "K s v"
and "invarNT (\<lambda> s. K s v)" and "noVal2 K v"
shows "exit s v"
proof-
  let ?K = "\<lambda> s. reachNT s \<and> K s v"
  show ?thesis using assms unfolding invarNT_def noVal2_def
  by (intro exit_coind[of ?K]) (metis IO_Automaton.validTrans reachNT.Step trans.exhaust_sel)+
qed

(* end binary version *)

lemma exit_validFrom:
assumes vl: "vl \<noteq> []" and i: "exit s (hd vl)" and v: "validFrom s tr" and V: "V tr = vl"
and T: "never T tr"
shows False
using i v V T proof(induction tr arbitrary: s)
  case Nil thus ?case by (metis V_simps(1) vl)
next
  case (Cons trn tr s)
  show ?case
  proof(cases "\<phi> trn")
    case True
    hence "f trn = hd vl" using Cons by (metis V_simps(3) hd_Cons_tl list.inject vl)
    moreover have "validFrom s [trn]" using \<open>validFrom s (trn # tr)\<close>
    unfolding validFrom_def by auto
    ultimately show ?thesis using Cons True unfolding exit_def
    by (elim allE[of _ "[]"]) auto
  next
    case False
    hence "V tr = vl" using Cons by auto
    moreover have "never T tr" by (metis Cons.prems list_all_simps)
    moreover from \<open>validFrom s (trn # tr)\<close> have "validFrom (tgtOf trn) tr" and s: "s = srcOf trn"
    by (metis list.distinct(1) validFrom_def valid_ConsE Cons.prems(2) 
              IO_Automaton.validFrom_def list.discI list.sel(1))+    
    moreover have "exit (tgtOf trn) (hd vl)" using \<open>exit s (hd vl)\<close>
    unfolding exit_def s by simp
    (metis (no_types) Cons.prems(2) Cons.prems(4) append_Cons list.sel(1)
           list.distinct list_all_simps valid.Cons validFrom_def valid_ConsE)
    ultimately show ?thesis using Cons(1) by auto
  qed
qed

definition unwind where
"unwind \<Delta> \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   (vl \<noteq> [] \<and> exit s (hd vl))
   \<or>
   iaction \<Delta> s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction \<Delta> s vl s1 vl1)"

lemma unwindI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reach s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   (vl \<noteq> [] \<and> exit s (hd vl))
   \<or>
   iaction \<Delta> s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction \<Delta> s vl s1 vl1)"
shows "unwind \<Delta>"
using assms unfolding unwind_def by auto

lemma unwind_trace:
assumes unwind: "unwind \<Delta>" and "reachNT s" and "reach s1" and "\<Delta> s vl s1 vl1"
and "validFrom s tr" and "never T tr" and "V tr = vl"
shows "\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
proof-
  let ?S = "\<lambda> tr vl1.
  \<forall> s vl s1. reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1 \<and> validFrom s tr \<and> never T tr \<and> V tr = vl \<longrightarrow>
          (\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1)"
  let ?f = "\<lambda> tr vl1. length tr + length vl1"
  have "?S tr vl1"
  proof(induct rule: measure_induct2[of ?f ?S])
    case (1 tr vl1)
    show ?case
    proof(intro allI impI, elim conjE)
      fix s vl s1 assume rs: "reachNT s" and rs1: "reach s1" and \<Delta>: "\<Delta> s vl s1 vl1"
      and v: "validFrom s tr" and NT: "never T tr" and V: "V tr = vl"
      hence "(vl \<noteq> [] \<and> exit s (hd vl)) \<or>
             iaction \<Delta> s vl s1 vl1 \<or>
             (reaction \<Delta> s vl s1 vl1 \<and> \<not> iaction \<Delta> s vl s1 vl1)"
      (is "?exit \<or> ?iact \<or> ?react \<and> _")
      using unwind unfolding unwind_def by metis
      thus "\<exists>tr1. validFrom s1 tr1 \<and> O tr1 = O tr \<and> V tr1 = vl1"
      proof safe
        assume "vl \<noteq> []" and "exit s (hd vl)"
        hence False using v V exit_validFrom NT by auto
        thus ?thesis by auto
      next
        assume ?iact
        thus ?thesis  unfolding iaction_def Let_def proof safe
          fix a1 :: 'act and ou1 :: 'out and s1' :: 'state and vl1'
          let ?trn1 = "Trans s1 a1 ou1 s1'"
          assume vtrans1: "validTrans ?trn1" and \<phi>1: "\<phi> ?trn1"
          and c: "consume ?trn1 vl1 vl1'" and \<gamma>: "\<not> \<gamma> ?trn1" and \<Delta>: "\<Delta> s vl s1' vl1'"
          from \<phi>1 c obtain v1 where vl1: "vl1 = v1 # vl1'" and f1: "f ?trn1 = v1"
          unfolding consume_def by (cases vl1) auto
          have rs1': "reach s1'" using rs1 vtrans1 by (auto intro: reach_PairI)
          obtain tr1 where v1: "validFrom s1' tr1" and O: "O tr1 = O tr" and V: "V tr1 = vl1'"
          using 1[of tr vl1'] rs rs1' \<Delta> v NT V unfolding vl1 by auto
          show ?thesis
          using vtrans1 v1 O \<gamma> V \<phi>1 f1 unfolding vl1 by (intro exI[of _ "?trn1 # tr1"]) auto
        qed
      next
        assume react: ?react and iact: "\<not> ?iact"
        show ?thesis
        proof(cases tr)
          case Nil note tr = Nil
          hence vl: "vl = []" using V by simp
          show ?thesis proof(cases vl1)
            case Nil note vl1 = Nil
            show ?thesis using 1[of tr vl1] \<Delta> V NT V unfolding tr vl1 by auto
          next
            case Cons
            hence False using vl unwind rs rs1 \<Delta> iact unfolding unwind_def by auto
            thus ?thesis by auto
          qed
        next
          case (Cons trn tr') note tr = Cons
          show ?thesis
          proof(cases trn)
            case (Trans ss a ou s') note trn = Trans let ?trn = "Trans s a ou s'"
            have ss: "ss = s" using trn v unfolding tr validFrom_def by auto
            have Ta: "\<not> T ?trn" and s: "s = srcOf trn" and vtrans: "validTrans ?trn"
            and v': "validFrom s' tr'" and NT': "never T tr'"
            using v NT V unfolding tr validFrom_def trn by auto
            have rs': "reachNT s'" using rs vtrans Ta by (auto intro: reachNT_PairI)
            {assume "\<phi> ?trn" hence "vl \<noteq> [] \<and> f ?trn = hd vl" using V unfolding tr trn ss by auto
            }
            then obtain vl' where c: "consume ?trn vl vl'"
            using ex_consume_\<phi> ex_consume_NO by metis
            have V': "V tr' = vl'" using V c unfolding tr trn ss consume_def
            by (cases "\<phi> ?trn") (simp_all, metis list.sel(2-3))
            have "match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'" (is "?match \<or> ?ignore")
            using react unfolding reaction_def using vtrans Ta c by auto
            thus ?thesis proof safe
              assume ?match
              thus ?thesis unfolding match_def Let_def proof (elim exE conjE)
                fix a1 :: 'act and ou1 :: 'out and s1' :: 'state and vl1'
                let ?trn1 = "Trans s1 a1 ou1 s1'"
                assume \<Delta>: "\<Delta> s' vl' s1' vl1'" and vtrans1: "validTrans ?trn1"
                and c1: "consume ?trn1 vl1 vl1'" and \<gamma>: "\<gamma> ?trn = \<gamma> ?trn1"
                and g: "\<gamma> ?trn \<longrightarrow> g ?trn = g ?trn1"
                have rs1': "reach s1'" using rs rs1 vtrans vtrans1 by (auto intro: reach_PairI)
                obtain tr1 where v1: "validFrom s1' tr1" and O: "O tr1 = O tr'" and V: "V tr1 = vl1'"
                using 1[of tr' vl1'] rs' rs1' \<Delta> v' NT' V' c1 unfolding tr by auto
                have "V (?trn1 # tr1) = vl1"
                using c1 V unfolding consume_def by (cases "\<phi> ?trn1") auto
                thus ?thesis
                apply(intro exI[of _ "Trans s1 a1 ou1 s1' # tr1"])
                using vtrans1 v1 O \<gamma> g V unfolding tr trn ss by auto
              qed
            next
              assume ?ignore
              thus ?thesis unfolding ignore_def Let_def proof (elim exE conjE)
                assume \<gamma>: "\<not> \<gamma> ?trn" and \<Delta>: "\<Delta> s' vl' s1 vl1"
                obtain tr1 where v1: "validFrom s1 tr1" and O: "O tr1 = O tr'" and V: "V tr1 = vl1"
                using 1[of tr' vl1] rs' rs1 \<Delta> v' NT' V' c unfolding tr by auto
                show ?thesis
                apply(intro exI[of _ tr1])
                using v1 O V \<gamma> unfolding tr trn ss by auto
              qed
            qed
          qed
        qed
      qed
    qed
  qed
  thus ?thesis using assms by auto
qed

theorem unwind_secure:
assumes init: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta> istate vl istate vl1"
and unwind: "unwind \<Delta>"
shows secure
using assms unwind_trace unfolding secure_def by (blast intro: reach.Istate reachNT.Istate)


(*<*)
end (* locale BD_Security *)


end
(*>*)
