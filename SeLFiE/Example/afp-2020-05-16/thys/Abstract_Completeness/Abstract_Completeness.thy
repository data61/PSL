(*<*)
(* An abstract completeness theorem *)
theory Abstract_Completeness
imports
  Collections.Locale_Code
  "HOL-Library.Countable_Set"
  "HOL-Library.FSet"
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
begin
(*>*)

section\<open>General Tree Concepts\<close>

codatatype 'a tree = Node (root: 'a) (cont: "'a tree fset")

inductive tfinite where
  tfinite: "(\<And> t'. t' |\<in>| cont t \<Longrightarrow> tfinite t') \<Longrightarrow> tfinite t"


(*<*)(* Infinite paths in trees. *)(*>*)
coinductive ipath where
  ipath: "\<lbrakk>root t = shd steps; t' |\<in>| cont t; ipath t' (stl steps)\<rbrakk> \<Longrightarrow> ipath t steps"

(*<*)(* Finite trees have no infinite paths. *)
lemma ftree_no_ipath: "tfinite t \<Longrightarrow> \<not> ipath t steps"
  by (induct t arbitrary: steps rule: tfinite.induct) (auto elim: ipath.cases)
(*>*)

primcorec konig where
  "shd (konig t) = root t"
| "stl (konig t) = konig (SOME t'. t' |\<in>| cont t \<and> \<not> tfinite t')"

lemma Konig: "\<not> tfinite t \<Longrightarrow> ipath t (konig t)"
  by (coinduction arbitrary: t) (metis (lifting) tfinite.simps konig.simps someI_ex)


section\<open>Rule Systems\<close>

(*<*)(* A step consists of a pair (s,r) such that the rule r is taken in state s. *)(*>*)
type_synonym ('state, 'rule) step = "'state \<times> 'rule"
(*<*)(* A derivation tree is a tree of steps: *)(*>*)
type_synonym ('state, 'rule) dtree = "('state, 'rule) step tree"

locale RuleSystem_Defs =
fixes eff :: "'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool"
(* The countable set of rules is initially provided as a stream: *)
and rules :: "'rule stream"
begin

abbreviation "R \<equiv> sset rules"

lemma countable_R: "countable R" by (metis countableI_type countable_image sset_range)
lemma NE_R: "R \<noteq> {}" by (metis UNIV_witness all_not_in_conv empty_is_image sset_range)

definition "enabled r s \<equiv> \<exists> sl. eff r s sl"
definition "pickEff r s \<equiv> if enabled r s then (SOME sl. eff r s sl) else the None"

lemma pickEff: "enabled r s \<Longrightarrow> eff r s (pickEff r s)"
  by (metis enabled_def pickEff_def tfl_some)

abbreviation "effStep step \<equiv> eff (snd step) (fst step)"
abbreviation "enabledAtStep r step \<equiv> enabled r (fst step)"
abbreviation "takenAtStep r step \<equiv> snd step = r"

text \<open>Saturation is a very strong notion of fairness:
  If a rule is enabled at some point, it will eventually be taken.\<close>
definition "saturated r \<equiv> alw (holds (enabledAtStep r) impl ev (holds (takenAtStep r)))"
definition "Saturated steps \<equiv> \<forall> r \<in> R. saturated r steps"

(*<*)(* Well-formed derivation trees *)(*>*)
coinductive wf where
  wf: "\<lbrakk>snd (root t) \<in> R; effStep (root t) (fimage (fst o root) (cont t));
    \<And>t'. t' |\<in>| cont t \<Longrightarrow> wf t'\<rbrakk> \<Longrightarrow> wf t"


(*<*)(* Escape paths *)(*>*)
coinductive epath where
  epath: "\<lbrakk>snd (shd steps) \<in> R; fst (shd (stl steps)) |\<in>| sl; effStep (shd steps) sl;
    epath (stl steps)\<rbrakk> \<Longrightarrow> epath steps"

lemma wf_ipath_epath:
  assumes "wf t" "ipath t steps"
  shows "epath steps"
proof -
  have *: "\<And>t st. ipath t st \<Longrightarrow> root t = shd st" by (auto elim: ipath.cases)
  show ?thesis using assms
  proof (coinduction arbitrary: t steps)
    case epath
    then show ?case by (cases rule: wf.cases[case_product ipath.cases]) (metis * o_apply fimageI)
  qed
qed

definition "fair rs \<equiv> sset rs \<subseteq> R \<and> (\<forall> r \<in> R. alw (ev (holds ((=) r))) rs)"

lemma fair_stl: "fair rs \<Longrightarrow> fair (stl rs)"
  unfolding fair_def by (metis alw.simps subsetD stl_sset subsetI)

lemma sdrop_fair: "fair rs \<Longrightarrow> fair (sdrop m rs)"
  using alw_sdrop unfolding fair_def by (metis alw.coinduct alw_nxt fair_def fair_stl)


section\<open>A Fair Enumeration of the Rules\<close>

(*<*)(* The fair enumeration of rules *)(*>*)
definition "fenum \<equiv> flat (smap (\<lambda>n. stake n rules) (fromN 1))"

lemma sset_fenum: "sset fenum = R"
  unfolding fenum_def by (subst sset_flat)
   (auto simp: stream.set_map in_set_conv_nth sset_range[of rules],
     metis atLeast_Suc_greaterThan greaterThan_0 lessI range_eqI stake_nth)

lemma fair_fenum: "fair fenum"
proof -
  { fix r assume "r \<in> R"
    then obtain m where r: "r = rules !! m" unfolding sset_range by blast
    { fix n :: nat and rs let ?fenum = "\<lambda>n. flat (smap (\<lambda>n. stake n rules) (fromN n))"
      assume "n > 0"
      hence "alw (ev (holds ((=) r))) (rs @- ?fenum n)"
      proof (coinduction arbitrary: n rs)
        case alw
        show ?case
        proof (rule exI[of _ "rs @- ?fenum n"], safe)
          show "\<exists>n' rs'. stl (rs @- ?fenum n) = rs' @- ?fenum n' \<and> n' > 0"
          proof(cases rs)
            case Nil thus ?thesis unfolding alw by (intro exI) auto
          qed (auto simp: alw intro: exI[of _ n])
        next
          show "ev (holds ((=) r)) (rs @- flat (smap (\<lambda>n. stake n rules) (fromN n)))"
            using alw r unfolding ev_holds_sset
            by (cases "m < n") (force simp: stream.set_map in_set_conv_nth)+
        qed
     qed
    }
  }
  thus "fair fenum" unfolding fair_def sset_fenum
    by (metis fenum_def alw_shift le_less zero_less_one)
qed

definition "trim rs s = sdrop_while (\<lambda>r. Not (enabled r s)) rs"


(*<*)(* The fair tree associated to a stream of rules and a state *)(*>*)
primcorec mkTree where
  "root (mkTree rs s) = (s, (shd (trim rs s)))"
| "cont (mkTree rs s) = fimage (mkTree (stl (trim rs s))) (pickEff (shd (trim rs s)) s)"

(*<*)(* More efficient code equation for mkTree *)(*>*)
lemma mkTree_unfold[code]: "mkTree rs s =
  (case trim rs s of SCons r s' \<Rightarrow> Node (s, r) (fimage (mkTree s') (pickEff r s)))"
  by (subst mkTree.ctr) (simp split: stream.splits)

end

locale RuleSystem = RuleSystem_Defs eff rules
for eff :: "'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool" and rules :: "'rule stream" +
fixes S :: "'state set"
assumes eff_S: "\<And> s r sl s'. \<lbrakk>s \<in> S; r \<in> R; eff r s sl; s' |\<in>| sl\<rbrakk> \<Longrightarrow> s' \<in> S"
and enabled_R: "\<And> s. s \<in> S \<Longrightarrow> \<exists> r \<in> R. \<exists> sl. eff r s sl"
begin

(*<*)(* The minimum waiting time in a stream for the enabled rules in a given state: *)(*>*)
definition "minWait rs s \<equiv> LEAST n. enabled (shd (sdrop n rs)) s"

lemma trim_alt:
  assumes s: "s \<in> S" and rs: "fair rs"
  shows "trim rs s = sdrop (minWait rs s) rs"
proof (unfold trim_def minWait_def sdrop_simps, rule sdrop_while_sdrop_LEAST[unfolded o_def])
  from enabled_R[OF s] obtain r sl where r: "r \<in> R" and sl: "eff r s sl" by blast
  from bspec[OF conjunct2[OF rs[unfolded fair_def]] r] obtain m where "r = rs !! m"
    by atomize_elim (erule alw.cases, auto simp only: ev_holds_sset sset_range)
  with r sl show "\<exists>n. enabled (rs !! n) s" unfolding enabled_def by auto
qed

lemma minWait_ex:
  assumes s: "s \<in> S" and rs: "fair rs"
  shows "\<exists> n. enabled (shd (sdrop n rs)) s"
proof -
  obtain r where r: "r \<in> R" and e: "enabled r s" using enabled_R s unfolding enabled_def by blast
  then obtain n where "shd (sdrop n rs) = r" using sdrop_fair[OF rs]
    by (metis (full_types) alw_nxt holds.simps sdrop.simps(1) fair_def sdrop_wait)
  thus ?thesis using r e by auto
qed

lemma assumes "s \<in> S" and "fair rs"
  shows trim_in_R: "shd (trim rs s) \<in> R"
  and trim_enabled: "enabled (shd (trim rs s)) s"
  and trim_fair: "fair (trim rs s)"
  unfolding trim_alt[OF assms] minWait_def
  using LeastI_ex[OF minWait_ex[OF assms]] sdrop_fair[OF assms(2)]
    conjunct1[OF assms(2)[unfolded fair_def]] by simp_all (metis subsetD snth_sset)

lemma minWait_least: "\<lbrakk>enabled (shd (sdrop n rs)) s\<rbrakk> \<Longrightarrow> minWait rs s \<le> n"
  unfolding minWait_def by (intro Least_le conjI)

lemma in_cont_mkTree:
  assumes s: "s \<in> S" and rs: "fair rs" and t': "t' |\<in>| cont (mkTree rs s)"
  shows "\<exists> sl' s'. s' \<in> S \<and> eff (shd (trim rs s)) s sl' \<and>
                 s' |\<in>| sl' \<and> t' = mkTree (stl (trim rs s)) s'"
proof -
  define sl' where "sl' = pickEff (shd (trim rs s)) s"
  obtain s' where s': "s' |\<in>| sl'" and "t' = mkTree (stl (trim rs s)) s'"
    using t' unfolding sl'_def by auto
  moreover have 1: "enabled (shd (trim rs s)) s" using trim_enabled[OF s rs] .
  moreover with trim_in_R pickEff eff_S s rs s'[unfolded sl'_def] have "s' \<in> S" by blast
  ultimately show ?thesis unfolding sl'_def using pickEff by blast
qed

lemma ipath_mkTree_sdrop:
  assumes s: "s \<in> S" and rs: "fair rs" and i: "ipath (mkTree rs s) steps"
  shows "\<exists> n s'. s' \<in> S \<and> ipath (mkTree (sdrop n rs) s') (sdrop m steps)"
using s rs i proof (induct m arbitrary: steps rs)
  case (Suc m)
  then obtain n s' where s': "s' \<in> S"
    and ip: "ipath (mkTree (sdrop n rs) s') (sdrop m steps)" (is "ipath ?t _") by blast
  from ip obtain t' where r: "root ?t = shd (sdrop m steps)" and t': "t' |\<in>| cont ?t"
    and i: "ipath t' (sdrop (Suc m) steps)" by (cases, simp)
  from in_cont_mkTree[OF s' sdrop_fair[OF Suc.prems(2)] t'] obtain sl'' s'' where
    e: "eff (shd (trim (sdrop n rs) s')) s' sl''" and
    s'': "s'' |\<in>| sl''" and t'_def: "t' = mkTree (stl (trim (sdrop n rs) s')) s''" by blast
  have "shd (trim (sdrop n rs) s') \<in> R" by (metis sdrop_fair Suc.prems(2) trim_in_R s')
  thus ?case using i s'' e s' unfolding sdrop_stl t'_def sdrop_add add.commute[of n]
    trim_alt[OF s' sdrop_fair[OF Suc.prems(2)]]
    by (intro exI[of _ "minWait (sdrop n rs) s' + Suc n"] exI[of _ s'']) (simp add: eff_S)
qed (auto intro!: exI[of _ 0] exI[of _ s])

lemma wf_mkTree:
  assumes s: "s \<in> S" and "fair rs"
  shows "wf (mkTree rs s)"
using assms proof (coinduction arbitrary: rs s)
  case (wf rs s) let ?t = "mkTree rs s"
  have "snd (root ?t) \<in> R" using trim_in_R[OF wf] by simp
  moreover have "fst \<circ> root \<circ> mkTree (stl (trim rs s)) = id" by auto
  hence "effStep (root ?t) (fimage (fst \<circ> root) (cont ?t))"
    using trim_enabled[OF wf] by (simp add: pickEff)
  ultimately show ?case using fair_stl[OF trim_fair[OF wf]] in_cont_mkTree[OF wf]
    by (auto intro!: exI[of _ "stl (trim rs s)"])
qed


(*<*)(* The position of a rule in a rule stream *)(*>*)
definition "pos rs r \<equiv> LEAST n. shd (sdrop n rs) = r"

lemma pos: "\<lbrakk>fair rs; r \<in> R\<rbrakk> \<Longrightarrow> shd (sdrop (pos rs r) rs) = r"
  unfolding pos_def
  by (rule LeastI_ex) (metis (full_types) alw.cases fair_def holds.simps sdrop_wait)

lemma pos_least: "shd (sdrop n rs) = r \<Longrightarrow> pos rs r \<le> n"
  unfolding pos_def by (metis (full_types) Least_le)

lemma minWait_le_pos: "\<lbrakk>fair rs; r \<in> R; enabled r s\<rbrakk> \<Longrightarrow> minWait rs s \<le> pos rs r"
  by (auto simp del: sdrop_simps intro: minWait_least simp: pos)

lemma stake_pos_minWait:
  assumes rs: "fair rs" and m: "minWait rs s < pos rs r" and r: "r \<in> R" and s: "s \<in> S"
  shows "pos (stl (trim rs s)) r = pos rs r - Suc (minWait rs s)"
proof -
  have "pos rs r - Suc (minWait rs s) + minWait rs s = pos rs r - Suc 0" using m by auto
  moreover have "shd (stl (sdrop (pos rs r - Suc 0) rs)) = shd (sdrop (pos rs r) rs)"
    by (metis Suc_pred gr_implies_not0 m neq0_conv sdrop.simps(2) sdrop_stl)
  ultimately have "pos (stl (trim rs s)) r \<le> pos rs r - Suc (minWait rs s)"
    using pos[OF rs r] by (auto simp: add.commute trim_alt[OF s rs] intro: pos_least)
  moreover
  have "pos rs r \<le> pos (stl (trim rs s)) r + Suc (minWait rs s)"
    using pos[OF sdrop_fair[OF fair_stl[OF rs]] r, of "minWait rs s"]
    by (auto simp: trim_alt[OF s rs] add.commute intro: pos_least)
  hence "pos rs r - Suc (minWait rs s) \<le> pos (stl (trim rs s)) r" by linarith
  ultimately show ?thesis by simp
qed

lemma ipath_mkTree_ev:
  assumes s: "s \<in> S" and rs: "fair rs"
  and i: "ipath (mkTree rs s) steps" and r: "r \<in> R"
  and alw: "alw (holds (enabledAtStep r)) steps"
  shows "ev (holds (takenAtStep r)) steps"
using s rs i alw proof (induction "pos rs r" arbitrary: rs s steps rule: less_induct)
  case (less rs s steps) note s = \<open>s \<in> S\<close> and trim_def' = trim_alt[OF s \<open>fair rs\<close>]
  let ?t = "mkTree rs s"
  from less(4,3) s in_cont_mkTree obtain t' :: "('state, 'rule) step tree" and s' where
    rt: "root ?t = shd steps" and i: "ipath (mkTree (stl (trim rs s)) s') (stl steps)" and
    s': "s' \<in> S" by cases fast
  show ?case
  proof(cases "pos rs r = minWait rs s")
    case True
    with pos[OF less.prems(2) r] rt[symmetric] show ?thesis by (auto simp: trim_def' ev.base)
  next
    case False
    have e: "enabled r s" using less.prems(4) rt  by (subst (asm) alw_nxt, cases steps) auto
    with False r less.prems(2) have 2: "minWait rs s < pos rs r" using minWait_le_pos by force
    let ?m1 = "pos rs r - Suc (minWait rs s)"
    have "Suc ?m1 \<le> pos rs r" using 2 by auto
    moreover have "?m1 = pos (stl (trim rs s)) r" using e \<open>fair rs\<close> 2 r s
      by (auto intro: stake_pos_minWait[symmetric])
    moreover have "fair (stl (trim rs s))" "alw (holds (enabledAtStep r)) (stl steps)"
      using less.prems by (metis fair_stl trim_fair, metis alw.simps)
    ultimately show "?thesis" by (auto intro: ev.step[OF less.hyps[OF _ s' _ i]])
  qed
qed

section\<open>Persistent rules\<close>

definition
  "per r \<equiv>
    \<forall>s r1 sl' s'. s \<in> S \<and> enabled r s \<and> r1 \<in> R - {r} \<and> eff r1 s sl' \<and> s' |\<in>| sl' \<longrightarrow> enabled r s'"

lemma per_alw:
  assumes p: "per r" and e: "epath steps \<and> fst (shd steps) \<in> S"
  shows "alw (holds (enabledAtStep r) impl
    (holds (takenAtStep r) or nxt (holds (enabledAtStep r)))) steps"
using e proof coinduct
  case (alw steps)
  moreover
  { let ?s = "fst (shd steps)"  let ?r1 = "snd (shd steps)"
    let ?s' = "fst (shd (stl steps))"
    assume "?s \<in> S" and "enabled r ?s" and "?r1 \<noteq> r"
    moreover have "?r1 \<in> R" using alw by (auto elim: epath.cases)
    moreover obtain sl' where "eff ?r1 ?s sl' \<and> ?s' |\<in>| sl'" using alw by (auto elim: epath.cases)
    ultimately have "enabled r ?s'" using p unfolding per_def by blast
  }
  ultimately show ?case by (auto intro: eff_S elim: epath.cases)
qed

end \<comment> \<open>context RuleSystem\<close>


(*<*) (* Rule-persistent rule system *) (*>*)
locale PersistentRuleSystem = RuleSystem eff rules S
for eff :: "'rule \<Rightarrow> 'state \<Rightarrow> 'state fset \<Rightarrow> bool" and rules :: "'rule stream" and S +
assumes per: "\<And> r. r \<in> R \<Longrightarrow> per r"
begin

lemma ipath_mkTree_saturated:
  assumes s: "s \<in> S" and rs: "fair rs"
  and i: "ipath (mkTree rs s) steps" and r: "r \<in> R"
  shows "saturated r steps"
unfolding saturated_def using s rs i proof (coinduction arbitrary: rs s steps)
  case (alw rs s steps)
  show ?case
  proof (intro exI[of _ steps], safe)
    assume "holds (enabledAtStep r) steps"
    hence "alw (holds (enabledAtStep r)) steps \<or> ev (holds (takenAtStep r)) steps"
      by (rule variance[OF _ per_alw[OF per[OF r]]])
        (metis wf_ipath_epath wf_mkTree alw mkTree.simps(1) ipath.simps fst_conv)
    thus "ev (holds (takenAtStep r)) steps" by (metis ipath_mkTree_ev[OF alw r])
  next
    from alw show "\<exists>rs' s' steps'.
      stl steps = steps' \<and> s' \<in> S \<and> fair rs' \<and> ipath (mkTree rs' s') steps'"
      using ipath_mkTree_sdrop[where m=1, simplified] trim_in_R sdrop_fair by fast
  qed
qed

theorem ipath_mkTree_Saturated:
  assumes "s \<in> S" and "fair rs" and "ipath (mkTree rs s) steps"
  shows "Saturated steps"
  unfolding Saturated_def using ipath_mkTree_saturated[OF assms] by blast

theorem epath_completeness_Saturated:
  assumes "s \<in> S"
  shows
  "(\<exists> t. fst (root t) = s \<and> wf t \<and> tfinite t) \<or>
   (\<exists> steps. fst (shd steps) = s \<and> epath steps \<and> Saturated steps)" (is "?A \<or> ?B")
proof -
  { assume "\<not> ?A"
    with assms have "\<not> tfinite (mkTree fenum s)" using wf_mkTree fair_fenum by auto
    then obtain steps where "ipath (mkTree fenum s) steps" using Konig by blast
    with assms have "fst (shd steps) = s \<and> epath steps \<and> Saturated steps"
      by (metis wf_ipath_epath ipath.simps ipath_mkTree_Saturated
        wf_mkTree fair_fenum mkTree.simps(1) fst_conv)
    hence ?B by blast
  }
  thus ?thesis by blast
qed


end \<comment> \<open>context PersistentRuleSystem\<close>



section\<open>Code generation\<close>

(* Here we assume a deterministic effect eff': *)

locale RuleSystem_Code =
fixes eff' :: "'rule \<Rightarrow> 'state \<Rightarrow> 'state fset option"
and rules :: "'rule stream" \<comment> \<open>countably many rules\<close>
begin

definition "eff r s sl \<equiv> eff' r s = Some sl"

end (* context RuleSystem_Code *)

definition [code del]: "effG eff' r s sl \<equiv> RuleSystem_Code.eff eff' r s sl"

sublocale RuleSystem_Code < RuleSystem_Defs
  where eff = "effG eff'" and rules = rules .

context RuleSystem_Code
begin

lemma enabled_eff': "enabled r s \<longleftrightarrow> eff' r s \<noteq> None"
unfolding enabled_def effG_def eff_def by auto

lemma pickEff_the[code]: "pickEff r s = the (eff' r s)"
unfolding pickEff_def enabled_def effG_def eff_def by auto

lemmas [code_unfold] = trim_def enabled_eff' pickEff_the

(*<*)
end (* context RuleSystem_Code *)
(*>*)

setup Locale_Code.open_block
interpretation i: RuleSystem_Code eff' rules for eff' and rules .
declare [[lc_delete "RuleSystem_Defs.mkTree (effG ?eff')"]]
declare [[lc_delete RuleSystem_Defs.trim]]
declare [[lc_delete RuleSystem_Defs.enabled]]
declare [[lc_delete RuleSystem_Defs.pickEff]]
declare [[lc_add "RuleSystem_Defs.mkTree (effG ?eff')" i.mkTree_unfold]]
setup Locale_Code.close_block

code_printing
  constant the \<rightharpoonup> (Haskell) "fromJust"
| constant Option.is_none \<rightharpoonup> (Haskell) "isNothing"

export_code mkTree_effG_uu in Haskell module_name Tree (*file "."*)

(*<*)
end
(*>*)
