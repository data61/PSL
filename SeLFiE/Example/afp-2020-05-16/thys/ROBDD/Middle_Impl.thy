section\<open>Functional interpretation for the abstract implementation\<close>
theory Middle_Impl
imports Abstract_Impl Pointer_Map
begin

text\<open>For the lack of a better name, the suffix mi stands for middle-implementation. 
This relects that this ``implementation'' is neither entirely abstract,
nor has it been made fully concrete: the data structures are decided, but not their implementations.\<close>

record bdd =
  dpm :: "(nat \<times> nat \<times> nat) pointermap"
  dcl :: "((nat \<times> nat \<times> nat),nat) map"

definition "emptymi \<equiv> \<lparr>dpm = empty_pointermap, dcl = Map.empty\<rparr>"

fun destrmi :: "nat \<Rightarrow> bdd \<Rightarrow> (nat, nat) IFEXD" where
"destrmi 0 bdd = FD" |
"destrmi (Suc 0) bdd = TD" |
"destrmi (Suc (Suc n)) bdd = (case pm_pth (dpm bdd) n of (v, t, e) \<Rightarrow> IFD v t e)"
fun tmi where "tmi bdd = (1, bdd)"
fun fmi where "fmi bdd = (0, bdd)"
fun ifmi :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> (nat \<times> bdd)" where
"ifmi v t e bdd = (if t = e 
  then (t, bdd) 
  else (let (r,pm) = pointermap_getmk (v, t, e) (dpm bdd) in 
  (Suc (Suc r), dpm_update (const pm) bdd)))"

fun Rmi_g :: "nat \<Rightarrow> nat ifex \<Rightarrow> bdd \<Rightarrow> bool" where
"Rmi_g 0 Falseif bdd = True" |
"Rmi_g (Suc 0) Trueif bdd = True" |
"Rmi_g (Suc (Suc n)) (IF v t e) bdd = (pointermap_p_valid n (dpm bdd)
  \<and> (case pm_pth (dpm bdd) n of (nv, nt, ne) \<Rightarrow> nv = v \<and> Rmi_g nt t bdd \<and> Rmi_g ne e bdd))" |
"Rmi_g _ _ _ = False"

definition "Rmi s \<equiv> {(a,b)|a b. Rmi_g a b s}"

interpretation mi_pre: bdd_impl_cmp_pre Rmi by -

definition "bdd_node_valid bdd n \<equiv> n \<in> Domain (Rmi bdd)"
lemma [simp]:
  "bdd_node_valid bdd 0"
  "bdd_node_valid bdd (Suc 0)"
  apply(simp_all add: bdd_node_valid_def Rmi_def)
   using Rmi_g.simps(1,2) apply blast+
  done

definition "ifexd_valid bdd e \<equiv> (case e of IFD _ t e \<Rightarrow> bdd_node_valid bdd t \<and> bdd_node_valid bdd e | _ \<Rightarrow> True)"

definition "bdd_sane bdd \<equiv> pointermap_sane (dpm bdd) \<and> mi_pre.map_invar_impl (dcl bdd) bdd"

lemma [simp,intro!]: "bdd_sane emptymi" 
  unfolding emptymi_def bdd_sane_def bdd.simps 
by(simp add: mi_pre.map_invar_impl_def)

lemma prod_split3: "P (case p of (x, xa, xaa) \<Rightarrow> f x xa xaa) = (\<forall>x1 x2 x3. p = (x1, x2, x3) \<longrightarrow> P (f x1 x2 x3))"
by(simp split: prod.splits)

lemma IfI: "(c \<Longrightarrow> P x) \<Longrightarrow> (\<not>c \<Longrightarrow> P y) \<Longrightarrow> P (if c then x else y)" by simp
lemma fstsndI: "x = (a,b) \<Longrightarrow> fst x = a \<and> snd x = b" by simp
thm nat.split
lemma Rmi_g_2_split: "P (Rmi_g n x m) =
  ((x = Falseif \<longrightarrow> P (Rmi_g n x m)) \<and>
  (x = Trueif \<longrightarrow> P (Rmi_g n x m)) \<and>
  (\<forall>vs ts es. x = IF vs ts es \<longrightarrow> P (Rmi_g n x m)))"
by(cases x;simp)

lemma rmigeq: "Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 = ni2 \<Longrightarrow> n1 = n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct, goal_cases)
  case (3 n v t e bdd n2 ni2) note goal3 = 3
  note 1 = goal3(1,2)
  have 2: "Rmi_g (fst (snd (pm_pth (dpm bdd) n))) t bdd" "Rmi_g (snd (snd (pm_pth (dpm bdd) n))) e bdd" using goal3(3) by(clarsimp)+
  note mIH = 1(1)[OF _ _ 2(1) _ refl] 1(2)[OF _ _ 2(2) _ refl]
  obtain v2 t2 e2 where v2: "n2 = IF v2 t2 e2" using Rmi_g.simps(4,6) goal3(3-5) by(cases n2) blast+
  thus ?case using goal3(3-4) by(clarsimp simp add: v2 goal3(5)[symmetric] mIH)
qed (rename_tac n2 ni2, (case_tac n2; clarsimp))+

lemma rmigneq: "bdd_sane s \<Longrightarrow> Rmi_g ni1 n1 s \<Longrightarrow> Rmi_g ni2 n2 s \<Longrightarrow> ni1 \<noteq> ni2 \<Longrightarrow> n1 \<noteq> n2"
proof(induction ni1 n1 s arbitrary: n2 ni2 rule: Rmi_g.induct, goal_cases)
  case 1 thus ?case by (metis Rmi_g.simps(6) old.nat.exhaust)
next
  case 2 thus ?case by (metis Rmi_g.simps(4,8) old.nat.exhaust)
next
  case (3 n v t e bdd n2 ni2) note goal3 = 3
  let ?bddpth = "pm_pth (dpm bdd)"
  note 1 = goal3(1,2)[OF prod.collapse prod.collapse]
  have 2: "Rmi_g (fst (snd (?bddpth n))) t bdd" "Rmi_g (snd (snd (?bddpth n))) e bdd" using goal3(4) by(clarsimp)+
  note mIH = 1(1)[OF goal3(3) 2(1)] 1(2)[OF goal3(3) 2(2)]
  show ?case proof(cases "0 < ni2", case_tac "1 < ni2")
    case False
    hence e: "ni2 = 0" by simp
    with goal3(5) have "n2 = Falseif" using rmigeq by auto (* honestly, I'm puzzled how this works\<dots> *)
    thus ?thesis by simp
  next
    case True moreover assume 3: "\<not> 1 < ni2"
    ultimately have "ni2 = 1" by simp
    with goal3(5) have "n2 = Trueif" using rmigeq by auto
    thus ?thesis by simp
  next
    assume 3: "1 < ni2"
    then obtain ni2s where [simp]: "ni2 = Suc (Suc ni2s)" unfolding One_nat_def using less_imp_Suc_add by blast
    obtain v2 t2 e2 where v2[simp]: "n2 = IF v2 t2 e2" using goal3(5) by(cases "(ni2, n2, bdd)" rule: Rmi_g.cases) clarsimp+
    have 4: "Rmi_g (fst (snd (?bddpth ni2s))) t2 bdd" "Rmi_g (snd (snd (?bddpth ni2s))) e2 bdd" using goal3(5) by clarsimp+
    show ?case unfolding v2
    proof(cases "fst (snd (?bddpth n)) = fst (snd (?bddpth ni2s))",
      case_tac "snd (snd (?bddpth n)) = snd (snd (?bddpth ni2s))",
      case_tac "v = v2")
      have ne: "ni2s \<noteq> n" using goal3(6) by simp
      have ib: "pointermap_p_valid n (dpm bdd)"  "pointermap_p_valid ni2s (dpm bdd)" using Rmi_g.simps(3) goal3(4,5) by simp_all
      assume goal1:
        "fst (snd (pm_pth (dpm bdd) n)) = fst (snd (pm_pth (dpm bdd) ni2s))"
        "snd (snd (pm_pth (dpm bdd) n)) = snd (snd (pm_pth (dpm bdd) ni2s))"
        "v = v2"
      hence "?bddpth n = ?bddpth ni2s" unfolding prod_eq_iff using goal3(4) goal3(5) by auto
      with goal3(3) ne have False unfolding bdd_sane_def using pth_eq_iff_index_eq[OF _ ib] by simp
      thus "IF v t e \<noteq> IF v2 t2 e2" ..
    qed (simp_all add: mIH(1)[OF 4(1)] mIH(2)[OF 4(2)])
  qed
qed simp_all

lemma ifmi_les_hlp: "pointermap_sane (dpm s) \<Longrightarrow> pointermap_getmk (v, ni1, ni2) (dpm s) = (x1, dpm s') \<Longrightarrow> Rmi_g nia n s \<Longrightarrow> Rmi_g nia n s'"
proof(induction nia n s rule: Rmi_g.induct, goal_cases)
  case (3 n v t e bdd) note goal3 = 3
  obtain x1a x2a where pth[simp]: "pm_pth (dpm bdd) n = (v, x1a, x2a)" using goal3(5) by force
  have pth'[simp]: "pm_pth (dpm s') n = (v, x1a, x2a)" unfolding pth[symmetric] using goal3(4,5) by (meson Rmi_g.simps(3) pointermap_p_pth_inv)
  note mIH = goal3(1,2)[OF pth[symmetric] refl goal3(3,4)]
  from goal3(5) show ?case 
    unfolding Rmi_g.simps
    using pointermap_p_valid_inv[OF _ goal3(4)] mIH
    by(simp split: prod.splits)
qed simp_all
lemma ifmi_les:
    assumes "bdd_sane s"
    assumes "ifmi v ni1 ni2 s = (ni, s')"
    shows "mi_pre.les s s'"
using assms
by(clarsimp simp: bdd_sane_def comp_def apfst_def map_prod_def mi_pre.les_def Rmi_def ifmi_les_hlp split: if_splits prod.splits)

lemma ifmi_notouch_dcl: "ifmi v ni1 ni2 s = (ni, s') \<Longrightarrow> dcl s' = dcl s"
  by(clarsimp split: if_splits prod.splits)

lemma ifmi_saneI: "bdd_sane s \<Longrightarrow> ifmi v ni1 ni2 s = (ni, s') \<Longrightarrow> bdd_sane s'"
  apply(subst bdd_sane_def)
  apply(rule conjI)
   apply(clarsimp simp: comp_def apfst_def map_prod_def bdd_sane_def split: if_splits option.splits split: prod.splits)
   apply(rule conjunct1[OF pointermap_sane_getmkD, of "dpm s" "(v, ni1, ni2)" _])
    apply(simp_all)[2]
  apply(frule (1) ifmi_les)
  apply(unfold bdd_sane_def, clarify)
  apply(rule mi_pre.map_invar_impl_les[rotated])
   apply assumption
  apply(drule ifmi_notouch_dcl)
  apply(simp)
done

lemma rmigif: "Rmi_g ni (IF v n1 n2) s \<Longrightarrow> \<exists>n. ni = Suc (Suc n)"
  apply(cases ni)
   apply(simp split: if_splits prod.splits)
  apply(rename_tac nis)
  apply(case_tac nis)
   apply(simp split: if_splits prod.splits)
  apply(simp split: if_splits prod.splits)
done

lemma in_lesI:
  assumes "mi_pre.les s s'"
    assumes "(ni1, n1) \<in> Rmi s"
    assumes "(ni2, n2) \<in> Rmi s"
    shows "(ni1, n1) \<in> Rmi s'" "(ni2, n2) \<in> Rmi s'"
by (meson assms mi_pre.les_def)+


lemma ifmi_modification_validI:
  assumes sane: "bdd_sane s"
  assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
  assumes vld: "bdd_node_valid s n"
  shows "bdd_node_valid s' n"
proof(cases "ni1 = ni2")
  case True with ifm vld show ?thesis by simp
next
  case False
  {
    fix b
    from ifm have "(n, b) \<in> Rmi s \<Longrightarrow> (n, b) \<in> Rmi s'" 
      by(induction n b _ rule: Rmi_g.induct) (auto dest: pointermap_p_pth_inv pointermap_p_valid_inv simp: apfst_def map_prod_def False Rmi_def split: prod.splits)
  }
  thus ?thesis
    using vld unfolding bdd_node_valid_def by blast
qed

definition "tmi' s \<equiv> do {oassert (bdd_sane s); Some (tmi s)}"
definition "fmi' s \<equiv> do {oassert (bdd_sane s); Some (fmi s)}"
definition "ifmi' v ni1 ni2 s \<equiv> do {oassert (bdd_sane s \<and> bdd_node_valid s ni1 \<and> bdd_node_valid s ni2); Some (ifmi v ni1 ni2 s)}"

lemma ifmi'_spec: "\<lbrakk>bdd_sane s; bdd_node_valid s ni1; bdd_node_valid s ni2\<rbrakk> \<Longrightarrow> ospec (ifmi' v ni1 ni2 s) (\<lambda>r. r = ifmi v ni1 ni2 s)"
  unfolding ifmi'_def by(simp split: Option.bind_splits)
lemma ifmi'_ifmi: "\<lbrakk>bdd_sane s; bdd_node_valid s ni1; bdd_node_valid s ni2\<rbrakk> \<Longrightarrow> ifmi' v ni1 ni2 s = Some (ifmi v ni1 ni2 s)"
  unfolding ifmi'_def by(simp split: Option.bind_splits)

definition "destrmi' ni s \<equiv> do {oassert (bdd_sane s \<and> bdd_node_valid s ni); Some (destrmi ni s)}"

lemma destrmi_someD: "destrmi' e bdd = Some x \<Longrightarrow> bdd_sane bdd \<and> bdd_node_valid bdd e"
by(simp add: destrmi'_def split: Option.bind_splits)

lemma Rmi_sv: 
  assumes "bdd_sane s" "(ni,n) \<in> Rmi s" "(ni',n') \<in> Rmi s"  
  shows "ni=ni' \<Longrightarrow> n=n'"
  and "ni\<noteq>ni' \<Longrightarrow> n\<noteq>n'"
  using assms
  apply safe
   apply (simp_all add: Rmi_def)
   using rmigeq apply simp
  apply (drule (3) rmigneq)
  by clarify

lemma True_rep[simp]: "bdd_sane s \<Longrightarrow> (ni,Trueif)\<in>Rmi s \<longleftrightarrow> ni=Suc 0"
  using Rmi_def Rmi_g.simps(2) Rmi_sv(2) by blast

lemma False_rep[simp]: "bdd_sane s \<Longrightarrow> (ni,Falseif)\<in>Rmi s \<longleftrightarrow> ni=0"
  using Rmi_def Rmi_g.simps(1) Rmi_sv(2) by blast

definition "updS s x r = dcl_update (\<lambda>m. m(x \<mapsto> r)) s"
thm Rmi_g.induct

lemma updS_dpm: "dpm (updS s x r) = dpm s"
  unfolding updS_def by simp

lemma updS_Rmi_g: "Rmi_g n i (updS s x r) = Rmi_g n i s"
  apply(induction n i s rule: Rmi_g.induct)
  apply(simp_all) unfolding updS_dpm by auto

lemma updS_Rmi: "Rmi (updS s x r) = Rmi s"
  unfolding Rmi_def updS_Rmi_g by blast


interpretation mi: bdd_impl_cmp bdd_sane Rmi tmi' fmi' ifmi' destrmi' dcl updS "(=)"
proof  -
  note s = mi_pre.les_def[simp] Rmi_def

  note [simp] = tmi'_def fmi'_def ifmi'_def destrmi'_def apfst_def map_prod_def

  show "bdd_impl_cmp bdd_sane Rmi tmi' fmi' ifmi' destrmi' dcl updS (=)"
  proof(unfold_locales, goal_cases)
    case 1 thus ?case by(clarsimp split: if_splits simp: Rmi_def)
  next case 2 thus ?case by(clarsimp split: if_splits simp: Rmi_def)
  next case (3 s ni1 n1 ni2 n2 v) note goal3 = 3
    note [simp] = Rmi_sv[OF this]
    have e: "n1 = n2 \<Longrightarrow> ni1 = ni2" by(rule ccontr) simp
    obtain ni s' where[simp]: "(ifmi' v ni1 ni2 s) = Some (ni, s')"
      unfolding ifmi'_def bdd_node_valid_def using goal3 by(simp add: DomainI del: ifmi.simps) fastforce
    hence ifm: "ifmi v ni1 ni2 s = (ni, s')" 
      using goal3 unfolding ifmi'_def bdd_node_valid_def  
      by(simp add: DomainI)
    have ifmi'_ospec: "\<And>P. ospec (ifmi' v ni1 ni2 s) P \<longleftrightarrow> P (ifmi v ni1 ni2 s)" by(simp del: ifmi'_def ifmi.simps add: ifm)
    from goal3 show ?case
      unfolding ifmi'_ospec
      apply(split prod.splits; clarify)
      apply(rule conjI)
      (* for the first thing, we don't have a helper lemma *)
      apply(clarsimp simp: Rmi_def IFC_def bdd_sane_def ifmi_les_hlp pointermap_sane_getmkD pointermap_update_pthI split: if_splits prod.splits)
      (* for the rest, we do *)
      using ifmi_les[OF \<open>bdd_sane s\<close> ifm] ifmi_saneI[OF \<open>bdd_sane s\<close> ifm] ifm apply(simp)
    done
  next case 4 thus ?case 
    apply (clarsimp split: Option.bind_splits if_splits)
    done
  next case 5 thus ?case by(clarsimp split: if_splits)
  next case 6 thus ?case 
    apply (clarsimp simp add: bdd_node_valid_def split: Option.bind_splits if_splits)
    apply (auto simp: Rmi_def elim: Rmi_g.elims)
    done
  next
    case 7 thus ?case using Rmi_sv by blast
  next
    case 8 thus ?case using Rmi_sv by blast
  next
    case 9 thus ?case unfolding bdd_sane_def by simp
  next
    case 10 thus ?case unfolding bdd_sane_def mi_pre.map_invar_impl_def using updS_Rmi
       by(clarsimp simp add: updS_def simp del: ifex_ite_opt.simps) blast
  next
    case 11 thus ?case using updS_Rmi by auto
qed
qed

lemma p_valid_RmiI: "(Suc (Suc na), b) \<in> Rmi bdd \<Longrightarrow> pointermap_p_valid na (dpm bdd)"
  unfolding Rmi_def by(cases b) (auto)
lemma n_valid_RmiI: "(na, b) \<in> Rmi bdd \<Longrightarrow> bdd_node_valid bdd na"
  unfolding bdd_node_valid_def
  by(intro DomainI, assumption)
lemma n_valid_Rmi_alt: "bdd_node_valid bdd na \<longleftrightarrow> (\<exists>b. (na, b) \<in> Rmi bdd)"
  unfolding bdd_node_valid_def
  by auto

  
lemma ifmi_result_validI:
  assumes sane: "bdd_sane s"
  assumes vld: "bdd_node_valid s ni1" "bdd_node_valid s ni2"
  assumes ifm: "ifmi v ni1 ni2 s = (ni, s')"
  shows "bdd_node_valid s' ni"
proof -
  from vld obtain n1 n2 where "(ni1, n1) \<in> Rmi s" "(ni2, n2) \<in> Rmi s" unfolding bdd_node_valid_def by blast
  note mi.IFimpl_rule[OF sane this]
  note this[unfolded ifmi'_ifmi[OF sane vld] ospec.simps, of v, unfolded ifm, unfolded prod.simps]
  thus ?thesis unfolding bdd_node_valid_def by blast
qed

end
