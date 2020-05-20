(*  Title:       variants/a_norreqid/Fresher.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
*)

section "Quality relations between routes"

theory A_Fresher
imports A_Aodv_Data
begin

subsection "Net sequence numbers"

subsubsection "On individual routes"

definition
  nsqn\<^sub>r :: "r \<Rightarrow> sqn"
where
  "nsqn\<^sub>r r \<equiv> if \<pi>\<^sub>4(r) = val \<or> \<pi>\<^sub>2(r) = 0 then \<pi>\<^sub>2(r) else (\<pi>\<^sub>2(r) - 1)"

lemma nsqnr_def':
  "nsqn\<^sub>r r = (if \<pi>\<^sub>4(r) = inv then \<pi>\<^sub>2(r) - 1 else \<pi>\<^sub>2(r))"
  unfolding nsqn\<^sub>r_def by simp

lemma nsqn\<^sub>r_zero [simp]:
  "\<And>dsn dsk flag hops nhip pre. nsqn\<^sub>r (0, dsk, flag, hops, nhip, pre) = 0"
  unfolding nsqn\<^sub>r_def by clarsimp

lemma nsqn\<^sub>r_val [simp]:
  "\<And>dsn dsk hops nhip pre. nsqn\<^sub>r (dsn, dsk, val, hops, nhip, pre) = dsn"
  unfolding nsqn\<^sub>r_def by clarsimp

lemma nsqn\<^sub>r_inv [simp]:
  "\<And>dsn dsk hops nhip pre. nsqn\<^sub>r (dsn, dsk, inv, hops, nhip, pre) = dsn - 1"
  unfolding nsqn\<^sub>r_def by clarsimp

lemma nsqn\<^sub>r_lte_dsn [simp]:
  "\<And>dsn dsk flag hops nhip pre. nsqn\<^sub>r (dsn, dsk, flag, hops, nhip, pre) \<le> dsn"
  unfolding nsqn\<^sub>r_def by clarsimp

subsubsection "On routes in routing tables"

definition
  nsqn :: "rt \<Rightarrow> ip \<Rightarrow> sqn"
where
  "nsqn \<equiv> \<lambda>rt dip. case \<sigma>\<^bsub>route\<^esub>(rt, dip) of None \<Rightarrow> 0 | Some r \<Rightarrow> nsqn\<^sub>r(r)"

lemma nsqn_sqn_def:
  "\<And>rt dip. nsqn rt dip = (if flag rt dip = Some val \<or> sqn rt dip = 0
                            then sqn rt dip else sqn rt dip - 1)"
  unfolding nsqn_def sqn_def by (clarsimp split: option.split)

lemma not_in_kD_nsqn [simp]:
  assumes "dip \<notin> kD(rt)"
  shows "nsqn rt dip = 0"
  using assms unfolding nsqn_def by simp

lemma kD_nsqn:
  assumes "dip \<in> kD(rt)"
    shows "nsqn rt dip = nsqn\<^sub>r(the (\<sigma>\<^bsub>route\<^esub>(rt, dip)))"
  using assms [THEN kD_Some] unfolding nsqn_def by clarsimp

lemma nsqnr_r_flag_pred [simp, intro]:
    fixes dsn dsk flag hops nhip pre
  assumes "P (nsqn\<^sub>r (dsn, dsk, val, hops, nhip, pre))"
      and "P (nsqn\<^sub>r (dsn, dsk, inv, hops, nhip, pre))"
    shows "P (nsqn\<^sub>r (dsn, dsk, flag, hops, nhip, pre))"
  using assms by (cases flag) auto

lemma nsqn\<^sub>r_addpreRT_inv [simp]:
  "\<And>rt dip npre dip'. dip \<in> kD(rt) \<Longrightarrow>
   nsqn\<^sub>r (the (the (addpreRT rt dip npre) dip')) = nsqn\<^sub>r (the (rt dip'))"
  unfolding addpreRT_def nsqn\<^sub>r_def
  by (frule kD_Some) (clarsimp split: option.split)

lemma sqn_nsqn:
  "\<And>rt dip. sqn rt dip - 1 \<le> nsqn rt dip"
  unfolding sqn_def nsqn_def by (clarsimp split: option.split)

lemma nsqn_sqn: "nsqn rt dip \<le> sqn rt dip"
  unfolding sqn_def nsqn_def by (cases "rt dip") auto

lemma val_nsqn_sqn [elim, simp]:
  assumes "ip\<in>kD(rt)"
      and "the (flag rt ip) = val"
    shows "nsqn rt ip = sqn rt ip"
  using assms unfolding nsqn_sqn_def by auto

lemma vD_nsqn_sqn [elim, simp]:
  assumes "ip\<in>vD(rt)"
    shows "nsqn rt ip = sqn rt ip"
  proof -
    from \<open>ip\<in>vD(rt)\<close> have "ip\<in>kD(rt)"
                      and "the (flag rt ip) = val" by auto
    thus ?thesis ..
  qed

lemma inv_nsqn_sqn [elim, simp]:
  assumes "ip\<in>kD(rt)"
      and "the (flag rt ip) = inv"
    shows "nsqn rt ip = sqn rt ip - 1"
  using assms unfolding nsqn_sqn_def by auto

lemma iD_nsqn_sqn [elim, simp]:
  assumes "ip\<in>iD(rt)"
    shows "nsqn rt ip = sqn rt ip - 1"
  proof -
    from \<open>ip\<in>iD(rt)\<close> have "ip\<in>kD(rt)"
                      and "the (flag rt ip) = inv" by auto
    thus ?thesis ..
  qed

lemma nsqn_update_changed_kno_val [simp]: "\<And>rt ip dsn dsk hops nhip.
  rt \<noteq> update rt ip (dsn, kno, val, hops, nhip, {})
   \<Longrightarrow> nsqn (update rt ip (dsn, kno, val, hops, nhip, {})) ip = dsn"
  unfolding nsqn\<^sub>r_def update_def
  by (clarsimp simp: kD_nsqn split: option.split_asm option.split if_split_asm)
     (metis fun_upd_triv)

lemma nsqn_addpreRT_inv [simp]:
  "\<And>rt dip npre dip'. dip \<in> kD(rt) \<Longrightarrow>
   nsqn (the (addpreRT rt dip npre)) dip' = nsqn rt dip'"
  unfolding addpreRT_def nsqn_def nsqn\<^sub>r_def
  by (frule kD_Some) (clarsimp split: option.split)

lemma nsqn_update_other [simp]:
    fixes dsn dsk flag hops dip nhip pre rt ip
  assumes "dip \<noteq> ip"
    shows "nsqn (update rt ip (dsn, dsk, flag, hops, nhip, pre)) dip = nsqn rt dip"
    using assms unfolding nsqn_def
    by (clarsimp split: option.split)

lemma nsqn_invalidate_eq:
  assumes "dip \<in> kD(rt)"
      and "dests dip = Some rsn"
    shows "nsqn (invalidate rt dests) dip = rsn - 1"
  using assms
  proof -
    from assms obtain dsk hops nhip pre
      where "invalidate rt dests dip = Some (rsn, dsk, inv, hops, nhip, pre)"
      unfolding invalidate_def
      by auto
    moreover from \<open>dip \<in> kD(rt)\<close> have "dip \<in> kD(invalidate rt dests)" by simp
    ultimately show ?thesis
      using \<open>dests dip = Some rsn\<close> by simp
  qed

lemma nsqn_invalidate_other [simp]:
  assumes "dip\<in>kD(rt)"
      and "dip\<notin>dom dests"
    shows "nsqn (invalidate rt dests) dip = nsqn rt dip"
  using assms by (clarsimp simp add: kD_nsqn)

subsection "Comparing routes "

definition
  fresher :: "r \<Rightarrow> r \<Rightarrow> bool" ("(_/ \<sqsubseteq> _)"  [51, 51] 50)
where
  "fresher r r' \<equiv> ((nsqn\<^sub>r r < nsqn\<^sub>r r') \<or> (nsqn\<^sub>r r  = nsqn\<^sub>r r' \<and> \<pi>\<^sub>5(r) \<ge> \<pi>\<^sub>5(r')))"

lemma fresherI1 [intro]:
  assumes "nsqn\<^sub>r r < nsqn\<^sub>r r'"
    shows "r \<sqsubseteq> r'"
  unfolding fresher_def using assms by simp

lemma fresherI2 [intro]:
  assumes "nsqn\<^sub>r r = nsqn\<^sub>r r'"
      and "\<pi>\<^sub>5(r) \<ge> \<pi>\<^sub>5(r')"
    shows "r \<sqsubseteq> r'"
  unfolding fresher_def using assms by simp

lemma fresherI [intro]:
  assumes "(nsqn\<^sub>r r < nsqn\<^sub>r r') \<or> (nsqn\<^sub>r r  = nsqn\<^sub>r r' \<and> \<pi>\<^sub>5(r) \<ge> \<pi>\<^sub>5(r'))"
    shows "r \<sqsubseteq> r'"
  unfolding fresher_def using assms .

lemma fresherE [elim]:
  assumes "r \<sqsubseteq> r'"
      and "nsqn\<^sub>r r < nsqn\<^sub>r r' \<Longrightarrow> P r r'"
      and "nsqn\<^sub>r r  = nsqn\<^sub>r r' \<and> \<pi>\<^sub>5(r) \<ge> \<pi>\<^sub>5(r') \<Longrightarrow> P r r'"
    shows "P r r'"
  using assms unfolding fresher_def by auto

lemma fresher_refl [simp]: "r \<sqsubseteq> r"
  unfolding fresher_def by simp

lemma fresher_trans [elim, trans]:
  "\<lbrakk> x \<sqsubseteq> y; y \<sqsubseteq> z \<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  unfolding fresher_def by auto

lemma not_fresher_trans [elim, trans]:
  "\<lbrakk> \<not>(x \<sqsubseteq> y); \<not>(z \<sqsubseteq> x) \<rbrakk> \<Longrightarrow> \<not>(z \<sqsubseteq> y)"
  unfolding fresher_def by auto

lemma fresher_dsn_flag_hops_const [simp]:
  fixes dsn dsk dsk' flag hops nhip nhip' pre pre'
  shows "(dsn, dsk, flag, hops, nhip, pre) \<sqsubseteq> (dsn, dsk', flag, hops, nhip', pre')"
  unfolding fresher_def by (cases flag) simp_all

lemma addpre_fresher [simp]: "\<And>r npre. r \<sqsubseteq> (addpre r npre)"
  by clarsimp

subsection "Comparing routing tables "

definition
  rt_fresher :: "ip \<Rightarrow> rt \<Rightarrow> rt \<Rightarrow> bool"
where
  "rt_fresher \<equiv> \<lambda>dip rt rt'. (the (\<sigma>\<^bsub>route\<^esub>(rt, dip))) \<sqsubseteq> (the (\<sigma>\<^bsub>route\<^esub>(rt', dip)))"

abbreviation
   rt_fresher_syn :: "rt \<Rightarrow> ip \<Rightarrow> rt \<Rightarrow> bool" ("(_/ \<sqsubseteq>\<^bsub>_\<^esub> _)"  [51, 999, 51] 50)
where
  "rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2 \<equiv> rt_fresher i rt1 rt2"

lemma rt_fresher_def':
  "(rt\<^sub>1 \<sqsubseteq>\<^bsub>i\<^esub> rt\<^sub>2) = (nsqn\<^sub>r (the (rt\<^sub>1 i)) < nsqn\<^sub>r (the (rt\<^sub>2 i)) \<or>
                     nsqn\<^sub>r (the (rt\<^sub>1 i)) = nsqn\<^sub>r (the (rt\<^sub>2 i)) \<and> \<pi>\<^sub>5 (the (rt\<^sub>2 i)) \<le> \<pi>\<^sub>5 (the (rt\<^sub>1 i)))"
  unfolding rt_fresher_def fresher_def by (rule refl)

lemma single_rt_fresher [intro]:
  assumes "the (rt1 ip) \<sqsubseteq> the (rt2 ip)"
    shows "rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2"
  using assms unfolding rt_fresher_def .

lemma rt_fresher_single [intro]:
  assumes "rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2"
    shows "the (rt1 ip) \<sqsubseteq> the (rt2 ip)"
  using assms unfolding rt_fresher_def .

lemma rt_fresher_def2:
  assumes "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
    shows "(rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2) = (nsqn rt1 dip < nsqn rt2 dip
                               \<or> (nsqn rt1 dip = nsqn rt2 dip
                                   \<and> the (dhops rt1 dip) \<ge> the (dhops rt2 dip)))"
  using assms unfolding rt_fresher_def fresher_def by (simp add: kD_nsqn proj5_eq_dhops)

lemma rt_fresherI1 [intro]:
  assumes "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
      and "nsqn rt1 dip < nsqn rt2 dip"
    shows "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
  unfolding rt_fresher_def2 [OF assms(1-2)] using assms(3) by simp

lemma rt_fresherI2 [intro]:
  assumes "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
      and "nsqn rt1 dip = nsqn rt2 dip"
      and "the (dhops rt1 dip) \<ge> the (dhops rt2 dip)"
    shows "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
  unfolding rt_fresher_def2 [OF assms(1-2)] using assms(3-4) by simp

lemma rt_fresherE [elim]:
  assumes "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
      and "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
      and "\<lbrakk> nsqn rt1 dip < nsqn rt2 dip \<rbrakk> \<Longrightarrow> P rt1 rt2 dip"
      and "\<lbrakk> nsqn rt1 dip = nsqn rt2 dip;
             the (dhops rt1 dip) \<ge> the (dhops rt2 dip) \<rbrakk> \<Longrightarrow> P rt1 rt2 dip"
    shows "P rt1 rt2 dip"
  using assms(1) unfolding rt_fresher_def2 [OF assms(2-3)]
  using assms(4-5) by auto

lemma rt_fresher_refl [simp]: "rt \<sqsubseteq>\<^bsub>dip\<^esub> rt"
  unfolding rt_fresher_def by simp

lemma rt_fresher_trans [elim, trans]:
  assumes "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
      and "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt3"
    shows "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt3"
  using assms unfolding rt_fresher_def by auto

lemma rt_fresher_if_Some [intro!]:
  assumes "the (rt dip) \<sqsubseteq> r"
    shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> (\<lambda>ip. if ip = dip then Some r else rt ip)"
  using assms unfolding rt_fresher_def by simp

definition rt_fresh_as :: "ip \<Rightarrow> rt \<Rightarrow> rt \<Rightarrow> bool"
where
  "rt_fresh_as \<equiv> \<lambda>dip rt1 rt2. (rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2) \<and> (rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)"

abbreviation
   rt_fresh_as_syn :: "rt \<Rightarrow> ip \<Rightarrow> rt \<Rightarrow> bool" ("(_/ \<approx>\<^bsub>_\<^esub> _)"  [51, 999, 51] 50)
where
  "rt1 \<approx>\<^bsub>i\<^esub> rt2 \<equiv> rt_fresh_as i rt1 rt2"

lemma rt_fresh_as_refl [simp]: "\<And>rt dip. rt \<approx>\<^bsub>dip\<^esub> rt"
  unfolding rt_fresh_as_def by simp

lemma rt_fresh_as_trans [simp, intro, trans]:
  "\<And>rt1 rt2 rt3 dip. \<lbrakk> rt1 \<approx>\<^bsub>dip\<^esub> rt2; rt2 \<approx>\<^bsub>dip\<^esub> rt3 \<rbrakk> \<Longrightarrow> rt1 \<approx>\<^bsub>dip\<^esub> rt3"
  unfolding rt_fresh_as_def rt_fresher_def
  by (metis (mono_tags) fresher_trans)

lemma rt_fresh_asI [intro!]:
  assumes "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
      and "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1"
    shows "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
  using assms unfolding rt_fresh_as_def by simp

lemma rt_fresh_as_fresherI [intro]:
  assumes "dip\<in>kD(rt1)"
      and "dip\<in>kD(rt2)"
      and "the (rt1 dip) \<sqsubseteq> the (rt2 dip)"
      and "the (rt2 dip) \<sqsubseteq> the (rt1 dip)"
    shows "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
  using assms unfolding rt_fresh_as_def
  by (clarsimp dest!: single_rt_fresher)

lemma nsqn_rt_fresh_asI:
  assumes "dip \<in> kD(rt)"
      and "dip \<in> kD(rt')"
      and "nsqn rt dip = nsqn rt' dip"
      and "\<pi>\<^sub>5(the (rt dip)) = \<pi>\<^sub>5(the (rt' dip))"
    shows "rt \<approx>\<^bsub>dip\<^esub> rt'"
  proof
    from assms(1-2,4) have dhops': "the (dhops rt' dip) \<le> the (dhops rt dip)"
      by (simp add: proj5_eq_dhops)
    with assms(1-3) show "rt \<sqsubseteq>\<^bsub>dip\<^esub> rt'"
      by (rule rt_fresherI2)
  next
    from assms(1-2,4) have dhops: "the (dhops rt dip) \<le> the (dhops rt' dip)"
      by (simp add: proj5_eq_dhops)
    with assms(2,1) assms(3) [symmetric] show "rt' \<sqsubseteq>\<^bsub>dip\<^esub> rt"
      by (rule rt_fresherI2)
  qed

lemma rt_fresh_asE [elim]:
  assumes "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
      and "\<lbrakk> rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2; rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1 \<rbrakk> \<Longrightarrow> P rt1 rt2 dip"
    shows "P rt1 rt2 dip"
  using assms unfolding rt_fresh_as_def by simp

lemma rt_fresh_asD1 [dest]:
  assumes "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    shows "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
  using assms unfolding rt_fresh_as_def by simp

lemma rt_fresh_asD2 [dest]:
  assumes "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    shows "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1"
  using assms unfolding rt_fresh_as_def by simp

lemma rt_fresh_as_sym:
  assumes "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    shows "rt2 \<approx>\<^bsub>dip\<^esub> rt1"
  using assms unfolding rt_fresh_as_def by simp

lemma not_rt_fresh_asI1 [intro]:
  assumes "\<not> (rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2)"
    shows "\<not> (rt1 \<approx>\<^bsub>dip\<^esub> rt2)"
  proof
    assume "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    hence "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2" ..
    with \<open>\<not> (rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2)\<close> show False ..
  qed

lemma not_rt_fresh_asI2 [intro]:
  assumes "\<not> (rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)"
    shows "\<not> (rt1 \<approx>\<^bsub>dip\<^esub> rt2)"
  proof
    assume "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    hence "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1" ..
    with \<open>\<not> (rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)\<close> show False ..
  qed

lemma not_single_rt_fresher [elim]:
  assumes "\<not>(the (rt1 ip) \<sqsubseteq> the (rt2 ip))"
    shows "\<not>(rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2)"
  proof
    assume "rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2"
    hence "the (rt1 ip) \<sqsubseteq> the (rt2 ip)" ..
    with \<open>\<not>(the (rt1 ip) \<sqsubseteq> the (rt2 ip))\<close> show False ..
  qed

lemmas not_single_rt_fresh_asI1 [intro] =  not_rt_fresh_asI1 [OF not_single_rt_fresher]
lemmas not_single_rt_fresh_asI2 [intro] =  not_rt_fresh_asI2 [OF not_single_rt_fresher]

lemma not_rt_fresher_single [elim]:
  assumes "\<not>(rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2)"
    shows "\<not>(the (rt1 ip) \<sqsubseteq> the (rt2 ip))"
  proof
    assume "the (rt1 ip) \<sqsubseteq> the (rt2 ip)"
    hence "rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2" ..
    with \<open>\<not>(rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2)\<close> show False ..
  qed

lemma rt_fresh_as_nsqnr:
  assumes "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
      and "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
    shows "nsqn\<^sub>r (the (rt2 dip)) = nsqn\<^sub>r (the (rt1 dip))"
  using assms(3) unfolding rt_fresh_as_def
  by (auto simp: rt_fresher_def2 [OF \<open>dip \<in> kD(rt1)\<close> \<open>dip \<in> kD(rt2)\<close>]
                 rt_fresher_def2 [OF \<open>dip \<in> kD(rt2)\<close> \<open>dip \<in> kD(rt1)\<close>]
                 kD_nsqn [OF \<open>dip \<in> kD(rt1)\<close>]
                 kD_nsqn [OF \<open>dip \<in> kD(rt2)\<close>])

lemma rt_fresher_mapupd [intro!]:
  assumes "dip\<in>kD(rt)"
      and "the (rt dip) \<sqsubseteq> r"
    shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> rt(dip \<mapsto> r)"
  using assms unfolding rt_fresher_def by simp

lemma rt_fresher_map_update_other [intro!]:
  assumes "dip\<in>kD(rt)"
      and "dip \<noteq> ip"
    shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> rt(ip \<mapsto> r)"
  using assms unfolding rt_fresher_def by simp

lemma rt_fresher_update_other [simp]:
  assumes inkD: "dip\<in>kD(rt)"
     and "dip \<noteq> ip"
   shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> update rt ip r"
   using assms unfolding update_def
   by (clarsimp split: option.split) (fastforce)

theorem rt_fresher_update [simp]:
  assumes "dip\<in>kD(rt)"
      and "the (dhops rt dip) \<ge> 1"
      and "update_arg_wf r"
   shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> update rt ip r"
  proof (cases "dip = ip")
    assume "dip \<noteq> ip" with \<open>dip\<in>kD(rt)\<close> show ?thesis
      by (rule rt_fresher_update_other)
  next
    assume "dip = ip"

    from \<open>dip\<in>kD(rt)\<close> obtain dsn\<^sub>n dsk\<^sub>n f\<^sub>n hops\<^sub>n nhip\<^sub>n pre\<^sub>n
      where rtn [simp]: "the (rt dip) = (dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)"
      by (metis prod_cases6)
    with \<open>the (dhops rt dip) \<ge> 1\<close> and \<open>dip\<in>kD(rt)\<close> have "hops\<^sub>n \<ge> 1"
      by (metis proj5_eq_dhops projs(4))
    from \<open>dip\<in>kD(rt)\<close> rtn have [simp]: "sqn rt dip = dsn\<^sub>n"
                           and [simp]: "the (dhops rt dip) = hops\<^sub>n"
                           and [simp]: "the (flag rt dip) = f\<^sub>n"
      by (simp add: sqn_def proj5_eq_dhops [symmetric]
                            proj4_eq_flag [symmetric])+

    from \<open>update_arg_wf r\<close> have "(dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
                                  \<sqsubseteq> the ((update rt dip r) dip)"
      proof (rule wf_r_cases)
        fix nhip pre
        from \<open>hops\<^sub>n \<ge> 1\<close> have "\<And>pre'. (dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
                                        \<sqsubseteq> (dsn\<^sub>n, unk, val, Suc 0, nhip, pre')"
          unfolding fresher_def sqn_def by (cases f\<^sub>n) auto
        thus "(dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
               \<sqsubseteq> the (update rt dip (0, unk, val, Suc 0, nhip, pre) dip)"
          using \<open>dip\<in>kD(rt)\<close> by - (rule update_cases_kD, simp_all)
      next
        fix dsn :: sqn and hops nhip pre
        assume "0 < dsn"
        show "(dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
               \<sqsubseteq> the (update rt dip (dsn, kno, val, hops, nhip, pre) dip)"
        proof (rule update_cases_kD [OF _ \<open>dip\<in>kD(rt)\<close>], simp_all add: \<open>0 < dsn\<close>)
          assume "dsn\<^sub>n < dsn"
            thus "(dsn\<^sub>n, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
                   \<sqsubseteq> (dsn, kno, val, hops, nhip, pre \<union> pre\<^sub>n)"
              unfolding fresher_def by auto
        next
          assume "dsn\<^sub>n = dsn"
             and "hops < hops\<^sub>n"
            thus "(dsn, dsk\<^sub>n, f\<^sub>n, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
                   \<sqsubseteq> (dsn, kno, val, hops, nhip, pre \<union> pre\<^sub>n)"
              unfolding fresher_def nsqn\<^sub>r_def by simp
        next
          assume "dsn\<^sub>n = dsn"
            with \<open>0 < dsn\<close>
            show "(dsn, dsk\<^sub>n, inv, hops\<^sub>n, nhip\<^sub>n, pre\<^sub>n)
                   \<sqsubseteq> (dsn, kno, val, hops, nhip, pre \<union> pre\<^sub>n)"
              unfolding fresher_def by simp
        qed
      qed
    hence "rt \<sqsubseteq>\<^bsub>dip\<^esub> update rt dip r"
      by - (rule single_rt_fresher, simp)
    with \<open>dip = ip\<close> show ?thesis by simp
  qed

theorem rt_fresher_invalidate [simp]:
  assumes "dip\<in>kD(rt)"
      and indests: "\<forall>rip\<in>dom(dests). rip\<in>vD(rt) \<and> sqn rt rip < the (dests rip)"
    shows "rt \<sqsubseteq>\<^bsub>dip\<^esub> invalidate rt dests"
  proof (cases "dip\<in>dom(dests)")
    assume "dip\<notin>dom(dests)"
      thus ?thesis using \<open>dip\<in>kD(rt)\<close>
      by - (rule single_rt_fresher, simp)
  next
    assume "dip\<in>dom(dests)"
    moreover with indests have "dip\<in>vD(rt)"
                           and "sqn rt dip < the (dests dip)"
      by auto
    ultimately show ?thesis
      unfolding invalidate_def sqn_def
      by - (rule single_rt_fresher, auto simp: fresher_def)
  qed

lemma nsqn\<^sub>r_invalidate [simp]:
  assumes "dip\<in>kD(rt)"
      and "dip\<in>dom(dests)"
    shows "nsqn\<^sub>r (the (invalidate rt dests dip)) = the (dests dip) - 1"
  using assms unfolding invalidate_def by auto

lemma rt_fresh_as_inc_invalidate [simp]:
  assumes "dip\<in>kD(rt)"
      and "\<forall>rip\<in>dom(dests). rip\<in>vD(rt) \<and> the (dests rip) = inc (sqn rt rip)"
    shows "rt \<approx>\<^bsub>dip\<^esub> invalidate rt dests"
  proof (cases "dip\<in>dom(dests)")
    assume "dip\<notin>dom(dests)"
    with \<open>dip\<in>kD(rt)\<close> have "dip\<in>kD(invalidate rt dests)"
      by simp
    with \<open>dip\<in>kD(rt)\<close> show ?thesis
      by rule (simp_all add: \<open>dip\<notin>dom(dests)\<close>)
  next
    assume "dip\<in>dom(dests)"
    with assms(2) have "dip\<in>vD(rt)"
                  and "the (dests dip) = inc (sqn rt dip)" by auto
    from \<open>dip\<in>vD(rt)\<close> have "dip\<in>kD(rt)" by simp
    moreover then have "dip\<in>kD(invalidate rt dests)" by simp
    ultimately show ?thesis
    proof (rule nsqn_rt_fresh_asI)
      from \<open>dip\<in>vD(rt)\<close> have "nsqn rt dip = sqn rt dip" by simp
      also have "sqn rt dip = nsqn\<^sub>r (the (invalidate rt dests dip))"
      proof -
        from \<open>dip\<in>kD(rt)\<close> have "nsqn\<^sub>r (the (invalidate rt dests dip)) = the (dests dip) - 1"
          using \<open>dip\<in>dom(dests)\<close> by (rule nsqn\<^sub>r_invalidate)
        with \<open>the (dests dip) = inc (sqn rt dip)\<close>
          show "sqn rt dip = nsqn\<^sub>r (the (invalidate rt dests dip))" by simp
      qed
      also from \<open>dip\<in>kD(invalidate rt dests)\<close>
        have "nsqn\<^sub>r (the (invalidate rt dests dip)) = nsqn (invalidate rt dests) dip"
          by (simp add: kD_nsqn)
      finally show "nsqn rt dip = nsqn (invalidate rt dests) dip" .
    qed simp
  qed

lemmas rt_fresher_inc_invalidate [simp] = rt_fresh_as_inc_invalidate [THEN rt_fresh_asD1]

lemma rt_fresh_as_addpreRT [simp]:
  assumes "ip\<in>kD(rt)"
    shows "rt \<approx>\<^bsub>dip\<^esub> the (addpreRT rt ip npre)"
  using assms [THEN kD_Some] by (auto simp: addpreRT_def)

lemmas rt_fresher_addpreRT [simp] = rt_fresh_as_addpreRT [THEN rt_fresh_asD1]

subsection "Strictly comparing routing tables "

definition rt_strictly_fresher :: "ip \<Rightarrow> rt \<Rightarrow> rt \<Rightarrow> bool"
where
  "rt_strictly_fresher \<equiv> \<lambda>dip rt1 rt2. (rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2) \<and> \<not>(rt1 \<approx>\<^bsub>dip\<^esub> rt2)"

abbreviation
   rt_strictly_fresher_syn :: "rt \<Rightarrow> ip \<Rightarrow> rt \<Rightarrow> bool" ("(_/ \<sqsubset>\<^bsub>_\<^esub> _)"  [51, 999, 51] 50)
where
  "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2 \<equiv> rt_strictly_fresher i rt1 rt2"

lemma rt_strictly_fresher_def'':
  "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2 = ((rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2) \<and> \<not>(rt2 \<sqsubseteq>\<^bsub>i\<^esub> rt1))"
  unfolding rt_strictly_fresher_def rt_fresh_as_def by auto

lemma rt_strictly_fresherI' [intro]:
  assumes "rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2"
      and "\<not>(rt2 \<sqsubseteq>\<^bsub>i\<^esub> rt1)"
    shows "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2"
  using assms unfolding rt_strictly_fresher_def'' by simp

lemma rt_strictly_fresherE' [elim]:
  assumes "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2"
      and "\<lbrakk> rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2; \<not>(rt2 \<sqsubseteq>\<^bsub>i\<^esub> rt1) \<rbrakk> \<Longrightarrow> P rt1 rt2 i"
    shows "P rt1 rt2 i"
  using assms unfolding rt_strictly_fresher_def'' by simp

lemma rt_strictly_fresherI [intro]:
  assumes "rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2"
      and "\<not>(rt1 \<approx>\<^bsub>i\<^esub> rt2)"
    shows "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2"
  unfolding rt_strictly_fresher_def using assms ..

lemmas rt_strictly_fresher_singleI [elim] = rt_strictly_fresherI [OF single_rt_fresher]

lemma rt_strictly_fresherE [elim]:
  assumes "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2"
      and "\<lbrakk> rt1 \<sqsubseteq>\<^bsub>i\<^esub> rt2; \<not>(rt1 \<approx>\<^bsub>i\<^esub> rt2) \<rbrakk> \<Longrightarrow> P rt1 rt2 i"
    shows "P rt1 rt2 i"
  using assms(1) unfolding rt_strictly_fresher_def
  by rule (erule(1) assms(2))

lemma rt_strictly_fresher_def':
  "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2 =
     (nsqn\<^sub>r (the (rt1 i)) < nsqn\<^sub>r (the (rt2 i))
       \<or> (nsqn\<^sub>r (the (rt1 i)) = nsqn\<^sub>r (the (rt2 i)) \<and> \<pi>\<^sub>5(the (rt1 i)) > \<pi>\<^sub>5(the (rt2 i))))"
  unfolding rt_strictly_fresher_def'' rt_fresher_def fresher_def by auto

lemma rt_strictly_fresher_fresherD [dest]:
  assumes "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2"
    shows "the (rt1 dip) \<sqsubseteq> the (rt2 dip)"
  using assms unfolding rt_strictly_fresher_def rt_fresher_def by auto

lemma rt_strictly_fresher_not_fresh_asD [dest]:
  assumes "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2"
    shows "\<not> rt1 \<approx>\<^bsub>dip\<^esub> rt2"
  using assms unfolding rt_strictly_fresher_def by auto

lemma rt_strictly_fresher_trans [elim, trans]:
  assumes "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2"
      and "rt2 \<sqsubset>\<^bsub>dip\<^esub> rt3"
    shows "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3"
  using assms proof -
    from \<open>rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2\<close> obtain "the (rt1 dip) \<sqsubseteq> the (rt2 dip)" by auto
    also from \<open>rt2 \<sqsubset>\<^bsub>dip\<^esub> rt3\<close> obtain "the (rt2 dip) \<sqsubseteq> the (rt3 dip)" by auto
    finally have "the (rt1 dip) \<sqsubseteq> the (rt3 dip)" .

    moreover have "\<not> (rt1 \<approx>\<^bsub>dip\<^esub> rt3)"
    proof -    
      from \<open>rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2\<close> obtain "\<not>(the (rt2 dip) \<sqsubseteq> the (rt1 dip))" by auto
      also from \<open>rt2 \<sqsubset>\<^bsub>dip\<^esub> rt3\<close> obtain "\<not>(the (rt3 dip) \<sqsubseteq> the (rt2 dip))" by auto
      finally have "\<not>(the (rt3 dip) \<sqsubseteq> the (rt1 dip))" .
      thus ?thesis ..
    qed
    ultimately show "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3" ..
 qed

lemma rt_strictly_fresher_irefl [simp]: "\<not> (rt \<sqsubset>\<^bsub>dip\<^esub> rt)"
  unfolding rt_strictly_fresher_def
  by clarsimp

lemma rt_fresher_trans_rt_strictly_fresher [elim, trans]:
  assumes "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2"
      and "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt3"
    shows "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3"
  proof -
    from \<open>rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2\<close> have "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
                           and "\<not>(rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)"
      unfolding rt_strictly_fresher_def'' by auto
    from this(1) and \<open>rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt3\<close> have "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt3" ..

    moreover from \<open>\<not>(rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)\<close> have "\<not>(rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)"
      proof (rule contrapos_nn)
        assume "rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt1"
        with \<open>rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt3\<close> show "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1" ..
      qed

    ultimately show "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3"
      unfolding rt_strictly_fresher_def'' by auto
  qed

lemma rt_fresher_trans_rt_strictly_fresher' [elim, trans]:
  assumes "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2"
      and "rt2 \<sqsubset>\<^bsub>dip\<^esub> rt3"
    shows "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3"
  proof -
    from \<open>rt2 \<sqsubset>\<^bsub>dip\<^esub> rt3\<close> have "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt3"
                           and "\<not>(rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt2)"
      unfolding rt_strictly_fresher_def'' by auto
    from \<open>rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2\<close> and this(1) have "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt3" ..

    moreover from \<open>\<not>(rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt2)\<close> have "\<not>(rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt1)"
      proof (rule contrapos_nn)
        assume "rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt1"
        thus "rt3 \<sqsubseteq>\<^bsub>dip\<^esub> rt2" using \<open>rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2\<close> ..
      qed

    ultimately show "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt3"
      unfolding rt_strictly_fresher_def'' by auto
  qed

lemma rt_fresher_imp_nsqn_le:
  assumes "rt1 \<sqsubseteq>\<^bsub>ip\<^esub> rt2"
      and "ip \<in> kD rt1"
      and "ip \<in> kD rt2"
    shows "nsqn rt1 ip \<le> nsqn rt2 ip"
  using assms(1)
  by (auto simp add: rt_fresher_def2 [OF assms(2-3)])

lemma rt_strictly_fresher_ltI [intro]:
  assumes "dip \<in> kD(rt1)"
      and "dip \<in> kD(rt2)"
      and "nsqn rt1 dip < nsqn rt2 dip"
    shows "rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2"
  proof
    from assms show "rt1 \<sqsubseteq>\<^bsub>dip\<^esub> rt2" ..
  next
    show "\<not>(rt1 \<approx>\<^bsub>dip\<^esub> rt2)"
    proof
      assume "rt1 \<approx>\<^bsub>dip\<^esub> rt2"
      hence "rt2 \<sqsubseteq>\<^bsub>dip\<^esub> rt1" ..
      hence "nsqn rt2 dip \<le> nsqn rt1 dip"
        using \<open>dip \<in> kD(rt2)\<close> \<open>dip \<in> kD(rt1)\<close>
        by (rule rt_fresher_imp_nsqn_le)
      with \<open>nsqn rt1 dip < nsqn rt2 dip\<close> show "False"
        by simp
    qed
  qed

lemma rt_strictly_fresher_eqI [intro]:
  assumes "i\<in>kD(rt1)"
      and "i\<in>kD(rt2)"
      and "nsqn rt1 i = nsqn rt2 i"
      and "\<pi>\<^sub>5(the (rt2 i)) < \<pi>\<^sub>5(the (rt1 i))"
    shows "rt1 \<sqsubset>\<^bsub>i\<^esub> rt2"
  using assms unfolding rt_strictly_fresher_def' by (auto simp add: kD_nsqn)

lemma invalidate_rtsf_left [simp]:
  "\<And>dests dip rt rt'. dests dip = None \<Longrightarrow> (invalidate rt dests \<sqsubset>\<^bsub>dip\<^esub> rt') = (rt \<sqsubset>\<^bsub>dip\<^esub> rt')"
  unfolding invalidate_def rt_strictly_fresher_def'
  by (rule iffI) (auto split: option.split_asm)

lemma vD_invalidate_rt_strictly_fresher [simp]:
  assumes "dip \<in> vD(invalidate rt1 dests)"
    shows "(invalidate rt1 dests \<sqsubset>\<^bsub>dip\<^esub> rt2) = (rt1 \<sqsubset>\<^bsub>dip\<^esub> rt2)"
  proof (cases "dip \<in> dom(dests)")
    assume "dip \<in> dom(dests)"
    hence "dip \<notin> vD(invalidate rt1 dests)"
      unfolding invalidate_def vD_def
      by clarsimp (metis assms option.simps(3) vD_invalidate_vD_not_dests)
    with \<open>dip \<in> vD(invalidate rt1 dests)\<close> show ?thesis by simp
  next
    assume "dip \<notin> dom(dests)"
    hence "dests dip = None" by auto
    moreover with \<open>dip \<in> vD(invalidate rt1 dests)\<close> have "dip \<in> vD(rt1)"
      unfolding invalidate_def vD_def
      by clarsimp (metis (hide_lams, no_types) assms vD_Some vD_invalidate_vD_not_dests)
    ultimately show ?thesis
      unfolding invalidate_def rt_strictly_fresher_def' by auto
  qed

lemma rt_strictly_fresher_update_other [elim!]:
  "\<And>dip ip rt r rt'. \<lbrakk> dip \<noteq> ip; rt \<sqsubset>\<^bsub>dip\<^esub> rt' \<rbrakk> \<Longrightarrow> update rt ip r \<sqsubset>\<^bsub>dip\<^esub> rt'"
  unfolding rt_strictly_fresher_def' by clarsimp

lemma addpreRT_strictly_fresher [simp]:
  assumes "dip \<in> kD(rt)"
    shows "(the (addpreRT rt dip npre) \<sqsubset>\<^bsub>ip\<^esub> rt2) = (rt \<sqsubset>\<^bsub>ip\<^esub> rt2)"
  using assms unfolding rt_strictly_fresher_def' by clarsimp

lemma lt_sqn_imp_update_strictly_fresher:
  assumes "dip \<in> vD (rt2 nhip)"
      and  *: "osn < sqn (rt2 nhip) dip"
      and **: "rt \<noteq> update rt dip (osn, kno, val, hops, nhip, {})"
    shows "update rt dip (osn, kno, val, hops, nhip, {}) \<sqsubset>\<^bsub>dip\<^esub> rt2 nhip"
  unfolding rt_strictly_fresher_def'
  proof (rule disjI1)
    from ** have "nsqn (update rt dip (osn, kno, val, hops, nhip, {})) dip = osn"
      by (rule nsqn_update_changed_kno_val)
    with \<open>dip\<in>vD(rt2 nhip)\<close>
      have "nsqn\<^sub>r (the (update rt dip (osn, kno, val, hops, nhip, {}) dip)) = osn"
        by (simp add: kD_nsqn)
    also have "osn < sqn (rt2 nhip) dip" by (rule *)
    also have "sqn (rt2 nhip) dip = nsqn\<^sub>r (the (rt2 nhip dip))"
      unfolding nsqn\<^sub>r_def using \<open>dip \<in> vD (rt2 nhip)\<close>
      by - (metis vD_flag_val proj2_eq_sqn proj4_eq_flag vD_iD_gives_kD(1))
    finally show "nsqn\<^sub>r (the (update rt dip (osn, kno, val, hops, nhip, {}) dip))
                                                              < nsqn\<^sub>r (the (rt2 nhip dip))" .
  qed

lemma dhops_le_hops_imp_update_strictly_fresher:
  assumes "dip \<in> vD(rt2 nhip)"
      and sqn: "sqn (rt2 nhip) dip = osn"
      and hop: "the (dhops (rt2 nhip) dip) \<le> hops"
      and **: "rt \<noteq> update rt dip (osn, kno, val, Suc hops, nhip, {})"
    shows "update rt dip (osn, kno, val, Suc hops, nhip, {}) \<sqsubset>\<^bsub>dip\<^esub> rt2 nhip"
  unfolding rt_strictly_fresher_def'
  proof (rule disjI2, rule conjI)
    from ** have "nsqn (update rt dip (osn, kno, val, Suc hops, nhip, {})) dip = osn"
      by (rule nsqn_update_changed_kno_val)
    with \<open>dip\<in>vD(rt2 nhip)\<close>
      have "nsqn\<^sub>r (the (update rt dip (osn, kno, val, Suc hops, nhip, {}) dip)) = osn"
        by (simp add: kD_nsqn)
    also have "osn = sqn (rt2 nhip) dip" by (rule sqn [symmetric])
    also have "sqn (rt2 nhip) dip = nsqn\<^sub>r (the (rt2 nhip dip))"
      unfolding nsqn\<^sub>r_def using \<open>dip \<in> vD(rt2 nhip)\<close>
      by - (metis vD_flag_val proj2_eq_sqn proj4_eq_flag vD_iD_gives_kD(1))
    finally show "nsqn\<^sub>r (the (update rt dip (osn, kno, val, Suc hops, nhip, {}) dip))
                                                              = nsqn\<^sub>r (the (rt2 nhip dip))" .
  next
    have "the (dhops (rt2 nhip) dip) \<le> hops" by (rule hop)
    also have "hops < hops + 1" by simp
    also have "hops + 1 = the (dhops (update rt dip (osn, kno, val, Suc hops, nhip, {})) dip)"
      using ** by simp
    finally have "the (dhops (rt2 nhip) dip)
                        < the (dhops (update rt dip (osn, kno, val, Suc hops, nhip, {})) dip)" .
    thus "\<pi>\<^sub>5 (the (rt2 nhip dip)) < \<pi>\<^sub>5 (the (update rt dip (osn, kno, val, Suc hops, nhip, {}) dip))"
      using \<open>dip \<in> vD(rt2 nhip)\<close> by (simp add: proj5_eq_dhops)
  qed

lemma nsqn_invalidate:
  assumes "dip \<in> kD(rt)"
      and "\<forall>ip\<in>dom(dests). ip \<in> vD(rt) \<and> the (dests ip) = inc (sqn rt ip)"
    shows "nsqn (invalidate rt dests) dip = nsqn rt dip"
  proof -
    from \<open>dip \<in> kD(rt)\<close> have "dip \<in> kD(invalidate rt dests)" by simp

    from assms have "rt \<approx>\<^bsub>dip\<^esub> invalidate rt dests"
      by (rule rt_fresh_as_inc_invalidate)
    with \<open>dip \<in> kD(rt)\<close> \<open>dip \<in> kD(invalidate rt dests)\<close> show ?thesis
      by (simp add: kD_nsqn del: invalidate_kD_inv)
         (erule(2) rt_fresh_as_nsqnr)
  qed

end
