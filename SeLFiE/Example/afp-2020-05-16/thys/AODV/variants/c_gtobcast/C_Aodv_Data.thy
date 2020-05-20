(*  Title:       variants/c_gtobcast/Aodv_Data.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke, Inria
    Author:      Peter Höfner, NICTA
*)

section "Predicates and functions used in the AODV model"

theory C_Aodv_Data
imports C_Gtobcast
begin

subsection "Sequence Numbers"

text \<open>Sequence numbers approximate the relative freshness of routing information.\<close>

definition inc :: "sqn \<Rightarrow> sqn"
  where "inc sn \<equiv> if sn = 0 then sn else sn + 1"

lemma less_than_inc [simp]: "x \<le> inc x"
  unfolding inc_def by simp

lemma inc_minus_suc_0 [simp]:
  "inc x - Suc 0 = x"
  unfolding inc_def by simp

lemma inc_never_one' [simp, intro]: "inc x \<noteq> Suc 0"
  unfolding inc_def by simp

lemma inc_never_one [simp, intro]: "inc x \<noteq> 1"
  by simp

subsection "Modelling Routes"

text \<open>
  A route is a 5-tuple, @{term "(dsn, dsk, flag, hops, nhip)"} where
  @{term dsn} is the `destination sequence number', @{term dsk} is the
  `destination-sequence-number status', @{term flag} is the route status,
  @{term hops} is the number of hops to the destination, and @{term nhip} is the
  next hop toward the destination.
  In this variant, the set of `precursor nodes' is not modelled.
\<close>

type_synonym r = "sqn \<times> k \<times> f \<times> nat \<times> ip"

definition proj2 :: "r \<Rightarrow> sqn" ("\<pi>\<^sub>2")
  where "\<pi>\<^sub>2 \<equiv> \<lambda>(dsn, _, _, _, _). dsn"

definition proj3 :: "r \<Rightarrow> k" ("\<pi>\<^sub>3")
  where "\<pi>\<^sub>3 \<equiv> \<lambda>(_, dsk, _, _, _). dsk"

definition proj4 :: "r \<Rightarrow> f" ("\<pi>\<^sub>4")
  where "\<pi>\<^sub>4 \<equiv> \<lambda>(_, _, flag, _, _). flag"

definition proj5 :: "r \<Rightarrow> nat" ("\<pi>\<^sub>5")
  where "\<pi>\<^sub>5 \<equiv> \<lambda>(_, _, _, hops, _). hops"

definition proj6 :: "r \<Rightarrow> ip" ("\<pi>\<^sub>6")
  where "\<pi>\<^sub>6 \<equiv> \<lambda>(_, _, _, _, nhip). nhip"

lemma projs [simp]:
  "\<pi>\<^sub>2(dsn, dsk, flag, hops, nhip) = dsn"
  "\<pi>\<^sub>3(dsn, dsk, flag, hops, nhip) = dsk"
  "\<pi>\<^sub>4(dsn, dsk, flag, hops, nhip) = flag"
  "\<pi>\<^sub>5(dsn, dsk, flag, hops, nhip) = hops"
  "\<pi>\<^sub>6(dsn, dsk, flag, hops, nhip) = nhip"
  by (clarsimp simp: proj2_def proj3_def proj4_def
                     proj5_def proj6_def)+

lemma proj3_pred [intro]: "\<lbrakk> P kno; P unk \<rbrakk> \<Longrightarrow> P (\<pi>\<^sub>3 x)"
  by (rule k.induct)

lemma proj4_pred [intro]: "\<lbrakk> P val; P inv \<rbrakk> \<Longrightarrow> P (\<pi>\<^sub>4 x)"
  by (rule f.induct)

lemma proj6_pair_snd [simp]:
  fixes dsn' r
  shows "\<pi>\<^sub>6 (dsn', snd (r)) = \<pi>\<^sub>6(r)"
  by (cases r) simp

subsection "Routing Tables"

text \<open>Routing tables map ip addresses to route entries.\<close>

type_synonym rt = "ip \<rightharpoonup> r"

syntax
  "_Sigma_route" :: "rt \<Rightarrow> ip \<rightharpoonup> r"  ("\<sigma>\<^bsub>route\<^esub>'(_, _')")

translations
 "\<sigma>\<^bsub>route\<^esub>(rt, dip)" => "rt dip" 

definition sqn :: "rt \<Rightarrow> ip \<Rightarrow> sqn"
  where "sqn rt dip \<equiv> case \<sigma>\<^bsub>route\<^esub>(rt, dip) of Some r \<Rightarrow> \<pi>\<^sub>2(r) | None \<Rightarrow> 0"

definition sqnf :: "rt \<Rightarrow> ip \<Rightarrow> k"
  where "sqnf rt dip \<equiv> case \<sigma>\<^bsub>route\<^esub>(rt, dip) of Some r \<Rightarrow> \<pi>\<^sub>3(r) | None \<Rightarrow> unk"

abbreviation flag :: "rt \<Rightarrow> ip \<rightharpoonup> f"
  where "flag rt dip \<equiv> map_option \<pi>\<^sub>4 (\<sigma>\<^bsub>route\<^esub>(rt, dip))"

abbreviation dhops :: "rt \<Rightarrow> ip \<rightharpoonup> nat"
   where "dhops rt dip \<equiv> map_option \<pi>\<^sub>5 (\<sigma>\<^bsub>route\<^esub>(rt, dip))"

abbreviation nhop :: "rt \<Rightarrow> ip \<rightharpoonup> ip"
   where "nhop rt dip \<equiv> map_option \<pi>\<^sub>6 (\<sigma>\<^bsub>route\<^esub>(rt, dip))"

definition vD :: "rt \<Rightarrow> ip set"
  where "vD rt \<equiv> {dip. flag rt dip = Some val}"

definition iD :: "rt \<Rightarrow> ip set"
  where "iD rt \<equiv> {dip. flag rt dip = Some inv}"

definition kD :: "rt \<Rightarrow> ip set"
  where "kD rt \<equiv> {dip. rt dip \<noteq> None}"

lemma kD_is_vD_and_iD: "kD rt = vD rt \<union> iD rt"
  unfolding kD_def vD_def iD_def by auto

lemma vD_iD_gives_kD [simp]:
   "\<And>ip rt. ip \<in> vD rt \<Longrightarrow> ip \<in> kD rt"
   "\<And>ip rt. ip \<in> iD rt \<Longrightarrow> ip \<in> kD rt"
  unfolding kD_is_vD_and_iD by simp_all

lemma kD_Some [dest]:
    fixes dip rt
  assumes "dip \<in> kD rt"
    shows "\<exists>dsn dsk flag hops nhip.
           \<sigma>\<^bsub>route\<^esub>(rt, dip) = Some (dsn, dsk, flag, hops, nhip)"
  using assms unfolding kD_def by simp

lemma kD_None [dest]:
    fixes dip rt
  assumes "dip \<notin> kD rt"
    shows "\<sigma>\<^bsub>route\<^esub>(rt, dip) = None"
  using assms unfolding kD_def
  by (metis (mono_tags) mem_Collect_eq)

lemma vD_Some [dest]:
    fixes dip rt
  assumes "dip \<in> vD rt"
    shows "\<exists>dsn dsk hops nhip.
           \<sigma>\<^bsub>route\<^esub>(rt, dip) = Some (dsn, dsk, val, hops, nhip)"
  using assms unfolding vD_def by simp

lemma vD_empty [simp]: "vD Map.empty = {}"
  unfolding vD_def by simp

lemma iD_Some [dest]:
    fixes dip rt
  assumes "dip \<in> iD rt"
    shows "\<exists>dsn dsk hops nhip.
           \<sigma>\<^bsub>route\<^esub>(rt, dip) = Some (dsn, dsk, inv, hops, nhip)"
  using assms unfolding iD_def by simp

lemma val_is_vD [elim]:
    fixes ip rt
  assumes "ip\<in>kD(rt)"
      and "the (flag rt ip) = val"
    shows "ip\<in>vD(rt)"
  using assms unfolding vD_def by auto

lemma inv_is_iD [elim]:
    fixes ip rt
  assumes "ip\<in>kD(rt)"
      and "the (flag rt ip) = inv"
    shows "ip\<in>iD(rt)"
  using assms unfolding iD_def by auto

lemma iD_flag_is_inv [elim, simp]:
    fixes ip rt
  assumes "ip\<in>iD(rt)"
    shows "the (flag rt ip) = inv"
  proof -
    from \<open>ip\<in>iD(rt)\<close> have "ip\<in>kD(rt)" by auto
    with assms show ?thesis unfolding iD_def by auto
  qed

lemma kD_but_not_vD_is_iD [elim]:
    fixes ip rt
  assumes "ip\<in>kD(rt)"
      and "ip\<notin>vD(rt)"
    shows "ip\<in>iD(rt)"
  proof -
    from \<open>ip\<in>kD(rt)\<close> obtain dsn dsk f hops nhop
      where rtip: "rt ip = Some (dsn, dsk, f, hops, nhop)"
       by (metis kD_Some)
    from \<open>ip\<notin>vD(rt)\<close> have "f \<noteq> val"
    proof (rule contrapos_nn)
      assume "f = val"
      with rtip have "the (flag rt ip) = val" by simp
      with \<open>ip\<in>kD(rt)\<close> show "ip\<in>vD(rt)" ..
    qed
    with rtip have "the (flag rt ip)= inv" by simp  
    with \<open>ip\<in>kD(rt)\<close> show "ip\<in>iD(rt)" ..
  qed

lemma vD_or_iD [elim]:
    fixes ip rt
  assumes "ip\<in>kD(rt)"
      and "ip\<in>vD(rt) \<Longrightarrow> P rt ip"
      and "ip\<in>iD(rt) \<Longrightarrow> P rt ip"
    shows "P rt ip"
  proof -
    from \<open>ip\<in>kD(rt)\<close> have "ip\<in>vD(rt) \<union> iD(rt)"
      by (simp add: kD_is_vD_and_iD)
    thus ?thesis by (auto elim: assms(2-3))
  qed

lemma proj5_eq_dhops: "\<And>dip rt. dip\<in>kD(rt) \<Longrightarrow> \<pi>\<^sub>5(the (rt dip)) = the (dhops rt dip)"
  unfolding sqn_def by (drule kD_Some) clarsimp

lemma proj4_eq_flag: "\<And>dip rt. dip\<in>kD(rt) \<Longrightarrow> \<pi>\<^sub>4(the (rt dip)) = the (flag rt dip)"
  unfolding sqn_def by (drule kD_Some) clarsimp

lemma proj2_eq_sqn: "\<And>dip rt. dip\<in>kD(rt) \<Longrightarrow> \<pi>\<^sub>2(the (rt dip)) = sqn rt dip"
  unfolding sqn_def by (drule kD_Some) clarsimp

lemma kD_sqnf_is_proj3 [simp]:
  "\<And>ip rt. ip\<in>kD(rt) \<Longrightarrow> sqnf rt ip = \<pi>\<^sub>3(the (rt ip))"
  unfolding sqnf_def by auto

lemma vD_flag_val [simp]:
  "\<And>dip rt. dip \<in> vD (rt) \<Longrightarrow> the (flag rt dip) = val"
  unfolding vD_def by clarsimp

lemma kD_update [simp]:
  "\<And>rt nip v. kD (rt(nip \<mapsto> v)) = insert nip (kD rt)"
  unfolding kD_def by auto

lemma kD_empty [simp]: "kD Map.empty = {}"
  unfolding kD_def by simp

lemma ip_equal_or_known [elim]:
  fixes rt ip ip'
  assumes "ip = ip' \<or> ip\<in>kD(rt)"
      and "ip = ip' \<Longrightarrow> P rt ip ip'"
      and "\<lbrakk> ip \<noteq> ip'; ip\<in>kD(rt)\<rbrakk> \<Longrightarrow> P rt ip ip'"
    shows "P rt ip ip'"
  using assms by auto

subsection "Updating Routing Tables"

text \<open>Routing table entries are modified through explicit functions.
      The properties of these functions are important in invariant proofs.\<close>

subsubsection "Updating route entries"

lemma in_kD_case [simp]:
    fixes dip rt
  assumes "dip \<in> kD(rt)"
    shows "(case rt dip of None \<Rightarrow> en | Some r \<Rightarrow> es r) = es (the (rt dip))"
  using assms [THEN kD_Some] by auto

lemma not_in_kD_case [simp]:
    fixes dip rt
  assumes "dip \<notin> kD(rt)"
    shows "(case rt dip of None \<Rightarrow> en | Some r \<Rightarrow> es r) = en"
  using assms [THEN kD_None] by auto

lemma rt_Some_sqn [dest]:
    fixes rt and ip dsn dsk flag hops nhip
  assumes "rt ip = Some (dsn, dsk, flag, hops, nhip)"
    shows "sqn rt ip = dsn"
  unfolding sqn_def using assms by simp

lemma not_kD_sqn [simp]:
    fixes dip rt
  assumes "dip \<notin> kD(rt)"
    shows "sqn rt dip = 0"
  using assms unfolding sqn_def
  by simp

definition update_arg_wf :: "r \<Rightarrow> bool"
where "update_arg_wf r \<equiv> \<pi>\<^sub>4(r) = val \<and>
                         (\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk) \<and>
                         (\<pi>\<^sub>3(r) = unk \<longrightarrow> \<pi>\<^sub>5(r) = 1)"

lemma update_arg_wf_gives_cases:
  "\<And>r. update_arg_wf r \<Longrightarrow> (\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)"
  unfolding update_arg_wf_def by simp

lemma update_arg_wf_tuples [simp]:
  "\<And>nhip. update_arg_wf (0, unk, val, Suc 0, nhip)"
  "\<And>n hops nhip. update_arg_wf (Suc n, kno, val, hops,  nhip)"
  unfolding update_arg_wf_def by auto

lemma update_arg_wf_tuples' [elim]:
  "\<And>n hops nhip. Suc 0 \<le> n \<Longrightarrow> update_arg_wf (n, kno, val, hops,  nhip)"
  unfolding update_arg_wf_def by auto

lemma wf_r_cases [intro]:
    fixes P r
  assumes "update_arg_wf r"
      and c1: "\<And>nhip. P (0, unk, val, Suc 0, nhip)"
      and c2: "\<And>dsn hops nhip. dsn > 0 \<Longrightarrow> P (dsn, kno, val, hops, nhip)"
    shows "P r"
  proof -
    obtain dsn dsk flag hops nhip
    where *: "r = (dsn, dsk, flag, hops, nhip)" by (cases r)
    with \<open>update_arg_wf r\<close> have wf1: "flag = val"
                            and wf2: "(dsn = 0) = (dsk = unk)"
                            and wf3: "dsk = unk \<longrightarrow> (hops = 1)"
      unfolding update_arg_wf_def by auto
    have "P (dsn, dsk, flag, hops, nhip)"
    proof (cases dsk)
      assume "dsk = unk"
      moreover with wf2 wf3 have "dsn = 0" and "hops = Suc 0" by auto
      ultimately show ?thesis using \<open>flag = val\<close> by simp (rule c1)
    next
      assume "dsk = kno"
      moreover with wf2 have "dsn > 0" by simp
      ultimately show ?thesis using \<open>flag = val\<close> by simp (rule c2)
    qed
    with * show "P r" by simp
  qed

definition update :: "rt \<Rightarrow> ip \<Rightarrow> r \<Rightarrow> rt"
  where
  "update rt ip r \<equiv>
     case \<sigma>\<^bsub>route\<^esub>(rt, ip) of
       None \<Rightarrow> rt (ip \<mapsto> r)
     | Some s \<Rightarrow>
          if \<pi>\<^sub>2(s) < \<pi>\<^sub>2(r) then rt (ip \<mapsto> r)
          else if \<pi>\<^sub>2(s) = \<pi>\<^sub>2(r) \<and> (\<pi>\<^sub>5(s) > \<pi>\<^sub>5(r) \<or> \<pi>\<^sub>4(s) = inv)
               then rt (ip \<mapsto> r)
               else if \<pi>\<^sub>3(r) = unk
                    then rt (ip \<mapsto> (\<pi>\<^sub>2(s), snd (r)))
                    else rt (ip \<mapsto> s)"

lemma update_simps [simp]:
  fixes r s nrt nr' ns rt ip
  defines "s \<equiv> the \<sigma>\<^bsub>route\<^esub>(rt, ip)"
      and "nr' \<equiv> (\<pi>\<^sub>2(s), \<pi>\<^sub>3(r), \<pi>\<^sub>4(r), \<pi>\<^sub>5(r), \<pi>\<^sub>6(r))"
  shows
  "\<lbrakk>ip \<notin> kD(rt)\<rbrakk>                            \<Longrightarrow> update rt ip r = rt (ip \<mapsto> r)"
  "\<lbrakk>ip \<in> kD(rt); sqn rt ip < \<pi>\<^sub>2(r)\<rbrakk>         \<Longrightarrow> update rt ip r = rt (ip \<mapsto> r)"
  "\<lbrakk>ip \<in> kD(rt); sqn rt ip = \<pi>\<^sub>2(r);
                 the (dhops rt ip) > \<pi>\<^sub>5(r)\<rbrakk> \<Longrightarrow> update rt ip r = rt (ip \<mapsto> r)"
  "\<lbrakk>ip \<in> kD(rt); sqn rt ip = \<pi>\<^sub>2(r);
                 flag rt ip = Some inv\<rbrakk>     \<Longrightarrow> update rt ip r = rt (ip \<mapsto> r)"
  "\<lbrakk>ip \<in> kD(rt); \<pi>\<^sub>3(r) = unk; (\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)\<rbrakk>  \<Longrightarrow> update rt ip r = rt (ip \<mapsto> nr')"
  "\<lbrakk>ip \<in> kD(rt); sqn rt ip \<ge> \<pi>\<^sub>2(r); \<pi>\<^sub>3(r) = kno;
    sqn rt ip = \<pi>\<^sub>2(r) \<Longrightarrow> the (dhops rt ip) \<le> \<pi>\<^sub>5(r) \<and> the (flag rt ip) = val \<rbrakk>
                                            \<Longrightarrow> update rt ip r = rt (ip \<mapsto> s)"
  proof -
    assume "ip\<notin>kD(rt)"
    hence "\<sigma>\<^bsub>route\<^esub>(rt, ip) = None" ..
    thus "update rt ip r = rt (ip \<mapsto> r)"
      unfolding update_def by simp
  next
    assume "ip \<in> kD(rt)"
       and "sqn rt ip < \<pi>\<^sub>2(r)"
    from this(1) obtain dsn dsk fl hops nhip
      where "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)
    with \<open>sqn rt ip < \<pi>\<^sub>2(r)\<close> show "update rt ip r = rt (ip \<mapsto> r)"
      unfolding update_def s_def by auto
  next
    assume "ip \<in> kD(rt)"
       and "sqn rt ip = \<pi>\<^sub>2(r)"
       and "the (dhops rt ip) > \<pi>\<^sub>5(r)"
    from this(1) obtain dsn dsk fl hops nhip
      where "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)
    with \<open>sqn rt ip = \<pi>\<^sub>2(r)\<close> and \<open>the (dhops rt ip) > \<pi>\<^sub>5(r)\<close>
      show "update rt ip r = rt (ip \<mapsto> r)"
        unfolding update_def s_def by auto
   next
     assume "ip \<in> kD(rt)"
        and "sqn rt ip = \<pi>\<^sub>2(r)"
        and "flag rt ip = Some inv"
    from this(1) obtain dsn dsk fl hops nhip
      where "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)        
     with \<open>sqn rt ip = \<pi>\<^sub>2(r)\<close> and \<open>flag rt ip = Some inv\<close>
      show "update rt ip r = rt (ip \<mapsto> r)"
        unfolding update_def s_def by auto
   next
    assume "ip \<in> kD(rt)"
       and "\<pi>\<^sub>3(r) = unk"
       and "(\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)"
    from this(1) obtain dsn dsk fl hops nhip
      where "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)
    with \<open>(\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)\<close> and \<open>\<pi>\<^sub>3(r) = unk\<close>
      show "update rt ip r = rt (ip \<mapsto> nr')"
        unfolding update_def nr'_def s_def
      by (cases r) simp
   next
    assume "ip \<in> kD(rt)"
       and otherassms: "sqn rt ip \<ge> \<pi>\<^sub>2(r)"
           "\<pi>\<^sub>3(r) = kno"
           "sqn rt ip = \<pi>\<^sub>2(r) \<Longrightarrow> the (dhops rt ip) \<le> \<pi>\<^sub>5(r) \<and> the (flag rt ip) = val"
    from this(1) obtain dsn dsk fl hops nhip
      where "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)
     with otherassms show "update rt ip r = rt (ip \<mapsto> s)"
      unfolding update_def s_def by auto
  qed

lemma update_cases [elim]:
  assumes "(\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)"
      and c1: "\<lbrakk>ip \<notin> kD(rt)\<rbrakk> \<Longrightarrow> P (rt (ip \<mapsto> r))"

      and c2: "\<lbrakk>ip \<in> kD(rt); sqn rt ip < \<pi>\<^sub>2(r)\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c3: "\<lbrakk>ip \<in> kD(rt); sqn rt ip = \<pi>\<^sub>2(r); the (dhops rt ip) > \<pi>\<^sub>5(r)\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c4: "\<lbrakk>ip \<in> kD(rt); sqn rt ip = \<pi>\<^sub>2(r); the (flag rt ip) = inv\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c5: "\<lbrakk>ip \<in> kD(rt); \<pi>\<^sub>3(r) = unk\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> (\<pi>\<^sub>2(the \<sigma>\<^bsub>route\<^esub>(rt, ip)), \<pi>\<^sub>3(r),
                                  \<pi>\<^sub>4(r), \<pi>\<^sub>5(r), \<pi>\<^sub>6(r))))"
      and c6: "\<lbrakk>ip \<in> kD(rt); sqn rt ip \<ge> \<pi>\<^sub>2(r); \<pi>\<^sub>3(r) = kno;
                sqn rt ip = \<pi>\<^sub>2(r) \<Longrightarrow> the (dhops rt ip) \<le> \<pi>\<^sub>5(r) \<and> the (flag rt ip) = val\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> the \<sigma>\<^bsub>route\<^esub>(rt, ip)))"
  shows "(P (update rt ip r))"
  proof (cases "ip \<in> kD(rt)")
    assume "ip \<notin> kD(rt)"
    with c1 show ?thesis
      by simp
  next
    assume "ip \<in> kD(rt)"
    moreover then obtain dsn dsk fl hops nhip
      where rteq: "rt ip = Some (dsn, dsk, fl, hops, nhip)"
        by (metis kD_Some)
    moreover obtain dsn' dsk' fl' hops' nhip'
      where req: "r = (dsn', dsk', fl', hops', nhip')"
        by (cases r) metis
    ultimately show ?thesis
      using \<open>(\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)\<close>
            c2 [OF \<open>ip\<in>kD(rt)\<close>]
            c3 [OF \<open>ip\<in>kD(rt)\<close>]
            c4 [OF \<open>ip\<in>kD(rt)\<close>]
            c5 [OF \<open>ip\<in>kD(rt)\<close>]
            c6 [OF \<open>ip\<in>kD(rt)\<close>]
    unfolding update_def sqn_def by auto
  qed

lemma update_cases_kD:
  assumes "(\<pi>\<^sub>2(r) = 0) = (\<pi>\<^sub>3(r) = unk)"
      and "ip \<in> kD(rt)"
      and c2: "sqn rt ip < \<pi>\<^sub>2(r) \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c3: "\<lbrakk>sqn rt ip = \<pi>\<^sub>2(r); the (dhops rt ip) > \<pi>\<^sub>5(r)\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c4: "\<lbrakk>sqn rt ip = \<pi>\<^sub>2(r); the (flag rt ip) = inv\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> r ))"
      and c5: "\<pi>\<^sub>3(r) = unk \<Longrightarrow> P (rt (ip \<mapsto> (\<pi>\<^sub>2(the \<sigma>\<^bsub>route\<^esub>(rt, ip)), \<pi>\<^sub>3(r),
                                            \<pi>\<^sub>4(r), \<pi>\<^sub>5(r), \<pi>\<^sub>6(r))))"
      and c6: "\<lbrakk>sqn rt ip \<ge> \<pi>\<^sub>2(r); \<pi>\<^sub>3(r) = kno;
                sqn rt ip = \<pi>\<^sub>2(r) \<Longrightarrow> the (dhops rt ip) \<le> \<pi>\<^sub>5(r) \<and> the (flag rt ip) = val\<rbrakk>
                \<Longrightarrow> P (rt (ip \<mapsto> the \<sigma>\<^bsub>route\<^esub>(rt, ip)))"
  shows "(P (update rt ip r))"
  using assms(1) proof (rule update_cases)
    assume "sqn rt ip < \<pi>\<^sub>2(r)"
    thus "P (rt(ip \<mapsto> r))" by (rule c2)
  next
    assume "sqn rt ip = \<pi>\<^sub>2(r)"
       and "the (dhops rt ip) > \<pi>\<^sub>5(r)"
    thus "P (rt(ip \<mapsto> r))"
      by (rule c3)
  next
    assume "sqn rt ip = \<pi>\<^sub>2(r)"
       and "the (flag rt ip) = inv"
    thus "P (rt(ip \<mapsto> r))"
      by (rule c4)
  next
    assume "\<pi>\<^sub>3(r) = unk"
    thus "P (rt (ip \<mapsto> (\<pi>\<^sub>2(the \<sigma>\<^bsub>route\<^esub>(rt, ip)), \<pi>\<^sub>3(r), \<pi>\<^sub>4(r), \<pi>\<^sub>5(r), \<pi>\<^sub>6(r))))"
      by (rule c5)
  next
    assume "sqn rt ip \<ge> \<pi>\<^sub>2(r)"
       and "\<pi>\<^sub>3(r) = kno"
       and "sqn rt ip = \<pi>\<^sub>2(r) \<Longrightarrow> the (dhops rt ip) \<le> \<pi>\<^sub>5(r) \<and> the (flag rt ip) = val"
    thus "P (rt (ip \<mapsto> the (rt ip)))"
      by (rule c6)
  qed (simp add: \<open>ip \<in> kD(rt)\<close>)

lemma in_kD_after_update [simp]:
  fixes rt nip dsn dsk flag hops nhip
  shows "kD (update rt nip (dsn, dsk, flag, hops, nhip)) = insert nip (kD rt)"
  unfolding update_def
  by (cases "rt nip") auto

lemma nhop_of_update [simp]:
  fixes rt dip dsn dsk flag hops nhip
  assumes "rt \<noteq> update rt dip (dsn, dsk, flag, hops, nhip)"
  shows "the (nhop (update rt dip (dsn, dsk, flag, hops, nhip)) dip) = nhip"
  proof -
  from assms
  have update_neq: "\<And>v. rt dip = Some v \<Longrightarrow>
          update rt dip (dsn, dsk, flag, hops, nhip)
             \<noteq> rt(dip \<mapsto> the (rt dip))"
    by auto
  show ?thesis
    proof (cases "rt dip = None")
      assume "rt dip = None"
      thus "?thesis" unfolding update_def by clarsimp
    next
      assume "rt dip \<noteq> None"
      then obtain v where "rt dip = Some v" by (metis not_None_eq)
      with update_neq [OF this] show ?thesis
        unfolding update_def by auto
    qed
  qed

lemma sqn_if_updated:
  fixes rip v rt ip
  shows "sqn (\<lambda>x. if x = rip then Some v else rt x) ip
         = (if ip = rip then \<pi>\<^sub>2(v) else sqn rt ip)"
  unfolding sqn_def by simp

lemma update_sqn [simp]:
  fixes rt dip rip dsn dsk hops nhip
  assumes "(dsn = 0) = (dsk = unk)"
  shows "sqn rt dip \<le> sqn (update rt rip (dsn, dsk, val, hops, nhip)) dip"
  proof (rule update_cases)
    show "(\<pi>\<^sub>2 (dsn, dsk, val, hops, nhip) = 0) = (\<pi>\<^sub>3 (dsn, dsk, val, hops, nhip) = unk)"
      by simp (rule assms)
  qed (clarsimp simp: sqn_if_updated sqn_def)+

lemma sqn_update_bigger [simp]:
    fixes rt ip ip' dsn dsk flag hops nhip
  assumes "1 \<le> hops"
    shows "sqn rt ip \<le> sqn (update rt ip' (dsn, dsk, flag, hops, nhip)) ip"
  using assms unfolding update_def sqn_def
  by (clarsimp split: option.split) auto

lemma dhops_update [intro]:
    fixes rt dsn dsk flag hops ip rip nhip
  assumes ex: "\<forall>ip\<in>kD rt. the (dhops rt ip) \<ge> 1"
      and ip: "(ip = rip \<and> Suc 0 \<le> hops) \<or> (ip \<noteq> rip \<and> ip\<in>kD rt)"
    shows "Suc 0 \<le> the (dhops (update rt rip (dsn, dsk, flag, hops, nhip)) ip)"
  using ip proof
    assume "ip = rip \<and> Suc 0 \<le> hops" thus ?thesis
      unfolding update_def using ex
      by (cases "rip \<in> kD rt") (drule(1) bspec, auto)
  next
    assume "ip \<noteq> rip \<and> ip\<in>kD rt" thus ?thesis
      using ex unfolding update_def
      by (cases "rip\<in>kD rt") auto
  qed

lemma update_another [simp]:
    fixes dip ip rt dsn dsk flag hops nhip
  assumes "ip \<noteq> dip"
    shows "(update rt dip (dsn, dsk, flag, hops, nhip)) ip = rt ip"
  using assms unfolding update_def
  by (clarsimp split: option.split)

lemma nhop_update_another [simp]:
    fixes dip ip rt dsn dsk flag hops nhip
  assumes "ip \<noteq> dip"
    shows "nhop (update rt dip (dsn, dsk, flag, hops, nhip)) ip = nhop rt ip"
  using assms unfolding update_def
  by (clarsimp split: option.split)

lemma dhops_update_another [simp]:
    fixes dip ip rt dsn dsk flag hops nhip
  assumes "ip \<noteq> dip"
    shows "dhops (update rt dip (dsn, dsk, flag, hops, nhip)) ip = dhops rt ip"
  using assms unfolding update_def
  by (clarsimp split: option.split)

lemma sqn_update_same [simp]:
  "\<And>rt ip dsn dsk flag hops nhip. sqn (rt(ip \<mapsto> v)) ip = \<pi>\<^sub>2(v)"
  unfolding sqn_def by simp

lemma dhops_update_changed [simp]:
    fixes rt dip osn hops nhip
  assumes "rt \<noteq> update rt dip (osn, kno, val, hops, nhip)"
    shows "the (dhops (update rt dip (osn, kno, val, hops, nhip)) dip) = hops"
  using assms unfolding update_def                                                      
  by (clarsimp split: option.split_asm option.split if_split_asm) auto

lemma nhop_update_unk_val [simp]:
  "\<And>rt dip ip dsn hops.
   the (nhop (update rt dip (dsn, unk, val, hops, ip)) dip) = ip"
   unfolding update_def by (clarsimp split: option.split)

lemma nhop_update_changed [simp]:
    fixes rt dip dsn dsk flg hops sip
  assumes "update rt dip (dsn, dsk, flg, hops, sip) \<noteq> rt"
    shows "the (nhop (update rt dip (dsn, dsk, flg, hops, sip)) dip) = sip"
  using assms unfolding update_def
  by (clarsimp split: option.splits if_split_asm) auto

lemma update_rt_split_asm:
  "\<And>rt ip dsn dsk flag hops sip.
   P (update rt ip (dsn, dsk, flag, hops, sip))
   =
   (\<not>(rt = update rt ip (dsn, dsk, flag, hops, sip) \<and> \<not>P rt
      \<or> rt \<noteq> update rt ip (dsn, dsk, flag, hops, sip)
         \<and> \<not>P (update rt ip (dsn, dsk, flag, hops, sip))))"
  by auto

lemma sqn_update [simp]: "\<And>rt dip dsn flg hops sip.
  rt \<noteq> update rt dip (dsn, kno, flg, hops, sip)
  \<Longrightarrow> sqn (update rt dip (dsn, kno, flg, hops, sip)) dip = dsn"
  unfolding update_def by (clarsimp split: option.split if_split_asm) auto

lemma sqnf_update [simp]: "\<And>rt dip dsn dsk flg hops sip.
  rt \<noteq> update rt dip (dsn, dsk, flg, hops, sip)
  \<Longrightarrow> sqnf (update rt dip (dsn, dsk, flg, hops, sip)) dip = dsk"
  unfolding update_def sqnf_def
  by (clarsimp split: option.splits if_split_asm) auto

lemma update_kno_dsn_greater_zero:
  "\<And>rt dip ip dsn hops. 1 \<le> dsn \<Longrightarrow> 1 \<le> (sqn (update rt dip (dsn, kno, val, hops, ip)) dip)"
   unfolding update_def 
  by (clarsimp split: option.splits)

lemma proj3_update [simp]: "\<And>rt dip dsn dsk flg hops sip.
  rt \<noteq> update rt dip (dsn, dsk, flg, hops, sip)
  \<Longrightarrow> \<pi>\<^sub>3(the (update rt dip (dsn, dsk, flg, hops, sip) dip)) = dsk"
  unfolding update_def sqnf_def
  by (clarsimp split: option.splits if_split_asm) auto

lemma nhop_update_changed_kno_val [simp]: "\<And>rt ip dsn dsk hops nhip.
  rt \<noteq> update rt ip (dsn, kno, val, hops, nhip)
   \<Longrightarrow> the (nhop (update rt ip (dsn, kno, val, hops, nhip)) ip) = nhip"
  unfolding update_def
  by (clarsimp split: option.split_asm option.split if_split_asm) auto

lemma flag_update [simp]: "\<And>rt dip dsn flg hops sip.
  rt \<noteq> update rt dip (dsn, kno, flg, hops, sip)
  \<Longrightarrow> the (flag (update rt dip (dsn, kno, flg, hops, sip)) dip) = flg"
  unfolding update_def
  by (clarsimp split: option.split if_split_asm) auto

lemma the_flag_Some [dest!]:
    fixes ip rt
  assumes "the (flag rt ip) = x"
      and "ip \<in> kD rt"
    shows "flag rt ip = Some x"
  using assms by auto

lemma kD_update_unchanged [dest]:
    fixes rt dip dsn dsk flag hops nhip
  assumes "rt = update rt dip (dsn, dsk, flag, hops, nhip)"
    shows "dip\<in>kD(rt)"
  proof -
    have "dip\<in>kD(update rt dip (dsn, dsk, flag, hops, nhip))" by simp
    with assms show ?thesis by simp
  qed

lemma nhop_update [simp]: "\<And>rt dip dsn dsk flg hops sip.
  rt \<noteq> update rt dip (dsn, dsk, flg, hops, sip)
  \<Longrightarrow> the (nhop (update rt dip (dsn, dsk, flg, hops, sip)) dip) = sip"
  unfolding update_def sqnf_def
  by (clarsimp split: option.splits if_split_asm) auto

lemma sqn_update_another [simp]:
    fixes dip ip rt dsn dsk flag hops nhip
  assumes "ip \<noteq> dip"
    shows "sqn (update rt dip (dsn, dsk, flag, hops, nhip)) ip = sqn rt ip"
  using assms unfolding update_def sqn_def
  by (clarsimp split: option.splits) auto

lemma sqnf_update_another [simp]:
    fixes dip ip rt dsn dsk flag hops nhip
  assumes "ip \<noteq> dip"
    shows "sqnf (update rt dip (dsn, dsk, flag, hops, nhip)) ip = sqnf rt ip"
  using assms unfolding update_def sqnf_def
  by (clarsimp split: option.splits) auto

lemma vD_update_val [dest]:
  "\<And>dip rt dip' dsn dsk hops nhip.
   dip \<in> vD(update rt dip' (dsn, dsk, val, hops, nhip)) \<Longrightarrow> (dip\<in>vD(rt) \<or> dip=dip')"
   unfolding update_def vD_def by (clarsimp split: option.split_asm if_split_asm)

subsubsection "Invalidating route entries"

definition invalidate :: "rt \<Rightarrow> (ip \<rightharpoonup> sqn) \<Rightarrow> rt"
where "invalidate rt dests \<equiv>
  \<lambda>ip. case (rt ip, dests ip) of
    (None, _) \<Rightarrow> None
  | (Some s, None) \<Rightarrow> Some s
  | (Some (_, dsk, _, hops, nhip), Some rsn) \<Rightarrow>
                      Some (rsn, dsk, inv, hops, nhip)"

lemma proj3_invalidate [simp]:
  "\<And>dip. \<pi>\<^sub>3(the ((invalidate rt dests) dip)) = \<pi>\<^sub>3(the (rt dip))"
  unfolding invalidate_def by (clarsimp split: option.split)

lemma proj5_invalidate [simp]:
  "\<And>dip. \<pi>\<^sub>5(the ((invalidate rt dests) dip)) = \<pi>\<^sub>5(the (rt dip))"
  unfolding invalidate_def by (clarsimp split: option.split)

lemma proj6_invalidate [simp]:
  "\<And>dip. \<pi>\<^sub>6(the ((invalidate rt dests) dip)) = \<pi>\<^sub>6(the (rt dip))"
  unfolding invalidate_def by (clarsimp split: option.split)


lemma invalidate_kD_inv [simp]:
  "\<And>rt dests. kD (invalidate rt dests) = kD rt"
  unfolding invalidate_def kD_def
  by (simp split: option.split)

lemma invalidate_sqn:
  fixes rt dip dests
  assumes "\<forall>rsn. dests dip = Some rsn \<longrightarrow> sqn rt dip \<le> rsn"
  shows "sqn rt dip \<le> sqn (invalidate rt dests) dip"
  proof (cases "dip \<notin> kD(rt)")
    assume "\<not> dip \<notin> kD(rt)"
    hence "dip\<in>kD(rt)" by simp
    then obtain dsn dsk flag hops nhip pre where "rt dip = Some (dsn, dsk, flag, hops, nhip)"
      by (metis kD_Some)
    with assms show "sqn rt dip \<le> sqn (invalidate rt dests) dip"
      by (cases "dests dip") (auto simp add: invalidate_def sqn_def)
  qed simp

lemma sqn_invalidate_in_dests [simp]:
    fixes dests ipa rsn rt
  assumes "dests ipa = Some rsn"
      and "ipa\<in>kD(rt)"
    shows "sqn (invalidate rt dests) ipa = rsn"
  unfolding invalidate_def sqn_def
  using assms(1) assms(2) [THEN kD_Some]
  by clarsimp

lemma dhops_invalidate [simp]:
  "\<And>dip. the (dhops (invalidate rt dests) dip) = the (dhops rt dip)"
  unfolding invalidate_def by (clarsimp split: option.split)

lemma sqnf_invalidate [simp]:
  "\<And>dip. sqnf (invalidate (rt \<xi>) (dests \<xi>)) dip = sqnf (rt \<xi>) dip"
  unfolding sqnf_def invalidate_def by (clarsimp split: option.split)

lemma nhop_invalidate [simp]:
  "\<And>dip. the (nhop (invalidate (rt \<xi>) (dests \<xi>)) dip) = the (nhop (rt \<xi>) dip)"
  unfolding invalidate_def by (clarsimp split: option.split)

lemma invalidate_other [simp]:
    fixes rt dests dip
  assumes "dip\<notin>dom(dests)"
    shows "invalidate rt dests dip = rt dip"
  using assms unfolding invalidate_def
  by (clarsimp split: option.split_asm)

lemma invalidate_none [simp]:
    fixes rt dests dip
  assumes "dip\<notin>kD(rt)"
    shows "invalidate rt dests dip = None"
  using assms unfolding invalidate_def by clarsimp

lemma vD_invalidate_vD_not_dests:
  "\<And>dip rt dests. dip\<in>vD(invalidate rt dests) \<Longrightarrow> dip\<in>vD(rt) \<and> dests dip = None"
  unfolding invalidate_def vD_def 
  by (clarsimp split: option.split_asm)

lemma sqn_invalidate_not_in_dests [simp]:
  fixes dests dip rt
  assumes "dip\<notin>dom(dests)"
  shows "sqn (invalidate rt dests) dip = sqn rt dip"
  using assms unfolding sqn_def by simp

lemma invalidate_changes:
    fixes rt dests dip dsn dsk flag hops nhip
  assumes "invalidate rt dests dip = Some (dsn, dsk, flag, hops, nhip)"
    shows "  dsn = (case dests dip of None \<Rightarrow> \<pi>\<^sub>2(the (rt dip)) | Some rsn \<Rightarrow> rsn)
           \<and> dsk = \<pi>\<^sub>3(the (rt dip))
           \<and> flag = (if dests dip = None then \<pi>\<^sub>4(the (rt dip)) else inv)
           \<and> hops = \<pi>\<^sub>5(the (rt dip))
           \<and> nhip = \<pi>\<^sub>6(the (rt dip))"
  using assms unfolding invalidate_def
  by (cases "rt dip", clarsimp, cases "dests dip") auto


lemma proj3_inv: "\<And>dip rt dests. dip\<in>kD (rt)
                      \<Longrightarrow> \<pi>\<^sub>3(the (invalidate rt dests dip)) = \<pi>\<^sub>3(the (rt dip))"
  by (clarsimp simp: invalidate_def kD_def split: option.split)

lemma dests_iD_invalidate [simp]:
  assumes "dests ip = Some rsn"
      and "ip\<in>kD(rt)"
    shows "ip\<in>iD(invalidate rt dests)"
  using assms(1) assms(2) [THEN kD_Some] unfolding invalidate_def iD_def
  by (clarsimp split: option.split)

subsection "Route Requests"

text \<open>Generate a fresh route request identifier.\<close>

definition nrreqid :: "(ip \<times> rreqid) set \<Rightarrow> ip \<Rightarrow> rreqid"
  where "nrreqid rreqs ip \<equiv> Max ({n. (ip, n) \<in> rreqs} \<union> {0}) + 1"

subsection "Queued Packets"

text \<open>Functions for sending data packets.\<close>

type_synonym store = "ip \<rightharpoonup> (p \<times> data list)"

definition sigma_queue :: "store \<Rightarrow> ip \<Rightarrow> data list"    ("\<sigma>\<^bsub>queue\<^esub>'(_, _')")
  where "\<sigma>\<^bsub>queue\<^esub>(store, dip) \<equiv> case store dip of None \<Rightarrow> [] | Some (p, q) \<Rightarrow> q"

definition qD :: "store \<Rightarrow> ip set"
  where "qD \<equiv> dom"

definition add :: "data \<Rightarrow> ip \<Rightarrow> store \<Rightarrow> store"
  where "add d dip store \<equiv> case store dip of
                              None \<Rightarrow> store (dip \<mapsto> (req, [d]))
                            | Some (p, q) \<Rightarrow> store (dip \<mapsto> (p, q @ [d]))"

lemma qD_add [simp]:
  fixes d dip store
  shows "qD(add d dip store) = insert dip (qD store)"
  unfolding add_def Let_def qD_def
  by (clarsimp split: option.split)

definition drop :: "ip \<Rightarrow> store \<rightharpoonup> store"
  where "drop dip store \<equiv>
    map_option (\<lambda>(p, q). if tl q = [] then store (dip := None)
                                      else store (dip \<mapsto> (p, tl q))) (store dip)"

definition sigma_p_flag :: "store \<Rightarrow> ip \<rightharpoonup> p" ("\<sigma>\<^bsub>p-flag\<^esub>'(_, _')")
  where "\<sigma>\<^bsub>p-flag\<^esub>(store, dip) \<equiv> map_option fst (store dip)"

definition unsetRRF :: "store \<Rightarrow> ip \<Rightarrow> store"
  where "unsetRRF store dip \<equiv> case store dip of
                                None \<Rightarrow> store
                              | Some (p, q) \<Rightarrow> store (dip \<mapsto> (noreq, q))"

definition setRRF :: "store \<Rightarrow> (ip \<rightharpoonup> sqn) \<Rightarrow> store"
  where "setRRF store dests \<equiv> \<lambda>dip. if dests dip = None then store dip
                                    else map_option (\<lambda>(_, q). (req, q)) (store dip)"

subsection "Comparison with the original technical report"

text \<open>
  The major differences with the AODV technical report of Fehnker et al are:
  \begin{enumerate}
  \item @{term nhop} is partial, thus a `@{term the}' is needed, similarly for @{term dhops}
        and @{term addpreRT}.
  \item @{term precs} is partial.
  \item @{term "\<sigma>\<^bsub>p-flag\<^esub>(store, dip)"} is partial.
  \item The routing table (@{typ rt}) is modelled as a map (@{typ "ip \<Rightarrow> r option"})
        rather than a set of 7-tuples, likewise, the @{typ r} is a 6-tuple rather than
        a 7-tuple, i.e., the destination ip-address (@{term "dip"}) is taken from the
        argument to the function, rather than a part of the result. Well-definedness then
        follows from the structure of the type and more related facts are available
        automatically, rather than having to be acquired through tedious proofs.
  \item Similar remarks hold for the dests mapping passed to @{term "invalidate"},
        and @{term "store"}.
  \end{enumerate}
\<close>

end

