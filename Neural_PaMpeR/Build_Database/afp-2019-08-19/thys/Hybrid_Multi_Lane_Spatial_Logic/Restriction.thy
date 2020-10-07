(*  Title:      Restriction.thy
    Author:     Sven Linker

Restrict a function from cars to lanes to a given view. Will be
used for claim and reservation functions of Traffic Snapshots.
*)

section\<open>Restrict Claims and Reservations to a View\<close>
text \<open>
To model that a view restricts the number of lanes a car may 
perceive, we define a function \(restrict\) taking a view \(v\), a function
\(f\) from cars to lanes and a car \(f\), and returning the intersection
between \(f(c)\) and the set of lanes of \(v\). This function
will in the following only be applied to the functions yielding
reservations and claims from traffic snapshots. 

The lemmas of this section describe the connection between 
\(restrict\) and the different operations on traffic snapshots
and views (e.g., the transition relations or the fact that 
reservations and claims are consecutive).
\<close>

theory Restriction
  imports Traffic Views
begin
  
locale restriction = view+traffic
begin
  
  
definition restrict :: "view \<Rightarrow> (cars \<Rightarrow> lanes) \<Rightarrow> cars \<Rightarrow> lanes"
  where  "restrict v f c ==  (f c) \<sqinter>  lan v"  
    
lemma restrict_def':" restrict v f c = lan v \<sqinter> f c"
  using inf_commute restriction.restrict_def by auto
    
lemma restrict_subseteq:"restrict v f c \<sqsubseteq> f c"
  using inf_le1 restrict_def by auto
    
lemma restrict_clm : "restrict v (clm ts) c \<sqsubseteq> clm ts c" 
  using inf_le1 restrict_def by auto
    
lemma restrict_res: "restrict v (res ts) c \<sqsubseteq> res ts c"
  using inf_le1 restrict_def by auto
    
lemma restrict_view:"restrict v f c \<sqsubseteq> lan v"
  using inf_le1 restrict_def by auto
    
lemma restriction_stable:"(v=u\<parallel>w) \<longrightarrow> restrict u f  c = restrict w f  c"
  using hchop_def restrict_def by auto
    
lemma restriction_stable1:"(v=u\<parallel>w) \<longrightarrow> restrict v f  c = restrict u f  c"
  by (simp add: hchop_def restrict_def)
    
lemma restriction_stable2:"(v=u\<parallel>w) \<longrightarrow> restrict v f  c = restrict w f  c"
  by (simp add: restriction_stable restriction_stable1)
    
lemma restriction_un:
  "(v=u--w) \<longrightarrow> restrict v f c = (restrict u f c \<squnion> restrict w f c)"
  using nat_int.inter_distr1 nat_int.inter_empty1 nat_int.un_empty_absorb1
    nat_int.un_empty_absorb2 nat_int.nchop_def restrict_def vchop_def 
  by auto
    
lemma restriction_mon1:"(v=u--w) \<longrightarrow> restrict u f c \<sqsubseteq> restrict v f c" 
  using inf_mono nat_int.chop_subset1 restrict_def vchop_def
  by (metis (no_types, hide_lams) order_refl)
    
lemma restriction_mon2:"(v=u--w) \<longrightarrow> restrict w f c \<sqsubseteq> restrict v f c" 
  using inf_mono nat_int.chop_subset2 restrict_def vchop_def 
  by (metis (no_types, hide_lams) order_refl)

lemma restriction_disj:"(v=u--w) \<longrightarrow> (restrict u f c) \<sqinter> (restrict w f c) = \<emptyset>" 
proof
  assume assm: "v=u--w"
  then have 1:"lan u \<sqinter> lan w = \<emptyset>" using vchop_def 
    by (metis inf_commute inter_empty1 nat_int.consec_inter_empty nat_int.nchop_def)
  from assm have "(restrict u f c) \<sqinter> (restrict w f c) \<sqsubseteq> lan u \<sqinter> lan w " 
    by (meson inf_mono restriction.restrict_view)
  with 1 show  "(restrict u f c) \<sqinter> (restrict w f c) = \<emptyset>" 
    by (simp add: bot.extremum_uniqueI)
qed

lemma vertical_chop_restriction_res_consec_or_empty:
  "(v=v1--v2) \<and> restrict v1 (res ts) c \<noteq> \<emptyset> \<and> consec ((lan v1)) ((lan v2)) \<and>  
    \<not>consec (restrict v1 (res ts) c) (restrict v2 (res ts) c) 
      \<longrightarrow> restrict v2 (res ts) c = \<emptyset>" 
proof
  assume assm:
    "(v=v1--v2) \<and> restrict v1 (res ts) c \<noteq> \<emptyset> \<and>
      consec ((lan v1)) ((lan v2)) \<and> 
      \<not>consec (restrict v1 (res ts) c) (restrict v2 (res ts) c)"
  hence "restrict v1 (res ts) c = \<emptyset> \<or> restrict v2 (res ts) c = \<emptyset> \<or>
   (maximum (restrict v1 (res ts) c)+1 \<noteq>minimum (restrict v2 (res ts) c))"
    using nat_int.consec_def by blast
  hence empty_or_non_consec:"restrict v2 (res ts) c = \<emptyset> \<or> 
    (maximum (restrict v1 (res ts) c)+1 \<noteq>minimum (restrict v2 (res ts) c))"
    using assm by blast
  have consec_lanes:"consec ((lan v1)) ((lan v2))" by (simp add: assm)
  have subs:"restrict v2 (res ts) c \<sqsubseteq> ((lan v2))" using restrict_view
    by simp
  show "restrict v2 (res ts) c = \<emptyset>" 
  proof (rule ccontr)
    assume non_empty:"restrict v2 (res ts) c \<noteq> \<emptyset>"
    hence max:
      "(maximum (restrict v1 (res ts) c)+1 \<noteq>minimum (restrict v2 (res ts) c))"
      using empty_or_non_consec by blast
    have ex_n:" \<exists>n. n \<in> Rep_nat_int (restrict v2 (res ts) c)" 
      using nat_int.el.rep_eq non_empty nat_int.non_empty_elem_in by auto
    have res1_or2:"|(res ts) c| = 1 \<or> |(res ts) c| = 2" 
      by (metis Suc_1 atLeastOneRes atMostTwoRes dual_order.antisym le_SucE)
    then show False 
    proof
      assume res_one:"|(res ts) c|=1"
      then obtain n where one_lane:"Rep_nat_int ((res ts) c) =  {n}" 
        using singleton by blast 
      then have "n \<in> Rep_nat_int (restrict v1 (res ts) c)"
        by (metis assm equals0D nat_int.el.rep_eq less_eq_nat_int.rep_eq 
            nat_int.non_empty_elem_in restrict_res singletonI subset_singletonD)
      then have "Rep_nat_int (restrict v2 (res ts) c) = {}" 
        by (metis one_lane assm inf.absorb1 less_eq_nat_int.rep_eq restriction.restrict_res
            restriction_disj subset_singleton_iff)
      thus False 
        using ex_n by blast
    next
      assume res_two:"|(res ts) c| = 2"
      hence ex_two_ln:" (\<exists>n . Rep_nat_int ((res ts) c) = {n,n+1})" 
        using consecutiveRes by blast
      then obtain n where n_def:"Rep_nat_int ((res ts) c) = {n,n+1}"  by blast
      hence rep_restrict_v1:"Rep_nat_int (restrict v1 (res ts) c) \<subseteq> {n,n+1}" 
        using less_eq_nat_int.rep_eq restrict_res by blast
      hence 
        "n \<in> Rep_nat_int (restrict v1 (res ts) c) \<or> 
         n+1 \<in> Rep_nat_int(restrict v1 (res ts) c)"
        using assm bot.extremum_unique less_eq_nat_int.rep_eq by fastforce
      thus False
      proof
        assume suc_n_in_res_v1:"n+1 \<in> Rep_nat_int (restrict v1 (res ts) c)"
        hence suc_n_in_v1:"n+1 \<in> Rep_nat_int ((lan v1))" 
          using less_eq_nat_int.rep_eq restrict_view by blast
        hence  "n+1 \<notin> Rep_nat_int (lan v2)" 
          using assm vchop_def nat_int.nchop_def nat_int.consec_in_exclusive1 
            nat_int.el.rep_eq nat_int.not_in.rep_eq by blast
        hence suc_n_not_in_res_v2:"n+1 \<notin> Rep_nat_int (restrict v2 (res ts) c)" 
          using less_eq_nat_int.rep_eq subs by blast 
        have "\<forall>m . m \<^bold>\<in> lan v2 \<longrightarrow> m \<ge> minimum (lan v2)" 
          by (metis consec_lanes nat_int.minimum_def nat_int.consec_def 
            nat_int.el.rep_eq atLeastAtMost_iff nat_int.leq_min_inf
            nat_int.rep_non_empty_means_seq)
        then have "\<forall>m . m \<^bold>\<in> lan v2 \<longrightarrow> m > maximum (lan v1)" 
          using assm nat_int.consec_def by fastforce
        then have "\<forall>m . m \<^bold>\<in> lan v2 \<longrightarrow> m > n+1" 
          using consec_lanes nat_int.maximum_def nat_int.card_seq 
            nat_int.consec_def suc_n_in_v1
          by (simp add: nat_int.consec_lesser)
        then have "n \<notin> Rep_nat_int ((lan v2))" 
          using suc_n_in_v1 assm nat_int.consec_def nat_int.el.rep_eq
          by auto
        hence "n\<notin> Rep_nat_int (restrict v2 (res ts) c)"
          using less_eq_nat_int.rep_eq rev_subsetD subs by blast
        hence "Rep_nat_int (restrict v2 (res ts) c) = {}" 
          using insert_absorb insert_ident insert_not_empty n_def less_eq_nat_int.rep_eq
            restrict_res singleton_insert_inj_eq subset_insert suc_n_not_in_res_v2 
          by fastforce
        thus False using ex_n by blast
      next
        assume n_in_res_v1:"n \<in> Rep_nat_int (restrict v1 (res ts) c)"
        hence n_not_in_v2:"n \<notin> Rep_nat_int ((lan v2))" 
          using assm vchop_def nat_int.nchop_def  nat_int.consec_in_exclusive1 
            nat_int.consec_in_exclusive2 nat_int.el.rep_eq nat_int.not_in.rep_eq
          by (meson less_eq_nat_int.rep_eq restrict_view subsetCE)
        hence n_not_in_res_v2:"n \<notin> Rep_nat_int (restrict v2 (res ts) c)" 
          using less_eq_nat_int.rep_eq subs by blast 
        show False
        proof (cases "n+1 \<in> Rep_nat_int(restrict v2 (res ts) c) ")
          case False
          hence "Rep_nat_int (restrict v2 (res ts) c) = {}"
            using insert_absorb insert_ident insert_not_empty n_def n_not_in_res_v2
              less_eq_nat_int.rep_eq restrict_res singleton_insert_inj_eq' subset_insert 
            by fastforce
          thus False using ex_n by blast
        next
          case True
          obtain NN :: "nat set \<Rightarrow> nat \<Rightarrow> nat set" where
            "\<forall>x0 x1. (\<exists>v2. x0 = insert x1 v2 \<and> x1 \<notin> v2) 
              = (x0 = insert x1 (NN x0 x1) \<and> x1 \<notin> NN x0 x1)"
            by moura
          then have f1: 
            "Rep_nat_int (restrict v2 (res ts) c) = 
              insert (n + 1) (NN (Rep_nat_int (restrict v2 (res ts) c)) (n + 1)) 
             \<and> n + 1 \<notin> NN (Rep_nat_int (restrict v2 (res ts) c)) (n + 1)"
            by (meson mk_disjoint_insert True)
          then have 
            "insert (n + 1) (NN (Rep_nat_int (restrict v2 (res ts) c)) (n+1)) 
              \<subseteq> {n+1}\<union>{}"
            by (metis (no_types) insert_is_Un n_def n_not_in_res_v2 less_eq_nat_int.rep_eq
                restrict_res subset_insert)
          then have "{n + 1} = Rep_nat_int (restrict v2 (res ts) c)"
            using f1 by blast
          then have min:"nat_int.minimum (restrict v2 (res ts) c) = n+1" 
            by (metis (no_types) Min_singleton nat_int.minimum_def non_empty)              
          then have suc_n_in_v2:"n+1 \<^bold>\<in> (lan v2)"
            using nat_int.el.rep_eq less_eq_nat_int.rep_eq subs True
            by auto
          have "\<forall>m . m \<^bold>\<in> lan v1 \<longrightarrow> m \<le> maximum (lan v1)" 
            by (metis atLeastAtMost_iff consec_lanes nat_int.maximum_def  nat_int.consec_def
              nat_int.el.rep_eq nat_int.leq_max_sup nat_int.rep_non_empty_means_seq)
          then have "\<forall>m . m \<^bold>\<in> lan v1 \<longrightarrow> m < minimum (lan v2)" using assm 
            using nat_int.consec_lesser nat_int.minimum_in nat_int.consec_def 
            by auto 
          then have "\<forall>m . m \<^bold>\<in> lan v1 \<longrightarrow> m < n+1" 
            using consec_lanes  nat_int.card_seq nat_int.consec_def suc_n_in_v2 
              nat_int.consec_lesser by auto
          then have suc_n_not_in_v1:"n+1 \<notin> Rep_nat_int ((lan v1))" 
            using nat_int.el.rep_eq by auto
          have suc_n_not_in_res_v1:"n+1 \<notin> Rep_nat_int (restrict v1 (res ts) c)" 
            using less_eq_nat_int.rep_eq restrict_view suc_n_not_in_v1 by blast
          from rep_restrict_v1 and n_in_res_v1 have res_v1_singleton:
            "Rep_nat_int (restrict v1 (res ts) c) = {n}"
            using Set.set_insert insert_absorb2 insert_commute singleton_insert_inj_eq'
              subset_insert suc_n_not_in_res_v1 by blast
          have max: "nat_int.maximum (restrict v1 (res ts) c) = n" 
            by (metis Rep_nat_int_inverse nat_int.leq_max_sup' order_refl 
                res_v1_singleton nat_int.rep_single)
          from min and max have 
            "maximum (restrict v1 (res ts) c)+1 = minimum (restrict v2 (res ts) c)"
            by auto
          thus False 
            using empty_or_non_consec non_empty by blast
        qed
      qed
    qed
  qed
qed
  
lemma restriction_consec_res:"(v=u--w) 
  \<longrightarrow> restrict u (res ts) c = \<emptyset> \<or> restrict w (res ts) c = \<emptyset> 
  \<or>  consec (restrict u (res ts) c) ( restrict w (res ts) c)" 
proof
  assume assm:"v=u--w"
  then show "restrict u (res ts) c = \<emptyset> \<or> restrict w (res ts) c = \<emptyset> 
  \<or>  consec (restrict u (res ts) c) ( restrict w (res ts) c)" 
  proof (cases "res ts c =\<emptyset>")
    case True
    show ?thesis 
      by (simp add: True inter_empty1 restriction.restrict_def')
  next
    case False
    then have "res ts c \<noteq> \<emptyset>" by best
    show ?thesis 
      by (metis (no_types, lifting) assm inter_empty1 nat_int.nchop_def 
          restriction.restrict_def restriction.vertical_chop_restriction_res_consec_or_empty
          view.vchop_def)
  qed
qed

lemma restriction_clm_res_disjoint:
  "(restrict v (res ts) c) \<sqinter> (restrict v (clm ts) c) = \<emptyset>"
  by (metis (no_types) inf_assoc nat_int.inter_empty2 restriction.restrict_def
      restrict_def' traffic.disjoint)
    
lemma el_in_restriction_clm_singleton:
  "n \<^bold>\<in> restrict v (clm ts) c \<longrightarrow> (clm ts) c = Abs_nat_int({n})" 
proof
  assume n_in_restr:"n \<^bold>\<in> restrict v (clm ts) c"
  hence "n \<^bold>\<in> ((clm ts) c \<sqinter> (lan v))" by (simp add: restrict_def)
  hence "n \<in> (Rep_nat_int (clm ts c) \<inter> Rep_nat_int (lan v))" 
    by (simp add: inf_nat_int.rep_eq nat_int.el_def)
  hence n_in_rep_clm:"n \<in> (Rep_nat_int ((clm ts) c))" by simp
  then have "(clm ts) c \<noteq> \<emptyset>" using nat_int.el.rep_eq nat_int.non_empty_elem_in 
    by auto
  then have "|(clm ts) c| \<ge> 1" 
    by (simp add: nat_int.card_non_empty_geq_one)
  then have "|(clm ts) c| = 1" using atMostOneClm le_antisym 
    by blast
  with n_in_rep_clm show "(clm ts) c = Abs_nat_int({n})"
    by (metis Rep_nat_int_inverse nat_int.singleton singletonD)
qed
  
lemma restriction_clm_v2_non_empty_v1_empty:
  "(v=u--w) \<and> restrict w (clm ts) c \<noteq> \<emptyset> \<and>  
    consec ((lan u)) ((lan w)) \<longrightarrow> restrict u (clm ts) c = \<emptyset>"
proof
  assume assm:"(v=u--w) \<and> restrict w (clm ts) c \<noteq> \<emptyset> \<and> consec (lan u) (lan w)"
  obtain n where n_in_res_v2: "(n \<^bold>\<in> restrict w (clm ts) c)" 
    using assm maximum_in by blast
  have "(clm ts) c = Abs_nat_int({n})" 
    using n_in_res_v2  by (simp add: el_in_restriction_clm_singleton)   
  then show "restrict u (clm ts) c = \<emptyset>" 
    by (metis assm inf.absorb_iff2 inf_commute less_eq_nat_int.rep_eq 
        n_in_res_v2 nat_int.el.rep_eq nat_int.in_singleton restriction.restrict_subseteq
        restriction.restriction_disj subsetI) 
qed
  
lemma restriction_consec_clm:
  "(v=u--w) \<and> consec (lan u) (lan w) 
    \<longrightarrow> restrict u (clm ts) c = \<emptyset> \<or> restrict w (clm ts) c = \<emptyset>"
  using nat_int.card_un_add nat_int.card_empty_zero restriction_un atMostOneClm
    nat_int.chop_add1 nat_int.inter_distr1 nat_int.inter_empty1 nat_int.un_empty_absorb1
    nat_int.un_empty_absorb2 nat_int.nchop_def restrict_def vchop_def 
    restriction_clm_v2_non_empty_v1_empty
  by meson
    
    
    
lemma restriction_add_res:
  "(v=u--w) 
    \<longrightarrow> |restrict v (res ts) c|=|restrict u (res ts) c|+|restrict w (res ts) c|"
proof 
  assume assm: "v=u--w"
  then have 1:"restrict u (res ts) c \<sqinter> restrict w (res ts) c = \<emptyset>" 
    using restriction.restriction_disj by auto
  from assm have "restrict v (res ts) c=restrict u (res ts) c\<squnion>restrict w (res ts) c" 
    using restriction.restriction_un by blast
  with 1 show " |restrict v (res ts) c|=|restrict u (res ts) c|+|restrict w (res ts) c|" 
    by (metis add.right_neutral add_cancel_left_left assm nat_int.card_empty_zero
        nat_int.card_un_add nat_int.un_empty_absorb1 nat_int.un_empty_absorb2 
        restriction.restriction_consec_res)
qed    
  
lemma restriction_eq_view_card:"restrict v f c = lan v \<longrightarrow> |restrict v f c| =|lan v|" 
  by simp
    
lemma restriction_card_mon1:"(v=u--w) \<longrightarrow> |restrict u f c| \<le> |restrict v f c|"
  using nat_int.card_subset_le restriction_mon1 by (simp )
    
lemma restriction_card_mon2:"(v=u--w) \<longrightarrow> |restrict w f c| \<le> |restrict v f c|"
  using nat_int.card_subset_le restriction_mon2 by (simp )
    
lemma restriction_res_leq_two:"|restrict v (res ts) c| \<le> 2"
  using atMostTwoRes nat_int.card_subset_le le_trans restrict_res
  by metis
    
lemma restriction_clm_leq_one:"|restrict v (clm ts) c| \<le> 1"
  using atMostOneClm nat_int.card_subset_le le_trans restrict_clm
  by metis
    

lemma restriction_add_clm:
  "(v=u--w) 
    \<longrightarrow> |restrict v (clm ts) c|=|restrict u (clm ts) c|+|restrict w (clm ts) c|" 
proof
  assume assm:"v=u--w"
  have "|restrict u (clm ts) c| = 1 \<or> |restrict u (clm ts) c| = 0" 
    by (metis One_nat_def le_0_eq le_SucE restriction.restriction_clm_leq_one)
  then show "|restrict v (clm ts) c|=|restrict u (clm ts) c|+|restrict w (clm ts) c|"
  proof
    assume clm_u:"|restrict u (clm ts) c| = 1"
    have "restrict u (clm ts) c \<noteq> \<emptyset>"
      using clm_u card_non_empty_geq_one by auto
    then have "|restrict w (clm ts) c| = 0" 
      by (metis (no_types) assm card_empty_zero inf_commute inter_empty2
          nat_int.nchop_def restriction.restrict_def 
          restriction.restriction_clm_v2_non_empty_v1_empty view.vchop_def)
    then show ?thesis 
      by (metis Nat.add_0_right assm clm_u inf.absorb1 inf_commute 
          restriction.restriction_card_mon1 restriction.restriction_clm_leq_one)
  next
    assume no_clm_u:"|restrict u (clm ts) c| = 0" 
    then have "|restrict w (clm ts) c| = 1 \<or> |restrict w (clm ts) c| = 0" 
      by (metis One_nat_def le_0_eq le_SucE restriction.restriction_clm_leq_one)
    then show ?thesis 
    proof
      assume "|restrict w (clm ts) c| = 1"
      then show ?thesis 
        by (metis no_clm_u add_cancel_left_left antisym_conv3 assm leD 
            restriction.restriction_card_mon2 restriction.restriction_clm_leq_one)
    next
      assume no_clm_w:"|restrict w (clm ts) c| = 0"
      then have "|restrict v (clm ts) c| = 0" 
        by (metis assm card_empty_zero chop_empty 
            nat_int.card_non_empty_geq_one nat_int.nchop_def no_clm_u 
            restriction.restriction_un)
      then show ?thesis
        using no_clm_u no_clm_w by linarith
    qed
  qed
qed

lemma restriction_card_mon_trans:
  "(v=v1--v2) \<and> (v2=v3--v4) \<and> |restrict v3 f c| = 1 \<longrightarrow> |restrict v f c|\<ge>1"
  by (metis One_nat_def Suc_leI neq0_conv not_less_eq_eq 
      restriction_card_mon1 restriction_card_mon2)

    
lemma restriction_card_somewhere_mon:
  "(v=vl\<parallel>v1)\<and>(v1=v2\<parallel>vr)\<and>(v2=vu--v3)\<and>(v3=v'--vd)\<and>|restrict v' f c|=1
      \<longrightarrow> |restrict v f c| \<ge> 1" 
proof
  assume assm:
    "(v=vl\<parallel>v1)\<and>(v1=v2\<parallel>vr)\<and>(v2=vu--v3)\<and>(v3=v'--vd)\<and>|restrict v' f c|=1"
  then have "|restrict v2 f c| \<ge> 1" using restriction_card_mon_trans by blast
  then show "|restrict v f c| \<ge> 1" using restriction_stable1 restriction_stable2 assm
    by metis
qed
  
lemma restrict_eq_lan_subs:
  "|restrict v f c| = |lan v| \<and> (restrict v f c \<sqsubseteq> lan v) \<longrightarrow> restrict v f c = lan v" 
proof
  assume assm:"|restrict v f c| = |lan v| \<and> (restrict v f c \<sqsubseteq> lan v)" 
  have "|restrict v f c| = 0 \<or> |restrict v f c| \<noteq> 0" by auto
  thus "restrict v f c = lan v"
  proof (cases "|restrict v f c| = 0")
    case True
    then have res_empty:"restrict v f c = \<emptyset>" 
      by (metis nat_int.card_non_empty_geq_one nat_int.card_empty_zero)
    then have "lan v = \<emptyset>" 
      by (metis assm nat_int.card_empty_zero nat_int.card_non_empty_geq_one)
    then show "restrict v f c = lan v" 
      using res_empty by auto
  next
    case False
    show "restrict v f c = lan v" 
    proof (rule ccontr)
      assume non_eq:"restrict v f c \<noteq> lan v"
       then have "restrict v f c < lan v" 
         by (simp add: assm less_le)
       then have "|restrict v f c| < |lan v|" 
         using card_subset_less by blast
       then show False using assm by simp
    qed
  qed
qed
  
lemma create_reservation_restrict_union:
  "(ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts') 
    \<longrightarrow> restrict v (res ts') c = restrict v (res ts) c \<squnion> restrict v (clm ts) c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(c)\<^bold>\<rightarrow>ts')"
  hence res_ts':"res ts' c = res ts c \<squnion> clm ts c" 
    by (simp add: create_reservation_def)
  show " restrict v (res ts') c = restrict v (res ts) c \<squnion> restrict v (clm ts) c"
  proof (cases "clm ts c = \<emptyset>")
    case True
    hence res_ts'eq_ts:"res ts' c = res ts c" 
      using res_ts' nat_int.un_empty_absorb1 by simp
    from True have restrict_clm:"restrict v (clm ts) c = \<emptyset>" 
      using nat_int.inter_empty2 restrict_def by simp 
    from res_ts'eq_ts have "restrict v (res ts') c = restrict v (res ts) c" 
      by (simp add: restrict_def)
    thus ?thesis using restrict_clm 
      by (simp add: nat_int.un_empty_absorb1)
  next 
    case False
    hence "consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)" 
      by (simp add: clm_consec_res)
    thus ?thesis 
    proof
      assume consec:"consec (clm ts c) (res ts c)"
      then show ?thesis 
        using inter_distr1 res_ts' restriction.restrict_def 
        by (simp add: Un_ac(3) inf_commute nat_int.union_def)
    next
      assume consec:"consec (res ts c) (clm ts c)"
      then show ?thesis 
        by (simp add: inter_distr2 res_ts' restriction.restrict_def)
    qed
  qed
qed
  
  (* switch lemmas *)
lemma switch_restrict_stable:"(v=c>u) \<longrightarrow> restrict v f d = restrict u f d"
  using switch_def by (simp add: restrict_def) 
end
end
