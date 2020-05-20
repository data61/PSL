(*  Title:      Traffic.thy
    Author:     Sven Linker

Defines a type for traffic snapshots. Consists of six elements:
pos: positions of cars
res: reservations of cars
clm: claims of cars
dyn: current dynamic behaviour of cars
physical_size: the real sizes of cars
braking_distance: braking distance each car needs in emergency

Definitions for transitions between traffic snapshots.
*)

section\<open>Traffic Snapshots\<close> 
text\<open>
Traffic snapshots define the spatial and dynamical arrangement of cars
on the whole of the motorway at a single point in time. A traffic snapshot
consists of several functions assigning spatial properties and dynamical
behaviour to each car. The functions are named as follows.
\begin{itemize}
\item pos: positions of cars
\item res: reservations of cars
\item clm: claims of cars
\item dyn: current dynamic behaviour of cars
\item physical\_size: the real sizes of cars
\item braking\_distance: braking distance each car needs in emergency
\end{itemize}
\<close>

theory Traffic
imports NatInt RealInt Cars
begin

type_synonym lanes = nat_int
type_synonym extension = real_int

text \<open>Definition of the type of traffic snapshots. 
The constraints on the different functions are the \emph{sanity conditions}
of traffic snapshots.\<close>

typedef traffic = 
  "{ts :: (cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
          (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
          (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
          (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
          (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
          (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
          (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow>
                (\<exists> n. Rep_nat_int(fst (snd ts) c)\<union>Rep_nat_int(fst (snd (snd ts)) c)
                      = {n, n+1})) \<and>
          (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
          (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)
 } "
proof -
  let ?type = 
    "{ts ::(cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
           (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
           (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
           (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
           (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow> 
                (\<exists> n. Rep_nat_int(fst (snd ts) c)\<union>Rep_nat_int(fst (snd (snd ts)) c)
                  = {n, n+1})) \<and>
           (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
           (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0)  
 }"
  obtain pos where sp_def:"\<forall>c::cars. pos c = (1::real)" by force
  obtain re where re_def:"\<forall>c::cars. re c = Abs_nat_int {1}" by force
  obtain cl where cl_def:"\<forall>c::cars. cl c = \<emptyset>" by force
  obtain dyn where dyn_def:"\<forall>c::cars. \<forall>x::real . (dyn c) x  = (0::real)"  by force
  obtain ps where ps_def :"\<forall>c::cars . ps c = (1::real)" by force
  obtain sd where sd_def:"\<forall>c::cars . sd c = (1::real)" by force
  obtain ts where ts_def:"ts =  (pos,re,cl, dyn, ps, sd)" by simp

  have disj:"\<forall>c .((re c) \<sqinter> (cl c) = \<emptyset>)" 
    by (simp add: cl_def nat_int.inter_empty1)
  have re_geq_one:"\<forall>c. |re c| \<ge> 1" 
    by (simp add: Abs_nat_int_inverse re_def)
  have re_leq_two:"\<forall>c. |re c| \<le> 2" 
    using re_def nat_int.rep_single by auto
  have cl_leq_one:"\<forall>c. |cl c| \<le> 1"
    using nat_int.card_empty_zero cl_def by auto
  have add_leq_two:"\<forall>c . |re c| + |cl c| \<le> 2"
    using nat_int.card_empty_zero cl_def re_leq_two by (simp )
  have consec_re:" \<forall>c. |(re c)| =2 \<longrightarrow> (\<exists>n . Rep_nat_int (re c) = {n,n+1})" 
    by (simp add: Abs_nat_int_inverse  re_def)
  have  clNextRe :
    "\<forall>c. ((cl c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int (re c) \<union> Rep_nat_int (cl c) = {n, n+1}))"
    by (simp add: cl_def)
  from dyn_def have dyn_geq_zero:"\<forall>c. \<forall>x. dyn(c) x \<ge> 0" 
    by auto
  from ps_def have ps_ge_zero:"\<forall>c. ps c > 0" by auto
  from sd_def have sd_ge_zero:"\<forall>c. sd c > 0" by auto
  
  have "ts\<in>?type"
    using sp_def re_def cl_def disj re_geq_one re_leq_two cl_leq_one add_leq_two
      consec_re ps_def sd_def ts_def by auto
  thus ?thesis by blast
qed 

locale traffic
begin   

notation nat_int.consec ("consec")

text\<open>For brevity, we define names for the different functions
within a traffic snapshot.\<close>

definition pos::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "pos ts \<equiv> fst (Rep_traffic ts)"

definition res::"traffic \<Rightarrow> (cars \<Rightarrow> lanes)"
where "res ts \<equiv> fst (snd (Rep_traffic ts))"

definition clm ::"traffic \<Rightarrow> (cars \<Rightarrow> lanes)"
where "clm ts \<equiv> fst (snd (snd (Rep_traffic ts)))"

definition dyn::"traffic \<Rightarrow> (cars \<Rightarrow> (real\<Rightarrow> real))"
where "dyn ts \<equiv> fst (snd (snd (snd (Rep_traffic ts))))"

definition physical_size::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "physical_size ts \<equiv> fst (snd (snd (snd (snd (Rep_traffic ts)))))"

definition braking_distance::"traffic \<Rightarrow> (cars \<Rightarrow> real)"
where "braking_distance ts \<equiv> snd (snd (snd (snd (snd (Rep_traffic ts)))))"


text \<open>
It is helpful to be able to refer to the sanity conditions of a traffic 
snapshot via lemmas, hence we prove that the sanity conditions hold
for each traffic snapshot.
\<close>

lemma disjoint: "(res ts c) \<sqinter> (clm ts c) = \<emptyset>"
using Rep_traffic res_def clm_def   by auto 

lemma atLeastOneRes: "1 \<le> |res ts c|" 
using Rep_traffic  res_def by auto 

lemma atMostTwoRes:" |res ts c| \<le> 2"
using Rep_traffic  res_def  by auto 

lemma  atMostOneClm: "|clm ts c| \<le> 1" 
using Rep_traffic  clm_def  by auto 

lemma atMostTwoLanes: "|res ts c| +|clm ts c| \<le> 2"
using Rep_traffic  res_def clm_def  by auto 

lemma  consecutiveRes:" |res ts  c| =2 \<longrightarrow> (\<exists>n . Rep_nat_int (res ts c) = {n,n+1})"
proof
  assume assump:"|res ts  c| =2" 
  then have not_empty:"(res ts c) \<noteq> \<emptyset>" 
    by (simp add: card_non_empty_geq_one)
  from assump and card_seq 
  have "Rep_nat_int (res ts  c) = {} \<or> (\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    by (metis add_diff_cancel_left' atLeastAtMost_singleton insert_is_Un nat_int.un_consec_seq
        one_add_one order_refl)  
  with assump show "(\<exists>n . Rep_nat_int (res ts c) = {n,n+1})" 
    using Rep_nat_int_inject bot_nat_int.rep_eq card_non_empty_geq_one 
    by (metis not_empty)
qed
  
lemma clmNextRes : 
  "(clm ts c) \<noteq> \<emptyset> \<longrightarrow> (\<exists> n. Rep_nat_int(res ts c) \<union> Rep_nat_int(clm ts c) = {n, n+1})"
  using Rep_traffic res_def clm_def by auto 

lemma psGeZero:"\<forall>c. (physical_size ts c > 0)"
  using Rep_traffic physical_size_def by auto 

lemma sdGeZero:"\<forall>c. (braking_distance ts c > 0)"
  using Rep_traffic braking_distance_def by auto 

text \<open>
While not a sanity condition directly, the following lemma helps to establish
general properties of HMLSL later on. It is a consequence of clmNextRes. 
\<close>

lemma clm_consec_res: 
"(clm ts) c \<noteq> \<emptyset> \<longrightarrow> consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)" 
proof
  assume assm:"clm ts c \<noteq>\<emptyset>"
  hence adj:"(\<exists> n. Rep_nat_int(res ts c) \<union> Rep_nat_int(clm ts c) = {n, n+1})" 
    using clmNextRes by blast
  obtain n where n_def:"Rep_nat_int(res ts c)\<union>Rep_nat_int(clm ts c) = {n, n+1}" 
    using adj by blast
  have disj:"res ts c \<sqinter> clm ts c = \<emptyset>" using disjoint by blast
  from n_def and disj 
    have "(n \<^bold>\<in> res ts c \<and> n \<^bold>\<notin> clm ts c) \<or> (n \<^bold>\<in> clm ts c \<and> n \<^bold>\<notin> res ts c)" 
      by (metis UnE bot_nat_int.rep_eq disjoint_insert(1) el.rep_eq inf_nat_int.rep_eq
          insertI1 insert_absorb not_in.rep_eq) 
  thus "consec (clm ts c) (res ts c) \<or> consec (res ts c) (clm ts c)" 
  proof
    assume n_in_res: "n \<^bold>\<in> res ts c \<and>  n \<^bold>\<notin> clm ts c"
    hence suc_n_in_clm:"n+1 \<^bold>\<in> clm ts c" 
      by (metis UnCI assm el.rep_eq in_not_in_iff1 insert_iff n_def non_empty_elem_in 
          singletonD)
    have "Rep_nat_int (res ts c) \<noteq> {n, n + 1}" 
      by (metis assm disj n_def inf_absorb1 inf_commute less_eq_nat_int.rep_eq 
          sup.cobounded2)
    then have suc_n_not_in_res:"n+1 \<^bold>\<notin> res ts c" 
      using n_def n_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq
        by auto
    from n_in_res have n_not_in_clm:"n \<^bold>\<notin> clm ts c" by blast
    have max:"nat_int.maximum (res ts c) = n"  
      using n_in_res suc_n_not_in_res nat_int.el.rep_eq nat_int.not_in.rep_eq n_def 
        nat_int.maximum_in nat_int.non_empty_elem_in inf_sup_aci(4) 
      by fastforce 
    have min:"nat_int.minimum (clm ts c) = n+1" 
      using suc_n_in_clm n_not_in_clm nat_int.el.rep_eq nat_int.not_in.rep_eq
        n_def nat_int.minimum_in nat_int.non_empty_elem_in  using inf_sup_aci(4)  
        not_in.rep_eq by fastforce
    show ?thesis 
      using assm max min n_in_res nat_int.consec_def nat_int.non_empty_elem_in
      by auto
  next
    assume n_in_clm: "n \<^bold>\<in> clm ts c \<and> n \<^bold>\<notin> res ts c "
    have suc_n_in_res:"n+1 \<^bold>\<in> res ts c" 
    proof (rule ccontr)
      assume "\<not>n+1 \<^bold>\<in> res ts c"
      then have "n \<^bold>\<in> res ts c " 
        by (metis Int_insert_right_if0 One_nat_def Suc_leI add.right_neutral add_Suc_right 
            atMostTwoRes el.rep_eq inf_bot_right inf_sup_absorb insert_not_empty le_antisym 
            n_def one_add_one order.not_eq_order_implies_strict singleton traffic.atLeastOneRes
            traffic.consecutiveRes)
      then show False using n_in_clm 
        using nat_int.el.rep_eq nat_int.not_in.rep_eq by auto
    qed
    have max:"nat_int.maximum (clm ts c) = n"       
      by (metis Rep_nat_int_inverse assm n_in_clm card_non_empty_geq_one 
          le_antisym nat_int.in_singleton nat_int.maximum_in singleton traffic.atMostOneClm)
    have min:"nat_int.minimum (res ts c) = n+1" 
      by (metis Int_insert_right_if0 Int_insert_right_if1 Rep_nat_int_inverse 
          bot_nat_int.rep_eq el.rep_eq in_not_in_iff1 in_singleton inf_nat_int.rep_eq 
          inf_sup_absorb insert_not_empty inter_empty1 minimum_in n_def 
          n_in_clm suc_n_in_res)
    then show ?thesis 
      using assm max min nat_int.consec_def nat_int.non_empty_elem_in 
        suc_n_in_res by auto
  qed
qed

text \<open>We define several possible transitions between traffic snapshots. 
Cars may create or withdraw claims and reservations, as long as the sanity conditions 
of the traffic snapshots are fullfilled. 

In particular, a car can only create
a claim, if it possesses only a reservation on a single lane, and does not 
already possess a claim. Withdrawing a claim can be done in any situation. 
It only has an effect, if the car possesses a claim. Similarly, the 
transition for a car to create a reservation is always possible, but only
changes the spatial situation on the road, if the car already has a claim.
Finally, a car may withdraw its reservation to a single lane, if its
current reservation consists of two lanes.

All of these transitions concern the spatial properties of a single car at a time, i.e., 
for several cars to change their properties, several transitions have to be taken.
\<close>
  
definition create_claim ::
  "traffic\<Rightarrow>cars\<Rightarrow>nat\<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>c'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> |clm ts c| = 0
                                \<and> |res ts c| = 1
                                \<and> ((n+1) \<^bold>\<in> res ts c \<or> (n-1 \<^bold>\<in> res ts c))
                                \<and> (clm ts') = (clm ts)(c:=Abs_nat_int {n})"

definition withdraw_claim ::
  "traffic\<Rightarrow>cars \<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>wdc'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)"


definition create_reservation ::
  "traffic\<Rightarrow>cars\<Rightarrow>traffic\<Rightarrow>bool" ("_ \<^bold>\<midarrow>r'( _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:=( (res ts c)\<squnion> (clm ts c) ))
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)(c:=\<emptyset>)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)"

definition withdraw_reservation ::
  "traffic\<Rightarrow>cars\<Rightarrow>nat\<Rightarrow>traffic\<Rightarrow> bool" ("_ \<^bold>\<midarrow>wdr'( _, _ ') \<^bold>\<rightarrow> _" 27)
where "  (ts \<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow> ts')  == (pos ts') = (pos ts) 
                                \<and> (res ts') = (res ts)(c:= Abs_nat_int{n} )
                                \<and> (dyn ts') = (dyn ts)
                                \<and> (clm ts') = (clm ts)
                                \<and> (physical_size ts') = (physical_size ts)
                                \<and> (braking_distance ts') = (braking_distance ts)
                                \<and> n \<^bold>\<in> (res ts c)
                                \<and> |res ts c| = 2"

text \<open>
The following two transitions concern the dynamical behaviour of the cars. 
Similar to the spatial properties, a car may change its dynamics, by setting
it to a new function \(f\) from real to real. Observe that this function is indeed 
arbitrary and does not constrain the possible behaviour in any way. However,
this transition allows a car to change the function determining their braking
distance (in fact, all cars are allowed to change this function, if a car changes
sets a new dynamical function). That is, our model describes an over-approximation
of a concrete situation, where the braking distance is determined by the dynamics. 

The final transition describes the passing of \(x\) time units. That is, all cars 
update their position according to their current dynamical behaviour. Observe that
this transition requires that the dynamics of each car is at least \(0\), for each time
point between \(0\) and \(x\). Hence, this condition denotes that all cars drive
into the same direction. If the current dynamics of a car violated this constraint,
it would have to reset its dynamics, until time may pass again.
\<close>

definition change_dyn::
  "traffic\<Rightarrow>cars\<Rightarrow>(real\<Rightarrow>real)\<Rightarrow>traffic\<Rightarrow> bool" (" _ \<^bold>\<midarrow> dyn'(_,_') \<^bold>\<rightarrow> _" 27)
where "(ts \<^bold>\<midarrow>dyn(c, f)\<^bold>\<rightarrow> ts') == (pos ts' = pos ts) 
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = (dyn ts)(c:= f))
                              \<and> (physical_size ts') = (physical_size ts)"


definition drive::
  "traffic\<Rightarrow>real\<Rightarrow>traffic\<Rightarrow>bool" (" _ \<^bold>\<midarrow> _ \<^bold>\<rightarrow> _" 27)
where "(ts \<^bold>\<midarrow> x \<^bold>\<rightarrow> ts') == (\<forall>c. (pos ts' c = (pos ts c) + (dyn ts c x))) 
                              \<and> (\<forall> c y. 0 \<le> y \<and> y \<le> x \<longrightarrow> dyn ts c y \<ge> 0)  
                              \<and> (res ts' = res ts)
                              \<and> (clm ts' = clm ts)
                              \<and> (dyn ts' = dyn ts)
                              \<and> (physical_size ts') = (physical_size ts)
                              \<and> (braking_distance ts') = (braking_distance ts)"

text\<open>
We bundle the dynamical transitions into \emph{evolutions}, since
we will only reason about combinations of the dynamical behaviour. 
This fits to the level of abstraction by hiding the dynamics completely
inside of the model.
\<close>

inductive evolve::"traffic \<Rightarrow> traffic \<Rightarrow> bool" ("_ \<^bold>\<leadsto> _")
where refl : "ts \<^bold>\<leadsto> ts" |
 change: "\<exists>c. \<exists>f. (ts \<^bold>\<midarrow>dyn(c,f)\<^bold>\<rightarrow>ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts'' \<Longrightarrow> ts \<^bold>\<leadsto> ts''" |
 drive:  "\<exists>x. x \<ge> 0 \<and>  ( ts \<^bold>\<midarrow>x\<^bold>\<rightarrow> ts') \<Longrightarrow> ts' \<^bold>\<leadsto> ts''    \<Longrightarrow> ts \<^bold>\<leadsto> ts''" 

lemma evolve_trans:"(ts0 \<^bold>\<leadsto> ts1) \<Longrightarrow> (ts1 \<^bold>\<leadsto> ts2) \<Longrightarrow> (ts0 \<^bold>\<leadsto> ts2)"
proof (induction rule:evolve.induct)
  case (refl ts)
  then show ?case by simp
next
  case (drive ts ts' ts'')
  then show ?case by (metis evolve.drive)
next
  case (change ts ts' ts'')
  then show ?case by (metis evolve.change)
qed

text \<open>
For general transition sequences, we introduce \emph{abstract transitions}. 
A traffic snapshot \(ts^\prime\) is reachable from \(ts\) via an abstract transition,
if there is an arbitrary sequence of transitions from \(ts\) to \(ts^\prime\).
\<close>
 
inductive abstract::"traffic \<Rightarrow> traffic \<Rightarrow> bool"  ("_ \<^bold>\<Rightarrow> _") for ts
where refl: "(ts \<^bold>\<Rightarrow> ts)" |
  evolve:"  ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> ts' \<^bold>\<leadsto> ts''   \<Longrightarrow> ts \<^bold>\<Rightarrow> ts''" |
  cr_clm:" ts \<^bold>\<Rightarrow> ts' \<Longrightarrow>\<exists>c. \<exists> n.  (ts' \<^bold>\<midarrow>c(c,n)\<^bold>\<rightarrow> ts'')     \<Longrightarrow> ts \<^bold>\<Rightarrow> ts''" |
  wd_clm:"ts \<^bold>\<Rightarrow> ts'  \<Longrightarrow> \<exists>c.  (ts' \<^bold>\<midarrow>wdc(c)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" |
  cr_res:"ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> \<exists>c.  (ts' \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" |
  wd_res:"ts \<^bold>\<Rightarrow> ts' \<Longrightarrow> \<exists>c. \<exists> n.  (ts' \<^bold>\<midarrow>wdr(c,n)\<^bold>\<rightarrow> ts'') \<Longrightarrow>  ts \<^bold>\<Rightarrow> ts''" 
  
  
lemma abs_trans:" (ts1 \<^bold>\<Rightarrow> ts2) \<Longrightarrow>(ts0 \<^bold>\<Rightarrow> ts1) \<Longrightarrow> (ts0 \<^bold>\<Rightarrow> ts2)"  
proof (induction  rule:abstract.induct    )
  case refl
  then show ?case by simp
next
  case (evolve ts' ts'')
  then show ?case 
    using traffic.evolve by blast  
next
  case (cr_clm ts' ts'')
  then show ?case 
    using traffic.cr_clm by blast 
next
  case (wd_clm ts' ts'')
  then show ?case 
    using traffic.wd_clm by blast 
next
  case (cr_res ts' ts'')
  then show ?case
    using traffic.cr_res by blast 
next
  case (wd_res ts' ts'')
  then show ?case 
    using traffic.wd_res by blast 
qed


text \<open>
Most properties of the transitions are straightforward. However, to show
that the transition to create a reservation is always possible,
we need to explicitly construct the resulting traffic snapshot. Due
to the size of such a snapshot, the proof is lengthy.
\<close>
  
    
lemma create_res_subseteq1:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "res ts c \<sqsubseteq> res ts' c"
    by (metis (no_types, lifting) Un_commute clm_consec_res  nat_int.un_subset2 
        nat_int.union_def nat_int.chop_subset1 nat_int.nchop_def)
qed

lemma create_res_subseteq2:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts') \<longrightarrow> clm ts c \<sqsubseteq> res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  hence "res ts' c = res ts c \<squnion> clm ts c" using create_reservation_def
    using fun_upd_apply by auto
  thus "clm ts c \<sqsubseteq> res ts' c"
    by (metis Un_commute clm_consec_res disjoint inf_le1 nat_int.un_subset1 nat_int.un_subset2
        nat_int.union_def)
qed

lemma create_res_subseteq1_neq:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c \<longrightarrow> res ts c = res ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c"
  thus "res ts c = res ts' c" using create_reservation_def
  using fun_upd_apply by auto
qed

lemma create_res_subseteq2_neq:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c \<longrightarrow> clm ts c= clm ts' c "
proof
  assume assm:"(ts \<^bold>\<midarrow>r(d)\<^bold>\<rightarrow> ts') \<and> d \<noteq>c"
  thus "clm ts c =  clm ts' c" using create_reservation_def
    using fun_upd_apply by auto
qed


lemma always_create_res:"\<forall>ts. \<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
proof
  let ?type = 
    "{ts ::(cars\<Rightarrow>real)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>lanes)*(cars\<Rightarrow>real\<Rightarrow>real)*(cars\<Rightarrow>real)*(cars\<Rightarrow>real).
           (\<forall>c. ((fst (snd ts))) c \<sqinter> ((fst (snd (snd ts)))) c = \<emptyset> )  \<and>
           (\<forall>c. |(fst (snd ts)) c| \<ge> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| \<le> 2) \<and>
           (\<forall>c. |(fst (snd (snd ts)) c)| \<le> 1) \<and>
           (\<forall>c. |(fst (snd ts)) c| + |(fst (snd (snd ts))) c| \<le> 2) \<and>
           (\<forall>c. (fst(snd(snd (ts)))) c \<noteq> \<emptyset> \<longrightarrow>
                  (\<exists> n. Rep_nat_int(fst (snd ts) c)\<union>Rep_nat_int(fst (snd (snd ts)) c)
                     = {n, n+1})) \<and>
           (\<forall>c . fst (snd (snd (snd (snd (ts))))) c > 0) \<and>
           (\<forall>c.  snd (snd (snd (snd (snd (ts))))) c > 0) 
     }"
  fix ts
  show " \<exists>ts'. (ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts')"
  proof (cases "clm ts c = \<emptyset>")
    case True
    obtain ts' where ts'_def:"ts' = ts" by simp
    then have "ts \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> ts'" 
      using create_reservation_def True fun_upd_triv nat_int.un_empty_absorb1
      by auto
    thus ?thesis ..
  next
    case False
    obtain ts' where ts'_def: "ts'=  (pos ts, 
                                (res ts)(c:=( (res ts c)\<squnion> (clm ts c) )),
                                (clm ts)(c:=\<emptyset>),
                                (dyn ts), (physical_size ts), (braking_distance ts))" 
      by blast
    have disj:"\<forall>c .(((fst (snd ts'))) c \<sqinter> ((fst (snd (snd ts')))) c = \<emptyset>)" 
      by (simp add: disjoint nat_int.inter_empty1 ts'_def)
    have re_geq_one:"\<forall>d. |fst (snd ts') d| \<ge> 1" 
    proof 
      fix d
      show " |fst (snd ts') d| \<ge> 1"
      proof (cases "c = d")
        case True
        then have "fst (snd ts') d = res ts d \<squnion> clm ts c" 
          by (simp add: ts'_def)
        then have "res ts d \<sqsubseteq> fst (snd ts') d"
          by (metis False True Un_ac(3) nat_int.un_subset1 nat_int.un_subset2 
              nat_int.union_def traffic.clm_consec_res)
        then show ?thesis 
          by (metis bot.extremum_uniqueI card_non_empty_geq_one traffic.atLeastOneRes)
      next
        case False
        then show ?thesis 
          using traffic.atLeastOneRes ts'_def by auto
      qed
    qed
    have re_leq_two:"\<forall>c. |(fst (snd ts')) c| \<le> 2"
      by (metis (no_types, lifting) Un_commute add.commute
          atMostTwoLanes atMostTwoRes nat_int.card_un_add clm_consec_res fun_upd_apply
          nat_int.union_def False prod.sel(1) prod.sel(2) ts'_def)
    have cl_leq_one:"\<forall>c. |(fst (snd (snd ts'))) c| \<le> 1" 
      using atMostOneClm nat_int.card_empty_zero ts'_def by auto
    have add_leq_two:"\<forall>c . |(fst (snd ts')) c| + |(fst (snd (snd ts'))) c| \<le> 2" 
      by (metis (no_types, lifting) Suc_1 add_Suc add_diff_cancel_left' 
          add_mono_thms_linordered_semiring(1) card_non_empty_geq_one cl_leq_one
          fun_upd_apply le_SucE one_add_one prod.sel(1) prod.sel(2) re_leq_two
          traffic.atMostTwoLanes ts'_def)
    have clNextRe :
      "\<forall>c. (((fst (snd (snd ts'))) c) \<noteq> \<emptyset> \<longrightarrow> 
        (\<exists> n. Rep_nat_int ((fst (snd ts')) c) \<union> Rep_nat_int (fst (snd (snd ts')) c) 
          = {n, n+1}))"
      using clmNextRes ts'_def by auto
    have ps_ge_zero: "(\<forall>c . fst (snd (snd (snd (snd (ts'))))) c > 0)" 
      using ts'_def psGeZero by simp
    have sd_ge_zero: "(\<forall>c . snd (snd (snd (snd (snd (ts'))))) c > 0)" 
      using ts'_def sdGeZero by simp
    have ts'_type:
      "ts'\<in> ?type"
      using  ts'_def disj  re_geq_one re_leq_two cl_leq_one add_leq_two    
        clNextRe mem_Collect_eq  ps_ge_zero  sd_ge_zero by blast
    have rep_eq:"Rep_traffic (Abs_traffic ts') = ts'" 
      using ts'_def ts'_type Abs_traffic_inverse by blast 
    have sp_eq:"(pos (Abs_traffic ts')) = (pos ts) "  
      using rep_eq ts'_def Rep_traffic pos_def by auto 
    have res_eq:"(res  (Abs_traffic ts')) = (res ts)(c:=( (res ts c)\<squnion> (clm ts c) ))" 
      using Rep_traffic ts'_def ts'_type Abs_traffic_inverse rep_eq res_def clm_def 
        fstI sndI by auto
    have dyn_eq:"(dyn  (Abs_traffic ts')) = (dyn ts)" 
      using Rep_traffic ts'_def ts'_type Abs_traffic_inverse rep_eq dyn_def fstI sndI 
      by auto
    have clm_eq:"(clm  (Abs_traffic ts')) = (clm ts)(c:=\<emptyset>)" 
      using ts'_def ts'_type Abs_traffic_inverse rep_eq clm_def fstI sndI Rep_traffic
      by fastforce 
    then have "ts  \<^bold>\<midarrow>r(c)\<^bold>\<rightarrow> Abs_traffic ts'" 
      using ts'_def ts'_type create_reservation_def 
        ts'_def disj re_geq_one re_leq_two cl_leq_one add_leq_two
        fst_conv snd_conv rep_eq sp_eq res_eq dyn_eq clm_eq
        Rep_traffic clm_def res_def clm_def dyn_def physical_size_def braking_distance_def 
      by auto 
    then show ?thesis ..
  qed
qed

lemma create_clm_eq_res:"(ts \<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow> ts')  \<longrightarrow> res ts c = res ts' c "
  using create_claim_def by auto

lemma withdraw_clm_eq_res:"(ts \<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts c= res ts' c "
  using withdraw_claim_def by auto

lemma withdraw_res_subseteq:"(ts \<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow> ts') \<longrightarrow> res ts' c \<sqsubseteq> res ts c "
  using withdraw_reservation_def order_refl less_eq_nat_int.rep_eq nat_int.el.rep_eq 
    nat_int.in_refl nat_int.in_singleton  fun_upd_apply subset_eq by fastforce

end
end
