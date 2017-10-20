section {* Idempotence of the SLin I/O automaton *}

theory Idempotence
imports SLin Simulations
begin

locale Idempotence = SLin +
  fixes id1 id2 :: nat
  assumes id1:"0 < id1" and id2:"id1 < id2"
begin

lemmas ids = id1 id2

definition composition where
  "composition  \<equiv> 
     hide ((ioa 0 id1) \<parallel> (ioa id1 id2))
          {act . EX p c av . act = Switch id1 p c av }"

lemmas comp_simps = hide_def composition_def ioa_def par2_def is_trans_def
  start_def actions_def asig_def trans_def

lemmas trans_defs = Inv_def Lin_def Resp_def Init_def
  Abort_def Reco_def

declare if_split_asm [split]

subsection {*A case rule for decomposing the transition relation 
  of the composition of two SLins *}

declare comp_simps [simp]
lemma trans_elim:
  fixes  s t a s' t' P
  assumes "(s,t) \<midarrow>a\<midarrow>composition\<longrightarrow> (s',t')"
  obtains 
    (Invoke1) i p c
      where "Inv p c s s' \<and> t = t'"
      and "i < id1" and "a = Invoke i p c"
  | (Invoke2) i p c
      where "Inv p c t t' \<and> s = s'"
      and "id1 \<le> i \<and> i < id2" and "a = Invoke i p c"
  | (Switch1) p c av
      where "Abort p c av s s' \<and> Init p c av t t'"
      and "a = Switch id1 p c av"
  | (Switch2) p c av 
      where "s = s' \<and> Abort p c av t t'"
      and "a = Switch id2 p c av"
  | (Response1) i p ou
      where "Resp p ou s s'\<and> t = t'"
      and "i < id1" and "a = Response i p ou"
  | (Response2) i p ou 
      where "Resp p ou t t' \<and> s = s'"
      and "id1 \<le> i \<and> i < id2" and "a = Response i p ou"
  | (Lin1) "Lin s s' \<and> t = t'" and "a = Linearize 0"
  | (Lin2) "Lin t t' \<and> s = s'" and "a = Linearize id1"
  | (Reco2) "Reco t t' \<and> s = s'" and "a = Recover id1"
proof %invisible (cases a)
  case (Invoke i p c)
  with assms have
    "(Inv p c s s' \<and> t = t' \<and> i < id1)
      \<or> (Inv p c t t' \<and> s = s' \<and> id1 \<le> i \<and> i < id2)" by auto
  thus ?thesis using Invoke that by blast 
next
  case (Response i p ou)
  with assms have
    "(Resp p ou s s' \<and> t = t' \<and> i < id1)
      \<or> (Resp p ou t t' \<and> s = s' \<and> id1 \<le> i \<and> i < id2)"
    by auto
  thus ?thesis using Response that by metis
next 
  case (Switch i p c av)
  with assms ids have
    "(i = id1 \<and> Abort p c av s s'\<and> Init p c av t t')
       \<or> (i = id2 \<and> s = s' \<and> Abort p c av t t')" 
    by auto
  thus ?thesis using Switch that by metis
next 
  case (Linearize i)
  with assms have
    "(Lin s s' \<and> t = t' \<and> i = 0) 
      \<or> (Lin t t' \<and> s = s' \<and> i = id1)"
      by auto
  thus ?thesis using Linearize that by metis
next
  case (Recover i)
  with assms have
    "Reco t t' \<and> s = s' \<and> a = Recover id1" by auto
   thus ?thesis using Recover that by auto
qed
declare comp_simps [simp del]

subsection {* Definition of the Refinement Mapping *}

fun f :: "(('a,'b,'c)SLin_state * ('a,'b,'c)SLin_state) \<Rightarrow> ('a,'b,'c)SLin_state"
  where
  "f (s1, s2) =
     \<lparr>pending = \<lambda> p. (if status s1 p \<noteq> Aborted then pending s1 p else pending s2 p),
      initVals = {},
      abortVals = abortVals s2,
      status = \<lambda> p. (if status s1 p \<noteq> Aborted then status s1 p else status s2 p),
      dstate = (if dstate s2 = \<bottom> then dstate s1 else dstate s2),
      initialized = True\<rparr>"

subsection {*Invariants *}

declare 
  trans_defs [simp]

fun P1 where
  "P1 (s1,s2) = (\<forall> p . status s1 p \<in> {Pending, Aborted} 
    \<longrightarrow> fst (pending s1 p) = p)"

fun P2 where
  "P2 (s1,s2) = (\<forall> p . status s2 p \<noteq> Sleep \<longrightarrow> fst (pending s2 p) = p)"

fun P3 where
  "P3 (s1,s2) = (\<forall> p . (status s2 p = Ready \<longrightarrow> initialized s2))"

(* Used to prove P19 only *)
fun P4 where
  "P4 (s1,s2) = ((\<forall> p . status s2 p = Sleep) = (initVals s2 = {}))"

fun P5 where
  "P5 (s1,s2) = (\<forall> p . status s1 p \<noteq> Sleep \<and> initialized s1 \<and> initVals s1 = {})"


fun P6  where
  "P6 (s1,s2) = (\<forall> p . (status s1 p \<noteq> Aborted) = (status s2 p = Sleep))"

fun P7 where
  "P7 (s1,s2) = (\<forall> c . status s1 c = Aborted \<and> \<not> initialized s2 
    \<longrightarrow> (pending s2 c = pending s1 c \<and> status s2 c \<in> {Pending, Aborted}))"

(* Only used in the proof of P8a *)
fun P8 where
  "P8 (s1,s2) = (\<forall> iv \<in> initVals s2 . \<exists> rs \<in> pendingSeqs s1 . 
    iv = dstate s1 \<star> rs)"

fun P8a where
  "P8a (s1,s2) = (\<forall> ivs \<in> initSets s2 . \<exists> rs \<in> pendingSeqs s1 . 
    \<Sqinter>ivs = dstate s1 \<star> rs)"

fun P9 where 
  "P9 (s1,s2) = (initialized s2 \<longrightarrow> dstate s1 \<preceq> dstate s2)"

fun P10  where
  "P10 (s1,s2) = ((\<not> initialized s2) \<longrightarrow> (dstate s2 = \<bottom>))"

fun P11  where
  "P11 (s1,s2) = (initVals s2 = abortVals s1)"

fun P12 where
  "P12 (s1,s2) = (initialized s2 \<longrightarrow> \<Sqinter> (initVals s2) \<preceq> dstate s2)"
  
fun P13 where
  "P13 (s1,s2) = (finite (initVals s2)
    \<and> finite (abortVals s1) \<and> finite (abortVals s2))"
  
fun P14 where
  "P14 (s1,s2) = (initialized s2 \<longrightarrow> initVals s2 \<noteq> {})"

fun P15 where
  "P15 (s1,s2) = (\<forall> av \<in> abortVals s1 . dstate s1 \<preceq> av)"

fun P16 where
  "P16 (s1,s2) = (dstate s2 \<noteq> \<bottom> \<longrightarrow> initialized s2)"

fun P17 where                                                         
-- {* For the Response1 case of the refinement proof, in case a response
  is produced in the first instance and the second instance is already
  initialized *}
  "P17 (s1,s2) = (initialized s2 
    \<longrightarrow> (\<forall> p . 
      ((status s1 p = Ready 
        \<or> (status s1 p = Pending \<and> contains (dstate s1) (pending s1 p))) 
          \<longrightarrow> (\<exists> rs . dstate s2 = dstate s1 \<star> rs \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)))
      \<and> ((status s1 p = Pending \<and> \<not> contains (dstate s1) (pending s1 p)) 
        \<longrightarrow> (\<exists> rs . dstate s2 = dstate s1 \<star> rs \<and> (\<forall> r \<in> set rs . 
          fst r = p \<longrightarrow> r = pending s1 p)))))"

(* Only used for proving P19 *)
fun P18 where
  "P18 (s1,s2) = (abortVals s2 \<noteq> {} \<longrightarrow> (\<exists> p . status s2 p \<noteq> Sleep))"

fun P19 where
  "P19 (s1,s2) = (abortVals s2 \<noteq> {} \<longrightarrow> abortVals s1 \<noteq> {})"

fun P20 where
  "P20 (s1,s2) = (\<forall> av \<in> abortVals s2 . dstate s2 \<preceq> av)"

fun P21 where
  "P21 (s1,s2) = (\<forall> av \<in> abortVals s2 . \<Sqinter>(abortVals s1) \<preceq> av)"

fun P22 where
  "P22 (s1,s2) = (initialized s2 \<longrightarrow> dstate (f (s1,s2)) = dstate s2)"

fun P23 where
  "P23 (s1,s2) = ((\<not> initialized s2) \<longrightarrow> 
    pendingSeqs s1 \<subseteq> pendingSeqs (f (s1,s2)))"

fun P25 where
  "P25 (s1,s2) = (\<forall> ivs . (ivs \<in> initSets s2 \<and> initialized s2 
    \<and> dstate s2 \<preceq> \<Sqinter>ivs)
      \<longrightarrow> (\<exists> rs' \<in> pendingSeqs (f (s1,s2)) . \<Sqinter>ivs = dstate s2 \<star> rs'))"

fun P26 where
  "P26 (s1,s2) = (\<forall> p . (status s1 p = Aborted 
    \<and> \<not> contains (dstate s2) (pending s1 p))
      \<longrightarrow> (status s2 p \<in> {Pending,Aborted} 
        \<and> pending s1 p = pending s2 p))"

lemma P1_invariant:
shows "invariant (composition) P1"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P1 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P1 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P1 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto
qed

lemma P2_invariant:
shows "invariant (composition) P2"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P2 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P2 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P2 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto 
qed

lemma P16_invariant:
shows "invariant (composition) P16"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P16 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P16 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P16 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto 
qed

lemma P3_invariant:
shows "invariant (composition) P3"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P3 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P3 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P3 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto
qed

lemma P4_invariant:
shows "invariant (composition) P4"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P4 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P4 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P4 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto 
qed

lemma P5_invariant:
shows "invariant (composition) P5"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P5 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P5 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P5 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto
qed


lemma P13_invariant:
shows "invariant (composition) P13"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P13 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P13 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P13 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim, auto)
qed

lemma P20_invariant:
shows "invariant (composition) P20"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P20 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P20 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach: "reachable (composition) (s1,s2)"
  from reach have P16:"P16 (s1,s2)" using P16_invariant and ids
    by (metis IOA.invariant_def)
  show "P20 (t1,t2)" using trans and hyp and P16
  by (cases rule:trans_elim, auto simp add:safeInits_def safeAborts_def
    initAborts_def uninitAborts_def bot)
qed

lemma P18_invariant:
shows "invariant (composition) P18"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P18 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P18 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P18 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim, auto)
qed

lemma P14_invariant:
shows "invariant (composition) P14"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P14 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P14 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P14 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim, auto simp add:safeInits_def)
qed

lemma P15_invariant:
shows "invariant (composition) P15"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P15 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P15 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach: "reachable (composition) (s1,s2)"
  from reach have P5:"P5 (s1,s2)" using P5_invariant and ids
    by (metis IOA.invariant_def)
  show "P15 (t1,t2)" using trans and hyp and P5
  by (cases rule:trans_elim, 
    auto simp add:less_eq_def safeAborts_def initAborts_def)
qed

lemma P6_invariant:
shows "invariant (composition) P6"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P6 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P6 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P6 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim, force+)
qed

lemma P7_invariant:
shows "invariant (composition) P7"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P7 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P7 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P7 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto
qed

lemma P10_invariant:
shows "invariant (composition) P10"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P10 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P10 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P10 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim) auto
qed

lemma P11_invariant:
shows "invariant (composition) P11"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P11 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P11 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  show "P11 (t1,t2)" using trans and hyp
  by (cases rule:trans_elim, force+)
qed
  
lemma P8_invariant:
shows "invariant (composition) P8"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P8 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P8 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach: "reachable (composition) (s1,s2)"
  from reach have P5:"P5 (s1,s2)" using P5_invariant and ids
    by (metis IOA.invariant_def)
  from reach have P1:"P1 (s1,s2)" using P1_invariant and ids
    by (metis IOA.invariant_def)
  from reach have P11:"P11 (s1,s2)" using P11_invariant and ids
    by (metis IOA.invariant_def)
  show "P8 (t1,t2)" using trans and hyp
  proof (cases rule:trans_elim)
    case (Invoke1 i p c)
    assume "P8 (s1,s2)"
    have "pendingSeqs s1 \<subseteq> pendingSeqs t1" 
    proof -
      have "pending t1 = (pending s1)(p := (p,c))"
      and "status t1 = (status s1)(p := Pending)"
      and "status s1 p = Ready"
      using Invoke1(1) by auto
      hence "pendingReqs s1 \<subseteq> pendingReqs t1" by (simp add:pendingReqs_def) force
      thus ?thesis by (auto simp add:pendingSeqs_def)
    qed
    moreover have "initVals t2 = initVals s2" and "dstate t1 = dstate s1" 
      using Invoke1(1) by auto
    ultimately show "P8 (t1,t2)" using `P8 (s1,s2)` by fastforce
  next
    case Lin1
    assume "P8 (s1,s2)"
    show "P8 (t1,t2)"
    proof (simp, rule ballI)
      fix iv
      assume 0:"iv \<in> initVals t2"
      have 1:"iv \<in> initVals s2" using Lin1(1) 0 by simp
      have 4:"iv \<in> abortVals s1" using 1 P11 by simp
      obtain rs where 2:"rs \<in> pendingSeqs s1" and 3:"iv = dstate s1 \<star> rs"
        using `P8 (s1,s2)` 1 by auto
      obtain rs' where 6:"dstate t1 = dstate s1 \<star> rs'" and 5:"dstate s1 \<star> rs' \<preceq> iv"
        using Lin1(1) 1 4 by auto
      obtain rs'' where 7:"iv = (dstate s1 \<star> rs') \<star> rs''" and 8:"set rs'' \<subseteq> set rs"
        using consistency 3 5 6 by simp (metis less_eq_def)
      have 10:"rs'' \<in> pendingSeqs t1" 
      proof -
        have 9:"pendingSeqs t1 = pendingSeqs s1" 
          using Lin1(1) by (auto simp add:pendingSeqs_def pendingReqs_def)
        thus ?thesis using 8 2  by (auto simp add:pendingSeqs_def)
      qed
      show "\<exists> rs \<in> pendingSeqs t1 . iv = dstate t1 \<star> rs"
        using 7 10 6 by auto
    qed
  next
    case (Response1 i p ou)
    assume ih:"P8 (s1,s2)"
    show "P8 (t1,t2)"
    proof auto
      fix iv 
      assume 1:"iv \<in> initVals t2"
      obtain rs where 2:"iv = dstate t1 \<star> rs" and 3:"rs \<in> pendingSeqs s1"
        using 1 Response1(1) ih by auto
      have 4:"pendingReqs t1 = ((pendingReqs s1) - {pending s1 p})"
      proof -
        have "pending t1 = pending s1" and "status t1 = (status s1)(p := Ready)"
          and 5:"status s1 p = Pending"
          using Response1(1) by auto
        moreover have "\<And> q . q \<noteq> p \<Longrightarrow> status s1 q \<in> {Pending,Aborted} 
          \<Longrightarrow> pending s1 q \<noteq> pending s1 p" 
          using P1 5 by (metis P1.simps insertI1) 
        ultimately show ?thesis by (simp add:pendingReqs_def) fastforce
      qed        
      have 8:"contains (dstate t1) (pending s1 p)" using Response1(1) by simp
      define rs' where "rs' = filter (\<lambda> x . x \<noteq> (pending s1 p)) rs"
      have 9:"rs' \<in> pendingSeqs t1" 
      proof -
        have 9:"pending s1 p \<notin> set rs'" by (auto simp add:rs'_def)
        have 10:"rs' \<in> pendingSeqs s1"
          using 3 by (auto simp add:rs'_def) 
            (metis filter_is_subset mem_Collect_eq pendingSeqs_def subset_trans)
        show ?thesis using 10 9 4 by (auto simp add:pendingSeqs_def)
      qed
      have 10:"iv = dstate t1 \<star> rs'" using 8 2 idem_star rs'_def by fast   
      show "\<exists> rs \<in> pendingSeqs t1 . iv = dstate t1 \<star> rs" using 10 9 by auto
    qed
  next
    case (Switch1 p c av)
    assume "P8 (s1,s2)"
    have 1:"initialized s1 \<and> initVals s1 = {}" using P5 by auto
    obtain av where 2:"initVals t2 = initVals s2 \<union> {av}" and 3:"av \<in> safeAborts s1"
      using Switch1(1) by auto
    obtain rs where 4:"rs \<in> pendingSeqs s1" and 5:"av = dstate s1 \<star> rs"
      using 1 3 by (auto simp add:safeAborts_def initAborts_def initSets_def)
    have 6:"dstate s1 = dstate t1" using Switch1(1) by simp 
    have 7:"pendingSeqs t1 = pendingSeqs s1"
    proof -
      have "pendingReqs t1 = pendingReqs s1"
        using Switch1(1) by (simp add:pendingReqs_def) fastforce
      thus ?thesis by (auto simp add:pendingSeqs_def)
    qed
    show "P8 (t1,t2)" using `P8 (s1,s2)` 2 4 5 6 7 by auto 
  next
    case (Invoke2 i p c)
    assume "P8 (s1,s2)"
    thus "P8 (t1,t2)" using Invoke2(1) by force
  next
    case Lin2
    assume "P8 (s1,s2)"
    thus "P8 (t1,t2)" using Lin2(1) by force
  next
    case (Response2 i p ou)
    assume "P8 (s1,s2)"
    thus "P8 (t1,t2)" using Response2(1) by force 
  next
    case (Switch2 p c av)
    assume "P8 (s1,s2)"
    thus "P8 (t1,t2)" using Switch2(1) by force
  next
    case Reco2
    assume "P8 (s1,s2)"
    thus "P8 (t1,t2)" using Reco2(1) by force
  qed
qed

lemma P8a_invariant:
shows "invariant (composition) P8a"
proof (auto simp:invariant_def)
  fix s1 s2 ivs
  assume 1:"reachable (composition) (s1,s2)"
  and 2:"ivs \<in> initSets s2"
  have 3:"finite ivs \<and> ivs \<noteq> {}"
  proof -
    have "P13 (s1,s2)" using P13_invariant 1
      by (metis IOA.invariant_def)
    thus ?thesis using 2 finite_subset by (auto simp add:initSets_def)
  qed
  have 4:"\<forall> av \<in> ivs . \<exists> rs \<in> pendingSeqs s1 . av = dstate s1 \<star> rs"
  proof -
    have P8:"P8 (s1,s2)" using P8_invariant 1
      by (metis IOA.invariant_def)
    thus ?thesis using 2 by (auto simp add:initSets_def)
  qed
  show "\<exists> rs \<in> pendingSeqs s1 . \<Sqinter>ivs = dstate s1 \<star> rs" 
    using 3 4 glb_common_set by (simp add:pendingSeqs_def, metis)
qed

lemma P12_invariant:
shows "invariant (composition) P12"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P12 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P12 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach: "reachable (composition) (s1,s2)"
  from reach have P13:"P13 (s1,s2)" using P13_invariant
    by (metis IOA.invariant_def)
  from reach have P14:"P14 (s1,s2)" using P14_invariant
    by (metis IOA.invariant_def)
  show "P12 (t1,t2)" using trans and hyp
  proof (cases rule:trans_elim)
    case (Invoke1 i p c)
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Invoke1(1) by auto
  next
    case Lin1
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Lin1(1) by auto
  next
    case (Response1 i p ou)
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Response1(1) by auto
  next
    case (Switch1 p c av)
    assume ih:"P12 (s1,s2)"
    have "initialized s2 \<Longrightarrow> \<Sqinter> (initVals t2) \<preceq> \<Sqinter> (initVals s2)"
    proof -
      assume 1:"initialized s2"
      have "initVals t2 = initVals s2 \<union> {av}" using Switch1(1) by simp
      hence "\<Sqinter> (initVals t2) = \<Sqinter> (initVals s2) \<sqinter> av" 
        using insert_not_elem P13 P14 1
        by (metis P13.simps P14.simps Un_empty_right Un_insert_right commute insert)
      thus ?thesis by (metis cobounded1)
    qed
    moreover have "dstate t2 = dstate s2" and "initialized s2 = initialized t2"
      using Switch1(1) by auto
    ultimately show "P12 (t1,t2)" using ih by auto (metis absorb2 coboundedI1) 
  next
    case (Invoke2 i p c)
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Invoke2(1) by force
  next
    case Lin2
    assume "P12 (s1,s2)"
    moreover
    have "initVals t2 = initVals s2" and "initialized s2"
    and "initialized t2" using Lin2(1) by auto
    moreover
    have "dstate s2 \<preceq> dstate t2" using Lin2(1) by auto (metis less_eq_def) 
    ultimately show "P12 (t1,t2)" by auto (metis strict_iff_order strict_trans1)  
  next
    case (Response2 i p ou)
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Response2(1) by force 
  next
    case (Switch2 p c av)
    assume "P12 (s1,s2)"
    thus "P12 (t1,t2)" using Switch2(1) by force
  next
    case Reco2
    obtain d where 1:"d \<in> safeInits s2" and 2:"dstate t2 = d"
      using Reco2(1) by force
    obtain ivs where 3:"ivs \<subseteq> initVals s2" and 4:"ivs \<noteq> {}"
      and 5:"\<Sqinter>ivs \<preceq> d" 
      using 1 by (auto simp add:safeInits_def initSets_def)
        (metis equals0D less_eq_def)
    have 6:"\<Sqinter> (initVals s2) \<preceq> \<Sqinter> ivs" using 3 P13 4
      by (metis P13.simps antimono) 
    have 7:"initVals s2 = initVals t2" using Reco2(1) by auto
    show "P12 (t1,t2)" using 2 5 6 7 
      by (metis P12.simps absorb2 coboundedI1)
  qed
qed

lemma P19_invariant:
shows "invariant (composition) P19"
proof (auto simp only:invariant_def)
  fix s1 s2
  assume 1:"reachable (composition) (s1,s2)"
  have P4:"P4 (s1,s2)" using P4_invariant 1
    by (simp add:invariant_def)
  moreover
  have P18:"P18 (s1,s2)" using P18_invariant 1
    by (metis IOA.invariant_def)
  moreover
  have P11:"P11 (s1,s2)" using P11_invariant 1
    by (metis IOA.invariant_def) 
  moreover
  ultimately show "P19 (s1,s2)" by auto
qed

lemma P9_invariant:
shows "invariant (composition) P9"
proof (auto simp only:invariant_def)
  fix s1 s2
  assume 1:"reachable (composition) (s1,s2)"
  have P12:"P12 (s1,s2)" using P12_invariant 1
    by (simp add:invariant_def)
  have P15:"P15 (s1,s2)" using P15_invariant 1
    by (metis IOA.invariant_def)
  have P13:"P13 (s1,s2)" using P13_invariant 1
    by (metis IOA.invariant_def)
  have P14:"P14 (s1,s2)" using P14_invariant 1
    by (metis IOA.invariant_def)
  have P11:"P11 (s1,s2)" using P11_invariant 1
    by (metis IOA.invariant_def)
  have "initialized s2 \<Longrightarrow> dstate s1 \<preceq> \<Sqinter>(abortVals s1)" 
    using P13 P15 P14 P11 boundedI by simp 
  thus "P9 (s1,s2)" using P12 P11 by simp (metis trans)  
qed

lemma P17_invariant:
shows "invariant (composition) P17"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P17 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P17 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach:"reachable (composition) (s1,s2)"
  show "P17 (t1,t2)" using trans and hyp
  proof (cases rule:trans_elim)
    case (Invoke1 i p c)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Invoke1(1) by fastforce
  next
    case (Response1 i p ou)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Response1(1) by auto
  next
    case (Switch1 p c av)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Switch1(1) by auto 
  next
    case (Invoke2 i p c)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Invoke2(1) by force
  next
    case (Response2 i p ou)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Response2(1) by force 
  next
    case (Switch2 p c av)
    assume "P17 (s1,s2)"
    thus "P17 (t1,t2)" using Switch2(1) by force
  next
    case Lin1
    assume 1:"P17 (s1,s2)"
    obtain rs' where 2:"dstate t1 = dstate s1 \<star> rs'"
      using Lin1(1) 1 by auto
    have 3:"dstate s2 = dstate t2" using Lin1(1) by auto
    have 4:"initialized t2 \<Longrightarrow> dstate t1 \<preceq> dstate t2"
    proof -
      assume "initialized t2"
      moreover
      have "P9 (t1,t2)" using reach trans P9_invariant
        by (metis IOA.invariant_def reachable_n)
      ultimately show ?thesis by auto
    qed
    show "P17 (t1,t2)"
    proof(simp, auto)
      fix p
      assume 5:"initialized t2" and 6:"status t1 p = Ready"
      obtain rs where 7:"\<forall> r \<in> set rs . fst r \<noteq> p"
        and 8:"dstate t2 = dstate s1 \<star> rs"
      proof -
        obtain rs where "dstate s2 = dstate s1 \<star> rs 
          \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)" using 1 5 6 Lin1(1) by force
        hence "\<forall> r \<in> set rs . fst r \<noteq> p" and "dstate t2 = dstate s1 \<star> rs"
          using Lin1(1) by auto 
        thus ?thesis using that by blast
      qed
      have 9:"dstate t1 \<preceq> dstate t2" using 4 5 by auto
      obtain rs'' where 10:"dstate t2 = dstate t1 \<star> rs''" 
        and 11:"set rs'' \<subseteq> set rs" 
          using consistency 2 8 9 by simp (metis less_eq_def) 
      have 12:"\<forall> r \<in> set rs'' . fst r \<noteq> p" using 7 11 by blast
      thus "\<exists> rs . dstate t2 = dstate t1 \<star> rs \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
        using 10 12 by auto
    next
      fix p
      assume 5:"initialized t2" and 6:"status t1 p = Pending"
        and 7:"\<not> contains (dstate t1) (pending t1 p)"
      obtain rs where 8:"\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending s1 p"
        and 9:"dstate t2 = dstate s1 \<star> rs"
      proof -
        have 9:"\<not> contains (dstate s1) (pending s1 p)"
          using 7 Lin1(1) contains_star by fastforce
        obtain rs where "dstate s2 = dstate s1 \<star> rs 
          \<and> (\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending s1 p)" 
            using 1 5 6 9 Lin1(1) by force
        hence "\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending s1 p" 
          and "dstate t2 = dstate s1 \<star> rs"
            using Lin1(1) by auto
        thus ?thesis using that by blast
      qed
      have 10:"dstate t1 \<preceq> dstate t2" using 4 5 by auto
      obtain rs'' where 11:"dstate t2 = dstate t1 \<star> rs''" 
        and 12:"set rs'' \<subseteq> set rs" 
          using consistency 2 9 10 by simp (metis less_eq_def)
      have 13:"\<forall> r \<in> set rs'' . fst r = p \<longrightarrow> r = pending s1 p" 
        using 8 12 by blast
      show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending t1 p)"
        using 11 13 Lin1(1) by auto
    next
      fix p
      assume 5:"initialized t2" and 6:"status t1 p = Pending"
        and 7:"contains (dstate t1) (pending t1 p)"
      show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
      proof (cases "contains (dstate s1) (pending s1 p)")
        case True
        obtain rs where 8:"\<forall> r \<in> set rs . fst r \<noteq> p"
          and 9:"dstate t2 = dstate s1 \<star> rs"
        proof -
          obtain rs where "dstate s2 = dstate s1 \<star> rs 
            \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)" using 1 5 6 True Lin1(1) by force
          hence "\<forall> r \<in> set rs . fst r \<noteq> p" and "dstate t2 = dstate s1 \<star> rs"
            using Lin1(1) by auto
          thus ?thesis using that by blast
        qed
        have 10:"dstate t1 \<preceq> dstate t2" using 4 5 by auto
        obtain rs'' where 11:"dstate t2 = dstate t1 \<star> rs''" 
          and 12:"set rs'' \<subseteq> set rs" 
            using consistency 2 9 10 by simp (metis less_eq_def)
        have 13:"\<forall> r \<in> set rs'' . fst r \<noteq> p" using 8 12 by blast
        thus "\<exists> rs . dstate t2 = dstate t1 \<star> rs \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
          using 11 13 by auto
      next
        case False
        obtain rs'' where 8:"dstate t2 = dstate t1 \<star> rs''"
          and 9:"\<forall> r \<in> set rs'' . fst r = p \<longrightarrow> r = pending t1 p"
        proof -
          obtain rs where 8:"\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending s1 p"
            and 9:"dstate t2 = dstate s1 \<star> rs"
          proof -
            obtain rs where "dstate s2 = dstate s1 \<star> rs 
              \<and> (\<forall> r \<in> set rs . fst r  = p \<longrightarrow> r = pending s1 p)" 
                using 1 5 6 False Lin1(1) by force
            hence "\<forall> r \<in> set rs . fst r  = p \<longrightarrow> r = pending s1 p" 
              and "dstate t2 = dstate s1 \<star> rs"
                using Lin1(1) by auto
            thus ?thesis using that by blast
          qed
          have 10:"dstate t1 \<preceq> dstate t2" using 4 5 by auto
          obtain rs'' where 11:"dstate t2 = dstate t1 \<star> rs''" 
            and 12:"set rs'' \<subseteq> set rs" 
              using consistency 2 9 10 by simp (metis less_eq_def)
          have 13:"\<forall> r \<in> set rs'' . fst r = p \<longrightarrow> r = pending s1 p" 
            using 8 12 by blast
          have "dstate t2 = dstate t1 \<star> rs''
            \<and> (\<forall> r \<in> set rs'' . fst r = p \<longrightarrow> r = pending t1 p)"
              using 11 13 Lin1(1) by auto
          thus ?thesis using that by blast
        qed
        have 10:"dstate t1 \<star> rs'' 
          = dstate t1 \<star> (filter (\<lambda> r . r \<noteq> pending t1 p) rs'')"
          using 7 idem_star by blast
        have 11:"\<forall> r \<in> set (filter (\<lambda> r . r \<noteq> pending t1 p) rs'') . 
          fst r \<noteq> p" using 9 by force
        show "\<exists> rs . dstate t2 = dstate t1 \<star> rs \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
          using 8 10 11 by metis
      qed
    qed
  next
    case Lin2
    assume 1:"P17 (s1,s2)"
    { fix p
      assume 2:"status s1 p \<noteq> Aborted"
      have "\<exists> rs' . dstate t2 = dstate s2 \<star> rs'
        \<and> (\<forall> r \<in> set rs' . fst r \<noteq> p)"
      proof -
        obtain rs' where 5:"dstate t2 = dstate s2 \<star> rs'"
          and 6:"rs' \<in> pendingSeqs s2" using Lin2(1) by force
        have 7:"\<forall> r \<in> set rs' . fst r \<noteq> p"
        proof (rule ballI)
          fix r
          assume "r \<in> set rs'"
          with 6 have "r \<in> pendingReqs s2" by (auto simp add:pendingSeqs_def)
          moreover 
          have "P2 (s1,s2)" using reach P2_invariant 
            by (metis invariant_def)
          moreover
          have "status s2 p = Sleep"
          proof -
            have "P6 (s1,s2)" using reach P6_invariant 
              by (metis invariant_def)
            thus ?thesis using 2 Lin2(1) by force
          qed
          ultimately show "fst r \<noteq> p" by (auto simp add:pendingReqs_def)
        qed
        show ?thesis using 5 7 by force
      qed }
      note a = this
    show "P17 (t1,t2)"
    proof auto
      fix p
      assume 2:"initialized t2" and 3:"status t1 p = Ready"
      obtain rs where "dstate s2 = dstate s1 \<star> rs" 
        and "\<forall> r \<in> set rs . fst r \<noteq> p"
      proof - 
        have "initialized s2" and "status s1 p = Ready" 
          using Lin2(1) 2 3 by auto
        thus ?thesis using that 1 by fastforce
      qed
      moreover
      obtain rs' where "dstate t2 = dstate s2 \<star> rs'" 
        and "\<forall> r \<in> set rs' . fst r \<noteq> p" using a 3 Lin2(1)
          by (metis SLin_status.distinct(11)) 
      ultimately show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)" using Lin2(1) 
          by auto (metis UnE exec_append set_append) 
    next
      fix p
      assume 2:"initialized t2" and 3:"status t1 p = Pending"
        and 4:"contains (dstate t1) (pending t1 p)"
      obtain rs where "dstate s2 = dstate s1 \<star> rs" 
        and "\<forall> r \<in> set rs . fst r \<noteq> p"
      proof -
        have "initialized s2" and "status s1 p = Pending
          \<and> contains (dstate s1) (pending s1 p)" 
            using Lin2(1) 2 3 4 by auto
        thus ?thesis using that 1 by fastforce
      qed
      moreover
      obtain rs' where "dstate t2 = dstate s2 \<star> rs'" 
        and "\<forall> r \<in> set rs' . fst r \<noteq> p" using a 3 Lin2(1)
          by (metis SLin_status.distinct(9))
      ultimately show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)" using Lin2(1) 
          by auto (metis UnE exec_append set_append) 
    next
      fix p
      assume 2:"initialized t2" and 3:"status t1 p = Pending"
        and 4:"\<not> contains (dstate t1) (pending t1 p)"
      obtain rs where "dstate s2 = dstate s1 \<star> rs" 
        and "\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending s1 p"
      proof - 
        have "initialized s2" and "status s1 p = Pending
          \<and> \<not> contains (dstate s1) (pending s1 p)" 
            using Lin2(1) 2 3 4 by auto
        thus ?thesis using that 1 by fastforce
      qed
      moreover
      obtain rs' where "dstate t2 = dstate s2 \<star> rs'" 
        and "\<forall> r \<in> set rs' . fst r \<noteq> p" using a 3 Lin2(1)
          by (metis SLin_status.distinct(9))
      ultimately show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending t1 p)" 
          using Lin2(1) 
            by auto (metis UnE exec_append set_append)
    qed
  next
    case Reco2
    assume 0:"P17 (s1,s2)"
    obtain rs' where 1:"dstate t2 = dstate t1 \<star> rs'" 
      and 2:"set rs' \<subseteq> pendingReqs s1 \<union> pendingReqs s2"
    proof -
      obtain ivs rs where 1:"ivs \<subseteq> initVals s2" and 2:"ivs \<noteq> {}"
        and 3:"dstate t2 = \<Sqinter>ivs \<star> rs" and 4:"rs \<in> pendingSeqs s2"
        using Reco2(1) by (simp add:safeInits_def initSets_def, force)
      obtain rs'' where "set rs'' \<subseteq> pendingReqs s1"
        and "\<Sqinter>ivs = dstate s1 \<star> rs''"
      proof -
        have "P8a (s1,s2)" using reach P8a_invariant
          by (metis invariant_def)
        thus ?thesis using that using 1 2 
          by (auto simp add:initSets_def pendingSeqs_def)
      qed
      hence "dstate t2 = dstate t1 \<star> (rs''@rs) 
        \<and> set rs'' \<subseteq> pendingReqs s1 
          \<and> set rs \<subseteq> pendingReqs s2"
        using 3 4 Reco2(1) 4
          by (metis exec_append mem_Collect_eq pendingSeqs_def)
      thus ?thesis using that by force
    qed        
    { fix p r
      assume 1:"r \<in> pendingReqs s2" 
        and 2:"status s1 p \<noteq> Aborted"
      have "fst r \<noteq> p"
      proof -
        have "P2 (s1,s2)" using reach P2_invariant
          by (metis invariant_def)
        moreover
        have "P6 (s1,s2)" using reach P6_invariant
          by (metis invariant_def)
        ultimately show ?thesis using 1 2 Reco2(1)
          by (simp add:pendingReqs_def)
            (metis SLin_status.distinct(1,5)) 
        qed }
    note 3 = this                
    { fix r p
      assume 1:"r \<in> pendingReqs s1" and 2:"fst r = p"
        and 3:"status s1 p = Pending"
      have "r = pending s1 p"
      proof -
        have "P1 (s1,s2)" using reach P1_invariant
          by (metis invariant_def)
        thus ?thesis using 1 2 3
          by (auto simp add:pendingReqs_def)
      qed }
    note 10 = this
    show "P17 (t1,t2)"
    proof (auto)
      fix p
      assume 4:"status t1 p = Ready"
      show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
      proof -
        { fix r
          assume 5:"r \<in> pendingReqs s1"
          have "fst r \<noteq> p"
          proof -
            have "P1 (s1,s2)" using reach P1_invariant
              by (metis invariant_def)
            with 4 5 Reco2(1) show ?thesis 
              by (auto simp add:pendingReqs_def)
          qed }
        moreover
        have "\<And> r . r \<in> pendingReqs s2 \<Longrightarrow> fst r \<noteq> p"
          using 3 4 Reco2(1) by auto
        ultimately show ?thesis using 1 2 by blast
      qed
    next
      fix p
      assume 4:"status t1 p = Pending"
        and 5:"contains (dstate t1) (pending t1 p)"
      show "\<exists> rs . dstate t2 = dstate t1 \<star> rs
        \<and> (\<forall> r \<in> set rs . fst r \<noteq> p)"
      proof -
        let ?rs = "filter (\<lambda> r . r \<noteq> pending t1 p) rs'"
        have "dstate t2 = dstate t1 \<star> ?rs"
          using 5 1 idem_star by metis
        moreover
        { fix r
          assume "r \<in> set ?rs"
          have "fst r \<noteq> p"
          proof -
            { fix r
              assume 6:"r \<in> set rs'" and 7:"fst r = p"
              have "r = pending s1 p"
              proof -
                have "\<And> r . r \<in> pendingReqs s2 \<Longrightarrow> fst r \<noteq> p"
                  using 3 4 Reco2(1) by auto
                moreover
                have "\<And> r . r \<in> pendingReqs s1 \<Longrightarrow> fst r = p
                  \<Longrightarrow> r = pending s1 p"
                    using 10 4 Reco2(1) by auto
                ultimately show ?thesis using 2 6 7 
                  by (metis (lifting, no_types) UnE subsetD) 
              qed }
            thus ?thesis using `r \<in> set ?rs` Reco2(1) by fastforce
          qed }
        ultimately show ?thesis by blast
      qed
    next
      fix p
      assume 4:"status t1 p = Pending"
        and 5:"\<not> contains (dstate t1) (pending t1 p)"
      show "\<exists> rs . dstate t2 = dstate t1 \<star> rs 
        \<and> (\<forall> r \<in> set rs . fst r = p \<longrightarrow> r = pending t1 p)"
      proof -
        have "\<And> r . r \<in> pendingReqs s2 \<Longrightarrow> fst r \<noteq> p"
          using 3 4 Reco2(1) by auto
        moreover
        have "\<And> r . r \<in> pendingReqs s1 \<Longrightarrow> fst r = p
          \<Longrightarrow> r = pending s1 p"
            using 10 4 Reco2(1) by auto
        ultimately show ?thesis using 1 2 Reco2(1) 
          by (metis (lifting, no_types) UnE set_rev_mp) 
      qed
    qed   
  qed
qed

lemma P21_invariant:
shows "invariant (composition) P21"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P21 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P21 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach: "reachable (composition) (s1,s2)"
  show "P21 (t1,t2)"
  proof (cases "initialized t2")
    case True
    moreover
    have P12:"P12 (t1,t2)" using P12_invariant reach trans
      by (metis invariant_def reachable_n)
    moreover
    have P11:"P11 (t1,t2)" using P11_invariant reach trans
      by (metis IOA.invariant_def reachable_n)
    moreover
    have P20:"P20 (t1,t2)" using P20_invariant reach trans
      by (metis IOA.invariant_def reachable_n) 
    ultimately show "P21 (t1,t2)" by simp
      (metis pre_RDR.trans) 
  next
    case False
    show "P21 (t1,t2)" using trans
    proof (cases rule:trans_elim)
      case (Switch2 p c av)
      obtain av where "abortVals t2 = abortVals s2 \<union> {av}"
        and "\<Sqinter>(abortVals s1) \<preceq> av"
      proof -
        obtain ivs rs where 1:"abortVals t2 = abortVals s2 \<union> {\<Sqinter>ivs \<star> rs}"
          and 2:"ivs \<subseteq> initVals s2" and 3:"ivs \<noteq> {}"
          using False Switch2(1) by (auto simp add:safeAborts_def
            uninitAborts_def initSets_def)
        have 4:"\<Sqinter>(abortVals s1) \<preceq> \<Sqinter>ivs"
        proof -
          have "P11 (s1,s2)" using reach P11_invariant
            by (metis invariant_def)
          moreover 
          have "P13 (s1,s2)" using reach P13_invariant
            by (metis invariant_def)
          ultimately show ?thesis using 2 3 antimono by simp
        qed
        show ?thesis using that 1 4 by simp
          (metis coboundedI2 less_eq_def orderE) 
      qed
      with hyp show ?thesis using Switch2(1) by simp
    next
      case (Switch1 p c av)
      show ?thesis
      proof (cases "abortVals s1 = {}")
        case False
        have "\<Sqinter> (abortVals t1) \<preceq> \<Sqinter> (abortVals s1)" 
        proof -
          obtain av where "abortVals t1 = abortVals s1 \<union> {av}"
            using Switch1(1) by auto
          moreover 
          have "P13 (s1,s2)" using reach P13_invariant
            by (metis invariant_def) 
          ultimately show ?thesis using False by simp
        qed
        moreover have "abortVals t2 = abortVals s2" 
          using Switch1(1) by auto
        ultimately show ?thesis using hyp 
          by auto (metis coboundedI2 orderE)  
      next
        case True
        have "abortVals t2 = {}"
        proof -
          have "P19 (s1,s2)" using reach P19_invariant
            by (metis invariant_def)
          thus ?thesis using True Switch1(1) by auto
        qed
        thus ?thesis by auto
      qed
    next
      case (Invoke1 p c)
      thus ?thesis using hyp by simp
    next
      case (Invoke2 p c)
      thus ?thesis using hyp by simp
    next
      case (Response1 p ou)
      thus ?thesis using hyp by simp
    next
      case (Response2 p ou)
      thus ?thesis using hyp by simp
    next
      case Lin1
      thus ?thesis using hyp by auto
    next
      case Lin2
      thus ?thesis using hyp by auto
    next
      case Reco2
      thus ?thesis using hyp by auto
    qed
  qed
qed

lemma P22_invariant:
shows "invariant (composition) P22"
proof (auto simp only:invariant_def)
  fix s1 s2
  assume 1:"reachable (composition) (s1,s2)"
  have P9:"P9 (s1,s2)" using P9_invariant 1
    by (simp add:invariant_def)
  show "P22 (s1,s2)"
  proof (simp only:P22.simps, rule impI)
    assume "initialized s2"
    show "dstate (f (s1,s2)) = dstate s2"
    proof (cases "dstate s2 = \<bottom>")
      case False
      thus ?thesis by auto
    next
      case True
      show "dstate  (f (s1,s2)) = dstate s2"
      proof -
        have "dstate s1 \<preceq> dstate s2"
          using `initialized s2` and `P9 (s1,s2)`
            by auto
        hence "dstate s1 = dstate s2" using True
          by (metis antisym bot)
        thus ?thesis by auto
      qed
    qed
  qed
qed

lemma P23_invariant:
shows "invariant (composition) P23"
proof (auto simp only:invariant_def)
  fix s1 s2
  assume 1:"reachable (composition) (s1,s2)"
  show "P23 (s1,s2)"
  proof (simp only:P23.simps, clarify)
    fix rs
    assume 2:"\<not>initialized s2" and 3:"rs\<in>pendingSeqs s1"
    show "rs\<in> pendingSeqs (f (s1,s2))"
    proof -
      { fix r
        assume 3:"r \<in> pendingReqs s1"
        have 4:"status s1 (fst r) = Pending \<or> status s1 (fst r) = Aborted"
          and 5:"pending s1 (fst r) = r"
        proof -
          have "P1 (s1,s2)" using 1 P1_invariant
            by (metis invariant_def)
          thus "status s1 (fst r) = Pending \<or> status s1 (fst r) = Aborted"
          and "pending s1 (fst r) = r"
            using 3 by (auto simp add:pendingReqs_def)
        qed
        have "r \<in> pendingReqs (f (s1,s2))" using 4
        proof
          assume "status s1 (fst r) = Pending"
          with 5 show ?thesis by (auto simp add:pendingReqs_def)
            (metis SLin_status.distinct(9)) 
        next
          assume 6:"status s1 (fst r) = Aborted"
          have 7:"pending s1 (fst r) = pending s2 (fst r)
            \<and> status s2 (fst r) \<in> {Pending,Aborted}"
          proof -
            have "P7 (s1,s2)" using 1 P7_invariant
              by (metis invariant_def)
            thus ?thesis using 2 6 by auto
          qed
          show ?thesis using 6 5 7 by (simp add:pendingReqs_def, metis)
        qed }
      thus ?thesis using 3 by (auto simp only:pendingSeqs_def)
    qed
  qed
qed

lemma P26_invariant:
shows "invariant (composition) P26"
proof (rule invariantI, simp_all only:split_paired_all)
  fix s1 s2
  assume "(s1,s2) \<in> ioa.start (composition)"
  thus "P26 (s1,s2)" using ids by (auto simp add:comp_simps)
next
  fix s1 s2 t1 t2 a
  assume hyp: "P26 (s1,s2)" and trans:"(s1,s2) \<midarrow>a\<midarrow>composition\<longrightarrow> (t1,t2)"
  and reach:"reachable composition (s1,s2)"
  show "P26 (t1,t2)" using trans and hyp
  proof (cases rule:trans_elim)
    case Lin2
    hence 1:"dstate s2 \<preceq> dstate t2" 
      by auto (metis less_eq_def)
    have 2:"t2 = s2\<lparr>dstate := dstate t2\<rparr>" and 3:"s1 = t1"
      using Lin2(1) by auto
    show ?thesis 
    proof (simp, clarify)
      fix p
      assume 4:"status t1 p = Aborted"
        and 5:"\<not> contains (dstate t2) (pending t1 p)"
      have 6:"status s1 p = Aborted" using 3 4 by auto
      have 7:"pending s1 p = pending t1 p" using 3 by simp
      have 8:"\<not> contains (dstate s2) (pending s1 p)"
        using 1 5 7 
          by simp (metis contains_star less_eq_def)
      have 11:"status s2 p \<in> {Pending,Aborted}" 
        and 9:"pending s1 p = pending s2 p" using hyp 6 8 by auto
      show "(status t2 p = Pending \<or> status t2 p = Aborted) 
        \<and> pending t1 p = pending t2 p"
      proof -
        from 2 have "pending s2 = pending t2" 
            and "status s2 = status t2" by ((cases s2, cases t2, auto)+)
        thus ?thesis using 9 3 11 by auto
      qed
    qed
  next
    case Reco2
    show ?thesis 
    proof (simp,clarify)
      fix p
      assume 1:"status t1 p = Aborted"
      have 2:"status s1 p = Aborted" and 3:"\<not>initialized s2"
        using 1 Reco2(1) by auto
      have 4:"P7 (s1,s2)" using reach P7_invariant
        by (metis invariant_def)
      have 5:"status s2 p \<in> {Pending,Aborted}" 
      and 6:"pending s1 p = pending s2 p" using 3 4 2 by auto
      show "(status t2 p = Pending \<or> status t2 p = Aborted) 
        \<and> pending t1 p = pending t2 p" using 5 6 Reco2(1) by auto
    qed
  next
    case Lin1
    thus ?thesis using hyp by force
  next
    case Response1
    thus ?thesis using hyp by force
  next
    case Response2
    thus ?thesis using hyp by force
  next
    case Invoke2
    thus ?thesis using hyp by force
  next
    case Switch1
    thus ?thesis using hyp by force
  next
    case Switch2
    thus ?thesis using hyp by force
  next
    case Invoke1
    thus ?thesis using hyp by force
  qed 
qed

lemma P25_invariant:
shows "invariant (composition) P25" 
proof (auto simp only:invariant_def)
  fix s1 s2
  assume reach:"reachable (composition) (s1,s2)"
  show "P25 (s1,s2)"
  proof (simp only:P25.simps, clarify)
    fix ivs
    assume 1:"ivs \<in> initSets s2" and 2:"initialized s2"
      and 3:"dstate s2 \<preceq> \<Sqinter>ivs"
    obtain rs' where 4:"dstate s2 \<star> rs' = \<Sqinter>ivs"
    and 5:"rs' \<in> pendingSeqs s1" and 6:"\<forall> r \<in> set rs' . \<not> contains (dstate s2) r"
    proof -
      have 5:"dstate s1 \<preceq> dstate s2"
      proof -
        have P9:"P9 (s1,s2)" using P9_invariant reach
          by (simp add:invariant_def)
        thus ?thesis using 2 by auto
      qed
      obtain rs where 6:"\<Sqinter>ivs = dstate s1 \<star> rs" and 7:"rs \<in> pendingSeqs s1"
      proof -
        have P8a:"P8a (s1,s2)" using P8a_invariant reach
          by (simp add:invariant_def)
        thus ?thesis using that 1 by auto
      qed
      have "\<exists> rs' . dstate s2 \<star> rs' = \<Sqinter> ivs \<and> rs' \<in> pendingSeqs s1"
        using 3 5 6 7 consistency[of "dstate s1" "dstate s2" "\<Sqinter>ivs" rs]
          by (force simp add:pendingSeqs_def)
      with this obtain rs' where "\<Sqinter>ivs = dstate s2 \<star> rs'" 
        and "rs' \<in> pendingSeqs s1" by metis
      with this show ?thesis using idem_star2 that 
        by (metis mem_Collect_eq pendingSeqs_def subset_trans)
    qed
    have 7:"rs' \<in> pendingSeqs (f (s1,s2))"
    proof -
      { fix r
        assume "r \<in> set rs'"
        with this obtain p where 8:"status s1 p = Pending 
          \<or> status s1 p = Aborted" 
        and 9:"r = pending s1 p"
          using 5 by (auto simp add:pendingReqs_def pendingSeqs_def)
        from 8 have "r \<in> pendingReqs (f (s1,s2))"
        proof 
          assume "status s1 p = Pending"
          thus ?thesis using 9 by (simp add:pendingReqs_def)
            (metis SLin_status.distinct(9))
        next
          assume 10:"status s1 p = Aborted"
          hence "status (f (s1,s2)) p = status s2 p"
            and "pending (f (s1,s2)) p = pending s2 p" by simp_all
          moreover 
          have "status s2 p \<in> {Pending,Aborted} \<and> pending s2 p = pending s1 p" 
          proof -
            have "\<not> contains (dstate s2) r"
              using 6 `r \<in> set rs'` by simp
            moreover 
            have "P26 (s1,s2)" using reach P26_invariant
              by (metis invariant_def)
            ultimately show ?thesis using 10 9 by force
          qed
          ultimately show ?thesis using 9 by (simp only:pendingReqs_def, force) 
        qed }
      thus ?thesis by (auto simp add:pendingSeqs_def)
    qed
    show "\<exists> rs \<in> pendingSeqs (f (s1,s2)) . \<Sqinter>ivs = dstate s2 \<star> rs"
      using 4 7 by force
  qed
qed

subsection {* Proof of the Idempotence Theorem *}

declare %invisible
  hide_asig_def[simp]
  asig_comp2_def[simp]
  externals_def[simp]
  comp_simps[simp]

theorem idempotence: 
  shows "((composition) =<| (ioa 0 id2))"
proof -
  have same_input_sig:"inp (composition) = inp (ioa 0 id2)" 
    -- {*First we show that both automata have the same input and output signature*}
      using  ids by auto
  moreover
  have same_output_sig:"out (composition) = out (ioa 0 id2)" 
    -- {*Then we show that output signatures match*}
    using ids by auto
  moreover
  have "traces (composition) \<subseteq> traces (ioa 0 id2)"
    -- {*Finally we show trace inclusion*}
  proof - 
    have "ext (composition) = ext (ioa 0 id2)"  
      -- {*First we show that they have the same external signature*}
      using same_input_sig and same_output_sig by simp
    moreover
    have "is_ref_map f (composition) (ioa 0 id2)"
      -- {*Then we show that @{text f_comp} is a refinement mapping*}
    proof (auto simp only:is_ref_map_def)
      fix s1 s2
      assume 1:"(s1,s2) \<in> ioa.start (composition)"
      show "f (s1,s2) \<in> ioa.start (ioa 0 id2)"
      proof -
        have 2:"ioa.start (ioa 0 id2) = start (0::nat)" by simp
        have 3:"ioa.start (composition) 
          = start (0::nat) \<times> start id1" by fastforce
        show ?thesis
          using 1 2 3 by simp 
      qed
    next
      fix s1 s2 t1 t2 :: "('a,'b,'c)SLin_state" and a :: "('a,'b,'c,'d)SLin_action"
      assume reach:"reachable (composition) (s1,s2)"
      and trans:"(s1,s2) \<midarrow>a\<midarrow>(composition)\<longrightarrow> (t1,t2)"
      define u where "u = f (s1,s2)"
      define u' where "u' = f (t1,t2)"
      txt {* Lemmas and invariants *}
      have "pendingReqs s2 \<subseteq> pendingReqs u"
      proof -
        have "P6 (s1,s2)" using reach P6_invariant
          by (metis invariant_def)
        thus ?thesis
          by (force simp add:pendingReqs_def u_def)
      qed
      note lem1 = this
      have "initialized u" by (auto simp add:u_def)
      have "P1 (s1,s2)" and "P1 (t1,t2)" using reach P1_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P6 (s1,s2)" and "P6 (t1,t2)" using reach P6_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P7 (s1,s2)" and "P7 (t1,t2)" using reach P7_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P8 (s1,s2)" and "P8 (t1,t2)" using reach P8_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P9 (s1,s2)" and "P9 (t1,t2)" using reach P9_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P10 (s1,s2)" and "P10 (t1,t2)" using reach P10_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P13 (s1,s2)" and "P13 (t1,t2)" using reach P13_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P15 (s1,s2)" and "P15 (t1,t2)" using reach P15_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P16 (s1,s2)" and "P16 (t1,t2)" using reach P16_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P17 (s1,s2)" and "P17 (t1,t2)" using reach P17_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P19 (s1,s2)" and "P19 (t1,t2)" using reach P19_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P21 (s1,s2)" and "P21 (t1,t2)" using reach P21_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P22 (s1,s2)" and "P22 (t1,t2)" using reach P22_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P25 (s1,s2)" and "P25 (t1,t2)" using reach P25_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P8a (s1,s2)" and "P8a (t1,t2)" using reach P8a_invariant
        trans invariant_def by (metis , metis reachable_n)
      have "P23 (s1,s2)" and "P23 (t1,t2)" using reach P23_invariant
        trans invariant_def by (metis , metis reachable_n)

      show "\<exists> e . refines e (s1,s2) a (t1,t2) (ioa 0 id2) f" 
        using trans 
      proof (cases rule:trans_elim)
        case (Invoke1 i p c)
        let ?e = "(u,[(a,u')])"
        have 1:"is_exec_frag_of (ioa 0 id2) ?e"
        proof -
          have 1:"status s1 p = Ready" and 2:"t2 = s2"
          and 3:"t1 = s1\<lparr>pending := (pending s1)(p := (p,c)), 
            status := (status s1)(p := Pending)\<rparr>"
            using Invoke1(1) by auto
          have 4:"status u p = Ready" using 1 u_def by auto
          have 5:"u' = u\<lparr>pending := (pending u)(p := (p,c)), 
            status := (status u)(p := Pending)\<rparr>" 
              using 2 3 u_def u'_def by auto
          have 6:"Inv p c u u'" using 4 5 by force
          show ?thesis using 6 Invoke1(3) ids by simp
        qed
        have 2:"a \<in> ext (ioa 0 id2)" and 3:"trace (ioa.asig (ioa 0 id2)) ?e = [a]"
          using Invoke1(2,3) ids by (auto simp add:trace_def schedule_def filter_act_def)
        show ?thesis using 1 2 3 
          by (simp only:refines_def u_def u'_def) 
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case (Invoke2 i p c)
        let ?e = "(u,[(a,u')])"
        have 1:"is_exec_frag_of (ioa 0 id2) ?e"
        proof -
          have 1:"status s2 p = Ready" and 2:"t1 = s1"
          and 3:"t2 = s2\<lparr>pending := (pending s2)(p := (p,c)), 
            status := (status s2)(p := Pending)\<rparr>"
            using Invoke2(1) by auto   
          have 4:"status u p = Ready" using 1 u_def `P6 (s1,s2)` by auto
          have 5:"u' = u\<lparr>pending := (pending u)(p := (p,c)), 
            status := (status u)(p := Pending)\<rparr>" 
              using 2 3 u_def u'_def `P6 (t1,t2)` by fastforce
          have 6:"Inv p c u u'" using 4 5 by force
          show ?thesis using 6 Invoke2(3) ids by simp
        qed
        have 2:"a \<in> ext (ioa 0 id2)" 
        and 3:"trace (ioa.asig (ioa 0 id2)) ?e = [a]"
          using Invoke2(2,3) by (auto simp add:trace_def schedule_def filter_act_def)
        show ?thesis using 1 2 3
          by (simp only:refines_def u_def u'_def) 
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case (Response2 i p ou)
        let ?e = "(u,[(a,u')])"
        have 1:"is_exec_frag_of (ioa 0 id2) ?e"
        proof -
          have 1:"status s1 p = Aborted \<and> status t1 p = Aborted"
          proof -
            show ?thesis using `P6 (s1,s2)` `P6 (t1,t2)` 
              Response2(1) by force
          qed
          have 2:"status u p = Pending \<and> initialized u" 
            using 1 Response2(1) u_def by auto
          have  3:"u' = u\<lparr>status := (status u)(p := Ready)\<rparr>"
            using 1 Response2(1) u_def u'_def
              by (cases u, cases u', auto)
          have 4:"ou = \<gamma> (dstate u) (pending u p) \<and> contains (dstate u) (pending u p)"
          proof (cases "dstate s2 = \<bottom>")
            case False
            thus ?thesis using 1 Response2(1) u_def by auto
          next
            case True
            have "dstate s1 = dstate s2" 
            proof -
              have "dstate s1 \<preceq> dstate s2"
                using Response2(1)  `P9 (s1,s2)` by auto
              with True show ?thesis by (metis antisym bot) 
            qed
            thus ?thesis using 1 Response2(1) u_def by auto
          qed
          show ?thesis using 2 3 4 Response2(3) ids by auto
        qed
        have 2:"a \<in> ext (ioa 0 id2)" 
        and 3:"trace (ioa.asig (ioa 0 id2)) ?e = [a]"
          using Response2(2,3) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        show ?thesis using 1 2 3
          by (simp only:refines_def u_def u'_def)
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case (Response1 i p ou)
        let ?e = "(u,[(a,u')])"
        have 1:"is_exec_frag_of (ioa 0 id2) ?e"
        proof (cases "dstate s2 = \<bottom>")
          case True
          have 1:"status u p = Pending \<and> initialized u" 
            using Response1(1) u_def by auto
          have  2:"u' = u\<lparr>status := (status u)(p := Ready)\<rparr>"
            using Response1(1) u_def u'_def
              by (cases u, cases u', auto)
          have 3:"ou = \<gamma> (dstate u) (pending u p)
            \<and> contains (dstate u) (pending u p)"
            using Response1(1) True u_def by auto
          show ?thesis using 1 2 3 `initialized u` Response1(3) ids by auto
        next
          case False
          have 1:"status u p = Pending \<and> initialized u" 
            using Response1(1) u_def by auto
          have  2:"u' = u\<lparr>status := (status u)(p := Ready)\<rparr>"
            using Response1(1) u_def u'_def
              by (cases u, cases u', auto)
          have 3:"ou = \<gamma> (dstate u) (pending u p)"
            and 4:"contains (dstate u) (pending u p)"
          proof -
            have 2:"contains (dstate s1) (pending s1 p)"
              using Response1(1) by auto
            show "contains (dstate u) (pending u p)"
            proof -
              have 3:"dstate s1 \<preceq> dstate u"
              proof -
                have "initialized s2" using `P16 (s1,s2)` False
                  by auto
                thus ?thesis using `P9 (s1,s2)` u_def False refl by simp
              qed
              have 4:"pending s1 p = pending u p" 
                using u_def Response1(1) by force
              show ?thesis 
                using 2 3 4 by (metis contains_star less_eq_def)
            qed
            have 4:"\<gamma> (dstate s1) (pending s1 p) = \<gamma> (dstate u) (pending u p)"
            proof -
              have 4:"pending s1 p = pending u p" 
                using u_def Response1(1) by force
              obtain rs where 5:"dstate u = dstate s1 \<star> rs"
                and 6:"\<forall> r \<in> set rs . fst r \<noteq> p" 
              proof -
                have 7:"dstate u = dstate s2" using u_def False by simp
                have 6:"status s1 p = Pending 
                  \<and> contains (dstate s1) (pending s1 p)" 
                    using Response1(1) by force
                have 8:"initialized s2" using False `P16 (s1,s2)`
                  by auto
                show ?thesis using that `P17 (s1,s2)` 6 8 7 by fastforce
              qed
              have 7:"fst (pending s1 p) = p"  
                using Response1(1) `P1 (s1,s2)` by auto
              show ?thesis using 4 5 6 7 2 idem2_star by auto
            qed
            thus "ou = \<gamma> (dstate u) (pending u p)" 
              using Response1(1) by simp
          qed
          thus ?thesis using 1 2 3 Response1(3) ids by auto
        qed
        have 2:"a \<in> ext (ioa 0 id2)" 
        and 3:"trace (ioa.asig (ioa 0 id2)) ?e = [a]"
          using Response1(2,3) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        show ?thesis using 1 2 3
          by (simp only:refines_def u_def u'_def)
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case (Reco2)
        let ?e = "(u,[(Linearize 0,u')])"
        have "is_exec_frag_of (ioa 0 id2) ?e"
        proof -
          obtain rs where 1:"rs \<in> pendingSeqs u"
            and 2:"dstate u' = dstate u \<star> rs" 
            and 3:"\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
          proof -
            obtain rs where "set rs \<subseteq> pendingReqs s1 \<union> pendingReqs s2"
            and "dstate t2 = dstate s1 \<star> rs"
            and "\<forall> av \<in> abortVals s2 . dstate t2 \<preceq> av"
            proof -
              obtain ivs rs where 3:"ivs \<subseteq> initVals s2" and 4:"ivs \<noteq> {}"
              and 5:"dstate t2 = \<Sqinter>ivs \<star> rs" and 7:"rs \<in> pendingSeqs s2"
              and 6:"\<forall> av \<in> abortVals s2 . dstate t2 \<preceq> av"
                using Reco2(1)
                by (auto simp add:safeInits_def initSets_def) 
                  (metis all_not_in_conv)
              obtain rs' where "\<Sqinter>ivs = dstate s1 \<star> rs'"
              and "set rs' \<subseteq> pendingReqs s1"
              proof -
                { fix iv
                  assume 7:"iv \<in> ivs"
                  have "\<exists> rs . set rs \<subseteq> pendingReqs s1 
                    \<and> iv = dstate s1 \<star> rs"
                      using `P8 (s1,s2)` 7 3 by auto
                        (metis mem_Collect_eq pendingSeqs_def set_rev_mp) }
                moreover have "finite ivs" using `P13 (s1,s2)` 3
                    by (metis P13.simps rev_finite_subset)
                ultimately show ?thesis using that glb_common_set 4
                  by metis
              qed
              hence "dstate t2 = dstate s1 \<star> (rs'@rs)
                \<and> set (rs'@rs) \<subseteq> pendingReqs s1 \<union> pendingReqs s2" using 5 7
                  by (metis (lifting, no_types) Un_commute Un_mono 
                      exec_append mem_Collect_eq pendingSeqs_def set_append)
              thus ?thesis using that 6 by blast
            qed
            moreover
            have "pendingReqs s1 \<union> pendingReqs s2 \<subseteq> pendingReqs u"
            proof -
              note `pendingReqs s2 \<subseteq> pendingReqs u`
              moreover
              have "pendingReqs s1 \<subseteq> pendingReqs u"
                using Reco2(1) `P7 (s1,s2)`
                  by (auto simp add:pendingReqs_def u_def)
              ultimately show ?thesis by auto
            qed
            moreover 
            have "abortVals u = abortVals s2" by (auto simp add:u_def)
            moreover
            have "dstate u = dstate s1" using `P16 (s1,s2)`
              Reco2(1) u_def by force
            moreover
            have "dstate u' = dstate t2" 
              using Reco2(1) `P22 (t1,t2)` by (auto simp add:u'_def)
            ultimately show ?thesis using that 
              by (auto simp add:pendingSeqs_def, blast)
          qed
          moreover
          have "u' = u\<lparr>dstate := dstate u \<star> rs\<rparr>"
            using 2 Reco2(1) u_def u'_def by force
          moreover
          note `initialized u`
          ultimately show ?thesis by auto 
        qed
        moreover
        have "a \<notin> ext (ioa 0 id2)" 
        and "trace (ioa.asig (ioa 0 id2)) ?e = []"
          using Reco2(2) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        ultimately show ?thesis
          by (simp only:refines_def u_def u'_def)
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case (Switch1 p c av)
        let ?e = "(u,[])"
        have "is_exec_frag_of (ioa 0 id2) ?e" by auto
        moreover
        have "a \<notin> ext (ioa 0 id2)"
        and "trace (ioa.asig (ioa 0 id2)) ?e = []"
          using Switch1(2) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        moreover
        have "u = u'" using Switch1(1) u_def u'_def by auto
        ultimately show ?thesis 
          using refines_def[of ?e "(s1,s2)" a "(t1,t2)" "ioa 0 id2" f]
            u_def u'_def by (metis last_state.simps(1) fst_conv)
      next

        case Lin2
        let ?e = "(u,[(Linearize 0,u')])"
        have "is_exec_frag_of (ioa 0 id2) ?e"
        proof -
          have "u' = u\<lparr>dstate := dstate u'\<rparr>" using Lin2(1)
            by (auto simp add:u_def u'_def)
          moreover
          note `initialized u` 
          moreover
          obtain rs where "dstate u' = dstate u \<star> rs"
            and "rs \<in> pendingSeqs u" 
            and "\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
          proof -
            obtain rs where 1:"dstate t2 = dstate s2 \<star> rs"
              and 2:"rs \<in> pendingSeqs s2" 
              and 3:"\<forall> av \<in> abortVals s2 . dstate t2 \<preceq> av"
              using Lin2(1) by force
            have 4:"rs \<in> pendingSeqs u" 
              using  2 and `pendingReqs s2 \<subseteq> pendingReqs u`
                by (metis mem_Collect_eq pendingSeqs_def subset_trans)
            have 5:"dstate u' = dstate u \<star> rs" 
              and 6:"\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
            proof -
              have 7:"dstate u = dstate s2 \<and> dstate u' = dstate t2"
                using `P22 (s1,s2)` and `P22 (t1,t2)` Lin2(1)
                  by (auto simp add:u_def u'_def)
              show "dstate u' = dstate u \<star> rs" using 7 1 by auto
              show "\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
              proof -
                have "abortVals s2 = abortVals u" by (auto simp add:u_def)
                thus ?thesis using 7 3 by simp
              qed
            qed
            show ?thesis using that 4 5 6 by auto
          qed
          ultimately show ?thesis by auto
        qed
        moreover
        have "a \<notin> ext (ioa 0 id2)"
        and "trace (ioa.asig (ioa 0 id2)) ?e = []"
          using Lin2(2) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        ultimately show ?thesis
          by (simp only:refines_def u_def u'_def)
            (metis fst_conv last_state.simps(2) snd_conv)
      next

        case Lin1
        have "u' = u\<lparr>dstate := dstate u'\<rparr>" using Lin1(1)
          by (auto simp add:u_def u'_def)
        show ?thesis
        proof (cases "initialized s2")
          case False
          let ?e = "(u,[(Linearize 0,u')])"
          have "is_exec_frag_of (ioa 0 id2) ?e"
          proof -
            note `u' = u\<lparr>dstate := dstate u'\<rparr>`
            moreover
            note `initialized u` 
            moreover
            obtain rs where "dstate u' = dstate u \<star> rs"
              and "rs \<in> pendingSeqs u" 
              and "\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
            proof -
              obtain rs where 1:"dstate t1 = dstate s1 \<star> rs"
                and 2:"rs \<in> pendingSeqs s1" 
                and 3:"\<forall> av \<in> abortVals s1 . dstate t1 \<preceq> av"
                using Lin1(1) by force
              have 5:"pendingSeqs s1 \<subseteq> pendingSeqs u" 
                using False `P7 (s1,s2)`
                  by (auto simp add:pendingReqs_def pendingSeqs_def u_def)
              have 6:"dstate u = dstate s1 \<and> dstate u' = dstate t1"
                using `P16 (s1,s2)` False Lin1(1)
                  by (auto simp add:u_def u'_def)
              have 4:"\<forall> av \<in> abortVals u . dstate u' \<preceq> av"
              proof (cases "abortVals u = {}")
                case True
                thus ?thesis by auto
              next
                case False
                have "dstate u' = dstate t1" using 6 by auto
                moreover have "abortVals u = abortVals t2" 
                  using Lin1(1) by (auto simp add:u_def)
                moreover have "dstate t1 \<preceq> \<Sqinter>(abortVals t1)" 
                proof - 
                  have "abortVals t1 = abortVals s1" using Lin1(1) by auto
                  moreover have "abortVals t1 \<noteq> {}" using False `P19 (t1,t2)`
                    Lin1(1) by (simp add: u_def)
                  ultimately show ?thesis using 3 `P13 (t1,t2)`  
                    by simp (metis boundedI) 
                qed
                ultimately show ?thesis using `P21 (t1,t2)` 3
                  by (metis P21.simps coboundedI2 orderE)
              qed
              show ?thesis using 1 2 3 4 5 6 that by auto
            qed
            ultimately show ?thesis by auto
          qed
          moreover
          have "a \<notin> ext (ioa 0 id2)"
          and "trace (ioa.asig (ioa 0 id2)) ?e = []"
            using Lin1(2) ids 
              by (auto simp add:trace_def schedule_def filter_act_def)
          ultimately show ?thesis
            by (simp only:refines_def u_def u'_def)
              (metis fst_conv last_state.simps(2) snd_conv)
        next
          case True
          let ?e = "(u,[])"
          have "is_exec_frag_of (ioa 0 id2) ?e" by auto
          moreover
          have "a \<notin> ext (ioa 0 id2)"
          and "trace (ioa.asig (ioa 0 id2)) ?e = []"
            using Lin1(2) ids 
              by (auto simp add:trace_def schedule_def filter_act_def)
          moreover have "last_state ?e = u'"
          proof -
            have "dstate u = dstate s2 \<and> dstate u' = dstate t2"
              using `P22 (s1,s2)` and `P22 (t1,t2)` and True and Lin1(1)
                by (auto simp add:u_def u'_def)
            thus ?thesis using Lin1(1) `u' = u\<lparr>dstate := dstate u'\<rparr>`
              by simp
          qed
          ultimately show ?thesis 
            using refines_def[of ?e "(s1,s2)" a "(t1,t2)" "ioa 0 id2" f]
              by (simp only:u_def u'_def, auto)
        qed
      next

        case (Switch2 p c av)
        let ?e = "(u,[(a,u')])"
        have 1:"is_exec_frag_of (ioa 0 id2) ?e"
        proof -        
          have 1:"u' = u\<lparr>abortVals := (abortVals u) \<union> {av},
            status := (status u)(p := Aborted)\<rparr>"
            and 2:"av \<in> safeAborts s2" and 3:"status u p = Pending"
            and 4:"pending u p = (p,c)"
          proof -
            have 1:"t2 = s2\<lparr>abortVals := (abortVals s2) \<union> {av},
              status := (status s2)(p := Aborted)\<rparr>"
              and 2:"av \<in> safeAborts s2" and 3:"s1 = t1" 
              and 4:"status s2 p = Pending"
                using Switch2(1) by auto
            show 5:"status u p = Pending" using `P6 (s1,s2)` 4
              by (auto simp add:u_def)
            have 6:"status u' p = Aborted" using `P6 (t1,t2)` 1
              by (auto simp add:u'_def)
            show "pending u p = (p,c)" using `P6 (s1,s2)` 4 Switch2(1)
              by (auto simp add:u_def)
            show "u' = u\<lparr>abortVals := (abortVals u) \<union> {av},
              status := (status u)(p := Aborted)\<rparr>" using 1 3 5 6
                by (auto simp add:u_def u'_def)
            show "av \<in> safeAborts s2" using 2 by assumption
          qed
          have 5:"av \<in> safeAborts u" 
          proof (cases "initialized s2")
            case True
            hence 6:"dstate u = dstate s2" using `P22 (s1,s2)`  
              by (auto simp add:u_def)
            have "(\<exists> rs \<in> pendingSeqs s2 . av = dstate s2 \<star> rs)
              \<or> (dstate s2 \<preceq> av \<and> (\<exists> ivs \<in> initSets s2 . 
                dstate s2 \<preceq> \<Sqinter>ivs \<and> (\<exists> rs \<in> pendingSeqs s2 . av = \<Sqinter>ivs \<star> rs)))"
            proof -
              have "av \<in> initAborts s2" 
                using 2 and True by (auto simp add:safeAborts_def)
              thus ?thesis by (auto simp add:initAborts_def)
            qed
            thus ?thesis
            proof
              assume "\<exists> rs \<in> pendingSeqs s2 . av = dstate s2 \<star> rs"
              moreover note `initialized u` 
              ultimately show ?thesis using `pendingReqs s2 \<subseteq> pendingReqs u` 6 
                by (simp add:safeAborts_def initAborts_def)
                  (metis less_eq_def mem_Collect_eq pendingSeqs_def 
                    sup.coboundedI2 sup.orderE) 
            next
              assume 7:"dstate s2 \<preceq> av \<and> (\<exists> ivs \<in> initSets s2 . 
                dstate s2 \<preceq> \<Sqinter>ivs \<and> (\<exists> rs \<in> pendingSeqs s2 . av = \<Sqinter>ivs \<star> rs))"
              show ?thesis
              proof -
                have 8:"dstate u \<preceq> av" using 7 6 by auto
                obtain ivs rs' where 9:"ivs \<in> initSets s2" 
                  and 10:"dstate s2 \<preceq> \<Sqinter>ivs" 
                  and 11:"rs' \<in> pendingSeqs s2 \<and> av = \<Sqinter>ivs \<star> rs'" 
                    using 7 by auto
                have 12:"dstate u = dstate s2" using True `P22 (s1,s2)`
                  by (auto simp add:u_def)
                moreover
                obtain rs where "rs \<in> pendingSeqs u" and "\<Sqinter>ivs = dstate s2 \<star> rs"
                  using `P25 (s1,s2)` True 9 10 by (auto simp add:u_def)
                ultimately have  "av = dstate u \<star> (rs@rs')" 
                  and "rs@rs' \<in> pendingSeqs u"
                  using 11 by (simp_all add:pendingSeqs_def)
                    (metis exec_append, metis lem1 subset_trans)
                thus ?thesis using 8 `initialized u`
                  by (auto simp add:safeAborts_def initAborts_def)
              qed
            qed
          next
            case False
            with 2 have 0:"av \<in> uninitAborts s2" by (auto simp add:safeAborts_def)
            show ?thesis
            proof -
              obtain ivs rs where 1:"ivs \<in> initSets s2" 
                and 2:"rs \<in>pendingSeqs s2"
                and 3:"av = \<Sqinter>ivs \<star> rs" 
                using 0 by (auto simp add:uninitAborts_def)
              have 4:"rs \<in> pendingSeqs u" using lem1 2 
                by (auto simp add:pendingSeqs_def)
              have 5:"dstate u = dstate s1" using False `P10 (s1,s2)`
                by (auto simp add:u_def) 
              obtain rs' where 6:"\<Sqinter>ivs = dstate s1 \<star> rs'" 
                and 7:"rs' \<in> pendingSeqs s1"
                  using 1 `P8a (s1,s2)` by auto
              have 8:"rs' \<in> pendingSeqs u" using False `P23 (s1,s2)` 7
                by (auto simp add:u_def)
              have 9:"av = dstate u \<star> (rs'@rs)" using 3 5 6
                by (metis exec_append) 
              have 10:"rs'@rs \<in> pendingSeqs u"
                using 4 8 by (auto simp add:pendingSeqs_def)
              show ?thesis using 9 10 `initialized u`
                by (auto simp add:safeAborts_def initAborts_def less_eq_def)
            qed
          qed
          show ?thesis using 1 3 4 5 Switch2(2) by auto
        qed
        moreover
        have "a \<in> ext (ioa 0 id2)" 
        and "trace (ioa.asig (ioa 0 id2)) ?e = [a]"
          using Switch2(2) ids 
            by (auto simp add:trace_def schedule_def filter_act_def)
        ultimately show ?thesis
          by (simp only:refines_def u_def u'_def)
            (metis fst_conv last_state.simps(2) snd_conv)
      qed
    qed
    ultimately show ?thesis using ref_map_soundness by blast
  qed
  ultimately show ?thesis by (metis ioa_implements_def)
qed

end

end
