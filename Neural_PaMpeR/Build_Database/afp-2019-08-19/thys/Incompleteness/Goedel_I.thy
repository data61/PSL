chapter \<open>Section 6 Material and Gödel's First Incompleteness Theorem\<close>

theory Goedel_I
imports Pf_Predicates Functions
begin

section\<open>The Function W and Lemma 6.1\<close>

subsection\<open>Predicate form, defined on sequences\<close>

definition SeqWR :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqWR s k y \<equiv> LstSeq s k y \<and> app s 0 = 0 \<and>
                        (\<forall>l \<^bold>\<in> k. app s (succ l) = q_Eats (app s l) (app s l))"

nominal_function SeqWRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl); atom sl \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqWRP s k y = LstSeqP s k y AND
          HPair Zero Zero IN s AND
          All2 l k (Ex sl (HPair (Var l) (Var sl) IN s AND
                           HPair (SUCC (Var l)) (Q_Succ (Var sl)) IN s))"
  by (auto simp: eqvt_def SeqWRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqWRP_fresh_iff [simp]: "a \<sharp> SeqWRP s k y \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> y" (is ?thesis1)
    and eval_fm_SeqWRP [simp]:   "eval_fm e (SeqWRP s k y) \<longleftrightarrow> SeqWR \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e \<lbrakk>y\<rbrakk>e"  (is ?thesis2)
    and SeqWRP_sf [iff]:         "Sigma_fm (SeqWRP s k y)"  (is ?thsf)
proof -
  obtain l::name and sl::name where "atom l \<sharp> (s,k,sl)" "atom sl \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
      by (auto simp: SeqWR_def q_defs LstSeq_imp_Ord
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"])
qed

lemma SeqWRP_subst [simp]:
      "(SeqWRP s k y)(i::=t) = SeqWRP (subst i t s) (subst i t k) (subst i t y)"
proof -
  obtain l::name and sl::name
    where "atom l \<sharp> (s,k,sl,t,i)" "atom sl \<sharp> (s,k,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqWRP.simps [where l=l and sl=sl])
qed

lemma SeqWRP_cong:
  assumes "H \<turnstile> s EQ s'" and  "H \<turnstile> k EQ k'" and  "H \<turnstile> y EQ y'"
  shows "H \<turnstile> SeqWRP s k y IFF SeqWRP s' k' y'"
  by (rule P3_cong [OF _ assms], auto)

declare SeqWRP.simps [simp del]

subsection\<open>Predicate form of W\<close>

definition WR :: "hf \<Rightarrow> hf \<Rightarrow> bool"
  where "WR x y \<equiv> (\<exists>s. SeqWR s x y)"

nominal_function WRP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (x,y)\<rbrakk> \<Longrightarrow>
    WRP x y = Ex s (SeqWRP (Var s) x y)"
  by (auto simp: eqvt_def WRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows WRP_fresh_iff [simp]: "a \<sharp> WRP x y \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y" (is ?thesis1)
    and eval_fm_WRP [simp]:   "eval_fm e (WRP x y) \<longleftrightarrow> WR \<lbrakk>x\<rbrakk>e \<lbrakk>y\<rbrakk>e"  (is ?thesis2)
    and sigma_fm_WRP [simp]:  "Sigma_fm (WRP x y)"  (is ?thsf)
proof -
  obtain s::name where "atom s \<sharp> (x,y)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: WR_def)
qed

lemma WRP_subst [simp]: "(WRP x y)(i::=t) = WRP (subst i t x) (subst i t y)"
proof -
  obtain s::name where "atom s \<sharp> (x,y,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: WRP.simps [of s])
qed

lemma WRP_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> u EQ u' \<Longrightarrow> H \<turnstile> WRP t u IFF WRP t' u'"
  by (rule P2_cong) auto

declare WRP.simps [simp del]

lemma WR0_iff: "WR 0 y \<longleftrightarrow> y=0"
  by (simp add: WR_def SeqWR_def) (metis LstSeq_1 LstSeq_app)

lemma WR0: "WR 0 0"
  by (simp add: WR0_iff)

lemma WR_succ_iff: assumes i: "Ord i" shows "WR (succ i) z = (\<exists>y. z = q_Eats y y \<and> WR i y)"
proof
  assume "WR (succ i) z"
  then obtain s where s: "SeqWR s (succ i) z"
    by (auto simp: WR_def i)
  moreover then have "app s (succ i) = z"
    by (auto simp: SeqWR_def)
  ultimately show "\<exists>y. z = q_Eats y y \<and> WR i y" using i 
    by (auto simp: WR_def SeqWR_def) (metis LstSeq_trunc hmem_succ_self)
next
  assume "\<exists>y. z = q_Eats y y \<and> WR i y"
  then obtain y where z: "z = q_Eats y y" and y: "WR i y"
    by blast
  thus "WR (succ i) z" using i
    apply (auto simp: WR_def SeqWR_def)
    apply (rule_tac x="insf s (succ i) (q_Eats y y)" in exI)
    apply (auto simp: LstSeq_imp_Seq_succ app_insf_Seq_if LstSeq_insf succ_notin_self)
    done
qed

lemma WR_succ: "Ord i \<Longrightarrow> WR (succ i) (q_Eats y y) = WR i y"
  by (metis WR_succ_iff q_Eats_iff)

lemma WR_ord_of: "WR (ord_of i) \<lbrakk>\<lceil>ORD_OF i\<rceil>\<rbrakk>e"
  by (induct i) (auto simp: WR0_iff WR_succ_iff quot_Succ q_defs)

text\<open>Lemma 6.1\<close>
lemma WR_quot_Var: "WR \<lbrakk>\<lceil>Var x\<rceil>\<rbrakk>e \<lbrakk>\<lceil>\<lceil>Var x\<rceil>\<rceil>\<rbrakk>e"
  by (auto simp: quot_Var quot_Succ)
     (metis One_nat_def Ord_ord_of WR_ord_of WR_succ htuple.simps q_Eats_def)

lemma ground_WRP [simp]: "ground_fm (WRP x y) \<longleftrightarrow> ground x \<and> ground y"
  by (auto simp: ground_aux_def ground_fm_aux_def supp_conv_fresh)

lemma prove_WRP:  "{} \<turnstile> WRP \<lceil>Var x\<rceil> \<lceil>\<lceil>Var x\<rceil>\<rceil>"
  by (auto simp: WR_quot_Var ground_aux_def supp_conv_fresh intro: Sigma_fm_imp_thm)

subsection\<open>Proving that these relations are functions\<close>

lemma SeqWRP_Zero_E:
  assumes "insert (y EQ Zero) H \<turnstile> A"  "H \<turnstile> k EQ Zero"
  shows "insert (SeqWRP s k y) H \<turnstile> A"
proof -
  obtain l::name and sl::name
    where "atom l \<sharp> (s,k,sl)" "atom sl \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: SeqWRP.simps [where s=s and l=l and sl=sl])
    apply (rule cut_same [where A = "LstSeqP s Zero y"])
    apply (blast intro: thin1 assms  LstSeqP_cong [OF Refl _ Refl, THEN Iff_MP_same])
    apply (rule cut_same [where A = "y EQ Zero"])
    apply (blast intro: LstSeqP_EQ)
    apply (metis rotate2 assms(1) thin1)
    done
qed

lemma SeqWRP_SUCC_lemma:
  assumes y': "atom y' \<sharp> (s,k,y)"
  shows "{SeqWRP s (SUCC k) y} \<turnstile> Ex y' (SeqWRP s k (Var y') AND y EQ Q_Succ (Var y'))"
proof -
  obtain l::name and sl::name
    where atoms: "atom l \<sharp> (s,k,y,y',sl)" "atom sl \<sharp> (s,k,y,y')"
    by (metis obtain_fresh)
  thus ?thesis using y'
    apply (auto simp: SeqWRP.simps [where s=s and l=l and sl=sl])
    apply (rule All2_SUCC_E' [where t=k, THEN rotate2], auto)
    apply (rule Ex_I [where x = "Var sl"], auto)
    apply (blast intro: LstSeqP_SUCC) \<comment> \<open>showing @{term"SeqWRP s k (Var sl)"}\<close>
    apply (blast intro: ContraProve LstSeqP_EQ)
    done
qed

lemma SeqWRP_SUCC_E:
  assumes y': "atom y' \<sharp> (s,k,y)" and k': "H \<turnstile> k' EQ (SUCC k)"
  shows "insert (SeqWRP s k' y) H  \<turnstile> Ex y' (SeqWRP s k (Var y') AND y EQ Q_Succ (Var y'))"
  using SeqWRP_cong [OF Refl k' Refl] cut1 [OF SeqWRP_SUCC_lemma [of y' s k y]]
  by (metis Assume Iff_MP_left Iff_sym y')

lemma SeqWRP_unique: "{OrdP x, SeqWRP s x y, SeqWRP s' x y'} \<turnstile> y' EQ y"
proof -
  obtain i::name and j::name and j'::name and k::name and sl::name and sl'::name and l::name and pi::name
    where  i: "atom i \<sharp> (s,s',y,y')" and j: "atom j \<sharp> (s,s',i,x,y,y')" and j': "atom j' \<sharp> (s,s',i,j,x,y,y')"
      and atoms: "atom k \<sharp> (s,s',i,j,j')" "atom sl \<sharp> (s,s',i,j,j',k)" "atom sl' \<sharp> (s,s',i,j,j',k,sl)"
                 "atom pi \<sharp> (s,s',i,j,j',k,sl,sl')"
    by (metis obtain_fresh)
  have "{OrdP (Var i)} \<turnstile> All j (All j' (SeqWRP s (Var i) (Var j) IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ Var j)))"
    apply (rule OrdIndH [where j=k])
    using i j j' atoms apply auto
    apply (rule rotate4)
    apply (rule OrdP_cases_E [where k=pi], simp_all)
    \<comment> \<open>Zero case\<close>
    apply (rule SeqWRP_Zero_E [THEN rotate3])
    prefer 2 apply blast
    apply (rule SeqWRP_Zero_E [THEN rotate4])
    prefer 2 apply blast
    apply (blast intro: ContraProve [THEN rotate4] Sym Trans)
    \<comment> \<open>SUCC case\<close>
    apply (rule Ex_I [where x = "Var pi"], auto)
    apply (metis ContraProve EQ_imp_SUBS2 Mem_SUCC_I2 Refl Subset_D)
    apply (rule cut_same)
    apply (rule SeqWRP_SUCC_E [of sl' s' "Var pi", THEN rotate4], auto)
    apply (rule cut_same)
    apply (rule SeqWRP_SUCC_E [of sl s "Var pi", THEN rotate7], auto)
    apply (rule All_E [where x = "Var sl", THEN rotate5], simp)
    apply (rule All_E [where x = "Var sl'"], simp)
    apply (rule Imp_E, blast)+
    apply (rule cut_same [OF Q_Succ_cong [OF Assume]])
    apply (blast intro: Trans [OF Hyp Sym] HPair_cong)
    done
  hence "{OrdP (Var i)} \<turnstile> (All j' (SeqWRP s (Var i) (Var j) IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ Var j)))(j::=y)"
    by (metis All_D)
  hence "{OrdP (Var i)} \<turnstile> (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) (Var j') IMP Var j' EQ y))(j'::=y')"
    using j j'
    by simp (drule All_D [where x=y'], simp)
  hence "{} \<turnstile> OrdP (Var i) IMP (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) y' IMP y' EQ y))"
    using j j'
    by simp (metis Imp_I)
  hence "{} \<turnstile> (OrdP (Var i) IMP (SeqWRP s (Var i) y IMP (SeqWRP s' (Var i) y' IMP y' EQ y)))(i::=x)"
    by (metis Subst emptyE)
  thus ?thesis using i
    by simp (metis anti_deduction insert_commute)
qed

theorem WRP_unique: "{OrdP x, WRP x y, WRP x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name
    where "atom s \<sharp> (x,y,y')"  "atom s' \<sharp> (x,y,y',s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqWRP_unique [THEN rotate3] WRP.simps [of s _ y]  WRP.simps [of s' _ y'])
qed

subsection\<open>The equivalent function\<close>

definition W :: "hf \<Rightarrow> tm"
  where "W \<equiv> hmemrec (\<lambda>f z. if z=0 then Zero else Q_Eats (f (pred z)) (f (pred z)))"

lemma W0 [simp]: "W 0 = Zero"
  by (rule trans [OF def_hmemrec [OF W_def]]) auto

lemma W_succ [simp]: "Ord i \<Longrightarrow> W (succ i) = Q_Eats (W i) (W i)"
  by (rule trans [OF def_hmemrec [OF W_def]]) (auto simp: ecut_apply SUCC_def W_def)

lemma W_ord_of [simp]: "W (ord_of i) = \<lceil>ORD_OF i\<rceil>"
  by (induct i, auto simp: SUCC_def quot_simps)

lemma WR_iff_eq_W: "Ord x \<Longrightarrow> WR x y \<longleftrightarrow> y = \<lbrakk>W x\<rbrakk>e"
proof (induct x arbitrary: y rule: Ord_induct2)
  case 0 thus ?case
    by (metis W0 WR0_iff eval_tm.simps(1))
next
  case (succ k) thus ?case
    by (auto simp: WR_succ_iff q_Eats_def)
qed


section\<open>The Function HF and Lemma 6.2\<close>

definition SeqHR :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "SeqHR x x' s k \<equiv>
       BuildSeq2 (\<lambda>y y'. Ord y \<and> WR y y')
                 (\<lambda>u u' v v' w w'. u = \<langle>v,w\<rangle> \<and> u' = q_HPair v' w') s k x x'"

subsection \<open>Defining the syntax: quantified body\<close>

nominal_function SeqHRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn');
          atom sl' \<sharp> (s,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn');
          atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn');
          atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn');
          atom sn' \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqHRP x x' s k =
      LstSeqP s k (HPair x x') AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                ((OrdP (Var sl) AND WRP (Var sl) (Var sl')) OR
                 Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       Var sl EQ HPair (Var sm) (Var sn) AND
                       Var sl' EQ Q_HPair (Var sm') (Var sn')))))))))))"
by (auto simp: eqvt_def SeqHRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows SeqHRP_fresh_iff [simp]:
      "a \<sharp> SeqHRP x x' s k \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
   and eval_fm_SeqHRP [simp]:
      "eval_fm e (SeqHRP x x' s k) \<longleftrightarrow> SeqHR \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e"  (is ?thesis2)
  and SeqHRP_sf [iff]:  "Sigma_fm (SeqHRP x x' s k)"  (is ?thsf)
  and SeqHRP_imp_OrdP: "{ SeqHRP x y s k } \<turnstile> OrdP k"  (is ?thord)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (s,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
         "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thord
    by (auto intro: LstSeqP_OrdP)
  show ?thesis2 using atoms
    by (fastforce simp: LstSeq_imp_Ord SeqHR_def 
             BuildSeq2_def BuildSeq_def Builds_def
             HBall_def q_HPair_def q_Eats_def
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"]
             cong: conj_cong)
qed

lemma SeqHRP_subst [simp]:
      "(SeqHRP x x' s k)(i::=t) = SeqHRP (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (s,k,t,i,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (s,t,i,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (s,t,i,m,n,sm,sm',sn,sn')"
          "atom m \<sharp> (s,t,i,n,sm,sm',sn,sn')" "atom n \<sharp> (s,t,i,sm,sm',sn,sn')"
          "atom sm \<sharp> (s,t,i,sm',sn,sn')" "atom sm' \<sharp> (s,t,i,sn,sn')"
          "atom sn \<sharp> (s,t,i,sn')" "atom sn' \<sharp> (s,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHRP.simps [of l _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqHRP_cong:
  assumes "H \<turnstile> x EQ x'" and "H \<turnstile> y EQ y'" "H \<turnstile> s EQ s'" and  "H \<turnstile> k EQ k'"
  shows "H \<turnstile> SeqHRP x y s k IFF SeqHRP x' y' s' k'"
  by (rule P4_cong [OF _ assms], auto)

subsection \<open>Defining the syntax: main predicate\<close>

definition HR :: "hf \<Rightarrow> hf \<Rightarrow> bool"
  where "HR x x' \<equiv> \<exists>s k. SeqHR x x' s k"

nominal_function HRP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (x,x',k); atom k \<sharp> (x,x')\<rbrakk> \<Longrightarrow>
         HRP x x' = Ex s (Ex k (SeqHRP x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def HRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows HRP_fresh_iff [simp]: "a \<sharp> HRP x x' \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> x'"  (is ?thesis1)
   and eval_fm_HRP [simp]:   "eval_fm e (HRP x x') \<longleftrightarrow> HR \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e"  (is ?thesis2)
   and HRP_sf [iff]:         "Sigma_fm (HRP x x')"  (is ?thsf)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (x,x',k)"  "atom k \<sharp> (x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: HR_def q_defs)
qed

lemma HRP_subst [simp]: "(HRP x x')(i::=t) = HRP (subst i t x) (subst i t x')"
proof -
  obtain s::name and k::name where "atom s \<sharp> (x,x',t,i,k)"  "atom k \<sharp> (x,x',t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: HRP.simps [of s _ _ k])
qed

subsection\<open>Proving that these relations are functions\<close>

lemma SeqHRP_lemma:
  assumes "atom m \<sharp> (x,x',s,k,n,sm,sm',sn,sn')" "atom n \<sharp> (x,x',s,k,sm,sm',sn,sn')"
          "atom sm \<sharp> (x,x',s,k,sm',sn,sn')" "atom sm' \<sharp> (x,x',s,k,sn,sn')"
          "atom sn \<sharp> (x,x',s,k,sn')" "atom sn' \<sharp> (x,x',s,k)"
    shows "{ SeqHRP x x' s k }
         \<turnstile> (OrdP x AND WRP x x') OR
             Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN k AND Var n IN k AND
                       SeqHRP (Var sm) (Var sm') s (Var m) AND
                       SeqHRP (Var sn) (Var sn') s (Var n) AND
                       x EQ HPair (Var sm) (Var sn) AND
                       x' EQ Q_HPair (Var sm') (Var sn')))))))"
proof -
  obtain l::name and sl::name and sl'::name
    where atoms:
          "atom l \<sharp> (x,x',s,k,sl,sl',m,n,sm,sm',sn,sn')"
          "atom sl \<sharp> (x,x',s,k,sl',m,n,sm,sm',sn,sn')"
          "atom sl' \<sharp> (x,x',s,k,m,n,sm,sm',sn,sn')"
    by (metis obtain_fresh)
  thus ?thesis using atoms assms
    apply (simp add: SeqHRP.simps [of l s k sl sl' m n sm sm' sn sn'])
    apply (rule Conj_E)
    apply (rule All2_SUCC_E' [where t=k, THEN rotate2], simp_all)
    apply (rule rotate2)
    apply (rule Ex_E Conj_E)+
    apply (rule cut_same [where A = "HPair x x' EQ HPair (Var sl) (Var sl')"])
    apply (metis Assume LstSeqP_EQ rotate4, simp_all, clarify)
    apply (rule Disj_E [THEN rotate4])
    apply (rule Disj_I1) 
    apply (metis Assume AssumeH(3) Sym thin1  Iff_MP_same [OF Conj_cong [OF OrdP_cong WRP_cong] Assume])
    \<comment> \<open>auto could be used but is VERY SLOW\<close>
    apply (rule Disj_I2) 
    apply (rule Ex_E Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sm'"], simp)
    apply (rule Ex_I [where x = "Var sn"], simp)
    apply (rule Ex_I [where x = "Var sn'"], simp)
    apply (simp add: SeqHRP.simps [of l _ _ sl sl' m n sm sm' sn sn'])
    apply (rule Conj_I, blast)+
    \<comment> \<open>first SeqHRP subgoal\<close>
    apply (rule Conj_I)+
    apply (blast intro: LstSeqP_Mem)
    apply (rule All2_Subset [OF Hyp], blast)
    apply (blast intro!: SUCC_Subset_Ord LstSeqP_OrdP, blast, simp)
    \<comment> \<open>next SeqHRP subgoal\<close>
    apply (rule Conj_I)+
    apply (blast intro: LstSeqP_Mem)
    apply (rule All2_Subset [OF Hyp], blast)
    apply (auto intro!: SUCC_Subset_Ord LstSeqP_OrdP)
    \<comment> \<open>finally, the equality pair\<close>
    apply (blast intro: Trans)+
    done
qed
 
lemma SeqHRP_unique: "{SeqHRP x y s u, SeqHRP x y' s' u'} \<turnstile> y' EQ y"
proof -
  obtain i::name and j::name and j'::name and k::name and k'::name and l::name
     and m::name and n::name and sm::name and sn::name and sm'::name and sn'::name
     and m2::name and n2::name and sm2::name and sn2::name and sm2'::name and sn2'::name
    where atoms:  "atom i \<sharp> (s,s',y,y')"   "atom j \<sharp> (s,s',i,x,y,y')"  "atom j' \<sharp> (s,s',i,j,x,y,y')"
                  "atom k \<sharp> (s,s',x,y,y',u',i,j,j')" "atom k' \<sharp> (s,s',x,y,y',k,i,j,j')" "atom l \<sharp> (s,s',i,j,j',k,k')"
                  "atom m \<sharp> (s,s',i,j,j',k,k',l)"   "atom n \<sharp> (s,s',i,j,j',k,k',l,m)"
                  "atom sm \<sharp> (s,s',i,j,j',k,k',l,m,n)"  "atom sn \<sharp> (s,s',i,j,j',k,k',l,m,n,sm)"
                  "atom sm' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn)"   "atom sn' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm')"
                  "atom m2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn')"   "atom n2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2)"
                  "atom sm2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2)"  "atom sn2 \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2)"
                  "atom sm2' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2)"   "atom sn2' \<sharp> (s,s',i,j,j',k,k',l,m,n,sm,sn,sm',sn',m2,n2,sm2,sn2,sm2')"
    by (metis obtain_fresh)
  have "{OrdP (Var k)}
       \<turnstile> All i (All j (All j' (All k' (SeqHRP (Var i) (Var j) s (Var k) IMP (SeqHRP (Var i) (Var j') s' (Var k') IMP Var j' EQ Var j)))))"
    apply (rule OrdIndH [where j=l])
    using atoms apply auto
    apply (rule Swap)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqHRP_lemma [of m "Var i" "Var j" s "Var k" n sm sm' sn sn']], simp_all, blast)
    apply (rule cut_same)
    apply (rule cut1 [OF SeqHRP_lemma [of m2 "Var i" "Var j'" s' "Var k'" n2 sm2 sm2' sn2 sn2']], simp_all, blast)
    apply (rule Disj_EH Conj_EH)+
    \<comment> \<open>case 1, both are ordinals\<close>
    apply (blast intro: cut3 [OF WRP_unique])
    \<comment> \<open>case 2, @{term "OrdP (Var i)"} but also a pair\<close>
    apply (rule Conj_EH Ex_EH)+
    apply simp_all
    apply (rule cut_same [where A = "OrdP (HPair (Var sm) (Var sn))"])
    apply (blast intro: OrdP_cong [OF Hyp, THEN Iff_MP_same], blast)
    \<comment> \<open>towards second two cases\<close>
    apply (rule Ex_E Disj_EH Conj_EH)+
    \<comment> \<open>case 3, @{term "OrdP (Var i)"} but also a pair\<close>
    apply (rule cut_same [where A = "OrdP (HPair (Var sm2) (Var sn2))"])
    apply (blast intro: OrdP_cong [OF Hyp, THEN Iff_MP_same], blast)
    \<comment> \<open>case 4, two pairs\<close>
    apply (rule Ex_E Disj_EH Conj_EH)+
    apply (rule All_E' [OF Hyp, where x="Var m"], blast)
    apply (rule All_E' [OF Hyp, where x="Var n"], blast, simp_all)
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (rule All_E [where x="Var sm"], simp)
    apply (rule All_E [where x="Var sm'"], simp)
    apply (rule All_E [where x="Var sm2'"], simp)
    apply (rule All_E [where x="Var m2"], simp)
    apply (rule All_E [where x="Var sn", THEN rotate2], simp)
    apply (rule All_E [where x="Var sn'"], simp)
    apply (rule All_E [where x="Var sn2'"], simp)
    apply (rule All_E [where x="Var n2"], simp)
    apply (rule cut_same [where A = "HPair (Var sm) (Var sn) EQ HPair (Var sm2) (Var sn2)"])
    apply (blast intro: Sym Trans)
    apply (rule cut_same [where A = "SeqHRP (Var sn) (Var sn2') s' (Var n2)"])
    apply (blast intro: SeqHRP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule cut_same [where A = "SeqHRP (Var sm) (Var sm2') s' (Var m2)"])
    apply (blast intro: SeqHRP_cong [OF Hyp Refl Refl, THEN Iff_MP2_same])
    apply (rule Disj_EH, blast intro: thin1 ContraProve)+
    apply (blast intro: Trans [OF Hyp Sym] intro!: HPair_cong)
    done
  hence "{OrdP (Var k)}
         \<turnstile> All j (All j' (All k' (SeqHRP x (Var j) s (Var k)
               IMP (SeqHRP x (Var j') s' (Var k') IMP Var j' EQ Var j))))"
    apply (rule All_D [where x = x, THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)}
         \<turnstile> All j' (All k' (SeqHRP x y s (Var k) IMP (SeqHRP x (Var j') s' (Var k') IMP Var j' EQ y)))"
    apply (rule All_D [where x = y, THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)}
          \<turnstile> All k' (SeqHRP x y s (Var k) IMP (SeqHRP x y' s' (Var k') IMP y' EQ y))"
    apply (rule All_D [where x = y', THEN cut_same])
    using atoms by auto
  hence "{OrdP (Var k)} \<turnstile> SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    apply (rule All_D [where x = u', THEN cut_same])
    using atoms by auto
  hence "{SeqHRP x y s (Var k)} \<turnstile> SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    by (metis SeqHRP_imp_OrdP cut1)
  hence "{} \<turnstile> ((SeqHRP x y s (Var k) IMP (SeqHRP x y' s' u' IMP y' EQ y)))(k::=u)"
    by (metis Subst emptyE Assume MP_same Imp_I)
  hence "{} \<turnstile> SeqHRP x y s u IMP (SeqHRP x y' s' u' IMP y' EQ y)"
    using atoms by simp
  thus ?thesis
    by (metis anti_deduction insert_commute)
qed

theorem HRP_unique: "{HRP x y, HRP x y'} \<turnstile> y' EQ y"
proof -
  obtain s::name and s'::name and k::name and k'::name
    where "atom s \<sharp> (x,y,y')" "atom s' \<sharp> (x,y,y',s)" 
          "atom k \<sharp> (x,y,y',s,s')" "atom k' \<sharp> (x,y,y',s,s',k)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqHRP_unique HRP.simps [of s x y k]  HRP.simps [of s' x y' k'])
qed

subsection \<open>Finally The Function HF Itself\<close>

definition HF :: "hf \<Rightarrow> tm"
  where "HF \<equiv> hmemrec (\<lambda>f z. if Ord z then W z else Q_HPair (f (hfst z)) (f (hsnd z)))"

lemma HF_Ord [simp]: "Ord i \<Longrightarrow> HF i = W i"
  by (rule trans [OF def_hmemrec [OF HF_def]]) auto

lemma HF_pair [simp]: "HF (hpair x y) = Q_HPair (HF x) (HF y)"
  by (rule trans [OF def_hmemrec [OF HF_def]]) (auto simp: ecut_apply HF_def)

lemma SeqHR_hpair: "SeqHR x1 x3 s1 k1 \<Longrightarrow> SeqHR x2 x4 s2 k2 \<Longrightarrow> \<exists>s k. SeqHR \<langle>x1,x2\<rangle> (q_HPair x3 x4) s k"
  by (auto simp: SeqHR_def intro: BuildSeq2_combine)

lemma HR_H:  "coding_hf x \<Longrightarrow> HR x \<lbrakk>HF x\<rbrakk>e"
proof (induct x rule: hmem_rel_induct)
  case (step x) show ?case
  proof (cases "Ord x")
    case True thus ?thesis
      by (auto simp: HR_def SeqHR_def Ord_not_hpair WR_iff_eq_W [where e=e] intro!: BuildSeq2_exI)
  next
    case False 
    then obtain x1 x2 where x: "x = \<langle>x1,x2\<rangle>" 
      by (metis Ord_ord_of coding_hf.simps step.prems)
    then have x12: "(x1, x) \<in> hmem_rel" "(x2, x) \<in> hmem_rel"
      by (auto simp: hmem_rel_iff_hmem_eclose)
    have co12: "coding_hf x1"  "coding_hf x2" using False step x
      by (metis Ord_ord_of coding_hf_hpair)+
    hence "HR x1 \<lbrakk>HF x1\<rbrakk>e"  "HR x2 \<lbrakk>HF x2\<rbrakk>e" 
      by (auto simp: x12 step)
    thus ?thesis using x SeqHR_hpair
      by (auto simp: HR_def q_defs)
  qed
qed

text\<open>Lemma 6.2\<close>
lemma HF_quot_coding_tm: "coding_tm t \<Longrightarrow> HF \<lbrakk>t\<rbrakk>e = \<lceil>t\<rceil>"
  by (induct t rule: coding_tm.induct) (auto, simp add: HPair_def quot_Eats)

lemma HR_quot_fm: fixes A::fm shows "HR \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<lbrakk>\<lceil>\<lceil>A\<rceil>\<rceil>\<rbrakk>e"
  by (metis HR_H HF_quot_coding_tm coding_tm_hf quot_fm_coding)

lemma prove_HRP: fixes A::fm shows "{} \<turnstile> HRP \<lceil>A\<rceil> \<lceil>\<lceil>A\<rceil>\<rceil>"
  by (auto simp: supp_conv_fresh Sigma_fm_imp_thm ground_aux_def ground_fm_aux_def HR_quot_fm)


section\<open>The Function K and Lemma 6.3\<close>

nominal_function KRP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "atom y \<sharp> (v,x,x') \<Longrightarrow>
         KRP v x x' = Ex y (HRP x (Var y) AND SubstFormP v (Var y) x x')"
  by (auto simp: eqvt_def KRP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma KRP_fresh_iff [simp]: "a \<sharp> KRP v x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> x \<and> a \<sharp> x'"
proof -
  obtain y::name where "atom y \<sharp> (v,x,x')"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma KRP_subst [simp]: "(KRP v x x')(i::=t) = KRP (subst i t v) (subst i t x) (subst i t x')"
proof -
  obtain y::name where "atom y \<sharp> (v,x,x',t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: KRP.simps [of y])
qed

declare KRP.simps [simp del]

lemma prove_SubstFormP: "{} \<turnstile> SubstFormP \<lceil>Var i\<rceil> \<lceil>\<lceil>A\<rceil>\<rceil> \<lceil>A\<rceil> \<lceil>A(i::=\<lceil>A\<rceil>)\<rceil>"
  by (auto simp: supp_conv_fresh Sigma_fm_imp_thm ground_aux_def SubstForm_quot)

lemma prove_KRP: "{} \<turnstile> KRP \<lceil>Var i\<rceil> \<lceil>A\<rceil> \<lceil>A(i::=\<lceil>A\<rceil>)\<rceil>"
  by (auto simp: KRP.simps [of y] 
           intro!: Ex_I [where x="\<lceil>\<lceil>A\<rceil>\<rceil>"] prove_HRP prove_SubstFormP)

lemma KRP_unique: "{KRP v x y, KRP v x y'} \<turnstile> y' EQ y"
proof -
  obtain u::name and u'::name where "atom u \<sharp> (v,x,y,y')" "atom u' \<sharp> (v,x,y,y',u)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: KRP.simps [of u v x y] KRP.simps [of u' v x y'] 
             intro: SubstFormP_cong [THEN Iff_MP2_same]
                    SubstFormP_unique [THEN cut2] HRP_unique [THEN cut2])
qed

lemma KRP_subst_fm: "{KRP \<lceil>Var i\<rceil> \<lceil>\<beta>\<rceil> (Var j)} \<turnstile> Var j EQ \<lceil>\<beta>(i::=\<lceil>\<beta>\<rceil>)\<rceil>"
  by (metis KRP_unique cut0 prove_KRP)


section\<open>The Diagonal Lemma and Gödel's Theorem\<close>

lemma diagonal: 
  obtains \<delta> where "{} \<turnstile> \<delta> IFF \<alpha>(i::=\<lceil>\<delta>\<rceil>)"  "supp \<delta> = supp \<alpha> - {atom i}"
proof -
  obtain k::name and j::name
    where atoms: "atom k \<sharp> (i,j,\<alpha>)" "atom j \<sharp> (i,\<alpha>)"
    by (metis obtain_fresh)
  define \<beta> where "\<beta> = Ex j (KRP \<lceil>Var i\<rceil> (Var i) (Var j) AND \<alpha>(i ::= Var j))"
  hence 1: "{} \<turnstile> \<beta>(i ::= \<lceil>\<beta>\<rceil>) IFF (Ex j (KRP \<lceil>Var i\<rceil> (Var i) (Var j) AND \<alpha>(i ::= Var j)))(i ::= \<lceil>\<beta>\<rceil>)"
    by (metis Iff_refl)
  have 2: "{} \<turnstile> (Ex j (KRP \<lceil>Var i\<rceil> (Var i) (Var j) AND \<alpha>(i ::= Var j)))(i ::= \<lceil>\<beta>\<rceil>) IFF
                Ex j (Var j EQ \<lceil>\<beta>(i::=\<lceil>\<beta>\<rceil>)\<rceil> AND \<alpha>(i::=Var j))"
    using atoms
    apply (auto intro!: Ex_cong Conj_cong KRP_subst_fm)
    apply (rule Iff_MP_same [OF Var_Eq_subst_Iff])
    apply (auto intro: prove_KRP thin0)
    done
  have 3: "{} \<turnstile> Ex j (Var j EQ \<lceil>\<beta>(i::=\<lceil>\<beta>\<rceil>)\<rceil> AND \<alpha>(i::=Var j)) IFF \<alpha>(i::=\<lceil>\<beta>(i::=\<lceil>\<beta>\<rceil>)\<rceil>)"
    using atoms
    apply auto
    apply (rule cut_same [OF Iff_MP2_same [OF Var_Eq_subst_Iff AssumeH(2)]])
    apply (auto intro: Ex_I [where x="\<lceil>\<beta>(i::=\<lceil>\<beta>\<rceil>)\<rceil>"])
    done
  have "supp (\<beta>(i ::= \<lceil>\<beta>\<rceil>)) = supp \<alpha> - {atom i}" using atoms
    by (auto simp: fresh_at_base ground_fm_aux_def \<beta>_def supp_conv_fresh)
  thus ?thesis using atoms
    by (metis that 1 2 3 Iff_trans)
qed

text\<open>Gödel's first incompleteness theorem: If consistent, our theory is incomplete.\<close>
theorem Goedel_I:
  assumes "\<not> {} \<turnstile> Fls"
  obtains \<delta> where "{} \<turnstile> \<delta> IFF Neg (PfP \<lceil>\<delta>\<rceil>)"  "\<not> {} \<turnstile> \<delta>"  "\<not> {} \<turnstile> Neg \<delta>"  
                  "eval_fm e \<delta>"  "ground_fm \<delta>"
proof -
  fix i::name
  obtain \<delta> where        "{} \<turnstile> \<delta> IFF Neg ((PfP (Var i))(i::=\<lceil>\<delta>\<rceil>))"
             and suppd: "supp \<delta> = supp (Neg (PfP (Var i))) - {atom i}"
    by (metis SyntaxN.Neg diagonal)
  then have diag: "{} \<turnstile> \<delta> IFF Neg (PfP \<lceil>\<delta>\<rceil>)"
    by simp
  then have np: "\<not> {} \<turnstile> \<delta> \<and> \<not> {} \<turnstile> Neg \<delta>"
    by (metis Iff_MP_same NegNeg_D Neg_D Neg_cong assms proved_iff_proved_PfP)
  then have "eval_fm e \<delta>" using hfthm_sound [where e=e, OF diag]
    by simp (metis Pf_quot_imp_is_proved)
  moreover have "ground_fm \<delta>" using suppd  
    by (simp add: supp_conv_fresh ground_fm_aux_def subset_eq) (metis fresh_ineq_at_base)
  ultimately show ?thesis
    by (metis diag np that)
qed

end

