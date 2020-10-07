chapter \<open>Predicates for Terms, Formulas and Substitution\<close>

theory Coding_Predicates
imports Coding Sigma
begin

declare succ_iff [simp del]

text \<open>This material comes from Section 3, greatly modified for de Bruijn syntax.\<close>

section \<open>Predicates for atomic terms\<close>

subsection \<open>Free Variables\<close>

definition is_Var :: "hf \<Rightarrow> bool" where "is_Var x \<equiv> Ord x \<and> 0 \<^bold>\<in> x"

definition VarP :: "tm \<Rightarrow> fm" where "VarP x \<equiv> OrdP x AND Zero IN x"

lemma VarP_eqvt [eqvt]: "(p \<bullet> VarP x) = VarP (p \<bullet> x)"
  by (simp add: VarP_def)

lemma VarP_fresh_iff [simp]: "a \<sharp> VarP x \<longleftrightarrow> a \<sharp> x"
  by (simp add: VarP_def)

lemma eval_fm_VarP [simp]:  "eval_fm e (VarP x) \<longleftrightarrow> is_Var \<lbrakk>x\<rbrakk>e"
  by (simp add: VarP_def is_Var_def)

lemma VarP_sf [iff]: "Sigma_fm (VarP x)"
  by (auto simp: VarP_def)

lemma VarP_subst [simp]: "(VarP x)(i::=t) = VarP (subst i t x) "
  by (simp add: VarP_def)

lemma VarP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> VarP x IFF VarP x'"
  by (rule P1_cong) auto

lemma VarP_HPairE [intro!]: "insert (VarP (HPair x y)) H \<turnstile> A"
  by (auto simp: VarP_def)

lemma is_Var_succ_iff [simp]: "is_Var (succ x) = Ord x"
  by (metis Ord_succ_iff is_Var_def succ_iff zero_in_Ord)

lemma is_Var_q_Var [iff]: "is_Var (q_Var i)"
  by (simp add: q_Var_def)

definition decode_Var :: "hf \<Rightarrow> name"
  where "decode_Var x \<equiv> name_of_nat (nat_of_ord (pred x))"

lemma decode_Var_q_Var [simp]: "decode_Var (q_Var i) = i"
  by (simp add: decode_Var_def q_Var_def)

lemma is_Var_imp_decode_Var: "is_Var x \<Longrightarrow> x = \<lbrakk>\<lceil>Var (decode_Var x)\<rceil>\<rbrakk> e"
  by (simp add: is_Var_def quot_Var decode_Var_def) (metis hempty_iff succ_pred)

lemma is_Var_iff: "is_Var v \<longleftrightarrow> v = succ (ord_of (nat_of_name (decode_Var v)))"
  by (metis eval_tm_ORD_OF eval_tm_SUCC is_Var_imp_decode_Var quot_Var is_Var_succ_iff Ord_ord_of)

lemma decode_Var_inject [simp]: "is_Var v \<Longrightarrow> is_Var v' \<Longrightarrow> decode_Var v = decode_Var v' \<longleftrightarrow> v=v'"
  by (metis is_Var_iff)

subsection \<open>De Bruijn Indexes\<close>

definition is_Ind :: "hf \<Rightarrow> bool"
  where "is_Ind x \<equiv> (\<exists>m. Ord m \<and> x = \<langle>htuple 6, m\<rangle>)"

abbreviation Q_Ind :: "tm \<Rightarrow> tm"
  where "Q_Ind k \<equiv> HPair (HTuple 6) k"

nominal_function IndP :: "tm \<Rightarrow> fm"
  where "atom m \<sharp> x \<Longrightarrow>
    IndP x = Ex m (OrdP (Var m) AND x EQ HPair (HTuple 6) (Var m))"
  by (auto simp: eqvt_def IndP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows IndP_fresh_iff [simp]: "a \<sharp> IndP x \<longleftrightarrow> a \<sharp> x"                (is ?thesis1)
    and eval_fm_IndP [simp]:   "eval_fm e (IndP x) \<longleftrightarrow> is_Ind \<lbrakk>x\<rbrakk>e"  (is ?thesis2)
    and IndP_sf [iff]:         "Sigma_fm (IndP x)"                   (is ?thsf)
    and OrdP_IndP_Q_Ind:       "{OrdP x} \<turnstile> IndP (Q_Ind x)"           (is ?thqind)
proof -
  obtain m::name where "atom m \<sharp> x"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf ?thqind
    by (auto simp: is_Ind_def intro: Ex_I [where x=x])
qed

lemma IndP_Q_Ind: "H \<turnstile> OrdP x \<Longrightarrow> H \<turnstile> IndP (Q_Ind x)"
  by (rule cut1 [OF OrdP_IndP_Q_Ind])

lemma subst_fm_IndP [simp]: "(IndP t)(i::=x) = IndP (subst i x t)"
proof -
  obtain m::name where "atom m \<sharp> (i,t,x)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: IndP.simps [of m])
qed

lemma IndP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> IndP x IFF IndP x'"
  by (rule P1_cong) auto

definition decode_Ind :: "hf \<Rightarrow> nat"
  where "decode_Ind x \<equiv> nat_of_ord (hsnd x)"

lemma is_Ind_pair_iff [simp]: "is_Ind \<langle>x, y\<rangle> \<longleftrightarrow> x = htuple 6 \<and> Ord y"
  by (auto simp: is_Ind_def)

subsection \<open>Various syntactic lemmas\<close>

lemma eval_Var_q: "\<lbrakk>\<lceil>Var i\<rceil>\<rbrakk> e = q_Var i"
  by (simp add: quot_tm_def q_Var_def)

lemma is_Var_eval_Var [simp]: "is_Var \<lbrakk>\<lceil>Var i\<rceil>\<rbrakk>e"
  by (metis decode_Var_q_Var is_Var_imp_decode_Var is_Var_q_Var)


section \<open>The predicate \<open>SeqCTermP\<close>, for Terms and Constants\<close>

(*SeqCTerm(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>l\<in>k)[s l=0 \<or> Var(s l)\<or>(\<exists>m,n\<in>l)[s l = \<langle>Eats, s m, s n\<rangle>]]*)
definition SeqCTerm :: "bool \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqCTerm vf s k t \<equiv> BuildSeq (\<lambda>u. u=0 \<or> vf \<and> is_Var u) (\<lambda>u v w. u = q_Eats v w) s k t"

nominal_function SeqCTermP :: "bool \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,sl,m,n,sm,sn);  atom sl \<sharp> (s,m,n,sm,sn);
          atom m \<sharp> (s,n,sm,sn);  atom n \<sharp> (s,sm,sn);
          atom sm \<sharp> (s,sn);  atom sn \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqCTermP vf s k t =
      LstSeqP s k t AND
      All2 l (SUCC k) (Ex sl (HPair (Var l) (Var sl) IN s AND 
               (Var sl EQ Zero OR (if vf then VarP (Var sl) else Fls) OR
                Ex m (Ex n (Ex sm (Ex sn (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var n) (Var sn) IN s AND
                       Var sl EQ Q_Eats (Var sm) (Var sn))))))))"
  by (auto simp: eqvt_def SeqCTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqCTermP_fresh_iff [simp]:
       "a \<sharp> SeqCTermP vf s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t"  (is ?thesis1)
    and eval_fm_SeqCTermP [simp]:
       "eval_fm e (SeqCTermP vf s k t) \<longleftrightarrow> SeqCTerm vf \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e \<lbrakk>t\<rbrakk>e"    (is ?thesis2)
    and SeqCTermP_sf [iff]:
       "Sigma_fm (SeqCTermP vf s k t)"   (is ?thsf)
    and SeqCTermP_imp_LstSeqP:
      "{ SeqCTermP vf s k t } \<turnstile> LstSeqP s k t"  (is ?thlstseq)
    and SeqCTermP_imp_OrdP [simp]:
      "{ SeqCTermP vf s k t } \<turnstile> OrdP k"  (is ?thord)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,m,n,sm,sn)"
        "atom m \<sharp> (s,n,sm,sn)"   "atom n \<sharp> (s,sm,sn)"
        "atom sm \<sharp> (s,sn)"   "atom sn \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thlstseq ?thord
    by (auto simp: LstSeqP.simps)
  show ?thesis2 using atoms
    by (simp cong: conj_cong add: LstSeq_imp_Ord SeqCTerm_def BuildSeq_def Builds_def
             HBall_def HBex_def q_Eats_def Fls_def
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"])
qed

lemma SeqCTermP_subst [simp]:
      "(SeqCTermP vf s k t)(j::=w) = SeqCTermP vf (subst j w s) (subst j w k) (subst j w t)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (j,w,s,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (j,w,s,m,n,sm,sn)"
          "atom m \<sharp> (j,w,s,n,sm,sn)"   "atom n \<sharp> (j,w,s,sm,sn)"
          "atom sm \<sharp> (j,w,s,sn)"   "atom sn \<sharp> (j,w,s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqCTermP.simps [of l _ _ sl m n sm sn])
qed

declare SeqCTermP.simps [simp del]

abbreviation SeqTerm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqTerm \<equiv> SeqCTerm True"

abbreviation SeqTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "SeqTermP \<equiv> SeqCTermP True"

abbreviation SeqConst :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqConst \<equiv> SeqCTerm False"

abbreviation SeqConstP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "SeqConstP \<equiv> SeqCTermP False"

lemma SeqConst_imp_SeqTerm: "SeqConst s k x \<Longrightarrow> SeqTerm s k x"
 by (auto simp: SeqCTerm_def intro: BuildSeq_mono)

lemma SeqConstP_imp_SeqTermP: "{SeqConstP s k t} \<turnstile> SeqTermP s k t"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (s,k,t,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,k,t,m,n,sm,sn)"
          "atom m \<sharp> (s,k,t,n,sm,sn)"   "atom n \<sharp> (s,k,t,sm,sn)"
          "atom sm \<sharp> (s,k,t,sn)"   "atom sn \<sharp> (s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis
    apply (auto simp: SeqCTermP.simps [of l s k sl m n sm sn])
    apply (rule Ex_I [where x="Var l"], auto)
    apply (rule Ex_I [where x = "Var sl"], force intro: Disj_I1)
    apply (rule Ex_I [where x = "Var sl"], simp)
    apply (rule Conj_I, blast)
    apply (rule Disj_I2)+
    apply (rule Ex_I [where x = "Var m"], simp)
    apply (rule Ex_I [where x = "Var n"], simp)
    apply (rule Ex_I [where x = "Var sm"], simp)
    apply (rule Ex_I [where x = "Var sn"], auto)
    done
qed


section \<open>The predicates \<open>TermP\<close> and \<open>ConstP\<close>\<close>

subsection \<open>Definition\<close>

definition CTerm :: "bool \<Rightarrow> hf \<Rightarrow> bool"
  where "CTerm vf t \<equiv> (\<exists>s k. SeqCTerm vf s k t)"

nominal_function CTermP :: "bool \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,t); atom s \<sharp> t\<rbrakk> \<Longrightarrow>
    CTermP vf t = Ex s (Ex k (SeqCTermP vf (Var s) (Var k) t))"
  by (auto simp: eqvt_def CTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows CTermP_fresh_iff [simp]: "a \<sharp> CTermP vf t \<longleftrightarrow> a \<sharp> t"            (is ?thesis1)
    and eval_fm_CTermP [simp] :"eval_fm e (CTermP vf t) \<longleftrightarrow> CTerm vf \<lbrakk>t\<rbrakk>e"  (is ?thesis2)
    and CTermP_sf [iff]: "Sigma_fm (CTermP vf t)"                      (is ?thsf)
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,t)" "atom s \<sharp> t"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: CTerm_def)
qed

lemma CTermP_subst [simp]: "(CTermP vf i)(j::=w) = CTermP vf (subst j w i)"
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,i,j,w)" "atom s \<sharp> (i,j,w)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: CTermP.simps [of k s])
qed

abbreviation Term :: "hf \<Rightarrow> bool"
  where "Term \<equiv> CTerm True"

abbreviation TermP :: "tm \<Rightarrow> fm"
  where "TermP \<equiv> CTermP True"

abbreviation Const :: "hf \<Rightarrow> bool"
  where "Const \<equiv> CTerm False"

abbreviation ConstP :: "tm \<Rightarrow> fm"
  where "ConstP \<equiv> CTermP False"

subsection \<open>Correctness: It Corresponds to Quotations of Real Terms\<close>

lemma wf_Term_quot_dbtm [simp]: "wf_dbtm u \<Longrightarrow> Term \<lbrakk>quot_dbtm u\<rbrakk>e"
by (induct rule: wf_dbtm.induct)
   (auto simp: CTerm_def SeqCTerm_def q_Eats_def intro: BuildSeq_combine BuildSeq_exI)

corollary Term_quot_tm [iff]: fixes t :: tm  shows "Term \<lbrakk>\<lceil>t\<rceil>\<rbrakk>e"
  by (metis quot_tm_def wf_Term_quot_dbtm wf_dbtm_trans_tm)

lemma SeqCTerm_imp_wf_dbtm:
  assumes "SeqCTerm vf s k x"
  shows "\<exists>t::dbtm. wf_dbtm t \<and> x = \<lbrakk>quot_dbtm t\<rbrakk>e"
using assms [unfolded SeqCTerm_def]
proof (induct x rule: BuildSeq_induct)
  case (B x) thus ?case
    by auto (metis ORD_OF.simps(2) Var quot_dbtm.simps(2) is_Var_imp_decode_Var quot_Var)
next
  case (C x y z)
  then obtain tm1::dbtm and tm2::dbtm
    where "wf_dbtm tm1" "y = \<lbrakk>quot_dbtm tm1\<rbrakk>e"
          "wf_dbtm tm2" "z = \<lbrakk>quot_dbtm tm2\<rbrakk>e"
    by blast
  thus ?case
    by (auto simp: wf_dbtm.intros C q_Eats_def intro!: exI [of _ "DBEats tm1 tm2"])
qed

corollary Term_imp_wf_dbtm:
  assumes "Term x" obtains t where "wf_dbtm t" "x = \<lbrakk>quot_dbtm t\<rbrakk>e"
  by (metis assms SeqCTerm_imp_wf_dbtm CTerm_def)

corollary Term_imp_is_tm: assumes "Term x" obtains t::tm where "x = \<lbrakk>\<lceil>t\<rceil>\<rbrakk> e"
  by (metis assms Term_imp_wf_dbtm quot_tm_def wf_dbtm_imp_is_tm)

lemma Term_Var: "Term (q_Var i)"
  using wf_Term_quot_dbtm [of "DBVar i"]
  by (metis Term_quot_tm is_Var_imp_decode_Var is_Var_q_Var)

lemma Term_Eats: assumes x: "Term x" and y: "Term y" shows "Term (q_Eats x y)"
proof -
  obtain t u  where "x = \<lbrakk>quot_dbtm t\<rbrakk>e" "y = \<lbrakk>quot_dbtm u\<rbrakk>e"
    by (metis Term_imp_wf_dbtm x y)
  thus ?thesis using wf_Term_quot_dbtm [of "DBEats t u"] x y
    by (auto simp: q_defs) (metis Eats Term_imp_wf_dbtm quot_dbtm_inject_lemma)
qed

subsection \<open>Correctness properties for constants\<close>

lemma Const_imp_Term: "Const x \<Longrightarrow> Term x"
  by (metis SeqConst_imp_SeqTerm CTerm_def)

lemma Const_0: "Const 0"
  by (force simp add: CTerm_def SeqCTerm_def intro: BuildSeq_exI)

lemma ConstP_imp_TermP: "{ConstP t} \<turnstile> TermP t"
proof -
  obtain k::name and s::name  where "atom k \<sharp> (s,t)" "atom s \<sharp> t"
    by (metis obtain_fresh)
  thus ?thesis
    apply auto
    apply (rule Ex_I [where x = "Var s"], simp)
    apply (rule Ex_I [where x = "Var k"], auto intro: SeqConstP_imp_SeqTermP [THEN cut1])
    done
qed


section \<open>Abstraction over terms\<close>

definition SeqStTerm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "SeqStTerm v u x x' s k \<equiv>
       is_Var v \<and> BuildSeq2 (\<lambda>y y'. (is_Ind y \<or> Ord y) \<and> y' = (if y=v then u else y))
                (\<lambda>u u' v v' w w'. u = q_Eats v w \<and> u' = q_Eats v' w') s k x x'"

definition AbstTerm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "AbstTerm v i x x' \<equiv> Ord i \<and> (\<exists>s k. SeqStTerm v (q_Ind i) x x' s k)"

subsection \<open>Defining the syntax: quantified body\<close>

nominal_function SeqStTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,i,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,v,i,sl',m,n,sm,sm',sn,sn'); atom sl' \<sharp> (s,v,i,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn'); atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn'); atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn'); atom sn' \<sharp> s\<rbrakk> \<Longrightarrow>
    SeqStTermP v i t u s k =
      VarP v AND LstSeqP s k (HPair t u) AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                (((Var sl EQ v AND Var sl' EQ i) OR
                  ((IndP (Var sl) OR Var sl NEQ v) AND Var sl' EQ Var sl)) OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       Var sl EQ Q_Eats (Var sm) (Var sn) AND
                       Var sl' EQ Q_Eats (Var sm') (Var sn')))))))))))"
  apply (simp_all add: eqvt_def SeqStTermP_graph_aux_def flip_fresh_fresh)
  by auto (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqStTermP_fresh_iff [simp]:
      "a \<sharp> SeqStTermP v i t u s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and eval_fm_SeqStTermP [simp]:
      "eval_fm e (SeqStTermP v i t u s k) \<longleftrightarrow> SeqStTerm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>t\<rbrakk>e \<lbrakk>u\<rbrakk>e \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e"  (is ?thesis2)
    and SeqStTermP_sf [iff]:
      "Sigma_fm (SeqStTermP v i t u s k)"  (is ?thsf)
    and SeqStTermP_imp_OrdP:
      "{ SeqStTermP v i t u s k } \<turnstile> OrdP k"  (is ?thord)
    and SeqStTermP_imp_VarP:
      "{ SeqStTermP v i t u s k } \<turnstile> VarP v"  (is ?thvar)
    and SeqStTermP_imp_LstSeqP:
      "{ SeqStTermP v i t u s k } \<turnstile> LstSeqP s k (HPair t u)"  (is ?thlstseq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
       "atom l \<sharp> (s,k,v,i,sl,sl',m,n,sm,sm',sn,sn')"
       "atom sl \<sharp> (s,v,i,sl',m,n,sm,sm',sn,sn')" "atom sl' \<sharp> (s,v,i,m,n,sm,sm',sn,sn')"
       "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
       "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
       "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thord ?thvar ?thlstseq
    by (auto intro: LstSeqP_OrdP)
  show ?thesis2 using atoms
    apply (simp add: LstSeq_imp_Ord SeqStTerm_def ex_disj_distrib
             BuildSeq2_def BuildSeq_def Builds_def
             HBall_def q_Eats_def q_Ind_def is_Var_def
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"]
             cong: conj_cong)
    apply (rule conj_cong refl all_cong)+
    apply auto
    apply (metis Not_Ord_hpair is_Ind_def)
    done
qed

lemma SeqStTermP_subst [simp]:
      "(SeqStTermP v i t u s k)(j::=w) =
       SeqStTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u) (subst j w s) (subst j w k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where "atom l \<sharp> (s,k,v,i,w,j,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,i,w,j,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,i,w,j,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,w,j,n,sm,sm',sn,sn')" "atom n \<sharp> (s,w,j,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,w,j,sm',sn,sn')" "atom sm' \<sharp> (s,w,j,sn,sn')"
         "atom sn \<sharp> (s,w,j,sn')" "atom sn' \<sharp> (s,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqStTermP.simps [of l _ _ _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqStTermP_cong:
  "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'; H \<turnstile> s EQ s'; H \<turnstile> k EQ k'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SeqStTermP v i t u s k IFF SeqStTermP v i t' u' s' k'"
   by (rule P4_cong [where tms="[v,i]"]) (auto simp: fresh_Cons)

declare SeqStTermP.simps [simp del]

subsection \<open>Defining the syntax: main predicate\<close>

nominal_function AbstTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,t,u,k); atom k \<sharp> (v,i,t,u)\<rbrakk> \<Longrightarrow>
    AbstTermP v i t u =
     OrdP i AND Ex s (Ex k (SeqStTermP v (Q_Ind i) t u (Var s) (Var k)))"
  by (auto simp: eqvt_def AbstTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstTermP_fresh_iff [simp]:
      "a \<sharp> AbstTermP v i t u \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u"  (is ?thesis1)
    and eval_fm_AbstTermP [simp]:
      "eval_fm e (AbstTermP v i t u) \<longleftrightarrow> AbstTerm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>t\<rbrakk>e \<lbrakk>u\<rbrakk>e "  (is ?thesis2)
    and AbstTermP_sf [iff]:
      "Sigma_fm (AbstTermP v i t u)"  (is ?thsf)
proof -
  obtain s::name and k::name where "atom s \<sharp> (v,i,t,u,k)"  "atom k \<sharp> (v,i,t,u)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: AbstTerm_def q_defs)
qed

lemma AbstTermP_subst [simp]:
      "(AbstTermP v i t u)(j::=w) = AbstTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u)"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,t,u,w,j,k)"  "atom k \<sharp> (v,i,t,u,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: AbstTermP.simps [of s _ _ _ _ k])
qed

declare AbstTermP.simps [simp del]

subsection \<open>Correctness: It Coincides with Abstraction over real terms\<close>

lemma not_is_Var_is_Ind: "is_Var v \<Longrightarrow> \<not> is_Ind v"
  by (auto simp: is_Var_def is_Ind_def)

lemma AbstTerm_imp_abst_dbtm:
  assumes "AbstTerm v i x x'"
  shows "\<exists>t. x = \<lbrakk>quot_dbtm t\<rbrakk>e \<and>
             x' = \<lbrakk>quot_dbtm (abst_dbtm (decode_Var v) (nat_of_ord i) t)\<rbrakk>e"
proof -
  obtain s k where v: "is_Var v" and i: "Ord i" and sk: "SeqStTerm v (q_Ind i) x x' s k"
    using assms
    by (auto simp: AbstTerm_def SeqStTerm_def)
  from sk [unfolded SeqStTerm_def, THEN conjunct2]
  show ?thesis
  proof (induct x x' rule: BuildSeq2_induct)
    case (B x x') thus ?case using v i
      apply (auto simp: not_is_Var_is_Ind)
      apply (rule_tac [1] x="DBInd (nat_of_ord (hsnd x))" in exI)
      apply (rule_tac [2] x="DBVar (decode_Var v)" in exI)
      apply (case_tac [3] "is_Var x")
      apply (rule_tac [3] x="DBVar (decode_Var x)" in exI)
      apply (rule_tac [4] x=DBZero in exI)
      apply (auto simp: is_Ind_def q_Ind_def is_Var_iff [symmetric])
      apply (metis hmem_0_Ord is_Var_def)
      done
  next
    case (C x x' y y' z z')
    then obtain tm1 and tm2
      where "y = \<lbrakk>quot_dbtm tm1\<rbrakk>e"
              "y' = \<lbrakk>quot_dbtm (abst_dbtm (decode_Var v) (nat_of_ord i) tm1)\<rbrakk>e"
            "z = \<lbrakk>quot_dbtm tm2\<rbrakk>e"
              "z' = \<lbrakk>quot_dbtm (abst_dbtm (decode_Var v) (nat_of_ord i) tm2)\<rbrakk>e"
    by blast
  thus ?case
    by (auto simp: wf_dbtm.intros C q_Eats_def intro!: exI [where x="DBEats tm1 tm2"])
  qed
qed

lemma AbstTerm_abst_dbtm:
     "AbstTerm (q_Var i) (ord_of n) \<lbrakk>quot_dbtm t\<rbrakk>e
                                    \<lbrakk>quot_dbtm (abst_dbtm i n t)\<rbrakk>e"
  by (induct t rule: dbtm.induct)
     (auto simp: AbstTerm_def SeqStTerm_def q_defs intro: BuildSeq2_exI BuildSeq2_combine)


section \<open>Substitution over terms\<close>

definition SubstTerm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SubstTerm v u x x' \<equiv> Term u \<and> (\<exists>s k. SeqStTerm v u x x' s k)"

subsection \<open>Defining the syntax\<close>

nominal_function SubstTermP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,t,u,k); atom k \<sharp> (v,i,t,u)\<rbrakk> \<Longrightarrow>
    SubstTermP v i t u = TermP i AND Ex s (Ex k (SeqStTermP v i t u (Var s) (Var k)))"
  by (auto simp: eqvt_def SubstTermP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstTermP_fresh_iff [simp]:
       "a \<sharp> SubstTermP v i t u \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> t \<and> a \<sharp> u"  (is ?thesis1)
    and eval_fm_SubstTermP [simp]:
       "eval_fm e (SubstTermP v i t u) \<longleftrightarrow> SubstTerm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>t\<rbrakk>e \<lbrakk>u\<rbrakk>e"  (is ?thesis2)
    and SubstTermP_sf [iff]:
       "Sigma_fm (SubstTermP v i t u)"     (is ?thsf)
    and SubstTermP_imp_TermP:
       "{ SubstTermP v i t u } \<turnstile> TermP i"  (is ?thterm)
    and SubstTermP_imp_VarP:
       "{ SubstTermP v i t u } \<turnstile> VarP v"   (is ?thvar)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,t,u,k)" "atom k \<sharp> (v,i,t,u)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf ?thterm ?thvar
    by (auto simp: SubstTerm_def intro: SeqStTermP_imp_VarP thin2)
qed

lemma SubstTermP_subst [simp]:
      "(SubstTermP v i t u)(j::=w) = SubstTermP (subst j w v) (subst j w i) (subst j w t) (subst j w u)"
proof -
  obtain s::name and k::name
    where "atom s \<sharp> (v,i,t,u,w,j,k)"  "atom k \<sharp> (v,i,t,u,w,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstTermP.simps [of s _ _ _ _ k])
qed

lemma SubstTermP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> i EQ i'; H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstTermP v i t u IFF SubstTermP v' i' t' u'"
  by (rule P4_cong) auto

declare SubstTermP.simps [simp del]

lemma SubstTerm_imp_subst_dbtm:
  assumes "SubstTerm v \<lbrakk>quot_dbtm u\<rbrakk>e x x'"
  shows "\<exists>t. x = \<lbrakk>quot_dbtm t\<rbrakk>e \<and>
             x' = \<lbrakk>quot_dbtm (subst_dbtm u (decode_Var v) t)\<rbrakk>e"
proof -
  obtain s k where v: "is_Var v" and u: "Term \<lbrakk>quot_dbtm u\<rbrakk>e"
               and sk: "SeqStTerm v \<lbrakk>quot_dbtm u\<rbrakk>e x x' s k"
    using assms [unfolded SubstTerm_def]
    by (auto simp: SeqStTerm_def)
  from sk [unfolded SeqStTerm_def, THEN conjunct2]
  show ?thesis
  proof (induct x x' rule: BuildSeq2_induct)
    case (B x x') thus ?case using v
      apply (auto simp: not_is_Var_is_Ind)
      apply (rule_tac [1] x="DBInd (nat_of_ord (hsnd x))" in exI)
      apply (rule_tac [2] x="DBVar (decode_Var v)" in exI)
      apply (case_tac [3] "is_Var x")
      apply (rule_tac [3] x="DBVar (decode_Var x)" in exI)
      apply (rule_tac [4] x=DBZero in exI)
      apply (auto simp: is_Ind_def q_Ind_def is_Var_iff [symmetric])
      apply (metis hmem_0_Ord is_Var_def)
      done
  next
    case (C x x' y y' z z')
    then obtain tm1 and tm2
      where "y = \<lbrakk>quot_dbtm tm1\<rbrakk>e"
              "y' = \<lbrakk>quot_dbtm (subst_dbtm u (decode_Var v) tm1)\<rbrakk>e"
            "z = \<lbrakk>quot_dbtm tm2\<rbrakk>e"
              "z' = \<lbrakk>quot_dbtm (subst_dbtm u (decode_Var v) tm2)\<rbrakk>e"
    by blast
  thus ?case
    by (auto simp: wf_dbtm.intros C q_Eats_def intro!: exI [where x="DBEats tm1 tm2"])
  qed
qed

corollary SubstTerm_imp_subst_dbtm':
  assumes "SubstTerm v y x x'"
  obtains t::dbtm and u::dbtm
  where "y = \<lbrakk>quot_dbtm u\<rbrakk>e"
        "x = \<lbrakk>quot_dbtm t\<rbrakk>e"
        "x' = \<lbrakk>quot_dbtm (subst_dbtm u (decode_Var v) t)\<rbrakk>e"
  by (metis SubstTerm_def SubstTerm_imp_subst_dbtm Term_imp_is_tm assms quot_tm_def)

lemma SubstTerm_subst_dbtm:
  assumes "Term \<lbrakk>quot_dbtm u\<rbrakk>e"
    shows "SubstTerm (q_Var v) \<lbrakk>quot_dbtm u\<rbrakk>e \<lbrakk>quot_dbtm t\<rbrakk>e \<lbrakk>quot_dbtm (subst_dbtm u v t)\<rbrakk>e"
  by (induct t rule: dbtm.induct) 
     (auto simp: assms SubstTerm_def SeqStTerm_def q_defs intro: BuildSeq2_exI BuildSeq2_combine)


section \<open>Abstraction over formulas\<close>

subsection \<open>The predicate \<open>AbstAtomicP\<close>\<close>

definition AbstAtomic :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "AbstAtomic v i y y' \<equiv> 
            (\<exists>t u t' u'. AbstTerm v i t t' \<and> AbstTerm v i u u' \<and>
             ((y = q_Eq t u \<and> y' = q_Eq t' u') \<or> (y = q_Mem t u \<and> y' = q_Mem t' u')))"

nominal_function AbstAtomicP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (v,i,y,y',t',u,u'); atom t' \<sharp> (v,i,y,y',u,u');
          atom u \<sharp> (v,i,y,y',u'); atom u' \<sharp> (v,i,y,y')\<rbrakk> \<Longrightarrow>
    AbstAtomicP v i y y' =
         Ex t (Ex u (Ex t' (Ex u'
           (AbstTermP v i (Var t) (Var t') AND AbstTermP v i (Var u) (Var u') AND
                      ((y EQ Q_Eq (Var t) (Var u) AND y' EQ Q_Eq (Var t') (Var u')) OR
                       (y EQ Q_Mem (Var t) (Var u) AND y' EQ Q_Mem (Var t') (Var u')))))))"
  by (auto simp: eqvt_def AbstAtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstAtomicP_fresh_iff [simp]:
       "a \<sharp> AbstAtomicP v i y y' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> y \<and> a \<sharp> y'"         (is ?thesis1)
    and eval_fm_AbstAtomicP [simp]:
       "eval_fm e (AbstAtomicP v i y y') \<longleftrightarrow> AbstAtomic \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>y\<rbrakk>e \<lbrakk>y'\<rbrakk>e"  (is ?thesis2)
    and AbstAtomicP_sf [iff]: "Sigma_fm (AbstAtomicP v i y y')"              (is ?thsf)
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,i,y,y',t',u,u')" "atom t' \<sharp> (v,i,y,y',u,u')"
          "atom u \<sharp> (v,i,y,y',u')" "atom u' \<sharp> (v,i,y,y')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: AbstAtomic_def q_defs)
qed

lemma AbstAtomicP_subst [simp]:
      "(AbstAtomicP v tm y y')(i::=w) = AbstAtomicP (subst i w v) (subst i w tm) (subst i w y) (subst i w y')"
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',w,i,t',u,u')"  "atom t' \<sharp> (v,tm,y,y',w,i,u,u')"
          "atom u \<sharp> (v,tm,y,y',w,i,u')"       "atom u' \<sharp> (v,tm,y,y',w,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: AbstAtomicP.simps [of t _ _ _ _ t' u u'])
qed

declare AbstAtomicP.simps [simp del]

subsection \<open>The predicate \<open>AbsMakeForm\<close>\<close>

definition AbstMakeForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "AbstMakeForm k y y' i u u' j w w' \<equiv>
      Ord k \<and>
      ((k = i \<and> k = j \<and> y = q_Disj u w \<and> y' = q_Disj u' w') \<or>
       (k = i \<and> y = q_Neg u \<and> y' = q_Neg u') \<or>
       (succ k = i \<and> y = q_Ex u \<and> y' = q_Ex u'))"

definition SeqAbstForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "SeqAbstForm v i x x' s k \<equiv>
       BuildSeq3 (AbstAtomic v) AbstMakeForm s k i x x'"

nominal_function SeqAbstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sli \<sharp> (s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sl \<sharp> (s,v,sl',m,n,smi,sm,sm',sni,sn,sn');
          atom sl' \<sharp> (s,v,m,n,smi,sm,sm',sni,sn,sn');
          atom m \<sharp> (s,n,smi,sm,sm',sni,sn,sn');
          atom n \<sharp> (s,smi,sm,sm',sni,sn,sn'); atom smi \<sharp> (s,sm,sm',sni,sn,sn');
          atom sm \<sharp> (s,sm',sni,sn,sn'); atom sm' \<sharp> (s,sni,sn,sn');
          atom sni \<sharp> (s,sn,sn'); atom sn \<sharp> (s,sn'); atom sn' \<sharp> (s)\<rbrakk> \<Longrightarrow>
    SeqAbstFormP v i x x' s k =
      LstSeqP s k (HPair i (HPair x x')) AND
      All2 l (SUCC k) (Ex sli (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sli) (HPair (Var sl) (Var sl'))) IN s AND
                (AbstAtomicP v (Var sli) (Var sl) (Var sl') OR
                OrdP (Var sli) AND
                Ex m (Ex n (Ex smi (Ex sm (Ex sm' (Ex sni (Ex sn (Ex sn'
                      (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var smi) (HPair (Var sm) (Var sm'))) IN s AND
                       HPair (Var n) (HPair (Var sni) (HPair (Var sn) (Var sn'))) IN s AND
                       ((Var sli EQ Var smi AND Var sli EQ Var sni AND
                         Var sl EQ Q_Disj (Var sm) (Var sn) AND
                         Var sl' EQ Q_Disj (Var sm') (Var sn')) OR
                        (Var sli EQ Var smi AND
                         Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm')) OR
                        (SUCC (Var sli) EQ Var smi AND
                         Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm'))))))))))))))))"
  by (auto simp: eqvt_def SeqAbstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)


nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqAbstFormP_fresh_iff [simp]:
       "a \<sharp> SeqAbstFormP v i x x' s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and eval_fm_SeqAbstFormP [simp]:
       "eval_fm e (SeqAbstFormP v i x x' s k) \<longleftrightarrow> SeqAbstForm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e" (is ?thesis2)
    and SeqAbstFormP_sf [iff]:
       "Sigma_fm (SeqAbstFormP v i x x' s k)"  (is ?thsf)
proof -
  obtain l::name and sli::name and sl::name and sl'::name and m::name and n::name and
         smi::name and sm::name and sm'::name and sni::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sli \<sharp> (s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl \<sharp> (s,v,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl' \<sharp> (s,v,m,n,smi,sm,sm',sni,sn,sn')"
         "atom m \<sharp> (s,n,smi,sm,sm',sni,sn,sn')" "atom n \<sharp> (s,smi,sm,sm',sni,sn,sn')"
         "atom smi \<sharp> (s,sm,sm',sni,sn,sn')"
         "atom sm \<sharp> (s,sm',sni,sn,sn')"
         "atom sm' \<sharp> (s,sni,sn,sn')"
         "atom sni \<sharp> (s,sn,sn')" "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> s"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by (auto intro: LstSeqP_OrdP)
  show ?thesis2 using atoms
    unfolding SeqAbstForm_def BuildSeq3_def BuildSeq_def Builds_def
              HBall_def HBex_def q_defs AbstMakeForm_def
    by (force simp add: LstSeq_imp_Ord   Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"]
                        Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
              intro!: conj_cong [OF refl] all_cong)
qed

lemma SeqAbstFormP_subst [simp]:
      "(SeqAbstFormP v u x x' s k)(i::=t) =
       SeqAbstFormP (subst i t v) (subst i t u) (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sli::name and sl::name and sl'::name and m::name and n::name and
         smi::name and sm::name and sm'::name and sni::name and sn::name and sn'::name
   where "atom l \<sharp> (i,t,s,k,v,sli,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sli \<sharp> (i,t,s,v,sl,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl \<sharp> (i,t,s,v,sl',m,n,smi,sm,sm',sni,sn,sn')"
         "atom sl' \<sharp> (i,t,s,v,m,n,smi,sm,sm',sni,sn,sn')"
         "atom m \<sharp> (i,t,s,n,smi,sm,sm',sni,sn,sn')"
         "atom n \<sharp> (i,t,s,smi,sm,sm',sni,sn,sn')"
         "atom smi \<sharp> (i,t,s,sm,sm',sni,sn,sn')"
         "atom sm \<sharp> (i,t,s,sm',sni,sn,sn')" "atom sm' \<sharp> (i,t,s,sni,sn,sn')"
         "atom sni \<sharp> (i,t,s,sn,sn')" "atom sn \<sharp> (i,t,s,sn')" "atom sn' \<sharp> (i,t,s)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqAbstFormP.simps [of l _ _ _ sli sl sl' m n smi sm sm' sni sn sn'])
qed

declare SeqAbstFormP.simps [simp del]

subsection \<open>Defining the syntax: the main AbstForm predicate\<close>

definition AbstForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "AbstForm v i x x' \<equiv> is_Var v \<and> Ord i \<and> (\<exists>s k. SeqAbstForm v i x x' s k)"

nominal_function AbstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,x,x',k);
          atom k \<sharp> (v,i,x,x')\<rbrakk> \<Longrightarrow>
    AbstFormP v i x x' = VarP v AND OrdP i AND Ex s (Ex k (SeqAbstFormP v i x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def AbstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AbstFormP_fresh_iff [simp]:
       "a \<sharp> AbstFormP v i x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x'" (is ?thesis1)
    and eval_fm_AbstFormP [simp]:
       "eval_fm e (AbstFormP v i x x') \<longleftrightarrow> AbstForm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e" (is ?thesis2)
    and AbstFormP_sf [iff]:
       "Sigma_fm (AbstFormP v i x x')"    (is ?thsf)
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',k)" "atom k \<sharp> (v,i,x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: AbstForm_def)
qed

lemma AbstFormP_subst [simp]:
     "(AbstFormP v i x x')(j::=t) = AbstFormP (subst j t v) (subst j t i) (subst j t x) (subst j t x')"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',t,j,k)" "atom k \<sharp> (v,i,x,x',t,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: AbstFormP.simps [of s _ _ _ _ k])
qed

declare AbstFormP.simps [simp del]


subsection \<open>Correctness: It Coincides with Abstraction over real Formulas\<close>

lemma AbstForm_imp_Ord: "AbstForm v u x x' \<Longrightarrow> Ord v"
  by (metis AbstForm_def is_Var_def)

lemma AbstForm_imp_abst_dbfm:
  assumes "AbstForm v i x x'"
  shows "\<exists>A. x = \<lbrakk>quot_dbfm A\<rbrakk>e \<and>
             x' = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) (nat_of_ord i) A)\<rbrakk>e"
proof -
  obtain s k where v: "is_Var v" and i: "Ord i" and sk: "SeqAbstForm v i x x' s k"
    using assms [unfolded AbstForm_def]
    by auto
  from sk [unfolded SeqAbstForm_def]
  show ?thesis
  proof (induction i x x' rule: BuildSeq3_induct)
    case (B i x x') thus ?case
      apply (auto simp: AbstAtomic_def dest!: AbstTerm_imp_abst_dbtm [where e=e])
      apply (rule_tac [1] x="DBEq ta tb" in exI)
      apply (rule_tac [2] x="DBMem ta tb" in exI)
      apply (auto simp: q_defs)
      done
  next
    case (C i x x' j y y' k z z')
    then obtain A1 and A2
      where "y = \<lbrakk>quot_dbfm A1\<rbrakk>e"
            "y' = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) (nat_of_ord j) A1)\<rbrakk>e"
            "z = \<lbrakk>quot_dbfm A2\<rbrakk>e"
            "z' = \<lbrakk>quot_dbfm (abst_dbfm (decode_Var v) (nat_of_ord k) A2)\<rbrakk>e"
    by blast
  with C.hyps show ?case
    apply (auto simp: AbstMakeForm_def)
    apply (rule_tac [1] x="DBDisj A1 A2" in exI)
    apply (rule_tac [2] x="DBNeg A1" in exI)
    apply (rule_tac [3] x="DBEx A1" in exI)
    apply (auto simp: C q_defs)
    done
  qed
qed

lemma AbstForm_abst_dbfm:
  "AbstForm (q_Var i) (ord_of n) \<lbrakk>quot_dbfm fm\<rbrakk>e \<lbrakk>quot_dbfm (abst_dbfm i n fm)\<rbrakk>e"
apply (induction fm arbitrary: n rule: dbfm.induct)
apply (force simp add: AbstForm_def SeqAbstForm_def AbstMakeForm_def AbstAtomic_def
                       AbstTerm_abst_dbtm htuple_minus_1 q_defs simp del: q_Var_def
             intro: BuildSeq3_exI BuildSeq3_combine)+
done

section \<open>Substitution over formulas\<close>

subsection \<open>The predicate \<open>SubstAtomicP\<close>\<close>

definition SubstAtomic :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SubstAtomic v tm y y' \<equiv> 
            (\<exists>t u t' u'. SubstTerm v tm t t' \<and> SubstTerm v tm u u' \<and>
             ((y = q_Eq t u \<and> y' = q_Eq t' u') \<or> (y = q_Mem t u \<and> y' = q_Mem t' u')))"

nominal_function SubstAtomicP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (v,tm,y,y',t',u,u');
          atom t' \<sharp> (v,tm,y,y',u,u');
          atom u \<sharp> (v,tm,y,y',u');
          atom u' \<sharp> (v,tm,y,y')\<rbrakk> \<Longrightarrow>
    SubstAtomicP v tm y y' =
         Ex t (Ex u (Ex t' (Ex u'
           (SubstTermP v tm (Var t) (Var t') AND SubstTermP v tm (Var u) (Var u') AND
                      ((y EQ Q_Eq (Var t) (Var u) AND y' EQ Q_Eq (Var t') (Var u')) OR
                       (y EQ Q_Mem (Var t) (Var u) AND y' EQ Q_Mem (Var t') (Var u')))))))"
by (auto simp: eqvt_def SubstAtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstAtomicP_fresh_iff [simp]:
       "a \<sharp> SubstAtomicP v tm y y' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> tm \<and> a \<sharp> y \<and> a \<sharp> y'"           (is ?thesis1)
    and eval_fm_SubstAtomicP [simp]:
       "eval_fm e (SubstAtomicP v tm y y') \<longleftrightarrow> SubstAtomic \<lbrakk>v\<rbrakk>e \<lbrakk>tm\<rbrakk>e \<lbrakk>y\<rbrakk>e \<lbrakk>y'\<rbrakk>e"  (is ?thesis2)
    and SubstAtomicP_sf [iff]: "Sigma_fm (SubstAtomicP v tm y y')"               (is ?thsf)
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',t',u,u')" "atom t' \<sharp> (v,tm,y,y',u,u')"
          "atom u \<sharp> (v,tm,y,y',u')" "atom u' \<sharp> (v,tm,y,y')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf 
    by (auto simp: SubstAtomic_def q_defs)
qed

lemma SubstAtomicP_subst [simp]:
  "(SubstAtomicP v tm y y')(i::=w) = SubstAtomicP (subst i w v) (subst i w tm) (subst i w y) (subst i w y')"
proof -
  obtain t::name and u::name and t'::name  and u'::name
    where "atom t \<sharp> (v,tm,y,y',w,i,t',u,u')" "atom t' \<sharp> (v,tm,y,y',w,i,u,u')"
          "atom u \<sharp> (v,tm,y,y',w,i,u')" "atom u' \<sharp> (v,tm,y,y',w,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (simp add: SubstAtomicP.simps [of t _ _ _ _ t' u u'])
qed

lemma SubstAtomicP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> tm EQ tm'; H \<turnstile> x EQ x'; H \<turnstile> y EQ y'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstAtomicP v tm x y IFF SubstAtomicP v' tm' x' y'"
  by (rule P4_cong) auto


subsection \<open>The predicate \<open>SubstMakeForm\<close>\<close>

definition SubstMakeForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SubstMakeForm y y' u u' w w' \<equiv>
          ((y = q_Disj u w \<and> y' = q_Disj u' w') \<or>
           (y = q_Neg u \<and> y' = q_Neg u') \<or>
           (y = q_Ex u \<and> y' = q_Ex u'))"

definition SeqSubstForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqSubstForm v u x x' s k \<equiv> BuildSeq2 (SubstAtomic v u) SubstMakeForm s k x x'"

nominal_function SeqSubstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,v,u,sl,sl',m,n,sm,sm',sn,sn');
          atom sl \<sharp> (s,v,u,sl',m,n,sm,sm',sn,sn');
          atom sl' \<sharp> (s,v,u,m,n,sm,sm',sn,sn');
          atom m \<sharp> (s,n,sm,sm',sn,sn'); atom n \<sharp> (s,sm,sm',sn,sn');
          atom sm \<sharp> (s,sm',sn,sn'); atom sm' \<sharp> (s,sn,sn');
          atom sn \<sharp> (s,sn'); atom sn' \<sharp> s\<rbrakk> \<Longrightarrow>
    SeqSubstFormP v u x x' s k =
      LstSeqP s k (HPair x x') AND
      All2 l (SUCC k) (Ex sl (Ex sl' (HPair (Var l) (HPair (Var sl) (Var sl')) IN s AND
                (SubstAtomicP v u (Var sl) (Var sl') OR
                Ex m (Ex n (Ex sm (Ex sm' (Ex sn (Ex sn' (Var m IN Var l AND Var n IN Var l AND
                       HPair (Var m) (HPair (Var sm) (Var sm')) IN s AND
                       HPair (Var n) (HPair (Var sn) (Var sn')) IN s AND
                       ((Var sl EQ Q_Disj (Var sm) (Var sn) AND
                        Var sl' EQ Q_Disj (Var sm') (Var sn')) OR
                        (Var sl EQ Q_Neg (Var sm) AND Var sl' EQ Q_Neg (Var sm')) OR
                        (Var sl EQ Q_Ex (Var sm) AND Var sl' EQ Q_Ex (Var sm')))))))))))))"
  apply (simp_all add: eqvt_def SeqSubstFormP_graph_aux_def flip_fresh_fresh)
  by auto (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqSubstFormP_fresh_iff [simp]:
       "a \<sharp> SeqSubstFormP v u x x' s k \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> u \<and> a \<sharp> x \<and> a \<sharp> x' \<and> a \<sharp> s \<and> a \<sharp> k"  (is ?thesis1)
    and eval_fm_SeqSubstFormP [simp]:
       "eval_fm e (SeqSubstFormP v u x x' s k) \<longleftrightarrow> 
         SeqSubstForm \<lbrakk>v\<rbrakk>e \<lbrakk>u\<rbrakk>e \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e" (is ?thesis2)
    and SeqSubstFormP_sf [iff]:
       "Sigma_fm (SeqSubstFormP v u x x' s k)"  (is ?thsf)
    and SeqSubstFormP_imp_OrdP:
       "{ SeqSubstFormP v u x x' s k } \<turnstile> OrdP k"  (is ?thOrd)
    and SeqSubstFormP_imp_LstSeqP:
       "{ SeqSubstFormP v u x x' s k } \<turnstile> LstSeqP s k (HPair x x')"  (is ?thLstSeq)
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
    where atoms:
         "atom l \<sharp> (s,k,v,u,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,u,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,u,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,n,sm,sm',sn,sn')" "atom n \<sharp> (s,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,sm',sn,sn')" "atom sm' \<sharp> (s,sn,sn')"
         "atom sn \<sharp> (s,sn')" "atom sn' \<sharp> (s)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf ?thOrd ?thLstSeq
    by (auto intro: LstSeqP_OrdP)
  show ?thesis2 using atoms
    unfolding SeqSubstForm_def BuildSeq2_def BuildSeq_def Builds_def
                 HBall_def HBex_def q_defs SubstMakeForm_def
    by (force simp add: LstSeq_imp_Ord   Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"]
                 Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
              intro!: conj_cong [OF refl]  all_cong)
qed

lemma SeqSubstFormP_subst [simp]:
      "(SeqSubstFormP v u x x' s k)(i::=t) =
       SeqSubstFormP (subst i t v) (subst i t u) (subst i t x) (subst i t x') (subst i t s) (subst i t k)"
proof -
  obtain l::name and sl::name and sl'::name and m::name and n::name and
         sm::name and sm'::name and sn::name and sn'::name
   where "atom l \<sharp> (s,k,v,u,t,i,sl,sl',m,n,sm,sm',sn,sn')"
         "atom sl \<sharp> (s,v,u,t,i,sl',m,n,sm,sm',sn,sn')"
         "atom sl' \<sharp> (s,v,u,t,i,m,n,sm,sm',sn,sn')"
         "atom m \<sharp> (s,t,i,n,sm,sm',sn,sn')" "atom n \<sharp> (s,t,i,sm,sm',sn,sn')"
         "atom sm \<sharp> (s,t,i,sm',sn,sn')" "atom sm' \<sharp> (s,t,i,sn,sn')"
         "atom sn \<sharp> (s,t,i,sn')" "atom sn' \<sharp> (s,t,i)"
    by (metis obtain_fresh)
  thus ?thesis
    by (force simp add: SeqSubstFormP.simps [of l _ _ _ _ sl sl' m n sm sm' sn sn'])
qed

lemma SeqSubstFormP_cong:
  "\<lbrakk>H \<turnstile> t EQ t'; H \<turnstile> u EQ u'; H \<turnstile> s EQ s'; H \<turnstile> k EQ k'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SeqSubstFormP v i t u s k IFF SeqSubstFormP v i t' u' s' k'"
   by (rule P4_cong [where tms="[v,i]"]) (auto simp: fresh_Cons)

declare SeqSubstFormP.simps [simp del]

subsection \<open>Defining the syntax: the main SubstForm predicate\<close>

definition SubstForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
where "SubstForm v u x x' \<equiv> is_Var v \<and> Term u \<and> (\<exists>s k. SeqSubstForm v u x x' s k)"

nominal_function SubstFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom s \<sharp> (v,i,x,x',k); atom k \<sharp> (v,i,x,x')\<rbrakk> \<Longrightarrow>
    SubstFormP v i x x' =
      VarP v AND TermP i AND Ex s (Ex k (SeqSubstFormP v i x x' (Var s) (Var k)))"
  by (auto simp: eqvt_def SubstFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SubstFormP_fresh_iff [simp]:
       "a \<sharp> SubstFormP v i x x' \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> i \<and> a \<sharp> x \<and> a \<sharp> x'"  (is ?thesis1)
    and eval_fm_SubstFormP [simp]:
       "eval_fm e (SubstFormP v i x x') \<longleftrightarrow> SubstForm \<lbrakk>v\<rbrakk>e \<lbrakk>i\<rbrakk>e \<lbrakk>x\<rbrakk>e \<lbrakk>x'\<rbrakk>e"  (is ?thesis2)
    and SubstFormP_sf [iff]:
       "Sigma_fm (SubstFormP v i x x')"  (is ?thsf)
proof -
  obtain s::name and k::name
    where "atom s \<sharp> (v,i,x,x',k)"  "atom k \<sharp> (v,i,x,x')"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: SubstForm_def)
qed

lemma SubstFormP_subst [simp]:
     "(SubstFormP v i x x')(j::=t) = SubstFormP (subst j t v) (subst j t i) (subst j t x) (subst j t x')"
proof -
  obtain s::name and k::name  where "atom s \<sharp> (v,i,x,x',t,j,k)" "atom k \<sharp> (v,i,x,x',t,j)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SubstFormP.simps [of s _ _ _ _ k])
qed

lemma SubstFormP_cong:
  "\<lbrakk>H \<turnstile> v EQ v'; H \<turnstile> i EQ i'; H \<turnstile> t EQ t'; H \<turnstile> u EQ u'\<rbrakk>
   \<Longrightarrow> H \<turnstile> SubstFormP v i t u IFF SubstFormP v' i' t' u'"
  by (rule P4_cong) auto

lemma ground_SubstFormP [simp]: "ground_fm (SubstFormP v y x x') \<longleftrightarrow> ground v \<and> ground y \<and> ground x \<and> ground x'"
  by (auto simp: ground_aux_def ground_fm_aux_def supp_conv_fresh)

declare SubstFormP.simps [simp del]

subsection \<open>Correctness of substitution over formulas\<close>

lemma SubstForm_imp_subst_dbfm_lemma:
  assumes "SubstForm v \<lbrakk>quot_dbtm u\<rbrakk>e x x'"
    shows "\<exists>A. x = \<lbrakk>quot_dbfm A\<rbrakk>e \<and>
               x' = \<lbrakk>quot_dbfm (subst_dbfm u (decode_Var v) A)\<rbrakk>e"
proof -
  obtain s k where v: "is_Var v" and u: "Term \<lbrakk>quot_dbtm u\<rbrakk>e"
               and sk: "SeqSubstForm v \<lbrakk>quot_dbtm u\<rbrakk>e x x' s k"
    using assms [unfolded SubstForm_def]
    by blast
  from sk [unfolded SeqSubstForm_def]
  show ?thesis
  proof (induct x x' rule: BuildSeq2_induct)
    case (B x x') thus ?case
      apply (auto simp: SubstAtomic_def elim!: SubstTerm_imp_subst_dbtm' [where e=e])
      apply (rule_tac [1] x="DBEq ta tb" in exI)
      apply (rule_tac [2] x="DBMem ta tb" in exI)
      apply (auto simp: q_defs)
      done
  next
    case (C x x' y y' z z')
    then obtain A and B
      where "y = \<lbrakk>quot_dbfm A\<rbrakk>e" "y' = \<lbrakk>quot_dbfm (subst_dbfm u (decode_Var v) A)\<rbrakk>e"
            "z = \<lbrakk>quot_dbfm B\<rbrakk>e" "z' = \<lbrakk>quot_dbfm (subst_dbfm u (decode_Var v) B)\<rbrakk>e"
    by blast
  with C.hyps show ?case
    apply (auto simp: SubstMakeForm_def)
    apply (rule_tac [1] x="DBDisj A B" in exI)
    apply (rule_tac [2] x="DBNeg A" in exI)
    apply (rule_tac [3] x="DBEx A" in exI)
    apply (auto simp: C q_defs)
    done
  qed
qed

lemma SubstForm_imp_subst_dbfm:
  assumes "SubstForm v u x x'"
   obtains t A where "u = \<lbrakk>quot_dbtm t\<rbrakk>e"
                     "x = \<lbrakk>quot_dbfm A\<rbrakk>e"
                     "x' = \<lbrakk>quot_dbfm (subst_dbfm t (decode_Var v) A)\<rbrakk>e"
proof -
  obtain t where "u = \<lbrakk>quot_dbtm t\<rbrakk>e"
    using assms [unfolded SubstForm_def]
    by (metis Term_imp_wf_dbtm)
  thus ?thesis
    by (metis SubstForm_imp_subst_dbfm_lemma assms that)
qed

lemma SubstForm_subst_dbfm:
  assumes u: "wf_dbtm u"
  shows "SubstForm (q_Var i) \<lbrakk>quot_dbtm u\<rbrakk>e \<lbrakk>quot_dbfm A\<rbrakk>e
                             \<lbrakk>quot_dbfm (subst_dbfm u i A)\<rbrakk>e"
apply (induction A rule: dbfm.induct)
apply (force simp: u SubstForm_def SeqSubstForm_def SubstAtomic_def SubstMakeForm_def 
                   SubstTerm_subst_dbtm q_defs simp del: q_Var_def
           intro: BuildSeq2_exI BuildSeq2_combine)+
done

corollary SubstForm_subst_dbfm_eq:
  "\<lbrakk>v = q_Var i; Term ux; ux = \<lbrakk>quot_dbtm u\<rbrakk>e; A' = subst_dbfm u i A\<rbrakk>
   \<Longrightarrow> SubstForm v ux \<lbrakk>quot_dbfm A\<rbrakk>e \<lbrakk>quot_dbfm A'\<rbrakk>e"
  by (metis SubstForm_subst_dbfm Term_imp_is_tm quot_dbtm_inject_lemma quot_tm_def wf_dbtm_iff_is_tm)


section \<open>The predicate \<open>AtomicP\<close>\<close>

definition Atomic :: "hf \<Rightarrow> bool"
  where "Atomic y \<equiv>\<exists>t u. Term t \<and> Term u \<and> (y = q_Eq t u \<or> y = q_Mem t u)"

nominal_function AtomicP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom t \<sharp> (u,y); atom u \<sharp> y\<rbrakk> \<Longrightarrow>
    AtomicP y = Ex t (Ex u (TermP (Var t) AND TermP (Var u) AND
                      (y EQ Q_Eq (Var t) (Var u) OR
                       y EQ Q_Mem (Var t) (Var u))))"
  by (auto simp: eqvt_def AtomicP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows AtomicP_fresh_iff [simp]: "a \<sharp> AtomicP y \<longleftrightarrow> a \<sharp> y"    (is ?thesis1)
    and eval_fm_AtomicP [simp]: "eval_fm e (AtomicP y) \<longleftrightarrow> Atomic\<lbrakk>y\<rbrakk>e"    (is ?thesis2)
    and AtomicP_sf [iff]: "Sigma_fm (AtomicP y)"  (is ?thsf)
proof -
  obtain t::name and u::name  where "atom t \<sharp> (u,y)"  "atom u \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: Atomic_def q_defs)
qed


section \<open>The predicate \<open>MakeForm\<close>\<close>

definition MakeForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "MakeForm y u w \<equiv>
         y = q_Disj u w \<or> y = q_Neg u \<or>
         (\<exists>v u'. AbstForm v 0 u u' \<and> y = q_Ex u')"

nominal_function MakeFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom v \<sharp> (y,u,w,au); atom au \<sharp> (y,u,w)\<rbrakk> \<Longrightarrow>
    MakeFormP y u w =
      y EQ Q_Disj u w OR y EQ Q_Neg u OR
      Ex v (Ex au (AbstFormP (Var v) Zero u (Var au) AND y EQ Q_Ex (Var au)))"
  by (auto simp: eqvt_def MakeFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows MakeFormP_fresh_iff [simp]:
       "a \<sharp> MakeFormP y u w \<longleftrightarrow> a \<sharp> y \<and> a \<sharp> u \<and> a \<sharp> w"  (is ?thesis1)
    and eval_fm_MakeFormP [simp]:
       "eval_fm e (MakeFormP y u w) \<longleftrightarrow> MakeForm \<lbrakk>y\<rbrakk>e \<lbrakk>u\<rbrakk>e \<lbrakk>w\<rbrakk>e"  (is ?thesis2)
    and MakeFormP_sf [iff]:
       "Sigma_fm (MakeFormP y u w)"  (is ?thsf)
proof -
  obtain v::name and au::name  where "atom v \<sharp> (y,u,w,au)"  "atom au \<sharp> (y,u,w)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: MakeForm_def q_defs)
qed

declare MakeFormP.simps [simp del]


section \<open>The predicate \<open>SeqFormP\<close>\<close>

(*SeqForm(s,k,t) \<equiv> LstSeq(s,k,t) \<and> (\<forall>n\<in>k)[Atomic (s n) \<or> (\<exists>m,l\<in>n)[MakeForm (s m) (s l) (s n)]]*)
definition SeqForm :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "SeqForm s k y \<equiv> BuildSeq Atomic MakeForm s k y"

nominal_function SeqFormP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom l \<sharp> (s,k,t,sl,m,n,sm,sn); atom sl \<sharp> (s,k,t,m,n,sm,sn);
          atom m \<sharp> (s,k,t,n,sm,sn); atom n \<sharp> (s,k,t,sm,sn);
          atom sm \<sharp> (s,k,t,sn); atom sn \<sharp> (s,k,t)\<rbrakk> \<Longrightarrow>
    SeqFormP s k t =
      LstSeqP s k t AND
      All2 n (SUCC k) (Ex sn (HPair (Var n) (Var sn) IN s AND (AtomicP (Var sn) OR
                Ex m (Ex l (Ex sm (Ex sl (Var m IN Var n AND Var l IN Var n AND
                       HPair (Var m) (Var sm) IN s AND HPair (Var l) (Var sl) IN s AND
                       MakeFormP (Var sn) (Var sm) (Var sl))))))))"
  by (auto simp: eqvt_def SeqFormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows SeqFormP_fresh_iff [simp]:
       "a \<sharp> SeqFormP s k t \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> t" (is ?thesis1)
    and eval_fm_SeqFormP [simp]:
       "eval_fm e (SeqFormP s k t) \<longleftrightarrow> SeqForm \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e \<lbrakk>t\<rbrakk>e"   (is ?thesis2)
    and SeqFormP_sf [iff]: "Sigma_fm (SeqFormP s k t)"          (is ?thsf)
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where atoms: "atom l \<sharp> (s,k,t,sl,m,n,sm,sn)"   "atom sl \<sharp> (s,k,t,m,n,sm,sn)"
        "atom m \<sharp> (s,k,t,n,sm,sn)"   "atom n \<sharp> (s,k,t,sm,sn)"
        "atom sm \<sharp> (s,k,t,sn)"       "atom sn \<sharp> (s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thsf
    by auto
  show ?thesis2 using atoms
    by (simp cong: conj_cong add: LstSeq_imp_Ord SeqForm_def BuildSeq_def Builds_def
             HBall_def HBex_def q_defs 
             Seq_iff_app [of "\<lbrakk>s\<rbrakk>e", OF LstSeq_imp_Seq_succ]
             Ord_trans [of _ _ "succ \<lbrakk>k\<rbrakk>e"])
qed

lemma SeqFormP_subst [simp]:
      "(SeqFormP s k t)(j::=w) = SeqFormP (subst j w s) (subst j w k) (subst j w t)"
proof -
  obtain l::name and sl::name and m::name and n::name and sm::name and sn::name
    where "atom l \<sharp> (j,w,s,t,k,sl,m,n,sm,sn)"   "atom sl \<sharp> (j,w,s,k,t,m,n,sm,sn)"
        "atom m \<sharp> (j,w,s,k,t,n,sm,sn)"   "atom n \<sharp> (j,w,s,k,t,sm,sn)"
        "atom sm \<sharp> (j,w,s,k,t,sn)"   "atom sn \<sharp> (j,w,s,k,t)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: SeqFormP.simps [of l _ _ _ sl m n sm sn])
qed

section \<open>The predicate \<open>FormP\<close>\<close>

subsection \<open>Definition\<close>

definition Form :: "hf \<Rightarrow> bool"
  where "Form y \<equiv> (\<exists>s k. SeqForm s k y)"

nominal_function FormP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom k \<sharp> (s,y); atom s \<sharp> y\<rbrakk> \<Longrightarrow>
    FormP y = Ex k (Ex s (SeqFormP (Var s) (Var k) y))"
  by (auto simp: eqvt_def FormP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows FormP_fresh_iff [simp]: "a \<sharp> FormP y \<longleftrightarrow> a \<sharp> y"              (is ?thesis1)
    and eval_fm_FormP [simp]:   "eval_fm e (FormP y) \<longleftrightarrow> Form \<lbrakk>y\<rbrakk>e"  (is ?thesis2)
    and FormP_sf [iff]:         "Sigma_fm (FormP y)"                 (is ?thsf)
proof -
  obtain k::name and s::name  where k: "atom k \<sharp> (s,y)" "atom s \<sharp> y"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2 ?thsf
    by (auto simp: Form_def)
qed

lemma FormP_subst [simp]: "(FormP y)(j::=w) = FormP (subst j w y)"
proof -
  obtain k::name and s::name where "atom k \<sharp> (s,j,w,y)"  "atom s \<sharp> (j,w,y)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: FormP.simps [of k s])
qed

subsection \<open>Correctness: It Corresponds to Quotations of Real Formulas\<close>

lemma AbstForm_trans_fm:
  "AbstForm (q_Var i) 0 \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<lbrakk>quot_dbfm (trans_fm [i] A)\<rbrakk>e"
  by (metis abst_trans_fm ord_of.simps(1) quot_fm_def AbstForm_abst_dbfm)

corollary AbstForm_trans_fm_eq:
  "\<lbrakk>x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk> e;  x' = \<lbrakk>quot_dbfm (trans_fm [i] A)\<rbrakk>e\<rbrakk> \<Longrightarrow> AbstForm (q_Var i) 0 x x'"
  by (metis AbstForm_trans_fm)

lemma wf_Form_quot_dbfm [simp]:
  assumes "wf_dbfm A" shows "Form \<lbrakk>quot_dbfm A\<rbrakk>e"
using assms
proof (induct rule: wf_dbfm.induct)
  case (Mem tm1 tm2)
  hence "Atomic \<lbrakk>quot_dbfm (DBMem tm1 tm2)\<rbrakk>e"
    by (auto simp: Atomic_def quot_Mem q_Mem_def dest: wf_Term_quot_dbtm)
  thus ?case
    by (auto simp: Form_def SeqForm_def BuildSeq_exI)
next
  case (Eq tm1 tm2)
  hence "Atomic \<lbrakk>quot_dbfm (DBEq tm1 tm2)\<rbrakk>e"
    by (auto simp: Atomic_def quot_Eq q_Eq_def dest: wf_Term_quot_dbtm)
  thus ?case
    by (auto simp: Form_def SeqForm_def BuildSeq_exI)
next
  case (Disj A1 A2)
    have "MakeForm \<lbrakk>quot_dbfm (DBDisj A1 A2)\<rbrakk>e \<lbrakk>quot_dbfm A1\<rbrakk>e \<lbrakk>quot_dbfm A2\<rbrakk>e"
      by (simp add: quot_Disj q_Disj_def MakeForm_def)
  thus ?case using Disj
    by (force simp add: Form_def SeqForm_def intro: BuildSeq_combine)
next
  case (Neg A)
    have "\<And>y. MakeForm \<lbrakk>quot_dbfm (DBNeg A)\<rbrakk>e \<lbrakk>quot_dbfm A\<rbrakk>e y"
      by (simp add: quot_Neg q_Neg_def MakeForm_def)
  thus ?case using Neg
    by (force simp add: Form_def SeqForm_def intro: BuildSeq_combine)
next
  case (Ex A i)
  have "\<And>A y. MakeForm \<lbrakk>quot_dbfm (DBEx (abst_dbfm i 0 A))\<rbrakk>e \<lbrakk>quot_dbfm A\<rbrakk>e y"
    by (simp add: quot_Ex q_defs MakeForm_def) (metis AbstForm_abst_dbfm ord_of.simps(1))
  thus ?case using Ex
    by (force simp add: Form_def SeqForm_def intro: BuildSeq_combine)
qed

lemma Form_quot_fm [iff]: fixes A :: fm  shows "Form \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e"
  by (metis quot_fm_def wf_Form_quot_dbfm wf_dbfm_trans_fm)

lemma Atomic_Form_is_wf_dbfm: "Atomic x \<Longrightarrow> \<exists>A. wf_dbfm A \<and> x = \<lbrakk>quot_dbfm A\<rbrakk>e"
proof (auto simp: Atomic_def)
  fix t u
  assume t: "Term t" and  u: "Term u"
  then obtain tm1 and tm2
    where tm1: "wf_dbtm tm1" "t = \<lbrakk>quot_dbtm tm1\<rbrakk>e"
      and tm2: "wf_dbtm tm2" "u = \<lbrakk>quot_dbtm tm2\<rbrakk>e"
      by (metis Term_imp_is_tm quot_tm_def wf_dbtm_trans_tm)+
  thus "\<exists>A. wf_dbfm A \<and> q_Eq t u = \<lbrakk>quot_dbfm A\<rbrakk>e"
    by (auto simp: quot_Eq q_Eq_def)
next
  fix t u
  assume t: "Term t" and  u: "Term u"
  then obtain tm1 and tm2
    where tm1: "wf_dbtm tm1" "t = \<lbrakk>quot_dbtm tm1\<rbrakk>e"
      and tm2: "wf_dbtm tm2" "u = \<lbrakk>quot_dbtm tm2\<rbrakk>e"
      by (metis Term_imp_is_tm quot_tm_def wf_dbtm_trans_tm)+
  thus "\<exists>A. wf_dbfm A \<and> q_Mem t u = \<lbrakk>quot_dbfm A\<rbrakk>e"
    by (auto simp: quot_Mem q_Mem_def)
qed

lemma SeqForm_imp_wf_dbfm:
  assumes "SeqForm s k x"
  shows "\<exists>A. wf_dbfm A \<and> x = \<lbrakk>quot_dbfm A\<rbrakk>e"
using assms [unfolded SeqForm_def]
proof (induct x rule: BuildSeq_induct)
  case (B x) thus ?case
    by (rule Atomic_Form_is_wf_dbfm)
next
  case (C x y z)
  then obtain A B where "wf_dbfm A" "y = \<lbrakk>quot_dbfm A\<rbrakk>e"
                        "wf_dbfm B" "z = \<lbrakk>quot_dbfm B\<rbrakk>e"
    by blast
  thus ?case using C
    apply (auto simp: MakeForm_def dest!: AbstForm_imp_abst_dbfm [where e=e])
    apply (rule exI [where x="DBDisj A B"])
    apply (rule_tac [2] x="DBNeg A" in exI)
    apply (rule_tac [3] x="DBEx (abst_dbfm (decode_Var v) 0 A)" in exI)
    apply (auto simp: q_defs)
    done
qed

lemma Form_imp_wf_dbfm:
  assumes "Form x" obtains A where "wf_dbfm A" "x = \<lbrakk>quot_dbfm A\<rbrakk>e"
  by (metis assms SeqForm_imp_wf_dbfm Form_def)

lemma Form_imp_is_fm: assumes "Form x" obtains A::fm where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk> e"
  by (metis assms Form_imp_wf_dbfm quot_fm_def wf_dbfm_imp_is_fm)

lemma SubstForm_imp_subst_fm:
  assumes "SubstForm v \<lbrakk>\<lceil>u\<rceil>\<rbrakk>e x x'" "Form x"
  obtains A::fm where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk> e" "x' = \<lbrakk>\<lceil>A(decode_Var v::=u)\<rceil>\<rbrakk> e"
  using assms [unfolded quot_tm_def]
  by (auto simp: quot_fm_def dest!: SubstForm_imp_subst_dbfm_lemma)
     (metis Form_imp_is_fm eval_quot_dbfm_ignore quot_dbfm_inject_lemma quot_fm_def)

lemma SubstForm_unique:
  assumes "is_Var v" and "Term y" and "Form x"
     shows "SubstForm v y x x' \<longleftrightarrow>
            (\<exists>t::tm. y = \<lbrakk>\<lceil>t\<rceil>\<rbrakk>e \<and> (\<exists>A::fm. x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<and> x' = \<lbrakk>\<lceil>A(decode_Var v::=t)\<rceil>\<rbrakk>e))"
  using assms
  apply (auto elim!: Term_imp_wf_dbtm [where e=e] Form_imp_is_fm [where e=e] 
                     SubstForm_imp_subst_dbfm [where e=e])
  apply (auto simp: quot_tm_def quot_fm_def is_Var_iff q_Var_def intro: SubstForm_subst_dbfm_eq)
  apply (metis subst_fm_trans_commute wf_dbtm_imp_is_tm)
  done

lemma SubstForm_quot_unique: "SubstForm (q_Var i) \<lbrakk>\<lceil>t\<rceil>\<rbrakk>e \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e x' \<longleftrightarrow> x' = \<lbrakk>\<lceil>A(i::=t)\<rceil>\<rbrakk> e"
  by (subst SubstForm_unique [where e=e]) auto

lemma SubstForm_quot: "SubstForm \<lbrakk>\<lceil>Var i\<rceil>\<rbrakk>e \<lbrakk>\<lceil>t\<rceil>\<rbrakk>e \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e \<lbrakk>\<lceil>A(i::=t)\<rceil>\<rbrakk>e"
  by (metis SubstForm_quot_unique eval_Var_q)

subsection \<open>The predicate \<open>VarNonOccFormP\<close> (Derived from \<open>SubstFormP\<close>)\<close>

definition VarNonOccForm :: "hf \<Rightarrow> hf \<Rightarrow> bool"
where "VarNonOccForm v x \<equiv> Form x \<and> SubstForm v 0 x x" 

nominal_function VarNonOccFormP :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "VarNonOccFormP v x = FormP x AND SubstFormP v Zero x x"
  by (auto simp: eqvt_def VarNonOccFormP_graph_aux_def) 

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows VarNonOccFormP_fresh_iff [simp]: "a \<sharp> VarNonOccFormP v y \<longleftrightarrow> a \<sharp> v \<and> a \<sharp> y" (is ?thesis1)
    and eval_fm_VarNonOccFormP [simp]:
       "eval_fm e (VarNonOccFormP v y) \<longleftrightarrow> VarNonOccForm \<lbrakk>v\<rbrakk>e \<lbrakk>y\<rbrakk>e"    (is ?thesis2)
    and VarNonOccFormP_sf [iff]: "Sigma_fm (VarNonOccFormP v y)" (is ?thsf)
proof -
  show ?thesis1 ?thsf ?thesis2
    by (auto simp add: VarNonOccForm_def)
qed

subsection \<open>Correctness for Real Terms and Formulas\<close>

lemma VarNonOccForm_imp_dbfm_fresh:
  assumes "VarNonOccForm v x" 
  shows "\<exists>A. wf_dbfm A \<and> x = \<lbrakk>quot_dbfm A\<rbrakk>e \<and> atom (decode_Var v) \<sharp> A"
proof -
  obtain A' where A': "wf_dbfm A'" "x = \<lbrakk>quot_dbfm A'\<rbrakk>e" "SubstForm v \<lbrakk>quot_dbtm DBZero\<rbrakk>e x x"
    using assms [unfolded VarNonOccForm_def]
    by auto (metis Form_imp_wf_dbfm)
  then obtain A where "x = \<lbrakk>quot_dbfm A\<rbrakk>e"
                      "x = \<lbrakk>quot_dbfm (subst_dbfm DBZero (decode_Var v) A)\<rbrakk>e"
    by (metis SubstForm_imp_subst_dbfm_lemma)
  thus ?thesis using A' 
    by auto (metis fresh_iff_non_subst_dbfm)
qed  

corollary VarNonOccForm_imp_fresh:
  assumes "VarNonOccForm v x"  obtains A::fm where "x = \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e" "atom (decode_Var v) \<sharp> A"
  using VarNonOccForm_imp_dbfm_fresh [OF assms, where e=e]
  by (auto simp: quot_fm_def wf_dbfm_iff_is_fm)

lemma VarNonOccForm_dbfm:
  "wf_dbfm A \<Longrightarrow> atom i \<sharp> A \<Longrightarrow> VarNonOccForm (q_Var i) \<lbrakk>quot_dbfm A\<rbrakk>e"
by (auto intro: SubstForm_subst_dbfm_eq [where u=DBZero] 
    simp add: VarNonOccForm_def Const_0 Const_imp_Term fresh_iff_non_subst_dbfm [symmetric]) 

corollary fresh_imp_VarNonOccForm:
  fixes A::fm  shows "atom i \<sharp> A \<Longrightarrow> VarNonOccForm (q_Var i) \<lbrakk>\<lceil>A\<rceil>\<rbrakk>e"
  by (simp add: quot_fm_def wf_dbfm_trans_fm VarNonOccForm_dbfm)

declare VarNonOccFormP.simps [simp del]

end

