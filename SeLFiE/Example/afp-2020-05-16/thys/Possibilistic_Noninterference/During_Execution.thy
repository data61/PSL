section \<open>During-execution security\<close> 

theory During_Execution 
imports Bisim Language_Semantics begin


subsection \<open>Basic setting\<close>

locale PL_Indis = PL tval aval 
  for 
    tval :: "'test \<Rightarrow> 'state \<Rightarrow> bool" and 
    aval :: "'atom \<Rightarrow> 'state \<Rightarrow> 'state"
  +
  fixes 
    indis :: "'state rel" 
  assumes 
    equiv_indis: "equiv UNIV indis" 
    

(*******************************************)
context PL_Indis 
begin 

abbreviation indisAbbrev (infix "\<approx>" 50)
where "s1 \<approx> s2 \<equiv> (s1,s2) \<in> indis"

definition indisE (infix "\<approx>e" 50) where 
"se1 \<approx>e se2 \<equiv> 
 case (se1,se2) of 
   (Inl s1, Inl s2) \<Rightarrow> s1 \<approx> s2
  |(Inr err1, Inr err2) \<Rightarrow> err1 = err2"

lemma refl_indis: "refl indis"
and trans_indis: "trans indis"
and sym_indis: "sym indis"
using equiv_indis unfolding equiv_def by auto

lemma indis_refl[intro]: "s \<approx> s"
using refl_indis unfolding refl_on_def by simp

lemma indis_trans: "\<lbrakk>s \<approx> s'; s' \<approx> s''\<rbrakk> \<Longrightarrow> s \<approx> s''"
using trans_indis unfolding trans_def by blast

lemma indis_sym: "s \<approx> s' \<Longrightarrow> s' \<approx> s"
using sym_indis unfolding sym_def by blast


subsection\<open>Compatibility and discreetness\<close> 

definition compatTst where 
"compatTst tst \<equiv> 
 \<forall> s t. s \<approx> t \<longrightarrow> tval tst s = tval tst t"

definition compatAtm where 
"compatAtm atm \<equiv> 
 \<forall> s t. s \<approx> t \<longrightarrow> aval atm s \<approx> aval atm t"

(* \<approx>-preservation: *)
definition presAtm where 
"presAtm atm \<equiv> 
 \<forall> s. s \<approx> aval atm s"

coinductive discr where 
intro: 
"\<lbrakk>\<And> s c' s'. (c,s) \<rightarrow>c (c',s') \<Longrightarrow> s \<approx> s' \<and> discr c'; 
  \<And> s s'. (c,s) \<rightarrow>t s' \<Longrightarrow> s \<approx> s'\<rbrakk> 
  \<Longrightarrow> discr c"

lemma presAtm_compatAtm[simp]:
assumes "presAtm atm"
shows "compatAtm atm"
using assms unfolding compatAtm_def
by (metis presAtm_def indis_sym indis_trans)

text\<open>Coinduction for discreetness:\<close>

lemma discr_coind:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> s \<approx> s' \<and> (phi c' \<or> discr c')" and 
***: "\<And> c s s'. \<lbrakk>phi c; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> s \<approx> s'"
shows "discr c"
using * apply - apply(erule discr.coinduct) using ** *** by auto

lemma discr_raw_coind:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> s \<approx> s' \<and> phi c'" and 
***: "\<And> c s s'. \<lbrakk>phi c; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> s \<approx> s'"
shows "discr c"
using * apply - apply(erule discr_coind) using ** *** by blast+

text\<open>Discreetness versus transition:\<close>

lemma discr_transC:
assumes *: "discr c" and **: "(c,s) \<rightarrow>c (c',s')"
shows "discr c'"
using * apply - apply(erule discr.cases) using ** by blast

lemma discr_MtransC:
assumes "discr c" and "(c,s) \<rightarrow>*c (c',s')"
shows "discr c'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> discr c \<longrightarrow> discr c'"
  apply(erule MtransC_induct2) using discr_transC by blast+
  thus ?thesis using assms by blast
qed

lemma discr_transC_indis:
assumes *: "discr c" and **: "(c,s) \<rightarrow>c (c',s')"
shows "s \<approx> s'"
using * apply - apply(erule discr.cases) using ** by blast

lemma discr_MtransC_indis:
assumes "discr c" and "(c,s) \<rightarrow>*c (c',s')"
shows "s \<approx> s'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> discr c \<longrightarrow> s \<approx> s'"
  apply(erule MtransC_induct2)
  apply (metis indis_refl)
  by (metis discr.cases discr_MtransC indis_trans)
  thus ?thesis using assms by blast
qed

lemma discr_transT:
assumes *: "discr c" and **: "(c,s) \<rightarrow>t s'"
shows "s \<approx> s'"
using * apply - apply(erule discr.cases) using ** by blast

lemma discr_MtransT:
assumes *: "discr c" and **: "(c,s) \<rightarrow>*t s'"
shows "s \<approx> s'"
proof-
  obtain d' t' where 
  cs: "(c,s) \<rightarrow>*c (d',t')" and d't': "(d',t') \<rightarrow>t s'"
  using ** by(rule MtransT_invert2)
  hence "s \<approx> t'" using * discr_MtransC_indis by blast
  moreover 
  {have "discr d'" using cs * discr_MtransC by blast 
   hence "t' \<approx> s'" using d't' discr_transT by blast
  }
  ultimately show ?thesis using indis_trans by blast
qed 


subsection\<open>Terminating-interctive discreetness\<close>

coinductive discr0 where 
intro: 
"\<lbrakk>\<And> s c' s'. \<lbrakk>mustT c s; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> s \<approx> s' \<and> discr0 c'; 
  \<And> s s'. \<lbrakk>mustT c s; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> s \<approx> s'\<rbrakk> 
  \<Longrightarrow> discr0 c" 

text\<open>Coinduction for 0-discreetness:\<close>

lemma discr0_coind[consumes 1, case_names Cont Term, induct pred: discr0]:
assumes *: "phi c" and 
**: "\<And> c s c' s'. 
       \<lbrakk>mustT c s; phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> 
       s \<approx> s' \<and> (phi c' \<or> discr0 c')" and 
***: "\<And> c s s'. \<lbrakk>mustT c s; phi c; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> s \<approx> s'"
shows "discr0 c"
using * apply - apply(erule discr0.coinduct) using ** *** by auto

lemma discr0_raw_coind[consumes 1, case_names Cont Term]:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>mustT c s; phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> s \<approx> s' \<and> phi c'" and 
***: "\<And> c s s'. \<lbrakk>mustT c s; phi c; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> s \<approx> s'"
shows "discr0 c"
using * apply - apply(erule discr0_coind) using ** *** by blast+

text\<open>0-Discreetness versus transition:\<close>

lemma discr0_transC:
assumes *: "discr0 c" and **: "mustT c s" "(c,s) \<rightarrow>c (c',s')"
shows "discr0 c'"
using * apply - apply(erule discr0.cases) using ** by blast

lemma discr0_MtransC:
assumes "discr0 c" and "mustT c s" "(c,s) \<rightarrow>*c (c',s')"
shows "discr0 c'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> mustT c s \<and> discr0 c \<longrightarrow> discr0 c'"
  apply(erule MtransC_induct2) using discr0_transC mustT_MtransC
  by blast+
  thus ?thesis using assms by blast
qed

lemma discr0_transC_indis:
assumes *: "discr0 c" and **: "mustT c s" "(c,s) \<rightarrow>c (c',s')"
shows "s \<approx> s'"
using * apply - apply(erule discr0.cases) using ** by blast

lemma discr0_MtransC_indis:
assumes "discr0 c" and "mustT c s" "(c,s) \<rightarrow>*c (c',s')"
shows "s \<approx> s'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> mustT c s \<and> discr0 c \<longrightarrow> s \<approx> s'"
  apply(erule MtransC_induct2)
  apply (metis indis_refl)
  by (metis discr0_MtransC discr0_transC_indis indis_trans mustT_MtransC)
  thus ?thesis using assms by blast
qed

lemma discr0_transT:
assumes *: "discr0 c" and **: "mustT c s" "(c,s) \<rightarrow>t s'"
shows "s \<approx> s'"
using * apply - apply(erule discr0.cases) using ** by blast

lemma discr0_MtransT:
assumes *: "discr0 c" and ***: "mustT c s" and **: "(c,s) \<rightarrow>*t s'"
shows "s \<approx> s'"
proof-
  obtain d' t' where 
  cs: "(c,s) \<rightarrow>*c (d',t')" and d't': "(d',t') \<rightarrow>t s'"
  using ** by(rule MtransT_invert2)
  hence "s \<approx> t'" using * discr0_MtransC_indis *** by blast
  moreover 
  {have "discr0 d'" using cs * discr0_MtransC *** by blast 
   hence "t' \<approx> s'"
   using *** by (metis mustT_MtransC cs d't' discr0_transT) 
  }
  ultimately show ?thesis using indis_trans by blast
qed 

lemma discr_discr0[simp]: "discr c \<Longrightarrow> discr0 c"
  by (induct rule: discr0_coind)
     (metis discr_transC discr_transC_indis discr_transT)+

subsection\<open>Self-isomorphism\<close>  

coinductive siso where 
intro: 
"\<lbrakk>\<And> s c' s'. (c,s) \<rightarrow>c (c',s') \<Longrightarrow> siso c'; 
  \<And> s t c' s'. \<lbrakk>s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t');
  \<And> s t s'. \<lbrakk>s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'\<rbrakk> 
  \<Longrightarrow> siso c"

text\<open>Coinduction for self-isomorphism:\<close>

lemma siso_coind:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> phi c' \<or> siso c'" and 
***: "\<And> c s t c' s'. \<lbrakk>phi c; s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')" and 
****: "\<And> c s t s'. \<lbrakk>phi c; s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
shows "siso c"
using * apply - apply(erule siso.coinduct) using ** *** **** by auto

lemma siso_raw_coind:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> phi c'" and 
***: "\<And> c s t c' s'. \<lbrakk>phi c; s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')" and 
****: "\<And> c s t s'. \<lbrakk>phi c; s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
shows "siso c"
using * apply - apply(erule siso_coind) using ** *** **** by blast+

text\<open>Self-Isomorphism versus transition:\<close>

lemma siso_transC:
assumes *: "siso c" and **: "(c,s) \<rightarrow>c (c',s')"
shows "siso c'"
using * apply - apply(erule siso.cases) using ** by blast

lemma siso_MtransC:
assumes "siso c" and "(c,s) \<rightarrow>*c (c',s')"
shows "siso c'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> siso c \<longrightarrow> siso c'"
  apply(erule MtransC_induct2) using siso_transC by blast+
  thus ?thesis using assms by blast
qed

lemma siso_transC_indis:
assumes *: "siso c" and **: "(c,s) \<rightarrow>c (c',s')" and ***: "s \<approx> t"
shows "\<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')"
using * apply - apply(erule siso.cases) using ** *** by blast

lemma siso_transT:
assumes *: "siso c" and **: "(c,s) \<rightarrow>t s'" and ***: "s \<approx> t"
shows "\<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
using * apply - apply(erule siso.cases) using ** *** by blast


subsection\<open>MustT-interactive self-isomorphism\<close>  

coinductive siso0 where 
intro: 
"\<lbrakk>\<And> s c' s'. \<lbrakk>mustT c s; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> siso0 c'; 
  \<And> s t c' s'. 
    \<lbrakk>mustT c s; mustT c t; s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> 
    \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t');
  \<And> s t s'. 
    \<lbrakk>mustT c s; mustT c t; s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> 
    \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'\<rbrakk> 
  \<Longrightarrow> siso0 c"

text\<open>Coinduction for self-isomorphism:\<close>

lemma siso0_coind[consumes 1, case_names Indef Cont Term, induct pred: discr0]:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; mustT c s; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> phi c' \<or> siso0 c'" and 
***: "\<And> c s t c' s'. 
        \<lbrakk>phi c; mustT c s; mustT c t; s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> 
        \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')" and 
****: "\<And> c s t s'. 
         \<lbrakk>mustT c s; mustT c t; phi c; s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> 
         \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
shows "siso0 c"
using * apply - apply(erule siso0.coinduct) using ** *** **** by auto

lemma siso0_raw_coind[consumes 1, case_names Indef Cont Term]:
assumes *: "phi c" and 
**: "\<And> c s c' s'. \<lbrakk>phi c; mustT c s; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> phi c'" and 
***: "\<And> c s t c' s'. 
        \<lbrakk>phi c; mustT c s; mustT c t; s \<approx> t; (c,s) \<rightarrow>c (c',s')\<rbrakk> \<Longrightarrow> 
        \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')" and 
****: "\<And> c s t s'. 
         \<lbrakk>phi c; mustT c s; mustT c t; s \<approx> t; (c,s) \<rightarrow>t s'\<rbrakk> \<Longrightarrow> 
         \<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
shows "siso0 c"
using * apply - apply(erule siso0_coind) using ** *** **** by blast+

text\<open>Self-Isomorphism versus transition:\<close>

lemma siso0_transC:
assumes *: "siso0 c" and **: "mustT c s" "(c,s) \<rightarrow>c (c',s')"
shows "siso0 c'"
using * apply - apply(erule siso0.cases) using ** by blast

lemma siso0_MtransC:
assumes "siso0 c" and "mustT c s" and "(c,s) \<rightarrow>*c (c',s')"
shows "siso0 c'"
proof-
  have "(c,s) \<rightarrow>*c (c',s') \<Longrightarrow> mustT c s \<and> siso0 c \<longrightarrow> siso0 c'"
  apply(erule MtransC_induct2) using siso0_transC mustT_MtransC siso0_transC
  by blast+
  thus ?thesis using assms by blast
qed

lemma siso0_transC_indis:
assumes *: "siso0 c" 
and **: "mustT c s" "mustT c t" "(c,s) \<rightarrow>c (c',s')" 
and ***: "s \<approx> t"
shows "\<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>c (c',t')"
using * apply - apply(erule siso0.cases) using ** *** by blast

lemma siso0_transT:
assumes *: "siso0 c" 
and **: "mustT c s" "mustT c t" "(c,s) \<rightarrow>t s'" 
and ***: "s \<approx> t"
shows "\<exists> t'. s' \<approx> t' \<and> (c,t) \<rightarrow>t t'"
using * apply - apply(erule siso0.cases) using ** *** by blast


subsection\<open>Notions of bisimilarity\<close> 

text\<open>Matchers:\<close>

(* Notations and conventions:
\\- ``<u>_<v>" means: ``match u by v", where u, v can be: 
C (one continuation step), MC (multiple continuation steps), 
ZOC (zero or one continuation steps), 
T (termination step), MT (multiple steps leading to termination).   *)

definition matchC_C where 
"matchC_C theta c d \<equiv> 
 \<forall> s t c' s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (\<exists> d' t'. (d,t) \<rightarrow>c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta)"

definition matchC_ZOC where 
"matchC_ZOC theta c d \<equiv> 
 \<forall> s t c' s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (s' \<approx> t \<and> (c',d) \<in> theta)
   \<or> 
   (\<exists> d' t'. (d,t) \<rightarrow>c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta)"

definition matchC_ZO where 
"matchC_ZO theta c d \<equiv> 
 \<forall> s t c' s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (s' \<approx> t \<and> (c',d) \<in> theta)
   \<or> 
   (\<exists> d' t'. (d,t) \<rightarrow>c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta) 
   \<or> 
   (\<exists> t'. (d,t) \<rightarrow>t t' \<and> s' \<approx> t' \<and> discr c')"

definition matchT_T where 
"matchT_T c d \<equiv> 
 \<forall> s t s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>t s' 
   \<longrightarrow> 
   (\<exists> t'. (d,t) \<rightarrow>t t' \<and> s' \<approx> t')"

definition matchT_ZO where 
"matchT_ZO c d \<equiv> 
 \<forall> s t s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>t s' 
   \<longrightarrow> 
   (s' \<approx> t \<and> discr d)
   \<or> 
   (\<exists> d' t'. (d,t) \<rightarrow>c (d',t') \<and> s' \<approx> t' \<and> discr d')
   \<or> 
   (\<exists> t'. (d,t) \<rightarrow>t t' \<and> s' \<approx> t')"

(*  *)

definition matchC_MC where 
"matchC_MC theta c d \<equiv> 
 \<forall> s t c' s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta)"

definition matchC_TMC where 
"matchC_TMC theta c d \<equiv> 
 \<forall> s t c' s'. 
   mustT c s \<and> mustT d t \<and> s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta)"

definition matchC_M where 
"matchC_M theta c d \<equiv> 
 \<forall> s t c' s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>c (c',s') 
   \<longrightarrow> 
   (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> (c',d') \<in> theta) 
   \<or> 
   (\<exists> t'. (d,t) \<rightarrow>*t t' \<and> s' \<approx> t' \<and> discr c')"

definition matchT_MT where 
"matchT_MT c d \<equiv> 
 \<forall> s t s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>t s' 
   \<longrightarrow> 
   (\<exists> t'. (d,t) \<rightarrow>*t t' \<and> s' \<approx> t')"

definition matchT_TMT where 
"matchT_TMT c d \<equiv> 
 \<forall> s t s'. 
   mustT c s \<and> mustT d t \<and> s \<approx> t \<and> (c,s) \<rightarrow>t s' 
   \<longrightarrow> 
   (\<exists> t'. (d,t) \<rightarrow>*t t' \<and> s' \<approx> t')"

definition matchT_M where 
"matchT_M c d \<equiv> 
 \<forall> s t s'. 
   s \<approx> t \<and> (c,s) \<rightarrow>t s' 
   \<longrightarrow> 
   (\<exists> d' t'. (d,t) \<rightarrow>*c (d',t') \<and> s' \<approx> t' \<and> discr d')
   \<or> 
   (\<exists> t'. (d,t) \<rightarrow>*t t' \<and> s' \<approx> t')"

lemmas match_defs = 
matchC_C_def 
matchC_ZOC_def matchC_ZO_def
matchT_T_def matchT_ZO_def
matchC_MC_def matchC_M_def
matchT_MT_def matchT_M_def
matchC_TMC_def matchT_TMT_def

(* For convenience, indis-symmetric variations of the above definitions: *)

lemma matchC_C_def2: 
"matchC_C theta d c =
 (\<forall> s t d' t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (\<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta))"
unfolding matchC_C_def using indis_sym by blast

lemma matchC_ZOC_def2:  
"matchC_ZOC theta d c= 
 (\<forall> s t d' t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (s \<approx> t' \<and> (d',c) \<in> theta)
   \<or> 
   (\<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta))"
unfolding matchC_ZOC_def using indis_sym by blast

lemma matchC_ZO_def2:
"matchC_ZO theta d c = 
 (\<forall> s t d' t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (s \<approx> t' \<and> (d',c) \<in> theta)
   \<or> 
   (\<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta) 
   \<or> 
   (\<exists> s'. (c,s) \<rightarrow>t s' \<and> s' \<approx> t' \<and> discr d'))"
unfolding matchC_ZO_def using indis_sym by blast

lemma matchT_T_def2:
"matchT_T d c = 
 (\<forall> s t t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>t t' 
   \<longrightarrow> 
   (\<exists> s'. (c,s) \<rightarrow>t s' \<and> s' \<approx> t'))"
unfolding matchT_T_def using indis_sym by blast

lemma matchT_ZO_def2:
"matchT_ZO d c = 
 (\<forall> s t t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>t t' 
   \<longrightarrow> 
   (s \<approx> t' \<and> discr c)
   \<or> 
   (\<exists> c' s'. (c,s) \<rightarrow>c (c',s') \<and> s' \<approx> t' \<and> discr c')
   \<or> 
   (\<exists> s'. (c,s) \<rightarrow>t s' \<and> s' \<approx> t'))"    
unfolding matchT_ZO_def using indis_sym by blast

(*  *)

lemma matchC_MC_def2:  
"matchC_MC theta d c= 
 (\<forall> s t d' t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (\<exists> c' s'. (c,s) \<rightarrow>*c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta))"
unfolding matchC_MC_def using indis_sym by blast

lemma matchC_TMC_def2:  
"matchC_TMC theta d c= 
 (\<forall> s t d' t'. 
   mustT c s \<and> mustT d t \<and> s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (\<exists> c' s'. (c,s) \<rightarrow>*c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta))"
unfolding matchC_TMC_def using indis_sym by blast

lemma matchC_M_def2:
"matchC_M theta d c = 
 (\<forall> s t d' t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>c (d',t') 
   \<longrightarrow> 
   (\<exists> c' s'. (c,s) \<rightarrow>*c (c',s') \<and> s' \<approx> t' \<and> (d',c') \<in> theta) 
   \<or> 
   (\<exists> s'. (c,s) \<rightarrow>*t s' \<and> s' \<approx> t' \<and> discr d'))"
unfolding matchC_M_def using indis_sym by blast

lemma matchT_MT_def2:
"matchT_MT d c = 
 (\<forall> s t t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>t t' 
   \<longrightarrow> 
   (\<exists> s'. (c,s) \<rightarrow>*t s' \<and> s' \<approx> t'))"
unfolding matchT_MT_def using indis_sym by blast

lemma matchT_TMT_def2:
"matchT_TMT d c = 
 (\<forall> s t t'. 
   mustT c s \<and> mustT d t \<and> s \<approx> t \<and> (d,t) \<rightarrow>t t' 
   \<longrightarrow> 
   (\<exists> s'. (c,s) \<rightarrow>*t s' \<and> s' \<approx> t'))"
unfolding matchT_TMT_def using indis_sym by blast

lemma matchT_M_def2:
"matchT_M d c = 
 (\<forall> s t t'. 
   s \<approx> t \<and> (d,t) \<rightarrow>t t' 
   \<longrightarrow> 
   (\<exists> c' s'. (c,s) \<rightarrow>*c (c',s') \<and> s' \<approx> t' \<and> discr c')
   \<or> 
   (\<exists> s'. (c,s) \<rightarrow>*t s' \<and> s' \<approx> t'))"    
unfolding matchT_M_def using indis_sym by blast

text\<open>Retracts:\<close>

(* Strong retract: *)
definition Sretr where 
"Sretr theta \<equiv> 
 {(c,d). 
    matchC_C theta c d \<and> 
    matchT_T c d}"

(* Zero-one retract: *)
definition ZOretr where 
"ZOretr theta \<equiv> 
 {(c,d). 
    matchC_ZO theta c d \<and> 
    matchT_ZO c d}"

(* Zero-one termination-sensitive retract: *)
definition ZOretrT where 
"ZOretrT theta \<equiv> 
 {(c,d). 
    matchC_ZOC theta c d \<and> 
    matchT_T c d}"

(* Weak retract: *)
definition Wretr where 
"Wretr theta \<equiv> 
 {(c,d). 
    matchC_M theta c d \<and> 
    matchT_M c d }"

(* Weak termination-sensitive retract: *)
definition WretrT where 
"WretrT theta \<equiv> 
 {(c,d). 
    matchC_MC theta c d \<and> 
    matchT_MT c d}"

(* Weak terminating-interactive termination-sensitive retract: *)
definition RetrT where 
"RetrT theta \<equiv> 
 {(c,d). 
    matchC_TMC theta c d \<and> 
    matchT_TMT c d}"

lemmas Retr_defs = 
Sretr_def 
ZOretr_def ZOretrT_def 
Wretr_def WretrT_def 
RetrT_def

text\<open>The associated bisimilarity relations:\<close>

definition Sbis where "Sbis \<equiv> bis Sretr"
definition ZObis where "ZObis \<equiv> bis ZOretr"
definition ZObisT where "ZObisT \<equiv> bis ZOretrT"
definition Wbis where "Wbis \<equiv> bis Wretr"
definition WbisT where "WbisT \<equiv> bis WretrT"
definition BisT where "BisT \<equiv> bis RetrT"

lemmas bis_defs = 
Sbis_def 
ZObis_def ZObisT_def 
Wbis_def WbisT_def 
BisT_def

abbreviation Sbis_abbrev (infix "\<approx>s" 55) where "c1 \<approx>s c2 \<equiv> (c1,c2) \<in> Sbis"
abbreviation ZObis_abbrev (infix "\<approx>01" 55) where "c1 \<approx>01 c2 \<equiv> (c1,c2) \<in> ZObis"
abbreviation ZObisT_abbrev (infix "\<approx>01T" 55) where "c1 \<approx>01T c2 \<equiv> (c1,c2) \<in> ZObisT"
abbreviation Wbis_abbrev (infix "\<approx>w" 55) where "c1 \<approx>w c2 \<equiv> (c1,c2) \<in> Wbis"
abbreviation WbisT_abbrev (infix "\<approx>wT" 55) where "c1 \<approx>wT c2 \<equiv> (c1,c2) \<in> WbisT"
abbreviation BisT_abbrev (infix "\<approx>T" 55) where "c1 \<approx>T c2 \<equiv> (c1,c2) \<in> BisT"


lemma mono_Retr:
"mono Sretr"
"mono ZOretr"  "mono ZOretrT"
"mono Wretr"  "mono WretrT"
"mono RetrT"
unfolding mono_def Retr_defs match_defs by blast+

(* Sbis: *)
lemma Sbis_prefix:
"Sbis \<subseteq> Sretr Sbis"
unfolding Sbis_def using mono_Retr bis_prefix by blast

lemma Sbis_sym: "sym Sbis"
unfolding Sbis_def using mono_Retr sym_bis by blast

lemma Sbis_Sym: "c \<approx>s d \<Longrightarrow> d \<approx>s c"
using Sbis_sym unfolding sym_def by blast

lemma Sbis_converse:
"((c,d) \<in> theta^-1 \<union> Sbis) = ((d,c) \<in> theta \<union> Sbis)"
by (metis Sbis_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma
Sbis_matchC_C: "\<And> s t. c \<approx>s d \<Longrightarrow> matchC_C Sbis c d"
and 
Sbis_matchT_T: "\<And> c d. c \<approx>s d \<Longrightarrow> matchT_T c d"
using Sbis_prefix unfolding Sretr_def by auto

lemmas Sbis_step = Sbis_matchC_C Sbis_matchT_T

lemma
Sbis_matchC_C_rev: "\<And> s t. s \<approx>s t \<Longrightarrow> matchC_C Sbis t s"
and 
Sbis_matchT_T_rev: "\<And> s t. s \<approx>s t \<Longrightarrow> matchT_T t s"
using Sbis_step Sbis_sym unfolding sym_def by blast+

lemmas Sbis_step_rev = Sbis_matchC_C_rev Sbis_matchT_T_rev

lemma Sbis_coind:  
assumes "sym theta" and "theta \<subseteq> Sretr (theta \<union> Sbis)"
shows "theta \<subseteq> Sbis"
using assms mono_Retr bis_coind 
unfolding Sbis_def by blast

lemma Sbis_raw_coind:  
assumes "sym theta" and "theta \<subseteq> Sretr theta"
shows "theta \<subseteq> Sbis"
using assms mono_Retr bis_raw_coind 
unfolding Sbis_def by blast

lemma Sbis_coind2:
assumes "theta \<subseteq> Sretr (theta \<union> Sbis)" and 
"theta ^-1 \<subseteq> Sretr ((theta ^-1) \<union> Sbis)"
shows "theta \<subseteq> Sbis"
using assms mono_Retr bis_coind2 
unfolding Sbis_def by blast

lemma Sbis_raw_coind2:
assumes "theta \<subseteq> Sretr theta" and 
"theta ^-1 \<subseteq> Sretr (theta ^-1)"
shows "theta \<subseteq> Sbis"
using assms mono_Retr bis_raw_coind2 
unfolding Sbis_def by blast

(* ZObis: *)
lemma ZObis_prefix:
"ZObis \<subseteq> ZOretr ZObis"
unfolding ZObis_def using mono_Retr bis_prefix by blast

lemma ZObis_sym: "sym ZObis"
unfolding ZObis_def using mono_Retr sym_bis by blast

lemma ZObis_converse:
"((c,d) \<in> theta^-1 \<union> ZObis) = ((d,c) \<in> theta \<union> ZObis)"
by (metis ZObis_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma ZObis_Sym: "s \<approx>01 t \<Longrightarrow> t \<approx>01 s"
using ZObis_sym unfolding sym_def by blast

lemma
ZObis_matchC_ZO: "\<And> s t. s \<approx>01 t \<Longrightarrow> matchC_ZO ZObis s t"
and 
ZObis_matchT_ZO: "\<And> s t. s \<approx>01 t \<Longrightarrow> matchT_ZO s t"
using ZObis_prefix unfolding ZOretr_def by auto

lemmas ZObis_step = ZObis_matchC_ZO ZObis_matchT_ZO 

lemma
ZObis_matchC_ZO_rev: "\<And> s t. s \<approx>01 t \<Longrightarrow> matchC_ZO ZObis t s"
and 
ZObis_matchT_ZO_rev: "\<And> s t. s \<approx>01 t \<Longrightarrow> matchT_ZO t s"
using ZObis_step ZObis_sym unfolding sym_def by blast+

lemmas ZObis_step_rev = ZObis_matchC_ZO_rev ZObis_matchT_ZO_rev

lemma ZObis_coind:  
assumes "sym theta" and "theta \<subseteq> ZOretr (theta \<union> ZObis)"
shows "theta \<subseteq> ZObis"
using assms mono_Retr bis_coind 
unfolding ZObis_def by blast

lemma ZObis_raw_coind:  
assumes "sym theta" and "theta \<subseteq> ZOretr theta"
shows "theta \<subseteq> ZObis"
using assms mono_Retr bis_raw_coind 
unfolding ZObis_def by blast

lemma ZObis_coind2:
assumes "theta \<subseteq> ZOretr (theta \<union> ZObis)" and 
"theta ^-1 \<subseteq> ZOretr ((theta ^-1) \<union> ZObis)"
shows "theta \<subseteq> ZObis"
using assms mono_Retr bis_coind2 
unfolding ZObis_def by blast

lemma ZObis_raw_coind2:
assumes "theta \<subseteq> ZOretr theta" and 
"theta ^-1 \<subseteq> ZOretr (theta ^-1)"
shows "theta \<subseteq> ZObis"
using assms mono_Retr bis_raw_coind2 
unfolding ZObis_def by blast

(* ZObisT: *)
lemma ZObisT_prefix:
"ZObisT \<subseteq> ZOretrT ZObisT"
unfolding ZObisT_def using mono_Retr bis_prefix by blast

lemma ZObisT_sym: "sym ZObisT"
unfolding ZObisT_def using mono_Retr sym_bis by blast

lemma ZObisT_Sym: "s \<approx>01T t \<Longrightarrow> t \<approx>01T s"
using ZObisT_sym unfolding sym_def by blast

lemma ZObisT_converse:
"((c,d) \<in> theta^-1 \<union> ZObisT) = ((d,c) \<in> theta \<union> ZObisT)"
by (metis ZObisT_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma
ZObisT_matchC_ZOC: "\<And> s t. s \<approx>01T t \<Longrightarrow> matchC_ZOC ZObisT s t"
and 
ZObisT_matchT_T: "\<And> s t. s \<approx>01T t \<Longrightarrow> matchT_T s t"
using ZObisT_prefix unfolding ZOretrT_def by auto

lemmas ZObisT_step = ZObisT_matchC_ZOC ZObisT_matchT_T

lemma
ZObisT_matchC_ZOC_rev: "\<And> s t. s \<approx>01T t \<Longrightarrow> matchC_ZOC ZObisT t s"
and 
ZObisT_matchT_T_rev: "\<And> s t. s \<approx>01T t \<Longrightarrow> matchT_T t s"
using ZObisT_step ZObisT_sym unfolding sym_def by blast+

lemmas ZObisT_step_rev = ZObisT_matchC_ZOC_rev ZObisT_matchT_T_rev 

lemma ZObisT_coind:  
assumes "sym theta" and "theta \<subseteq> ZOretrT (theta \<union> ZObisT)"
shows "theta \<subseteq> ZObisT"
using assms mono_Retr bis_coind 
unfolding ZObisT_def by blast

lemma ZObisT_raw_coind:  
assumes "sym theta" and "theta \<subseteq> ZOretrT theta"
shows "theta \<subseteq> ZObisT"
using assms mono_Retr bis_raw_coind 
unfolding ZObisT_def by blast

lemma ZObisT_coind2:
assumes "theta \<subseteq> ZOretrT (theta \<union> ZObisT)" and 
"theta ^-1 \<subseteq> ZOretrT ((theta ^-1) \<union> ZObisT)"
shows "theta \<subseteq> ZObisT"
using assms mono_Retr bis_coind2 
unfolding ZObisT_def by blast

lemma ZObisT_raw_coind2:
assumes "theta \<subseteq> ZOretrT theta" and 
"theta ^-1 \<subseteq> ZOretrT (theta ^-1)"
shows "theta \<subseteq> ZObisT"
using assms mono_Retr bis_raw_coind2 
unfolding ZObisT_def by blast

(* Wbis: *)
lemma Wbis_prefix:
"Wbis \<subseteq> Wretr Wbis"
unfolding Wbis_def using mono_Retr bis_prefix by blast

lemma Wbis_sym: "sym Wbis"
unfolding Wbis_def using mono_Retr sym_bis by blast

lemma Wbis_converse:
"((c,d) \<in> theta^-1 \<union> Wbis) = ((d,c) \<in> theta \<union> Wbis)"
by (metis Wbis_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma Wbis_Sym: "c \<approx>w d \<Longrightarrow> d \<approx>w c"
using Wbis_sym unfolding sym_def by blast

lemma
Wbis_matchC_M: "\<And> c d. c \<approx>w d \<Longrightarrow> matchC_M Wbis c d"
and 
Wbis_matchT_M: "\<And> c d. c \<approx>w d \<Longrightarrow> matchT_M c d"
using Wbis_prefix unfolding Wretr_def by auto

lemmas Wbis_step = Wbis_matchC_M Wbis_matchT_M 

lemma
Wbis_matchC_M_rev: "\<And> s t. s \<approx>w t \<Longrightarrow> matchC_M Wbis t s"
and 
Wbis_matchT_M_rev: "\<And> s t. s \<approx>w t \<Longrightarrow> matchT_M t s"
using Wbis_step Wbis_sym unfolding sym_def by blast+

lemmas Wbis_step_rev = Wbis_matchC_M_rev Wbis_matchT_M_rev

lemma Wbis_coind:  
assumes "sym theta" and "theta \<subseteq> Wretr (theta \<union> Wbis)"
shows "theta \<subseteq> Wbis"
using assms mono_Retr bis_coind 
unfolding Wbis_def by blast

lemma Wbis_raw_coind:  
assumes "sym theta" and "theta \<subseteq> Wretr theta"
shows "theta \<subseteq> Wbis"
using assms mono_Retr bis_raw_coind 
unfolding Wbis_def by blast

lemma Wbis_coind2:
assumes "theta \<subseteq> Wretr (theta \<union> Wbis)" and 
"theta ^-1 \<subseteq> Wretr ((theta ^-1) \<union> Wbis)"
shows "theta \<subseteq> Wbis"
using assms mono_Retr bis_coind2 
unfolding Wbis_def by blast

lemma Wbis_raw_coind2:
assumes "theta \<subseteq> Wretr theta" and 
"theta ^-1 \<subseteq> Wretr (theta ^-1)"
shows "theta \<subseteq> Wbis"
using assms mono_Retr bis_raw_coind2 
unfolding Wbis_def by blast

(* WbisT: *)
lemma WbisT_prefix:
"WbisT \<subseteq> WretrT WbisT"
unfolding WbisT_def using mono_Retr bis_prefix by blast

lemma WbisT_sym: "sym WbisT"
unfolding WbisT_def using mono_Retr sym_bis by blast

lemma WbisT_Sym: "c \<approx>wT d \<Longrightarrow> d \<approx>wT c"
using WbisT_sym unfolding sym_def by blast

lemma WbisT_converse:
"((c,d) \<in> theta^-1 \<union> WbisT) = ((d,c) \<in> theta \<union> WbisT)"
by (metis WbisT_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma
WbisT_matchC_MC: "\<And> c d. c \<approx>wT d \<Longrightarrow> matchC_MC WbisT c d"
and 
WbisT_matchT_MT: "\<And> c d. c \<approx>wT d \<Longrightarrow> matchT_MT c d"
using WbisT_prefix unfolding WretrT_def by auto

lemmas WbisT_step = WbisT_matchC_MC WbisT_matchT_MT

lemma
WbisT_matchC_MC_rev: "\<And> s t. s \<approx>wT t \<Longrightarrow> matchC_MC WbisT t s"
and 
WbisT_matchT_MT_rev: "\<And> s t. s \<approx>wT t \<Longrightarrow> matchT_MT t s"
using WbisT_step WbisT_sym unfolding sym_def by blast+

lemmas WbisT_step_rev = WbisT_matchC_MC_rev WbisT_matchT_MT_rev 

lemma WbisT_coind:  
assumes "sym theta" and "theta \<subseteq> WretrT (theta \<union> WbisT)"
shows "theta \<subseteq> WbisT"
using assms mono_Retr bis_coind 
unfolding WbisT_def by blast

lemma WbisT_raw_coind:  
assumes "sym theta" and "theta \<subseteq> WretrT theta"
shows "theta \<subseteq> WbisT"
using assms mono_Retr bis_raw_coind 
unfolding WbisT_def by blast

lemma WbisT_coind2:
assumes "theta \<subseteq> WretrT (theta \<union> WbisT)" and 
"theta ^-1 \<subseteq> WretrT ((theta ^-1) \<union> WbisT)"
shows "theta \<subseteq> WbisT"
using assms mono_Retr bis_coind2 
unfolding WbisT_def by blast

lemma WbisT_raw_coind2:
assumes "theta \<subseteq> WretrT theta" and 
"theta ^-1 \<subseteq> WretrT (theta ^-1)"
shows "theta \<subseteq> WbisT"
using assms mono_Retr bis_raw_coind2 
unfolding WbisT_def by blast

lemma WbisT_coinduct[consumes 1, case_names sym cont termi]:
  assumes \<phi>: "\<phi> c d"
  assumes S: "\<And>c d. \<phi> c d \<Longrightarrow> \<phi> d c"
  assumes C: "\<And>c s d t c' s'.
    \<lbrakk> \<phi> c d ; s \<approx> t ; (c, s) \<rightarrow>c (c', s') \<rbrakk> \<Longrightarrow> \<exists>d' t'. (d, t) \<rightarrow>*c (d', t') \<and> s' \<approx> t' \<and> (\<phi> c' d' \<or> c' \<approx>wT d')"
  assumes T: "\<And>c s d t s'.
    \<lbrakk> \<phi> c d ; s \<approx> t ; (c, s) \<rightarrow>t s' \<rbrakk> \<Longrightarrow> \<exists>t'. (d, t) \<rightarrow>*t t' \<and> s' \<approx> t'"
  shows "c \<approx>wT d"
proof -
  let ?\<theta> = "{(c, d). \<phi> c d}"
  have "sym ?\<theta>" by (auto intro!: symI S)
  moreover 
  have "?\<theta> \<subseteq> WretrT (?\<theta> \<union> WbisT)"
    using C T by (auto simp: WretrT_def matchC_MC_def matchT_MT_def)
  ultimately have "?\<theta> \<subseteq> WbisT"
    using WbisT_coind by auto
  with \<phi> show ?thesis
    by auto
qed

(* BisT: *)
lemma BisT_prefix:
"BisT \<subseteq> RetrT BisT"
unfolding BisT_def using mono_Retr bis_prefix by blast

lemma BisT_sym: "sym BisT"
unfolding BisT_def using mono_Retr sym_bis by blast

lemma BisT_Sym: "c \<approx>T d \<Longrightarrow> d \<approx>T c"
using BisT_sym unfolding sym_def by blast

lemma BisT_converse:
"((c,d) \<in> theta^-1 \<union> BisT) = ((d,c) \<in> theta \<union> BisT)"
by (metis BisT_sym converseI converse_Un converse_converse sym_conv_converse_eq)

lemma
BisT_matchC_TMC: "\<And> c d. c \<approx>T d \<Longrightarrow> matchC_TMC BisT c d"
and 
BisT_matchT_TMT: "\<And> c d. c \<approx>T d \<Longrightarrow> matchT_TMT c d"
using BisT_prefix unfolding RetrT_def by auto

lemmas BisT_step = BisT_matchC_TMC BisT_matchT_TMT

lemma
BisT_matchC_TMC_rev: "\<And> c d. c \<approx>T d \<Longrightarrow> matchC_TMC BisT d c"
and 
BisT_matchT_TMT_rev: "\<And> c d. c \<approx>T d \<Longrightarrow> matchT_TMT d c"
using BisT_step BisT_sym unfolding sym_def by blast+

lemmas BisT_step_rev = BisT_matchC_TMC_rev BisT_matchT_TMT_rev 

lemma BisT_coind:  
assumes "sym theta" and "theta \<subseteq> RetrT (theta \<union> BisT)"
shows "theta \<subseteq> BisT"
using assms mono_Retr bis_coind 
unfolding BisT_def by blast

lemma BisT_raw_coind:  
assumes "sym theta" and "theta \<subseteq> RetrT theta"
shows "theta \<subseteq> BisT"
using assms mono_Retr bis_raw_coind 
unfolding BisT_def by blast

lemma BisT_coind2:
assumes "theta \<subseteq> RetrT (theta \<union> BisT)" and 
"theta ^-1 \<subseteq> RetrT ((theta ^-1) \<union> BisT)"
shows "theta \<subseteq> BisT"
using assms mono_Retr bis_coind2 
unfolding BisT_def by blast

lemma BisT_raw_coind2:
assumes "theta \<subseteq> RetrT theta" and 
"theta ^-1 \<subseteq> RetrT (theta ^-1)"
shows "theta \<subseteq> BisT"
using assms mono_Retr bis_raw_coind2 
unfolding BisT_def by blast

text\<open>Inclusions between bisimilarities:\<close>

lemma match_imp[simp]:
"\<And> theta c1 c2. matchC_C theta c1 c2 \<Longrightarrow> matchC_ZOC theta c1 c2"
(*  *)
"\<And> theta c1 c2. matchC_ZOC theta c1 c2 \<Longrightarrow> matchC_ZO theta c1 c2"
(*  *)
"\<And> theta c1 c2. matchC_ZOC theta c1 c2 \<Longrightarrow> matchC_MC theta c1 c2"
(*  *)
"\<And> theta c1 c2. matchC_ZO theta c1 c2 \<Longrightarrow> matchC_M theta c1 c2"
(*  *)
"\<And> theta c1 c2. matchC_MC theta c1 c2 \<Longrightarrow> matchC_M theta c1 c2"
(*  *)
(*  *)
"\<And> c1 c2. matchT_T c1 c2 \<Longrightarrow> matchT_ZO c1 c2"
(*  *)
"\<And> c1 c2. matchT_T c1 c2 \<Longrightarrow> matchT_MT c1 c2"
(*  *)
"\<And> c1 c2. matchT_ZO c1 c2 \<Longrightarrow> matchT_M c1 c2"
(*  *)
"\<And> c1 c2. matchT_MT c1 c2 \<Longrightarrow> matchT_M c1 c2"
(*  *)
"\<And> theta c1 c2. matchC_MC theta c1 c2 \<Longrightarrow> matchC_TMC theta c1 c2"
(*  *)
"\<And> theta c1 c2. matchT_MT c1 c2 \<Longrightarrow> matchT_TMT c1 c2"
unfolding match_defs apply(tactic \<open>mauto_no_simp_tac @{context}\<close>)
apply fastforce apply fastforce
apply (metis MtransC_Refl transC_MtransC)
by force+

lemma Retr_incl:
"\<And>theta. Sretr theta \<subseteq> ZOretrT theta"
(*  *)
"\<And>theta. ZOretrT theta \<subseteq> ZOretr theta"
(*  *)
"\<And>theta. ZOretrT theta \<subseteq> WretrT theta"
(*  *)
"\<And>theta. ZOretr theta \<subseteq> Wretr theta"
(*  *)
"\<And>theta. WretrT theta \<subseteq> Wretr theta"
(*  *)
"\<And>theta. WretrT theta \<subseteq> RetrT theta"
unfolding Retr_defs by auto

lemma bis_incl:
"Sbis \<subseteq> ZObisT"
(*  *)
"ZObisT \<subseteq> ZObis"
(*  *)
"ZObisT \<subseteq> WbisT"
(*  *)
"ZObis \<subseteq> Wbis"
(*  *)
"WbisT \<subseteq> Wbis"
(*  *)
"WbisT \<subseteq> BisT"
unfolding bis_defs 
using Retr_incl mono_bis mono_Retr by blast+

lemma bis_imp[simp]:
"\<And> c1 c2. c1 \<approx>s c2 \<Longrightarrow> c1 \<approx>01T c2"
(*  *)
"\<And> c1 c2. c1 \<approx>01T c2 \<Longrightarrow> c1 \<approx>01 c2"
(*  *)
"\<And> c1 c2. c1 \<approx>01T c2 \<Longrightarrow> c1 \<approx>wT c2"
(*  *)
"\<And> c1 c2. c1 \<approx>01 c2 \<Longrightarrow> c1 \<approx>w c2"
(*  *)
"\<And> c1 c2. c1 \<approx>wT c2 \<Longrightarrow> c1 \<approx>w c2"
(*  *)
"\<And> c1 c2. c1 \<approx>wT c2 \<Longrightarrow> c1 \<approx>T c2"
using bis_incl rev_subsetD by auto

text\<open>Self-isomorphism implies strong bisimilarity:\<close>

lemma siso_Sbis[simp]:
assumes "siso c"
shows "c \<approx>s c"
proof-
  let ?theta = "{(c,c) | c . siso c}"
  have "?theta \<subseteq> Sbis"
  proof(rule Sbis_raw_coind)
    show "sym ?theta" unfolding sym_def by blast
  next
    show "?theta \<subseteq> Sretr ?theta"
    proof clarify
      fix c assume c: "siso c"
      show "(c, c) \<in> Sretr ?theta"
      unfolding Sretr_def proof (clarify, intro conjI)
        show "matchC_C ?theta c c"
        unfolding matchC_C_def apply simp
        by (metis c siso_transC siso_transC_indis)
      next
        show "matchT_T c c"
        unfolding matchT_T_def
        by (metis c siso_transT)           
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

text\<open>0-Self-isomorphism implies weak T 0-bisimilarity:\<close>

lemma siso0_Sbis[simp]:
assumes "siso0 c"
shows "c \<approx>T c"
proof-
  let ?theta = "{(c,c) | c . siso0 c}"
  have "?theta \<subseteq> BisT"
  proof(rule BisT_raw_coind)
    show "sym ?theta" unfolding sym_def by blast
  next
    show "?theta \<subseteq> RetrT ?theta"
    proof clarify
      fix c assume c: "siso0 c"
      show "(c, c) \<in> RetrT ?theta"
      unfolding RetrT_def proof (clarify, intro conjI)
        show "matchC_TMC ?theta c c"
        unfolding matchC_TMC_def apply simp
        by (metis c siso0_transC siso0_transC_indis transC_MtransC)
      next
        show "matchT_TMT c c"
        unfolding matchC_TMC_def
        by (metis c matchT_TMT_def siso0_transT transT_MtransT)
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed
 

end 
(* context PL_Indis *)


end
