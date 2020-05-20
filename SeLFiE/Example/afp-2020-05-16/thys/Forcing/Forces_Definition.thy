section\<open>The definition of \<^term>\<open>forces\<close>\<close>
theory Forces_Definition imports Arities FrecR Synthetic_Definition begin

text\<open>This is the core of our development.\<close>

subsection\<open>The relation \<^term>\<open>frecrel\<close>\<close>

definition
  frecrelP :: "[i\<Rightarrow>o,i] \<Rightarrow> o" where
  "frecrelP(M,xy) \<equiv> (\<exists>x[M]. \<exists>y[M]. pair(M,x,y,xy) \<and> is_frecR(M,x,y))"

definition
  frecrelP_fm :: "i \<Rightarrow> i" where
  "frecrelP_fm(a) \<equiv> Exists(Exists(And(pair_fm(1,0,a#+2),frecR_fm(1,0))))"

lemma arity_frecrelP_fm :
  "a\<in>nat \<Longrightarrow> arity(frecrelP_fm(a)) = succ(a)"
  unfolding frecrelP_fm_def
  using arity_frecR_fm arity_pair_fm pred_Un_distrib
  by simp

lemma frecrelP_fm_type[TC] :
  "a\<in>nat \<Longrightarrow> frecrelP_fm(a)\<in>formula"
  unfolding frecrelP_fm_def by simp

lemma sats_frecrelP_fm :
  assumes "a\<in>nat" "env\<in>list(A)"
  shows "sats(A,frecrelP_fm(a),env) \<longleftrightarrow> frecrelP(##A,nth(a, env))"
  unfolding frecrelP_def frecrelP_fm_def
  using assms by (auto simp add:frecR_fm_iff_sats[symmetric])

lemma frecrelP_iff_sats:
  assumes
    "nth(a,env) = aa" "a\<in> nat"  "env \<in> list(A)"
  shows
    "frecrelP(##A,aa)  \<longleftrightarrow> sats(A, frecrelP_fm(a), env)"
  using assms
  by (simp add:sats_frecrelP_fm)

definition
  is_frecrel :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
  "is_frecrel(M,A,r) \<equiv> \<exists>A2[M]. cartprod(M,A,A,A2) \<and> is_Collect(M,A2, frecrelP(M) ,r)"

definition
  frecrel_fm :: "[i,i] \<Rightarrow> i" where
  "frecrel_fm(a,r) \<equiv> Exists(And(cartprod_fm(a#+1,a#+1,0),Collect_fm(0,frecrelP_fm(0),r#+1)))"

lemma frecrel_fm_type[TC] :
  "\<lbrakk>a\<in>nat;b\<in>nat\<rbrakk> \<Longrightarrow> frecrel_fm(a,b)\<in>formula"
  unfolding frecrel_fm_def by simp

lemma arity_frecrel_fm :
  assumes "a\<in>nat"  "b\<in>nat"
  shows "arity(frecrel_fm(a,b)) = succ(a) \<union> succ(b)"
  unfolding frecrel_fm_def
  using assms arity_Collect_fm arity_cartprod_fm arity_frecrelP_fm pred_Un_distrib
  by auto

lemma sats_frecrel_fm :
  assumes
    "a\<in>nat"  "r\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,frecrel_fm(a,r),env)
    \<longleftrightarrow> is_frecrel(##A,nth(a, env),nth(r, env))"
  unfolding is_frecrel_def frecrel_fm_def
  using assms
  by (simp add:sats_Collect_fm sats_frecrelP_fm)

lemma is_frecrel_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(r,env) = rr" "a\<in> nat"  "r\<in> nat"  "env \<in> list(A)"
  shows
    "is_frecrel(##A, aa,rr) \<longleftrightarrow> sats(A, frecrel_fm(a,r), env)"
  using assms
  by (simp add:sats_frecrel_fm)

definition
  names_below :: "i \<Rightarrow> i \<Rightarrow> i" where
  "names_below(P,x) \<equiv> 2\<times>ecloseN(x)\<times>ecloseN(x)\<times>P"

lemma names_belowsD:
  assumes "x \<in> names_below(P,z)"
  obtains f n1 n2 p where
    "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>P"
  using assms unfolding names_below_def by auto


definition
  is_names_below :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_names_below(M,P,x,nb) \<equiv> \<exists>p1[M]. \<exists>p0[M]. \<exists>t[M]. \<exists>ec[M].
              is_ecloseN(M,ec,x) \<and> number2(M,t) \<and> cartprod(M,ec,P,p0) \<and> cartprod(M,ec,p0,p1)
              \<and> cartprod(M,t,p1,nb)"

definition
  number2_fm :: "i\<Rightarrow>i" where
  "number2_fm(a) \<equiv> Exists(And(number1_fm(0), succ_fm(0,succ(a))))"

lemma number2_fm_type[TC] :
  "a\<in>nat \<Longrightarrow> number2_fm(a) \<in> formula"
  unfolding number2_fm_def by simp

lemma number2arity__fm :
  "a\<in>nat \<Longrightarrow> arity(number2_fm(a)) = succ(a)"
  unfolding number2_fm_def
  using number1arity__fm arity_succ_fm nat_union_abs2 pred_Un_distrib
  by simp

lemma sats_number2_fm [simp]:
  "\<lbrakk> x \<in> nat; env \<in> list(A) \<rbrakk>
    \<Longrightarrow> sats(A, number2_fm(x), env) \<longleftrightarrow> number2(##A, nth(x,env))"
  by (simp add: number2_fm_def number2_def)

definition
  is_names_below_fm :: "[i,i,i] \<Rightarrow> i" where
  "is_names_below_fm(P,x,nb) \<equiv> Exists(Exists(Exists(Exists(
                    And(ecloseN_fm(0,x #+ 4),And(number2_fm(1),
                    And(cartprod_fm(0,P #+ 4,2),And(cartprod_fm(0,2,3),cartprod_fm(1,3,nb#+4)))))))))"

lemma arity_is_names_below_fm :
  "\<lbrakk>P\<in>nat;x\<in>nat;nb\<in>nat\<rbrakk> \<Longrightarrow> arity(is_names_below_fm(P,x,nb)) = succ(P) \<union> succ(x) \<union> succ(nb)"
  unfolding is_names_below_fm_def
  using arity_cartprod_fm number2arity__fm arity_ecloseN_fm nat_union_abs2 pred_Un_distrib
  by auto


lemma is_names_below_fm_type[TC]:
  "\<lbrakk>P\<in>nat;x\<in>nat;nb\<in>nat\<rbrakk> \<Longrightarrow> is_names_below_fm(P,x,nb)\<in>formula"
  unfolding is_names_below_fm_def by simp

lemma sats_is_names_below_fm :
  assumes
    "P\<in>nat" "x\<in>nat" "nb\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,is_names_below_fm(P,x,nb),env)
    \<longleftrightarrow> is_names_below(##A,nth(P, env),nth(x, env),nth(nb, env))"
  unfolding is_names_below_fm_def is_names_below_def using assms by simp

definition
  is_tuple :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_tuple(M,z,t1,t2,p,t) \<equiv> \<exists>t1t2p[M]. \<exists>t2p[M]. pair(M,t2,p,t2p) \<and> pair(M,t1,t2p,t1t2p) \<and>
                                                  pair(M,z,t1t2p,t)"


definition
  is_tuple_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "is_tuple_fm(z,t1,t2,p,tup) = Exists(Exists(And(pair_fm(t2 #+ 2,p #+ 2,0),
                      And(pair_fm(t1 #+ 2,0,1),pair_fm(z #+ 2,1,tup #+ 2)))))"


lemma arity_is_tuple_fm : "\<lbrakk> z\<in>nat ; t1\<in>nat ; t2\<in>nat ; p\<in>nat ; tup\<in>nat \<rbrakk> \<Longrightarrow>
  arity(is_tuple_fm(z,t1,t2,p,tup)) = \<Union> {succ(z),succ(t1),succ(t2),succ(p),succ(tup)}"
  unfolding is_tuple_fm_def
  using arity_pair_fm nat_union_abs1 nat_union_abs2 pred_Un_distrib
  by auto

lemma is_tuple_fm_type[TC] :
  "z\<in>nat \<Longrightarrow> t1\<in>nat \<Longrightarrow> t2\<in>nat \<Longrightarrow> p\<in>nat \<Longrightarrow> tup\<in>nat \<Longrightarrow> is_tuple_fm(z,t1,t2,p,tup)\<in>formula"
  unfolding is_tuple_fm_def by simp

lemma sats_is_tuple_fm :
  assumes
    "z\<in>nat"  "t1\<in>nat" "t2\<in>nat" "p\<in>nat" "tup\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,is_tuple_fm(z,t1,t2,p,tup),env)
    \<longleftrightarrow> is_tuple(##A,nth(z, env),nth(t1, env),nth(t2, env),nth(p, env),nth(tup, env))"
  unfolding is_tuple_def is_tuple_fm_def using assms by simp

lemma is_tuple_iff_sats:
  assumes
    "nth(a,env) = aa" "nth(b,env) = bb" "nth(c,env) = cc" "nth(d,env) = dd" "nth(e,env) = ee"
    "a\<in>nat" "b\<in>nat" "c\<in>nat" "d\<in>nat" "e\<in>nat"  "env \<in> list(A)"
  shows
    "is_tuple(##A,aa,bb,cc,dd,ee)  \<longleftrightarrow> sats(A, is_tuple_fm(a,b,c,d,e), env)"
  using assms by (simp add: sats_is_tuple_fm)

subsection\<open>Definition of \<^term>\<open>forces\<close> for equality and membership\<close>

(* p ||- \<tau> = \<theta> \<equiv>
  \<forall>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<longrightarrow> (\<forall>q\<in>P. \<langle>q,p\<rangle>\<in>leq \<longrightarrow> ((q ||- \<sigma>\<in>\<tau>) \<longleftrightarrow> (q ||- \<sigma>\<in>\<theta>)) ) *)
definition
  eq_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "eq_case(t1,t2,p,P,leq,f) \<equiv> \<forall>s. s\<in>domain(t1) \<union> domain(t2) \<longrightarrow>
      (\<forall>q. q\<in>P \<and> \<langle>q,p\<rangle>\<in>leq \<longrightarrow> (f`\<langle>1,s,t1,q\<rangle>=1  \<longleftrightarrow> f`\<langle>1,s,t2,q\<rangle> =1))"


definition
  is_eq_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_eq_case(M,t1,t2,p,P,leq,f) \<equiv>
   \<forall>s[M]. (\<exists>d[M]. is_domain(M,t1,d) \<and> s\<in>d) \<or> (\<exists>d[M]. is_domain(M,t2,d) \<and> s\<in>d)
       \<longrightarrow> (\<forall>q[M]. q\<in>P \<and> (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>leq) \<longrightarrow>
            (\<exists>ost1q[M]. \<exists>ost2q[M]. \<exists>o[M].  \<exists>vf1[M]. \<exists>vf2[M].
             is_tuple(M,o,s,t1,q,ost1q) \<and>
             is_tuple(M,o,s,t2,q,ost2q) \<and> number1(M,o) \<and>
             fun_apply(M,f,ost1q,vf1) \<and> fun_apply(M,f,ost2q,vf2) \<and>
             (vf1 = o \<longleftrightarrow> vf2 = o)))"

(* p ||-
   \<pi> \<in> \<tau> \<equiv> \<forall>v\<in>P. \<langle>v,p\<rangle>\<in>leq \<longrightarrow> (\<exists>q\<in>P. \<langle>q,v\<rangle>\<in>leq \<and> (\<exists>\<sigma>. \<exists>r\<in>P. \<langle>\<sigma>,r\<rangle>\<in>\<tau> \<and> \<langle>q,r\<rangle>\<in>leq \<and>  q ||- \<pi> = \<sigma>)) *)
definition
  mem_case :: "[i,i,i,i,i,i] \<Rightarrow> o" where
  "mem_case(t1,t2,p,P,leq,f) \<equiv> \<forall>v\<in>P. \<langle>v,p\<rangle>\<in>leq \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> \<langle>q,v\<rangle>\<in>leq \<and> \<langle>s,r\<rangle> \<in> t2 \<and> \<langle>q,r\<rangle>\<in>leq \<and>  f`\<langle>0,t1,s,q\<rangle> = 1)"

definition
  is_mem_case :: "[i\<Rightarrow>o,i,i,i,i,i,i] \<Rightarrow> o" where
  "is_mem_case(M,t1,t2,p,P,leq,f) \<equiv> \<forall>v[M]. \<forall>vp[M]. v\<in>P \<and> pair(M,v,p,vp) \<and> vp\<in>leq \<longrightarrow>
    (\<exists>q[M]. \<exists>s[M]. \<exists>r[M]. \<exists>qv[M]. \<exists>sr[M]. \<exists>qr[M]. \<exists>z[M]. \<exists>zt1sq[M]. \<exists>o[M].
     r\<in> P \<and> q\<in>P \<and> pair(M,q,v,qv) \<and> pair(M,s,r,sr) \<and> pair(M,q,r,qr) \<and>
     empty(M,z) \<and> is_tuple(M,z,t1,s,q,zt1sq) \<and>
     number1(M,o) \<and> qv\<in>leq \<and> sr\<in>t2 \<and> qr\<in>leq \<and> fun_apply(M,f,zt1sq,o))"


schematic_goal sats_is_mem_case_fm_auto:
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_mem_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?imc_fm(n1,n2,p,P,leq,f),env)"
  unfolding is_mem_case_def
  by (insert assms ; (rule sep_rules'  is_tuple_iff_sats | simp)+)


synthesize "mem_case_fm" from_schematic sats_is_mem_case_fm_auto

lemma arity_mem_case_fm :
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat"
  shows
    "arity(mem_case_fm(n1,n2,p,P,leq,f)) =
    succ(n1) \<union> succ(n2) \<union> succ(p) \<union> succ(P) \<union> succ(leq) \<union> succ(f)"
  unfolding mem_case_fm_def
  using assms arity_pair_fm arity_is_tuple_fm number1arity__fm arity_fun_apply_fm arity_empty_fm
    pred_Un_distrib
  by auto

schematic_goal sats_is_eq_case_fm_auto:
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "is_eq_case(##A, nth(n1, env),nth(n2, env),nth(p, env),nth(P, env), nth(leq, env),nth(f,env))
    \<longleftrightarrow> sats(A,?iec_fm(n1,n2,p,P,leq,f),env)"
  unfolding is_eq_case_def
  by (insert assms ; (rule sep_rules'  is_tuple_iff_sats | simp)+)

synthesize "eq_case_fm" from_schematic sats_is_eq_case_fm_auto

lemma arity_eq_case_fm :
  assumes
    "n1\<in>nat" "n2\<in>nat" "p\<in>nat" "P\<in>nat" "leq\<in>nat" "f\<in>nat"
  shows
    "arity(eq_case_fm(n1,n2,p,P,leq,f)) =
    succ(n1) \<union> succ(n2) \<union> succ(p) \<union> succ(P) \<union> succ(leq) \<union> succ(f)"
  unfolding eq_case_fm_def
  using assms arity_pair_fm arity_is_tuple_fm number1arity__fm arity_fun_apply_fm arity_empty_fm
    arity_domain_fm pred_Un_distrib
  by auto

definition
  Hfrc :: "[i,i,i,i] \<Rightarrow> o" where
  "Hfrc(P,leq,fnnc,f) \<equiv> \<exists>ft. \<exists>n1. \<exists>n2. \<exists>c. c\<in>P \<and> fnnc = \<langle>ft,n1,n2,c\<rangle> \<and>
     (  ft = 0 \<and>  eq_case(n1,n2,c,P,leq,f)
      \<or> ft = 1 \<and> mem_case(n1,n2,c,P,leq,f))"

definition
  is_Hfrc :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc(M,P,leq,fnnc,f) \<equiv>
     \<exists>ft[M]. \<exists>n1[M]. \<exists>n2[M]. \<exists>co[M].
      co\<in>P \<and> is_tuple(M,ft,n1,n2,co,fnnc) \<and>
      (  (empty(M,ft) \<and> is_eq_case(M,n1,n2,co,P,leq,f))
       \<or> (number1(M,ft) \<and>  is_mem_case(M,n1,n2,co,P,leq,f)))"

definition
  Hfrc_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "Hfrc_fm(P,leq,fnnc,f) \<equiv>
    Exists(Exists(Exists(Exists(
      And(Member(0,P #+ 4),And(is_tuple_fm(3,2,1,0,fnnc #+ 4),
      Or(And(empty_fm(3),eq_case_fm(2,1,0,P #+ 4,leq #+ 4,f #+ 4)),
         And(number1_fm(3),mem_case_fm(2,1,0,P #+ 4,leq #+ 4,f #+ 4)))))))))"

lemma Hfrc_fm_type[TC] :
  "\<lbrakk>P\<in>nat;leq\<in>nat;fnnc\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> Hfrc_fm(P,leq,fnnc,f)\<in>formula"
  unfolding Hfrc_fm_def by simp

lemma arity_Hfrc_fm :
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat"
  shows
    "arity(Hfrc_fm(P,leq,fnnc,f)) = succ(P) \<union> succ(leq) \<union> succ(fnnc) \<union> succ(f)"
  unfolding Hfrc_fm_def
  using assms arity_is_tuple_fm arity_mem_case_fm arity_eq_case_fm
    arity_empty_fm number1arity__fm pred_Un_distrib
  by auto

lemma sats_Hfrc_fm:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,Hfrc_fm(P,leq,fnnc,f),env)
    \<longleftrightarrow> is_Hfrc(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env))"
  unfolding is_Hfrc_def Hfrc_fm_def
  using assms  
  by (simp add: sats_is_tuple_fm eq_case_fm_iff_sats[symmetric] mem_case_fm_iff_sats[symmetric])

lemma Hfrc_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "env\<in>list(A)"
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc" "nth(f,env) = ff"
  shows
    "is_Hfrc(##A, PP, lleq,ffnnc,ff)
    \<longleftrightarrow> sats(A,Hfrc_fm(P,leq,fnnc,f),env)"
  using assms
  by (simp add:sats_Hfrc_fm)

definition
  is_Hfrc_at :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_Hfrc_at(M,P,leq,fnnc,f,z) \<equiv>
            (empty(M,z) \<and> \<not> is_Hfrc(M,P,leq,fnnc,f))
          \<or> (number1(M,z) \<and> is_Hfrc(M,P,leq,fnnc,f))"

definition
  Hfrc_at_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "Hfrc_at_fm(P,leq,fnnc,f,z) \<equiv> Or(And(empty_fm(z),Neg(Hfrc_fm(P,leq,fnnc,f))),
                                      And(number1_fm(z),Hfrc_fm(P,leq,fnnc,f)))"

lemma arity_Hfrc_at_fm :
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat"
  shows
    "arity(Hfrc_at_fm(P,leq,fnnc,f,z)) = succ(P) \<union> succ(leq) \<union> succ(fnnc) \<union> succ(f) \<union> succ(z)"
  unfolding Hfrc_at_fm_def
  using assms arity_Hfrc_fm arity_empty_fm number1arity__fm pred_Un_distrib
  by auto


lemma Hfrc_at_fm_type[TC] :
  "\<lbrakk>P\<in>nat;leq\<in>nat;fnnc\<in>nat;f\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> Hfrc_at_fm(P,leq,fnnc,f,z)\<in>formula"
  unfolding Hfrc_at_fm_def by simp

lemma sats_Hfrc_at_fm:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,Hfrc_at_fm(P,leq,fnnc,f,z),env)
    \<longleftrightarrow> is_Hfrc_at(##A,nth(P, env), nth(leq, env), nth(fnnc, env),nth(f, env),nth(z, env))"
  unfolding is_Hfrc_at_def Hfrc_at_fm_def using assms sats_Hfrc_fm
  by simp

lemma is_Hfrc_at_iff_sats:
  assumes
    "P\<in>nat" "leq\<in>nat" "fnnc\<in>nat" "f\<in>nat" "z\<in>nat" "env\<in>list(A)"
    "nth(P,env) = PP"  "nth(leq,env) = lleq" "nth(fnnc,env) = ffnnc"
    "nth(f,env) = ff" "nth(z,env) = zz"
  shows
    "is_Hfrc_at(##A, PP, lleq,ffnnc,ff,zz)
    \<longleftrightarrow> sats(A,Hfrc_at_fm(P,leq,fnnc,f,z),env)"
  using assms by (simp add:sats_Hfrc_at_fm)

lemma arity_tran_closure_fm :
  "\<lbrakk>x\<in>nat;f\<in>nat\<rbrakk> \<Longrightarrow> arity(trans_closure_fm(x,f)) = succ(x) \<union> succ(f)"
  unfolding trans_closure_fm_def
  using arity_omega_fm arity_field_fm arity_typed_function_fm arity_pair_fm arity_empty_fm arity_fun_apply_fm
    arity_composition_fm arity_succ_fm nat_union_abs2 pred_Un_distrib 
  by auto

subsection\<open>The well-founded relation \<^term>\<open>forcerel\<close>\<close>
definition
  forcerel :: "i \<Rightarrow> i \<Rightarrow> i" where
  "forcerel(P,x) \<equiv> frecrel(names_below(P,x))^+"

definition
  is_forcerel :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_forcerel(M,P,x,z) \<equiv> \<exists>r[M]. \<exists>nb[M]. tran_closure(M,r,z) \<and>
                        (is_names_below(M,P,x,nb) \<and> is_frecrel(M,nb,r))"

definition
  forcerel_fm :: "i\<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "forcerel_fm(p,x,z) \<equiv> Exists(Exists(And(trans_closure_fm(1, z#+2),
                                        And(is_names_below_fm(p#+2,x#+2,0),frecrel_fm(0,1)))))"

lemma arity_forcerel_fm:
  "\<lbrakk>p\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> arity(forcerel_fm(p,x,z)) = succ(p) \<union> succ(x) \<union> succ(z)"
  unfolding forcerel_fm_def
  using arity_frecrel_fm arity_tran_closure_fm arity_is_names_below_fm pred_Un_distrib
  by auto

lemma forcerel_fm_type[TC]:
  "\<lbrakk>p\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> forcerel_fm(p,x,z)\<in>formula"
  unfolding forcerel_fm_def by simp


lemma sats_forcerel_fm:
  assumes
    "p\<in>nat" "x\<in>nat"  "z\<in>nat" "env\<in>list(A)"
  shows
    "sats(A,forcerel_fm(p,x,z),env) \<longleftrightarrow> is_forcerel(##A,nth(p,env),nth(x, env),nth(z, env))"
proof -
  have "sats(A,trans_closure_fm(1,z #+ 2),Cons(nb,Cons(r,env))) \<longleftrightarrow>
        tran_closure(##A, r, nth(z, env))" if "r\<in>A" "nb\<in>A" for r nb
    using that assms trans_closure_fm_iff_sats[of 1 "[nb,r]@env" _ "z#+2",symmetric] by simp
  moreover
  have "sats(A, is_names_below_fm(succ(succ(p)), succ(succ(x)), 0), Cons(nb, Cons(r, env))) \<longleftrightarrow>
        is_names_below(##A, nth(p,env), nth(x, env), nb)"
    if "r\<in>A" "nb\<in>A" for nb r
    using assms that sats_is_names_below_fm[of "p #+ 2" "x #+ 2" 0 "[nb,r]@env"] by simp
  moreover
  have "sats(A, frecrel_fm(0, 1), Cons(nb, Cons(r, env))) \<longleftrightarrow>
        is_frecrel(##A, nb, r)"
    if "r\<in>A" "nb\<in>A" for r nb
    using assms that sats_frecrel_fm[of 0 1 "[nb,r]@env"] by simp
  ultimately
  show ?thesis using assms unfolding is_forcerel_def forcerel_fm_def by simp
qed

subsection\<open>\<^term>\<open>frc_at\<close>, forcing for atomic formulas\<close>
definition
  frc_at :: "[i,i,i] \<Rightarrow> i" where
  "frc_at(P,leq,fnnc) \<equiv> wfrec(frecrel(names_below(P,fnnc)),fnnc,
                              \<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"

definition
  is_frc_at :: "[i\<Rightarrow>o,i,i,i,i] \<Rightarrow> o" where
  "is_frc_at(M,P,leq,x,z) \<equiv> \<exists>r[M]. is_forcerel(M,P,x,r) \<and>
                                    is_wfrec(M,is_Hfrc_at(M,P,leq),r,x,z)"

definition
  frc_at_fm :: "[i,i,i,i] \<Rightarrow> i" where
  "frc_at_fm(p,l,x,z) \<equiv> Exists(And(forcerel_fm(succ(p),succ(x),0),
          is_wfrec_fm(Hfrc_at_fm(6#+p,6#+l,2,1,0),0,succ(x),succ(z))))"

lemma frc_at_fm_type [TC] :
  "\<lbrakk>p\<in>nat;l\<in>nat;x\<in>nat;z\<in>nat\<rbrakk> \<Longrightarrow> frc_at_fm(p,l,x,z)\<in>formula"
  unfolding frc_at_fm_def by simp

lemma arity_frc_at_fm :
  assumes "p\<in>nat" "l\<in>nat" "x\<in>nat" "z\<in>nat"
  shows "arity(frc_at_fm(p,l,x,z)) = succ(p) \<union> succ(l) \<union> succ(x) \<union> succ(z)"
proof -
  let ?\<phi> = "Hfrc_at_fm(6 #+ p, 6 #+ l, 2, 1, 0)"
  from assms
  have  "arity(?\<phi>) = (7#+p) \<union> (7#+l)" "?\<phi> \<in> formula"
    using arity_Hfrc_at_fm nat_simp_union
    by auto
  with assms
  have W: "arity(is_wfrec_fm(?\<phi>, 0, succ(x), succ(z))) = 2#+p \<union> (2#+l) \<union> (2#+x) \<union> (2#+z)"
    using arity_is_wfrec_fm[OF \<open>?\<phi>\<in>_\<close> _ _ _ _ \<open>arity(?\<phi>) = _\<close>] pred_Un_distrib pred_succ_eq
      nat_union_abs1
    by auto
  from assms
  have "arity(forcerel_fm(succ(p),succ(x),0)) = succ(succ(p)) \<union> succ(succ(x))"
    using arity_forcerel_fm nat_simp_union
    by auto
  with W assms
  show ?thesis
    unfolding frc_at_fm_def
    using arity_forcerel_fm pred_Un_distrib
    by auto
qed

lemma sats_frc_at_fm :
  assumes
    "p\<in>nat" "l\<in>nat" "i\<in>nat" "j\<in>nat" "env\<in>list(A)" "i < length(env)" "j < length(env)"
  shows
    "sats(A,frc_at_fm(p,l,i,j),env) \<longleftrightarrow>
     is_frc_at(##A,nth(p,env),nth(l,env),nth(i,env),nth(j,env))"
proof -
  {
    fix r pp ll
    assume "r\<in>A"
    have 0:"is_Hfrc_at(##A,nth(p,env),nth(l,env),a2, a1, a0) \<longleftrightarrow>
         sats(A, Hfrc_at_fm(6#+p,6#+l,2,1,0), [a0,a1,a2,a3,a4,r]@env)"
      if "a0\<in>A" "a1\<in>A" "a2\<in>A" "a3\<in>A" "a4\<in>A" for a0 a1 a2 a3 a4
      using  that assms \<open>r\<in>A\<close>
        is_Hfrc_at_iff_sats[of "6#+p" "6#+l" 2 1 0 "[a0,a1,a2,a3,a4,r]@env" A]  by simp
    have "sats(A,is_wfrec_fm(Hfrc_at_fm(6 #+ p, 6 #+ l, 2, 1, 0), 0, succ(i), succ(j)),[r]@env) \<longleftrightarrow>
         is_wfrec(##A, is_Hfrc_at(##A, nth(p,env), nth(l,env)), r,nth(i, env), nth(j, env))"
      using assms \<open>r\<in>A\<close>
        sats_is_wfrec_fm[OF 0[simplified]]
      by simp
  }
  moreover
  have "sats(A, forcerel_fm(succ(p), succ(i), 0), Cons(r, env)) \<longleftrightarrow>
        is_forcerel(##A,nth(p,env),nth(i,env),r)" if "r\<in>A" for r
    using assms sats_forcerel_fm that by simp
  ultimately
  show ?thesis unfolding is_frc_at_def frc_at_fm_def
    using assms by simp
qed

definition
  forces_eq' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_eq'(P,l,p,t1,t2) \<equiv> frc_at(P,l,\<langle>0,t1,t2,p\<rangle>) = 1"

definition
  forces_mem' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_mem'(P,l,p,t1,t2) \<equiv> frc_at(P,l,\<langle>1,t1,t2,p\<rangle>) = 1"

definition
  forces_neq' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_neq'(P,l,p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. \<langle>q,p\<rangle>\<in>l \<and> forces_eq'(P,l,q,t1,t2))"

definition
  forces_nmem' :: "[i,i,i,i,i] \<Rightarrow> o" where
  "forces_nmem'(P,l,p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. \<langle>q,p\<rangle>\<in>l \<and> forces_mem'(P,l,q,t1,t2))"

definition
  is_forces_eq' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_eq'(M,P,l,p,t1,t2) \<equiv> \<exists>o[M]. \<exists>z[M]. \<exists>t[M]. number1(M,o) \<and> empty(M,z) \<and>
                                is_tuple(M,z,t1,t2,p,t) \<and> is_frc_at(M,P,l,t,o)"

definition
  is_forces_mem' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_mem'(M,P,l,p,t1,t2) \<equiv> \<exists>o[M]. \<exists>t[M]. number1(M,o) \<and>
                                is_tuple(M,o,t1,t2,p,t) \<and> is_frc_at(M,P,l,t,o)"

definition
  is_forces_neq' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_neq'(M,P,l,p,t1,t2) \<equiv>
      \<not> (\<exists>q[M]. q\<in>P \<and> (\<exists>qp[M]. pair(M,q,p,qp) \<and> qp\<in>l \<and> is_forces_eq'(M,P,l,q,t1,t2)))"

definition
  is_forces_nmem' :: "[i\<Rightarrow>o,i,i,i,i,i] \<Rightarrow> o" where
  "is_forces_nmem'(M,P,l,p,t1,t2) \<equiv>
      \<not> (\<exists>q[M]. \<exists>qp[M]. q\<in>P \<and> pair(M,q,p,qp) \<and> qp\<in>l \<and> is_forces_mem'(M,P,l,q,t1,t2))"

definition
  forces_eq_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_eq_fm(p,l,q,t1,t2) \<equiv>
     Exists(Exists(Exists(And(number1_fm(2),And(empty_fm(1),
              And(is_tuple_fm(1,t1#+3,t2#+3,q#+3,0),frc_at_fm(p#+3,l#+3,0,2) ))))))"

definition
  forces_mem_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_mem_fm(p,l,q,t1,t2) \<equiv> Exists(Exists(And(number1_fm(1),
                          And(is_tuple_fm(1,t1#+2,t2#+2,q#+2,0),frc_at_fm(p#+2,l#+2,0,1)))))"

definition
  forces_neq_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_neq_fm(p,l,q,t1,t2) \<equiv> Neg(Exists(Exists(And(Member(1,p#+2),
     And(pair_fm(1,q#+2,0),And(Member(0,l#+2),forces_eq_fm(p#+2,l#+2,1,t1#+2,t2#+2)))))))"

definition
  forces_nmem_fm :: "[i,i,i,i,i] \<Rightarrow> i" where
  "forces_nmem_fm(p,l,q,t1,t2) \<equiv> Neg(Exists(Exists(And(Member(1,p#+2),
     And(pair_fm(1,q#+2,0),And(Member(0,l#+2),forces_mem_fm(p#+2,l#+2,1,t1#+2,t2#+2)))))))"


lemma forces_eq_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_eq_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_eq_fm_def
  by simp

lemma forces_mem_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_mem_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_mem_fm_def
  by simp

lemma forces_neq_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_neq_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_neq_fm_def
  by simp

lemma forces_nmem_fm_type [TC]:
  "\<lbrakk> p\<in>nat;l\<in>nat;q\<in>nat;t1\<in>nat;t2\<in>nat\<rbrakk> \<Longrightarrow> forces_nmem_fm(p,l,q,t1,t2) \<in> formula"
  unfolding forces_nmem_fm_def
  by simp

lemma arity_forces_eq_fm :
  "p\<in>nat \<Longrightarrow> l\<in>nat \<Longrightarrow> q\<in>nat \<Longrightarrow> t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow>
   arity(forces_eq_fm(p,l,q,t1,t2)) = succ(t1) \<union> succ(t2) \<union> succ(q) \<union> succ(p) \<union> succ(l)"
  unfolding forces_eq_fm_def
  using number1arity__fm arity_empty_fm arity_is_tuple_fm arity_frc_at_fm
    pred_Un_distrib
  by auto

lemma arity_forces_mem_fm :
  "p\<in>nat \<Longrightarrow> l\<in>nat \<Longrightarrow> q\<in>nat \<Longrightarrow> t1 \<in> nat \<Longrightarrow> t2 \<in> nat \<Longrightarrow>
   arity(forces_mem_fm(p,l,q,t1,t2)) = succ(t1) \<union> succ(t2) \<union> succ(q) \<union> succ(p) \<union> succ(l)"
  unfolding forces_mem_fm_def
  using number1arity__fm arity_empty_fm arity_is_tuple_fm arity_frc_at_fm
    pred_Un_distrib
  by auto

lemma sats_forces_eq'_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
  shows "sats(M,forces_eq_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
         is_forces_eq'(##M,nth(p,env),nth(l,env),nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_eq_fm_def is_forces_eq'_def using assms sats_is_tuple_fm  sats_frc_at_fm
  by simp

lemma sats_forces_mem'_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
  shows "sats(M,forces_mem_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
             is_forces_mem'(##M,nth(p,env),nth(l,env),nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_mem_fm_def is_forces_mem'_def using assms sats_is_tuple_fm sats_frc_at_fm
  by simp

lemma sats_forces_neq'_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
  shows "sats(M,forces_neq_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
             is_forces_neq'(##M,nth(p,env),nth(l,env),nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_neq_fm_def is_forces_neq'_def
  using assms sats_forces_eq'_fm sats_is_tuple_fm sats_frc_at_fm
  by simp

lemma sats_forces_nmem'_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
  shows "sats(M,forces_nmem_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
             is_forces_nmem'(##M,nth(p,env),nth(l,env),nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_nmem_fm_def is_forces_nmem'_def
  using assms sats_forces_mem'_fm sats_is_tuple_fm sats_frc_at_fm
  by simp

context forcing_data
begin

(* Absoluteness of components *)
lemma fst_abs [simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_fst(##M,x,y) \<longleftrightarrow> y = fst(x)"
  unfolding fst_def is_fst_def using pair_in_M_iff zero_in_M
  by (auto;rule_tac the_0 the_0[symmetric],auto)

lemma snd_abs [simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_snd(##M,x,y) \<longleftrightarrow> y = snd(x)"
  unfolding snd_def is_snd_def using pair_in_M_iff zero_in_M
  by (auto;rule_tac the_0 the_0[symmetric],auto)

lemma ftype_abs[simp] :
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_ftype(##M,x,y) \<longleftrightarrow> y = ftype(x)" unfolding ftype_def  is_ftype_def by simp

lemma name1_abs[simp] :
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name1(##M,x,y) \<longleftrightarrow> y = name1(x)"
  unfolding name1_def is_name1_def
  by (rule hcomp_abs[OF fst_abs];simp_all add:fst_snd_closed)

lemma snd_snd_abs:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_snd_snd(##M,x,y) \<longleftrightarrow> y = snd(snd(x))"
  unfolding is_snd_snd_def
  by (rule hcomp_abs[OF snd_abs];simp_all add:fst_snd_closed)

lemma name2_abs[simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_name2(##M,x,y) \<longleftrightarrow> y = name2(x)"
  unfolding name2_def is_name2_def
  by (rule hcomp_abs[OF fst_abs snd_snd_abs];simp_all add:fst_snd_closed)

lemma cond_of_abs[simp]:
  "\<lbrakk>x\<in>M; y\<in>M \<rbrakk> \<Longrightarrow> is_cond_of(##M,x,y) \<longleftrightarrow> y = cond_of(x)"
  unfolding cond_of_def is_cond_of_def
  by (rule hcomp_abs[OF snd_abs snd_snd_abs];simp_all add:fst_snd_closed)

lemma tuple_abs[simp]:
  "\<lbrakk>z\<in>M;t1\<in>M;t2\<in>M;p\<in>M;t\<in>M\<rbrakk> \<Longrightarrow>
   is_tuple(##M,z,t1,t2,p,t) \<longleftrightarrow> t = \<langle>z,t1,t2,p\<rangle>"
  unfolding is_tuple_def using tuples_in_M by simp

lemma oneN_in_M[simp]: "1\<in>M"
  by (simp flip: setclass_iff)

lemma twoN_in_M : "2\<in>M"
  by (simp flip: setclass_iff)

lemma comp_in_M:
  "p \<preceq> q \<Longrightarrow> p\<in>M"
  "p \<preceq> q \<Longrightarrow> q\<in>M"
  using leq_in_M transitivity[of _ leq] pair_in_M_iff by auto

(* Absoluteness of Hfrc *)

lemma eq_case_abs [simp]:
  assumes
    "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M"
  shows
    "is_eq_case(##M,t1,t2,p,P,leq,f) \<longleftrightarrow> eq_case(t1,t2,p,P,leq,f)"
proof -
  have "q \<preceq> p \<Longrightarrow> q\<in>M" for q
    using comp_in_M by simp
  moreover
  have "\<langle>s,y\<rangle>\<in>t \<Longrightarrow> s\<in>domain(t)" if "t\<in>M" for s y t
    using that unfolding domain_def by auto
  ultimately
  have
    "(\<forall>s\<in>M. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q\<in>M. q\<in>P \<and> q \<preceq> p \<longrightarrow>
                              (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1))) \<longleftrightarrow>
    (\<forall>s. s \<in> domain(t1) \<or> s \<in> domain(t2) \<longrightarrow> (\<forall>q. q\<in>P \<and> q \<preceq> p \<longrightarrow>
                                  (f ` \<langle>1, s, t1, q\<rangle> =1 \<longleftrightarrow> f ` \<langle>1, s, t2, q\<rangle>=1)))"
    using assms domain_trans[OF trans_M,of t1]
      domain_trans[OF trans_M,of t2] by auto
  then show ?thesis
    unfolding eq_case_def is_eq_case_def
    using assms pair_in_M_iff n_in_M[of 1] domain_closed tuples_in_M
      apply_closed leq_in_M
    by simp
qed

lemma mem_case_abs [simp]:
  assumes
    "t1\<in>M" "t2\<in>M" "p\<in>M" "f\<in>M"
  shows
    "is_mem_case(##M,t1,t2,p,P,leq,f) \<longleftrightarrow> mem_case(t1,t2,p,P,leq,f)"
proof
  {
    fix v
    assume "v\<in>P" "v \<preceq> p" "is_mem_case(##M,t1,t2,p,P,leq,f)"
    moreover
    from this
    have "v\<in>M" "\<langle>v,p\<rangle> \<in> M" "(##M)(v)"
      using transitivity[OF _ P_in_M,of v] transitivity[OF _ leq_in_M]
      by simp_all
    moreover
    from calculation assms
    obtain q r s where
      "r \<in> P \<and> q \<in> P \<and> \<langle>q, v\<rangle> \<in> M \<and> \<langle>s, r\<rangle> \<in> M \<and> \<langle>q, r\<rangle> \<in> M \<and> 0 \<in> M \<and>
       \<langle>0, t1, s, q\<rangle> \<in> M \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      unfolding is_mem_case_def by auto
    then
    have "\<exists>q s r. r \<in> P \<and> q \<in> P \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      by auto
  }
  then
  show "mem_case(t1, t2, p, P, leq, f)" if "is_mem_case(##M, t1, t2, p, P, leq, f)"
    unfolding mem_case_def using that assms by auto
next
  { fix v
    assume "v \<in> M" "v \<in> P" "\<langle>v, p\<rangle> \<in> M" "v \<preceq> p" "mem_case(t1, t2, p, P, leq, f)"
    moreover
    from this
    obtain q s r where "r \<in> P \<and> q \<in> P \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      unfolding mem_case_def by auto
    moreover
    from this \<open>t2\<in>M\<close>
    have "r\<in>M" "q\<in>M" "s\<in>M" "r \<in> P \<and> q \<in> P \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      using transitivity P_in_M domain_closed[of t2] by auto
    moreover
    note \<open>t1\<in>M\<close>
    ultimately
    have "\<exists>q\<in>M . \<exists>s\<in>M. \<exists>r\<in>M.
         r \<in> P \<and> q \<in> P \<and> \<langle>q, v\<rangle> \<in> M \<and> \<langle>s, r\<rangle> \<in> M \<and> \<langle>q, r\<rangle> \<in> M \<and> 0 \<in> M \<and>
         \<langle>0, t1, s, q\<rangle> \<in> M \<and> q \<preceq> v \<and> \<langle>s, r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> f ` \<langle>0, t1, s, q\<rangle> = 1"
      using tuples_in_M zero_in_M by auto
  }
  then
  show "is_mem_case(##M, t1, t2, p, P, leq, f)" if "mem_case(t1, t2, p, P, leq, f)"
    unfolding is_mem_case_def using assms that by auto
qed


lemma Hfrc_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc(##M,P,leq,fnnc,f) \<longleftrightarrow> Hfrc(P,leq,fnnc,f)"
  unfolding is_Hfrc_def Hfrc_def using pair_in_M_iff
  by auto

lemma Hfrc_at_abs:
  "\<lbrakk>fnnc\<in>M; f\<in>M ; z\<in>M\<rbrakk> \<Longrightarrow>
   is_Hfrc_at(##M,P,leq,fnnc,f,z) \<longleftrightarrow>  z = bool_of_o(Hfrc(P,leq,fnnc,f)) "
  unfolding is_Hfrc_at_def using Hfrc_abs
  by auto

lemma components_closed :
  "x\<in>M \<Longrightarrow> ftype(x)\<in>M"
  "x\<in>M \<Longrightarrow> name1(x)\<in>M"
  "x\<in>M \<Longrightarrow> name2(x)\<in>M"
  "x\<in>M \<Longrightarrow> cond_of(x)\<in>M"
  unfolding ftype_def name1_def name2_def cond_of_def using fst_snd_closed by simp_all

lemma ecloseN_closed:
  "(##M)(A) \<Longrightarrow> (##M)(ecloseN(A))"
  "(##M)(A) \<Longrightarrow> (##M)(eclose_n(name1,A))"
  "(##M)(A) \<Longrightarrow> (##M)(eclose_n(name2,A))"
  unfolding ecloseN_def eclose_n_def
  using components_closed eclose_closed singletonM Un_closed by auto

lemma is_eclose_n_abs :
  assumes "x\<in>M" "ec\<in>M"
  shows "is_eclose_n(##M,is_name1,ec,x) \<longleftrightarrow> ec = eclose_n(name1,x)"
    "is_eclose_n(##M,is_name2,ec,x) \<longleftrightarrow> ec = eclose_n(name2,x)"
  unfolding is_eclose_n_def eclose_n_def
  using assms name1_abs name2_abs eclose_abs singletonM components_closed
  by auto


lemma is_ecloseN_abs :
  "\<lbrakk>x\<in>M;ec\<in>M\<rbrakk> \<Longrightarrow> is_ecloseN(##M,ec,x) \<longleftrightarrow> ec = ecloseN(x)"
  unfolding is_ecloseN_def ecloseN_def
  using is_eclose_n_abs Un_closed union_abs ecloseN_closed
  by auto

lemma frecR_abs :
  "x\<in>M \<Longrightarrow> y\<in>M \<Longrightarrow> frecR(x,y) \<longleftrightarrow> is_frecR(##M,x,y)"
  unfolding frecR_def is_frecR_def using components_closed domain_closed by simp

lemma frecrelP_abs :
  "z\<in>M \<Longrightarrow> frecrelP(##M,z) \<longleftrightarrow> (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y))"
  using pair_in_M_iff frecR_abs unfolding frecrelP_def by auto

lemma frecrel_abs:
  assumes
    "A\<in>M" "r\<in>M"
  shows
    "is_frecrel(##M,A,r) \<longleftrightarrow>  r = frecrel(A)"
proof -
  from \<open>A\<in>M\<close>
  have "z\<in>M" if "z\<in>A\<times>A" for z
    using cartprod_closed transitivity that by simp
  then
  have "Collect(A\<times>A,frecrelP(##M)) = Collect(A\<times>A,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y)))"
    using Collect_cong[of "A\<times>A" "A\<times>A" "frecrelP(##M)"] assms frecrelP_abs by simp
  with assms
  show ?thesis unfolding is_frecrel_def def_frecrel using cartprod_closed
    by simp
qed

lemma frecrel_closed:
  assumes
    "x\<in>M"
  shows
    "frecrel(x)\<in>M"
proof -
  have "Collect(x\<times>x,\<lambda>z. (\<exists>x y. z = \<langle>x,y\<rangle> \<and> frecR(x,y)))\<in>M"
    using Collect_in_M_0p[of "frecrelP_fm(0)"] arity_frecrelP_fm sats_frecrelP_fm
      frecrelP_abs \<open>x\<in>M\<close> cartprod_closed by simp
  then show ?thesis
    unfolding frecrel_def Rrel_def frecrelP_def by simp
qed

lemma field_frecrel : "field(frecrel(names_below(P,x))) \<subseteq> names_below(P,x)"
  unfolding frecrel_def
  using field_Rrel by simp

lemma forcerelD : "uv \<in> forcerel(P,x) \<Longrightarrow> uv\<in> names_below(P,x) \<times> names_below(P,x)"
  unfolding forcerel_def
  using trancl_type field_frecrel by blast

lemma wf_forcerel :
  "wf(forcerel(P,x))"
  unfolding forcerel_def using wf_trancl wf_frecrel .

lemma restrict_trancl_forcerel:
  assumes "frecR(w,y)"
  shows "restrict(f,frecrel(names_below(P,x))-``{y})`w
       = restrict(f,forcerel(P,x)-``{y})`w"
  unfolding forcerel_def frecrel_def using assms restrict_trancl_Rrel[of frecR]
  by simp

lemma names_belowI :
  assumes "frecR(\<langle>ft,n1,n2,p\<rangle>,\<langle>a,b,c,d\<rangle>)" "p\<in>P"
  shows "\<langle>ft,n1,n2,p\<rangle> \<in> names_below(P,\<langle>a,b,c,d\<rangle>)" (is "?x \<in> names_below(_,?y)")
proof -
  from assms
  have "ft \<in> 2" "a \<in> 2"
    unfolding frecR_def by (auto simp add:components_simp)
  from assms
  consider (e) "n1 \<in> domain(b) \<union> domain(c) \<and> (n2 = b \<or> n2 =c)"
    | (m) "n1 = b \<and> n2 \<in> domain(c)"
    unfolding frecR_def by (auto simp add:components_simp)
  then show ?thesis
  proof cases
    case e
    then
    have "n1 \<in> eclose(b) \<or> n1 \<in> eclose(c)"
      using Un_iff in_dom_in_eclose by auto
    with e
    have "n1 \<in> ecloseN(?y)" "n2 \<in> ecloseN(?y)"
      using ecloseNI components_in_eclose by auto
    with \<open>ft\<in>2\<close> \<open>p\<in>P\<close>
    show ?thesis unfolding names_below_def by  auto
  next
    case m
    then
    have "n1 \<in> ecloseN(?y)" "n2 \<in> ecloseN(?y)"
      using mem_eclose_trans  ecloseNI
        in_dom_in_eclose components_in_eclose by auto
    with \<open>ft\<in>2\<close> \<open>p\<in>P\<close>
    show ?thesis unfolding names_below_def
      by auto
  qed
qed

lemma names_below_tr :
  assumes "x\<in> names_below(P,y)"
    "y\<in> names_below(P,z)"
  shows "x\<in> names_below(P,z)"
proof -
  let ?A="\<lambda>y . names_below(P,y)"
  from assms
  obtain fx x1 x2 px where
    "x = \<langle>fx,x1,x2,px\<rangle>" "fx\<in>2" "x1\<in>ecloseN(y)" "x2\<in>ecloseN(y)" "px\<in>P"
    unfolding names_below_def by auto
  from assms
  obtain fy y1 y2 py where
    "y = \<langle>fy,y1,y2,py\<rangle>" "fy\<in>2" "y1\<in>ecloseN(z)" "y2\<in>ecloseN(z)" "py\<in>P"
    unfolding names_below_def by auto
  from \<open>x1\<in>_\<close> \<open>x2\<in>_\<close> \<open>y1\<in>_\<close> \<open>y2\<in>_\<close> \<open>x=_\<close> \<open>y=_\<close>
  have "x1\<in>ecloseN(z)" "x2\<in>ecloseN(z)"
    using ecloseN_mono names_simp by auto
  with \<open>fx\<in>2\<close> \<open>px\<in>P\<close> \<open>x=_\<close>
  have "x\<in>?A(z)"
    unfolding names_below_def by simp
  then show ?thesis using subsetI by simp
qed

lemma arg_into_names_below2 :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P,z))"
  shows  "x \<in> names_below(P,y)"
proof -
  {
    from assms
    have "x\<in>names_below(P,z)" "y\<in>names_below(P,z)" "frecR(x,y)"
      unfolding frecrel_def Rrel_def
      by auto
    obtain f n1 n2 p where
      "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>P"
      using \<open>x\<in>names_below(P,z)\<close>
      unfolding names_below_def by auto
    moreover
    obtain fy m1 m2 q where
      "q\<in>P" "y = \<langle>fy,m1,m2,q\<rangle>"
      using \<open>y\<in>names_below(P,z)\<close>
      unfolding names_below_def by auto
    moreover
    note \<open>frecR(x,y)\<close>
    ultimately
    have "x\<in>names_below(P,y)" using names_belowI by simp
  }
  then show ?thesis .
qed

lemma arg_into_names_below :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P,z))"
  shows  "x \<in> names_below(P,x)"
proof -
  {
    from assms
    have "x\<in>names_below(P,z)"
      unfolding frecrel_def Rrel_def
      by auto
    from \<open>x\<in>names_below(P,z)\<close>
    obtain f n1 n2 p where
      "x = \<langle>f,n1,n2,p\<rangle>" "f\<in>2" "n1\<in>ecloseN(z)" "n2\<in>ecloseN(z)" "p\<in>P"
      unfolding names_below_def by auto
    then
    have "n1\<in>ecloseN(x)" "n2\<in>ecloseN(x)"
      using components_in_eclose by simp_all
    with \<open>f\<in>2\<close> \<open>p\<in>P\<close> \<open>x = \<langle>f,n1,n2,p\<rangle>\<close>
    have "x\<in>names_below(P,x)"
      unfolding names_below_def by simp
  }
  then show ?thesis .
qed

lemma forcerel_arg_into_names_below :
  assumes "\<langle>x,y\<rangle> \<in> forcerel(P,z)"
  shows  "x \<in> names_below(P,x)"
  using assms
  unfolding forcerel_def
  by(rule trancl_induct;auto simp add: arg_into_names_below)

lemma names_below_mono :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P,z))"
  shows "names_below(P,x) \<subseteq> names_below(P,y)"
proof -
  from assms
  have "x\<in>names_below(P,y)"
    using arg_into_names_below2 by simp
  then
  show ?thesis
    using names_below_tr subsetI by simp
qed

lemma frecrel_mono :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P,z))"
  shows "frecrel(names_below(P,x)) \<subseteq> frecrel(names_below(P,y))"
  unfolding frecrel_def
  using Rrel_mono names_below_mono assms by simp

lemma forcerel_mono2 :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P,z))"
  shows "forcerel(P,x) \<subseteq> forcerel(P,y)"
  unfolding forcerel_def
  using trancl_mono frecrel_mono assms by simp

lemma forcerel_mono_aux :
  assumes "\<langle>x,y\<rangle> \<in> frecrel(names_below(P, w))^+"
  shows "forcerel(P,x) \<subseteq> forcerel(P,y)"
  using assms
  by (rule trancl_induct,simp_all add: subset_trans forcerel_mono2)

lemma forcerel_mono :
  assumes "\<langle>x,y\<rangle> \<in> forcerel(P,z)"
  shows "forcerel(P,x) \<subseteq> forcerel(P,y)"
  using forcerel_mono_aux assms unfolding forcerel_def by simp

lemma aux: "x \<in> names_below(P, w) \<Longrightarrow> \<langle>x,y\<rangle> \<in> forcerel(P,z) \<Longrightarrow>
  (y \<in> names_below(P, w) \<longrightarrow> \<langle>x,y\<rangle> \<in> forcerel(P,w))"
  unfolding forcerel_def
proof(rule_tac a=x and b=y and P="\<lambda> y . y \<in> names_below(P, w) \<longrightarrow> \<langle>x,y\<rangle> \<in> frecrel(names_below(P,w))^+" in trancl_induct,simp)
  let ?A="\<lambda> a . names_below(P, a)"
  let ?R="\<lambda> a . frecrel(?A(a))"
  let ?fR="\<lambda> a .forcerel(a)"
  show "u\<in>?A(w) \<longrightarrow> \<langle>x,u\<rangle>\<in>?R(w)^+" if "x\<in>?A(w)" "\<langle>x,y\<rangle>\<in>?R(z)^+" "\<langle>x,u\<rangle>\<in>?R(z)"  for  u
    using that frecrelD frecrelI r_into_trancl unfolding names_below_def by simp
  {
    fix u v
    assume "x \<in> ?A(w)"
      "\<langle>x, y\<rangle> \<in> ?R(z)^+"
      "\<langle>x, u\<rangle> \<in> ?R(z)^+"
      "\<langle>u, v\<rangle> \<in> ?R(z)"
      "u \<in> ?A(w) \<Longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+"
    then
    have "v \<in> ?A(w) \<Longrightarrow> \<langle>x, v\<rangle> \<in> ?R(w)^+"
    proof -
      assume "v \<in>?A(w)"
      from \<open>\<langle>u,v\<rangle>\<in>_\<close>
      have "u\<in>?A(v)"
        using arg_into_names_below2 by simp
      with \<open>v \<in>?A(w)\<close>
      have "u\<in>?A(w)"
        using names_below_tr by simp
      with \<open>v\<in>_\<close> \<open>\<langle>u,v\<rangle>\<in>_\<close>
      have "\<langle>u,v\<rangle>\<in> ?R(w)"
        using frecrelD frecrelI r_into_trancl unfolding names_below_def by simp
      with \<open>u \<in> ?A(w) \<Longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+\<close> \<open>u\<in>?A(w)\<close>
      have "\<langle>x, u\<rangle> \<in> ?R(w)^+" by simp
      with \<open>\<langle>u,v\<rangle>\<in> ?R(w)\<close>
      show "\<langle>x,v\<rangle>\<in> ?R(w)^+" using trancl_trans r_into_trancl
        by simp
    qed
  }
  then show "v \<in> ?A(w) \<longrightarrow> \<langle>x, v\<rangle> \<in> ?R(w)^+"
    if "x \<in> ?A(w)"
      "\<langle>x, y\<rangle> \<in> ?R(z)^+"
      "\<langle>x, u\<rangle> \<in> ?R(z)^+"
      "\<langle>u, v\<rangle> \<in> ?R(z)"
      "u \<in> ?A(w) \<longrightarrow> \<langle>x, u\<rangle> \<in> ?R(w)^+" for u v
    using that by simp
qed

lemma forcerel_eq :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(P,x)"
  shows "forcerel(P,z) = forcerel(P,x) \<inter> names_below(P,z)\<times>names_below(P,z)"
  using assms aux forcerelD forcerel_mono[of z x x] subsetI
  by auto

lemma forcerel_below_aux :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(P,x)" "\<langle>u,z\<rangle> \<in> forcerel(P,x)"
  shows "u \<in> names_below(P,z)"
  using assms(2)
  unfolding forcerel_def
proof(rule trancl_induct)
  show  "u \<in> names_below(P,y)" if " \<langle>u, y\<rangle> \<in> frecrel(names_below(P, x))" for y
    using that vimage_singleton_iff arg_into_names_below2 by simp
next
  show "u \<in> names_below(P,z)"
    if "\<langle>u, y\<rangle> \<in> frecrel(names_below(P, x))^+"
      "\<langle>y, z\<rangle> \<in> frecrel(names_below(P, x))"
      "u \<in> names_below(P, y)"
    for y z
    using that arg_into_names_below2[of y z x] names_below_tr by simp
qed

lemma forcerel_below :
  assumes "\<langle>z,x\<rangle> \<in> forcerel(P,x)"
  shows "forcerel(P,x) -`` {z} \<subseteq> names_below(P,z)"
  using vimage_singleton_iff assms forcerel_below_aux by auto

lemma relation_forcerel :
  shows "relation(forcerel(P,z))" "trans(forcerel(P,z))"
  unfolding forcerel_def using relation_trancl trans_trancl by simp_all

lemma Hfrc_restrict_trancl: "bool_of_o(Hfrc(P, leq, y, restrict(f,frecrel(names_below(P,x))-``{y})))
         = bool_of_o(Hfrc(P, leq, y, restrict(f,(frecrel(names_below(P,x))^+)-``{y})))"
  unfolding Hfrc_def bool_of_o_def eq_case_def mem_case_def
  using restrict_trancl_forcerel frecRI1 frecRI2 frecRI3
  unfolding forcerel_def
  by simp

(* Recursive definition of forces for atomic formulas using a transitive relation *)
lemma frc_at_trancl: "frc_at(P,leq,z) = wfrec(forcerel(P,z),z,\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
  unfolding frc_at_def forcerel_def using wf_eq_trancl Hfrc_restrict_trancl by simp


lemma forcerelI1 :
  assumes "n1 \<in> domain(b) \<or> n1 \<in> domain(c)" "p\<in>P" "d\<in>P"
  shows "\<langle>\<langle>1, n1, b, p\<rangle>, \<langle>0,b,c,d\<rangle>\<rangle>\<in> forcerel(P,\<langle>0,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>1, n1, b, p\<rangle>"
  let ?y="\<langle>0,b,c,d\<rangle>"
  from assms
  have "frecR(?x,?y)"
    using frecRI1 by simp
  then
  have "?x\<in>names_below(P,?y)"  "?y \<in> names_below(P,?y)"
    using names_belowI  assms components_in_eclose
    unfolding names_below_def by auto
  with \<open>frecR(?x,?y)\<close>
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemma forcerelI2 :
  assumes "n1 \<in> domain(b) \<or> n1 \<in> domain(c)" "p\<in>P" "d\<in>P"
  shows "\<langle>\<langle>1, n1, c, p\<rangle>, \<langle>0,b,c,d\<rangle>\<rangle>\<in> forcerel(P,\<langle>0,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>1, n1, c, p\<rangle>"
  let ?y="\<langle>0,b,c,d\<rangle>"
  from assms
  have "frecR(?x,?y)"
    using frecRI2 by simp
  then
  have "?x\<in>names_below(P,?y)"  "?y \<in> names_below(P,?y)"
    using names_belowI  assms components_in_eclose
    unfolding names_below_def by auto
  with \<open>frecR(?x,?y)\<close>
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemma forcerelI3 :
  assumes "\<langle>n2, r\<rangle> \<in> c" "p\<in>P" "d\<in>P" "r \<in> P"
  shows "\<langle>\<langle>0, b, n2, p\<rangle>,\<langle>1, b, c, d\<rangle>\<rangle> \<in> forcerel(P,\<langle>1,b,c,d\<rangle>)"
proof -
  let ?x="\<langle>0, b, n2, p\<rangle>"
  let ?y="\<langle>1, b, c, d\<rangle>"
  from assms
  have "frecR(?x,?y)"
    using assms frecRI3 by simp
  then
  have "?x\<in>names_below(P,?y)"  "?y \<in> names_below(P,?y)"
    using names_belowI  assms components_in_eclose
    unfolding names_below_def by auto
  with \<open>frecR(?x,?y)\<close>
  show ?thesis
    unfolding forcerel_def frecrel_def
    using subsetD[OF r_subset_trancl[OF relation_Rrel]] RrelI
    by auto
qed

lemmas forcerelI = forcerelI1[THEN vimage_singleton_iff[THEN iffD2]]
  forcerelI2[THEN vimage_singleton_iff[THEN iffD2]]
  forcerelI3[THEN vimage_singleton_iff[THEN iffD2]]

lemma  aux_def_frc_at:
  assumes "z \<in> forcerel(P,x) -`` {x}"
  shows "wfrec(forcerel(P,x), z, H) =  wfrec(forcerel(P,z), z, H)"
proof -
  let ?A="names_below(P,z)"
  from assms
  have "\<langle>z,x\<rangle> \<in> forcerel(P,x)"
    using vimage_singleton_iff by simp
  then
  have "z \<in> ?A"
    using forcerel_arg_into_names_below by simp
  from \<open>\<langle>z,x\<rangle> \<in> forcerel(P,x)\<close>
  have E:"forcerel(P,z) = forcerel(P,x) \<inter> (?A\<times>?A)"
    "forcerel(P,x) -`` {z} \<subseteq> ?A"
    using forcerel_eq forcerel_below
    by auto
  with \<open>z\<in>?A\<close>
  have "wfrec(forcerel(P,x), z, H) = wfrec[?A](forcerel(P,x), z, H)"
    using wfrec_trans_restr[OF relation_forcerel(1) wf_forcerel relation_forcerel(2), of x z ?A]
    by simp
  then show ?thesis
    using E wfrec_restr_eq by simp
qed

subsection\<open>Recursive expression of \<^term>\<open>frc_at\<close>\<close>

lemma def_frc_at :
  assumes "p\<in>P"
  shows
    "frc_at(P,leq,\<langle>ft,n1,n2,p\<rangle>) =
   bool_of_o( p \<in>P \<and>
  (  ft = 0 \<and>  (\<forall>s. s\<in>domain(n1) \<union> domain(n2) \<longrightarrow>
        (\<forall>q. q\<in>P \<and> q \<preceq> p \<longrightarrow> (frc_at(P,leq,\<langle>1,s,n1,q\<rangle>) =1 \<longleftrightarrow> frc_at(P,leq,\<langle>1,s,n2,q\<rangle>) =1)))
   \<or> ft = 1 \<and> ( \<forall>v\<in>P. v \<preceq> p \<longrightarrow>
    (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> q \<preceq> v \<and> \<langle>s,r\<rangle> \<in> n2 \<and> q \<preceq> r \<and>  frc_at(P,leq,\<langle>0,n1,s,q\<rangle>) = 1))))"
proof -
  let ?r="\<lambda>y. forcerel(P,y)" and ?Hf="\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"
  let ?t="\<lambda>y. ?r(y) -`` {y}"
  let ?arg="\<langle>ft,n1,n2,p\<rangle>"
  from wf_forcerel
  have wfr: "\<forall>w . wf(?r(w))" ..
  with wfrec [of "?r(?arg)" ?arg ?Hf]
  have "frc_at(P,leq,?arg) = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. wfrec(?r(?arg), x, ?Hf))"
    using frc_at_trancl by simp
  also
  have " ... = ?Hf( ?arg, \<lambda>x\<in>?r(?arg) -`` {?arg}. frc_at(P,leq,x))"
    using aux_def_frc_at frc_at_trancl by simp
  finally
  show ?thesis
    unfolding Hfrc_def mem_case_def eq_case_def
    using forcerelI  assms
    by auto
qed


subsection\<open>Absoluteness of \<^term>\<open>frc_at\<close>\<close>

lemma trans_forcerel_t : "trans(forcerel(P,x))"
  unfolding forcerel_def using trans_trancl .

lemma relation_forcerel_t : "relation(forcerel(P,x))"
  unfolding forcerel_def using relation_trancl .


lemma forcerel_in_M :
  assumes
    "x\<in>M"
  shows
    "forcerel(P,x)\<in>M"
  unfolding forcerel_def def_frecrel names_below_def
proof -
  let ?Q = "2 \<times> ecloseN(x) \<times> ecloseN(x) \<times> P"
  have "?Q \<times> ?Q \<in> M"
    using \<open>x\<in>M\<close> P_in_M twoN_in_M ecloseN_closed cartprod_closed by simp
  moreover
  have "separation(##M,\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y))"
  proof -
    have "arity(frecrelP_fm(0)) = 1"
      unfolding number1_fm_def frecrelP_fm_def
      by (simp del:FOL_sats_iff pair_abs empty_abs
          add: fm_defs frecR_fm_def number1_fm_def components_defs nat_simp_union)
    then
    have "separation(##M, \<lambda>z. sats(M,frecrelP_fm(0) , [z]))"
      using separation_ax by simp
    moreover
    have "frecrelP(##M,z) \<longleftrightarrow> sats(M,frecrelP_fm(0),[z])"
      if "z\<in>M" for z
      using that sats_frecrelP_fm[of 0 "[z]"] by simp
    ultimately
    have "separation(##M,frecrelP(##M))"
      unfolding separation_def by simp
    then
    show ?thesis using frecrelP_abs
        separation_cong[of "##M" "frecrelP(##M)" "\<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)"]
      by simp
  qed
  ultimately
  show "{z \<in> ?Q \<times> ?Q . \<exists>x y. z = \<langle>x, y\<rangle> \<and> frecR(x, y)}^+ \<in> M"
    using separation_closed frecrelP_abs trancl_closed by simp
qed

lemma relation2_Hfrc_at_abs:
  "relation2(##M,is_Hfrc_at(##M,P,leq),\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f)))"
  unfolding relation2_def using Hfrc_at_abs
  by simp

lemma Hfrc_at_closed :
  "\<forall>x\<in>M. \<forall>g\<in>M. function(g) \<longrightarrow> bool_of_o(Hfrc(P,leq,x,g))\<in>M"
  unfolding bool_of_o_def using zero_in_M n_in_M[of 1] by simp

lemma wfrec_Hfrc_at :
  assumes
    "X\<in>M"
  shows
    "wfrec_replacement(##M,is_Hfrc_at(##M,P,leq),forcerel(P,X))"
proof -
  have 0:"is_Hfrc_at(##M,P,leq,a,b,c) \<longleftrightarrow>
        sats(M,Hfrc_at_fm(8,9,2,1,0),[c,b,a,d,e,y,x,z,P,leq,forcerel(P,X)])"
    if "a\<in>M" "b\<in>M" "c\<in>M" "d\<in>M" "e\<in>M" "y\<in>M" "x\<in>M" "z\<in>M"
    for a b c d e y x z
    using that P_in_M leq_in_M \<open>X\<in>M\<close> forcerel_in_M
      is_Hfrc_at_iff_sats[of concl:M P leq a b c 8 9 2 1 0
        "[c,b,a,d,e,y,x,z,P,leq,forcerel(P,X)]"] by simp
  have 1:"sats(M,is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0),[y,x,z,P,leq,forcerel(P,X)]) \<longleftrightarrow>
                   is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(P,X), x, y)"
    if "x\<in>M" "y\<in>M" "z\<in>M" for x y z
    using  that \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M
      sats_is_wfrec_fm[OF 0]
    by simp
  let
    ?f="Exists(And(pair_fm(1,0,2),is_wfrec_fm(Hfrc_at_fm(8,9,2,1,0),5,1,0)))"
  have satsf:"sats(M, ?f, [x,z,P,leq,forcerel(P,X)]) \<longleftrightarrow>
              (\<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(P,X), x, y))"
    if "x\<in>M" "z\<in>M" for x z
    using that 1 \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M by (simp del:pair_abs)
  have artyf:"arity(?f) = 5"
    unfolding is_wfrec_fm_def Hfrc_at_fm_def Hfrc_fm_def Replace_fm_def PHcheck_fm_def
      pair_fm_def upair_fm_def is_recfun_fm_def fun_apply_fm_def big_union_fm_def
      pre_image_fm_def restriction_fm_def image_fm_def fm_defs number1_fm_def
      eq_case_fm_def mem_case_fm_def is_tuple_fm_def
    by (simp add:nat_simp_union)
  moreover
  have "?f\<in>formula"
    unfolding fm_defs Hfrc_at_fm_def by simp
  ultimately
  have "strong_replacement(##M,\<lambda>x z. sats(M,?f,[x,z,P,leq,forcerel(P,X)]))"
    using replacement_ax 1 artyf \<open>X\<in>M\<close> forcerel_in_M P_in_M leq_in_M by simp
  then
  have "strong_replacement(##M,\<lambda>x z.
          \<exists>y\<in>M. pair(##M,x,y,z) & is_wfrec(##M, is_Hfrc_at(##M,P,leq),forcerel(P,X), x, y))"
    using repl_sats[of M ?f "[P,leq,forcerel(P,X)]"] satsf by (simp del:pair_abs)
  then
  show ?thesis unfolding wfrec_replacement_def by simp
qed

lemma names_below_abs :
  "\<lbrakk>Q\<in>M;x\<in>M;nb\<in>M\<rbrakk> \<Longrightarrow> is_names_below(##M,Q,x,nb) \<longleftrightarrow> nb = names_below(Q,x)"
  unfolding is_names_below_def names_below_def
  using succ_in_M_iff zero_in_M cartprod_closed is_ecloseN_abs ecloseN_closed
  by auto

lemma names_below_closed:
  "\<lbrakk>Q\<in>M;x\<in>M\<rbrakk> \<Longrightarrow> names_below(Q,x) \<in> M"
  unfolding names_below_def
  using zero_in_M cartprod_closed ecloseN_closed succ_in_M_iff
  by simp

lemma "names_below_productE" :
  assumes "Q \<in> M" "x \<in> M"
    "\<And>A1 A2 A3 A4. A1 \<in> M \<Longrightarrow> A2 \<in> M \<Longrightarrow> A3 \<in> M \<Longrightarrow> A4 \<in> M \<Longrightarrow> R(A1 \<times> A2 \<times> A3 \<times> A4)"
  shows "R(names_below(Q,x))"
  unfolding names_below_def using assms zero_in_M ecloseN_closed[of x] twoN_in_M by auto

lemma forcerel_abs :
  "\<lbrakk>x\<in>M;z\<in>M\<rbrakk> \<Longrightarrow> is_forcerel(##M,P,x,z) \<longleftrightarrow> z = forcerel(P,x)"
  unfolding is_forcerel_def forcerel_def
  using frecrel_abs names_below_abs trancl_abs P_in_M twoN_in_M ecloseN_closed names_below_closed
    names_below_productE[of concl:"\<lambda>p. is_frecrel(##M,p,_) \<longleftrightarrow>  _ = frecrel(p)"] frecrel_closed
  by simp

lemma frc_at_abs:
  assumes "fnnc\<in>M" "z\<in>M"
  shows "is_frc_at(##M,P,leq,fnnc,z) \<longleftrightarrow> z = frc_at(P,leq,fnnc)"
proof -
  from assms
  have "(\<exists>r\<in>M. is_forcerel(##M,P,fnnc, r) \<and> is_wfrec(##M, is_Hfrc_at(##M, P, leq), r, fnnc, z))
        \<longleftrightarrow> is_wfrec(##M, is_Hfrc_at(##M, P, leq), forcerel(P,fnnc), fnnc, z)"
    using forcerel_abs forcerel_in_M by simp
  then
  show ?thesis
    unfolding frc_at_trancl is_frc_at_def
    using assms wfrec_Hfrc_at[of fnnc] wf_forcerel trans_forcerel_t relation_forcerel_t forcerel_in_M
      Hfrc_at_closed relation2_Hfrc_at_abs
      trans_wfrec_abs[of "forcerel(P,fnnc)" fnnc z "is_Hfrc_at(##M,P,leq)" "\<lambda>x f. bool_of_o(Hfrc(P,leq,x,f))"]
    by (simp flip:setclass_iff)
qed

lemma forces_eq'_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_eq'(##M,P,leq,p,t1,t2) \<longleftrightarrow> forces_eq'(P,leq,p,t1,t2)"
  unfolding is_forces_eq'_def forces_eq'_def
  using frc_at_abs zero_in_M tuples_in_M by auto

lemma forces_mem'_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_mem'(##M,P,leq,p,t1,t2) \<longleftrightarrow> forces_mem'(P,leq,p,t1,t2)"
  unfolding is_forces_mem'_def forces_mem'_def
  using frc_at_abs zero_in_M tuples_in_M by auto

lemma forces_neq'_abs :
  assumes
    "p\<in>M" "t1\<in>M" "t2\<in>M"
  shows
    "is_forces_neq'(##M,P,leq,p,t1,t2) \<longleftrightarrow> forces_neq'(P,leq,p,t1,t2)"
proof -
  have "q\<in>M" if "q\<in>P" for q
    using that transitivity P_in_M by simp
  then show ?thesis
    unfolding is_forces_neq'_def forces_neq'_def
    using assms forces_eq'_abs pair_in_M_iff
    by (auto,blast)
qed


lemma forces_nmem'_abs :
  assumes
    "p\<in>M" "t1\<in>M" "t2\<in>M"
  shows
    "is_forces_nmem'(##M,P,leq,p,t1,t2) \<longleftrightarrow> forces_nmem'(P,leq,p,t1,t2)"
proof -
  have "q\<in>M" if "q\<in>P" for q
    using that transitivity P_in_M by simp
  then show ?thesis
    unfolding is_forces_nmem'_def forces_nmem'_def
    using assms forces_mem'_abs pair_in_M_iff
    by (auto,blast)
qed

end (* forcing_data *)

subsection\<open>Forcing for general formulas\<close>

definition
  ren_forces_nand :: "i\<Rightarrow>i" where
  "ren_forces_nand(\<phi>) \<equiv> Exists(And(Equal(0,1),iterates(\<lambda>p. incr_bv(p)`1 , 2, \<phi>)))"

lemma ren_forces_nand_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_forces_nand(\<phi>) \<in>formula"
  unfolding ren_forces_nand_def
  by simp

lemma arity_ren_forces_nand :
  assumes "\<phi>\<in>formula"
  shows "arity(ren_forces_nand(\<phi>)) \<le> succ(arity(\<phi>))"
proof -
  consider (lt) "1<arity(\<phi>)" | (ge) "\<not> 1 < arity(\<phi>)"
    by auto
  then
  show ?thesis
  proof cases
    case lt
    with \<open>\<phi>\<in>_\<close>
    have "2 < succ(arity(\<phi>))" "2<arity(\<phi>)#+2"
      using succ_ltI by auto
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`1,2,\<phi>)) = 2#+arity(\<phi>)"
      using arity_incr_bv_lemma lt
      by auto
    with \<open>\<phi>\<in>_\<close>
    show ?thesis
      unfolding ren_forces_nand_def
      using lt pred_Un_distrib nat_union_abs1 Un_assoc[symmetric] Un_le_compat
      by simp
  next
    case ge
    with \<open>\<phi>\<in>_\<close>
    have "arity(\<phi>) \<le> 1" "pred(arity(\<phi>)) \<le> 1"
      using not_lt_iff_le le_trans[OF le_pred]
      by simp_all
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`1,2,\<phi>)) = (arity(\<phi>))"
      using arity_incr_bv_lemma ge
      by simp
    with \<open>arity(\<phi>) \<le> 1\<close> \<open>\<phi>\<in>_\<close> \<open>pred(_) \<le> 1\<close>
    show ?thesis
      unfolding ren_forces_nand_def
      using  pred_Un_distrib nat_union_abs1 Un_assoc[symmetric] nat_union_abs2
      by simp
  qed
qed

lemma sats_ren_forces_nand:
  "[q,P,leq,o,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
   sats(M, ren_forces_nand(\<phi>),[q,p,P,leq,o] @ env) \<longleftrightarrow> sats(M, \<phi>,[q,P,leq,o] @ env)"
  unfolding ren_forces_nand_def
  using sats_incr_bv_iff [of _ _ M _ "[q]"]
  by simp


definition
  ren_forces_forall :: "i\<Rightarrow>i" where
  "ren_forces_forall(\<phi>) \<equiv>
      Exists(Exists(Exists(Exists(Exists(
        And(Equal(0,6),And(Equal(1,7),And(Equal(2,8),And(Equal(3,9),
        And(Equal(4,5),iterates(\<lambda>p. incr_bv(p)`5 , 5, \<phi>)))))))))))"

lemma arity_ren_forces_all :
  assumes "\<phi>\<in>formula"
  shows "arity(ren_forces_forall(\<phi>)) = 5 \<union> arity(\<phi>)"
proof -
  consider (lt) "5<arity(\<phi>)" | (ge) "\<not> 5 < arity(\<phi>)"
    by auto
  then
  show ?thesis
  proof cases
    case lt
    with \<open>\<phi>\<in>_\<close>
    have "5 < succ(arity(\<phi>))" "5<arity(\<phi>)#+2"  "5<arity(\<phi>)#+3"  "5<arity(\<phi>)#+4"
      using succ_ltI by auto
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`5,5,\<phi>)) = 5#+arity(\<phi>)"
      using arity_incr_bv_lemma lt
      by simp
    with \<open>\<phi>\<in>_\<close>
    show ?thesis
      unfolding ren_forces_forall_def
      using pred_Un_distrib nat_union_abs1 Un_assoc[symmetric] nat_union_abs2
      by simp
  next
    case ge
    with \<open>\<phi>\<in>_\<close>
    have "arity(\<phi>) \<le> 5" "pred^5(arity(\<phi>)) \<le> 5"
      using not_lt_iff_le le_trans[OF le_pred]
      by simp_all
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`5,5,\<phi>)) = arity(\<phi>)"
      using arity_incr_bv_lemma ge
      by simp
    with \<open>arity(\<phi>) \<le> 5\<close> \<open>\<phi>\<in>_\<close> \<open>pred^5(_) \<le> 5\<close>
    show ?thesis
      unfolding ren_forces_forall_def
      using  pred_Un_distrib nat_union_abs1 Un_assoc[symmetric] nat_union_abs2
      by simp
  qed
qed

lemma ren_forces_forall_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_forces_forall(\<phi>) \<in>formula"
  unfolding ren_forces_forall_def by simp

lemma sats_ren_forces_forall :
  "[x,P,leq,o,p] @ env \<in> list(M) \<Longrightarrow> \<phi>\<in>formula \<Longrightarrow>
    sats(M, ren_forces_forall(\<phi>),[x,p,P,leq,o] @ env) \<longleftrightarrow> sats(M, \<phi>,[p,P,leq,o,x] @ env)"
  unfolding ren_forces_forall_def
  using sats_incr_bv_iff [of _ _ M _ "[p,P,leq,o,x]"]
  by simp


definition
  is_leq :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
  "is_leq(A,l,q,p) \<equiv> \<exists>qp[A]. (pair(A,q,p,qp) \<and> qp\<in>l)"

lemma (in forcing_data) leq_abs[simp]:
  "\<lbrakk> l\<in>M ; q\<in>M ; p\<in>M \<rbrakk> \<Longrightarrow> is_leq(##M,l,q,p) \<longleftrightarrow> \<langle>q,p\<rangle>\<in>l"
  unfolding is_leq_def using pair_in_M_iff by simp


definition
  leq_fm :: "[i,i,i] \<Rightarrow> i" where
  "leq_fm(leq,q,p) \<equiv> Exists(And(pair_fm(q#+1,p#+1,0),Member(0,leq#+1)))"

lemma arity_leq_fm :
  "\<lbrakk>leq\<in>nat;q\<in>nat;p\<in>nat\<rbrakk> \<Longrightarrow> arity(leq_fm(leq,q,p)) = succ(q) \<union> succ(p) \<union> succ(leq)"
  unfolding leq_fm_def
  using arity_pair_fm pred_Un_distrib nat_simp_union
  by auto

lemma leq_fm_type[TC] :
  "\<lbrakk>leq\<in>nat;q\<in>nat;p\<in>nat\<rbrakk> \<Longrightarrow> leq_fm(leq,q,p)\<in>formula"
  unfolding leq_fm_def by simp

lemma sats_leq_fm :
  "\<lbrakk> leq\<in>nat;q\<in>nat;p\<in>nat;env\<in>list(A) \<rbrakk> \<Longrightarrow>
     sats(A,leq_fm(leq,q,p),env) \<longleftrightarrow> is_leq(##A,nth(leq,env),nth(q,env),nth(p,env))"
  unfolding leq_fm_def is_leq_def by simp

subsubsection\<open>The primitive recursion\<close>

consts forces' :: "i\<Rightarrow>i"
primrec
  "forces'(Member(x,y)) = forces_mem_fm(1,2,0,x#+4,y#+4)"
  "forces'(Equal(x,y))  = forces_eq_fm(1,2,0,x#+4,y#+4)"
  "forces'(Nand(p,q))   =
        Neg(Exists(And(Member(0,2),And(leq_fm(3,0,1),And(ren_forces_nand(forces'(p)),
                                         ren_forces_nand(forces'(q)))))))"
  "forces'(Forall(p))   = Forall(ren_forces_forall(forces'(p)))"


definition
  forces :: "i\<Rightarrow>i" where
  "forces(\<phi>) \<equiv> And(Member(0,1),forces'(\<phi>))"

lemma forces'_type [TC]:  "\<phi>\<in>formula \<Longrightarrow> forces'(\<phi>) \<in> formula"
  by (induct \<phi> set:formula; simp)

lemma forces_type[TC] : "\<phi>\<in>formula \<Longrightarrow> forces(\<phi>) \<in> formula"
  unfolding forces_def by simp

context forcing_data
begin

subsection\<open>Forcing for atomic formulas in context\<close>

definition
  forces_eq :: "[i,i,i] \<Rightarrow> o" where
  "forces_eq \<equiv> forces_eq'(P,leq)"

definition
  forces_mem :: "[i,i,i] \<Rightarrow> o" where
  "forces_mem \<equiv> forces_mem'(P,leq)"

(* frc_at(P,leq,\<langle>0,t1,t2,p\<rangle>) = 1*)
definition
  is_forces_eq :: "[i,i,i] \<Rightarrow> o" where
  "is_forces_eq \<equiv> is_forces_eq'(##M,P,leq)"

(* frc_at(P,leq,\<langle>1,t1,t2,p\<rangle>) = 1*)
definition
  is_forces_mem :: "[i,i,i] \<Rightarrow> o" where
  "is_forces_mem \<equiv> is_forces_mem'(##M,P,leq)"


lemma def_forces_eq: "p\<in>P \<Longrightarrow> forces_eq(p,t1,t2) \<longleftrightarrow>
      (\<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q\<in>P \<and> q \<preceq> p \<longrightarrow>
      (forces_mem(q,s,t1) \<longleftrightarrow> forces_mem(q,s,t2)))"
  unfolding forces_eq_def forces_mem_def forces_eq'_def forces_mem'_def
  using def_frc_at[of p 0 t1 t2 ]  unfolding bool_of_o_def
  by auto

lemma def_forces_mem: "p\<in>P \<Longrightarrow> forces_mem(p,t1,t2) \<longleftrightarrow>
     (\<forall>v\<in>P. v \<preceq> p \<longrightarrow>
      (\<exists>q. \<exists>s. \<exists>r. r\<in>P \<and> q\<in>P \<and> q \<preceq> v \<and> \<langle>s,r\<rangle> \<in> t2 \<and> q \<preceq> r \<and> forces_eq(q,t1,s)))"
  unfolding forces_eq'_def forces_mem'_def forces_eq_def forces_mem_def
  using def_frc_at[of p 1 t1 t2]  unfolding bool_of_o_def
  by auto

lemma forces_eq_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_eq(p,t1,t2) \<longleftrightarrow> forces_eq(p,t1,t2)"
  unfolding is_forces_eq_def forces_eq_def
  using forces_eq'_abs by simp

lemma forces_mem_abs :
  "\<lbrakk>p\<in>M ; t1\<in>M ; t2\<in>M\<rbrakk> \<Longrightarrow> is_forces_mem(p,t1,t2) \<longleftrightarrow> forces_mem(p,t1,t2)"
  unfolding is_forces_mem_def forces_mem_def
  using forces_mem'_abs by simp

lemma sats_forces_eq_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
    "nth(p,env)=P" "nth(l,env)=leq"
  shows "sats(M,forces_eq_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
         is_forces_eq(nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_eq_fm_def is_forces_eq_def is_forces_eq'_def
  using assms sats_is_tuple_fm  sats_frc_at_fm
  by simp

lemma sats_forces_mem_fm:
  assumes  "p\<in>nat" "l\<in>nat" "q\<in>nat" "t1\<in>nat" "t2\<in>nat"  "env\<in>list(M)"
    "nth(p,env)=P" "nth(l,env)=leq"
  shows "sats(M,forces_mem_fm(p,l,q,t1,t2),env) \<longleftrightarrow>
             is_forces_mem(nth(q,env),nth(t1,env),nth(t2,env))"
  unfolding forces_mem_fm_def is_forces_mem_def is_forces_mem'_def
  using assms sats_is_tuple_fm sats_frc_at_fm
  by simp


definition
  forces_neq :: "[i,i,i] \<Rightarrow> o" where
  "forces_neq(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. q\<preceq>p \<and> forces_eq(q,t1,t2))"

definition
  forces_nmem :: "[i,i,i] \<Rightarrow> o" where
  "forces_nmem(p,t1,t2) \<equiv> \<not> (\<exists>q\<in>P. q\<preceq>p \<and> forces_mem(q,t1,t2))"


lemma forces_neq :
  "forces_neq(p,t1,t2) \<longleftrightarrow> forces_neq'(P,leq,p,t1,t2)"
  unfolding forces_neq_def forces_neq'_def forces_eq_def by simp

lemma forces_nmem :
  "forces_nmem(p,t1,t2) \<longleftrightarrow> forces_nmem'(P,leq,p,t1,t2)"
  unfolding forces_nmem_def forces_nmem'_def forces_mem_def by simp


lemma sats_forces_Member :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)"
    "nth(x,env)=xx" "nth(y,env)=yy" "q\<in>M"
  shows "sats(M,forces(Member(x,y)),[q,P,leq,one]@env) \<longleftrightarrow>
                (q\<in>P \<and> is_forces_mem(q,xx,yy))"
  unfolding forces_def
  using assms sats_forces_mem_fm P_in_M leq_in_M one_in_M
  by simp

lemma sats_forces_Equal :
  assumes  "x\<in>nat" "y\<in>nat" "env\<in>list(M)"
    "nth(x,env)=xx" "nth(y,env)=yy" "q\<in>M"
  shows "sats(M,forces(Equal(x,y)),[q,P,leq,one]@env) \<longleftrightarrow>
                (q\<in>P \<and> is_forces_eq(q,xx,yy))"
  unfolding forces_def
  using assms sats_forces_eq_fm P_in_M leq_in_M one_in_M
  by simp

lemma sats_forces_Nand :
  assumes  "\<phi>\<in>formula" "\<psi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "sats(M,forces(Nand(\<phi>,\<psi>)),[p,P,leq,one]@env) \<longleftrightarrow>
         (p\<in>P \<and> \<not>(\<exists>q\<in>M. q\<in>P \<and> is_leq(##M,leq,q,p) \<and>
               (sats(M,forces'(\<phi>),[q,P,leq,one]@env) \<and> sats(M,forces'(\<psi>),[q,P,leq,one]@env))))"
  unfolding forces_def using sats_leq_fm assms sats_ren_forces_nand P_in_M leq_in_M one_in_M
  by simp

lemma sats_forces_Neg :
  assumes  "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "sats(M,forces(Neg(\<phi>)),[p,P,leq,one]@env) \<longleftrightarrow>
         (p\<in>P \<and> \<not>(\<exists>q\<in>M. q\<in>P \<and> is_leq(##M,leq,q,p) \<and>
               (sats(M,forces'(\<phi>),[q,P,leq,one]@env))))"
  unfolding Neg_def using assms sats_forces_Nand
  by simp

lemma sats_forces_Forall :
  assumes  "\<phi>\<in>formula" "env\<in>list(M)" "p\<in>M"
  shows "sats(M,forces(Forall(\<phi>)),[p,P,leq,one]@env) \<longleftrightarrow>
         p\<in>P \<and> (\<forall>x\<in>M. sats(M,forces'(\<phi>),[p,P,leq,one,x]@env))"
  unfolding forces_def using assms sats_ren_forces_forall P_in_M leq_in_M one_in_M
  by simp

end (* forcing_data *)

subsection\<open>The arity of \<^term>\<open>forces\<close>\<close>

lemma arity_forces_at:
  assumes  "x \<in> nat" "y \<in> nat"
  shows "arity(forces(Member(x, y))) = (succ(x) \<union> succ(y)) #+ 4"
    "arity(forces(Equal(x, y))) = (succ(x) \<union> succ(y)) #+ 4"
  unfolding forces_def
  using assms arity_forces_mem_fm arity_forces_eq_fm succ_Un_distrib nat_simp_union
  by auto

lemma arity_forces':
  assumes "\<phi>\<in>formula"
  shows "arity(forces'(\<phi>)) \<le> arity(\<phi>) #+ 4"
  using assms
proof (induct set:formula)
  case (Member x y)
  then
  show ?case
    using arity_forces_mem_fm succ_Un_distrib nat_simp_union
    by simp
next
  case (Equal x y)
  then
  show ?case
    using arity_forces_eq_fm succ_Un_distrib nat_simp_union
    by simp
next
  case (Nand \<phi> \<psi>)
  let ?\<phi>' = "ren_forces_nand(forces'(\<phi>))"
  let ?\<psi>' = "ren_forces_nand(forces'(\<psi>))"
  have "arity(leq_fm(3, 0, 1)) = 4"
    using arity_leq_fm succ_Un_distrib nat_simp_union
    by simp
  have "3 \<le> (4#+arity(\<phi>)) \<union> (4#+arity(\<psi>))" (is "_ \<le> ?rhs")
    using nat_simp_union by simp
  from \<open>\<phi>\<in>_\<close> Nand
  have "pred(arity(?\<phi>')) \<le> ?rhs"  "pred(arity(?\<psi>')) \<le> ?rhs"
  proof -
    from \<open>\<phi>\<in>_\<close> \<open>\<psi>\<in>_\<close>
    have A:"pred(arity(?\<phi>')) \<le> arity(forces'(\<phi>))"
      "pred(arity(?\<psi>')) \<le> arity(forces'(\<psi>))"
      using pred_mono[OF _  arity_ren_forces_nand] pred_succ_eq
      by simp_all
    from Nand
    have "3 \<union> arity(forces'(\<phi>)) \<le> arity(\<phi>) #+ 4"
      "3 \<union> arity(forces'(\<psi>)) \<le> arity(\<psi>) #+ 4"
      using Un_le by simp_all
    with Nand
    show "pred(arity(?\<phi>')) \<le> ?rhs"
      "pred(arity(?\<psi>')) \<le> ?rhs"
      using le_trans[OF A(1)] le_trans[OF A(2)] le_Un_iff
      by simp_all
  qed
  with Nand \<open>_=4\<close>
  show ?case
    using pred_Un_distrib Un_assoc[symmetric] succ_Un_distrib nat_union_abs1 Un_leI3[OF \<open>3 \<le> ?rhs\<close>]
    by simp
next
  case (Forall \<phi>)
  let ?\<phi>' = "ren_forces_forall(forces'(\<phi>))"
  show ?case
  proof (cases "arity(\<phi>) = 0")
    case True
    with Forall
    show ?thesis
    proof -
      from Forall True
      have "arity(forces'(\<phi>)) \<le> 5"
        using le_trans[of _ 4 5] by auto
      with \<open>\<phi>\<in>_\<close>
      have "arity(?\<phi>') \<le> 5"
        using arity_ren_forces_all[OF forces'_type[OF \<open>\<phi>\<in>_\<close>]] nat_union_abs2
        by auto
      with Forall True
      show ?thesis
        using pred_mono[OF _ \<open>arity(?\<phi>') \<le> 5\<close>]
        by simp
    qed
  next
    case False
    with Forall
    show ?thesis
    proof -
      from Forall False
      have "arity(?\<phi>') = 5 \<union> arity(forces'(\<phi>))"
        "arity(forces'(\<phi>)) \<le> 5 #+ arity(\<phi>)"
        "4 \<le> succ(succ(succ(arity(\<phi>))))"
        using Ord_0_lt arity_ren_forces_all
          le_trans[OF _ add_le_mono[of 4 5, OF _ le_refl]]
        by auto
      with \<open>\<phi>\<in>_\<close>
      have "5 \<union> arity(forces'(\<phi>)) \<le> 5#+arity(\<phi>)"
        using nat_simp_union by auto
      with \<open>\<phi>\<in>_\<close> \<open>arity(?\<phi>') = 5 \<union> _\<close>
      show ?thesis
        using pred_Un_distrib succ_pred_eq[OF _ \<open>arity(\<phi>)\<noteq>0\<close>]
          pred_mono[OF _ Forall(2)] Un_le[OF \<open>4\<le>succ(_)\<close>]
        by simp
    qed
  qed
qed

lemma arity_forces :
  assumes "\<phi>\<in>formula"
  shows "arity(forces(\<phi>)) \<le> 4#+arity(\<phi>)"
  unfolding forces_def
  using assms arity_forces' le_trans nat_simp_union by auto

lemma arity_forces_le :
  assumes "\<phi>\<in>formula" "n\<in>nat" "arity(\<phi>) \<le> n"
  shows "arity(forces(\<phi>)) \<le> 4#+n"
  using assms le_trans[OF _ add_le_mono[OF le_refl[of 5] \<open>arity(\<phi>)\<le>_\<close>]] arity_forces
  by auto

end