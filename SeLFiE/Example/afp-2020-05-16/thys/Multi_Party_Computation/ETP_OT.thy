subsection \<open> Oblivious transfer constructed from ETPs \<close>

text\<open>Here we construct the OT protocol based on ETPs given in \cite{DBLP:books/sp/17/Lindell17} (Chapter 4) and prove
semi honest security for both parties. We show information theoretic security for Party 1 and reduce the security of 
Party 2 to the HCP assumption.\<close>

theory ETP_OT imports
  "HOL-Number_Theory.Cong"
  ETP
  OT_Functionalities
  Semi_Honest_Def
begin

type_synonym 'range viewP1 = "((bool \<times> bool) \<times> 'range \<times> 'range) spmf"
type_synonym 'range dist1 = "((bool \<times> bool) \<times> 'range \<times> 'range) \<Rightarrow> bool spmf"
type_synonym 'index viewP2 = "(bool \<times> 'index \<times> (bool \<times> bool)) spmf"
type_synonym 'index dist2 = "(bool \<times> 'index \<times> bool \<times> bool) \<Rightarrow> bool spmf"
type_synonym ('index, 'range) advP2 = "'index \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'index dist2 \<Rightarrow> 'range \<Rightarrow> bool spmf"

lemma if_False_True: "(if x then False else \<not> False) \<longleftrightarrow> (if x then False else True)"
  by simp

lemma if_then_True [simp]: "(if b then True else x) \<longleftrightarrow> (\<not> b \<longrightarrow> x)"
  by simp

lemma if_else_True [simp]: "(if b then x else True) \<longleftrightarrow> (b \<longrightarrow> x)"
  by simp

lemma inj_on_Not [simp]: "inj_on Not A"
  by(auto simp add: inj_on_def)

locale ETP_base = etp: etp I domain range F F\<^sub>i\<^sub>n\<^sub>v B
  for I :: "('index \<times> 'trap) spmf" \<comment> \<open>samples index and trapdoor\<close>
    and domain :: "'index \<Rightarrow> 'range set" 
    and range :: "'index \<Rightarrow> 'range set"
    and B :: "'index \<Rightarrow> 'range \<Rightarrow> bool" \<comment> \<open>hard core predicate\<close>
    and F :: "'index \<Rightarrow> 'range \<Rightarrow> 'range"
    and F\<^sub>i\<^sub>n\<^sub>v :: "'index \<Rightarrow> 'trap \<Rightarrow> 'range \<Rightarrow> 'range"
begin

text\<open>The probabilistic program that defines the protocol.\<close>

definition protocol :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (unit \<times> bool) spmf"
  where "protocol input\<^sub>1 \<sigma> = do {  
    let (b\<^sub>\<sigma>, b\<^sub>\<sigma>') = input\<^sub>1;
    (\<alpha> :: 'index, \<tau> :: 'trap) \<leftarrow> I;
    x\<^sub>\<sigma> :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    let (y\<^sub>\<sigma> :: 'range) = F \<alpha> x\<^sub>\<sigma>;
    let (x\<^sub>\<sigma> :: 'range) = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
    let (x\<^sub>\<sigma>' :: 'range) = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let (\<beta>\<^sub>\<sigma> :: bool) = xor (B \<alpha> x\<^sub>\<sigma>) b\<^sub>\<sigma>;
    let (\<beta>\<^sub>\<sigma>' :: bool) = xor (B \<alpha> x\<^sub>\<sigma>') b\<^sub>\<sigma>';
    return_spmf ((), if \<sigma> then xor (B \<alpha> x\<^sub>\<sigma>') \<beta>\<^sub>\<sigma>' else xor (B \<alpha> x\<^sub>\<sigma>) \<beta>\<^sub>\<sigma>)}"

lemma correctness: "protocol (m0,m1) c = funct_OT_12 (m0,m1) c"
proof-
  have "(B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = (B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = m1)) = m1" 
    for \<alpha> \<tau> y\<^sub>\<sigma>'  by auto
  then show ?thesis 
    by(auto simp add: protocol_def funct_OT_12_def Let_def etp.B_F_inv_rewrite bind_spmf_const etp.lossless_S local.etp.lossless_I lossless_weight_spmfD split_def cong: bind_spmf_cong)
qed

text \<open> Party 1 views \<close>

definition R1 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'range viewP1"
  where "R1 input\<^sub>1 \<sigma> = do {
    let (b\<^sub>0, b\<^sub>1) = input\<^sub>1;
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
    return_spmf ((b\<^sub>0, b\<^sub>1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"

lemma lossless_R1: "lossless_spmf (R1 msgs \<sigma>)"
  by(simp add: R1_def local.etp.lossless_I split_def etp.lossless_S Let_def)

definition S1 :: "(bool \<times> bool) \<Rightarrow> unit \<Rightarrow> 'range viewP1"
  where "S1 == (\<lambda> input\<^sub>1 (). do {
    let (b\<^sub>0, b\<^sub>1) = input\<^sub>1;
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>0 :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>1 \<leftarrow> etp.S \<alpha>;
    return_spmf ((b\<^sub>0, b\<^sub>1), y\<^sub>0, y\<^sub>1)})" 

lemma lossless_S1: "lossless_spmf (S1 msgs ())"
  by(simp add: S1_def local.etp.lossless_I split_def etp.lossless_S)

text \<open> Party 2 views \<close>

definition R2 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'index viewP2"
  where "R2 msgs \<sigma> = do {
    let (b0,b1) = msgs;
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
    let x\<^sub>\<sigma> = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
    let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> (if \<sigma> then b1 else b0) ;
    let \<beta>\<^sub>\<sigma>' = (B \<alpha> x\<^sub>\<sigma>') \<oplus> (if \<sigma> then b0 else b1);
    return_spmf (\<sigma>, \<alpha>,(\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'))}"

lemma lossless_R2: "lossless_spmf (R2 msgs \<sigma>)"
  by(simp add: R2_def split_def local.etp.lossless_I etp.lossless_S)

definition S2 :: "bool \<Rightarrow> bool \<Rightarrow> 'index viewP2"
  where "S2 \<sigma> b\<^sub>\<sigma> = do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
    let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = B \<alpha> x\<^sub>\<sigma>';
    return_spmf (\<sigma>, \<alpha>, (\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'))}"

lemma lossless_S2: "lossless_spmf (S2 \<sigma> b\<^sub>\<sigma>)"
  by(simp add: S2_def local.etp.lossless_I etp.lossless_S split_def)

text \<open> Security for Party 1 \<close>

text\<open>We have information theoretic security for Party 1.\<close>

lemma P1_security: "R1 input\<^sub>1 \<sigma> = funct_OT_12 x y \<bind> (\<lambda> (s1, s2). S1 input\<^sub>1 s1)" 
  including monad_normalisation
proof-
   have "R1 input\<^sub>1 \<sigma> =  do {
    let (b0,b1) = input\<^sub>1;
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma> \<leftarrow> map_spmf (\<lambda> x\<^sub>\<sigma>. F \<alpha> x\<^sub>\<sigma>) (etp.S \<alpha>);
    return_spmf ((b0,b1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"
     by(simp add: bind_map_spmf o_def Let_def R1_def)
   also have "... = do {
    let (b0,b1) = input\<^sub>1;
    (\<alpha>, \<tau>) \<leftarrow> I;
    y\<^sub>\<sigma>' :: 'range \<leftarrow> etp.S \<alpha>;
    y\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    return_spmf ((b0,b1), if \<sigma> then y\<^sub>\<sigma>' else y\<^sub>\<sigma>, if \<sigma> then y\<^sub>\<sigma> else y\<^sub>\<sigma>')}"
     by(simp add: etp.uni_set_samp Let_def split_def cong: bind_spmf_cong)
   also have "... = funct_OT_12 x y \<bind> (\<lambda> (s1, s2). S1 input\<^sub>1 s1)"
     by(cases \<sigma>; simp add: S1_def R1_def Let_def funct_OT_12_def)
   ultimately show ?thesis by auto
qed 

text \<open> The adversary used in proof of security for party 2 \<close>

definition \<A> :: "('index, 'range) advP2"
  where "\<A> \<alpha> \<sigma> b\<^sub>\<sigma> D2 x = do {
    \<beta>\<^sub>\<sigma>' \<leftarrow> coin_spmf;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    d \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    return_spmf(if d then \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>')}"

lemma lossless_\<A>: 
  assumes "\<forall> view. lossless_spmf (D2 view)"
  shows "y \<in> set_spmf I \<longrightarrow>  lossless_spmf (\<A> (fst y) \<sigma> b\<^sub>\<sigma> D2 x)"
  by(simp add: \<A>_def etp.lossless_S assms)

lemma assm_bound_funct_OT_12: 
  assumes "etp.HCP_adv \<A> \<sigma> (if \<sigma> then b1 else b0) D \<le> HCP_ad"
  shows "\<bar>spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1,out2). 
              etp.HCP_game \<A> \<sigma> out2 D)) True - 1/2\<bar> \<le> HCP_ad"
(is "?lhs \<le> HCP_ad")
proof-
  have "?lhs = \<bar>spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D) True - 1/2\<bar>" 
    by(simp add: funct_OT_12_def)
  thus ?thesis using assms etp.HCP_adv_def by simp
qed

lemma assm_bound_funct_OT_12_collapse: 
  assumes "\<forall> b\<^sub>\<sigma>. etp.HCP_adv \<A> \<sigma> b\<^sub>\<sigma> D \<le> HCP_ad"
  shows "\<bar>spmf (funct_OT_12 m1 \<sigma> \<bind> (\<lambda> (out1,out2). etp.HCP_game \<A> \<sigma> out2 D)) True - 1/2\<bar> \<le> HCP_ad"
  using assm_bound_funct_OT_12 surj_pair assms by metis 

text \<open> To prove security for party 2 we split the proof on the cases on party 2's input \<close>

lemma R2_S2_False:
  assumes "((if \<sigma> then b0 else b1) = False)" 
  shows "spmf (R2 (b0,b1) \<sigma> \<bind> (D2 :: (bool \<times> 'index \<times> bool \<times> bool) \<Rightarrow> bool spmf)) True 
                = spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1,out2). S2 \<sigma> out2 \<bind> D2)) True"
proof-
  have "\<sigma> \<Longrightarrow> \<not> b0" using assms by simp
  moreover have "\<not> \<sigma> \<Longrightarrow> \<not> b1" using assms by simp
  ultimately show ?thesis
    by(auto simp add: R2_def S2_def split_def local.etp.F_f_inv assms funct_OT_12_def cong: bind_spmf_cong_simp) 
qed

lemma R2_S2_True:
  assumes "((if \<sigma> then b0 else b1) = True)" 
    and lossless_D: "\<forall> a. lossless_spmf (D2 a)"
  shows "\<bar>(spmf (bind_spmf (R2 (b0,b1) \<sigma>) D2) True) - spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1, out2). S2 \<sigma> out2 \<bind> (\<lambda> view. D2 view))) True\<bar>
                         = \<bar>2*((spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D2) True) - 1/2)\<bar>"
proof-
  have  "(spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1, out2). S2 \<sigma> out2 \<bind> D2)) True
              - spmf (bind_spmf (R2 (b0,b1) \<sigma>) D2) True) 
                    = 2 * ((spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D2) True) - 1/2)"
  proof-
    have  "((spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D2) True) - 1/2)  = 
                  1/2*(spmf (bind_spmf (S2 \<sigma> (if \<sigma> then b1 else b0)) D2) True
                        - spmf (bind_spmf (R2 (b0,b1) \<sigma>) D2) True)"
      including monad_normalisation
    proof- 
      have \<sigma>_true_b0_true: "\<sigma> \<Longrightarrow> b0 = True" using assms(1) by simp
      have \<sigma>_false_b1_true: "\<not> \<sigma> \<Longrightarrow> b1" using assms(1) by simp 
      have return_True_False: "spmf (return_spmf (\<not> d)) True = spmf (return_spmf d) False"
        for d by(cases d; simp)
      define HCP_game_true where "HCP_game_true == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    x \<leftarrow> (etp.S \<alpha>);
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x); 
    d \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    let b' = (if d then \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
    let b = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
    return_spmf (b = b')}"
      define HCP_game_false where "HCP_game_false == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    x \<leftarrow> (etp.S \<alpha>);
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x); 
    d \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    let b' = (if d then \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
    let b = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
    return_spmf (b = b')}"
      define HCP_game_\<A> where "HCP_game_\<A> == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
    \<beta>\<^sub>\<sigma>' \<leftarrow> coin_spmf;
    (\<alpha>, \<tau>) \<leftarrow> I;
    x \<leftarrow> etp.S \<alpha>;
    x' \<leftarrow> etp.S \<alpha>;
    d \<leftarrow> D2 (\<sigma>, \<alpha>, (B \<alpha> x) \<oplus> b\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    let b' = (if d then  \<beta>\<^sub>\<sigma>' else \<not> \<beta>\<^sub>\<sigma>');
    return_spmf (B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x') = b')}"
      define S2D where "S2D == \<lambda> \<sigma> b\<^sub>\<sigma> . do {
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
      let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
      let \<beta>\<^sub>\<sigma>' = B \<alpha> x\<^sub>\<sigma>';
      d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
      return_spmf d}"
      define R2D where "R2D == \<lambda> msgs \<sigma>.  do {
      let (b0,b1) = msgs;
      (\<alpha>, \<tau>) \<leftarrow> I;
      x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
      y\<^sub>\<sigma>' \<leftarrow> etp.S \<alpha>;
      let y\<^sub>\<sigma> = F \<alpha> x\<^sub>\<sigma>;
      let x\<^sub>\<sigma> = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>;
      let x\<^sub>\<sigma>' = F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>';
      let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> (if \<sigma> then b1 else b0) ;
      let \<beta>\<^sub>\<sigma>' = (B \<alpha> x\<^sub>\<sigma>') \<oplus> (if \<sigma> then b0 else b1);
      b :: bool \<leftarrow> D2(\<sigma>, \<alpha>,(\<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>'));
      return_spmf b}"
      define D_true where "D_true  == \<lambda>\<sigma> b\<^sub>\<sigma>. do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    x \<leftarrow> (etp.S \<alpha>);
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
    d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    return_spmf d}"
      define D_false where "D_false == \<lambda> \<sigma> b\<^sub>\<sigma>. do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x\<^sub>\<sigma> \<leftarrow> etp.S \<alpha>;
    x \<leftarrow> etp.S \<alpha>;
    let \<beta>\<^sub>\<sigma> = (B \<alpha> x\<^sub>\<sigma>) \<oplus> b\<^sub>\<sigma>;
    let \<beta>\<^sub>\<sigma>' = \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
    d :: bool \<leftarrow> D2(\<sigma>, \<alpha>, \<beta>\<^sub>\<sigma>, \<beta>\<^sub>\<sigma>');
    return_spmf d}"
      have lossless_D_false: "lossless_spmf (D_false \<sigma> (if \<sigma> then b1 else b0))"
        apply(auto simp add: D_false_def lossless_D local.etp.lossless_I) 
        using local.etp.lossless_S by auto
      have "spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D2) True =  spmf (HCP_game_\<A> \<sigma> (if \<sigma> then b1 else b0)) True" 
        apply(simp add: etp.HCP_game_def HCP_game_\<A>_def \<A>_def split_def etp.F_f_inv)
        by(rewrite bind_commute_spmf[where q = "coin_spmf"]; rewrite bind_commute_spmf[where q = "coin_spmf"]; rewrite bind_commute_spmf[where q = "coin_spmf"]; auto)+
      also have "... = spmf (bind_spmf (map_spmf Not coin_spmf) (\<lambda>b. if b then HCP_game_true \<sigma> (if \<sigma> then b1 else b0) else HCP_game_false \<sigma> (if \<sigma> then b1 else b0))) True"
        unfolding HCP_game_\<A>_def HCP_game_true_def HCP_game_false_def \<A>_def Let_def
        apply(simp add: split_def cong: if_cong)
        supply [[simproc del: monad_normalisation]]
        apply(subst if_distrib[where f = "bind_spmf _" for f, symmetric]; simp cong: bind_spmf_cong add: if_distribR )+
        apply(rewrite in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(fold map_spmf_conv_bind_spmf)
        apply(rule conjI; rule impI; simp) 
         apply(simp only: spmf_bind)
         apply(rule Bochner_Integration.integral_cong[OF refl])+
         apply clarify
        subgoal for r r\<^sub>\<sigma> \<alpha> \<tau> 
          apply(simp only: UNIV_bool spmf_of_set integral_spmf_of_set) 
          apply(simp cong: if_cong split del: if_split)
          apply(cases "B r (F\<^sub>i\<^sub>n\<^sub>v r r\<^sub>\<sigma> \<tau>)") 
          by auto
        apply(rewrite in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
        apply(rewrite in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
        apply(simp only: spmf_bind)
        apply(rule Bochner_Integration.integral_cong[OF refl])+
        apply clarify
        subgoal for r r\<^sub>\<sigma> \<alpha> \<tau> 
          apply(simp only: UNIV_bool spmf_of_set integral_spmf_of_set) 
          apply(simp cong: if_cong split del: if_split)
          apply(cases " B r (F\<^sub>i\<^sub>n\<^sub>v r r\<^sub>\<sigma> \<tau>)") 
          by auto
        done
      also have "... = 1/2*(spmf (HCP_game_true \<sigma> (if \<sigma> then b1 else b0)) True) + 1/2*(spmf (HCP_game_false \<sigma> (if \<sigma> then b1 else b0)) True)"
        by(simp add: spmf_bind UNIV_bool spmf_of_set integral_spmf_of_set)
      also have "... = 1/2*(spmf (D_true \<sigma> (if \<sigma> then b1 else b0)) True) + 1/2*(spmf (D_false \<sigma> (if \<sigma> then b1 else b0)) False)"   
      proof-
        have "spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2 (\<sigma>, \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)) \<bind> (\<lambda>d. return_spmf (\<not> d)))))) True 
                = spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2 (\<sigma>, \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)))))) False"
          (is "?lhs = ?rhs")
        proof-
          have "?lhs = spmf (I \<bind> (\<lambda>(\<alpha>, \<tau>). etp.S \<alpha> \<bind> (\<lambda>x\<^sub>\<sigma>. etp.S \<alpha> \<bind> (\<lambda>x. D2 (\<sigma>, \<alpha>, B \<alpha> x\<^sub>\<sigma> = (\<not> (if \<sigma> then b1 else b0)), \<not> B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x)) \<bind> (\<lambda>d. return_spmf (d)))))) False"
            by(simp only: split_def return_True_False spmf_bind) 
          then show ?thesis by simp
        qed
        then show ?thesis  by(simp add: HCP_game_true_def HCP_game_false_def Let_def D_true_def D_false_def if_distrib[where f="(=) _"] cong: if_cong)   
      qed
      also have "... =  1/2*((spmf (D_true \<sigma> (if \<sigma> then b1 else b0) ) True) + (1 - spmf (D_false \<sigma> (if \<sigma> then b1 else b0) ) True))"
        by(simp add: spmf_False_conv_True lossless_D_false)
      also have "... = 1/2 + 1/2* (spmf (D_true \<sigma> (if \<sigma> then b1 else b0)) True) - 1/2*(spmf (D_false \<sigma> (if \<sigma> then b1 else b0)) True)" 
        by(simp)     
      also have "... =  1/2 + 1/2* (spmf (S2D \<sigma> (if \<sigma> then b1 else b0) ) True) - 1/2*(spmf (R2D (b0,b1) \<sigma> ) True)"
        apply(auto  simp add: local.etp.F_f_inv S2D_def R2D_def D_true_def D_false_def  assms split_def cong: bind_spmf_cong_simp)
         apply(simp add: \<sigma>_true_b0_true)
        by(simp add: \<sigma>_false_b1_true)
      ultimately show ?thesis by(simp add: S2D_def R2D_def R2_def S2_def split_def)
    qed
    then show ?thesis by(auto simp add: funct_OT_12_def)
  qed
  thus ?thesis by simp
qed

lemma P2_adv_bound:
  assumes lossless_D: "\<forall> a. lossless_spmf (D2 a)"
  shows "\<bar>(spmf (bind_spmf (R2 (b0,b1) \<sigma>) D2) True) - spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1, out2). S2 \<sigma> out2 \<bind> (\<lambda> view. D2 view))) True\<bar>
                         \<le> \<bar>2*((spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D2) True) - 1/2)\<bar>"
  by(cases "(if \<sigma> then b0 else b1)"; auto simp add: R2_S2_False R2_S2_True assms)

sublocale OT_12: sim_det_def R1 S1 R2 S2 funct_OT_12 protocol 
  unfolding sim_det_def_def 
  by(simp add: lossless_R1 lossless_S1 lossless_R2 lossless_S2 funct_OT_12_def)

lemma correct: "OT_12.correctness m1 m2"
  unfolding OT_12.correctness_def  
  by (metis prod.collapse correctness)

lemma P1_security_inf_the: "OT_12.perfect_sec_P1 m1 m2" 
  unfolding OT_12.perfect_sec_P1_def using P1_security by simp 

lemma P2_security:
  assumes "\<forall> a. lossless_spmf (D a)"
  and "\<forall> b\<^sub>\<sigma>. etp.HCP_adv \<A> m2 b\<^sub>\<sigma> D \<le> HCP_ad"
  shows "OT_12.adv_P2 m1 m2 D \<le> 2 * HCP_ad"
proof-
  have "spmf (etp.HCP_game \<A> \<sigma> (if \<sigma> then b1 else b0) D) True = spmf (funct_OT_12 (b0,b1) \<sigma> \<bind> (\<lambda> (out1, out2). etp.HCP_game \<A> \<sigma> out2 D)) True"
    for \<sigma> b0 b1
  by(simp add: funct_OT_12_def)
  hence "OT_12.adv_P2 m1 m2 D \<le> \<bar>2*((spmf (funct_OT_12 m1 m2 \<bind> (\<lambda> (out1, out2). etp.HCP_game \<A> m2 out2 D)) True) - 1/2)\<bar>"
    unfolding OT_12.adv_P2_def using P2_adv_bound assms surj_pair prod.collapse by metis
  moreover have "\<bar>2*((spmf (funct_OT_12 m1 m2 \<bind> (\<lambda> (out1, out2). etp.HCP_game \<A> m2 out2 D)) True) - 1/2)\<bar> \<le> \<bar>2*HCP_ad\<bar>" 
  proof -
    have "(\<exists>r. \<bar>(1::real) / r\<bar> \<noteq> 1 / \<bar>r\<bar>) \<or> 2 / \<bar>1 / (spmf (funct_OT_12 m1 m2 
                \<bind> (\<lambda>(x, y). ((\<lambda>u b. etp.HCP_game \<A> m2 b D)::unit \<Rightarrow> bool \<Rightarrow> bool spmf) x y)) True - 1 / 2)\<bar> 
                      \<le> HCP_ad / (1 / 2)"
      using assm_bound_funct_OT_12_collapse assms by auto
    then show ?thesis
      by fastforce
  qed 
  moreover have "HCP_ad \<ge> 0" 
    using assms(2)  local.etp.HCP_adv_def by auto
  ultimately show ?thesis by argo
qed

end

text \<open> We also consider the asymptotic case for security proofs \<close>

locale ETP_sec_para = 
  fixes I :: "nat \<Rightarrow> ('index \<times> 'trap) spmf"
    and domain ::  "'index \<Rightarrow> 'range set"
    and range ::  "'index \<Rightarrow> 'range set"
    and f :: "'index \<Rightarrow> ('range \<Rightarrow> 'range)"
    and F :: "'index \<Rightarrow> 'range \<Rightarrow> 'range"
    and F\<^sub>i\<^sub>n\<^sub>v :: "'index \<Rightarrow> 'trap \<Rightarrow> 'range \<Rightarrow> 'range"
    and B :: "'index \<Rightarrow> 'range \<Rightarrow> bool"
  assumes ETP_base: "\<And> n. ETP_base (I n) domain range F F\<^sub>i\<^sub>n\<^sub>v"
begin

sublocale ETP_base "(I n)" domain range 
  using ETP_base  by simp

lemma correct_asym: "OT_12.correctness n m1 m2"
  by(simp add: correct)

lemma P1_sec_asym: "OT_12.perfect_sec_P1 n m1 m2"
  using P1_security_inf_the by simp                                                                

lemma P2_sec_asym: 
  assumes "\<forall> a. lossless_spmf (D a)" 
    and HCP_adv_neg: "negligible (\<lambda> n. etp_advantage n)"
    and etp_adv_bound: "\<forall> b\<^sub>\<sigma> n. etp.HCP_adv n \<A> m2 b\<^sub>\<sigma> D \<le> etp_advantage n"
  shows "negligible (\<lambda> n. OT_12.adv_P2 n m1 m2 D)" 
proof-
  have "negligible (\<lambda> n. 2 * etp_advantage n)" using HCP_adv_neg 
    by (simp add: negligible_cmultI)
  moreover have "\<bar>OT_12.adv_P2 n m1 m2 D\<bar> = OT_12.adv_P2 n m1 m2 D" for n unfolding OT_12.adv_P2_def by simp
  moreover have  "OT_12.adv_P2 n m1 m2 D \<le> 2 * etp_advantage n" for n using assms P2_security by blast
  ultimately show ?thesis 
    using assms negligible_le HCP_adv_neg P2_security by presburger 
qed

end

end