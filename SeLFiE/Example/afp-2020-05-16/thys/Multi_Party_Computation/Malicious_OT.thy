subsection \<open>Malicious OT\<close>

text \<open>Here we prove secure the 1-out-of-2 OT protocol given in \cite{DBLP:series/isc/HazayL10} (p190). 
For party 1 reduce security to the DDH assumption and for party 2 we show information theoretic security.\<close>

theory Malicious_OT imports
  "HOL-Number_Theory.Cong"
  Cyclic_Group_Ext
  DH_Ext
  Malicious_Defs  
  Number_Theory_Aux
  OT_Functionalities
  Uniform_Sampling
begin

type_synonym ('aux, 'grp', 'state) adv_1_P1 = "('grp' \<times> 'grp') \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'aux \<Rightarrow> (('grp' \<times> 'grp' \<times> 'grp') \<times> 'state) spmf"

type_synonym ('grp', 'state) adv_2_P1 = "'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> ('grp' \<times> 'grp') \<Rightarrow> 'state \<Rightarrow> ((('grp' \<times> 'grp') \<times> ('grp' \<times> 'grp')) \<times> 'state) spmf"

type_synonym ('adv_out1,'state) adv_3_P1 = "'state \<Rightarrow> 'adv_out1 spmf"

type_synonym ('aux, 'grp', 'adv_out1, 'state) adv_mal_P1 = "(('aux, 'grp', 'state) adv_1_P1 \<times> ('grp', 'state) adv_2_P1 \<times> ('adv_out1,'state) adv_3_P1)" 

type_synonym ('aux, 'grp','state) adv_1_P2 = "bool \<Rightarrow> 'aux \<Rightarrow> (('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<times> 'state) spmf"

type_synonym ('grp','state) adv_2_P2 = "('grp' \<times> 'grp' \<times> 'grp' \<times> 'grp' \<times> 'grp') \<Rightarrow> 'state \<Rightarrow> ((('grp' \<times> 'grp' \<times> 'grp') \<times> nat) \<times> 'state) spmf" 

type_synonym ('grp', 'adv_out2, 'state) adv_3_P2 = "('grp' \<times> 'grp') \<Rightarrow> ('grp' \<times> 'grp') \<Rightarrow> 'state \<Rightarrow> 'adv_out2 spmf"

type_synonym ('aux, 'grp', 'adv_out2, 'state) adv_mal_P2 = "(('aux, 'grp','state) adv_1_P2 \<times> ('grp','state) adv_2_P2 \<times> ('grp', 'adv_out2,'state) adv_3_P2)"

locale ot_base = 
  fixes \<G> :: "'grp cyclic_group" (structure)
  assumes finite_group: "finite (carrier \<G>)"
    and order_gt_0: "order \<G> > 0"
    and prime_order: "prime (order \<G>)"
begin

lemma prime_field: "a < (order \<G>) \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> coprime a (order \<G>)" 
  by (metis dvd_imp_le neq0_conv not_le prime_imp_coprime prime_order coprime_commute)

text\<open>The protocol uses a call to an idealised functionality of a zero knowledge protocol for the 
DDH relation, this is described by the functionality given below.\<close>

fun funct_DH_ZK :: "('grp \<times> 'grp \<times> 'grp) \<Rightarrow> (('grp \<times> 'grp \<times> 'grp) \<times> nat)  \<Rightarrow> (bool \<times> unit) spmf"
  where "funct_DH_ZK (h,a,b) ((h',a',b'),r) = return_spmf (a = \<^bold>g [^] r \<and> b = h [^] r \<and> (h,a,b) = (h',a',b'), ())"

text\<open>The probabilistic program that defines the output for both parties in the protocol.\<close>

definition protocol_ot :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> (unit \<times> 'grp) spmf"
  where "protocol_ot M \<sigma> = do {
  let (x0,x1) = M;
  r \<leftarrow> sample_uniform (order \<G>);
  \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
  \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
  let h0 = \<^bold>g [^] \<alpha>0;
  let h1 = \<^bold>g [^] \<alpha>1;
  let a = \<^bold>g [^] r;
  let b0 = h0 [^] r \<otimes> \<^bold>g [^] (if \<sigma> then (1::nat) else 0);
  let b1 = h1 [^] r \<otimes> \<^bold>g [^] (if \<sigma> then (1::nat) else 0);
  let h = h0 \<otimes> inv h1;
  let b = b0 \<otimes> inv b1;
  _ :: unit \<leftarrow> assert_spmf (a = \<^bold>g [^] r \<and> b = h [^] r);
  u0 \<leftarrow> sample_uniform (order \<G>);
  u1 \<leftarrow> sample_uniform (order \<G>);
  v0 \<leftarrow> sample_uniform (order \<G>);
  v1 \<leftarrow> sample_uniform (order \<G>); 
  let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
  let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
  let e0 = (w0, z0);
  let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
  let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
  let e1 = (w1, z1);
  return_spmf ((), (if \<sigma> then (z1 \<otimes> inv (w1 [^] \<alpha>1)) else (z0 \<otimes> inv (w0 [^] \<alpha>0))))}"

text\<open>Party 1 sends three messages (including the output) in the protocol so we split the adversary into three parts, one part
to output each message. The real view of the protocol for party 1 outputs the correct output for party 2 
and the adversary outputs the output for party 1.\<close>

definition P1_real_model :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out1, 'state) adv_mal_P1 \<Rightarrow> ('adv_out1 \<times> 'grp) spmf"
  where "P1_real_model M \<sigma> z \<A> = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = h0 [^] r \<otimes> (if \<sigma> then \<^bold>g else \<one>);
    let b1 = h1 [^] r \<otimes> (if \<sigma> then \<^bold>g else \<one>);
    ((in1 :: 'grp, in2 ::'grp, in3 :: 'grp), s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (b :: bool, _ :: unit) \<leftarrow> funct_DH_ZK (in1, in2, in3) ((h,a,b), r);
    _ :: unit \<leftarrow> assert_spmf (b); 
    (((w0,z0),(w1,z1)), s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    adv_out :: 'adv_out1  \<leftarrow> \<A>3 s';
    return_spmf (adv_out, (if \<sigma> then (z1 \<otimes> (inv w1 [^] \<alpha>1)) else (z0 \<otimes> (inv w0 [^] \<alpha>0))))}"

text\<open>The first and second part of the simulator for party 1 are defined below.\<close>

definition P1_S1 :: "('aux, 'grp, 'adv_out1, 'state) adv_mal_P1 \<Rightarrow> ('grp \<times> 'grp) \<Rightarrow> 'aux \<Rightarrow> (('grp \<times> 'grp) \<times> 'state) spmf"
  where "P1_S1 \<A> M z = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = h0 [^] r;
    let b1 = h1 [^] r \<otimes> \<^bold>g;
    ((in1 :: 'grp, in2 ::'grp, in3 :: 'grp), s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    _ :: unit \<leftarrow> assert_spmf ((in1, in2, in3) = (h,a,b));
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x0 = (z0 \<otimes> (inv w0 [^] \<alpha>0));
    let x1 = (z1 \<otimes> (inv w1 [^] \<alpha>1));
    return_spmf ((x0,x1), s')}" 

definition P1_S2 :: "('aux, 'grp, 'adv_out1,'state) adv_mal_P1 \<Rightarrow> ('grp \<times> 'grp) \<Rightarrow> 'aux \<Rightarrow> unit \<Rightarrow> 'state \<Rightarrow> 'adv_out1 spmf"
  where "P1_S2 \<A> M z out1 s' = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    \<A>3 s'}"

text\<open>We explicitly provide the unfolded definition of the ideal model for convieience in the proof.\<close>

definition P1_ideal_model :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out1,'state) adv_mal_P1 \<Rightarrow> ('adv_out1 \<times> 'grp) spmf"
  where "P1_ideal_model M \<sigma> z \<A>  = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = h0 [^] r;
    let b1 = h1 [^] r \<otimes> \<^bold>g;
    ((in1 :: 'grp, in2 ::'grp, in3 :: 'grp), s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    _ :: unit \<leftarrow> assert_spmf ((in1, in2, in3) = (h,a,b));
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x0' = z0 \<otimes> inv w0 [^] \<alpha>0;
    let x1' = z1 \<otimes> inv w1 [^] \<alpha>1;
    (_, f_out2) \<leftarrow> funct_OT_12  (x0', x1') \<sigma>;
    adv_out :: 'adv_out1  \<leftarrow> \<A>3 s';
    return_spmf (adv_out, f_out2)}"

text\<open>The advantage associated with the unfolded definition of the ideal view.\<close>

definition 
  "P1_adv_real_ideal_model (D :: ('adv_out1 \<times> 'grp) \<Rightarrow> bool spmf) M \<sigma> \<A> z
                  = \<bar>spmf ((P1_real_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) True 
                              - spmf ((P1_ideal_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) True\<bar>"

text\<open>We now define the real view and simulators for party 2 in an analogous way.\<close>

definition P2_real_model :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out2,'state) adv_mal_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_real_model M \<sigma> z \<A> = do {
    let (x0,x1) = M;
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G> \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3 :: 'grp), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    u0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>); 
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
    let e0 = (w0, z0);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
    let e1 = (w1, z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 

definition P2_S1 :: "('aux, 'grp, 'adv_out2,'state) adv_mal_P2 \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> (bool \<times> ('grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) \<times> 'state)  spmf"
  where "P2_S1 \<A> \<sigma> z = do {
   let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z; 
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3 :: 'grp), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    let l = b0 \<otimes> (inv (h0 [^] r));
    return_spmf ((if l = \<one> then False else True), (h0,h1,a,b0,b1), s')}"

definition P2_S2 :: "('aux, 'grp, 'adv_out2,'state) adv_mal_P2 \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> 'grp \<Rightarrow> (('grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) \<times> 'state) \<Rightarrow> 'adv_out2 spmf"
  where "P2_S2 \<A> \<sigma>' z x\<sigma> aux_out  = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    let ((h0,h1,a,b0,b1),s) = aux_out;
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> (if \<sigma>' then \<one> else x\<sigma>);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> (if \<sigma>' then x\<sigma> else \<one>);
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    \<A>3 e0 e1 s}"

sublocale mal_def : malicious_base funct_OT_12 protocol_ot P1_S1 P1_S2 P1_real_model P2_S1 P2_S2 P2_real_model .

text\<open>We prove the unfolded definition of the ideal views are equal to the definition we provide in the 
abstract locale that defines security.\<close>

lemma P1_ideal_ideal_eq:
  shows  "mal_def.ideal_view_1 x y z (P1_S1, P1_S2) \<A> = P1_ideal_model x y z \<A>"
  including monad_normalisation
  unfolding mal_def.ideal_view_1_def mal_def.ideal_game_1_def P1_ideal_model_def P1_S1_def P1_S2_def Let_def split_def 
  by(simp add: split_def)

lemma P1_advantages_eq: 
  shows "mal_def.adv_P1 x y z (P1_S1, P1_S2) \<A> D = P1_adv_real_ideal_model D x y \<A> z"
  by(simp add: mal_def.adv_P1_def P1_adv_real_ideal_model_def P1_ideal_ideal_eq)

fun P1_DDH_mal_adv_\<sigma>_false :: "('grp \<times> 'grp) \<Rightarrow> 'aux  \<Rightarrow> ('aux, 'grp, 'adv_out1,'state) adv_mal_P1 \<Rightarrow> (('adv_out1 \<times> 'grp) \<Rightarrow> bool spmf) \<Rightarrow> 'grp ddh.adversary"
  where "P1_DDH_mal_adv_\<sigma>_false M z \<A> D h a t = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = h;
    let b0 = a [^] \<alpha>0;
    let b1 = t;
    ((in1 :: 'grp, in2 ::'grp, in3 :: 'grp),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    _ :: unit \<leftarrow> assert_spmf (in1 = h0 \<otimes> inv h1 \<and> in2 = a \<and> in3 = b0 \<otimes> inv b1);
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x0 = (z0 \<otimes> (inv w0 [^] \<alpha>0));
    adv_out :: 'adv_out1 \<leftarrow> \<A>3 s';
    D (adv_out, x0)}"

fun P1_DDH_mal_adv_\<sigma>_true :: "('grp \<times> 'grp) \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out1,'state) adv_mal_P1 \<Rightarrow> (('adv_out1 \<times> 'grp) \<Rightarrow> bool spmf) \<Rightarrow> 'grp ddh.adversary"
  where "P1_DDH_mal_adv_\<sigma>_true M z \<A> D h a t = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    \<alpha>1 :: nat \<leftarrow> sample_uniform (order \<G>);
    let h1 = \<^bold>g [^] \<alpha>1;
    let h0 = h;
    let b0 = t;
    let b1 = a [^] \<alpha>1 \<otimes> \<^bold>g;
    ((in1 :: 'grp, in2 ::'grp, in3 :: 'grp),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    _ :: unit \<leftarrow> assert_spmf (in1 = h0 \<otimes> inv h1 \<and> in2 = a \<and> in3 = b0 \<otimes> inv b1);
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x1 = (z1 \<otimes> (inv w1 [^] \<alpha>1));
    adv_out :: 'adv_out1 \<leftarrow> \<A>3 s';
    D (adv_out, x1)}"

definition P2_ideal_model :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow>  ('aux, 'grp, 'adv_out2, 'state) adv_mal_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_ideal_model M \<sigma> z \<A> = do {
    let (x0,x1) = M;
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1), s) \<leftarrow> \<A>1 \<sigma> z; 
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r); 
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    let l = b0 \<otimes> (inv (h0 [^] r)); 
    let \<sigma>' = (if l = \<one> then False else True);
    (_ :: unit, x\<sigma>) \<leftarrow> funct_OT_12 (x0, x1) \<sigma>'; 
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> (if \<sigma>' then \<one> else x\<sigma>);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> (if \<sigma>' then x\<sigma> else \<one>);
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"

definition P2_ideal_model_end :: "('grp \<times> 'grp) \<Rightarrow> 'grp \<Rightarrow> (('grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) \<times> 'state)
                                    \<Rightarrow> ('grp, 'adv_out2, 'state) adv_3_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_ideal_model_end M l bs \<A>3 = do {
    let (x0,x1) = M;
    let ((h0,h1,a,b0,b1),s) = bs;
    let \<sigma>' = (if l = \<one> then False else True);
    (_:: unit, x\<sigma>) \<leftarrow> funct_OT_12 (x0, x1) \<sigma>';
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> (if \<sigma>' then \<one> else x\<sigma>);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> (if \<sigma>' then x\<sigma> else \<one>);
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s;
    return_spmf ((), out)}"

definition P2_ideal_model' :: "('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out2, 'state) adv_mal_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_ideal_model' M \<sigma> z \<A> = do {
    let (x0,x1) = M;
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3 :: 'grp), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    let l = b0 \<otimes> (inv (h0 [^] r));
    P2_ideal_model_end (x0,x1) l ((h0,h1,a,b0,b1),s') \<A>3}"

lemma P2_ideal_model_rewrite: "P2_ideal_model M \<sigma> z \<A> = P2_ideal_model' M \<sigma> z \<A> "
  by(simp add: P2_ideal_model'_def P2_ideal_model_def P2_ideal_model_end_def Let_def split_def) 

definition P2_real_model_end :: "('grp \<times> 'grp) \<Rightarrow> (('grp \<times> 'grp \<times> 'grp \<times> 'grp \<times> 'grp) \<times> 'state) 
                                    \<Rightarrow> ('grp, 'adv_out2,'state) adv_3_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_real_model_end M bs \<A>3 = do {
    let (x0,x1) = M;
    let ((h0,h1,a,b0,b1),s) = bs;
    u0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>); 
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let w0 = a [^] u0 \<otimes> \<^bold>g [^] v0;
    let e0 = (w0, z0);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let w1 = a [^] u1 \<otimes> \<^bold>g [^] v1;
    let e1 = (w1, z1);
    out \<leftarrow> \<A>3 e0 e1 s;
    return_spmf ((), out)}" 

definition P2_real_model' ::"('grp \<times> 'grp) \<Rightarrow> bool \<Rightarrow> 'aux \<Rightarrow> ('aux, 'grp, 'adv_out2, 'state) adv_mal_P2 \<Rightarrow> (unit \<times> 'adv_out2) spmf"
  where "P2_real_model' M \<sigma> z \<A> = do {
    let (x0,x1) = M;
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3 :: 'grp), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    P2_real_model_end M ((h0,h1,a,b0,b1),s') \<A>3}"

lemma P2_real_model_rewrite: "P2_real_model M \<sigma> z \<A> = P2_real_model' M \<sigma> z \<A>"
  by(simp add: P2_real_model'_def P2_real_model_def P2_real_model_end_def split_def)

lemma P2_ideal_view_unfold: "mal_def.ideal_view_2 (x0,x1) \<sigma> z (P2_S1, P2_S2) \<A> = P2_ideal_model (x0,x1) \<sigma> z \<A>"
  unfolding local.mal_def.ideal_view_2_def P2_ideal_model_def local.mal_def.ideal_game_2_def P2_S1_def P2_S2_def 
  by(auto simp add: Let_def split_def) 

end 

locale ot = ot_base + cyclic_group \<G>
begin

lemma P1_assert_correct1: 
  shows "((\<^bold>g [^] (\<alpha>0::nat)) [^] (r::nat) \<otimes> \<^bold>g \<otimes> inv ((\<^bold>g [^] (\<alpha>1::nat)) [^] r \<otimes> \<^bold>g) 
                = (\<^bold>g [^] \<alpha>0 \<otimes> inv (\<^bold>g [^] \<alpha>1)) [^] r)"
    (is "?lhs = ?rhs")
proof-
  have in_carrier1: "(\<^bold>g [^] \<alpha>1) [^] r \<in> carrier \<G>" by simp
  have in_carrier2: "inv ((\<^bold>g [^] \<alpha>1) [^] r) \<in> carrier \<G>" by simp
  have 1:"?lhs = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> \<^bold>g \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r) \<otimes> inv \<^bold>g"  
    using  cyclic_group_assoc nat_pow_pow inverse_split in_carrier1 by simp
  also have 2:"... = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> (\<^bold>g \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r)) \<otimes> inv \<^bold>g"
    using cyclic_group_assoc in_carrier2 by simp
  also have "... = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> (inv ((\<^bold>g [^] \<alpha>1) [^] r) \<otimes> \<^bold>g) \<otimes> inv \<^bold>g" 
    using in_carrier2 cyclic_group_commute by simp
  also have 3: "... = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r) \<otimes> (\<^bold>g \<otimes> inv \<^bold>g)"
    using cyclic_group_assoc in_carrier2 by simp
  also have "... = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r)" by simp
  also have "... = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> inv ((\<^bold>g [^] \<alpha>1)) [^] r" 
    using inverse_pow_pow by simp
  ultimately show ?thesis
    by (simp add: cyclic_group_commute pow_mult_distrib)
qed

lemma P1_assert_correct2: 
  shows   "(\<^bold>g [^] (\<alpha>0::nat)) [^] (r::nat) \<otimes> inv ((\<^bold>g [^] (\<alpha>1::nat)) [^] r) = (\<^bold>g [^] \<alpha>0 \<otimes> inv (\<^bold>g [^] \<alpha>1)) [^] r"
    (is "?lhs = ?rhs")
proof-
  have in_carrier2:"\<^bold>g [^] \<alpha>1 \<in> carrier \<G>" by simp
  hence "?lhs = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> inv ((\<^bold>g [^] \<alpha>1)) [^] r" 
    using inverse_pow_pow by simp
  thus ?thesis
    by (simp add: cyclic_group_commute monoid_comm_monoidI pow_mult_distrib)
qed

sublocale ddh: ddh_ext  
  by (simp add: cyclic_group_axioms ddh_ext.intro)

lemma P1_real_ddh0_\<sigma>_false:
  assumes "\<sigma> = False"
  shows "((P1_real_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = (ddh.DDH0 (P1_DDH_mal_adv_\<sigma>_false M z \<A> D))"
  including monad_normalisation
proof-
  have 
    "(in2 = \<^bold>g [^] (r::nat) \<and> in3 = in1 [^] r \<and> in1 = \<^bold>g [^] (\<alpha>0::nat) \<otimes> inv (\<^bold>g [^] (\<alpha>1::nat)) 
        \<and> in2 = \<^bold>g [^] r \<and> in3 = (\<^bold>g [^] r) [^] \<alpha>0 \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r))
          \<longleftrightarrow> (in1 = \<^bold>g [^] \<alpha>0 \<otimes> inv (\<^bold>g [^] \<alpha>1) \<and> in2 = \<^bold>g [^] r \<and> in3 
            = (\<^bold>g [^] r) [^] \<alpha>0 \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r))"  
    for in1 in2 in3 r \<alpha>0 \<alpha>1 
    by (auto simp add: P1_assert_correct2 power_swap)
  moreover have "((P1_real_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = (\<^bold>g [^] r) [^] \<alpha>0;
    let b1 = h1 [^] r;
    ((in1, in2, in3),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (b :: bool, _ :: unit) \<leftarrow> funct_DH_ZK (in1, in2, in3) ((h,a,b), r);
    _ :: unit \<leftarrow> assert_spmf (b); 
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    adv_out \<leftarrow> \<A>3 s';
    D (adv_out, ((z0 \<otimes> (inv w0 [^] \<alpha>0))))}"
    by(simp add: P1_real_model_def assms split_def Let_def power_swap)
  ultimately show ?thesis  
    by(simp add: P1_real_model_def ddh.DDH0_def Let_def)
qed

lemma P1_ideal_ddh1_\<sigma>_false:
  assumes "\<sigma> = False"
  shows "((P1_ideal_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = (ddh.DDH1 (P1_DDH_mal_adv_\<sigma>_false M z \<A> D))"
  including monad_normalisation
proof-
  have "((P1_ideal_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = (\<^bold>g [^] r) [^] \<alpha>0;
    let b1 = h1 [^] r \<otimes> \<^bold>g;
    ((in1, in2, in3),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    _ :: unit \<leftarrow> assert_spmf ((in1, in2, in3) = (h,a,b));
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x0 = (z0 \<otimes> (inv w0 [^] \<alpha>0));
    let x1 = (z1 \<otimes> (inv w1 [^] \<alpha>1));
    (_, f_out2) \<leftarrow> funct_OT_12  (x0, x1) \<sigma>;
    adv_out \<leftarrow> \<A>3 s';
    D (adv_out, f_out2)}"
    by(simp add: P1_ideal_model_def assms split_def Let_def  power_swap)
  thus ?thesis 
    by(auto simp add: P1_ideal_model_def ddh.DDH1_def funct_OT_12_def Let_def assms )
qed

lemma P1_real_ddh1_\<sigma>_true:
  assumes "\<sigma> = True"
  shows "((P1_real_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = (ddh.DDH1 (P1_DDH_mal_adv_\<sigma>_true M z \<A> D))"
  including monad_normalisation
proof-
  have "(in2 = \<^bold>g [^] (r::nat) \<and> in3 = in1 [^] r \<and> in1 = \<^bold>g [^] (\<alpha>0::nat) \<otimes> inv (\<^bold>g [^] (\<alpha>1::nat)) 
          \<and> in2 = \<^bold>g [^] r \<and> in3 = (\<^bold>g [^] r) [^] \<alpha>0 \<otimes> \<^bold>g \<otimes> inv ((\<^bold>g [^] \<alpha>1) [^] r \<otimes> \<^bold>g))
          \<longleftrightarrow> (in1 = \<^bold>g [^] \<alpha>0 \<otimes> inv (\<^bold>g [^] \<alpha>1) \<and> in2 = \<^bold>g [^] r 
              \<and> in3 = (\<^bold>g [^] \<alpha>0) [^] r \<otimes> \<^bold>g \<otimes> inv ((\<^bold>g [^] r) [^] \<alpha>1 \<otimes> \<^bold>g))"
    for in1 in2 in3 r \<alpha>0 \<alpha>1
    by (auto simp add: P1_assert_correct1 power_swap)
  moreover have "((P1_real_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = ((\<^bold>g [^] r) [^] \<alpha>0) \<otimes> \<^bold>g;
    let b1 = (h1 [^] r) \<otimes> \<^bold>g;
    ((in1, in2, in3),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (b :: bool, _ :: unit) \<leftarrow> funct_DH_ZK (in1, in2, in3) ((h,a,b), r);
    _ :: unit \<leftarrow> assert_spmf (b); 
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    adv_out \<leftarrow> \<A>3 s';
    D (adv_out, ((z1 \<otimes> (inv w1 [^] \<alpha>1))))}"
    by(simp add: P1_real_model_def assms split_def Let_def power_swap)
  ultimately show ?thesis  
    by(simp add: Let_def P1_real_model_def ddh.DDH1_def assms power_swap)
qed

lemma P1_ideal_ddh0_\<sigma>_true:
  assumes "\<sigma> = True"
  shows "((P1_ideal_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = (ddh.DDH0 (P1_DDH_mal_adv_\<sigma>_true M z \<A> D))"
  including monad_normalisation
proof-
  have "((P1_ideal_model M \<sigma> z \<A>) \<bind> (\<lambda> view. D view)) = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    r \<leftarrow> sample_uniform (order \<G>);
    \<alpha>0 \<leftarrow> sample_uniform (order \<G>);
    \<alpha>1 \<leftarrow> sample_uniform (order \<G>);
    let h0 = \<^bold>g [^] \<alpha>0;
    let h1 = \<^bold>g [^] \<alpha>1;
    let a = \<^bold>g [^] r;
    let b0 = (\<^bold>g [^] r) [^] \<alpha>0;
    let b1 = h1 [^] r \<otimes> \<^bold>g;
    ((in1, in2, in3),s) \<leftarrow> \<A>1 M h0 h1 a b0 b1 z;
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    _ :: unit \<leftarrow> assert_spmf ((in1, in2, in3) = (h,a,b));
    (((w0,z0),(w1,z1)),s') \<leftarrow> \<A>2 h0 h1 a b0 b1 M s;
    let x0 = (z0 \<otimes> (inv w0 [^] \<alpha>0));
    let x1 = (z1 \<otimes> (inv w1 [^] \<alpha>1));
    (_, f_out2) \<leftarrow> funct_OT_12  (x0, x1) \<sigma>;
    adv_out \<leftarrow> \<A>3 s';
    D (adv_out, f_out2)}"
    by(simp add: P1_ideal_model_def assms Let_def split_def power_swap)
  thus ?thesis 
    by(simp add: split_def Let_def P1_ideal_model_def ddh.DDH0_def assms funct_OT_12_def power_swap) 
qed

lemma P1_real_ideal_DDH_advantage_false:
  assumes "\<sigma> = False" 
  shows "mal_def.adv_P1 M \<sigma> z (P1_S1, P1_S2) \<A> D = ddh.DDH_advantage (P1_DDH_mal_adv_\<sigma>_false M z \<A> D)"
  by(simp add: P1_adv_real_ideal_model_def ddh.DDH_advantage_def P1_ideal_ddh1_\<sigma>_false P1_real_ddh0_\<sigma>_false assms P1_advantages_eq)

lemma P1_real_ideal_DDH_advantage_false_bound:
  assumes "\<sigma> = False"
  shows "mal_def.adv_P1 M \<sigma> z (P1_S1, P1_S2) \<A> D 
          \<le> ddh.advantage (P1_DDH_mal_adv_\<sigma>_false M z \<A> D) 
            + ddh.advantage (ddh.DDH_\<A>' (P1_DDH_mal_adv_\<sigma>_false M z \<A> D))"
  using P1_real_ideal_DDH_advantage_false ddh.DDH_advantage_bound assms by metis

lemma P1_real_ideal_DDH_advantage_true:
  assumes "\<sigma> = True" 
  shows "mal_def.adv_P1 M \<sigma> z (P1_S1, P1_S2) \<A> D = ddh.DDH_advantage (P1_DDH_mal_adv_\<sigma>_true M z \<A> D)"
  by(simp add: P1_adv_real_ideal_model_def ddh.DDH_advantage_def P1_real_ddh1_\<sigma>_true P1_ideal_ddh0_\<sigma>_true assms P1_advantages_eq)

lemma P1_real_ideal_DDH_advantage_true_bound:
  assumes "\<sigma> = True"
  shows "mal_def.adv_P1 M \<sigma> z (P1_S1, P1_S2) \<A> D 
          \<le> ddh.advantage (P1_DDH_mal_adv_\<sigma>_true M z \<A> D) 
            + ddh.advantage (ddh.DDH_\<A>' (P1_DDH_mal_adv_\<sigma>_true M z \<A> D))"
  using P1_real_ideal_DDH_advantage_true ddh.DDH_advantage_bound assms by metis


(*Auxillary proofs that we use in the proof of security, mainly rewriting things for P2*)

lemma P2_output_rewrite:
  assumes "s < order \<G>"
  shows "(\<^bold>g [^] (r * u1 + v1),  \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] u1)
           = (\<^bold>g [^] (r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>),  
             \<^bold>g [^] (r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
               \<otimes> inv \<^bold>g [^] ((s + u1) mod order \<G> + (order \<G> - s)))"
proof-
  have "\<^bold>g [^] (r * u1 + v1) = \<^bold>g [^] (r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>)"
  proof-
    have "[(r * u1 + v1) = (r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>)] (mod (order \<G>))"
    proof-
      have "[(r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>) = r * (s + u1) + (r * order \<G> - r * s + v1)] (mod (order \<G>))" 
        by (metis (no_types, hide_lams) cong_def mod_add_left_eq mod_add_right_eq mod_mult_right_eq)
      hence "[(r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>) = r * s + r * u1 + r * order \<G> - r * s + v1] (mod (order \<G>))" 
        by (metis (no_types, lifting) Nat.add_diff_assoc add.assoc assms distrib_left less_or_eq_imp_le mult_le_mono)
      hence "[(r * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G>) = r * u1 + r * order \<G> + v1] (mod (order \<G>))" by simp
      thus ?thesis
        by (simp add: cong_def semiring_normalization_rules(23))
    qed 
    then show ?thesis using finite_group pow_generator_eq_iff_cong by blast
  qed
  moreover have " \<^bold>g [^] (r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
               \<otimes> inv \<^bold>g [^] ((s + u1) mod order \<G> + (order \<G> - s)) 
                    = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] u1" 
  proof-
    have "\<^bold>g [^] (r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>)"
    proof-
      have "[(r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) = r * \<alpha> * u1 + v1 * \<alpha>] (mod (order \<G>))"
      proof-
        have "[(r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * (s + u1) + (r * order \<G> - r * s + v1) * \<alpha>] (mod (order \<G>))" 
          using cong_def mod_add_cong mod_mult_left_eq mod_mult_right_eq by blast
        hence "[(r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * s + r * \<alpha> * u1 + (r * order \<G> - r * s + v1) * \<alpha>] (mod (order \<G>))"
          by (simp add: distrib_left)
        hence "[(r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * s + r * \<alpha> * u1 + r * order \<G> * \<alpha> - r * s * \<alpha> + v1 * \<alpha>] (mod (order \<G>))" using distrib_right assms 
          by (smt Groups.mult_ac(3) order_gt_0 Nat.add_diff_assoc2 add.commute diff_mult_distrib2 mult.commute mult_strict_mono order.strict_implies_order semiring_normalization_rules(25) zero_order(1))
        hence "[(r * \<alpha> * ((s + u1) mod order \<G>) + (r * order \<G> - r * s + v1) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * u1 + r * order \<G> * \<alpha> + v1 * \<alpha>] (mod (order \<G>))" by simp
        thus ?thesis
          by (simp add: cong_def semiring_normalization_rules(16) semiring_normalization_rules(23))
      qed
      thus ?thesis using finite_group pow_generator_eq_iff_cong by blast
    qed
    also have "inv \<^bold>g [^] ((s + u1) mod order \<G> + (order \<G> - s)) = inv \<^bold>g [^] u1"
    proof-
      have "[((s + u1) mod order \<G> + (order \<G> - s)) = u1] (mod (order \<G>))" 
      proof-
        have "[((s + u1) mod order \<G> + (order \<G> - s)) = s + u1 + (order \<G> - s)] (mod (order \<G>))" 
          by (simp add: add.commute mod_add_right_eq cong_def)
        hence "[((s + u1) mod order \<G> + (order \<G> - s)) = u1 + order \<G>] (mod (order \<G>))" 
          using assms by simp
        thus ?thesis by (simp add: cong_def)
      qed
      hence "\<^bold>g [^] ((s + u1) mod order \<G> + (order \<G> - s)) = \<^bold>g [^] u1"
        using finite_group pow_generator_eq_iff_cong by blast
      thus ?thesis 
        by (metis generator_closed inverse_pow_pow)
    qed
    ultimately show ?thesis by argo
  qed
  ultimately show ?thesis by simp
qed

lemma P2_inv_g_rewrite:
  assumes "s < order \<G>" 
  shows "(inv \<^bold>g) [^] (u1' + (order \<G> - s)) = \<^bold>g [^] s \<otimes> inv (\<^bold>g [^] u1')"
proof-
  have power_commute_rewrite: "\<^bold>g [^] (((order \<G> - s) + u1') mod order \<G>) =  \<^bold>g [^] (u1' + (order \<G> - s))" 
    using add.commute pow_generator_mod by metis
  have "(order \<G> - s + u1') mod order \<G> = (int (order \<G>) - int s + int u1') mod order \<G>" 
    by (metis of_nat_add of_nat_diff order.strict_implies_order zmod_int assms(1))
  also have "... = (- int s + int u1') mod order \<G>" 
    by (metis (full_types) add.commute minus_mod_self1 mod_add_right_eq)
  ultimately have "(order \<G> - s + u1') mod order \<G> = (- int s mod (order \<G>) + int u1' mod (order \<G>)) mod order \<G>" 
    by presburger
  hence "\<^bold>g [^] (((order \<G> - s) + u1') mod order \<G>)
              = \<^bold>g [^] ((- int s mod (order \<G>) + int u1' mod (order \<G>)) mod order \<G>)" 
    by (metis int_pow_int)
  hence "\<^bold>g [^] (u1' + (order \<G> - s))
              = \<^bold>g [^] ((- int s mod (order \<G>) + int u1' mod (order \<G>)) mod order \<G>)" 
    using power_commute_rewrite by argo
  also have "...
              = \<^bold>g [^] (- int s mod (order \<G>) + int u1' mod (order \<G>))" 
    using pow_generator_mod_int by blast
  also have "... = \<^bold>g [^] (- int s mod (order \<G>)) \<otimes> \<^bold>g [^] (int u1' mod (order \<G>))" 
    by (simp add: int_pow_mult)
  also have "... = \<^bold>g [^] (- int s) \<otimes> \<^bold>g [^] (int u1')" 
    using pow_generator_mod_int by simp
  ultimately have "inv (\<^bold>g [^] (u1' + (order \<G> - s))) = inv (\<^bold>g [^] (- int s) \<otimes> \<^bold>g [^] (int u1'))" by simp
  hence "inv (\<^bold>g [^] ((u1' + (order \<G> - s)) mod (order \<G>)) ) = inv (\<^bold>g [^] (- int s)) \<otimes> inv (\<^bold>g [^] (int u1'))"
    using pow_generator_mod 
    by (simp add: inverse_split)
  also have "... = \<^bold>g [^] (int s) \<otimes> inv (\<^bold>g [^] (int u1'))" 
    by (simp add: int_pow_neg)
  also have "... = \<^bold>g [^] s \<otimes> inv (\<^bold>g [^] u1')" 
    by (simp add: int_pow_int)
  ultimately show ?thesis 
    by (simp add: inverse_pow_pow pow_generator_mod )
qed

lemma P2_inv_g_s_rewrite:
  assumes "s < order \<G>" 
  shows "\<^bold>g [^] ((r::nat) * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] (u1 + (order \<G> - s)) = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> \<^bold>g [^] s \<otimes> inv \<^bold>g [^] u1"
proof-
  have in_carrier1: "inv \<^bold>g [^] (u1 + (order \<G> - s)) \<in> carrier \<G>" by blast
  have in_carrier2: "inv \<^bold>g [^] u1 \<in> carrier \<G>" by simp
  have in_carrier_3: "\<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<in> carrier \<G>" by simp
  have "\<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> (inv \<^bold>g [^] (u1 + (order \<G> - s))) =  \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> (\<^bold>g [^] s \<otimes> inv \<^bold>g [^] u1)"
    using P2_inv_g_rewrite assms  
    by (simp add: inverse_pow_pow)
  thus ?thesis using cyclic_group_assoc in_carrier1 in_carrier2 by auto
qed

lemma P2_e0_rewrite: 
  assumes "s < order \<G> "
  shows "(\<^bold>g [^] (r * x + xa), \<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>) \<otimes> \<^bold>g [^] x)  = 
            (\<^bold>g [^] (r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>),
               \<^bold>g [^] (r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  \<otimes> \<^bold>g [^] ((order \<G> - s + x) mod order \<G> + s))"
proof-
  have "\<^bold>g [^] (r * x + xa) = \<^bold>g [^] (r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>)"
  proof-
    have "[(r * x + xa) = (r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>)] (mod order \<G>)"
    proof-
      have "[(r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>) 
              = (r * ((order \<G> - s + x)) + (r * s + xa))] (mod order \<G>)"  
        by (metis (no_types, lifting) mod_mod_trivial cong_add cong_def mod_mult_right_eq)
      hence "[(r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>) 
              = r * (order \<G> - s) + r * x + r * s + xa] (mod order \<G>)" 
        by (simp add: add.assoc distrib_left)
      hence "[(r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>) 
              = r * x + r * s + r * (order \<G> - s) + xa] (mod order \<G>)" 
        by (metis add.assoc add.commute)
      hence "[(r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>) 
              = r * x + r * s + r * order \<G> - r * s + xa] (mod order \<G>)" 
      proof -
        have "[(xa + r * s) mod order \<G> + r * ((x + (order \<G> - s)) mod order \<G>) = xa + r * (s + x + (order \<G> - s))] (mod order \<G>)"
          by (metis (no_types) \<open>[r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> = r * x + r * s + r * (order \<G> - s) + xa] (mod order \<G>)\<close> add.commute distrib_left)
        then show ?thesis
          by (simp add: assms add.commute distrib_left order.strict_implies_order)
      qed
      hence "[(r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G>) 
              = r * x + xa] (mod order \<G>)" 
      proof -
        have "[(xa + r * s) mod order \<G> + r * ((x + (order \<G> - s)) mod order \<G>) = xa + (r * x + r * order \<G>)] (mod order \<G>)"
          by (metis (no_types) \<open>[r * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> = r * x + r * s + r * order \<G> - r * s + xa] (mod order \<G>)\<close> add.commute add.left_commute add_diff_cancel_left')
        then show ?thesis
          by (metis (no_types) add.commute cong_add_lcancel_nat cong_def distrib_left mod_add_self2 mod_mult_right_eq)
      qed
      then show ?thesis using cong_def by metis
    qed
    then show ?thesis using finite_group pow_generator_eq_iff_cong by blast
  qed
  moreover have "\<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>) \<otimes> \<^bold>g [^] x = 
              \<^bold>g [^] (r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  \<otimes> \<^bold>g [^] ((order \<G> - s + x) mod order \<G> + s)"
  proof-
    have "\<^bold>g [^] (r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                = \<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>)" 
    proof-
      have "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) = r * \<alpha> * x + xa * \<alpha>] (mod order \<G>)"
      proof-
        have "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = (r * \<alpha> * ((order \<G> - s) + x) + (r * s + xa) * \<alpha>)] (mod order \<G>)"
          by (metis (no_types, lifting) cong_add cong_def mod_mult_left_eq mod_mult_right_eq) 
        hence "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * (order \<G> - s) + r * \<alpha> * x + r * s * \<alpha> + xa * \<alpha>] (mod order \<G>)" 
          by (simp add: add.assoc distrib_left distrib_right)
        hence "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * (order \<G> - s) + xa * \<alpha>] (mod order \<G>)" 
          by (simp add: add.commute add.left_commute)
        hence "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * order \<G> - r * \<alpha> * s + xa * \<alpha>] (mod order \<G>)" 
        proof -
          have "\<forall>n na. \<not> (n::nat) \<le> na \<or> n + (na - n) = na"
            by (meson ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
          then have "r * \<alpha> * s + r * \<alpha> * (order \<G> - s) = r * \<alpha> * order \<G>"
            by (metis add_mult_distrib2 assms less_or_eq_imp_le)
          then have "r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * order \<G> = r * \<alpha> * s + r * \<alpha> * (order \<G> - s) + (r * \<alpha> * x + r * s * \<alpha>)"
            by presburger
          then have f1: "r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * order \<G> - r * \<alpha> * s = r * \<alpha> * s + r * \<alpha> * (order \<G> - s) - r * \<alpha> * s + (r * \<alpha> * x + r * s * \<alpha>)"
            by simp
          have "r * \<alpha> * s + r * \<alpha> * (order \<G> - s) = r * \<alpha> * (order \<G> - s) + r * \<alpha> * s"
            by presburger
          then have "r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * order \<G> - r * \<alpha> * s = r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * (order \<G> - s)"
            using f1 diff_add_inverse2 by presburger
          then show ?thesis
            using \<open>[r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha> = r * \<alpha> * x + r * s * \<alpha> + r * \<alpha> * (order \<G> - s) + xa * \<alpha>] (mod order \<G>)\<close> by presburger
        qed
        hence "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * x + r * \<alpha> * s + r * \<alpha> * order \<G> - r * \<alpha> * s + xa * \<alpha>] (mod order \<G>)" 
          using add.commute add.assoc by force
        hence "[(r * \<alpha> * ((order \<G> - s + x) mod order \<G>) + (r * s + xa) mod order \<G> * \<alpha>) 
                  = r * \<alpha> * x + r * \<alpha> * order \<G> + xa * \<alpha>] (mod order \<G>)" by simp
        thus ?thesis using cong_def semiring_normalization_rules(23) 
          by (simp add: \<open>\<And>c b a. [b = c] (mod a) = (b mod a = c mod a)\<close> \<open>\<And>c b a. a + b + c = a + c + b\<close>)
      qed
      thus ?thesis using finite_group pow_generator_eq_iff_cong by blast
    qed
    also have "\<^bold>g [^] ((order \<G> - s + x) mod order \<G> + s) = \<^bold>g [^] x"
    proof-
      have "[((order \<G> - s + x) mod order \<G> + s) = x] (mod order \<G>)" 
      proof-
        have "[((order \<G> - s + x) mod order \<G> + s) = (order \<G> - s + x+ s)] (mod order \<G>)" 
          by (simp add: add.commute cong_def mod_add_right_eq)
        hence "[((order \<G> - s + x) mod order \<G> + s) = (order \<G> + x)] (mod order \<G>)" 
          using assms by auto
        thus ?thesis
          by (simp add: cong_def)
      qed
      thus ?thesis using finite_group pow_generator_eq_iff_cong by blast
    qed
    ultimately show ?thesis by argo
  qed
  ultimately show ?thesis by simp
qed

lemma P2_case_l_new_1_gt_e0_rewrite:
  assumes "s < order \<G>"
  shows "(\<^bold>g [^] (r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
            + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>),
              \<^bold>g [^] (r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>) \<otimes>
                  \<^bold>g [^] (t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> 
                    + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))) = (\<^bold>g [^] (r * x + xa), \<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>) \<otimes> \<^bold>g [^] (t * x))"
proof-
  have "\<^bold>g [^] ((r::nat) * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>)
                   + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>)
                                = \<^bold>g [^] (r * x + xa)"
  proof(cases "r = 0")
    case True
    then show ?thesis 
      by (simp add: pow_generator_mod)
  next
    case False
    have "[(r::nat) * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>)
                  + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> = r * x + xa] (mod order \<G>)"
    proof-
      have "[r * ((order \<G> * order \<G> - s * (nat (fst (bezw t (order \<G>))) mod order \<G>) + x) mod order \<G>) 
                  + (r * s * nat (fst (bezw t (order \<G>))) + xa) mod order \<G>
                        =  (r * (((order \<G> * order \<G> - s * (nat (fst (bezw t (order \<G>))) mod order \<G>)) + x)) 
                              + (r * s * nat (fst (bezw t (order \<G>))) + xa))] (mod order \<G>)" 
      proof -
        have "order \<G> \<noteq> 0"
          using order_gt_0 by simp
        then show ?thesis
          using  cong_add cong_def mod_mult_right_eq 
          by (smt mod_mod_trivial)
      qed
      hence "[r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                  + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>
                        =  r * (order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))) + r * x 
                              + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa)] (mod order \<G>)" 
      proof -
        have "[r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                = r * (order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))) + r * x] (mod order \<G>)"
          by (simp add: cong_def distrib_left mod_mult_right_eq)
        then show ?thesis
          using assms cong_add gr_implies_not0 by fastforce
      qed
      hence "[r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                    + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>
                          =  r * order \<G> * order \<G> - r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + r * x 
                                + r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa] (mod order \<G>)" 
        by (simp add: ab_semigroup_mult_class.mult_ac(1) right_diff_distrib' add.assoc)
      hence "[r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                    + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>
                          =  r * order \<G> * order \<G> + r * x + xa] (mod order \<G>)" 
      proof-
        have "r * order \<G> * order \<G> - r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) > 0" 
        proof-
          have "order \<G> * order \<G> > s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))" 
          proof- 
            have "(nat ((fst (bezw t (order \<G>))) mod order \<G>)) \<le> order \<G>" 
            proof -
              have "\<forall>x0 x1. ((x0::int) mod x1 < x1) = (\<not> x1 + - 1 * (x0 mod x1) \<le> 0)"
                by linarith
              then have "\<not> int (order \<G>) + - 1 * (fst (bezw t (order \<G>)) mod int (order \<G>)) \<le> 0"
                using of_nat_0_less_iff order_gt_0 by fastforce
              then show ?thesis
                by linarith
            qed
            thus ?thesis using assms 
            proof -
              have "\<forall>n na. \<not> n \<le> na \<or> \<not> na * order \<G> < n * nat (fst (bezw t (order \<G>)) mod int (order \<G>))"
                by (meson \<open>nat (fst (bezw (t::nat) (order \<G>)) mod int (order \<G>)) \<le> order \<G>\<close> mult_le_mono not_le)
              then show ?thesis
                by(metis  (no_types, hide_lams) \<open>(s::nat) < order \<G>\<close> mult_less_cancel2 nat_less_le not_le not_less_zero)
            qed
          qed
          thus ?thesis using False
            by auto
        qed
        thus ?thesis 
        proof -
          have "r * order \<G> * order \<G> + r * x + xa = r * (order \<G> * order \<G> - s * nat (fst (bezw t (order \<G>)) mod int (order \<G>))) + (r * s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) + xa) + r * x"
            using \<open>(0::nat) < (r::nat) * order \<G> * order \<G> - r * (s::nat) * nat (fst (bezw (t::nat) (order \<G>)) mod int (order \<G>))\<close> diff_mult_distrib2 by force
          then show ?thesis
            by (metis (no_types) \<open>[(r::nat) * ((order \<G> * order \<G> - (s::nat) * nat (fst (bezw (t::nat) (order \<G>)) mod int (order \<G>)) + (x::nat)) mod order \<G>) + (r * s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) + (xa::nat)) mod order \<G> = r * (order \<G> * order \<G> - s * nat (fst (bezw t (order \<G>)) mod int (order \<G>))) + r * x + (r * s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) + xa)] (mod order \<G>)\<close> semiring_normalization_rules(23))
        qed
      qed
      hence "[r * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                    + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G>
                          = r * x + xa] (mod order \<G>)" 
        by (metis (no_types, lifting) mod_mult_self4 add.assoc mult.commute cong_def)
      thus ?thesis by blast
    qed
    then show ?thesis using finite_group pow_generator_eq_iff_cong by blast
  qed
  moreover have "\<^bold>g [^] (r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) 
                      + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>) \<otimes>
                             \<^bold>g [^] (t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> 
                                  + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))
                                      =  \<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>) \<otimes> \<^bold>g [^] (t * x)"
  proof-
    have "\<^bold>g [^] (r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>)
              = \<^bold>g [^] (r * \<alpha> * x + xa * \<alpha>)"
    proof-
      have "[r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>
                  = r * \<alpha> * x + xa * \<alpha>] (mod order \<G>)"
      proof-
        have "[r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>
                  = r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))) + x) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) * \<alpha>] (mod order \<G>)"
        proof -
          show ?thesis
            by (meson cong_def mod_add_cong mod_mult_left_eq mod_mult_right_eq)
        qed 
        hence mod_eq: "[r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>
                  = r * \<alpha> * (order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))) + r * \<alpha> * x + r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) * \<alpha> + xa * \<alpha>] (mod order \<G>)"
          by (simp add: distrib_left distrib_right add.assoc)
        hence mod_eq': "[r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>
                  = r * \<alpha> * order \<G> * order \<G> - r * \<alpha> * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + r * \<alpha> * x + r * \<alpha> * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa * \<alpha>] (mod order \<G>)"
          by (simp add: semiring_normalization_rules(16) diff_mult_distrib2 semiring_normalization_rules(18))
        hence "[r * \<alpha> * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G>) + (r * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + xa) mod order \<G> * \<alpha>
                  = r * \<alpha> * order \<G> * order \<G> + r * \<alpha> * x + xa * \<alpha>] (mod order \<G>)"
        proof(cases "r * \<alpha> = 0")
          case True
          then show ?thesis 
            by (metis mod_eq' diff_zero mult_0 plus_nat.add_0)
        next
          case False
          hence bound: " r * \<alpha> * order \<G> * order \<G> - r * \<alpha> * s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) > 0" 
          proof-
            have "s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) < order \<G> * order \<G>" 
              using assms 
              by (simp add: mult_strict_mono nat_less_iff)
            thus ?thesis 
              using False by auto
          qed
          thus ?thesis 
          proof -
            have "r * \<alpha> * order \<G> * order \<G> = r * \<alpha> * (order \<G> * order \<G> - s * nat (fst (bezw t (order \<G>)) mod int (order \<G>))) 
                                                      + r * s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) * \<alpha>"
              using bound diff_mult_distrib2 by force
            then have "r * \<alpha> * order \<G> * order \<G> + r * \<alpha> * x = r * \<alpha> * (order \<G> * order \<G> - s * nat (fst (bezw t (order \<G>)) mod int (order \<G>))) 
                                                                  + r * \<alpha> * x + r * s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) * \<alpha>"
              by presburger
            then show ?thesis
              using mod_eq by presburger
          qed
        qed
        thus ?thesis 
          by (metis (mono_tags, lifting) add.assoc cong_def mod_mult_self3)
      qed
      then show ?thesis using finite_group pow_generator_eq_iff_cong by blast
    qed
    also have "\<^bold>g [^] (t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))
                    = \<^bold>g [^] (t * x)"
    proof-
      have "[t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))) = t * x] (mod order \<G>)"
      proof-
        have "[t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))
                    = (t * (order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))] (mod order \<G>)"
          using cong_def mod_add_left_eq mod_mult_cong by blast
        hence "[t * ((order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + x) mod order \<G> + s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))
                    = t * (order \<G> * order \<G> + x )] (mod order \<G>)"
        proof-
          have "order \<G> * order \<G> - s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)) > 0" 
          proof-
            have "(nat ((fst (bezw t (order \<G>))) mod order \<G>)) \<le> order \<G>" 
              using nat_le_iff order.strict_implies_order order_gt_0
              by (simp add: order.strict_implies_order)
            thus ?thesis 
              by (metis assms diff_mult_distrib le0 linorder_neqE_nat mult_strict_mono not_le zero_less_diff)
          qed
          thus ?thesis 
            using \<open>[(t::nat) * ((order \<G> * order \<G> - (s::nat) * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) + (x::nat)) mod order \<G> + s * nat (fst (bezw t (order \<G>)) mod int (order \<G>))) = t * (order \<G> * order \<G> - s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)) + x + s * nat (fst (bezw t (order \<G>)) mod int (order \<G>)))] (mod order \<G>)\<close> by auto
        qed
        thus ?thesis 
          by (metis (no_types, hide_lams) add.commute cong_def mod_mult_right_eq mod_mult_self1)
      qed
      thus ?thesis using finite_group pow_generator_eq_iff_cong  by blast
    qed
    ultimately show ?thesis by argo
  qed
  ultimately show ?thesis by simp
qed

lemma P2_case_l_neq_1_gt_x0_rewrite:
  assumes "t < order \<G>" 
    and "t \<noteq> 0"
  shows "\<^bold>g [^] (t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))) = \<^bold>g [^] (t * u0) \<otimes>  \<^bold>g [^] s"
proof-
  from assms have gcd: "gcd t (order \<G>) = 1" 
    using prime_field coprime_imp_gcd_eq_1 by blast
  hence inverse_t: "[ s * (t * (fst (bezw t (order \<G>)))) = s * 1] (mod order \<G>)" 
    by (metis Num.of_nat_simps(2) Num.of_nat_simps(5) cong_scalar_left order_gt_0 inverse) 
  hence inverse_t': "[t * u0 + s * (t * (fst (bezw t (order \<G>)))) =t * u0 + s * 1] (mod order \<G>)"
    using cong_add_lcancel by fastforce
  have eq: "int (nat ((fst (bezw t (order \<G>))) mod order \<G>)) = (fst (bezw t (order \<G>))) mod order \<G>" 
  proof-
    have "(fst (bezw t (order \<G>))) mod order \<G> \<ge> 0" using order_gt_0 by simp
    hence "(nat ((fst (bezw t (order \<G>))) mod order \<G>)) = (fst (bezw t (order \<G>))) mod order \<G>" by linarith
    thus ?thesis by blast 
  qed
  have "[(t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))) = t * u0 + s] (mod order \<G>)"
  proof-
    have "[t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))) = t * u0 + t * (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))] (mod order \<G>)"
      by (simp add: distrib_left)
    hence "[t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))) = t * u0 + s * (t * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))] (mod order \<G>)"
      by (simp add: ab_semigroup_mult_class.mult_ac(1) mult.left_commute)
    hence "[t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))) = t * u0 + s * (t * ( ((fst (bezw t (order \<G>))) mod order \<G>)))] (mod order \<G>)"
      using eq 
      by (simp add: distrib_left mult.commute semiring_normalization_rules(18))
    hence "[t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))) = t * u0 + s * (t * (fst (bezw t (order \<G>))))] (mod order \<G>)"
      by (metis (no_types, hide_lams) cong_def mod_add_right_eq mod_mult_right_eq)
    hence "[t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))) = t * u0 + s * 1] (mod order \<G>)" using inverse_t'  
      using cong_trans cong_int_iff by blast
    thus ?thesis by simp
  qed
  hence "\<^bold>g [^] (t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>))))) = \<^bold>g [^] (t * u0 + s)" using finite_group pow_generator_eq_iff_cong by blast
  thus ?thesis 
    by (simp add: nat_pow_mult)
qed

text \<open> Now we show the two end definitions are equal when the input for l (in the ideal model, the second input) is the one constructed by the simulator \<close>

lemma P2_ideal_real_end_eq:
  assumes b0_inv_b1: "b0 \<otimes> inv b1 = (h0 \<otimes> inv h1) [^] r"
    and assert_in_carrier: "h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>"
    and x1_in_carrier: "x1 \<in> carrier \<G>" 
    and x0_in_carrier: "x0 \<in> carrier \<G>"
  shows "P2_ideal_model_end (x0,x1) (b0 \<otimes> (inv (h0 [^] r))) ((h0,h1, \<^bold>g [^] (r::nat),b0,b1),s') \<A>3 = P2_real_model_end (x0,x1) ((h0,h1, \<^bold>g [^] (r::nat),b0,b1),s') \<A>3"
  including monad_normalisation
proof(cases "(b0 \<otimes> (inv (h0 [^] r))) = \<one>") \<comment> \<open> The case distinctions follow the 3 cases give on p 193/194*) \<close>
  case True
  have b1_h1: "b1 = h1 [^] r" 
  proof-
    from b0_inv_b1 assert_in_carrier have "b0 \<otimes> inv b1 = h0 [^] r \<otimes> inv h1 [^] r" 
      by (simp add: pow_mult_distrib cyclic_group_commute monoid_comm_monoidI)
    hence "b0 \<otimes> inv h0 [^] r = b1 \<otimes> inv h1 [^] r"
      by (metis Units_eq Units_l_cancel local.inv_equality True assert_in_carrier 
              cyclic_group.inverse_pow_pow cyclic_group_axioms 
                  inv_closed nat_pow_closed r_inv)
    with True have "\<one> = b1 \<otimes> inv h1 [^] r" 
      by (simp add: assert_in_carrier inverse_pow_pow)
    hence "\<one> \<otimes> h1 [^] r = b1" 
      by (metis assert_in_carrier cyclic_group.inverse_pow_pow cyclic_group_axioms inv_closed inv_inv l_one local.inv_equality nat_pow_closed) 
    thus ?thesis 
      using assert_in_carrier l_one by blast
  qed
  obtain \<alpha> :: nat where \<alpha>: "\<^bold>g [^] \<alpha> = h1" and "\<alpha> < order \<G>"
    by (metis mod_less_divisor assert_in_carrier generatorE order_gt_0 pow_generator_mod) 
  obtain s :: nat where s: "\<^bold>g [^] s = x1" and s_lt: "s < order \<G>"  
    by (metis assms(3) mod_less_divisor generatorE order_gt_0 pow_generator_mod)
  have "b1 \<otimes> inv \<^bold>g = \<^bold>g [^] (r * \<alpha>) \<otimes> inv \<^bold>g" 
    by (metis \<alpha> b1_h1 generator_closed mult.commute nat_pow_pow)
  have a_g_exp_rewrite: "(\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0 =  \<^bold>g [^] (r * u0 + v0)" 
    for u0 v0 
    by (simp add: nat_pow_mult nat_pow_pow)
  have z1_rewrite: "(b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> \<one> = \<^bold>g [^] (r * \<alpha> * u1 +  v1 * \<alpha>) \<otimes> inv \<^bold>g [^] u1" 
    for u1 v1 :: nat 
    by (smt \<alpha> b1_h1 pow_mult_distrib cyclic_group_commute generator_closed inv_closed m_assoc m_closed monoid_comm_monoidI mult.commute nat_pow_closed nat_pow_mult nat_pow_pow r_one) 
  have z1_rewrite': "\<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> \<^bold>g [^] s \<otimes>  inv \<^bold>g [^] u1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1"
    for u1 v1 
    using assert_in_carrier cyclic_group_commute m_assoc s z1_rewrite by auto
  have "P2_ideal_model_end (x0,x1) (b0 \<otimes> (inv (h0 [^] r))) ((h0,h1, \<^bold>g [^] (r::nat),b0,b1),s') \<A>3 = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> \<one>;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: P2_ideal_model_end_def True funct_OT_12_def)
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] u1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: z1_rewrite)
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = \<^bold>g [^] (r * u1 + v1);
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] u1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: a_g_exp_rewrite)
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> map_spmf (\<lambda> u1'. (s + u1') mod (order \<G>)) (sample_uniform (order \<G>));
    v1 \<leftarrow> map_spmf (\<lambda> v1'. ((r * order \<G> - r * s) + v1')  mod (order \<G>)) (sample_uniform (order \<G>));
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = \<^bold>g [^] (r * u1 + v1);
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] (u1 + (order \<G> - s));
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    apply(simp add: bind_map_spmf o_def Let_def)
    using P2_output_rewrite assms s_lt assms by presburger 
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = \<^bold>g [^] (r * u1 + v1);
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> inv \<^bold>g [^] (u1 + (order \<G> - s));
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: samp_uni_plus_one_time_pad)
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = \<^bold>g [^] (r * u1 + v1);
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = \<^bold>g [^] (r * \<alpha> * u1 + v1 * \<alpha>) \<otimes> \<^bold>g [^] s \<otimes>  inv \<^bold>g [^] u1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: P2_inv_g_s_rewrite assms s_lt cong: bind_spmf_cong_simp)
  also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
    by(simp add: a_g_exp_rewrite z1_rewrite')
  ultimately show ?thesis 
    by(simp add: P2_real_model_end_def)
next
  obtain \<alpha> :: nat where \<alpha>: "\<^bold>g [^] \<alpha> = h0"  
    using generatorE assms  
    using assert_in_carrier by auto 
  have w0_rewrite: "\<^bold>g [^] (r * u0 + v0) =  (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0"
    for u0 v0 
    by (simp add: nat_pow_mult nat_pow_pow)
  have order_gt_0: "order \<G> > 0" using order_gt_0 by simp
  obtain s :: nat where s: "\<^bold>g [^] s = x0" and s_lt: "s < order \<G>" 
    by (metis mod_less_divisor generatorE order_gt_0 pow_generator_mod x0_in_carrier)
  case False \<comment> \<open>case 2\<close>
  hence l_neq_1: "(b0 \<otimes> (inv (h0 [^] r))) \<noteq> \<one>"by auto
  then show ?thesis 
  proof(cases "(b0 \<otimes> (inv (h0 [^] r))) = \<^bold>g")
    case True
    hence "b0 = \<^bold>g \<otimes> h0 [^] r" 
      by (metis assert_in_carrier generator_closed inv_solve_right nat_pow_closed) 
    hence "b0 = \<^bold>g \<otimes> \<^bold>g [^] (r * \<alpha>)" 
      by (metis \<alpha> generator_closed mult.commute nat_pow_pow)
    have z0_rewrite: "b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> \<one> = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] u0" 
      for u0 v0 :: nat 
      by (smt \<alpha> \<open>b0 = \<^bold>g \<otimes> \<^bold>g [^] (r * \<alpha>)\<close> pow_mult_distrib cyclic_group_commute generator_closed m_assoc monoid_comm_monoidI mult.commute nat_pow_closed nat_pow_mult nat_pow_pow r_one)
    have z0_rewrite': "\<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (u0 + s) =  \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] u0 \<otimes> \<^bold>g [^] s"
      for u0 v0
      by (simp add: add.assoc nat_pow_mult)
    have z0_rewrite'': "\<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] u0 \<otimes> x0 =  b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0"
      for u0 v0 using z0_rewrite 
      using assert_in_carrier by auto
    have "P2_ideal_model_end (x0,x1) (b0 \<otimes> (inv (h0 [^] r))) ((h0,h1,\<^bold>g [^] (r::nat),b0,b1),s') \<A>3 = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> \<one>;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      apply(simp add: P2_ideal_model_end_def True funct_OT_12_def) 
      using order_gt_0 order_gt_1_gen_not_1 True l_neq_1 by auto 
    also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] u0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: z0_rewrite w0_rewrite)
    also have "... = do {
    u0 \<leftarrow> map_spmf (\<lambda> u0. ((order \<G> - s) + u0) mod (order \<G>)) (sample_uniform (order \<G>));
    v0 \<leftarrow> map_spmf (\<lambda> v0. (r * s + v0) mod (order \<G>)) (sample_uniform (order \<G>));
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (u0 + s);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      apply(simp add: bind_map_spmf o_def Let_def cong: bind_spmf_cong_simp)
      using P2_e0_rewrite assms s_lt assms by presburger 
    also have "... = do {
    u0 \<leftarrow> map_spmf (\<lambda> u0. ((order \<G> - s) + u0) mod (order \<G>)) (sample_uniform (order \<G>));
    v0 \<leftarrow> map_spmf (\<lambda> v0. (r * s + v0) mod (order \<G>)) (sample_uniform (order \<G>));
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] u0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: z0_rewrite' s)
    also have "... = do {
    u0 \<leftarrow> map_spmf (\<lambda> u0. ((order \<G> - s) + u0) mod (order \<G>)) (sample_uniform (order \<G>));
    v0 \<leftarrow> map_spmf (\<lambda> v0. (r * s + v0) mod (order \<G>)) (sample_uniform (order \<G>));
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: w0_rewrite z0_rewrite'')
    also have "... = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: samp_uni_plus_one_time_pad)
    ultimately show ?thesis 
      by(simp add: P2_real_model_end_def)
  next 
    case False \<comment> \<open>case 3\<close>
    have b0_l: "b0 = (b0 \<otimes> (inv (h0 [^] r))) \<otimes> h0 [^] r"
      by (simp add: assert_in_carrier m_assoc)
    have b0_g_r:"b0 = (b0 \<otimes> (inv (h0 [^] r))) \<otimes> \<^bold>g [^] (r * \<alpha>)"
      by (metis \<alpha> b0_l generator_closed mult.commute nat_pow_pow)
    obtain t :: nat where t: "\<^bold>g [^] t = (b0 \<otimes> (inv (h0 [^] r)))" and t_lt_order_g: "t < order \<G>"
      by (metis (full_types) mod_less_divisor order_gt_0 pow_generator_mod 
                assert_in_carrier cyclic_group.generatorE cyclic_group_axioms 
                      inv_closed m_closed nat_pow_closed)
    with l_neq_1 have t_neq_0: "t \<noteq> 0" using l_neq_1_exp_neq_0 by simp
    have z0_rewrite: "b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> \<one> = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0"
      for u0 v0 
    proof-
      from b0_l have "b0 [^] u0 \<otimes> h0 [^] v0 = ((b0 \<otimes> (inv (h0 [^] r))) \<otimes> h0 [^] r) [^] u0 \<otimes> h0 [^] v0" by simp
      hence "b0 [^] u0 \<otimes> h0 [^] v0 = ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0 \<otimes> (h0 [^] r) [^] u0 \<otimes> h0 [^] v0" 
        by (simp add: assert_in_carrier pow_mult_distrib cyclic_group_commute monoid_comm_monoidI)
      hence "b0 [^] u0 \<otimes> h0 [^] v0 = ((\<^bold>g [^] \<alpha>) [^] r) [^] u0 \<otimes> (\<^bold>g [^] \<alpha>) [^] v0 \<otimes> ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0" 
        using cyclic_group_assoc cyclic_group_commute assert_in_carrier \<alpha> by simp 
      hence "b0 [^] u0 \<otimes> h0 [^] v0 =  \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes>  ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0" 
        by (simp add: monoid.nat_pow_pow mult.commute nat_pow_mult)
      thus ?thesis 
        by (simp add: assert_in_carrier)
    qed
    have z0_rewrite': "\<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0 =  \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * u0)"
      for u0 v0 
      by (metis generator_closed nat_pow_pow t)
    have z0_rewrite'': "\<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * u0) \<otimes> \<^bold>g [^] s =  b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0"
      for u0 v0 
      using assert_in_carrier s z0_rewrite z0_rewrite' by auto
    have "P2_ideal_model_end (x0,x1) (b0 \<otimes> (inv (h0 [^] r))) ((h0,h1,\<^bold>g [^] (r::nat),b0,b1),s') \<A>3 = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> ((b0 \<otimes> (inv (h0 [^] r)))) [^] u0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
      by(simp add: P2_ideal_model_end_def l_neq_1 funct_OT_12_def w0_rewrite z0_rewrite)
    also have "...  = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * u0);
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
      by(simp add: z0_rewrite')
    also have "...  = do {
    u0 \<leftarrow> map_spmf (\<lambda> u0. (order \<G> * order \<G> - (s * ((nat (((fst (bezw t (order \<G>)))) mod (order \<G>))))) + u0) mod (order \<G>)) (sample_uniform (order \<G>));
    v0 \<leftarrow> map_spmf (\<lambda> v0. (r * s *  (nat ((fst (bezw t (order \<G>))) mod order \<G>)) + v0) mod (order \<G>)) (sample_uniform (order \<G>));
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))));
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
      by(simp add: bind_map_spmf o_def Let_def s_lt P2_case_l_new_1_gt_e0_rewrite cong: bind_spmf_cong_simp)
    also have "...  = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * (u0 + (s * (nat ((fst (bezw t (order \<G>))) mod order \<G>)))));
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}"
      by(simp add: samp_uni_plus_one_time_pad)
    also have "...  = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = \<^bold>g [^] (r * u0 + v0);
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = \<^bold>g [^] (r * \<alpha> * u0 + v0 * \<alpha>) \<otimes> \<^bold>g [^] (t * u0) \<otimes> \<^bold>g [^] s;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: P2_case_l_neq_1_gt_x0_rewrite t_lt_order_g t_neq_0 cyclic_group_assoc)
    also have "...  = do {
    u0 \<leftarrow> sample_uniform (order \<G>);
    v0 \<leftarrow> sample_uniform (order \<G>);
    u1 \<leftarrow> sample_uniform (order \<G>);
    v1 \<leftarrow> sample_uniform (order \<G>);
    let w0 = (\<^bold>g [^] (r::nat)) [^] u0 \<otimes> \<^bold>g [^] v0;
    let w1 = (\<^bold>g [^] (r::nat)) [^] u1 \<otimes> \<^bold>g [^] v1;
    let z0 = b0 [^] u0 \<otimes> h0 [^] v0 \<otimes> x0;
    let z1 = (b1 \<otimes> inv \<^bold>g) [^] u1 \<otimes> h1 [^] v1 \<otimes> x1;
    let e0 = (w0,z0);
    let e1 = (w1,z1);
    out \<leftarrow> \<A>3 e0 e1 s';
    return_spmf ((), out)}" 
      by(simp add: w0_rewrite z0_rewrite'')
    ultimately show ?thesis 
      by(simp add: P2_real_model_end_def)
  qed
qed

lemma P2_ideal_real_eq: 
  assumes x1_in_carrier: "x1 \<in> carrier \<G>" 
    and x0_in_carrier: "x0 \<in> carrier \<G>"  
  shows "P2_real_model (x0,x1) \<sigma>  z \<A>  = P2_ideal_model (x0,x1) \<sigma>  z \<A>"
proof-
  have "P2_real_model' (x0, x1) \<sigma>  z \<A> = P2_ideal_model' (x0, x1) \<sigma>  z \<A>"
  proof-
    have 1:"do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    let l = b0 \<otimes> (inv (h0 [^] r));
    P2_ideal_model_end (x0,x1) l ((h0,h1,a,b0,b1),s') \<A>3} = P2_ideal_model' (x0,x1) \<sigma> z \<A>"
      unfolding P2_ideal_model'_def by simp
    have "P2_real_model' (x0, x1) \<sigma>  z \<A> = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    P2_real_model_end (x0, x1) ((h0,h1,a,b0,b1),s') \<A>3}"
      by(simp add: P2_real_model'_def)
    also have "... = do {
    let (\<A>1, \<A>2, \<A>3) = \<A>;
    ((h0,h1,a,b0,b1),s) \<leftarrow> \<A>1 \<sigma> z;
    _ :: unit \<leftarrow> assert_spmf (h0 \<in> carrier \<G> \<and> h1 \<in> carrier \<G>  \<and> a \<in> carrier \<G> \<and> b0 \<in> carrier \<G> \<and> b1 \<in> carrier \<G>);
    (((in1, in2, in3), r),s') \<leftarrow> \<A>2 (h0,h1,a,b0,b1) s; 
    let (h,a,b) = (h0 \<otimes> inv h1, a, b0 \<otimes> inv b1);
    (out_zk_funct, _) \<leftarrow> funct_DH_ZK (h,a,b) ((in1, in2, in3), r);  
    _ :: unit \<leftarrow> assert_spmf out_zk_funct;
    let l = b0 \<otimes> (inv (h0 [^] r));
    P2_ideal_model_end (x0,x1) l ((h0,h1,a,b0,b1),s') \<A>3}"
      by(simp add: P2_ideal_real_end_eq assms cong: bind_spmf_cong_simp)  
    ultimately show ?thesis  by(simp add: P2_real_model'_def P2_ideal_model'_def)
  qed
  thus ?thesis by(simp add: P2_ideal_model_rewrite P2_real_model_rewrite)
qed

lemma malicious_sec_P2:   
  assumes x1_in_carrier: "x1 \<in> carrier \<G>"
    and x0_in_carrier: "x0 \<in> carrier \<G>"  
  shows "mal_def.perfect_sec_P2 (x0,x1) \<sigma> z (P2_S1, P2_S2) \<A>"
  unfolding malicious_base.perfect_sec_P2_def
  by (simp add: P2_ideal_real_eq P2_ideal_view_unfold assms)

(*correctness*)

lemma correct:
  assumes "x0 \<in> carrier \<G>" 
    and "x1 \<in> carrier \<G>"
  shows "funct_OT_12 (x0, x1) \<sigma> = protocol_ot (x0,x1) \<sigma>"
proof-
  have \<sigma>_eq_0_output_correct:
    "((\<^bold>g [^] \<alpha>0) [^] r) [^] u0 \<otimes> (\<^bold>g [^] \<alpha>0) [^] v0 \<otimes> x0 \<otimes>
                      inv (((\<^bold>g [^] r) [^] u0 \<otimes> \<^bold>g [^] v0) [^] \<alpha>0) = x0"
    (is "?lhs = ?rhs")
    for \<alpha>0 r u0 v0 :: nat
  proof-
    have mult_com: "r * u0 * \<alpha>0 = \<alpha>0 * r * u0" by simp
    have in_carrier1: "((\<^bold>g [^] (r  * u0 * \<alpha>0))) \<otimes> (\<^bold>g [^] (v0 * \<alpha>0)) \<in> carrier \<G>" by simp
    have in_carrier2: "inv ((\<^bold>g [^] (r  * u0 * \<alpha>0))) \<otimes> (\<^bold>g [^] (v0 * \<alpha>0)) \<in> carrier \<G>" by simp
    have "?lhs = ((\<^bold>g [^] (\<alpha>0 * r * u0))) \<otimes> (\<^bold>g [^] (\<alpha>0 * v0)) \<otimes> x0 \<otimes>
                        inv (((\<^bold>g [^] (r  * u0 * \<alpha>0)) \<otimes> \<^bold>g [^] (v0 * \<alpha>0)))" 
      by (simp add: nat_pow_pow pow_mult_distrib cyclic_group_commute monoid_comm_monoidI)
    also have "... = (((\<^bold>g [^] (r  * u0 * \<alpha>0))) \<otimes> (\<^bold>g [^] (v0 * \<alpha>0))) \<otimes> x0 \<otimes>
                        (inv (((\<^bold>g [^] (r  * u0 * \<alpha>0)) \<otimes> \<^bold>g [^] (v0 * \<alpha>0))))" 
      using mult.commute mult.assoc mult_com   
      by (metis (no_types) mult.commute) 
    also have "... = x0 \<otimes> (((\<^bold>g [^] (r  * u0 * \<alpha>0))) \<otimes> (\<^bold>g [^] (v0 * \<alpha>0))) \<otimes>
                        (inv (((\<^bold>g [^] (r  * u0 * \<alpha>0)) \<otimes> \<^bold>g [^] (v0 * \<alpha>0))))"
      using cyclic_group_commute in_carrier1 assms by simp
    also have "... = x0 \<otimes> ((((\<^bold>g [^] (r  * u0 * \<alpha>0))) \<otimes> (\<^bold>g [^] (v0 * \<alpha>0))) \<otimes>
                        (inv (((\<^bold>g [^] (r  * u0 * \<alpha>0)) \<otimes> \<^bold>g [^] (v0 * \<alpha>0)))))"
      using cyclic_group_assoc in_carrier1 in_carrier2 assms by auto
    ultimately show ?thesis using assms by simp
  qed
  have \<sigma>_eq_1_output_correct: 
    "((\<^bold>g [^] \<alpha>1) [^] r \<otimes> \<^bold>g \<otimes> inv \<^bold>g) [^] u1 \<otimes> (\<^bold>g [^] \<alpha>1) [^] v1 \<otimes> x1 \<otimes>
                               inv (((\<^bold>g [^] r) [^] u1 \<otimes> \<^bold>g [^] v1) [^] \<alpha>1) = x1"
    (is "?lhs = ?rhs")
    for \<alpha>1 r u1 v1 :: nat
  proof-
    have com1: "\<alpha>1 * r * u1 = r *  u1 * \<alpha>1" "v1 * \<alpha>1 = \<alpha>1 * v1" by simp+
    have in_carrier1: "(\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> (\<^bold>g [^] (v1 * \<alpha>1)) \<in> carrier \<G>" by simp
    have in_carrier2: "inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> (\<^bold>g [^] (v1 * \<alpha>1))) \<in> carrier \<G>" by simp
    have lhs: "?lhs = ((\<^bold>g [^] (\<alpha>1*r)) \<otimes> \<^bold>g \<otimes> inv \<^bold>g) [^] u1 \<otimes> (\<^bold>g [^] (\<alpha>1 * v1)) \<otimes> x1 \<otimes>
                                 inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> \<^bold>g [^] (v1*\<alpha>1))" 
      by (simp add: nat_pow_pow pow_mult_distrib cyclic_group_commute monoid_comm_monoidI)
    also have lhs1: "... = (\<^bold>g [^] (\<alpha>1 * r)) [^] u1 \<otimes> (\<^bold>g [^] (\<alpha>1 * v1)) \<otimes> x1 \<otimes>
                                 inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> \<^bold>g [^] (v1*\<alpha>1))" 
      by (simp add: cyclic_group_assoc)
    also have lhs2: "... = (\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> (\<^bold>g [^] (v1 * \<alpha>1)) \<otimes> x1 \<otimes>
                                 inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> \<^bold>g [^] (v1 * \<alpha>1))" 
      by (simp add: nat_pow_pow pow_mult_distrib cyclic_group_commute monoid_comm_monoidI com1)
    also have "... = (((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> (\<^bold>g [^] (v1 * \<alpha>1))) \<otimes> x1) \<otimes>
                                 inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> \<^bold>g [^] (v1 * \<alpha>1))"
      using in_carrier1 in_carrier2 assms cyclic_group_assoc by blast
    also have "... = (x1 \<otimes> ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> (\<^bold>g [^] (v1 * \<alpha>1)))) \<otimes>
                                 inv ((\<^bold>g [^] (r *  u1 * \<alpha>1)) \<otimes> \<^bold>g [^] (v1 * \<alpha>1))" 
      using in_carrier1 assms cyclic_group_commute by simp
    ultimately show ?thesis
      using cyclic_group_assoc assms in_carrier1 in_carrier1 assms cyclic_group_commute lhs1 lhs2 lhs by force
  qed
  show ?thesis
    unfolding funct_OT_12_def protocol_ot_def Let_def
    by(cases \<sigma>; auto simp add: assms \<sigma>_eq_1_output_correct \<sigma>_eq_0_output_correct bind_spmf_const
        lossless_sample_uniform_units order_gt_0 P1_assert_correct1 P1_assert_correct2 lossless_weight_spmfD) 
qed

lemma correctness:
  assumes "x0 \<in> carrier \<G>" 
    and "x1 \<in> carrier \<G>"
  shows "mal_def.correct (x0,x1) \<sigma>"
  unfolding mal_def.correct_def 
  by(simp add: correct assms)

end 

locale OT_asymp = 
  fixes \<G> :: "nat \<Rightarrow> 'grp cyclic_group"
  assumes ot: "\<And>\<eta>. ot (\<G> \<eta>)"
begin

sublocale ot "\<G> n" for n using ot by simp

lemma correctness_asym:
  assumes "x0 \<in> carrier (\<G> n)" 
    and "x1 \<in> carrier (\<G> n)" 
  shows "mal_def.correct n (x0,x1) \<sigma>" 
  using assms correctness by simp

lemma P1_security_asym:
  "negligible (\<lambda> n. mal_def.adv_P1 n M \<sigma> z (P1_S1 n, P1_S2) \<A> D)" 
  if neg1: "negligible (\<lambda> n. ddh.advantage n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D))"
    and neg2: "negligible (\<lambda> n. ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D)))" 
    and neg3: "negligible (\<lambda> n. ddh.advantage n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D))"
    and neg4: "negligible (\<lambda> n. ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D)))"  
proof-
  have neg_add1: "negligible (\<lambda> n. ddh.advantage n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D) 
        + ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D)))" 
    and neg_add2: "negligible (\<lambda> n. ddh.advantage n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D)
        + ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D)))"  
    using neg1 neg2 neg3 neg4 negligible_plus by(blast)+ 
  show ?thesis 
  proof(cases \<sigma>)
    case True
    have bound_mod: "\<bar>mal_def.adv_P1 n M \<sigma> z (P1_S1 n, P1_S2) \<A> D\<bar> 
            \<le> ddh.advantage n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D) 
              + ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_true n M z \<A> D))" for n 
      by (metis (no_types) True abs_idempotent P1_adv_real_ideal_model_def P1_advantages_eq P1_real_ideal_DDH_advantage_true_bound)
    then show ?thesis 
      using P1_real_ideal_DDH_advantage_true_bound that bound_mod that negligible_le neg_add1 by presburger
  next
    case False
    have bound_mod: "\<bar>mal_def.adv_P1 n M \<sigma> z (P1_S1 n, P1_S2) \<A> D\<bar> 
            \<le> ddh.advantage n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D) 
              + ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D))" for n 
    proof -
      have "\<bar>spmf (P1_real_model n M \<sigma> z \<A> \<bind> D) True - spmf (P1_ideal_model n M \<sigma> z \<A> \<bind> D) True\<bar> 
                    \<le> local.ddh.advantage n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D)    
                            + local.ddh.advantage n (ddh.DDH_\<A>' n (P1_DDH_mal_adv_\<sigma>_false n M z \<A> D))"
        by (metis (no_types) False P1_adv_real_ideal_model_def P1_advantages_eq P1_real_ideal_DDH_advantage_false_bound)
      then show ?thesis
        by (simp add: P1_adv_real_ideal_model_def P1_advantages_eq)
    qed
    then show ?thesis using P1_real_ideal_DDH_advantage_false_bound  bound_mod that negligible_le neg_add2 by presburger
  qed
qed

lemma P2_security_asym:   
  assumes x1_in_carrier: "x1 \<in> carrier (\<G> n)"
    and x0_in_carrier: "x0 \<in> carrier (\<G> n)"  
  shows "mal_def.perfect_sec_P2 n (x0,x1) \<sigma> z (P2_S1 n, P2_S2 n) \<A>"
  using assms malicious_sec_P2 by fast

end

end
