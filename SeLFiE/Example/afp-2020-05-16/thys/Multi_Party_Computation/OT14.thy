subsection \<open>1-out-of-2 OT to 1-out-of-4 OT\<close>

text \<open>Here we construct a protocol that achieves 1-out-of-4 OT from 1-out-of-2 OT. We follow the protocol
for constructing 1-out-of-n OT from 1-out-of-2 OT from \cite{DBLP:books/cu/Goldreich2004}. We assume the security
properties on 1-out-of-2 OT.\<close>

theory OT14 imports
  Semi_Honest_Def
  OT_Functionalities
  Uniform_Sampling
begin

type_synonym input1 = "bool \<times> bool \<times> bool \<times> bool"
type_synonym input2 = "bool \<times> bool"
type_synonym 'v_OT121' view1 = "(input1 \<times> (bool \<times> bool \<times> bool \<times> bool \<times> bool \<times> bool) \<times> 'v_OT121' \<times> 'v_OT121' \<times> 'v_OT121')"
type_synonym 'v_OT122' view2 = "(input2 \<times> (bool \<times> bool \<times> bool \<times> bool) \<times> 'v_OT122' \<times> 'v_OT122' \<times> 'v_OT122')"

locale ot14_base = 
  fixes S1_OT12 :: "(bool \<times> bool) \<Rightarrow> unit \<Rightarrow> 'v_OT121 spmf" \<comment> \<open>simulator for party 1 in OT12\<close>
    and R1_OT12 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'v_OT121 spmf" \<comment> \<open>real view for party 1 in OT12\<close>
    and adv_OT12 :: real
    and S2_OT12 :: "bool \<Rightarrow> bool \<Rightarrow> 'v_OT122 spmf" 
    and R2_OT12 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'v_OT122 spmf"
    and protocol_OT12 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (unit \<times> bool) spmf"
  assumes ass_adv_OT12: "sim_det_def.adv_P1 R1_OT12 S1_OT12 funct_OT12 (m0,m1) c D \<le> adv_OT12" \<comment> \<open>bound the advantage of OT12 for party 1\<close> 
    and inf_th_OT12_P2:  "sim_det_def.perfect_sec_P2 R2_OT12 S2_OT12 funct_OT12 (m0,m1) \<sigma>" \<comment> \<open>information theoretic security for party 2\<close>
    and correct: "protocol_OT12 msgs b = funct_OT_12 msgs b"
    and lossless_R1_12: "lossless_spmf (R1_OT12 m c)"
    and lossless_S1_12: "lossless_spmf (S1_OT12 m out1)"
    and lossless_S2_12: "lossless_spmf (S2_OT12 c out2)"
    and lossless_R2_12: "lossless_spmf (R2_OT12 M c)"
    and lossless_funct_OT12: "lossless_spmf (funct_OT12 (m0,m1) c)"
    and lossless_protocol_OT12: "lossless_spmf (protocol_OT12 M C)"
begin

sublocale OT_12_sim: sim_det_def R1_OT12 S1_OT12 R2_OT12 S2_OT12 funct_OT_12 protocol_OT12
  unfolding sim_det_def_def 
  by(simp add: lossless_R1_12 lossless_S1_12 lossless_funct_OT12 lossless_R2_12 lossless_S2_12)

lemma OT_12_P1_assms_bound': "\<bar>spmf (bind_spmf (R1_OT12 (m0,m1) c) (\<lambda> view. ((D::'v_OT121 \<Rightarrow> bool spmf) view ))) True 
                - spmf (bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (D view ))) True\<bar> \<le> adv_OT12"
proof-
  have "sim_det_def.adv_P1 R1_OT12 S1_OT12 funct_OT_12 (m0,m1) c D =
                      \<bar>spmf (bind_spmf (R1_OT12 (m0,m1) c) (\<lambda> view. (D view ))) True 
                                    - spmf (funct_OT_12 (m0,m1) c \<bind> (\<lambda> ((out1::unit), (out2::bool)). 
                                              S1_OT12 (m0,m1) out1 \<bind> (\<lambda> view. D view))) True\<bar>"
    using sim_det_def.adv_P1_def 
    using  OT_12_sim.adv_P1_def by auto
  also have "... = \<bar>spmf (bind_spmf (R1_OT12 (m0,m1) c) (\<lambda> view. ((D::'v_OT121 \<Rightarrow> bool spmf) view ))) True 
                - spmf (bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (D view ))) True\<bar>" 
    by(simp add: funct_OT_12_def)
  ultimately show ?thesis 
    by(metis ass_adv_OT12)
qed

lemma OT_12_P2_assm: "R2_OT12 (m0,m1) \<sigma> = funct_OT_12 (m0,m1) \<sigma> \<bind> (\<lambda> (out1, out2). S2_OT12 \<sigma> out2)"
  using inf_th_OT12_P2 OT_12_sim.perfect_sec_P2_def by blast

definition protocol_14_OT :: "input1 \<Rightarrow> input2 \<Rightarrow> (unit \<times> bool) spmf"
  where "protocol_14_OT M C = do {
    let (c0,c1) = C;
    let (m00, m01, m10, m11) = M;
    S0 \<leftarrow> coin_spmf;
    S1 \<leftarrow> coin_spmf;
    S2 \<leftarrow> coin_spmf;
    S3 \<leftarrow> coin_spmf;
    S4 \<leftarrow> coin_spmf;
    S5 \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m00;
    let a1 = S0 \<oplus> S3 \<oplus> m01;
    let a2 = S1 \<oplus> S4 \<oplus> m10;
    let a3 = S1 \<oplus> S5 \<oplus> m11;
    (_,Si) \<leftarrow> protocol_OT12 (S0, S1) c0;
    (_,Sj) \<leftarrow> protocol_OT12 (S2, S3) c1;
    (_,Sk) \<leftarrow> protocol_OT12 (S4, S5) c1;
    let s2 = Si \<oplus> (if c0 then Sk else Sj) \<oplus> (if c0 then (if c1 then a3 else a2) else (if c1 then a1 else a0));
    return_spmf ((), s2)}"

lemma lossless_protocol_14_OT: "lossless_spmf (protocol_14_OT M C)" 
  by(simp add: protocol_14_OT_def lossless_protocol_OT12 split_def)

definition R1_14 :: "input1 \<Rightarrow> input2 \<Rightarrow> 'v_OT121 view1 spmf"
  where "R1_14 msgs choice = do {
    let (m00, m01, m10, m11) = msgs;
    let (c0, c1) = choice;
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> R1_OT12 (S0, S1) c0; 
    b :: 'v_OT121 \<leftarrow> R1_OT12 (S2, S3) c1;
    c :: 'v_OT121 \<leftarrow> R1_OT12 (S4, S5) c1;
    return_spmf (msgs, (S0, S1, S2, S3, S4, S5), a, b, c)}"

lemma lossless_R1_14: "lossless_spmf (R1_14 msgs C)"
  by(simp add: R1_14_def split_def lossless_R1_12)

definition R1_14_interm1 :: "input1 \<Rightarrow> input2 \<Rightarrow> 'v_OT121 view1 spmf"
  where "R1_14_interm1 msgs choice = do {
    let (m00, m01, m10, m11) = msgs;
    let (c0, c1) = choice;
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> S1_OT12 (S0, S1) (); 
    b :: 'v_OT121 \<leftarrow> R1_OT12 (S2, S3) c1;
    c :: 'v_OT121 \<leftarrow> R1_OT12 (S4, S5) c1;
    return_spmf (msgs, (S0, S1, S2, S3, S4, S5), a, b, c)}"

lemma lossless_R1_14_interm1: "lossless_spmf (R1_14_interm1 msgs C)"
  by(simp add: R1_14_interm1_def split_def lossless_R1_12 lossless_S1_12)

definition R1_14_interm2 :: "input1 \<Rightarrow> input2 \<Rightarrow> 'v_OT121 view1 spmf"
  where "R1_14_interm2 msgs choice = do {
    let (m00, m01, m10, m11) = msgs;
    let (c0, c1) = choice;
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> S1_OT12 (S0, S1) (); 
    b :: 'v_OT121 \<leftarrow> S1_OT12 (S2, S3) ();
    c :: 'v_OT121 \<leftarrow> R1_OT12 (S4, S5) c1;
    return_spmf (msgs, (S0, S1, S2, S3, S4, S5), a, b, c)}"

lemma lossless_R1_14_interm2: "lossless_spmf (R1_14_interm2 msgs C)"
  by(simp add: R1_14_interm2_def split_def lossless_R1_12 lossless_S1_12)

definition S1_14 :: "input1 \<Rightarrow> unit \<Rightarrow> 'v_OT121 view1 spmf"
  where "S1_14 msgs _ = do {   
    let (m00, m01, m10, m11) = msgs;    
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> S1_OT12 (S0, S1) (); 
    b :: 'v_OT121 \<leftarrow> S1_OT12 (S2, S3) ();
    c :: 'v_OT121 \<leftarrow> S1_OT12 (S4, S5) ();
    return_spmf (msgs, (S0, S1, S2, S3, S4, S5), a, b, c)}"

lemma lossless_S1_14: "lossless_spmf (S1_14 m out)"
  by(simp add: S1_14_def lossless_S1_12)

lemma reduction_step1: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True\<bar> =
              \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
  including monad_normalisation
proof-
  define A1' where "A1' == \<lambda> (view :: 'v_OT121) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    b :: 'v_OT121 \<leftarrow> R1_OT12 (S2, S3) c1;
    c :: 'v_OT121 \<leftarrow> R1_OT12 (S4, S5) c1;
    let R = (M, (m0,m1, S2, S3, S4, S5), view, b, c);
    D R}"
  have "\<bar>spmf (bind_spmf (R1_14 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
    apply(simp add: pair_spmf_alt_def R1_14_def R1_14_interm1_def A1'_def Let_def split_def) 
    apply(subst bind_commute_spmf[of "S1_OT12 _ _"])
    apply(subst bind_commute_spmf[of "S1_OT12 _ _"])
    apply(subst bind_commute_spmf[of "S1_OT12 _ _"])
    apply(subst bind_commute_spmf[of "S1_OT12 _ _"])
    apply(subst bind_commute_spmf[of "S1_OT12 _ _"])
    by auto
  then show ?thesis by auto
qed

lemma reduction_step1':
  shows "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> 
                        \<le> adv_OT12"
  (is "?lhs \<le> adv_OT12")
proof-
  have int1: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>x. spmf (case x of (m0, m1) \<Rightarrow> R1_OT12 (m0, m1) c0 \<bind> (\<lambda>view. A1 view (m0, m1))) True)" 
    and int2: "integrable (measure_spmf (pair_spmf coin_spmf coin_spmf)) (\<lambda>x. spmf (case x of (m0, m1) \<Rightarrow> S1_OT12 (m0, m1) () \<bind> (\<lambda>view. A1 view (m0, m1))) True)" 
    by(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)+
  have "?lhs = 
            \<bar>LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). spmf (case x of (m0, m1) \<Rightarrow> R1_OT12 (m0, m1) c0 \<bind> (\<lambda>view. A1 view (m0, m1))) True 
              - spmf (case x of (m0, m1) \<Rightarrow> S1_OT12 (m0, m1) () \<bind> (\<lambda>view. A1 view (m0, m1))) True\<bar>"
    apply(subst (1 2) spmf_bind) using int1 int2 by simp
  also have "... \<le> LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
               \<bar>spmf (R1_OT12 x c0 \<bind> (\<lambda>view. A1 view x)) True - spmf (S1_OT12 x () \<bind> (\<lambda>view. A1 view x)) True\<bar>"
    by(rule integral_abs_bound[THEN order_trans]; simp add: split_beta)
  ultimately have "?lhs \<le> LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                      \<bar>spmf (R1_OT12 x c0 \<bind> (\<lambda>view. A1 view x)) True - spmf (S1_OT12 x () \<bind> (\<lambda>view. A1 view x)) True\<bar>"
    by simp
  also have "LINT x|measure_spmf (pair_spmf coin_spmf coin_spmf). 
                \<bar>spmf (R1_OT12 x c0 \<bind> (\<lambda>view::'v_OT121. A1 view x)) True 
                    - spmf (S1_OT12 x () \<bind> (\<lambda>view::'v_OT121. A1 view x)) True\<bar> \<le> adv_OT12"
    apply(rule integral_mono[THEN order_trans])
       apply(rule measure_spmf.integrable_const_bound[where B=2])
        apply clarsimp
        apply(rule abs_triangle_ineq4[THEN order_trans])
    subgoal for m0 m1
      using pmf_le_1[of "R1_OT12 (m0, m1) c0 \<bind> (\<lambda>view. A1 view (m0, m1))" "Some True"]
        pmf_le_1[of "S1_OT12 (m0, m1) () \<bind> (\<lambda>view. A1 view (m0, m1))" "Some True"]
      by simp
       apply simp
      apply(rule measure_spmf.integrable_const)
     apply clarify
     apply(rule OT_12_P1_assms_bound'[rule_format]) 
    by simp
  ultimately show ?thesis by simp
qed

lemma reduction_step2: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1 view (m0,m1))))) True -
            spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
proof-
  define A1' where "A1' == \<lambda> (view :: 'v_OT121) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> S1_OT12 (S2,S3) ();
    c :: 'v_OT121 \<leftarrow> R1_OT12 (S4, S5) c1;
    let R = (M, (S2,S3, m0, m1, S4, S5), a, view, c);
    D R}"
  have "\<bar>spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (R1_14_interm1 M (c0, c1)) D) = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding R1_14_interm1_def R1_14_interm2_def A1'_def Let_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by(simp)
    also have "(bind_spmf (R1_14_interm2 M (c0, c1)) D) =  (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding R1_14_interm1_def R1_14_interm2_def A1'_def Let_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
      by(simp)  
    ultimately show ?thesis by simp
  qed
  then show ?thesis by auto
qed

lemma reduction_step3: 
  shows "\<exists> A1. \<bar>spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True - spmf (bind_spmf (S1_14 M out) D) True\<bar> =
          \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1 view (m0,m1))))) True -
            spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
proof-
  define A1' where "A1' == \<lambda> (view :: 'v_OT121) (m0,m1). do {
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a :: 'v_OT121 \<leftarrow> S1_OT12 (S2,S3) ();
    b :: 'v_OT121 \<leftarrow> S1_OT12 (S4, S5) ();
    let R = (M, (S2,S3, S4, S5,m0, m1), a, b, view);
    D R}"
  have "\<bar>spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True - spmf (bind_spmf (S1_14 M out) D) True\<bar> =
       \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1' view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1' view (m0,m1))))) True\<bar>"
  proof-
    have "(bind_spmf (R1_14_interm2 M (c0, c1)) D) = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding  R1_14_interm2_def A1'_def Let_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      including monad_normalisation by(simp)
    also have "(bind_spmf (S1_14 M out) D) = (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1' view (m0,m1)))))"
      unfolding S1_14_def Let_def A1'_def split_def
      apply(simp add: pair_spmf_alt_def) 
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
      apply(rewrite in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
      including monad_normalisation by(simp)
    ultimately show ?thesis by simp
  qed
  then show ?thesis by auto
qed

lemma reduction_P1_interm: 
  shows "\<bar>spmf (bind_spmf (R1_14 M (c0,c1)) (D)) True - spmf (bind_spmf (S1_14 M out) (D)) True\<bar> \<le> 3 * adv_OT12"
    (is "?lhs \<le> ?rhs")
proof-
  have lhs: "?lhs \<le> \<bar>spmf (bind_spmf (R1_14 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True\<bar> + 
                     \<bar>spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True\<bar> +
                      \<bar>spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True - spmf (bind_spmf (S1_14 M out) D) True\<bar>"
    by simp
  obtain A1 where A1: "\<bar>spmf (bind_spmf (R1_14 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True\<bar> =
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar>"
    using reduction_step1 by blast
  obtain A2 where A2: "\<bar>spmf (bind_spmf (R1_14_interm1 M (c0, c1)) D) True - spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True\<bar> = 
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A2 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A2 view (m0,m1))))) True\<bar>"
    using reduction_step2 by blast
  obtain A3 where A3: "\<bar>spmf (bind_spmf (R1_14_interm2 M (c0, c1)) D) True - spmf (bind_spmf (S1_14 M out) D) True\<bar> =
                        \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A3 view (m0,m1))))) True -
                          spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using reduction_step3 by blast
  have lhs_bound: "?lhs \<le> \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> + 
                   \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A2 view (m0,m1))))) True -
                    spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A2 view (m0,m1))))) True\<bar> +
                     \<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A3 view (m0,m1))))) True -
                      spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A3 view (m0,m1))))) True\<bar>"
    using A1 A2 A3 lhs by simp
  have bound1: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c0) (\<lambda> view. (A1 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A1 view (m0,m1))))) True\<bar> 
                      \<le> adv_OT12" 
    and bound2: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A2 view (m0,m1))))) True -
                  spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A2 view (m0,m1))))) True\<bar> 
                      \<le> adv_OT12" 
    and bound3: "\<bar>spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (R1_OT12 (m0,m1) c1) (\<lambda> view. (A3 view (m0,m1))))) True -
        spmf (bind_spmf (pair_spmf coin_spmf coin_spmf) (\<lambda>(m0, m1). bind_spmf (S1_OT12 (m0,m1) ()) (\<lambda> view. (A3 view (m0,m1))))) True\<bar> \<le> adv_OT12"
    using reduction_step1' by auto
  thus ?thesis
    using reduction_step1' lhs_bound by argo  
qed

lemma reduction_P1: "\<bar>spmf (bind_spmf (R1_14 M (c0,c1)) (D)) True 
                        - spmf (funct_OT_14 M (c0,c1) \<bind> (\<lambda> (out1,out2). S1_14 M out1 \<bind> (\<lambda> view. D view))) True\<bar> 
                              \<le> 3 * adv_OT12"
  by(simp add: funct_OT_14_def split_def Let_def reduction_P1_interm )

text\<open>Party 2 security.\<close>

lemma coin_coin: "map_spmf (\<lambda> S0. S0 \<oplus> S3 \<oplus> m1) coin_spmf = coin_spmf"
  (is "?lhs = ?rhs")
proof-
  have lhs: "?lhs = map_spmf (\<lambda> S0. S0 \<oplus> (S3 \<oplus> m1)) coin_spmf" by blast
  also have op_eq: "... = map_spmf ((\<oplus>) (S3 \<oplus> m1)) coin_spmf" 
    by (metis xor_bool_def)
  also have "... = ?rhs" 
    using xor_uni_samp by fastforce
  ultimately show ?thesis 
    using op_eq by auto
qed

lemma coin_coin': "map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf = coin_spmf"
proof-
  have "map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf = map_spmf (\<lambda> S3. S3 \<oplus> S0 \<oplus> m1) coin_spmf" 
    by (metis xor_left_commute)
  thus ?thesis using coin_coin by simp
qed

definition R2_14:: "input1 \<Rightarrow> input2 \<Rightarrow> 'v_OT122 view2 spmf"
  where "R2_14 M C = do {
    let (m0,m1,m2,m3) = M;
    let (c0,c1) = C;
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'v_OT122 \<leftarrow> R2_OT12 (S0,S1) c0;
    b :: 'v_OT122 \<leftarrow> R2_OT12 (S2,S3) c1;
    c :: 'v_OT122 \<leftarrow> R2_OT12 (S4,S5) c1;
    return_spmf (C, (a0,a1,a2,a3), a,b,c)}"

lemma lossless_R2_14: "lossless_spmf (R2_14 M C)"
  by(simp add: R2_14_def split_def lossless_R2_12)

definition S2_14 :: "input2 \<Rightarrow> bool \<Rightarrow> 'v_OT122 view2 spmf"
  where "S2_14 C out = do {
    let ((c0::bool),(c1::bool)) = C;
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 :: bool \<leftarrow> coin_spmf;
    let a0' = (if ((\<not> c0) \<and> (\<not> c1)) then (S0 \<oplus> S2 \<oplus> out) else a0);
    let a1' = (if ((\<not> c0) \<and> c1) then (S0 \<oplus> S3 \<oplus> out) else a1);
    let a2' = (if (c0 \<and> (\<not> c1)) then (S1 \<oplus> S4 \<oplus> out) else a2);
    let a3' = (if (c0 \<and> c1) then (S1 \<oplus> S5 \<oplus> out) else a3);
    a :: 'v_OT122 \<leftarrow> S2_OT12 (c0::bool) (if c0 then S1 else S0);
    b :: 'v_OT122 \<leftarrow> S2_OT12 (c1::bool) (if c1 then S3 else S2);
    c :: 'v_OT122 \<leftarrow> S2_OT12 (c1::bool) (if c1 then S5 else S4);
    return_spmf ((c0,c1), (a0',a1',a2',a3'), a,b,c)}"

lemma lossless_S2_14: "lossless_spmf (S2_14 c out)" 
  by(simp add: S2_14_def lossless_S2_12 split_def)

lemma P2_OT_14_FT: "R2_14 (m0,m1,m2,m3) (False,True) = funct_OT_14 (m0,m1,m2,m3) (False,True) \<bind> (\<lambda> (out1, out2). S2_14 (False,True) out2)"
  including monad_normalisation
proof-
  have "R2_14 (m0,m1,m2,m3) (False,True) =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((False,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def R2_14_def inf_th_OT12_P2 funct_OT_12_def OT_12_P2_assm)
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((False,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> map_spmf (\<lambda> S1. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((False,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((False,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: funct_OT_14_def S2_14_def bind_spmf_const)
qed

lemma P2_OT_14_TT: "R2_14 (m0,m1,m2,m3) (True,True) = funct_OT_14 (m0,m1,m2,m3) (True,True) \<bind> (\<lambda> (out1, out2). S2_14 (True,True) out2)"
  including monad_normalisation
proof-
  have "R2_14 (m0,m1,m2,m3) (True,True) =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S2. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> map_spmf (\<lambda> S4. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((True,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def R2_14_def inf_th_OT12_P2 funct_OT_12_def OT_12_P2_assm Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    let a1 = S0 \<oplus> S3 \<oplus> m1;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((True,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S0. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((True,True), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)    
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S3 :: bool \<leftarrow> coin_spmf;
    S5 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 \<leftarrow> coin_spmf;
    let a3 = S1 \<oplus> S5 \<oplus> m3;
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 True S3;
    c :: 'v_OT122 \<leftarrow> S2_OT12 True S5;
    return_spmf ((True,True), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    by(simp add: funct_OT_14_def S2_14_def bind_spmf_const)
qed

lemma P2_OT_14_FF: "R2_14 (m0,m1,m2,m3) (False, False) = funct_OT_14 (m0,m1,m2,m3) (False, False) \<bind> (\<lambda> (out1, out2). S2_14 (False, False) out2)"
  including monad_normalisation
proof-
  have "R2_14 (m0,m1,m2,m3) (False,False) =  do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((False,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def R2_14_def inf_th_OT12_P2 funct_OT_12_def OT_12_P2_assm Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((False,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> map_spmf (\<lambda> S1. S1 \<oplus> S4 \<oplus> m2) coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((False,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    a2 :: bool \<leftarrow> coin_spmf;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 False S0; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((False,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis 
    by(simp add: funct_OT_14_def S2_14_def bind_spmf_const)
qed

lemma P2_OT_14_TF: "R2_14 (m0,m1,m2,m3) (True,False) = funct_OT_14 (m0,m1,m2,m3) (True,False) \<bind> (\<lambda> (out1, out2). S2_14 (True,False) out2)"
  including monad_normalisation
proof-
  have "R2_14 (m0,m1,m2,m3) (True,False) = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> map_spmf (\<lambda> S3. S0 \<oplus> S3 \<oplus> m1) coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> map_spmf (\<lambda> S5. S1 \<oplus> S5 \<oplus> m3) coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((True,False), (a0,a1,a2,a3), a,b,c)}"
    apply(simp add: R2_14_def inf_th_OT12_P2 OT_12_P2_assm funct_OT_12_def Let_def)
    apply(rewrite in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>"  in "bind_spmf _ \<hole>" in "\<hole> = _" bind_commute_spmf)
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S0 :: bool \<leftarrow> coin_spmf;
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    let a0 = S0 \<oplus> S2 \<oplus> m0;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((True,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin' by simp
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> map_spmf (\<lambda> S0. S0 \<oplus> S2 \<oplus> m0) coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((True,False), (a0,a1,a2,a3), a,b,c)}"
    by(simp add: bind_map_spmf o_def Let_def)
  also have "... = do {
    S1 :: bool \<leftarrow> coin_spmf;
    S2 :: bool \<leftarrow> coin_spmf;
    S4 :: bool \<leftarrow> coin_spmf;
    a0 :: bool \<leftarrow> coin_spmf;
    a1 :: bool \<leftarrow> coin_spmf;
    let a2 = S1 \<oplus> S4 \<oplus> m2;
    a3 \<leftarrow> coin_spmf; 
    a :: 'v_OT122 \<leftarrow> S2_OT12 True S1; 
    b :: 'v_OT122 \<leftarrow> S2_OT12 False S2;
    c :: 'v_OT122 \<leftarrow> S2_OT12 False S4;
    return_spmf ((True,False), (a0,a1,a2,a3), a,b,c)}"
    using coin_coin by simp
  ultimately show ?thesis
    apply(simp add: funct_OT_14_def S2_14_def bind_spmf_const)
    apply(rewrite in "bind_spmf _ \<hole>"  in "_ = \<hole>" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
    apply(rewrite in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "bind_spmf _ \<hole>" in "_ = \<hole>" bind_commute_spmf)
    by simp
qed

lemma P2_sec_OT_14_split: "R2_14 (m0,m1,m2,m3) (c0,c1) = funct_OT_14 (m0,m1,m2,m3) (c0,c1) \<bind> (\<lambda> (out1, out2). S2_14 (c0,c1) out2)"
  by(cases c0; cases c1; auto simp add: P2_OT_14_FF P2_OT_14_TF P2_OT_14_FT P2_OT_14_TT)

lemma P2_sec_OT_14: "R2_14 M C = funct_OT_14 M C \<bind> (\<lambda> (out1, out2). S2_14 C out2)"
  by(metis P2_sec_OT_14_split surj_pair) 

sublocale OT_14: sim_det_def R1_14 S1_14 R2_14 S2_14 funct_OT_14 protocol_14_OT
  unfolding sim_det_def_def 
  by(simp add: lossless_R1_14 lossless_S1_14 lossless_funct_14_OT lossless_R2_14 lossless_S2_14 )

lemma correctness_OT_14: 
  shows "funct_OT_14 M C = protocol_14_OT M C"
proof-
  have "S1 = (S5 = (S1 = (S5 = d))) = d" for S1 S5 d by auto
  thus ?thesis
    by(cases "fst C"; cases "snd C"; simp add: funct_OT_14_def protocol_14_OT_def correct funct_OT_12_def lossless_funct_OT_12 bind_spmf_const split_def)
qed

lemma OT_14_correct: "OT_14.correctness M C"
  unfolding OT_14.correctness_def 
  using correctness_OT_14 by auto

lemma OT_14_P2_sec: "OT_14.perfect_sec_P2 m1 m2"
  unfolding OT_14.perfect_sec_P2_def
  using P2_sec_OT_14 by blast

lemma OT_14_P1_sec: "OT_14.adv_P1 m1 m2 D \<le> 3 * adv_OT12"
  unfolding OT_14.adv_P1_def  
  by (metis reduction_P1 surj_pair) 

end

locale OT_14_asymp = sim_det_def +
  fixes S1_OT12 :: "nat \<Rightarrow> (bool \<times> bool) \<Rightarrow> unit \<Rightarrow> 'v_OT121 spmf"
    and R1_OT12 :: "nat \<Rightarrow> (bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'v_OT121 spmf" 
    and adv_OT12 :: "nat \<Rightarrow> real"
    and S2_OT12 :: "nat \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'v_OT122 spmf" 
    and R2_OT12 :: "nat \<Rightarrow> (bool \<times> bool) \<Rightarrow> bool \<Rightarrow> 'v_OT122 spmf"
    and protocol_OT12 :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (unit \<times> bool) spmf"
  assumes ot14_base: "\<And> (n::nat). ot14_base (S1_OT12 n) (R1_12_0T n) (adv_OT12 n) (S2_OT12 n) (R2_12OT n) (protocol_OT12)"
begin 

sublocale ot14_base "(S1_OT12 n)" "(R1_12_0T n)" "(adv_OT12 n)" "(S2_OT12 n)" "(R2_12OT n)" using local.ot14_base by simp

lemma OT_14_P1_sec: "OT_14.adv_P1 (R1_12_0T n) n m1 m2 D \<le> 3 * (adv_OT12 n)"
  unfolding OT_14.adv_P1_def using reduction_P1 surj_pair by metis

theorem OT_14_P1_asym_sec: "negligible (\<lambda> n. OT_14.adv_P1 (R1_12_0T n) n m1 m2 D)" if "negligible (\<lambda> n. adv_OT12 n)"
proof-
  have adv_neg: "negligible (\<lambda>n. 3 * adv_OT12 n)" using that negligible_cmultI by simp
  have "\<bar>OT_14.adv_P1 (R1_12_0T n) n m1 m2 D\<bar> \<le> \<bar>3 * (adv_OT12 n)\<bar>" for n 
  proof -
    have "\<bar>OT_14.adv_P1 (R1_12_0T n) n m1 m2 D\<bar> \<le> 3 * adv_OT12 n"
      using OT_14.adv_P1_def OT_14_P1_sec by auto
    then show ?thesis
      by (meson abs_ge_self order_trans)
  qed
  thus ?thesis using OT_14_P1_sec negligible_le adv_neg 
    by (metis (no_types, lifting) negligible_absI)
qed

theorem OT_14_P2_asym_sec: "OT_14.perfect_sec_P2 R2_OT12 n m1 m2"
  using OT_14_P2_sec by simp

end

end


