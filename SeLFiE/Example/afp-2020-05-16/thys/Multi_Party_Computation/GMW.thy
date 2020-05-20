subsection \<open>1-out-of-4 OT to GMW\<close>

text\<open>We prove security for the gates of the GMW protocol in the semi honest model. We assume security on
1-out-of-4 OT.\<close>

theory GMW imports
  OT14
begin

type_synonym share_1 = bool 
type_synonym share_2 = bool

type_synonym shares_1 = "bool list"
type_synonym shares_2 = "bool list"

type_synonym msgs_14_OT = "(bool \<times> bool \<times> bool \<times> bool)"
type_synonym choice_14_OT = "(bool \<times> bool)"

type_synonym share_wire = "(share_1 \<times> share_2)"

locale gmw_base =
  fixes S1_14_OT :: "msgs_14_OT \<Rightarrow> unit \<Rightarrow> 'v_14_OT1 spmf" \<comment> \<open>simulated view for party 1 of OT14\<close>
    and R1_14_OT :: "msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> 'v_14_OT1 spmf" \<comment> \<open>real view for party 1 of OT14\<close>
    and S2_14_OT :: "choice_14_OT \<Rightarrow> bool \<Rightarrow> 'v_14_OT2 spmf" 
    and R2_14_OT :: "msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> 'v_14_OT2 spmf"
    and protocol_14_OT :: "msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> (unit \<times> bool) spmf"
    and adv_14_OT :: real
  assumes P1_OT_14_adv_bound: "sim_det_def.adv_P1 R1_14_OT S1_14_OT funct_14_OT M C D \<le> adv_14_OT" \<comment> \<open>bound the advantage of party 1 in the 1-out-of-4 OT\<close>
    and P2_OT_12_inf_theoretic: "sim_det_def.perfect_sec_P2 R2_14_OT S2_14_OT funct_14_OT M C" \<comment> \<open>information theoretic security for party 2 in the 1-out-of-4 OT\<close>
    and correct_14: "funct_OT_14 msgs C = protocol_14_OT msgs C" \<comment> \<open>correctness of the 1-out-of-4 OT\<close>
    and lossless_R1_14_OT: "lossless_spmf (R1_14_OT (m1,m2,m3,m4) (c0,c1))"
    and lossless_R2_14_OT: "lossless_spmf (R2_14_OT (m1,m2,m3,m4) (c0,c1))"
    and lossless_S1_14_OT: "lossless_spmf (S1_14_OT (m1,m2,m3,m4) ())"
    and lossless_S2_14_OT: "lossless_spmf (S2_14_OT (c0,c1) b)"
    and lossless_protocol_14_OT: "lossless_spmf (protocol_14_OT S C)" 
    and lossless_funct_14_OT: "lossless_spmf (funct_14_OT M C)"
begin

lemma  funct_14: "funct_OT_14 (m00,m01,m10,m11) (c0,c1) 
                      = return_spmf ((),if c0 then (if c1 then m11 else m10) else (if c1 then m01 else m00))"
  by(simp add: funct_OT_14_def)

sublocale OT_14_sim: sim_det_def R1_14_OT S1_14_OT R2_14_OT S2_14_OT funct_14_OT protocol_14_OT
  unfolding sim_det_def_def 
  by(simp add: lossless_R1_14_OT lossless_S1_14_OT lossless_funct_14_OT lossless_R2_14_OT lossless_S2_14_OT)

lemma inf_th_14_OT_P4: "R2_14_OT msgs C = (funct_OT_14 msgs C \<bind> (\<lambda> (s1, s2). S2_14_OT C s2))" 
  using P2_OT_12_inf_theoretic sim_det_def.perfect_sec_P2_def OT_14_sim.perfect_sec_P2_def by auto

lemma ass_adv_14_OT: "\<bar>spmf (bind_spmf (S1_14_OT msgs ()) (\<lambda> view. (D view))) True - 
                    spmf (bind_spmf (R1_14_OT msgs (c0,c1)) (\<lambda> view. (D view))) True \<bar> \<le> adv_14_OT"
  (is "?lhs \<le> adv_14_OT")
proof-
  have "funct_OT_14 (m0,m1,m2,m3) (c0, c1) \<bind> (\<lambda>(o1, o2). S1_14_OT (m0,m1,m2,m3) () \<bind> D) = S1_14_OT (m0,m1,m2,m3) () \<bind> D" 
    for m0 m1 m2 m3 by(simp add: funct_14)
  hence funct: "funct_OT_14 msgs (c0, c1) \<bind> (\<lambda>(o1, o2). S1_14_OT msgs () \<bind> D) = S1_14_OT msgs () \<bind> D" 
    by (metis prod_cases4)
  have "?lhs = \<bar>spmf (bind_spmf (R1_14_OT msgs (c0,c1)) (\<lambda> view. (D view))) True 
                  - spmf (bind_spmf (S1_14_OT msgs ()) (\<lambda> view. (D view))) True\<bar>"
    by linarith
  hence "... = \<bar>(spmf (R1_14_OT msgs (c0,c1) \<bind> (\<lambda> view. D view)) True) 
            - spmf (funct_OT_14 msgs (c0,c1) \<bind> (\<lambda> (o1, o2). S1_14_OT msgs o1 \<bind> (\<lambda> view. D view))) True\<bar>" 
    by(simp add: funct)
  thus ?thesis using P1_OT_14_adv_bound sim_det_def.adv_P1_def 
    by (simp add: OT_14_sim.adv_P1_def abs_minus_commute)
qed

text \<open>The sharing scheme\<close>

definition share :: "bool \<Rightarrow> share_wire spmf"
  where "share x = do {
    a\<^sub>1 \<leftarrow> coin_spmf;
    let b\<^sub>1 = x \<oplus> a\<^sub>1;
    return_spmf (a\<^sub>1, b\<^sub>1)}" 

lemma lossless_share [simp]: "lossless_spmf (share x)" 
  by(simp add: share_def)

definition reconstruct :: "(share_1 \<times> share_2) \<Rightarrow> bool spmf"
  where "reconstruct shares = do {
    let (a,b) = shares;
    return_spmf (a \<oplus> b)}"

lemma lossless_reconstruct [simp]: "lossless_spmf (reconstruct s)" 
  by(simp add: reconstruct_def split_def)

lemma reconstruct_share : "(bind_spmf (share x) reconstruct) = (return_spmf x)"
proof-
  have "y = (y = x) = x" for y by auto
  thus ?thesis 
    by(auto simp add: share_def reconstruct_def bind_spmf_const eq_commute)  
qed

lemma "(reconstruct (s1,s2) \<bind> (\<lambda> rec. share rec \<bind> (\<lambda> shares. reconstruct shares))) = return_spmf (s1 \<oplus> s2)"
  apply(simp add: reconstruct_share reconstruct_def share_def)
  apply(cases s1; cases s2) by(auto simp add: bind_spmf_const)

definition xor_evaluate ::  "bool \<Rightarrow> bool \<Rightarrow> bool spmf"
  where "xor_evaluate A B = return_spmf (A \<oplus> B)"

definition xor_funct :: "share_wire \<Rightarrow> share_wire \<Rightarrow> (bool \<times> bool) spmf"
  where "xor_funct A B = do {
    let (a1, b1) = A;
    let (a2,b2) = B;
    return_spmf (a1 \<oplus> a2, b1 \<oplus> b2)}"

lemma lossless_xor_funct: "lossless_spmf (xor_funct A B)"
  by(simp add: xor_funct_def split_def)

definition xor_protocol :: "share_wire \<Rightarrow> share_wire \<Rightarrow> (bool \<times> bool) spmf"
  where "xor_protocol A B = do {
    let (a1, b1) = A;
    let (a2,b2) = B;
    return_spmf (a1 \<oplus> a2, b1 \<oplus> b2)}"

lemma lossless_xor_protocol: "lossless_spmf (xor_protocol A B)"
  by(simp add: xor_protocol_def split_def)

lemma share_xor_reconstruct: 
  shows "share x \<bind> (\<lambda> w1. share y \<bind> (\<lambda> w2. xor_protocol w1 w2 
              \<bind> (\<lambda> (a, b). reconstruct (a, b)))) = xor_evaluate x y"
proof-
  have "(ya = (\<not> yb)) = ((x = (\<not> ya)) = (y = (\<not> yb))) = (x = (\<not> y))" for ya yb
    by auto
  then show ?thesis
    by(simp add: share_def xor_protocol_def reconstruct_def xor_evaluate_def bind_spmf_const)
qed

definition R1_xor :: "(bool \<times> bool) \<Rightarrow> (bool \<times> bool) \<Rightarrow> (bool \<times> bool) spmf"
  where "R1_xor A B = return_spmf A"

lemma lossless_R1_xor: "lossless_spmf (R1_xor A B)" 
  by(simp add: R1_xor_def)

definition S1_xor :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
  where "S1_xor A out  = return_spmf A"

lemma lossless_S1_xor: "lossless_spmf (S1_xor A out)" 
  by(simp add: S1_xor_def)

lemma P1_xor_inf_th: "R1_xor A B = xor_funct A B \<bind> (\<lambda> (out1, out2). S1_xor A out1)"
  by(simp add: R1_xor_def xor_funct_def S1_xor_def split_def)

definition R2_xor :: "(bool \<times> bool) \<Rightarrow> (bool \<times> bool) \<Rightarrow> (bool \<times> bool) spmf"
  where "R2_xor A B = return_spmf B"

lemma lossless_R2_xor: "lossless_spmf (R2_xor A B)" 
  by(simp add: R2_xor_def)

definition S2_xor :: "(bool \<times> bool) \<Rightarrow> bool \<Rightarrow> (bool \<times> bool) spmf"
  where "S2_xor B out  = return_spmf B"

lemma lossless_S2_xor: "lossless_spmf (S2_xor A out)" 
  by(simp add: S2_xor_def)

lemma P2_xor_inf_th: "R2_xor A B = xor_funct A B \<bind> (\<lambda> (out1, out2). S2_xor B out2)"
  by(simp add: R2_xor_def xor_funct_def S2_xor_def split_def)

sublocale xor_sim_det: sim_det_def  R1_xor S1_xor R2_xor S2_xor xor_funct xor_protocol 
  unfolding sim_det_def_def
  by(simp add: lossless_R1_xor lossless_S1_xor lossless_R2_xor lossless_S2_xor lossless_xor_funct)

lemma "xor_sim_det.perfect_sec_P1 m1 m2"
  by(simp add: xor_sim_det.perfect_sec_P1_def P1_xor_inf_th)

lemma "xor_sim_det.perfect_sec_P2 m1 m2"
  by(simp add: xor_sim_det.perfect_sec_P2_def P2_xor_inf_th)

definition and_funct :: "(share_1 \<times> share_2) \<Rightarrow> (share_1 \<times> share_2) \<Rightarrow> share_wire spmf"
  where "and_funct A B = do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    return_spmf (\<sigma>, \<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2)))}"

lemma lossless_and_funct: "lossless_spmf (and_funct A B)"
  by(simp add: and_funct_def split_def)

definition and_evaluate :: "bool \<Rightarrow> bool \<Rightarrow> bool spmf"
  where "and_evaluate A B  = return_spmf (A \<and> B)"

definition and_protocol :: "share_wire \<Rightarrow> share_wire \<Rightarrow> share_wire spmf"
  where "and_protocol A B = do {
    let (a1, b1) = A;
    let (a2,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (b1 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (b1 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (b1 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (b1 \<oplus> True)); 
    (_, s) \<leftarrow> protocol_14_OT (s0,s1,s2,s3) (a2,b2);
    return_spmf (\<sigma>, s)}" 

lemma lossless_and_protocol: "lossless_spmf (and_protocol A B)"
  by(simp add: and_protocol_def split_def lossless_protocol_14_OT)

lemma and_correct: "and_protocol (a1, b1) (a2,b2) = and_funct (a1, b1) (a2,b2)"
  apply(simp add: and_protocol_def and_funct_def correct_14[symmetric] funct_14)
  by(cases b2 ; cases b1; cases a1; cases a2; auto)

lemma share_and_reconstruct: 
  shows "share x \<bind> (\<lambda> (a1,a2). share y \<bind> (\<lambda> (b1,b2).
             and_protocol (a1,b1) (a2,b2) \<bind> (\<lambda> (a, b). reconstruct (a, b)))) = and_evaluate x y"
proof-
  have "(yc = (\<not> (if x = (\<not> ya) then if snd (snd (ya, x = (\<not> ya)), snd (yb, y = (\<not> yb))) then yc 
            = (fst (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))) \<or> snd (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))))
                   else yc = (fst (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))) \<or> \<not> snd (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))))
                       else if snd (snd (ya, x = (\<not> ya)), snd (yb, y = (\<not> yb))) then yc = (fst (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))) 
                            \<longrightarrow> snd (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))))
                                  else yc = (fst (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))) 
                                      \<longrightarrow> \<not> snd (fst (ya, x = (\<not> ya)), fst (yb, y = (\<not> yb))))))) = (x \<and> y)"
    for yc yb ya by auto
  then show ?thesis 
    by(auto simp add: share_def reconstruct_def and_protocol_def and_evaluate_def split_def correct_14[symmetric] funct_14 bind_spmf_const Let_def)
qed

definition and_R1 :: "(share_1 \<times> share_1) \<Rightarrow> (share_2 \<times> share_2) \<Rightarrow> (((share_1 \<times> share_1) \<times> bool \<times> 'v_14_OT1)  \<times> (share_1 \<times> share_2)) spmf"
  where "and_R1 A B = do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V \<leftarrow> R1_14_OT (s0,s1,s2,s3) (b1,b2);
    (_, s) \<leftarrow> protocol_14_OT (s0,s1,s2,s3) (b1,b2);
    return_spmf (((a1,a2), \<sigma>, V), (\<sigma>, s))}"

lemma lossless_and_R1: "lossless_spmf (and_R1 A B)"
  apply(simp add: and_R1_def split_def lossless_R1_14_OT lossless_protocol_14_OT Let_def)
  by (metis prod.collapse lossless_R1_14_OT)

definition S1_and :: "(share_1 \<times> share_1) \<Rightarrow> bool \<Rightarrow> (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1)) spmf"
  where "S1_and A \<sigma> = do {
    let (a1,a2) = A;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V \<leftarrow> S1_14_OT (s0,s1,s2,s3) ();
    return_spmf ((a1,a2), \<sigma>, V)}"

definition out1 :: "(share_1 \<times> share_1) \<Rightarrow> (share_2 \<times> share_2) \<Rightarrow> bool \<Rightarrow> (share_1 \<times> share_2) spmf"
  where "out1 A B \<sigma> = do {
    let (a1,a2) = A;
    let (b1,b2) = B;
    return_spmf (\<sigma>, \<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2)))}"

definition S1_and' :: "(share_1 \<times> share_1) \<Rightarrow> (share_2 \<times> share_2) \<Rightarrow> bool \<Rightarrow> (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) spmf"
  where "S1_and' A B \<sigma> = do {
    let (a1,a2) = A;
    let (b1,b2) = B;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    V \<leftarrow> S1_14_OT (s0,s1,s2,s3) ();
    return_spmf (((a1,a2), \<sigma>, V), (\<sigma>, \<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2))))}"

lemma sec_ex_P1_and: 
  shows "\<exists> (A :: 'v_14_OT1 \<Rightarrow> bool \<Rightarrow> bool spmf).
          \<bar>spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
            \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True - spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True\<bar> =
              \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. S1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) () 
                \<bind>  (\<lambda> view. A view \<sigma>))) True 
                  - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. R1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) (b1, b2) 
                    \<bind> (\<lambda> view. A view \<sigma>))) True\<bar>"
  including monad_normalisation
proof-
  define A' where "A' == \<lambda> view \<sigma>.  (D (((a1,a2), \<sigma>, view), (\<sigma>, \<sigma> \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2)))))" 
  have "\<bar>spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
          \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True - 
            spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (bool \<times> bool)) \<Rightarrow> bool spmf)) True\<bar> =
              \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma> :: bool. S1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) () 
                \<bind>  (\<lambda> view. A' view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. R1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) (b1, b2) 
                  \<bind> (\<lambda> view. A' view \<sigma>))) True\<bar>"
    by(auto simp add: S1_and'_def A'_def and_funct_def and_R1_def Let_def split_def correct_14[symmetric] funct_14; cases a1; cases a2; cases b1; cases b2; auto)
  then show ?thesis by auto
qed

lemma bound_14_OT:
  "\<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. S1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) () 
        \<bind>  (\<lambda> view. (A :: 'v_14_OT1 \<Rightarrow> bool \<Rightarrow> bool spmf) view \<sigma>))) True - spmf (coin_spmf \<bind> (\<lambda> \<sigma>. R1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) (b1, b2) 
              \<bind> (\<lambda> view. A view \<sigma>))) True\<bar> \<le> adv_14_OT"
  (is "?lhs \<le> adv_14_OT")
proof-
  have int1: "integrable (measure_spmf coin_spmf) (\<lambda>x. spmf (S1_14_OT (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True)) () \<bind> (\<lambda>view. A view x)) True)"
    and int2: "integrable (measure_spmf coin_spmf) (\<lambda>x. spmf (R1_14_OT (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True)) (b1, b2) \<bind> (\<lambda>view. A view x)) True)"
    by(rule measure_spmf.integrable_const_bound[where B=1]; simp add: pmf_le_1)+
  have "?lhs = \<bar>LINT x|measure_spmf coin_spmf.
        spmf (S1_14_OT (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True)) () \<bind> (\<lambda>view. A view x)) True -
        spmf (R1_14_OT (x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> False \<and> a2 \<oplus> True), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> False), x \<oplus> (a1 \<oplus> True \<and> a2 \<oplus> True)) (b1, b2) \<bind> (\<lambda>view. A view x)) True\<bar>"
    apply(subst (1 2) spmf_bind) using int1 int2 by simp
  also have "... \<le> LINT x|measure_spmf coin_spmf. \<bar>spmf (S1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) () \<bind> (\<lambda>view. A view x)) True 
                - spmf (R1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) (b1, b2) \<bind> (\<lambda>view. A view x)) True\<bar>"
    by(rule integral_abs_bound[THEN order_trans]; simp add: split_beta)
  ultimately have "?lhs \<le> LINT x|measure_spmf coin_spmf. \<bar>spmf (S1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) () \<bind> (\<lambda>view. A view x)) True 
                - spmf (R1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) (b1, b2) \<bind> (\<lambda>view. A view x)) True\<bar>"
    by simp
  also have "LINT x|measure_spmf coin_spmf. \<bar>spmf (S1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) () \<bind> (\<lambda>view. A view x)) True 
                - spmf (R1_14_OT (x = (a1 \<longrightarrow> \<not> a2), x = (a1 \<longrightarrow> a2), x = (a1 \<or> \<not> a2), x = (a1 \<or> a2)) (b1, b2) \<bind> (\<lambda>view. A view x)) True\<bar> \<le> adv_14_OT"
    apply(rule integral_mono[THEN order_trans]) 
       apply(rule measure_spmf.integrable_const_bound[where B=2])
        apply clarsimp
        apply(rule abs_triangle_ineq4[THEN order_trans])
        apply(cases a1) apply(cases a2) 
    subgoal for M
      using pmf_le_1[of "R1_14_OT (\<not> M, M, M, M) (b1,b2) \<bind>  (\<lambda> view. A view M)" "Some True"]
        pmf_le_1[of "S1_14_OT (\<not> M, M, M, M) () \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by simp
    subgoal for M 
      using pmf_le_1[of "R1_14_OT  (M, \<not> M, M, M) (b1,b2) \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "S1_14_OT (M, \<not> M, M, M) () \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by simp
        apply(cases a2) apply(auto)
    subgoal for M
      using pmf_le_1[of "R1_14_OT  (M, M, \<not> M, M) (b1,b2) \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "S1_14_OT (M, M, \<not> M, M) () \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by(simp)
    subgoal for M
      using pmf_le_1[of "R1_14_OT  (M, M, M, \<not> M) (b1,b2) \<bind>  (\<lambda> view. A view M)" "Some True"] 
        pmf_le_1[of "S1_14_OT (M, M, M, \<not> M) () \<bind>  (\<lambda> view. A view M)" "Some True"] 
      by(simp)
    using ass_adv_14_OT by fast
  ultimately show ?thesis by simp
qed

lemma security_and_P1:
  shows "\<bar>spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
              \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True - 
                    spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True\<bar> \<le> adv_14_OT"
proof-
  obtain A :: "'v_14_OT1 \<Rightarrow> bool \<Rightarrow> bool spmf" where A: 
    "\<bar>spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) \<bind> D)) True - spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True\<bar> =
       \<bar>spmf (coin_spmf \<bind> (\<lambda> \<sigma>. S1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) () 
         \<bind>  (\<lambda> view. A view \<sigma>))) True - spmf (coin_spmf 
           \<bind> (\<lambda> \<sigma>. R1_14_OT ((\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False))), (\<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)))) (b1, b2)
             \<bind> (\<lambda> view. A view \<sigma>))) True\<bar>" 
    using sec_ex_P1_and by blast
  then show ?thesis using bound_14_OT[of "a1" "a2" "A" "b1" "b2" ] by metis
qed

lemma security_and_P1':
  shows "\<bar>spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True - 
           spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
            \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True\<bar> \<le> adv_14_OT"
proof-
  have "\<bar>spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True - 
          spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
            \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True\<bar> =
              \<bar>spmf ((and_funct (a1, a2) (b1,b2)) \<bind> (\<lambda> (s1, s2). (S1_and' (a1,a2) (b1,b2) s1) 
                \<bind> (D :: (((bool \<times> bool) \<times> bool \<times> 'v_14_OT1) \<times> (share_1 \<times> share_2)) \<Rightarrow> bool spmf))) True - 
                  spmf ((and_R1 (a1, a2) (b1,b2)) \<bind> D) True\<bar>" using abs_minus_commute by blast
  thus ?thesis using security_and_P1 by simp
qed

definition and_R2 :: "(share_1 \<times> share_2) \<Rightarrow> (share_2 \<times> share_1) \<Rightarrow> (((bool \<times> bool) \<times> 'v_14_OT2) \<times> (share_1 \<times> share_2)) spmf"
  where "and_R2 A B = do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    \<sigma> \<leftarrow> coin_spmf;
    let s0 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> False));   
    let s1 = \<sigma> \<oplus> ((a1 \<oplus> False) \<and> (a2 \<oplus> True));   
    let s2 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> False));   
    let s3 = \<sigma> \<oplus> ((a1 \<oplus> True) \<and> (a2 \<oplus> True)); 
    (_, s) \<leftarrow> protocol_14_OT (s0,s1,s2,s3) B;
    V \<leftarrow> R2_14_OT (s0,s1,s2,s3) B;
    return_spmf ((B, V), (\<sigma>, s))}"

lemma lossless_and_R2: "lossless_spmf (and_R2 A B)"
  apply(simp add: and_R2_def split_def lossless_R2_14_OT lossless_protocol_14_OT Let_def) 
  by (metis lossless_R2_14_OT prod.collapse)

definition S2_and :: "(share_1 \<times> share_2) \<Rightarrow> bool \<Rightarrow> (((bool \<times> bool) \<times> 'v_14_OT2)) spmf"
  where "S2_and B s2 =  do {
    let (a2,b2) = B;
    V :: 'v_14_OT2 \<leftarrow> S2_14_OT (a2,b2) s2;
    return_spmf ((B, V))}"

definition out2 :: "(share_1 \<times> share_2) \<Rightarrow> (share_1 \<times> share_2) \<Rightarrow> bool \<Rightarrow> (share_1 \<times> share_2) spmf"
  where "out2 B A s2 = do {
    let (a1, b1) = A;
    let (a2,b2) = B;
    let s1 = s2 \<oplus> ((a1 \<oplus> a2) \<and> (b1 \<oplus> b2));
    return_spmf (s1, s2)}"

definition S2_and' :: "(share_1 \<times> share_2) \<Rightarrow> (share_1 \<times> share_2) \<Rightarrow> bool \<Rightarrow> (((bool \<times> bool) \<times> 'v_14_OT2) \<times> (share_1 \<times> share_2)) spmf"
  where "S2_and' B A s2 =  do {
    let (a1, a2) = A;
    let (b1,b2) = B;
    V :: 'v_14_OT2 \<leftarrow> S2_14_OT B s2;
    let s1 = s2 \<oplus> ((a1 \<oplus> b1) \<and> (a2 \<oplus> b2));
    return_spmf ((B, V), s1, s2)}"

lemma lossless_S2_and: "lossless_spmf (S2_and B s2)"
  apply(simp add: S2_and_def split_def)
  by(metis prod.collapse lossless_S2_14_OT) 

sublocale and_secret_sharing: sim_non_det_def and_R1 S1_and out1 and_R2 S2_and out2 and_funct .

lemma ideal_S1_and: "and_secret_sharing.Ideal1 (a1, b1) (a2, b2) s2 = S1_and' (a1, b1) (a2, b2) s2"
  by(simp add: Let_def and_secret_sharing.Ideal1_def S1_and'_def split_def out1_def S1_and_def)

lemma and_P2_security: "and_secret_sharing.perfect_sec_P2 m1 m2"
proof-
  have "and_R2 (a1, b1) (a2, b2) = and_funct (a1, b1) (a2, b2) \<bind> (\<lambda>(s1, s2). and_secret_sharing.Ideal2 (a2, b2) (a1, b1) s2)"
    for a1 a2 b1 b2
    apply(auto simp add: split_def inf_th_14_OT_P4  S2_and'_def and_R2_def and_funct_def Let_def correct_14[symmetric] and_secret_sharing.Ideal2_def S2_and_def out2_def)
    apply(simp only: funct_14) 
    apply auto
    by(cases b1;cases b2; cases a1; cases a2; auto) 
  thus ?thesis
    by(simp add: and_secret_sharing.perfect_sec_P2_def; metis  prod.collapse)
qed

lemma and_P1_security: "and_secret_sharing.adv_P1 m1 m2 D \<le> adv_14_OT"
proof-
  have "\<bar>spmf (and_R1 (a1, a2) (b1, b2) \<bind> D) True -
            spmf (and_funct (a1, a2) (b1, b2) \<bind> (\<lambda>(s1, s2). 
                and_secret_sharing.Ideal1 (a1, a2) (b1, b2) s1 \<bind> D)) True\<bar>
                    \<le> adv_14_OT" for a1 a2 b1 b2 
    using security_and_P1' ideal_S1_and prod.collapse by simp 
  thus ?thesis 
    by(simp add:  and_secret_sharing.adv_P1_def; metis prod.collapse)
qed

definition "F = {and_evaluate, xor_evaluate}"

lemma share_reconstruct_xor: "share x \<bind> (\<lambda>(a1, a2). share y \<bind> (\<lambda>(b1, b2). 
          xor_protocol (a1, b1) (a2, b2) \<bind> (\<lambda>(a, b). 
              reconstruct (a, b)))) = xor_evaluate x y"
proof-
  have "(((ya = (x = ya)) = (yb = (y = (\<not> yb))))) = (x = (\<not> y))" for ya yb by auto
  thus ?thesis
    by(simp add: xor_protocol_def share_def reconstruct_def xor_evaluate_def bind_spmf_const)
qed

sublocale share_correct: secret_sharing_scheme share reconstruct F .

lemma "share_correct.sharing_correct input"
  by(simp add: share_correct.sharing_correct_def reconstruct_share) 

lemma "share_correct.correct_share_eval input1 input2"
  unfolding share_correct.correct_share_eval_def
  apply(auto simp add: F_def) 
  using share_and_reconstruct apply auto 
  using share_reconstruct_xor by force

end 

locale gmw_asym =
  fixes S1_14_OT :: "nat \<Rightarrow> msgs_14_OT \<Rightarrow> unit \<Rightarrow> 'v_14_OT1 spmf"
    and R1_14_OT :: "nat \<Rightarrow> msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> 'v_14_OT1 spmf"
    and S2_14_OT :: "nat \<Rightarrow> choice_14_OT \<Rightarrow> bool \<Rightarrow> 'v_14_OT2 spmf" 
    and R2_14_OT :: "nat \<Rightarrow> msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> 'v_14_OT2 spmf"
    and protocol_14_OT :: "nat \<Rightarrow> msgs_14_OT \<Rightarrow> choice_14_OT \<Rightarrow> (unit \<times> bool) spmf"
    and adv_14_OT :: "nat \<Rightarrow> real"
  assumes gmw_base: "\<And> (n::nat). gmw_base (S1_14_OT n) (R1_14_OT n) (S2_14_OT n) (R2_14_OT n) (protocol_14_OT n) (adv_14_OT n)"
begin

sublocale gmw_base "(S1_14_OT n)" "(R1_14_OT n)" "(S2_14_OT n)" "(R2_14_OT n)" "(protocol_14_OT n)" "(adv_14_OT n)"
  by (simp add: gmw_base)

lemma "xor_sim_det.perfect_sec_P1 m1 m2" 
  by (simp add: P1_xor_inf_th xor_sim_det.perfect_sec_P1_def)

lemma "xor_sim_det.perfect_sec_P2 m1 m2"
  by (simp add: P2_xor_inf_th xor_sim_det.perfect_sec_P2_def)

lemma and_P1_adv_negligible:
  assumes "negligible (\<lambda> n. adv_14_OT n)"
  shows "negligible (\<lambda> n. and_secret_sharing.adv_P1 n m1 m2 D)" 
proof-
  have "and_secret_sharing.adv_P1 n m1 m2 D \<le> adv_14_OT n" for n
    by (simp add: and_P1_security)
  thus ?thesis 
    using and_secret_sharing.adv_P1_def assms negligible_le by auto
qed

lemma and_P2_security: "and_secret_sharing.perfect_sec_P2 n m1 m2" 
  by (simp add: and_P2_security)

end

end


