section \<open>Semi-Honest Security\<close> 

text \<open>We follow the security definitions for the semi honest setting as described in \cite{DBLP:books/sp/17/Lindell17}.
In the semi honest model the parties are assumed not to deviate from the protocol transcript. 
Semi honest security guarantees that no information is leaked during the running of the protocol.\<close>

subsection \<open>Security definitions\<close>

theory Semi_Honest_Def imports
  CryptHOL.CryptHOL
begin

subsubsection \<open>Security for deterministic functionalities\<close>

locale sim_det_def = 
  fixes R1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view1 spmf"
    and S1  :: "'msg1 \<Rightarrow> 'out1 \<Rightarrow> 'view1 spmf" 
    and R2 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view2 spmf"
    and S2  :: "'msg2 \<Rightarrow> 'out2 \<Rightarrow> 'view2 spmf"
    and funct :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('out1 \<times> 'out2) spmf"
    and protocol :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('out1 \<times> 'out2) spmf"
  assumes lossless_R1: "lossless_spmf (R1 m1 m2)" 
    and lossless_S1: "lossless_spmf (S1 m1 out1)"
    and lossless_R2: "lossless_spmf (R2 m1 m2)" 
    and lossless_S2: "lossless_spmf (S2 m2 out2)"
    and lossless_funct: "lossless_spmf (funct m1 m2)"
begin

type_synonym 'view' adversary_det = "'view' \<Rightarrow> bool spmf"

definition "correctness m1 m2 \<equiv> (protocol m1 m2 = funct m1 m2)"

definition adv_P1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view1 adversary_det \<Rightarrow> real" 
  where "adv_P1 m1 m2 D \<equiv> \<bar>(spmf (R1 m1 m2 \<bind> D) True) 
            - spmf (funct m1 m2 \<bind> (\<lambda> (o1, o2). S1 m1 o1 \<bind> D)) True\<bar>"

definition "perfect_sec_P1 m1 m2 \<equiv> (R1 m1 m2 = funct m1 m2 \<bind> (\<lambda> (s1, s2). S1 m1 s1))"

definition adv_P2 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view2 adversary_det \<Rightarrow> real"
  where "adv_P2 m1 m2 D = \<bar>spmf (R2 m1 m2 \<bind> (\<lambda> view. D view)) True 
            - spmf (funct m1 m2 \<bind> (\<lambda> (o1, o2). S2 m2 o2 \<bind> (\<lambda> view. D view))) True\<bar>"

definition "perfect_sec_P2 m1 m2 \<equiv> (R2 m1 m2 = funct m1 m2 \<bind> (\<lambda> (s1, s2). S2 m2 s2))"
 
text \<open>We also define the security games (for Party 1 and 2) used in EasyCrypt to define semi honest security for Party 1. 
We then show the two definitions are equivalent.\<close>

definition P1_game_alt :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view1 adversary_det \<Rightarrow> bool spmf"
  where "P1_game_alt m1 m2 D = do {
    b \<leftarrow> coin_spmf;
    (out1, out2) \<leftarrow> funct m1 m2;
    rview :: 'view1 \<leftarrow> R1 m1 m2;
    sview :: 'view1 \<leftarrow> S1 m1 out1;
    b' \<leftarrow> D (if b then rview else sview);
    return_spmf (b = b')}"

definition adv_P1_game :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view1 adversary_det \<Rightarrow> real"
  where "adv_P1_game m1 m2 D = \<bar>2*(spmf (P1_game_alt m1 m2 D ) True) - 1\<bar>"

text \<open>We show the two definitions are equivalent\<close>

lemma equiv_defs_P1:
  assumes lossless_D: "\<forall> view. lossless_spmf ((D:: 'view1 adversary_det) view)" 
  shows "adv_P1_game m1 m2 D = adv_P1 m1 m2 D"
  including monad_normalisation
proof-
  have return_True_not_False: "spmf (return_spmf (b)) True = spmf (return_spmf (\<not> b)) False" 
    for b by(cases b; auto)
  have lossless_ideal: "lossless_spmf ((funct m1 m2 \<bind> (\<lambda>(out1, out2). S1 m1 out1 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b'))))))"
    by(simp add: lossless_S1 lossless_funct lossless_weight_spmfD split_def lossless_D)
  have return: "spmf (funct m1 m2 \<bind> (\<lambda>(o1, o2). S1 m1 o1 \<bind> D)) True 
                  = spmf (funct m1 m2 \<bind> (\<lambda>(o1, o2). S1 m1 o1 \<bind> (\<lambda> view. D view \<bind> (\<lambda> b. return_spmf b)))) True"
    by simp
  have "2*(spmf (P1_game_alt m1 m2 D ) True) - 1 = (spmf (R1 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
        - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S1 m1 out1 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)"
    by(simp add: spmf_bind integral_spmf_of_set adv_P1_game_def P1_game_alt_def spmf_of_set
          UNIV_bool bind_spmf_const lossless_R1 lossless_S1 lossless_funct lossless_weight_spmfD)
   hence "adv_P1_game m1 m2 D = \<bar>(spmf (R1 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
        - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S1 m1 out1 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)\<bar>" 
     using adv_P1_game_def by simp 
    also have "\<bar>(spmf (R1 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
                      - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S1 m1 out1 \<bind> (\<lambda>sview. D sview 
                            \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)\<bar> = adv_P1 m1 m2 D" 
    apply(simp only: adv_P1_def spmf_False_conv_True[symmetric] lossless_ideal; simp) 
    by(simp only: return)(simp only: split_def spmf_bind return_True_not_False)
  ultimately show ?thesis by simp
qed

definition P2_game_alt :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view2 adversary_det \<Rightarrow> bool spmf"
  where "P2_game_alt m1 m2 D = do {
    b \<leftarrow> coin_spmf;
    (out1, out2) \<leftarrow> funct m1 m2;
    rview :: 'view2 \<leftarrow> R2 m1 m2;
    sview :: 'view2 \<leftarrow> S2 m2 out2;
    b' \<leftarrow> D (if b then rview else sview);
    return_spmf (b = b')}"

definition adv_P2_game :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'view2 adversary_det \<Rightarrow> real"
  where "adv_P2_game m1 m2 D = \<bar>2*(spmf (P2_game_alt m1 m2 D ) True) - 1\<bar>"

lemma equiv_defs_P2:
  assumes lossless_D: "\<forall> view. lossless_spmf ((D:: 'view2 adversary_det) view)" 
  shows "adv_P2_game m1 m2 D = adv_P2 m1 m2 D"
  including monad_normalisation
proof-
  have return_True_not_False: "spmf (return_spmf (b)) True = spmf (return_spmf (\<not> b)) False" 
    for b by(cases b; auto)
  have lossless_ideal: "lossless_spmf ((funct m1 m2 \<bind> (\<lambda>(out1, out2). S2 m2 out2 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b'))))))"
      by(simp add: lossless_S2 lossless_funct lossless_weight_spmfD split_def lossless_D)
  have return: "spmf (funct m1 m2 \<bind> (\<lambda>(o1, o2). S2 m2 o2 \<bind> D)) True = spmf (funct m1 m2 \<bind> (\<lambda>(o1, o2). S2 m2 o2 \<bind> (\<lambda> view. D view \<bind> (\<lambda> b. return_spmf b)))) True"
    by simp
  have 
    "2*(spmf (P2_game_alt m1 m2 D ) True) - 1 = (spmf (R2 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
        - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S2 m2 out2 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)"
    by(simp add: spmf_bind integral_spmf_of_set adv_P1_game_def P2_game_alt_def spmf_of_set 
          UNIV_bool bind_spmf_const lossless_R2 lossless_S2 lossless_funct lossless_weight_spmfD)
   hence "adv_P2_game m1 m2 D = \<bar>(spmf (R2 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
        - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S2 m2 out2 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)\<bar>"
     using adv_P2_game_def by simp 
    also have "\<bar>(spmf (R2 m1 m2 \<bind> (\<lambda>rview. D rview \<bind> (\<lambda>(b':: bool). return_spmf (True = b'))))) True
        - (1 - (spmf (funct m1 m2 \<bind> (\<lambda>(out1, out2). S2 m2 out2 \<bind> (\<lambda>sview. D sview \<bind> (\<lambda>b'. return_spmf (False = b')))))) True)\<bar> = adv_P2 m1 m2 D" 
    apply(simp only: adv_P2_def spmf_False_conv_True[symmetric] lossless_ideal; simp) 
    by(simp only: return)(simp only: split_def spmf_bind return_True_not_False)
  ultimately show ?thesis by simp
qed

end 

subsubsection \<open> Security definitions for non deterministic functionalities \<close>

locale sim_non_det_def = 
  fixes R1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('view1 \<times> ('out1 \<times> 'out2)) spmf"
    and S1  :: "'msg1 \<Rightarrow> 'out1 \<Rightarrow> 'view1 spmf"
    and Out1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'out1 \<Rightarrow> ('out1 \<times> 'out2) spmf" \<comment> \<open>takes the input of the other party so can form the outputs of parties\<close>
    and R2 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('view2 \<times> ('out1 \<times> 'out2)) spmf"
    and S2  :: "'msg2 \<Rightarrow> 'out2 \<Rightarrow> 'view2 spmf"
    and Out2 :: "'msg2 \<Rightarrow> 'msg1 \<Rightarrow> 'out2 \<Rightarrow> ('out1 \<times> 'out2) spmf"
    and funct :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('out1 \<times> 'out2) spmf"
begin

type_synonym ('view', 'out1', 'out2') adversary_non_det = "('view' \<times> ('out1' \<times> 'out2')) \<Rightarrow> bool spmf"

definition Ideal1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> 'out1  \<Rightarrow> ('view1 \<times> ('out1 \<times> 'out2)) spmf"
  where "Ideal1 m1 m2 out1 = do {
    view1 :: 'view1 \<leftarrow> S1 m1 out1;
    out1 \<leftarrow> Out1 m1 m2 out1;
    return_spmf (view1, out1)}"

definition Ideal2 :: "'msg2 \<Rightarrow> 'msg1 \<Rightarrow> 'out2 \<Rightarrow> ('view2 \<times> ('out1 \<times> 'out2)) spmf"
  where "Ideal2 m2 m1 out2 = do {
    view2 :: 'view2 \<leftarrow> S2 m2 out2;
    out2 \<leftarrow> Out2 m2 m1 out2;
    return_spmf (view2, out2)}"

definition adv_P1 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('view1, 'out1, 'out2) adversary_non_det \<Rightarrow> real"
  where "adv_P1 m1 m2 D \<equiv> \<bar>(spmf (R1 m1 m2 \<bind> (\<lambda> view. D view)) True) - spmf (funct m1 m2 \<bind> (\<lambda> (o1, o2). Ideal1 m1 m2 o1 \<bind> (\<lambda> view. D view))) True\<bar>"

definition "perfect_sec_P1 m1 m2 \<equiv> (R1 m1 m2 = funct m1 m2 \<bind> (\<lambda> (s1, s2). Ideal1 m1 m2 s1))"

definition adv_P2 :: "'msg1 \<Rightarrow> 'msg2 \<Rightarrow> ('view2, 'out1, 'out2) adversary_non_det \<Rightarrow> real"
  where "adv_P2 m1 m2 D = \<bar>spmf (R2 m1 m2 \<bind> (\<lambda> view. D view)) True - spmf (funct m1 m2 \<bind> (\<lambda> (o1, o2). Ideal2 m2 m1 o2 \<bind> (\<lambda> view. D view))) True\<bar>"

definition "perfect_sec_P2 m1 m2 \<equiv> (R2 m1 m2 = funct m1 m2 \<bind> (\<lambda> (s1, s2). Ideal2 m2 m1 s2))"

end 

subsubsection \<open> Secret sharing schemes \<close>

locale secret_sharing_scheme = 
  fixes share :: "'input_out \<Rightarrow> ('share \<times> 'share) spmf"
    and reconstruct :: "('share \<times> 'share) \<Rightarrow> 'input_out spmf"
    and F :: "('input_out \<Rightarrow> 'input_out \<Rightarrow> 'input_out spmf) set"
begin

definition "sharing_correct input \<equiv> (share input \<bind> (\<lambda> (s1,s2). reconstruct (s1,s2)) = return_spmf input)"

definition "correct_share_eval input1 input2 \<equiv> (\<forall> gate_eval \<in> F. 
              \<exists> gate_protocol :: ('share \<times> 'share) \<Rightarrow> ('share \<times> 'share) \<Rightarrow> ('share \<times> 'share) spmf. 
                  share input1 \<bind> (\<lambda> (s1,s2). share input2 
                      \<bind> (\<lambda> (s3,s4). gate_protocol (s1,s3) (s2,s4) 
                          \<bind> (\<lambda> (S1,S2). reconstruct (S1,S2)))) = gate_eval input1 input2)"

end

end

