section \<open>Malicious Security\<close>

text \<open>Here we define security in the malicious security setting. We follow the definitions given in 
\cite{DBLP:series/isc/HazayL10} and \cite{DBLP:books/cu/Goldreich2004}. The definition of malicious security 
follows the real/ideal world paradigm.\<close>

subsection \<open>Malicious Security Definitions\<close>

theory Malicious_Defs imports
  CryptHOL.CryptHOL
begin

type_synonym ('in1','aux', 'P1_S1_aux') P1_ideal_adv1 = "'in1' \<Rightarrow> 'aux' \<Rightarrow> ('in1' \<times> 'P1_S1_aux') spmf"

type_synonym ('in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_ideal_adv2 = "'in1' \<Rightarrow> 'aux' \<Rightarrow> 'out1' \<Rightarrow> 'P1_S1_aux' \<Rightarrow> 'adv_out1' spmf"

type_synonym ('in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_ideal_adv = "('in1','aux', 'P1_S1_aux') P1_ideal_adv1 \<times> ('in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_ideal_adv2"

type_synonym ('P1_real_adv', 'in1', 'aux', 'P1_S1_aux') P1_sim1 = "'P1_real_adv' \<Rightarrow> 'in1' \<Rightarrow> 'aux' \<Rightarrow> ('in1' \<times> 'P1_S1_aux') spmf"

type_synonym ('P1_real_adv', 'in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_sim2 
                  = "'P1_real_adv' \<Rightarrow> 'in1' \<Rightarrow> 'aux' \<Rightarrow> 'out1' 
                      \<Rightarrow> 'P1_S1_aux' \<Rightarrow> 'adv_out1' spmf"

type_synonym ('P1_real_adv', 'in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_sim  
                = "(('P1_real_adv', 'in1', 'aux', 'P1_S1_aux') P1_sim1 
                    \<times> ('P1_real_adv', 'in1', 'aux', 'out1', 'P1_S1_aux', 'adv_out1') P1_sim2)"

type_synonym ('in2','aux', 'P2_S2_aux') P2_ideal_adv1 = "'in2' \<Rightarrow> 'aux' \<Rightarrow> ('in2' \<times> 'P2_S2_aux') spmf"

type_synonym ('in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_ideal_adv2 
                = "'in2' \<Rightarrow> 'aux' \<Rightarrow> 'out2' \<Rightarrow> 'P2_S2_aux' \<Rightarrow> 'adv_out2' spmf"

type_synonym ('in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_ideal_adv 
                    = "('in2','aux', 'P2_S2_aux') P2_ideal_adv1 
                        \<times> ('in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_ideal_adv2"

type_synonym ('P2_real_adv', 'in2', 'aux', 'P2_S2_aux') P2_sim1 = "'P2_real_adv' \<Rightarrow> 'in2' \<Rightarrow> 'aux' \<Rightarrow> ('in2' \<times> 'P2_S2_aux') spmf"

type_synonym ('P2_real_adv', 'in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_sim2 
                  = "'P2_real_adv' \<Rightarrow> 'in2' \<Rightarrow> 'aux' \<Rightarrow> 'out2' 
                      \<Rightarrow> 'P2_S2_aux' \<Rightarrow> 'adv_out2' spmf"

type_synonym ('P2_real_adv', 'in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_sim 
                  = "(('P2_real_adv', 'in2', 'aux', 'P2_S2_aux') P2_sim1 
                      \<times> ('P2_real_adv', 'in2', 'aux', 'out2', 'P2_S2_aux', 'adv_out2') P2_sim2)"

locale malicious_base =
  fixes funct :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> ('out1 \<times> 'out2) spmf" \<comment> \<open>the functionality\<close>
    and protocol :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> ('out1 \<times> 'out2) spmf" \<comment> \<open>outputs the output of each party in the protocol\<close>
    and S1_1 :: "('P1_real_adv, 'in1, 'aux, 'P1_S1_aux) P1_sim1" \<comment> \<open>first part of the simulator for party 1\<close>
    and S1_2 :: "('P1_real_adv, 'in1, 'aux, 'out1, 'P1_S1_aux, 'adv_out1) P1_sim2" \<comment> \<open>second part of the simulator for party 1\<close>
    and P1_real_view :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> 'P1_real_adv \<Rightarrow> ('adv_out1 \<times> 'out2) spmf" \<comment> \<open>real view for party 1, the adversary totally controls party 1\<close>
    and S2_1 :: "('P2_real_adv, 'in2, 'aux, 'P2_S2_aux) P2_sim1" \<comment> \<open>first part of the simulator for party 2\<close>
    and S2_2 :: "('P2_real_adv, 'in2, 'aux, 'out2, 'P2_S2_aux, 'adv_out2) P2_sim2" \<comment> \<open>second part of the simulator for party 1\<close>
    and P2_real_view :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> 'P2_real_adv \<Rightarrow> ('out1 \<times> 'adv_out2) spmf" \<comment> \<open>real view for party 2, the adversary totally controls party 2\<close>
begin

definition "correct m1 m2 \<longleftrightarrow> (protocol m1 m2 = funct m1 m2)"

abbreviation "trusted_party x y \<equiv> funct x y"

text\<open>The ideal game defines the ideal world. First we consider the case where party 1 is corrupt, and thus 
controlled by the adversary. The adversary is split into two parts, the first part takes the original input and 
auxillary information and outputs its input to the protocol. The trusted party then computes the functionality on
the input given by the adversary and the correct input for party 2. Party 2 outputs the its correct output as
given by the trusted party, the adversary provides the output for party 1.\<close>

definition ideal_game_1 :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> ('in1, 'aux, 'out1, 'P1_S1_aux, 'adv_out1) P1_ideal_adv \<Rightarrow> ('adv_out1 \<times> 'out2) spmf"
  where "ideal_game_1 x y z A = do {
    let (A1,A2) = A;
    (x', aux_out) \<leftarrow> A1 x z;
    (out1, out2) \<leftarrow> trusted_party x' y; 
    out1' :: 'adv_out1 \<leftarrow> A2 x' z out1 aux_out; 
    return_spmf (out1', out2)}" 

definition ideal_view_1 :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> ('P1_real_adv, 'in1, 'aux, 'out1, 'P1_S1_aux, 'adv_out1) P1_sim \<Rightarrow> 'P1_real_adv \<Rightarrow> ('adv_out1 \<times> 'out2) spmf"
  where "ideal_view_1 x y z S \<A> = (let (S1, S2) = S in (ideal_game_1 x y z (S1 \<A>, S2 \<A>)))" 

text\<open>We have information theoretic security when the real and ideal views are equal.\<close>

definition "perfect_sec_P1 x y z S \<A> \<longleftrightarrow> (ideal_view_1 x y z S \<A> = P1_real_view x y z \<A>)"

text\<open>The advantage of party 1 denotes the probability of a distinguisher distinguishing the real and 
ideal views.\<close>

definition "adv_P1 x y z S \<A> (D :: ('adv_out1 \<times> 'out2) \<Rightarrow> bool spmf) = 
                \<bar>spmf (P1_real_view x y z \<A> \<bind> (\<lambda> view. D view)) True
                    - spmf (ideal_view_1 x y z S \<A> \<bind> (\<lambda> view. D view)) True \<bar>" 

definition ideal_game_2 :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> ('in2, 'aux, 'out2, 'P2_S2_aux, 'adv_out2) P2_ideal_adv \<Rightarrow> ('out1 \<times> 'adv_out2) spmf"
  where "ideal_game_2 x y z A = do {
    let (A1,A2) = A;
    (y', aux_out) \<leftarrow> A1 y z; 
    (out1, out2) \<leftarrow> trusted_party x y';
    out2' :: 'adv_out2 \<leftarrow> A2 y' z out2 aux_out; 
    return_spmf (out1, out2')}"   

definition ideal_view_2 :: "'in1 \<Rightarrow> 'in2 \<Rightarrow> 'aux \<Rightarrow> ('P2_real_adv, 'in2, 'aux, 'out2, 'P2_S2_aux, 'adv_out2) P2_sim \<Rightarrow> 'P2_real_adv \<Rightarrow> ('out1 \<times> 'adv_out2) spmf"
  where "ideal_view_2 x y z S \<A> = (let (S1, S2) = S in (ideal_game_2 x y z (S1 \<A>, S2 \<A>)))" 

definition "perfect_sec_P2 x y z S \<A> \<longleftrightarrow> (ideal_view_2 x y z S \<A> = P2_real_view x y z \<A>)"

definition "adv_P2 x y z S \<A> (D :: ('out1 \<times> 'adv_out2) \<Rightarrow> bool spmf) = 
                \<bar>spmf (P2_real_view x y z \<A> \<bind> (\<lambda> view. D view)) True
                    - spmf (ideal_view_2 x y z S \<A> \<bind> (\<lambda> view. D view)) True \<bar>" 


end

end