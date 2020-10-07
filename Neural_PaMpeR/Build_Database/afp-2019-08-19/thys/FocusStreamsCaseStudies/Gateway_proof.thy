(*<*)
(*
   Title: Gateway_proof.thy  (Gateway: Verification)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)

(* header {*Gateway: Verification *} *)

theory Gateway_proof 
imports Gateway_proof_aux
begin

subsection \<open>Properties of the Gateway\<close>

lemma Gateway_L1:
  assumes h1:"Gateway req dt a stop lose d ack i vc"
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) a"
      and h4:"msg (Suc 0) stop" 
      and h5:"ts lose"
      and h6:"ack t = [init_state]"
      and h7:"req (Suc t) = [init]"
      and h8:"lose (Suc t) = [False]"
      and h9:"lose (Suc (Suc t)) = [False]"
  shows "ack (Suc (Suc t)) = [connection_ok]" 
proof - 
  from h1 obtain i1 i2 x y
    where a1:"Sample req dt x stop lose ack i1 vc"
      and a2:"Delay y i1 d x i2"
      and a3:"Loss lose a i2 y i"
    by (simp only: Gateway_def, auto) 
  from a2 and a3 and h3 have sg1:"msg (Suc 0) x"   
    by (simp add: Loss_Delay_msg_a) 
  from a1 and h2 and h4 and sg1 obtain st buffer where a4:
    "tiTable_SampleT req x stop lose 
        (fin_inf_append [init_state] st) (fin_inf_append [[]] buffer) ack
         i1 vc st"
     by (simp add: Sample_def Sample_L_def, auto)
  from a4 and h5 and sg1 and h4 have sg2:"st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from h6 and sg1 and sg2 and h4 have sg3:
   "(fin_inf_append [init_state] st) (Suc t) = init_state"
    by (simp add: correct_fin_inf_append1)
  from a4 and h7 and sg3 have sg4:"st (Suc t) = call"
    by (simp add: tiTable_SampleT_def)
  from sg4 have sg5:"(fin_inf_append [init_state] st) (Suc (Suc t)) = call"
    by (simp add: correct_fin_inf_append1)
  from a4 and sg5 and assms show ?thesis 
    by (simp add: tiTable_SampleT_def)
qed

lemma Gateway_L2:
  assumes h1:"Gateway req dt a stop lose d ack i vc"
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) a"
      and h4:"msg (Suc 0) stop" 
      and h5:"ts lose"
      and h6:"ack t = [connection_ok]"
      and h7:"req (Suc t) = [send]"
      and h8:"\<forall>k\<le>Suc d. lose (t + k) = [False]" 
  shows "i (Suc (t + d))  = inf_last_ti dt t"
proof - 
  from h1 obtain i1 i2 x y
    where a1:"Sample req dt x stop lose ack i1 vc"
      and a2:"Delay y i1 d x i2"
      and a3:"Loss lose a i2 y i"
    by (simp only: Gateway_def, auto) 
  from a2 and a3 and h3 have sg1:"msg (Suc 0) x"   
    by (simp add: Loss_Delay_msg_a) 
  from a1 and h2 and h4 and sg1 obtain st buffer where a4:
    "Sample_L req dt x stop lose (fin_inf_append [init_state] st) 
         (fin_inf_append [[]] buffer) ack i1 vc st buffer"
    by (simp add: Sample_def, auto)
  from a4 have sg2:"buffer t = inf_last_ti dt t"
    by (simp add: Sample_L_buffer) 
  from assms and a1 and a4 and sg1 and sg2 have sg3:"i1 (Suc t) =  buffer t"
    by (simp add: Sample_L_i1_buffer)
  from a2 and sg1 have sg4:"i2 ((Suc t) + d)  =  i1 (Suc t)"
    by (simp add: Delay_def)
  from a3 and h8 have sg5:"i ((Suc t) + d)  =  i2 ((Suc t) + d)"
    by (simp add: Loss_def, auto)
  from sg5 and sg4 and sg3 and sg2 show ?thesis by simp
qed

lemma Gateway_L3:
  assumes h1:"Gateway req dt a stop lose d ack i vc"
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) a"
      and h4:"msg (Suc 0) stop" 
      and h5:"ts lose"
      and h6:"ack t = [connection_ok]"
      and h7:"req (Suc t) = [send]"
      and h8:"\<forall>k\<le>Suc d. lose (t + k) = [False]" 
  shows "ack (Suc t) = [sending_data]"
proof - 
  from h1 obtain i1 i2 x y
    where a1:"Sample req dt x stop lose ack i1 vc"
      and a2:"Delay y i1 d x i2"
      and a3:"Loss lose a i2 y i"
    by (simp only: Gateway_def, auto) 
  from a2 and a3 and h3 have sg1:"msg (Suc 0) x"   
    by (simp add: Loss_Delay_msg_a) 
  from a1 and h2 and h4 and sg1 obtain st buffer where a4:
    "tiTable_SampleT req x stop lose 
        (fin_inf_append [init_state] st) (fin_inf_append [[]] buffer) ack
         i1 vc st"
     by (simp add: Sample_def Sample_L_def, auto)
  from a4 and h5 and sg1 and h4 have sg2:"st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from sg2 and h6 have sg3:"(fin_inf_append [init_state] st) (Suc t) = connection_ok"
    by (simp add: correct_fin_inf_append1)
  from h8 have sg4:"lose (Suc t) = [False]" by auto
  from a4 and sg3 and sg4 and h7 have sg5:"st (Suc t) = sending_data"
    by (simp add: tiTable_SampleT_def) 
  from a4 and h2 and sg1 and h4 and h5 have sg6:"ack (Suc t) = [st (Suc t)]"
    by (simp add: tiTable_ack_st)
  from sg5 and sg6 show ?thesis by simp  
qed

lemma Gateway_L4:
  assumes h1:"Gateway req dt a stop lose d ack i vc"
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) a"
      and h4:"msg (Suc 0) stop" 
      and h5:"ts lose"
      and h6:"ack (t + d) = [sending_data]"
      and h7:"a (Suc t) = [sc_ack]"
      and h8:"\<forall>k\<le>Suc d. lose (t + k) = [False]" 
  shows "vc (Suc (t + d)) = [vc_com]"
proof - 
  from h1 obtain i1 i2 x y
    where a1:"Sample req dt x stop lose ack i1 vc"
       and a2:"Delay y i1 d x i2"
       and a3:"Loss lose a i2 y i"
    by (simp only: Gateway_def, auto) 
  from a2 and a3 and h3 have sg1:"msg (Suc 0) x"   
    by (simp add: Loss_Delay_msg_a) 
  from a1 and h2 and h4 and sg1 obtain st buffer where a4:
    "tiTable_SampleT req x stop lose 
        (fin_inf_append [init_state] st) (fin_inf_append [[]] buffer) ack
         i1 vc st"
     by (simp add: Sample_def Sample_L_def, auto)
  from a4 and h5 and sg1 and h4 have sg2:"st (t+d) =  hd (ack (t+d))"
    by (simp add: tiTable_ack_st_hd)  
  from sg2 and h6 have sg3:"(fin_inf_append [init_state] st) (Suc (t+d)) = sending_data"
    by (simp add: correct_fin_inf_append1)
  from a3 and h8 have sg4:"y (Suc t)  =  a (Suc t)"
    by (simp add: Loss_def, auto)
  from a2 and sg1 have sg5:"x ((Suc t) + d)  =  y (Suc t)"
    by (simp add: Delay_def) 
  from sg5 and sg4 and h7 have sg6:" x (Suc (t + d)) = [sc_ack]" by simp
  from h8 have sg7:"lose (Suc (t + d)) = [False]" by auto
  from sg6 and a4 and h2 and sg1 and h4 and h5 and sg7 and sg3 show ?thesis
    by (simp add: tiTable_SampleT_def) 
qed

lemma Gateway_L5:
  assumes h1:"Gateway req dt a stop lose d ack i vc"
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) a"
      and h4:"msg (Suc 0) stop" 
      and h5:"ts lose"
      and h6:"ack (t + d) = [sending_data]"
      and h7:"\<forall> j \<le> Suc d. a (t+j) = []"
      and h8:"\<forall>k\<le> (d + d). lose (t + k) = [False]" 
  shows "j \<le> d \<longrightarrow> ack (t+d+j) = [sending_data]"
proof - 
  from h1 obtain i1 i2 x y
    where a1:"Sample req dt x stop lose ack i1 vc"
       and a2:"Delay y i1 d x i2"
       and a3:"Loss lose a i2 y i"
    by (simp only: Gateway_def, auto) 
  from a2 and a3 and h3 have sg1:"msg (Suc 0) x"   
    by (simp add: Loss_Delay_msg_a) 
  from a1 and h2 and h4 and sg1 obtain st buffer where a4:
    "tiTable_SampleT req x stop lose 
        (fin_inf_append [init_state] st) (fin_inf_append [[]] buffer) ack
         i1 vc st"
     by (simp add: Sample_def Sample_L_def, auto)
  from assms and a2 and a3 and sg1 and a4 show ?thesis
  proof (induct j)
    case 0 then show ?case by simp
  next
    case (Suc j)
    then show ?case
    proof (cases "Suc j \<le> d")
      assume "\<not> Suc j \<le> d" then show ?thesis by simp
    next
      assume a0:"Suc j \<le> d"
      then have "d + Suc j \<le> d + d"   by arith
      then have sg3:"Suc (d + j) \<le> d + d" by arith
      from a4 and h2 and sg1 and h4 and h5 have sg4: 
       "st (t+d+j) =  hd (ack (t+d+j))"
        by (simp add: tiTable_ack_st_hd)  
      from Suc and a0 and sg4 have sg5:
       "(fin_inf_append [init_state] st) (Suc (t+d+j)) = sending_data"
        by (simp add: correct_fin_inf_append1) 
      from h7 and a0  have sg6:"\<forall>j\<le> d. a (t + Suc j) = []" by auto 
      from sg6 and a3 and a0 and h5 have sg7:"y (t + (Suc j)) = []" 
        by (rule Loss_L5Suc)
      from sg7 and a2 have sg8a:"x (t + d + (Suc j)) = []"
        by (simp add: Delay_def)
      then  have sg8:"x (Suc (t + d + j)) = []" by simp
      have sg9:"Suc (t + d + j) = Suc (t + (d + j))" by arith  
      from a4 have sg10:
        "fin_inf_append [init_state] st (Suc (t + d + j)) = sending_data \<and> 
         x (Suc (t + d + j)) = [] \<and> 
         lose (Suc (t + d + j)) = [False] \<longrightarrow>
         ack (Suc (t + d + j)) = [sending_data]"
        by (simp add: tiTable_SampleT_def)  
      from h8 and sg3 have sg11:"lose (t + Suc (d + j)) = [False]" by blast
      have "Suc (t + d + j) = t + Suc (d + j)"  by arith
      from this and sg11 have "lose (Suc (t + d + j)) = [False]" 
        by  (simp (no_asm_simp), simp) 
     from sg10 and sg5 and sg8a and this show ?thesis by simp
    qed
  qed
qed

lemma Gateway_L6_induction:
 assumes h1:"msg (Suc 0) req"
     and h2:"msg (Suc 0) x" 
     and h3:"msg (Suc 0) stop"
     and h4:"ts lose"
     and h5:"\<forall>j\<le> k. lose (t + j) = [False]" 
     and h6:"\<forall>m \<le> k. req (t + m) \<noteq> [send]"
     and h7:"ack t = [connection_ok]"
     and h8:"Sample req dt x1 stop lose ack i1 vc" 
     and h9:"Delay x2 i1 d x1 i2"
     and h10:"Loss lose x i2 x2 i"
     and h11:"m \<le> k"
 shows "ack (t + m) = [connection_ok]"
using assms
proof (induct m)
  case 0 then show ?case  by simp
next
  case (Suc m)
  then have sg1:"msg (Suc 0) x1" by (simp add:  Loss_Delay_msg_a)
  from Suc and this obtain st buffer where
    a1:"tiTable_SampleT req x1 stop lose (fin_inf_append [init_state] st) 
         (fin_inf_append [[]] buffer) ack i1 vc st"  and 
    a2:"\<forall> t. buffer t = (if dt t = [] then fin_inf_append [[]] buffer t else dt t)"
    by (simp add: Sample_def Sample_L_def, auto)
  from a1 and sg1 and h3 and h4 have sg2:"st (t + m) =  hd (ack (t + m))"  
    by (simp add: tiTable_ack_st_hd)
  from Suc have sg3:"ack (t + m) = [connection_ok]" by simp
  from a1 and sg2 and sg3 have sg4:
  "(fin_inf_append [init_state] st) (Suc (t + m)) = connection_ok"
    by (simp add: fin_inf_append_def)
  from Suc have sg5:"Suc m \<le> k" by simp
  from sg5 and h5 have sg6:"lose (Suc (t + m)) = [False]" by auto
  from h6 and sg5 have sg7:"req (Suc (t + m)) \<noteq> [send]" by auto
  from a1 and sg3 and sg4 and sg5 and sg6 and sg7 show ?case
    by (simp add: tiTable_SampleT_def)
qed

lemma Gateway_L6:
 assumes "Gateway req dt a stop lose d ack i vc"
     and "\<forall>m\<le>k. req (t + m) \<noteq> [send]"
     and "\<forall>j\<le>k. lose (t + j) = [False]"
     and "ack t = [connection_ok]"
     and "msg (Suc 0) req"
     and "msg (Suc 0) stop"
     and "msg (Suc 0) a"
     and "ts lose"
 shows "\<forall>m\<le>k. ack (t + m) = [connection_ok]"
using assms 
by (simp add: Gateway_def, clarify, simp add: Gateway_L6_induction) 

lemma Gateway_L6a:
 assumes "Gateway req dt a stop lose d ack i vc"
     and "\<forall>m\<le>k. req (t + 2 + m) \<noteq> [send]"
     and "\<forall>j\<le>k. lose (t + 2 + j) = [False]"
     and "ack (t + 2) = [connection_ok]"
     and "msg (Suc 0) req"
     and "msg (Suc 0) stop"
     and "msg (Suc 0) a"
     and "ts lose"
 shows "\<forall>m\<le>k. ack (t + 2 + m) = [connection_ok]"
using assms by (rule Gateway_L6)

lemma aux_k3req:
assumes h1:"\<forall>m<k + 3. req (t + m) \<noteq> [send]"
       and h2:"m \<le> k"
shows "req (Suc (Suc (t + m))) \<noteq> [send]"
proof - 
  from h2 have "m + 2 < k + 3" by arith
  from h1 and this have "req (t + (m + 2)) \<noteq> [send]" by blast
  then show ?thesis by simp
qed

lemma aux3lose:
assumes h1:"\<forall>j\<le>k + d + 3. lose (t + j) = [False]"
       and h2:"j \<le> k"
shows "lose (Suc (Suc (t + j))) = [False]"
proof - 
  from h2 have "j + 2 \<le>k + d + 3" by arith
  from h1 and this have "lose (t + (j + 2)) = [False]" by blast
  then show ?thesis by simp
qed


lemma Gateway_L7:
assumes h1:"Gateway req dt a stop lose d ack i vc"
     and h2:"ts lose"
     and h3:"msg (Suc 0) a"
     and h4:"msg (Suc 0) stop" 
     and h5:"msg (Suc 0) req"
     and h6:"req (Suc t) = [init]"
     and h7:"\<forall>m < (k + 3). req (t + m) \<noteq> [send]"
     and h8:"req (t + 3 + k) = [send]"
     and h9:"ack t = [init_state]"
     and h10:"\<forall>j\<le>k + d + 3. lose (t + j) = [False]"
     and h11:"\<forall> t1 \<le> t. req t1 = []"
shows "\<forall> t2 < (t + 3 + k + d). i t2 = []"
proof -
  have "Suc 0 \<le> k + d + 3" by arith
  from h10 and this have "lose (t + Suc 0) = [False]" by blast
  then have sg1:"lose (Suc t) = [False]" by simp
  have "Suc (Suc 0)\<le> k + d + 3" by arith
  from h10 and this have "lose (t + Suc (Suc 0)) = [False]" by blast
  then have sg2:"lose (Suc (Suc t)) = [False]" by simp 
  from h1 and h2 and h3 and h4 and h5 and h6 and h9 and sg1 and sg2 
     have sg3:"ack (t + 2) = [connection_ok]"
    by (simp add: Gateway_L1)
  from h7 and this have sg4:"\<forall>m\<le> k. req ((t + 2) + m) \<noteq> [send]" 
    by (auto, simp add: aux_k3req)  
  from h10 have sg5:"\<forall>j\<le> k. lose ((t + 2) + j) = [False]" 
    by (auto, simp add: aux3lose) 
  from h1 and sg4 and sg5 and sg3 and h5 and h4 and h3 and h2 have sg6:
   "\<forall>m \<le>  k. ack ((t + 2) + m) = [connection_ok]"
    by (rule Gateway_L6a)
  from sg6 have sg7:"ack (t + 2 + k) = [connection_ok]"  by auto
  from h1 obtain i1 i2 x y where
    a1:"Sample req dt x stop lose ack i1 vc" and
    a2:"Delay y i1 d x i2" and 
    a3:"Loss lose a i2 y i"
    by (simp add: Gateway_def, auto) 
  from h3 and a2 and a3  have sg8:"msg (Suc 0) x"
    by (simp add: Loss_Delay_msg_a)  
  from a1 and sg8 and h4 and h5 obtain st buffer where
    a4:"tiTable_SampleT req x stop lose (fin_inf_append [init_state] st) 
         (fin_inf_append [[]] buffer) ack i1 vc st"  and 
    a5:"\<forall> t. buffer t = (if dt t = [] then fin_inf_append [[]] buffer t else dt t)"
    by (simp add: Sample_def Sample_L_def, auto)
  from a4 and h2 and sg8 and h4 and h11 and h6 and h7 and sg6 and h10 
    have sg9:"\<forall> t1 < (t + 3 + k). i1 t1 = []"
    by (simp add: tiTable_i1_4)
  from sg9 and a2 have sg10:"\<forall> t2 < (t + 3 + k + d). i2 t2 = []"
    by (rule Delay_L2) 
  from sg10 and a3 and h2 show ?thesis by (rule Loss_L2)
qed 

lemma Gateway_L8a:
  assumes h1:"Gateway req dt a stop lose d ack i vc" 
      and h2:"msg (Suc 0) req"
      and h3:"msg (Suc 0) stop"
      and h4:"msg (Suc 0) a"
      and h5:"ts lose"
      and h6:"\<forall>j\<le>2 * d. lose (t + j) = [False]" 
      and h7:"ack t = [sending_data]"
      and h8:"\<forall>t3 \<le> t + d. a t3 = []"
      and h9:"x \<le> d + d"
  shows "ack (t + x) = [sending_data]"
proof -
  from h1 obtain i1 i2 x y where
    a1:"Sample req dt x stop lose ack i1 vc" and
    a2:"Delay y i1 d x i2" and 
    a3:"Loss lose a i2 y i"
    by (simp add: Gateway_def, auto) 
  from h8 and a3 and h5 have sg1:"\<forall>t3 \<le> t + d. y t3 = []" by (rule Loss_L6)
  from sg1 and a2 have sg2:"\<forall>t4 \<le> t + d + d. x t4 = []"   by (rule Delay_L4) 
  from h4 and a2 and a3 have sg3:"msg (Suc 0) x" by (simp add:  Loss_Delay_msg_a)
  from h3 and h5 and h2 and sg3 and h6 and h7 and a1 and h9 and sg2 show ?thesis
    by (simp add: Sample_sending_data)
qed


lemma Gateway_L8:
assumes "Gateway req dt a stop lose d ack i vc" 
       and "msg (Suc 0) req"
       and "msg (Suc 0) stop"
       and "msg (Suc 0) a"
       and "ts lose"
       and "\<forall>j\<le>2 * d. lose (t + j) = [False]" 
       and "ack t = [sending_data]"
       and "\<forall>t3 \<le> t + d. a t3 = []"
shows "\<forall>x \<le> d + d. ack (t + x) = [sending_data]"
using assms 
by (simp add: Gateway_L8a)


subsection \<open>Proof of the Refinement Relation for the Gateway Requirements\<close>

lemma Gateway_L0:
 assumes "Gateway req dt a stop lose d ack i vc"
 shows     "GatewayReq req dt a stop lose d ack i vc"
using assms
by (simp add: GatewayReq_def Gateway_L1 Gateway_L2 Gateway_L3 Gateway_L4) 
 

subsection \<open>Lemmas about Gateway Requirements\<close>

lemma GatewayReq_L1:
  assumes h1:"msg (Suc 0) req"
      and h2:"msg (Suc 0) stop"
      and h3:"msg (Suc 0) a"
      and h4:"ts lose"
      and h6:"req (t + 3 + k) = [send]" 
      and h7:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
      and h9:"\<forall>m\<le> k. ack (t + 2 + m) = [connection_ok]"
      and h10:"GatewayReq req dt a stop lose d ack i vc"
 shows "ack (t + 3 + k) = [sending_data]"
proof - 
  from h9 have sg1:"ack (Suc (Suc (t + k))) = [connection_ok]" by auto 
  from h7 have sg2: 
   "\<forall>ka\<le>Suc d. lose (Suc (Suc (t + k + ka))) = [False]"
    by (simp add: aux_lemma_lose_1) 
  from h1 and h2 and h3 and h4 and h6 and h10 and sg1 and sg2 have sg3:
   "ack (t + 2 + k) = [connection_ok] \<and> 
    req (Suc (t + 2 + k)) = [send] \<and> (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
    ack (Suc (t + 2 + k)) = [sending_data]"
    by (simp add: GatewayReq_def)  
  have "t + 3 + k = Suc (Suc (Suc (t + k)))" by arith
  from sg3 and sg1 and h6 and h7 and this show ?thesis 
    by (simp add: eval_nat_numeral)  
qed

lemma GatewayReq_L2:
 assumes  h1:"msg (Suc 0) req"
      and h2:"msg (Suc 0) stop"
      and h3:"msg (Suc 0) a"
      and h4:"ts lose"
      and h5:"GatewayReq req dt a stop lose d ack i vc"
      and h6:"req (t + 3 + k) = [send]"
      and h7:"inf_last_ti dt t \<noteq> []"
      and h8:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
      and h9:"\<forall>m\<le>k. ack (t + 2 + m) = [connection_ok]"
  shows "i (t + 3 + k + d) \<noteq> []"
proof -
  from h8 have sg1:"(\<forall> (x::nat). x \<le> (d+1) \<longrightarrow> lose (t+x) = [False])"
    by (simp add: aux_lemma_lose_2) 
  from h8 have sg2:"\<forall>ka\<le>Suc d. lose (Suc (Suc (t + k + ka))) = [False]"
    by (simp add: aux_lemma_lose_1)
  from h9 have sg3:"ack (t + 2 + k) = [connection_ok]" by simp
  from h1 and h2 and h3 and h4 and h5 and h6 and sg2 and sg3 have sg4:
   "ack (t + 2 + k) = [connection_ok] \<and> 
    req (Suc (t + 2 + k)) = [send] \<and> (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
    i (Suc (t + 2 + k + d)) = inf_last_ti dt (t + 2 + k)"
    by (simp add: GatewayReq_def, auto)  
  from h7 have sg5:"inf_last_ti dt (t + 2 + k) \<noteq> []"
    by (simp add: inf_last_ti_nonempty_k)
  have sg6:"t + 3 + k = Suc (Suc (Suc (t + k)))" by arith
  have "t + 2 + k = Suc (Suc (t + k))" by arith
  from sg1 and sg2 and sg3 and sg4 and sg5 and sg6 and this and h6 show ?thesis
    by (simp add: eval_nat_numeral)
qed


subsection \<open>Properties of the Gateway System\<close>
   
lemma GatewaySystem_L1aux:
assumes "msg (Suc 0) req"
       and "msg (Suc 0) stop"
       and "msg (Suc 0) a"
       and "ts lose"
       and "msg (Suc 0) req \<and> msg (Suc 0) a \<and> msg (Suc 0) stop \<and> ts lose \<longrightarrow> 
        (\<forall>t. (ack t = [init_state] \<and>
          req (Suc t) = [init] \<and> lose (Suc t) = [False] \<and> 
          lose (Suc (Suc t)) = [False] \<longrightarrow>
          ack (Suc (Suc t)) = [connection_ok]) \<and>
         (ack t = [connection_ok] \<and> req (Suc t) = [send] \<and> 
         (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
          i (Suc (t + d)) = inf_last_ti dt t \<and> ack (Suc t) = [sending_data]) \<and>
         (ack (t + d) = [sending_data] \<and> a (Suc t) = [sc_ack] \<and> 
          (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
          vc (Suc (t + d)) = [vc_com]))"
shows  "ack (t + 3 + k + d + d) = [sending_data] \<and>
          a (Suc (t + 3 + k + d)) = [sc_ack] \<and> 
         (\<forall>ka\<le>Suc d. lose (t + 3 + k + d + ka) = [False]) \<longrightarrow>
         vc (Suc (t + 3 + k + d + d)) = [vc_com]"
using assms  by blast

lemma GatewaySystem_L3aux:
assumes "msg (Suc 0) req"
       and "msg (Suc 0) stop"
       and "msg (Suc 0) a"
       and "ts lose"
       and "msg (Suc 0) req \<and> msg (Suc 0) a \<and> msg (Suc 0) stop \<and> ts lose \<longrightarrow> 
        (\<forall>t. (ack t = [init_state] \<and>
          req (Suc t) = [init] \<and> lose (Suc t) = [False] \<and> 
          lose (Suc (Suc t)) = [False] \<longrightarrow>
          ack (Suc (Suc t)) = [connection_ok]) \<and>
         (ack t = [connection_ok] \<and> req (Suc t) = [send] \<and> 
         (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
          i (Suc (t + d)) = inf_last_ti dt t \<and> ack (Suc t) = [sending_data]) \<and>
         (ack (t + d) = [sending_data] \<and> a (Suc t) = [sc_ack] \<and> 
          (\<forall>k\<le>Suc d. lose (t + k) = [False]) \<longrightarrow>
          vc (Suc (t + d)) = [vc_com]))"
shows "ack (t + 2 + k) = [connection_ok] \<and>
         req (Suc (t + 2 + k)) = [send] \<and> 
         (\<forall>j\<le>Suc d. lose (t + 2 + k + j) = [False]) \<longrightarrow>
         i (Suc (t + 2 + k + d)) = inf_last_ti dt (t + 2 + k)"
using assms  by blast

lemma GatewaySystem_L1:
 assumes  h2:"ServiceCenter i a" 
     and h3:"GatewayReq req dt a stop lose d ack i vc" 
     and h4:"msg (Suc 0) req"
     and h5:"msg (Suc 0) stop"
     and h6:"msg (Suc 0) a"
     and h7:"ts lose"
     and h9:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]" 
     and h11:"i (t + 3 + k + d) \<noteq> []"
     and h14:"\<forall>x \<le> d + d. ack (t + 3 + k + x) = [sending_data]"
 shows "vc (2 * d + (t + (4 + k))) = [vc_com]"
proof - 
  from h2 have "\<forall>t. a (Suc t) = (if i t = [] then [] else [sc_ack])"
    by (simp add:ServiceCenter_def) 
  then have sg1:
    "a (Suc (t + 3 + k + d)) = (if i (t + 3 + k + d) = [] then [] else [sc_ack])" 
     by blast
  from sg1 and h11 have sg2:"a (Suc (t + 3 + k + d)) = [sc_ack]" by auto
  from h14 have sg3:"ack (t + 3 + k + 2*d) = [sending_data]" by simp
  from h4 and h5 and h6 and h7 and h3 have sg4:
    "ack (t + 3 + k + d + d) = [sending_data] \<and> a (Suc (t + 3 + k + d)) = [sc_ack] \<and> 
     (\<forall>ka\<le>Suc d. lose (t + 3 + k + d + ka) = [False]) \<longrightarrow>
     vc (Suc (t + 3 + k + d + d)) = [vc_com]" 
    apply (simp only: GatewayReq_def)
    by (rule GatewaySystem_L1aux, auto) 
  from h9 have sg5:"\<forall>ka\<le>Suc d. lose (d + (t + (3 + k)) + ka) = [False]"
    by (simp add: aux_lemma_lose_3)
  have sg5a:"d + (t + (3 + k)) = t + 3 + k + d" by arith
  from sg5 and sg5a have sg5b:"\<forall>ka\<le>Suc d. lose (t + 3 + k + d + ka) = [False]" 
    by auto 
  have sg6:"(t + 3 + k + 2 * d)  = (2 * d + (t + (3 + k)))" by arith
  have sg7:"Suc (Suc (Suc (t + k + (d + d)))) = Suc (Suc (Suc (t + k + d + d)))" 
    by arith
  have "Suc (Suc (Suc (Suc (t + k + d + d)))) = 
            Suc (Suc (Suc (Suc (d + d + (t + k)))))" by arith
  from sg4 and sg3 and sg2 and sg5b and sg6 and sg7 and this show ?thesis
    by (simp add: eval_nat_numeral)
qed

lemma aux4lose1:
assumes h1:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
       and h2:"j \<le> k"
shows "lose (t + (2::nat) + j) = [False]"
proof - 
  from h2 have "(2::nat) + j \<le> (2::nat) * d + (4 + k)" by arith
  from h1 and this have "lose (t + (2 + j)) = [False]" by blast
  then show ?thesis by simp
qed

lemma aux4lose2:
assumes "\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
       and "3 + k + d \<le> 2 * d + (4 + k)"
shows "lose (t + (3::nat) + k + d) = [False]"
proof -
  from assms have "lose (t + ((3::nat) + k + d)) = [False]" by blast
  then show ?thesis by (simp add: arith_sum1)
qed

lemma aux4req:
assumes h1:"\<forall> (m::nat) \<le> k + 2. req (t + m) \<noteq> [send]"
      and h2:"m \<le> k"
      and h3:"req (t + 2 + m) = [send]" shows "False"
proof - 
  from h2 have "(2::nat) + m \<le> k + (2::nat)" by arith
  from h1 and this have "req (t + (2 + m)) \<noteq> [send]" by blast
  from this and h3 show ?thesis by simp
qed
 
lemma GatewaySystem_L2:
 assumes h1:"Gateway req dt a stop lose d ack i vc" 
     and h2:"ServiceCenter i a" 
     and h3:"GatewayReq req dt a stop lose d ack i vc" 
     and h4:"msg (Suc 0) req"
     and h5:"msg (Suc 0) stop"
     and h6:"msg (Suc 0) a"
     and h7:"ts lose"
     and h8:"ack t = [init_state]"
     and h9:"req (Suc t) = [init]" 
     and h10:"\<forall>t1\<le>t. req t1 = []"
     and h11:"\<forall>m \<le> k + 2. req (t + m) \<noteq> [send]"
     and h12:"req (t + 3 + k) = [send]" 
     and h13:"inf_last_ti dt t \<noteq> []"
     and h14:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
 shows "vc (2 * d + (t + (4 + k))) = [vc_com]"
proof -
  have "Suc 0 \<le> 2 * d + (4 + k)" by arith
  from h14 and this have "lose (t + Suc 0) = [False]" by blast
  then have sg1:"lose (Suc t) = [False]" by simp
  have "Suc (Suc 0) \<le> 2 * d + (4 + k)" by arith
  from h14 and this have "lose (t + Suc (Suc 0)) = [False]" by blast
  then have sg2:"lose (Suc (Suc t)) = [False]" by simp 
  from h3 and h4 and h5 and h6 and h7 and h8 and h9 and sg1 and sg2 have sg3:
   "ack (t + 2) = [connection_ok]" 
    by (simp add: GatewayReq_def)
  from h14 have sg4:" \<forall>j\<le>k. lose (t + 2 + j) = [False]" 
    by (clarify, rule aux4lose1, simp) 
  from h11 have sg5:"\<forall>m \<le> k. req (t + 2 + m) \<noteq> [send]" 
    by (clarify, rule aux4req, auto) 
  (* stable connection *)
  from h1 and sg5 and sg4 and sg3 and h4 and h5 and h6 and h7 have sg6:
   "\<forall>m \<le> k. ack (t + 2 + m) = [connection_ok]"
    by (rule Gateway_L6)
  (* sending data*)
  from h3 and h4 and h5 and h6 and h7 and h12 and h14 and sg6 have sg10:
   "ack (t + 3 + k) = [sending_data]"
    by (simp add: GatewayReq_L1)
  from h3 and h4 and h5 and h6 and h7 and h12 and h13 and h14 and sg6 have sg11:
   "i (t + 3 + k + d) \<noteq> []"
    by (simp add: GatewayReq_L2)
  (* waiting for sc-ack *)
  from h11 have sg12:"\<forall>m < k + 3. req (t + m) \<noteq> [send]" by auto
  from h14 have sg13:"\<forall>j\<le>k + d + 3. lose (t + j) = [False]" by auto
  from h1 and h7 and h6 and h5 and h4 and h9 and sg12 
          and h12 and h8 and sg13 and h10
    have sg14:"\<forall> t2 < (t + 3 + k + d). i t2 = []"
    by (simp add: Gateway_L7) 
  from sg14 and h2 have sg15:"\<forall> t3 \<le> (t + 3 + k + d). a t3 = []"
    by (simp add: ServiceCenter_L2)
  from h14 have sg18:"\<forall>j\<le>2 * d. lose ((t + 3 + k) + j) = [False]" 
    by (simp add: streamValue43)
  from h14  have sg16a:"\<forall>j\<le>2 * d. lose (t + j + (4 + k)) = [False]" 
    by (simp add: streamValue2)
  have sg16b:"Suc (3 + k) = (4 + k)" by arith
  from sg16a and sg16b have sg16:"\<forall>j\<le>2 * d. lose (t + j + Suc (3 + k)) = [False]" 
    by (simp (no_asm_simp))  
  from h1 and h4 and h5 and h6 and h7 and sg18 and sg10 and sg15 have sg19:
    "\<forall>x \<le> d + d. ack (t + 3 + k + x) = [sending_data]"
     by (simp add: Gateway_L8)
  from sg19 have sg19a:"ack (t + 3 + k + d + d) = [sending_data]" by auto
  from sg16 have sg20a:"\<forall>j\<le> d. lose (t + 3 + k + d + (Suc j)) = [False]" 
    by (rule streamValue10) 
  have sg20b:"3 + k + d \<le> 2 * d + (4 + k)" by arith
  from h14 and sg20b have sg20c:"lose (t + 3 + k + d) = [False]"
    by (rule aux4lose2)
  from sg20a and sg20c have sg20:"\<forall>j\<le>Suc d. lose (t + 3 + k + d + j) = [False]" 
    by (rule streamValue8) 
  from h4 and h5 and h6 and h7 and h3 have sg21:
     "ack (t + 3 + k + d + d) = [sending_data] \<and> 
      a (Suc (t + 3 + k + d)) = [sc_ack] \<and> 
      (\<forall>j\<le>Suc d. lose (t + 3 + k + d + j) = [False]) \<longrightarrow>
      vc (Suc (t + 3 + k + d + d)) = [vc_com]"
     apply (simp only: GatewayReq_def) 
     by (rule GatewaySystem_L1aux, auto)  
   from h2 and sg11 have sg22:"a (Suc (t + 3 + k + d)) = [sc_ack]"
     by (simp only: ServiceCenter_def, auto)
   from sg21 and sg19a and sg22 and sg20 have sg23:
     "vc (Suc (t + 3 + k + d + d)) = [vc_com]" by simp
   have "2 * d + (t + (4 + k)) = (Suc (t + 3 + k + d + d))" by arith
   from sg23 and this show ?thesis 
     by (simp (no_asm_simp), simp)
qed

lemma GatewaySystem_L3:
 assumes h1:"Gateway req dt a stop lose d ack i vc"
     and h2:"ServiceCenter i a"
     and h3:"GatewayReq req dt a stop lose d ack i vc"
     and h4:"msg (Suc 0) req"
     and h5:"msg (Suc 0) stop"
     and h6:"msg (Suc 0) a"
     and h7:"ts lose"
     and h8: "dt (Suc t) \<noteq> [] \<or> dt (Suc (Suc t)) \<noteq> []"
     and h9: "ack t = [init_state]"
     and h10:"req (Suc t) = [init]"
     and h11:"\<forall>t1\<le>t. req t1 = []"
     and h12:"\<forall>m \<le> k + 2. req (t + m) \<noteq> [send]" 
     and h13:"req (t + 3 + k) = [send]"
     and h14:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
 shows "vc (2 * d + (t + (4 + k))) = [vc_com]"
proof -
  have "Suc 0 \<le> 2 * d + (4 + k)" by arith
  from h14 and this have "lose (t + Suc 0) = [False]" by blast
  then have sg1:"lose (Suc t) = [False]" by simp
  have "Suc (Suc 0) \<le> 2 * d + (4 + k)" by arith
  from h14 and this have "lose (t + Suc (Suc 0)) = [False]" by blast
  then have sg2:"lose (Suc (Suc t)) = [False]" by simp 
  from h3 and h4 and h5 and h6 and h7 and h10 and h9 and sg1 and sg2 have sg3:
   "ack (t + 2) = [connection_ok]" 
    by (simp add: GatewayReq_def)
  from h14 have sg4:" \<forall>j\<le>k. lose (t + 2 + j) = [False]" 
    by (clarify, rule aux4lose1, simp) 
  from h12 have sg5:"\<forall>m \<le> k. req (t + 2 + m) \<noteq> [send]" 
    by (clarify, rule aux4req, auto)  
  (* stable connection *)
  from h1 and sg5 and sg4 and sg3 and h4 and h5 and h6 and h7 have sg6:
   "\<forall>m \<le> k. ack (t + 2 + m) = [connection_ok]"
    by (rule Gateway_L6)
  from sg6 have sg6a:"ack (t + 2 + k) = [connection_ok]" by simp
  (* sending data*)
  from h3 and h4 and h5 and h6 and h7 and h13 and h14 and sg6 have sg10:
   "ack (t + 3 + k) = [sending_data]"
    by (simp add: GatewayReq_L1)
  from h3 and h4 and h5 and h6 and h7 have sg11a:
   "ack (t + 2 + k) = [connection_ok] \<and>
    req (Suc (t + 2 + k)) = [send] \<and> 
    (\<forall>j\<le>Suc d. lose ((t + 2 + k) + j) = [False]) \<longrightarrow>
    i (Suc (t + (2::nat) + k + d)) = inf_last_ti dt (t + 2 + k)"
    apply (simp only: GatewayReq_def)
    by (rule GatewaySystem_L3aux, auto) 
  have sg12:"Suc (t + 2 + k) = t + 3 + k" by arith
  from h13 and sg12 have sg12a:"req (Suc (t + 2 + k)) = [send]" 
    by (simp add: eval_nat_numeral)
  from h14 have sg13:"\<forall>j\<le>Suc d. lose ((t + 2 + k) + j) = [False]"
    by (rule streamValue12) 
  from sg11a and sg6a and h13 and sg12a and sg13 have sg14:
    "i (Suc (t + (2::nat) + k + d)) = inf_last_ti dt (t + 2 + k)" by simp
  from h8 have sg15:"inf_last_ti dt (t + 2 + k) \<noteq> []" 
    by (rule inf_last_ti_Suc2) 
  from sg14 and sg15 have sg16: "i (t + 3 + k + d) \<noteq> []"
    by (simp add: arith_sum4)
  (* waiting for sc-ack *)
  from h14 have sg17:"\<forall>j\<le>k + d + 3. lose (t + j) = [False]" by auto
  from h12 have sg18:"\<forall>m < (k + 3). req (t + m) \<noteq> [send]"   by auto
  from h1 and h4 and h5 and h6 and h7 and h10 and sg18 and h13 and h9 and sg17 and h11 
    have sg19:"\<forall> t2 < (t + 3 + k + d). i t2 = []"
    by (simp add: Gateway_L7) 
  from h2 and sg19 have sg20:"\<forall> t3 \<le> (t + 3 + k + d). a t3 = []"
    by (simp add: ServiceCenter_L2)
  from h14 have sg21:"\<forall>j\<le>2 * d. lose (t + 3 + k + j) = [False]"
    by (simp add: streamValue43)
  from h1 and h4 and h5 and h6 and h7 and sg21 and sg10 and sg20 have 
    "\<forall>x \<le> d + d. ack (t + 3 + k + x) = [sending_data]"
    by (simp add: Gateway_L8)
  from h2 and h3 and h4 and h5 and h6 and h7 and h14 and sg16 and this show ?thesis
    by (simp add: GatewaySystem_L1)
qed


subsection \<open>Proof of the Refinement for the Gateway System\<close> 

lemma GatewaySystem_L0:
 assumes "GatewaySystem req dt stop lose d ack vc"
 shows    "GatewaySystemReq req dt stop lose d ack vc"
proof - 
  from assms obtain x i where
    a1:"Gateway req dt x stop lose d ack i vc" and 
    a2:"ServiceCenter i x"
    by (simp add: GatewaySystem_def, auto)
  from a1 have sg1:"GatewayReq req dt x stop lose d ack i vc"
    by (simp add: Gateway_L0)
  from a2 have sg2:"msg (Suc 0) x"
    by (simp add: ServiceCenter_a_msg)
  from assms and a1 and a2 and sg1 and sg2 show ?thesis
    apply (simp add: GatewaySystemReq_def, auto)
    apply (simp add: GatewaySystem_L3)
    apply (simp add: GatewaySystem_L3)
    apply (simp add: GatewaySystem_L3)
    by (simp add: GatewaySystem_L2)
qed

end
