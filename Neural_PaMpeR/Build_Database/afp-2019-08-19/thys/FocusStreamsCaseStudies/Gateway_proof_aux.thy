(*<*)
(*
   Title:  Gateway_proof_aux.thy  (Gateway: Verification, aux. lemmas)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
section \<open>Gateway: Verification\<close>

theory Gateway_proof_aux 
imports Gateway BitBoolTS
begin

subsection \<open>Properties of the defined data types\<close>


lemma aType_empty: 
  assumes h1:"msg (Suc 0) a"
         and h2: "a t \<noteq> [sc_ack]"
  shows       "a t = []"
proof (cases "a t")
  assume a1:"a t = []"
  from this show ?thesis by simp
next
  fix aa l
  assume a2:"a t = aa # l"
  show ?thesis
    proof (cases "aa") 
      assume a3:"aa = sc_ack"
      from h1 have sg1:"length (a t) \<le> Suc 0" by (simp add: msg_def)
      from this and assms and a2 and a3 show ?thesis by auto 
    qed
qed

lemma aType_nonempty: 
  assumes h1:"msg (Suc 0) a"
      and h2: "a t \<noteq> []"
  shows       "a t = [sc_ack]"
proof (cases "a t")
  assume a1:"a t = []"
  from this and h2 show ?thesis by simp
next
  fix aa l
  assume a2:"a t = aa # l"
  from a2 and h1 have sg1: "l = []" by (simp add: msg_nonempty1)
  from a2 and h1 and sg1 show ?thesis
    proof (cases "aa") 
      assume a3:"aa = sc_ack" 
      from this and sg1 and h2 and a2 show ?thesis  by simp
    qed
qed

lemma aType_lemma: 
  assumes "msg (Suc 0) a" 
  shows    "a t = [] \<or> a t = [sc_ack]"
using assms
by (metis aType_nonempty)

lemma stopType_empty: 
  assumes "msg (Suc 0) a"
         and "a t \<noteq> [stop_vc]"
  shows "a t = []"
using assms
by (metis (full_types) list_length_hint2 msg_nonempty2 stopType.exhaust)

lemma stopType_nonempty: 
  assumes "msg (Suc 0) a"
         and "a t \<noteq> []"
  shows "a t = [stop_vc]"
using assms
by (metis stopType_empty)

lemma stopType_lemma: 
  assumes "msg (Suc 0) a" 
  shows    "a t = [] \<or> a t = [stop_vc]"
using assms
by (metis stopType_nonempty)

lemma vcType_empty: 
  assumes "msg (Suc 0) a"
         and "a t \<noteq> [vc_com]"
  shows"a t = []"
using assms
by (metis (full_types) list_length_hint2 msg_nonempty2 vcType.exhaust)

lemma vcType_lemma: 
  assumes "msg (Suc 0) a" 
  shows    "a t = [] \<or> a t = [vc_com]"
using assms
by (metis vcType_empty)


subsection \<open>Properties of the Delay component\<close>

lemma Delay_L1:
 assumes h1:"\<forall>t1 < t. i1 t1 = []"
         and h2:"Delay y i1 d x i2"
         and h3:"t2 < t + d"
   shows "i2 t2 = []"
proof (cases "t2 < d")
  assume a1:"t2 < d"
  from h2 have sg1:"t2 < d \<longrightarrow> i2 t2 = []"
    by (simp add: Delay_def)
  from sg1 and a1 show ?thesis by simp
next
  assume a2:"\<not> t2 < d"
  from h2 have sg2:"d \<le> t2 \<longrightarrow> i2 t2 = i1 (t2 - d)"
    by (simp add: Delay_def)
  from a2 and sg2 have "i2 t2 = i1 (t2 - d)" by simp
  from h1 and a2 and h3 and this show ?thesis by auto
qed

lemma Delay_L2:
 assumes "\<forall>t1 < t. i1 t1 = []"
        and "Delay y i1 d x i2"
   shows "\<forall>t2 < t + d. i2 t2 = []"
using assms by (clarify, rule Delay_L1, auto)

lemma Delay_L3:
 assumes h1:"\<forall>t1 \<le> t. y t1 = []"
        and h2:"Delay y i1 d x i2"
        and h3:"t2 \<le> t + d"
   shows "x t2 = []"
proof (cases "t2 < d")
  assume a1:"t2 < d"
  from h2 have sg1:"t2 < d \<longrightarrow> x t2 = []"
    by (simp add: Delay_def)
  from sg1 and a1 show ?thesis by simp
next
  assume a2:"\<not> t2 < d"
  from h2 have sg2:"d \<le> t2 \<longrightarrow> x t2 = y (t2 - d)"
    by (simp add: Delay_def)
  from a2 and sg2 have sg3:"x t2 = y (t2 - d)" by simp
  from h1 and a2 and h3 and sg3 show ?thesis by auto
qed

lemma Delay_L4:
 assumes "\<forall>t1 \<le> t. y t1 = []"
     and "Delay y i1 d x i2"
   shows "\<forall>t2 \<le> t + d. x t2 = []"
using assms by (clarify, rule Delay_L3, auto)

lemma Delay_lengthOut1:
  assumes h1:"\<forall>t. length (x t) \<le> Suc 0"
         and h2:"Delay x i1 d y i2"
  shows "length (y t) \<le> Suc 0"
proof (cases "t < d")
  assume a1:"t < d"
  from h2 have sg1:"t < d \<longrightarrow> y t = []"
    by (simp add: Delay_def)
  from a1 and sg1 show ?thesis by auto
next
  assume a2:"\<not> t < d"
  from h2 have sg2:"t \<ge> d \<longrightarrow> (y t = x (t-d))"
    by (simp add: Delay_def)
  from a2 and sg2 and h1 show ?thesis by auto 
qed 

lemma Delay_msg1:
  assumes "msg (Suc 0) x"
         and "Delay x i1 d y i2" 
  shows      "msg (Suc 0) y"
using assms
by (simp add: msg_def Delay_lengthOut1)


subsection \<open>Properties of the Loss component\<close>

lemma Loss_L1:
 assumes "\<forall>t2<t. i2 t2 = []"
        and "Loss lose a i2 y i"
        and "t2 < t"
        and "ts lose"
 shows "i t2 = []"
using assms
by (metis Loss_def)

lemma Loss_L2:
 assumes "\<forall>t2<t. i2 t2 = []"
        and "Loss lose a i2 y i"
        and "ts lose"
 shows  "\<forall>t2<t. i t2 = []"
using assms
by (metis Loss_def)

lemma Loss_L3:
 assumes "\<forall>t2<t. a t2 = []"
        and "Loss lose a i2 y i"
        and "t2 < t"
        and "ts lose"
 shows "y t2 = []"
using assms
by (metis Loss_def)

lemma Loss_L4:
 assumes "\<forall>t2<t. a t2 = []"
        and "Loss lose a i2 y i"
        and "ts lose"
 shows  "\<forall>t2<t. y t2 = []"
using assms
by (metis Loss_def)

lemma Loss_L5:
 assumes "\<forall>t1 \<le> t. a t1 = []"
        and "Loss lose a i2 y i"
        and "t2 \<le> t"
        and "ts lose"
 shows "y t2 = []"
using assms
by (metis Loss_def)

lemma Loss_L5Suc:
 assumes "\<forall>j \<le> d. a (t + Suc j) = []"
        and "Loss lose a i2 y i"
        and "Suc j \<le> d"
        and tsLose:"ts lose"
 shows "y (t + Suc j) = []"
using assms
proof (cases "lose (t + Suc j) = [False]")
  assume "lose (t + Suc j) = [False]"
  from assms and this show ?thesis by (simp add: Loss_def)
next
  assume "lose (t + Suc j) \<noteq> [False]"
  from this and tsLose have "lose (t + Suc j) = [True]" 
    by (simp add: ts_bool_True)
  from assms and this show ?thesis by (simp add: Loss_def)
qed

lemma Loss_L6:
 assumes "\<forall>t2 \<le> t. a t2 = []"
        and "Loss lose a i2 y i"
        and "ts lose"
 shows  "\<forall>t2 \<le> t. y t2 = []"
using assms
by (metis Loss_L5)

lemma Loss_lengthOut1:
  assumes h1:"\<forall>t. length (a t) \<le> Suc 0"
         and h2:"Loss lose a i2 x i"
  shows "length (x t) \<le> Suc 0"
proof (cases "lose t =  [False]")
  assume "lose t =  [False]"
  from this and h2 have sg1:"x t = a t" by (simp add: Loss_def)
  from h1 have sg2:"length (a t) \<le> Suc 0" by auto
  from sg1 and sg2 show ?thesis by simp
next
  assume "lose t \<noteq> [False]"
  from this and h2 have "x t = []" by (simp add: Loss_def)
  from this show ?thesis by simp
qed

lemma Loss_lengthOut2:
  assumes "\<forall>t. length (a t) \<le> Suc 0"
         and "Loss lose a i2 x i"
  shows "\<forall>t. length (x t) \<le> Suc 0"
using assms
by (simp add: Loss_lengthOut1)

lemma Loss_msg1:
  assumes "msg (Suc 0) a" 
         and "Loss lose a i2 x i"
  shows      "msg (Suc 0) x"
using assms
by (simp add: msg_def Loss_def Loss_lengthOut1)


subsection \<open>Properties of the composition of Delay and Loss components\<close>

lemma Loss_Delay_length_y:
  assumes "\<forall>t. length (a t) \<le> Suc 0"
         and "Delay x i1 d y i2"
         and "Loss lose a i2 x i"
  shows "length (y t) \<le> Suc 0"
using assms
by (metis Delay_msg1 Loss_msg1 msg_def)

lemma Loss_Delay_msg_a:
  assumes "msg (Suc 0) a"
         and "Delay x i1 d y i2"
         and "Loss lose a i2 x i"
  shows  "msg (Suc 0) y"
using assms
by (simp add: msg_def Loss_Delay_length_y)


subsection \<open>Auxiliary Lemmas\<close>

lemma inf_last_ti2:
  assumes "inf_last_ti dt (Suc (Suc t)) \<noteq> []"
  shows    "inf_last_ti dt (Suc (Suc (t + k))) \<noteq> []"
using assms
by (metis add_Suc inf_last_ti_nonempty_k)
  
lemma aux_ack_t2:
  assumes h1:"\<forall>m\<le>k. ack (Suc (Suc (t + m))) = [connection_ok]"
         and h2:"Suc (Suc t) < t2"
         and h3:"t2 < t + 3 + k"
  shows "ack t2 = [connection_ok]"
proof -
  from h3 have sg1:"t2 - Suc (Suc t) \<le> k" by arith
  from h1 and sg1 
    obtain m where a1:"m = t2 - Suc (Suc t)" 
                  and a2:"ack (Suc (Suc (t + m))) = [connection_ok]" 
    by auto 
  from h2 have sg2:"(Suc (Suc (t2 - 2))) =  t2" by arith
  from h2 have sg3:"Suc (Suc (t + (t2 - Suc (Suc t)))) =  t2" by arith
  from sg1 and a1 and a2 and sg2 and sg3 show ?thesis by simp
qed

lemma aux_lemma_lose_1:
  assumes h1:"\<forall>j\<le>((2::nat) * d + ((4::nat) + k)). (lose (t + j) = x)"
         and h2:"ka\<le>Suc d"
  shows "lose (Suc (Suc (t + k + ka))) = x"
proof -
  from h2 have sg1:"k + (2::nat) + ka \<le> (2::nat) * d + ((4::nat) + k)" by auto
  from h2 and sg1 have sg2:"Suc (Suc (k + ka)) \<le>2 * d + (4 + k)" by auto
  from sg1 and sg2 and h1 and h2  obtain j where a1:"j = k + (2::nat) + ka"
                                     and a2:"lose (t + j) = x"
    by blast
  have sg3:"Suc (Suc (t + (k + ka))) = Suc (Suc (t + k + ka))" by arith
  from a1 and a2 and sg3 show ?thesis  by simp
qed

lemma aux_lemma_lose_2:
  assumes "\<forall>j\<le>(2::nat) * d + ((4::nat) + k). lose (t + j) = [False]"
  shows    "\<forall>x\<le>d + (1::nat). lose (t + x) = [False]"
using assms by auto

lemma aux_lemma_lose_3a:
  assumes h1:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]" 
         and h2:"ka \<le> Suc d"
  shows "lose (d + (t + (3 + k)) + ka) = [False]"
proof - 
  from h2 have sg1:"(d + 3 + k + ka) \<le>2 * d + (4 + k)"
    by arith
  from h1 and h2 and sg1  obtain j where a1:"j = (d + 3 + k + ka)" and 
                                         a2:"lose (t + j) = [False]" 
    by simp
  from h2 and sg1 have sg2:"(t + (d + 3 + k + ka)) = (d + (t + (3 + k)) + ka)" 
    by arith
  from h1 and h2 and a1 and a2 and sg2 show ?thesis
    by simp 
qed

lemma aux_lemma_lose_3:
  assumes "\<forall>j\<le>2 * d + (4 + k). lose (t + j) = [False]"
  shows    "\<forall>ka\<le>Suc d. lose (d + (t + (3 + k)) + ka) = [False]"
using assms
by (auto, simp add: aux_lemma_lose_3a)

lemma aux_arith1_Gateway7:
  assumes "t2 - t \<le> (2::nat) * d + (t + ((4::nat) + k))"
         and "t2 < t + (3::nat) + k + d"
         and "\<not> t2 - d < (0::nat)"
  shows "t2 - d < t + (3::nat) + k"
using assms  by arith

lemma ts_lose_ack_st1ts:
  assumes "ts lose" 
         and "lose t = [True]  \<longrightarrow>  ack t = [x]  \<and> st_out t = x"
         and "lose t = [False] \<longrightarrow>  ack t = [y]  \<and> st_out t = y"
  shows "ack t = [st_out t]"
using assms
by (metis ts_bool_False)

lemma ts_lose_ack_st1:
  assumes h1:"lose t = [True] \<or> lose t = [False]" 
  and h2:"lose t = [True]  \<longrightarrow>  ack t = [x]  \<and> st_out t = x"
  and h3:"lose t = [False] \<longrightarrow>  ack t = [y]  \<and> st_out t = y"
  shows "ack t = [st_out t]"
proof (cases "lose t = [False]")
  assume "lose t = [False]"
  from this and h3 show ?thesis by simp
next 
  assume a2:"lose t \<noteq> [False]"
  from this and h1 have "lose t = [True]" by (simp add: ts_bool_True)
  from this and a2 and h2 show ?thesis by simp
qed

lemma ts_lose_ack_st2ts:
  assumes "ts lose" 
         and "lose t = [True] \<longrightarrow> 
                 ack t = [x]  \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = x"
        and "lose t = [False] \<longrightarrow> 
               ack t = [y] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = y"
  shows "ack t = [st_out t]"
using assms
by (metis ts_bool_True_False)

lemma ts_lose_ack_st2:
  assumes h1:"lose t = [True] \<or> lose t = [False]" 
         and h2:"lose t = [True] \<longrightarrow> 
                ack t = [x]  \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = x"
         and h3:"lose t = [False] \<longrightarrow> 
                ack t = [y] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = y"
  shows "ack t = [st_out t]"
proof (cases "lose t = [False]")
  assume "lose t = [False]"
  from this and h3 show ?thesis by simp
next 
  assume a2:"lose t \<noteq> [False]"
  from this and h1 have "lose t = [True]" by (simp add: ts_bool_True)
  from this and a2 and h2 show ?thesis by simp
qed

lemma ts_lose_ack_st2vc_com:
assumes h1:"lose t = [True] \<or> lose t = [False]" 
       and h2:"lose t = [True] \<longrightarrow> 
             ack t = [x]  \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = x"
       and h3:"lose t = [False] \<longrightarrow> 
             ack t = [y] \<and> i1 t = [] \<and> vc t = [vc_com] \<and> st_out t = y"
shows "ack t = [st_out t]"
proof (cases "lose t = [False]")
  assume "lose t = [False]"
  from this and h3 show ?thesis by simp
next 
  assume a2:"lose t \<noteq> [False]"
  from this and h1 have ag1:"lose t = [True]" by (simp add: ts_bool_True)
  from this and a2 and h2 show ?thesis by simp
qed

lemma ts_lose_ack_st2send:
  assumes h1:"lose t = [True] \<or> lose t = [False]" 
  and h2:"lose t = [True] \<longrightarrow> 
      ack t = [x]  \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = x"
  and h3:"lose t = [False] \<longrightarrow> 
      ack t = [y] \<and> i1 t = b t \<and> vc t = [] \<and> st_out t = y"
  shows "ack t = [st_out t]"
proof (cases "lose t = [False]")
  assume "lose t = [False]"
  from this and h3 show ?thesis by simp
next 
  assume a2:"lose t \<noteq> [False]"
  from this and h1 have "lose t = [True]" by (simp add: ts_bool_True)
  from this and a2 and h2 show ?thesis by simp
qed

lemma tiTable_ack_st_splitten:
  assumes h1:"ts lose"
      and h2:"msg (Suc 0) a1"
      and h3:"msg (Suc 0) stop"
      and h4:"st_in t = init_state \<and> req t = [init] \<longrightarrow> 
          ack t = [call] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = call"
      and h5:"st_in t = init_state \<and> req t \<noteq> [init] \<longrightarrow>
          ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
      and h6:"(st_in t = call \<or> st_in t = connection_ok \<and> req t \<noteq> [send]) \<and> lose t = [False] \<longrightarrow>
          ack t = [connection_ok] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = connection_ok"
      and h7:"(st_in t = call \<or> st_in t = connection_ok \<or> st_in t = sending_data) \<and> lose t = [True] \<longrightarrow>
          ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
      and h8:"st_in t = connection_ok \<and> req t = [send] \<and> lose t = [False] \<longrightarrow>
          ack t = [sending_data] \<and> i1 t = b t \<and> vc t = [] \<and> st_out t = sending_data"
      and h9:"st_in t = sending_data \<and> a1 t = [] \<and> lose t = [False] \<longrightarrow>
          ack t = [sending_data] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = sending_data"
      and h10:"st_in t = sending_data \<and> a1 t = [sc_ack] \<and> lose t = [False] \<longrightarrow>
          ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] \<and> st_out t = voice_com"
      and h11:"st_in t = voice_com \<and> stop t = [] \<and> lose t = [False] \<longrightarrow>
          ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] \<and> st_out t = voice_com"
      and h12:"st_in t = voice_com \<and> stop t = [] \<and> lose t = [True] \<longrightarrow>
          ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = voice_com"
      and h13:"st_in t = voice_com \<and> stop t = [stop_vc] \<longrightarrow>
          ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
  shows "ack t = [st_out t]"
proof - 
  from h1 and h6 and h7 have sg1:"lose t = [True] \<or> lose t = [False]"
    by (simp add: ts_bool_True_False)
show ?thesis 
proof (cases "st_in t")
  assume a1:"st_in t = init_state"
  from a1 and h4 and h5 show ?thesis 
  proof (cases "req t = [init]")
    assume a11:"req t = [init]"
    from a11 and a1 and h4 and h5 show ?thesis by simp
  next
    assume a12:"req t \<noteq> [init]"
    from a12 and a1 and h4 and h5 show ?thesis by simp
  qed
next
  assume a2:"st_in t = call"
  from a2 and sg1 and h6 and h7 show ?thesis 
     apply simp
     by (rule ts_lose_ack_st2, assumption+)
next
  assume a3:"st_in t = connection_ok"
  from a3 and h6 and h7 and h8 show ?thesis apply simp
  proof (cases "req t = [send]")
    assume a31:"req t = [send]"
    from this and a3 and h6 and h7 and h8 and sg1 show ?thesis 
      apply simp
      by (rule ts_lose_ack_st2send, assumption+) 
  next
    assume a32:"req t \<noteq> [send]"
    from this and a3 and h6 and h7 and h8 and sg1 show ?thesis 
      apply simp
      by (rule ts_lose_ack_st2, assumption+) 
  qed
next
  assume a4:"st_in t = sending_data" 
  from sg1 and a4 and h7 and h9 and h10  show ?thesis apply simp 
  proof (cases "a1 t = []")
    assume a41:"a1 t = []"
    from this and a4 and sg1 and h7 and h9 and h10 show ?thesis
      apply simp
      by (rule ts_lose_ack_st2, assumption+) 
  next
    assume a42:"a1 t \<noteq> []"
    from this and h2  have "a1 t = [sc_ack]"  by (simp add: aType_nonempty)
    from this and a4 and a42 and sg1 and h7 and h9 and h10 show ?thesis
      apply simp
      by (rule ts_lose_ack_st2vc_com, assumption+)
  qed  
next
  assume a5:"st_in t = voice_com"
  from a5 and h11 and h12 and h13 show ?thesis 
  apply simp
  proof (cases "stop t = []")
    assume a51:"stop t = []"
    from this and a5 and h11 and h12 and h13 and sg1 show ?thesis
      apply simp
      by (rule ts_lose_ack_st2vc_com, assumption+)
  next
    assume a52:"stop t \<noteq> []"
    from this and h3 have sg7:"stop t = [stop_vc]"  
      by (simp add: stopType_nonempty)
    from this and a5 and a52 and h13 show ?thesis by simp
  qed
qed
qed

lemma tiTable_ack_st:
assumes "tiTable_SampleT req a1 stop lose st_in b ack i1 vc st_out"
       and tsLose:"ts lose"
       and a1Msg1:"msg (Suc 0) a1"      
       and stopMsg1:"msg (Suc 0) stop"
  shows      "ack t = [st_out t] "
proof -
  from assms have sg1:
   "st_in t = init_state \<and> req t = [init] \<longrightarrow>
    ack t = [call] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = call"
     by (simp add: tiTable_SampleT_def)
  from assms have sg2:
   "st_in t = init_state \<and> req t \<noteq> [init] \<longrightarrow>
    ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
     by (simp add: tiTable_SampleT_def)
  from assms have sg3:
   "(st_in t = call \<or> st_in t = connection_ok \<and> req t \<noteq> [send]) \<and> 
     lose t = [False] \<longrightarrow>
     ack t = [connection_ok] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = connection_ok"
     by (simp add: tiTable_SampleT_def)
  from assms have sg4:
   "(st_in t = call \<or> st_in t = connection_ok \<or> st_in t = sending_data) \<and> 
     lose t = [True] \<longrightarrow>
     ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
     by (simp add: tiTable_SampleT_def)
  from assms have sg5:
   "st_in t = connection_ok \<and> req t = [send] \<and> lose t = [False] \<longrightarrow>
    ack t = [sending_data] \<and> i1 t = b t \<and> vc t = [] \<and> st_out t = sending_data"
    by (simp add: tiTable_SampleT_def)
  from assms have sg6:
   "st_in t = sending_data \<and> a1 t = [] \<and> lose t = [False] \<longrightarrow>
    ack t = [sending_data] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = sending_data"
     by (simp add: tiTable_SampleT_def)
  from assms have sg7:
   "st_in t = sending_data \<and> a1 t = [sc_ack] \<and> lose t = [False] \<longrightarrow>
    ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] \<and> st_out t = voice_com"
    by (simp add: tiTable_SampleT_def)
  from assms have sg8:
   "st_in t = voice_com \<and> stop t = [] \<and> lose t = [False] \<longrightarrow>
    ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] \<and> st_out t = voice_com"
    by (simp add: tiTable_SampleT_def)
  from assms have sg9:
   "st_in t = voice_com \<and> stop t = [] \<and> lose t = [True] \<longrightarrow>
    ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = voice_com"
    by (simp add: tiTable_SampleT_def)
  from assms have sg10:
   "st_in t = voice_com \<and> stop t = [stop_vc] \<longrightarrow>
    ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
    by (simp add: tiTable_SampleT_def)
  from tsLose and a1Msg1 and stopMsg1 and sg1 and sg2 and sg3 and sg4 and sg5 and 
  sg6 and sg7 and sg8 and sg9 and sg10 show ?thesis 
    by (rule tiTable_ack_st_splitten)
qed

lemma tiTable_ack_st_hd:
assumes "tiTable_SampleT req a1 stop lose st_in b ack i1 vc st_out"
       and "ts lose"
       and "msg (Suc 0) a1"
       and "msg (Suc 0) stop"
shows "st_out t =  hd (ack t)"
using assms by (simp add:  tiTable_ack_st)

lemma tiTable_ack_connection_ok:
  assumes tbl:"tiTable_SampleT req x stop lose st_in b ack i1 vc st_out"
      and ackCon:"ack t = [connection_ok]"
      and xMsg1:"msg (Suc 0) x"
      and tsLose:"ts lose"
      and stopMsg1:"msg (Suc 0) stop"
  shows "(st_in t = call \<or> st_in t = connection_ok \<and> req t \<noteq> [send]) \<and> 
         lose t = [False]"
proof - 
  from tbl and tsLose have sg1:"lose t = [True] \<or> lose t = [False]"
    by (simp add: ts_bool_True_False)
  from tbl and xMsg1 have sg2:"x t = [] \<or> x t = [sc_ack]"
    by (simp add: aType_lemma) 
  from tbl and stopMsg1 have sg3:"stop t = [] \<or> stop t = [stop_vc]"
    by (simp add: stopType_lemma) 
  show ?thesis
  proof (cases "st_in t")
    assume a1:"st_in t = init_state"
    show ?thesis
    proof (cases "req t = [init]")
      assume a11:"req t = [init]"
      from tbl and a1 and a11 and ackCon show ?thesis by (simp add: tiTable_SampleT_def)
    next
      assume a12:"req t \<noteq> [init]"
      from tbl and a1 and a12 and ackCon show ?thesis by (simp add: tiTable_SampleT_def)
    qed 
  next
    assume a2:"st_in t = call"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a21:"lose t = [True]"
      from tbl and a2 and a21 and ackCon show ?thesis by (simp add: tiTable_SampleT_def)
    next
      assume a22:"lose t \<noteq> [True]"
      from this and tsLose have a22a:"lose t = [False]" by (simp add: ts_bool_False)
      from tbl have 
       "(st_in t = call \<or> st_in t = connection_ok \<and> req t \<noteq> [send]) \<and> 
         lose t = [False] \<longrightarrow>
         ack t = [connection_ok] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = connection_ok"
         by (simp add: tiTable_SampleT_def)
      from this and a2 and a22a and ackCon show ?thesis by simp
    qed 
  next
    assume a3:"st_in t = connection_ok"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a31:"lose t = [True]"
      from tbl have 
       "(st_in t = call \<or> st_in t = connection_ok \<or> st_in t = sending_data) \<and> 
         lose t = [True] \<longrightarrow>
         ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] \<and> st_out t = init_state"
        by (simp add: tiTable_SampleT_def)
      from this and a3 and a31 and ackCon show ?thesis by simp
    next
      assume a32:"lose t \<noteq> [True]"
      from this and tsLose have a32a:"lose t = [False]" by (simp add: ts_bool_False)
      show ?thesis
      proof (cases "req t = [send]")
        assume a321:"req t = [send]"
        from tbl and a3 and a32a and a321 and ackCon show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a322:"req t \<noteq> [send]"
        from tbl and a3 and a32a and a322 and ackCon show ?thesis
           by (simp add: tiTable_SampleT_def)
      qed
    qed 
  next
    assume a4:"st_in t = sending_data"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a41:"lose t = [True]"
      from tbl and a4 and a41 and ackCon show ?thesis 
         by (simp add: tiTable_SampleT_def)
    next
      assume a42:"lose t \<noteq> [True]"
      from this and tsLose have a42a:"lose t = [False]" by (simp add: ts_bool_False)
      show ?thesis
      proof (cases "x t = [sc_ack]")
        assume a421:"x t = [sc_ack]"
        from tbl and a4 and a42a and a421 and ackCon show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a422:" x t \<noteq> [sc_ack]"
        from this and xMsg1 have a422a:"x t = []" by (simp add: aType_empty)
        from tbl and a4 and a42a and a422a and ackCon show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  next  
    assume a5:"st_in t = voice_com"
    show ?thesis
    proof (cases "stop t = [stop_vc]")
      assume a51:"stop t = [stop_vc]"
      from tbl and a5 and a51 and ackCon show ?thesis 
         by (simp add: tiTable_SampleT_def)
    next
      assume a52:"stop t \<noteq> [stop_vc]"
      from this and stopMsg1 have a52a:"stop t = []" by (simp add: stopType_empty)
      show ?thesis
      proof (cases "lose t = [True]")
        assume a521:"lose t = [True]"
        from tbl and a5 and a52a and a521 and ackCon show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a522:"lose t \<noteq> [True]"
        from this and tsLose have a522a:"lose t = [False]" by (simp add: ts_bool_False)
        from tbl and a5 and a52a and a522a and ackCon show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  qed
qed
     
lemma tiTable_i1_1:
assumes tbl:"tiTable_SampleT req x stop lose st_in b ack i1 vc st_out"
       and "ts lose"
       and "msg (Suc 0) x"
       and "msg (Suc 0) stop"
       and "ack t = [connection_ok]"
shows "i1 t = []"
proof -
  from assms have 
   "(st_in t = call \<or> st_in t = connection_ok \<and> req t \<noteq> [send]) \<and> 
    lose t = [False]"
    by (simp add: tiTable_ack_connection_ok)
  from this and tbl show ?thesis by (simp add: tiTable_SampleT_def)
qed

lemma tiTable_ack_call:
assumes tbl:"tiTable_SampleT req x stop lose st_in b ack i1 vc st_out"
      and ackCall:"ack t = [call]"
      and xMsg1:"msg (Suc 0) x"
      and tsLose:"ts lose"
      and stopMsg1:"msg (Suc 0) stop"
shows "st_in t = init_state \<and> req t = [init]"
proof - 
  from tbl and tsLose have sg1:"lose t = [True] \<or> lose t = [False]"
    by (simp add: ts_bool_True_False)
  from tbl and xMsg1 have sg2:"x t = [] \<or> x t = [sc_ack]"
    by (simp add: aType_lemma) 
  from tbl and stopMsg1 have sg3:"stop t = [] \<or> stop t = [stop_vc]"
    by (simp add: stopType_lemma) 
  show ?thesis
  proof (cases "st_in t")
    assume a1:"st_in t = init_state"
    show ?thesis
    proof (cases "req t = [init]")
      assume a11:"req t = [init]"
      from tbl and a1 and a11 and ackCall show ?thesis 
        by (simp add: tiTable_SampleT_def)
    next
      assume a12:"req t \<noteq> [init]"
      from tbl and a1 and a12 and ackCall show ?thesis 
         by (simp add: tiTable_SampleT_def)
    qed 
  next
    assume a2:"st_in t = call"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a21:"lose t = [True]"
      from tbl and a2 and a21 and ackCall show ?thesis 
        by (simp add: tiTable_SampleT_def)
    next
      assume a22:"lose t \<noteq> [True]"
      from this and tsLose have a22a:"lose t = [False]" 
         by (simp add: ts_bool_False)
      from tbl and a2 and a22a and ackCall show ?thesis
         by (simp add: tiTable_SampleT_def)
    qed 
  next
    assume a3:"st_in t = connection_ok"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a31:"lose t = [True]"
      from tbl and a3 and a31 and ackCall show ?thesis 
        by (simp add: tiTable_SampleT_def)
    next
      assume a32:"lose t \<noteq> [True]"
      from this and tsLose have a32a:"lose t = [False]" 
        by (simp add: ts_bool_False)
      show ?thesis
      proof (cases "req t = [send]")
        assume a321:"req t = [send]"
        from tbl and a3 and a32a and a321 and ackCall show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a322:"req t \<noteq> [send]"
        from tbl and a3 and a32a and a322 and ackCall show ?thesis
           by (simp add: tiTable_SampleT_def)
      qed
    qed 
  next
    assume a4:"st_in t = sending_data"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a41:"lose t = [True]"
      from tbl and a4 and a41 and ackCall show ?thesis
        by (simp add: tiTable_SampleT_def)
    next
      assume a42:"lose t \<noteq> [True]"
      from this and tsLose have a42a:"lose t = [False]" 
        by (simp add: ts_bool_False)
      show ?thesis
      proof (cases "x t = [sc_ack]")
        assume a421:"x t = [sc_ack]"
        from tbl and a4 and a42a and a421 and ackCall show ?thesis
          by (simp add: tiTable_SampleT_def)
      next
        assume a422:" x t \<noteq> [sc_ack]"
        from this and xMsg1  have a422a:"x t = []" 
          by (simp add: aType_empty)
        from tbl and a4 and a42a and a422a and ackCall show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  next  
    assume a5:"st_in t = voice_com"
    show ?thesis
    proof (cases "stop t = [stop_vc]")
      assume a51:"stop t = [stop_vc]"
      from tbl and a5 and a51 and ackCall show ?thesis 
        by (simp add: tiTable_SampleT_def)
    next
      assume a52:"stop t \<noteq> [stop_vc]"
      from this and stopMsg1 have a52a:"stop t = []" by (simp add: stopType_empty)
      show ?thesis
      proof (cases "lose t = [True]")
        assume a521:"lose t = [True]"
        from tbl and a5 and a52a and a521 and ackCall show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a522:"lose t \<noteq> [True]"
        from this and tsLose have a522a:"lose t = [False]" by (simp add: ts_bool_False)
        from tbl and a5 and a52a and a522a and ackCall show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  qed
qed

lemma tiTable_i1_2:
assumes tbl:"tiTable_SampleT req a1 stop lose st_in b ack i1 vc st_out" 
       and "ts lose"
       and "msg (Suc 0) a1"
       and "msg (Suc 0) stop" 
       and "ack t = [call]"
shows "i1 t = []"
proof -
  from assms have "st_in t = init_state \<and> req t = [init]"
    by (simp add: tiTable_ack_call)
  from this and tbl show ?thesis
    by (simp add: tiTable_SampleT_def)
qed 

lemma tiTable_ack_init0:
assumes tbl:"tiTable_SampleT req a1 stop lose 
                  (fin_inf_append [init_state] st) 
                   b ack i1 vc st" 
      and req0:"req 0 = []"
shows "ack 0 = [init_state]"
proof -
  have "(fin_inf_append [init_state] st) (0::nat) = init_state" 
    by (simp add: fin_inf_append_def)
  from tbl and this and req0 show ?thesis by (simp add: tiTable_SampleT_def)
qed

lemma tiTable_ack_init:
assumes "tiTable_SampleT req a1 stop lose 
                  (fin_inf_append [init_state] st) 
                   b ack i1 vc st"
      and "ts lose"
      and "msg (Suc 0) a1"
      and "msg (Suc 0) stop"
      and "\<forall> t1 \<le> t. req t1 = []"
shows "ack t = [init_state]"
using assms
proof (induction t)
  case 0
  from this show ?case
    by (simp add: tiTable_ack_init0)
next 
  case (Suc t)
  from Suc have sg1: "st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from Suc and sg1 have sg2: 
   "(fin_inf_append [init_state] st) (Suc t) = init_state"
    by (simp add: correct_fin_inf_append2)
  from Suc and sg1 and sg2 show ?case
    by (simp add: tiTable_SampleT_def)
qed

lemma tiTable_i1_3:
assumes tbl:"tiTable_SampleT req x stop lose 
                  (fin_inf_append [init_state] st)  b ack i1 vc st" 
      and tsLose:"ts lose"
      and xMsg1:"msg (Suc 0) x"
      and stopMsg1:"msg (Suc 0) stop"
      and h5:"\<forall> t1 \<le> t. req t1 = []" 
shows "i1 t = []"
proof - 
  from assms have sg1:"ack t = [init_state]"
    by (simp add: tiTable_ack_init)
  from assms have sg2:"st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from sg1 and sg2 have sg3:
   "(fin_inf_append [init_state] st) (Suc t) = init_state"
    by (simp add: correct_fin_inf_append2)
  from tbl and tsLose have sg4:"lose t = [True] \<or> lose t = [False]"
    by (simp add: ts_bool_True_False)
  from tbl and xMsg1 have sg5:"x t = [] \<or> x t = [sc_ack]"
    by (simp add: aType_lemma) 
  from tbl and stopMsg1 have sg6:"stop t = [] \<or> stop t = [stop_vc]"
    by (simp add: stopType_lemma) 
  show ?thesis
  proof (cases "fin_inf_append [init_state] st t")
    assume a1:"fin_inf_append [init_state] st t = init_state"
    from assms and sg1 and sg2 and sg3 and a1 show ?thesis
      by (simp add:  tiTable_SampleT_def)
  next
    assume a2:"fin_inf_append [init_state] st t = call"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a21:"lose t = [True]"
      from tbl and a2 and a21 show ?thesis 
         by (simp add: tiTable_SampleT_def)
    next
      assume a22:"lose t \<noteq> [True]"
      from this and tsLose have a22a:"lose t = [False]" 
        by (simp add: ts_bool_False)
      from tbl and a2 and a22a show ?thesis 
        by (simp add: tiTable_SampleT_def)
    qed 
  next
    assume a3:"fin_inf_append [init_state] st t = connection_ok"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a31:"lose t = [True]"
      from tbl and a3 and a31 show ?thesis 
         by (simp add: tiTable_SampleT_def)
    next
      assume a32:"lose t \<noteq> [True]"
      from this and tsLose have a32a:"lose t = [False]" 
         by (simp add: ts_bool_False)
      from h5 have a322:"req t \<noteq> [send]" by auto
      from tbl and a3 and a32a and a322 show ?thesis 
        by (simp add: tiTable_SampleT_def)
    qed 
  next
    assume a4:"fin_inf_append [init_state] st t = sending_data"
    show ?thesis
    proof (cases "lose t = [True]")
      assume a41:"lose t = [True]"
      from tbl and a4 and a41 show ?thesis by (simp add: tiTable_SampleT_def) 
    next
      assume a42:"lose t \<noteq> [True]"
      from this and tsLose have a42a:"lose t = [False]" by (simp add: ts_bool_False)
      show ?thesis
      proof (cases "x t = [sc_ack]")
        assume a421:"x t = [sc_ack]"
        from tbl and a4 and a42a and a421 and tsLose show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a422:" x t \<noteq> [sc_ack]"
        from this and xMsg1 have a422a:"x t = []" by (simp add: aType_empty)
        from tbl and a4 and a42a and a422a and tsLose show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  next
    assume a5:"fin_inf_append [init_state] st t = voice_com"
    show ?thesis
    proof (cases "stop t = [stop_vc]")
      assume a51:"stop t = [stop_vc]"
      from tbl and a5 and a51 and tsLose show ?thesis 
         by (simp add: tiTable_SampleT_def)
    next
      assume a52:"stop t \<noteq> [stop_vc]"
      from this and stopMsg1 have a52a:"stop t = []" by (simp add: stopType_empty)
      show ?thesis
      proof (cases "lose t = [True]")
        assume a521:"lose t = [True]"
        from tbl and a5 and a52a and a521 and tsLose show ?thesis 
          by (simp add: tiTable_SampleT_def)
      next
        assume a522:"lose t \<noteq> [True]"
        from this and tsLose have a522a:"lose t = [False]" by (simp add: ts_bool_False)
        from tbl and a5 and a52a and a522a and tsLose show ?thesis 
          by (simp add: tiTable_SampleT_def)
      qed
    qed
  qed
qed

lemma tiTable_st_call_ok:
assumes tbl:"tiTable_SampleT req x stop lose 
                  (fin_inf_append [init_state] st) 
                   b ack i1 vc st"
      and tsLose:"ts lose"
      and h3:"\<forall>m \<le> k. ack (Suc (Suc (t + m))) = [connection_ok]"
      and h4:"st (Suc t) = call"
shows "st (Suc (Suc t)) = connection_ok"
proof - 
    from h4 have sg1:
     "(fin_inf_append [init_state] st) (Suc (Suc t)) = call"
      by (simp add: correct_fin_inf_append2)
   from tbl and tsLose have sg2:"lose (Suc (Suc t)) = [True] \<or> lose (Suc (Suc t)) = [False]"
    by (simp add: ts_bool_True_False) 
   show ?thesis
   proof (cases "lose (Suc (Suc t)) = [False]")
     assume a1:"lose (Suc (Suc t)) = [False]"
     from tbl and a1 and sg1 show ?thesis  
       by (simp add: tiTable_SampleT_def)
   next
     assume a2:"lose (Suc (Suc t)) \<noteq> [False]"
     from h3 have sg3:"ack (Suc (Suc t)) = [connection_ok]" by auto
     from tbl and a2 and sg1 and sg2 and sg3 show ?thesis
       by (simp add: tiTable_SampleT_def)   
   qed
qed

lemma tiTable_i1_4b:
assumes "tiTable_SampleT req x stop lose 
                  (fin_inf_append [init_state] st) b ack i1 vc st"
      and "ts lose"
      and "msg (Suc 0) x"
      and "msg (Suc 0) stop" 
      and "\<forall> t1 \<le> t. req t1 = []"
      and "req (Suc t) = [init]"
      and "\<forall>m < k + 3. req (t + m) \<noteq> [send]"
      and h7:"\<forall>m \<le> k. ack (Suc (Suc (t + m))) = [connection_ok]"
      and "\<forall>j \<le> k + 3. lose (t + j) = [False]"
      and h9:"t2 < (t + 3 + k)"
shows "i1 t2 = []"
proof (cases "t2 \<le> t")
  assume "t2 \<le> t"
  from assms and this show ?thesis by (simp add: tiTable_i1_3)
next 
  assume a2:"\<not> t2 \<le> t"
  from assms have sg1:"ack t = [init_state]" by (simp add: tiTable_ack_init)
  from assms have sg2:"st t =  hd (ack t)" by (simp add: tiTable_ack_st_hd)  
  from sg1 and sg2 have sg3:
   "(fin_inf_append [init_state] st) (Suc t) = init_state"
    by (simp add: correct_fin_inf_append2)
  from assms and sg3 have sg4:"st (Suc t) = call"
    by (simp add: tiTable_SampleT_def)
  show ?thesis
  proof (cases "t2 = Suc t")
    assume a3:"t2 = Suc t"
    from assms and sg3 and a3 show ?thesis
      by (simp add: tiTable_SampleT_def)  
  next
    assume a4:"t2 \<noteq> Suc t" 
    from assms and sg4 and a4 and a2 have sg7:"st (Suc (Suc t)) = connection_ok"
      by (simp add: tiTable_st_call_ok)
    from assms have sg8:"ack (Suc (Suc t)) = [st (Suc (Suc t))]"
      by (simp add: tiTable_ack_st)
    show ?thesis
    proof (cases "t2 =  Suc (Suc t)")
      assume a5:"t2 =  Suc (Suc t)"
      from h7 and h9 and a5 have sg9:"ack t2 = [connection_ok]" by auto
      from assms and sg9 show ?thesis by (simp add:  tiTable_i1_1)
    next 
      assume a6:"t2 \<noteq> Suc (Suc t)"
      from a6 and a4 and a2 have sg10:"Suc (Suc t) < t2" by arith
      from h7 and h9 and sg10 have sg11:"ack t2 = [connection_ok]" 
        by (simp add: aux_ack_t2)
      from assms and a6 and sg7 and sg8 and sg11 show ?thesis 
        by (simp add:  tiTable_i1_1)
    qed
  qed
qed
 
lemma tiTable_i1_4:
assumes "tiTable_SampleT req a1 stop lose 
                  (fin_inf_append [init_state] st) b ack i1 vc st"
      and "ts lose"
      and "msg (Suc 0) a1"
      and "msg (Suc 0) stop" 
      and "\<forall> t1 \<le> t. req t1 = []"
      and "req (Suc t) = [init]"
      and "\<forall>m < k + 3. req (t + m) \<noteq> [send]"
      and "\<forall>m \<le> k. ack (Suc (Suc (t + m))) = [connection_ok]"
      and "\<forall>j \<le> k + 3. lose (t + j) = [False]"
shows "\<forall> t2 < (t + 3 + k). i1 t2 = []"
using assms by (simp add: tiTable_i1_4b)

lemma tiTable_ack_ok:
  assumes h1:"\<forall>j\<le> d + 2. lose (t + j) = [False]"
      and tsLose:"ts lose"
      and stopMsg1:"msg (Suc 0) stop"
      and a1Msg1:"msg (Suc 0) a1"
      and reqNsend:"req (Suc t) \<noteq> [send]"
      and ackCon:"ack t = [connection_ok]"
      and tbl:"tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) b ack i1 vc st"
  shows "ack (Suc t) = [connection_ok]"
proof -
  from tbl and tsLose and a1Msg1 and stopMsg1 have "st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from this and ackCon have sg2:
   "(fin_inf_append [init_state] st) (Suc t) =  connection_ok"
    by (simp add: correct_fin_inf_append2)
  have sg3a:"Suc 0 \<le> d + 2" by arith
  from h1 and sg3a have sg3:"lose (t + Suc 0) = [False]" by auto 
  from sg2 and sg3 and reqNsend and tbl show ?thesis
    by (simp add: tiTable_SampleT_def) 
qed

lemma Gateway_L7a:
  assumes gw:"Gateway req dt a stop lose d ack i vc"
      and aMsg1:"msg (Suc 0) a"
      and stopMsg1:"msg (Suc 0) stop"
      and reqMsg1:"msg (Suc 0) req"
      and tsLose:"ts lose"
      and loseFalse:"\<forall>j\<le> d + 2. lose (t + j) = [False]"
      and nsend:"req (Suc t) \<noteq> [send]"
      and ackNCon:"ack (t) = [connection_ok]"
  shows "ack (Suc t) = [connection_ok]"
proof -
  from gw and stopMsg1 and reqMsg1 and nsend obtain i1 i2 a1 a2 where 
    ah1:"Sample req dt a1 stop lose ack i1 vc" and
    ah2:"Delay a2 i1 d a1 i2" and
    ah3:"Loss lose a i2 a2 i"
    by (simp add: Gateway_def, auto)
  from ah2 and ah3 and aMsg1 have sg1:"msg (Suc 0) a1"
    by (simp add: Loss_Delay_msg_a) 
  from ah1 and sg1 and stopMsg1 and reqMsg1 obtain st buffer where
    ah4:"Sample_L req dt a1 stop lose (fin_inf_append [init_state] st) 
             (fin_inf_append [[]] buffer)
             ack i1 vc st buffer"
    by (simp add: Sample_def, auto)
  from ah4 have sg2:
    "tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) 
         (fin_inf_append [[]] buffer)
         ack i1 vc st"
    by (simp add: Sample_L_def)
  from loseFalse and tsLose and stopMsg1 and sg1 and 
           nsend and ackNCon and sg2 show ?thesis
    by (simp add: tiTable_ack_ok)
qed

lemma Sample_L_buffer:
  assumes 
    "Sample_L req dt a1 stop lose (fin_inf_append [init_state] st)
          (fin_inf_append [[]] buffer)
           ack i1 vc st buffer"
  shows "buffer t = inf_last_ti dt t"
proof - 
  from assms have 
   "\<forall>t. buffer t = 
    (if dt t = [] then fin_inf_append [[]] buffer t else dt t)"
    by (simp add: Sample_L_def) 
  from this show ?thesis 
  proof (induct t)
    case 0 
    from this show ?case
      by (simp add: fin_inf_append_def)
  next
    fix t
    case (Suc t)  
    from this show ?case
    proof (cases "dt t = []")
      assume "dt t = []"
      from this and Suc show ?thesis
        by (simp add: correct_fin_inf_append1)
    next
      assume "dt t \<noteq> []"
      from this and Suc show ?thesis
        by (simp add: correct_fin_inf_append1)
    qed
  qed
qed
 
lemma  tiTable_SampleT_i1_buffer:
 assumes "ack t = [connection_ok]"
        and reqSend:"req (Suc t) = [send]" 
        and loseFalse:"\<forall>k\<le>Suc d. lose (t + k) = [False]" 
        and buf: "buffer t = inf_last_ti dt t"
        and tbl:"tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) 
      (fin_inf_append [[]] buffer) ack
      i1 vc st"
     and conOk:"fin_inf_append [init_state] st (Suc t) = connection_ok"
shows "i1 (Suc t) = inf_last_ti dt t"
proof -  
  have sg1:"Suc 0 \<le>Suc d" by arith
  from loseFalse and sg1 have sg2:"lose (Suc t) = [False]" by auto
  from tbl have
   "fin_inf_append [init_state] st (Suc t) = connection_ok \<and> 
    req (Suc t) = [send] \<and> 
    lose (Suc t) = [False] \<longrightarrow>
    ack (Suc t) = [sending_data] \<and> 
    i1 (Suc t) = (fin_inf_append [[]] buffer) (Suc t) \<and> 
    vc (Suc t) = [] \<and> st (Suc t) = sending_data"
    by (simp add: tiTable_SampleT_def)  
  from this and conOk and reqSend and sg2 have 
   "i1 (Suc t) = (fin_inf_append [[]] buffer) (Suc t)" by simp
  from this and buf show ?thesis by (simp add: correct_fin_inf_append1) 
qed  

lemma Sample_L_i1_buffer:
  assumes "msg (Suc 0) req"
      and "msg (Suc 0) a"
      and stopMsg1:"msg (Suc 0) stop"
      and a1Msg1:"msg (Suc 0) a1"
      and tsLose:"ts lose"
      and ackCon:"ack t = [connection_ok]"
      and reqSend:"req (Suc t) = [send]"
      and loseFalse:"\<forall>k\<le>Suc d. lose (t + k) = [False]"
      and smpl:"Sample_L req dt a1 stop lose 
                (fin_inf_append [init_state] st) 
                (fin_inf_append [[]] buffer) ack i1 vc st buffer"
  shows "i1 (Suc t) =  buffer t"
proof - 
  from smpl have sg1:"buffer t = inf_last_ti dt t"
    by (simp add: Sample_L_buffer)
  from smpl have sg2:
    "\<forall>t. buffer t = (if dt t = [] then fin_inf_append [[]] buffer t else dt t)"
    by (simp add: Sample_L_def)
  from smpl have sg3: 
    "tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) 
      (fin_inf_append [[]] buffer) ack
      i1 vc st"   
    by (simp add: Sample_L_def) 
  from sg3 and tsLose and a1Msg1 and stopMsg1 have sg4:"st t =  hd (ack t)"
    by (simp add: tiTable_ack_st_hd)  
  from ackCon and sg4 have sg5:
    "(fin_inf_append [init_state] st) (Suc t) = connection_ok"
    by (simp add: correct_fin_inf_append1)
  from ackCon and reqSend and loseFalse and sg1 and 
           sg3 and sg4 and sg5 have sg6:
    "i1 (Suc t) = inf_last_ti dt t"
     by (simp add: tiTable_SampleT_i1_buffer)
  from this and sg1 show ?thesis by simp
qed

lemma tiTable_SampleT_sending_data:
  assumes tbl: "tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) 
         (fin_inf_append [[]] buffer)
         ack i1 vc st"
      and loseFalse:"\<forall>j\<le>2 * d. lose (t + j) = [False]"
      and a1e:"\<forall>t4\<le>t + d + d. a1 t4 = []"
      and snd:"fin_inf_append [init_state] st (Suc (t + x)) = sending_data"
      and h6:"Suc (t + x) \<le> 2 * d + t"
  shows "ack (Suc (t + x)) = [sending_data]"
proof -
  from h6 have "Suc x \<le> 2 * d" by arith
  from this and loseFalse have sg1:"lose (t + Suc x) = [False]" by auto
  from h6 have "Suc (t + x) \<le>t + d + d" by arith
  from this and a1e have sg2:"a1 (Suc (t + x)) = []" by auto
  from tbl and sg1 and sg2 and snd show ?thesis 
    by (simp add: tiTable_SampleT_def) 
qed

lemma Sample_sending_data:
  assumes stopMsg1:"msg (Suc 0) stop"
      and tsLose:"ts lose"
      and reqMsg1:"msg (Suc 0) req"
      and a1Msg1:"msg (Suc 0) a1"
      and loseFalse:"\<forall>j\<le>2 * d. lose (t + j) = [False]"
      and ackSnd:"ack t = [sending_data]"
      and smpl:"Sample req dt a1 stop lose ack i1 vc"
      and xdd:"x \<le> d + d"
      and h9:"\<forall>t4 \<le> t + d + d. a1 t4 = []"
 shows "ack (t + x) = [sending_data]"
using assms
proof -
  from stopMsg1 and reqMsg1 and a1Msg1 and smpl obtain st buffer where a1: 
   "Sample_L req dt a1 stop lose (fin_inf_append [init_state] st) 
             (fin_inf_append [[]] buffer) ack
             i1 vc st buffer"
    by (simp add: Sample_def, auto)
  from a1 have sg1:
    "tiTable_SampleT req a1 stop lose (fin_inf_append [init_state] st) 
        (fin_inf_append [[]] buffer)
         ack i1 vc st" 
     by (simp add: Sample_L_def)
  from a1 have sg2:
    "\<forall>t. buffer t = (if dt t = [] then fin_inf_append [[]] buffer t else dt t)"
     by (simp add: Sample_L_def)
  from stopMsg1 and tsLose and a1Msg1 and ackSnd and xdd and sg1 and sg2 show ?thesis
  proof (induct "x")
    case 0
    from this show ?case by simp
  next
    fix x
    case (Suc x)  
    from this have sg3:"st (t + x) = hd (ack (t + x))"
      by (simp add: tiTable_ack_st_hd) 
    from Suc have sg4:"x \<le> d + d" by arith 
    from Suc and sg3 and sg4 have sg5:  
     "(fin_inf_append [init_state] st) (Suc (t + x)) = sending_data"
      by (simp add: fin_inf_append_def)
    from Suc have sg6:"Suc (t + x) \<le> 2 * d + t" by simp
    from Suc have sg7:"ack (t + x) = [sending_data]" by simp
    from sg1 and loseFalse and h9 and sg7 and sg5 and sg6 have sg7:
     "ack (Suc (t + x)) = [sending_data]"
      by (simp add: tiTable_SampleT_sending_data)
    from this show ?case by simp
  qed
qed


subsection \<open>Properties of the ServiceCenter component\<close>

lemma ServiceCenter_a_l:
  assumes "ServiceCenter i a"
  shows    "length (a t) \<le> (Suc 0)" 
proof (cases "t")
  case 0 
  from this and assms show ?thesis by (simp add: ServiceCenter_def)
next
  fix m assume "t = Suc m"
  from this and assms show ?thesis by (simp add: ServiceCenter_def)
qed

lemma ServiceCenter_a_msg:
  assumes "ServiceCenter i a"
  shows    "msg (Suc 0) a"
using assms  
by (simp add: msg_def ServiceCenter_a_l)

lemma ServiceCenter_L1:
assumes "\<forall> t2 < x. i t2 = []"
       and "ServiceCenter i a"
       and "t \<le> x"
shows "a t = []"
using assms
proof (induct t)
   case 0 
   from this show ?case by (simp add: ServiceCenter_def)
next
   case (Suc t)
   from this show ?case by (simp add: ServiceCenter_def)
qed

lemma ServiceCenter_L2:
assumes "\<forall> t2 < x. i t2 = []"
       and "ServiceCenter i a"
shows "\<forall> t3 \<le> x. a t3 = []"
using assms 
by (clarify, simp add: ServiceCenter_L1)


subsection \<open>General properties of stream values\<close>

lemma streamValue1: 
assumes h1:"\<forall>j\<le> D + (z::nat). str (t + j) = x"
       and h2: "j\<le> D"
shows      "str (t + j + z) = x"
proof - 
    from h2 have sg1:" j + z \<le> D + z" by arith
    have sg2:"t + j + z = t + (j + z)" by arith 
    from h1 and sg1 and sg2 show ?thesis by (simp (no_asm_simp))
qed

lemma streamValue2:
  assumes "\<forall>j\<le> D + (z::nat). str (t + j) = x"
  shows    "\<forall>j\<le> D. str (t + j + z) = x"
using assms by (clarify, simp add: streamValue1)

lemma streamValue3:
assumes "\<forall>j\<le> D. str (t + j + (Suc y)) = x"
        and "j \<le> D"
        and h3:"str (t + y) = x"
    shows    "str (t + j + y) = x"
using assms
proof (induct j) 
  case 0
  from h3 show ?case by simp
next
  case (Suc j) 
  from this show ?case by auto
qed
  
lemma streamValue4:
assumes "\<forall>j\<le> D. str (t + j + (Suc y)) = x"
       and "str (t + y) = x"
shows     "\<forall>j\<le> D. str (t + j + y) = x"
using assms 
by (clarify, hypsubst_thin, simp add: streamValue3)

lemma streamValue5:
assumes "\<forall>j\<le> D. str (t + j + ((i::nat) + k)) = x"
       and "j\<le> D"
shows      "str (t + i + k + j) = x"
using assms
by (metis add.commute add.left_commute)

lemma streamValue6:
  assumes "\<forall>j\<le> D. str (t + j + ((i::nat) + k)) = x"
  shows     "\<forall>j\<le> D. str (t + (i::nat) + k + j) = x"
using assms by (clarify, simp add: streamValue5)

lemma streamValue7:
  assumes h1:"\<forall>j\<le>d. str (t + i + k + d + Suc j) = x"
      and h2:"str (t + i + k + d) = x"
      and h3:"j\<le> Suc d"
  shows      "str (t + i + k + d + j) = x"
proof - 
  from h1 have sg1:"str (t + i + k + d + Suc d) = x" 
     by (simp (no_asm_simp), simp) 
  from assms show ?thesis 
  proof (cases "j = Suc d")
    assume a1:"j = Suc d"
    from a1 and sg1 show ?thesis by simp
  next
    assume a2:"j \<noteq> Suc d"
    from a2 and h3 have sg2:"j\<le>d" by auto
    from assms and sg2 show ?thesis
    proof (cases "j > 0")
      assume a3:"0 < j"
      from a3 and h3 have sg3:"j - (1::nat) \<le> d" by simp
      from a3 have sg4:"Suc (j - (1::nat)) = j"  by arith
      from sg3 and h1 and sg4 have sg5:"str (t + i + k + d + j) = x" by auto
      from sg5 show ?thesis by simp
    next
      assume a4:"\<not> 0 < j"
      from a4 have sg6:"j = 0" by simp
      from h2 and sg6 show ?thesis by simp
    qed
  qed
qed

lemma streamValue8:
assumes "\<forall>j\<le>d. str (t + i + k + d + Suc j) = x"
       and "str (t + i + k + d) = x" 
shows "\<forall> j\<le> Suc d. str (t + i + k + d + j) = x"
using assms streamValue7
  by metis

lemma arith_streamValue9aux:
"Suc (t + (j + d) + (i + k)) =  Suc (t + i + k + d + j)" 
by arith

lemma streamValue9:
assumes h1:"\<forall>j\<le>2 * d. str (t + j + Suc (i + k)) = x"
       and h2:"j\<le>d"
shows      "str (t + i + k + d + Suc j) = x"
proof -
  from h2 have "(j+d) \<le>2 * d" by arith
  from h1 and this have "str (t + (j + d) + Suc (i + k)) = x" by auto
  from this show ?thesis  by (simp add: arith_streamValue9aux)  
qed     

lemma streamValue10:
  assumes "\<forall>j\<le>2 * d. str (t + j + Suc (i + k)) = x"
  shows    "\<forall>j\<le>d. str (t + i + k + d + Suc j) = x"
using assms 
  apply clarify
  by (rule streamValue9, auto)

lemma arith_sum1:"(t::nat) + (i + k + d) =  t + i + k + d"
by arith

lemma arith_sum2:"Suc (Suc (t + k + j)) = Suc (Suc (t + (k + j)))"
by arith

lemma arith_sum4:"t + 3 + k + d = Suc (t + (2::nat) + k + d)"
by arith

lemma streamValue11:
assumes h1:"\<forall>j\<le>2 * d + (4 + k). lose (t + j) = x"
       and h2:"j\<le>Suc d"
shows      "lose (t + 2 + k + j) = x"
proof -
  from h2 have sg1:"2 + k + j \<le>2 * d + (4 + k)" by arith
  have sg2:"Suc (Suc (t + k + j)) = Suc (Suc (t + (k + j)))" by arith
  from sg1 and h1 have "lose (t + (2 + k + j)) = x" by blast
  from this and sg2 show ?thesis by (simp add: arith_sum2)
qed 

lemma streamValue12:
 assumes  "\<forall>j\<le>2 * d + (4 + k). lose (t + j) = x"
 shows     "\<forall>j\<le>Suc d. lose (t + 2 + k + j) = x"
using assms
  apply clarify
  by (rule streamValue11, auto)

lemma streamValue43:
  assumes "\<forall>j\<le>2 * d + ((4::nat) + k). lose (t + j) = [False]"
  shows    "\<forall>j\<le>2 * d. lose ((t + (3::nat) + k) + j) = [False]"
proof -
  from assms have sg1:"\<forall>j\<le>2 * d. lose (t + j + (4 + k)) = [False]" 
    by (simp add: streamValue2)
  have sg2:"Suc (3 + k) = (4 + k)" by arith
  from sg1 and sg2 have sg3:"\<forall>j\<le>2 * d. lose (t + j + Suc (3 + k)) = [False]" 
    by (simp (no_asm_simp))  
  from assms have sg4:"lose (t + (3 + k)) = [False]" by auto
  from sg3 and sg4 have sg5:"\<forall>j\<le>2 * d. lose (t + j + (3 + k)) = [False]" 
    by (rule streamValue4) 
  from sg5 show ?thesis by (rule streamValue6) 
qed

end
