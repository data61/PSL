(*<*)
(*
   Title:  Gateway.thy  (Gateway: Specification)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
section \<open>Gateway: Specification\<close>

theory Gateway 
imports Gateway_types
begin

definition
 ServiceCenter :: 
   "ECall_Info istream \<Rightarrow> aType istream \<Rightarrow> bool "
where
 "ServiceCenter i a 
  \<equiv> 
  \<forall> (t::nat). 
  a 0 = [] \<and>  a (Suc t) =  (if (i t) = [] then []  else [sc_ack])"

definition
  Loss ::
   "bool istream \<Rightarrow> aType istream \<Rightarrow> ECall_Info istream \<Rightarrow> 
    aType istream \<Rightarrow> ECall_Info istream \<Rightarrow> bool"
where
 "Loss lose a i2 a2 i 
  \<equiv> 
  \<forall> (t::nat). 
  ( if lose t =  [False]
    then a2 t = a t \<and> i t = i2 t 
    else a2 t = []  \<and> i t = []   )"

definition
 Delay ::
  "aType istream \<Rightarrow> ECall_Info istream \<Rightarrow> nat \<Rightarrow> 
   aType istream \<Rightarrow> ECall_Info istream \<Rightarrow> bool"
where
 "Delay a2 i1 d a1 i2 
  \<equiv> 
  \<forall> (t::nat).  
   (t < d \<longrightarrow> a1 t = [] \<and> i2 t = []) \<and> 
   (t \<ge> d \<longrightarrow> (a1 t = a2 (t-d)) \<and> (i2 t = i1 (t-d)))"

definition
 tiTable_SampleT ::
 "reqType istream  \<Rightarrow> aType istream \<Rightarrow> 
  stopType istream \<Rightarrow> bool istream \<Rightarrow> 
  (nat \<Rightarrow> GatewayStatus) \<Rightarrow>  (nat \<Rightarrow> ECall_Info list) \<Rightarrow>
  GatewayStatus istream \<Rightarrow> ECall_Info istream \<Rightarrow> vcType istream 
  \<Rightarrow> (nat \<Rightarrow> GatewayStatus) \<Rightarrow> bool "
where
 "tiTable_SampleT req a1 stop lose st_in buffer_in 
         ack i1 vc st_out
  \<equiv>
  \<forall> (t::nat) 
     (r::reqType list) (x::aType list) 
     (y::stopType list) (z::bool list).
   \<comment> \<open>1:\<close>
   ( st_in t = init_state \<and> req t = [init]
     \<longrightarrow> ack t = [call] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = call ) 
   \<and>     
   \<comment> \<open>2:\<close>
   ( st_in t = init_state \<and> req t \<noteq> [init]
     \<longrightarrow>  ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = init_state ) 
   \<and>
   \<comment> \<open>3:\<close>
   ( (st_in t = call \<or> (st_in t = connection_ok \<and> r \<noteq> [send])) \<and>
     req t = r \<and> lose t = [False]
     \<longrightarrow>  ack t = [connection_ok] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = connection_ok ) 
   \<and>
   \<comment> \<open>4:\<close>
   ( (st_in t = call \<or> st_in t = connection_ok \<or> st_in t = sending_data)
     \<and> lose t = [True]
     \<longrightarrow>  ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = init_state ) 
   \<and>
   \<comment> \<open>5:\<close>
   ( st_in t = connection_ok \<and> req t = [send] \<and> lose t = [False]
     \<longrightarrow> ack t = [sending_data] \<and> i1 t = buffer_in t \<and> vc t = [] 
         \<and> st_out t = sending_data ) 
   \<and>
   \<comment> \<open>6:\<close>
   ( st_in t = sending_data \<and> a1 t = [] \<and> lose t = [False]
     \<longrightarrow> ack t = [sending_data] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = sending_data ) 
   \<and>
   \<comment> \<open>7:\<close>
   ( st_in t = sending_data \<and> a1 t = [sc_ack] \<and> lose t = [False]
     \<longrightarrow> ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] 
         \<and> st_out t = voice_com ) 
   \<and>
   \<comment> \<open>8:\<close>
   ( st_in t = voice_com \<and> stop t = [] \<and> lose t = [False]
     \<longrightarrow> ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [vc_com] 
         \<and> st_out t = voice_com ) 
   \<and>
   \<comment> \<open>9:\<close>
   ( st_in t = voice_com \<and> stop t = [] \<and> lose t = [True]
     \<longrightarrow> ack t = [voice_com] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = voice_com ) 
   \<and>
   \<comment> \<open>10:\<close>
   ( st_in t = voice_com \<and> stop t = [stop_vc] 
     \<longrightarrow> ack t = [init_state] \<and> i1 t = [] \<and> vc t = [] 
         \<and> st_out t = init_state )" 

definition
 Sample_L ::
 "reqType istream  \<Rightarrow> ECall_Info istream \<Rightarrow> aType istream \<Rightarrow> 
  stopType istream \<Rightarrow> bool istream \<Rightarrow> 
  (nat \<Rightarrow> GatewayStatus) \<Rightarrow>  (nat \<Rightarrow> ECall_Info list) \<Rightarrow>
  GatewayStatus istream \<Rightarrow> ECall_Info istream \<Rightarrow> vcType istream 
  \<Rightarrow> (nat \<Rightarrow> GatewayStatus)  \<Rightarrow> (nat \<Rightarrow> ECall_Info list)
  \<Rightarrow> bool "
where
 "Sample_L req dt a1 stop lose st_in buffer_in 
         ack i1 vc st_out buffer_out
  \<equiv>
  (\<forall> (t::nat). 
   buffer_out t = 
    (if dt t = [] then buffer_in t  else dt t) )
  \<and> 
  (tiTable_SampleT req a1 stop lose st_in buffer_in 
                   ack i1 vc st_out)" 

definition
 Sample ::
 "reqType istream  \<Rightarrow> ECall_Info istream \<Rightarrow> aType istream \<Rightarrow> 
  stopType istream \<Rightarrow> bool istream \<Rightarrow> 
  GatewayStatus istream \<Rightarrow> ECall_Info istream \<Rightarrow> vcType istream
  \<Rightarrow> bool "
where
 "Sample req dt a1 stop lose  ack i1 vc 
  \<equiv>
  ((msg (1::nat) req) \<and> 
   (msg (1::nat) a1)  \<and> 
   (msg (1::nat) stop)) 
  \<longrightarrow> 
  (\<exists> st buffer. 
  (Sample_L req dt a1 stop lose 
            (fin_inf_append [init_state] st)
            (fin_inf_append [[]] buffer)
            ack i1 vc st buffer) )"

definition
 Gateway :: 
   "reqType istream \<Rightarrow> ECall_Info istream \<Rightarrow> aType istream \<Rightarrow> 
    stopType istream \<Rightarrow> bool istream \<Rightarrow> nat \<Rightarrow>
    GatewayStatus istream \<Rightarrow> ECall_Info istream \<Rightarrow> vcType istream
    \<Rightarrow> bool"
where
 "Gateway req dt a stop lose d ack i vc 
  \<equiv> \<exists> i1 i2 x y. 
    (Sample req dt x stop lose ack i1 vc) \<and> 
    (Delay y i1 d x i2) \<and> 
    (Loss lose a i2 y i)"


definition
  GatewaySystem :: 
   "reqType istream \<Rightarrow> ECall_Info istream \<Rightarrow> 
    stopType istream \<Rightarrow> bool istream \<Rightarrow> nat \<Rightarrow>
    GatewayStatus istream \<Rightarrow> vcType istream
    \<Rightarrow> bool"
where
 "GatewaySystem req dt stop lose d ack vc 
  \<equiv>
  \<exists> a i. 
 (Gateway req dt a stop lose d ack i vc) \<and> 
 (ServiceCenter i a)"

definition
 GatewayReq :: 
   "reqType istream \<Rightarrow> ECall_Info istream \<Rightarrow> aType istream \<Rightarrow> 
    stopType istream \<Rightarrow> bool istream \<Rightarrow> nat \<Rightarrow>
    GatewayStatus istream \<Rightarrow> ECall_Info istream \<Rightarrow> vcType istream
    \<Rightarrow> bool"
where
 "GatewayReq req dt a stop lose d ack i vc 
  \<equiv>  
 ((msg (1::nat) req) \<and>  (msg (1::nat) a)  \<and> 
  (msg (1::nat) stop) \<and>  (ts lose)) 
   \<longrightarrow>
  (\<forall> (t::nat).
  ( ack t = [init_state] \<and> req (Suc t) = [init] \<and> 
    lose (t+1) = [False] \<and> lose (t+2) = [False]
    \<longrightarrow> ack (t+2) = [connection_ok]) 
  \<and> 
  ( ack t = [connection_ok] \<and> req (Suc t)  = [send] \<and>  
    (\<forall> (k::nat). k \<le> (d+1) \<longrightarrow> lose (t+k) = [False]) 
    \<longrightarrow> i ((Suc t) + d) = inf_last_ti dt t 
        \<and>  ack (Suc t) = [sending_data])
  \<and> 
  ( ack (t+d) = [sending_data] \<and> a (Suc t) = [sc_ack] \<and>  
    (\<forall> (k::nat). k \<le> (d+1) \<longrightarrow> lose (t+k) = [False]) 
    \<longrightarrow> vc ((Suc t) + d) = [vc_com]) )"

definition
  GatewaySystemReq :: 
   "reqType istream \<Rightarrow> ECall_Info istream \<Rightarrow> 
    stopType istream \<Rightarrow> bool istream \<Rightarrow> nat \<Rightarrow>
    GatewayStatus istream \<Rightarrow> vcType istream
    \<Rightarrow> bool"
where
 "GatewaySystemReq req dt  stop lose d ack vc 
  \<equiv>
 ((msg (1::nat) req) \<and> (msg (1::nat) stop) \<and> (ts lose))
   \<longrightarrow>
  (\<forall> (t::nat) (k::nat). 
  ( ack t = [init_state] \<and> req (Suc t) = [init]
  \<and> (\<forall> t1. t1 \<le> t \<longrightarrow> req t1 = [])
  \<and> req (t+2) = []
  \<and> (\<forall> m. m < k + 3 \<longrightarrow> req (t + m) \<noteq> [send])
  \<and>  req (t+3+k)  = [send] \<and>  inf_last_ti dt (t+2) \<noteq> []
  \<and> (\<forall> (j::nat). 
     j \<le> (4 + k + d + d) \<longrightarrow> lose (t+j) = [False]) 
  \<longrightarrow> vc (t + 4 + k + d + d) = [vc_com]) )"

end
