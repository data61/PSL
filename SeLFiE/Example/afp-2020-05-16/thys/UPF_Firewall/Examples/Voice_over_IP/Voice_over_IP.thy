(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2016 Université Paris-Sud, France
 *               2015-2016 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *****************************************************************************)

section \<open>Voice over IP\<close>
theory 
  Voice_over_IP
  imports 
    "../../UPF-Firewall"
begin
  

text\<open>
  In this theory we generate the test data for correct runs of the FTP protocol. As usual, we 
  start with definining the networks and the policy. We use a rather simple policy which allows 
  only FTP connections starting from the Intranet and going to the Internet, and deny everything 
  else. 
\<close>

definition 
  intranet :: "adr\<^sub>i\<^sub>p net" where
  "intranet = {{(a,e) . a = 3}}"

definition 
  internet :: "adr\<^sub>i\<^sub>p net" where
  "internet = {{(a,c). a > 4}}"

definition 
  gatekeeper :: "adr\<^sub>i\<^sub>p net" where
  "gatekeeper = {{(a,c). a =4}}"

definition 
  voip_policy :: "(adr\<^sub>i\<^sub>p,address voip_msg) FWPolicy" where
  "voip_policy = A\<^sub>U"

text\<open>
  The next two constants check if an address is in the Intranet or in the Internet respectively.
\<close>

definition 
  is_in_intranet :: "address  \<Rightarrow> bool" where
  "is_in_intranet a = (a = 3)"

definition 
  is_gatekeeper :: "address \<Rightarrow> bool" where
  "is_gatekeeper a =  (a = 4)"

definition 
  is_in_internet :: "address \<Rightarrow> bool" where
  "is_in_internet a =  (a > 4)"

text\<open>
  The next definition is our starting state: an empty trace and the just defined policy.
\<close>

definition 
  "\<sigma>_0_voip" ::  "(adr\<^sub>i\<^sub>p, address voip_msg) history \<times>
                 (adr\<^sub>i\<^sub>p, address voip_msg) FWPolicy" 
where                                     
  "\<sigma>_0_voip = ([],voip_policy)"

text\<open>
  Next we state the conditions we have on our trace: a normal behaviour FTP run from the intranet 
  to some server in the internet on port 21.
\<close>

definition "accept_voip" ::  "(adr\<^sub>i\<^sub>p, address voip_msg) history \<Rightarrow> bool" where
          "accept_voip t =   (\<exists> c s g i p1 p2. t \<in> NB_voip c s g i p1 p2 \<and> is_in_intranet c 
                                              \<and> is_in_internet s
                                              \<and> is_gatekeeper g)"

fun packet_with_id where
 "packet_with_id [] i = []"
|"packet_with_id (x#xs) i = 
  (if id x = i then (x#(packet_with_id xs i)) else (packet_with_id xs i))"

text\<open>
  The depth of the test case generation corresponds to the maximal length of generated traces,  
  4 is the minimum to get a full FTP protocol run.
\<close>

fun ids1 where
 "ids1 i (x#xs) = (id x = i \<and> ids1 i xs)"
|"ids1 i [] = True"

lemmas ST_simps = Let_def valid_SE_def unit_SE_def bind_SE_def
 subnet_of_int_def  p_accept_def content_def
 is_in_intranet_def is_in_internet_def intranet_def internet_def exI
 subnetOf_lemma subnetOf_lemma2 subnetOf_lemma3 subnetOf_lemma4 voip_policy_def
 NetworkCore.id_def  is_arq_def is_fin_def
 is_connect_def is_setup_def ports_open_def subnet_of_adr_def
 VOIP.NB_voip_def \<sigma>_0_voip_def PLemmas VOIP_TRPolicy_def
 policy2MON_def applyPolicy_def 

end
