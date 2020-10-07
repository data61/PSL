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

subsection\<open>Personal Firewall: Integer\<close>
theory 
  PersonalFirewallInt
  imports 
    "../../UPF-Firewall"
begin

text\<open>
  The most basic firewall scenario; there is a personal PC on one side and the Internet on the 
  other.  There are two policies: the first one allows all traffic from the PC to the Internet and 
  denies all coming into the PC. The second policy only allows specific ports from the PC. This 
  scenario comes in three variants: the first one specifies the allowed protocols directly, the 
  second together  with their respective port numbers, the third one only with the port numbers.
\<close>

text\<open>
  Definitions of the subnets 
\<close>

definition
  PC :: "(adr\<^sub>i\<^sub>p net)" where
  "PC = {{(a,b). a = 3}}"
  
definition
  Internet :: "adr\<^sub>i\<^sub>p net" where
  "Internet = {{(a,b). \<not> (a = 3)}}"

definition
  not_in_same_net :: "(adr\<^sub>i\<^sub>p,DummyContent) packet \<Rightarrow> bool" where
  "not_in_same_net x = ((src x \<sqsubset> PC \<longrightarrow> dest x \<sqsubset> Internet) \<and> (src x \<sqsubset> Internet \<longrightarrow> dest x \<sqsubset> PC))" 
  
text \<open>
  Definitions of the policies 
\<close>

definition
  strictPolicy :: "(adr\<^sub>i\<^sub>p,DummyContent) FWPolicy" where
  "strictPolicy = deny_all ++ allow_all_from_to PC Internet"

definition 
  PortPolicy :: "(adr\<^sub>i\<^sub>p,DummyContent) FWPolicy" where
  "PortPolicy = deny_all ++ allow_from_ports_to {http,smtp,ftp} PC Internet"
  
definition
  PortPolicyBig :: "(adr\<^sub>i\<^sub>p,DummyContent) FWPolicy" where
  "PortPolicyBig = deny_all ++ 
                 allow_from_port_to http PC Internet ++ 
                 allow_from_port_to smtp PC Internet ++ 
                 allow_from_port_to ftp PC Internet"
  
lemmas policyLemmas = strictPolicy_def PortPolicy_def PC_def
  Internet_def PortPolicyBig_def src_def dest_def
  adr\<^sub>i\<^sub>pLemmas content_def
  PortCombinators in_subnet_def PortPolicyBig_def id_def
  
declare Ports [simp add]
  
definition wellformed_packet::"(adr\<^sub>i\<^sub>p,DummyContent) packet \<Rightarrow> bool" where
  "wellformed_packet p = (content p = data)"
  
end
