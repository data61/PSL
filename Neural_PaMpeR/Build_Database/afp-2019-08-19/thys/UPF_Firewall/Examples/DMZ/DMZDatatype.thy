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

subsection \<open>DMZ Datatype\<close>
theory 
  DMZDatatype
  imports 
    "../../UPF-Firewall"
begin
  
text\<open>
  This is the fourth scenario, slightly more complicated than the previous one, as we now also 
  model specific servers within one network. Therefore, we could not use anymore the modelling 
  using datatype synonym, but only use the one where an address is modelled as an
  integer (with ports). 

  Just for comparison, this theory is the same scenario with datatype synonym anyway, but with four 
  distinct networks instead of one contained in another. As there is no corresponding network model 
  included, we need to define a custom one.  
\<close>
  
datatype Adr = Intranet | Internet | Mail | Web | DMZ
instance Adr::adr ..
type_synonym port = int
type_synonym Networks = "Adr \<times> port"

definition
  intranet::"Networks net" where
  "intranet = {{(a,b). a= Intranet}}"
definition
  dmz :: "Networks net" where
  "dmz = {{(a,b). a= DMZ}}"
definition
  mail :: "Networks net" where
  "mail = {{(a,b). a=Mail}}" 
definition
  web :: "Networks net" where
  "web = {{(a,b). a=Web}}" 
definition
  internet :: "Networks net" where 
  "internet = {{(a,b). a= Internet}}"
  
definition 
  Intranet_mail_port :: "(Networks ,DummyContent) FWPolicy" where
  "Intranet_mail_port = (allow_from_ports_to {21::port,14} intranet mail)" 
  
definition
  Intranet_Internet_port :: "(Networks,DummyContent) FWPolicy" where
  "Intranet_Internet_port = allow_from_ports_to {80::port,90} intranet internet"
  
definition
  Internet_web_port :: "(Networks,DummyContent) FWPolicy" where
  "Internet_web_port = (allow_from_ports_to {80::port,90} internet web)"
  
definition
  Internet_mail_port :: "(Networks,DummyContent) FWPolicy" where
  "Internet_mail_port =  (allow_all_from_port_to internet (21::port) dmz)"
  
definition 
  policyPort :: "(Networks, DummyContent) FWPolicy" where
  "policyPort = deny_all ++ 
                  Intranet_Internet_port ++ 
                  Intranet_mail_port ++  
                  Internet_mail_port ++ 
                  Internet_web_port"

text \<open>
  We only want to create test cases which are sent between the three main networks: e.g. not 
  between the mailserver and the dmz. Therefore, the constraint looks as follows. \
\<close>

definition
  not_in_same_net :: "(Networks,DummyContent) packet \<Rightarrow> bool" where
  "not_in_same_net x  =  ((src x \<sqsubset> internet \<longrightarrow> \<not> dest x \<sqsubset> internet) \<and> 
                        (src x \<sqsubset> intranet \<longrightarrow> \<not> dest x \<sqsubset> intranet) \<and> 
                        (src x \<sqsubset> dmz \<longrightarrow> \<not> dest x \<sqsubset> dmz))"
  
lemmas PolicyLemmas =   dmz_def internet_def intranet_def mail_def web_def 
  Internet_web_port_def Internet_mail_port_def
  Intranet_Internet_port_def Intranet_mail_port_def 
  src_def dest_def src_port dest_port in_subnet_def
  
  
end
