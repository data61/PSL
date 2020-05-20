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

subsection \<open>DMZ: Integer\<close>
theory 
  DMZInteger
  imports 
    "../../UPF-Firewall"
begin
  
text\<open>This scenario is slightly more complicated than the SimpleDMZ
one, as we now also model specific servers within one
network. Therefore, we cannot use anymore the modelling using
datatype synonym, but only use the one where an address is modelled as an
integer (with ports).

The scenario is the following:

\begin{labeling}{Networks:}
\item[Networks:]
  \begin{itemize}
  \item Intranet (Company intern network)
  \item DMZ (demilitarised zone, servers, etc), containing
     at least two distinct servers ``mail'' and ``web''
  \item Internet (``all others'') 
  \end{itemize}
\item[Policy:]
  \begin{itemize}
  \item allow http(s) from Intranet to Internet
  \item deny all trafic from Internet to Intranet
  \item allo imaps and smtp from intranet to mailserver
  \item allow smtp from Internet to mailserver
  \item allow http(s) from Internet to webserver 
  \item deny everything else
  \end{itemize}
  
\end{labeling}
\<close>

definition
  intranet::"adr\<^sub>i\<^sub>p net" where
  "intranet = {{(a,b) . (a > 1 \<and> a < 4) }}"
definition
  dmz :: "adr\<^sub>i\<^sub>p net" where
  "dmz = {{(a,b). (a > 6) \<and> (a < 11)}}" 
definition
  mail :: "adr\<^sub>i\<^sub>p net" where
  "mail = {{(a,b). a = 7}}"
definition
  web :: "adr\<^sub>i\<^sub>p net" where
  "web = {{(a,b). a = 8 }}"
definition
  internet :: "adr\<^sub>i\<^sub>p net" where
  "internet = {{(a,b).  \<not> ( (a > 1 \<and> a < 4) \<or> (a > 6) \<and> (a < 11))   }}"

definition 
  Intranet_mail_port :: "(adr\<^sub>i\<^sub>p,'b) FWPolicy" where
  "Intranet_mail_port = (allow_from_to_ports {21::port,14} intranet mail)" 
  
definition
  Intranet_Internet_port :: "(adr\<^sub>i\<^sub>p,'b) FWPolicy" where
  "Intranet_Internet_port = allow_from_to_ports {80::port,90} intranet internet"
  
definition
  Internet_web_port :: "(adr\<^sub>i\<^sub>p,'b) FWPolicy" where
  "Internet_web_port = (allow_from_to_ports {80::port,90} internet web)"
  
definition
  Internet_mail_port :: "(adr\<^sub>i\<^sub>p,'b) FWPolicy" where
  "Internet_mail_port =  (allow_all_from_port_to internet (21::port) dmz )"

definition 
  policyPort :: "(adr\<^sub>i\<^sub>p, DummyContent) FWPolicy" where
  "policyPort = deny_all ++ 
                  Intranet_Internet_port ++ 
                  Intranet_mail_port ++  
                  Internet_mail_port ++ 
                  Internet_web_port"

text \<open>
  We only want to create test cases which are sent between the three main networks:
   e.g. not between the mailserver and the dmz. Therefore, the constraint looks as follows. 
\<close>
  
definition
  not_in_same_net :: "(adr\<^sub>i\<^sub>p,DummyContent) packet \<Rightarrow> bool" where
  "not_in_same_net x  =  ((src x \<sqsubset> internet \<longrightarrow> \<not> dest x \<sqsubset> internet) \<and> 
                        (src x \<sqsubset> intranet \<longrightarrow> \<not> dest x \<sqsubset> intranet) \<and> 
                        (src x \<sqsubset> dmz \<longrightarrow> \<not> dest x \<sqsubset> dmz))"
  
lemmas PolicyLemmas =  policyPort_def  dmz_def internet_def intranet_def mail_def web_def 
  Intranet_Internet_port_def Intranet_mail_port_def Internet_web_port_def 
  Internet_mail_port_def src_def dest_def IntegerPort.src_port
  in_subnet_def IntegerPort.dest_port
  
end
