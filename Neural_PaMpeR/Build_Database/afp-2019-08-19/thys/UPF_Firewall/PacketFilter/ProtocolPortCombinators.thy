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

subsection \<open>Policy Combinators with Ports and Protocols\<close>

theory 
  ProtocolPortCombinators
  imports 
    PortCombinators
begin

text\<open>
  This theory defines policy combinators for those network models which 
  have ports. They are provided in addition to the the ones defined in the 
  PolicyCombinators theory. 

  This theory requires from the network models a definition for the two following constants:
  \begin{itemize}
    \item $src\_port :: ('\alpha,'\beta) packet \Rightarrow ('\gamma::port)$
    \item $dest\_port :: ('\alpha,'\beta) packet \Rightarrow ('\gamma::port)$
  \end{itemize}
\<close> 

definition
  allow_all_from_port_prot :: "protocol \<Rightarrow> '\<alpha>::adr net \<Rightarrow> ('\<gamma>::port) \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_port_prot p src_net s_port =   
       {pa. dest_protocol pa = p} \<triangleleft> allow_all_from_port src_net s_port"

definition 
  deny_all_from_port_prot    :: "protocol =>'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_port_prot p src_net s_port =  
       {pa. dest_protocol pa = p} \<triangleleft> deny_all_from_port src_net s_port" 

definition
  allow_all_to_port_prot    :: "protocol =>'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_to_port_prot p dest_net d_port  =  
     {pa. dest_protocol pa = p} \<triangleleft> allow_all_to_port dest_net d_port"

definition 
  deny_all_to_port_prot :: "protocol =>'\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_to_port_prot p dest_net d_port = 
    {pa. dest_protocol pa = p} \<triangleleft> deny_all_to_port dest_net d_port"

definition
  allow_all_from_port_to_prot:: "protocol =>'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where
    "allow_all_from_port_to_prot p src_net s_port dest_net =  
   {pa. dest_protocol pa = p} \<triangleleft> allow_all_from_port_to src_net s_port dest_net"

definition 
  deny_all_from_port_to_prot::"protocol \<Rightarrow> '\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where
    "deny_all_from_port_to_prot p src_net s_port dest_net = 
   {pa. dest_protocol pa = p} \<triangleleft>  deny_all_from_port_to  src_net s_port dest_net"

definition
  allow_all_from_port_to_port_prot::"protocol \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow>
                              (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_port_to_port_prot p src_net s_port dest_net d_port = 
       {pa. dest_protocol pa = p} \<triangleleft>      allow_all_from_port_to_port src_net s_port dest_net d_port "

definition 
  deny_all_from_port_to_port_prot :: "protocol =>'\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                                 '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_port_to_port_prot p src_net s_port dest_net d_port =              
   {pa. dest_protocol pa = p} \<triangleleft>       deny_all_from_port_to_port src_net s_port dest_net d_port"

definition 
  allow_all_from_to_port_prot    :: "protocol =>'\<alpha>::adr net  \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                                '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_to_port_prot p src_net dest_net d_port = 
    {pa. dest_protocol pa = p} \<triangleleft> allow_all_from_to_port src_net dest_net d_port "

definition 
  deny_all_from_to_port_prot    :: "protocol =>'\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow>
                               (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_to_port_prot p src_net dest_net d_port =   
    {pa. dest_protocol pa = p} \<triangleleft> deny_all_from_to_port src_net dest_net d_port"

definition 
  allow_from_port_to_prot :: "protocol =>'\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "allow_from_port_to_prot p port src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> allow_from_port_to port src_net dest_net"

definition 
  deny_from_port_to_prot :: "protocol =>'\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "deny_from_port_to_prot p port src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> deny_from_port_to port src_net dest_net"

definition 
  allow_from_to_port_prot :: "protocol =>'\<gamma>::port  \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "allow_from_to_port_prot p port src_net dest_net =   
  {pa. dest_protocol pa = p} \<triangleleft> allow_from_to_port port src_net dest_net"

definition 
  deny_from_to_port_prot :: "protocol =>'\<gamma>::port  \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "deny_from_to_port_prot p port src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> deny_from_to_port port src_net dest_net"

definition 
  allow_from_ports_to_prot :: "protocol =>'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_from_ports_to_prot p ports src_net dest_net =   
   {pa. dest_protocol pa = p} \<triangleleft> allow_from_ports_to ports src_net dest_net"

definition 
  allow_from_to_ports_prot :: "protocol =>'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_from_to_ports_prot p ports src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> allow_from_to_ports ports src_net dest_net"

definition 
  deny_from_ports_to_prot :: "protocol =>'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_from_ports_to_prot p ports src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> deny_from_ports_to ports src_net dest_net"

definition 
  deny_from_to_ports_prot :: "protocol =>'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_from_to_ports_prot p ports src_net dest_net =   
    {pa. dest_protocol pa = p} \<triangleleft> deny_from_to_ports ports src_net dest_net"

text\<open>As before, we put all the rules into one lemma to ease writing later.\<close> 

lemmas ProtocolCombinatorsCore = 
  allow_all_from_port_prot_def deny_all_from_port_prot_def allow_all_to_port_prot_def
  deny_all_to_port_prot_def allow_all_from_to_port_prot_def
  deny_all_from_to_port_prot_def
  allow_from_ports_to_prot_def allow_from_to_ports_prot_def
  deny_from_ports_to_prot_def deny_from_to_ports_prot_def
  allow_all_from_port_to_prot_def deny_all_from_port_to_prot_def
  allow_from_port_to_prot_def allow_from_to_port_prot_def deny_from_to_port_prot_def
  deny_from_port_to_prot_def 

lemmas ProtocolCombinators = PortCombinators.PortCombinators ProtocolCombinatorsCore

end
