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

subsection \<open>Policy Combinators with Ports\<close>
theory 
  PortCombinators
  imports 
    PolicyCombinators
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
  allow_all_from_port :: "'\<alpha>::adr net \<Rightarrow> ('\<gamma>::port) \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_port src_net s_port = {pa. src_port pa = s_port} \<triangleleft> allow_all_from src_net"
  
definition 
  deny_all_from_port    :: "'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_port src_net s_port  = {pa. src_port pa = s_port} \<triangleleft> deny_all_from src_net "

definition
  allow_all_to_port    :: "'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_to_port dest_net d_port  = {pa. dest_port pa = d_port} \<triangleleft> allow_all_to dest_net"

definition 
  deny_all_to_port :: "'\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_to_port dest_net d_port = {pa. dest_port pa = d_port} \<triangleleft> deny_all_to dest_net"

definition
  allow_all_from_port_to:: "'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where
    "allow_all_from_port_to src_net s_port dest_net   
       = {pa. src_port pa = s_port} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  deny_all_from_port_to::"'\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where
    "deny_all_from_port_to src_net s_port dest_net  
      = {pa. src_port pa = s_port} \<triangleleft> deny_all_from_to src_net dest_net "

definition
  allow_all_from_port_to_port::"'\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow>
                              (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_port_to_port src_net s_port dest_net d_port = 
      {pa. dest_port pa = d_port} \<triangleleft> allow_all_from_port_to src_net s_port dest_net"

definition 
  deny_all_from_port_to_port :: "'\<alpha>::adr net \<Rightarrow>  '\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                                 '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_port_to_port src_net s_port dest_net d_port = 
     {pa. dest_port pa = d_port} \<triangleleft> deny_all_from_port_to src_net s_port dest_net"
  
definition 
  allow_all_from_to_port    :: "'\<alpha>::adr net  \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                                '\<gamma>::port \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_all_from_to_port src_net dest_net d_port =  
    {pa. dest_port pa = d_port} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  deny_all_from_to_port    :: "'\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<gamma>::port \<Rightarrow>
                               (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_all_from_to_port src_net dest_net d_port = 
                                 {pa. dest_port pa = d_port} \<triangleleft> deny_all_from_to src_net dest_net"

definition 
  allow_from_port_to :: "'\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "allow_from_port_to port src_net dest_net =   
            {pa. src_port pa = port} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  deny_from_port_to :: "'\<gamma>::port \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "deny_from_port_to port src_net dest_net =   
            {pa. src_port pa = port} \<triangleleft> deny_all_from_to src_net dest_net"

definition 
  allow_from_to_port :: "'\<gamma>::port  \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "allow_from_to_port port src_net dest_net =   
         {pa. dest_port pa = port} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  deny_from_to_port :: "'\<gamma>::port  \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where 
    "deny_from_to_port port src_net dest_net =   
         {pa. dest_port pa = port} \<triangleleft> deny_all_from_to src_net dest_net"

definition 
  allow_from_ports_to :: "'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_from_ports_to ports src_net dest_net =   
         {pa. src_port pa \<in> ports} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  allow_from_to_ports :: "'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "allow_from_to_ports ports src_net dest_net =   
        {pa. dest_port pa \<in> ports} \<triangleleft> allow_all_from_to src_net dest_net"

definition 
  deny_from_ports_to :: "'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_from_ports_to ports src_net dest_net =   
         {pa. src_port pa \<in> ports} \<triangleleft> deny_all_from_to src_net dest_net"

definition 
  deny_from_to_ports :: "'\<gamma>::port set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> '\<alpha>::adr net \<Rightarrow>
                          (('\<alpha>,'\<beta>) packet \<mapsto> unit)" where
  "deny_from_to_ports ports src_net dest_net =   
        {pa. dest_port pa \<in> ports} \<triangleleft> deny_all_from_to src_net dest_net"
  
definition
  allow_all_from_port_tos:: "'\<alpha>::adr net \<Rightarrow> ('\<gamma>::port) set \<Rightarrow> '\<alpha>::adr net \<Rightarrow> (('\<alpha>,'\<beta>) packet \<mapsto> unit)"
  where
    "allow_all_from_port_tos src_net s_port dest_net   
       = {pa. dest_port pa \<in>  s_port} \<triangleleft> allow_all_from_to src_net dest_net"

text\<open>
  As before, we put all the rules into one lemma called PortCombinators to ease  writing later.  
\<close> 

lemmas PortCombinatorsCore = 
  allow_all_from_port_def deny_all_from_port_def allow_all_to_port_def
  deny_all_to_port_def allow_all_from_to_port_def
  deny_all_from_to_port_def
  allow_from_ports_to_def allow_from_to_ports_def
  deny_from_ports_to_def deny_from_to_ports_def
  allow_all_from_port_to_def deny_all_from_port_to_def
  allow_from_port_to_def allow_from_to_port_def deny_from_to_port_def
  deny_from_port_to_def allow_all_from_port_tos_def

lemmas PortCombinators = PortCombinatorsCore PolicyCombinators

end
