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

subsection \<open>Integer Addresses with Ports and Protocols\<close>
theory 
  IntegerPort_TCPUDP
  imports 
    NetworkCore
begin

text\<open>A theory describing addresses which are modelled as a pair of Integers - the first being 
       the host address, the second the port number.\<close>

type_synonym 
  address = int

type_synonym 
  port = int 

type_synonym 
  adr\<^sub>i\<^sub>p\<^sub>p = "address \<times> port \<times> protocol" 

instance protocol :: adr ..

overloading src_port_int_TCPUDP \<equiv> "src_port :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port" 
begin 
definition 
  "src_port_int_TCPUDP (x::(adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet)  \<equiv> (fst o snd o fst  o snd) x"
end 

overloading dest_port_int_TCPUDP \<equiv> "dest_port :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port"
begin
definition 
  "dest_port_int_TCPUDP (x::(adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet) \<equiv> (fst o snd o fst o  snd o snd) x"
end 

overloading subnet_of_int_TCPUDP \<equiv> "subnet_of :: '\<alpha>::adr \<Rightarrow> '\<alpha> net"
begin 
definition
  "subnet_of_int_TCPUDP (x::(adr\<^sub>i\<^sub>p\<^sub>p)) \<equiv> {{(a,b,c). a = fst x}}::adr\<^sub>i\<^sub>p\<^sub>p net" 
end

overloading src_protocol_int_TCPUDP \<equiv> "src_protocol :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> protocol"
begin
definition 
  "src_protocol_int_TCPUDP (x::(adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet) \<equiv> (snd o snd o fst o snd) x"
end

overloading dest_protocol_int_TCPUDP \<equiv> "dest_protocol :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> protocol"
begin
definition 
  "dest_protocol_int_TCPUDP (x::(adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet) \<equiv> (snd o snd o fst o snd o snd) x"
end

lemma src_port: "src_port (a,x::adr\<^sub>i\<^sub>p\<^sub>p,d,e) = fst (snd x)"
  by (simp add: src_port_int_TCPUDP_def in_subnet)

lemma dest_port: "dest_port (a,d,x::adr\<^sub>i\<^sub>p\<^sub>p,e) = fst (snd x)"
  by (simp add: dest_port_int_TCPUDP_def in_subnet)

text \<open>Common test constraints:\<close>

definition port_positive :: "(adr\<^sub>i\<^sub>p\<^sub>p,'b) packet \<Rightarrow> bool" where
  "port_positive x = (dest_port x > (0::port))"

definition fix_values :: "(adr\<^sub>i\<^sub>p\<^sub>p,DummyContent) packet \<Rightarrow> bool" where
  "fix_values x =  (src_port x = (1::port) \<and> src_protocol x = udp \<and> content x = data \<and> id x = 1)"


lemmas adr\<^sub>i\<^sub>p\<^sub>pLemmas = src_port dest_port src_port_int_TCPUDP_def dest_port_int_TCPUDP_def 
  src_protocol_int_TCPUDP_def dest_protocol_int_TCPUDP_def subnet_of_int_TCPUDP_def 

lemmas adr\<^sub>i\<^sub>p\<^sub>pTestConstraints = port_positive_def fix_values_def
  
end
