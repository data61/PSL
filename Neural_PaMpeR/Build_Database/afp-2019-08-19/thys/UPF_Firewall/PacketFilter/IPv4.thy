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

subsection \<open>Formalizing IPv4 Addresses\<close>
theory 
  IPv4
  imports 
    NetworkCore
begin
text\<open>
  A theory describing IPv4 addresses with ports. The host address is a four-tuple of Integers, 
  the port number is a single Integer.
\<close>

type_synonym 
  ipv4_ip = "(int \<times> int \<times> int \<times> int)" 

type_synonym 
  port    =  "int"

type_synonym 
  ipv4    =  "(ipv4_ip \<times> port)"

overloading src_port_ipv4 \<equiv> "src_port :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port" 
begin 
definition 
  "src_port_ipv4 (x::(ipv4,'\<beta>) packet) \<equiv> (snd o fst o snd) x"
end 

overloading dest_port_ipv4 \<equiv> "dest_port :: ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port"
begin
definition 
  "dest_port_ipv4  (x::(ipv4,'\<beta>) packet) \<equiv> (snd o fst o snd o snd) x"
end 

overloading subnet_of_ipv4 \<equiv> "subnet_of :: '\<alpha>::adr \<Rightarrow> '\<alpha> net"
begin 
definition
  "subnet_of_ipv4 (x::ipv4) \<equiv> {{(a,b::int). a =  fst x}}" 
end

definition subnet_of_ip :: "ipv4_ip \<Rightarrow> ipv4 net"
  where "subnet_of_ip ip = {{(a,b). (a = ip)}}"

lemma src_port: "src_port (a,(x::ipv4),d,e) = snd x"
  by (simp add: src_port_ipv4_def in_subnet)

lemma dest_port: "dest_port (a,d,(x::ipv4),e) = snd x"
  by (simp add: dest_port_ipv4_def in_subnet)


lemmas IPv4Lemmas = src_port dest_port src_port_ipv4_def dest_port_ipv4_def

end
