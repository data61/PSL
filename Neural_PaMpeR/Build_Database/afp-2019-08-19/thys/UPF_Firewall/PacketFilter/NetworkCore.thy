(*****************************************************************************
 * Copyright (c) 2005-2010 ETH Zurich, Switzerland
 *               2008-2015 Achim D. Brucker, Germany
 *               2009-2017 Université Paris-Sud, France
 *               2015-2017 The University of Sheffield, UK
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

subsection\<open>Packets and Networks\<close>
theory 
  NetworkCore
  imports 
    Main
begin

text\<open>
  In networks based e.g. on TCP/IP, a message from A to B is encapsulated in  \emph{packets}, which 
  contain the content of the message and routing information. The routing information mainly 
  contains its source and its destination address.
  
  In the case of stateless packet filters, a firewall bases its decision upon this routing 
  information and, in the stateful case, on the content. Thus, we model a packet as a four-tuple of 
  the mentioned elements, together with an id field.
\<close>

text\<open>The ID is an integer:\<close>
type_synonym id = int

text\<open>
  To enable different representations of addresses (e.g. IPv4 and IPv6, with or without ports), 
  we model them as an unconstrained type class and directly provide several instances: 
\<close>
class adr

type_synonym    '\<alpha> src  = "'\<alpha>"
type_synonym    '\<alpha> dest = "'\<alpha>"

instance int ::adr ..
instance nat ::adr ..

instance "fun" :: (adr,adr) adr ..
instance prod :: (adr,adr) adr ..

text\<open>
  The content is also specified with an unconstrained generic type: 
\<close>
type_synonym '\<beta> content = "'\<beta>"

text \<open>
  For applications where the concrete representation of the content field does not matter (usually 
  the case for stateless packet filters), we provide a default type which can be used in those
  cases: 
\<close>
 
datatype DummyContent = data

text\<open>Finally, a packet is:\<close>

type_synonym ('\<alpha>,'\<beta>) packet = "id \<times> '\<alpha> src \<times> '\<alpha> dest \<times> '\<beta> content"

text\<open>
  Protocols (e.g. http) are not modelled explicitly. In the case of stateless packet filters, they 
  are only visible by the destination port of a packet, which are modelled as part of the address. 
  Additionally, stateful firewalls often determine the protocol by the content of a packet. 
\<close>

definition src :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<alpha>"
  where "src  = fst o snd "

text\<open>
  Port numbers (which are part of an address) are also modelled in a generic way. The integers and 
  the naturals are typical representations of port numbers. 
\<close>

class port

instance int ::port ..
instance nat :: port ..
instance "fun" :: (port,port) port ..
instance "prod" :: (port,port) port ..

text\<open>
  A packet therefore has two parameters, the first being the address, the second the content. For 
  the sake of simplicity, we do not allow to have a different address representation format for the 
  source and the destination of a packet. 
  
  To access the different parts of a packet directly, we define a couple of projectors: 
\<close>
definition id :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> id" 
  where "id = fst"

definition dest :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<alpha> dest"
  where "dest = fst o snd o snd"

definition content :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<beta> content"
  where "content = snd o snd o snd"

datatype protocol = tcp | udp

lemma either: "\<lbrakk>a \<noteq> tcp;a \<noteq> udp\<rbrakk> \<Longrightarrow> False"
  by (case_tac "a",simp_all)

lemma either2[simp]: "(a \<noteq> tcp) = (a = udp)"
  by (case_tac "a",simp_all)                 

lemma either3[simp]: "(a \<noteq> udp) = (a = tcp)"
  by (case_tac "a",simp_all)                

text\<open>
  The following two constants give the source and destination port number of a packet. Address 
  representations using port numbers need to provide a definition for these types.
\<close>

consts src_port :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port" 
consts dest_port :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> '\<gamma>::port"
consts src_protocol :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> protocol"
consts dest_protocol :: "('\<alpha>::adr,'\<beta>) packet \<Rightarrow> protocol"

text\<open>A subnetwork (or simply a network) is a set of sets of addresses.\<close>

type_synonym '\<alpha> net = "'\<alpha> set set"
 
text\<open>The relation {in\_subnet} (\<open>\<sqsubset>\<close>) checks if an address is in a specific network.\<close>

definition
  in_subnet :: "'\<alpha>::adr \<Rightarrow> '\<alpha> net \<Rightarrow> bool"  (infixl "\<sqsubset>" 100)  where
  "in_subnet a S = (\<exists> s \<in> S. a \<in> s)"


text\<open>The following lemmas will be useful later.\<close>

lemma in_subnet: 
  "(a, e) \<sqsubset> {{(x1,y). P x1 y}} = P a e"
  by (simp add: in_subnet_def)

lemma src_in_subnet: 
  "src(q,(a,e),r,t) \<sqsubset> {{(x1,y). P x1 y}} = P a e"
  by (simp add: in_subnet_def in_subnet src_def)

lemma dest_in_subnet: 
  "dest (q,r,((a),e),t) \<sqsubset> {{(x1,y). P x1 y}} = P a e"
  by (simp add: in_subnet_def in_subnet dest_def)

text\<open>
  Address models should provide a definition for the following constant, returning a network 
  consisting of the input address only. 
\<close>

consts subnet_of :: "'\<alpha>::adr \<Rightarrow> '\<alpha> net"

lemmas packet_defs = in_subnet_def id_def content_def src_def dest_def

end
