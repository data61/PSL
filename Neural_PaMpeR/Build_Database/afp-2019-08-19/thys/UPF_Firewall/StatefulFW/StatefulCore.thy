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

subsection \<open>Stateful Protocols: Foundations\<close>
theory 
  StatefulCore 
  imports 
    "../PacketFilter/PacketFilter" 
    LTL_alike
begin

text\<open>
  The simple system of a stateless packet filter is not enough to model all common real-world 
  scenarios. Some protocols need further actions in order to be secured.  A prominent example is 
  the File Transfer Protocol (FTP), which is a popular means to move files across the Internet. 
  It behaves quite differently from most other application layer protocols as it uses a two-way 
  connection establishment which opens a dynamic port. A stateless packet filter would only have 
  the possibility to either always open all the possible dynamic ports or not to allow that 
  protocol at all. Neither of these options is satisfactory. In the first case, all ports above
  1024 would have to be opened which introduces a big security hole in the system, in the second 
  case users wouldn't be very happy. A firewall which tracks the state of the TCP connections on 
  a system does not help here either, as the opening and closing of the ports takes place on the 
  application layer. Therefore, a firewall needs to have some knowledge of the application 
  protocols being run and track the states of these protocols. We next model this behaviour.

  The key point of our model is the idea that a policy remains the same as before: a mapping from 
  packet to packet out. We still specify for every packet, based on its source and destination 
  address, the expected action.  The only thing that changes now is that this mapping is allowed 
  to change over time. This indicates that our test data will not consist of single packets but 
  rather of sequences thereof. 

  At first we hence need a state. It is a tuple from some memory to be refined later and the 
  current policy. 
\<close>
  
type_synonym ('\<alpha>,'\<beta>,'\<gamma>) FWState = "'\<alpha> \<times> (('\<beta>,'\<gamma>) packet \<mapsto> unit)"  



text\<open>Having a state, we need of course some state transitions. Such
  a transition can happen every time a new packet arrives. State
  transitions can be modelled using a state-exception monad.  
\<close>


type_synonym ('\<alpha>,'\<beta>,'\<gamma>) FWStateTransitionP =
             "('\<beta>,'\<gamma>) packet \<Rightarrow> ((('\<beta>,'\<gamma>) packet \<mapsto> unit) decision, ('\<alpha>,'\<beta>,'\<gamma>) FWState) MON\<^sub>S\<^sub>E"
             
type_synonym ('\<alpha>,'\<beta>,'\<gamma>) FWStateTransition = 
             "(('\<beta>,'\<gamma>) packet \<times> ('\<alpha>,'\<beta>,'\<gamma>) FWState) \<rightharpoonup> ('\<alpha>,'\<beta>,'\<gamma>) FWState"

text\<open>The memory could be modelled as a list of accepted packets.\<close>
type_synonym ('\<beta>,'\<gamma>) history = "('\<beta>,'\<gamma>) packet list"


fun packet_with_id where
  "packet_with_id [] i = []"
|"packet_with_id (x#xs) i = (if id x = i then (x#(packet_with_id xs i)) else (packet_with_id xs i))"


fun ids1 where
 "ids1 i (x#xs) = (id x = i \<and> ids1 i xs)"
|"ids1 i [] = True"
  
fun ids where
  "ids a (x#xs) = (NetworkCore.id x \<in> a \<and> ids a xs)"
|"ids a [] = True"

definition applyPolicy::  "('i \<times> ('i \<mapsto> 'o)) \<mapsto> 'o" 
  where     "applyPolicy = (\<lambda> (x,z). z x)"  

end
