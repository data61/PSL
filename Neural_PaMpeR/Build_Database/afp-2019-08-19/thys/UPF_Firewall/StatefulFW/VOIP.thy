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

subsection \<open>A simple voice-over-ip model\<close>
theory VOIP
  imports  StatefulCore
begin

text\<open>

  After the FTP-Protocol which was rather simple we show the strength
  of the model with a more current and especially much more
  complicated example, namely Voice over IP (VoIP). VoIP is
  standardized by the ITU-T under the name H.323, which can be seen as
  an "umbrella standard" which aggregates standards for multimedia
  conferencing over packet-based networks. H.323 poses many problems
  to firewalls. These problems include:
  \begin{itemize}
    \item An H.323 call is made up of many different simultaneous
          connections.
    \item Most connections are made to dynamic ports.
    \item The addresses and port numbers are exchanged within
          the data stream of the next higher connection. 
    \item Calls can be initiated from outside the firewall.
  \end{itemize}

  Again we only consider a simplified VoIP scenario with the following
  seven messages which are grouped into four subprotocols:
  \begin{itemize}
    \item Registration and Admission (H.225, port 1719): The caller
          contacts its gatekeeper with a call request. The gatekeeper
          either rejects or confirms the request, returning the
          address of the callee in the latter case.
  
          \begin{itemize}
            \item Admission Request (ARQ)
            \item Admission Reject (ARJ)
            \item Admission Confirm (ACF) \<open>'a\<close>
          \end{itemize}
    \item Call Signaling (Q.931, port 1720) The caller and the callee 
          agree on the dynamic ports over which the call will take 
          place.  
          \begin{itemize}
            \item Setup \<open>port\<close>
            \item Connect \<open>port\<close>
          \end{itemize}
    \item Stream (dynamic ports). The call itself. In reality, several 
          connections are used here.
    \item Fin (port 1720).
  \end{itemize}


  The two main differences to FTP are:
  \begin{itemize}
    \item In VoIP, we deal with three different entities: the caller, 
          the callee, and the gatekeeper.
    \item We do not know in advance which entity will close the 
          connection.
  \end{itemize}
  
  We model the protocol as seen from a firewall at the caller, namely
  we are not interested in the messages from the callee to its
  gatekeeper. Incoming calls are not modelled either, they would
  require a different set of state transitions.  
\<close>


text\<open>
  The content of a packet now consists of one of the seven messages or
  a default one. It is parameterized with the type of the address that
  the gatekeeper returns.
\<close>


datatype 'a voip_msg =  ARQ
                     | ACF 'a 
                     | ARJ
                     | Setup port 
                     | Connect port 
                     | Stream 
                     | Fin 
                     | other
text\<open>
  As before, we need operators which check if a packet contains a
  specific content and ID, respectively if such a packet has appeared
  in the trace. 
\<close>


definition
  is_arq :: "NetworkCore.id \<Rightarrow> ('a::adr, 'b voip_msg) packet \<Rightarrow> bool" where 
  "is_arq i p = (NetworkCore.id p = i \<and> content p = ARQ)"


definition
  is_fin :: "id \<Rightarrow> ('a::adr, 'b voip_msg) packet \<Rightarrow> bool" where
  "is_fin i p = (id p = i \<and> content p = Fin)"

definition
  is_connect :: "id \<Rightarrow> port \<Rightarrow> ('a::adr, 'b voip_msg) packet \<Rightarrow> bool" where
  "is_connect i port p = (id p = i \<and> content p = Connect port)"

definition
  is_setup :: "id \<Rightarrow> port \<Rightarrow> ('a::adr, 'b voip_msg) packet \<Rightarrow> bool" where
  "is_setup i port p = (id p = i \<and> content p = Setup port)"


text\<open>
  We need also an operator \<open>ports_open\<close> to get access to the two
  dynamic ports.
\<close>
definition 
  ports_open :: "id \<Rightarrow> port \<times> port \<Rightarrow> (adr\<^sub>i\<^sub>p, 'a voip_msg) history \<Rightarrow> bool" where
  "ports_open i p L = ((not_before (is_fin i) (is_setup i (fst p)) L) \<and> 
                             not_before (is_fin i) (is_connect i (snd p)) L)"




text\<open>
  As we do not know which entity closes the connection, we define an
  operator which checks if the closer is the caller.
\<close>
fun 
  src_is_initiator :: "id \<Rightarrow> adr\<^sub>i\<^sub>p \<Rightarrow> (adr\<^sub>i\<^sub>p,'b voip_msg) history \<Rightarrow> bool" where
 "src_is_initiator i a [] = False"
|"src_is_initiator i a (p#S) =  (((id p = i) \<and> 
                                            (\<exists> port. content p = Setup port) \<and> 
                                            ((fst (src p) = fst a))) \<or>
                                        (src_is_initiator i a S))"



text\<open>
  The first state transition is for those messages which do not change
  the policy. In this scenario, this only happens for the Stream
  messages. 
\<close>

definition subnet_of_adr where
 "subnet_of_adr x = {{(a,b). a = x}}"

fun VOIP_STA ::
  "((adr\<^sub>i\<^sub>p,address voip_msg) history, adr\<^sub>i\<^sub>p, address voip_msg) FWStateTransition"
where
 
(*
    If the policy accepts the ARQ packet, we have to assure that we
    will accept the returning packet of the gatekeeper (on port 1719)
*)
 "VOIP_STA ((a,c,d,ARQ), (InL, policy)) =
          Some (((a,c,d, ARQ)#InL, 
  (allow_from_to_port (1719::port)(subnet_of d) (subnet_of c)) \<Oplus> policy))"
(*
  And if the gatekeeper answers, no matter if it's a good or bad
  answer, we can close the channel again. If the answer was positive
  (ACF), we allow the caller to contact the callee and get contacted
  by him over port 1720. 
*)
|"VOIP_STA ((a,c,d,ARJ), (InL, policy)) = 
                  (if (not_before (is_fin a) (is_arq a) InL)
                            then Some (((a,c,d,ARJ)#InL, 
                 deny_from_to_port (14::port) (subnet_of c) (subnet_of d) \<Oplus> policy))
                            else Some (((a,c,d,ARJ)#InL,policy)))"

|"VOIP_STA ((a,c,d,ACF callee), (InL, policy)) =
              Some (((a,c,d,ACF callee)#InL,   
  allow_from_to_port (1720::port) (subnet_of_adr callee) (subnet_of d) \<Oplus>
  allow_from_to_port (1720::port) (subnet_of d) (subnet_of_adr callee) \<Oplus>
  deny_from_to_port (1719::port) (subnet_of d) (subnet_of c) \<Oplus> 
  policy))"

(*
  In the Setup message, the caller specifies the port on which he
  wants the connection to take place so we need to open it for
  incoming VoIP messages. 
*)

|"VOIP_STA ((a,c,d, Setup port), (InL, policy)) =
           Some (((a,c,d,Setup port)#InL,  
 allow_from_to_port port (subnet_of d) (subnet_of c) \<Oplus> policy))"
 
(*
  The same happens after the Connect message of the callee. 
*)
 |"VOIP_STA ((a,c,d, Connect port), (InL, policy)) =
                 Some (((a,c,d,Connect port)#InL, 
   allow_from_to_port port (subnet_of d) (subnet_of c)  \<Oplus> policy))"
                
(*
  In the FIN message, we have to close all the previously opened
  ports. This works as in the FTP close message, only a little bit
  more complicated. 
*)
|"VOIP_STA ((a,c,d,Fin), (InL,policy)) = 
       (if \<exists> p1 p2. ports_open a (p1,p2) InL then (
           (if src_is_initiator a c InL
           then (Some (((a,c,d,Fin)#InL,  
(deny_from_to_port (1720::int) (subnet_of c) (subnet_of d) ) \<Oplus>
(deny_from_to_port (snd (SOME p. ports_open a p InL))
                   (subnet_of c) (subnet_of d)) \<Oplus>
(deny_from_to_port (fst (SOME p. ports_open a p InL))
                    (subnet_of d) (subnet_of c)) \<Oplus> policy)))

           else (Some (((a,c,d,Fin)#InL,  
(deny_from_to_port (1720::int) (subnet_of c) (subnet_of d) ) \<Oplus>
(deny_from_to_port (fst (SOME p. ports_open a p InL))
                   (subnet_of c) (subnet_of d)) \<Oplus>
(deny_from_to_port (snd (SOME p. ports_open a p InL))
                    (subnet_of d) (subnet_of c)) \<Oplus> policy)))))

       else
           (Some (((a,c,d,Fin)#InL,policy))))"
 

(* The default action for all other packets *)
| "VOIP_STA (p, (InL, policy)) = 
                          Some ((p#InL,policy)) "

fun VOIP_STD  where
 "VOIP_STD (p,s) = Some s"


definition VOIP_TRPolicy where 
 "VOIP_TRPolicy = policy2MON ( 
   ((VOIP_STA,VOIP_STD) \<Otimes>\<^sub>\<nabla> applyPolicy) o (\<lambda> (x,(y,z)). ((x,z),(x,(y,z)))))"

text\<open>
  For a full protocol run, six states are needed. 
\<close>
datatype voip_states = S0 | S1 | S2 | S3 | S4 | S5

text\<open>
  The constant \<open>is_voip\<close> checks if a trace corresponds to a
  legal VoIP protocol, given the IP-addresses of the three entities,
  the ID, and the two dynamic ports. 
\<close>

fun is_voip :: "voip_states \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> id \<Rightarrow> port \<Rightarrow>
                port \<Rightarrow>  (adr\<^sub>i\<^sub>p, address voip_msg) history \<Rightarrow> bool"
where
 "is_voip H s d g i p1 p2 [] = (H = S5)"
|"is_voip H s d g i p1 p2 (x#InL) = 
  (((\<lambda> (id,sr,de,co). 
 (((id = i \<and> 
(H = S4 \<and> ((sr = (s,1719) \<and> de = (g,1719) \<and> co = ARQ \<and>
    is_voip S5 s d g i p1 p2 InL))) \<or>
(H = S0 \<and> sr = (g,1719) \<and> de = (s,1719) \<and> co = ARJ \<and>
    is_voip S4 s d g i p1 p2 InL) \<or>
(H = S3 \<and> sr = (g,1719) \<and> de = (s,1719) \<and> co = ACF d \<and>
    is_voip S4 s d g i p1 p2 InL) \<or>
(H = S2 \<and> sr = (s,1720) \<and> de = (d,1720) \<and> co = Setup p1 \<and>
    is_voip S3 s d g i p1 p2 InL) \<or>
(H = S1 \<and> sr = (d,1720) \<and> de = (s,1720) \<and> co = Connect p2 \<and>
    is_voip S2 s d g i p1 p2 InL) \<or>
(H = S1 \<and> sr = (s,p1) \<and> de = (d,p2) \<and> co = Stream \<and>
    is_voip S1 s d g i p1 p2 InL) \<or>
(H = S1 \<and> sr = (d,p2) \<and> de = (s,p1) \<and> co = Stream \<and>
    is_voip S1 s d g i p1 p2 InL) \<or>
(H = S0 \<and> sr = (d,1720) \<and> de = (s,1720) \<and> co = Fin \<and>
    is_voip S1 s d g i p1 p2 InL) \<or>
(H = S0 \<and> sr = (s,1720) \<and> de = (d,1720) \<and> co = Fin \<and>
    is_voip S1 s d g i p1 p2 InL)))))) x)"
 

text\<open>
  Finally, \<open>NB_voip\<close> returns the set of protocol traces which
  correspond to a correct protocol run given the three addresses, the
  ID, and the two dynamic ports.
\<close>
definition 
  NB_voip :: "address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> id  \<Rightarrow> port \<Rightarrow> port \<Rightarrow>
              (adr\<^sub>i\<^sub>p, address voip_msg) history set" where
  "NB_voip s d g i p1 p2= {x. (is_voip S0 s d g i p1 p2 x)}"

end
