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

subsection \<open>The File Transfer Protocol (ftp)\<close>
theory 
  FTP
  imports 
    StatefulCore 
begin

subsubsection\<open>The protocol syntax\<close>
text\<open>
  The File Transfer Protocol FTP is a well known example of a protocol which uses dynamic ports and
  is therefore a natural choice to use as an example for our model. 

  We model only a simplified version of the FTP protocol over IntegerPort addresses, still 
  containing all messages that matter for our purposes. It consists of the following four messages:
  \begin{enumerate} 
    \item \<open>init\<close>: The client contacts the server indicating
          his wish to get some data.
    \item \<open>ftp_port_request p\<close>: The client, usually after having
          received an acknowledgement of the server, indicates a port
          number on which he wants to receive the data.
    \item \<open>ftp_ftp_data\<close>: The server sends the requested data over
          the new channel. There might be an arbitrary number of such
          messages, including zero.
      \item \<open>ftp_close\<close>: The client closes the connection. The
          dynamic port gets closed again.
  \end{enumerate}

  The content field of a packet therefore now consists of either one of those four messages or a 
  default one.  
\<close>

datatype  msg = ftp_init  | ftp_port_request port | ftp_data | ftp_close | ftp_other

text\<open>
  We now also make use of the ID field of a packet. It is used as session ID and we make the 
  assumption that they are all unique among different protocol runs.

  At first, we need some predicates which check if a packet is a specific FTP message and has the 
  correct session ID. 
\<close>

definition
  is_init :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p, msg)packet \<Rightarrow> bool" where 
  "is_init = (\<lambda> i p. (id p = i \<and> content p = ftp_init))"

definition
  is_ftp_port_request :: "id  \<Rightarrow> port \<Rightarrow>(adr\<^sub>i\<^sub>p, msg) packet \<Rightarrow> bool" where
  "is_ftp_port_request = (\<lambda> i port p. (id p = i \<and> content p = ftp_port_request port))" 

definition
  is_ftp_data :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p, msg) packet \<Rightarrow> bool" where
  "is_ftp_data = (\<lambda> i p. (id p = i \<and> content p = ftp_data))"

definition
  is_ftp_close :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p, msg) packet \<Rightarrow> bool" where
  "is_ftp_close = (\<lambda> i p.  (id p = i \<and> content p = ftp_close))"

definition 
  port_open :: "(adr\<^sub>i\<^sub>p, msg) history \<Rightarrow> id \<Rightarrow> port \<Rightarrow> bool" where
  "port_open = (\<lambda> L a p. (not_before (is_ftp_close a) (is_ftp_port_request a p) L))"

definition
  is_ftp_other :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p, msg ) packet \<Rightarrow> bool" where 
  "is_ftp_other = (\<lambda> i p. (id p = i \<and> content p = ftp_other))"

fun are_ftp_other where
  "are_ftp_other i (x#xs) = (is_ftp_other i x \<and> are_ftp_other i xs)"
  |"are_ftp_other i [] = True"

subsubsection\<open>The protocol policy specification\<close>
text\<open>
  We now have to model the respective state transitions. It is important to note that state 
  transitions themselves allow all packets which are allowed by the policy, not only those which 
  are allowed by the protocol. Their only task is to change the policy. As an alternative, we could 
  have decided that they only allow packets which follow the protocol (e.g. come on the correct 
  ports), but this should in our view rather be reflected in the policy itself.

  Of course, not every message changes the policy. In such cases, we do not have to model different 
  cases, one is enough. In our example, only messages 2 and 4 need special transitions. The default 
  says that if the policy accepts the packet, it is added to the history, otherwise it is simply 
  dropped. The policy remains the same in both cases.  
\<close>

fun last_opened_port where
  "last_opened_port i ((j,s,d,ftp_port_request p)#xs) = (if i=j then p else last_opened_port i xs)"
| "last_opened_port i (x#xs) = last_opened_port i xs"
| "last_opened_port x [] = undefined"

fun FTP_STA :: "((adr\<^sub>i\<^sub>p,msg) history, adr\<^sub>i\<^sub>p, msg) FWStateTransition"
  where 
 (* FTP_PORT_REQUEST *)
   "FTP_STA ((i,s,d,ftp_port_request pr), (log, pol)) =
       (if before(Not o is_ftp_close i)(is_init i) log \<and>
           dest_port (i,s,d,ftp_port_request pr) = (21::port) 
        then Some (((i,s,d,ftp_port_request pr)#log, 
                   (allow_from_to_port pr (subnet_of d) (subnet_of s)) \<Oplus> pol))
        else Some (((i,s,d,ftp_port_request pr)#log,pol)))"
 (* FTP_PORT_CLOSURE *) 
  |"FTP_STA ((i,s,d,ftp_close), (log,pol)) = 
       (if   (\<exists> p. port_open log i p) \<and> dest_port (i,s,d,ftp_close) = (21::port) 
        then Some ((i,s,d,ftp_close)#log, 
                   deny_from_to_port (last_opened_port i log) (subnet_of d)(subnet_of s) \<Oplus> pol)
       else  Some (((i,s,d,ftp_close)#log, pol)))"

 (* DEFAULT *)
  |"FTP_STA (p, s) = Some (p#(fst s),snd s)"


fun    FTP_STD :: "((adr\<^sub>i\<^sub>p,msg) history, adr\<^sub>i\<^sub>p, msg) FWStateTransition"
  where "FTP_STD (p,s) = Some s" 

definition TRPolicy ::"    (adr\<^sub>i\<^sub>p,msg)packet \<times> (adr\<^sub>i\<^sub>p,msg)history \<times> ((adr\<^sub>i\<^sub>p,msg)packet \<mapsto> unit)
                        \<mapsto> (unit             \<times> (adr\<^sub>i\<^sub>p,msg)history \<times> ((adr\<^sub>i\<^sub>p,msg)packet \<mapsto> unit))"
  where     "TRPolicy = ((FTP_STA,FTP_STD) \<Otimes>\<^sub>\<nabla> applyPolicy) o (\<lambda>(x,(y,z)).((x,z),(x,(y,z))))"

definition TRPolicy\<^sub>M\<^sub>o\<^sub>n
  where     "TRPolicy\<^sub>M\<^sub>o\<^sub>n = policy2MON(TRPolicy)"

text\<open>If required to contain the policy in the output\<close>
definition TRPolicy\<^sub>M\<^sub>o\<^sub>n' 
  where     "TRPolicy\<^sub>M\<^sub>o\<^sub>n' = policy2MON (((\<lambda>(x,y,z). (z,(y,z))) o_f  TRPolicy ))"

text\<open>
  Now we specify our test scenario in more detail. We could test:
  \begin{itemize}
    \item one correct FTP-Protocol run,
    \item several runs after another,
    \item several runs interleaved,
    \item an illegal protocol run, or
    \item several illegal protocol runs.
  \end{itemize}

  We only do the the simplest case here: one correct protocol run.
\<close>

text\<open>
  There are four different states which are modelled as a datatype.
\<close>
datatype ftp_states = S0 | S1 | S2 | S3

text\<open>
  The following constant is \<open>True\<close> for all sets which are correct FTP runs for a given 
  source and destination address, ID, and data-port number.  
\<close>


fun
  is_ftp :: "ftp_states \<Rightarrow> adr\<^sub>i\<^sub>p  \<Rightarrow> adr\<^sub>i\<^sub>p \<Rightarrow> id \<Rightarrow> port \<Rightarrow>
            (adr\<^sub>i\<^sub>p,msg) history \<Rightarrow> bool"
  where
    "is_ftp H c s i p [] = (H=S3)"
  |"is_ftp H c s i p (x#InL) = (snd s = 21  \<and>((\<lambda> (id,sr,de,co). (((id = i \<and> (
   (H=ftp_states.S2 \<and> sr = c \<and> de = s \<and> co = ftp_init \<and> is_ftp S3 c s i p InL) \<or> 
   (H=ftp_states.S1 \<and> sr = c \<and> de = s \<and> co = ftp_port_request p \<and>  is_ftp S2 c s i p InL) \<or> 
   (H=ftp_states.S1 \<and> sr = s \<and> de = (fst c,p) \<and> co= ftp_data \<and> is_ftp S1 c s i p InL) \<or> 
   (H=ftp_states.S0 \<and> sr = c \<and> de = s \<and> co = ftp_close  \<and> is_ftp S1 c s i p InL) ))))) x))"



definition  is_single_ftp_run :: "adr\<^sub>i\<^sub>p src \<Rightarrow> adr\<^sub>i\<^sub>p dest \<Rightarrow> id \<Rightarrow> port  \<Rightarrow> (adr\<^sub>i\<^sub>p,msg) history set" 
  where      "is_single_ftp_run s d i p = {x. (is_ftp S0 s d i p x)}"

text\<open>
  The following constant then returns a set of all the historys which denote such a normal 
  behaviour FTP run, again for a given source and destination address, ID, and data-port. 

  The following definition returns the set of all possible interleaving of two correct FTP protocol 
  runs. 
\<close>
definition 
  ftp_2_interleaved :: "adr\<^sub>i\<^sub>p src \<Rightarrow> adr\<^sub>i\<^sub>p dest \<Rightarrow> id \<Rightarrow> port  \<Rightarrow>
               adr\<^sub>i\<^sub>p src \<Rightarrow> adr\<^sub>i\<^sub>p dest \<Rightarrow> id \<Rightarrow> port  \<Rightarrow>
            (adr\<^sub>i\<^sub>p,msg) history set" where
  "ftp_2_interleaved s1 d1 i1 p1 s2 d2 i2 p2 = 
      {x. (is_ftp S0 s1 d1 i1 p1 (packet_with_id x i1)) \<and>
          (is_ftp S0 s2 d2 i2 p2 (packet_with_id x i2))}"

lemma subnetOf_lemma: "(a::int) \<noteq> (c::int) \<Longrightarrow> \<forall>x\<in>subnet_of (a, b::port). (c, d) \<notin> x"
  by (rule ballI, simp add: subnet_of_int_def)

lemma subnetOf_lemma2: " \<forall>x\<in>subnet_of (a::int, b::port). (a, b) \<in>  x"
  by (rule ballI, simp add: subnet_of_int_def)

lemma subnetOf_lemma3: "(\<exists>x. x \<in> subnet_of (a::int, b::port))"
  by (rule exI,  simp add: subnet_of_int_def)

lemma subnetOf_lemma4: "\<exists>x\<in>subnet_of (a::int, b::port). (a, c::port) \<in> x"
  by (rule bexI, simp_all add: subnet_of_int_def)

lemma port_open_lemma: "\<not> (Ex (port_open [] (x::port)))"
  by (simp add: port_open_def)

lemmas FTPLemmas =  TRPolicy_def applyPolicy_def policy2MON_def 
                    Let_def in_subnet_def src_def
                    dest_def  subnet_of_int_def 
                    is_init_def p_accept_def port_open_def is_ftp_data_def is_ftp_close_def 
                    is_ftp_port_request_def content_def PortCombinators
                    exI subnetOf_lemma subnetOf_lemma2 subnetOf_lemma3 subnetOf_lemma4 
                    NetworkCore.id_def adr\<^sub>i\<^sub>pLemmas port_open_lemma
                    bind_SE_def unit_SE_def valid_SE_def
end
