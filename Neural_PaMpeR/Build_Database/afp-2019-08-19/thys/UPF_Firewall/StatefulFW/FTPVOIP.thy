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

subsection \<open>FTP and VoIP Protocol\<close>
theory  
  FTPVOIP
  imports 
    FTP_WithPolicy VOIP
begin

datatype  ftpvoip =  ARQ
                     | ACF int 
                     | ARJ
                     | Setup port 
                     | Connect port 
                     | Stream 
                     | Fin 
                     | ftp_init 
                     | ftp_port_request port 
                     | ftp_data 
                     | ftp_close 
                     | other


text\<open>
  We now also make use of the ID field of a packet. It is used as session ID and we make the 
  assumption that they are all unique among different protocol runs.

  At first, we need some predicates which check if a packet is a specific FTP message and has 
  the correct session ID. 
\<close>
 
definition
  FTPVOIP_is_init :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p,  ftpvoip ) packet \<Rightarrow> bool" where 
  "FTPVOIP_is_init = (\<lambda> i p. (id p = i \<and> content p = ftp_init))"

definition
  FTPVOIP_is_port_request :: "id  \<Rightarrow> port \<Rightarrow>(adr\<^sub>i\<^sub>p,  ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_port_request = (\<lambda> i port p. (id p = i \<and> content p = ftp_port_request port))" 

definition
  FTPVOIP_is_data :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p,  ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_data = (\<lambda> i p. (id p = i \<and> content p = ftp_data))"

definition
  FTPVOIP_is_close :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p,  ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_close = (\<lambda> i p.  (id p = i \<and> content p = ftp_close))"

definition 
  FTPVOIP_port_open :: "(adr\<^sub>i\<^sub>p,  ftpvoip) history \<Rightarrow> id \<Rightarrow> port \<Rightarrow> bool" where
  "FTPVOIP_port_open = (\<lambda> L a p. (not_before (FTPVOIP_is_close a) (FTPVOIP_is_port_request a p) L))"

definition
  FTPVOIP_is_other :: "id \<Rightarrow> (adr\<^sub>i\<^sub>p,  ftpvoip ) packet \<Rightarrow> bool" where 
  "FTPVOIP_is_other = (\<lambda> i p. (id p = i \<and> content p = other))"

fun FTPVOIP_are_other where
  "FTPVOIP_are_other i (x#xs) = (FTPVOIP_is_other i x \<and> FTPVOIP_are_other i xs)"
 |"FTPVOIP_are_other i [] = True"

fun last_opened_port where
  "last_opened_port i ((j,s,d,ftp_port_request p)#xs) = (if i=j then p else last_opened_port i xs)"
| "last_opened_port i (x#xs) = last_opened_port i xs"
| "last_opened_port x [] = undefined"

fun FTPVOIP_FTP_STA ::
  "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
where 
(* FTP_PORT_REQUEST *)
 "FTPVOIP_FTP_STA ((i,s,d,ftp_port_request pr), (InL, policy)) =
       (if not_before  (FTPVOIP_is_close i) (FTPVOIP_is_init i) InL \<and>
           dest_port (i,s,d,ftp_port_request pr) = (21::port) then
                          Some (((i,s,d,ftp_port_request pr)#InL, policy ++ 
                             (allow_from_to_port pr (subnet_of d) (subnet_of s))))
       else Some (((i,s,d,ftp_port_request pr)#InL,policy)))"
 
  |"FTPVOIP_FTP_STA ((i,s,d,ftp_close), (InL,policy)) = 
       (if   (\<exists> p. FTPVOIP_port_open InL i p) \<and> dest_port (i,s,d,ftp_close) = (21::port) 
        then Some ((i,s,d,ftp_close)#InL, policy ++ 
                 deny_from_to_port (last_opened_port i InL) (subnet_of d) (subnet_of s))
       else  Some (((i,s,d,ftp_close)#InL, policy)))"

(* DEFAULT *)
 |"FTPVOIP_FTP_STA (p, s) = Some (p#(fst s),snd s)"


fun   FTPVOIP_FTP_STD :: "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
where"FTPVOIP_FTP_STD (p,s) = Some s" 
 


definition
   FTPVOIP_is_arq :: "NetworkCore.id \<Rightarrow> ('a::adr, ftpvoip) packet \<Rightarrow> bool" where 
  "FTPVOIP_is_arq i p = (NetworkCore.id p = i \<and> content p = ARQ)"

definition
   FTPVOIP_is_fin :: "id \<Rightarrow> ('a::adr, ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_fin i p = (id p = i \<and> content p = Fin)"

definition
   FTPVOIP_is_connect :: "id \<Rightarrow> port \<Rightarrow> ('a::adr, ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_connect i port p = (id p = i \<and> content p = Connect port)"

definition
   FTPVOIP_is_setup :: "id \<Rightarrow> port \<Rightarrow> ('a::adr, ftpvoip) packet \<Rightarrow> bool" where
  "FTPVOIP_is_setup i port p = (id p = i \<and> content p = Setup port)"


text\<open>
  We need also an operator \<open>ports_open\<close> to get access to the two
  dynamic ports.
\<close>
definition 
   FTPVOIP_ports_open :: "id \<Rightarrow> port \<times> port \<Rightarrow> (adr\<^sub>i\<^sub>p,  ftpvoip) history \<Rightarrow> bool" where
  "FTPVOIP_ports_open i p L = ((not_before (FTPVOIP_is_fin i) (FTPVOIP_is_setup i (fst p)) L) \<and> 
                             not_before (FTPVOIP_is_fin i) (FTPVOIP_is_connect i (snd p)) L)"

text\<open>
  As we do not know which entity closes the connection, we define an
  operator which checks if the closer is the caller.
\<close>
fun 
  FTPVOIP_src_is_initiator :: "id \<Rightarrow> adr\<^sub>i\<^sub>p \<Rightarrow> (adr\<^sub>i\<^sub>p,ftpvoip) history \<Rightarrow> bool" where
 "FTPVOIP_src_is_initiator i a [] = False"
|"FTPVOIP_src_is_initiator i a (p#S) =  (((id p = i) \<and> 
                                            (\<exists> port. content p = Setup port) \<and> 
                                            ((fst (src p) = fst a))) \<or>
                                        (FTPVOIP_src_is_initiator i a S))"

definition FTPVOIP_subnet_of_adr :: "int \<Rightarrow> adr\<^sub>i\<^sub>p net" where
 "FTPVOIP_subnet_of_adr x = {{(a,b). a = x}}"

fun FTPVOIP_VOIP_STA ::
  "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
  where
 "FTPVOIP_VOIP_STA ((a,c,d,ARQ), (InL, policy)) =
          Some (((a,c,d, ARQ)#InL, 
  (allow_from_to_port (1719::port)(subnet_of d) (subnet_of c)) \<Oplus> policy))"

|"FTPVOIP_VOIP_STA ((a,c,d,ARJ), (InL, policy)) = 
                  (if (not_before (FTPVOIP_is_fin a) (FTPVOIP_is_arq a) InL)
                            then Some (((a,c,d,ARJ)#InL, 
                 deny_from_to_port (14::port) (subnet_of c) (subnet_of d) \<Oplus> policy))
                            else Some (((a,c,d,ARJ)#InL,policy)))"

|"FTPVOIP_VOIP_STA ((a,c,d,ACF callee), (InL, policy)) =
              Some (((a,c,d,ACF callee)#InL,   
  allow_from_to_port (1720::port) (subnet_of_adr callee) (subnet_of d) \<Oplus>
  allow_from_to_port (1720::port) (subnet_of d) (subnet_of_adr callee) \<Oplus>
  deny_from_to_port (1719::port) (subnet_of d) (subnet_of c) \<Oplus> 
  policy))"

|"FTPVOIP_VOIP_STA ((a,c,d, Setup port), (InL, policy)) =
           Some (((a,c,d,Setup port)#InL,  
 allow_from_to_port port (subnet_of d) (subnet_of c) \<Oplus> policy))"

 |"FTPVOIP_VOIP_STA ((a,c,d, ftpvoip.Connect port), (InL, policy)) =
                 Some (((a,c,d,ftpvoip.Connect port)#InL, 
   allow_from_to_port port (subnet_of d) (subnet_of c)  \<Oplus> policy))"

|"FTPVOIP_VOIP_STA ((a,c,d,Fin), (InL,policy)) = 
       (if \<exists> p1 p2. FTPVOIP_ports_open a (p1,p2) InL then (
           (if FTPVOIP_src_is_initiator a c InL
           then (Some (((a,c,d,Fin)#InL,  
(deny_from_to_port (1720::int) (subnet_of c) (subnet_of d) ) \<Oplus>
(deny_from_to_port (snd (SOME p. FTPVOIP_ports_open a p InL))
                   (subnet_of c) (subnet_of d)) \<Oplus>
(deny_from_to_port (fst (SOME p. FTPVOIP_ports_open a p InL))
                    (subnet_of d) (subnet_of c)) \<Oplus> policy)))

           else (Some (((a,c,d,Fin)#InL,  
(deny_from_to_port (1720::int) (subnet_of c) (subnet_of d) ) \<Oplus>
(deny_from_to_port (fst (SOME p. FTPVOIP_ports_open a p InL))
                   (subnet_of c) (subnet_of d)) \<Oplus>
(deny_from_to_port (snd (SOME p. FTPVOIP_ports_open a p InL))
                    (subnet_of d) (subnet_of c)) \<Oplus> policy)))))

       else
           (Some (((a,c,d,Fin)#InL,policy))))"
 

(* The default action for all other packets *)
| "FTPVOIP_VOIP_STA (p, (InL, policy)) = 
                          Some ((p#InL,policy)) "

fun FTPVOIP_VOIP_STD ::
  "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
  where 
    "FTPVOIP_VOIP_STD (p,s) = Some s" 

definition FTP_VOIP_STA :: "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
  where 
    "FTP_VOIP_STA = ((\<lambda>(x,x). Some x) \<circ>\<^sub>m ((FTPVOIP_FTP_STA \<Otimes>\<^sub>S FTPVOIP_VOIP_STA o (\<lambda> (p,x). (p,x,x)))))"


definition FTP_VOIP_STD :: "((adr\<^sub>i\<^sub>p, ftpvoip) history, adr\<^sub>i\<^sub>p,  ftpvoip) FWStateTransition"
  where 
    "FTP_VOIP_STD = (\<lambda>(x,x). Some x) \<circ>\<^sub>m ((FTPVOIP_FTP_STD \<Otimes>\<^sub>S FTPVOIP_VOIP_STD o (\<lambda> (p,x). (p,x,x))))"

definition FTPVOIP_TRPolicy where 
 "FTPVOIP_TRPolicy = policy2MON ( 
   (((FTP_VOIP_STA,FTP_VOIP_STD) \<Otimes>\<^sub>\<nabla> applyPolicy) o (\<lambda> (x,(y,z)). ((x,z),(x,(y,z))))))"

lemmas FTPVOIP_ST_simps = Let_def in_subnet_def src_def dest_def
subnet_of_int_def id_def FTPVOIP_port_open_def
 FTPVOIP_is_init_def FTPVOIP_is_data_def FTPVOIP_is_port_request_def FTPVOIP_is_close_def p_accept_def content_def  PortCombinators exI
 NetworkCore.id_def adr\<^sub>i\<^sub>pLemmas

datatype ftp_states2 = FS0 | FS1 | FS2 | FS3
datatype voip_states2 = V0 | V1 | V2 | V3 | V4 | V5

text\<open>
  The constant \<open>is_voip\<close> checks if a trace corresponds to a
  legal VoIP protocol, given the IP-addresses of the three entities,
  the ID, and the two dynamic ports. 
\<close>

fun FTPVOIP_is_voip :: "voip_states2 \<Rightarrow> address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> id \<Rightarrow> port \<Rightarrow>
                port \<Rightarrow>  (adr\<^sub>i\<^sub>p, ftpvoip) history \<Rightarrow> bool"
where
 "FTPVOIP_is_voip H s d g i p1 p2 [] = (H = V5)"
|"FTPVOIP_is_voip H s d g i p1 p2 (x#InL) = 
  (((\<lambda> (id,sr,de,co). 
 (((id = i \<and> 
(H = V4 \<and> ((sr = (s,1719) \<and> de = (g,1719) \<and> co = ARQ \<and>
    FTPVOIP_is_voip V5 s d g i p1 p2 InL))) \<or>
(H = V0 \<and> sr = (g,1719) \<and> de = (s,1719) \<and> co = ARJ \<and>
    FTPVOIP_is_voip V4 s d g i p1 p2 InL) \<or>
(H = V3 \<and> sr = (g,1719) \<and> de = (s,1719) \<and> co = ACF d \<and>
    FTPVOIP_is_voip V4 s d g i p1 p2 InL) \<or>
(H = V2 \<and> sr = (s,1720) \<and> de = (d,1720) \<and> co = Setup p1 \<and>
    FTPVOIP_is_voip V3 s d g i p1 p2 InL) \<or>
(H = V1 \<and> sr = (d,1720) \<and> de = (s,1720) \<and> co = Connect p2 \<and>
    FTPVOIP_is_voip V2 s d g i p1 p2 InL) \<or>
(H = V1 \<and> sr = (s,p1) \<and> de = (d,p2) \<and> co = Stream \<and>
    FTPVOIP_is_voip V1 s d g i p1 p2 InL) \<or>
(H = V1 \<and> sr = (d,p2) \<and> de = (s,p1) \<and> co = Stream \<and>
    FTPVOIP_is_voip V1 s d g i p1 p2 InL) \<or>
(H = V0 \<and> sr = (d,1720) \<and> de = (s,1720) \<and> co = Fin \<and>
    FTPVOIP_is_voip V1 s d g i p1 p2 InL) \<or>
(H = V0 \<and> sr = (s,1720) \<and> de = (d,1720) \<and> co = Fin \<and>
    FTPVOIP_is_voip V1 s d g i p1 p2 InL)))))) x)"
 

text\<open>
  Finally, \<open>NB_voip\<close> returns the set of protocol traces which
  correspond to a correct protocol run given the three addresses, the
  ID, and the two dynamic ports.
\<close>
definition 
  FTPVOIP_NB_voip :: "address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> id  \<Rightarrow> port \<Rightarrow> port \<Rightarrow>
              (adr\<^sub>i\<^sub>p, ftpvoip) history set" where
  "FTPVOIP_NB_voip s d g i p1 p2= {x. (FTPVOIP_is_voip V0 s d g i p1 p2 x)}"

fun
  FTPVOIP_is_ftp :: "ftp_states2 \<Rightarrow> adr\<^sub>i\<^sub>p  \<Rightarrow> adr\<^sub>i\<^sub>p \<Rightarrow> id \<Rightarrow> port \<Rightarrow>
            (adr\<^sub>i\<^sub>p, ftpvoip) history \<Rightarrow> bool"
where
 "FTPVOIP_is_ftp H c s i p [] = (H=FS3)"
|"FTPVOIP_is_ftp H c s i p (x#InL) = (snd s = 21  \<and>((\<lambda> (id,sr,de,co). (((id = i \<and> (
   (H=FS2 \<and> sr = c \<and> de = s \<and> co = ftp_init \<and> FTPVOIP_is_ftp FS3 c s i p InL) \<or> 
   (H=FS1 \<and> sr = c \<and> de = s \<and> co = ftp_port_request p \<and>  FTPVOIP_is_ftp FS2 c s i p InL) \<or> 
   (H=FS1 \<and> sr = s \<and> de = (fst c,p) \<and> co= ftp_data \<and> FTPVOIP_is_ftp FS1 c s i p InL) \<or> 
   (H=FS0 \<and> sr = c \<and> de = s \<and> co = ftp_close  \<and> FTPVOIP_is_ftp FS1 c s i p InL) ))))) x))"

definition 
  FTPVOIP_NB_ftp :: "adr\<^sub>i\<^sub>p src \<Rightarrow> adr\<^sub>i\<^sub>p dest \<Rightarrow> id \<Rightarrow> port  \<Rightarrow> (adr\<^sub>i\<^sub>p, ftpvoip) history set" where
 "FTPVOIP_NB_ftp s d i p = {x. (FTPVOIP_is_ftp FS0 s d i p x)}"

definition 
  ftp_voip_interleaved :: "adr\<^sub>i\<^sub>p src \<Rightarrow> adr\<^sub>i\<^sub>p dest \<Rightarrow> id \<Rightarrow> port  \<Rightarrow>
                           address \<Rightarrow> address \<Rightarrow> address \<Rightarrow> id  \<Rightarrow> port \<Rightarrow> port \<Rightarrow>
                           (adr\<^sub>i\<^sub>p, ftpvoip) history set" 

where
  "ftp_voip_interleaved s1 d1 i1 p1 vs vd vg vi vp1 vp2 = 
      {x. (FTPVOIP_is_ftp FS0 s1 d1 i1 p1 (packet_with_id x i1)) \<and>
          (FTPVOIP_is_voip V0 vs vd vg vi vp1 vp2 (packet_with_id x vi))}"

end
