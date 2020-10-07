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

subsection \<open>FTP enriched with a security policy\<close>
theory  
  FTP_WithPolicy
  imports 
    FTP 
begin

text\<open>FTP where the policy is part of the output.\<close>

definition POL :: "'a \<Rightarrow> 'a"   where  "POL x = x"

text\<open>Variant 2 takes the policy into the output\<close>
fun FTP_STP ::
  "((id \<rightharpoonup> port), adr\<^sub>i\<^sub>p, msg) FWStateTransitionP"
  where
(* FTP_PORT_REQUEST *)
 "FTP_STP (i,s,d,ftp_port_request pr) (ports, policy) = 
  (if p_accept (i,s,d,ftp_port_request pr) policy then
  Some (allow (POL ((allow_from_to_port pr (subnet_of d) (subnet_of s)) \<Oplus> policy)),
 ( (ports(i\<mapsto>pr)),(allow_from_to_port pr (subnet_of d) (subnet_of s)) 
                                 \<Oplus> policy))       
  else (Some (deny (POL policy),(ports,policy))))"

(* FTP_CLOSE *)
 |"FTP_STP (i,s,d,ftp_close) (ports,policy) = 
  (if (p_accept (i,s,d,ftp_close) policy) then 
 case ports i of 
  Some pr \<Rightarrow>
       Some(allow (POL (deny_from_to_port pr (subnet_of d) (subnet_of s) \<Oplus> policy)),
        ports(i:=None),
        deny_from_to_port pr (subnet_of d) (subnet_of s) \<Oplus> policy)
 |None \<Rightarrow>Some(allow (POL policy), ports, policy)
       else Some (deny (POL policy), ports, policy))"
(* DEFAULT *)
  |"FTP_STP p x =  (if p_accept p (snd x) 
                   then Some (allow (POL (snd x)),((fst x),snd x)) 
                   else Some (deny (POL (snd x)),(fst x,snd x)))"
end
