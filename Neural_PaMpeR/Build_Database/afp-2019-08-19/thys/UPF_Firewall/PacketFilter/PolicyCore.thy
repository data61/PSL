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

subsection \<open>Policy Core\<close>
theory 
  PolicyCore
  imports 
     NetworkCore 
     UPF.UPF
begin


text\<open>A policy is seen as a partial mapping from packet to packet out.\<close>

type_synonym ('\<alpha>, '\<beta>) FWPolicy = "('\<alpha>, '\<beta>) packet \<mapsto> unit" 

text\<open>
  When combining several rules, the firewall is supposed to apply the
  first matching one. In our setting this means the first rule which
  maps the packet in question to \<open>Some (packet out)\<close>. This is
  exactly what happens when using the map-add operator (\<open>rule1
  ++ rule2\<close>). The only difference is that the rules must be given in
  reverse order. 
\<close>



text\<open>
  The constant \<open>p_accept\<close> is \<open>True\<close> iff the policy
  accepts the packet. 
\<close>

definition
  p_accept :: "('\<alpha>, '\<beta>) packet \<Rightarrow> ('\<alpha>, '\<beta>) FWPolicy \<Rightarrow> bool" where
  "p_accept p pol =  (pol p = \<lfloor>allow ()\<rfloor>)"

end
