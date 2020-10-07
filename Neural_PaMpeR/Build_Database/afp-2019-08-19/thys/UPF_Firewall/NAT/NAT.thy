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

subsection\<open>Network Address Translation\<close>
theory 
  NAT
  imports 
    "../PacketFilter/PacketFilter"
begin


definition src2pool :: "'\<alpha> set \<Rightarrow> ('\<alpha>::adr,'\<beta>) packet \<Rightarrow> ('\<alpha>,'\<beta>) packet set" where
  "src2pool t = (\<lambda> p. ({(i,s,d,da). (i = id p \<and> s \<in> t \<and> d = dest p \<and> da = content p)}))"

definition src2poolAP where
  "src2poolAP t = A\<^sub>f (src2pool t)"

definition srcNat2pool :: "'\<alpha> set \<Rightarrow> '\<alpha> set \<Rightarrow> ('\<alpha>::adr,'\<beta>) packet \<mapsto> ('\<alpha>,'\<beta>) packet set" where 
  "srcNat2pool srcs transl = {x. src x \<in> srcs} \<triangleleft> (src2poolAP transl)"

definition src2poolPort :: "int set \<Rightarrow> (adr\<^sub>i\<^sub>p,'\<beta>) packet \<Rightarrow> (adr\<^sub>i\<^sub>p,'\<beta>) packet set" where
  "src2poolPort t = (\<lambda> p. ({(i,(s1,s2),(d1,d2),da). 
          (i = id p \<and> s1 \<in> t \<and> s2 = (snd (src p)) \<and> d1 = (fst (dest p)) \<and> 
                d2 = snd (dest p) \<and> da = content p)}))"

definition src2poolPort_Protocol :: "int set \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet set" where
  "src2poolPort_Protocol t = (\<lambda> p. ({(i,(s1,s2,s3),(d1,d2,d3), da). 
  (i = id p \<and> s1 \<in> t \<and> s2 = (fst (snd (src p))) \<and> s3 = snd (snd (src p)) \<and> 
                   (d1,d2,d3) = dest p \<and> da = content p)}))"

definition srcNat2pool_IntPort :: "address set \<Rightarrow> address set \<Rightarrow> 
 (adr\<^sub>i\<^sub>p,'\<beta>) packet \<mapsto> (adr\<^sub>i\<^sub>p,'\<beta>) packet set" where
  "srcNat2pool_IntPort srcs transl = 
      {x. fst (src x) \<in> srcs} \<triangleleft> (A\<^sub>f (src2poolPort transl))" 

definition srcNat2pool_IntProtocolPort :: "int set \<Rightarrow> int set \<Rightarrow> 
 (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet \<mapsto> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet set" where 
  "srcNat2pool_IntProtocolPort srcs transl =
      {x. (fst ( (src x))) \<in> srcs} \<triangleleft> (A\<^sub>f (src2poolPort_Protocol transl))" 

definition srcPat2poolPort_t :: "int set \<Rightarrow> (adr\<^sub>i\<^sub>p,'\<beta>) packet \<Rightarrow> (adr\<^sub>i\<^sub>p,'\<beta>) packet set" where
  "srcPat2poolPort_t t = (\<lambda> p. ({(i,(s1,s2),(d1,d2),da). 
           (i = id p \<and> s1 \<in> t \<and> d1 = (fst (dest p)) \<and> d2 = snd (dest p)\<and> da = content p)}))"

definition srcPat2poolPort_Protocol_t :: "int set \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet set" where
  "srcPat2poolPort_Protocol_t t = (\<lambda> p. ({(i,(s1,s2,s3),(d1,d2,d3),da). 
  (i = id p \<and> s1 \<in> t \<and> s3 = src_protocol p \<and> (d1,d2,d3) = dest p \<and> da = content p)}))"

definition srcPat2pool_IntPort :: "int set \<Rightarrow> int set \<Rightarrow> (adr\<^sub>i\<^sub>p,'\<beta>) packet \<mapsto> 
                                            (adr\<^sub>i\<^sub>p,'\<beta>) packet set" where 
  "srcPat2pool_IntPort srcs transl = 
  {x. (fst (src x)) \<in> srcs} \<triangleleft> (A\<^sub>f (srcPat2poolPort_t transl))" 

definition srcPat2pool_IntProtocol :: 
  "int set \<Rightarrow> int set \<Rightarrow> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet \<mapsto> (adr\<^sub>i\<^sub>p\<^sub>p,'\<beta>) packet set" where 

  "srcPat2pool_IntProtocol srcs transl = 
  {x. (fst (src x)) \<in> srcs} \<triangleleft> (A\<^sub>f (srcPat2poolPort_Protocol_t transl))" 

text\<open>
  The following lemmas are used for achieving a normalized output format of packages after 
  applying NAT. This is used, e.g., by our firewall execution tool. 
\<close>

lemma datasimp: "{(i, (s1, s2, s3), aba).
                    \<forall>a aa b ba. aba = ((a, aa, b), ba) \<longrightarrow> i = i1 \<and> s1 = i101 \<and> 
                               s3 = iudp \<and> a = i110 \<and> aa = X606X3 \<and> b = X607X4 \<and> ba = data} 
                 = {(i, (s1, s2, s3), aba).
                    i = i1 \<and> s1 = i101 \<and> s3 = iudp \<and> (\<lambda> ((a,aa,b),ba). a = i110 \<and> aa = X606X3 \<and>
                    b = X607X4 \<and> ba = data) aba}"
  by auto

lemma datasimp2: "{(i, (s1, s2, s3), aba).
                    \<forall>a aa b ba. aba = ((a, aa, b), ba) \<longrightarrow> i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> 
                        s2 = i1 \<and> a = i110 \<and> aa = i4 \<and> b = iudp \<and> ba = data}
                = {(i, (s1, s2, s3), aba).
                       i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> s2 = i1 \<and> (\<lambda> ((a,aa,b),ba). a = i110 \<and> 
                       aa = i4 \<and> b = iudp \<and> ba = data) aba}"
  by auto

lemma datasimp3: "{(i, (s1, s2, s3), aba).
                     \<forall> a aa b ba. aba = ((a, aa, b), ba) \<longrightarrow> i = i1 \<and> i115 < s1 \<and> s1 < i124 \<and> 
                         s3 = iudp \<and> s2 = ii1 \<and> a = i110 \<and> aa = i3 \<and> b = itcp \<and> ba = data}
                = {(i, (s1, s2, s3), aba).
                         i = i1 \<and> i115 < s1 \<and> s1 < i124 \<and> s3 = iudp \<and> s2 = ii1 \<and> 
                       (\<lambda> ((a,aa,b),ba). a = i110 & aa = i3 & b = itcp & ba = data) aba}"
  by auto

lemma datasimp4: "{(i, (s1, s2, s3), aba).
                    \<forall>a aa b ba. aba = ((a, aa, b), ba) \<longrightarrow> i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> 
                        s2 = ii1 \<and> a = i110 \<and> aa = i7 \<and> b = itcp \<and> ba = data}
                = {(i, (s1, s2, s3), aba).
                        i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> s2 = ii1 \<and> 
                        (\<lambda> ((a,aa,b),ba). a = i110 \<and> aa = i7 \<and> b = itcp \<and> ba = data) aba}"
  by auto

lemma datasimp5: " {(i, (s1, s2, s3), aba).
                     i = i1 \<and> s1 = i101 \<and> s3 = iudp \<and> (\<lambda> ((a,aa,b),ba). a = i110 \<and> aa = X606X3 \<and> 
                       b = X607X4 \<and> ba = data) aba}
                 = {(i, (s1, s2, s3), (a,aa,b),ba).
                       i = i1 \<and> s1 = i101 \<and> s3 = iudp \<and>  a = i110 \<and> aa = X606X3 \<and> 
                       b = X607X4 \<and> ba = data}"
  by auto

lemma datasimp6: "{(i, (s1, s2, s3), aba).
                     i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> s2 = i1 \<and> 
                     (\<lambda> ((a,aa,b),ba). a = i110 \<and>  aa = i4 \<and> b = iudp \<and> ba = data) aba}
                 = {(i, (s1, s2, s3), (a,aa,b),ba).
                       i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> s2 = i1 \<and> a = i110 \<and> 
                       aa = i4 \<and> b = iudp \<and> ba = data}"
  by auto

lemma datasimp7: "{(i, (s1, s2, s3), aba).
                     i = i1 \<and> i115 < s1 \<and> s1 < i124 \<and> s3 = iudp \<and> s2 = ii1 \<and> 
                     (\<lambda> ((a,aa,b),ba). a = i110 \<and> aa = i3 \<and> b = itcp \<and> ba = data) aba} 
                = {(i, (s1, s2, s3), (a,aa,b),ba).
                     i = i1 \<and> i115 < s1 \<and> s1 < i124 \<and> s3 = iudp \<and> s2 = ii1 
                     \<and> a = i110 \<and> aa = i3 \<and> b = itcp \<and> ba = data}"
  by auto

lemma datasimp8: "{(i, (s1, s2, s3), aba). i = i1 \<and> s1 = i132 \<and> s3 = iudp \<and> s2 = ii1 \<and> 
                   (\<lambda> ((a,aa,b),ba). a = i110 \<and> aa = i7 \<and> b = itcp \<and> ba = data) aba}
                = {(i, (s1, s2, s3), (a,aa,b),ba). i = i1 \<and> s1 = i132 \<and> s3 = iudp 
                                   \<and> s2 = ii1 \<and>  a = i110 \<and> aa = i7 \<and> b = itcp \<and> ba = data}"
  by auto

lemmas datasimps = datasimp datasimp2 datasimp3 datasimp4
                   datasimp5 datasimp6 datasimp7 datasimp8

lemmas NATLemmas = src2pool_def src2poolPort_def
                   src2poolPort_Protocol_def src2poolAP_def srcNat2pool_def
                   srcNat2pool_IntProtocolPort_def srcNat2pool_IntPort_def
                   srcPat2poolPort_t_def srcPat2poolPort_Protocol_t_def
                   srcPat2pool_IntPort_def srcPat2pool_IntProtocol_def
end
