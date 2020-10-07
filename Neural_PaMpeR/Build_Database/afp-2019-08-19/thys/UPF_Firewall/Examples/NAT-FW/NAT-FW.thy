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

section \<open>Example: NAT\<close> 
theory 
  "NAT-FW"
  imports
    "../../UPF-Firewall"
begin

definition subnet1 :: "adr\<^sub>i\<^sub>p net" where
 "subnet1 = {{(d,e). d > 1 \<and> d < 256}}"

definition subnet2 :: "adr\<^sub>i\<^sub>p net" where
 "subnet2 = {{(d,e). d > 500 \<and> d < 1256}}"

definition
  "accross_subnets x  \<equiv> 
 ((src x \<sqsubset> subnet1 \<and> (dest x \<sqsubset> subnet2)) \<or>
  (src x \<sqsubset> subnet2 \<and> (dest x \<sqsubset> subnet1)))"

definition
   filter :: "(adr\<^sub>i\<^sub>p, DummyContent) FWPolicy" where
  "filter = allow_from_port_to (1::port) subnet1 subnet2 ++
             allow_from_port_to (2::port) subnet1 subnet2 ++
             allow_from_port_to (3::port) subnet1 subnet2 ++ deny_all"

definition 
 nat_0  where 
 "nat_0 = (A\<^sub>f(\<lambda>x. {x}))"

lemmas UnfoldPolicy0 =filter_def nat_0_def 
                      NATLemmas 
                      ProtocolPortCombinators.ProtocolCombinators 
                      adr\<^sub>i\<^sub>pLemmas
                      packet_defs accross_subnets_def
                      subnet1_def subnet2_def

lemmas subnets = subnet1_def subnet2_def 

definition Adr11 :: "int set"
where "Adr11 = {d. d > 2 \<and> d < 3}"

definition Adr21 :: "int set" where
 "Adr21 = {d. d > 502 \<and> d < 503}"

definition nat_1 where
 "nat_1 = nat_0 ++ (srcPat2pool_IntPort Adr11 Adr21)"

definition policy_1 where
 "policy_1 = ((\<lambda> (x,y). x) o_f 
 ((nat_1 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy1 = UnfoldPolicy0 nat_1_def Adr11_def Adr21_def policy_1_def

definition Adr12 :: "int set"
where "Adr12 = {d. d > 4 \<and> d < 6}"

definition Adr22 :: "int set" where
 "Adr22 = {d. d > 504 \<and> d < 506}"

definition nat_2 where
 "nat_2 = nat_1 ++ (srcPat2pool_IntPort Adr12 Adr22)"

definition policy_2 where
 "policy_2 = ((\<lambda> (x,y). x) o_f 
 ((nat_2 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy2 = UnfoldPolicy1 nat_2_def Adr12_def Adr22_def policy_2_def

definition Adr13 :: "int set"
where "Adr13 = {d. d > 6 \<and> d < 9}"

definition Adr23 :: "int set" where
 "Adr23 = {d. d > 506 \<and> d < 509}"

definition nat_3 where
 "nat_3 = nat_2 ++ (srcPat2pool_IntPort Adr13 Adr23)"

definition policy_3 where
 "policy_3 = ((\<lambda> (x,y). x) o_f 
 ((nat_3 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy3 = UnfoldPolicy2 nat_3_def Adr13_def Adr23_def policy_3_def

definition Adr14 :: "int set"
where "Adr14 = {d. d > 8 \<and> d < 12}"

definition Adr24 :: "int set" where
 "Adr24 = {d. d > 508 \<and> d < 512}"

definition nat_4 where
 "nat_4 = nat_3 ++ (srcPat2pool_IntPort Adr14 Adr24)"

definition policy_4 where
 "policy_4 = ((\<lambda> (x,y). x) o_f 
 ((nat_4 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy4 = UnfoldPolicy3 nat_4_def Adr14_def Adr24_def policy_4_def

definition Adr15 :: "int set"
where "Adr15 = {d. d > 10 \<and> d < 15}"

definition Adr25 :: "int set" where
 "Adr25 = {d. d > 510 \<and> d < 515}"

definition nat_5 where
 "nat_5 = nat_4 ++ (srcPat2pool_IntPort Adr15 Adr25)"

definition policy_5 where
 "policy_5 = ((\<lambda> (x,y). x) o_f 
 ((nat_5 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy5 = UnfoldPolicy4 nat_5_def Adr15_def Adr25_def policy_5_def

definition Adr16 :: "int set"
where "Adr16 = {d. d > 12 \<and> d < 18}"

definition Adr26 :: "int set" where
 "Adr26 = {d. d > 512 \<and> d < 518}"

definition nat_6 where
 "nat_6 = nat_5 ++ (srcPat2pool_IntPort Adr16 Adr26)"

definition policy_6 where
 "policy_6 = ((\<lambda> (x,y). x) o_f 
 ((nat_6 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy6 = UnfoldPolicy5 nat_6_def Adr16_def Adr26_def policy_6_def

definition Adr17 :: "int set"
where "Adr17 = {d. d > 14 \<and> d < 21}"

definition Adr27 :: "int set" where
 "Adr27 = {d. d > 514 \<and> d < 521}"

definition nat_7 where
 "nat_7 = nat_6 ++ (srcPat2pool_IntPort Adr17 Adr27)"

definition policy_7 where
 "policy_7 = ((\<lambda> (x,y). x) o_f 
 ((nat_7 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy7 = UnfoldPolicy6 nat_7_def Adr17_def Adr27_def policy_7_def

definition Adr18 :: "int set"
where "Adr18 = {d. d > 16 \<and> d < 24}"

definition Adr28 :: "int set" where
 "Adr28 = {d. d > 516 \<and> d < 524}"

definition nat_8 where
 "nat_8 = nat_7 ++ (srcPat2pool_IntPort Adr18 Adr28)"

definition policy_8 where
 "policy_8 = ((\<lambda> (x,y). x) o_f 
 ((nat_8 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy8 = UnfoldPolicy7 nat_8_def Adr18_def Adr28_def policy_8_def

definition Adr19 :: "int set"
where "Adr19 = {d. d > 18 \<and> d < 27}"

definition Adr29 :: "int set" where
 "Adr29 = {d. d > 518 \<and> d < 527}"

definition nat_9 where
 "nat_9 = nat_8 ++ (srcPat2pool_IntPort Adr19 Adr29)"

definition policy_9 where
 "policy_9 = ((\<lambda> (x,y). x) o_f 
 ((nat_9 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy9 = UnfoldPolicy8 nat_9_def Adr19_def Adr29_def policy_9_def

definition Adr110 :: "int set"
where "Adr110 = {d. d > 20 \<and> d < 30}"

definition Adr210 :: "int set" where
 "Adr210 = {d. d > 520 \<and> d < 530}"

definition nat_10 where
 "nat_10 = nat_9 ++ (srcPat2pool_IntPort Adr110 Adr210)"

definition policy_10 where
 "policy_10 = ((\<lambda> (x,y). x) o_f 
 ((nat_10 \<Otimes>\<^sub>2 filter) o (\<lambda> x. (x,x))))"

lemmas UnfoldPolicy10 = UnfoldPolicy9 nat_10_def Adr110_def Adr210_def policy_10_def

end
