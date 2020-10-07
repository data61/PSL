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

subsection \<open>Transformation Example 1\<close>
theory 
  Transformation01
  imports 
    "../../UPF-Firewall"
begin

definition
  FWLink :: "adr\<^sub>i\<^sub>p net" where
  "FWLink = {{(a,b). a = 1}}"
  
definition
  any :: "adr\<^sub>i\<^sub>p net" where
  "any = {{(a,b). a > 5}}"
  
definition
  i4:: "adr\<^sub>i\<^sub>p net" where
  "i4 = {{(a,b). a = 2 }}" 
  
definition
  i27:: "adr\<^sub>i\<^sub>p net" where
  "i27 = {{(a,b). a = 3 }}" 
  
definition
  eth_intern:: "adr\<^sub>i\<^sub>p net" where
  "eth_intern = {{(a,b). a = 4 }}"
  
definition
  eth_private:: "adr\<^sub>i\<^sub>p net" where
  "eth_private = {{(a,b). a = 5 }}"

definition
  (* Mandatory: Global *)
  MG2 :: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "MG2 = AllowPortFromTo i27 any 1 \<oplus> 
       AllowPortFromTo i27 any 2 \<oplus>
       AllowPortFromTo i27 any 3"
  
definition
  MG3 :: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "MG3 = AllowPortFromTo any FWLink 1"
  
definition
  MG4 :: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "MG4 = AllowPortFromTo FWLink FWLink 4"
  
definition
  MG7 :: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "MG7 = AllowPortFromTo FWLink i4 6 \<oplus>
       AllowPortFromTo FWLink i4 7"
  
definition
  MG8 :: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "MG8 = AllowPortFromTo FWLink i4 6 \<oplus>
       AllowPortFromTo FWLink i4 7"
  
  (* Default Global *)
definition
  DG3:: "(adr\<^sub>i\<^sub>p net,port) Combinators" where
  "DG3 = AllowPortFromTo any any 7"

definition
  "Policy = DenyAll \<oplus> MG8 \<oplus>  MG7 \<oplus> MG4 \<oplus> MG3 \<oplus> MG2 \<oplus> DG3"   

lemmas PolicyLemmas =  Policy_def
  FWLink_def
  any_def
  i27_def
  i4_def
  eth_intern_def
  eth_private_def
  MG2_def MG3_def MG4_def MG7_def MG8_def  
  DG3_def

lemmas PolicyL =  MG2_def MG3_def MG4_def MG7_def MG8_def DG3_def Policy_def

definition 
  not_in_same_net :: "(adr\<^sub>i\<^sub>p,DummyContent) packet \<Rightarrow> bool" where
  "not_in_same_net x =  (((src x \<sqsubset> i27) \<longrightarrow> ( \<not> (dest x \<sqsubset> i27))) \<and>
                      ((src x \<sqsubset>  i4) \<longrightarrow> ( \<not> (dest x \<sqsubset> i4))) \<and>
                      ((src x \<sqsubset>  eth_intern) \<longrightarrow> ( \<not> (dest x \<sqsubset> eth_intern))) \<and>
                      ((src x \<sqsubset>  eth_private) \<longrightarrow> ( \<not> (dest x \<sqsubset> eth_private))))"
                   
consts fixID :: id
consts fixContent :: DummyContent

definition "fixElements p = (id p = fixID \<and> content p = fixContent)"

lemmas fixDefs = fixElements_def NetworkCore.id_def NetworkCore.content_def



lemma sets_distinct1: "(n::int) \<noteq> m \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto

lemma sets_distinct2: "(m::int) \<noteq> n \<Longrightarrow> {(a,b). a = n} \<noteq> {(a,b). a = m}"
  by auto

lemma sets_distinct3: "{((a::int),(b::int)). a = n} \<noteq> {(a,b). a > n}"
  by auto

lemma sets_distinct4: "{((a::int),(b::int)). a > n} \<noteq> {(a,b). a = n}"
  by auto

lemma aux: "\<lbrakk>a \<in> c; a \<notin> d; c = d\<rbrakk> \<Longrightarrow> False"
  by auto 
    
lemma sets_distinct5: "(s::int) < g \<Longrightarrow> {(a::int, b::int). a = s} \<noteq> {(a::int, b::int).  g < a}"
  apply (auto simp: sets_distinct3)[1]
  apply (subgoal_tac "(s,4) \<in> {(a::int,b::int). a = (s)}")
   apply (subgoal_tac "(s,4) \<notin> {(a::int,b::int). g < a}")
    apply (erule aux)
     apply assumption+
   apply simp
  by blast

lemma sets_distinct6: "(s::int) < g \<Longrightarrow> {(a::int, b::int).  g < a} \<noteq> {(a::int, b::int).  a = s}"
  apply (rule not_sym)
  apply (rule sets_distinct5)
  by simp

lemma distinctNets: "FWLink \<noteq>  any \<and> FWLink \<noteq>  i4 \<and> FWLink \<noteq>  i27 \<and> FWLink \<noteq>  eth_intern \<and> FWLink \<noteq>   eth_private \<and> 
any \<noteq>  FWLink \<and> any \<noteq>  i4 \<and> any \<noteq>  i27 \<and> any \<noteq>  eth_intern \<and> any \<noteq>  eth_private \<and> i4 \<noteq>  FWLink \<and> 
i4 \<noteq>  any \<and> i4 \<noteq>  i27 \<and> i4 \<noteq>  eth_intern \<and> i4 \<noteq>  eth_private \<and> i27 \<noteq>  FWLink \<and> i27 \<noteq>  any \<and> 
i27 \<noteq>  i4 \<and> i27 \<noteq>  eth_intern \<and> i27 \<noteq>  eth_private \<and> eth_intern \<noteq>  FWLink \<and> eth_intern \<noteq>  any \<and> 
eth_intern \<noteq>  i4 \<and> eth_intern \<noteq>  i27 \<and> eth_intern \<noteq>  eth_private \<and> eth_private \<noteq>  FWLink \<and> 
eth_private \<noteq>  any \<and> eth_private \<noteq>  i4 \<and> eth_private \<noteq>  i27 \<and> eth_private \<noteq>  eth_intern"
  by (simp add: PolicyLemmas sets_distinct1 sets_distinct2 sets_distinct3 sets_distinct4 
                sets_distinct5 sets_distinct6)

lemma aux5: "\<lbrakk>x \<noteq> a; y\<noteq>b; (x \<noteq> y \<and> x \<noteq> b) \<or>  (a \<noteq> b \<and> a \<noteq> y)\<rbrakk> \<Longrightarrow> {x,a} \<noteq> {y,b}"
  by auto

lemma aux2: "{a,b} = {b,a}"
  by auto

lemma ANDex: "allNetsDistinct (policy2list Policy)"
  apply (simp add: PolicyL allNetsDistinct_def distinctNets)
  by (auto simp: PLemmas PolicyLemmas netsDistinct_def sets_distinct5 sets_distinct6)
    
fun (sequential) numberOfRules where 
  "numberOfRules (a\<oplus>b) = numberOfRules a + numberOfRules b"
|"numberOfRules a = (1::int)" 

fun numberOfRulesList where 
 "numberOfRulesList  (x#xs) = ((numberOfRules x)#(numberOfRulesList xs)) "
 |"numberOfRulesList [] = []" 

lemma all_in_list: "all_in_list (policy2list Policy) (Nets_List Policy)"
  apply (simp add: PolicyL)
  apply (unfold Nets_List_def)
  apply (unfold bothNets_def)
  apply (insert distinctNets)
  by simp

lemmas normalizeUnfold =   normalize_def Policy_def Nets_List_def bothNets_def aux aux2 bothNets_def

end
