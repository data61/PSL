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

subsection \<open>Transforamtion Example 2\<close>
theory 
  Transformation02
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
  i4_32:: "adr\<^sub>i\<^sub>p net" where
  "i4_32 = {{(a,b). a = 2 }}" 
  
definition
  i10_32:: "adr\<^sub>i\<^sub>p net" where
  "i10_32 = {{(a,b). a = 3 }}" 
  
definition
  eth_intern:: "adr\<^sub>i\<^sub>p net" where
  "eth_intern = {{(a,b). a = 4 }}"
  
definition
  eth_private:: "adr\<^sub>i\<^sub>p net" where
  "eth_private = {{(a,b). a = 5 }}"
  
definition
  D1a :: "(adr\<^sub>i\<^sub>p net, port) Combinators" where
  "D1a = AllowPortFromTo eth_intern any 1 \<oplus> 
       AllowPortFromTo eth_intern any 2"
  
definition
  D1b :: "(adr\<^sub>i\<^sub>p net, port) Combinators" where
  "D1b = AllowPortFromTo eth_private any 1 \<oplus>
       AllowPortFromTo eth_private any 2"
  
definition
  D2a :: "(adr\<^sub>i\<^sub>p net, port) Combinators" where
  "D2a = AllowPortFromTo  any i4_32 21"
  
definition
  D2b :: "(adr\<^sub>i\<^sub>p net, port) Combinators" where
  "D2b = AllowPortFromTo any i10_32 21 \<oplus> 
       AllowPortFromTo any i10_32 43"
  
definition
  Policy :: "(adr\<^sub>i\<^sub>p net, port) Combinators" where
  "Policy = DenyAll \<oplus> D2b \<oplus> D2a \<oplus> D1b \<oplus> D1a"
  
lemmas PolicyLemmas = Policy_def D1a_def D1b_def D2a_def D2b_def 
  
lemmas PolicyL =  Policy_def
  FWLink_def
  any_def
  i10_32_def
  i4_32_def
  eth_intern_def
  eth_private_def
  D1a_def D1b_def D2a_def D2b_def 
                    
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
  apply (auto simp: sets_distinct3)
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

lemma distinctNets: "FWLink \<noteq> any \<and> FWLink \<noteq> i4_32 \<and> FWLink \<noteq> i10_32 \<and>
FWLink \<noteq> eth_intern \<and> FWLink \<noteq> eth_private \<and> any \<noteq> FWLink \<and> any \<noteq>
i4_32 \<and> any \<noteq> i10_32 \<and> any \<noteq> eth_intern \<and> any \<noteq> eth_private \<and> i4_32 \<noteq>
FWLink \<and> i4_32 \<noteq> any \<and> i4_32 \<noteq> i10_32 \<and> i4_32 \<noteq> eth_intern \<and> i4_32 \<noteq>
eth_private \<and> i10_32 \<noteq> FWLink \<and> i10_32 \<noteq> any \<and> i10_32 \<noteq> i4_32 \<and> i10_32
\<noteq> eth_intern \<and> i10_32 \<noteq> eth_private \<and> eth_intern \<noteq> FWLink \<and> eth_intern
\<noteq> any \<and> eth_intern \<noteq> i4_32 \<and> eth_intern \<noteq> i10_32 \<and> eth_intern \<noteq>
eth_private \<and> eth_private \<noteq> FWLink \<and> eth_private \<noteq> any \<and> eth_private \<noteq>
i4_32 \<and> eth_private \<noteq> i10_32 \<and> eth_private \<noteq> eth_intern " 
  by (simp add: PolicyL sets_distinct1 sets_distinct2 sets_distinct3
      sets_distinct4 sets_distinct5 sets_distinct6) 
    
lemma aux5: "\<lbrakk>x \<noteq> a; y\<noteq>b; (x \<noteq> y \<and> x \<noteq> b) \<or>  (a \<noteq> b \<and> a \<noteq> y)\<rbrakk> \<Longrightarrow> {x,a} \<noteq> {y,b}"
  by auto
    
lemma aux2: "{a,b} = {b,a}"
  by auto
    
lemma ANDex: "allNetsDistinct (policy2list Policy)"
  apply (simp add: PolicyLemmas allNetsDistinct_def distinctNets)
  apply (simp add: PolicyL)
  by (auto simp: PLemmas PolicyL netsDistinct_def sets_distinct5 sets_distinct6 sets_distinct1
                 sets_distinct2)
    
fun (sequential) numberOfRules where 
  "numberOfRules (a\<oplus>b) = numberOfRules a + numberOfRules b"
|"numberOfRules a = (1::int)" 
  
fun numberOfRulesList where 
  "numberOfRulesList  (x#xs) = ((numberOfRules x)#(numberOfRulesList xs)) "
|"numberOfRulesList [] = []" 
  
lemma all_in_list: "all_in_list (policy2list Policy) (Nets_List Policy)"
  apply (simp add: PolicyLemmas)
  apply (unfold Nets_List_def)
  apply (unfold bothNets_def)
  apply (insert distinctNets)
  by simp
    
lemmas normalizeUnfold =   normalize_def PolicyL Nets_List_def bothNets_def aux aux2 bothNets_def sets_distinct1 sets_distinct2 sets_distinct3 sets_distinct4 sets_distinct5 sets_distinct6  aux5 aux2

end
