(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2014 Achim D. Brucker, Germany
 *               2010-2014 Université Paris-Sud, France
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
 ******************************************************************************)

section \<open>Instantiating Our Secure Service Example\<close>
theory 
  ServiceExample
  imports 
    Service
begin
text \<open>
  In the following, we briefly present an instantiations  of our secure service example 
  from the last section. We assume three different members of the health care staff and 
  two patients:
\<close>

subsection \<open>Access Control Configuration\<close>
definition alice :: user where "alice = 1"
definition bob :: user where "bob = 2"
definition charlie :: user where "charlie = 3"
definition patient1 :: patient where "patient1 = 5"
definition patient2 :: patient where "patient2 = 6"

definition UC0 :: \<upsilon> where
 "UC0 = Map.empty(alice\<mapsto>Nurse)(bob\<mapsto>ClinicalPractitioner)(charlie\<mapsto>Clerical)"

definition entry1  :: entry where
 "entry1 = (Open,alice, dummyContent)"

definition entry2  :: entry where
 "entry2 = (Closed,bob, dummyContent)"

definition entry3  :: entry where
 "entry3 = (Closed,alice, dummyContent)"

definition SCR1 :: SCR where
 "SCR1 = (Map.empty(1\<mapsto>entry1))"

definition SCR2 :: SCR where
 "SCR2 =  (Map.empty)"

definition Spine0 :: DB where
 "Spine0 = Map.empty(patient1\<mapsto>SCR1)(patient2\<mapsto>SCR2)"

definition LR1 :: LR where
 "LR1 =(Map.empty(1\<mapsto>{alice}))"

definition \<Sigma>0 :: \<Sigma> where
 "\<Sigma>0 = (Map.empty(patient1\<mapsto>LR1))"

subsection \<open>The Initial System State\<close>
definition \<sigma>0 :: "DB \<times> \<Sigma>\<times>\<upsilon>" where
 "\<sigma>0 = (Spine0,\<Sigma>0,UC0)"
 
subsection\<open>Basic Properties\<close>

lemma [simp]: "(case a of allow d \<Rightarrow> \<lfloor>X\<rfloor> | deny d2 \<Rightarrow> \<lfloor>Y\<rfloor>) = \<bottom> \<Longrightarrow> False"
  by (case_tac a,simp_all)


lemma [cong,simp]: 
 "((if hasLR urp1_alice 1 \<Sigma>0 then \<lfloor>allow ()\<rfloor> else \<lfloor>deny ()\<rfloor>) = \<bottom>) = False"
  by (simp)

lemmas MonSimps =  valid_SE_def unit_SE_def bind_SE_def
lemmas Psplits  = option.splits unit.splits prod.splits decision.splits
lemmas PolSimps = valid_SE_def unit_SE_def bind_SE_def if_splits policy2MON_def 
                  SE_LR_RBAC_ST_Policy_def map_add_def id_def LRsimps prod_2_def RBACPolicy_def 
                  SE_LR_Policy_def SEPolicy_def RBAC_def deleteEntrySE_def editEntrySE_def 
                  readEntrySE_def \<sigma>0_def \<Sigma>0_def UC0_def patient1_def patient2_def LR1_def 
                  alice_def bob_def charlie_def get_entry_def SE_LR_RBAC_Policy_def Allow_def 
                  Deny_def dom_restrict_def policy_range_comp_def prod_orA_def prod_orD_def 
                  ST_Allow_def ST_Deny_def Spine0_def SCR1_def SCR2_def entry1_def entry2_def 
                  entry3_def FunPolicy_def SE_LR_FUN_Policy_def o_def image_def UPFDefs

lemma "SE_LR_RBAC_Policy ((createSCR alice Clerical patient1),\<sigma>0)= Some (deny ())"
  by (simp add: PolSimps)
    
lemma exBool[simp]: "\<exists>a::bool. a"  
  by auto
    
lemma deny_allow[simp]: " \<lfloor>deny ()\<rfloor> \<notin> Some ` range allow"  
  by auto
    
lemma allow_deny[simp]: " \<lfloor>allow ()\<rfloor> \<notin> Some ` range deny" 
  by auto
    
text\<open>Policy as monad. Alice using her first urp can read the SCR of patient1.\<close>
lemma 
  "(\<sigma>0 \<Turnstile> (os \<leftarrow> mbind [(createSCR alice Clerical patient1)] (PolMon); 
       (return (os = [(deny (Out) )]))))"
  by (simp add: PolMon_def MonSimps PolSimps)
    
text\<open>Presenting her other urp, she is not allowed to read it.\<close>
lemma "SE_LR_RBAC_Policy ((appendEntry alice Clerical patient1 ei d),\<sigma>0)= \<lfloor>deny ()\<rfloor>"
  by (simp add: PolSimps)  

end


