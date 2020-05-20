(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2010-2012 ETH Zurich, Switzerland
 *               2010-2015 Achim D. Brucker, Germany
 *               2010-2017 Université Paris-Sud, France
 *               2015-2017 The Univeristy of Sheffield, UK
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

section \<open>Secure Service Specification\<close>
theory 
  Service
  imports 
    UPF
begin
text \<open>
  In this section, we model a simple Web service and its access control model 
  that allows the staff in a hospital to access health care records of patients. 
\<close>

subsection\<open>Datatypes for Modelling Users and Roles\<close>
subsubsection \<open>Users\<close>
text\<open>
  First, we introduce a type for users that we use to model that each 
  staff member has a unique id:
\<close>
type_synonym user = int  (* Each NHS employee has a unique NHS_ID. *)

text \<open>
  Similarly, each patient has a unique id:
\<close>
type_synonym patient = int (* Each patient gets a unique id *)

subsubsection \<open>Roles and Relationships\<close>
text\<open>In our example, we assume three different roles for members of the clinical staff:\<close>

datatype role =  ClinicalPractitioner | Nurse | Clerical 

text\<open>
  We model treatment relationships (legitimate relationships) between staff and patients 
  (respectively, their health records. This access control model is inspired by our detailed 
  NHS model.
\<close>     
type_synonym lr_id = int
type_synonym LR    = "lr_id \<rightharpoonup> (user set)"
  
text\<open>The security context stores all the existing LRs.\<close>
type_synonym \<Sigma> = "patient \<rightharpoonup> LR"
  
text\<open>The user context stores the roles the users are in.\<close>
type_synonym \<upsilon> = "user \<rightharpoonup> role"
  
subsection \<open>Modelling Health Records and the Web Service API\<close>
subsubsection \<open>Health Records\<close>
text \<open>The content and the status of the entries of a health record\<close>
datatype data         = dummyContent 
datatype status       = Open | Closed
type_synonym entry_id = int
type_synonym entry    = "status \<times> user \<times> data"
type_synonym SCR      = "(entry_id \<rightharpoonup> entry)"
type_synonym DB       = "patient \<rightharpoonup> SCR"

subsubsection \<open>The Web Service API\<close>
text\<open>The operations provided by the service:\<close>
datatype Operation = createSCR user role patient  
                   | appendEntry user role patient entry_id entry
                   | deleteEntry user role patient entry_id  
                   | readEntry user role patient entry_id
                   | readSCR user role patient
                   | addLR user role patient lr_id "(user set)"
                   | removeLR user role patient lr_id
                   | changeStatus user role patient entry_id status
                   | deleteSCR user role patient 
                   | editEntry user role patient entry_id entry

fun is_createSCR where
 "is_createSCR (createSCR u r p) = True"
|"is_createSCR x = False"

fun is_appendEntry where
  "is_appendEntry (appendEntry u r p e ei) = True"
 |"is_appendEntry x = False" 

fun is_deleteEntry where
  "is_deleteEntry (deleteEntry u r p e_id) = True"
 |"is_deleteEntry x = False"

fun is_readEntry where
  "is_readEntry (readEntry u r p e) = True"
 |"is_readEntry x = False"

fun is_readSCR where
  "is_readSCR (readSCR u r p) = True"
 |"is_readSCR x = False"

fun is_changeStatus where
  "is_changeStatus (changeStatus u r p s ei) = True"
 |"is_changeStatus x = False"

fun is_deleteSCR where
  "is_deleteSCR (deleteSCR u r p) = True"
 |"is_deleteSCR x = False"

fun is_addLR where
  "is_addLR (addLR u r lrid lr us) = True"
 |"is_addLR x = False"

fun is_removeLR where
  "is_removeLR (removeLR u r p lr) = True"
 |"is_removeLR x = False"

fun is_editEntry where
  "is_editEntry (editEntry u r p e_id s) = True"
 |"is_editEntry x = False"

fun SCROp :: "(Operation \<times> DB) \<rightharpoonup> SCR" where
   "SCROp ((createSCR u r p), S) = S p"
  |"SCROp ((appendEntry u r p ei e), S) = S p"
  |"SCROp ((deleteEntry u r p e_id), S) = S p"
  |"SCROp ((readEntry u r p e), S) = S p"
  |"SCROp ((readSCR u r p), S) = S p"
  |"SCROp ((changeStatus u r p s ei),S) = S p"
  |"SCROp ((deleteSCR u r p),S) = S p"
  |"SCROp ((editEntry u r p e_id s),S) = S p"
  |"SCROp x = \<bottom>"

fun patientOfOp :: "Operation \<Rightarrow> patient" where
   "patientOfOp (createSCR u r p) =  p"
  |"patientOfOp (appendEntry u r p e ei) =  p"
  |"patientOfOp (deleteEntry u r p e_id) =  p"
  |"patientOfOp (readEntry u r p e) =  p"
  |"patientOfOp (readSCR u r p) =  p"
  |"patientOfOp (changeStatus u r p s ei) =  p"
  |"patientOfOp (deleteSCR u r p) =  p"
  |"patientOfOp (addLR u r p lr ei) =  p"
  |"patientOfOp (removeLR u r p lr) =  p"
  |"patientOfOp (editEntry u r p e_id s) =  p"

fun userOfOp :: "Operation \<Rightarrow> user" where
   "userOfOp (createSCR u r p) = u"
  |"userOfOp (appendEntry u r p e ei) = u"
  |"userOfOp (deleteEntry u r p e_id) = u"
  |"userOfOp (readEntry u r p e) = u"
  |"userOfOp (readSCR u r p) = u"
  |"userOfOp (changeStatus u r p s ei) = u"
  |"userOfOp (deleteSCR u r p) = u"
  |"userOfOp (editEntry u r p e_id s) = u"
  |"userOfOp (addLR u r p lr ei) = u"
  |"userOfOp (removeLR u r p lr) = u"

fun roleOfOp :: "Operation \<Rightarrow> role" where
   "roleOfOp (createSCR u r p) = r"
  |"roleOfOp (appendEntry u r p e ei) = r"
  |"roleOfOp (deleteEntry u r p e_id) = r"
  |"roleOfOp (readEntry u r p e) = r"
  |"roleOfOp (readSCR u r p) = r"
  |"roleOfOp (changeStatus u r p s ei) = r"
  |"roleOfOp (deleteSCR u r p) = r"
  |"roleOfOp (editEntry u r p e_id s) = r"
  |"roleOfOp (addLR u r p lr ei) = r"
  |"roleOfOp (removeLR u r p lr) = r"

fun contentOfOp :: "Operation \<Rightarrow> data" where
   "contentOfOp (appendEntry u r p ei e) = (snd (snd e))"
  |"contentOfOp (editEntry u r p ei e) = (snd (snd e))"

fun contentStatic :: "Operation \<Rightarrow> bool" where
   "contentStatic (appendEntry u r p ei e) = ((snd (snd e)) = dummyContent)"
  |"contentStatic (editEntry u r p ei e) = ((snd (snd e)) = dummyContent)"
  |"contentStatic x = True"

fun allContentStatic where 
   "allContentStatic (x#xs) = (contentStatic x \<and> allContentStatic xs)"
  |"allContentStatic [] = True"


subsection\<open>Modelling Access Control\<close>
text \<open>
  In the following, we define a rather complex access control model for our 
  scenario that extends traditional role-based access control 
  (RBAC)~\cite{sandhu.ea:role-based:1996} with treatment relationships and sealed 
  envelopes. Sealed envelopes (see~\cite{bruegger:generation:2012} for details)
  are a variant of break-the-glass access control (see~\cite{brucker.ea:extending:2009} 
  for a general motivation and explanation of break-the-glass access control).
\<close>

subsubsection \<open>Sealed Envelopes\<close>

type_synonym SEPolicy = "(Operation \<times> DB \<mapsto>  unit) "

definition get_entry:: "DB \<Rightarrow> patient \<Rightarrow> entry_id \<Rightarrow> entry option" where
 "get_entry S p e_id =   (case S p of \<bottom> \<Rightarrow> \<bottom>
                                    | \<lfloor>Scr\<rfloor> \<Rightarrow> Scr e_id)"

definition userHasAccess:: "user \<Rightarrow> entry \<Rightarrow> bool" where
 "userHasAccess u e = ((fst e) = Open \<or> (fst (snd e) = u))"

definition readEntrySE :: SEPolicy where
 "readEntrySE x = (case x of (readEntry u r p e_id,S) \<Rightarrow> (case get_entry S p e_id of 
                                                            \<bottom> \<Rightarrow> \<bottom>
                                                          | \<lfloor>e\<rfloor>  \<Rightarrow> (if (userHasAccess u e) 
                                                                     then \<lfloor>allow ()\<rfloor> 
                                                                     else \<lfloor>deny ()\<rfloor> ))
                            | x \<Rightarrow> \<bottom>)"

definition deleteEntrySE :: SEPolicy where
 "deleteEntrySE x = (case x of (deleteEntry u r p e_id,S) \<Rightarrow>  (case get_entry S p e_id of 
                                                                \<bottom> \<Rightarrow> \<bottom>
                                                              | \<lfloor>e\<rfloor> \<Rightarrow> (if (userHasAccess u e) 
                                                                       then \<lfloor>allow ()\<rfloor> 
                                                                       else \<lfloor>deny ()\<rfloor>))   
                              | x \<Rightarrow> \<bottom>)"

definition editEntrySE :: SEPolicy where
 "editEntrySE x = (case x of (editEntry u r p e_id s,S) \<Rightarrow>  (case get_entry S p e_id of 
                                                               \<bottom> \<Rightarrow> \<bottom>
                                                             | \<lfloor>e\<rfloor> \<Rightarrow> (if (userHasAccess u e) 
                                                                      then \<lfloor>allow ()\<rfloor>
                                                                      else \<lfloor>deny ()\<rfloor>))
                            | x \<Rightarrow> \<bottom>)"
  
definition SEPolicy :: SEPolicy where
 "SEPolicy =  editEntrySE \<Oplus> deleteEntrySE \<Oplus> readEntrySE \<Oplus> A\<^sub>U"
  

lemmas SEsimps = SEPolicy_def get_entry_def userHasAccess_def
                 editEntrySE_def deleteEntrySE_def readEntrySE_def

subsubsection \<open>Legitimate Relationships\<close>

type_synonym LRPolicy = "(Operation \<times> \<Sigma>, unit) policy"

fun hasLR:: "user \<Rightarrow> patient \<Rightarrow> \<Sigma> \<Rightarrow> bool"  where
 "hasLR u p \<Sigma> = (case \<Sigma> p of \<bottom>     \<Rightarrow> False  
                           | \<lfloor>lrs\<rfloor>  \<Rightarrow>  (\<exists>lr. lr\<in>(ran lrs) \<and> u \<in> lr))"

definition LRPolicy :: LRPolicy where 
 "LRPolicy = (\<lambda>(x,y). (if hasLR (userOfOp x) (patientOfOp x) y 
                       then \<lfloor>allow ()\<rfloor> 
                       else \<lfloor>deny ()\<rfloor>))"

definition createSCRPolicy :: LRPolicy where
 "createSCRPolicy x = (if   (is_createSCR (fst x)) 
                       then \<lfloor>allow ()\<rfloor> 
                       else  \<bottom>)"

definition addLRPolicy :: LRPolicy where
 "addLRPolicy x = (if  (is_addLR (fst x)) 
                   then \<lfloor>allow ()\<rfloor> 
                   else \<bottom>)"

definition LR_Policy where  "LR_Policy = createSCRPolicy \<Oplus> addLRPolicy \<Oplus> LRPolicy \<Oplus> A\<^sub>U"

lemmas LRsimps = LR_Policy_def createSCRPolicy_def addLRPolicy_def LRPolicy_def

type_synonym FunPolicy = "(Operation \<times> DB \<times> \<Sigma>,unit) policy" 

fun createFunPolicy :: FunPolicy where
   "createFunPolicy ((createSCR u r p),(D,S)) = (if p \<in> dom D 
                                                 then \<lfloor>deny ()\<rfloor> 
                                                 else \<lfloor>allow ()\<rfloor>)"
  |"createFunPolicy x = \<bottom>"

fun addLRFunPolicy :: FunPolicy where
   "addLRFunPolicy ((addLR u r p l us),(D,S)) = (if l \<in> dom S 
                                                 then \<lfloor>deny ()\<rfloor> 
                                                 else \<lfloor>allow ()\<rfloor>)"
  |"addLRFunPolicy x = \<bottom>"

fun removeLRFunPolicy :: FunPolicy where
   "removeLRFunPolicy ((removeLR u r p l),(D,S)) = (if l \<in> dom S 
                                                    then \<lfloor>allow ()\<rfloor> 
                                                    else \<lfloor>deny ()\<rfloor>)"
  |"removeLRFunPolicy x = \<bottom>"

fun readSCRFunPolicy :: FunPolicy where
   "readSCRFunPolicy ((readSCR u r p),(D,S)) = (if p \<in> dom D 
                                                then \<lfloor>allow ()\<rfloor> 
                                                else \<lfloor>deny ()\<rfloor>)"
  |"readSCRFunPolicy x = \<bottom>"

fun deleteSCRFunPolicy :: FunPolicy where
   "deleteSCRFunPolicy ((deleteSCR u r p),(D,S)) = (if p \<in> dom D 
                                                    then \<lfloor>allow ()\<rfloor> 
                                                    else \<lfloor>deny ()\<rfloor>)"
  |"deleteSCRFunPolicy x = \<bottom>"

fun changeStatusFunPolicy  :: FunPolicy where
   "changeStatusFunPolicy (changeStatus u r p e s,(d,S)) = 
          (case d p of \<lfloor>x\<rfloor> \<Rightarrow> (if e \<in> dom x 
                                  then \<lfloor>allow ()\<rfloor> 
                                  else \<lfloor>deny ()\<rfloor>)
                     | _  \<Rightarrow> \<lfloor>deny ()\<rfloor>)" 
  |"changeStatusFunPolicy x = \<bottom>"

fun deleteEntryFunPolicy  :: FunPolicy where
   "deleteEntryFunPolicy (deleteEntry u r p e,(d,S)) = 
          (case d p of \<lfloor>x\<rfloor> \<Rightarrow> (if e \<in> dom x 
                                  then \<lfloor>allow ()\<rfloor> 
                                  else \<lfloor>deny ()\<rfloor>)
                     | _  \<Rightarrow> \<lfloor>deny ()\<rfloor>)" 
  |"deleteEntryFunPolicy x = \<bottom>"

fun readEntryFunPolicy :: FunPolicy where
   "readEntryFunPolicy (readEntry u r p e,(d,S)) = 
          (case d p of \<lfloor>x\<rfloor> \<Rightarrow>  (if e \<in> dom x 
                                   then \<lfloor>allow ()\<rfloor> 
                                   else \<lfloor>deny ()\<rfloor>)
                      | _ \<Rightarrow> \<lfloor>deny ()\<rfloor>)" 
  |"readEntryFunPolicy x = \<bottom>"

fun appendEntryFunPolicy  :: FunPolicy where
   "appendEntryFunPolicy (appendEntry u r p e ed,(d,S)) = 
          (case d p of \<lfloor>x\<rfloor> \<Rightarrow>  (if e \<in> dom x 
                                   then \<lfloor>deny ()\<rfloor> 
                                   else \<lfloor>allow ()\<rfloor>)
                      | _ \<Rightarrow> \<lfloor>deny ()\<rfloor>)" 
  |"appendEntryFunPolicy x = \<bottom>"

fun editEntryFunPolicy  :: FunPolicy where
   "editEntryFunPolicy (editEntry u r p ei e,(d,S)) = 
               (case d p of \<lfloor>x\<rfloor> \<Rightarrow> (if ei \<in> dom x 
                                       then \<lfloor>allow ()\<rfloor> 
                                       else \<lfloor>deny ()\<rfloor>)
                          | _ \<Rightarrow> \<lfloor>deny ()\<rfloor>)" 
  |"editEntryFunPolicy x = \<bottom>"

definition FunPolicy where 
 "FunPolicy = editEntryFunPolicy \<Oplus> appendEntryFunPolicy \<Oplus>
              readEntryFunPolicy \<Oplus> deleteEntryFunPolicy \<Oplus> 
              changeStatusFunPolicy \<Oplus> deleteSCRFunPolicy \<Oplus>
              removeLRFunPolicy \<Oplus> readSCRFunPolicy \<Oplus>
              addLRFunPolicy \<Oplus> createFunPolicy \<Oplus> A\<^sub>U"

subsubsection\<open>Modelling Core RBAC\<close>

type_synonym RBACPolicy = "Operation \<times> \<upsilon> \<mapsto> unit"

definition RBAC :: "(role \<times> Operation) set" where 
 "RBAC = {(r,f). r = Nurse \<and> is_readEntry f} \<union>  
        {(r,f). r = Nurse \<and> is_readSCR f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_appendEntry f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_deleteEntry f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_readEntry f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_readSCR f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_changeStatus f} \<union>  
        {(r,f). r = ClinicalPractitioner \<and> is_editEntry f} \<union>  
        {(r,f). r = Clerical \<and> is_createSCR f} \<union>  
        {(r,f). r = Clerical \<and> is_deleteSCR f} \<union>  
        {(r,f). r = Clerical \<and> is_addLR f}  \<union>  
        {(r,f). r = Clerical \<and> is_removeLR f}"

definition RBACPolicy :: RBACPolicy where
 "RBACPolicy = (\<lambda> (f,uc).
     if    ((roleOfOp f,f) \<in> RBAC \<and> \<lfloor>roleOfOp f\<rfloor> = uc (userOfOp f)) 
     then  \<lfloor>allow ()\<rfloor>
     else  \<lfloor>deny ()\<rfloor>)"

subsection \<open>The State Transitions and Output Function\<close>

subsubsection\<open>State Transition\<close>

fun OpSuccessDB :: "(Operation \<times> DB) \<rightharpoonup> DB"  where
   "OpSuccessDB (createSCR u r p,S) = (case S p of \<bottom> \<Rightarrow> \<lfloor>S(p\<mapsto>\<emptyset>)\<rfloor>
                                                 | \<lfloor>x\<rfloor> \<Rightarrow> \<lfloor>S\<rfloor>)" 
  |"OpSuccessDB ((appendEntry u r p ei e),S) = 
                                      (case S p of \<bottom>  \<Rightarrow> \<lfloor>S\<rfloor>
                                                | \<lfloor>x\<rfloor> \<Rightarrow> ((if ei \<in> (dom x) 
                                                              then \<lfloor>S\<rfloor> 
                                                              else \<lfloor>S(p \<mapsto> x(ei\<mapsto>e))\<rfloor>)))"
  |"OpSuccessDB ((deleteSCR u r p),S) =  (Some (S(p:=\<bottom>)))"
  |"OpSuccessDB ((deleteEntry u r p ei),S) = 
                                      (case S p of \<bottom> \<Rightarrow> \<lfloor>S\<rfloor>
                                                 | \<lfloor>x\<rfloor> \<Rightarrow> Some (S(p\<mapsto>(x(ei:=\<bottom>)))))"
  |"OpSuccessDB ((changeStatus u r p ei s),S) = 
                                      (case S p of \<bottom> \<Rightarrow> \<lfloor>S\<rfloor>
                                                 | \<lfloor>x\<rfloor> \<Rightarrow> (case x ei of
                                                            \<lfloor>e\<rfloor> \<Rightarrow> \<lfloor>S(p \<mapsto> x(ei\<mapsto>(s,snd e)))\<rfloor>
                                                          | \<bottom> \<Rightarrow> \<lfloor>S\<rfloor>))"
  |"OpSuccessDB ((editEntry u r p ei e),S) = 
                                      (case S p of \<bottom> \<Rightarrow>\<lfloor>S\<rfloor>
                                                 | \<lfloor>x\<rfloor> \<Rightarrow> (case x ei of
                                                                 \<lfloor>e\<rfloor> \<Rightarrow> \<lfloor>S(p\<mapsto>(x(ei\<mapsto>(e))))\<rfloor>
                                                              | \<bottom> \<Rightarrow> \<lfloor>S\<rfloor>))"
  |"OpSuccessDB (x,S) = \<lfloor>S\<rfloor>"


fun OpSuccessSigma :: "(Operation \<times> \<Sigma>) \<rightharpoonup> \<Sigma>" where
   "OpSuccessSigma (addLR u r p lr_id us,S) = 
                   (case S p of \<lfloor>lrs\<rfloor>  \<Rightarrow> (case (lrs lr_id) of 
                                               \<bottom>  \<Rightarrow> \<lfloor>S(p\<mapsto>(lrs(lr_id\<mapsto>us)))\<rfloor>                        
                                             | \<lfloor>x\<rfloor> \<Rightarrow> \<lfloor>S\<rfloor>)
                              | \<bottom> \<Rightarrow> \<lfloor>S(p\<mapsto>(Map.empty(lr_id\<mapsto>us)))\<rfloor>)"
  |"OpSuccessSigma (removeLR u r p lr_id,S) = 
                   (case S p of Some lrs \<Rightarrow> \<lfloor>S(p\<mapsto>(lrs(lr_id:=\<bottom>)))\<rfloor>
                              | \<bottom> \<Rightarrow> \<lfloor>S\<rfloor>)"
  |"OpSuccessSigma (x,S) = \<lfloor>S\<rfloor>"



fun OpSuccessUC :: "(Operation \<times> \<upsilon>) \<rightharpoonup> \<upsilon>" where
   "OpSuccessUC (f,u) = \<lfloor>u\<rfloor>"

subsubsection \<open>Output\<close>

type_synonym Output = unit  

fun OpSuccessOutput :: "(Operation) \<rightharpoonup> Output" where 
   "OpSuccessOutput x = \<lfloor>()\<rfloor>"
 

fun OpFailOutput :: "Operation \<rightharpoonup>  Output" where
   "OpFailOutput x = \<lfloor>()\<rfloor>"

subsection \<open>Combine All Parts\<close>

definition SE_LR_Policy :: "(Operation \<times> DB \<times> \<Sigma>, unit) policy" where
   "SE_LR_Policy = (\<lambda>(x,x). x)  o\<^sub>f  (SEPolicy \<Otimes>\<^sub>\<or>\<^sub>D LR_Policy) o (\<lambda>(a,b,c). ((a,b),a,c))"

definition SE_LR_FUN_Policy :: "(Operation \<times> DB \<times> \<Sigma>, unit) policy" where
  "SE_LR_FUN_Policy =  ((\<lambda>(x,x). x) o\<^sub>f (FunPolicy \<Otimes>\<^sub>\<or>\<^sub>D SE_LR_Policy) o (\<lambda>a. (a,a)))"

definition SE_LR_RBAC_Policy :: "(Operation \<times> DB \<times> \<Sigma> \<times> \<upsilon>, unit) policy" where
  "SE_LR_RBAC_Policy = (\<lambda>(x,x). x) 
                        o\<^sub>f (RBACPolicy \<Otimes>\<^sub>\<or>\<^sub>D SE_LR_FUN_Policy) 
                        o (\<lambda>(a,b,c,d). ((a,d),(a,b,c)))"

definition ST_Allow :: "Operation \<times> DB \<times> \<Sigma>  \<times> \<upsilon> \<rightharpoonup> Output \<times> DB \<times> \<Sigma> \<times> \<upsilon>" 
where     "ST_Allow = ((OpSuccessOutput \<Otimes>\<^sub>M (OpSuccessDB \<Otimes>\<^sub>S OpSuccessSigma \<Otimes>\<^sub>S OpSuccessUC)) 
                      o ( (\<lambda>(a,b,c). ((a),(a,b,c)))))"
      

definition ST_Deny :: "Operation \<times> DB \<times> \<Sigma> \<times> \<upsilon> \<rightharpoonup> Output \<times> DB \<times> \<Sigma> \<times> \<upsilon>" 
where     "ST_Deny = (\<lambda> (ope,sp,si,uc). Some ((), sp,si,uc))"


definition SE_LR_RBAC_ST_Policy :: "Operation \<times> DB \<times> \<Sigma>  \<times> \<upsilon> \<mapsto> Output \<times> DB \<times> \<Sigma> \<times> \<upsilon>"
where     "SE_LR_RBAC_ST_Policy =   ((\<lambda> (x,y).y)  
                                     o\<^sub>f ((ST_Allow,ST_Deny) \<Otimes>\<^sub>\<nabla> SE_LR_RBAC_Policy) 
                                     o (\<lambda>x.(x,x)))"

definition PolMon :: "Operation \<Rightarrow> (Output decision,DB \<times> \<Sigma> \<times> \<upsilon>) MON\<^sub>S\<^sub>E" 
where     "PolMon = (policy2MON SE_LR_RBAC_ST_Policy)" 

end
