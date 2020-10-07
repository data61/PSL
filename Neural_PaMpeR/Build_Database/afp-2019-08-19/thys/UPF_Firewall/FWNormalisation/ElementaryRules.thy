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

subsection \<open>Elementary Firewall Policy Transformation Rules\<close> 
theory 
  ElementaryRules
  imports 
    FWNormalisationCore
begin
  
  
text\<open>
  This theory contains those elementary transformation rules which are presented in the ICST 
  2010 paper~\cite{brucker.ea:firewall:2010}. They are not used elsewhere.
\<close>
  
lemma elem1:
  "C (AllowPortFromTo x y p \<oplus> DenyAllFromTo x y) = C (DenyAllFromTo x y)"
  by (rule ext, auto simp: PLemmas)
    
    
lemma elem2:
  "C ((a \<oplus> b) \<oplus> c) = C (a \<oplus> (b \<oplus> c))"
  by (simp add: C.simps) 
    
lemma elem3:
  "C (AllowPortFromTo x y a \<oplus> AllowPortFromTo x y b) = 
  C (AllowPortFromTo x y b \<oplus> AllowPortFromTo x y a)"
  by (rule ext, auto simp: PLemmas)
    
lemma elem4:
  "C (a \<oplus> DenyAll) = C DenyAll"
  by (rule ext, auto simp: PLemmas)
    
lemma elem5:
  "C (DenyAllFromTo x y \<oplus> DenyAllFromTo u v) = C (DenyAllFromTo u v \<oplus> DenyAllFromTo x y)"
  by (rule ext, auto simp: PLemmas)
    
    
lemma elem6: 
  "dom (C a) \<inter> dom (C b) = {} \<Longrightarrow> C (a \<oplus> b) = C (b \<oplus> a)"
  by (rule ext, metis C.simps(4) map_add_comm)
    
end
