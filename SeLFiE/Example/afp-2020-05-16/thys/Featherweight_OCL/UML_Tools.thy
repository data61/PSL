(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5 
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_Tools.thy ---
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
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

(* < *)
theory UML_Tools
imports UML_Logic
begin


lemmas substs1 = StrongEq_L_subst2_rev
                 foundation15[THEN iffD2, THEN StrongEq_L_subst2_rev]
                 foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                       THEN StrongEq_L_subst2_rev]]                
                 foundation14[THEN iffD2, THEN StrongEq_L_subst2_rev]
                 foundation13[THEN iffD2, THEN StrongEq_L_subst2_rev]
                
lemmas substs2 = StrongEq_L_subst3_rev
                 foundation15[THEN iffD2, THEN StrongEq_L_subst3_rev]
                 foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                       THEN StrongEq_L_subst3_rev]]                
                 foundation14[THEN iffD2, THEN StrongEq_L_subst3_rev]
                 foundation13[THEN iffD2, THEN StrongEq_L_subst3_rev]
                 
lemmas substs4 = StrongEq_L_subst4_rev
                 foundation15[THEN iffD2, THEN StrongEq_L_subst4_rev]
                 foundation7'[THEN iffD2, THEN foundation15[THEN iffD2, 
                                       THEN StrongEq_L_subst4_rev]]                
                 foundation14[THEN iffD2, THEN StrongEq_L_subst4_rev]
                 foundation13[THEN iffD2, THEN StrongEq_L_subst4_rev]

                 
lemmas substs = substs1 substs2 substs4 [THEN iffD2] substs4
thm substs
ML\<open>
fun ocl_subst_asm_tac ctxt  = FIRST'(map (fn C => (eresolve0_tac [C]) THEN' (simp_tac ctxt)) 
                                         @{thms "substs"})

val ocl_subst_asm = fn ctxt => SIMPLE_METHOD (ocl_subst_asm_tac ctxt 1); 

val _ = Theory.setup 
             (Method.setup (Binding.name "ocl_subst_asm") 
             (Scan.succeed (ocl_subst_asm)) 
             "ocl substition step") 
 
\<close>

lemma test1 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
apply(tactic "ocl_subst_asm_tac @{context} 1")
apply(simp)
done

lemma test2 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> B)"
by(ocl_subst_asm, simp)

lemma test3 : "\<tau> \<Turnstile> A \<Longrightarrow> \<tau> \<Turnstile> (A and A)"
by(ocl_subst_asm, simp)

lemma test4 : "\<tau> \<Turnstile> not A \<Longrightarrow> \<tau> \<Turnstile> (A and B \<triangleq> false)"
by(ocl_subst_asm, simp)

lemma test5 : "\<tau> \<Turnstile> (A \<triangleq> null) \<Longrightarrow> \<tau> \<Turnstile> (B \<triangleq> null) \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm,ocl_subst_asm,simp)

lemma test6 : "\<tau> \<Turnstile> not A \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm, simp)

lemma test7 : "\<not> (\<tau> \<Turnstile> (\<upsilon> A)) \<Longrightarrow> \<tau> \<Turnstile> (not B) \<Longrightarrow> \<not> (\<tau> \<Turnstile> (A and B))"
by(ocl_subst_asm,ocl_subst_asm,simp)

                  
    


(* a proof that shows that not everything is humpty dumpty ... *)
lemma X: "\<not> (\<tau> \<Turnstile> (invalid and B))"
apply(insert foundation8[of "\<tau>" "B"], elim disjE, 
      simp add:defined_bool_split, elim disjE)
apply(ocl_subst_asm, simp)
apply(ocl_subst_asm, simp)
apply(ocl_subst_asm, simp)
apply(ocl_subst_asm, simp)
done

(* easier is: *)
(* just to show the power of this extremely useful foundational rule:*)
lemma X': "\<not> (\<tau> \<Turnstile> (invalid and B))"
by(simp add:foundation10')
lemma Y: "\<not> (\<tau> \<Turnstile> (null and B))"
by(simp add: foundation10')
lemma Z: "\<not> (\<tau> \<Turnstile> (false and B))"
by(simp add: foundation10')
lemma Z': "(\<tau> \<Turnstile> (true and B)) = (\<tau> \<Turnstile> B)"
by(simp)

 
end

(* > *)
