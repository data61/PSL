(*****************************************************************************
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Monads.thy --- a base testing theory for sequential computations.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2005-2012 ETH Zurich, Switzerland
 *               2009-2017 Univ. Paris-Sud, France 
 *               2009-2015 Achim D. Brucker, Germany
 *               2015-2017 The University of Sheffield, UK
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

section \<open>Basic Monad Theory for Sequential Computations\<close>
theory 
  Monads 
  imports 
    Main
begin 

subsection\<open>General Framework for Monad-based Sequence-Test\<close>
text\<open>
  As such, Higher-order Logic as a purely functional specification formalism has no built-in 
  mechanism for state and state-transitions. Forms of testing involving state require therefore 
  explicit mechanisms for their treatment inside the logic; a well-known technique to model
  states inside purely functional languages are \emph{monads} made popular by Wadler and Moggi 
  and extensively used in Haskell. \HOL is powerful enough to represent the most important 
  standard monads; however, it is not possible to represent monads as such due to well-known 
  limitations of the Hindley-Milner type-system. 

  Here is a variant for state-exception monads, that models precisely transition functions with 
  preconditions. Next, we declare the state-backtrack-monad. In all of them, our concept of 
  i/o-stepping functions can be formulated; these are functions mapping input to a given monad. 
  Later on, we will build the usual concepts of:
  \begin{enumerate}
    \item deterministic i/o automata,
    \item non-deterministic i/o automata, and
    \item labelled transition systems (LTS)
  \end{enumerate}
\<close>

subsubsection\<open>State Exception Monads\<close>
type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = "'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)"        
      
definition bind_SE :: "('o,'\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('o \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
where     "bind_SE f g = (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> None 
                                        | Some (out, \<sigma>') \<Rightarrow> g out \<sigma>')"

notation bind_SE ("bind\<^sub>S\<^sub>E")
syntax
          "_bind_SE" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E"  
                                                                          ("(2 _ \<leftarrow> _; _)" [5,8,8]8)
translations 
          "x \<leftarrow> f; g" \<rightleftharpoons> "CONST bind_SE f (% x . g)"

definition unit_SE :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   ("(return _)" 8) 
where     "unit_SE e = (\<lambda>\<sigma>. Some(e,\<sigma>))"
notation   unit_SE ("unit\<^sub>S\<^sub>E")

definition fail\<^sub>S\<^sub>E :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "fail\<^sub>S\<^sub>E = (\<lambda>\<sigma>. None)"
notation   fail\<^sub>S\<^sub>E ("fail\<^sub>S\<^sub>E")

definition assert_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (bool, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assert_SE P = (\<lambda>\<sigma>. if P \<sigma> then Some(True,\<sigma>) else None)"
notation   assert_SE ("assert\<^sub>S\<^sub>E")

definition assume_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assume_SE P = (\<lambda>\<sigma>. if \<exists>\<sigma> . P \<sigma> then Some((), SOME \<sigma> . P \<sigma>) else None)"
notation   assume_SE ("assume\<^sub>S\<^sub>E")

definition if_SE :: "['\<sigma> \<Rightarrow> bool, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "if_SE c E F = (\<lambda>\<sigma>. if c \<sigma> then E \<sigma> else F \<sigma>)" 
notation   if_SE   ("if\<^sub>S\<^sub>E")

text\<open>
  The standard monad theorems about unit and associativity: 
\<close>

lemma bind_left_unit : "(x \<leftarrow> return a; k) = k"
  apply (simp add: unit_SE_def bind_SE_def)
  done

lemma bind_right_unit: "(x \<leftarrow> m; return x) = m"
  apply (simp add:  unit_SE_def bind_SE_def)
  apply (rule ext)
  subgoal for "\<sigma>"
    apply (case_tac "m \<sigma>")
     apply ( simp_all)
    done
  done

lemma bind_assoc: "(y \<leftarrow> (x \<leftarrow> m; k); h) = (x \<leftarrow> m; (y \<leftarrow> k; h))"
  apply (simp add: unit_SE_def bind_SE_def)
  apply (rule ext)
  subgoal for "\<sigma>"
    apply (case_tac "m \<sigma>", simp_all)
    subgoal for a
      apply (case_tac "a", simp_all)
      done
    done
  done

text\<open>
  In order to express test-sequences also on the object-level and to make our theory amenable to 
  formal reasoning over test-sequences, we represent them as lists of input and generalize the 
  bind-operator of the state-exception monad accordingly. The approach is straightforward, but 
  comes with a price: we have to encapsulate all input and output data into one type. Assume that 
  we have a typed interface to a module with the operations $op_1$, $op_2$, \ldots, $op_n$ with 
  the inputs $\iota_1$, $\iota_2$, \ldots, $\iota_n$ (outputs are treated analogously). Then we 
  can encode for this interface the general input - type:
  \begin{displaymath}
    \texttt{datatype}\ \texttt{in}\ =\ op_1\ ::\ \iota_1\ |\ ...\ |\ \iota_n
  \end{displaymath}
  Obviously, we loose some type-safety in this approach; we have to express that in traces only 
  \emph{corresponding} input and output belonging to the same operation will occur; this form 
  of side-conditions have to be expressed inside \HOL. From the user perspective, this will not 
  make much difference, since junk-data resulting from too weak typing can be ruled out by adopted
  front-ends. 
\<close>

text\<open>
  In order to express test-sequences also on the object-level and to make our theory amenable to 
  formal reasoning over test-sequences, we represent them as lists of input and generalize the 
  bind-operator of the state-exception monad accordingly. Thus, the notion of test-sequence
  is mapped to the notion of a \emph{computation}, a semantic notion; at times we will use 
  reifications of computations, \ie{} a data-type in order to make computation amenable to
  case-splitting and meta-theoretic reasoning. To this end,  we have to encapsulate all input 
  and output data into one type. Assume that we have a typed interface to a module with
  the operations $op_1$, $op_2$, \ldots, $op_n$ with the inputs  $\iota_1$, $\iota_2$, \ldots, 
  $\iota_n$ (outputs are treated analogously).
   Then we can encode for this interface the general input - type:
  \begin{displaymath}
  \texttt{datatype}\ \texttt{in}\ =\ op_1\ ::\ \iota_1\ |\ ...\ |\ \iota_n
  \end{displaymath}
  Obviously, we loose some type-safety in this approach; we have to express
  that in traces only \emph{corresponding} input and output belonging to the 
  same operation will occur; this form of side-conditions have to be expressed
  inside \HOL. From the user perspective, this will not make much difference,
  since junk-data resulting from too weak typing can be ruled out by adopted
  front-ends.\<close>


text\<open>Note that the subsequent notion of a test-sequence allows the io stepping 
function (and the special case of a program under test) to stop execution 
\emph{within} the sequence; such premature terminations are characterized by an 
output list which is shorter than the input list. Note that our primary
notion of multiple execution ignores failure and reports failure
steps only by missing results ...\<close>


fun    mbind :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"  
  where "mbind [] iostep \<sigma> = Some([], \<sigma>)" |
    "mbind (a#H) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> Some([], \<sigma>)
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind H iostep \<sigma>' of 
                                          None    \<Rightarrow> Some([out],\<sigma>') 
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

text\<open>As mentioned, this definition is fail-safe; in case of an exception, 
the current state is maintained, no result is reported. 
An alternative is the fail-strict variant \<open>mbind'\<close> defined below.\<close>

lemma mbind_unit [simp]: "mbind [] f = (return [])"
  by(rule ext, simp add: unit_SE_def)

    
lemma mbind_nofailure [simp]: "mbind S f \<sigma> \<noteq> None"
  apply (rule_tac x=\<sigma> in spec)
  apply (induct S)
  using mbind.simps(1) apply force
  apply(simp add:unit_SE_def)
  apply(safe)[1]
  subgoal for a S x
    apply (case_tac "f a x")
     apply(simp)
    apply(safe)[1]
    subgoal for aa b
      apply (erule_tac x="b" in allE)
      apply (erule exE)+
      apply (simp)
      done 
    done
  done

text\<open>The fail-strict version of \<open>mbind'\<close> looks as follows:\<close>
fun    mbind' :: "'\<iota> list  \<Rightarrow>  ('\<iota> \<Rightarrow> ('o,'\<sigma>) MON\<^sub>S\<^sub>E) \<Rightarrow> ('o list,'\<sigma>) MON\<^sub>S\<^sub>E"
where "mbind' [] iostep \<sigma> = Some([], \<sigma>)" |
      "mbind' (a#H) iostep \<sigma> = 
                (case iostep a \<sigma> of 
                     None   \<Rightarrow> None
                  |  Some (out, \<sigma>') \<Rightarrow> (case mbind H iostep \<sigma>' of 
                                          None    \<Rightarrow> None   \<comment> \<open>fail-strict\<close>
                                        | Some(outs,\<sigma>'') \<Rightarrow> Some(out#outs,\<sigma>'')))"

text\<open>
  mbind' as failure strict operator can be seen as a foldr on bind---if the types would  
  match \ldots 
\<close>

definition try_SE :: "('o,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> ('o option,'\<sigma>) MON\<^sub>S\<^sub>E" 
where     "try_SE ioprog = (\<lambda>\<sigma>. case ioprog \<sigma> of
                                      None \<Rightarrow> Some(None, \<sigma>)
                                    | Some(outs, \<sigma>') \<Rightarrow> Some(Some outs, \<sigma>'))" 
text\<open>In contrast @{term mbind} as a failure safe operator can roughly be seen 
       as a @{term foldr} on bind - try:
       \<open>m1 ; try m2 ; try m3; ...\<close>. Note, that the rough equivalence only holds for
       certain predicates in the sequence - length equivalence modulo None,
       for example. However, if a conditional is added, the equivalence
       can be made precise:\<close>


lemma mbind_try: 
  "(x \<leftarrow> mbind (a#S) F; M x) = 
   (a' \<leftarrow> try_SE(F a); 
      if a' = None 
      then (M [])
      else (x \<leftarrow> mbind S F; M (the a' # x)))"
  apply (rule ext)
  apply (simp add: bind_SE_def try_SE_def)
  subgoal for x 
    apply (case_tac "F a x")
     apply(simp)
    apply (safe)[1]
    apply (simp add: bind_SE_def try_SE_def)
    subgoal for aa b
      apply (case_tac "mbind S F b") 
       apply (auto)
      done
    done 
  done

text\<open>On this basis, a symbolic evaluation scheme can be established
  that reduces @{term mbind}-code to @{term try_SE}-code and If-cascades.\<close>


definition alt_SE    :: "[('o, '\<sigma>)MON\<^sub>S\<^sub>E, ('o, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   (infixl "\<sqinter>\<^sub>S\<^sub>E" 10)
where     "(f \<sqinter>\<^sub>S\<^sub>E g) = (\<lambda> \<sigma>. case f \<sigma> of None \<Rightarrow> g \<sigma>
                                      | Some H \<Rightarrow> Some H)"

definition malt_SE   :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E list \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "malt_SE S = foldr alt_SE S fail\<^sub>S\<^sub>E"
notation   malt_SE ("\<Sqinter>\<^sub>S\<^sub>E")

lemma malt_SE_mt [simp]: "\<Sqinter>\<^sub>S\<^sub>E [] = fail\<^sub>S\<^sub>E"
  by(simp add: malt_SE_def)

lemma malt_SE_cons [simp]: "\<Sqinter>\<^sub>S\<^sub>E (a # S) = (a \<sqinter>\<^sub>S\<^sub>E (\<Sqinter>\<^sub>S\<^sub>E S))"
  by(simp add: malt_SE_def)

subsubsection\<open>State-Backtrack Monads\<close>
text\<open>This subsection is still rudimentary and as such an interesting
  formal analogue to the previous monad definitions. It is doubtful that it is
  interesting for testing and as a computational structure at all. 
  Clearly more relevant is ``sequence'' instead of ``set,'' which would
  rephrase Isabelle's internal tactic concept. 
\<close>


type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>B = "'\<sigma> \<Rightarrow> ('o \<times> '\<sigma>) set"

definition bind_SB :: "('o, '\<sigma>)MON\<^sub>S\<^sub>B \<Rightarrow> ('o \<Rightarrow>  ('o', '\<sigma>)MON\<^sub>S\<^sub>B) \<Rightarrow> ('o', '\<sigma>)MON\<^sub>S\<^sub>B"
where     "bind_SB f g \<sigma> = \<Union> ((\<lambda>(out, \<sigma>). (g out \<sigma>)) ` (f \<sigma>))"
notation   bind_SB ("bind\<^sub>S\<^sub>B")

definition unit_SB   :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>B" ("(returns _)" 8) 
where     "unit_SB e = (\<lambda>\<sigma>. {(e,\<sigma>)})"
notation   unit_SB ("unit\<^sub>S\<^sub>B")

syntax "_bind_SB" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>B,('o','\<sigma>)MON\<^sub>S\<^sub>B] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B" 
                                                                         ("(2 _ := _; _)" [5,8,8]8)
translations 
          "x := f; g" \<rightleftharpoons> "CONST bind_SB f (% x . g)"

lemma bind_left_unit_SB : "(x := returns a; m) = m"
  apply (rule ext)
  apply (simp add: unit_SB_def bind_SB_def)
  done

lemma bind_right_unit_SB: "(x := m; returns x) = m"
  apply (rule ext)
  apply (simp add: unit_SB_def bind_SB_def)
done

lemma bind_assoc_SB: "(y := (x := m; k); h) = (x := m; (y := k; h))"
  apply (rule ext)
  apply (simp add: unit_SB_def bind_SB_def split_def)
done

subsubsection\<open>State Backtrack Exception Monad\<close>
text\<open>
  The following combination of the previous two Monad-Constructions allows for the semantic 
  foundation of a simple generic assertion language in the style of Schirmer's Simpl-Language or 
  Rustan Leino's Boogie-PL language. The key is to use the exceptional element None for violations 
  of the assert-statement. 
\<close>
type_synonym  ('o, '\<sigma>) MON\<^sub>S\<^sub>B\<^sub>E = "'\<sigma> \<Rightarrow> (('o \<times> '\<sigma>) set) option"
      
definition bind_SBE :: "('o,'\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E \<Rightarrow> ('o \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E) \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E" 
where     "bind_SBE f g = (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> None 
                                         | Some S \<Rightarrow> (let S' = (\<lambda>(out, \<sigma>'). g out \<sigma>') ` S
                                                      in  if None \<in> S' then None
                                                          else Some(\<Union> (the ` S'))))"

syntax "_bind_SBE" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E" 
                                                                         ("(2 _ :\<equiv> _; _)" [5,8,8]8)
translations 
          "x :\<equiv> f; g" \<rightleftharpoons> "CONST bind_SBE f (% x . g)"

definition unit_SBE   :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"   ("(returning _)" 8) 
where     "unit_SBE e = (\<lambda>\<sigma>. Some({(e,\<sigma>)}))"

definition assert_SBE   :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "assert_SBE e = (\<lambda>\<sigma>. if e \<sigma> then Some({((),\<sigma>)})
                                      else None)"
notation   assert_SBE ("assert\<^sub>S\<^sub>B\<^sub>E")

definition assume_SBE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "assume_SBE e = (\<lambda>\<sigma>. if e \<sigma> then Some({((),\<sigma>)})
                                      else Some {})"
notation   assume_SBE ("assume\<^sub>S\<^sub>B\<^sub>E")

definition havoc_SBE :: " (unit, '\<sigma>)MON\<^sub>S\<^sub>B\<^sub>E"
where     "havoc_SBE = (\<lambda>\<sigma>.  Some({x. True}))"
notation   havoc_SBE ("havoc\<^sub>S\<^sub>B\<^sub>E")

lemma bind_left_unit_SBE : "(x :\<equiv> returning a; m) = m"
  apply (rule ext)
  apply (simp add: unit_SBE_def bind_SBE_def)
  done

lemma bind_right_unit_SBE: "(x :\<equiv> m; returning x) = m"
  apply (rule ext)
  apply (simp add: unit_SBE_def bind_SBE_def)
  subgoal for x 
    apply (case_tac "m x")
     apply (simp_all add:Let_def)
    apply (rule HOL.ccontr)
    apply (simp add: Set.image_iff)
    done
  done 
   
lemmas aux = trans[OF HOL.neq_commute,OF Option.not_None_eq]

lemma bind_assoc_SBE: "(y :\<equiv> (x :\<equiv> m; k); h) = (x :\<equiv> m; (y :\<equiv> k; h))"
proof (rule ext, simp add: unit_SBE_def bind_SBE_def, rename_tac x,
    case_tac "m x", simp_all add: Let_def Set.image_iff, safe,goal_cases)
  case (1 x a aa b ab ba a b)
  then show ?case  by(rule_tac x="(a, b)" in bexI, simp_all)
next
  case (2 x a aa b ab ba)
  then show ?case  
    apply (rule_tac x="(aa, b)" in bexI, simp_all add:split_def)
    apply (erule_tac x="(aa,b)" in ballE)
     apply (auto simp: aux image_def split_def intro!: rev_bexI)
    done
next
  case (3 x a a b)
  then show ?case  by(rule_tac x="(a, b)" in bexI, simp_all)
next
  case (4 x a aa b)
  then show ?case 
    apply (erule_tac Q="None = X" for X in contrapos_pp)
    apply (erule_tac x="(aa,b)" and P="\<lambda> x. None \<noteq> case_prod (\<lambda>out. k) x" in ballE)
     apply (auto simp: aux image_def split_def intro!: rev_bexI)
    done
next
  case (5 x a aa b ab ba a b)
  then show ?case  apply simp apply ((erule_tac x="(ab,ba)" in ballE)+)
       apply (simp_all add: aux, (erule exE)+, simp add:split_def)
    apply (erule rev_bexI, case_tac "None\<in>(\<lambda>p. h(snd p))`y",auto simp:split_def)
    done
      
next
  case (6 x a aa b a b)
  then show ?case    apply simp apply ((erule_tac x="(a,b)" in ballE)+)
       apply (simp_all add: aux, (erule exE)+, simp add:split_def)
    apply (erule rev_bexI, case_tac "None\<in>(\<lambda>p. h(snd p))`y",auto simp:split_def)
    done
qed 
  
  

subsection\<open>Valid Test Sequences in the State Exception Monad\<close>
text\<open>
  This is still an unstructured merge of executable monad concepts and specification oriented 
  high-level properties initiating test procedures. 
\<close>

definition valid_SE :: "'\<sigma> \<Rightarrow> (bool,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> bool" (infix "\<Turnstile>" 15)
where "(\<sigma> \<Turnstile> m) = (m \<sigma> \<noteq> None \<and> fst(the (m \<sigma>)))"
text\<open>
  This notation consideres failures as valid---a definition inspired by I/O conformance. 
  Note that it is not possible to define this concept once and for all in a Hindley-Milner 
  type-system. For the moment, we present it only for the state-exception monad, although for 
  the same definition, this notion is applicable to other monads as well.  
\<close>

lemma syntax_test : 
  "\<sigma> \<Turnstile> (os \<leftarrow> (mbind \<iota>s ioprog); return(length \<iota>s = length os))"
oops


lemma valid_true[simp]: "(\<sigma> \<Turnstile> (s \<leftarrow> return x ; return (P s))) = P x"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def)

text\<open>Recall mbind\_unit for the base case.\<close>

lemma valid_failure: "ioprog a \<sigma> = None \<Longrightarrow> 
                                   (\<sigma> \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; M s)) = 
                                   (\<sigma> \<Turnstile> (M []))"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def)



lemma valid_failure': "A \<sigma> = None \<Longrightarrow> \<not>(\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)))"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def)

lemma valid_successElem: (* atomic boolean Monad "Query Functions" *) 
                         "M \<sigma> = Some(f \<sigma>,\<sigma>) \<Longrightarrow>  (\<sigma> \<Turnstile> M) = f \<sigma>"
  by(simp add: valid_SE_def unit_SE_def bind_SE_def )

lemma valid_success:  "ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow> 
                                  (\<sigma>  \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; M s)) = 
                                  (\<sigma>' \<Turnstile> (s \<leftarrow> mbind S ioprog ; M (b#s)))"
  apply (simp add: valid_SE_def unit_SE_def bind_SE_def )
  apply (cases "mbind S ioprog \<sigma>'", auto)
  done

lemma valid_success'': "ioprog a \<sigma> = Some(b,\<sigma>') \<Longrightarrow>
                                    (\<sigma>  \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; return (P s))) =
                                    (\<sigma>' \<Turnstile> (s \<leftarrow> mbind S ioprog ; return (P (b#s))))"
  apply (simp add: valid_SE_def unit_SE_def bind_SE_def )
  apply (cases "mbind S ioprog \<sigma>'")
   apply (simp_all)
  apply (auto)
  done

lemma valid_success':  "A \<sigma> = Some(b,\<sigma>') \<Longrightarrow> (\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s))) = (\<sigma>' \<Turnstile> (M b))"
by(simp add: valid_SE_def unit_SE_def bind_SE_def )

lemma valid_both: "(\<sigma> \<Turnstile> (s \<leftarrow> mbind (a#S) ioprog ; return (P s))) =
                         (case ioprog a \<sigma> of
                               None \<Rightarrow> (\<sigma>  \<Turnstile> (return (P [])))
                             | Some(b,\<sigma>') \<Rightarrow> (\<sigma>'  \<Turnstile> (s \<leftarrow> mbind S ioprog ; return (P (b#s)))))"
  apply (case_tac "ioprog a \<sigma>")
   apply (simp_all add: valid_failure valid_success'' split: prod.splits)
  done

lemma valid_propagate_1 [simp]: "(\<sigma> \<Turnstile> (return P)) = (P)"
  by(auto simp: valid_SE_def unit_SE_def)
    
lemma valid_propagate_2: "\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> v \<sigma>'. the(A \<sigma>) = (v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
  apply (auto simp: valid_SE_def unit_SE_def bind_SE_def)
  apply (cases "A \<sigma>")
   apply (simp_all)
  apply (drule_tac x="A \<sigma>" and f=the in arg_cong)
  apply (simp) 
  apply (rename_tac a b aa )
  apply (rule_tac x="fst aa" in exI)
  apply (rule_tac x="snd aa" in exI)
  by (auto)          
       
lemma valid_propagate_2': "\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow>  \<exists> a. (A \<sigma>) = Some a \<and> (snd a) \<Turnstile> (M (fst a))"
  apply (auto simp: valid_SE_def unit_SE_def bind_SE_def)
  apply (cases "A \<sigma>")
   apply (simp_all)
  apply (simp_all split: prod.splits)
  apply (drule_tac x="A \<sigma>" and f=the in arg_cong)
  apply (simp)
  apply (rename_tac a b aa x1 x2)
  apply (rule_tac x="fst aa" in exI)
  apply (rule_tac x="snd aa" in exI)
  apply (auto)
  done

lemma valid_propagate_2'': "\<sigma> \<Turnstile> ((s \<leftarrow> A ; M s)) \<Longrightarrow> \<exists> v \<sigma>'. A \<sigma> = Some(v,\<sigma>') \<and> \<sigma>' \<Turnstile> (M v)"
  apply (auto simp: valid_SE_def unit_SE_def bind_SE_def)
  apply (cases "A \<sigma>")
   apply (simp_all)
  apply (drule_tac x="A \<sigma>" and f=the in arg_cong)
  apply (simp)
  apply (rename_tac a b aa )
  apply (rule_tac x="fst aa" in exI)
  apply (rule_tac x="snd aa" in exI)
  apply (auto)
  done

lemma valid_propoagate_3[simp]: "(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. Some (f \<sigma>, \<sigma>))) = (f \<sigma>\<^sub>0)"
  by(simp add: valid_SE_def )

lemma valid_propoagate_3'[simp]: "\<not>(\<sigma>\<^sub>0 \<Turnstile> (\<lambda>\<sigma>. None))"
  by(simp add: valid_SE_def )

lemma assert_disch1 :" P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) = (\<sigma> \<Turnstile> (M True))"
  by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch2 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P ; M s))"
  by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_disch3 :" \<not> P \<sigma> \<Longrightarrow> \<not> (\<sigma> \<Turnstile> (assert\<^sub>S\<^sub>E P))"
  by(auto simp: bind_SE_def assert_SE_def valid_SE_def)

lemma assert_D : "(\<sigma> \<Turnstile> (x \<leftarrow> assert\<^sub>S\<^sub>E P; M x)) \<Longrightarrow> P \<sigma> \<and> (\<sigma> \<Turnstile> (M True))"
  by(auto simp: bind_SE_def assert_SE_def valid_SE_def split: HOL.if_split_asm)
    
lemma assume_D : "(\<sigma> \<Turnstile> (x \<leftarrow> assume\<^sub>S\<^sub>E P; M x)) \<Longrightarrow> \<exists> \<sigma>. (P \<sigma> \<and>  \<sigma> \<Turnstile> (M ()))"
  apply (auto simp: bind_SE_def assume_SE_def valid_SE_def split: HOL.if_split_asm)
  apply (rule_tac x="Eps P" in exI)
  apply (auto)[1]
  subgoal for x a b 
    apply (rule_tac x="True" in exI, rule_tac x="b" in exI)
    apply (subst Hilbert_Choice.someI)
     apply (assumption)
    apply (simp)
    done
  apply (subst Hilbert_Choice.someI,assumption)
  apply (simp)
  done

text\<open>
  These two rule prove that the SE Monad in connection with the notion of valid sequence is 
  actually sufficient for a representation of a Boogie-like language. The SBE monad with explicit
  sets of states---to be shown below---is strictly speaking not necessary (and will therefore
  be discontinued in the development). 
\<close>
  
lemma if_SE_D1 : "P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> if\<^sub>S\<^sub>E P B\<^sub>1 B\<^sub>2) = (\<sigma> \<Turnstile> B\<^sub>1)"
  by(auto simp: if_SE_def valid_SE_def)
    
lemma if_SE_D2 : "\<not> P \<sigma> \<Longrightarrow> (\<sigma> \<Turnstile> if\<^sub>S\<^sub>E P B\<^sub>1 B\<^sub>2) = (\<sigma> \<Turnstile> B\<^sub>2)"
  by(auto simp: if_SE_def valid_SE_def)
    
lemma if_SE_split_asm : " (\<sigma> \<Turnstile> if\<^sub>S\<^sub>E P B\<^sub>1 B\<^sub>2) = ((P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>1)) \<or> (\<not> P \<sigma> \<and> (\<sigma> \<Turnstile> B\<^sub>2)))"
  by(cases "P \<sigma>",auto simp: if_SE_D1 if_SE_D2)
    
lemma if_SE_split : " (\<sigma> \<Turnstile> if\<^sub>S\<^sub>E P B\<^sub>1 B\<^sub>2) = ((P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>1)) \<and> (\<not> P \<sigma> \<longrightarrow> (\<sigma> \<Turnstile> B\<^sub>2)))"
  by(cases "P \<sigma>", auto simp: if_SE_D1 if_SE_D2)
    
lemma [code]: "(\<sigma> \<Turnstile> m) = (case (m \<sigma>) of None  \<Rightarrow> False | (Some (x,y))  \<Rightarrow> x)"
  apply (simp add: valid_SE_def)
  apply (cases "m \<sigma> = None")
   apply (simp_all)
  apply (insert not_None_eq)
  apply (auto)
  done
    
subsection\<open>Valid Test Sequences in the State Exception Backtrack Monad\<close>
text\<open>
  This is still an unstructured merge of executable monad concepts and specification oriented 
  high-level properties initiating test procedures. 
\<close>
  
definition valid_SBE :: "'\<sigma> \<Rightarrow> ('a,'\<sigma>) MON\<^sub>S\<^sub>B\<^sub>E \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>S\<^sub>B\<^sub>E" 15)
  where "\<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E m \<equiv> (m \<sigma> \<noteq> None)"
text\<open>
  This notation considers all non-failures as valid. 
\<close>
  
lemma assume_assert: "(\<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E ( _ :\<equiv> assume\<^sub>S\<^sub>B\<^sub>E P ; assert\<^sub>S\<^sub>B\<^sub>E Q)) = (P \<sigma> \<longrightarrow> Q \<sigma>)" 
  by(simp add: valid_SBE_def assume_SBE_def assert_SBE_def bind_SBE_def)
    
lemma assert_intro: "Q \<sigma> \<Longrightarrow> \<sigma> \<Turnstile>\<^sub>S\<^sub>B\<^sub>E (assert\<^sub>S\<^sub>B\<^sub>E Q)"
  by(simp add: valid_SBE_def assume_SBE_def assert_SBE_def bind_SBE_def)
    
    
end
