(*****************************************************************************
 * Clean
 *                                                                            
 * HOL-TestGen --- theorem-prover based test case generation
 *                 http://www.brucker.ch/projects/hol-testgen/
 *                                                                            
 * Copyright (c) 2005-2007 ETH Zurich, Switzerland
 *               2009-2017 Univ. Paris-Sud, France 
 *               2009-2012 Achim D. Brucker, Germany
 *               2015-2017 University Sheffield, UK
 *               2018-2019 Université Paris-Saclay, Univ. Paris-Sud, France
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

(*
 * Monads --- a base testing theory for sequential computations.
 * This file is part of HOL-TestGen.
 *)

theory MonadSE
  imports Main
begin
        
section\<open>Definition : Standard State Exception Monads\<close>
text\<open>State exception monads in our sense are a direct, pure formulation
of automata with a partial transition function.\<close>

subsection\<open>Definition : Core Types and Operators\<close>

type_synonym ('o, '\<sigma>) MON\<^sub>S\<^sub>E = "'\<sigma> \<rightharpoonup> ('o \<times> '\<sigma>)" (* = '\<sigma> \<Rightarrow> ('o \<times> '\<sigma>)option *)       
      
definition bind_SE :: "('o,'\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('o \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E) \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
where     "bind_SE f g = (\<lambda>\<sigma>. case f \<sigma> of None \<Rightarrow> None 
                                        | Some (out, \<sigma>') \<Rightarrow> g out \<sigma>')"

notation bind_SE ("bind\<^sub>S\<^sub>E")

syntax    (xsymbols)
          "_bind_SE" :: "[pttrn,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(2 _ \<leftarrow> _; _)" [5,8,8]8)
translations 
          "x \<leftarrow> f; g" == "CONST bind_SE f (% x . g)"

definition unit_SE :: "'o \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   ("(result _)" 8) 
where     "unit_SE e = (\<lambda>\<sigma>. Some(e,\<sigma>))"
notation   unit_SE ("unit\<^sub>S\<^sub>E")

text\<open>In the following, we prove the required Monad-laws\<close>

lemma bind_right_unit[simp]: "(x \<leftarrow> m; result x) = m"
  apply (simp add:  unit_SE_def bind_SE_def)
  apply (rule ext)
  apply (case_tac "m \<sigma>", simp_all)
  done

lemma bind_left_unit [simp]: "(x \<leftarrow> result c; P x) = P c"
  by (simp add: unit_SE_def bind_SE_def)
  
lemma bind_assoc[simp]: "(y \<leftarrow> (x \<leftarrow> m; k x); h y) = (x \<leftarrow> m; (y \<leftarrow> k x; h y))"
  apply (simp add: unit_SE_def bind_SE_def, rule ext)
  apply (case_tac "m \<sigma>", simp_all)
  apply (case_tac "a", simp_all)
  done
    
subsection\<open>Definition : More Operators and their Properties\<close>

definition fail_SE :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "fail_SE = (\<lambda>\<sigma>. None)" 
notation   fail_SE ("fail\<^sub>S\<^sub>E")

definition assert_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (bool, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assert_SE P = (\<lambda>\<sigma>. if P \<sigma> then Some(True,\<sigma>) else None)"
notation   assert_SE ("assert\<^sub>S\<^sub>E")

definition assume_SE :: "('\<sigma> \<Rightarrow> bool) \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "assume_SE P = (\<lambda>\<sigma>. if \<exists>\<sigma> . P \<sigma> then Some((), SOME \<sigma> . P \<sigma>) else None)"
notation   assume_SE ("assume\<^sub>S\<^sub>E")


lemma bind_left_fail_SE[simp] : "(x \<leftarrow> fail\<^sub>S\<^sub>E; P x) = fail\<^sub>S\<^sub>E"
  by (simp add: fail_SE_def bind_SE_def)


text\<open>We also provide a "Pipe-free" - variant of the bind operator.
Just a "standard" programming sequential operator without output frills.\<close>
(* TODO: Eliminate/Modify this. Is a consequence of the Monad-Instantiation. *)


definition bind_SE' :: "('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<beta>, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<beta>, '\<sigma>)MON\<^sub>S\<^sub>E" (infixr ";-" 60)
where     "f ;- g = (_ \<leftarrow> f ; g)"

lemma bind_assoc'[simp]: "((m;- k);- h ) = (m;- (k;- h))"
by(simp add:bind_SE'_def)


lemma bind_left_unit' [simp]: "((result c);- P) = P"
  by (simp add:  bind_SE'_def)
  

lemma bind_left_fail_SE'[simp]: "(fail\<^sub>S\<^sub>E;- P) = fail\<^sub>S\<^sub>E"
  by (simp add: bind_SE'_def)

lemma bind_right_unit'[simp]: "(m;- (result ())) = m"
  by (simp add:  bind_SE'_def)
          
text\<open>The bind-operator in the state-exception monad yields already
       a semantics for the concept of an input sequence on the meta-level:\<close>
lemma     syntax_test: "(o1 \<leftarrow> f1 ; o2 \<leftarrow> f2; result (post o1 o2)) = X"
oops
  
definition yield\<^sub>C :: "('a  \<Rightarrow> 'b) \<Rightarrow>  ('b,'a ) MON\<^sub>S\<^sub>E"
    where "yield\<^sub>C f \<equiv> (\<lambda>\<sigma>. Some(f \<sigma>, \<sigma>))"


definition try_SE :: "('o,'\<sigma>) MON\<^sub>S\<^sub>E \<Rightarrow> ('o option,'\<sigma>) MON\<^sub>S\<^sub>E" ("try\<^sub>S\<^sub>E")
where     "try\<^sub>S\<^sub>E ioprog = (\<lambda>\<sigma>. case ioprog \<sigma> of
                                      None \<Rightarrow> Some(None, \<sigma>)
                                    | Some(outs, \<sigma>') \<Rightarrow> Some(Some outs, \<sigma>'))" 
text\<open>In contrast, mbind as a failure safe operator can roughly be seen 
       as a foldr on bind - try:
       m1 ; try m2 ; try m3; ... Note, that the rough equivalence only holds for
       certain predicates in the sequence - length equivalence modulo None,
       for example. However, if a conditional is added, the equivalence
       can be made precise:\<close>
  
text\<open>On this basis, a symbolic evaluation scheme can be established
  that reduces mbind-code to try\_SE\_code and ite-cascades.\<close>

definition alt_SE :: "[('o, '\<sigma>)MON\<^sub>S\<^sub>E, ('o, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"   (infixl "\<sqinter>\<^sub>S\<^sub>E" 10)
where     "(f \<sqinter>\<^sub>S\<^sub>E g) = (\<lambda> \<sigma>. case f \<sigma> of None \<Rightarrow> g \<sigma>
                                      | Some H \<Rightarrow> Some H)"

definition malt_SE :: "('o, '\<sigma>)MON\<^sub>S\<^sub>E list \<Rightarrow> ('o, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "malt_SE S = foldr alt_SE S fail\<^sub>S\<^sub>E"
notation   malt_SE ("\<Sqinter>\<^sub>S\<^sub>E")

lemma malt_SE_mt [simp]: "\<Sqinter>\<^sub>S\<^sub>E [] = fail\<^sub>S\<^sub>E"
by(simp add: malt_SE_def)

lemma malt_SE_cons [simp]: "\<Sqinter>\<^sub>S\<^sub>E (a # S) = (a \<sqinter>\<^sub>S\<^sub>E (\<Sqinter>\<^sub>S\<^sub>E S))"
by(simp add: malt_SE_def)


subsection\<open>Definition : Programming Operators and their Properties\<close>

definition  "skip\<^sub>S\<^sub>E = unit\<^sub>S\<^sub>E ()"

definition if_SE :: "['\<sigma> \<Rightarrow> bool, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E, ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('\<alpha>, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "if_SE c E F = (\<lambda>\<sigma>. if c \<sigma> then E \<sigma> else F \<sigma>)" 

syntax    (xsymbols)
          "_if_SE" :: "['\<sigma> \<Rightarrow> bool,('o,'\<sigma>)MON\<^sub>S\<^sub>E,('o','\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('o','\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(if\<^sub>S\<^sub>E _ then _ else _fi)" [5,8,8]8)
translations 
          "(if\<^sub>S\<^sub>E cond then T1 else T2 fi)" == "CONST if_SE cond T1 T2"


subsection\<open>Theory of a Monadic While\<close>

text\<open>Prerequisites\<close>
fun replicator :: "[('a, '\<sigma>)MON\<^sub>S\<^sub>E, nat] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" (infixr "^^^" 60)
where     "f ^^^ 0      = (result ())"
        | "f ^^^ (Suc n) = (f ;- f ^^^  n)"


fun replicator2 :: "[('a, '\<sigma>)MON\<^sub>S\<^sub>E, nat, ('b, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> ('b, '\<sigma>)MON\<^sub>S\<^sub>E" (infixr "^:^" 60)
where     "(f ^:^ 0) M      = (M )"
        | "(f ^:^ (Suc n)) M = (f ;- ((f ^:^  n) M))"


text\<open>First Step : Establishing an embedding between partial functions and relations\<close> 
(* plongement *)
definition Mon2Rel :: "(unit, '\<sigma>)MON\<^sub>S\<^sub>E \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set"
where "Mon2Rel f = {(x, y). (f x = Some((), y))}"
(* ressortir *)
definition Rel2Mon :: " ('\<sigma> \<times> '\<sigma>) set \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E "
where "Rel2Mon S = (\<lambda> \<sigma>. if \<exists>\<sigma>'. (\<sigma>, \<sigma>') \<in> S then Some((), SOME \<sigma>'. (\<sigma>, \<sigma>') \<in> S) else None)"

lemma Mon2Rel_Rel2Mon_id: assumes det:"single_valued R" shows "(Mon2Rel \<circ> Rel2Mon) R = R"
apply (simp add: comp_def Mon2Rel_def Rel2Mon_def,auto)
apply (case_tac "\<exists>\<sigma>'. (a, \<sigma>') \<in> R", auto)
apply (subst (2) some_eq_ex) 
using det[simplified single_valued_def] by auto


lemma Rel2Mon_Id: "(Rel2Mon \<circ> Mon2Rel) x = x"
apply (rule ext)
apply (auto simp: comp_def Mon2Rel_def Rel2Mon_def)
apply (erule contrapos_pp, drule HOL.not_sym, simp)
done

lemma single_valued_Mon2Rel: "single_valued (Mon2Rel B)"
by (auto simp: single_valued_def Mon2Rel_def)

text\<open>Second Step : Proving an induction principle allowing to establish that lfp remains
       deterministic\<close> 


(* A little complete partial order theory due to Tobias Nipkow *)
definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" 
where     "chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

lemma chain_total: "chain S ==> S i \<le> S j \<or> S j \<le> S i"
by (metis chain_def le_cases lift_Suc_mono_le)

definition cont :: "('a set => 'b set) => bool" 
where     "cont f = (\<forall>S. chain S \<longrightarrow> f(UN n. S n) = (UN n. f(S n)))"

lemma mono_if_cont: fixes f :: "'a set \<Rightarrow> 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>n::nat. if n=0 then a else b"
  have "chain ?S" using \<open>a \<subseteq> b\<close> by(auto simp: chain_def)
  hence "f(UN n. ?S n) = (UN n. f(?S n))"
    using assms by (metis cont_def)
  moreover have "(UN n. ?S n) = b" using \<open>a \<subseteq> b\<close> by (auto split: if_splits)
  moreover have "(UN n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" by (metis Un_upper1)
qed

lemma chain_iterates: fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  { fix n have "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" using assms
    by(induction n) (auto simp: mono_def) }
  thus ?thesis by(auto simp: chain_def)
qed

theorem lfp_if_cont:
  assumes "cont f" shows "lfp f =  (\<Union>n. (f ^^ n) {})" (is "_ = ?U")
proof
  show "lfp f \<subseteq> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (UN n. (f^^Suc n){})"
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f^^0){} \<union> \<dots>" by simp
    also have "\<dots> = ?U"
      apply(auto simp del: funpow.simps)
      by (metis empty_iff funpow_0 old.nat.exhaust)
    finally show "f ?U \<subseteq> ?U" by simp
  qed
next
  { fix n p assume "f p \<subseteq> p"
    have "(f^^n){} \<subseteq> p"
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_cont[OF assms] Suc] \<open>f p \<subseteq> p\<close>
      show ?case by simp
    qed
  }
  thus "?U \<subseteq> lfp f" by(auto simp: lfp_def)
qed


lemma single_valued_UN_chain:
  assumes "chain S" "(!!n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
  fix m n x y z assume "(x, y) \<in> S m" "(x, z) \<in> S n"
  with chain_total[OF assms(1), of m n] assms(2)
  show "y = z" by (auto simp: single_valued_def)
qed

lemma single_valued_lfp: 
fixes f :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain[OF chain_iterates[OF mono_if_cont[OF assms(1)]]])
  fix n show "single_valued ((f ^^ n) {})"
  by(induction n)(auto simp: assms(2))
qed


text\<open>Third Step: Definition of the Monadic While \<open> \<close>\<close>
definition \<Gamma> :: "['\<sigma> \<Rightarrow> bool,('\<sigma> \<times> '\<sigma>) set] \<Rightarrow> (('\<sigma> \<times> '\<sigma>) set \<Rightarrow> ('\<sigma> \<times> '\<sigma>) set)" 
where     "\<Gamma> b cd = (\<lambda>cw. {(s,t). if b s then (s, t) \<in> cd O cw else s = t})"


definition while_SE :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E"
where     "while_SE c B \<equiv> (Rel2Mon(lfp(\<Gamma> c (Mon2Rel B))))"

syntax    (xsymbols)
          "_while_SE" :: "['\<sigma> \<Rightarrow> bool, (unit, '\<sigma>)MON\<^sub>S\<^sub>E] \<Rightarrow> (unit, '\<sigma>)MON\<^sub>S\<^sub>E" 
          ("(while\<^sub>S\<^sub>E _ do _ od)" [8,8]8)
translations 
          "while\<^sub>S\<^sub>E c do b od" == "CONST while_SE c b"

lemma cont_\<Gamma>: "cont (\<Gamma> c b)"
by (auto simp: cont_def \<Gamma>_def)

text\<open>The fixpoint theory now allows us to establish that the lfp constructed over
       @{term Mon2Rel} remains deterministic\<close>

theorem single_valued_lfp_Mon2Rel: "single_valued (lfp(\<Gamma> c (Mon2Rel B)))"
apply(rule single_valued_lfp, simp_all add: cont_\<Gamma>)
apply(auto simp: \<Gamma>_def single_valued_def)
apply(metis single_valued_Mon2Rel[of "B"] single_valued_def)
done


lemma Rel2Mon_if:
  "Rel2Mon {(s, t). if b s then (s, t) \<in> Mon2Rel c O lfp (\<Gamma> b (Mon2Rel c)) else s = t} \<sigma> =
  (if b \<sigma> then Rel2Mon (Mon2Rel c O lfp (\<Gamma> b (Mon2Rel c))) \<sigma> else Some ((), \<sigma>))"
by (simp add: Rel2Mon_def)

lemma Rel2Mon_homomorphism:
  assumes determ_X: "single_valued X" and determ_Y: "single_valued Y"
  shows   "Rel2Mon (X O Y) = (Rel2Mon X) ;- (Rel2Mon Y)"
proof - 
    have relational_partial_next_in_O: "\<And>x E F. (\<exists>y. (x, y) \<in> (E O F)) \<Longrightarrow> (\<exists>y. (x, y) \<in> E)" 
                        by (auto)
    have some_eq_intro: "\<And> X x y . single_valued X \<Longrightarrow> (x, y) \<in> X \<Longrightarrow> (SOME y. (x, y) \<in> X) = y"
                        by (auto simp: single_valued_def)

    show ?thesis
apply (simp add: Rel2Mon_def bind_SE'_def bind_SE_def)
apply (rule ext, rename_tac "\<sigma>")
apply (case_tac " \<exists> \<sigma>'. (\<sigma>, \<sigma>') \<in> X O Y")
apply (simp only: HOL.if_True)
apply (frule relational_partial_next_in_O)
apply (auto simp: single_valued_relcomp some_eq_intro determ_X determ_Y relcomp.relcompI)
by blast
qed



text\<open>Putting everything together, the theory of embedding and the invariance of
       determinism of the while-body, gives us the usual unfold-theorem:\<close>
theorem while_SE_unfold:
"(while\<^sub>S\<^sub>E b do c od) = (if\<^sub>S\<^sub>E b then (c ;- (while\<^sub>S\<^sub>E b do c od)) else result () fi)"
apply (simp add: if_SE_def bind_SE'_def while_SE_def unit_SE_def)
apply (subst lfp_unfold [OF mono_if_cont, OF cont_\<Gamma>])
apply (rule ext)
apply (subst \<Gamma>_def)
apply (auto simp: Rel2Mon_if Rel2Mon_homomorphism bind_SE'_def Rel2Mon_Id [simplified comp_def] 
                  single_valued_Mon2Rel single_valued_lfp_Mon2Rel )
done
  

lemma bind_cong : " f \<sigma> = g \<sigma> \<Longrightarrow>  (x \<leftarrow> f ; M x)\<sigma> = (x \<leftarrow> g ; M x)\<sigma>"
  unfolding bind_SE'_def bind_SE_def  by simp

lemma bind'_cong : " f \<sigma> = g \<sigma> \<Longrightarrow>  (f ;- M )\<sigma> = (g ;- M )\<sigma>"
  unfolding bind_SE'_def bind_SE_def  by simp

  
  
lemma if\<^sub>S\<^sub>E_True [simp]: "(if\<^sub>S\<^sub>E (\<lambda> x. True) then c else d fi) = c" 
  apply(rule ext) by (simp add: MonadSE.if_SE_def) 

lemma if\<^sub>S\<^sub>E_False [simp]: "(if\<^sub>S\<^sub>E (\<lambda> x. False) then c else d fi) = d" 
  apply(rule ext) by (simp add: MonadSE.if_SE_def) 
  
    
lemma if\<^sub>S\<^sub>E_cond_cong : "f \<sigma> = g \<sigma> \<Longrightarrow> 
                           (if\<^sub>S\<^sub>E f then c else d fi) \<sigma> = 
                           (if\<^sub>S\<^sub>E g then c else d fi) \<sigma>"
  unfolding if_SE_def  by simp
 
lemma while\<^sub>S\<^sub>E_skip[simp] : "(while\<^sub>S\<^sub>E (\<lambda> x. False) do c od) = skip\<^sub>S\<^sub>E" 
  apply(rule ext,subst MonadSE.while_SE_unfold)
  by (simp add: MonadSE.if_SE_def skip\<^sub>S\<^sub>E_def)
  
    
end
  