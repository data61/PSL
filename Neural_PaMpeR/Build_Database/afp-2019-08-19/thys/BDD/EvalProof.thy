(*  Title:       BDD

    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LPGL
*)

(*  
EvalProof.thy

Copyright (C) 2004-2008 Veronika Ortner and Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

section \<open>Proof of Procedure Eval\<close>
theory EvalProof imports ProcedureSpecs begin

lemma (in Eval_impl) Eval_modifies:
  shows "\<forall>\<sigma>. \<Gamma>\<turnstile>{\<sigma>}  PROC Eval (\<acute>p, \<acute>varval, \<acute>R) 
                {t. t may_not_modify_globals \<sigma>}"
  apply (hoare_rule HoarePartial.ProcRec1)
  apply (vcg spec=modifies)
  done 


lemma (in Eval_impl) Eval_spec:
  shows "\<forall>\<sigma> t bdt1. \<Gamma>\<turnstile>
  \<lbrace>\<sigma>. Dag \<acute>p \<acute>low \<acute>high t \<and> bdt t \<acute>var = Some bdt1\<rbrace> 
   \<acute>R :== PROC Eval(\<acute>p, \<acute>varval) 
  \<lbrace>\<acute>R = eval bdt1 \<^bsup>\<sigma>\<^esup>varval \<rbrace>"
apply (hoare_rule HoarePartial.ProcRec1)
apply vcg
apply clarsimp
apply safe
apply    (case_tac bdt1)
apply      simp
apply     fastforce
apply    fastforce
apply   simp
apply   (case_tac bdt1)
apply     fastforce
apply    fastforce
apply   fastforce
apply  (case_tac bdt1)
apply    fastforce
apply   fastforce
apply  fastforce
apply (case_tac bdt1)
apply   fastforce
apply  fastforce
apply fastforce
done



end
