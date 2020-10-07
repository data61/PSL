(*  Title:      statecharts/HA/HAKripke.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)


section \<open>Kripke Structures as Hierarchical Automata\<close>
theory HAKripke
imports HASem Kripke
begin

type_synonym ('s,'e,'d)hakripke = "(('s,'e,'d)status,('s,'e,'d)atomar)kripke"
type_synonym ('s,'e,'d)hactl    = "(('s,'e,'d)status,('s,'e,'d)atomar)ctl"

definition
  LabelFunSem :: "('s,'e,'d)hierauto
              => (('s,'e,'d)status \<rightharpoonup> ((('s,'e,'d) atomar) set))" where
  "LabelFunSem a = (\<lambda> ST.
         (if (HA ST = a) then
              (let
                  In_preds = (\<lambda> s. (IN s)) ` (Conf ST);
                  En_preds = (\<lambda> e. (EN e)) ` (Events ST);
                  Val_preds = { x . (\<exists> P. (x = (VAL P)) \<and> P (Value ST)) }
               in
                  Some (In_preds \<union> En_preds \<union> Val_preds \<union> {atomar.TRUE}))
            else
               None))"

definition
  HA2Kripke :: "('s,'e,'d)hierauto => ('s,'e,'d)hakripke" where
  "HA2Kripke a =
         Abs_kripke ({ST. HA ST = a},
                     {InitStatus a},
                     StepRelSem a,
                     LabelFunSem a)"

definition
   eval_ctl_HA :: "[('s,'e,'d)hierauto, ('s,'e,'d)hactl]
                   => bool"  ("_ |=H= _" [92,91]90) where

   "eval_ctl_HA a f = ((HA2Kripke a), (InitStatus a) |=c= f)"

lemma Kripke_HA [simp]:
  "Kripke {ST. HA ST = a} {InitStatus a} (StepRelSem a) (LabelFunSem a)"
apply (unfold Kripke_def)
apply auto
apply (unfold StepRelSem_def)
apply auto
apply (unfold LabelFunSem_def Let_def If_def dom_def)
apply auto
prefer 2
apply (rename_tac ST S)
apply (case_tac "HA ST = a")
apply auto
apply (rename_tac ST)
apply (case_tac "HPT ST = {}")
apply auto
apply (rename_tac TSS)
apply (erule_tac x="StepStatus ST TSS (@ u. u : ResolveRacing TSS)" in allE)
apply (erule_tac x=TSS in ballE)
apply auto
done

lemma LabelFun_LabelFunSem [simp]: 
  "(LabelFun (HA2Kripke a)) = (LabelFunSem a)"
apply (unfold HA2Kripke_def LabelFun_def)
apply auto
apply (subst Abs_kripke_inverse)
apply auto
apply (unfold kripke_def)
apply auto
done

lemma InitStatuses_InitStatus [simp]:
   "(InitStatuses (HA2Kripke a)) = {(InitStatus a)}"
apply (unfold HA2Kripke_def InitStatuses_def)
apply simp
apply (subst Abs_kripke_inverse)
apply (unfold kripke_def)
apply auto
done

lemma Statuses_StatusesOfHA [simp]:
   "(Statuses (HA2Kripke a)) = {ST. HA ST = a}"
apply (unfold HA2Kripke_def Statuses_def)
apply simp
apply (subst Abs_kripke_inverse)
apply (unfold kripke_def)
apply auto
done

lemma StepRel_StepRelSem [simp]:
  "(StepRel (HA2Kripke a)) = (StepRelSem a)"
apply (unfold HA2Kripke_def StepRel_def)
apply simp
apply (subst Abs_kripke_inverse)
apply (unfold kripke_def)
apply auto
done

lemma TRUE_LabelFunSem [simp]:
   "atomar.TRUE \<in> the (LabelFunSem (HA ST) ST)"
apply (unfold LabelFunSem_def Let_def)
apply auto
done

lemma FALSE_LabelFunSem [simp]:
   "atomar.FALSE \<notin> the (LabelFunSem (HA ST) ST)"
apply (unfold LabelFunSem_def Let_def)
apply auto
done

lemma Conf_LabelFunSem [simp]:
   "((IN S) \<in> the (LabelFunSem (HA ST) ST)) = (S \<in> (Conf ST))"
apply (unfold LabelFunSem_def Let_def)
apply auto
done

lemma Events_LabelFunSem [simp]:
  "((EN S) \<in> the (LabelFunSem (HA ST) ST)) = (S \<in> (Events ST))"
apply (unfold LabelFunSem_def Let_def)
apply auto
done

lemma Value_LabelFunSem [simp]:
  "((VAL P) \<in> the (LabelFunSem (HA ST) ST)) = (P (Value ST))"
apply (unfold LabelFunSem_def Let_def)
apply auto
done

lemma AtomTRUE_EvalCTLHA [simp]:
  "a |=H= (Atom (atomar.TRUE))"
apply (unfold eval_ctl_HA_def)
apply auto
apply (subst HA_InitStatus [THEN sym])
apply (rule TRUE_LabelFunSem)
done

lemma AtomFalse_EvalCTLHA [simp]:
  "\<not> a |=H= (Atom (atomar.FALSE))"
apply (unfold eval_ctl_HA_def)
apply auto
apply (subst (asm) HA_InitStatus [THEN sym])
apply (simp only: FALSE_LabelFunSem)
done

lemma Events_InitStatus_EvalCTLHA [simp]:
  "(a |=H= (Atom (EN S))) = (S \<in> (Events (InitStatus a)))"
apply (unfold eval_ctl_HA_def)
apply simp
apply (subst HA_InitStatus [THEN sym])
apply (rule Events_LabelFunSem)
done

lemma Conf_InitStatus_EvalCTLHA [simp]:
  "(a |=H= (Atom (IN S))) = (S \<in> (Conf (InitStatus a)))"
apply (unfold eval_ctl_HA_def)
apply simp
apply (subst HA_InitStatus [THEN sym])
apply (subst Conf_LabelFunSem)
apply simp
done

lemma HAInitValue_EvalCTLHA [simp]:
  "(a |=H= (Atom (VAL P))) = (P (HAInitValue a))"
apply (unfold eval_ctl_HA_def)
apply simp
apply (subst HA_InitStatus [THEN sym])
apply (subst Value_LabelFunSem)
apply auto
done

end
