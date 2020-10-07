(*  Title:      statecharts/CTL/Kripke.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)


section \<open>Kripke Structures and CTL\<close>
theory Kripke
imports Main
begin

definition
  Kripke :: "['s set,
              's set,
              ('s * 's) set,
              ('s \<rightharpoonup> 'a set)]
             => bool" where

  "Kripke S S0 R L =
                (S0 \<subseteq> S \<and> 
                 R <= S \<times> S \<and> 
                 (Domain R) = S \<and> 
                 (dom L) = S)"

lemma Kripke_EmptySet:
 "({@x. True}, {@x. True},{(@x. True, @x. True)}, Map.empty(@x. True \<mapsto> {@x. True})) \<in> 
   {(S,S0,R,L) | S S0 R L. Kripke S S0 R L}"
by (unfold Kripke_def Domain_unfold, auto)

definition
  "kripke =
    {(S,S0,T,L) |
        (S::('s set))
        (S0::('s set))
        (T::(('s * 's) set))
        (L::('s \<rightharpoonup> ('a  set))).
                      Kripke S S0 T L}"

typedef ('s,'a) kripke =
    "kripke :: ('s set * 's set * ('s * 's) set * ('s \<rightharpoonup> 'a set)) set"
  unfolding kripke_def
  apply (rule exI)
  apply (rule Kripke_EmptySet)
  done

definition
  Statuses :: "('s,'a) kripke => 's set" where
  "Statuses = fst o Rep_kripke"

definition
   InitStatuses :: "('s,'a) kripke  => 's set" where
  "InitStatuses == fst o snd o Rep_kripke"

definition
   StepRel :: "('s,'a) kripke => ('s * 's) set" where
  "StepRel == fst o snd o snd o Rep_kripke"

definition
   LabelFun :: "('s,'a) kripke => ('s \<rightharpoonup> 'a set)" where
  "LabelFun == snd o snd o snd o Rep_kripke"

definition
   Paths :: "[('s,'a) kripke, 's] =>
             (nat => 's) set" where
  "Paths M S == { p . S = p (0::nat) \<and> (\<forall>i. (p i, p (i+1)) \<in> (StepRel M))}"

datatype ('s,'a) ctl =  Atom "'a"
                          | AND "('s,'a) ctl" "('s,'a) ctl"
                          | OR  "('s,'a) ctl" "('s,'a) ctl"
                          | IMPLIES "('s,'a) ctl" "('s,'a) ctl"
                          | CAX "('s,'a) ctl"
                          | AF  "('s,'a) ctl"
                          | AG  "('s,'a) ctl"
                          | AU  "('s,'a) ctl" "('s,'a) ctl"
                          | AR  "('s,'a) ctl" "('s,'a) ctl"


primrec
   eval_ctl :: "[('s,'a) kripke, 's, ('s,'a) ctl] => bool"  ("_,_ |=c= _" [92,91,90]90) 
   where
     "(M,S |=c= (Atom P))        = (P \<in> the ((LabelFun M) S))"
   | "(M,S |=c= (AND F1 F2))     = ((M,S |=c= F1) \<and> (M,S |=c= F2))"
   | "(M,S |=c= (OR F1 F2))      = ((M,S |=c= F1) \<or> (M,S |=c= F2))"
   | "(M,S |=c= (IMPLIES F1 F2)) = ((M,S |=c= F1) \<longrightarrow> (M,S |=c= F2))"
   | "(M,S |=c= (CAX F))         = (\<forall> T. (S,T) \<in> (StepRel M) \<longrightarrow> (M,T |=c= F))"
   | "(M,S |=c= (AF F))          = (\<forall> P \<in> Paths M S. \<exists> i. (M,(P i) |=c= F))"
   | "(M,S |=c= (AG F))          = (\<forall> P \<in> Paths M S. \<forall> i. (M,(P i) |=c= F))"
   | "(M,S |=c= (AU F G))        = (\<forall> P \<in> Paths M S.
                                     \<exists> i. (M,(P i) |=c= G) \<and> 
                                       (\<forall> j. j < i \<longrightarrow> (M,(P j) |=c= F)))"
   | "(M,S |=c= (AR F G))        = (\<forall> P \<in> Paths M S.
                                     \<forall> i. (M,(P i) |=c= G) \<or> 
                                       (\<exists> j. j < i \<and> (M,(P j) |=c= F)))"

end
