theory FactoredSystemLib
  imports Main "HOL-Library.Finite_Map"
begin 


section \<open>Factored Systems Library\<close>

text \<open>This section contains definitions used in the factored system theory (FactoredSystem.thy) and in 
other theories. \<close>


subsection \<open>Semantics of Map Addition\<close>

text \<open> Most importantly, we are redefining the map addition operator (`++`) to reflect HOL4 
semantics which are left to right (ltr), rather than right-to-left as in Isabelle/HOL. 

This means that given a finite map (`M = M1 ++ M2`) and a variable `v` which is in the domain of
both `M1` and `M2`, the lookup `M v` will yield `M1 v` in HOL4 but `M2 v` in Isabelle/HOL.
This behavior can be confirmed  by looking at the definition of `fmap\_add` (`++f`, 
Finite\_Map.thy:460)---which is lifted from `map\_add` (Map.thy:24)

  @{const map_add}  (infixl "++" 100) where
    @{term "m1 ++ m2 = (\<lambda>x. case m2 x of None \<Rightarrow> m1 x | Some y \<Rightarrow> Some y)"}
  

to finite sets---and the HOL4 definition of "FUNION` (finite\_mapScript.sml:770) which recurs
on `union\_lemma` (finite\_mapScript.sml:756)

  !\^fmap g.
     ?union.
       (FDOM union = FDOM f Union (g ` FDOM)) /\
       (!x. FAPPLY union x = if x IN FDOM f then FAPPLY f x else FAPPLY g x)
  
The ltr semantics are also reflected in [Abdulaziz et al., Definition 2, p.9].
\<close>

\<comment> \<open>NOTE hide `Map.map\_add` to free the operator symbol `++` and redefine it to reflect HOL4 map 
addition semantics.\<close>
hide_const (open) Map.map_add
no_notation Map.map_add (infixl "++" 100)
definition fmap_add_ltr :: "('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap \<Rightarrow> ('a, 'b) fmap" (infixl "++" 100) where 
  "m1 ++ m2 \<equiv> m2 ++\<^sub>f m1"  


subsection \<open>States, Actions and Problems.\<close> 

text \<open> Planning problems are typically formalized by considering possible states and the effect
of actions upon these states. 

In this case we consider a world model in propositional logic: i.e. states are finite maps of 
variables (with arbitrary type 'a) to boolean values and actions are pairs of states where the first
component specifies preconditions and the second component specifies effects (postconditions) of 
applying the action to a given state. [Abdulaziz et al., Definition 2, p.9] \<close>

type_synonym ('a) state = "('a, bool) fmap" 
type_synonym ('a) action = "('a state \<times> 'a state)"
type_synonym ('a) problem = "('a state \<times> 'a state) set"


text \<open> For a given action @{term "\<pi> = (p, e)"} the action domain @{term "\<D>(\<pi>)"} is the set of variables `v` where 
a value is assigned to `v` in either `p` or `e`, i.e. `p v` or `e v` are defined. [Abdulaziz et al., 
Definition 2, p.9] \<close>
definition action_dom where 
  "action_dom s1 s2 \<equiv> (fmdom' s1 \<union> fmdom' s2)"


\<comment> \<open>NOTE lemma `action\_dom\_pair`

  action\_dom a = FDOM (FST a) Union ((SND a) ` FDOM)

was removed because the curried definition of `action\_dom` in the translation makes it redundant.\<close>


text \<open> Now, for a given problem (i.e. action set) @{term "\<delta>"}, the problem domain @{term "\<D>(\<delta>)"} is given by the
union of the action domains of all actions in @{term "\<delta>"}. [Abdulaziz et al., Definition 3, p.9]

Moreover, the set of valid states @{term "U(\<delta>)"} is given by the union over all states whose domain is equal 
to the problem domain and the set of valid action sequences (or, valid plans) is given by the 
Kleene closure of @{term "\<delta>"}, i.e. @{term "\<delta>_star = {\<pi>. set(\<pi>) \<subseteq> \<delta>}"}. [Abdulaziz et al., Definition 3, p.9] 
  
Ultimately, the effect of executing an action `a` on a state `s` is given by calculating the 
succeding state. In general, the succeding state is either the preceding state---if the action does
not apply to the state, i.e. if the preconditions are not met---; or, the union of the effects of
the action application and the state. [Abdulaziz et al., Definition 3, p.9]
\<close>

\<comment> \<open>NOTE name shortened to 'prob\_dom'.\<close>
\<comment> \<open>NOTE lambda added to convert problem pairs to arguments of 'action\_dom'.\<close>
definition prob_dom where 
  "prob_dom prob \<equiv> \<Union> ((\<lambda> (s1, s2). action_dom s1 s2) ` prob)"

definition valid_states where
  "valid_states prob \<equiv> {s. fmdom' s = prob_dom prob}"

definition valid_plans  where 
  "valid_plans prob \<equiv> {as. set as \<subseteq> prob}"

definition state_succ where
  "state_succ s a \<equiv> (if fst a \<subseteq>\<^sub>f s then (snd a ++ s) else s)"

end