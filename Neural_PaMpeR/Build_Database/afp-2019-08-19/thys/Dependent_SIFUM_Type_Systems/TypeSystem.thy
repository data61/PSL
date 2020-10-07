(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
section \<open>Type System for Ensuring SIFUM-Security of Commands\<close>

theory TypeSystem
imports Compositionality Language
begin

subsection \<open>Typing Rules\<close>

text \<open>
  Types now depend on memories. To see why, consider an assignment in which some variable
  @{term x} for which we have a @{term AsmNoReadOrWrite} assumption is assigned the value in 
  variable @{term input}, but where @{term input}'s classification depends on some control
  variable. Then the new type of @{term x} depends on memory. If we were to just take the 
  upper bound of @{term input}'s classification, this would likely give us @{term High} as
  @{term x}'s type, but that would prevent us from treating @{term x} as @{term Low}
  if we later learn @{term input}'s original classification. 
  
  Instead we need to make @{term x}'s type explicitly depend on memory so later on, once we
  learn @{term input}'s classification, we can resolve @{term x}'s type to a concrete
  security level.
  
  We choose to deeply embed types as sets of boolean expressions. If any expression in the
  set evaluates to @{term True}, the type is @{term High}; otherwise it is @{term Low}.
\<close>
type_synonym 'BExp Type = "'BExp set"

text \<open>
  We require @{term \<Gamma>} to track all stable (i.e. @{term AsmNoWrite} or @{term AsmNoReadOrWrite}), 
  non-@{term \<C>} variables.
  
  This differs from Mantel a bit. Mantel would exclude from @{term \<Gamma>}, variables
  whose classification (according to @{term dma}) is @{term Low} for which we have only
  an @{term AsmNoWrite} assumption.
  
  We decouple the requirement for inclusion in @{term \<Gamma>} from a variable's classification
  so that we don't need to be updating @{term \<Gamma>} each time we alter a control variable.
  Even if we tried to keep @{term \<Gamma>} up-to-date in that case, we may not be able to 
  precisely compute the new classification of each variable after the modification anyway.
\<close>
type_synonym ('Var,'BExp) TyEnv = "'Var \<rightharpoonup> 'BExp Type"

text \<open>
  This records which variables are \emph{stable} in that we have an assumption
  implying that their value won't change. It duplicates a bit of info in
  @{term \<Gamma>} above but I haven't yet thought of a way to remove that duplication
  cleanly.
  
  The first component of the pair records variables for which we have
  @{term AsmNoWrite}; the second component is for @{term AsmNoReadOrWrite}.
  
  The reason we want to distinguish the different kinds of assumptions is to know whether
  a variable should remain in @{term \<Gamma>} when we drop an assumption on it. If we drop
  e.g. @{term AsmNoWrite} but also have @{term AsmNoReadOrWrite} then if we didn't track
  stability info this way we wouldn't know whether we had to remove the variable from
  @{term \<Gamma>} or not.
\<close>
type_synonym 'Var Stable = "('Var set \<times> 'Var set)"

text \<open>
  We track a set of predicates on memories as we execute. If we evaluate a boolean expression
  all of whose variables are stable, then we enrich this set predicate with that one.
  If we assign to a stable variable, then we enrich this predicate also.
  If we release an assumption making a variable unstable, we need to remove all predicates that
  pertain to it from this set.
  
  This needs to be deeply embedded (i.e. it cannot be stored as a predicate of type
  @{typ "('Var,'Val) Mem \<Rightarrow> bool"} or even @{typ "('Var,'Val) Mem set"}), because we need to be 
  able to identify each individual predicate and for each predicate identify all of the
  variables in it, so we can discard the right predicates each time a variable becomes unstable.
\<close>
type_synonym 'bexp preds = "'bexp set"

context sifum_lang_no_dma begin

definition
  pred :: "'BExp preds \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> bool"
where
  "pred P \<equiv> \<lambda>mem. (\<forall>p\<in>P. eval\<^sub>B mem p)"

end

locale sifum_types =
  sifum_lang_no_dma ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars + sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  for ev\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  and ev\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  and aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  and bexp_vars :: "'BExp \<Rightarrow> 'Var set"
  and dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  and \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  and \<C> :: "'Var set" +
  (* we need to be able to negate predicates, when we explore the ELSE branch of an IF *)
  fixes bexp_neg :: "'BExp \<Rightarrow> 'BExp"
  assumes bexp_neg_negates: "\<And>mem e. (ev\<^sub>B mem (bexp_neg e)) = (\<not> (ev\<^sub>B mem e))" 
  (* we need to be able to compute a valid postcondition after an assignment *)
  fixes assign_post :: "'BExp preds \<Rightarrow> 'Var \<Rightarrow> 'AExp \<Rightarrow> 'BExp preds"
  assumes assign_post_valid: "\<And>mem. pred P mem \<Longrightarrow> pred (assign_post P x e) (mem(x := ev\<^sub>A mem e))"
  fixes dma_type :: "'Var \<Rightarrow> 'BExp set"
  assumes dma_correct:
    "dma mem x = (if (\<forall>e\<in>dma_type x. ev\<^sub>B mem e) then Low else High)"
  assumes \<C>_vars_correct:
    "\<C>_vars x = (\<Union>(bexp_vars ` dma_type x))"
  fixes pred_False :: 'BExp
  assumes pred_False_is_False: "\<not> ev\<^sub>B mem pred_False"
  assumes bexp_vars_pred_False: "bexp_vars pred_False = {}"
  

(* a more specialised form of the above locale useful for the examples that provides
   a brain-dead instantiation for the assignment postcondition transformer *)
locale sifum_types_assign =
  sifum_lang_no_dma ev\<^sub>A ev\<^sub>B aexp_vars bexp_vars + sifum_security dma \<C>_vars \<C> eval\<^sub>w undefined
  for ev\<^sub>A :: "('Var, 'Val) Mem \<Rightarrow> 'AExp \<Rightarrow> 'Val"
  and ev\<^sub>B :: "('Var, 'Val) Mem \<Rightarrow> 'BExp \<Rightarrow> bool"
  and aexp_vars :: "'AExp \<Rightarrow> 'Var set"
  and bexp_vars :: "'BExp \<Rightarrow> 'Var set"
  and dma :: "('Var,'Val) Mem \<Rightarrow> 'Var \<Rightarrow> Sec"
  and \<C>_vars :: "'Var \<Rightarrow> 'Var set"
  and \<C> :: "'Var set" +
  (* we need to be able to negate predicates, when we explore the ELSE branch of an IF *)
  fixes bexp_neg :: "'BExp \<Rightarrow> 'BExp"
  assumes bexp_neg_negates: "\<And>mem e. (ev\<^sub>B mem (bexp_neg e)) = (\<not> (ev\<^sub>B mem e))" 
  fixes dma_type :: "'Var \<Rightarrow> 'BExp set"
  assumes dma_correct:
    "dma mem x = (if (\<forall>e\<in>dma_type x. ev\<^sub>B mem e) then Low else High)"
  assumes \<C>_vars_correct:
    "\<C>_vars x = (\<Union>(bexp_vars ` dma_type x))"
  fixes pred_False :: 'BExp
  assumes pred_False_is_False: "\<not> ev\<^sub>B mem pred_False"
  assumes bexp_vars_pred_False: "bexp_vars pred_False = {}"
  (* we need to be able to say "variable x has value e" when we assign (the evaluation of e) to x *)
  fixes bexp_assign :: "'Var \<Rightarrow> 'AExp \<Rightarrow> 'BExp"
  assumes bexp_assign_eval: "\<And>mem e x. (ev\<^sub>B mem (bexp_assign x e)) = (mem x = (ev\<^sub>A mem e))"
  assumes bexp_assign_vars: "\<And>e x. (bexp_vars (bexp_assign x e)) = aexp_vars e \<union> {x}"

(* things needed by both sifum_types_assign and sifum_types, before we prove the former a sublocale *)
context sifum_lang_no_dma begin

definition
  stable :: "'Var Stable \<Rightarrow> 'Var \<Rightarrow> bool"
where
  "stable \<S> x \<equiv> x \<in> (fst \<S> \<union> snd \<S>)"

definition
  add_pred :: "'BExp preds \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp \<Rightarrow> 'BExp preds" ("_ +\<^sub>_ _" [120, 120, 120] 1000)
where
  "P +\<^sub>\<S> e \<equiv> (if (\<forall>x\<in>bexp_vars e. stable \<S> x) then P \<union> {e} else P)"

lemma add_pred_subset:
  "P \<subseteq> P +\<^sub>\<S> p"
  apply(clarsimp simp: add_pred_def)
  done


(* TODO: overloads the syntax for partial functions --- pick something else? *)
definition
  restrict_preds_to_vars :: "'BExp preds \<Rightarrow> 'Var set \<Rightarrow> 'BExp preds" ("_ |` _" [120, 120] 1000)
where
  "P |` V \<equiv> {e. e \<in> P \<and> bexp_vars e \<subseteq> V}"

end

context sifum_types_assign begin


text \<open>
  the most simple assignment postcondition transformer
\<close>
definition
  assign_post :: "'BExp preds \<Rightarrow> 'Var \<Rightarrow> 'AExp \<Rightarrow> 'BExp preds"
where
  "assign_post P x e \<equiv> 
           (if x \<in> (aexp_vars e) then 
              (restrict_preds_to_vars P  (-{x})) 
            else 
              (restrict_preds_to_vars P  (-{x})) \<union> {bexp_assign x e})"
 
end

sublocale sifum_types_assign \<subseteq> sifum_types _ _ _ _ _ _ _ _ assign_post
  apply(unfold_locales)
     using bexp_neg_negates apply blast
    apply(clarsimp simp: assign_post_def pred_def | safe)+
       using eval_vars_det\<^sub>B
       unfolding restrict_preds_to_vars_def
       apply (metis (mono_tags, lifting) ComplD fun_upd_other mem_Collect_eq singletonI subset_eq)
      unfolding bexp_assign_eval
      using eval_vars_det\<^sub>A
      apply fastforce
     using eval_vars_det\<^sub>B
     apply (metis (mono_tags, lifting) ComplD fun_upd_other mem_Collect_eq singletonI subset_eq)
    using dma_correct apply blast
   using \<C>_vars_correct pred_False_is_False bexp_vars_pred_False apply blast+
  done

context sifum_types
begin

(* Redefined since Isabelle does not seem to be able to reuse the abbreviation from the old locale *)
abbreviation 
  mm_equiv_abv2 :: "(_, _, _) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infix "\<approx>" 60)
where 
  "mm_equiv_abv2 c c' \<equiv> mm_equiv_abv c c'"

abbreviation 
  eval_abv2 :: "(_, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>" 70)
where
  "x \<leadsto> y \<equiv> (x, y) \<in> eval\<^sub>w"
  
abbreviation 
  eval_plus_abv :: "(_, 'Var, 'Val) LocalConf \<Rightarrow> (_, _, _) LocalConf \<Rightarrow> bool"
  (infixl "\<leadsto>\<^sup>+" 70)
where
  "x \<leadsto>\<^sup>+ y \<equiv> (x, y) \<in> eval\<^sub>w\<^sup>+"
  
abbreviation 
  no_eval_abv :: "(_, 'Var, 'Val) LocalConf \<Rightarrow> bool" 
  ("_ \<leadsto> \<bottom>")
where
  "x \<leadsto> \<bottom> \<equiv> \<forall> y. (x, y) \<notin> eval\<^sub>w"

abbreviation 
  low_indistinguishable_abv :: "'Var Mds \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt \<Rightarrow> (_, _, _) Stmt \<Rightarrow> bool"
  ("_ \<sim>\<index> _" [100, 100] 80)
where
  "c \<sim>\<^bsub>mds\<^esub> c' \<equiv> low_indistinguishable mds c c'"


abbreviation
  vars_of_type :: "'BExp Type \<Rightarrow> 'Var set"
where
  "vars_of_type t \<equiv> \<Union>(bexp_vars ` t)"
  
definition
  type_wellformed :: "'BExp Type \<Rightarrow> bool"
where
  "type_wellformed t \<equiv> vars_of_type t \<subseteq> \<C>"

lemma dma_type_wellformed [simp]:
  "type_wellformed (dma_type x)"
  apply(clarsimp simp: type_wellformed_def  \<C>_def | safe)+
  using \<C>_vars_correct apply blast
  done
  
definition 
  to_total :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var \<Rightarrow> 'BExp Type"
where 
  "to_total \<Gamma> \<equiv> \<lambda>v. if v \<in> dom \<Gamma> then the (\<Gamma> v) else dma_type v"

definition
  types_wellformed :: "('Var,'BExp) TyEnv \<Rightarrow> bool"
where
  "types_wellformed \<Gamma> \<equiv> \<forall>x\<in>dom \<Gamma>. type_wellformed (the (\<Gamma> x))"
  
lemma to_total_type_wellformed:
  "types_wellformed \<Gamma> \<Longrightarrow>
  type_wellformed (to_total \<Gamma> x)"
  by(auto simp: to_total_def types_wellformed_def)
  
lemma Un_type_wellformed:
  "\<forall>t\<in>ts. type_wellformed t \<Longrightarrow> type_wellformed (\<Union> ts)"
  apply(clarsimp simp: type_wellformed_def | safe)+
  by(fastforce simp: \<C>_def elim!: subsetCE)

inductive 
  type_aexpr :: "('Var,'BExp) TyEnv \<Rightarrow> 'AExp \<Rightarrow> 'BExp Type \<Rightarrow> bool" ("_ \<turnstile>\<^sub>a _ \<in> _" [120, 120, 120] 1000)
where
  type_aexpr [intro!]: "\<Gamma> \<turnstile>\<^sub>a e \<in> \<Union> (image (\<lambda> x. to_total \<Gamma> x) (aexp_vars e))"

lemma type_aexprI:
  "t =  \<Union> (image (\<lambda> x. to_total \<Gamma> x) (aexp_vars e)) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>a e \<in> t"
  apply(erule ssubst)
  apply(rule type_aexpr.intros)
  done

lemma type_aexpr_type_wellformed:
  "types_wellformed \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>a e \<in> t \<Longrightarrow> type_wellformed t"
  apply(erule type_aexpr.cases)
  apply(erule ssubst, rule Un_type_wellformed)
  apply clarsimp
  apply(blast intro: to_total_type_wellformed)
  done
  
inductive_cases type_aexpr_elim [elim]: "\<Gamma> \<turnstile>\<^sub>a e \<in> t"

inductive
  type_bexpr :: "('Var,'BExp) TyEnv \<Rightarrow> 'BExp \<Rightarrow> 'BExp Type \<Rightarrow> bool" ("_ \<turnstile>\<^sub>b _ \<in> _ " [120, 120, 120] 1000)
where
  type_bexpr [intro!]: "\<Gamma> \<turnstile>\<^sub>b e \<in> \<Union> (image (\<lambda> x. to_total \<Gamma> x) (bexp_vars e))"

lemma type_bexprI:
  "t =  \<Union> (image (\<lambda> x. to_total \<Gamma> x) (bexp_vars e)) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>b e \<in> t"
  apply(erule ssubst)
  apply(rule type_bexpr.intros)
  done

lemma type_bexpr_type_wellformed:
  "types_wellformed \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>b e \<in> t \<Longrightarrow> type_wellformed t"
  apply(erule type_bexpr.cases)
  apply(erule ssubst, rule Un_type_wellformed)
  apply clarsimp
  apply(blast intro: to_total_type_wellformed)
  done
  
inductive_cases type_bexpr_elim [elim]: "\<Gamma> \<turnstile>\<^sub>b e \<in> t"


text \<open>
  Define a sufficient condition for a type to be stable, assuming the type is wellformed.
  
  We need this because there is no point tracking the fact that e.g. variable @{term x}'s data has
  a classification that depends on some control variable @{term c} (where @{term c} might be
  the control variable for some other variable @{term y} whose value we've just assigned to
  @{term x}) if @{term c} can then go and be modified, since now the classification of
  the data in @{term x} no longer depends on the value of @{term c}, instead it depends on
  @{term c}'s \emph{old} value, which has now been lost.
  
  Therefore, if a type depends on @{term c}, then @{term c} had better be stable.
\<close>
abbreviation
  pred_stable :: "'Var Stable \<Rightarrow> 'BExp \<Rightarrow> bool"
where
  "pred_stable \<S> p \<equiv> \<forall>x\<in>bexp_vars p. stable \<S> x"

abbreviation
  type_stable :: "'Var Stable \<Rightarrow> 'BExp Type \<Rightarrow> bool"
where
  "type_stable \<S> t \<equiv> (\<forall>p\<in>t. pred_stable \<S> p)"
  
lemma type_stable_is_sufficient:
  "\<lbrakk>type_stable \<S> t\<rbrakk> \<Longrightarrow>
  \<forall>mem mem'. (\<forall>x. stable \<S> x \<longrightarrow> mem x = mem' x) \<longrightarrow> (ev\<^sub>B mem) ` t = (ev\<^sub>B mem') ` t"
  apply(clarsimp simp: type_wellformed_def image_def)
  apply safe
   using eval_vars_det\<^sub>B apply blast+
  done
  
definition 
  mds_consistent :: "'Var Mds \<Rightarrow> ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> bool"
where 
  "mds_consistent mds \<Gamma> \<S> P \<equiv>
    (\<S> = (mds AsmNoWrite, mds AsmNoReadOrWrite)) \<and>
    (dom \<Gamma> = {x. x \<notin> \<C> \<and> stable \<S> x}) \<and>
    (\<forall>p \<in> P. pred_stable \<S> p)"

fun 
  add_anno_dom :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'Var ModeUpd \<Rightarrow> 'Var set"
where
  "add_anno_dom \<Gamma> \<S> (Acq v AsmNoReadOrWrite) = (if v \<notin> \<C> then dom \<Gamma> \<union> {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> \<S> (Acq v AsmNoWrite) = (if v \<notin> \<C> then dom \<Gamma> \<union> {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> \<S> (Acq v _) = dom \<Gamma>" |
  "add_anno_dom \<Gamma> \<S> (Rel v AsmNoReadOrWrite) = (if v \<notin> fst \<S> then dom \<Gamma> - {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> \<S> (Rel v AsmNoWrite) = (if v \<notin> snd \<S> then dom \<Gamma> - {v} else dom \<Gamma>)" |
  "add_anno_dom \<Gamma> \<S> (Rel v _) = dom \<Gamma>"

definition 
  add_anno :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'Var ModeUpd \<Rightarrow> ('Var,'BExp) TyEnv" ("_ \<oplus>\<^sub>_ _" [120, 120, 120] 1000)
where
  "\<Gamma> \<oplus>\<^sub>\<S> upd = restrict_map (\<lambda>x. Some (to_total \<Gamma> x)) (add_anno_dom \<Gamma> \<S> upd)"

lemma add_anno_acq_AsmNoReadOrWrite_idemp [simp]:
  "v \<in> dom \<Gamma> \<or> v \<in> \<C> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Acq v AsmNoReadOrWrite) = \<Gamma>"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
    apply(rule ext)
    apply(clarsimp simp: restrict_map_def | safe)+
    apply(case_tac "\<Gamma> x", fastforce+)[5]
   apply(rule ext)
   apply(clarsimp simp: restrict_map_def | safe)+
   apply(case_tac "\<Gamma> x", fastforce+)
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(rule ext)
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(case_tac "\<Gamma> x", fastforce+)
  done

lemma add_anno_rel_AsmNoReadOrWrite_idemp [simp]:
  "\<lbrakk>v \<notin> dom \<Gamma>; v \<notin> fst \<S>\<rbrakk> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Rel v AsmNoReadOrWrite) = \<Gamma>"
  apply(subgoal_tac "v \<notin> dom \<Gamma>")
   apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(erule_tac P="(\<lambda>x. if x \<in> dom \<Gamma> \<and> x \<noteq> v
          then Some (if x \<in> dom \<Gamma> then the (\<Gamma> x) else dma_type x) else None) = \<Gamma>" in notE)
  apply(rule ext)
  apply(case_tac "\<Gamma> x", fastforce+)
  done

lemma add_anno_acq_AsmNoReadOrWrite [simp]:
  assumes notin [simp]: "v \<notin> dom \<Gamma>"
  shows "v \<notin> \<C> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Acq v AsmNoReadOrWrite) = (\<Gamma>(v \<mapsto> dma_type v))"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(rule ext)
  apply(auto intro: sym)
  done

lemma add_anno_rel_AsmNoReadOrWrite [simp]:
  assumes isin [simp]: "v \<in> dom \<Gamma>"
  shows "v \<notin> fst \<S> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Rel v AsmNoReadOrWrite) = restrict_map \<Gamma> ((dom \<Gamma>) - {v})"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(rule ext)
  apply(auto intro: sym)
  done

lemma add_anno_acq_AsmNoWrite_idemp [simp]:
  "v \<in> dom \<Gamma> \<or> v \<in> \<C> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Acq v AsmNoWrite) = \<Gamma>"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
    apply(rule ext)
    apply(clarsimp simp: restrict_map_def | safe)+
    apply(case_tac "\<Gamma> x", fastforce+)[5]
   apply(rule ext)
   apply(clarsimp simp: restrict_map_def | safe)+
   apply(case_tac "\<Gamma> x", fastforce+)
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(rule ext)
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(case_tac "\<Gamma> x", fastforce+)
  done

lemma add_anno_rel_AsmNoWrite_idemp [simp]:
  "\<lbrakk>v \<notin> dom \<Gamma>; v \<notin> snd \<S>\<rbrakk> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Rel v AsmNoWrite) = \<Gamma>"
  apply(subgoal_tac "v \<notin> dom \<Gamma>")
   apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(erule_tac P="(\<lambda>x. if x \<in> dom \<Gamma> \<and> x \<noteq> v
          then Some (if x \<in> dom \<Gamma> then the (\<Gamma> x) else dma_type x) else None) = \<Gamma>" in notE)
  apply(rule ext)
  apply(case_tac "\<Gamma> x", fastforce+)
  done

lemma add_anno_acq_AsmNoWrite [simp]:
  assumes notin [simp]: "v \<notin> dom \<Gamma>"
  shows "v \<notin> \<C> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Acq v AsmNoWrite) = (\<Gamma>(v \<mapsto> dma_type v))"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(rule ext)
  apply(auto intro: sym)
  done

lemma add_anno_rel_AsmNoWrite [simp]:
  assumes isin [simp]: "v \<in> dom \<Gamma>"
  shows "v \<notin> snd \<S> \<Longrightarrow> \<Gamma> \<oplus>\<^sub>\<S> (Rel v AsmNoWrite) = restrict_map \<Gamma> ((dom \<Gamma>) - {v})"
  apply(safe | clarsimp simp: add_anno_def to_total_def)+
  apply(clarsimp simp: restrict_map_def | safe)+
  apply(rule ext)
  apply(auto intro: sym)
  done
  
fun 
  add_anno_stable :: "'Var Stable \<Rightarrow> 'Var ModeUpd \<Rightarrow> 'Var Stable"
where
  "add_anno_stable \<S> (Acq v AsmNoReadOrWrite) = (fst \<S>, snd \<S> \<union> {v})" |
  "add_anno_stable \<S> (Acq v AsmNoWrite) = (fst \<S> \<union> {v}, snd \<S>)" |
  "add_anno_stable \<S> (Acq v _) = \<S>" |
  "add_anno_stable \<S> (Rel v AsmNoReadOrWrite) = (fst \<S>, snd \<S> - {v})" |
  "add_anno_stable \<S> (Rel v AsmNoWrite) = (fst \<S> - {v}, snd \<S>)" |
  "add_anno_stable \<S> (Rel v _) = \<S>"

definition
  pred_entailment :: "'BExp preds \<Rightarrow> 'BExp preds \<Rightarrow> bool" (infix "\<turnstile>" 70)
where
  "P \<turnstile> P' \<equiv> \<forall>mem. pred P mem \<longrightarrow> pred P' mem"

text \<open>
  We give a predicate interpretation of subtype and then prove it has the correct
  semantic property.
\<close>
definition
  subtype :: "'BExp Type \<Rightarrow> 'BExp preds \<Rightarrow> 'BExp Type \<Rightarrow> bool" ("_ \<le>:\<^sub>_ _" [120, 120, 120] 1000)
where
  "t \<le>:\<^sub>P t' \<equiv> (P \<union> t') \<turnstile> t"

definition
  type_max :: "'BExp Type \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> Sec"
where
  "type_max t mem \<equiv> if (\<forall>p\<in>t. ev\<^sub>B mem p) then Low else High"

lemma type_stable_is_sufficient':
  "\<lbrakk>type_stable \<S> t\<rbrakk> \<Longrightarrow>
  \<forall>mem mem'. (\<forall>x. stable \<S> x \<longrightarrow> mem x = mem' x) \<longrightarrow> type_max t mem = type_max t mem'"
  using type_stable_is_sufficient
  unfolding type_max_def image_def
  by (metis (no_types, lifting) eval_vars_det\<^sub>B)

lemma subtype_sound:
  "t \<le>:\<^sub>P t' \<Longrightarrow> \<forall>mem. pred P mem \<longrightarrow> type_max t mem \<le> type_max t' mem"
  apply(fastforce simp: subtype_def pred_entailment_def pred_def type_max_def less_eq_Sec_def)
  done

lemma subtype_complete:
  assumes a: "\<And>mem. pred P mem \<Longrightarrow> type_max t mem \<le> type_max t' mem"
  shows "t \<le>:\<^sub>P t'"
unfolding subtype_def pred_entailment_def
proof (clarify)
  fix mem
  assume p: "pred (P \<union> t') mem"
  hence "pred P mem"
    unfolding pred_def by blast
  with a have tmax: "type_max t mem \<le> type_max t' mem" by blast
  from p have t': "pred t' mem"
    unfolding pred_def by blast
  from t' have "type_max t' mem = Low"
    unfolding type_max_def pred_def by force
  with tmax have "type_max t mem \<le> Low"
    by simp
  hence "type_max t mem = Low"
    unfolding less_eq_Sec_def by blast
  thus "pred t mem"
    unfolding type_max_def pred_def by (auto split: if_splits)
qed

lemma subtype_correct:
  "(t \<le>:\<^sub>P t')  = (\<forall>mem. pred P mem \<longrightarrow> type_max t mem \<le> type_max t' mem)"
  apply(rule iffI)
   apply(simp add: subtype_sound)
  apply(simp add: subtype_complete)
  done

definition
  type_equiv :: "'BExp Type \<Rightarrow> 'BExp preds \<Rightarrow> 'BExp Type \<Rightarrow> bool" ("_ =:\<^sub>_ _" [120, 120, 120] 1000)
where
  "t =:\<^sub>P t' \<equiv> t \<le>:\<^sub>P t' \<and> t' \<le>:\<^sub>P t"
  

lemma subtype_refl [simp]:
  "t \<le>:\<^sub>P t"
  by(simp add: subtype_def pred_entailment_def pred_def)

lemma type_equiv_refl [simp]:
  "t =:\<^sub>P t"
  by (simp add: type_equiv_def)
  
definition
  anno_type_stable :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'Var ModeUpd \<Rightarrow> bool"
where
  "anno_type_stable \<Gamma> \<S> upd \<equiv> (case upd of (Rel v m) \<Rightarrow>
                                 (v \<in> \<C> \<and> v \<notin> add_anno_dom \<Gamma> \<S> upd) \<longrightarrow>
                                    (\<forall>x\<in>dom \<Gamma>. v \<notin> vars_of_type (the (\<Gamma> x)))
                                          | (Acq v m) \<Rightarrow> 
                                    (v \<notin> \<C> \<and> v\<in>add_anno_dom \<Gamma> \<S> upd - dom \<Gamma>) \<longrightarrow>
                                      (\<forall>x\<in>\<C>_vars v. stable \<S> x))"

definition
  anno_type_sec :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow>  'BExp preds \<Rightarrow> 'Var ModeUpd \<Rightarrow> bool"
where
  "anno_type_sec \<Gamma> \<S> P upd \<equiv> (case upd of (Rel v AsmNoReadOrWrite) \<Rightarrow>
                                (v \<in> add_anno_dom \<Gamma> \<S> upd \<longrightarrow> (the (\<Gamma> v)) \<le>:\<^sub>P (dma_type v))
                                          |  _ \<Rightarrow> True)"

definition
  types_stable :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> bool"
where
  "types_stable \<Gamma> \<S> \<equiv> \<forall>x\<in>dom \<Gamma>. type_stable \<S> (the (\<Gamma> x))"
  
definition
  tyenv_wellformed :: "'Var Mds \<Rightarrow> ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> bool"
where
  "tyenv_wellformed mds \<Gamma> \<S> P \<equiv> 
      mds_consistent mds \<Gamma> \<S> P \<and>
      types_wellformed \<Gamma> \<and> types_stable \<Gamma> \<S>"

lemma subset_entailment:
  "P' \<subseteq> P \<Longrightarrow> P \<turnstile> P'"
  apply(auto simp: pred_entailment_def pred_def)
  done

lemma pred_entailment_refl [simp]:
  "P \<turnstile> P"
  by(simp add: pred_entailment_def)

lemma pred_entailment_mono:
  "P \<turnstile> P' \<Longrightarrow> P \<subseteq> P'' \<Longrightarrow> P'' \<turnstile> P'"
  by(auto simp: pred_entailment_def pred_def)
  
lemma type_equiv_subset:
  "type_equiv t P t' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> type_equiv t P' t'"
  apply(auto simp: type_equiv_def subtype_def intro: pred_entailment_mono)
  done
  
definition
  context_equiv :: "('Var,'BExp) TyEnv \<Rightarrow> 'BExp preds \<Rightarrow> ('Var,'BExp) TyEnv \<Rightarrow> bool" ("_ =:\<^sub>_ _" [120, 120, 120] 1000)
where
  "\<Gamma> =:\<^sub>P \<Gamma>' \<equiv> dom \<Gamma> = dom \<Gamma>' \<and>
                           (\<forall>x\<in>dom \<Gamma>'. type_equiv (the (\<Gamma> x)) P (the (\<Gamma>' x)))"

lemma context_equiv_refl[simp]:
  "context_equiv \<Gamma> P \<Gamma>"
  by(simp add: context_equiv_def)

lemma context_equiv_subset:
  "context_equiv \<Gamma> P \<Gamma>' \<Longrightarrow> P \<subseteq> P' \<Longrightarrow> context_equiv \<Gamma> P' \<Gamma>'"
  apply(auto simp: context_equiv_def intro: type_equiv_subset)
  done

lemma pred_entailment_trans:
  "P \<turnstile> P' \<Longrightarrow> P' \<turnstile> P'' \<Longrightarrow> P \<turnstile> P''"
  by(auto simp: pred_entailment_def)

lemma pred_un [simp]:
  "pred (P \<union> P') mem = (pred P mem \<and> pred P' mem)"
  apply(auto simp: pred_def)
  done
  
lemma pred_entailment_un:
  "P \<turnstile> P' \<Longrightarrow> P \<turnstile> P'' \<Longrightarrow> P \<turnstile> (P' \<union> P'')"
  apply(subst pred_entailment_def)
  apply clarsimp
  apply(fastforce simp: pred_entailment_def)
  done

lemma pred_entailment_mono_un:
  "P \<turnstile> P' \<Longrightarrow> (P \<union> P'') \<turnstile> (P' \<union> P'')"
  apply(auto simp: pred_entailment_def pred_def)
  done
  
lemma subtype_trans:
  "t \<le>:\<^sub>P t' \<Longrightarrow> t' \<le>:\<^sub>P' t'' \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> t \<le>:\<^sub>P t''"
  "t \<le>:\<^sub>P' t' \<Longrightarrow> t' \<le>:\<^sub>P t'' \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> t \<le>:\<^sub>P t''"
   apply(clarsimp simp: subtype_def)
   apply(rule pred_entailment_trans)
    prefer 2
    apply assumption
   apply(rule pred_entailment_un)
    apply(blast intro: subset_entailment)
   apply(rule pred_entailment_trans)
    prefer 2
    apply assumption
   apply(blast intro: pred_entailment_mono_un)
  apply(clarsimp simp: subtype_def)
  apply(rule pred_entailment_trans)
   prefer 2
   apply assumption
  apply(rule pred_entailment_un)
   apply(blast intro: pred_entailment_mono)
  apply(blast intro: subset_entailment)
  done
  
lemma type_equiv_trans:
  "type_equiv t P t' \<Longrightarrow> type_equiv t' P' t'' \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> type_equiv t P t''"
  apply(auto simp: type_equiv_def intro: subtype_trans)
  done

lemma context_equiv_trans:
  "context_equiv \<Gamma> P \<Gamma>' \<Longrightarrow> context_equiv \<Gamma>' P' \<Gamma>'' \<Longrightarrow> P \<turnstile> P' \<Longrightarrow> context_equiv \<Gamma> P \<Gamma>''"
  apply(force simp: context_equiv_def intro: type_equiv_trans)
  done

lemma un_pred_entailment_mono:
  "(P \<union> P') \<turnstile> P'' \<Longrightarrow> P''' \<turnstile> P \<Longrightarrow> (P''' \<union> P') \<turnstile> P''"
  unfolding pred_entailment_def pred_def
  apply blast
  done
  
lemma subtype_entailment:
  "t \<le>:\<^sub>P t' \<Longrightarrow> P' \<turnstile> P \<Longrightarrow> t \<le>:\<^sub>P' t'"
  apply(auto simp: subtype_def intro: un_pred_entailment_mono)
  done
  
lemma type_equiv_entailment:
  "type_equiv t P t' \<Longrightarrow> P' \<turnstile> P \<Longrightarrow> type_equiv t P' t'"
  apply(auto simp: type_equiv_def intro: subtype_entailment)  
  done
  
lemma context_equiv_entailment:
  "context_equiv \<Gamma> P \<Gamma>' \<Longrightarrow> P' \<turnstile> P \<Longrightarrow> context_equiv \<Gamma> P' \<Gamma>'"
  apply(auto simp: context_equiv_def intro: type_equiv_entailment)
  done


  
  
inductive 
  has_type :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> ('Var, 'AExp, 'BExp) Stmt \<Rightarrow> ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> bool"
  ("\<turnstile> _,_,_ {_} _,_,_" [120, 120, 120, 120, 120, 120, 120] 1000)
where
  stop_type [intro]: "\<turnstile> \<Gamma>,\<S>,P {Stop} \<Gamma>,\<S>,P" |
  skip_type [intro] : "\<turnstile> \<Gamma>,\<S>,P {Skip} \<Gamma>,\<S>,P" |
  assign\<^sub>\<C> : 
  "\<lbrakk>x \<in> \<C>; \<Gamma> \<turnstile>\<^sub>a e \<in> t; P \<turnstile> t; (\<forall>v\<in>dom \<Gamma>. x \<notin> vars_of_type (the (\<Gamma> v))); 
    P' = restrict_preds_to_vars (assign_post P x e) {v. stable \<S> v}; 
    \<forall>v. x \<in> \<C>_vars v \<and> v \<notin> snd \<S> \<longrightarrow> P \<turnstile> (to_total \<Gamma> v) \<and> 
                                      (to_total \<Gamma> v) \<le>:\<^sub>P' (dma_type v) \<rbrakk> \<Longrightarrow> 
   \<turnstile> \<Gamma>,\<S>,P {x \<leftarrow> e} \<Gamma>,\<S>,P'" | 
  assign\<^sub>1 : 
  "\<lbrakk> x \<notin> dom \<Gamma> ; x \<notin> \<C>; \<Gamma> \<turnstile>\<^sub>a e \<in> t; t \<le>:\<^sub>P (dma_type x); 
     P' = restrict_preds_to_vars (assign_post P x e)  {v. stable \<S> v} \<rbrakk> \<Longrightarrow> 
   \<turnstile> \<Gamma>,\<S>,P {x \<leftarrow> e} \<Gamma>,\<S>,P'" |
  assign\<^sub>2 : 
  "\<lbrakk> x \<in> dom \<Gamma> ; \<Gamma> \<turnstile>\<^sub>a e \<in> t;  type_stable \<S> t; P' = restrict_preds_to_vars (assign_post P x e) {v. stable \<S> v}; 
     x \<notin> snd \<S> \<longrightarrow> t \<le>:\<^sub>P' (dma_type x) \<rbrakk> \<Longrightarrow> 
   has_type \<Gamma> \<S> P (x \<leftarrow> e) (\<Gamma> (x := Some t)) \<S> P'" |
  if_type [intro]: 
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> t; P \<turnstile> t; 
     \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> e) { c\<^sub>1 } \<Gamma>',\<S>',P'; \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> (bexp_neg e)) { c\<^sub>2 } \<Gamma>'',\<S>',P''; 
     context_equiv \<Gamma>' P' \<Gamma>'''; context_equiv \<Gamma>'' P'' \<Gamma>'''; P' \<turnstile> P'''; P'' \<turnstile> P'''; 
     \<forall>mds. tyenv_wellformed mds \<Gamma>' \<S>' P' \<longrightarrow> tyenv_wellformed mds \<Gamma>''' \<S>' P'''; 
     \<forall>mds. tyenv_wellformed mds \<Gamma>'' \<S>' P'' \<longrightarrow> tyenv_wellformed mds \<Gamma>''' \<S>' P''' \<rbrakk> \<Longrightarrow> 
   \<turnstile> \<Gamma>,\<S>,P { If e c\<^sub>1 c\<^sub>2 } \<Gamma>''',\<S>',P'''" | 
  while_type [intro]: "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> t ; P \<turnstile> t; \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> e) { c } \<Gamma>,\<S>,P \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,\<S>,P { While e c } \<Gamma>,\<S>,P" |
  anno_type [intro]: "\<lbrakk> \<Gamma>' = \<Gamma> \<oplus>\<^sub>\<S> upd ; \<S>' = add_anno_stable \<S> upd; P' = restrict_preds_to_vars P {v. stable \<S>' v};
                 \<turnstile> \<Gamma>',\<S>',P' { c } \<Gamma>'',\<S>'',P'' ; c \<noteq> Stop ;
                 (\<And> x. (to_total \<Gamma> x) \<le>:\<^sub>P' (to_total \<Gamma>' x));
                 anno_type_stable \<Gamma> \<S> upd; anno_type_sec \<Gamma> \<S> P upd\<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,\<S>,P { c@[upd] } \<Gamma>'',\<S>'',P''" |
  seq_type [intro]: "\<lbrakk> \<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 } \<Gamma>',\<S>',P' ; \<turnstile> \<Gamma>',\<S>',P' { c\<^sub>2 } \<Gamma>'',\<S>'',P'' \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 ;; c\<^sub>2 } \<Gamma>'',\<S>'',P''" |
  sub : "\<lbrakk> \<turnstile> \<Gamma>\<^sub>1,\<S>,P\<^sub>1 { c } \<Gamma>\<^sub>1',\<S>',P\<^sub>1' ; context_equiv \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>1 ; (\<forall>mds. tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1);
           (\<forall>mds. tyenv_wellformed mds \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>2' \<S>' P\<^sub>2'); context_equiv \<Gamma>\<^sub>1' P\<^sub>1' \<Gamma>\<^sub>2'; P\<^sub>2 \<turnstile> P\<^sub>1; P\<^sub>1' \<turnstile> P\<^sub>2' \<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>\<^sub>2,\<S>,P\<^sub>2 { c } \<Gamma>\<^sub>2',\<S>',P\<^sub>2'" |
 await_type [intro]: 
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> t; P \<turnstile> t; 
     \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> e) { c } \<Gamma>',\<S>',P' \<rbrakk> \<Longrightarrow> 
   \<turnstile> \<Gamma>,\<S>,P { Await e c } \<Gamma>',\<S>',P'"

lemma sub':
  "\<lbrakk> context_equiv \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>1 ;
    (\<forall>mds. tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1);
    (\<forall>mds. tyenv_wellformed mds \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>2' \<S>' P\<^sub>2');
    context_equiv \<Gamma>\<^sub>1' P\<^sub>1' \<Gamma>\<^sub>2';
    P\<^sub>2 \<turnstile> P\<^sub>1;
    P\<^sub>1' \<turnstile> P\<^sub>2';
    \<turnstile> \<Gamma>\<^sub>1,\<S>,P\<^sub>1 { c } \<Gamma>\<^sub>1',\<S>',P\<^sub>1' \<rbrakk> \<Longrightarrow>
  \<turnstile> \<Gamma>\<^sub>2,\<S>,P\<^sub>2 { c } \<Gamma>\<^sub>2',\<S>',P\<^sub>2'"
  by(rule sub)

lemma assign\<^sub>2_helper:
  "\<lbrakk>\<Gamma> x = Some t; has_type \<Gamma> \<S> P (x \<leftarrow> e) (\<Gamma>(x \<mapsto> t)) \<S> P'\<rbrakk> \<Longrightarrow> has_type \<Gamma> \<S> P (x \<leftarrow> e) \<Gamma> \<S> P'"
  by (simp add:map_upd_triv)

lemma conc':
  "\<lbrakk> \<turnstile> \<Gamma>\<^sub>1,\<S>,P { c } \<Gamma>',\<S>',P'; 
    \<Gamma>\<^sub>1 = (\<Gamma>\<^sub>2(x \<mapsto> t)); 
    x \<in> dom \<Gamma>\<^sub>2; 
    type_equiv (the (\<Gamma>\<^sub>2 x)) P t; 
    type_wellformed t; 
    type_stable \<S> t  \<rbrakk> \<Longrightarrow> 
  \<turnstile> \<Gamma>\<^sub>2,\<S>,P { c } \<Gamma>',\<S>',P'"  
  apply(erule sub)
      apply(fastforce simp: context_equiv_def)
     apply(clarsimp simp: tyenv_wellformed_def mds_consistent_def)
     apply(rule conjI)
      apply fastforce
     apply(rule conjI)
      apply(fastforce simp: types_wellformed_def)
     apply(fastforce simp: types_stable_def)
     apply blast
    apply simp+
  done

lemma tyenv_wellformed_subset:
  "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> P' \<subseteq> P \<Longrightarrow> tyenv_wellformed mds \<Gamma> \<S> P'"
  apply(auto simp: tyenv_wellformed_def mds_consistent_def)
  done

lemma if_type':
  "\<lbrakk> \<Gamma> \<turnstile>\<^sub>b e \<in> t; 
    P \<turnstile> t; 
    \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> e) { c\<^sub>1 } \<Gamma>',\<S>',P'; 
    \<turnstile> \<Gamma>,\<S>,(P +\<^sub>\<S> (bexp_neg e)) { c\<^sub>2 } \<Gamma>',\<S>',P''; 
    P''' \<subseteq> P' \<inter> P'' \<rbrakk> \<Longrightarrow> 
  \<turnstile> \<Gamma>,\<S>,P { If e c\<^sub>1 c\<^sub>2 } \<Gamma>',\<S>',P'''"
  apply(erule (3) if_type)
       apply(rule context_equiv_refl)
      apply(rule context_equiv_refl)
     apply(blast intro: subset_entailment)+
   apply(blast intro: tyenv_wellformed_subset)+
  done

lemma skip_type':
  "\<lbrakk>\<Gamma> = \<Gamma>'; \<S> = \<S>'; P = P'\<rbrakk> \<Longrightarrow> \<turnstile> \<Gamma>,\<S>,P {Skip} \<Gamma>',\<S>',P'"
  using skip_type by simp

text \<open>
  Some helper lemmas to discharge the assumption of the @{thm anno_type} rule.
\<close>
lemma anno_type_helpers [simp]:
  "(to_total \<Gamma> x) \<le>:\<^sub>P (to_total (add_anno \<Gamma> \<S> (buffer +=\<^sub>m AsmNoWrite)) x)"
  "(to_total \<Gamma> x) \<le>:\<^sub>P (to_total (add_anno \<Gamma> \<S> (buffer +=\<^sub>m AsmNoReadOrWrite)) x)"
  apply(auto simp: to_total_def add_anno_def subtype_def intro: subset_entailment)
  done

subsection \<open>Typing Soundness\<close>

text \<open>The following predicate is needed to exclude some pathological
  cases, that abuse the @{term Stop} command which is not allowed to
  occur in actual programs.\<close>


inductive_cases has_type_elim: "\<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P'"
inductive_cases has_type_stop_elim: "\<turnstile> \<Gamma>,\<S>,P { Stop } \<Gamma>',\<S>',P'"

definition tyenv_eq :: "('Var,'BExp) TyEnv \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> bool"
  (infix "=\<index>" 60)
  where "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<equiv> \<forall> x. (type_max (to_total \<Gamma> x) mem\<^sub>1 = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x)"

lemma type_max_dma_type [simp]:
  "type_max (dma_type x) mem = dma mem x"
  using dma_correct unfolding type_max_def apply auto
  done

  
text \<open>
  This result followed trivially for Mantel et al., but we need to know that the
  type environment is wellformed.
\<close>
lemma tyenv_eq_sym': 
  "dom \<Gamma> \<inter> \<C> = {} \<Longrightarrow> types_wellformed \<Gamma> \<Longrightarrow> mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<Longrightarrow> mem\<^sub>2 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>1"
proof(clarsimp simp: tyenv_eq_def)
  fix x
  assume a: "\<forall>x. type_max (to_total \<Gamma> x) mem\<^sub>1 = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
  assume b: "dom \<Gamma> \<inter> \<C> = {}"
  from a b have eq_\<C>: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>2 x"
    by (fastforce simp: to_total_def \<C>_Low type_max_dma_type split: if_splits)
  hence "dma mem\<^sub>1 = dma mem\<^sub>2"
    by (rule dma_\<C>)
  hence dma_type_eq: "type_max (dma_type x) mem\<^sub>1 = type_max (dma_type x) mem\<^sub>2"
    by(simp)
  assume c: "types_wellformed \<Gamma>"
  
  assume d: "type_max (to_total \<Gamma> x) mem\<^sub>2 = Low"
  show "mem\<^sub>2 x = mem\<^sub>1 x"
  proof(cases "x \<in> dom \<Gamma>")
    assume in_dom: "x \<in> dom \<Gamma>"
    from this obtain t where t: "\<Gamma> x = Some t" by blast
    from this in_dom c have "type_wellformed t" by (force simp: types_wellformed_def)
    hence "\<forall>x\<in>vars_of_type t. mem\<^sub>1 x = mem\<^sub>2 x"
      using eq_\<C> unfolding type_wellformed_def by blast
    hence t_eq: "type_max t mem\<^sub>1 = type_max t mem\<^sub>2" 
      unfolding type_max_def using eval_vars_det\<^sub>B
      by fastforce
    with in_dom t have "to_total \<Gamma> x = t"
      by (auto simp: to_total_def)
    with t_eq have "type_max (to_total \<Gamma> x) mem\<^sub>2 = type_max (to_total \<Gamma> x) mem\<^sub>1" by simp
    with d have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low" by simp
    with a show ?thesis by (metis sym)
  next
    assume "x \<notin> dom \<Gamma>"
    hence "to_total \<Gamma> x = dma_type x"
      by (auto simp: to_total_def)
    with dma_type_eq have "type_max (to_total \<Gamma> x) mem\<^sub>2 = type_max (to_total \<Gamma> x) mem\<^sub>1" by simp
    with d have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low" by simp
    with a show ?thesis by (metis sym)
  qed
qed

lemma tyenv_eq_sym:
  "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 \<Longrightarrow> mem\<^sub>2 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>1"
  apply(rule tyenv_eq_sym')
    apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
   apply(simp add: tyenv_wellformed_def)
  by assumption
  
inductive_set \<R>\<^sub>1 :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  and \<R>\<^sub>1_abv :: "
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  bool" ("_ \<R>\<^sup>1\<^bsub>_,_,_\<^esub> _" [120, 120, 120, 120, 120] 1000)
  for \<Gamma>' :: "('Var,'BExp) TyEnv"
  and \<S>' :: "'Var Stable"
  and P' :: "'BExp preds"
where
  "x \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> y \<equiv> (x, y) \<in> \<R>\<^sub>1 \<Gamma> \<S> P" |
  intro [intro!] : "\<lbrakk> \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P' ; tyenv_wellformed mds \<Gamma> \<S> P ; mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2;
                      pred P mem\<^sub>1; pred P mem\<^sub>2; \<forall>x\<in>dom \<Gamma>. x\<notin>mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem\<^sub>1 \<le> dma mem\<^sub>1 x\<rbrakk> \<Longrightarrow> 
                    \<langle>c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c, mds, mem\<^sub>2\<rangle>"

inductive \<R>\<^sub>3_aux :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                 ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
                 bool" ("_ \<R>\<^sup>3\<^bsub>_,_,_\<^esub> _" [120, 120, 120, 120, 120] 1000)
  and \<R>\<^sub>3 :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow> (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  where
  "\<R>\<^sub>3 \<Gamma>' \<S>' P' \<equiv> {(lc\<^sub>1, lc\<^sub>2). \<R>\<^sub>3_aux lc\<^sub>1 \<Gamma>' \<S>' P' lc\<^sub>2}" |
  intro\<^sub>1 [intro] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P' \<rbrakk> \<Longrightarrow>
                      \<langle>Seq c\<^sub>1 c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>Seq c\<^sub>2 c, mds, mem\<^sub>2\<rangle>" |
  intro\<^sub>3 [intro] : "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P' \<rbrakk> \<Longrightarrow>
                      \<langle>Seq c\<^sub>1 c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>Seq c\<^sub>2 c, mds, mem\<^sub>2\<rangle>"

(* A weaker property than bisimulation to reason about the sub-relations of \<R>: *)
definition 
  weak_bisim :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel \<Rightarrow>
                        (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel \<Rightarrow> bool"
where 
  "weak_bisim \<T>\<^sub>1 \<T> \<equiv> \<forall> c\<^sub>1 c\<^sub>2 mds mem\<^sub>1 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'.
  ((\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<T>\<^sub>1 \<and>
   (\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>)) \<longrightarrow>
  (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and> 
                (\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>, \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>) \<in> \<T>)"

inductive_set \<R> :: "('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf rel"
  and \<R>_abv :: "
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  ('Var,'BExp) TyEnv \<Rightarrow> 'Var Stable \<Rightarrow> 'BExp preds \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  bool" ("_ \<R>\<^sup>u\<^bsub>_,_,_\<^esub> _" [120, 120, 120, 120, 120] 1000)
  for \<Gamma> :: "('Var,'BExp) TyEnv"
  and \<S> :: "'Var Stable"
  and P :: "'BExp preds"
where
  "x \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> y \<equiv> (x, y) \<in> \<R> \<Gamma> \<S> P" |
  intro\<^sub>1: "lc \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> lc' \<Longrightarrow> (lc, lc') \<in> \<R> \<Gamma> \<S> P" |
  intro\<^sub>3: "lc \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> lc' \<Longrightarrow> (lc, lc') \<in> \<R> \<Gamma> \<S> P"

(* Some eliminators for the above relations *)
inductive_cases \<R>\<^sub>1_elim [elim]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>3_elim [elim]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"

inductive_cases \<R>_elim [elim]: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma> \<S> P"
inductive_cases \<R>_elim': "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma> \<S> P"
inductive_cases \<R>\<^sub>1_elim' : "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"
inductive_cases \<R>\<^sub>3_elim' : "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>"

lemma \<R>\<^sub>1_mem_eq: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
proof (erule \<R>\<^sub>1_elim)
  fix \<Gamma> \<S> P
  assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
  hence mds_consistent: "mds_consistent mds \<Gamma> \<S> P"
    unfolding tyenv_wellformed_def by blast
  assume tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2"
  assume leq: "\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem\<^sub>1 \<le> dma mem\<^sub>1 x"
  assume pred: "pred P mem\<^sub>1"
  
  show "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  unfolding low_mds_eq_def
  proof(clarify)
    fix x
    assume is_Low: "dma mem\<^sub>1 x = Low"
    assume is_readable: "x \<in> \<C> \<or> x \<notin> mds AsmNoReadOrWrite"
    show "mem\<^sub>1 x = mem\<^sub>2 x"
    proof(cases "x \<in> dom \<Gamma>")
      assume in_dom: "x \<in> dom \<Gamma>"
      with mds_consistent have "x \<notin> \<C>"
        unfolding mds_consistent_def by blast
      with is_readable have "x \<notin> mds AsmNoReadOrWrite"
        by blast
       
      with in_dom leq  have "type_max (to_total \<Gamma> x) mem\<^sub>1 \<le> dma mem\<^sub>1 x"
        unfolding to_total_def
        by auto
      with is_Low have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
        by(simp add: less_eq_Sec_def)
      with tyenv_eq show ?thesis
        unfolding tyenv_eq_def by blast
    next         
      assume nin_dom: "x \<notin> dom \<Gamma>"
      with is_Low have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
        unfolding to_total_def
        by simp
      with tyenv_eq show ?thesis
        unfolding tyenv_eq_def by blast
    qed
  qed
qed

lemma \<R>\<^sub>1_dma_eq:
  "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> dma mem\<^sub>1 = dma mem\<^sub>2"
  apply(drule \<R>\<^sub>1_mem_eq)
  apply(erule low_mds_eq_dma)
  done


(* \<R> meets the criteria of a "simple bisim"
   which can be used to simplify the establishment of a refinement relation *)
lemma bisim_simple_\<R>\<^sub>1:
  "\<langle>c, mds, mem\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c', mds', mem'\<rangle> \<Longrightarrow> c = c'"
  apply(cases rule: \<R>\<^sub>1.cases, simp+)
  done

lemma bisim_simple_\<R>\<^sub>3:
  "lc \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> lc' \<Longrightarrow> (fst (fst lc)) = (fst (fst lc'))"
  apply(induct rule: \<R>\<^sub>3_aux.induct)
  using bisim_simple_\<R>\<^sub>1 apply clarsimp
  apply simp
  done

lemma bisim_simple_\<R>\<^sub>u:
  "lc \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> lc' \<Longrightarrow> (fst (fst lc)) = (fst (fst lc'))"
  apply(induct rule: \<R>.induct)
   apply clarsimp
   apply(cases rule: \<R>\<^sub>1.cases, simp+)
  apply(cases rule: \<R>\<^sub>3_aux.cases, simp+)
   apply blast
  using bisim_simple_\<R>\<^sub>3 apply clarsimp
  done


(* To prove that \<R> is a bisimulation, we first show symmetry *)

lemma \<C>_eq_type_max_eq:
  assumes wf: "type_wellformed t"
  assumes \<C>_eq: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>2 x" 
  shows "type_max t mem\<^sub>1 = type_max t mem\<^sub>2"
proof -
  have "\<forall>x\<in>vars_of_type t. mem\<^sub>1 x = mem\<^sub>2 x"
    using wf \<C>_eq unfolding type_wellformed_def by blast
  thus ?thesis
    unfolding type_max_def using eval_vars_det\<^sub>B by fastforce
qed

lemma vars_of_type_eq_type_max_eq:
  assumes mem_eq: "\<forall>x\<in>vars_of_type t. mem\<^sub>1 x = mem\<^sub>2 x" 
  shows "type_max t mem\<^sub>1 = type_max t mem\<^sub>2"
proof -
  from assms show ?thesis
    unfolding type_max_def using eval_vars_det\<^sub>B by fastforce
qed

lemma \<R>\<^sub>1_sym: "sym (\<R>\<^sub>1 \<Gamma>' \<S>' P')"
unfolding sym_def
proof clarsimp
  fix c mds mem c' mds' mem'
  assume in_\<R>\<^sub>1: "\<langle>c, mds, mem\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c', mds', mem'\<rangle>"
  then obtain \<Gamma> \<S> P where
  stuff: "c' = c"  "mds' = mds"  "\<turnstile> \<Gamma>,\<S>,P {c} \<Gamma>',\<S>',P'"  "tyenv_wellformed mds \<Gamma> \<S> P"
  "mem =\<^bsub>\<Gamma>\<^esub> mem'" "pred P mem" "pred P mem'"
  "\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem \<le> dma mem x"
    using \<R>\<^sub>1_elim' by blast+
  from stuff have stuff': "mem' =\<^bsub>\<Gamma>\<^esub> mem"
    by (metis tyenv_eq_sym)
  
  have "\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem' \<le> dma mem' x"
  proof -
    from in_\<R>\<^sub>1 have "dma mem = dma mem'"
      using \<R>\<^sub>1_dma_eq stuff by metis
    moreover have "\<forall>x\<in>dom \<Gamma>. type_max (the (\<Gamma> x)) mem = type_max (the (\<Gamma> x)) mem'"
    proof
      fix x
      assume "x \<in> dom \<Gamma>"
      hence "type_wellformed (the (\<Gamma> x))"
        using \<open>tyenv_wellformed mds \<Gamma> \<S> P\<close>
        by(auto simp: tyenv_wellformed_def types_wellformed_def)
      moreover have "\<forall>x\<in>\<C>. mem x = mem' x"
        using in_\<R>\<^sub>1 \<R>\<^sub>1_mem_eq \<C>_Low stuff
        unfolding low_mds_eq_def by auto
      ultimately
      show "type_max (the (\<Gamma> x)) mem = type_max (the (\<Gamma> x)) mem'"
        using \<C>_eq_type_max_eq by blast
    qed
    ultimately show ?thesis
      using stuff(8) by fastforce
  qed
  with stuff stuff'
  show "\<langle>c', mds', mem'\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c, mds, mem\<rangle>"
  by (metis (no_types) \<R>\<^sub>1.intro)
qed

lemma \<R>\<^sub>3_sym: "sym (\<R>\<^sub>3 \<Gamma> \<S> P)"
  unfolding sym_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds' mem\<^sub>2
  assume asm: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle>"
  hence [simp]: "mds' = mds"
    using \<R>\<^sub>3_elim' by blast
  from asm show "\<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>"
    apply auto
    apply (induct rule: \<R>\<^sub>3_aux.induct)
     apply (metis (lifting) \<R>\<^sub>1_sym \<R>\<^sub>3_aux.intro\<^sub>1 symD)
    by (metis (lifting) \<R>\<^sub>3_aux.intro\<^sub>3)
qed

lemma \<R>_mds [simp]: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds', mem\<^sub>2\<rangle> \<Longrightarrow> mds = mds'"
  apply (rule \<R>_elim')
     apply (auto)
   apply (metis \<R>\<^sub>1_elim')
  apply (insert \<R>\<^sub>3_elim')
  by blast

lemma \<R>_sym: "sym (\<R> \<Gamma> \<S> P)"
  unfolding sym_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds\<^sub>2 mem\<^sub>2
  assume asm: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma> \<S> P"
  with \<R>_mds have [simp]: "mds\<^sub>2 = mds"
    by blast
  from asm show "(\<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle>, \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>) \<in> \<R> \<Gamma> \<S> P"
    using \<R>.intro\<^sub>1 [of \<Gamma> \<S> P] and \<R>.intro\<^sub>3 [of _ \<Gamma> \<S> P]
    using \<R>\<^sub>1_sym [of \<Gamma>] and \<R>\<^sub>3_sym [of \<Gamma>]
    apply simp
    apply (erule \<R>_elim)
      by (auto simp: sym_def)
qed

(* Next, we show that the relations are closed under globally consistent changes *)

lemma \<R>\<^sub>1_closed_glob_consistent: "closed_glob_consistent (\<R>\<^sub>1 \<Gamma>' \<S>' P')"
  unfolding closed_glob_consistent_def
proof (clarify)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 A
  assume R1: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  hence [simp]: "c\<^sub>2 = c\<^sub>1" by blast
  assume A_updates_vars: "\<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds x"
  assume A_updates_dma: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x"
  assume A_updates_sec: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x = Low \<and> (x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>) \<longrightarrow> mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>2 [\<parallel>\<^sub>2 A] x"
  from R1 obtain \<Gamma> \<S> P where \<Gamma>_props: "\<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 } \<Gamma>',\<S>',P'" "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2" "tyenv_wellformed mds \<Gamma> \<S> P"
                                      "pred P mem\<^sub>1" "pred P mem\<^sub>2"
                                      "\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem\<^sub>1 \<le> dma mem\<^sub>1 x"
    by force

  from \<Gamma>_props(3) have stable_not_written: "\<forall>x. stable \<S> x \<longrightarrow> var_asm_not_written mds x"
    by(auto simp: tyenv_wellformed_def mds_consistent_def stable_def var_asm_not_written_def)
  with A_updates_vars have stable_unchanged\<^sub>1: "\<forall>x. stable \<S> x \<longrightarrow> (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = mem\<^sub>1 x" and
                           stable_unchanged\<^sub>2: "\<forall>x. stable \<S> x \<longrightarrow> (mem\<^sub>2 [\<parallel>\<^sub>2 A]) x = mem\<^sub>2 x"
    by(auto simp: apply_adaptation_def split: option.splits)

  from stable_not_written A_updates_dma 
  have stable_unchanged_dma\<^sub>1: "\<forall>x. stable \<S> x \<longrightarrow> dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = dma mem\<^sub>1 x"
    by(blast)

  have tyenv_eq': "mem\<^sub>1 [\<parallel>\<^sub>1 A] =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 [\<parallel>\<^sub>2 A]"
  proof(clarsimp simp: tyenv_eq_def)
    fix x
    assume a: "type_max (to_total \<Gamma> x) mem\<^sub>1 [\<parallel>\<^sub>1 A] = Low"
    show "mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>2 [\<parallel>\<^sub>2 A] x"
    proof(cases "x \<in> dom \<Gamma>")
      assume in_dom: "x \<in> dom \<Gamma>"
      with \<Gamma>_props(3) have "var_asm_not_written mds x"
        by(auto simp: tyenv_wellformed_def mds_consistent_def var_asm_not_written_def stable_def)
      hence [simp]: "mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>1 x" and [simp]: "mem\<^sub>2 [\<parallel>\<^sub>2 A] x = mem\<^sub>2 x"
        using A_updates_vars by(auto simp: apply_adaptation_def split: option.splits)
      from in_dom a obtain t\<^sub>x where \<Gamma>\<^sub>x: "\<Gamma> x = Some t\<^sub>x" and t\<^sub>x_Low': "type_max t\<^sub>x (mem\<^sub>1 [\<parallel>\<^sub>1 A]) = Low"
        by(auto simp: to_total_def)
      have t\<^sub>x_unchanged: "type_max t\<^sub>x (mem\<^sub>1 [\<parallel>\<^sub>1 A])  = type_max t\<^sub>x mem\<^sub>1"
      proof - 
        from \<Gamma>\<^sub>x \<Gamma>_props(3) have t\<^sub>x_stable: "type_stable \<S> t\<^sub>x" and t\<^sub>x_wellformed: "type_wellformed t\<^sub>x"
          by(force simp: tyenv_wellformed_def types_stable_def types_wellformed_def)+
        from t\<^sub>x_stable t\<^sub>x_wellformed stable_unchanged\<^sub>1 show ?thesis
          using type_stable_is_sufficient'
          by blast
      qed
      with t\<^sub>x_Low' have t\<^sub>x_Low: "type_max t\<^sub>x mem\<^sub>1 = Low" by simp
      with \<Gamma>\<^sub>x \<Gamma>_props(2) have "mem\<^sub>1 x = mem\<^sub>2 x"
        by(force simp: tyenv_eq_def to_total_def split: if_splits)
      thus ?thesis by simp
    next
      assume nin_dom: "x \<notin> dom \<Gamma>"
      with a have is_Low': "dma (mem\<^sub>1[\<parallel>\<^sub>1 A]) x = Low"
        by(simp add: to_total_def)
      show ?thesis
      proof(cases "x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>")
        assume "x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>"
        with is_Low' show ?thesis
          using A_updates_sec by blast
      next
        assume "\<not> (x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>)"
        hence "x \<in> mds AsmNoReadOrWrite" and "x \<notin> \<C>"
          by auto
        with nin_dom \<Gamma>_props(3) have "False"
          by(auto simp: tyenv_wellformed_def mds_consistent_def stable_def)
        thus ?thesis by blast
      qed
    qed
  qed
  
  have sec': "\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) (mem\<^sub>1 [\<parallel>\<^sub>1 A]) \<le> dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x"
  proof(intro ballI impI)
    fix x
    assume readable: "x \<notin> mds AsmNoReadOrWrite"
    assume in_dom: "x \<in> dom \<Gamma>"
    with \<Gamma>_props(3) have "var_asm_not_written mds x"
      by(auto simp: tyenv_wellformed_def mds_consistent_def var_asm_not_written_def stable_def)
    hence [simp]: "dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x = dma mem\<^sub>1 x"
      using A_updates_dma by(auto simp: apply_adaptation_def split: option.splits)
    from in_dom obtain t\<^sub>x where \<Gamma>\<^sub>x: "\<Gamma> x = Some t\<^sub>x"
      by(auto simp: to_total_def)
    have t\<^sub>x_unchanged: "type_max t\<^sub>x (mem\<^sub>1 [\<parallel>\<^sub>1 A])  = type_max t\<^sub>x mem\<^sub>1"
    proof - 
      from \<Gamma>\<^sub>x \<Gamma>_props(3) have t\<^sub>x_stable: "type_stable \<S> t\<^sub>x" and t\<^sub>x_wellformed: "type_wellformed t\<^sub>x"
        by(force simp: tyenv_wellformed_def types_stable_def types_wellformed_def)+
      from t\<^sub>x_stable t\<^sub>x_wellformed stable_unchanged\<^sub>1 show ?thesis
        using type_stable_is_sufficient'
        by blast
    qed
    with \<Gamma>\<^sub>x have [simp]:"type_max (the (\<Gamma> x)) (mem\<^sub>1 [\<parallel>\<^sub>1 A]) = type_max (the (\<Gamma> x)) mem\<^sub>1"
      by simp
    show "type_max (the (\<Gamma> x)) mem\<^sub>1 [\<parallel>\<^sub>1 A] \<le> dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x "
      apply simp
      using in_dom readable \<Gamma>_props by metis
  qed
    
  from stable_unchanged\<^sub>1 stable_unchanged\<^sub>2 \<Gamma>_props(3) have "\<forall>p\<in>P. ev\<^sub>B (mem\<^sub>1 [\<parallel>\<^sub>1 A]) p = ev\<^sub>B mem\<^sub>1 p \<and> ev\<^sub>B (mem\<^sub>2 [\<parallel>\<^sub>2 A]) p = ev\<^sub>B mem\<^sub>2 p"
    apply(intro ballI)
    apply(rule conjI)
    by(rule eval_vars_det\<^sub>B,force simp: tyenv_wellformed_def mds_consistent_def stable_def)+
    
  hence "pred P (mem\<^sub>1 [\<parallel>\<^sub>1 A]) = pred P mem\<^sub>1" and
        "pred P (mem\<^sub>2 [\<parallel>\<^sub>2 A]) = pred P mem\<^sub>2"
    by(simp add: pred_def)+
  
  with \<Gamma>_props tyenv_eq' sec'
  show "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle>"
    by auto
qed


lemma \<R>\<^sub>3_closed_glob_consistent:
  "closed_glob_consistent (\<R>\<^sub>3 \<Gamma>' \<S>' P')"
unfolding closed_glob_consistent_def
proof(clarsimp)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 A
  assume in_\<R>\<^sub>3: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  assume A_modifies_vars: "\<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds x"
  assume A_modifies_dma: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x"
  assume A_modifies_sec: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x = Low \<and> (x \<in> mds AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow> mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>2 [\<parallel>\<^sub>2 A] x"
  (* do a bit of massaging to get the goal state set-up nicely for the induction rule *)
  define lc\<^sub>1 where "lc\<^sub>1 \<equiv> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>"
  define lc\<^sub>2 where "lc\<^sub>2 \<equiv> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  from lc\<^sub>1_def lc\<^sub>2_def in_\<R>\<^sub>3 have "lc\<^sub>1 \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> lc\<^sub>2" by simp
  from this lc\<^sub>1_def lc\<^sub>2_def A_modifies_vars A_modifies_dma A_modifies_sec
  show "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle>"
  proof(induct arbitrary: c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mds mem\<^sub>2 rule: \<R>\<^sub>3_aux.induct)
    case (intro\<^sub>1 c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P')
    show ?case
      apply (rule \<R>\<^sub>3_aux.intro\<^sub>1[OF _ intro\<^sub>1(2)])
      using \<R>\<^sub>1_closed_glob_consistent intro\<^sub>1
      unfolding closed_glob_consistent_def by blast
  next
    case (intro\<^sub>3 c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P')
    show ?case
      apply(rule \<R>\<^sub>3_aux.intro\<^sub>3)
      apply(rule intro\<^sub>3(2))
      using intro\<^sub>3 apply simp+
      done
  qed
qed


lemma \<R>_closed_glob_consistent: "closed_glob_consistent (\<R> \<Gamma>' \<S>' P')"
  unfolding closed_glob_consistent_def
proof (clarify, erule \<R>_elim, simp_all)
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 A
  assume R1: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  and A_modifies_vars: "\<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds x"
  and A_modifies_dma: "\<forall>x. dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x"
  and A_modifies_sec: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x = Low \<and> (x \<in> mds AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow> mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>2 [\<parallel>\<^sub>2 A] x"  
  show
    "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle>"
    apply(rule intro\<^sub>1)
    apply clarify
    using \<R>\<^sub>1_closed_glob_consistent unfolding closed_glob_consistent_def
    using R1 A_modifies_vars A_modifies_dma A_modifies_sec
    by blast
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 x A
  assume R3: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  and A_modifies_vars: "\<forall>x. case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v' \<longrightarrow> \<not> var_asm_not_written mds x"
  and A_modifies_dma: "\<forall>x. dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x"
  and A_modifies_sec: "\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x = Low \<and> (x \<in> mds AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow> mem\<^sub>1 [\<parallel>\<^sub>1 A] x = mem\<^sub>2 [\<parallel>\<^sub>2 A] x"
  show "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle> "
    apply(rule intro\<^sub>3)
    using \<R>\<^sub>3_closed_glob_consistent unfolding closed_glob_consistent_def
    using R3 A_modifies_vars A_modifies_dma A_modifies_sec
    by blast
qed

(* It now remains to show that steps of the first of two related configurations
    can be matched by the second: *)

(* Some technical lemmas: *)
lemma mode_update_add_anno:
  "mds_consistent mds \<Gamma> \<S> P \<Longrightarrow> 
   mds_consistent (update_modes upd mds) 
                  (\<Gamma> \<oplus>\<^sub>\<S> upd) 
                  (add_anno_stable \<S> upd) 
                  (P |` {v. stable (add_anno_stable \<S> upd) v})"
  apply(case_tac upd)
   apply(rename_tac v m)
   apply(case_tac m)
      apply((clarsimp simp: add_anno_def mds_consistent_def stable_def restrict_preds_to_vars_def | safe | fastforce)+)[4]
  apply(rename_tac v m)
  apply(case_tac m)
     apply((clarsimp simp: add_anno_def mds_consistent_def stable_def restrict_preds_to_vars_def | safe | fastforce)+)[4]
  done

lemma add_anno_acq_GuarNoReadOrWrite [simp]:
  "\<Gamma> \<oplus>\<^sub>\<S> (v +=\<^sub>m GuarNoReadOrWrite) = \<Gamma>"
  apply(clarsimp simp: add_anno_def to_total_def restrict_map_def)
  apply(rule ext)
  apply(clarsimp | safe)+
  by (metis option.collapse prod.collapse)

lemma add_anno_rel_GuarNoReadOrWrite [simp]:
  "\<Gamma> \<oplus>\<^sub>\<S> (v -=\<^sub>m GuarNoReadOrWrite) = \<Gamma>"
  apply(clarsimp simp: add_anno_def to_total_def restrict_map_def)
  apply(rule ext)
  apply(clarsimp | safe)+
  by (metis option.collapse)

lemma add_anno_acq_GuarNoWrite [simp]:
  "\<Gamma> \<oplus>\<^sub>\<S> (v +=\<^sub>m GuarNoWrite) = \<Gamma>"
  apply(clarsimp simp: add_anno_def to_total_def restrict_map_def)
  apply(rule ext)
  apply(clarsimp | safe)+
  by (metis option.collapse prod.collapse)

lemma add_anno_rel_GuarNoWrite [simp]:
  "\<Gamma> \<oplus>\<^sub>\<S> (v -=\<^sub>m GuarNoWrite) = \<Gamma>"
  apply(clarsimp simp: add_anno_def to_total_def restrict_map_def)
  apply(rule ext)
  apply(clarsimp | safe)+
  by (metis option.collapse)

lemma dom_add_anno_rel:
  "\<forall>x\<in>dom (\<Gamma> \<oplus>\<^sub>\<S> (v -=\<^sub>m m)). (\<Gamma> \<oplus>\<^sub>\<S> (v -=\<^sub>m m)) x = \<Gamma> x"
  apply(clarsimp simp: add_anno_def to_total_def restrict_map_def split: if_splits)
  apply(case_tac m)
  apply(auto split: if_splits)
  done

lemma types_wellformed_mode_update:
  "types_wellformed \<Gamma> \<Longrightarrow>
   types_wellformed (\<Gamma> \<oplus>\<^sub>\<S> upd)"
  apply(clarsimp simp: types_wellformed_def)
  apply(case_tac upd)
   apply(rename_tac v t v' m)
   apply(case_tac m)
      apply clarsimp
      apply(case_tac "v' \<in> dom \<Gamma> \<or> v' \<in> \<C>")
       apply(clarsimp, force)
      apply(simp split: if_splits)
       apply(drule sym, fastforce)
      apply(clarsimp | force )+
     apply(case_tac "v' \<in> dom \<Gamma> \<or> v' \<in> \<C>")
      apply clarsimp
      apply force
     apply(simp split: if_splits)
      apply(drule sym, fastforce)
     apply(clarsimp | force)+
  using dom_add_anno_rel[THEN bspec, OF domI]
  apply (metis domI option.sel)
  done
  
(* TODO: consider putting this proof into Isar so we can explain the reasoning behind the
   anno_type_stable predicate *)
lemma types_stable_mode_update:
   "types_stable \<Gamma> \<S> \<Longrightarrow> types_wellformed \<Gamma> \<Longrightarrow> anno_type_stable \<Gamma> \<S> upd
    \<Longrightarrow> types_stable (\<Gamma> \<oplus>\<^sub>\<S> upd) (add_anno_stable \<S> upd)"
  apply(clarsimp simp: types_stable_def)
  apply(rename_tac x c f C)
  apply(case_tac upd)
   apply(rename_tac v m)
   apply(case_tac m)
      apply clarsimp
      apply(case_tac "v \<in> dom \<Gamma> \<or> v \<in> \<C>")
       apply clarsimp
       apply(force simp: stable_def)
      apply(simp split: if_splits)
       using \<C>_vars_correct
       apply(fastforce simp:  anno_type_stable_def stable_def)
      apply(force simp: stable_def)
     apply clarsimp
     apply(case_tac "v \<in> dom \<Gamma> \<or> v \<in> \<C>")
      apply clarsimp
      apply(force simp: stable_def)
     apply(simp split: if_splits)
      using \<C>_vars_correct
      apply(fastforce simp: anno_type_stable_def stable_def)
     apply(force simp: stable_def)
    apply(force simp: stable_def)
   apply(force simp: stable_def)
  apply(rename_tac v m)
  apply(subgoal_tac "\<Gamma> x = Some (C)")
   prefer 2
   using dom_add_anno_rel
   apply (metis domI)
  apply(case_tac m)
     apply(clarsimp simp: anno_type_stable_def split: if_splits)
      apply(clarsimp simp: stable_def types_wellformed_def type_wellformed_def)
      using \<C>_vars_correct
      apply (metis (mono_tags, lifting) UN_I contra_subsetD domI option.sel)
     apply(clarsimp simp: stable_def types_wellformed_def type_wellformed_def)
     using \<C>_vars_correct
     apply (metis (mono_tags, lifting) UN_I contra_subsetD domI option.sel)
    apply(clarsimp simp: anno_type_stable_def split: if_splits)
     apply(clarsimp simp: stable_def types_wellformed_def type_wellformed_def)
     apply (metis (mono_tags, lifting) UN_I contra_subsetD domI option.sel)
    apply(clarsimp simp: stable_def)
    apply (metis (no_types, lifting) domI option.sel snd_conv subsetD type_wellformed_def types_wellformed_def)
   apply(clarsimp simp: anno_type_stable_def split: if_splits)
   apply(clarsimp simp: stable_def)
   apply (metis (no_types, lifting) domI option.sel snd_conv subsetD type_wellformed_def types_wellformed_def)
  apply(clarsimp simp: stable_def)
  apply (metis (no_types, lifting) domI option.sel snd_conv subsetD type_wellformed_def types_wellformed_def)
  done  
     
     
lemma tyenv_wellformed_mode_update:
  "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> anno_type_stable \<Gamma> \<S> upd \<Longrightarrow>
   tyenv_wellformed (update_modes upd mds) 
                  (\<Gamma> \<oplus>\<^sub>\<S> upd) 
                  (add_anno_stable \<S> upd) 
                  (P |` {v. stable (add_anno_stable \<S> upd) v})"
  apply(clarsimp simp: tyenv_wellformed_def)
  apply(rule conjI)
   apply(blast intro: mode_update_add_anno)
  apply(rule conjI)
   apply(blast intro: types_wellformed_mode_update)
  apply(blast intro: types_stable_mode_update)
  done


lemma stop_cxt :
  "\<lbrakk> \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P' ; c = Stop \<rbrakk> \<Longrightarrow> 
  context_equiv \<Gamma> P \<Gamma>' \<and> \<S>' = \<S> \<and> P \<turnstile> P' \<and> (\<forall>mds. tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds \<Gamma>' \<S> P')"
  apply (induct rule: has_type.induct)
          apply (auto intro: context_equiv_trans context_equiv_entailment pred_entailment_trans)
  done

lemma tyenv_wellformed_preds_update:
  "P' = P'' |` {v. stable \<S> v} \<Longrightarrow>
  tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> tyenv_wellformed mds \<Gamma> \<S> P'"
  apply(clarsimp simp: tyenv_wellformed_def)
  apply(clarsimp simp: mds_consistent_def)
  apply(auto simp: restrict_preds_to_vars_def add_pred_def split: if_splits)
  done


lemma mds_consistent_preds_tyenv_update:
  "P' = P'' |` {v. stable \<S> v} \<Longrightarrow> v \<in> dom \<Gamma> \<Longrightarrow>
  mds_consistent mds \<Gamma> \<S> P \<Longrightarrow> mds_consistent mds (\<Gamma>(v \<mapsto> t)) \<S> P'"
  apply(clarsimp simp: mds_consistent_def)
  apply(auto simp: restrict_preds_to_vars_def add_pred_def split: if_splits)
  done


lemma pred_preds_update:
  assumes mem'_def: "mem' = mem (x := ev\<^sub>A mem e)" 
  assumes P'_def: "P' = (assign_post P x e) |` {v. stable \<S> v}"
  assumes pred_P: "pred P mem" 
  shows "pred P' mem'"
proof -
  from P'_def have P'_def': "P' \<subseteq> assign_post P x e"
    by(auto simp: restrict_preds_to_vars_def add_pred_def split: if_splits)
  have "pred (assign_post P x e) mem'"
    using assign_post_valid pred_P mem'_def by blast
  with P'_def' show ?thesis
    unfolding pred_def by blast
qed

lemma types_wellformed_update:
  "types_wellformed \<Gamma> \<Longrightarrow> type_wellformed t \<Longrightarrow> types_wellformed (\<Gamma>(x \<mapsto> t))"
  by(auto simp: types_wellformed_def)

lemma types_stable_update:
  "types_stable \<Gamma> \<S> \<Longrightarrow> type_stable \<S> t \<Longrightarrow> types_stable (\<Gamma>(x \<mapsto> t)) \<S>"
  by(auto simp: types_stable_def)
  
lemma tyenv_wellformed_sub:
  "\<lbrakk>P\<^sub>1 \<subseteq> P\<^sub>2;
  \<Gamma>\<^sub>2 = \<Gamma>\<^sub>1; tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2\<rbrakk> \<Longrightarrow>
     tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1"
  apply(clarsimp simp: tyenv_wellformed_def | safe)+
  apply(fastforce simp: mds_consistent_def)
  done

abbreviation
  tyenv_sec :: "'Var Mds \<Rightarrow> ('Var,'BExp) TyEnv \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> bool"
where
  "tyenv_sec mds \<Gamma> mem \<equiv> \<forall>x\<in>dom \<Gamma>. x\<notin>mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem \<le> dma mem x"

lemma tyenv_sec_mode_update:
  "(\<forall>x.  (to_total \<Gamma> x) \<le>:\<^sub>P''  (to_total \<Gamma>'' x)) \<Longrightarrow> pred P'' mem \<Longrightarrow> \<S> = (mds AsmNoWrite, mds AsmNoReadOrWrite) \<Longrightarrow>
    anno_type_sec \<Gamma> \<S> P upd \<Longrightarrow> \<S>'' = add_anno_stable \<S> upd \<Longrightarrow> (\<forall>p\<in>P. \<forall>v\<in>bexp_vars p. stable \<S> v) \<Longrightarrow>
  P'' = P |` {v. stable \<S>'' v} \<Longrightarrow>
    \<Gamma>'' = \<Gamma> \<oplus>\<^sub>\<S> upd \<Longrightarrow> tyenv_sec mds \<Gamma> mem \<Longrightarrow> tyenv_sec (update_modes upd mds) \<Gamma>'' mem"
  apply(case_tac upd)
   apply(rename_tac v m)
   apply(case_tac m)
    apply(auto simp: add_anno_def to_total_def)[4]
  apply(rename_tac v m)
  apply(case_tac m)
    apply(subgoal_tac "v \<in> mds AsmNoWrite \<longrightarrow> P'' = P")
    by(auto simp: add_anno_def to_total_def dest: subtype_sound split: if_splits simp: anno_type_sec_def restrict_preds_to_vars_def stable_def)


lemma tyenv_sec_eq:
  "\<forall>x\<in>\<C>. mem x = mem' x \<Longrightarrow> types_wellformed \<Gamma> \<Longrightarrow> tyenv_sec mds \<Gamma> mem = tyenv_sec mds \<Gamma> mem'"
  apply(rule ball_cong[OF HOL.refl])
  apply(rename_tac x)
  apply(rule imp_cong[OF HOL.refl])
  apply(subgoal_tac "type_max (the (\<Gamma> x)) mem = type_max (the (\<Gamma> x)) mem'")
   using dma_\<C> apply fastforce
  apply(force intro: \<C>_eq_type_max_eq simp: types_wellformed_def)
  done

lemma context_equiv_tyenv_sec:
  "context_equiv \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>1 \<Longrightarrow>
    pred P\<^sub>2 mem \<Longrightarrow> tyenv_sec mds \<Gamma>\<^sub>2 mem \<Longrightarrow> tyenv_sec mds \<Gamma>\<^sub>1 mem"
   apply(clarsimp simp: context_equiv_def type_equiv_def)
   apply(rename_tac x y)
   apply(rule_tac y="type_max (the (\<Gamma>\<^sub>2 x)) mem" in order_trans)
    apply(rule subtype_sound[rule_format])
     apply force
    apply assumption
   apply force
   done

lemma add_pred_entailment:
  "P +\<^sub>\<S> p \<turnstile> P"
  apply(rule subset_entailment)
  apply(rule add_pred_subset)
  done


lemma preservation_no_await: 
  "\<lbrakk>\<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P';
    \<langle>c, mds, mem\<rangle> \<leadsto>  \<langle>c', mds', mem'\<rangle>;
    no_await c\<rbrakk> \<Longrightarrow> 
  \<exists> \<Gamma>'' \<S>'' P''. (\<turnstile> \<Gamma>'',\<S>'',P'' { c' } \<Gamma>',\<S>',P') \<and> 
         (tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> 
           tyenv_wellformed mds' \<Gamma>'' \<S>'' P'' \<and> 
           pred P'' mem' \<and> 
           tyenv_sec mds' \<Gamma>'' mem')"
proof (induct arbitrary: c' mds rule: has_type.induct)
  
  case (anno_type \<Gamma>'' \<Gamma> \<S> upd \<S>'' P'' P c\<^sub>1 \<Gamma>' \<S>' P')
  hence step: "\<langle>c\<^sub>1, update_modes upd mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
    by (metis upd_elim)
  from \<open>no_await (c\<^sub>1@[upd])\<close> no_await.cases have "no_await c\<^sub>1" by fast
  with step anno_type(5) obtain \<Gamma>''' \<S>''' P''' where
    "\<turnstile> \<Gamma>''',\<S>''',P''' { c' } \<Gamma>',\<S>',P' \<and> 
    (tyenv_wellformed (update_modes upd mds) \<Gamma>'' \<S>'' P'' \<and> pred P'' mem \<and> tyenv_sec (update_modes upd mds) \<Gamma>'' mem \<longrightarrow>
       tyenv_wellformed mds' \<Gamma>''' \<S>''' P''' \<and> pred P''' mem' \<and> tyenv_sec mds' \<Gamma>''' mem')"
    by blast
  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed (update_modes upd mds) \<Gamma>'' \<S>'' P''"
    using anno_type
    apply auto
    by (metis tyenv_wellformed_mode_update)
  moreover
  have pred: "pred P mem \<longrightarrow> pred P'' mem"
    using anno_type
    by (auto simp: pred_def restrict_preds_to_vars_def)
  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec (update_modes upd mds) \<Gamma>'' mem"
    apply(rule impI)
    apply(rule tyenv_sec_mode_update)
            using anno_type apply fastforce
           using anno_type pred apply fastforce
          using anno_type apply fastforce
         using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
        using anno_type apply fastforce
       apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
      apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
     using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
    by simp  
  ultimately show ?case
    by blast
next
  case stop_type
  with stop_no_eval show ?case by auto
next
  case skip_type
  hence "c' = Stop \<and> mds' = mds \<and> mem' = mem"
    by (metis skip_elim)
  thus ?case
    by (metis stop_type)
next
  case (assign\<^sub>1 x \<Gamma> e t P P' \<S> c' mds)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  from assign\<^sub>1(2) upd have \<C>_eq: "\<forall>x\<in>\<C>. mem x = mem' x"
    by auto
  from upd have " \<turnstile> \<Gamma>,\<S>,P' {c'} \<Gamma>,\<S>,P'"
    by (metis stop_type)
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>1 by metis
  moreover have "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>1 upd by metis
    
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P  \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds \<Gamma> mem'"
    using tyenv_sec_eq[OF \<C>_eq, where \<Gamma>=\<Gamma>]
    unfolding tyenv_wellformed_def by blast
  ultimately show ?case
    by (metis upd)
next
  case (assign\<^sub>2 x \<Gamma> e t \<S> P' P c' mds)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  let ?\<Gamma>' = "\<Gamma> (x \<mapsto> t)"
  from upd have ty: " \<turnstile> ?\<Gamma>',\<S>,P' {c'} ?\<Gamma>',\<S>,P'"
    by (metis stop_type)
  have wf: "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
  proof
    assume tyenv_wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    hence wf: "types_wellformed \<Gamma>"
      unfolding tyenv_wellformed_def by blast
    hence  "type_wellformed t"
      using assign\<^sub>2(2) type_aexpr_type_wellformed
      by blast
    with wf have wf': "types_wellformed ?\<Gamma>'"
      using types_wellformed_update by metis
    from tyenv_wf have stable': "types_stable ?\<Gamma>' \<S>"
      using types_stable_update
            assign\<^sub>2(3)
      unfolding tyenv_wellformed_def by blast
    have m: "mds_consistent mds \<Gamma> \<S> P"
      using tyenv_wf unfolding tyenv_wellformed_def by blast
    from assign\<^sub>2(4) assign\<^sub>2(1)
    have "mds_consistent mds' (\<Gamma>(x \<mapsto> t)) \<S> P'"
      apply(rule mds_consistent_preds_tyenv_update)
      using upd m by simp
    from wf' stable' this show "tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
      unfolding tyenv_wellformed_def by blast
  qed
  have p: "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>2 upd by metis
  have sec: "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> pred P mem \<Longrightarrow> tyenv_sec mds \<Gamma> mem \<Longrightarrow> tyenv_sec mds' ?\<Gamma>' mem'"
  proof(clarify)
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem"
    assume sec: "tyenv_sec mds \<Gamma> mem"
    from pred p have pred': "pred P' mem'" by blast
    fix v t'
    assume \<Gamma>v: "(\<Gamma>(x \<mapsto> t)) v = Some t'"
    assume "v \<notin> mds' AsmNoReadOrWrite"
    show "type_max (the ((\<Gamma>(x \<mapsto> t)) v)) mem' \<le> dma mem' v"
    proof(cases "v = x")
      assume [simp]: "v = x"
      hence [simp]: "(the ((\<Gamma>(x \<mapsto> t)) v)) = t" and t_def: "t = t'"
        using \<Gamma>v by auto
      from \<open>v \<notin> mds' AsmNoReadOrWrite\<close> upd wf have readable: "v \<notin> snd \<S>"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      with assign\<^sub>2(5) have "t \<le>:\<^sub>P' (dma_type x)" by fastforce
      with pred' show ?thesis
        using type_max_dma_type subtype_correct
        by fastforce
    next
      assume neq: "v \<noteq> x"
      hence [simp]: "((\<Gamma>(x \<mapsto> t)) v) = \<Gamma> v"
        by simp
      with \<Gamma>v have \<Gamma>v: "\<Gamma> v = Some t'" by simp
      with sec upd \<open>v \<notin> mds' AsmNoReadOrWrite\<close> have f_leq: "type_max t' mem \<le> dma mem v"
        by auto
      have \<C>_eq: "\<forall>x\<in>\<C>. mem x = mem' x"
        using wf assign\<^sub>2(1) upd by(auto simp: tyenv_wellformed_def mds_consistent_def)
      hence dma_eq: "dma mem = dma mem'"
        by(rule dma_\<C>)
      have f_eq: "type_max t' mem = type_max t' mem'"
        apply(rule \<C>_eq_type_max_eq)
         using \<Gamma>v wf apply(force simp: tyenv_wellformed_def types_wellformed_def)
        by(rule \<C>_eq)     
      from neq \<Gamma>v f_leq dma_eq f_eq show ?thesis
        by simp
    qed
  qed
  from ty wf p sec show ?case
    by blast
next
  case (assign\<^sub>\<C> x \<Gamma> e t P P' \<S> c' mds)
  (* this case follows from the same argument as assign\<^sub>1 *)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  hence " \<turnstile> \<Gamma>,\<S>,P' {c'} \<Gamma>,\<S>,P'"
    by (metis stop_type)
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>\<C> by metis
  moreover have "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<Longrightarrow> tyenv_sec mds' \<Gamma> mem'"
  proof(clarify)
    fix v t'
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem"
    hence pred': "pred P' mem'" using \<open>pred P mem \<longrightarrow> pred P' mem'\<close> by blast
    assume sec: "tyenv_sec mds \<Gamma> mem"
    assume \<Gamma>v: "\<Gamma> v = Some t'"
    assume readable': "v \<notin> mds' AsmNoReadOrWrite"
    with upd have readable: "v \<notin> mds AsmNoReadOrWrite" by simp
    with wf have "v \<notin> snd \<S>" by(auto simp: tyenv_wellformed_def mds_consistent_def)
    show "type_max (the (\<Gamma> v)) mem' \<le> dma mem' v"
    proof(cases "x \<in> \<C>_vars v")
      assume "x \<in> \<C>_vars v"
      with assign\<^sub>\<C>(6) \<open>v \<notin> snd \<S>\<close> have "(to_total \<Gamma> v) \<le>:\<^sub>P' (dma_type v)" by blast
      from pred' \<Gamma>v subtype_correct this show ?thesis
        using type_max_dma_type by(auto simp: to_total_def split: if_splits)
    next
      assume "x \<notin> \<C>_vars v"
      hence "\<forall>v'\<in>\<C>_vars v. mem v' = mem' v'"
        using upd by auto
      hence dma_eq: "dma mem v = dma mem' v"
        by(rule dma_\<C>_vars)
      from \<Gamma>v assign\<^sub>\<C>(4) have "x \<notin> vars_of_type t'" by force
      have "type_wellformed t'"
        using wf \<Gamma>v by(force simp: tyenv_wellformed_def types_wellformed_def)
      with \<open>x \<notin> vars_of_type t'\<close> upd have f_eq: "type_max t' mem = type_max t' mem'"
        using vars_of_type_eq_type_max_eq by fastforce
      from sec \<Gamma>v readable have "type_max t' mem \<le> dma mem v"
        by auto
      with f_eq dma_eq \<Gamma>v show ?thesis
        by simp
    qed
  qed
  ultimately show ?case
    by (metis)
next
  case (if_type \<Gamma> e t P \<S> th \<Gamma>' \<S>' P' el \<Gamma>'' P'' \<Gamma>''' P''' c' mds)
  from if_type(13)
  show ?case
  proof(rule if_elim)
    assume [simp]: "ev\<^sub>B mem e" and [simp]: "c' = th" and [simp]: "mem' = mem" and [simp]: "mds' = mds"
    from if_type(3) have " \<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> e {c'} \<Gamma>',\<S>',P'" by simp
    hence "\<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> e {c'} \<Gamma>''',\<S>',P'''"
      apply(rule sub)
           apply simp+
         using if_type apply blast
        using if_type apply blast
       apply simp
      using if_type apply(blast intro: pred_entailment_trans)
      done
    moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> (P +\<^sub>\<S> e)"
      by(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)
    moreover have "pred P mem \<longrightarrow> pred (P +\<^sub>\<S> e) mem'"
      by(auto simp: pred_def add_pred_def)
    moreover have "tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds' \<Gamma> mem'"
      by(simp)
    ultimately show ?case by blast
  next
    assume [simp]: "\<not> ev\<^sub>B mem e" and [simp]: "c' = el" and [simp]: "mem' = mem" and [simp]: "mds' = mds"
    from if_type(5) have " \<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> bexp_neg e {c'} \<Gamma>'',\<S>',P''" by simp
    hence "\<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> bexp_neg e {c'} \<Gamma>''',\<S>',P'''"
      apply(rule sub)
           apply simp+
         using if_type apply blast
        using if_type apply blast
       apply simp
      using if_type apply(blast intro: pred_entailment_trans)
      done
    moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> (P +\<^sub>\<S> bexp_neg e)"
      by(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)
    moreover have "pred P mem \<longrightarrow> pred (P +\<^sub>\<S> bexp_neg e) mem'"
      by(auto simp: pred_def add_pred_def bexp_neg_negates)
    moreover have "tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds' \<Gamma> mem'"
      by(simp)
    ultimately show ?case by blast
  qed
next
  case (while_type \<Gamma> e t P \<S> c c' mds)
  hence [simp]: "mds' = mds \<and> c' = If e (c ;; While e c) Stop \<and> mem' = mem"
    by (metis while_elim)
  have " \<turnstile> \<Gamma>,\<S>,P {c'} \<Gamma>,\<S>,P"
    apply simp
    apply(rule if_type)
             apply(rule while_type(1))
            apply(rule while_type(2))
           apply(rule seq_type)
            apply(rule while_type(3))
           apply(rule has_type.while_type)
             apply(rule while_type(1))
            apply(rule while_type(2))
           apply(rule while_type(3))
          apply(rule stop_type)
         apply simp
        apply simp
       apply simp
      apply(rule add_pred_entailment)
      apply simp+
    by(blast intro!: tyenv_wellformed_subset add_pred_subset)
  thus ?case
    by fastforce
next
  case (seq_type \<Gamma> \<S> P c\<^sub>1 \<Gamma>\<^sub>1 \<S>\<^sub>1 P\<^sub>1 c\<^sub>2 \<Gamma>\<^sub>2 \<S>\<^sub>2 P\<^sub>2 c' mds)
  thus ?case
  proof (cases "c\<^sub>1 = Stop")
    assume [simp]: "c\<^sub>1 = Stop"
    with seq_type have [simp]: "mds' = mds" and [simp]: "c' = c\<^sub>2" and [simp]: "mem' = mem"
      by (metis seq_stop_elim)+
    have context_eq: "context_equiv \<Gamma> P \<Gamma>\<^sub>1" and [simp]: "\<S>\<^sub>1 = \<S>" and entail: "P \<turnstile> P\<^sub>1" and
             wf_imp: "\<forall>mds. tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1"
      using stop_cxt seq_type(1) by simp+
    have "\<turnstile> \<Gamma>,\<S>,P {c\<^sub>2} \<Gamma>\<^sub>2,\<S>\<^sub>2,P\<^sub>2"
      apply(rule sub)
            using seq_type(3) apply simp
           apply(rule context_eq)
          apply(rule wf_imp)
         apply simp+
       apply(rule entail)
      apply(rule pred_entailment_refl)
      done
    thus ?case
      by fastforce
  next
    assume "c\<^sub>1 \<noteq> Stop"
    then obtain c\<^sub>1' where step: "\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = (c\<^sub>1' ;; c\<^sub>2)"
      by (metis seq_elim seq_type.prems)
    then have "no_await c\<^sub>1" using \<open>no_await (c\<^sub>1 ;; c\<^sub>2)\<close> no_await.cases by blast
    then obtain \<Gamma>''' \<S>''' P''' where "\<turnstile> \<Gamma>''',\<S>''',P''' {c\<^sub>1'} \<Gamma>\<^sub>1,\<S>\<^sub>1,P\<^sub>1 \<and>
      (tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> 
       tyenv_wellformed mds' \<Gamma>''' \<S>''' P''' \<and> pred P''' mem' \<and> tyenv_sec mds' \<Gamma>''' mem')"
      using step seq_type(2)
      by blast
    moreover
    from seq_type have "\<turnstile> \<Gamma>\<^sub>1,\<S>\<^sub>1,P\<^sub>1 {c\<^sub>2} \<Gamma>\<^sub>2,\<S>\<^sub>2,P\<^sub>2" by auto
    moreover
    ultimately show ?case
      apply (rule_tac x = \<Gamma>''' in exI)
      using \<open>\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = c\<^sub>1' ;; c\<^sub>2\<close> by blast
  qed
next
  case (sub \<Gamma>\<^sub>1 \<S> P\<^sub>1 c \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>2' P\<^sub>2' c' mds)
  then obtain \<Gamma>'' \<S>'' P'' where stuff: "\<turnstile> \<Gamma>'',\<S>'',P'' { c' } \<Gamma>\<^sub>1',\<S>',P\<^sub>1' \<and>
    (tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem \<longrightarrow> 
     tyenv_wellformed mds' \<Gamma>'' \<S>'' P'' \<and> pred P'' mem' \<and> tyenv_sec mds' \<Gamma>'' mem')"
    by force

  have imp: "tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<and> pred P\<^sub>2 mem \<and> tyenv_sec mds \<Gamma>\<^sub>2 mem \<Longrightarrow> 
             tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem"
    apply(rule conjI)
     using sub(5) sub(4) tyenv_wellformed_sub unfolding pred_def
     apply blast
    apply(rule conjI) 
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    using sub(3) context_equiv_tyenv_sec unfolding pred_def by blast
  show ?case
    apply (rule_tac x = \<Gamma>'' in exI, rule_tac x = "\<S>''" in exI, rule_tac x="P''" in exI)  
    apply (rule conjI)
     apply(rule has_type.sub)
           apply(rule stuff[THEN conjunct1])
          apply simp+
        apply(rule sub(5))
       apply(rule sub(6))
      apply simp
     using sub apply blast
    using imp stuff apply blast
   done
next
  case (await_type \<Gamma> e t P \<S> c \<Gamma>' \<S>' P' c' mds)
    show ?case using no_await_no_await await_type.prems by blast 
qed


lemma preservation_no_await_plus: 
  "\<lbrakk>\<langle>c, mds, mem\<rangle> \<leadsto>\<^sup>+ \<langle>c', mds', mem'\<rangle>;
    \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P';
    no_await c\<rbrakk> \<Longrightarrow> 
     no_await c' \<and> (\<exists> \<Gamma>'' \<S>'' P''. (\<turnstile> \<Gamma>'',\<S>'',P'' { c' } \<Gamma>',\<S>',P') \<and> 
     (tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> 
     tyenv_wellformed mds' \<Gamma>'' \<S>'' P'' \<and> pred P'' mem' \<and> tyenv_sec mds' \<Gamma>'' mem'))"
  apply (induct arbitrary: \<Gamma> \<S> P rule: my_trancl_step_induct3)
   using preservation_no_await no_await_trans apply fast
  using preservation_no_await no_await_trans by metis 

(* First we show that (roughly) typeability is preserved by evaluation steps *)
lemma preservation:
  assumes typed: "\<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P'"
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  shows "\<exists> \<Gamma>'' \<S>'' P''. (\<turnstile> \<Gamma>'',\<S>'',P'' { c' } \<Gamma>',\<S>',P') \<and> 
                    (tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> 
                      tyenv_wellformed mds' \<Gamma>'' \<S>'' P'' \<and> pred P'' mem' \<and> tyenv_sec mds' \<Gamma>'' mem')"
  using typed eval
proof (induct arbitrary: c' mds rule: has_type.induct)

  case (anno_type \<Gamma>'' \<Gamma> \<S> upd \<S>'' P'' P c\<^sub>1 \<Gamma>' \<S>' P')
  hence "\<langle>c\<^sub>1, update_modes upd mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
    by (metis upd_elim)
  with anno_type(5) obtain \<Gamma>''' \<S>''' P''' where
    "\<turnstile> \<Gamma>''',\<S>''',P''' { c' } \<Gamma>',\<S>',P' \<and> 
    (tyenv_wellformed (update_modes upd mds) \<Gamma>'' \<S>'' P'' \<and> pred P'' mem \<and> tyenv_sec (update_modes upd mds) \<Gamma>'' mem \<longrightarrow>
       tyenv_wellformed mds' \<Gamma>''' \<S>''' P''' \<and> pred P''' mem' \<and> tyenv_sec mds' \<Gamma>''' mem')"
    by blast

  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed (update_modes upd mds) \<Gamma>'' \<S>'' P''"
    using anno_type
    apply auto
    by (metis tyenv_wellformed_mode_update)
  moreover
  have pred: "pred P mem \<longrightarrow> pred P'' mem"
    using anno_type
    by (auto simp: pred_def restrict_preds_to_vars_def)
  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec (update_modes upd mds) \<Gamma>'' mem"
    apply(rule impI)
    apply(rule tyenv_sec_mode_update)
            using anno_type apply fastforce
           using anno_type pred apply fastforce
          using anno_type apply fastforce
         using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
        using anno_type apply fastforce
       apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
      apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
     using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
    by simp  
  ultimately show ?case
    by blast
next
  case stop_type
  with stop_no_eval show ?case ..
next
  case skip_type
  hence "c' = Stop \<and> mds' = mds \<and> mem' = mem"
    by (metis skip_elim)
  thus ?case
    by (metis stop_type)
next
  case (assign\<^sub>1 x \<Gamma> e t P P' \<S> c' mds)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  from assign\<^sub>1(2) upd have \<C>_eq: "\<forall>x\<in>\<C>. mem x = mem' x"
    by auto
  from upd have " \<turnstile> \<Gamma>,\<S>,P' {c'} \<Gamma>,\<S>,P'"
    by (metis stop_type)
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>1 by metis
  moreover have "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>1 upd by metis
    
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P  \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds \<Gamma> mem'"
    using tyenv_sec_eq[OF \<C>_eq, where \<Gamma>=\<Gamma>]
    unfolding tyenv_wellformed_def by blast
  ultimately show ?case
    by (metis upd)
next
  case (assign\<^sub>2 x \<Gamma> e t \<S> P' P c' mds)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  let ?\<Gamma>' = "\<Gamma> (x \<mapsto> t)"
  from upd have ty: " \<turnstile> ?\<Gamma>',\<S>,P' {c'} ?\<Gamma>',\<S>,P'"
    by (metis stop_type)
  have wf: "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
  proof
    assume tyenv_wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    hence wf: "types_wellformed \<Gamma>"
      unfolding tyenv_wellformed_def by blast
    hence  "type_wellformed t"
      using assign\<^sub>2(2) type_aexpr_type_wellformed
      by blast
    with wf have wf': "types_wellformed ?\<Gamma>'"
      using types_wellformed_update by metis
    from tyenv_wf have stable': "types_stable ?\<Gamma>' \<S>"
      using types_stable_update
            assign\<^sub>2(3)
      unfolding tyenv_wellformed_def by blast
    have m: "mds_consistent mds \<Gamma> \<S> P"
      using tyenv_wf unfolding tyenv_wellformed_def by blast
    from assign\<^sub>2(4) assign\<^sub>2(1)
    have "mds_consistent mds' (\<Gamma>(x \<mapsto> t)) \<S> P'"
      apply(rule mds_consistent_preds_tyenv_update)
      using upd m by simp
    from wf' stable' this show "tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
      unfolding tyenv_wellformed_def by blast
  qed
  have p: "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>2 upd by metis
  have sec: "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> pred P mem \<Longrightarrow> tyenv_sec mds \<Gamma> mem \<Longrightarrow> tyenv_sec mds' ?\<Gamma>' mem'"
  proof(clarify)
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem"
    assume sec: "tyenv_sec mds \<Gamma> mem"
    from pred p have pred': "pred P' mem'" by blast
    fix v t'
    assume \<Gamma>v: "(\<Gamma>(x \<mapsto> t)) v = Some t'"
    assume "v \<notin> mds' AsmNoReadOrWrite"
    show "type_max (the ((\<Gamma>(x \<mapsto> t)) v)) mem' \<le> dma mem' v"
    proof(cases "v = x")
      assume [simp]: "v = x"
      hence [simp]: "(the ((\<Gamma>(x \<mapsto> t)) v)) = t" and t_def: "t = t'"
        using \<Gamma>v by auto
      from \<open>v \<notin> mds' AsmNoReadOrWrite\<close> upd wf have readable: "v \<notin> snd \<S>"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      with assign\<^sub>2(5) have "t \<le>:\<^sub>P' (dma_type x)" by fastforce
      with pred' show ?thesis
        using type_max_dma_type subtype_correct
        by fastforce
    next
      assume neq: "v \<noteq> x"
      hence [simp]: "((\<Gamma>(x \<mapsto> t)) v) = \<Gamma> v"
        by simp
      with \<Gamma>v have \<Gamma>v: "\<Gamma> v = Some t'" by simp
      with sec upd \<open>v \<notin> mds' AsmNoReadOrWrite\<close> have f_leq: "type_max t' mem \<le> dma mem v"
        by auto
      have \<C>_eq: "\<forall>x\<in>\<C>. mem x = mem' x"
        using wf assign\<^sub>2(1) upd by(auto simp: tyenv_wellformed_def mds_consistent_def)
      hence dma_eq: "dma mem = dma mem'"
        by(rule dma_\<C>)
      have f_eq: "type_max t' mem = type_max t' mem'"
        apply(rule \<C>_eq_type_max_eq)
         using \<Gamma>v wf apply(force simp: tyenv_wellformed_def types_wellformed_def)
        by(rule \<C>_eq)     
      from neq \<Gamma>v f_leq dma_eq f_eq show ?thesis
        by simp
    qed
  qed
  from ty wf p sec show ?case
    by blast
next
  case (assign\<^sub>\<C> x \<Gamma> e t P P' \<S> c' mds)
  (* this case follows from the same argument as assign\<^sub>1 *)
  hence upd: "c' = Stop \<and> mds' = mds \<and> mem' = mem (x := ev\<^sub>A mem e)"
    by (metis assign_elim)
  hence " \<turnstile> \<Gamma>,\<S>,P' {c'} \<Gamma>,\<S>,P'"
    by (metis stop_type)
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>\<C> by metis
  moreover have "pred P mem \<longrightarrow> pred P' mem'"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<Longrightarrow> tyenv_sec mds' \<Gamma> mem'"
  proof(clarify)
    fix v t'
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem"
    hence pred': "pred P' mem'" using \<open>pred P mem \<longrightarrow> pred P' mem'\<close> by blast
    assume sec: "tyenv_sec mds \<Gamma> mem"
    assume \<Gamma>v: "\<Gamma> v = Some t'"
    assume readable': "v \<notin> mds' AsmNoReadOrWrite"
    with upd have readable: "v \<notin> mds AsmNoReadOrWrite" by simp
    with wf have "v \<notin> snd \<S>" by(auto simp: tyenv_wellformed_def mds_consistent_def)
    show "type_max (the (\<Gamma> v)) mem' \<le> dma mem' v"
    proof(cases "x \<in> \<C>_vars v")
      assume "x \<in> \<C>_vars v"
      with assign\<^sub>\<C>(6) \<open>v \<notin> snd \<S>\<close> have "(to_total \<Gamma> v) \<le>:\<^sub>P' (dma_type v)" by blast
      from pred' \<Gamma>v subtype_sound[OF this] show ?thesis
        using type_max_dma_type by(auto simp: to_total_def split: if_splits)
    next
      assume "x \<notin> \<C>_vars v"
      hence "\<forall>v'\<in>\<C>_vars v. mem v' = mem' v'"
        using upd by auto
      hence dma_eq: "dma mem v = dma mem' v"
        by(rule dma_\<C>_vars)
      from \<Gamma>v assign\<^sub>\<C>(4) have "x \<notin> vars_of_type t'" by force
      have "type_wellformed t'"
        using wf \<Gamma>v by(force simp: tyenv_wellformed_def types_wellformed_def)
      with \<open>x \<notin> vars_of_type t'\<close> upd have f_eq: "type_max t' mem = type_max t' mem'"
        using vars_of_type_eq_type_max_eq by fastforce
      from sec \<Gamma>v readable have "type_max t' mem \<le> dma mem v"
        by auto
      with f_eq dma_eq \<Gamma>v show ?thesis
        by simp
    qed
  qed
  ultimately show ?case
    by (metis stop_type)
next
  case (if_type \<Gamma> e t P \<S> th \<Gamma>' \<S>' P' el \<Gamma>'' P'' \<Gamma>''' P''' c' mds)
  from if_type(13)
  show ?case
  proof(rule if_elim)
    assume [simp]: "ev\<^sub>B mem e" and [simp]: "c' = th" and [simp]: "mem' = mem" and [simp]: "mds' = mds"
    from if_type(3) have " \<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> e {c'} \<Gamma>',\<S>',P'" by simp
    hence "\<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> e {c'} \<Gamma>''',\<S>',P'''"
      apply(rule sub)
           apply simp+
         using if_type apply blast
        using if_type apply blast
       apply simp
      using if_type apply(blast intro: pred_entailment_trans)
      done
    moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> (P +\<^sub>\<S> e)"
      by(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)
    moreover have "pred P mem \<longrightarrow> pred (P +\<^sub>\<S> e) mem'"
      by(auto simp: pred_def add_pred_def)
    moreover have "tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds' \<Gamma> mem'"
      by(simp)
    ultimately show ?case by blast
  next
    assume [simp]: "\<not> ev\<^sub>B mem e" and [simp]: "c' = el" and [simp]: "mem' = mem" and [simp]: "mds' = mds"
    from if_type(5) have " \<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> bexp_neg e {c'} \<Gamma>'',\<S>',P''" by simp
    hence "\<turnstile> \<Gamma>,\<S>,P +\<^sub>\<S> bexp_neg e {c'} \<Gamma>''',\<S>',P'''"
      apply(rule sub)
           apply simp+
         using if_type apply blast
        using if_type apply blast
       apply simp
      using if_type apply(blast intro: pred_entailment_trans)
      done
    moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> (P +\<^sub>\<S> bexp_neg e)"
      by(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)
    moreover have "pred P mem \<longrightarrow> pred (P +\<^sub>\<S> bexp_neg e) mem'"
      by(auto simp: pred_def add_pred_def bexp_neg_negates)
    moreover have "tyenv_sec mds \<Gamma> mem \<longrightarrow> tyenv_sec mds' \<Gamma> mem'"
      by(simp)
    ultimately show ?case by blast
  qed
next
  case (while_type \<Gamma> e t P \<S> c c' mds)
  hence [simp]: "mds' = mds \<and> c' = If e (c ;; While e c) Stop \<and> mem' = mem"
    by (metis while_elim)
  have " \<turnstile> \<Gamma>,\<S>,P {c'} \<Gamma>,\<S>,P"
    apply simp
    apply(rule if_type)
             apply(rule while_type(1))
            apply(rule while_type(2))
           apply(rule seq_type)
            apply(rule while_type(3))
           apply(rule has_type.while_type)
             apply(rule while_type(1))
            apply(rule while_type(2))
           apply(rule while_type(3))
          apply(rule stop_type)
         apply simp
        apply simp
       apply simp
      apply(rule add_pred_entailment)
      apply simp+
    by(blast intro!: tyenv_wellformed_subset add_pred_subset)
  thus ?case
    by fastforce
next
  case (seq_type \<Gamma> \<S> P c\<^sub>1 \<Gamma>\<^sub>1 \<S>\<^sub>1 P\<^sub>1 c\<^sub>2 \<Gamma>\<^sub>2 \<S>\<^sub>2 P\<^sub>2 c' mds)
  thus ?case
  proof (cases "c\<^sub>1 = Stop")
    assume [simp]: "c\<^sub>1 = Stop"
    with seq_type have [simp]: "mds' = mds" and [simp]: "c' = c\<^sub>2" and [simp]: "mem' = mem"
      by (metis seq_stop_elim)+
    have context_eq: "context_equiv \<Gamma> P \<Gamma>\<^sub>1" and [simp]: "\<S>\<^sub>1 = \<S>" and entail: "P \<turnstile> P\<^sub>1" and
             wf_imp: "\<forall>mds. tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1"
      using stop_cxt seq_type(1) by simp+
    have "\<turnstile> \<Gamma>,\<S>,P {c\<^sub>2} \<Gamma>\<^sub>2,\<S>\<^sub>2,P\<^sub>2"
      apply(rule sub)
            using seq_type(3) apply simp
           apply(rule context_eq)
          apply(rule wf_imp)
         apply simp+
       apply(rule entail)
      apply(rule pred_entailment_refl)
      done
    thus ?case
      by fastforce
  next
    assume "c\<^sub>1 \<noteq> Stop"
    then obtain c\<^sub>1' where "\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = (c\<^sub>1' ;; c\<^sub>2)"
      by (metis seq_elim seq_type.prems)
    then obtain \<Gamma>''' \<S>''' P''' where "\<turnstile> \<Gamma>''',\<S>''',P''' {c\<^sub>1'} \<Gamma>\<^sub>1,\<S>\<^sub>1,P\<^sub>1 \<and>
      (tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem \<and> tyenv_sec mds \<Gamma> mem \<longrightarrow> 
       tyenv_wellformed mds' \<Gamma>''' \<S>''' P''' \<and> pred P''' mem' \<and> tyenv_sec mds' \<Gamma>''' mem')"
      using seq_type(2)
      by force
    moreover
    from seq_type have "\<turnstile> \<Gamma>\<^sub>1,\<S>\<^sub>1,P\<^sub>1 {c\<^sub>2} \<Gamma>\<^sub>2,\<S>\<^sub>2,P\<^sub>2" by auto
    moreover
    ultimately show ?case
      apply (rule_tac x = \<Gamma>''' in exI)
      using \<open>\<langle>c\<^sub>1, mds, mem\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem'\<rangle> \<and> c' = c\<^sub>1' ;; c\<^sub>2\<close> by blast
  qed
next
  case (sub \<Gamma>\<^sub>1 \<S> P\<^sub>1 c \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>2' P\<^sub>2' c' mds)
  then obtain \<Gamma>'' \<S>'' P'' where stuff: "\<turnstile> \<Gamma>'',\<S>'',P'' { c' } \<Gamma>\<^sub>1',\<S>',P\<^sub>1' \<and>
    (tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem \<longrightarrow> 
     tyenv_wellformed mds' \<Gamma>'' \<S>'' P'' \<and> pred P'' mem' \<and> tyenv_sec mds' \<Gamma>'' mem')"
    by force

  have imp: "tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<and> pred P\<^sub>2 mem \<and> tyenv_sec mds \<Gamma>\<^sub>2 mem \<Longrightarrow> 
             tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem"
    apply(rule conjI)
     using sub(5) sub(4) tyenv_wellformed_sub unfolding pred_def
     apply blast
    apply(rule conjI) 
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    using sub(3) context_equiv_tyenv_sec unfolding pred_def by blast
  show ?case
    apply (rule_tac x = \<Gamma>'' in exI, rule_tac x = "\<S>''" in exI, rule_tac x="P''" in exI)  
    apply (rule conjI)
     apply(rule has_type.sub)
           apply(rule stuff[THEN conjunct1])
          apply simp+
        apply(rule sub(5))
       apply(rule sub(6))
      apply simp
     using sub apply blast
    using imp stuff apply blast
   done
next
  case (await_type \<Gamma> e t P \<S> c \<Gamma>' \<S>' P' c' mds)
  from this show ?case
    apply simp
    apply (drule await_elim, clarsimp)
    apply (drule preservation_no_await_plus[of c mds mem c' mds' mem' \<Gamma> \<S> "P +\<^sub>\<S> e" \<Gamma>' \<S>' P'], assumption+)
    apply (subgoal_tac "\<lbrakk> tyenv_wellformed mds \<Gamma> \<S> P \<rbrakk> \<Longrightarrow> tyenv_wellformed mds \<Gamma> \<S> P +\<^sub>\<S> e") defer
      apply (unfold add_pred_def)[1]
      apply (case_tac "pred_stable \<S> e", clarsimp)
        apply (unfold tyenv_wellformed_def, clarsimp)[1]
        apply (unfold mds_consistent_def, clarsimp)[1]
      apply clarsimp
    apply (subgoal_tac "pred P mem \<Longrightarrow> pred P +\<^sub>\<S> e mem") defer
      apply (unfold add_pred_def)[1]
      apply (case_tac "pred_stable \<S> e", clarsimp)
        apply (unfold pred_def, clarsimp)[1]
      apply clarsimp
    apply clarsimp
    using has_type.sub by (metis context_equiv_refl pred_entailment_refl)
qed

inductive_cases await_type_elim: "\<turnstile> \<Gamma>,\<S>,P {Await b ca} \<Gamma>',\<S>',P'"


fun bisim_helper :: "(('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow>
  (('Var, 'AExp, 'BExp) Stmt, 'Var, 'Val) LocalConf \<Rightarrow> bool"
  where
  "bisim_helper \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds\<^sub>2, mem\<^sub>2\<rangle> = mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"

lemma \<R>\<^sub>3_mem_eq: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  apply (subgoal_tac "bisim_helper \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>")
   apply simp
  apply (induct rule: \<R>\<^sub>3_aux.induct)
  by (auto simp: \<R>\<^sub>1_mem_eq)


lemma ev\<^sub>A_eq:
  assumes tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2"
  assumes pred: "pred P mem\<^sub>1" 
  assumes e_type: "\<Gamma> \<turnstile>\<^sub>a e \<in> t"
  assumes subtype: "t \<le>:\<^sub>P (dma_type v)"
  assumes is_Low: "dma mem\<^sub>1 v = Low"
  shows "ev\<^sub>A mem\<^sub>1 e = ev\<^sub>A mem\<^sub>2 e"
proof(rule eval_vars_det\<^sub>A, clarify)
  fix x
  assume in_vars: "x \<in> aexp_vars e"
  have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
  proof -
    from subtype_sound[OF subtype] pred have "type_max t mem\<^sub>1 \<le> dma mem\<^sub>1 v"
      by(auto)
    with is_Low have "type_max t mem\<^sub>1 = Low" by(auto simp: less_eq_Sec_def)
    with e_type in_vars show ?thesis
      apply -
      apply(erule type_aexpr.cases)
      using Sec.exhaust by(auto simp: type_max_def split: if_splits)
  qed
  thus "mem\<^sub>1 x = mem\<^sub>2 x"
    using tyenv_eq unfolding tyenv_eq_def by blast
qed

lemma ev\<^sub>A_eq':
  assumes tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2"
  assumes pred: "pred P mem\<^sub>1" 
  assumes e_type: "\<Gamma> \<turnstile>\<^sub>a e \<in> t"
  assumes subtype: "P \<turnstile> t"
  shows "ev\<^sub>A mem\<^sub>1 e = ev\<^sub>A mem\<^sub>2 e"
proof(rule eval_vars_det\<^sub>A, clarify)
  fix x
  assume in_vars: "x \<in> aexp_vars e"
  have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
  proof -
    from subtype pred have "type_max t mem\<^sub>1 \<le> Low"
      by(auto simp: type_max_def pred_entailment_def pred_def)
    hence "type_max t mem\<^sub>1 = Low" by(auto simp: less_eq_Sec_def)
    with e_type in_vars show ?thesis
      apply -
      apply(erule type_aexpr.cases)
      using Sec.exhaust by(auto simp: type_max_def  split: if_splits)
  qed
  thus "mem\<^sub>1 x = mem\<^sub>2 x"
    using tyenv_eq unfolding tyenv_eq_def by blast
qed

lemma ev\<^sub>B_eq':
  assumes tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2"
  assumes pred: "pred P mem\<^sub>1" 
  assumes e_type: "\<Gamma> \<turnstile>\<^sub>b e \<in> t"
  assumes subtype: "P \<turnstile> t"
  shows "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
proof(rule eval_vars_det\<^sub>B, clarify)
  fix x
  assume in_vars: "x \<in> bexp_vars e"
  have "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
  proof -
    from subtype pred have "type_max t mem\<^sub>1 \<le> Low"
      by(auto simp: type_max_def pred_entailment_def pred_def)
    hence "type_max t mem\<^sub>1 = Low" by(auto simp: less_eq_Sec_def)
    with e_type in_vars show ?thesis
      apply -
      apply(erule type_bexpr.cases)
      using Sec.exhaust by(auto simp: type_max_def  split: if_splits)
  qed
  thus "mem\<^sub>1 x = mem\<^sub>2 x"
    using tyenv_eq unfolding tyenv_eq_def by blast
qed

lemma R1_equiv_entailment:
  "\<langle>c, mds, mem\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c', mds', mem'\<rangle> \<Longrightarrow>  
  context_equiv \<Gamma>' P' \<Gamma>'' \<Longrightarrow> P' \<turnstile> P'' \<Longrightarrow>
  \<forall>mds. tyenv_wellformed mds \<Gamma>' \<S>' P' \<longrightarrow> tyenv_wellformed mds \<Gamma>'' \<S>' P'' \<Longrightarrow>
   \<langle>c, mds, mem\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>'',\<S>',P''\<^esub> \<langle>c', mds', mem'\<rangle>"
  apply(induct rule: \<R>\<^sub>1.induct)
  apply(rule \<R>\<^sub>1.intro)
       apply(blast intro: sub context_equiv_refl pred_entailment_refl)+
  done

lemma R3_equiv_entailment:
  "\<langle>c, mds, mem\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c', mds', mem'\<rangle> \<Longrightarrow> 
    context_equiv \<Gamma>' P' \<Gamma>'' \<Longrightarrow> P' \<turnstile> P'' \<Longrightarrow> 
  \<forall>mds. tyenv_wellformed mds \<Gamma>' \<S>' P' \<longrightarrow> tyenv_wellformed mds \<Gamma>'' \<S>' P'' \<Longrightarrow>
  \<langle>c, mds, mem\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>'',\<S>',P''\<^esub> \<langle>c', mds', mem'\<rangle>"
  apply(induct rule: \<R>\<^sub>3_aux.induct)
   apply(erule \<R>\<^sub>3_aux.intro\<^sub>1)
   apply(blast intro: sub context_equiv_refl tyenv_wellformed_subset subset_entailment)
  apply(erule \<R>\<^sub>3_aux.intro\<^sub>3)
  apply(blast intro: sub context_equiv_refl tyenv_wellformed_subset subset_entailment)
  done

lemma R_equiv_entailment:
  "lc\<^sub>1 \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> lc\<^sub>2 \<Longrightarrow> 
    context_equiv \<Gamma>' P' \<Gamma>'' \<Longrightarrow> P' \<turnstile> P'' \<Longrightarrow> 
  \<forall>mds. tyenv_wellformed mds \<Gamma>' \<S>' P' \<longrightarrow> tyenv_wellformed mds \<Gamma>'' \<S>' P'' \<Longrightarrow>
  lc\<^sub>1 \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>',P''\<^esub> lc\<^sub>2"
  apply(induct rule: \<R>.induct)
   apply clarsimp
   apply(rule \<R>.intro\<^sub>1)
   apply(fastforce intro: R1_equiv_entailment)
  apply(rule \<R>.intro\<^sub>3)
  apply(fastforce intro: R3_equiv_entailment)
  done

lemma context_equiv_tyenv_eq:
  "tyenv_eq \<Gamma> mem mem' \<Longrightarrow> context_equiv \<Gamma> P \<Gamma>' \<Longrightarrow> pred P mem \<Longrightarrow> tyenv_eq \<Gamma>' mem mem'"
  apply(clarsimp simp: tyenv_eq_def to_total_def context_equiv_def split: if_splits simp: type_equiv_def)
  using subtype_trans subtype_sound
  by (metis domI less_eq_Sec_def option.sel)


lemma \<R>_typed_step_no_await:
"\<lbrakk> \<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 } \<Gamma>',\<S>',P' ;
  tyenv_wellformed mds \<Gamma> \<S> P; mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2; pred P mem\<^sub>1;
        pred P mem\<^sub>2; tyenv_sec mds \<Gamma> mem\<^sub>1;
     \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>; no_await c\<^sub>1 \<rbrakk> \<Longrightarrow>
   (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                 \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
proof (induct arbitrary: mds c\<^sub>1' rule: has_type.induct)
  case (seq_type \<Gamma> \<S> P c\<^sub>1 \<Gamma>'' \<S>'' P'' c\<^sub>2 \<Gamma>' \<S>' P' mds)
  show ?case
  proof (cases "c\<^sub>1 = Stop")
    assume "c\<^sub>1 = Stop"
    hence [simp]: "c\<^sub>1' = c\<^sub>2" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1"
      using seq_type
      by (auto simp: seq_stop_elim)
    from seq_type \<open>c\<^sub>1 = Stop\<close> have "context_equiv \<Gamma> P \<Gamma>''" and "\<S> = \<S>''" and "P \<turnstile> P''" and
                                   "(\<forall>mds. tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed  mds \<Gamma>'' \<S> P'')"
      by (metis stop_cxt)+
    hence "\<turnstile> \<Gamma>,\<S>,P { c\<^sub>2 } \<Gamma>',\<S>',P'"
      apply -
      apply(rule sub)
          using seq_type(3) apply simp
         by auto
    have "\<langle>c\<^sub>2, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
      apply (rule \<R>\<^sub>1.intro [of \<Gamma>])
           apply(rule \<open>\<turnstile> \<Gamma>,\<S>,P { c\<^sub>2 } \<Gamma>',\<S>',P'\<close>)
          using seq_type by auto
    thus ?case
      using \<R>.intro\<^sub>1
      apply clarify
      apply (rule_tac x = c\<^sub>2 in exI)
      apply (rule_tac x = mem\<^sub>2 in exI)
      by (auto simp: \<open>c\<^sub>1 = Stop\<close> seq_stop_eval\<^sub>w  \<R>.intro\<^sub>1)
  next
    assume "c\<^sub>1 \<noteq> Stop"
    with \<open>\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>\<close> obtain c\<^sub>1'' where c\<^sub>1''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = c\<^sub>1'' ;; c\<^sub>2"
      by (metis seq_elim)
    with \<open>no_await (c\<^sub>1 ;; c\<^sub>2)\<close> have "no_await c\<^sub>1" using no_await.cases by blast
    with seq_type(2) \<open>no_await c\<^sub>1\<close> obtain c\<^sub>2'' mem\<^sub>2' where c\<^sub>2''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
      using seq_type.prems(1) seq_type.prems(2) seq_type.prems(3) seq_type.prems(4) seq_type.prems(5) c\<^sub>1''_props
      by blast
    hence "\<langle>c\<^sub>1'' ;; c\<^sub>2, mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      apply (rule conjE)
      apply (erule \<R>_elim, auto)
       apply (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>1 seq_type(3))
      by (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>3 seq_type(3))
    moreover
    from c\<^sub>2''_props have "\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      by (metis eval\<^sub>w.seq)
    ultimately show ?case
      by (metis c\<^sub>1''_props)
  qed
next
  case (anno_type \<Gamma>' \<Gamma> \<S> upd \<S>' P' P c \<Gamma>'' \<S>'' P'' mds)
  have "mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2"
  proof(clarsimp simp: tyenv_eq_def)
    fix x  
    assume a: "type_max (to_total \<Gamma>' x) mem\<^sub>1 = Low"
    hence "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
    proof -
      from \<open>pred P mem\<^sub>1\<close> have "pred P' mem\<^sub>1"
        using anno_type.hyps(3)
        by(auto simp: restrict_preds_to_vars_def pred_def)
      with subtype_correct anno_type.hyps(7) a 
      show ?thesis
        using less_eq_Sec_def by metis
    qed
    thus " mem\<^sub>1 x = mem\<^sub>2 x"
      using anno_type.prems(2)
      unfolding tyenv_eq_def by blast
  qed
  
  have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed (update_modes upd mds) \<Gamma>' \<S>' P'"
    using anno_type
    apply auto
    by (metis tyenv_wellformed_mode_update)
  moreover
  have pred: "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1"
    using anno_type
    by (auto simp: pred_def restrict_preds_to_vars_def)
  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem\<^sub>1 \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<longrightarrow> 
        tyenv_sec (update_modes upd mds) \<Gamma>' mem\<^sub>1"
    apply(rule impI)
    apply(rule tyenv_sec_mode_update)
            using anno_type apply fastforce
           using anno_type pred apply fastforce
          using anno_type apply fastforce
         using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
        using anno_type apply fastforce
       apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
      apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
     using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
    by simp
  from \<open>no_await (c@[upd])\<close> have "no_await c" using no_await.cases by blast
  ultimately obtain c\<^sub>2' mem\<^sub>2' where "(\<langle>c, update_modes upd mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
    \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
    using anno_type
    apply auto    
    using \<open>mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2\<close> local.pred_def restrict_preds_to_vars_def upd_elim \<open>no_await c\<close>
      (* TODO: cleanup *)
      using \<open>tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem\<^sub>1 \<and> (\<forall>x\<in>dom \<Gamma>. x \<notin> mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma> x)) mem\<^sub>1 \<le> dma mem\<^sub>1 x) \<longrightarrow> (\<forall>x\<in>dom \<Gamma>'. x \<notin> update_modes upd mds AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma>' x)) mem\<^sub>1 \<le> dma mem\<^sub>1 x)\<close> mem_Collect_eq by fastforce try0
  thus ?case
    apply (rule_tac x = c\<^sub>2' in exI)
    apply (rule_tac x = mem\<^sub>2' in exI)
    apply auto
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.decl)
next
  case stop_type
  with stop_no_eval show ?case by auto
next
  case (skip_type \<Gamma> \<S> P mds)
  moreover
  with skip_type have [simp]: "mds' = mds" "c\<^sub>1' = Stop" "mem\<^sub>1' = mem\<^sub>1"
    using skip_elim
    by (metis, metis, metis)
  with skip_type have "\<langle>Stop, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>Stop, mds, mem\<^sub>2\<rangle>"
    by auto
  thus ?case
    using \<R>.intro\<^sub>1 and unannotated [where c = Skip and E = "[]"]
    apply auto
    by (metis (mono_tags, lifting) \<R>.intro\<^sub>1 old.prod.case skip_eval\<^sub>w)
next (* assign\<^sub>1 *)
  case (assign\<^sub>1 x \<Gamma> e t P P' \<S> mds)
  hence upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim
    by (auto, metis)
  from assign\<^sub>1(2) upd have \<C>_eq: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>1' x"
    by auto
  have dma_eq [simp]: "dma mem\<^sub>1 = dma mem\<^sub>1'"
    using dma_\<C> assign\<^sub>1(2) by simp
  have "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total \<Gamma> v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v \<in> dom \<Gamma>")
      assume [simp]: "v \<in> dom \<Gamma>"
      then obtain t' where [simp]: "\<Gamma> v = Some t'" by force
      hence [simp]: "(to_total \<Gamma> v) = t'"
        unfolding to_total_def by (auto split: if_splits)
      have "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        apply(rule \<C>_eq_type_max_eq)
         using \<open>\<Gamma> v = Some t'\<close> assign\<^sub>1(6) 
         unfolding tyenv_wellformed_def types_wellformed_def
         apply (metis \<open>v \<in> dom \<Gamma>\<close> option.sel)
                
        using assign\<^sub>1(2) apply simp
        done
      with is_Low' have is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
        by simp
      from assign\<^sub>1(1) \<open>v \<in> dom \<Gamma>\<close> have "x \<noteq> v" by auto
      thus ?thesis
        apply simp
        using is_Low assign\<^sub>1(7) unfolding tyenv_eq_def by auto
    next
      assume "v \<notin> dom \<Gamma>"
      hence [simp]: "\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v"
        unfolding to_total_def by simp
      with is_Low' have "dma mem\<^sub>1' v = Low" by simp
      with dma_eq have dma_v_Low: "dma mem\<^sub>1 v = Low" by simp
      hence is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low" by simp
      show ?thesis
      proof(cases "x = v")
        assume "x \<noteq> v"
        thus ?thesis
          apply simp
          using is_Low assign\<^sub>1(7) unfolding tyenv_eq_def by blast
      next
        assume "x = v"
        thus ?thesis
          apply simp
          apply(rule ev\<^sub>A_eq)
              apply(rule assign\<^sub>1(7))
             apply(rule assign\<^sub>1(8))
            apply(rule assign\<^sub>1(3))
           apply(rule assign\<^sub>1(4))
          using dma_v_Low by simp
      qed
    qed
  qed

  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>1 by metis
  moreover have "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>1 upd by metis

  moreover have "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>1 upd by metis
    
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P  \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<longrightarrow> tyenv_sec mds \<Gamma> mem\<^sub>1'"
    using tyenv_sec_eq[OF \<C>_eq, where \<Gamma>=\<Gamma>]
    unfolding tyenv_wellformed_def by blast

  ultimately have \<R>':
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply -
    apply (rule \<R>.intro\<^sub>1, auto simp: assign\<^sub>1 simp del: dma_eq)
    done

  have a: "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
  by (auto, metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.assign)

  from \<R>' a show ?case
    using \<open>c\<^sub>1' = Stop\<close> and \<open>mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* assign\<^sub>\<C> *)
  case (assign\<^sub>\<C> x \<Gamma> e t P P' \<S> mds)
  hence upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim
    by (auto, metis)
  have "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total \<Gamma> v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v \<in> dom \<Gamma>")
      assume in_dom [simp]: "v \<in> dom \<Gamma>"
      then obtain t' where \<Gamma>v [simp]: "\<Gamma> v = Some t'" by force
      hence [simp]: "(to_total \<Gamma> v) = t'"
        unfolding to_total_def by (auto split: if_splits)
      from assign\<^sub>\<C>(4) have x_nin_C: "x \<notin> vars_of_type t'"
        using in_dom \<Gamma>v 
        by (metis option.sel snd_conv)
      have \<Gamma>v_wf: "type_wellformed t'"
        using in_dom \<Gamma>v assign\<^sub>\<C>(7) unfolding tyenv_wellformed_def types_wellformed_def
        by (metis option.sel)
        
      with x_nin_C have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        using vars_of_type_eq_type_max_eq by simp
      with is_Low' have is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
        by simp  
      from assign\<^sub>\<C>(1) \<open>v \<in> dom \<Gamma>\<close> assign\<^sub>\<C>(7) have "x \<noteq> v"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      thus ?thesis
        apply simp
        using is_Low assign\<^sub>\<C>(8) unfolding tyenv_eq_def by auto
    next
      assume nin_dom: "v \<notin> dom \<Gamma>"
      hence [simp]: "\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v"
        unfolding to_total_def  by simp
      with is_Low' have "dma mem\<^sub>1' v = Low" by simp
      show ?thesis
      proof(cases "x = v")
        assume "x = v"
        thus ?thesis
          apply simp
          apply(rule ev\<^sub>A_eq')
             apply(rule assign\<^sub>\<C>(8))
            apply(rule assign\<^sub>\<C>(9))
           apply(rule assign\<^sub>\<C>(2))
          by(rule assign\<^sub>\<C>(3))
      next
        assume [simp]: "x \<noteq> v"
        show ?thesis
        proof(cases "x \<in> \<C>_vars v")
          assume in_\<C>_vars: "x \<in> \<C>_vars v"
          hence "v \<notin> \<C>"
            using \<C>_vars_\<C> by auto
          with nin_dom have "v \<notin> snd \<S>"
            using assign\<^sub>\<C>(7)
            by(auto simp: tyenv_wellformed_def mds_consistent_def stable_def)
          with in_\<C>_vars have "P \<turnstile> (to_total \<Gamma> v)"
            using assign\<^sub>\<C>(6) by blast
          with assign\<^sub>\<C>(9) have "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
            by(auto simp: type_max_def pred_def pred_entailment_def)
          thus ?thesis
            using not_sym[OF \<open>x \<noteq> v\<close>]
            apply simp
            using assign\<^sub>\<C>(8)
            unfolding tyenv_eq_def by auto
        next
          assume "x \<notin> \<C>_vars v"
          with is_Low' have "dma mem\<^sub>1 v = Low"
            using dma_\<C>_vars \<open>\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v\<close>
            by (metis fun_upd_other)
          thus ?thesis
            using not_sym[OF \<open>x \<noteq> v\<close>]
            apply simp
            using assign\<^sub>\<C>(8)
            unfolding tyenv_eq_def by auto            
        qed
      qed
    qed
  qed

  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>\<C> by metis
  moreover have "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem\<^sub>1 \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<Longrightarrow> tyenv_sec mds' \<Gamma> mem\<^sub>1'"
  proof(clarify)
    fix v t'
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem\<^sub>1"
    hence pred': "pred P' mem\<^sub>1'" using \<open>pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'\<close> by blast
    assume sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
    assume \<Gamma>v: "\<Gamma> v = Some t'"
    assume readable': "v \<notin> mds' AsmNoReadOrWrite"
    with upd have readable: "v \<notin> mds AsmNoReadOrWrite" by simp
    with wf have "v \<notin> snd \<S>" by(auto simp: tyenv_wellformed_def mds_consistent_def)
    show "type_max (the (\<Gamma> v)) mem\<^sub>1' \<le> dma mem\<^sub>1' v"
    proof(cases "x \<in> \<C>_vars v")
      assume "x \<in> \<C>_vars v"
      with assign\<^sub>\<C>(6) \<open>v \<notin> snd \<S>\<close> have "(to_total \<Gamma> v) \<le>:\<^sub>P' (dma_type v)" by blast
      from pred' \<Gamma>v subtype_correct this show ?thesis
        using type_max_dma_type by(auto simp: to_total_def split: if_splits)
    next
      assume "x \<notin> \<C>_vars v"
      hence "\<forall>v'\<in>\<C>_vars v. mem\<^sub>1 v' = mem\<^sub>1' v'"
        using upd by auto
      hence dma_eq: "dma mem\<^sub>1 v = dma mem\<^sub>1' v"
        by(rule dma_\<C>_vars)
      from \<Gamma>v assign\<^sub>\<C>(4) have "x \<notin> vars_of_type t'" by force
      have "type_wellformed t'"
        using wf \<Gamma>v by(force simp: tyenv_wellformed_def types_wellformed_def)
      with \<open>x \<notin> vars_of_type t'\<close> upd have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        using vars_of_type_eq_type_max_eq by fastforce
      from sec \<Gamma>v readable have "type_max t' mem\<^sub>1 \<le> dma mem\<^sub>1 v"
        by auto
      with f_eq dma_eq \<Gamma>v show ?thesis
        by simp
    qed
  qed

  ultimately have \<R>':
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply -
    apply (rule \<R>.intro\<^sub>1, auto simp: assign\<^sub>\<C>)
    done

  have a: "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
  by (auto, metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.assign)

  from \<R>' a show ?case
    using \<open>c\<^sub>1' = Stop\<close> and \<open>mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* assign\<^sub>2 *)
  case (assign\<^sub>2 x \<Gamma> e t \<S> P' P mds)
  have upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim[OF assign\<^sub>2(11)]
    by auto
  from \<open>x \<in> dom \<Gamma>\<close> \<open>tyenv_wellformed mds \<Gamma> \<S> P\<close>
  have x_nin_\<C>: "x \<notin> \<C>"
    by(auto simp: tyenv_wellformed_def mds_consistent_def)
  hence dma_eq [simp]: "dma mem\<^sub>1' = dma mem\<^sub>1"
    using dma_\<C> assign\<^sub>2
    by auto
    
  let ?\<Gamma>' = "\<Gamma> (x \<mapsto> t)"
  have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using assign\<^sub>2
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.assign eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
    
  moreover
  have tyenv_eq': "mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>(x \<mapsto> t)\<^esub> mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total (\<Gamma>(x \<mapsto> t)) v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v = x")
      assume neq: "v \<noteq> x"
      hence "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
      proof(cases "v \<in> dom \<Gamma>")
        assume "v \<in> dom \<Gamma>"
        then obtain t' where [simp]: "\<Gamma> v = Some t'" by force
        hence [simp]: "(to_total \<Gamma> v) = t'"
          unfolding to_total_def by (auto split: if_splits)
        hence [simp]: "(to_total ?\<Gamma>' v) = t'"
          using neq by(auto simp: to_total_def)
        have "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
          apply(rule \<C>_eq_type_max_eq)
            using assign\<^sub>2(6) 
            apply(clarsimp simp: tyenv_wellformed_def types_wellformed_def)
            using \<open>v \<in> dom \<Gamma>\<close> \<open>\<Gamma> v = Some t'\<close> apply(metis option.sel)
           using x_nin_\<C> by simp
        from this is_Low' neq neq[THEN not_sym] show "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
          by auto
      next
        assume "v \<notin> dom \<Gamma>"
        with is_Low' neq
        have "dma mem\<^sub>1' v = Low"
          by(auto simp: to_total_def  split: if_splits)
        with dma_eq \<open>v \<notin> dom \<Gamma>\<close> show ?thesis
          by(auto simp: to_total_def  split: if_splits)
      qed
      with neq assign\<^sub>2(7) show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
        by(auto simp: tyenv_eq_def)
    next
      assume eq[simp]: "v = x"
      with is_Low' \<open>x \<in> dom \<Gamma>\<close> have t_Low': "type_max t mem\<^sub>1' = Low"
        by(auto simp: to_total_def split: if_splits)
      have wf_t: "type_wellformed t"
        using type_aexpr_type_wellformed assign\<^sub>2(2) assign\<^sub>2(6)
        by(fastforce simp: tyenv_wellformed_def)
      with t_Low' \<open>x \<notin> \<C>\<close> have t_Low: "type_max t mem\<^sub>1 = Low"
        using \<C>_eq_type_max_eq
        by (metis (no_types, lifting) fun_upd_other upd(3))
      show ?thesis
      proof(simp, rule eval_vars_det\<^sub>A, clarify)
        fix y
        assume in_vars: "y \<in> aexp_vars e"
        have "type_max (to_total \<Gamma> y) mem\<^sub>1 = Low"
        proof -
          from t_Low in_vars assign\<^sub>2(2) show ?thesis
            apply -
            apply(erule type_aexpr.cases)
            using Sec.exhaust by(auto simp: type_max_def  split: if_splits)
        qed
        thus "mem\<^sub>1 y = mem\<^sub>2 y"
          using assign\<^sub>2 unfolding tyenv_eq_def by blast
      qed
    qed
  qed

  from upd have ty: " \<turnstile> ?\<Gamma>',\<S>,P' {c\<^sub>1'} ?\<Gamma>',\<S>,P'"
    by (metis stop_type)
  have wf: "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
  proof
    assume tyenv_wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    hence wf: "types_wellformed \<Gamma>"
      unfolding tyenv_wellformed_def by blast
    hence  "type_wellformed t"
      using assign\<^sub>2(2) type_aexpr_type_wellformed
      by blast
    with wf have wf': "types_wellformed ?\<Gamma>'"
      using types_wellformed_update by metis
    from tyenv_wf have stable': "types_stable ?\<Gamma>' \<S>"
      using types_stable_update
            assign\<^sub>2(3)
      unfolding tyenv_wellformed_def by blast
    have m: "mds_consistent mds \<Gamma> \<S> P"
      using tyenv_wf unfolding tyenv_wellformed_def by blast
    from assign\<^sub>2(4) assign\<^sub>2(1)
    have "mds_consistent mds' (\<Gamma>(x \<mapsto> t)) \<S> P'"
      apply(rule mds_consistent_preds_tyenv_update)
      using upd m by simp
    from wf' stable' this show "tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
      unfolding tyenv_wellformed_def by blast
  qed
  have p: "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>2 upd by metis
  have p\<^sub>2: "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>2 upd by metis
  have sec: "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> pred P mem\<^sub>1 \<Longrightarrow> tyenv_sec mds \<Gamma> mem\<^sub>1 \<Longrightarrow> tyenv_sec mds' ?\<Gamma>' mem\<^sub>1'"
  proof(clarify)
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem\<^sub>1"
    assume sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
    from pred p have pred': "pred P' mem\<^sub>1'" by blast
    fix v t'
    assume \<Gamma>v: "(\<Gamma>(x \<mapsto> t)) v = Some t'"
    assume "v \<notin> mds' AsmNoReadOrWrite"
    show "type_max (the ((\<Gamma>(x \<mapsto> t)) v)) mem\<^sub>1' \<le> dma mem\<^sub>1' v"
    proof(cases "v = x")
      assume [simp]: "v = x"
      hence [simp]: "(the ((\<Gamma>(x \<mapsto> t)) v)) = t" and t_def: "t = t'"
        using \<Gamma>v by auto
      from \<open>v \<notin> mds' AsmNoReadOrWrite\<close> upd wf have readable: "v \<notin> snd \<S>"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      with assign\<^sub>2(5) have "t \<le>:\<^sub>P' (dma_type x)" by fastforce
      with pred' show ?thesis
        using type_max_dma_type subtype_correct
        by fastforce
    next
      assume neq: "v \<noteq> x"
      hence [simp]: "((\<Gamma>(x \<mapsto> t)) v) = \<Gamma> v"
        by simp
      with \<Gamma>v have \<Gamma>v: "\<Gamma> v = Some t'" by simp
      with sec upd \<open>v \<notin> mds' AsmNoReadOrWrite\<close> have f_leq: "type_max t' mem\<^sub>1 \<le> dma mem\<^sub>1 v"
        by auto
      have \<C>_eq: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>1' x"
        using wf assign\<^sub>2(1) upd by(auto simp: tyenv_wellformed_def mds_consistent_def)
      hence dma_eq: "dma mem\<^sub>1 = dma mem\<^sub>1'"
        by(rule dma_\<C>)
      have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        apply(rule \<C>_eq_type_max_eq)
         using \<Gamma>v wf apply(force simp: tyenv_wellformed_def types_wellformed_def)
        by(rule \<C>_eq)     
      from neq \<Gamma>v f_leq dma_eq f_eq show ?thesis
        by simp
    qed
  qed

  have "\<langle>Stop, mds, mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>1\<^bsub>?\<Gamma>',\<S>,P'\<^esub> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply(rule \<R>\<^sub>1.intro)
         apply blast
        using wf assign\<^sub>2 apply fastforce
       apply(rule tyenv_eq')
      using p assign\<^sub>2 apply fastforce
     using p\<^sub>2 assign\<^sub>2 apply fastforce
    using sec assign\<^sub>2
    using upd(2) upd(3) by blast
    
  ultimately have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>(x \<mapsto> t),\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using \<R>.intro\<^sub>1
    by auto
  thus ?case
    using \<open>mds' = mds\<close> \<open>c\<^sub>1' = Stop\<close> \<open>mem\<^sub>1' = mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* if *)
  case (if_type \<Gamma> e t P \<S> th \<Gamma>' \<S>' P' el \<Gamma>'' P'' \<Gamma>''' P''')
  let ?P = "if (ev\<^sub>B mem\<^sub>1 e) then P +\<^sub>\<S> e else P +\<^sub>\<S> (bexp_neg e)"
  from \<open>\<langle>Stmt.If e th el, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>\<close> have ty: "\<turnstile> \<Gamma>,\<S>,?P {c\<^sub>1'} \<Gamma>''',\<S>',P'''"
  proof (rule if_elim)
    assume "c\<^sub>1' = th" "mem\<^sub>1' = mem\<^sub>1" "mds' = mds" "ev\<^sub>B mem\<^sub>1 e"
    with if_type(3)
    show ?thesis
      apply simp
      apply(erule sub)
         using if_type apply simp+
      done
  next
    assume "c\<^sub>1' = el" "mem\<^sub>1' = mem\<^sub>1" "mds' = mds" "\<not> ev\<^sub>B mem\<^sub>1 e"
    with if_type(5)
    show ?thesis
      apply simp
      apply(erule sub)
         using if_type apply simp+
      done
  qed
  have ev\<^sub>B_eq [simp]: "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
    apply(rule ev\<^sub>B_eq')
       apply(rule \<open>mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2\<close>)
      apply(rule \<open>pred P mem\<^sub>1\<close>)
     apply(rule \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close>)
    by(rule \<open> P \<turnstile> t\<close>)
  have "(\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>''' \<S>' P'''"
    apply (rule intro\<^sub>1)
    apply clarify
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma> and \<Gamma>' = \<Gamma>''' and \<S> = \<S> and P = ?P])
         apply(rule ty)
        using \<open>tyenv_wellformed mds \<Gamma> \<S> P\<close>
        apply(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)[1]
       apply(rule \<open>mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2\<close>)       
      using \<open>pred P mem\<^sub>1\<close> apply(fastforce simp: pred_def add_pred_def bexp_neg_negates)
     using \<open>pred P mem\<^sub>2\<close> apply(fastforce simp: pred_def add_pred_def bexp_neg_negates)
    by(rule \<open>tyenv_sec mds \<Gamma> mem\<^sub>1\<close>)

  show ?case
  proof -
    from ev\<^sub>B_eq if_type(13) have "(\<langle>If e th el, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>)"
      apply (cases "ev\<^sub>B mem\<^sub>1 e")
       apply (subgoal_tac "c\<^sub>1' = th")
        apply clarify
        apply (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.if_true eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq if_type(8))
       using if_type.prems(6) apply blast
      apply (subgoal_tac "c\<^sub>1' = el")
       apply (metis (hide_lams, mono_tags) cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false if_type(8))
      using if_type.prems(6) by blast
    with \<open>\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>''',\<S>',P'''\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>\<close> show ?thesis  
    by (metis if_elim if_type.prems(6))    
  qed
next (* while *)
  case (while_type \<Gamma> e t P \<S> c)
  hence [simp]: "c\<^sub>1' = (If e (c ;; While e c) Stop)" and
    [simp]: "mds' = mds" and
    [simp]: "mem\<^sub>1' = mem\<^sub>1"
    by (auto simp: while_elim)

  with while_type have "\<langle>While e c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.while eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
    
  moreover have ty: " \<turnstile> \<Gamma>,\<S>,P {c\<^sub>1'} \<Gamma>,\<S>,P"
    apply simp
    apply(rule if_type)
              apply(rule while_type(1))
             apply(rule while_type(2))
            apply(rule seq_type)
             apply(rule while_type(3))
            apply(rule has_type.while_type)
              apply(rule while_type(1))
             apply(rule while_type(2))
            apply(rule while_type(3))
           apply(rule stop_type)
          apply simp+
      apply(rule add_pred_entailment)
     apply simp
    apply(blast intro!: add_pred_subset tyenv_wellformed_subset)
    done
  moreover
  have "\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma>])
         apply(rule ty)
        using while_type apply simp+
    done
  hence "\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    using \<R>.intro\<^sub>1 by auto
  ultimately show ?case
    by fastforce
next
  case (sub \<Gamma>\<^sub>1 \<S> P\<^sub>1 c \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>2' P\<^sub>2' mds c\<^sub>1')
  have imp: "tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<and> pred P\<^sub>2 mem\<^sub>1 \<and> pred P\<^sub>2 mem\<^sub>2 \<and> tyenv_sec mds \<Gamma>\<^sub>2 mem\<^sub>1 \<Longrightarrow> 
             tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem\<^sub>1 \<and> pred P\<^sub>1 mem\<^sub>2 \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem\<^sub>1"
    apply(rule conjI)
     using sub(5) sub(4) tyenv_wellformed_sub unfolding pred_def
     apply blast
    apply(rule conjI)
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    apply(rule conjI)
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    using sub(3) context_equiv_tyenv_sec unfolding pred_def by blast

  have tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^sub>1\<^esub> mem\<^sub>2"
    using context_equiv_tyenv_eq sub by blast
    
  from imp tyenv_eq obtain c\<^sub>2' mem\<^sub>2' where c\<^sub>2'_props: "\<langle>c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    "\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^sub>1',\<S>',P\<^sub>1'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    using sub by blast 
  with R_equiv_entailment \<open>P\<^sub>1' \<turnstile> P\<^sub>2'\<close> show ?case
    using sub.hyps(6) sub.hyps(5) by blast
next case (await_type \<Gamma> e t P \<S> c \<Gamma>' \<S>' P' \<Gamma>'' P'')
  from this show ?case using no_await_no_await by blast
qed

lemma is_final_\<R>\<^sub>u_is_final:
  "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<Longrightarrow> is_final c\<^sub>1 \<Longrightarrow> is_final c\<^sub>2"
  by (fastforce dest: bisim_simple_\<R>\<^sub>u)

lemma pred_plus_impl:
  "pred P mem \<Longrightarrow> ev\<^sub>B mem e \<Longrightarrow> pred P +\<^sub>S e mem"
  unfolding add_pred_def pred_def by simp

lemma my_\<R>\<^sub>3_aux_induct [consumes 1, case_names intro\<^sub>1 intro\<^sub>3]: 
  "\<lbrakk>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>;
   \<And>c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P'. 
     \<lbrakk>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; 
      \<turnstile> \<Gamma>,\<S>,P {c} \<Gamma>',\<S>',P'\<rbrakk> \<Longrightarrow> 
    Q (c\<^sub>1 ;; c) mds mem\<^sub>1 \<Gamma>' \<S>' P' (c\<^sub>2 ;; c) mds mem\<^sub>2;
   \<And>c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P'. 
     \<lbrakk>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>; 
      Q c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mds mem\<^sub>2; 
      \<turnstile> \<Gamma>,\<S>,P {c} \<Gamma>',\<S>',P'\<rbrakk> \<Longrightarrow> 
    Q (c\<^sub>1 ;; c) mds mem\<^sub>1 \<Gamma>' \<S>' P' (c\<^sub>2 ;; c) mds mem\<^sub>2\<rbrakk> \<Longrightarrow> 
  Q c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mds mem\<^sub>2"
using \<R>\<^sub>3_aux.induct[where 
    ?x1.0 = "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>" and
    ?x2.0 = \<Gamma> and
    ?x3.0 = \<S> and
    ?x4.0 = P and
    ?x5.0 = "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>" and
    ?P = "\<lambda>ctx\<^sub>1 \<Gamma> \<S> P ctx\<^sub>2. Q (fst (fst ctx\<^sub>1)) (snd (fst ctx\<^sub>1)) (snd ctx\<^sub>1) \<Gamma> \<S> P (fst (fst ctx\<^sub>2)) (snd (fst ctx\<^sub>2)) (snd ctx\<^sub>2)"]
by force

lemma \<R>_typed_step_plus: 
  "\<lbrakk>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>; 
    \<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 } \<Gamma>',\<S>',P';
    no_await c\<^sub>1;
    tyenv_wellformed mds \<Gamma> \<S> P; 
    mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2; 
    pred P mem\<^sub>1;
    pred P mem\<^sub>2; 
    tyenv_sec mds \<Gamma> mem\<^sub>1 \<rbrakk> \<Longrightarrow> 
   (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                 \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
proof (induct arbitrary: \<Gamma> \<S> P mem\<^sub>2 rule: my_trancl_big_step_induct3)
  case (base c\<^sub>1 mds mem\<^sub>1 c\<^sub>1' mds' mem\<^sub>1')
  from this show ?case using \<R>_typed_step_no_await bisim_simple_\<R>\<^sub>u by fast
next 
  case (step c\<^sub>1 mds mem\<^sub>1 c\<^sub>1' mds' mem\<^sub>1' c\<^sub>1'' mds'' mem\<^sub>1'') 
  from this obtain mem\<^sub>2' where step\<^sub>2': "\<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1', mds', mem\<^sub>2'\<rangle>" and
      rel\<^sub>2': "\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>1', mds', mem\<^sub>2'\<rangle>"
    using bisim_simple_\<R>\<^sub>u by (metis fst_conv)
  from rel\<^sub>2' show ?case
  proof(cases rule: \<R>.cases)
    case (intro\<^sub>1) 
    from this obtain \<Gamma>'' \<S>'' P'' where 
      "\<turnstile> \<Gamma>'',\<S>'',P'' {c\<^sub>1'} \<Gamma>',\<S>',P'" 
      "tyenv_wellformed mds' \<Gamma>'' \<S>'' P''"
      "mem\<^sub>1' =\<^bsub>\<Gamma>''\<^esub> mem\<^sub>2'"
      "pred P'' mem\<^sub>1'"
      "pred P'' mem\<^sub>2'"
      "\<forall>x\<in>dom \<Gamma>''. x \<notin> mds' AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma>'' x)) mem\<^sub>1' \<le> dma mem\<^sub>1' x"
      using \<R>\<^sub>1.cases by auto
    from step\<^sub>2' \<open>no_await c\<^sub>1\<close> step.hyps(1) step.hyps(4) this obtain mem\<^sub>2'' where 
        step\<^sub>2'': "\<langle>c\<^sub>1', mds', mem\<^sub>2'\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>" and 
        rel\<^sub>2'': "\<langle>c\<^sub>1'', mds'', mem\<^sub>1''\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>"
      using no_await_trancl bisim_simple_\<R>\<^sub>u by (metis fst_conv)
    from this step\<^sub>2' show ?thesis using trancl_trans by fast
  next 
    case (intro\<^sub>3)
    from intro\<^sub>3 step.prems step.hyps(1) step.hyps(3) step.hyps(4) obtain mem\<^sub>2'' where
        step'': "\<langle>c\<^sub>1', mds', mem\<^sub>2'\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>" and 
        rel'': "\<langle>c\<^sub>1'', mds'', mem\<^sub>1''\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>"
    proof (induct arbitrary: rule: my_\<R>\<^sub>3_aux_induct)
      case (intro\<^sub>1 c\<^sub>1'1' mds' mem\<^sub>1' \<Gamma>''' \<S>''' P''' c\<^sub>1'1 mem\<^sub>2' c\<^sub>1'2 \<Gamma>'' \<S>'' P'')
      from intro\<^sub>1(1) obtain \<Gamma>v \<S>v Pv where pre_props: 
        "\<turnstile> \<Gamma>v,\<S>v,Pv {c\<^sub>1'1} \<Gamma>''',\<S>''',P'''" 
        "tyenv_wellformed mds' \<Gamma>v \<S>v Pv"
        "mem\<^sub>1' =\<^bsub>\<Gamma>v\<^esub> mem\<^sub>2'"
        "pred Pv mem\<^sub>1'"
        "pred Pv mem\<^sub>2'"
        "c\<^sub>1'1 = c\<^sub>1'1'"
        "\<forall>x\<in>dom \<Gamma>v. x \<notin> mds' AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma>v x)) mem\<^sub>1' \<le> dma mem\<^sub>1' x"
        using \<R>\<^sub>1.cases by blast
      from this intro\<^sub>1 have typed: "\<turnstile> \<Gamma>v,\<S>v,Pv {c\<^sub>1'1 ;; c\<^sub>1'2} \<Gamma>'',\<S>'',P''"
        using has_type.seq_type by blast
      from this pre_props \<open>no_await c\<^sub>1\<close> \<open>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>1'\<rangle>\<close> intro\<^sub>1(13)
        obtain mem\<^sub>2'' where 
               step: "\<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>2'\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle> \<and> 
                      \<langle>c\<^sub>1'', mds'', mem\<^sub>1''\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>"
        using no_await_trancl bisim_simple_\<R>\<^sub>u by (metis fst_conv)
      from this intro\<^sub>1(3) show ?case using no_await_trancl bisim_simple_\<R>\<^sub>u by blast
    next 
      case (intro\<^sub>3 c\<^sub>1'1' mds' mem\<^sub>1' \<Gamma>''' \<S>''' P''' c\<^sub>1'1 mem\<^sub>2' c\<^sub>1'2 \<Gamma>'' \<S>'' P'')
      from intro\<^sub>3(1) obtain \<Gamma>v \<S>v Pv where pre_props: 
        "\<turnstile> \<Gamma>v,\<S>v,Pv {c\<^sub>1'1} \<Gamma>''',\<S>''',P'''" 
        "tyenv_wellformed mds' \<Gamma>v \<S>v Pv"
        "mem\<^sub>1' =\<^bsub>\<Gamma>v\<^esub> mem\<^sub>2'"
        "pred Pv mem\<^sub>1'"
        "pred Pv mem\<^sub>2'"
        "c\<^sub>1'1 = c\<^sub>1'1'"
        "\<forall>x\<in>dom \<Gamma>v. x \<notin> mds' AsmNoReadOrWrite \<longrightarrow> type_max (the (\<Gamma>v x)) mem\<^sub>1' \<le> dma mem\<^sub>1' x"
        by (induct arbitrary: rule: my_\<R>\<^sub>3_aux_induct) 
           (blast elim: \<R>\<^sub>1.cases, blast) 
      from this intro\<^sub>1 have typed: "\<turnstile> \<Gamma>v,\<S>v,Pv {c\<^sub>1'1 ;; c\<^sub>1'2} \<Gamma>'',\<S>'',P''"
        using has_type.seq_type intro\<^sub>3.hyps(3) by blast

      from this pre_props \<open>no_await c\<^sub>1\<close> \<open>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>1'\<rangle>\<close> intro\<^sub>3
        obtain mem\<^sub>2'' where 
        step: "\<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>2'\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle> \<and> 
               \<langle>c\<^sub>1'', mds'', mem\<^sub>1''\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle>"   
      proof -
        assume a1: "\<And>mem\<^sub>2''. \<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>2'\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle> \<and> 
                               \<langle>c\<^sub>1'', mds'', mem\<^sub>1''\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>1'', mds'', mem\<^sub>2''\<rangle> \<Longrightarrow> thesis"
        thus ?thesis using intro\<^sub>3.prems(11)
          using a1 by (metis (no_types) pre_props(2-)
                       \<open>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1'1 ;; c\<^sub>1'2, mds', mem\<^sub>1'\<rangle>\<close>  \<open>no_await c\<^sub>1\<close> 
                       bisim_simple_\<R>\<^sub>u fst_conv no_await_trancl typed)
      qed
      from this intro\<^sub>3 show ?case using no_await_trancl bisim_simple_\<R>\<^sub>u by blast
    qed
    thus ?thesis 
      by (meson step\<^sub>2' trancl_trans) 
  qed
qed

(* This is the main part of the proof and used in \<R>\<^sub>1_weak_bisim: *)
lemma \<R>_typed_step:
  "\<lbrakk> \<turnstile> \<Gamma>,\<S>,P { c\<^sub>1 } \<Gamma>',\<S>',P' ;
  tyenv_wellformed mds \<Gamma> \<S> P; mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2; pred P mem\<^sub>1;
        pred P mem\<^sub>2; tyenv_sec mds \<Gamma> mem\<^sub>1;
     \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<rbrakk> \<Longrightarrow>
   (\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                 \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
proof (induct arbitrary: mds c\<^sub>1' rule: has_type.induct)
  case (seq_type \<Gamma> \<S> P c\<^sub>1 \<Gamma>'' \<S>'' P'' c\<^sub>2 \<Gamma>' \<S>' P' mds)
  show ?case
  proof (cases "c\<^sub>1 = Stop")
    assume "c\<^sub>1 = Stop"
    hence [simp]: "c\<^sub>1' = c\<^sub>2" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1"
      using seq_type
      by (auto simp: seq_stop_elim)
    from seq_type \<open>c\<^sub>1 = Stop\<close> have "context_equiv \<Gamma> P \<Gamma>''" and "\<S> = \<S>''" and "P \<turnstile> P''" and
                                   "(\<forall>mds. tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed  mds \<Gamma>'' \<S> P'')"
      by (metis stop_cxt)+
    hence "\<turnstile> \<Gamma>,\<S>,P { c\<^sub>2 } \<Gamma>',\<S>',P'"
      apply -
      apply(rule sub)
          using seq_type(3) apply simp
         by auto
    have "\<langle>c\<^sub>2, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
      apply (rule \<R>\<^sub>1.intro [of \<Gamma>])
           apply(rule \<open>\<turnstile> \<Gamma>,\<S>,P { c\<^sub>2 } \<Gamma>',\<S>',P'\<close>)
          using seq_type by auto
    thus ?case
      using \<R>.intro\<^sub>1
      apply clarify
      apply (rule_tac x = c\<^sub>2 in exI)
      apply (rule_tac x = mem\<^sub>2 in exI)
      by (auto simp: \<open>c\<^sub>1 = Stop\<close> seq_stop_eval\<^sub>w  \<R>.intro\<^sub>1)
  next
    assume "c\<^sub>1 \<noteq> Stop"
    with \<open>\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>\<close> obtain c\<^sub>1'' where c\<^sub>1''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = c\<^sub>1'' ;; c\<^sub>2"
      by (metis seq_elim)
    with seq_type(2) obtain c\<^sub>2'' mem\<^sub>2' where c\<^sub>2''_props:
      "\<langle>c\<^sub>1, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
      using seq_type.prems(1) seq_type.prems(2) seq_type.prems(3) seq_type.prems(4) seq_type.prems(5) by presburger
    hence "\<langle>c\<^sub>1'' ;; c\<^sub>2, mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      apply (rule conjE)
      apply (erule \<R>_elim, auto)
       apply (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>1 seq_type(3))
      by (metis \<R>.intro\<^sub>3 \<R>\<^sub>3_aux.intro\<^sub>3 seq_type(3))
    moreover
    from c\<^sub>2''_props have "\<langle>c\<^sub>1 ;; c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'' ;; c\<^sub>2, mds', mem\<^sub>2'\<rangle>"
      by (metis eval\<^sub>w.seq)
    ultimately show ?case
      by (metis c\<^sub>1''_props)
  qed
next
  case (anno_type \<Gamma>' \<Gamma> \<S> upd \<S>' P' P c \<Gamma>'' \<S>'' P'' mds)
  have "mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2"
  proof(clarsimp simp: tyenv_eq_def)
    fix x  
    assume a: "type_max (to_total \<Gamma>' x) mem\<^sub>1 = Low"
    hence "type_max (to_total \<Gamma> x) mem\<^sub>1 = Low"
    proof -
      from \<open>pred P mem\<^sub>1\<close> have "pred P' mem\<^sub>1"
        using anno_type.hyps(3)
        by(auto simp: restrict_preds_to_vars_def pred_def)
      with subtype_sound[OF anno_type.hyps(7)] a 
      show ?thesis
        using less_eq_Sec_def by metis
    qed
    thus " mem\<^sub>1 x = mem\<^sub>2 x"
      using anno_type.prems(2)
      unfolding tyenv_eq_def by blast
  qed
  
  have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed (update_modes upd mds) \<Gamma>' \<S>' P'"
    using anno_type
    apply auto
    by (metis tyenv_wellformed_mode_update)
  moreover
  have pred: "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1"
    using anno_type
    by (auto simp: pred_def restrict_preds_to_vars_def)
  moreover
  have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem\<^sub>1 \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<longrightarrow> 
        tyenv_sec (update_modes upd mds) \<Gamma>' mem\<^sub>1"
    apply(rule impI)
    apply(rule tyenv_sec_mode_update)
            using anno_type apply fastforce
           using anno_type pred apply fastforce
          using anno_type apply fastforce
         using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
        using anno_type apply fastforce
       apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
      apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
     using anno_type apply(fastforce simp: tyenv_wellformed_def mds_consistent_def)
    by simp  
  ultimately obtain c\<^sub>2' mem\<^sub>2' where "(\<langle>c, update_modes upd mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
    \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>'',\<S>'',P''\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>)"
    using anno_type
    apply auto    
    using \<open>mem\<^sub>1 =\<^bsub>\<Gamma>'\<^esub> mem\<^sub>2\<close> local.pred_def restrict_preds_to_vars_def upd_elim by fastforce
  thus ?case
    apply (rule_tac x = c\<^sub>2' in exI)
    apply (rule_tac x = mem\<^sub>2' in exI)
    apply auto
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w.decl)
next
  case stop_type
  with stop_no_eval show ?case by auto
next
  case (skip_type \<Gamma> \<S> P mds)
  moreover
  with skip_type have [simp]: "mds' = mds" "c\<^sub>1' = Stop" "mem\<^sub>1' = mem\<^sub>1"
    using skip_elim
    by (metis, metis, metis)
  with skip_type have "\<langle>Stop, mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>Stop, mds, mem\<^sub>2\<rangle>"
    by auto
  thus ?case
    using \<R>.intro\<^sub>1 and unannotated [where c = Skip and E = "[]"]
    apply auto
    by (metis (mono_tags, lifting) \<R>.intro\<^sub>1 old.prod.case skip_eval\<^sub>w)
next (* assign\<^sub>1 *)
  case (assign\<^sub>1 x \<Gamma> e t P P' \<S> mds)
  hence upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim
    by (auto, metis)
  from assign\<^sub>1(2) upd have \<C>_eq: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>1' x"
    by auto
  have dma_eq [simp]: "dma mem\<^sub>1 = dma mem\<^sub>1'"
    using dma_\<C> assign\<^sub>1(2) by simp
  have "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total \<Gamma> v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v \<in> dom \<Gamma>")
      assume [simp]: "v \<in> dom \<Gamma>"
      then obtain t' where [simp]: "\<Gamma> v = Some t'" by force
      hence [simp]: "(to_total \<Gamma> v) = t'"
        unfolding to_total_def by (auto split: if_splits)
      have "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        apply(rule \<C>_eq_type_max_eq)
         using \<open>\<Gamma> v = Some t'\<close> assign\<^sub>1(6) 
         unfolding tyenv_wellformed_def types_wellformed_def
         apply (metis \<open>v \<in> dom \<Gamma>\<close> option.sel)
                
        using assign\<^sub>1(2) apply simp
        done
      with is_Low' have is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
        by simp
      from assign\<^sub>1(1) \<open>v \<in> dom \<Gamma>\<close> have "x \<noteq> v" by auto
      thus ?thesis
        apply simp
        using is_Low assign\<^sub>1(7) unfolding tyenv_eq_def by auto
    next
      assume "v \<notin> dom \<Gamma>"
      hence [simp]: "\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v"
        unfolding to_total_def by simp
      with is_Low' have "dma mem\<^sub>1' v = Low" by simp
      with dma_eq have dma_v_Low: "dma mem\<^sub>1 v = Low" by simp
      hence is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low" by simp
      show ?thesis
      proof(cases "x = v")
        assume "x \<noteq> v"
        thus ?thesis
          apply simp
          using is_Low assign\<^sub>1(7) unfolding tyenv_eq_def by blast
      next
        assume "x = v"
        thus ?thesis
          apply simp
          apply(rule ev\<^sub>A_eq)
              apply(rule assign\<^sub>1(7))
             apply(rule assign\<^sub>1(8))
            apply(rule assign\<^sub>1(3))
           apply(rule assign\<^sub>1(4))
          using dma_v_Low by simp
      qed
    qed
  qed

  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>1 by metis
  moreover have "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>1 upd by metis

  moreover have "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>1 upd by metis
    
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P  \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<longrightarrow> tyenv_sec mds \<Gamma> mem\<^sub>1'"
    using tyenv_sec_eq[OF \<C>_eq, where \<Gamma>=\<Gamma>]
    unfolding tyenv_wellformed_def by blast

  ultimately have \<R>':
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply -
    apply (rule \<R>.intro\<^sub>1, auto simp: assign\<^sub>1 simp del: dma_eq)
    done

  have a: "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
  by (auto, metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.assign)

  from \<R>' a show ?case
    using \<open>c\<^sub>1' = Stop\<close> and \<open>mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* assign\<^sub>\<C> *)
  case (assign\<^sub>\<C> x \<Gamma> e t P P' \<S> mds)
  hence upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim
    by (auto, metis)
  have "mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total \<Gamma> v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v \<in> dom \<Gamma>")
      assume in_dom [simp]: "v \<in> dom \<Gamma>"
      then obtain t' where \<Gamma>v [simp]: "\<Gamma> v = Some t'" by force
      hence [simp]: "(to_total \<Gamma> v) = t'"
        unfolding to_total_def by (auto split: if_splits)
      from assign\<^sub>\<C>(4) have x_nin_C: "x \<notin> vars_of_type t'"
        using in_dom \<Gamma>v 
        by (metis option.sel snd_conv)
      have \<Gamma>v_wf: "type_wellformed t'"
        using in_dom \<Gamma>v assign\<^sub>\<C>(7) unfolding tyenv_wellformed_def types_wellformed_def
        by (metis option.sel)
        
      with x_nin_C have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        using vars_of_type_eq_type_max_eq by simp
      with is_Low' have is_Low: "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
        by simp  
      from assign\<^sub>\<C>(1) \<open>v \<in> dom \<Gamma>\<close> assign\<^sub>\<C>(7) have "x \<noteq> v"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      thus ?thesis
        apply simp
        using is_Low assign\<^sub>\<C>(8) unfolding tyenv_eq_def by auto
    next
      assume nin_dom: "v \<notin> dom \<Gamma>"
      hence [simp]: "\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v"
        unfolding to_total_def  by simp
      with is_Low' have "dma mem\<^sub>1' v = Low" by simp
      show ?thesis
      proof(cases "x = v")
        assume "x = v"
        thus ?thesis
          apply simp
          apply(rule ev\<^sub>A_eq')
             apply(rule assign\<^sub>\<C>(8))
            apply(rule assign\<^sub>\<C>(9))
           apply(rule assign\<^sub>\<C>(2))
          by(rule assign\<^sub>\<C>(3))
      next
        assume [simp]: "x \<noteq> v"
        show ?thesis
        proof(cases "x \<in> \<C>_vars v")
          assume in_\<C>_vars: "x \<in> \<C>_vars v"
          hence "v \<notin> \<C>"
            using \<C>_vars_\<C> by auto
          with nin_dom have "v \<notin> snd \<S>"
            using assign\<^sub>\<C>(7)
            by(auto simp: tyenv_wellformed_def mds_consistent_def stable_def)
          with in_\<C>_vars have "P \<turnstile> (to_total \<Gamma> v)"
            using assign\<^sub>\<C>(6) by blast
          with assign\<^sub>\<C>(9) have "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
            by(auto simp: type_max_def pred_def pred_entailment_def)
          thus ?thesis
            using not_sym[OF \<open>x \<noteq> v\<close>]
            apply simp
            using assign\<^sub>\<C>(8)
            unfolding tyenv_eq_def by auto
        next
          assume "x \<notin> \<C>_vars v"
          with is_Low' have "dma mem\<^sub>1 v = Low"
            using dma_\<C>_vars \<open>\<And>mem. type_max (to_total \<Gamma> v) mem = dma mem v\<close>
            by (metis fun_upd_other)
          thus ?thesis
            using not_sym[OF \<open>x \<noteq> v\<close>]
            apply simp
            using assign\<^sub>\<C>(8)
            unfolding tyenv_eq_def by auto            
        qed
      qed
    qed
  qed

  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' \<Gamma> \<S> P'"
    using upd tyenv_wellformed_preds_update assign\<^sub>\<C> by metis
  moreover have "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>\<C> upd by metis
  moreover have "tyenv_wellformed mds \<Gamma> \<S> P \<and> pred P mem\<^sub>1 \<and> tyenv_sec mds \<Gamma> mem\<^sub>1 \<Longrightarrow> tyenv_sec mds' \<Gamma> mem\<^sub>1'"
  proof(clarify)
    fix v t'
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem\<^sub>1"
    hence pred': "pred P' mem\<^sub>1'" using \<open>pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'\<close> by blast
    assume sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
    assume \<Gamma>v: "\<Gamma> v = Some t'"
    assume readable': "v \<notin> mds' AsmNoReadOrWrite"
    with upd have readable: "v \<notin> mds AsmNoReadOrWrite" by simp
    with wf have "v \<notin> snd \<S>" by(auto simp: tyenv_wellformed_def mds_consistent_def)
    show "type_max (the (\<Gamma> v)) mem\<^sub>1' \<le> dma mem\<^sub>1' v"
    proof(cases "x \<in> \<C>_vars v")
      assume "x \<in> \<C>_vars v"
      with assign\<^sub>\<C>(6) \<open>v \<notin> snd \<S>\<close> have "(to_total \<Gamma> v) \<le>:\<^sub>P' (dma_type v)" by blast
      from pred' \<Gamma>v subtype_sound[OF this] show ?thesis
        using type_max_dma_type by(auto simp: to_total_def split: if_splits)
    next
      assume "x \<notin> \<C>_vars v"
      hence "\<forall>v'\<in>\<C>_vars v. mem\<^sub>1 v' = mem\<^sub>1' v'"
        using upd by auto
      hence dma_eq: "dma mem\<^sub>1 v = dma mem\<^sub>1' v"
        by(rule dma_\<C>_vars)
      from \<Gamma>v assign\<^sub>\<C>(4) have "x \<notin> vars_of_type t'" by force
      have "type_wellformed t'"
        using wf \<Gamma>v by(force simp: tyenv_wellformed_def types_wellformed_def)
      with \<open>x \<notin> vars_of_type t'\<close> upd have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        using vars_of_type_eq_type_max_eq by fastforce
      from sec \<Gamma>v readable have "type_max t' mem\<^sub>1 \<le> dma mem\<^sub>1 v"
        by auto
      with f_eq dma_eq \<Gamma>v show ?thesis
        by simp
    qed
  qed

  ultimately have \<R>':
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply -
    apply (rule \<R>.intro\<^sub>1, auto simp: assign\<^sub>\<C>)
    done

  have a: "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
  by (auto, metis cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.assign)

  from \<R>' a show ?case
    using \<open>c\<^sub>1' = Stop\<close> and \<open>mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* assign\<^sub>2 *)
  case (assign\<^sub>2 x \<Gamma> e t \<S> P' P mds)
  have upd [simp]: "c\<^sub>1' = Stop" "mds' = mds" "mem\<^sub>1' = mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)"
    using assign_elim[OF assign\<^sub>2(11)]
    by auto
  from \<open>x \<in> dom \<Gamma>\<close> \<open>tyenv_wellformed mds \<Gamma> \<S> P\<close>
  have x_nin_\<C>: "x \<notin> \<C>"
    by(auto simp: tyenv_wellformed_def mds_consistent_def)
  hence dma_eq [simp]: "dma mem\<^sub>1' = dma mem\<^sub>1"
    using dma_\<C> assign\<^sub>2
    by auto
    
  let ?\<Gamma>' = "\<Gamma> (x \<mapsto> t)"
  have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using assign\<^sub>2
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.assign eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
    
  moreover
  have tyenv_eq': "mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e) =\<^bsub>\<Gamma>(x \<mapsto> t)\<^esub> mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)"
  unfolding tyenv_eq_def
  proof(clarify)
    fix v
    assume is_Low': "type_max (to_total (\<Gamma>(x \<mapsto> t)) v) (mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) = Low"
    show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
    proof(cases "v = x")
      assume neq: "v \<noteq> x"
      hence "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
      proof(cases "v \<in> dom \<Gamma>")
        assume "v \<in> dom \<Gamma>"
        then obtain t' where [simp]: "\<Gamma> v = Some t'" by force
        hence [simp]: "(to_total \<Gamma> v) = t'"
          unfolding to_total_def by (auto split: if_splits)
        hence [simp]: "(to_total ?\<Gamma>' v) = t'"
          using neq by(auto simp: to_total_def)
        have "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
          apply(rule \<C>_eq_type_max_eq)
            using assign\<^sub>2(6) 
            apply(clarsimp simp: tyenv_wellformed_def types_wellformed_def)
            using \<open>v \<in> dom \<Gamma>\<close> \<open>\<Gamma> v = Some t'\<close> apply(metis option.sel)
           using x_nin_\<C> by simp
        from this is_Low' neq neq[THEN not_sym] show "type_max (to_total \<Gamma> v) mem\<^sub>1 = Low"
          by auto
      next
        assume "v \<notin> dom \<Gamma>"
        with is_Low' neq
        have "dma mem\<^sub>1' v = Low"
          by(auto simp: to_total_def  split: if_splits)
        with dma_eq \<open>v \<notin> dom \<Gamma>\<close> show ?thesis
          by(auto simp: to_total_def  split: if_splits)
      qed
      with neq assign\<^sub>2(7) show "(mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)) v = (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e)) v"
        by(auto simp: tyenv_eq_def)
    next
      assume eq[simp]: "v = x"
      with is_Low' \<open>x \<in> dom \<Gamma>\<close> have t_Low': "type_max t mem\<^sub>1' = Low"
        by(auto simp: to_total_def split: if_splits)
      have wf_t: "type_wellformed t"
        using type_aexpr_type_wellformed assign\<^sub>2(2) assign\<^sub>2(6)
        by(fastforce simp: tyenv_wellformed_def)
      with t_Low' \<open>x \<notin> \<C>\<close> have t_Low: "type_max t mem\<^sub>1 = Low"
        using \<C>_eq_type_max_eq
        by (metis (no_types, lifting) fun_upd_other upd(3))
      show ?thesis
      proof(simp, rule eval_vars_det\<^sub>A, clarify)
        fix y
        assume in_vars: "y \<in> aexp_vars e"
        have "type_max (to_total \<Gamma> y) mem\<^sub>1 = Low"
        proof -
          from t_Low in_vars assign\<^sub>2(2) show ?thesis
            apply -
            apply(erule type_aexpr.cases)
            using Sec.exhaust by(auto simp: type_max_def  split: if_splits)
        qed
        thus "mem\<^sub>1 y = mem\<^sub>2 y"
          using assign\<^sub>2 unfolding tyenv_eq_def by blast
      qed
    qed
  qed

  from upd have ty: " \<turnstile> ?\<Gamma>',\<S>,P' {c\<^sub>1'} ?\<Gamma>',\<S>,P'"
    by (metis stop_type)
  have wf: "tyenv_wellformed mds \<Gamma> \<S> P \<longrightarrow> tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
  proof
    assume tyenv_wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    hence wf: "types_wellformed \<Gamma>"
      unfolding tyenv_wellformed_def by blast
    hence  "type_wellformed t"
      using assign\<^sub>2(2) type_aexpr_type_wellformed
      by blast
    with wf have wf': "types_wellformed ?\<Gamma>'"
      using types_wellformed_update by metis
    from tyenv_wf have stable': "types_stable ?\<Gamma>' \<S>"
      using types_stable_update
            assign\<^sub>2(3)
      unfolding tyenv_wellformed_def by blast
    have m: "mds_consistent mds \<Gamma> \<S> P"
      using tyenv_wf unfolding tyenv_wellformed_def by blast
    from assign\<^sub>2(4) assign\<^sub>2(1)
    have "mds_consistent mds' (\<Gamma>(x \<mapsto> t)) \<S> P'"
      apply(rule mds_consistent_preds_tyenv_update)
      using upd m by simp
    from wf' stable' this show "tyenv_wellformed mds' ?\<Gamma>' \<S> P'"
      unfolding tyenv_wellformed_def by blast
  qed
  have p: "pred P mem\<^sub>1 \<longrightarrow> pred P' mem\<^sub>1'"
    using pred_preds_update assign\<^sub>2 upd by metis
  have p\<^sub>2: "pred P mem\<^sub>2 \<longrightarrow> pred P' (mem\<^sub>2(x := ev\<^sub>A mem\<^sub>2 e))"
    using pred_preds_update assign\<^sub>2 upd by metis
  have sec: "tyenv_wellformed mds \<Gamma> \<S> P \<Longrightarrow> pred P mem\<^sub>1 \<Longrightarrow> tyenv_sec mds \<Gamma> mem\<^sub>1 \<Longrightarrow> tyenv_sec mds' ?\<Gamma>' mem\<^sub>1'"
  proof(clarify)
    assume wf: "tyenv_wellformed mds \<Gamma> \<S> P"
    assume pred: "pred P mem\<^sub>1"
    assume sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
    from pred p have pred': "pred P' mem\<^sub>1'" by blast
    fix v t'
    assume \<Gamma>v: "(\<Gamma>(x \<mapsto> t)) v = Some t'"
    assume "v \<notin> mds' AsmNoReadOrWrite"
    show "type_max (the ((\<Gamma>(x \<mapsto> t)) v)) mem\<^sub>1' \<le> dma mem\<^sub>1' v"
    proof(cases "v = x")
      assume [simp]: "v = x"
      hence [simp]: "(the ((\<Gamma>(x \<mapsto> t)) v)) = t" and t_def: "t = t'"
        using \<Gamma>v by auto
      from \<open>v \<notin> mds' AsmNoReadOrWrite\<close> upd wf have readable: "v \<notin> snd \<S>"
        by(auto simp: tyenv_wellformed_def mds_consistent_def)
      with assign\<^sub>2(5) have "t \<le>:\<^sub>P' (dma_type x)" by fastforce
      with pred' show ?thesis
        using type_max_dma_type subtype_sound
        by fastforce
    next
      assume neq: "v \<noteq> x"
      hence [simp]: "((\<Gamma>(x \<mapsto> t)) v) = \<Gamma> v"
        by simp
      with \<Gamma>v have \<Gamma>v: "\<Gamma> v = Some t'" by simp
      with sec upd \<open>v \<notin> mds' AsmNoReadOrWrite\<close> have f_leq: "type_max t' mem\<^sub>1 \<le> dma mem\<^sub>1 v"
        by auto
      have \<C>_eq: "\<forall>x\<in>\<C>. mem\<^sub>1 x = mem\<^sub>1' x"
        using wf assign\<^sub>2(1) upd by(auto simp: tyenv_wellformed_def mds_consistent_def)
      hence dma_eq: "dma mem\<^sub>1 = dma mem\<^sub>1'"
        by(rule dma_\<C>)
      have f_eq: "type_max t' mem\<^sub>1 = type_max t' mem\<^sub>1'"
        apply(rule \<C>_eq_type_max_eq)
         using \<Gamma>v wf apply(force simp: tyenv_wellformed_def types_wellformed_def)
        by(rule \<C>_eq)     
      from neq \<Gamma>v f_leq dma_eq f_eq show ?thesis
        by simp
    qed
  qed

  have "\<langle>Stop, mds, mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>1\<^bsub>?\<Gamma>',\<S>,P'\<^esub> \<langle>Stop, mds, mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    apply(rule \<R>\<^sub>1.intro)
         apply blast
        using wf assign\<^sub>2 apply fastforce
       apply(rule tyenv_eq')
      using p assign\<^sub>2 apply fastforce
     using p\<^sub>2 assign\<^sub>2 apply fastforce
    using sec assign\<^sub>2
    using upd(2) upd(3) by blast
    
  ultimately have "\<langle>x \<leftarrow> e, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    "\<langle>Stop, mds', mem\<^sub>1 (x := ev\<^sub>A mem\<^sub>1 e)\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>(x \<mapsto> t),\<S>,P'\<^esub> \<langle>Stop, mds', mem\<^sub>2 (x := ev\<^sub>A mem\<^sub>2 e)\<rangle>"
    using \<R>.intro\<^sub>1
    by auto
  thus ?case
    using \<open>mds' = mds\<close> \<open>c\<^sub>1' = Stop\<close> \<open>mem\<^sub>1' = mem\<^sub>1(x := ev\<^sub>A mem\<^sub>1 e)\<close>
    by blast
next (* if *)
  case (if_type \<Gamma> e t P \<S> th \<Gamma>' \<S>' P' el \<Gamma>'' P'' \<Gamma>''' P''')
  let ?P = "if (ev\<^sub>B mem\<^sub>1 e) then P +\<^sub>\<S> e else P +\<^sub>\<S> (bexp_neg e)"
  from \<open>\<langle>Stmt.If e th el, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>\<close> have ty: "\<turnstile> \<Gamma>,\<S>,?P {c\<^sub>1'} \<Gamma>''',\<S>',P'''"
  proof (rule if_elim)
    assume "c\<^sub>1' = th" "mem\<^sub>1' = mem\<^sub>1" "mds' = mds" "ev\<^sub>B mem\<^sub>1 e"
    with if_type(3)
    show ?thesis
      apply simp
      apply(erule sub)
         using if_type apply simp+
      done
  next
    assume "c\<^sub>1' = el" "mem\<^sub>1' = mem\<^sub>1" "mds' = mds" "\<not> ev\<^sub>B mem\<^sub>1 e"
    with if_type(5)
    show ?thesis
      apply simp
      apply(erule sub)
         using if_type apply simp+
      done
  qed
  have ev\<^sub>B_eq [simp]: "ev\<^sub>B mem\<^sub>1 e = ev\<^sub>B mem\<^sub>2 e"
    apply(rule ev\<^sub>B_eq')
       apply(rule \<open>mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2\<close>)
      apply(rule \<open>pred P mem\<^sub>1\<close>)
     apply(rule \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close>)
    by(rule \<open> P \<turnstile> t\<close>)
  have "(\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>) \<in> \<R> \<Gamma>''' \<S>' P'''"
    apply (rule intro\<^sub>1)
    apply clarify
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma> and \<Gamma>' = \<Gamma>''' and \<S> = \<S> and P = ?P])
         apply(rule ty)
        using \<open>tyenv_wellformed mds \<Gamma> \<S> P\<close>
        apply(auto simp: tyenv_wellformed_def mds_consistent_def add_pred_def)[1]
       apply(rule \<open>mem\<^sub>1 =\<^bsub>\<Gamma>\<^esub> mem\<^sub>2\<close>)       
      using \<open>pred P mem\<^sub>1\<close> apply(fastforce simp: pred_def add_pred_def bexp_neg_negates)
     using \<open>pred P mem\<^sub>2\<close> apply(fastforce simp: pred_def add_pred_def bexp_neg_negates)
    by(rule \<open>tyenv_sec mds \<Gamma> mem\<^sub>1\<close>)

  show ?case
  proof -
    from ev\<^sub>B_eq if_type(13) have "(\<langle>If e th el, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>)"
      apply (cases "ev\<^sub>B mem\<^sub>1 e")
       apply (subgoal_tac "c\<^sub>1' = th")
        apply clarify
        apply (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.if_true eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq if_type(8))
       using if_type.prems(6) apply blast
      apply (subgoal_tac "c\<^sub>1' = el")
       apply (metis (hide_lams, mono_tags) cxt_to_stmt.simps(1) eval\<^sub>w.unannotated eval\<^sub>w_simple.if_false if_type(8))
      using if_type.prems(6) by blast
    with \<open>\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>''',\<S>',P'''\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>\<close> show ?thesis  
    by (metis if_elim if_type.prems(6))    
  qed
next (* while *)
  case (while_type \<Gamma> e t P \<S> c)
  hence [simp]: "c\<^sub>1' = (If e (c ;; While e c) Stop)" and
    [simp]: "mds' = mds" and
    [simp]: "mem\<^sub>1' = mem\<^sub>1"
    by (auto simp: while_elim)

  with while_type have "\<langle>While e c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    by (metis cxt_to_stmt.simps(1) eval\<^sub>w_simplep.while eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq)
    
  moreover have ty: " \<turnstile> \<Gamma>,\<S>,P {c\<^sub>1'} \<Gamma>,\<S>,P"
    apply simp
    apply(rule if_type)
              apply(rule while_type(1))
             apply(rule while_type(2))
            apply(rule seq_type)
             apply(rule while_type(3))
            apply(rule has_type.while_type)
              apply(rule while_type(1))
             apply(rule while_type(2))
            apply(rule while_type(3))
           apply(rule stop_type)
          apply simp+
      apply(rule add_pred_entailment)
     apply simp
    apply(blast intro!: add_pred_subset tyenv_wellformed_subset)
    done
  moreover
  have "\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>1\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    apply (rule \<R>\<^sub>1.intro [where \<Gamma> = \<Gamma>])
         apply(rule ty)
        using while_type apply simp+
    done
  hence "\<langle>c\<^sub>1', mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>1', mds, mem\<^sub>2\<rangle>"
    using \<R>.intro\<^sub>1 by auto
  ultimately show ?case
    by fastforce
next
  case (sub \<Gamma>\<^sub>1 \<S> P\<^sub>1 c \<Gamma>\<^sub>1' \<S>' P\<^sub>1' \<Gamma>\<^sub>2 P\<^sub>2 \<Gamma>\<^sub>2' P\<^sub>2' mds c\<^sub>1')
  have imp: "tyenv_wellformed mds \<Gamma>\<^sub>2 \<S> P\<^sub>2 \<and> pred P\<^sub>2 mem\<^sub>1 \<and> pred P\<^sub>2 mem\<^sub>2 \<and> tyenv_sec mds \<Gamma>\<^sub>2 mem\<^sub>1 \<Longrightarrow> 
             tyenv_wellformed mds \<Gamma>\<^sub>1 \<S> P\<^sub>1 \<and> pred P\<^sub>1 mem\<^sub>1 \<and> pred P\<^sub>1 mem\<^sub>2 \<and> tyenv_sec mds \<Gamma>\<^sub>1 mem\<^sub>1"
    apply(rule conjI)
     using sub(5) sub(4) tyenv_wellformed_sub unfolding pred_def
     apply blast
    apply(rule conjI)
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    apply(rule conjI)
     using local.pred_def pred_entailment_def sub.hyps(7) apply auto[1]
    using sub(3) context_equiv_tyenv_sec unfolding pred_def by blast

  have tyenv_eq: "mem\<^sub>1 =\<^bsub>\<Gamma>\<^sub>1\<^esub> mem\<^sub>2"
    using context_equiv_tyenv_eq sub by blast
    
  from imp tyenv_eq obtain c\<^sub>2' mem\<^sub>2' where c\<^sub>2'_props: "\<langle>c, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    "\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>\<^sub>1',\<S>',P\<^sub>1'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    using sub by blast 
  with R_equiv_entailment \<open>P\<^sub>1' \<turnstile> P\<^sub>2'\<close> show ?case
    using sub.hyps(6) sub.hyps(5) by blast
next case (await_type \<Gamma> e t P \<S> c \<Gamma>' \<S>' P')
  from await_type.prems have "ev\<^sub>B mem\<^sub>1 e" "no_await c" "is_final c\<^sub>1'" and step: "\<langle>c, mds, mem\<^sub>1\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
    using await_elim by simp+
  from await_type.prems \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close> \<open>P \<turnstile> t\<close> have "pred P +\<^sub>\<S> e mem\<^sub>1" "pred P +\<^sub>\<S> e mem\<^sub>2" "ev\<^sub>B mem\<^sub>2 e"
    using pred_plus_impl \<open>ev\<^sub>B mem\<^sub>1 e\<close> \<open>pred P mem\<^sub>1\<close> ev\<^sub>B_eq'
    by blast+
  from await_type.prems \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close> \<open>P \<turnstile> t\<close> have wellformed: "tyenv_wellformed mds \<Gamma> \<S> P +\<^sub>\<S> e"
    apply (unfold add_pred_def)[1]
      apply (case_tac "pred_stable \<S> e", clarsimp)
        apply (unfold tyenv_wellformed_def, clarsimp)[1]
        apply (unfold mds_consistent_def, clarsimp)[1]
      by clarsimp
  from step \<open>is_final c\<^sub>1'\<close> \<open>no_await c\<close> \<open>tyenv_wellformed mds \<Gamma> \<S> P +\<^sub>\<S> e\<close> await_type.prems \<open>pred P +\<^sub>\<S> e mem\<^sub>1\<close> \<open>pred P +\<^sub>\<S> e mem\<^sub>2\<close>
    obtain c\<^sub>2' mem\<^sub>2' where step: "\<langle>c, mds, mem\<^sub>2\<rangle> \<leadsto>\<^sup>+ \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>" and 
      rel: "\<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>" "is_final c\<^sub>2'"  
    using \<R>_typed_step_plus await_type.hyps(3) is_final_\<R>\<^sub>u_is_final by meson
  from wellformed \<open>is_final c\<^sub>2'\<close> \<open>ev\<^sub>B mem\<^sub>2 e\<close> \<open>no_await c\<close> \<open>\<Gamma> \<turnstile>\<^sub>b e \<in> t\<close> \<open>P \<turnstile> t\<close> \<open>pred P +\<^sub>\<S> e mem\<^sub>2\<close> step rel show ?case 
    using eval\<^sub>w.intros(4) by blast
qed

(* We can now show that \<R>\<^sub>1 and \<R>\<^sub>3 are weak bisimulations of \<R>,: *)
lemma \<R>\<^sub>1_weak_bisim:
  "weak_bisim (\<R>\<^sub>1 \<Gamma>' \<S>' P') (\<R> \<Gamma>' \<S>' P')"
  unfolding weak_bisim_def
  apply clarsimp
  apply(erule \<R>\<^sub>1_elim)
  apply(blast intro: \<R>_typed_step)
  done


lemma \<R>_to_\<R>\<^sub>3: "\<lbrakk> \<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> ; \<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P' \<rbrakk> \<Longrightarrow>
  \<langle>c\<^sub>1 ;; c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>3\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2 ;; c, mds, mem\<^sub>2\<rangle>"
  apply (erule \<R>_elim)
  by auto


lemma \<R>\<^sub>3_weak_bisim:
  "weak_bisim (\<R>\<^sub>3 \<Gamma>' \<S>' P') (\<R> \<Gamma>' \<S>' P')"
proof -
  {
    fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
    assume case3: "(\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle>, \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>) \<in> \<R>\<^sub>3 \<Gamma>' \<S>' P'"
    assume eval: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
    have "\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
      using case3 eval
      apply simp
      
    proof (induct arbitrary: c\<^sub>1' rule: \<R>\<^sub>3_aux.induct)
      case (intro\<^sub>1 c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P')
      hence [simp]: "c\<^sub>2 = c\<^sub>1"
        by (metis (lifting) \<R>\<^sub>1_elim)
      thus ?case
      proof (cases "c\<^sub>1 = Stop")
        assume [simp]: "c\<^sub>1 = Stop"
        from intro\<^sub>1(1) show ?thesis
          apply (rule \<R>\<^sub>1_elim)
          apply simp
          apply (rule_tac x = c in exI)
          apply (rule_tac x = mem\<^sub>2 in exI)
          apply (rule conjI)
           apply (metis \<open>c\<^sub>1 = Stop\<close> cxt_to_stmt.simps(1) eval\<^sub>w_simplep.seq_stop eval\<^sub>wp.unannotated eval\<^sub>wp_eval\<^sub>w_eq intro\<^sub>1.prems seq_stop_elim)
          apply (rule \<R>.intro\<^sub>1, clarify)
          apply (subgoal_tac "c\<^sub>1' = c")
           apply simp
           apply (rule \<R>\<^sub>1.intro)
                apply(rule intro\<^sub>1(2))
               apply (metis (no_types, lifting) \<open>c\<^sub>1 = Stop\<close> intro\<^sub>1.prems seq_stop_elim stop_cxt tyenv_wellformed_sub)
              using \<open>c\<^sub>1 = Stop\<close> intro\<^sub>1.prems seq_stop_elim stop_cxt context_equiv_tyenv_eq
              apply metis

             using \<open>c\<^sub>1 = Stop\<close> intro\<^sub>1.prems pred_entailment_def seq_stop_elim stop_cxt apply blast
            using pred_entailment_def stop_cxt apply blast
           
           apply (metis (no_types, lifting) \<open>c\<^sub>1 = Stop\<close> context_equiv_def intro\<^sub>1.prems less_eq_Sec_def seq_stop_elim stop_cxt subtype_sound type_equiv_def)
          using intro\<^sub>1.prems seq_stop_elim by auto
      next
        assume "c\<^sub>1 \<noteq> Stop"
        from intro\<^sub>1
        obtain c\<^sub>1'' where "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = (c\<^sub>1'' ;; c)"
          by (metis \<open>c\<^sub>1 \<noteq> Stop\<close> intro\<^sub>1.prems seq_elim)
        with intro\<^sub>1
        obtain c\<^sub>2'' mem\<^sub>2' where "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>" "\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
          using \<R>\<^sub>1_weak_bisim and weak_bisim_def
          by blast
        thus ?thesis
          using intro\<^sub>1(2) \<R>_to_\<R>\<^sub>3
          apply (rule_tac x = "c\<^sub>2'' ;; c" in exI)
          apply (rule_tac x = mem\<^sub>2' in exI)
          apply (rule conjI)
           apply (metis eval\<^sub>w.seq)
          apply auto
          apply (rule \<R>.intro\<^sub>3)
          
          by (simp add: \<R>_to_\<R>\<^sub>3 \<open>\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<and> c\<^sub>1' = c\<^sub>1'' ;; c\<close>)
      qed
    next
      case (intro\<^sub>3 c\<^sub>1 mds mem\<^sub>1 \<Gamma> \<S> P c\<^sub>2 mem\<^sub>2 c \<Gamma>' \<S>' P')
      thus ?case
        apply (cases "c\<^sub>1 = Stop")
         apply blast
      proof -
        assume "c\<^sub>1 \<noteq> Stop"
        then obtain c\<^sub>1'' where "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle>" "c\<^sub>1' = (c\<^sub>1'' ;; c)"
          by (metis intro\<^sub>3.prems seq_elim)
        then obtain c\<^sub>2'' mem\<^sub>2' where "\<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>" "\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>"
          using intro\<^sub>3(2) by metis
        thus ?thesis
          apply (rule_tac x = "c\<^sub>2'' ;; c" in exI)
          apply (rule_tac x = mem\<^sub>2' in exI)
          apply (rule conjI)
           apply (metis eval\<^sub>w.seq)
          apply (erule \<R>_elim)
            apply simp_all
            apply (metis \<R>.intro\<^sub>3 \<R>_to_\<R>\<^sub>3 \<open>\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>\<close> \<open>c\<^sub>1' = c\<^sub>1'' ;; c\<close> intro\<^sub>3(3))
          apply (metis (lifting) \<R>.intro\<^sub>3 \<R>_to_\<R>\<^sub>3 \<open>\<langle>c\<^sub>1'', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>,\<S>,P\<^esub> \<langle>c\<^sub>2'', mds', mem\<^sub>2'\<rangle>\<close> \<open>c\<^sub>1' = c\<^sub>1'' ;; c\<close> intro\<^sub>3(3))
          done
      qed
    qed
  }
  thus ?thesis
    unfolding weak_bisim_def
    by auto
qed

(* Hence \<R> is a bisimulation: *)
lemma \<R>_bisim: "strong_low_bisim_mm (\<R> \<Gamma>' \<S>' P')"
  unfolding strong_low_bisim_mm_def
proof (auto)
  from \<R>_sym show "sym (\<R> \<Gamma>' \<S>' P')" .
next
  from \<R>_closed_glob_consistent show "closed_glob_consistent (\<R> \<Gamma>' \<S>' P')" .
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2
  assume "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  thus "mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
    apply (rule \<R>_elim)
    by (auto simp: \<R>\<^sub>1_mem_eq \<R>\<^sub>3_mem_eq)
next
  fix c\<^sub>1 mds mem\<^sub>1 c\<^sub>2 mem\<^sub>2 c\<^sub>1' mds' mem\<^sub>1'
  assume eval: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<leadsto> \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle>"
  assume R: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  from R show "\<exists> c\<^sub>2' mem\<^sub>2'. \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle> \<leadsto> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle> \<and>
                            \<langle>c\<^sub>1', mds', mem\<^sub>1'\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c\<^sub>2', mds', mem\<^sub>2'\<rangle>"
    apply (rule \<R>_elim)
      apply (insert \<R>\<^sub>1_weak_bisim \<R>\<^sub>3_weak_bisim eval weak_bisim_def)
      apply auto
    done
qed

lemma Typed_in_\<R>:
  assumes typeable: "\<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P'"
  assumes wf: "tyenv_wellformed mds \<Gamma> \<S> P"
  assumes mem_eq: "\<forall> x. type_max (to_total \<Gamma> x) mem\<^sub>1 = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
  assumes pred\<^sub>1: "pred P mem\<^sub>1"
  assumes pred\<^sub>2: "pred P mem\<^sub>2"
  assumes tyenv_sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
  shows "\<langle>c, mds, mem\<^sub>1\<rangle> \<R>\<^sup>u\<^bsub>\<Gamma>',\<S>',P'\<^esub> \<langle>c, mds, mem\<^sub>2\<rangle>"
  apply (rule \<R>.intro\<^sub>1 [of \<Gamma>'])
  apply clarify
  apply (rule \<R>\<^sub>1.intro [of \<Gamma>])
       apply(rule typeable)
      apply(rule wf)
     using mem_eq apply(fastforce simp: tyenv_eq_def)
    using assms by simp+

(* We then prove the main soundness theorem using the fact that typeable
    configurations can be related using \<R>\<^sub>1 *)
theorem type_soundness:
  assumes well_typed: "\<turnstile> \<Gamma>,\<S>,P { c } \<Gamma>',\<S>',P'"
  assumes wf: "tyenv_wellformed mds \<Gamma> \<S> P"
  assumes mem_eq: "\<forall> x. type_max (to_total \<Gamma> x) mem\<^sub>1 = Low \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
  assumes pred\<^sub>1: "pred P mem\<^sub>1"
  assumes pred\<^sub>2: "pred P mem\<^sub>2"
  assumes tyenv_sec: "tyenv_sec mds \<Gamma> mem\<^sub>1"
  shows "\<langle>c, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c, mds, mem\<^sub>2\<rangle>"
  using \<R>_bisim Typed_in_\<R>
  by (metis assms mem_eq mm_equiv.simps well_typed)

definition
  \<Gamma>_of_mds :: "'Var Mds \<Rightarrow> ('Var,'BExp) TyEnv"
where
  "\<Gamma>_of_mds mds \<equiv> (\<lambda>x. if x \<notin> \<C> \<and> x \<in> mds AsmNoWrite \<union> mds AsmNoReadOrWrite then
                         if x \<in> mds AsmNoReadOrWrite then 
                           Some ({pred_False}) 
                         else
                           Some (dma_type x) 
                       else None)"

definition
  \<S>_of_mds :: "'Var Mds \<Rightarrow> 'Var Stable"
where
  "\<S>_of_mds mds \<equiv> (mds AsmNoWrite, mds AsmNoReadOrWrite)"

definition
  mds_yields_stable_types :: "'Var Mds \<Rightarrow> bool"
where
  "mds_yields_stable_types mds \<equiv> \<forall>x. x \<in> mds AsmNoWrite \<union> mds AsmNoReadOrWrite \<longrightarrow>
                                     (\<forall>v\<in>\<C>_vars x. v \<in> mds AsmNoWrite \<union> mds AsmNoReadOrWrite)"
  
(* The typing relation for lists of commands ("thread pools"). *)
inductive 
  type_global :: "(('Var, 'AExp, 'BExp) Stmt \<times> 'Var Mds) list \<Rightarrow> bool"
  ("\<turnstile> _" [120] 1000)
where
  "\<lbrakk> list_all (\<lambda> (c,m). (\<exists> \<Gamma>' \<S>' P'. \<turnstile> (\<Gamma>_of_mds m),(\<S>_of_mds m),{} { c } \<Gamma>',\<S>',P') \<and> mds_yields_stable_types m) cs ;
       \<forall> mem. sound_mode_use (cs, mem)
    \<rbrakk> \<Longrightarrow>
    type_global cs"

                                     
inductive_cases type_global_elim: "\<turnstile> cs"

lemma of_mds_tyenv_wellformed: "mds_yields_stable_types m \<Longrightarrow> tyenv_wellformed m (\<Gamma>_of_mds m) (\<S>_of_mds m) {}"
  apply(auto simp: tyenv_wellformed_def \<Gamma>_of_mds_def \<S>_of_mds_def mds_consistent_def stable_def
                   types_wellformed_def types_stable_def  mds_yields_stable_types_def 
                   type_wellformed_def dma_\<C>_vars \<C>_def bexp_vars_pred_False \<C>_vars_correct
             split: if_splits)
  done

lemma \<Gamma>_of_mds_tyenv_sec:
  "tyenv_sec m (\<Gamma>_of_mds m) mem\<^sub>1"
  apply(auto simp: \<Gamma>_of_mds_def)
  done

lemma type_max_pred_False [simp]:
  "type_max {pred_False} mem = High"
  apply(simp add: type_max_def pred_False_is_False)
  done
  
lemma typed_secure:
  "\<lbrakk> \<turnstile> (\<Gamma>_of_mds m),(\<S>_of_mds m),{} { c } \<Gamma>',\<S>',P'; mds_yields_stable_types m \<rbrakk> \<Longrightarrow> com_sifum_secure (c,m)"
  apply (clarsimp simp: com_sifum_secure_def low_indistinguishable_def)
  apply (erule type_soundness)
      apply(erule of_mds_tyenv_wellformed)
     apply(auto simp: to_total_def split: if_split simp: \<Gamma>_of_mds_def low_mds_eq_def)[1]
    apply(fastforce simp: pred_def type_max_def)
   apply(fastforce simp: pred_def)
  by(rule \<Gamma>_of_mds_tyenv_sec)

lemma list_all_set: "\<forall> x \<in> set xs. P x \<Longrightarrow> list_all P xs"
  by (metis (lifting) list_all_iff)

theorem type_soundness_global:
  assumes typeable: "\<turnstile> cs"
  shows "prog_sifum_secure_cont cs"
  using typeable
  apply (rule type_global_elim)
  apply (subgoal_tac "\<forall> c \<in> set cs. com_sifum_secure c")
   apply(rule sifum_compositionality_cont)
    using list_all_set apply fastforce
   apply fastforce
  apply(drule list_all_iff[THEN iffD1])
  apply clarsimp
  apply(rename_tac c m)
  apply(drule_tac x="(c,m)" in bspec)
   apply assumption
  apply clarsimp
  using typed_secure by blast

end
end
