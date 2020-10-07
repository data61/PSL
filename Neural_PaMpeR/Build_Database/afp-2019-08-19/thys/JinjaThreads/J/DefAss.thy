(*  Title:      JinjaThreads/J/DefAss.thy
    Author:     Tobias Nipkow, Andreas Lochbihler
*)

section \<open>Definite assignment\<close>

theory DefAss
imports 
  Expr
begin

subsection "Hypersets"

type_synonym 'a hyperset = "'a set option"

definition hyperUn :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<squnion>" 65)
where
  "A \<squnion> B  \<equiv>  case A of None \<Rightarrow> None
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> None | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<union> B\<rfloor>)"

definition hyperInt :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> 'a hyperset"   (infixl "\<sqinter>" 70)
where
  "A \<sqinter> B  \<equiv>  case A of None \<Rightarrow> B
                 | \<lfloor>A\<rfloor> \<Rightarrow> (case B of None \<Rightarrow> \<lfloor>A\<rfloor> | \<lfloor>B\<rfloor> \<Rightarrow> \<lfloor>A \<inter> B\<rfloor>)"

definition hyperDiff1 :: "'a hyperset \<Rightarrow> 'a \<Rightarrow> 'a hyperset"   (infixl "\<ominus>" 65)
where
  "A \<ominus> a  \<equiv>  case A of None \<Rightarrow> None | \<lfloor>A\<rfloor> \<Rightarrow> \<lfloor>A - {a}\<rfloor>"

definition hyper_isin :: "'a \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<in>\<in>" 50)
where
 "a \<in>\<in> A  \<equiv>  case A of None \<Rightarrow> True | \<lfloor>A\<rfloor> \<Rightarrow> a \<in> A"

definition hyper_subset :: "'a hyperset \<Rightarrow> 'a hyperset \<Rightarrow> bool"   (infix "\<sqsubseteq>" 50)
where
  "A \<sqsubseteq> B  \<equiv>  case B of None \<Rightarrow> True
                 | \<lfloor>B\<rfloor> \<Rightarrow> (case A of None \<Rightarrow> False | \<lfloor>A\<rfloor> \<Rightarrow> A \<subseteq> B)"

lemmas hyperset_defs =
 hyperUn_def hyperInt_def hyperDiff1_def hyper_isin_def hyper_subset_def

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> A = A  \<and>  A \<squnion> \<lfloor>{}\<rfloor> = A"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "\<lfloor>A\<rfloor> \<squnion> \<lfloor>B\<rfloor> = \<lfloor>A \<union> B\<rfloor> \<and> \<lfloor>A\<rfloor> \<ominus> a = \<lfloor>A - {a}\<rfloor>"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "None \<squnion> A = None \<and> A \<squnion> None = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma [simp]: "a \<in>\<in> None \<and> None \<ominus> a = None"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma hyperUn_assoc: "(A \<squnion> B) \<squnion> C = A \<squnion> (B \<squnion> C)"
(*<*)by(simp add:hyperset_defs Un_assoc)(*>*)

lemma hyper_insert_comm: "A \<squnion> \<lfloor>{a}\<rfloor> = \<lfloor>{a}\<rfloor> \<squnion> A \<and> A \<squnion> (\<lfloor>{a}\<rfloor> \<squnion> B) = \<lfloor>{a}\<rfloor> \<squnion> (A \<squnion> B)"
(*<*)by(simp add:hyperset_defs)(*>*)

lemma sqSub_mem_lem [elim]: "\<lbrakk> A \<sqsubseteq> A'; a \<in>\<in> A \<rbrakk> \<Longrightarrow> a \<in>\<in> A'"
by(auto simp add: hyperset_defs)

lemma [iff]: "A \<sqsubseteq> None"
by(auto simp add: hyperset_defs)

lemma [simp]: "A \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma [iff]: "\<lfloor>A\<rfloor> \<sqsubseteq> \<lfloor>B\<rfloor> \<longleftrightarrow> A \<subseteq> B"
by(auto simp add: hyperset_defs)

lemma sqUn_lem2: "A \<sqsubseteq> A' \<Longrightarrow> B \<squnion> A \<sqsubseteq> B \<squnion> A'"
by(simp add:hyperset_defs) blast

lemma sqSub_trans [trans, intro]: "\<lbrakk> A \<sqsubseteq> B; B \<sqsubseteq> C \<rbrakk> \<Longrightarrow> A \<sqsubseteq> C"
by(auto simp add: hyperset_defs)

lemma hyperUn_comm: "A \<squnion> B = B \<squnion> A"
by(auto simp add: hyperset_defs)

lemma hyperUn_leftComm: "A \<squnion> (B \<squnion> C) = B \<squnion> (A \<squnion> C)"
by(auto simp add: hyperset_defs)

lemmas hyperUn_ac = hyperUn_comm hyperUn_leftComm hyperUn_assoc

lemma [simp]: "\<lfloor>{}\<rfloor> \<squnion> B = B"
by(auto)

lemma [simp]: "\<lfloor>{}\<rfloor> \<sqsubseteq> A"
by(auto simp add: hyperset_defs)

lemma sqInt_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<sqinter> B \<sqsubseteq> A' \<sqinter> B"
by(auto simp add: hyperset_defs)

subsection "Definite assignment"

primrec \<A>  :: "('a,'b,'addr) exp \<Rightarrow> 'a hyperset"
  and \<A>s :: "('a,'b,'addr) exp list \<Rightarrow> 'a hyperset"
where
  "\<A> (new C) = \<lfloor>{}\<rfloor>"
| "\<A> (newA T\<lfloor>e\<rceil>) = \<A> e"
| "\<A> (Cast C e) = \<A> e"
| "\<A> (e instanceof T) = \<A> e"
| "\<A> (Val v) = \<lfloor>{}\<rfloor>"
| "\<A> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (Var V) = \<lfloor>{}\<rfloor>"
| "\<A> (LAss V e) = \<lfloor>{V}\<rfloor> \<squnion> \<A> e"
| "\<A> (a\<lfloor>i\<rceil>) = \<A> a \<squnion> \<A> i"
| "\<A> (a\<lfloor>i\<rceil> := e) = \<A> a \<squnion> \<A> i \<squnion> \<A> e"
| "\<A> (a\<bullet>length) = \<A> a"
| "\<A> (e\<bullet>F{D}) = \<A> e"
| "\<A> (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) = \<A> e1 \<squnion> \<A> e2 \<squnion> \<A> e3"
| "\<A> (e\<bullet>M(es)) = \<A> e \<squnion> \<A>s es"
| "\<A> ({V:T=vo; e}) = \<A> e \<ominus> V"
| "\<A> (sync\<^bsub>V\<^esub> (o') e) = \<A> o' \<squnion> \<A> e"
| "\<A> (insync\<^bsub>V\<^esub> (a) e) = \<A> e"
| "\<A> (e\<^sub>1;;e\<^sub>2) = \<A> e\<^sub>1 \<squnion> \<A> e\<^sub>2"
| "\<A> (if (e) e\<^sub>1 else e\<^sub>2) =  \<A> e \<squnion> (\<A> e\<^sub>1 \<sqinter> \<A> e\<^sub>2)"
| "\<A> (while (b) e) = \<A> b"
| "\<A> (throw e) = None"
| "\<A> (try e\<^sub>1 catch(C V) e\<^sub>2) = \<A> e\<^sub>1 \<sqinter> (\<A> e\<^sub>2 \<ominus> V)"

| "\<A>s ([]) = \<lfloor>{}\<rfloor>"
| "\<A>s (e#es) = \<A> e \<squnion> \<A>s es"

primrec \<D>  :: "('a,'b,'addr) exp \<Rightarrow> 'a hyperset \<Rightarrow> bool"
  and \<D>s :: "('a,'b,'addr) exp list \<Rightarrow> 'a hyperset \<Rightarrow> bool"
where
  "\<D> (new C) A = True"
| "\<D> (newA T\<lfloor>e\<rceil>) A = \<D> e A"
| "\<D> (Cast C e) A = \<D> e A"
| "\<D> (e instanceof T) = \<D> e"
| "\<D> (Val v) A = True"
| "\<D> (e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (Var V) A = (V \<in>\<in> A)"
| "\<D> (LAss V e) A = \<D> e A"
| "\<D> (a\<lfloor>i\<rceil>) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a))"
| "\<D> (a\<lfloor>i\<rceil> := e) A = (\<D> a A \<and> \<D> i (A \<squnion> \<A> a) \<and> \<D> e (A \<squnion> \<A> a \<squnion> \<A> i))"
| "\<D> (a\<bullet>length) A = \<D> a A"
| "\<D> (e\<bullet>F{D}) A = \<D> e A"
| "\<D> (e\<^sub>1\<bullet>F{D}:=e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (e1\<bullet>compareAndSwap(D\<bullet>F, e2, e3)) A = (\<D> e1 A \<and> \<D> e2 (A \<squnion> \<A> e1) \<and> \<D> e3 (A \<squnion> \<A> e1 \<squnion> \<A> e2))"
| "\<D> (e\<bullet>M(es)) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"
| "\<D> ({V:T=vo; e}) A = (if vo = None then \<D> e (A \<ominus> V) else \<D> e (A \<squnion> \<lfloor>{V}\<rfloor>))"
| "\<D> (sync\<^bsub>V\<^esub> (o') e) A = (\<D> o' A \<and> \<D> e (A \<squnion> \<A> o'))"
| "\<D> (insync\<^bsub>V\<^esub> (a) e) A = \<D> e A"
| "\<D> (e\<^sub>1;;e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e\<^sub>1))"
| "\<D> (if (e) e\<^sub>1 else e\<^sub>2) A = (\<D> e A \<and> \<D> e\<^sub>1 (A \<squnion> \<A> e) \<and> \<D> e\<^sub>2 (A \<squnion> \<A> e))"
| "\<D> (while (e) c) A = (\<D> e A \<and> \<D> c (A \<squnion> \<A> e))"
| "\<D> (throw e) A = \<D> e A"
| "\<D> (try e\<^sub>1 catch(C V) e\<^sub>2) A = (\<D> e\<^sub>1 A \<and> \<D> e\<^sub>2 (A \<squnion> \<lfloor>{V}\<rfloor>))"

| "\<D>s ([]) A = True"
| "\<D>s (e#es) A = (\<D> e A \<and> \<D>s es (A \<squnion> \<A> e))"

lemma As_map_Val[simp]: "\<A>s (map Val vs) = \<lfloor>{}\<rfloor>"
(*<*)by (induct vs) simp_all(*>*)

lemma As_append [simp]: "\<A>s (xs @ ys) = (\<A>s xs) \<squnion> (\<A>s ys)"
by(induct xs, auto simp add: hyperset_defs)

lemma Ds_map_Val[simp]: "\<D>s (map Val vs) A"
(*<*)by (induct vs) simp_all(*>*)

lemma D_append[iff]: "\<And>A. \<D>s (es @ es') A = (\<D>s es A \<and> \<D>s es' (A \<squnion> \<A>s es))"
(*<*)by (induct es type:list) (auto simp:hyperUn_assoc)(*>*)


lemma fixes e :: "('a,'b,'addr) exp" and es :: "('a,'b,'addr) exp list"
  shows A_fv: "\<And>A. \<A> e = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fv e"
  and  "\<And>A. \<A>s es = \<lfloor>A\<rfloor> \<Longrightarrow> A \<subseteq> fvs es"
apply(induct e and es rule: \<A>.induct \<A>s.induct)
apply (simp_all add:hyperset_defs)
apply fast+
done


lemma sqUn_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<squnion> B \<sqsubseteq> A' \<squnion> B"
(*<*)by(simp add:hyperset_defs) blast(*>*)

lemma diff_lem: "A \<sqsubseteq> A' \<Longrightarrow> A \<ominus> b \<sqsubseteq> A' \<ominus> b"
(*<*)by(simp add:hyperset_defs) blast(*>*)

(* This order of the premises avoids looping of the simplifier *)
lemma fixes e :: "('a, 'b, 'addr) exp" and es :: "('a, 'b, 'addr) exp list"
  shows D_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D> e A \<Longrightarrow> \<D> e A'"
  and Ds_mono: "\<And>A A'. A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A \<Longrightarrow> \<D>s es A'"
(*<*)
apply(induct e and es rule: \<D>.induct \<D>s.induct)
subgoal by simp
subgoal by simp
subgoal by simp
subgoal by simp
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
subgoal by(fastforce simp add:hyperset_defs)
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp (iprover dest: sqUn_lem)
subgoal 
  apply(clarsimp split: if_split_asm) 
  apply (iprover dest:diff_lem) 
  apply(iprover dest: sqUn_lem)
  done
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
subgoal by simp
subgoal by simp (iprover dest:sqUn_lem)
done
(*>*)

(* And this is the order of premises preferred during application: *)
lemma D_mono': "\<D> e A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D> e A'"
and Ds_mono': "\<D>s es A \<Longrightarrow> A \<sqsubseteq> A' \<Longrightarrow> \<D>s es A'"
(*<*)by(blast intro:D_mono, blast intro:Ds_mono)(*>*)

declare hyperUn_comm [simp]
declare hyperUn_leftComm [simp]

end
