(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Runs.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Runs.thy 132861 2016-12-21 10:34:41Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Defines types protocol runs: a run is described by a protocol role, the owner 
  and partner agents, and frame, which maps variables to messages. 

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Runs\<close>

theory Runs imports Messages
begin

subsection \<open>Type definitions\<close>


datatype role_t = Init | Resp 

datatype var = Var nat

type_synonym 
  rid_t = "fid_t"

type_synonym 
  frame = "var \<rightharpoonup> msg" 

record run_t = 
  role :: role_t
  owner :: agent
  partner :: agent

type_synonym
  progress_t = "rid_t \<rightharpoonup> var set" 


fun
  in_progress :: "var set option \<Rightarrow> var \<Rightarrow> bool"
where
  "in_progress (Some S) x = (x \<in> S)"
 |"in_progress None x = False"

fun
  in_progressS :: "var set option \<Rightarrow> var set \<Rightarrow> bool"
where
  "in_progressS (Some S) S' = (S' \<subseteq> S)"
 |"in_progressS None S' = False"

lemma in_progress_dom [elim]: "in_progress (r R) x \<Longrightarrow> R \<in> dom r"
by (cases "r R", auto)

lemma in_progress_Some [elim]: "in_progress r x \<Longrightarrow> \<exists> x. r = Some x"
by (cases "r", auto)

lemma in_progressS_elt [elim]: "in_progressS r S \<Longrightarrow> x \<in> S \<Longrightarrow> in_progress r x"
by (cases r, auto)


end
