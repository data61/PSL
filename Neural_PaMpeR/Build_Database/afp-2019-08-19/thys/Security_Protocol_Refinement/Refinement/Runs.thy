(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/Runs.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Runs.thy 132773 2016-12-09 15:30:22Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Protocol runs: local state of executing protocol roles

  Copyright (c) 2010-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Protocol runs\<close>

theory Runs imports Atoms
begin


(******************************************************************************)
subsection \<open>Runs\<close>
(******************************************************************************)

text \<open>Define some typical roles.\<close>

datatype role_t = Init | Resp | Serv

fun 
  roleIdx :: "role_t \<Rightarrow> nat"
where
  "roleIdx Init = 0"
| "roleIdx Resp = 1"
| "roleIdx Serv = 2"


text \<open>The type of runs is a partial function from run identifiers to 
a triple consisting of a role, a list of agents, and a list of atomic messages 
recorded during the run's execution. 

The type of roles could be made a parameter for more flexibility.\<close>

type_synonym
  rid_t = "fid_t"

type_synonym
  runs_t = "rid_t \<rightharpoonup> role_t \<times> agent list \<times> atom list"


subsection \<open>Run abstraction\<close>
(******************************************************************************)

text \<open>Define a function that lifts a function on roles and atom lists 
to a function on runs.\<close>

definition 
  map_runs :: "([role_t, atom list] \<Rightarrow> atom list) \<Rightarrow> runs_t \<Rightarrow> runs_t"
where
  "map_runs h runz rid \<equiv> case runz rid of
     None \<Rightarrow> None
   | Some (rol, agts, al) \<Rightarrow> Some (rol, agts, h rol al)"

lemma map_runs_empty [simp]: "map_runs h Map.empty = Map.empty"
by (rule ext) (auto simp add: map_runs_def)

lemma map_runs_dom [simp]: "dom (map_runs h runz) = dom runz"
by (auto simp add: map_runs_def split: option.split_asm)

lemma map_runs_update [simp]:
  "map_runs h (runz(R \<mapsto> (rol, agts, al))) 
   = (map_runs h runz)(R \<mapsto> (rol, agts, h rol al))"
by (auto simp add: map_runs_def)



end
