(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory MapOps
imports Main
begin
(*>*)

subsection\<open>Finite map operations\<close>

text\<open>

\label{sec:kbps-theory-map-ops}

The algorithm represents an automaton as a pair of maps, which we
capture abstractly with a record and a predicate:

\<close>

record ('m, 'k, 'e) MapOps =
  empty :: "'m"
  lookup :: "'m \<Rightarrow> 'k \<rightharpoonup> 'e"
  update :: "'k \<Rightarrow> 'e \<Rightarrow> 'm \<Rightarrow> 'm"

definition
  MapOps :: "('k \<Rightarrow> 'kabs) \<Rightarrow> 'kabs set \<Rightarrow> ('m, 'k, 'e) MapOps \<Rightarrow> bool"
where
  "MapOps \<alpha> d ops \<equiv>
      (\<forall>k. \<alpha> k \<in> d \<longrightarrow> lookup ops (empty ops) k = None)
    \<and> (\<forall>e k k' M. \<alpha> k \<in> d \<and> \<alpha> k' \<in> d
        \<longrightarrow> lookup ops (update ops k e M) k'
          = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k'))"
(*<*)

lemma MapOpsI[intro]:
  "\<lbrakk> \<And>k. \<alpha> k \<in> d \<Longrightarrow> lookup ops (empty ops) k = None;
     \<And>e k k' M. \<lbrakk> \<alpha> k \<in> d; \<alpha> k' \<in> d \<rbrakk> \<Longrightarrow>
                 lookup ops (update ops k e M) k'
              = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k') \<rbrakk>
     \<Longrightarrow> MapOps \<alpha> d ops"
  unfolding MapOps_def by blast

lemma MapOps_emptyD:
  "\<lbrakk> \<alpha> k \<in> d; MapOps \<alpha> d ops \<rbrakk> \<Longrightarrow> lookup ops (empty ops) k = None"
  unfolding MapOps_def by simp

lemma MapOps_lookup_updateD:
  "\<lbrakk> \<alpha> k \<in> d; \<alpha> k' \<in> d; MapOps \<alpha> d ops \<rbrakk> \<Longrightarrow> lookup ops (update ops k e M) k' = (if \<alpha> k' = \<alpha> k then Some e else lookup ops M k')"
  unfolding MapOps_def by simp

(*>*)

text\<open>

The function @{term "\<alpha>"} abstracts concrete keys of type @{typ "'k"},
and the parameter @{term "d"} specifies the valid abstract keys.

This approach has the advantage over a locale that we can pass records
to functions, while for a locale we would need to pass the three
functions separately (as in the DFS theory of \S\ref{sec:dfs}).

We use the following function to test for membership in the domain of
the map:

\<close>

definition isSome :: "'a option \<Rightarrow> bool" where
  "isSome opt \<equiv> case opt of None \<Rightarrow> False | Some _ \<Rightarrow> True"
(*<*)

lemma isSome_simps[simp]:
  "\<And>x. isSome (Some x)"
  "\<And>x. \<not> isSome x \<longleftrightarrow> x = None"
  unfolding isSome_def by (auto split: option.split)

lemma isSome_eq:
  "isSome x \<longleftrightarrow> (\<exists>y. x = Some y)"
  unfolding isSome_def by (auto split: option.split)

lemma isSomeE: "\<lbrakk> isSome x; \<And>s. x = Some s \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding isSome_def by (cases x) auto

end
(*>*)
