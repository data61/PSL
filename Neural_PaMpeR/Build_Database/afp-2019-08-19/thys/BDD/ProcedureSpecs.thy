(*  Title:       BDD
    Author:      Veronika Ortner and Norbert Schirmer, 2004
    Maintainer:  Norbert Schirmer,  norbert.schirmer at web de
    License:     LGPL
*)

(*  
ProcedureSpecs.thy

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

section \<open>Definitions of Procedures\<close>
theory ProcedureSpecs
imports General Simpl.Vcg
begin

record "globals" =
  var_' :: "ref \<Rightarrow> nat"
  low_' :: "ref \<Rightarrow> ref"
  high_' :: "ref \<Rightarrow> ref"
  rep_' :: "ref \<Rightarrow> ref"
  mark_' :: "ref \<Rightarrow> bool"
  next_' ::"ref \<Rightarrow> ref"


record 'g bdd_state = "'g state" +
  varval_' :: "bool list"
  p_' :: "ref"
  R_' :: "bool"
  levellist_' :: "ref list"
  nodeslist_' :: "ref"
  node_':: "ref"
  m_' :: "bool"
  n_' :: "nat"


(*Evaluation even of unsymmetric dags. 
If a child is unexpectedly Null Eval returns False*)


procedures
  Eval (p, varval | R) = 
    "IF (\<acute>p\<rightarrow>\<acute>var = 0) THEN \<acute>R :==False
     ELSE IF (\<acute>p\<rightarrow>\<acute>var = 1) THEN \<acute>R :==True
       ELSE IF (\<acute>varval ! (\<acute>p\<rightarrow>\<acute>var)) THEN CALL Eval (\<acute>p\<rightarrow>\<acute>high, \<acute>varval, \<acute>R)
         ELSE CALL Eval (\<acute>p\<rightarrow>\<acute>low, \<acute>varval, \<acute>R)
         FI
       FI
     FI"
  


procedures 
  Levellist (p, m, levellist | levellist) = 
    "IF (\<acute>p \<noteq> Null) 
     THEN
       IF (\<acute>p \<rightarrow> \<acute>mark \<noteq> \<acute>m)
       THEN
         \<acute>levellist :== CALL Levellist ( \<acute>p \<rightarrow> \<acute>low, \<acute>m, \<acute>levellist );;
         \<acute>levellist :== CALL Levellist ( \<acute>p \<rightarrow> \<acute>high, \<acute>m, \<acute>levellist );;
         \<acute>p \<rightarrow> \<acute>next :== \<acute>levellist ! (\<acute>p\<rightarrow>\<acute>var);;
         \<acute>levellist ! (\<acute>p\<rightarrow>\<acute>var) :== \<acute>p;;
         \<acute>p \<rightarrow> \<acute>mark :==\<acute>m
       FI
     FI"


procedures
  ShareRep (nodeslist, p) =
  "IF (isLeaf_pt \<acute>p \<acute>low \<acute>high) 
   THEN \<acute>p \<rightarrow> \<acute>rep :== \<acute>nodeslist
   ELSE
        WHILE (\<acute>nodeslist \<noteq> Null) DO
          IF (repNodes_eq \<acute>nodeslist \<acute>p \<acute>low \<acute>high \<acute>rep)
          THEN \<acute>p\<rightarrow>\<acute>rep :== \<acute>nodeslist;; \<acute>nodeslist :== Null
          ELSE \<acute>nodeslist :== \<acute>nodeslist\<rightarrow>\<acute>next
          FI
        OD
   FI"



procedures
  ShareReduceRepList (nodeslist | ) =
  "\<acute>node :== \<acute>nodeslist;;
   WHILE (\<acute>node \<noteq> Null) DO
     IF (\<not> isLeaf_pt \<acute>node \<acute>low \<acute>high \<and> 
         \<acute>node \<rightarrow> \<acute>low \<rightarrow> \<acute>rep = \<acute>node \<rightarrow> \<acute>high \<rightarrow> \<acute>rep )
     THEN \<acute>node \<rightarrow> \<acute>rep :== \<acute>node \<rightarrow> \<acute>low \<rightarrow> \<acute>rep
     ELSE CALL ShareRep (\<acute>nodeslist , \<acute>node )  
     FI;;
     \<acute>node :==\<acute>node \<rightarrow> \<acute>next
   OD"


procedures 
  Repoint (p|p) = 
  "IF ( \<acute>p \<noteq> Null )
   THEN  
     \<acute>p :== \<acute>p \<rightarrow> \<acute>rep;;
     IF ( \<acute>p \<noteq> Null )
     THEN \<acute>p  \<rightarrow> \<acute>low :== CALL Repoint (\<acute>p  \<rightarrow> \<acute>low);;
          \<acute>p  \<rightarrow> \<acute>high :== CALL Repoint (\<acute>p \<rightarrow> \<acute>high)
     FI
   FI"


procedures 
  Normalize (p|p) =
  "\<acute>levellist :==replicate (\<acute>p\<rightarrow>\<acute>var +1) Null;;
    \<acute>levellist :== CALL Levellist (\<acute>p, (\<not> \<acute>p\<rightarrow>\<acute>mark) , \<acute>levellist);;
   (\<acute>n :==0;;
   WHILE (\<acute>n < length \<acute>levellist) DO
     CALL ShareReduceRepList(\<acute>levellist ! \<acute>n);;
     \<acute>n :==\<acute>n + 1
   OD);;
   \<acute>p :== CALL Repoint (\<acute>p)"

end
