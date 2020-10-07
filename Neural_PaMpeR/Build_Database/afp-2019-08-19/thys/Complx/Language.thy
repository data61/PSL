(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

section \<open>The COMPLX Syntax\<close>

theory Language
imports Main
begin

subsection \<open>The Core Language\<close>

text \<open>We use a shallow embedding of boolean expressions as well as assertions
as sets of states. 
\<close>

type_synonym 's bexp = "'s set"
type_synonym 's assn = "'s set"

datatype ('s, 'p, 'f) com =
    Skip
  | Basic "'s \<Rightarrow> 's"
  | Spec "('s \<times> 's) set"
  | Seq "('s ,'p, 'f) com" "('s,'p, 'f) com"    
  | Cond "'s bexp" "('s,'p,'f) com"  "('s,'p,'f) com"
  | While "'s bexp" "('s,'p,'f) com"
  | Call "'p"
  | DynCom "'s \<Rightarrow> ('s,'p,'f) com" 
  | Guard "'f" "'s bexp" "('s,'p,'f) com" 
  | Throw
  | Catch "('s,'p,'f) com" "('s,'p,'f) com"
  | Parallel "('s, 'p, 'f) com list"
  | Await "'s bexp" "('s,'p,'f) com"


subsection \<open>Derived Language Constructs\<close>

text \<open>We inherit the remainder of derived language constructs from SIMPL\<close>

definition
  raise:: "('s \<Rightarrow> 's) \<Rightarrow> ('s,'p,'f) com" where
  "raise f = Seq (Basic f) Throw"

definition
  condCatch:: "('s,'p,'f) com \<Rightarrow> 's bexp \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "condCatch c\<^sub>1 b c\<^sub>2 = Catch c\<^sub>1 (Cond b c\<^sub>2 Throw)"

definition
  bind:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "bind e c = DynCom (\<lambda>s. c (e s))"

definition
  bseq:: "('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "bseq = Seq"
 
definition
  block:: "['s\<Rightarrow>'s ,('s,'p,'f) com,'s\<Rightarrow>'s\<Rightarrow>'s,'s\<Rightarrow>'s\<Rightarrow>('s,'p,'f) com]\<Rightarrow>('s,'p,'f) com"
where
  "block init bdy restore return =
    DynCom (\<lambda>s. (Seq (Catch (Seq (Basic init) bdy) (Seq (Basic (restore s)) Throw)) 
                            (DynCom (\<lambda>t. Seq (Basic (restore s)) (return s t))))
                        )" 

definition
  call:: "('s\<Rightarrow>'s) \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow>('s\<Rightarrow>'s\<Rightarrow>('s,'p,'f) com)\<Rightarrow>('s,'p,'f)com" where
  "call init p restore return = block init (Call p) restore return"

definition
  dynCall:: "('s\<Rightarrow>'s) \<Rightarrow> ('s \<Rightarrow> 'p) \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow>
             ('s \<Rightarrow> 's \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "dynCall init p restore return = DynCom (\<lambda>s. call init (p s) restore return)"

definition
  fcall:: "('s\<Rightarrow>'s) \<Rightarrow> 'p \<Rightarrow> ('s \<Rightarrow> 's \<Rightarrow> 's)\<Rightarrow>('s \<Rightarrow> 'v) \<Rightarrow> ('v\<Rightarrow>('s,'p,'f) com)
            \<Rightarrow>('s,'p,'f) com" where
  "fcall init p restore result return = call init p restore (\<lambda>s t. return (result t))"

definition
  lem:: "'x \<Rightarrow> ('s,'p,'f)com \<Rightarrow>('s,'p,'f)com" where
  "lem x c = c"

primrec switch:: "('s \<Rightarrow> 'v) \<Rightarrow> ('v set \<times> ('s,'p,'f) com) list \<Rightarrow> ('s,'p,'f) com" 
where
"switch v [] = Skip" |
"switch v (Vc#vs) = Cond {s. v s \<in> fst Vc} (snd Vc) (switch v vs)"

definition guaranteeStrip:: "'f \<Rightarrow> 's set \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
  where "guaranteeStrip f g c = Guard f g c"

definition guaranteeStripPair:: "'f \<Rightarrow> 's set \<Rightarrow> ('f \<times> 's set)"
  where "guaranteeStripPair f g = (f,g)"

primrec guards:: "('f \<times> 's set ) list \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com"
where
"guards [] c = c" |
"guards (g#gs) c = Guard (fst g) (snd g) (guards gs c)"

definition
  while::  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s, 'p, 'f) com"
where
  "while gs b c = guards gs (While b (Seq c (guards gs Skip)))"

definition
  whileAnno:: 
  "'s bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "whileAnno b I V c = While b c"

definition
  whileAnnoG:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> 's assn \<Rightarrow> ('s \<times> 's) assn \<Rightarrow> 
     ('s,'p,'f) com \<Rightarrow> ('s,'p,'f) com" where
  "whileAnnoG gs b I V c = while gs b c"
 
definition
  specAnno::  "('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> 
                         ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('s,'p,'f) com"
  where "specAnno P c Q A = (c undefined)"

definition
  whileAnnoFix:: 
  "'s bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> 
     ('s,'p,'f) com" where
  "whileAnnoFix b I V c = While b (c undefined)"

definition
  whileAnnoGFix:: 
  "('f \<times> 's set) list \<Rightarrow> 's bexp \<Rightarrow> ('a \<Rightarrow> 's assn) \<Rightarrow> ('a \<Rightarrow> ('s \<times> 's) assn) \<Rightarrow> 
     ('a \<Rightarrow> ('s,'p,'f) com) \<Rightarrow> ('s,'p,'f) com" where
  "whileAnnoGFix gs b I V c = while gs b (c undefined)"

definition if_rel::"('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> ('s \<times> 's) set" 
  where "if_rel b f g h = {(s,t). if b s then t = f s else t = g s \<or> t = h s}"

lemma fst_guaranteeStripPair: "fst (guaranteeStripPair f g) = f"
  by (simp add: guaranteeStripPair_def)

lemma snd_guaranteeStripPair: "snd (guaranteeStripPair f g) = g"
  by (simp add: guaranteeStripPair_def)

end
