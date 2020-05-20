(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/Atoms.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Atoms.thy 132773 2016-12-09 15:30:22Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Atomic messages for L1-L2 protocols

  Copyright (c) 2009-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Atomic messages\<close>

theory Atoms imports Keys
begin

(******************************************************************************)
subsection \<open>Atoms datatype\<close>
(******************************************************************************)

datatype atom =
  aAgt "agent" 
| aNon "nonce"
| aKey "key"
| aNum "nat" 


(******************************************************************************)
subsection \<open>Long-term key setup (abstractly)\<close>
(******************************************************************************)

text \<open>Suppose an initial long-term key setup without looking into the 
structure of long-term keys. 

Remark: This setup is agnostic with respect to the structure of the
type @{typ "ltkey"}. Ideally, the type @{typ "ltkey"} should be a
parameter of the type @{typ "key"}, which is instantiated only at
Level 3.\<close>

consts
  ltkeySetup :: "(ltkey \<times> agent) set"  \<comment> \<open>LT key setup, for now unspecified\<close>

text \<open>The initial key setup contains static, long-term keys.\<close>

definition
  keySetup :: "(key \<times> agent) set" where
  "keySetup \<equiv> {(ltK K, A) | K A. (K, A) \<in> ltkeySetup}"


text \<open>Corrupted keys are the long-term keys known by bad agents.\<close>

definition
  corrKey :: "key set" where 
  "corrKey \<equiv> keySetup\<inverse> `` bad" 

lemma corrKey_Dom_keySetup [simp, intro]: "K \<in> corrKey \<Longrightarrow> K \<in> Domain keySetup"
by (auto simp add: corrKey_def)

lemma keySetup_noSessionKeys [simp]: "(sesK K, A) \<notin> keySetup"
by (simp add: keySetup_def)

lemma corrKey_noSessionKeys [simp]: "sesK K \<notin> corrKey"
by (auto simp add: keySetup_def corrKey_def)


end
