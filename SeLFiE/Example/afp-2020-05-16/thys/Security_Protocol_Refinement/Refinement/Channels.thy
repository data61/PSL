(*******************************************************************************

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/Channels.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Channels.thy 132773 2016-12-09 15:30:22Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Channel messages for Level 2 protocols

  Copyright (c) 2009-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Channel Messages\<close>

theory Channels imports Atoms
begin

(******************************************************************************)
subsection \<open>Channel messages\<close>
(******************************************************************************)

datatype secprop = auth | confid

type_synonym 
  chtyp = "secprop set"

abbreviation 
  secure :: chtyp where
  "secure \<equiv> {auth, confid}"

datatype payload = Msg "atom list"
 
datatype chmsg = 
  StatCh "chtyp" "agent" "agent" "payload"
| DynCh "chtyp" "key" "payload" 


text \<open>Abbreviations for use in protocol defs\<close>

abbreviation 
  Insec :: "[agent, agent, payload] \<Rightarrow> chmsg" where
  "Insec \<equiv> StatCh {}"

abbreviation 
  Confid :: "[agent, agent, payload] \<Rightarrow> chmsg" where
  "Confid \<equiv> StatCh {confid}"

abbreviation 
  Auth :: "[agent, agent, payload] \<Rightarrow> chmsg" where
  "Auth \<equiv> StatCh {auth}"

abbreviation 
  Secure :: "[agent, agent, payload] \<Rightarrow> chmsg" where
  "Secure \<equiv> StatCh {auth, confid}"

abbreviation 
  dConfid :: "[key, payload] \<Rightarrow> chmsg" where
  "dConfid \<equiv> DynCh {confid}"

abbreviation 
  dAuth :: "[key, payload] \<Rightarrow> chmsg" where
  "dAuth \<equiv> DynCh {auth}"

abbreviation 
  dSecure :: "[key, payload] \<Rightarrow> chmsg" where
  "dSecure \<equiv> DynCh {auth, confid}"


(******************************************************************************)
subsection \<open>Keys used in dynamic channel messages\<close>
(******************************************************************************)

definition 
  keys_for :: "chmsg set \<Rightarrow> key set" where
  "keys_for H \<equiv> {K. \<exists>c M. DynCh c K M \<in> H}"

lemma keys_forI [dest]: "DynCh c K M \<in> H \<Longrightarrow> K \<in> keys_for H"
by (auto simp add: keys_for_def)


lemma keys_for_empty [simp]: "keys_for {} = {}"
by (simp add: keys_for_def)

lemma keys_for_monotone: "G \<subseteq> H \<Longrightarrow> keys_for G \<subseteq> keys_for H"
by (auto simp add: keys_for_def)

lemmas keys_for_mono [elim] = keys_for_monotone [THEN [2] rev_subsetD]


lemma keys_for_insert_StatCh [simp]: 
  "keys_for (insert (StatCh c A B M) H) = keys_for H"
by (auto simp add: keys_for_def)

lemma keys_for_insert_DynCh [simp]: 
  "keys_for (insert (DynCh c K M) H) = insert K (keys_for H)"
by (auto simp add: keys_for_def)


(******************************************************************************)
subsection \<open>Atoms in a set of channel messages\<close>
(******************************************************************************)

text \<open>The set of atoms contained in a set of channel messages. We also 
include the public atoms, i.e., the agent names, numbers, and corrupted keys. 
\<close>

inductive_set 
  atoms :: "chmsg set \<Rightarrow> atom set"
  for H :: "chmsg set"
where
  at_StatCh: "\<lbrakk> StatCh c A B (Msg M) \<in> H; At \<in> set M \<rbrakk> \<Longrightarrow> At \<in> atoms H"
| at_DynCh: "\<lbrakk> DynCh c K (Msg M) \<in> H; At \<in> set M \<rbrakk> \<Longrightarrow> At \<in> atoms H"

declare atoms.intros [intro]

lemma atoms_empty [simp]: "atoms {} = {}"
by (auto elim!: atoms.cases)

lemma atoms_monotone: "G \<subseteq> H \<Longrightarrow> atoms G \<subseteq> atoms H"
by (auto elim!: atoms.cases)

lemmas atoms_mono [elim] = atoms_monotone [THEN [2] rev_subsetD]


lemma atoms_insert_StatCh [simp]: 
  "atoms (insert (StatCh c A B (Msg M)) H) = set M \<union> atoms H"
by (auto elim!: atoms.cases)

lemma atoms_insert_DynCh [simp]: 
  "atoms (insert (DynCh c K (Msg M)) H) = set M \<union> atoms H"
by (auto elim!: atoms.cases)


(******************************************************************************)
subsection \<open>Intruder knowledge (atoms)\<close>
(******************************************************************************)

text \<open>Atoms that the intruder can extract from a set of channel messages.\<close>

inductive_set 
  extr :: "atom set \<Rightarrow> chmsg set \<Rightarrow> atom set"
  for T :: "atom set" 
  and H :: "chmsg set"
where 
  extr_Inj: "At \<in> T \<Longrightarrow> At \<in> extr T H"
| extr_StatCh: 
    "\<lbrakk> StatCh c A B (Msg M) \<in> H; At \<in> set M; confid \<notin> c \<or> A \<in> bad \<or> B \<in> bad \<rbrakk> 
   \<Longrightarrow> At \<in> extr T H"
| extr_DynCh: 
    "\<lbrakk> DynCh c K (Msg M) \<in> H; At \<in> set M; confid \<notin> c \<or> aKey K \<in> extr T H \<rbrakk> 
   \<Longrightarrow> At \<in> extr T H"

declare extr.intros [intro]
declare extr.cases [elim]


text\<open>Typical parameter describing initial intruder knowledge.\<close>

definition
  ik0 :: "atom set" where 
  "ik0 \<equiv> range aAgt \<union> range aNum \<union> aKey`corrKey"

lemma ik0_aAgt [iff]: "aAgt A \<in> ik0"
by (auto simp add: ik0_def)

lemma ik0_aNum [iff]: "aNum T \<in> ik0"
by (auto simp add: ik0_def)

lemma ik0_aNon [iff]: "aNon N \<notin> ik0"
by (auto simp add: ik0_def)

lemma ik0_aKey_corr [simp]: "(aKey K \<in> ik0) = (K \<in> corrKey)"
by (auto simp add: ik0_def)


subsubsection \<open>Basic lemmas\<close>
(******************************************************************************)

lemma extr_empty [simp]: "extr T {} = T"
by (auto)

lemma extr_monotone [dest]: "G \<subseteq> H \<Longrightarrow> extr T G \<subseteq> extr T H"
by (safe, erule extr.induct, auto)

lemmas extr_mono [elim] = extr_monotone [THEN [2] rev_subsetD]

lemma extr_monotone_param [dest]: "T \<subseteq> U \<Longrightarrow> extr T H \<subseteq> extr U H"
by (safe, erule extr.induct, auto)

lemmas extr_mono_param [elim] = extr_monotone_param [THEN [2] rev_subsetD]

lemma extr_insert [intro]: "At \<in> extr T H \<Longrightarrow> At \<in> extr T (insert C H)"
by (erule extr_mono) (auto)

lemma extr_into_atoms [dest]: "At \<in> extr T H \<Longrightarrow> At \<in> T \<union> atoms H"
by (erule extr.induct, auto)


subsubsection \<open>Insertion lemmas for atom parameters\<close>
(******************************************************************************)

lemma extr_insert_non_key_param [simp]:
  assumes "At \<in> range aNon \<union> range aAgt \<union> range aNum"
  shows "extr (insert At T) H = insert At (extr T H)"
proof -
  { fix Bt
    assume "Bt \<in> extr (insert At T) H"
    hence "Bt \<in> insert At (extr T H)" 
      using assms by induct auto
  }
  thus ?thesis by auto
qed

lemma extr_insert_unused_key_param [simp]:
  assumes "K \<notin> keys_for H"
  shows "extr (insert (aKey K) T) H = insert (aKey K) (extr T H)"
proof -
  { fix At
    assume "At \<in> extr (insert (aKey K) T) H"
    hence "At \<in> insert (aKey K) (extr T H)" 
      using assms by induct (auto simp add: keys_for_def)
  }
  thus ?thesis by auto
qed



subsubsection \<open>Insertion lemmas for each type of channel message\<close>
(******************************************************************************)

text \<open>Note that the parameter accumulates the extracted atoms. In particular, 
these may include keys that may open further dynamically confidential messages. 
\<close>

lemma extr_insert_StatCh [simp]: 
  "extr T (insert (StatCh c A B (Msg M)) H) 
   = (if confid \<notin> c \<or> A \<in> bad \<or> B \<in> bad then extr (set M \<union> T) H else extr T H)"
proof (cases "confid \<notin> c \<or> A \<in> bad \<or> B \<in> bad")
  case True
  moreover 
  {
    fix At
    assume "At \<in> extr T (insert (StatCh c A B (Msg M)) H)"
    hence "At \<in> extr (set M \<union> T) H" by induct auto
  }
  moreover
  {
    fix At
    assume "At \<in> extr (set M \<union> T) H" 
    and    "confid \<notin> c \<or> A \<in> bad \<or> B \<in> bad"
    hence "At \<in> extr T (insert (StatCh c A B (Msg M)) H)" by induct auto
  }
  ultimately show ?thesis by auto
next 
  case False
  moreover
  {
    fix At
    assume "At \<in> extr T (insert (StatCh c A B (Msg M)) H)"
    and "confid \<in> c" "A \<notin> bad" "B \<notin> bad"
    hence "At \<in> extr T H" by induct auto
  }
  ultimately show ?thesis by auto
qed

lemma extr_insert_DynCh [simp]: 
  "extr T (insert (DynCh c K (Msg M)) H) 
   = (if confid \<notin> c \<or> aKey K \<in> extr T H then extr (set M \<union> T) H else extr T H)"
proof (cases "confid \<notin> c \<or> aKey K \<in> extr T H")
  case True
  moreover
  {
    fix At
    assume "At \<in> extr T (insert (DynCh c K (Msg M)) H)"
    hence "At \<in> extr (set M \<union> T) H" by induct auto
  }
  moreover
  {
    fix At
    assume "At \<in> extr (set M \<union> T) H"
    hence "At \<in> extr T (insert (DynCh c K (Msg M)) H)" 
      using True by induct auto
  }
  ultimately show ?thesis by auto
next
  case False
  moreover
  hence "extr T (insert (DynCh c K (Msg M)) H) = extr T H" 
    by (intro equalityI subsetI) (erule extr.induct, auto)+
  ultimately show ?thesis by auto
qed


declare extr.cases [rule del, elim]


(******************************************************************************)
subsection \<open>Faking messages\<close>
(******************************************************************************)

text \<open>Channel messages that are fakeable from a given set of channel
messages.  Parameters are a set of atoms and a set of freshness identifiers.

For faking messages on dynamic non-authentic channels, we cannot allow the
intruder to use arbitrary keys. Otherwise, we would lose the possibility to 
generate fresh values in our model. Therefore, the chosen keys must correspond
to session keys associated with existing runs (i.e., from set 
@{term "rkeys U"}).
\<close>

abbreviation 
  rkeys :: "fid_t set \<Rightarrow> key set" where
  "rkeys U \<equiv> sesK`(\<lambda>(x, y). x $ y)`(U \<times> (UNIV::nat set))"

lemma rkeys_sesK [simp, dest]: "sesK (R$i) \<in> rkeys U \<Longrightarrow> R \<in> U"
by (auto simp add: image_def)


inductive_set 
  fake :: "atom set \<Rightarrow> fid_t set \<Rightarrow> chmsg set \<Rightarrow> chmsg set"
  for T :: "atom set"
  and U :: "fid_t set"
  and H :: "chmsg set"
where 
  fake_Inj:
    "M \<in> H \<Longrightarrow> M \<in> fake T U H"
| fake_StatCh: 
    "\<lbrakk> set M \<subseteq> extr T H; auth \<notin> c \<or> A \<in> bad \<or> B \<in> bad  \<rbrakk> 
   \<Longrightarrow> StatCh c A B (Msg M) \<in> fake T U H"
| fake_DynCh:  
    "\<lbrakk> set M \<subseteq> extr T H; auth \<notin> c \<and> K \<in> rkeys U \<or> aKey K \<in> extr T H \<rbrakk> 
   \<Longrightarrow> DynCh c K (Msg M) \<in> fake T U H"

declare fake.cases [elim]
declare fake.intros [intro]

lemmas fake_intros = fake_StatCh fake_DynCh

lemma fake_expanding [intro]: "H \<subseteq> fake T U H"
by (auto)

lemma fake_monotone [intro]: "G \<subseteq> H \<Longrightarrow> fake T U G \<subseteq> fake T U H"
by (safe, erule fake.cases, auto intro!: fake_intros)

lemma fake_monotone_param1 [intro]: 
  "T \<subseteq> T' \<Longrightarrow> fake T U H \<subseteq> fake T' U H" 
by (safe, erule fake.cases, auto intro!: fake_intros)

lemmas fake_mono [elim] = fake_monotone [THEN [2] rev_subsetD]
lemmas fake_mono_param1 [elim] = fake_monotone_param1 [THEN [2] rev_subsetD]


subsubsection \<open>Atoms and extr together with fake\<close>
(******************************************************************************)

lemma atoms_fake [simp]: "atoms (fake T U H) = T \<union> atoms H"
proof -
  {
    fix At 
    assume "At \<in> T"
    hence "At \<in> atoms (fake T U H)"
    proof -
      {
        fix A B 
        have "Insec A B (Msg [At]) \<in> fake T U H" using \<open>At \<in> T\<close>
        by (intro fake_StatCh) (auto)
      }
      thus ?thesis by (intro at_StatCh) (auto)
    qed
  }
  moreover
  {
    fix At
    assume "At \<in> atoms (fake T U H) "
    hence "At \<in> T \<union> atoms H" by cases blast+
  }
  ultimately show ?thesis by auto
qed


lemma extr_fake [simp]: 
  assumes "T' \<subseteq> T" shows "extr T (fake T' U H) = extr T H"
proof (intro equalityI subsetI) 
  fix At
  assume "At \<in> extr T (fake T' U H)"
  with assms have "At \<in> extr T (fake T U H)" by auto
  thus "At \<in> extr T H" by induct auto
qed auto

(*
lemma extr_fake [simp]: "extr T (fake T U H) = extr T H"
proof -
  {
    fix At
    assume "At \<in> extr T (fake T U H)"
    hence "At \<in> extr T H" by induct auto
  }
  thus ?thesis by auto
qed
*)

end
