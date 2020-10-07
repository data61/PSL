(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Messages.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Messages.thy 133008 2017-01-17 13:53:14Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Message datatype and quotient construction based on Diffie-Hellman 
  equational theory.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Message definitions\<close> 

theory Messages
imports Main
begin

(****************************************************************************************)
subsection \<open>Messages\<close>
(****************************************************************************************)

text \<open>Agents\<close>
datatype
  agent = Agent nat

text \<open>Nonces\<close>
typedecl fid_t

datatype fresh_t = 
  mk_fresh "fid_t" "nat"      (infixr "$" 65) 

fun fid :: "fresh_t \<Rightarrow> fid_t" where
  "fid (f $ n) = f"

fun num :: "fresh_t \<Rightarrow> nat" where
  "num (f $ n) = n"

datatype
  nonce_t =
    nonce_fresh "fresh_t"
  | nonce_atk "nat"


text \<open>Keys\<close>
datatype ltkey =
  sharK "agent" "agent"
| publK "agent"
| privK "agent"

datatype ephkey =
  epublK nonce_t
| eprivK nonce_t

datatype tag = insec | auth | confid | secure

text \<open>Messages\<close>

datatype cmsg =
  cAgent "agent"
| cNumber "nat"
| cNonce "nonce_t"
| cLtK "ltkey"
| cEphK "ephkey"
| cPair cmsg cmsg
| cEnc cmsg cmsg
| cAenc cmsg cmsg
| cSign cmsg cmsg
| cHash cmsg
| cTag tag
| cExp cmsg cmsg

fun catomic :: "cmsg \<Rightarrow> bool"
where
  "catomic (cAgent _) = True"
| "catomic (cNumber _) = True"
| "catomic (cNonce _) = True"
| "catomic (cLtK _) = True"
| "catomic (cEphK _) = True"
| "catomic (cTag _) = True"
|" catomic _ = False"


inductive eq :: "cmsg \<Rightarrow> cmsg \<Rightarrow> bool"
where
\<comment> \<open>equations\<close>
  Permute [intro]:"eq (cExp (cExp a b) c) (cExp (cExp a c) b)"
\<comment> \<open>closure by context\<close>
 | Tag[intro]: "eq (cTag t) (cTag t)"
 | Agent[intro]: "eq (cAgent A) (cAgent A)"
 | Nonce[intro]:"eq (cNonce x) (cNonce x)"
 | Number[intro]:"eq (cNumber x) (cNumber x)"
 | LtK[intro]:"eq (cLtK x) (cLtK x)"
 | EphK[intro]:"eq (cEphK x) (cEphK x)"
 | Pair[intro]:"eq a b \<Longrightarrow> eq c d \<Longrightarrow> eq (cPair a c) (cPair b d)"
 | Enc[intro]:"eq a b \<Longrightarrow> eq c d \<Longrightarrow> eq (cEnc a c) (cEnc b d)"
 | Aenc[intro]:"eq a b \<Longrightarrow> eq c d \<Longrightarrow> eq (cAenc a c) (cAenc b d)"
 | Sign[intro]:"eq a b \<Longrightarrow> eq c d \<Longrightarrow> eq (cSign a c) (cSign b d)"
 | Hash[intro]:"eq a b \<Longrightarrow> eq (cHash a) (cHash b)"
 | Exp[intro]:"eq a b \<Longrightarrow> eq c d \<Longrightarrow> eq (cExp a c) (cExp b d)"
\<comment> \<open>reflexive closure is not needed here because the context closure implies it\<close>
\<comment> \<open>symmetric closure is not needed as it is easier to include equations in both directions\<close>
\<comment> \<open>transitive closure\<close>
 | Tr[intro]: "eq a b \<Longrightarrow> eq b c \<Longrightarrow> eq a c"

lemma eq_sym: "eq a b \<longleftrightarrow> eq b a"
by (auto elim: eq.induct)

lemma eq_Sym [intro]: "eq a b \<Longrightarrow> eq b a"
by (auto elim: eq.induct)

lemma eq_refl [simp, intro]: "eq a a"
by (induction a, auto)

text \<open>inductive cases; keep the transitivity case, so we prove the the right lemmas by hand.\<close>
lemma eq_Number: "eq (cNumber N) y \<Longrightarrow>  y = cNumber N"
  by (induction "cNumber N" y rule: eq.induct, auto)
lemma eq_Agent: "eq (cAgent A) y \<Longrightarrow>  y = cAgent A"
  by (induction "cAgent A" y rule: eq.induct, auto)
lemma eq_Nonce: "eq (cNonce N) y \<Longrightarrow>  y = cNonce N"
  by (induction "cNonce N" y rule: eq.induct, auto)
lemma eq_LtK: "eq (cLtK N) y \<Longrightarrow>  y = cLtK N"
  by (induction "cLtK N" y rule: eq.induct, auto)
lemma eq_EphK: "eq (cEphK N) y \<Longrightarrow>  y = cEphK N"
  by (induction "cEphK N" y rule: eq.induct, auto)
lemma eq_Tag: "eq (cTag N) y \<Longrightarrow>  y = cTag N"
  by (induction "cTag N" y rule: eq.induct, auto)
lemma eq_Hash: "eq (cHash X) y \<Longrightarrow> \<exists>Y. y = cHash Y \<and> eq X Y"
  by (drule eq.induct [where P="\<lambda>x. \<lambda>y. \<forall> X. x = cHash X \<longrightarrow> (\<exists>Y. y = cHash Y \<and> eq X Y)"],
      auto elim!:Tr)
lemma eq_Pair: "eq (cPair X Y) y \<Longrightarrow>  \<exists> X' Y'. y = cPair X' Y' \<and> eq X X' \<and> eq Y Y'"
  apply (drule eq.induct [where 
    P="\<lambda>x. \<lambda>y. \<forall> X Y. x = cPair X Y \<longrightarrow> (\<exists> X' Y'. y = cPair X' Y' \<and> eq X X' \<and> eq Y Y')"])
  apply (auto elim!: Tr)
done
lemma eq_Enc: "eq (cEnc X Y) y \<Longrightarrow>  \<exists> X' Y'. y = cEnc X' Y' \<and> eq X X' \<and> eq Y Y'"
  apply (drule eq.induct [where 
    P="\<lambda>x. \<lambda>y. \<forall> X Y. x = cEnc X Y \<longrightarrow> (\<exists> X' Y'. y = cEnc X' Y' \<and> eq X X' \<and> eq Y Y')"])
  apply (auto elim!: Tr)
done
lemma eq_Aenc: "eq (cAenc X Y) y \<Longrightarrow>  \<exists> X' Y'. y = cAenc X' Y' \<and> eq X X' \<and> eq Y Y'"
  apply (drule eq.induct [where 
    P="\<lambda>x. \<lambda>y. \<forall> X Y. x = cAenc X Y \<longrightarrow> (\<exists> X' Y'. y = cAenc X' Y' \<and> eq X X' \<and> eq Y Y')"])
  apply (auto elim!: Tr)
done
lemma eq_Sign: "eq (cSign X Y) y \<Longrightarrow>  \<exists> X' Y'. y = cSign X' Y' \<and> eq X X' \<and> eq Y Y'"
  apply (drule eq.induct [where 
    P="\<lambda>x. \<lambda>y. \<forall> X Y. x = cSign X Y \<longrightarrow> (\<exists> X' Y'. y = cSign X' Y' \<and> eq X X' \<and> eq Y Y')"])
  apply (auto elim!: Tr)
done
lemma eq_Exp: "eq (cExp X Y) y \<Longrightarrow>  \<exists> X' Y'. y = cExp X' Y'"
  apply (drule eq.induct [where 
    P="\<lambda>x. \<lambda>y. \<forall> X Y. x = cExp X Y \<longrightarrow> (\<exists> X' Y'. y = cExp X' Y')"])
  apply (auto elim!: Tr)
done

lemmas eqD_aux = eq_Number eq_Agent eq_Nonce eq_LtK eq_EphK eq_Tag
                    eq_Hash eq_Pair eq_Enc eq_Aenc eq_Sign eq_Exp
lemmas eqD [dest] = eqD_aux eqD_aux [OF eq_Sym]


text \<open>Quotient construction\<close>

quotient_type msg = cmsg / eq
morphisms Re Ab
by (auto simp add:equivp_def)


lift_definition Number :: "nat \<Rightarrow> msg" is cNumber by -
lift_definition Nonce :: "nonce_t \<Rightarrow> msg" is cNonce by -
lift_definition Agent :: "agent \<Rightarrow> msg" is cAgent by -
lift_definition LtK :: "ltkey \<Rightarrow> msg" is cLtK by -
lift_definition EphK :: "ephkey \<Rightarrow> msg" is cEphK by -
lift_definition Pair :: "msg \<Rightarrow> msg \<Rightarrow> msg" is cPair by auto
lift_definition Enc :: "msg \<Rightarrow> msg \<Rightarrow> msg" is cEnc by auto
lift_definition Aenc :: "msg \<Rightarrow> msg \<Rightarrow> msg" is cAenc by auto
lift_definition Exp :: "msg \<Rightarrow> msg \<Rightarrow> msg" is cExp by auto
lift_definition Tag :: "tag \<Rightarrow> msg" is cTag by -
lift_definition Hash :: "msg \<Rightarrow> msg" is cHash by auto
lift_definition Sign :: "msg \<Rightarrow> msg \<Rightarrow> msg" is cSign by auto

lemmas msg_defs = 
  Agent_def Number_def Nonce_def LtK_def EphK_def Pair_def 
  Enc_def Aenc_def Exp_def Hash_def Tag_def Sign_def


text \<open>Commutativity of exponents\<close>

lemma permute_exp [simp]: "Exp (Exp X Y) Z = Exp (Exp X Z) Y"
by (transfer, auto)

lift_definition atomic :: "msg \<Rightarrow> bool" is catomic by (erule eq.induct, auto)

abbreviation 
  composed :: "msg \<Rightarrow> bool" where
  "composed X \<equiv> \<not>atomic X"

lemma atomic_Agent [simp, intro]: "atomic (Agent X)" by (transfer, auto)
lemma atomic_Tag [simp, intro]: "atomic (Tag X)" by (transfer, auto)
lemma atomic_Nonce [simp, intro]: "atomic (Nonce X)" by (transfer, auto)
lemma atomic_Number [simp, intro]: "atomic (Number X)" by (transfer, auto)
lemma atomic_LtK [simp, intro]: "atomic (LtK X)" by (transfer, auto)
lemma atomic_EphK [simp, intro]: "atomic (EphK X)" by (transfer, auto)

lemma non_atomic_Pair [simp]: "\<not>atomic (Pair x y)" by (transfer, auto)
lemma non_atomic_Enc [simp]: "\<not>atomic (Enc x y)" by (transfer, auto)
lemma non_atomic_Aenc [simp]: "\<not>atomic (Aenc x y)" by (transfer, auto)
lemma non_atomic_Sign [simp]: "\<not>atomic (Sign x y)" by (transfer, auto)
lemma non_atomic_Exp [simp]: "\<not>atomic (Exp x y)" by (transfer, auto)
lemma non_atomic_Hash [simp]: "\<not>atomic (Hash x)" by (transfer, auto)

lemma Nonce_Nonce: "(Nonce X = Nonce X') = (X = X')" by transfer auto
lemma Nonce_Agent: "Nonce X \<noteq> Agent X'" by transfer auto
lemma Nonce_Number: "Nonce X \<noteq> Number X'" by transfer auto
lemma Nonce_Hash: "Nonce X \<noteq> Hash  X'" by transfer auto
lemma Nonce_Tag: "Nonce X \<noteq> Tag  X'" by transfer auto
lemma Nonce_EphK: "Nonce X \<noteq> EphK  X'" by transfer auto
lemma Nonce_LtK: "Nonce X \<noteq> LtK  X'" by transfer auto
lemma Nonce_Pair: "Nonce X \<noteq> Pair  X' Y'" by transfer auto
lemma Nonce_Enc: "Nonce X \<noteq> Enc  X' Y'" by transfer auto
lemma Nonce_Aenc: "Nonce X \<noteq> Aenc  X' Y'" by transfer auto
lemma Nonce_Sign: "Nonce X \<noteq> Sign  X' Y'" by transfer auto
lemma Nonce_Exp: "Nonce X \<noteq> Exp  X' Y'" by transfer auto

lemma Agent_Nonce: "Agent X \<noteq> Nonce  X'" by transfer auto
lemma Agent_Agent: "(Agent X = Agent X') = (X = X')" by transfer auto
lemma Agent_Number: "Agent X \<noteq> Number  X'" by transfer auto
lemma Agent_Hash: "Agent X \<noteq> Hash  X'" by transfer auto
lemma Agent_Tag: "Agent X \<noteq> Tag  X'" by transfer auto
lemma Agent_EphK: "Agent X \<noteq> EphK  X'" by transfer auto
lemma Agent_LtK: "Agent X \<noteq> LtK  X'" by transfer auto
lemma Agent_Pair: "Agent X \<noteq> Pair  X' Y'" by transfer auto
lemma Agent_Enc: "Agent X \<noteq> Enc  X' Y'" by transfer auto
lemma Agent_Aenc: "Agent X \<noteq> Aenc  X' Y'" by transfer auto
lemma Agent_Sign: "Agent X \<noteq> Sign  X' Y'" by transfer auto
lemma Agent_Exp: "Agent X \<noteq> Exp  X' Y'" by transfer auto

lemma Number_Nonce: "Number X \<noteq> Nonce  X'" by transfer auto
lemma Number_Agent: "Number X \<noteq> Agent  X'" by transfer auto
lemma Number_Number: "(Number X = Number X') = (X = X')" by transfer auto
lemma Number_Hash: "Number X \<noteq> Hash  X'" by transfer auto
lemma Number_Tag: "Number X \<noteq> Tag  X'" by transfer auto
lemma Number_EphK: "Number X \<noteq> EphK  X'" by transfer auto
lemma Number_LtK: "Number X \<noteq> LtK  X'" by transfer auto
lemma Number_Pair: "Number X \<noteq> Pair  X' Y'" by transfer auto
lemma Number_Enc: "Number X \<noteq> Enc  X' Y'" by transfer auto
lemma Number_Aenc: "Number X \<noteq> Aenc  X' Y'" by transfer auto
lemma Number_Sign: "Number X \<noteq> Sign  X' Y'" by transfer auto
lemma Number_Exp: "Number X \<noteq> Exp  X' Y'" by transfer auto

lemma Hash_Nonce: "Hash X \<noteq> Nonce  X'" by transfer auto
lemma Hash_Agent: "Hash X \<noteq> Agent  X'" by transfer auto
lemma Hash_Number: "Hash X \<noteq> Number  X'" by transfer auto
lemma Hash_Hash: "(Hash X = Hash X') = (X = X')" by transfer auto
lemma Hash_Tag: "Hash X \<noteq> Tag  X'" by transfer auto
lemma Hash_EphK: "Hash X \<noteq> EphK  X'" by transfer auto
lemma Hash_LtK: "Hash X \<noteq> LtK  X'" by transfer auto
lemma Hash_Pair: "Hash X \<noteq> Pair  X' Y'" by transfer auto
lemma Hash_Enc: "Hash X \<noteq> Enc  X' Y'" by transfer auto
lemma Hash_Aenc: "Hash X \<noteq> Aenc  X' Y'" by transfer auto
lemma Hash_Sign: "Hash X \<noteq> Sign  X' Y'" by transfer auto
lemma Hash_Exp: "Hash X \<noteq> Exp  X' Y'" by transfer auto

lemma Tag_Nonce: "Tag X \<noteq> Nonce  X'" by transfer auto
lemma Tag_Agent: "Tag X \<noteq> Agent  X'" by transfer auto
lemma Tag_Number: "Tag X \<noteq> Number  X'" by transfer auto
lemma Tag_Hash: "Tag X \<noteq> Hash  X'" by transfer auto
lemma Tag_Tag: "(Tag X = Tag X') = (X = X')" by transfer auto
lemma Tag_EphK: "Tag X \<noteq> EphK  X'" by transfer auto
lemma Tag_LtK: "Tag X \<noteq> LtK  X'" by transfer auto
lemma Tag_Pair: "Tag X \<noteq> Pair  X' Y'" by transfer auto
lemma Tag_Enc: "Tag X \<noteq> Enc  X' Y'" by transfer auto
lemma Tag_Aenc: "Tag X \<noteq> Aenc  X' Y'" by transfer auto
lemma Tag_Sign: "Tag X \<noteq> Sign  X' Y'" by transfer auto
lemma Tag_Exp: "Tag X \<noteq> Exp  X' Y'" by transfer auto

lemma EphK_Nonce: "EphK X \<noteq> Nonce  X'" by transfer auto
lemma EphK_Agent: "EphK X \<noteq> Agent  X'" by transfer auto
lemma EphK_Number: "EphK X \<noteq> Number  X'" by transfer auto
lemma EphK_Hash: "EphK X \<noteq> Hash  X'" by transfer auto
lemma EphK_Tag: "EphK X \<noteq> Tag  X'" by transfer auto
lemma EphK_EphK: "(EphK X = EphK X') = (X = X')" by transfer auto
lemma EphK_LtK: "EphK X \<noteq> LtK  X'" by transfer auto
lemma EphK_Pair: "EphK X \<noteq> Pair  X' Y'" by transfer auto
lemma EphK_Enc: "EphK X \<noteq> Enc  X' Y'" by transfer auto
lemma EphK_Aenc: "EphK X \<noteq> Aenc  X' Y'" by transfer auto
lemma EphK_Sign: "EphK X \<noteq> Sign  X' Y'" by transfer auto
lemma EphK_Exp: "EphK X \<noteq> Exp  X' Y'" by transfer auto

lemma LtK_Nonce: "LtK X \<noteq> Nonce  X'" by transfer auto
lemma LtK_Agent: "LtK X \<noteq> Agent  X'" by transfer auto
lemma LtK_Number: "LtK X \<noteq> Number  X'" by transfer auto
lemma LtK_Hash: "LtK X \<noteq> Hash  X'" by transfer auto
lemma LtK_Tag: "LtK X \<noteq> Tag  X'" by transfer auto
lemma LtK_EphK: "LtK X \<noteq> EphK  X'" by transfer auto
lemma LtK_LtK: "(LtK X = LtK X') = (X = X')" by transfer auto
lemma LtK_Pair: "LtK X \<noteq> Pair  X' Y'" by transfer auto
lemma LtK_Enc: "LtK X \<noteq> Enc  X' Y'" by transfer auto
lemma LtK_Aenc: "LtK X \<noteq> Aenc  X' Y'" by transfer auto
lemma LtK_Sign: "LtK X \<noteq> Sign  X' Y'" by transfer auto
lemma LtK_Exp: "LtK X \<noteq> Exp  X' Y'" by transfer auto

lemma Pair_Nonce: "Pair X Y \<noteq> Nonce  X'" by transfer auto
lemma Pair_Agent: "Pair X Y \<noteq> Agent  X'" by transfer auto
lemma Pair_Number: "Pair X Y \<noteq> Number  X'" by transfer auto
lemma Pair_Hash: "Pair X Y \<noteq> Hash  X'" by transfer auto
lemma Pair_Tag: "Pair X Y \<noteq> Tag  X'" by transfer auto
lemma Pair_EphK: "Pair X Y \<noteq> EphK  X'" by transfer auto
lemma Pair_LtK: "Pair X Y \<noteq> LtK  X'" by transfer auto
lemma Pair_Pair: "(Pair X Y = Pair X' Y') = (X = X' \<and> Y = Y')" by transfer auto
lemma Pair_Enc: "Pair X Y \<noteq> Enc  X' Y'" by transfer auto
lemma Pair_Aenc: "Pair X Y \<noteq> Aenc  X' Y'" by transfer auto
lemma Pair_Sign: "Pair X Y \<noteq> Sign  X' Y'" by transfer auto
lemma Pair_Exp: "Pair X Y \<noteq> Exp  X' Y'" by transfer auto

lemma Enc_Nonce: "Enc X Y \<noteq> Nonce  X'" by transfer auto
lemma Enc_Agent: "Enc X Y \<noteq> Agent  X'" by transfer auto
lemma Enc_Number: "Enc X Y \<noteq> Number  X'" by transfer auto
lemma Enc_Hash: "Enc X Y \<noteq> Hash  X'" by transfer auto
lemma Enc_Tag: "Enc X Y \<noteq> Tag  X'" by transfer auto
lemma Enc_EphK: "Enc X Y \<noteq> EphK  X'" by transfer auto
lemma Enc_LtK: "Enc X Y \<noteq> LtK  X'" by transfer auto
lemma Enc_Pair: "Enc X Y \<noteq> Pair  X' Y'" by transfer auto
lemma Enc_Enc: "(Enc X Y = Enc X' Y') = (X = X' \<and> Y = Y')" by transfer auto
lemma Enc_Aenc: "Enc X Y \<noteq> Aenc  X' Y'" by transfer auto
lemma Enc_Sign: "Enc X Y \<noteq> Sign  X' Y'" by transfer auto
lemma Enc_Exp: "Enc X Y \<noteq> Exp  X' Y'" by transfer auto

lemma Aenc_Nonce: "Aenc X Y \<noteq> Nonce  X'" by transfer auto
lemma Aenc_Agent: "Aenc X Y \<noteq> Agent  X'" by transfer auto
lemma Aenc_Number: "Aenc X Y \<noteq> Number  X'" by transfer auto
lemma Aenc_Hash: "Aenc X Y \<noteq> Hash  X'" by transfer auto
lemma Aenc_Tag: "Aenc X Y \<noteq> Tag  X'" by transfer auto
lemma Aenc_EphK: "Aenc X Y \<noteq> EphK  X'" by transfer auto
lemma Aenc_LtK: "Aenc X Y \<noteq> LtK  X'" by transfer auto
lemma Aenc_Pair: "Aenc X Y \<noteq> Pair  X' Y'" by transfer auto
lemma Aenc_Enc: "Aenc X Y \<noteq> Enc  X' Y'" by transfer auto
lemma Aenc_Aenc: "(Aenc X Y = Aenc X' Y') = (X = X' \<and> Y = Y')" by transfer auto
lemma Aenc_Sign: "Aenc X Y \<noteq> Sign  X' Y'" by transfer auto
lemma Aenc_Exp: "Aenc X Y \<noteq> Exp  X' Y'" by transfer auto

lemma Sign_Nonce: "Sign X Y \<noteq> Nonce  X'" by transfer auto
lemma Sign_Agent: "Sign X Y \<noteq> Agent  X'" by transfer auto
lemma Sign_Number: "Sign X Y \<noteq> Number  X'" by transfer auto
lemma Sign_Hash: "Sign X Y \<noteq> Hash  X'" by transfer auto
lemma Sign_Tag: "Sign X Y \<noteq> Tag  X'" by transfer auto
lemma Sign_EphK: "Sign X Y \<noteq> EphK  X'" by transfer auto
lemma Sign_LtK: "Sign X Y \<noteq> LtK  X'" by transfer auto
lemma Sign_Pair: "Sign X Y \<noteq> Pair  X' Y'" by transfer auto
lemma Sign_Enc: "Sign X Y \<noteq> Enc  X' Y'" by transfer auto
lemma Sign_Aenc: "Sign X Y \<noteq> Aenc  X' Y'" by transfer auto
lemma Sign_Sign: "(Sign X Y = Sign X' Y') = (X = X' \<and> Y = Y')" by transfer auto
lemma Sign_Exp: "Sign X Y \<noteq> Exp  X' Y'" by transfer auto

lemma Exp_Nonce: "Exp X Y \<noteq> Nonce  X'" by transfer auto
lemma Exp_Agent: "Exp X Y \<noteq> Agent  X'" by transfer auto
lemma Exp_Number: "Exp X Y \<noteq> Number  X'" by transfer auto
lemma Exp_Hash: "Exp X Y \<noteq> Hash  X'" by transfer auto
lemma Exp_Tag: "Exp X Y \<noteq> Tag  X'" by transfer auto
lemma Exp_EphK: "Exp X Y \<noteq> EphK  X'" by transfer auto
lemma Exp_LtK: "Exp X Y \<noteq> LtK  X'" by transfer auto
lemma Exp_Pair: "Exp X Y \<noteq> Pair  X' Y'" by transfer auto
lemma Exp_Enc: "Exp X Y \<noteq> Enc  X' Y'" by transfer auto
lemma Exp_Aenc: "Exp X Y \<noteq> Aenc  X' Y'" by transfer auto
lemma Exp_Sign: "Exp X Y \<noteq> Sign  X' Y'" by transfer auto


lemmas msg_inject [iff, induct_simp] =
  Nonce_Nonce Agent_Agent Number_Number Hash_Hash Tag_Tag EphK_EphK LtK_LtK 
  Pair_Pair Enc_Enc Aenc_Aenc Sign_Sign

lemmas msg_distinct [simp, induct_simp] =
  Nonce_Agent Nonce_Number Nonce_Hash Nonce_Tag Nonce_EphK Nonce_LtK Nonce_Pair 
  Nonce_Enc Nonce_Aenc Nonce_Sign Nonce_Exp 
  Agent_Nonce Agent_Number Agent_Hash Agent_Tag Agent_EphK Agent_LtK Agent_Pair 
  Agent_Enc Agent_Aenc Agent_Sign Agent_Exp 
  Number_Nonce Number_Agent Number_Hash Number_Tag Number_EphK Number_LtK 
  Number_Pair Number_Enc Number_Aenc Number_Sign Number_Exp 
  Hash_Nonce Hash_Agent Hash_Number Hash_Tag Hash_EphK Hash_LtK Hash_Pair 
  Hash_Enc Hash_Aenc Hash_Sign Hash_Exp 
  Tag_Nonce Tag_Agent Tag_Number Tag_Hash Tag_EphK Tag_LtK Tag_Pair 
  Tag_Enc Tag_Aenc Tag_Sign Tag_Exp 
  EphK_Nonce EphK_Agent EphK_Number EphK_Hash EphK_Tag EphK_LtK EphK_Pair 
  EphK_Enc EphK_Aenc EphK_Sign EphK_Exp 
  LtK_Nonce LtK_Agent LtK_Number LtK_Hash LtK_Tag LtK_EphK LtK_Pair 
  LtK_Enc LtK_Aenc LtK_Sign LtK_Exp 
  Pair_Nonce Pair_Agent Pair_Number Pair_Hash Pair_Tag Pair_EphK Pair_LtK 
  Pair_Enc Pair_Aenc Pair_Sign Pair_Exp 
  Enc_Nonce Enc_Agent Enc_Number Enc_Hash Enc_Tag Enc_EphK Enc_LtK Enc_Pair 
  Enc_Aenc Enc_Sign Enc_Exp 
  Aenc_Nonce Aenc_Agent Aenc_Number Aenc_Hash Aenc_Tag Aenc_EphK Aenc_LtK 
  Aenc_Pair Aenc_Enc Aenc_Sign Aenc_Exp 
  Sign_Nonce Sign_Agent Sign_Number Sign_Hash Sign_Tag Sign_EphK Sign_LtK 
  Sign_Pair Sign_Enc Sign_Aenc Sign_Exp 
  Exp_Nonce Exp_Agent Exp_Number Exp_Hash Exp_Tag Exp_EphK Exp_LtK Exp_Pair 
  Exp_Enc Exp_Aenc Exp_Sign 


consts Ngen :: nat
abbreviation "Gen \<equiv> Number Ngen"
abbreviation "cGen \<equiv> cNumber Ngen"

abbreviation 
  "InsecTag \<equiv> Tag insec"

abbreviation 
  "AuthTag \<equiv> Tag auth"

abbreviation 
  "ConfidTag \<equiv> Tag confid"

abbreviation 
  "SecureTag \<equiv> Tag secure"

abbreviation 
  "Tags \<equiv> range Tag"

abbreviation
  NonceF :: "fresh_t \<Rightarrow> msg" where
  "NonceF N \<equiv> Nonce (nonce_fresh N)"

abbreviation
  NonceA :: "nat \<Rightarrow> msg" where
  "NonceA N \<equiv> Nonce (nonce_atk N)"

abbreviation
  shrK :: "agent \<Rightarrow> agent \<Rightarrow> msg" where
  "shrK A B \<equiv> LtK (sharK A B)"

abbreviation
  pubK :: "agent \<Rightarrow> msg" where
  "pubK A \<equiv> LtK (publK A)"

abbreviation
  priK :: "agent \<Rightarrow> msg" where
  "priK A \<equiv> LtK (privK A)"

abbreviation
  epubK :: "nonce_t \<Rightarrow> msg" where
  "epubK N \<equiv> EphK (epublK N)"

abbreviation
  epriK :: "nonce_t \<Rightarrow> msg" where
  "epriK N \<equiv> EphK (eprivK N)"

abbreviation
  epubKF :: "fresh_t \<Rightarrow> msg" where
  "epubKF N \<equiv> EphK (epublK (nonce_fresh N))"

abbreviation
  epriKF :: "fresh_t \<Rightarrow> msg" where
  "epriKF N \<equiv> EphK (eprivK (nonce_fresh N))"

abbreviation
  epubKA :: "nat \<Rightarrow> msg" where
  "epubKA N \<equiv> EphK (epublK (nonce_atk N))"

abbreviation
  epriKA :: "nat \<Rightarrow> msg" where
  "epriKA N \<equiv> EphK (eprivK (nonce_atk N))"


text\<open>Concrete syntax: messages appear as <A,B,NA>, etc...\<close>

syntax
  "_MTuple"      :: "['a, args] \<Rightarrow> 'a * 'b"       ("(2\<langle>_,/ _\<rangle>)")
translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"    \<rightleftharpoons> "CONST Pair x y"

text \<open>hash macs\<close>
abbreviation
  hmac :: "msg \<Rightarrow> msg \<Rightarrow> msg" where
  "hmac M K \<equiv> Hash \<langle>M, K\<rangle>"


text \<open>recover some kind of injectivity for Exp\<close>
lemma eq_expgen: 
  "eq X Y \<Longrightarrow> (\<forall> X'. X = cExp cGen X' \<longrightarrow> (\<exists> Z. Y = (cExp cGen Z) \<and> eq X' Z)) \<and>
              (\<forall> Y'. Y = cExp cGen Y' \<longrightarrow> (\<exists> Z. X = (cExp cGen Z) \<and> eq Y' Z))"
by (erule eq.induct, auto elim!: Tr)

lemma Exp_Gen_inj: "Exp Gen X = Exp Gen Y \<Longrightarrow> X = Y"
by (transfer, auto dest: eq_expgen)


lemma eq_expexpgen: 
  "eq X Y \<Longrightarrow> (\<forall> X' X''. X = cExp (cExp cGen X') X'' \<longrightarrow> 
                (\<exists> Y' Y''. Y = cExp (cExp cGen Y') Y'' \<and> 
                   ((eq X' Y' \<and> eq X'' Y'') \<or> (eq X' Y'' \<and> eq X'' Y'))))" 
apply (erule eq.induct, simp_all) 
apply ((drule eq_expgen)+, force)
apply (auto, blast+)
done

lemma Exp_Exp_Gen_inj:
  "Exp (Exp Gen X) X' = Z \<Longrightarrow>
   (\<exists> Y Y'. Z = Exp (Exp Gen Y) Y' \<and> ((X = Y \<and> X' = Y') \<or> (X = Y' \<and> X' = Y)))"
by (transfer, auto dest: eq_expexpgen)

lemma Exp_Exp_Gen_inj2:
  "Exp (Exp Gen X) X' = Exp Z Y' \<Longrightarrow>
  (Y' = X \<and> Z = Exp Gen X') \<or> (Y' = X' \<and> Z = Exp Gen X)"
apply (transfer, auto)
apply (drule eq_expexpgen, auto)+
done



end
