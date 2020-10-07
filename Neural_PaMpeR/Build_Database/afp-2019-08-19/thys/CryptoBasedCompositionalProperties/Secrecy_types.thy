(*
   Title: Theory  Secrecy_types.thy
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)

section \<open>Auxiliary data types\<close>

theory Secrecy_types
imports Main
begin

\<comment> \<open>We assume disjoint sets: Data of data values,\<close>
\<comment> \<open>Secrets of unguessable values, Keys - set of cryptographic  keys.\<close>  
\<comment> \<open>Based on these sets, we specify the sets EncType of encryptors that may be\<close>
\<comment> \<open>used for encryption or decryption, and Expression of expression items.\<close>
\<comment> \<open>The specification (component) identifiers should be listed in the set specID,\<close>
\<comment> \<open>the channel indentifiers should be listed in the set chanID.\<close> 

datatype Keys = CKey | CKeyP | SKey | SKeyP | genKey 
datatype Secrets = secretD | N | NA
type_synonym Var  = "nat"
type_synonym Data = "nat"
datatype KS          = kKS Keys | sKS Secrets
datatype EncType  = kEnc Keys | vEnc Var
datatype specID = sComp1 | sComp2 | sComp3 | sComp4
datatype Expression = kE Keys | sE Secrets | dE Data | idE specID 
datatype chanID = ch1 | ch2   | ch3  | ch4

primrec Expression2KSL:: "Expression list \<Rightarrow> KS list" 
where
   "Expression2KSL [] = []" |
   "Expression2KSL (x#xs) = 
     ((case x of (kE m) \<Rightarrow> [kKS m] 
                  | (sE m) \<Rightarrow> [sKS m] 
                  | (dE m) \<Rightarrow> [] 
                  | (idE m) \<Rightarrow> []) @ Expression2KSL xs) "

primrec KS2Expression:: "KS \<Rightarrow> Expression" 
where
  "KS2Expression (kKS m) = (kE m)"  |
  "KS2Expression (sKS m) = (sE m)"

end
