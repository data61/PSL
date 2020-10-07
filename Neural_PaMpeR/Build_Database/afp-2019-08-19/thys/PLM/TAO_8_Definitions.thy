(*<*)
theory TAO_8_Definitions
imports TAO_7_Axioms
begin
(*>*)

section\<open>Definitions\<close>
text\<open>\label{TAO_Definitions}\<close>

subsection\<open>Property Negations\<close>

consts propnot :: "'a\<Rightarrow>'a" ("_\<^sup>-" [90] 90)
overloading propnot\<^sub>0 \<equiv> "propnot :: \<Pi>\<^sub>0\<Rightarrow>\<Pi>\<^sub>0"
            propnot\<^sub>1 \<equiv> "propnot :: \<Pi>\<^sub>1\<Rightarrow>\<Pi>\<^sub>1"
            propnot\<^sub>2 \<equiv> "propnot :: \<Pi>\<^sub>2\<Rightarrow>\<Pi>\<^sub>2"
            propnot\<^sub>3 \<equiv> "propnot :: \<Pi>\<^sub>3\<Rightarrow>\<Pi>\<^sub>3"
begin
  definition propnot\<^sub>0 :: "\<Pi>\<^sub>0\<Rightarrow>\<Pi>\<^sub>0" where
    "propnot\<^sub>0 \<equiv> \<lambda> p . \<^bold>\<lambda>\<^sup>0 (\<^bold>\<not>p)"
  definition propnot\<^sub>1 where
    "propnot\<^sub>1 \<equiv> \<lambda> F . \<^bold>\<lambda> x . \<^bold>\<not>\<lparr>F, x\<^sup>P\<rparr>"
  definition propnot\<^sub>2 where
    "propnot\<^sub>2 \<equiv> \<lambda> F . \<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<^bold>\<not>\<lparr>F, x\<^sup>P, y\<^sup>P\<rparr>)"
  definition propnot\<^sub>3 where
    "propnot\<^sub>3 \<equiv> \<lambda> F . \<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<^bold>\<not>\<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)"
end

named_theorems propnot_defs
declare propnot\<^sub>0_def[propnot_defs] propnot\<^sub>1_def[propnot_defs]
        propnot\<^sub>2_def[propnot_defs] propnot\<^sub>3_def[propnot_defs]

subsection\<open>Noncontingent and Contingent Relations\<close>

consts Necessary :: "'a\<Rightarrow>\<o>"
overloading Necessary\<^sub>0 \<equiv> "Necessary :: \<Pi>\<^sub>0\<Rightarrow>\<o>"
            Necessary\<^sub>1 \<equiv> "Necessary :: \<Pi>\<^sub>1\<Rightarrow>\<o>"
            Necessary\<^sub>2 \<equiv> "Necessary :: \<Pi>\<^sub>2\<Rightarrow>\<o>"
            Necessary\<^sub>3 \<equiv> "Necessary :: \<Pi>\<^sub>3\<Rightarrow>\<o>"
begin
  definition Necessary\<^sub>0 where
    "Necessary\<^sub>0 \<equiv> \<lambda> p . \<^bold>\<box>p"
  definition Necessary\<^sub>1 :: "\<Pi>\<^sub>1\<Rightarrow>\<o>" where
    "Necessary\<^sub>1 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr>)"
  definition Necessary\<^sub>2 where
    "Necessary\<^sub>2 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x y . \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>)"
  definition Necessary\<^sub>3 where
    "Necessary\<^sub>3 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x y z . \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
end

named_theorems Necessary_defs
declare Necessary\<^sub>0_def[Necessary_defs] Necessary\<^sub>1_def[Necessary_defs]
        Necessary\<^sub>2_def[Necessary_defs] Necessary\<^sub>3_def[Necessary_defs]

consts Impossible :: "'a\<Rightarrow>\<o>"
overloading Impossible\<^sub>0 \<equiv> "Impossible :: \<Pi>\<^sub>0\<Rightarrow>\<o>"
            Impossible\<^sub>1 \<equiv> "Impossible :: \<Pi>\<^sub>1\<Rightarrow>\<o>"
            Impossible\<^sub>2 \<equiv> "Impossible :: \<Pi>\<^sub>2\<Rightarrow>\<o>"
            Impossible\<^sub>3 \<equiv> "Impossible :: \<Pi>\<^sub>3\<Rightarrow>\<o>"
begin
  definition Impossible\<^sub>0 where
    "Impossible\<^sub>0 \<equiv> \<lambda> p . \<^bold>\<box>\<^bold>\<not>p"
  definition Impossible\<^sub>1 where
    "Impossible\<^sub>1 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)"
  definition Impossible\<^sub>2 where
    "Impossible\<^sub>2 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x y. \<^bold>\<not>\<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>)"
  definition Impossible\<^sub>3 where
    "Impossible\<^sub>3 \<equiv> \<lambda> F . \<^bold>\<box>(\<^bold>\<forall> x y z. \<^bold>\<not>\<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
end

named_theorems Impossible_defs
declare Impossible\<^sub>0_def[Impossible_defs] Impossible\<^sub>1_def[Impossible_defs]
        Impossible\<^sub>2_def[Impossible_defs] Impossible\<^sub>3_def[Impossible_defs]

definition NonContingent where
  "NonContingent \<equiv> \<lambda> F . (Necessary F) \<^bold>\<or> (Impossible F)"
definition Contingent where
  "Contingent \<equiv> \<lambda> F .  \<^bold>\<not>(Necessary F \<^bold>\<or> Impossible F)"

definition ContingentlyTrue :: "\<o>\<Rightarrow>\<o>" where
  "ContingentlyTrue \<equiv> \<lambda> p . p \<^bold>& \<^bold>\<diamond>\<^bold>\<not>p"
definition ContingentlyFalse :: "\<o>\<Rightarrow>\<o>" where
  "ContingentlyFalse \<equiv> \<lambda> p . \<^bold>\<not>p \<^bold>& \<^bold>\<diamond>p"

definition WeaklyContingent where
  "WeaklyContingent \<equiv> \<lambda> F . Contingent F \<^bold>& (\<^bold>\<forall> x. \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F,x\<^sup>P\<rparr>)"

subsection\<open>Null and Universal Objects\<close>

definition Null :: "\<kappa>\<Rightarrow>\<o>" where
  "Null \<equiv> \<lambda> x . \<lparr>A!,x\<rparr> \<^bold>& \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x, F\<rbrace>)"
definition Universal :: "\<kappa>\<Rightarrow>\<o>" where
  "Universal \<equiv> \<lambda> x . \<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x, F\<rbrace>)"

definition NullObject :: "\<kappa>" ("\<^bold>a\<^sub>\<emptyset>") where
  "NullObject \<equiv> (\<^bold>\<iota>x . Null (x\<^sup>P))"
definition UniversalObject :: "\<kappa>" ("\<^bold>a\<^sub>V") where
  "UniversalObject \<equiv> (\<^bold>\<iota>x . Universal (x\<^sup>P))"

subsection\<open>Propositional Properties\<close>

definition Propositional where
  "Propositional F \<equiv> \<^bold>\<exists>  p . F \<^bold>= (\<^bold>\<lambda> x . p)"

subsection\<open>Indiscriminate Properties\<close>

definition Indiscriminate :: "\<Pi>\<^sub>1\<Rightarrow>\<o>" where
  "Indiscriminate \<equiv> \<lambda> F . \<^bold>\<box>((\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr>))"

subsection\<open>Miscellaneous\<close>

definition not_identical\<^sub>E :: "\<kappa>\<Rightarrow>\<kappa>\<Rightarrow>\<o>" (infixl "\<^bold>\<noteq>\<^sub>E" 63)
  where "not_identical\<^sub>E \<equiv> \<lambda> x y . \<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P))\<^sup>-, x, y\<rparr>"

(*<*)
end
(*>*)
