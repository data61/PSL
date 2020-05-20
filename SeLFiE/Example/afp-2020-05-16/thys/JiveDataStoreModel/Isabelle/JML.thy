(*  Title:       Jive Data and Store Model
    Author:      Norbert Schirmer <schirmer at informatik.tu-muenchen.de>  and  
                 Nicole Rauch <rauch at informatik.uni-kl.de>, 2005
    Maintainer:  Nicole Rauch <rauch at informatik.uni-kl.de>
    License:     LGPL
*)

section \<open>The Formalization of JML Operators\<close>

theory JML imports "../Isabelle_Store/StoreProperties" begin

text \<open>JML operators that are to be used in Hoare formulae can be formalized here.
\<close>

definition
  instanceof :: "Value \<Rightarrow> Javatype \<Rightarrow> bool"  ("_ @instanceof _")
where
  "instanceof v t = (typeof v \<le> t)"

end
