(*  Title:       CoreC++

    Author:      Tobias Nipkow, Daniel Wasserrab 
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>

    Extracted from the Jinja theory J/Expr.thy by Tobias Nipkow
*)

section \<open>Syntax\<close>

theory Syntax imports Exceptions begin


text\<open>Syntactic sugar\<close>

abbreviation (input)
  InitBlock :: "vname \<Rightarrow> ty \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> expr"   ("(1'{_:_ := _;/ _})") where
  "InitBlock V T e1 e2 == {V:T; V := e1;; e2}"

abbreviation unit where "unit == Val Unit"
abbreviation null where "null == Val Null"
abbreviation "ref r == Val(Ref r)"
abbreviation "true == Val(Bool True)"
abbreviation "false == Val(Bool False)"

abbreviation
  Throw :: "reference \<Rightarrow> expr" where
  "Throw r == throw(ref r)"

abbreviation (input)
  THROW :: "cname \<Rightarrow> expr" where
  "THROW xc == Throw(addr_of_sys_xcpt xc,[xc])"

end
