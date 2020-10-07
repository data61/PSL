theory Relations
imports Main
begin

type_synonym 'a Rel = "'a \<Rightarrow> 'a \<Rightarrow> bool"

abbreviation symmetric :: "'a Rel \<Rightarrow> bool" where 
  "symmetric  A \<equiv> \<forall> x.  \<forall> y. (A x y) \<longrightarrow> (A y x)"

abbreviation asymmetric :: "'a Rel \<Rightarrow> bool" where
 " asymmetric A \<equiv> \<forall> x. \<forall> y. (A x y) \<longrightarrow> \<not>(A y x)"

abbreviation antisymmetric :: "'a Rel \<Rightarrow> bool" where
 " antisymmetric A \<equiv> \<forall> x. \<forall> y. (A x y \<and> A y x) \<longrightarrow> x = y" 

abbreviation reflexive :: "'a Rel \<Rightarrow> bool" where 
  "reflexive  A \<equiv> \<forall> x. A x x"

abbreviation irreflexive :: "'a Rel \<Rightarrow> bool" where 
  "irreflexive  A \<equiv> \<forall> x. \<not>(A x x)"

abbreviation transitive :: "'a Rel \<Rightarrow> bool" where 
  "transitive  A \<equiv> \<forall> x. \<forall> y. \<forall> z. (A x y) \<and> (A y z) \<longrightarrow> (A x z)"

abbreviation total :: "'a Rel \<Rightarrow> bool" where 
  "total  A \<equiv> \<forall> x. \<forall> y. A x y \<or> A y x"

abbreviation universal :: "'a Rel \<Rightarrow> bool" where 
  "universal  A \<equiv> \<forall> x. \<forall> y. A x y"

abbreviation serial :: "'a Rel \<Rightarrow> bool" where 
  "serial  A \<equiv> \<forall> x. \<exists> y. A x y"

abbreviation euclidean :: "'a Rel \<Rightarrow> bool" where 
  "euclidean  A \<equiv> \<forall>x y z. (A x y \<and> A x z) \<longrightarrow> A y z"

abbreviation preorder :: "'a Rel \<Rightarrow> bool" where
  "preorder A \<equiv> reflexive A \<and> transitive A"

abbreviation equivalence :: "'a Rel \<Rightarrow> bool" where
  "equivalence A \<equiv> preorder A \<and> symmetric A"

abbreviation partial_order :: "'a Rel \<Rightarrow> bool" where
  "partial_order A \<equiv>  preorder A \<and> antisymmetric A"

abbreviation strict_partial_order :: "'a Rel \<Rightarrow> bool" where
  "strict_partial_order A \<equiv>  irreflexive A \<and> asymmetric A \<and> transitive A" (* asymmetry is redundant *)

end
