theory BoolProgs_LTL_Conv
imports
  BoolProgs_Extras
  "HOL-Library.Mapping"
  LTL.LTL
begin

fun b2l :: "bexp \<Rightarrow> nat ltlc" where
  "b2l TT = true\<^sub>c"
| "b2l FF = false\<^sub>c"
| "b2l (bexp.V v) = prop\<^sub>c(v)"
| "b2l (bexp.Not e) = not\<^sub>c (b2l e)"
| "b2l (And e1 e2) = b2l e1 and\<^sub>c b2l e2"
| "b2l (Or e1 e2) = b2l e1 or\<^sub>c b2l e2"

datatype
  propc = CProp String.literal | FProp "String.literal * integer"

fun ltl_conv :: "const_map \<Rightarrow> fun_map \<Rightarrow> propc ltlc \<Rightarrow> (nat ltlc + String.literal)"
where
  "ltl_conv _ _ True_ltlc = Inl True_ltlc"
| "ltl_conv _ _ False_ltlc = Inl False_ltlc"
| "ltl_conv C _ (Prop_ltlc (CProp s)) = (case Mapping.lookup C s of
                                              Some c \<Rightarrow> Inl (b2l c)
                                             | None \<Rightarrow> Inr (STR ''Unknown constant: '' + s))"
| "ltl_conv _ M (Prop_ltlc (FProp (s, argm))) = (case Mapping.lookup M s of
                                                    Some f \<Rightarrow> (Inl \<circ> b2l \<circ> f \<circ> nat_of_integer) argm
                                                  | None \<Rightarrow> Inr (STR ''Unknown function: '' + s))"
| "ltl_conv C M (Not_ltlc x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (Not_ltlc l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (Next_ltlc x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (Next_ltlc l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (Final_ltlc x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (Final_ltlc l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (Global_ltlc x) = (case ltl_conv C M x of Inl l \<Rightarrow> Inl (Global_ltlc l) | Inr s \<Rightarrow> Inr s)"
| "ltl_conv C M (And_ltlc x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (And_ltlc l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (Or_ltlc x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (Or_ltlc l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (Implies_ltlc x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (Implies_ltlc l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (Until_ltlc x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (Until_ltlc l r) | Inr s \<Rightarrow> Inr s))"
| "ltl_conv C M (Release_ltlc x y) = (case ltl_conv C M x of 
                                    Inr s \<Rightarrow> Inr s
                                  | Inl l \<Rightarrow> (case ltl_conv C M y of Inl r \<Rightarrow> Inl (Release_ltlc l r) | Inr s \<Rightarrow> Inr s))"

end
