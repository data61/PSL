(* Title: Verification Component Based on KAD: Trace Semantics
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

subsection \<open>Two Extensions\<close>

subsubsection \<open>KAD Component with Trace Semantics\<close>

theory Path_Model_Example
  imports VC_KAD "HOL-Eisbach.Eisbach"
begin

text \<open>This component supports the verification of simple while programs
in a partial correctness setting based on a program trace semantics.\<close>

text \<open>Program traces are modelled as non-empty paths or state sequences. The non-empty path model 
of Kleene algebra is taken from the AFP entry for Kleene algebra. Here we show that sets of paths form
antidomain Kleene Algebras.\<close>

definition pp_a ::  "'a ppath set \<Rightarrow> 'a ppath set" where
  "pp_a X = {(Node u) |u. \<not> (\<exists>v \<in> X. u = pp_first v)}"

interpretation ppath_aka: antidomain_kleene_algebra pp_a "(\<union>)" pp_prod pp_one "{}" "(\<subseteq>)" "(\<subset>)" pp_star
  apply standard
  apply (clarsimp simp add: pp_prod_def pp_a_def)
  apply (simp add: pp_prod_def pp_a_def, safe, metis pp_first.simps(1) pp_first_pp_fusion)
  by (auto simp: pp_a_def pp_one_def)   

text \<open>A verification component can then be built with little effort, by and large reusing
parts of the relational components that are generic with respect to the store.\<close>      

definition pp_gets :: "string \<Rightarrow> ('a store \<Rightarrow> 'a) \<Rightarrow> 'a store ppath set" ("_ ::= _" [70, 65] 61) where 
  "v ::= e = {Cons s (Node (s (v := e s))) | s. True}"

definition p2pp :: "'a pred \<Rightarrow> 'a ppath set" where
  "p2pp P = {Node s |s. P s}"

lemma pp_a_neg [simp]: "pp_a (p2pp Q) = p2pp (-Q)"
  by (force simp add: pp_a_def p2pp_def)

lemma ppath_assign [simp]: "ppath_aka.fbox (v ::= e) (p2pp Q) = p2pp (\<lambda>s. Q (s(v := e s)))"
  by (force simp: ppath_aka.fbox_def pp_a_def p2pp_def pp_prod_def pp_gets_def)      

no_notation spec_sugar ("PRE _ _ POST _" [64,64,64] 63)
   and relcomp (infixl ";" 70)
   and cond_sugar ("IF _ THEN _ ELSE _ FI" [64,64,64] 63)
   and whilei_sugar ("WHILE _ INV _ DO _ OD" [64,64,64] 63)
   and gets ("_ ::= _" [70, 65] 61)
   and rel_antidomain_kleene_algebra.fbox ("wp")
   and rel_antidomain_kleene_algebra.ads_d ("rdom")
   and p2r ("\<lceil>_\<rceil>")

notation ppath_aka.fbox ("wp")
  and ppath_aka.ads_d ("rdom")
  and p2pp ("\<lceil>_\<rceil>")
  and pp_prod (infixl ";" 70)

abbreviation spec_sugar :: "'a pred \<Rightarrow> 'a ppath set \<Rightarrow> 'a pred \<Rightarrow> bool" ("PRE _ _ POST _" [64,64,64] 63) where
  "PRE P X POST Q \<equiv> rdom \<lceil>P\<rceil> \<subseteq> wp X \<lceil>Q\<rceil>"

abbreviation cond_sugar :: "'a pred \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set" ("IF _ THEN _ ELSE _ FI" [64,64,64] 63) where
  "IF P THEN X ELSE Y FI \<equiv> ppath_aka.cond \<lceil>P\<rceil> X Y"

abbreviation whilei_sugar :: "'a pred \<Rightarrow> 'a pred \<Rightarrow> 'a ppath set \<Rightarrow> 'a ppath set" ("WHILE _ INV _ DO _ OD" [64,64,64] 63) where
  "WHILE P INV I DO X OD \<equiv> ppath_aka.whilei \<lceil>P\<rceil> \<lceil>I\<rceil> X"

lemma [simp]: "p2pp P \<union> p2pp Q = p2pp (P \<squnion> Q)"
  by (force simp: p2pp_def)

lemma [simp]: "p2pp P; p2pp Q = p2pp (P \<sqinter> Q)"
  by (force simp: p2pp_def pp_prod_def)

lemma [intro!]:  "P \<le> Q \<Longrightarrow> \<lceil>P\<rceil> \<subseteq> \<lceil>Q\<rceil>"
  by (force simp: p2pp_def)

lemma [simp]: "rdom \<lceil>P\<rceil> = \<lceil>P\<rceil>"
  by (simp add: ppath_aka.addual.ars_r_def)

lemma euclid:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
  by (rule ppath_aka.fbox_whilei, simp_all, auto simp: p2pp_def rel_ad_def gcd_non_0_nat)

lemma euclid_diff: 
   "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y \<and> x > 0 \<and> y > 0)
    (WHILE (\<lambda>s. s ''x''\<noteq> s ''y'') INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
     DO
        (IF (\<lambda>s. s ''x'' >  s ''y'')
         THEN (''x'' ::= (\<lambda>s. s ''x'' - s ''y''))
         ELSE (''y'' ::= (\<lambda>s. s ''y'' - s ''x''))
         FI)
    OD)
    POST (\<lambda>s. s ''x'' = gcd x y)"
  apply (rule ppath_aka.fbox_whilei, simp_all)
  apply (simp_all add: p2pp_def) 
  apply auto[2]
  by (safe, metis gcd.commute gcd_diff1_nat le_cases nat_less_le)

lemma varible_swap:
  "PRE (\<lambda>s. s ''x'' = a \<and> s ''y'' = b)   
    (''z'' ::= (\<lambda>s. s ''x''));
    (''x'' ::= (\<lambda>s. s ''y''));
    (''y'' ::= (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by auto

lemma maximum: 
  "PRE (\<lambda>s:: nat store. True) 
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
  by auto

lemma integer_division: 
  "PRE (\<lambda>s::nat store. x \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. x));
    (WHILE (\<lambda>s. y \<le> s ''r'') INV (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - y))
      OD)
   POST (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < y)"
  by (rule ppath_aka.fbox_whilei_break, auto)
 
text \<open>We now reconsider these examples with an Eisbach tactic.\<close>

named_theorems ht

declare ppath_aka.fbox_whilei [ht]
  ppath_aka.fbox_seq_var [ht]
  subset_refl[ht]

method hoare = (rule ht; hoare?)

lemma euclid2:
  "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y)
   (WHILE (\<lambda>s. s ''y'' \<noteq> 0) INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
    DO
     (''z'' ::= (\<lambda>s. s ''y''));
     (''y'' ::= (\<lambda>s. s ''x'' mod s ''y''));
     (''x'' ::= (\<lambda>s. s ''z''))
    OD)
   POST (\<lambda>s. s ''x'' = gcd x y)"
apply hoare
using gcd_red_nat by auto

lemma euclid_diff2: 
   "PRE (\<lambda>s::nat store. s ''x'' = x \<and> s ''y'' = y \<and> x > 0 \<and> y > 0)
    (WHILE (\<lambda>s. s ''x''\<noteq> s ''y'') INV (\<lambda>s. gcd (s ''x'') (s ''y'') = gcd x y) 
     DO
        (IF (\<lambda>s. s ''x'' >  s ''y'')
         THEN (''x'' ::= (\<lambda>s. s ''x'' - s ''y''))
         ELSE (''y'' ::= (\<lambda>s. s ''y'' - s ''x''))
         FI)
    OD)
    POST (\<lambda>s. s ''x'' = gcd x y)"
  by (hoare; clarsimp; metis gcd.commute gcd_diff1_nat le_cases nat_less_le)

lemma varible_swap2:
  "PRE (\<lambda>s. s ''x'' = a \<and> s ''y'' = b)   
    (''z'' ::= (\<lambda>s. s ''x''));
    (''x'' ::= (\<lambda>s. s ''y''));
    (''y'' ::= (\<lambda>s. s ''z''))
   POST (\<lambda>s. s ''x'' = b \<and> s ''y'' = a)"
  by clarsimp

lemma maximum2: 
  "PRE (\<lambda>s:: nat store. True) 
   (IF (\<lambda>s. s ''x'' \<ge> s ''y'') 
    THEN (''z'' ::= (\<lambda>s. s ''x''))
    ELSE (''z'' ::= (\<lambda>s. s ''y''))
    FI)
   POST (\<lambda>s. s ''z'' = max (s ''x'') (s ''y''))"
   by auto

lemma integer_division2: 
  "PRE (\<lambda>s::nat store. x \<ge> 0)
    (''q'' ::= (\<lambda>s. 0)); 
    (''r'' ::= (\<lambda>s. x));
    (WHILE (\<lambda>s. y \<le> s ''r'') INV (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0)
     DO
      (''q'' ::= (\<lambda>s. s ''q'' + 1));
      (''r'' ::= (\<lambda>s. s ''r'' - y))
      OD)
   POST (\<lambda>s. x = s ''q'' * y + s ''r'' \<and> s ''r'' \<ge> 0 \<and> s ''r'' < y)"
   by hoare auto

lemma my_power2:
  "PRE (\<lambda>s::nat store. True)
   (''i'' ::= (\<lambda>s. 0));
   (''y'' ::= (\<lambda>s. 1));
   (WHILE (\<lambda>s. s ''i'' < n) INV (\<lambda>s. s ''y'' = x ^ (s ''i'') \<and> s ''i'' \<le> n)
     DO
       (''y'' ::= (\<lambda>s. (s ''y'') * x));
       (''i'' ::= (\<lambda>s. s ''i'' + 1))
     OD)
   POST (\<lambda>s. s ''y'' = x ^ n)"
  by hoare auto

lemma imp_reverse2:
  "PRE (\<lambda>s:: 'a list store. s ''x'' = X)
   (''y'' ::= (\<lambda>s. []));
   (WHILE (\<lambda>s. s ''x'' \<noteq> []) INV (\<lambda>s. rev (s ''x'') @ s ''y'' = rev X)
    DO 
     (''y'' ::= (\<lambda>s. hd (s ''x'') # s ''y'')); 
     (''x'' ::= (\<lambda>s. tl (s ''x'')))
    OD) 
   POST (\<lambda>s. s ''y''= rev X )"
  apply hoare
  apply auto
  apply (metis append.simps append_assoc hd_Cons_tl rev.simps(2))
done

end
