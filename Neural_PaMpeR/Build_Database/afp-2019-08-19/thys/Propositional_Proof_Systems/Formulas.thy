section \<open>Formulas\<close>

theory Formulas
imports Main "HOL-Library.Countable"
begin

(* unrelated, but I need this in too many places. *)
notation insert ("_ \<triangleright> _" [56,55] 55)

datatype (atoms: 'a) formula = 
    Atom 'a
  | Bot                              ("\<bottom>")  
  | Not "'a formula"                 ("\<^bold>\<not>")
  | And "'a formula" "'a formula"    (infix "\<^bold>\<and>" 68)
  | Or "'a formula" "'a formula"     (infix "\<^bold>\<or>" 68)
  | Imp "'a formula" "'a formula"    (infixr "\<^bold>\<rightarrow>" 68)
(* In a standard Isabelle/jEdit config, bold can be done with C-e rightarrow.
   I learned that way too late. *)
(* I'm not sure I'm happy about the definition of what is an atom.
   I'm inclined to treat 'a as our atom type and call an Atom k an "atom formula",
   but this goes against anything the literature does. So, Atom k will be an atom,
   k its index, but there are probably a few cases where I call 'a an atom\<dots> *)
(* like here: *)
lemma atoms_finite[simp,intro!]: "finite (atoms F)" by(induction F; simp)

primrec subformulae where
"subformulae \<bottom> = [\<bottom>]" |
"subformulae (Atom k) = [Atom k]" |
"subformulae (Not F) = Not F # subformulae F" |
"subformulae (And F G) = And F G # subformulae F @ subformulae G" |
"subformulae (Imp F G) = Imp F G # subformulae F @ subformulae G" |
"subformulae (Or F G) = Or F G # subformulae F @ subformulae G"

lemma atoms_are_subformulae: "Atom ` atoms F \<subseteq> set (subformulae F)"
  by (induction F) auto
    
lemma subsubformulae: "G \<in> set (subformulae F) \<Longrightarrow> H \<in> set (subformulae G) \<Longrightarrow> H \<in> set (subformulae F)"
  by(induction F; force)
    
lemma subformula_atoms: "G \<in> set (subformulae F) \<Longrightarrow> atoms G \<subseteq> atoms F"
  by(induction F) auto
    
lemma subformulae_self[simp,intro]: "F \<in> set (subformulae F)"
  by(induction F; simp)

lemma subformulas_in_subformulas:
  "G \<^bold>\<and> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "G \<^bold>\<or> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "G \<^bold>\<rightarrow> H \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F) \<and> H \<in> set (subformulae F)"
  "\<^bold>\<not> G \<in> set (subformulae F) \<Longrightarrow> G \<in> set (subformulae F)"
  by(fastforce elim: subsubformulae)+

lemma length_subformulae: "length (subformulae F) = size F" by(induction F; simp)

subsection\<open>Derived Connectives\<close>
    
definition Top ("\<top>") where
"\<top> \<equiv> \<bottom> \<^bold>\<rightarrow> \<bottom>"
lemma top_atoms_simp[simp]: "atoms \<top> = {}" unfolding Top_def by simp

primrec BigAnd :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<And>_") where
"\<^bold>\<And>Nil = (\<^bold>\<not>\<bottom>)" \<comment> \<open>essentially, it doesn't matter what I use here. But since I want to use this in CNFs, implication is not a nice thing to have.\<close> |
"\<^bold>\<And>(F#Fs) = F \<^bold>\<and> \<^bold>\<And>Fs"

lemma atoms_BigAnd[simp]: "atoms (\<^bold>\<And>Fs) = \<Union>(atoms ` set Fs)"
  by(induction Fs; simp)

primrec BigOr :: "'a formula list \<Rightarrow> 'a formula" ("\<^bold>\<Or>_") where
"\<^bold>\<Or>Nil = \<bottom>" |
"\<^bold>\<Or>(F#Fs) = F \<^bold>\<or> \<^bold>\<Or>Fs"

text\<open>Formulas are countable if their atoms are, and @{method countable_datatype} is really helpful with that.\<close> 
instance formula :: (countable) countable by countable_datatype

definition "prod_unions A B \<equiv> case A of (a,b) \<Rightarrow> case B of (c,d) \<Rightarrow> (a \<union> c, b \<union> d)"
primrec pn_atoms where
"pn_atoms (Atom A) = ({A},{})" |
"pn_atoms Bot = ({},{})" |
"pn_atoms (Not F) = prod.swap (pn_atoms F)" |
"pn_atoms (And F G) = prod_unions (pn_atoms F) (pn_atoms G)" |
"pn_atoms (Or F G) = prod_unions (pn_atoms F) (pn_atoms G)" |
"pn_atoms (Imp F G) = prod_unions (prod.swap (pn_atoms F)) (pn_atoms G)"
lemma pn_atoms_atoms: "atoms F = fst (pn_atoms F) \<union> snd (pn_atoms F)"
  by(induction F) (auto simp add: prod_unions_def split: prod.splits)

text\<open>A very trivial simplifier.
Does wonders as a postprocessor for the Harrison-style Craig interpolations.\<close>
context begin
definition "isstop F \<equiv> F = \<^bold>\<not>\<bottom> \<or> F = \<top>"
fun simplify_consts where
"simplify_consts (Atom k) = Atom k" |
"simplify_consts \<bottom> = \<bottom>" |
"simplify_consts (Not F) = (let S = simplify_consts F in case S of (Not G) \<Rightarrow> G | _ \<Rightarrow>
  if isstop S then \<bottom> else \<^bold>\<not> S)" |
"simplify_consts (And F G) = (let S = simplify_consts F; T = simplify_consts G in (
  if S = \<bottom> then \<bottom> else
  if isstop S then T \<comment> \<open>not \<open>\<top>\<close>, \<open>T\<close>\<close> else
  if T = \<bottom> then \<bottom> else
  if isstop T then S else
  if S = T then S else
  S \<^bold>\<and> T))" |
"simplify_consts (Or F G) = (let S = simplify_consts F; T = simplify_consts G in (
  if S = \<bottom> then T else
  if isstop S then \<top> else
  if T = \<bottom> then S else
  if isstop T then \<top> else
  if S = T then S else
  S \<^bold>\<or> T))" |
"simplify_consts (Imp F G) = (let S = simplify_consts F; T = simplify_consts G in (
  if S = \<bottom> then \<top> else
  if isstop S then T else
  if isstop T then \<top> else
  if T = \<bottom> then \<^bold>\<not> S else
  if S = T then \<top> else
  case S of Not H \<Rightarrow> (case T of Not I \<Rightarrow> 
    I \<^bold>\<rightarrow> H | _ \<Rightarrow> 
    H \<^bold>\<or> T) | _ \<Rightarrow>
    S \<^bold>\<rightarrow> T))"

lemma simplify_consts_size_le: "size (simplify_consts F) \<le> size F"
proof -
  have [simp]: "Suc (Suc 0) \<le> size F + size G" for F G :: "'a formula" by(cases F; cases G; simp)
  show ?thesis by(induction F; fastforce simp add: Let_def isstop_def Top_def split: formula.splits)
qed

lemma simplify_const: "atoms F = {} \<Longrightarrow> isstop (simplify_consts F) \<or> (simplify_consts F) = \<bottom>"
  by(induction F; fastforce simp add: Let_def isstop_def Top_def split: formula.splits)
value "(size \<top>, size (\<^bold>\<not>\<bottom>))" (* this is why I need isstop in this lemma and can't write simplify_consts
  in a way that this lemma can say \<in> {\<top>, \<bottom>} *)

end
  
(*
Here's a useful little function for testing a conjecture on "a few" examples: 
*)
fun all_formulas_of_size where
"all_formulas_of_size K 0 = {\<bottom>} \<union> Atom ` K" |
"all_formulas_of_size K (Suc n) = (
  let af = \<Union>(set [all_formulas_of_size K m. m \<leftarrow> [0..<Suc n]]) in
  (\<Union>F\<in>af.
    (\<Union>G\<in>af. if size F + size G \<le> Suc n then {And F G, Or F G, Imp F G} else {}) 
   \<union> (if size F \<le> Suc n then {Not F} else {})) 
  \<union> af)"
(* this set obviously grows exponentially (with a base of 5 approximately).
   size 7 produces 26032 formulas, which is probably the last value
   where I can test anything meaningfully with this implementation. *)

lemma all_formulas_of_size: "F \<in> all_formulas_of_size K n \<longleftrightarrow> (size F \<le> Suc n \<and> atoms F \<subseteq> K)" (is "?l \<longleftrightarrow> ?r")
proof -
  have rl: "?r \<Longrightarrow> ?l"
  proof(induction F arbitrary: n)
    case (Atom x)
    have *: "Atom x \<in> all_formulas_of_size K 0" using Atom by simp
    hence **: "Atom x \<in> \<Union> (all_formulas_of_size K ` set [0..<Suc m])" for m
      by (simp; metis atLeastLessThan_iff le_zero_eq not_le)
    thus ?case using Atom by(cases n; simp)
  next
    case Bot
    have *: "Bot \<in> all_formulas_of_size K 0" by simp
    hence **: "Bot \<in> \<Union> (all_formulas_of_size K ` set [0..<Suc m])" for m
      by (simp; metis atLeastLessThan_iff le_zero_eq not_le)
    then show ?case using Bot by(cases n; simp)
  next
    case (Not F)
    have *: "size F \<le> n" using Not by simp
    then obtain m where n[simp]: "n = Suc m" by (metis Suc_diff_1 formula.size_neq leD neq0_conv)
    with Not have IH: "F \<in> all_formulas_of_size K m" by simp
    then show ?case using * by(simp add: bexI[where x=F])
  next
    case (And F G)
    with And have *: "size F + size G \<le> n" by simp
    then obtain m where n[simp]: "n = Suc m"
      by (metis Suc_diff_1 add_is_0 formula.size_neq le_zero_eq neq0_conv)
    then obtain nF nG where nFG[simp]: "size F \<le> nF" "size G \<le> nG" "n = nF + nG"
      by (metis * add.assoc nat_le_iff_add order_refl)
    then obtain mF mG where mFG[simp]: "nF = Suc mF" "nG = Suc mG"
      by (metis Suc_diff_1 formula.size_neq leD neq0_conv)
    with And have IH: "F \<in> all_formulas_of_size K mF" "G \<in> all_formulas_of_size K mG" 
      using nFG by simp+
    let ?af = "\<Union>(set [all_formulas_of_size K m. m \<leftarrow> [0..<Suc m]])"
    have r: "F \<in> all_formulas_of_size K mF \<Longrightarrow> mF \<le> n \<Longrightarrow> F \<in> \<Union>(set (map (all_formulas_of_size K) [0..<Suc n]))"
      for F mF n by fastforce
    have af: "F \<in> ?af" "G \<in> ?af" using nFG(3) by(intro IH[THEN r]; simp)+
    have m: "F \<^bold>\<and> G \<in> (if size F + size G \<le> Suc m then {F \<^bold>\<and> G, F \<^bold>\<or> G, F \<^bold>\<rightarrow> G} else {})" using * by simp
    from IH * show ?case using af by(simp only: n all_formulas_of_size.simps Let_def, insert m) fast
  next
    case (Or F G) case (Imp F G) \<comment> \<open>analogous\<close> (*<*)
  next
    case (Or F G)
    with Or have *: "size F + size G \<le> n" by simp
    then obtain m where n[simp]: "n = Suc m"
      by (metis Suc_diff_1 add_is_0 formula.size_neq le_zero_eq neq0_conv)
    then obtain nF nG where nFG[simp]: "size F \<le> nF" "size G \<le> nG" "n = nF + nG"
      by (metis * add.assoc nat_le_iff_add order_refl)
    then obtain mF mG where mFG[simp]: "nF = Suc mF" "nG = Suc mG"
      by (metis Suc_diff_1 formula.size_neq leD neq0_conv)
    with Or have IH: "F \<in> all_formulas_of_size K mF" "G \<in> all_formulas_of_size K mG" 
      using nFG by simp+
    let ?af = "\<Union>(set [all_formulas_of_size K m. m \<leftarrow> [0..<Suc m]])"
    have r: "F \<in> all_formulas_of_size K mF \<Longrightarrow> mF \<le> n \<Longrightarrow> F \<in> \<Union>(set (map (all_formulas_of_size K) [0..<Suc n]))"
      for F mF n by fastforce
    have af: "F \<in> ?af" "G \<in> ?af" using nFG(3) by(intro IH[THEN r]; simp)+
    have m: "Or F G \<in> (if size F + size G \<le> Suc m then {F \<^bold>\<and> G, F \<^bold>\<or> G, F \<^bold>\<rightarrow> G} else {})" using * by simp
    from IH * show ?case using af by(simp only: n all_formulas_of_size.simps Let_def, insert m) fast
  next
    case (Imp F G)
    with Imp have *: "size F + size G \<le> n" by simp
    then obtain m where n[simp]: "n = Suc m"
      by (metis Suc_diff_1 add_is_0 formula.size_neq le_zero_eq neq0_conv)
    then obtain nF nG where nFG[simp]: "size F \<le> nF" "size G \<le> nG" "n = nF + nG"
      by (metis * add.assoc nat_le_iff_add order_refl)
    then obtain mF mG where mFG[simp]: "nF = Suc mF" "nG = Suc mG"
      by (metis Suc_diff_1 formula.size_neq leD neq0_conv)
    with Imp have IH: "F \<in> all_formulas_of_size K mF" "G \<in> all_formulas_of_size K mG" 
      using nFG by simp+
    let ?af = "\<Union>(set [all_formulas_of_size K m. m \<leftarrow> [0..<Suc m]])"
    have r: "F \<in> all_formulas_of_size K mF \<Longrightarrow> mF \<le> n \<Longrightarrow> F \<in> \<Union>(set (map (all_formulas_of_size K) [0..<Suc n]))"
      for F mF n by fastforce
    have af: "F \<in> ?af" "G \<in> ?af" using nFG(3) by(intro IH[THEN r]; simp)+
    have m: "Imp F G \<in> (if size F + size G \<le> Suc m then {F \<^bold>\<and> G, F \<^bold>\<or> G, F \<^bold>\<rightarrow> G} else {})" using * by simp
    from IH * show ?case using af by(simp only: n all_formulas_of_size.simps Let_def, insert m) fast
  (*>*)
  qed
  have lr: ?r if l: ?l 
  proof
    have *: "F \<in> all_formulas_of_size K x \<Longrightarrow> F \<in> all_formulas_of_size K (x + n)" for x n
      by(induction n; simp)
    show "size F \<le> Suc n" using l
      by(induction n; auto split: if_splits) (metis "*" le_SucI le_eq_less_or_eq le_iff_add)
    show "atoms F \<subseteq> K" using l
      proof(induction n arbitrary: F rule: less_induct)
        case (less x)
        then show ?case proof(cases x)
          case 0 with less show ?thesis by force
        next
          case (Suc y) with less show ?thesis 
            by(simp only: all_formulas_of_size.simps Let_def) (fastforce simp add: less_Suc_eq split: if_splits)
        qed
      qed
  qed
  from lr rl show ?thesis proof qed
qed
(* At first I thought: why would I prove anything about all_formulas_of_size, I only want to test a conjecture with it.
   Guess why: it was broken.
   Granted, I spent too much time on this. *)

end
