section \<open>Robbins Conjecture\<close>

theory Robbins_Conjecture
imports Main
begin

text \<open>The document gives a formalization of the proof of the Robbins 
        conjecture, following A. Mann, \emph{A Complete Proof of the 
        Robbins Conjecture}, 2003, DOI 10.1.1.6.7838\<close>

section \<open>Axiom Systems\<close>

text \<open>The following presents several axiom systems that shall be under study.

        The first axiom sets common systems that underly all of 
        the systems we shall be looking at.

        The second system is a reformulation of Boolean algebra.  We shall 
        follow pages 7--8 in S. Koppelberg. \emph{General Theory of Boolean 
        Algebras}, Volume 1 of \emph{Handbook of Boolean Algebras}. North 
        Holland, 1989. Note that our formulation deviates slightly from this, 
        as we only provide one distribution axiom, as the dual is redundant.

        The third system is Huntington's algebra and the fourth system is 
        Robbins' algebra.

        Apart from the common system, all of these systems are demonstrated 
        to be equivalent to the library formulation of Boolean algebra, under 
        appropriate interpretation.\<close>

subsection \<open>Common Algebras\<close>

class common_algebra = uminus +
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)
  fixes bot :: "'a" ("\<bottom>")
  fixes top :: "'a" ("\<top>")
  assumes sup_assoc: "x \<squnion> (y \<squnion> z) = (x \<squnion> y) \<squnion> z"
  assumes sup_comm: "x \<squnion> y = y \<squnion> x" 

context common_algebra begin

definition less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
   "x \<sqsubseteq> y = (x \<squnion> y = y)"
definition less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
   "x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)"
definition minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "-" 65) where 
   "minus x y = (x \<sqinter> - y)"

(* We shall need some object in order to define falsum and verum *)
definition secret_object1 :: "'a" ("\<iota>") where
  "\<iota> = (SOME x. True)"

end

class ext_common_algebra = common_algebra +
  assumes inf_eq: "x \<sqinter> y = -(- x \<squnion> - y)"
  assumes top_eq: "\<top> = \<iota> \<squnion> - \<iota>"
  assumes bot_eq: "\<bottom> = -(\<iota> \<squnion> - \<iota>)"

subsection \<open>Boolean Algebra\<close>

class boolean_algebra_II = 
  common_algebra +
  assumes inf_comm: "x \<sqinter> y = y \<sqinter> x"
  assumes inf_assoc: "x \<sqinter> (y \<sqinter> z) = (x \<sqinter> y) \<sqinter> z"
  assumes sup_absorb: "x \<squnion> (x \<sqinter> y) = x"
  assumes inf_absorb: "x \<sqinter> (x \<squnion> y) = x"
  assumes sup_inf_distrib1: "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  assumes sup_compl: "x \<squnion> - x = \<top>"
  assumes inf_compl: "x \<sqinter> - x = \<bottom>"

subsection \<open>Huntington's Algebra\<close>

class huntington_algebra = ext_common_algebra +
  assumes huntington: "- (-x \<squnion> -y) \<squnion> - (-x \<squnion>  y) = x"

subsection \<open>Robbins' Algebra\<close>

class robbins_algebra = ext_common_algebra +
  assumes robbins: "- (- (x \<squnion> y) \<squnion> - (x \<squnion> -y)) = x"

section \<open>Equivalence\<close>

text \<open>With our axiom systems defined, we turn to providing equivalence 
        results between them.  
        
        We shall begin by illustrating equivalence for our formulation and 
        the library formulation of Boolean algebra.\<close>

subsection \<open>Boolean Algebra\<close>

text \<open>The following provides the canonical definitions for order and 
        relative complementation for Boolean algebras.  These are necessary 
        since the Boolean algebras presented in the Isabelle/HOL library have 
        a lot of structure, while our formulation is considerably simpler.
     
       Since our formulation of Boolean algebras is considerably simple, it is 
       easy to show that the library instantiates our axioms.\<close>

context boolean_algebra_II begin

lemma boolean_II_is_boolean:
   "class.boolean_algebra minus uminus (\<sqinter>) (\<sqsubseteq>) (\<sqsubset>) (\<squnion>) \<bottom> \<top>"
apply unfold_locales
apply (metis inf_absorb inf_assoc inf_comm inf_compl
             less_def less_eq_def minus_def 
             sup_absorb sup_assoc sup_comm
             sup_compl sup_inf_distrib1
             sup_absorb inf_comm)+
done

end

context boolean_algebra begin

lemma boolean_is_boolean_II:
  "class.boolean_algebra_II uminus inf sup bot top"
apply unfold_locales
apply (metis sup_assoc sup_commute sup_inf_absorb sup_compl_top
             inf_assoc inf_commute inf_sup_absorb inf_compl_bot
             sup_inf_distrib1)+
done

end

subsection \<open>Huntington Algebra\<close>

text \<open>We shall illustrate here that all Boolean algebra using our 
        formulation are Huntington algebras, and illustrate that every 
        Huntington algebra may be interpreted as a Boolean algebra.

        Since the Isabelle/HOL library has good automation, it is convenient 
        to first show that the library instances Huntington algebras to exploit 
        previous results, and then use our previously derived correspondence.\<close>

context boolean_algebra begin
lemma boolean_is_huntington:
  "class.huntington_algebra uminus inf sup bot top"
apply unfold_locales
apply (metis double_compl inf_sup_distrib1 inf_top_right
             compl_inf inf_commute inf_compl_bot  
             compl_sup sup_commute sup_compl_top 
             sup_compl_top sup_assoc)+
done

end

context boolean_algebra_II begin

lemma boolean_II_is_huntington:
  "class.huntington_algebra uminus (\<sqinter>) (\<squnion>) \<bottom> \<top>"
proof -
  interpret boolean: 
    boolean_algebra minus uminus "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<squnion>)" \<bottom> \<top>
      by (fact boolean_II_is_boolean)
  show ?thesis by (simp add: boolean.boolean_is_huntington)
qed

end

context huntington_algebra begin

lemma huntington_id: "x \<squnion> -x = -x \<squnion> -(-x)"
proof -
  from huntington have 
  "x \<squnion> -x = -(-x \<squnion> -(-(-x))) \<squnion> -(-x \<squnion> -(-x)) \<squnion> 
             (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-x) \<squnion> -(-x)))"
    by simp
  also from sup_comm have 
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -(-(-x))) \<squnion> 
        (-(-(-x) \<squnion> -x) \<squnion> -(-(-(-x)) \<squnion> -x))"  
    by simp
  also from sup_assoc have 
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> 
        (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-x) \<squnion> -x)) \<squnion> 
       -(-(-(-x)) \<squnion> -x)"  
    by simp
  also from sup_comm have 
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> 
        (-(-(-x) \<squnion> -x) \<squnion> -(-(-x) \<squnion> -(-(-x)))) \<squnion> 
       -(-(-(-x)) \<squnion> -x)"  
    by simp
  also from sup_assoc have 
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -x) \<squnion> 
        (-(-(-x) \<squnion> -(-(-x))) \<squnion> -(-(-(-x)) \<squnion> -x))"  
    by simp
  also from sup_comm have 
  "\<dots> = -(-(-x) \<squnion> -(-x)) \<squnion> -(-(-x) \<squnion> -x) \<squnion> 
        (-(-(-(-x)) \<squnion> -(-x)) \<squnion> -(-(-(-x)) \<squnion> -x))"
    by simp
  also from huntington have 
  "\<dots> = -x \<squnion> -(-x)"
    by simp
  finally show ?thesis by simp
qed

lemma dbl_neg: "- (-x) = x"
apply (metis huntington huntington_id sup_comm)
done

lemma towards_sup_compl: "x \<squnion> -x = y \<squnion> -y"
proof -
   from huntington have 
  "x \<squnion> -x = -(-x \<squnion> -(-y)) \<squnion> -(-x \<squnion> -y) \<squnion> (-(-(-x) \<squnion> -(-y)) \<squnion> -(-(-x) \<squnion> -y))"
     by simp
   also from sup_comm have 
  "\<dots> = -(-(-y) \<squnion> -x) \<squnion> -(-y \<squnion> -x) \<squnion> (-(-y \<squnion> -(-x)) \<squnion> -(-(-y) \<squnion> -(-x)))"
     by simp
   also from sup_assoc have 
  "\<dots> = -(-(-y) \<squnion> -x) \<squnion> (-(-y \<squnion> -x) \<squnion> -(-y \<squnion> -(-x))) \<squnion> -(-(-y) \<squnion> -(-x))"
     by simp
   also from sup_comm have
  "\<dots> = -(-y \<squnion> -(-x)) \<squnion> -(-y \<squnion> -x) \<squnion> -(-(-y) \<squnion> -x) \<squnion> -(-(-y) \<squnion> -(-x))"
     by simp
   also from sup_assoc have 
  "\<dots> = -(-y \<squnion> -(-x)) \<squnion> -(-y \<squnion> -x) \<squnion> (-(-(-y) \<squnion> -x) \<squnion> -(-(-y) \<squnion> -(-x)))"
     by simp
   also from sup_comm have 
  "\<dots> = -(-y \<squnion> -(-x)) \<squnion> -(-y \<squnion> -x) \<squnion> (-(-(-y) \<squnion> -(-x)) \<squnion> -(-(-y) \<squnion> -x))"
     by simp
   also from huntington have 
  "y \<squnion> -y = \<dots>" by simp
   finally show ?thesis by simp
qed

lemma sup_compl: "x \<squnion> -x = \<top>"
by (simp add: top_eq towards_sup_compl)

lemma towards_inf_compl: "x \<sqinter> -x = y \<sqinter> -y"
by (metis dbl_neg inf_eq sup_comm sup_compl)

lemma inf_compl: "x \<sqinter> -x = \<bottom>"
by (metis dbl_neg sup_comm bot_eq towards_inf_compl inf_eq)

lemma towards_idem: "\<bottom> = \<bottom> \<squnion> \<bottom>"
by (metis dbl_neg huntington inf_compl inf_eq sup_assoc sup_comm sup_compl)

lemma sup_ident: "x \<squnion> \<bottom> = x"
by (metis dbl_neg huntington inf_compl inf_eq sup_assoc 
          sup_comm sup_compl towards_idem)

lemma inf_ident: "x \<sqinter> \<top> = x"
by (metis dbl_neg inf_compl inf_eq sup_ident sup_comm sup_compl)

lemma sup_idem: "x \<squnion> x = x"
by (metis dbl_neg huntington inf_compl inf_eq sup_ident sup_comm sup_compl)

lemma inf_idem: "x \<sqinter> x = x"
by (metis dbl_neg inf_eq sup_idem)

lemma sup_nil: "x \<squnion> \<top> = \<top>"
by (metis sup_idem sup_assoc sup_comm sup_compl)

lemma inf_nil: "x \<sqinter> \<bottom> = \<bottom>"
by (metis dbl_neg inf_compl inf_eq sup_nil sup_comm sup_compl)

lemma sup_absorb: "x \<squnion> x \<sqinter> y = x"
by (metis huntington inf_eq sup_idem sup_assoc sup_comm)

lemma inf_absorb: "x \<sqinter> (x \<squnion> y) = x"
by (metis dbl_neg inf_eq sup_absorb)

lemma partition: "x \<sqinter> y \<squnion> x \<sqinter> -y = x"
by (metis dbl_neg huntington inf_eq sup_comm)

lemma demorgans1: "-(x \<sqinter> y) = -x \<squnion> -y"
by (metis dbl_neg inf_eq)

lemma demorgans2: "-(x \<squnion> y) = -x \<sqinter> -y"
by (metis dbl_neg inf_eq)

lemma inf_comm: "x \<sqinter> y = y \<sqinter> x"
by (metis inf_eq sup_comm)

lemma inf_assoc: "x \<sqinter> (y \<sqinter> z) = x \<sqinter> y \<sqinter> z"
by (metis dbl_neg inf_eq sup_assoc)

lemma inf_sup_distrib1: "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof -
  from partition have 
  "x \<sqinter> (y \<squnion> z) = x \<sqinter> (y \<squnion> z) \<sqinter> y \<squnion> x \<sqinter> (y \<squnion> z) \<sqinter> -y" ..
  also from inf_assoc have
  "\<dots> = x \<sqinter> ((y \<squnion> z) \<sqinter> y) \<squnion> x \<sqinter> (y \<squnion> z) \<sqinter> -y" by simp
  also from inf_comm have
  "\<dots> = x \<sqinter> (y \<sqinter> (y \<squnion> z)) \<squnion> x \<sqinter> (y \<squnion> z) \<sqinter> -y" by simp
  also from inf_absorb have
  "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> (y \<squnion> z) \<sqinter> -y)" by simp
  also from partition have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> (y \<squnion> z) \<sqinter> -y \<sqinter> z) \<squnion> (x \<sqinter> (y \<squnion> z) \<sqinter> -y \<sqinter> -z))" by simp
  also from inf_assoc have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z))) \<squnion> (x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> -z))))" by simp
  also from demorgans2 have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z))) \<squnion> (x \<sqinter> ((y \<squnion> z) \<sqinter> -(y \<squnion> z))))" by simp
  also from inf_compl have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z))) \<squnion> (x \<sqinter> \<bottom>))" by simp
  also from inf_nil have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z))) \<squnion> \<bottom>)" by simp
  also from sup_idem have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       ((x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z))) \<squnion> \<bottom>)" by simp
  also from sup_ident have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       (x \<sqinter> ((y \<squnion> z) \<sqinter> (-y \<sqinter> z)))" by simp
  also from inf_comm have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       (x \<sqinter> ((-y \<sqinter> z) \<sqinter> (y \<squnion> z)))" by simp
  also from sup_comm have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       (x \<sqinter> ((-y \<sqinter> z) \<sqinter> (z \<squnion> y)))" by simp
  also from inf_assoc have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> (y \<sqinter> z)) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> 
       (x \<sqinter> (-y \<sqinter> (z \<sqinter> (z \<squnion> y))))" by simp
  also from inf_absorb have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> (y \<sqinter> z)) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> (x \<sqinter> (-y \<sqinter> z))" 
     by simp
  also from inf_comm have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> (z \<sqinter> y)) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> (x \<sqinter> (z \<sqinter> -y))" 
     by simp
  also from sup_assoc have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> ((x \<sqinter> (z \<sqinter> y)) \<squnion> (x \<sqinter> y \<sqinter> -z))) \<squnion> (x \<sqinter> (z \<sqinter> -y))" 
     by simp
  also from sup_comm have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> ((x \<sqinter> y \<sqinter> -z) \<squnion> (x \<sqinter> (z \<sqinter> y)))) \<squnion> (x \<sqinter> (z \<sqinter> -y))" 
     by simp
  also from sup_assoc have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> ((x \<sqinter> (z \<sqinter> y)) \<squnion> (x \<sqinter> (z \<sqinter> -y)))" 
     by simp
  also from inf_assoc have
  "\<dots> = ((x \<sqinter> y \<sqinter> z) \<squnion> (x \<sqinter> y \<sqinter> -z)) \<squnion> ((x \<sqinter> z \<sqinter> y) \<squnion> (x \<sqinter> z \<sqinter> -y))" by simp
  also from partition have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by simp
  finally show ?thesis by simp
qed

lemma sup_inf_distrib1:
  "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof -
  from dbl_neg have
  "x \<squnion> (y \<sqinter> z) = -(-(-(-x) \<squnion> (y \<sqinter> z)))" by simp
  also from inf_eq have
  "\<dots> = -(-x \<sqinter> (-y \<squnion> -z))" by simp
  also from inf_sup_distrib1 have
  "\<dots> = -((-x \<sqinter> -y) \<squnion> (-x \<sqinter> -z))" by simp
  also from demorgans2 have
  "\<dots> = -(-x \<sqinter> -y) \<sqinter> -(-x \<sqinter> -z)" by simp
  also from demorgans1 have
  "\<dots> = (-(-x) \<squnion> -(-y)) \<sqinter> (-(-x) \<squnion> -(-z))" by simp
  also from dbl_neg have
  "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by simp
  finally show ?thesis by simp
qed

lemma huntington_is_boolean_II:
   "class.boolean_algebra_II uminus (\<sqinter>) (\<squnion>) \<bottom> \<top>"
apply unfold_locales
apply (metis inf_comm inf_assoc sup_absorb 
             inf_absorb sup_inf_distrib1 
             sup_compl inf_compl)+
done

lemma huntington_is_boolean:
   "class.boolean_algebra minus uminus (\<sqinter>) (\<sqsubseteq>) (\<sqsubset>) (\<squnion>) \<bottom> \<top>"
proof -
  interpret boolean_II: 
    boolean_algebra_II uminus "(\<sqinter>)" "(\<squnion>)" \<bottom> \<top>
      by (fact huntington_is_boolean_II)
  show ?thesis by (simp add: boolean_II.boolean_II_is_boolean)
qed
end

subsection \<open>Robbins' Algebra\<close>

context boolean_algebra begin
lemma boolean_is_robbins:
  "class.robbins_algebra uminus inf sup bot top"
apply unfold_locales
apply (metis sup_assoc sup_commute compl_inf double_compl sup_compl_top 
             inf_compl_bot diff_eq sup_bot_right sup_inf_distrib1)+
done
end

context boolean_algebra_II begin
lemma boolean_II_is_robbins:
  "class.robbins_algebra uminus inf sup bot top"
proof -
  interpret boolean: 
    boolean_algebra minus uminus "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<squnion>)" \<bottom> \<top>
      by (fact boolean_II_is_boolean)
  show ?thesis by (simp add: boolean.boolean_is_robbins)
qed
end

context huntington_algebra begin
lemma huntington_is_robbins:
  "class.robbins_algebra uminus inf sup bot top"
proof -
  interpret boolean: 
    boolean_algebra minus uminus "(\<sqinter>)" "(\<sqsubseteq>)" "(\<sqsubset>)" "(\<squnion>)" \<bottom> \<top>
      by (fact huntington_is_boolean)
  show ?thesis by (simp add: boolean.boolean_is_robbins)
qed
end

text \<open>Before diving into the proof that the Robbins algebra is Boolean,
        we shall present some shorthand machinery\<close>

context common_algebra begin

(* Iteration Machinery/Shorthand *)

primrec copyp :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<otimes>" 80)
where 
  copyp_0:   "0 \<otimes> x = x"
| copyp_Suc: "(Suc k) \<otimes> x = (k \<otimes> x) \<squnion> x"

no_notation 
  Product_Type.Times (infixr "\<times>" 80)

primrec copy :: "nat \<Rightarrow> 'a \<Rightarrow> 'a" (infix "\<times>" 85)
where
  "0 \<times> x = x"
| "(Suc k) \<times> x = k \<otimes> x"

(* Theorems for translating shorthand into syntax *)

lemma one:  "1 \<times> x = x"
proof -
  have       "1 = Suc(0)" by arith 
  hence      "1 \<times> x = Suc(0) \<times> x" by metis
  also have  "\<dots> = x" by simp
  finally show ?thesis by simp
qed

lemma two:  "2 \<times> x = x \<squnion> x"
proof -
  have       "2 = Suc(Suc(0))" by arith 
  hence      "2 \<times> x = Suc(Suc(0)) \<times> x" by metis
  also have  "\<dots> = x \<squnion> x" by simp
  finally show ?thesis by simp
qed

lemma three:  "3 \<times> x = x \<squnion> x \<squnion> x"
proof -
   have       "3 = Suc(Suc(Suc(0)))" by arith 
   hence      "3 \<times> x = Suc(Suc(Suc(0))) \<times> x" by metis
   also have  "\<dots> = x \<squnion> x \<squnion> x" by simp
   finally show ?thesis by simp
qed

lemma four:  "4 \<times> x = x \<squnion> x \<squnion> x \<squnion> x"
proof -
  have       "4 = Suc(Suc(Suc(Suc(0))))" by arith 
  hence      "4 \<times> x = Suc(Suc(Suc(Suc(0)))) \<times> x" by metis
  also have  "\<dots> = x \<squnion> x \<squnion> x \<squnion> x" by simp
  finally show ?thesis by simp
qed

lemma five:  "5 \<times> x = x \<squnion> x \<squnion> x \<squnion> x \<squnion> x"
proof -
  have       "5 = Suc(Suc(Suc(Suc(Suc(0)))))" by arith 
  hence      "5 \<times> x = Suc(Suc(Suc(Suc(Suc(0))))) \<times> x" by metis
  also have  "\<dots> = x \<squnion> x \<squnion> x \<squnion> x \<squnion> x" by simp
  finally show ?thesis by simp
qed

lemma six:  "6 \<times> x = x \<squnion> x \<squnion> x \<squnion> x \<squnion> x \<squnion> x"
proof -
  have       "6 = Suc(Suc(Suc(Suc(Suc(Suc(0))))))" by arith 
  hence      "6 \<times> x = Suc(Suc(Suc(Suc(Suc(Suc(0)))))) \<times> x" by metis
  also have  "\<dots> = x \<squnion> x \<squnion> x \<squnion> x \<squnion> x \<squnion> x" by simp
  finally show ?thesis by simp
qed

(* Distribution Laws *)

lemma copyp_distrib: "k \<otimes> (x \<squnion> y) = (k \<otimes> x) \<squnion> (k \<otimes> y)"
proof (induct k)
  case 0 show ?case by simp
  case Suc thus ?case by (simp, metis sup_assoc sup_comm)
qed

corollary copy_distrib: "k \<times> (x \<squnion> y) = (k \<times> x) \<squnion> (k \<times> y)"
by (induct k, (simp add: sup_assoc sup_comm copyp_distrib)+)

lemma copyp_arith: "(k + l + 1) \<otimes> x = (k \<otimes> x) \<squnion> (l \<otimes> x)"
proof (induct l)
  case 0 have "k + 0 + 1 = Suc(k)" by arith
    thus ?case by simp
  case (Suc l) note ind_hyp = this
    have "k + Suc(l) + 1 = Suc(k + l + 1)" by arith+
    hence "(k + Suc(l) + 1) \<otimes> x = (k + l + 1) \<otimes> x \<squnion> x" by (simp add: ind_hyp)
    also from ind_hyp have 
          "\<dots> = (k \<otimes> x) \<squnion> (l \<otimes> x) \<squnion> x" by simp
    also note sup_assoc
    finally show ?case by simp
qed

lemma copy_arith: 
   assumes "k \<noteq> 0" and "l \<noteq> 0"
     shows "(k + l) \<times> x = (k \<times> x) \<squnion> (l \<times> x)"
using assms
proof -
  from assms have "\<exists> k'. Suc(k') = k" 
              and "\<exists> l'. Suc(l') = l" by arith+
  from this obtain k' l' where A: "Suc(k') = k"
                           and B: "Suc(l') = l" by fast+
  from this have A1: "k \<times> x = k' \<otimes> x"
             and B1: "l \<times> x = l' \<otimes> x" by fastforce+
  from A B have "k + l = Suc(k' + l' + 1)" by arith
  hence "(k + l) \<times> x = (k' + l' + 1) \<otimes> x" by simp
  also from copyp_arith have  
        "\<dots> = k' \<otimes> x \<squnion> l' \<otimes> x" by fast
  also from A1 B1 have
        "\<dots> = k \<times> x \<squnion> l \<times> x" by fastforce
  finally show ?thesis by simp
qed

end

text \<open>The theorem asserting all Robbins algebras are Boolean  
       comes in 6 movements.
       
       First: The Winker identity is proved.

       Second: Idempotence for a particular object is proved.  
       Note that falsum is defined in terms of this object.

       Third: An identity law for falsum is derived.

       Fourth: Idempotence for supremum is derived.

       Fifth: The double negation law is proven

       Sixth: Robbin's algebras are proven to be Huntington Algebras.\<close>

context robbins_algebra begin

definition secret_object2 :: "'a" ("\<alpha>") where
  "\<alpha> = -(-(\<iota> \<squnion> \<iota> \<squnion> \<iota>) \<squnion> \<iota>)"
definition secret_object3 :: "'a" ("\<beta>") where
  "\<beta> = \<iota> \<squnion> \<iota>"
definition secret_object4 :: "'a" ("\<delta>") where
  "\<delta> = \<beta> \<squnion> (-(\<alpha> \<squnion> -\<beta>) \<squnion> -(\<alpha> \<squnion> -\<beta>))"
definition secret_object5 :: "'a" ("\<gamma>") where
  "\<gamma> = \<delta> \<squnion> -(\<delta> \<squnion> -\<delta>)"
definition winker_object :: "'a" ("\<rho>") where
  "\<rho> = \<gamma> \<squnion> \<gamma> \<squnion> \<gamma>"
definition fake_bot :: "'a" ("\<bottom>\<bottom>") where
  "\<bottom>\<bottom> = -(\<rho> \<squnion> -\<rho>)"

(* Towards Winker's Identity *)

(* These lemmas are due to Alan Mann *)

lemma robbins2: "y = -(-(-x \<squnion> y) \<squnion> -(x \<squnion> y))"
  by (metis robbins sup_comm)

lemma mann0: "-(x \<squnion> y) = -(-(-(x \<squnion> y) \<squnion> -x \<squnion> y) \<squnion> y)"
  by (metis robbins sup_comm sup_assoc)

lemma mann1: "-(-x \<squnion> y) = -(-(-(-x \<squnion> y) \<squnion> x \<squnion> y) \<squnion> y)"
  by (metis robbins sup_comm sup_assoc)

lemma mann2: "y = -(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y))"
  by (metis mann1 robbins sup_comm sup_assoc)

lemma mann3: "z = -(-(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y) \<squnion> z) \<squnion> -(y \<squnion> z))"
proof -
  let ?w = "-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y)"
  from robbins[where x="z" and y="?w"] sup_comm mann2 
  have "z = -(-(y \<squnion> z) \<squnion> -(?w \<squnion> z))" by metis
  thus ?thesis by (metis sup_comm)
qed

lemma mann4: "-(y \<squnion> z) = 
  -(-(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y) \<squnion> -(y \<squnion> z) \<squnion> z) \<squnion> z)"
proof -
 from robbins2[where x="-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y) \<squnion> z" 
                 and y="-(y \<squnion> z)"]
      mann3[where x="x" and y="y" and z="z"]
 have "-(y \<squnion> z) = 
       -(z \<squnion> -(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> -(-x \<squnion> y) \<squnion> z \<squnion> -(y \<squnion> z)))" 
   by metis
 with sup_comm sup_assoc show ?thesis by metis
qed

lemma mann5: "u = 
-(-(-(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> 
      -(-x \<squnion> y) \<squnion> - (y \<squnion> z) \<squnion> z) \<squnion> z \<squnion> u) \<squnion> 
  -(-(y \<squnion> z) \<squnion> u))"
using robbins2[where x="-(-(-(-x \<squnion> y) \<squnion> x \<squnion> y \<squnion> y) \<squnion> 
                          -(-x \<squnion> y) \<squnion> -(y \<squnion> z) \<squnion> z) \<squnion> z"
                 and y="u"]
      mann4[where x=x and y=y and z=z] 
      sup_comm
by metis

lemma mann6: 
"-(- 3\<times>x \<squnion> x) = -(-(-(- 3\<times>x \<squnion> x) \<squnion> - 3\<times>x) \<squnion> -(-(- 3\<times>x \<squnion> x) \<squnion> 5\<times>x))"
proof -
  have "3+2=(5::nat)" and "3\<noteq>(0::nat)" and "2\<noteq>(0::nat)" by arith+
  with copy_arith have \<heartsuit>: "3\<times>x \<squnion> 2\<times>x = 5\<times>x" by metis
  let ?p = "-(- 3\<times>x \<squnion> x)"
  { fix q
    from sup_comm have
    "-(q \<squnion> 5\<times>x) = -(5\<times>x \<squnion> q)" by metis
    also from \<heartsuit> mann0[where x="3\<times>x" and y="q \<squnion> 2\<times>x"] sup_assoc sup_comm have
    "\<dots> = -(-(-(3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> - 3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> (q \<squnion> 2\<times>x))"
      by metis
    also from sup_assoc have
    "\<dots> = -(-(-((3\<times>x \<squnion> q) \<squnion> 2\<times>x) \<squnion> - 3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> (q \<squnion> 2\<times>x))" by metis
    also from sup_comm have
    "\<dots> = -(-(-((q \<squnion> 3\<times>x) \<squnion> 2\<times>x) \<squnion> - 3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> (q \<squnion> 2\<times>x))" by metis
    also from sup_assoc have
    "\<dots> = -(-(-(q \<squnion> (3\<times>x \<squnion> 2\<times>x)) \<squnion> - 3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> (q \<squnion> 2\<times>x))" by metis
    also from \<heartsuit> have
    "\<dots> = -(-(-(q \<squnion> 5\<times>x) \<squnion> - 3\<times>x \<squnion> (q \<squnion> 2\<times>x)) \<squnion> (q \<squnion> 2\<times>x))" by metis
    also from sup_assoc have
    "\<dots> = -(-(-(q \<squnion> 5\<times>x) \<squnion> (- 3\<times>x \<squnion> q) \<squnion> 2\<times>x) \<squnion> (q \<squnion> 2\<times>x))" by metis
    also from sup_comm have
    "\<dots> = -(-(-(q \<squnion> 5\<times>x) \<squnion> (q \<squnion> - 3\<times>x) \<squnion> 2\<times>x) \<squnion> (2\<times>x \<squnion> q))" by metis
    also from sup_assoc have
    "\<dots> = -(-(-(q \<squnion> 5\<times>x) \<squnion> q \<squnion> - 3\<times>x \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> q)" by metis
    finally have 
    "-(q \<squnion> 5\<times>x) = -(-(-(q \<squnion> 5\<times>x) \<squnion> q \<squnion> - 3\<times>x \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> q)" by simp
  } hence \<spadesuit>: 
    "-(?p \<squnion> 5\<times>x) = -(-(-(?p \<squnion> 5\<times>x) \<squnion> ?p \<squnion> - 3\<times>x \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> ?p)"
    by simp

  from mann5[where x="3\<times>x" and y="x" and z="2\<times>x" and u="?p"] 
       sup_assoc three[where x=x] five[where x=x] have
  "?p = 
   -(-(-(-(?p \<squnion> 5\<times>x) \<squnion> ?p \<squnion> -(x \<squnion> 2\<times>x) \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> ?p) \<squnion>
     -(-(x \<squnion> 2\<times>x) \<squnion> ?p))" by metis
  also from sup_comm have
  "\<dots> = 
   -(-(-(-(?p \<squnion> 5\<times>x) \<squnion> ?p \<squnion> -(2\<times>x \<squnion> x) \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> ?p) \<squnion>
     -(-(2\<times>x \<squnion> x) \<squnion> ?p))" by metis
  also from two[where x=x] three[where x=x] have
  "\<dots> = 
   -(-(-(-(?p \<squnion> 5\<times>x) \<squnion> ?p \<squnion> - 3\<times>x \<squnion> 2\<times>x) \<squnion> 2\<times>x \<squnion> ?p) \<squnion>
     -(- 3\<times>x \<squnion> ?p))" by metis
  also from \<spadesuit> have "\<dots> = -(-(?p \<squnion> 5\<times>x) \<squnion> -(- 3\<times>x \<squnion> ?p))" by simp
  also from sup_comm have "\<dots> = -(-(?p \<squnion> 5\<times>x) \<squnion> -(?p \<squnion> - 3\<times>x))" by simp
  also from sup_comm have "\<dots> = -(-(?p \<squnion> - 3\<times>x) \<squnion> -(?p \<squnion> 5\<times>x))" by simp
  finally show ?thesis .
qed

lemma mann7:
"- 3\<times>x = -(-(- 3\<times>x \<squnion> x) \<squnion> 5\<times>x)"
proof -
  let ?p = "-(- 3\<times>x \<squnion> x)"
  let ?q = "?p \<squnion> - 3\<times>x"
  let ?r = "-(?p \<squnion> 5\<times>x)"
  from robbins2[where x="?q"
                  and y="?r"]
       mann6[where x=x]
  have "?r = - (?p \<squnion> - (?q \<squnion> ?r))" by simp
  also from sup_comm have "\<dots> = - (- (?q \<squnion> ?r) \<squnion> ?p)" by simp
  also from sup_comm have "\<dots> = - (- (?r \<squnion> ?q) \<squnion> ?p)" by simp
  finally have \<spadesuit>: "?r = - (- (?r \<squnion> ?q) \<squnion> ?p)" .
  from mann3[where x="3\<times>x" and y="x" and z="- 3\<times>x"]
       sup_comm have
       "- 3\<times>x = -(-(-(?p \<squnion> 3\<times>x \<squnion> x \<squnion> x) \<squnion> ?p \<squnion> - 3\<times>x) \<squnion> ?p)" by metis
  also from sup_assoc have
       "\<dots> = -(-(-(?p \<squnion> (3\<times>x \<squnion> x \<squnion> x)) \<squnion> ?q) \<squnion> ?p)" by metis
  also from three[where x=x] five[where x=x] have
       "\<dots> = -(-(?r \<squnion> ?q) \<squnion> ?p)" by metis
  finally have "- 3\<times>x = -(-(?r \<squnion> ?q) \<squnion> ?p)" by metis
  with \<spadesuit> show ?thesis by simp
qed

lemma mann8:
"-(- 3\<times>x \<squnion> x) \<squnion> 2\<times>x = -(-(-(- 3\<times>x \<squnion> x) \<squnion> - 3\<times>x \<squnion> 2\<times>x) \<squnion> - 3\<times>x)"
(is "?lhs = ?rhs")
proof -
  let ?p = "-(- 3\<times>x \<squnion> x)"
  let ?q = "?p \<squnion> 2\<times>x"
  let ?r = "3\<times>x"
  have "3+2=(5::nat)" and "3\<noteq>(0::nat)" and "2\<noteq>(0::nat)" by arith+
  with copy_arith have \<heartsuit>: "3\<times>x \<squnion> 2\<times>x = 5\<times>x" by metis
  from robbins2[where x="?r" and y="?q"] and sup_assoc
  have "?q = -(-(- 3\<times>x \<squnion> ?q) \<squnion> -(3\<times>x \<squnion> ?p \<squnion> 2\<times>x))" by metis
  also from sup_comm have 
       "\<dots> = -(-(?q \<squnion> - 3\<times>x) \<squnion> -(?p \<squnion> 3\<times>x \<squnion> 2\<times>x))" by metis
  also from \<heartsuit> sup_assoc have
       "\<dots> = -(-(?q \<squnion> - 3\<times>x) \<squnion> -(?p \<squnion> 5\<times>x))" by metis
  also from mann7[where x=x] have 
       "\<dots> = -(-(?q \<squnion> - 3\<times>x) \<squnion> - 3\<times>x)" by metis
  also from sup_assoc have
       "\<dots> = -(-(?p \<squnion> (2\<times>x  \<squnion> - 3\<times>x)) \<squnion> - 3\<times>x)" by metis
  also from sup_comm have
       "\<dots> = -(-(?p \<squnion> (- 3\<times>x  \<squnion> 2\<times>x)) \<squnion> - 3\<times>x)" by metis
  also from sup_assoc have
       "\<dots> = ?rhs" by metis
  finally show ?thesis by simp
qed

lemma mann9: "x = -(-(- 3\<times>x \<squnion> x) \<squnion> - 3\<times>x )"
proof -
  let ?p = "-(- 3\<times>x \<squnion> x)"
  let ?q = "?p \<squnion> 4\<times>x"
  have "4+1=(5::nat)" and "1\<noteq>(0::nat)" and "4\<noteq>(0::nat)" by arith+
  with copy_arith one have \<heartsuit>: "4\<times>x \<squnion> x = 5\<times>x" by metis
  with sup_assoc robbins2[where y=x and x="?q"]
  have "x = -(-(-?q \<squnion> x) \<squnion> -(?p \<squnion> 5\<times>x))" by metis
  with mann7 have "x = -(-(-?q \<squnion> x) \<squnion> - 3\<times>x)" by metis
  moreover
  have "3+1=(4::nat)" and "1\<noteq>(0::nat)" and "3\<noteq>(0::nat)" by arith+
  with copy_arith one have \<spadesuit>: "3\<times>x \<squnion> x = 4\<times>x" by metis
  with mann1[where x="3\<times>x" and y="x"] sup_assoc have
  "-(-?q \<squnion> x) = ?p" by metis
  ultimately show ?thesis by simp
qed

lemma mann10: "y = -(-(-(- 3\<times>x \<squnion> x) \<squnion> - 3\<times>x \<squnion> y) \<squnion> -(x \<squnion> y))"
using robbins2[where x="-(- 3\<times>x \<squnion> x) \<squnion> - 3\<times>x" and y=y]
      mann9[where x=x]
      sup_comm 
by metis

theorem mann: "2\<times>x = -(- 3\<times>x \<squnion> x) \<squnion> 2\<times>x"
using mann10[where x=x and y="2\<times>x"]
      mann8[where x=x]
      two[where x=x] three[where x=x] sup_comm 
by metis

corollary winkerr: "\<alpha> \<squnion> \<beta> = \<beta>"
using mann secret_object2_def secret_object3_def two three
by metis

corollary winker: "\<beta> \<squnion> \<alpha> = \<beta>"
  by (metis winkerr sup_comm)

corollary multi_winkerp: "\<beta> \<squnion> k \<otimes> \<alpha> = \<beta>"
  by (induct k, (simp add: winker sup_comm sup_assoc)+)

corollary multi_winker: "\<beta> \<squnion> k \<times> \<alpha> = \<beta>"
  by (induct k, (simp add: multi_winkerp winker sup_comm sup_assoc)+)

(* Towards Idempotence *)

lemma less_eq_introp: 
"-(x \<squnion> -(y \<squnion> z)) = -(x \<squnion> y \<squnion> -z) \<Longrightarrow> y \<sqsubseteq> x"
  by (metis robbins sup_assoc less_eq_def
            sup_comm[where x=x and y=y])

corollary less_eq_intro:
"-(x \<squnion> -(y \<squnion> z)) = -(x \<squnion> y \<squnion> -z) \<Longrightarrow> x \<squnion> y = x"
  by (metis less_eq_introp less_eq_def sup_comm)

lemma eq_intro: 
"-(x \<squnion> -(y \<squnion> z)) = -(y \<squnion> -(x \<squnion> z)) \<Longrightarrow> x = y"
  by (metis robbins sup_assoc sup_comm)

lemma copyp0:
   assumes "-(x \<squnion> -y) = z"
     shows "-(x \<squnion> -(y \<squnion> k \<otimes> (x \<squnion> z))) = z"
using assms
proof (induct k)
  case 0 show ?case
     by (simp, metis assms robbins sup_assoc sup_comm)
  case Suc note ind_hyp = this
  show ?case
     by (simp, metis ind_hyp robbins sup_assoc sup_comm)
qed

lemma copyp1:
   assumes "-(-(x \<squnion> -y) \<squnion> -y) = x"
     shows "-(y \<squnion> k \<otimes> (x \<squnion> -(x \<squnion> -y))) = -y"
using assms
proof -
  let ?z = "-(x \<squnion> - y)"
  let ?ky = "y \<squnion> k \<otimes> (x \<squnion> ?z)"
  have "-(x \<squnion> -?ky) = ?z" by (simp add: copyp0)
  hence "-(-?ky \<squnion> -(-y \<squnion> ?z)) = ?z" by (metis assms sup_comm)
  also have "-(?z \<squnion> -?ky) = x" by (metis assms copyp0 sup_comm)
  hence "?z = -(-y \<squnion> -(-?ky \<squnion> ?z))" by (metis sup_comm)
  finally show ?thesis by (metis eq_intro)
qed

corollary copyp2: 
   assumes "-(x \<squnion> y) = -y"
     shows "-(y \<squnion> k \<otimes> (x \<squnion> -(x \<squnion> -y))) = -y"
   by (metis assms robbins sup_comm copyp1)

lemma two_threep:
   assumes "-(2 \<times> x \<squnion> y) = -y"
       and "-(3 \<times> x \<squnion> y) = -y" 
     shows "2 \<times> x \<squnion> y = 3 \<times> x \<squnion> y"
using assms
proof -
  from assms two three have 
     A: "-(x \<squnion> x \<squnion> y) = -y" and
     B: "-(x \<squnion> x \<squnion> x \<squnion> y) = -y"  by simp+
  with sup_assoc
       copyp2[where x="x" and y="x \<squnion> x \<squnion> y" and k="0"]
  have "-(x \<squnion> x \<squnion> y \<squnion> x \<squnion> -(x \<squnion> -y)) = -y" by simp
  moreover 
  from sup_comm sup_assoc A B
       copyp2[where x="x \<squnion> x" and y="y" and k="0"] 
  have "-(y \<squnion> x \<squnion> x \<squnion> -(x \<squnion> x \<squnion> -y)) = -y" by fastforce
  with sup_comm sup_assoc 
  have "-(x \<squnion> x \<squnion> y \<squnion> -(x \<squnion> (x \<squnion> -y))) = -y" by metis
  ultimately have 
    "-(x \<squnion> x \<squnion> y \<squnion> -(x \<squnion> (x \<squnion> -y))) = -(x \<squnion> x \<squnion> y \<squnion> x \<squnion> -(x \<squnion> -y))" by simp
  with less_eq_intro have "x \<squnion> x \<squnion> y = x \<squnion> x \<squnion> y \<squnion> x" by metis
  with sup_comm sup_assoc two three show ?thesis by metis
qed

lemma two_three:
   assumes "-(x \<squnion> y) = -y \<or> -(-(x \<squnion> -y) \<squnion> -y) = x"
     shows "y \<squnion> 2 \<times> (x \<squnion> -(x \<squnion> -y)) = y \<squnion> 3 \<times> (x \<squnion> -(x \<squnion> -y))"
           (is "y \<squnion> ?z2 = y \<squnion> ?z3")
using assms
proof
    assume "-(x \<squnion> y) = -y"
      with copyp2[where k="Suc(0)"] 
           copyp2[where k="Suc(Suc(0))"]
           two three
      have "-(y \<squnion> ?z2) = -y" and "-(y \<squnion> ?z3) = -y" by simp+
      with two_threep sup_comm show ?thesis by metis
  next 
    assume "-(-(x \<squnion> -y) \<squnion> -y) = x"
      with copyp1[where k="Suc(0)"] 
           copyp1[where k="Suc(Suc(0))"]
           two three
      have "-(y \<squnion> ?z2) = -y" and "-(y \<squnion> ?z3) = -y" by simp+
      with two_threep sup_comm show ?thesis by metis
qed

lemma sup_idem: "\<rho> \<squnion> \<rho> = \<rho>"
proof -
    from winkerr two 
         copyp2[where x="\<alpha>" and y="\<beta>" and k="Suc(0)"] have
    "-\<beta> = -(\<beta> \<squnion> 2 \<times> (\<alpha> \<squnion> -(\<alpha> \<squnion> -\<beta>)))" by simp
    also from copy_distrib sup_assoc have
    "\<dots> = -(\<beta> \<squnion> 2 \<times> \<alpha> \<squnion> 2 \<times> (-(\<alpha> \<squnion> -\<beta>)))" by simp
    also from sup_assoc secret_object4_def two
              multi_winker[where k="2"] have
    "\<dots> = -\<delta>" by metis
    finally have "-\<beta> = -\<delta>" by simp
    with secret_object4_def sup_assoc three have
    "\<delta> \<squnion> -(\<alpha> \<squnion> -\<delta>) = \<beta> \<squnion> 3 \<times> (-(\<alpha> \<squnion> -\<beta>))" by simp
    also from copy_distrib[where k="3"] 
              multi_winker[where k="3"] 
              sup_assoc have 
    "\<dots> = \<beta> \<squnion> 3 \<times> (\<alpha> \<squnion> -(\<alpha> \<squnion> -\<beta>))" by metis
    also from winker sup_comm two_three[where x="\<alpha>" and y="\<beta>"] have 
    "\<dots> = \<beta> \<squnion> 2 \<times> (\<alpha> \<squnion> -(\<alpha> \<squnion> -\<beta>))" by fastforce
    also from copy_distrib[where k="2"] 
              multi_winker[where k="2"] 
              sup_assoc two secret_object4_def have 
    "\<dots> = \<delta>" by metis
    finally have \<heartsuit>: "\<delta> \<squnion> -(\<alpha> \<squnion> -\<delta>) = \<delta>" by simp
    from secret_object4_def winkerr sup_assoc have 
          "\<alpha> \<squnion> \<delta> = \<delta>" by metis
    hence "\<delta> \<squnion> \<alpha> = \<delta>" by (metis sup_comm)
    hence "-(-(\<delta> \<squnion> -\<delta>) \<squnion> -\<delta>) = -(-(\<delta> \<squnion> (\<alpha> \<squnion> -\<delta>)) \<squnion> -\<delta>)" by (metis sup_assoc)
    also from \<heartsuit> have
          "\<dots> = -(-(\<delta> \<squnion> (\<alpha> \<squnion> -\<delta>)) \<squnion> -(\<delta> \<squnion> -(\<alpha> \<squnion> -\<delta>)))" by metis
    also from robbins have
          "\<dots> = \<delta>" by metis
    finally have "-(-(\<delta> \<squnion> -\<delta>) \<squnion> -\<delta>) = \<delta>" by simp
    with two_three[where x="\<delta>" and y="\<delta>"] 
         secret_object5_def sup_comm
    have "3 \<times> \<gamma> \<squnion> \<delta> = 2 \<times> \<gamma> \<squnion> \<delta>" by fastforce
    with secret_object5_def sup_assoc sup_comm have  
         "3 \<times> \<gamma> \<squnion> \<gamma> = 2 \<times> \<gamma> \<squnion> \<gamma>" by fastforce
    with two three four five six have
         "6 \<times> \<gamma> = 3 \<times> \<gamma>" by simp
    moreover have "3 + 3 = (6::nat)" and "3 \<noteq> (0::nat)" by arith+
    moreover note copy_arith[where k="3" and l="3" and x="\<gamma>"]
                  winker_object_def three
    ultimately show ?thesis by simp
qed

(* Idempotence implies the identity law *)

lemma sup_ident: "x \<squnion> \<bottom>\<bottom> = x"
proof -
  have I: "\<rho> = -(-\<rho> \<squnion> \<bottom>\<bottom>)"
    by (metis fake_bot_def inf_eq robbins sup_comm sup_idem)

  { fix x have "x = -(-(x \<squnion> -\<rho> \<squnion> \<bottom>\<bottom>) \<squnion> -(x \<squnion> \<rho>))"
    by (metis I robbins sup_assoc) }
  note II = this

  have III: "-\<rho> = -(-(\<rho> \<squnion> -\<rho> \<squnion> -\<rho>) \<squnion> \<rho>)"
    by (metis robbins[where x="-\<rho>" and y="\<rho> \<squnion> -\<rho>"]
              I sup_comm fake_bot_def)
  hence "\<rho> = -(-(\<rho> \<squnion> -\<rho> \<squnion> -\<rho>) \<squnion> -\<rho>)"
    by (metis robbins[where x="\<rho>" and y="\<rho> \<squnion> -\<rho> \<squnion> -\<rho>"]
              sup_comm[where x="\<rho>" and y="-(\<rho> \<squnion> -\<rho> \<squnion> -\<rho>)"]
              sup_assoc sup_idem)
  hence "-(\<rho> \<squnion> -\<rho> \<squnion> -\<rho>) = \<bottom>\<bottom>"
    by (metis robbins[where x="-(\<rho> \<squnion> -\<rho> \<squnion> -\<rho>)" and y="\<rho>"] 
              III sup_comm fake_bot_def)
  hence "-\<rho> = -(\<rho> \<squnion> \<bottom>\<bottom>)"
    by (metis III sup_comm)
  hence "\<rho> = -(-(\<rho> \<squnion> \<bottom>\<bottom>) \<squnion> -(\<rho> \<squnion> \<bottom>\<bottom> \<squnion> -\<rho>))"
    by (metis II sup_idem sup_comm sup_assoc)
  moreover have "\<rho> \<squnion> \<bottom>\<bottom> = -(-(\<rho> \<squnion> \<bottom>\<bottom>) \<squnion> -(\<rho> \<squnion> \<bottom>\<bottom> \<squnion> -\<rho>))"
    by (metis robbins[where x="\<rho> \<squnion> \<bottom>\<bottom>" and y="\<rho>"] 
              sup_comm[where y="\<rho>"] 
              sup_assoc sup_idem)
  ultimately have "\<rho> = \<rho> \<squnion> \<bottom>\<bottom>" by auto
  hence "x \<squnion> \<bottom>\<bottom> = -(-(x \<squnion> \<rho>) \<squnion> -(x \<squnion> \<bottom>\<bottom> \<squnion> -\<rho>))"
    by (metis robbins[where x="x \<squnion> \<bottom>\<bottom>" and y=\<rho>]
              sup_comm[where x="\<bottom>\<bottom>" and y=\<rho>]
              sup_assoc)
  thus ?thesis by (metis sup_assoc sup_comm II)
qed

(* The identity law implies double negation *)

lemma dbl_neg: "- (-x) = x"
proof -
  { fix x have "\<bottom>\<bottom> = -(-x \<squnion> -(-x))"
      by (metis robbins sup_comm sup_ident) 
  } note I = this

  { fix x have "-x = -(-(-x \<squnion> -(-(-x))))"
    by (metis I robbins sup_comm sup_ident)
  } note II = this

  { fix x have "-(-(-x)) = -(-(-x \<squnion> -(-(-x))))"
    by (metis I II robbins sup_assoc sup_comm sup_ident) 
  } note III = this

  show ?thesis by (metis II III robbins)
qed

(* Double negation implies Huntington's axiom, hence Boolean*)

theorem robbins_is_huntington:
  "class.huntington_algebra uminus (\<sqinter>) (\<squnion>) \<bottom> \<top>"
apply unfold_locales
apply (metis dbl_neg robbins sup_comm)
done

theorem robbins_is_boolean_II:
  "class.boolean_algebra_II uminus (\<sqinter>) (\<squnion>) \<bottom> \<top>"
proof -
  interpret huntington: 
    huntington_algebra uminus "(\<sqinter>)" "(\<squnion>)" \<bottom> \<top>
      by (fact robbins_is_huntington)
  show ?thesis by (simp add: huntington.huntington_is_boolean_II)
qed

theorem robbins_is_boolean:
  "class.boolean_algebra minus uminus (\<sqinter>) (\<sqsubseteq>) (\<sqsubset>) (\<squnion>) \<bottom> \<top>"
proof -
  interpret huntington: 
    huntington_algebra uminus "(\<sqinter>)" "(\<squnion>)" \<bottom> \<top>
      by (fact robbins_is_huntington)
  show ?thesis by (simp add: huntington.huntington_is_boolean)
qed

end

no_notation secret_object1 ("\<iota>")
   and secret_object2 ("\<alpha>") 
   and secret_object3 ("\<beta>")
   and secret_object4 ("\<delta>")
   and secret_object5 ("\<gamma>")
   and winker_object ("\<rho>")
   and less_eq  (infix "\<sqsubseteq>" 50) 
   and less (infix "\<sqsubset>" 50)
   and inf (infixl "\<sqinter>" 70) 
   and sup (infixl "\<squnion>" 65) 
   and top ("\<top>")
   and bot ("\<bottom>")
   and copyp (infix "\<otimes>" 80)
   and copy (infix "\<times>" 85)

notation
  Product_Type.Times  (infixr "\<times>" 80)

end
