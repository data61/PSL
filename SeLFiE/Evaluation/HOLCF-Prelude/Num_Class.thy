section \<open>The Num Class\<close>

theory Num_Class
  imports
    Type_Classes
    Data_Integer
    Data_Tuple
begin


subsection \<open>Num class\<close>

(* TODO: Show class (jb) *)

class Num_syn =
  Eq +
  plus +
  minus +
  times +
  zero +
  one +
  fixes  negate :: "'a \<rightarrow> 'a"
  and   abs :: "'a \<rightarrow> 'a"
  and   signum :: "'a \<rightarrow> 'a"
  and   fromInteger :: "Integer \<rightarrow> 'a"

(* If I create this class in one step I get problems with Num_faithful... (jb) *)
class Num = Num_syn + plus_cpo + minus_cpo + times_cpo

class Num_strict = Num +
  assumes plus_strict[simp]:
    "x + \<bottom> = (\<bottom>::'a::Num)"
    "\<bottom> + x = \<bottom>"
  assumes minus_strict[simp]:
    "x - \<bottom> = \<bottom>"
    "\<bottom> - x = \<bottom>"
  assumes mult_strict[simp]:
    "x * \<bottom> = \<bottom>"
    "\<bottom> * x = \<bottom>"
  assumes negate_strict[simp]:
    "negate\<cdot>\<bottom> = \<bottom>"
  assumes abs_strict[simp]:
    "abs\<cdot>\<bottom> = \<bottom>"
  assumes signum_strict[simp]:
    "signum\<cdot>\<bottom> = \<bottom>"
  assumes fromInteger_strict[simp]:
    "fromInteger\<cdot>\<bottom> = \<bottom>"

(* TODO: How to name the type class that adds the reqiured relations? For Eq, we have Eq_equiv
resp. Eq_eq, but for Num I don't see a nice name. Also, a generic name might be nicer. (jb) *)

class Num_faithful =
  (* TODO: Why is it not possible to use Num here? I get
     Type unification failed: No type arity lift :: minus
     (jb)
  *)
  Num_syn +
  (* This is the only relation about Num required by the Haskell report. By using eq we leave it
  to the users choice of Eq_eq or Eq_equiv whether the relations should hold up to equivalence or
  syntactic equality. (jb) *)
  assumes abs_signum_eq: "(eq\<cdot>((abs\<cdot>x) * (signum\<cdot>x))\<cdot>(x::'a::{Num_syn})) \<sqsubseteq> TT"
  (* TODO: Should we add sensible relations on our own? (jb) *)

  (* The zero and one type class are "artificial", so we ensure they do what expected. *)
  (* Unfortunately, this is not working. Is isabelle trying to give all occurrences of 0
      the same type?
  assumes "0 = fromInteger\<cdot>0"
  assumes "1 = fromInteger\<cdot>1"
  *)

class Integral =
  Num +
  (* fixes quot rem  *)
  fixes div mod :: "'a \<rightarrow> 'a \<rightarrow> ('a::Num)"
  fixes toInteger :: "'a \<rightarrow> Integer"
begin
  (* fixrec quotRem :: "'a \<rightarrow> 'a \<rightarrow> \<langle>'a, 'a\<rangle>"  where "quotRem\<cdot>x\<cdot>y = \<langle>quot\<cdot>x\<cdot>y, (rem\<cdot>x\<cdot>y)\<rangle>" *)
  fixrec divMod :: "'a \<rightarrow> 'a \<rightarrow> \<langle>'a, 'a\<rangle>"  where "divMod\<cdot>x\<cdot>y = \<langle>div\<cdot>x\<cdot>y, mod\<cdot>x\<cdot>y\<rangle>"

  fixrec even :: "'a \<rightarrow> tr" where "even\<cdot>x = eq\<cdot>(div\<cdot>x\<cdot>(fromInteger\<cdot>2))\<cdot>0"
  fixrec odd :: "'a \<rightarrow> tr" where "odd\<cdot>x = neg\<cdot>(even\<cdot>x)"
end

class Integral_strict = Integral +
  assumes div_strict[simp]:
    "div\<cdot>x\<cdot>\<bottom> = (\<bottom>::'a::Integral)"
    "div\<cdot>\<bottom>\<cdot>x = \<bottom>"
  assumes mod_strict[simp]:
    "mod\<cdot>x\<cdot>\<bottom> = \<bottom>"
    "mod\<cdot>\<bottom>\<cdot>x = \<bottom>"
  assumes toInteger_strict[simp]:
    "toInteger\<cdot>\<bottom> = \<bottom>"

class Integral_faithful =
  Integral +
  Num_faithful +
  (* assumes "\<not>(eq\<cdot>y\<cdot>0 = TT) \<Longrightarrow> quot\<cdot>x\<cdot>y * y + rem\<cdot>x\<cdot>y = (x::'a::{Integral})" *)
  assumes "eq\<cdot>y\<cdot>0 = FF \<Longrightarrow> div\<cdot>x\<cdot>y * y + mod\<cdot>x\<cdot>y = (x::'a::{Integral})"


subsection \<open>Instances for Integer\<close>

instantiation Integer :: Num_syn
begin
  definition "negate = (\<Lambda> (MkI\<cdot>x). MkI\<cdot>(uminus x))"
  definition "abs = (\<Lambda> (MkI\<cdot>x) . MkI\<cdot>(\<bar>x\<bar>))"
  definition "signum = (\<Lambda> (MkI\<cdot>x) . MkI\<cdot>(sgn x))"
  definition "fromInteger = (\<Lambda> x. x)"
  instance..
end

instance Integer :: Num
  by standard

instance Integer :: Num_faithful
  apply standard
  apply (rename_tac x, case_tac x)
   apply simp
  apply (simp add: signum_Integer_def abs_Integer_def)
  apply (metis mult.commute mult_sgn_abs)
  done

instance Integer :: Num_strict
  apply standard
  unfolding signum_Integer_def abs_Integer_def negate_Integer_def fromInteger_Integer_def
  by simp_all

instantiation Integer :: Integral
begin
  definition "div = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). MkI\<cdot>(Rings.divide x y))"
  definition "mod = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). MkI\<cdot>(Rings.modulo x y))"
  definition "toInteger = (\<Lambda> x. x)"
  instance ..
end

instance Integer :: Integral_strict
  apply standard
  unfolding div_Integer_def mod_Integer_def toInteger_Integer_def
      apply simp_all
   apply (rename_tac x, case_tac x, simp, simp)+
  done

instance Integer :: Integral_faithful
  apply standard
  unfolding div_Integer_def mod_Integer_def
  apply (rename_tac y x)
  apply (case_tac y, simp)
  apply (case_tac x, simp)
  apply simp
  done

lemma Integer_Integral_simps[simp]:
  "div\<cdot>(MkI\<cdot>x)\<cdot>(MkI\<cdot>y) = MkI\<cdot>(Rings.divide x y)"
  "mod\<cdot>(MkI\<cdot>x)\<cdot>(MkI\<cdot>y) = MkI\<cdot>(Rings.modulo x y)"
  "fromInteger\<cdot>i = i"
  unfolding mod_Integer_def div_Integer_def fromInteger_Integer_def by simp_all

end
