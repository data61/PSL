(*<*)
(*
 * Domains of natural numbers.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Nats
imports HOLCF
begin
(*>*)

section\<open>Boxed Types, HOL's natural numbers hoisted.\<close>

subsection\<open>Unboxed naturals.\<close>

text\<open>We can represent the unboxed naturals as a discrete domain (every
number is equal to itself and unequal to everything else, and there is no
bottom). Think of these functions as the machine operations.

We could actually lift all HOL types and classes in this way; indeed
the HOLCF theory "Lift" does something similar, but is not as
fine-grained as this development.

Note: we default to just CPOs (not pointed CPOs) in this theory. We
adopt bothg the Isabelle syntax for overloaded arithmetic and the
notation for unboxed operators of \citet{SPJ-JL:1991}.\<close>

default_sort predomain

type_synonym UNat = "nat discr"

instantiation discr :: (zero) zero
begin
definition zero_discr_def: "0 \<equiv> Discr 0"
instance ..
end

lemma zero_discr[simp]: "undiscr 0 = 0" unfolding zero_discr_def by simp

instantiation discr :: (one) one
begin
definition one_discr_def: "1 \<equiv> Discr 1"
instance ..
end

lemma one_discr[simp]: "undiscr 1 = 1" unfolding one_discr_def by simp

instantiation discr :: (ord) ord
begin
definition less_def[simp]: "m < n \<equiv> (undiscr m) < (undiscr n)"
definition le_def[simp]:   "m \<le> n \<equiv> (undiscr m) \<le> (undiscr n)"
instance ..
end

definition
  uPlus :: "UNat \<rightarrow> UNat \<rightarrow> UNat" where
  "uPlus \<equiv> \<Lambda> x y. Discr (undiscr x + undiscr y)"

abbreviation
  uPlus_syn :: "UNat \<Rightarrow> UNat \<Rightarrow> UNat" (infixl "+\<^sub>#" 65) where
  "x +\<^sub># y \<equiv> uPlus\<cdot>x\<cdot>y"

instantiation discr :: (plus) plus
begin
definition plus_discr_def[simp]: "x + y \<equiv> Discr (undiscr x + undiscr y)"
instance ..
end

definition
  uMinus :: "UNat \<rightarrow> UNat \<rightarrow> UNat" where
  "uMinus \<equiv> \<Lambda> x y. Discr (undiscr x - undiscr y)"

abbreviation
  uMinus_syn :: "UNat \<Rightarrow> UNat \<Rightarrow> UNat" (infixl "-\<^sub>#" 65) where
  "x -\<^sub># y \<equiv> uMinus\<cdot>x\<cdot>y"

instantiation discr :: (minus) minus
begin
definition minus_discr_def[simp]: "x - y \<equiv> Discr (undiscr x - undiscr y)"
instance ..
end

definition
  uMult :: "UNat \<rightarrow> UNat \<rightarrow> UNat" where
  "uMult \<equiv> \<Lambda> x y. Discr (undiscr x * undiscr y)"

abbreviation
  uMult_syn :: "UNat \<Rightarrow> UNat \<Rightarrow> UNat" (infixl "*\<^sub>#" 65) where
  "x *\<^sub># y \<equiv> uMult\<cdot>x\<cdot>y"

instantiation discr :: (times) times
begin
definition times_discr_def[simp]: "x * y \<equiv> Discr (undiscr x * undiscr y)"
instance ..
end

lemma uMult_unit_left: "1 *\<^sub># (x::UNat) = x"
  unfolding uMult_def one_discr_def by simp
lemma uMult_unit_right: "(x::UNat) *\<^sub># 1 = x"
  unfolding uMult_def one_discr_def by simp

lemma uMult_assoc: "(x *\<^sub># y) *\<^sub># z = x *\<^sub># (y *\<^sub># z)"
  unfolding uMult_def by simp

lemma uMult_commute: "x *\<^sub># y = y *\<^sub># x"
  unfolding uMult_def by simp

lemma uMult_left_commute: "a *\<^sub># (b *\<^sub># c) = b *\<^sub># (a *\<^sub># c)"
  unfolding uMult_def by simp

lemmas uMult_arithmetic =
  uMult_unit_left uMult_unit_right uMult_assoc uMult_commute uMult_left_commute

subsection \<open>The "@{term \<bottom>}" monad.\<close>

text\<open>

As Brian Huffman helpfully observed, the "@{term "\<bottom>"}" type
constructor supports the monadic operations; it's isomorphic to
Haskell's @{term "Maybe a"}, or ML's @{typ "'a option"}.

Note that @{term "return"} is @{term "up"}.

\<close>

definition
  bbind :: "('a::cpo)\<^sub>\<bottom> \<rightarrow> ('a \<rightarrow> ('b::pcpo)) \<rightarrow> 'b" where
  "bbind \<equiv> \<Lambda> b g. fup\<cdot>g\<cdot>b"

abbreviation
  bbind_syn :: "('a::cpo)\<^sub>\<bottom> \<Rightarrow> ('a \<rightarrow> ('b::pcpo)) \<Rightarrow> 'b" (infixl ">>=" 65) where
  "b >>= g \<equiv> bbind\<cdot>b\<cdot>g"

lemma bbind_strict1[simp]: "bbind\<cdot>\<bottom> = \<bottom>"
  by (simp add: bbind_def)
lemma bbind_strict2[simp]: "x >>= \<bottom> = \<bottom>"
  by (cases x, simp_all add: bbind_def)

lemma bbind_leftID[simp]: "up\<cdot>a >>= f = f\<cdot>a" by (simp add: bbind_def)
lemma bbind_rightID[simp]: "m >>= up = m" by (cases m, simp_all)

lemma bbind_assoc[simp]: "f >>= g >>= h = f >>= (\<Lambda> x. g\<cdot>x >>= h)"
  by (cases f, simp_all)

lemma bbind_case_distr_strict: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> f\<cdot>(g >>= h) = g >>= (\<Lambda> x. f\<cdot>(h\<cdot>x))"
  unfolding bbind_def by (cases g, simp_all)

text\<open>

Kleisli composition is sometimes helpful. It forms a monad too,
and has many useful algebraic properties. Unfortunately it is more
work than is useful to write the lemmas in a way that makes the
higher-order unifier in the simplifier happy. Seems easier just to
unfold the definition and go from there.

\<close>

definition
  bKleisli :: "('a::cpo \<rightarrow> ('b::cpo)\<^sub>\<bottom>) \<rightarrow> ('b \<rightarrow> ('c::cpo)\<^sub>\<bottom>) \<rightarrow> ('a \<rightarrow> 'c\<^sub>\<bottom>)" where
  "bKleisli \<equiv> \<Lambda> f g x. f\<cdot>x >>= g"

abbreviation
  bKleisli_syn :: "('a::cpo \<rightarrow> ('b::cpo)\<^sub>\<bottom>) \<Rightarrow> ('b \<rightarrow> ('c::cpo)\<^sub>\<bottom>) \<Rightarrow> ('a \<rightarrow> 'c\<^sub>\<bottom>)" (infixl ">=>" 65) where
  "b >=> g \<equiv> bKleisli\<cdot>b\<cdot>g"

lemma bKleisli_strict1[simp]: "bKleisli\<cdot>\<bottom> = \<bottom>"
  by (simp add: bKleisli_def)
lemma bKleisli_strict2[simp]: "b >=> \<bottom> = \<bottom>"
  by (rule cfun_eqI, simp add: bKleisli_def)

lemma bKleisli_bbind: "(f >>= g) >=> h = f >>= (\<Lambda> x. g\<cdot>x >=> h)"
  by (cases f, simp_all)

text \<open>

The "Box" type denotes computations that, when demanded, yield
either @{term "\<bottom>"} or an unboxed value. Note that the @{term "Box"}
constructor is strict, and so merely tags the lifted computation @{typ
"'a\<^sub>\<bottom>"}. @{typ "'a"} can be pointed or unpointed. This approach enables
us to distinguish the boxed values from the lifted-function-space that
models recursive functions with unboxed codomains.

\<close>

domain 'a Box = Box (unbox :: "'a\<^sub>\<bottom>")

definition
  box :: "('a::predomain) \<rightarrow> 'a Box" where
  "box \<equiv> Box oo up"

lemma boxI: "Box\<cdot>(up\<cdot>x) = box\<cdot>x" unfolding box_def by simp
lemma unbox_box[simp]: "unbox\<cdot>(box\<cdot>x) = up\<cdot>x" unfolding box_def by simp
lemma unbox_Box[simp]: "x \<noteq> \<bottom> \<Longrightarrow> unbox\<cdot>(Box\<cdot>x) = x" by simp

text\<open>

If we suceed in @{term "box"}ing something, then clearly that
something was not @{term "\<bottom>"}.

\<close>

lemma box_casedist[case_names bottom Box, cases type: Box]:
  assumes xbot: "x = \<bottom> \<Longrightarrow> P"
      and xbox: "\<And>u. x = box\<cdot>u \<Longrightarrow> P"
  shows "P"
proof(cases x)
  case bottom with xbot show ?thesis by simp
next
  case (Box u) with xbox show ?thesis
    by (cases u, simp_all add: box_def up_def cont_Iup bottomI[OF minimal_up])
qed

lemma bbind_leftID'[simp]: "unbox\<cdot>a >>= box = a" by (cases a, simp_all add: bbind_def)

(*<*)
text \<open>

The optimisations of \citet{SPJ-JL:1991}.

p11: Repeated unboxing of the same value can be done once (roughly:
store the value in a register). Their story is more general.

\<close>

lemma box_repeated:
  "x >>= (\<Lambda> x'. f >>= (\<Lambda> y'. x >>= body\<cdot>x'\<cdot>y'))
  = x >>= (\<Lambda> x'. f >>= (\<Lambda> y'. body\<cdot>x'\<cdot>y'\<cdot>x'))"
  by (cases x, simp_all)
(*>*)

text\<open>Lift binary predicates over @{typ "'a discr"} into @{typ "'a discr Box"}.\<close>

text \<open>@{term "bliftM"} and @{term "bliftM2"} encapsulate the boxing
and unboxing.\<close>

definition
  bliftM :: "('a::predomain \<rightarrow> 'b::predomain) \<Rightarrow> 'a Box \<rightarrow> 'b Box" where
  "bliftM f \<equiv> \<Lambda> x. unbox\<cdot>x >>= (\<Lambda> x'. box\<cdot>(f\<cdot>x'))"

lemma bliftM_strict1[simp]: "bliftM f\<cdot>\<bottom> = \<bottom>" by (simp add: bliftM_def)
lemma bliftM_op[simp]: "bliftM f\<cdot>(box\<cdot>x) = box\<cdot>(f\<cdot>x)" by (simp add: bliftM_def)

definition
  bliftM2 :: "('a::predomain \<rightarrow> 'b::predomain \<rightarrow> 'c::predomain) \<Rightarrow> 'a Box \<rightarrow> 'b Box \<rightarrow> 'c Box" where
  "bliftM2 f \<equiv> \<Lambda> x y. unbox\<cdot>x >>= (\<Lambda> x'. unbox\<cdot>y >>= (\<Lambda> y'. box\<cdot>(f\<cdot>x'\<cdot>y')))"

lemma bliftM2_strict1[simp]: "bliftM2 f\<cdot>\<bottom> = \<bottom>" by (rule cfun_eqI)+ (simp add: bliftM2_def)
lemma bliftM2_strict2[simp]: "bliftM2 f\<cdot>x\<cdot>\<bottom> = \<bottom>" by (cases x, simp_all add: bliftM2_def)
lemma bliftM2_op[simp]: "bliftM2 f\<cdot>(box\<cdot>x)\<cdot>(box\<cdot>y) = box\<cdot>(f\<cdot>x\<cdot>y)" by (simp add: bliftM2_def)

text\<open>

Define the arithmetic operations. We need extra continuity lemmas as
we're using the full function space, so we can re-use the conventional
operators. The goal is to work at this level.

\<close>

instantiation Box :: ("{predomain,plus}") plus
begin
definition plus_Box_def: "x + y \<equiv> bliftM2 (\<Lambda> a b. a + b)\<cdot>x\<cdot>y"
instance ..
end

lemma plus_Box_cont[simp, cont2cont]:
  "\<lbrakk>cont g; cont h\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (g x :: 'a :: {predomain, plus} Box) + h x)"
  unfolding plus_Box_def by simp

lemma plus_Box_strict1[simp]: "\<bottom> + (y :: 'a::{predomain, plus} Box) = \<bottom>"
  unfolding plus_Box_def by simp
lemma plus_Box_strict2[simp]: "(x :: 'a::{predomain, plus} Box) + \<bottom> = \<bottom>"
  unfolding plus_Box_def by simp

instantiation Box :: ("{predomain,minus}") minus
begin
definition minus_Box_def: "x - y \<equiv> bliftM2 (\<Lambda> a b. a - b)\<cdot>x\<cdot>y"
instance ..
end

lemma minus_Box_cont[simp, cont2cont]:
  "\<lbrakk>cont g; cont h\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (g x :: 'a :: {predomain, minus} Box) - h x)"
  unfolding minus_Box_def by simp

lemma minus_Box_strict1[simp]: "\<bottom> - (y :: 'a::{predomain, minus} Box) = \<bottom>"
  unfolding minus_Box_def by simp
lemma minus_Box_strict2[simp]: "(x :: 'a::{predomain, minus} Box) - \<bottom> = \<bottom>"
  unfolding minus_Box_def by simp

instantiation Box :: ("{predomain,times}") times
begin
definition times_Box_def: "x * y \<equiv> bliftM2 (\<Lambda> a b. a * b)\<cdot>x\<cdot>y"
instance ..
end

lemma times_Box_cont[simp, cont2cont]:
  "\<lbrakk>cont g; cont h\<rbrakk> \<Longrightarrow> cont (\<lambda>x. (g x :: 'a :: {predomain, times} Box) * h x)"
  unfolding times_Box_def by simp

lemma times_Box_strict1[simp]: "\<bottom> * (y :: 'a::{predomain, times} Box) = \<bottom>"
  unfolding times_Box_def by simp
lemma times_Box_strict2[simp]: "(x :: 'a::{predomain, times} Box) * \<bottom> = \<bottom>"
  unfolding times_Box_def by simp

definition
  bpred :: "('a::countable discr \<Rightarrow> 'a discr \<Rightarrow> bool) \<Rightarrow> 'a discr Box \<rightarrow> 'a discr Box \<rightarrow> tr" where
  "bpred p \<equiv> \<Lambda> x y. unbox\<cdot>x >>= (\<Lambda> x'. unbox\<cdot>y >>= (\<Lambda> y'. if p x' y' then TT else FF))"

lemma bpred_strict1[simp]: "bpred p\<cdot>\<bottom> = \<bottom>" unfolding bpred_def by (rule cfun_eqI, simp)
lemma bpred_strict2[simp]: "bpred p\<cdot>x\<cdot>\<bottom> = \<bottom>" unfolding bpred_def by (cases x, simp_all)

lemma bpred_eval[simp]: "bpred p\<cdot>(box\<cdot>x)\<cdot>(box\<cdot>y) = (if p x y then TT else FF)"
  unfolding bpred_def by simp

abbreviation
  beq_syn :: "'a::countable discr Box \<Rightarrow> 'a discr Box \<Rightarrow> tr" (infix "=\<^sub>B" 50) where
  "x =\<^sub>B y \<equiv> bpred (=)\<cdot>x\<cdot>y"

abbreviation
  ble_syn :: "'a::{countable,ord} discr Box \<Rightarrow> 'a discr Box \<Rightarrow> tr" (infix "\<le>\<^sub>B" 50) where
  "x \<le>\<^sub>B y \<equiv> bpred (\<le>)\<cdot>x\<cdot>y"

abbreviation
  blt_syn :: "'a::{countable,ord} discr Box \<Rightarrow> 'a discr Box \<Rightarrow> tr" (infix "<\<^sub>B" 50) where
  "x <\<^sub>B y \<equiv> bpred (<)\<cdot>x\<cdot>y"

subsection\<open>The flat domain of natural numbers\<close>

text\<open>Lift arithmetic to the boxed naturals. Define some things that make
playing with boxed naturals more convenient.\<close>

type_synonym Nat = "UNat Box"

instantiation Box :: ("{predomain, zero}") zero
begin
definition zero_Nat_def: "0 \<equiv> box\<cdot>0"
instance ..
end

instantiation Box :: ("{predomain, one}") one
begin
definition one_Nat_def: "1 \<equiv> box\<cdot>1"
instance ..
end

text \<open>We need to know the underlying operations are continuous for these to work.\<close>

lemma plus_Nat_eval[simp]: "(box\<cdot>x :: Nat) + box\<cdot>y = box\<cdot>(x + y)" unfolding plus_Box_def by simp
lemma minus_Nat_eval[simp]: "(box\<cdot>x :: Nat) - box\<cdot>y = box\<cdot>(x - y)" unfolding minus_Box_def by simp
lemma times_Nat_eval[simp]: "(box\<cdot>x :: Nat) * box\<cdot>y = box\<cdot>(x * y)" unfolding times_Box_def by simp

definition
  Nat_case :: "'a::domain \<rightarrow> (Nat \<rightarrow> 'a) \<rightarrow> Nat \<rightarrow> 'a" where
  "Nat_case \<equiv> \<Lambda> z s n. unbox\<cdot>n >>= (\<Lambda> n'. case_nat z (\<lambda>n''. s\<cdot>(box\<cdot>(Discr n''))) (undiscr n'))"

lemma cont_case_nat[simp]:
  "\<lbrakk>cont (\<lambda>x. f x); \<And>n. cont (\<lambda>x. g x n) \<rbrakk> \<Longrightarrow> cont (\<lambda>x. case_nat (f x) (g x) n)"
  by (cases n, simp_all)

lemma Nat_case_strict[simp]: "Nat_case\<cdot>z\<cdot>s\<cdot>\<bottom> = \<bottom>" by (simp add: Nat_case_def)
lemma Nat_case_zero[simp]: "Nat_case\<cdot>z\<cdot>s\<cdot>0 = z" by (simp add: Nat_case_def zero_Nat_def zero_discr_def)
lemma Nat_case_suc[simp]:  "Nat_case\<cdot>z\<cdot>s\<cdot>(box\<cdot>(Discr (Suc n))) = s\<cdot>(box\<cdot>(Discr n))"
  by (simp add: Nat_case_def)

lemma Nat_case_add_1[simp]:
  assumes ndef: "n \<noteq> \<bottom>"
  shows "Nat_case\<cdot>z\<cdot>s\<cdot>(n + 1) = s\<cdot>n"
proof -
  from ndef obtain nu where nu: "n = box\<cdot>nu"
    unfolding box_def
    apply (cases "n" rule: Box.exhaust)
    apply simp
    apply (case_tac "u")
    apply simp_all
    done
  then obtain u where "nu = Discr u"
    unfolding box_def
    apply (cases nu)
    apply simp
    done
  with nu show ?thesis unfolding one_Nat_def by simp
qed

lemma Nat_case_case_nat: "Nat_case\<cdot>z\<cdot>s\<cdot>(box\<cdot>(Discr n)) = case_nat z (\<lambda>n'. s\<cdot>(box\<cdot>(Discr n'))) n"
  by (simp add: Nat_case_def)

lemma Nat_casedist[case_names bottom zero Suc]:
  fixes x :: Nat
  assumes xbot: "x = \<bottom> \<Longrightarrow> P"
      and xzero: "x = 0 \<Longrightarrow> P"
      and xsuc: "\<And>n. x = n + 1 \<Longrightarrow> P"
  shows "P"
proof(cases x rule: Box.exhaust)
  case bottom with xbot show ?thesis by simp
next
  case (Box u) hence xu: "x = Box\<cdot>u" and ubottom: "u \<noteq> \<bottom>" .
  from ubottom obtain n where ndn: "u = up\<cdot>(Discr n)" apply (cases u) apply simp_all apply (case_tac x) apply simp done
  show ?thesis
  proof(cases n)
    case 0 with ndn xu xzero show ?thesis unfolding zero_Nat_def by (simp add: boxI zero_discr_def)
  next
    case (Suc m) with ndn xu xsuc[where n="box\<cdot>(Discr m)"]
    show ?thesis
      unfolding plus_Box_def unfolding one_Nat_def by (simp add: boxI one_discr_def)
  qed
qed

lemma cont_Nat_case[simp]:
  "\<lbrakk>cont (\<lambda>x. f x); \<And>n. cont (\<lambda>x. g x\<cdot>n) \<rbrakk> \<Longrightarrow> cont (\<lambda>x. Nat_case\<cdot>(f x)\<cdot>(g x)\<cdot>n)"
  apply (cases n rule: Nat_casedist)
    apply simp_all
  apply (case_tac na rule: Box.exhaust)
   apply simp_all
  done

lemma Nat_induct[case_names bottom zero Suc]:
  fixes P :: "Nat \<Rightarrow> bool"
  assumes xbot: "P \<bottom>"
      and xzero: "P 0"
      and xsuc: "\<And>n. \<lbrakk>n \<noteq> \<bottom>; P n \<rbrakk> \<Longrightarrow> P (n + 1)"
  shows "P x"
proof(cases x rule: box_casedist)
  case bottom with xbot show ?thesis by simp
next
  case (Box u)
  then obtain n where un: "u = Discr n" by (cases u, simp)
  {
    fix n
    have "\<And>x. x = box\<cdot>(Discr n) \<Longrightarrow> P x"
    proof(induct n)
      case 0 with xzero show ?case unfolding zero_Nat_def zero_discr_def by simp
    next
      case (Suc n)
      hence "P (box\<cdot>(Discr n))" by simp
      with xsuc[where n="box\<cdot>(Discr n)"] have "P (box\<cdot>(Discr n) + 1)" unfolding box_def by simp
      with Suc show ?case unfolding one_Nat_def one_discr_def plus_Box_def by simp
    qed
  }
  with un Box show ?thesis by simp
qed

lemma plus_commute: "(x :: Nat) + y = y + x"
proof -
  have dc: "\<And>u v. (undiscr (u::nat discr) + undiscr v) = (undiscr v + undiscr u)"
    by simp
  thus ?thesis
    apply (cases x)
     apply simp
    apply (cases y)
    by (simp_all add: dc plus_Box_def)
qed

lemma mult_unit: "(x::Nat) * 1 = x"
  unfolding times_Box_def one_Nat_def by (cases x, simp_all)

lemma mult_commute: "(x :: Nat) * y = y * x"
proof -
  have dc: "\<And>u v. (undiscr (u::nat discr) * undiscr v) = (undiscr v * undiscr u)"
    by simp
  show ?thesis
    apply (cases x)
     apply simp
    apply (cases y)
    by (simp_all add: dc)
qed

lemma mult_assoc: "((x :: Nat) * y) * z = x * (y * z)"
proof -
  have ac: "\<And>u v w. undiscr (u::nat discr) * (undiscr v * undiscr w)
                   =  (undiscr u * undiscr v) * undiscr w" by simp
  show ?thesis
    apply (cases x)
     apply simp
    apply (cases y)
     apply simp
    apply (cases z)
     apply simp
    by (simp add: ac)
qed

text\<open>Restore the HOLCF default sort.\<close>

default_sort "domain"

(*<*)
end
(*>*)
