(*<*)
(*
 * The Maybe monad.
 * (C)opyright 2009-2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Maybe
imports HOLCF
begin
(*>*)

section\<open>The \<open>'a Maybe\<close> Monad\<close>

text\<open>This section defines the monadic machinery for the \<open>'a
Maybe\<close> type. @{term "return"} is @{term "Just"}.\<close>

domain 'a Maybe = Nothing | Just (lazy "'a")

definition
  mfail :: "'a Maybe"
where
  "mfail \<equiv> Nothing"

definition
  mcatch :: "'a Maybe \<rightarrow> 'a Maybe \<rightarrow> 'a Maybe"
where
  "mcatch \<equiv> \<Lambda> body handler. case body of Nothing \<Rightarrow> handler | Just\<cdot>x \<Rightarrow> Just\<cdot>x"

lemma mcatch_strict[simp]: "mcatch\<cdot>\<bottom> = \<bottom>"
  by (rule cfun_eqI, simp add: mcatch_def)

definition
  mbind :: "'a Maybe \<rightarrow> ('a \<rightarrow> 'b Maybe) \<rightarrow> 'b Maybe" where
  "mbind \<equiv> \<Lambda> f g. (case f of Nothing \<Rightarrow> Nothing | Just\<cdot>f' \<Rightarrow> g\<cdot>f')"

abbreviation
  mbind_syn :: "'a Maybe \<Rightarrow> ('a \<rightarrow> 'b Maybe) \<Rightarrow> 'b Maybe" (infixl ">>=\<^sub>M" 55) where
  "f >>=\<^sub>M g \<equiv> mbind\<cdot>f\<cdot>g"

lemma mbind_strict1[simp]: "\<bottom> >>=\<^sub>M g = \<bottom>" by (simp add: mbind_def)

text\<open>The standard monad laws.\<close>

lemma leftID[simp]: "Just\<cdot>a >>=\<^sub>M f = f\<cdot>a" by (simp add: mbind_def)
lemma rightID[simp]: "m >>=\<^sub>M Just = m" by (cases m, simp_all add: mbind_def)

lemma assoc[simp]: "(m >>=\<^sub>M f) >>=\<^sub>M g = m >>=\<^sub>M (\<Lambda> x. f\<cdot>x >>=\<^sub>M g)"
  by (cases m, simp_all add: mbind_def)

text\<open>Reduction for the Maybe monad.\<close>

lemma nothing_bind[simp]: "Nothing >>=\<^sub>M f = Nothing" by (simp add: mbind_def)
lemma just_bind[simp]: "Just\<cdot>x >>=\<^sub>M f = f\<cdot>x" by (simp add: mbind_def)

definition
  mliftM2 :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> 'a Maybe \<rightarrow> 'b Maybe \<rightarrow> 'c Maybe" where
  "mliftM2 f \<equiv> \<Lambda> x y. x >>=\<^sub>M (\<Lambda> x'. y >>=\<^sub>M (\<Lambda> y'. Just\<cdot>(f\<cdot>x'\<cdot>y')))"

lemma mliftM2_Nothing1[simp]: "mliftM2 f\<cdot>Nothing\<cdot>y = Nothing" by (simp add: mliftM2_def)
lemma mliftM2_Nothing2[simp]: "mliftM2 f\<cdot>(Just\<cdot>x)\<cdot>Nothing = Nothing" by (simp add: mliftM2_def)
lemma mliftM2_op[simp]: "mliftM2 f\<cdot>(Just\<cdot>x)\<cdot>(Just\<cdot>y) = Just\<cdot>(f\<cdot>x\<cdot>y)" by (simp add: mliftM2_def)

lemma mliftM2_strict1[simp]: "mliftM2 f\<cdot>\<bottom> = \<bottom>" by (rule cfun_eqI)+ (simp add: mliftM2_def)
lemma mliftM2_strict2[simp]: "mliftM2 f\<cdot>(Just\<cdot>x)\<cdot>\<bottom> = \<bottom>" by (simp add: mliftM2_def)

end
