(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* 
   Nondeterministic state and error monads with failure in Isabelle.
*)

chapter "Nondeterministic State Monad with Failure"

theory NonDetMonad
imports "../Lib"
begin

text \<open>
  \label{c:monads}

  State monads are used extensively in the seL4 specification. They are
  defined below.
\<close>

section "The Monad"

text \<open>
  The basic type of the nondeterministic state monad with failure is
  very similar to the normal state monad. Instead of a pair consisting
  of result and new state, we return a set of these pairs coupled with
  a failure flag. Each element in the set is a potential result of the
  computation. The flag is @{const True} if there is an execution path
  in the computation that may have failed. Conversely, if the flag is
  @{const False}, none of the computations resulting in the returned
  set can have failed.\<close> 
type_synonym ('s,'a) nondet_monad = "'s \<Rightarrow> ('a \<times> 's) set \<times> bool"


text \<open>
  The definition of fundamental monad functions \<open>return\<close> and
  \<open>bind\<close>. The monad function \<open>return x\<close> does not change 
  the  state, does not fail, and returns \<open>x\<close>.
\<close> 
definition
  return :: "'a \<Rightarrow> ('s,'a) nondet_monad" where
  "return a \<equiv> \<lambda>s. ({(a,s)},False)"

text \<open>
  The monad function \<open>bind f g\<close>, also written \<open>f >>= g\<close>,
  is the execution of @{term f} followed by the execution of \<open>g\<close>.
  The function \<open>g\<close> takes the result value \emph{and} the result
  state of \<open>f\<close> as parameter. The definition says that the result of
  the combined operation is the union of the set of sets that is created
  by \<open>g\<close> applied to the result sets of \<open>f\<close>. The combined
  operation may have failed, if \<open>f\<close> may have failed or \<open>g\<close> may
  have failed on any of the results of \<open>f\<close>.
\<close>
definition
  bind :: "('s, 'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> ('s, 'b) nondet_monad) \<Rightarrow> 
           ('s, 'b) nondet_monad" (infixl ">>=" 60)
  where
  "bind f g \<equiv> \<lambda>s. (\<Union>(fst ` case_prod g ` fst (f s)),
                   True \<in> snd ` case_prod g ` fst (f s) \<or> snd (f s))"

text \<open>
  Sometimes it is convenient to write \<open>bind\<close> in reverse order.
\<close>
abbreviation(input)
  bind_rev :: "('c \<Rightarrow> ('a, 'b) nondet_monad) \<Rightarrow> ('a, 'c) nondet_monad \<Rightarrow> 
               ('a, 'b) nondet_monad" (infixl "=<<" 60) where 
  "g =<< f \<equiv> f >>= g"

text \<open>
  The basic accessor functions of the state monad. \<open>get\<close> returns
  the current state as result, does not fail, and does not change the state.
  \<open>put s\<close> returns nothing (@{typ unit}), changes the current state
  to \<open>s\<close> and does not fail.
\<close>
definition
  get :: "('s,'s) nondet_monad" where
  "get \<equiv> \<lambda>s. ({(s,s)}, False)"

definition
  put :: "'s \<Rightarrow> ('s, unit) nondet_monad" where
  "put s \<equiv> \<lambda>_. ({((),s)}, False)"


subsection "Nondeterminism"

text \<open>
  Basic nondeterministic functions. \<open>select A\<close> chooses an element 
  of the set \<open>A\<close>, does not change the state, and does not fail
  (even if the set is empty). \<open>f \<sqinter> g\<close> executes \<open>f\<close> or
  executes \<open>g\<close>. It retuns the union of results of \<open>f\<close> and
  \<open>g\<close>, and may have failed if either may have failed.  
\<close>
definition
  select :: "'a set \<Rightarrow> ('s,'a) nondet_monad" where
  "select A \<equiv> \<lambda>s. (A \<times> {s}, False)"

definition
  alternative :: "('s,'a) nondet_monad \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> 
                  ('s,'a) nondet_monad" 
  (infixl "\<sqinter>" 20)
where
  "f \<sqinter> g \<equiv> \<lambda>s. (fst (f s) \<union> fst (g s), snd (f s) \<or> snd (g s))"


text \<open>A variant of \<open>select\<close> that takes a pair. The first component
  is a set as in normal \<open>select\<close>, the second component indicates
  whether the execution failed. This is useful to lift monads between
  different state spaces.
\<close>
definition
  select_f :: "'a set \<times> bool  \<Rightarrow> ('s,'a) nondet_monad" where
  "select_f S \<equiv> \<lambda>s. (fst S \<times> {s}, snd S)"

text \<open>\<open>select_state\<close> takes a relationship between
  states, and outputs nondeterministically a state
  related to the input state.\<close>

definition
  state_select :: "('s \<times> 's) set \<Rightarrow> ('s, unit) nondet_monad"
where
  "state_select r \<equiv> \<lambda>s. ((\<lambda>x. ((), x)) ` {s'. (s, s') \<in> r}, \<not> (\<exists>s'. (s, s') \<in> r))"

subsection "Failure"

text \<open>The monad function that always fails. Returns an empty set of
results and sets the failure flag.\<close>
definition
  fail :: "('s, 'a) nondet_monad" where
 "fail \<equiv> \<lambda>s. ({}, True)"

text \<open>Assertions: fail if the property \<open>P\<close> is not true\<close>
definition
  assert :: "bool \<Rightarrow> ('a, unit) nondet_monad" where
 "assert P \<equiv> if P then return () else fail"

text \<open>Fail if the value is @{const None}, 
  return result \<open>v\<close> for @{term "Some v"}\<close>
definition
  assert_opt :: "'a option \<Rightarrow> ('b, 'a) nondet_monad" where
 "assert_opt v \<equiv> case v of None \<Rightarrow> fail | Some v \<Rightarrow> return v"

text \<open>An assertion that also can introspect the current state.\<close>

definition
  state_assert :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, unit) nondet_monad"
where
  "state_assert P \<equiv> get >>= (\<lambda>s. assert (P s))"

subsection "Generic functions on top of the state monad"

text \<open>Apply a function to the current state and return the result
without changing the state.\<close>
definition
  gets :: "('s \<Rightarrow> 'a) \<Rightarrow> ('s, 'a) nondet_monad" where
 "gets f \<equiv> get >>= (\<lambda>s. return (f s))"

text \<open>Modify the current state using the function passed in.\<close>
definition
  modify :: "('s \<Rightarrow> 's) \<Rightarrow> ('s, unit) nondet_monad" where
 "modify f \<equiv> get >>= (\<lambda>s. put (f s))"

lemma simpler_gets_def: "gets f = (\<lambda>s. ({(f s, s)}, False))"
  apply (simp add: gets_def return_def bind_def get_def)
  done

lemma simpler_modify_def:
  "modify f = (\<lambda>s. ({((), f s)}, False))"
  by (simp add: modify_def bind_def get_def put_def)

text \<open>Execute the given monad when the condition is true, 
  return \<open>()\<close> otherwise.\<close>
definition
  "when" :: "bool \<Rightarrow> ('s, unit) nondet_monad \<Rightarrow> 
           ('s, unit) nondet_monad" where 
  "when P m \<equiv> if P then m else return ()"

text \<open>Execute the given monad unless the condition is true, 
  return \<open>()\<close> otherwise.\<close>
definition 
  unless :: "bool \<Rightarrow> ('s, unit) nondet_monad \<Rightarrow> 
            ('s, unit) nondet_monad" where
  "unless P m \<equiv> when (\<not>P) m"

text \<open>
  Perform a test on the current state, performing the left monad if
  the result is true or the right monad if the result is false.
\<close>
definition
  condition :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'r) nondet_monad \<Rightarrow> ('s, 'r) nondet_monad \<Rightarrow> ('s, 'r) nondet_monad"
where
  "condition P L R \<equiv> \<lambda>s. if (P s) then (L s) else (R s)"

notation (output)
  condition  ("(condition (_)//  (_)//  (_))" [1000,1000,1000] 1000)

text \<open>
Apply an option valued function to the current state, fail 
if it returns @{const None}, return \<open>v\<close> if it returns 
@{term "Some v"}.  
\<close> 
definition
  gets_the :: "('s \<Rightarrow> 'a option) \<Rightarrow> ('s, 'a) nondet_monad" where
 "gets_the f \<equiv> gets f >>= assert_opt"


subsection \<open>The Monad Laws\<close>

text \<open>A more expanded definition of \<open>bind\<close>\<close>
lemma bind_def':
  "(f >>= g) \<equiv>
       \<lambda>s. ({(r'', s''). \<exists>(r', s') \<in> fst (f s). (r'', s'') \<in> fst (g r' s') },
                     snd (f s) \<or> (\<exists>(r', s') \<in> fst (f s). snd (g r' s')))"
  apply (rule eq_reflection)
  apply (auto simp add: bind_def split_def Let_def)
  done

text \<open>Each monad satisfies at least the following three laws.\<close>

text \<open>@{term return} is absorbed at the left of a @{term bind}, 
  applying the return value directly:\<close> 
lemma return_bind [simp]: "(return x >>= f) = f x"
  by (simp add: return_def bind_def)

text \<open>@{term return} is absorbed on the right of a @{term bind}\<close> 
lemma bind_return [simp]: "(m >>= return) = m"
  apply (rule ext)
  apply (simp add: bind_def return_def split_def)
  done
 
text \<open>@{term bind} is associative\<close>
lemma bind_assoc: 
  fixes m :: "('a,'b) nondet_monad"
  fixes f :: "'b \<Rightarrow> ('a,'c) nondet_monad"
  fixes g :: "'c \<Rightarrow> ('a,'d) nondet_monad"
  shows "(m >>= f) >>= g  =  m >>= (\<lambda>x. f x >>= g)"
  apply (unfold bind_def Let_def split_def)
  apply (rule ext)
  apply clarsimp
  apply (auto intro: rev_image_eqI)
  done


section \<open>Adding Exceptions\<close>

text \<open>
  The type @{typ "('s,'a) nondet_monad"} gives us nondeterminism and
  failure. We now extend this monad with exceptional return values
  that abort normal execution, but can be handled explicitly.
  We use the sum type to indicate exceptions. 

  In @{typ "('s, 'e + 'a) nondet_monad"}, @{typ "'s"} is the state,
  @{typ 'e} is an exception, and @{typ 'a} is a normal return value.

  This new type itself forms a monad again. Since type classes in 
  Isabelle are not powerful enough to express the class of monads,
  we provide new names for the @{term return} and @{term bind} functions
  in this monad. We call them \<open>returnOk\<close> (for normal return values)
  and \<open>bindE\<close> (for composition). We also define \<open>throwError\<close>
  to return an exceptional value.
\<close>
definition
  returnOk :: "'a \<Rightarrow> ('s, 'e + 'a) nondet_monad" where
  "returnOk \<equiv> return o Inr"

definition
  throwError :: "'e \<Rightarrow> ('s, 'e + 'a) nondet_monad" where
  "throwError \<equiv> return o Inl"

text \<open>
  Lifting a function over the exception type: if the input is an
  exception, return that exception; otherwise continue execution.
\<close>
definition
  lift :: "('a \<Rightarrow> ('s, 'e + 'b) nondet_monad) \<Rightarrow> 
           'e +'a \<Rightarrow> ('s, 'e + 'b) nondet_monad"
where
  "lift f v \<equiv> case v of Inl e \<Rightarrow> throwError e
                      | Inr v' \<Rightarrow> f v'"

text \<open>
  The definition of @{term bind} in the exception monad (new
  name \<open>bindE\<close>): the same as normal @{term bind}, but 
  the right-hand side is skipped if the left-hand side
  produced an exception.
\<close>
definition
  bindE :: "('s, 'e + 'a) nondet_monad \<Rightarrow> 
            ('a \<Rightarrow> ('s, 'e + 'b) nondet_monad) \<Rightarrow> 
            ('s, 'e + 'b) nondet_monad"  (infixl ">>=E" 60)
where
  "bindE f g \<equiv> bind f (lift g)"


text \<open>
  Lifting a normal nondeterministic monad into the 
  exception monad is achieved by always returning its
  result as normal result and never throwing an exception.
\<close>
definition
  liftE :: "('s,'a) nondet_monad \<Rightarrow> ('s, 'e+'a) nondet_monad"
where
  "liftE f \<equiv> f >>= (\<lambda>r. return (Inr r))"


text \<open>
  Since the underlying type and \<open>return\<close> function changed, 
  we need new definitions for when and unless:
\<close>
definition
  whenE :: "bool \<Rightarrow> ('s, 'e + unit) nondet_monad \<Rightarrow> 
            ('s, 'e + unit) nondet_monad" 
  where
  "whenE P f \<equiv> if P then f else returnOk ()"

definition
  unlessE :: "bool \<Rightarrow> ('s, 'e + unit) nondet_monad \<Rightarrow> 
            ('s, 'e + unit) nondet_monad" 
  where
  "unlessE P f \<equiv> if P then returnOk () else f"


text \<open>
  Throwing an exception when the parameter is @{term None}, otherwise
  returning @{term "v"} for @{term "Some v"}.
\<close>
definition
  throw_opt :: "'e \<Rightarrow> 'a option \<Rightarrow> ('s, 'e + 'a) nondet_monad" where
  "throw_opt ex x \<equiv> 
  case x of None \<Rightarrow> throwError ex | Some v \<Rightarrow> returnOk v"


text \<open>
  Failure in the exception monad is redefined in the same way
  as @{const whenE} and @{const unlessE}, with @{term returnOk}
  instead of @{term return}.
\<close> 
definition
  assertE :: "bool \<Rightarrow> ('a, 'e + unit) nondet_monad" where
 "assertE P \<equiv> if P then returnOk () else fail"

subsection "Monad Laws for the Exception Monad"

text \<open>More direct definition of @{const liftE}:\<close>
lemma liftE_def2:
  "liftE f = (\<lambda>s. ((\<lambda>(v,s'). (Inr v, s')) ` fst (f s), snd (f s)))"
  by (auto simp: liftE_def return_def split_def bind_def)

text \<open>Left @{const returnOk} absorbtion over @{term bindE}:\<close>
lemma returnOk_bindE [simp]: "(returnOk x >>=E f) = f x"
  apply (simp only: bindE_def return_def returnOk_def)
  apply (clarsimp simp: lift_def)
  done

lemma lift_return [simp]:
  "lift (return \<circ> Inr) = return"
  by (rule ext)
     (simp add: lift_def throwError_def split: sum.splits)

text \<open>Right @{const returnOk} absorbtion over @{term bindE}:\<close>
lemma bindE_returnOk [simp]: "(m >>=E returnOk) = m"
  by (simp add: bindE_def returnOk_def)

text \<open>Associativity of @{const bindE}:\<close>
lemma bindE_assoc:
  "(m >>=E f) >>=E g = m >>=E (\<lambda>x. f x >>=E g)"
  apply (simp add: bindE_def bind_assoc)
  apply (rule arg_cong [where f="\<lambda>x. m >>= x"])
  apply (rule ext)
  apply (case_tac x, simp_all add: lift_def throwError_def)
  done

text \<open>@{const returnOk} could also be defined via @{const liftE}:\<close>
lemma returnOk_liftE:
  "returnOk x = liftE (return x)"
  by (simp add: liftE_def returnOk_def)

text \<open>Execution after throwing an exception is skipped:\<close>
lemma throwError_bindE [simp]:
  "(throwError E >>=E f) = throwError E"
  by (simp add: bindE_def bind_def throwError_def lift_def return_def)


section "Syntax"

text \<open>This section defines traditional Haskell-like do-syntax 
  for the state monad in Isabelle.\<close>

subsection "Syntax for the Nondeterministic State Monad"

text \<open>We use \<open>K_bind\<close> to syntactically indicate the 
  case where the return argument of the left side of a @{term bind}
  is ignored\<close>
definition
  K_bind_def [iff]: "K_bind \<equiv> \<lambda>x y. x"

nonterminal
  dobinds and dobind and nobind

syntax (ASCII)
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ <-/ _)" 10)
syntax
  "_dobind"    :: "[pttrn, 'a] => dobind"             ("(_ \<leftarrow>/ _)" 10)
  ""           :: "dobind => dobinds"                 ("_")
  "_nobind"    :: "'a => dobind"                      ("_")
  "_dobinds"   :: "[dobind, dobinds] => dobinds"      ("(_);//(_)")

  "_do"        :: "[dobinds, 'a] => 'a"               ("(do ((_);//(_))//od)" 100)
translations
  "_do (_dobinds b bs) e"  == "_do b (_do bs e)"
  "_do (_nobind b) e"      == "b >>= (CONST K_bind e)"
  "do x <- a; e od"        == "a >>= (\<lambda>x. e)"  

text \<open>Syntax examples:\<close>
lemma "do x \<leftarrow> return 1; 
          return (2::nat); 
          return x 
       od = 
       return 1 >>= 
       (\<lambda>x. return (2::nat) >>= 
            K_bind (return x))" 
  by (rule refl)

lemma "do x \<leftarrow> return 1; 
          return 2; 
          return x 
       od = return 1" 
  by simp

subsection "Syntax for the Exception Monad"

text \<open>
  Since the exception monad is a different type, we
  need to syntactically distinguish it in the syntax.
  We use \<open>doE\<close>/\<open>odE\<close> for this, but can re-use
  most of the productions from \<open>do\<close>/\<open>od\<close>
  above.
\<close>

syntax
  "_doE" :: "[dobinds, 'a] => 'a"  ("(doE ((_);//(_))//odE)" 100)

translations
  "_doE (_dobinds b bs) e"  == "_doE b (_doE bs e)"
  "_doE (_nobind b) e"      == "b >>=E (CONST K_bind e)"
  "doE x <- a; e odE"       == "a >>=E (\<lambda>x. e)"

text \<open>Syntax examples:\<close>
lemma "doE x \<leftarrow> returnOk 1; 
           returnOk (2::nat); 
           returnOk x 
       odE =
       returnOk 1 >>=E 
       (\<lambda>x. returnOk (2::nat) >>=E 
            K_bind (returnOk x))"
  by (rule refl)

lemma "doE x \<leftarrow> returnOk 1; 
           returnOk 2; 
           returnOk x 
       odE = returnOk 1" 
  by simp



section "Library of Monadic Functions and Combinators"


text \<open>Lifting a normal function into the monad type:\<close>
definition
  liftM :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('s, 'b) nondet_monad"
where
  "liftM f m \<equiv> do x \<leftarrow> m; return (f x) od"

text \<open>The same for the exception monad:\<close>
definition
  liftME :: "('a \<Rightarrow> 'b) \<Rightarrow> ('s,'e+'a) nondet_monad \<Rightarrow> ('s,'e+'b) nondet_monad"
where
  "liftME f m \<equiv> doE x \<leftarrow> m; returnOk (f x) odE"

text \<open>
  Run a sequence of monads from left to right, ignoring return values.\<close>
definition
  sequence_x :: "('s, 'a) nondet_monad list \<Rightarrow> ('s, unit) nondet_monad" 
where
  "sequence_x xs \<equiv> foldr (\<lambda>x y. x >>= (\<lambda>_. y)) xs (return ())"

text \<open>
  Map a monadic function over a list by applying it to each element
  of the list from left to right, ignoring return values.
\<close>
definition
  mapM_x :: "('a \<Rightarrow> ('s,'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('s, unit) nondet_monad"
where
  "mapM_x f xs \<equiv> sequence_x (map f xs)"

text \<open>
  Map a monadic function with two parameters over two lists,
  going through both lists simultaneously, left to right, ignoring
  return values.
\<close>
definition
  zipWithM_x :: "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) nondet_monad) \<Rightarrow> 
                 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, unit) nondet_monad"
where
  "zipWithM_x f xs ys \<equiv> sequence_x (zipWith f xs ys)"


text \<open>The same three functions as above, but returning a list of
return values instead of \<open>unit\<close>\<close>
definition
  sequence :: "('s, 'a) nondet_monad list \<Rightarrow> ('s, 'a list) nondet_monad" 
where
  "sequence xs \<equiv> let mcons = (\<lambda>p q. p >>= (\<lambda>x. q >>= (\<lambda>y. return (x#y))))
                 in foldr mcons xs (return [])"

definition
  mapM :: "('a \<Rightarrow> ('s,'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'b list) nondet_monad"
where
  "mapM f xs \<equiv> sequence (map f xs)"

definition
  zipWithM :: "('a \<Rightarrow> 'b \<Rightarrow> ('s,'c) nondet_monad) \<Rightarrow> 
                 'a list \<Rightarrow> 'b list \<Rightarrow> ('s, 'c list) nondet_monad"
where
  "zipWithM f xs ys \<equiv> sequence (zipWith f xs ys)"

definition
  foldM :: "('b \<Rightarrow> 'a \<Rightarrow> ('s, 'a) nondet_monad) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> ('s, 'a) nondet_monad" 
where
  "foldM m xs a \<equiv> foldr (\<lambda>p q. q >>= m p) xs (return a) "

text \<open>The sequence and map functions above for the exception monad,
with and without lists of return value\<close>
definition
  sequenceE_x :: "('s, 'e+'a) nondet_monad list \<Rightarrow> ('s, 'e+unit) nondet_monad" 
where
  "sequenceE_x xs \<equiv> foldr (\<lambda>x y. doE _ <- x; y odE) xs (returnOk ())"

definition
  mapME_x :: "('a \<Rightarrow> ('s,'e+'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> 
              ('s,'e+unit) nondet_monad"
where
  "mapME_x f xs \<equiv> sequenceE_x (map f xs)"

definition
  sequenceE :: "('s, 'e+'a) nondet_monad list \<Rightarrow> ('s, 'e+'a list) nondet_monad" 
where
  "sequenceE xs \<equiv> let mcons = (\<lambda>p q. p >>=E (\<lambda>x. q >>=E (\<lambda>y. returnOk (x#y))))
                 in foldr mcons xs (returnOk [])"

definition
  mapME :: "('a \<Rightarrow> ('s,'e+'b) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> 
              ('s,'e+'b list) nondet_monad"
where
  "mapME f xs \<equiv> sequenceE (map f xs)"


text \<open>Filtering a list using a monadic function as predicate:\<close>
primrec
  filterM :: "('a \<Rightarrow> ('s, bool) nondet_monad) \<Rightarrow> 'a list \<Rightarrow> ('s, 'a list) nondet_monad"
where
  "filterM P []       = return []"
| "filterM P (x # xs) = do
     b  <- P x;
     ys <- filterM P xs; 
     return (if b then (x # ys) else ys)
   od"


section "Catching and Handling Exceptions"

text \<open>
  Turning an exception monad into a normal state monad
  by catching and handling any potential exceptions:
\<close>
definition
  catch :: "('s, 'e + 'a) nondet_monad \<Rightarrow>
            ('e \<Rightarrow> ('s, 'a) nondet_monad) \<Rightarrow>
            ('s, 'a) nondet_monad" (infix "<catch>" 10)
where
  "f <catch> handler \<equiv>
     do x \<leftarrow> f;
        case x of
          Inr b \<Rightarrow> return b
        | Inl e \<Rightarrow> handler e
     od"

text \<open>
  Handling exceptions, but staying in the exception monad.
  The handler may throw a type of exceptions different from
  the left side.
\<close>
definition
  handleE' :: "('s, 'e1 + 'a) nondet_monad \<Rightarrow>
               ('e1 \<Rightarrow> ('s, 'e2 + 'a) nondet_monad) \<Rightarrow>
               ('s, 'e2 + 'a) nondet_monad" (infix "<handle2>" 10)
where
  "f <handle2> handler \<equiv>
   do
      v \<leftarrow> f;
      case v of
        Inl e \<Rightarrow> handler e
      | Inr v' \<Rightarrow> return (Inr v')
   od"

text \<open>
  A type restriction of the above that is used more commonly in
  practice: the exception handle (potentially) throws exception
  of the same type as the left-hand side.
\<close>
definition
  handleE :: "('s, 'x + 'a) nondet_monad \<Rightarrow> 
              ('x \<Rightarrow> ('s, 'x + 'a) nondet_monad) \<Rightarrow> 
              ('s, 'x + 'a) nondet_monad" (infix "<handle>" 10)
where
  "handleE \<equiv> handleE'"


text \<open>
  Handling exceptions, and additionally providing a continuation
  if the left-hand side throws no exception:
\<close>
definition
  handle_elseE :: "('s, 'e + 'a) nondet_monad \<Rightarrow>
                   ('e \<Rightarrow> ('s, 'ee + 'b) nondet_monad) \<Rightarrow>
                   ('a \<Rightarrow> ('s, 'ee + 'b) nondet_monad) \<Rightarrow>
                   ('s, 'ee + 'b) nondet_monad"
  ("_ <handle> _ <else> _" 10)
where
  "f <handle> handler <else> continue \<equiv>
   do v \<leftarrow> f;
   case v of Inl e  \<Rightarrow> handler e
           | Inr v' \<Rightarrow> continue v'
   od"

subsection "Loops"

text \<open>
  Loops are handled using the following inductive predicate;
  non-termination is represented using the failure flag of the
  monad.
\<close>

inductive_set
  whileLoop_results :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) nondet_monad) \<Rightarrow> ((('r \<times> 's) option) \<times> (('r \<times> 's) option)) set"
  for C B
where
    "\<lbrakk> \<not> C r s \<rbrakk> \<Longrightarrow> (Some (r, s), Some (r, s)) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; snd (B r s) \<rbrakk> \<Longrightarrow> (Some (r, s), None) \<in> whileLoop_results C B"
  | "\<lbrakk> C r s; (r', s') \<in> fst (B r s); (Some (r', s'), z) \<in> whileLoop_results C B  \<rbrakk>
       \<Longrightarrow> (Some (r, s), z) \<in> whileLoop_results C B"

inductive_cases whileLoop_results_cases_valid: "(Some x, Some y) \<in> whileLoop_results C B"
inductive_cases whileLoop_results_cases_fail: "(Some x, None) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps: "(Some x, y) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps_valid: "(Some x, Some y) \<in> whileLoop_results C B"
inductive_simps whileLoop_results_simps_start_fail [simp]: "(None, x) \<in> whileLoop_results C B"

inductive
  whileLoop_terminates :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'r) nondet_monad) \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> bool"
  for C B
where
    "\<not> C r s \<Longrightarrow> whileLoop_terminates C B r s"
  | "\<lbrakk> C r s; \<forall>(r', s') \<in> fst (B r s). whileLoop_terminates C B r' s' \<rbrakk>
        \<Longrightarrow> whileLoop_terminates C B r s"

inductive_cases whileLoop_terminates_cases: "whileLoop_terminates C B r s"
inductive_simps whileLoop_terminates_simps: "whileLoop_terminates C B r s"

definition
  "whileLoop C B \<equiv> (\<lambda>r s.
     ({(r',s'). (Some (r, s), Some (r', s')) \<in> whileLoop_results C B},
        (Some (r, s), None) \<in> whileLoop_results C B \<or> (\<not> whileLoop_terminates C B r s)))"

notation (output)
  whileLoop  ("(whileLoop (_)//  (_))" [1000, 1000] 1000)

definition
  whileLoopE :: "('r \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('r \<Rightarrow> ('s, 'e + 'r) nondet_monad)
      \<Rightarrow> 'r \<Rightarrow> 's \<Rightarrow> (('e + 'r) \<times> 's) set \<times> bool"
where
  "whileLoopE C body \<equiv>
      \<lambda>r. whileLoop (\<lambda>r s. (case r of Inr v \<Rightarrow> C v s | _ \<Rightarrow> False)) (lift body) (Inr r)"

notation (output)
  whileLoopE  ("(whileLoopE (_)//  (_))" [1000, 1000] 1000)

section "Hoare Logic"

subsection "Validity"

text \<open>This section defines a Hoare logic for partial correctness for
  the nondeterministic state monad as well as the exception monad.
  The logic talks only about the behaviour part of the monad and ignores
  the failure flag.

  The logic is defined semantically. Rules work directly on the
  validity predicate.

  In the nondeterministic state monad, validity is a triple of precondition,
  monad, and postcondition. The precondition is a function from state to 
  bool (a state predicate), the postcondition is a function from return value
  to state to bool. A triple is valid if for all states that satisfy the
  precondition, all result values and result states that are returned by
  the monad satisfy the postcondition. Note that if the computation returns
  the empty set, the triple is trivially valid. This means @{term "assert P"} 
  does not require us to prove that @{term P} holds, but rather allows us
  to assume @{term P}! Proving non-failure is done via separate predicate and
  calculus (see below).
\<close>
definition
  valid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" 
  ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall>s. P s \<longrightarrow> (\<forall>(r,s') \<in> fst (f s). Q r s')"

text \<open>
  Validity for the exception monad is similar and build on the standard 
  validity above. Instead of one postcondition, we have two: one for
  normal and one for exceptional results.
\<close>
definition
  validE :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) nondet_monad \<Rightarrow> 
             ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> 
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" 
("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>)")
where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace> \<equiv> \<lbrace>P\<rbrace> f \<lbrace> \<lambda>v s. case v of Inr r \<Rightarrow> Q r s | Inl e \<Rightarrow> E e s \<rbrace>"


text \<open>
  The following two instantiations are convenient to separate reasoning
  for exceptional and normal case.
\<close>
definition
  validE_R :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + 'a) nondet_monad \<Rightarrow> 
               ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
   ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>, -")
where
 "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>,- \<equiv> validE P f Q (\<lambda>x y. True)"

definition
  validE_E :: "('s \<Rightarrow> bool) \<Rightarrow>  ('s, 'e + 'a) nondet_monad \<Rightarrow> 
               ('e \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
   ("\<lbrace>_\<rbrace>/ _ /-, \<lbrace>_\<rbrace>")
where
 "\<lbrace>P\<rbrace> f -,\<lbrace>Q\<rbrace> \<equiv> validE P f (\<lambda>x y. True) Q"


text \<open>Abbreviations for trivial preconditions:\<close>
abbreviation(input)
  top :: "'a \<Rightarrow> bool" ("\<top>")
where
  "\<top> \<equiv> \<lambda>_. True"

abbreviation(input)
  bottom :: "'a \<Rightarrow> bool" ("\<bottom>")
where
  "\<bottom> \<equiv> \<lambda>_. False"

text \<open>Abbreviations for trivial postconditions (taking two arguments):\<close>
abbreviation(input)
  toptop :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<top>\<top>")
where
 "\<top>\<top> \<equiv> \<lambda>_ _. True"

abbreviation(input)
  botbot :: "'a \<Rightarrow> 'b \<Rightarrow> bool" ("\<bottom>\<bottom>")
where
 "\<bottom>\<bottom> \<equiv> \<lambda>_ _. False"

text \<open>
  Lifting \<open>\<and>\<close> and \<open>\<or>\<close> over two arguments. 
  Lifting \<open>\<and>\<close> and \<open>\<or>\<close> over one argument is already
  defined (written \<open>and\<close> and \<open>or\<close>).
\<close>
definition
  bipred_conj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" 
  (infixl "And" 96)
where
  "bipred_conj P Q \<equiv> \<lambda>x y. P x y \<and> Q x y"

definition
  bipred_disj :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool)" 
  (infixl "Or" 91)
where
  "bipred_disj P Q \<equiv> \<lambda>x y. P x y \<or> Q x y"


subsection "Determinism"

text \<open>A monad of type \<open>nondet_monad\<close> is deterministic iff it
returns exactly one state and result and does not fail\<close> 
definition
  det :: "('a,'s) nondet_monad \<Rightarrow> bool"
where
  "det f \<equiv> \<forall>s. \<exists>r. f s = ({r},False)" 

text \<open>A deterministic \<open>nondet_monad\<close> can be turned
  into a normal state monad:\<close>
definition
  the_run_state :: "('s,'a) nondet_monad \<Rightarrow> 's \<Rightarrow> 'a \<times> 's"
where
  "the_run_state M \<equiv> \<lambda>s. THE s'. fst (M s) = {s'}"


subsection "Non-Failure"

text \<open>
  With the failure flag, we can formulate non-failure separately
  from validity. A monad \<open>m\<close> does not fail under precondition
  \<open>P\<close>, if for no start state in that precondition it sets
  the failure flag.
\<close>
definition
  no_fail :: "('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> bool"
where
  "no_fail P m \<equiv> \<forall>s. P s \<longrightarrow> \<not> (snd (m s))"


text \<open>
  It is often desired to prove non-failure and a Hoare triple
  simultaneously, as the reasoning is often similar. The following
  definitions allow such reasoning to take place.
\<close>

definition
  validNF ::"('s \<Rightarrow> bool) \<Rightarrow> ('s,'a) nondet_monad \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
      ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>!")
where
  "validNF P f Q \<equiv> valid P f Q \<and> no_fail P f"

definition
  validE_NF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'a + 'b) nondet_monad \<Rightarrow>
             ('b \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow>
             ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lbrace>_\<rbrace>/ _ /(\<lbrace>_\<rbrace>,/ \<lbrace>_\<rbrace>!)")
where
  "validE_NF P f Q E \<equiv> validE P f Q E \<and> no_fail P f"

lemma validE_NF_alt_def:
  "\<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>! = \<lbrace> P \<rbrace> B \<lbrace> \<lambda>v s. case v of Inl e \<Rightarrow> E e s | Inr r \<Rightarrow> Q r s \<rbrace>!"
  by (clarsimp simp: validE_NF_def validE_def validNF_def)

text \<open>
  Usually, well-formed monads constructed from the primitives
  above will have the following property: if they return an
  empty set of results, they will have the failure flag set.
\<close>
definition
  empty_fail :: "('s,'a) nondet_monad \<Rightarrow> bool" 
where
  "empty_fail m \<equiv> \<forall>s. fst (m s) = {} \<longrightarrow> snd (m s)"


text \<open>
  Useful in forcing otherwise unknown executions to have
  the @{const empty_fail} property.
\<close>
definition
  mk_ef :: "'a set \<times> bool \<Rightarrow> 'a set \<times> bool"
where
  "mk_ef S \<equiv> (fst S, fst S = {} \<or> snd S)"

section "Basic exception reasoning"

text \<open>
  The following predicates \<open>no_throw\<close> and \<open>no_return\<close> allow
  reasoning that functions in the exception monad either do
  no throw an exception or never return normally.
\<close>

definition "no_throw P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace> \<lambda>_ _. True \<rbrace>,\<lbrace> \<lambda>_ _. False \<rbrace>"

definition "no_return P A \<equiv> \<lbrace> P \<rbrace> A \<lbrace>\<lambda>_ _. False\<rbrace>,\<lbrace>\<lambda>_ _. True \<rbrace>"

end
