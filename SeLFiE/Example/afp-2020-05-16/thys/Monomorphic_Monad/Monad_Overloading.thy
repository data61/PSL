section \<open>Overloaded monad operations\<close>

theory Monad_Overloading imports Monomorphic_Monad begin

consts return :: "('a, 'm) return"
consts bind :: "('a, 'm) bind"
consts get :: "('s, 'm) get"
consts put :: "('s, 'm) put"
consts fail :: "'m fail"
consts catch :: "'m catch"
consts ask :: "('r, 'm) ask"
consts sample :: "('p, 'm) sample"
consts pause :: "('o, 'i, 'm) pause"
consts tell :: "('w, 'm) tell"
consts alt :: "'m alt"
consts altc :: "('c, 'm) altc"

subsection \<open>Identity monad\<close>

overloading 
  bind_id' \<equiv> "bind :: ('a, 'a id) bind"
  return_id \<equiv> "return :: ('a, 'a id) return"
begin

definition bind_id' :: "('a, 'a id) bind"
where [code_unfold, monad_unfold]: "bind_id' = bind_id"

definition return_id :: "('a, 'a id) return"
where [code_unfold, monad_unfold]: "return_id = id.return_id"

end

lemma extract_bind' [simp]: "extract (bind x f) = extract (f (extract x))"
by(simp add: bind_id'_def)

lemma extract_return [simp]: "extract (return x) = x"
by(simp add: return_id_def)

lemma monad_id' [locale_witness]: "monad return (bind :: ('a, 'a id) bind)"
unfolding bind_id'_def return_id_def by(rule monad_id)

lemma monad_commute_id' [locale_witness]: "monad_commute return (bind :: ('a, 'a id) bind)"
unfolding bind_id'_def return_id_def by(rule monad_commute_id)


subsection \<open>Probability monad\<close>

overloading
  return_prob \<equiv> "return :: ('a, 'a prob) return"
  bind_prob \<equiv> "bind :: ('a, 'a prob) bind"
  sample_prob \<equiv> "sample :: ('p, 'a prob) sample"
begin

definition return_prob :: "('a, 'a pmf) return"
where [code_unfold, monad_unfold]: "return_prob = return_pmf"

definition bind_prob :: "('a, 'a prob) bind"
where [code_unfold, monad_unfold]: "bind_prob = bind_pmf"

definition sample_prob :: "('p, 'a pmf) sample"
where [code_unfold, monad_unfold]: "sample_prob = bind_pmf"

end

lemma monad_prob' [locale_witness]: "monad return (bind :: ('a, 'a prob) bind)"
unfolding return_prob_def bind_prob_def by(rule monad_prob)

lemma monad_commute_prob' [locale_witness]: "monad_commute return (bind :: ('a, 'a prob) bind)"
unfolding return_prob_def bind_prob_def by(rule monad_commute_prob)

lemma monad_prob_prob' [locale_witness]: "monad_prob return (bind :: ('a, 'a prob) bind) (sample :: ('p, 'a prob) sample)"
unfolding return_prob_def bind_prob_def sample_prob_def by(rule monad_prob_prob)

subsection \<open>Nondeterminism monad transformer\<close>

text \<open>As the collection type is not determined from the type of the return operation, we can
  only provide definitions for one collection type implementation. We choose multisets.
  Accordingly, @{const altc} is not available.\<close>

consts
  munionMT :: "'a itself \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm"
  mUnionMT :: "'a itself \<Rightarrow> 'm multiset \<Rightarrow> 'm"

overloading 
  return_nondetT \<equiv> "return :: ('a, ('a, 'm) nondetT) return" (unchecked)
  bind_nondetT \<equiv> "bind :: ('a, ('a, 'm) nondetT) bind" (unchecked)
  fail_nondetT \<equiv> "fail :: ('a, 'm) nondetT fail" (unchecked)
  ask_nondetT \<equiv> "ask :: ('r, ('a, 'm) nondetT) ask"
  get_nondetT \<equiv> "get :: ('s, ('a, 'm) nondetT) get"
  put_nondetT \<equiv> "put :: ('s, ('a, 'm) nondetT) put"
  alt_nondetT \<equiv> "alt :: ('a, 'm) nondetT alt" (unchecked)
  munionMT \<equiv> "munionMT :: 'a itself \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm" (unchecked)
  mUnionMT \<equiv> "mUnionMT :: 'a itself \<Rightarrow> 'm multiset \<Rightarrow> 'm" (unchecked)
begin

interpretation nondetM_base return bind "mmerge return bind" "{#}" "\<lambda>x. {#x#}" "(+)" .

definition return_nondetT :: "('a, ('a, 'm) nondetT) return"
where [code_unfold, monad_unfold]: "return_nondetT = return_nondet"

definition bind_nondetT :: "('a, ('a, 'm) nondetT) bind"
where [code_unfold, monad_unfold]: "bind_nondetT = bind_nondet" 

definition fail_nondetT :: "('a, 'm) nondetT fail"
where [code_unfold, monad_unfold]: "fail_nondetT = fail_nondet"

definition ask_nondetT :: "('r, ('a, 'm) nondetT) ask"
where [code_unfold, monad_unfold]: "ask_nondetT = ask_nondet ask"

definition get_nondetT :: "('s, ('a, 'm) nondetT) get"
where [code_unfold, monad_unfold]: "get_nondetT = get_nondet get"

definition put_nondetT :: "('s, ('a, 'm) nondetT) put"
where [code_unfold, monad_unfold]: "put_nondetT = put_nondet put"

definition alt_nondetT :: "('a, 'm) nondetT alt"
where [code_unfold, monad_unfold]: "alt_nondetT = alt_nondet"

definition munionMT :: "'a itself \<Rightarrow> 'm \<Rightarrow> 'm \<Rightarrow> 'm"
where "munionMT _ m1 m2 = bind m1 (\<lambda>A. bind m2 (\<lambda>B. return (A + B :: 'a multiset)))"

definition mUnionMT :: "'a itself \<Rightarrow> 'm multiset \<Rightarrow> 'm"
where "mUnionMT _ = fold_mset (munionMT TYPE('a)) (return ({#} :: 'a multiset))"

end

context begin
interpretation nondetM_base return bind "mmerge return bind" "{#}" "\<lambda>x. {#x#}" "(+)" .

lemma run_bind_nondetT:
  fixes f :: "'a \<Rightarrow> ('a, 'm) nondetT" shows
  "run_nondet (bind m f) = bind (run_nondet m) (\<lambda>A. mUnionMT TYPE('a) (image_mset (run_nondet \<circ> f) A))"
by(simp add: bind_nondetT_def mUnionMT_def munionMT_def[abs_def] mmerge_def)

lemma run_return_nondetT [simp]: "run_nondet (return x :: ('a, 'm) nondetT) = return {#x#}" for x :: 'a
by(simp add: return_nondetT_def)

lemma run_fail_nondetT [simp]: "run_nondet (fail :: ('a, 'm) nondetT) = return ({#} :: 'a multiset)"
by(simp add: fail_nondetT_def)

lemma run_ask_nondetT [simp]: "run_nondet (ask f) = ask (\<lambda>r. run_nondet (f r))"
by(simp add: ask_nondetT_def)

lemma run_get_nondetT [simp]: "run_nondet (get f) = get (\<lambda>s. run_nondet (f s))"
by(simp add: get_nondetT_def)

lemma run_put_nondetT [simp]: "run_nondet (put s m) = put s (run_nondet m)"
by(simp add: put_nondetT_def)

lemma run_alt_nondetT [simp]:
  "run_nondet (alt m m' :: ('a, 'm) nondetT) = 
   bind (run_nondet m) (\<lambda>A :: 'a multiset. bind (run_nondet m') (\<lambda>B. return (A + B)))"
by(simp add: alt_nondetT_def)

end

lemma monad_nondetT' [locale_witness]: 
  "monad_commute return (bind :: ('a multiset, 'm) bind)
  \<Longrightarrow> monad return (bind :: ('a, ('a, 'm) nondetT) bind)"
unfolding return_nondetT_def bind_nondetT_def by(rule mset_nondetMs)

lemma monad_fail_nondetT' [locale_witness]:
  "monad_commute return (bind :: ('a multiset, 'm) bind)
  \<Longrightarrow> monad_fail return (bind :: ('a, ('a, 'm) nondetT) bind) fail"
unfolding return_nondetT_def bind_nondetT_def fail_nondetT_def by(rule mset_nondetMs)

lemma monad_alt_nondetT' [locale_witness]: 
  "monad_commute return (bind :: ('a multiset, 'm) bind)
  \<Longrightarrow> monad_alt return (bind :: ('a, ('a, 'm) nondetT) bind) alt"
unfolding return_nondetT_def bind_nondetT_def alt_nondetT_def by(rule mset_nondetMs)

lemma monad_fail_alt_nondetT' [locale_witness]:
  "monad_commute return (bind :: ('a multiset, 'm) bind)
  \<Longrightarrow> monad_fail_alt return (bind :: ('a, ('a, 'm) nondetT) bind) fail alt"
unfolding return_nondetT_def bind_nondetT_def fail_nondetT_def alt_nondetT_def by(rule mset_nondetMs)

lemma monad_reader_nondetT' [locale_witness]:
  "\<lbrakk> monad_commute return (bind :: ('a multiset, 'm) bind);
     monad_reader return (bind :: ('a multiset, 'm) bind) (ask :: ('r, 'm) ask) \<rbrakk>
  \<Longrightarrow> monad_reader return (bind :: ('a, ('a, 'm) nondetT) bind) (ask :: ('r, ('a, 'm) nondetT) ask)"
unfolding return_nondetT_def bind_nondetT_def ask_nondetT_def by(rule mset_nondetMs)

subsection \<open>State monad transformer\<close>

overloading
  get_stateT \<equiv> "get :: ('s, ('s, 'm) stateT) get"
  put_stateT \<equiv> "put :: ('s, ('s, 'm) stateT) put"
  bind_stateT \<equiv> "bind :: ('a, ('s, 'm) stateT) bind" (unchecked)
  return_stateT \<equiv> "return :: ('a, ('s, 'm) stateT) return" (unchecked)
  fail_stateT \<equiv> "fail :: ('s, 'm) stateT fail"
  ask_stateT \<equiv> "ask :: ('r, ('s, 'm) stateT) ask"
  sample_stateT \<equiv> "sample :: ('p, ('s, 'm) stateT) sample"
  tell_stateT \<equiv> "tell :: ('w, ('s, 'm) stateT) tell"
  alt_stateT \<equiv> "alt :: ('s, 'm) stateT alt"
  altc_stateT \<equiv> "altc :: ('c, ('s, 'm) stateT) altc"
  pause_stateT \<equiv> "pause :: ('o, 'i, ('s, 'm) stateT) pause"
begin

definition get_stateT :: "('s, ('s, 'm) stateT) get"
where [code_unfold, monad_unfold]: "get_stateT = get_state"

definition put_stateT :: "('s, ('s, 'm) stateT) put"
where [code_unfold, monad_unfold]: "put_stateT = put_state"

definition bind_stateT :: "('a, ('s, 'm) stateT) bind"
where [code_unfold, monad_unfold]: "bind_stateT = bind_state bind"

definition return_stateT :: "('a, ('s, 'm) stateT) return"
where [code_unfold, monad_unfold]: "return_stateT = return_state return"

definition fail_stateT :: "('s, 'm) stateT fail"
where [code_unfold, monad_unfold]: "fail_stateT = fail_state fail"

definition ask_stateT :: "('r, ('s, 'm) stateT) ask"
where [code_unfold, monad_unfold]: "ask_stateT = ask_state ask"

definition sample_stateT :: "('p, ('s, 'm) stateT) sample"
where [code_unfold, monad_unfold]: "sample_stateT = sample_state sample"

definition tell_stateT :: "('w, ('s, 'm) stateT) tell"
where [code_unfold, monad_unfold]: "tell_stateT = tell_state tell"

definition alt_stateT :: "('s, 'm) stateT alt"
where [code_unfold, monad_unfold]: "alt_stateT = alt_state alt"

definition altc_stateT :: "('c, ('s, 'm) stateT) altc"
where [code_unfold, monad_unfold]: "altc_stateT = altc_state altc"

definition pause_stateT :: "('o, 'i, ('s, 'm) stateT) pause"
where [code_unfold, monad_unfold]: "pause_stateT = pause_state pause"

end

lemma run_bind_stateT [simp]:
  "run_state (bind x f) s = bind (run_state x s) (\<lambda>(a, s'). run_state (f a) s')"
by(simp add: bind_stateT_def)

lemma run_return_stateT [simp]: "run_state (return x) s = return (x, s)"
by(simp add: return_stateT_def)

lemma run_put_stateT [simp]: "run_state (put s m) s' = run_state m s"
by(simp add: put_stateT_def)

lemma run_get_state [simp]: "run_state (get f) s = run_state (f s) s"
by(simp add: get_stateT_def)

lemma run_fail_stateT [simp]: "run_state fail s = fail"
by(simp add: fail_stateT_def)

lemma run_ask_stateT [simp]: "run_state (ask f) s = ask (\<lambda>r. run_state (f r) s)"
by(simp add: ask_stateT_def)

lemma run_sample_stateT [simp]: "run_state (sample p f) s = sample p (\<lambda>x. run_state (f x) s)"
by(simp add: sample_stateT_def)

lemma run_tell_stateT [simp]: "run_state (tell w m) s = tell w (run_state m s)"
by(simp add: tell_stateT_def)

lemma run_alt_stateT [simp]: "run_state (alt m m') s = alt (run_state m s) (run_state m' s)"
by(simp add: alt_stateT_def)

lemma run_altc_stateT [simp]: "run_state (altc C f) s = altc C (\<lambda>x. run_state (f x) s)"
by(simp add: altc_stateT_def)

lemma run_pause_stateT [simp]: "run_state (pause out c) s = pause out (\<lambda>input. run_state (c input) s)"
by(simp add: pause_stateT_def)

lemma monad_stateT' [locale_witness]:
  "monad return (bind :: ('a \<times> 's, 'm) bind) \<Longrightarrow> monad return (bind :: ('a, ('s, 'm) stateT) bind)"
unfolding return_stateT_def bind_stateT_def by(rule monad_stateT) 

lemma monad_state_stateT' [locale_witness]:
  "monad return (bind :: ('a \<times> 's, 'm) bind) 
  \<Longrightarrow> monad_state return (bind :: ('a, ('s, 'm) stateT) bind) get (put :: ('s, ('s, 'm) stateT) put)"
unfolding return_stateT_def bind_stateT_def get_stateT_def put_stateT_def by(rule monad_state_stateT) 

lemma monad_fail_stateT' [locale_witness]:
  "monad_fail return (bind :: ('a \<times> 's, 'm) bind) fail
  \<Longrightarrow> monad_fail return (bind :: ('a, ('s, 'm) stateT) bind) fail"
unfolding return_stateT_def bind_stateT_def fail_stateT_def by(rule monad_fail_stateT)

lemma monad_reader_stateT' [locale_witness]:
  "monad_reader return (bind :: ('a \<times> 's, 'm) bind) (ask :: ('r, 'm) ask)
  \<Longrightarrow> monad_reader return (bind :: ('a, ('s, 'm) stateT) bind) (ask :: ('r, ('s, 'm) stateT) ask)"
unfolding return_stateT_def bind_stateT_def ask_stateT_def by(rule monad_reader_stateT)

lemma monad_reader_state_stateT' [locale_witness]:
  "monad_reader return (bind :: ('a \<times> 's, 'm) bind) (ask :: ('r, 'm) ask)
  \<Longrightarrow> monad_reader_state return (bind :: ('a, ('s, 'm) stateT) bind) (ask :: ('r, ('s, 'm) stateT) ask) get_state put_state"
unfolding return_stateT_def bind_stateT_def ask_stateT_def by(rule monad_reader_state_stateT)

lemma monad_prob_stateT' [locale_witness]:
  "monad_prob return (bind :: ('a \<times> 's, 'm) bind) (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_prob return (bind :: ('a, ('s, 'm) stateT) bind) (sample :: ('p, ('s, 'm) stateT) sample)"
unfolding return_stateT_def bind_stateT_def sample_stateT_def by(rule monad_prob_stateT)

lemma monad_state_prob_stateT' [locale_witness]:
  "monad_prob return (bind :: ('a \<times> 's, 'm) bind) (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_state_prob return (bind :: ('a, ('s, 'm) stateT) bind) get (put :: ('s, ('s, 'm) stateT) put) (sample :: ('p, ('s, 'm) stateT) sample)"
unfolding return_stateT_def bind_stateT_def sample_stateT_def get_stateT_def put_stateT_def by(rule monad_state_prob_stateT)

lemma monad_writer_stateT' [locale_witness]:
  "monad_writer return (bind :: ('a \<times> 's, 'm) bind) (tell :: ('w, 'm) tell)
  \<Longrightarrow> monad_writer return (bind :: ('a, ('s, 'm) stateT) bind) (tell :: ('w, ('s, 'm) stateT) tell)"
unfolding return_stateT_def bind_stateT_def tell_stateT_def by(rule monad_writer_stateT)

lemma monad_alt_stateT' [locale_witness]:
  "monad_alt return (bind :: ('a \<times> 's, 'm) bind) alt
   \<Longrightarrow> monad_alt return (bind :: ('a, ('s, 'm) stateT) bind) alt"
unfolding return_stateT_def bind_stateT_def alt_stateT_def by(rule monad_alt_stateT)

lemma monad_state_alt_stateT' [locale_witness]:
  "monad_alt return (bind :: ('a \<times> 's, 'm) bind) alt
   \<Longrightarrow> monad_state_alt return (bind :: ('a, ('s, 'm) stateT) bind) (get :: ('s, ('s, 'm) stateT) get) put alt"
unfolding return_stateT_def bind_stateT_def get_stateT_def put_stateT_def alt_stateT_def by(rule monad_state_alt_stateT)

lemma monad_fail_alt_stateT' [locale_witness]:
  "monad_fail_alt return (bind :: ('a \<times> 's, 'm) bind) fail alt
   \<Longrightarrow> monad_fail_alt return (bind :: ('a, ('s, 'm) stateT) bind) fail alt"
unfolding return_stateT_def bind_stateT_def fail_stateT_def alt_stateT_def by(rule monad_fail_alt_stateT)

lemma monad_altc_stateT' [locale_witness]:
  "monad_altc return (bind :: ('a \<times> 's, 'm) bind) (altc :: ('c, 'm) altc)
   \<Longrightarrow> monad_altc return (bind :: ('a, ('s, 'm) stateT) bind) (altc :: ('c, ('s, 'm) stateT) altc)"
unfolding return_stateT_def bind_stateT_def altc_stateT_def by(rule monad_altc_stateT)

lemma monad_state_altc_stateT' [locale_witness]:
  "monad_altc return (bind :: ('a \<times> 's, 'm) bind) (altc :: ('c, 'm) altc)
   \<Longrightarrow> monad_state_altc return (bind :: ('a, ('s, 'm) stateT) bind) (get :: ('s, ('s, 'm) stateT) get) put (altc :: ('c, ('s, 'm) stateT) altc)"
unfolding return_stateT_def bind_stateT_def get_stateT_def put_stateT_def altc_stateT_def by(rule monad_state_altc_stateT)

lemma monad_resumption_stateT' [locale_witness]:
  "monad_resumption return (bind :: ('a \<times> 's, 'm) bind) (pause :: ('o, 'i, 'm) pause)
   \<Longrightarrow> monad_resumption return (bind :: ('a, ('s, 'm) stateT) bind) (pause :: ('o, 'i, ('s, 'm) stateT) pause)"
unfolding return_stateT_def bind_stateT_def fail_stateT_def pause_stateT_def by(rule monad_resumption_stateT)

subsection \<open>Failure and Exception monad transformer\<close>

overloading 
  return_optionT \<equiv> "return :: ('a, ('a, 'm) optionT) return" (unchecked)
  bind_optionT \<equiv> "bind :: ('a, ('a, 'm) optionT) bind" (unchecked)
  fail_optionT \<equiv> "fail :: ('a, 'm) optionT fail" (unchecked)
  catch_optionT \<equiv> "catch :: ('a, 'm) optionT catch" (unchecked)
  ask_optionT \<equiv> "ask :: ('r, ('a, 'm) optionT) ask"
  get_optionT \<equiv> "get :: ('s, ('a, 'm) optionT) get"
  put_optionT \<equiv> "put :: ('s, ('a, 'm) optionT) put"
  sample_optionT \<equiv> "sample :: ('p, ('a, 'm) optionT) sample"
  tell_optionT \<equiv> "tell :: ('w, ('a, 'm) optionT) tell"
  alt_optionT \<equiv> "alt :: ('a, 'm) optionT alt"
  altc_optionT \<equiv> "altc :: ('c, ('a, 'm) optionT) altc"
  pause_optionT \<equiv> "pause :: ('o, 'i, ('a, 'm) optionT) pause"
begin

definition return_optionT :: "('a, ('a, 'm) optionT) return"
where [code_unfold, monad_unfold]: "return_optionT = return_option return"

definition bind_optionT :: "('a, ('a, 'm) optionT) bind"
where [code_unfold, monad_unfold]: "bind_optionT = bind_option return bind" 

definition fail_optionT :: "('a, 'm) optionT fail"
where [code_unfold, monad_unfold]: "fail_optionT = fail_option return"

definition catch_optionT :: "('a, 'm) optionT catch"
where [code_unfold, monad_unfold]: "catch_optionT = catch_option return bind"

definition ask_optionT :: "('r, ('a, 'm) optionT) ask"
where [code_unfold, monad_unfold]: "ask_optionT = ask_option ask"

definition get_optionT :: "('s, ('a, 'm) optionT) get"
where [code_unfold, monad_unfold]: "get_optionT = get_option get"

definition put_optionT :: "('s, ('a, 'm) optionT) put"
where [code_unfold, monad_unfold]: "put_optionT = put_option put"

definition sample_optionT :: "('p, ('a, 'm) optionT) sample"
where [code_unfold, monad_unfold]: "sample_optionT = sample_option sample"

definition tell_optionT :: "('w, ('a, 'm) optionT) tell"
where [code_unfold, monad_unfold]: "tell_optionT = tell_option tell"

definition alt_optionT :: "('a, 'm) optionT alt"
where [code_unfold, monad_unfold]: "alt_optionT = alt_option alt"

definition altc_optionT :: "('c, ('a, 'm) optionT) altc"
where [code_unfold, monad_unfold]: "altc_optionT = altc_option altc"

definition pause_optionT :: "('o, 'i, ('a, 'm) optionT) pause"
where [code_unfold, monad_unfold]: "pause_optionT = pause_option pause"

end

lemma run_bind_optionT:
  fixes f :: "'a \<Rightarrow> ('a, 'm) optionT" shows
  "run_option (bind x f) = bind (run_option x) (\<lambda>x. case x of None \<Rightarrow> return (None :: 'a option) | Some y \<Rightarrow> run_option (f y))"
by(simp add: bind_optionT_def run_bind_option)

lemma run_return_optionT [simp]: "run_option (return x :: ('a, 'm) optionT) = return (Some x)" for x :: 'a
by(simp add: return_optionT_def)

lemma run_fail_optionT [simp]: "run_option (fail :: ('a, 'm) optionT fail) = return (None :: 'a option)"
by(simp add: fail_optionT_def)

lemma run_catch_optionT [simp]: 
  "run_option (catch m h :: ('a, 'm) optionT) = 
   bind (run_option m) (\<lambda>x :: 'a option. if x = None then run_option h else return x)"
by(simp add: catch_optionT_def)

lemma run_ask_optionT [simp]: "run_option (ask f) = ask (\<lambda>r. run_option (f r))"
by(simp add: ask_optionT_def)

lemma run_get_optionT [simp]: "run_option (get f) = get (\<lambda>s. run_option (f s))"
by(simp add: get_optionT_def)

lemma run_put_optionT [simp]: "run_option (put s m) = put s (run_option m)"
by(simp add: put_optionT_def)

lemma run_sample_optionT [simp]: "run_option (sample p f) = sample p (\<lambda>x. run_option (f x))"
by(simp add: sample_optionT_def)

lemma run_tell_optionT [simp]: "run_option (tell w m) = tell w (run_option m)"
by(simp add: tell_optionT_def)

lemma run_alt_optionT [simp]: "run_option (alt m m') = alt (run_option m) (run_option m')"
by(simp add: alt_optionT_def)

lemma run_altc_optionT [simp]: "run_option (altc C f) = altc C (run_option \<circ> f)"
by(simp add: altc_optionT_def o_def)

lemma run_pause_optionT [simp]: "run_option (pause out c) = pause out (\<lambda>input. run_option (c input))"
by(simp add: pause_optionT_def)

lemma monad_optionT' [locale_witness]:
  "monad return (bind :: ('a option, 'm) bind)
  \<Longrightarrow> monad return (bind :: ('a, ('a, 'm) optionT) bind)"
unfolding return_optionT_def bind_optionT_def by(rule monad_optionT)

lemma monad_fail_optionT' [locale_witness]:
  "monad return (bind :: ('a option, 'm) bind)
  \<Longrightarrow> monad_fail return (bind :: ('a, ('a, 'm) optionT) bind) fail"
unfolding return_optionT_def bind_optionT_def fail_optionT_def by(rule monad_fail_optionT)

lemma monad_catch_optionT' [locale_witness]:
  "monad return (bind :: ('a option, 'm) bind)
  \<Longrightarrow> monad_catch return (bind :: ('a, ('a, 'm) optionT) bind) fail catch"
unfolding return_optionT_def bind_optionT_def fail_optionT_def catch_optionT_def by(rule monad_catch_optionT)

lemma monad_reader_optionT' [locale_witness]:
  "monad_reader return (bind :: ('a option, 'm) bind) (ask :: ('r, 'm) ask)
  \<Longrightarrow> monad_reader return (bind :: ('a, ('a, 'm) optionT) bind) (ask :: ('r, ('a, 'm) optionT) ask)"
unfolding return_optionT_def bind_optionT_def ask_optionT_def
by(rule monad_reader_optionT)

lemma monad_state_optionT' [locale_witness]:
  "monad_state return (bind :: ('a option, 'm) bind) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_state return (bind :: ('a, ('a, 'm) optionT) bind) (get :: ('s, ('a, 'm) optionT) get) put"
unfolding return_optionT_def bind_optionT_def get_optionT_def put_optionT_def
by(rule monad_state_optionT)

lemma monad_catch_state_optionT' [locale_witness]:
  "monad_state return (bind :: ('a option, 'm) bind) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_catch_state return (bind :: ('a, ('a, 'm) optionT) bind) fail catch (get :: ('s, ('a, 'm) optionT) get) put"
unfolding return_optionT_def bind_optionT_def fail_optionT_def catch_optionT_def get_optionT_def put_optionT_def
by(rule monad_catch_state_optionT)

lemma monad_prob_optionT' [locale_witness]:
  "monad_prob return (bind :: ('a option, 'm) bind) (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_prob return (bind :: ('a, ('a, 'm) optionT) bind) (sample :: ('p, ('a, 'm) optionT) sample)"
unfolding return_optionT_def bind_optionT_def sample_optionT_def
by(rule monad_prob_optionT)

lemma monad_state_prob_optionT' [locale_witness]:
  "monad_state_prob return (bind :: ('a option, 'm) bind) (get :: ('s, 'm) get) put (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_state_prob return (bind :: ('a, ('a, 'm) optionT) bind) (get :: ('s, ('a, 'm) optionT) get) put(sample :: ('p, ('a, 'm) optionT) sample)"
unfolding return_optionT_def bind_optionT_def get_optionT_def put_optionT_def sample_optionT_def
by(rule monad_state_prob_optionT)

lemma monad_writer_optionT' [locale_witness]:
  "monad_writer return (bind :: ('a option, 'm) bind) (tell :: ('w, 'm) tell)
  \<Longrightarrow> monad_writer return (bind :: ('a, ('a, 'm) optionT) bind) (tell :: ('w, ('a, 'm) optionT) tell)"
unfolding return_optionT_def bind_optionT_def tell_optionT_def by(rule monad_writer_optionT)

lemma monad_alt_optionT' [locale_witness]:
  "monad_alt return (bind :: ('a option, 'm) bind) alt
  \<Longrightarrow> monad_alt return (bind :: ('a, ('a, 'm) optionT) bind) alt"
unfolding return_optionT_def bind_optionT_def alt_optionT_def by(rule monad_alt_optionT)

lemma monad_state_alt_optionT' [locale_witness]:
  "monad_state_alt return (bind :: ('a option, 'm) bind) (get :: ('s, 'm) get) put alt
  \<Longrightarrow> monad_state_alt return (bind :: ('a, ('a, 'm) optionT) bind) (get :: ('s, ('a, 'm) optionT) get) put alt"
unfolding return_optionT_def bind_optionT_def alt_optionT_def get_optionT_def put_optionT_def by(rule monad_state_alt_optionT)

lemma monad_altc_optionT' [locale_witness]:
  "monad_altc return (bind :: ('a option, 'm) bind) (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_altc return (bind :: ('a, ('a, 'm) optionT) bind) (altc :: ('c, ('a, 'm) optionT) altc)"
unfolding return_optionT_def bind_optionT_def altc_optionT_def by(rule monad_altc_optionT)

lemma monad_state_altc_optionT' [locale_witness]:
  "monad_state_altc return (bind :: ('a option, 'm) bind) (get :: ('s, 'm) get) put (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_state_altc return (bind :: ('a, ('a, 'm) optionT) bind) (get :: ('s, ('a, 'm) optionT) get) put (altc :: ('c, ('a, 'm) optionT) altc)"
unfolding return_optionT_def bind_optionT_def altc_optionT_def get_optionT_def put_optionT_def by(rule monad_state_altc_optionT)

lemma monad_resumption_optionT' [locale_witness]:
  "monad_resumption return (bind :: ('a option, 'm) bind) (pause :: ('o, 'i, 'm) pause)
  \<Longrightarrow> monad_resumption return (bind :: ('a, ('a, 'm) optionT) bind) (pause :: ('o, 'i, ('a, 'm) optionT) pause)"
unfolding return_optionT_def bind_optionT_def pause_optionT_def by(rule monad_resumption_optionT)

lemma monad_commute_optionT' [locale_witness]:
  "\<lbrakk> monad_commute return (bind :: ('a option, 'm) bind); monad_discard return (bind :: ('a option, 'm) bind) \<rbrakk>
  \<Longrightarrow> monad_commute return (bind :: ('a, ('a, 'm) optionT) bind)"
unfolding return_optionT_def bind_optionT_def by(rule monad_commute_optionT)


subsection \<open>Reader monad transformer\<close>

overloading
  return_envT \<equiv> "return :: ('a, ('r, 'm) envT) return"
  bind_envT \<equiv> "bind :: ('a, ('r, 'm) envT) bind"
  fail_envT \<equiv> "fail :: ('r, 'm) envT fail"
  get_envT \<equiv> "get :: ('s, ('r, 'm) envT) get"
  put_envT \<equiv> "put :: ('s, ('r, 'm) envT) put"
  sample_envT \<equiv> "sample :: ('p, ('r, 'm) envT) sample"
  ask_envT \<equiv> "ask :: ('r, ('r, 'm) envT) ask"
  catch_envT \<equiv> "catch :: ('r, 'm) envT catch"
  alt_envT \<equiv> "alt :: ('r, 'm) envT alt"
  altc_envT \<equiv> "altc :: ('c, ('r, 'm) envT) altc"
  pause_envT \<equiv> "pause :: ('o, 'i, ('r, 'm) envT) pause"
  tell_envT \<equiv> "tell :: ('w, ('r, 'm) envT) tell"
begin

definition return_envT :: "('a, ('r, 'm) envT) return"
where [code_unfold, monad_unfold]: "return_envT = return_env return"

definition bind_envT :: "('a, ('r, 'm) envT) bind"
where [code_unfold, monad_unfold]: "bind_envT = bind_env bind"

definition ask_envT :: "('r, ('r, 'm) envT) ask"
where [code_unfold, monad_unfold]: "ask_envT = ask_env"

definition fail_envT :: "('r, 'm) envT fail"
where [code_unfold, monad_unfold]: "fail_envT = fail_env fail"

definition get_envT :: "('s, ('r, 'm) envT) get"
where [code_unfold, monad_unfold]: "get_envT = get_env get"

definition put_envT :: "('s, ('r, 'm) envT) put"
where [code_unfold, monad_unfold]: "put_envT = put_env put"

definition sample_envT :: "('p, ('r, 'm) envT) sample"
where [code_unfold, monad_unfold]: "sample_envT = sample_env sample"

definition catch_envT :: "('r, 'm) envT catch"
where [code_unfold, monad_unfold]: "catch_envT = catch_env catch"

definition alt_envT :: "('r, 'm) envT alt"
where [code_unfold, monad_unfold]: "alt_envT = alt_env alt"

definition altc_envT :: "('c, ('r, 'm) envT) altc"
where [code_unfold, monad_unfold]: "altc_envT = altc_env altc"

definition pause_envT :: "('o, 'i, ('r, 'm) envT) pause"
where [code_unfold, monad_unfold]: "pause_envT = pause_env pause"

definition tell_envT :: "('w, ('r, 'm) envT) tell"
where [code_unfold, monad_unfold]: "tell_envT = tell_env tell"

end

lemma run_bind_envT [simp]: "run_env (bind x f) r = bind (run_env x r) (\<lambda>y. run_env (f y) r)"
by(simp add: bind_envT_def)

lemma run_return_envT [simp]: "run_env (return x) r = return x"
by(simp add: return_envT_def)

lemma run_ask_envT [simp]: "run_env (ask f) r = run_env (f r) r"
by(simp add: ask_envT_def)

lemma run_fail_envT [simp]: "run_env fail r = fail"
by(simp add: fail_envT_def)

lemma run_get_envT [simp]: "run_env (get f) r = get (\<lambda>s. run_env (f s) r)"
by(simp add: get_envT_def)

lemma run_put_envT [simp]: "run_env (put s m) r = put s (run_env m r)"
by(simp add: put_envT_def)

lemma run_sample_envT [simp]: "run_env (sample p f) r = sample p (\<lambda>x. run_env (f x) r)"
by(simp add: sample_envT_def)

lemma run_catch_envT [simp]: "run_env (catch m h) r = catch (run_env m r) (run_env h r)"
by(simp add: catch_envT_def)

lemma run_alt_envT [simp]: "run_env (alt m m') r = alt (run_env m r) (run_env m' r)"
by(simp add: alt_envT_def)

lemma run_altc_envT [simp]: "run_env (altc C f) r = altc C (\<lambda>x. run_env (f x) r)"
by(simp add: altc_envT_def)

lemma run_pause_envT [simp]: "run_env (pause out c) r = pause out (\<lambda>input. run_env (c input) r)"
by(simp add: pause_envT_def)

lemma run_tell_envT [simp]: "run_env (tell s m) r = tell s (run_env m r)"
by(simp add: tell_envT_def)

lemma monad_envT' [locale_witness]: 
  "monad return (bind :: ('a, 'm) bind)
  \<Longrightarrow> monad return (bind :: ('a, ('r, 'm) envT) bind)"
unfolding return_envT_def bind_envT_def by(rule monad_envT)

lemma monad_reader_envT' [locale_witness]: 
  "monad return (bind :: ('a, 'm) bind)
  \<Longrightarrow> monad_reader return (bind :: ('a, ('r, 'm) envT) bind) (ask :: ('r, ('r, 'm) envT) ask)"
unfolding return_envT_def bind_envT_def ask_envT_def by(rule monad_reader_envT)

lemma monad_fail_envT' [locale_witness]:
  "monad_fail return (bind :: ('a, 'm) bind) fail
  \<Longrightarrow> monad_fail return (bind :: ('a, ('r, 'm) envT) bind) fail"
unfolding return_envT_def bind_envT_def fail_envT_def by(rule monad_fail_envT)

lemma monad_catch_envT' [locale_witness]:
  "monad_catch return (bind :: ('a, 'm) bind) fail catch
  \<Longrightarrow> monad_catch return (bind :: ('a, ('r, 'm) envT) bind) fail catch"
unfolding return_envT_def bind_envT_def fail_envT_def catch_envT_def by(rule monad_catch_envT)

lemma monad_state_envT' [locale_witness]:
  "monad_state return (bind :: ('a, 'm) bind) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_state return (bind :: ('a, ('r, 'm) envT) bind) (get :: ('s, ('r, 'm) envT) get) put"
unfolding return_envT_def bind_envT_def get_envT_def put_envT_def by(rule monad_state_envT)

lemma monad_prob_envT' [locale_witness]:
  "monad_prob return (bind :: ('a, 'm) bind) (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_prob return (bind :: ('a, ('r, 'm) envT) bind) (sample :: ('p, ('r, 'm) envT) sample)"
unfolding return_envT_def bind_envT_def sample_envT_def by(rule monad_prob_envT)

lemma monad_state_prob_envT' [locale_witness]:
  "monad_state_prob return (bind :: ('a, 'm) bind) (get :: ('s, 'm) get) put (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_state_prob return (bind :: ('a, ('r, 'm) envT) bind) (get :: ('s, ('r, 'm) envT) get) put (sample :: ('p, ('r, 'm) envT) sample)"
unfolding return_envT_def bind_envT_def sample_envT_def get_envT_def put_envT_def  by(rule monad_state_prob_envT)

lemma monad_alt_envT' [locale_witness]:
  "monad_alt return (bind :: ('a, 'm) bind) alt
  \<Longrightarrow> monad_alt return (bind :: ('a, ('r, 'm) envT) bind) alt"
unfolding return_envT_def bind_envT_def alt_envT_def by(rule monad_alt_envT)

lemma monad_fail_alt_envT' [locale_witness]:
  "monad_fail_alt return (bind :: ('a, 'm) bind) fail alt
  \<Longrightarrow> monad_fail_alt return (bind :: ('a, ('r, 'm) envT) bind) fail alt"
unfolding return_envT_def bind_envT_def fail_envT_def alt_envT_def by(rule monad_fail_alt_envT)

lemma monad_state_alt_envT' [locale_witness]:
  "monad_state_alt return (bind :: ('a, 'm) bind) (get :: ('s, 'm) get) put alt
  \<Longrightarrow> monad_state_alt return (bind :: ('a, ('r, 'm) envT) bind) (get :: ('s, ('r, 'm) envT) get) put alt"
unfolding return_envT_def bind_envT_def fail_envT_def get_envT_def put_envT_def alt_envT_def by(rule monad_state_alt_envT)

lemma monad_altc_envT' [locale_witness]:
  "monad_altc return (bind :: ('a, 'm) bind) (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_altc return (bind :: ('a, ('r, 'm) envT) bind) (altc :: ('c, ('r, 'm) envT) altc)"
unfolding return_envT_def bind_envT_def altc_envT_def by(rule monad_altc_envT)

lemma monad_state_altc_envT' [locale_witness]:
  "monad_state_altc return (bind :: ('a, 'm) bind) (get :: ('s, 'm) get) put (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_state_altc return (bind :: ('a, ('r, 'm) envT) bind) (get :: ('s, ('r, 'm) envT) get) put (altc :: ('c, ('r, 'm) envT) altc)"
unfolding return_envT_def bind_envT_def fail_envT_def get_envT_def put_envT_def altc_envT_def by(rule monad_state_altc_envT)

lemma monad_resumption_envT' [locale_witness]:
  "monad_resumption return (bind :: ('a, 'm) bind) (pause :: ('o, 'i, 'm) pause)
  \<Longrightarrow> monad_resumption return (bind :: ('a, ('r, 'm) envT) bind) (pause :: ('o, 'i, ('r, 'm) envT) pause)"
unfolding return_envT_def bind_envT_def pause_envT_def by(rule monad_resumption_envT)

lemma monad_writer_readerT' [locale_witness]:
  "monad_writer return (bind :: ('a, 'm) bind) (tell :: ('w, 'm) tell)
  \<Longrightarrow> monad_writer return (bind :: ('a, ('r, 'm) envT) bind) (tell :: ('w, ('r, 'm) envT) tell)"
unfolding return_envT_def bind_envT_def tell_envT_def by(rule monad_writer_envT)

lemma monad_commute_envT' [locale_witness]:
  "monad_commute return (bind :: ('a, 'm) bind)
  \<Longrightarrow> monad_commute return (bind :: ('a, ('r, 'm) envT) bind)"
unfolding return_envT_def bind_envT_def by(rule monad_commute_envT)

lemma monad_discard_envT' [locale_witness]:
  "monad_discard return (bind :: ('a, 'm) bind)
  \<Longrightarrow> monad_discard return (bind :: ('a, ('r, 'm) envT) bind)"
unfolding return_envT_def bind_envT_def by(rule monad_discard_envT)

subsection \<open>Writer monad transformer\<close>

overloading
  return_writerT \<equiv> "return :: ('a, ('w, 'a, 'm) writerT) return" (unchecked)
  bind_writerT \<equiv> "bind :: ('a, ('w, 'a, 'm) writerT) bind" (unchecked)
  fail_writerT \<equiv> "fail :: ('w, 'a, 'm) writerT fail"
  get_writerT \<equiv> "get :: ('s, ('w, 'a, 'm) writerT) get"
  put_writerT \<equiv> "put :: ('s, ('w, 'a, 'm) writerT) put"
  sample_writerT \<equiv> "sample :: ('p, ('w, 'a, 'm) writerT) sample"
  ask_writerT \<equiv> "ask :: ('r, ('w, 'a, 'm) writerT) ask"
  alt_writerT \<equiv> "alt :: ('w, 'a, 'm) writerT alt"
  altc_writerT \<equiv> "altc :: ('c, ('w, 'a, 'm) writerT) altc"
  pause_writerT \<equiv> "pause :: ('o, 'i, ('w, 'a, 'm) writerT) pause"
  tell_writerT \<equiv> "tell :: ('w, ('w, 'a, 'm) writerT) tell" (unchecked)
begin

definition return_writerT :: "('a, ('w, 'a, 'm) writerT) return"
where [code_unfold, monad_unfold]: "return_writerT = return_writer return"

definition bind_writerT :: "('a, ('w, 'a, 'm) writerT) bind"
where [code_unfold, monad_unfold]: "bind_writerT = bind_writer return bind"
                                                     
definition ask_writerT :: "('r, ('w, 'a, 'm) writerT) ask"
where [code_unfold, monad_unfold]: "ask_writerT = ask_writer ask"
                                                   
definition fail_writerT :: "('w, 'a, 'm) writerT fail"
where [code_unfold, monad_unfold]: "fail_writerT = fail_writer fail"

definition get_writerT :: "('s, ('w, 'a, 'm) writerT) get"
where [code_unfold, monad_unfold]: "get_writerT = get_writer get"

definition put_writerT :: "('s, ('w, 'a, 'm) writerT) put"
where [code_unfold, monad_unfold]: "put_writerT = put_writer put"

definition sample_writerT :: "('p, ('w, 'a, 'm) writerT) sample"
where [code_unfold, monad_unfold]: "sample_writerT = sample_writer sample"

definition alt_writerT :: "('w, 'a, 'm) writerT alt"
where [code_unfold, monad_unfold]: "alt_writerT = alt_writer alt"

definition altc_writerT :: "('c, ('w, 'a, 'm) writerT) altc"
where [code_unfold, monad_unfold]: "altc_writerT = altc_writer altc"

definition pause_writerT :: "('o, 'i, ('w, 'a, 'm) writerT) pause"
where [code_unfold, monad_unfold]: "pause_writerT = pause_writer pause"

definition tell_writerT :: "('w, ('w, 'a, 'm) writerT) tell"
where [code_unfold, monad_unfold]: "tell_writerT = tell_writer return bind"

end

lemma run_bind_writerT [simp]: 
  "run_writer (bind m f :: ('w, 'a, 'm) writerT) = bind (run_writer m) (\<lambda>(a :: 'a, ws :: 'w list). bind (run_writer (f a)) (\<lambda>(b :: 'a, ws' :: 'w list). return (b, ws @ ws')))"
by(simp add: bind_writerT_def)

lemma run_return_writerT [simp]: "run_writer (return x :: ('w, 'a, 'm) writerT) = return (x :: 'a, [] :: 'w list)"
by(simp add: return_writerT_def)

lemma run_ask_writerT [simp]: "run_writer (ask f) = ask (\<lambda>r. run_writer (f r))"
by(simp add: ask_writerT_def)

lemma run_fail_writerT [simp]: "run_writer fail = fail"
by(simp add: fail_writerT_def)

lemma run_get_writerT [simp]: "run_writer (get f) = get (\<lambda>s. run_writer (f s))"
by(simp add: get_writerT_def)

lemma run_put_writerT [simp]: "run_writer (put s m) = put s (run_writer m)"
by(simp add: put_writerT_def)

lemma run_sample_writerT [simp]: "run_writer (sample p f) = sample p (\<lambda>x. run_writer (f x))"
by(simp add: sample_writerT_def)

lemma run_alt_writerT [simp]: "run_writer (alt m m') = alt (run_writer m) (run_writer m')"
by(simp add: alt_writerT_def)

lemma run_altc_writerT [simp]: "run_writer (altc C f) = altc C (run_writer \<circ> f)"
by(simp add: altc_writerT_def o_def)

lemma run_pause_writerT [simp]: "run_writer (pause out c) = pause out (\<lambda>input. run_writer (c input))"
by(simp add: pause_writerT_def)

lemma run_tell_writerT [simp]: 
  "run_writer (tell (w :: 'w) m :: ('w, 'a, 'm) writerT) = 
  bind (run_writer m) (\<lambda>(a :: 'a, ws :: 'w list). return (a, w # ws))"
by(simp add: tell_writerT_def)

lemma monad_writerT' [locale_witness]: 
  "monad return (bind :: ('a \<times> 'w list, 'm) bind)
  \<Longrightarrow> monad return (bind :: ('a, ('w, 'a, 'm) writerT) bind)"
unfolding return_writerT_def bind_writerT_def by(rule monad_writerT)

lemma monad_writer_writerT' [locale_witness]: 
  "monad return (bind :: ('a \<times> 'w list, 'm) bind)
  \<Longrightarrow> monad_writer return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (tell :: ('w, ('w, 'a, 'm) writerT) tell)"
unfolding return_writerT_def bind_writerT_def tell_writerT_def by(rule monad_writer_writerT)

lemma monad_fail_writerT' [locale_witness]:
  "monad_fail return (bind :: ('a \<times> 'w list, 'm) bind) fail
  \<Longrightarrow> monad_fail return (bind :: ('a, ('w, 'a, 'm) writerT) bind) fail"
unfolding return_writerT_def bind_writerT_def fail_writerT_def by(rule monad_fail_writerT)

lemma monad_state_writerT' [locale_witness]:
  "monad_state return (bind :: ('a \<times> 'w list, 'm) bind) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_state return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (get :: ('s, ('w, 'a, 'm) writerT) get) put"
unfolding return_writerT_def bind_writerT_def get_writerT_def put_writerT_def by(rule monad_state_writerT)

lemma monad_prob_writerT' [locale_witness]:
  "monad_prob return (bind :: ('a \<times> 'w list, 'm) bind) (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_prob return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (sample :: ('p, ('w, 'a, 'm) writerT) sample)"
unfolding return_writerT_def bind_writerT_def sample_writerT_def by(rule monad_prob_writerT)

lemma monad_state_prob_writerT' [locale_witness]:
  "monad_state_prob return (bind :: ('a \<times> 'w list, 'm) bind) (get :: ('s, 'm) get) put (sample :: ('p, 'm) sample)
  \<Longrightarrow> monad_state_prob return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (get :: ('s, ('w, 'a, 'm) writerT) get) put (sample :: ('p, ('w, 'a, 'm) writerT) sample)"
unfolding return_writerT_def bind_writerT_def sample_writerT_def get_writerT_def put_writerT_def by(rule monad_state_prob_writerT)

lemma monad_reader_writerT' [locale_witness]: 
  "monad_reader return (bind :: ('a \<times> 'w list, 'm) bind) (ask :: ('r, 'm) ask)
  \<Longrightarrow> monad_reader return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (ask :: ('r, ('w, 'a, 'm) writerT) ask)"
unfolding return_writerT_def bind_writerT_def ask_writerT_def by(rule monad_reader_writerT)

lemma monad_reader_state_writerT' [locale_witness]: 
  "monad_reader_state return (bind :: ('a \<times> 'w list, 'm) bind) (ask :: ('r, 'm) ask) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_reader_state return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (ask :: ('r, ('w, 'a, 'm) writerT) ask) (get :: ('s, ('w, 'a, 'm) writerT) get) put"
unfolding return_writerT_def bind_writerT_def ask_writerT_def get_writerT_def put_writerT_def by(rule monad_reader_state_writerT)

lemma monad_resumption_writerT' [locale_witness]:
  "monad_resumption return (bind :: ('a \<times> 'w list, 'm) bind) (pause :: ('o, 'i, 'm) pause)
  \<Longrightarrow> monad_resumption return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (pause :: ('o, 'i, ('w, 'a, 'm) writerT) pause)"
unfolding return_writerT_def bind_writerT_def pause_writerT_def by(rule monad_resumption_writerT)

lemma monad_alt_writerT' [locale_witness]:
  "monad_alt return (bind :: ('a \<times> 'w list, 'm) bind) alt
  \<Longrightarrow> monad_alt return (bind :: ('a, ('w, 'a, 'm) writerT) bind) alt"
unfolding return_writerT_def bind_writerT_def alt_writerT_def by(rule monad_alt_writerT)

lemma monad_fail_alt_writerT' [locale_witness]:
  "monad_fail_alt return (bind :: ('a \<times> 'w list, 'm) bind) fail alt
  \<Longrightarrow> monad_fail_alt return (bind :: ('a, ('w, 'a, 'm) writerT) bind) fail alt"
unfolding return_writerT_def bind_writerT_def fail_writerT_def alt_writerT_def by(rule monad_fail_alt_writerT)

lemma monad_state_alt_writerT' [locale_witness]:
  "monad_state_alt return (bind :: ('a \<times> 'w list, 'm) bind) (get :: ('s, 'm) get) put alt
  \<Longrightarrow> monad_state_alt return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (get :: ('s, ('w, 'a, 'm) writerT) get) put alt"
unfolding return_writerT_def bind_writerT_def get_writerT_def put_writerT_def alt_writerT_def by(rule monad_state_alt_writerT)

lemma monad_altc_writerT' [locale_witness]:
  "monad_altc return (bind :: ('a \<times> 'w list, 'm) bind) (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_altc return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (altc :: ('c, ('w, 'a, 'm) writerT) altc)"
unfolding return_writerT_def bind_writerT_def altc_writerT_def by(rule monad_altc_writerT)

lemma monad_state_altc_writerT' [locale_witness]:
  "monad_state_altc return (bind :: ('a \<times> 'w list, 'm) bind) (get :: ('s, 'm) get) put (altc :: ('c, 'm) altc)
  \<Longrightarrow> monad_state_altc return (bind :: ('a, ('w, 'a, 'm) writerT) bind) (get :: ('s, ('w, 'a, 'm) writerT) get) put (altc :: ('c, ('w, 'a, 'm) writerT) altc)"
unfolding return_writerT_def bind_writerT_def get_writerT_def put_writerT_def altc_writerT_def by(rule monad_state_altc_writerT)

subsection \<open>Continuation monad transformer\<close>

overloading
  return_contT \<equiv> "return :: ('a, ('a, 'm) contT) return"
  bind_contT \<equiv> "bind :: ('a, ('a, 'm) contT) bind"
  fail_contT \<equiv> "fail :: ('a, 'm) contT fail"
  get_contT \<equiv> "get :: ('s, ('a, 'm) contT) get"
  put_contT \<equiv> "put :: ('s, ('a, 'm) contT) put"
begin

definition return_contT :: "('a, ('a, 'm) contT) return"
where [code_unfold, monad_unfold]: "return_contT = return_cont"

definition bind_contT :: "('a, ('a, 'm) contT) bind"
where [code_unfold, monad_unfold]: "bind_contT = bind_cont"

definition fail_contT :: "('a, 'm) contT fail"
where [code_unfold, monad_unfold]: "fail_contT = fail_cont fail"

definition get_contT :: "('s, ('a, 'm) contT) get"
where [code_unfold, monad_unfold]: "get_contT = get_cont get"

definition put_contT :: "('s, ('a, 'm) contT) put"
where [code_unfold, monad_unfold]: "put_contT = put_cont put"

end

lemma monad_contT' [locale_witness]: "monad return (bind :: ('a, ('a, 'm) contT) bind)"
unfolding return_contT_def bind_contT_def by(rule monad_contT)

lemma monad_fail_contT' [locale_witness]: "monad_fail return (bind :: ('a, ('a, 'm) contT) bind) fail"
unfolding return_contT_def bind_contT_def fail_contT_def by(rule monad_fail_contT)

lemma monad_state_contT' [locale_witness]:
  "monad_state return (bind :: ('a, 'm) bind) (get :: ('s, 'm) get) put
  \<Longrightarrow> monad_state return (bind :: ('a, ('a, 'm) contT) bind) (get :: ('s, ('a, 'm) contT) get) put"
unfolding return_contT_def bind_contT_def get_contT_def put_contT_def by(rule monad_state_contT)

end
