section \<open>Fresh monad operations as class operations\<close>

theory Fresh_Class
imports
  Fresh_Monad
  Name
begin

text \<open>
  The @{const fresh} locale allows arbitrary instantiations. However, this may be inconvenient to
  use. The following class serves as a global instantiation that can be used without interpretation.
  The \<open>arb\<close> parameter of the locale redirects to @{const default}.

  Some instantiations are provided. For @{typ name}s, underscores are appended to generate a fresh
  name.
\<close>

class fresh = linorder + default +
  fixes "next" :: "'a \<Rightarrow> 'a"
  assumes next_ge: "next x > x"

global_interpretation Fresh_Monad.fresh "next" default
  defines fresh_create = create
      and fresh_Next = Next
      and fresh_fNext = fNext
      and fresh_frun = frun_fresh
      and fresh_run = run_fresh
proof
  show "x < next x" for x by (rule next_ge)
qed

lemma [code]: "fresh_frun m S = fst (run_state m (fresh_fNext S))"
by (simp add: fresh_fNext_def fresh_frun_def)

lemma [code]: "fresh_run m S = fst (run_state m (fresh_Next S))"
by (simp add: fresh_Next_def fresh_run_def)

instantiation nat :: fresh begin

definition default_nat :: nat where
"default_nat = 0"

definition next_nat where
"next_nat = Suc"

instance
by intro_classes (auto simp: next_nat_def)

end

instantiation char :: default
begin

definition default_char :: char where
"default_char = CHR ''_''"

instance ..

end

instantiation name :: fresh begin

definition default_name where
"default_name = Name ''_''"

definition next_name where
"next_name xs = Name.append xs default"

instance proof
  fix v :: name
  show "v < next v"
    unfolding next_name_def default_name_def
    by (rule name_append_less) simp
qed

end

export_code
  fresh_create fresh_Next fresh_fNext fresh_frun fresh_run
  checking Scala? SML?

end