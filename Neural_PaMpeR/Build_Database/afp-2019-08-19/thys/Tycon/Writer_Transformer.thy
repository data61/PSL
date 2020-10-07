section \<open>Writer monad transformer\<close>

theory Writer_Transformer
imports Writer_Monad
begin

subsection \<open>Type definition\<close>

text \<open>Below is the standard Haskell definition of a writer monad
transformer:\<close>

text_raw \<open>
\begin{verbatim}
newtype WriterT w m a = WriterT { runWriterT :: m (a, w) }
\end{verbatim}
\<close>

text \<open>In this development, since a lazy pair type is not pre-defined
in HOLCF, we will use an equivalent formulation in terms of our
previous \texttt{Writer} type:\<close>

text_raw \<open>
\begin{verbatim}
data Writer w a = Writer w a
newtype WriterT w m a = WriterT { runWriterT :: m (Writer w a) }
\end{verbatim}
\<close>

text \<open>We can translate this definition directly into HOLCF using
\<open>tycondef\<close>. \medskip\<close>

tycondef 'a\<cdot>('m::"functor",'w) writerT =
  WriterT (runWriterT :: "('a\<cdot>'w writer)\<cdot>'m")

lemma coerce_writerT_abs [simp]:
  "coerce\<cdot>(writerT_abs\<cdot>x) = writerT_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: writerT_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_writerT)
done

lemma coerce_WriterT [simp]: "coerce\<cdot>(WriterT\<cdot>k) = WriterT\<cdot>(coerce\<cdot>k)"
unfolding WriterT_def by simp

lemma writerT_cases [case_names WriterT]:
  obtains k where "y = WriterT\<cdot>k"
proof
  show "y = WriterT\<cdot>(runWriterT\<cdot>y)"
    by (cases y, simp_all)
qed

lemma WriterT_runWriterT [simp]: "WriterT\<cdot>(runWriterT\<cdot>m) = m"
by (cases m rule: writerT_cases, simp)

lemma writerT_induct [case_names WriterT]:
  fixes P :: "'a\<cdot>('f::functor,'e) writerT \<Rightarrow> bool"
  assumes "\<And>k. P (WriterT\<cdot>k)"
  shows "P y"
by (cases y rule: writerT_cases, simp add: assms)

lemma writerT_eq_iff:
  "a = b \<longleftrightarrow> runWriterT\<cdot>a = runWriterT\<cdot>b"
apply (cases a rule: writerT_cases)
apply (cases b rule: writerT_cases)
apply simp
done

lemma writerT_below_iff:
  "a \<sqsubseteq> b \<longleftrightarrow> runWriterT\<cdot>a \<sqsubseteq> runWriterT\<cdot>b"
apply (cases a rule: writerT_cases)
apply (cases b rule: writerT_cases)
apply simp
done

lemma writerT_eqI:
  "runWriterT\<cdot>a = runWriterT\<cdot>b \<Longrightarrow> a = b"
by (simp add: writerT_eq_iff)

lemma writerT_belowI:
  "runWriterT\<cdot>a \<sqsubseteq> runWriterT\<cdot>b \<Longrightarrow> a \<sqsubseteq> b"
by (simp add: writerT_below_iff)

lemma runWriterT_coerce [simp]:
  "runWriterT\<cdot>(coerce\<cdot>k) = coerce\<cdot>(runWriterT\<cdot>k)"
by (induct k rule: writerT_induct, simp)

subsection \<open>Functor class instance\<close>

lemma fmap_writer_def: "fmap = writer_map\<cdot>ID"
apply (rule cfun_eqI, rename_tac f)
apply (rule cfun_eqI, rename_tac x)
apply (case_tac x rule: writer.exhaust, simp_all)
apply (simp add: writer_map_def fix_const)
apply (simp add: writer_map_def fix_const Writer_def)
done

lemma fmapU_WriterT [simp]:
  "fmapU\<cdot>f\<cdot>(WriterT\<cdot>m) = WriterT\<cdot>(fmap\<cdot>(fmap\<cdot>f)\<cdot>m)"
unfolding fmapU_writerT_def writerT_map_def fmap_writer_def fix_const
  WriterT_def by simp

lemma runWriterT_fmapU [simp]:
  "runWriterT\<cdot>(fmapU\<cdot>f\<cdot>m) = fmap\<cdot>(fmap\<cdot>f)\<cdot>(runWriterT\<cdot>m)"
by (induct m rule: writerT_induct) simp

instance writerT :: ("functor", "domain") "functor"
proof
  fix f g :: "udom \<rightarrow> udom" and xs :: "udom\<cdot>('a,'b) writerT"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    apply (induct xs rule: writerT_induct)
    apply (simp add: fmap_fmap eta_cfun)
    done
qed

subsection \<open>Monad operations\<close>

text \<open>The writer monad transformer does not yield a monad in the
usual sense: We cannot prove a \<open>monad\<close> class instance, because
type \<open>'a\<cdot>('m,'w) writerT\<close> contains values that break the monad
laws. However, it turns out that such values are inaccessible: The
monad laws are satisfied by all values constructible from the abstract
operations.\<close>

text \<open>To explore the properties of the writer monad transformer
operations, we define them all as non-overloaded functions. \medskip
\<close>

definition unitWT :: "'a \<rightarrow> 'a\<cdot>('m::monad,'w::monoid) writerT"
  where "unitWT = (\<Lambda> x. WriterT\<cdot>(return\<cdot>(Writer\<cdot>mempty\<cdot>x)))"

definition bindWT :: "'a\<cdot>('m::monad,'w::monoid) writerT \<rightarrow> ('a \<rightarrow> 'b\<cdot>('m,'w) writerT) \<rightarrow> 'b\<cdot>('m,'w) writerT"
  where "bindWT = (\<Lambda> m k. WriterT\<cdot>(bind\<cdot>(runWriterT\<cdot>m)\<cdot>
    (\<Lambda>(Writer\<cdot>w\<cdot>x). bind\<cdot>(runWriterT\<cdot>(k\<cdot>x))\<cdot>(\<Lambda>(Writer\<cdot>w'\<cdot>y).
      return\<cdot>(Writer\<cdot>(mappend\<cdot>w\<cdot>w')\<cdot>y)))))"

definition liftWT :: "'a\<cdot>'m \<rightarrow> 'a\<cdot>('m::monad,'w::monoid) writerT"
  where "liftWT = (\<Lambda> m. WriterT\<cdot>(fmap\<cdot>(Writer\<cdot>mempty)\<cdot>m))"

definition tellWT :: "'a \<rightarrow> 'w \<rightarrow> 'a\<cdot>('m::monad,'w::monoid) writerT"
  where "tellWT = (\<Lambda> x w. WriterT\<cdot>(return\<cdot>(Writer\<cdot>w\<cdot>x)))"

definition fmapWT :: "('a \<rightarrow> 'b) \<rightarrow> 'a\<cdot>('m::monad,'w::monoid) writerT \<rightarrow> 'b\<cdot>('m,'w) writerT"
  where "fmapWT = (\<Lambda> f m. bindWT\<cdot>m\<cdot>(\<Lambda> x. unitWT\<cdot>(f\<cdot>x)))"

lemma runWriterT_fmap [simp]:
  "runWriterT\<cdot>(fmap\<cdot>f\<cdot>m) = fmap\<cdot>(fmap\<cdot>f)\<cdot>(runWriterT\<cdot>m)"
by (subst fmap_def, simp add: coerce_simp eta_cfun)

lemma runWriterT_unitWT [simp]:
  "runWriterT\<cdot>(unitWT\<cdot>x) = return\<cdot>(Writer\<cdot>mempty\<cdot>x)"
unfolding unitWT_def by simp

lemma runWriterT_bindWT [simp]:
  "runWriterT\<cdot>(bindWT\<cdot>m\<cdot>k) = bind\<cdot>(runWriterT\<cdot>m)\<cdot>
    (\<Lambda>(Writer\<cdot>w\<cdot>x). bind\<cdot>(runWriterT\<cdot>(k\<cdot>x))\<cdot>(\<Lambda>(Writer\<cdot>w'\<cdot>y).
      return\<cdot>(Writer\<cdot>(mappend\<cdot>w\<cdot>w')\<cdot>y)))"
unfolding bindWT_def by simp

lemma runWriterT_liftWT [simp]:
  "runWriterT\<cdot>(liftWT\<cdot>m) = fmap\<cdot>(Writer\<cdot>mempty)\<cdot>m"
unfolding liftWT_def by simp

lemma runWriterT_tellWT [simp]:
  "runWriterT\<cdot>(tellWT\<cdot>x\<cdot>w) = return\<cdot>(Writer\<cdot>w\<cdot>x)"
unfolding tellWT_def by simp

lemma runWriterT_fmapWT [simp]:
  "runWriterT\<cdot>(fmapWT\<cdot>f\<cdot>m) =
    runWriterT\<cdot>m \<bind> (\<Lambda> (Writer\<cdot>w\<cdot>x). return\<cdot>(Writer\<cdot>w\<cdot>(f\<cdot>x)))"
by (simp add: fmapWT_def bindWT_def mempty_right)

subsection \<open>Laws\<close>

text \<open>The \<open>liftWT\<close> function maps \<open>return\<close> and
\<open>bind\<close> on the inner monad to \<open>unitWT\<close> and \<open>bindWT\<close>, as expected. \medskip\<close>

lemma liftWT_return:
  "liftWT\<cdot>(return\<cdot>x) = unitWT\<cdot>x"
by (rule writerT_eqI, simp add: fmap_return)

lemma liftWT_bind:
  "liftWT\<cdot>(bind\<cdot>m\<cdot>k) = bindWT\<cdot>(liftWT\<cdot>m)\<cdot>(liftWT oo k)"
by (rule writerT_eqI)
   (simp add: monad_fmap bind_bind mempty_left)

text \<open>The composition rule holds unconditionally for fmap. The fmap
function also interacts as expected with unit and bind. \medskip\<close>

lemma fmapWT_fmapWT:
  "fmapWT\<cdot>f\<cdot>(fmapWT\<cdot>g\<cdot>m) = fmapWT\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>m"
apply (simp add: writerT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x, simp add: bind_strict, simp add: mempty_right)
done

lemma fmapWT_unitWT:
  "fmapWT\<cdot>f\<cdot>(unitWT\<cdot>x) = unitWT\<cdot>(f\<cdot>x)"
by (simp add: writerT_eq_iff mempty_right)

lemma fmapWT_bindWT:
  "fmapWT\<cdot>f\<cdot>(bindWT\<cdot>m\<cdot>k) = bindWT\<cdot>m\<cdot>(\<Lambda> x. fmapWT\<cdot>f\<cdot>(k\<cdot>x))"
apply (simp add: writerT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, rename_tac x, simp)
apply (case_tac x, simp add: bind_strict, simp add: bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, rename_tac y, simp)
apply (case_tac y, simp add: bind_strict, simp add: mempty_right)
done

lemma bindWT_fmapWT:
  "bindWT\<cdot>(fmapWT\<cdot>f\<cdot>m)\<cdot>k = bindWT\<cdot>m\<cdot>(\<Lambda> x. k\<cdot>(f\<cdot>x))"
apply (simp add: writerT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, rename_tac x, simp)
apply (case_tac x, simp add: bind_strict, simp add: mempty_right)
done

text \<open>The left unit monad law is not satisfied in general. \medskip\<close>

lemma bindWT_unitWT_counterexample:
  fixes k :: "'a \<rightarrow> 'b\<cdot>('m::monad,'w::monoid) writerT"
  assumes 1: "k\<cdot>x = WriterT\<cdot>(return\<cdot>\<bottom>)"
  assumes 2: "return\<cdot>\<bottom> \<noteq> (\<bottom> :: ('b\<cdot>'w writer)\<cdot>'m::monad)"
  shows "bindWT\<cdot>(unitWT\<cdot>x)\<cdot>k \<noteq> k\<cdot>x"
by (simp add: writerT_eq_iff mempty_left assms)

text \<open>However, left unit is satisfied for inner monads with a strict
\<open>return\<close> function.\<close>

lemma bindWT_unitWT_restricted:
  fixes k :: "'a \<rightarrow> 'b\<cdot>('m::monad,'w::monoid) writerT"
  assumes "return\<cdot>\<bottom> = (\<bottom> :: ('b\<cdot>'w writer)\<cdot>'m)"
  shows "bindWT\<cdot>(unitWT\<cdot>x)\<cdot>k = k\<cdot>x"
unfolding writerT_eq_iff
apply (simp add: mempty_left)
apply (rule trans [OF _ monad_right_unit])
apply (rule cfun_arg_cong)
apply (rule cfun_eqI)
apply (case_tac x, simp_all add: assms)
done

text \<open>The associativity of \<open>bindWT\<close> holds
unconditionally. \medskip\<close>

lemma bindWT_bindWT:
  "bindWT\<cdot>(bindWT\<cdot>m\<cdot>h)\<cdot>k = bindWT\<cdot>m\<cdot>(\<Lambda> x. bindWT\<cdot>(h\<cdot>x)\<cdot>k)"
apply (rule writerT_eqI)
apply simp
apply (simp add: bind_bind)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, simp)
apply (case_tac x)
apply (simp add: bind_strict)
apply (simp add: bind_bind)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, simp, rename_tac y)
apply (case_tac y)
apply (simp add: bind_strict)
apply (simp add: bind_bind)
apply (rule cfun_arg_cong)
apply (rule cfun_eqI, simp, rename_tac z)
apply (case_tac z)
apply (simp add: bind_strict)
apply (simp add: mappend_assoc)
done

text \<open>The right unit monad law is not satisfied in general. \medskip\<close>

lemma bindWT_unitWT_right_counterexample:
  fixes m :: "'a\<cdot>('m::monad,'w::monoid) writerT"
  assumes "m = WriterT\<cdot>(return\<cdot>\<bottom>)"
  assumes "return\<cdot>\<bottom> \<noteq> (\<bottom> :: ('a\<cdot>'w writer)\<cdot>'m)"
  shows "bindWT\<cdot>m\<cdot>unitWT \<noteq> m"
by (simp add: writerT_eq_iff assms)

text \<open>Right unit is satisfied for inner monads with a strict \<open>return\<close> function. \medskip\<close>

lemma bindWT_unitWT_right_restricted:
  fixes m :: "'a\<cdot>('m::monad,'w::monoid) writerT"
  assumes "return\<cdot>\<bottom> = (\<bottom> :: ('a\<cdot>'w writer)\<cdot>'m)"
  shows "bindWT\<cdot>m\<cdot>unitWT = m"
unfolding writerT_eq_iff
apply simp
apply (rule trans [OF _ monad_right_unit])
apply (rule cfun_arg_cong)
apply (rule cfun_eqI)
apply (case_tac x, simp_all add: assms mempty_right)
done

subsection \<open>Writer monad transformer invariant\<close>

text \<open>We inductively define a predicate that includes all values
that can be constructed from the standard \<open>writerT\<close> operations.
\medskip\<close>

inductive invar :: "'a\<cdot>('m::monad, 'w::monoid) writerT \<Rightarrow> bool"
  where invar_bottom: "invar \<bottom>"
  | invar_lub: "\<And>Y. \<lbrakk>chain Y; \<And>i. invar (Y i)\<rbrakk> \<Longrightarrow> invar (\<Squnion>i. Y i)"
  | invar_unitWT: "\<And>x. invar (unitWT\<cdot>x)"
  | invar_bindWT: "\<And>m k. \<lbrakk>invar m; \<And>x. invar (k\<cdot>x)\<rbrakk> \<Longrightarrow> invar (bindWT\<cdot>m\<cdot>k)"
  | invar_tellWT: "\<And>x w. invar (tellWT\<cdot>x\<cdot>w)"
  | invar_liftWT: "\<And>m. invar (liftWT\<cdot>m)"

text \<open>Right unit is satisfied for arguments built from standard
functions. \medskip\<close>

lemma bindWT_unitWT_right_invar:
  fixes m :: "'a\<cdot>('m::monad,'w::monoid) writerT"
  assumes "invar m"
  shows "bindWT\<cdot>m\<cdot>unitWT = m"
using assms proof (induct set: invar)
  case invar_bottom thus ?case
    by (rule writerT_eqI, simp add: bind_strict)
next
  case invar_lub thus ?case
    by - (rule admD, simp, assumption, assumption)
next
  case invar_unitWT thus ?case
    by (rule writerT_eqI, simp add: bind_bind mempty_left)
next
  case invar_bindWT thus ?case
    apply (simp add: writerT_eq_iff bind_bind)
    apply (rule cfun_arg_cong, rule cfun_eqI, simp)
    apply (case_tac x, simp add: bind_strict, simp add: bind_bind)
    apply (rule cfun_arg_cong, rule cfun_eqI, simp, rename_tac y)
    apply (case_tac y, simp add: bind_strict, simp add: mempty_right)
    done
next
  case invar_tellWT thus ?case
    by (simp add: writerT_eq_iff mempty_right)
next
  case invar_liftWT thus ?case
    by (rule writerT_eqI, simp add: monad_fmap bind_bind mempty_right)
qed

text \<open>Left unit is also satisfied for arguments built from standard
functions. \medskip\<close>

lemma writerT_left_unit_invar_lemma:
  assumes "invar m"
  shows "runWriterT\<cdot>m \<bind> (\<Lambda> (Writer\<cdot>w\<cdot>x). return\<cdot>(Writer\<cdot>w\<cdot>x)) = runWriterT\<cdot>m"
using assms proof (induct m set: invar)
  case invar_bottom thus ?case
    by (simp add: bind_strict)
next
  case invar_lub thus ?case
    by - (rule admD, simp, assumption, assumption)
next
  case invar_unitWT thus ?case
    by simp
next
  case invar_bindWT thus ?case
    apply (simp add: bind_bind)
    apply (rule cfun_arg_cong)
    apply (rule cfun_eqI, simp, rename_tac n)
    apply (case_tac n, simp add: bind_strict)
    apply (simp add: bind_bind)
    apply (rule cfun_arg_cong)
    apply (rule cfun_eqI, simp, rename_tac p)
    apply (case_tac p, simp add: bind_strict)
    apply simp
    done
next
  case invar_tellWT thus ?case
    by simp
next
  case invar_liftWT thus ?case
    by (simp add: monad_fmap bind_bind)
qed

lemma bindWT_unitWT_invar:
  assumes "invar (k\<cdot>x)"
  shows "bindWT\<cdot>(unitWT\<cdot>x)\<cdot>k = k\<cdot>x"
apply (simp add: writerT_eq_iff mempty_left)
apply (rule writerT_left_unit_invar_lemma [OF assms])
done

subsection \<open>Invariant expressed as a deflation\<close>

definition invar' :: "'a\<cdot>('m::monad, 'w::monoid) writerT \<Rightarrow> bool"
  where "invar' m \<longleftrightarrow> fmapWT\<cdot>ID\<cdot>m = m"

text \<open>All standard operations preserve the invariant.\<close>

lemma invar'_bottom: "invar' \<bottom>"
  unfolding invar'_def by (simp add: writerT_eq_iff bind_strict)

lemma adm_invar': "adm invar'"
  unfolding invar'_def [abs_def] by simp

lemma invar'_unitWT: "invar' (unitWT\<cdot>x)"
  unfolding invar'_def by (simp add: writerT_eq_iff)

lemma invar'_bindWT: "\<lbrakk>invar' m; \<And>x. invar' (k\<cdot>x)\<rbrakk> \<Longrightarrow> invar' (bindWT\<cdot>m\<cdot>k)"
  unfolding invar'_def
  apply (erule subst)
  apply (simp add: writerT_eq_iff)
  apply (simp add: bind_bind)
  apply (rule cfun_arg_cong)
  apply (rule cfun_eqI, case_tac x)
  apply (simp add: bind_strict)
  apply simp
  apply (simp add: bind_bind)
  apply (rule cfun_arg_cong)
  apply (rule cfun_eqI, rename_tac x, case_tac x)
  apply (simp add: bind_strict)
  apply simp
  done

lemma invar'_tellWT: "invar' (tellWT\<cdot>x\<cdot>w)"
  unfolding invar'_def by (simp add: writerT_eq_iff)

lemma invar'_liftWT: "invar' (liftWT\<cdot>m)"
  unfolding invar'_def by (simp add: writerT_eq_iff monad_fmap bind_bind)

text \<open>Left unit is satisfied for arguments built from fmap.\<close>

lemma bindWT_unitWT_fmapWT:
  "bindWT\<cdot>(unitWT\<cdot>x)\<cdot>(\<Lambda> x. fmapWT\<cdot>f\<cdot>(k\<cdot>x))
    = fmapWT\<cdot>f\<cdot>(k\<cdot>x)"
apply (simp add: fmapWT_def writerT_eq_iff bind_bind)
apply (rule cfun_arg_cong, rule cfun_eqI, simp)
apply (case_tac x, simp_all add: bind_strict mempty_left)
done

text \<open>Right unit is satisfied for arguments built from fmap.\<close>

lemma bindWT_fmapWT_unitWT:
  shows "bindWT\<cdot>(fmapWT\<cdot>f\<cdot>m)\<cdot>unitWT = fmapWT\<cdot>f\<cdot>m"
apply (simp add: bindWT_fmapWT)
apply (simp add: fmapWT_def)
done

text \<open>All monad laws are preserved by values satisfying the invariant.\<close>

lemma invar'_right_unit: "invar' m \<Longrightarrow> bindWT\<cdot>m\<cdot>unitWT = m"
unfolding invar'_def by (erule subst, rule bindWT_fmapWT_unitWT)

lemma invar'_monad_fmap:
  "invar' m \<Longrightarrow> fmapWT\<cdot>f\<cdot>m = bindWT\<cdot>m\<cdot>(\<Lambda> x. unitWT\<cdot>(f\<cdot>x))"
  unfolding invar'_def
  by (erule subst, simp add: writerT_eq_iff mempty_right)

lemma invar'_bind_assoc:
  "\<lbrakk>invar' m; \<And>x. invar' (f\<cdot>x); \<And>y. invar' (g\<cdot>y)\<rbrakk>
    \<Longrightarrow> bindWT\<cdot>(bindWT\<cdot>m\<cdot>f)\<cdot>g = bindWT\<cdot>m\<cdot>(\<Lambda> x. bindWT\<cdot>(f\<cdot>x)\<cdot>g)"
  by (rule bindWT_bindWT)

end
