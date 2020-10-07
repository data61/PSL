section \<open>Writer monad\<close>

theory Writer_Monad
imports Monad
begin

subsection \<open>Monoid class\<close>

class monoid = "domain" +
  fixes mempty :: "'a"
  fixes mappend :: "'a \<rightarrow> 'a \<rightarrow> 'a"
  assumes mempty_left: "\<And>ys. mappend\<cdot>mempty\<cdot>ys = ys"
  assumes mempty_right: "\<And>xs. mappend\<cdot>xs\<cdot>mempty = xs"
  assumes mappend_assoc:
    "\<And>xs ys zs. mappend\<cdot>(mappend\<cdot>xs\<cdot>ys)\<cdot>zs = mappend\<cdot>xs\<cdot>(mappend\<cdot>ys\<cdot>zs)"

subsection \<open>Writer monad type\<close>

text \<open>Below is the standard Haskell definition of a writer monad
type; it is an isomorphic copy of the lazy pair type \texttt{(a, w)}.
\<close>

text_raw \<open>
\begin{verbatim}
newtype Writer w a = Writer { runWriter :: (a, w) }
\end{verbatim}
\<close>

text \<open>Since HOLCF does not have a pre-defined lazy pair type, we
will base this formalization on an equivalent, more direct definition:
\<close>

text_raw \<open>
\begin{verbatim}
data Writer w a = Writer w a
\end{verbatim}
\<close>

text \<open>We can directly translate the above Haskell type definition
using \<open>tycondef\<close>. \medskip\<close>

tycondef 'a\<cdot>'w writer = Writer (lazy "'w") (lazy "'a")

lemma coerce_writer_abs [simp]: "coerce\<cdot>(writer_abs\<cdot>x) = writer_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: writer_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_writer)
done

lemma coerce_Writer [simp]:
  "coerce\<cdot>(Writer\<cdot>w\<cdot>x) = Writer\<cdot>(coerce\<cdot>w)\<cdot>(coerce\<cdot>x)"
unfolding Writer_def by simp

lemma fmapU_writer_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>'w writer) = \<bottom>"
  "fmapU\<cdot>f\<cdot>(Writer\<cdot>w\<cdot>x) = Writer\<cdot>w\<cdot>(f\<cdot>x)"
unfolding fmapU_writer_def writer_map_def fix_const
apply simp
apply (simp add: Writer_def)
done

subsection \<open>Class instance proofs\<close>

instance writer :: ("domain") "functor"
proof
  fix f g :: "udom \<rightarrow> udom" and xs :: "udom\<cdot>'a writer"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    by (induct xs rule: writer.induct) simp_all
qed

instantiation writer :: (monoid) monad
begin

fixrec bindU_writer ::
    "udom\<cdot>'a writer \<rightarrow> (udom \<rightarrow> udom\<cdot>'a writer) \<rightarrow> udom\<cdot>'a writer"
  where "bindU_writer\<cdot>(Writer\<cdot>w\<cdot>x)\<cdot>f =
    (case f\<cdot>x of Writer\<cdot>w'\<cdot>y \<Rightarrow> Writer\<cdot>(mappend\<cdot>w\<cdot>w')\<cdot>y)"

lemma bindU_writer_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>'a writer)"
by fixrec_simp

definition
  "returnU = Writer\<cdot>mempty"

instance proof
  fix f :: "udom \<rightarrow> udom" and m :: "udom\<cdot>'a writer"
  show "fmapU\<cdot>f\<cdot>m = bindU\<cdot>m\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct m rule: writer.induct)
       (simp_all add: returnU_writer_def mempty_right)
next
  fix f :: "udom \<rightarrow> udom\<cdot>'a writer" and x :: "udom"
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>f = f\<cdot>x"
    by (cases "f\<cdot>x" rule: writer.exhaust)
       (simp_all add: returnU_writer_def mempty_left)
next
  fix m :: "udom\<cdot>'a writer" and f g :: "udom \<rightarrow> udom\<cdot>'a writer"
  show "bindU\<cdot>(bindU\<cdot>m\<cdot>f)\<cdot>g = bindU\<cdot>m\<cdot>(\<Lambda> x. bindU\<cdot>(f\<cdot>x)\<cdot>g)"
    apply (induct m rule: writer.induct, simp)
    apply (case_tac "f\<cdot>a" rule: writer.exhaust, simp)
    apply (case_tac "g\<cdot>aa" rule: writer.exhaust, simp)
    apply (simp add: mappend_assoc)
    done
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_writer_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>'w writer) = \<bottom>"
  "fmap\<cdot>f\<cdot>(Writer\<cdot>w\<cdot>x :: 'a\<cdot>'w writer) = Writer\<cdot>w\<cdot>(f\<cdot>x)"
unfolding fmap_def [where 'f="'w writer"]
by (simp_all add: coerce_simp)

lemma return_writer_def: "return = Writer\<cdot>mempty"
unfolding return_def returnU_writer_def
by (simp add: coerce_simp eta_cfun)

lemma bind_writer_simps [simp]:
  "bind\<cdot>(\<bottom> :: 'a\<cdot>'w::monoid writer)\<cdot>f = \<bottom>"
  "bind\<cdot>(Writer\<cdot>w\<cdot>x :: 'a\<cdot>'w::monoid writer)\<cdot>k =
    (case k\<cdot>x of Writer\<cdot>w'\<cdot>y \<Rightarrow> Writer\<cdot>(mappend\<cdot>w\<cdot>w')\<cdot>y)"
unfolding bind_def
apply (simp add: coerce_simp)
apply (cases "k\<cdot>x" rule: writer.exhaust)
apply (simp_all add: coerce_simp)
done

lemma join_writer_simps [simp]:
  "join\<cdot>\<bottom> = (\<bottom> :: 'a\<cdot>'w::monoid writer)"
  "join\<cdot>(Writer\<cdot>w\<cdot>(Writer\<cdot>w'\<cdot>x)) = Writer\<cdot>(mappend\<cdot>w\<cdot>w')\<cdot>x"
unfolding join_def by simp_all

subsection \<open>Extra operations\<close>

definition tell :: "'w \<rightarrow> unit\<cdot>('w::monoid writer)"
  where "tell = (\<Lambda> w. Writer\<cdot>w\<cdot>())"

end
