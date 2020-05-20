section \<open>Resumption monad transformer\<close>

theory Resumption_Transformer
imports Monad_Plus
begin

subsection \<open>Type definition\<close>

text \<open>The standard Haskell libraries do not include a resumption
monad transformer type; below is the Haskell definition for the one we
will use here.\<close>

text_raw \<open>
\begin{verbatim}
data ResT m a = Done a | More (m (ResT m a))
\end{verbatim}
\<close>

text \<open>The above datatype definition can be translated directly into
HOLCF using \<open>tycondef\<close>. \medskip\<close>

tycondef 'a\<cdot>('f::"functor") resT =
  Done (lazy "'a") | More (lazy "('a\<cdot>'f resT)\<cdot>'f")

lemma coerce_resT_abs [simp]: "coerce\<cdot>(resT_abs\<cdot>x) = resT_abs\<cdot>(coerce\<cdot>x)"
apply (simp add: resT_abs_def coerce_def)
apply (simp add: emb_prj_emb prj_emb_prj DEFL_eq_resT)
done

lemma coerce_Done [simp]: "coerce\<cdot>(Done\<cdot>x) = Done\<cdot>(coerce\<cdot>x)"
unfolding Done_def by simp

lemma coerce_More [simp]: "coerce\<cdot>(More\<cdot>m) = More\<cdot>(coerce\<cdot>m)"
unfolding More_def by simp

lemma resT_induct [case_names adm bottom Done More]:
  fixes P :: "'a\<cdot>'f::functor resT \<Rightarrow> bool"
  assumes adm: "adm P"
  assumes bottom: "P \<bottom>"
  assumes Done: "\<And>x. P (Done\<cdot>x)"
  assumes More: "\<And>m f. (\<And>(r::'a\<cdot>'f resT). P (f\<cdot>r)) \<Longrightarrow> P (More\<cdot>(fmap\<cdot>f\<cdot>m))"
  shows "P r"
proof (induct r rule: resT.take_induct [OF adm])
  fix n show "P (resT_take n\<cdot>r)"
    apply (induct n arbitrary: r)
    apply (simp add: bottom)
    apply (case_tac r rule: resT.exhaust)
    apply (simp add: bottom)
    apply (simp add: Done)
    apply (simp add: More)
    done
qed

subsection \<open>Class instance proofs\<close>

lemma fmapU_resT_simps [simp]:
  "fmapU\<cdot>f\<cdot>(\<bottom>::udom\<cdot>'f::functor resT) = \<bottom>"
  "fmapU\<cdot>f\<cdot>(Done\<cdot>x) = Done\<cdot>(f\<cdot>x)"
  "fmapU\<cdot>f\<cdot>(More\<cdot>m) = More\<cdot>(fmap\<cdot>(fmapU\<cdot>f)\<cdot>m)"
unfolding fmapU_resT_def resT_map_def
apply (subst fix_eq, simp)
apply (subst fix_eq, simp add: Done_def)
apply (subst fix_eq, simp add: More_def)
done

instance resT :: ("functor") "functor"
proof
  fix f g :: "udom \<rightarrow> udom" and xs :: "udom\<cdot>'a resT"
  show "fmapU\<cdot>f\<cdot>(fmapU\<cdot>g\<cdot>xs) = fmapU\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
    by (induct xs rule: resT_induct, simp_all add: fmap_fmap)
qed

instantiation resT :: ("functor") monad
begin

fixrec bindU_resT :: "udom\<cdot>'a resT \<rightarrow> (udom \<rightarrow> udom\<cdot>'a resT) \<rightarrow> udom\<cdot>'a resT"
  where "bindU_resT\<cdot>(Done\<cdot>x)\<cdot>f = f\<cdot>x"
  | "bindU_resT\<cdot>(More\<cdot>m)\<cdot>f = More\<cdot>(fmap\<cdot>(\<Lambda> r. bindU_resT\<cdot>r\<cdot>f)\<cdot>m)"

lemma bindU_resT_strict [simp]: "bindU\<cdot>\<bottom>\<cdot>k = (\<bottom>::udom\<cdot>'a resT)"
by fixrec_simp

definition
  "returnU = Done"

instance proof
  fix f :: "udom \<rightarrow> udom" and xs :: "udom\<cdot>'a resT"
  show "fmapU\<cdot>f\<cdot>xs = bindU\<cdot>xs\<cdot>(\<Lambda> x. returnU\<cdot>(f\<cdot>x))"
    by (induct xs rule: resT_induct)
       (simp_all add: fmap_fmap returnU_resT_def)
next
  fix f :: "udom \<rightarrow> udom\<cdot>'a resT" and x :: "udom"
  show "bindU\<cdot>(returnU\<cdot>x)\<cdot>f = f\<cdot>x"
    by (simp add: returnU_resT_def)
next
  fix xs :: "udom\<cdot>'a resT" and h k :: "udom \<rightarrow> udom\<cdot>'a resT"
  show "bindU\<cdot>(bindU\<cdot>xs\<cdot>h)\<cdot>k = bindU\<cdot>xs\<cdot>(\<Lambda> x. bindU\<cdot>(h\<cdot>x)\<cdot>k)"
    by (induct xs rule: resT_induct)
       (simp_all add: fmap_fmap)
qed

end

subsection \<open>Transfer properties to polymorphic versions\<close>

lemma fmap_resT_simps [simp]:
  "fmap\<cdot>f\<cdot>(\<bottom>::'a\<cdot>'f::functor resT) = \<bottom>"
  "fmap\<cdot>f\<cdot>(Done\<cdot>x :: 'a\<cdot>'f::functor resT) = Done\<cdot>(f\<cdot>x)"
  "fmap\<cdot>f\<cdot>(More\<cdot>m :: 'a\<cdot>'f::functor resT) = More\<cdot>(fmap\<cdot>(fmap\<cdot>f)\<cdot>m)"
unfolding fmap_def [where 'f="'f resT"]
by (simp_all add: coerce_simp)

lemma return_resT_def: "return = Done"
unfolding return_def returnU_resT_def
by (simp add: coerce_simp eta_cfun)

lemma bind_resT_simps [simp]:
  "bind\<cdot>(\<bottom> :: 'a\<cdot>'f::functor resT)\<cdot>f = \<bottom>"
  "bind\<cdot>(Done\<cdot>x :: 'a\<cdot>'f::functor resT)\<cdot>f = f\<cdot>x"
  "bind\<cdot>(More\<cdot>m :: 'a\<cdot>'f::functor resT)\<cdot>f = More\<cdot>(fmap\<cdot>(\<Lambda> r. bind\<cdot>r\<cdot>f)\<cdot>m)"
unfolding bind_def
by (simp_all add: coerce_simp)

lemma join_resT_simps [simp]:
  "join\<cdot>\<bottom> = (\<bottom> :: 'a\<cdot>'f::functor resT)"
  "join\<cdot>(Done\<cdot>x) = x"
  "join\<cdot>(More\<cdot>m) = More\<cdot>(fmap\<cdot>join\<cdot>m)"
unfolding join_def by simp_all

subsection \<open>Nondeterministic interleaving\<close>

text \<open>In this section we present a more general formalization of the
nondeterministic interleaving operation presented in Chapter 7 of the
author's PhD thesis \cite{holcf11}. If both arguments are \<open>Done\<close>, then \<open>zipRT\<close> combines the results with the function
\<open>f\<close> and terminates. While either argument is \<open>More\<close>,
\<open>zipRT\<close> nondeterministically chooses one such argument, runs
it for one step, and then calls itself recursively.\<close>

fixrec zipRT ::
  "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> 'a\<cdot>('m::functor_plus) resT \<rightarrow> 'b\<cdot>'m resT \<rightarrow> 'c\<cdot>'m resT"
  where zipRT_Done_Done:
    "zipRT\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>(Done\<cdot>y) = Done\<cdot>(f\<cdot>x\<cdot>y)"
  | zipRT_Done_More:
    "zipRT\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>(More\<cdot>b) =
      More\<cdot>(fmap\<cdot>(\<Lambda> r. zipRT\<cdot>f\<cdot>(Done\<cdot>x)\<cdot>r)\<cdot>b)"
  | zipRT_More_Done:
    "zipRT\<cdot>f\<cdot>(More\<cdot>a)\<cdot>(Done\<cdot>y) =
      More\<cdot>(fmap\<cdot>(\<Lambda> r. zipRT\<cdot>f\<cdot>r\<cdot>(Done\<cdot>y))\<cdot>a)"
  | zipRT_More_More:
    "zipRT\<cdot>f\<cdot>(More\<cdot>a)\<cdot>(More\<cdot>b) =
      More\<cdot>(fplus\<cdot>(fmap\<cdot>(\<Lambda> r. zipRT\<cdot>f\<cdot>(More\<cdot>a)\<cdot>r)\<cdot>b)
                 \<cdot>(fmap\<cdot>(\<Lambda> r. zipRT\<cdot>f\<cdot>r\<cdot>(More\<cdot>b))\<cdot>a))"

lemma zipRT_strict1 [simp]: "zipRT\<cdot>f\<cdot>\<bottom>\<cdot>r = \<bottom>"
by fixrec_simp

lemma zipRT_strict2 [simp]: "zipRT\<cdot>f\<cdot>r\<cdot>\<bottom> = \<bottom>"
by (fixrec_simp, cases r, simp_all)

abbreviation apR (infixl "\<diamondop>" 70)
  where "a \<diamondop> b \<equiv> zipRT\<cdot>ID\<cdot>a\<cdot>b"

text \<open>Proofs that \<open>zipRT\<close> satisfies the applicative functor laws:\<close>

lemma zipRT_homomorphism: "Done\<cdot>f \<diamondop> Done\<cdot>x = Done\<cdot>(f\<cdot>x)"
  by simp

lemma zipRT_identity: "Done\<cdot>ID \<diamondop> r = r"
  by (induct r rule: resT_induct, simp_all add: fmap_fmap eta_cfun)

lemma zipRT_interchange: "r \<diamondop> Done\<cdot>x = Done\<cdot>(\<Lambda> f. f\<cdot>x) \<diamondop> r"
  by (induct r rule: resT_induct, simp_all add: fmap_fmap)

text \<open>The associativity rule is the hard one!\<close>

lemma zipRT_associativity: "Done\<cdot>cfcomp \<diamondop> r1 \<diamondop> r2 \<diamondop> r3 = r1 \<diamondop> (r2 \<diamondop> r3)"
proof (induct r1 arbitrary: r2 r3 rule: resT_induct)
  case (Done x1) thus ?case
  proof (induct r2 arbitrary: r3 rule: resT_induct)
    case (Done x2) thus ?case
    proof (induct r3 rule: resT_induct)
      case (More p3 c3) thus ?case (* Done/Done/More *)
        by (simp add: fmap_fmap)
    qed simp_all
  next
    case (More p2 c2) thus ?case
    proof (induct r3 rule: resT_induct)
      case (Done x3) thus ?case (* Done/More/Done *)
        by (simp add: fmap_fmap)
    next
      case (More p3 c3) thus ?case (* Done/More/More *)
        by (simp add: fmap_fmap fmap_fplus)
    qed simp_all
  qed simp_all
next
  case (More p1 c1) thus ?case
  proof (induct r2 arbitrary: r3 rule: resT_induct)
    case (Done y) thus ?case
    proof (induct r3 rule: resT_induct)
      case (Done x3) thus ?case
        by (simp add: fmap_fmap)
    next
      case (More p3 c3) thus ?case
        by (simp add: fmap_fmap)
    qed simp_all
  next
    case (More p2 c2) thus ?case
    proof (induct r3 rule: resT_induct)
      case (Done x3) thus ?case
        by (simp add: fmap_fmap fmap_fplus)
    next
      case (More p3 c3) thus ?case
        by (simp add: fmap_fmap fmap_fplus fplus_assoc)
    qed simp_all
  qed simp_all
qed simp_all

end
