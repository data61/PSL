(*  Title:      Logical_Relations.thy
    Author:     Peter Gammie
*)

section {* Pitts's method for solving recursive domain predicates *}
(*<*)

theory Logical_Relations
imports
  Basis
begin

(*>*)
text{*

We adopt the general theory of \citet{PittsAM:relpod} for solving
recursive domain predicates. This is based on the idea of
\emph{minimal invariants} that \citet[Def 2]{DBLP:conf/mfps/Pitts93}
ascribes ``essentially to D. Scott''.

Ideally we would like to do the proofs once and use Pitts's
\emph{relational structures}. Unfortunately it seems we need
higher-order polymorphism (type functions) to make this work (but see
\citet{Huffman:MonadTransformers:2012}). Here we develop three
versions, one for each of our applications. The proofs are similar
(but not quite identical) in all cases.

We begin by defining an \emph{admissible} set (aka an \emph{inclusive
predicate}) to be one that contains @{term "\<bottom>"} and is closed under
countable chains:

*}

definition admS :: "'a::pcpo set set" where
  "admS \<equiv> { R :: 'a set. \<bottom> \<in> R \<and> adm (\<lambda>x. x \<in> R) }"

typedef ('a::pcpo) admS = "{ x::'a::pcpo set . x \<in> admS }"
  morphisms unlr mklr unfolding admS_def by fastforce

text{*

These sets form a complete lattice.

*}
(*<*)

lemma admSI [intro]:
  "\<lbrakk> \<bottom> \<in> R; adm (\<lambda>x. x \<in> R) \<rbrakk> \<Longrightarrow> R \<in> admS"
unfolding admS_def by simp

lemma bottom_in_unlr [simp]:
  "\<bottom> \<in> unlr R"
using admS.unlr [of R] by (simp add: admS_def)

lemma adm_unlr [simp]:
  "adm (\<lambda>x. x \<in> unlr R)"
using admS.unlr [of R] by (simp add: admS_def)

lemma adm_cont_unlr [intro, simp]:
  "cont f \<Longrightarrow> adm (\<lambda>x. f x \<in> unlr r)"
by (erule adm_subst) simp

declare admS.mklr_inverse[simp add]

instantiation admS :: (pcpo) order
begin

definition
  "x \<le> y \<equiv> unlr x \<subseteq> unlr y"

definition
  "x < y \<equiv> unlr x \<subset> unlr y"

instance
  by standard (auto simp add: less_eq_admS_def less_admS_def admS.unlr_inject)

end

lemma mklr_leq [iff]: "\<lbrakk> x \<in> admS; y \<in> admS \<rbrakk> \<Longrightarrow> (mklr x \<le> mklr y) \<longleftrightarrow> (x \<le> y)"
  unfolding less_eq_admS_def by simp

lemma unlr_leq: "(unlr x \<le> unlr y) \<longleftrightarrow> (x \<le> y)"
  unfolding less_eq_admS_def by simp

instantiation admS :: (pcpo) lattice
begin

definition
  "inf f g \<equiv> mklr (unlr f \<inter> unlr g)"

definition
  "sup f g = mklr (unlr f \<union> unlr g)"

lemma unlr_inf: "unlr (inf x y) = unlr x \<inter> unlr y"
  unfolding inf_admS_def by (simp add: admS_def)

lemma unlr_sup: "unlr (sup x y) = unlr x \<union> unlr y"
  unfolding sup_admS_def by (simp add: admS_def)

instance
apply intro_classes
apply (auto simp: less_eq_admS_def unlr_inf unlr_sup)
done

end

instantiation admS :: (pcpo) bounded_lattice
begin

definition
  "bot_admS \<equiv> mklr {\<bottom>}"

lemma unlr_bot[simp]:
  "unlr bot = {\<bottom>}"
  by (simp add: admS_def bot_admS_def)

definition
  "top_admS \<equiv> mklr UNIV"

instance
proof
  fix x :: "'a admS"
  show "bot \<le> x" by (simp add: bot_admS_def less_eq_admS_def admS_def)
next
  fix x :: "'a admS"
  show "x \<le> top" by (simp add: top_admS_def less_eq_admS_def admS_def)
qed

end

instantiation admS :: (pcpo) complete_lattice
begin

definition
  "Inf A \<equiv> mklr (Inf (unlr ` A))"

definition
  "Sup (A::'a admS set) = Inf {y. \<forall>x\<in>A. x \<le> y}"

lemma mklr_Inf: "unlr (Inf A) = Inf (unlr ` A)"
  unfolding Inf_admS_def by (simp add: admS_def)

lemma INT_admS_bot [simp]:
  "(\<Inter>R. unlr R) = {\<bottom>}"
by (auto, metis singletonE unlr_bot)

instance
  by standard
    (auto simp add:
      less_eq_admS_def mklr_Inf Sup_admS_def
      Inf_admS_def bot_admS_def top_admS_def admS_def)

end
(*>*)


subsection{* Sets of vectors *}

text{*

The simplest case involves the recursive definition of a set of
vectors over a single domain. This involves taking the fixed point of
a functor where the \emph{positive} (covariant) occurrences of the
recursion variable are separated from the \emph{negative}
(contravariant) ones. (See \S\ref{sec:por} etc. for examples.)

By dually ordering the negative uses of the recursion variable the
functor is made monotonic with respect to the order on the domain
@{typ "'d"}. Here the type constructor @{typ "'a dual"} yields a type
with the same elements as @{typ "'a"} but with the reverse order. The
functions @{term "dual"} and @{term "undual"} mediate the isomorphism.

*}

type_synonym 'd lf_rep = "'d admS dual \<times> 'd admS \<Rightarrow> 'd set"
type_synonym 'd lf = "'d admS dual \<times> 'd admS \<Rightarrow> 'd admS"

text{*

The predicate @{term "eRSV"} encodes our notion of relation.  (This is
Pitts's @{text "e : R \<subset> S"}.) We model a vector as a function from
some index type @{typ "'i"} to the domain @{typ "'d"}. Note that the
minimal invariant is for the domain @{typ "'d"} only.

*}

abbreviation
  eRSV :: "('d::pcpo \<rightarrow> 'd) \<Rightarrow> ('i::type \<Rightarrow> 'd) admS dual \<Rightarrow> ('i \<Rightarrow> 'd) admS \<Rightarrow> bool"
where
  "eRSV e R S \<equiv> \<forall>d \<in> unlr (undual R). (\<lambda>x. e\<cdot>(d x)) \<in> unlr S"

text{*

In general we can also assume that @{term "e"} here is strict, but we
do not need to do so for our examples.

Our locale captures the key ingredients in Pitts's scheme:
\begin{itemize}

\item that the function @{term "\<delta>"} is a minimal invariant;

\item that the functor defining the relation is suitably monotonic; and

\item that the functor is closed with respect to the minimal invariant.

\end{itemize}

*}

locale DomSolV =
  fixes \<delta> :: "('d::pcpo \<rightarrow> 'd) \<rightarrow> 'd \<rightarrow> 'd"
  fixes F :: "('i::type \<Rightarrow> 'd::pcpo) lf"
  assumes min_inv_ID: "fix\<cdot>\<delta> = ID"
  assumes monoF: "mono F"
  assumes eRSV_deltaF:
      "\<And>(e :: 'd \<rightarrow> 'd) (R :: ('i \<Rightarrow> 'd) admS dual) (S :: ('i \<Rightarrow> 'd) admS).
          eRSV e R S \<Longrightarrow> eRSV (\<delta>\<cdot>e) (dual (F (dual S, undual R))) (F (R, S))"
(*<*)
context DomSolV
begin

definition
  sym_lr :: "('i \<Rightarrow> 'd) admS dual \<times> ('i \<Rightarrow> 'd) admS
          \<Rightarrow> ('i \<Rightarrow> 'd) admS dual \<times> ('i \<Rightarrow> 'd) admS"
where
  "sym_lr \<equiv> \<lambda>(rm, rp). (dual (F (dual rp, undual rm)), F (rm, rp))"

lemma sym_lr_mono:
  shows "mono sym_lr"
  unfolding sym_lr_def
  apply (rule monoI)
  using monoF
  apply (simp add: split_def monoD)
  apply (rule monoD[OF monoF])
  apply (simp add: undual_leq fst_mono snd_mono)
  done

abbreviation
  f_lim :: "('i \<Rightarrow> 'd) admS dual \<times> ('i \<Rightarrow> 'd) admS"
where
  "f_lim \<equiv> lfp sym_lr"

definition
  delta_neg :: "('i \<Rightarrow> 'd) admS dual"
where
  "delta_neg = fst f_lim"

definition
  delta_pos :: "('i \<Rightarrow> 'd) admS"
where
  "delta_pos = snd f_lim"

lemma delta:
  "(delta_neg, delta_pos) = f_lim"
  apply (cases f_lim)
  apply (simp add: delta_neg_def delta_pos_def)
  done

lemma delta_neg_sol:
  "delta_neg = dual (F (dual delta_pos, undual delta_neg))"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def less_eq_prod_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_sol:
  "delta_pos = F (delta_neg, delta_pos)"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def less_eq_prod_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_neg_least:
  assumes rm: "rm \<le> F (dual rp, rm)"
  assumes rp: "F (dual rm, rp) \<le> rp"
  shows "delta_neg \<le> dual rm"
    and "delta_pos \<le> rp"
proof -
  from rm rp
  have "(delta_neg, delta_pos) \<le> (dual rm, rp)"
    apply (subst delta)
    apply (rule lfp_lowerbound)
    apply (simp add: sym_lr_def)
    done
  thus "delta_neg \<le> dual rm" and "delta_pos \<le> rp"
    by (simp_all add: undual_leq)
qed

lemma delta_eq:
  "undual delta_neg = delta_pos"
proof(rule antisym)
  show "delta_pos \<le> undual delta_neg"
    apply (rule delta_pos_neg_least(2)[where rm="delta_pos"])
     apply (simp_all add: delta_pos_sol[symmetric])
    by (subst delta_neg_sol, simp)
next
  let ?P = "\<lambda>x. eRSV x (delta_neg) (delta_pos)"
  have "?P (fix\<cdot>\<delta>)"
    apply (rule fix_ind)
      apply simp
     apply (simp add: inst_fun_pcpo[symmetric])
    apply clarsimp
    apply (drule eRSV_deltaF[where R=delta_neg and S=delta_pos])
    apply simp
    apply (subst delta_pos_sol)
    apply (subst (asm) delta_neg_sol)
    apply force
    done
  with min_inv_ID
  show "undual delta_neg \<le> delta_pos"
    by (fastforce simp: unlr_leq[symmetric])
qed
(*>*)
text{*

From these assumptions we can show that there is a unique object that
is a solution to the recursive equation specified by @{term "F"}.

*}

definition "delta \<equiv> delta_pos"

lemma delta_sol: "delta = F (dual delta, delta)"
(*<*)
unfolding delta_def
by (subst delta_eq[symmetric], simp, rule delta_pos_sol)
(*>*)

lemma delta_unique:
  assumes r: "F (dual r, r) = r"
  shows "r = delta"
(*<*)
unfolding delta_def
proof(rule antisym)
  show "delta_pos \<le> r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
next
  have "delta_neg \<le> dual r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
  hence "r \<le> undual delta_neg" by (simp add: less_eq_dual_def)
  thus "r \<le> delta_pos"
    using delta_eq by simp
qed
(*>*)

end

text{*

We use this to show certain functions are not PCF-definable in
\S\ref{sec:pcfdefinability}.

*}

subsection{* Relations between domains and syntax *}

text{*

\label{sec:synlr}

To show computational adequacy (\S\ref{sec:compad}) we need to relate
elements of a domain to their syntactic counterparts. An advantage of
Pitts's technique is that this is straightforward to do.

*}

definition synlr :: "('d::pcpo \<times> 'a::type) set set" where
  "synlr \<equiv> { R :: ('d \<times> 'a) set. \<forall>a. { d. (d, a) \<in> R } \<in> admS }"

typedef ('d::pcpo, 'a::type) synlr = "{ x::('d \<times> 'a) set. x \<in> synlr }"
  morphisms unsynlr mksynlr unfolding synlr_def by fastforce

text{*

An alternative representation (suggested by Brian Huffman) is to
directly use the type @{typ "'a \<Rightarrow> 'b admS"} as this is automatically
a complete lattice. However we end up fighting the automatic methods a
lot.

*}

(*<*)
lemma synlrI [intro]:
  "\<lbrakk> \<And>a. (\<bottom>, a) \<in> R; \<And>a. adm (\<lambda>x. (x, a) \<in> R) \<rbrakk> \<Longrightarrow> R \<in> synlr"
  unfolding synlr_def by fastforce

lemma bottom_in_unsynlr [simp]:
  "(\<bottom>, a) \<in> unsynlr R"
  using synlr.unsynlr [of R] by (simp add: synlr_def admS_def)

lemma adm_unsynlr [simp]:
  "adm (\<lambda>x. (x, a) \<in> unsynlr R)"
  using synlr.unsynlr[of R] by (simp add: synlr_def admS_def)

lemma adm_cont_unsynlr [intro, simp]:
  "cont f \<Longrightarrow> adm (\<lambda>x. (f x, a) \<in> unsynlr r)"
  by (erule adm_subst) simp

declare synlr.mksynlr_inverse[simp add]

text{* Lattice machinery. *}

instantiation synlr :: (pcpo, type) order
begin

definition
  "x \<le> y \<equiv> unsynlr x \<le> unsynlr y"

definition
  "x < y \<equiv> unsynlr x < unsynlr y"

instance
  by standard (auto simp add: less_eq_synlr_def less_synlr_def synlr.unsynlr_inject)

end

lemma mksynlr_leq [iff]: "\<lbrakk> x \<in> synlr; y \<in> synlr \<rbrakk> \<Longrightarrow> (mksynlr x \<le> mksynlr y) \<longleftrightarrow> (x \<le> y)"
  unfolding less_eq_synlr_def by simp

lemma unsynlr_leq: "(unsynlr x \<le> unsynlr y) \<longleftrightarrow> (x \<le> y)"
  unfolding less_eq_synlr_def by simp

instantiation synlr :: (pcpo, type) lattice
begin

definition
  "inf f g \<equiv> mksynlr (unsynlr f \<inter> unsynlr g)"

definition
  "sup f g = mksynlr (unsynlr f \<union> unsynlr g)"

lemma unsynlr_inf: "unsynlr (inf x y) = unsynlr x \<inter> unsynlr y"
  unfolding inf_synlr_def by (simp add: admS_def synlr_def)

lemma unsynlr_sup: "unsynlr (sup x y) = unsynlr x \<union> unsynlr y"
  unfolding sup_synlr_def by (simp add: admS_def synlr_def)

instance
apply intro_classes
apply (auto simp: less_eq_synlr_def unsynlr_inf unsynlr_sup)
done

end

instantiation synlr :: (pcpo, type) bounded_lattice
begin

definition
  "bot_synlr \<equiv> mksynlr ({\<bottom>} \<times> UNIV)"

lemma unsynlr_bot[simp]:
  "unsynlr bot = {\<bottom>} \<times> UNIV"
  by (simp add: admS_def synlr_def bot_synlr_def)

definition
  "top_synlr \<equiv> mksynlr UNIV"

instance
proof
  fix x :: "('a, 'b) synlr"
  show "bot \<le> x" by (auto simp: bot_synlr_def less_eq_synlr_def admS_def synlr_def)
next
  fix x :: "('a, 'b) synlr"
  show "x \<le> top" by (auto simp: top_synlr_def less_eq_synlr_def admS_def synlr_def)
qed

end

instantiation synlr :: (pcpo, type) complete_lattice
begin

definition
  "Inf A \<equiv> mksynlr (Inf (unsynlr ` A))"

definition
  "Sup (A::('a,'b) synlr set) = Inf {y. \<forall>x\<in>A. x \<le> y}"

lemma mksynlr_Inf: "unsynlr (Inf A) = Inf (unsynlr ` A)"
  unfolding Inf_synlr_def by (simp add: admS_def synlr_def)

lemma INT_synlr_bot [simp]:
  "(\<Inter>R. unsynlr R) = {\<bottom>} \<times> UNIV"
apply auto
apply (drule spec[of _ "mksynlr ({\<bottom>} \<times> UNIV)"])
apply (metis bot_synlr_def mem_Sigma_iff singletonE unsynlr_bot)
done

instance
apply standard
apply (auto simp add: less_eq_synlr_def mksynlr_Inf Sup_synlr_def)
apply (auto simp add: Inf_synlr_def bot_synlr_def top_synlr_def)
done

end

(*>*)
text{*

Again we define functors on @{typ "('d, 'a) synlr"}.

*}

type_synonym ('d, 'a) synlf_rep = "('d, 'a) synlr dual \<times> ('d, 'a) synlr \<Rightarrow> ('d \<times> 'a) set"
type_synonym ('d, 'a) synlf = "('d, 'a) synlr dual \<times> ('d, 'a) synlr \<Rightarrow> ('d, 'a) synlr"

text{*

We capture our relations as before. Note we need the inclusion @{term
"e"} to be strict for our example.

*}

abbreviation
  eRSS :: "('d::pcpo \<rightarrow> 'd) \<Rightarrow> ('d, 'a::type) synlr dual \<Rightarrow> ('d, 'a) synlr \<Rightarrow> bool"
where
  "eRSS e R S \<equiv> \<forall>(d, a) \<in> unsynlr (undual R). (e\<cdot>d, a) \<in> unsynlr S"

locale DomSolSyn =
  fixes \<delta> :: "('d::pcpo \<rightarrow> 'd) \<rightarrow> 'd \<rightarrow> 'd"
  fixes F :: "('d::pcpo, 'a::type) synlf"
  assumes min_inv_ID: "fix\<cdot>\<delta> = ID"
  assumes min_inv_strict: "\<And>r. \<delta>\<cdot>r\<cdot>\<bottom> = \<bottom>"
  assumes monoF: "mono F"
  assumes eRS_deltaF:
      "\<And>(e :: 'd \<rightarrow> 'd) (R :: ('d, 'a) synlr dual) (S :: ('d, 'a) synlr).
          \<lbrakk> e\<cdot>\<bottom> = \<bottom>; eRSS e R S \<rbrakk> \<Longrightarrow> eRSS (\<delta>\<cdot>e) (dual (F (dual S, undual R))) (F (R, S))"
(*<*)

context DomSolSyn
begin


definition
  sym_lr :: "('d, 'a) synlr dual \<times> ('d, 'a) synlr
          \<Rightarrow> ('d, 'a) synlr dual \<times> ('d, 'a) synlr"
where
  "sym_lr \<equiv> \<lambda>(rm, rp). (dual (F (dual rp, undual rm)), F (rm, rp))"

lemma sym_lr_mono:
  shows "mono sym_lr"
  unfolding sym_lr_def
  apply (rule monoI)
  using monoF
  apply (simp add: split_def monoD)
  apply (rule monoD[OF monoF])
  apply (simp add: undual_leq fst_mono snd_mono)
  done

abbreviation
  f_lim :: "('d, 'a) synlr dual \<times> ('d, 'a) synlr"
where
  "f_lim \<equiv> lfp sym_lr"

definition
  delta_neg :: "('d, 'a) synlr dual"
where
  "delta_neg = fst f_lim"

definition
  delta_pos :: "('d, 'a) synlr"
where
  "delta_pos = snd f_lim"

lemma delta:
  "(delta_neg, delta_pos) = f_lim"
  apply (cases f_lim)
  apply (simp add: delta_neg_def delta_pos_def)
  done

lemma delta_neg_sol:
  "delta_neg = dual (F (dual delta_pos, undual delta_neg))"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def less_eq_prod_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_sol:
  "delta_pos = F (delta_neg, delta_pos)"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def less_eq_prod_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_neg_least:
  assumes rm: "rm \<le> F (dual rp, rm)"
  assumes rp: "F (dual rm, rp) \<le> rp"
  shows "delta_neg \<le> dual rm"
    and "delta_pos \<le> rp"
proof -
  from rm rp
  have "(delta_neg, delta_pos) \<le> (dual rm, rp)"
    apply (subst delta)
    apply (rule lfp_lowerbound)
    apply (simp add: sym_lr_def)
    done
  thus "delta_neg \<le> dual rm" and "delta_pos \<le> rp"
    by (simp_all add: undual_leq)
qed

lemma delta_eq:
  "undual delta_neg = delta_pos"
proof(rule antisym)
  show "delta_pos \<le> undual delta_neg"
    apply (rule delta_pos_neg_least(2)[where rm="delta_pos"])
     apply (simp_all add: delta_pos_sol[symmetric])
    apply (subst delta_neg_sol) back
    apply simp
    done
next
  let ?P = "\<lambda>x. x\<cdot>\<bottom> = \<bottom> \<and> eRSS x (delta_neg) (delta_pos)"
  have "?P (fix\<cdot>\<delta>)"
    apply (rule fix_ind)
      apply simp
     apply simp
    apply clarsimp
    apply (drule (1) eRS_deltaF[where R=delta_neg and S=delta_pos])
    apply (simp add: min_inv_strict)
    apply (subst delta_pos_sol)
    apply (subst delta_neg_sol)
    apply force
    done
  with min_inv_ID
  show "undual delta_neg \<le> delta_pos"
    by (fastforce simp: unsynlr_leq[symmetric])
qed

definition
  "delta \<equiv> delta_pos"

lemma delta_sol:
  "delta = F (dual delta, delta)"
  unfolding delta_def
  apply (subst delta_eq[symmetric]) back
  apply simp
  apply (rule delta_pos_sol)
  done

lemma delta_unique:
  assumes r: "F (dual r, r) = r"
  shows "r = delta"
unfolding delta_def
proof(rule antisym)
  show "delta_pos \<le> r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
next
  have "delta_neg \<le> dual r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
  hence "r \<le> undual delta_neg" by (simp add: less_eq_dual_def)
  thus "r \<le> delta_pos"
    using delta_eq by simp
qed

end

(*>*)
text{*

Again, from these assumptions we can construct the unique solution to
the recursive equation specified by @{term "F"}.

*}

subsection{* Relations between pairs of domains *}

text{*

Following \citet{DBLP:conf/icalp/Reynolds74} and
\citet{DBLP:journals/tcs/Filinski07}, we want to relate two pairs of
mutually-recursive domains. Each of the pairs represents a (monadic)
computation and value space.

*}

type_synonym ('am, 'bm, 'av, 'bv) lr_pair = "('am \<times> 'bm) admS \<times> ('av \<times> 'bv) admS"

type_synonym ('am, 'bm, 'av, 'bv) lf_pair_rep =
  "('am, 'bm, 'av, 'bv) lr_pair dual \<times> ('am, 'bm, 'av, 'bv) lr_pair \<Rightarrow> (('am \<times> 'bm) set \<times> ('av \<times> 'bv) set)"

type_synonym ('am, 'bm, 'av, 'bv) lf_pair =
  "('am, 'bm, 'av, 'bv) lr_pair dual \<times> ('am, 'bm, 'av, 'bv) lr_pair \<Rightarrow> (('am \<times> 'bm) admS \<times> ('av \<times> 'bv) admS)"

text{*

The inclusions need to be strict to get our example through.

*}

abbreviation
  eRSP :: "(('am::pcpo \<rightarrow> 'am) \<times> ('av::pcpo \<rightarrow> 'av))
       \<Rightarrow> (('bm::pcpo \<rightarrow> 'bm) \<times> ('bv::pcpo \<rightarrow> 'bv))
       \<Rightarrow> (('am \<times> 'bm) admS \<times> ('av \<times> 'bv) admS) dual
       \<Rightarrow> ('am \<times> 'bm) admS \<times> ('av \<times> 'bv) admS
       \<Rightarrow> bool"
where
  "eRSP ea eb R S \<equiv>
     (\<forall>(am, bm) \<in> unlr (fst (undual R)). (fst ea\<cdot>am, fst eb\<cdot>bm) \<in> unlr (fst S))
   \<and> (\<forall>(av, bv) \<in> unlr (snd (undual R)). (snd ea\<cdot>av, snd eb\<cdot>bv) \<in> unlr (snd S))"

locale DomSolP =
  fixes ad :: "(('am::pcpo \<rightarrow> 'am) \<times> ('av::pcpo \<rightarrow> 'av)) \<rightarrow> (('am \<rightarrow> 'am) \<times> ('av \<rightarrow> 'av))"
  fixes bd :: "(('bm::pcpo \<rightarrow> 'bm) \<times> ('bv::pcpo \<rightarrow> 'bv)) \<rightarrow> (('bm \<rightarrow> 'bm) \<times> ('bv \<rightarrow> 'bv))"
  fixes F :: "('am, 'bm, 'av, 'bv) lf_pair"
  assumes monoF: "mono F"
  assumes ad_ID: "fix\<cdot>ad = (ID, ID)"
  assumes bd_ID: "fix\<cdot>bd = (ID, ID)"
  assumes ad_strict: "\<And>r. fst (ad\<cdot>r)\<cdot>\<bottom> = \<bottom>" "\<And>r. snd (ad\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  assumes bd_strict: "\<And>r. fst (bd\<cdot>r)\<cdot>\<bottom> = \<bottom>" "\<And>r. snd (bd\<cdot>r)\<cdot>\<bottom> = \<bottom>"
  assumes eRSP_deltaF:
    "\<lbrakk> eRSP ea eb R S; fst ea\<cdot>\<bottom> = \<bottom>; snd ea\<cdot>\<bottom> = \<bottom>; fst eb\<cdot>\<bottom> = \<bottom>; snd ea\<cdot>\<bottom> = \<bottom> \<rbrakk>
      \<Longrightarrow> eRSP (ad\<cdot>ea) (bd\<cdot>eb) (dual (F (dual S, undual R))) (F (R, S))"
(*<*)

context DomSolP
begin

definition
  sym_lr :: "('am, 'bm, 'av, 'bv) lr_pair dual \<times> ('am, 'bm, 'av, 'bv) lr_pair
          \<Rightarrow> ('am, 'bm, 'av, 'bv) lr_pair dual \<times> ('am, 'bm, 'av, 'bv) lr_pair"
where
  "sym_lr \<equiv> \<lambda>(rm, rp). (dual (F (dual rp, undual rm)), F (rm, rp))"

lemma sym_lr_mono:
  shows "mono sym_lr"
  unfolding sym_lr_def
  apply (rule monoI)
  using monoF
  apply (simp add: split_def monoD)
  apply (rule monoD[OF monoF])
  apply (simp add: undual_leq fst_mono snd_mono)
  done

abbreviation
  f_lim :: "('am, 'bm, 'av, 'bv) lr_pair dual \<times> ('am, 'bm, 'av, 'bv) lr_pair"
where
  "f_lim \<equiv> lfp sym_lr"

definition
  delta_neg :: "('am, 'bm, 'av, 'bv) lr_pair dual"
where
  "delta_neg = fst f_lim"

definition
  delta_pos :: "('am, 'bm, 'av, 'bv) lr_pair"
where
  "delta_pos = snd f_lim"

lemma delta:
  "(delta_neg, delta_pos) = f_lim"
  apply (cases f_lim)
  apply (simp add: delta_neg_def delta_pos_def)
  done

lemma delta_neg_sol:
  "delta_neg = dual (F (dual delta_pos, undual delta_neg))"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_sol:
  "delta_pos = F (delta_neg, delta_pos)"
  apply (simp add: delta_neg_def delta_pos_def sym_lr_def split_def)
  apply (subst lfp_unfold)
   apply (rule monoI)
   apply (auto simp: less_eq_dual_def
              split: prod.split
              intro: monoD[OF monoF])
  done

lemma delta_pos_neg_least:
  assumes rm: "rm \<le> F (dual rp, rm)"
  assumes rp: "F (dual rm, rp) \<le> rp"
  shows "delta_neg \<le> dual rm"
    and "delta_pos \<le> rp"
proof -
  from rm rp
  have "(delta_neg, delta_pos) \<le> (dual rm, rp)"
    apply (subst delta)
    apply (rule lfp_lowerbound)
    apply (simp add: sym_lr_def)
    done
  thus "delta_neg \<le> dual rm" and "delta_pos \<le> rp"
    by (simp_all add: undual_leq)
qed

lemma delta_eq:
  "undual delta_neg = delta_pos"
proof(rule antisym)
  show "delta_pos \<le> undual delta_neg"
    apply (rule delta_pos_neg_least(2)[where rm="delta_pos"])
     apply (simp_all add: delta_pos_sol[symmetric])
    apply (subst delta_neg_sol) back
    apply simp
    done
next
  let ?P = "\<lambda>(ea, eb). eRSP ea eb (delta_neg) (delta_pos) \<and> fst ea\<cdot>\<bottom> = \<bottom> \<and> snd ea\<cdot>\<bottom> = \<bottom> \<and> fst eb\<cdot>\<bottom> = \<bottom> \<and> snd eb\<cdot>\<bottom> = \<bottom>"
  have "?P (fix\<cdot>ad, fix\<cdot>bd)"
    apply (rule parallel_fix_ind)
      apply simp
     apply simp
    using ad_strict bd_strict
    apply clarsimp
    apply (cut_tac ea="(a, b)" and eb="(aa, ba)" in eRSP_deltaF[where R=delta_neg and S=delta_pos])
    apply simp_all
    apply (simp add: delta_pos_sol[symmetric])
    apply (subst delta_neg_sol)
    apply simp
    apply (subst delta_neg_sol)
    apply simp
    done
  hence "?P ((ID, ID), (ID, ID))" by (simp only: ad_ID bd_ID)
  thus "undual delta_neg \<le> delta_pos"
    by (fastforce simp: unlr_leq[symmetric] less_eq_prod_def)
qed

definition
  "delta \<equiv> delta_pos"

lemma delta_sol:
  "delta = F (dual delta, delta)"
  unfolding delta_def
  apply (subst delta_eq[symmetric]) back
  apply simp
  apply (rule delta_pos_sol)
  done

lemma delta_unique:
  assumes r: "F (dual r, r) = r"
  shows "r = delta"
unfolding delta_def
proof(rule antisym)
  show "delta_pos \<le> r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
next
  have "delta_neg \<le> dual r"
    using assms delta_pos_neg_least[where rm=r and rp=r] by simp
  hence "r \<le> undual delta_neg" by (simp add: less_eq_dual_def)
  thus "r \<le> delta_pos"
    using delta_eq by simp
qed

end
(*>*)

text{*

We use this solution to relate the direct and continuation semantics
for PCF in \S\ref{sec:continuations}.

*}
(*<*)

end
(*>*)
