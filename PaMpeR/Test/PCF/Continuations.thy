(*  Title:      Continuations.thy
    Author:     Peter Gammie
*)

section {* Relating direct and continuation semantics *}
(*<*)
theory Continuations
imports
  PCF
begin

(*>*)
text{*

\label{sec:continuations}

This is a fairly literal version of
\citet{DBLP:conf/icalp/Reynolds74}, adapted to untyped PCF. A more
abstract account has been given by
\citet{DBLP:journals/tcs/Filinski07} in terms of a monadic meta
language, which is difficult to model in Isabelle (but see
\citet{Huffman:MonadTransformers:2012}).

We begin by giving PCF a continuation semantics following the modern
account of \citet{wadler92:_essence_of_funct_progr}.  We use the
symmetric function space @{text "('o ValK, 'o) K \<rightarrow> ('o ValK, 'o) K"}
as our language includes call-by-name.

*}

type_synonym ('a, 'o) K = "('a \<rightarrow> 'o) \<rightarrow> 'o"

domain 'o ValK
  = ValKF (lazy appKF :: "('o ValK, 'o) K \<rightarrow> ('o ValK, 'o) K")
  | ValKTT | ValKFF
  | ValKN (lazy "nat")

type_synonym 'o ValKM = "('o ValK, 'o) K"
(*<*)

lemma ValK_case_ID [simp]:
  "ValK_case\<cdot>ValKF\<cdot>ValKTT\<cdot>ValKFF\<cdot>ValKN = ID"
  apply (rule cfun_eqI)
  apply (case_tac x)
  apply simp_all
  done

lemma below_monic_ValKF [iff]:
  "below_monic_cfun ValKF"
  by (rule below_monicI) simp

lemma below_monic_ValKN [iff]:
  "below_monic_cfun ValKN"
  by (rule below_monicI) simp

(*>*)
text{*

We use the standard continuation monad to ease the semantic
definition.

*}

definition unitK :: "'o ValK \<rightarrow> 'o ValKM" where
  "unitK \<equiv> \<Lambda> a. \<Lambda> c. c\<cdot>a"

definition bindK :: "'o ValKM \<rightarrow> ('o ValK \<rightarrow> 'o ValKM) \<rightarrow> 'o ValKM" where
  "bindK \<equiv> \<Lambda> m k. \<Lambda> c. m\<cdot>(\<Lambda> a. k\<cdot>a\<cdot>c)"

definition appKM :: "'o ValKM \<rightarrow> 'o ValKM \<rightarrow> 'o ValKM" where
  "appKM \<equiv> \<Lambda> fK xK. bindK\<cdot>fK\<cdot>(\<Lambda> (ValKF\<cdot>f). f\<cdot>xK)"
(*<*)

lemma unitK_simps [simp]:
  "unitK\<cdot>v\<cdot>c = c\<cdot>v"
  unfolding unitK_def by simp

lemma bindK_strict:
  "bindK\<cdot>\<bottom> = \<bottom>"
  unfolding bindK_def by (simp add: eta_cfun)

lemma bindK_unitl:
  "bindK\<cdot>(unitK\<cdot>e)\<cdot>f = f\<cdot>e"
  unfolding bindK_def unitK_def by (simp add: eta_cfun)

lemma bindK_unitr:
  "bindK\<cdot>e\<cdot>unitK = e"
  unfolding bindK_def unitK_def by (simp add: eta_cfun)

lemma bindK_assoc:
  "bindK\<cdot>(bindK\<cdot>f\<cdot>g)\<cdot>h = bindK\<cdot>f\<cdot>(\<Lambda> v. bindK\<cdot>(g\<cdot>v)\<cdot>h)"
  unfolding bindK_def unitK_def by simp

lemmas bindK_simps[simp] = bindK_strict bindK_unitl bindK_unitr bindK_assoc

(*>*)
text{* The interpretations of the constants. *}

definition
  condK :: "'o ValKM \<rightarrow> 'o ValKM \<rightarrow> 'o ValKM \<rightarrow> 'o ValKM"
where
  "condK \<equiv> \<Lambda> iK tK eK. bindK\<cdot>iK\<cdot>(\<Lambda> i. case i of
                ValKF\<cdot>f \<Rightarrow> \<bottom> | ValKTT \<Rightarrow> tK | ValKFF \<Rightarrow> eK | ValKN\<cdot>n \<Rightarrow> \<bottom>)"

definition succK :: "'o ValKM \<rightarrow> 'o ValKM" where
  "succK \<equiv> \<Lambda> nK. bindK\<cdot>nK\<cdot>(\<Lambda> (ValKN\<cdot>n). unitK\<cdot>(ValKN\<cdot>(n + 1)))"

definition predK :: "'o ValKM \<rightarrow> 'o ValKM" where
  "predK \<equiv> \<Lambda> nK. bindK\<cdot>nK\<cdot>(\<Lambda> (ValKN\<cdot>n). case n of 0 \<Rightarrow> \<bottom> | Suc n \<Rightarrow> unitK\<cdot>(ValKN\<cdot>n))"

definition isZeroK :: "'o ValKM \<rightarrow> 'o ValKM" where
  "isZeroK \<equiv> \<Lambda> nK. bindK\<cdot>nK\<cdot>(\<Lambda> (ValKN\<cdot>n). unitK\<cdot>(if n = 0 then ValKTT else ValKFF))"

text {*

A continuation semantics for PCF. If we had defined our direct
semantics using a monad then the correspondence would be more
syntactically obvious.

*}

type_synonym 'o EnvK = "'o ValKM Env"

primrec
  evalK :: "expr \<Rightarrow> 'o EnvK \<rightarrow> 'o ValKM"
where
  "evalK (Var v) = (\<Lambda> \<rho>. \<rho>\<cdot>v)"
| "evalK (App f x) = (\<Lambda> \<rho>. appKM\<cdot>(evalK f\<cdot>\<rho>)\<cdot>(evalK x\<cdot>\<rho>))"
| "evalK (AbsN v e) = (\<Lambda> \<rho>. unitK\<cdot>(ValKF\<cdot>(\<Lambda> x. evalK e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>))))"
| "evalK (AbsV v e) = (\<Lambda> \<rho>. unitK\<cdot>(ValKF\<cdot>(\<Lambda> x c. x\<cdot>(\<Lambda> x'. evalK e\<cdot>(env_ext\<cdot>v\<cdot>(unitK\<cdot>x')\<cdot>\<rho>)\<cdot>c))))"
| "evalK (Diverge) = (\<Lambda> \<rho>. \<bottom>)"
| "evalK (Fix v e) = (\<Lambda> \<rho>. \<mu> x. evalK e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>))"
| "evalK (tt) = (\<Lambda> \<rho>. unitK\<cdot>ValKTT)"
| "evalK (ff) = (\<Lambda> \<rho>. unitK\<cdot>ValKFF)"
| "evalK (Cond i t e) = (\<Lambda> \<rho>. condK\<cdot>(evalK i\<cdot>\<rho>)\<cdot>(evalK t\<cdot>\<rho>)\<cdot>(evalK e\<cdot>\<rho>))"
| "evalK (Num n) = (\<Lambda> \<rho>. unitK\<cdot>(ValKN\<cdot>n))"
| "evalK (Succ e) = (\<Lambda> \<rho>. succK\<cdot>(evalK e\<cdot>\<rho>))"
| "evalK (Pred e) = (\<Lambda> \<rho>. predK\<cdot>(evalK e\<cdot>\<rho>))"
| "evalK (IsZero e) = (\<Lambda> \<rho>. isZeroK\<cdot>(evalK e\<cdot>\<rho>))"

text{*

To establish the chain completeness (admissibility) of our logical
relation, we need to show that @{term "unitK"} is an \emph{order
monic}, i.e., if @{term "unitK\<cdot>x \<sqsubseteq> unitK\<cdot>y"} then @{term "x \<sqsubseteq>
y"}. This is an order-theoretic version of injectivity.

In order to define a continuation that witnesses this, we need to be
able to distinguish converging and diverging computations. We
therefore require our observation domain to contain at least two
elements:

*}

locale at_least_two_elements =
  fixes some_non_bottom_element :: "'o::domain"
  assumes some_non_bottom_element: "some_non_bottom_element \<noteq> \<bottom>"

text{*

Following \citet{DBLP:conf/icalp/Reynolds74} and \citet[Remark
47]{DBLP:journals/tcs/Filinski07} we use the following continuation:

*}

lemma cont_below [simp, cont2cont]:
  "cont (\<lambda>x::'a::pcpo. if x \<sqsubseteq> d then \<bottom> else c)"
(*<*)
proof(rule contI2)
  show "monofun (\<lambda>x. if x \<sqsubseteq> d then \<bottom> else c)"
    apply (rule monofunI)
    apply clarsimp
    apply (cut_tac x=x and y=y and z=d in below_trans)
    apply auto
    done
next
  fix Y :: "nat \<Rightarrow> 'a::pcpo"
  assume Y: "chain Y"
  assume "chain (\<lambda>i. if Y i \<sqsubseteq> d then \<bottom> else c)"
  show "(if (\<Squnion> i. Y i) \<sqsubseteq> d then \<bottom> else c) \<sqsubseteq> (\<Squnion> i. if Y i \<sqsubseteq> d then \<bottom> else c)"
  proof(cases "\<forall>i. Y i \<sqsubseteq> d")
    case True hence "Lub Y \<sqsubseteq> d"
      using lub_below_iff[OF Y] by simp
    thus ?thesis by simp
  next
    case False
    let ?f = "\<lambda>i. if Y i \<sqsubseteq> d then \<bottom> else c"
    from False have LubY: "\<not> Lub Y \<sqsubseteq> d"
      using lub_below_iff[OF Y] by simp
    from False have F: "chain ?f"
      apply -
      apply (rule chainI)
      apply clarsimp
      apply (cut_tac i=i and j="Suc i" in chain_mono[OF Y])
      apply clarsimp
      apply (cut_tac x="Y i" and y="Y (Suc i)" and z=d in below_trans)
      apply simp_all
      done
    from False obtain i where Yi: "\<not> Y i \<sqsubseteq> d" by blast
    hence M: "max_in_chain i ?f"
      apply -
      apply (rule max_in_chainI)
      apply clarsimp
      apply (drule chain_mono[OF Y])
      apply (cut_tac x="Y i" and y="Y j" and z=d in below_trans)
      apply simp_all
      done
    from LubY Yi show ?thesis
      using iffD1[OF maxinch_is_thelub, OF F M] by simp
  qed
qed
(*>*)
text{**}

lemma (in at_least_two_elements) below_monic_unitK [intro, simp]:
  "below_monic_cfun (unitK :: 'o ValK \<rightarrow> 'o ValKM)"
proof(rule below_monicI)
  fix v v' :: "'o ValK"
  assume vv': "unitK\<cdot>v \<sqsubseteq> unitK\<cdot>v'"
  let ?k = "\<Lambda> x. if x \<sqsubseteq> v' then \<bottom> else some_non_bottom_element"
  from vv' have "unitK\<cdot>v\<cdot>?k \<sqsubseteq> unitK\<cdot>v'\<cdot>?k" by (rule monofun_cfun_fun)
  hence "?k\<cdot>v \<sqsubseteq> ?k\<cdot>v'" by (simp add: unitK_def)
  with some_non_bottom_element show "v \<sqsubseteq> v'" by (auto split: if_split_asm)
qed


subsection{* Logical relation *}

text{*

We follow \citet{DBLP:conf/icalp/Reynolds74} by simultaneously
defining a pair of relations over values and functions. Both are
bottom-reflecting, in contrast to the situation for computational
adequacy in \S\ref{sec:compad}.  \citet{DBLP:journals/tcs/Filinski07}
differs by assuming that values are always defined, and relates values
and monadic computations.

*}

type_synonym 'o lfr = "(ValD, 'o ValKM, ValD \<rightarrow> ValD, 'o ValKM \<rightarrow> 'o ValKM) lf_pair_rep"
type_synonym 'o lflf = "(ValD, 'o ValKM, ValD \<rightarrow> ValD, 'o ValKM \<rightarrow> 'o ValKM) lf_pair"

context at_least_two_elements
begin

abbreviation lr_eta_rep_N where
  "lr_eta_rep_N \<equiv> { (e, e') .
       (e = \<bottom> \<and> e' = \<bottom>)
     \<or> (e = ValTT \<and> e' = unitK\<cdot>ValKTT)
     \<or> (e = ValFF \<and> e' = unitK\<cdot>ValKFF)
     \<or> (\<exists>n. e = ValN\<cdot>n \<and> e' = unitK\<cdot>(ValKN\<cdot>n)) }"

abbreviation lr_eta_rep_F where
  "lr_eta_rep_F \<equiv> \<lambda>(rm, rp). { (e, e') .
       (e = \<bottom> \<and> e' = \<bottom>)
     \<or> (\<exists>f f'. e = ValF\<cdot>f \<and> e' = unitK\<cdot>(ValKF\<cdot>f') \<and> (f, f') \<in> unlr (snd rp)) }"

definition lr_eta_rep where
  "lr_eta_rep \<equiv> \<lambda>r. lr_eta_rep_N \<union> lr_eta_rep_F r"

definition lr_theta_rep where
  "lr_theta_rep \<equiv> \<lambda>(rm, rp). { (f, f') .
     (\<forall>(x, x') \<in> unlr (fst (undual rm)). (f\<cdot>x, f'\<cdot>x') \<in> unlr (fst rp)) }"

definition lr_rep :: "'o lfr" where
  "lr_rep \<equiv> \<lambda>r. (lr_eta_rep r, lr_theta_rep r)"

abbreviation lr :: "'o lflf" where
  "lr \<equiv> \<lambda>r. (mklr (fst (lr_rep r)), mklr (snd (lr_rep r)))"
(*<*)
text{*

Properties of the logical relation.

*}

lemma admS_eta_rep [intro, simp]:
  "fst (lr_rep r) \<in> admS"
  unfolding lr_rep_def lr_eta_rep_def
  apply simp
  apply rule
  apply (auto intro!: adm_disj simp: split_def)
   using adm_below_monic_exists[OF _ below_monic_pair[OF below_monic_ValN below_monic_cfcomp2[OF below_monic_unitK below_monic_ValKN]], where P="\<lambda>_. True"]
   apply (simp add: prod_eq_iff)
  using adm_below_monic_exists[OF _ below_monic_pair_split[OF below_monic_ValF below_monic_cfcomp2[OF below_monic_unitK below_monic_ValKF]], where P="\<lambda>x. x \<in> unlr (snd (snd r))"]
  apply (simp add: prod_eq_iff)
  done

lemma admS_theta_rep [intro, simp]:
  "snd (lr_rep r) \<in> admS"
proof
  show "\<bottom> \<in> snd (lr_rep r)"
    unfolding lr_rep_def lr_theta_rep_def
    by (cases r) simp
next
  show "adm (\<lambda>x. x \<in> snd (lr_rep r))"
    apply (rule admI)
    unfolding lr_rep_def lr_theta_rep_def
    apply (clarsimp simp: split_def)
    apply (rule admD)
      apply (rule adm_subst)
      apply force+
    done
qed

lemma mono_lr:
  shows "mono (lr :: 'o lflf)"
  apply (rule monoI)
  apply simp
  apply (simp add: lr_rep_def)
  apply (rule conjI)
   apply (force simp: lr_eta_rep_def split_def undual_leq[symmetric] unlr_leq[symmetric])
  (* FIXME stuck with the projections on the product *)
  apply (auto simp: lr_theta_rep_def split_def undual_leq[symmetric] unlr_leq[symmetric])

  apply (drule_tac x="(ae, bc)" in bspec)
   apply (case_tac a)
   apply (case_tac ab)
   apply (auto simp: unlr_leq[symmetric])
  done

(*>*)
end (* context at_least_two_elements *)

text{*

It takes some effort to set up the minimal invariant relating the two
pairs of domains. One might hope this would be easier using deflations
(which might compose) rather than ``copy'' functions (which certainly
don't).

We elide these as they are tedious.

*}
(*<*)

primrec
  ValD_copy_i :: "nat \<Rightarrow> ValD \<rightarrow> ValD"
where
  "ValD_copy_i 0 = \<bottom>"
| "ValD_copy_i (Suc n) = (\<Lambda> v. case v of ValF\<cdot>f \<Rightarrow> ValF\<cdot>(ValD_copy_i n oo f oo ValD_copy_i n) | ValTT \<Rightarrow> ValTT | ValFF \<Rightarrow> ValFF | ValN\<cdot>m \<Rightarrow> ValN\<cdot>m)"

abbreviation
  "ValD_copy_lub \<equiv> (\<Squnion>i. ValD_copy_i i)"

lemma ValD_copy_chain [intro, simp]:
  "chain ValD_copy_i"
proof(rule chainI)
  fix i show "ValD_copy_i i \<sqsubseteq> ValD_copy_i (Suc i)"
  proof(induct i)
    case (Suc i)
    { fix x
      have "ValD_copy_i (Suc i)\<cdot>x \<sqsubseteq> ValD_copy_i (Suc (Suc i))\<cdot>x"
      proof(cases x)
        case (ValF f) with Suc show ?thesis
          by (clarsimp simp: cfcomp1 cfun_below_iff monofun_cfun)
      qed simp_all }
    thus ?case by (simp add: cfun_below_iff)
  qed simp
qed

lemma ValD_copy_lub_ID:
  "ValD_copy_lub = ID"
proof -
  { fix x :: ValD
    fix i :: nat
    have "ValD_take i\<cdot>(ValD_copy_i i\<cdot>(ValD_take i\<cdot>x)) = ValD_take i\<cdot>x"
    proof (induct i arbitrary: x)
      case (Suc n) thus ?case
        by (cases x) (simp_all add: cfun_map_def)
    qed simp }
  hence "\<And>x :: ValD. (\<Squnion>i. ValD_take i\<cdot>(ValD_copy_i i\<cdot>(ValD_take i\<cdot>x))) = (\<Squnion>i. ValD_take i\<cdot>x)"
    by (blast intro: lub_eq)
  thus ?thesis by (simp add: lub_distribs ValD.lub_take cfun_eq_iff)
qed

lemma ValD_copy_strict [intro, simp]:
  "ValD_copy\<cdot>\<bottom> = \<bottom>"
  using ValD_copy_lub_ID by simp

text{*

Continuations: we need to ensure the observation type is always the
same.

*}

definition
  KM_map :: "('o ValK \<rightarrow> 'o ValK) \<rightarrow> 'o ValKM \<rightarrow> 'o ValKM"
where
  "KM_map \<equiv> \<Lambda> f. cfun_map\<cdot>(cfun_map\<cdot>f\<cdot>ID)\<cdot>ID"

lemma KM_map_id [intro, simp]:
  "KM_map\<cdot>ID = ID"
  unfolding KM_map_def by (simp add: cfun_map_ID)

lemma KM_map_strict [intro, simp]:
  "KM_map\<cdot>f\<cdot>\<bottom> = \<bottom>"
  unfolding KM_map_def by (simp add: cfun_map_def)

primrec
  ValK_copy_i :: "nat \<Rightarrow> 'o ValK \<rightarrow> 'o ValK"
where
  "ValK_copy_i 0 = \<bottom>"
| "ValK_copy_i (Suc n) = (\<Lambda> v. case v of ValKF\<cdot>f \<Rightarrow> ValKF\<cdot>(cfun_map\<cdot>(KM_map\<cdot>(ValK_copy_i n))\<cdot>(KM_map\<cdot>(ValK_copy_i n))\<cdot>f) | ValKTT \<Rightarrow> ValKTT | ValKFF \<Rightarrow> ValKFF | ValKN\<cdot>m \<Rightarrow> ValKN\<cdot>m)"

abbreviation
  "ValK_copy \<equiv> (\<Squnion>i. ValK_copy_i i)"

lemma ValK_copy_chain [intro, simp]:
  "chain (ValK_copy_i :: nat \<Rightarrow> 'o ValK \<rightarrow> 'o ValK)"
proof(rule chainI)
  fix i show "ValK_copy_i i \<sqsubseteq> (ValK_copy_i (Suc i) :: 'o ValK \<rightarrow> 'o ValK)"
  proof(induct i)
    case (Suc i)
    { fix x :: "'o ValK"
      have "ValK_copy_i (Suc i)\<cdot>x \<sqsubseteq> ValK_copy_i (Suc (Suc i))\<cdot>x"
      proof(cases x)
        case (ValKF f) with Suc show ?thesis by (clarsimp simp: monofun_cfun KM_map_def)
      qed simp_all }
    thus ?case by (simp add: cfun_below_iff)
  qed simp
qed

lemma ValK_copy_fix:
  "ValK_copy = (ID :: 'o ValK \<rightarrow> 'o ValK)"
proof -
  { fix x :: "'o ValK"
    fix i :: nat
    have "ValK_take i\<cdot>(ValK_copy_i i\<cdot>(ValK_take i\<cdot>x)) = ValK_take i\<cdot>x"
    proof (induct i arbitrary: x)
      case (Suc n) thus ?case
        by (cases x) (simp_all add: KM_map_def cfun_map_def)
    qed simp }
  hence "\<And>x :: 'o ValK. (\<Squnion>i. ValK_take i\<cdot>(ValK_copy_i i\<cdot>(ValK_take i\<cdot>x))) = (\<Squnion>i. ValK_take i\<cdot>x)"
    by (blast intro: lub_eq)
  thus ?thesis by (simp add: lub_distribs ValK.lub_take cfun_eq_iff)
qed

lemma ValK_strict [intro, simp]:
  "ValK_copy\<cdot>\<bottom> = \<bottom>"
  by (simp add: ValK_copy_fix)

text{*

We need to respect the purported domain structure, and positive and
negative occurrences.

*}

fixrec
  ValD_copy_rec :: "((ValD \<rightarrow> ValD) \<times> ((ValD \<rightarrow> ValD) \<rightarrow> (ValD \<rightarrow> ValD)))
                  \<rightarrow> ((ValD \<rightarrow> ValD) \<times> ((ValD \<rightarrow> ValD) \<rightarrow> (ValD \<rightarrow> ValD)))"
where
  "ValD_copy_rec\<cdot>r =
     (\<Lambda> v. case v of ValF\<cdot>f \<Rightarrow> ValF\<cdot>(snd r\<cdot>f) | ValTT \<Rightarrow> ValTT | ValFF \<Rightarrow> ValFF | ValN\<cdot>n \<Rightarrow> ValN\<cdot>n,
      \<Lambda> f. cfun_map\<cdot>(strictify\<cdot>(fst r))\<cdot>(strictify\<cdot>(fst r))\<cdot>f)"

abbreviation
  ValD_copy_eta :: "nat \<Rightarrow> ValD \<rightarrow> ValD"
where
  "ValD_copy_eta i \<equiv> fst (iterate i\<cdot>ValD_copy_rec\<cdot>\<bottom>)"

abbreviation
  ValD_copy_theta :: "nat \<Rightarrow> (ValD \<rightarrow> ValD) \<rightarrow> (ValD \<rightarrow> ValD)"
where
  "ValD_copy_theta i \<equiv> snd (iterate i\<cdot>ValD_copy_rec\<cdot>\<bottom>)"

lemma ValD_copy_eta_theta_strict [intro, simp]:
  "ValD_copy_eta n\<cdot>\<bottom> = \<bottom>"
  "ValD_copy_theta n\<cdot>\<bottom> = \<bottom>"
  by (induct n) (simp_all add: cfun_map_def)

lemma ValD_copy_fix_strict [simp]:
  "fst (fix\<cdot>ValD_copy_rec)\<cdot>\<bottom> = \<bottom>"
  "snd (fix\<cdot>ValD_copy_rec)\<cdot>\<bottom> = \<bottom>"
  by (subst fix_eq, simp add: cfun_map_def)+

lemma ValD_copy_rec_ValD_copy_lub:
  "fix\<cdot>ValD_copy_rec = (ValD_copy_lub, cfun_map\<cdot>ValD_copy_lub\<cdot>ValD_copy_lub)" (is "?lhs = ?rhs")
proof(rule below_antisym)
  show "?lhs \<sqsubseteq> ?rhs"
    apply (rule fix_least)
    apply (simp add: eta_cfun strictify_cancel ValD_copy_lub_ID cfun_map_def ID_def)
    done
next
  { fix i have "ValD_copy_i i \<sqsubseteq> fst (fix\<cdot>ValD_copy_rec)"
    proof(induct i)
      case (Suc i) thus ?case
        apply -
        apply (subst fix_eq)
        apply (subst fix_eq)
        apply (simp add: eta_cfun strictify_cancel cfcomp1 cfun_map_def)
        apply (intro monofun_cfun_fun monofun_cfun_arg)
        apply (simp add: eta_cfun strictify_cancel monofun_cfun cfcomp1 cfun_map_def cfun_below_iff)
        done
    qed simp }
  hence D: "ValD_copy_lub \<sqsubseteq> fst (fix\<cdot>ValD_copy_rec)" by (simp add: lub_below_iff)
  moreover
  from D
  have "cfun_map\<cdot>ValD_copy_lub\<cdot>ValD_copy_lub \<sqsubseteq> snd (fix\<cdot>ValD_copy_rec)"
    by (subst fix_eq) (simp add: eta_cfun strictify_cancel monofun_cfun)
  ultimately show "?rhs \<sqsubseteq> ?lhs" by (simp add: prod_belowI)
qed

lemma fix_ValD_copy_rec_ID:
  "fix\<cdot>ValD_copy_rec = (ID, ID)"
  using ValD_copy_rec_ValD_copy_lub ValD_copy_lub_ID cfun_map_ID
  by simp

fixrec
  ValK_copy_rec :: "(('o ValKM \<rightarrow> 'o ValKM) \<times> (('o ValKM \<rightarrow> 'o ValKM) \<rightarrow> ('o ValKM \<rightarrow> 'o ValKM)))
                  \<rightarrow> ('o ValKM \<rightarrow> 'o ValKM) \<times> (('o ValKM \<rightarrow> 'o ValKM) \<rightarrow> ('o ValKM \<rightarrow> 'o ValKM))"
where
  "ValK_copy_rec\<cdot>r =
     (\<Lambda> vm. KM_map\<cdot>(\<Lambda> v. case v of ValKF\<cdot>f \<Rightarrow> ValKF\<cdot>(snd r\<cdot>f) | ValKTT \<Rightarrow> ValKTT | ValKFF \<Rightarrow> ValKFF | ValKN\<cdot>a \<Rightarrow> ValKN\<cdot>a)\<cdot>vm,
      \<Lambda> f. cfun_map\<cdot>(strictify\<cdot>(fst r))\<cdot>(strictify\<cdot>(fst r))\<cdot>f)"

abbreviation
  ValK_copy_eta
where
  "ValK_copy_eta i \<equiv> fst (iterate i\<cdot>ValK_copy_rec\<cdot>\<bottom>)"

abbreviation
  ValK_copy_theta
where
  "ValK_copy_theta i \<equiv> snd (iterate i\<cdot>ValK_copy_rec\<cdot>\<bottom>)"

lemma ValK_copy_strict [intro, simp]:
  "ValK_copy_eta n\<cdot>\<bottom> = (\<bottom> :: 'o ValKM)"
  "ValK_copy_theta n\<cdot>\<bottom> = (\<bottom> :: 'o ValKM \<rightarrow> 'o ValKM)"
  by (induct n) (simp_all add: cfun_map_def)

lemma ValK_copy_fix_strict [simp]:
  "fst (fix\<cdot>ValK_copy_rec)\<cdot>\<bottom> = \<bottom>"
  "snd (fix\<cdot>ValK_copy_rec)\<cdot>\<bottom> = \<bottom>"
  by (subst fix_eq, simp add: cfun_map_def)+

lemma ValK_copy_rec_ValK_copy:
  "fix\<cdot>ValK_copy_rec
  = (KM_map\<cdot>(ValK_copy :: 'o ValK \<rightarrow> 'o ValK),
     cfun_map\<cdot>(KM_map\<cdot>ValK_copy)\<cdot>(KM_map\<cdot>ValK_copy))" (is "?lhs = ?rhs")
proof(rule below_antisym)
  show "?lhs \<sqsubseteq> ?rhs"
    apply (rule fix_least)
    apply (simp add: eta_cfun strictify_cancel cfun_map_def ID_def)
    apply (intro cfun_eqI)
    apply (simp add: KM_map_def cfun_map_def ValK_copy_fix eta_cfun)
    done
next
  { fix i
    have "KM_map\<cdot>(ValK_copy_i i :: 'o ValK \<rightarrow> 'o ValK) \<sqsubseteq> fst (fix\<cdot>ValK_copy_rec)"
     and "(ValK_copy_i i :: 'o ValK \<rightarrow> 'o ValK) \<sqsubseteq> ValK_case\<cdot>(\<Lambda> f. ValKF\<cdot>(snd (fix\<cdot>ValK_copy_rec)\<cdot>f))\<cdot>ValKTT\<cdot>ValKFF\<cdot>ValKN"
    proof(induct i)
      case 0
      { case 1 show ?case
          apply (subst fix_eq)
          apply (auto iff: cfun_below_iff intro!: monofun_cfun_arg simp: KM_map_def cfun_map_def eta_cfun)
          done }
      { case 2 show ?case by simp }
    next
      case (Suc i)
      { case 1 from Suc show ?case
          apply -
          apply (subst fix_eq)
          apply (subst fix_eq)
          apply (simp add: eta_cfun strictify_cancel cfcomp1 cfun_map_def KM_map_def)
          apply (intro cfun_belowI)
          apply (simp add: eta_cfun strictify_cancel cfcomp1 cfun_map_def KM_map_def)
          apply (intro monofun_cfun_arg)
          apply (intro cfun_belowI)
          apply (simp add: eta_cfun strictify_cancel cfcomp1 cfun_map_def KM_map_def)
          apply (intro monofun_cfun_arg)
          apply (simp add: eta_cfun strictify_cancel monofun_cfun cfcomp1 cfun_map_def)
          apply (intro monofun_cfun)
          apply simp_all
          apply (intro cfun_belowI)
          apply (simp add: eta_cfun strictify_cancel monofun_cfun cfcomp1 cfun_map_def)
          apply (intro cfun_belowI)
          apply (subst fix_eq)
          apply (simp add: eta_cfun strictify_cancel monofun_cfun cfcomp1 KM_map_def cfun_map_def)
          apply (intro monofun_cfun)
          apply simp_all
          apply (subst fix_eq)
          apply (intro cfun_belowI)
          apply (simp add: eta_cfun strictify_cancel monofun_cfun cfcomp1 KM_map_def cfun_map_def)
          apply (intro monofun_cfun)
          apply simp_all
          apply (intro cfun_belowI)
          apply simp
          apply (intro monofun_cfun)
          apply simp_all
          apply (intro cfun_belowI)
          apply simp
          apply (intro monofun_cfun)
          apply simp_all
          done }
      { case 2 from Suc show ?case
          apply -
          apply (subst fix_eq)
          apply (subst fix_eq)
          apply (auto simp: eta_cfun strictify_cancel cfcomp1 cfun_map_def KM_map_def cfun_below_iff intro!: monofun_cfun)
          done }
    qed }
  hence "(\<Squnion>i. KM_map\<cdot>(ValK_copy_i i :: 'o ValK \<rightarrow> 'o ValK)) \<sqsubseteq> fst (fix\<cdot>ValK_copy_rec)"
    by (simp add: lub_below_iff)
  hence D: "KM_map\<cdot>(ValK_copy :: 'o ValK \<rightarrow> 'o ValK) \<sqsubseteq> fst (fix\<cdot>ValK_copy_rec)"
    by (simp add: contlub_cfun_arg[symmetric])
  from D
  have E: "cfun_map\<cdot>(KM_map\<cdot>(ValK_copy :: 'o ValK \<rightarrow> 'o ValK))\<cdot>(KM_map\<cdot>ValK_copy) \<sqsubseteq> snd (fix\<cdot>ValK_copy_rec)"
    apply (subst fix_eq)
    apply (simp add: eta_cfun strictify_cancel KM_map_def)
    apply (intro monofun_cfun)
    apply simp_all
    done
  show "?rhs \<sqsubseteq> ?lhs" by (simp add: prod_belowI D E)
qed

lemma fix_ValK_copy_rec_ID:
  "fix\<cdot>ValK_copy_rec = (ID, ID)"
  by (simp add: ValK_copy_rec_ValK_copy ValK_copy_fix cfun_map_ID)

lemma (in at_least_two_elements) min_inv_lr:
  assumes "fst ea\<cdot>\<bottom> = \<bottom>"
  assumes "fst eb\<cdot>\<bottom> = \<bottom>"
  assumes "eRSP ea eb R S"
  shows "eRSP (ValD_copy_rec\<cdot>ea) (ValK_copy_rec\<cdot>eb) (dual ((lr :: 'o lflf) (dual S, undual R))) (lr (R, S))"
  using assms some_non_bottom_element
  apply (simp add: split_def)
  apply (auto simp: split_def lr_rep_def lr_eta_rep_def lr_theta_rep_def KM_map_def cfun_map_def unitK_def)
  apply (force simp: cfun_map_def strictify_cancel unitK_def) (* FIXME obvious but auto misses it *)
  done

(*>*)
sublocale at_least_two_elements < F: DomSolP ValD_copy_rec ValK_copy_rec lr
  apply standard
         apply (rule mono_lr)
        apply (rule fix_ValD_copy_rec_ID)
       apply (rule fix_ValK_copy_rec_ID)
      apply (simp_all add: cfun_map_def)[4]
  apply (erule (2) min_inv_lr)
  done


subsection{* A retraction between the two definitions *}

text{*

We can use the relation to establish a strong connection between the
direct and continuation semantics.  All results depend on the
observation type being rich enough.

*}

context at_least_two_elements
begin

abbreviation mrel ("\<eta>: _ \<mapsto> _" [50, 51] 50) where
  "\<eta>: x \<mapsto> x' \<equiv> (x, x') \<in> unlr (fst F.delta)"

abbreviation vrel ("\<theta>: _ \<mapsto> _" [50, 51] 50) where
  "\<theta>: y \<mapsto> y' \<equiv> (y, y') \<in> unlr (snd F.delta)"
(*<*)
lemma F_bottom_triv [intro, simp]:
  "\<eta>: \<bottom> \<mapsto> \<bottom>"
  "\<theta>: \<bottom> \<mapsto> \<bottom>"
  by simp_all

lemma etaI [intro, simp]:
  "\<eta>: ValTT \<mapsto> unitK\<cdot>ValKTT"
  "\<eta>: ValFF \<mapsto> unitK\<cdot>ValKFF"
  "\<eta>: ValN\<cdot>n \<mapsto> unitK\<cdot>(ValKN\<cdot>n)"
  by (subst F.delta_sol, simp, simp add: lr_rep_def lr_eta_rep_def)+

lemma eta_F:
  "\<theta>: f \<mapsto> f' \<Longrightarrow> \<eta>: ValF\<cdot>f \<mapsto> unitK\<cdot>(ValKF\<cdot>f')"
apply (subst F.delta_sol)
apply simp
apply (subst lr_rep_def)
apply (fastforce simp: lr_eta_rep_def split_def)
done

lemma theta_F:
  "(\<And>x x'. \<eta>: x \<mapsto> x' \<Longrightarrow> \<eta>: f\<cdot>x \<mapsto> f'\<cdot>x') \<Longrightarrow> \<theta>: f \<mapsto> f'"
apply (subst F.delta_sol)
apply simp
apply (subst lr_rep_def)
apply (simp add: lr_theta_rep_def split_def)
done

lemma eta_induct[case_names bottom N F, consumes 1]:
  "\<lbrakk> \<eta>: x \<mapsto> x';
     \<lbrakk> x = \<bottom>; x' = \<bottom> \<rbrakk> \<Longrightarrow> P x x';
     \<And>n. \<lbrakk> x = ValTT; x' = unitK\<cdot>ValKTT \<rbrakk> \<Longrightarrow> P x x';
     \<And>n. \<lbrakk> x = ValFF; x' = unitK\<cdot>ValKFF \<rbrakk> \<Longrightarrow> P x x';
     \<And>n. \<lbrakk> x = ValN\<cdot>n; x' = unitK\<cdot>(ValKN\<cdot>n) \<rbrakk> \<Longrightarrow> P x x';
     \<And>f f'. \<lbrakk> x = ValF\<cdot>f; x' = unitK\<cdot>(ValKF\<cdot>f'); \<theta>: f \<mapsto> f' \<rbrakk> \<Longrightarrow> P x x'
   \<rbrakk> \<Longrightarrow> P x x'"
  apply (cases x)
      apply (subst (asm) F.delta_sol, simp, simp add: lr_rep_def lr_eta_rep_def)
     defer
     apply (subst (asm) F.delta_sol, simp, simp add: lr_rep_def lr_eta_rep_def)
    apply (subst (asm) F.delta_sol, simp, simp add: lr_rep_def lr_eta_rep_def)
   apply (subst (asm) F.delta_sol, simp, simp add: lr_rep_def lr_eta_rep_def)
  apply simp
  apply (subst (asm) F.delta_sol)
  apply simp
  apply (subst (asm) lr_rep_def)
  apply (subst (asm) lr_eta_rep_def)
  apply clarsimp
  done

lemma theta_induct[case_names F, consumes 1]:
  "\<lbrakk> \<theta>: f \<mapsto> f';
     (\<And>x x'. \<eta>: x \<mapsto> x' \<Longrightarrow> \<eta>: f\<cdot>x \<mapsto> f'\<cdot>x') \<Longrightarrow> P f f'
   \<rbrakk> \<Longrightarrow> P f f'"
  apply (subst (asm) F.delta_sol)
  apply simp
  apply (subst (asm) lr_rep_def)
  apply (subst (asm) lr_theta_rep_def)
  apply fastforce
  done

(*>*)
text{*

Theorem 1 from \citet{DBLP:conf/icalp/Reynolds74}.

*}

lemma AbsV_aux:
  assumes "\<eta>: ValF\<cdot>f \<mapsto> unitK\<cdot>(ValKF\<cdot>f')"
  shows "\<eta>: ValF\<cdot>(strictify\<cdot>f) \<mapsto> unitK\<cdot>(ValKF\<cdot>(\<Lambda> x c. x\<cdot>(\<Lambda> x'. f'\<cdot>(unitK\<cdot>x')\<cdot>c)))"
(*<*)
  apply (rule eta_F)
  apply (rule theta_F)
  using assms
  apply (rule eta_induct) (* FIXME special rule would help *)
  apply simp_all
  apply (drule injD[OF below_monic_inj[OF below_monic_unitK]])
  apply clarsimp
  apply (erule theta_induct)
  apply (erule eta_induct)
  apply (simp_all add: eta_cfun eta_F)
  done

(*>*)
text{**}

theorem Theorem1:
  assumes "\<forall>v. \<eta>: \<rho>\<cdot>v \<mapsto> \<rho>'\<cdot>v"
  shows "\<eta>: evalD e\<cdot>\<rho> \<mapsto> evalK e\<cdot>\<rho>'"
(*<*)
using assms
proof(induct e arbitrary: \<rho> \<rho>')
  case App show ?case
    apply simp
    apply (simp add: appKM_def bindK_def)
    using App.hyps(1)[OF App(3)]
    apply (rule eta_induct)
      apply simp_all
    apply (simp add: eta_cfun)
    apply (erule theta_induct)
    using App.hyps(2)[OF App(3)]
    apply simp
    done
next
  case AbsN show ?case
    apply simp
    apply (rule eta_F)
    apply (rule theta_F)
    apply simp
    apply (rule AbsN.hyps)
    using AbsN(2)
    unfolding env_ext_def
    apply simp
    done
next
  case (AbsV v e \<rho> \<rho>')
  have "\<eta>: ValF\<cdot>(\<Lambda> x. evalD e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>)) \<mapsto> unitK\<cdot>(ValKF\<cdot>(\<Lambda> x. evalK e\<cdot>(env_ext\<cdot>v\<cdot>x\<cdot>\<rho>')))"
    apply (rule eta_F)
    apply (rule theta_F)
    apply simp
    apply (rule AbsV.hyps)
    using AbsV(2)
    unfolding env_ext_def
    apply simp
    done
  thus ?case by (fastforce dest: AbsV_aux)
next
  case Fix thus ?case
    apply simp
    apply (rule parallel_fix_ind)
    apply (simp_all add: env_ext_def)
    done
next
  case Cond thus ?case
    apply (simp add: cond_def condK_def eta_cfun)
    using Cond(1)[OF Cond(4)]
    apply (rule eta_induct)
    apply simp_all
    done
next
  case Succ thus ?case
    apply (simp add: succ_def succK_def eta_cfun)
    using Succ(1)[OF Succ(2)]
    apply (rule eta_induct)
    apply simp_all
    done
next
  case Pred thus ?case
    apply (simp add: pred_def predK_def eta_cfun)
    using Pred(1)[OF Pred(2)]
    apply (rule eta_induct)
    apply (simp_all split: nat.split)
    done
next
  case IsZero thus ?case
    apply (simp add: isZero_def isZeroK_def eta_cfun)
    using IsZero(1)[OF IsZero(2)]
    apply (rule eta_induct)
    apply (simp_all split: nat.split)
    done
qed simp_all
(*>*)

end


text{*

The retraction between the two value and monadic value spaces.

Note we need to work with an observation type that can represent the
``explicit values'', i.e. @{typ "'o ValK"}.

*}

locale value_retraction =
  fixes VtoO :: "'o ValK \<rightarrow> 'o"
  fixes OtoV :: "'o \<rightarrow> 'o ValK"
  assumes OV: "OtoV oo VtoO = ID"

sublocale value_retraction < at_least_two_elements "VtoO\<cdot>(ValKN\<cdot>0)"
using OV by - (standard, simp add: injection_defined cfcomp1 cfun_eq_iff)

context value_retraction
begin

fun
  DtoKM_i :: "nat \<Rightarrow> ValD \<rightarrow> 'o ValKM"
and
  KMtoD_i :: "nat \<Rightarrow> 'o ValKM \<rightarrow> ValD"
where
  "DtoKM_i 0 = \<bottom>"
| "DtoKM_i (Suc n) = (\<Lambda> v. case v of
     ValF\<cdot>f \<Rightarrow> unitK\<cdot>(ValKF\<cdot>(cfun_map\<cdot>(KMtoD_i n)\<cdot>(DtoKM_i n)\<cdot>f))
   | ValTT \<Rightarrow> unitK\<cdot>ValKTT
   | ValFF \<Rightarrow> unitK\<cdot>ValKFF
   | ValN\<cdot>m \<Rightarrow> unitK\<cdot>(ValKN\<cdot>m))"

| "KMtoD_i 0 = \<bottom>"
| "KMtoD_i (Suc n) = (\<Lambda> v. case OtoV\<cdot>(v\<cdot>VtoO) of
     ValKF\<cdot>f \<Rightarrow> ValF\<cdot>(cfun_map\<cdot>(DtoKM_i n)\<cdot>(KMtoD_i n)\<cdot>f)
   | ValKTT \<Rightarrow> ValTT
   | ValKFF \<Rightarrow> ValFF
   | ValKN\<cdot>m \<Rightarrow> ValN\<cdot>m)"

abbreviation "DtoKM \<equiv> (\<Squnion>i. DtoKM_i i)"
abbreviation "KMtoD \<equiv> (\<Squnion>i. KMtoD_i i)"
(*<*)

lemma DtoKM_KMtoD_chain [intro, simp]:
  "chain DtoKM_i"
  "chain KMtoD_i"
proof -
  let ?C = "\<lambda>i. (DtoKM_i i, KMtoD_i i)"
  have "chain ?C"
  proof(rule chainI)
    fix i show "?C i \<sqsubseteq> ?C (Suc i)"
    proof(induct i)
      case (Suc i) show ?case
      proof(rule monofun_pair)
        show "DtoKM_i (Suc i) \<sqsubseteq> DtoKM_i (Suc (Suc i))"
        proof(rule cfun_belowI)
          fix x from Suc show "DtoKM_i (Suc i)\<cdot>x \<sqsubseteq> DtoKM_i (Suc (Suc i))\<cdot>x"
            by (cases x) (auto intro!: monofun_cfun simp: cfun_map_def cfun_below_iff)
        qed
        show "KMtoD_i (Suc i) \<sqsubseteq> KMtoD_i (Suc (Suc i))"
        proof(rule cfun_belowI)
          fix x from Suc show "KMtoD_i (Suc i)\<cdot>x \<sqsubseteq> KMtoD_i (Suc (Suc i))\<cdot>x"
            apply (simp add: eta_cfun)
            apply (intro monofun_cfun_fun monofun_cfun_arg)
            apply (intro cfun_belowI)
            apply (auto intro: monofun_cfun)
            done
        qed
      qed
    qed simp
  qed
  then show "chain DtoKM_i" "chain KMtoD_i"
    by (auto dest: ch2ch_fst ch2ch_snd)
qed
(*>*)

text{*

Lemma 1 from \citet{DBLP:conf/icalp/Reynolds74}.

*}

lemma Lemma1:
  "\<eta>: x \<mapsto> DtoKM\<cdot>x"
  "\<eta>: x \<mapsto> x' \<Longrightarrow> x = KMtoD\<cdot>x'"
(*<*)
proof -
  { fix x x' i
    have "\<eta>: ValD_copy_i i\<cdot>x \<mapsto> DtoKM_i i\<cdot>x"
     and "\<eta>: x \<mapsto> x' \<Longrightarrow> ValD_copy_i i\<cdot>x = KMtoD_i i\<cdot>x'"
    proof(induct i arbitrary: x x')
      case 0
      { case 1 thus ?case by simp }
      { case 2 thus ?case by simp }
    next
      case (Suc i)
      { case 1 show ?case
          apply (cases x)
            apply simp_all
          apply (rule eta_F)
          apply (rule theta_F)
          using Suc
          apply simp
          done }
      { case 2 thus ?case
          apply (induct rule: eta_induct)
            using OV
            apply (simp_all add: cfun_eq_iff retraction_strict)
          apply (clarsimp simp: cfun_eq_iff)
          apply (erule theta_induct)
          using Suc
          apply simp
          done }
    qed }
  note K = this
  let ?C1 = "\<lambda>i. (ValD_copy_i i, DtoKM_i i)"
  let ?P1 = "\<lambda>f. \<eta>: (fst f)\<cdot>x \<mapsto> (snd f)\<cdot>x"
  have "adm ?P1" by (rule adm_subst) simp_all
  with K(1)
  have "?P1 (\<Squnion>i. ValD_copy_i i, \<Squnion>i. DtoKM_i i)"
    using admD[where P="?P1" and Y="?C1"]
    using lub_prod[where S="?C1"]
    apply simp
    done
  moreover
  { fix x :: ValD
    fix x' :: "'o ValKM"
    let ?C2 = "\<lambda>i. (ValD_copy_i i, KMtoD_i i)"
    let ?P2 = "\<lambda>f. (fst f)\<cdot>x = (snd f)\<cdot>x'"
    have "adm (\<lambda>f. ?P2 f)" by simp
    with K(2) have "\<eta>: x \<mapsto> x' \<Longrightarrow> ?P2 (\<Squnion>i. ValD_copy_i i, \<Squnion>i. KMtoD_i i)"
      using admD[where P="?P2" and Y="?C2"] lub_prod[where S="?C2"]
      by simp }
  ultimately show
    "\<eta>: x \<mapsto> DtoKM\<cdot>x"
    "\<eta>: x \<mapsto> x' \<Longrightarrow> x = KMtoD\<cdot>x'"
    apply (simp_all add: ValD_copy_lub_ID)
    done
qed

(*>*)
text{*

Theorem 2 from \citet{DBLP:conf/icalp/Reynolds74}.

*}

theorem Theorem2: "evalD e\<cdot>\<rho> = KMtoD\<cdot>(evalK e\<cdot>(DtoKM oo \<rho>))"
using Lemma1(2)[OF Theorem1] Lemma1(1) by (simp add: cfcomp1)

end

text{*

\citet[Remark~48]{DBLP:journals/tcs/Filinski07} observes that there
will not be a retraction between direct and continuation semantics for
languages with richer notions of effects.

It should be routine to extend the above approach to the higher-order
backtracking language of \citet{DBLP:conf/icfp/WandV04}.

I wonder if it is possible to construct continuation semantics from
direct semantics as proposed by
\citet{DBLP:journals/jacm/SethiT80}. Roughly we might hope to lift a
retraction between two value domains to a retraction at higher types
by synthesising a suitable logical relation.

*}
(*<*)

end
(*>*)
