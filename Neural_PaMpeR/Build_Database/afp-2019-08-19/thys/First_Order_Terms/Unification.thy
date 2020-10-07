(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>A Concrete Unification Algorithm\<close>

theory Unification
  imports
    Abstract_Unification
    Option_Monad
begin

definition
  "decompose s t =
    (case (s, t) of
      (Fun f ss, Fun g ts) \<Rightarrow> if f = g then zip_option ss ts else None
    | _ \<Rightarrow> None)"

lemma decompose_Some [dest]:
  "decompose (Fun f ss) (Fun g ts) = Some E \<Longrightarrow>
    f = g \<and> length ss = length ts \<and> E = zip ss ts"
  by (cases "f = g") (auto simp: decompose_def)

lemma decompose_None [dest]:
  "decompose (Fun f ss) (Fun g ts) = None \<Longrightarrow> f \<noteq> g \<or> length ss \<noteq> length ts"
  by (cases "f = g") (auto simp: decompose_def)

text \<open>Applying a substitution to a list of equations.\<close>
definition
  subst_list :: "('f, 'v) subst \<Rightarrow> ('f, 'v) equation list \<Rightarrow> ('f, 'v) equation list"
  where
    "subst_list \<sigma> ys = map (\<lambda>p. (fst p \<cdot> \<sigma>, snd p \<cdot> \<sigma>)) ys"

lemma mset_subst_list [simp]:
  "mset (subst_list (subst x t) ys) = subst_mset (subst x t) (mset ys)"
  by (auto simp: subst_mset_def subst_list_def)

lemma subst_list_append:
  "subst_list \<sigma> (xs @ ys) = subst_list \<sigma> xs @ subst_list \<sigma> ys"
by (auto simp: subst_list_def)

function (sequential)
  unify ::
    "('f, 'v) equation list \<Rightarrow> ('v \<times> ('f, 'v) term) list \<Rightarrow> ('v \<times> ('f, 'v) term) list option"
where
  "unify [] bs = Some bs"
| "unify ((Fun f ss, Fun g ts) # E) bs =
    (case decompose (Fun f ss) (Fun g ts) of
      None \<Rightarrow> None
    | Some us \<Rightarrow> unify (us @ E) bs)"
| "unify ((Var x, t) # E) bs =
    (if t = Var x then unify E bs
    else if x \<in> vars_term t then None
    else unify (subst_list (subst x t) E) ((x, t) # bs))"
| "unify ((t, Var x) # E) bs =
    (if x \<in> vars_term t then None
    else unify (subst_list (subst x t) E) ((x, t) # bs))"
  by pat_completeness auto
termination
  by (standard, rule wf_inv_image [of "unif\<inverse>" "mset \<circ> fst", OF wf_converse_unif])
     (force intro: UNIF1.intros simp: unif_def union_commute)+

definition subst_of :: "('v \<times> ('f, 'v) term) list \<Rightarrow> ('f, 'v) subst"
  where
    "subst_of ss = List.foldr (\<lambda>(x, t) \<sigma>. \<sigma> \<circ>\<^sub>s subst x t) ss Var"

text \<open>Computing the mgu of two terms.\<close>
fun mgu :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst option" where
  "mgu s t =
    (case unify [(s, t)] [] of
      None \<Rightarrow> None
    | Some res \<Rightarrow> Some (subst_of res))"

lemma subst_of_simps [simp]:
  "subst_of [] = Var"
  "subst_of ((x, Var x) # ss) = subst_of ss"
  "subst_of (b # ss) = subst_of ss \<circ>\<^sub>s subst (fst b) (snd b)"
  by (simp_all add: subst_of_def split: prod.splits)

lemma subst_of_append [simp]:
  "subst_of (ss @ ts) = subst_of ts \<circ>\<^sub>s subst_of ss"
  by (induct ss) (auto simp: ac_simps)

text \<open>The concrete algorithm \<open>unify\<close> can be simulated by the inference
  rules of \<open>UNIF\<close>.\<close>
lemma unify_Some_UNIF:
  assumes "unify E bs = Some cs"
  shows "\<exists>ds ss. cs = ds @ bs \<and> subst_of ds = compose ss \<and> UNIF ss (mset E) {#}"
using assms
proof (induction E bs arbitrary: cs rule: unify.induct)
  case (2 f ss g ts E bs)
  then obtain us where "decompose (Fun f ss) (Fun g ts) = Some us"
    and [simp]: "f = g" "length ss = length ts" "us = zip ss ts"
    and "unify (us @ E) bs = Some cs" by (auto split: option.splits)
  from "2.IH" [OF this(1, 5)] obtain xs ys
    where "cs = xs @ bs"
    and [simp]: "subst_of xs = compose ys"
    and *: "UNIF ys (mset (us @ E)) {#}" by auto
  then have "UNIF (Var # ys) (mset ((Fun f ss, Fun g ts) # E)) {#}"
    by (force intro: UNIF1.decomp simp: ac_simps)
  moreover have "cs = xs @ bs" by fact
  moreover have "subst_of xs = compose (Var # ys)" by simp
  ultimately show ?case by blast
next
  case (3 x t E bs)
  show ?case
  proof (cases "t = Var x")
    assume "t = Var x"
    then show ?case
      using 3 by auto (metis UNIF.step compose_simps(2) UNIF1.trivial)
  next
    assume "t \<noteq> Var x"
    with 3 obtain xs ys
      where [simp]: "cs = (ys @ [(x, t)]) @ bs"
      and [simp]: "subst_of ys = compose xs"
      and "x \<notin> vars_term t"
      and "UNIF xs (mset (subst_list (subst x t) E)) {#}"
        by (cases "x \<in> vars_term t") force+
    then have "UNIF (subst x t # xs) (mset ((Var x, t) # E)) {#}"
      by (force intro: UNIF1.Var_left simp: ac_simps)
    moreover have "cs = (ys @ [(x, t)]) @ bs" by simp
    moreover have "subst_of (ys @ [(x, t)]) = compose (subst x t # xs)" by simp
    ultimately show ?case by blast
  qed
next
  case (4 f ss x E bs)
  with 4 obtain xs ys
    where [simp]: "cs = (ys @ [(x, Fun f ss)]) @ bs"
    and [simp]: "subst_of ys = compose xs"
    and "x \<notin> vars_term (Fun f ss)"
    and "UNIF xs (mset (subst_list (subst x (Fun f ss)) E)) {#}"
      by (cases "x \<in> vars_term (Fun f ss)") force+
  then have "UNIF (subst x (Fun f ss) # xs) (mset ((Fun f ss, Var x) # E)) {#}"
    by (force intro: UNIF1.Var_right simp: ac_simps)
  moreover have "cs = (ys @ [(x, Fun f ss)]) @ bs" by simp
  moreover have "subst_of (ys @ [(x, Fun f ss)]) = compose (subst x (Fun f ss) # xs)" by simp
  ultimately show ?case by blast
qed force

lemma unify_sound:
  assumes "unify E [] = Some cs"
  shows "is_imgu (subst_of cs) (set E)"
proof -
  from unify_Some_UNIF [OF assms] obtain ss
    where "subst_of cs = compose ss"
    and "UNIF ss (mset E) {#}" by auto
  with UNIF_empty_imp_is_mgu_compose [OF this(2)]
    and UNIF_idemp [OF this(2)]
    show ?thesis
      by (auto simp add: is_imgu_def is_mgu_def)
         (metis subst_compose_assoc)
qed

text \<open>If \<open>unify\<close> gives up, then the given set of equations
  cannot be reduced to the empty set by \<open>UNIF\<close>.\<close>
lemma unify_None:
  assumes "unify E ss = None"
  shows "\<exists>E'. E' \<noteq> {#} \<and> (mset E, E') \<in> unif\<^sup>!"
using assms
proof (induction E ss rule: unify.induct)
  case (1 bs)
  then show ?case by simp
next
  case (2 f ss g ts E bs)
  moreover
  { assume *: "decompose (Fun f ss) (Fun g ts) = None"
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(Fun f ss, Fun g ts)#}"] obtain \<sigma>
        where "(mset E + {#(Fun f ss, Fun g ts)#}, {#(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover have "{#(Fun f ss \<cdot> \<sigma>, Fun g ts \<cdot> \<sigma>)#} \<in> NF unif"
        using decompose_None [OF *]
        by (auto simp: single_is_union NF_def unif_def elim!: UNIF1.cases)
           (metis length_map)
      ultimately show ?thesis
        by auto (metis normalizability_I add_mset_not_empty)
    next
      case False
      moreover have "\<not> unifiable {(Fun f ss, Fun g ts)}"
        using * by (auto simp: unifiable_def)
      ultimately have "\<not> unifiable (set ((Fun f ss, Fun g ts) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis by (simp add: not_unifiable_imp_not_empty_NF)
    qed }
  moreover
  { fix us
    assume *: "decompose (Fun f ss) (Fun g ts) = Some us"
      and "unify (us @ E) bs = None"
    from "2.IH" [OF this] obtain E'
      where "E' \<noteq> {#}" and "(mset (us @ E), E') \<in> unif\<^sup>!" by blast
    moreover have "(mset ((Fun f ss, Fun g ts) # E), mset (us @ E)) \<in> unif"
    proof -
      have "g = f" and "length ss = length ts" and "us = zip ss ts"
        using * by auto
      then show ?thesis
        by (auto intro: UNIF1.decomp simp: unif_def ac_simps)
    qed
    ultimately have ?case by auto }
  ultimately show ?case by (auto split: option.splits)
next
  case (3 x t E bs)
  { assume [simp]: "t = Var x"
    obtain E' where "E' \<noteq> {#}" and "(mset E, E') \<in> unif\<^sup>!" using 3 by auto
    moreover have "(mset ((Var x, t) # E), mset E) \<in> unif"
      by (auto intro: UNIF1.trivial simp: unif_def)
    ultimately have ?case by auto }
  moreover
  { assume *: "t \<noteq> Var x" "x \<notin> vars_term t"
    then obtain E' where "E' \<noteq> {#}"
      and "(mset (subst_list (subst x t) E), E') \<in> unif\<^sup>!" using 3 by auto
    moreover have "(mset ((Var x, t) # E), mset (subst_list (subst x t) E)) \<in> unif"
      using * by (auto intro: UNIF1.Var_left simp: unif_def)
    ultimately have ?case by auto }
  moreover
  { assume *: "t \<noteq> Var x" "x \<in> vars_term t"
    then have "x \<in> vars_term t" "is_Fun t" by auto
    then have "\<not> unifiable {(Var x, t)}" by (rule in_vars_is_Fun_not_unifiable)
    then have **: "\<not> unifiable {(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)}" for \<sigma> :: "('b, 'a) subst"
      using subst_set_reflects_unifiable [of \<sigma> "{(Var x, t)}"] by (auto simp: subst_set_def)
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(Var x, t)#}"] obtain \<sigma>
        where "(mset E + {#(Var x, t)#}, {#(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover obtain E' where "E' \<noteq> {#}"
        and "({#(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)#}, E') \<in> unif\<^sup>!"
        using not_unifiable_imp_not_empty_NF and **
          by (metis set_mset_single)
      ultimately show ?thesis by auto
    next
      case False
      moreover have "\<not> unifiable {(Var x, t)}"
        using * by (force simp: unifiable_def)
      ultimately have "\<not> unifiable (set ((Var x, t) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis
        by (simp add: not_unifiable_imp_not_empty_NF)
    qed }
  ultimately show ?case by blast
next
  case (4 f ss x E bs)
  define t where "t = Fun f ss"
  { assume *: "x \<notin> vars_term t"
    then obtain E' where "E' \<noteq> {#}"
      and "(mset (subst_list (subst x t) E), E') \<in> unif\<^sup>!" using 4 by (auto simp: t_def)
    moreover have "(mset ((t, Var x) # E), mset (subst_list (subst x t) E)) \<in> unif"
      using * by (auto intro: UNIF1.Var_right simp: unif_def)
    ultimately have ?case by (auto simp: t_def) }
  moreover
  { assume "x \<in> vars_term t"
    then have *: "x \<in> vars_term t" "t \<noteq> Var x" by (auto simp: t_def)
    then have "x \<in> vars_term t" "is_Fun t" by auto
    then have "\<not> unifiable {(Var x, t)}" by (rule in_vars_is_Fun_not_unifiable)
    then have **: "\<not> unifiable {(Var x \<cdot> \<sigma>, t \<cdot> \<sigma>)}" for \<sigma> :: "('b, 'a) subst"
      using subst_set_reflects_unifiable [of \<sigma> "{(Var x, t)}"] by (auto simp: subst_set_def)
    have ?case
    proof (cases "unifiable (set E)")
      case True
      then have "(mset E, {#}) \<in> unif\<^sup>*"
        by (simp add: unifiable_imp_empty)
      from unif_rtrancl_mono [OF this, of "{#(t, Var x)#}"] obtain \<sigma>
        where "(mset E + {#(t, Var x)#}, {#(t \<cdot> \<sigma>, Var x \<cdot> \<sigma>)#}) \<in> unif\<^sup>*"
        by (auto simp: subst_mset_def)
      moreover obtain E' where "E' \<noteq> {#}"
        and "({#(t \<cdot> \<sigma>, Var x \<cdot> \<sigma>)#}, E') \<in> unif\<^sup>!"
        using not_unifiable_imp_not_empty_NF and **
          by (metis unifiable_insert_swap set_mset_single)
      ultimately show ?thesis by (auto simp: t_def)
    next
      case False
      moreover have "\<not> unifiable {(t, Var x)}"
        using * by (simp add: unifiable_def)
      ultimately have "\<not> unifiable (set ((t, Var x) # E))" by (auto simp: unifiable_def unifiers_def)
      then show ?thesis by (simp add: not_unifiable_imp_not_empty_NF t_def)
    qed }
  ultimately show ?case by blast
qed

lemma unify_complete:
  assumes "unify E bs = None"
  shows "unifiers (set E) = {}"
proof -
  from unify_None [OF assms] obtain E'
    where "E' \<noteq> {#}" and "(mset E, E') \<in> unif\<^sup>!" by blast
  then have "\<not> unifiable (set E)"
    using irreducible_reachable_imp_not_unifiable by force
  then show ?thesis
    by (auto simp: unifiable_def)
qed

lemma mgu_complete:
  "mgu s t = None \<Longrightarrow> unifiers {(s, t)} = {}"
proof -
  assume "mgu s t = None"
  then have "unify [(s, t)] [] = None" by (cases "unify [(s, t)] []", auto)
  then have "unifiers (set [(s, t)]) = {}" by (rule unify_complete)
  then show ?thesis by simp
qed

lemma finite_subst_domain_subst_of:
  "finite (subst_domain (subst_of xs))"
proof (induct xs)
  case (Cons x xs)
  moreover have "finite (subst_domain (subst (fst x) (snd x)))" by (metis finite_subst_domain_subst)
  ultimately show ?case
    using subst_domain_compose [of "subst_of xs" "subst (fst x) (snd x)"]
    by (simp del: subst_subst_domain) (metis finite_subset infinite_Un)
qed simp

lemma mgu_subst_domain:
  assumes "mgu s t = Some \<sigma>"
  shows "subst_domain \<sigma> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where *: "unify [(s, t)] [] = Some xs" and [simp]: "subst_of xs = \<sigma>"
    using assms by (simp split: option.splits)
  from unify_Some_UNIF [OF *] obtain ss
    where "compose ss = \<sigma>" and "UNIF ss {#(s, t)#} {#}" by auto
  with UNIF_subst_domain_subset [of ss "{#(s, t)#}" "{#}"]
  show ?thesis using vars_mset_singleton by fastforce
qed

lemma mgu_finite_subst_domain:
  "mgu s t = Some \<sigma> \<Longrightarrow> finite (subst_domain \<sigma>)"
  by (cases "unify [(s, t)] []")
    (auto simp: finite_subst_domain_subst_of)

lemma mgu_sound:
  assumes "mgu s t = Some \<sigma>"
  shows "is_imgu \<sigma> {(s, t)}"
proof -
  obtain ss where "unify [(s, t)] [] = Some ss"
    and "\<sigma> = subst_of ss"
    using assms by (auto split: option.splits)
  then have "is_imgu \<sigma> (set [(s, t)])" by (metis unify_sound)
  then show ?thesis by simp
qed

end
