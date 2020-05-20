(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
section \<open>Matching\<close>

theory Matching
  imports
    Abstract_Matching
    Unification (* for decompose *)
begin

function match_term_list
where
  "match_term_list [] \<sigma> = Some \<sigma>" |
  "match_term_list ((Var x, t) # P) \<sigma> =
    (if \<sigma> x = None \<or> \<sigma> x = Some t then match_term_list P (\<sigma> (x \<mapsto> t))
    else None)" |
  "match_term_list ((Fun f ss, Fun g ts) # P) \<sigma> =
    (case decompose (Fun f ss) (Fun g ts) of
      None \<Rightarrow> None
    | Some us \<Rightarrow> match_term_list (us @ P) \<sigma>)" |
  "match_term_list ((Fun f ss, Var x) # P) \<sigma> = None"
  by (pat_completeness) auto
termination
  by (standard, rule wf_inv_image [OF wf_measure [of size_mset], of "mset \<circ> fst"]) (auto simp: pair_size_def)

lemma match_term_list_Some_matchrel:
  assumes "match_term_list P \<sigma> = Some \<tau>"
  shows "((mset P, \<sigma>), ({#}, \<tau>)) \<in> matchrel\<^sup>*"
using assms
proof (induction P \<sigma> rule: match_term_list.induct)
  case (2 x t P \<sigma>)
  from "2.prems"
    have *: "\<sigma> x = None \<or> \<sigma> x = Some t"
    and **: "match_term_list P (\<sigma> (x \<mapsto> t)) = Some \<tau>" by (auto split: if_splits)
  from MATCH1.Var [of \<sigma> x t "mset P", OF *]
    have "((mset ((Var x, t) # P), \<sigma>), (mset P, \<sigma> (x \<mapsto> t))) \<in> matchrel\<^sup>*"
    by (simp add: MATCH1_matchrel_conv)
  with "2.IH" [OF * **] show ?case by (blast dest: rtrancl_trans)
next
  case (3 f ss g ts P \<sigma>)
  let ?s = "Fun f ss" and ?t = "Fun g ts"
  from "3.prems" have [simp]: "f = g"
    and *: "length ss = length ts"
    and **: "decompose ?s ?t = Some (zip ss ts)"
      "match_term_list (zip ss ts @ P) \<sigma> = Some \<tau>"
    by (auto split: option.splits)
  from MATCH1.Fun [OF *, of "mset P" g \<sigma>]
    have "((mset ((?s, ?t) # P), \<sigma>), (mset (zip ss ts @ P), \<sigma>)) \<in> matchrel\<^sup>*"
    by (simp add: MATCH1_matchrel_conv ac_simps)
  with "3.IH" [OF **] show ?case by (blast dest: rtrancl_trans)
qed simp_all

lemma match_term_list_None:
  assumes "match_term_list P \<sigma> = None"
  shows "matchers_map \<sigma> \<inter> matchers (set P) = {}"
using assms
proof (induction P \<sigma> rule: match_term_list.induct)
  case (2 x t P \<sigma>)
  have "\<not> (\<sigma> x = None \<or> \<sigma> x = Some t) \<or>
    (\<sigma> x = None \<or> \<sigma> x = Some t) \<and> match_term_list P (\<sigma> (x \<mapsto> t)) = None"
    using "2.prems" by (auto split: if_splits)
  then show ?case
  proof
    assume *: "\<not> (\<sigma> x = None \<or> \<sigma> x = Some t)"
    have "\<not> (\<exists>y. (({#(Var x, t)#}, \<sigma>), y) \<in> matchrel)"
    proof
      presume "\<not> ?thesis"
      then obtain y where "MATCH1 ({#(Var x, t)#}, \<sigma>) y"
        by (auto simp: MATCH1_matchrel_conv)
      then show False using * by (cases) simp_all
    qed simp
    moreover have "(({#(Var x, t)#}, \<sigma>), ({#(Var x, t)#}, \<sigma>)) \<in> matchrel\<^sup>*" by simp
    ultimately have "(({#(Var x, t)#}, \<sigma>), ({#(Var x, t)#}, \<sigma>)) \<in> matchrel\<^sup>!"
      by (metis NF_I normalizability_I)
    from irreducible_reachable_imp_matchers_empty [OF this]
      have "matchers_map \<sigma> \<inter> matchers {(Var x, t)} = {}" by simp
    then show ?case by auto
  next
    presume *: "\<sigma> x = None \<or> \<sigma> x = Some t"
      and "match_term_list P (\<sigma> (x \<mapsto> t)) = None"
    from "2.IH" [OF this] have "matchers_map (\<sigma> (x \<mapsto> t)) \<inter> matchers (set P) = {}" .
    with MATCH1_matchers [OF MATCH1.Var [of \<sigma> x, OF *], of "mset P"]
      show ?case by simp
  qed auto
next
  case (3 f ss g ts P \<sigma>)
  let ?s = "Fun f ss" and ?t = "Fun g ts"
  have "decompose ?s ?t = None \<or>
    decompose ?s ?t = Some (zip ss ts) \<and> match_term_list (zip ss ts @ P) \<sigma> = None"
    using "3.prems" by (auto split: option.splits)
  then show ?case
  proof
    assume "decompose ?s ?t = None"
    then show ?case by auto
  next
    presume "decompose ?s ?t = Some (zip ss ts)"
      and "match_term_list (zip ss ts @ P) \<sigma> = None"
    from "3.IH" [OF this] show ?case by auto
  qed auto
qed simp_all

text \<open>Compute a matching substitution for a list of term pairs @{term P},
where left-hand sides are "patterns" against which the right-hand sides are matched.\<close>
definition match_list ::
  "('v \<Rightarrow> ('f, 'w) term) \<Rightarrow> (('f, 'v) term \<times> ('f, 'w) term) list \<Rightarrow> ('f, 'v, 'w) gsubst option"
  where
    "match_list d P = map_option (subst_of_map d) (match_term_list P Map.empty)"

lemma match_list_sound:
  assumes "match_list d P = Some \<sigma>"
  shows "\<sigma> \<in> matchers (set P)"
  using matchrel_sound [of "mset P"]
    and match_term_list_Some_matchrel [of P Map.empty]
    and assms by (auto simp: match_list_def)

lemma match_list_matches:
  assumes "match_list d P = Some \<sigma>"
  shows "\<And>p t. (p, t) \<in> set P \<Longrightarrow> p \<cdot> \<sigma> = t"
  using match_list_sound [OF assms] by (force simp: matchers_def)

lemma match_list_complete:
  assumes "match_list d P = None"
  shows "matchers (set P) = {}"
  using match_term_list_None [of P Map.empty] and assms by (simp add: match_list_def)

lemma match_list_None_conv:
  "match_list d P = None \<longleftrightarrow> matchers (set P) = {}"
  using match_list_sound [of d P] and match_list_complete [of d P]
  by (metis empty_iff not_None_eq)

definition "match t l = match_list Var [(l, t)]"

lemma match_sound:
  assumes "match t p = Some \<sigma>"
  shows "\<sigma> \<in> matchers {(p, t)}"
  using match_list_sound [of Var "[(p, t)]"] and assms by (simp add: match_def)

lemma match_matches:
  assumes "match t p = Some \<sigma>"
  shows "p \<cdot> \<sigma> = t"
  using match_sound [OF assms] by (force simp: matchers_def)

lemma match_complete:
  assumes "match t p = None"
  shows "matchers {(p, t)} = {}"
  using match_list_complete [of Var "[(p, t)]"] and assms by (simp add: match_def)

definition matches :: "('f, 'w) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "matches t p = (case match_list (\<lambda> _. t) [(p,t)] of None \<Rightarrow> False | Some _ \<Rightarrow> True)"

lemma matches_iff:
  "matches t p \<longleftrightarrow> (\<exists>\<sigma>. p \<cdot> \<sigma> = t)"
  using match_list_sound [of _ "[(p,t)]"]  
  and match_list_complete [of _ "[(p,t)]"]
  unfolding matches_def matchers_def
  by (force simp: split: option.splits)

lemma match_complete':
  assumes "p \<cdot> \<sigma> = t"
  shows "\<exists>\<tau>. match t p = Some \<tau> \<and> (\<forall>x\<in>vars_term p. \<sigma> x = \<tau> x)"
proof -
  from assms have \<sigma>: "\<sigma> \<in> matchers {(p,t)}" by (simp add: matchers_def)
  with match_complete[of t p] 
  obtain \<tau> where match: "match t p = Some \<tau>" by (auto split: option.splits)
  from match_sound[OF this]
  have "\<tau> \<in> matchers {(p, t)}" .
  from matchers_vars_term_eq[OF \<sigma> this] match show ?thesis by auto
qed

abbreviation lvars :: "(('f, 'v) term \<times> ('f, 'w) term) list \<Rightarrow> 'v set"
where
  "lvars P \<equiv> \<Union> ((vars_term \<circ> fst) ` set P)"

lemma match_list_complete':
  assumes "\<And>s t. (s, t) \<in> set P \<Longrightarrow> s \<cdot> \<sigma> = t"
  shows "\<exists>\<tau>. match_list d P = Some \<tau> \<and> (\<forall>x\<in>lvars P. \<sigma> x = \<tau> x)"
proof -
  from assms have "\<sigma> \<in> matchers (set P)" by (force simp: matchers_def)
  moreover with match_list_complete [of d P] obtain \<tau>
    where "match_list d P = Some \<tau>" by auto
  moreover with match_list_sound [of d P]
    have "\<tau> \<in> matchers (set P)"
    by (auto simp: match_def split: option.splits)
  ultimately show ?thesis
    using matchers_vars_term_eq [of \<sigma> "set P" "\<tau>"] by auto
qed

end
