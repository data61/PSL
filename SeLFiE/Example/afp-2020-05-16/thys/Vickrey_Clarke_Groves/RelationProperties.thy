(*
Auction Theory Toolbox (http://formare.github.io/auctions/)

Authors:
* Marco B. Caminati http://caminati.co.nr
* Manfred Kerber <mnfrd.krbr@gmail.com>
* Christoph Lange <math.semantic.web@gmail.com>
* Colin Rowat <c.rowat@bham.ac.uk>

Dually licenced under
* Creative Commons Attribution (CC-BY) 3.0
* ISC License (1-clause BSD License)
See LICENSE file for details
(Rationale for this dual licence: http://arxiv.org/abs/1107.3212)
*)

section \<open>Additional properties of relations, and operators on relations,
  as they have been defined by Relations.thy\<close>

theory RelationProperties
imports
  RelationOperators

begin

subsection \<open>Right-Uniqueness\<close>

(* flip is applied to pairs so that (flip (x, y)) = (y, x) *)
lemma injflip: "inj_on flip A" 
  by (metis flip_flip inj_on_def)

lemma lm01: "card P = card (P^-1)" 
  using card_image flip_conv injflip by metis

lemma cardinalityOneTheElemIdentity: "(card X = 1) = (X={the_elem X})" 
  by (metis One_nat_def card_Suc_eq card_empty empty_iff the_elem_eq)

lemma lm02: "trivial X = (X={} \<or> card X=1)" 
  using cardinalityOneTheElemIdentity order_refl subset_singletonD trivial_def trivial_empty by (metis(no_types))

lemma lm03: "trivial P = trivial (P^-1)" 
  using trivial_def subset_singletonD  subset_refl subset_insertI cardinalityOneTheElemIdentity converse_inject
        converse_empty lm01 
  by metis

(* The range of P restricted to X is equal to the image of X through P *)
lemma restrictedRange: "Range (P||X) = P``X" 
  unfolding restrict_def by blast

lemma doubleRestriction:  "((P || X) || Y) = (P || (X \<inter> Y))" 
  unfolding restrict_def by fast

lemma restrictedDomain: "Domain (R||X) = Domain R \<inter> X" 
  using restrict_def by fastforce

text \<open>A subrelation of a right-unique relation is right-unique.\<close>

lemma subrel_runiq: 
  assumes "runiq Q" "P \<subseteq> Q" 
  shows "runiq P" 
  using assms runiq_def by (metis Image_mono subsetI trivial_subset)

lemma rightUniqueInjectiveOnFirstImplication: 
  assumes "runiq P" 
  shows "inj_on fst P" 
  unfolding inj_on_def 
  using assms runiq_def trivial_def trivial_imp_no_distinct 
        the_elem_eq surjective_pairing subsetI Image_singleton_iff 
  by (metis(no_types))

text \<open>alternative characterization of right-uniqueness: the image of a singleton set is
   @{const trivial}, i.e.\ an empty or a singleton set.\<close>
lemma runiq_alt: "runiq R \<longleftrightarrow> (\<forall> x . trivial (R `` {x}))" 
  unfolding runiq_def by (metis Image_empty2 trivial_empty_or_singleton trivial_singleton) 
 
text \<open>an alternative definition of right-uniqueness in terms of @{const eval_rel}\<close>
(* Note that R `` {x} is the image of {x} under R and R ,, x gives you an element y such that R x y. Because of right-uniqueness in this case the element is determined, otherwise it may be undetermined *)
lemma runiq_wrt_eval_rel: "runiq R = (\<forall>x . R `` {x} \<subseteq> {R ,, x})" 
  by (metis eval_rel.simps runiq_alt trivial_def)

lemma rightUniquePair: 
  assumes "runiq f" 
  assumes "(x,y)\<in>f" 
  shows "y=f,,x" 
  using assms runiq_wrt_eval_rel subset_singletonD Image_singleton_iff equals0D singletonE 
  by fast

lemma runiq_basic: "runiq R \<longleftrightarrow> (\<forall> x y y' . (x, y) \<in> R \<and> (x, y') \<in> R \<longrightarrow> y = y')" 
  unfolding runiq_alt trivial_same by blast

lemma rightUniqueFunctionAfterInverse: 
  assumes "runiq f" 
  shows "f``(f^-1``Y) \<subseteq> Y" 
  using assms runiq_basic ImageE converse_iff subsetI by (metis(no_types))

lemma lm04: 
  assumes "runiq f" "y1 \<in> Range f" 
  shows "(f^-1 `` {y1} \<inter> f^-1 `` {y2} \<noteq> {}) = (f^-1``{y1}=f^-1``{y2})"
  using assms rightUniqueFunctionAfterInverse by fast

lemma converse_Image: 
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R^-1)"
  shows "(R^-1) `` R `` X \<subseteq> X" 
  using assms by (metis converse_converse rightUniqueFunctionAfterInverse)

lemma lm05: 
  assumes "inj_on fst P" 
  shows "runiq P" 
  unfolding runiq_basic 
  using assms fst_conv inj_on_def old.prod.inject 
  by (metis(no_types))

(* Another characterization of runiq, relating the set theoretical expression P to the injectivity of the function fst applied to P *)
lemma rightUniqueInjectiveOnFirst: "(runiq P) = (inj_on fst P)" 
  using rightUniqueInjectiveOnFirstImplication lm05 by blast

lemma disj_Un_runiq: 
  assumes "runiq P" "runiq Q" "(Domain P) \<inter> (Domain Q) = {}" 
  shows "runiq (P \<union> Q)" 
  using assms rightUniqueInjectiveOnFirst fst_eq_Domain injection_union by metis

lemma runiq_paste1: 
  assumes "runiq Q" "runiq (P outside Domain Q)" 
  shows "runiq (P +* Q)"
  unfolding paste_def 
  using assms disj_Un_runiq Diff_disjoint Un_commute outside_reduces_domain
  by (metis (poly_guards_query))

corollary runiq_paste2: 
  assumes "runiq Q" "runiq P" 
  shows "runiq (P +* Q)"
  using assms runiq_paste1 subrel_runiq Diff_subset Outside_def 
  by (metis)

(* Let f be a function, then its graph {(x, f x)} and all its restrictions such that P x for arbitrary P are right-unique. *)
lemma rightUniqueRestrictedGraph: "runiq {(x,f x)| x. P x}" 
  unfolding runiq_basic by fast

lemma rightUniqueSetCardinality: 
  assumes "x \<in> Domain R" "runiq R" 
  shows "card (R``{x})=1"
  using assms  lm02 DomainE Image_singleton_iff empty_iff
  by (metis runiq_alt)


text \<open>The image of a singleton set under a right-unique relation is a singleton set.\<close>
lemma Image_runiq_eq_eval: 
  assumes "x \<in> Domain R" "runiq R" 
  shows "R `` {x} = {R ,, x}" 
  using assms rightUniqueSetCardinality
  by (metis eval_rel.simps cardinalityOneTheElemIdentity)

lemma lm06: 
  assumes "trivial f" 
  shows "runiq f" 
  using assms trivial_subset_non_empty runiq_basic snd_conv
  by fastforce

text \<open>A singleton relation is right-unique.\<close>
corollary runiq_singleton_rel: "runiq {(x, y)}" 
  using trivial_singleton lm06 by fast

text \<open>The empty relation is right-unique\<close>
lemma runiq_emptyrel: "runiq {}" 
  using trivial_empty lm06 by blast

(* characterization of right-uniqueness with  \<exists>! *)
lemma runiq_wrt_ex1:
  "runiq R \<longleftrightarrow> (\<forall> a \<in> Domain R . \<exists>! b . (a, b) \<in> R)"
  using runiq_basic by (metis Domain.DomainI Domain.cases)

text \<open>alternative characterization of the fact that, if a relation @{term R} is right-unique,
  its evaluation @{term "R,,x"} on some argument @{term x} in its domain, occurs in @{term R}'s
  range. Note that we need runiq R in order to get a definite value for @{term "R,,x"}\<close>
lemma eval_runiq_rel:
  assumes domain: "x \<in> Domain R"
      and runiq: "runiq R" 
  shows "(x, R,,x) \<in> R"
  using assms by (metis rightUniquePair runiq_wrt_ex1)

text \<open>Evaluating a right-unique relation as a function on the relation's domain yields an
  element from its range.\<close>
lemma eval_runiq_in_Range:
  assumes "runiq R"
      and "a \<in> Domain R"
  shows "R ,, a \<in> Range R"
  using assms by (metis Range_iff eval_runiq_rel)





subsection \<open>Converse\<close>

text \<open>The inverse image of the image of a singleton set under some relation is the same
  singleton set, if both the relation and its converse are right-unique and the singleton set
  is in the relation's domain.\<close>
lemma converse_Image_singleton_Domain:
  assumes runiq: "runiq R"
      and runiq_conv: "runiq (R\<inverse>)"
      and domain: "x \<in> Domain R"
  shows "R\<inverse> `` R `` {x} = {x}"
proof -
  have sup: "{x} \<subseteq> R\<inverse> `` R `` {x}" using domain by fast
  have "trivial (R `` {x})" using runiq domain by (metis runiq_def trivial_singleton)
  then have "trivial (R\<inverse> `` R `` {x})"
    using assms runiq_def by blast
  then show ?thesis
    using sup by (metis singleton_sub_trivial_uniq subset_antisym trivial_def)
qed

text \<open>The images of two disjoint sets under an injective function are disjoint.\<close>

lemma disj_Domain_imp_disj_Image: 
  assumes "Domain R \<inter> X \<inter> Y = {}" 
  assumes "runiq R"
      and "runiq (R\<inverse>)"
  shows "(R `` X) \<inter> (R `` Y) = {}" 
  using assms unfolding runiq_basic by blast

lemma runiq_converse_paste_singleton: 
  assumes "runiq (P^-1)" "y\<notin>(Range P)" 
  shows "runiq ((P +* {(x,y)})\<inverse>)" 
  (is "?u (?P^-1)")
proof -
  have "(?P) \<subseteq> P \<union> {(x,y)}" using assms by (metis paste_sub_Un)
  then have "?P^-1 \<subseteq> P^-1 \<union> ({(x,y)}^-1)" by blast
  moreover have "... = P^-1 \<union> {(y,x)}" by fast
  moreover have "Domain (P^-1) \<inter> Domain {(y,x)} = {}" using assms(2) by auto
  ultimately moreover have "?u (P^-1 \<union> {(y,x)})" using assms(1) by (metis disj_Un_runiq runiq_singleton_rel)
  ultimately show ?thesis by (metis subrel_runiq)
qed










subsection \<open>Injectivity\<close>

text \<open>The following is a classical definition of the set of all injective functions from @{term X} to @{term Y}.\<close>
definition injections :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<times> 'b) set set"
  where "injections X Y = {R . Domain R = X \<and> Range R \<subseteq> Y \<and> runiq R \<and> runiq (R\<inverse>)}"

text \<open>The following definition is a constructive (computational) characterization of the set of all injections X Y, represented by a list. That is, we define the list of all injective functions (represented as relations) from one set (represented as a list) to another set. We formally prove the equivalence of the constructive and the classical definition in Universes.thy.\<close>
fun injections_alg (* :: "'a list \<Rightarrow> 'b::linorder set \<Rightarrow> ('a \<times> 'b) set list" *)
  where "injections_alg [] Y = [{}]" |
        "injections_alg (x # xs) Y = concat [ [ R +* {(x,y)} . y \<leftarrow> sorted_list_of_set (Y - Range R) ]
       . R \<leftarrow> injections_alg xs Y ]"
(* We need this as a list in order to be able to iterate over it.  It would be easy to provide 
   an alternative of type ('a \<times> 'b) set set, by using \<Union> and set comprehension. *)

lemma Image_within_domain': 
  fixes x R 
  shows "(x \<in> Domain R) = (R `` {x} \<noteq> {})" 
  by blast

end

