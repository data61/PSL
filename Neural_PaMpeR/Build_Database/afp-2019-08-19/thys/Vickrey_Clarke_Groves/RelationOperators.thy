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


section \<open>Additional operators on relations, going beyond Relations.thy,
  and properties of these operators\<close>

theory RelationOperators
imports
  SetUtils
  "HOL-Library.Code_Target_Nat"

begin

subsection \<open>Evaluating a relation as a function\<close>

text \<open>If an input has a unique image element under a given relation, return that element; 
  otherwise return a fallback value.\<close>
fun eval_rel_or :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b"
  where "eval_rel_or R a z = (let im = R `` {a} in if card im = 1 then the_elem im else z)"

text \<open>right-uniqueness of a relation: the image of a @{const trivial} set (i.e.\ an empty or
  singleton set) under the relation is trivial again. 
This is the set-theoretical way of characterizing functions, as opposed to \<open>\<lambda>\<close> functions.\<close>
definition runiq :: "('a \<times> 'b) set \<Rightarrow> bool" 
  where "runiq R = (\<forall> X . trivial X \<longrightarrow> trivial (R `` X))"

subsection \<open>Restriction\<close>

text \<open>restriction of a relation to a set (usually resulting in a relation with a smaller domain)\<close>
definition restrict :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "||" 75)
  where "R || X = (X \<times> Range R) \<inter> R"

text \<open>extensional characterization of the pairs within a restricted relation\<close>
lemma restrict_ext: "R || X = {(x, y) | x y . x \<in> X \<and> (x, y) \<in> R}"
      unfolding restrict_def using Range_iff by blast

text \<open>alternative statement of @{thm restrict_ext} without explicitly naming the pair's components\<close>
lemma restrict_ext': "R || X = {p . fst p \<in> X \<and> p \<in> R}"
proof -
  have "R || X = {(x, y) | x y . x \<in> X \<and> (x, y) \<in> R}" by (rule restrict_ext)
  also have "\<dots> = { p . fst p \<in> X \<and> p \<in> R }" by force
  finally show ?thesis .
qed

text \<open>Restricting a relation to the empty set yields the empty set.\<close>
lemma restrict_empty: "P || {} = {}" 
      unfolding restrict_def by simp

text \<open>A restriction is a subrelation of the original relation.\<close>
lemma restriction_is_subrel: "P || X \<subseteq> P" 
      using restrict_def by blast

text \<open>Restricting a relation only has an effect within its domain.\<close>
lemma restriction_within_domain: "P || X = P || (X \<inter> (Domain P))" 
      unfolding restrict_def by fast

text \<open>alternative characterization of the restriction of a relation to a singleton set\<close>
lemma restrict_to_singleton: "P || {x} = {x} \<times> (P `` {x})" 
      unfolding restrict_def by fast

subsection \<open>Relation outside some set\<close>

text \<open>For a set-theoretical relation @{term R} and an ``exclusion'' set @{term X}, return those
  tuples of @{term R} whose first component is not in @{term X}.  In other words, exclude @{term X}
  from the domain of @{term R}.\<close>
definition Outside :: "('a \<times> 'b) set \<Rightarrow> 'a set \<Rightarrow> ('a \<times> 'b) set" (infix "outside" 75)
   where "R outside X = R - (X \<times> Range R)"

text \<open>Considering a relation outside some set @{term X} reduces its domain by @{term X}.\<close>
lemma outside_reduces_domain: "Domain (P outside X) = (Domain P) - X"
      unfolding Outside_def by fast

text \<open>Considering a relation outside a singleton set @{term "{x}"} reduces its domain by 
  @{term x}.\<close>
corollary Domain_outside_singleton:
  assumes "Domain R = insert x A"
      and "x \<notin> A"
  shows "Domain (R outside {x}) = A"
  using assms outside_reduces_domain by (metis Diff_insert_absorb)

text \<open>For any set, a relation equals the union of its restriction to that set and its
  pairs outside that set.\<close>
lemma outside_union_restrict: "P = (P outside X) \<union> (P || X)"
      unfolding Outside_def restrict_def by fast

text \<open>The range of a relation @{term R} outside some exclusion set @{term X} is a 
  subset of the image of the domain of @{term R}, minus @{term X}, under @{term R}.\<close>
lemma Range_outside_sub_Image_Domain: "Range (R outside X) \<subseteq> R `` (Domain R - X)"
      using Outside_def Image_def Domain_def Range_def by blast

text \<open>Considering a relation outside some set does not enlarge its range.\<close>
lemma Range_outside_sub:
  assumes "Range R \<subseteq> Y"
  shows "Range (R outside X) \<subseteq> Y"
  using assms outside_union_restrict by (metis Range_mono inf_sup_ord(3) subset_trans)

subsection \<open>Flipping pairs of relations\<close>

text \<open>flipping a pair: exchanging first and second component\<close>
definition flip where "flip tup = (snd tup, fst tup)"

text \<open>Flipped pairs can be found in the converse relation.\<close>
lemma flip_in_conv:
  assumes "tup \<in> R"
  shows "flip tup \<in> R\<inverse>"
  using assms unfolding flip_def by simp

text \<open>Flipping a pair twice doesn't change it.\<close>
lemma flip_flip: "flip (flip tup) = tup"
  by (metis flip_def fst_conv snd_conv surjective_pairing)

text \<open>Flipping all pairs in a relation yields the converse relation.\<close>
lemma flip_conv: "flip ` R = R\<inverse>"
proof -
  have "flip ` R = { flip tup | tup . tup \<in> R }" by (metis image_Collect_mem)
  also have "\<dots> = { tup . tup \<in> R\<inverse> }" using flip_in_conv by (metis converse_converse flip_flip)
  also have "\<dots> = R\<inverse>" by simp
  finally show ?thesis .
qed

subsection \<open>Evaluation as a function\<close>

text \<open>Evaluates a relation @{term R} for a single argument, as if it were a function.
  This will only work if @{term R} is right-unique, i.e. if the image is always a singleton set.\<close>
fun eval_rel :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> 'b" (infix ",," 75) (* . (Mizar's notation) confuses Isar *)
    where "R ,, a = the_elem (R `` {a})"

subsection \<open>Paste\<close>

text \<open>the union of two binary relations @{term P} and @{term Q}, where pairs from @{term Q}
  override pairs from @{term P} when their first components coincide.
This is particularly useful when P, Q are @{term runiq}, and one wants to preserve that property.\<close>
definition paste (infix "+*" 75)
   where "P +* Q = (P outside Domain Q) \<union> Q"

text \<open>If a relation @{term P} is a subrelation of another relation @{term Q} on @{term Q}'s
  domain, pasting @{term Q} on @{term P} is the same as forming their union.\<close>
lemma paste_subrel: 
   assumes "P || Domain Q \<subseteq> Q" 
   shows "P +* Q = P \<union> Q"
   unfolding paste_def using assms outside_union_restrict by blast

text \<open>Pasting two relations with disjoint domains is the same as forming their union.\<close>
lemma paste_disj_domains: 
   assumes "Domain P \<inter> Domain Q = {}" 
   shows "P +* Q = P \<union> Q"
   unfolding paste_def Outside_def using assms by fast

text \<open>A relation @{term P} is equivalent to pasting its restriction to some set @{term X} on 
  @{term "P outside X"}.\<close>
lemma paste_outside_restrict: "P = (P outside X) +* (P || X)"
proof -
  have "Domain (P outside X) \<inter> Domain (P || X) = {}"
    unfolding Outside_def restrict_def by fast
  moreover have "P = P outside X \<union> P || X" by (rule outside_union_restrict)
  ultimately show ?thesis using paste_disj_domains by metis
qed

text \<open>The domain of two pasted relations equals the union of their domains.\<close>
lemma paste_Domain: "Domain(P +* Q)=Domain P\<union>Domain Q" unfolding paste_def Outside_def by blast

text \<open>Pasting two relations yields a subrelation of their union.\<close>
lemma paste_sub_Un: "P +* Q \<subseteq> P \<union> Q" 
  unfolding paste_def Outside_def by fast

text \<open>The range of two pasted relations is a subset of the union of their ranges.\<close>
lemma paste_Range: "Range (P +* Q) \<subseteq> Range P \<union> Range Q"
  using paste_sub_Un by blast
end

