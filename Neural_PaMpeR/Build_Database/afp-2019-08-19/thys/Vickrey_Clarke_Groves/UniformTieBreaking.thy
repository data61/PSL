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

section \<open>Termination theorem for uniform tie-breaking\<close>

theory UniformTieBreaking

imports 
StrictCombinatorialAuction
Universes
"HOL-Library.Code_Target_Nat"

begin


subsection \<open>Uniform tie breaking: definitions\<close>
text\<open>Let us repeat the general context. Each bidder has made their bids and the VCG algorithm up
 to now allocates goods to the higher bidders. If there are several high bidders tie breaking has 
to take place. To do tie breaking we generate out of a random number a second bid vector so that 
the same algorithm can be run again to determine a unique allocation.

To this end, we associate to each allocation the bid in which each participant bids for a set 
of goods an amount equal to the cardinality of the intersection of the bid with the set 
she gets in this allocation.
By construction, the revenue of an auction run using this bid is maximal on the given allocation,
and this maximal is unique.
We can then use the bid constructed this way @{term tiebids} to break ties by running an auction 
having the same form as a normal auction (that is why we use the adjective ``uniform''), 
only with this special bid vector.\<close>

(* omega pair is a tool to compute cardinalities of pairs, e.g. for a pair made of a participant 1 and a set of goods {11,12,13}, the result will be the set of pairs: {(1,{11}), (1,{12}), (1,{13})}.
*)
abbreviation "omega pair == {fst pair} \<times> (finestpart (snd pair))"

(* pseudo allocation is like an allocation, but without uniqueness of the elements allocated *)
definition "pseudoAllocation allocation == \<Union> (omega ` allocation)"

(* some abbreviation to defined tiebids below *)
abbreviation "bidMaximizedBy allocation N G == 
              pseudoAllocation allocation <|| ((N \<times> (finestpart G)))"
(* functional version of the above *)
abbreviation "maxbid a N G == 
              toFunction (bidMaximizedBy a N G)"

(* For bidding the cardinality of the second element of a single pair, i.e.,
   (bidder, goods) \<rightarrow> ((bidder, goods), bid) *)
abbreviation "summedBid bids pair == 
              (pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair)))"

(* returns just the bid in the above *)
abbreviation "summedBidSecond bids pair == 
              sum (%g. bids (fst pair, g)) (finestpart (snd pair))"

(* apply summedBid to each possible pair *)
abbreviation "summedBidVectorRel bids N G == (summedBid bids) ` (N \<times> (Pow G - {{}}))"

(* functional version of above *)
abbreviation "summedBidVector bids N G == toFunction (summedBidVectorRel bids N G)"

(* tiebids returns a bid vector that when the VCG algorithm runs on it yields the singleton {allocation}. Functional version *)
abbreviation "tiebids allocation N G == summedBidVector (maxbid allocation N G) N G"

(* relational version of the above *)
abbreviation "Tiebids allocation N G == summedBidVectorRel (real\<circ>maxbid allocation N G) N G"

(* Assumed we have a list and a random we take the random-th element of the list. However, if the
   random number is bigger than the list is long we take it modulo the length of the list *)
definition "randomEl list (random::integer) = list ! ((nat_of_integer random) mod (size list))"

value "nat_of_integer (-3::integer) mod 2"

(* The randomEl taken out of a list is in the list *)
lemma randomElLemma:
   assumes "set list \<noteq> {}"
   shows "randomEl list random \<in> set list"
   using assms by (simp add: randomEl_def)

(* The chosen allocation takes the random-th element of all possible winning allocations. This is
   done by taking the element given by randomEl list random defined above. *)
abbreviation "chosenAllocation N G bids random == 
   randomEl (takeAll (%x. x\<in>(winningAllocationsRel N (set G) bids)) 
                     (allAllocationsAlg N G)) 
            random"

(* find the bid vector in random values that returns the chosen winning allocation *)
abbreviation "resolvingBid N G bids random == 
  tiebids (chosenAllocation N G bids random) N (set G)"

subsection \<open>Termination theorem for the uniform tie-breaking scheme\<close>

corollary winningAllocationPossible: 
  "winningAllocationsRel N G b \<subseteq> allAllocations N G" 
  using injectionsFromEmptyAreEmpty mem_Collect_eq subsetI by auto

lemma subsetAllocation: 
  assumes "a \<in> allocationsUniverse" "c \<subseteq> a" 
  shows "c \<in> allocationsUniverse"  
proof - 
  have "c=a-(a-c)" using assms(2) by blast 
  thus ?thesis using assms(1) reducedAllocation by (metis (no_types)) 
qed

lemma lm001: 
  assumes "a \<in> allocationsUniverse" 
  shows "a outside X \<in> allocationsUniverse"
  using assms reducedAllocation Outside_def by (metis (no_types))

corollary lm002: 
  "{x}\<times>({X}-{{}}) \<in> allocationsUniverse" 
  using allocationUniverseProperty pairDifference by metis

(* TPTP? *)
corollary lm003: 
  "{(x,{y})} \<in> allocationsUniverse" 
proof -
  have "\<And>x1. {} - {x1::'a \<times> 'b set} = {}" by simp
  thus "{(x, {y})} \<in> allocationsUniverse" 
  by (metis (no_types) allocationUniverseProperty empty_iff insert_Diff_if insert_iff prod.inject)
qed

corollary lm004: 
  "allocationsUniverse \<noteq> {}" 
  using lm003 by fast

corollary lm005:
  "{} \<in> allocationsUniverse" 
  using subsetAllocation lm003 by (metis (lifting, mono_tags) empty_subsetI)

lemma lm006: 
  assumes "G \<noteq> {}" 
  shows "{G} \<in> all_partitions G" 
  using all_partitions_def is_partition_of_def is_non_overlapping_def assms by force

lemma lm007: 
  assumes "n \<in> N" 
  shows "{(G,n)} \<in> totalRels {G} N" 
  using assms by force

lemma lm008: 
  assumes "n\<in>N" 
  shows "{(G,n)} \<in> injections {G} N" 
  using assms injections_def singlePairInInjectionsUniverse by fastforce

corollary lm009: 
  assumes " G\<noteq>{}" "n\<in>N" 
  shows "{(G,n)} \<in> possible_allocations_rel G N"
proof -
  have "{(G,n)} \<in> injections {G} N" using assms lm008 by fast
  moreover have "{G} \<in> all_partitions G" using assms lm006 by metis
  ultimately show ?thesis by auto
qed

corollary lm010: 
  assumes "N \<noteq> {}" "G\<noteq>{}" 
  shows "allAllocations N G \<noteq> {}"
  using assms lm009
  by (metis (hide_lams, no_types) equals0I image_insert insert_absorb insert_not_empty)

corollary lm011: 
  assumes "N \<noteq> {}" "finite N" "G \<noteq> {}" "finite G" 
  shows "winningAllocationsRel N G bids \<noteq> {} & finite (winningAllocationsRel N G bids)" 
  using assms lm010 allAllocationsFinite argmax_non_empty_iff 
  by (metis winningAllocationPossible rev_finite_subset)

lemma lm012: 
  "allAllocations N {} \<subseteq> {{}}" 
  using emptyset_part_emptyset3 rangeEmpty characterizationallAllocations
        mem_Collect_eq subsetI vimage_def by metis

lemma lm013: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "finite (Range a)" 
  using assms elementOfPartitionOfFiniteSetIsFinite by (metis allocationReverseInjective)

corollary allocationFinite: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "finite a"
  using assms finite_converse Range_converse imageE allocationProperty finiteDomainImpliesFinite lm013
  by (metis (erased, lifting))

lemma lm014: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "\<forall> y \<in> Range a. finite y" 
  using assms is_partition_of_def allocationInverseRangeDomainProperty
  by (metis Union_upper rev_finite_subset)

(* Note that allocations are strict, that is, all goods are allocated to the bidders at this point. Later we will have the seller as participant 0 getting all goods not allocated *)
corollary lm015: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "card G = sum card (Range a)" 
  using assms cardSumCommute lm013 allocationInverseRangeDomainProperty by (metis is_partition_of_def)



subsection \<open>Results on summed bid vectors\<close>

lemma lm016: 
  "summedBidVectorRel bids N G = 
   {(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair)))|
    pair. pair \<in> N \<times> (Pow G-{{}})}" 
  by blast

(* Note that || stands for restriction, here to an allocation a *)
corollary lm017: 
  "{(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G-{{}})) } || a = 
   {(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G-{{}}))   \<inter>  a}"
  by (metis restrictionVsIntersection)

corollary lm018: 
  "(summedBidVectorRel bids N G) || a = 
   {(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
    pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
   (is "?L = ?R")
proof -
  let ?l = summedBidVectorRel
  let ?M = "{(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
             pair. pair \<in> N \<times> (Pow G-{{}})}"
  have "?l bids N G = ?M" by (rule lm016)
  then have "?L = (?M || a)" by presburger
  moreover have "... = ?R" by (rule lm017)
  ultimately show ?thesis by simp
qed

lemma lm019: 
  "(summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a) = 
   {(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) | 
    pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
  by blast

corollary lm020: 
  "(summedBidVectorRel bids N G) || a = (summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a)"
  (is "?L=?R")
proof -
  let ?l=summedBidVectorRel 
  let ?p=summedBid 
  let ?M="{(pair, sum (%g. bids (fst pair, g)) (finestpart (snd pair))) |
           pair. pair \<in> (N \<times> (Pow G - {{}})) \<inter> a}"
  have "?L = ?M" by (rule lm018)
  moreover have "... = ?R" using lm019 by blast
  ultimately show ?thesis by simp
qed

(* the function made by (summedBid bids) is always injective, that is, also with domain UNIV *)
lemma summedBidInjective: 
  "inj_on (summedBid bids) UNIV" 
  using fst_conv inj_on_inverseI by (metis (lifting)) 

(* restrict above to any set X *)
corollary lm021: 
  "inj_on (summedBid bids) X" 
  using fst_conv inj_on_inverseI by (metis (lifting))

(* relationship between different formalizations of summedBid *)
lemma lm022: 
  "sum snd (summedBidVectorRel bids N G) = 
   sum (snd \<circ> (summedBid bids)) (N \<times> (Pow G - {{}}))" 
  using lm021 sum.reindex by blast 

(* remember: omega of (1,{11,12,13}) is {(1,{11}), (1,{12}), (1,{13})} *)
corollary lm023: 
  "snd (summedBid bids pair) = sum bids (omega pair)" 
  using sumCurry by force

(* restatement of the above *)
corollary lm024: 
  "snd \<circ> summedBid bids = (sum bids) \<circ> omega" 
  using lm023 by fastforce

lemma lm025: 
  assumes "finite  (finestpart (snd pair))" 
  shows "card (omega pair) = card (finestpart (snd pair))" 
  using assms by force

corollary lm026:
  assumes "finite (snd pair)" 
  shows "card (omega pair) = card (snd pair)" 
  using assms cardFinestpart card_cartesian_product_singleton by metis

lemma lm027: 
  assumes "{} \<notin> Range f" "runiq f"
  shows "is_non_overlapping (omega ` f)"
proof -
let ?X="omega ` f" let ?p=finestpart
  { fix y1 y2
    assume "y1 \<in> ?X \<and> y2 \<in> ?X"
    then obtain pair1 pair2 where 
      "y1 = omega pair1 & y2 = omega pair2 & pair1 \<in> f & pair2 \<in> f" by blast
    then moreover have "snd pair1 \<noteq> {} & snd pair1 \<noteq> {}" 
      using assms by (metis rev_image_eqI snd_eq_Range)
    ultimately moreover have "fst pair1 = fst pair2 \<longleftrightarrow> pair1 = pair2" 
      using assms runiq_basic surjective_pairing by metis
    ultimately moreover have "y1 \<inter> y2 \<noteq> {} \<longrightarrow> y1 = y2" using assms by fast
    ultimately have "y1 = y2 \<longleftrightarrow> y1 \<inter> y2 \<noteq> {}" 
      using assms notEmptyFinestpart by (metis Int_absorb Times_empty insert_not_empty)
    }
  thus ?thesis using is_non_overlapping_def 
    by (metis (lifting, no_types) inf_commute inf_sup_aci(1))
qed

lemma lm028: 
  assumes "{} \<notin> Range X" 
  shows "inj_on omega X"
proof -
  let ?p=finestpart
  {
    fix pair1 pair2 
    assume "pair1 \<in> X & pair2 \<in> X" 
    then have "snd pair1 \<noteq> {} & snd pair2 \<noteq> {}" 
      using assms by (metis Range.intros surjective_pairing)
    moreover assume "omega pair1 = omega pair2" 
    then moreover have "?p (snd pair1) = ?p (snd pair2)" by blast
    then moreover have "snd pair1 = snd pair2" by (metis finestPart nonEqualitySetOfSets)
    ultimately moreover have "{fst pair1} = {fst pair2}" using notEmptyFinestpart 
      by (metis fst_image_times)
    ultimately have "pair1 = pair2" by (metis prod_eqI singleton_inject)
  }
  thus ?thesis by (metis (lifting, no_types) inj_onI)
qed

lemma lm029: 
  assumes "{} \<notin> Range a" "\<forall>X \<in> omega ` a. finite X" 
          "is_non_overlapping (omega ` a)"
  shows "card (pseudoAllocation a) = sum (card \<circ> omega) a" 
  (is "?L = ?R")
proof -
  have "?L = sum card (omega ` a)" 
  unfolding pseudoAllocation_def
  using assms by (simp add: cardinalityPreservation)
  moreover have "... = ?R" using assms(1) lm028 sum.reindex by blast
  ultimately show ?thesis by simp
qed

lemma lm030: 
  "card (omega pair)= card (snd pair)" 
  using cardFinestpart card_cartesian_product_singleton by metis

corollary lm031: 
  "card \<circ> omega = card \<circ> snd" 
  using lm030 by fastforce

(* set image of omega on a set of pair is called pseudoAllocation *)
corollary lm032: 
  assumes "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" "finite a" "runiq a" 
  shows "card (pseudoAllocation a) = sum (card \<circ> snd) a"
proof -
  let ?P=pseudoAllocation 
  let ?c=card
  have "\<forall> pair \<in> a. finite (omega pair)" using finiteFinestpart assms by blast 
  moreover have "is_non_overlapping (omega ` a)" using assms lm027 by force 
  ultimately have "?c (?P a) = sum (?c \<circ> omega) a" using assms lm029 by force
  moreover have "... = sum (?c \<circ> snd) a" using lm031 by metis
  ultimately show ?thesis by simp
qed

corollary lm033: 
  assumes "runiq (a^-1)" "runiq a" "finite a" "{} \<notin> Range a" "\<forall> pair \<in> a. finite (snd pair)" 
  shows "card (pseudoAllocation a) = sum card (Range a)" 
  using assms sumPairsInverse lm032 by force

corollary lm034: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "card (pseudoAllocation a) = card G"
proof -
  have "{} \<notin> Range a" using assms by (metis emptyNotInRange)
  moreover have "\<forall> pair \<in> a. finite (snd pair)" using assms lm014 finitePairSecondRange by metis
  moreover have "finite a" using assms allocationFinite by blast
  moreover have "runiq a" using assms 
    by (metis (lifting) Int_lower1 in_mono allocationInjectionsUnivervseProperty mem_Collect_eq)
  moreover have "runiq (a^-1)" using assms 
    by (metis (mono_tags) injections_def characterizationallAllocations mem_Collect_eq)
  ultimately have "card (pseudoAllocation a) = sum card (Range a)" using lm033 by fast
  moreover have "... = card G" using assms lm015 by metis
  ultimately show ?thesis by simp
qed

corollary lm035: 
  assumes "pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" 
          "finite (pseudoAllocation aa)"
  shows "sum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation a) - 
            (sum (toFunction (bidMaximizedBy a N G)) (pseudoAllocation aa)) = 
         card (pseudoAllocation a) - 
            card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
  using assms subsetCardinality by blast

corollary lm036: 
  assumes "pseudoAllocation aa \<subseteq> pseudoAllocation a \<union> (N \<times> (finestpart G))" 
          "finite (pseudoAllocation aa)"
  shows "int (sum (maxbid a N G) (pseudoAllocation a)) - 
           int (sum (maxbid a N G) (pseudoAllocation aa)) = 
         int (card (pseudoAllocation a)) - 
           int (card (pseudoAllocation aa \<inter> (pseudoAllocation a)))" 
  using differenceSumVsCardinality assms by blast

lemma lm037: 
  "pseudoAllocation {} = {}" 
  unfolding pseudoAllocation_def by simp

corollary lm038: 
  assumes "a \<in> allAllocations N {}" 
  shows "(pseudoAllocation a) = {}"
  unfolding pseudoAllocation_def using assms lm012 by blast

corollary lm039: 
  assumes "a \<in> allAllocations N G" "finite G" "G \<noteq> {}"
  shows "finite (pseudoAllocation a)" 
proof -
  have "card (pseudoAllocation a) = card G" using assms(1,2) lm034 by blast
  thus "finite (pseudoAllocation a)" using assms(2,3) by fastforce
qed

corollary lm040: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "finite (pseudoAllocation a)" 
  using assms finite.emptyI lm039 lm038 by (metis (no_types))

lemma lm041: 
  assumes "a \<in> allAllocations N G" "aa \<in> allAllocations N G" "finite G" 
  shows  "(card (pseudoAllocation aa \<inter> (pseudoAllocation a)) = card (pseudoAllocation a)) = 
          (pseudoAllocation a = pseudoAllocation aa)" 
proof -
  let ?P=pseudoAllocation 
  let ?c=card 
  let ?A="?P a" 
  let ?AA="?P aa"
  have "?c ?A=?c G & ?c ?AA=?c G" using assms lm034 by (metis (lifting, mono_tags))
  moreover have "finite ?A & finite ?AA" using assms lm040 by blast
  ultimately show ?thesis using assms cardinalityIntersectionEquality by (metis(no_types,lifting))
qed

(* alternative definition for omega *)
lemma lm042: 
  "omega pair = {fst pair} \<times> {{y}| y. y \<in> snd pair}" 
  using finestpart_def finestPart by auto

(* variant of above *)
lemma lm043: 
  "omega pair = {(fst pair, {y})| y. y \<in>  snd pair}" 
  using lm042 setOfPairs by metis

lemma lm044: 
  "pseudoAllocation a = \<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a}"
  unfolding pseudoAllocation_def using lm043 by blast

lemma lm045: 
  "\<Union> {{(fst pair, {y})| y. y \<in> snd pair}| pair. pair \<in> a} = 
   {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}"
  by blast

corollary lm046: 
  "pseudoAllocation a = {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a}"
  unfolding pseudoAllocation_def using setOfPairsEquality by fastforce

lemma lm047: 
  assumes "runiq a" 
  shows "{(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> a} = 
         {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
         (is "?L=?R") 
  using assms Domain.DomainI fst_conv functionOnFirstEqualsSecond runiq_wrt_ex1 surjective_pairing
  by (metis(hide_lams,no_types))

corollary lm048: 
  assumes "runiq a" 
  shows "pseudoAllocation a = {(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
  unfolding pseudoAllocation_def using assms lm047 lm046 by fastforce

corollary lm049: 
  "Range (pseudoAllocation a) = \<Union> (finestpart ` (Range a))"
  unfolding pseudoAllocation_def
  using lm046 rangeSetOfPairs unionFinestPart  by fastforce

corollary lm050: 
  "Range (pseudoAllocation a) = finestpart (\<Union> (Range a))" 
  using commuteUnionFinestpart lm049 by metis 

lemma lm051: 
  "pseudoAllocation a = {(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" 
  using lm044 lm045 by (metis (no_types))

lemma lm052: 
  "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a} = 
   {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}"
   by auto

lemma lm053: 
  "pseudoAllocation a = {(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a}"
  (is "?L=?R")
proof -
  have "?L={(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> a}" by (rule lm051)
  moreover have "... = ?R" by (rule lm052) 
  ultimately show ?thesis by simp
qed

lemma lm054: 
  "runiq (summedBidVectorRel bids N G)" 
  using graph_def image_Collect_mem domainOfGraph by (metis(no_types))

corollary lm055: 
  "runiq (summedBidVectorRel bids N G || a)"
  unfolding restrict_def using lm054 subrel_runiq Int_commute by blast

lemma summedBidVectorCharacterization: 
  "N \<times> (Pow G - {{}}) = Domain (summedBidVectorRel bids N G)" 
  by blast

corollary lm056: 
  assumes "a \<in> allAllocations N G" 
  shows "a \<subseteq> Domain (summedBidVectorRel bids N G)"
proof -
  let ?p=allAllocations 
  let ?L=summedBidVectorRel
  have "a \<subseteq> N \<times> (Pow G - {{}})" using assms allocationPowerset by (metis(no_types))
  moreover have "N \<times> (Pow G - {{}}) = Domain (?L bids N G)" using summedBidVectorCharacterization by blast
  ultimately show ?thesis by blast
qed

corollary lm057: 
  "sum (summedBidVector bids N G) (a \<inter> (Domain (summedBidVectorRel bids N G))) = 
   sum snd ((summedBidVectorRel bids N G) || a)" 
  using sumRestrictedToDomainInvariant lm055 by fast

corollary lm058: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = sum snd ((summedBidVectorRel bids N G) || a)" 
proof -
  let ?l=summedBidVector let ?L=summedBidVectorRel
  have "a \<subseteq> Domain (?L bids N G)" using assms by (rule lm056) 
  then have "a = a \<inter> Domain (?L bids N G)" by blast 
  then have "sum (?l bids N G) a = sum (?l bids N G) (a \<inter> Domain (?L bids N G))" 
       by presburger
  thus ?thesis using lm057 by auto
qed

corollary lm059: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = 
         sum snd ((summedBid bids) ` ((N \<times> (Pow G - {{}})) \<inter> a))"
        (is "?X=?R")
proof -
  let ?p = summedBid 
  let ?L = summedBidVectorRel 
  let ?l = summedBidVector
  let ?A = "N \<times> (Pow G - {{}})" 
  let ?inner2 = "(?p bids)`(?A \<inter> a)" 
  let ?inner1 = "(?L bids N G)||a"
  have "?R = sum snd ?inner1" using assms lm020 by (metis (no_types))
  moreover have "sum (?l bids N G) a = sum snd ?inner1" using assms by (rule lm058)
  ultimately show ?thesis by simp
qed

corollary lm060: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = sum snd ((summedBid bids) ` a)" 
  (is "?L=?R")
proof -
  let ?p=summedBid 
  let ?l=summedBidVector
  have "?L = sum snd ((?p bids)`((N \<times> (Pow G - {{}}))\<inter> a))" using assms by (rule lm059)
  moreover have "... = ?R" using assms allocationPowerset Int_absorb1 by (metis (no_types))
  ultimately show ?thesis by simp
qed

corollary lm061: 
  "sum snd ((summedBid bids) ` a) = sum (snd \<circ> (summedBid bids)) a"
  using sum.reindex lm021 by blast

corollary lm062: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = sum (snd \<circ> (summedBid bids)) a" 
  (is "?L=?R")
proof -
  let ?p = summedBid 
  let ?l = summedBidVector
  have "?L = sum snd ((?p bids)` a)" using assms by (rule lm060)
  moreover have "... = ?R" using assms lm061 by blast
  ultimately show ?thesis by simp
qed

corollary lm063: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = sum ((sum bids) \<circ> omega) a" 
  (is "?L=?R") 
proof -
  let ?inner1 = "snd \<circ> (summedBid bids)" 
  let ?inner2="(sum bids) \<circ> omega"
  let ?M="sum ?inner1 a"
  have "?L = ?M" using assms by (rule lm062)
  moreover have "?inner1 = ?inner2" using lm023 assms by fastforce
  ultimately show "?L = ?R" using assms by metis
qed

corollary lm064: 
  assumes "a \<in> allAllocations N G" 
  shows "sum (summedBidVector bids N G) a = sum (sum bids) (omega` a)"
proof -
  have "{} \<notin> Range a" using assms by (metis emptyNotInRange)
  then have "inj_on omega a" using lm028 by blast
  then have "sum (sum bids) (omega ` a) = sum ((sum bids) \<circ> omega) a" 
       by (rule sum.reindex)
  moreover have "sum (summedBidVector bids N G) a = sum ((sum bids) \<circ> omega) a"
       using assms lm063 by (rule Extraction.exE_realizer)
  ultimately show ?thesis by presburger
qed

lemma lm065: 
  assumes "finite (snd pair)" 
  shows "finite (omega pair)" 
  using assms finite.emptyI finite.insertI finite_SigmaI finiteFinestpart  by (metis(no_types))

corollary lm066: 
  assumes "\<forall>y\<in>(Range a). finite y" 
  shows "\<forall>y\<in>(omega ` a). finite y"
  using assms lm065 imageE finitePairSecondRange by fast

corollary lm067: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "\<forall>x\<in>(omega ` a). finite x" 
  using assms lm066 lm014 by (metis(no_types))

corollary lm068: 
  assumes "a \<in> allAllocations N G" 
  shows "is_non_overlapping (omega ` a)"
proof -
  have "runiq a" by (metis (no_types) assms image_iff allocationRightUniqueRangeDomain)
  moreover have "{} \<notin> Range a" using assms by (metis emptyNotInRange)
  ultimately show ?thesis using lm027 by blast
qed

lemma lm069: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "sum (sum bids) (omega` a) = sum bids (\<Union> (omega ` a))" 
  using assms sumUnionDisjoint2 lm068 lm067 by (metis (lifting, mono_tags))

corollary lm070: 
  assumes "a \<in> allAllocations N G" "finite G" 
  shows "sum (summedBidVector bids N G) a = sum bids (pseudoAllocation a)" 
  (is "?L = ?R")
proof -
  have "?L = sum (sum bids) (omega `a)" using assms lm064 by blast
  moreover have "... = sum bids (\<Union> (omega ` a))" using assms lm069 by blast
  ultimately show ?thesis unfolding pseudoAllocation_def by presburger
qed

lemma lm071: 
  "Domain (pseudoAllocation a) \<subseteq> Domain a"
  unfolding pseudoAllocation_def by fastforce

corollary lm072: 
  assumes "a \<in> allAllocations N G" 
  shows "Domain (pseudoAllocation a) \<subseteq> N   &   Range (pseudoAllocation a) = finestpart G" 
  using assms lm071 allocationInverseRangeDomainProperty lm050 is_partition_of_def subset_trans 
  by (metis(no_types))

corollary lm073: 
  assumes "a \<in> allAllocations N G" 
  shows "pseudoAllocation a \<subseteq> N \<times> finestpart G"
proof -
  let ?p = pseudoAllocation 
  let ?aa = "?p a" 
  let ?d = Domain 
  let ?r = Range
  have "?d ?aa \<subseteq> N" using assms lm072 by (metis (lifting, mono_tags))
  moreover have "?r ?aa \<subseteq> finestpart G" using assms lm072 by (metis (lifting, mono_tags) equalityE)
  ultimately have "?d ?aa \<times> (?r ?aa) \<subseteq> N \<times> finestpart G" by auto
  then show "?aa \<subseteq> N \<times> finestpart G" by auto
qed








subsection \<open>From Pseudo-allocations to allocations\<close>

(* pseudoAllocationInv inverts pseudoAllocation *)
abbreviation "pseudoAllocationInv pseudo == {(x, \<Union> (pseudo `` {x}))| x. x \<in> Domain pseudo}"
 
lemma lm074: 
  assumes "runiq a" "{} \<notin> Range a" 
  shows "a = pseudoAllocationInv (pseudoAllocation a)"
proof -
  let ?p="{(x, Y)| Y x. Y \<in> finestpart (a,,x) & x \<in> Domain a}"
  let ?a="{(x, \<Union> (?p `` {x}))| x. x \<in> Domain ?p}" 
  have "\<forall>x \<in> Domain a. a,,x \<noteq> {}" by (metis assms eval_runiq_in_Range)
  then have "\<forall>x \<in> Domain a. finestpart (a,,x) \<noteq> {}" by (metis notEmptyFinestpart) 
  then have "Domain a \<subseteq> Domain ?p" by force
  moreover have "Domain a \<supseteq> Domain ?p" by fast
  ultimately have 
  1: "Domain a = Domain ?p" by fast
  {
    fix z assume "z \<in> ?a" 
    then obtain x where 
    "x \<in> Domain ?p & z=(x , \<Union> (?p `` {x}))" by blast
    then have "x \<in> Domain a & z=(x , \<Union> (?p `` {x}))" by fast
    then moreover have "?p``{x} = finestpart (a,,x)" using assms by fastforce
    moreover have "\<Union> (finestpart (a,,x))= a,,x" by (metis finestPartUnion)
    ultimately have "z \<in> a" by (metis assms(1) eval_runiq_rel)
  }
  then have
  2: "?a \<subseteq> a" by fast
  {
    fix z assume 0: "z \<in> a" let ?x="fst z" let ?Y="a,,?x" let ?YY="finestpart ?Y"
    have "z \<in> a & ?x \<in> Domain a" using 0 by (metis fst_eq_Domain rev_image_eqI) 
    then have 
    3: "z \<in> a & ?x \<in> Domain ?p" using 1 by presburger  
    then have "?p `` {?x} = ?YY" by fastforce
    then have "\<Union> (?p `` {?x}) = ?Y" by (metis finestPartUnion)
    moreover have "z = (?x, ?Y)" using assms by (metis "0" functionOnFirstEqualsSecond
                                                           surjective_pairing)
    ultimately have "z \<in> ?a" using 3 by (metis (lifting, mono_tags) mem_Collect_eq)
  }
  then have "a = ?a" using 2 by blast
  moreover have "?p = pseudoAllocation a" using lm048 assms by (metis (lifting, mono_tags))
  ultimately show ?thesis by auto
qed

corollary lm075: 
  assumes "a \<in> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" 
  shows "(pseudoAllocationInv \<circ> pseudoAllocation) a = id a"
proof -
  have "runiq a" using runiqs_def assms by fast
  moreover have "{} \<notin> Range a" using assms by blast
  ultimately show ?thesis using lm074 by fastforce
qed

lemma lm076: 
  "inj_on (pseudoAllocationInv \<circ> pseudoAllocation) (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
proof -
  let ?ne="Pow (UNIV \<times> (UNIV - {{}}))" 
  let ?X="runiqs \<inter> ?ne" 
  let ?f="pseudoAllocationInv \<circ> pseudoAllocation"
  have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> id a1 = id a2" using lm075 by blast 
  then have "\<forall>a1 \<in> ?X. \<forall> a2 \<in> ?X. ?f a1 = ?f a2 \<longrightarrow> a1 = a2" by auto
  thus ?thesis unfolding inj_on_def by blast
qed

corollary lm077: 
  "inj_on pseudoAllocation (runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}})))" 
  using lm076 inj_on_imageI2 by blast

lemma lm078: 
  "injectionsUniverse \<subseteq> runiqs" 
  using runiqs_def Collect_conj_eq Int_lower1 by metis

lemma lm079: 
  "partitionValuedUniverse \<subseteq> Pow (UNIV \<times> (UNIV - {{}}))" 
  using is_non_overlapping_def by force

corollary lm080: 
  "allocationsUniverse \<subseteq> runiqs \<inter> Pow (UNIV \<times> (UNIV - {{}}))" 
  using lm078 lm079 by auto

corollary lm081: 
  "inj_on pseudoAllocation allocationsUniverse" 
  using lm077 lm080 subset_inj_on by blast

corollary lm082: 
  "inj_on pseudoAllocation (allAllocations N G)" 
proof -
  have "allAllocations N G \<subseteq> allocationsUniverse" 
    by (metis (no_types) allAllocationsUniverse)
  thus "inj_on pseudoAllocation (allAllocations N G)" using lm081 subset_inj_on by blast
qed

lemma lm083: 
  assumes "card N > 0" "distinct G" 
  shows "winningAllocationsRel N (set G) bids \<subseteq> set (allAllocationsAlg N G)"
  using assms winningAllocationPossible allAllocationsBridgingLemma by (metis(no_types))
 
corollary lm084: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "winningAllocationsRel N (set G) bids \<inter> set (allAllocationsAlg N G) \<noteq> {}"
proof -
  let ?w = winningAllocationsRel 
  let ?a = allAllocationsAlg
  let ?G = "set G" 
  have "card N > 0" using assms by (metis card_gt_0_iff)
  then have "?w N ?G bids \<subseteq> set (?a N G)" using lm083 by (metis assms(3))
  then show ?thesis using assms lm011 by (metis List.finite_set le_iff_inf)
qed

(* -` is the reverse image *)
lemma lm085: 
  "X = (%x. x \<in> X) -`{True}" 
  by blast

corollary lm086: 
  assumes  "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "(%x. x\<in>winningAllocationsRel N (set G) bids)-`{True} \<inter> 
         set (allAllocationsAlg N G) \<noteq> {}"
  using assms lm084 lm085 by metis

lemma lm087: 
  assumes "P -` {True} \<inter> set l \<noteq> {}" 
  shows "takeAll P l \<noteq> []" 
  using assms nonEmptyListFiltered filterpositions2_def by (metis Nil_is_map_conv)

corollary lm088: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) (allAllocationsAlg N G) \<noteq> []"
  using assms lm087 lm086 by metis

corollary lm089: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "perm2 (takeAll (%x. x \<in> winningAllocationsRel N (set G) bids) 
                        (allAllocationsAlg N G)) 
               n \<noteq> []"
  using assms permutationNotEmpty lm088 by metis

(* The chosen allocation is in the set of possible winning allocations *)

corollary lm090: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}" 
  shows "chosenAllocation N G bids random \<in> winningAllocationsRel N (set G) bids"
proof -
  have "\<And>x\<^sub>1 b_x x. set x\<^sub>1 = {} 
        \<or> (randomEl x\<^sub>1 b_x::('a \<times> 'b set) set) \<in> x 
        \<or> \<not> set x\<^sub>1 \<subseteq> x" by (metis (no_types) randomElLemma subsetCE)
  thus "winningAllocationRel N (set G) 
          ((\<in>) (randomEl (takeAll (\<lambda>x. winningAllocationRel N (set G) ((\<in>) x) bids)
                (allAllocationsAlg N G)) random)) bids" 
       by (metis lm088 assms(1) assms(2) assms(3) assms(4) takeAllSubset set_empty)
qed

(* The following lemma proves a property of maxbid, which in the following will be proved to maximize the revenue. a and aa are allocations. *)
lemma lm091: 
  assumes "finite G" "a \<in> allAllocations N G" "aa \<in> allAllocations N G"
  shows "real(sum(maxbid a N G)(pseudoAllocation a)) - 
            sum(maxbid a N G)(pseudoAllocation aa) = 
         real (card G) - 
            card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
proof -
  let ?p = pseudoAllocation 
  let ?f = finestpart 
  let ?m = maxbid 
  let ?B = "?m a N G" 
  have "?p aa \<subseteq> N \<times> ?f G" using assms lm073 by (metis (lifting, mono_tags)) 
  then have "?p aa \<subseteq> ?p a \<union> (N \<times> ?f G)" by auto 
  moreover have "finite (?p aa)" using assms lm034 lm040 by blast 
  ultimately have "real(sum ?B (?p a)) - sum ?B (?p aa) = 
                   real(card (?p a))-card(?p aa \<inter> (?p a))" 
    using differenceSumVsCardinalityReal by fast
  moreover have "... = real (card G) - card (?p aa \<inter> (?p a))" 
    using assms lm034 by (metis (lifting, mono_tags))
  ultimately show ?thesis by simp
qed

lemma lm092: 
  "summedBidVectorRel bids N G = graph (N \<times> (Pow G-{{}})) (summedBidSecond bids)" 
  unfolding graph_def using lm016 by blast

lemma lm093: 
  assumes "x\<in>X" 
  shows "toFunction (graph X f) x = f x" 
  using assms by (metis graphEqImage toFunction_def)

corollary lm094: 
  assumes "pair \<in> N \<times> (Pow G-{{}})" 
  shows "summedBidVector bids N G pair = summedBidSecond bids pair"
  using assms lm093 lm092 by (metis(mono_tags))

(* type conversion to real commutes *)
lemma lm095: 
  "summedBidSecond (real \<circ> ((bids:: _ => nat))) pair = real (summedBidSecond bids pair)" 
  by simp

lemma lm096: 
  assumes "pair \<in> N \<times> (Pow G-{{}})" 
  shows  "summedBidVector (real\<circ>(bids:: _ => nat)) N G pair = 
          real (summedBidVector bids N G pair)" 
  using assms lm094 lm095 by (metis(no_types))

(* TPTP?*)
corollary lm097: 
  assumes "X \<subseteq> N \<times> (Pow G - {{}})" 
  shows "\<forall>pair \<in> X. summedBidVector (real \<circ> (bids::_=>nat)) N G pair =
         (real \<circ> (summedBidVector bids N G)) pair"
proof -
  { fix esk48\<^sub>0 :: "'a \<times> 'b set"
    { assume "esk48\<^sub>0 \<in> N \<times> (Pow G - {{}})"
      hence "summedBidVector (real \<circ> bids) N G esk48\<^sub>0 = real (summedBidVector bids N G esk48\<^sub>0)" using lm096 by blast
      hence "esk48\<^sub>0 \<notin> X \<or> summedBidVector (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> summedBidVector bids N G) esk48\<^sub>0" by simp }
    hence "esk48\<^sub>0 \<notin> X \<or> summedBidVector (real \<circ> bids) N G esk48\<^sub>0 = (real \<circ> summedBidVector bids N G) esk48\<^sub>0" using assms by blast }
  thus "\<forall>pair\<in>X. summedBidVector (real \<circ> bids) N G pair = (real \<circ> summedBidVector bids N G) pair" by blast
qed

corollary lm098: 
  assumes "aa \<subseteq> N \<times> (Pow G-{{}})" 
  shows "sum ((summedBidVector (real \<circ> (bids::_=>nat)) N G)) aa = 
         real (sum ((summedBidVector bids N G)) aa)" 
  (is "?L=?R")
proof -
  have "\<forall> pair \<in> aa. summedBidVector (real \<circ> bids) N G pair = 
                     (real \<circ> (summedBidVector bids N G)) pair"
  using assms by (rule lm097)
  then have "?L = sum (real\<circ>(summedBidVector bids N G)) aa" using sum.cong by force
  then show ?thesis by simp
qed

corollary lm099: 
  assumes "aa \<in> allAllocations N G" 
  shows "sum ((summedBidVector (real \<circ> (bids::_=>nat)) N G)) aa = 
         real (sum ((summedBidVector bids N G)) aa)" 
  using assms lm098 allocationPowerset by (metis(lifting,mono_tags))

corollary lm100: 
  assumes "finite G" "a \<in> allAllocations N G" "aa \<in> allAllocations N G"
  shows "real (sum (tiebids a N G) a) - sum (tiebids a N G) aa = 
         real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))" 
  (is "?L=?R")
proof -
  let ?l=summedBidVector 
  let ?m=maxbid 
  let ?s=sum 
  let ?p=pseudoAllocation
  let ?bb="?m a N G" 
  let ?b="real \<circ> (?m a N G)"  
  have "real (?s ?bb (?p a)) - (?s ?bb (?p aa)) = ?R" using assms lm091 by blast 
  then have 
  1: "?R = real (?s ?bb (?p a)) - (?s ?bb (?p aa))" by simp
  have " ?s (?l ?b N G) aa = ?s ?b (?p aa)" using assms lm070 by blast moreover have 
  "... = ?s ?bb (?p aa)" by fastforce 
  moreover have "(?s (?l ?b N G) aa) = real (?s (?l ?bb N G) aa)" using assms(3) by (rule lm099)
  ultimately have 
  2: "?R = real (?s ?bb (?p a)) - (?s (?l ?bb N G) aa)" by (metis 1)
  have "?s (?l ?b N G) a=(?s ?b (?p a))" using assms lm070 by blast
  moreover have "... = ?s ?bb (?p a)" by force
  moreover have "... = real (?s ?bb (?p a))" by fast
  moreover have "?s (?l ?b N G) a = real (?s (?l ?bb N G) a)" using assms(2) by (rule lm099)
  ultimately have "?s (?l ?bb N G) a = real (?s ?bb (?p a))" by simp
  thus ?thesis using 2 by simp
qed

corollary lm101: 
  assumes "finite G" "a \<in> allAllocations N G" "aa \<in> allAllocations N G"
          "x = real (sum (tiebids a N G) a) - sum (tiebids a N G) aa" 
  shows "x <= card G & 
         x \<ge> 0 & 
        (x=0 \<longleftrightarrow> a = aa) & 
        (aa \<noteq> a \<longrightarrow> sum (tiebids a N G) aa < sum (tiebids a N G) a)"
proof -
  let ?p = pseudoAllocation 
  have "real (card G) >= real (card G) - card (?p aa \<inter> (?p a))" by force
  moreover have "real (sum (tiebids a N G) a) - sum (tiebids a N G) aa = 
                 real (card G) - card (pseudoAllocation aa \<inter> (pseudoAllocation a))"
           using assms lm100 by blast 
  ultimately have
  1: "x=real(card G)-card(pseudoAllocation aa\<inter>(pseudoAllocation a))" using assms by force 
  then have
  2: "x \<le> real (card G)" using assms by linarith 
  have 
  3: "card (?p aa) = card G & card (?p a) = card G" using assms lm034 by blast 
  moreover have "finite (?p aa) & finite (?p a)" using assms lm040 by blast
  ultimately have "card (?p aa \<inter> ?p a) \<le> card G" using Int_lower2 card_mono by fastforce 
  then have 
  4: "x \<ge> 0" using assms lm100 1 by linarith 
  have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (?p aa = ?p a)" 
       using 3 lm041 4 assms by (metis (lifting, mono_tags))
  moreover have "?p aa = ?p a \<longrightarrow> a = aa" using assms lm082 inj_on_def 
       by (metis (lifting, mono_tags))
  ultimately have "card (?p aa \<inter> (?p a)) = card G \<longleftrightarrow> (a=aa)" by blast
  moreover have "x = real (card G) - card (?p aa \<inter> (?p a))" using assms lm100 by blast
  ultimately have 
  5: "x = 0 \<longleftrightarrow> (a=aa)" by linarith 
  then have 
  "aa \<noteq> a \<longrightarrow> sum (tiebids a N G) aa < real (sum (tiebids a N G) a)" 
        using 1 4 assms by auto
  thus ?thesis using 2 4 5
    unfolding of_nat_less_iff by force
qed 

(* If for an arbitrary allocation a we compute tiebids for it then the corresponding revenue is strictly maximal. *)
corollary lm102: 
  assumes "finite G" "a \<in> allAllocations N G" 
          "aa \<in> allAllocations N G" "aa \<noteq> a" 
  shows "sum (tiebids a N G) aa < sum (tiebids a N G) a" 
  using assms lm101 by blast

lemma lm103: 
  assumes "N \<noteq> {}" "finite N" "distinct G" "set G \<noteq> {}"
          "aa \<in> (allAllocations N (set G))-{chosenAllocation N G bids random}" 
  shows "sum (resolvingBid N G bids random) aa < 
         sum (resolvingBid N G bids random) (chosenAllocation N G bids random)" 
proof -
  let ?a="chosenAllocation N G bids random" 
  let ?p=allAllocations 
  let ?G="set G"
  have "?a \<in> winningAllocationsRel N (set G) bids" using assms lm090 by blast
  moreover have "winningAllocationsRel N (set G) bids \<subseteq> ?p N ?G" using assms winningAllocationPossible by metis
  ultimately have "?a \<in> ?p N ?G" using lm090 assms winningAllocationPossible rev_subsetD by blast
  then show ?thesis using assms lm102 by blast 
qed

(* putting together the two rounds in the auction, first using the bids, then the random values. *)
abbreviation "terminatingAuctionRel N G bids random == 
              argmax (sum (resolvingBid N G bids random)) 
                     (argmax (sum bids) (allAllocations N (set G)))"

text\<open>Termination theorem: it assures that the number of winning allocations is exactly one\<close>
theorem winningAllocationUniqueness: 
  assumes "N \<noteq> {}" "distinct G" "set G \<noteq> {}" "finite N"
  shows "terminatingAuctionRel N G (bids) random = {chosenAllocation N G bids random}"
proof -
  let ?p = allAllocations 
  let ?G = "set G" 
  let ?X = "argmax (sum bids) (?p N ?G)"
  let ?a = "chosenAllocation N G bids random" 
  let ?b = "resolvingBid N G bids random"
  let ?f = "sum ?b" 
  let ?t=terminatingAuctionRel 
  have "\<forall>aa \<in> (allAllocations N ?G)-{?a}. ?f aa < ?f ?a" 
    using assms lm103 by blast 
  then have "\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a" using assms lm103 by auto
  moreover have "finite N" using assms by simp 
  then have "finite (?p N ?G)" using assms allAllocationsFinite by (metis List.finite_set)
  then have "finite ?X" using assms by (metis finite_subset winningAllocationPossible)
  moreover have "?a \<in> ?X" using lm090 assms by blast
  ultimately have "finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)" by force
  moreover have "(finite ?X & ?a \<in> ?X & (\<forall>aa \<in> ?X-{?a}. ?f aa < ?f ?a)) \<longrightarrow> argmax ?f ?X = {?a}"
    by (rule argmaxProperty)
  ultimately have "{?a} = argmax ?f ?X" using injectionsFromEmptyIsEmpty by presburger
  moreover have "... = ?t N G bids random" by simp
  ultimately show ?thesis by simp
qed

text \<open>The computable variant of Else is defined next as Elsee.\<close>
definition "toFunctionWithFallbackAlg R fallback == 
            (% x. if (x \<in> Domain R) then (R,,x) else fallback)"
notation toFunctionWithFallbackAlg (infix "Elsee" 75) 

end

