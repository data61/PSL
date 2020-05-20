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

section \<open>VCG auction: definitions and theorems\<close>

theory CombinatorialAuction

imports
UniformTieBreaking

begin

subsection \<open>Definition of a VCG auction scheme, through the pair @{term "(vcga, vcgp)"}\<close>

(* b is a bid vector and participants is the set of all participants present in b *) 
abbreviation "participants b == Domain (Domain b)"

(* goods is the list of goods auctioned *)
abbreviation "goods == sorted_list_of_set o Union o Range o Domain"

(* The seller is represented as integer 0, the other particants as integers 1, ..., n *)
abbreviation "seller == (0::integer)"

(* allAllocations' and allAllocations'' are variants of allAllocations. All three formulations are equivent. *)
abbreviation "allAllocations' N \<Omega> == 
  injectionsUniverse \<inter> {a. Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>}" 

abbreviation "allAllocations'' N \<Omega> == allocationsUniverse \<inter> {a. Domain a \<subseteq> N & \<Union>(Range a) = \<Omega>}"

lemma allAllocationsEquivalence: 
  "allAllocations N \<Omega> = allAllocations' N \<Omega> & allAllocations N \<Omega> = allAllocations'' N \<Omega>" 
  using allocationInjectionsUnivervseProperty allAllocationsIntersection by metis

lemma allAllocationsVarCharacterization: 
  "(a \<in> allAllocations'' N \<Omega>) = (a \<in> allocationsUniverse& Domain a \<subseteq> N & \<Union>(Range a) = \<Omega>)" 
  by force

(* remove the seller from the set of all allocations *)
abbreviation "soldAllocations N \<Omega> == (Outside' {seller}) ` (allAllocations (N \<union> {seller}) \<Omega>)"

(* soldAllocations' and soldAllocations'' are variants of soldAllocations reflecting the different
   formulations of allAllocations. soldAllocations''' is yet another variant. These variants are
   used since for different proofs different variants are easier to use. *)
abbreviation "soldAllocations' N \<Omega> == (Outside' {seller}) ` (allAllocations' (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations'' N \<Omega> == (Outside' {seller}) ` (allAllocations'' (N \<union> {seller}) \<Omega>)"
abbreviation "soldAllocations''' N \<Omega> == 
  allocationsUniverse \<inter> {aa. Domain aa\<subseteq>N-{seller} & \<Union>(Range aa)\<subseteq>\<Omega>}"
lemma soldAllocationsEquivalence: 
  "soldAllocations N \<Omega> = soldAllocations' N \<Omega> & 
   soldAllocations' N \<Omega> = soldAllocations'' N \<Omega>"
  using allAllocationsEquivalence by metis

corollary soldAllocationsEquivalenceVariant: 
  "soldAllocations = soldAllocations'  & 
   soldAllocations' = soldAllocations'' & 
   soldAllocations = soldAllocations''" 
  using soldAllocationsEquivalence by metis

lemma allocationSellerMonotonicity: 
  "soldAllocations (N-{seller}) \<Omega> \<subseteq> soldAllocations N \<Omega>" 
  using Outside_def by simp

lemma allocationsUniverseCharacterization: 
  "(a \<in> allocationsUniverse) = (a \<in> allAllocations'' (Domain a) (\<Union>(Range a)))"
  by blast

lemma allocationMonotonicity: 
  assumes "N1 \<subseteq> N2" 
  shows "allAllocations'' N1 \<Omega> \<subseteq> allAllocations'' N2 \<Omega>" 
  using assms by auto

lemma allocationWithOneParticipant: 
  assumes "a \<in> allAllocations'' N \<Omega>" 
  shows "Domain (a -- x) \<subseteq> N-{x}" 
  using assms Outside_def by fastforce

lemma soldAllocationIsAllocation: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a \<in> allocationsUniverse"
proof -
obtain aa where "a  =aa -- seller & aa \<in> allAllocations (N\<union>{seller}) \<Omega>"
  using assms by blast
then have "a \<subseteq> aa & aa \<in> allocationsUniverse" 
  unfolding Outside_def using allAllocationsIntersectionSubset by blast
then show ?thesis using subsetAllocation by blast
qed

lemma soldAllocationIsAllocationVariant: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a \<in> allAllocations'' (Domain a) (\<Union>(Range a))"
proof - 
  show ?thesis using assms soldAllocationIsAllocation
  by auto blast+
qed

lemma onlyGoodsAreSold: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "\<Union> (Range a) \<subseteq> \<Omega>" 
  using assms Outside_def by blast

lemma soldAllocationIsRestricted: 
  "a \<in> soldAllocations'' N \<Omega> = 
   (\<exists>aa. aa -- (seller) = a  \<and>  aa \<in> allAllocations'' (N \<union> {seller}) \<Omega>)" 
  by blast

(* Note that +* enlarges the function by one additional pair *)
lemma restrictionConservation:
  "(R +* ({x}\<times>Y)) -- x = R -- x" 
  unfolding Outside_def paste_def by blast

lemma allocatedToBuyerMeansSold: 
  assumes "a \<in> allocationsUniverse" "Domain a \<subseteq> N-{seller}" "\<Union> (Range a) \<subseteq> \<Omega>" 
  shows "a \<in> soldAllocations'' N \<Omega>"
proof -
  let ?i = "seller" 
  let ?Y = "{\<Omega>-\<Union> (Range a)}-{{}}" 
  let ?b = "{?i}\<times>?Y" 
  let ?aa = "a\<union>?b"
  let ?aa' = "a +* ?b" 
  have
  1: "a \<in> allocationsUniverse" using assms(1) by fast 
  have "?b \<subseteq> {(?i,\<Omega>-\<Union>(Range a))} - {(?i, {})}" by fastforce 
  then have 
  2: "?b \<in> allocationsUniverse" 
    using allocationUniverseProperty subsetAllocation by (metis(no_types))
  have 
  3: "\<Union> (Range a) \<inter> \<Union> (Range ?b) = {}" by blast 
  have 
  4: "Domain a \<inter> Domain ?b ={}" using assms by fast
  have "?aa \<in> allocationsUniverse" using 1 2 3 4 by (rule allocationUnion)
  then have "?aa \<in> allAllocations'' (Domain ?aa) (\<Union> (Range ?aa))" 
    unfolding allocationsUniverseCharacterization by metis 
  then have "?aa \<in> allAllocations'' (N\<union>{?i}) (\<Union> (Range ?aa))" 
    using allocationMonotonicity assms paste_def by auto
  moreover have "Range ?aa = Range a \<union> ?Y" by blast 
  then moreover have "\<Union> (Range ?aa) = \<Omega>" 
    using Un_Diff_cancel Un_Diff_cancel2 Union_Un_distrib Union_empty Union_insert  
    by (metis (lifting, no_types) assms(3) cSup_singleton subset_Un_eq) 
  moreover have "?aa' = ?aa" using 4 by (rule paste_disj_domains)
  ultimately have "?aa' \<in> allAllocations'' (N\<union>{?i}) \<Omega>" by simp
  moreover have "Domain ?b \<subseteq> {?i}" by fast 
  have "?aa' -- ?i = a -- ?i" by (rule restrictionConservation)
  moreover have "... = a" using Outside_def assms(2) by auto 
  ultimately show ?thesis using soldAllocationIsRestricted by auto
qed

lemma allocationCharacterization: 
  "a \<in> allAllocations N \<Omega>  =  
   (a \<in> injectionsUniverse & Domain a \<subseteq> N & Range a \<in> all_partitions \<Omega>)" 
  by (metis (full_types) posssibleAllocationsRelCharacterization)

(* The lemmas lm01, lm02, lm03, and lm04 are used in order to prove
   lemma soldAllocationVariantEquivalence   *)
lemma lm01: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "Domain a \<subseteq> N-{seller} & a \<in> allocationsUniverse"  
proof -
  let ?i = "seller" 
  obtain aa where
  0: "a = aa -- ?i & aa \<in> allAllocations'' (N \<union> {?i}) \<Omega>" 
    using assms(1) soldAllocationIsRestricted by blast
  then have "Domain aa \<subseteq> N \<union> {?i}" using allocationCharacterization by blast
  then have "Domain a \<subseteq> N - {?i}" using 0 Outside_def by blast
  moreover have "a \<in> soldAllocations N \<Omega>" using assms soldAllocationsEquivalenceVariant by metis
  then moreover have "a \<in> allocationsUniverse" using soldAllocationIsAllocation by blast
  ultimately show ?thesis by blast
qed

corollary lm02: 
  assumes "a \<in> soldAllocations'' N \<Omega>" 
  shows "a \<in> allocationsUniverse & Domain a \<subseteq> N-{seller} & \<Union> (Range a) \<subseteq> \<Omega>"
proof -
  have "a \<in> allocationsUniverse" using assms lm01 [of a] by blast
  moreover have "Domain a \<subseteq> N-{seller}" using assms lm01 by blast
  moreover have "\<Union> (Range a) \<subseteq> \<Omega>" using assms onlyGoodsAreSold by blast
  ultimately show ?thesis by blast
qed

corollary lm03:
  "(a \<in> soldAllocations'' N \<Omega>) =
   (a \<in> allocationsUniverse & a \<in> {aa. Domain aa \<subseteq> N-{seller} & \<Union> (Range aa) \<subseteq> \<Omega>})" 
  (is "?L = ?R") 
proof -
  have "(a\<in>soldAllocations'' N \<Omega>) =
        (a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> (Range a) \<subseteq> \<Omega>)" 
  using lm02 allocatedToBuyerMeansSold by (metis (mono_tags))
  then have "?L = (a\<in>allocationsUniverse& Domain a \<subseteq> N-{seller} & \<Union> (Range a) \<subseteq> \<Omega>)" by fast
  moreover have "... = ?R" using mem_Collect_eq by (metis (lifting, no_types))
  ultimately show ?thesis by auto
qed

corollary lm04: 
  "a \<in> soldAllocations'' N \<Omega> =
   (a\<in> (allocationsUniverse \<inter> {aa. Domain aa \<subseteq> N-{seller} & \<Union> (Range aa) \<subseteq> \<Omega>}))" 
  using lm03 by (metis (mono_tags) Int_iff)

corollary soldAllocationVariantEquivalence: 
  "soldAllocations'' N \<Omega> = soldAllocations''' N \<Omega>" 
  (is "?L=?R") 
proof - 
  {
   fix a 
   have "a \<in> ?L = (a \<in> ?R)" by (rule lm04)
  } 
  thus ?thesis by blast 
qed

(* We use lm05 in order to show a variant for soldAllocations without ''' *)
lemma lm05: 
  assumes "a \<in> soldAllocations''' N \<Omega>" 
  shows "a -- n \<in> soldAllocations''' (N-{n}) \<Omega>"
proof -
  let ?bb = seller 
  let ?d = Domain 
  let ?r = Range 
  let ?X1 = "{aa. ?d aa \<subseteq> N-{n}-{?bb} & \<Union>(?r aa)\<subseteq>\<Omega>}" 
  let ?X2 = "{aa. ?d aa \<subseteq> N-{?bb} & \<Union>(?r aa) \<subseteq> \<Omega>}" 
  have "a\<in>?X2" using assms(1) by fast  
  then have 
  0: "?d a \<subseteq> N-{?bb} & \<Union>(?r a) \<subseteq> \<Omega>" by blast 
  then have "?d (a--n) \<subseteq> N-{?bb}-{n}" 
    using outside_reduces_domain by (metis Diff_mono subset_refl) 
  moreover have "... = N-{n}-{?bb}" by fastforce 
  ultimately have "?d (a--n) \<subseteq> N-{n}-{?bb}" by blast 
  moreover have "\<Union> (?r (a--n)) \<subseteq> \<Omega>" 
    unfolding Outside_def using 0 by blast 
  ultimately have "a -- n \<in> ?X1" by fast 
  moreover have "a--n \<in> allocationsUniverse" 
    using assms(1) Int_iff allocationsUniverseOutside by (metis(lifting,mono_tags)) 
  ultimately show ?thesis by blast
qed

lemma allAllocationsEquivalenceExtended: 
  "soldAllocations =  soldAllocations' & 
   soldAllocations' = soldAllocations'' &
   soldAllocations'' = soldAllocations'''" 
  using soldAllocationVariantEquivalence soldAllocationsEquivalenceVariant by metis

(* The following corollary shows that an allocation is invariant to subtracting a single bidder.   
   This is used a fundamental step to prove the non-negativity of price in VCG. *)
corollary soldAllocationRestriction: 
  assumes "a \<in> soldAllocations N \<Omega>" 
  shows "a -- n \<in> soldAllocations (N-{n}) \<Omega>"
proof - 
  let ?A' = soldAllocations''' 
  have "a \<in> ?A' N \<Omega>" using assms allAllocationsEquivalenceExtended by metis 
  then have "a -- n \<in> ?A' (N-{n}) \<Omega>" by (rule lm05) 
  thus ?thesis using allAllocationsEquivalenceExtended by metis 
qed

corollary allocationGoodsMonotonicity: 
  assumes "\<Omega>1 \<subseteq> \<Omega>2" 
  shows "soldAllocations''' N \<Omega>1 \<subseteq> soldAllocations''' N \<Omega>2"
  using assms by blast

corollary allocationGoodsMonotonicityVariant: 
  assumes "\<Omega>1 \<subseteq> \<Omega>2" 
  shows "soldAllocations'' N \<Omega>1 \<subseteq> soldAllocations'' N \<Omega>2" 
proof -
  have "soldAllocations'' N \<Omega>1 = soldAllocations''' N \<Omega>1" 
    by (rule soldAllocationVariantEquivalence)
  moreover have "... \<subseteq> soldAllocations''' N \<Omega>2" 
    using assms(1) by (rule allocationGoodsMonotonicity)
  moreover have "... = soldAllocations'' N \<Omega>2" using soldAllocationVariantEquivalence by metis
  ultimately show ?thesis by auto
qed

(* maximalStrictAllocationsAlg are the allocations maximizing the revenue. They also include the
   unallocated goods assigned to the seller (bidder 0).*)
abbreviation "maximalStrictAllocations N \<Omega> b == argmax (sum b) (allAllocations ({seller}\<union>N) \<Omega>)"

(* randomBids builds up a bid vector from a random number so that bidding with this bid vector
   resolves any ties. Details are defined in UniformTieBreaking.thy *)
abbreviation "randomBids N \<Omega> b random == resolvingBid (N\<union>{seller}) \<Omega> b random"

(* vcgas gives the one-element set with the winning allocation after tie breaking.
   (argmax\<circ>sum) b ... determines the set of all maximal allocations.
   (argmax\<circ>sum) (randomBids ...) restricts that by tie-breaking to a singleton.
   Outside' {seller} removes the seller from the only allocation in the singleton.   *)
abbreviation "vcgas N \<Omega> b r  == 
  Outside' {seller} `((argmax\<circ>sum) (randomBids N \<Omega> b r)
                                      ((argmax\<circ>sum) b (allAllocations (N \<union> {seller}) (set \<Omega>))))"

(* Takes the element out of the one elemnt set (vcgas ...) *)
abbreviation "vcga N \<Omega> b r == the_elem (vcgas N \<Omega> b r)"

(* alternative definition of vcga *)
abbreviation "vcga' N \<Omega> b r == 
  (the_elem (argmax (sum (randomBids N \<Omega> b r)) 
                    (maximalStrictAllocations N (set \<Omega>) b)))
  -- seller"

(* The following three auxiliary lemmas, lm06, lm07, and lm08 are used to prove lemma
   vcgaEquivalence as well as in the theorem that cardinality of vcgas is one.*)
lemma lm06: 
  assumes "card ((argmax\<circ>sum) (randomBids N \<Omega> b r) 
                                 ((argmax\<circ>sum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1" 
  shows "vcga N \<Omega> b r = 
         (the_elem ((argmax\<circ>sum) (randomBids N \<Omega> b r) 
                                    ((argmax\<circ>sum) b (allAllocations ({seller}\<union>N) (set \<Omega>))))) 
          -- seller"
  using assms cardOneTheElem by auto

corollary lm07: 
  assumes "card ((argmax\<circ>sum) (randomBids N \<Omega> b r) 
                                 ((argmax\<circ>sum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1"
  shows "vcga N \<Omega> b r = vcga' N \<Omega> b r" 
  (is "?l = ?r")
proof -
  have "?l = (the_elem ((argmax\<circ>sum) (randomBids N \<Omega> b r) 
                                        ((argmax\<circ>sum) b (allAllocations ({seller}\<union>N) (set \<Omega>)))))
              -- seller"
    using assms by (rule lm06) 
  moreover have "... = ?r" by force 
  ultimately show ?thesis by blast
qed

lemma lm08: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card ((argmax\<circ>sum) (randomBids N \<Omega> bids random)
                               ((argmax\<circ>sum) bids (allAllocations (N\<union>{seller}) (set \<Omega>)))) = 1"
  (is "card ?l=_")
proof - 
  let ?N = "N\<union>{seller}" 
  let ?b' = "randomBids N \<Omega> bids random" 
  let ?s = sum 
  let ?a = argmax 
  let ?f = "?a \<circ> ?s"
  have 
  1: "?N\<noteq>{}" by auto 
  have 
  2: "finite ?N" using assms(3) by simp
  have "?a (?s ?b') (?a (?s bids) (allAllocations ?N (set \<Omega>))) =
        {chosenAllocation ?N \<Omega> bids random}" (is "?L=?R")
  using 1 assms(1) assms(2) 2 by (rule winningAllocationUniqueness)
  moreover have "?L= ?f ?b' (?f bids (allAllocations ?N (set \<Omega>)))" by auto
  ultimately have "?l = {chosenAllocation ?N \<Omega> bids random}" by simp
  moreover have "card ...=1" by simp ultimately show ?thesis by simp 
qed

lemma vcgaEquivalence: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga N \<Omega> b r = vcga' N \<Omega> b r"
  using assms lm07 lm08 by blast

(* After showing that the cardinality of vcgas is 1, we know that the_elem to determine vcga
   will return a definite value. *)
theorem vcgaDefiniteness: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card (vcgas N \<Omega> b r) = 1"
proof -
  have "card ((argmax\<circ>sum) (randomBids N \<Omega> b r) 
                              ((argmax\<circ>sum) b (allAllocations (N\<union>{seller}) (set \<Omega>)))) =
        1" 
  (is "card ?X = _") using assms lm08 by blast
  moreover have "(Outside'{seller}) ` ?X = vcgas N \<Omega> b r" by blast
  ultimately show ?thesis using cardOneImageCardOne by blast
qed

(* The following lemma is a variant of the vcgaDefiniteness theorem. *)
lemma vcgaDefinitenessVariant: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows  "card (argmax (sum (randomBids N \<Omega> b r)) 
                       (maximalStrictAllocations N (set \<Omega>) b)) =
          1"
  (is "card ?L=_")
proof -
  let ?n = "{seller}" 
  have 
  1: "(?n \<union> N)\<noteq>{}" by simp 
  have 
  2: "finite (?n\<union>N)" using assms(3) by fast 
  have "terminatingAuctionRel (?n\<union>N) \<Omega> b r = {chosenAllocation (?n\<union>N) \<Omega> b r}" 
    using 1 assms(1) assms(2) 2 by (rule winningAllocationUniqueness) 
  moreover have "?L = terminatingAuctionRel (?n\<union>N) \<Omega> b r" by auto
  ultimately show ?thesis by auto
qed

theorem winningAllocationIsMaximal:
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "the_elem (argmax (sum (randomBids N \<Omega> b r)) 
                          (maximalStrictAllocations N (set \<Omega>) b)) \<in>
         (maximalStrictAllocations N (set \<Omega>) b)" 
  (is "the_elem ?X \<in> ?R") 
proof -
  have "card ?X=1" using assms by (rule vcgaDefinitenessVariant) 
  moreover have "?X \<subseteq> ?R" by auto
  ultimately show ?thesis using cardinalityOneTheElem by blast
qed

corollary winningAllocationIsMaximalWithoutSeller: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> (Outside' {seller})`(maximalStrictAllocations N (set \<Omega>) b)"
  using assms winningAllocationIsMaximal by blast

lemma maximalAllactionWithoutSeller: 
  "(Outside' {seller})`(maximalStrictAllocations N \<Omega> b) \<subseteq> soldAllocations N \<Omega>"
  using Outside_def by force

lemma onlyGoodsAreAllocatedAuxiliary: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> soldAllocations N (set \<Omega>)" 
  (is "?a \<in> ?A") 
proof - 
  have "?a \<in> (Outside' {seller})`(maximalStrictAllocations N (set \<Omega>) b)" 
    using assms by (rule winningAllocationIsMaximalWithoutSeller) 
  thus ?thesis using maximalAllactionWithoutSeller  by fastforce 
qed

theorem onlyGoodsAreAllocated: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga N \<Omega> b r \<in> soldAllocations N (set \<Omega>)" 
  (is "_\<in>?r") 
proof - 
  have "vcga' N \<Omega> b r \<in> ?r" using assms by (rule onlyGoodsAreAllocatedAuxiliary) 
  then show ?thesis using assms vcgaEquivalence by blast 
qed

(* Let b be a bid vector such that the seller's bid for each possible set of goods is 0 then 
   the revenue does not depend on the presence of the seller. *)
corollary neutralSeller: 
  assumes "\<forall>X. X \<in> Range a \<longrightarrow>b (seller, X)=0" "finite a" 
  shows "sum b a = sum b (a--seller)"
proof -
  let ?n = seller 
  have "finite (a||{?n})" using assms restrict_def by (metis finite_Int) 
  moreover have "\<forall>z \<in> a||{?n}. b z=0" using assms restrict_def by fastforce
  ultimately have "sum b (a||{?n}) = 0" using assms by (metis sum.neutral)
  thus ?thesis using sumOutside assms(2) by (metis add.comm_neutral) 
qed

corollary neutralSellerVariant: 
  assumes "\<forall>a\<in>A. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (seller, X)=0)"
  shows "{sum b a| a. a\<in>A} = {sum b (a -- seller)| a. a\<in>A}" 
  using assms neutralSeller by (metis (lifting, no_types))

lemma vcgaIsMaximalAux1: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "\<exists>a. ((a \<in> (maximalStrictAllocations N (set \<Omega>) b))  \<and>  (vcga' N \<Omega> b r = a -- seller)  &
                (a \<in> argmax (sum b) (allAllocations ({seller}\<union>N) (set \<Omega>))))" 
  using assms winningAllocationIsMaximalWithoutSeller by fast

lemma vcgaIsMaximalAux2: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  "\<forall>a \<in> allAllocations ({seller}\<union>N) (set \<Omega>). \<forall> X \<in> Range a. b (seller, X)=0"
  (is "\<forall>a\<in>?X. _") 
  shows "sum b (vcga' N \<Omega> b r) = Max{sum b a| a. a \<in> soldAllocations N (set \<Omega>)}"
proof -
  let ?n = seller 
  let ?s = sum 
  let ?a = "vcga' N \<Omega> b r" 
  obtain a where 
  0: "a \<in> maximalStrictAllocations N (set \<Omega>) b & 
      ?a = a--?n & 
      (a \<in> argmax (sum b) (allAllocations({seller}\<union>N)(set \<Omega>)))"
  (is "_ & ?a=_ & a\<in>?Z")
    using assms(1,2,3) vcgaIsMaximalAux1 by blast
  have 
  1: "\<forall>a \<in> ?X. finite a & (\<forall> X. X\<in>Range a \<longrightarrow> b (?n, X)=0)" 
    using assms(4) List.finite_set allocationFinite by metis 
  have 
  2: "a \<in> ?X" using 0 by auto have "a \<in> ?Z" using 0 by fast 
  then have "a \<in> ?X\<inter>{x. ?s b x = Max (?s b ` ?X)}" using injectionsUnionCommute by simp
  then have "a \<in> {x. ?s b x = Max (?s b ` ?X)}" using injectionsUnionCommute by simp
  moreover have "?s b ` ?X = {?s b a| a. a\<in>?X}" by blast
  ultimately have "?s b a = Max {?s b a| a. a\<in>?X}" by auto
  moreover have "{?s b a| a. a\<in>?X} = {?s b (a--?n)| a. a\<in>?X}" 
    using 1 by (rule neutralSellerVariant)
  moreover have "... = {?s b a| a. a \<in> Outside' {?n}`?X}" by blast
  moreover have "... = {?s b a| a. a \<in> soldAllocations N (set \<Omega>)}" by simp
  ultimately have "Max {?s b a| a. a \<in> soldAllocations N (set \<Omega>)} = ?s b a" by simp
  moreover have "... = ?s b (a--?n)" using 1 2 neutralSeller by (metis (lifting, no_types))
  ultimately show "?s b ?a=Max{?s b a| a. a \<in> soldAllocations N (set \<Omega>)}" using 0 by simp
qed

text \<open>Adequacy theorem: The allocation satisfies the standard pen-and-paper specification 
of a VCG auction. See, for example, \cite[\S~1.2]{cramton}.\<close>
theorem vcgaIsMaximal: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" "\<forall> X. b (seller, X) = 0" 
  shows "sum b (vcga' N \<Omega> b r) = Max{sum b a| a. a \<in> soldAllocations N (set \<Omega>)}"
  using assms vcgaIsMaximalAux2 by blast

corollary vcgaIsAllocationAllocatingGoodsOnly: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcga' N \<Omega> b r \<in> allocationsUniverse & \<Union> (Range (vcga' N \<Omega> b r)) \<subseteq> set \<Omega>" 
proof -
  let ?a = "vcga' N \<Omega> b r" 
  let ?n = seller
  obtain a where 
  0: "?a = a -- seller & a \<in> maximalStrictAllocations N (set \<Omega>) b"
    using assms winningAllocationIsMaximalWithoutSeller by blast
  then moreover have 
  1: "a \<in> allAllocations ({?n}\<union>N) (set \<Omega>)" by auto
  moreover have "maximalStrictAllocations N (set \<Omega>) b \<subseteq> allocationsUniverse" 
     by (metis (lifting, mono_tags) winningAllocationPossible 
                                    allAllocationsUniverse subset_trans)
  ultimately moreover have "?a = a -- seller  &  a \<in> allocationsUniverse" by blast
  then have "?a \<in> allocationsUniverse" using allocationsUniverseOutside by auto
  moreover have "\<Union> (Range a) = set \<Omega>" using allAllocationsIntersectionSetEquals 1 by metis
  then moreover have "\<Union> (Range ?a) \<subseteq> set \<Omega>" using Outside_def 0 by fast
  ultimately show ?thesis using allocationsUniverseOutside Outside_def by blast
qed

(* The price a participant n has to pay is the revenue achieved if n had not participated minus
   the value of the goods allocated not to n. *)
abbreviation "vcgp N \<Omega> b r n ==
   Max (sum b ` (soldAllocations (N-{n}) (set \<Omega>))) 
    -  (sum b (vcga N \<Omega> b r -- n))"

(* Since vcga is well-defined the following theorem is trivial. *)
theorem vcgpDefiniteness: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "\<exists>! y. vcgp N \<Omega> b r n = y" 
  using assms vcgaDefiniteness by simp

lemma soldAllocationsFinite: 
  assumes "finite N" "finite \<Omega>" 
  shows "finite (soldAllocations N \<Omega>)" 
  using assms allAllocationsFinite finite.emptyI finite.insertI finite_UnI finite_imageI 
  by metis

text\<open>The price paid by any participant is non-negative.\<close>
theorem NonnegPrices: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "vcgp N \<Omega> b r n >= (0::price)" 
proof - 
  let ?a = "vcga N \<Omega> b r" 
  let ?A = soldAllocations 
  let ?f = "sum b" 
  have "?a \<in> ?A N (set \<Omega>)" using assms by (rule onlyGoodsAreAllocated)
  then have "?a -- n \<in> ?A (N-{n}) (set \<Omega>)" by (rule soldAllocationRestriction)
  moreover have "finite (?A (N-{n}) (set \<Omega>))" 
    using assms(3) soldAllocationsFinite finite_set finite_Diff by blast
  ultimately have "Max (?f`(?A (N-{n}) (set \<Omega>))) \<ge> ?f (?a -- n)" 
  (is "?L >= ?R") by (rule maxLemma)
  then show "?L - ?R >=0" by linarith
qed

lemma allocationDisjointAuxiliary: 
  assumes "a \<in> allocationsUniverse" and "n1 \<in> Domain a" and "n2 \<in> Domain a" and "n1 \<noteq> n2" 
  shows "a,,n1 \<inter> a,,n2 = {}"
proof - 
  have "Range a \<in> partitionsUniverse" using assms nonOverlapping by blast
  moreover have "a \<in> injectionsUniverse & a \<in> partitionValuedUniverse" 
    using assms by (metis (lifting, no_types) IntD1 IntD2)
  ultimately moreover have "a,,n1 \<in> Range a" 
    using assms by (metis (mono_tags) eval_runiq_in_Range mem_Collect_eq)
  ultimately moreover have "a,,n1 \<noteq> a,,n2" 
    using assms converse.intros eval_runiq_rel mem_Collect_eq runiq_basic 
    by (metis (lifting, no_types))
  ultimately show ?thesis 
    using is_non_overlapping_def 
    by (metis (lifting, no_types) assms(3) eval_runiq_in_Range mem_Collect_eq)
qed

lemma allocationDisjoint: 
  assumes "a \<in> allocationsUniverse" and "n1 \<in> Domain a" and "n2 \<in> Domain a" and "n1 \<noteq> n2" 
  shows "a,,,n1 \<inter> a,,,n2 = {}" 
  using assms allocationDisjointAuxiliary imageEquivalence by fastforce 

text\<open>No good is assigned twice.\<close>
(* We assume implicitely that n1, n2 are participants, \<Omega> a goods list and N the participant set
   with "n1 \<in> Domain (vcga' N \<Omega> b r)" "n2 \<in> Domain (vcga' N \<Omega> b r)". However,
   formally these assumptions are not needed for the theorem. *) 
theorem PairwiseDisjointAllocations:
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N"  "n1 \<noteq> n2" 
  shows "(vcga' N \<Omega> b r),,,n1 \<inter> (vcga' N \<Omega> b r),,,n2 = {}"  
proof -
  have "vcga' N \<Omega> b r \<in> allocationsUniverse" 
    using vcgaIsAllocationAllocatingGoodsOnly assms by blast
  then show ?thesis using allocationDisjoint assms by fast
qed

text \<open>Nothing outside the set of goods is allocated.\<close>
theorem OnlyGoodsAllocated: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" "g \<in> (vcga N \<Omega> b r),,,n" 
  shows "g \<in> set \<Omega>"
proof - 
  let ?a = "vcga' N \<Omega> b r" 
  have "?a \<in> allocationsUniverse" using assms(1,2,3) vcgaIsAllocationAllocatingGoodsOnly by blast
  then have 1: "runiq ?a" using assms(1,2,3) by blast
  have 2: "n \<in> Domain ?a" using assms vcgaEquivalence by fast
  with 1 have "?a,,n \<in> Range ?a" using eval_runiq_in_Range by fast 
  with 1 2 have "?a,,,n \<in> Range ?a" using imageEquivalence by fastforce
  then have "g \<in> \<Union> (Range ?a)" using assms vcgaEquivalence by blast 
  moreover have "\<Union> (Range ?a) \<subseteq> set \<Omega>" using assms(1,2,3) vcgaIsAllocationAllocatingGoodsOnly by fast
  ultimately show ?thesis by blast
qed

subsection \<open>Computable versions of the VCG formalization\<close>

(*  The computable versions are used to extract code.
   Furthermore we prove the equivalence with their classical counterparts. This computes the set of all maximal allocations including the seller. *)
abbreviation "maximalStrictAllocationsAlg N \<Omega> b ==
  argmax (sum b) (set (allAllocationsAlg ({seller}\<union>N) \<Omega>))"

(* This computes the maximal allocation after tie breaking. *)
definition "chosenAllocationAlg N \<Omega> b (r::integer) == 
  (randomEl (takeAll (%x. x\<in> (argmax \<circ> sum) b (set (allAllocationsAlg N \<Omega>))) 
                    (allAllocationsAlg N \<Omega>)) 
            r)"

(* This is the computable version of maxbid in UniformTieBreaking.thy. It takes an allocation, 
   the bidders and the goods and computes a bid such for each good a bidder bids 1 if they get
   that good in allocation a, else they bid 0.*)
definition "maxbidAlg a N \<Omega> == (bidMaximizedBy a N \<Omega>) Elsee 0"

(* This is the completed version of summedBidVectorRel by returning 0 if 
   summedBidVectorRel is not defined. *)
definition "summedBidVectorAlg bids N \<Omega> == (summedBidVectorRel bids N \<Omega>) Elsee 0"

(* Computable version of tiebids. If computes a bid vector that when the VCG algorithm runs 
   on it yields the singleton {a}. *)
definition "tiebidsAlg a N \<Omega> == summedBidVectorAlg (maxbidAlg a N \<Omega>) N \<Omega>"

(* Computable version of resolvingBid, that is, is computes the bid vector in random values 
   that returns the chosen winning allocation *)
definition "resolvingBidAlg N \<Omega> bids random == 
  tiebidsAlg (chosenAllocationAlg N \<Omega> bids random) N (set \<Omega>)"

(* The same as above, but adding the seller who receives all unallocated goods. *)
definition "randomBidsAlg N \<Omega> b random == resolvingBidAlg (N\<union>{seller}) \<Omega> b random"

(* Computable allocation without those participants who do not receive anything. *)
definition "vcgaAlgWithoutLosers N \<Omega> b r == 
  (the_elem (argmax (sum (randomBidsAlg N \<Omega> b r)) 
                    (maximalStrictAllocationsAlg N \<Omega> b))) 
  -- seller"

(* Adding losers to an arbitrary allocation *)
abbreviation "addLosers participantset allocation == (participantset \<times> {{}}) +* allocation"

(* Computable version of vcga. It computes the winning allocation incl. losers. *)
definition "vcgaAlg N \<Omega> b r = addLosers N (vcgaAlgWithoutLosers N \<Omega> b r)"

(* Computable version of soldAllocations *)
abbreviation "soldAllocationsAlg N \<Omega> == 
  (Outside' {seller}) ` set (allAllocationsAlg (N \<union> {seller}) \<Omega>)"

(* Computable version of vcgp, which computes the prices each participant has to pay. Note that
   losers do not pay anything, hence vcgaAlgWithoutLosers is here equivalent to vcgaAlg. 
   The price a participant n has to pay is the revenue achieved if n had not participated minus
   the value of the goods allocated not to n.*)
definition "vcgpAlg N \<Omega> b r n (winningAllocation::allocation) =
  Max (sum b ` (soldAllocationsAlg (N-{n}) \<Omega>)) - 
  (sum b (winningAllocation -- n))"

lemma functionCompletion: 
  assumes "x \<in> Domain f" 
  shows "toFunction f x = (f Elsee 0) x"
  unfolding toFunctionWithFallbackAlg_def by (metis assms toFunction_def)

(* This technical lemma shows the equivalence of Elsee and toFunction inside a sum expression
   under certain assumptions. It is used for the proof of the bridging theorem that
   the two versions of the definition of maximalStrictAllocations are equivalent.*)
lemma lm09: 
  assumes "fst pair \<in> N" "snd pair \<in> Pow \<Omega> - {{}}" 
  shows "sum (%g. (toFunction (bidMaximizedBy a N \<Omega>))  (fst pair, g)) 
                (finestpart (snd pair)) =
         sum (%g. ((bidMaximizedBy a N \<Omega>) Elsee 0) (fst pair, g)) 
                (finestpart (snd pair))"
proof -
  let ?f1 = "%g.(toFunction (bidMaximizedBy a N \<Omega>))(fst pair, g)"
  let ?f2 = "%g.((bidMaximizedBy a N \<Omega>) Elsee 0)(fst pair, g)"
  { 
    fix g assume "g \<in> finestpart (snd pair)" 
    then have 
    0: "g \<in> finestpart \<Omega>" using assms finestpartSubset  by (metis Diff_iff Pow_iff in_mono)
    have "?f1 g = ?f2 g" 
    proof -
      have "\<And>x\<^sub>1 x\<^sub>2. (x\<^sub>1, g) \<in> x\<^sub>2 \<times> finestpart \<Omega> \<or> x\<^sub>1 \<notin> x\<^sub>2" by (metis 0 mem_Sigma_iff) 
      then have "(pseudoAllocation a <| (N \<times> finestpart \<Omega>)) (fst pair, g) = 
                 maxbidAlg a N \<Omega> (fst pair, g)"
        unfolding toFunctionWithFallbackAlg_def maxbidAlg_def
        by (metis (no_types) domainCharacteristicFunction UnCI assms(1) toFunction_def)
    thus ?thesis unfolding maxbidAlg_def by blast
    qed
  }
  thus ?thesis using sum.cong by simp
qed

(* lm10, lm11, lm12, l13 are variants of lm09 *)
corollary lm10: 
  assumes "pair \<in> N \<times> (Pow \<Omega> - {{}})" 
  shows  "summedBid (toFunction (bidMaximizedBy a N \<Omega>)) pair = 
          summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0) pair"
proof - 
  have "fst pair \<in> N" using assms by force 
  moreover have "snd pair \<in> Pow \<Omega> - {{}}" using assms(1) by force
  ultimately show ?thesis using lm09 by blast
qed

corollary lm11: 
  "\<forall> pair \<in> N \<times> (Pow \<Omega> - {{}}).  
   summedBid (toFunction (bidMaximizedBy a N \<Omega>)) pair = 
   summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0) pair" 
  using lm10 by blast  

corollary lm12: 
  "(summedBid (toFunction (bidMaximizedBy a N \<Omega>))) ` (N \<times> (Pow \<Omega> - {{}}))=
   (summedBid ((bidMaximizedBy a N \<Omega>) Elsee 0)) ` (N \<times> (Pow \<Omega> - {{}}))" 
  (is "?f1 ` ?Z = ?f2 ` ?Z")
proof - 
  have "\<forall> z \<in> ?Z. ?f1 z = ?f2 z" by (rule lm11) 
  thus ?thesis by (rule functionEquivalenceOnSets)
qed

corollary lm13: 
  "summedBidVectorRel (toFunction (bidMaximizedBy a N \<Omega>)) N \<Omega> =
   summedBidVectorRel ((bidMaximizedBy a N \<Omega>) Elsee 0) N \<Omega>" 
  using lm12 by metis

corollary maxbidEquivalence: 
  "summedBidVectorRel (maxbid a N \<Omega>) N \<Omega> = 
   summedBidVectorRel (maxbidAlg a N \<Omega>) N \<Omega>"
  unfolding maxbidAlg_def using lm13 by metis

lemma summedBidVectorEquivalence: 
  assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" 
  shows "summedBidVector (maxbid a N \<Omega>) N \<Omega> x = summedBidVectorAlg (maxbidAlg a N \<Omega>) N \<Omega> x"
  (is "?f1 ?g1 N \<Omega> x = ?f2 ?g2 N \<Omega> x")
proof -
  let ?h1 = "maxbid a N \<Omega>" 
  let ?h2 = "maxbidAlg a N \<Omega>" 
  have "summedBidVectorRel ?h1 N \<Omega> = summedBidVectorRel ?h2 N \<Omega>" 
    using maxbidEquivalence by metis 
  moreover have "summedBidVectorAlg ?h2 N \<Omega> = (summedBidVectorRel ?h2 N \<Omega>) Elsee 0"
    unfolding summedBidVectorAlg_def by fast
  ultimately have " summedBidVectorAlg ?h2 N \<Omega>=summedBidVectorRel ?h1 N \<Omega> Elsee 0" by simp
  moreover have "... x = (toFunction (summedBidVectorRel ?h1 N \<Omega>)) x" 
    using assms functionCompletion summedBidVectorCharacterization by (metis (mono_tags))
  ultimately have "summedBidVectorAlg ?h2 N \<Omega> x = (toFunction (summedBidVectorRel ?h1 N \<Omega>)) x" 
    by (metis (lifting, no_types))
  thus ?thesis by simp
qed

(* TPTP ? *)
corollary chosenAllocationEquivalence: 
  assumes "card N > 0" and "distinct \<Omega>"
  shows  "chosenAllocation N \<Omega> b r = chosenAllocationAlg N \<Omega> b r" 
  using assms allAllocationsBridgingLemma
  by (metis (no_types) chosenAllocationAlg_def comp_apply)

corollary tiebidsBridgingLemma: 
  assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" 
  shows "tiebids a N \<Omega> x = tiebidsAlg a N \<Omega> x" 
  (is "?L=_") 
proof - 
  have "?L = summedBidVector (maxbid a N \<Omega>) N \<Omega> x" by fast 
  moreover have "...= summedBidVectorAlg (maxbidAlg a N \<Omega>) N \<Omega> x" 
    using assms by (rule summedBidVectorEquivalence) 
  ultimately show ?thesis unfolding tiebidsAlg_def by fast
qed 

definition "tiebids'=tiebids"
corollary tiebidsBridgingLemma': 
  assumes "x \<in> (N \<times> (Pow \<Omega> - {{}}))" 
  shows "tiebids' a N \<Omega> x = tiebidsAlg a N \<Omega> x"
using assms tiebidsBridgingLemma tiebids'_def by metis 

abbreviation "resolvingBid' N G bids random == 
  tiebids' (chosenAllocation N G bids random) N (set G)"

lemma resolvingBidEquivalence: 
  assumes "x \<in> (N \<times> (Pow (set \<Omega>) - {{}}))"  "card N > 0" "distinct \<Omega>"
  shows "resolvingBid' N \<Omega> b r x = resolvingBidAlg N \<Omega> b r x" 
  using assms chosenAllocationEquivalence tiebidsBridgingLemma' resolvingBidAlg_def by metis
  
lemma sumResolvingBidEquivalence:
  assumes "card N > 0" "distinct \<Omega>" "a \<subseteq> (N \<times> (Pow (set \<Omega>) - {{}}))" 
  shows "sum (resolvingBid' N \<Omega> b r) a = sum (resolvingBidAlg N \<Omega> b r) a" 
  (is "?L=?R")
proof - 
    have "\<forall>x\<in>a. resolvingBid' N \<Omega> b r x = resolvingBidAlg N \<Omega> b r x" 
      using assms resolvingBidEquivalence by blast
    thus ?thesis using sum.cong by force 
qed

lemma resolvingBidBridgingLemma: 
  assumes "card N > 0" "distinct \<Omega>" "a \<subseteq> (N \<times> (Pow (set \<Omega>) - {{}}))" 
  shows "sum (resolvingBid N \<Omega> b r) a = sum (resolvingBidAlg N \<Omega> b r) a" 
  (is "?L=?R")
proof - 
  have "?L=sum (resolvingBid' N \<Omega> b r) a" unfolding tiebids'_def by fast
  moreover have "...=?R" 
  using assms by (rule sumResolvingBidEquivalence) 
  ultimately show ?thesis by simp
qed

lemma allAllocationsInPowerset: 
  "allAllocations N \<Omega> \<subseteq> Pow (N \<times> (Pow \<Omega> - {{}}))" 
  by (metis PowI allocationPowerset subsetI)

corollary resolvingBidBridgingLemmaVariant1: 
  assumes "card N > 0" "distinct \<Omega>" "a \<in> allAllocations N (set \<Omega>)" 
  shows "sum (resolvingBid N \<Omega> b r) a = sum (resolvingBidAlg N \<Omega> b r) a"
proof -
  have "a \<subseteq> N \<times> (Pow (set \<Omega>) - {{}})" using assms(3) allAllocationsInPowerset by blast 
  thus ?thesis using assms(1,2) resolvingBidBridgingLemma by blast
qed

corollary resolvingBidBridgingLemmaVariant2: 
  assumes "finite N" "distinct \<Omega>" "a \<in> maximalStrictAllocations N (set \<Omega>) b" 
  shows "sum (randomBids N \<Omega> b r) a = sum (randomBidsAlg N \<Omega> b r) a"
proof - 
  have "card (N\<union>{seller}) > 0" using assms(1) sup_eq_bot_iff insert_not_empty
    by (metis card_gt_0_iff finite.emptyI finite.insertI finite_UnI)
  moreover have "distinct \<Omega>" using assms(2) by simp
  moreover have "a \<in> allAllocations (N\<union>{seller}) (set \<Omega>)" using assms(3) by fastforce
  ultimately show ?thesis unfolding randomBidsAlg_def by (rule resolvingBidBridgingLemmaVariant1)
qed

corollary tiebreakingGivesSingleton: 
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card (argmax (sum (randomBidsAlg N \<Omega> b r)) 
                      (maximalStrictAllocations N (set \<Omega>) b)) = 
         1"
proof -
  have "\<forall> a \<in> maximalStrictAllocations N (set \<Omega>) b. 
        sum (randomBids N \<Omega> b r) a = sum (randomBidsAlg N \<Omega> b r) a" 
    using assms(3,1) resolvingBidBridgingLemmaVariant2 by blast
  then have "argmax (sum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b) =
             argmax (sum (randomBids N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b)" 
    using argmaxEquivalence by blast
  moreover have "card ... = 1" using assms by (rule vcgaDefinitenessVariant)
  ultimately show ?thesis by simp
qed

theorem maximalAllocationBridgingTheorem:
  assumes "finite N" "distinct \<Omega>" 
  shows "maximalStrictAllocations N (set \<Omega>) b = maximalStrictAllocationsAlg N \<Omega> b" 
proof -
  let ?N = "{seller} \<union> N" 
  have "card ?N>0" using assms(1) 
    by (metis (full_types) card_gt_0_iff finite_insert insert_is_Un insert_not_empty)
  thus ?thesis using assms(2) allAllocationsBridgingLemma by metis
qed

theorem vcgaAlgDefinedness:
  assumes "distinct \<Omega>" "set \<Omega> \<noteq> {}" "finite N" 
  shows "card (argmax (sum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocationsAlg N \<Omega> b)) = 1"
proof - 
  have "card (argmax (sum (randomBidsAlg N \<Omega> b r)) (maximalStrictAllocations N (set \<Omega>) b)) = 1"
    using assms by (rule tiebreakingGivesSingleton)
  moreover have "maximalStrictAllocations N (set \<Omega>) b = maximalStrictAllocationsAlg N \<Omega> b" 
    using assms(3,1) by (rule maximalAllocationBridgingTheorem) 
  ultimately show ?thesis by metis
qed

end

