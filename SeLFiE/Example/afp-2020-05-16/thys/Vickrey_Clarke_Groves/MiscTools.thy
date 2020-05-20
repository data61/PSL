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


section \<open>Toolbox of various definitions and theorems about sets, relations and lists\<close>

theory MiscTools 

imports 
"HOL-Library.Discrete"
RelationProperties
"HOL-Library.Code_Target_Nat"
"HOL-Library.Indicator_Function"
Argmax

begin

subsection \<open>Facts and notations about relations, sets and functions.\<close>

(* We use as alternative notation for paste instead of +* also +< and overload this with the next definition *)
notation paste (infix "+<" 75)

text \<open>\<open>+<\<close> abbreviation permits to shorten the notation for altering a function f in a single point by giving a pair (a, b) so that the new function has value b with argument a.\<close>

abbreviation singlepaste
  where "singlepaste f pair == f +* {(fst pair, snd pair)}"
  notation singlepaste (infix "+<" 75)
(* Type of g in f +< g should avoid ambiguities *)

text \<open>\<open>--\<close> abbreviation permits to shorten the notation for considering a function outside a single point.\<close>

abbreviation singleoutside (infix "--" 75)
  where "f -- x \<equiv> f outside {x}"

text \<open>Turns a HOL function into a set-theoretical function\<close>

definition (*Graph :: "('a => 'b) => ('a \<times> 'b) set" where *) 
  "Graph f = {(x, f x) | x . True}"

text \<open>Inverts @{term Graph} (which is equivalently done by @{term eval_rel}).\<close>
(* Assume (x, y) is in R. Apply R to x, i.e., R ,, x,  will result in y assumed y is unique. *)  

definition
  "toFunction R = (\<lambda> x . (R ,, x))"

(* toFunction = eval_rel *)
lemma 
  "toFunction = eval_rel" 
  using toFunction_def by blast

lemma lm001: 
  "((P \<union> Q) || X) = ((P || X) \<union> (Q||X))" 
  unfolding restrict_def by blast

text \<open>update behaves like P +* Q (paste), but without enlarging P's Domain. update is the set theoretic equivalent of the lambda function update @{term fun_upd}\<close>

definition update 
  where "update P Q = P +* (Q || (Domain P))"
  notation update (infix "+^" 75)

(* The operator runiqer will make out of an arbitrary relation a function by making a choice to all those elements in the domain for which the value is not unique by applying the axiom of choice. *)
definition runiqer  :: "('a \<times> 'b) set => ('a \<times> 'b) set"
  where "runiqer R = { (x, THE y. y \<in> R `` {x})| x. x \<in> Domain R }"

text \<open>@{term graph} is like @{term Graph}, but with a built-in restriction to a given set @{term X}.
This makes it computable for finite X, whereas @{term "Graph f || X"} is not computable. 
Duplicates the eponymous definition found in \<open>Function_Order\<close>, which is otherwise not needed.\<close>

definition graph 
  where "graph X f = {(x, f x) | x. x \<in> X}" 

lemma lm002: 
  assumes "runiq R" 
  shows "R \<supseteq> graph (Domain R) (toFunction R)" 
  unfolding graph_def toFunction_def
  using assms graph_def toFunction_def eval_runiq_rel by fastforce

lemma lm003: 
  assumes "runiq R" 
  shows "R \<subseteq> graph (Domain R) (toFunction R)" 
  unfolding graph_def toFunction_def
  using assms eval_runiq_rel runiq_basic Domain.DomainI mem_Collect_eq subrelI by fastforce

lemma lm004: 
  assumes "runiq R" 
  shows "R = graph (Domain R) (toFunction R)"
  using assms lm002 lm003 by fast

lemma domainOfGraph: 
  "runiq(graph X f) & Domain(graph X f)=X" 
  unfolding graph_def 
  using rightUniqueRestrictedGraph by fast

(* The following definition gives the image of a relation R for a fixed element x. It is equivalent to eval_rel for right unique R, but more general since it determines values even when R is not right unique. *)
abbreviation "eval_rel2 (R::('a \<times> ('b set)) set) (x::'a) == \<Union> (R``{x})"
  notation eval_rel2 (infix ",,," 75)

lemma imageEquivalence: 
  assumes "runiq (f::(('a \<times> ('b set)) set))" "x \<in> Domain f" 
  shows "f,,x = f,,,x"
  using assms Image_runiq_eq_eval cSup_singleton by metis

(* UNIV is the universal set containing everything of the given type. It is defined in Set.thy.*)
lemma lm005: 
  "Graph f=graph UNIV f" 
  unfolding Graph_def graph_def by simp

lemma graphIntersection: 
  "graph (X \<inter> Y) f \<subseteq> ((graph X f) || Y)" 
  unfolding graph_def 
  using Int_iff mem_Collect_eq restrict_ext subrelI by auto

definition runiqs 
  where "runiqs={f. runiq f}"

lemma outsideOutside: 
  "((P outside X) outside Y) = P outside (X\<union>Y)" 
  unfolding Outside_def by blast

corollary lm006: 
  "((P outside X) outside X) = P outside X" 
  using outsideOutside by force 

lemma lm007: 
  assumes "(X \<inter> Domain P) \<subseteq> Domain Q" 
  shows "P +* Q = (P outside X) +* Q" 
  unfolding paste_def Outside_def using assms by blast

corollary lm008: 
  "P +* Q = (P outside (Domain Q)) +* Q" 
  using lm007 by fast

corollary outsideUnion: 
  "R = (R outside {x}) \<union> ({x} \<times> (R `` {x}))" 
  using restrict_to_singleton outside_union_restrict by metis

lemma lm009: 
  "P = P \<union> {x}\<times>P``{x}" 
  by (metis outsideUnion sup.right_idem)

corollary lm010: 
  "R = (R outside {x}) +* ({x} \<times> (R `` {x}))" 
  by (metis paste_outside_restrict restrict_to_singleton)

lemma lm011: 
  "R \<subseteq> R +* ({x} \<times> (R``{x}))" 
  using lm010 lm008 paste_def Outside_def by fast

lemma lm012: 
  "R \<supseteq> R+*({x} \<times> (R``{x}))" 
  by (metis Un_least Un_upper1 outside_union_restrict paste_def 
            restrict_to_singleton restriction_is_subrel)

lemma lm013: 
  "R = R +* ({x} \<times> (R``{x}))" 
  using lm011 lm012 by force

lemma rightUniqueTrivialCartes: 
  assumes "trivial Y" 
  shows "runiq (X \<times> Y)" 
  using assms runiq_def Image_subset lm013 trivial_subset lm011 by (metis(no_types))

(* Two constant functions can be combined to a function *)
lemma lm014: 
  "runiq ((X \<times> {x}) +* (Y \<times> {y}))" 
  using rightUniqueTrivialCartes trivial_singleton runiq_paste2 by metis

lemma lm015: 
  "(P || (X \<inter> Y)) \<subseteq> (P||X)    &    P outside (X \<union> Y) \<subseteq> P outside X" 
  using Outside_def restrict_def Sigma_Un_distrib1 Un_upper1 inf_mono Diff_mono subset_refl 
  by (metis (lifting) Sigma_mono inf_le1)

lemma lm016: 
  "P || X \<subseteq> (P||(X \<union> Y))       &    P outside X \<subseteq> P outside (X \<inter> Y)" 
  using lm015 distrib_sup_le sup_idem le_inf_iff subset_antisym sup_commute
  by (metis sup_ge1)

lemma lm017: 
  "P``(X \<inter> Domain P) = P``X" 
  by blast

lemma cardinalityOneSubset: 
  assumes "card X=1" and "X \<subseteq> Y" 
  shows "Union X \<in> Y" 
  using assms cardinalityOneTheElemIdentity by (metis cSup_singleton insert_subset)

lemma cardinalityOneTheElem: 
  assumes "card X=1" "X \<subseteq> Y" 
  shows "the_elem X \<in> Y" 
  using assms by (metis (full_types) insert_subset cardinalityOneTheElemIdentity)

lemma lm018: 
  "(R outside X1) outside X2 = (R outside X2) outside X1" 
  by (metis outsideOutside sup_commute)




subsection \<open>Ordered relations\<close>

(* note that card \<^bold>X\<ge>1 means in Isabelle that X is finite and not empty *)
lemma lm019: 
  assumes "card X\<ge>1" "\<forall>x\<in>X. y > x" 
  shows "y > Max X" 
  using assms by (metis (poly_guards_query) Max_in One_nat_def card_eq_0_iff lessI not_le)

(* assume the function f has a maximum in mx *)
lemma lm020: 
  assumes "finite X" "mx \<in> X" "f x < f mx" 
  shows"x \<notin> argmax f X" 
  using assms not_less by fastforce

lemma lm021: 
  assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" 
  shows "argmax f X \<subseteq> {mx}"
  using assms mk_disjoint_insert by force

lemma lm022: 
  assumes "finite X" "mx \<in> X" "\<forall>x \<in> X-{mx}. f x < f mx" 
  shows "argmax f X = {mx}" 
  using assms lm021 by (metis argmax_non_empty_iff equals0D subset_singletonD)

(* The following corollary is essentially the same as lm022, however, is simplifies a proof in UniformTieBreaking.thy *)
corollary argmaxProperty: 
  "(finite X & mx \<in> X & (\<forall>aa \<in> X-{mx}. f aa < f mx)) \<longrightarrow> argmax f X = {mx}"
  using lm022 by metis

corollary lm023: 
  assumes "finite X" "mx \<in> X" "\<forall>x \<in> X. x \<noteq> mx \<longrightarrow> f x < f mx" 
  shows "argmax f X = {mx}"
  using assms lm022 by (metis Diff_iff insertI1)

lemma lm024: 
  assumes "f \<circ> g = id" 
  shows "inj_on g UNIV" using assms 
  by (metis inj_on_id inj_on_imageI2)

(* Note that Pow X is the powerset of X *)
lemma lm025: 
  assumes "inj_on f X" 
  shows "inj_on (image f) (Pow X)"
  using assms inj_on_image_eq_iff inj_onI PowD by (metis (mono_tags, lifting))

lemma injectionPowerset: 
  assumes "inj_on f Y" "X \<subseteq> Y" 
  shows "inj_on (image f) (Pow X)"
  using assms lm025 by (metis subset_inj_on)

(* the finest possible partition of X, e.g., X = {1, 2, 3} goes to {{1}, {2}, {3}}. *)
definition finestpart 
  where "finestpart X = (%x. {x}) ` X"

lemma finestPart: 
  "finestpart X = {{x}|x . x\<in>X}" 
  unfolding finestpart_def by blast

lemma finestPartUnion: 
  "X=\<Union> (finestpart X)" 
  using finestPart by auto

lemma lm026: 
  "Union \<circ> finestpart = id" 
  using finestpart_def finestPartUnion by fastforce

lemma lm027: 
  "inj_on Union (finestpart ` UNIV)" 
  using lm026 by (metis inj_on_id inj_on_imageI)

lemma nonEqualitySetOfSets: 
  assumes "X \<noteq> Y" 
  shows "{{x}| x. x \<in> X} \<noteq> {{x}| x. x \<in> Y}" 
  using assms by auto

corollary lm028: 
  "inj_on finestpart UNIV" 
  using nonEqualitySetOfSets finestPart by (metis (lifting, no_types) injI)

(* E.g. in the following example, with X = {{1}, {1,2}}, x can be {1} and {1,2} and Y is {{1}} and {{1},{2}}, that is, the lefthand and righthand sides evaluate to {{1},{2}} *)
lemma unionFinestPart: 
  "{Y | Y. \<exists>x.((Y \<in> finestpart x) \<and> (x \<in> X))} = \<Union>(finestpart`X)" 
  by auto

(* Now we specialize the previous lemma to the situation where X consists of a relation (that is is a set of pairs) *)
lemma rangeSetOfPairs: 
  "Range {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> X} = 
   {Y. \<exists>x. ((Y \<in> finestpart x) \<and> (x \<in> Range X))}" 
  by auto

(* Further specialization to a singleton for Y *)
lemma setOfPairsEquality: 
  "{(fst pair, {y})| y pair. y \<in> snd pair & pair \<in> X} = 
   {(fst pair, Y)| Y pair. Y \<in> finestpart (snd pair) & pair \<in> X}"
  using finestpart_def by fastforce

lemma setOfPairs: 
  "{(fst pair, {y})| y. y \<in>  snd pair} = 
   {fst pair} \<times> {{y}| y. y \<in> snd pair}" 
  by fastforce

lemma lm029: 
  "x \<in> X = ({x} \<in> finestpart X)" 
  using finestpart_def by force

lemma pairDifference: 
  "{(x,X)}-{(x,Y)} = {x}\<times>({X}-{Y})" 
  by blast

lemma lm030: 
  assumes "\<Union> P = X" 
  shows "P \<subseteq> Pow X" 
  using assms by blast

lemma lm031: 
  "argmax f {x} = {x}" 
  by auto

lemma sortingSameSet: 
  assumes "finite X" 
  shows "set (sorted_list_of_set X) = X" 
  using assms by simp

(* We assume for the next lemma that f has value in numbers, and sum f A is
   sum f(x) for x in A. *)
lemma lm032: 
  assumes "finite A" 
  shows "sum f A = sum f (A \<inter> B) + sum f (A - B)" 
  using assms by (metis DiffD2 Int_iff Un_Diff_Int Un_commute finite_Un sum.union_inter_neutral)

corollary sumOutside: 
  assumes "finite g" 
  shows "sum f g = sum f (g outside X) + (sum f (g||X))" 
  unfolding Outside_def restrict_def using assms add.commute inf_commute lm032 by (metis)

lemma lm033: 
  assumes "(Domain P \<subseteq> Domain Q)" 
  shows "(P +* Q) = Q"
  unfolding paste_def Outside_def using assms by fast

lemma lm034: 
  assumes "(P +* Q=Q)" 
  shows "(Domain P \<subseteq> Domain Q)"
  using assms paste_def Outside_def by blast

lemma lm035: 
  "(Domain P \<subseteq> Domain Q) = (P +* Q=Q)" 
  using lm033 lm034 by metis

lemma 
  "(P||(Domain Q)) +* Q = Q" 
  by (metis Int_lower2 restrictedDomain lm035)

lemma lm036: 
  "P||X   =   P outside (Domain P - X)" 
  using Outside_def restrict_def by fastforce

lemma lm037: 
  "(P outside X) \<subseteq>    P || ((Domain P)-X)" 
  using lm036 lm016 by (metis Int_commute restrictedDomain outside_reduces_domain)

lemma lm038: 
  "Domain (P outside X) \<inter> Domain (Q || X) = {}" 
  using lm036
  by (metis Diff_disjoint Domain_empty_iff Int_Diff inf_commute restrictedDomain     
            outside_reduces_domain restrict_empty)

lemma lm039: 
  "(P outside X) \<inter> (Q || X) = {}" 
  using lm038 by fast

lemma lm040: 
  "(P outside (X \<union> Y)) \<inter> (Q || X) = {}   &   (P outside X) \<inter> (Q || (X \<inter> Z)) = {}" 
  using Outside_def restrict_def lm039 lm015 by fast

lemma lm041: 
  "P outside X    =    P || ((Domain P) - X)" 
  using Outside_def restrict_def  lm037 by fast

lemma lm042: 
  "R``(X-Y) = (R||X)``(X-Y)" 
  using restrict_def by blast

(* x is a (non-empty) element of the family XX whose union is a subset of X *)
lemma lm043: 
  assumes "\<Union> XX \<subseteq> X" "x \<in> XX" "x \<noteq> {}" 
  shows "x \<inter> X \<noteq> {}" 
  using assms by blast

(* Note that set converts lists such as L1 into sets. L1 is here a list of lists and l an element, that is, a list. We assume furthermore that f2 is constant function with the fixed 2nd argument N. Then we can convert lists to sets in a canonical way. *)
lemma lm044: 
  assumes "\<forall>l \<in> set L1. set L2 = f2 (set l) N" 
  shows "set [set L2. l <- L1]  =  {f2 P N| P. P \<in> set (map set L1)}" 
  using assms by auto

(* Two Variants of the previous lemma *)
lemma setVsList: 
  assumes "\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N" 
  shows "set [set (g2 l N). l <- (g1 G)]  =  {f2 P N| P. P \<in> set (map set (g1 G))}" 
  using assms by auto

lemma lm045: 
  "(\<forall>l \<in> set (g1 G). set (g2 l N) = f2 (set l) N) -->  
     {f2 P N| P. P \<in> set (map set (g1 G))} = set [set (g2 l N). l <- g1 G]" 
  by auto

lemma lm046: 
  assumes "X \<inter> Y  =  {}" 
  shows "R``X = (R outside Y)``X"
  using assms Outside_def Image_def by blast

lemma lm047: 
  assumes "(Range P) \<inter> (Range Q) = {}" "runiq (P^-1)" "runiq (Q^-1)" 
  shows "runiq ((P \<union> Q)^-1)"
  using assms by (metis Domain_converse converse_Un disj_Un_runiq)

lemma lm048: 
  assumes "(Range P) \<inter> (Range Q) = {}" "runiq (P^-1)" "runiq (Q^-1)" 
  shows "runiq ((P +* Q)^-1)"
  using lm047 assms subrel_runiq by (metis converse_converse converse_subset_swap paste_sub_Un)

lemma lm049: 
  assumes "runiq R" 
  shows "card (R `` {a}) = 1 \<longleftrightarrow> a \<in> Domain R"
  using assms card_Suc_eq One_nat_def  
  by (metis Image_within_domain' Suc_neq_Zero assms rightUniqueSetCardinality)

(* triples a can be bracket in any way, i.e., (1st, (2nd, 3rd)) \<rightarrow> ((1st, 2nd), 3rd).*)
lemma lm050: 
  "inj (\<lambda>a. ((fst a, fst (snd a)), snd (snd a)))"
  by (auto intro: injI)

lemma lm051: 
  assumes "finite X" "x > Max X" 
  shows "x \<notin> X" 
  using assms Max.coboundedI by (metis leD)

lemma lm052: 
  assumes "finite A" "A \<noteq> {}" 
  shows "Max (f`A) \<in> f`A" 
  using assms by (metis Max_in finite_imageI image_is_empty)

(* Note that in the following -` means the inverse image of the following set. *)
lemma lm053: 
  "argmax f A \<subseteq> f -` {Max (f ` A)}" 
  by force

lemma lm054: 
  "argmax f A = A \<inter> { x . f x = Max (f ` A) }" 
  by auto

lemma lm055: 
  "(x \<in> argmax f X) = (x \<in> X & f x = Max (f ` X))" 
  using argmax.simps mem_Collect_eq by (metis (mono_tags, lifting))

lemma rangeEmpty: 
  "Range -` {{}} = {{}}" 
  by auto

lemma finitePairSecondRange: 
  "(\<forall> pair \<in> R. finite (snd pair)) = (\<forall> y \<in> Range R. finite y)" 
  by fastforce

lemma lm056: 
  "fst ` P = snd ` (P^-1)" 
  by force

lemma lm057: 
  "fst pair = snd (flip pair) & snd pair = fst (flip pair)" 
  unfolding flip_def by simp

lemma flip_flip2: 
  "flip \<circ> flip   =   id" 
  using flip_flip by fastforce

lemma lm058: 
  "fst = (snd\<circ>flip)" 
  using lm057 by fastforce

lemma lm059: 
  "snd = (fst\<circ>flip)" 
  using lm057 by fastforce

lemma lm060: 
  "inj_on fst P = inj_on (snd\<circ>flip) P" 
  using lm058 by metis

lemma lm062: 
  "inj_on fst P = inj_on snd (P^-1)" 
  using lm060 flip_conv by (metis converse_converse inj_on_imageI lm059)

lemma sumPairsInverse: 
  assumes "runiq (P^-1)" 
  shows "sum (f \<circ> snd) P = sum f (Range P)" 
  using assms lm062 converse_converse rightUniqueInjectiveOnFirst rightUniqueInjectiveOnFirst
        sum.reindex snd_eq_Range 
  by metis

lemma notEmptyFinestpart: 
  assumes "X \<noteq> {}" 
  shows "finestpart X \<noteq> {}" 
  using assms finestpart_def by blast

lemma lm063: 
  assumes "inj_on g X" 
  shows "sum f (g`X) = sum (f \<circ> g) X" 
  using assms by (metis sum.reindex)

lemma functionOnFirstEqualsSecond: 
  assumes "runiq R" "z \<in> R" 
  shows "R,,(fst z) = snd z" 
  using assms by (metis rightUniquePair surjective_pairing)

lemma lm064: 
  assumes "runiq R" 
  shows "sum (toFunction R) (Domain R) = sum snd R" 
  using assms toFunction_def sum.reindex_cong functionOnFirstEqualsSecond
        rightUniqueInjectiveOnFirst 
  by (metis (no_types) fst_eq_Domain)

corollary lm065: 
  assumes "runiq (f||X)" 
  shows "sum (toFunction (f||X)) (X \<inter> Domain f) = sum snd (f||X)" 
  using assms lm064 by (metis Int_commute restrictedDomain)

lemma lm066: 
  "Range (R outside X) = R``((Domain R) - X)"
  by (metis Diff_idemp ImageE Range.intros Range_outside_sub_Image_Domain lm041
            lm042 order_class.order.antisym subsetI)

lemma lm067: 
  "(R||X) `` X = R``X" 
  using Int_absorb doubleRestriction restrictedRange by metis

lemma lm068: 
  assumes "x \<in> Domain (f||X)" 
  shows "(f||X)``{x} = f``{x}" 
  using assms doubleRestriction restrictedRange Int_empty_right Int_iff 
        Int_insert_right_if1 restrictedDomain 
  by metis

lemma lm069: 
  assumes "x \<in> X \<inter> Domain f" "runiq (f||X)" 
  shows "(f||X),,x = f,,x" 
  using assms doubleRestriction restrictedRange Int_empty_right Int_iff Int_insert_right_if1
        eval_rel.simps 
  by metis

lemma lm070: 
  assumes "runiq (f||X)" 
  shows "sum (toFunction (f||X)) (X \<inter> Domain f) = sum (toFunction f) (X \<inter> Domain f)" 
  using assms sum.cong lm069 toFunction_def by metis

corollary sumRestrictedToDomainInvariant: 
  assumes "runiq (f||X)" 
  shows "sum (toFunction f) (X \<inter> Domain f) = sum snd (f||X)" 
  using assms lm065 lm070 by fastforce

corollary sumRestrictedOnFunction: 
  assumes "runiq (f||X)" 
  shows "sum (toFunction (f||X)) (X \<inter> Domain f) = sum snd (f||X)" 
  using assms lm064 restrictedDomain Int_commute by metis

lemma cardFinestpart: 
  "card (finestpart X) = card X" 
  using finestpart_def by (metis (lifting) card_image inj_on_inverseI the_elem_eq)

corollary lm071: 
  "finestpart {} = {}    &    card \<circ> finestpart = card" 
  using cardFinestpart finestpart_def by fastforce

lemma finiteFinestpart: 
  "finite (finestpart X) = finite X" 
  using finestpart_def lm071 
  by (metis card_eq_0_iff empty_is_image finite.simps cardFinestpart)

lemma lm072: 
  "finite \<circ> finestpart = finite" 
  using finiteFinestpart by fastforce

lemma finestpartSubset: 
  assumes "X \<subseteq> Y" 
  shows "finestpart X \<subseteq> finestpart Y" 
  using assms finestpart_def by (metis image_mono)

corollary lm073: 
  assumes "x \<in> X" 
  shows "finestpart x \<subseteq> finestpart (\<Union> X)" 
  using assms finestpartSubset by (metis Union_upper)

lemma lm074: 
  "\<Union> (finestpart ` XX) \<subseteq> finestpart (\<Union> XX)" 
  using finestpart_def lm073 by force

lemma lm075: 
  "\<Union> (finestpart ` XX) \<supseteq> finestpart (\<Union> XX)" 
  (is "?L \<supseteq> ?R") 
  unfolding finestpart_def using finestpart_def by auto

corollary commuteUnionFinestpart: 
  "\<Union> (finestpart ` XX) = finestpart (\<Union> XX)"
  using lm074 lm075 by fast

lemma unionImage: 
  assumes "runiq a" 
  shows "{(x, {y})| x y. y \<in> \<Union> (a``{x}) & x \<in> Domain a} = 
         {(x, {y})| x y. y \<in> a,,x & x \<in> Domain a}" 
  using assms Image_runiq_eq_eval 
  by (metis (lifting, no_types) cSup_singleton)

lemma lm076: 
  assumes "runiq P" 
  shows "card (Domain P) = card P" 
  using assms rightUniqueInjectiveOnFirst card_image by (metis Domain_fst)

lemma finiteDomainImpliesFinite: 
  assumes "runiq f" 
  shows "finite (Domain f) = finite f" 
  using assms Domain_empty_iff card_eq_0_iff finite.emptyI lm076 by metis

(* A relation for the sum of all y\<in>Y of f(x,y) for a fixed x. *)
lemma sumCurry: 
  "sum ((curry f) x) Y = sum f ({x} \<times> Y)"
proof -
  let ?f="% y. (x, y)" let ?g="(curry f) x" let ?h=f
  have "inj_on ?f Y" by (metis(no_types) Pair_inject inj_onI) 
  moreover have "{x} \<times> Y = ?f ` Y" by fast
  moreover have "\<forall> y. y \<in> Y \<longrightarrow> ?g y = ?h (?f y)" by simp
  ultimately show ?thesis using sum.reindex_cong by metis
qed

lemma lm077: 
  "sum (%y. f (x,y)) Y = sum f ({x}\<times>Y)" 
  using sumCurry Sigma_cong curry_def sum.cong by fastforce

corollary lm078: 
  assumes "finite X" 
  shows "sum f X = sum f (X-Y) + (sum f (X \<inter> Y))" 
  using assms Diff_iff IntD2 Un_Diff_Int finite_Un inf_commute sum.union_inter_neutral 
  by metis

lemma lm079: 
  "(P +* Q)``(Domain Q\<inter>X)  =  Q``(Domain Q\<inter>X)" 
  unfolding paste_def Outside_def Image_def Domain_def by blast

corollary lm080: 
  "(P +* Q)``(X\<inter>(Domain Q))  =  Q``X"
  using Int_commute lm079 by (metis lm017)

corollary lm081: 
  assumes "X \<inter> (Domain Q) = {}"
  shows "(P +* Q) `` X = (P outside (Domain Q))`` X" 
  using assms paste_def by fast

lemma lm082: 
  assumes "X\<inter>Y = {}" 
  shows "(P outside Y)``X=P``X" 
  using assms Outside_def by blast

corollary lm083: 
  assumes "X\<inter> (Domain Q) = {}" 
  shows "(P +* Q)``X=P``X" 
  using assms lm081 lm082 by metis

lemma lm084: 
  assumes "finite X" "finite Y" "card(X\<inter>Y) = card X" 
  shows "X \<subseteq> Y" 
  using assms by (metis Int_lower1 Int_lower2 card_seteq order_refl)

lemma cardinalityIntersectionEquality: 
  assumes "finite X" "finite Y" "card X = card Y" 
  shows "(card (X\<inter>Y) = card X)     =    (X = Y)"
  using assms lm084 by (metis card_seteq le_iff_inf order_refl)

lemma lm085: (*fixes f::"'a => 'b" fixes P::"'a => bool" fixes xx::"'a"*) 
  assumes "P xx" 
  shows "{(x,f x)| x. P x},,xx   =   f xx"
proof -
  let ?F="{(x,f x)| x. P x}" let ?X="?F``{xx}"
  have "?X={f xx}" using Image_def assms by blast thus ?thesis by fastforce 
qed

lemma graphEqImage: 
  assumes "x \<in> X" 
  shows "graph X f,,x   =   f x" 
  unfolding graph_def using assms lm085 by (metis (mono_tags) Gr_def)

lemma lm086: 
  "Graph f,,x    =    f x" 
  using UNIV_I graphEqImage lm005 by (metis(no_types))

lemma lm087: 
  "toFunction (Graph f)    =    f"    (is "?L=_") 
proof -
  {fix x have "?L x=f x" unfolding toFunction_def lm086 by metis} 
  thus ?thesis by blast 
qed

lemma lm088: 
  "R outside X \<subseteq> R" 
  by (metis outside_union_restrict subset_Un_eq sup_left_idem)

lemma lm089: 
  "Range(f outside X) \<supseteq> (Range f)-(f``X)" 
  using Outside_def by blast

lemma lm090: 
  assumes "runiq P" 
  shows "(P\<inverse>``((Range P)-Y)) \<inter> ((P\<inverse>)``Y)   =   {}"
  using assms rightUniqueFunctionAfterInverse by blast

lemma lm091: 
  assumes "runiq (P\<inverse>)"
  shows "(P``((Domain P) - X)) \<inter> (P``X)  =  {}"
  using assms rightUniqueFunctionAfterInverse by fast

lemma lm092: 
  assumes "runiq f" "runiq (f^-1)" 
  shows "Range(f outside X) \<subseteq> (Range f)-(f``X)" 
  using assms Diff_triv lm091 lm066 Diff_iff ImageE Range_iff subsetI by metis 

lemma rangeOutside: 
  assumes "runiq f" "runiq (f^-1)" 
  shows "Range(f outside X) = (Range f)-(f``X)" 
  using assms lm089 lm092 by (metis order_class.order.antisym)

(* X and Y are family of sets such that any x and y in X and Y resp. are disjoint. *)
lemma unionIntersectionEmpty: 
  "(\<forall>x\<in>X. \<forall>y\<in>Y. x\<inter>y = {}) = ((\<Union>X)\<inter>(\<Union> Y)={})"
  by blast

lemma setEqualityAsDifference: 
  "{x}-{y} = {}  =  (x = y)" 
  by auto

lemma lm093: 
  assumes "R \<noteq> {}" "Domain R \<inter> X \<noteq> {}" 
  shows "R``X \<noteq> {}" 
  using assms by blast

lemma lm095: 
  "R \<subseteq> (Domain R) \<times> (Range R)" 
  by auto

lemma finiteRelationCharacterization: 
  "(finite (Domain Q) & finite (Range Q)) = finite Q"
  using rev_finite_subset finite_SigmaI lm095 finite_Domain finite_Range by metis

lemma familyUnionFiniteEverySetFinite: 
  assumes "finite (\<Union> XX)" 
  shows "\<forall>X \<in> XX. finite X" 
  using assms by (metis Union_upper finite_subset)

lemma lm096: 
  assumes "runiq f" "X \<subseteq> (f^-1)``Y" 
  shows "f``X \<subseteq> Y" 
  using assms rightUniqueFunctionAfterInverse by (metis Image_mono order_refl subset_trans)

lemma lm097: 
  assumes "y \<in> f``{x}" "runiq f" 
  shows "f,,x = y" 
  using assms by (metis Image_singleton_iff rightUniquePair)




subsection \<open>Indicator function in set-theoretical form.\<close>

abbreviation 
  "Outside' X f == f outside X"

abbreviation 
  "Chi X Y == (Y \<times> {0::nat}) +* (X \<times> {1})"
  notation Chi (infix "<||" 80)

abbreviation 
  "chii X Y == toFunction (X <|| Y)"
  notation chii (infix "<|" 80)

(* X is a set and chi X is a function that returns 1 for elements X and 0 else. *)
abbreviation 
  "chi X == indicator X"

lemma lm098: 
  "runiq (X <|| Y)" 
  by (rule lm014)

lemma lm099: 
  assumes "x \<in> X" 
  shows "1 \<in> (X <|| Y) `` {x}" 
  using assms toFunction_def paste_def Outside_def runiq_def lm014 by blast

lemma lm100: 
  assumes "x \<in> Y-X" 
  shows "0 \<in> (X <|| Y) `` {x}" 
  using assms toFunction_def paste_def Outside_def runiq_def lm014 by blast

lemma lm101: 
  assumes "x \<in> X \<union> Y" 
  shows "(X <|| Y),,x = chi X x" (is "?L=?R") 
  using assms lm014 lm099 lm100 lm097 
  by (metis DiffI Un_iff indicator_simps(1) indicator_simps(2))

lemma lm102: 
  assumes "x \<in> X \<union> Y" 
  shows "(X <| Y) x = chi X x" 
  using assms toFunction_def lm101 by metis

corollary lm103: 
  "sum (X <| Y) (X\<union>Y) = sum (chi X) (X\<union>Y)"
  using lm102 sum.cong by metis

corollary lm104: 
  assumes "\<forall>x\<in>X. f x = g x" 
  shows "sum f X = sum g X" 
  using assms by (metis (poly_guards_query) sum.cong)

corollary lm105: 
  assumes "\<forall>x\<in>X. f x = g x" "Y\<subseteq>X" 
  shows "sum f Y = sum g Y" 
  using assms lm104 by (metis contra_subsetD)

corollary lm106: 
  assumes "Z \<subseteq> X \<union> Y" 
  shows "sum (X <| Y) Z = sum (chi X) Z"  
proof - 
  have "\<forall>x\<in>Z.(X<|Y) x=(chi X) x" using assms lm102 in_mono by metis 
  thus ?thesis using lm104 by blast 
qed

corollary lm107: 
  "sum (chi X) (Z - X) = 0" 
  by simp

corollary lm108: 
  assumes "Z \<subseteq> X \<union> Y" 
  shows "sum (X <| Y) (Z - X) = 0" 
  using assms lm107 lm106 Diff_iff in_mono subsetI by metis

corollary lm109: 
  assumes "finite Z" 
  shows "sum (X <| Y) Z    =    sum (X <| Y) (Z - X)   +  (sum (X <| Y) (Z \<inter> X))" 
  using lm078 assms by blast

corollary lm110: 
  assumes "Z \<subseteq> X \<union> Y" "finite Z" 
  shows "sum (X <| Y) Z = sum (X <| Y) (Z \<inter> X)" 
  using assms lm078 lm108 comm_monoid_add_class.add_0 by metis

corollary lm111: 
  assumes "finite Z" 
  shows "sum (chi X) Z = card (X \<inter> Z)" 
  using assms sum_indicator_eq_card by (metis Int_commute)

corollary lm112: 
  assumes "Z \<subseteq> X \<union> Y" "finite Z" 
  shows "sum (X <| Y) Z = card (Z \<inter> X)"
  using assms lm111 by (metis lm106 sum_indicator_eq_card)

corollary subsetCardinality: 
  assumes "Z \<subseteq> X \<union> Y" "finite Z" 
  shows "(sum (X <| Y) X) - (sum (X <| Y) Z) = card X - card (Z \<inter> X)" 
  using assms lm112 by (metis Int_absorb2 Un_upper1 card_infinite equalityE sum.infinite)

corollary differenceSumVsCardinality: 
  assumes "Z \<subseteq> X \<union> Y" "finite Z" 
  shows "int (sum (X <| Y) X) - int (sum (X <| Y) Z) =  int (card X) - int (card (Z \<inter> X))" 
  using assms lm112 by (metis Int_absorb2 Un_upper1 card_infinite equalityE sum.infinite)

(* type conversion in Isabelle *)
lemma lm113: 
  "int (n::nat) = real n" 
  by simp

(* same as differenceSumVsCardinality but for type real *)
corollary differenceSumVsCardinalityReal: 
  assumes "Z\<subseteq>X\<union>Y" "finite Z" 
  shows "real (sum (X <| Y) X) - real (sum (X <| Y) Z) = 
         real (card X) - real (card (Z \<inter> X))" 
  using assms lm112 by (metis Int_absorb2 Un_upper1 card_infinite equalityE sum.infinite)


subsection \<open>Lists\<close>
(* If there is an element in a list satisfying P, then the list of all elements satisfying P is not the empty list *)
lemma lm114: 
  assumes "\<exists> n \<in> {0..<size l}. P (l!n)" 
  shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []"
  using assms by auto

(* Assume ll is an element of list l, then there is an index n such that the n-th entry of l is ll. *)
lemma lm115: 
  assumes "ll \<in> set (l::'a list)" 
  shows "\<exists> n\<in> (nth l) -` (set l). ll=l!n"
  using assms(1) by (metis in_set_conv_nth vimageI2)

(* variant of the above *)
lemma lm116: 
  assumes "ll \<in> set (l::'a list)" 
  shows "\<exists> n. ll=l!n & n < size l & n >= 0"
  using assms in_set_conv_nth by (metis le0)

(* another variant of the above *)
lemma lm117: 
  assumes "P -` {True} \<inter> set l \<noteq> {}" 
  shows "\<exists> n \<in> {0..<size l}. P (l!n)" 
  using assms lm116 by fastforce

(* variant of lm114 *)
lemma nonEmptyListFiltered: 
  assumes "P -` {True} \<inter> set l \<noteq> {}" 
  shows "[n. n \<leftarrow> [0..<size l], P (l!n)] \<noteq> []" 
  using assms filterpositions2_def lm117 lm114 by metis

(* take the elements of a list l which are also in a set X then this forms a subset of X intersection with the elements of the list *)
lemma lm118: 
  "(nth l) ` set ([n. n \<leftarrow> [0..<size l], (%x. x\<in>X) (l!n)]) \<subseteq> X\<inter>set l" 
  by force

(* variant of the above *)
corollary lm119: 
  "(nth l)` set (filterpositions2 (%x.(x\<in>X)) l) \<subseteq> X \<inter>  set l" 
  unfolding filterpositions2_def using lm118 by fast

lemma lm120: 
  "(n\<in>{0..<N}) = ((n::nat) < N)" 
  using atLeast0LessThan lessThan_iff by metis

(* If X is a set of indices then the corresponding elements combined are a subset of all the elements of the list. *)
lemma lm121: 
  assumes "X \<subseteq> {0..<size list}" 
  shows "(nth list)`X \<subseteq> set list" 
  using assms atLeastLessThan_def atLeast0LessThan lessThan_iff by auto

(* The indices of the elements of a list satisfying a predicate P are a subset of all the indices. *)
lemma lm122: 
  "set ([n. n \<leftarrow> [0..<size l], P (l!n)]) \<subseteq> {0..<size l}" 
  by force

(* variant of the above *)
lemma lm123: 
  "set (filterpositions2 pre list) \<subseteq> {0..<size list}" 
  using filterpositions2_def lm122 by metis



subsection \<open>Computing all the permutations of a list\<close>
abbreviation 
  "rotateLeft == rotate"
abbreviation 
  "rotateRight n l == rotateLeft (size l - (n mod (size l))) l"

(* for n in {0, ..., size l} inserts x in l so that it will have index n in the output*)
(* note that for other n, the behaviour is not guaranteed to be consistent with that *)
abbreviation 
  "insertAt x l n == rotateRight n (x#(rotateLeft n l))"

(* for n in {0,..., fact(size l) - 1 }, 
   perm2 l n gives all and only the possible permutations of l *)
fun perm2 where
  "perm2 [] = (%n. [])" | 
  "perm2 (x#l) = (%n. insertAt x ((perm2 l) (n div (1+size l)))
                      (n mod (1+size l)))"

abbreviation 
  "takeAll P list == map (nth list) (filterpositions2 P list)"

lemma permutationNotEmpty: 
  assumes "l \<noteq> []" 
  shows "perm2 l n \<noteq> []" 
  using assms perm2.simps(2) rotate_is_Nil_conv by (metis neq_Nil_conv)

lemma lm124: 
  "set (takeAll P list) = ((nth list) ` set (filterpositions2 P list))" 
  by simp

corollary listIntersectionWithSet: 
  "set (takeAll (%x.(x\<in>X)) l) \<subseteq>  (X \<inter> set l)" 
  using lm119 lm124 by metis

corollary lm125: 
  "set (takeAll P list) \<subseteq> set list" 
  using lm123 lm124 lm121 by metis

lemma takeAllSubset:
  "set (takeAll (%x. x\<in> P) list) \<subseteq> P"
  by (metis Int_subset_iff listIntersectionWithSet) 

lemma lm126: 
  "set (insertAt x l n) = {x} \<union> set l" 
  by simp

lemma lm127: 
  "\<forall>n. set (perm2 [] n) = set []" 
  by simp

lemma lm128: 
  assumes "\<forall>n. (set (perm2 l n) = set l)" 
  shows "set (perm2 (x#l) n) = {x} \<union> set l" 
  using assms lm126 by force

(* Combining the previous two lemmas we get inductively that the set of elements in a permuted list are the same as the elements in the original list. This is weaker than saying (perm2 l n) is a permutation of l, but suffices for our purposes. *) 
corollary permutationInvariance: 
   "\<forall>n. set (perm2 (l::'a list) n) = set l" 
proof (induct l)
   let ?P = "%l::('a list). (\<forall>n. set (perm2 l n)  =  set l)"
   show "?P []" using lm127 by force 
   fix x fix l 
   assume "?P l" then 
   show "?P (x#l)" by force
qed

(* variant of listIntersectionWithSet with permutation added *)
corollary takeAllPermutation: 
  "set (perm2 (takeAll (%x.(x\<in>X)) l) n)  \<subseteq>  X \<inter> set l" 
  using listIntersectionWithSet permutationInvariance by metis

(* "subList list1 list2" extracts the components of list1 according to the indices given in list2, e.g.,  "subList [1::nat,2,3,4] [0,2]" gives [1,3] *)
abbreviation "subList l xl == map (nth l) (takeAll (%x. x \<le> size l) xl)"


subsection \<open>A more computable version of @{term toFunction}.\<close>

(* If R is a relation and the image of x is unique then take that, else take the fallback *)
abbreviation "toFunctionWithFallback R fallback == 
              (% x. if (R``{x} = {R,,x}) then (R,,x) else fallback)"
notation 
  toFunctionWithFallback (infix "Else" 75)

abbreviation sum' where
  "sum' R X == sum (R Else 0) X"

lemma lm129: 
  assumes "runiq f" "x \<in> Domain f" 
  shows "(f Else 0) x = (toFunction f) x" 
  using assms by (metis Image_runiq_eq_eval toFunction_def)

lemma lm130: 
  assumes "runiq f" 
  shows "sum (f Else 0) (X\<inter>(Domain f))  =  sum (toFunction f) (X\<inter>(Domain f))" 
  using assms sum.cong lm129 by fastforce

lemma lm131: 
  assumes "Y \<subseteq> f-`{0}" 
  shows "sum f Y  =  0" 
  using assms by (metis rev_subsetD sum.neutral vimage_singleton_eq)

lemma lm132: 
  assumes "Y \<subseteq> f-`{0}" "finite X" 
  shows "sum f X = sum f (X-Y)"
  using Int_lower2 add.comm_neutral assms(1) assms(2) lm078 lm131 order_trans
  by (metis (no_types))

(* - means the complement of a set. *)
lemma lm133: 
  "-(Domain f) \<subseteq> (f Else 0)-`{0}" 
  by fastforce

corollary lm134: 
  assumes "finite X" 
  shows "sum (f Else 0) X    =   sum (f Else 0) (X\<inter>Domain f)" 
proof - 
  have "X\<inter>Domain f=X-(-Domain f)" by simp 
  thus ?thesis using assms lm133 lm132 by fastforce
qed

corollary lm135: 
  assumes "finite X" 
  shows "sum (f Else 0) (X\<inter>Domain f)   =   sum (f Else 0) X"
  (is "?L=?R") 
proof - 
  have "?R=?L" using assms by (rule lm134) 
  thus ?thesis by simp 
qed

corollary lm136: 
  assumes "finite X" "runiq f" 
  shows "sum (f Else 0) X = sum (toFunction f) (X\<inter>Domain f)" 
  (is "?L=?R") 
proof -
  have "?R = sum (f Else 0) (X\<inter>Domain f) " using assms(2) lm130 by fastforce
  moreover have "... = ?L" using assms(1) by (rule lm135) 
  ultimately show ?thesis by presburger
qed

lemma lm137: 
  "sum (f Else 0) X = sum' f X" 
  by fast

corollary lm138: 
  assumes "finite X" "runiq f" 
  shows "sum (toFunction f) (X\<inter>Domain f)   =   sum' f X"
  using assms lm137 lm136 by fastforce

lemma lm139: 
  "argmax (sum' b) = (argmax \<circ> sum') b" 
  by simp

lemma domainConstant: 
  "Domain (Y \<times> {0::nat}) = Y & Domain (X \<times> {1}) = X" 
  by blast

lemma domainCharacteristicFunction: 
  "Domain (X <|| Y) = X \<union> Y" 
  using domainConstant paste_Domain sup_commute by metis

lemma functionEquivalenceOnSets: 
  assumes "\<forall>x \<in> X. f x = g x" 
  shows "f`X = g`X" 
  using assms by (metis image_cong)


subsection \<open>Cardinalities of sets.\<close>
lemma lm140: 
  assumes "runiq R" "runiq (R^-1)" 
  shows "(R``A) \<inter> (R``B) = R``(A\<inter>B)" 
  using assms rightUniqueInjectiveOnFirst converse_Image by force

lemma intersectionEmptyRelationIntersectionEmpty: 
  assumes "runiq (R^-1)" "runiq R" "X1 \<inter> X2 = {}" 
  shows "(R``X1) \<inter> (R``X2) = {}"
  using assms by (metis disj_Domain_imp_disj_Image inf_assoc inf_bot_right)

lemma lm141: 
  assumes "runiq f" "trivial Y" 
  shows "trivial (f `` (f^-1 `` Y))"
  using assms by (metis rightUniqueFunctionAfterInverse trivial_subset)

lemma lm142: 
  assumes "trivial X" 
  shows "card (Pow X)\<in>{1,2}" 
  using trivial_empty_or_singleton card_Pow Pow_empty assms trivial_implies_finite
        cardinalityOneTheElemIdentity power_one_right the_elem_eq 
  by (metis insert_iff)

lemma lm143: 
  assumes "card (Pow A) = 1" 
  shows "A = {}" 
  using assms by (metis Pow_bottom Pow_top cardinalityOneTheElemIdentity singletonD)

(* Note that in Isabelle infinite sets have cardinality 0 *) 
lemma lm144: 
  "(\<not> (finite A)) = (card (Pow A) = 0)" 
  by auto

corollary lm145: 
  "(finite A) = (card (Pow A) \<noteq> 0)" 
  using lm144 by metis

lemma lm146: 
  assumes "card (Pow A) \<noteq> 0" 
  shows "card A=Discrete.log (card (Pow A))" 
  using assms log_exp card_Pow by (metis card_infinite finite_Pow_iff)

lemma log_2 [simp]:
  "Discrete.log 2 = 1"
  using log_exp [of 1] by simp

lemma lm147: 
  assumes "card (Pow A) = 2" 
  shows "card A = 1" 
  using assms lm146 [of A] by simp

lemma lm148: 
  assumes "card (Pow X) = 1 \<or> card (Pow X) = 2" 
  shows "trivial X" 
  using assms trivial_empty_or_singleton lm143 lm147 cardinalityOneTheElemIdentity by metis

lemma lm149: 
  "trivial A = (card (Pow A) \<in> {1,2})" 
  using lm148 lm142 by blast

lemma lm150: 
  assumes "R \<subseteq> f" "runiq f" "Domain f = Domain R" 
  shows "runiq R"
  using assms by (metis subrel_runiq)

lemma lm151: 
  assumes "f \<subseteq> g" "runiq g" "Domain f = Domain g" 
  shows "g \<subseteq> f"
  using assms Domain_iff contra_subsetD runiq_wrt_ex1 subrelI
  by (metis (full_types,hide_lams))

lemma lm152: 
  assumes "R \<subseteq> f" "runiq f" "Domain f \<subseteq> Domain R" 
  shows "f = R" 
  using assms lm151 by (metis Domain_mono dual_order.antisym)

lemma lm153: 
  "graph X f = (Graph f) || X" 
  using inf_top.left_neutral lm005 domainOfGraph restrictedDomain lm152 graphIntersection
        restriction_is_subrel subrel_runiq subset_iff 
  by (metis (erased, lifting))

lemma lm154: 
  "graph (X \<inter> Y) f = (graph X f) || Y" 
  using doubleRestriction lm153 by metis

lemma restrictionVsIntersection:
  "{(x, f x)| x. x \<in> X2} || X1 = {(x, f x)| x. x \<in> X2 \<inter> X1}" 
  using graph_def lm154 by metis

lemma lm155: 
  assumes "runiq f" "X \<subseteq> Domain f" 
  shows "graph X (toFunction f) = (f||X)" 
proof -
  have "\<And>v w. (v::'a set) \<subseteq> w \<longrightarrow> w \<inter> v = v" by (simp add: Int_commute inf.absorb1)
  thus "graph X (toFunction f) = f || X" by (metis assms(1) assms(2) doubleRestriction lm004 lm153)
qed

lemma lm156: 
  "(Graph f) `` X = f ` X" 
  unfolding Graph_def image_def by auto

lemma lm157: 
  assumes "X \<subseteq> Domain f" "runiq f" 
  shows "f``X = (eval_rel f)`X"
  using assms lm156 by (metis restrictedRange lm153 lm155 toFunction_def)

lemma cardOneImageCardOne: 
  assumes "card A = 1" 
  shows "card (f`A) = 1" 
  using assms card_image card_image_le 
proof -
  have "finite (f`A)" using assms One_nat_def Suc_not_Zero card_infinite finite_imageI 
       by (metis(no_types)) 
  moreover have "f`A \<noteq> {}" using assms by fastforce
  moreover have "card (f`A) \<le> 1" using assms card_image_le One_nat_def Suc_not_Zero card_infinite
       by (metis)
  ultimately show ?thesis by (metis assms image_empty image_insert 
                                    cardinalityOneTheElemIdentity the_elem_eq)
qed

lemma cardOneTheElem: 
  assumes "card A = 1" 
  shows "the_elem (f`A) = f (the_elem A)" 
  using assms image_empty image_insert the_elem_eq by (metis cardinalityOneTheElemIdentity)

(* With split being the inverse of curry we have with g as swap f,  (g x y) = (f y x) *)
abbreviation 
  "swap f == curry ((case_prod f) \<circ> flip)" (*swaps the two arguments of a function*)

(* X is finite if and only if X is the set of elements of some list. *)
lemma lm158: 
  "finite X   =  (X \<in> range set)" 
  by (metis List.finite_set finite_list image_iff rangeI)

(* as above, just as lambda expression *)
lemma lm159: 
  "finite = (%X. X\<in>range set)" 
  using lm158 by metis

lemma lm160: 
  "swap f = (%x. %y. f y x)" 
  by (metis comp_eq_dest_lhs curry_def flip_def fst_conv old.prod.case snd_conv)



subsection \<open>Some easy properties on real numbers\<close>
lemma lm161: 
  fixes a::real 
  fixes b c 
  shows "a*b - a*c=a*(b-c)"
  by (metis real_scaleR_def real_vector.scale_right_diff_distrib)

lemma lm162: 
  fixes a::real 
  fixes b c 
  shows "a*b - c*b=(a-c)*b"
  using lm161 by (metis mult.commute)

end

