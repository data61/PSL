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

section \<open>Locus where a function or a list (of linord type) attains its maximum value\<close>

theory Argmax
imports Main

begin

text \<open>Structural induction is used in proofs on lists.\<close>
lemma structInduct: assumes "P []" and "\<forall>x xs. P (xs) \<longrightarrow> P (x#xs)" 
                    shows "P l" 
      using assms list_nonempty_induct by (metis)

text \<open>the subset of elements of a set where a function reaches its maximum\<close>
fun argmax :: "('a \<Rightarrow> 'b::linorder) \<Rightarrow> 'a set \<Rightarrow> 'a set"
    where "argmax f A = { x \<in> A . f x = Max (f ` A) }"

(* For reasons we do not understand we have to duplicate the definition as a lemma 
   in order to prove lm16 in CombinatorialAuctions.thy. *)
lemma argmaxLemma: "argmax f A = { x \<in> A . f x = Max (f ` A) }" 
  by simp

lemma maxLemma: 
  assumes "x \<in> X" "finite X" 
  shows "Max (f`X) >= f x" 
  (is "?L >= ?R") using assms 
  by (metis (hide_lams, no_types) Max.coboundedI finite_imageI image_eqI)

lemma lm01: 
  "argmax f A = A \<inter> f -` {Max (f ` A)}" 
  by force

lemma lm02: 
  assumes "y \<in> f`A" 
  shows "A \<inter> f -` {y} \<noteq> {}" 
  using assms by blast

lemma argmaxEquivalence: 
  assumes "\<forall>x\<in>X. f x = g x" 
  shows "argmax f X = argmax g X" 
  using assms argmaxLemma Collect_cong image_cong 
  by (metis(no_types,lifting))

text \<open>The arg max of a function over a non-empty set is non-empty.\<close>
corollary argmax_non_empty_iff: assumes "finite X" "X \<noteq> {}" 
                                shows "argmax f X \<noteq>{}"
                                using assms Max_in finite_imageI image_is_empty lm01 lm02 
                                by (metis(no_types))

text \<open>The previous definition of argmax operates on sets. In the following we define a corresponding notion on lists. To this end, we start with defining a filter predicate and are looking for the elements of a list satisfying a given predicate;
but, rather than returning them directly, we return the (sorted) list of their indices. 
This is done, in different ways, by @{term filterpositions} and @{term filterpositions2}.\<close>

(* Given a list l, filterpositions yields the indices of its elements which satisfy a given pred P*)
definition filterpositions :: "('a => bool) => 'a list => nat list"
           where "filterpositions P l = map snd (filter (P o fst) (zip l (upt 0 (size l))))"
(* That is, you take the list [a0, a1, ..., an] pair with the indices [0, 1, ..., n], i.e., you get
   [(a0,0), (a1,1), ..., (an,n)] look where the predicate (P o fst) holds and return the list of the
   corresponding snd elements. *)


(* Alternative definition, making use of list comprehension. In the next line the type info is
   commented out, since the type inference can be left to Isabelle. *)
definition filterpositions2 (*  :: "('a => bool) => 'a list => nat list" *)
           where "filterpositions2 P l = [n. n \<leftarrow> [0..<size l], P (l!n)]"

definition maxpositions (*:: "'a::linorder list => nat list"*) 
           where "maxpositions l = filterpositions2 (%x . x \<ge> Max (set l)) l"

lemma lm03: "maxpositions l = [n. n\<leftarrow>[0..<size l], l!n \<ge> Max(set l)]" 
      unfolding maxpositions_def filterpositions2_def by fastforce

(* argmaxList takes a function and a list as arguments and looks for the positions of the elements at which the function applied to the list element is maximal, e.g., 
for the list [9, 3, 5, 9, 13] and the function `modulo 8', the function applied to the list would give the list [1, 3, 5, 1, 5], that is, argmaxList will return [2, 4]. *)
definition argmaxList (*:: "('a => ('b::linorder)) => 'a list => 'a list"*)
           where "argmaxList f l = map (nth l) (maxpositions (map f l))"

(* The following lemmas state some relationships between different representation such as map and list comprehension *)
lemma lm04: "[n . n <- l, P n] = [n . n <- l, n \<in> set l, P n]" 
proof - 
(*sledgehammer-generated proof. 
  Commented out the first three lines (they look quite useless), making it more readable. 
  assume "\<forall>v0. SMT2.fun_app uu__ v0 = (if P v0 then [v0] else [])"
  assume "\<forall>v0. SMT2.fun_app uua__ v0 = (if v0 \<in> set l then if P v0 then [v0] else [] else [])" 
  obtain v3_0 :: "('a \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a list) \<Rightarrow> 'a" where *) 
  have "map (\<lambda>uu. if P uu then [uu] else []) l = 
    map (\<lambda>uu. if uu \<in> set l then if P uu then [uu] else [] else []) l" by simp
  thus "concat (map (\<lambda>n. if P n then [n] else []) l) = 
    concat (map (\<lambda>n. if n \<in> set l then if P n then [n] else [] else []) l)" by presburger
qed

lemma lm05: "[n . n <- [0..<m], P n] = [n . n <- [0..<m], n \<in> set [0..<m], P n]" 
      using lm04 by fast
 (* sledgehammer suggested:  concat_map_singleton map_ident  map_ext by smt*)

lemma lm06: fixes f m P 
            shows "(map f [n . n <- [0..<m], P n]) = [ f n . n <- [0..<m], P n]" 
      by (induct m) auto

(* Base case stating the property for the empty list *)
lemma map_commutes_a: "[f n . n <- [], Q (f n)] = [x <- (map f []). Q x]" 
      by simp

(* Step case where the element x is added to the list xs *)
lemma map_commutes_b: "\<forall> x xs. ([f n . n <- xs,     Q (f n)] = [x <- (map f xs).     Q x] \<longrightarrow> 
                                [f n . n <- (x#xs), Q (f n)] = [x <- (map f (x#xs)). Q x])" 
      by simp

(* General case comprising the two previous cases. *)
lemma map_commutes: fixes f::"'a => 'b" fixes Q::"'b => bool" fixes xs::"'a list" 
                    shows "[f n . n <- xs, Q (f n)] = [x <- (map f xs). Q x]"
      using map_commutes_a map_commutes_b structInduct by fast

lemma lm07: fixes f l 
            shows "maxpositions (map f l) = 
                   [n . n <- [0..<size l], f (l!n) \<ge> Max (f`(set l))]" 
            (is "maxpositions (?fl) = _") (* Pattern matching abbreviation ?fl corresponds to (map f l). Used in the proof, not part of lemma itself *)
proof -
  have "maxpositions ?fl = 
  [n. n <- [0..<size ?fl], n\<in> set[0..<size ?fl], ?fl!n \<ge> Max (set ?fl)]"
  using lm04 unfolding filterpositions2_def maxpositions_def .
  also have "... = 
  [n . n <- [0..<size l], (n<size l), (?fl!n  \<ge> Max (set ?fl))]" by simp
  also have "... = 
  [n . n <- [0..<size l], (n<size l) \<and> (f (l!n)  \<ge> Max (set ?fl))]" 
  using nth_map by (metis (poly_guards_query, hide_lams)) also have "... = 
  [n . n <- [0..<size l], (n\<in> set [0..<size l]),(f (l!n)  \<ge> Max (set ?fl))]" 
  using atLeastLessThan_iff le0 set_upt by (metis(no_types))
  also have "... =  
  [n . n <- [0..<size l], f (l!n) \<ge> Max (set ?fl)]" using lm05 by presburger 
  finally show ?thesis by auto
qed

lemma lm08: fixes f l 
            shows "argmaxList f l = 
                   [ l!n . n <- [0..<size l], f (l!n) \<ge> Max (f`(set l))]"
      unfolding lm07 argmaxList_def by (metis lm06)

text\<open>The theorem expresses that argmaxList is the list of arguments greater equal the Max of the list.\<close>

theorem argmaxadequacy: fixes f::"'a => ('b::linorder)" fixes l::"'a list" 
                        shows "argmaxList f l = [ x <- l. f x \<ge> Max (f`(set l))]"
                        (is "?lh=_") (* pattern match ?lh abbreviates "argmaxList f l" *)
proof -
  let ?P="% y::('b::linorder) . y \<ge> Max (f`(set l))"
  let ?mh="[nth l n . n <- [0..<size l], ?P (f (nth l n))]"
  let ?rh="[ x <- (map (nth l) [0..<size l]). ?P (f x)]"
  have "?lh = ?mh" using lm08 by fast
  also have "... = ?rh" using map_commutes by fast
  also have "...= [x <- l. ?P (f x)]" using map_nth by metis
  finally show ?thesis by force
qed

end

