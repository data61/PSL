(*  Author: Gertrud Bauer, Tobias Nipkow *)

section \<open>Enumeration of Tame Plane Graphs\<close>

theory Generator
imports Plane1 Tame
begin


text\<open>\paragraph{Lower bounds for total weight}\<close>


definition faceSquanderLowerBound :: "graph \<Rightarrow> nat" where
"faceSquanderLowerBound g \<equiv> \<Sum>\<^bsub>f \<in> finals g\<^esub> \<d> |vertices f|"

definition d3_const :: nat where
"d3_const == \<d> 3"

definition  d4_const :: nat where
"d4_const == \<d> 4"

definition excessAtType :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"excessAtType t q e \<equiv>
    if e = 0 then if 7 < t + q then squanderTarget
                  else \<b> t q - t * d3_const - q * d4_const
    else if t + q + e \<noteq> 6 then 0
         else if t=5 then \<a> else squanderTarget"

declare d3_const_def[simp] d4_const_def[simp]


definition ExcessAt :: "graph \<Rightarrow> vertex \<Rightarrow> nat" where
 "ExcessAt g v \<equiv> if \<not> finalVertex g v then 0
     else excessAtType (tri g v) (quad g v) (except g v)"


definition ExcessTable :: "graph \<Rightarrow> vertex list \<Rightarrow> (vertex \<times> nat) list" where
 "ExcessTable g vs \<equiv>
     [(v, ExcessAt g v). v \<leftarrow> [v \<leftarrow> vs. 0 < ExcessAt g v ]]"
text\<open>Implementation:\<close>
lemma [code]:
  "ExcessTable g =
   List.map_filter (\<lambda>v. let e = ExcessAt g v in if 0 < e then Some (v, e) else None)"
 by (rule ext) (simp add: ExcessTable_def map_filter_def)

(* FIXME delete stupid removeKeyList *)
definition deleteAround :: "graph \<Rightarrow> vertex \<Rightarrow> (vertex \<times> nat) list \<Rightarrow> (vertex \<times> nat) list" where
 "deleteAround g v ps \<equiv>
      let fs = facesAt g v;
      ws = \<Squnion>\<^bsub>f\<in>fs\<^esub> if |vertices f| = 4 then [f\<bullet>v, f\<^bsup>2\<^esup>\<bullet>v] else [f\<bullet>v] in
      removeKeyList ws ps"
text\<open>Implementation:\<close>
lemma [code]: "deleteAround g v ps =
      (let vs = (\<lambda>f. let n = f\<bullet>v
                     in if |vertices f| = 4 then [n, f\<bullet>n] else [n])
       in removeKeyList (concat(map vs (facesAt g v))) ps)"
  by (simp only: concat_map_singleton Let_def deleteAround_def nextV2)

lemma length_deleteAround: "length (deleteAround g v ps) \<le> length ps"
  by (auto simp only: deleteAround_def length_removeKeyList Let_def)

function ExcessNotAtRec :: "(nat, nat) table \<Rightarrow> graph \<Rightarrow> nat" where
 "ExcessNotAtRec [] = (\<lambda>g. 0)"
 | "ExcessNotAtRec ((x, y)#ps) = (\<lambda>g.  max (ExcessNotAtRec ps g)
         (y + ExcessNotAtRec (deleteAround g x ps) g))"
by pat_completeness auto
termination by (relation "measure size") 
  (auto simp add: length_deleteAround less_Suc_eq_le)

definition ExcessNotAt :: "graph \<Rightarrow> vertex option \<Rightarrow> nat" where
 "ExcessNotAt g v_opt \<equiv>
     let ps = ExcessTable g (vertices g) in
     case v_opt of None \<Rightarrow>  ExcessNotAtRec ps g
      | Some v \<Rightarrow> ExcessNotAtRec (deleteAround g v ps) g"

definition squanderLowerBound :: "graph \<Rightarrow> nat" where
 "squanderLowerBound g \<equiv>  faceSquanderLowerBound g + ExcessNotAt g None"



text\<open>\paragraph{Tame graph enumeration}\<close>

definition is_tame13a :: "graph \<Rightarrow> bool" where
"is_tame13a g \<equiv> squanderLowerBound g < squanderTarget"

definition notame :: "graph \<Rightarrow> bool" where
"notame g \<equiv> \<not> (tame10ub g \<and> tame11b g)"

definition notame7 :: "graph \<Rightarrow> bool" where
"notame7 g \<equiv> \<not> (tame10ub g \<and> tame11b g \<and> is_tame13a g)"

definition generatePolygonTame :: "nat \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> graph \<Rightarrow> graph list" where
"generatePolygonTame n v f g \<equiv>
     let
     enumeration = enum n |vertices f|;
     enumeration = [is \<leftarrow> enumeration. \<not> containsDuplicateEdge g f v is];
     vertexLists = [indexToVertexList f v is. is \<leftarrow> enumeration]
     in
     [g' \<leftarrow> [subdivFace g f vs. vs \<leftarrow> vertexLists] . \<not> notame g']"

definition polysizes :: "nat \<Rightarrow> graph \<Rightarrow> nat list" where
"polysizes p g \<equiv>
    let lb = squanderLowerBound g in
    [n \<leftarrow> [3 ..< Suc(maxGon p)]. lb + \<d> n < squanderTarget]"

definition next_tame0 :: "nat \<Rightarrow> graph \<Rightarrow> graph list" ("next'_tame0\<^bsub>_\<^esub>") where
"next_tame0\<^bsub>p\<^esub> g \<equiv>
     let fs = nonFinals g in
     if fs = [] then []
     else let f = minimalFace fs; v = minimalVertex g f
          in \<Squnion>\<^bsub>i \<in> polysizes p g\<^esub> generatePolygonTame i v f g"

text\<open>\noindent Extensionally, @{const next_tame0} is just
@{term"filter P \<circ> next_plane p"} for some suitable \<open>P\<close>. But
efficiency suffers considerably if we first create many graphs and
then filter out the ones not in @{const polysizes}.\<close>

end
