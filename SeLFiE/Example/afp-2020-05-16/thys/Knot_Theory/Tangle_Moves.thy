section\<open>Tangle\_Moves: Defining moves on tangles\<close>

theory Tangle_Moves
imports Tangles Tangle_Algebra Tangle_Relation
begin


text\<open>Two Links diagrams represent the same link if and only if the diagrams can be related by a 
set of moves called the reidemeister moves. For links defined through Tangles, addition set of moves 
are needed to account for different tangle representations of the same link diagram.

We formalise these 'moves' in terms of relations. Each move is defined as a relation on diagrams. 
Two diagrams are then stated to be equivalent if the reflexive-symmetric-transitive closure of the 
disjunction of above relations holds true. A Link is defined as an element of the quotient type of
diagrams modulo equivalence relations. We formalise the definition of framed links on similar lines. 

In terms of formalising the moves, there is a trade off between choosing a small number of moves
from which all other moves can be obtained, which is conducive to probe invariance of a function 
on diagrams. However, such an approach might not be conducive to establish equivalence of two 
diagrams. We opt for the former approach of minimising the number of tangle moves. 
However, the moves that would be useful in practise are proved as theorems in
\<close>


type_synonym relation = "wall \<Rightarrow> wall \<Rightarrow> bool" 

text\<open>Link uncross\<close>

abbreviation right_over::"wall"
where
"right_over \<equiv>   ((basic [vert,cup]) \<circ> (basic [over,vert])\<circ>(basic [vert,cap]))"


abbreviation left_over::"wall"
where
" left_over \<equiv> ((basic (cup#vert#[])) \<circ> (basic (vert#over#[]))
\<circ> (basic (cap#vert#[])))"

abbreviation right_under::"wall"
where
"right_under \<equiv>   ((basic (vert#cup#[])) \<circ> (basic (under#vert#[]))
\<circ> (basic (vert#cap#[])))"


abbreviation left_under::"wall"
where
" left_under \<equiv> ((basic (cup#vert#[])) \<circ> (basic (vert#under#[]))
\<circ> (basic (cap#vert#[])))"

abbreviation straight_line::"wall"
where
"straight_line \<equiv> (basic (vert#[])) \<circ> (basic (vert#[])) \<circ> (basic (vert#[]))"

definition uncross_positive_flip::relation
where
"uncross_positive_flip x y \<equiv> ((x = right_over)\<and>(y =  left_over))"

definition uncross_positive_straighten::relation
where
"uncross_positive_straighten x y \<equiv> ((x = right_over)\<and>(y = straight_line))"

definition uncross_negative_flip::relation
where
"uncross_negative_flip x y \<equiv> ((x = right_under)\<and>(y =  left_under))"


definition uncross_negative_straighten::relation
where
"uncross_negative_straighten x y \<equiv> ((x = left_under)\<and>(y = straight_line))"

(*The relation uncross*)
definition uncross
where
"uncross x y \<equiv> ((uncross_positive_straighten x y)\<or>(uncross_positive_flip x y)
                \<or>(uncross_negative_straighten x y)\<or> (uncross_negative_flip x y))"



text\<open>swing begins\<close>

abbreviation r_over_braid::"wall"
where
"r_over_braid  \<equiv>  ((basic ((over#vert#[]))\<circ>(basic ((vert#over#[])))
                 \<circ>(basic (over# vert#[]))))"



abbreviation l_over_braid::"wall"
where
"l_over_braid  \<equiv>   (basic (vert#over#[]))\<circ>(basic (over#vert#[]))
                    \<circ>(basic (vert#over#[]))"


abbreviation r_under_braid::"wall"
where
"r_under_braid  \<equiv>   ((basic ((under#vert#[]))\<circ>(basic ((vert#under#[])))
                 \<circ>(basic (under# vert#[]))))"

abbreviation l_under_braid::"wall"
where
"l_under_braid  \<equiv>   (basic (vert#under#[]))\<circ>(basic (under#vert#[]))
                    \<circ>(basic (vert#under#[]))"

definition swing_pos::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"swing_pos x y \<equiv> (x = r_over_braid)\<and>(y = l_over_braid)"

definition swing_neg::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"swing_neg x y \<equiv>(x = r_under_braid)\<and>(y=l_under_braid)"

definition swing::relation
where
"swing x y \<equiv> (swing_pos x y)\<or>(swing_neg x y)"

text\<open>pull begins\<close>

definition pull_posneg::relation
where
"pull_posneg x y \<equiv>  ((x = ((basic (over#[]))\<circ>(basic  (under#[]))))
                            \<and>(y = ((basic (vert#vert#[])))
                                   \<circ>(basic ((vert#vert#[])))))"


definition pull_negpos::relation
where
"pull_negpos x y \<equiv>  ((x = ((basic (under#[]))\<circ>(basic  (over#[]))))
                          \<and>(y = ((basic (vert#vert#[])))
                                   \<circ>(basic ((vert#vert#[])))))"

text\<open>pull definition\<close>
definition pull::relation
where
"pull x y \<equiv> ((pull_posneg x y) \<or> (pull_negpos x y))"                   

text\<open>linkrel-pull ends\<close>    
text\<open>linkrel-straighten\<close>

definition straighten_topdown::relation
where
"straighten_topdown x y \<equiv>  ((x =((basic ((vert#cup#[])))
                                         \<circ>(basic ((cap#vert#[])))))
                                   \<and>(y = ((basic (vert#[]))\<circ>(basic (vert#[])))))"



definition straighten_downtop::relation
where
"straighten_downtop x y \<equiv>  ((x =((basic ((cup# vert#[])))
                                         \<circ>(basic ((vert# cap#[])))))
                                   \<and>(y = ((basic (vert#[]))\<circ>(basic (vert#[])))))"




text\<open>definition straighten\<close>
definition straighten::relation
where
"straighten x y \<equiv> ((straighten_topdown x y) \<or> (straighten_downtop x y))"



text\<open>straighten ends\<close>
text\<open>rotate moves\<close>

definition rotate_toppos::relation
where
"rotate_toppos x y \<equiv>  ((x = ((basic ((vert #over#[])))
                                     \<circ>(basic ((cap# vert#[])))))
                             \<and> (y = ((basic ((under#vert#[]))
                                     \<circ>(basic ((vert#cap#[])))))))"

definition rotate_topneg::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"rotate_topneg x y \<equiv>  ((x = ((basic ((vert #under#[])))
                                     \<circ>(basic ((cap# vert#[])))))
                             \<and> (y = ((basic ((over#vert#[]))
                                     \<circ>(basic ((vert#cap#[])))))))"


definition rotate_downpos::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"rotate_downpos x y \<equiv>  ((x = ((basic (cup#vert#[]))
                                     \<circ>(basic (vert#over#[]))))
                             \<and> (y = ((basic ((vert#cup#[])))
                                    \<circ>(basic ((under#vert#[]))))))"



definition rotate_downneg::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"rotate_downneg x y \<equiv>  ((x = ((basic (cup#vert#[]))
                                     \<circ>(basic (vert#under#[]))))
                             \<and> (y = ((basic ((vert#cup#[])))
                                    \<circ>(basic ((over#vert#[]))))))"


text\<open>rotate definition\<close>


definition rotate::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"rotate x y \<equiv> ((rotate_toppos x y) \<or> (rotate_topneg x y)
\<or> (rotate_downpos x y) \<or> (rotate_downneg x y))"

text\<open>rotate ends\<close>


text\<open>Compress -  Compress has two levels of equivalences. It is a composition of Compress-null, compbelow
and compabove. compbelow and compabove are further written as disjunction of many other relations.
Compbelow refers to when the bottom row is extended or compressed. Compabove refers to when the 
row above is extended or compressed\<close>

definition compress_top1::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"compress_top1 x y \<equiv>  \<exists>B.((x = (basic (make_vert_block (nat (domain_wall B))))\<circ> B)
                              \<and>(y = B)\<and>(codomain_wall B \<noteq> 0)
                               \<and>(is_tangle_diagram B))"

definition compress_bottom1::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"compress_bottom1 x y \<equiv>  \<exists>B.((x = B \<circ> (basic (make_vert_block (nat (codomain_wall B)))))
                              \<and>(y =  B))\<and>(domain_wall B \<noteq> 0)
                               \<and>(is_tangle_diagram B)"

definition compress_bottom::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"compress_bottom x y \<equiv>   \<exists>B.((x = B \<circ> (basic (make_vert_block (nat (codomain_wall B)))))
                              \<and>(y = ((basic ([]) \<circ> B)))\<and>(domain_wall B = 0)
                               \<and>(is_tangle_diagram B))"

definition compress_top::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"compress_top x y \<equiv>  \<exists>B.((x = (basic (make_vert_block (nat (domain_wall B))))\<circ> B)
                              \<and>(y = (B \<circ> (basic ([]))))\<and>(codomain_wall B = 0)
                               \<and>(is_tangle_diagram B))"


(*compress*)
definition compress::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"compress x y = ((compress_top x y) \<or> (compress_bottom x y))"
(*(compress_top1 x y) \<or> (compress_bottom1 x y))*)
text\<open>slide relation refer to the relation where a crossing is slided over a vertical strand\<close>
definition slide::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"slide x y \<equiv>  \<exists>B.((x = ((basic (make_vert_block (nat (domain_block B))))\<circ>(basic B)))
               \<and>(y = ((basic B)\<circ>(basic (make_vert_block (nat (codomain_block B))))))
\<and> ((domain_block B) \<noteq> 0))"
(*can integrate slide and compress using domain-codomain fundas.
ALSO check for domain and codomain in the above equations*)
text\<open>linkrel-definition\<close>

definition linkrel::"wall =>wall \<Rightarrow>bool"
where
"linkrel x y = ((uncross x y) \<or> (pull x y) \<or> (straighten x y) 
\<or>(swing x y)\<or>(rotate x y) \<or> (compress x y) \<or> (slide x y))"


definition framed_uncross::"wall \<Rightarrow> wall \<Rightarrow> bool"
where
"framed_uncross x y \<equiv> ((uncross_positive_flip x y)\<or>(uncross_negative_flip x y))"

definition framed_linkrel::"wall =>wall \<Rightarrow>bool"
where
"framed_linkrel x y = ((framed_uncross x y) \<or> (pull x y) \<or> (straighten x y) 
\<or>(swing x y)\<or>(rotate x y) \<or> (compress x y) \<or> (slide x y))"



lemma framed_uncross_implies_uncross: "(framed_uncross x y)\<Longrightarrow>(uncross x y)"
 by (auto simp add: framed_uncross_def uncross_def)


end
