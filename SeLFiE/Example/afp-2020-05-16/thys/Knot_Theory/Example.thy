section\<open>Showing equivalence of links: An example\<close>

theory Example
imports Link_Algebra 
begin

text\<open>We prove that a link diagram with a single crossing is equivalent to the 
unknot\<close>

lemma transitive: assumes "a~b" and "b~c" shows "a~c"
    using Tangle_Equivalence.trans assms(1) assms(2) by metis

lemma prelim_cup_compress:
 " ((basic (cup#[])) \<circ> (basic (vert # vert # []))) ~
      ((basic [])\<circ>(basic (cup#[])))"  
proof-
 have "domain_wall (basic (cup # [])) = 0" 
       by auto
 moreover have "codomain_wall (basic (cup # [])) = 2" 
       by auto
 moreover 
     have "make_vert_block (nat (codomain_wall (basic (cup # [])))) 
                                    = (vert # vert # [])"
       unfolding make_vert_block_def 
       by auto
 moreover have "is_tangle_diagram   ((basic (cup#[])) \<circ> (basic (vert # vert # [])))"
      using is_tangle_diagram.simps by auto 
 ultimately 
  have "compress_bottom 
          ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
          ((basic []) \<circ>(basic (cup#[])))" 
      using compress_bottom_def by (metis is_tangle_diagram.simps(1))
 then have "compress  ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
      ((basic [])\<circ>(basic (cup#[])))" 
      using compress_def by auto
 then have "linkrel ((basic (cup#[])) \<circ> (basic (vert # vert # []))) 
      ((basic [])\<circ>(basic (cup#[])))" 
      unfolding linkrel_def by auto
 then show ?thesis 
     using Tangle_Equivalence.equality compress_bottom_def 
           Tangle_Moves.compress_bottom_def Tangle_Moves.compress_def 
           Tangle_Moves.linkrel_def 
     by auto
 qed

lemma cup_compress:
 "(basic (cup#[])) \<circ> (basic (vert # vert # [])) ~ (basic (cup#[]))"
 proof-
 have " ((basic (cup#[])) \<circ> (basic (vert # vert # []))) ~
      ((basic [])\<circ>(basic (cup#[])))"  
         using prelim_cup_compress  by auto
 moreover have "((basic [])\<circ>(basic (cup#[]))) ~  (basic (cup#[]))"
         using domain_compose refl sym Tangle_Equivalence.domain_compose 
         Tangle_Equivalence.sym domain.simps(2) domain_block.simps 
         domain_wall.simps(1) 
         is_tangle_diagram.simps(1) monoid_add_class.add.right_neutral
         by auto
 ultimately show ?thesis using trans by (metis Example.transitive)
 qed
 
abbreviation x::"wall"
where
"x \<equiv>   (basic [cup,cup])\<circ>(basic [vert,over,vert]) \<circ> (basic [cap,cap])"

abbreviation y::"wall"
where
"y \<equiv>    (basic [cup]) \<circ> (basic [cap])"

lemma uncross_straighten_left_over:"left_over ~ straight_line"
proof-
 have "uncross right_over left_over"
        using uncross_positive_flip_def uncross_def by auto
 then have "linkrel right_over left_over"
    using linkrel_def by auto
 then have "right_over ~ left_over"
    using Tangle_Equivalence.equality by auto
 then have 1:"left_over ~ right_over"
    using Tangle_Equivalence.sym by auto
  have "uncross right_over straight_line"
        using uncross_positive_straighten_def uncross_def by auto
 then have "linkrel right_over straight_line"
    using linkrel_def by auto
 then have 2:"right_over ~ straight_line"
    using Tangle_Equivalence.equality by auto
  have "(left_over ~  straight_line) \<and> (right_over ~ straight_line)
         \<Longrightarrow> ?thesis" 
            using transitive by auto
 then show ?thesis using 1 2 transitive  by blast
 qed



theorem Example:
  "x ~ y" 
proof-
 have 1:"left_over ~ straight_line"
    using Tangle_Equivalence.equality uncross_straighten_left_over by auto
 moreover have 2:"straight_line ~ straight_line"
   using refl by auto
 have 3:"(left_over \<otimes> straight_line) ~ (straight_line \<otimes> straight_line)"
 proof-
  have "is_tangle_diagram (left_over)"
    unfolding is_tangle_diagram_def by auto 
  moreover have "is_tangle_diagram (straight_line)"
    unfolding is_tangle_diagram_def by auto
  ultimately show ?thesis using 1 2 by (metis Tangle_Equivalence.tensor_eq)
 qed
 then have 4:
  "((basic (cup#[])) \<circ> (left_over \<otimes> straight_line)) 
           ~   ((basic (cup#[])) \<circ> (straight_line \<otimes> straight_line))"
 proof-
  have "is_tangle_diagram (left_over \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (straight_line \<otimes> straight_line)"
        by auto
  moreover have "is_tangle_diagram (basic (cup#[]))" 
         by auto
  moreover have "domain_wall (left_over \<otimes> straight_line) = (codomain_wall (basic (cup#[])))"
        unfolding domain_wall_def by auto
  moreover have "domain_wall (straight_line \<otimes> straight_line) = (codomain_wall (basic (cup#[])))"
        unfolding domain_wall_def by auto
  moreover have "(basic (cup#[])) ~ (basic (cup#[]))" 
        using refl by auto
  ultimately show ?thesis 
        using compose_eq 3  by (metis Tangle_Equivalence.compose_eq)
 qed
 moreover have 5:"  (basic [cup])\<circ> (straight_line \<otimes> straight_line) 
                 ~ (basic [cup])"
 proof-
  have 0:
   "(basic ([cup])) \<circ> (straight_line \<otimes> straight_line) = (basic [cup]) \<circ>(basic [vert,vert]) 
                                                         \<circ> (basic [vert,vert])\<circ>(basic [vert,vert])"
           by auto
  let ?x ="(basic (cup#[]))
   \<circ>(basic (vert#vert#[])) \<circ> (basic (vert#vert#[]))
   \<circ> (basic (vert#vert#[]))"
  let ?x1 = " (basic (vert#vert#[]))\<circ> (basic (vert#vert#[]))"
  have 1:"?x ~ ((basic (cup#[])) \<circ> ?x1)"
  proof-
   have "(basic (cup#[]))\<circ>(basic (vert # vert # [])) ~ (basic (cup#[]))"
        using cup_compress by auto
   moreover have "is_tangle_diagram  (basic (cup#[]))" 
        using is_tangle_diagram_def by auto
   moreover have "is_tangle_diagram ((basic (cup#[]))\<circ>(basic (vert # vert # [])))"
        using is_tangle_diagram_def by auto
   moreover have "is_tangle_diagram (?x1)"
        by auto
   moreover have "?x1 ~ ?x1" 
        using refl by auto       
   moreover have 
     "codomain_wall (basic (cup#[])) = domain_wall  (basic (vert#vert#[]))"
        by auto
   moreover have "(basic (cup#[])) ~ (basic (cup#[]))"
         using refl by auto
   ultimately show ?thesis 
         using compose_eq codomain_wall_compose compose_leftassociativity 
               converse_composition_of_tangle_diagrams domain_wall_compose
         by (metis Tangle_Equivalence.compose_eq is_tangle_diagram.simps(1))
  qed
  have 2: " ((basic (cup#[])) \<circ> ?x1) ~ (basic (cup#[]))"
  proof-
   have "
     ((basic (cup # []))\<circ>(basic (vert # vert # [])))\<circ>(basic (vert # vert # [])) 
          ~ ((basic(cup#[]))\<circ>(basic(vert#vert#[])))"
   proof-
    have "(basic (cup#[]))\<circ>(basic (vert # vert # [])) ~ (basic (cup#[]))"
         using cup_compress by auto
    moreover have "(basic(vert#vert#[])) ~ (basic(vert#vert#[]))" 
         using refl by auto  
    moreover have "is_tangle_diagram  (basic (cup#[]))" 
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram ((basic (cup#[]))\<circ>(basic (vert # vert # [])))"
         using is_tangle_diagram_def by auto
    moreover have "is_tangle_diagram ((basic(vert#vert#[])))"
         by auto     
    moreover have 
         "codomain_wall ((basic (cup#[]))\<circ>  (basic(vert#vert#[]))) 
                       = domain_wall  (basic(vert#vert#[]))  "
         by auto
    moreover 
         have "codomain_wall (basic (cup#[])) = domain_wall (basic(vert#vert#[]))"
         by auto       
    ultimately show ?thesis 
                 using compose_eq 
                 by (metis Tangle_Equivalence.compose_eq)
   qed 
   then have "((basic (cup#[])) \<circ> ?x1) ~
           ((basic(cup#[]))\<circ>(basic(vert#vert#[])))"
         by auto
   then show ?thesis using cup_compress trans
         by (metis (full_types) Example.transitive)
  qed
  from 0 1 2 show ?thesis using trans transp_def trans compose_Nil
          by (metis (hide_lams, no_types) Example.transitive)
 qed
 let ?y = "((basic ([])) \<circ> (basic (cup#[])))  "
 let ?temp = "(basic (vert#over#vert#[]))\<circ>(basic (cap#vert#vert#[])) "  
 have 45:"(left_over \<otimes> straight_line) = 
          ((basic (cup#vert#vert#[])) \<circ> ?temp)"  
          using tensor.simps by (metis compose_Nil concatenates_Cons concatenates_Nil)
 then have 55:"(basic (cup#[])) \<circ> (left_over \<otimes> straight_line) 
             =  (basic (cup#[])) \<circ>  (basic (cup#vert#vert#[])) \<circ> ?temp"
          by auto
 then have 
  "(basic (cup#[])) \<circ> (basic (cup#vert#vert#[]))
      =  (basic (([]) \<otimes>(cup#[])))\<circ>(basic ((cup#[])\<otimes>(vert#vert#[])))"
          using concatenate.simps  by auto
 then have 6:
 "(basic (cup#[])) \<circ> (basic (cup#vert#vert#[]))
          = ((basic ([]))\<circ>(basic (cup#[])))
            \<otimes>((basic (cup#[])) \<circ>(basic (vert#vert#[])))"
          using tensor.simps by auto
 then have "((basic (cup#[])) \<circ>(basic (vert#vert#[]))) 
                   ~ (basic ([]))\<circ>(basic (cup#[]))"
          using prelim_cup_compress by auto
 moreover have "((basic ([]))\<circ>(basic (cup#[]))) 
                       ~ ((basic ([]))\<circ>(basic (cup#[])))"
          using refl by auto
 moreover have "is_tangle_diagram ((basic (cup#[])) \<circ>(basic (vert#vert#[])))"
          by auto
 moreover have "is_tangle_diagram ((basic ([]))\<circ>(basic (cup#[]))) "
          by auto
 ultimately have 7:"?y \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))~ ((?y) \<otimes> (?y))"
          using tensor_eq cup_compress Nil_right_tensor is_tangle_diagram.simps(1) refl
          by (metis Tangle_Equivalence.tensor_eq)
 then have " ((?y) \<otimes> (?y)) = (basic (([]) \<otimes> ([])))
                   \<circ> ((basic (cup#[])) \<otimes> (basic (cup#[])))"
          using tensor.simps(4)  by (metis compose_Nil) 
 then have "  ((?y) \<otimes> (?y)) = (basic ([])) \<circ>((basic (cup#cup#[])))"
          using tensor.simps(1) concatenate_def by auto
 then have "(?y) \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))
             ~ (basic ([])) \<circ>(basic (cup#cup#[]))" 
          using 7 by auto
 moreover have "(basic ([]))\<circ>(basic (cup#cup#[]))~(basic (cup#cup#[]))"
 proof-
  have "domain_wall (basic (cup#cup#[])) = 0"
          by auto
  then show ?thesis using domain_compose sym 
          by (metis Tangle_Equivalence.domain_compose Tangle_Equivalence.sym is_tangle_diagram.simps(1))
 qed
 ultimately have "(?y) \<otimes> ((basic (cup#[])) \<circ>(basic (vert#vert#[])))
               ~  (basic (cup#cup#[]))"
          using trans  by (metis (full_types) Example.transitive)
 then have " (basic(cup#[]))\<circ>(basic(cup#vert#vert#[]))~(basic(cup#cup#[]))" 
          by auto
 moreover have "?temp ~ ?temp"
          using refl by auto
 moreover  have "is_tangle_diagram ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[])))"
          by auto
 moreover have "is_tangle_diagram (basic(cup#cup#[]))"
          by auto
 moreover have "is_tangle_diagram  (?temp)"
          by auto
 moreover have "codomain_wall  ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[])))
                    = domain_wall ?temp"
          by auto
 moreover have "codomain_wall (basic(cup#cup#[])) = domain_wall ?temp"
          by auto
 ultimately have 8:" ((basic(cup#[]))\<circ>(basic(cup#vert#vert#[]))) \<circ>(?temp)
                       ~ (basic(cup#cup#[])) \<circ> (?temp)"
          using compose_eq by (metis Tangle_Equivalence.compose_eq)
 then have "((basic [cup,cup]) \<circ> (?temp)) 
                 ~ (basic [cup] \<circ> (left_over \<otimes> straight_line))"
          using 55 compose_leftassociativity sym wall.simps   
          by (metis Tangle_Equivalence.sym compose_Nil)
 moreover have "(basic [cup]) \<circ> (left_over \<otimes> straight_line) 
                    ~ (basic [cup]) \<circ> (straight_line \<otimes> straight_line)"
          using 4 by auto
 ultimately have "((basic [cup,cup]) \<circ> (?temp)) 
                  ~ (basic [cup]) \<circ> (straight_line \<otimes> straight_line)"          
  proof-
   have "((basic [cup,cup]) \<circ> (?temp)) 
                 ~ (basic [cup] \<circ> (left_over \<otimes> straight_line))"
          using 8 55 compose_leftassociativity sym wall.simps  Tangle_Equivalence.sym compose_Nil  
          by (metis)    
   moreover have "(basic [cup]) \<circ> (left_over \<otimes> straight_line) 
                    ~ (basic [cup]) \<circ> (straight_line \<otimes> straight_line)"
          using 4 by auto
   moreover have "(((basic [cup,cup]) \<circ> (?temp)) 
                 ~ (basic [cup] \<circ> (left_over \<otimes> straight_line)))
        \<and> ((basic [cup]) \<circ> (left_over \<otimes> straight_line) 
                    ~ (basic [cup]) \<circ> (straight_line \<otimes> straight_line))
           \<Longrightarrow> ?thesis"
          using Example.transitive by auto
   ultimately show ?thesis by auto
  qed
  then have "(basic ([cup,cup])) \<circ> (?temp)  ~ (basic (cup # []))"
         using trans transp_def 5 by (metis Example.transitive)
  moreover have "(basic (cap#[])) ~ (basic (cap#[]))"
         using refl by auto
  moreover have "is_tangle_diagram ((basic(cup#cup#[])) \<circ> (?temp))"
         by auto
  moreover have "is_tangle_diagram (basic (cup # []))"
         by auto
  moreover have "is_tangle_diagram (basic (cap # []))"
         by auto
  moreover have "codomain_wall ((basic(cup#cup#[])) \<circ> (?temp)) 
                   = domain_wall (basic (cap # []))"
         by auto
  moreover have "codomain_wall (basic(cup#[])) = domain_wall (basic (cap # []))"
         by auto
 ultimately have 9:"((basic(cup#cup#[])) \<circ> (?temp)) \<circ> (basic (cap#[]))
                     ~ (basic (cup#[])) \<circ> (basic (cap#[]))"
         using Tangle_Equivalence.compose_eq by metis
  let ?z = "((basic(cup#cup#[])) \<circ> (basic(vert#over#vert#[])))"
  have 10:"((basic(cup#cup#[])) \<circ> (?temp)) \<circ> (basic (cap#[]))
              = ?z \<circ> ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))"
         by auto
  then have 11:"((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
                           = ((basic ((cap#[])\<otimes>(vert#vert#[])))\<circ>(basic (([]) \<otimes>(cap#[]))))"
          unfolding concatenate_def by auto
  then have 12:" ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))) 
                       = ((basic (cap#[]))\<circ>(basic ([])))\<otimes>((basic (vert#vert#[]))\<circ>(basic (cap#[])))"
          using tensor.simps by auto
  let ?w = "((basic (cap#[]))\<circ>(basic ([])))"
  have 13:"((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ?w"
  proof-
   have "codomain_wall (basic (cap#[])) = 0" 
        by auto
   then have "domain_wall (basic (cap#[])) = 2" by auto
   then have "(vert#vert#[]) 
                          = make_vert_block (nat (domain_wall (basic (cap#[]))))"
     by (simp add: make_vert_block_def)
   then have "compress_top  ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w"
        using compress_top_def by auto
   then have "compress ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w" 
        using compress_def by auto
   then have "linkrel  ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ?w" 
        using linkrel_def by auto
   then have " ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ?w"
        using Tangle_Equivalence.equality by auto
   then show ?thesis by simp
  qed
  moreover have "is_tangle_diagram ((basic (vert#vert#[]))\<circ>(basic (cap#[])))"
        by auto
  moreover have "is_tangle_diagram ?w"
        by auto
  moreover have "?w ~ ?w" 
        using refl by auto
  ultimately have 14:"(?w) \<otimes> ((basic (vert#vert#[]))\<circ>(basic (cap#[]))) ~ ((?w)\<otimes> (?w))"
        using Tangle_Equivalence.tensor_eq by metis
  then have "((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))) ~ ((?w)\<otimes> (?w))"
        using 13 by auto
  moreover have " ((?w)\<otimes> (?w)) = (basic (cap#cap#[])) \<circ> (basic ([]))"
        using tensor.simps by auto
  ultimately have "((basic(cap#vert#vert#[]))\<circ>(basic (cap#[])))~ (basic (cap#cap#[]))\<circ>(basic ([]))"
        by auto
  moreover have "?z ~ ?z" 
        using refl by auto
  moreover have "domain_wall ((basic(cap#cap#[])) \<circ> (basic ([])))
                                = codomain_wall (?z)"
        by auto
  moreover have "domain_wall (((basic(cap#vert#vert#[])) \<circ> (basic (cap#[]))))
                                = codomain_wall (?z)" 
        by auto
  moreover have "is_tangle_diagram ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))"
        by auto
  moreover have "is_tangle_diagram (?z)"
        by auto
  moreover have "is_tangle_diagram  ((basic(cap#cap#[])) \<circ> (basic ([])))"
        by auto
  ultimately have 14:" (?z) \<circ>  ((basic(cap#vert#vert#[])) \<circ> (basic (cap#[])))
                      ~ (?z) \<circ> ((basic(cap#cap#[])) \<circ> (basic ([])))" (is "?aa ~ ?bb")
        using Tangle_Equivalence.compose_eq by metis
  moreover  have 15: "((?z) \<circ> ((basic(cap#cap#[]))) \<circ> (basic ([]))) 
                ~ ((?z) \<circ> (basic(cap#cap#[])))" (is "?bb ~ ?cc")
        using Tangle_Equivalence.codomain_compose  Tangle_Equivalence.sym 
               \<open>is_tangle_diagram (basic [cap, cap] \<circ> basic [])\<close> codomain_wall_compose 
               compose_leftassociativity converse_composition_of_tangle_diagrams 
               domain_block.simps(1) domain_wall.simps(1)
        by (metis (hide_lams, mono_tags) Tangle_Equivalence.compose_eq 
                Tangle_Equivalence.refl 
                \<open>codomain_wall (basic [cup, cup]) 
                         = domain_wall (basic [vert, over, vert] \<circ> basic [cap, vert, vert])\<close> 
                   \<open>domain_wall (basic [cap, cap] \<circ> basic []) 
          = codomain_wall (basic [cup, cup] \<circ> basic [vert, over, vert])\<close> 
                          comp_of_tangle_dgms domain_wall_compose is_tangle_diagram.simps(1))
  ultimately have "(?aa ~ ?bb)\<and> (?bb ~ ?cc) \<Longrightarrow>?aa ~ ?cc"
        using transitive by auto
  then have 16:"?aa ~ ?cc"
        using 14 15 by auto
  then have 17:" ((basic (cup#[]))\<circ>(basic (cap#[])))~ ?aa"
        using 9 10 Tangle_Equivalence.trans  Tangle_Equivalence.sym 
        by (metis (hide_lams, no_types))
  have "(((basic (cup#[]))\<circ>(basic (cap#[])))~ ?aa)\<and>(?aa ~ ?cc)
            \<Longrightarrow> ((basic (cup#[]))\<circ>(basic (cap#[])))~ ?cc" 
        using transitive by auto
  then have "((basic (cup#[]))\<circ>(basic (cap#[])))~ ?cc"
            using 17 16 by auto
  then show ?thesis using Tangle_Equivalence.sym by auto
qed
    
end       
