(*  Title:       Isabelle Collections Framework
    Author:      Peter Lammich <lammich at in.tum.de>
    Maintainer:  Peter Lammich <lammich at in.tum.de>
*)
section \<open>\isaheader{More Generic Algorithms}\<close>
theory Algos
imports 
  "../spec/SetSpec"
  "../spec/MapSpec"
  "../spec/ListSpec"
begin
text_raw \<open>\label{thy:Algos}\<close>
     

subsection "Injective Map to Naturals"

text "Whether a set is an initial segment of the natural numbers"
definition inatseg :: "nat set \<Rightarrow> bool" 
  where "inatseg s == \<exists>k. s = {i::nat. i<k}"

lemma inatseg_simps[simp]:
  "inatseg {}"
  "inatseg {0}"
  by (unfold inatseg_def)
    auto

text "Compute an injective map from objects into an initial 
    segment of the natural numbers"
locale map_to_nat_loc = 
  s: StdSet s_ops +
  m: StdMap m_ops
  for s_ops :: "('x,'s,'more1) set_ops_scheme"
  and m_ops :: "('x,nat,'m,'more2) map_ops_scheme"
begin

  definition map_to_nat 
    :: "'s \<Rightarrow> 'm" where
    "map_to_nat s ==
      snd (s.iterate s (\<lambda>x (c,m). (c+1,m.update x c m)) (0,m.empty ()))"

  lemma map_to_nat_correct:
    assumes INV[simp]: "s.invar s"
    shows 
      \<comment> \<open>All elements have got a number\<close>
      "dom (m.\<alpha> (map_to_nat s)) = s.\<alpha> s" (is ?T1) and
      \<comment> \<open>No two elements got the same number\<close>
      [rule_format]: "inj_on (m.\<alpha> (map_to_nat s)) (s.\<alpha> s)" (is ?T2) and
      \<comment> \<open>Numbering is inatseg\<close>
      [rule_format]: "inatseg (ran (m.\<alpha> (map_to_nat s)))" (is ?T3) and
      \<comment> \<open>The result satisfies the map invariant\<close>
      "m.invar (map_to_nat s)" (is ?T4)
    proof -
      have i_aux: "!!m S S' k v. \<lbrakk>inj_on m S; S' = insert k S; v\<notin>ran m\<rbrakk> 
                                 \<Longrightarrow> inj_on (m(k\<mapsto>v)) S'"
        apply (rule inj_onI)
        apply (simp split: if_split_asm)
        apply (simp add: ran_def)
        apply (simp add: ran_def)
        apply blast
        apply (blast dest: inj_onD)
        done

      have "?T1 \<and> ?T2 \<and> ?T3 \<and> ?T4"
        apply (unfold map_to_nat_def)
        apply (rule_tac I="\<lambda>it (c,m). 
          m.invar m \<and> 
          dom (m.\<alpha> m) = s.\<alpha> s - it \<and> 
          inj_on (m.\<alpha> m) (s.\<alpha> s - it) \<and> 
          (ran (m.\<alpha> m) = {i. i<c})
          " in s.iterate_rule_P)
        apply simp
        apply (simp add: m.empty_correct)
        apply (case_tac \<sigma>)
        apply (simp add: m.empty_correct m.update_correct)
        apply (intro conjI)
        apply blast
        apply clarify
        apply (rule_tac m2="m.\<alpha> ba" and 
                        k2=x and v2=aa and 
                        S'2="(s.\<alpha> s - (it - {x}))" and 
                        S2="(s.\<alpha> s - it)" 
                        in i_aux)
        apply auto [3]
        apply auto [1]
        apply (case_tac \<sigma>)
        apply (auto simp add: inatseg_def)
        done
      thus ?T1 ?T2 ?T3 ?T4 by auto
    qed
  
end

subsection "Map from Set"
text "Build a map using a set of keys and a function to compute the values."

locale it_dom_fun_to_map_loc =
  s: StdSet s_ops
+ m: StdMap m_ops 
  for s_ops :: "('k,'s,'more1) set_ops_scheme"
  and m_ops :: "('k,'v,'m,'more2) map_ops_scheme"
begin

  definition it_dom_fun_to_map ::
    "'s \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> 'm"
    where "it_dom_fun_to_map s f == 
           s.iterate s (\<lambda>k m. m.update_dj k (f k) m) (m.empty ())"

  lemma it_dom_fun_to_map_correct:
    assumes INV: "s.invar s"
    shows "m.\<alpha> (it_dom_fun_to_map s f) k 
      = (if k \<in> s.\<alpha> s then Some (f k) else None)" (is ?G1)
    and "m.invar (it_dom_fun_to_map s f)" (is ?G2)
  proof -
    have "m.\<alpha> (it_dom_fun_to_map s f) k 
      = (if k \<in> s.\<alpha> s then Some (f k) else None) \<and>
      m.invar (it_dom_fun_to_map s f)"
      unfolding it_dom_fun_to_map_def
      apply (rule s.iterate_rule_P[where 
        I = "\<lambda>it res. m.invar res 
        \<and> (\<forall>k. m.\<alpha> res k = (if (k \<in> (s.\<alpha> s) - it) then Some (f k) else None))"
        ])
        apply (simp add: INV)

        apply (simp add: m.empty_correct)

        apply (subgoal_tac "x\<notin>dom (m.\<alpha> \<sigma>)")

        apply (auto simp: INV m.empty_correct m.update_dj_correct) []

        apply auto [2]
      done
    thus ?G1 and ?G2
      by auto
  qed

end


locale set_to_list_defs_loc =
  s: StdSetDefs s_ops
+ l: StdListDefs l_ops
  for s_ops :: "('x,'s,'more1) set_ops_scheme"
  and l_ops :: "('x,'l,'more2) list_ops_scheme"
begin
  definition "g_set_to_listl s \<equiv> s.iterate s l.appendl (l.empty ())"
  definition "g_set_to_listr s \<equiv> s.iterate s l.appendr (l.empty ())"
end

locale set_to_list_loc = set_to_list_defs_loc s_ops l_ops
+ s: StdSet s_ops
+ l: StdList l_ops
  for s_ops :: "('x,'s,'more1) set_ops_scheme"
  and l_ops :: "('x,'l,'more2) list_ops_scheme"
begin
  lemma g_set_to_listl_correct: 
    assumes I: "s.invar s"
    shows "List.set (l.\<alpha> (g_set_to_listl s)) = s.\<alpha> s"
    and "l.invar (g_set_to_listl s)"
    and "distinct (l.\<alpha> (g_set_to_listl s))"
    using I apply -
    unfolding g_set_to_listl_def
    apply (rule_tac I="\<lambda>it \<sigma>. l.invar \<sigma> \<and> List.set (l.\<alpha> \<sigma>) = it 
      \<and> distinct (l.\<alpha> \<sigma>)" 
      in s.iterate_rule_insert_P, auto simp: l.correct)+
    done

  lemma g_set_to_listr_correct: 
    assumes I: "s.invar s"
    shows "List.set (l.\<alpha> (g_set_to_listr s)) = s.\<alpha> s"
    and "l.invar (g_set_to_listr s)"
    and "distinct (l.\<alpha> (g_set_to_listr s))"
    using I apply -
    unfolding g_set_to_listr_def
    apply (rule_tac I="\<lambda>it \<sigma>. l.invar \<sigma> \<and> List.set (l.\<alpha> \<sigma>) = it
      \<and> distinct (l.\<alpha> \<sigma>)" 
      in s.iterate_rule_insert_P, auto simp: l.correct)+
    done

end

end
