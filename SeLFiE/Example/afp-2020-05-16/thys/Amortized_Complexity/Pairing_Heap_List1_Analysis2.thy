(* Author: Tobias Nipkow *)

subsection \<open>Transfer of Tree Analysis to List Representation\<close>

theory Pairing_Heap_List1_Analysis2
imports
  Pairing_Heap_List1_Analysis
  Pairing_Heap_Tree_Analysis
begin

text\<open>This theory transfers the amortized analysis of the tree-based
pairing heaps to Okasaki's pairing heaps.\<close>

abbreviation "is_root' == Pairing_Heap_List1_Analysis.is_root"
abbreviation "del_min' == Pairing_Heap_List1.del_min"
abbreviation "insert' == Pairing_Heap_List1.insert"
abbreviation "merge' == Pairing_Heap_List1.merge"
abbreviation "pass\<^sub>1' == Pairing_Heap_List1.pass\<^sub>1"
abbreviation "pass\<^sub>2' == Pairing_Heap_List1.pass\<^sub>2"
abbreviation "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1' == Pairing_Heap_List1_Analysis.t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1"
abbreviation "t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2' == Pairing_Heap_List1_Analysis.t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2"

fun homs :: "'a heap list \<Rightarrow> 'a tree" where
"homs [] = Leaf" |
"homs (Hp x lhs # rhs) = Node (homs lhs) x (homs rhs)"

fun hom :: "'a heap \<Rightarrow> 'a tree" where
"hom heap.Empty = Leaf" |
"hom (Hp x hs) = (Node (homs hs) x Leaf)"

lemma homs_pass1': "no_Emptys hs \<Longrightarrow> homs(pass\<^sub>1' hs) = pass\<^sub>1 (homs hs)"
apply(induction hs rule: Pairing_Heap_List1.pass\<^sub>1.induct)
  apply simp
 subgoal for h
 apply(case_tac h)
  apply (auto)
 done
subgoal for h1 h2
apply(case_tac h1)
 apply simp
apply(case_tac h2)
 apply (auto)
done
done

lemma hom_merge': "\<lbrakk> no_Emptys lhs; Pairing_Heap_List1_Analysis.is_root h\<rbrakk>
       \<Longrightarrow> hom (merge' (Hp x lhs) h) = link \<langle>homs lhs, x, hom h\<rangle>"
by(cases h) auto

lemma hom_pass2': "no_Emptys hs \<Longrightarrow> hom(pass\<^sub>2' hs) = pass\<^sub>2 (homs hs)"
by(induction hs rule: homs.induct) (auto simp: hom_merge' is_root_pass2)

lemma del_min': "is_root' h \<Longrightarrow> hom(del_min' h) = del_min (hom h)"
by(cases h)
  (auto simp: homs_pass1' hom_pass2' no_Emptys_pass1 is_root_pass2)

lemma insert': "is_root' h \<Longrightarrow> hom(insert' x h) = insert x (hom h)"
by(cases h)(auto)

lemma merge':
  "\<lbrakk> is_root' h1; is_root' h2 \<rbrakk> \<Longrightarrow> hom(merge' h1 h2) = merge (hom h1) (hom h2)"
apply(cases h1)
 apply(simp)
apply(cases h2)
 apply(auto)
done

lemma t_pass1': "no_Emptys hs \<Longrightarrow> t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1' hs = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>1(homs hs)"
apply(induction hs rule: Pairing_Heap_List1.pass\<^sub>1.induct)
  apply simp
 subgoal for h
 apply(case_tac h)
  apply (auto)
 done
subgoal for h1 h2
apply(case_tac h1)
 apply simp
apply(case_tac h2)
 apply (auto)
done
done

lemma t_pass2': "no_Emptys hs \<Longrightarrow> t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2' hs = t\<^sub>p\<^sub>a\<^sub>s\<^sub>s\<^sub>2(homs hs)"
by(induction hs rule: homs.induct) (auto simp: hom_merge' is_root_pass2)

lemma size_hp: "is_root' h \<Longrightarrow> size_hp h = size (hom h)"
proof(induction h)
  case (Hp _ hs) thus ?case
    apply(induction hs rule: homs.induct)
      apply simp
     apply force
    apply simp
    done
qed simp

interpretation Amortized2
where arity = arity and exec = exec and inv = is_root
and cost = cost and \<Phi> = \<Phi> and U = U
and hom = hom
and exec' = Pairing_Heap_List1_Analysis.exec
and cost' = Pairing_Heap_List1_Analysis.cost and inv' = "is_root'"
and U' = Pairing_Heap_List1_Analysis.U
proof (standard, goal_cases)
  case (1 _ f) thus ?case
    by (cases f)(auto simp: merge' del_min' numeral_eq_Suc)
next
  case (2 ts f)
  show ?case
  proof(cases f)
    case [simp]: Del_min
    then obtain h where [simp]: "ts = [h]" using 2 by auto
    show ?thesis using 2
      by(cases h) (auto simp: is_root_pass2 no_Emptys_pass1)
  qed (insert 2,
      auto simp: Pairing_Heap_List1_Analysis.is_root_merge numeral_eq_Suc)
next
  case (3 t) thus ?case by (cases t) (auto)
next
  case (4 ts f) show ?case
  proof (cases f)
    case [simp]: Del_min
    then obtain h where [simp]: "ts = [h]" using 4 by auto
    show ?thesis using 4
      by (cases h)(auto simp: t_pass1' t_pass2' no_Emptys_pass1 homs_pass1')
  qed (insert 4, auto)
next
  case (5 _ f) thus ?case by(cases f) (auto simp: size_hp numeral_eq_Suc)
qed

end
