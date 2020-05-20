(*  Title:       Effects of the function mtf2 on index and before_in
    Author:      Max Haslbeck
*)

section "Effect of mtf2"

theory MTF2_Effects
imports Move_to_Front
begin



lemma difind_difelem: 
       "i < length xs \<Longrightarrow> distinct xs \<Longrightarrow> xs ! j = a \<Longrightarrow> j < length xs \<Longrightarrow> i \<noteq> j 
          \<Longrightarrow> ~ a = xs ! i"
apply(rule ccontr) by(metis index_nth_id)


lemma fullchar: assumes  "index xs q < length xs"
  shows 
    "(i < length xs) =
  (index xs q < i \<and> i < length xs
    \<or> index xs q = i
    \<or> index xs q - n \<le> i \<and> i < index xs q
    \<or> i < index xs q - n)"
using assms by auto

lemma mtf2_effect:
    "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> (index xs q < i \<and> i < length xs \<longrightarrow>( index (mtf2 n q xs) (xs!i) = index xs (xs!i) \<and> index xs q < index (mtf2 n q xs) (xs!i) \<and> index (mtf2 n q xs) (xs!i) < length xs))
    \<and> (index xs q = i \<longrightarrow> (index (mtf2 n q xs) (xs!i) = index xs q - n \<and> index (mtf2 n q xs) (xs!i) = index xs q - n))
    \<and> (index xs q - n \<le> i \<and> i < index xs q \<longrightarrow> (index (mtf2 n q xs) (xs!i) = Suc (index xs (xs!i)) \<and> index xs q - n < index (mtf2 n q xs) (xs!i) \<and> index (mtf2 n q xs) (xs!i) \<le> index xs q))
    \<and> (i < index xs q - n \<longrightarrow> (index (mtf2 n q xs) (xs!i) = index xs (xs!i) \<and> index (mtf2 n q xs) (xs!i) < index xs q - n))"
unfolding mtf2_def
apply (induct n)
proof -
  case (Suc n)
  note indH=Suc(1)[OF Suc(2) Suc(3), simplified Suc(2) if_True] 
  note qinxs=Suc(2)[simp]
  note distxs=Suc(3)[simp]
  show ?case (is ?toshow)
  apply(simp only: qinxs if_True)
  proof (cases "index xs q \<ge> Suc n")
    case True 
    note True1=this
from True have onemore: "[index xs q - Suc n..<index xs q] = (index xs q - Suc n) # [index xs q - n..<index xs q]"
              using Suc_diff_Suc upt_rec by auto

        from onemore have yeah: "swaps [index xs q - Suc n..<index xs q] xs
            = swap (index xs q - Suc n) (swaps  [index xs q - n..<index xs q] xs)" by auto

      have sis: "Suc (index xs q - Suc n) = index xs q - n" using True Suc_diff_Suc by auto
      
      have indq: "index xs q < length xs"
        apply(rule index_less) by auto
 
      let ?i' = "index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i)"
      let ?x = "(xs!i)" and  ?xs="(swaps  [index xs q - n..<index xs q] xs)"
              and ?n="(index xs q - Suc n)"
      have "?i'
          =  index (swap (index xs q - Suc n) (swaps  [index xs q - n..<index xs q] xs)) (xs!i)" using yeah by auto
      also have "\<dots> = (if ?x = ?xs ! ?n then Suc ?n else if ?x = ?xs ! Suc ?n then ?n else index ?xs ?x)"
        apply(rule index_swap_distinct)
          apply(simp)
          apply(simp add: sis) using indq by linarith
      finally have i': "?i' = (if ?x = ?xs ! ?n then Suc ?n else if ?x = ?xs ! Suc ?n then ?n else index ?xs ?x)" .
      
      let ?i''="index (swaps [index xs q - n..<index xs q] xs) (xs ! i)"


    show "(index xs q < i \<and> i < length xs \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs (xs ! i) \<and>
     index xs q < index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) < length xs) \<and>
    (index xs q = i \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs q - Suc n \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs q - Suc n) \<and>
    (index xs q - Suc n \<le> i \<and> i < index xs q \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = Suc (index xs (xs ! i)) \<and>
     index xs q - Suc n < index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<le> index xs q) \<and>
    (i < index xs q - Suc n \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) < index xs q - Suc n)"
    apply(intro conjI)
    apply(intro impI) apply(elim conjE) prefer 4 apply(intro impI)  prefer 4 apply(intro impI) apply(elim conjE) 
      prefer 4 apply(intro impI) prefer 4
    proof (goal_cases)
      case 1 
      have indH1: "(index xs q < i \<and> i < length xs \<longrightarrow>
                      ?i'' =  index xs (xs ! i))" using indH by auto
      assume ass: "index xs q < i" and ass2:"i < length xs"      
      then have a: "?i'' =  index xs (xs ! i)" using indH1 by auto
      also have a': "\<dots> = i" apply(rule index_nth_id) using ass2 by(auto)
      finally have ii: "?i'' = i" .
      have fstF: "~ ?x = ?xs ! ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
        using indq apply (simp add: less_imp_diff_less)
        apply(simp)
        apply(rule nth_index) apply(simp) using ass2 apply(simp)
        apply(rule index_less) 
          apply(simp) using ass2 apply(simp)
          apply(simp)
        using ii ass by auto
      have sndF: "~ ?x = ?xs ! Suc ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
        using indq True apply (simp add: Suc_diff_Suc less_imp_diff_less)
        apply(simp)
        apply(rule nth_index) apply(simp) using ass2 apply(simp)
        apply(rule index_less) 
          apply(simp) using ass2 apply(simp)
          apply(simp)
        using ii ass Suc_diff_Suc True by auto     
        
      have "?i' = index xs (xs ! i)" unfolding i' using fstF sndF a by simp
      then show ?case using a' ass ass2 by auto
    next
      case 2
      have indH2: "index xs q = i \<longrightarrow> ?i'' = index xs (xs ! i) - n" using indH by auto
      assume "index xs q = i"
      then have ass: "i = index xs q" by auto
      with indH2 have a: "i - n = ?i''" by auto
      from ass have c: "index xs (xs ! i) = i" by auto  
      have "Suc (index xs q - Suc n) = i - n" using ass True Suc_diff_Suc by auto
      also have "\<dots> = ?i''" using a by auto
      finally have a: "Suc ?n = ?i''" .

      have sndTrue: "?x = ?xs ! Suc ?n" apply(simp add: a)
              apply(rule nth_index[symmetric]) by (simp add: ass)
      have fstFalse: "~ ?x = ?xs ! ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
        using indq True apply (simp add: Suc_diff_Suc less_imp_diff_less)
        apply(simp)
        apply(rule nth_index) apply(simp) using ass  apply(simp)
        apply(rule index_less) 
          apply(simp) using ass  apply(simp)
          apply(simp)
        using a by auto    

      have "?i' = index xs (xs ! index xs q) - Suc n"
          unfolding i' using sndTrue fstFalse by simp
      with ass show ?case by auto
    next
      case 3
      have indH3: "index xs q - n \<le> i \<and> i < index xs q
              \<longrightarrow>  ?i'' = Suc (index xs (xs ! i))" using indH by auto
      assume ass: "index xs q - Suc n \<le> i" and
              ass2: "i < index xs q" 
      from ass2 have ilen: "i < length xs" using indq dual_order.strict_trans by blast
      show ?case 
      proof (cases "index xs q - n \<le> i")
        case False
        then have "i < index xs q - n" by auto
        moreover have "(i < index xs q - n \<longrightarrow> ?i'' = index xs (xs ! i))" using indH by auto
        ultimately have d: "?i'' = index xs (xs ! i)" by simp
        from False ass have b: "index xs q - Suc n = i" by auto
        have "index xs q < length xs" apply(rule index_less) by (auto)
        have c: "index xs (xs ! i) = i"
          apply(rule index_nth_id) apply(simp) using indq ass2 using less_trans by blast
        from b c d have f: "?i'' = index xs q - Suc n" by auto
        have fstT: "?xs ! ?n = ?x" 
            apply(simp only: f[symmetric]) apply(rule nth_index)
            by (simp add: ilen)

        have "?i' = Suc (index xs q - Suc n)"
          unfolding i' using fstT by simp
        also have "\<dots> = Suc (index xs (xs ! i))" by(simp only: b c)
        finally show ?thesis using c False ass by auto
      next
        case True
        with ass2 indH3 have a: "?i'' = Suc (index xs (xs ! i))" by auto
        have jo: "index xs (xs ! i) = i" apply(rule index_nth_id) using ilen by(auto)
        have fstF: "~ ?x = ?xs ! ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
          using indq apply (simp add: less_imp_diff_less)
          apply(simp)
          apply(rule nth_index) apply(simp) using ilen apply(simp)
          apply(rule index_less) 
            apply(simp) using ilen apply(simp)
            apply(simp)
          apply(simp only: a jo) using True by auto
        have sndF: "~ ?x = ?xs ! Suc ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
          using True1 apply (simp add: Suc_diff_Suc less_imp_diff_less)
          apply(simp)
          apply(rule nth_index) apply(simp) using ilen apply(simp)
          apply(rule index_less) 
            apply(simp) using ilen apply(simp)
            apply(simp)
          apply(simp only: a jo) using True1 apply (simp add: Suc_diff_Suc less_imp_diff_less)
          using True by auto   
        have "?i' = Suc (index xs (xs ! i))" unfolding i' using fstF sndF a by simp 
        then show ?thesis using ass ass2 jo by auto
      qed
    next
      case 4
      assume ass: "i < index xs q - Suc n"
      then have ass2: "i < index xs q - n" by auto
      moreover have "(i < index xs q - n \<longrightarrow> ?i'' = index xs (xs ! i))" using indH by auto
      ultimately have a: "?i'' = index xs (xs ! i)" by auto
      from ass2 have "i < index xs q" by auto
      then have ilen: "i < length xs" using indq dual_order.strict_trans by blast


      have jo: "index xs (xs ! i) = i" apply(rule index_nth_id) using ilen by(auto)
      have fstF: "~ ?x = ?xs ! ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
        using indq apply (simp add: less_imp_diff_less)
        apply(simp)
        apply(rule nth_index) apply(simp) using ilen apply(simp)
        apply(rule index_less) 
          apply(simp) using ilen apply(simp)
          apply(simp)
        apply(simp only: a jo) using ass by auto 
      have sndF: "~ ?x = ?xs ! Suc ?n" apply(rule difind_difelem[where j="index (swaps [index xs q - n..<index xs q] xs) (xs!i)"])
        using True1 apply (simp add: Suc_diff_Suc less_imp_diff_less)
        apply(simp)
        apply(rule nth_index) apply(simp) using ilen apply(simp)
        apply(rule index_less) 
          apply(simp) using ilen apply(simp)
          apply(simp)
        apply(simp only: a jo) using True1 apply (simp add: Suc_diff_Suc less_imp_diff_less)
        using ass by auto  
      have "?i' = (index xs (xs ! i))" unfolding i' using fstF sndF a by simp
      then show ?case using jo ass by auto
    qed
  next
    case False

    then have smalla: "index xs q - Suc n = index xs q - n" by auto
    then have nomore: "swaps [index xs q - Suc n..<index xs q] xs
            =swaps [index xs q - n..<index xs q] xs" by auto
    show "(index xs q < i \<and> i < length xs \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs (xs ! i) \<and>
     index xs q < index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) < length xs) \<and>
    (index xs q = i \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs q - Suc n \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs q - Suc n) \<and>
    (index xs q - Suc n \<le> i \<and> i < index xs q \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = Suc (index xs (xs ! i)) \<and>
     index xs q - Suc n < index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) \<le> index xs q) \<and>
    (i < index xs q - Suc n \<longrightarrow>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) = index xs (xs ! i) \<and>
     index (swaps [index xs q - Suc n..<index xs q] xs) (xs ! i) < index xs q - Suc n)" 
      unfolding nomore smalla by (rule indH)
  qed
next
  case 0
  then show ?case apply(simp)
  proof (safe, goal_cases)
    case 1
    have " index xs (xs ! i) = i" apply(rule index_nth_id) using 1 by auto
    with 1 show ?case by auto
  next
    case 2
    have "xs ! index xs q = q" using 2 by(auto)
    with 2 show ?case by auto
  next
    case 3
    have a: "index xs q < length xs" apply(rule index_less) using 3 by auto
    have "index xs (xs ! i) = i" apply(rule index_nth_id) apply(fact 3(2)) using 3(3) a by auto
    with 3 show ?case by auto
  qed   
qed

lemma mtf2_forward_effect1:
  "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q < i \<and> i < length xs 
      \<Longrightarrow> index (mtf2 n q xs) (xs ! i) = index xs (xs ! i) \<and> index xs q < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) < length xs" and    
  mtf2_forward_effect2: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q = i
      \<Longrightarrow> index (mtf2 n q xs) (xs!i) = index xs q - n \<and> index xs q - n = index (mtf2 n q xs) (xs!i)" and    
  mtf2_forward_effect3: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q - n \<le> i \<and> i < index xs q
      \<Longrightarrow> index (mtf2 n q xs) (xs!i) = Suc (index xs (xs!i)) \<and> index xs q - n < index (mtf2 n q xs) (xs!i) \<and> index (mtf2 n q xs) (xs!i) \<le> index xs q" and    
  mtf2_forward_effect4: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> i < index xs q - n 
      \<Longrightarrow> index (mtf2 n q xs) (xs!i) = index xs (xs!i) \<and> index (mtf2 n q xs) (xs!i) < index xs q - n"
apply(safe) using mtf2_effect by metis+

lemma yes[simp]: "index xs x < length xs 
      \<Longrightarrow> (xs!index xs x ) = x" apply(rule nth_index) by (simp add: index_less_size_conv)

lemma mtf2_forward_effect1':
  "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q < index xs x \<and> index xs x < length xs 
      \<Longrightarrow> index (mtf2 n q xs) x = index xs x \<and> index xs q < index (mtf2 n q xs) x \<and> index (mtf2 n q xs) x < length xs"     
 using mtf2_forward_effect1[where xs=xs and i="index xs x"] yes
 by(auto)

lemma
 mtf2_forward_effect2': "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q = index xs x
      \<Longrightarrow> index (mtf2 n q xs) (xs!index xs x) = index xs q - n \<and> index xs q - n = index (mtf2 n q xs) (xs!index xs x)"
 using mtf2_forward_effect2[where xs=xs and i="index xs x"] 
by fast

lemma
  mtf2_forward_effect3': "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q - n \<le> index xs x \<Longrightarrow> index xs x < index xs q
      \<Longrightarrow> index (mtf2 n q xs) (xs!index xs x) = Suc (index xs (xs!index xs x)) \<and> index xs q - n < index (mtf2 n q xs) (xs!index xs x) \<and> index (mtf2 n q xs) (xs!index xs x) \<le> index xs q" 
 using mtf2_forward_effect3[where xs=xs and i="index xs x"] 
by fast

lemma    
  mtf2_forward_effect4': "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs x < index xs q - n 
      \<Longrightarrow> index (mtf2 n q xs) (xs!index xs x) = index xs (xs!index xs x) \<and> index (mtf2 n q xs) (xs!index xs x) < index xs q - n"
 using mtf2_forward_effect4[where xs=xs and i="index xs x"] 
by fast


lemma splitit: " (index xs q < i \<and> i < length xs  \<Longrightarrow> P)
     \<Longrightarrow> (index xs q = i \<Longrightarrow> P)
     \<Longrightarrow> (index xs q - n \<le> i \<and> i < index xs q \<Longrightarrow> P)
     \<Longrightarrow> (i < index xs q - n \<Longrightarrow> P)
   \<Longrightarrow> (i < length xs \<Longrightarrow> P)"
by force


lemma mtf2_forward_beforeq: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> i < index xs q 
        \<Longrightarrow> index (mtf2 n q xs) (xs!i) \<le> index xs q"
apply (cases "i < index xs q - n")
  using mtf2_forward_effect4 apply force
  using mtf2_forward_effect3 using leI by metis


lemma x_stays_before_y_if_y_not_moved_to_front:
  assumes "q \<in> set xs" "distinct xs" "x \<in> set xs" "y \<in> set xs" "y \<noteq> q"
   and "x < y in xs"
  shows "x < y in (mtf2 n q xs)"
proof - 
  from assms(3) obtain i where i: "i = index xs x" and i2: "i < length xs" by auto
  from assms(4) obtain j where j: "j = index xs y" and j2: "j < length xs" by auto
  have "x < y in xs \<Longrightarrow> x < y in (mtf2 n q xs)"
  apply(cases i xs rule: splitit[where q=q and n=n])
     apply(simp add: i  assms(1,2) mtf2_forward_effect1' before_in_def)
     apply(cases j xs rule: splitit[where q=q and n=n])
      apply (metis before_in_def assms(1-3) i j less_imp_diff_less mtf2_effect nth_index set_mtf2)
      apply(simp add: i j assms mtf2_forward_effect1' mtf2_forward_effect2' before_in_def)
      apply(simp add: i j assms mtf2_forward_effect1' mtf2_forward_effect2' before_in_def)
      apply(simp add: i j assms mtf2_forward_effect1' mtf2_forward_effect3' before_in_def)
      apply(rule j2)
     apply(cases j xs rule: splitit[where q=q and n=n])
      apply (smt before_in_def assms(1-3) i j le_less_trans mtf2_forward_effect1 mtf2_forward_effect3 nth_index set_mtf2)
      using assms(4,5) j apply simp
      apply (smt Suc_leI before_in_def assms(1-3) i j le_less_trans lessI mtf2_forward_effect3 nth_index set_mtf2)
      apply (simp add: before_in_def i j)     
      apply(rule j2)
     apply(cases j xs rule: splitit[where q=q and n=n])
      apply (smt before_in_def assms(1-3) i j le_less_trans mtf2_forward_effect1 mtf2_forward_effect4 nth_index set_mtf2)
      using assms(4-5) j apply simp
      apply (smt before_in_def assms(1-3) i j le_less_trans less_imp_le_nat mtf2_forward_effect3 mtf2_forward_effect4 nth_index set_mtf2)
      apply (metis before_in_def assms(1-3) i j mtf2_forward_effect4 nth_index set_mtf2)     
      apply(rule j2)
     apply(rule i2) done
   with assms(6) show ?thesis by auto
qed


corollary swapped_by_mtf2: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>  y \<in> set xs \<Longrightarrow> 
      x < y in xs \<Longrightarrow> y < x in (mtf2 n q xs) \<Longrightarrow> y = q"
apply(rule ccontr) using x_stays_before_y_if_y_not_moved_to_front not_before_in by (metis before_in_setD1)

lemma x_stays_before_y_if_y_not_moved_to_front_2dir: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>  y \<in> set xs \<Longrightarrow> y \<noteq> q \<Longrightarrow> 
      x < y in xs = x < y in (mtf2 n q xs)"
oops

lemma mtf2_backwards_effect1:
  assumes "index xs q < length xs" "q \<in> set xs" "distinct xs" 
    "index xs q < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) < length xs"
    "i < length xs"
  shows  "index xs q <  i \<and> i  < length xs"
proof -
  from assms(4) have "~ (index xs q - n = index (mtf2 n q xs) (xs ! i))" by auto
  with assms mtf2_forward_effect2 have 1: "~ (index xs q = i)" by metis
  from assms(4) have "~ (index xs q - n < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) \<le> index xs q)" by auto
  with assms mtf2_forward_effect3 have 2: "~ (index xs q - n \<le> i \<and> i < index xs q)" by metis
  from assms(4) have "~ (index (mtf2 n q xs) (xs ! i) < index xs q - n)" by auto
  with assms mtf2_forward_effect4 have 3: "~ (i < index xs q - n)" by metis

  from fullchar[OF assms(1)] assms(5) 1 2 3 show "index xs q <  i \<and> i  < length xs" by metis
qed

lemma mtf2_backwards_effect2:
  assumes "index xs q < length xs" "q \<in> set xs" "distinct xs" "index (mtf2 n q xs) (xs ! i) = index xs q - n"
    "i < length xs" 
    shows "index xs q = i"
proof - 
  from assms(4) have "~ (index xs q < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) < length xs)" by auto
  with assms mtf2_forward_effect1 have 1: "~ (index xs q < i \<and> i < length xs)" by metis
  from assms(4) have "~ (index xs q - n < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) \<le> index xs q)" by auto
  with assms mtf2_forward_effect3 have 2: "~ (index xs q - n \<le> i \<and> i < index xs q)" by metis
  from assms(4) have "~ (index (mtf2 n q xs) (xs ! i) < index xs q - n)" by auto
  with assms mtf2_forward_effect4 have 3: "~ (i < index xs q - n)" by metis

  from fullchar[OF assms(1)] assms(5) 1 2 3 show "index xs q = i" by metis
qed

lemma mtf2_backwards_effect3:
  assumes "index xs q < length xs" "q \<in> set xs" "distinct xs"
    "index xs q - n < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) \<le> index xs q"
    "i < length xs"
  shows "index xs q - n \<le> i \<and> i < index xs q"
proof -
  from assms(4) have "~ (index xs q < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) < length xs)" by auto
  with assms mtf2_forward_effect1 have 2: "~ (index xs q <  i \<and> i  < length xs)" by metis
  from assms(4) have "~ (index xs q - n = index (mtf2 n q xs) (xs ! i))" by auto
  with assms mtf2_forward_effect2 have 1: "~ (index xs q = i)" by metis
  from assms(4) have "~ (index (mtf2 n q xs) (xs ! i) < index xs q - n)" by auto
  with assms mtf2_forward_effect4 have 3: "~ (i < index xs q - n)" by metis

  from fullchar[OF assms(1)] assms(5) 1 2 3 show "index xs q - n \<le> i \<and> i < index xs q" by metis
qed


lemma mtf2_backwards_effect4:
  assumes "index xs q < length xs" "q \<in> set xs" "distinct xs"
   "index (mtf2 n q xs) (xs ! i) < index xs q - n"
   "i < length xs" 
  shows "i < index xs q - n"
proof - 
  from assms(4) have "~ (index xs q < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) < length xs)" by auto
  with assms mtf2_forward_effect1 have 2: "~ (index xs q <  i \<and> i  < length xs)" by metis
  from assms(4) have "~ (index xs q - n = index (mtf2 n q xs) (xs ! i))" by auto
  with assms mtf2_forward_effect2 have 1: "~ (index xs q = i)" by metis
  from assms(4) have "~ (index xs q - n < index (mtf2 n q xs) (xs ! i) \<and> index (mtf2 n q xs) (xs ! i) \<le> index xs q)" by auto
  with assms mtf2_forward_effect3 have 3: "~ (index xs q - n \<le> i \<and> i < index xs q)" by metis

  from fullchar[OF assms(1)] assms(5) 1 2 3 show "i < index xs q - n" by metis
qed

lemma mtf2_backwards_effect4':
 assumes "index xs q < length xs" "q \<in> set xs" "distinct xs"
  "index (mtf2 n q xs) x < index xs q - n"
  "x \<in> set xs"
 shows "(index xs x) < index xs q - n"
 using assms mtf2_backwards_effect4[where xs=xs and i="index xs x"] yes
by auto

lemma 
  assumes distA: "distinct A" and
          asm: "q \<in> set A"
  shows 
      mtf2_mono:  "q< x in A \<Longrightarrow> q < x in (mtf2 n q A)" and
      mtf2_q_after: "index (mtf2 n q A) q =  index A q - n"
proof -

    have lele: "(q < x in A \<longrightarrow> q < x in swaps [index A q - n..<index A q] A) \<and> (index (swaps [index A q - n..<index A q] A) q =  index A q - n)"
    apply(induct n) apply(simp)
    proof -
      fix n
      assume ind: "(q < x in A \<longrightarrow> q < x in swaps [index A q - n..<index A q] A)
            \<and> index (swaps [index A q - n..<index A q] A) q =  index A q - n"
      then have iH: " q < x in A \<Longrightarrow> q < x in swaps [index A q - n..<index A q] A" by auto
      from ind have indH2: "index (swaps [index A q - n..<index A q] A) q =  index A q - n" by auto

      show "(q < x in A \<longrightarrow> q < x in swaps [index A q - Suc n..<index A q] A) \<and>
          index (swaps [index A q - Suc n..<index A q] A) q = index A q - Suc n" (is "?part1 \<and> ?part2")
      proof (cases "index A q \<ge> Suc n")
          case True    
          then have onemore: "[index A q - Suc n..<index A q] = (index A q - Suc n) # [index A q - n..<index A q]"
                using Suc_diff_Suc upt_rec by auto

          from onemore have yeah: "swaps [index A q - Suc n..<index A q] A
              = swap (index A q - Suc n) (swaps  [index A q - n..<index A q] A)" by auto


            from indH2 have gr: "index (swaps [index A q - n..<index A q] A) q =  Suc(index A q - Suc n)" using Suc_diff_Suc True by auto
            have whereisq: "swaps [index A q - n..<index A q] A ! Suc (index A q - Suc n) = q" 
                unfolding gr[symmetric] apply(rule nth_index) using asm by auto

          have indSi: "index A q < length A" using asm index_less by auto
          have 3: "Suc (index A q - Suc n) < length (swaps [index A q - n..<index A q] A)" using True
            apply(auto simp: Suc_diff_Suc asm) using indSi by auto
          have 1: "q \<noteq> swaps [index A q - n..<index A q] A ! (index A q - Suc n)"
              proof
                assume as: "q = swaps [index A q - n..<index A q] A ! (index A q - Suc n)"
                {
                  fix xs x
                  have "Suc x < length xs \<Longrightarrow> xs ! x = q \<Longrightarrow> xs ! Suc x = q \<Longrightarrow> \<not> distinct xs"  
                  by (metis Suc_lessD index_nth_id n_not_Suc_n)
                } note cool=this

                have "\<not> distinct (swaps [index A q - n..<index A q] A)"
                  apply(rule cool[of "(index A q - Suc n)"])
                    apply(simp only: 3)
                    apply(simp only: as[symmetric])
                    by(simp only: whereisq)
                then show "False" using distA by auto 
              qed

          have part1: ?part1
          proof
            assume qx: "q < x in A"
            {  
              fix q x B i
               assume a1: "q < x in B"
               assume a2: "~ q = B ! i"
               assume a3: "distinct B"
               assume a4: "Suc i < length B"

               have "dist_perm B B" by(simp add: a3)
               moreover have "Suc i < length B" using a4 by auto
               moreover have "q < x in B \<and> \<not> (q = B ! i \<and> x = B ! Suc i)" using a1 a2 by auto
               ultimately have "q < x in swap i B"
                using before_in_swap[of B B] by simp
           } note grr=this

            have 2: "distinct (swaps [index A q - n..<index A q] A)" using distA by auto
            

            show "q < x in swaps [index A q - Suc n..<index A q] A"
              apply(simp only: yeah)
              apply(rule grr[OF iH[OF qx]]) using 1 2 3 by auto
           qed


           let ?xs = "(swaps [index A q - n..<index A q] A)"
           let ?n = "(index A q - Suc n)" 
           have "?xs ! Suc ?n = swaps [index A q - n..<index A q] A ! (index (swaps [index A q - n..<index A q] A) q)" 
              using indH2 Suc_diff_Suc True by auto
           also have "\<dots> = q" apply(rule nth_index) using asm by auto
           finally have sndTrue: "?xs ! Suc ?n = q" .
           have fstFalse: "~ q = ?xs ! ?n" by (fact 1) 


           have "index (swaps [index A q - Suc n..<index A q] A) q
              = index (swap (index A q - Suc n) ?xs) q" by (simp only: yeah) 
           also have "\<dots> = (if q = ?xs ! ?n then Suc ?n else if q = ?xs ! Suc ?n then ?n else index ?xs q)"
            apply(rule index_swap_distinct)
              apply(simp add: distA)
              by (fact 3)
           also have "\<dots> = ?n" using fstFalse sndTrue by auto
           finally have part2: ?part2 .

           from part1 part2 show "?part1 \<and> ?part2" by simp
        next 
          case False
          then have a: "index A q - Suc n = index A q - n" by auto
          then have b: "[index A q - Suc n..<index A q] = [index A q - n..<index A q]" by auto
          show ?thesis apply(simp only: b a) by (fact ind) 
        qed      
      qed 
 
    show "q < x in A \<Longrightarrow> q < x in (mtf2 n q A)"
        "(index (mtf2 n q A) q) =  index A q - n"
    unfolding mtf2_def  
      using asm lele apply(simp)
      using asm lele by(simp)
qed




subsection "effect of mtf2 on index"

lemma swapsthrough: "distinct xs \<Longrightarrow> q \<in> set xs \<Longrightarrow> index ( swaps [index xs q - entf..<index xs q] xs ) q = index xs q - entf"
proof (induct entf)
  case (Suc e)
  note iH=this
  show ?case
  proof (cases "index xs q - e")
    case 0
    then have "[index xs q - Suc e..<index xs q]
        = [index xs q - e..<index xs q]" by force
    then have "index (swaps [index xs q - Suc e..<index xs q] xs) q
          =  index xs q - e" using Suc by auto
    also have "\<dots> = index xs q - (Suc e)" using 0 by auto
    finally show "index (swaps [index xs q - Suc e..<index xs q] xs) q = index xs q - Suc e" .
  next
    case (Suc f)

    have gaa: "Suc (index xs q - Suc e) = index xs q - e" using Suc by auto

    from Suc have "index xs q - e \<le> index xs q" by auto
    also have "\<dots> < length xs" by(simp add: index_less_size_conv iH)
    finally have indle: "index xs q - e < length xs".

    have arg: "Suc (index xs q - Suc e) < length (swaps [index xs q - e..<index xs q] xs)"
      apply(auto) unfolding gaa using indle by simp
    then have arg2: "index xs q - Suc e < length (swaps [index xs q - e..<index xs q] xs)" by auto
    from Suc have nexter: "index xs q - e = Suc (index xs q - (Suc e))" by auto
    then have aaa: "[index xs q - Suc e..<index xs q]
        = (index xs q - Suc e)#[index xs q - e..<index xs q]" using upt_rec by auto

     
    let ?i="index xs q - Suc e"
    let ?rest="swaps [index xs q - e..<index xs q] xs"
    from iH nexter have indj: "index ?rest q = Suc ?i" by auto

    from iH(2) have "distinct ?rest" by auto

    have "?rest ! (index ?rest q) = q" apply(rule nth_index) by(simp add: iH)
    with indj have whichcase: "q = ?rest ! Suc ?i" by auto

    with \<open>distinct ?rest\<close> have whichcase2: "~ q = ?rest ! ?i" 
          by (metis Suc_lessD arg index_nth_id n_not_Suc_n)

    from aaa have "index (swaps [index xs q - Suc e..<index xs q] xs) q
        = index (swap (index xs q - Suc e) (swaps [index xs q - e..<index xs q] xs)) q" 
          by auto
    also have "\<dots> = (if q = ?rest ! ?i then (Suc ?i) else if q = ?rest ! (Suc ?i) then ?i else index ?rest q)"
        apply(simp only: swap_def arg if_True)
        apply(rule index_swap_if_distinct)
          apply(simp add: iH)
          apply(simp only: arg2)
          by(simp only: arg)
    also have "\<dots> = ?i" using whichcase whichcase2 by simp
    finally show "index (swaps [index xs q - Suc e..<index xs q] xs) q =
              index xs q - Suc e" .
  qed
next
  case 0
  show ?case by simp
qed

term "mtf2"
lemma mtf2_moves_to_front: "distinct xs \<Longrightarrow> q \<in> set xs \<Longrightarrow> index (mtf2 (length xs) q xs) q  = 0"
unfolding mtf2_def
proof -
  assume distxs: "distinct xs"
  assume qinxs: "q \<in> set xs"
  have " index (if q \<in> set xs then swaps [index xs q - length xs..<index xs q] xs else xs) q 
    = index ( swaps [index xs q - length xs..<index xs q] xs) q" using qinxs by auto
  also have "\<dots> = index xs q - (length xs)" apply(rule swapsthrough) using distxs qinxs by auto
  also have "\<dots> = 0" using index_less_size_conv qinxs by (simp add: index_le_size)
  finally show "index (if q \<in> set xs then swaps [index xs q - length xs..<index xs q] xs else xs) q = 0" .
qed




lemma xy_relativorder_mtf2:
  assumes 
    "q\<noteq>x" "q\<noteq>y" "distinct xs" "x\<in>set xs" "y\<in>set xs" "q\<in>set xs"
  shows "x < y in mtf2 n q xs
          = x < y in xs"
using assms
by (metis before_in_setD2 not_before_in x_stays_before_y_if_y_not_moved_to_front)



lemma mtf2_moves_to_frontm1: "distinct xs \<Longrightarrow> q \<in> set xs \<Longrightarrow> index (mtf2 (length xs -1) q xs) q  = 0"
unfolding mtf2_def
proof -
  assume distxs: "distinct xs"
  assume qinxs: "q \<in> set xs"
  have " index (if q \<in> set xs then swaps [index xs q - (length xs -1)..<index xs q] xs else xs) q 
    = index ( swaps [index xs q - (length xs -1)..<index xs q] xs) q" using qinxs by auto
  also have "\<dots> = index xs q - (length xs -1)" apply(rule swapsthrough) using distxs qinxs by auto
  also have "\<dots> = 0" using index_less_size_conv qinxs 
by (metis Suc_pred' gr0I length_pos_if_in_set less_irrefl less_trans_Suc zero_less_diff)
  finally show "index (if q \<in> set xs then swaps [index xs q - (length xs -1)..<index xs q] xs else xs) q = 0" .
qed

lemma mtf2_moves_to_front': "distinct xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x\<noteq>y \<Longrightarrow> x < y in mtf2 (length xs-1) x xs = True"
using mtf2_moves_to_frontm1 by (metis before_in_def gr0I index_eq_index_conv set_mtf2)

lemma mtf2_moves_to_front'': "distinct xs \<Longrightarrow> y \<in> set xs \<Longrightarrow> x \<in> set xs \<Longrightarrow> x\<noteq>y \<Longrightarrow> x < y in mtf2 (length xs) x xs = True"
using mtf2_moves_to_front by (metis before_in_def gr0I index_eq_index_conv set_mtf2)




end
