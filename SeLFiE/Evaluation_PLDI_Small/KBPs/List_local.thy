
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory List_local
imports Extra "HOL-Library.While_Combinator"
begin


text\<open>Partition a list with respect to an equivalence relation.\<close>

text\<open>First up: split a list according to a relation.\<close>

abbreviation "rel_ext r \<equiv> { x . r x }"

definition
  partition_split_body :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<times> 'a list \<Rightarrow> 'a list \<times> 'a list"
where
  [code]: "partition_split_body r x \<equiv> \<lambda>y (X', xc).
            if r (x, y) then (X', List.insert y xc) else (List.insert y X', xc)"

definition
  partition_split :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list"
where
  [code]: "partition_split r x xs \<equiv> foldr (partition_split_body r x) xs ([], [])"

lemma partition_split:
  shows "set (fst (partition_split r x xs)) = set xs - (rel_ext r `` {x})"
    and "set (snd (partition_split r x xs)) = set xs \<inter> (rel_ext r `` {x})"
proof(induct xs)
  case Nil
  { case 1 with Nil show ?case
      unfolding partition_split_def by simp }
  { case 2 with Nil show ?case
      unfolding partition_split_def by simp }
next
  case (Cons x xs)
  { case 1 with Cons show ?case
      unfolding partition_split_def
      apply simp
      apply (subst partition_split_body_def)
      apply (split prod.split)
      apply clarsimp
      apply rule
       apply clarsimp
      apply clarsimp
      unfolding Image_def
      apply auto
      done }
  { case 2 with Cons show ?case
      unfolding partition_split_def
      apply simp
      apply (subst partition_split_body_def)
      apply (split prod.split)
      apply clarsimp
      apply rule
       apply clarsimp
      apply clarsimp
      done }
qed

lemma partition_split':
  assumes "partition_split r x xs = (xxs', xec)"
  shows "set xxs' = set xs - (rel_ext r `` {x})"
    and "set xec = set xs \<inter> (rel_ext r `` {x})"
  using assms partition_split[where r=r and x=x and xs=xs]
  by simp_all

text\<open>Next, split an list on each of its members. For this to be
unambiguous @{term "r"} must be an equivalence relation.\<close>

definition
  partition_aux_body :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<times> 'a list list \<Rightarrow> 'a list \<times> 'a list list"
where
  "partition_aux_body \<equiv> \<lambda>r (xxs, ecs). case xxs of [] \<Rightarrow> ([], []) | x # xs \<Rightarrow>
                           let (xxs', xec) = partition_split r x xs
                            in (xxs', (x # xec) # ecs)"

definition
  partition_aux :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<times> 'a list list"
where
  [code]: "partition_aux r xs \<equiv>
             while (Not \<circ> List.null \<circ> fst) (partition_aux_body r) (xs, [])"

(* FIXME move these. *)

lemma equiv_subseteq_in_sym:
  "\<lbrakk> r `` X \<subseteq> X;  (x, y) \<in> r; y \<in> X; equiv Y r; X \<subseteq> Y \<rbrakk> \<Longrightarrow> x \<in> X"
  unfolding equiv_def by (auto dest: symD)

lemma FIXME_refl_on_insert_absorb[simp]:
  "\<lbrakk> refl_on A r; x \<in> A \<rbrakk> \<Longrightarrow> insert x (r `` {x}) = r `` {x}"
  by (auto dest: refl_onD)

lemma equiv_subset[intro]:
  "\<lbrakk> equiv A r; B \<subseteq> A \<rbrakk> \<Longrightarrow> equiv B (r \<inter> B \<times> B)"
  unfolding equiv_def by (auto intro: refl_onI symI transI dest: refl_onD symD transD)

lemma FIXME_fiddle1: "\<lbrakk> x \<in> Y; X \<subseteq> Y; refl_on Y r \<rbrakk> \<Longrightarrow> insert x (X \<inter> r `` {x}) = (insert x X) \<inter> r `` {x}"
  by (auto dest: refl_onD)

lemma FIXME_second_fiddle:
  "\<lbrakk> (r \<inter> Y \<times> Y) `` X \<subseteq> X; refl_on Z r; x \<in> X; X \<subseteq> Y; Y \<subseteq> Z \<rbrakk>
     \<Longrightarrow> (r \<inter> (Y - (X - r `` {x})) \<times> (Y - (X - r `` {x}))) `` {x}
       = (r \<inter> X \<times> X) `` {x}"
  by (blast dest: refl_onD)

lemma FIXME_third_fiddle:
  "\<lbrakk> (r \<inter> Y \<times> Y) `` X \<subseteq> X; X \<subseteq> Y; x \<in> X; y \<in> Y - X    ;    r `` {y} \<inter> X = {} \<rbrakk>
     \<Longrightarrow> (r \<inter> (Y - (X - r `` {x})) \<times> (Y - (X - r `` {x}))) `` {y}
       = (r \<inter> (Y - X) \<times> (Y - X)) `` {y}"
  by auto

lemma partition_aux:
  assumes equiv: "equiv X (rel_ext r)"
      and XZ: "set xs \<subseteq> X"
  shows "fst (partition_aux r xs) = []
       \<and> set ` set (snd (partition_aux r xs))
       = (set xs // (rel_ext r \<inter> set xs \<times> set xs))"
proof -
  let ?b = "Not \<circ> List.null \<circ> fst"
  let ?c = "partition_aux_body r"
  let ?r' = "\<lambda>A. rel_ext r \<inter> A \<times> A"
  let ?P1 = "\<lambda>(A, B). set A \<subseteq> set xs"
  let ?P2 = "\<lambda>(A, B). ?r' (set xs) `` set A \<subseteq> set A"
  let ?P3 = "\<lambda>(A, B). set ` set B = ((set xs - set A) // ?r' (set xs - set A))"
  let ?P = "\<lambda>AB. ?P1 AB \<and> ?P2 AB \<and> ?P3 AB"
  let ?wfr = "inv_image finite_psubset (set \<circ> fst)"
  show ?thesis
  unfolding partition_aux_def
  proof(rule while_rule[where P="?P" and r="?wfr"])
    from equiv XZ show "?P (xs, [])" by auto
  next
    fix s assume P: "?P s" and b: "?b s"

    obtain A B where s: "s = (A, B)" by (cases s) blast

    moreover
    from XZ P s have "?P1 (?c (A, B))"
      unfolding partition_aux_body_def
      by (auto simp add: partition_split' split: list.split prod.split)

    moreover
    from equiv XZ P s have "?P2 (?c s)"
      apply (cases A)
      unfolding partition_aux_body_def
      apply simp_all
      subgoal for a as
        apply (cases "partition_split r a as")
        apply (simp add: partition_split')
        unfolding equiv_def
        apply (auto dest: symD transD elim: quotientE)
        done
      done

    moreover
    have "?P3 (?c s)"
    proof -
      from b s obtain x where x: "x \<in> set A" by (cases A) (auto iff: null_def)
      with XZ equiv P b s x
      show ?thesis
      
        unfolding partition_aux_body_def
        apply clarsimp
        apply (erule equivE)
        apply (cases A)
         apply simp
        apply simp
        apply (case_tac "partition_split r a list")
        apply clarsimp
        apply (simp add: partition_split')

        apply (subst FIXME_fiddle1[where Y=X])
           apply blast
          apply auto[1]
         apply blast

        apply rule
         apply clarsimp
         apply rule
          apply (rule_tac x=a in quotientI2)
           apply (blast dest: refl_onD)
          using XZ
          apply (auto dest: refl_onD)[1]
         apply clarsimp
         apply (erule quotientE)
         apply clarsimp
         apply (rule_tac x=xa in quotientI2)
          apply (blast dest: refl_onD)
         apply rule
          apply clarsimp
         apply clarsimp
         apply rule
          apply rule
          apply clarsimp
          apply (cut_tac X="insert a (set list)" and Y="set xs" and x=xa and y=a and r="rel_ext r \<inter> set xs \<times> set xs" in equiv_subseteq_in_sym)
          apply simp_all
          using equiv
          apply blast
         apply clarsimp
         apply (cut_tac X="insert a (set list)" and Y="set xs" and x=xa and y=xb and r="rel_ext r \<inter> set xs \<times> set xs" in equiv_subseteq_in_sym)
         apply simp_all
         using equiv
         apply blast

        apply (rule subsetI)
        apply (erule quotientE)
        apply (case_tac "xaa = a")
         apply auto[1]
        apply clarsimp

        apply (case_tac "xa \<in> set list")
         apply clarsimp
         apply rule
          apply (auto dest: transD)[1]
         apply (auto dest: symD transD)[1]

        unfolding quotient_def
        apply clarsimp
        apply (erule_tac x=xa in ballE)
         unfolding Image_def
         apply clarsimp
        apply (auto dest: symD transD)  (* SLOW *)
        done
    qed

    ultimately show "?P (?c s)" by auto
  next
    fix s assume P: "?P s" and b: "\<not> (?b s)"
    from b have F: "fst s = []"
      apply (cases s)
      apply simp
      apply (case_tac a)
      apply (simp_all add: List.null_def)
      done
    from equiv P F have S: "set ` set (snd s) = (set xs // ?r' (set xs))"
      apply (cases s)
      unfolding Image_def
      apply simp
      done
    from F S show "fst s = [] \<and> set ` set (snd s) = (set xs // ?r' (set xs))"
      by (simp add: prod_eqI)
  next
    show "wf ?wfr" by (blast intro: wf_finite_psubset Int_lower2 [THEN [2] wf_subset])
  next
    fix s assume P: "?P s" and b: "?b s"
    from equiv XZ P b have "set (fst (?c s)) \<subset> set (fst s)"
      apply -
      apply (cases s)
      apply (simp add: Let_def)
      unfolding partition_aux_body_def
      apply clarsimp
      apply (case_tac a)
       apply (simp add: List.null_def)
      apply simp
      apply (case_tac "partition_split r aa list")
      apply (simp add: partition_split')

      unfolding equiv_def
      apply (auto dest: refl_onD)
      done
    thus "(?c s, s) \<in> ?wfr" by auto
  qed
qed

definition
  partition :: "('a \<times> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list"
where
  [code]: "partition r xs \<equiv> snd (partition_aux r xs)"

lemma partition:
  assumes equiv: "equiv X (rel_ext r)"
      and xs: "set xs \<subseteq> X"
  shows "set ` set (partition r xs) = set xs // ((rel_ext r) \<inter> set xs \<times> set xs)"
  unfolding partition_def
  using partition_aux[OF equiv xs] by simp

(* **************************************** *)

fun
  odlist_equal :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "odlist_equal [] [] = True"
| "odlist_equal [] ys = False"
| "odlist_equal xs [] = False"
| "odlist_equal (x # xs) (y # ys) = (x = y \<and> odlist_equal xs ys)"

declare odlist_equal.simps [code]

lemma equal_odlist_equal[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> odlist_equal xs ys \<longleftrightarrow> (xs = ys)"
  by (induct xs ys rule: odlist_equal.induct) (auto)

fun
  difference :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "difference [] ys = []"
| "difference xs [] = xs"
| "difference (x # xs) (y # ys) =
     (if x = y then difference xs ys
               else if x < y then x # difference xs (y # ys)
                             else difference (x # xs) ys)"

declare difference.simps [code]

lemma set_difference[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> set (difference xs ys) = set xs - set ys"
  by (induct xs ys rule: difference.induct) (auto)

lemma distinct_sorted_difference[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> distinct (difference xs ys) \<and> sorted (difference xs ys)"
  by (induct xs ys rule: difference.induct) (auto)

fun
  intersection :: "('a :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "intersection [] ys = []"
| "intersection xs [] = []"
| "intersection (x # xs) (y # ys) =
     (if x = y then x # intersection xs ys
               else if x < y then intersection xs (y # ys)
                             else intersection (x # xs) ys)"

declare intersection.simps [code]

lemma set_intersection[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> set (intersection xs ys) = set xs \<inter> set ys"
  by (induct xs ys rule: intersection.induct) (auto)

lemma distinct_sorted_intersection[simp]:
  "\<lbrakk> distinct xs; distinct ys; sorted xs; sorted ys \<rbrakk>
     \<Longrightarrow> distinct (intersection xs ys) \<and> sorted (intersection xs ys)"
  by (induct xs ys rule: intersection.induct) (auto)

(* This is a variant of zipWith *)
fun
  image :: "('a :: linorder \<times> 'b :: linorder) list \<Rightarrow> 'a list \<Rightarrow> 'b list"
where
  "image [] xs = []"
| "image R []  = []"
| "image ((x, y) # rs) (z # zs) =
     (if x = z then y # image rs (z # zs)
               else if x < z then image rs (z # zs)
                             else image ((x, y) # rs) zs)"

declare image.simps [code]

lemma set_image[simp]:
  "\<lbrakk> distinct R; distinct xs; sorted R; sorted xs \<rbrakk>
     \<Longrightarrow> set (image R xs) = set R `` set xs"
  by (induct R xs rule: image.induct) (auto iff: less_eq_prod_def)

(* Extra lemmas that really belong in List.thy *)

lemma sorted_filter[simp]:
  "sorted xs \<Longrightarrow> sorted (filter P xs)"
  by (induct xs) (auto)

lemma map_prod_eq:
  assumes f: "map fst xs = map fst ys"
      and s: "map snd xs = map snd ys"
  shows "xs = ys"
  using assms by (fact pair_list_eqI)

lemma list_choose_hd:
  assumes "\<forall>x \<in> set xs. P x"
      and "x \<in> set xs"
  shows "P (List.hd xs)"
  using assms by (induct xs arbitrary: x) auto

end
