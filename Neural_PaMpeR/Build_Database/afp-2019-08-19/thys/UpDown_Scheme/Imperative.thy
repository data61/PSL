section \<open> Imperative Version \<close>

theory Imperative
imports UpDown_Scheme Separation_Logic_Imperative_HOL.Sep_Main
begin

type_synonym pointmap = "grid_point \<Rightarrow> nat"
type_synonym impgrid = "rat array"

instance rat :: heap ..

primrec rat_pair where "rat_pair (a, b) = (of_rat a, of_rat b)"

declare rat_pair.simps [simp del]

definition
   zipWithA :: "('a::heap \<Rightarrow> 'b::heap \<Rightarrow> 'a::heap) \<Rightarrow> 'a array \<Rightarrow> 'b array \<Rightarrow> 'a array Heap"
where
  "zipWithA f a b = do {
     n \<leftarrow> Array.len a;
     Heap_Monad.fold_map (\<lambda>n. do {
       x \<leftarrow> Array.nth a n ;
       y \<leftarrow> Array.nth b n ;
       Array.upd n (f x y) a
     }) [0..<n];
     return a
   }"

theorem zipWithA [sep_heap_rules]:
  fixes xs ys :: "'a::heap list"
  assumes "length xs = length ys"
  shows "< a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys > zipWithA f a b < \<lambda>r. (a \<mapsto>\<^sub>a map (case_prod f) (zip xs ys)) * b \<mapsto>\<^sub>a ys * \<up>(a = r) >"
proof -
  { fix n and xs :: "'a list"
    let ?part_res = "\<lambda>n xs. (map (case_prod f) (zip (take n xs) (take n ys)) @ drop n xs)"
    assume "n \<le> length xs" "length xs = length ys"
    then have "< a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys > Heap_Monad.fold_map (\<lambda>n. do {
         x \<leftarrow> Array.nth a n ;
         y \<leftarrow> Array.nth b n ;
         Array.upd n (f x y) a
       }) [0..<n] < \<lambda>r. a \<mapsto>\<^sub>a ?part_res n xs * b \<mapsto>\<^sub>a ys >"
    proof (induct n arbitrary: xs)
      case 0 then show ?case by sep_auto
    next
      case (Suc n)
      note Suc.hyps [sep_heap_rules]
      have *: "(?part_res n xs)[n := f (?part_res n xs ! n) (ys ! n)] =  ?part_res (Suc n) xs"
        using Suc.prems by (simp add: nth_append take_Suc_conv_app_nth upd_conv_take_nth_drop)
      from Suc.prems show ?case
        by (sep_auto simp add: fold_map_append *)
    qed }
  note this[sep_heap_rules]
  show ?thesis
    unfolding zipWithA_def
    by (sep_auto simp add: assms)
qed

definition copy_array :: "'a::heap array \<Rightarrow> ('a::heap array) Heap" where
  "copy_array a = Array.freeze a \<bind> Array.of_list"

theorem copy_array [sep_heap_rules]:
  "< a \<mapsto>\<^sub>a xs > copy_array a < \<lambda>r. a \<mapsto>\<^sub>a xs * r \<mapsto>\<^sub>a xs >"
  unfolding copy_array_def
  by sep_auto

definition sum_array :: "rat array \<Rightarrow> rat array \<Rightarrow> unit Heap" where
  "sum_array a b = zipWithA (+) a b \<then> return ()"

theorem sum_array [sep_heap_rules]:
  fixes xs ys :: "rat list"
  shows "length xs = length ys \<Longrightarrow> < a \<mapsto>\<^sub>a xs * b \<mapsto>\<^sub>a ys > sum_array a b < \<lambda>r. (a \<mapsto>\<^sub>a map (\<lambda>(a, b). a + b) (zip xs ys)) * b \<mapsto>\<^sub>a ys >"
  unfolding sum_array_def by sep_auto

locale linearization =
  fixes dm lm :: nat
  fixes pm :: pointmap
  assumes pm: "bij_betw pm (sparsegrid dm lm) {..< card (sparsegrid dm lm)}"
begin

lemma linearizationD:
  "p \<in> sparsegrid dm lm \<Longrightarrow> pm p < card (sparsegrid dm lm)"
  using pm by (auto simp: bij_betw_def)

definition gridI :: "impgrid \<Rightarrow> (grid_point \<Rightarrow> real) \<Rightarrow> assn" where
  "gridI a v =
    (\<exists>\<^sub>A xs. a \<mapsto>\<^sub>a xs * \<up>((\<forall>p\<in>sparsegrid dm lm. v p = of_rat (xs ! pm p)) \<and> length xs = card (sparsegrid dm lm)))"

lemma gridI_nth_rule [sep_heap_rules]:
  "g \<in> sparsegrid dm lm \<Longrightarrow> < gridI a v > Array.nth a (pm g) <\<lambda>r. gridI a v * \<up> (of_rat r = v g)>"
  using pm by (sep_auto simp: bij_betw_def gridI_def)

lemma gridI_upd_rule [sep_heap_rules]:
  "g \<in> sparsegrid dm lm \<Longrightarrow>
    < gridI a v > Array.upd (pm g) x a <\<lambda>a'. gridI a (fun_upd v g (of_rat x)) * \<up>(a' = a)>"
  unfolding gridI_def using pm
  by (sep_auto simp: bij_betw_def inj_onD intro!: nth_list_update_eq[symmetric] nth_list_update_neq[symmetric])

primrec upI' :: "nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> impgrid \<Rightarrow> (rat * rat) Heap" where
  "upI' d       0 p a = return (0, 0)" |
  "upI' d (Suc l) p a = do {
       (fl, fml) \<leftarrow> upI' d l (child p left d) a ;
       (fmr, fr) \<leftarrow> upI' d l (child p right d) a ;
       val \<leftarrow> Array.nth a (pm p) ;
       Array.upd (pm p) (fml + fmr) a ;
       let result = ((fml + fmr + val / 2 ^ (lv p d) / 2) / 2) ;
       return (fl + result, fr + result)
     }"

lemma upI' [sep_heap_rules]:
  assumes lin[simp]: "d < dm"
    and l: "level p + l = lm" "l = 0 \<or> p \<in> sparsegrid dm lm"
  shows "< gridI a v > upI' d l p a <\<lambda>r. let (r', v') = up' d l p v in gridI a v' * \<up>(rat_pair r = r') >"
  using l
proof (induct l arbitrary: p v)
  note rat_pair.simps [simp]
  case 0 then show ?case by sep_auto
next
  case (Suc l)
  from Suc.prems \<open>d < dm\<close>
  have [simp]: "level (child p left d) + l = lm" "level (child p right d) + l = lm" "p \<in> sparsegrid dm lm"
    by (auto simp: sparsegrid_length)

  have [simp]: "child p left d \<notin> sparsegrid dm lm \<Longrightarrow> l = 0" "child p right d \<notin> sparsegrid dm lm \<Longrightarrow> l = 0"
    using Suc.prems by (auto simp: sparsegrid_def lgrid_def)

  note Suc(1)[sep_heap_rules]
  show ?case
    by (sep_auto split: prod.split simp: of_rat_add of_rat_divide of_rat_power of_rat_mult rat_pair_def Let_def)
qed

primrec downI' :: "nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> impgrid \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> unit Heap" where
  "downI' d       0 p a fl fr = return ()" |
  "downI' d (Suc l) p a fl fr = do {
      val \<leftarrow> Array.nth a (pm p) ;
      let fm = ((fl + fr) / 2 + val) ;
      Array.upd (pm p) (((fl + fr) / 4 + (1 / 3) * val) / 2 ^ (lv p d)) a ;
      downI' d l (child p left d) a fl fm ;
      downI' d l (child p right d) a fm fr
    }"

lemma downI' [sep_heap_rules]:
  assumes lin[simp]: "d < dm"
    and l: "level p + l = lm" "l = 0 \<or> p \<in> sparsegrid dm lm"
  shows "< gridI a v > downI' d l p a fl fr <\<lambda>r. gridI a (down' d l p (of_rat fl) (of_rat fr) v) >"
  using l
proof (induct l arbitrary: p v fl fr)
  note rat_pair.simps [simp]
  case 0 then show ?case by sep_auto
next
  case (Suc l)
  from Suc.prems \<open>d < dm\<close>
  have [simp]: "level (child p left d) + l = lm" "level (child p right d) + l = lm" "p \<in> sparsegrid dm lm"
    by (auto simp: sparsegrid_length)

  have [simp]: "child p left d \<notin> sparsegrid dm lm \<Longrightarrow> l = 0" "child p right d \<notin> sparsegrid dm lm \<Longrightarrow> l = 0"
    using Suc.prems by (auto simp: sparsegrid_def lgrid_def)

  note Suc(1)[sep_heap_rules]
  show ?case
    by (sep_auto split: prod.split simp: of_rat_add of_rat_divide of_rat_power of_rat_mult rat_pair_def Let_def fun_upd_def)
qed

definition liftI :: "(nat \<Rightarrow> nat \<Rightarrow> grid_point \<Rightarrow> impgrid \<Rightarrow> unit Heap) \<Rightarrow> nat \<Rightarrow> impgrid \<Rightarrow> unit Heap" where
  "liftI f d a = 
    foldr (\<lambda> p n. n \<then> f d (lm - level p) p a) (gridgen (start dm) ({ 0 ..< dm } - { d }) lm) (return ())"

theorem liftI [sep_heap_rules]:
  assumes "d < dm"
  and f[sep_heap_rules]: "\<And>v p. p \<in> lgrid (start dm) ({0..<dm} - {d}) lm \<Longrightarrow>
    < gridI a v > f d (lm - level p) p a <\<lambda>r. gridI a (f' d (lm - level p) p v) >"
  shows "< gridI a v > liftI f d a <\<lambda>r. gridI a (Grid.lift f' dm lm d v) >"
proof -
  let ?ds = "{0..<dm} - {d}" and ?g = "gridI a"
  { fix ps assume "set ps \<subseteq> set (gridgen (start dm) ?ds lm)" and "distinct ps"
    then have "< ?g v >
        foldr (\<lambda>p n. (n :: unit Heap) \<then> f d (lm - level p) p a) ps (return ())
      <\<lambda>r. ?g (foldr (\<lambda>p \<alpha>. f' d (lm - level p) p \<alpha>) ps v) >"
      by (induct ps arbitrary: v) (sep_auto simp: gridgen_lgrid_eq)+ }
  from this[OF subset_refl gridgen_distinct]
  show ?thesis
    by (simp add: liftI_def Grid.lift_def)
qed

definition upI where "upI = liftI (\<lambda>d l p a. upI' d l p a \<then> return ())"

theorem upI [sep_heap_rules]:
  assumes [simp]: "d < dm"
  shows "< gridI a v > upI d a <\<lambda>r. gridI a (up dm lm d v) > "
  unfolding up_def upI_def
  by (sep_auto simp: lgrid_def sparsegrid_def lgrid_def split: prod.split
               intro: grid_union_dims[of "{0..<dm} - {d}" "{0..<dm}"])

definition downI where "downI = liftI (\<lambda>d l p a. downI' d l p a 0 0)"

theorem downI [sep_heap_rules]:
  assumes [simp]: "d < dm"
  shows "< gridI a v > downI d a <\<lambda>r. gridI a (down dm lm d v) > "
  unfolding down_def downI_def
  by (sep_auto simp: lgrid_def sparsegrid_def lgrid_def split: prod.split
               intro: grid_union_dims[of "{0..<dm} - {d}" "{0..<dm}"])

theorem copy_array_gridI [sep_heap_rules]:
  "< gridI a v > copy_array a < \<lambda>r. gridI a v * gridI r v >"
  unfolding gridI_def
  by sep_auto

theorem sum_array_gridI [sep_heap_rules]:
  "< gridI a v * gridI b w > sum_array a b < \<lambda>r. gridI a (sum_vector v w) * gridI b w >"
  unfolding gridI_def
  by (sep_auto simp: sum_vector_def nth_map linearizationD of_rat_add)

primrec updownI' :: "nat \<Rightarrow> impgrid \<Rightarrow> unit Heap" where
  "updownI' 0 a = return ()" |
  "updownI' (Suc d) a = do {
      b \<leftarrow> copy_array a ;
      upI d a ;
      updownI' d a ;
      updownI' d b ;
      downI d b ;
      sum_array a b
    }"

theorem updownI' [sep_heap_rules]:
  "d \<le> dm \<Longrightarrow> < gridI a v > updownI' d a <\<lambda>r. gridI a (updown' dm lm d v) >\<^sub>t"
proof (induct d arbitrary: a v)
  case (Suc d)
  note Suc.hyps [sep_heap_rules]
  from Suc.prems show ?case
    by sep_auto
qed sep_auto

definition updownI where "updownI a = updownI' dm a"

theorem updownI [sep_heap_rules]:
  "< gridI a v > updownI a <\<lambda>r. gridI a (updown dm lm v) >\<^sub>t"
  unfolding updown_def updownI_def by sep_auto

end

end

