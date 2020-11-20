(*  Title:       Operations on Iterators over Finite Sets
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>Operations on Set Iterators\<close>
theory SetIteratorOperations
imports Main SetIterator
begin

text\<open>Many operations on sets can be lifted to iterators over sets. This theory tries to introduce
the most useful such operations.\<close>

subsection \<open>Empty set\<close>

text \<open>Iterators over empty sets and singleton sets are very easy to define.\<close>
definition set_iterator_emp :: "('a,'\<sigma>) set_iterator" where
  "set_iterator_emp c f \<sigma>0 = \<sigma>0"

lemma set_iterator_emp_foldli_conv :
  "set_iterator_emp = foldli []"
by (simp add: fun_eq_iff set_iterator_emp_def)

lemma set_iterator_genord_emp_correct :
  "set_iterator_genord set_iterator_emp {} R"
apply (rule set_iterator_genord.intro)
apply (rule exI[where x="[]"])
apply (simp add: set_iterator_emp_foldli_conv)
done

lemma set_iterator_emp_correct :
  "set_iterator set_iterator_emp {}"
using set_iterator_intro [OF set_iterator_genord_emp_correct] .

lemma (in linorder) set_iterator_linord_emp_correct :
  "set_iterator_linord set_iterator_emp {}"
unfolding set_iterator_linord_def
by (fact set_iterator_genord_emp_correct) 

lemma (in linorder) set_iterator_rev_linord_emp_correct :
  "set_iterator_rev_linord set_iterator_emp {}"
unfolding set_iterator_rev_linord_def
by (fact set_iterator_genord_emp_correct) 

lemma (in linorder) map_iterator_linord_emp_correct :
  "map_iterator_linord set_iterator_emp Map.empty"
  "set_iterator_map_linord set_iterator_emp {}"
unfolding set_iterator_map_linord_def
by (simp_all add: set_iterator_genord_emp_correct map_to_set_def) 

lemma (in linorder) map_iterator_rev_linord_emp_correct :
  "map_iterator_rev_linord set_iterator_emp Map.empty"
  "set_iterator_map_rev_linord set_iterator_emp {}"
unfolding set_iterator_map_rev_linord_def
by (simp_all add: set_iterator_genord_emp_correct map_to_set_def) 


subsection\<open>Singleton Sets\<close>

definition set_iterator_sng :: "'a \<Rightarrow> ('a,'\<sigma>) set_iterator" where
  "set_iterator_sng x c f \<sigma>0 = (if c \<sigma>0 then f x \<sigma>0 else \<sigma>0)"

lemma set_iterator_sng_foldli_conv :
  "set_iterator_sng x = foldli [x]"
by (simp add: fun_eq_iff set_iterator_sng_def)

lemma set_iterator_genord_sng_correct :
  "set_iterator_genord (set_iterator_sng (x::'a)) {x} R"
apply (rule set_iterator_genord.intro)
apply (rule exI[where x="[x]"])
apply (simp add: set_iterator_sng_foldli_conv)
done

lemma set_iterator_sng_correct :
  "set_iterator (set_iterator_sng x) {x}"
unfolding set_iterator_def
by (rule set_iterator_genord_sng_correct)

lemma (in linorder) set_iterator_linord_sng_correct :
  "set_iterator_linord (set_iterator_sng x) {x}"
unfolding set_iterator_linord_def
by (simp add: set_iterator_genord_sng_correct) 

lemma (in linorder) set_iterator_rev_linord_sng_correct :
  "set_iterator_rev_linord (set_iterator_sng x) {x}"
unfolding set_iterator_rev_linord_def
by (simp add: set_iterator_genord_sng_correct) 

lemma (in linorder) map_iterator_linord_sng_correct :
  "map_iterator_linord (set_iterator_sng (k,v)) (Map.empty (k \<mapsto> v))"
unfolding set_iterator_map_linord_def
by (simp add: set_iterator_genord_sng_correct) 

lemma (in linorder) map_iterator_rev_linord_sng_correct :
  "map_iterator_rev_linord (set_iterator_sng (k,v)) (Map.empty (k \<mapsto> v))"
unfolding set_iterator_map_rev_linord_def
by (simp add: set_iterator_genord_sng_correct) 


subsection \<open>Union\<close>

text \<open>Iterators over disjoint sets can be combined by first iterating over one and then the
other set. The result is an iterator over the union of the original sets.\<close>

definition set_iterator_union ::
    "('a,'\<sigma>) set_iterator \<Rightarrow> ('a, '\<sigma>) set_iterator \<Rightarrow> ('a,'\<sigma>) set_iterator" where
  "set_iterator_union it_a it_b \<equiv> \<lambda>c f \<sigma>0. (it_b c f (it_a c f \<sigma>0))"

lemma set_iterator_union_foldli_conv :
  "set_iterator_union (foldli as) (foldli bs) = foldli (as @ bs)"
by (simp add: fun_eq_iff set_iterator_union_def foldli_append)

lemma set_iterator_genord_union_correct :
  fixes it_a :: "('a,'\<sigma>) set_iterator"
  fixes it_b :: "('a,'\<sigma>) set_iterator"
  fixes R S_a S_b
  assumes it_a: "set_iterator_genord it_a S_a R"
  assumes it_b: "set_iterator_genord it_b S_b R"
  assumes dist_Sab: "S_a \<inter> S_b = {}"
  assumes R_OK: "\<And>a b. \<lbrakk>a \<in> S_a; b \<in> S_b\<rbrakk> \<Longrightarrow> R a b"
  shows "set_iterator_genord (set_iterator_union it_a it_b) (S_a \<union> S_b) R"
proof -
  from it_a obtain as where 
    dist_as: "distinct as" and S_a_eq: "S_a = set as" and 
    sorted_as: "sorted_wrt R as" and it_a_eq: "it_a = foldli as"
  unfolding set_iterator_genord_foldli_conv by blast

  from it_b obtain bs where 
    dist_bs: "distinct bs" and S_b_eq: "S_b = set bs" and 
    sorted_bs: "sorted_wrt R bs" and it_b_eq: "it_b = foldli bs"
  unfolding set_iterator_genord_foldli_conv by blast

  show ?thesis
  proof (rule set_iterator_genord_I [of "as @ bs"])
    from dist_Sab S_a_eq S_b_eq dist_as dist_bs
    show "distinct (as @ bs)" by simp
  next
    from S_a_eq S_b_eq 
    show "S_a \<union> S_b = set (as @ bs)" by simp
  next
    from sorted_as sorted_bs R_OK S_a_eq S_b_eq
    show "sorted_wrt R (as @ bs)"
      by (simp add: sorted_wrt_append Ball_def)
  next
    show "set_iterator_union it_a it_b = (foldli (as @ bs))"
      unfolding it_a_eq it_b_eq set_iterator_union_foldli_conv by simp
  qed
qed

lemma set_iterator_union_emp [simp] :
  "set_iterator_union (set_iterator_emp) it = it"
  "set_iterator_union it (set_iterator_emp) = it"
unfolding set_iterator_emp_def set_iterator_union_def
by simp_all

lemma set_iterator_union_correct :
  assumes it_a: "set_iterator it_a S_a"
  assumes it_b: "set_iterator it_b S_b"
  assumes dist_Sab: "S_a \<inter> S_b = {}"
  shows "set_iterator (set_iterator_union it_a it_b) (S_a \<union> S_b)"
proof -
  note res' = set_iterator_genord_union_correct [OF it_a[unfolded set_iterator_def] 
                                                    it_b[unfolded set_iterator_def] dist_Sab]
  from set_iterator_intro [OF res']
  show ?thesis by simp
qed

lemma (in linorder) set_iterator_linord_union_correct :
  assumes it_a: "set_iterator_linord it_a S_a"
  assumes it_b: "set_iterator_linord it_b S_b"
  assumes ord_Sab: "\<And>a b. \<lbrakk>a \<in> S_a; b \<in> S_b\<rbrakk> \<Longrightarrow> a < b"
  shows "set_iterator_linord (set_iterator_union it_a it_b) (S_a \<union> S_b)"
unfolding set_iterator_linord_def
apply (rule_tac set_iterator_genord_union_correct[
   OF it_a[unfolded set_iterator_linord_def] it_b[unfolded set_iterator_linord_def]])
apply (insert ord_Sab)
apply auto
apply (metis less_le_not_le ord_Sab)
done

lemma (in linorder) set_iterator_rev_linord_union_correct :
  assumes it_a: "set_iterator_rev_linord it_a S_a"
  assumes it_b: "set_iterator_rev_linord it_b S_b"
  assumes ord_Sab: "\<And>a b. \<lbrakk>a \<in> S_a; b \<in> S_b\<rbrakk> \<Longrightarrow> a > b"
  shows "set_iterator_rev_linord (set_iterator_union it_a it_b) (S_a \<union> S_b)"
unfolding set_iterator_rev_linord_def
apply (rule_tac set_iterator_genord_union_correct[
   OF it_a[unfolded set_iterator_rev_linord_def] it_b[unfolded set_iterator_rev_linord_def]])
apply (insert ord_Sab)
apply auto
apply (metis less_le_not_le ord_Sab)
done

lemma (in linorder) map_iterator_linord_union_correct :
  assumes it_a: "set_iterator_map_linord it_a S_a"
  assumes it_b: "set_iterator_map_linord it_b S_b"
  assumes ord_Sab: "\<And>kv kv'. \<lbrakk>kv \<in> S_a; kv' \<in> S_b\<rbrakk> \<Longrightarrow> fst kv < fst kv'"
  shows "set_iterator_map_linord (set_iterator_union it_a it_b) (S_a \<union> S_b)"
  unfolding set_iterator_map_linord_def
  apply (rule set_iterator_genord_union_correct [OF 
    it_a[unfolded set_iterator_map_linord_def] 
    it_b[unfolded set_iterator_map_linord_def]])
  apply (insert ord_Sab)
  apply auto
  apply (metis less_le_not_le)
done

lemma (in linorder) map_iterator_rev_linord_union_correct :
  assumes it_a: "set_iterator_map_rev_linord it_a S_a"
  assumes it_b: "set_iterator_map_rev_linord it_b S_b"
  assumes ord_Sab: "\<And>kv kv'. \<lbrakk>kv \<in> S_a; kv' \<in> S_b\<rbrakk> \<Longrightarrow> fst kv > fst kv'"
  shows "set_iterator_map_rev_linord (set_iterator_union it_a it_b) (S_a \<union> S_b)"
  unfolding set_iterator_map_rev_linord_def
  apply (rule set_iterator_genord_union_correct [OF 
    it_a[unfolded set_iterator_map_rev_linord_def] 
    it_b[unfolded set_iterator_map_rev_linord_def]])
  apply (insert ord_Sab)
  apply auto
  apply (metis less_le_not_le)
done


subsection \<open>Product\<close>

definition set_iterator_product :: 
    "('a,'\<sigma>) set_iterator \<Rightarrow> ('a \<Rightarrow> ('b,'\<sigma>) set_iterator) \<Rightarrow> ('a \<times> 'b ,'\<sigma>) set_iterator" where
  "set_iterator_product it_a it_b \<equiv> \<lambda>c f \<sigma>0.
    it_a c (
      \<lambda>a \<sigma>. it_b a c (\<lambda>b \<sigma>. f (a,b) \<sigma>) \<sigma>
    ) \<sigma>0"


lemma set_iterator_product_foldli_conv: 
  "set_iterator_product (foldli as) (\<lambda>a. foldli (bs a)) =
   foldli (concat (map (\<lambda>a. map (\<lambda>b. (a, b)) (bs a)) as))"
apply (induct as)
  apply (simp add: set_iterator_product_def)
apply (simp add: set_iterator_product_def foldli_append foldli_map o_def fun_eq_iff)
done

lemma set_iterator_product_it_b_cong: 
assumes it_a_OK: "set_iterator it_a S_a"
    and it_b_b': "\<And>a. a \<in> S_a \<Longrightarrow> it_b a = it_b' a"
shows "set_iterator_product it_a it_b =
       set_iterator_product it_a it_b'"
proof -
  from it_a_OK obtain as where 
    dist_as: "distinct as" and S_a_eq: "S_a = set as" and 
    it_a_eq: "it_a = foldli as"
  unfolding set_iterator_foldli_conv by blast
  
  from it_b_b'[unfolded S_a_eq]
  show ?thesis unfolding it_a_eq
    by (induct as) 
       (simp_all add: set_iterator_product_def it_b_b' fun_eq_iff)
qed

definition set_iterator_product_order ::
  "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow>
   ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" where
  "set_iterator_product_order R_a R_b ab ab' \<longleftrightarrow>
   (if (fst ab = fst ab') then R_b (fst ab) (snd ab) (snd ab') else
                               R_a (fst ab) (fst ab'))"

lemma set_iterator_genord_product_correct :
  fixes it_a :: "('a,'\<sigma>) set_iterator"
  fixes it_b :: "'a \<Rightarrow> ('b,'\<sigma>) set_iterator" 
  assumes it_a: "set_iterator_genord it_a S_a R_a"
  assumes it_b: "\<And>a. a \<in> S_a \<Longrightarrow> set_iterator_genord (it_b a) (S_b a) (R_b a)"
  shows "set_iterator_genord (set_iterator_product it_a it_b) (Sigma S_a S_b) 
             (set_iterator_product_order R_a R_b)"
proof -
  from it_a obtain as where 
    dist_as: "distinct as" and S_a_eq: "S_a = set as" and 
    sorted_as: "sorted_wrt R_a as" and it_a_eq: "it_a = foldli as"
  unfolding set_iterator_genord_foldli_conv by blast

  from it_b obtain bs where 
    dist_bs: "\<And>a. a \<in> set as \<Longrightarrow> distinct (bs a)" and S_b_eq: "\<And>a. a \<in> set as \<Longrightarrow>  S_b a = set (bs a)" and 
    sorted_bs: "\<And>a. a \<in> set as \<Longrightarrow> sorted_wrt (R_b a) (bs a)" and 
    it_b_eq: "\<And>a. a \<in> set as \<Longrightarrow> it_b a = foldli (bs a)"
  unfolding set_iterator_genord_foldli_conv by (metis S_a_eq)

  let ?abs = "concat (map (\<lambda>a. map (\<lambda>b. (a, b)) (bs a)) as)"

  show ?thesis
  proof (rule set_iterator_genord_I[of ?abs])
    from set_iterator_product_it_b_cong[of it_a S_a it_b, 
       OF set_iterator_intro[OF it_a] it_b_eq] it_a_eq S_a_eq
    have "set_iterator_product it_a it_b =
          set_iterator_product (foldli as) (\<lambda>a. foldli (bs a))" by simp
    thus "set_iterator_product it_a it_b = foldli ?abs"
      by (simp add: set_iterator_product_foldli_conv)
  next
    show "distinct ?abs"
    using dist_as dist_bs[unfolded S_a_eq]
    by (induct as) 
       (simp_all add: distinct_map inj_on_def dist_bs set_eq_iff image_iff)
  next
    show "Sigma S_a S_b = set ?abs" 
      unfolding S_a_eq using S_b_eq
      by (induct as) auto  
  next
    from sorted_as sorted_bs dist_as     
    show "sorted_wrt
           (set_iterator_product_order R_a R_b)
           (concat (map (\<lambda>a. map (Pair a) (bs a)) as))"
    proof (induct as rule: list.induct)
      case Nil thus ?case by simp
    next
      case (Cons a as)
      from Cons(2) have R_a_as: "\<And>a'. a' \<in> set as \<Longrightarrow> R_a a a'" and
                        sorted_as: "sorted_wrt R_a as" by simp_all
      from Cons(3) have sorted_bs_a: "sorted_wrt (R_b a) (bs a)" 
                    and sorted_bs_as: "\<And>a. a \<in> set as \<Longrightarrow> sorted_wrt (R_b a) (bs a)" by simp_all
      from Cons(4) have dist_as: "distinct as" and a_nin_as: "a \<notin> set as" by simp_all
      note ind_hyp = Cons(1)[OF sorted_as sorted_bs_as dist_as]
      
      define bs_a where "bs_a = bs a"
      from sorted_bs_a
      have sorted_prod_a : "sorted_wrt (set_iterator_product_order R_a R_b) (map (Pair a) (bs a))"
        unfolding bs_a_def[symmetric]
        apply (induct bs_a rule: list.induct) 
        apply (simp_all add: set_iterator_product_order_def Ball_def image_iff)
      done

      show ?case
        apply (simp add: sorted_wrt_append ind_hyp sorted_prod_a)
        apply (simp add: set_iterator_product_order_def R_a_as a_nin_as)
      done
    qed
  qed
qed

lemma set_iterator_product_correct :
  assumes it_a: "set_iterator it_a S_a"
  assumes it_b: "\<And>a. a \<in> S_a \<Longrightarrow> set_iterator (it_b a) (S_b a)"
  shows "set_iterator (set_iterator_product it_a it_b) (Sigma S_a S_b)"
proof -
  note res' = set_iterator_genord_product_correct [OF it_a[unfolded set_iterator_def], 
     of it_b S_b "\<lambda>_ _ _. True", OF it_b[unfolded set_iterator_def]]
  note res = set_iterator_intro [OF res']
  thus ?thesis by simp
qed


subsection \<open>Filter and Image\<close>

text \<open>Filtering and applying an injective function on iterators is easily defineable as well.
  In contrast to sets the function really has to be injective, because an iterator guarentees to
  visit each element only once.\<close>

definition set_iterator_image_filter ::
    "('a \<Rightarrow> 'b option) \<Rightarrow> ('a,'\<sigma>) set_iterator \<Rightarrow> ('b,'\<sigma>) set_iterator" where
  "set_iterator_image_filter g it \<equiv> \<lambda>c f \<sigma>0. (it c
     (\<lambda>x \<sigma>. (case (g x) of Some x' \<Rightarrow> f x' \<sigma> | None \<Rightarrow> \<sigma>)) \<sigma>0)"

lemma set_iterator_image_filter_foldli_conv :
  "set_iterator_image_filter g (foldli xs) =
   foldli (List.map_filter g xs)"
by (induct xs) (auto simp add: List.map_filter_def set_iterator_image_filter_def fun_eq_iff)  

lemma set_iterator_genord_image_filter_correct :
  fixes it :: "('a,'\<sigma>) set_iterator"
  fixes g :: "'a \<Rightarrow> 'b option"
  assumes it_OK: "set_iterator_genord it S R"
  assumes g_inj_on: "inj_on g (S \<inter> dom g)"
  assumes R'_prop: "\<And>x y x' y'. \<lbrakk>x \<in> S; g x = Some x'; y \<in> S; g y = Some y'; R x y\<rbrakk> \<Longrightarrow> R' x' y'"
  shows "set_iterator_genord (set_iterator_image_filter g it) {y. \<exists>x. x \<in> S \<and> g x = Some y} R'"
proof -
  from it_OK obtain xs where 
    dist_xs: "distinct xs" and S_eq: "S = set xs" and 
    sorted_xs: "sorted_wrt R xs" and it_eq: "it = foldli xs"
  unfolding set_iterator_genord_foldli_conv by blast

  show ?thesis
  proof (rule set_iterator_genord_I [of "List.map_filter g xs"])
    show "set_iterator_image_filter g it =
          foldli (List.map_filter g xs)"
      unfolding it_eq  set_iterator_image_filter_foldli_conv by simp
  next
    from dist_xs g_inj_on[unfolded S_eq]
    show "distinct (List.map_filter g xs)"
      apply (induct xs)
      apply (simp add: List.map_filter_simps) 
      apply (simp add: List.map_filter_def image_iff inj_on_def Ball_def dom_def)
      apply (metis not_Some_eq option.sel)
    done
  next
    show "{y. \<exists>x. x \<in> S \<and> g x = Some y} =
          set (List.map_filter g xs)"
      unfolding S_eq set_map_filter by simp
  next
    from sorted_xs R'_prop[unfolded S_eq]
    show "sorted_wrt R' (List.map_filter g xs)"
    proof (induct xs rule: list.induct)
      case Nil thus ?case by (simp add: List.map_filter_simps) 
    next
      case (Cons x xs)
      note sort_x_xs = Cons(2)
      note R'_x_xs = Cons(3)

      from Cons have ind_hyp: "sorted_wrt R' (List.map_filter g xs)" by auto

      show ?case
        apply (cases "g x")  
        apply (simp add: List.map_filter_simps ind_hyp)
        apply (simp add: List.map_filter_simps set_map_filter Ball_def ind_hyp)
        apply (insert R'_x_xs[of x] sort_x_xs)
        apply (simp add: Ball_def)
        apply metis
      done
    qed
  qed
qed


lemma set_iterator_image_filter_correct :
  fixes it :: "('a,'\<sigma>) set_iterator"
  fixes g :: "'a \<Rightarrow> 'b option"
  assumes it_OK: "set_iterator it S"
  assumes g_inj_on: "inj_on g (S \<inter> dom g)"
  shows "set_iterator (set_iterator_image_filter g it) {y. \<exists>x. x \<in> S \<and> g x = Some y}"
proof -
  note res' = set_iterator_genord_image_filter_correct [OF it_OK[unfolded set_iterator_def], 
     of g "\<lambda>_ _. True"]
  note res = set_iterator_intro [OF res']
  with g_inj_on show ?thesis by simp 
qed


text \<open>Special definitions for only filtering or only appling a function are handy.\<close>
definition set_iterator_filter ::
    "('a \<Rightarrow> bool) \<Rightarrow> ('a,'\<sigma>) set_iterator \<Rightarrow> ('a,'\<sigma>) set_iterator" where
  "set_iterator_filter P \<equiv> set_iterator_image_filter (\<lambda>x. if P x then Some x else None)"

lemma set_iterator_filter_foldli_conv :
  "set_iterator_filter P (foldli xs) = foldli (filter P xs)"
  apply (simp add: set_iterator_filter_def set_iterator_image_filter_foldli_conv)
  apply (rule cong) apply simp
  apply (induct xs)
  apply (simp_all add: List.map_filter_def)
done

lemma set_iterator_filter_alt_def [code] : 
  "set_iterator_filter P it = (\<lambda>c f. it c (\<lambda>(x::'a) (\<sigma>::'b). if P x then f x \<sigma> else \<sigma>))"
proof -
  have "\<And>f. (\<lambda>(x::'a) (\<sigma>::'b).
             case if P x then Some x else None of None \<Rightarrow> \<sigma>
             | Some x' \<Rightarrow> f x' \<sigma>) =
            (\<lambda>x \<sigma>. if P x then f x \<sigma> else \<sigma>)"
     by auto
  thus ?thesis 
    unfolding set_iterator_filter_def
              set_iterator_image_filter_def[abs_def]
    by simp
qed

lemma set_iterator_genord_filter_correct :
  fixes it :: "('a,'\<sigma>) set_iterator"
  assumes it_OK: "set_iterator_genord it S R"
  shows "set_iterator_genord (set_iterator_filter P it) {x. x \<in> S \<and> P x} R"
proof -
  let ?g = "\<lambda>x. if P x then Some x else None"
  have in_dom_g: "\<And>x. x \<in> dom ?g \<longleftrightarrow> P x" unfolding dom_def by auto

  from set_iterator_genord_image_filter_correct [OF it_OK, of ?g R, folded set_iterator_filter_def]
  show ?thesis
    by (simp add: if_split_eq1 inj_on_def Ball_def in_dom_g)
qed

lemma set_iterator_filter_correct :
  assumes it_OK: "set_iterator it S"
  shows "set_iterator (set_iterator_filter P it) {x. x \<in> S \<and> P x}"
proof -
  note res' = set_iterator_genord_filter_correct [OF it_OK[unfolded set_iterator_def], 
    of P]
  note res = set_iterator_intro [OF res']
  thus ?thesis by simp
qed

lemma (in linorder) set_iterator_linord_filter_correct :
  assumes it_OK: "set_iterator_linord it S"
  shows "set_iterator_linord (set_iterator_filter P it) {x. x \<in> S \<and> P x}"
using assms
unfolding set_iterator_linord_def
by (rule set_iterator_genord_filter_correct)

lemma (in linorder) set_iterator_rev_linord_filter_correct :
  assumes it_OK: "set_iterator_rev_linord it S"
  shows "set_iterator_rev_linord (set_iterator_filter P it) {x. x \<in> S \<and> P x}"
using assms
unfolding set_iterator_rev_linord_def
by (rule set_iterator_genord_filter_correct)

definition set_iterator_image ::
    "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'\<sigma>) set_iterator \<Rightarrow> ('b,'\<sigma>) set_iterator" where
  "set_iterator_image g \<equiv> set_iterator_image_filter (\<lambda>x. Some (g x))"

lemma set_iterator_image_foldli_conv :
  "set_iterator_image g (foldli xs) = foldli (map g xs)"
  apply (simp add: set_iterator_image_def set_iterator_image_filter_foldli_conv)
  apply (rule cong) apply simp
  apply (induct xs)
  apply (simp_all add: List.map_filter_def)
done

lemma set_iterator_image_alt_def [code] : 
  "set_iterator_image g it = (\<lambda>c f. it c (\<lambda>x. f (g x)))"
unfolding set_iterator_image_def
          set_iterator_image_filter_def[abs_def]
by simp

lemma set_iterator_genord_image_correct :
  fixes it :: "('a,'\<sigma>) set_iterator"
  assumes it_OK: "set_iterator_genord it S R"
  assumes g_inj: "inj_on g S"
  assumes R'_prop: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; R x y\<rbrakk> \<Longrightarrow> R' (g x) (g y)"
  shows "set_iterator_genord (set_iterator_image g it) (g ` S) R'"
proof -
  let ?g = "\<lambda>x. Some (g x)"
  have set_eq: "\<And>S. {y . \<exists>x. x \<in> S \<and> ?g x = Some y} = g ` S" by auto

  show ?thesis
    apply (rule set_iterator_genord_image_filter_correct [OF it_OK, of ?g R', 
     folded set_iterator_image_def set_eq[symmetric]])
    apply (insert g_inj, simp add: inj_on_def) []
    apply (insert R'_prop, auto)
  done
qed

lemma set_iterator_image_correct :
  assumes it_OK: "set_iterator it S"
  assumes g_inj: "inj_on g S"
  assumes S'_OK: "S' = g ` S"
  shows "set_iterator (set_iterator_image g it) S'"
proof -
  note res' = set_iterator_genord_image_correct [OF it_OK[unfolded set_iterator_def] g_inj, 
    of "\<lambda>_ _. True"]
  note res = set_iterator_intro [OF res', folded S'_OK]
  thus ?thesis by simp
qed



subsection \<open>Construction from list (foldli)\<close>

text \<open>Iterators correspond by definition to iteration over distinct lists. They fix an order 
 in which the elements are visited. Therefore, it is trivial to construct an iterator from a 
 distinct list.\<close>

lemma set_iterator_genord_foldli_correct :
"distinct xs \<Longrightarrow> sorted_wrt R xs \<Longrightarrow> set_iterator_genord (foldli xs) (set xs) R"
by (rule set_iterator_genord_I[of xs]) (simp_all)

lemma set_iterator_foldli_correct :
"distinct xs \<Longrightarrow> set_iterator (foldli xs) (set xs)"
by (rule set_iterator_I[of xs]) (simp_all)

lemma (in linorder) set_iterator_linord_foldli_correct :
assumes dist_xs: "distinct xs"
assumes sorted_xs: "sorted xs"
shows "set_iterator_linord (foldli xs) (set xs)"
using assms
by (rule_tac set_iterator_linord_I[of xs]) (simp_all)


lemma (in linorder) set_iterator_rev_linord_foldli_correct :
assumes dist_xs: "distinct xs"
assumes sorted_xs: "sorted (rev xs)"
shows "set_iterator_rev_linord (foldli xs) (set xs)"
using assms
by (rule_tac set_iterator_rev_linord_I[of xs]) (simp_all)


lemma map_iterator_genord_foldli_correct :
"distinct (map fst xs) \<Longrightarrow> sorted_wrt R xs \<Longrightarrow> map_iterator_genord (foldli xs) (map_of xs) R"
by (rule map_iterator_genord_I[of xs]) simp_all

lemma map_iterator_foldli_correct :
"distinct (map fst xs) \<Longrightarrow> map_iterator (foldli xs) (map_of xs)"
by (rule map_iterator_I[of xs]) (simp_all)

lemma (in linorder) map_iterator_linord_foldli_correct :
assumes dist_xs: "distinct (map fst xs)"
assumes sorted_xs: "sorted (map fst xs)"
shows "map_iterator_linord (foldli xs) (map_of xs)"
using assms
by (rule_tac map_iterator_linord_I[of xs]) (simp_all)


lemma (in linorder) map_iterator_rev_linord_foldli_correct :
assumes dist_xs: "distinct (map fst xs)"
assumes sorted_xs: "sorted (rev (map fst xs))"
shows "map_iterator_rev_linord (foldli xs) (map_of xs)"
using assms
by (rule_tac map_iterator_rev_linord_I[of xs]) (simp_all)


subsection \<open>Construction from list (foldri)\<close>

lemma set_iterator_genord_foldri_correct :
"distinct xs \<Longrightarrow> sorted_wrt R (rev xs) \<Longrightarrow> set_iterator_genord (foldri xs) (set xs) R"
by (rule set_iterator_genord_I[of "rev xs"]) (simp_all add: foldri_def)

lemma set_iterator_foldri_correct :
"distinct xs \<Longrightarrow> set_iterator (foldri xs) (set xs)"
by (rule set_iterator_I[of "rev xs"]) (simp_all add: foldri_def)

lemma (in linorder) set_iterator_linord_foldri_correct :
assumes dist_xs: "distinct xs"
assumes sorted_xs: "sorted (rev xs)"
shows "set_iterator_linord (foldri xs) (set xs)"
using assms
by (rule_tac set_iterator_linord_I[of "rev xs"]) (simp_all add: foldri_def)

lemma (in linorder) set_iterator_rev_linord_foldri_correct :
assumes dist_xs: "distinct xs"
assumes sorted_xs: "sorted xs"
shows "set_iterator_rev_linord (foldri xs) (set xs)"
using assms
by (rule_tac set_iterator_rev_linord_I[of "rev xs"]) (simp_all add: foldri_def)

lemma map_iterator_genord_foldri_correct :
"distinct (map fst xs) \<Longrightarrow> sorted_wrt R (rev xs) \<Longrightarrow> map_iterator_genord (foldri xs) (map_of xs) R"
by (rule map_iterator_genord_I[of "rev xs"]) 
   (simp_all add: rev_map[symmetric] foldri_def)

lemma map_iterator_foldri_correct :
"distinct (map fst xs) \<Longrightarrow> map_iterator (foldri xs) (map_of xs)"
by (rule map_iterator_I[of "rev xs"]) 
   (simp_all add: rev_map[symmetric] foldri_def)

lemma (in linorder) map_iterator_linord_foldri_correct :
assumes dist_xs: "distinct (map fst xs)"
assumes sorted_xs: "sorted (rev (map fst xs))"
shows "map_iterator_linord (foldri xs) (map_of xs)"
using assms
by (rule_tac map_iterator_linord_I[of "rev xs"]) 
   (simp_all add: rev_map[symmetric] foldri_def)

lemma (in linorder) map_iterator_rev_linord_foldri_correct :
assumes dist_xs: "distinct (map fst xs)"
assumes sorted_xs: "sorted (map fst xs)"
shows "map_iterator_rev_linord (foldri xs) (map_of xs)"
using assms
by (rule_tac map_iterator_rev_linord_I[of "rev xs"]) 
   (simp_all add: rev_map[symmetric] foldri_def)


subsection \<open>Iterators over Maps\<close>

text \<open>In the following iterator over the key-value pairs of a finite map are called
 iterators over maps. Operations for such iterators are presented.\<close>

subsubsection\<open>Domain Iterator\<close>

text \<open>One very simple such operation is iterating over only the keys of the map.\<close>

definition map_iterator_dom where
  "map_iterator_dom it = set_iterator_image fst it"

lemma map_iterator_dom_foldli_conv :
  "map_iterator_dom (foldli kvs) = foldli (map fst kvs)"
unfolding map_iterator_dom_def set_iterator_image_foldli_conv by simp

lemma map_iterator_genord_dom_correct :
  assumes it_OK: "map_iterator_genord it m R"
  assumes R'_prop: "\<And>k v k' v'. \<lbrakk>m k = Some v; m k' = Some v'; R (k, v) (k', v')\<rbrakk> \<Longrightarrow> R' k k'"
  shows "set_iterator_genord (map_iterator_dom it) (dom m) R'"
proof -
  have pre1: "inj_on fst (map_to_set m)" 
     unfolding inj_on_def map_to_set_def by simp

  from set_iterator_genord_image_correct[OF it_OK pre1, of R'] R'_prop
  show ?thesis
    unfolding map_iterator_dom_def map_to_set_dom[symmetric]
    by (auto simp add: map_to_set_def)
qed

lemma map_iterator_dom_correct :
  assumes it_OK: "map_iterator it m"
  shows "set_iterator (map_iterator_dom it) (dom m)"
using assms
unfolding set_iterator_def 
apply (rule_tac map_iterator_genord_dom_correct)
apply simp_all
done

lemma (in linorder) map_iterator_linord_dom_correct :
  assumes it_OK: "map_iterator_linord it m"
  shows "set_iterator_linord (map_iterator_dom it) (dom m)"
using assms
unfolding set_iterator_linord_def set_iterator_map_linord_def  
apply (rule_tac map_iterator_genord_dom_correct)
apply assumption
apply auto
done

lemma (in linorder) map_iterator_rev_linord_dom_correct :
  assumes it_OK: "map_iterator_rev_linord it m"
  shows "set_iterator_rev_linord (map_iterator_dom it) (dom m)"
using assms
unfolding set_iterator_rev_linord_def set_iterator_map_rev_linord_def
apply (rule_tac map_iterator_genord_dom_correct)
apply assumption
apply auto
done


subsubsection\<open>Domain Iterator with Filter\<close>

text \<open>More complex is iterating over only the keys such that the key-value pairs satisfy some
        property.\<close>

definition map_iterator_dom_filter ::
    "('a \<times> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b,'\<sigma>) set_iterator \<Rightarrow> ('a,'\<sigma>) set_iterator" where
  "map_iterator_dom_filter P it \<equiv> set_iterator_image_filter 
     (\<lambda>xy. if P xy then Some (fst xy) else None) it"

lemma map_iterator_dom_filter_alt_def [code] :
  "map_iterator_dom_filter P it = 
   (\<lambda>c f. it c (\<lambda>kv \<sigma>. if P kv then f (fst kv) \<sigma> else \<sigma>))"
unfolding map_iterator_dom_filter_def set_iterator_image_filter_def
apply (rule ext)
apply (rule ext)
apply (rule arg_cong2[where f="it"])
apply (simp)
apply (simp add: fun_eq_iff split: option.splits)
done

lemma map_iterator_genord_dom_filter_correct :
  fixes it :: "('a \<times> 'b, '\<sigma>) set_iterator"
  assumes it_OK: "set_iterator_genord it (map_to_set m) R"
  assumes R'_prop: "\<And>k1 v1 k2 v2.
      \<lbrakk>m k1 = Some v1; P (k1, v1);
       m k2 = Some v2; P (k2, v2); R (k1, v1) (k2, v2)\<rbrakk> \<Longrightarrow> R' k1 k2"
  shows "set_iterator_genord (map_iterator_dom_filter P it) {k . \<exists>v. m k = Some v \<and> P (k, v)} R'"
proof - 
  define g where "g xy = (if P xy then Some (fst xy) else None)" for xy :: "'a \<times> 'b"

  note set_iterator_genord_image_filter_correct [OF it_OK, of g R']

  have g_eq_Some: "\<And>kv k. g kv = Some k \<longleftrightarrow> ((k = fst kv) \<and> P kv)"
    unfolding g_def by (auto split: prod.splits option.splits)

  have "\<And>x1 x2 y. x1 \<in> map_to_set m \<Longrightarrow> x2 \<in> map_to_set m \<Longrightarrow>
                  g x1 = Some y \<Longrightarrow> g x2 = Some y \<Longrightarrow> x1 = x2"
  proof -
    fix x1 x2 y
    assume x1_in: "x1 \<in> map_to_set m"
       and x2_in: "x2 \<in> map_to_set m"
       and g1_eq: "g x1 = Some y" 
       and g2_eq: "g x2 = Some y"

    obtain k1 v1 where x1_eq[simp] : "x1 = (k1, v1)" by (rule prod.exhaust)
    obtain k2 v2 where x2_eq[simp] : "x2 = (k2, v2)" by (rule prod.exhaust)

    from g1_eq g2_eq g_eq_Some have k1_eq: "k1 = k2" by simp 
    with x1_in x2_in have v1_eq: "v1 = v2"
      unfolding map_to_set_def by simp
    from k1_eq v1_eq show "x1 = x2" by simp
  qed
  hence g_inj_on: "inj_on g (map_to_set m \<inter> dom g)"
    unfolding inj_on_def dom_def by auto

  have g_eq_Some: "\<And>x y. (g x = Some y) \<longleftrightarrow> (P x \<and> y = (fst x))"
    unfolding g_def by auto

  have "set_iterator_genord (set_iterator_image_filter g it)
            {y. \<exists>x. x \<in> map_to_set m \<and> g x = Some y} R'" 
    apply (rule set_iterator_genord_image_filter_correct [OF it_OK, of g R', OF g_inj_on])
    apply (insert R'_prop) 
    apply (auto simp add: g_eq_Some map_to_set_def)
  done
  thus ?thesis
    unfolding map_iterator_dom_filter_def g_def[symmetric]
    by (simp add: g_eq_Some map_to_set_def)
qed

lemma map_iterator_dom_filter_correct :
  assumes it_OK: "map_iterator it m"
  shows "set_iterator (map_iterator_dom_filter P it) {k. \<exists>v. m k = Some v \<and> P (k, v)}"
using assms
unfolding set_iterator_def
apply (rule_tac map_iterator_genord_dom_filter_correct)
apply simp_all
done

lemma (in linorder) map_iterator_linord_dom_filter_correct :
  assumes it_OK: "map_iterator_linord it m"
  shows "set_iterator_linord (map_iterator_dom_filter P it) {k. \<exists>v. m k = Some v \<and> P (k, v)}"
using assms
unfolding set_iterator_map_linord_def set_iterator_linord_def 
apply (rule_tac map_iterator_genord_dom_filter_correct 
  [where R = "\<lambda>(k,_) (k',_). k\<le>k'"])
apply (simp_all add: set_iterator_def)
done

lemma (in linorder) set_iterator_rev_linord_map_filter_correct :
  assumes it_OK: "map_iterator_rev_linord it m"
  shows "set_iterator_rev_linord (map_iterator_dom_filter P it) 
  {k. \<exists>v. m k = Some v \<and> P (k, v)}"
using assms
unfolding set_iterator_map_rev_linord_def set_iterator_rev_linord_def 
apply (rule_tac map_iterator_genord_dom_filter_correct 
  [where R = "\<lambda>(k,_) (k',_). k\<ge>k'"])
apply (simp_all add: set_iterator_def)
done


subsubsection\<open>Product for Maps\<close>

definition map_iterator_product where
  "map_iterator_product it_a it_b =
   set_iterator_image (\<lambda>kvv'. (fst (fst kvv'), snd kvv')) 
    (set_iterator_product it_a (\<lambda>kv. it_b (snd kv)))"

lemma map_iterator_product_foldli_conv :
"map_iterator_product (foldli as) (\<lambda>a. foldli (bs a)) = 
 foldli (concat (map (\<lambda>(k, v). map (Pair k) (bs v)) as))"
unfolding map_iterator_product_def set_iterator_product_foldli_conv set_iterator_image_foldli_conv
by (simp add: map_concat o_def split_def) 

lemma map_iterator_product_alt_def [code] :
  "map_iterator_product it_a it_b = 
   (\<lambda>c f. it_a c (\<lambda>a. it_b (snd a) c (\<lambda>b. f (fst a, b))))"
unfolding map_iterator_product_def set_iterator_product_def set_iterator_image_alt_def
by simp

lemma map_iterator_genord_product_correct :
  fixes it_a :: "(('k \<times> 'v),'\<sigma>) set_iterator"
  fixes it_b :: "'v \<Rightarrow> ('e,'\<sigma>) set_iterator" 
  fixes S_a S_b R_a R_b m
  assumes it_a: "map_iterator_genord it_a m R_a"
  assumes it_b: "\<And>k v. m k = Some v \<Longrightarrow> set_iterator_genord (it_b v) (S_b v) (R_b v)"
  assumes R'_prop: "\<And>k v u k' v' u'.
       m k = Some v \<Longrightarrow>
       u \<in> S_b v \<Longrightarrow>
       m k' = Some v' \<Longrightarrow>
       u' \<in> S_b v' \<Longrightarrow>
       if k = k' then R_b v u u'
       else R_a (k, v) (k', v') \<Longrightarrow>
       R_ab (k, u) (k', u')"
  shows "set_iterator_genord (map_iterator_product it_a it_b) 
     {(k, e) . (\<exists>v. m k = Some v \<and> e \<in> S_b v)} R_ab"
proof -
  from it_b have it_b': "\<And>kv. kv \<in> map_to_set m \<Longrightarrow>
       set_iterator_genord (it_b (snd kv)) (S_b (snd kv)) (R_b (snd kv))"
    unfolding map_to_set_def by (case_tac kv, simp)

  have "(\<Union>x\<in>{(k, v). m k = Some v}. \<Union>y\<in>S_b (snd x). {(x, y)}) = {((k,v), e) . 
          (m k = Some v) \<and> e \<in> S_b v}" by (auto)
  with set_iterator_genord_product_correct [OF it_a, of "\<lambda>kv. it_b (snd kv)" 
    "\<lambda>kv. S_b (snd kv)" "\<lambda>kv. R_b (snd kv)", OF it_b']
  have it_ab': "set_iterator_genord (set_iterator_product it_a (\<lambda>kv. it_b (snd kv)))
      {((k,v), e) . (m k = Some v) \<and> e \<in> S_b v}
      (set_iterator_product_order R_a
        (\<lambda>kv. R_b (snd kv)))"
     (is "set_iterator_genord ?it_ab' ?S_ab' ?R_ab'")
    unfolding map_to_set_def
    by (simp add: Sigma_def)

  let ?g = "\<lambda>kvv'. (fst (fst kvv'), snd kvv')"
  have inj_g: "inj_on ?g ?S_ab'"
    unfolding inj_on_def by simp

  have R_ab_OK: "\<And>x y.
      x \<in> {((k, v), e). m k = Some v \<and> e \<in> S_b v} \<Longrightarrow>
      y \<in> {((k, v), e). m k = Some v \<and> e \<in> S_b v} \<Longrightarrow>
      set_iterator_product_order R_a (\<lambda>kv. R_b (snd kv)) x y \<Longrightarrow>
      R_ab (fst (fst x), snd x) (fst (fst y), snd y)"
    apply (simp add: set_iterator_product_order_def)
    apply clarify
    apply (simp)
    apply (unfold fst_conv snd_conv)
    apply (metis R'_prop option.inject)
  done

  have "(?g ` {((k, v), e). m k = Some v \<and> e \<in> S_b v}) = {(k, e). \<exists>v. m k = Some v \<and> e \<in> S_b v}" 
    by (simp add: image_iff set_eq_iff)
  with set_iterator_genord_image_correct [OF it_ab' inj_g, of R_ab, OF R_ab_OK]
  show ?thesis 
    by (simp add: map_iterator_product_def)
qed

lemma map_iterator_product_correct :
  assumes it_a: "map_iterator it_a m"
  assumes it_b: "\<And>k v. m k = Some v \<Longrightarrow> set_iterator (it_b v) (S_b v)"
  shows "set_iterator (map_iterator_product it_a it_b) 
         {(k, e) . (\<exists>v. m k = Some v \<and> e \<in> S_b v)}"
proof -
  note res' = map_iterator_genord_product_correct [OF it_a[unfolded set_iterator_def], 
     of it_b S_b "\<lambda>_ _ _. True"]
  note res = set_iterator_intro [OF res']
  with it_b show ?thesis unfolding set_iterator_def by simp
qed

  
subsubsection\<open>Key Filter\<close>

definition map_iterator_key_filter ::
    "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b,'\<sigma>) set_iterator \<Rightarrow> ('a \<times> 'b,'\<sigma>) set_iterator" where
  "map_iterator_key_filter P \<equiv> set_iterator_filter (P \<circ> fst)"

lemma map_iterator_key_filter_foldli_conv :
  "map_iterator_key_filter P (foldli kvs) =  foldli (filter (\<lambda>(k, v). P k) kvs)"
unfolding map_iterator_key_filter_def set_iterator_filter_foldli_conv o_def split_def 
by simp

lemma map_iterator_key_filter_alt_def [code] :
  "map_iterator_key_filter P it = (\<lambda>c f. it c (\<lambda>x \<sigma>. if P (fst x) then f x \<sigma> else \<sigma>))"
unfolding map_iterator_key_filter_def set_iterator_filter_alt_def
  set_iterator_image_filter_def by simp

lemma map_iterator_genord_key_filter_correct :
  fixes it :: "('a \<times> 'b, '\<sigma>) set_iterator"
  assumes it_OK: "map_iterator_genord it m R"
  shows "map_iterator_genord (map_iterator_key_filter P it) (m |` {k . P k}) R"
proof - 
  from set_iterator_genord_filter_correct [OF it_OK, of "P \<circ> fst", 
    folded map_iterator_key_filter_def] 
  have step1: "set_iterator_genord (map_iterator_key_filter P it)
                  {x \<in> map_to_set m. (P \<circ> fst) x} R" 
    by simp

  have "{x \<in> map_to_set m. (P \<circ> fst) x} = map_to_set (m |` {k . P k})"
    unfolding map_to_set_def restrict_map_def
    by (auto split: if_splits)
  with step1 show ?thesis by simp
qed

lemma map_iterator_key_filter_correct :
  assumes it_OK: "map_iterator it m"
  shows "set_iterator (map_iterator_key_filter P it) (map_to_set (m |` {k . P k}))"
using assms
unfolding set_iterator_def
apply (rule_tac map_iterator_genord_key_filter_correct)
apply simp_all
done

end


