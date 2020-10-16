section \<open>\isaheader{Orderings By Comparison Operator}\<close>
theory Intf_Comp
imports 
  Automatic_Refinement.Automatic_Refinement
begin

subsection \<open>Basic Definitions\<close>

datatype comp_res = LESS | EQUAL | GREATER

consts i_comp_res :: interface
abbreviation "comp_res_rel \<equiv> Id :: (comp_res \<times> _) set"
lemmas [autoref_rel_intf] = REL_INTFI[of comp_res_rel i_comp_res]

definition "comp2le cmp a b \<equiv> 
  case cmp a b of LESS \<Rightarrow> True | EQUAL \<Rightarrow> True | GREATER \<Rightarrow> False"

definition "comp2lt cmp a b \<equiv> 
  case cmp a b of LESS \<Rightarrow> True | EQUAL \<Rightarrow> False | GREATER \<Rightarrow> False"

definition "comp2eq cmp a b \<equiv> 
  case cmp a b of LESS \<Rightarrow> False | EQUAL \<Rightarrow> True | GREATER \<Rightarrow> False"

locale linorder_on =
  fixes D :: "'a set"
  fixes cmp :: "'a \<Rightarrow> 'a \<Rightarrow> comp_res"
  assumes lt_eq: "\<lbrakk>x\<in>D; y\<in>D\<rbrakk> \<Longrightarrow> cmp x y = LESS \<longleftrightarrow> (cmp y x = GREATER)"
  assumes refl[simp, intro!]: "x\<in>D \<Longrightarrow> cmp x x = EQUAL"
  assumes trans[trans]: 
    "\<lbrakk> x\<in>D; y\<in>D; z\<in>D; cmp x y = LESS; cmp y z = LESS\<rbrakk> \<Longrightarrow> cmp x z = LESS"
    "\<lbrakk> x\<in>D; y\<in>D; z\<in>D; cmp x y = LESS; cmp y z = EQUAL\<rbrakk> \<Longrightarrow> cmp x z = LESS"
    "\<lbrakk> x\<in>D; y\<in>D; z\<in>D; cmp x y = EQUAL; cmp y z = LESS\<rbrakk> \<Longrightarrow> cmp x z = LESS"
    "\<lbrakk> x\<in>D; y\<in>D; z\<in>D; cmp x y = EQUAL; cmp y z = EQUAL\<rbrakk> \<Longrightarrow> cmp x z = EQUAL"
begin
  abbreviation "le \<equiv> comp2le cmp"
  abbreviation "lt \<equiv> comp2lt cmp"

  lemma eq_sym: "\<lbrakk>x\<in>D; y\<in>D\<rbrakk> \<Longrightarrow> cmp x y = EQUAL \<Longrightarrow> cmp y x = EQUAL"
    apply (cases "cmp y x")
    using lt_eq lt_eq[symmetric]
    by auto
end

abbreviation "linorder \<equiv> linorder_on UNIV"

lemma linorder_to_class:
  assumes "linorder cmp" 
  assumes [simp]: "\<And>x y. cmp x y = EQUAL \<Longrightarrow> x=y"
  shows "class.linorder (comp2le cmp) (comp2lt cmp)"
proof -
  interpret linorder_on UNIV cmp by fact
  show ?thesis
    apply (unfold_locales)
    unfolding comp2le_def comp2lt_def
    apply (auto split: comp_res.split comp_res.split_asm)
    using lt_eq apply simp
    using lt_eq apply simp
    using lt_eq[symmetric] apply simp
    apply (drule (1) trans[rotated 3], simp_all) []
    apply (drule (1) trans[rotated 3], simp_all) []
    apply (drule (1) trans[rotated 3], simp_all) []
    apply (drule (1) trans[rotated 3], simp_all) []
    using lt_eq apply simp
    using lt_eq apply simp
    using lt_eq[symmetric] apply simp
    done
qed

definition "dflt_cmp le lt a b \<equiv> 
  if lt a b then LESS 
  else if le a b then EQUAL 
  else GREATER"

lemma (in linorder) class_to_linorder:
  "linorder (dflt_cmp (\<le>) (<))"
  apply (unfold_locales)
  unfolding dflt_cmp_def
  by (auto split: if_split_asm)

lemma restrict_linorder: "\<lbrakk>linorder_on D cmp ; D'\<subseteq>D\<rbrakk> \<Longrightarrow> linorder_on D' cmp"
  apply (rule linorder_on.intro)
  apply (drule (1) rev_subsetD)+
  apply (erule (2) linorder_on.lt_eq)
  apply (drule (1) rev_subsetD)+
  apply (erule (1) linorder_on.refl)
  apply (drule (1) rev_subsetD)+
  apply (erule (5) linorder_on.trans)
  apply (drule (1) rev_subsetD)+
  apply (erule (5) linorder_on.trans)
  apply (drule (1) rev_subsetD)+
  apply (erule (5) linorder_on.trans)
  apply (drule (1) rev_subsetD)+
  apply (erule (5) linorder_on.trans)
  done

subsection \<open>Operations on Linear Orderings\<close>

text \<open>Map with injective function\<close>
definition cmp_img where "cmp_img f cmp a b \<equiv> cmp (f a) (f b)"

lemma img_linorder[intro?]: 
  assumes LO: "linorder_on (f`D) cmp"
  shows "linorder_on D (cmp_img f cmp)"
  apply unfold_locales
  unfolding cmp_img_def
  apply (rule linorder_on.lt_eq[OF LO], auto) []
  apply (rule linorder_on.refl[OF LO], auto) []
  apply (erule (1) linorder_on.trans[OF LO, rotated -2], auto) []
  apply (erule (1) linorder_on.trans[OF LO, rotated -2], auto) []
  apply (erule (1) linorder_on.trans[OF LO, rotated -2], auto) []
  apply (erule (1) linorder_on.trans[OF LO, rotated -2], auto) []
  done

text \<open>Combine\<close>
definition "cmp_combine D1 cmp1 D2 cmp2 a b \<equiv> 
  if a\<in>D1 \<and> b\<in>D1 then cmp1 a b
  else if a\<in>D1 \<and> b\<in>D2 then LESS
  else if a\<in>D2 \<and> b\<in>D1 then GREATER
  else cmp2 a b
"

(* TODO: Move *)
lemma UnE': 
  assumes "x\<in>A\<union>B"
  obtains "x\<in>A" | "x\<notin>A" "x\<in>B"
  using assms by blast

lemma combine_linorder[intro?]:
  assumes "linorder_on D1 cmp1"
  assumes "linorder_on D2 cmp2"
  assumes "D = D1\<union>D2"
  shows "linorder_on D (cmp_combine D1 cmp1 D2 cmp2)"
  apply unfold_locales
  unfolding cmp_combine_def
  using assms apply -
  apply (simp only:)
  apply (elim UnE)
  apply (auto dest: linorder_on.lt_eq) [4]

  apply (simp only:)
  apply (elim UnE)
  apply (auto dest: linorder_on.refl) [2]

  apply (simp only:)
  apply (elim UnE')
  apply simp_all [8]
  apply (erule (5) linorder_on.trans)
  apply (erule (5) linorder_on.trans)

  apply (simp only:)
  apply (elim UnE')
  apply simp_all [8]
  apply (erule (5) linorder_on.trans)
  apply (erule (5) linorder_on.trans)

  apply (simp only:)
  apply (elim UnE')
  apply simp_all [8]
  apply (erule (5) linorder_on.trans)
  apply (erule (5) linorder_on.trans)

  apply (simp only:)
  apply (elim UnE')
  apply simp_all [8]
  apply (erule (5) linorder_on.trans)
  apply (erule (5) linorder_on.trans)
  done

subsection \<open>Universal Linear Ordering\<close>
text \<open>With Zorn's Lemma, we get a universal linear (even wf) ordering\<close>

definition "univ_order_rel \<equiv> (SOME r. well_order_on UNIV r)"
definition "univ_cmp x y \<equiv> 
  if x=y then EQUAL 
  else if (x,y)\<in>univ_order_rel then LESS
  else GREATER"

lemma univ_wo: "well_order_on UNIV univ_order_rel"
  unfolding univ_order_rel_def
  using well_order_on[of UNIV]
  ..

lemma univ_linorder[intro?]: "linorder univ_cmp"
  apply unfold_locales
  unfolding univ_cmp_def 
  apply (auto split: if_split_asm)
  using univ_wo
  apply -
  unfolding well_order_on_def linear_order_on_def partial_order_on_def
    preorder_on_def
  apply (auto simp add: antisym_def) []
  apply (unfold total_on_def, fast) []
  apply (unfold trans_def, fast) []
  apply (auto simp add: antisym_def) []
  done

text \<open>Extend any linear order to a universal order\<close>
definition "cmp_extend D cmp \<equiv> 
  cmp_combine D cmp UNIV univ_cmp"

lemma extend_linorder[intro?]: 
  "linorder_on D cmp \<Longrightarrow> linorder (cmp_extend D cmp)"
  unfolding cmp_extend_def
  apply rule
  apply assumption
  apply rule
  by simp

subsubsection \<open>Lexicographic Order on Lists\<close>  

fun cmp_lex where
  "cmp_lex cmp [] [] = EQUAL"
| "cmp_lex cmp [] _ = LESS"
| "cmp_lex cmp _ [] = GREATER"
| "cmp_lex cmp (a#l) (b#m) = (
    case cmp a b of
      LESS \<Rightarrow> LESS
    | EQUAL \<Rightarrow> cmp_lex cmp l m
    | GREATER \<Rightarrow> GREATER)"

primrec cmp_lex' where
  "cmp_lex' cmp [] m = (case m of [] \<Rightarrow> EQUAL | _ \<Rightarrow> LESS)"
| "cmp_lex' cmp (a#l) m = (case m of [] \<Rightarrow> GREATER | (b#m) \<Rightarrow> 
    (case cmp a b of
      LESS \<Rightarrow> LESS
    | EQUAL \<Rightarrow> cmp_lex' cmp l m
    | GREATER \<Rightarrow> GREATER
  ))"

lemma cmp_lex_alt: "cmp_lex cmp l m = cmp_lex' cmp l m"
  apply (induct l arbitrary: m)
  apply (auto split: comp_res.split list.split)
  done

lemma (in linorder_on) lex_linorder[intro?]:
  "linorder_on (lists D) (cmp_lex cmp)"
proof
  fix l m
  assume "l\<in>lists D" "m\<in>lists D"
  thus "(cmp_lex cmp l m = LESS) = (cmp_lex cmp m l = GREATER)"
    apply (induct cmp\<equiv>cmp l m rule: cmp_lex.induct)
    apply (auto split: comp_res.split simp: lt_eq)
    apply (auto simp: lt_eq[symmetric])
    done
next
  fix x
  assume "x\<in>lists D"
  thus "cmp_lex cmp x x = EQUAL"
    by (induct x) auto
next
  fix x y z
  assume M: "x\<in>lists D" "y\<in>lists D" "z\<in>lists D"

  {
    assume "cmp_lex cmp x y = LESS" "cmp_lex cmp y z = LESS"
    thus "cmp_lex cmp x z = LESS"
      using M
      apply (induct cmp\<equiv>cmp x y arbitrary: z rule: cmp_lex.induct)
      apply (auto split: comp_res.split_asm comp_res.split)
      apply (case_tac z, auto) []
      apply (case_tac z,
        auto split: comp_res.split_asm comp_res.split,
        (drule (4) trans, simp)+
      ) []
      apply (case_tac z,
        auto split: comp_res.split_asm comp_res.split,
        (drule (4) trans, simp)+
      ) []
      done
  }

  {
    assume "cmp_lex cmp x y = LESS" "cmp_lex cmp y z = EQUAL"
    thus "cmp_lex cmp x z = LESS"
      using M
      apply (induct cmp\<equiv>cmp x y arbitrary: z rule: cmp_lex.induct)
      apply (auto split: comp_res.split_asm comp_res.split)
      apply (case_tac z, auto) []
      apply (case_tac z,
        auto split: comp_res.split_asm comp_res.split,
        (drule (4) trans, simp)+
      ) []
      apply (case_tac z,
        auto split: comp_res.split_asm comp_res.split,
        (drule (4) trans, simp)+
      ) []
      done
  }

  {
    assume "cmp_lex cmp x y = EQUAL" "cmp_lex cmp y z = LESS"
    thus "cmp_lex cmp x z = LESS"
      using M
      apply (induct cmp\<equiv>cmp x y arbitrary: z rule: cmp_lex.induct)
      apply (auto split: comp_res.split_asm comp_res.split)
      apply (case_tac z,
        auto split: comp_res.split_asm comp_res.split,
        (drule (4) trans, simp)+
      ) []
      done
  }

  {
    assume "cmp_lex cmp x y = EQUAL" "cmp_lex cmp y z = EQUAL"
    thus "cmp_lex cmp x z = EQUAL"
      using M
      apply (induct cmp\<equiv>cmp x y arbitrary: z rule: cmp_lex.induct)
      apply (auto split: comp_res.split_asm comp_res.split)
      apply (case_tac z)
      apply (auto split: comp_res.split_asm comp_res.split)
      apply (drule (4) trans, simp)+
      done
  }
qed

subsubsection \<open>Lexicographic Order on Pairs\<close>  

fun cmp_prod where 
  "cmp_prod cmp1 cmp2 (a1,a2) (b1,b2) 
  = (
    case cmp1 a1 b1 of
      LESS \<Rightarrow> LESS
    | EQUAL \<Rightarrow> cmp2 a2 b2
    | GREATER \<Rightarrow> GREATER)"

lemma cmp_prod_alt: "cmp_prod = (\<lambda>cmp1 cmp2 (a1,a2) (b1,b2). (
    case cmp1 a1 b1 of
      LESS \<Rightarrow> LESS
    | EQUAL \<Rightarrow> cmp2 a2 b2
    | GREATER \<Rightarrow> GREATER))"
  by (auto intro!: ext)

lemma prod_linorder[intro?]: 
  assumes A: "linorder_on A cmp1" 
  assumes B: "linorder_on B cmp2" 
  shows "linorder_on (A\<times>B) (cmp_prod cmp1 cmp2)"
proof -
  interpret A: linorder_on A cmp1
    + B: linorder_on B cmp2 by fact+

  show ?thesis
    apply unfold_locales
    apply (auto split: comp_res.split comp_res.split_asm,
      simp_all add: A.lt_eq B.lt_eq,
      simp_all add: A.lt_eq[symmetric]
      ) []

    apply (auto split: comp_res.split comp_res.split_asm) []

    apply (auto split: comp_res.split comp_res.split_asm) []
    apply (drule (4) A.trans B.trans, simp)+

    apply (auto split: comp_res.split comp_res.split_asm) []
    apply (drule (4) A.trans B.trans, simp)+

    apply (auto split: comp_res.split comp_res.split_asm) []
    apply (drule (4) A.trans B.trans, simp)+

    apply (auto split: comp_res.split comp_res.split_asm) []
    apply (drule (4) A.trans B.trans, simp)+
    done
qed

subsection \<open>Universal Ordering for Sets that is Effective for Finite Sets\<close>

subsubsection \<open>Sorted Lists of Sets\<close>
text \<open>Some more results about sorted lists of finite sets\<close>

lemma set_to_map_set_is_map_of: 
  "distinct (map fst l) \<Longrightarrow> set_to_map (set l) = map_of l"
  apply (induct l)
  apply (auto simp: set_to_map_insert)
  done

context linorder begin

  lemma sorted_list_of_set_eq_nil[simp]:
    assumes "finite A" 
    shows "sorted_list_of_set A = [] \<longleftrightarrow> A={}"
    using assms
    apply (induct rule: finite_induct)
    apply simp
    apply simp
    done

  lemma sorted_list_of_set_eq_nil2[simp]:
    assumes "finite A" 
    shows "[] = sorted_list_of_set A \<longleftrightarrow> A={}"
    using assms
    by (auto dest: sym)

  lemma set_insort[simp]: "set (insort x l) = insert x (set l)"
    by (induct l) auto

  lemma sorted_list_of_set_inj_aux:
    fixes A B :: "'a set"
    assumes "finite A" 
    assumes "finite B" 
    assumes "sorted_list_of_set A = sorted_list_of_set B"
    shows "A=B"
    using assms
  proof -
    from \<open>finite B\<close> have "B = set (sorted_list_of_set B)" by simp
    also from assms have "\<dots> = set (sorted_list_of_set (A))"
      by simp
    also from \<open>finite A\<close> 
    have "set (sorted_list_of_set (A)) = A"
      by simp
    finally show ?thesis by simp
  qed

  lemma sorted_list_of_set_inj: "inj_on sorted_list_of_set (Collect finite)"
    apply (rule inj_onI)
    using sorted_list_of_set_inj_aux
    by blast
 
  lemma the_sorted_list_of_set:
    assumes "distinct l"
    assumes "sorted l"
    shows "sorted_list_of_set (set l) = l"
    using assms
    by (simp 
      add: sorted_list_of_set_sort_remdups distinct_remdups_id sorted_sort_id)


  definition "sorted_list_of_map m \<equiv> 
    map (\<lambda>k. (k, the (m k))) (sorted_list_of_set (dom m))"

  lemma the_sorted_list_of_map:
    assumes "distinct (map fst l)"
    assumes "sorted (map fst l)"
    shows "sorted_list_of_map (map_of l) = l"
  proof -
    have "dom (map_of l) = set (map fst l)" by (induct l) force+
    hence "sorted_list_of_set (dom (map_of l)) = map fst l"
      using the_sorted_list_of_set[OF assms] by simp
    hence "sorted_list_of_map (map_of l) 
      = map (\<lambda>k. (k, the (map_of l k))) (map fst l)"
      unfolding sorted_list_of_map_def by simp
    also have "\<dots> = l" using \<open>distinct (map fst l)\<close>
    proof (induct l)
      case Nil thus ?case by simp
    next
      case (Cons a l) 
      hence 
        1: "distinct (map fst l)" 
        and 2: "fst a\<notin>fst`set l" 
        and 3: "map (\<lambda>k. (k, the (map_of l k))) (map fst l) = l" 
        by simp_all

      from 2 have [simp]: "\<not>(\<exists>x\<in>set l. fst x = fst a)"
        by (auto simp: image_iff)

      show ?case
        apply simp
        apply (subst (3) 3[symmetric])
        apply simp
        done
    qed
    finally show ?thesis .
  qed

  lemma map_of_sorted_list_of_map[simp]:
    assumes FIN: "finite (dom m)" 
    shows "map_of (sorted_list_of_map m) = m"
    unfolding sorted_list_of_map_def
  proof -
    have "set (sorted_list_of_set (dom m)) = dom m"
      and DIST: "distinct (sorted_list_of_set (dom m))"
      by (simp_all add: FIN) 

    have [simp]: "(fst \<circ> (\<lambda>k. (k, the (m k)))) = id" by auto

    have [simp]: "(\<lambda>k. (k, the (m k))) ` dom m = map_to_set m"
      by (auto simp: map_to_set_def)

    show "map_of (map (\<lambda>k. (k, the (m k))) (sorted_list_of_set (dom m))) = m"
      apply (subst set_to_map_set_is_map_of[symmetric])
      apply (simp add: DIST)
      apply (subst set_map)
      apply (simp add: FIN map_to_set_inverse)
      done
  qed

  lemma sorted_list_of_map_inj_aux:
    fixes A B :: "'a\<rightharpoonup>'b"
    assumes [simp]: "finite (dom A)" 
    assumes [simp]: "finite (dom B)" 
    assumes E: "sorted_list_of_map A = sorted_list_of_map B"
    shows "A=B"
    using assms
  proof -
    have "A = map_of (sorted_list_of_map A)" by simp
    also note E
    also have "map_of (sorted_list_of_map B) = B" by simp
    finally show ?thesis .
  qed

  lemma sorted_list_of_map_inj: 
    "inj_on sorted_list_of_map (Collect (finite o dom))"
    apply (rule inj_onI)
    using sorted_list_of_map_inj_aux
    by auto
end

definition "cmp_set cmp \<equiv> 
  cmp_extend (Collect finite) (
    cmp_img
      (linorder.sorted_list_of_set (comp2le cmp)) 
      (cmp_lex cmp)
  )"

thm img_linorder

lemma set_ord_linear[intro?]: 
  "linorder cmp \<Longrightarrow> linorder (cmp_set cmp)"
  unfolding cmp_set_def
  apply rule
  apply rule
  apply (rule restrict_linorder)
  apply (erule linorder_on.lex_linorder)
  apply simp
  done

definition "cmp_map cmpk cmpv \<equiv>
  cmp_extend (Collect (finite o dom)) (
    cmp_img
      (linorder.sorted_list_of_map (comp2le cmpk))
      (cmp_lex (cmp_prod cmpk cmpv))
  )
"

lemma map_to_set_inj[intro!]: "inj map_to_set"
  apply (rule inj_onI)
  unfolding map_to_set_def
  apply (rule ext)
  apply (case_tac "x xa")
  apply (case_tac [!] "y xa")
  apply force+
  done

corollary map_to_set_inj'[intro!]: "inj_on map_to_set S"
  by (metis map_to_set_inj subset_UNIV subset_inj_on)
  
lemma map_ord_linear[intro?]: 
  assumes A: "linorder cmpk" 
  assumes B: "linorder cmpv" 
  shows "linorder (cmp_map cmpk cmpv)"
proof -
  interpret lk: linorder_on UNIV cmpk by fact
  interpret lv: linorder_on UNIV cmpv by fact
  
  show ?thesis
    unfolding cmp_map_def
    apply rule
    apply rule
    apply (rule restrict_linorder)
    apply (rule linorder_on.lex_linorder)
    apply (rule)
    apply fact
    apply fact
    apply simp
    done
qed
  
  
locale eq_linorder_on = linorder_on +
  assumes cmp_imp_equal: "\<lbrakk>x\<in>D; y\<in>D\<rbrakk> \<Longrightarrow> cmp x y = EQUAL \<Longrightarrow> x = y"
begin
  lemma cmp_eq[simp]: "\<lbrakk>x\<in>D; y\<in>D\<rbrakk> \<Longrightarrow> cmp x y = EQUAL \<longleftrightarrow> x = y"
    by (auto simp: cmp_imp_equal)
end
  
abbreviation "eq_linorder \<equiv> eq_linorder_on UNIV"

lemma dflt_cmp_2inv[simp]: 
  "dflt_cmp (comp2le cmp) (comp2lt cmp) = cmp"
  unfolding dflt_cmp_def[abs_def] comp2le_def[abs_def] comp2lt_def[abs_def]
  apply (auto split: comp_res.splits intro!: ext)
  done

lemma (in linorder) dflt_cmp_inv2[simp]:
  shows 
  "(comp2le (dflt_cmp (\<le>) (<)))= (\<le>)"
  "(comp2lt (dflt_cmp (\<le>) (<)))= (<)"
proof -
  show "(comp2lt (dflt_cmp (\<le>) (<)))= (<)"
    unfolding dflt_cmp_def[abs_def] comp2le_def[abs_def] comp2lt_def[abs_def]
    apply (auto split: comp_res.splits intro!: ext)
    done

  show "(comp2le (dflt_cmp (\<le>) (<))) = (\<le>)"
    unfolding dflt_cmp_def[abs_def] comp2le_def[abs_def] comp2lt_def[abs_def]
    apply (auto split: comp_res.splits intro!: ext)
    done

qed
    
lemma eq_linorder_class_conv:
  "eq_linorder cmp \<longleftrightarrow> class.linorder (comp2le cmp) (comp2lt cmp)"
proof
  assume "eq_linorder cmp"
  then interpret eq_linorder_on UNIV cmp .
  have "linorder cmp" by unfold_locales
  show "class.linorder (comp2le cmp) (comp2lt cmp)"
    apply (rule linorder_to_class)
    apply fact
    by simp
next
  assume "class.linorder (comp2le cmp) (comp2lt cmp)"
  then interpret linorder "comp2le cmp" "comp2lt cmp" .
  
  from class_to_linorder interpret linorder_on UNIV cmp
    by simp
  show "eq_linorder cmp"
  proof
    fix x y
    assume "cmp x y = EQUAL"
    hence "comp2le cmp x y" "\<not>comp2lt cmp x y"
      by (auto simp: comp2le_def comp2lt_def)
    thus "x=y" by simp
  qed
qed
  
lemma (in linorder) class_to_eq_linorder:
  "eq_linorder (dflt_cmp (\<le>) (<))"
proof -
  interpret linorder_on UNIV "dflt_cmp (\<le>) (<)"
    by (rule class_to_linorder)

  show ?thesis
    apply unfold_locales
    apply (auto simp: dflt_cmp_def split: if_split_asm)
    done
qed

lemma eq_linorder_comp2eq_eq: 
  assumes "eq_linorder cmp"
  shows "comp2eq cmp = (=)"
proof -
  interpret eq_linorder_on UNIV cmp by fact
  show ?thesis
    apply (intro ext)
    unfolding comp2eq_def
    apply (auto split: comp_res.split dest: refl)
    done
qed
    
lemma restrict_eq_linorder: 
  assumes "eq_linorder_on D cmp" 
  assumes S: "D'\<subseteq>D" 
  shows "eq_linorder_on D' cmp"
proof -
  interpret eq_linorder_on D cmp by fact
  
  show ?thesis
    apply (rule eq_linorder_on.intro)
    apply (rule restrict_linorder[where D=D])
    apply unfold_locales []
    apply fact
    apply unfold_locales
    using S
    apply -
    apply (drule (1) rev_subsetD)+
    apply auto
    done
qed
  
lemma combine_eq_linorder[intro?]:
  assumes A: "eq_linorder_on D1 cmp1"
  assumes B: "eq_linorder_on D2 cmp2"
  assumes EQ: "D=D1\<union>D2"
  shows "eq_linorder_on D (cmp_combine D1 cmp1 D2 cmp2)"
proof -
  interpret A: eq_linorder_on D1 cmp1 by fact
  interpret B: eq_linorder_on D2 cmp2 by fact
  interpret linorder_on "(D1 \<union> D2)" "(cmp_combine D1 cmp1 D2 cmp2)"
    apply rule
    apply unfold_locales
    by simp
  
  show ?thesis
    apply (simp only: EQ)
    apply unfold_locales
    unfolding cmp_combine_def
    by (auto split: if_split_asm)
qed

lemma img_eq_linorder[intro?]:
  assumes A: "eq_linorder_on (f`D) cmp"
  assumes INJ: "inj_on f D"
  shows "eq_linorder_on D (cmp_img f cmp)"
proof -
  interpret eq_linorder_on "f`D" cmp by fact
  interpret L: linorder_on "(D)" "(cmp_img f cmp)"
    apply rule
    apply unfold_locales
    done
  
  show ?thesis
    apply unfold_locales
    unfolding cmp_img_def
    using INJ
    apply (auto dest: inj_onD)
    done
qed

lemma univ_eq_linorder[intro?]:
  shows "eq_linorder univ_cmp"
  apply (rule eq_linorder_on.intro)
  apply rule
  apply unfold_locales
  unfolding univ_cmp_def
  apply (auto split: if_split_asm)
  done
  
lemma extend_eq_linorder[intro?]:
  assumes "eq_linorder_on D cmp"
  shows "eq_linorder (cmp_extend D cmp)"
proof -
  interpret eq_linorder_on D cmp by fact
  show ?thesis
    unfolding cmp_extend_def
    apply (rule)
    apply fact
    apply rule
    by simp
qed
  
lemma lex_eq_linorder[intro?]:
  assumes "eq_linorder_on D cmp"
  shows "eq_linorder_on (lists D) (cmp_lex cmp)"
proof -
  interpret eq_linorder_on D cmp by fact
  show ?thesis
    apply (rule eq_linorder_on.intro)
    apply rule
    apply unfold_locales
    subgoal for l m
      apply (induct cmp\<equiv>cmp l m rule: cmp_lex.induct)
      apply (auto split: comp_res.splits)
      done
    done
qed

lemma prod_eq_linorder[intro?]:
  assumes "eq_linorder_on D1 cmp1"
  assumes "eq_linorder_on D2 cmp2"
  shows "eq_linorder_on (D1\<times>D2) (cmp_prod cmp1 cmp2)"
proof -
  interpret A: eq_linorder_on D1 cmp1 by fact
  interpret B: eq_linorder_on D2 cmp2 by fact
  show ?thesis
    apply (rule eq_linorder_on.intro)
    apply rule
    apply unfold_locales
    apply (auto split: comp_res.splits)
    done
qed

lemma set_ord_eq_linorder[intro?]: 
  "eq_linorder cmp \<Longrightarrow> eq_linorder (cmp_set cmp)"
  unfolding cmp_set_def
  apply rule
  apply rule
  apply (rule restrict_eq_linorder)
  apply rule
  apply assumption
  apply simp

  apply (rule linorder.sorted_list_of_set_inj)
  apply (subst (asm) eq_linorder_class_conv)
  .

lemma map_ord_eq_linorder[intro?]: 
  "\<lbrakk>eq_linorder cmpk; eq_linorder cmpv\<rbrakk> \<Longrightarrow> eq_linorder (cmp_map cmpk cmpv)"
  unfolding cmp_map_def
  apply rule
  apply rule
  apply (rule restrict_eq_linorder)
  apply rule
  apply rule
  apply assumption
  apply assumption
  apply simp

  apply (rule linorder.sorted_list_of_map_inj)
  apply (subst (asm) eq_linorder_class_conv)
  .

definition cmp_unit :: "unit \<Rightarrow> unit \<Rightarrow> comp_res" 
  where [simp]: "cmp_unit u v \<equiv> EQUAL"

lemma cmp_unit_eq_linorder:
  "eq_linorder cmp_unit"
  by unfold_locales simp_all
  
subsection \<open>Parametricity\<close>  
  
lemma param_cmp_extend[param]:
  assumes "(cmp,cmp')\<in>R \<rightarrow> R \<rightarrow> Id"
  assumes "Range R \<subseteq> D"
  shows "(cmp,cmp_extend D cmp') \<in> R \<rightarrow> R \<rightarrow> Id"
  unfolding cmp_extend_def cmp_combine_def[abs_def]
  using assms
  apply clarsimp
  by (blast dest!: fun_relD)

lemma param_cmp_img[param]: 
  "(cmp_img,cmp_img) \<in> (Ra\<rightarrow>Rb) \<rightarrow> (Rb\<rightarrow>Rb\<rightarrow>Rc) \<rightarrow> Ra \<rightarrow> Ra \<rightarrow> Rc"
  unfolding cmp_img_def[abs_def]
  by parametricity

lemma param_comp_res[param]:
  "(LESS,LESS)\<in>Id"
  "(EQUAL,EQUAL)\<in>Id"
  "(GREATER,GREATER)\<in>Id"
  "(case_comp_res,case_comp_res)\<in>Ra\<rightarrow>Ra\<rightarrow>Ra\<rightarrow>Id\<rightarrow>Ra"
  by (auto split: comp_res.split)

term cmp_lex
lemma param_cmp_lex[param]:
  "(cmp_lex,cmp_lex)\<in>(Ra\<rightarrow>Rb\<rightarrow>Id)\<rightarrow>\<langle>Ra\<rangle>list_rel\<rightarrow>\<langle>Rb\<rangle>list_rel\<rightarrow>Id"
  unfolding cmp_lex_alt[abs_def] cmp_lex'_def
  by (parametricity)

term cmp_prod
lemma param_cmp_prod[param]:
  "(cmp_prod,cmp_prod)\<in>
  (Ra\<rightarrow>Rb\<rightarrow>Id)\<rightarrow>(Rc\<rightarrow>Rd\<rightarrow>Id)\<rightarrow>\<langle>Ra,Rc\<rangle>prod_rel\<rightarrow>\<langle>Rb,Rd\<rangle>prod_rel\<rightarrow>Id"
  unfolding cmp_prod_alt
  by (parametricity)

lemma param_cmp_unit[param]: 
  "(cmp_unit,cmp_unit)\<in>Id\<rightarrow>Id\<rightarrow>Id" 
  by auto

lemma param_comp2eq[param]: "(comp2eq,comp2eq)\<in>(R\<rightarrow>R\<rightarrow>Id)\<rightarrow>R\<rightarrow>R\<rightarrow>Id"
  unfolding comp2eq_def[abs_def]
  by (parametricity)


  
lemma cmp_combine_paramD:
  assumes "(cmp,cmp_combine D1 cmp1 D2 cmp2)\<in>R\<rightarrow>R\<rightarrow>Id"
  assumes "Range R \<subseteq> D1"
  shows "(cmp,cmp1)\<in>R\<rightarrow>R\<rightarrow>Id"
  using assms
  unfolding cmp_combine_def[abs_def]
  apply (intro fun_relI)
  apply (drule_tac x=a in fun_relD, assumption)
  apply (drule_tac x=aa in fun_relD, assumption)
  apply (drule RangeI, drule (1) rev_subsetD)
  apply (drule RangeI, drule (1) rev_subsetD)
  apply simp
  done

lemma cmp_extend_paramD:
  assumes "(cmp,cmp_extend D cmp')\<in>R\<rightarrow>R\<rightarrow>Id"
  assumes "Range R \<subseteq> D"
  shows "(cmp,cmp')\<in>R\<rightarrow>R\<rightarrow>Id"
  using assms
  unfolding cmp_extend_def
  apply (rule cmp_combine_paramD)
  done
  

subsection \<open>Tuning of Generated Implementation\<close>
lemma [autoref_post_simps]: "comp2eq (dflt_cmp (\<le>) ((<)::_::linorder\<Rightarrow>_)) = (=)"
  by (simp add: class_to_eq_linorder eq_linorder_comp2eq_eq)



end

