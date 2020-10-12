theory Impl_Uv_Set
imports 
  "../../Iterator/Iterator" 
  "../Intf/Intf_Set" 
  Native_Word.Uint
begin

  subsection \<open>Bit-Vectors as Lists of Words\<close>

  subsubsection \<open>Lookup\<close>

  primrec lookup :: "nat \<Rightarrow> ('a::len) word list \<Rightarrow> bool" where
    "lookup _ [] \<longleftrightarrow> False"
  | "lookup n (w#ws) 
      \<longleftrightarrow> (if n<LENGTH('a) then test_bit w n else lookup (n-LENGTH('a)) ws)"

  lemma lookup_append[simp]: "lookup n (w1@w2 :: 'a::len word list) 
    \<longleftrightarrow> (
      if n < LENGTH('a) * length w1 then 
        lookup n w1 
      else lookup (n - LENGTH('a) * length w1) w2)"
    by (induction w1 arbitrary: n) auto

  lemma lookup_zeroes[simp]: "lookup i (replicate n (0::'a::len word)) = False"
    by (induction n arbitrary: i) auto

  lemma lookup_out_of_bound: 
    fixes uv :: "'a::len word list"
    assumes "\<not> i < LENGTH('a::len) * length uv" 
    shows "\<not> lookup i uv"
    using assms
    by (induction uv arbitrary: i) auto


  subsubsection \<open>Empty\<close>

  definition empty :: "'a::len word list" where "empty = []"

  subsubsection \<open>Set and Reset Bit\<close>

  function single_bit :: "nat \<Rightarrow> ('a::len) word list" 
    where "single_bit n = (
      if (n<LENGTH('a)) then 
        [set_bit 0 n True] 
      else 0#single_bit (n-LENGTH('a)))"
    by pat_completeness auto
  termination
    apply (relation "measure id")
    apply simp
    apply (simp add: not_less less_diff_conv2)
    done

  declare single_bit.simps[simp del]

  lemma lookup_single_bit[simp]: "lookup i ((single_bit n)::'a::len word list) \<longleftrightarrow> i = n"
    apply (induction n arbitrary: i rule: single_bit.induct)
    apply (subst single_bit.simps)
    apply (auto simp: bin_nth_sc_gen)
    done

find_consts name: set_bit

  primrec set_bit :: "nat \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list" where
    "set_bit i [] = single_bit i"
  | "set_bit i (w#ws) = (
      if i<LENGTH('a) then 
        Bits.set_bit w i True # ws
      else 
        w # set_bit (i - LENGTH('a)) ws)"
  
  lemma set_bit_lookup[simp]: "lookup i (set_bit j ws) \<longleftrightarrow> (lookup i ws \<or> i=j)"
    apply (induction ws arbitrary: i j)
    apply (auto simp: test_bit_set_gen word_size)
    done


  primrec reset_bit :: "nat \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list" where
    "reset_bit i [] = []"
  | "reset_bit i (w#ws) = (
      if i<LENGTH('a) then 
        Bits.set_bit w i False # ws
      else 
        w # reset_bit (i - LENGTH('a)) ws)"
  
  lemma reset_bit_lookup[simp]: "lookup i (reset_bit j ws) \<longleftrightarrow> (lookup i ws \<and> i\<noteq>j)"
    apply (induction ws arbitrary: i j)
    apply (auto simp: test_bit_set_gen word_size)
    done

  subsubsection \<open>Binary Operations\<close>

  definition 
    is_bin_op_impl 
    :: "(bool\<Rightarrow>bool\<Rightarrow>bool) \<Rightarrow> ('a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word) \<Rightarrow> bool"
    where "is_bin_op_impl f g \<equiv> 
    (\<forall>w v.  \<forall>i<LENGTH('a). test_bit (g w v) i \<longleftrightarrow> f (test_bit w i) (test_bit v i))"

  definition "is_strict_bin_op_impl f g \<equiv> is_bin_op_impl f g \<and> f False False = False"

  fun binary :: "('a::len word \<Rightarrow> 'a::len word \<Rightarrow> 'a::len word) 
    \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "binary f [] [] = []"
  | "binary f [] (w#ws) = f 0 w # binary f [] ws"
  | "binary f (v#vs) [] = f v 0 # binary f vs []"
  | "binary f (v#vs) (w#ws) = f v w # binary f vs ws"

  lemma binary_lookup:
    assumes "is_strict_bin_op_impl f g"
    shows "lookup i (binary g ws vs) \<longleftrightarrow> f (lookup i ws) (lookup i vs)"
    using assms
    apply (induction g ws vs arbitrary: i rule: binary.induct)
    apply (auto simp: is_strict_bin_op_impl_def is_bin_op_impl_def)
    done

  subsection \<open>Abstraction to Sets of Naturals\<close>

  definition "\<alpha> uv \<equiv> {n. lookup n uv}"
  
  lemma memb_correct: "lookup i ws \<longleftrightarrow> i\<in>\<alpha> ws"
    by (auto simp: \<alpha>_def)

  lemma empty_correct: "\<alpha> empty = {}"
    by (simp add: \<alpha>_def empty_def)

  lemma single_bit_correct: "\<alpha> (single_bit n) = {n}"
    by (simp add: \<alpha>_def)

  lemma insert_correct: "\<alpha> (set_bit i ws) = Set.insert i (\<alpha> ws)"
    by (auto simp add: \<alpha>_def)

  lemma delete_correct: "\<alpha> (reset_bit i ws) = (\<alpha> ws) - {i}"
    by (auto simp add: \<alpha>_def)

  lemma binary_correct:
    assumes "is_strict_bin_op_impl f g"
    shows "\<alpha> (binary g ws vs) = { i . f (i\<in>\<alpha> ws) (i\<in>\<alpha> vs) }"
    unfolding \<alpha>_def
    by (auto simp add: binary_lookup[OF assms])

  fun union :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "union [] ws = ws"
  | "union vs [] = vs"
  | "union (v#vs) (w#ws) = (v OR w) # union vs ws"

  lemma union_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (union vs ws) \<longleftrightarrow> lookup i vs \<or> lookup i ws"
    apply (induction vs ws arbitrary: i rule: union.induct)
    apply (auto simp: word_ao_nth)
    done

  lemma union_correct: "\<alpha> (union ws vs) = \<alpha> ws \<union> \<alpha> vs"
    by (auto simp add: \<alpha>_def)

  fun inter :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "inter [] ws = []"
  | "inter vs [] = []"
  | "inter (v#vs) (w#ws) = (v AND w) # inter vs ws"

  lemma inter_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (inter vs ws) \<longleftrightarrow> lookup i vs \<and> lookup i ws"
    apply (induction vs ws arbitrary: i rule: inter.induct)
    apply (auto simp: word_ao_nth)
    done

  lemma inter_correct: "\<alpha> (inter ws vs) = \<alpha> ws \<inter> \<alpha> vs"
    by (auto simp add: \<alpha>_def)


  fun diff :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> 'a::len word list"
    where 
    "diff [] ws = []"
  | "diff vs [] = vs"
  | "diff (v#vs) (w#ws) = (v AND NOT w) # diff vs ws"

  lemma diff_lookup[simp]:
    fixes vs :: "'a::len word list" 
    shows "lookup i (diff vs ws) \<longleftrightarrow> lookup i vs - lookup i ws"
    apply (induction vs ws arbitrary: i rule: diff.induct)
    apply (auto simp: word_ops_nth_size word_size)
    done

  lemma diff_correct: "\<alpha> (diff ws vs) = \<alpha> ws - \<alpha> vs"
    by (auto simp add: \<alpha>_def)
   
  fun zeroes :: "'a::len word list \<Rightarrow> bool" where
    "zeroes [] \<longleftrightarrow> True"
  | "zeroes (w#ws) \<longleftrightarrow> w=0 \<and> zeroes ws"

  lemma zeroes_lookup: "zeroes ws \<longleftrightarrow> (\<forall>i. \<not>lookup i ws)"
    apply (induction ws)
    apply (auto simp: word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma isEmpty_correct: "zeroes ws \<longleftrightarrow> \<alpha> ws = {}"
    by (auto simp: zeroes_lookup \<alpha>_def)

  fun equal :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "equal [] [] \<longleftrightarrow> True"
  | "equal [] ws \<longleftrightarrow> zeroes ws"
  | "equal vs [] \<longleftrightarrow> zeroes vs"
  | "equal (v#vs) (w#ws) \<longleftrightarrow> v=w \<and> equal vs ws"

  lemma equal_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "equal vs ws \<longleftrightarrow> (\<forall>i. lookup i vs = lookup i ws)"
  proof (induction vs ws rule: equal.induct)
    fix v w and vs ws :: "'a::len word list"
    assume IH: "equal vs ws = (\<forall>i. lookup i vs = lookup i ws)"
    show "equal (v # vs) (w # ws) = (\<forall>i. lookup i (v # vs) = lookup i (w # ws))"
    proof (rule iffI, rule allI)
      fix i
      assume "equal (v#vs) (w#ws)"
      thus "lookup i (v # vs) = lookup i (w # ws)"
        by (auto simp: IH)
    next
      assume "\<forall>i. lookup i (v # vs) = lookup i (w # ws)"
      thus "equal (v # vs) (w # ws)"
        apply (auto simp: word_eq_iff IH)
        apply metis
        apply metis
        apply (drule_tac x="i + LENGTH('a)" in spec)
        apply auto []
        apply (drule_tac x="i + LENGTH('a)" in spec)
        apply auto []
        done
    qed
  qed (auto simp: zeroes_lookup)
    
  lemma equal_correct: "equal vs ws \<longleftrightarrow> \<alpha> vs = \<alpha> ws"
    by (auto simp: \<alpha>_def equal_lookup)
  
  fun subseteq :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "subseteq [] ws \<longleftrightarrow> True"
  | "subseteq vs [] \<longleftrightarrow> zeroes vs"
  | "subseteq (v#vs) (w#ws) \<longleftrightarrow> (v AND NOT w = 0) \<and> subseteq vs ws"

  
  lemma subseteq_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "subseteq vs ws \<longleftrightarrow> (\<forall>i. lookup i vs \<longrightarrow> lookup i ws)"
    apply (induction vs ws rule: subseteq.induct)
    apply simp
    apply (auto simp: zeroes_lookup) []
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma subseteq_correct: "subseteq vs ws \<longleftrightarrow> \<alpha> vs \<subseteq> \<alpha> ws"
    by (auto simp: \<alpha>_def subseteq_lookup)


  fun subset :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "subset [] ws \<longleftrightarrow> \<not>zeroes ws"
  | "subset vs [] \<longleftrightarrow> False"
  | "subset (v#vs) (w#ws) \<longleftrightarrow> (if v=w then subset vs ws else subseteq (v#vs) (w#ws))"

  lemma subset_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "subset vs ws \<longleftrightarrow> ((\<forall>i. lookup i vs \<longrightarrow> lookup i ws) 
      \<and> (\<exists>i. \<not>lookup i vs \<and> lookup i ws))"
    apply (induction vs ws rule: subset.induct)
    apply (simp add: zeroes_lookup)
    apply (simp add: zeroes_lookup) []
    apply (simp del: subseteq_correct add: subseteq_lookup)
    apply safe
    apply simp_all
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    done

  lemma subset_correct: "subset vs ws \<longleftrightarrow> \<alpha> vs \<subset> \<alpha> ws"
    by (auto simp: \<alpha>_def subset_lookup)

  
  fun disjoint :: "'a::len word list \<Rightarrow> 'a::len word list \<Rightarrow> bool" where
    "disjoint [] ws \<longleftrightarrow> True"
  | "disjoint vs [] \<longleftrightarrow> True"
  | "disjoint (v#vs) (w#ws) \<longleftrightarrow> (v AND w = 0) \<and> disjoint vs ws"

  lemma disjoint_lookup: 
    fixes vs ws :: "'a::len word list"
    shows "disjoint vs ws \<longleftrightarrow> (\<forall>i. \<not>(lookup i vs \<and> lookup i ws))"
    apply (induction vs ws rule: disjoint.induct)
    apply simp
    apply simp
    apply (auto simp: word_ops_nth_size word_size word_eq_iff)
    by (metis diff_add_inverse2 not_add_less2)

  lemma disjoint_correct: "disjoint vs ws \<longleftrightarrow> \<alpha> vs \<inter> \<alpha> ws = {}"
    by (auto simp: \<alpha>_def disjoint_lookup)

  
subsection \<open>Lifting to Uint\<close>
  type_synonym uint_vector = "uint list"

  lift_definition uv_\<alpha> :: "uint_vector \<Rightarrow> nat set" is \<alpha> .
  lift_definition uv_lookup :: "nat \<Rightarrow> uint_vector \<Rightarrow> bool" is lookup .
  lift_definition uv_empty :: "uint_vector" is empty .
  lift_definition uv_single_bit :: "nat \<Rightarrow> uint_vector" is single_bit .
  lift_definition uv_set_bit :: "nat \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is set_bit .
  lift_definition uv_reset_bit :: "nat \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is reset_bit .
  lift_definition uv_union :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is union .
  lift_definition uv_inter :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is inter .
  lift_definition uv_diff :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> uint_vector" is diff .
  lift_definition uv_zeroes :: "uint_vector \<Rightarrow> bool" is zeroes .
  lift_definition uv_equal :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is equal .
  lift_definition uv_subseteq :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is subseteq .
  lift_definition uv_subset :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is subset .
  lift_definition uv_disjoint :: "uint_vector \<Rightarrow> uint_vector \<Rightarrow> bool" is disjoint .

  lemmas uv_memb_correct = memb_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_empty_correct = empty_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_single_bit_correct = single_bit_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_insert_correct = insert_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_delete_correct = delete_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_union_correct = union_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_inter_correct = inter_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_diff_correct = diff_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_isEmpty_correct = isEmpty_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_equal_correct = equal_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_subseteq_correct = subseteq_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_subset_correct = subset_correct[where 'a=dflt_size, Transfer.transferred]
  lemmas uv_disjoint_correct = disjoint_correct[where 'a=dflt_size, Transfer.transferred]



  lemmas [where 'a=dflt_size, Transfer.transferred, code] = 
    lookup.simps 
    empty_def
    single_bit.simps 
    set_bit.simps 
    reset_bit.simps 
    union.simps 
    inter.simps 
    diff.simps 
    zeroes.simps 
    equal.simps 
    subseteq.simps 
    subset.simps 
    disjoint.simps 
    

  hide_const (open) \<alpha> lookup empty single_bit set_bit reset_bit union inter diff zeroes 
    equal subseteq subset disjoint


subsection \<open>Autoref Setup\<close>

  definition uv_set_rel_def_internal: 
    "uv_set_rel Rk \<equiv> 
      if Rk=nat_rel then br uv_\<alpha> (\<lambda>_. True) else {}"
  lemma uv_set_rel_def: 
    "\<langle>nat_rel\<rangle>uv_set_rel \<equiv> br uv_\<alpha> (\<lambda>_. True)" 
    unfolding uv_set_rel_def_internal relAPP_def by simp

  lemmas [autoref_rel_intf] = REL_INTFI[of "uv_set_rel" i_set]

  lemma uv_set_rel_sv[relator_props]: "single_valued (\<langle>nat_rel\<rangle>uv_set_rel)"
    unfolding uv_set_rel_def by auto

  lemma uv_autoref[autoref_rules,param]:
    "(uv_lookup,(\<in>)) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_empty,{}) \<in> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_set_bit,insert) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_reset_bit,op_set_delete) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_union,(\<union>)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_inter,(\<inter>)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_diff,(-)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel"
    "(uv_zeroes,op_set_isEmpty) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_equal,(=)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_subseteq,(\<subseteq>)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_subset,(\<subset>)) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    "(uv_disjoint,op_set_disjoint) \<in> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> \<langle>nat_rel\<rangle>uv_set_rel \<rightarrow> bool_rel"
    by (auto 
      simp: uv_set_rel_def br_def
      simp: uv_memb_correct uv_empty_correct uv_insert_correct uv_delete_correct
      simp: uv_union_correct uv_inter_correct uv_diff_correct uv_isEmpty_correct
      simp: uv_equal_correct uv_subseteq_correct uv_subset_correct uv_disjoint_correct)


  export_code 
    uv_lookup 
    uv_empty
    uv_single_bit 
    uv_set_bit 
    uv_reset_bit 
    uv_union 
    uv_inter 
    uv_diff 
    uv_zeroes 
    uv_equal 
    uv_subseteq 
    uv_subset 
    uv_disjoint 
  checking SML Scala Haskell? OCaml?

end
