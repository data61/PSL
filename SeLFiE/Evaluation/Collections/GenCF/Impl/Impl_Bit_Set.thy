section "Bitvector based Sets of Naturals"
theory Impl_Bit_Set
imports 
  "../../Iterator/Iterator" 
  "../Intf/Intf_Set" 
  Native_Word.Bits_Integer
begin
  text \<open>
    Based on the Native-Word library, using bit-operations on arbitrary
    precision integers. Fast for sets of small numbers, 
    direct and fast implementations of equal, union, inter, diff.

    Note: On Poly/ML 5.5.1, bit-operations on arbitrary precision integers are 
      rather inefficient. Use MLton instead, here they are efficiently implemented.
\<close>

  type_synonym bitset = integer

  definition bs_\<alpha> :: "bitset \<Rightarrow> nat set" where "bs_\<alpha> s \<equiv> { n . test_bit s n}"


context includes integer.lifting begin

  definition bs_empty :: "unit \<Rightarrow> bitset" where "bs_empty \<equiv> \<lambda>_. 0"


  lemma bs_empty_correct: "bs_\<alpha> (bs_empty ()) = {}"
    unfolding bs_\<alpha>_def bs_empty_def 
    apply transfer
    by auto

  definition bs_isEmpty :: "bitset \<Rightarrow> bool" where "bs_isEmpty s \<equiv> s=0"

  lemma bs_isEmpty_correct: "bs_isEmpty s \<longleftrightarrow> bs_\<alpha> s = {}"
    unfolding bs_isEmpty_def bs_\<alpha>_def 
    by transfer (auto simp: bin_eq_iff) 
    
  term set_bit
  definition bs_insert :: "nat \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_insert i s \<equiv> set_bit s i True"

  lemma bs_insert_correct: "bs_\<alpha> (bs_insert i s) = insert i (bs_\<alpha> s)"
    unfolding bs_\<alpha>_def bs_insert_def
    apply transfer
    apply auto
    apply (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)
    apply (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)
    by (metis bin_nth_sc_gen bin_set_conv_OR int_set_bit_True_conv_OR)

  definition bs_delete :: "nat \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_delete i s \<equiv> set_bit s i False"

  lemma bs_delete_correct: "bs_\<alpha> (bs_delete i s) = (bs_\<alpha> s) - {i}"
    unfolding bs_\<alpha>_def bs_delete_def
    apply transfer
    apply auto
    apply (metis bin_nth_ops(1) int_set_bit_False_conv_NAND)
    apply (metis (full_types) bin_nth_sc set_bit_int_def)
    by (metis (full_types) bin_nth_sc_gen set_bit_int_def)
  
  definition bs_mem :: "nat \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_mem i s \<equiv> test_bit s i"

  lemma bs_mem_correct: "bs_mem i s \<longleftrightarrow> i\<in>bs_\<alpha> s"
    unfolding bs_mem_def bs_\<alpha>_def by transfer auto


  definition bs_eq :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where 
    "bs_eq s1 s2 \<equiv> (s1=s2)"

  lemma bs_eq_correct: "bs_eq s1 s2 \<longleftrightarrow> bs_\<alpha> s1 = bs_\<alpha> s2"
    unfolding bs_eq_def bs_\<alpha>_def
    including integer.lifting
    apply transfer
    apply auto
    by (metis bin_eqI mem_Collect_eq test_bit_int_def)

  definition bs_subset_eq :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_subset_eq s1 s2 \<equiv> s1 AND NOT s2 = 0"
  
  lemma bs_subset_eq_correct: "bs_subset_eq s1 s2 \<longleftrightarrow> bs_\<alpha> s1 \<subseteq> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_subset_eq_def
    apply transfer
    apply rule
    apply auto []
    apply (metis bin_nth_code(1) bin_nth_ops(1) bin_nth_ops(4))
    apply (auto intro!: bin_eqI simp: bin_nth_ops)
    done

  definition bs_disjoint :: "bitset \<Rightarrow> bitset \<Rightarrow> bool" where
    "bs_disjoint s1 s2 \<equiv> s1 AND s2 = 0"
  
  lemma bs_disjoint_correct: "bs_disjoint s1 s2 \<longleftrightarrow> bs_\<alpha> s1 \<inter> bs_\<alpha> s2 = {}"
    unfolding bs_\<alpha>_def bs_disjoint_def
    apply transfer
    apply rule
    apply auto []
    apply (metis bin_nth_code(1) bin_nth_ops(1))
    apply (auto intro!: bin_eqI simp: bin_nth_ops)
    done

  definition bs_union :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_union s1 s2 = s1 OR s2"

  lemma bs_union_correct: "bs_\<alpha> (bs_union s1 s2) = bs_\<alpha> s1 \<union> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_union_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_inter :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_inter s1 s2 = s1 AND s2"

  lemma bs_inter_correct: "bs_\<alpha> (bs_inter s1 s2) = bs_\<alpha> s1 \<inter> bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_inter_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_diff :: "bitset \<Rightarrow> bitset \<Rightarrow> bitset" where
    "bs_diff s1 s2 = s1 AND NOT s2"

  lemma bs_diff_correct: "bs_\<alpha> (bs_diff s1 s2) = bs_\<alpha> s1 - bs_\<alpha> s2"
    unfolding bs_\<alpha>_def bs_diff_def
    by transfer (auto simp: bin_nth_ops)

  definition bs_UNIV :: "unit \<Rightarrow> bitset" where "bs_UNIV \<equiv> \<lambda>_. -1"

  lemma bs_UNIV_correct: "bs_\<alpha> (bs_UNIV ()) = UNIV"
    unfolding bs_\<alpha>_def bs_UNIV_def
    by transfer (auto)

  definition bs_complement :: "bitset \<Rightarrow> bitset" where
    "bs_complement s = NOT s"

  lemma bs_complement_correct: "bs_\<alpha> (bs_complement s) = - bs_\<alpha> s"
    unfolding bs_\<alpha>_def bs_complement_def
    by transfer (auto simp: bin_nth_ops)

end

  lemmas bs_correct[simp] = 
    bs_empty_correct
    bs_isEmpty_correct
    bs_insert_correct
    bs_delete_correct
    bs_mem_correct
    bs_eq_correct
    bs_subset_eq_correct
    bs_disjoint_correct
    bs_union_correct
    bs_inter_correct
    bs_diff_correct
    bs_UNIV_correct
    bs_complement_correct


subsection \<open>Autoref Setup\<close>

definition bs_set_rel_def_internal: 
  "bs_set_rel Rk \<equiv> 
    if Rk=nat_rel then br bs_\<alpha> (\<lambda>_. True) else {}"
lemma bs_set_rel_def: 
  "\<langle>nat_rel\<rangle>bs_set_rel \<equiv> br bs_\<alpha> (\<lambda>_. True)" 
  unfolding bs_set_rel_def_internal relAPP_def by simp

lemmas [autoref_rel_intf] = REL_INTFI[of "bs_set_rel" i_set]

lemma bs_set_rel_sv[relator_props]: "single_valued (\<langle>nat_rel\<rangle>bs_set_rel)"
  unfolding bs_set_rel_def by auto


term bs_empty

lemma [autoref_rules]: "(bs_empty (),{})\<in>\<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_UNIV (),UNIV)\<in>\<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_isEmpty,op_set_isEmpty)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

term insert
lemma [autoref_rules]: "(bs_insert,insert)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

term op_set_delete
lemma [autoref_rules]: "(bs_delete,op_set_delete)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_mem,(\<in>))\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_eq,(=))\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_subset_eq,(\<subseteq>))\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_union,(\<union>))\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_inter,(\<inter>))\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_diff,(-))\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_complement,uminus)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel"
  by (auto simp: bs_set_rel_def br_def)

lemma [autoref_rules]: "(bs_disjoint,op_set_disjoint)\<in>\<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> \<langle>nat_rel\<rangle>bs_set_rel \<rightarrow> bool_rel"
  by (auto simp: bs_set_rel_def br_def)


export_code 
    bs_empty
    bs_isEmpty
    bs_insert
    bs_delete
    bs_mem
    bs_eq
    bs_subset_eq
    bs_disjoint
    bs_union
    bs_inter
    bs_diff
    bs_UNIV
    bs_complement
 in SML

(*

    TODO: Iterator

  definition "maxbi s \<equiv> GREATEST i. s!!i"

  lemma cmp_BIT_append_conv[simp]: "i < i BIT b \<longleftrightarrow> ((i\<ge>0 \<and> b=1) \<or> i>0)"
    by (cases b) (auto simp: Bit_B0 Bit_B1)

  lemma BIT_append_cmp_conv[simp]: "i BIT b < i \<longleftrightarrow> ((i<0 \<and> (i=-1 \<longrightarrow> b=0)))"
    by (cases b) (auto simp: Bit_B0 Bit_B1)

  lemma BIT_append_eq[simp]: fixes i :: int shows "i BIT b = i \<longleftrightarrow> (i=0 \<and> b=0) \<or> (i=-1 \<and> b=1)"
    by (cases b) (auto simp: Bit_B0 Bit_B1)

  lemma int_no_bits_eq_zero[simp]:
    fixes s::int shows "(\<forall>i. \<not>s!!i) \<longleftrightarrow> s=0"
    apply clarsimp
    by (metis bin_eqI bin_nth_code(1))

  lemma int_obtain_bit:
    fixes s::int
    assumes "s\<noteq>0"
    obtains i where "s!!i"
    by (metis assms int_no_bits_eq_zero)
    
  lemma int_bit_bound:
    fixes s::int
    assumes "s\<ge>0" and "s!!i"
    shows "i \<le> Bits_Integer.log2 s"
  proof (rule ccontr)
    assume "\<not>i\<le>Bits_Integer.log2 s"
    hence "i>Bits_Integer.log2 s" by simp
    hence "i - 1 \<ge> Bits_Integer.log2 s" by simp
    hence "s AND bin_mask (i - 1) = s" by (simp add: int_and_mask `s\<ge>0`)
    hence "\<not> (s!!i)"  
      by clarsimp (metis Nat.diff_le_self bin_nth_mask bin_nth_ops(1) leD)
    thus False using `s!!i` ..
  qed

  lemma int_bit_bound':
    fixes s::int
    assumes "s\<ge>0" and "s!!i"
    shows "i < Bits_Integer.log2 s + 1"
    using assms int_bit_bound by smt

  lemma int_obtain_bit_pos:
    fixes s::int
    assumes "s>0"
    obtains i where "s!!i" "i < Bits_Integer.log2 s + 1"
    by (metis assms int_bit_bound' int_no_bits_eq_zero less_imp_le less_irrefl)

  lemma maxbi_set: fixes s::int shows "s>0 \<Longrightarrow> s!!maxbi s"
    unfolding maxbi_def
    apply (rule int_obtain_bit_pos, assumption)
    apply (rule GreatestI_nat, assumption)
    apply (intro allI impI)
    apply (rule int_bit_bound'[rotated], assumption)
    by auto

  lemma maxbi_max: fixes s::int shows "i>maxbi s \<Longrightarrow> \<not> s!!i"
    oops

  function get_maxbi :: "nat \<Rightarrow> int \<Rightarrow> nat" where
    "get_maxbi n s = (let
        b = 1<<n
      in
        if b\<le>s then get_maxbi (n+1) s
        else n
    )"
    by pat_completeness auto

  termination
    apply (rule "termination"[of "measure (\<lambda>(n,s). nat (s + 1 - (1<<n)))"])
    apply simp
    apply auto
    by (smt bin_mask_ge0 bin_mask_p1_conv_shift)


  partial_function (tailrec) 
    bs_iterate_aux :: "nat \<Rightarrow> bitset \<Rightarrow> ('\<sigma> \<Rightarrow> bool) \<Rightarrow> (nat \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
    where "bs_iterate_aux i s c f \<sigma> = (
    if s < 1 << i then \<sigma>
    else if \<not>c \<sigma> then \<sigma>
    else if test_bit s i then bs_iterate_aux (i+1) s c f (f i \<sigma>)
    else bs_iterate_aux (i+1) s c f \<sigma>
  )"

  definition bs_iteratei :: "bitset \<Rightarrow> (nat,'\<sigma>) set_iterator" where 
    "bs_iteratei s = bs_iterate_aux 0 s"


  definition bs_set_rel_def_internal: 
    "bs_set_rel Rk \<equiv> 
      if Rk=nat_rel then br bs_\<alpha> (\<lambda>_. True) else {}"
  lemma bs_set_rel_def: 
    "\<langle>nat_rel\<rangle>bs_set_rel \<equiv> br bs_\<alpha> (\<lambda>_. True)" 
    unfolding bs_set_rel_def_internal relAPP_def by simp


  definition "bs_to_list \<equiv> it_to_list bs_iteratei"

  lemma "(1::int)<<i = 2^i"
    by (simp add: shiftl_int_def)

  lemma 
    fixes s :: int
    assumes "s\<ge>0"  
    shows "s < 1<<i \<longleftrightarrow> Bits_Integer.log2 s \<le> i"
    using assms
  proof (induct i arbitrary: s)
    case 0 thus ?case by auto
  next
    case (Suc i)
    note GE=`0\<le>s`
    show ?case proof
      assume "s < 1 << Suc i"

      have "s \<le> (s >> 1) BIT 1"

      hence "(s >> 1) < (1<<i)" using GE apply auto
      with Suc.hyps[of "s div 2"]


    apply auto
    


  lemma "distinct (bs_to_list s)"
    unfolding bs_to_list_def it_to_list_def bs_iteratei_def[abs_def]
  proof -
    {
      fix l i
      assume "distinct l"
      show "distinct (bs_iterate_aux 0 s (\<lambda>_. True) (\<lambda>x l. l @ [x]) [])"

    }


    apply auto
    



    lemma "set (bs_to_list s) = bs_\<alpha> s"


  lemma autoref_iam_is_iterator[autoref_ga_rules]: 
    shows "is_set_to_list nat_rel bs_set_rel bs_to_list"
    unfolding is_set_to_list_def is_set_to_sorted_list_def
    apply clarsimp
    unfolding it_to_sorted_list_def
    apply (refine_rcg refine_vcg)
    apply (simp_all add: bs_set_rel_def br_def)

  proof (clarsimp)



  definition 

"iterate s c f \<sigma> \<equiv> let
    i=0;
    b=0;
    (_,_,s) = while 
  in

  end"


*)


end
