section \<open>Challenge 2.A\<close>
theory Challenge2A
imports "lib/VTcomp"
begin

text \<open>Problem definition:
\<^url>\<open>https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Verify%20This/Challenges%202019/cartesian_trees.pdf\<close>\<close>

text \<open>Polished and worked-over version.\<close>

subsection \<open>Specification\<close>

text \<open>We first fix the input, a list of integers\<close>
context fixes xs :: "int list" begin

text \<open>We then specify the desired output: 
  For each index \<open>j\<close>, return the greatest index \<open>i<j\<close> such that \<open>xs!i < xs!j\<close>, or \<open>None\<close> if
  no such index exists.
  
  Note that our indexes start at zero, and we use an option datatype to model that 
  no left-smaller value may exists.
\<close>  
definition
  "left_spec j = (if (\<exists>i<j. xs ! i < xs ! j) then Some (GREATEST i. i < j \<and> xs ! i < xs ! j) else None)"

text \<open>The output of the algorithm should be an array \<open>lf\<close>, containing the indexes of the 
  left-smaller values:
\<close>
definition "all_left_spec lf \<equiv> length lf = length xs \<and> (\<forall>i<length xs. lf!i = left_spec i)"
      
subsection \<open>Auxiliary Theory\<close>
text \<open>We derive some theory specific to this algorithm\<close>

subsubsection \<open>Has-Left and The-Left\<close>
text \<open>We split the specification of nearest left value into a predicate and a total function\<close>
definition "has_left j = (\<exists>i<j. xs ! i < xs ! j)"
definition "the_left j = (GREATEST i. i < j \<and> xs ! i < xs ! j)"

lemma left_alt: "left_spec j = (if has_left j then Some (the_left j) else None)"
  by (auto simp: left_spec_def has_left_def the_left_def)

lemma the_leftI: "has_left j \<Longrightarrow> the_left j < j \<and> xs!the_left j < xs!j"
  apply (clarsimp simp: has_left_def the_left_def)
  by (metis (no_types, lifting) GreatestI_nat less_le_not_le nat_le_linear pinf(5))

lemma the_left_decr[simp]: "has_left i \<Longrightarrow> the_left i < i"  
  by (simp add: the_leftI)

lemma le_the_leftI:
  assumes "i\<le>j" "xs!i < xs!j"
  shows "i \<le> the_left j"
  using assms unfolding the_left_def
  by (metis (no_types, lifting)
      Greatest_le_nat le_less_linear less_imp_not_less less_irrefl
      order.not_eq_order_implies_strict)

lemma the_left_leI:  
  assumes "\<forall>k. j<k \<and> k<i \<longrightarrow> \<not>xs!k<xs!i"
  assumes "has_left i"
  shows "the_left i \<le> j"
  using assms
  unfolding the_left_def has_left_def
  apply auto
  by (metis (full_types) the_leftI assms(2) not_le the_left_def)

subsubsection \<open>Derived Stack\<close>    
text \<open>We note that the stack in the algorithm doesn't contain any 
  extra information. It can be derived from the left neighbours that have been 
  computed so far:
  The first element of the stack is the current index - 1, and each next element is
  the nearest left smaller value of the previous element:
\<close>

fun der_stack where
  "der_stack i = (if has_left i then the_left i # der_stack (the_left i) else [])"  
declare der_stack.simps[simp del]  

text \<open>
  Although the refinement framework would allow us to phrase the 
  algorithm without a stack first, and then introduce the stack in a subsequent 
  refinement step (or omit it altogether), for simplicity of presentation, we decided
  to model the algorithm with a stack in first place. However, the invariant will account for
  the stack being derived.
\<close>

lemma set_der_stack_lt: "k \<in> set (der_stack i\<^sub>0) \<Longrightarrow> k<i\<^sub>0"  
  apply (induction i\<^sub>0 rule: der_stack.induct)
  apply (subst (asm) der_stack.simps)
  apply auto
  using less_trans the_leftI by blast
  


subsection \<open>Abstract Implementation\<close>
text \<open>We first implement the algorithm on lists. 
  The assertions that we annotated into the algorithm ensure
  that all list index accesses are in bounds.
\<close>
definition "pop stk v \<equiv> dropWhile (\<lambda>j. xs!j\<ge>v) stk"

lemma pop_Nil[simp]: "pop [] v = []" by (auto simp: pop_def)
lemma pop_cons: "pop (j#js) v = (if xs!j \<ge> v then pop js v else j#js)"
  by (simp add: pop_def)


definition "all_left \<equiv> doN {
  (_,lf) \<leftarrow> nfoldli [0..<length xs] (\<lambda>_. True) (\<lambda>i (stk,lf). doN {
    ASSERT (set stk \<subseteq> {0..<length xs} );
    let stk = pop stk (xs!i);
    ASSERT (stk = der_stack i);
    ASSERT (i<length lf);
    if (stk = []) then doN {
      let lf = lf[i:=None];
      RETURN (i#stk,lf)
    } else doN {
      let lf = lf[i:= Some (hd stk)];
      RETURN (i#stk,lf)
    }
  }) ([],replicate (length xs) None);
  RETURN lf
}"


subsection \<open>Correctness Proof\<close>

subsubsection \<open>Popping From the Stack\<close>

text \<open>We show that the abstract algorithm implements its specification.
  The main idea here is the popping of the stack.
  Top obtain a left smaller value, it is enough to follow the left-values of
  the left-neighbour, until we have found the value or there are no more left-values.
  
  The following theorem formalizes this idea:
\<close>
theorem find_left_rl:
  assumes "i\<^sub>0 < length xs"
  assumes "i<i\<^sub>0"
  assumes "left_spec i\<^sub>0 \<le> Some i"
  shows "if xs!i < xs!i\<^sub>0 then left_spec i\<^sub>0 = Some i
         else left_spec i\<^sub>0 \<le> left_spec i"
  using assms           
  apply (simp; intro impI conjI; clarsimp)
  subgoal
    apply (auto simp: left_alt split: if_splits)
    apply (simp add: le_antisym le_the_leftI)
    apply (auto simp: has_left_def)
    done
  subgoal
    apply (auto simp: left_alt split: if_splits)
    subgoal
      apply (drule the_leftI)
      using nat_less_le by (auto simp: has_left_def)
    subgoal  
      using le_the_leftI the_leftI by fastforce
    done  
  done  

text \<open>Using this lemma, we can show that the stack popping procedure preserves the form of the stack.\<close>
lemma pop_aux: "\<lbrakk> k<i\<^sub>0; i\<^sub>0<length xs; left_spec i\<^sub>0 \<le> Some k \<rbrakk> \<Longrightarrow> pop (k # der_stack k) (xs!i\<^sub>0) = der_stack i\<^sub>0"
  apply (induction k rule: nat_less_induct)
  apply (clarsimp)
  by (smt der_stack.simps left_alt pop_def the_leftI dropWhile.simps(1) find_left_rl leD less_option_None_Some option.inject pop_cons)
  
  
subsubsection \<open>Main Algorithm\<close>  

text \<open>Ad-Hoc lemmas\<close>
lemma swap_adhoc[simp]: 
  "None = left i \<longleftrightarrow> left i = None"
  "Some j = left i \<longleftrightarrow> left i = Some j" by auto

lemma left_spec_None_iff[simp]: "left_spec i = None \<longleftrightarrow> \<not>has_left i" by (auto simp: left_alt)
lemma [simp]: "left_spec 0 = None" by (auto simp: left_spec_def)
lemma [simp]: "has_left 0 = False"
  by (simp add: has_left_def)
lemma [simp]: "der_stack 0 = []"
  by (subst der_stack.simps) auto
  
  
lemma algo_correct: "all_left \<le> SPEC all_left_spec"
  unfolding all_left_def all_left_spec_def
  apply (refine_vcg nfoldli_upt_rule[where I="
    \<lambda>k (stk,lf). 
      (length lf = length xs)
    \<and> (\<forall>i<k. lf!i = left_spec i)
    \<and> (case k of Suc kk \<Rightarrow> stk = kk#der_stack kk | _ \<Rightarrow>  stk=[])  
      "])
  apply (vc_solve split: nat.splits)
  subgoal using set_der_stack_lt by fastforce
  subgoal for lf k
    by (metis left_alt less_Suc_eq_le less_eq_option_None less_eq_option_Some nat_in_between_eq(2) pop_aux the_leftI)
  subgoal
    by (metis der_stack.simps left_alt less_Suc_eq list.distinct(1) nth_list_update)
  subgoal
    by (metis der_stack.simps left_alt less_Suc_eq list.sel(1) nth_list_update)
  done

subsection \<open>Implementation With Arrays\<close>    
text \<open>We refine the algorithm to use actual arrays for the input and output. 
  The stack remains a list, as pushing and popping from a (functional) list is efficient.
\<close>

subsubsection \<open>Implementation of Pop\<close>   
text \<open>In a first step, we refine the pop function to an explicit loop.\<close>

definition "pop2 stk v \<equiv> 
  monadic_WHILEIT 
    (\<lambda>_. set stk \<subseteq> {0..<length xs}) 
    (\<lambda>[] \<Rightarrow> RETURN False | k#stk \<Rightarrow> doN { ASSERT (k<length xs); RETURN (v \<le> xs!k) })
    (\<lambda>stk. mop_list_tl stk)
    stk"
  
lemma pop2_refine_aux: "set stk \<subseteq> {0..<length xs} \<Longrightarrow> pop2 stk v \<le> RETURN (pop stk v)"
  apply (induction stk)
  unfolding pop_def pop2_def
  subgoal
    apply (subst monadic_WHILEIT_unfold)
    by auto
  subgoal
    apply (subst monadic_WHILEIT_unfold)
    unfolding mop_list_tl_def op_list_tl_def by auto
  done
        
end \<comment> \<open>Context fixing the input \<open>xs\<close>.\<close>


text \<open>The refinement lemma written in higher-order form.\<close>
lemma pop2_refine: "(uncurry2 pop2, uncurry2 (RETURN ooo pop)) \<in> [\<lambda>((xs,stk),v). set stk \<subseteq> {0..<length xs}]\<^sub>f (Id \<times>\<^sub>r Id) \<times>\<^sub>r Id \<rightarrow> \<langle>Id\<rangle>nres_rel"
  using pop2_refine_aux
  by (auto intro!: frefI nres_relI)

text \<open>Next, we use the Sepref tool to synthesize an implementation on arrays.\<close>
sepref_definition pop2_impl is "uncurry2 pop2" :: "(array_assn id_assn)\<^sup>k *\<^sub>a (list_assn id_assn)\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a list_assn id_assn"
  unfolding pop2_def
  by sepref
lemmas [sepref_fr_rules] = pop2_impl.refine[FCOMP pop2_refine]  

subsubsection \<open>Implementation of Main Algorithm\<close>  

sepref_definition all_left_impl is all_left :: "(array_assn id_assn)\<^sup>k \<rightarrow>\<^sub>a array_assn (option_assn id_assn)"
  unfolding all_left_def
  apply (rewrite at "nfoldli _ _ _ (\<hole>,_)" HOL_list.fold_custom_empty)
  apply (rewrite in "nfoldli _ _ _ (_,\<hole>)" array_fold_custom_replicate)
  by sepref

subsubsection \<open>Correctness Theorem for Concrete Algorithm\<close>
text \<open>We compose the correctness theorem and the refinement theorem, to get a correctness
  theorem for the final implementation.\<close>
  
text \<open>Abstract correctness theorem in higher-order form.\<close>
lemma algo_correct': "(all_left, SPEC o all_left_spec) 
  \<in> \<langle>Id\<rangle>list_rel \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>option_rel\<rangle>list_rel\<rangle>nres_rel"
  using algo_correct by (auto simp: nres_relI)  

text \<open>Main correctness theorem in higher-order form.\<close>   
theorem algo_impl_correct:
    "(all_left_impl, SPEC o all_left_spec)
    \<in> (array_assn int_assn, array_assn int_assn) \<rightarrow>\<^sub>a array_assn (option_assn nat_assn)"      
  using all_left_impl.refine[FCOMP algo_correct', simplified] .
    
text \<open>Main correctness theorem as Hoare-Triple\<close>  
theorem algo_impl_correct': "
  <array_assn int_assn xs xsi> 
    all_left_impl xsi 
  <\<lambda>lfi. \<exists>\<^sub>Alf. array_assn int_assn xs xsi 
        * array_assn (option_assn id_assn) lf lfi 
        * \<up>(all_left_spec xs lf)>\<^sub>t" 
  apply (rule cons_rule[OF _ _ algo_impl_correct[to_hnr, THEN hn_refineD, unfolded autoref_tag_defs]])
  apply (simp add: hn_ctxt_def, rule ent_refl) 
  by (auto simp: hn_ctxt_def)


subsection \<open>Code Generation\<close>
    
export_code all_left_impl checking SML Scala Haskell? OCaml?


text \<open>The example from the problem description, in ML using the verified algorithm\<close>
ML_val \<open>
  (* Convert from option to 1-based indexes *)
  fun cnv NONE = 0
    | cnv (SOME i) = @{code integer_of_nat} i + 1

  (* The verified algorithm, boxing the input list into an array, 
    and unboxing the output to a list, and converting it from option to 1-based *)
  fun all_left xs = 
       @{code all_left_impl} (Array.fromList (map @{code int_of_integer} xs)) ()
    |> Array.foldr (op ::) []
    |> map cnv

  val test = all_left [ 4, 7, 8, 1, 2, 3, 9, 5, 6 ]  
\<close>
 
end