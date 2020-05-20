section \<open>Union-Find Data-Structure\<close>
theory Union_Find
imports 
  "../Sep_Main" 
  Collections.Partial_Equivalence_Relation
  "HOL-Library.Code_Target_Numeral"
begin
text \<open>
  We implement a simple union-find data-structure based on an array.
  It uses path compression and a size-based union heuristics.
\<close>

subsection \<open>Abstract Union-Find on Lists\<close>
text \<open>
  We first formulate union-find structures on lists, and later implement 
  them using Imperative/HOL. This is a separation of proof concerns
  between proving the algorithmic idea correct and generating the verification
  conditions.
\<close>

subsubsection \<open>Representatives\<close>
text \<open>
  We define a function that searches for the representative of an element.
  This function is only partially defined, as it does not terminate on all
  lists. We use the domain of this function to characterize valid union-find 
  lists. 
\<close>
function (domintros) rep_of 
  where "rep_of l i = (if l!i = i then i else rep_of l (l!i))"
  by pat_completeness auto

text \<open>A valid union-find structure only contains valid indexes, and
  the \<open>rep_of\<close> function terminates for all indexes.\<close>
definition 
  "ufa_invar l \<equiv> \<forall>i<length l. rep_of_dom (l,i) \<and> l!i<length l"

lemma ufa_invarD: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of_dom (l,i)" 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> l!i<length l" 
  unfolding ufa_invar_def by auto

text \<open>We derive the following equations for the \<open>rep-of\<close> function.\<close>
lemma rep_of_refl: "l!i=i \<Longrightarrow> rep_of l i = i"
  apply (subst rep_of.psimps)
  apply (rule rep_of.domintros)
  apply (auto)
  done

lemma rep_of_step: 
  "\<lbrakk>ufa_invar l; i<length l; l!i\<noteq>i\<rbrakk> \<Longrightarrow> rep_of l i = rep_of l (l!i)"
  apply (subst rep_of.psimps)
  apply (auto dest: ufa_invarD)
  done

lemmas rep_of_simps = rep_of_refl rep_of_step

lemma rep_of_iff: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> 
  \<Longrightarrow> rep_of l i = (if l!i=i then i else rep_of l (l!i))"
  by (simp add: rep_of_simps)

text \<open>We derive a custom induction rule, that is more suited to
  our purposes.\<close>
lemma rep_of_induct[case_names base step, consumes 2]:
  assumes I: "ufa_invar l" 
  assumes L: "i<length l"
  assumes BASE: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i=i \<rbrakk> \<Longrightarrow> P l i"
  assumes STEP: "\<And>i. \<lbrakk> ufa_invar l; i<length l; l!i\<noteq>i; P l (l!i) \<rbrakk> 
    \<Longrightarrow> P l i"
  shows "P l i"
proof -
  from ufa_invarD[OF I L] have "ufa_invar l \<and> i<length l \<longrightarrow> P l i"
    apply (induct l\<equiv>l i rule: rep_of.pinduct)
    apply (auto intro: STEP BASE dest: ufa_invarD)
    done
  thus ?thesis using I L by simp
qed

text \<open>In the following, we define various properties of \<open>rep_of\<close>.\<close>
lemma rep_of_min: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
proof -
  have "\<lbrakk>rep_of_dom (l,i) \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    apply (induct arbitrary:  rule: rep_of.pinduct)
    apply (subst rep_of.psimps, assumption)
    apply (subst (2) rep_of.psimps, assumption)
    apply auto
    done 
  thus "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> l!(rep_of l i) = rep_of l i"
    by (metis ufa_invarD(1))
qed

lemma rep_of_bound: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l i < length l"
  apply (induct rule: rep_of_induct)
  apply (auto simp: rep_of_iff)
  done

lemma rep_of_idem: 
  "\<lbrakk> ufa_invar l; i<length l \<rbrakk> \<Longrightarrow> rep_of l (rep_of l i) = rep_of l i"
  by (auto simp: rep_of_min rep_of_refl)

lemma rep_of_min_upd: "\<lbrakk> ufa_invar l; x<length l; i<length l \<rbrakk> \<Longrightarrow> 
  rep_of (l[rep_of l x := rep_of l x]) i = rep_of l i"
  by (metis list_update_id rep_of_min)   

lemma rep_of_idx: 
  "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow> rep_of l (l!i) = rep_of l i"
  by (metis rep_of_step)

subsubsection \<open>Abstraction to Partial Equivalence Relation\<close>
definition ufa_\<alpha> :: "nat list \<Rightarrow> (nat\<times>nat) set" 
  where "ufa_\<alpha> l 
    \<equiv> {(x,y). x<length l \<and> y<length l \<and> rep_of l x = rep_of l y}"

lemma ufa_\<alpha>_equiv[simp, intro!]: "part_equiv (ufa_\<alpha> l)"
  apply rule
  unfolding ufa_\<alpha>_def
  apply (rule symI)
  apply auto
  apply (rule transI)
  apply auto
  done

lemma ufa_\<alpha>_lenD: 
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> x<length l"
  "(x,y)\<in>ufa_\<alpha> l \<Longrightarrow> y<length l"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_dom[simp]: "Domain (ufa_\<alpha> l) = {0..<length l}"
  unfolding ufa_\<alpha>_def by auto

lemma ufa_\<alpha>_refl[simp]: "(i,i)\<in>ufa_\<alpha> l \<longleftrightarrow> i<length l"
  unfolding ufa_\<alpha>_def
  by simp

lemma ufa_\<alpha>_len_eq: 
  assumes "ufa_\<alpha> l = ufa_\<alpha> l'"  
  shows "length l = length l'"
  by (metis assms le_antisym less_not_refl linorder_le_less_linear ufa_\<alpha>_refl)

subsubsection \<open>Operations\<close>
lemma ufa_init_invar: "ufa_invar [0..<n]"
  unfolding ufa_invar_def
  by (auto intro: rep_of.domintros)

lemma ufa_init_correct: "ufa_\<alpha> [0..<n] = {(x,x) | x. x<n}"
  unfolding ufa_\<alpha>_def
  using ufa_init_invar[of n]
  apply (auto simp: rep_of_refl)
  done

lemma ufa_find_correct: "\<lbrakk>ufa_invar l; x<length l; y<length l\<rbrakk> 
  \<Longrightarrow> rep_of l x = rep_of l y \<longleftrightarrow> (x,y)\<in>ufa_\<alpha> l"
  unfolding ufa_\<alpha>_def
  by auto

abbreviation "ufa_union l x y \<equiv> l[rep_of l x := rep_of l y]"

lemma ufa_union_invar:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l"
  shows "ufa_invar (ufa_union l x y)"
  unfolding ufa_invar_def
proof (intro allI impI, simp only: length_list_update)
  fix i
  assume A: "i<length l"
  with I have "rep_of_dom (l,i)" by (auto dest: ufa_invarD)

  have "ufa_union l x y ! i < length l" using I L A
    apply (cases "i=rep_of l x")
    apply (auto simp: rep_of_bound dest: ufa_invarD)
    done
  moreover have "rep_of_dom (ufa_union l x y, i)" using I A L
  proof (induct rule: rep_of_induct)
    case (base i)
    thus ?case
      apply -
      apply (rule rep_of.domintros)
      apply (cases "i=rep_of l x")
      apply auto
      apply (rule rep_of.domintros)
      apply (auto simp: rep_of_min)
      done
  next
    case (step i)

    from step.prems \<open>ufa_invar l\<close> \<open>i<length l\<close> \<open>l!i\<noteq>i\<close> 
    have [simp]: "ufa_union l x y ! i = l!i"
      apply (auto simp: rep_of_min rep_of_bound nth_list_update)
      done

    from step show ?case
      apply -
      apply (rule rep_of.domintros)
      apply simp
      done
  qed
  ultimately show 
    "rep_of_dom (ufa_union l x y, i) \<and> ufa_union l x y ! i < length l"
    by blast

qed

lemma ufa_union_aux:
  assumes I: "ufa_invar l"
  assumes L: "x<length l" "y<length l" 
  assumes IL: "i<length l"
  shows "rep_of (ufa_union l x y) i = 
    (if rep_of l i = rep_of l x then rep_of l y else rep_of l i)"
  using I IL
proof (induct rule: rep_of_induct)
  case (base i)
  have [simp]: "rep_of l i = i" using \<open>l!i=i\<close> by (simp add: rep_of_refl)
  note [simp] = \<open>ufa_invar l\<close> \<open>i<length l\<close>
  show ?case proof (cases)
    assume A[simp]: "rep_of l x = i"
    have [simp]: "l[i := rep_of l y] ! i = rep_of l y" 
      by (auto simp: rep_of_bound)

    show ?thesis proof (cases)
      assume [simp]: "rep_of l y = i" 
      show ?thesis by (simp add: rep_of_refl)
    next
      assume A: "rep_of l y \<noteq> i"
      have [simp]: "rep_of (l[i := rep_of l y]) i = rep_of l y"
        apply (subst rep_of_step[OF ufa_union_invar[OF I L], simplified])
        using A apply simp_all
        apply (subst rep_of_refl[where i="rep_of l y"])
        using I L
        apply (simp_all add: rep_of_min)
        done
      show ?thesis by (simp add: rep_of_refl)
    qed
  next
    assume A: "rep_of l x \<noteq> i"
    hence "ufa_union l x y ! i = l!i" by (auto)
    also note \<open>l!i=i\<close>
    finally have "rep_of (ufa_union l x y) i = i" by (simp add: rep_of_refl)
    thus ?thesis using A by auto
  qed
next    
  case (step i)

  note [simp] = I L \<open>i<length l\<close>

  have "rep_of l x \<noteq> i" by (metis I L(1) rep_of_min \<open>l!i\<noteq>i\<close>)
  hence [simp]: "ufa_union l x y ! i = l!i"
    by (auto simp add: nth_list_update rep_of_bound \<open>l!i\<noteq>i\<close>) []

  have "rep_of (ufa_union l x y) i = rep_of (ufa_union l x y) (l!i)" 
    by (auto simp add: rep_of_iff[OF ufa_union_invar[OF I L]])
  also note step.hyps(4)
  finally show ?case
    by (auto simp: rep_of_idx)
qed
  
lemma ufa_union_correct: "\<lbrakk> ufa_invar l; x<length l; y<length l \<rbrakk> 
  \<Longrightarrow> ufa_\<alpha> (ufa_union l x y) = per_union (ufa_\<alpha> l) x y"
  unfolding ufa_\<alpha>_def per_union_def
  by (auto simp: ufa_union_aux
    split: if_split_asm
  )

lemma ufa_compress_aux:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  and "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
proof -
  {
    fix i
    assume "i<length (l[x := rep_of l x])"
    hence IL: "i<length l" by simp

    have G1: "l[x := rep_of l x] ! i < length (l[x := rep_of l x])"
      using I IL 
      by (auto dest: ufa_invarD[OF I] simp: nth_list_update rep_of_bound)
    from I IL have G2: "rep_of (l[x := rep_of l x]) i = rep_of l i 
      \<and> rep_of_dom (l[x := rep_of l x], i)"
    proof (induct rule: rep_of_induct)
      case (base i)
      thus ?case
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_refl)
        done
    next
      case (step i) 
      hence D: "rep_of_dom (l[x := rep_of l x], i)"
        apply -
        apply (rule rep_of.domintros)
        apply (cases "x=i")
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
      
      thus ?case apply simp using step
        apply -
        apply (subst rep_of.psimps[OF D])
        apply (cases "x=i")
        apply (auto simp: rep_of_min rep_of_idx)
        apply (subst rep_of.psimps[where i="rep_of l i"])
        apply (auto intro: rep_of.domintros simp: rep_of_min)
        done
    qed
    note G1 G2
  } note G=this

  thus "\<forall>i<length l. rep_of (l[x := rep_of l x]) i = rep_of l i"
    by auto

  from G show "ufa_invar (l[x := rep_of l x])" 
    by (auto simp: ufa_invar_def)
qed

lemma ufa_compress_invar:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_invar (l[x := rep_of l x])" 
  using assms by (rule ufa_compress_aux)

lemma ufa_compress_correct:
  assumes I: "ufa_invar l"
  assumes L[simp]: "x<length l"
  shows "ufa_\<alpha> (l[x := rep_of l x]) = ufa_\<alpha> l"
  by (auto simp: ufa_\<alpha>_def ufa_compress_aux[OF I])

subsection \<open>Implementation with Imperative/HOL\<close>
text \<open>In this section, we implement the union-find data-structure with
  two arrays, one holding the next-pointers, and another one holding the size
  information. Note that we do not prove that the array for the 
  size information contains any reasonable values, as the correctness of the
  algorithm is not affected by this. We leave it future work to also estimate
  the complexity of the algorithm.
\<close>

type_synonym uf = "nat array \<times> nat array"

definition is_uf :: "(nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where 
  "is_uf R u \<equiv> case u of (s,p) \<Rightarrow> 
  \<exists>\<^sub>Al szl. p\<mapsto>\<^sub>al * s\<mapsto>\<^sub>aszl 
    * \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length szl = length l)"

definition uf_init :: "nat \<Rightarrow> uf Heap" where 
  "uf_init n \<equiv> do {
    l \<leftarrow> Array.of_list [0..<n];
    szl \<leftarrow> Array.new n (1::nat);
    return (szl,l)
  }"

lemma uf_init_rule[sep_heap_rules]: 
  "<emp> uf_init n <is_uf {(i,i) |i. i<n}>"
  unfolding uf_init_def is_uf_def[abs_def]
  by (sep_auto simp: ufa_init_correct ufa_init_invar)

partial_function (heap) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" 
  where [code]: 
  "uf_rep_of p i = do {
    n \<leftarrow> Array.nth p i;
    if n=i then return i else uf_rep_of p n
  }"

lemma uf_rep_of_rule[sep_heap_rules]: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_rep_of p i <\<lambda>r. p\<mapsto>\<^sub>al * \<up>(r=rep_of l i)>"
  apply (induct rule: rep_of_induct)
  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_refl)

  apply (subst uf_rep_of.simps)
  apply (sep_auto simp: rep_of_step)
  done

text \<open>We chose a non tail-recursive version here, as it is easier to prove.\<close>
partial_function (heap) uf_compress :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" 
  where [code]: 
  "uf_compress i ci p = (
    if i=ci then return ()
    else do {
      ni\<leftarrow>Array.nth p i;
      uf_compress ni ci p;
      Array.upd i ci p;
      return ()
    })"

lemma uf_compress_rule: "\<lbrakk> ufa_invar l; i<length l; ci=rep_of l i \<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_compress i ci p 
  <\<lambda>_. \<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' * \<up>(ufa_invar l' \<and> length l' = length l 
     \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>"
proof (induction rule: rep_of_induct)
  case (base i) thus ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: rep_of_refl)
    done
next
  case (step i)
  note SS = \<open>ufa_invar l\<close> \<open>i<length l\<close> \<open>l!i\<noteq>i\<close> \<open>ci = rep_of l i\<close>

  from step.IH 
  have IH': 
    "<p \<mapsto>\<^sub>a l> 
       uf_compress (l ! i) (rep_of l i) p
     <\<lambda>_. \<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * 
        \<up> (ufa_invar l' \<and> length l = length l' 
           \<and> (\<forall>i<length l'. rep_of l i = rep_of l' i))
     >"
    apply (simp add: rep_of_idx SS)
    apply (erule 
      back_subst[OF _ cong[OF cong[OF arg_cong[where f=hoare_triple]]]])
    apply (auto) [2]
    apply (rule ext)
    apply (rule ent_iffI)
    apply sep_auto+
    done

  show ?case
    apply (subst uf_compress.simps)
    apply (sep_auto simp: SS)

    apply (rule IH')
    
    using SS apply (sep_auto (plain)) 
    using ufa_compress_invar apply fastforce []
    apply simp
    using ufa_compress_aux(2) apply fastforce []
    done
qed

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap"
  where "uf_rep_of_c p i \<equiv> do {
    ci\<leftarrow>uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"

lemma uf_rep_of_c_rule[sep_heap_rules]: "\<lbrakk>ufa_invar l; i<length l\<rbrakk> \<Longrightarrow>
  <p\<mapsto>\<^sub>al> uf_rep_of_c p i <\<lambda>r. \<exists>\<^sub>Al'. p\<mapsto>\<^sub>al' 
    * \<up>(r=rep_of l i \<and> ufa_invar l'
       \<and> length l' = length l 
       \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>"
  unfolding uf_rep_of_c_def
  by (sep_auto heap: uf_compress_rule)

definition uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where 
  "uf_cmp u i j \<equiv> do {
    let (s,p)=u;
    n\<leftarrow>Array.len p;
    if (i\<ge>n \<or> j\<ge>n) then return False
    else do {
      ci\<leftarrow>uf_rep_of_c p i;
      cj\<leftarrow>uf_rep_of_c p j;
      return (ci=cj)
    }
  }"

lemma cnv_to_ufa_\<alpha>_eq: 
  "\<lbrakk>(\<forall>i<length l. rep_of l' i = rep_of l i); length l = length l'\<rbrakk> 
  \<Longrightarrow> (ufa_\<alpha> l = ufa_\<alpha> l')"
  unfolding ufa_\<alpha>_def by auto

lemma uf_cmp_rule[sep_heap_rules]:
  "<is_uf R u> uf_cmp u i j <\<lambda>r. is_uf R u * \<up>(r\<longleftrightarrow>(i,j)\<in>R)>"
  unfolding uf_cmp_def is_uf_def
  apply (sep_auto dest: ufa_\<alpha>_lenD simp: not_le split: prod.split)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (drule cnv_to_ufa_\<alpha>_eq, simp_all)
  apply (subst ufa_find_correct)
  apply (auto simp add: )
  done
  

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where 
  "uf_union u i j \<equiv> do {
    let (s,p)=u;
    ci \<leftarrow> uf_rep_of p i;
    cj \<leftarrow> uf_rep_of p j;
    if (ci=cj) then return (s,p) 
    else do {
      si \<leftarrow> Array.nth s ci;
      sj \<leftarrow> Array.nth s cj;
      if si<sj then do {
        Array.upd ci cj p;
        Array.upd cj (si+sj) s;
        return (s,p)
      } else do { 
        Array.upd cj ci p;
        Array.upd ci (si+sj) s;
        return (s,p)
      }
    }
  }"

lemma uf_union_rule[sep_heap_rules]: "\<lbrakk>i\<in>Domain R; j\<in> Domain R\<rbrakk> 
  \<Longrightarrow> <is_uf R u> uf_union u i j <is_uf (per_union R i j)>"
  unfolding uf_union_def
  apply (cases u)
  apply (simp add: is_uf_def[abs_def])
  apply (sep_auto 
    simp: per_union_cmp ufa_\<alpha>_lenD ufa_find_correct
    rep_of_bound
    ufa_union_invar
    ufa_union_correct
  )
  done


export_code uf_init uf_cmp uf_union checking SML_imp

export_code uf_init uf_cmp uf_union checking Scala_imp

(*
ML_val {*
  val u = @{code uf_init} 10 ();

  val u = @{code uf_union} u 1 2 ();
  val u = @{code uf_union} u 3 4 ();
  val u = @{code uf_union} u 5 6 ();
  val u = @{code uf_union} u 7 8 ();

  val u = @{code uf_union} u 1 3 ();
  val u = @{code uf_union} u 5 7 ();

  val u = @{code uf_union} u 1 5 ();

  val b = @{code uf_cmp} u 8 4 ();
  val it = u;
*}*)

end
