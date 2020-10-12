section \<open>Foreach Loops\<close>
theory Refine_Foreach
imports 
  Refine_While 
  Refine_Pfun 
  Refine_Transfer 
  Refine_Heuristics
  (*"../Collections/Lib/SetIterator"
  "../Collections/Lib/Proper_Iterator"*)
begin

text \<open>
  A common pattern for loop usage is iteration over the elements of a set.
  This theory provides the \<open>FOREACH\<close>-combinator, that iterates over 
  each element of a set.
\<close>

subsection \<open>Auxilliary Lemmas\<close>
text \<open>The following lemma is commonly used when reasoning about iterator
  invariants.
  It helps converting the set of elements that remain to be iterated over to
  the set of elements already iterated over.\<close>
lemma it_step_insert_iff: 
  "it \<subseteq> S \<Longrightarrow> x\<in>it \<Longrightarrow> S-(it-{x}) = insert x (S-it)" by auto

subsection \<open>Definition\<close>

text \<open>
  Foreach-loops come in different versions, depending on whether they have an 
  annotated invariant (I), a termination condition (C), and an order (O).

  Note that asserting that the set is finite is not necessary to guarantee
  termination. However, we currently provide only iteration over finite sets,
  as this also matches the ICF concept of iterators.
\<close>
   
definition "FOREACH_body f \<equiv> \<lambda>(xs, \<sigma>). do {
  let x = hd xs; \<sigma>'\<leftarrow>f x \<sigma>; RETURN (tl xs,\<sigma>')
  }"

definition FOREACH_cond where "FOREACH_cond c \<equiv> (\<lambda>(xs,\<sigma>). xs\<noteq>[] \<and> c \<sigma>)"

text \<open>Foreach with continuation condition, order and annotated invariant:\<close>

definition FOREACHoci ("FOREACH\<^sub>O\<^sub>C\<^bsup>_,_\<^esup>") where "FOREACHoci R \<Phi> S c f \<sigma>0 \<equiv> do {
  ASSERT (finite S);
  xs \<leftarrow> SPEC (\<lambda>xs. distinct xs \<and> S = set xs \<and> sorted_wrt R xs);
  (_,\<sigma>) \<leftarrow> WHILEIT 
    (\<lambda>(it,\<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>) (FOREACH_cond c) (FOREACH_body f) (xs,\<sigma>0); 
  RETURN \<sigma> }"

text \<open>Foreach with continuation condition and annotated invariant:\<close>
definition FOREACHci ("FOREACH\<^sub>C\<^bsup>_\<^esup>") where "FOREACHci \<equiv> FOREACHoci (\<lambda>_ _. True)"

text \<open>Foreach with continuation condition:\<close>
definition FOREACHc ("FOREACH\<^sub>C") where "FOREACHc \<equiv> FOREACHci (\<lambda>_ _. True)"

text \<open>Foreach with annotated invariant:\<close>
definition FOREACHi ("FOREACH\<^bsup>_\<^esup>") where 
  "FOREACHi \<Phi> S \<equiv> FOREACHci \<Phi> S (\<lambda>_. True)"

text \<open>Foreach with annotated invariant and order:\<close>
definition FOREACHoi ("FOREACH\<^sub>O\<^bsup>_,_\<^esup>") where 
  "FOREACHoi R \<Phi> S \<equiv> FOREACHoci R \<Phi> S (\<lambda>_. True)"

text \<open>Basic foreach\<close>
definition "FOREACH S \<equiv> FOREACHc S (\<lambda>_. True)"

lemmas FOREACH_to_oci_unfold
  = FOREACHci_def FOREACHc_def FOREACHi_def FOREACHoi_def FOREACH_def

subsection \<open>Proof Rules\<close>

lemma FOREACHoci_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> c \<sigma>; x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma>;
                         \<forall>x\<in>it. \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoci R I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHoci_def
  apply (intro refine_vcg)

  apply (rule FIN)

  apply (subgoal_tac "wf (measure (\<lambda>(xs, _). length xs))")
    apply assumption
    apply simp

  apply (insert I0, simp add: I0) []
  unfolding FOREACH_body_def FOREACH_cond_def
  apply (rule refine_vcg)+
  apply ((simp, elim conjE exE)+) []
  apply (rename_tac xs'' s xs' \<sigma> xs)
defer
  apply (simp, elim conjE exE)+
  apply (rename_tac x s xs' \<sigma> xs)
defer
proof -
  fix xs' \<sigma> xs

  assume I_xs': "I (set xs') \<sigma>"
     and sorted_xs_xs': "sorted_wrt R (xs @ xs')"
     and dist: "distinct xs" "distinct xs'" "set xs \<inter> set xs' = {}"
     and S_eq: "S = set xs \<union> set xs'" 

  from S_eq have "set xs' \<subseteq> S" by simp
  from dist S_eq have S_diff: "S - set xs' = set xs" by blast

  { assume "xs' \<noteq> []" "c \<sigma>"
    from \<open>xs' \<noteq> []\<close> obtain x xs'' where xs'_eq: "xs' = x # xs''" by (cases xs', auto)

    have x_in_xs': "x \<in> set xs'" and x_nin_xs'': "x \<notin> set xs''" 
       using \<open>distinct xs'\<close> unfolding xs'_eq by simp_all
  
    from IP[of \<sigma> x "set xs'", OF \<open>c \<sigma>\<close> x_in_xs' \<open>set xs' \<subseteq> S\<close> \<open>I (set xs') \<sigma>\<close>] x_nin_xs''
         sorted_xs_xs' S_diff
    show "f (hd xs') \<sigma> \<le> SPEC
            (\<lambda>x. (\<exists>xs'a. xs @ xs' = xs'a @ tl xs') \<and>
                 I (set (tl xs')) x)"
      apply (simp add: xs'_eq)
      apply (simp add: sorted_wrt_append)
    done
  }

  { assume "xs' = [] \<or> \<not>(c \<sigma>)"
    show "P \<sigma>" 
    proof (cases "xs' = []")
      case True thus "P \<sigma>" using \<open>I (set xs') \<sigma>\<close> by (simp add: II1)
    next
      case False note xs'_neq_nil = this
      with \<open>xs' = [] \<or> \<not> c \<sigma>\<close> have "\<not> c \<sigma>" by simp
 
      from II2 [of "set xs'" \<sigma>] S_diff sorted_xs_xs'
      show "P \<sigma>" 
        apply (simp add: xs'_neq_nil S_eq \<open>\<not> c \<sigma>\<close> I_xs')
        apply (simp add: sorted_wrt_append)
      done
    qed
  }
qed

lemma FOREACHoi_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoi R I S f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHoi_def 
  by (rule FOREACHoci_rule) (simp_all add: assms)

lemma FOREACHci_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHci I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHci_def
  by (rule FOREACHoci_rule) (simp_all add: assms)

subsubsection \<open>Refinement:\<close>

text \<open>
  Refinement rule using a coupling invariant over sets of remaining
  items and the state.
\<close>

lemma FOREACHoci_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; 
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; \<forall>y\<in>it-{x}. RR x y;
    x'\<in>it'; \<forall>y'\<in>it'-{x'}. RR' x' y';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R' (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"
  (* TODO: Clean up this mess !!! *)
  unfolding FOREACHoci_def
  apply (refine_rcg WHILEIT_refine_genR[where 
    R'="{((xs,\<sigma>),(xs',\<sigma>')) . 
      xs'=map \<alpha> xs \<and> 
      set xs \<subseteq> S \<and> set xs' \<subseteq> S' \<and>
      (\<forall>x\<in>S - set xs. \<forall>y\<in>set xs. RR x y) \<and>
      (\<forall>x\<in>S' - set xs'. \<forall>y\<in>set xs'. RR' x y) \<and>
      ((set xs,\<sigma>),(set xs',\<sigma>')) \<in> R }"
    ])

  using REFS INJ apply (auto dest: finite_imageD) []
  apply (rule intro_prgR[where R="{(xs,xs') . xs'=map \<alpha> xs }"])
  apply (rule SPEC_refine)
  using INJ RR_OK 
  apply (auto 
    simp add: distinct_map sorted_wrt_map 
    intro: sorted_wrt_mono_rel[of _ RR]) []
  using REF0 apply auto []

  apply simp apply (rule conjI)
  using INJ apply clarsimp
  apply (erule map_eq_appendE)
  apply clarsimp
  apply (rule_tac x=l in exI)
  apply simp
  apply (subst inj_on_map_eq_map[where f=\<alpha>,symmetric])
  apply (rule subset_inj_on, assumption, blast)
  apply assumption

  apply (simp split: prod.split_asm, elim conjE)
  apply (rule REFPHI, auto) []

  apply (simp add: FOREACH_cond_def split: prod.split prod.split_asm, 
    intro allI impI conj_cong) []
  apply auto []
  apply (rule REFC, auto) []

  unfolding FOREACH_body_def
  apply refine_rcg
  apply (rule REFSTEP) []
  prefer 3 apply auto []
  prefer 3 apply auto []
  apply simp_all[13]
  apply auto []
  apply (rename_tac a b d e f g h i) 
  apply (case_tac h, auto simp: FOREACH_cond_def) []
  apply auto []
  apply (auto simp: FOREACH_cond_def) []
  apply (clarsimp simp: FOREACH_cond_def)
  apply (rule ccontr)
  apply (rename_tac a b d e f)
  apply (case_tac b)
  apply (auto simp: sorted_wrt_append) [2]

  apply (auto simp: FOREACH_cond_def) []
  apply (rename_tac a b d e)
  apply (case_tac b)
  apply (auto) [2]

  apply (clarsimp simp: FOREACH_cond_def)
  apply (rule ccontr)
  apply (rename_tac a b d e f)
  apply (case_tac b)
  apply (auto simp: sorted_wrt_append) [2]

  apply (clarsimp simp: FOREACH_cond_def)
  apply (clarsimp simp: FOREACH_cond_def)
 
  apply (clarsimp simp: map_tl)
  apply (intro conjI)

  apply (rename_tac a b d e f g)
  apply (case_tac b, auto) []
  apply (rename_tac a b d e f g)
  apply (case_tac b, auto) []
  apply (rename_tac a b d e f g)
  apply (case_tac b, auto simp: sorted_wrt_append) []
  apply (rename_tac a b d e f g)
  apply (case_tac b, auto simp: sorted_wrt_append) []
  apply (rename_tac a b d e f g)
  apply (case_tac b, auto) []

  apply (rule introR[where R="{((xs,\<sigma>),(xs',\<sigma>')). 
      xs'=map \<alpha> xs \<and> \<Phi> (set xs) \<sigma> \<and> \<Phi>' (set xs') \<sigma>' \<and>
      set xs \<subseteq> S \<and> set xs' \<subseteq> S' \<and>
      (\<forall>x\<in>S - set xs. \<forall>y\<in>set xs. RR x y) \<and>
      (\<forall>x\<in>S' - set xs'. \<forall>y\<in>set xs'. RR' x y) \<and>
      ((set xs,\<sigma>),(set xs',\<sigma>')) \<in> R \<and>
      \<not> FOREACH_cond c (xs,\<sigma>) \<and> \<not> FOREACH_cond c' (xs',\<sigma>')
    }
    "])
  apply auto []
  apply (simp add: FOREACH_cond_def, elim conjE)
  apply (elim disjE1, simp_all) []
  using REF_R_DONE apply auto []
  using REF_R_BRK apply auto []
  done

lemma FOREACHoci_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>\<forall>y\<in>it-{x}. RR x y; 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"

  apply (rule FOREACHoci_refine_genR[
    where R = "{((it,\<sigma>),(it',\<sigma>')). (\<sigma>,\<sigma>')\<in>R \<and> \<Phi>'' it \<sigma> it' \<sigma>'}"
    ])
  apply fact
  apply fact
  apply fact
  using REF0 REFPHI0 apply blast
  using REFC apply auto []
  using REFPHI apply auto []
  using REFSTEP apply auto []
  apply auto []
  apply auto []
  done
 
lemma FOREACHoci_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> \<forall>y\<in>it-{x}. RR x y;
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHoci RR \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHoci RR' \<Phi>' S' c' f' \<sigma>0')"
  apply (rule FOREACHoci_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHoci_weaken:
  assumes IREF: "\<And>it \<sigma>. it\<subseteq>S \<Longrightarrow> I it \<sigma> \<Longrightarrow> I' it \<sigma>"
  shows "FOREACHoci RR I' S c f \<sigma>0 \<le> FOREACHoci RR I S c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: IREF)
  done

lemma FOREACHoci_weaken_order:
  assumes RRREF: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> RR x y \<Longrightarrow> RR' x y"
  shows "FOREACHoci RR I S c f \<sigma>0 \<le> FOREACHoci RR' I S c f \<sigma>0"
  apply (rule FOREACHoci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: RRREF)
  done


subsubsection \<open>Rules for Derived Constructs\<close>

lemma FOREACHoi_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    \<forall>x\<in>S-it. \<forall>y\<in>it. RR x y; \<forall>x\<in>S'-it'. \<forall>y\<in>it'. RR' x y;
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; \<forall>y\<in>it-{x}. RR x y;
    x'\<in>it'; \<forall>y'\<in>it'-{x'}. RR' x' y'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R' (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHoi_def
  apply (rule FOREACHoci_refine_genR)
  apply (fact | simp)+
  using REFSTEP apply auto []
  apply (fact | simp)+
  done

lemma FOREACHoi_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>\<forall>y\<in>it-{x}. RR x y; 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHoi_def
  apply (rule FOREACHoci_refine [of \<alpha> _ _ _ _ _ _ _ \<Phi>''])
  apply (simp_all add: assms)
done

lemma FOREACHoi_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes RR_OK: "\<And>x y. \<lbrakk>x \<in> S; y \<in> S; RR x y\<rbrakk> \<Longrightarrow> RR' (\<alpha> x) (\<alpha> y)"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> \<forall>y\<in>it-{x}. RR x y;
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHoi RR \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHoi RR' \<Phi>' S' f' \<sigma>0')"
  apply (rule FOREACHoi_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by simp_all

lemma FOREACHci_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R' (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHci_def
  apply (rule FOREACHoci_refine_genR)
  apply (fact|simp)+
  using REFC apply auto []
  using REFPHI apply auto []
  using REFSTEP apply auto []
  apply (fact|simp)+
  using REF_R_BRK apply auto []
  done

lemma FOREACHci_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHci_def
  apply (rule FOREACHoci_refine [of \<alpha> _ _ _ _ _ _ _ \<Phi>''])
  apply (simp_all add: assms)
done

lemma FOREACHci_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi> it \<sigma>; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHci \<Phi> S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  apply (rule FOREACHci_refine[where \<Phi>''="\<lambda>_ _ _ _. True"])
  apply (rule assms)+
  using assms by auto

lemma FOREACHci_weaken:
  assumes IREF: "\<And>it \<sigma>. it\<subseteq>S \<Longrightarrow> I it \<sigma> \<Longrightarrow> I' it \<sigma>"
  shows "FOREACHci I' S c f \<sigma>0 \<le> FOREACHci I S c f \<sigma>0"
  apply (rule FOREACHci_refine_rcg[where \<alpha>=id and R=Id, simplified])
  apply (auto intro: IREF)
  done

lemma FOREACHi_rule[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHi I S f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHi_def
  apply (rule FOREACHci_rule[of S I])
  using assms by auto

lemma FOREACHc_rule:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<noteq>{}; it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHc S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule[where I=I])
  using assms by auto

lemma FOREACH_rule:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACH S f \<sigma>0 \<le> SPEC P"
  unfolding FOREACH_def FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule[where I=I])
  using assms by auto


lemma FOREACHc_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; 
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it';
    c \<sigma>; c' \<sigma>'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  assumes REF_R_BRK: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; 
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    it\<noteq>{}; it'\<noteq>{};
    \<not>c \<sigma>; \<not>c' \<sigma>'
  \<rbrakk> \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R' (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_genR)
  apply simp_all
  apply (fact|simp)+
  using REFC apply auto []
  using REFSTEP apply auto []
  using REF_R_DONE apply auto []
  using REF_R_BRK apply auto []
  done

lemma FOREACHc_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>'' it \<sigma> it' \<sigma>'; c \<sigma>; c' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 REFPHI0])
  apply (erule (4) REFC)
  apply (rule TrueI)
  apply (erule (9) REFSTEP)
  done

lemma FOREACHc_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHc S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_rcg)
  apply (rule assms)+
  using assms by auto

lemma FOREACHi_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>';
    it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S'; \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<Phi> {} \<sigma>; \<Phi>' {} \<sigma>'; (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R' (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine_genR)
  apply (fact|simp)+
  using REFSTEP apply auto []
  apply (fact|simp)+
  done

lemma FOREACHi_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';  \<Phi>'' it \<sigma> it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 REFPHI0])
  apply (rule refl)
  apply (erule (5) REFPHI)
  apply (erule (9) REFSTEP)
  done

lemma FOREACHi_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFPHI: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> \<Phi> it \<sigma>"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi> it \<sigma>; \<Phi>' it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHi \<Phi> S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACHi_def
  apply (rule FOREACHci_refine_rcg)
  apply (rule assms)+
  using assms apply auto
  done

lemma FOREACH_refine_genR:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa" \<comment> \<open>Abstraction mapping of elements\<close>
  fixes S :: "'S set" \<comment> \<open>Concrete set\<close>
  fixes S' :: "'Sa set" \<comment> \<open>Abstract set\<close>
  fixes \<sigma>0 :: "'\<sigma>"
  fixes \<sigma>0' :: "'\<sigma>a"
  fixes R :: "(('S set \<times> '\<sigma>) \<times> ('Sa set \<times> '\<sigma>a)) set"
  assumes INJ: "inj_on \<alpha> S" 
  assumes REFS[simp]: "S' = \<alpha>`S"
  assumes REF0: "((S,\<sigma>0),(\<alpha>`S,\<sigma>0')) \<in> R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk>
    it\<subseteq>S; it'\<subseteq>S';
    x'=\<alpha> x; it'=\<alpha>`it; ((it,\<sigma>),(it',\<sigma>'))\<in>R;
    x\<in>it; x'\<in>it'
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). ((it-{x},\<sigma>),(it'-{x'},\<sigma>'))\<in>R}) (f' x' \<sigma>')"
  assumes REF_R_DONE: "\<And>\<sigma> \<sigma>'. \<lbrakk> (({},\<sigma>),({},\<sigma>'))\<in>R \<rbrakk> 
    \<Longrightarrow> (\<sigma>,\<sigma>')\<in>R'"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R' (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine_genR)
  apply (fact|simp)+
  using REFSTEP apply auto []
  apply (fact|simp)+
  done

lemma FOREACH_refine:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFPHI0: "\<Phi>'' S \<sigma>0 (\<alpha>`S) \<sigma>0'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>'' it \<sigma> it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> 
    \<le> \<Down>({(\<sigma>, \<sigma>'). (\<sigma>, \<sigma>') \<in> R \<and> \<Phi>'' (it - {x}) \<sigma> (it' - {x'}) \<sigma>'}) (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine[where \<Phi>''=\<Phi>'', OF INJ REFS REF0 REFPHI0])
  apply (rule refl)
  apply (erule (7) REFSTEP)
  done

lemma FOREACH_refine_rcg[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACH S' f' \<sigma>0')"
  unfolding FOREACH_def
  apply (rule FOREACHc_refine_rcg)
  apply (rule assms)+
  using assms by auto

lemma FOREACHci_refine_rcg'[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFC: "\<And>it \<sigma> it' \<sigma>'. \<lbrakk> 
    it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S'; \<Phi>' it' \<sigma>'; (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> c \<sigma> \<longleftrightarrow> c' \<sigma>'"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>' it' \<sigma>'; c \<sigma>; c' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACHc S c f \<sigma>0 \<le> \<Down>R (FOREACHci \<Phi>' S' c' f' \<sigma>0')"
  unfolding FOREACHc_def
  apply (rule FOREACHci_refine_rcg) 
  apply (rule assms)
  apply (rule assms)
  apply (rule assms)
  apply (erule (4) REFC)
  apply (rule TrueI)
  apply (rule REFSTEP, assumption+)
  done

lemma FOREACHi_refine_rcg'[refine]:
  fixes \<alpha> :: "'S \<Rightarrow> 'Sa"
  fixes S :: "'S set"
  fixes S' :: "'Sa set"
  assumes INJ: "inj_on \<alpha> S"
  assumes REFS: "S' = \<alpha>`S"
  assumes REF0: "(\<sigma>0,\<sigma>0')\<in>R"
  assumes REFSTEP: "\<And>x it \<sigma> x' it' \<sigma>'. \<lbrakk> 
    x'=\<alpha> x; x\<in>it; x'\<in>it'; it'=\<alpha>`it; it\<subseteq>S; it'\<subseteq>S';
    \<Phi>' it' \<sigma>';
    (\<sigma>,\<sigma>')\<in>R
  \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> \<Down>R (f' x' \<sigma>')"
  shows "FOREACH S f \<sigma>0 \<le> \<Down>R (FOREACHi \<Phi>' S' f' \<sigma>0')"
  unfolding FOREACH_def FOREACHi_def
  apply (rule FOREACHci_refine_rcg') 
  apply (rule assms)+
  apply simp
  apply (rule REFSTEP, assumption+)
  done

subsubsection \<open>Alternative set of FOREACHc-rules\<close>
text \<open>Here, we provide an alternative set of FOREACH rules with 
  interruption. In some cases, they are easier to use, as they avoid 
  redundancy between the final cases for interruption and non-interruption\<close>

lemma FOREACHoci_rule':
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> c \<sigma>; x\<in>it; it\<subseteq>S; I it \<sigma>; \<forall>y\<in>it - {x}. R x y;
                \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma>;
                         \<forall>x\<in>it. \<forall>y\<in>S - it. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHoci R I S c f \<sigma>0 \<le> SPEC P"
  apply (rule FOREACHoci_rule[OF FIN, where I=I, OF I0])
  apply (rule IP, assumption+)
  apply (case_tac "c \<sigma>")
  apply (blast intro: II1)
  apply (blast intro: II2)
  apply (blast intro: II2)
  done
  
lemma FOREACHci_rule'[refine_vcg]:
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHci I S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHci_def
  by (rule FOREACHoci_rule') (simp_all add: assms)

lemma FOREACHc_rule':
  assumes FIN: "finite S"
  assumes I0: "I S \<sigma>0"
  assumes IP: 
    "\<And>x it \<sigma>. \<lbrakk> x\<in>it; it\<subseteq>S; I it \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (it-{x}))"
  assumes II1: "\<And>\<sigma>. \<lbrakk>I {} \<sigma>; c \<sigma>\<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes II2: "\<And>it \<sigma>. \<lbrakk> it\<subseteq>S; I it \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "FOREACHc S c f \<sigma>0 \<le> SPEC P"
  unfolding FOREACHc_def
  apply (rule order_trans[OF FOREACHci_weaken], rule TrueI)
  apply (rule FOREACHci_rule'[where I=I])
  using assms by auto



subsection \<open>FOREACH with empty sets\<close>

lemma FOREACHoci_emp [simp] :
  "FOREACHoci R \<Phi> {} c f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
  by (simp add: FOREACHoci_def FOREACH_cond_def bind_RES)
    (simp add: WHILEIT_unfold)

lemma FOREACHoi_emp [simp] :
  "FOREACHoi R \<Phi> {} f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHoi_def)

lemma FOREACHci_emp [simp] :
  "FOREACHci \<Phi> {} c f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHci_def)

lemma FOREACHc_emp [simp] :
  "FOREACHc {} c f \<sigma> = RETURN \<sigma>"
by (simp add: FOREACHc_def)

lemma FOREACH_emp [simp] :
  "FOREACH {} f \<sigma> = RETURN \<sigma>"
by (simp add: FOREACH_def)

lemma FOREACHi_emp [simp] :
  "FOREACHi \<Phi> {} f \<sigma> = do {ASSERT (\<Phi> {} \<sigma>); RETURN \<sigma>}"
by (simp add: FOREACHi_def)

subsection "Monotonicity"

(* TODO: Move to RefineG_Domain *)
definition "lift_refl P c f g == \<forall>x. P c (f x) (g x)"
definition "lift_mono P c f g == \<forall>x y. c x y \<longrightarrow> P c (f x) (g y)"
definition "lift_mono1 P c f g == \<forall>x y. (\<forall>a. c (x a) (y a)) \<longrightarrow> P c (f x) (g y)"
definition "lift_mono2 P c f g == \<forall>x y. (\<forall>a b. c (x a b) (y a b)) \<longrightarrow> P c (f x) (g y)"

definition "trimono_spec L f == ((L id (\<le>) f f) \<and> (L id flat_ge f f))"

lemmas trimono_atomize = atomize_imp atomize_conj atomize_all
lemmas trimono_deatomize = trimono_atomize[symmetric]

lemmas trimono_spec_defs = trimono_spec_def lift_refl_def[abs_def] comp_def id_def
    lift_mono_def[abs_def] lift_mono1_def[abs_def] lift_mono2_def[abs_def]
    trimono_deatomize

locale trimono_spec begin
abbreviation "R \<equiv> lift_refl"
abbreviation "M \<equiv> lift_mono"
abbreviation "M1 \<equiv> lift_mono1"
abbreviation "M2 \<equiv> lift_mono2"
end

context begin interpretation trimono_spec .

lemma FOREACHoci_mono[unfolded trimono_spec_defs,refine_mono]: 
  "trimono_spec (R o R o R o R o M2 o R) FOREACHoci"
  "trimono_spec (R o R o R o M2 o R) FOREACHoi"
  "trimono_spec (R o R o R o M2 o R) FOREACHci"
  "trimono_spec (R o R o M2 o R) FOREACHc"
  "trimono_spec (R o R o M2 o R) FOREACHi"
  "trimono_spec (R o M2 o R) FOREACH"
  apply (unfold trimono_spec_defs)
  apply -
  unfolding FOREACHoci_def FOREACH_to_oci_unfold FOREACH_body_def
  apply (refine_mono)+
  done

end

subsection \<open>Nres-Fold with Interruption (nfoldli)\<close>
text \<open>
  A foreach-loop can be conveniently expressed as an operation that converts
  the set to a list, followed by folding over the list.
  
  This representation is handy for automatic refinement, as the complex 
  foreach-operation is expressed by two relatively simple operations.
\<close>

text \<open>We first define a fold-function in the nres-monad\<close>
partial_function (nrec) nfoldli where
  "nfoldli l c f s = (case l of 
    [] \<Rightarrow> RETURN s 
    | x#ls \<Rightarrow> if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURN s
  )"

lemma nfoldli_simps[simp]:
  "nfoldli [] c f s = RETURN s"
  "nfoldli (x#ls) c f s = 
    (if c s then do { s\<leftarrow>f x s; nfoldli ls c f s} else RETURN s)"
  apply (subst nfoldli.simps, simp)+
  done
  
lemma param_nfoldli[param]:
  shows "(nfoldli,nfoldli) \<in> 
    \<langle>Ra\<rangle>list_rel \<rightarrow> (Rb\<rightarrow>Id) \<rightarrow> (Ra\<rightarrow>Rb\<rightarrow>\<langle>Rb\<rangle>nres_rel) \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  apply (intro fun_relI)
proof goal_cases
  case (1 l l' c c' f f' s s')
  thus ?case
    apply (induct arbitrary: s s')
    apply (simp only: nfoldli_simps True_implies_equals)
    apply parametricity
    apply (simp only: nfoldli_simps True_implies_equals)
    apply (parametricity)
    done
qed

lemma nfoldli_no_ctd[simp]: "\<not>ctd s \<Longrightarrow> nfoldli l ctd f s = RETURN s"
  by (cases l) auto

lemma nfoldli_append[simp]: "nfoldli (l1@l2) ctd f s = nfoldli l1 ctd f s \<bind> nfoldli l2 ctd f"
  by (induction l1 arbitrary: s) (auto simp: pw_eq_iff refine_pw_simps)

lemma nfoldli_map: "nfoldli (map f l) ctd g s = nfoldli l ctd (g o f) s"  
  apply (induction l arbitrary: s) 
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma nfoldli_nfoldli_prod_conv: 
  "nfoldli l2 ctd (\<lambda>i. nfoldli l1 ctd (f i)) s = nfoldli (List.product l2 l1) ctd (\<lambda>(i,j). f i j) s"
proof -
  have [simp]: "nfoldli (map (Pair a) l) ctd (\<lambda>(x, y). f x y) s = nfoldli l ctd (f a) s"
    for a l s
    apply (induction l arbitrary: s) 
    by (auto simp: pw_eq_iff refine_pw_simps)

  show ?thesis  
    by (induction l2 arbitrary: l1 s) auto
qed  
  
  
text \<open>The fold-function over the nres-monad is transfered to a plain 
  foldli function\<close>
lemma nfoldli_transfer_plain[refine_transfer]:
  assumes "\<And>x s. RETURN (f x s) \<le> f' x s"
  shows "RETURN (foldli l c f s) \<le> (nfoldli l c f' s)"
  using assms
  apply (induct l arbitrary: s)
  apply (auto)
  by (metis (lifting) plain_bind)

lemma nfoldli_transfer_dres[refine_transfer]:
  fixes l :: "'a list" and c:: "'b \<Rightarrow> bool"
  assumes FR: "\<And>x s. nres_of (f x s) \<le> f' x s"
  shows "nres_of 
    (foldli l (case_dres False False c) (\<lambda>x s. s\<bind>f x) (dRETURN s)) 
    \<le> (nfoldli l c f' s)"
proof (induct l arbitrary: s)
  case Nil thus ?case by auto
next
  case (Cons a l)
  thus ?case
    apply (auto)
    apply (cases "f a s")
    apply (cases l, simp_all) []
    apply simp
    apply (rule order_trans[rotated])
    apply (rule bind_mono)
    apply (rule FR)
    apply assumption
    apply simp
    apply simp
    using FR[of a s]
    apply simp
    done
qed

lemma nfoldli_mono[refine_mono]: 
  "\<lbrakk> \<And>x s. f x s \<le> f' x s \<rbrakk> \<Longrightarrow> nfoldli l c f \<sigma> \<le> nfoldli l c f' \<sigma>"
  "\<lbrakk> \<And>x s. flat_ge (f x s) (f' x s) \<rbrakk> \<Longrightarrow> flat_ge (nfoldli l c f \<sigma>) (nfoldli l c f' \<sigma>)"
  apply (induct l arbitrary: \<sigma>)
  apply auto
  apply refine_mono

  apply (induct l arbitrary: \<sigma>)
  apply auto
  apply refine_mono
  done

text \<open>We relate our fold-function to the while-loop that we used in
  the original definition of the foreach-loop\<close>
lemma nfoldli_while: "nfoldli l c f \<sigma>
          \<le>
         (WHILE\<^sub>T\<^bsup>I\<^esup>
           (FOREACH_cond c) (FOREACH_body f) (l, \<sigma>) \<bind>
          (\<lambda>(_, \<sigma>). RETURN \<sigma>))"
proof (induct l arbitrary: \<sigma>)
  case Nil thus ?case by (subst WHILEIT_unfold) (auto simp: FOREACH_cond_def)
next
  case (Cons x ls)
  show ?case
  proof (cases "c \<sigma>")
    case False thus ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def
      by simp
  next
    case [simp]: True
    from Cons show ?thesis
      apply (subst WHILEIT_unfold)
      unfolding FOREACH_cond_def FOREACH_body_def
      apply clarsimp
      apply (rule Refine_Basic.bind_mono)
      apply simp_all
      done
  qed
qed

lemma while_nfoldli:
  "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (FOREACH_body f) (l,\<sigma>);
    RETURN \<sigma>
  } \<le> nfoldli l c f \<sigma>"
  apply (induct l arbitrary: \<sigma>)
  apply (subst WHILET_unfold)
  apply (simp add: FOREACH_cond_def)

  apply (subst WHILET_unfold)
  apply (auto
    simp: FOREACH_cond_def FOREACH_body_def
    intro: bind_mono)
  done

lemma while_eq_nfoldli: "do {
    (_,\<sigma>) \<leftarrow> WHILE\<^sub>T (FOREACH_cond c) (FOREACH_body f) (l,\<sigma>);
    RETURN \<sigma>
  } = nfoldli l c f \<sigma>"
  apply (rule antisym)
  apply (rule while_nfoldli)
  apply (rule order_trans[OF nfoldli_while[where I="\<lambda>_. True"]])
  apply (simp add: WHILET_def)
  done

lemma nfoldli_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (l1@[x]) l2)"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli l0 c f \<sigma>0 \<le> SPEC P"
  apply (rule order_trans[OF nfoldli_while[
    where I="\<lambda>(l2,\<sigma>). \<exists>l1. l0=l1@l2 \<and> I l1 l2 \<sigma>"]])
  unfolding FOREACH_cond_def FOREACH_body_def
  apply (refine_rcg WHILEIT_rule[where R="measure (length o fst)"] refine_vcg)
  apply simp
  using I0 apply simp

  apply (case_tac a, simp)
  apply simp
  apply (elim exE conjE)
  apply (rule order_trans[OF IS], assumption+)
  apply auto []

  apply simp
  apply (elim exE disjE2)
  using FC apply auto []
  using FNC apply auto []
  done

lemma nfoldli_leof_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le>\<^sub>n SPEC (I (l1@[x]) l2)"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "nfoldli l0 c f \<sigma>0 \<le>\<^sub>n SPEC P"
proof -
  {
    fix l1 l2 \<sigma>
    assume "l0=l1@l2" "I l1 l2 \<sigma>"
    hence "nfoldli l2 c f \<sigma> \<le>\<^sub>n SPEC P"
    proof (induction l2 arbitrary: l1 \<sigma>)
      case Nil thus ?case
        apply simp
        apply (cases "c \<sigma>")
        apply (rule FC; auto; fail)
        apply (rule FNC[of l1 "[]"]; auto; fail) 
        done
    next
      case (Cons x l2) 
      note [refine_vcg] = Cons.IH[of "l1@[x]",THEN leof_trans] IS[of l1 x l2 \<sigma>,THEN leof_trans]

      show ?case
        apply (simp split del: if_split)
        apply refine_vcg
        using Cons.prems FNC by auto
    qed
  } from this[of "[]" l0 \<sigma>0] I0 show ?thesis by auto
qed  
    
    
lemma nfoldli_refine[refine]:
  assumes "(li, l) \<in> \<langle>S\<rangle>list_rel"
    and "(si, s) \<in> R"
    and CR: "(ci, c) \<in> R \<rightarrow> bool_rel"
    and [refine]: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  shows "nfoldli li ci fi si \<le> \<Down> R (nfoldli l c f s)"
  using assms(1,2)
proof (induction arbitrary: si s rule: list_rel_induct)
  case Nil thus ?case by simp
next
  case (Cons xi x li l) 
  note [refine] = Cons

  show ?case
    apply (simp split del: if_split)
    apply refine_rcg
    using CR Cons.prems by (auto dest: fun_relD)
qed    

(* Refine, establishing additional invariant *)
lemma nfoldli_invar_refine:
  assumes "(li,l)\<in>\<langle>S\<rangle>list_rel"
  assumes "(si,s)\<in>R"
  assumes "I [] li si"
  assumes COND: "\<And>l1i l2i l1 l2 si s. \<lbrakk>
    li=l1i@l2i; l=l1@l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (l2i,l2)\<in>\<langle>S\<rangle>list_rel; 
    I l1i l2i si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> (ci si, c s)\<in>bool_rel"
  assumes INV: "\<And>l1i xi l2i si. \<lbrakk>li=l1i@xi#l2i; I l1i (xi#l2i) si\<rbrakk> \<Longrightarrow> fi xi si \<le>\<^sub>n SPEC (I (l1i@[xi]) l2i)"
  assumes STEP: "\<And>l1i xi l2i l1 x l2 si s. \<lbrakk>
    li=l1i@xi#l2i; l=l1@x#l2; (l1i,l1)\<in>\<langle>S\<rangle>list_rel; (xi,x)\<in>S; (l2i,l2)\<in>\<langle>S\<rangle>list_rel; 
    I l1i (xi#l2i) si; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  shows "nfoldli li ci fi si \<le> \<Down>R (nfoldli l c f s)"
proof -
  {
    have [refine_dref_RELATES]: "RELATES R" "RELATES S" by (auto simp: RELATES_def)

    note [refine del] = nfoldli_refine

    fix l1i l2i l1 l2 si s
    assume "(l2i,l2) \<in> \<langle>S\<rangle>list_rel" "(l1i,l1) \<in> \<langle>S\<rangle>list_rel"
    and "li=l1i@l2i" "l=l1@l2"
    and "(si,s)\<in>R" "I l1i l2i si"
    hence "nfoldli l2i ci fi si \<le> \<Down>R (nfoldli l2 c f s)"
    proof (induction arbitrary: si s l1i l1 rule: list_rel_induct)
      case Nil thus ?case by auto
    next  
      case (Cons xi x l2i l2)

      show ?case
        apply (simp split del: if_split)
        apply (refine_rcg bind_refine')
        apply (refine_dref_type)
        subgoal using COND[of l1i "xi#l2i" l1 "x#l2" si s] Cons.prems Cons.hyps by auto
        subgoal apply (rule STEP) using Cons.prems Cons.hyps by auto
        subgoal for si' s'
          apply (rule Cons.IH[of "l1i@[xi]" "l1@[x]"])
          using Cons.prems Cons.hyps
          apply (auto simp: list_rel_append1) apply force
          using INV[of l1i xi l2i si]
          by (auto simp: pw_leof_iff)
        subgoal using Cons.prems by simp
        done
    qed
  }
  from this[of li l "[]" "[]" si s] assms(1,2,3) show ?thesis by auto
qed
    
    
    
lemma foldli_mono_dres_aux1:
  fixes \<sigma> :: "'a :: {order_bot, order_top}"
  assumes COND: "\<And>\<sigma> \<sigma>'. \<sigma>\<le>\<sigma>' \<Longrightarrow> c \<sigma> \<noteq> c \<sigma>' \<Longrightarrow> \<sigma>=bot \<or> \<sigma>'=top "
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes B: "\<sigma>\<le>\<sigma>'"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l c f \<sigma> \<le> foldli l c f' \<sigma>'"
proof -
  { fix l 
    have "foldli l c f bot = bot" by (induct l) (auto simp: STRICT)
  } note [simp] = this
  { fix l 
    have "foldli l c f' top = top" by (induct l) (auto simp: STRICT)
  } note [simp] = this

  show ?thesis
    using B
    apply (induct l arbitrary: \<sigma> \<sigma>')
    apply (auto simp: A STRICT dest!: COND)
    done
qed

lemma foldli_mono_dres_aux2:
  assumes STRICT: "\<And>x. f x bot = bot" "\<And>x. f' x top = top"
  assumes A: "\<And>a x x'. x\<le>x' \<Longrightarrow> f a x \<le> f' a x'"
  shows "foldli l (case_dres False False c) f \<sigma> 
    \<le> foldli l (case_dres False False c) f' \<sigma>"
  apply (rule foldli_mono_dres_aux1)
  apply (simp_all split: dres.split_asm add: STRICT A)
  done

lemma foldli_mono_dres[refine_mono]:
  assumes A: "\<And>a x. f a x \<le> f' a x"
  shows "foldli l (case_dres False False c) (\<lambda>x s. dbind s (f x)) \<sigma> 
    \<le> foldli l (case_dres False False c) (\<lambda>x s. dbind s (f' x)) \<sigma>"
  apply (rule foldli_mono_dres_aux2)
  apply (simp_all)
  apply (rule dbind_mono)
  apply (simp_all add: A)
  done


partial_function (drec) dfoldli where
  "dfoldli l c f s = (case l of 
    [] \<Rightarrow> dRETURN s 
    | x#ls \<Rightarrow> if c s then do { s\<leftarrow>f x s; dfoldli ls c f s} else dRETURN s
  )"

lemma dfoldli_simps[simp]:
  "dfoldli [] c f s = dRETURN s"
  "dfoldli (x#ls) c f s = 
    (if c s then do { s\<leftarrow>f x s; dfoldli ls c f s} else dRETURN s)"
  apply (subst dfoldli.simps, simp)+
  done
  
lemma dfoldli_mono[refine_mono]: 
  "\<lbrakk> \<And>x s. f x s \<le> f' x s \<rbrakk> \<Longrightarrow> dfoldli l c f \<sigma> \<le> dfoldli l c f' \<sigma>"
  "\<lbrakk> \<And>x s. flat_ge (f x s) (f' x s) \<rbrakk> \<Longrightarrow> flat_ge (dfoldli l c f \<sigma>) (dfoldli l c f' \<sigma>)"
  apply (induct l arbitrary: \<sigma>)
  apply auto
  apply refine_mono

  apply (induct l arbitrary: \<sigma>)
  apply auto
  apply refine_mono
  done

lemma foldli_dres_pres_FAIL[simp]: 
  "foldli l (case_dres False False c) (\<lambda>x s. dbind s (f x)) dFAIL = dFAIL"
  by (cases l) auto

lemma foldli_dres_pres_SUCCEED[simp]:
  "foldli l (case_dres False False c) (\<lambda>x s. dbind s (f x)) dSUCCEED = dSUCCEED"
  by (cases l) auto

lemma dfoldli_by_foldli: "dfoldli l c f \<sigma>
  = foldli l (case_dres False False c) (\<lambda>x s. dbind s (f x)) (dRETURN \<sigma>)"
  apply (induction l arbitrary: \<sigma>)
  apply simp
  apply (clarsimp intro!: ext)
  apply (rename_tac a l x)
  apply (case_tac "f a x")
  apply auto
  done

lemma foldli_mono_dres_flat[refine_mono]:
  assumes A: "\<And>a x. flat_ge (f a x) (f' a x)"
  shows "flat_ge (foldli l (case_dres False False c) (\<lambda>x s. dbind s (f x)) \<sigma>) 
          (foldli l (case_dres False False c) (\<lambda>x s. dbind s (f' x)) \<sigma>)"
  apply (cases \<sigma>)
  apply (simp_all add: dfoldli_by_foldli[symmetric])
  using A apply refine_mono
  done

lemma dres_foldli_ne_bot[refine_transfer]:
  assumes 1: "\<sigma> \<noteq> dSUCCEED"
  assumes 2: "\<And>x \<sigma>. f x \<sigma> \<noteq> dSUCCEED"
  shows "foldli l c (\<lambda>x s. s \<bind> f x) \<sigma> \<noteq> dSUCCEED"
  using 1 apply (induct l arbitrary: \<sigma>)
  apply simp
  apply (simp split: dres.split, intro allI impI)
  apply rprems
  using 2
  apply (simp add: dres_ne_bot_basic)
  done

subsection \<open>LIST FOREACH combinator\<close>
text \<open>
  Foreach-loops are mapped to the combinator \<open>LIST_FOREACH\<close>, that
  takes as first argument an explicit \<open>to_list\<close> operation. 
  This mapping is done during operation identification. 
  It is then the responsibility of the various implementations to further map
  the \<open>to_list\<close> operations to custom \<open>to_list\<close> operations, like
  \<open>set_to_list\<close>, \<open>map_to_list\<close>, \<open>nodes_to_list\<close>, etc.
\<close>

  
text \<open>We define a relation between distinct lists and sets.\<close>  
definition [to_relAPP]: "list_set_rel R \<equiv> \<langle>R\<rangle>list_rel O br set distinct"
  
  
lemma autoref_nfoldli[autoref_rules]:
  shows "(nfoldli, nfoldli)
  \<in> \<langle>Ra\<rangle>list_rel \<rightarrow> (Rb \<rightarrow> bool_rel) \<rightarrow> (Ra \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel) \<rightarrow> Rb \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  by (rule param_nfoldli)

text \<open>This constant is a placeholder to be converted to
  custom operations by pattern rules\<close>
definition "it_to_sorted_list R s 
  \<equiv> SPEC (\<lambda>l. distinct l \<and> s = set l \<and> sorted_wrt R l)"

definition "LIST_FOREACH \<Phi> tsl c f \<sigma>0 \<equiv> do {
  xs \<leftarrow> tsl;
  (_,\<sigma>) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(it, \<sigma>). \<exists>xs'. xs = xs' @ it \<and> \<Phi> (set it) \<sigma>\<^esup>
    (FOREACH_cond c) (FOREACH_body f) (xs, \<sigma>0);
    RETURN \<sigma>}"

lemma FOREACHoci_by_LIST_FOREACH:
  "FOREACHoci R \<Phi> S c f \<sigma>0 = do {
    ASSERT (finite S);
    LIST_FOREACH \<Phi> (it_to_sorted_list R S) c f \<sigma>0
  }"
  unfolding OP_def FOREACHoci_def LIST_FOREACH_def it_to_sorted_list_def 
  by simp

text \<open>Patterns that convert FOREACH-constructs 
  to \<open>LIST_FOREACH\<close>
\<close>
context begin interpretation autoref_syn .

lemma FOREACH_patterns[autoref_op_pat_def]:
  "FOREACH\<^bsup>I\<^esup> s f \<equiv> FOREACH\<^sub>O\<^sub>C\<^bsup>\<lambda>_ _. True,I\<^esup> s (\<lambda>_. True) f"
  "FOREACHci I s c f \<equiv> FOREACHoci (\<lambda>_ _. True) I s c f"
  "FOREACH\<^sub>O\<^sub>C\<^bsup>R,\<Phi>\<^esup> s c f \<equiv> \<lambda>\<sigma>. do {
    ASSERT (finite s);
    Autoref_Tagging.OP (LIST_FOREACH \<Phi>) (it_to_sorted_list R s) c f \<sigma>
  }"
  "FOREACH s f \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s (\<lambda>_. True) f"
  "FOREACHoi R I s f \<equiv> FOREACHoci R I s (\<lambda>_. True) f"
  "FOREACHc s c f \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s c f"
  unfolding 
    FOREACHoci_by_LIST_FOREACH[abs_def]
    FOREACHc_def[abs_def] 
    FOREACH_def[abs_def] 
    FOREACHci_def[abs_def] 
    FOREACHi_def[abs_def] 
    FOREACHoi_def[abs_def] 
  by simp_all

(*lemma FOREACH_patterns[autoref_op_pat]: 
  "FOREACHoci R \<Phi> s c f \<sigma> \<equiv> do {
    ASSERT (finite s);
    OP (LIST_FOREACH \<Phi>) (it_to_sorted_list R s) c f \<sigma>
  }"
  "FOREACHc s c f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s c f \<sigma>"
  "FOREACH s f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) (\<lambda>_ _. True) s (\<lambda>_. True) f \<sigma>"
  "FOREACHci I s c f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) I s c f \<sigma>"
  "FOREACHi I s f \<sigma> \<equiv> FOREACHoci (\<lambda>_ _. True) I s (\<lambda>_. True) f \<sigma>"
  "FOREACHoi R I s f \<sigma> \<equiv> FOREACHoci R I s (\<lambda>_. True) f \<sigma>"
  unfolding 
    FOREACHoci_by_LIST_FOREACH[abs_def]
    FOREACHc_def[abs_def] 
    FOREACH_def[abs_def] 
    FOREACHci_def[abs_def] 
    FOREACHi_def[abs_def] 
    FOREACHoi_def[abs_def] 
  by simp_all*)
end
definition "LIST_FOREACH' tsl c f \<sigma> \<equiv> do {xs \<leftarrow> tsl; nfoldli xs c f \<sigma>}"

lemma LIST_FOREACH'_param[param]: 
  shows "(LIST_FOREACH',LIST_FOREACH') 
  \<in> (\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel \<rightarrow> (R\<sigma>\<rightarrow>bool_rel) 
    \<rightarrow> (Rv \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel)"
  unfolding LIST_FOREACH'_def[abs_def]
  by parametricity

lemma LIST_FOREACH_autoref[autoref_rules]:
  shows "(LIST_FOREACH', LIST_FOREACH \<Phi>) \<in> 
    (\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel \<rightarrow> (R\<sigma>\<rightarrow>bool_rel) 
      \<rightarrow> (Rv \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel) \<rightarrow> R\<sigma> \<rightarrow> \<langle>R\<sigma>\<rangle>nres_rel)"
proof (intro fun_relI nres_relI)
  fix tsl tsl' c c' f f' \<sigma> \<sigma>'
  assume [param]:
    "(tsl,tsl')\<in>\<langle>\<langle>Rv\<rangle>list_rel\<rangle>nres_rel"
    "(c,c')\<in>R\<sigma>\<rightarrow>bool_rel" 
    "(f,f')\<in>Rv\<rightarrow>R\<sigma>\<rightarrow>\<langle>R\<sigma>\<rangle>nres_rel"
    "(\<sigma>,\<sigma>')\<in>R\<sigma>"

  have "LIST_FOREACH' tsl c f \<sigma> \<le> \<Down>R\<sigma> (LIST_FOREACH' tsl' c' f' \<sigma>')"
    apply (rule nres_relD)
    by parametricity
  also have "LIST_FOREACH' tsl' c' f' \<sigma>'
    \<le> LIST_FOREACH \<Phi> tsl' c' f' \<sigma>'"
    apply (rule refine_IdD)
    unfolding LIST_FOREACH_def LIST_FOREACH'_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done 
  finally show 
    "LIST_FOREACH' tsl c f \<sigma> \<le> \<Down> R\<sigma> (LIST_FOREACH \<Phi> tsl' c' f' \<sigma>')"
    .
qed

context begin interpretation trimono_spec .

lemma LIST_FOREACH'_mono[unfolded trimono_spec_defs,refine_mono]: 
  "trimono_spec (R o R o M2 o R) LIST_FOREACH'"
  apply (unfold trimono_spec_defs)
  apply -
  unfolding LIST_FOREACH'_def
  by refine_mono+

end

lemma LIST_FOREACH'_transfer_plain[refine_transfer]:
  assumes "RETURN tsl \<le> tsl'"
  assumes "\<And>x \<sigma>. RETURN (f x \<sigma>) \<le> f' x \<sigma>"
  shows "RETURN (foldli tsl c f \<sigma>) \<le> LIST_FOREACH' tsl' c f' \<sigma>"
  apply (rule order_trans[rotated])
  unfolding LIST_FOREACH'_def
  using assms
  apply refine_transfer
  by simp

thm refine_transfer

lemma LIST_FOREACH'_transfer_nres[refine_transfer]:
  assumes "nres_of tsl \<le> tsl'"
  assumes "\<And>x \<sigma>. nres_of (f x \<sigma>) \<le> f' x \<sigma>"
  shows "nres_of (
    do {
      xs\<leftarrow>tsl; 
      foldli xs (case_dres False False c) (\<lambda>x s. s\<bind>f x) (dRETURN \<sigma>)
    }) \<le> LIST_FOREACH' tsl' c f' \<sigma>"
  unfolding LIST_FOREACH'_def
  using assms
  by refine_transfer

text \<open>Simplification rules to summarize iterators\<close>
lemma [refine_transfer_post_simp]: 
  "do {
    xs \<leftarrow> dRETURN tsl;
    foldli xs c f \<sigma>
  } = foldli tsl c f \<sigma>" 
  by simp

lemma [refine_transfer_post_simp]: 
  "(let xs = tsl in foldli xs c f \<sigma>) = foldli tsl c f \<sigma>" 
  by simp

    
lemma LFO_pre_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "(ci,c)\<in>R \<rightarrow> bool_rel"
  assumes "(fi,f)\<in>A\<rightarrow>R\<rightarrow>\<langle>R\<rangle>nres_rel"
  assumes "(s0i,s0)\<in>R"
  shows "LIST_FOREACH' (RETURN li) ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
proof -
  from assms(1) have [simp]: "finite l" by (auto simp: list_set_rel_def br_def)
  show ?thesis
    unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH
    apply simp
    apply (rule LIST_FOREACH_autoref[param_fo, THEN nres_relD])
    using assms
    apply auto
    apply (auto simp: it_to_sorted_list_def nres_rel_def pw_le_iff refine_pw_simps
      list_set_rel_def br_def)
    done
qed    
    

lemma LFOci_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
  assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes "(s0i,s0)\<in>R"
  shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHci I l c f s0)"
proof -
  from assms LFO_pre_refine[of li l A ci c R fi f s0i s0] show ?thesis
    unfolding fun_rel_def nres_rel_def LIST_FOREACH'_def
    apply (simp add: pw_le_iff refine_pw_simps)
    apply blast+
    done
qed    

lemma LFOc_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "\<And>s si. (si,s)\<in>R \<Longrightarrow> ci si \<longleftrightarrow> c s"
  assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes "(s0i,s0)\<in>R"
  shows "nfoldli li ci fi s0i \<le> \<Down>R (FOREACHc l c f s0)"
  unfolding FOREACHc_def
  by (rule LFOci_refine[OF assms])

  
lemma LFO_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes "(s0i,s0)\<in>R"
  shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACH l f s0)"
  unfolding FOREACH_def
  apply (rule LFOc_refine)
  apply (rule assms | simp)+
  done

lemma LFOi_refine: (* TODO: Generalize! *)
  assumes "(li,l)\<in>\<langle>A\<rangle>list_set_rel"
  assumes "\<And>x xi s si. \<lbrakk>(xi,x)\<in>A; (si,s)\<in>R\<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>R (f x s)"
  assumes "(s0i,s0)\<in>R"
  shows "nfoldli li (\<lambda>_. True) fi s0i \<le> \<Down>R (FOREACHi I l f s0)"
  unfolding FOREACHi_def
  apply (rule LFOci_refine)
  apply (rule assms | simp)+
  done
    
lemma LIST_FOREACH'_refine: "LIST_FOREACH' tsl' c' f' \<sigma>' \<le> LIST_FOREACH \<Phi> tsl' c' f' \<sigma>'"
  apply (rule refine_IdD)
  unfolding LIST_FOREACH_def LIST_FOREACH'_def
  apply refine_rcg
  apply simp
  apply (rule nfoldli_while)
  done

lemma LIST_FOREACH'_eq: "LIST_FOREACH (\<lambda>_ _. True) tsl' c' f' \<sigma>' = (LIST_FOREACH' tsl' c' f' \<sigma>')"
  apply (rule antisym)
  subgoal
    apply (rule refine_IdD)
    unfolding LIST_FOREACH_def LIST_FOREACH'_def while_eq_nfoldli[symmetric] 
    apply (refine_rcg WHILEIT_refine_new_invar)
    unfolding WHILET_def
    apply (rule WHILEIT_refine_new_invar)

    apply refine_dref_type
    apply clarsimp_all
    unfolding FOREACH_body_def FOREACH_cond_def
    apply refine_vcg
    apply (auto simp: refine_pw_simps pw_le_iff neq_Nil_conv)
    done
  subgoal by (rule LIST_FOREACH'_refine)
  done
    
    
subsection \<open>FOREACH with duplicates\<close>

definition "FOREACHcd S c f \<sigma> \<equiv> do {
  ASSERT (finite S);
  l \<leftarrow> SPEC (\<lambda>l. set l = S);
  nfoldli l c f \<sigma>
}"

lemma FOREACHcd_rule:
  assumes "finite S\<^sub>0"
  assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
  assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
  assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
  assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
  shows "FOREACHcd S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
  unfolding FOREACHcd_def
  apply refine_vcg
  apply fact
  apply (rule nfoldli_rule[where I = "\<lambda>l1 l2 \<sigma>. I (set l1) (set l2) \<sigma>"])
  subgoal using I0 by auto
  subgoal using STEP by auto
  subgoal using INTR by auto
  subgoal using COMPL by auto
  done

definition FOREACHcdi 
  :: "('a set \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> bool) 
    \<Rightarrow> 'a set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b nres) \<Rightarrow> 'b \<Rightarrow> 'b nres"
  where
  "FOREACHcdi I \<equiv> FOREACHcd"  

lemma FOREACHcdi_rule[refine_vcg]:
  assumes "finite S\<^sub>0"
  assumes I0: "I {} S\<^sub>0 \<sigma>\<^sub>0"
  assumes STEP: "\<And>S1 S2 x \<sigma>. \<lbrakk> S\<^sub>0 = insert x (S1\<union>S2); I S1 (insert x S2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> SPEC (I (insert x S1) S2)"
  assumes INTR: "\<And>S1 S2 \<sigma>. \<lbrakk> S\<^sub>0 = S1\<union>S2; I S1 S2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
  assumes COMPL: "\<And>\<sigma>. \<lbrakk> I S\<^sub>0 {} \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> \<Phi> \<sigma>"
  shows "FOREACHcdi I S\<^sub>0 c f \<sigma>\<^sub>0 \<le> SPEC \<Phi>"
  unfolding FOREACHcdi_def
  using assms
  by (rule FOREACHcd_rule)

lemma FOREACHcd_refine[refine]:
  assumes [simp]: "finite s'"
  assumes S: "(s',s)\<in>\<langle>S\<rangle>set_rel"
  assumes SV: "single_valued S"
  assumes R0: "(\<sigma>',\<sigma>)\<in>R"
  assumes C: "\<And>\<sigma>' \<sigma>. (\<sigma>',\<sigma>)\<in>R \<Longrightarrow> (c' \<sigma>', c \<sigma>)\<in>bool_rel"
  assumes F: "\<And>x' x \<sigma>' \<sigma>. \<lbrakk>(x', x) \<in> S; (\<sigma>', \<sigma>) \<in> R\<rbrakk>
     \<Longrightarrow> f' x' \<sigma>' \<le> \<Down> R (f x \<sigma>)"
  shows "FOREACHcd s' c' f' \<sigma>' \<le> \<Down>R (FOREACHcdi I s c f \<sigma>)"
proof -
  have [refine_dref_RELATES]: "RELATES S" by (simp add: RELATES_def)

  from SV obtain \<alpha> I where [simp]: "S=br \<alpha> I" by (rule single_valued_as_brE)
  with S have [simp]: "s=\<alpha>`s'" and [simp]: "\<forall>x\<in>s'. I x" 
    by (auto simp: br_set_rel_alt)
  
  show ?thesis
    unfolding FOREACHcd_def FOREACHcdi_def
    apply refine_rcg
    apply refine_dref_type
    subgoal by simp
    subgoal
      apply (auto simp: pw_le_iff refine_pw_simps)
      using S
      apply (rule_tac x="map \<alpha> x" in exI)
      apply (auto simp: map_in_list_rel_conv)
      done
    subgoal using R0 by auto
    subgoal using C by auto  
    subgoal using F by auto
    done
qed    
    

  
lemma FOREACHc_refines_FOREACHcd_aux:
  shows "FOREACHc s c f \<sigma> \<le> FOREACHcd s c f \<sigma>"
  unfolding FOREACHc_def FOREACHci_def FOREACHoci_by_LIST_FOREACH LIST_FOREACH'_eq
    LIST_FOREACH'_def FOREACHcd_def it_to_sorted_list_def
  apply (rule refine_IdD)  
  apply (refine_rcg)
  apply refine_dref_type
  apply auto
  done
    
lemmas FOREACHc_refines_FOREACHcd[refine]
  = order_trans[OF FOREACHc_refines_FOREACHcd_aux FOREACHcd_refine]
    
    
subsection \<open>Miscellanneous Utility Lemmas\<close>

(* TODO: Can we make this somewhat more general ? *)
lemma map_foreach:
  assumes "finite S"
  shows "FOREACH S (\<lambda>x \<sigma>. RETURN (insert (f x) \<sigma>)) R0 \<le> SPEC ((=) (R0 \<union> f`S))"
  apply (rule FOREACH_rule[where I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(S-it)"])
  apply (auto intro: assms)
  done

lemma map_sigma_foreach:
  fixes f :: "'a \<times> 'b \<Rightarrow> 'c"
  assumes "finite A"
  assumes "\<And>x. x\<in>A \<Longrightarrow> finite (B x)"
  shows "FOREACH A (\<lambda>a \<sigma>. 
    FOREACH (B a) (\<lambda>b \<sigma>. RETURN (insert (f (a,b)) \<sigma>)) \<sigma>
  ) R0 \<le> SPEC ((=) (R0 \<union> f`Sigma A B))"
  apply (rule FOREACH_rule[where I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A-it) B)"])
  apply (auto intro: assms) [2]
  
  apply (rule_tac I="\<lambda>it' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) B) 
    \<union> f`({x} \<times> (B x - it'))"
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  apply (rule refine_vcg)
  apply auto []
  apply auto []
  apply auto []
  done

lemma map_sigma_sigma_foreach:
  fixes f :: "'a \<times> ('b \<times> 'c) \<Rightarrow> 'd"
  assumes "finite A"
  assumes "\<And>a. a\<in>A \<Longrightarrow> finite (B a)"
  assumes "\<And>a b. \<lbrakk>a\<in>A; b\<in>B a\<rbrakk> \<Longrightarrow> finite (C a b)"
  shows "FOREACH A (\<lambda>a \<sigma>. 
    FOREACH (B a) (\<lambda>b \<sigma>. 
      FOREACH (C a b) (\<lambda>c \<sigma>.
        RETURN (insert (f (a,(b,c))) \<sigma>)) \<sigma>) \<sigma>
  ) R0 \<le> SPEC ((=) (R0 \<union> f`Sigma A (\<lambda>a. Sigma (B a) (C a))))"
  apply (rule FOREACH_rule[where 
    I="\<lambda>it \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A-it) (\<lambda>a. Sigma (B a) (C a)))"])
  apply (auto intro: assms) [2]
  apply (rule_tac 
    I="\<lambda>it' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) (\<lambda>a. Sigma (B a) (C a))) 
      \<union> f`({x} \<times> ( Sigma (B x - it') (C x)))"
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  apply (rule_tac 
    I="\<lambda>it'' \<sigma>. \<sigma>=R0 \<union> f`(Sigma (A - it) (\<lambda>a. Sigma (B a) (C a))) 
      \<union> f`({x} \<times> ( Sigma (B x - ita) (C x)))
      \<union> f`({x} \<times> ({xa} \<times> (C x xa - it'')))
    "
    in FOREACH_rule)
  apply (auto intro: assms) [2]
  
  apply auto
  done


lemma bij_set_rel_for_inj: 
  fixes R
  defines "\<alpha> \<equiv> fun_of_rel R" 
  assumes "bijective R" "(s,s')\<in>\<langle>R\<rangle>set_rel"  
  shows "inj_on \<alpha> s" "s' = \<alpha>`s"
  \<comment> \<open>To be used when generating refinement conditions for foreach-loops\<close>
  using assms
  unfolding bijective_def set_rel_def \<alpha>_def fun_of_rel_def[abs_def]
  apply (auto intro!: inj_onI ImageI simp: image_def)
  apply (metis (mono_tags) Domain.simps contra_subsetD tfl_some)
  apply (metis (mono_tags) someI)
  apply (metis DomainE contra_subsetD tfl_some)
  done

lemma nfoldli_by_idx_gen:
  shows "nfoldli (drop k l) c f s = nfoldli [k..<length l] c (\<lambda>i s. do {
      ASSERT (i<length l);
      let x = l!i;
      f x s
    }) s"
proof (cases "k\<le>length l")
  case False thus ?thesis by auto
next
  case True thus ?thesis 
  proof (induction arbitrary: s rule: inc_induct)
    case base thus ?case
      by auto
  next    
    case (step k) 
    from step.hyps have 1: "drop k l = l!k # drop (Suc k) l" 
      by (auto simp: Cons_nth_drop_Suc)
    from step.hyps have 2: "[k..<length l] = k#[Suc k..<length l]" 
      by (auto simp: upt_conv_Cons)

    show ?case
      unfolding 1 2
      by (auto simp: step.IH[abs_def] step.hyps) 
  qed
qed
  


lemma nfoldli_by_idx: 
  "nfoldli l c f s = nfoldli [0..<length l] c (\<lambda>i s. do {
    ASSERT (i<length l);
    let x = l!i;
    f x s
  }) s"
  using nfoldli_by_idx_gen[of 0] by auto

lemma nfoldli_map_inv:
  assumes "inj g"
  shows "nfoldli l c f = nfoldli (map g l) c (\<lambda>x s. f (the_inv g x) s)"
  using assms
  apply (induction l)
  subgoal by auto
  subgoal by (auto simp: the_inv_f_f)
  done
    
lemma nfoldli_shift:
  fixes ofs :: nat 
  shows "nfoldli l c f = nfoldli (map (\<lambda>i. i+ofs) l) c (\<lambda>x s. do {ASSERT (x\<ge>ofs); f (x - ofs) s})" 
  by (induction l) auto
  
lemma nfoldli_foreach_shift: 
  shows "nfoldli [a..<b] c f = nfoldli [a+ofs..<b+ofs] c (\<lambda>x s. do{ASSERT(x\<ge>ofs); f (x - ofs) s})"
  using nfoldli_shift[of "[a..<b]" c f ofs] 
  by (auto simp: map_add_upt')


(* TODO: Move. Probably we have this already with FOREACH, or iterator! *)
lemma member_by_nfoldli: "nfoldli l (\<lambda>f. \<not>f) (\<lambda>y _. RETURN (y=x)) False \<le> SPEC (\<lambda>r. r \<longleftrightarrow> x\<in>set l)"
proof -
  have "nfoldli l (\<lambda>f. \<not>f) (\<lambda>y _. RETURN (y=x)) s \<le> SPEC (\<lambda>r. r \<longleftrightarrow> s \<or> x\<in>set l)" for s
    apply (induction l arbitrary: s)
    subgoal by auto
    subgoal for a l s
      apply clarsimp
      apply (rule order_trans)
      apply rprems
      by auto
    done
  from this[of False] show ?thesis by auto
qed  

  
definition sum_impl :: "('a \<Rightarrow> 'b::comm_monoid_add nres) \<Rightarrow> 'a set \<Rightarrow> 'b nres" where
  "sum_impl g S \<equiv> FOREACH S (\<lambda>x a. do { b \<leftarrow> g x; RETURN (a+b)}) 0"

lemma sum_impl_correct: 
  assumes [simp]: "finite S"
  assumes [refine_vcg]: "\<And>x. x\<in>S \<Longrightarrow> gi x \<le> SPEC (\<lambda>r. r=g x)"
  shows "sum_impl gi S \<le> SPEC (\<lambda>r. r=sum g S)"
  unfolding sum_impl_def
  apply (refine_vcg FOREACH_rule[where I="\<lambda>it a. a = sum g (S - it)"])
  apply (auto simp: it_step_insert_iff algebra_simps)
  done
  

end
