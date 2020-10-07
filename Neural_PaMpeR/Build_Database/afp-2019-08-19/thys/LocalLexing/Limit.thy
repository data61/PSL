theory Limit
imports LocalLexing
begin

definition setmonotone :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "setmonotone f = (\<forall> X. X \<subseteq> f X)"

lemma setmonotone_funpower: "setmonotone f \<Longrightarrow> setmonotone (funpower f n)"
  by (induct n, auto simp add: setmonotone_def)

lemma subset_setmonotone: "setmonotone f \<Longrightarrow> X \<subseteq> f X"
  by (simp add: setmonotone_def)

lemma elem_setmonotone: "setmonotone f \<Longrightarrow> x \<in> X \<Longrightarrow> x \<in> f X"
  by (auto simp add: setmonotone_def)

lemma elem_natUnion: "(\<forall> n. x \<in> f n) \<Longrightarrow> x \<in> natUnion f"
  by (auto simp add: natUnion_def)

lemma subset_natUnion: "(\<forall> n. X \<subseteq> f n) \<Longrightarrow> X \<subseteq> natUnion f"
  by (auto simp add: natUnion_def)
  
lemma setmonotone_limit:
  assumes fmono: "setmonotone f"
  shows "setmonotone (limit f)"
proof -
  show "setmonotone (limit f)" 
    apply (auto simp add: setmonotone_def limit_def)
    apply (rule elem_natUnion, auto)
    apply (rule elem_setmonotone[OF setmonotone_funpower])
    by (auto simp add: fmono)
qed

lemma[simp]: "funpower id n = id"
  by (rule ext, induct n, simp_all)

lemma[simp]: "limit id = id"
  by (rule ext, auto simp add: limit_def natUnion_def)

lemma natUnion_decompose[consumes 1, case_names Decompose]:
  assumes p: "p \<in> natUnion S"
  assumes decompose: "\<And> n p. p \<in> S n \<Longrightarrow> P p" 
  shows "P p" 
proof -
  from p have "\<exists> n. p \<in> S n" 
    by (auto simp add: natUnion_def)
  then obtain n where "p \<in> S n" by blast
  from decompose[OF this] show ?thesis .
qed

lemma limit_induct[consumes 1, case_names Init Iterate]:
  assumes p: "(p :: 'a) \<in> limit f X"
  assumes init: "\<And> p. p \<in> X \<Longrightarrow> P p"
  assumes iterate: "\<And> p Y. (\<And> q . q \<in> Y \<Longrightarrow> P q) \<Longrightarrow> p \<in> f Y \<Longrightarrow> P p"
  shows "P p"
proof -
  from p have p_in_natUnion: "p \<in> natUnion (\<lambda> n. funpower f n X)"    
    by (simp add: limit_def)
  {
    fix p :: 'a
    fix n :: nat
    have "p \<in> funpower f n X \<Longrightarrow> P p"
    proof (induct n arbitrary: p) 
      case 0 thus ?case using init[OF 0[simplified]] by simp
    next
      case (Suc n) show ?case 
        using iterate[OF Suc(1) Suc(2)[simplified], simplified] by simp
    qed
  }
  with p_in_natUnion show ?thesis
    by (induct rule: natUnion_decompose)
qed

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "chain C = (\<forall> i. C i \<subseteq> C (i + 1))"

definition continuous :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool"
where
  "continuous f = (\<forall> C. chain C \<longrightarrow> (chain (f o C) \<and> f (natUnion C) = natUnion (f o C)))"

lemma continuous_apply:
  "continuous f \<Longrightarrow> chain C \<Longrightarrow> f (natUnion C) = natUnion (f o C)"
by (simp add: continuous_def)

lemma continuous_imp_mono:
  assumes continuous: "continuous f"
  shows "mono f"
proof -
  { 
    fix A :: "'a set"
    fix B :: "'a set"
    assume sub: "A \<subseteq> B"
    let ?C = "\<lambda> (i::nat). if (i = 0) then A else B"
    have "chain ?C" by (simp add: chain_def sub) 
    then have fC: "chain (f o ?C)" using continuous continuous_def by blast
    then have "f (?C 0) \<subseteq> f (?C (0 + 1))"
    proof -
      have "\<And>f n. \<not> chain f \<or> (f n::'b set) \<subseteq> f (Suc n)"
        by (metis Suc_eq_plus1 chain_def)
      then show ?thesis using fC by fastforce
    qed
    then have "f A \<subseteq> f B" by auto
  }
  then show "mono f" by (simp add: monoI)
qed 
      
lemma mono_maps_chain_to_chain: 
  assumes f: "mono f"
  assumes C: "chain C"
  shows "chain (f o C)"
by (metis C comp_def f chain_def mono_def)

lemma natUnion_upperbound: 
  "(\<And> n. f n \<subseteq> G) \<Longrightarrow> (natUnion f) \<subseteq> G"
by (auto simp add: natUnion_def)

lemma funpower_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> funpower f n I \<subseteq> G"
proof (induct n)
  case 0 thus ?case by simp
next
  case (Suc n) thus ?case by simp
qed

lemma limit_upperbound:
  "(\<And> I. I \<subseteq> G \<Longrightarrow> f I \<subseteq> G) \<Longrightarrow> I \<subseteq> G \<Longrightarrow> limit f I \<subseteq> G"
by (simp add: funpower_upperbound limit_def natUnion_upperbound)

lemma elem_limit_simp: "x \<in> limit f X = (\<exists> n. x \<in> funpower f n X)"
by (auto simp add: limit_def natUnion_def)

definition pointwise :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointwise f = (\<forall> X. f X = \<Union> { f {x} | x. x \<in> X})" 

lemma pointwise_simp: 
  assumes f: "pointwise f"
  shows "f X =  \<Union> { f {x} | x. x \<in> X}"
proof -
  from f have "\<forall> X. f X = \<Union> { f {x} | x. x \<in> X}"
    by (rule iffD1[OF pointwise_def[where f=f]])
  then show ?thesis by blast
qed

lemma natUnion_elem: "x \<in> f n \<Longrightarrow> x \<in> natUnion f"
using natUnion_def by fastforce
  
lemma limit_elem: "x \<in> funpower f n X \<Longrightarrow> x \<in> limit f X"
by (simp add: limit_def natUnion_elem)

lemma limit_step_pointwise:
  assumes x: "x \<in> limit f X"
  assumes f: "pointwise f"
  assumes y: "y \<in> f {x}"
  shows "y \<in> limit f X"
proof - 
  from x have "\<exists> n. x \<in> funpower f n X" 
    by (simp add: elem_limit_simp)
  then obtain n where n: "x \<in> funpower f n X" by blast
  have "y \<in> funpower f (Suc n) X"
    apply simp 
    apply (subst pointwise_simp[OF f])
    using y n by auto
  then show "y \<in> limit f X" by (meson limit_elem)
qed

definition pointbase :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
  "pointbase F I = \<Union> { F X | X. finite X \<and> X \<subseteq> I }"

definition pointbased :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
  "pointbased f = (\<exists> F. f = pointbase F)"

lemma pointwise_implies_pointbased:
  assumes pointwise: "pointwise f"
  shows "pointbased f"
proof -
  let ?F = "\<lambda> X. f X"
  {
    fix I :: "'a set"
    fix x :: "'b"
    have lr: "x \<in> pointbase ?F I \<Longrightarrow> x \<in> f I"
    proof -
      assume x: "x \<in> pointbase ?F I"
      have "\<exists> X. x \<in> f X \<and> X \<subseteq> I"
        proof -
          have "x \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> I}"
            by (metis pointbase_def x)
          then show ?thesis
            by blast
        qed
      then obtain X where X:"x \<in> f X \<and> X \<subseteq> I" by blast
      have "\<exists> y. y \<in> I \<and> x \<in> f {y}"
        using X apply (simp add: pointwise_simp[OF pointwise, where X=X])
        by blast
      then show "x \<in> f I"
        apply (simp add: pointwise_simp[OF pointwise, where X=I])
        by blast
    qed
    have rl: "x \<in> f I \<Longrightarrow> x \<in> pointbase ?F I"
    proof -
      assume x: "x \<in> f I"
      have "\<exists> y. y \<in> I \<and> x \<in> f {y}"
        using x apply (simp add: pointwise_simp[OF pointwise, where X=I])
        by blast
      then obtain y where "y \<in> I \<and> x \<in> f {y}" by blast
      then have "\<exists> X. x \<in> f X \<and> finite X \<and> X \<subseteq> I" by blast
      then show "x \<in> pointbase f I"
        apply (simp add: pointbase_def)
        by blast
    qed
    note lr rl
  }
  then have "\<And> I. pointbase f I = f I" by blast
  then have "pointbase f = f" by blast
  then show ?thesis by (metis pointbased_def) 
qed  
   
lemma pointbase_is_mono:
  "mono (pointbase f)"
proof -
  {
    fix A :: "'a set"
    fix B :: "'a set"
    assume subset: "A \<subseteq> B"
    have "(pointbase f) A \<subseteq> (pointbase f) B" 
      apply (simp add: pointbase_def)
      using subset by fastforce
  }
  then show ?thesis by (simp add: mono_def)
qed

lemma chain_implies_mono: "chain C \<Longrightarrow> mono C"
by (simp add: chain_def mono_iff_le_Suc)

lemma chain_cover_witness: "finite X \<Longrightarrow> chain C \<Longrightarrow> X \<subseteq> natUnion C \<Longrightarrow> \<exists> n. X \<subseteq> C n"
proof (induct rule: finite.induct)
  case emptyI thus ?case by blast
next
  case (insertI X x) 
  then have "X \<subseteq> natUnion C" by simp
  with insertI have "\<exists> n. X \<subseteq> C n" by blast
  then obtain n where n: "X \<subseteq> C n" by blast
  have x: "x \<in> natUnion C" using insertI.prems(2) by blast
  then have "\<exists> m. x \<in> C m"
  proof -
    have "x \<in> \<Union>{A. \<exists>n. A = C n}" by (metis x natUnion_def)
    then show ?thesis by blast
  qed
  then obtain m where m: "x \<in> C m" by blast
  have mono_C: "\<And> i j. i \<le> j \<Longrightarrow> C i \<subseteq> C j"
    using chain_implies_mono insertI(3) mono_def by blast 
  show ?case
    apply (rule_tac x="max n m" in exI)
    apply auto
    apply (meson contra_subsetD m max.cobounded2 mono_C)
    by (metis max_def mono_C n subsetCE)
qed
    
lemma pointbase_is_continuous:
  "continuous (pointbase f)"
proof -
  {
    fix C :: "nat \<Rightarrow> 'a set"
    assume C: "chain C"
    have mono: "chain ((pointbase f) o C)"
      by (simp add: C mono_maps_chain_to_chain pointbase_is_mono)
    have subset1: "natUnion ((pointbase f) o C) \<subseteq> (pointbase f) (natUnion C)"
    proof (auto)
      fix y :: "'b"
      assume "y \<in> natUnion ((pointbase f) o C)"
      then show "y \<in> (pointbase f) (natUnion C)"
      proof (induct rule: natUnion_decompose)
        case (Decompose n p)
          thus ?case by (metis comp_apply contra_subsetD mono_def natUnion_elem 
            pointbase_is_mono subsetI) 
      qed
    qed
    have subset2: "(pointbase f) (natUnion C) \<subseteq> natUnion ((pointbase f) o C)"
    proof (auto)
      fix y :: "'b"
      assume y: "y \<in> (pointbase f) (natUnion C)"
      have "\<exists> X. finite X \<and> X \<subseteq> natUnion C \<and> y \<in> f X"
      proof -
        have "y \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> natUnion C}"
          by (metis y pointbase_def)
        then show ?thesis by blast
      qed
      then obtain X where X: "finite X \<and> X \<subseteq> natUnion C \<and> y \<in> f X" by blast
      then have "\<exists> n. X \<subseteq> C n" using chain_cover_witness C by blast
      then obtain n where X_sub_C: "X \<subseteq> C n" by blast
      show "y \<in> natUnion ((pointbase f) o C)" 
        apply (rule_tac natUnion_elem[where n=n])
        proof -
          have "y \<in> \<Union>{f A |A. finite A \<and> A \<subseteq> C n}"
          using X X_sub_C by blast
          then show "y \<in> (pointbase f \<circ> C) n" by (simp add: pointbase_def)
      qed
    qed
    note mono subset1 subset2
  }  
  then show ?thesis by (simp add: continuous_def subset_antisym)   
qed
 
lemma pointbased_implies_continuous:
  "pointbased f \<Longrightarrow> continuous f"
  using pointbase_is_continuous pointbased_def by force

lemma setmonotone_implies_chain_funpower:
  assumes setmonotone: "setmonotone f"
  shows "chain (\<lambda> n. funpower f n I)"
by (simp add: chain_def setmonotone subset_setmonotone)  

lemma natUnion_subset: "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> natUnion f \<subseteq> natUnion g"
  by (meson natUnion_elem natUnion_upperbound subset_iff)

lemma natUnion_eq[case_names Subset Superset]: 
  "(\<And> n. \<exists> m. f n \<subseteq> g m) \<Longrightarrow> (\<And> n. \<exists> m. g n \<subseteq> f m) \<Longrightarrow> natUnion f = natUnion g"
by (simp add: natUnion_subset subset_antisym)
  
lemma natUnion_shift[symmetric]: 
  assumes chain: "chain C"
  shows "natUnion C = natUnion (\<lambda> n. C (n + m))"
proof (induct rule: natUnion_eq)
  case (Subset n)
    show ?case using chain chain_implies_mono le_add1 mono_def by blast 
next
  case (Superset n)
    show ?case by blast 
qed

definition regular :: "('a set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "regular f = (setmonotone f \<and> continuous f)"

lemma regular_fixpoint:
  assumes regular: "regular f"
  shows "f (limit f I) = limit f I"
proof -
  have setmonotone: "setmonotone f" using regular regular_def by blast
  have continuous: "continuous f" using regular regular_def by blast

  let ?C = "\<lambda> n. funpower f n I"
  have chain: "chain ?C"
    by (simp add: setmonotone setmonotone_implies_chain_funpower)
  have "f (limit f I) = f (natUnion ?C)"
    using limit_def by metis
  also have "f (natUnion ?C) = natUnion (f o ?C)"
    by (metis continuous continuous_def chain)
  also have "natUnion (f o ?C) = natUnion (\<lambda> n. f(funpower f n I))"
    by (meson comp_apply)
  also have "natUnion (\<lambda> n. f(funpower f n I)) = natUnion (\<lambda> n. ?C (n + 1))"
    by simp
  also have "natUnion (\<lambda> n. ?C(n + 1)) = natUnion ?C"
    apply (subst natUnion_shift)
    using chain by (blast+)
  finally show ?thesis by (simp add: limit_def)
qed  
    
lemma fix_is_fix_of_limit:
  assumes fixpoint: "f I = I"   
  shows "limit f I = I"
proof -
  have funpower: "\<And> n. funpower f n I = I" 
  proof -  
    fix n :: nat
    from fixpoint show "funpower f n I = I"
      by (induct n, auto)
  qed
  show ?thesis by (simp add: limit_def funpower natUnion_def)
qed     

lemma limit_is_idempotent: "regular f \<Longrightarrow> limit f (limit f I) = limit f I"
by (simp add: fix_is_fix_of_limit regular_fixpoint)

definition mk_regular1 :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular1 P F I = I \<union> { F q x | q x. x \<in> I \<and> P q x }"

definition mk_regular2 :: "('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "mk_regular2 P F I = I \<union> { F q x y | q x y. x \<in> I \<and> y \<in> I \<and> P q x y }"

lemma setmonotone_mk_regular1: "setmonotone (mk_regular1 P F)"
by (simp add: mk_regular1_def setmonotone_def)

lemma setmonotone_mk_regular2: "setmonotone (mk_regular2 P F)"
by (simp add: mk_regular2_def setmonotone_def)

lemma pointbased_mk_regular1: "pointbased (mk_regular1 P F)"
proof -
  let ?f = "\<lambda> X. X \<union> { F q x | q x. x \<in> X \<and> P q x }"
  {
    fix I :: "'a set"
    have 1: "pointbase ?f I \<subseteq> mk_regular1 P F I"
      by (auto simp add: pointbase_def mk_regular1_def)
    have 2: "mk_regular1 P F I \<subseteq> pointbase ?f I"
      apply (simp add: pointbase_def mk_regular1_def)
      apply blast
      done
    from 1 2 have "pointbase ?f I = mk_regular1 P F I" by blast
  }
  then show ?thesis
    apply (subst pointbased_def)
    apply (rule_tac x="?f" in exI)
    by blast
qed

lemma pointbased_mk_regular2: "pointbased (mk_regular2 P F)"
proof -
  let ?f = "\<lambda> X. X \<union> { F q x y | q x y. x \<in> X \<and> y \<in> X \<and> P q x y }"
  {
    fix I :: "'a set"
    have 1: "pointbase ?f I \<subseteq> mk_regular2 P F I"
      by (auto simp add: pointbase_def mk_regular2_def)
    have 2: "mk_regular2 P F I \<subseteq> pointbase ?f I"
      apply (auto simp add: pointbase_def mk_regular2_def)
      apply blast
      proof -
        fix q x y
        assume x: "x \<in> I"
        assume y: "y \<in> I"
        assume P: "P q x y"
        let ?X = "{x, y}"
        let ?A = "?X \<union> {F q x y |q x y. x \<in> ?X \<and> y \<in> ?X \<and> P q x y}"
        show "\<exists>A. (\<exists>X. A = X \<union> {F q x y |q x y. x \<in> X \<and> y \<in> X \<and> P q x y} \<and> 
          finite X \<and> X \<subseteq> I) \<and> F q x y \<in> A"
          apply (rule_tac x="?A" in exI)
          apply (rule conjI)
          apply (rule_tac x="?X" in exI)
          apply (auto simp add: x y)[1]
          using x y P by blast
      qed  
    from 1 2 have "pointbase ?f I = mk_regular2 P F I" by blast
  }
  then show ?thesis
    apply (subst pointbased_def)
    apply (rule_tac x="?f" in exI)
    by blast
qed

lemma regular1:"regular (mk_regular1 P F)"
by (simp add: pointbased_implies_continuous pointbased_mk_regular1 regular_def 
  setmonotone_mk_regular1)
  
lemma regular2: "regular (mk_regular2 P F)"
by (simp add: pointbased_implies_continuous pointbased_mk_regular2 regular_def 
  setmonotone_mk_regular2)

lemma continous_comp: 
  assumes f: "continuous f"
  assumes g: "continuous g"
  shows "continuous (g o f)"
by (metis (no_types, lifting) comp_assoc comp_def continuous_def f g)

lemma setmonotone_comp:
  assumes f: "setmonotone f"
  assumes g: "setmonotone g"
  shows "setmonotone (g o f)"
by (metis (mono_tags, lifting) comp_def f g rev_subsetD setmonotone_def subsetI)

lemma regular_comp:
  assumes f: "regular f"
  assumes g: "regular g"
  shows "regular (g o f)"
using continous_comp f g regular_def setmonotone_comp by blast

lemma setmonotone_id[simp]: "setmonotone id"
  by (simp add: id_def setmonotone_def)

lemma continuous_id[simp]: "continuous id"
  by (simp add: continuous_def)

lemma regular_id[simp]: "regular id"
  by (simp add: regular_def)

lemma regular_funpower: "regular f \<Longrightarrow> regular (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n) 
  have funpower: "funpower f (Suc n) = f o (funpower f n)"
    apply (rule ext)
    by simp
  with Suc show ?case
    by (auto simp only: funpower regular_comp)
qed

lemma mono_id[simp]: "mono id"
  by (simp add: mono_def id_def)

lemma mono_funpower:
  assumes mono: "mono f"
  shows "mono (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n) 
  show ?case by (simp add: Suc.hyps mono monoD monoI)
qed    

lemma mono_limit:
  assumes mono: "mono f"
  shows "mono (limit f)"
proof(auto simp add: mono_def limit_def)
  fix A :: "'a set" 
  fix B :: "'a set"
  fix x
  assume subset: "A \<subseteq> B"
  assume "x \<in> natUnion (\<lambda>n. funpower f n A)"
  then have "\<exists> n. x \<in> funpower f n A" using elem_limit_simp limit_def by fastforce 
  then obtain n where n: "x \<in> funpower f n A" by blast
  then have mono: "mono (funpower f n)" by (simp add: mono mono_funpower)
  then have "x \<in> funpower f n B" by (meson contra_subsetD monoD n subset)  
  then show "x \<in> natUnion (\<lambda>n. funpower f n B)" by (simp add: natUnion_elem) 
qed

lemma continuous_funpower:
  assumes continuous: "continuous f"
  shows "continuous (funpower f n)"
proof (induct n)
  case 0 thus ?case by (simp add: id_def[symmetric])
next
  case (Suc n)
  have mono: "mono (funpower f (Suc n))" 
    by (simp add: continuous continuous_imp_mono mono_funpower) 
  have chain: "\<forall> C. chain C \<longrightarrow> chain ((funpower f (Suc n)) o C)"
    by (simp del: funpower.simps add: mono mono_maps_chain_to_chain) 
  have limit: "\<And> C. chain C \<Longrightarrow> (funpower f (Suc n)) (natUnion C) = 
      natUnion ((funpower f (Suc n)) o C)"
      apply simp
      apply (subst continuous_apply[OF Suc])
      apply simp
      apply (subst continuous_apply[OF continuous])
      apply (simp add: Suc.hyps continuous_imp_mono mono_maps_chain_to_chain)
      apply (rule arg_cong[where f="natUnion"])
      apply (rule ext)
      by simp
  from chain limit show ?case using continuous_def by blast
qed      

lemma natUnion_swap:
  "natUnion (\<lambda> i. natUnion (\<lambda> j. f i j)) = natUnion (\<lambda> j. natUnion (\<lambda> i. f i j))"
by (metis (no_types, lifting) natUnion_elem natUnion_upperbound subsetI subset_antisym)
      
lemma continuous_limit:
  assumes continuous: "continuous f"
  shows "continuous (limit f)"
proof -
  have mono: "mono (limit f)"
    by (simp add: continuous continuous_imp_mono mono_limit) 
  have chain: "\<And> C. chain C \<Longrightarrow> chain ((limit f) o C)"
    by (simp add: mono mono_maps_chain_to_chain)
  have "\<And> C. chain C \<Longrightarrow> (limit f) (natUnion C) = natUnion ((limit f) o C)"
  proof -
    fix C :: "nat \<Rightarrow> 'a set"
    assume chain_C: "chain C"
    have contpower: "\<And> n. continuous (funpower f n)"
      by (simp add: continuous continuous_funpower) 
    have comp: "\<And> n F. F o C = (\<lambda> i. F (C i))"
      by auto    
    have "(limit f) (natUnion C) = natUnion (\<lambda> n. funpower f n (natUnion C))"
      by (simp add: limit_def)
    also have "natUnion (\<lambda> n. funpower f n (natUnion C)) = 
          natUnion (\<lambda> n. natUnion ((funpower f n) o C))"
      apply (subst continuous_apply[OF contpower])
      apply (simp add: chain_C)+
      done
    also have "natUnion (\<lambda> n. natUnion ((funpower f n) o C)) = 
      natUnion (\<lambda> n. natUnion (\<lambda> i. funpower f n (C i)))" 
      apply (subst comp)
      apply blast
      done
    also have "natUnion (\<lambda> n. natUnion (\<lambda> i. funpower f n (C i))) =
      natUnion (\<lambda> i. natUnion (\<lambda> n. funpower f n (C i)))"
      apply (subst natUnion_swap)
      apply blast
      done
    also have "natUnion (\<lambda> i. natUnion (\<lambda> n. funpower f n (C i))) = 
      (natUnion (\<lambda> i. limit f (C i)))"
      apply (simp add: limit_def)
      done
    also have "natUnion (\<lambda> i. limit f (C i)) = natUnion ((limit f) o C)"
      apply (subst comp)
      apply simp
      done
    finally show "(limit f) (natUnion C) = natUnion ((limit f) o C)" by blast
  qed
  with chain show ?thesis by (simp add: continuous_def)
qed   
      
lemma regular_limit: "regular f \<Longrightarrow> regular (limit f)"
by (simp add: continuous_limit regular_def setmonotone_limit)

lemma regular_implies_mono: "regular f \<Longrightarrow> mono f"
by (simp add: continuous_imp_mono regular_def)

lemma regular_implies_setmonotone: "regular f \<Longrightarrow> setmonotone f"
by (simp add: regular_def)
  
lemma regular_implies_continuous: "regular f \<Longrightarrow> continuous f"
by (simp add: regular_def)

end
