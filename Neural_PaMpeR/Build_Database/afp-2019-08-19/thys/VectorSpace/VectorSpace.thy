section \<open>Basic theory of vector spaces, using locales\<close>

theory VectorSpace
imports Main
  "HOL-Algebra.Module"
  "HOL-Algebra.Coset"
  RingModuleFacts
  MonoidSums
  LinearCombinations
  SumSpaces
begin

subsection \<open>Basic definitions and facts carried over from modules\<close>
text \<open>A \<open>vectorspace\<close> is a module where the ring is a field. 
Note that we switch notation from $(R, M)$ to $(K, V)$.\<close>
locale vectorspace = 
  module?: module K V + field?: field K  
  for K and V

(*
Use sets for bases, and functions from the sets to carrier K 
represent the coefficients. 
*)

text \<open>A \<open>subspace\<close> of a vectorspace is a nonempty subset 
that is closed under addition and scalar multiplication. These properties
have already been defined in submodule. Caution: W is a set, while V is 
a module record. To get W as a vectorspace, write vs W.\<close>
locale subspace =
  fixes K and W and V (structure)
  assumes vs: "vectorspace K V"
      and submod: "submodule K W V"


lemma (in vectorspace) is_module[simp]:
  "subspace K W V\<Longrightarrow>submodule K W V"
by (unfold subspace_def, auto)

text \<open>We introduce some basic facts and definitions copied from module.
We introduce some abbreviations, to match convention.\<close>
abbreviation (in vectorspace) vs::"'c set \<Rightarrow> ('a, 'c, 'd) module_scheme"
  where "vs W \<equiv> V\<lparr>carrier :=W\<rparr>"

lemma (in vectorspace) carrier_vs_is_self [simp]:
  "carrier (vs W) = W"
  by auto

lemma (in vectorspace) subspace_is_vs:
  fixes W::"'c set"
  assumes 0: "subspace K W V"
  shows "vectorspace K (vs W)"
proof -
  from 0 show ?thesis
    apply (unfold vectorspace_def subspace_def, auto)
    by (intro submodule_is_module, auto)
qed

abbreviation (in module) subspace_sum:: "['c set, 'c set] \<Rightarrow> 'c set"
  where "subspace_sum W1 W2 \<equiv>submodule_sum W1 W2"

lemma (in vectorspace) vs_zero_lin_dep: 
  assumes h2: "S\<subseteq>carrier V" and h3: "lin_indpt S"
  shows "\<zero>\<^bsub>V\<^esub> \<notin> S"
proof -
  have vs: "vectorspace K V"..
  from vs have nonzero: "carrier K \<noteq>{\<zero>\<^bsub>K\<^esub>}"
    by (metis one_zeroI zero_not_one)
  from h2 h3 nonzero show ?thesis by (rule zero_nin_lin_indpt)
qed

text \<open>A \<open>linear_map\<close> is a module homomorphism between 2 vectorspaces
over the same field.\<close>
locale linear_map = 
  V?: vectorspace K V + W?: vectorspace K W
  + mod_hom?: mod_hom K V W T
    for K and V and W and T

context linear_map
begin
lemmas T_hom = f_hom
lemmas T_add = f_add
lemmas T_smult = f_smult
lemmas T_im = f_im
lemmas T_neg = f_neg
lemmas T_minus = f_minus
lemmas T_ker = f_ker

abbreviation imT:: "'e set"
  where "imT \<equiv> mod_hom.im"

abbreviation kerT:: "'c set"
  where "kerT \<equiv> mod_hom.ker"

lemmas T0_is_0[simp] = f0_is_0

lemma kerT_is_subspace: "subspace K ker V"
proof - 
  have vs: "vectorspace K V"..
  from vs show ?thesis
    apply (unfold subspace_def, auto)
    by (rule ker_is_submodule)
qed

lemma imT_is_subspace: "subspace K imT W"
proof - 
  have vs: "vectorspace K W"..
  from vs show ?thesis
    apply (unfold subspace_def, auto)
    by (rule im_is_submodule)
qed
end

lemma vs_criteria:
  fixes K and V 
  assumes field: "field K"
      and zero: "\<zero>\<^bsub>V\<^esub>\<in> carrier V" 
      and add: "\<forall>v w. v\<in>carrier V \<and> w\<in>carrier V\<longrightarrow> v\<oplus>\<^bsub>V\<^esub> w\<in> carrier V"
      and neg: "\<forall>v\<in>carrier V. (\<exists>neg_v\<in>carrier V. v\<oplus>\<^bsub>V\<^esub>neg_v=\<zero>\<^bsub>V\<^esub>)"
      and smult: "\<forall>c v. c\<in> carrier K \<and> v\<in>carrier V\<longrightarrow> c\<odot>\<^bsub>V\<^esub> v \<in> carrier V"
      and comm: "\<forall>v w. v\<in>carrier V \<and> w\<in>carrier V\<longrightarrow> v\<oplus>\<^bsub>V\<^esub> w=w\<oplus>\<^bsub>V\<^esub> v"
      and assoc: "\<forall>v w x. v\<in>carrier V \<and> w\<in>carrier V \<and> x\<in>carrier V\<longrightarrow> (v\<oplus>\<^bsub>V\<^esub> w)\<oplus>\<^bsub>V\<^esub> x= v\<oplus>\<^bsub>V\<^esub> (w\<oplus>\<^bsub>V\<^esub> x)"
      and add_id: "\<forall>v\<in>carrier V. (v\<oplus>\<^bsub>V\<^esub> \<zero>\<^bsub>V\<^esub> =v)"
      and compat: "\<forall>a b v. a\<in> carrier K \<and> b\<in> carrier K \<and> v\<in>carrier V\<longrightarrow> (a\<otimes>\<^bsub>K\<^esub> b)\<odot>\<^bsub>V\<^esub> v =a\<odot>\<^bsub>V\<^esub> (b\<odot>\<^bsub>V\<^esub> v)"
      and smult_id: "\<forall>v\<in>carrier V. (\<one>\<^bsub>K\<^esub> \<odot>\<^bsub>V\<^esub> v =v)"
      and dist_f: "\<forall>a b v. a\<in> carrier K \<and> b\<in> carrier K \<and> v\<in>carrier V\<longrightarrow> (a\<oplus>\<^bsub>K\<^esub> b)\<odot>\<^bsub>V\<^esub> v =(a\<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> (b\<odot>\<^bsub>V\<^esub> v)"
      and dist_add: "\<forall>a v w. a\<in> carrier K \<and> v\<in>carrier V \<and> w\<in>carrier V\<longrightarrow> a\<odot>\<^bsub>V\<^esub> (v\<oplus>\<^bsub>V\<^esub> w) =(a\<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> (a\<odot>\<^bsub>V\<^esub> w)"
  shows "vectorspace K V"
proof - 
  from field have 1: "cring K" by (unfold field_def domain_def, auto)
  from assms 1 have 2: "module K V" by (intro module_criteria, auto)
  from field 2 show ?thesis by (unfold vectorspace_def module_def, auto)
qed

text \<open>For any set $S$, the space of functions $S\to K$ forms a vector space.\<close>
lemma (in vectorspace) func_space_is_vs:
  fixes S
  shows "vectorspace K (func_space S)" 
proof -
  have 0: "field K"..
  have 1: "module K (func_space S)" by (rule func_space_is_module)
  from 0 1 show ?thesis by (unfold vectorspace_def module_def, auto)
qed


lemma direct_sum_is_vs: 
  fixes K V1 V2
  assumes h1: "vectorspace K V1" and h2: "vectorspace K V2"
  shows "vectorspace K (direct_sum V1 V2)"
proof -
  from h1 h2 have mod: "module K (direct_sum V1 V2)" by (unfold vectorspace_def, intro direct_sum_is_module, auto)
  from mod h1 show ?thesis by (unfold vectorspace_def, auto)
qed

lemma inj1_linear:
  fixes K V1 V2
  assumes h1: "vectorspace K V1" and h2: "vectorspace K V2"
  shows "linear_map K V1 (direct_sum V1 V2) (inj1 V1 V2)"
proof - 
  from h1 h2 have mod: "mod_hom K V1 (direct_sum V1 V2) (inj1 V1 V2)" by (unfold vectorspace_def, intro inj1_hom, auto)
  from mod h1 h2 show ?thesis 
    by (unfold linear_map_def vectorspace_def , auto, intro direct_sum_is_module, auto)
qed

lemma inj2_linear:
  fixes K V1 V2
  assumes h1: "vectorspace K V1" and h2: "vectorspace K V2"
  shows "linear_map K V2 (direct_sum V1 V2) (inj2 V1 V2)"
proof - 
  from h1 h2 have mod: "mod_hom K V2 (direct_sum V1 V2) (inj2 V1 V2)" by (unfold vectorspace_def, intro inj2_hom, auto)
  from mod h1 h2 show ?thesis 
    by (unfold linear_map_def vectorspace_def , auto, intro direct_sum_is_module, auto)
qed

text \<open>For subspaces $V_1,V_2\subseteq V$, the map $V_1\oplus V_2\to V$ given by $(v_1,v_2)\mapsto 
v_1+v_2$ is linear.\<close>
lemma (in vectorspace) sum_map_linear: 
  fixes V1 V2
  assumes h1: "subspace K V1 V" and h2: "subspace K V2 V"
  shows "linear_map K (direct_sum (vs V1) (vs V2)) V (\<lambda> v. (fst v) \<oplus>\<^bsub>V\<^esub> (snd v))"
proof - 
  from h1 h2 have mod: "mod_hom K (direct_sum (vs V1) (vs V2)) V (\<lambda> v. (fst v) \<oplus>\<^bsub>V\<^esub> (snd v))" 
    by ( intro sum_map_hom, unfold subspace_def, auto)
  from mod h1 h2 show ?thesis 
    apply (unfold linear_map_def, auto) apply (intro direct_sum_is_vs subspace_is_vs, auto).. 
qed

lemma (in vectorspace) sum_is_subspace:
  fixes W1 W2
  assumes h1: "subspace K W1 V" and h2: "subspace K W2 V"
  shows "subspace K (subspace_sum W1 W2) V"
proof -
  from h1 h2 have mod: "submodule K (submodule_sum W1 W2) V" 
    by ( intro sum_is_submodule, unfold subspace_def, auto)
  from mod h1 h2 show ?thesis 
    by (unfold subspace_def, auto)
qed

text \<open>If $W_1,W_2\subseteq V$ are subspaces, $W_1\subseteq W_1 + W_2$\<close>
lemma (in vectorspace) in_sum_vs:
  fixes W1 W2
  assumes h1: "subspace K W1 V" and h2: "subspace K W2 V"
  shows "W1 \<subseteq> subspace_sum W1 W2"
proof -
  from h1 h2 show ?thesis by (intro in_sum, unfold subspace_def, auto)
qed

lemma (in vectorspace) vsum_comm:
  fixes W1 W2
  assumes h1: "subspace K W1 V" and h2: "subspace K W2 V"
  shows "(subspace_sum W1 W2) = (subspace_sum W2 W1)"
proof - 
  from h1 h2 show ?thesis by (intro msum_comm, unfold subspace_def, auto)
qed

text \<open>If $W_1,W_2\subseteq V$ are subspaces, then $W_1+W_2$ is the minimal subspace such that 
both $W_1\subseteq W$ and $W_2\subseteq W$.\<close>
lemma (in vectorspace) vsum_is_minimal:
  fixes W W1 W2
  assumes h1: "subspace K W1 V" and h2: "subspace K W2 V" and h3: "subspace K W V"
  shows "(subspace_sum W1 W2) \<subseteq> W \<longleftrightarrow> W1 \<subseteq> W \<and> W2 \<subseteq> W"
proof - 
  from h1 h2 h3 show ?thesis by (intro sum_is_minimal, unfold subspace_def, auto)
qed


lemma (in vectorspace) span_is_subspace:
  fixes S
  assumes h2: "S\<subseteq>carrier V"
  shows "subspace K (span S) V"
proof -
  have 0: "vectorspace K V"..
  from h2 have 1: "submodule K (span S) V" by (rule span_is_submodule)
  from 0 1 show ?thesis by (unfold subspace_def mod_hom_def linear_map_def, auto)
qed

subsubsection \<open>Facts specific to vector spaces\<close>

text \<open>If $av = w$ and $a\neq 0$, $v=a^{-1}w$.\<close>
lemma (in vectorspace) mult_inverse:
  assumes h1: "a\<in>carrier K" and h2: "v\<in>carrier V" and h3: "a \<odot>\<^bsub>V\<^esub> v = w" and h4: "a\<noteq>\<zero>\<^bsub>K\<^esub>"
  shows "v = (inv\<^bsub>K\<^esub> a )\<odot>\<^bsub>V\<^esub> w"
proof -
  from h1 h2 h3 have 1: "w\<in>carrier V" by auto
  from h3 1 have 2: "(inv\<^bsub>K\<^esub> a )\<odot>\<^bsub>V\<^esub>(a \<odot>\<^bsub>V\<^esub> v) =(inv\<^bsub>K\<^esub> a )\<odot>\<^bsub>V\<^esub>w" by auto
  from h1 h4 have 3: "inv\<^bsub>K\<^esub> a\<in>carrier K" by auto
  interpret g: group "(units_group K)" by (rule units_form_group)
  have f: "field K"..
  from f h1 h4 have 4: "a\<in>Units K" 
    by (unfold field_def field_axioms_def, simp)
  from 4 h1 h4 have 5: "((inv\<^bsub>K\<^esub> a) \<otimes>\<^bsub>K\<^esub>a) = \<one>\<^bsub>K\<^esub>" 
    by (intro Units_l_inv, auto)
  from 5 have 6: "(inv\<^bsub>K\<^esub> a )\<odot>\<^bsub>V\<^esub>(a \<odot>\<^bsub>V\<^esub> v) = v" 
  proof - 
    from h1 h2 h4 have 7: "(inv\<^bsub>K\<^esub> a )\<odot>\<^bsub>V\<^esub>(a \<odot>\<^bsub>V\<^esub> v) =(inv\<^bsub>K\<^esub> a \<otimes>\<^bsub>K\<^esub>a) \<odot>\<^bsub>V\<^esub> v" by (auto simp add: smult_assoc1)
    from 5 h2 have 8: "(inv\<^bsub>K\<^esub> a \<otimes>\<^bsub>K\<^esub>a) \<odot>\<^bsub>V\<^esub> v = v" by auto
    from 7 8 show ?thesis by auto
  qed
  from 2 6 show ?thesis by auto
qed

text \<open>If $w\in S$ and $\sum_{w\in S} a_ww=0$, we have $v=\sum_{w\not\in S}a_v^{-1}a_ww$\<close>
lemma (in vectorspace) lincomb_isolate: 
  fixes A v
  assumes h1: "finite A" and h2: "A\<subseteq>carrier V"  and h3: "a\<in>A\<rightarrow>carrier K" and h4: "v\<in>A"
    and h5: "a v \<noteq> \<zero>\<^bsub>K\<^esub>" and h6: "lincomb a A=\<zero>\<^bsub>V\<^esub>"
  shows "v=lincomb (\<lambda>w. \<ominus>\<^bsub>K\<^esub>(inv\<^bsub>K\<^esub> (a v)) \<otimes>\<^bsub>K\<^esub> a w) (A-{v})" and "v\<in> span (A-{v})"
proof -
  from h1 h2 h3 h4 have 1: "lincomb a A = ((a v) \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a (A-{v})" 
    by (rule lincomb_del2)
  from 1 have 2: "\<zero>\<^bsub>V\<^esub>= ((a v) \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb a (A-{v})" by (simp add: h6)
  from h1 h2 h3 have 5: "lincomb a (A-{v}) \<in>carrier V" by auto (*intro lincomb_closed*)
  from 2 h1 h2 h3 h4 have 3: " \<ominus>\<^bsub>V\<^esub> lincomb a (A-{v}) = ((a v) \<odot>\<^bsub>V\<^esub> v)" 
    by (auto intro!: M.minus_equality)
  have 6: "v = (\<ominus>\<^bsub>K\<^esub> (inv\<^bsub>K\<^esub> (a v))) \<odot>\<^bsub>V\<^esub> lincomb a (A-{v})"
  proof - 
    from h2 h3 h4 h5 3 have 7: "v = inv\<^bsub>K\<^esub> (a v) \<odot>\<^bsub>V\<^esub> (\<ominus>\<^bsub>V\<^esub> lincomb a (A-{v}))" 
      by (intro mult_inverse, auto)
    from assms have 8: "inv\<^bsub>K\<^esub> (a v)\<in>carrier K" by auto
    from assms 5 8 have 9: "inv\<^bsub>K\<^esub> (a v) \<odot>\<^bsub>V\<^esub> (\<ominus>\<^bsub>V\<^esub> lincomb a (A-{v})) 
      = (\<ominus>\<^bsub>K\<^esub> (inv\<^bsub>K\<^esub> (a v))) \<odot>\<^bsub>V\<^esub> lincomb a (A-{v})"
        by (simp add: smult_assoc_simp smult_minus_1_back r_minus)
    from 7 9 show ?thesis by auto
  qed
  from h1 have 10: "finite (A-{v})" by auto
  from assms have 11 : "(\<ominus>\<^bsub>K\<^esub> (inv\<^bsub>K\<^esub> (a v)))\<in> carrier K" by auto
  from assms have 12: "lincomb (\<lambda>w. \<ominus>\<^bsub>K\<^esub>(inv\<^bsub>K\<^esub> (a v)) \<otimes>\<^bsub>K\<^esub> a w) (A-{v}) = 
    (\<ominus>\<^bsub>K\<^esub> (inv\<^bsub>K\<^esub> (a v))) \<odot>\<^bsub>V\<^esub> lincomb a (A-{v})" 
    by (intro lincomb_smult, auto)
  from 6 12 show "v=lincomb (\<lambda>w. \<ominus>\<^bsub>K\<^esub>(inv\<^bsub>K\<^esub> (a v)) \<otimes>\<^bsub>K\<^esub> a w) (A-{v})" by auto
  with assms show "v\<in> span (A-{v})" 
    unfolding span_def 
    by (force simp add: 11 ring_subset_carrier)
qed

text \<open>The map $(S\to K)\mapsto V$ given by $(a_v)_{v\in S}\mapsto \sum_{v\in S} a_v v$ is linear.\<close>
lemma (in vectorspace) lincomb_is_linear:
  fixes S
  assumes h: "finite S" and h2: "S\<subseteq>carrier V"
  shows "linear_map K (func_space S) V (\<lambda>a. lincomb a S)" 
proof -
  have 0: "vectorspace K V"..
  from h h2 have 1: "mod_hom K (func_space S) V (\<lambda>a. lincomb a S)" by (rule lincomb_is_mod_hom)
  from 0 1 show ?thesis by (unfold vectorspace_def mod_hom_def linear_map_def, auto)
qed

subsection \<open>Basic facts about span and linear independence\<close>

text \<open>If $S$ is linearly independent, then $v\in \text{span}S$ iff $S\cup \{v\}$ is linearly 
dependent.\<close>
theorem (in vectorspace) lin_dep_iff_in_span:
  fixes A v S
  assumes  h1: "S \<subseteq> carrier V" and h2: "lin_indpt S" and h3: "v\<in> carrier V" and h4: "v\<notin>S"
  shows "v\<in> span S \<longleftrightarrow> lin_dep (S \<union> {v})"
proof -
  let ?T = "S \<union> {v}" 
  have 0: "v\<in>?T " by auto
  from h1 h3 have h1_1: "?T \<subseteq> carrier V" by auto
  have a1:"lin_dep ?T \<Longrightarrow> v\<in> span S"
  proof - 
    assume a11: "lin_dep ?T"
    from a11 obtain a w A where a: "(finite A \<and> A\<subseteq>?T \<and> (a\<in> (A\<rightarrow>carrier K)) \<and> (lincomb a A = \<zero>\<^bsub>V\<^esub>) \<and> (w\<in>A) \<and> (a w\<noteq> \<zero>\<^bsub>K\<^esub>))"
      by (metis lin_dep_def)
    from assms a have nz2: "\<exists>v\<in>A-S. a v\<noteq>\<zero>\<^bsub>K\<^esub>" 
      by (intro lincomb_must_include[where ?v="w" and ?T="S\<union>{v}"], auto)
    from a nz2 have singleton: "{v}=A-S" by auto
    from singleton nz2 have nz3: "a v\<noteq>\<zero>\<^bsub>K\<^esub>" by auto
(*Can modularize this whole section out. "solving for one variable"*)
    let ?b="(\<lambda>w. \<ominus>\<^bsub>K\<^esub> (inv\<^bsub>K\<^esub> (a v)) \<otimes>\<^bsub>K\<^esub> (a w))"
    from singleton have Ains: "(A\<inter>S) = A-{v}" by auto
    from assms a singleton nz3 have a31: "v= lincomb ?b (A\<inter>S)" 
      apply (subst Ains)
      by (intro lincomb_isolate(1), auto)
    from a a31 nz3 singleton show ?thesis 
      apply (unfold span_def, auto) 
      apply (rule_tac x="?b" in exI)
      apply (rule_tac x="A\<inter>S" in exI) 
      by (auto intro!: m_closed)
  qed
  have a2: "v\<in> (span S) \<Longrightarrow> lin_dep ?T"
  proof - 
    assume inspan: "v\<in> (span S)"
    from inspan obtain a A where a: "A\<subseteq>S \<and> finite A \<and> (v = lincomb a A)\<and> a\<in>A\<rightarrow>carrier K" by (simp add: span_def, auto)
    let ?b = "\<lambda> w. if (w=v) then (\<ominus>\<^bsub>K\<^esub> \<one>\<^bsub>K\<^esub>) else a w" (*consider -v + \sum a_w w*)
    have lc0: " lincomb ?b (A\<union>{v})=\<zero>\<^bsub>V\<^esub>" 
    proof - 
      from assms a have lc_ins: "lincomb ?b (A\<union>{v}) = ((?b v) \<odot>\<^bsub>V\<^esub> v) \<oplus>\<^bsub>V\<^esub> lincomb ?b A" 
        by (intro lincomb_insert, auto)
      from assms a have lc_elim: "lincomb ?b A=lincomb a A" by (intro lincomb_elim_if, auto)
      from assms lc_ins lc_elim a show ?thesis by (simp add: M.l_neg smult_minus_1)
    qed
    from  a lc0 show ?thesis 
      apply (unfold lin_dep_def)
      apply (rule_tac x="A\<union>{v}" in exI)
      apply (rule_tac x="?b" in exI)
      apply (rule_tac x="v" in exI)
      by auto
  qed
  from a1 a2 show ?thesis by auto
qed

text \<open>If $v\in \text{span} A$ then $\text{span}A =\text{span}(A\cup \{v\})$\<close>
lemma (in vectorspace) already_in_span:
  fixes v A
  assumes  inC: "A\<subseteq>carrier V" and inspan: "v\<in>span A"
  shows "span A= span (A\<union>{v})"
proof - 
  from inC inspan have dir1: "span A \<subseteq> span (A\<union>{v})" by (intro span_is_monotone, auto)

  from inC have inown: "A\<subseteq>span A" by (rule in_own_span)
  from inC have subm: "submodule K (span A) V" by (rule span_is_submodule)
  from inown inspan subm have dir2: "span (A \<union> {v}) \<subseteq> span A" by (intro span_is_subset, auto) 

  from dir1 dir2 show ?thesis by auto
qed

subsection \<open>The Replacement Theorem\<close>

text \<open>If $A,B\subseteq V$ are finite, $A$ is linearly independent, $B$ generates $W$, 
and $A\subseteq W$, then there exists $C\subseteq V$ disjoint from $A$ such that
$\text{span}(A\cup C) = W$ and $|C|\le |B|-|A|$. In other words, we can complete
any linearly independent set to a generating set of $W$ by adding at most $|B|-|A|$ more elements.\<close>
theorem (in vectorspace) replacement:
  fixes A B (*A B are lists of vectors (colloquially we refer to them as sets)*) 
  assumes h1: "finite A"
      and h2: "finite B"
      and h3: "B\<subseteq>carrier V"
      and h4: "lin_indpt A" (*A is linearly independent*)
      and h5: "A\<subseteq>span B" (*All entries of A are in K*)
  shows "\<exists>C. finite C \<and> C\<subseteq>carrier V \<and> C\<subseteq>span B \<and> C\<inter>A={} \<and> int (card C) \<le> (int (card B)) - (int (card A)) \<and> (span (A \<union> C) = span B)" 
  (is "\<exists>C. ?P A B C")
  (*There is a set C of cardinality |B| - |A| such that A\<union>C generates V*)
using h1 h2 h3 h4 h5 
proof (induct "card A" arbitrary: A B)
  case 0
  from "0.prems"(1) "0.hyps" have a0: "A={}" by auto
  from "0.prems"(3) have a3: "B\<subseteq>span B" by (rule in_own_span)
  from a0 a3 "0.prems" show ?case by (rule_tac x="B" in exI, auto)
next
  case (Suc m)
  let ?W="span B"
  from Suc.prems(3) have BinC: "span B\<subseteq>carrier V" by (rule span_is_subset2)
  (*everything you want to know about A*)
  from Suc.prems Suc.hyps BinC have A: "finite A" "lin_indpt A" "A\<subseteq>span B" "Suc m = card A" "A\<subseteq>carrier V" 
    by auto
  (*everything you want to know about B*)
  from Suc.prems have B: "finite B" "B\<subseteq>carrier V" by auto
  (*A B are lists of vectors (colloquially we refer to them as sets)*) 
  from Suc.hyps(2) obtain v where v: "v\<in>A" by fastforce
  let ?A'="A-{v}"
  (*?A' is linearly independent because it is the subset of a linearly independent set, A.*)
  from A(2) have liA': "lin_indpt ?A'" 
    apply (intro subset_li_is_li[of "A" "?A'"]) 
     by auto
  from v liA' Suc.prems Suc.hyps(2) have "\<exists>C'. ?P ?A' B C'" 
    apply (intro Suc.hyps(1))
         by auto
  from this obtain C' where C': "?P ?A' B C'" by auto

  show ?case 
  proof (cases "v\<in> C'")
    case True
    have vinC': "v\<in>C'" by fact
    from vinC' v have seteq: "A - {v} \<union> C' = A \<union> (C' - {v})" by auto
    from C' seteq have spaneq: "span (A \<union> (C' - {v})) = span (B)" by algebra
    from Suc.prems Suc.hyps C' vinC' v spaneq show ?thesis
      apply (rule_tac x="C'-{v}" in exI)
      apply (subgoal_tac "card C' >0")
       by auto
  next 
    case False
    have f: "v\<notin>C'" by fact
    from A v C' have "\<exists>a. a\<in>(?A'\<union>C')\<rightarrow>carrier K \<and>  lincomb a (?A' \<union> C') =v" 
      by (intro finite_in_span, auto)
    from this obtain a where a: "a\<in>(?A'\<union>C')\<rightarrow>carrier K \<and> v= lincomb a (?A' \<union> C')" by metis
    let ?b="(\<lambda> w. if (w=v) then \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub> else a w)"
    from a have b: "?b\<in>A\<union>C'\<rightarrow>carrier K" by auto
    from v have rewrite_ins: "A\<union>C'=(?A'\<union>C')\<union>{v}" by auto
    from f have "v\<notin>?A'\<union>C'" by auto
    from this A C' v a f have lcb: "lincomb ?b (A \<union> C') = \<zero>\<^bsub>V\<^esub>"
      apply (subst rewrite_ins)
      apply (subst lincomb_insert)
           apply (simp_all add: ring_subset_carrier coeff_in_ring)
        apply (auto split: if_split_asm)
      apply (subst lincomb_elim_if)
          by (auto simp add: smult_minus_1 l_neg ring_subset_carrier)
(*NOTE: l_neg got deleted from the simp rules, but it is very useful.*)
    from C' f have rewrite_minus: "C'=(A\<union>C')-A" by auto
    from A C' b lcb v have exw: "\<exists>w\<in> C'. ?b w\<noteq>\<zero>\<^bsub>K\<^esub>" 
      apply (subst rewrite_minus)
      apply (intro lincomb_must_include[where ?T="A\<union>C'" and ?v="v"])
              by auto
    from exw obtain w where w: "w\<in> C'" "?b w\<noteq>\<zero>\<^bsub>K\<^esub>" by auto
    from A C' w f b lcb have w_in: "w\<in>span ((A\<union> C') -{w})" 
      apply (intro lincomb_isolate[where a="?b"]) 
           by auto
    have spaneq2: "span (A\<union>(C'-{w})) = span B"
    proof - 
      have 1: "span (?A'\<union>C') = span (A\<union> C')" (*adding v doesn't change the span*)
        proof - 
          from A C' v have m1: "span (?A'\<union>C') = span ((?A'\<union> C')\<union>{v})"
            apply (intro already_in_span) 
             by auto
          from f m1 show ?thesis by (metis rewrite_ins)
        qed
      have 2: "span (A\<union> (C'-{w})) = span (A\<union> C')" (*removing w doesn't change the span*)
      proof - 
        from C' w(1) f have b60: "A\<union> (C'-{w}) = (A\<union> C') -{w}" by auto
        from  w(1) have b61: "A\<union> C'= (A\<union> C' -{w})\<union>{w}" by auto
        from A C'  w_in show ?thesis 
          apply (subst b61) 
          apply (subst b60) 
          apply (intro already_in_span) 
           by auto
        qed
    from C' 1 2 show ?thesis by auto
  qed(* "span (A\<union>(C'-{w})) = span B"*)
    from A C' w f v spaneq2 show ?thesis
      apply (rule_tac x="C'-{w}" in exI)
      apply (subgoal_tac "card C' >0")
       by auto
  qed
qed

subsection \<open>Defining dimension and bases.\<close>

text \<open>Finite dimensional is defined as having a finite generating set.\<close>
definition (in vectorspace) fin_dim:: "bool"
  where "fin_dim = (\<exists> A. ((finite A) \<and> (A \<subseteq> carrier V) \<and> (gen_set A)))"

text \<open>The dimension is the size of the smallest generating set. For equivalent
characterizations see below.\<close>
definition (in vectorspace) dim:: "nat"
  where "dim = (LEAST n. (\<exists> A. ((finite A) \<and> (card A = n) \<and> (A \<subseteq> carrier V) \<and> (gen_set A))))"

text \<open>A \<open>basis\<close> is a linearly independent generating set.\<close>
definition (in vectorspace) basis:: "'c set \<Rightarrow> bool"
  where "basis A = ((lin_indpt A) \<and> (gen_set A)\<and> (A\<subseteq>carrier V))"

text \<open>From the replacement theorem, any linearly independent set is smaller than any generating set.\<close>
lemma (in vectorspace) li_smaller_than_gen:
  fixes A B
  assumes h1: "finite A" and h2: "finite B" and h3: "A\<subseteq>carrier V" and h4: "B\<subseteq>carrier V" 
    and h5: "lin_indpt A" and h6: "gen_set B"
  shows "card A \<le> card B"
proof - 
  from h3 h6 have 1: "A\<subseteq>span B" by  auto
  from h1 h2 h4 h5 1 obtain C where 
    2: "finite C \<and> C\<subseteq>carrier V \<and> C\<subseteq>span B \<and> C\<inter>A={} \<and> int (card C) \<le> int (card B) - int (card A) \<and> (span (A \<union> C) = span B)" 
    by (metis replacement) 
  from 2 show ?thesis by arith
qed

text \<open>The dimension is the cardinality of any basis. (In particular, all bases are the same size.)\<close>
lemma (in vectorspace) dim_basis:
  fixes A 
  assumes  fin: "finite A" and h2: "basis A"
  shows "dim = card A"
proof - 
  have 0: "\<And>B m. ((finite B) \<and> (card B = m) \<and> (B \<subseteq> carrier V) \<and> (gen_set B)) \<Longrightarrow> card A \<le> m"
  proof - 
    fix B m 
    assume 1: "((finite B) \<and> (card B = m) \<and> (B \<subseteq> carrier V) \<and> (gen_set B))"
    from 1 fin h2 have 2: "card A \<le> card B" 
      apply (unfold basis_def) 
      apply (intro li_smaller_than_gen) 
           by auto
    from 1 2 show "?thesis B m" by auto
  qed
  from fin h2 0 show ?thesis
    apply (unfold dim_def basis_def) 
    apply (intro Least_equality)
     apply (rule_tac x="A" in exI)
     by auto 
qed

(*can define more generally with posets*)
text \<open>A \<open>maximal\<close> set with respect to $P$ is such that if $B\supseteq A$ and $P$ is also 
satisfied for $B$, then $B=A$.\<close>
definition maximal::"'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> bool"
  where "maximal A P = ((P A) \<and> (\<forall>B. B\<supseteq>A \<and> P B \<longrightarrow> B = A))"

text \<open>A \<open>minimal\<close> set with respect to $P$ is such that if $B\subseteq A$ and $P$ is also 
satisfied for $B$, then $B=A$.\<close>
definition minimal::"'a set \<Rightarrow> ('a set \<Rightarrow> bool) \<Rightarrow> bool"
  where "minimal A P = ((P A) \<and> (\<forall>B. B\<subseteq>A \<and> P B \<longrightarrow> B = A))"
 
text \<open>A maximal linearly independent set is a generating set.\<close>
lemma (in vectorspace) max_li_is_gen:
  fixes A
  assumes h1: "maximal A (\<lambda>S. S\<subseteq>carrier V \<and> lin_indpt S)"
  shows "gen_set A"
proof (rule ccontr)
  assume 0: "\<not>(gen_set A)"
  from h1 have 1: " A\<subseteq> carrier V \<and> lin_indpt A" by (unfold maximal_def, auto)
  from 1 have 2: "span A \<subseteq> carrier V" by (intro span_is_subset2, auto)
  from 0 1 2 have 3: "\<exists>v. v\<in>carrier V \<and> v \<notin> (span A)"
    by auto
  from 3 obtain v where 4: "v\<in>carrier V \<and> v \<notin> (span A)" by auto
  have 5: "v\<notin>A" 
  proof - 
    from h1 1 have 51: "A\<subseteq>span A" apply (intro in_own_span) by auto
    from 4 51 show ?thesis by auto
  qed
  from lin_dep_iff_in_span have 6: "\<And>S v. S \<subseteq> carrier V\<and> lin_indpt S \<and> v\<in> carrier V \<and> v\<notin>S
    \<and> v\<notin> span S \<Longrightarrow>  (lin_indpt (S \<union> {v}))" by auto
  from 1 4 5 have 7: "lin_indpt (A \<union> {v})" apply (intro 6) by auto
(*  assumes h0:"finite S" and h1: "S \<subseteq> carrier V" and h2: "lin_indpt S" and h3: "v\<in> carrier V" and h4: "v\<notin>S"
  shows "v\<in> span S \<longleftrightarrow>  \<not> (lin_indpt (S \<union> {v}))"*)
  have 9: "\<not>(maximal A (\<lambda>S. S\<subseteq>carrier V \<and> lin_indpt S))"
  proof - 
    from 1 4 5 7 have 8: "(\<exists>B. A \<subseteq> B  \<and> B \<subseteq> carrier V \<and> lin_indpt B \<and> B \<noteq> A)"
      apply (rule_tac x="A\<union>{v}" in exI) 
      by auto    
    from 8 show ?thesis 
      apply (unfold maximal_def) 
      by simp
  qed
  from h1 9 show False by auto
qed

text \<open>A minimal generating set is linearly independent.\<close>
lemma (in vectorspace) min_gen_is_li:
  fixes A
  assumes h1: "minimal A (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S)"
  shows "lin_indpt A"
proof (rule ccontr)
  assume 0: "\<not>lin_indpt A"
  from h1 have 1: " A\<subseteq> carrier V \<and> gen_set A" by (unfold minimal_def, auto)
  from 1 have 2: "span A = carrier V" by auto
  from 0 1 obtain a v A' where 
    3: "finite A' \<and> A'\<subseteq>A \<and> a \<in> A' \<rightarrow> carrier K \<and> LinearCombinations.module.lincomb V a A' = \<zero>\<^bsub>V\<^esub> \<and> v \<in> A' \<and> a v \<noteq> \<zero>\<^bsub>K\<^esub>" 
    by (unfold lin_dep_def, auto)
  have 4: "gen_set (A-{v})"
  proof - 
    from 1 3 have 5: "v\<in>span (A'-{v})" 
      apply (intro lincomb_isolate[where a="a" and v="v"]) 
           by auto
    from 3 5 have 51: "v\<in>span (A-{v})"
      apply (intro subsetD[where ?A="span (A'-{v})" and ?B="span (A-{v})" and ?c="v"])
       by (intro span_is_monotone, auto)
    from 1 have 6: "A\<subseteq>span A" apply (intro in_own_span) by auto
    from 1 51 have 7: "span (A-{v}) = span ((A-{v})\<union>{v})" apply (intro already_in_span) by auto
    from 3 have 8: "A =  ((A-{v})\<union>{v})" by auto
    from 2 7 8 have 9:"span (A-{v}) = carrier V" by auto (*can't use 3 directly :( *)
    from 9 show ?thesis  by auto
  qed
  have 10: "\<not>(minimal A (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S))"
  proof - 
    from 1 3 4 have 11: "(\<exists>B. A \<supseteq> B \<and> B \<subseteq> carrier V \<and> gen_set B \<and> B \<noteq> A)"
      apply (rule_tac x="A-{v}" in exI) 
      by auto
    from 11 show ?thesis 
      apply (unfold minimal_def) 
      by auto
  qed
  from h1 10 show False by auto
qed

text \<open>Given that some finite set satisfies $P$, there is a minimal set that satisfies $P$.\<close>
lemma minimal_exists:
  fixes A P
  assumes h1: "finite A" and h2: "P A"
  shows "\<exists>B. B\<subseteq>A \<and> minimal B P"
using h1 h2 
proof (induct "card A"  arbitrary: A rule: less_induct)
case (less A)
  show ?case
  proof (cases "card A = 0")  
  case True
    from True less.hyps less.prems show ?thesis
      apply (rule_tac x="{}" in exI)
      apply (unfold minimal_def)
      by  auto
  next
  case False
    show ?thesis
    proof (cases "minimal A P")
      case True
        then show ?thesis 
          apply (rule_tac x="A" in exI) 
          by auto
      next
      case False
        have 2: "\<not>minimal A P" by fact
        from less.prems 2 have 3: "\<exists>B. P B \<and> B \<subseteq> A \<and> B\<noteq>A"
          apply (unfold minimal_def) 
          by auto
        from 3 obtain B where 4: "P B \<and> B \<subset> A \<and> B\<noteq>A" by auto
        from 4 have 5: "card B < card A" by (metis less.prems(1) psubset_card_mono)
        from less.hyps less.prems 3 4 5 have 6: "\<exists>C\<subseteq>B. minimal C P" 
          apply (intro less.hyps) 
            apply auto
          by (metis rev_finite_subset)
        from 6 obtain C where 7: "C\<subseteq>B \<and> minimal C P" by auto
        from 4 7 show ?thesis 
          apply (rule_tac x="C" in exI) 
          apply (unfold minimal_def) 
          by auto
     qed
   qed
qed

text \<open>If $V$ is finite-dimensional, then any linearly independent set is finite.\<close>
lemma (in vectorspace) fin_dim_li_fin:
  assumes fd: "fin_dim" and li: "lin_indpt A" and inC: "A\<subseteq>carrier V"
  shows fin: "finite A"
proof (rule ccontr)
  assume A: "\<not>finite A"
  from fd obtain C where C: "finite C \<and> C\<subseteq>carrier V \<and> gen_set C" by (unfold fin_dim_def, auto)
  from A obtain B where B: "B\<subseteq>A\<and> finite B \<and> card B = card C + 1"
    by (metis infinite_arbitrarily_large) 
  from B li have liB: "lin_indpt B" 
    by (intro subset_li_is_li[where ?A="A" and ?B="B"], auto)
  from B C liB inC have "card B \<le> card C" by (intro li_smaller_than_gen, auto) 
  from this B show False by auto
qed

text \<open>If $V$ is finite-dimensional (has a finite generating set), then a finite basis exists.\<close>
lemma (in vectorspace) finite_basis_exists:
  assumes h1: "fin_dim"
  shows "\<exists>\<beta>. finite \<beta> \<and> basis \<beta>"
proof -
  from h1 obtain A where 1: "finite A \<and> A\<subseteq>carrier V \<and> gen_set A" by (metis fin_dim_def)
  hence 2: "\<exists>\<beta>. \<beta>\<subseteq>A \<and> minimal \<beta> (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S)" 
    apply (intro minimal_exists) 
     by auto
  then obtain \<beta> where 3: "\<beta>\<subseteq>A \<and> minimal \<beta> (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S)" by auto
  hence 4: "lin_indpt \<beta>" apply (intro min_gen_is_li) by auto
  moreover from 3 have 5: "gen_set \<beta> \<and> \<beta>\<subseteq>carrier V" apply (unfold minimal_def) by auto
  moreover from 1 3 have 6: "finite \<beta>" by (auto simp add: finite_subset)
  ultimately show ?thesis apply (unfold basis_def) by auto
qed
text\<open>
The proof is as follows.
\begin{enumerate}
\item Because $V$ is finite-dimensional, there is a finite generating set 
(we took this as our definition of finite-dimensional).
\item Hence, there is a minimal $\beta \subseteq A$ such that $\beta$ generates $V$.
\item $\beta$ is linearly independent because a minimal generating set is linearly independent.
\end{enumerate}
Finally, $\beta$ is a basis because it is both generating and linearly independent.
\<close>

text \<open>Any linearly independent set has cardinality at most equal to the dimension.\<close>
lemma (in vectorspace) li_le_dim: 
  fixes A
  assumes fd: "fin_dim" and c: "A\<subseteq>carrier V" and l: "lin_indpt A"
  shows "finite A" "card A \<le> dim"
proof  -
  from fd c l show fa: "finite A" by (intro fin_dim_li_fin, auto)
  from fd obtain \<beta> where 1: "finite \<beta> \<and> basis \<beta>" 
    by (metis finite_basis_exists)
  from assms fa 1 have 2: "card A \<le> card \<beta>" 
    apply (intro li_smaller_than_gen, auto) 
      by (unfold basis_def, auto)
  from assms 1 have 3: "dim = card \<beta>" by (intro dim_basis, auto)
  from 2 3 show "card A \<le> dim" by auto
qed

text \<open>Any generating set has cardinality at least equal to the dimension.\<close>
lemma (in vectorspace) gen_ge_dim: 
  fixes A
  assumes fa: "finite A" and c: "A\<subseteq>carrier V" and l: "gen_set A"
  shows "card A \<ge> dim"
proof  -
  from assms have fd: "fin_dim" by (unfold fin_dim_def, auto)
  from fd obtain \<beta> where 1: "finite \<beta> \<and> basis \<beta>" by (metis finite_basis_exists)
  from assms 1 have 2: "card A \<ge> card \<beta>" 
    apply (intro li_smaller_than_gen, auto) 
     by (unfold basis_def, auto)
  from assms 1 have 3: "dim = card \<beta>" by (intro dim_basis, auto)
  from 2 3 show ?thesis by auto
qed


text \<open>If there is an upper bound on the cardinality of sets satisfying $P$, then there is a maximal
set satisfying $P$.\<close>
lemma maximal_exists:
  fixes P B N
  assumes maxc: "\<And>A. P A \<Longrightarrow> finite A \<and> (card A \<le>N)" and b: "P B"
  shows "\<exists>A. finite A \<and> maximal A P"
proof -
(*take the maximal*)
  let ?S="{card A| A. P A}"
  let ?n="Max ?S"
  from maxc have 1:"finite ?S"
    apply (simp add: finite_nat_set_iff_bounded_le) by auto
  from 1 have 2: "?n\<in>?S"
    by (metis (mono_tags, lifting) Collect_empty_eq Max_in b) 
  from assms 2 have 3: "\<exists>A. P A \<and> finite A \<and> card A = ?n" 
    by auto
  from 3 obtain A where 4: "P A \<and> finite A \<and> card A = ?n" by auto
  from 1 maxc have 5: "\<And>A. P A \<Longrightarrow> finite A \<and> (card A \<le>?n)"
    by (metis (mono_tags, lifting) Max.coboundedI mem_Collect_eq) 
  from 4 5 have 6: "maximal A P"
    apply (unfold maximal_def)
    by (metis card_seteq)
  from 4 6 show ?thesis by auto
qed

text \<open>Any maximal linearly independent set is a basis.\<close>
lemma (in vectorspace) max_li_is_basis:
  fixes A
  assumes h1: "maximal A (\<lambda>S. S\<subseteq>carrier V \<and> lin_indpt S)"
  shows "basis A"
proof - 
  from h1 have 1: "gen_set A" by (rule max_li_is_gen)
  from assms 1 show ?thesis by (unfold basis_def maximal_def, auto)
qed

text \<open>Any minimal linearly independent set is a generating set.\<close>
lemma (in vectorspace) min_gen_is_basis:
  fixes A
  assumes h1: "minimal A (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S)"
  shows "basis A"
proof - 
  from h1 have 1: "lin_indpt A" by (rule min_gen_is_li)
  from assms 1 show ?thesis by (unfold basis_def minimal_def, auto)
qed

text \<open>Any linearly independent set with cardinality at least the dimension is a basis.\<close>
lemma (in vectorspace) dim_li_is_basis:
  fixes A
  assumes fd: "fin_dim" and fa: "finite A" and ca: "A\<subseteq>carrier V" and li: "lin_indpt A" 
    and d: "card A \<ge> dim" (*\<ge>*)
  shows "basis A"
proof - 
  from fd have 0: "\<And>S. S\<subseteq>carrier V \<and> lin_indpt S \<Longrightarrow> finite S \<and> card S \<le>dim"
    by (auto intro: li_le_dim)
(*fin_dim_li_fin*)
  from 0 assms have h1:  "finite A \<and> maximal A (\<lambda>S.  S\<subseteq>carrier V \<and> lin_indpt S)"
    apply (unfold maximal_def) 
    apply auto
    by (metis card_seteq eq_iff)
  from h1 show ?thesis by (auto intro: max_li_is_basis)
qed

text \<open>Any generating set with cardinality at most the dimension is a basis.\<close>
lemma (in vectorspace) dim_gen_is_basis:
  fixes A
  assumes fa: "finite A" and ca: "A\<subseteq>carrier V" and li: "gen_set A" 
    and d: "card A \<le> dim"
  shows "basis A"
proof - 
  have 0: "\<And>S. finite S\<and> S\<subseteq>carrier V \<and> gen_set S \<Longrightarrow> card S \<ge>dim"
    by (intro gen_ge_dim, auto)
(*li_le_dim*)
  from 0 assms have h1:  "minimal A (\<lambda>S. finite S \<and> S\<subseteq>carrier V \<and> gen_set S)"
    apply (unfold minimal_def) 
    apply auto
    by (metis card_seteq eq_iff)
  (*slightly annoying: we have to get rid of "finite S" inside.*)
  from h1 have h: "\<And>B. B \<subseteq> A \<and> B \<subseteq> carrier V \<and> LinearCombinations.module.gen_set K V B \<Longrightarrow> B = A"
  proof - 
    fix B
    assume asm: "B \<subseteq> A \<and> B \<subseteq> carrier V \<and> LinearCombinations.module.gen_set K V B" 
    from asm h1 have "finite B" 
      apply (unfold minimal_def) 
       apply (intro finite_subset[where ?A="B" and ?B="A"]) 
       by auto
    from h1 asm this show "?thesis B" apply (unfold minimal_def) by simp
  qed
  from h1 h have h2: "minimal A (\<lambda>S. S\<subseteq>carrier V \<and> gen_set S)" 
    apply (unfold minimal_def)
    by presburger
  from h2 show ?thesis by (rule min_gen_is_basis)
qed

text \<open>$\beta$ is a basis iff for all $v\in V$, there exists a unique $(a_v)_{v\in S}$ such that
$\sum_{v\in S} a_v v=v$.\<close>
lemma (in vectorspace) basis_criterion:
  assumes A_fin: "finite A" and AinC: "A\<subseteq>carrier V"
  shows "basis A \<longleftrightarrow> (\<forall>v. v\<in> carrier V \<longrightarrow>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v))"
proof -
  have 1: "\<not>(\<forall>v.  v\<in> carrier V \<longrightarrow>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v)) \<Longrightarrow> \<not>basis A"
  proof - 
    assume "\<not>(\<forall>v.  v\<in> carrier V \<longrightarrow>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v))"
    then obtain v where v: "v\<in> carrier V \<and> \<not>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v)" by metis
    (*either there is more than 1 rep, or no reps*)
    from v have vinC: "v\<in>carrier V" by auto
    from v have "\<not>(\<exists> a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v) \<or>  (\<exists> a b. 
      a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v \<and> b\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb b A = v 
      \<and> a\<noteq>b)" by metis
    then show ?thesis
    proof
      assume a: "\<not>(\<exists> a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v)"
      from A_fin AinC have "\<And>a. a\<in>A \<rightarrow> carrier K \<Longrightarrow> lincomb a A = lincomb (restrict a A) A" 
        unfolding lincomb_def restrict_def
        by (simp cong: finsum_cong add: ring_subset_carrier coeff_in_ring)
      with a have "\<not>(\<exists> a.  a\<in>A \<rightarrow> carrier K \<and> lincomb a A = v)" by auto
      with A_fin AinC have "v\<notin>span A"
        using finite_in_span by blast 
      with AinC v show "\<not>(basis A)" by (unfold basis_def, auto)
    next
      assume a2: "(\<exists> a b. 
        a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v \<and> b\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb b A = v 
        \<and> a\<noteq>b)"
      then obtain a b where ab: "a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v \<and> b\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb b A = v 
        \<and> a\<noteq>b" by metis
      from ab obtain w where w: "w\<in>A \<and> a w \<noteq> b w" apply (unfold PiE_def, auto)
        by (metis extensionalityI)
      let ?c="\<lambda> x. (if x\<in>A then ((a x) \<ominus>\<^bsub>K\<^esub> (b x)) else undefined)"
      from ab have a_fun: "a\<in>A \<rightarrow> carrier K" 
               and b_fun: "b\<in>A \<rightarrow> carrier K" 
        by (unfold PiE_def, auto)
      from w a_fun b_fun have abinC: "a w \<in>carrier K" "b w \<in>carrier K" by auto

      from abinC w have nz: "a w \<ominus>\<^bsub>K\<^esub> b w \<noteq> \<zero>\<^bsub>K\<^esub>" 
        by auto (*uses M.minus_other_side*)
      from A_fin AinC a_fun b_fun ab vinC have a_b:
      "LinearCombinations.module.lincomb V (\<lambda>x. if x \<in> A then a x \<ominus>\<^bsub>K\<^esub> b x else undefined) A = \<zero>\<^bsub>V\<^esub>"
        by (simp cong: lincomb_cong add: coeff_in_ring lincomb_diff)
      from A_fin AinC ab w v nz a_b have "lin_dep A"
        apply (intro lin_dep_crit[where ?A="A" and ?a="?c" and ?v="w"])
             apply (auto simp add: PiE_def)
        by auto
      thus "\<not>basis A" by (unfold basis_def, auto)
    qed
  qed
  have 2: "(\<forall>v. v\<in> carrier V \<longrightarrow>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v)) \<Longrightarrow> basis A"
  proof -
    assume b1: "(\<forall>v. v\<in> carrier V \<longrightarrow>(\<exists>! a.  a\<in>A \<rightarrow>\<^sub>E carrier K \<and> lincomb a A = v))" 
      (is "(\<forall>v. v\<in> carrier V \<longrightarrow>(\<exists>! a.  ?Q a v))")
    from b1 have b2: "(\<forall>v.  v\<in> carrier V \<longrightarrow>(\<exists> a.  a\<in>A \<rightarrow> carrier K \<and> lincomb a A = v))" 
      apply (unfold PiE_def) 
      by blast 
    from A_fin AinC b2 have "gen_set A"
      apply (unfold span_def)
      by blast
    from b1 have A_li: "lin_indpt A"
    proof -
      let ?z="\<lambda> x. (if (x\<in>A) then \<zero>\<^bsub>K\<^esub> else undefined)" 
      from A_fin AinC have zero: "?Q ?z \<zero>\<^bsub>V\<^esub>" 
        by (unfold PiE_def extensional_def lincomb_def, auto simp add: ring_subset_carrier)
        (*uses finsum_all0*)
      from A_fin AinC show ?thesis 
      proof (rule finite_lin_indpt2)
        fix a
        assume a_fun: "a \<in> A \<rightarrow> carrier K" and
          lc_a: "LinearCombinations.module.lincomb V a A = \<zero>\<^bsub>V\<^esub>"
        from a_fun have a_res: "restrict a A \<in> A \<rightarrow>\<^sub>E carrier K" by auto
        from a_fun A_fin AinC lc_a have 
          lc_a_res: "LinearCombinations.module.lincomb V (restrict a A) A = \<zero>\<^bsub>V\<^esub>"
          apply (unfold lincomb_def restrict_def)
          by (simp cong: finsum_cong2 add: coeff_in_ring ring_subset_carrier)
        from a_fun a_res lc_a_res zero b1 have "restrict a A = ?z" by auto
        from this show "\<forall>v\<in>A. a v = \<zero>\<^bsub>K\<^esub>" 
          apply (unfold restrict_def)
          by meson
      qed
    qed
    have A_gen: "gen_set A" 
    proof - 
      from AinC have dir1: "span A\<subseteq>carrier V" by (rule span_is_subset2)
      have dir2: "carrier V\<subseteq>span A"
      proof (auto)
        fix v
        assume v: "v\<in>carrier V"
        from v b2 obtain a where "a\<in>A \<rightarrow> carrier K \<and> lincomb a A = v" by auto
        from this A_fin AinC show "v\<in>span A" by (subst finite_span, auto)
      qed
      from dir1 dir2 show ?thesis by auto
    qed
    from A_li A_gen AinC show "basis A" by (unfold basis_def, auto)
  qed
  from 1 2 show ?thesis by satx
qed

lemma (in linear_map) surj_imp_imT_carrier:
  assumes surj: "T` (carrier V) = carrier W"
  shows "(imT) = carrier W" 
  by (simp add: surj im_def)

subsection \<open>The rank-nullity (dimension) theorem\<close>

text \<open>If $V$ is finite-dimensional and $T:V\to W$ is a linear map, then $\text{dim}(\text{im}(T))+
\text{dim}(\text{ker}(T)) = \text{dim} V$. Moreover, we prove that if $T$ is surjective 
  linear-map between $V$ and $W$, where $V$ is finite-dimensional, then also $W$ is finite-dimensional.\<close>
theorem (in linear_map) rank_nullity_main: 
  assumes fd: "V.fin_dim"
  shows "(vectorspace.dim K (W.vs imT)) + (vectorspace.dim K (V.vs kerT)) = V.dim"       
    "T ` (carrier V) = carrier W \<Longrightarrow> W.fin_dim"
proof - 
  \<comment> \<open>First interpret kerT, imT as vectorspaces\<close>
  have subs_ker: "subspace K kerT V" by (intro kerT_is_subspace)
  from subs_ker have vs_ker: "vectorspace K (V.vs kerT)" by (rule V.subspace_is_vs)
  from vs_ker interpret ker: vectorspace K "(V.vs kerT)" by auto
  have kerInC: "kerT\<subseteq>carrier V" by (unfold ker_def, auto)

  have subs_im: "subspace K imT W" by (intro imT_is_subspace)  
  from subs_im have vs_im: "vectorspace K (W.vs imT)" by (rule W.subspace_is_vs)
  from vs_im interpret im: vectorspace K "(W.vs imT)" by auto
  have imInC: "imT\<subseteq>carrier W" by (unfold im_def, auto)
  (* obvious fact *)
  have zero_same[simp]: "\<zero>\<^bsub>V.vs kerT\<^esub> = \<zero>\<^bsub>V\<^esub>" apply (unfold ker_def) by auto
  \<comment> \<open>Show ker T has a finite basis. This is not obvious. Show that any linearly independent set 
has size at most that of V. There exists a maximal linearly independent set, which is the basis.\<close>
  have every_li_small: "\<And>A. (A \<subseteq> kerT)\<and> ker.lin_indpt A \<Longrightarrow> 
    finite A \<and> card A \<le> V.dim"
  proof - 
    fix A
    assume eli_asm: "(A \<subseteq> kerT)\<and> ker.lin_indpt A"
    (*annoying: I can't just use subst V.module.span_li_not_depend(2) in the show ?thesis 
    statement because it doesn't appear in the conclusion.*)
    note V.module.span_li_not_depend(2)[where ?N="kerT" and ?S="A"] 
    from this subs_ker fd eli_asm kerInC show "?thesis A" 
      apply (intro conjI) 
       by (auto intro!: V.li_le_dim)
  qed
  from every_li_small have exA: 
    "\<exists>A. finite A \<and> maximal A (\<lambda>S. S\<subseteq>carrier (V.vs kerT) \<and> ker.lin_indpt S)"
    apply (intro maximal_exists[where ?N="V.dim" and ?B="{}"])
     apply auto
    by (unfold ker.lin_dep_def, auto)
  from exA obtain A where A:" finite A \<and> maximal A (\<lambda>S. S\<subseteq>carrier (V.vs kerT) \<and> ker.lin_indpt S)" 
    by blast
  hence finA: "finite A" and Ainker: "A\<subseteq>carrier (V.vs kerT)" and AinC: "A\<subseteq>carrier V"
    by (unfold maximal_def ker_def, auto)
  \<comment> \<open>We obtain the basis A of kerT. It is also linearly independent when considered in V rather
than kerT\<close>
  from A have Abasis: "ker.basis A" 
    by (intro ker.max_li_is_basis, auto) 
  from subs_ker Abasis have spanA: "V.module.span A = kerT"
    apply (unfold ker.basis_def)
    by (subst sym[OF V.module.span_li_not_depend(1)[where ?N="kerT"]], auto)
  from Abasis have Akerli: "ker.lin_indpt A" 
    apply (unfold ker.basis_def) 
    by auto
  from subs_ker Ainker Akerli have Ali: "V.module.lin_indpt A" 
    by (auto simp add: V.module.span_li_not_depend(2))
  txt\<open>Use the replacement theorem to find C such that $A\cup C$ is a basis of V.\<close>
  from fd obtain B where B: "finite B\<and> V.basis B" by (metis V.finite_basis_exists)
  from B have Bfin: "finite B" and Bbasis:"V.basis B" by auto
  from B have Bcard: "V.dim = card B" by (intro V.dim_basis, auto) 
  from Bbasis have 62: "V.module.span B = carrier V" 
    by (unfold V.basis_def, auto)
  from A Abasis Ali B vs_ker have "\<exists>C. finite C \<and> C\<subseteq>carrier V \<and> C\<subseteq> V.module.span B \<and> C\<inter>A={} 
      \<and> int (card C) \<le> (int (card B)) - (int (card A)) \<and> (V.module.span (A \<union> C) = V.module.span B)"
    apply (intro V.replacement)
    apply (unfold vectorspace.basis_def V.basis_def)
      by (unfold ker_def, auto)
  txt \<open>From replacement we got $|C|\leq |B|-|A|$. Equality must actually hold, because no generating set
can be smaller than $B$. Now $A\cup C$ is a maximal generating set, hence a basis; its cardinality
equals the dimension.\<close>
  txt \<open>We claim that $T(C)$ is basis for $\text{im}(T)$.\<close>
  then obtain C where C: "finite C \<and> C\<subseteq>carrier V \<and> C\<subseteq> V.module.span B \<and> C\<inter>A={} 
    \<and> int (card C) \<le> (int (card B)) - (int (card A)) \<and> (V.module.span (A \<union> C) = V.module.span B)" by auto
  hence Cfin: "finite C" and CinC: "C\<subseteq>carrier V" and CinspanB: " C\<subseteq>V.module.span B" and CAdis: "C\<inter>A={}" 
    and Ccard: "int (card C) \<le> (int (card B)) - (int (card A))"
    and ACspanB: "(V.module.span (A \<union> C) = V.module.span B)" by auto
  from C have cardLe: "card A + card C \<le> card B" by auto
  from B C have ACgen: "V.module.gen_set (A\<union>C)" apply (unfold V.basis_def) by auto
  from finA C ACgen AinC B have cardGe: "card (A\<union>C) \<ge> card B" by (intro V.li_smaller_than_gen, unfold V.basis_def, auto)
  from finA C have cardUn: "card (A\<union>C)\<le>  card A + card C"
    by (metis Int_commute card_Un_disjoint le_refl)
  from cardLe cardUn cardGe Bcard have cardEq: 
    "card (A\<union>C) = card A + card C" 
    "card (A\<union>C) = card B" 
    "card (A\<union>C) = V.dim" 
    by auto
  from Abasis C cardEq have disj: "A\<inter>C={}" by auto
  from finA AinC C cardEq 62 have ACfin: "finite (A\<union>C)" and ACbasis: "V.basis (A\<union>C)" 
    by (auto intro!: V.dim_gen_is_basis) 
  have lm: "linear_map K V W T"..
  txt \<open>Let $C'$ be the image of $C$ under $T$. We will show $C'$ is a basis for $\text{im}(T)$.\<close>
  let ?C' = "T`C"
  from Cfin have C'fin: "finite ?C'" by auto
  from AinC C have cim: "?C'\<subseteq>imT" by (unfold im_def, auto)

  txt \<open>"There is a subtle detail: we first have to show $T$ is injective on $C$.\<close>
  txt \<open>We establish that no nontrivial linear combination of $C$ can have image 0 under $T$, 
because that would mean it is a linear combination of $A$, giving that $A\cup C$ is linearly dependent, 
contradiction. We use this result in 2 ways: (1) if $T$ is not injective on $C$, then we obtain $v$, $w\in C$ 
such that $v-w$ is in the kernel, contradiction, (2) if $T(C)$ is linearly dependent, 
taking the inverse image of that linear combination gives a linear combination of $C$ in the kernel, 
contradiction. Hence $T$ is injective on $C$ and $T(C)$ is linearly independent.\<close>
  have lc_in_ker: "\<And>d D v. \<lbrakk>D\<subseteq>C; d\<in>D\<rightarrow>carrier K; T (V.module.lincomb d D) = \<zero>\<^bsub>W\<^esub>; 
    v\<in>D; d v \<noteq>\<zero>\<^bsub>K\<^esub>\<rbrakk>\<Longrightarrow>False"
  proof -
    fix d D v
    assume D: "D\<subseteq>C" and d: "d\<in>D\<rightarrow>carrier K" and T0: "T (V.module.lincomb d D) = \<zero>\<^bsub>W\<^esub>" 
      and v: "v\<in>D" and dvnz: "d v \<noteq>\<zero>\<^bsub>K\<^esub>"
    from D Cfin have Dfin: "finite D"  by (auto intro: finite_subset)
    from D CinC have DinC: "D\<subseteq>carrier V" by auto
    from T0 d Dfin DinC have lc_d: "V.module.lincomb d D\<in>kerT" 
      by (unfold ker_def, auto)
    from lc_d spanA AinC have  "\<exists>a' A'. A'\<subseteq>A \<and> a'\<in>A'\<rightarrow>carrier K \<and>
       V.module.lincomb a' A'= V.module.lincomb d D" 
      by (intro V.module.in_span, auto)
    then obtain a' A' where a': "A'\<subseteq>A \<and> a'\<in>A'\<rightarrow>carrier K \<and>
      V.module.lincomb d D = V.module.lincomb a' A'" 
      by metis
    hence  A'sub: "A'\<subseteq>A" and a'fun: "a'\<in>A'\<rightarrow>carrier K" 
      and a'_lc:"V.module.lincomb d D = V.module.lincomb a' A'"  by auto
    from a' finA Dfin have A'fin: "finite (A')"  by (auto intro: finite_subset)
    from AinC A'sub have A'inC: "A'\<subseteq>carrier V" by auto
    let ?e = "(\<lambda>v. if v \<in> A' then a' v else \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<otimes>\<^bsub>K\<^esub> d v)"
    from a'fun d have e_fun: "?e \<in> A' \<union> D \<rightarrow> carrier K" 
      apply (unfold Pi_def) 
      by auto
    from
      A'fin Dfin (*finiteness*)
      A'inC DinC (*in carrier*)
      a'fun d e_fun (*coefficients valid*)
      disj D A'sub (*A and C disjoint*)
    have lccomp1:
      "V.module.lincomb a' A' \<oplus>\<^bsub>V\<^esub> \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<odot>\<^bsub>V\<^esub> V.module.lincomb d D = 
        V.module.lincomb (\<lambda>v. if v\<in>A' then a' v else \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<otimes>\<^bsub>K\<^esub> d v) (A'\<union>D)"
      apply (subst sym[OF V.module.lincomb_smult])
          apply (simp_all)
      apply (subst V.module.lincomb_union2)
           by (auto)
    from
      A'fin (*finiteness*)
      A'inC (*in carrier*)
      a'fun (*coefficients valid*)
    have lccomp2: 
      "V.module.lincomb a' A' \<oplus>\<^bsub>V\<^esub> \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<odot>\<^bsub>V\<^esub> V.module.lincomb d D = 
      \<zero>\<^bsub>V\<^esub>" 
      by (simp add: a'_lc 
        V.module.smult_minus_1  V.module.M.r_neg)
    from lccomp1 lccomp2 have lc0: "V.module.lincomb (\<lambda>v. if v\<in>A' then a' v else \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<otimes>\<^bsub>K\<^esub> d v) (A'\<union>D)
      =\<zero>\<^bsub>V\<^esub>" by auto
    from disj a' v D have v_nin: "v\<notin>A'" by auto
    from A'fin Dfin (*finiteness*)
      A'inC DinC (*in carrier*)
      e_fun d (*coefficients valid*)
      A'sub D disj (*A' D are disjoint subsets*)
      v dvnz (*d v is nonzero coefficient*)
      lc0
    have AC_ld: "V.module.lin_dep (A\<union>C)" 
      apply (intro V.module.lin_dep_crit[where ?A="A'\<union>D" and 
        ?S="A\<union>C" and ?a="\<lambda>v. if v\<in>A' then a' v else \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>\<otimes>\<^bsub>K\<^esub> d v" and ?v="v"])
           by (auto dest: integral)
    from AC_ld ACbasis show False by (unfold V.basis_def, auto)
  qed
  have C'_card: "inj_on T C" "card C = card ?C'"
  proof -
    show "inj_on T C"
    proof (rule ccontr)
      assume "\<not>inj_on T C"
      then obtain v w where "v\<in>C" "w\<in>C" "v\<noteq>w" "T v = T w" by (unfold inj_on_def, auto) 
      from this CinC show False 
        apply (intro lc_in_ker[where ?D1="{v,w}" and ?d1="\<lambda>x. if x=v then \<one>\<^bsub>K\<^esub> else \<ominus>\<^bsub>K\<^esub>\<one>\<^bsub>K\<^esub>"
          and ?v1="v"])
            by (auto simp add: V.module.lincomb_def hom_sum ring_subset_carrier 
              W.module.smult_minus_1 r_neg T_im)
    qed
    from this Cfin show "card C = card ?C'"
      by (metis card_image) 
  qed
  let ?f="the_inv_into C T"
  have f: "\<And>x. x\<in>C \<Longrightarrow> ?f (T x) = x" "\<And>y. y\<in>?C' \<Longrightarrow> T (?f y) = y"
    apply (insert C'_card(1))
     apply (metis the_inv_into_f_f)
    by (metis f_the_inv_into_f)
(*We show C' is a basis for the image. First we show it is linearly independent.*)
  have C'_li: "im.lin_indpt ?C'"
  proof (rule ccontr)
    assume Cld: "\<not>im.lin_indpt ?C'"
    from Cld cim subs_im have CldW: "W.module.lin_dep ?C'" 
      apply (subst sym[OF W.module.span_li_not_depend(2)[where ?S="T`C" and ?N="imT"]]) 
        by auto
    from C CldW have "\<exists>c' v'. (c'\<in> (?C'\<rightarrow>carrier K)) \<and> (W.module.lincomb c' ?C' = \<zero>\<^bsub>W\<^esub>) 
      \<and> (v'\<in>?C') \<and> (c' v'\<noteq> \<zero>\<^bsub>K\<^esub>)" by (intro W.module.finite_lin_dep, auto)
    then obtain c' v' where c': "(c'\<in> (?C'\<rightarrow>carrier K)) \<and> (W.module.lincomb c' ?C' = \<zero>\<^bsub>W\<^esub>) 
      \<and> (v'\<in>?C') \<and> (c' v'\<noteq> \<zero>\<^bsub>K\<^esub>)" by auto
    hence c'fun: "(c'\<in> (?C'\<rightarrow>carrier K))" and c'lc: "(W.module.lincomb c' ?C' = \<zero>\<^bsub>W\<^esub>)" and 
      v':"(v'\<in>?C')" and cvnz: "(c' v'\<noteq> \<zero>\<^bsub>K\<^esub>)" by auto
(*can't get c' directly with metis/auto with W.module.finite_lin_dep*)
    txt \<open>We take the inverse image of $C'$ under $T$ to get a linear combination of $C$ that is 
in the kernel and hence a linear combination of $A$. This contradicts $A\cup C$ being linearly
independent.\<close>
    let ?c="\<lambda>v. c' (T v)"
    from c'fun have c_fun: "?c\<in> C\<rightarrow>carrier K" by auto
    from Cfin (*C finite*)
      c_fun c'fun (*coefficients valid*)
      C'_card (*bijective*)
      CinC (*C in carrier*)
      f (*inverse to T*) 
      c'lc (*lc c' = 0*)
    have "T (V.module.lincomb ?c C) = \<zero>\<^bsub>W\<^esub>"
      apply (unfold V.module.lincomb_def W.module.lincomb_def)
      apply (subst hom_sum, auto)
      apply (simp cong: finsum_cong add: ring_subset_carrier coeff_in_ring)
      apply (subst finsum_reindex[where ?f="\<lambda>w. c' w \<odot>\<^bsub>W\<^esub> w" and ?h="T" and ?A="C", THEN sym])
         by auto
    with f c'fun cvnz v' show False
      by (intro lc_in_ker[where ?D1="C" and ?d1="?c" and ?v1="?f v'"], auto)
  qed
  have C'_gen: "im.gen_set ?C'"
  proof - 
    have C'_span: "span ?C' = imT"
    proof (rule equalityI)
      from cim subs_im show "W.module.span ?C' \<subseteq> imT"
        by (intro span_is_subset, unfold subspace_def, auto)
    next
      show "imT\<subseteq>W.module.span ?C'"
      proof (auto)
        fix w
        assume w: "w\<in>imT"
        from this finA Cfin AinC CinC obtain v where v_inC: "v\<in>carrier V" and w_eq_T_v: "w= T v" 
          by (unfold im_def image_def, auto)
        from finA Cfin AinC CinC v_inC ACgen have "\<exists>a.  a \<in> A\<union>C \<rightarrow> carrier K\<and> V.module.lincomb a (A\<union>C) = v"
          by (intro V.module.finite_in_span, auto)
        then obtain a where 
          a_fun: "a \<in> A\<union>C \<rightarrow> carrier K" and
          lc_a_v: "v= V.module.lincomb a (A\<union>C)"
          by auto
        let ?a'="\<lambda>v. a (?f v)"
        from finA Cfin AinC CinC a_fun disj Ainker f C'_card have Tv: "T v = W.module.lincomb ?a' ?C'"
          apply (subst lc_a_v)
          apply (subst V.module.lincomb_union, simp_all) (*Break up the union A\<union>C*)
          apply (unfold lincomb_def V.module.lincomb_def)
          apply (subst hom_sum, auto) (*Take T inside the sum over A*)
          apply (simp add: subsetD coeff_in_ring
            hom_sum (*Take T inside the sum over C*)
            T_ker (*all terms become 0 because the vectors are in the kernel.*)
            ) 
          apply (subst finsum_reindex[where ?h="T" and ?f="\<lambda>v. ?a' v\<odot>\<^bsub>W\<^esub> v"], auto)
           by (auto cong: finsum_cong simp add: coeff_in_ring ring_subset_carrier)
        from a_fun f have a'_fun: "?a'\<in>?C' \<rightarrow> carrier K" by auto
        from C'fin CinC this w_eq_T_v a'_fun Tv show "w \<in> LinearCombinations.module.span K W (T ` C)" 
          by (subst finite_span, auto)
      qed
    qed
    from this subs_im CinC show ?thesis 
      apply (subst span_li_not_depend(1))
        by (unfold im_def subspace_def, auto)
  qed
  from C'_li C'_gen C cim have C'_basis: "im.basis  (T`C)" 
    by (unfold im.basis_def, auto)
  have C_card_im: "card C = (vectorspace.dim K (W.vs imT))"
    using C'_basis C'_card(2) C'fin im.dim_basis by auto
  from finA Abasis have  "ker.dim = card A" by (rule ker.dim_basis)
  note * = this C_card_im cardEq 
  show "(vectorspace.dim K (W.vs imT)) + (vectorspace.dim K (V.vs kerT)) = V.dim"  using * by auto
  assume "T` (carrier V) = carrier W" 
  from * surj_imp_imT_carrier[OF this]  
  show "W.fin_dim" using C'_basis C'fin unfolding W.fin_dim_def im.basis_def by auto
qed

theorem (in linear_map) rank_nullity: 
  assumes fd: "V.fin_dim"
  shows "(vectorspace.dim K (W.vs imT)) + (vectorspace.dim K (V.vs kerT)) = V.dim"       
  by (rule rank_nullity_main[OF fd])


end

