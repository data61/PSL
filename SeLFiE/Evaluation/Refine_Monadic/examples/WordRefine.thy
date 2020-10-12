section \<open>Machine Words\<close>
theory WordRefine
imports "../Refine_Monadic" "HOL-Word.Word"
begin

text \<open>This theory provides a simple example to show refinement of natural
  numbers to machine words. The setup is not yet very elaborated, but shows 
  the direction to go.
\<close>

subsection \<open>Setup\<close>
definition [simp]: "word_nat_rel \<equiv> build_rel (unat) (\<lambda>_. True)"
lemma word_nat_RELEATES[refine_dref_RELATES]: 
  "RELATES word_nat_rel" by (simp add: RELATES_def)

lemma [simp, relator_props]: 
  "single_valued word_nat_rel" unfolding word_nat_rel_def
  by blast

lemma [simp]: "single_valuedp (\<lambda>c a. a = unat c)" 
  by (rule single_valuedpI) blast

lemma [simp, relator_props]: "single_valued (converse word_nat_rel)" 
  apply (auto intro!: injI)
  by (metis order_antisym order_eq_refl word_le_nat_alt)

lemmas [refine_hsimp] = 
  word_less_nat_alt word_le_nat_alt unat_sub iffD1[OF unat_add_lem]

subsection \<open>Example\<close>
type_synonym word32 = "32 word"

definition test :: "nat \<Rightarrow> nat \<Rightarrow> nat set nres" where "test x0 y0 \<equiv> do {
  let S={};
  (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
    let S=S\<union>{y};
    let x=x - 1;
    ASSERT (y<x0+y0);
    let y=y + 1;
    RETURN (S,x,y)
  }) (S,x0,y0);
  RETURN S
}"

lemma "y0>0 \<Longrightarrow> test x0 y0 \<le> SPEC (\<lambda>S. S={y0 .. y0 + x0 - 1})"
  \<comment> \<open>Choosen pre-condition to get least trouble when proving\<close>
  unfolding test_def
  apply (intro WHILE_rule[where I="\<lambda>(S,x,y). 
    x+y=x0+y0 \<and> x\<le>x0 \<and>
    S={y0 .. y0 + (x0-x) - 1}"] 
    refine_vcg)
  by auto

definition test_impl :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 set nres" where 
  "test_impl x y \<equiv> do {
    let S={};
    (S,_,_) \<leftarrow> WHILE (\<lambda>(S,x,y). x>0) (\<lambda>(S,x,y). do {
      let S=S\<union>{y}; 
      let x=x - 1;
      let y=y + 1;
      RETURN (S,x,y)
    }) (S,x,y);
    RETURN S
  }"

lemma test_impl_refine: 
  assumes "x'+y'<2^LENGTH(32)"
  assumes "(x,x')\<in>word_nat_rel" 
  assumes "(y,y')\<in>word_nat_rel" 
  shows "test_impl x y \<le> \<Down>(\<langle>word_nat_rel\<rangle>set_rel) (test x' y')"
proof -
  from assms show ?thesis
    unfolding test_impl_def test_def
    apply (refine_rcg)
    apply (refine_dref_type)
    apply (auto simp: refine_hsimp refine_rel_defs)
  done
qed

end
