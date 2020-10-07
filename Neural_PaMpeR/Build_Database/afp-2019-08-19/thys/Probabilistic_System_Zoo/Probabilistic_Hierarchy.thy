
(*<*)
theory Probabilistic_Hierarchy
imports
  "HOL-Probability.Probability"
  Nonempty_Bounded_Set
  "HOL-Eisbach.Eisbach"
begin
(*>*)

section \<open>Bisimilarity\<close>

definition bisimilar where
  "bisimilar Q s1 s2 x y \<equiv> (\<exists>R. R x y \<and> (\<forall>x y. R x y \<longrightarrow> Q R (s1 x) (s2 y)))"

abbreviation "bisimilar_mc \<equiv> bisimilar (\<lambda>R. rel_pmf R)"
abbreviation "bisimilar_dlts \<equiv> bisimilar (\<lambda>R. rel_fun (=) (rel_option R))"
abbreviation "bisimilar_lts \<equiv> bisimilar (\<lambda>R. rel_bset (rel_prod (=) R))"
abbreviation "bisimilar_react \<equiv> bisimilar (\<lambda>R. rel_fun (=) (rel_option (rel_pmf R)))"
abbreviation "bisimilar_lmc \<equiv> bisimilar (\<lambda>R. rel_prod (=) (rel_pmf R))"
abbreviation "bisimilar_lmdp \<equiv> bisimilar (\<lambda>R. rel_prod (=) (rel_nebset (rel_pmf R)))"
abbreviation "bisimilar_gen \<equiv> bisimilar (\<lambda>R. rel_option (rel_pmf (rel_prod (=) R)))"
abbreviation "bisimilar_str \<equiv> bisimilar (\<lambda>R. rel_sum (rel_pmf R) (rel_option (rel_prod (=) R)))"
abbreviation "bisimilar_alt \<equiv> bisimilar (\<lambda>R. rel_sum (rel_pmf R) (rel_bset (rel_prod (=) R)))"
abbreviation "bisimilar_sseg \<equiv> bisimilar (\<lambda>R. rel_bset (rel_prod (=) (rel_pmf R)))"
abbreviation "bisimilar_seg \<equiv> bisimilar (\<lambda>R. rel_bset (rel_pmf (rel_prod (=) R)))"
abbreviation "bisimilar_bun \<equiv> bisimilar (\<lambda>R. rel_pmf (rel_bset (rel_prod (=) R)))"
abbreviation "bisimilar_pz \<equiv> bisimilar (\<lambda>R. rel_bset (rel_pmf (rel_bset (rel_prod (=) R))))"
abbreviation "bisimilar_mg \<equiv> bisimilar (\<lambda>R. rel_bset (rel_pmf (rel_bset (rel_sum (rel_prod (=) R) R))))"


section \<open>Systems\<close>

codatatype mc = MC "mc pmf"
codatatype 'a dlts = DLTS "'a \<Rightarrow> 'a dlts option"
codatatype ('a, 'k) lts = LTS "('a \<times> ('a, 'k) lts) set['k]"
codatatype 'a react = React "'a \<Rightarrow> 'a react pmf option"
codatatype 'a lmc = LMC "'a \<times> 'a lmc pmf"
codatatype ('a, 'k) lmdp = LMDP "'a \<times> ('a, 'k) lmdp pmf set!['k]"
codatatype 'a gen = Gen "('a \<times> 'a gen) pmf option"
codatatype 'a str = Str "'a str pmf + ('a \<times> 'a str) option"
codatatype ('a, 'k) alt = Alt "('a, 'k) alt pmf + ('a \<times> ('a, 'k) alt) set['k]"
codatatype ('a, 'k) sseg = SSeg "('a \<times> ('a, 'k) sseg pmf) set['k]"
codatatype ('a, 'k) seg = Seg "('a \<times> ('a, 'k) seg) pmf set['k]"
codatatype ('a, 'k) bun = Bun "(('a \<times> ('a, 'k) bun) set['k]) pmf"
codatatype ('a, 'k1, 'k2) pz = PZ "(('a \<times> ('a, 'k1, 'k2) pz) set['k1]) pmf set['k2]"
codatatype ('a, 'k1, 'k2) mg = MG "(('a \<times> ('a, 'k1, 'k2) mg + ('a, 'k1, 'k2) mg) set['k1]) pmf set['k2]"


section \<open>Unfolds\<close>

primcorec unfold_mc :: "('a \<Rightarrow> 'a pmf) \<Rightarrow> 'a \<Rightarrow> mc" where
  "unfold_mc s x = MC (map_pmf (unfold_mc s) (s x))"

primcorec unfold_dlts :: "('a \<Rightarrow> 'b \<Rightarrow> 'a option) \<Rightarrow> 'a \<Rightarrow> 'b dlts" where
  "unfold_dlts s x = DLTS (map_option (unfold_dlts s) o s x)"

primcorec unfold_lts :: "('a \<Rightarrow> ('b \<times> 'a) set['k]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) lts" where
  "unfold_lts s x = LTS (map_bset (map_prod id (unfold_lts s)) (s x))"

primcorec unfold_react :: "('a \<Rightarrow> 'b \<Rightarrow> 'a pmf option) \<Rightarrow> 'a \<Rightarrow> 'b react" where
  "unfold_react s x = React (map_option (map_pmf (unfold_react s)) o s x)"

primcorec unfold_lmc :: "('a \<Rightarrow> 'b \<times> 'a pmf) \<Rightarrow> 'a \<Rightarrow> 'b lmc" where
  "unfold_lmc s x = LMC (map_prod id (map_pmf (unfold_lmc s)) (s x))"

primcorec unfold_lmdp :: "('a \<Rightarrow> 'b \<times> 'a pmf set!['k]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) lmdp" where
  "unfold_lmdp s x = LMDP (map_prod id (map_nebset (map_pmf (unfold_lmdp s))) (s x))"

primcorec unfold_gen :: "('a \<Rightarrow> (('b \<times> 'a) pmf) option) \<Rightarrow> 'a \<Rightarrow> 'b gen" where
  "unfold_gen s x = Gen (map_option (map_pmf (map_prod id (unfold_gen s))) (s x))"

primcorec unfold_str :: "('a \<Rightarrow> 'a pmf + ('b \<times> 'a) option) \<Rightarrow> 'a \<Rightarrow> 'b str" where
  "unfold_str s x = Str (map_sum (map_pmf (unfold_str s)) (map_option (map_prod id (unfold_str s))) (s x))"

primcorec unfold_alt :: "('a \<Rightarrow> 'a pmf + ('b \<times> 'a) set['k]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) alt" where
  "unfold_alt s x = Alt (map_sum (map_pmf (unfold_alt s)) (map_bset (map_prod id (unfold_alt s))) (s x))"

primcorec unfold_sseg :: "('a \<Rightarrow> ('b \<times> 'a pmf) set['k]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) sseg" where
  "unfold_sseg s x = SSeg (map_bset (map_prod id (map_pmf (unfold_sseg s))) (s x))"

primcorec unfold_seg :: "('a \<Rightarrow> (('b \<times> 'a) pmf) set['k]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) seg" where
  "unfold_seg s x = Seg (map_bset (map_pmf (map_prod id (unfold_seg s))) (s x))"

primcorec unfold_bun :: "('a \<Rightarrow> (('b \<times> 'a) set['k]) pmf) \<Rightarrow> 'a \<Rightarrow> ('b, 'k) bun" where
  "unfold_bun s x = Bun (map_pmf (map_bset (map_prod id (unfold_bun s))) (s x))"

primcorec unfold_pz :: "('a \<Rightarrow> (('b \<times> 'a) set['k1]) pmf set['k2]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k1, 'k2) pz" where
  "unfold_pz s x = PZ (map_bset (map_pmf (map_bset (map_prod id (unfold_pz s)))) (s x))"

primcorec unfold_mg :: "('a \<Rightarrow> (('b \<times> 'a + 'a) set['k1]) pmf set['k2]) \<Rightarrow> 'a \<Rightarrow> ('b, 'k1, 'k2) mg" where
  "unfold_mg s x = MG (map_bset (map_pmf (map_bset (map_sum (map_prod id (unfold_mg s)) (unfold_mg s)))) (s x))"


section \<open>Embeddings\<close>

abbreviation (input) "react_of_dlts_emb dlts \<equiv> map_option return_pmf o dlts"
abbreviation (input) "lts_of_dlts_emb \<equiv> bgraph"
abbreviation (input) "sseg_of_react_emb \<equiv> bgraph"
abbreviation (input) "gen_of_lmc_emb \<equiv> Some o case_prod (map_pmf o Pair)"
abbreviation (input) "lmdp_of_lmc_emb \<equiv> map_prod id nebsingleton"
abbreviation (input) "sseg_of_lmdp_emb \<equiv> (\<lambda>(a, X). map_bset (Pair a) (bset_of_nebset X))"
abbreviation (input) "sseg_of_lts_emb \<equiv> map_bset (map_prod id return_pmf)"
abbreviation (input) "ssegopt_of_alt_emb \<equiv> case_sum
   (map_bset (Pair None) o bsingleton)
   (map_bset (map_prod Some return_pmf))"
abbreviation (input) "bunopt_of_alt_emb \<equiv> case_sum
   (map_pmf (bsingleton o Pair None))
   (map_pmf (map_bset (map_prod Some id)) o return_pmf)"
abbreviation (input) "segopt_of_seg_emb \<equiv> map_bset (map_pmf (map_prod Some id))"
abbreviation (input) "ssegopt_of_sseg_emb \<equiv> map_bset (map_prod Some id)"
abbreviation (input) "bunopt_of_bun_emb \<equiv> map_pmf (map_bset (map_prod Some id))"
abbreviation (input) "pzopt_of_pz_emb \<equiv> map_bset (map_pmf (map_bset (map_prod Some id)))"
abbreviation (input) "seg_of_sseg_emb \<equiv> map_bset (case_prod (map_pmf o Pair))"
abbreviation (input) "pz_of_seg_emb \<equiv> map_bset (map_pmf bsingleton)"
abbreviation (input) "pz_of_bun_emb \<equiv> bsingleton"
abbreviation (input) "seg_of_gen_emb \<equiv>  bset_of_option"
abbreviation (input) "bun_of_lts_emb \<equiv> return_pmf"
abbreviation (input) "bun_of_gen_emb \<equiv> case_option (return_pmf bempty) (map_pmf bsingleton)"
abbreviation (input) "str_of_mc_emb \<equiv> Inl"
abbreviation (input) "alt_of_str_emb \<equiv> map_sum id bset_of_option"
abbreviation (input) "pzopt_of_mg_emb \<equiv> map_bset (map_pmf (map_bset (case_sum (map_prod Some id) (Pair None))))"
abbreviation (input) "mg_of_pzopt_emb \<equiv> map_bset (map_pmf (map_bset (\<lambda>(a, s). case_option (Inr s) (\<lambda>a. (Inl (a, s))) a)))"

text \<open>Obsolete edges (susumed by transitive ones)\<close>

abbreviation (input) "mg_of_pz_emb \<equiv> map_bset (map_pmf (map_bset Inl))"
abbreviation (input) "mg_of_alt1_emb \<equiv> case_sum
   (map_bset (map_pmf (map_bset Inr o bsingleton)) o bsingleton)
   (map_bset (map_pmf (map_bset Inl o bsingleton) o return_pmf))"
abbreviation (input) "mg_of_alt2_emb \<equiv> case_sum
   (map_bset (map_pmf (map_bset Inr o bsingleton)) o bsingleton)
   (map_bset (map_pmf (map_bset Inl) o return_pmf) o bsingleton)"
abbreviation (input) "pz_of_alt1_emb \<equiv> case_sum
   (map_bset (map_pmf (map_bset (Pair None) o bsingleton)) o bsingleton)
   (map_bset (map_pmf (map_bset (map_prod Some id) o bsingleton) o return_pmf))"
abbreviation (input) "pz_of_alt2_emb \<equiv> case_sum
   (map_bset (map_pmf (map_bset (Pair None) o bsingleton)) o bsingleton)
   (map_bset (map_pmf (map_bset (map_prod Some id)) o return_pmf) o bsingleton)"


definition react_of_dlts :: "'a dlts \<Rightarrow> 'a react" where
  [simp]: "react_of_dlts = unfold_react (react_of_dlts_emb o un_DLTS)"

definition lts_of_dlts :: "'a dlts \<Rightarrow> ('a, 'a set) lts" where
  [simp]: "lts_of_dlts = unfold_lts (lts_of_dlts_emb o un_DLTS)"

definition sseg_of_react :: "'a react \<Rightarrow> ('a, 'a set) sseg" where
  [simp]: "sseg_of_react = unfold_sseg (sseg_of_react_emb o un_React)"

definition lmdp_of_lmc :: "'a lmc \<Rightarrow> ('a, 'k) lmdp" where
  [simp]: "lmdp_of_lmc = unfold_lmdp (lmdp_of_lmc_emb o un_LMC)"

definition gen_of_lmc :: "'a lmc \<Rightarrow> 'a gen" where
  [simp]: "gen_of_lmc = unfold_gen (gen_of_lmc_emb o un_LMC)"

definition sseg_of_lmdp :: "('a, 'k) lmdp \<Rightarrow> ('a, 'k) sseg" where
  [simp]: "sseg_of_lmdp = unfold_sseg (sseg_of_lmdp_emb o un_LMDP)"

definition sseg_of_lts :: "('a, 'k) lts \<Rightarrow> ('a, 'k) sseg" where
  [simp]: "sseg_of_lts = unfold_sseg (sseg_of_lts_emb o un_LTS)"

definition ssegopt_of_alt :: "('a, 'k) alt \<Rightarrow> ('a option, 'k) sseg" where
  [simp]: "ssegopt_of_alt = unfold_sseg (ssegopt_of_alt_emb o un_Alt)"

definition bunopt_of_alt :: "('a, 'k) alt \<Rightarrow> ('a option, 'k) bun" where
  [simp]: "bunopt_of_alt = unfold_bun (bunopt_of_alt_emb o un_Alt)"

definition seg_of_sseg :: "('a, 'k) sseg \<Rightarrow> ('a, 'k) seg" where
  [simp]: "seg_of_sseg = unfold_seg (seg_of_sseg_emb o un_SSeg)"

definition seg_of_gen :: "'a gen \<Rightarrow> ('a, 'k) seg" where
  [simp]: "seg_of_gen = unfold_seg (seg_of_gen_emb o un_Gen)"

definition bun_of_lts :: "('a, 'k) lts \<Rightarrow> ('a, 'k) bun" where
  [simp]: "bun_of_lts = unfold_bun (bun_of_lts_emb o un_LTS)"

definition bun_of_gen :: "'a gen \<Rightarrow> ('a, 'k) bun" where
  [simp]: "bun_of_gen = unfold_bun (bun_of_gen_emb o un_Gen)"

definition pz_of_seg :: "('a, 'k) seg \<Rightarrow> ('a, 'k1, 'k) pz" where
  [simp]: "pz_of_seg = unfold_pz (pz_of_seg_emb o un_Seg)"

definition pz_of_bun :: "('a, 'k) bun \<Rightarrow> ('a, 'k, 'k1) pz" where
  [simp]: "pz_of_bun = unfold_pz (pz_of_bun_emb o un_Bun)"

definition mg_of_pz :: "('a, 'k1, 'k2) pz \<Rightarrow> ('a, 'k1, 'k2) mg" where
  [simp]: "mg_of_pz = unfold_mg (mg_of_pz_emb o un_PZ)"

definition str_of_mc :: "mc \<Rightarrow> 'a str" where
  [simp]: "str_of_mc = unfold_str (str_of_mc_emb o un_MC)"

definition alt_of_str :: "'a str \<Rightarrow> ('a, 'k) alt" where
  [simp]: "alt_of_str = unfold_alt (alt_of_str_emb o un_Str)"

definition ssegopt_of_sseg :: "('a, 'k) sseg \<Rightarrow> ('a option, 'k) sseg" where
  [simp]: "ssegopt_of_sseg = unfold_sseg (ssegopt_of_sseg_emb o un_SSeg)"

definition segopt_of_seg :: "('a, 'k) seg \<Rightarrow> ('a option, 'k) seg" where
  [simp]: "segopt_of_seg = unfold_seg (segopt_of_seg_emb o un_Seg)"

definition bunopt_of_bun :: "('a, 'k) bun \<Rightarrow> ('a option, 'k) bun" where
  [simp]: "bunopt_of_bun = unfold_bun (bunopt_of_bun_emb o un_Bun)"

definition pzopt_of_pz :: "('a, 'k1, 'k2) pz \<Rightarrow> ('a option, 'k1, 'k2) pz" where
  [simp]: "pzopt_of_pz = unfold_pz (pzopt_of_pz_emb o un_PZ)"

definition pzopt_of_mg :: "('a, 'k1, 'k2) mg \<Rightarrow> ('a option, 'k1, 'k2) pz" where
  [simp]: "pzopt_of_mg = unfold_pz (pzopt_of_mg_emb o un_MG)"

definition mg_of_pzopt :: "('a option, 'k1, 'k2) pz \<Rightarrow> ('a, 'k1, 'k2) mg" where
  [simp]: "mg_of_pzopt = unfold_mg (mg_of_pzopt_emb o un_PZ)"

definition mg_of_alt1 :: "('a, 'k) alt \<Rightarrow> ('a, 'k1, 'k) mg" where
  [simp]: "mg_of_alt1 = unfold_mg (mg_of_alt1_emb o un_Alt)"

definition mg_of_alt2 :: "('a, 'k) alt \<Rightarrow> ('a, 'k, 'k1) mg" where
  [simp]: "mg_of_alt2 = unfold_mg (mg_of_alt2_emb o un_Alt)"

definition pz_of_alt1 :: "('a, 'k) alt \<Rightarrow> ('a option, 'k1, 'k) pz" where
  [simp]: "pz_of_alt1 = unfold_pz (pz_of_alt1_emb o un_Alt)"

definition pz_of_alt2 :: "('a, 'k) alt \<Rightarrow> ('a option, 'k, 'k2) pz" where
  [simp]: "pz_of_alt2 = unfold_pz (pz_of_alt2_emb o un_Alt)"


section \<open>Automation Setup\<close>

lemma mc_rel_eq[unfolded vimage2p_def]:
  "BNF_Def.vimage2p un_MC un_MC (rel_pmf (=)) = (=)"
  by (auto simp add: vimage2p_def pmf.rel_eq option.rel_eq fun.rel_eq fun_eq_iff mc.expand)

lemma dlts_rel_eq[unfolded vimage2p_def]:
  "BNF_Def.vimage2p un_DLTS un_DLTS (rel_fun (=) (rel_option (=))) = (=)"
  by (auto simp add: vimage2p_def pmf.rel_eq option.rel_eq fun.rel_eq fun_eq_iff dlts.expand)

lemma react_rel_eq[unfolded vimage2p_def]:
  "BNF_Def.vimage2p un_React un_React (rel_fun (=) (rel_option (rel_pmf (=)))) = (=)"
  by (auto simp add: vimage2p_def pmf.rel_eq option.rel_eq fun.rel_eq fun_eq_iff react.expand)

lemma all_neq_Inl_ex_eq_Inr[dest]: "(\<forall>l. x \<noteq> Inl l) \<Longrightarrow> (\<exists>r. x = Inr r)" by (cases x) auto
lemma all_neq_Inr_ex_eq_Inl[dest]: "(\<forall>r. x \<noteq> Inr r) \<Longrightarrow> (\<exists>l. x = Inl l)"  by (cases x) auto
lemma all2_neq_Inl_ex_eq_Inr[dest]: "(\<forall>a b. x \<noteq> Inl (a, b)) \<Longrightarrow> (\<exists>r. x = Inr r)" by (cases x) auto
lemma all2_neq_Inr_ex_eq_Inl[dest]: "(\<forall>a b. x \<noteq> Inr (a, b)) \<Longrightarrow> (\<exists>l. x = Inl l)" by (cases x) auto

lemma rel_prod_simp_asym[simp]:
  "\<And>x y. rel_prod R S (x, y) = (\<lambda>z. case z of (x', y') \<Rightarrow> R x x' \<and> S y y')"
  "\<And>x y z. rel_prod R S x (y, z) = (case x of (y', z') \<Rightarrow> R y' y \<and> S z' z)"
  by auto

lemma map_prod_eq_Pair_iff[simp]:
  "map_prod f g x = (y, z) \<longleftrightarrow> (f (fst x) = y \<and> g (snd x) = z)"
  by (cases x) auto

lemmas [abs_def, simp] =
  sum.rel_map prod.rel_map option.rel_map pmf.rel_map bset.rel_map fun.rel_map nebset.rel_map

lemmas [simp] =
  lts.rel_eq lmc.rel_eq lmdp.rel_eq gen.rel_eq str.rel_eq alt.rel_eq sseg.rel_eq seg.rel_eq
  bun.rel_eq pz.rel_eq mg.rel_eq
  rel_pmf_return_pmf1 rel_pmf_return_pmf2 set_pmf_not_empty rel_pmf_rel_prod
  bset.set_map nebset.set_map

lemmas [simp del] =
  split_paired_Ex

lemma bisimilar_eqI:
  assumes "\<And>R. \<lbrakk>R x y; \<And>x y. R x y \<Longrightarrow> Q R (s1 x) (s2 y)\<rbrakk> \<Longrightarrow>  P x y"
  and "P x y \<Longrightarrow> \<forall>x y. P x y \<longrightarrow> Q P (s1 x) (s2 y)"
  shows "bisimilar Q s1 s2 x y = P x y"
  using assms unfolding bisimilar_def by auto

bundle probabilistic_hierarchy =
  rel_fun_def[simp]
  sum.splits[split]
  prod.splits[split]
  option.splits[split]

  predicate2_eqD[THEN iffD2, OF mc_rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF dlts_rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF lts.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF react_rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF lmc.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF lmdp.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF gen.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF str.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF alt.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF sseg.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF seg.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF bun.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF pz.rel_eq, dest]
  predicate2_eqD[THEN iffD2, OF mg.rel_eq, dest]

  iffD1[OF lts.rel_sel, dest!]
  iffD1[OF lmc.rel_sel, dest!]
  iffD1[OF lmdp.rel_sel, dest!]
  iffD1[OF gen.rel_sel, dest!]
  iffD1[OF str.rel_sel, dest!]
  iffD1[OF alt.rel_sel, dest!]
  iffD1[OF sseg.rel_sel, dest!]
  iffD1[OF seg.rel_sel, dest!]
  iffD1[OF bun.rel_sel, dest!]
  iffD1[OF pz.rel_sel, dest!]
  iffD1[OF mg.rel_sel, dest!]

  pmf.rel_refl[intro]
  bset.rel_refl[intro]
  nebset.rel_refl[intro]
  prod.rel_refl[intro]
  sum.rel_refl[intro]
  option.rel_refl[intro]

  pmf.rel_mono_strong[intro]
  bset.rel_mono_strong[intro]
  nebset.rel_mono_strong[intro]
  prod.rel_mono_strong[intro]
  sum.rel_mono_strong[intro]
  option.rel_mono_strong[intro]

section \<open>Proofs\<close>

context
includes probabilistic_hierarchy
begin

method bisimilar_alt =
  rule bisimilar_eqI,
  match conclusion in "u1 s1 x = u2 s2 y" for u1 u2 s1 s2 x y \<Rightarrow>
    \<open>coinduction arbitrary: x y, fastforce\<close>,
  fastforce

lemma bisimilar_alt:
  "\<And>s1 s2. bisimilar_mc s1 s2 x y = (unfold_mc s1 x = unfold_mc s2 y)"
  "\<And>s1 s2. bisimilar_dlts s1 s2 x y = (unfold_dlts s1 x = unfold_dlts s2 y)"
  "\<And>s1 s2. bisimilar_lts s1 s2 x y = (unfold_lts s1 x = unfold_lts s2 y)"
  "\<And>s1 s2. bisimilar_react s1 s2 x y = (unfold_react s1 x = unfold_react s2 y)"
  "\<And>s1 s2. bisimilar_lmc s1 s2 x y = (unfold_lmc s1 x = unfold_lmc s2 y)"
  "\<And>s1 s2. bisimilar_lmdp s1 s2 x y = (unfold_lmdp s1 x = unfold_lmdp s2 y)"
  "\<And>s1 s2. bisimilar_gen s1 s2 x y = (unfold_gen s1 x = unfold_gen s2 y)"
  "\<And>s1 s2. bisimilar_str s1 s2 x y = (unfold_str s1 x = unfold_str s2 y)"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y = (unfold_alt s1 x = unfold_alt s2 y)"
  "\<And>s1 s2. bisimilar_sseg s1 s2 x y = (unfold_sseg s1 x = unfold_sseg s2 y)"
  "\<And>s1 s2. bisimilar_seg s1 s2 x y = (unfold_seg s1 x = unfold_seg s2 y)"
  "\<And>s1 s2. bisimilar_bun s1 s2 x y = (unfold_bun s1 x = unfold_bun s2 y)"
  "\<And>s1 s2. bisimilar_pz s1 s2 x y = (unfold_pz s1 x = unfold_pz s2 y)"
  "\<And>s1 s2. bisimilar_mg s1 s2 x y = (unfold_mg s1 x = unfold_mg s2 y)"
  by bisimilar_alt+

method commute_prover =
  intro ext,
  match conclusion in "u1 s1 x = (emb o u2 s2) x" for emb u1 u2 s1 s2 x \<Rightarrow>
     \<open>coinduction arbitrary: x, fastforce\<close>

lemma emb_commute:
  "\<And>s. unfold_lts (lts_of_dlts_emb o s) = lts_of_dlts o unfold_dlts s"
  "\<And>s. unfold_gen (gen_of_lmc_emb o s) = gen_of_lmc o unfold_lmc s"
  "\<And>s. unfold_lmdp (lmdp_of_lmc_emb o s) = lmdp_of_lmc o unfold_lmc s"
  "\<And>s. unfold_react (react_of_dlts_emb o s) = react_of_dlts o unfold_dlts s"
  "\<And>s. unfold_sseg (sseg_of_lmdp_emb o s) = sseg_of_lmdp o unfold_lmdp s"
  "\<And>s. unfold_sseg (sseg_of_lts_emb o s) = sseg_of_lts o unfold_lts s"
  "\<And>s. unfold_sseg (ssegopt_of_alt_emb o s) = ssegopt_of_alt o unfold_alt s"
  "\<And>s. unfold_sseg (sseg_of_react_emb o s) = sseg_of_react o unfold_react s"
  "\<And>s. unfold_seg (seg_of_sseg_emb o s) = seg_of_sseg o unfold_sseg s"
  "\<And>s. unfold_seg (seg_of_gen_emb o s) = seg_of_gen o unfold_gen s"
  "\<And>s. unfold_bun (bun_of_lts_emb o s) = bun_of_lts o unfold_lts s"
  "\<And>s. unfold_bun (bunopt_of_alt_emb o s) = bunopt_of_alt o unfold_alt s"
  "\<And>s. unfold_bun (bun_of_gen_emb o s) = bun_of_gen o unfold_gen s"
  "\<And>s. unfold_pz (pz_of_seg_emb o s) = pz_of_seg o unfold_seg s"
  "\<And>s. unfold_pz (pz_of_bun_emb o s) = pz_of_bun o unfold_bun s"
  "\<And>s. unfold_str (str_of_mc_emb o s) = str_of_mc o unfold_mc s"
  "\<And>s. unfold_alt (alt_of_str_emb o s) = alt_of_str o unfold_str s"
  "\<And>s. unfold_sseg (ssegopt_of_sseg_emb o s) = ssegopt_of_sseg o unfold_sseg s"
  "\<And>s. unfold_seg (segopt_of_seg_emb o s) = segopt_of_seg o unfold_seg s"
  "\<And>s. unfold_bun (bunopt_of_bun_emb o s) = bunopt_of_bun o unfold_bun s"
  "\<And>s. unfold_pz (pzopt_of_pz_emb o s) = pzopt_of_pz o unfold_pz s"
  "\<And>s. unfold_pz (pzopt_of_mg_emb o s) = pzopt_of_mg o unfold_mg s"
  "\<And>s. unfold_mg (mg_of_pzopt_emb o s) = mg_of_pzopt o unfold_pz s"

  "\<And>s. unfold_mg (mg_of_pz_emb o s) = mg_of_pz o unfold_pz s"
  "\<And>s. unfold_mg (mg_of_alt1_emb o s) = mg_of_alt1 o unfold_alt s"
  "\<And>s. unfold_mg (mg_of_alt2_emb o s) = mg_of_alt2 o unfold_alt s"
  "\<And>s. unfold_pz (pz_of_alt1_emb o s) = pz_of_alt1 o unfold_alt s"
  "\<And>s. unfold_pz (pz_of_alt2_emb o s) = pz_of_alt2 o unfold_alt s"
  by commute_prover+

method inj_prover =
  intro injI,
  match conclusion in "x = y" for x y \<Rightarrow> \<open>coinduction arbitrary: x y, fastforce\<close>

lemma inj:
  "inj lts_of_dlts"
  "inj react_of_dlts"
  "inj gen_of_lmc"
  "inj lmdp_of_lmc"
  "inj sseg_of_lmdp"
  "inj sseg_of_react"
  "inj sseg_of_lts"
  "inj ssegopt_of_alt"
  "inj seg_of_gen"
  "inj seg_of_sseg"
  "inj bun_of_lts"
  "inj bunopt_of_alt"
  "inj bun_of_gen"
  "inj pz_of_seg"
  "inj pz_of_bun"
  "inj str_of_mc"
  "inj alt_of_str"
  "inj ssegopt_of_sseg"
  "inj segopt_of_seg"
  "inj bunopt_of_bun"
  "inj pzopt_of_pz"
  "inj pzopt_of_mg"
  "inj mg_of_pzopt"

  "inj mg_of_pz"
  "inj mg_of_alt1"
  "inj mg_of_alt2"
  "inj pz_of_alt1"
  "inj pz_of_alt2"
  by inj_prover+

end

lemma hierarchy:
  "\<And>s1 s2. bisimilar_dlts s1 s2 x y \<longleftrightarrow> bisimilar_lts (lts_of_dlts_emb o s1) (lts_of_dlts_emb o s2) x y"
  "\<And>s1 s2. bisimilar_lmc s1 s2 x y \<longleftrightarrow> bisimilar_gen (gen_of_lmc_emb o s1) (gen_of_lmc_emb o s2) x y"
  "\<And>s1 s2. bisimilar_lmc s1 s2 x y \<longleftrightarrow> bisimilar_lmdp (lmdp_of_lmc_emb o s1) (lmdp_of_lmc_emb o s2) x y"
  "\<And>s1 s2. bisimilar_dlts s1 s2 x y \<longleftrightarrow> bisimilar_react (react_of_dlts_emb o s1) (react_of_dlts_emb o s2) x y"
  "\<And>s1 s2. bisimilar_lmdp s1 s2 x y \<longleftrightarrow> bisimilar_sseg (sseg_of_lmdp_emb o s1) (sseg_of_lmdp_emb o s2) x y"
  "\<And>s1 s2. bisimilar_lts s1 s2 x y \<longleftrightarrow> bisimilar_sseg (sseg_of_lts_emb o s1) (sseg_of_lts_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_sseg (ssegopt_of_alt_emb o s1) (ssegopt_of_alt_emb o s2) x y"
  "\<And>s1 s2. bisimilar_react s1 s2 x y \<longleftrightarrow> bisimilar_sseg (sseg_of_react_emb o s1) (sseg_of_react_emb o s2) x y"
  "\<And>s1 s2. bisimilar_sseg s1 s2 x y \<longleftrightarrow> bisimilar_seg (seg_of_sseg_emb o s1) (seg_of_sseg_emb o s2) x y"
  "\<And>(s1 :: _ \<Rightarrow> ('a option \<times> _ pmf) set[_]) s2.
     bisimilar_sseg s1 s2 x y \<longleftrightarrow> bisimilar_seg (seg_of_sseg_emb o s1) (seg_of_sseg_emb o s2) x y"
  "\<And>s1 s2. bisimilar_gen s1 s2 x y \<longleftrightarrow> bisimilar_seg (seg_of_gen_emb o s1) (seg_of_gen_emb o s2) x y"
  "\<And>s1 s2. bisimilar_lts s1 s2 x y \<longleftrightarrow> bisimilar_bun (bun_of_lts_emb o s1) (bun_of_lts_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_bun (bunopt_of_alt_emb o s1) (bunopt_of_alt_emb o s2) x y"
  "\<And>s1 s2. bisimilar_gen s1 s2 x y \<longleftrightarrow> bisimilar_bun (bun_of_gen_emb o s1) (bun_of_gen_emb o s2) x y"
  "\<And>s1 s2. bisimilar_seg s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_seg_emb o s1) (pz_of_seg_emb o s2) x y"
  "\<And>s1 s2. bisimilar_bun s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_bun_emb o s1) (pz_of_bun_emb o s2) x y"
  "\<And>(s1 :: _ \<Rightarrow> ('a option \<times> _) pmf set[_]) s2.
     bisimilar_seg s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_seg_emb o s1) (pz_of_seg_emb o s2) x y"
  "\<And>(s1 :: _ \<Rightarrow> (('a option \<times> _) set[_]) pmf) s2.
     bisimilar_bun s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_bun_emb o s1) (pz_of_bun_emb o s2) x y"
  "\<And>s1 s2. bisimilar_mc s1 s2 x y \<longleftrightarrow> bisimilar_str (str_of_mc_emb o s1) (str_of_mc_emb o s2) x y"
  "\<And>s1 s2. bisimilar_sseg s1 s2 x y \<longleftrightarrow> bisimilar_sseg (ssegopt_of_sseg_emb o s1) (ssegopt_of_sseg_emb o s2) x y"
  "\<And>s1 s2. bisimilar_seg s1 s2 x y \<longleftrightarrow> bisimilar_seg (segopt_of_seg_emb o s1) (segopt_of_seg_emb o s2) x y"
  "\<And>s1 s2. bisimilar_bun s1 s2 x y \<longleftrightarrow> bisimilar_bun (bunopt_of_bun_emb o s1) (bunopt_of_bun_emb o s2) x y"
  "\<And>s1 s2. bisimilar_pz s1 s2 x y \<longleftrightarrow> bisimilar_pz (pzopt_of_pz_emb o s1) (pzopt_of_pz_emb o s2) x y"
  "\<And>s1 s2. bisimilar_str s1 s2 x y \<longleftrightarrow> bisimilar_alt (alt_of_str_emb o s1) (alt_of_str_emb o s2) x y"
  "\<And>s1 s2. bisimilar_mg s1 s2 x y \<longleftrightarrow> bisimilar_pz (pzopt_of_mg_emb o s1) (pzopt_of_mg_emb o s2) x y"
  unfolding inj[THEN inj_eq] bisimilar_alt emb_commute o_apply by (rule refl)+

text \<open>An edge that would make the graph cyclic\<close>

lemma
  "\<And>s1 s2. bisimilar_pz s1 s2 x y \<longleftrightarrow> bisimilar_mg (mg_of_pz_emb o s1) (mg_of_pz_emb o s2) x y"
  unfolding inj[THEN inj_eq] bisimilar_alt emb_commute o_apply by (rule refl)+

text \<open>Some redundant (historic) transitive edges\<close>

lemma
  "\<And>s1 s2. bisimilar_pz s1 s2 x y \<longleftrightarrow> bisimilar_mg (mg_of_pzopt_emb o s1) (mg_of_pzopt_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_mg (mg_of_alt1_emb o s1) (mg_of_alt1_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_mg (mg_of_alt2_emb o s1) (mg_of_alt2_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_alt1_emb o s1) (pz_of_alt1_emb o s2) x y"
  "\<And>s1 s2. bisimilar_alt s1 s2 x y \<longleftrightarrow> bisimilar_pz (pz_of_alt2_emb o s1) (pz_of_alt2_emb o s2) x y"
  unfolding inj[THEN inj_eq] bisimilar_alt emb_commute o_apply by (rule refl)+


section \<open>Some special proofs\<close>

text \<open>Two views on LTS\<close>

lemma "\<exists>f::(('a \<times> 's) set \<Rightarrow> 'a \<Rightarrow> 's set). bij f"
  by (fastforce simp: bij_def inj_on_def fun_eq_iff image_iff
    intro: exI[of _ "\<lambda>S a. {s. (a, s) \<in> S}"] exI[of _ "{(a, b). b \<in> f a}" for f])

lemma "\<exists>f::(('a \<times> 's) set[('a \<times> 's) set] \<Rightarrow> 'a \<Rightarrow> 's set['s set]). bij f"
  by (auto simp: bij_def inj_on_def fun_eq_iff image_iff bset_eq_iff
    intro!: exI[of _ "\<lambda>S a. bCollect (\<lambda>s. bmember (a, s) S)"]
            exI[of _ "bCollect (\<lambda>(a, b). bmember b (f a))" for f])

text \<open>mc is trivial\<close>

lemma mc_unit:
  fixes x y :: mc
  shows "x = y"
  by (coinduction arbitrary: x y)
    (auto simp: pmf.in_rel map_fst_pair_pmf map_snd_pair_pmf intro: exI[of _ "pair_pmf x y" for x y])

lemma "bisimilar_mc s1 s2 x y"
  unfolding bisimilar_alt by (rule mc_unit)


section \<open>Printing the Hierarchy Graph\<close>

ML \<open>
local

val trim = filter (fn s => s <> "" andalso s <> "set");

fun str_of_T (Type (c, Ts)) =
    space_implode " " (trim [commas (trim (map str_of_T Ts)), Long_Name.base_name c])
  | str_of_T _ = "";

fun get_edge thm = thm
  |> Thm.concl_of
  |> HOLogic.dest_Trueprop
  |> HOLogic.dest_eq |> fst
  |> dest_comb |> fst
  |> fastype_of
  |> dest_funT
  |> apply2 str_of_T;

val edges = map get_edge @{thms hierarchy[unfolded bisimilar_alt emb_commute o_apply, THEN iffD1]};

val nodes = distinct (op =) (maps (fn (x, y) => [x, y]) edges);

val node_graph = map (fn s => ((s, Graph_Display.content_node s []), [] : string list)) nodes;

val graph = fold (fn (x, y) => fn g =>
  AList.map_entry (fn (x, (y, _)) => x = y) x (cons y) g) edges node_graph

in

val _ = Graph_Display.display_graph graph

end
\<close>
(*<*)
end
(*>*)
