theory Converter imports
  Resource
begin

section \<open>Converters\<close>

subsection \<open>Type definition\<close>

codatatype ('a, results'_converter: 'b, outs'_converter: 'out, 'in) converter
  = Converter (run_converter: "'a \<Rightarrow> ('b \<times> ('a, 'b, 'out, 'in) converter, 'out, 'in) gpv")
  for map: map_converter'
    rel: rel_converter'
    pred: pred_converter'

lemma case_converter_conv_run_converter: "case_converter f conv = f (run_converter conv)"
  by(fact converter.case_eq_if)

subsection \<open>Functor\<close>

context 
  fixes a :: "'a \<Rightarrow> 'a'"
    and b :: "'b \<Rightarrow> 'b'"
    and out :: "'out \<Rightarrow> 'out'"
    and "inn" :: "'in \<Rightarrow> 'in'"
begin

primcorec map_converter :: "('a', 'b, 'out, 'in') converter \<Rightarrow> ('a, 'b', 'out', 'in) converter" where
  "run_converter (map_converter conv) = 
   map_gpv (map_prod b map_converter) out \<circ> map_gpv' id id inn \<circ> run_converter conv \<circ> a"

lemma map_converter_sel [simp]:
  "run_converter (map_converter conv) a' = map_gpv' (map_prod b map_converter) out inn (run_converter conv (a a'))"
  by(simp add: map_gpv_conv_map_gpv' map_gpv'_comp)

declare map_converter.sel [simp del]

lemma map_converter_ctr [simp, code]:
  "map_converter (Converter f) = Converter (map_fun a (map_gpv' (map_prod b map_converter) out inn) f)"
  by(rule converter.expand; simp add: fun_eq_iff)

end

lemma map_converter_id14: "map_converter id b out id res = map_converter' b out res"
  by(coinduction arbitrary: res)
    (auto 4 3 intro!: rel_funI simp add: converter.map_sel gpv.rel_map map_gpv_conv_map_gpv'[symmetric] intro!: gpv.rel_refl_strong)

lemma map_converter_id [simp]: "map_converter id id id id conv = conv"
  by(simp add: map_converter_id14 converter.map_id)

lemma map_converter_compose [simp]:
  "map_converter a b f g (map_converter a' b' f' g' conv) = map_converter (a' \<circ> a) (b \<circ> b') (f \<circ> f') (g' \<circ> g) conv"
  by(coinduction arbitrary: conv)
    (auto 4 3 intro!: rel_funI gpv.rel_refl_strong simp add: rel_gpv_map_gpv' map_gpv'_comp o_def prod.map_comp)

functor converter: map_converter by(simp_all add: o_def fun_eq_iff)

subsection \<open>Set functions with interfaces\<close>

context fixes \<I> :: "('a, 'b) \<I>" and \<I>' :: "('out, 'in) \<I>" begin

qualified inductive outsp_converter :: "'out \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool" for out where
  Out: "outsp_converter out conv" if "out \<in> outs_gpv \<I>' (run_converter conv a)" "a \<in> outs_\<I> \<I>"
| Cont: "outsp_converter out conv" 
if "(b, conv') \<in> results_gpv \<I>' (run_converter conv a)" "outsp_converter out conv'" "a \<in> outs_\<I> \<I>"

definition outs_converter :: "('a, 'b, 'out, 'in) converter \<Rightarrow> 'out set"
  where "outs_converter conv \<equiv> {x. outsp_converter x conv}"

qualified inductive resultsp_converter :: "'b \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool" for b where
  Result: "resultsp_converter b conv"
if "(b, conv') \<in> results_gpv \<I>' (run_converter conv a)" "a \<in> outs_\<I> \<I>"
| Cont: "resultsp_converter b conv"
if "(b', conv') \<in> results_gpv \<I>' (run_converter conv a)" "resultsp_converter b conv'" "a \<in> outs_\<I> \<I>"

definition results_converter :: "('a, 'b, 'out, 'in) converter \<Rightarrow> 'b set"
  where "results_converter conv = {b. resultsp_converter b conv}"

end

lemma outsp_converter_outs_converter_eq [pred_set_conv]: "Converter.outsp_converter \<I> \<I>' x = (\<lambda>conv. x \<in> outs_converter \<I> \<I>' conv)"
  by(simp add: outs_converter_def)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "outs_converter")\<close>

lemmas intros [intro?] = outsp_converter.intros[to_set]
  and Out = outsp_converter.Out[to_set]
  and Cont = outsp_converter.Cont[to_set]
  and induct [consumes 1, case_names Out Cont, induct set: outs_converter] = outsp_converter.induct[to_set]
  and cases [consumes 1, case_names Out Cont, cases set: outs_converter] = outsp_converter.cases[to_set]
  and simps = outsp_converter.simps[to_set]
end

inductive_simps outs_converter_Converter [to_set, simp]: "Converter.outsp_converter \<I> \<I>' x (Converter conv)"

lemma resultsp_converter_results_converter_eq [pred_set_conv]:
  "Converter.resultsp_converter \<I> \<I>' x = (\<lambda>conv. x \<in> results_converter \<I> \<I>' conv)"
  by(simp add: results_converter_def)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "results_converter")\<close>

lemmas intros [intro?] = resultsp_converter.intros[to_set]
  and Result = resultsp_converter.Result[to_set]
  and Cont = resultsp_converter.Cont[to_set]
  and induct [consumes 1, case_names Result Cont, induct set: results_converter] = resultsp_converter.induct[to_set]
  and cases [consumes 1, case_names Result Cont, cases set: results_converter] = resultsp_converter.cases[to_set]
  and simps = resultsp_converter.simps[to_set]
end

inductive_simps results_converter_Converter [to_set, simp]: "Converter.resultsp_converter \<I> \<I>' x (Converter conv)"

subsection \<open>Relator\<close>

coinductive rel_converter 
  :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> 'out' \<Rightarrow> bool) \<Rightarrow> ('in \<Rightarrow> 'in' \<Rightarrow> bool) 
  \<Rightarrow> ('a, 'c, 'out, 'in) converter \<Rightarrow> ('b, 'd, 'out', 'in') converter \<Rightarrow> bool"
  for A B C R where
    rel_converterI:
    "rel_fun A (rel_gpv'' (rel_prod B (rel_converter A B C R)) C R) (run_converter conv1) (run_converter conv2) 
  \<Longrightarrow> rel_converter A B C R conv1 conv2"

lemma rel_converter_coinduct [consumes 1, case_names rel_converter, coinduct pred: rel_converter]:
  assumes "X conv1 conv2"
    and "\<And>conv1 conv2. X conv1 conv2 \<Longrightarrow>
         rel_fun A (rel_gpv'' (rel_prod B (\<lambda>conv1 conv2. X conv1 conv2 \<or> rel_converter A B C R conv1 conv2)) C R)
            (run_converter conv1) (run_converter conv2)"
  shows "rel_converter A B C R conv1 conv2"
  using assms(1) by(rule rel_converter.coinduct)(simp add: assms(2))

lemma rel_converter_simps [simp, code]:
  "rel_converter A B C R (Converter f) (Converter g) \<longleftrightarrow> 
  rel_fun A (rel_gpv'' (rel_prod B (rel_converter A B C R)) C R) f g" 
  by(subst rel_converter.simps) simp

lemma rel_converterD:
  "rel_converter A B C R conv1 conv2 
  \<Longrightarrow> rel_fun A (rel_gpv'' (rel_prod B (rel_converter A B C R)) C R) (run_converter conv1) (run_converter conv2)"
  by(blast elim: rel_converter.cases)

lemma rel_converter_eq14: "rel_converter (=) B C (=) = rel_converter' B C" (is "?lhs = ?rhs")
proof(intro ext iffI)
  show "?rhs conv1 conv2" if "?lhs conv1 conv2" for conv1 conv2 using that
    by(coinduction arbitrary: conv1 conv2)(auto elim: rel_converter.cases simp add: rel_gpv_conv_rel_gpv'')
  show "?lhs conv1 conv2" if "?rhs conv1 conv2" for conv1 conv2 using that
    by(coinduction arbitrary: conv1 conv2)
      (auto 4 4 elim: converter.rel_cases intro: gpv.rel_mono_strong simp add: rel_fun_def rel_gpv_conv_rel_gpv''[symmetric])
qed

lemma rel_converter_eq [relator_eq]: "rel_converter (=) (=) (=) (=) = (=)"
  by(simp add: rel_converter_eq14 converter.rel_eq)

lemma rel_converter_mono [relator_mono]:
  assumes "A' \<le> A" "B \<le> B'" "C \<le> C'" "R' \<le> R"
  shows "rel_converter A B C R \<le> rel_converter A' B' C' R'"
proof
  show "rel_converter A' B' C' R' conv1 conv2" if "rel_converter A B C R conv1 conv2" for conv1 conv2 using that
    by(coinduct)(auto dest: rel_converterD elim!: rel_gpv''_mono[THEN predicate2D, rotated -1] prod.rel_mono_strong rel_fun_mono intro: assms[THEN predicate2D])
qed

lemma rel_converter_conversep: "rel_converter A\<inverse>\<inverse> B\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> = (rel_converter A B C R)\<inverse>\<inverse>"
proof(intro ext iffI; simp)
  show "rel_converter A B C R conv1 conv2" if "rel_converter A\<inverse>\<inverse> B\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> conv2 conv1"
    for A :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool" and B :: "'b1 \<Rightarrow> 'b2 \<Rightarrow> bool" and C :: "'c1 \<Rightarrow> 'c2 \<Rightarrow> bool" and R :: "'r1 \<Rightarrow> 'r2 \<Rightarrow> bool"
      and conv2 conv1
    using that apply(coinduct)
    apply(drule rel_converterD)
    apply(rewrite in \<hole> conversep_iff[symmetric])
    apply(subst rel_fun_conversep[symmetric])
    apply(subst rel_gpv''_conversep[symmetric])
    apply(erule rel_fun_mono, blast)
    by(auto simp add: prod.rel_conversep[symmetric] rel_fun_def conversep_iff[abs_def]
        elim: prod.rel_mono_strong rel_gpv''_mono[THEN predicate2D, rotated -1])

  from this[of "A\<inverse>\<inverse>" "B\<inverse>\<inverse>" "C\<inverse>\<inverse>" "R\<inverse>\<inverse>"]
  show "rel_converter A\<inverse>\<inverse> B\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> conv2 conv1" if "rel_converter A B C R conv1 conv2" for conv1 conv2
    using that by simp
qed

lemma rel_converter_map_converter'1:
  "rel_converter A B C R (map_converter' f g conv1) conv2 = rel_converter A (\<lambda>x. B (f x)) (\<lambda>x. C (g x)) R conv1 conv2"
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs using that
    by(coinduction arbitrary: conv1 conv2)
      (drule rel_converterD, auto intro: prod.rel_mono elim!: rel_fun_mono rel_gpv''_mono[THEN predicate2D, rotated -1]
        simp add: map_gpv'_id rel_gpv''_map_gpv map_converter.sel map_converter_id14[symmetric] rel_fun_comp spmf_rel_map prod.rel_map[abs_def])
  show ?lhs if ?rhs using that
    by(coinduction arbitrary: conv1 conv2)
      (drule rel_converterD, auto intro: prod.rel_mono elim!: rel_fun_mono rel_gpv''_mono[THEN predicate2D, rotated -1]
        simp add: map_gpv'_id rel_gpv''_map_gpv map_converter.sel map_converter_id14[symmetric] rel_fun_comp spmf_rel_map prod.rel_map[abs_def])
qed

lemma rel_converter_map_converter'2:
  "rel_converter A B C R conv1 (map_converter' f g conv2) = rel_converter A (\<lambda>x y. B x (f y)) (\<lambda>x y. C x (g y)) R conv1 conv2"
  using rel_converter_map_converter'1[of "conversep A" "conversep B" "conversep C" "conversep R" f g conv2 conv1]
  apply(rewrite in "\<hole> = _" conversep_iff[symmetric])
  apply(rewrite in "_ = \<hole>" conversep_iff[symmetric])
  apply(simp only: rel_converter_conversep[symmetric])
  apply(simp only: conversep_iff[abs_def])
  done

lemmas converter_rel_map' = rel_converter_map_converter'1[abs_def] rel_converter_map_converter'2

lemma rel_converter_pos_distr [relator_distr]:
  "rel_converter A B C R OO rel_converter A' B' C' R' \<le> rel_converter (A OO A') (B OO B') (C OO C') (R OO R')"
proof(rule predicate2I)
  show "rel_converter (A OO A') (B OO B') (C OO C') (R OO R') conv1 conv3"
    if "(rel_converter A B C R OO rel_converter A' B' C' R') conv1 conv3"
    for conv1 conv3 using that
    apply(coinduction arbitrary: conv1 conv3)
    apply(erule relcomppE)
    apply(drule rel_converterD)+
    apply(rule rel_fun_mono)
      apply(rule pos_fun_distr[THEN predicate2D])
      apply(erule (1) relcomppI)
     apply simp
    apply(rule rel_gpv''_mono[THEN predicate2D, rotated -1])
       apply(erule rel_gpv''_pos_distr[THEN predicate2D])
    by(auto simp add:  prod.rel_compp[symmetric] intro: prod.rel_mono)
qed

lemma left_unique_rel_converter:
  "\<lbrakk> left_total A; left_unique B; left_unique C; left_total R \<rbrakk> \<Longrightarrow> left_unique (rel_converter A B C R)"
  unfolding left_unique_alt_def left_total_alt_def rel_converter_conversep[symmetric]
  by(subst rel_converter_eq[symmetric], rule order_trans[OF rel_converter_pos_distr], erule (3) rel_converter_mono)

lemma right_unique_rel_converter:
  "\<lbrakk> right_total A; right_unique B; right_unique C; right_total R \<rbrakk> \<Longrightarrow> right_unique (rel_converter A B C R)"
  unfolding right_unique_alt_def right_total_alt_def rel_converter_conversep[symmetric]
  by(subst rel_converter_eq[symmetric], rule order_trans[OF rel_converter_pos_distr], erule (3) rel_converter_mono)

lemma bi_unique_rel_converter [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique B; bi_unique C; bi_total R \<rbrakk> \<Longrightarrow> bi_unique (rel_converter A B C R)"
  unfolding bi_unique_alt_def bi_total_alt_def by(blast intro: left_unique_rel_converter right_unique_rel_converter)


definition rel_witness_converter :: "('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> 'out' \<Rightarrow> bool) \<Rightarrow> ('in \<Rightarrow> 'in'' \<Rightarrow> bool) \<Rightarrow> ('in'' \<Rightarrow> 'in' \<Rightarrow> bool)
  \<Rightarrow> ('a, 'b, 'out, 'in) converter \<times> ('c, 'd, 'out', 'in') converter \<Rightarrow> ('e, 'b \<times> 'd, 'out \<times> 'out', 'in'') converter" where
  "rel_witness_converter A A' B C R R' = corec_converter (\<lambda>(conv1, conv2).
   map_gpv (map_prod id Inr \<circ> rel_witness_prod) id \<circ> 
   rel_witness_gpv (rel_prod B (rel_converter (A OO A') B C (R OO R'))) C R R' \<circ> 
   rel_witness_fun A A' (run_converter conv1, run_converter conv2))"

lemma rel_witness_converter_sel [simp]:
  "run_converter (rel_witness_converter A A' B C R R' (conv1, conv2)) =
   map_gpv (map_prod id (rel_witness_converter A A' B C R R') \<circ> rel_witness_prod) id \<circ> 
   rel_witness_gpv (rel_prod B (rel_converter (A OO A') B C (R OO R'))) C R R' \<circ> 
   rel_witness_fun A A' (run_converter conv1, run_converter conv2)"
  by(auto simp add: rel_witness_converter_def o_def fun_eq_iff gpv.map_comp intro!: gpv.map_cong)

lemma assumes "rel_converter (A OO A') B C (R OO R') conv conv'"
  and A: "left_unique A" "right_total A"
  and A': "right_unique A'" "left_total A'"
  and R: "left_unique R" "right_total R"
  and R': "right_unique R'" "left_total R'"
shows rel_witness_converter1: "rel_converter A (\<lambda>b (b', c). b = b' \<and> B b' c) (\<lambda>c (c', d). c = c' \<and> C c' d) R conv (rel_witness_converter A A' B C R R' (conv, conv'))" (is "?thesis1")
  and rel_witness_converter2: "rel_converter A' (\<lambda>(b, c') c. c = c' \<and> B b c') (\<lambda>(c, d') d. d = d' \<and> C c d') R' (rel_witness_converter A A' B C R R' (conv, conv')) conv'" (is "?thesis2")
proof -
  show ?thesis1 using assms(1)
  proof(coinduction arbitrary: conv conv')
    case rel_converter
    from this[THEN rel_converterD] show ?case
      apply(simp add: rel_fun_comp)
      apply(erule rel_fun_mono[OF rel_witness_fun1[OF _ A A']]; clarsimp simp add: rel_gpv''_map_gpv)
      apply(erule rel_gpv''_mono[THEN predicate2D, rotated -1, OF rel_witness_gpv1[OF _ R R']]; auto)
      done
  qed
  show ?thesis2 using assms(1)
  proof(coinduction arbitrary: conv conv')
    case rel_converter
    from this[THEN rel_converterD] show ?case
      apply(simp add: rel_fun_comp)
      apply(erule rel_fun_mono[OF rel_witness_fun2[OF _ A A']]; clarsimp simp add: rel_gpv''_map_gpv)
      apply(erule rel_gpv''_mono[THEN predicate2D, rotated -1, OF rel_witness_gpv2[OF _ R R']]; auto)
      done
  qed
qed

lemma rel_converter_neg_distr [relator_distr]:
  assumes A: "left_unique A" "right_total A"
    and A': "right_unique A'" "left_total A'"
    and R: "left_unique R" "right_total R"
    and R': "right_unique R'" "left_total R'"
  shows "rel_converter (A OO A') (B OO B') (C OO C') (R OO R') \<le> rel_converter A B C R OO rel_converter A' B' C' R'"
proof(rule predicate2I relcomppI)+
  fix conv conv''
  assume *: "rel_converter (A OO A') (B OO B') (C OO C') (R OO R') conv conv''"
  let ?conv' = "map_converter' (relcompp_witness B B') (relcompp_witness C C') (rel_witness_converter A A' (B OO B') (C OO C') R R' (conv, conv''))"
  show "rel_converter A B C R conv ?conv'" using rel_witness_converter1[OF * A A' R R'] unfolding converter_rel_map'
    by(rule rel_converter_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
  show "rel_converter A' B' C' R' ?conv' conv''" using rel_witness_converter2[OF * A A' R R'] unfolding converter_rel_map'
    by(rule rel_converter_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
qed

lemma left_total_rel_converter:
  "\<lbrakk> left_unique A; right_total A; left_total B; left_total C; left_unique R; right_total R \<rbrakk>
  \<Longrightarrow> left_total (rel_converter A B C R)"
  unfolding left_unique_alt_def left_total_alt_def rel_converter_conversep[symmetric]
  apply(subst rel_converter_eq[symmetric])
  apply(rule order_trans[rotated])
   apply(rule rel_converter_neg_distr; simp add: left_unique_alt_def)
  apply(rule rel_converter_mono; assumption)
  done

lemma right_total_rel_converter:
  "\<lbrakk> right_unique A; left_total A; right_total B; right_total C; right_unique R; left_total R \<rbrakk>
   \<Longrightarrow> right_total (rel_converter A B C R)"
  unfolding right_unique_alt_def right_total_alt_def rel_converter_conversep[symmetric]
  apply(subst rel_converter_eq[symmetric])
  apply(rule order_trans[rotated])
   apply(rule rel_converter_neg_distr; simp add: right_unique_alt_def)
  apply(rule rel_converter_mono; assumption)
  done

lemma bi_total_rel_converter [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique A; bi_total B; bi_total C; bi_total R; bi_unique R \<rbrakk> 
  \<Longrightarrow> bi_total (rel_converter A B C R)"
  unfolding bi_total_alt_def bi_unique_alt_def
  by(blast intro: left_total_rel_converter right_total_rel_converter)

inductive pred_converter :: "'a set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> bool) \<Rightarrow> 'in set \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool"
  for A B C R conv where
    "pred_converter A B C R conv" if
    "\<forall>x\<in>results_converter (\<I>_uniform A UNIV) (\<I>_uniform UNIV R) conv. B x" 
    "\<forall>out\<in>outs_converter (\<I>_uniform A UNIV) (\<I>_uniform UNIV R) conv. C out"

lemma pred_gpv'_mono_weak: (* TODO: Generalize to R' \<subseteq> R *)
  "pred_gpv' A C R \<le> pred_gpv' A' C' R" if "A \<le> A'" "C \<le> C'"
  using that by(auto 4 3 simp add: pred_gpv'.simps)

lemma Domainp_rel_converter_le:
  "Domainp (rel_converter A B C R) \<le> pred_converter (Collect (Domainp A)) (Domainp B) (Domainp C) (Collect (Domainp R))"
  (is "?lhs \<le> ?rhs")
proof(intro predicate1I pred_converter.intros strip)
  fix conv
  assume *: "?lhs conv"  
  let ?\<I> = "\<I>_uniform (Collect (Domainp A)) UNIV" and ?\<I>' = "\<I>_uniform UNIV (Collect (Domainp R))"
  show "Domainp B x" if "x \<in> results_converter ?\<I> ?\<I>' conv" for x using that *
    apply(induction)
     apply clarsimp
     apply(erule rel_converter.cases; clarsimp)
     apply(drule (1) rel_funD)
     apply(drule Domainp_rel_gpv''_le[THEN predicate1D, OF DomainPI])
     apply(erule pred_gpv'.cases)
     apply fastforce
    apply clarsimp
    apply(erule rel_converter.cases; clarsimp)
    apply(drule (1) rel_funD)
    apply(drule Domainp_rel_gpv''_le[THEN predicate1D, OF DomainPI])
    apply(erule pred_gpv'.cases)
    apply fastforce
    done
  show "Domainp C x" if "x \<in> outs_converter ?\<I> ?\<I>' conv" for x using that *
    apply induction
     apply clarsimp
     apply(erule rel_converter.cases; clarsimp)
     apply(drule (1) rel_funD)
     apply(drule Domainp_rel_gpv''_le[THEN predicate1D, OF DomainPI])
     apply(erule pred_gpv'.cases)
     apply fastforce
    apply clarsimp
    apply(erule rel_converter.cases; clarsimp)
    apply(drule (1) rel_funD)
    apply(drule Domainp_rel_gpv''_le[THEN predicate1D, OF DomainPI])
    apply(erule pred_gpv'.cases)
    apply fastforce
    done
qed

lemma rel_converter_Grp:
  "rel_converter (BNF_Def.Grp UNIV f)\<inverse>\<inverse> (BNF_Def.Grp B g) (BNF_Def.Grp C h) (BNF_Def.Grp UNIV k)\<inverse>\<inverse> =
   BNF_Def.Grp {conv. results_converter (\<I>_uniform (range f) UNIV) (\<I>_uniform UNIV (range k)) conv \<subseteq> B \<and> 
    outs_converter (\<I>_uniform (range f) UNIV) (\<I>_uniform UNIV (range k)) conv \<subseteq> C}
    (map_converter f g h k)"
  (is "?lhs = ?rhs")
  including lifting_syntax
proof(intro ext GrpI iffI CollectI conjI subsetI)
  let ?\<I> = "\<I>_uniform (range f) UNIV" and ?\<I>' = "\<I>_uniform UNIV (range k)"
  fix conv conv'
  assume *: "?lhs conv conv'"
  then show "map_converter f g h k conv = conv'"
    apply(coinduction arbitrary: conv conv')
    apply(drule rel_converterD)
    apply(unfold map_converter.sel)
    apply(subst (2) map_fun_def[symmetric])
    apply(subst map_fun2_id)
    apply(subst rel_fun_comp)
    apply(rule rel_fun_map_fun1)
    apply(erule rel_fun_mono, simp)
    apply(simp add: gpv.rel_map)
    by (auto simp add: rel_gpv_conv_rel_gpv'' prod.rel_map intro!: predicate2I rel_gpv''_map_gpv'1
        elim!: rel_gpv''_mono[THEN predicate2D, rotated -1] prod.rel_mono_strong GrpE)
  show "b \<in> B" if "b \<in> results_converter ?\<I> ?\<I>' conv" for b using * that
    by - (drule Domainp_rel_converter_le[THEN predicate1D, OF DomainPI]
        , auto simp add: Domainp_conversep Rangep_Grp iff: Grp_iff elim: pred_converter.cases)
  show "out \<in> C" if "out \<in> outs_converter ?\<I> ?\<I>' conv" for out using * that
    by - (drule Domainp_rel_converter_le[THEN predicate1D, OF DomainPI]
        , auto simp add: Domainp_conversep Rangep_Grp iff: Grp_iff elim: pred_converter.cases)
next
  let ?abr1="\<lambda>conv. results_converter (\<I>_uniform (range f) UNIV) (\<I>_uniform UNIV (range k)) conv \<subseteq> B"
  let ?abr2="\<lambda>conv. outs_converter (\<I>_uniform (range f) UNIV) (\<I>_uniform UNIV (range k)) conv \<subseteq> C"

  fix conv conv'
  assume "?rhs conv conv'"
  hence  *: "conv' = map_converter f g h k conv" and f1: "?abr1 conv" and f2: "?abr2 conv" by(auto simp add: Grp_iff)

  have[intro]: "?abr1 conv \<Longrightarrow> ?abr2 conv \<Longrightarrow> z \<in> run_converter conv ` range f \<Longrightarrow>
       out \<in> outs_gpv (\<I>_uniform UNIV (range k)) z \<Longrightarrow> BNF_Def.Grp C h out (h out)" for conv z out
    by(auto simp add: Grp_iff elim:  outs_converter.Out elim!: subsetD)

  from f1 f2 show "?lhs conv conv'" unfolding *
    apply(coinduction arbitrary: conv)
    apply(unfold map_converter.sel)
    apply(subst (2) map_fun_def[symmetric])
    apply(subst map_fun2_id)
    apply(subst rel_fun_comp)
    apply(rule rel_fun_map_fun2)
    apply(rule rel_fun_refl_eq_onp)
    apply(unfold map_gpv_conv_map_gpv' gpv.comp comp_id)
    apply(subst map_gpv'_id12)
    apply(rule rel_gpv''_map_gpv'2)
    apply(unfold rel_gpv''_map_gpv)
    apply(rule rel_gpv''_refl_eq_on)
     apply(simp add: prod.rel_map)
     apply(rule prod.rel_refl_strong)
      apply(clarsimp simp add: Grp_iff)
    by (auto intro: results_converter.Result results_converter.Cont outs_converter.Cont elim!: subsetD)
qed

context 
  includes lifting_syntax 
  notes [transfer_rule] = map_gpv_parametric'
begin

lemma Converter_parametric [transfer_rule]:
  "((A ===> rel_gpv'' (rel_prod B (rel_converter A B C R)) C R) ===> rel_converter A B C R) Converter Converter"
  by(rule rel_funI)(simp)

lemma run_converter_parametric [transfer_rule]:
  "(rel_converter A B C R ===> A ===> rel_gpv'' (rel_prod B (rel_converter A B C R)) C R)
  run_converter run_converter"
  by(rule rel_funI)(auto dest: rel_converterD)

lemma corec_converter_parametric [transfer_rule]:
  "((S ===> A ===> rel_gpv'' (rel_prod B (rel_sum (rel_converter A B C R) S)) C R) ===> S ===> rel_converter A B C R)
   corec_converter corec_converter"
proof((rule rel_funI)+, goal_cases)
  case (1 f g s1 s2)
  then show ?case 
    by(coinduction arbitrary: s1 s2)
      (drule 1(1)[THEN rel_funD]
        , auto 4 4 simp add: rel_fun_comp prod.rel_map[abs_def] rel_gpv''_map_gpv prod.rel_map split: sum.split 
        intro: prod.rel_mono elim!: rel_fun_mono rel_gpv''_mono[THEN predicate2D, rotated -1])
qed

lemma map_converter_parametric [transfer_rule]:
  "((A' ===> A) ===> (B ===> B') ===> (C ===> C') ===> (R' ===> R) ===> rel_converter A B C R ===> rel_converter A' B' C' R')
  map_converter map_converter"
  unfolding map_converter_def by(transfer_prover)

lemma map_converter'_parametric [transfer_rule]:
  "((B ===> B') ===> (C ===> C') ===> rel_converter (=) B C (=) ===> rel_converter (=) B' C' (=))
  map_converter' map_converter'"
  unfolding map_converter_id14[symmetric] by transfer_prover

lemma case_converter_parametric [transfer_rule]:
  "(((A ===> rel_gpv'' (rel_prod B (rel_converter A B C R)) C R) ===> X) ===> rel_converter A B C R ===> X)
  case_converter case_converter"
  unfolding case_converter_conv_run_converter by transfer_prover

end

subsection \<open>Well-typing\<close>

coinductive WT_converter :: "('a, 'b) \<I> \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool"
  ("_,/ _ \<turnstile>\<^sub>C/ _ \<surd>" [100, 0, 0] 99)
  for \<I> \<I>' where
    WT_converterI: "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>" if
    "\<And>q. q \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g run_converter conv q \<surd>"
    "\<And>q r conv'. \<lbrakk> q \<in> outs_\<I> \<I>; (r, conv') \<in> results_gpv \<I>' (run_converter conv q) \<rbrakk> \<Longrightarrow> r \<in> responses_\<I> \<I> q \<and> \<I>, \<I>' \<turnstile>\<^sub>C conv' \<surd>"

lemma WT_converter_coinduct[consumes 1, case_names WT_converter, case_conclusion WT_converter WT_gpv results_gpv, coinduct pred: WT_converter]:
  assumes "X conv"
    and "\<And>conv q r conv'. \<lbrakk> X conv; q \<in> outs_\<I> \<I> \<rbrakk>
  \<Longrightarrow> \<I>' \<turnstile>g run_converter conv q \<surd> \<and>
      ((r, conv') \<in> results_gpv \<I>' (run_converter conv q) \<longrightarrow> r \<in> responses_\<I> \<I> q \<and> (X conv' \<or> \<I>, \<I>' \<turnstile>\<^sub>C conv' \<surd>))"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>"
  using assms(1) by(rule WT_converter.coinduct)(blast dest: assms(2))

lemma WT_converterD:
  assumes "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>" "q \<in> outs_\<I> \<I>"
  shows WT_converterD_WT: "\<I>' \<turnstile>g run_converter conv q \<surd>"
    and WT_converterD_results: "(r, conv') \<in> results_gpv \<I>' (run_converter conv q) \<Longrightarrow> r \<in> responses_\<I> \<I> q \<and> \<I>, \<I>' \<turnstile>\<^sub>C conv' \<surd>"
  using assms by(auto elim: WT_converter.cases)

lemma WT_converterD':
  assumes "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>" "q \<in> outs_\<I> \<I>"
  shows "\<I>' \<turnstile>g run_converter conv q \<surd> \<and> (\<forall>(r, conv') \<in> results_gpv \<I>' (run_converter conv q). r \<in> responses_\<I> \<I> q \<and> \<I>, \<I>' \<turnstile>\<^sub>C conv' \<surd>)"
  using assms by(auto elim: WT_converter.cases)

lemma WT_converter_bot1 [simp]: "bot, \<I> \<turnstile>\<^sub>C conv \<surd>"
  by(rule WT_converter.intros) auto

lemma WT_converter_mono: 
  "\<lbrakk> \<I>1,\<I>2 \<turnstile>\<^sub>C conv \<surd>; \<I>1' \<le> \<I>1; \<I>2 \<le> \<I>2' \<rbrakk>  \<Longrightarrow> \<I>1',\<I>2' \<turnstile>\<^sub>C conv \<surd> "
  apply(coinduction arbitrary: conv)
  apply(auto)
    apply(drule WT_converterD_WT)
     apply(erule (1) outs_\<I>_mono[THEN subsetD])
    apply(erule WT_gpv_mono)
     apply(erule outs_\<I>_mono)
    apply(erule (1) responses_\<I>_mono)
   apply(frule WT_converterD_results)
     apply(erule (1) outs_\<I>_mono[THEN subsetD])
    apply(erule results_gpv_mono[THEN subsetD])
     apply(erule WT_converterD_WT)
     apply(erule (1) outs_\<I>_mono[THEN subsetD])
    apply simp
   apply clarify
   apply(erule (2) responses_\<I>_mono[THEN subsetD])
  apply(frule WT_converterD_results)
    apply(erule (1) outs_\<I>_mono[THEN subsetD])
   apply(erule results_gpv_mono[THEN subsetD])
    apply(erule WT_converterD_WT)
    apply(erule (1) outs_\<I>_mono[THEN subsetD])
   apply simp
  apply simp
  done

lemma callee_invariant_on_run_resource [simp]: "callee_invariant_on run_resource (WT_resource \<I>) \<I>"
  by(unfold_locales)(auto dest: WT_resourceD intro: WT_calleeI)

interpretation run_resource: callee_invariant_on run_resource "WT_resource \<I>" \<I> for \<I>
  by simp

lemma raw_converter_invariant_run_converter: "raw_converter_invariant \<I> \<I>' run_converter (WT_converter \<I> \<I>')"
  by(unfold_locales)(auto dest: WT_converterD)

interpretation run_converter: raw_converter_invariant \<I> \<I>' run_converter "WT_converter \<I> \<I>'" for \<I> \<I>'
  by(rule raw_converter_invariant_run_converter)

lemma WT_converter_\<I>_full: "\<I>_full, \<I>_full \<turnstile>\<^sub>C conv \<surd>"
  by(coinduction arbitrary: conv)(auto)

lemma WT_converter_map_converter [WT_intro]:
  "\<I>, \<I>' \<turnstile>\<^sub>C map_converter f g f' g' conv \<surd>" if 
  *: "map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>, map_\<I> f' g' \<I>' \<turnstile>\<^sub>C conv \<surd>"
  and f: "inj f" and g: "surj g"
  using *
proof(coinduction arbitrary: conv)
  case (WT_converter q r conv' conv)
  have "?WT_gpv" using WT_converter
    by(auto intro!: WT_gpv_map_gpv' elim: WT_converterD_WT simp add: inv_into_f_f[OF f])
  moreover
  have "?results_gpv"
  proof(intro strip conjI disjI1)
    assume "(r, conv') \<in> results_gpv \<I>' (run_converter (map_converter f g f' g' conv) q)"
    then obtain r' conv''
      where results: "(r', conv'') \<in> results_gpv (map_\<I> f' g' \<I>') (run_converter conv (f q))"
        and r: "r = g r'"
        and conv': "conv' = map_converter f g f' g' conv''"
      by auto
    from WT_converterD_results[OF WT_converter(1), of "f q"] WT_converter(2) results 
    have r': "r' \<in> inv_into UNIV g ` responses_\<I> \<I> q"
      and WT': "map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>, map_\<I> f' g' \<I>' \<turnstile>\<^sub>C conv'' \<surd>"
      by(auto simp add: inv_into_f_f[OF f])
    from r' r show "r \<in> responses_\<I> \<I> q" by(auto simp add: surj_f_inv_f[OF g])

    show "\<exists>conv. conv' = map_converter f g f' g' conv \<and>
       map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>, map_\<I> f' g' \<I>' \<turnstile>\<^sub>C conv \<surd>"
      using conv' WT' by(auto)
  qed
  ultimately show ?case ..
qed


subsection \<open>Losslessness\<close>

coinductive plossless_converter :: "('a, 'b) \<I> \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool"
  for \<I> \<I>' where
    plossless_converterI: "plossless_converter \<I> \<I>' conv" if
    "\<And>a. a \<in> outs_\<I> \<I> \<Longrightarrow> plossless_gpv \<I>' (run_converter conv a)"
    "\<And>a b conv'. \<lbrakk> a \<in> outs_\<I> \<I>; (b, conv') \<in> results_gpv \<I>' (run_converter conv a) \<rbrakk> \<Longrightarrow> plossless_converter \<I> \<I>' conv'"

lemma plossless_converter_coinduct[consumes 1, case_names plossless_converter, case_conclusion plossless_converter plossless step, coinduct pred: plossless_converter]:
  assumes "X conv"
    and step: "\<And>conv a. \<lbrakk> X conv; a \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> plossless_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). X conv' \<or> plossless_converter \<I> \<I>' conv')"
  shows "plossless_converter \<I> \<I>' conv"
  using assms(1) by(rule plossless_converter.coinduct)(auto dest: step)

lemma plossless_converterD:
  "\<lbrakk> plossless_converter \<I> \<I>' conv; a \<in> outs_\<I> \<I> \<rbrakk> 
  \<Longrightarrow> plossless_gpv \<I>' (run_converter conv a) \<and>
     (\<forall>(b, conv') \<in> results_gpv \<I>' (run_converter conv a). plossless_converter \<I> \<I>' conv')"
  by(auto elim: plossless_converter.cases)

lemma plossless_converter_bot1 [simp]: "plossless_converter bot \<I> conv"
  by(rule plossless_converterI) auto

lemma plossless_converter_mono:
  assumes *: "plossless_converter \<I>1 \<I>2 conv"
    and le: "outs_\<I> \<I>1' \<subseteq> outs_\<I> \<I>1" "\<I>2 \<le> \<I>2'"
    and WT: "\<I>1, \<I>2 \<turnstile>\<^sub>C conv \<surd>"
  shows "plossless_converter \<I>1' \<I>2' conv"
  using * WT
  apply(coinduction arbitrary: conv)
  apply(drule plossless_converterD)
   apply(erule le(1)[THEN subsetD])
  apply(drule WT_converterD')
   apply(erule le(1)[THEN subsetD])
  using le(2)[THEN responses_\<I>_mono]
  by(auto intro: plossless_gpv_mono[OF _ le(2)] results_gpv_mono[OF le(2), THEN subsetD] dest: bspec)

lemma raw_converter_invariant_run_plossless_converter: "raw_converter_invariant \<I> \<I>' run_converter (\<lambda>conv. plossless_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>)"
  by(unfold_locales)(auto dest: WT_converterD plossless_converterD)

interpretation run_plossless_converter: raw_converter_invariant
  \<I> \<I>' run_converter "\<lambda>conv. plossless_converter \<I> \<I>' conv \<and> \<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>" for \<I> \<I>'
  by(rule raw_converter_invariant_run_plossless_converter)

named_theorems plossless_intro "Introduction rules for probabilistic losslessness"

subsection \<open>Operations\<close>

context
  fixes callee :: "'s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's, 'out, 'in) gpv"
begin

primcorec converter_of_callee :: "'s \<Rightarrow> ('a, 'b, 'out, 'in) converter" where
  "run_converter (converter_of_callee s) = (\<lambda>a. map_gpv (map_prod id converter_of_callee) id (callee s a))"

end

lemma converter_of_callee_parametric [transfer_rule]: includes lifting_syntax shows
  "((S ===> A ===> rel_gpv'' (rel_prod B S) C R) ===> S ===> rel_converter A B C R)
  converter_of_callee converter_of_callee"
  unfolding converter_of_callee_def supply map_gpv_parametric'[transfer_rule] by transfer_prover

lemma map_converter_of_callee:
  "map_converter f g h k (converter_of_callee callee s) =
   converter_of_callee (map_fun id (map_fun f (map_gpv' (map_prod g id) h k)) callee) s"
proof(coinduction arbitrary: s)
  case Eq_converter
  have *: "map_gpv' (map_prod g id) h k gpv = map_gpv (map_prod g id) id (map_gpv' id h k gpv)" for gpv
    by(simp add: map_gpv_conv_map_gpv' gpv.compositionality)
  show ?case
    by(auto simp add: rel_fun_def map_gpv'_map_gpv_swap gpv.rel_map * intro!: gpv.rel_refl_strong)
qed

lemma WT_converter_of_callee:
  assumes WT: "\<And>s q. q \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g callee s q \<surd>"
    and res: "\<And>s q r s'. \<lbrakk> q \<in> outs_\<I> \<I>; (r, s') \<in> results_gpv \<I>' (callee s q) \<rbrakk> \<Longrightarrow> r \<in> responses_\<I> \<I> q"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C converter_of_callee callee s \<surd>"
  by(coinduction arbitrary: s)(auto simp add: WT res)

text \<open>
  We can define two versions of parallel composition. One that attaches to the same interface 
  and one that attach to different interfaces. We choose the one variant where both attach to the same interface
  because (1) this is more general and (2) we do not have to assume that the resource respects the parallel composition. 
\<close>

primcorec parallel_converter
  :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('c, 'd, 'out, 'in) converter \<Rightarrow> ('a + 'c, 'b + 'd, 'out, 'in) converter"
  where
    "run_converter (parallel_converter conv1 conv2) = (\<lambda>ac. case ac of
     Inl a \<Rightarrow> map_gpv (map_prod Inl (\<lambda>conv1'. parallel_converter conv1' conv2)) id (run_converter conv1 a)
   | Inr b \<Rightarrow> map_gpv (map_prod Inr (\<lambda>conv2'. parallel_converter conv1 conv2')) id (run_converter conv2 b))"

lemma parallel_callee_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C R ===> rel_converter A' B' C R ===> rel_converter (rel_sum A A') (rel_sum B B') C R)
   parallel_converter parallel_converter"
  unfolding parallel_converter_def supply map_gpv_parametric'[transfer_rule] by transfer_prover

lemma parallel_converter_assoc:
  "parallel_converter (parallel_converter conv1 conv2) conv3 =
   map_converter rsuml lsumr id id (parallel_converter conv1 (parallel_converter conv2 conv3))"
  by(coinduction arbitrary: conv1 conv2 conv3)
    (auto 4 5 intro!: rel_funI gpv.rel_refl_strong split: sum.split simp add: gpv.rel_map map_gpv'_id map_gpv_conv_map_gpv'[symmetric])

lemma plossless_parallel_converter [plossless_intro]:
  "\<lbrakk> plossless_converter \<I>1 \<I> conv1; plossless_converter \<I>2 \<I> conv2; \<I>1, \<I> \<turnstile>\<^sub>C conv1 \<surd>; \<I>2, \<I> \<turnstile>\<^sub>C conv2 \<surd> \<rbrakk>
  \<Longrightarrow> plossless_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<I> (parallel_converter conv1 conv2)"
  by(coinduction arbitrary: conv1 conv2)
    (clarsimp; erule PlusE; drule (1) plossless_converterD; drule (1) WT_converterD'; fastforce)

primcorec id_converter :: "('a, 'b, 'a, 'b) converter" where
  "run_converter id_converter = (\<lambda>a.
   map_gpv (map_prod id (\<lambda>_. id_converter)) id (Pause a (\<lambda>b. Done (b, ()))))"

lemma id_converter_parametric [transfer_rule]: "rel_converter A B A B id_converter id_converter"
  unfolding id_converter_def 
  supply map_gpv_parametric'[transfer_rule] Done_parametric'[transfer_rule] Pause_parametric'[transfer_rule]
  by transfer_prover

lemma converter_of_callee_id_oracle [simp]:
  "converter_of_callee id_oracle s = id_converter"
  by(coinduction) (auto simp add: id_oracle_def)

lemma conv_callee_plus_id_left: "converter_of_callee (plus_intercept id_oracle callee) s =
  parallel_converter id_converter (converter_of_callee callee s) "
  by (coinduction arbitrary: callee s)
    (clarsimp split!: sum.split intro!: rel_funI
      , force simp add: gpv.rel_map id_oracle_def, force simp add: gpv.rel_map intro!: gpv.rel_refl)

lemma conv_callee_plus_id_right: "converter_of_callee (plus_intercept callee id_oracle) s =
  parallel_converter (converter_of_callee callee s) id_converter"
  by (coinduction arbitrary: callee s)
    (clarsimp split!: sum.split intro!: rel_funI
      , (force intro: gpv.rel_refl | simp add: gpv.rel_map id_oracle_def)+)

lemma plossless_id_converter [simp, plossless_intro]: "plossless_converter \<I> \<I> id_converter"
  by(coinduction) auto

lemma WT_converter_id [simp, intro, WT_intro]: "\<I>, \<I> \<turnstile>\<^sub>C id_converter \<surd>"
  by(coinduction) auto

lemma WT_map_converter_idD:
  "\<I>,\<I>' \<turnstile>\<^sub>C map_converter id id f g id_converter \<surd> \<Longrightarrow> \<I> \<le> map_\<I> f g \<I>'"
  unfolding le_\<I>_def by(auto 4 3 dest: WT_converterD)


definition fail_converter :: "('a, 'b, 'out, 'in) converter" where
  "fail_converter = Converter (\<lambda>_. Fail)"

lemma fail_converter_sel [simp]: "run_converter fail_converter a = Fail"
  by(simp add: fail_converter_def)

lemma fail_converter_parametric [transfer_rule]: "rel_converter A B C R fail_converter fail_converter"
  unfolding fail_converter_def supply Fail_parametric'[transfer_rule] by transfer_prover

lemma plossless_fail_converter [simp]: "plossless_converter \<I> \<I>' fail_converter \<longleftrightarrow> \<I> = bot" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  show ?rhs if ?lhs using that by(cases)(auto intro!: \<I>_eqI)
qed simp

lemma plossless_fail_converterI [plossless_intro]: "plossless_converter bot \<I>' fail_converter"
  by simp

lemma WT_fail_converter [simp, WT_intro]: "\<I>, \<I>' \<turnstile>\<^sub>C fail_converter \<surd>"
  by(rule WT_converter.intros) simp_all

lemma map_converter_id_move_left:
  "map_converter f g f' g' id_converter = map_converter (f' \<circ> f) (g \<circ> g') id id id_converter"
  by coinduction(simp add: rel_funI)

lemma map_converter_id_move_right:
  "map_converter f g f' g' id_converter = map_converter id id (f' \<circ> f) (g \<circ> g') id_converter"
  by coinduction(simp add: rel_funI)


text \<open>
  And here is the version for parallel composition that assumes disjoint interfaces.
\<close>
primcorec parallel_converter2
  :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('c, 'd, 'out', 'in') converter \<Rightarrow> ('a + 'c, 'b + 'd, 'out + 'out', 'in + 'in') converter"
  where
    "run_converter (parallel_converter2 conv1 conv2) = (\<lambda>ac. case ac of
     Inl a \<Rightarrow> map_gpv (map_prod Inl (\<lambda>conv1'. parallel_converter2 conv1' conv2)) id (left_gpv (run_converter conv1 a))
   | Inr b \<Rightarrow> map_gpv (map_prod Inr (\<lambda>conv2'. parallel_converter2 conv1 conv2')) id (right_gpv (run_converter conv2 b)))"

lemma parallel_converter2_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C R ===> rel_converter A' B' C' R' 
   ===> rel_converter (rel_sum A A') (rel_sum B B') (rel_sum C C') (rel_sum R R'))
  parallel_converter2 parallel_converter2"
  unfolding parallel_converter2_def
  supply left_gpv_parametric'[transfer_rule] right_gpv_parametric'[transfer_rule] map_gpv_parametric'[transfer_rule]
  by transfer_prover

lemma map_converter_parallel_converter2:
  "map_converter (map_sum f f') (map_sum g g') (map_sum h h') (map_sum k k') (parallel_converter2 conv1 conv2) =
   parallel_converter2 (map_converter f g h k conv1) (map_converter f' g' h' k' conv2)"
  using parallel_converter2_parametric[of
      "conversep (BNF_Def.Grp UNIV f)" "BNF_Def.Grp UNIV g"  "BNF_Def.Grp UNIV h"  "conversep (BNF_Def.Grp UNIV k)"
      "conversep (BNF_Def.Grp UNIV f')" "BNF_Def.Grp UNIV g'"  "BNF_Def.Grp UNIV h'"  "conversep (BNF_Def.Grp UNIV k')"]
  unfolding sum.rel_conversep sum.rel_Grp
  by(simp add: rel_converter_Grp rel_fun_def Grp_iff)

lemma WT_converter_parallel_converter2 [WT_intro]:
  assumes "\<I>1,\<I>2 \<turnstile>\<^sub>C conv1 \<surd>"
    and "\<I>1',\<I>2' \<turnstile>\<^sub>C conv2 \<surd>"
  shows "\<I>1 \<oplus>\<^sub>\<I> \<I>1',\<I>2 \<oplus>\<^sub>\<I> \<I>2' \<turnstile>\<^sub>C parallel_converter2 conv1 conv2 \<surd>"
  using assms
  apply(coinduction arbitrary: conv1 conv2)
  apply(clarsimp split!: sum.split)
  subgoal by(auto intro: WT_gpv_left_gpv dest: WT_converterD_WT)
  subgoal by(auto dest: WT_converterD_results)
  subgoal by(auto dest: WT_converterD_results)
  subgoal by(auto intro: WT_gpv_right_gpv dest: WT_converterD_WT)
  subgoal by(auto dest: WT_converterD_results)
  subgoal by(auto 4 3 dest: WT_converterD_results)
  done

lemma plossless_parallel_converter2 [plossless_intro]:
  assumes "plossless_converter \<I>1 \<I>1' conv1"
    and "plossless_converter \<I>2 \<I>2' conv2"
  shows "plossless_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>1' \<oplus>\<^sub>\<I> \<I>2') (parallel_converter2 conv1 conv2)"
  using assms
  by(coinduction arbitrary: conv1 conv2)
    ((rule exI conjI refl)+ | auto dest: plossless_converterD)+

lemma parallel_converter2_map1_out:
  "parallel_converter2 (map_converter f g h k conv1) conv2 =
   map_converter (map_sum f id) (map_sum g id) (map_sum h id) (map_sum k id) (parallel_converter2 conv1 conv2)"
  by(simp add: map_converter_parallel_converter2)

lemma parallel_converter2_map2_out:
  "parallel_converter2 conv1 (map_converter f g h k conv2) =
   map_converter (map_sum id f) (map_sum id g) (map_sum id h) (map_sum id k) (parallel_converter2 conv1 conv2)"
  by(simp add: map_converter_parallel_converter2)


primcorec left_interface :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('a, 'b, 'out + 'out', 'in + 'in') converter" where
  "run_converter (left_interface conv) = (\<lambda>a. map_gpv (map_prod id left_interface) id (left_gpv (run_converter conv a)))"

lemma left_interface_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C R ===> rel_converter A B (rel_sum C C') (rel_sum R R')) left_interface left_interface"
  unfolding left_interface_def
  supply left_gpv_parametric'[transfer_rule] map_gpv_parametric'[transfer_rule] by transfer_prover

primcorec right_interface :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('a, 'b, 'out' + 'out, 'in' + 'in) converter" where
  "run_converter (right_interface conv) = (\<lambda>a. map_gpv (map_prod id right_interface) id (right_gpv (run_converter conv a)))"

lemma right_interface_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C' R' ===> rel_converter A B (rel_sum C C') (rel_sum R R')) right_interface right_interface"
  unfolding right_interface_def
  supply right_gpv_parametric'[transfer_rule] map_gpv_parametric'[transfer_rule] by transfer_prover

lemma parallel_converter2_alt_def:
  "parallel_converter2 conv1 conv2 = parallel_converter (left_interface conv1) (right_interface conv2)"
  by(coinduction arbitrary: conv1 conv2 rule: converter.coinduct_strong)
    (auto 4 5 intro!: rel_funI gpv.rel_refl_strong split: sum.split simp add: gpv.rel_map)

lemma conv_callee_parallel_id_left: "converter_of_callee (parallel_intercept id_oracle callee) (s, s') =
  parallel_converter2 (id_converter) (converter_of_callee callee s')"
  apply (coinduction arbitrary: callee s')
  apply (rule rel_funI)
  apply (clarsimp simp add: gpv.rel_map left_gpv_map[of _ _ _ "id"] 
      right_gpv_map[of _ _ _ "id"] split!: sum.split)
   apply (force simp add: id_oracle_def split!: sum.split)
  apply (rule gpv.rel_refl)
  by force+

lemma conv_callee_parallel_id_right: "converter_of_callee (parallel_intercept callee id_oracle) (s, s') =
  parallel_converter2 (converter_of_callee callee s) (id_converter)"
  apply (coinduction arbitrary: callee s)
  apply (rule rel_funI)
  apply (clarsimp simp add: gpv.rel_map left_gpv_map[of _ _ _ "id"] 
      right_gpv_map[of _ _ _ "id"] split!: sum.split)
   apply (rule gpv.rel_refl)
  by (force simp add: id_oracle_def  split!: sum.split)+

lemma conv_callee_parallel: "converter_of_callee (parallel_intercept callee1 callee2) (s,s') 
  = parallel_converter2 (converter_of_callee callee1 s) (converter_of_callee callee2 s')"
  apply (coinduction arbitrary: callee1 callee2 s s')
  apply (clarsimp simp add: gpv.rel_map left_gpv_map[of _ _ _ "id"] right_gpv_map[of _ _ _ "id"] intro!: rel_funI split!: sum.split)
   apply (rule gpv.rel_refl)
    apply force+
  apply (rule gpv.rel_refl)
  by force+

lemma WT_converter_parallel_converter [WT_intro]:
  assumes "\<I>1, \<I> \<turnstile>\<^sub>C conv1 \<surd>"
    and "\<I>2, \<I> \<turnstile>\<^sub>C conv2 \<surd>"
  shows "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I> \<turnstile>\<^sub>C parallel_converter conv1 conv2 \<surd>"
  using assms by(coinduction arbitrary: conv1 conv2)(auto 4 4 dest: WT_converterD intro!: imageI)

primcorec converter_of_resource :: "('a, 'b) resource \<Rightarrow> ('a, 'b, 'c, 'd) converter" where
  "run_converter (converter_of_resource res) = (\<lambda>x. map_gpv (map_prod id converter_of_resource) id (lift_spmf (run_resource res x)))"

lemma WT_converter_of_resource [WT_intro]:
  assumes "\<I> \<turnstile>res res \<surd>"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C converter_of_resource res \<surd>"
  using assms by(coinduction arbitrary: res)(auto dest: WT_resourceD)

lemma plossless_converter_of_resource [plossless_intro]:
  assumes "lossless_resource \<I> res"
  shows "plossless_converter \<I> \<I>' (converter_of_resource res)"
  using assms by(coinduction arbitrary: res)(auto 4 3 dest: lossless_resourceD)

lemma plossless_converter_of_callee:
  assumes "\<And>s x. x \<in> outs_\<I> \<I>1 \<Longrightarrow> plossless_gpv \<I>2 (callee s x) \<and> (\<forall>(y, s')\<in>results_gpv \<I>2 (callee s x). y \<in> responses_\<I> \<I>1 x)"
  shows "plossless_converter \<I>1 \<I>2 (converter_of_callee callee s)"
  apply(coinduction arbitrary: s)
  subgoal for x s by(drule assms[where s=s]) auto
  done

context 
  fixes A :: "'a set"
  and \<I> :: "('c, 'd) \<I>"
begin

primcorec restrict_converter :: "('a, 'b, 'c, 'd) converter \<Rightarrow> ('a, 'b, 'c, 'd) converter"
  where 
  "run_converter (restrict_converter cnv) = (\<lambda>a. if a \<in> A then
     map_gpv (map_prod id (\<lambda>cnv'. restrict_converter cnv')) id (restrict_gpv \<I> (run_converter cnv a))
   else Fail)"

end

lemma WT_restrict_converter [WT_intro]:
  assumes "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<surd>"
  shows "\<I>,\<I>' \<turnstile>\<^sub>C restrict_converter A \<I>' cnv \<surd>"
  using assms by(coinduction arbitrary: cnv)(auto dest: WT_converterD dest!: in_results_gpv_restrict_gpvD)

lemma pgen_lossless_restrict_gpv [simp]:
  "\<I> \<turnstile>g gpv \<surd> \<Longrightarrow> pgen_lossless_gpv b \<I> (restrict_gpv \<I> gpv) = pgen_lossless_gpv b \<I> gpv"
  unfolding pgen_lossless_gpv_def by(simp add: expectation_gpv_restrict_gpv)

lemma plossless_restrict_converter [simp]:
  assumes "plossless_converter \<I> \<I>' conv"
    and "\<I>,\<I>' \<turnstile>\<^sub>C conv \<surd>"
    and "outs_\<I> \<I> \<subseteq> A"
  shows "plossless_converter \<I> \<I>' (restrict_converter A \<I>' conv)"
  using assms
  by(coinduction arbitrary: conv)
    (auto dest!: in_results_gpv_restrict_gpvD WT_converterD' plossless_converterD)

lemma plossless_map_converter:
  "plossless_converter \<I> \<I>' (map_converter f g h k conv)"
  if "plossless_converter (map_\<I> (inv_into UNIV f) (inv_into UNIV g) \<I>) (map_\<I> h k \<I>') conv" "inj f"
  using that
  by(coinduction arbitrary: conv)(auto dest!: plossless_converterD[where a="f _"])



subsection \<open>Attaching converters to resources\<close>

primcorec "attach" :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('out, 'in) resource \<Rightarrow> ('a, 'b) resource" where
  "run_resource (attach conv res) = (\<lambda>a. 
   map_spmf (\<lambda>((b, conv'), res'). (b, attach conv' res')) (exec_gpv run_resource (run_converter conv a) res))"

lemma attach_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C R ===> rel_resource C R ===> rel_resource A B) attach attach"
  unfolding attach_def
  supply exec_gpv_parametric'[transfer_rule] by transfer_prover

lemma attach_map_converter:
  "attach (map_converter f g h k conv) res = map_resource f g (attach conv (map_resource h k res))"
  using attach_parametric[of "conversep (BNF_Def.Grp UNIV f)" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h" "conversep (BNF_Def.Grp UNIV k)"]
  unfolding rel_converter_Grp rel_resource_Grp
  by (simp, rewrite at "rel_fun _ (rel_fun \<hole> _)" in asm conversep_iff[symmetric, abs_def])
    (simp add: rel_resource_conversep[symmetric] rel_fun_def Grp_iff conversep_conversep rel_resource_Grp)

lemma WT_resource_attach [WT_intro]: "\<lbrakk> \<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>; \<I>' \<turnstile>res res \<surd> \<rbrakk> \<Longrightarrow> \<I> \<turnstile>res attach conv res \<surd>"
  by(coinduction arbitrary: conv res)
    (auto 4 3 intro!: exI dest: run_resource.in_set_spmf_exec_gpv_into_results_gpv WT_converterD intro: run_resource.exec_gpv_invariant)

lemma lossless_attach [plossless_intro]:
  assumes "plossless_converter \<I> \<I>' conv"
    and "lossless_resource \<I>' res"
    and "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>" "\<I>' \<turnstile>res res \<surd>"
  shows "lossless_resource \<I> (attach conv res)"
  using assms
proof(coinduction arbitrary: res conv)
  case (lossless_resource a res conv)
  from plossless_converterD[OF lossless_resource(1,5)] have lossless: "plossless_gpv \<I>' (run_converter conv a)"
    "\<And>b conv'. (b, conv') \<in> results_gpv \<I>' (run_converter conv a) \<Longrightarrow> plossless_converter \<I> \<I>' conv'" by auto
  from WT_converterD'[OF lossless_resource(3,5)] have WT: "\<I>' \<turnstile>g run_converter conv a \<surd>"
    "\<And>b conv'. (b, conv') \<in> results_gpv \<I>' (run_converter conv a) \<Longrightarrow> b \<in> responses_\<I> \<I> a \<and> \<I>, \<I>' \<turnstile>\<^sub>C conv' \<surd>" by auto
  have ?lossless using lossless(1) WT(1) lossless_resource(2,4)
    by(auto intro: run_lossless_resource.plossless_exec_gpv dest: lossless_resourceD)
  moreover have ?step (is "\<forall>(b, res')\<in>?set. ?P b res' \<or> _")
  proof(safe)
    fix b res''
    assume "(b, res'') \<in> ?set"
    then obtain conv' res' where *: "((b, conv'), res') \<in> set_spmf (exec_gpv run_resource (run_converter conv a) res)"
      and [simp]: "res'' = attach conv' res'" by auto
    from run_lossless_resource.in_set_spmf_exec_gpv_into_results_gpv[OF *, of \<I>'] lossless_resource(2,4) WT
    have conv': "(b, conv') \<in> results_gpv \<I>' (run_converter conv a)" by auto
    from run_lossless_resource.exec_gpv_invariant[OF *, of \<I>'] WT(2)[OF this] WT(1) lossless(2)[OF this] lossless_resource
    show "?P b res''" by auto
  qed
  ultimately show ?case ..
qed


definition attach_callee
  :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's, 'out, 'in) gpv) 
  \<Rightarrow> ('s' \<Rightarrow> 'out \<Rightarrow> ('in \<times> 's') spmf)
  \<Rightarrow> ('s \<times> 's' \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's \<times> 's') spmf)" where
  "attach_callee callee oracle = (\<lambda>(s, s') q. map_spmf rprodl (exec_gpv oracle (callee s q) s'))"

lemma attach_callee_simps [simp]:
  "attach_callee callee oracle (s, s') q = map_spmf rprodl (exec_gpv oracle (callee s q) s')"
  by(simp add: attach_callee_def)

lemma attach_CNV_RES:
  "attach (converter_of_callee callee s) (resource_of_oracle res s') = 
   resource_of_oracle (attach_callee callee res) (s, s')"
  by(coinduction arbitrary: s s')
    (clarsimp simp add: spmf_rel_map rel_fun_def exec_gpv_map_gpv_id
      , rule exec_gpv_parametric[where S="\<lambda>l r. l = resource_of_oracle res r" and A="(=)" and CALL="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD, THEN rel_spmf_mono]
      , auto 4 3 simp add: rel_fun_def spmf_rel_map gpv.rel_eq intro!: rel_spmf_reflI)

lemma attach_stateless_callee:
  "attach_callee (stateless_callee callee) oracle = extend_state_oracle (\<lambda>s q. exec_gpv oracle (callee q) s)"
  by(simp add: attach_callee_def stateless_callee_def fun_eq_iff exec_gpv_map_gpv_id spmf.map_comp o_def split_def apfst_def map_prod_def)

lemma attach_id_converter [simp]: "attach id_converter res = res"
  by(coinduction arbitrary: res)(auto simp add: rel_fun_def spmf_rel_map split_def map_spmf_conv_bind_spmf[symmetric] intro!: rel_spmf_reflI)

lemma attach_callee_parallel_intercept: includes lifting_syntax shows
  "attach_callee (parallel_intercept callee1 callee2) (plus_oracle oracle1 oracle2) =
   (rprodl ---> id ---> map_spmf (map_prod id lprodr)) (plus_oracle (lift_state_oracle extend_state_oracle (attach_callee callee1 oracle1)) (extend_state_oracle (attach_callee callee2 oracle2)))"
proof ((rule ext)+, clarify, goal_cases)
  case (1 s1 s2 s q)
  then show ?case by(cases q) (auto simp add: exec_gpv_plus_oracle_left exec_gpv_plus_oracle_right spmf.map_comp apfst_def o_def prod.map_comp split_def exec_gpv_map_gpv_id intro!: map_spmf_cong)
qed

lemma attach_callee_id_oracle [simp]:
  "attach_callee id_oracle oracle = extend_state_oracle oracle"
  by(clarsimp simp add: fun_eq_iff id_oracle_def map_spmf_conv_bind_spmf split_def)

lemma attach_parallel2: "attach (parallel_converter2 conv1 conv2) (parallel_resource res1 res2)
  = parallel_resource (attach conv1 res1) (attach conv2 res2)"
  apply(coinduction arbitrary: conv1 conv2 res1 res2)
  apply simp
  apply(rule rel_funI)
  apply clarsimp
  apply(simp split!: sum.split)
  subgoal for conv1 conv2 res1 res2 a
    apply(simp add: exec_gpv_map_gpv_id spmf_rel_map)
    apply(rule rel_spmf_mono)
     apply(rule
        exec_gpv_parametric'[where ?S = "\<lambda>res1res2 res1. res1res2 = parallel_resource res1 res2" and
          A="(=)" and CALL="\<lambda>l r. l = Inl r" and R="\<lambda>l r. l = Inl r", 
          THEN rel_funD, THEN rel_funD, THEN rel_funD
          ])
    subgoal by(auto simp add: rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)
    subgoal by (simp add: left_gpv_Inl_transfer)
    subgoal by blast
    apply clarsimp
    apply(rule exI conjI refl)+
    done
  subgoal for conv1 conv2 res1 res2 a
    apply(simp add: exec_gpv_map_gpv_id spmf_rel_map)
    apply(rule rel_spmf_mono)
     apply(rule
        exec_gpv_parametric'[where ?S = "\<lambda>res1res2 res2. res1res2 = parallel_resource res1 res2" and
          A="(=)" and CALL="\<lambda>l r. l = Inr r" and R="\<lambda>l r. l = Inr r", 
          THEN rel_funD, THEN rel_funD, THEN rel_funD
          ])
    subgoal by(auto simp add: rel_fun_def spmf_rel_map intro: rel_spmf_reflI)
    subgoal by (simp add: right_gpv_Inr_transfer)
    subgoal by blast
    apply clarsimp
    apply(rule exI conjI refl)+
    done
  done

subsection \<open>Composing converters\<close>

primcorec comp_converter :: "('a, 'b, 'out, 'in) converter \<Rightarrow> ('out, 'in, 'out', 'in') converter \<Rightarrow> ('a, 'b, 'out', 'in') converter" where
  "run_converter (comp_converter conv1 conv2) = (\<lambda>a.
  map_gpv (\<lambda>((b, conv1'), conv2'). (b, comp_converter conv1' conv2')) id (inline run_converter (run_converter conv1 a) conv2))"

lemma comp_converter_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_converter A B C R ===> rel_converter C R C' R' ===> rel_converter A B C' R')
  comp_converter comp_converter"
  unfolding comp_converter_def
  supply inline_parametric'[transfer_rule] map_gpv_parametric'[transfer_rule] by transfer_prover

lemma comp_converter_map_converter1:
  fixes conv' :: "('a, 'b, 'out, 'in) converter" shows
    "comp_converter (map_converter f g h k conv) conv' = map_converter f g id id (comp_converter conv (map_converter h k id id conv'))"
  using comp_converter_parametric[of
      "conversep (BNF_Def.Grp UNIV f)" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h" "conversep (BNF_Def.Grp UNIV k)"
      "BNF_Def.Grp UNIV (id :: 'out \<Rightarrow> _)" "conversep (BNF_Def.Grp UNIV (id :: 'in \<Rightarrow> _))"
      ]
  apply(unfold rel_converter_Grp)
  apply(simp add: rel_fun_def Grp_iff)
  apply(rewrite at "\<forall>_ _ _. \<hole> \<longrightarrow> _" in asm conversep_iff[symmetric])
  apply(unfold rel_converter_conversep[symmetric] conversep_conversep eq_alt[symmetric])
  apply(rewrite in "rel_converter _ _ \<hole> _" in asm conversep_eq)
  apply(rewrite in "rel_converter _ _ _ \<hole>" in asm conversep_eq[symmetric])
  apply(rewrite in "rel_converter _ _ \<hole> _" in asm eq_alt)
  apply(rewrite in "rel_converter _ _ _ \<hole>" in asm eq_alt)
  apply(unfold rel_converter_Grp)
  apply(simp add: Grp_iff)
  done

lemma comp_converter_map_converter2:
  fixes conv :: "('a, 'b, 'out, 'in) converter" shows
    "comp_converter conv (map_converter f g h k conv') = map_converter id id h k (comp_converter (map_converter id id f g conv) conv')"
  using comp_converter_parametric[of
      "BNF_Def.Grp UNIV (id :: 'a \<Rightarrow> _)" "conversep (BNF_Def.Grp UNIV (id :: 'b \<Rightarrow> _))"
      "conversep (BNF_Def.Grp UNIV f)" "BNF_Def.Grp UNIV g" "BNF_Def.Grp UNIV h" "conversep (BNF_Def.Grp UNIV k)"
      ]
  apply(unfold rel_converter_Grp)
  apply(simp add: rel_fun_def Grp_iff)
  apply(rewrite at "\<forall>_ _. \<hole> \<longrightarrow> _" in asm conversep_iff[symmetric])
  apply(unfold rel_converter_conversep[symmetric] conversep_conversep rel_converter_Grp)
  apply simp
  apply(unfold eq_alt[symmetric])
  apply(rewrite in "rel_converter _ \<hole>" in asm conversep_eq)
  apply(rewrite in "rel_converter \<hole> _" in asm conversep_eq[symmetric])
  apply(rewrite in "rel_converter \<hole> _" in asm eq_alt)
  apply(rewrite in "rel_converter _ \<hole>" in asm eq_alt)
  apply(unfold rel_converter_Grp)
  apply(simp add: Grp_iff)
  done

lemma attach_compose:
  "attach (comp_converter conv1 conv2) res = attach conv1 (attach conv2 res)"
  apply(coinduction arbitrary: conv1 conv2 res)
  apply(auto intro!: rel_funI simp add: spmf_rel_map exec_gpv_map_gpv_id exec_gpv_inline o_def split_beta)
  including lifting_syntax
  apply(rule rel_spmf_mono)
   apply(rule exec_gpv_parametric[where A="(=)" and CALL="(=)" and S="\<lambda>(l, r) s2. s2 = attach l r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
     prefer 4
     apply clarsimp
  by(auto simp add: case_prod_def spmf_rel_map gpv.rel_eq split_def intro!: rel_funI rel_spmf_reflI)


lemma comp_converter_assoc:
  "comp_converter (comp_converter conv1 conv2) conv3 = comp_converter conv1 (comp_converter conv2 conv3)"
  apply(coinduction arbitrary: conv1 conv2 conv3)
  apply(rule rel_funI)
  apply(clarsimp simp add: gpv.rel_map inline_map_gpv)
  apply(subst inline_assoc)
  apply(simp add: gpv.rel_map)
  including lifting_syntax
  apply(rule gpv.rel_mono_strong)
    apply(rule inline_parametric[where C="(=)" and C'="(=)" and A="(=)" and S="\<lambda>(l, r) s2. s2 = comp_converter l r", THEN rel_funD, THEN rel_funD, THEN rel_funD])
      prefer 4
      apply clarsimp
  by(auto simp add: gpv.rel_eq gpv.rel_map split_beta intro!: rel_funI gpv.rel_refl_strong)


lemma comp_converter_assoc_left:
  assumes "comp_converter conv1 conv2 = conv3"
  shows "comp_converter conv1 (comp_converter conv2 conv) = comp_converter conv3 conv"
  by(fold comp_converter_assoc)(simp add: assms)

lemma comp_converter_attach_left:
  assumes "comp_converter conv1 conv2 = conv3"
  shows "attach conv1 (attach conv2 res) = attach conv3 res"
  by(fold attach_compose)(simp add: assms)  

lemmas comp_converter_eqs = 
  asm_rl[where psi="x = y" for x y :: "(_, _, _, _) converter"]
  comp_converter_assoc_left
  comp_converter_attach_left

lemma WT_converter_comp [WT_intro]:
  "\<lbrakk> \<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>; \<I>', \<I>'' \<turnstile>\<^sub>C conv' \<surd> \<rbrakk> \<Longrightarrow> \<I>, \<I>'' \<turnstile>\<^sub>C comp_converter conv conv' \<surd>"
  by(coinduction arbitrary: conv conv')
    (auto; auto 4 4 dest: WT_converterD run_converter.results_gpv_inline intro: run_converter.WT_gpv_inline_invar[where \<I>=\<I>' and \<I>'=\<I>''])

lemma plossless_comp_converter [plossless_intro]:
  assumes "plossless_converter \<I> \<I>' conv"
    and "plossless_converter \<I>' \<I>'' conv'"
    and "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>" "\<I>', \<I>'' \<turnstile>\<^sub>C conv' \<surd>"
  shows "plossless_converter \<I> \<I>'' (comp_converter conv conv')"
  using assms
proof(coinduction arbitrary: conv conv')
  case (plossless_converter a conv conv')
  have conv1: "plossless_gpv \<I>' (run_converter conv a)" 
    using plossless_converter(1, 5) by(simp add: plossless_converterD)
  have conv2: "\<I>' \<turnstile>g run_converter conv a \<surd>"
    using plossless_converter(3, 5) by(simp add: WT_converterD)
  have ?plossless using plossless_converter(2,4,5)
    by(auto intro: run_plossless_converter.plossless_inline[OF conv1] dest: plossless_converterD intro: conv2)
  moreover have ?step (is "\<forall>(b, conv')\<in>?res. ?P b conv' \<or> _")
  proof(clarify)
    fix b conv''
    assume "(b, conv'') \<in> ?res"
    then obtain conv1 conv2 where [simp]: "conv'' = comp_converter conv1 conv2" 
      and inline: "((b, conv1), conv2) \<in> results_gpv \<I>'' (inline run_converter (run_converter conv a) conv')" 
      by auto
    from run_plossless_converter.results_gpv_inline[OF inline conv2] plossless_converter(2,4)
    have run: "(b, conv1) \<in> results_gpv \<I>' (run_converter conv a)"
      and *: "plossless_converter \<I>' \<I>'' conv2" "\<I>', \<I>'' \<turnstile>\<^sub>C conv2 \<surd>" by auto
    with WT_converterD(2)[OF plossless_converter(3,5) run] plossless_converterD[THEN conjunct2, rule_format, OF plossless_converter(1,5) run]
    show "?P b conv''" by auto
  qed
  ultimately show ?case ..
qed

lemma comp_converter_id_left: "comp_converter id_converter conv = conv"
  by (coinduction arbitrary:conv)
    (auto simp add: gpv.rel_map split_def map_gpv_conv_bind[symmetric]  intro!:rel_funI gpv.rel_refl_strong)

lemma comp_converter_id_right: "comp_converter conv id_converter = conv"
proof -
  have lem4: "inline run_converter gpv id_converter = inline id_oracle gpv id_converter" for gpv
    by (simp only: gpv.rel_eq[symmetric])
      (rule gpv.rel_mono_strong
        , rule inline_parametric[where A="(=)" and C="(=)" and C'="(=)" and S="\<lambda>l r. l = r \<and> r = id_converter", THEN rel_funD, THEN rel_funD, THEN rel_funD]
        , auto simp add: id_oracle_def intro!: rel_funI  gpv.rel_refl_strong)
  show ?thesis
    by (coinduction arbitrary:conv)
      (auto simp add: lem4 gpv.rel_map intro!:rel_funI gpv.rel_refl_strong)
qed

lemma comp_coverter_of_callee: "comp_converter (converter_of_callee callee1 s1) (converter_of_callee callee2 s2)
  = converter_of_callee (\<lambda>(s1, s2) q. map_gpv rprodl id (inline callee2 (callee1 s1 q) s2)) (s1, s2)"
  apply (coinduction arbitrary: callee1 s1 callee2 s2)
  apply (rule rel_funI)
  apply (clarsimp simp add: gpv.rel_map inline_map_gpv)
  subgoal for cal1 s1 cal2 s2 y
    apply (rule gpv.rel_mono_strong)
      apply (rule inline_parametric[where A="(=)" and C="(=)" and C'="(=)" and S="\<lambda>c s. c = converter_of_callee cal2 s", THEN rel_funD, THEN rel_funD, THEN rel_funD])
        apply(auto simp add: gpv.rel_eq rel_fun_def gpv.rel_map intro!: gpv.rel_refl_strong)
    by (auto simp add: rprodl_def intro!:exI)
  done

lemmas comp_converter_of_callee' = comp_converter_eqs[OF comp_coverter_of_callee]

lemma comp_converter_parallel2: "comp_converter (parallel_converter2 conv1l conv1r) (parallel_converter2 conv2l conv2r) =
  parallel_converter2 (comp_converter conv1l conv2l) (comp_converter conv1r conv2r)"
  apply (coinduction arbitrary: conv1l conv1r conv2l conv2r)
  apply (rule rel_funI)
  apply (clarsimp simp add: gpv.rel_map inline_map_gpv split!: sum.split)
  subgoal for conv1l conv1r conv2l conv2r input
    apply(subst left_gpv_map[where h=id])
    apply(simp add: gpv.rel_map left_gpv_inline)
    apply(unfold rel_gpv_conv_rel_gpv'')
    apply(rule rel_gpv''_mono[THEN predicate2D, rotated -1])
       apply(rule inline_parametric'[where S="\<lambda>c1 c2. c1 = parallel_converter2 c2 conv2r" and C="\<lambda>l r. l = Inl r" and R="\<lambda>l r. l = Inl r" and C' = "(=)" and R'="(=)",
          THEN rel_funD, THEN rel_funD, THEN rel_funD])
    subgoal by(auto split: sum.split simp add: gpv.rel_map rel_gpv_conv_rel_gpv''[symmetric] intro!:  gpv.rel_refl_strong rel_funI)
        apply(rule left_gpv_Inl_transfer)
       apply(auto 4 6 simp add: sum.map_id)
    done
  subgoal for conv1l conv1r conv2l conv2r input
    apply(subst right_gpv_map[where h=id])
    apply(simp add: gpv.rel_map right_gpv_inline)
    apply(unfold rel_gpv_conv_rel_gpv'')
    apply(rule rel_gpv''_mono[THEN predicate2D, rotated -1])
       apply(rule inline_parametric'[where S="\<lambda>c1 c2. c1 = parallel_converter2 conv2l c2" and C="\<lambda>l r. l = Inr r" and R="\<lambda>l r. l = Inr r" and C' = "(=)" and R'="(=)",
          THEN rel_funD, THEN rel_funD, THEN rel_funD])
    subgoal by(auto split: sum.split simp add: gpv.rel_map rel_gpv_conv_rel_gpv''[symmetric] intro!:  gpv.rel_refl_strong rel_funI)
        apply(rule right_gpv_Inr_transfer)
       apply(auto 4 6 simp add: sum.map_id)
    done
  done

lemmas comp_converter_parallel2' = comp_converter_eqs[OF comp_converter_parallel2]

lemma comp_converter_map1_out:
  "comp_converter (map_converter f g id id conv) conv' = map_converter f g id id (comp_converter conv conv')"
  by(simp add: comp_converter_map_converter1)

lemma parallel_converter2_comp1_out:
  "parallel_converter2 (comp_converter conv conv') conv'' = comp_converter (parallel_converter2 conv id_converter) (parallel_converter2 conv' conv'')"
  by(simp add: comp_converter_parallel2 comp_converter_id_left)

lemma parallel_converter2_comp2_out:
  "parallel_converter2 conv'' (comp_converter conv conv') = comp_converter (parallel_converter2 id_converter conv) (parallel_converter2 conv'' conv')"
  by(simp add: comp_converter_parallel2 comp_converter_id_left)

subsection \<open>Interaction bound\<close>

coinductive interaction_any_bounded_converter :: "('a, 'b, 'c, 'd) converter \<Rightarrow> enat \<Rightarrow> bool" where
  "interaction_any_bounded_converter conv n" if
  "\<And>a. interaction_any_bounded_by (run_converter conv a) n"
  "\<And>a b conv'. (b, conv') \<in> results'_gpv (run_converter conv a) \<Longrightarrow> interaction_any_bounded_converter conv' n"

lemma interaction_any_bounded_converterD:
  assumes "interaction_any_bounded_converter conv n"
  shows "interaction_any_bounded_by (run_converter conv a) n \<and> (\<forall>(b, conv')\<in>results'_gpv (run_converter conv a). interaction_any_bounded_converter conv' n)"
  using assms
  by(auto elim: interaction_any_bounded_converter.cases)

lemma interaction_any_bounded_converter_mono:
  assumes "interaction_any_bounded_converter conv n"
    and "n \<le> m"
  shows "interaction_any_bounded_converter conv m"
  using assms
  by(coinduction arbitrary: conv)(auto elim: interaction_any_bounded_converter.cases intro: interaction_bounded_by_mono)

lemma interaction_any_bounded_converter_trivial [simp]: "interaction_any_bounded_converter conv \<infinity>"
  by(coinduction arbitrary: conv)
    (auto simp add: interaction_bounded_by.simps)

lemmas interaction_any_bounded_converter_start = 
  interaction_any_bounded_converter_mono
  interaction_bounded_by_mono

method interaction_bound_converter_start = (rule interaction_any_bounded_converter_start)
method interaction_bound_converter_step uses add simp =
  ((match conclusion in "interaction_bounded_by _ _ _" \<Rightarrow> fail \<bar> "interaction_any_bounded_converter _ _" \<Rightarrow> fail \<bar> _ \<Rightarrow> \<open>solves \<open>clarsimp simp add: simp\<close>\<close>) | rule add interaction_bound)
method interaction_bound_converter_rec uses add simp = 
  (interaction_bound_converter_step add: add simp: simp; (interaction_bound_converter_rec add: add simp: simp)?)
method interaction_bound_converter uses add simp =
  ((* use in *) interaction_bound_converter_start, interaction_bound_converter_rec add: add simp: simp)

lemma interaction_any_bounded_converter_id [interaction_bound]:
  "interaction_any_bounded_converter id_converter 1"
  by(coinduction) simp

lemma raw_converter_invariant_interaction_any_bounded_converter:
  "raw_converter_invariant \<I>_full \<I>_full run_converter (\<lambda>conv. interaction_any_bounded_converter conv n)"
  by(unfold_locales)(auto simp add: results_gpv_\<I>_full dest: interaction_any_bounded_converterD)

lemma interaction_bounded_by_left_gpv [interaction_bound]:
  assumes "interaction_bounded_by consider gpv n"
    and "\<And>x. consider' (Inl x) \<Longrightarrow> consider x"
  shows "interaction_bounded_by consider' (left_gpv gpv) n"
proof -
  define ib :: "('b, 'a, 'c) gpv \<Rightarrow> _" where "ib \<equiv> interaction_bound consider"
  have "interaction_bound consider' (left_gpv gpv) \<le> ib gpv"
  proof(induction arbitrary: gpv rule: interaction_bound_fixp_induct)
    case (step interaction_bound')
    show ?case unfolding ib_def
      apply(subst interaction_bound.simps)
      apply(rule SUP_least)
      apply(clarsimp split!: generat.split if_split)
       apply(rule SUP_upper2, assumption)
       apply(clarsimp split!: if_split simp add: assms(2))
       apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      apply(rule SUP_upper2, assumption)
      apply(clarsimp split!: if_split)
       apply(rule order_trans, rule ile_eSuc)
       apply(simp)
       apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      done
  qed simp_all
  then show ?thesis using assms(1)
    by(auto simp add: ib_def interaction_bounded_by.simps intro: order_trans)
qed

lemma interaction_bounded_by_right_gpv [interaction_bound]:
  assumes "interaction_bounded_by consider gpv n"
    and "\<And>x. consider' (Inr x) \<Longrightarrow> consider x"
  shows "interaction_bounded_by consider' (right_gpv gpv) n"
proof -
  define ib :: "('b, 'a, 'c) gpv \<Rightarrow> _" where "ib \<equiv> interaction_bound consider"
  have "interaction_bound consider' (right_gpv gpv) \<le> ib gpv"
  proof(induction arbitrary: gpv rule: interaction_bound_fixp_induct)
    case (step interaction_bound')
    show ?case unfolding ib_def
      apply(subst interaction_bound.simps)
      apply(rule SUP_least)
      apply(clarsimp split!: generat.split if_split)
       apply(rule SUP_upper2, assumption)
       apply(clarsimp split!: if_split simp add: assms(2))
       apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      apply(rule SUP_upper2, assumption)
      apply(clarsimp split!: if_split)
       apply(rule order_trans, rule ile_eSuc)
       apply(simp)
       apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      apply(rule SUP_mono)
      subgoal for \<dots> input
        by(cases input)(auto 4 3 intro: step.IH[unfolded ib_def] order_trans[OF step.hyps(1)])
      done
  qed simp_all
  then show ?thesis using assms(1)
    by(auto simp add: ib_def interaction_bounded_by.simps intro: order_trans)
qed

lemma interaction_any_bounded_converter_parallel_converter2:
  assumes "interaction_any_bounded_converter conv1 n"
    and "interaction_any_bounded_converter conv2 n"
  shows "interaction_any_bounded_converter (parallel_converter2 conv1 conv2) n"
  using assms
  by(coinduction arbitrary: conv1 conv2)
    (auto 4 4 split: sum.split intro!: interaction_bounded_by_map_gpv_id intro: interaction_bounded_by_left_gpv interaction_bounded_by_right_gpv elim: interaction_any_bounded_converter.cases)

lemma interaction_any_bounded_converter_parallel_converter2' [interaction_bound]:
  assumes "interaction_any_bounded_converter conv1 n"
    and "interaction_any_bounded_converter conv2 m"
  shows "interaction_any_bounded_converter (parallel_converter2 conv1 conv2) (max n m)"
  by(rule interaction_any_bounded_converter_parallel_converter2; rule assms[THEN interaction_any_bounded_converter_mono]; simp)

lemma interaction_any_bounded_converter_compose [interaction_bound]:
  assumes "interaction_any_bounded_converter conv1 n"
    and "interaction_any_bounded_converter conv2 m"
  shows "interaction_any_bounded_converter (comp_converter conv1 conv2) (n * m)"
proof -
  have [simp]: "\<lbrakk>interaction_any_bounded_converter conv1 n; interaction_any_bounded_converter conv2 m\<rbrakk> \<Longrightarrow>
    interaction_any_bounded_by (inline run_converter (run_converter conv1 x) conv2) (n * m)" for conv1 conv2 x
    by (rule interaction_bounded_by_inline_invariant[where I="\<lambda>conv2. interaction_any_bounded_converter conv2 m" and consider'="\<lambda>_. True"])
      (auto dest: interaction_any_bounded_converterD)

  show ?thesis using assms
    by(coinduction arbitrary: conv1 conv2)
      ((clarsimp simp add: results_gpv_\<I>_full[symmetric] | intro conjI strip interaction_bounded_by_map_gpv_id)+
        , drule raw_converter_invariant.results_gpv_inline[OF raw_converter_invariant_interaction_any_bounded_converter]
        , (rule exI conjI refl WT_gpv_full |  auto simp add: results_gpv_\<I>_full dest: interaction_any_bounded_converterD
          raw_converter_invariant.results_gpv_inline[OF raw_converter_invariant_interaction_any_bounded_converter])+ )
qed

lemma interaction_any_bounded_converter_of_callee [interaction_bound]:
  assumes "\<And>s x. interaction_any_bounded_by (conv s x) n"
  shows "interaction_any_bounded_converter (converter_of_callee conv s) n"
  by(coinduction arbitrary: s)(auto intro!: interaction_bounded_by_map_gpv_id assms)

lemma interaction_any_bounded_converter_map_converter [interaction_bound]:
  assumes "interaction_any_bounded_converter conv n"
    and "surj k"
  shows "interaction_any_bounded_converter (map_converter f g h k conv) n"
  using assms
  by(coinduction arbitrary: conv)
    (auto 4 3 simp add: assms results'_gpv_map_gpv'[OF \<open>surj k\<close>]  intro: assms  interaction_any_bounded_by_map_gpv' dest: interaction_any_bounded_converterD)

lemma interaction_any_bounded_converter_parallel_converter:
  assumes "interaction_any_bounded_converter conv1 n"
    and "interaction_any_bounded_converter conv2 n"
  shows "interaction_any_bounded_converter (parallel_converter conv1 conv2) n"
  using assms
  by(coinduction arbitrary: conv1 conv2)
    (auto 4 4 split: sum.split intro!: interaction_bounded_by_map_gpv_id elim: interaction_any_bounded_converter.cases)

lemma interaction_any_bounded_converter_parallel_converter' [interaction_bound]:
  assumes "interaction_any_bounded_converter conv1 n"
    and "interaction_any_bounded_converter conv2 m"
  shows "interaction_any_bounded_converter (parallel_converter conv1 conv2) (max n m)"
  by(rule interaction_any_bounded_converter_parallel_converter; rule assms[THEN interaction_any_bounded_converter_mono]; simp)

lemma interaction_any_bounded_converter_converter_of_resource:
  "interaction_any_bounded_converter (converter_of_resource res) n"
  by(coinduction arbitrary: res)(auto intro: interaction_bounded_by_map_gpv_id)

lemma interaction_any_bounded_converter_converter_of_resource' [interaction_bound]:
  "interaction_any_bounded_converter (converter_of_resource res) 0"
  by(rule interaction_any_bounded_converter_converter_of_resource)

lemma interaction_any_bounded_converter_restrict_converter [interaction_bound]:
  "interaction_any_bounded_converter (restrict_converter A \<I> cnv) bound"
  if "interaction_any_bounded_converter cnv bound"
  using that
  by(coinduction arbitrary: cnv)
    (auto 4 3 dest: interaction_any_bounded_converterD dest!: in_results'_gpv_restrict_gpvD intro!: interaction_bound)

end