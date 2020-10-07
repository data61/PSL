(* Title: Generative_Probabilistic_Value.thy
  Author: Andreas Lochbihler, ETH Zurich *)

theory Generative_Probabilistic_Value imports
  Resumption
  Generat
  "HOL-Types_To_Sets.Types_To_Sets"
begin

hide_const (open) Done

subsection \<open>Type definition\<close>

context notes [[bnf_internals]] begin

codatatype (results'_gpv: 'a, outs'_gpv: 'out, 'in) gpv
  = GPV (the_gpv: "('a, 'out, 'in \<Rightarrow> ('a, 'out, 'in) gpv) generat spmf")

end

declare gpv.rel_eq [relator_eq]

text \<open>Reactive values are like generative, except that they take an input first.\<close>

type_synonym ('a, 'out, 'in) rpv = "'in \<Rightarrow> ('a, 'out, 'in) gpv"
print_translation \<comment> \<open>pretty printing for @{typ "('a, 'out, 'in) rpv"}\<close> \<open>
  let
    fun tr' [in1, Const (@{type_syntax gpv}, _) $ a $ out $ in2] =
      if in1 = in2 then Syntax.const @{type_syntax rpv} $ a $ out $ in1
      else raise Match;
  in [(@{type_syntax "fun"}, K tr')]
  end
\<close>
typ "('a, 'out, 'in) rpv"
text \<open>
  Effectively, @{typ "('a, 'out, 'in) gpv"} and @{typ "('a, 'out, 'in) rpv"} are mutually recursive.
\<close>

lemma eq_GPV_iff: "f = GPV g \<longleftrightarrow> the_gpv f = g"
by(cases f) auto

declare gpv.set[simp del]

declare gpv.set_map[simp]

lemma rel_gpv_def':
  "rel_gpv A B gpv gpv' \<longleftrightarrow>
  (\<exists>gpv''. (\<forall>(x, y) \<in> results'_gpv gpv''. A x y) \<and> (\<forall>(x, y) \<in> outs'_gpv gpv''. B x y) \<and>
           map_gpv fst fst gpv'' = gpv \<and> map_gpv snd snd gpv'' = gpv')"
unfolding rel_gpv_def by(auto simp add: BNF_Def.Grp_def)

definition results'_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> 'a set"
where "results'_rpv rpv = range rpv \<bind> results'_gpv"

definition outs'_rpv :: "('a, 'out, 'in) rpv \<Rightarrow> 'out set"
where "outs'_rpv rpv = range rpv \<bind> outs'_gpv"

abbreviation rel_rpv
  :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> 'out' \<Rightarrow> bool)
  \<Rightarrow> ('in \<Rightarrow> ('a, 'out, 'in) gpv) \<Rightarrow> ('in \<Rightarrow> ('b, 'out', 'in) gpv) \<Rightarrow> bool"
where "rel_rpv A B \<equiv> rel_fun (=) (rel_gpv A B)"

lemma in_results'_rpv [iff]: "x \<in> results'_rpv rpv \<longleftrightarrow> (\<exists>input. x \<in> results'_gpv (rpv input))"
by(simp add: results'_rpv_def)

lemma in_outs_rpv [iff]: "out \<in> outs'_rpv rpv \<longleftrightarrow> (\<exists>input. out \<in> outs'_gpv (rpv input))"
by(simp add: outs'_rpv_def)

lemma results'_GPV [simp]:
  "results'_gpv (GPV r) =
   (set_spmf r \<bind> generat_pures) \<union> 
   ((set_spmf r \<bind> generat_conts) \<bind> results'_rpv)"
by(auto simp add: gpv.set bind_UNION set_spmf_def)

lemma outs'_GPV [simp]:
  "outs'_gpv (GPV r) =
   (set_spmf r \<bind> generat_outs) \<union> 
   ((set_spmf r \<bind> generat_conts) \<bind> outs'_rpv)"
by(auto simp add: gpv.set bind_UNION set_spmf_def)

lemma outs'_gpv_unfold:
  "outs'_gpv r =
   (set_spmf (the_gpv r) \<bind> generat_outs) \<union> 
   ((set_spmf (the_gpv r) \<bind> generat_conts) \<bind> outs'_rpv)"
by(cases r) simp

lemma outs'_gpv_induct [consumes 1, case_names Out Cont, induct set: outs'_gpv]:
  assumes x: "x \<in> outs'_gpv gpv"
  and Out: "\<And>generat gpv. \<lbrakk> generat \<in> set_spmf (the_gpv gpv); x \<in> generat_outs generat \<rbrakk> \<Longrightarrow> P gpv"
  and Cont: "\<And>generat gpv c input.
    \<lbrakk> generat \<in> set_spmf (the_gpv gpv); c \<in> generat_conts generat; x \<in> outs'_gpv (c input); P (c input) \<rbrakk> \<Longrightarrow> P gpv"
  shows "P gpv"
using x
apply(induction y\<equiv>"x" gpv)
 apply(rule Out, simp add: in_set_spmf, simp)
apply(erule imageE, rule Cont, simp add: in_set_spmf, simp, simp, simp)
.

lemma outs'_gpv_cases [consumes 1, case_names Out Cont, cases set: outs'_gpv]:
  assumes "x \<in> outs'_gpv gpv"
  obtains (Out) generat where "generat \<in> set_spmf (the_gpv gpv)" "x \<in> generat_outs generat"
    | (Cont) generat c input where "generat \<in> set_spmf (the_gpv gpv)" "c \<in> generat_conts generat" "x \<in> outs'_gpv (c input)"
using assms by cases(auto simp add: in_set_spmf)

lemma outs'_gpvI [intro?]:
  shows outs'_gpv_Out: "\<lbrakk> generat \<in> set_spmf (the_gpv gpv); x \<in> generat_outs generat \<rbrakk> \<Longrightarrow> x \<in> outs'_gpv gpv"
  and outs'_gpv_Cont: "\<lbrakk> generat \<in> set_spmf (the_gpv gpv); c \<in> generat_conts generat; x \<in> outs'_gpv (c input) \<rbrakk> \<Longrightarrow> x \<in> outs'_gpv gpv"
by(auto intro: gpv.set_sel simp add: in_set_spmf)

lemma results'_gpv_induct [consumes 1, case_names Pure Cont, induct set: results'_gpv]:
  assumes x: "x \<in> results'_gpv gpv"
  and Pure: "\<And>generat gpv. \<lbrakk> generat \<in> set_spmf (the_gpv gpv); x \<in> generat_pures generat \<rbrakk> \<Longrightarrow> P gpv"
  and Cont: "\<And>generat gpv c input.
    \<lbrakk> generat \<in> set_spmf (the_gpv gpv); c \<in> generat_conts generat; x \<in> results'_gpv (c input); P (c input) \<rbrakk> \<Longrightarrow> P gpv"
  shows "P gpv"
using x
apply(induction y\<equiv>"x" gpv)
 apply(rule Pure; simp add: in_set_spmf)
apply(erule imageE, rule Cont, simp add: in_set_spmf, simp, simp, simp)
.

lemma results'_gpv_cases [consumes 1, case_names Pure Cont, cases set: results'_gpv]:
  assumes "x \<in> results'_gpv gpv"
  obtains (Pure) generat where "generat \<in> set_spmf (the_gpv gpv)" "x \<in> generat_pures generat"
    | (Cont) generat c input where "generat \<in> set_spmf (the_gpv gpv)" "c \<in> generat_conts generat" "x \<in> results'_gpv (c input)"
using assms by cases(auto simp add: in_set_spmf)

lemma results'_gpvI [intro?]:
  shows results'_gpv_Pure: "\<lbrakk> generat \<in> set_spmf (the_gpv gpv); x \<in> generat_pures generat \<rbrakk> \<Longrightarrow> x \<in> results'_gpv gpv"
  and results'_gpv_Cont: "\<lbrakk> generat \<in> set_spmf (the_gpv gpv); c \<in> generat_conts generat; x \<in> results'_gpv (c input) \<rbrakk> \<Longrightarrow> x \<in> results'_gpv gpv"
by(auto intro: gpv.set_sel simp add: in_set_spmf)

lemma left_unique_rel_gpv [transfer_rule]:
  "\<lbrakk> left_unique A; left_unique B \<rbrakk> \<Longrightarrow> left_unique (rel_gpv A B)"
unfolding left_unique_alt_def gpv.rel_conversep[symmetric] gpv.rel_compp[symmetric]
by(subst gpv.rel_eq[symmetric])(rule gpv.rel_mono)

lemma right_unique_rel_gpv [transfer_rule]:
  "\<lbrakk> right_unique A; right_unique B \<rbrakk> \<Longrightarrow> right_unique (rel_gpv A B)"
unfolding right_unique_alt_def gpv.rel_conversep[symmetric] gpv.rel_compp[symmetric]
by(subst gpv.rel_eq[symmetric])(rule gpv.rel_mono)

lemma bi_unique_rel_gpv [transfer_rule]:
  "\<lbrakk> bi_unique A; bi_unique B \<rbrakk> \<Longrightarrow> bi_unique (rel_gpv A B)"
unfolding bi_unique_alt_def by(simp add: left_unique_rel_gpv right_unique_rel_gpv)

lemma left_total_rel_gpv [transfer_rule]:
  "\<lbrakk> left_total A; left_total B \<rbrakk> \<Longrightarrow> left_total (rel_gpv A B)"
unfolding left_total_alt_def gpv.rel_conversep[symmetric] gpv.rel_compp[symmetric]
by(subst gpv.rel_eq[symmetric])(rule gpv.rel_mono)

lemma right_total_rel_gpv [transfer_rule]:
  "\<lbrakk> right_total A; right_total B \<rbrakk> \<Longrightarrow> right_total (rel_gpv A B)"
unfolding right_total_alt_def gpv.rel_conversep[symmetric] gpv.rel_compp[symmetric]
by(subst gpv.rel_eq[symmetric])(rule gpv.rel_mono)

lemma bi_total_rel_gpv [transfer_rule]: "\<lbrakk> bi_total A; bi_total B \<rbrakk> \<Longrightarrow> bi_total (rel_gpv A B)"
unfolding bi_total_alt_def by(simp add: left_total_rel_gpv right_total_rel_gpv)

declare gpv.map_transfer[transfer_rule]

lemma if_distrib_map_gpv [if_distribs]:
  "map_gpv f g (if b then gpv else gpv') = (if b then map_gpv f g gpv else map_gpv f g gpv')"
by simp

lemma gpv_pred_mono_strong:
  "\<lbrakk> pred_gpv P Q x; \<And>a. \<lbrakk> a \<in> results'_gpv x; P a \<rbrakk> \<Longrightarrow> P' a; \<And>b. \<lbrakk> b \<in> outs'_gpv x; Q b \<rbrakk> \<Longrightarrow> Q' b \<rbrakk> \<Longrightarrow> pred_gpv P' Q' x"
by(simp add: pred_gpv_def)

lemma pred_gpv_top [simp]:
  "pred_gpv (\<lambda>_. True) (\<lambda>_. True) = (\<lambda>_. True)"
by(simp add: pred_gpv_def)

lemma pred_gpv_conj [simp]:
  shows pred_gpv_conj1: "\<And>P Q R. pred_gpv (\<lambda>x. P x \<and> Q x) R = (\<lambda>x. pred_gpv P R x \<and> pred_gpv Q R x)"
  and pred_gpv_conj2: "\<And>P Q R. pred_gpv P (\<lambda>x. Q x \<and> R x) = (\<lambda>x. pred_gpv P Q x \<and> pred_gpv P R x)"
by(auto simp add: pred_gpv_def)

lemma rel_gpv_restrict_relp1I [intro?]:
  "\<lbrakk> rel_gpv R R' x y; pred_gpv P P' x; pred_gpv Q Q' y \<rbrakk> \<Longrightarrow> rel_gpv (R \<upharpoonleft> P \<otimes> Q) (R' \<upharpoonleft> P' \<otimes> Q') x y"
by(erule gpv.rel_mono_strong)(simp_all add: pred_gpv_def)

lemma rel_gpv_restrict_relpE [elim?]:
  assumes "rel_gpv (R \<upharpoonleft> P \<otimes> Q) (R' \<upharpoonleft> P' \<otimes> Q') x y"
  obtains "rel_gpv R R' x y" "pred_gpv P P' x" "pred_gpv Q Q' y"
proof
  show "rel_gpv R R' x y" using assms by(auto elim!: gpv.rel_mono_strong)
  have "pred_gpv (Domainp (R \<upharpoonleft> P \<otimes> Q)) (Domainp (R' \<upharpoonleft> P' \<otimes> Q')) x" using assms by(fold gpv.Domainp_rel) blast
  then show "pred_gpv P P' x" by(rule gpv_pred_mono_strong)(blast dest!: restrict_relp_DomainpD)+
  have "pred_gpv (Domainp (R \<upharpoonleft> P \<otimes> Q)\<inverse>\<inverse>) (Domainp (R' \<upharpoonleft> P' \<otimes> Q')\<inverse>\<inverse>) y" using assms
    by(fold gpv.Domainp_rel)(auto simp only: gpv.rel_conversep Domainp_conversep)
  then show "pred_gpv Q Q' y" by(rule gpv_pred_mono_strong)(auto dest!: restrict_relp_DomainpD)
qed

lemma gpv_pred_map [simp]: "pred_gpv P Q (map_gpv f g gpv) = pred_gpv (P \<circ> f) (Q \<circ> g) gpv"
by(simp add: pred_gpv_def)

subsection \<open>Generalised mapper and relator\<close>

context includes lifting_syntax begin

primcorec map_gpv' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('out \<Rightarrow> 'out') \<Rightarrow> ('ret' \<Rightarrow> 'ret) \<Rightarrow> ('a, 'out, 'ret) gpv \<Rightarrow> ('b, 'out', 'ret') gpv"
where
  "map_gpv' f g h gpv = 
   GPV (map_spmf (map_generat f g ((\<circ>) (map_gpv' f g h))) (map_spmf (map_generat id id (map_fun h id)) (the_gpv gpv)))"

declare map_gpv'.sel [simp del]

lemma map_gpv'_sel [simp]:
  "the_gpv (map_gpv' f g h gpv) = map_spmf (map_generat f g (h ---> map_gpv' f g h)) (the_gpv gpv)"
by(simp add: map_gpv'.sel spmf.map_comp o_def generat.map_comp map_fun_def[abs_def])

lemma map_gpv'_GPV [simp]:
  "map_gpv' f g h (GPV p) = GPV (map_spmf (map_generat f g (h ---> map_gpv' f g h)) p)"
by(rule gpv.expand) simp

lemma map_gpv'_id: "map_gpv' id id id = id"
apply(rule ext)
apply(coinduction)
apply(auto simp add: spmf_rel_map generat.rel_map rel_fun_def intro!: rel_spmf_reflI generat.rel_refl)
done

lemma map_gpv'_comp: "map_gpv' f g h (map_gpv' f' g' h' gpv) = map_gpv' (f \<circ> f') (g \<circ> g') (h' \<circ> h) gpv"
by(coinduction arbitrary: gpv)(auto simp add: spmf.map_comp spmf_rel_map generat.rel_map rel_fun_def intro!: rel_spmf_reflI generat.rel_refl)

functor gpv: map_gpv' by(simp_all add: map_gpv'_comp map_gpv'_id o_def) 

lemma map_gpv_conv_map_gpv': "map_gpv f g = map_gpv' f g id"
apply(rule ext)
apply(coinduction)
apply(auto simp add: gpv.map_sel spmf_rel_map generat.rel_map rel_fun_def intro!: generat.rel_refl_strong rel_spmf_reflI)
done

coinductive rel_gpv'' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('out \<Rightarrow> 'out' \<Rightarrow> bool) \<Rightarrow> ('ret \<Rightarrow> 'ret' \<Rightarrow> bool) \<Rightarrow> ('a, 'out, 'ret) gpv \<Rightarrow> ('b, 'out', 'ret') gpv \<Rightarrow> bool"
  for A C R
where
  "rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R)) (the_gpv gpv) (the_gpv gpv')
  \<Longrightarrow> rel_gpv'' A C R gpv gpv'"

lemma rel_gpv''_coinduct [consumes 1, case_names rel_gpv'', coinduct pred: rel_gpv'']:
  "\<lbrakk>X gpv gpv';
    \<And>gpv gpv'. X gpv gpv'
     \<Longrightarrow> rel_spmf (rel_generat A C (R ===> (\<lambda>gpv gpv'. X gpv gpv' \<or> rel_gpv'' A C R gpv gpv')))
           (the_gpv gpv) (the_gpv gpv') \<rbrakk>
   \<Longrightarrow> rel_gpv'' A C R gpv gpv'"
by(erule rel_gpv''.coinduct) blast

lemma rel_gpv''D:
  "rel_gpv'' A C R gpv gpv' 
  \<Longrightarrow> rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R)) (the_gpv gpv) (the_gpv gpv')"
by(simp add: rel_gpv''.simps)

lemma rel_gpv''_GPV [simp]:
  "rel_gpv'' A C R (GPV p) (GPV q) \<longleftrightarrow>
   rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R)) p q"
by(simp add: rel_gpv''.simps)

lemma rel_gpv_conv_rel_gpv'': "rel_gpv A C = rel_gpv'' A C (=)"
proof(rule ext iffI)+
  show "rel_gpv A C gpv gpv'" if "rel_gpv'' A C (=) gpv gpv'" for gpv :: "('a, 'b, 'c) gpv" and gpv' :: "('d, 'e, 'c) gpv"
    using that by(coinduct)(blast dest: rel_gpv''D)
  show "rel_gpv'' A C (=) gpv gpv'" if "rel_gpv A C gpv gpv'" for gpv :: "('a, 'b, 'c) gpv" and gpv' :: "('d, 'e, 'c) gpv"
    using that by(coinduct)(auto elim!: gpv.rel_cases rel_spmf_mono generat.rel_mono_strong rel_fun_mono)
qed

lemma rel_gpv''_eq (* [relator_eq] do not use this attribute unless all transfer rules for gpv have been changed to rel_gvp'' *):
  "rel_gpv'' (=) (=) (=) = (=)"
by(simp add: rel_gpv_conv_rel_gpv''[symmetric] gpv.rel_eq)

lemma rel_gpv''_mono:
  assumes "A \<le> A'" "C \<le> C'" "R' \<le> R"
  shows "rel_gpv'' A C R \<le> rel_gpv'' A' C' R'"
proof
  show "rel_gpv'' A' C' R' gpv gpv'" if "rel_gpv'' A C R gpv gpv'" for gpv gpv' using that
    by(coinduct)(auto dest: rel_gpv''D elim!: rel_spmf_mono generat.rel_mono_strong rel_fun_mono intro: assms[THEN predicate2D])
qed

lemma rel_gpv''_conversep: "rel_gpv'' A\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> = (rel_gpv'' A C R)\<inverse>\<inverse>"
proof(intro ext iffI; simp)
  show "rel_gpv'' A C R gpv gpv'" if "rel_gpv'' A\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> gpv' gpv"
    for A :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool" and C :: "'c1 \<Rightarrow> 'c2 \<Rightarrow> bool" and R :: "'r1 \<Rightarrow> 'r2 \<Rightarrow> bool" and gpv gpv'
    using that apply(coinduct)
    apply(drule rel_gpv''D)
    apply(rewrite in \<hole> conversep_iff[symmetric])
    apply(subst spmf_rel_conversep[symmetric])
    apply(erule rel_spmf_mono)
    apply(subst generat.rel_conversep[symmetric])
    apply(erule generat.rel_mono_strong)
    apply(auto simp add: rel_fun_def conversep_iff[abs_def])
    done
  from this[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" "R\<inverse>\<inverse>"]
  show "rel_gpv'' A\<inverse>\<inverse> C\<inverse>\<inverse> R\<inverse>\<inverse> gpv' gpv" if "rel_gpv'' A C R gpv gpv'" for gpv gpv' using that by simp
qed


lemma rel_gpv''_pos_distr:
  "rel_gpv'' A C R OO rel_gpv'' A' C' R' \<le> rel_gpv'' (A OO A') (C OO C') (R OO R')"
proof(rule predicate2I; erule relcomppE)
  show "rel_gpv'' (A OO A') (C OO C') (R OO R') gpv gpv''"
    if "rel_gpv'' A C R gpv gpv'" "rel_gpv'' A' C' R' gpv' gpv''"
    for gpv gpv' gpv'' using that
    apply(coinduction arbitrary: gpv gpv' gpv'')
    apply(drule rel_gpv''D)+
    apply(drule (1) rel_spmf_pos_distr[THEN predicate2D, OF relcomppI])
    apply(erule spmf_rel_mono_strong)
    apply(subst (asm) generat.rel_compp[symmetric])
    apply(erule generat.rel_mono_strong, assumption, assumption)
    apply(drule pos_fun_distr[THEN predicate2D])
    apply(auto simp add: rel_fun_def)
    done
qed

lemma left_unique_rel_gpv'':
  "\<lbrakk> left_unique A; left_unique C; left_total R \<rbrakk> \<Longrightarrow> left_unique (rel_gpv'' A C R)"
unfolding left_unique_alt_def left_total_alt_def rel_gpv''_conversep[symmetric]
apply(subst rel_gpv''_eq[symmetric])
apply(rule order_trans[OF rel_gpv''_pos_distr])
apply(erule (2) rel_gpv''_mono)
done

lemma right_unique_rel_gpv'':
  "\<lbrakk> right_unique A; right_unique C; right_total R \<rbrakk> \<Longrightarrow> right_unique (rel_gpv'' A C R)"
unfolding right_unique_alt_def right_total_alt_def rel_gpv''_conversep[symmetric]
apply(subst rel_gpv''_eq[symmetric])
apply(rule order_trans[OF rel_gpv''_pos_distr])
apply(erule (2) rel_gpv''_mono)
done

lemma bi_unique_rel_gpv'' [transfer_rule]:
  "\<lbrakk> bi_unique A; bi_unique C; bi_total R \<rbrakk> \<Longrightarrow> bi_unique (rel_gpv'' A C R)"
unfolding bi_unique_alt_def bi_total_alt_def by(blast intro: left_unique_rel_gpv'' right_unique_rel_gpv'')

lemma rel_gpv''_neg_distr:
  assumes R: "left_unique R" "right_total R"
  and R': "right_unique R'" "left_total R'"
  shows "rel_gpv'' (A OO A') (C OO C') (R OO R') \<le> rel_gpv'' A C R OO rel_gpv'' A' C' R'"
proof(rule predicate2I relcomppI)+
  fix gpv gpv''
  assume *: "rel_gpv'' (A OO A') (C OO C') (R OO R') gpv gpv''"
  let ?P_spmf = "\<lambda>gpv gpv'' pq. 
    (\<forall>(generat, generat'') \<in> set_spmf pq. rel_generat (A OO A') (C OO C') (R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) generat generat'') \<and>
    map_spmf fst pq = the_gpv gpv \<and>
    map_spmf snd pq = the_gpv gpv''"
  define pq where "pq gpv gpv'' = Eps (?P_spmf gpv gpv'')" for gpv gpv''
  let ?P_generat = "\<lambda>generat generat'' gg'. 
    (\<forall>(a, a'') \<in> generat_pures gg'. (A OO A') a a'') \<and> (\<forall>(out, out'') \<in> generat_outs gg'. (C OO C') out out'') \<and> (\<forall>(c, c'')\<in>generat_conts gg'. (R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) c c'') \<and>
    map_generat fst fst fst gg' = generat \<and> 
    map_generat snd snd snd gg' = generat''"
  define gg' where "gg' generat generat'' = Eps (?P_generat generat generat'')" for generat generat''
  define middle where "middle \<equiv> corec_gpv (\<lambda>(gpv, gpv''). 
     map_spmf (\<lambda>(generat, generat''). 
       map_generat (\<lambda>(a, a''). SOME a'. A a a' \<and> A' a' a'') (\<lambda>(out, out''). SOME out'. C out out' \<and> C' out' out'')
            (\<lambda>(rpv, rpv'') input. Inr (rpv (THE x. R x input), rpv'' (THE z. R' input z))) (gg' generat generat'')
     ) (pq gpv gpv''))"
  have sel_middle:
    "the_gpv (middle (gpv, gpv'')) = map_spmf (\<lambda>(generat, generat''). map_generat
           (\<lambda>(a, a''). SOME a'. A a a' \<and> A' a' a'')
           (\<lambda>(out, out''). SOME out'. C out out' \<and> C' out' out'')
           (\<lambda>(rpv, rpv'') xa. middle (rpv (THE x. R x xa), rpv'' (THE x''. R' xa x'')))
           (gg' generat generat''))
       (pq gpv gpv'')"
    for gpv gpv'' unfolding middle_def by(simp add: spmf.map_comp split_def o_def generat.map_comp)
  from * show "rel_gpv'' A C R gpv (middle (gpv, gpv''))"
  proof(coinduction arbitrary: gpv gpv'')
    case (rel_gpv'' gpv gpv'')
    let ?X = "\<lambda>gpv gpv'. (\<exists>gpv''. gpv' = middle (gpv, gpv'') \<and> rel_gpv'' (A OO A') (C OO C') (R OO R') gpv gpv'') \<or> rel_gpv'' A C R gpv gpv'"
    from rel_gpv''D[OF rel_gpv''] have "Ex (?P_spmf gpv gpv'')" by(auto simp add: rel_spmf_simps)
    hence pq: "?P_spmf gpv gpv'' (pq gpv gpv'')" unfolding pq_def by(rule someI_ex)
    hence "rel_spmf (\<lambda>generat (generat', generat''). generat = generat')\<inverse>\<inverse> (pq gpv gpv'') (the_gpv gpv)"
      by(fold spmf_rel_eq)(auto simp add: spmf_rel_map split_def elim: rel_spmf_mono)
    then show ?case
    proof(clarsimp simp add: sel_middle spmf_rel_conversep spmf_rel_map generat.rel_map prod.case_distrib[where h="A _"] prod.case_distrib[where h="C _"] prod.case_distrib[where h="rel_fun _ _ _"] elim!: rel_spmf_mono_strong)
      fix generat generat''
      assume "(generat, generat'') \<in> set_spmf (pq gpv gpv'')"
      with pq have "rel_generat (A OO A') (C OO C') (R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) generat generat''"
        by blast
      hence "Ex (?P_generat generat generat'')" by(auto simp add: Grp_def generat.rel_compp_Grp)
      hence gg': "?P_generat generat generat'' (gg' generat generat'')" unfolding gg'_def by(rule someI_ex)
      hence "rel_generat (\<lambda>a aa''. a = fst aa'')\<inverse>\<inverse> (\<lambda>out outout''. out = fst outout'')\<inverse>\<inverse> (\<lambda>rpv rpvrpv''. rpv = fst rpvrpv'')\<inverse>\<inverse> (gg' generat generat'') generat"
        by(fold generat.rel_eq)(auto simp add: generat.rel_map elim!: generat.rel_mono_strong)
      then show "rel_generat (\<lambda>a (aa, a''). A a (SOME a'. A aa a' \<and> A' a' a''))
                 (\<lambda>out (outt, out''). C out (SOME out'. C outt out' \<and> C' out' out''))
                 (\<lambda>rpv (rpvv, rpv''). (R ===> ?X) rpv (\<lambda>y. middle (rpvv (THE x. R x y), rpv'' (THE z. R' y z))))
                 generat (gg' generat generat'')"
        unfolding generat.rel_conversep conversep_iff apply(rule generat.rel_mono_strong)
      proof(safe, simp_all)
        fix a a''
        assume "(a, a'') \<in> generat_pures (gg' generat generat'')"
        with gg' have "\<exists>a'. A a a' \<and> A' a' a''" by blast
        from someI_ex[OF this] show "A a (SOME a'. A a a' \<and> A' a' a'')" ..
      next
        fix out out''
        assume "(out, out'') \<in> generat_outs (gg' generat generat'')"
        with gg' have "\<exists>out'. C out out' \<and> C' out' out''" by blast
        from someI_ex[OF this] show "C out (SOME out'. C out out' \<and> C' out' out'')" ..
      next
        fix rpv rpv''
        assume "(rpv, rpv'') \<in> generat_conts (gg' generat generat'')"
        with gg' have *: "(R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) rpv rpv''" by blast
        show "(R ===> ?X) rpv (\<lambda>y. middle (rpv (THE x. R x y), rpv'' (THE z. R' y z)))"
        proof(rule rel_funI)
          fix x y
          assume xy: "R x y"
          from R' obtain z where yz: "R' y z" by(blast elim: left_totalE)
          with xy have "(R OO R') x z" by blast
          with * have "rel_gpv'' (A OO A') (C OO C') (R OO R') (rpv x) (rpv'' z)" by(rule rel_funD)
          moreover have "(THE x. R x y) = x" using xy
            by(rule the_equality)(blast dest: left_uniqueD[OF R(1) xy])
          moreover have "(THE z. R' y z) = z" using yz
            by(rule the_equality)(blast dest: right_uniqueD[OF R'(1) yz])
          ultimately show "?X (rpv x) (middle (rpv (THE x. R x y), rpv'' (THE z. R' y z)))" by blast
        qed
      qed
    qed
  qed
  from * show "rel_gpv'' A' C' R' (middle (gpv, gpv'')) gpv''"
  proof(coinduction arbitrary: gpv gpv'')
    case (rel_gpv'' gpv gpv'')
    let ?X = "\<lambda>gpv' gpv''. (\<exists>gpv. gpv' = middle (gpv, gpv'') \<and> rel_gpv'' (A OO A') (C OO C') (R OO R') gpv gpv'') \<or> rel_gpv'' A' C' R' gpv' gpv''"
    from rel_gpv''D[OF rel_gpv''] have "Ex (?P_spmf gpv gpv'')" by(auto simp add: rel_spmf_simps)
    hence pq: "?P_spmf gpv gpv'' (pq gpv gpv'')" unfolding pq_def by(rule someI_ex)
    hence "rel_spmf (\<lambda>(generat', generat'') generat. generat = generat'') (pq gpv gpv'') (the_gpv gpv'')"
      by(fold spmf_rel_eq)(auto simp add: spmf_rel_map split_def elim: rel_spmf_mono)
    then show ?case
    proof(clarsimp simp add: sel_middle spmf_rel_conversep spmf_rel_map generat.rel_map prod.case_distrib[where h="A'"] prod.case_distrib[where h="C'"] prod.case_distrib[where h="rel_fun _ _"] elim!: rel_spmf_mono_strong)
      fix generat generat''
      assume "(generat, generat'') \<in> set_spmf (pq gpv gpv'')"
      with pq have "rel_generat (A OO A') (C OO C') (R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) generat generat''"
        by blast
      hence "Ex (?P_generat generat generat'')" by(auto simp add: Grp_def generat.rel_compp_Grp)
      hence gg': "?P_generat generat generat'' (gg' generat generat'')" unfolding gg'_def by(rule someI_ex)
      hence "rel_generat (\<lambda>aa'' a. a = snd aa'') (\<lambda>outout'' out. out = snd outout'') (\<lambda>rpvrpv'' rpv. rpv = snd rpvrpv'') (gg' generat generat'') generat''"
        by(fold generat.rel_eq)(auto simp add: generat.rel_map elim!: generat.rel_mono_strong)
      then show "rel_generat (\<lambda>(a, aa'') a''. A' (SOME a'. A a a' \<and> A' a' aa'') a'')
                 (\<lambda>(out, outt'') out''. C' (SOME out'. C out out' \<and> C' out' outt'') out'')
                 (\<lambda>(rpv, rpvv'') rpv''. (R' ===> ?X) (\<lambda>y. middle (rpv (THE x. R x y), rpvv'' (THE z. R' y z))) rpv'')
                 (gg' generat generat'') generat''"
        apply(rule generat.rel_mono_strong)
      proof(safe, simp_all)
        fix a a''
        assume "(a, a'') \<in> generat_pures (gg' generat generat'')"
        with gg' have "\<exists>a'. A a a' \<and> A' a' a''" by blast
        from someI_ex[OF this] show "A' (SOME a'. A a a' \<and> A' a' a'') a''" ..
      next
        fix out out''
        assume "(out, out'') \<in> generat_outs (gg' generat generat'')"
        with gg' have "\<exists>out'. C out out' \<and> C' out' out''" by blast
        from someI_ex[OF this] show "C' (SOME out'. C out out' \<and> C' out' out'') out''" ..
      next
        fix rpv rpv''
        assume "(rpv, rpv'') \<in> generat_conts (gg' generat generat'')"
        with gg' have *: "(R OO R' ===> rel_gpv'' (A OO A') (C OO C') (R OO R')) rpv rpv''" by blast
        show "(R' ===> ?X) (\<lambda>y. middle (rpv (THE x. R x y), rpv'' (THE z. R' y z))) rpv''"
        proof(rule rel_funI)
          fix y z
          assume yz: "R' y z"
          from R obtain x where xy: "R x y" by(blast elim: right_totalE)
          with yz have "(R OO R') x z" by blast
          with * have "rel_gpv'' (A OO A') (C OO C') (R OO R') (rpv x) (rpv'' z)" by(rule rel_funD)
          moreover have "(THE x. R x y) = x" using xy
            by(rule the_equality)(blast dest: left_uniqueD[OF R(1) xy])
          moreover have "(THE z. R' y z) = z" using yz
            by(rule the_equality)(blast dest: right_uniqueD[OF R'(1) yz])
          ultimately show "?X (middle (rpv (THE x. R x y), rpv'' (THE z. R' y z))) (rpv'' z)" by blast
        qed
      qed
    qed
  qed
qed

lemma left_total_rel_gpv':
  "\<lbrakk> left_total A; left_total C; left_unique R; right_total R \<rbrakk> \<Longrightarrow> left_total (rel_gpv'' A C R)"
unfolding left_unique_alt_def left_total_alt_def rel_gpv''_conversep[symmetric]
apply(subst rel_gpv''_eq[symmetric])
apply(rule order_trans[rotated])
apply(rule rel_gpv''_neg_distr; simp add: left_unique_alt_def)
apply(rule rel_gpv''_mono; assumption)
done

lemma right_total_rel_gpv':
  "\<lbrakk> right_total A; right_total C; right_unique R; left_total R \<rbrakk> \<Longrightarrow> right_total (rel_gpv'' A C R)"
unfolding right_unique_alt_def right_total_alt_def rel_gpv''_conversep[symmetric]
apply(subst rel_gpv''_eq[symmetric])
apply(rule order_trans[rotated])
apply(rule rel_gpv''_neg_distr; simp add: right_unique_alt_def)
apply(rule rel_gpv''_mono; assumption)
done

lemma bi_total_rel_gpv' [transfer_rule]:
  "\<lbrakk> bi_total A; bi_total C; bi_unique R; bi_total R \<rbrakk> \<Longrightarrow> bi_total (rel_gpv'' A C R)"
unfolding bi_total_alt_def bi_unique_alt_def by(blast intro: left_total_rel_gpv' right_total_rel_gpv')

lemma rel_fun_conversep_grp_grp:
  "rel_fun (conversep (BNF_Def.Grp UNIV f)) (BNF_Def.Grp B g) = BNF_Def.Grp {x. (x \<circ> f) ` UNIV \<subseteq> B} (map_fun f g)"
unfolding rel_fun_def Grp_def simp_thms fun_eq_iff conversep_iff by auto

lemma Quotient_gpv:
  assumes Q1: "Quotient R1 Abs1 Rep1 T1"
  and Q2: "Quotient R2 Abs2 Rep2 T2"
  and Q3: "Quotient R3 Abs3 Rep3 T3"
  shows "Quotient (rel_gpv'' R1 R2 R3) (map_gpv' Abs1 Abs2 Rep3) (map_gpv' Rep1 Rep2 Abs3) (rel_gpv'' T1 T2 T3)"
  (is "Quotient ?R ?abs ?rep ?T")
unfolding Quotient_alt_def2
proof(intro conjI strip iffI; (elim conjE exE)?)
  note [simp] = spmf_rel_map generat.rel_map
    and [elim!] = rel_spmf_mono generat.rel_mono_strong
    and [rule del] = rel_funI and [intro!] = rel_funI
  have Abs1 [simp]: "Abs1 x = y" if "T1 x y" for x y using Q1 that by(simp add: Quotient_alt_def)
  have Abs2 [simp]: "Abs2 x = y" if "T2 x y" for x y using Q2 that by(simp add: Quotient_alt_def)
  have Abs3 [simp]: "Abs3 x = y" if "T3 x y" for x y using Q3 that by(simp add: Quotient_alt_def)
  have Rep1: "T1 (Rep1 x) x" for x using Q1 by(simp add: Quotient_alt_def)
  have Rep2: "T2 (Rep2 x) x" for x using Q2 by(simp add: Quotient_alt_def)
  have Rep3: "T3 (Rep3 x) x" for x using Q3 by(simp add: Quotient_alt_def)
  have T1: "T1 x (Abs1 y)" if "R1 x y" for x y using Q1 that by(simp add: Quotient_alt_def2)
  have T2: "T2 x (Abs2 y)" if "R2 x y" for x y using Q2 that by(simp add: Quotient_alt_def2)
  have T1': "T1 x (Abs1 y)" if "R1 y x" for x y using Q1 that by(simp add: Quotient_alt_def2)
  have T2': "T2 x (Abs2 y)" if "R2 y x" for x y using Q2 that by(simp add: Quotient_alt_def2)
  have R3: "R3 x (Rep3 y)" if "T3 x y" for x y using Q3 that by(simp add: Quotient_alt_def2 Abs3[OF Rep3])
  have R3': "R3 (Rep3 y) x" if "T3 x y" for x y using Q3 that by(simp add: Quotient_alt_def2 Abs3[OF Rep3])
  have r1: "R1 = T1 OO T1\<inverse>\<inverse>" using Q1 by(simp add: Quotient_alt_def4)
  have r2: "R2 = T2 OO T2\<inverse>\<inverse>" using Q2 by(simp add: Quotient_alt_def4)
  have r3: "R3 = T3 OO T3\<inverse>\<inverse>" using Q3 by(simp add: Quotient_alt_def4)
  show abs: "?abs gpv = gpv'" if "?T gpv gpv'" for gpv gpv' using that
    by(coinduction arbitrary: gpv gpv')(drule rel_gpv''D; auto 4 4 intro: Rep3 dest: rel_funD)
  show "?T (?rep gpv) gpv" for gpv
    by(coinduction arbitrary: gpv)(auto simp add: Rep1 Rep2 intro!: rel_spmf_reflI generat.rel_refl_strong)
  show "?T gpv (?abs gpv')" if "?R gpv gpv'" for gpv gpv' using that
    by(coinduction arbitrary: gpv gpv')(drule rel_gpv''D; auto 4 3 simp add: T1 T2 intro!: R3 dest: rel_funD)
  show "?T gpv (?abs gpv')" if "?R gpv' gpv" for gpv gpv'
  proof -
    from that have "rel_gpv'' R1\<inverse>\<inverse> R2\<inverse>\<inverse> R3\<inverse>\<inverse> gpv gpv'" unfolding rel_gpv''_conversep by simp
    then show ?thesis
      by(coinduction arbitrary: gpv gpv')(drule rel_gpv''D; auto 4 3 simp add: T1' T2' intro!: R3' dest: rel_funD)
  qed
  show "?R gpv gpv'" if "?T gpv (?abs gpv')" "?T gpv' (?abs gpv)" for gpv gpv'
  proof -
    from that[THEN abs] have "?abs gpv' = ?abs gpv" by simp
    with that have "(?T OO ?T\<inverse>\<inverse>) gpv gpv'" by auto
    hence "rel_gpv'' (T1 OO T1\<inverse>\<inverse>) (T2 OO T2\<inverse>\<inverse>) (T3 OO T3\<inverse>\<inverse>) gpv gpv'"
      unfolding rel_gpv''_conversep[symmetric]
      by(rule rel_gpv''_pos_distr[THEN predicate2D])
    thus ?thesis by(simp add: r1 r2 r3)
  qed
qed

lemma rel_gpv''_Grp: (* does not hold! *)
  "rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse> = 
   BNF_Def.Grp {x. results'_gpv x \<subseteq> A \<and> outs'_gpv x \<subseteq> B} (map_gpv' f g h)"
   (is "?lhs = ?rhs")
proof(intro ext GrpI iffI CollectI conjI subsetI)
  fix gpv gpv'
  assume *: "?lhs gpv gpv'"
  then show "map_gpv' f g h gpv = gpv'"
    apply(coinduction arbitrary: gpv gpv')
    apply(drule rel_gpv''D)
    apply(auto 4 5 simp add: spmf_rel_map generat.rel_map elim!: rel_spmf_mono generat.rel_mono_strong GrpE intro!: GrpI dest: rel_funD)
    done
  show "x \<in> A" if "x \<in> results'_gpv gpv" for x using that *
  proof(induction arbitrary: gpv')
    case (Pure generat gpv)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using Pure.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with Pure.hyps show ?case by(simp add: generat.Domainp_rel pred_spmf_def pred_generat_def Domainp_Grp)
  next
    case (Cont generat gpv c input)
    have "pred_spmf (Domainp (rel_generat (BNF_Def.Grp A f) (BNF_Def.Grp B g) ((BNF_Def.Grp UNIV h)\<inverse>\<inverse> ===> rel_gpv'' (BNF_Def.Grp A f) (BNF_Def.Grp B g) (BNF_Def.Grp UNIV h)\<inverse>\<inverse>))) (the_gpv gpv)"
      using Cont.prems[THEN rel_gpv''D] unfolding spmf_Domainp_rel[symmetric] by(rule DomainPI)
    with Cont.hyps show ?case apply(clarsimp simp add: generat.Domainp_rel pred_spmf_def pred_generat_def)
      apply(drule (1) bspec)+
      apply clarsimp
      apply(drule rel_funD)
      prefer 2
      apply(erule Cont.IH)
      apply(simp add: Grp_def)
      oops


lemma the_gpv_parametric':
  "(rel_gpv'' A C R ===> rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R))) the_gpv the_gpv"
by(rule rel_funI)(auto elim: rel_gpv''.cases)

lemma GPV_parametric':
  "(rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R)) ===> rel_gpv'' A C R) GPV GPV"
by(rule rel_funI)(auto)

lemma corec_gpv_parametric':
  "((S ===> rel_spmf (rel_generat A C (R ===> rel_sum (rel_gpv'' A C R) S))) ===> S ===> rel_gpv'' A C R)
  corec_gpv corec_gpv"
proof(rule rel_funI)+
  fix f g s1 s2
  assume fg: "(S ===> rel_spmf (rel_generat A C (R ===> rel_sum (rel_gpv'' A C R) S))) f g"
    and s: "S s1 s2"
  from s show "rel_gpv'' A C R (corec_gpv f s1) (corec_gpv g s2)"
    apply(coinduction arbitrary: s1 s2)
    apply(drule fg[THEN rel_funD])
    apply(simp add: spmf_rel_map)
    apply(erule rel_spmf_mono)
    apply(simp add: generat.rel_map)
    apply(erule generat.rel_mono_strong; clarsimp simp add: o_def)
    apply(rule rel_funI)
    apply(drule (1) rel_funD)
    apply(auto 4 3 elim!: rel_sum.cases)
    done
qed

lemma map_gpv'_parametric [transfer_rule]:
  "((A ===> A') ===> (C ===> C') ===> (R' ===> R) ===> rel_gpv'' A C R ===> rel_gpv'' A' C' R') map_gpv' map_gpv'"
  unfolding map_gpv'_def
  supply corec_gpv_parametric'[transfer_rule] the_gpv_parametric'[transfer_rule]
  by(transfer_prover)

lemma map_gpv_parametric': "((A ===> A') ===> (C ===> C') ===> rel_gpv'' A C R ===> rel_gpv'' A' C' R) map_gpv map_gpv"
  unfolding map_gpv_conv_map_gpv'[abs_def] by transfer_prover

end

subsection \<open>Simple, derived operations\<close>

primcorec Done :: "'a \<Rightarrow> ('a, 'out, 'in) gpv"
where "the_gpv (Done a) = return_spmf (Pure a)"

primcorec Pause :: "'out \<Rightarrow> ('in \<Rightarrow> ('a, 'out, 'in) gpv) \<Rightarrow> ('a, 'out, 'in) gpv"
where "the_gpv (Pause out c) = return_spmf (IO out c)"

primcorec lift_spmf :: "'a spmf \<Rightarrow> ('a, 'out, 'in) gpv"
where "the_gpv (lift_spmf p) = map_spmf Pure p"

definition Fail :: "('a, 'out, 'in) gpv"
where "Fail = GPV (return_pmf None)"

definition React :: "('in \<Rightarrow> 'out \<times> ('a, 'out, 'in) rpv) \<Rightarrow> ('a, 'out, 'in) rpv"
where "React f input = case_prod Pause (f input)"

definition rFail :: "('a, 'out, 'in) rpv"
where "rFail = (\<lambda>_. Fail)"

lemma Done_inject [simp]: "Done x = Done y \<longleftrightarrow> x = y"
by(simp add: Done.ctr)

lemma Pause_inject [simp]: "Pause out c = Pause out' c' \<longleftrightarrow> out = out' \<and> c = c'"
by(simp add: Pause.ctr)

lemma [simp]:
  shows Done_neq_Pause: "Done x \<noteq> Pause out c"
  and Pause_neq_Done: "Pause out c \<noteq> Done x"
by(simp_all add: Done.ctr Pause.ctr)

lemma outs'_gpv_Done [simp]: "outs'_gpv (Done x) = {}"
by(auto elim: outs'_gpv_cases)

lemma results'_gpv_Done [simp]: "results'_gpv (Done x) = {x}"
by(auto intro: results'_gpvI elim: results'_gpv_cases)

lemma pred_gpv_Done [simp]: "pred_gpv P Q (Done x) = P x"
by(simp add: pred_gpv_def)

lemma outs'_gpv_Pause [simp]: "outs'_gpv (Pause out c) = insert out (\<Union>input. outs'_gpv (c input))"
by(auto 4 4 intro: outs'_gpvI elim: outs'_gpv_cases)

lemma results'_gpv_Pause [simp]: "results'_gpv (Pause out rpv) = results'_rpv rpv"
by(auto 4 4 intro: results'_gpvI elim: results'_gpv_cases)

lemma pred_gpv_Pause [simp]: "pred_gpv P Q (Pause x c) = (Q x \<and> All (pred_gpv P Q \<circ> c))"
by(auto simp add: pred_gpv_def o_def)

lemma lift_spmf_return [simp]: "lift_spmf (return_spmf x) = Done x"
by(simp add: lift_spmf.ctr Done.ctr)

lemma lift_spmf_None [simp]: "lift_spmf (return_pmf None) = Fail"
by(rule gpv.expand)(simp add: Fail_def)

lemma the_gpv_lift_spmf [simp]: "the_gpv (lift_spmf r) = map_spmf Pure r"
by(simp)

lemma outs'_gpv_lift_spmf [simp]: "outs'_gpv (lift_spmf p) = {}"
by(auto 4 3 elim: outs'_gpv_cases)

lemma results'_gpv_lift_spmf [simp]: "results'_gpv (lift_spmf p) = set_spmf p"
by(auto 4 3 elim: results'_gpv_cases intro: results'_gpvI)

lemma pred_gpv_lift_spmf [simp]: "pred_gpv P Q (lift_spmf p) = pred_spmf P p"
by(simp add: pred_gpv_def pred_spmf_def)

lemma lift_spmf_inject [simp]: "lift_spmf p = lift_spmf q \<longleftrightarrow> p = q"
by(auto simp add: lift_spmf.code dest!: pmf.inj_map_strong[rotated] option.inj_map_strong[rotated])

lemma map_lift_spmf: "map_gpv f g (lift_spmf p) = lift_spmf (map_spmf f p)"
by(rule gpv.expand)(simp add: gpv.map_sel spmf.map_comp o_def)

lemma lift_map_spmf: "lift_spmf (map_spmf f p) = map_gpv f id (lift_spmf p)"
by(rule gpv.expand)(simp add: gpv.map_sel spmf.map_comp o_def)

lemma [simp]:
  shows Fail_neq_Pause: "Fail \<noteq> Pause out c"
  and Pause_neq_Fail: "Pause out c \<noteq> Fail"
  and Fail_neq_Done: "Fail \<noteq> Done x"
  and Done_neq_Fail: "Done x \<noteq> Fail"
by(simp_all add: Fail_def Pause.ctr Done.ctr)

text \<open>Add @{typ unit} closure to circumvent SML value restriction\<close>

definition Fail' :: "unit \<Rightarrow> ('a, 'out, 'in) gpv"
where [code del]: "Fail' _ = Fail"

lemma Fail_code [code_unfold]: "Fail = Fail' ()"
by(simp add: Fail'_def)

lemma Fail'_code [code]:
  "Fail' x = GPV (return_pmf None)"
by(simp add: Fail'_def Fail_def)

lemma Fail_sel [simp]:
  "the_gpv Fail = return_pmf None"
by(simp add: Fail_def)

lemma Fail_eq_GPV_iff [simp]: "Fail = GPV f \<longleftrightarrow> f = return_pmf None"
by(auto simp add: Fail_def)

lemma outs'_gpv_Fail [simp]: "outs'_gpv Fail = {}"
by(auto elim: outs'_gpv_cases)

lemma results'_gpv_Fail [simp]: "results'_gpv Fail = {}"
by(auto elim: results'_gpv_cases)

lemma pred_gpv_Fail [simp]: "pred_gpv P Q Fail"
by(simp add: pred_gpv_def)

lemma React_inject [iff]: "React f = React f' \<longleftrightarrow> f = f'"
by(auto simp add: React_def fun_eq_iff split_def intro: prod.expand)

lemma React_apply [simp]: "f input = (out, c) \<Longrightarrow> React f input = Pause out c"
by(simp add: React_def)

lemma rFail_apply [simp]: "rFail input = Fail"
by(simp add: rFail_def)

lemma [simp]:
  shows rFail_neq_React: "rFail \<noteq> React f"
  and React_neq_rFail: "React f \<noteq> rFail"
by(simp_all add: React_def fun_eq_iff split_beta)

lemma rel_gpv_FailI [simp]: "rel_gpv A C Fail Fail"
by(subst gpv.rel_sel) simp

lemma rel_gpv_Done [iff]: "rel_gpv A C (Done x) (Done y) \<longleftrightarrow> A x y"
by(subst gpv.rel_sel) simp

lemma rel_gpv''_Done [iff]: "rel_gpv'' A C R (Done x) (Done y) \<longleftrightarrow> A x y"
by(subst rel_gpv''.simps) simp

lemma rel_gpv_Pause [iff]:
  "rel_gpv A C (Pause out c) (Pause out' c') \<longleftrightarrow> C out out' \<and> (\<forall>x. rel_gpv A C (c x) (c' x))"
by(subst gpv.rel_sel)(simp add: rel_fun_def)

lemma rel_gpv''_Pause [iff]:
  "rel_gpv'' A C R (Pause out c) (Pause out' c') \<longleftrightarrow> C out out' \<and> (\<forall>x x'. R x x' \<longrightarrow> rel_gpv'' A C R (c x) (c' x'))"
by(subst rel_gpv''.simps)(simp add: rel_fun_def)

lemma rel_gpv_lift_spmf [iff]: "rel_gpv A C (lift_spmf p) (lift_spmf q) \<longleftrightarrow> rel_spmf A p q"
by(subst gpv.rel_sel)(simp add: spmf_rel_map)

lemma rel_gpv''_lift_spmf [iff]:
  "rel_gpv'' A C R (lift_spmf p) (lift_spmf q) \<longleftrightarrow> rel_spmf A p q"
by(subst rel_gpv''.simps)(simp add: spmf_rel_map)

context includes lifting_syntax begin
lemmas Fail_parametric [transfer_rule] = rel_gpv_FailI

lemma Fail_parametric' [simp]: "rel_gpv'' A C R Fail Fail"
unfolding Fail_def by simp

lemma Done_parametric [transfer_rule]: "(A ===> rel_gpv A C) Done Done"
by(rule rel_funI) simp

lemma Done_parametric': "(A ===> rel_gpv'' A C R) Done Done"
by(rule rel_funI) simp

lemma Pause_parametric [transfer_rule]:
  "(C ===> ((=) ===> rel_gpv A C) ===> rel_gpv A C) Pause Pause"
by(simp add: rel_fun_def)

lemma Pause_parametric':
  "(C ===> (R ===> rel_gpv'' A C R) ===> rel_gpv'' A C R) Pause Pause"
by(simp add: rel_fun_def)

lemma lift_spmf_parametric [transfer_rule]:
  "(rel_spmf A ===> rel_gpv A C) lift_spmf lift_spmf"
by(simp add: rel_fun_def)

lemma lift_spmf_parametric':
  "(rel_spmf A ===> rel_gpv'' A C R) lift_spmf lift_spmf"
by(simp add: rel_fun_def)
end

lemma map_gpv_Done [simp]: "map_gpv f g (Done x) = Done (f x)"
by(simp add: Done.code)

lemma map_gpv'_Done [simp]: "map_gpv' f g h (Done x) = Done (f x)"
by(simp add: Done.code)

lemma map_gpv_Pause [simp]: "map_gpv f g (Pause x c) = Pause (g x) (map_gpv f g \<circ> c)"
by(simp add: Pause.code)

lemma map_gpv'_Pause [simp]: "map_gpv' f g h (Pause x c) = Pause (g x) (map_gpv' f g h \<circ> c \<circ> h)"
by(simp add: Pause.code map_fun_def)

lemma map_gpv_Fail [simp]: "map_gpv f g Fail = Fail"
by(simp add: Fail_def)

lemma map_gpv'_Fail [simp]: "map_gpv' f g h Fail = Fail"
by(simp add: Fail_def)

subsection \<open>Monad structure\<close>

primcorec bind_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a \<Rightarrow> ('b, 'out, 'in) gpv) \<Rightarrow> ('b, 'out, 'in) gpv"
where
  "the_gpv (bind_gpv r f) =
   map_spmf (map_generat id id ((\<circ>) (case_sum id (\<lambda>r. bind_gpv r f))))
     (the_gpv r \<bind>
      (case_generat
        (\<lambda>x. map_spmf (map_generat id id ((\<circ>) Inl)) (the_gpv (f x)))
        (\<lambda>out c. return_spmf (IO out (\<lambda>input. Inr (c input))))))"

declare bind_gpv.sel [simp del]

adhoc_overloading Monad_Syntax.bind bind_gpv

lemma bind_gpv_unfold [code]:
  "r \<bind> f = GPV (
   do {
     generat \<leftarrow> the_gpv r;
     case generat of Pure x \<Rightarrow> the_gpv (f x)
       | IO out c \<Rightarrow> return_spmf (IO out (\<lambda>input. c input \<bind> f))
   })"
unfolding bind_gpv_def
apply(rule gpv.expand)
apply(simp add: map_spmf_bind_spmf)
apply(rule arg_cong[where f="bind_spmf (the_gpv r)"])
apply(auto split: generat.split simp add: map_spmf_bind_spmf fun_eq_iff spmf.map_comp o_def generat.map_comp id_def[symmetric] generat.map_id pmf.map_id option.map_id)
done

lemma bind_gpv_code_cong: "f = f' \<Longrightarrow> bind_gpv f g = bind_gpv f' g" by simp
setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm bind_gpv_code_cong})\<close>

lemma bind_gpv_sel:
  "the_gpv (r \<bind> f) =
   do {
     generat \<leftarrow> the_gpv r;
     case generat of Pure x \<Rightarrow> the_gpv (f x)
       | IO out c \<Rightarrow> return_spmf (IO out (\<lambda>input. bind_gpv (c input) f))
   }"
by(subst bind_gpv_unfold) simp

lemma bind_gpv_sel' [simp]:
  "the_gpv (r \<bind> f) =
   do {
     generat \<leftarrow> the_gpv r;
     if is_Pure generat then the_gpv (f (result generat))
     else return_spmf (IO (output generat) (\<lambda>input. bind_gpv (continuation generat input) f))
   }"
unfolding bind_gpv_sel
by(rule arg_cong[where f="bind_spmf (the_gpv r)"])(simp add: fun_eq_iff split: generat.split)

lemma Done_bind_gpv [simp]: "Done a \<bind> f = f a"
by(rule gpv.expand)(simp)

lemma bind_gpv_Done [simp]: "f \<bind> Done = f"
proof(coinduction arbitrary: f rule: gpv.coinduct)
  case (Eq_gpv f)
  have *: "the_gpv f \<bind> (case_generat (\<lambda>x. return_spmf (Pure x)) (\<lambda>out c. return_spmf (IO out (\<lambda>input. Inr (c input))))) =
           map_spmf (map_generat id id ((\<circ>) Inr)) (bind_spmf (the_gpv f) return_spmf)"
    unfolding map_spmf_bind_spmf
    by(rule arg_cong2[where f=bind_spmf])(auto simp add: fun_eq_iff split: generat.split)
  show ?case
    by(auto simp add: * bind_gpv.simps pmf.rel_map option.rel_map[abs_def] generat.rel_map[abs_def] simp del: bind_gpv_sel' intro!: rel_generatI rel_spmf_reflI)
qed

lemma if_distrib_bind_gpv2 [if_distribs]:
  "bind_gpv gpv (\<lambda>y. if b then f y else g y) = (if b then bind_gpv gpv f else bind_gpv gpv g)"
by simp

lemma lift_spmf_bind: "lift_spmf r \<bind> f = GPV (r \<bind> the_gpv \<circ> f)"
by(coinduction arbitrary: r f rule: gpv.coinduct_strong)(auto simp add: bind_map_spmf o_def intro: rel_pmf_reflI rel_optionI rel_generatI)

lemma the_gpv_bind_gpv_lift_spmf [simp]:
  "the_gpv (bind_gpv (lift_spmf p) f) = bind_spmf p (the_gpv \<circ> f)"
by(simp add: bind_map_spmf o_def)

lemma lift_spmf_bind_spmf: "lift_spmf (p \<bind> f) = lift_spmf p \<bind> (\<lambda>x. lift_spmf (f x))"
by(rule gpv.expand)(simp add: lift_spmf_bind o_def map_spmf_bind_spmf)

lemma lift_bind_spmf: "lift_spmf (bind_spmf p f) = bind_gpv (lift_spmf p) (lift_spmf \<circ> f)"
by(rule gpv.expand)(simp add: bind_map_spmf map_spmf_bind_spmf o_def)

lemma GPV_bind:
  "GPV f \<bind> g = 
   GPV (f \<bind> (\<lambda>generat. case generat of Pure x \<Rightarrow> the_gpv (g x) | IO out c \<Rightarrow> return_spmf (IO out (\<lambda>input. c input \<bind> g))))"
by(subst bind_gpv_unfold) simp

lemma GPV_bind':
  "GPV f \<bind> g = GPV (f \<bind> (\<lambda>generat. if is_Pure generat then the_gpv (g (result generat)) else return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> g))))"
unfolding GPV_bind gpv.inject
by(rule arg_cong[where f="bind_spmf f"])(simp add: fun_eq_iff split: generat.split)

lemma bind_gpv_assoc:
  fixes f :: "('a, 'out, 'in) gpv"
  shows "(f \<bind> g) \<bind> h = f \<bind> (\<lambda>x. g x \<bind> h)"
proof(coinduction arbitrary: f g h rule: gpv.coinduct_strong)
  case (Eq_gpv f g h)
  show ?case
    apply(simp cong del: if_weak_cong)
    apply(rule rel_spmf_bindI[where R="(=)"])
     apply(simp add: option.rel_eq pmf.rel_eq)
    apply(fastforce intro: rel_pmf_return_pmfI rel_generatI rel_spmf_reflI)
    done
qed

lemma map_gpv_bind_gpv: "map_gpv f g (bind_gpv gpv h) = bind_gpv (map_gpv id g gpv) (\<lambda>x. map_gpv f g (h x))"
apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
apply(simp add: bind_gpv.sel gpv.map_sel spmf_rel_map generat.rel_map o_def bind_map_spmf del: bind_gpv_sel')
apply(rule rel_spmf_bind_reflI)
apply(auto simp add: spmf_rel_map generat.rel_map split: generat.split del: rel_funI intro!: rel_spmf_reflI generat.rel_refl rel_funI)
done

lemma map_gpv_id_bind_gpv: "map_gpv f id (bind_gpv gpv g) = bind_gpv gpv (map_gpv f id \<circ> g)"
by(simp add: map_gpv_bind_gpv gpv.map_id o_def)

lemma map_gpv_conv_bind:
  "map_gpv f (\<lambda>x. x) x = bind_gpv x (\<lambda>x. Done (f x))"
using map_gpv_bind_gpv[of f "\<lambda>x. x" x Done] by(simp add: id_def[symmetric] gpv.map_id)

lemma bind_map_gpv: "bind_gpv (map_gpv f id gpv) g = bind_gpv gpv (g \<circ> f)"
by(simp add: map_gpv_conv_bind id_def bind_gpv_assoc o_def)

lemma outs_bind_gpv:
  "outs'_gpv (bind_gpv x f) = outs'_gpv x \<union> (\<Union>x \<in> results'_gpv x. outs'_gpv (f x))"
  (is "?lhs = ?rhs")
proof(rule Set.set_eqI iffI)+
  fix out
  assume "out \<in> ?lhs"
  then show "out \<in> ?rhs"
  proof(induction g\<equiv>"x \<bind> f" arbitrary: x)
    case (Out generat)
    then obtain generat' where *: "generat' \<in> set_spmf (the_gpv x)"
      and **: "generat \<in> set_spmf (if is_Pure generat' then the_gpv (f (result generat'))
                                else return_spmf (IO (output generat') (\<lambda>input. continuation generat' input \<bind> f)))"
      by(auto)
    show ?case
    proof(cases "is_Pure generat'")
      case True
      then have "out \<in> outs'_gpv (f (result generat'))" using Out(2) ** by(auto intro: outs'_gpvI)
      moreover have "result generat' \<in> results'_gpv x" using * True
        by(auto intro: results'_gpvI generat.set_sel)
      ultimately show ?thesis by blast
    next
      case False
      hence "out \<in> outs'_gpv x" using * ** Out(2) by(auto intro: outs'_gpvI generat.set_sel)
      thus ?thesis by blast
    qed
  next
    case (Cont generat c input)
    then obtain generat' where *: "generat' \<in> set_spmf (the_gpv x)"
      and **: "generat \<in> set_spmf (if is_Pure generat' then the_gpv (f (generat.result generat'))
                                 else return_spmf (IO (generat.output generat') (\<lambda>input. continuation generat' input \<bind> f)))"
      by(auto)
    show ?case
    proof(cases "is_Pure generat'")
      case True
      then have "out \<in> outs'_gpv (f (result generat'))" using Cont(2-3) ** by(auto intro: outs'_gpvI)
      moreover have "result generat' \<in> results'_gpv x" using * True
        by(auto intro: results'_gpvI generat.set_sel)
      ultimately show ?thesis by blast
    next
      case False
      then have generat: "generat = IO (output generat') (\<lambda>input. continuation generat' input \<bind> f)"
        using ** by simp
      with Cont(2) have "c input = continuation generat' input \<bind> f" by auto
      hence "out \<in> outs'_gpv (continuation generat' input) \<union> (\<Union>x\<in>results'_gpv (continuation generat' input). outs'_gpv (f x))"
        by(rule Cont)
      thus ?thesis
      proof
        assume "out \<in> outs'_gpv (continuation generat' input)"
        with * ** False have "out \<in> outs'_gpv x" by(auto intro: outs'_gpvI generat.set_sel)
        thus ?thesis ..
      next
        assume "out \<in> (\<Union>x\<in>results'_gpv (continuation generat' input). outs'_gpv (f x))"
        then obtain y where "y \<in> results'_gpv (continuation generat' input)" "out \<in> outs'_gpv (f y)" ..
        from \<open>y \<in> _\<close> * ** False have "y \<in> results'_gpv x" 
          by(auto intro: results'_gpvI generat.set_sel)
        with \<open>out \<in> outs'_gpv (f y)\<close> show ?thesis by blast
      qed
    qed
  qed
next
  fix out
  assume "out \<in> ?rhs"
  then show "out \<in> ?lhs"
  proof
    assume "out \<in> outs'_gpv x"
    thus ?thesis
    proof(induction)
      case (Out generat gpv)
      then show ?case
        by(cases generat)(fastforce intro: outs'_gpvI rev_bexI)+
    next
      case (Cont generat gpv gpv')
      then show ?case
        by(cases generat)(auto 4 4 intro: outs'_gpvI rev_bexI simp add: in_set_spmf set_pmf_bind_spmf simp del: set_bind_spmf)
    qed
  next
    assume "out \<in> (\<Union>x\<in>results'_gpv x. outs'_gpv (f x))"
    then obtain y where "y \<in> results'_gpv x" "out \<in> outs'_gpv (f y)" ..
    from \<open>y \<in> _\<close> show ?thesis
    proof(induction)
      case (Pure generat gpv)
      thus ?case using \<open>out \<in> outs'_gpv _\<close>
        by(cases generat)(auto 4 5 intro: outs'_gpvI rev_bexI elim: outs'_gpv_cases)
    next
      case (Cont generat gpv gpv')
      thus ?case
        by(cases generat)(auto 4 4 simp add: in_set_spmf simp add: set_pmf_bind_spmf intro: outs'_gpvI rev_bexI simp del: set_bind_spmf)
    qed
  qed
qed

lemma bind_gpv_Fail [simp]: "Fail \<bind> f = Fail"
by(subst bind_gpv_unfold)(simp add: Fail_def)

lemma bind_gpv_eq_Fail:
  "bind_gpv gpv f = Fail \<longleftrightarrow> (\<forall>x\<in>set_spmf (the_gpv gpv). is_Pure x) \<and> (\<forall>x\<in>results'_gpv gpv. f x = Fail)"
  (is "?lhs = ?rhs")
proof(intro iffI conjI strip)
  show ?lhs if ?rhs using that
    by(intro gpv.expand)(auto 4 4 simp add: bind_eq_return_pmf_None intro: results'_gpv_Pure generat.set_sel dest: bspec)

  assume ?lhs
  hence *: "the_gpv (bind_gpv gpv f) = return_pmf None" by simp
  from * show "is_Pure x" if "x \<in> set_spmf (the_gpv gpv)" for x using that
    by(simp add: bind_eq_return_pmf_None split: if_split_asm)
  show "f x = Fail" if "x \<in> results'_gpv gpv" for x using that *
    by(cases)(auto 4 3 simp add: bind_eq_return_pmf_None elim!: generat.set_cases intro: gpv.expand dest: bspec)
qed

context includes lifting_syntax begin

lemma bind_gpv_parametric [transfer_rule]:
  "(rel_gpv A C ===> (A ===> rel_gpv B C) ===> rel_gpv B C) bind_gpv bind_gpv"
unfolding bind_gpv_def by transfer_prover

lemma bind_gpv_parametric':
  "(rel_gpv'' A C R ===> (A ===> rel_gpv'' B C R) ===> rel_gpv'' B C R) bind_gpv bind_gpv"
unfolding bind_gpv_def supply corec_gpv_parametric'[transfer_rule] the_gpv_parametric'[transfer_rule]
by(transfer_prover)

end

lemma monad_gpv [locale_witness]: "monad Done bind_gpv"
by(unfold_locales)(simp_all add: bind_gpv_assoc)

lemma monad_fail_gpv [locale_witness]: "monad_fail Done bind_gpv Fail"
by unfold_locales auto

lemma rel_gpv_bindI:
  "\<lbrakk> rel_gpv A C gpv gpv'; \<And>x y. A x y \<Longrightarrow> rel_gpv B C (f x) (g y) \<rbrakk>
  \<Longrightarrow> rel_gpv B C (bind_gpv gpv f) (bind_gpv gpv' g)"
by(fact bind_gpv_parametric[THEN rel_funD, THEN rel_funD, OF _ rel_funI])

lemma bind_gpv_cong:
  "\<lbrakk> gpv = gpv'; \<And>x. x \<in> results'_gpv gpv' \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> bind_gpv gpv f = bind_gpv gpv' g"
apply(subst gpv.rel_eq[symmetric])
apply(rule rel_gpv_bindI[where A="eq_onp (\<lambda>x. x \<in> results'_gpv gpv')"])
 apply(subst (asm) gpv.rel_eq[symmetric])
 apply(erule gpv.rel_mono_strong)
  apply(simp add: eq_onp_def)
 apply simp
apply(clarsimp simp add: gpv.rel_eq eq_onp_def)
done

definition bind_rpv :: "('a, 'in, 'out) rpv \<Rightarrow> ('a \<Rightarrow> ('b, 'in, 'out) gpv) \<Rightarrow> ('b, 'in, 'out) rpv"
where "bind_rpv rpv f = (\<lambda>input. bind_gpv (rpv input) f)"

lemma bind_rpv_apply [simp]: "bind_rpv rpv f input = bind_gpv (rpv input) f"
by(simp add: bind_rpv_def fun_eq_iff)

adhoc_overloading Monad_Syntax.bind bind_rpv

lemma bind_rpv_code_cong: "rpv = rpv' \<Longrightarrow> bind_rpv rpv f = bind_rpv rpv' f" by simp
setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm bind_rpv_code_cong})\<close>

lemma bind_rpv_rDone [simp]: "bind_rpv rpv Done = rpv"
by(simp add: bind_rpv_def)

lemma bind_gpv_Pause [simp]: "bind_gpv (Pause out rpv) f = Pause out (bind_rpv rpv f)"
by(rule gpv.expand)(simp add: fun_eq_iff)

lemma bind_rpv_React [simp]: "bind_rpv (React f) g = React (apsnd (\<lambda>rpv. bind_rpv rpv g) \<circ> f)"
by(simp add: React_def split_beta fun_eq_iff)

lemma bind_rpv_assoc: "bind_rpv (bind_rpv rpv f) g = bind_rpv rpv ((\<lambda>gpv. bind_gpv gpv g) \<circ> f)"
by(simp add: fun_eq_iff bind_gpv_assoc o_def)

lemma bind_rpv_Done [simp]: "bind_rpv Done f = f"
by(simp add: bind_rpv_def)

lemma results'_rpv_Done [simp]: "results'_rpv Done = UNIV"
by(auto simp add: results'_rpv_def)


subsection \<open> Embedding @{typ "'a spmf"} as a monad \<close>

lemma neg_fun_distr3:
  includes lifting_syntax
  assumes 1: "left_unique R" "right_total R"
  assumes 2: "right_unique S" "left_total S"
  shows "(R OO R' ===> S OO S') \<le> ((R ===> S) OO (R' ===> S'))"
using functional_relation[OF 2] functional_converse_relation[OF 1]
unfolding rel_fun_def OO_def
apply clarify
apply (subst all_comm)
apply (subst all_conj_distrib[symmetric])
apply (intro choice)
by metis

locale spmf_to_gpv begin

text \<open>
  The lifting package cannot handle free term variables in the merging of transfer rules,
  so for the embedding we define a specialised relator \<open>rel_gpv'\<close>
  which acts only on the returned values.
\<close>

definition rel_gpv' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> ('b, 'out, 'in) gpv \<Rightarrow> bool"
where "rel_gpv' A = rel_gpv A (=)"

lemma rel_gpv'_eq [relator_eq]: "rel_gpv' (=) = (=)"
unfolding rel_gpv'_def gpv.rel_eq ..

lemma rel_gpv'_mono [relator_mono]: "A \<le> B \<Longrightarrow> rel_gpv' A \<le> rel_gpv' B"
unfolding rel_gpv'_def by(rule gpv.rel_mono; simp)

lemma rel_gpv'_distr [relator_distr]: "rel_gpv' A OO rel_gpv' B = rel_gpv' (A OO B)"
unfolding rel_gpv'_def by (metis OO_eq gpv.rel_compp) 

lemma left_unique_rel_gpv' [transfer_rule]: "left_unique A \<Longrightarrow> left_unique (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: left_unique_rel_gpv left_unique_eq)

lemma right_unique_rel_gpv' [transfer_rule]: "right_unique A \<Longrightarrow> right_unique (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: right_unique_rel_gpv right_unique_eq)

lemma bi_unique_rel_gpv' [transfer_rule]: "bi_unique A \<Longrightarrow> bi_unique (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: bi_unique_rel_gpv bi_unique_eq)

lemma left_total_rel_gpv' [transfer_rule]: "left_total A \<Longrightarrow> left_total (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: left_total_rel_gpv left_total_eq)

lemma right_total_rel_gpv' [transfer_rule]: "right_total A \<Longrightarrow> right_total (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: right_total_rel_gpv right_total_eq)

lemma bi_total_rel_gpv' [transfer_rule]: "bi_total A \<Longrightarrow> bi_total (rel_gpv' A)"
unfolding rel_gpv'_def by(simp add: bi_total_rel_gpv bi_total_eq)


text \<open>
  We cannot use \<open>setup_lifting\<close> because @{typ "('a, 'out, 'in) gpv"} contains
  type variables which do not appear in @{typ "'a spmf"}.
\<close>

definition cr_spmf_gpv :: "'a spmf \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where "cr_spmf_gpv p gpv \<longleftrightarrow> gpv = lift_spmf p"

definition spmf_of_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> 'a spmf"
where "spmf_of_gpv gpv = (THE p. gpv = lift_spmf p)"

lemma spmf_of_gpv_lift_spmf [simp]: "spmf_of_gpv (lift_spmf p) = p"
unfolding spmf_of_gpv_def by auto

lemma rel_spmf_setD2:
  "\<lbrakk> rel_spmf A p q; y \<in> set_spmf q \<rbrakk> \<Longrightarrow> \<exists>x\<in>set_spmf p. A x y"
by(erule rel_spmfE) force

lemma rel_gpv_lift_spmf1: "rel_gpv A B (lift_spmf p) gpv \<longleftrightarrow> (\<exists>q. gpv = lift_spmf q \<and> rel_spmf A p q)"
apply(subst gpv.rel_sel)
apply(simp add: spmf_rel_map rel_generat_Pure1)
apply safe
 apply(rule exI[where x="map_spmf result (the_gpv gpv)"])
 apply(clarsimp simp add: spmf_rel_map)
 apply(rule conjI)
  apply(rule gpv.expand)
  apply(simp add: spmf.map_comp)
  apply(subst map_spmf_cong[OF refl, where g=id])
   apply(drule (1) rel_spmf_setD2)
   apply clarsimp
  apply simp
 apply(erule rel_spmf_mono)
 apply clarsimp
apply(clarsimp simp add: spmf_rel_map)
done

lemma rel_gpv_lift_spmf2: "rel_gpv A B gpv (lift_spmf q) \<longleftrightarrow> (\<exists>p. gpv = lift_spmf p \<and> rel_spmf A p q)"
by(subst gpv.rel_flip[symmetric])(simp add: rel_gpv_lift_spmf1 pmf.rel_flip option.rel_conversep)

definition pcr_spmf_gpv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> ('b, 'out, 'in) gpv \<Rightarrow> bool"
where "pcr_spmf_gpv A = cr_spmf_gpv OO rel_gpv A (=)"

lemma pcr_cr_eq_spmf_gpv: "pcr_spmf_gpv (=) = cr_spmf_gpv"
by(simp add: pcr_spmf_gpv_def gpv.rel_eq OO_eq)

lemma left_unique_cr_spmf_gpv: "left_unique cr_spmf_gpv"
by(rule left_uniqueI)(simp add: cr_spmf_gpv_def)

lemma left_unique_pcr_spmf_gpv [transfer_rule]:
  "left_unique A \<Longrightarrow> left_unique (pcr_spmf_gpv A)"
unfolding pcr_spmf_gpv_def by(intro left_unique_OO left_unique_cr_spmf_gpv left_unique_rel_gpv left_unique_eq)

lemma right_unique_cr_spmf_gpv: "right_unique cr_spmf_gpv"
by(rule right_uniqueI)(simp add: cr_spmf_gpv_def)

lemma right_unique_pcr_spmf_gpv [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (pcr_spmf_gpv A)"
unfolding pcr_spmf_gpv_def by(intro right_unique_OO right_unique_cr_spmf_gpv right_unique_rel_gpv right_unique_eq)

lemma bi_unique_cr_spmf_gpv: "bi_unique cr_spmf_gpv"
by(simp add: bi_unique_alt_def left_unique_cr_spmf_gpv right_unique_cr_spmf_gpv)

lemma bi_unique_pcr_spmf_gpv [transfer_rule]: "bi_unique A \<Longrightarrow> bi_unique (pcr_spmf_gpv A)"
by(simp add: bi_unique_alt_def left_unique_pcr_spmf_gpv right_unique_pcr_spmf_gpv)

lemma left_total_cr_spmf_gpv: "left_total cr_spmf_gpv"
by(rule left_totalI)(simp add: cr_spmf_gpv_def)

lemma left_total_pcr_spmf_gpv [transfer_rule]: "left_total A ==> left_total (pcr_spmf_gpv A)"
unfolding pcr_spmf_gpv_def by(intro left_total_OO left_total_cr_spmf_gpv left_total_rel_gpv left_total_eq)

context includes lifting_syntax begin

lemma return_spmf_gpv_transfer':
  "((=) ===> cr_spmf_gpv) return_spmf Done"
by(rule rel_funI)(simp add: cr_spmf_gpv_def)

lemma return_spmf_gpv_transfer [transfer_rule]:
  "(A ===> pcr_spmf_gpv A) return_spmf Done"
unfolding pcr_spmf_gpv_def
apply(rewrite in "(\<hole> ===> _) _ _" eq_OO[symmetric])
apply(rule pos_fun_distr[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
apply(rule relcomppI)
 apply(rule return_spmf_gpv_transfer')
apply transfer_prover
done

lemma bind_spmf_gpv_transfer':
  "(cr_spmf_gpv ===> ((=) ===> cr_spmf_gpv) ===> cr_spmf_gpv) bind_spmf bind_gpv"
apply(clarsimp simp add: rel_fun_def cr_spmf_gpv_def)
apply(rule gpv.expand)
apply(simp add: bind_map_spmf map_spmf_bind_spmf o_def)
done

lemma bind_spmf_gpv_transfer [transfer_rule]:
  "(pcr_spmf_gpv A ===> (A ===> pcr_spmf_gpv B) ===> pcr_spmf_gpv B) bind_spmf bind_gpv"
unfolding pcr_spmf_gpv_def
apply(rewrite in "(_ ===> (\<hole> ===> _) ===> _) _ _" eq_OO[symmetric])
apply(rule fun_mono[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
  apply(rule order.refl)
 apply(rule fun_mono)
  apply(rule neg_fun_distr3[OF left_unique_eq right_total_eq right_unique_cr_spmf_gpv left_total_cr_spmf_gpv])
 apply(rule order.refl)
apply(rule fun_mono[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
  apply(rule order.refl)
 apply(rule pos_fun_distr)
apply(rule pos_fun_distr[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
apply(rule relcomppI)
 apply(rule bind_spmf_gpv_transfer')
apply transfer_prover
done

lemma lift_spmf_gpv_transfer':
  "((=) ===> cr_spmf_gpv) (\<lambda>x. x) lift_spmf"
by(simp add: rel_fun_def cr_spmf_gpv_def)

lemma lift_spmf_gpv_transfer [transfer_rule]:
  "(rel_spmf A ===> pcr_spmf_gpv A) (\<lambda>x. x) lift_spmf"
unfolding pcr_spmf_gpv_def
apply(rewrite in "(\<hole> ===> _) _ _" eq_OO[symmetric])
apply(rule pos_fun_distr[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
apply(rule relcomppI)
 apply(rule lift_spmf_gpv_transfer')
apply transfer_prover
done

lemma fail_spmf_gpv_transfer': "cr_spmf_gpv (return_pmf None) Fail"
by(simp add: cr_spmf_gpv_def)

lemma fail_spmf_gpv_transfer [transfer_rule]: "pcr_spmf_gpv A (return_pmf None) Fail"
unfolding pcr_spmf_gpv_def
apply(rule relcomppI)
 apply(rule fail_spmf_gpv_transfer')
apply transfer_prover
done

lemma map_spmf_gpv_transfer':
  "((=) ===> R ===> cr_spmf_gpv ===> cr_spmf_gpv) (\<lambda>f g. map_spmf f) map_gpv"
by(simp add: rel_fun_def cr_spmf_gpv_def map_lift_spmf)

lemma map_spmf_gpv_transfer [transfer_rule]:
  "((A ===> B) ===> R ===> pcr_spmf_gpv A ===> pcr_spmf_gpv B) (\<lambda>f g. map_spmf f) map_gpv"
unfolding pcr_spmf_gpv_def
apply(rewrite in "((\<hole> ===> _) ===> _)  _ _" eq_OO[symmetric])
apply(rewrite in "((_ ===> \<hole>) ===> _)  _ _" eq_OO[symmetric])
apply(rewrite in "(_ ===> \<hole> ===> _)  _ _" OO_eq[symmetric])
apply(rule fun_mono[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
  apply(rule neg_fun_distr3[OF left_unique_eq right_total_eq right_unique_eq left_total_eq])
 apply(rule fun_mono[OF order.refl])
 apply(rule pos_fun_distr)
apply(rule fun_mono[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
  apply(rule order.refl)
 apply(rule pos_fun_distr)
apply(rule pos_fun_distr[THEN le_funD, THEN le_funD, THEN le_boolD, THEN mp])
apply(rule relcomppI)
 apply(unfold rel_fun_eq)
 apply(rule map_spmf_gpv_transfer')
apply(unfold rel_fun_eq[symmetric])
apply transfer_prover
done

end

end

subsection \<open> Embedding @{typ "'a option"} as a monad \<close>

locale option_to_gpv begin

interpretation option_to_spmf .
interpretation spmf_to_gpv .

definition cr_option_gpv :: "'a option \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where "cr_option_gpv x gpv \<longleftrightarrow> gpv = (lift_spmf \<circ> return_pmf) x"

lemma cr_option_gpv_conv_OO:
  "cr_option_gpv = cr_spmf_option\<inverse>\<inverse> OO cr_spmf_gpv"
by(simp add: fun_eq_iff relcompp.simps cr_option_gpv_def cr_spmf_gpv_def cr_spmf_option_def)

context includes lifting_syntax begin

text \<open>These transfer rules should follow from merging the transfer rules, but this has not yet been implemented.\<close>

lemma return_option_gpv_transfer [transfer_rule]:
  "((=) ===> cr_option_gpv) Some Done"
by(simp add: cr_option_gpv_def rel_fun_def)

lemma bind_option_gpv_transfer [transfer_rule]:
  "(cr_option_gpv ===> ((=) ===> cr_option_gpv) ===> cr_option_gpv) Option.bind bind_gpv"
apply(clarsimp simp add: cr_option_gpv_def rel_fun_def)
subgoal for x f g by(cases x; simp)
done

lemma fail_option_gpv_transfer [transfer_rule]: "cr_option_gpv None Fail"
by(simp add: cr_option_gpv_def)

lemma map_option_gpv_transfer [transfer_rule]:
  "((=) ===> R ===> cr_option_gpv ===> cr_option_gpv) (\<lambda>f g. map_option f) map_gpv"
unfolding rel_fun_eq by(simp add: rel_fun_def cr_option_gpv_def map_lift_spmf)

end

end

locale option_le_gpv begin

interpretation option_le_spmf .
interpretation spmf_to_gpv .

definition cr_option_le_gpv :: "'a option \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where "cr_option_le_gpv x gpv \<longleftrightarrow> gpv = (lift_spmf \<circ> return_pmf) x \<or> x = None"

context includes lifting_syntax begin

lemma return_option_le_gpv_transfer [transfer_rule]:
  "((=) ===> cr_option_le_gpv) Some Done"
by(simp add: cr_option_le_gpv_def rel_fun_def)

lemma bind_option_gpv_transfer [transfer_rule]:
  "(cr_option_le_gpv ===> ((=) ===> cr_option_le_gpv) ===> cr_option_le_gpv) Option.bind bind_gpv"
apply(clarsimp simp add: cr_option_le_gpv_def rel_fun_def bind_eq_Some_conv)
subgoal for f g x y by(erule allE[where x=y]) auto
done

lemma fail_option_gpv_transfer [transfer_rule]:
  "cr_option_le_gpv None Fail"
by(simp add: cr_option_le_gpv_def)

lemma map_option_gpv_transfer [transfer_rule]:
  "(((=) ===> (=)) ===> cr_option_le_gpv ===> cr_option_le_gpv) map_option (\<lambda>f. map_gpv f id)"
unfolding rel_fun_eq by(simp add: rel_fun_def cr_option_le_gpv_def map_lift_spmf)

end

end

subsection \<open>Embedding resumptions\<close>

primcorec lift_resumption :: "('a, 'out, 'in) resumption \<Rightarrow> ('a, 'out, 'in) gpv"
where
  "the_gpv (lift_resumption r) = 
  (case r of resumption.Done None \<Rightarrow> return_pmf None
    | resumption.Done (Some x') => return_spmf (Pure x')
    | resumption.Pause out c => map_spmf (map_generat id id ((\<circ>) lift_resumption)) (return_spmf (IO out c)))"

lemma the_gpv_lift_resumption:
  "the_gpv (lift_resumption r) = 
   (if is_Done r then if Option.is_none (resumption.result r) then return_pmf None else return_spmf (Pure (the (resumption.result r)))
    else return_spmf (IO (resumption.output r) (lift_resumption \<circ> resume r)))"
by(simp split: option.split resumption.split)

declare lift_resumption.simps [simp del]

lemma lift_resumption_Done [code]:
  "lift_resumption (resumption.Done x) = (case x of None \<Rightarrow> Fail | Some x' \<Rightarrow> Done x')"
by(rule gpv.expand)(simp add: the_gpv_lift_resumption split: option.split)

lemma lift_resumption_DONE [simp]:
  "lift_resumption (DONE x) = Done x"
by(simp add: DONE_def lift_resumption_Done)

lemma lift_resumption_ABORT [simp]:
  "lift_resumption ABORT = Fail"
by(simp add: ABORT_def lift_resumption_Done)

lemma lift_resumption_Pause [simp, code]:
  "lift_resumption (resumption.Pause out c) = Pause out (lift_resumption \<circ> c)"
by(rule gpv.expand)(simp add: the_gpv_lift_resumption)

lemma lift_resumption_Done_Some [simp]: "lift_resumption (resumption.Done (Some x)) = Done x"
using lift_resumption_DONE unfolding DONE_def by simp

lemma results'_gpv_lift_resumption [simp]:
  "results'_gpv (lift_resumption r) = results r" (is "?lhs = ?rhs")
proof(rule set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv\<equiv>"lift_resumption r" arbitrary: r)
      (auto intro: resumption.set_sel simp add: lift_resumption.sel split: resumption.split_asm option.split_asm)
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that by induction(auto simp add: lift_resumption.sel)
qed

lemma outs'_gpv_lift_resumption [simp]:
  "outs'_gpv (lift_resumption r) = outputs r" (is "?lhs = ?rhs")
proof(rule set_eqI iffI)+
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
    by(induction gpv\<equiv>"lift_resumption r" arbitrary: r)
      (auto simp add: lift_resumption.sel split: resumption.split_asm option.split_asm)
  show "x \<in> ?lhs" if "x \<in> ?rhs" for x using that by induction auto
qed

lemma pred_gpv_lift_resumption [simp]:
  "\<And>A. pred_gpv A C (lift_resumption r) = pred_resumption A C r"
by(simp add: pred_gpv_def pred_resumption_def)

lemma lift_resumption_bind: "lift_resumption (r \<bind> f) = lift_resumption r \<bind> lift_resumption \<circ> f"
by(coinduction arbitrary: r rule: gpv.coinduct_strong)
  (auto simp add: lift_resumption.sel Done_bind split: resumption.split option.split del: rel_funI intro!: rel_funI)

subsection \<open>Assertions\<close>

definition assert_gpv :: "bool \<Rightarrow> (unit, 'out, 'in) gpv"
where "assert_gpv b = (if b then Done () else Fail)"

lemma assert_gpv_simps [simp]:
  "assert_gpv True = Done ()"
  "assert_gpv False = Fail"
by(simp_all add: assert_gpv_def)

lemma [simp]:
  shows assert_gpv_eq_Done: "assert_gpv b = Done x \<longleftrightarrow> b"
  and Done_eq_assert_gpv: "Done x = assert_gpv b \<longleftrightarrow> b"
  and Pause_neq_assert_gpv: "Pause out rpv \<noteq> assert_gpv b"
  and assert_gpv_neq_Pause: "assert_gpv b \<noteq> Pause out rpv"
  and assert_gpv_eq_Fail: "assert_gpv b = Fail \<longleftrightarrow> \<not> b"
  and Fail_eq_assert_gpv: "Fail = assert_gpv b \<longleftrightarrow> \<not> b"
by(simp_all add: assert_gpv_def)

lemma assert_gpv_inject [simp]: "assert_gpv b = assert_gpv b' \<longleftrightarrow> b = b'"
by(simp add: assert_gpv_def)

lemma assert_gpv_sel [simp]:
  "the_gpv (assert_gpv b) = map_spmf Pure (assert_spmf b)"
by(simp add: assert_gpv_def)

lemma the_gpv_bind_assert [simp]:
  "the_gpv (bind_gpv (assert_gpv b) f) =
   bind_spmf (assert_spmf b) (the_gpv \<circ> f)"
by(cases b) simp_all

lemma pred_gpv_assert [simp]: "pred_gpv P Q (assert_gpv b) = (b \<longrightarrow> P ())"
by(cases b) simp_all

primcorec try_gpv :: "('a, 'call, 'ret) gpv \<Rightarrow> ('a, 'call, 'ret) gpv \<Rightarrow> ('a, 'call, 'ret) gpv" ("TRY _ ELSE _" [0,60] 59)
where
  "the_gpv (TRY gpv ELSE gpv') = 
   map_spmf (map_generat id id (\<lambda>c input. case c input of Inl gpv \<Rightarrow> try_gpv gpv gpv' | Inr gpv' \<Rightarrow> gpv'))
     (try_spmf (map_spmf (map_generat id id (map_fun id Inl)) (the_gpv gpv))
               (map_spmf (map_generat id id (map_fun id Inr)) (the_gpv gpv')))"

lemma try_gpv_sel:
  "the_gpv (TRY gpv ELSE gpv') =
   TRY map_spmf (map_generat id id (\<lambda>c input. TRY c input ELSE gpv')) (the_gpv gpv) ELSE the_gpv gpv'"
by(simp add: try_gpv_def map_try_spmf spmf.map_comp o_def generat.map_comp generat.map_ident id_def)

lemma try_gpv_Done [simp]: "TRY Done x ELSE gpv' = Done x"
by(rule gpv.expand)(simp)

lemma try_gpv_Fail [simp]: "TRY Fail ELSE gpv' = gpv'"
by(rule gpv.expand)(simp add: spmf.map_comp o_def generat.map_comp generat.map_ident)

lemma try_gpv_Pause [simp]: "TRY Pause out c ELSE gpv' = Pause out (\<lambda>input. TRY c input ELSE gpv')"
by(rule gpv.expand) simp

lemma try_gpv_Fail2 [simp]: "TRY gpv ELSE Fail = gpv"
by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  (auto simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI generat.rel_refl)

lemma lift_try_spmf: "lift_spmf (TRY p ELSE q) = TRY lift_spmf p ELSE lift_spmf q" 
by(rule gpv.expand)(simp add: map_try_spmf spmf.map_comp o_def)

lemma try_assert_gpv: "TRY assert_gpv b ELSE gpv' = (if b then Done () else gpv')"
by(simp)

context includes lifting_syntax begin
lemma try_gpv_parametric [transfer_rule]:
  "(rel_gpv A C ===> rel_gpv A C ===> rel_gpv A C) try_gpv try_gpv"
unfolding try_gpv_def by transfer_prover

lemma try_gpv_parametric':
  "(rel_gpv'' A C R ===> rel_gpv'' A C R ===> rel_gpv'' A C R) try_gpv try_gpv"
unfolding try_gpv_def
supply corec_gpv_parametric'[transfer_rule] the_gpv_parametric'[transfer_rule]
by transfer_prover
end

lemma map_try_gpv: "map_gpv f g (TRY gpv ELSE gpv') = TRY map_gpv f g gpv ELSE map_gpv f g gpv'"
by(simp add: gpv.rel_map try_gpv_parametric[THEN rel_funD, THEN rel_funD] gpv.rel_refl gpv.rel_eq[symmetric])

lemma map'_try_gpv: "map_gpv' f g h (TRY gpv ELSE gpv') = TRY map_gpv' f g h gpv ELSE map_gpv' f g h gpv'"
by(coinduction arbitrary: gpv rule: gpv.coinduct_strong)(auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI generat.rel_refl rel_funI rel_spmf_try_spmf)
  

lemma try_bind_assert_gpv:
  "TRY (assert_gpv b \<bind> f) ELSE gpv = (if b then TRY (f ()) ELSE gpv else gpv)"
by(simp)



subsection \<open>Order for @{typ "('a, 'out, 'in) gpv"}\<close>

coinductive ord_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where
  "ord_spmf (rel_generat (=) (=) (rel_fun (=) ord_gpv)) f g \<Longrightarrow> ord_gpv (GPV f) (GPV g)"

inductive_simps ord_gpv_simps [simp]:
  "ord_gpv (GPV f) (GPV g)"

lemma ord_gpv_coinduct [consumes 1, case_names ord_gpv, coinduct pred: ord_gpv]:
  assumes "X f g"
  and step: "\<And>f g. X f g \<Longrightarrow> ord_spmf (rel_generat (=) (=) (rel_fun (=) X)) (the_gpv f) (the_gpv g)"
  shows "ord_gpv f g"
using \<open>X f g\<close>
by(coinduct)(auto dest: step simp add: eq_GPV_iff intro: ord_spmf_mono rel_generat_mono rel_fun_mono)

lemma ord_gpv_the_gpvD:
  "ord_gpv f g \<Longrightarrow> ord_spmf (rel_generat (=) (=) (rel_fun (=) ord_gpv)) (the_gpv f) (the_gpv g)"
by(erule ord_gpv.cases) simp

lemma reflp_equality: "reflp (=)"
by(simp add: reflp_def)

lemma ord_gpv_reflI [simp]: "ord_gpv f f"
by(coinduction arbitrary: f)(auto intro: ord_spmf_reflI simp add: rel_generat_same rel_fun_def)

lemma reflp_ord_gpv: "reflp ord_gpv"
by(rule reflpI)(rule ord_gpv_reflI)

lemma ord_gpv_trans:
  assumes "ord_gpv f g" "ord_gpv g h"
  shows "ord_gpv f h"
using assms
proof(coinduction arbitrary: f g h)
  case (ord_gpv f g h)
  have *: "ord_spmf (rel_generat (=) (=) (rel_fun (=) (\<lambda>f h. \<exists>g. ord_gpv f g \<and> ord_gpv g h))) (the_gpv f) (the_gpv h) =
    ord_spmf (rel_generat ((=) OO (=)) ((=) OO (=)) (rel_fun (=) (ord_gpv OO ord_gpv))) (the_gpv f) (the_gpv h)"
    by(simp add: relcompp.simps[abs_def])
  then show ?case using ord_gpv
    by(auto elim!: ord_gpv.cases simp add: generat.rel_compp ord_spmf_compp fun.rel_compp)
qed

lemma ord_gpv_compp: "(ord_gpv OO ord_gpv) = ord_gpv"
by(auto simp add: fun_eq_iff intro: ord_gpv_trans)

lemma transp_ord_gpv [simp]: "transp ord_gpv"
by(blast intro: transpI ord_gpv_trans)

lemma ord_gpv_antisym:
  "\<lbrakk> ord_gpv f g; ord_gpv g f \<rbrakk> \<Longrightarrow> f = g"
proof(coinduction arbitrary: f g)
  case (Eq_gpv f g)
  let ?R = "rel_generat (=) (=) (rel_fun (=) ord_gpv)"
  from \<open>ord_gpv f g\<close> have "ord_spmf ?R (the_gpv f) (the_gpv g)" by cases simp
  moreover
  from \<open>ord_gpv g f\<close> have "ord_spmf ?R (the_gpv g) (the_gpv f)" by cases simp
  ultimately have "rel_spmf (inf ?R ?R\<inverse>\<inverse>) (the_gpv f) (the_gpv g)"
    by(rule rel_spmf_inf)(auto 4 3 intro: transp_rel_generatI transp_ord_gpv reflp_ord_gpv reflp_equality reflp_fun1 is_equality_eq transp_rel_fun)
  also have "inf ?R ?R\<inverse>\<inverse> = rel_generat (inf (=) (=)) (inf (=) (=)) (rel_fun (=) (inf ord_gpv ord_gpv\<inverse>\<inverse>))"
    unfolding rel_generat_inf[symmetric] rel_fun_inf[symmetric]
    by(simp add: generat.rel_conversep[symmetric] fun.rel_conversep)
  finally show ?case by(simp add: inf_fun_def)
qed

lemma RFail_least [simp]: "ord_gpv Fail f"
by(coinduction arbitrary: f)(simp add: eq_GPV_iff)

subsection \<open>Bounds on interaction\<close>

context
  fixes "consider" :: "'out \<Rightarrow> bool"
  notes monotone_SUP[partial_function_mono] [[function_internals]]
begin
declaration \<open>Partial_Function.init "lfp_strong" @{term lfp.fixp_fun} @{term lfp.mono_body}
  @{thm lfp.fixp_rule_uc} @{thm lfp.fixp_induct_strong2_uc} NONE\<close>

partial_function (lfp_strong) interaction_bound :: "('a, 'out, 'in) gpv \<Rightarrow> enat"
where
  "interaction_bound gpv =
  (SUP generat\<in>set_spmf (the_gpv gpv). case generat of Pure _ \<Rightarrow> 0 
     | IO out c \<Rightarrow> if consider out then eSuc (SUP input. interaction_bound (c input)) else (SUP input. interaction_bound (c input)))"

lemma interaction_bound_fixp_induct [case_names adm bottom step]:
  "\<lbrakk> ccpo.admissible (fun_lub Sup) (fun_ord (\<le>)) P;
     P (\<lambda>_. 0);
    \<And>interaction_bound'. 
    \<lbrakk> P interaction_bound'; 
      \<And>gpv. interaction_bound' gpv \<le> interaction_bound gpv;
      \<And>gpv. interaction_bound' gpv \<le> (SUP generat\<in>set_spmf (the_gpv gpv). case generat of Pure _ \<Rightarrow> 0 
     | IO out c \<Rightarrow> if consider out then eSuc (SUP input. interaction_bound' (c input)) else (SUP input. interaction_bound' (c input)))
      \<rbrakk>
      \<Longrightarrow> P (\<lambda>gpv. \<Squnion>generat\<in>set_spmf (the_gpv gpv). case generat of Pure x \<Rightarrow> 0
         | IO out c \<Rightarrow> if consider out then eSuc (\<Squnion>input. interaction_bound' (c input)) else (\<Squnion>input. interaction_bound' (c input))) \<rbrakk>
   \<Longrightarrow> P interaction_bound"
by(erule interaction_bound.fixp_induct)(simp_all add: bot_enat_def fun_ord_def)

lemma interaction_bound_IO:
   "IO out c \<in> set_spmf (the_gpv gpv)
   \<Longrightarrow> (if consider out then eSuc (interaction_bound (c input)) else interaction_bound (c input)) \<le> interaction_bound gpv"
by(rewrite in "_ \<le> \<hole>" interaction_bound.simps)(auto intro!: SUP_upper2)

lemma interaction_bound_IO_consider:
   "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); consider out \<rbrakk>
   \<Longrightarrow> eSuc (interaction_bound (c input)) \<le> interaction_bound gpv"
by(drule interaction_bound_IO) simp

lemma interaction_bound_IO_ignore:
   "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); \<not> consider out \<rbrakk>
   \<Longrightarrow> interaction_bound (c input) \<le> interaction_bound gpv"
by(drule interaction_bound_IO) simp

lemma interaction_bound_Done [simp]: "interaction_bound (Done x) = 0"
by(simp add: interaction_bound.simps)

lemma interaction_bound_Fail [simp]: "interaction_bound Fail = 0"
by(simp add: interaction_bound.simps bot_enat_def)

lemma interaction_bound_Pause [simp]:
  "interaction_bound (Pause out c) = 
   (if consider out then eSuc (SUP input. interaction_bound (c input)) else (SUP input. interaction_bound (c input)))"
by(simp add: interaction_bound.simps)

lemma interaction_bound_lift_spmf [simp]: "interaction_bound (lift_spmf p) = 0"
by(simp add: interaction_bound.simps SUP_constant bot_enat_def)

lemma interaction_bound_assert_gpv [simp]: "interaction_bound (assert_gpv b) = 0"
by(cases b) simp_all

lemma interaction_bound_bind_step:
  assumes IH: "\<And>p. interaction_bound' (p \<bind> f) \<le> interaction_bound p + (\<Squnion>x\<in>results'_gpv p. interaction_bound' (f x))"
  and unfold: "\<And>gpv. interaction_bound' gpv \<le> (\<Squnion>generat\<in>set_spmf (the_gpv gpv). case generat of Pure x \<Rightarrow> 0
             | IO out c \<Rightarrow> if consider out then eSuc (\<Squnion>input. interaction_bound' (c input)) else \<Squnion>input. interaction_bound' (c input))"
  shows "(\<Squnion>generat\<in>set_spmf (the_gpv (p \<bind> f)).
             case generat of Pure x \<Rightarrow> 0
             | IO out c \<Rightarrow>
                 if consider out then eSuc (\<Squnion>input. interaction_bound' (c input))
                 else \<Squnion>input. interaction_bound' (c input))
         \<le> interaction_bound p +
            (\<Squnion>x\<in>results'_gpv p.
                \<Squnion>generat\<in>set_spmf (the_gpv (f x)).
                   case generat of Pure x \<Rightarrow> 0
                   | IO out c \<Rightarrow>
                       if consider out then eSuc (\<Squnion>input. interaction_bound' (c input))
                       else \<Squnion>input. interaction_bound' (c input))"
    (is "(SUP generat'\<in>?bind. ?g generat') \<le> ?p + ?f")
proof(rule SUP_least)
  fix generat'
  assume "generat' \<in> ?bind"
  then obtain generat where generat: "generat \<in> set_spmf (the_gpv p)"
    and *: "case generat of Pure x \<Rightarrow> generat' \<in> set_spmf (the_gpv (f x)) 
         | IO out c \<Rightarrow> generat' = IO out (\<lambda>input. c input \<bind> f)"
    by(clarsimp simp add: bind_gpv.sel simp del: bind_gpv_sel')
      (clarsimp split: generat.split_asm simp add: generat.map_comp o_def generat.map_id[unfolded id_def])
  show "?g generat' \<le> ?p + ?f"
  proof(cases generat)
    case (Pure x)
    have "?g generat' \<le> (SUP generat'\<in>set_spmf (the_gpv (f x)). (case generat' of Pure x \<Rightarrow> 0 | IO out c \<Rightarrow> if consider out then eSuc (\<Squnion>input. interaction_bound' (c input)) else \<Squnion>input. interaction_bound' (c input)))"
      using * Pure by(auto intro: SUP_upper)
    also have "\<dots> \<le> 0 + ?f" using generat Pure
      by(auto 4 3 intro: SUP_upper results'_gpv_Pure)
    also have "\<dots> \<le> ?p + ?f" by simp
    finally show ?thesis .
  next
    case (IO out c)
    with * have "?g generat' = (if consider out then eSuc (SUP input. interaction_bound' (c input \<bind> f)) else (SUP input. interaction_bound' (c input \<bind> f)))" by simp
    also have "\<dots> \<le> (if consider out then eSuc (SUP input. interaction_bound (c input) + (\<Squnion>x\<in>results'_gpv (c input). interaction_bound' (f x))) else (SUP input. interaction_bound (c input) + (\<Squnion>x\<in>results'_gpv (c input). interaction_bound' (f x))))"
      by(auto intro: SUP_mono IH)
    also have "\<dots> \<le> (case IO out c of Pure (x :: 'a) \<Rightarrow> 0 | IO out c \<Rightarrow> if consider out then eSuc (SUP input. interaction_bound (c input)) else (SUP input. interaction_bound (c input))) + (SUP input. SUP x\<in>results'_gpv (c input). interaction_bound' (f x))"
      by(simp add: iadd_Suc SUP_le_iff)(meson SUP_upper2 UNIV_I add_mono order_refl)
    also have "\<dots> \<le> ?p + ?f"
      apply(rewrite in "_ \<le> \<hole>" interaction_bound.simps)
      apply(rule add_mono SUP_least SUP_upper generat[unfolded IO])+
      apply(rule order_trans[OF unfold])
      apply(auto 4 3 intro: results'_gpv_Cont[OF generat] SUP_upper simp add: IO)
      done
    finally show ?thesis .
  qed
qed

lemma interaction_bound_bind:
  defines "ib1 \<equiv> interaction_bound"
  shows "interaction_bound (p \<bind> f) \<le> ib1 p + (SUP x\<in>results'_gpv p. interaction_bound (f x))"
proof(induction arbitrary: p rule: interaction_bound_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step interaction_bound') then show ?case unfolding ib1_def by -(rule interaction_bound_bind_step)
qed

lemma interaction_bound_bind_lift_spmf [simp]:
  "interaction_bound (lift_spmf p \<bind> f) = (SUP x\<in>set_spmf p. interaction_bound (f x))"
by(subst (1 2) interaction_bound.simps)(simp add: bind_UNION SUP_UNION)

end

abbreviation interaction_any_bound :: "('a, 'out, 'in) gpv \<Rightarrow> enat"
where "interaction_any_bound \<equiv> interaction_bound (\<lambda>_. True)"

lemma interaction_any_bound_coinduct [consumes 1, case_names interaction_bound]:
  assumes X: "X gpv n"
  and *: "\<And>gpv n out c input. \<lbrakk> X gpv n; IO out c \<in> set_spmf (the_gpv gpv) \<rbrakk> 
    \<Longrightarrow> \<exists>n'. (X (c input) n' \<or> interaction_any_bound (c input) \<le> n') \<and> eSuc n' \<le> n"
  shows "interaction_any_bound gpv \<le> n"
using X
proof(induction arbitrary: gpv n rule: interaction_bound_fixp_induct)
  case adm show ?case by(intro cont_intro)
  case bottom show ?case by simp
next
  case (step interaction_bound')
  { fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    from *[OF step.prems IO] obtain n' where n: "n = eSuc n'"
      by(cases n rule: co.enat.exhaust) auto
    moreover 
    { fix input
      have "\<exists>n''. (X (c input) n'' \<or> interaction_any_bound (c input) \<le> n'') \<and> eSuc n'' \<le> n"
        using step.prems IO \<open>n = eSuc n'\<close> by(auto 4 3 dest: *)
      then have "interaction_bound' (c input) \<le> n'" using n
        by(auto dest: step.IH intro: step.hyps[THEN order_trans] elim!: order_trans simp add: neq_zero_conv_eSuc) }
    ultimately have "eSuc (\<Squnion>input. interaction_bound' (c input)) \<le> n"
      by(auto intro: SUP_least) }
  then show ?case by(auto intro!: SUP_least split: generat.split)
qed

context includes lifting_syntax begin
lemma interaction_bound_parametric':
  assumes [transfer_rule]: "bi_total R"
  shows "((C ===> (=)) ===> rel_gpv'' A C R ===> (=)) interaction_bound interaction_bound"
unfolding interaction_bound_def[abs_def]
apply(rule rel_funI)
apply(rule fixp_lfp_parametric_eq[OF interaction_bound.mono interaction_bound.mono])
subgoal premises [transfer_rule]
  supply the_gpv_parametric'[transfer_rule] rel_gpv''_eq[relator_eq]
  by transfer_prover
done

lemma interaction_bound_parametric [transfer_rule]:
  "((C ===> (=)) ===> rel_gpv A C ===> (=)) interaction_bound interaction_bound"
unfolding rel_gpv_conv_rel_gpv'' by(rule interaction_bound_parametric')(rule bi_total_eq)
end

text \<open>
  There is no nice @{const interaction_bound} equation for @{const bind_gpv}, as it computes
  an exact bound, but we only need an upper bound.
  As @{typ enat} is hard to work with (and @{term \<infinity>} does not constrain a gpv in any way),
  we work with @{typ nat}.
\<close>

inductive interaction_bounded_by :: "('out \<Rightarrow> bool) \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> enat \<Rightarrow> bool"
for "consider" gpv n where
  interaction_bounded_by: "\<lbrakk> interaction_bound consider gpv \<le> n \<rbrakk> \<Longrightarrow> interaction_bounded_by consider gpv n"

lemmas interaction_bounded_byI = interaction_bounded_by
hide_fact (open) interaction_bounded_by

context includes lifting_syntax begin
lemma interaction_bounded_by_parametric [transfer_rule]:
  "((C ===> (=)) ===> rel_gpv A C ===> (=) ===> (=)) interaction_bounded_by interaction_bounded_by"
unfolding interaction_bounded_by.simps[abs_def] by transfer_prover

lemma interaction_bounded_by_parametric':
  notes interaction_bound_parametric'[transfer_rule]
  assumes [transfer_rule]: "bi_total R"
  shows "((C ===> (=)) ===> rel_gpv'' A C R ===> (=) ===> (=)) 
         interaction_bounded_by interaction_bounded_by"
unfolding interaction_bounded_by.simps[abs_def] by transfer_prover
end

lemma interaction_bounded_by_mono:
  "\<lbrakk> interaction_bounded_by consider gpv n; n \<le> m \<rbrakk> \<Longrightarrow> interaction_bounded_by consider gpv m"
unfolding interaction_bounded_by.simps by(erule order_trans) simp

lemma interaction_bounded_by_contD:
  "\<lbrakk> interaction_bounded_by consider gpv n; IO out c \<in> set_spmf (the_gpv gpv); consider out \<rbrakk>
  \<Longrightarrow> n > 0 \<and> interaction_bounded_by consider (c input) (n - 1)"
unfolding interaction_bounded_by.simps
by(subst (asm) interaction_bound.simps)(auto simp add: SUP_le_iff eSuc_le_iff enat_eSuc_iff dest!: bspec)

lemma interaction_bounded_by_contD_ignore:
  "\<lbrakk> interaction_bounded_by consider gpv n; IO out c \<in> set_spmf (the_gpv gpv) \<rbrakk>
  \<Longrightarrow> interaction_bounded_by consider (c input) n"
unfolding interaction_bounded_by.simps
by(subst (asm) interaction_bound.simps)(auto 4 4 simp add: SUP_le_iff eSuc_le_iff enat_eSuc_iff dest!: bspec split: if_split_asm elim: order_trans)

lemma interaction_bounded_byI_epred:
  assumes "\<And>out c. \<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); consider out \<rbrakk> \<Longrightarrow> n \<noteq> 0 \<and> (\<forall>input. interaction_bounded_by consider (c input) (n - 1))"
  and "\<And>out c input. \<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); \<not> consider out \<rbrakk> \<Longrightarrow> interaction_bounded_by consider (c input) n"
  shows "interaction_bounded_by consider gpv n"
unfolding interaction_bounded_by.simps
by(subst interaction_bound.simps)(auto 4 5 intro!: SUP_least split: generat.split dest: assms simp add: eSuc_le_iff enat_eSuc_iff gr0_conv_Suc neq_zero_conv_eSuc interaction_bounded_by.simps)

lemma interaction_bounded_by_IO:
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); interaction_bounded_by consider gpv n; consider out \<rbrakk>
  \<Longrightarrow> n \<noteq> 0 \<and> interaction_bounded_by consider (c input) (n - 1)"
by(drule interaction_bound_IO[where input=input and ?consider="consider"])(auto simp add: interaction_bounded_by.simps epred_conv_minus eSuc_le_iff enat_eSuc_iff)

lemma interaction_bounded_by_0: "interaction_bounded_by consider gpv 0 \<longleftrightarrow> interaction_bound consider gpv = 0"
by(simp add: interaction_bounded_by.simps zero_enat_def[symmetric])

abbreviation interaction_bounded_by' :: "('out \<Rightarrow> bool) \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> nat \<Rightarrow> bool"
where "interaction_bounded_by' consider gpv n \<equiv> interaction_bounded_by consider gpv (enat n)"

named_theorems interaction_bound

lemmas interaction_bounded_by_start = interaction_bounded_by_mono

method interaction_bound_start = (rule interaction_bounded_by_start)
method interaction_bound_step uses add simp =
  ((match conclusion in "interaction_bounded_by _ _ _" \<Rightarrow> fail \<bar> _ \<Rightarrow> \<open>solves \<open>clarsimp simp add: simp\<close>\<close>) | rule add interaction_bound)
method interaction_bound_rec uses add simp = 
  (interaction_bound_step add: add simp: simp; (interaction_bound_rec add: add simp: simp)?)
method interaction_bound uses add simp =
  ((* use in *) interaction_bound_start, interaction_bound_rec add: add simp: simp)

lemma interaction_bounded_by_Done [simp]: "interaction_bounded_by consider (Done x) n"
by(simp add: interaction_bounded_by.simps)

lemma interaction_bounded_by_DoneI [interaction_bound]:
  "interaction_bounded_by consider (Done x) 0"
by simp

lemma interaction_bounded_by_Fail [simp]: "interaction_bounded_by consider Fail n"
by(simp add: interaction_bounded_by.simps)

lemma interaction_bounded_by_FailI [interaction_bound]: "interaction_bounded_by consider Fail 0"
by simp

lemma interaction_bounded_by_lift_spmf [simp]: "interaction_bounded_by consider (lift_spmf p) n"
by(simp add: interaction_bounded_by.simps)

lemma interaction_bounded_by_lift_spmfI [interaction_bound]:
  "interaction_bounded_by consider (lift_spmf p) 0"
by simp

lemma interaction_bounded_by_assert_gpv [simp]: "interaction_bounded_by consider (assert_gpv b) n"
by(cases b) simp_all

lemma interaction_bounded_by_assert_gpvI [interaction_bound]:
  "interaction_bounded_by consider (assert_gpv b) 0"
by simp

lemma interaction_bounded_by_Pause [simp]:
  "interaction_bounded_by consider (Pause out c) n \<longleftrightarrow> 
  (if consider out then 0 < n \<and> (\<forall>input. interaction_bounded_by consider (c input) (n - 1)) else (\<forall>input. interaction_bounded_by consider (c input) n))"
by(cases n rule: co.enat.exhaust)
  (auto 4 3 simp add: interaction_bounded_by.simps eSuc_le_iff enat_eSuc_iff gr0_conv_Suc intro: SUP_least dest: order_trans[OF SUP_upper, rotated])

lemma interaction_bounded_by_PauseI [interaction_bound]:
  "(\<And>input. interaction_bounded_by consider (c input) (n input))
  \<Longrightarrow> interaction_bounded_by consider (Pause out c) (if consider out then 1 + (SUP input. n input) else (SUP input. n input))"
by(auto simp add: iadd_is_0 enat_add_sub_same intro: interaction_bounded_by_mono SUP_upper)

lemma interaction_bounded_by_bindI [interaction_bound]:
  "\<lbrakk> interaction_bounded_by consider gpv n; \<And>x. x \<in> results'_gpv gpv \<Longrightarrow> interaction_bounded_by consider (f x) (m x) \<rbrakk>
  \<Longrightarrow> interaction_bounded_by consider (gpv \<bind> f) (n + (SUP x\<in>results'_gpv gpv. m x))"
unfolding interaction_bounded_by.simps plus_enat_simps(1)[symmetric]
by(rule interaction_bound_bind[THEN order_trans])(auto intro: add_mono SUP_mono)

lemma interaction_bounded_by_bind_PauseI [interaction_bound]:
  "(\<And>input. interaction_bounded_by consider (c input \<bind> f) (n input))
  \<Longrightarrow> interaction_bounded_by consider (Pause out c \<bind> f) (if consider out then SUP input. n input + 1 else SUP input. n input)"
by(auto 4 3 simp add: interaction_bounded_by.simps SUP_enat_add_left eSuc_plus_1 intro: SUP_least SUP_upper2)

lemma interaction_bounded_by_bind_lift_spmf [simp]:
  "interaction_bounded_by consider (lift_spmf p \<bind> f) n \<longleftrightarrow> (\<forall>x\<in>set_spmf p. interaction_bounded_by consider (f x) n)"
by(simp add: interaction_bounded_by.simps SUP_le_iff)

lemma interaction_bounded_by_bind_lift_spmfI [interaction_bound]:
  "(\<And>x. x \<in> set_spmf p \<Longrightarrow> interaction_bounded_by consider (f x) (n x))
  \<Longrightarrow> interaction_bounded_by consider (lift_spmf p \<bind> f) (SUP x\<in>set_spmf p. n x)"
by(auto intro: interaction_bounded_by_mono SUP_upper)

lemma interaction_bounded_by_bind_DoneI [interaction_bound]:
  "interaction_bounded_by consider (f x) n \<Longrightarrow> interaction_bounded_by consider (Done x \<bind> f) n"
by(simp)

lemma interaction_bounded_by_if [interaction_bound]:
  "\<lbrakk> b \<Longrightarrow> interaction_bounded_by consider gpv1 n; \<not> b \<Longrightarrow> interaction_bounded_by consider gpv2 m \<rbrakk>
  \<Longrightarrow> interaction_bounded_by consider (if b then gpv1 else gpv2) (if b then n else m)"
by(auto 4 3 simp add: max_def not_le elim: interaction_bounded_by_mono)

lemma interaction_bounded_by_case_bool [interaction_bound]:
  "\<lbrakk> b \<Longrightarrow> interaction_bounded_by consider t bt; \<not> b \<Longrightarrow> interaction_bounded_by consider f bf \<rbrakk>
  \<Longrightarrow> interaction_bounded_by consider (case_bool t f b) (if b then bt else bf)"
by(cases b)(auto)

lemma interaction_bounded_by_case_sum [interaction_bound]:
  "\<lbrakk> \<And>y. x = Inl y \<Longrightarrow> interaction_bounded_by consider (l y) (bl y);
     \<And>y. x = Inr y \<Longrightarrow> interaction_bounded_by consider (r y) (br y) \<rbrakk>
  \<Longrightarrow> interaction_bounded_by consider (case_sum l r x) (case_sum bl br x)"
by(cases x)(auto)

lemma interaction_bounded_by_case_prod [interaction_bound]:
  "(\<And>a b. x = (a, b) \<Longrightarrow> interaction_bounded_by consider (f a b) (n a b))
  \<Longrightarrow> interaction_bounded_by consider (case_prod f x) (case_prod n x)"
by(simp split: prod.split)

lemma interaction_bounded_by_let [interaction_bound]: \<comment> \<open>This rule unfolds let's\<close>
  "interaction_bounded_by consider (f t) m \<Longrightarrow> interaction_bounded_by consider (Let t f) m"
by(simp add: Let_def)

lemma interaction_bounded_by_map_gpv_id [interaction_bound]:
  assumes [interaction_bound]: "interaction_bounded_by P gpv n"
  shows "interaction_bounded_by P (map_gpv f id gpv) n"
unfolding id_def map_gpv_conv_bind by interaction_bound simp

abbreviation interaction_any_bounded_by :: "('a, 'out, 'in) gpv \<Rightarrow> enat \<Rightarrow> bool"
where "interaction_any_bounded_by \<equiv> interaction_bounded_by (\<lambda>_. True)"

subsection \<open>Typing\<close>

subsubsection \<open>Interface between gpvs and rpvs / callees\<close>

lemma is_empty_parametric [transfer_rule]: "rel_fun (rel_set A) (=) Set.is_empty Set.is_empty" (* Move *)
by(auto simp add: rel_fun_def Set.is_empty_def dest: rel_setD1 rel_setD2)

typedef ('call, 'ret) \<I> = "UNIV :: ('call \<Rightarrow> 'ret set) set" ..

setup_lifting type_definition_\<I>

lemma outs_\<I>_tparametric:
  includes lifting_syntax 
  assumes [transfer_rule]: "bi_total A"
  shows "((A ===> rel_set B) ===> rel_set A) (\<lambda>resps. {out. resps out \<noteq> {}}) (\<lambda>resps. {out. resps out \<noteq> {}})"
  by(fold Set.is_empty_def) transfer_prover

lift_definition outs_\<I> :: "('call, 'ret) \<I> \<Rightarrow> 'call set" is "\<lambda>resps. {out. resps out \<noteq> {}}" parametric outs_\<I>_tparametric .
lift_definition responses_\<I> :: "('call, 'ret) \<I> \<Rightarrow> 'call \<Rightarrow> 'ret set" is "\<lambda>x. x" parametric id_transfer[unfolded id_def] .

lift_definition rel_\<I> :: "('call \<Rightarrow> 'call' \<Rightarrow> bool) \<Rightarrow> ('ret \<Rightarrow> 'ret' \<Rightarrow> bool) \<Rightarrow> ('call, 'ret) \<I> \<Rightarrow> ('call', 'ret') \<I> \<Rightarrow> bool"
is "\<lambda>C R resp1 resp2. rel_set C {out. resp1 out \<noteq> {}} {out. resp2 out \<noteq> {}} \<and> rel_fun C (rel_set R) resp1 resp2"
.

lemma rel_\<I>I [intro?]:
  "\<lbrakk> rel_set C (outs_\<I> \<I>1) (outs_\<I> \<I>2); \<And>x y. C x y \<Longrightarrow> rel_set R (responses_\<I> \<I>1 x) (responses_\<I> \<I>2 y) \<rbrakk>
  \<Longrightarrow> rel_\<I> C R \<I>1 \<I>2"
by transfer(auto simp add: rel_fun_def)

lemma rel_\<I>_eq [relator_eq]: "rel_\<I> (=) (=) = (=)"
unfolding fun_eq_iff by transfer(auto simp add: relator_eq)

lemma rel_\<I>_conversep [simp]: "rel_\<I> C\<inverse>\<inverse> R\<inverse>\<inverse> = (rel_\<I> C R)\<inverse>\<inverse>"
unfolding fun_eq_iff conversep_iff
apply transfer
apply(rewrite in "rel_fun \<hole>" conversep_iff[symmetric])
apply(rewrite in "rel_set \<hole>" conversep_iff[symmetric])
apply(rewrite in "rel_fun _ \<hole>" conversep_iff[symmetric])
apply(simp del: conversep_iff add: rel_fun_conversep)
apply(simp)
done

lemma rel_\<I>_conversep1_eq [simp]: "rel_\<I> C\<inverse>\<inverse> (=) = (rel_\<I> C (=))\<inverse>\<inverse>"
by(rewrite in "\<hole> = _" conversep_eq[symmetric])(simp del: conversep_eq)

lemma rel_\<I>_conversep2_eq [simp]: "rel_\<I> (=) R\<inverse>\<inverse> = (rel_\<I> (=) R)\<inverse>\<inverse>"
by(rewrite in "\<hole> = _" conversep_eq[symmetric])(simp del: conversep_eq)

lemma responses_\<I>_empty_iff: "responses_\<I> \<I> out = {} \<longleftrightarrow> out \<notin> outs_\<I> \<I>"
including \<I>.lifting by transfer auto

lemma in_outs_\<I>_iff_responses_\<I>: "out \<in> outs_\<I> \<I> \<longleftrightarrow> responses_\<I> \<I> out \<noteq> {}"
by(simp add: responses_\<I>_empty_iff)

lift_definition \<I>_full :: "('call, 'ret) \<I>" is "\<lambda>_. UNIV" .

lemma \<I>_full_sel [simp]:
  shows outs_\<I>_full: "outs_\<I> \<I>_full = UNIV"
  and responses_\<I>_full: "responses_\<I> \<I>_full x = UNIV"
by(transfer; simp; fail)+

context includes lifting_syntax begin
lemma outs_\<I>_parametric [transfer_rule]: "(rel_\<I> C R ===> rel_set C) outs_\<I> outs_\<I>"
unfolding rel_fun_def by transfer simp

lemma responses_\<I>_parametric [transfer_rule]: 
  "(rel_\<I> C R ===> C ===> rel_set R) responses_\<I> responses_\<I>"
unfolding rel_fun_def by transfer(auto dest: rel_funD)

end

definition \<I>_trivial :: "('out, 'in) \<I> \<Rightarrow> bool"
where "\<I>_trivial \<I> \<longleftrightarrow> outs_\<I> \<I> = UNIV"

lemma \<I>_trivialI [intro?]: "(\<And>x. x \<in> outs_\<I> \<I>) \<Longrightarrow> \<I>_trivial \<I>"
by(auto simp add: \<I>_trivial_def)

lemma \<I>_trivialD: "\<I>_trivial \<I> \<Longrightarrow> outs_\<I> \<I> = UNIV"
by(simp add: \<I>_trivial_def)

lemma \<I>_trivial_\<I>_full [simp]: "\<I>_trivial \<I>_full"
by(simp add: \<I>_trivial_def)

lifting_update \<I>.lifting
lifting_forget \<I>.lifting


context begin
qualified inductive resultsp_gpv :: "('out, 'in) \<I> \<Rightarrow> 'a \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
  for \<Gamma> x
where
  Pure: "Pure x \<in> set_spmf (the_gpv gpv) \<Longrightarrow> resultsp_gpv \<Gamma> x gpv"
| IO:
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<Gamma> out; resultsp_gpv \<Gamma> x (c input) \<rbrakk>
  \<Longrightarrow> resultsp_gpv \<Gamma> x gpv"

definition results_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> 'a set"
where "results_gpv \<Gamma> gpv \<equiv> {x. resultsp_gpv \<Gamma> x gpv}"

lemma resultsp_gpv_results_gpv_eq [pred_set_conv]: "resultsp_gpv \<Gamma> x gpv \<longleftrightarrow> x \<in> results_gpv \<Gamma> gpv"
by(simp add: results_gpv_def)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "results_gpv")\<close>

lemmas intros [intro?] = resultsp_gpv.intros[to_set]
  and Pure = Pure[to_set]
  and IO = IO[to_set]
  and induct [consumes 1, case_names Pure IO, induct set: results_gpv] = resultsp_gpv.induct[to_set]
  and cases [consumes 1, case_names Pure IO, cases set: results_gpv] = resultsp_gpv.cases[to_set]
  and simps = resultsp_gpv.simps[to_set]
end

inductive_simps results_gpv_GPV [to_set, simp]: "resultsp_gpv \<Gamma> x (GPV gpv)"

end

lemma results_gpv_Done [iff]: "results_gpv \<Gamma> (Done x) = {x}"
by(auto simp add: Done.ctr)

lemma results_gpv_Fail [iff]: "results_gpv \<Gamma> Fail = {}"
by(auto simp add: Fail_def)

lemma results_gpv_Pause [simp]:
  "results_gpv \<Gamma> (Pause out c) = (\<Union>input\<in>responses_\<I> \<Gamma> out. results_gpv \<Gamma> (c input))"
by(auto simp add: Pause.ctr)

lemma results_gpv_lift_spmf [iff]: "results_gpv \<Gamma> (lift_spmf p) = set_spmf p"
by(auto simp add: lift_spmf.ctr)

lemma results_gpv_assert_gpv [simp]: "results_gpv \<Gamma> (assert_gpv b) = (if b then {()} else {})"
by auto

lemma results_gpv_bind_gpv [simp]:
  "results_gpv \<Gamma> (gpv \<bind> f) = (\<Union>x\<in>results_gpv \<Gamma> gpv. results_gpv \<Gamma> (f x))"
  (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  fix x
  assume "x \<in> ?lhs"
  then show "x \<in> ?rhs"
  proof(induction gpv'\<equiv>"gpv \<bind> f" arbitrary: gpv)
    case Pure thus ?case
      by(auto 4 3 split: if_split_asm intro: results_gpv.intros rev_bexI)
  next
    case (IO out c input)
    from \<open>IO out c \<in> _\<close>
    obtain generat where generat: "generat \<in> set_spmf (the_gpv gpv)"
      and *: "IO out c \<in> set_spmf (if is_Pure generat then the_gpv (f (result generat))
                                   else return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> f)))"
      by(auto)
    thus ?case
    proof(cases generat)
      case (Pure y)
      with generat have "y \<in> results_gpv \<Gamma> gpv" by(auto intro: results_gpv.intros)
      thus ?thesis using * Pure \<open>input \<in> responses_\<I> \<Gamma> out\<close> \<open>x \<in> results_gpv \<Gamma> (c input)\<close>
        by(auto intro: results_gpv.IO)
    next
      case (IO out' c')
      hence [simp]: "out' = out"
        and c: "\<And>input. c input = bind_gpv (c' input) f" using * by simp_all
      from IO.hyps(4)[OF c] obtain y where y: "y \<in> results_gpv \<Gamma> (c' input)"
        and "x \<in> results_gpv \<Gamma> (f y)" by blast
      from y IO generat have "y \<in> results_gpv \<Gamma> gpv" using \<open>input \<in> responses_\<I> \<Gamma> out\<close>
        by(auto intro: results_gpv.IO)
      with \<open>x \<in> results_gpv \<Gamma> (f y)\<close> show ?thesis by blast
    qed
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then obtain y where y: "y \<in> results_gpv \<Gamma> gpv"
    and x: "x \<in> results_gpv \<Gamma> (f y)" by blast
  from y show "x \<in> ?lhs"
  proof(induction)
    case (Pure gpv)
    with x show ?case
      by cases(auto 4 4 intro: results_gpv.intros rev_bexI)
  qed(auto 4 4 intro: rev_bexI results_gpv.IO)
qed

lemma results_gpv_\<I>_full: "results_gpv \<I>_full = results'_gpv"
proof(intro ext set_eqI iffI)
  show "x \<in> results'_gpv gpv" if "x \<in> results_gpv \<I>_full gpv" for x gpv
    using that by induction(auto intro: results'_gpvI)
  show "x \<in> results_gpv \<I>_full gpv" if "x \<in> results'_gpv gpv" for x gpv
    using that by induction(auto intro: results_gpv.intros elim!: generat.set_cases)
qed

lemma results'_bind_gpv [simp]:
  "results'_gpv (bind_gpv gpv f) = (\<Union>x\<in>results'_gpv gpv. results'_gpv (f x))"
unfolding results_gpv_\<I>_full[symmetric] by simp

lemma results_gpv_map_gpv_id [simp]: "results_gpv \<I> (map_gpv f id gpv) = f ` results_gpv \<I> gpv"
  by(auto simp add: map_gpv_conv_bind id_def)

lemma results_gpv_map_gpv_id' [simp]: "results_gpv \<I> (map_gpv f (\<lambda>x. x) gpv) = f ` results_gpv \<I> gpv"
  by(auto simp add: map_gpv_conv_bind id_def)

lemma pred_gpv_bind [simp]: "pred_gpv P Q (bind_gpv gpv f) = pred_gpv (pred_gpv P Q \<circ> f) Q gpv"
by(auto simp add: pred_gpv_def outs_bind_gpv)

lemma results'_gpv_bind_option [simp]:
  "results'_gpv (monad.bind_option Fail x f) = (\<Union>y\<in>set_option x. results'_gpv (f y))"
by(cases x) simp_all

lemma bind_gpv_bind_option_assoc:
  "bind_gpv (monad.bind_option Fail x f) g = monad.bind_option Fail x (\<lambda>x. bind_gpv (f x) g)"
by(cases x) simp_all

subsubsection \<open>Type judgements\<close>

coinductive WT_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool" ("((_)/ \<turnstile>g (_) \<surd>)" [100, 0] 99)
  for \<Gamma>
where
  "(\<And>out c. IO out c \<in> set_spmf gpv \<Longrightarrow> out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input\<in>responses_\<I> \<Gamma> out. \<Gamma> \<turnstile>g c input \<surd>))
  \<Longrightarrow> \<Gamma> \<turnstile>g GPV gpv \<surd>"

lemma WT_gpv_coinduct [consumes 1, case_names WT_gpv, case_conclusion WT_gpv out cont, coinduct pred: WT_gpv]:
  assumes *: "X gpv"
  and step: "\<And>gpv out c.
    \<lbrakk> X gpv; IO out c \<in> set_spmf (the_gpv gpv) \<rbrakk>
    \<Longrightarrow> out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input \<in> responses_\<I> \<Gamma> out. X (c input) \<or> \<Gamma> \<turnstile>g c input \<surd>)"
  shows "\<Gamma> \<turnstile>g gpv \<surd>"
using * by(coinduct)(auto dest: step simp add: eq_GPV_iff)

lemma WT_gpv_simps:
  "\<Gamma> \<turnstile>g GPV gpv \<surd> \<longleftrightarrow>
   (\<forall>out c. IO out c \<in> set_spmf gpv \<longrightarrow> out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input\<in>responses_\<I> \<Gamma> out. \<Gamma> \<turnstile>g c input \<surd>))"
by(subst WT_gpv.simps) simp

lemma WT_gpvI:
  "(\<And>out c. IO out c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input\<in>responses_\<I> \<Gamma> out. \<Gamma> \<turnstile>g c input \<surd>))
  \<Longrightarrow> \<Gamma> \<turnstile>g gpv \<surd>"
by(cases gpv)(simp add: WT_gpv_simps)

lemma WT_gpvD:
  assumes "\<Gamma> \<turnstile>g gpv \<surd>"
  shows WT_gpv_OutD: "IO out c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> out \<in> outs_\<I> \<Gamma>"
  and WT_gpv_ContD: "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<Gamma> out \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile>g c input \<surd>"
using assms by(cases, fastforce)+

lemma WT_gpv_mono:
  assumes WT: "\<I>1 \<turnstile>g gpv \<surd>"
  and outs: "outs_\<I> \<I>1 \<subseteq> outs_\<I> \<I>2"
  and responses: "\<And>x. x \<in> outs_\<I> \<I>1 \<Longrightarrow> responses_\<I> \<I>2 x \<subseteq> responses_\<I> \<I>1 x"
  shows "\<I>2 \<turnstile>g gpv \<surd>"
using WT
proof coinduct
  case (WT_gpv gpv out c)
  with outs show ?case by(auto 6 4 dest: responses WT_gpvD)
qed

lemma WT_gpv_Done [iff]: "\<Gamma> \<turnstile>g Done x \<surd>"
by(rule WT_gpvI) simp_all

lemma WT_gpv_Fail [iff]: "\<Gamma> \<turnstile>g Fail \<surd>"
by(rule WT_gpvI) simp_all

lemma WT_gpv_PauseI: 
  "\<lbrakk> out \<in> outs_\<I> \<Gamma>; \<And>input. input \<in> responses_\<I> \<Gamma> out \<Longrightarrow> \<Gamma> \<turnstile>g c input \<surd> \<rbrakk>
   \<Longrightarrow> \<Gamma> \<turnstile>g Pause out c \<surd>"
by(rule WT_gpvI) simp_all

lemma WT_gpv_Pause [iff]:
  "\<Gamma> \<turnstile>g Pause out c \<surd> \<longleftrightarrow> out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input \<in> responses_\<I> \<Gamma> out. \<Gamma> \<turnstile>g c input \<surd>)"
by(auto intro: WT_gpv_PauseI dest: WT_gpvD)

lemma WT_gpv_bindI:
  "\<lbrakk> \<Gamma> \<turnstile>g gpv \<surd>; \<And>x. x \<in> results_gpv \<Gamma> gpv \<Longrightarrow> \<Gamma> \<turnstile>g f x \<surd> \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile>g gpv \<bind> f \<surd>"
proof(coinduction arbitrary: gpv)
  case [rule_format]: (WT_gpv out c gpv)
  from \<open>IO out c \<in> _\<close>
  obtain generat where generat: "generat \<in> set_spmf (the_gpv gpv)"
    and *: "IO out c \<in> set_spmf (if is_Pure generat then the_gpv (f (result generat))
                                 else return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> f)))"
    by(auto)
  show ?case
  proof(cases generat)
    case (Pure y)
    with generat have "y \<in> results_gpv \<Gamma> gpv" by(auto intro: results_gpv.Pure)
    hence "\<Gamma> \<turnstile>g f y \<surd>" by(rule WT_gpv)
    with * Pure show ?thesis by(auto dest: WT_gpvD) 
  next
    case (IO out' c')
    hence [simp]: "out' = out"
      and c: "\<And>input. c input = bind_gpv (c' input) f" using * by simp_all
    from generat IO have **: "IO out c' \<in> set_spmf (the_gpv gpv)" by simp
    with \<open>\<Gamma> \<turnstile>g gpv \<surd>\<close> have ?out by(auto dest: WT_gpvD)
    moreover {
      fix input
      assume input: "input \<in> responses_\<I> \<Gamma> out"
      with \<open>\<Gamma> \<turnstile>g gpv \<surd>\<close> ** have "\<Gamma> \<turnstile>g c' input \<surd>" by(rule WT_gpvD)
      moreover {
        fix y
        assume "y \<in> results_gpv \<Gamma> (c' input)"
        with ** input have "y \<in> results_gpv \<Gamma> gpv" by(rule results_gpv.IO)
        hence "\<Gamma> \<turnstile>g f y \<surd>" by(rule WT_gpv) }
      moreover note calculation }
    hence ?cont using c by blast
    ultimately show ?thesis ..
  qed
qed

lemma WT_gpv_bindD2:
  assumes WT: "\<Gamma> \<turnstile>g gpv \<bind> f \<surd>"
  and x: "x \<in> results_gpv \<Gamma> gpv"
  shows "\<Gamma> \<turnstile>g f x \<surd>"
using x WT
proof induction
  case (Pure gpv)
  show ?case
  proof(rule WT_gpvI)
    fix out c
    assume "IO out c \<in> set_spmf (the_gpv (f x))"
    with Pure have "IO out c \<in> set_spmf (the_gpv (gpv \<bind> f))" by(auto intro: rev_bexI)
    with \<open>\<Gamma> \<turnstile>g gpv \<bind> f \<surd>\<close> show "out \<in> outs_\<I> \<Gamma> \<and> (\<forall>input\<in>responses_\<I> \<Gamma> out. \<Gamma> \<turnstile>g c input \<surd>)"
      by(auto dest: WT_gpvD simp del: set_bind_spmf)
  qed
next
  case (IO out c gpv input)
  from \<open>IO out c \<in> _\<close>
  have "IO out (\<lambda>input. bind_gpv (c input) f) \<in> set_spmf (the_gpv (gpv \<bind> f))"
    by(auto intro: rev_bexI)
  with IO.prems have "\<Gamma> \<turnstile>g c input \<bind> f \<surd>" using \<open>input \<in> _\<close> by(rule WT_gpv_ContD)
  thus ?case by(rule IO.IH)
qed

lemma WT_gpv_bindD1: "\<Gamma> \<turnstile>g gpv \<bind> f \<surd> \<Longrightarrow> \<Gamma> \<turnstile>g gpv \<surd>"
proof(coinduction arbitrary: gpv)
  case (WT_gpv out c gpv)
  from \<open>IO out c \<in> _\<close>
  have "IO out (\<lambda>input. bind_gpv (c input) f) \<in> set_spmf (the_gpv (gpv \<bind> f))"
    by(auto intro: rev_bexI)
  with \<open>\<Gamma> \<turnstile>g gpv \<bind> f \<surd>\<close> show ?case
    by(auto simp del: bind_gpv_sel' dest: WT_gpvD)
qed

lemma WT_gpv_bind [simp]: "\<Gamma> \<turnstile>g gpv \<bind> f \<surd> \<longleftrightarrow> \<Gamma> \<turnstile>g gpv \<surd> \<and> (\<forall>x\<in>results_gpv \<Gamma> gpv. \<Gamma> \<turnstile>g f x \<surd>)"
by(blast intro: WT_gpv_bindI dest: WT_gpv_bindD1 WT_gpv_bindD2)

lemma WT_gpv_full [simp, intro!]: "\<I>_full \<turnstile>g gpv \<surd>"
by(coinduction arbitrary: gpv)(auto)

lemma WT_gpv_lift_spmf [simp, intro!]: "\<I> \<turnstile>g lift_spmf p \<surd>"
by(rule WT_gpvI) auto

lemma WT_gpv_coinduct_bind [consumes 1, case_names WT_gpv, case_conclusion WT_gpv out cont]:
  assumes *: "X gpv"
  and step: "\<And>gpv out c. \<lbrakk> X gpv; IO out c \<in> set_spmf (the_gpv gpv) \<rbrakk>
    \<Longrightarrow> out \<in> outs_\<I> \<I> \<and> (\<forall>input\<in>responses_\<I> \<I> out.
            X (c input) \<or>
            \<I> \<turnstile>g c input \<surd> \<or>
            (\<exists>(gpv' :: ('b, 'call, 'ret) gpv) f. c input = gpv' \<bind> f \<and> \<I> \<turnstile>g gpv' \<surd> \<and> (\<forall>x\<in>results_gpv \<I> gpv'. X (f x))))"
  shows "\<I> \<turnstile>g gpv \<surd>"
proof -
  fix x
  define gpv' :: "('b, 'call, 'ret) gpv" and f :: "'b \<Rightarrow> ('a, 'call, 'ret) gpv"
    where "gpv' = Done x" and "f = (\<lambda>_. gpv)"
  with * have "\<I> \<turnstile>g gpv' \<surd>" and "\<And>x. x \<in> results_gpv \<I> gpv' \<Longrightarrow> X (f x)" by simp_all
  then have "\<I> \<turnstile>g gpv' \<bind> f \<surd>"
  proof(coinduction arbitrary: gpv' f rule: WT_gpv_coinduct)
    case [rule_format]: (WT_gpv out c gpv')
    from \<open>IO out c \<in> _\<close>
    obtain generat where generat: "generat \<in> set_spmf (the_gpv gpv')"
      and *: "IO out c \<in> set_spmf (if is_Pure generat
        then the_gpv (f (result generat))
        else return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> f)))"
      by(clarsimp)
    show ?case
    proof(cases generat)
      case (Pure x)
      from Pure * have IO: "IO out c \<in> set_spmf (the_gpv (f x))" by simp
      from generat Pure have "x \<in> results_gpv \<I> gpv'" by (simp add: results_gpv.Pure)
      then have "X (f x)" by(rule WT_gpv)
      from step[OF this IO] show ?thesis by(auto 4 4 intro: exI[where x="Done _"])
    next
      case (IO out' c')
      with * have [simp]: "out' = out"
        and c: "c = (\<lambda>input. c' input \<bind> f)" by simp_all
      from IO generat have IO: "IO out c' \<in> set_spmf (the_gpv gpv')" by simp
      then have "\<And>input. input \<in> responses_\<I> \<I> out \<Longrightarrow> results_gpv \<I> (c' input) \<subseteq> results_gpv \<I> gpv'"
        by(auto intro: results_gpv.IO)
      with WT_gpvD[OF \<open>\<I> \<turnstile>g gpv' \<surd>\<close> IO] show ?thesis unfolding c using WT_gpv(2) by blast
    qed
  qed
  then show ?thesis unfolding gpv'_def f_def by simp
qed

lemma \<I>_trivial_WT_gpvD [simp]: "\<I>_trivial \<I> \<Longrightarrow> \<I> \<turnstile>g gpv \<surd>"
using WT_gpv_full by(rule WT_gpv_mono)(simp_all add: \<I>_trivial_def)

lemma \<I>_trivial_WT_gpvI: 
  assumes "\<And>gpv :: ('a, 'out, 'in) gpv. \<I> \<turnstile>g gpv \<surd>"
  shows "\<I>_trivial \<I>"
proof
  fix x
  have "\<I> \<turnstile>g Pause x (\<lambda>_. Fail :: ('a, 'out, 'in) gpv) \<surd>" by(rule assms)
  thus "x \<in> outs_\<I> \<I>" by(simp)
qed

subsection \<open>Sub-gpvs\<close>

context begin
qualified inductive sub_gpvsp :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
  for \<I> x
where
  base:
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out; x = c input \<rbrakk> 
  \<Longrightarrow> sub_gpvsp \<I> x gpv"
| cont: 
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out; sub_gpvsp \<I> x (c input) \<rbrakk>
  \<Longrightarrow> sub_gpvsp \<I> x gpv"

qualified lemma sub_gpvsp_base:
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out \<rbrakk> 
  \<Longrightarrow> sub_gpvsp \<I> (c input) gpv"
by(rule base) simp_all

definition sub_gpvs :: "('out, 'in) \<I> \<Rightarrow>  ('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv set"
where "sub_gpvs \<I> gpv \<equiv> {x. sub_gpvsp \<I> x gpv}"

lemma sub_gpvsp_sub_gpvs_eq [pred_set_conv]: "sub_gpvsp \<I> x gpv \<longleftrightarrow> x \<in> sub_gpvs \<I> gpv"
by(simp add: sub_gpvs_def)

context begin
local_setup \<open>Local_Theory.map_background_naming (Name_Space.mandatory_path "sub_gpvs")\<close>

lemmas intros [intro?] = sub_gpvsp.intros[to_set]
  and base = sub_gpvsp_base[to_set]
  and cont = cont[to_set]
  and induct [consumes 1, case_names Pure IO, induct set: sub_gpvs] = sub_gpvsp.induct[to_set]
  and cases [consumes 1, case_names Pure IO, cases set: sub_gpvs] = sub_gpvsp.cases[to_set]
  and simps = sub_gpvsp.simps[to_set]
end
end

lemma WT_sub_gpvsD:
  assumes "\<I> \<turnstile>g gpv \<surd>" and "gpv' \<in> sub_gpvs \<I> gpv"
  shows "\<I> \<turnstile>g gpv' \<surd>"
using assms(2,1) by(induction)(auto dest: WT_gpvD)

lemma WT_sub_gpvsI:
  "\<lbrakk> \<And>out c. IO out c \<in> set_spmf (the_gpv gpv) \<Longrightarrow> out \<in> outs_\<I> \<Gamma>; 
     \<And>gpv'. gpv' \<in> sub_gpvs \<Gamma> gpv \<Longrightarrow> \<Gamma> \<turnstile>g gpv' \<surd> \<rbrakk>
  \<Longrightarrow> \<Gamma> \<turnstile>g gpv \<surd>"
by(rule WT_gpvI)(auto intro: sub_gpvs.base)

subsection \<open>Losslessness\<close>

text \<open>A gpv is lossless iff we are guaranteed to get a result after a finite number of interactions
  that respect the interface. It is colossless if the interactions may go on for ever, but there is
  no non-termination.\<close>

text \<open> We define both notions of losslessness simultaneously by mimicking what the (co)inductive
  package would do internally. Thus, we get a constant which is parametrised by the choice of the
  fixpoint, i.e., for non-recursive gpvs, we can state and prove both versions of losslessness
  in one go.\<close>

context
  fixes co :: bool and \<I> :: "('out, 'in) \<I>"
  and F :: "(('a, 'out, 'in) gpv \<Rightarrow> bool) \<Rightarrow> (('a, 'out, 'in) gpv \<Rightarrow> bool)"
  and co' :: bool
  defines "F \<equiv> \<lambda>gen_lossless_gpv gpv. \<exists>pa. gpv = GPV pa \<and> 
     lossless_spmf pa \<and> (\<forall>out c input. IO out c \<in> set_spmf pa \<longrightarrow> input \<in> responses_\<I> \<I> out \<longrightarrow> gen_lossless_gpv (c input))"
  and "co' \<equiv> co" \<comment> \<open>We use a copy of @{term co} such that we can do case distinctions on @{term co'} without
    the simplifier rewriting the @{term co} in the local abbreviations for the constants.\<close>
begin

lemma gen_lossless_gpv_mono: "mono F"
unfolding F_def
apply(rule monoI le_funI le_boolI')+
apply(tactic \<open>REPEAT (resolve_tac @{context} (Inductive.get_monos @{context}) 1)\<close>)
apply(erule le_funE)
apply(erule le_boolD)
done

definition gen_lossless_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> bool"
where "gen_lossless_gpv = (if co' then gfp else lfp) F"

lemma gen_lossless_gpv_unfold: "gen_lossless_gpv = F gen_lossless_gpv"
by(simp add: gen_lossless_gpv_def gfp_unfold[OF gen_lossless_gpv_mono, symmetric] lfp_unfold[OF gen_lossless_gpv_mono, symmetric])

lemma gen_lossless_gpv_True: "co' = True \<Longrightarrow> gen_lossless_gpv \<equiv> gfp F"
  and gen_lossless_gpv_False: "co' = False \<Longrightarrow> gen_lossless_gpv \<equiv> lfp F"
by(simp_all add: gen_lossless_gpv_def)

lemma gen_lossless_gpv_cases [elim?, cases pred]:
  assumes "gen_lossless_gpv gpv"
  obtains (gen_lossless_gpv) p where "gpv = GPV p" "lossless_spmf p" 
    "\<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> gen_lossless_gpv (c input)"
proof -
  from assms show ?thesis
    by(rewrite in asm gen_lossless_gpv_unfold)(auto simp add: F_def intro: that)
qed

lemma gen_lossless_gpvD:
  assumes "gen_lossless_gpv gpv"
  shows gen_lossless_gpv_lossless_spmfD: "lossless_spmf (the_gpv gpv)"
  and gen_lossless_gpv_continuationD:
  "\<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out \<rbrakk> \<Longrightarrow> gen_lossless_gpv (c input)"
using assms by(auto elim: gen_lossless_gpv_cases)

lemma gen_lossless_gpv_intros:
  "\<lbrakk> lossless_spmf p;
     \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; input \<in> responses_\<I> \<I> out \<rbrakk> \<Longrightarrow> gen_lossless_gpv (c input) \<rbrakk>
  \<Longrightarrow> gen_lossless_gpv (GPV p)"
by(rewrite gen_lossless_gpv_unfold)(simp add: F_def)

lemma gen_lossless_gpvI [intro?]:
  "\<lbrakk> lossless_spmf (the_gpv gpv);
     \<And>out c input. \<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out \<rbrakk>
     \<Longrightarrow> gen_lossless_gpv (c input) \<rbrakk>
  \<Longrightarrow> gen_lossless_gpv gpv"
by(cases gpv)(auto intro: gen_lossless_gpv_intros)

lemma gen_lossless_gpv_simps:
  "gen_lossless_gpv gpv \<longleftrightarrow>
   (\<exists>p. gpv = GPV p \<and> lossless_spmf p \<and> (\<forall>out c input.
        IO out c \<in> set_spmf p \<longrightarrow> input \<in> responses_\<I> \<I> out \<longrightarrow> gen_lossless_gpv (c input)))"
by(rewrite gen_lossless_gpv_unfold)(simp add: F_def)

lemma gen_lossless_gpv_Done [iff]: "gen_lossless_gpv (Done x)"
by(rule gen_lossless_gpvI) auto

lemma gen_lossless_gpv_Fail [iff]: "\<not> gen_lossless_gpv Fail"
by(auto dest: gen_lossless_gpvD)

lemma gen_lossless_gpv_Pause [simp]:
  "gen_lossless_gpv (Pause out c) \<longleftrightarrow> (\<forall>input \<in> responses_\<I> \<I> out. gen_lossless_gpv (c input))"
by(auto dest: gen_lossless_gpvD intro: gen_lossless_gpvI)

lemma gen_lossless_gpv_lift_spmf [iff]: "gen_lossless_gpv (lift_spmf p) \<longleftrightarrow> lossless_spmf p"
by(auto dest: gen_lossless_gpvD intro: gen_lossless_gpvI)

end

lemma gen_lossless_gpv_assert_gpv [iff]: "gen_lossless_gpv co \<I> (assert_gpv b) \<longleftrightarrow> b"
by(cases b) simp_all

abbreviation lossless_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where "lossless_gpv \<equiv> gen_lossless_gpv False"

abbreviation colossless_gpv :: "('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> bool"
where "colossless_gpv \<equiv> gen_lossless_gpv True"

lemma lossless_gpv_induct [consumes 1, case_names lossless_gpv, induct pred]:
  assumes *: "lossless_gpv \<I> gpv"
  and step: "\<And>p. \<lbrakk> lossless_spmf p;
     \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> lossless_gpv \<I> (c input);
     \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> P (c input) \<rbrakk>
     \<Longrightarrow> P (GPV p)"
  shows "P gpv"
proof -
  have "lossless_gpv \<I> \<le> P"
    by(rule def_lfp_induct[OF gen_lossless_gpv_False gen_lossless_gpv_mono])(auto intro!: le_funI step)
  then show ?thesis using * by auto
qed

lemma colossless_gpv_coinduct 
  [consumes 1, case_names colossless_gpv, case_conclusion colossless_gpv lossless_spmf continuation, coinduct pred]:
  assumes *: "X gpv"
  and step: "\<And>gpv. X gpv \<Longrightarrow> lossless_spmf (the_gpv gpv) \<and> (\<forall>out c input. 
       IO out c \<in> set_spmf (the_gpv gpv) \<longrightarrow> input \<in> responses_\<I> \<I> out \<longrightarrow> X (c input) \<or> colossless_gpv \<I> (c input))"
  shows "colossless_gpv \<I> gpv"
proof -
  have "X \<le> colossless_gpv \<I>"
    by(rule def_coinduct[OF gen_lossless_gpv_True gen_lossless_gpv_mono])
      (auto 4 4 intro!: le_funI dest!: step intro: exI[where x="the_gpv _"])
  then show ?thesis using * by auto
qed

lemmas lossless_gpvI = gen_lossless_gpvI[where co=False]
  and lossless_gpvD = gen_lossless_gpvD[where co=False]
  and lossless_gpv_lossless_spmfD = gen_lossless_gpv_lossless_spmfD[where co=False]
  and lossless_gpv_continuationD = gen_lossless_gpv_continuationD[where co=False]

lemmas colossless_gpvI = gen_lossless_gpvI[where co=True]
  and colossless_gpvD = gen_lossless_gpvD[where co=True]
  and colossless_gpv_lossless_spmfD = gen_lossless_gpv_lossless_spmfD[where co=True]
  and colossless_gpv_continuationD = gen_lossless_gpv_continuationD[where co=True]

lemma gen_lossless_bind_gpvI:
  assumes "gen_lossless_gpv co \<I> gpv" "\<And>x. x \<in> results_gpv \<I> gpv \<Longrightarrow> gen_lossless_gpv co \<I> (f x)"
  shows "gen_lossless_gpv co \<I> (gpv \<bind> f)"
proof(cases co)
  case False
  hence eq: "co = False" by simp
  show ?thesis using assms unfolding eq
  proof(induction)
    case (lossless_gpv p)
    { fix x
      assume "Pure x \<in> set_spmf p"
      hence "x \<in> results_gpv \<I> (GPV p)" by simp
      hence "lossless_gpv \<I> (f x)" by(rule lossless_gpv.prems) }
    with \<open>lossless_spmf p\<close> show ?case unfolding GPV_bind
      apply(intro gen_lossless_gpv_intros)
       apply(fastforce dest: lossless_gpvD split: generat.split)
      apply(clarsimp; split generat.split_asm)
      apply(auto dest: lossless_gpvD intro!: lossless_gpv)
      done
  qed
next
  case True
  hence eq: "co = True" by simp
  show ?thesis using assms unfolding eq
  proof(coinduction arbitrary: gpv rule: colossless_gpv_coinduct)
    case * [rule_format]: (colossless_gpv gpv)
    from *(1) have ?lossless_spmf 
      by(auto 4 3 dest: colossless_gpv_lossless_spmfD elim!: is_PureE intro: *(2)[THEN colossless_gpv_lossless_spmfD] results_gpv.Pure)
    moreover have ?continuation
    proof(intro strip)
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv (gpv \<bind> f))"
        and input: "input \<in> responses_\<I> \<I> out"
      from IO obtain generat where generat: "generat \<in> set_spmf (the_gpv gpv)"
        and IO: "IO out c \<in> set_spmf (if is_Pure generat then the_gpv (f (result generat))
                 else return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> f)))"
        by(auto)
      show "(\<exists>gpv. c input = gpv \<bind> f \<and> colossless_gpv \<I> gpv \<and> (\<forall>x. x \<in> results_gpv \<I> gpv \<longrightarrow> colossless_gpv \<I> (f x))) \<or>
        colossless_gpv \<I> (c input)"
      proof(cases generat)
        case (Pure x)
        hence "x \<in> results_gpv \<I> gpv" using generat by(auto intro: results_gpv.Pure)
        from *(2)[OF this] have "colossless_gpv \<I> (c input)"
          using IO Pure input by(auto intro: colossless_gpv_continuationD)
        thus ?thesis ..
      next
        case **: (IO out' c')
        with input generat IO have "colossless_gpv \<I> (f x)" if "x \<in> results_gpv \<I> (c' input)" for x
          using that by(auto intro: * results_gpv.IO)
        then show ?thesis using IO input ** *(1) generat by(auto dest: colossless_gpv_continuationD)
      qed
    qed
    ultimately show ?case ..
  qed
qed

lemmas lossless_bind_gpvI = gen_lossless_bind_gpvI[where co=False]
  and colossless_bind_gpvI = gen_lossless_bind_gpvI[where co=True]

lemma gen_lossless_bind_gpvD1: 
  assumes "gen_lossless_gpv co \<I> (gpv \<bind> f)"
  shows "gen_lossless_gpv co \<I> gpv"
proof(cases co)
  case False
  hence eq: "co = False" by simp
  show ?thesis using assms unfolding eq
  proof(induction gpv'\<equiv>"gpv \<bind> f" arbitrary: gpv)
    case (lossless_gpv p)
    obtain p' where gpv: "gpv = GPV p'" by(cases gpv)
    from lossless_gpv.hyps gpv have "lossless_spmf p'" by(simp add: GPV_bind)
    then show ?case unfolding gpv
    proof(rule gen_lossless_gpv_intros)
      fix out c input
      assume "IO out c \<in> set_spmf p'" "input \<in> responses_\<I> \<I> out"
      hence "IO out (\<lambda>input. c input \<bind> f) \<in> set_spmf p" using lossless_gpv.hyps gpv
        by(auto simp add: GPV_bind intro: rev_bexI)
      thus "lossless_gpv \<I> (c input)" using \<open>input \<in> _\<close> by(rule lossless_gpv.hyps) simp
    qed
  qed
next
  case True
  hence eq: "co = True" by simp
  show ?thesis using assms unfolding eq
    by(coinduction arbitrary: gpv)(auto 4 3 intro: rev_bexI elim!: colossless_gpv_continuationD dest: colossless_gpv_lossless_spmfD)
qed

lemmas lossless_bind_gpvD1 = gen_lossless_bind_gpvD1[where co=False]
  and colossless_bind_gpvD1 = gen_lossless_bind_gpvD1[where co=True]

lemma gen_lossless_bind_gpvD2:
  assumes "gen_lossless_gpv co \<I> (gpv \<bind> f)"
  and "x \<in> results_gpv \<I> gpv"
  shows "gen_lossless_gpv co \<I> (f x)"
using assms(2,1)
proof(induction)
  case (Pure gpv)
  thus ?case
    by -(rule gen_lossless_gpvI, auto 4 4 dest: gen_lossless_gpvD intro: rev_bexI)
qed(auto 4 4 dest: gen_lossless_gpvD intro: rev_bexI)

lemmas lossless_bind_gpvD2 = gen_lossless_bind_gpvD2[where co=False]
  and colossless_bind_gpvD2 = gen_lossless_bind_gpvD2[where co=True]

lemma gen_lossless_bind_gpv [simp]:
  "gen_lossless_gpv co \<I> (gpv \<bind> f) \<longleftrightarrow> gen_lossless_gpv co \<I> gpv \<and> (\<forall>x\<in>results_gpv \<I> gpv. gen_lossless_gpv co \<I> (f x))"
by(blast intro: gen_lossless_bind_gpvI dest: gen_lossless_bind_gpvD1 gen_lossless_bind_gpvD2)

lemmas lossless_bind_gpv = gen_lossless_bind_gpv[where co=False]
  and colossless_bind_gpv = gen_lossless_bind_gpv[where co=True]

context includes lifting_syntax begin

lemma rel_gpv''_lossless_gpvD1:
  assumes rel: "rel_gpv'' A C R gpv gpv'"
  and gpv: "lossless_gpv \<I> gpv"
  and [transfer_rule]: "rel_\<I> C R \<I> \<I>'"
  shows "lossless_gpv \<I>' gpv'"
using gpv rel
proof(induction arbitrary: gpv')
  case (lossless_gpv p)
  from lossless_gpv.prems obtain q where q: "gpv' = GPV q"
    and [transfer_rule]: "rel_spmf (rel_generat A C (R ===> rel_gpv'' A C R)) p q"
    by(cases gpv') auto
  show ?case
  proof(rule lossless_gpvI)
    have "lossless_spmf p = lossless_spmf q" by transfer_prover
    with lossless_gpv.hyps(1) q show "lossless_spmf (the_gpv gpv')" by simp

    fix out' c' input'
    assume IO': "IO out' c' \<in> set_spmf (the_gpv gpv')"
      and input': "input' \<in> responses_\<I> \<I>' out'"
    have "rel_set (rel_generat A C (R ===> rel_gpv'' A C R)) (set_spmf p) (set_spmf q)"
      by transfer_prover
    with IO' q obtain out c where IO: "IO out c \<in> set_spmf p"
      and [transfer_rule]: "C out out'" "(R ===> rel_gpv'' A C R) c c'"
      by(auto dest!: rel_setD2 elim: generat.rel_cases)
    have "rel_set R (responses_\<I> \<I> out) (responses_\<I> \<I>' out')" by transfer_prover
    moreover
    from this[THEN rel_setD2, OF input'] obtain input
      where [transfer_rule]: "R input input'" and input: "input \<in> responses_\<I> \<I> out" by blast
    have "rel_gpv'' A C R (c input) (c' input')" by transfer_prover
    ultimately show "lossless_gpv \<I>' (c' input')" using input IO by(auto intro: lossless_gpv.IH)
  qed
qed

lemma rel_gpv''_lossless_gpvD2:
  "\<lbrakk> rel_gpv'' A C R gpv gpv'; lossless_gpv \<I>' gpv'; rel_\<I> C R \<I> \<I>' \<rbrakk>
  \<Longrightarrow> lossless_gpv \<I> gpv"
using rel_gpv''_lossless_gpvD1[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" "R\<inverse>\<inverse>" gpv' gpv \<I>' \<I>]
by(simp add: rel_gpv''_conversep prod.rel_conversep rel_fun_eq_conversep)

lemma rel_gpv_lossless_gpvD1:
  "\<lbrakk> rel_gpv A C gpv gpv'; lossless_gpv \<I> gpv; rel_\<I> C (=) \<I> \<I>' \<rbrakk> \<Longrightarrow> lossless_gpv \<I>' gpv'"
using rel_gpv''_lossless_gpvD1[of A C "(=)" gpv gpv' \<I> \<I>'] by(simp add: rel_gpv_conv_rel_gpv'')

lemma rel_gpv_lossless_gpvD2:
  "\<lbrakk> rel_gpv A C gpv gpv'; lossless_gpv \<I>' gpv'; rel_\<I> C (=) \<I> \<I>' \<rbrakk>
  \<Longrightarrow> lossless_gpv \<I> gpv"
using rel_gpv_lossless_gpvD1[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" gpv' gpv \<I>' \<I>]
by(simp add: gpv.rel_conversep prod.rel_conversep rel_fun_eq_conversep)

lemma rel_gpv''_colossless_gpvD1:
  assumes rel: "rel_gpv'' A C R gpv gpv'"
  and gpv: "colossless_gpv \<I> gpv"
  and [transfer_rule]: "rel_\<I> C R \<I> \<I>'"
  shows "colossless_gpv \<I>' gpv'"
using gpv rel
proof(coinduction arbitrary: gpv gpv')
  case (colossless_gpv gpv gpv')
  note [transfer_rule] = \<open>rel_gpv'' A C R gpv gpv'\<close> the_gpv_parametric'
    and co = \<open>colossless_gpv \<I> gpv\<close>
  have "lossless_spmf (the_gpv gpv) = lossless_spmf (the_gpv gpv')" by transfer_prover
  with co have "?lossless_spmf" by(auto dest: colossless_gpv_lossless_spmfD)
  moreover have "?continuation"
  proof(intro strip disjI1)
    fix out' c' input'
    assume IO': "IO out' c' \<in> set_spmf (the_gpv gpv')"
      and input': "input' \<in> responses_\<I> \<I>' out'"
    have "rel_set (rel_generat A C (R ===> rel_gpv'' A C R)) (set_spmf (the_gpv gpv)) (set_spmf (the_gpv gpv'))"
      by transfer_prover
    with IO' obtain out c where IO: "IO out c \<in> set_spmf (the_gpv gpv)"
      and [transfer_rule]: "C out out'" "(R ===> rel_gpv'' A C R) c c'"
      by(auto dest!: rel_setD2 elim: generat.rel_cases)
    have "rel_set R (responses_\<I> \<I> out) (responses_\<I> \<I>' out')" by transfer_prover
    moreover 
    from this[THEN rel_setD2, OF input'] obtain input
      where [transfer_rule]: "R input input'" and input: "input \<in> responses_\<I> \<I> out" by blast
    have "rel_gpv'' A C R (c input) (c' input')" by transfer_prover
    ultimately show "\<exists>gpv gpv'. c' input' = gpv' \<and> colossless_gpv \<I> gpv \<and> rel_gpv'' A C R gpv gpv'"
      using input IO co by(auto dest: colossless_gpv_continuationD)
  qed
  ultimately show ?case ..
qed

lemma rel_gpv''_colossless_gpvD2:
  "\<lbrakk> rel_gpv'' A C R gpv gpv'; colossless_gpv \<I>' gpv'; rel_\<I> C R \<I> \<I>' \<rbrakk>
  \<Longrightarrow> colossless_gpv \<I> gpv"
using rel_gpv''_colossless_gpvD1[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" "R\<inverse>\<inverse>" gpv' gpv \<I>' \<I>]
by(simp add: rel_gpv''_conversep prod.rel_conversep rel_fun_eq_conversep)

lemma rel_gpv_colossless_gpvD1:
  "\<lbrakk> rel_gpv A C gpv gpv'; colossless_gpv \<I> gpv; rel_\<I> C (=) \<I> \<I>' \<rbrakk> \<Longrightarrow> colossless_gpv \<I>' gpv'"
using rel_gpv''_colossless_gpvD1[of A C "(=)" gpv gpv' \<I> \<I>'] by(simp add: rel_gpv_conv_rel_gpv'')

lemma rel_gpv_colossless_gpvD2:
  "\<lbrakk> rel_gpv A C gpv gpv'; colossless_gpv \<I>' gpv'; rel_\<I> C (=) \<I> \<I>' \<rbrakk>
  \<Longrightarrow> colossless_gpv \<I> gpv"
using rel_gpv_colossless_gpvD1[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" gpv' gpv \<I>' \<I>]
by(simp add: gpv.rel_conversep prod.rel_conversep rel_fun_eq_conversep)

lemma gen_lossless_gpv_parametric':
  "((=) ===> rel_\<I> C R ===> rel_gpv'' A C R ===> (=))
   gen_lossless_gpv gen_lossless_gpv"
proof(rule rel_funI; hypsubst)
  show "(rel_\<I> C R ===> rel_gpv'' A C R ===> (=)) (gen_lossless_gpv b) (gen_lossless_gpv b)" for b
    by(cases b)(auto intro!: rel_funI dest: rel_gpv''_colossless_gpvD1 rel_gpv''_colossless_gpvD2 rel_gpv''_lossless_gpvD1 rel_gpv''_lossless_gpvD2)
qed

lemma gen_lossless_gpv_parametric [transfer_rule]:
  "((=) ===> rel_\<I> C (=) ===> rel_gpv A C ===> (=))
   gen_lossless_gpv gen_lossless_gpv"
proof(rule rel_funI; hypsubst)
  show "(rel_\<I> C (=) ===> rel_gpv A C ===> (=)) (gen_lossless_gpv b) (gen_lossless_gpv b)" for b
    by(cases b)(auto intro!: rel_funI dest: rel_gpv_colossless_gpvD1 rel_gpv_colossless_gpvD2 rel_gpv_lossless_gpvD1 rel_gpv_lossless_gpvD2)
qed

end

lemma gen_lossless_gpv_map_full [simp]:
  "gen_lossless_gpv b \<I>_full (map_gpv f g gpv) = gen_lossless_gpv b \<I>_full gpv"
  (is "?lhs = ?rhs")
proof(cases "b = True")
  case True
  show "?lhs = ?rhs"
  proof
    show ?rhs if ?lhs using that unfolding True
      by(coinduction arbitrary: gpv)(auto 4 3 dest: colossless_gpvD simp add: gpv.map_sel intro!: rev_image_eqI)
    show ?lhs if ?rhs using that unfolding True
      by(coinduction arbitrary: gpv)(auto 4 4 dest: colossless_gpvD simp add: gpv.map_sel intro!: rev_image_eqI)
  qed
next
  case False
  hence False: "b = False" by simp
  show "?lhs = ?rhs"
  proof
    show ?rhs if ?lhs using that unfolding False
      apply(induction gpv'\<equiv>"map_gpv f g gpv" arbitrary: gpv)
      subgoal for p gpv by(cases gpv)(rule lossless_gpvI; fastforce intro: rev_image_eqI)
      done
    show ?lhs if ?rhs using that unfolding False
      by induction(auto 4 4 intro: lossless_gpvI)
  qed
qed

lemma gen_lossless_gpv_map_id [simp]:
  "gen_lossless_gpv b \<I> (map_gpv f id gpv) = gen_lossless_gpv b \<I> gpv"
  using gen_lossless_gpv_parametric[of "BNF_Def.Grp UNIV id" "BNF_Def.Grp UNIV f"] unfolding gpv.rel_Grp
  by(simp add: rel_fun_def eq_alt[symmetric] rel_\<I>_eq)(auto simp add: Grp_def)

lemma results_gpv_try_gpv [simp]:
  "results_gpv \<I> (TRY gpv ELSE gpv') = 
   results_gpv \<I> gpv \<union> (if colossless_gpv \<I> gpv then {} else results_gpv \<I> gpv')"
  (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
  proof(induction gpv''\<equiv>"try_gpv gpv gpv'" arbitrary: gpv)
    case Pure thus ?case
      by(auto split: if_split_asm intro: results_gpv.Pure dest: colossless_gpv_lossless_spmfD)
  next
    case (IO out c input)
    then show ?case
      apply(auto dest: colossless_gpv_lossless_spmfD split: if_split_asm)
      apply(force intro: results_gpv.IO dest: colossless_gpv_continuationD split: if_split_asm)+
      done
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then consider (left) "x \<in> results_gpv \<I> gpv" | (right) "\<not> colossless_gpv \<I> gpv" "x \<in> results_gpv \<I> gpv'"
    by(auto split: if_split_asm)
  thus "x \<in> ?lhs"
  proof cases
    case left
    thus ?thesis 
      by(induction)(auto 4 4 intro: results_gpv.intros rev_image_eqI split del: if_split)
  next
    case right
    from right(1) show ?thesis
    proof(rule contrapos_np)
      assume "x \<notin> ?lhs"
      with right(2) show "colossless_gpv \<I> gpv"
      proof(coinduction arbitrary: gpv)
        case (colossless_gpv gpv)
        then have ?lossless_spmf
          apply(rewrite in asm try_gpv.code)
          apply(rule ccontr)
          apply(erule results_gpv.cases)
          apply(fastforce simp add: image_Un image_image generat.map_comp o_def)+
          done
        moreover have "?continuation" using colossless_gpv
          by(auto 4 4 split del: if_split simp add: image_Un image_image generat.map_comp o_def intro: rev_image_eqI results_gpv.IO)
        ultimately show ?case ..
      qed
    qed
  qed
qed

lemma results'_gpv_try_gpv [simp]:
  "results'_gpv (TRY gpv ELSE gpv') = 
   results'_gpv gpv \<union> (if colossless_gpv \<I>_full gpv then {} else results'_gpv gpv')"
by(simp add: results_gpv_\<I>_full[symmetric])

lemma outs'_gpv_try_gpv [simp]:
  "outs'_gpv (TRY gpv ELSE gpv') =
   outs'_gpv gpv \<union> (if colossless_gpv \<I>_full gpv then {} else outs'_gpv gpv')"
  (is "?lhs = ?rhs")
proof(intro set_eqI iffI)
  show "x \<in> ?rhs" if "x \<in> ?lhs" for x using that
  proof(induction gpv''\<equiv>"try_gpv gpv gpv'" arbitrary: gpv)
    case Out thus ?case
      by(auto 4 3 simp add: generat.map_comp o_def elim!: generat.set_cases(2) intro: outs'_gpv_Out split: if_split_asm dest: colossless_gpv_lossless_spmfD)
  next
    case (Cont generat c input)
    then show ?case
      apply(auto dest: colossless_gpv_lossless_spmfD split: if_split_asm elim!: generat.set_cases(3))
      apply(auto 4 3 dest: colossless_gpv_continuationD split: if_split_asm intro: outs'_gpv_Cont elim!: meta_allE meta_impE[OF _ refl])+
      done
  qed
next
  fix x
  assume "x \<in> ?rhs"
  then consider (left) "x \<in> outs'_gpv gpv" | (right) "\<not> colossless_gpv \<I>_full gpv" "x \<in> outs'_gpv gpv'"
    by(auto split: if_split_asm)
  thus "x \<in> ?lhs"
  proof cases
    case left
    thus ?thesis 
      by(induction)(auto elim!: generat.set_cases(2,3) intro: outs'_gpvI intro!: rev_image_eqI split del: if_split simp add: image_Un image_image generat.map_comp o_def)
  next
    case right
    from right(1) show ?thesis
    proof(rule contrapos_np)
      assume "x \<notin> ?lhs"
      with right(2) show "colossless_gpv \<I>_full gpv"
      proof(coinduction arbitrary: gpv)
        case (colossless_gpv gpv)
        then have ?lossless_spmf
          apply(rewrite in asm try_gpv.code)
          apply(erule contrapos_np)
          apply(erule gpv.set_cases)
          apply(auto 4 3 simp add: image_Un image_image generat.map_comp o_def generat.set_map in_set_spmf[symmetric] bind_UNION generat.map_id[unfolded id_def] elim!: generat.set_cases)
          done
        moreover have "?continuation" using colossless_gpv
          by(auto simp add: image_Un image_image generat.map_comp o_def split del: if_split intro!: rev_image_eqI intro: outs'_gpv_Cont)
        ultimately show ?case ..
      qed
    qed
  qed
qed

lemma pred_gpv_try [simp]:
  "pred_gpv P Q (try_gpv gpv gpv') = (pred_gpv P Q gpv \<and> (\<not> colossless_gpv \<I>_full gpv \<longrightarrow> pred_gpv P Q gpv'))"
by(auto simp add: pred_gpv_def)

lemma lossless_WT_gpv_induct [consumes 2, case_names lossless_gpv]:
  assumes lossless: "lossless_gpv \<I> gpv"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  and step: "\<And>p. \<lbrakk>
       lossless_spmf p;
       \<And>out c. IO out c \<in> set_spmf p \<Longrightarrow> out \<in> outs_\<I> \<I>;
       \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; out \<in> outs_\<I> \<I> \<Longrightarrow> input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> lossless_gpv \<I> (c input);
       \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; out \<in> outs_\<I> \<I> \<Longrightarrow> input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> \<I> \<turnstile>g c input \<surd>;
       \<And>out c input. \<lbrakk>IO out c \<in> set_spmf p; out \<in> outs_\<I> \<I> \<Longrightarrow> input \<in> responses_\<I> \<I> out\<rbrakk> \<Longrightarrow> P (c input)\<rbrakk>
      \<Longrightarrow> P (GPV p)"
  shows "P gpv"
using lossless WT
apply(induction)
apply(erule step)
apply(auto elim: WT_gpvD simp add: WT_gpv_simps)
done

lemma lossless_gpv_induct_strong [consumes 1, case_names lossless_gpv]:
  assumes gpv: "lossless_gpv \<I> gpv"
  and step:
  "\<And>p. \<lbrakk> lossless_spmf p;
          \<And>gpv. gpv \<in> sub_gpvs \<I> (GPV p) \<Longrightarrow> lossless_gpv \<I> gpv;
          \<And>gpv. gpv \<in> sub_gpvs \<I> (GPV p) \<Longrightarrow> P gpv \<rbrakk>
       \<Longrightarrow> P (GPV p)"
  shows "P gpv"
proof -
  define gpv' where "gpv' = gpv"
  then have "gpv' \<in> insert gpv (sub_gpvs \<I> gpv)" by simp
  with gpv have "lossless_gpv \<I> gpv' \<and> P gpv'"
  proof(induction arbitrary: gpv')
    case (lossless_gpv p)
    from \<open>gpv' \<in> insert (GPV p) _\<close> show ?case
    proof(rule insertE)
      assume "gpv' = GPV p"
      moreover have "lossless_gpv \<I> (GPV p)"
        by(auto 4 3 intro: lossless_gpvI lossless_gpv.hyps)
      moreover have "P (GPV p)" using lossless_gpv.hyps(1)
        by(rule step)(fastforce elim: sub_gpvs.cases lossless_gpv.IH[THEN conjunct1] lossless_gpv.IH[THEN conjunct2])+
      ultimately show ?case by simp
    qed(fastforce elim: sub_gpvs.cases lossless_gpv.IH[THEN conjunct1] lossless_gpv.IH[THEN conjunct2])
  qed
  thus ?thesis by(simp add: gpv'_def)
qed

lemma lossless_sub_gpvsI:
  assumes spmf: "lossless_spmf (the_gpv gpv)"
  and sub: "\<And>gpv'. gpv' \<in> sub_gpvs \<I> gpv \<Longrightarrow> lossless_gpv \<I> gpv'"
  shows "lossless_gpv \<I> gpv"
using spmf by(rule lossless_gpvI)(rule sub[OF sub_gpvs.base])

lemma lossless_sub_gpvsD:
  assumes "lossless_gpv \<I> gpv" "gpv' \<in> sub_gpvs \<I> gpv"
  shows "lossless_gpv \<I> gpv'"
using assms(2,1) by(induction)(auto dest: lossless_gpvD)

lemma lossless_WT_gpv_induct_strong [consumes 2, case_names lossless_gpv]:
  assumes lossless: "lossless_gpv \<I> gpv"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  and step: "\<And>p. \<lbrakk> lossless_spmf p;
       \<And>out c. IO out c \<in> set_spmf p \<Longrightarrow> out \<in> outs_\<I> \<I>;
       \<And>gpv. gpv \<in> sub_gpvs \<I> (GPV p) \<Longrightarrow> lossless_gpv \<I> gpv;
       \<And>gpv. gpv \<in> sub_gpvs \<I> (GPV p) \<Longrightarrow> \<I> \<turnstile>g gpv \<surd>;
       \<And>gpv. gpv \<in> sub_gpvs \<I> (GPV p) \<Longrightarrow> P gpv \<rbrakk>
      \<Longrightarrow> P (GPV p)"
  shows "P gpv"
using lossless WT
apply(induction rule: lossless_gpv_induct_strong)
apply(erule step)
apply(auto elim: WT_gpvD dest: WT_sub_gpvsD)
done

lemma try_gpv_gen_lossless: \<comment> \<open>TODO: generalise to arbitrary typings ?\<close>
  "gen_lossless_gpv b \<I>_full gpv \<Longrightarrow> (TRY gpv ELSE gpv') = gpv"
proof(coinduction arbitrary: gpv)
  case (Eq_gpv gpv)
  from Eq_gpv[THEN gen_lossless_gpv_lossless_spmfD]
  have eq: "the_gpv gpv = (TRY the_gpv gpv ELSE the_gpv gpv')" by(simp)
  show ?case
    by(subst eq)(auto simp add: spmf_rel_map generat.rel_map[abs_def] intro!: rel_spmf_try_spmf rel_spmf_reflI rel_generat_reflI elim!: generat.set_cases gen_lossless_gpv_continuationD[OF Eq_gpv] simp add: Eq_gpv[THEN gen_lossless_gpv_lossless_spmfD])
qed

\<comment> \<open>We instantiate the parameter @{term b} such that it can be used as a conditional simp rule.\<close>
lemmas try_gpv_lossless [simp] = try_gpv_gen_lossless[where b=False]
  and try_gpv_colossless [simp] = try_gpv_gen_lossless[where b=True]

lemma try_gpv_bind_gen_lossless: \<comment> \<open>TODO: generalise to arbitrary typings?\<close>
  "gen_lossless_gpv b \<I>_full gpv \<Longrightarrow> TRY bind_gpv gpv f ELSE gpv' = bind_gpv gpv (\<lambda>x. TRY f x ELSE gpv')"
proof(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  case (Eq_gpv gpv)
  note [simp] = spmf_rel_map generat.rel_map map_spmf_bind_spmf
    and [intro!] = rel_spmf_reflI rel_generat_reflI rel_funI
  show ?case using gen_lossless_gpvD[OF Eq_gpv]
    by(auto 4 3 simp del: bind_gpv_sel' simp add: bind_gpv.sel try_spmf_bind_spmf_lossless split: generat.split intro!: rel_spmf_bind_reflI rel_spmf_try_spmf)
qed

\<comment> \<open>We instantiate the parameter @{term b} such that it can be used as a conditional simp rule.\<close>
lemmas try_gpv_bind_lossless = try_gpv_bind_gen_lossless[where b=False]
  and try_gpv_bind_colossless = try_gpv_bind_gen_lossless[where b=True]

lemma try_gpv_cong:
  "\<lbrakk> gpv = gpv''; \<not> colossless_gpv \<I>_full gpv'' \<Longrightarrow> gpv' = gpv''' \<rbrakk>
  \<Longrightarrow> try_gpv gpv gpv' = try_gpv gpv'' gpv'''"
by(cases "colossless_gpv \<I>_full gpv''") simp_all

(* lemma try_gpv_bind_colossless2:
  "colossless_gpv \<I>_full gpv' \<Longrightarrow> try_gpv (bind_gpv gpv f) gpv' = try_gpv (bind_gpv gpv (\<lambda>x. try_gpv (f x) gpv')) gpv'"
apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
apply(simp add: spmf_rel_map bind_gpv_sel del: bind_gpv_sel')
apply(rule rel_spmf_try_spmf)
 apply(simp add: spmf_rel_map)
 apply(rule rel_spmf_bind_reflI)
 apply(simp split: generat.split)
 apply(rule conjI; clarsimp)
 apply(simp add: spmf_rel_map generat.map_comp o_def generat.rel_map rel_fun_def)
 apply(subst map_try_spmf[symmetric])
 *)

subsection \<open>Sequencing with failure handling included\<close>

definition catch_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a option, 'out, 'in) gpv"
where "catch_gpv gpv = TRY map_gpv Some id gpv ELSE Done None"

lemma catch_gpv_Done [simp]: "catch_gpv (Done x) = Done (Some x)"
by(simp add: catch_gpv_def)

lemma catch_gpv_Fail [simp]: "catch_gpv Fail = Done None"
by(simp add: catch_gpv_def)

lemma catch_gpv_Pause [simp]: "catch_gpv (Pause out rpv) = Pause out (\<lambda>input. catch_gpv (rpv input))"
by(simp add: catch_gpv_def)

lemma catch_gpv_lift_spmf [simp]: "catch_gpv (lift_spmf p) = lift_spmf (spmf_of_pmf p)"
by(rule gpv.expand)(auto simp add: catch_gpv_def spmf_of_pmf_def map_lift_spmf try_spmf_def o_def map_pmf_def bind_assoc_pmf bind_return_pmf intro!: bind_pmf_cong[OF refl] split: option.split)

lemma catch_gpv_assert [simp]: "catch_gpv (assert_gpv b) = Done (assert_option b)"
by(cases b) simp_all

lemma catch_gpv_sel [simp]:
  "the_gpv (catch_gpv gpv) = 
   TRY map_spmf (map_generat Some id (\<lambda>rpv input. catch_gpv (rpv input))) (the_gpv gpv)
   ELSE return_spmf (Pure None)"
by(simp add: catch_gpv_def gpv.map_sel spmf.map_comp o_def generat.map_comp map_try_spmf id_def)

lemma catch_gpv_bind_gpv: "catch_gpv (bind_gpv gpv f) = bind_gpv (catch_gpv gpv) (\<lambda>x. case x of None \<Rightarrow> Done None | Some x' \<Rightarrow> catch_gpv (f x'))"
  using [[show_variants]]
  apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
  apply(clarsimp simp add: map_bind_pmf bind_gpv.sel spmf.map_comp o_def[abs_def] map_bind_spmf generat.map_comp simp del: bind_gpv_sel')
  apply(subst bind_spmf_def)
  apply(subst try_spmf_bind_pmf)
  apply(subst (2) try_spmf_def)
  apply(subst bind_spmf_pmf_assoc)
  apply(simp add: bind_map_pmf)
  apply(rule rel_pmf_bind_reflI)
  apply(auto split!: option.split generat.split simp add: spmf_rel_map spmf.map_comp o_def generat.map_comp id_def[symmetric] generat.map_id rel_spmf_reflI generat.rel_refl refl rel_fun_def)
  done

context includes lifting_syntax begin
lemma catch_gpv_parametric [transfer_rule]:
  "(rel_gpv A C ===> rel_gpv (rel_option A) C) catch_gpv catch_gpv"
unfolding catch_gpv_def by transfer_prover

lemma catch_gpv_parametric':
  notes [transfer_rule] = try_gpv_parametric' map_gpv_parametric' Done_parametric'
  shows "(rel_gpv'' A C R ===> rel_gpv'' (rel_option A) C R) catch_gpv catch_gpv"
unfolding catch_gpv_def by transfer_prover
end

lemma catch_gpv_map': "catch_gpv (map_gpv' f g h gpv) = map_gpv' (map_option f) g h (catch_gpv gpv)"
by(simp add: catch_gpv_def map'_try_gpv map_gpv_conv_map_gpv' map_gpv'_comp o_def)

lemma catch_gpv_map: "catch_gpv (map_gpv f g gpv) = map_gpv (map_option f) g (catch_gpv gpv)"
  by(simp add: map_gpv_conv_map_gpv' catch_gpv_map')

lemma colossless_gpv_catch_gpv [simp]: "colossless_gpv \<I>_full (catch_gpv gpv)"
by(coinduction arbitrary: gpv) auto

lemma colosless_gpv_catch_gpv_conv_map:
  "colossless_gpv \<I>_full gpv \<Longrightarrow> catch_gpv gpv = map_gpv Some id gpv"
  apply(coinduction arbitrary: gpv)
  apply(frule colossless_gpv_lossless_spmfD)
  apply(auto simp add: spmf_rel_map gpv.map_sel generat.rel_map intro!: rel_spmf_reflI generat.rel_refl_strong rel_funI elim!: colossless_gpv_continuationD generat.set_cases)
  done

lemma catch_gpv_catch_gpv [simp]: "catch_gpv (catch_gpv gpv) = map_gpv Some id (catch_gpv gpv)"
  by(simp add: colosless_gpv_catch_gpv_conv_map)

lemma case_map_resumption: (* Move to Resumption *)
  "case_resumption done pause (map_resumption f g r) = 
   case_resumption (done \<circ> map_option f) (\<lambda>out c. pause (g out) (map_resumption f g \<circ> c)) r" 
by(cases r) simp_all

lemma catch_gpv_lift_resumption [simp]: "catch_gpv (lift_resumption r) = lift_resumption (map_resumption Some id r)"
  apply(coinduction arbitrary: r)
  apply(auto simp add: lift_resumption.sel case_map_resumption split: resumption.split option.split)
  oops (* TODO: We'd need a catch_resumption for this *)

lemma results_gpv_catch_gpv:
  "results_gpv \<I> (catch_gpv gpv) = Some ` results_gpv \<I> gpv \<union> (if colossless_gpv \<I> gpv then {} else {None})"
  by(simp add: catch_gpv_def)

lemma Some_in_results_gpv_catch_gpv [simp]:
  "Some x \<in> results_gpv \<I> (catch_gpv gpv) \<longleftrightarrow> x \<in> results_gpv \<I> gpv"
  by(auto simp add: results_gpv_catch_gpv)

lemma None_in_results_gpv_catch_gpv [simp]:
  "None \<in> results_gpv \<I> (catch_gpv gpv) \<longleftrightarrow> \<not> colossless_gpv \<I> gpv"
  by(auto simp add: results_gpv_catch_gpv)

lemma results'_gpv_catch_gpv:
  "results'_gpv (catch_gpv gpv) = Some ` results'_gpv gpv \<union> (if colossless_gpv \<I>_full gpv then {} else {None})"
  by(simp add: results_gpv_\<I>_full[symmetric] results_gpv_catch_gpv)

lemma Some_in_results'_gpv_catch_gpv [simp]:
  "Some x \<in> results'_gpv (catch_gpv gpv) \<longleftrightarrow> x \<in> results'_gpv gpv"
  by(simp add: results_gpv_\<I>_full[symmetric])

lemma None_in_results'_gpv_catch_gpv [simp]:
  "None \<in> results'_gpv (catch_gpv gpv) \<longleftrightarrow> \<not> colossless_gpv \<I>_full gpv"
  by(simp add: results_gpv_\<I>_full[symmetric])

lemma results'_gpv_catch_gpvE:
  assumes "x \<in> results'_gpv (catch_gpv gpv)"
  obtains (Some) x'
  where "x = Some x'" "x' \<in> results'_gpv gpv"
  | (colossless) "x = None" "\<not> colossless_gpv \<I>_full gpv"
  using assms by(auto simp add: results'_gpv_catch_gpv split: if_split_asm)

lemma outs'_gpv_catch_gpv [simp]: "outs'_gpv (catch_gpv gpv) = outs'_gpv gpv"
  by(simp add: catch_gpv_def)

lemma pred_gpv_catch_gpv [simp]: "pred_gpv (pred_option P) Q (catch_gpv gpv) = pred_gpv P Q gpv"
  by(simp add: pred_gpv_def results'_gpv_catch_gpv)

abbreviation bind_gpv' :: "('a, 'call, 'ret) gpv \<Rightarrow> ('a option \<Rightarrow> ('b, 'call, 'ret) gpv) \<Rightarrow> ('b, 'call, 'ret) gpv"
where "bind_gpv' gpv \<equiv> bind_gpv (catch_gpv gpv)"

(* lemma bind_gpv'_sel [simp]:
  "the_gpv (bind_gpv' gpv f) =
   bind_pmf (the_gpv gpv) (\<lambda>x. case x of
     None \<Rightarrow> the_gpv (f None)
   | Some (Pure x) \<Rightarrow> the_gpv (f (Some x))
   | Some (IO out rpv) \<Rightarrow> return_spmf (IO out (\<lambda>input. bind_gpv' (rpv input) f)))"
by(auto simp add: bind_gpv'_def bind_map_spmf try_spmf_def bind_spmf_pmf_assoc bind_map_pmf gpv.map_sel intro!: bind_pmf_cong[OF refl] split: option.split generat.split)
 *)
  
lemma bind_gpv'_assoc [simp]: "bind_gpv' (bind_gpv' gpv f) g = bind_gpv' gpv (\<lambda>x. bind_gpv' (f x) g)"
by(simp add: catch_gpv_bind_gpv bind_map_gpv o_def bind_gpv_assoc)

lemma bind_gpv'_bind_gpv: "bind_gpv' (bind_gpv gpv f) g = bind_gpv' gpv (case_option (g None) (\<lambda>y. bind_gpv' (f y) g))"
  by(clarsimp simp add: catch_gpv_bind_gpv bind_gpv_assoc intro!: bind_gpv_cong[OF refl] split: option.split)

lemma bind_gpv'_cong:
  "\<lbrakk> gpv = gpv'; \<And>x. x \<in> Some ` results'_gpv gpv' \<or> (\<not> colossless_gpv \<I>_full gpv \<and> x = None) \<Longrightarrow> f x = f' x \<rbrakk>
  \<Longrightarrow> bind_gpv' gpv f = bind_gpv' gpv' f'"
by(auto elim: results'_gpv_catch_gpvE split: if_split_asm intro!: bind_gpv_cong[OF refl])

lemma bind_gpv'_cong2:
  "\<lbrakk> gpv = gpv'; \<And>x. x \<in> results'_gpv gpv' \<Longrightarrow> f (Some x) = f' (Some x); \<not> colossless_gpv \<I>_full gpv \<Longrightarrow> f None = f' None \<rbrakk>
  \<Longrightarrow> bind_gpv' gpv f = bind_gpv' gpv' f'"
by(rule bind_gpv'_cong) auto

subsection \<open>Inlining\<close>

lemma gpv_coinduct_bind [consumes 1, case_names Eq_gpv]:
  fixes gpv gpv' :: "('a, 'call, 'ret) gpv"
  assumes *: "R gpv gpv'"
  and step: "\<And>gpv gpv'. R gpv gpv' 
    \<Longrightarrow> rel_spmf (rel_generat (=) (=) (rel_fun (=) (\<lambda>gpv gpv'. R gpv gpv' \<or> gpv = gpv' \<or> 
      (\<exists>gpv2 :: ('b, 'call, 'ret) gpv. \<exists>gpv2' :: ('c, 'call, 'ret) gpv. \<exists>f f'. gpv = bind_gpv gpv2 f \<and> gpv' = bind_gpv gpv2' f' \<and> 
        rel_gpv (\<lambda>x y. R (f x) (f' y)) (=) gpv2 gpv2'))))
      (the_gpv gpv) (the_gpv gpv')"
  shows "gpv = gpv'"
proof -
  fix x y
  define gpv1 :: "('b, 'call, 'ret) gpv"
    and f :: "'b \<Rightarrow> ('a, 'call, 'ret) gpv"
    and gpv1' :: "('c, 'call, 'ret) gpv"
    and f' :: "'c \<Rightarrow> ('a, 'call, 'ret) gpv"
    where "gpv1 = Done x"
      and "f = (\<lambda>_. gpv)"
      and "gpv1' = Done y"
      and "f' = (\<lambda>_. gpv')"
  from * have "rel_gpv (\<lambda>x y. R (f x) (f' y)) (=) gpv1 gpv1'"
    by(simp add: gpv1_def gpv1'_def f_def f'_def)
  then have "gpv1 \<bind> f = gpv1' \<bind> f'"
  proof(coinduction arbitrary: gpv1 gpv1' f f' rule: gpv.coinduct_strong)
    case (Eq_gpv gpv1 gpv1' f f')
    from Eq_gpv[simplified gpv.rel_sel] show ?case unfolding bind_gpv.sel spmf_rel_map
      apply(rule rel_spmf_bindI)
      subgoal for generat generat'
        apply(cases generat generat' rule: generat.exhaust[case_product generat.exhaust]; clarsimp simp add: o_def spmf_rel_map generat.rel_map)
        subgoal premises Pure for x y
          using step[OF \<open>R (f x) (f' y)\<close>] apply -
          apply(assumption | rule rel_spmf_mono rel_generat_mono rel_fun_mono refl)+
          apply(fastforce intro: exI[where x="Done _"])+
          done
        subgoal by(fastforce simp add: rel_fun_def)
        done
      done
  qed
  thus ?thesis by(simp add: gpv1_def gpv1'_def f_def f'_def)
qed

text \<open>
  Inlining one gpv into another. This may throw out arbitrarily many
  interactions between the two gpvs if the inlined one does not call its callee.
  So we define it as the coiteration of a least-fixpoint search operator.
\<close>

context
  fixes callee :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call', 'ret') gpv"
  notes [[function_internals]]
begin

partial_function (spmf) inline1
  :: "('a, 'call, 'ret) gpv \<Rightarrow> 's
  \<Rightarrow> ('a \<times> 's + 'call' \<times> ('ret \<times> 's, 'call', 'ret') rpv \<times> ('a, 'call, 'ret) rpv) spmf"
where
  "inline1 gpv s =
   the_gpv gpv \<bind>
   case_generat (\<lambda>x. return_spmf (Inl (x, s)))
     (\<lambda>out rpv. the_gpv (callee s out) \<bind>
         case_generat (\<lambda>(x, y). inline1 (rpv x) y)
          (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv))))"

lemma inline1_unfold:
  "inline1 gpv s =
   the_gpv gpv \<bind>
   case_generat (\<lambda>x. return_spmf (Inl (x, s)))
     (\<lambda>out rpv. the_gpv (callee s out) \<bind>
         case_generat (\<lambda>(x, y). inline1 (rpv x) y)
          (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv))))"
by(fact inline1.simps)

lemma inline1_fixp_induct [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>inline1'. P (\<lambda>gpv s. inline1' (gpv, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>inline1'. P inline1' \<Longrightarrow> P (\<lambda>gpv s. the_gpv gpv \<bind> case_generat (\<lambda>x. return_spmf (Inl (x, s))) (\<lambda>out rpv. the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1' (rpv x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv)))))"
  shows "P inline1"
using assms by(rule inline1.fixp_induct[unfolded curry_conv[abs_def]])

lemma inline1_fixp_induct_strong [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>inline1'. P (\<lambda>gpv s. inline1' (gpv, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>inline1'. \<lbrakk> \<And>gpv s. ord_spmf (=) (inline1' gpv s) (inline1 gpv s); P inline1' \<rbrakk>
    \<Longrightarrow> P (\<lambda>gpv s. the_gpv gpv \<bind> case_generat (\<lambda>x. return_spmf (Inl (x, s))) (\<lambda>out rpv. the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1' (rpv x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv)))))"
  shows "P inline1"
using assms by(rule spmf.fixp_strong_induct_uc[where P="\<lambda>f. P (curry f)" and U=case_prod and C=curry, OF inline1.mono inline1_def, simplified curry_case_prod, simplified curry_conv[abs_def] fun_ord_def split_paired_All prod.case case_prod_eta, OF refl]) blast+

lemma inline1_fixp_induct_strong2 [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>inline1'. P (\<lambda>gpv s. inline1' (gpv, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>inline1'. 
    \<lbrakk> \<And>gpv s. ord_spmf (=) (inline1' gpv s) (inline1 gpv s); 
      \<And>gpv s. ord_spmf (=) (inline1' gpv s) (the_gpv gpv \<bind> case_generat (\<lambda>x. return_spmf (Inl (x, s))) (\<lambda>out rpv. the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1' (rpv x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv)))));
      P inline1' \<rbrakk>
    \<Longrightarrow> P (\<lambda>gpv s. the_gpv gpv \<bind> case_generat (\<lambda>x. return_spmf (Inl (x, s))) (\<lambda>out rpv. the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1' (rpv x) y) (\<lambda>out rpv'. return_spmf (Inr (out, rpv', rpv)))))"
  shows "P inline1"
using assms
by(rule spmf.fixp_induct_strong2_uc[where P="\<lambda>f. P (curry f)" and U=case_prod and C=curry, OF inline1.mono inline1_def, simplified curry_case_prod, simplified curry_conv[abs_def] fun_ord_def split_paired_All prod.case case_prod_eta, OF refl]) blast+

text \<open>
  Iterate @{const inline1} over all interactions. We'd like to use @{const bind_gpv} before
  the recursive call, but primcorec does not support this. So we emulate @{const bind_gpv}
  by effectively defining two mutually recursive functions (sum type in the argument)
  where the second is exactly @{const bind_gpv} specialised to call \<open>inline\<close> in the bind.
\<close>

primcorec inline_aux
  :: "('a, 'call, 'ret) gpv \<times> 's + ('ret \<Rightarrow> ('a, 'call, 'ret) gpv) \<times> ('ret \<times> 's, 'call', 'ret') gpv
  \<Rightarrow> ('a \<times> 's, 'call', 'ret') gpv"
where
  "\<And>state. the_gpv (inline_aux state) =
  (case state of Inl (c, s) \<Rightarrow> map_spmf (\<lambda>result. 
     case result of Inl (x, s) \<Rightarrow> Pure (x, s)
     | Inr (out, oracle, rpv) \<Rightarrow> IO out (\<lambda>input. inline_aux (Inr (rpv, oracle input)))) (inline1 c s)
  | Inr (rpv, c) \<Rightarrow>  
    map_spmf (\<lambda>result. 
       case result of Inl (Inl (x, s)) \<Rightarrow> Pure (x, s)
       | Inl (Inr (out, oracle, rpv)) \<Rightarrow> IO out (\<lambda>input. inline_aux (Inr (rpv, oracle input)))
       | Inr (out, c) \<Rightarrow> IO out (\<lambda>input. inline_aux (Inr (rpv, c input))))
  (bind_spmf (the_gpv c) (\<lambda>generat. case generat of Pure (x, s') \<Rightarrow> (map_spmf Inl (inline1 (rpv x) s'))
     | IO out c \<Rightarrow> return_spmf (Inr (out, c)))
     ))"

declare inline_aux.simps[simp del]

definition inline :: "('a, 'call, 'ret) gpv \<Rightarrow> 's \<Rightarrow> ('a \<times> 's, 'call', 'ret') gpv"
where "inline c s = inline_aux (Inl (c, s))"

lemma inline_aux_Inr:
  "inline_aux (Inr (rpv, oracl)) = bind_gpv oracl (\<lambda>(x, s). inline (rpv x) s)"
unfolding inline_def
apply(coinduction arbitrary: oracl rule: gpv.coinduct_strong)
apply(simp add: inline_aux.sel bind_gpv.sel spmf_rel_map del: bind_gpv_sel')
apply(rule rel_spmf_bindI[where R="(=)"])
apply(auto simp add: spmf_rel_map inline_aux.sel rel_spmf_reflI generat.rel_map generat.rel_refl rel_fun_def split: generat.split)
done

lemma inline_sel:
  "the_gpv (inline c s) = 
   map_spmf (\<lambda>result. case result of Inl xs \<Rightarrow> Pure xs
                       | Inr (out, oracle, rpv) \<Rightarrow> IO out (\<lambda>input. bind_gpv (oracle input) (\<lambda>(x, s'). inline (rpv x) s'))) (inline1 c s)"
by(simp add: inline_def inline_aux.sel inline_aux_Inr cong del: sum.case_cong)

lemma inline1_Fail [simp]: "inline1 Fail s = return_pmf None"
by(rewrite inline1.simps) simp

lemma inline_Fail [simp]: "inline Fail s = Fail"
by(rule gpv.expand)(simp add: inline_sel)

lemma inline1_Done [simp]: "inline1 (Done x) s = return_spmf (Inl (x, s))"
by(rewrite inline1.simps) simp

lemma inline_Done [simp]: "inline (Done x) s = Done (x, s)"
by(rule gpv.expand)(simp add: inline_sel)

lemma inline1_lift_spmf [simp]: "inline1 (lift_spmf p) s = map_spmf (\<lambda>x. Inl (x, s)) p"
by(rewrite inline1.simps)(simp add: bind_map_spmf o_def map_spmf_conv_bind_spmf)

lemma inline_lift_spmf [simp]: "inline (lift_spmf p) s = lift_spmf (map_spmf (\<lambda>x. (x, s)) p)"
by(rule gpv.expand)(simp add: inline_sel spmf.map_comp o_def)

lemma inline1_Pause:
  "inline1 (Pause out c) s = 
  the_gpv (callee s out) \<bind> (\<lambda>react. case react of Pure (x, s') \<Rightarrow> inline1 (c x) s' | IO out' c' \<Rightarrow> return_spmf (Inr (out', c', c)))"
by(rewrite inline1.simps) simp

lemma inline_Pause [simp]:
  "inline (Pause out c) s = callee s out \<bind> (\<lambda>(x, s'). inline (c x) s')"
by(rule gpv.expand)(auto simp add: inline_sel inline1_Pause map_spmf_bind_spmf bind_gpv.sel o_def[abs_def] spmf.map_comp generat.map_comp id_def generat.map_id[unfolded id_def] simp del: bind_gpv_sel' intro!: bind_spmf_cong[OF refl] split: generat.split)

lemma inline1_bind_gpv:
  fixes gpv f s
  defines [simp]: "inline11 \<equiv> inline1" and [simp]: "inline12 \<equiv> inline1" and [simp]: "inline13 \<equiv> inline1"
  shows "inline11 (bind_gpv gpv f) s = bind_spmf (inline12 gpv s) 
    (\<lambda>res. case res of Inl (x, s') \<Rightarrow> inline13 (f x) s' | Inr (out, rpv', rpv) \<Rightarrow> return_spmf (Inr (out, rpv', bind_rpv rpv f)))"
  (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  note [intro!] = ord_spmf_bind_reflI and [split] = generat.split
  show "ord_spmf (=) ?lhs ?rhs" unfolding inline11_def
  proof(induction arbitrary: gpv s f rule: inline1_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline1')
    show ?case unfolding inline12_def
      apply(rewrite inline1.simps; clarsimp simp add: bind_rpv_def)
      apply(rule conjI; clarsimp)
      subgoal premises Pure for x
        apply(rewrite inline1.simps; clarsimp)
        subgoal for out c ret s' using step.IH[of "Done x" "\<lambda>_. c ret" s'] by simp
        done
      subgoal for out c ret s' using step.IH[of "c ret" f s'] by(simp cong del: sum.case_cong_weak)
      done
  qed
  show "ord_spmf (=) ?rhs ?lhs" unfolding inline12_def
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline1')
    show ?case unfolding inline11_def
      apply(rewrite inline1.simps; clarsimp simp add: bind_rpv_def)
      apply(rule conjI; clarsimp)
      subgoal by(rewrite inline1.simps; simp)
      subgoal for out c ret s' using step.IH[of "c ret" s'] by(simp cong del: sum.case_cong_weak)
      done
  qed
qed

lemma inline_bind_gpv [simp]:
  "inline (bind_gpv gpv f) s = bind_gpv (inline gpv s) (\<lambda>(x, s'). inline (f x) s')"
apply(coinduction arbitrary: gpv s rule: gpv_coinduct_bind)
apply(clarsimp simp add: map_spmf_bind_spmf o_def[abs_def] bind_gpv.sel inline_sel bind_map_spmf inline1_bind_gpv simp del: bind_gpv_sel' intro!: rel_spmf_bind_reflI split: generat.split)
apply(rule conjI)
 subgoal by(auto split: sum.split_asm simp add: spmf_rel_map spmf.map_comp o_def generat.map_comp generat.map_id[unfolded id_def] spmf.map_id[unfolded id_def] inline_sel intro!: rel_spmf_reflI generat.rel_refl fun.rel_refl)
by(auto split: sum.split_asm simp add: bind_gpv_assoc split_def intro!: gpv.rel_refl exI disjI2 rel_funI)

end

lemma set_inline1_lift_spmf1: "set_spmf (inline1 (\<lambda>s x. lift_spmf (p s x)) gpv s) \<subseteq> range Inl"
apply(induction arbitrary: gpv s rule: inline1_fixp_induct)
subgoal by(rule cont_intro ccpo_class.admissible_leI)+
apply(auto simp add: o_def bind_UNION split: generat.split_asm)+
done

lemma in_set_inline1_lift_spmf1: "y \<in> set_spmf (inline1 (\<lambda>s x. lift_spmf (p s x)) gpv s) \<Longrightarrow> \<exists>r s'. y = Inl (r, s')"
by(drule set_inline1_lift_spmf1[THEN subsetD]) auto

lemma inline_lift_spmf1:
  fixes p defines "callee \<equiv> \<lambda>s c. lift_spmf (p s c)"
  shows "inline callee gpv s = lift_spmf (map_spmf projl (inline1 callee gpv s))"
by(rule gpv.expand)(auto simp add: inline_sel spmf.map_comp callee_def intro!: map_spmf_cong[OF refl] dest: in_set_inline1_lift_spmf1)

context includes lifting_syntax begin
lemma inline1_parametric':
  "((S ===> C ===> rel_gpv'' (rel_prod R S) C' R') ===> rel_gpv'' A C R ===> S
   ===> rel_spmf (rel_sum (rel_prod A S) (rel_prod C' (rel_prod (R' ===> rel_gpv'' (rel_prod R S) C' R') (R ===> rel_gpv'' A C R)))))
  inline1 inline1"
  (is "(_ ===> ?R) _ _")
proof(rule rel_funI)
  note [transfer_rule] = the_gpv_parametric'
  show "?R (inline1 callee) (inline1 callee')" 
    if [transfer_rule]: "(S ===> C ===> rel_gpv'' (rel_prod R S) C' R') callee callee'"
    for callee callee'
    unfolding inline1_def
    by(unfold rel_fun_curry case_prod_curry)(rule fixp_spmf_parametric[OF inline1.mono inline1.mono]; transfer_prover)
qed

lemma inline1_parametric [transfer_rule]:
  "((S ===> C ===> rel_gpv (rel_prod (=) S) C') ===> rel_gpv A C ===> S
   ===> rel_spmf (rel_sum (rel_prod A S) (rel_prod C' (rel_prod (rel_rpv (rel_prod (=) S) C') (rel_rpv A C)))))
  inline1 inline1"
unfolding rel_gpv_conv_rel_gpv'' by(rule inline1_parametric')

lemma inline_parametric':
  notes [transfer_rule] = inline1_parametric' the_gpv_parametric' corec_gpv_parametric'
  shows "((S ===> C ===> rel_gpv'' (rel_prod R S) C' R') ===> rel_gpv'' A C R ===> S ===> rel_gpv'' (rel_prod A S) C' R')
  inline inline"
unfolding inline_def[abs_def] inline_aux_def
(* apply transfer_prover raises loose bound variable *)
apply(rule rel_funI)+
subgoal premises [transfer_rule] by transfer_prover
done

lemma inline_parametric [transfer_rule]:
  "((S ===> C ===> rel_gpv (rel_prod (=) S) C') ===> rel_gpv A C ===> S ===> rel_gpv (rel_prod A S) C')
  inline inline"
unfolding rel_gpv_conv_rel_gpv'' by(rule inline_parametric')
end


text \<open>Associativity rule for @{const inline}\<close>

context
  fixes callee1 :: "'s1 \<Rightarrow> 'c1 \<Rightarrow> ('r1 \<times> 's1, 'c, 'r) gpv"
  and callee2 :: "'s2 \<Rightarrow> 'c2 \<Rightarrow> ('r2 \<times> 's2, 'c1, 'r1) gpv"
begin

partial_function (spmf) inline2 :: "('a, 'c2, 'r2) gpv \<Rightarrow> 's2 \<Rightarrow> 's1
  \<Rightarrow> ('a \<times> ('s2 \<times> 's1) + 'c \<times> ('r1 \<times> 's1, 'c, 'r) rpv \<times> ('r2 \<times> 's2, 'c1, 'r1) rpv \<times> ('a, 'c2, 'r2) rpv) spmf"
where
  "inline2 gpv s2 s1 =
  bind_spmf (the_gpv gpv)
   (case_generat (\<lambda>x. return_spmf (Inl (x, s2, s1)))
     (\<lambda>out rpv. bind_spmf (inline1 callee1 (callee2 s2 out) s1)
       (case_sum (\<lambda>((r2, s2), s1). inline2 (rpv r2) s2 s1)
         (\<lambda>(x, rpv'', rpv'). return_spmf (Inr (x, rpv'', rpv', rpv))))))"

lemma inline2_fixp_induct [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>inline2. P (\<lambda>gpv s2 s1. inline2 ((gpv, s2), s1)))"
  and "P (\<lambda>_ _ _. return_pmf None)"
  and "\<And>inline2'. P inline2' \<Longrightarrow>
       P (\<lambda>gpv s2 s1. bind_spmf (the_gpv gpv) (\<lambda>generat. case generat of
           Pure x \<Rightarrow> return_spmf (Inl (x, s2, s1))
         | IO out rpv \<Rightarrow> bind_spmf (inline1 callee1 (callee2 s2 out) s1) (\<lambda>lr. case lr of
              Inl ((r2, s2), c) \<Rightarrow> inline2' (rpv r2) s2 c
           | Inr (x, rpv'', rpv') \<Rightarrow> return_spmf (Inr (x, rpv'', rpv', rpv)))))"
  shows "P inline2"
using assms unfolding split_def by(rule inline2.fixp_induct[unfolded curry_conv[abs_def] split_def])

lemma inline1_inline_conv_inline2:
  fixes gpv' :: "('r2 \<times> 's2, 'c1, 'r1) gpv"
  shows "inline1 callee1 (inline callee2 gpv s2) s1 = 
  map_spmf (map_sum (\<lambda>(x, (s2, s1)). ((x, s2), s1))
    (\<lambda>(x, rpv'', rpv', rpv). (x, rpv'', \<lambda>r1. rpv' r1 \<bind> (\<lambda>(r2, s2). inline callee2 (rpv r2) s2))))
  (inline2 gpv s2 s1)"
  (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  define inline1_1 :: "('s1 \<Rightarrow> 'c1 \<Rightarrow> ('r1 \<times> 's1, 'c, 'r) gpv) \<Rightarrow> ('r2 \<times> 's2, 'c1, 'r1) gpv \<Rightarrow> 's1 \<Rightarrow> _"
    where "inline1_1 = inline1"
  have "ord_spmf (=) ?lhs ?rhs"
    \<comment> \<open>We need in the inductive step that the approximation behaves well with @{const bind_gpv}
         because of @{thm [source] inline_aux_Inr}. So we have to thread it through the induction
         and do one half of the proof from @{thm [source] inline1_bind_gpv} again. We cannot inline
         @{thm [source] inline1_bind_gpv} in this proof here because the types are too specific.\<close>
    and "ord_spmf (=) (inline1 callee1 (gpv' \<bind> f) s1') 
      (do {
      res \<leftarrow> inline1_1 callee1 gpv' s1';
      case res of Inl (x, s') \<Rightarrow> inline1 callee1 (f x) s'
      | Inr (out, rpv', rpv) \<Rightarrow> return_spmf (Inr (out, rpv', rpv \<bind> f))
    })" for gpv' and f :: "_ \<Rightarrow> ('a \<times> 's2, 'c1, 'r1) gpv" and s1'
  proof(induction arbitrary: gpv s2 s1 gpv' f s1' rule: inline1_fixp_induct_strong2)
    case adm thus ?case
      apply(rule cont_intro)+
      subgoal for a b c d by(cases d; clarsimp)
      done

    case (step inline1')
    note step_IH = step.IH[unfolded inline1_1_def] and step_hyps = step.hyps[unfolded inline1_1_def]
    { case 1
      have inline1: "ord_spmf (=)
         (inline1 callee2 gpv s2 \<bind> (\<lambda>lr. case lr of Inl as2 \<Rightarrow> return_spmf (Inl (as2, s1))
            | Inr (out1, rpv', rpv) \<Rightarrow> the_gpv (callee1 s1 out1) \<bind> (\<lambda>generat. case generat of
                Pure (r1, s1) \<Rightarrow> inline1' (bind_gpv (rpv' r1) (\<lambda>(r2, s2). inline callee2 (rpv r2) s2)) s1
              | IO out rpv'' \<Rightarrow> return_spmf (Inr (out, rpv'', \<lambda>r1. bind_gpv (rpv' r1) (\<lambda>(r2, s2). inline callee2 (rpv r2) s2)) ))))
         (the_gpv gpv \<bind> (\<lambda>generat. case generat of Pure x \<Rightarrow> return_spmf (Inl ((x, s2), s1))
            | IO out2 rpv \<Rightarrow> inline1_1 callee1 (callee2 s2 out2) s1 \<bind> (\<lambda>lr. case lr of
                Inl ((r2, s2), s1) \<Rightarrow>
                   map_spmf (map_sum (\<lambda>(x, s2, s1). ((x, s2), s1)) (\<lambda>(x, rpv'', rpv', rpv). (x, rpv'', \<lambda>r1. bind_gpv (rpv' r1) (\<lambda>(r2, s2). inline callee2 (rpv r2) s2))))
                     (inline2 (rpv r2) s2 s1)
              | Inr (out, rpv'', rpv') \<Rightarrow>
                   return_spmf (Inr (out, rpv'', \<lambda>r1. bind_gpv (rpv' r1) (\<lambda>(r2, s2). inline callee2 (rpv r2) s2))))))"
      proof(induction arbitrary: gpv s2 s1 rule: inline1_fixp_induct)
        case step2: (step inline1'')
        note step2_IH = step2.IH[unfolded inline1_1_def]

        show ?case unfolding inline1_1_def
          apply(rewrite in "ord_spmf _ _ \<hole>" inline1.simps)
          apply(clarsimp intro!: ord_spmf_bind_reflI split: generat.split)
          apply(rule conjI)
          subgoal by(rewrite in "ord_spmf _ _ \<hole>" inline2.simps)(clarsimp simp add: map_spmf_bind_spmf o_def split: generat.split sum.split intro!: ord_spmf_bind_reflI spmf.leq_trans[OF step2_IH])
          subgoal by(clarsimp intro!: ord_spmf_bind_reflI step_IH[THEN spmf.leq_trans] split: generat.split sum.split simp add: bind_rpv_def)
          done
      qed simp_all
      show ?case
        apply(rewrite in "ord_spmf _ \<hole> _" inline_sel)
        apply(rewrite in "ord_spmf _ _ \<hole>" inline2.simps)
        apply(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf o_def intro!: ord_spmf_bind_reflI split: generat.split)
        apply(rule spmf.leq_trans[OF spmf.leq_trans, OF _ inline1])
        apply(auto intro!: ord_spmf_bind_reflI split: sum.split generat.split simp add: inline1_1_def map_spmf_bind_spmf)
        done }
    { case 2
      show ?case unfolding inline1_1_def
        by(rewrite inline1.simps)(auto simp del: bind_gpv_sel' simp add: bind_gpv.sel map_spmf_bind_spmf bind_map_spmf o_def bind_rpv_def intro!: ord_spmf_bind_reflI step_IH(2)[THEN spmf.leq_trans] step_hyps(2) split: generat.split sum.split) }
  qed simp_all
  thus "ord_spmf (=) ?lhs ?rhs" by -

  show "ord_spmf (=) ?rhs ?lhs"
  proof(induction arbitrary: gpv s2 s1 rule: inline2_fixp_induct)
    case adm show ?case by simp
    case bottom show ?case by simp
    case (step inline2')
    show ?case
      apply(rewrite in "ord_spmf _ _ \<hole>" inline1.simps)
      apply(rewrite inline_sel)
      apply(rewrite in "ord_spmf _ \<hole> _" inline1.simps)
      apply(rewrite in "ord_spmf _ _ \<hole>" inline1.simps)
      apply(clarsimp simp add: map_spmf_bind_spmf bind_map_spmf intro!: ord_spmf_bind_reflI split: generat.split)
      apply(rule conjI)
      subgoal
         apply clarsimp
         apply(rule step.IH[THEN spmf.leq_trans])
         apply(rewrite in "ord_spmf _ \<hole> _" inline1.simps)
         apply(rewrite inline_sel)
         apply(simp add: bind_map_spmf)
         done
      subgoal by(clarsimp intro!: ord_spmf_bind_reflI split: generat.split sum.split simp add: o_def inline1_bind_gpv bind_rpv_def step.IH)
      done
  qed
qed

lemma inline1_inline_conv_inline2':
  "inline1 (\<lambda>(s2, s1) c2. map_gpv (\<lambda>((r, s2), s1). (r, s2, s1)) id (inline callee1 (callee2 s2 c2) s1)) gpv (s2, s1) =
   map_spmf (map_sum id (\<lambda>(x, rpv'', rpv', rpv). (x, \<lambda>r. bind_gpv (rpv'' r)
       (\<lambda>(r1, s1). map_gpv (\<lambda>((r2, s2), s1). (r2, s2, s1)) id (inline callee1 (rpv' r1) s1)), rpv)))
     (inline2 gpv s2 s1)"
  (is "?lhs = ?rhs")
proof(rule spmf.leq_antisym)
  show "ord_spmf (=) ?lhs ?rhs"
  proof(induction arbitrary: gpv s2 s1 rule: inline1_fixp_induct)
    case (step inline1') show ?case
      by(rewrite inline2.simps)(auto simp add: map_spmf_bind_spmf o_def inline_sel gpv.map_sel bind_map_spmf id_def[symmetric] gpv.map_id map_gpv_bind_gpv split_def intro!: ord_spmf_bind_reflI step.IH[THEN spmf.leq_trans] split: generat.split sum.split)
  qed simp_all
  show "ord_spmf (=) ?rhs ?lhs"
  proof(induction arbitrary: gpv s2 s1 rule: inline2_fixp_induct)
   case (step inline2')
   show ?case
     apply(rewrite in "ord_spmf _ _ \<hole>" inline1.simps)
     apply(clarsimp simp add: map_spmf_bind_spmf bind_rpv_def o_def gpv.map_sel bind_map_spmf inline_sel map_gpv_bind_gpv id_def[symmetric] gpv.map_id split_def split: generat.split sum.split intro!: ord_spmf_bind_reflI)
     apply(rule spmf.leq_trans[OF spmf.leq_trans, OF _ step.IH])
     apply(auto simp add: split_def id_def[symmetric] intro!: ord_spmf_reflI)
     done
  qed simp_all
qed

lemma inline_assoc:
  "inline callee1 (inline callee2 gpv s2) s1 =
   map_gpv (\<lambda>(r, s2, s1). ((r, s2), s1)) id (inline (\<lambda>(s2, s1) c2. map_gpv (\<lambda>((r, s2), s1). (r, s2, s1)) id (inline callee1 (callee2 s2 c2) s1)) gpv (s2, s1))"
proof(coinduction arbitrary: s2 s1 gpv rule: gpv_coinduct_bind[where ?'b = "('r2 \<times> 's2) \<times> 's1" and ?'c = "('r2 \<times> 's2) \<times> 's1"])
  case (Eq_gpv s2 s1 gpv)
  have "\<exists>gpv2 gpv2' (f :: ('r2 \<times> 's2) \<times> 's1 \<Rightarrow> _) (f' :: ('r2 \<times> 's2) \<times> 's1 \<Rightarrow> _).
          bind_gpv (bind_gpv (rpv'' r) (\<lambda>(r1, s1). inline callee1 (rpv' r1) s1)) (\<lambda>((r2, s2), s1). inline callee1 (inline callee2 (rpv r2) s2) s1) = gpv2 \<bind> f \<and>
          bind_gpv (bind_gpv (rpv'' r) (\<lambda>(r1, s1). inline callee1 (rpv' r1) s1)) (\<lambda>((r2, s2), s1). map_gpv (\<lambda>(r, s2, y). ((r, s2), y)) id (inline (\<lambda>(s2, s1) c2. map_gpv (\<lambda>((r, s2), s1). (r, s2, s1)) id (inline callee1 (callee2 s2 c2) s1)) (rpv r2) (s2, s1))) = gpv2' \<bind> f' \<and>
          rel_gpv (\<lambda>x y. \<exists>s2 s1 gpv. f x = inline callee1 (inline callee2 gpv s2) s1 \<and>
              f' y = map_gpv (\<lambda>(r, s2, y). ((r, s2), y)) id (inline (\<lambda>(s2, s1) c2. map_gpv (\<lambda>((r, s2), s1). (r, s2, s1)) id (inline callee1 (callee2 s2 c2) s1)) gpv (s2, s1)))
            (=) gpv2 gpv2'" 
    for rpv'' :: "('r1 \<times> 's1, 'c, 'r) rpv" and rpv' :: "('r2 \<times> 's2, 'c1, 'r1) rpv" and rpv :: "('a, 'c2, 'r2) rpv" and r :: 'r
    by(auto intro!: exI gpv.rel_refl)
  then show ?case
    apply(subst inline_sel)
    apply(subst gpv.map_sel)
    apply(subst inline_sel)
    apply(subst inline1_inline_conv_inline2)
    apply(subst inline1_inline_conv_inline2')
    apply(unfold spmf.map_comp o_def case_sum_map_sum spmf_rel_map generat.rel_map)
    apply(rule rel_spmf_reflI)
    subgoal for lr by(cases lr)(auto del: disjCI intro!: rel_funI disjI2 simp add: split_def map_gpv_conv_bind[folded id_def] bind_gpv_assoc)
    done
qed

end

lemma set_inline2_lift_spmf1: "set_spmf (inline2 (\<lambda>s x. lift_spmf (p s x)) callee gpv s s') \<subseteq> range Inl"
apply(induction arbitrary: gpv s s' rule: inline2_fixp_induct)
subgoal by(rule cont_intro ccpo_class.admissible_leI)+
apply(auto simp add: o_def bind_UNION split: generat.split_asm sum.split_asm dest!: in_set_inline1_lift_spmf1)
apply blast
done

lemma in_set_inline2_lift_spmf1: "y \<in> set_spmf (inline2 (\<lambda>s x. lift_spmf (p s x)) callee gpv s s') \<Longrightarrow> \<exists>r s s'. y = Inl (r, s, s')"
by(drule set_inline2_lift_spmf1[THEN subsetD]) auto

context
  fixes consider' :: "'call \<Rightarrow> bool" 
  and "consider" :: "'call' \<Rightarrow> bool" 
  and callee :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call', 'ret') gpv" 
  notes [[function_internals]]
begin

private partial_function (spmf) inline1'
  :: "('a, 'call, 'ret) gpv \<Rightarrow> 's
  \<Rightarrow> ('a \<times> 's + 'call \<times> 'call' \<times> ('ret \<times> 's, 'call', 'ret') rpv \<times> ('a, 'call, 'ret) rpv) spmf"
where
  "inline1' gpv s =
   the_gpv gpv \<bind>
   case_generat (\<lambda>x. return_spmf (Inl (x, s)))
     (\<lambda>out rpv. the_gpv (callee s out) \<bind>
         case_generat (\<lambda>(x, y). inline1' (rpv x) y)
          (\<lambda>out' rpv'. return_spmf (Inr (out, out', rpv', rpv))))"

private lemma inline1'_fixp_induct [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>inline1'. P (\<lambda>gpv s. inline1' (gpv, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>inline1'. P inline1' \<Longrightarrow> P (\<lambda>gpv s. the_gpv gpv \<bind> case_generat (\<lambda>x. return_spmf (Inl (x, s))) (\<lambda>out rpv. the_gpv (callee s out) \<bind> case_generat (\<lambda>(x, y). inline1' (rpv x) y) (\<lambda>out' rpv'. return_spmf (Inr (out, out', rpv', rpv)))))"
  shows "P inline1'"
using assms by(rule inline1'.fixp_induct[unfolded curry_conv[abs_def]])

private lemma inline1_conv_inline1': "inline1 callee gpv s = map_spmf (map_sum id snd) (inline1' gpv s)"
proof(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1'.mono inline1_def inline1'_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1 inline1')
  thus ?case by(clarsimp simp add: map_spmf_bind_spmf o_def intro!: bind_spmf_cong[OF refl] split: generat.split)
qed

context
  fixes q :: "enat" 
  assumes q: "\<And>s x. consider' x \<Longrightarrow> interaction_bound consider (callee s x) \<le> q"
  and ignore: "\<And>s x. \<not> consider' x \<Longrightarrow> interaction_bound consider (callee s x) = 0"
begin

private lemma interaction_bound_inline1'_aux:
  "interaction_bound consider' gpv \<le> p
  \<Longrightarrow> set_spmf (inline1' gpv s) \<subseteq> {Inr (out', out, c', rpv) | out' out c' rpv. 
        if consider' out'
        then (\<forall>input. (if consider out then eSuc (interaction_bound consider (c' input)) else interaction_bound consider (c' input)) \<le> q) \<and> 
             (\<forall>x. eSuc (interaction_bound consider' (rpv x)) \<le> p)
        else \<not> consider out \<and> (\<forall>input. interaction_bound consider (c' input) = 0) \<and> (\<forall>x. interaction_bound consider' (rpv x) \<le> p)}
      \<union> range Inl"
proof(induction arbitrary: gpv s rule: inline1'_fixp_induct)
  { case adm show ?case by(rule cont_intro ccpo_class.admissible_leI)+ }
  { case bottom show ?case by simp }
  case (step inline1')
  have *: "interaction_bound consider' (c input) \<le> p" if "IO out c \<in> set_spmf (the_gpv gpv)" for out c input
    by(cases "consider' out")(auto intro: interaction_bound_IO_consider[OF that, THEN order_trans, THEN order_trans[OF ile_eSuc]] interaction_bound_IO_ignore[OF that, THEN order_trans] step.prems)
  have **: "if consider' out'
    then (\<forall>input. (if consider out then eSuc (interaction_bound consider (c input))  else interaction_bound consider (c input)) \<le> q) \<and>
         (\<forall>x. eSuc (interaction_bound consider' (rpv x)) \<le> p)
    else \<not> consider out \<and> (\<forall>input. interaction_bound consider (c input) = 0) \<and> (\<forall>x. interaction_bound consider' (rpv x) \<le> p)"
    if "IO out' rpv \<in> set_spmf (the_gpv gpv)" "IO out c \<in> set_spmf (the_gpv (callee s out'))"
    for out' rpv out c
  proof(cases "consider' out'")
    case True
    then show ?thesis using that q
      by(auto split del: if_split intro!: interaction_bound_IO[THEN order_trans] interaction_bound_IO_consider[THEN order_trans] step.prems)
  next
    case False
    have "\<not> consider out" "interaction_bound consider (c input) = 0" for input
      using interaction_bound_IO[OF that(2), of "consider" input] ignore[OF False, of s]
      by(auto split: if_split_asm)
    then show ?thesis using False that
      by(auto split del: if_split intro: interaction_bound_IO_ignore[THEN order_trans] step.prems)
  qed
  show ?case
    by(auto 6 4 simp add: bind_UNION del: subsetI intro!: UN_least intro: step.IH * ** split: generat.split split del: if_split)
qed

lemma interaction_bound_inline1':
  "\<lbrakk> Inr (out', out, c', rpv) \<in> set_spmf (inline1' gpv s); interaction_bound consider' gpv \<le> p \<rbrakk>
  \<Longrightarrow> if consider' out' then
        (if consider out then eSuc (interaction_bound consider (c' input)) else interaction_bound consider (c' input)) \<le> q \<and> 
        eSuc (interaction_bound consider' (rpv x)) \<le> p
      else \<not> consider out \<and> interaction_bound consider (c' input) = 0 \<and> interaction_bound consider' (rpv x) \<le> p"
using interaction_bound_inline1'_aux[where gpv=gpv and p=p and s=s] by(auto split: if_split_asm)

end

lemma interaction_bounded_by_inline1:
  "\<lbrakk> Inr (out', out, c', rpv) \<in> set_spmf (inline1' gpv s); 
    interaction_bounded_by consider' gpv p;
    \<And>s x. consider' x \<Longrightarrow> interaction_bounded_by consider (callee s x) q; 
    \<And>s x. \<not> consider' x \<Longrightarrow> interaction_bounded_by consider (callee s x) 0 \<rbrakk>
  \<Longrightarrow> if consider' out' then
        (if consider out then q \<noteq> 0 \<and> interaction_bounded_by consider (c' input) (q - 1) else interaction_bounded_by consider (c' input) q) \<and>
        p \<noteq> 0 \<and> interaction_bounded_by consider' (rpv x) (p - 1)
      else \<not> consider out \<and> interaction_bounded_by consider (c' input) 0 \<and> interaction_bounded_by consider' (rpv x) p"
unfolding interaction_bounded_by_0 unfolding interaction_bounded_by.simps
apply(drule (1) interaction_bound_inline1'[where input=input and x=x, rotated 2], assumption, assumption)
apply(cases p q rule: co.enat.exhaust[case_product co.enat.exhaust])
apply(simp_all add: zero_enat_def[symmetric] eSuc_enat[symmetric] split: if_split_asm)
done

declare enat_0_iff [simp]

lemma interaction_bounded_by_inline [interaction_bound]:
  assumes p: "interaction_bounded_by consider' gpv p"
  and q: "\<And>s x. consider' x \<Longrightarrow> interaction_bounded_by consider (callee s x) q"
  and ignore: "\<And>s x. \<not> consider' x \<Longrightarrow> interaction_bounded_by consider (callee s x) 0"
  shows "interaction_bounded_by consider (inline callee gpv s) (p * q)"
proof
  have "interaction_bounded_by consider' gpv p \<Longrightarrow> interaction_bound consider (inline callee gpv s) \<le> p * q"
    and "interaction_bound consider (bind_gpv gpv' f) \<le> interaction_bound consider gpv' + (SUP x\<in>results'_gpv gpv'. interaction_bound consider (f x))"
    for gpv' and f :: "'ret \<times> 's \<Rightarrow> ('a \<times> 's, 'call', 'ret') gpv"
  proof(induction arbitrary: gpv s p gpv' f rule: interaction_bound_fixp_induct)
    case adm show ?case by simp
    case bottom case 1 show ?case by simp
    case (step interaction_bound') case step: 1
    show ?case (is "(SUP generat\<in>?inline. ?lhs generat) \<le> ?rhs")
    proof(rule SUP_least)
      fix generat
      assume "generat \<in> ?inline"
      then consider (Pure) ret s' where "generat = Pure (ret, s')"
          and "Inl (ret, s') \<in> set_spmf (inline1 callee gpv s)"
        | (IO) out c rpv where "generat = IO out (\<lambda>input. bind_gpv (c input) (\<lambda>(ret, s'). inline callee (rpv ret) s'))"
          and "Inr (out, c, rpv) \<in> set_spmf (inline1 callee gpv s)"
        by(clarsimp simp add: inline_sel split: sum.split_asm)
      then show "?lhs generat \<le> ?rhs"
      proof(cases)
        case Pure thus ?thesis by simp
      next
        case IO
        from IO(2) obtain out' where out': "Inr (out', out, c, rpv) \<in> set_spmf (inline1' gpv s)"
          by(auto simp add: inline1_conv_inline1' Inr_eq_map_sum_iff)
        show ?thesis
        proof(cases "consider' out'")
          case True
          with interaction_bounded_by_inline1[OF out' step.prems q ignore]
          have p: "p \<noteq> 0" and rpv: "\<And>x. interaction_bounded_by consider' (rpv x) (p - 1)"
            and c: "\<And>input. if consider out then q \<noteq> 0 \<and> interaction_bounded_by consider (c input) (q - 1) else interaction_bounded_by consider (c input) q"
            by auto

          have "?lhs generat \<le> (if consider out then 1 else 0) + (SUP input. interaction_bound' (bind_gpv (c input) (\<lambda>(ret, s'). inline callee (rpv ret) s')))"
            (is "_ \<le> _ + ?sup")
            using IO(1) by(auto simp add: plus_1_eSuc)
          also have "?sup \<le> (SUP input. interaction_bound consider (c input) + (SUP (ret, s') \<in> results'_gpv (c input). interaction_bound' (inline callee (rpv ret) s')))"
            unfolding split_def by(rule SUP_mono)(blast intro: step.IH)
          also have "\<dots> \<le> (SUP input. interaction_bound consider (c input) + (SUP (ret, s') \<in> results'_gpv (c input). (p - 1) * q))"
            using rpv by(auto intro!: SUP_mono rev_bexI add_mono step.IH)
          also have "\<dots> \<le> (SUP input. interaction_bound consider (c input) + (p - 1) * q)"
            apply(auto simp add: SUP_constant bot_enat_def intro!: SUP_mono)
            apply(metis add.right_neutral add_mono i0_lb order_refl)+
            done
          also have "\<dots> \<le> (SUP input :: 'ret'. (if consider out then q - 1 else q) + (p - 1) * q)"
            apply(rule SUP_mono rev_bexI UNIV_I add_mono)+
            using c
            apply(auto simp add: interaction_bounded_by.simps)
            done
          also have "\<dots> = (if consider out then q - 1 else q) + (p - 1) * q"
            by(simp add: SUP_constant)
          finally show ?thesis
            apply(rule order_trans)
            prefer 5
            using p c
            apply(cases p; cases q)
            apply(auto simp add: one_enat_def algebra_simps Suc_leI)
            done
        next
          case False
          with interaction_bounded_by_inline1[OF out' step.prems q ignore]
          have out: "\<not> consider out" and zero: "\<And>input. interaction_bounded_by consider (c input) 0"
            and rpv: "\<And>x. interaction_bounded_by consider' (rpv x) p" by auto
          have "?lhs generat \<le> (SUP input. interaction_bound' (bind_gpv (c input) (\<lambda>(ret, s'). inline callee (rpv ret) s')))"
            using IO(1) out by auto
          also have "\<dots> \<le> (SUP input. interaction_bound consider (c input) + (SUP (ret, s') \<in> results'_gpv (c input). interaction_bound' (inline callee (rpv ret) s')))"
            unfolding split_def by(rule SUP_mono)(blast intro: step.IH)
          also have "\<dots> \<le> (SUP input. (SUP (ret, s') \<in> results'_gpv (c input). p * q))"
            using rpv zero by(auto intro!: SUP_mono rev_bexI add_mono step.IH simp add: interaction_bounded_by_0)
          also have "\<dots> \<le> (SUP input :: 'ret'. p * q)"
            by(rule SUP_mono rev_bexI)+(auto simp add: SUP_constant)
          also have "\<dots> = p * q" by(simp add: SUP_constant)
          finally show ?thesis .
        qed
      qed
    qed
  next
    case bottom case 2 show ?case by simp
    case step case 2 show ?case using step by -(rule interaction_bound_bind_step)
  qed
  then show "interaction_bound consider (inline callee gpv s) \<le> p * q" using p by -
qed

end

lemma interaction_bounded_by_inline_invariant: (* TODO: augment with types *)
  includes lifting_syntax
  fixes consider' :: "'call \<Rightarrow> bool" 
  and "consider" :: "'call' \<Rightarrow> bool" 
  and callee :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call', 'ret') gpv" 
  and gpv :: "('a, 'call, 'ret) gpv"
  assumes p: "interaction_bounded_by consider' gpv p"
  and q: "\<And>s x. \<lbrakk> I s; consider' x \<rbrakk> \<Longrightarrow> interaction_bounded_by consider (callee s x) q"
  and ignore: "\<And>s x. \<lbrakk> I s; \<not> consider' x \<rbrakk> \<Longrightarrow> interaction_bounded_by consider (callee s x) 0"
  and I: "I s"
  and invariant: "\<And>s x y s'. \<lbrakk> (y, s') \<in> results'_gpv (callee s x); I s \<rbrakk> \<Longrightarrow> I s'"
  shows "interaction_bounded_by consider (inline callee gpv s) (p * q)"
proof -
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr x y \<longleftrightarrow> x = Rep y" for x y
    have [transfer_rule]: "bi_unique cr" "right_total cr"
      using td cr_def[abs_def] by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I"
      using type_definition_Domainp[OF td cr_def[abs_def]] by simp

    define callee' where "callee' = (Rep --->  id ---> map_gpv (map_prod id Abs) id) callee"
    have [transfer_rule]: "(cr ===> (=) ===> rel_gpv (rel_prod (=) cr) (=)) callee callee'"
      by(auto simp add: callee'_def rel_fun_def cr_def gpv.rel_map prod.rel_map td.Abs_inverse intro!: gpv.rel_refl_strong intro: td.Rep[simplified] dest: invariant)

    define s' where "s' = Abs s"
    have [transfer_rule]: "cr s s'" using I by(simp add: cr_def s'_def td.Abs_inverse)

    note p moreover
    have "consider' x \<Longrightarrow> interaction_bounded_by consider (callee' s x) q" for s x
      by(transfer fixing: "consider" consider' q)(clarsimp simp add: q)
    moreover have "\<not> consider' x \<Longrightarrow> interaction_bounded_by consider (callee' s x) 0" for s x
      by(transfer fixing: "consider" consider')(clarsimp simp add: ignore)
    ultimately have "interaction_bounded_by consider (inline callee' gpv s') (p * q)" 
      by(rule interaction_bounded_by_inline)
    then have "interaction_bounded_by consider (inline callee gpv s) (p * q)" by transfer  }
  from this[cancel_type_definition] I show ?thesis by blast
qed

context
  fixes \<I> :: "('call, 'ret) \<I>"
  and \<I>' :: "('call', 'ret') \<I>"
  and callee :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call', 'ret') gpv"
  assumes results: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> results_gpv \<I>' (callee s x) \<subseteq> responses_\<I> \<I> x \<times> UNIV"
begin

lemma inline1_in_sub_gpvs_callee:
  assumes "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  shows "\<exists>call\<in>outs_\<I> \<I>. \<exists>s. \<forall>x \<in> responses_\<I> \<I>' out. callee' x \<in> sub_gpvs \<I>' (callee s call)"
proof -
  from WT
  have "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, callee', rpv') | out callee' rpv'.
    \<exists>call\<in>outs_\<I> \<I>. \<exists>s. \<forall>x \<in> responses_\<I> \<I>' out. callee' x \<in> sub_gpvs \<I>' (callee s call)} \<union> range Inl"
    (is "?concl (inline1 callee) gpv s")
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
    case bottom show ?case by simp
    case (step inline1')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
      from step.prems IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      { fix x s'
        assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
        then have "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
        with out have "x \<in> responses_\<I> \<I> out" by(auto dest: results)
        with step.prems IO have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
        hence "?concl inline1' (c x) s'" by(rule step.IH)
      } moreover {
        fix out' c'
        assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
        hence "\<forall>x\<in>responses_\<I> \<I>' out'. c' x \<in> sub_gpvs \<I>' (callee s out)"
          by(auto intro: sub_gpvs.base)
        then have "\<exists>call\<in>outs_\<I> \<I>. \<exists>s. \<forall>x\<in>responses_\<I> \<I>' out'. c' x \<in> sub_gpvs \<I>' (callee s call)"
          using out by blast
      } moreover note calculation }
    then show ?case using step.prems
      by(auto del: subsetI simp add: bind_UNION intro!: UN_least split: generat.split)
  qed
  thus ?thesis using assms by fastforce
qed

lemma inline1_in_sub_gpvs:
  assumes "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
  and "(x, s') \<in> results_gpv \<I>' (callee' input)"
  and "input \<in> responses_\<I> \<I>' out"
  and "\<I> \<turnstile>g gpv \<surd>"
  shows "rpv' x \<in> sub_gpvs \<I> gpv"
proof -
  from \<open>\<I> \<turnstile>g gpv \<surd>\<close>
  have "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, callee', rpv') | out callee' rpv'.
    \<forall>input \<in> responses_\<I> \<I>' out. \<forall>(x, s')\<in>results_gpv \<I>' (callee' input). rpv' x \<in> sub_gpvs \<I> gpv}
    \<union> range Inl" (is "?concl (inline1 callee) gpv s" is "_ \<subseteq> ?rhs gpv s")
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
    case bottom show ?case by simp
  next
    case (step inline1')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
      from step.prems IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      { fix x s'
        assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
        then have "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
        with out have "x \<in> responses_\<I> \<I> out" by(auto dest: results)
        with step.prems IO have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
        hence "?concl inline1' (c x) s'" by(rule step.IH)
        also have "\<dots> \<subseteq> ?rhs gpv s'" using IO Pure
          by(fastforce intro: sub_gpvs.cont dest: WT_gpv_OutD[OF step.prems] results[THEN subsetD, OF _ results_gpv.Pure])
        finally have "set_spmf (inline1' (c x) s') \<subseteq> \<dots>" .
      } moreover {
        fix out' c' input x s'
        assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
          and "input \<in> responses_\<I> \<I>' out'" and "(x, s') \<in> results_gpv \<I>' (c' input)"
        then have "c x \<in> sub_gpvs \<I> gpv" using IO
          by(auto intro!: sub_gpvs.base dest: WT_gpv_OutD[OF step.prems] results[THEN subsetD, OF _ results_gpv.IO])
      } moreover note calculation }
    then show ?case
      by(auto simp add: bind_UNION intro!: UN_least split: generat.split del: subsetI)
  qed
  with assms show ?thesis by fastforce
qed

context
  assumes WT: "\<And>x s. x \<in> outs_\<I> \<I> \<Longrightarrow> \<I>' \<turnstile>g callee s x \<surd>"
begin

lemma WT_gpv_inline1:
  assumes "Inr (out, rpv, rpv') \<in> set_spmf (inline1 callee gpv s)"
  and "\<I> \<turnstile>g gpv \<surd>"
  shows "out \<in> outs_\<I> \<I>'" (is "?thesis1")
  and "input \<in> responses_\<I> \<I>' out \<Longrightarrow> \<I>' \<turnstile>g rpv input \<surd>" (is "PROP ?thesis2")
  and "\<lbrakk> input \<in> responses_\<I> \<I>' out; (x, s') \<in> results_gpv \<I>' (rpv input) \<rbrakk> \<Longrightarrow> \<I> \<turnstile>g rpv' x \<surd>" (is "PROP ?thesis3")
proof -
  from \<open>\<I> \<turnstile>g gpv \<surd>\<close>
  have "set_spmf (inline1 callee gpv s) \<subseteq> {Inr (out, rpv, rpv') | out rpv rpv'. out \<in> outs_\<I> \<I>'} \<union> range Inl"
  proof(induction arbitrary: gpv s rule: inline1_fixp_induct)
    { case adm show ?case by(intro cont_intro ccpo_class.admissible_leI) }
    { case bottom show ?case by simp }
    case (step inline1')
    { fix out c
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" 
      from step.prems IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      { fix x s'
        assume Pure: "Pure (x, s') \<in> set_spmf (the_gpv (callee s out))"
        then have "(x, s') \<in> results_gpv \<I>' (callee s out)" by(rule results_gpv.Pure)
        with out have "x \<in> responses_\<I> \<I> out" by(auto dest: results)
        with step.prems IO have "\<I> \<turnstile>g c x \<surd>" by(rule WT_gpvD)
      } moreover {
        fix out' c'
        from out have "\<I>' \<turnstile>g callee s out \<surd>" by(rule WT)
        moreover assume "IO out' c' \<in> set_spmf (the_gpv (callee s out))"
        ultimately have "out' \<in> outs_\<I> \<I>'" by(rule WT_gpvD) 
      } moreover note calculation }
    then show ?case 
      by(auto del: subsetI simp add: bind_UNION intro!: UN_least split: generat.split intro!: step.IH[THEN order_trans])
  qed
  then show ?thesis1 using assms by auto

  assume "input \<in> responses_\<I> \<I>' out"
  with inline1_in_sub_gpvs_callee[OF \<open>Inr _ \<in> _\<close>] \<open>\<I> \<turnstile>g gpv \<surd>\<close>
  obtain out' s where "out' \<in> outs_\<I> \<I>" 
    and *: "rpv input \<in> sub_gpvs \<I>' (callee s out')" by auto
  from \<open>out' \<in> _\<close> have "\<I>' \<turnstile>g callee s out' \<surd>" by(rule WT)
  then show "\<I>' \<turnstile>g rpv input \<surd>" using * by(rule WT_sub_gpvsD)

  assume "(x, s') \<in> results_gpv \<I>' (rpv input)"
  with \<open>Inr _ \<in> _\<close> have "rpv' x \<in> sub_gpvs \<I> gpv"
    using \<open>input \<in> _\<close> \<open>\<I> \<turnstile>g gpv \<surd>\<close> by(rule inline1_in_sub_gpvs)
  with \<open>\<I> \<turnstile>g gpv \<surd>\<close> show "\<I> \<turnstile>g rpv' x \<surd>" by(rule WT_sub_gpvsD)
qed

lemma WT_gpv_inline:
  assumes "\<I> \<turnstile>g gpv \<surd>"
  shows "\<I>' \<turnstile>g inline callee gpv s \<surd>"
using assms
proof(coinduction arbitrary: gpv s rule: WT_gpv_coinduct_bind)
  case (WT_gpv out c gpv)
  from \<open>IO out c \<in> _\<close> obtain callee' rpv'
    where Inr: "Inr (out, callee', rpv') \<in> set_spmf (inline1 callee gpv s)"
    and c: "c = (\<lambda>input. callee' input \<bind> (\<lambda>(x, s). inline callee (rpv' x) s))"
    by(clarsimp simp add: inline_sel split: sum.split_asm)
  from Inr \<open>\<I> \<turnstile>g gpv \<surd>\<close> have ?out by(rule WT_gpv_inline1)
  moreover have "?cont TYPE('ret \<times> 's)" (is "\<forall>input\<in>_. _ \<or> _ \<or> ?case' input")
  proof(rule ballI disjI2)+
    fix input
    assume "input \<in> responses_\<I> \<I>' out"
    with Inr \<open>\<I> \<turnstile>g gpv \<surd> \<close>have "\<I>' \<turnstile>g callee' input \<surd>"
      and "\<And>x s'. (x, s') \<in> results_gpv \<I>' (callee' input) \<Longrightarrow> \<I> \<turnstile>g rpv' x \<surd>"
      by(blast intro: WT_gpv_inline1)+
    then show "?case' input" by(subst c)(auto 4 4)
  qed
  ultimately show "?case TYPE('ret \<times> 's)" ..
qed

end

context
  fixes gpv :: "('a, 'call, 'ret) gpv"
  assumes gpv: "lossless_gpv \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
begin

lemma lossless_spmf_inline1:
  assumes lossless: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (the_gpv (callee s x))"
  shows "lossless_spmf (inline1 callee gpv s)"
using gpv
proof(induction arbitrary: s rule: lossless_WT_gpv_induct)
  case (lossless_gpv p)
  show ?case using \<open>lossless_spmf p\<close>
    apply(subst inline1_unfold)
    apply(auto split: generat.split intro: lossless lossless_gpv.hyps dest: results[THEN subsetD, rotated, OF results_gpv.Pure] intro: lossless_gpv.IH)
    done
qed

lemma lossless_gpv_inline1:
  assumes *: "Inr (out, rpv, rpv') \<in> set_spmf (inline1 callee gpv s)"
  and **: "input \<in> responses_\<I> \<I>' out"
  and lossless: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_gpv \<I>' (callee s x)"
  shows "lossless_gpv \<I>' (rpv input)"
proof -
  from inline1_in_sub_gpvs_callee[OF * gpv(2)] **
  obtain out' s where "out' \<in> outs_\<I> \<I>" and ***: "rpv input \<in> sub_gpvs \<I>' (callee s out')" by blast
  from \<open>out' \<in> _\<close> have "lossless_gpv \<I>' (callee s out')" by(rule lossless)
  thus ?thesis using *** by(rule lossless_sub_gpvsD)
qed

lemma lossless_results_inline1:
  assumes "Inr (out, rpv, rpv') \<in> set_spmf (inline1 callee gpv s)"
  and "(x, s') \<in> results_gpv \<I>' (rpv input)"
  and "input \<in> responses_\<I> \<I>' out"
  shows "lossless_gpv \<I> (rpv' x)"
proof -
  from assms gpv(2) have "rpv' x \<in> sub_gpvs \<I> gpv" by(rule inline1_in_sub_gpvs)
  with gpv(1) show "lossless_gpv \<I> (rpv' x)" by(rule lossless_sub_gpvsD)
qed

end

lemmas lossless_inline1[rotated 2] = lossless_spmf_inline1 lossless_gpv_inline1 lossless_results_inline1

lemma lossless_inline[rotated]:
  fixes gpv :: "('a, 'call, 'ret) gpv"
  assumes gpv: "lossless_gpv \<I> gpv" "\<I> \<turnstile>g gpv \<surd>"
  and lossless: "\<And>s x. x \<in> outs_\<I> \<I> \<Longrightarrow> lossless_gpv \<I>' (callee s x)"
  shows "lossless_gpv \<I>' (inline callee gpv s)"
using gpv
proof(induction arbitrary: s rule: lossless_WT_gpv_induct_strong)
  case (lossless_gpv p)
  have lp: "lossless_gpv \<I> (GPV p)" by(rule lossless_sub_gpvsI)(auto intro: lossless_gpv.hyps)
  moreover have wp: "\<I> \<turnstile>g GPV p \<surd>" by(rule WT_sub_gpvsI)(auto intro: lossless_gpv.hyps)
  ultimately have "lossless_spmf (the_gpv (inline callee (GPV p) s))"
    by(auto simp add: inline_sel intro: lossless_spmf_inline1 lossless_gpv_lossless_spmfD[OF lossless])
  moreover {
    fix out c input
    assume IO: "IO out c \<in> set_spmf (the_gpv (inline callee (GPV p) s))"
      and "input \<in> responses_\<I> \<I>' out"
    from IO obtain callee' rpv
      where Inr: "Inr (out, callee', rpv) \<in> set_spmf (inline1 callee (GPV p) s)"
      and c: "c = (\<lambda>input. callee' input \<bind> (\<lambda>(x, y). inline callee (rpv x) y))"
      by(clarsimp simp add: inline_sel split: sum.split_asm)
    from Inr \<open>input \<in> _\<close> lossless lp wp have "lossless_gpv \<I>' (callee' input)" by(rule lossless_inline1)
    moreover {
      fix x s'
      assume "(x, s') \<in> results_gpv \<I>' (callee' input)"
      with Inr have "rpv x \<in> sub_gpvs \<I> (GPV p)" using \<open>input \<in> _\<close> wp by(rule inline1_in_sub_gpvs)
      hence "lossless_gpv \<I>' (inline callee (rpv x) s')" by(rule lossless_gpv.IH)
    } ultimately have "lossless_gpv \<I>' (c input)" unfolding c by clarsimp
  } ultimately show ?case by(rule lossless_gpvI)
qed

end

definition id_oracle :: "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's, 'call, 'ret) gpv"
where "id_oracle s x = Pause x (\<lambda>x. Done (x, s))"

lemma inline1_id_oracle:
  "inline1 id_oracle gpv s =
   map_spmf (\<lambda>generat. case generat of Pure x \<Rightarrow> Inl (x, s) | IO out c \<Rightarrow> Inr (out, \<lambda>x. Done (x, s), c)) (the_gpv gpv)"
by(subst inline1.simps)(auto simp add: id_oracle_def map_spmf_conv_bind_spmf intro!: bind_spmf_cong split: generat.split)

lemma inline_id_oracle [simp]: "inline id_oracle gpv s = map_gpv (\<lambda>x. (x, s)) id gpv"
by(coinduction arbitrary: gpv s)(auto 4 3 simp add: inline_sel inline1_id_oracle spmf_rel_map gpv.map_sel o_def generat.rel_map intro!: rel_spmf_reflI rel_funI split: generat.split)

subsection \<open>Running GPVs\<close>

type_synonym ('call, 'ret, 's) callee = "'s \<Rightarrow> 'call \<Rightarrow> ('ret \<times> 's) spmf"

context fixes callee :: "('call, 'ret, 's) callee" notes [[function_internals]] begin

partial_function (spmf) exec_gpv :: "('a, 'call, 'ret) gpv \<Rightarrow> 's \<Rightarrow> ('a \<times> 's) spmf"
where
  "exec_gpv c s =
   the_gpv c \<bind>
     case_generat (\<lambda>x. return_spmf (x, s))
     (\<lambda>out c. callee s out \<bind> (\<lambda>(x, y). exec_gpv (c x) y))"

abbreviation run_gpv :: "('a, 'call, 'ret) gpv \<Rightarrow> 's \<Rightarrow> 'a spmf"
where "run_gpv gpv s \<equiv> map_spmf fst (exec_gpv gpv s)"

lemma exec_gpv_fixp_induct [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>f. P (\<lambda>c s. f (c, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>exec_gpv. P exec_gpv \<Longrightarrow> 
     P (\<lambda>c s. the_gpv c \<bind> case_generat (\<lambda>x. return_spmf (x, s)) (\<lambda>out c. callee s out \<bind> (\<lambda>(x, y). exec_gpv (c x) y)))"
  shows "P exec_gpv"
using assms(1)
by(rule exec_gpv.fixp_induct[unfolded curry_conv[abs_def]])(simp_all add: assms(2-))

lemma exec_gpv_fixp_induct_strong [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>f. P (\<lambda>c s. f (c, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>exec_gpv'. \<lbrakk> \<And>c s. ord_spmf (=) (exec_gpv' c s) (exec_gpv c s); P exec_gpv' \<rbrakk>
    \<Longrightarrow> P (\<lambda>c s. the_gpv c \<bind> case_generat (\<lambda>x. return_spmf (x, s)) (\<lambda>out c. callee s out \<bind> (\<lambda>(x, y). exec_gpv' (c x) y)))"
  shows "P exec_gpv"
using assms
by(rule spmf.fixp_strong_induct_uc[where P="\<lambda>f. P (curry f)" and U=case_prod and C=curry, OF exec_gpv.mono exec_gpv_def, simplified curry_case_prod, simplified curry_conv[abs_def] fun_ord_def split_paired_All prod.case case_prod_eta, OF refl]) blast

lemma exec_gpv_fixp_induct_strong2 [case_names adm bottom step]:
  assumes "ccpo.admissible (fun_lub lub_spmf) (fun_ord (ord_spmf (=))) (\<lambda>f. P (\<lambda>c s. f (c, s)))"
  and "P (\<lambda>_ _. return_pmf None)"
  and "\<And>exec_gpv'.
    \<lbrakk> \<And>c s. ord_spmf (=) (exec_gpv' c s) (exec_gpv c s); 
      \<And>c s. ord_spmf (=) (exec_gpv' c s) (the_gpv c \<bind> case_generat (\<lambda>x. return_spmf (x, s)) (\<lambda>out c. callee s out \<bind> (\<lambda>(x, y). exec_gpv' (c x) y)));
      P exec_gpv' \<rbrakk>
    \<Longrightarrow> P (\<lambda>c s. the_gpv c \<bind> case_generat (\<lambda>x. return_spmf (x, s)) (\<lambda>out c. callee s out \<bind> (\<lambda>(x, y). exec_gpv' (c x) y)))"
  shows "P exec_gpv"
using assms
by(rule spmf.fixp_induct_strong2_uc[where P="\<lambda>f. P (curry f)" and U=case_prod and C=curry, OF exec_gpv.mono exec_gpv_def, simplified curry_case_prod, simplified curry_conv[abs_def] fun_ord_def split_paired_All prod.case case_prod_eta, OF refl]) blast+

end

lemma exec_gpv_conv_inline1:
  "exec_gpv callee gpv s = map_spmf projl (inline1 (\<lambda>s c. lift_spmf (callee s c) :: (_, unit, unit) gpv) gpv s)"
by(induction arbitrary: gpv s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono inline1.mono exec_gpv_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  (auto simp add: map_spmf_bind_spmf o_def spmf.map_comp bind_map_spmf split_def intro!: bind_spmf_cong[OF refl] split: generat.split)

lemma exec_gpv_simps:
  "exec_gpv callee gpv s =
   the_gpv gpv \<bind>
     case_generat (\<lambda>x. return_spmf (x, s))
     (\<lambda>out rpv. callee s out \<bind> (\<lambda>(x, y). exec_gpv callee (rpv x) y))"
by(fact exec_gpv.simps)

lemma exec_gpv_lift_spmf [simp]:
  "exec_gpv callee (lift_spmf p) s = bind_spmf p (\<lambda>x. return_spmf (x, s))"
by(simp add: exec_gpv_conv_inline1 spmf.map_comp o_def map_spmf_conv_bind_spmf)

lemma exec_gpv_Done [simp]: "exec_gpv callee (Done x) s = return_spmf (x, s)"
by(simp add: exec_gpv_conv_inline1)

lemma exec_gpv_Fail [simp]: "exec_gpv callee Fail s = return_pmf None"
by(simp add: exec_gpv_conv_inline1)

lemma if_distrib_exec_gpv [if_distribs]:
  "exec_gpv callee (if b then x else y) s = (if b then exec_gpv callee x s else exec_gpv callee y s)"
by simp

lemmas exec_gpv_fixp_parallel_induct [case_names adm bottom step] =
  parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono exec_gpv.mono exec_gpv_def exec_gpv_def, unfolded lub_spmf_empty]

context includes lifting_syntax begin

lemma exec_gpv_parametric':
  "((S ===> CALL ===> rel_spmf (rel_prod R S)) ===> rel_gpv'' A CALL R ===> S ===> rel_spmf (rel_prod A S))
  exec_gpv exec_gpv"
apply(rule rel_funI)+
apply(unfold spmf_rel_map exec_gpv_conv_inline1)
apply(rule rel_spmf_mono_strong)
 apply(erule inline1_parametric'[THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated])
  prefer 3
  apply(drule in_set_inline1_lift_spmf1)+
  apply fastforce
 subgoal by simp
subgoal premises [transfer_rule]
  supply lift_spmf_parametric'[transfer_rule] by transfer_prover
done

lemma exec_gpv_parametric [transfer_rule]:
  "((S ===> CALL ===> rel_spmf (rel_prod ((=) :: 'ret \<Rightarrow> _) S)) ===> rel_gpv A CALL ===> S ===> rel_spmf (rel_prod A S))
  exec_gpv exec_gpv"
unfolding rel_gpv_conv_rel_gpv'' by(rule exec_gpv_parametric')

end

lemma exec_gpv_bind: "exec_gpv callee (c \<bind> f) s = exec_gpv callee c s \<bind> (\<lambda>(x, s') \<Rightarrow> exec_gpv callee (f x) s')"
by(auto simp add: exec_gpv_conv_inline1 inline1_bind_gpv map_spmf_bind_spmf o_def bind_map_spmf intro!: bind_spmf_cong[OF refl] dest: in_set_inline1_lift_spmf1)

lemma exec_gpv_map_gpv_id:
  "exec_gpv oracle (map_gpv f id gpv) \<sigma> = map_spmf (apfst f) (exec_gpv oracle gpv \<sigma>)"
proof(rule sym)
  define gpv' where "gpv' = map_gpv f id gpv"
  have [transfer_rule]: "rel_gpv (\<lambda>x y. y = f x) (=) gpv gpv'"
    unfolding gpv'_def by(simp add: gpv.rel_map gpv.rel_refl)
  have "rel_spmf (rel_prod (\<lambda>x y. y = f x) (=)) (exec_gpv oracle gpv \<sigma>) (exec_gpv oracle gpv' \<sigma>)"
    by transfer_prover
  thus "map_spmf (apfst f) (exec_gpv oracle gpv \<sigma>) = exec_gpv oracle (map_gpv f id gpv) \<sigma>"
    unfolding spmf_rel_eq[symmetric] gpv'_def spmf_rel_map by(rule rel_spmf_mono) clarsimp
qed

lemma exec_gpv_Pause [simp]:
  "exec_gpv callee (Pause out f) s = callee s out \<bind> (\<lambda>(x, s'). exec_gpv callee (f x) s')"
by(simp add: inline1_Pause map_spmf_bind_spmf bind_map_spmf o_def exec_gpv_conv_inline1 split_def)

lemma exec_gpv_bind_lift_spmf:
  "exec_gpv callee (bind_gpv (lift_spmf p) f) s = bind_spmf p (\<lambda>x. exec_gpv callee (f x) s)"
by(simp add: exec_gpv_bind)

lemma exec_gpv_bind_option [simp]:
  "exec_gpv oracle (monad.bind_option Fail x f) s = monad.bind_option (return_pmf None) x (\<lambda>a. exec_gpv oracle (f a) s)"
by(cases x) simp_all

lemma pred_spmf_exec_gpv:
  \<comment> \<open>We don't get an equivalence here because states are threaded through in @{const exec_gpv}.\<close>
  "\<lbrakk> pred_gpv A C gpv; pred_fun S (pred_fun C (pred_spmf (pred_prod (\<lambda>_. True) S))) callee; S s \<rbrakk>
  \<Longrightarrow> pred_spmf (pred_prod A S) (exec_gpv callee gpv s)"
using exec_gpv_parametric[of "eq_onp S" "eq_onp C" "eq_onp A", folded eq_onp_True]
apply(unfold prod.rel_eq_onp option.rel_eq_onp pmf.rel_eq_onp gpv.rel_eq_onp)
apply(drule rel_funD[where x=callee and y=callee])
 subgoal
   apply(rule rel_fun_mono[where X="eq_onp S"])
     apply(rule rel_fun_eq_onpI)
     apply(unfold eq_onp_same_args)
     apply assumption
    apply simp
   apply(erule rel_fun_eq_onpI)
   done
apply(auto dest!: rel_funD simp add: eq_onp_def)
done

lemma exec_gpv_inline:
  fixes callee :: "('c, 'r, 's) callee"
  and gpv :: "'s' \<Rightarrow> 'c' \<Rightarrow> ('r' \<times> 's', 'c, 'r) gpv"
  shows "exec_gpv callee (inline gpv c' s') s =
    map_spmf (\<lambda>(x, s', s). ((x, s'), s)) (exec_gpv (\<lambda>(s', s) y. map_spmf (\<lambda>((x, s'), s). (x, s', s)) (exec_gpv callee (gpv s' y) s)) c' (s', s))"
    (is "?lhs = ?rhs")
proof -
  have "?lhs = map_spmf projl (map_spmf (map_sum (\<lambda>(x, s2, y). ((x, s2), y))
        (\<lambda>(x, rpv'' :: ('r \<times> 's, unit, unit) rpv, rpv', rpv). (x, rpv'', \<lambda>r1. bind_gpv (rpv' r1) (\<lambda>(r2, y). inline gpv (rpv r2) y))))
      (inline2 (\<lambda>s c. lift_spmf (callee s c)) gpv c' s' s))"
    unfolding exec_gpv_conv_inline1 by(simp add: inline1_inline_conv_inline2)
  also have "\<dots> = map_spmf (\<lambda>(x, s', s). ((x, s'), s)) (map_spmf projl (map_spmf (map_sum id
        (\<lambda>(x, rpv'' :: ('r \<times> 's, unit, unit) rpv, rpv', rpv). (x, \<lambda>r. bind_gpv (rpv'' r) (\<lambda>(r1, s1). map_gpv (\<lambda>((r2, s2), s1). (r2, s2, s1)) id (inline (\<lambda>s c. lift_spmf (callee s c)) (rpv' r1) s1)), rpv)))
      (inline2 (\<lambda>s c. lift_spmf (callee s c)) gpv c' s' s)))"
   unfolding spmf.map_comp by(rule map_spmf_cong[OF refl])(auto dest!: in_set_inline2_lift_spmf1)
  also have "\<dots> = ?rhs" unfolding exec_gpv_conv_inline1
    by(subst inline1_inline_conv_inline2'[symmetric])(simp add: spmf.map_comp split_def inline_lift_spmf1 map_lift_spmf)
  finally show ?thesis .
qed

lemma ord_spmf_exec_gpv:
  assumes callee: "\<And>s x. ord_spmf (=) (callee1 s x) (callee2 s x)"
  shows "ord_spmf (=) (exec_gpv callee1 gpv s) (exec_gpv callee2 gpv s)"
proof(induction arbitrary: gpv s rule: exec_gpv_fixp_parallel_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
next
  case (step exec_gpv1 exec_gpv2)
  show ?case using step.prems
    by(clarsimp intro!: ord_spmf_bind_reflI ord_spmf_bindI[OF assms] step.IH split!: generat.split)
qed

context fixes callee :: "('call, 'ret, 's) callee" notes [[function_internals]] begin

partial_function (spmf) execp_resumption :: "('a, 'call, 'ret) resumption \<Rightarrow> 's \<Rightarrow> ('a \<times> 's) spmf"
where
  "execp_resumption r s = (case r of resumption.Done x \<Rightarrow> return_pmf (map_option (\<lambda>a. (a, s)) x)
      | resumption.Pause out c \<Rightarrow> bind_spmf (callee s out) (\<lambda>(input, s'). execp_resumption (c input) s'))"

simps_of_case execp_resumption_simps [simp]: execp_resumption.simps

lemma execp_resumption_ABORT [simp]: "execp_resumption ABORT s = return_pmf None"
by(simp add: ABORT_def)

lemma execp_resumption_DONE [simp]: "execp_resumption (DONE x) s = return_spmf (x, s)"
by(simp add: DONE_def)

lemma exec_gpv_lift_resumption: "exec_gpv callee (lift_resumption r) s = execp_resumption r s"
proof(induction arbitrary: r s rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono execp_resumption.mono exec_gpv_def execp_resumption_def, case_names adm bot step])
  case adm show ?case by(simp)
  case bot thus ?case by simp
  case (step exec_gpv' execp_resumption')
  show ?case
    by(auto split: resumption.split option.split simp add: lift_resumption.sel intro: bind_spmf_cong step)
qed

lemma mcont2mcont_execp_resumption [THEN spmf.mcont2mcont, cont_intro, simp]:
  shows mcont_execp_resumption:
  "mcont resumption_lub resumption_ord lub_spmf (ord_spmf (=)) (\<lambda>r. execp_resumption r s)"
proof -
  have "mcont (prod_lub resumption_lub the_Sup) (rel_prod resumption_ord (=)) lub_spmf (ord_spmf (=)) (case_prod execp_resumption)"
  proof(rule ccpo.fixp_preserves_mcont2[OF ccpo_spmf execp_resumption.mono execp_resumption_def])
    fix execp_resumption' :: "('b, 'call, 'ret) resumption \<Rightarrow> 's \<Rightarrow> ('b \<times> 's) spmf"
    assume *: "mcont (prod_lub resumption_lub the_Sup) (rel_prod resumption_ord (=)) lub_spmf (ord_spmf (=)) (\<lambda>(r, s). execp_resumption' r s)"
    have [THEN spmf.mcont2mcont, cont_intro, simp]: "mcont resumption_lub resumption_ord lub_spmf (ord_spmf (=)) (\<lambda>r. execp_resumption' r s)" 
      for s using * by simp
    have "mcont resumption_lub resumption_ord lub_spmf (ord_spmf (=))
      (\<lambda>r. case r of resumption.Done x \<Rightarrow> return_pmf (map_option (\<lambda>a. (a, s)) x)
           | resumption.Pause out c \<Rightarrow> bind_spmf (callee s out) (\<lambda>(input, s'). execp_resumption' (c input) s'))"
      for s by(rule mcont_case_resumption)(auto simp add: ccpo_spmf intro!: mcont_bind_spmf)
    thus "mcont (prod_lub resumption_lub the_Sup) (rel_prod resumption_ord (=)) lub_spmf (ord_spmf (=))
          (\<lambda>(r, s). case r of resumption.Done x \<Rightarrow> return_pmf (map_option (\<lambda>a. (a, s)) x)
              | resumption.Pause out c \<Rightarrow> bind_spmf (callee s out) (\<lambda>(input, s'). execp_resumption' (c input) s'))"
      by simp
  qed
  thus ?thesis by auto
qed


lemma execp_resumption_bind [simp]:
  "execp_resumption (r \<bind> f) s = execp_resumption r s \<bind> (\<lambda>(x, s'). execp_resumption (f x) s')"
by(simp add: exec_gpv_lift_resumption[symmetric] lift_resumption_bind exec_gpv_bind)

lemma pred_spmf_execp_resumption:
  "\<And>A. \<lbrakk> pred_resumption A C r; pred_fun S (pred_fun C (pred_spmf (pred_prod (\<lambda>_. True) S))) callee; S s \<rbrakk>
  \<Longrightarrow> pred_spmf (pred_prod A S) (execp_resumption r s)"
unfolding exec_gpv_lift_resumption[symmetric]
by(rule pred_spmf_exec_gpv) simp_all

end

inductive WT_callee :: "('call, 'ret) \<I> \<Rightarrow> ('call \<Rightarrow> ('ret \<times> 's) spmf) \<Rightarrow> bool" ("(_) \<turnstile>c/ (_) \<surd>" [100, 0] 99)
  for \<I> callee
where
  WT_callee:
  "\<lbrakk> \<And>call ret s. \<lbrakk> call \<in> outs_\<I> \<I>; (ret, s) \<in> set_spmf (callee call) \<rbrakk> \<Longrightarrow> ret \<in> responses_\<I> \<I> call \<rbrakk>
  \<Longrightarrow> \<I> \<turnstile>c callee \<surd>"

lemmas WT_calleeI = WT_callee
hide_fact WT_callee

lemma WT_calleeD: "\<lbrakk> \<I> \<turnstile>c callee \<surd>; (ret, s) \<in> set_spmf (callee out); out \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> ret \<in> responses_\<I> \<I> out"
by(rule WT_callee.cases)

lemma WT_callee_full [intro!, simp]: "\<I>_full \<turnstile>c callee \<surd>"
by(rule WT_calleeI) simp

lemma WT_callee_parametric [transfer_rule]:
  includes lifting_syntax 
  assumes [transfer_rule]: "bi_unique R"
  shows "(rel_\<I> C R ===> (C ===> rel_spmf (rel_prod R S)) ===> (=)) WT_callee WT_callee"
proof -
  have *: "WT_callee = (\<lambda>\<I> callee. \<forall>call\<in> outs_\<I> \<I>. \<forall>(ret, s) \<in> set_spmf (callee call). ret \<in> responses_\<I> \<I> call)"
    unfolding WT_callee.simps by blast
  show ?thesis unfolding * by transfer_prover
qed

locale callee_invariant_on_base =
  fixes callee :: "'s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's) spmf"
  and I :: "'s \<Rightarrow> bool"
  and \<I> :: "('a, 'b) \<I>"

locale callee_invariant_on = callee_invariant_on_base callee I \<I>
  for callee :: "'s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's) spmf"
  and I :: "'s \<Rightarrow> bool"
  and \<I> :: "('a, 'b) \<I>"
  +
  assumes callee_invariant: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> I s'"
  and WT_callee: "\<And>s. I s \<Longrightarrow> \<I> \<turnstile>c callee s \<surd>"
begin

lemma callee_invariant': "\<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> I s' \<and> y \<in> responses_\<I> \<I> x"
by(auto dest: WT_calleeD[OF WT_callee] callee_invariant)

lemma exec_gpv_invariant':
  "\<lbrakk> I s; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> set_spmf (exec_gpv callee gpv s) \<subseteq> {(x, s'). I s'}"
proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
  case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
  case bottom show ?case by simp
  case step show ?case using step.prems
    by(auto simp add: bind_UNION intro!: UN_least step.IH del: subsetI split: generat.split dest!: callee_invariant' elim: WT_gpvD)
qed

lemma exec_gpv_invariant:
  "\<lbrakk> (x, s') \<in> set_spmf (exec_gpv callee gpv s); I s; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> I s'"
by(drule exec_gpv_invariant') blast+

lemma interaction_bounded_by_exec_gpv_count':
  fixes count
  assumes bound: "interaction_bounded_by consider gpv n"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> eSuc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "set_spmf (exec_gpv callee gpv s) \<subseteq> {(x, s'). count s' \<le> n + count s}"
using bound I WT
proof(induction arbitrary: gpv s n rule: exec_gpv_fixp_induct)
  case adm show ?case by(intro cont_intro ccpo_class.admissible_leI)
  case bottom show ?case by simp
  case (step exec_gpv')
  have "set_spmf (exec_gpv' (c input) s') \<subseteq> {(x, s''). count s'' \<le> n + count s}"
    if out: "IO out c \<in> set_spmf (the_gpv gpv)"
    and input: "(input, s') \<in> set_spmf (callee s out)"
    and X: "out \<in> outs_\<I> \<I>"
    for out c input s'
  proof(cases "consider out")
    case True
    with step.prems out have "n > 0"
      and bound': "interaction_bounded_by consider (c input) (n - 1)"
      by(auto dest: interaction_bounded_by_contD)
    note bound'
    moreover from input \<open>I s\<close> X have "I s'" by(rule callee_invariant)
    moreover have "\<I> \<turnstile>g c input \<surd>" using step.prems(3) out WT_calleeD[OF WT_callee input]
      by(rule WT_gpvD)(rule step.prems X)+
    ultimately have "set_spmf (exec_gpv' (c input) s') \<subseteq> {(x, s''). count s'' \<le> n - 1 + count s'}"      
      by(rule step.IH)
    also have "\<dots> \<subseteq> {(x, s''). count s'' \<le> n + count s}" using \<open>n > 0\<close> count[OF input \<open>I s\<close> True X]     
      by(cases n rule: co.enat.exhaust)(auto, metis add_left_mono_trans eSuc_plus iadd_Suc_right)
    finally show ?thesis .
  next
    case False
    from step.prems out this have bound': "interaction_bounded_by consider (c input) n"
      by(auto dest: interaction_bounded_by_contD_ignore)
    from input \<open>I s\<close> X have "I s'" by(rule callee_invariant)
    note bound'
    moreover from input \<open>I s\<close> X have "I s'" by(rule callee_invariant)
    moreover have "\<I> \<turnstile>g c input \<surd>" using step.prems(3) out WT_calleeD[OF WT_callee input]
      by(rule WT_gpvD)(rule step.prems X)+
    ultimately have "set_spmf (exec_gpv' (c input) s') \<subseteq> {(x, s''). count s'' \<le> n + count s'}"
      by(rule step.IH)
    also have "\<dots> \<subseteq> {(x, s''). count s'' \<le> n + count s}"
      using ignore[OF input \<open>I s\<close> False X] by(auto elim: order_trans)
    finally show ?thesis .
  qed
  then show ?case using step.prems(3)
    by(auto 4 3 simp add: bind_UNION del: subsetI intro!: UN_least split: generat.split dest: WT_gpvD)
qed

lemma interaction_bounded_by_exec_gpv_count:
  fixes count
  assumes bound: "interaction_bounded_by consider gpv n"
  and xs': "(x, s') \<in> set_spmf (exec_gpv callee gpv s)"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> eSuc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and WT: "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "count s' \<le> n + count s"
using bound count ignore WT I 
by(rule interaction_bounded_by_exec_gpv_count'[THEN subsetD, OF _ _ _ _ _ xs', unfolded mem_Collect_eq prod.case])

lemma interaction_bounded_by'_exec_gpv_count:
  fixes count
  assumes bound: "interaction_bounded_by' consider gpv n"
  and xs': "(x, s') \<in> set_spmf (exec_gpv callee gpv s)"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> Suc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and outs: "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "count s' \<le> n + count s"
using interaction_bounded_by_exec_gpv_count[OF bound xs', of count] count ignore outs I
by(simp add: eSuc_enat)

lemma pred_spmf_calleeI: "\<lbrakk> I s; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> pred_spmf (pred_prod (\<lambda>_. True) I) (callee s x)"
by(auto simp add: pred_spmf_def dest: callee_invariant)

lemma lossless_exec_gpv:
  assumes gpv: "lossless_gpv \<I> gpv"
  and callee: "\<And>s out. \<lbrakk> out \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> lossless_spmf (callee s out)"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "lossless_spmf (exec_gpv callee gpv s)"
using gpv WT_gpv I
proof(induction arbitrary: s rule: lossless_WT_gpv_induct)
  case (lossless_gpv gpv)
  show ?case using lossless_gpv.hyps lossless_gpv.prems
    by(subst exec_gpv.simps)(fastforce split: generat.split simp add: callee intro!: lossless_gpv.IH intro: WT_calleeD[OF WT_callee] elim!: callee_invariant)
qed

lemma in_set_spmf_exec_gpv_into_results_gpv:
  assumes *: "(x, s') \<in> set_spmf (exec_gpv callee gpv s)"
  and WT_gpv : "\<I> \<turnstile>g gpv \<surd>"
  and I: "I s"
  shows "x \<in> results_gpv \<I> gpv"
proof -
  have "set_spmf (exec_gpv callee gpv s) \<subseteq> results_gpv \<I> gpv \<times> UNIV"
    using WT_gpv I
  proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
    { case adm show ?case by(intro cont_intro ccpo_class.admissible_leI) }
    { case bottom show ?case by simp }
    case (step exec_gpv')
    { fix out c ret s'
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
        and ret: "(ret, s') \<in> set_spmf (callee s out)"
      from step.prems(1) IO have "out \<in> outs_\<I> \<I>" by(rule WT_gpvD)
      with WT_callee[OF \<open>I s\<close>] ret have "ret \<in> responses_\<I> \<I> out" by(rule WT_calleeD)
      with step.prems(1) IO have "\<I> \<turnstile>g c ret \<surd>" by(rule WT_gpvD)
      moreover from ret \<open>I s\<close> \<open>out \<in> outs_\<I> \<I>\<close> have "I s'" by(rule callee_invariant)
      ultimately have "set_spmf (exec_gpv' (c ret) s') \<subseteq> results_gpv \<I> (c ret) \<times> UNIV"
        by(rule step.IH)
      also have "\<dots> \<subseteq> results_gpv \<I> gpv \<times> UNIV" using IO \<open>ret \<in> _\<close>
        by(auto intro: results_gpv.IO)
      finally have "set_spmf (exec_gpv' (c ret) s') \<subseteq> results_gpv \<I> gpv \<times> UNIV" . }
    then show ?case using step.prems
      by(auto simp add: bind_UNION intro!: UN_least del: subsetI split: generat.split intro: results_gpv.Pure)
  qed
  thus "x \<in> results_gpv \<I> gpv" using * by blast+
qed

end

lemma callee_invariant_on_alt_def:
  "callee_invariant_on = (\<lambda>callee I \<I>.
    (\<forall>s \<in> Collect I. \<forall>x \<in> outs_\<I> \<I>. \<forall>(y, s') \<in> set_spmf (callee s x). I s') \<and>
    (\<forall>s \<in> Collect I. \<I> \<turnstile>c callee s \<surd>))"
unfolding callee_invariant_on_def by blast

lemma callee_invariant_on_parametric [transfer_rule]: includes lifting_syntax
  assumes [transfer_rule]: "bi_unique R" "bi_total S"
  shows "((S ===> C ===> rel_spmf (rel_prod R S)) ===> (S ===> (=)) ===> rel_\<I> C R ===> (=))
    callee_invariant_on callee_invariant_on"
unfolding callee_invariant_on_alt_def by transfer_prover

lemma callee_invariant_on_cong:
  "\<lbrakk> I = I'; outs_\<I> \<I> = outs_\<I> \<I>'; 
    \<And>s x. \<lbrakk> I' s; x \<in> outs_\<I> \<I>' \<rbrakk> \<Longrightarrow> set_spmf (callee s x) \<subseteq> responses_\<I> \<I> x \<times> Collect I' \<longleftrightarrow> set_spmf (callee' s x) \<subseteq> responses_\<I> \<I>' x \<times> Collect I' \<rbrakk>
  \<Longrightarrow> callee_invariant_on callee I \<I> = callee_invariant_on callee' I' \<I>'"
unfolding callee_invariant_on_def WT_callee.simps
by safe((erule meta_allE)+, (erule (1) meta_impE)+, force)+ 

abbreviation callee_invariant :: "('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's) spmf) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> bool"
where "callee_invariant callee I \<equiv> callee_invariant_on callee I \<I>_full"

interpretation oi_True: callee_invariant_on callee "\<lambda>_. True" \<I>_full for callee
by unfold_locales (simp_all)

lemma callee_invariant_on_return_spmf [simp]:
  "callee_invariant_on (\<lambda>s x. return_spmf (f s x)) I \<I> \<longleftrightarrow> (\<forall>s. \<forall>x\<in>outs_\<I> \<I>. I s \<longrightarrow> I (snd (f s x)) \<and> fst (f s x) \<in> responses_\<I> \<I> x)"
by(auto simp add: callee_invariant_on_def split_pairs WT_callee.simps)

lemma callee_invariant_return_spmf [simp]:
  "callee_invariant (\<lambda>s x. return_spmf (f s x)) I \<longleftrightarrow> (\<forall>s x. I s \<longrightarrow> I (snd (f s x)))"
by(auto simp add: callee_invariant_on_def split_pairs)

lemma callee_invariant_restrict_relp:
  includes lifting_syntax
  assumes "(S ===> C ===> rel_spmf (rel_prod R S)) callee1 callee2"
  and "callee_invariant callee1 I1"
  and "callee_invariant callee2 I2"
  shows "((S \<upharpoonleft> I1 \<otimes> I2) ===> C ===> rel_spmf (rel_prod R (S \<upharpoonleft> I1 \<otimes> I2))) callee1 callee2"
proof -
  interpret ci1: callee_invariant_on callee1 I1 \<I>_full by fact
  interpret ci2: callee_invariant_on callee2 I2 \<I>_full by fact
  show ?thesis using assms(1)
    by(intro rel_funI)(auto simp add: restrict_rel_prod2 intro!: rel_spmf_restrict_relpI intro: ci1.pred_spmf_calleeI ci2.pred_spmf_calleeI dest: rel_funD rel_setD1 rel_setD2)
qed

lemma callee_invariant_on_True [simp]: "callee_invariant_on callee (\<lambda>_. True) \<I> \<longleftrightarrow> (\<forall>s. \<I> \<turnstile>c callee s \<surd>)"
by(simp add: callee_invariant_on_def)

lemma lossless_exec_gpv:
  "\<lbrakk> lossless_gpv \<I> gpv;  \<And>s out. out \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (callee s out);
     \<I> \<turnstile>g gpv \<surd>; \<And>s. \<I> \<turnstile>c callee s \<surd> \<rbrakk>
  \<Longrightarrow> lossless_spmf (exec_gpv callee gpv s)"
by(rule callee_invariant_on.lossless_exec_gpv; simp)

lemma in_set_spmf_exec_gpv_into_results'_gpv:
  assumes *: "(x, s') \<in> set_spmf (exec_gpv callee gpv s)"
  shows "x \<in> results'_gpv gpv"
using oi_True.in_set_spmf_exec_gpv_into_results_gpv[OF *] by(simp add: results_gpv_\<I>_full)


context fixes \<I> :: "('out, 'in) \<I>" begin

primcorec restrict_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> ('a, 'out, 'in) gpv"
where
  "restrict_gpv gpv = GPV (
  map_pmf (case_option None (case_generat (Some \<circ> Pure) 
       (\<lambda>out c. if out \<in> outs_\<I> \<I> then Some (IO out (\<lambda>input. if input \<in> responses_\<I> \<I> out then restrict_gpv (c input) else Fail))
          else None)))
    (the_gpv gpv))" 

lemma restrict_gpv_Done [simp]: "restrict_gpv (Done x) = Done x"
by(rule gpv.expand)(simp)

lemma restrict_gpv_Fail [simp]: "restrict_gpv Fail = Fail"
by(rule gpv.expand)(simp)

lemma restrict_gpv_Pause [simp]: "restrict_gpv (Pause out c) = (if out \<in> outs_\<I> \<I> then Pause out (\<lambda>input. if input \<in> responses_\<I> \<I> out then restrict_gpv (c input) else Fail) else Fail)"
by(rule gpv.expand)(simp)

lemma restrict_gpv_bind [simp]: "restrict_gpv (bind_gpv gpv f) = bind_gpv (restrict_gpv gpv) (\<lambda>x. restrict_gpv (f x))"
apply(coinduction arbitrary: gpv rule: gpv.coinduct_strong)
apply(auto 4 3 simp del: bind_gpv_sel' simp add: bind_gpv.sel bind_spmf_def pmf.rel_map bind_map_pmf rel_fun_def intro!: rel_pmf_bind_reflI rel_pmf_reflI split!: option.split generat.split split: if_split_asm)
done

lemma WT_restrict_gpv [simp]: "\<I> \<turnstile>g restrict_gpv gpv \<surd>"
apply(coinduction arbitrary: gpv)
apply(clarsimp split: option.split_asm)
apply(split generat.split_asm; auto split: if_split_asm)
done

lemma exec_gpv_restrict_gpv:
  assumes "\<I> \<turnstile>g gpv \<surd>" and WT_callee: "\<And>s. \<I> \<turnstile>c callee s \<surd>"
  shows "exec_gpv callee (restrict_gpv gpv) s = exec_gpv callee gpv s"
using assms(1)
proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step exec_gpv') show ?case 
    by(auto 4 3 simp add: bind_spmf_def bind_map_pmf in_set_spmf[symmetric] WT_gpv_OutD[OF step.prems] WT_calleeD[OF WT_callee] intro!: bind_pmf_cong[OF refl] step.IH split!: option.split generat.split intro: WT_gpv_ContD[OF step.prems])
qed

lemma in_outs'_restrict_gpvD: "x \<in> outs'_gpv (restrict_gpv gpv) \<Longrightarrow> x \<in> outs_\<I> \<I>"
apply(induction gpv'\<equiv>"restrict_gpv gpv" arbitrary: gpv rule: outs'_gpv_induct)
apply(clarsimp split: option.split_asm; split generat.split_asm; clarsimp split: if_split_asm)+
done

lemma outs'_restrict_gpv: "outs'_gpv (restrict_gpv gpv) \<subseteq> outs_\<I> \<I>" by(blast intro: in_outs'_restrict_gpvD)

lemma lossless_restrict_gpvI: "\<lbrakk> lossless_gpv \<I> gpv; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> lossless_gpv \<I> (restrict_gpv gpv)"
apply(induction rule: lossless_gpv_induct)
apply(rule lossless_gpvI)
subgoal by(clarsimp simp add: lossless_map_pmf lossless_iff_set_pmf_None in_set_spmf[symmetric] WT_gpv_OutD split: option.split_asm generat.split_asm if_split_asm)
subgoal by(clarsimp split: option.split_asm; split generat.split_asm; force simp add: fun_eq_iff in_set_spmf[symmetric] split: if_split_asm intro: WT_gpv_ContD)
done

lemma lossless_restrict_gpvD: "\<lbrakk> lossless_gpv \<I> (restrict_gpv gpv); \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> lossless_gpv \<I> gpv"
proof(induction gpv'\<equiv>"restrict_gpv gpv" arbitrary: gpv rule: lossless_gpv_induct)
  case (lossless_gpv p)
  from lossless_gpv.hyps(4) have p: "p = the_gpv (restrict_gpv gpv)" by(cases "restrict_gpv gpv") simp
  show ?case
  proof(rule lossless_gpvI) 
    from lossless_gpv.hyps(1) show "lossless_spmf (the_gpv gpv)"
      by(auto simp add: p lossless_iff_set_pmf_None intro: rev_image_eqI)

    fix out c input
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" and input: "input \<in> responses_\<I> \<I> out"
    from lossless_gpv.prems(1) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    hence "IO out (\<lambda>input. if input \<in> responses_\<I> \<I> out then restrict_gpv (c input) else Fail) \<in> set_spmf p" using IO
      by(auto simp add: p in_set_spmf intro: rev_bexI)
    from lossless_gpv.hyps(3)[OF this input, of "c input"] WT_gpvD[OF lossless_gpv.prems IO] input
    show "lossless_gpv \<I> (c input)" by simp
  qed
qed
  
lemma colossless_restrict_gpvD:
  "\<lbrakk> colossless_gpv \<I> (restrict_gpv gpv); \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> colossless_gpv \<I> gpv"
proof(coinduction arbitrary: gpv)
  case (colossless_gpv gpv)
  have ?lossless_spmf using colossless_gpv(1)[THEN colossless_gpv_lossless_spmfD]
    by(auto simp add: lossless_iff_set_pmf_None intro: rev_image_eqI)
  moreover have ?continuation
  proof(intro strip disjI1)
    fix out c input
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" and input: "input \<in> responses_\<I> \<I> out"
    from colossless_gpv(2) IO have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    hence "IO out (\<lambda>input. if input \<in> responses_\<I> \<I> out then restrict_gpv (c input) else Fail) \<in> set_spmf (the_gpv (restrict_gpv gpv))"
      using IO by(auto simp add: in_set_spmf intro: rev_bexI)
    from colossless_gpv_continuationD[OF colossless_gpv(1) this input] input WT_gpv_ContD[OF colossless_gpv(2) IO input]
    show "\<exists>gpv. c input = gpv \<and> colossless_gpv \<I> (restrict_gpv gpv) \<and> \<I> \<turnstile>g gpv \<surd>" by simp
  qed
  ultimately show ?case ..
qed

lemma colossless_restrict_gpvI:
  "\<lbrakk> colossless_gpv \<I> gpv; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> colossless_gpv \<I> (restrict_gpv gpv)"
proof(coinduction arbitrary: gpv)
  case (colossless_gpv gpv)
  have ?lossless_spmf using colossless_gpv(1)[THEN colossless_gpv_lossless_spmfD]
    by(auto simp add: lossless_iff_set_pmf_None in_set_spmf[symmetric] split: option.split_asm generat.split_asm if_split_asm dest: WT_gpv_OutD[OF colossless_gpv(2)])
  moreover have ?continuation
  proof(intro strip disjI1)
    fix out c input
    assume IO: "IO out c \<in> set_spmf (the_gpv (restrict_gpv gpv))" and input: "input \<in> responses_\<I> \<I> out"
    then obtain c' where out: "out \<in> outs_\<I> \<I>"
      and c: "c = (\<lambda>input. if input \<in> responses_\<I> \<I> out then restrict_gpv (c' input) else Fail)"
      and IO': "IO out c' \<in> set_spmf (the_gpv gpv)"
      by(clarsimp split: option.split_asm; split generat.split_asm; clarsimp simp add: in_set_spmf split: if_split_asm)
    with input WT_gpv_ContD[OF colossless_gpv(2) IO' input] colossless_gpv_continuationD[OF colossless_gpv(1) IO' input]
    show "\<exists>gpv. c input = restrict_gpv gpv \<and> colossless_gpv \<I> gpv \<and> \<I> \<turnstile>g gpv \<surd>" by(auto)
  qed
  ultimately show ?case ..
qed

lemma gen_colossless_restrict_gpv [simp]:
  "\<I> \<turnstile>g gpv \<surd> \<Longrightarrow> gen_lossless_gpv b \<I> (restrict_gpv gpv) \<longleftrightarrow> gen_lossless_gpv b \<I> gpv"
by(cases b)(auto intro: lossless_restrict_gpvI lossless_restrict_gpvD colossless_restrict_gpvI colossless_restrict_gpvD)

lemma interaction_bound_restrict_gpv:
  "interaction_bound consider (restrict_gpv gpv) \<le> interaction_bound consider gpv"
proof(induction arbitrary: gpv rule: interaction_bound_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step interaction_bound')
  show ?case using step.hyps(1)[of Fail]
    by(fastforce simp add: SUP_UNION set_spmf_def bind_UNION intro: SUP_mono rev_bexI step.IH split: option.split generat.split)
qed

lemma interaction_bounded_by_restrict_gpvI [interaction_bound, simp]:
  "interaction_bounded_by consider gpv n \<Longrightarrow> interaction_bounded_by consider (restrict_gpv gpv) n"
using interaction_bound_restrict_gpv[of "consider" gpv] by(simp add: interaction_bounded_by.simps)

end

lemma restrict_gpv_parametric':
  includes lifting_syntax
  notes [transfer_rule] = the_gpv_parametric' Fail_parametric' corec_gpv_parametric'
  assumes [transfer_rule]: "bi_unique C" "bi_unique R"
  shows "(rel_\<I> C R ===> rel_gpv'' A C R ===> rel_gpv'' A C R) restrict_gpv restrict_gpv"
unfolding restrict_gpv_def by transfer_prover

lemma restrict_gpv_parametric [transfer_rule]: includes lifting_syntax shows 
  "bi_unique C \<Longrightarrow> (rel_\<I> C (=) ===> rel_gpv A C ===> rel_gpv A C) restrict_gpv restrict_gpv"
using restrict_gpv_parametric'[of C "(=)" A]
by(simp add: bi_unique_eq rel_gpv_conv_rel_gpv'')

lemma map_restrict_gpv: "map_gpv f id (restrict_gpv \<I> gpv) = restrict_gpv \<I> (map_gpv f id gpv)"
  for gpv :: "('a, 'out, 'ret) gpv"
using restrict_gpv_parametric[of "BNF_Def.Grp UNIV (id :: 'out \<Rightarrow> 'out)" "BNF_Def.Grp UNIV f", where ?'c='ret]
unfolding gpv.rel_Grp by(simp add: eq_alt[symmetric] rel_\<I>_eq rel_fun_def bi_unique_eq)(simp add: Grp_def)

lemma (in callee_invariant_on) exec_gpv_restrict_gpv_invariant:
  assumes "\<I> \<turnstile>g gpv \<surd>" and "I s"
  shows "exec_gpv callee (restrict_gpv \<I> gpv) s = exec_gpv callee gpv s"
using assms
proof(induction arbitrary: gpv s rule: exec_gpv_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step exec_gpv') show ?case using step.prems(2)
    by(auto 4 3 simp add: bind_spmf_def bind_map_pmf in_set_spmf[symmetric] WT_gpv_OutD[OF step.prems(1)] WT_calleeD[OF WT_callee[OF step.prems(2)]] intro!: bind_pmf_cong[OF refl] step.IH split!: option.split generat.split intro: WT_gpv_ContD[OF step.prems(1)] callee_invariant)
qed

context fixes \<I> :: "('out, 'in) \<I>" begin

inductive finite_gpv :: "('a, 'out, 'in) gpv \<Rightarrow> bool"
where
  finite_gpvI: 
  "(\<And>out c input. \<lbrakk> IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out \<rbrakk> \<Longrightarrow> finite_gpv (c input)) \<Longrightarrow> finite_gpv gpv"

lemmas finite_gpv_induct[consumes 1, case_names finite_gpv, induct pred] = finite_gpv.induct

lemma finite_gpvD: "\<lbrakk> finite_gpv gpv; IO out c \<in> set_spmf (the_gpv gpv); input \<in> responses_\<I> \<I> out \<rbrakk> \<Longrightarrow> finite_gpv (c input)"
by(auto elim: finite_gpv.cases)

lemma finite_gpv_Fail [simp]: "finite_gpv Fail"
by(auto intro: finite_gpvI)

lemma finite_gpv_Done [simp]: "finite_gpv (Done x)"
by(auto intro: finite_gpvI)

lemma finite_gpv_Pause [simp]: "finite_gpv (Pause x c) \<longleftrightarrow> (\<forall>input \<in> responses_\<I> \<I> x. finite_gpv (c input))"
by(auto dest: finite_gpvD intro: finite_gpvI)

lemma finite_gpv_lift_spmf [simp]: "finite_gpv (lift_spmf p)"
by(auto intro: finite_gpvI)

lemma finite_gpv_bind [simp]:
  "finite_gpv (gpv \<bind> f) \<longleftrightarrow> finite_gpv gpv \<and> (\<forall>x\<in>results_gpv \<I> gpv. finite_gpv (f x))"
  (is "?lhs = ?rhs")
proof(intro iffI conjI ballI; (elim conjE)?)
  show "finite_gpv gpv" if "?lhs" using that
  proof(induction gpv'\<equiv>"gpv \<bind> f" arbitrary: gpv)
    case finite_gpv
    show ?case
    proof(rule finite_gpvI)
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
        and input: "input \<in> responses_\<I> \<I> out"
      have "IO out (\<lambda>input. c input \<bind> f) \<in> set_spmf (the_gpv (gpv \<bind> f))"
        using IO by(auto intro: rev_bexI)
      thus "finite_gpv (c input)" using input by(rule finite_gpv.hyps) simp
    qed
  qed
  show "finite_gpv (f x)" if "x \<in> results_gpv \<I> gpv" ?lhs for x using that
  proof(induction)
    case (Pure gpv)
    show ?case
    proof
      fix out c input
      assume "IO out c \<in> set_spmf (the_gpv (f x))" "input \<in> responses_\<I> \<I> out"
      with Pure have "IO out c \<in> set_spmf (the_gpv (gpv \<bind> f))" by(auto intro: rev_bexI)
      with Pure.prems show "finite_gpv (c input)" by(rule finite_gpvD) fact
    qed
  next
    case (IO out c gpv input)
    with IO.hyps have "IO out (\<lambda>input. c input \<bind> f) \<in> set_spmf (the_gpv (gpv \<bind> f))"
      by(auto intro: rev_bexI)
    with IO.prems have "finite_gpv (c input \<bind> f)" using IO.hyps(2) by(rule finite_gpvD)
    thus ?case by(rule IO.IH)
  qed
  show ?lhs if "finite_gpv gpv" "\<forall>x\<in>results_gpv \<I> gpv. finite_gpv (f x)" using that
  proof induction
    case (finite_gpv gpv)
    show ?case
    proof(rule finite_gpvI)
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv (gpv \<bind> f))" and input: "input \<in> responses_\<I> \<I> out"
      then obtain generat where generat: "generat \<in> set_spmf (the_gpv gpv)"
        and IO: "IO out c \<in> set_spmf (if is_Pure generat then the_gpv (f (result generat)) else
                   return_spmf (IO (output generat) (\<lambda>input. continuation generat input \<bind> f)))"
        by(auto)
      show "finite_gpv (c input)"
      proof(cases generat)
        case (Pure x)
        with generat IO have "x \<in> results_gpv \<I> gpv" "IO out c \<in> set_spmf (the_gpv (f x))"
          by(auto intro: results_gpv.Pure)
        thus ?thesis using finite_gpv.prems input by(auto dest: finite_gpvD)
      next
        case *: (IO out' c')
        with IO generat finite_gpv.prems input show ?thesis
          by(auto 4 4 intro: finite_gpv.IH results_gpv.IO)
      qed
    qed
  qed
qed

end

context includes lifting_syntax begin

lemma finite_gpv_rel''D1:
  assumes "rel_gpv'' A C R gpv gpv'" and "finite_gpv \<I> gpv" and \<I>: "rel_\<I> C R \<I> \<I>'"
  shows "finite_gpv \<I>' gpv'"
using assms(2,1)
proof(induction arbitrary: gpv')
  case (finite_gpv gpv)
  note finite_gpv.prems[transfer_rule]
  show ?case
  proof(rule finite_gpvI)
    fix out' c' input'
    assume IO: "IO out' c' \<in> set_spmf (the_gpv gpv')" and input': "input' \<in> responses_\<I> \<I>' out'"
    have "rel_set (rel_generat A C (R ===> (rel_gpv'' A C R))) (set_spmf (the_gpv gpv)) (set_spmf (the_gpv gpv'))"
      supply the_gpv_parametric'[transfer_rule] by transfer_prover
    with IO input' responses_\<I>_parametric[THEN rel_funD, OF \<I>] obtain out c input
      where "IO out c \<in> set_spmf (the_gpv gpv)" "input \<in> responses_\<I> \<I> out" "rel_gpv'' A C R (c input) (c' input')"
      by(auto 4 3 dest!: rel_setD2 elim!: generat.rel_cases dest: rel_funD)
    then show "finite_gpv \<I>' (c' input')" by(rule finite_gpv.IH)
  qed
qed

lemma finite_gpv_relD1: "\<lbrakk> rel_gpv A C gpv gpv'; finite_gpv \<I> gpv; rel_\<I> C (=) \<I> \<I> \<rbrakk> \<Longrightarrow> finite_gpv \<I> gpv'"
using finite_gpv_rel''D1[of A C "(=)" gpv gpv' \<I> \<I>] by(simp add: rel_gpv_conv_rel_gpv'')

lemma finite_gpv_rel''D2: "\<lbrakk> rel_gpv'' A C R gpv gpv'; finite_gpv \<I> gpv'; rel_\<I> C R \<I>' \<I> \<rbrakk> \<Longrightarrow> finite_gpv \<I>' gpv"
using finite_gpv_rel''D1[of "A\<inverse>\<inverse>" "C\<inverse>\<inverse>" "R\<inverse>\<inverse>" gpv' gpv \<I> \<I>'] by(simp add: rel_gpv''_conversep)

lemma finite_gpv_relD2: "\<lbrakk> rel_gpv A C gpv gpv'; finite_gpv \<I> gpv'; rel_\<I> C (=) \<I> \<I> \<rbrakk> \<Longrightarrow> finite_gpv \<I> gpv"
using finite_gpv_rel''D2[of A C "(=)" gpv gpv' \<I> \<I>] by(simp add: rel_gpv_conv_rel_gpv'')

lemma finite_gpv_parametric': "(rel_\<I> C R ===> rel_gpv'' A C R ===> (=)) finite_gpv finite_gpv"
by(blast dest: finite_gpv_rel''D2 finite_gpv_rel''D1)

lemma finite_gpv_parametric [transfer_rule]: "(rel_\<I> C (=) ===> rel_gpv A C ===> (=)) finite_gpv finite_gpv"
using finite_gpv_parametric'[of C "(=)" A] by(simp add: rel_gpv_conv_rel_gpv'')

end

lemma finite_gpv_map [simp]: "finite_gpv \<I> (map_gpv f id gpv) = finite_gpv \<I> gpv"
using finite_gpv_parametric[of "BNF_Def.Grp UNIV id" "BNF_Def.Grp UNIV f"]
unfolding gpv.rel_Grp by(auto simp add: rel_fun_def BNF_Def.Grp_def eq_commute rel_\<I>_eq)

lemma finite_gpv_assert [simp]: "finite_gpv \<I> (assert_gpv b)"
by(cases b) simp_all

lemma finite_gpv_try [simp]:
  "finite_gpv \<I> (TRY gpv ELSE gpv') \<longleftrightarrow> finite_gpv \<I> gpv \<and> (colossless_gpv \<I> gpv \<or> finite_gpv \<I> gpv')"
  (is "?lhs = _")
proof(intro iffI conjI; (elim conjE disjE)?)
  show 1: "finite_gpv \<I> gpv" if ?lhs using that
  proof(induction gpv''\<equiv>"TRY gpv ELSE gpv'" arbitrary: gpv)
    case (finite_gpv gpv)
    show ?case
    proof(rule finite_gpvI)
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" and input: "input \<in> responses_\<I> \<I> out"
      from IO have "IO out (\<lambda>input. TRY c input ELSE gpv') \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))"
        by(auto simp add: image_image generat.map_comp o_def intro: rev_image_eqI)
      thus "finite_gpv \<I> (c input)" using input by(rule finite_gpv.hyps) simp
    qed
  qed
  have "finite_gpv \<I> gpv'" if "?lhs" "\<not> colossless_gpv \<I> gpv" using that
  proof(induction gpv''\<equiv>"TRY gpv ELSE gpv'" arbitrary: gpv)
    case (finite_gpv gpv)
    show ?case
    proof(cases "lossless_spmf (the_gpv gpv)")
      case True
      have "\<exists>out c input. IO out c \<in> set_spmf (the_gpv gpv) \<and> input \<in> responses_\<I> \<I> out \<and> \<not> colossless_gpv \<I> (c input)"
        using finite_gpv.prems by(rule contrapos_np)(auto intro: colossless_gpvI simp add: True)
      then obtain out c input where IO: "IO out c \<in> set_spmf (the_gpv gpv)"
        and co': "\<not> colossless_gpv \<I> (c input)" 
        and input: "input \<in> responses_\<I> \<I> out" by blast
      from IO have "IO out (\<lambda>input. TRY c input ELSE gpv') \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))"
        by(auto simp add: image_image generat.map_comp o_def intro: rev_image_eqI)
      with co' show ?thesis using input by(blast intro: finite_gpv.hyps(2))
    next
      case False
      show ?thesis
      proof(rule finite_gpvI)
        fix out c input
        assume IO: "IO out c \<in> set_spmf (the_gpv gpv')" and input: "input \<in> responses_\<I> \<I> out"
        from IO False have "IO out c \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))" by(auto intro: rev_image_eqI)
        then show "finite_gpv \<I> (c input)" using input by(rule finite_gpv.hyps)
      qed
    qed
  qed
  then show "colossless_gpv \<I> gpv \<or> finite_gpv \<I> gpv'" if ?lhs using that by blast
  
  show ?lhs if "finite_gpv \<I> gpv" "finite_gpv \<I> gpv'" using that(1)
  proof induction
    case (finite_gpv gpv)
    show ?case
    proof
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))"
        and input: "input \<in> responses_\<I> \<I> out"
      then consider (gpv) c' where "IO out c' \<in> set_spmf (the_gpv gpv)" "c = (\<lambda>input. TRY c' input ELSE gpv')"
        | (gpv') "IO out c \<in> set_spmf (the_gpv gpv')" by(auto split: if_split_asm)
      then show "finite_gpv \<I> (c input)" using input
        by cases(auto intro: finite_gpv.IH finite_gpvD[OF that(2)])
    qed
  qed
  show ?lhs if "finite_gpv \<I> gpv" "colossless_gpv \<I> gpv" using that
  proof induction
    case (finite_gpv gpv)
    show ?case
      by(rule finite_gpvI)(use finite_gpv.prems in \<open>fastforce split: if_split_asm dest: colossless_gpvD intro: finite_gpv.IH\<close>)
  qed
qed

lemma lossless_gpv_conv_finite:
  "lossless_gpv \<I> gpv \<longleftrightarrow> finite_gpv \<I> gpv \<and> colossless_gpv \<I> gpv"
  (is "?loss \<longleftrightarrow> ?fin \<and> ?co")
proof(intro iffI conjI; (elim conjE)?)
  show ?fin if ?loss using that by induction(auto intro: finite_gpvI)
  show ?co if ?loss using that by induction(auto intro: colossless_gpvI)
  show ?loss if ?fin ?co using that
  proof induction
    case (finite_gpv gpv)
    from finite_gpv.prems finite_gpv.IH show ?case
      by cases(auto intro: lossless_gpvI)
  qed
qed

lemma colossless_gpv_try [simp]:
  "colossless_gpv \<I> (TRY gpv ELSE gpv') \<longleftrightarrow> colossless_gpv \<I> gpv \<or> colossless_gpv \<I> gpv'"
  (is "?lhs \<longleftrightarrow> ?gpv \<or> ?gpv'")
proof(intro iffI disjCI; (elim disjE)?)
  show "?gpv" if ?lhs "\<not> ?gpv'" using that(1)
  proof(coinduction arbitrary: gpv)
    case (colossless_gpv gpv)
    have ?lossless_spmf
    proof(rule ccontr)
      assume loss: "\<not> ?lossless_spmf"
      with colossless_gpv_lossless_spmfD[OF colossless_gpv(1)]
      have gpv': "lossless_spmf (the_gpv gpv')" by auto
      have "\<exists>out c input. IO out c \<in> set_spmf (the_gpv gpv') \<and> input \<in> responses_\<I> \<I> out \<and> \<not> colossless_gpv \<I> (c input)"
        using that(2) by(rule contrapos_np)(auto intro: colossless_gpvI gpv')
      then obtain out c input
        where IO: "IO out c \<in> set_spmf (the_gpv gpv')"
        and co': "\<not> colossless_gpv \<I> (c input)" 
        and input: "input \<in> responses_\<I> \<I> out" by blast
      from IO loss have "IO out c \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))"
        by(auto intro: rev_image_eqI)
      with colossless_gpv(1) have "colossless_gpv \<I> (c input)" using input
        by(rule colossless_gpv_continuationD)
      with co' show False by contradiction
    qed
    moreover have ?continuation
    proof(intro strip disjI1; simp)
      fix out c input
      assume IO: "IO out c \<in> set_spmf (the_gpv gpv)" and input: "input \<in> responses_\<I> \<I> out"
      hence "IO out (\<lambda>input. TRY c input ELSE gpv') \<in> set_spmf (the_gpv (TRY gpv ELSE gpv'))"
        by(auto intro: rev_image_eqI)
      with colossless_gpv show "colossless_gpv \<I> (TRY c input ELSE gpv')"
        by(rule colossless_gpv_continuationD)(simp add: input)
    qed
    ultimately show ?case ..
  qed
  show ?lhs if ?gpv'
  proof(coinduction arbitrary: gpv)
    case colossless_gpv
    show ?case using colossless_gpvD[OF that] by(auto 4 3)
  qed
  show ?lhs if ?gpv using that
  proof(coinduction arbitrary: gpv)
    case colossless_gpv
    show ?case using colossless_gpvD[OF colossless_gpv] by(auto 4 3)
  qed
qed

lemma lossless_gpv_try [simp]:
  "lossless_gpv \<I> (TRY gpv ELSE gpv') \<longleftrightarrow> 
   finite_gpv \<I> gpv \<and> (lossless_gpv \<I> gpv \<or> lossless_gpv \<I> gpv')"
by(auto simp add: lossless_gpv_conv_finite)

lemma interaction_any_bounded_by_imp_finite:
  assumes "interaction_any_bounded_by gpv (enat n)"
  shows "finite_gpv \<I>_full gpv"
using assms 
proof(induction n arbitrary: gpv)
  case 0
  then show ?case by(auto intro: finite_gpv.intros dest: interaction_bounded_by_contD simp add: zero_enat_def[symmetric])
next
  case (Suc n)
  from Suc.prems show ?case unfolding eSuc_enat[symmetric]
    by(auto 4 4 intro: finite_gpv.intros Suc.IH dest: interaction_bounded_by_contD)
qed

lemma finite_restrict_gpvI [simp]: "finite_gpv \<I>' gpv \<Longrightarrow> finite_gpv \<I>' (restrict_gpv \<I> gpv)"
by(induction rule: finite_gpv_induct)(rule finite_gpvI; clarsimp split: option.split_asm; split generat.split_asm; clarsimp split: if_split_asm simp add: in_set_spmf)

lemma interaction_bounded_by_exec_gpv_bad_count:
  fixes count and bad and n :: enat and k :: real
  assumes bound: "interaction_bounded_by consider gpv n"
  and good: "\<not> bad s"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> Suc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and bad: "\<And>s' x. \<lbrakk> \<not> bad s'; count s' < n + count s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> spmf (map_spmf (bad \<circ> snd) (callee s' x)) True \<le> k"
  and "consider": "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); \<not> bad s; bad s'; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> consider x"
  and k_nonneg: "k \<ge> 0"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  and WT_callee: "\<And>s. \<I> \<turnstile>c callee s \<surd>"
  shows "spmf (map_spmf (bad \<circ> snd) (exec_gpv callee gpv s)) True \<le> ennreal k * n"
using bound good bad WT_gpv
proof(induction arbitrary: gpv s n rule: exec_gpv_fixp_induct)
  case adm show ?case by(rule cont_intro ccpo_class.admissible_leI)+
  case bottom show ?case using k_nonneg by(simp add: zero_ereal_def[symmetric])
next
  case (step exec_gpv')
  let ?M = "restrict_space (measure_spmf (the_gpv gpv)) {IO out c|out c. True}"
  have "ennreal (spmf (map_spmf (bad \<circ> snd) (bind_spmf (the_gpv gpv) (case_generat (\<lambda>x. return_spmf (x, s)) (\<lambda>out c. bind_spmf (callee s out) (\<lambda>(x, y). exec_gpv' (c x) y))))) True) =
    ennreal (spmf (bind_spmf (the_gpv gpv) (\<lambda>generat. case generat of Pure x \<Rightarrow> return_spmf (bad s) |
       IO out rpv \<Rightarrow> bind_spmf (callee s out) (\<lambda>(x, s'). map_spmf (bad \<circ> snd) (exec_gpv' (rpv x) s')))) True)"
    (is "_ = ennreal (spmf (bind_spmf _ (case_generat _ ?io)) _)")
    by(simp add: map_spmf_bind_spmf o_def generat.case_distrib[where h="map_spmf _"] split_def cong del: generat.case_cong_weak)
  also have "\<dots> = \<integral>\<^sup>+ generat. \<integral>\<^sup>+ (x, s'). spmf (map_spmf (bad \<circ> snd) (exec_gpv' (continuation generat x) s')) True \<partial>measure_spmf (callee s (output generat)) \<partial>?M"
    using step.prems(2) by(auto simp add: ennreal_spmf_bind nn_integral_restrict_space intro!: nn_integral_cong split: generat.split)
  also have "\<dots> \<le> \<integral>\<^sup>+ generat. \<integral>\<^sup>+ (x, s'). (if bad s' then 1 else ennreal k * (if consider (output generat) then n - 1 else n)) \<partial>measure_spmf (callee s (output generat)) \<partial>?M"
  proof(clarsimp intro!: nn_integral_mono_AE simp add: AE_restrict_space_iff split del: if_split cong del: if_cong)
    show "ennreal (spmf (map_spmf (bad \<circ> snd) (exec_gpv' (rpv ret) s')) True)
          \<le> (if bad s' then 1 else ennreal k * ennreal_of_enat (if consider out then n - 1 else n))"
      if IO: "IO out rpv \<in> set_spmf (the_gpv gpv)"
      and call: "(ret, s') \<in> set_spmf (callee s out)"
      for out rpv ret s'
    proof(cases "bad s'")
      case True
      then show ?thesis by(simp add: pmf_le_1)
    next
      case False
      let ?n' = "if consider out then n - 1 else n"
      have out: "out \<in> outs_\<I> \<I>" using IO step.prems(4) by(simp add: WT_gpv_OutD)
      have bound': "interaction_bounded_by consider (rpv ret) ?n'"
        using interaction_bounded_by_contD[OF step.prems(1) IO]
              interaction_bounded_by_contD_ignore[OF step.prems(1) IO] by(auto)
      have "ret \<in> responses_\<I> \<I> out" using WT_callee call out by(rule WT_calleeD)
      with step.prems(4) IO have WT': "\<I> \<turnstile>g rpv ret \<surd>" by(rule WT_gpv_ContD)
      have bad':  "spmf (map_pmf (map_option (bad \<circ> snd)) (callee s'' x)) True \<le> k"
        if "\<not> bad s''" and count': "count s'' < ?n' + count s'" and "consider x" and "x \<in> outs_\<I> \<I>"
        for s'' x using \<open>\<not> bad s''\<close> _ \<open>consider x\<close> \<open>x \<in> outs_\<I> \<I>\<close>
      proof(rule step.prems)
        show "count s'' < n + count s"
        proof(cases "consider out")
          case True
          with count[OF call True out] count' interaction_bounded_by_contD[OF step.prems(1) IO, of undefined]
          show ?thesis by(cases n)(auto simp add: one_enat_def)
        next
          case False
          with ignore[OF call _ out] count' show ?thesis by(cases n)auto
        qed
      qed
      from step.IH[OF bound' False this] False WT' show ?thesis by(auto simp add: o_def)
    qed
  qed
  also have "\<dots> = \<integral>\<^sup>+ generat. \<integral>\<^sup>+ b. indicator {True} b + ennreal k * (if consider (output generat) then n - 1 else n) * indicator {False} b \<partial>measure_spmf (map_spmf (bad \<circ> snd) (callee s (output generat))) \<partial>?M"
    (is "_ = \<integral>\<^sup>+ generat. \<integral>\<^sup>+ _. _ \<partial>?O' generat \<partial>_")
    by(auto intro!: nn_integral_cong)
  also have "\<dots> = \<integral>\<^sup>+ generat. (\<integral>\<^sup>+ b. indicator {True} b \<partial>?O' generat) + ennreal k * (if consider (output generat) then n - 1 else n) * \<integral>\<^sup>+ b. indicator {False} b \<partial>?O' generat \<partial>?M"
    by(subst nn_integral_add)(simp_all add: k_nonneg nn_integral_cmult o_def)
  also have "\<dots> = \<integral>\<^sup>+ generat. ennreal (spmf (map_spmf (bad \<circ> snd) (callee s (output generat))) True) + ennreal k * (if consider (output generat) then n - 1 else n) * spmf (map_spmf (bad \<circ> snd) (callee s (output generat))) False \<partial>?M"
    by(simp del: nn_integral_map_spmf add: emeasure_spmf_single ereal_of_enat_mult)
  also have "\<dots> \<le> \<integral>\<^sup>+ generat. ennreal k * n \<partial>?M"
  proof(intro nn_integral_mono_AE, clarsimp intro!: nn_integral_mono_AE simp add: AE_restrict_space_iff not_is_Pure_conv split del: if_split)
    fix out c
    assume IO: "IO out c \<in> set_spmf (the_gpv gpv)"
    with step.prems(4) have out: "out \<in> outs_\<I> \<I>" by(rule WT_gpv_OutD)
    show "spmf (map_spmf (bad \<circ> snd) (callee s out)) True +
           ennreal k * (if consider out then n - 1 else n) * spmf (map_spmf (bad \<circ> snd) (callee s out)) False
          \<le> ennreal k * n"
    proof(cases "consider out")
      case True
      with IO have "n > 0" using interaction_bounded_by_contD[OF step.prems(1)] by(blast dest: interaction_bounded_by_contD)
      have "spmf (map_spmf (bad \<circ> snd) (callee s out)) True \<le> k" (is "?o True \<le> _")
        using \<open>\<not> bad s\<close> True \<open>n > 0\<close> out by(intro step.prems)(simp)
      hence "ennreal (?o True) \<le> k" using k_nonneg by(simp del: o_apply)
      hence "?o True + ennreal k * (n - 1) * ?o False \<le> ennreal k + ennreal k * (n - 1) * ennreal 1"
        by(rule add_mono)(rule mult_left_mono, simp_all add: pmf_le_1 k_nonneg)
      also have "\<dots> \<le> ennreal k * n" using \<open>n > 0\<close>
        by(cases n)(auto simp add: zero_enat_def ennreal_top_mult gr0_conv_Suc eSuc_enat[symmetric] field_simps)
      finally show ?thesis using True by(simp del: o_apply add: ereal_of_enat_mult)
    next
      case False
      hence "spmf (map_spmf (bad \<circ> snd) (callee s out)) True = 0" using \<open>\<not> bad s\<close> out
        unfolding spmf_eq_0_set_spmf by(auto dest: "consider")
      with False k_nonneg pmf_le_1[of "map_spmf (bad \<circ> snd) (callee s out)" "Some False"]
      show ?thesis by(simp add: mult_left_mono[THEN order_trans, where ?b1=1])
    qed
  qed
  also have "\<dots> \<le> ennreal k * n"
    by(simp add: k_nonneg emeasure_restrict_space measure_spmf.emeasure_eq_measure space_restrict_space measure_spmf.subprob_measure_le_1 mult_left_mono[THEN order_trans, where ?b1=1])
  finally show ?case by(simp del: o_apply)
qed

context callee_invariant_on begin

lemma interaction_bounded_by_exec_gpv_bad_count:
  includes lifting_syntax
  fixes count and bad and n :: enat
  assumes bound: "interaction_bounded_by consider gpv n"
  and I: "I s"
  and good: "\<not> bad s"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> Suc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and bad: "\<And>s' x. \<lbrakk> I s'; \<not> bad s'; count s' < n + count s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> spmf (map_spmf (bad \<circ> snd) (callee s' x)) True \<le> k"
  and "consider": "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> bad s; bad s'; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> consider x"
  and k_nonneg: "k \<ge> 0"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  shows "spmf (map_spmf (bad \<circ> snd) (exec_gpv callee gpv s)) True \<le> ennreal k * n"
proof -
  { assume "\<exists>(Rep :: 's' \<Rightarrow> 's) Abs. type_definition Rep Abs {s. I s}"
    then obtain Rep :: "'s' \<Rightarrow> 's" and Abs where td: "type_definition Rep Abs {s. I s}" by blast
    then interpret td: type_definition Rep Abs "{s. I s}" .
    define cr where "cr \<equiv> \<lambda>x y. x = Rep y"
    have [transfer_rule]: "bi_unique cr" "right_total cr" using td cr_def by(rule typedef_bi_unique typedef_right_total)+
    have [transfer_domain_rule]: "Domainp cr = I" using type_definition_Domainp[OF td cr_def] by simp
    
    let ?C = "eq_onp (\<lambda>x. x \<in> outs_\<I> \<I>)"

    define callee' where "callee' \<equiv> (Rep ---> id ---> map_spmf (map_prod id Abs)) callee"
    have [transfer_rule]: "(cr ===> ?C ===> rel_spmf (rel_prod (=) cr)) callee callee'"
      by(auto simp add: callee'_def rel_fun_def cr_def spmf_rel_map prod.rel_map td.Abs_inverse eq_onp_def intro!: rel_spmf_reflI intro: td.Rep[simplified] dest: callee_invariant)
    define s' where "s' \<equiv> Abs s"
    have [transfer_rule]: "cr s s'" using I by(simp add: cr_def s'_def td.Abs_inverse)
    define bad' where "bad' \<equiv> (Rep ---> id) bad"
    have [transfer_rule]: "(cr ===> (=)) bad bad'" by(simp add: rel_fun_def bad'_def cr_def)
    define count' where "count' \<equiv> (Rep ---> id) count"
    have [transfer_rule]: "(cr ===> (=)) count count'" by(simp add: rel_fun_def count'_def cr_def)

    have [transfer_rule]: "(?C ===> (=)) consider consider" by(simp add: eq_onp_def rel_fun_def)
    have [transfer_rule]: "rel_\<I> ?C (=) \<I> \<I>"
      by(rule rel_\<I>I)(auto simp add: rel_set_eq set_relator_eq_onp eq_onp_same_args dest: eq_onp_to_eq)
    note [transfer_rule] = bi_unique_eq_onp bi_unique_eq

    define gpv' where "gpv' \<equiv> restrict_gpv \<I> gpv"
    have [transfer_rule]: "rel_gpv (=) ?C gpv' gpv'"
      by(fold eq_onp_top_eq_eq)(auto simp add: gpv.rel_eq_onp eq_onp_same_args pred_gpv_def gpv'_def dest: in_outs'_restrict_gpvD)

    have "interaction_bounded_by consider gpv' n" using bound by(simp add: gpv'_def)
    moreover have "\<not> bad' s'" using good by transfer
    moreover have [rule_format, rotated]:
      "\<And>s y s'. \<forall>x \<in> outs_\<I> \<I>. (y, s') \<in> set_spmf (callee' s x) \<longrightarrow> consider x \<longrightarrow> count' s' \<le> Suc (count' s)"
      by(transfer fixing: "consider")(blast intro: count)
    moreover have [rule_format, rotated]:
      "\<And>s y s'. \<forall>x \<in> outs_\<I> \<I>. (y, s') \<in> set_spmf (callee' s x) \<longrightarrow> \<not> consider x \<longrightarrow> count' s' \<le> count' s"
      by(transfer fixing: "consider")(blast intro: ignore)
    moreover have [rule_format, rotated]: 
      "\<And>s''. \<forall>x \<in> outs_\<I> \<I>. \<not> bad' s'' \<longrightarrow> count' s'' < n + count' s' \<longrightarrow> consider x \<longrightarrow> spmf (map_spmf (bad' \<circ> snd) (callee' s'' x)) True \<le> k"
      by(transfer fixing: "consider" k n)(blast intro: bad)
    moreover have [rule_format, rotated]: 
      "\<And>s y s'. \<forall>x \<in> outs_\<I> \<I>. (y, s') \<in> set_spmf (callee' s x) \<longrightarrow> \<not> bad' s \<longrightarrow> bad' s' \<longrightarrow> consider x"
      by(transfer fixing: "consider")(blast intro: "consider")
    moreover note k_nonneg
    moreover have "\<I> \<turnstile>g gpv' \<surd>" by(simp add: gpv'_def)
    moreover have "\<And>s. \<I> \<turnstile>c callee' s \<surd>" by transfer(rule WT_callee)
    ultimately have **: "spmf (map_spmf (bad' \<circ> snd) (exec_gpv callee' gpv' s')) True \<le> ennreal k * n"
      by(rule interaction_bounded_by_exec_gpv_bad_count)
    have [transfer_rule]: "((=) ===> ?C ===> rel_spmf (rel_prod (=) (=))) callee callee"
      by(simp add: rel_fun_def eq_onp_def prod.rel_eq)
    have "spmf (map_spmf (bad \<circ> snd) (exec_gpv callee gpv' s)) True \<le> ennreal k * n" using **
      by(transfer)
    also have "exec_gpv callee gpv' s = exec_gpv callee gpv s"
      unfolding gpv'_def using WT_gpv I by(rule exec_gpv_restrict_gpv_invariant)
    finally have ?thesis . }
  from this[cancel_type_definition] I show ?thesis by blast
qed

lemma interaction_bounded_by'_exec_gpv_bad_count:
  fixes count and bad and n :: nat
  assumes bound: "interaction_bounded_by' consider gpv n"
  and I: "I s"
  and good: "\<not> bad s"
  and count: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> Suc (count s)"
  and ignore: "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> count s' \<le> count s"
  and bad: "\<And>s' x. \<lbrakk> I s'; \<not> bad s'; count s' < n + count s; consider x; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> spmf (map_spmf (bad \<circ> snd) (callee s' x)) True \<le> k"
  and "consider": "\<And>s x y s'. \<lbrakk> (y, s') \<in> set_spmf (callee s x); I s; \<not> bad s; bad s'; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> consider x"
  and k_nonneg: "k \<ge> 0"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  shows "spmf (map_spmf (bad \<circ> snd) (exec_gpv callee gpv s)) True \<le> k * n"
apply(subst ennreal_le_iff[symmetric], simp_all add: k_nonneg ennreal_mult ennreal_real_conv_ennreal_of_enat del: ennreal_of_enat_enat ennreal_le_iff)
apply(rule interaction_bounded_by_exec_gpv_bad_count[OF bound I _ count ignore bad "consider" k_nonneg WT_gpv, OF good])
apply simp_all
done

lemma interaction_bounded_by_exec_gpv_bad:
  assumes "interaction_any_bounded_by gpv n"
  and "I s" "\<not> bad s"
  and bad: "\<And>s x. \<lbrakk> I s; \<not> bad s; x \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> spmf (map_spmf (bad \<circ> snd) (callee s x)) True \<le> k"
  and k_nonneg: "0 \<le> k"
  and WT_gpv: "\<I> \<turnstile>g gpv \<surd>"
  shows "spmf (map_spmf (bad \<circ> snd) (exec_gpv callee gpv s)) True \<le> k * n"
using interaction_bounded_by_exec_gpv_bad_count[where bad=bad, OF assms(1) assms(2-3), where ?count = "\<lambda>_. 0", OF _ _ bad _ k_nonneg] k_nonneg WT_gpv
by(simp add: ennreal_real_conv_ennreal_of_enat[symmetric] ennreal_mult[symmetric] del: ennreal_of_enat_enat)

end

end
