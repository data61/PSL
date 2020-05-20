(*  Title:       N2M
    Authors:     Jasmin Blanchette, Andrei Popescu, Dmitriy Traytel
    Maintainer:  Dmitriy Traytel <traytel at inf.ethz.ch>
*)

section \<open>Mutual View on Nested Datatypes\<close>

(*<*)
theory N2M
  imports "HOL-Library.BNF_Axiomatization"
begin
(*>*)

notation BNF_Def.convol ("<_, _>")

declare [[bnf_internals]]

declare [[typedef_overloaded]]

bnf_axiomatization ('a, 'b) F0 [wits: "'a \<Rightarrow> ('a, 'b) F0"]
bnf_axiomatization ('a, 'b) G0 [wits: "'a \<Rightarrow> ('a, 'b) G0"]


subsection \<open>Nested Definition\<close>

datatype 'a F = CF "('a, 'a F) F0"
datatype 'a G = CG "('a, ('a G) F) G0"

type_synonym ('b, 'c) F_pre_F = "('c, 'b) F0"
type_synonym ('c, 'a) G_pre_G = "('a, 'c F) G0"

term "ctor_fold_F :: (('b, 'c) F_pre_F \<Rightarrow> 'b) \<Rightarrow> 'c F \<Rightarrow> 'b"
term "ctor_fold_G :: (('c, 'a) G_pre_G \<Rightarrow> 'c) \<Rightarrow> 'a G \<Rightarrow> 'c"
term "ctor_rec_F :: (('c F \<times> 'b, 'c) F_pre_F \<Rightarrow> 'b) \<Rightarrow> 'c F \<Rightarrow> 'b"
term "ctor_rec_G :: (('a G \<times> 'c, 'a) G_pre_G \<Rightarrow> 'c) \<Rightarrow> 'a G \<Rightarrow> 'c"
thm F.ctor_rel_induct
thm G.ctor_rel_induct[unfolded rel_pre_G_def id_apply]


subsection \<open>Isomorphic Mutual Definition\<close>

datatype 'a G\<^sub>M = CG "('a, 'a GF\<^sub>M) G0"
  and  'a GF\<^sub>M = CF "('a G\<^sub>M, 'a GF\<^sub>M) F0"

type_synonym ('b, 'c) GF\<^sub>M_pre_GF\<^sub>M = "('c, 'b) F0"
type_synonym ('c, 'a) G\<^sub>M_pre_G\<^sub>M = "('a, 'c) G0"

term "ctor_fold_G\<^sub>M :: (('c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('c, 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G\<^sub>M \<Rightarrow> 'b"
term "ctor_fold_GF\<^sub>M :: (('c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('c, 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a GF\<^sub>M \<Rightarrow> 'c"
term "ctor_rec_G\<^sub>M :: (('a GF\<^sub>M \<times> 'c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('a GF\<^sub>M \<times> 'c, 'a G\<^sub>M \<times> 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G\<^sub>M \<Rightarrow> 'b"
term "ctor_rec_GF\<^sub>M :: (('a GF\<^sub>M \<times> 'c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('a GF\<^sub>M \<times> 'c, 'a G\<^sub>M \<times> 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a GF\<^sub>M \<Rightarrow> 'c"
thm G\<^sub>M_GF\<^sub>M.ctor_rel_induct[unfolded rel_pre_G\<^sub>M_def rel_pre_GF\<^sub>M_def]

subsection \<open>Mutualization\<close>

subsubsection \<open>Iterators\<close>

definition n2m_ctor_fold_G :: "(('c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('c, 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G \<Rightarrow> 'b"
  where "n2m_ctor_fold_G s1 s2 = ctor_fold_G (s1 o
    map_pre_G\<^sub>M id (id :: unit \<Rightarrow> unit) (ctor_fold_F (s2 o BNF_Composition.id_bnf o BNF_Composition.id_bnf)) o BNF_Composition.id_bnf o BNF_Composition.id_bnf)"
definition n2m_ctor_fold_G_F :: "(('c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('c, 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G F \<Rightarrow> 'c"
  where "n2m_ctor_fold_G_F s1 s2 = ctor_fold_F (s2 o map_pre_GF\<^sub>M (id :: unit \<Rightarrow> unit) (n2m_ctor_fold_G s1 s2) id o BNF_Composition.id_bnf o BNF_Composition.id_bnf)"

lemma G_ctor_o_fold: "ctor_fold_G s o ctor_G = s o map_pre_G id (ctor_fold_G s)"
  unfolding fun_eq_iff o_apply G.ctor_fold by simp
lemma F_ctor_o_fold: "ctor_fold_F s o ctor_F = s o map_pre_F id (ctor_fold_F s)"
  unfolding fun_eq_iff o_apply F.ctor_fold by simp

lemma G_ctor_o_rec: "ctor_rec_G s o ctor_G = s o map_pre_G id (BNF_Def.convol id (ctor_rec_G s))"
  unfolding fun_eq_iff o_apply G.ctor_rec by simp
lemma F_ctor_o_rec: "ctor_rec_F s o ctor_F = s o map_pre_F id (BNF_Def.convol id (ctor_rec_F s))"
  unfolding fun_eq_iff o_apply F.ctor_rec by simp

lemma n2m_ctor_fold_G:
  "n2m_ctor_fold_G s1 s2 o ctor_G = s1 o map_pre_G\<^sub>M id id (n2m_ctor_fold_G_F s1 s2) o BNF_Composition.id_bnf o BNF_Composition.id_bnf"
  unfolding n2m_ctor_fold_G_def n2m_ctor_fold_G_F_def
    map_pre_G_def map_pre_F_def map_pre_G\<^sub>M_def map_pre_GF\<^sub>M_def
    G_ctor_o_fold id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF type_copy_map_comp0_undo[OF BNF_Composition.type_definition_id_bnf_UNIV BNF_Composition.type_definition_id_bnf_UNIV BNF_Composition.type_definition_id_bnf_UNIV pre_G\<^sub>M.map_comp0[unfolded map_pre_G\<^sub>M_def]]]
    F.ctor_fold_o_map
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

lemma n2m_ctor_fold_G_F:
  "n2m_ctor_fold_G_F s1 s2 o ctor_F = s2 o map_pre_GF\<^sub>M id (n2m_ctor_fold_G s1 s2) (n2m_ctor_fold_G_F s1 s2) o BNF_Composition.id_bnf o BNF_Composition.id_bnf"
  unfolding n2m_ctor_fold_G_F_def map_pre_F_def map_pre_G\<^sub>M_def map_pre_GF\<^sub>M_def
    F_ctor_o_fold id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF F0.map_comp0[symmetric]]
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

subsubsection \<open>Recursors\<close>

definition n2m_ctor_rec_G ::
  "(('a G F \<times> 'c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('a G F \<times> 'c, 'a G \<times> 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G \<Rightarrow> 'b"
  where "n2m_ctor_rec_G s1 s2 =
    ctor_rec_G (s1 o
      map_pre_G\<^sub>M id (id :: unit \<Rightarrow> unit)
        (BNF_Def.convol (map_F fst) (ctor_rec_F (s2 o map_pre_GF\<^sub>M (id :: unit \<Rightarrow> unit) id (map_prod (map_F fst) id) o BNF_Composition.id_bnf o BNF_Composition.id_bnf))) o
      BNF_Composition.id_bnf o BNF_Composition.id_bnf)"

definition n2m_ctor_rec_G_F ::
  "(('a G F \<times> 'c, 'a) G\<^sub>M_pre_G\<^sub>M \<Rightarrow> 'b) \<Rightarrow> (('a G F \<times> 'c, 'a G \<times> 'b) GF\<^sub>M_pre_GF\<^sub>M \<Rightarrow> 'c) \<Rightarrow> 'a G F \<Rightarrow> 'c"
  where "n2m_ctor_rec_G_F s1 s2 = ctor_rec_F (s2 o map_pre_GF\<^sub>M (id :: unit \<Rightarrow> unit) (BNF_Def.convol id (n2m_ctor_rec_G s1 s2)) id o BNF_Composition.id_bnf o BNF_Composition.id_bnf)"

lemma n2m_ctor_rec_G:
  "n2m_ctor_rec_G s1 s2 o ctor_G = s1 o map_pre_G\<^sub>M id id (BNF_Def.convol id (n2m_ctor_rec_G_F s1 s2)) o BNF_Composition.id_bnf o BNF_Composition.id_bnf"
  unfolding n2m_ctor_rec_G_def n2m_ctor_rec_G_F_def
    map_pre_G_def map_pre_F_def map_pre_G\<^sub>M_def map_pre_GF\<^sub>M_def
    G_ctor_o_rec
    id_apply comp_id id_comp comp_assoc map_prod.comp map_prod.id
    fst_convol map_prod_o_convol convol_o
    rewriteL_comp_comp[OF G0.map_comp0[symmetric]]
    rewriteL_comp_comp[OF F0.map_comp0[symmetric]]
    F.map_comp0[symmetric] F.map_id0
    F.ctor_rec_o_map
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

lemma n2m_ctor_rec_G_F:
  "n2m_ctor_rec_G_F s1 s2 o ctor_F = s2 o map_pre_GF\<^sub>M id (BNF_Def.convol id (n2m_ctor_rec_G s1 s2)) (BNF_Def.convol id (n2m_ctor_rec_G_F s1 s2)) o BNF_Composition.id_bnf o BNF_Composition.id_bnf"
  unfolding n2m_ctor_rec_G_F_def map_pre_F_def map_pre_G\<^sub>M_def map_pre_GF\<^sub>M_def
    F_ctor_o_rec id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF F0.map_comp0[symmetric]]
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

subsubsection \<open>Induction\<close>

lemma n2m_rel_induct_G_G_F:
  assumes IH1: "\<forall>x y. BNF_Def.vimage2p (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (rel_pre_G\<^sub>M P R S) x y \<longrightarrow> R (ctor_G x) (ctor_G y)"
    and     IH2: "\<forall>x y. BNF_Def.vimage2p (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (rel_pre_GF\<^sub>M P R S) x y \<longrightarrow> S (ctor_F x) (ctor_F y)"
  shows "rel_G P \<le> R \<and> rel_F (rel_G P) \<le> S"
  apply (rule context_conjI)
  apply (rule G.ctor_rel_induct[unfolded rel_pre_G_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF IH1], OF vimage2p_mono[OF _ pre_G\<^sub>M.rel_mono], unfolded vimage2p_def o_apply rel_pre_G\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule F.ctor_rel_induct[unfolded rel_pre_F_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF IH2], unfolded vimage2p_def o_apply rel_pre_GF\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])

  apply (rule F.ctor_rel_induct[unfolded rel_pre_F_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF IH2], OF vimage2p_mono[OF _ pre_GF\<^sub>M.rel_mono], unfolded vimage2p_def o_apply rel_pre_GF\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])
  apply (rule order_refl)
  apply assumption
  apply (rule order_refl)
  done

lemmas n2m_ctor_induct_G_G_F = spec[OF spec [OF
      n2m_rel_induct_G_G_F[of "(=)" "BNF_Def.Grp (Collect R) id" "BNF_Def.Grp (Collect S) id" for R S,
        unfolded G.rel_eq F.rel_eq eq_le_Grp_id_iff all_simps(1,2)[symmetric]]],
    unfolded eq_alt pre_G\<^sub>M.rel_Grp pre_GF\<^sub>M.rel_Grp pre_G\<^sub>M.map_id0 pre_GF\<^sub>M.map_id0,
    unfolded vimage2p_comp vimage2p_id comp_apply comp_id Grp_id_mono_subst
    type_copy_vimage2p_Grp_Rep[OF BNF_Composition.type_definition_id_bnf_UNIV]
    type_copy_Abs_o_Rep[OF BNF_Composition.type_definition_id_bnf_UNIV]
    eqTrueI[OF subset_UNIV] simp_thms(22)
    atomize_conjL[symmetric] atomize_all[symmetric] atomize_imp[symmetric],
    unfolded subset_iff mem_Collect_eq]


section \<open>Mutual View on Nested Coatatypes\<close>

bnf_axiomatization ('a, 'b) coF0
bnf_axiomatization ('a, 'b) coG0


subsection \<open>Nested definition\<close>

codatatype 'a coF = CcoF "('a, 'a coF) coF0"
codatatype 'a coG = CcoG "('a, ('a coG) coF) coG0"

type_synonym ('b, 'c) coF_pre_coF = "('c, 'b) coF0"
type_synonym ('c, 'a) coG_pre_coG = "('a, 'c coF) coG0"

term "dtor_unfold_coF :: ('b \<Rightarrow> ('b, 'c) coF_pre_coF) \<Rightarrow> 'b \<Rightarrow> 'c coF"
term "dtor_unfold_coG :: ('c \<Rightarrow> ('c, 'a) coG_pre_coG) \<Rightarrow> 'c \<Rightarrow> 'a coG"
term "dtor_corec_coF :: ('b \<Rightarrow> ('c coF + 'b, 'c) coF_pre_coF) \<Rightarrow> 'b \<Rightarrow> 'c coF"
term "dtor_corec_coG :: ('c \<Rightarrow> ('a coG + 'c, 'a) coG_pre_coG) \<Rightarrow> 'c \<Rightarrow> 'a coG"
thm coF.dtor_rel_coinduct
thm coG.dtor_rel_coinduct[unfolded rel_pre_coG_def id_apply]


subsection \<open>Isomorphic Mutual Definition\<close>

codatatype 'a coG\<^sub>M = CcoG "('a, 'a coGcoF\<^sub>M) coG0"
  and  'a coGcoF\<^sub>M = CcoF "('a coG\<^sub>M, 'a coGcoF\<^sub>M) coF0"

type_synonym ('b, 'c) coGcoF\<^sub>M_pre_coGcoF\<^sub>M = "('c, 'b) coF0"
type_synonym ('c, 'a) coG\<^sub>M_pre_coG\<^sub>M = "('a, 'c) coG0"

term "dtor_unfold_coG\<^sub>M :: ('b \<Rightarrow> ('c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('c, 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'b \<Rightarrow> 'a coG\<^sub>M"
term "dtor_unfold_coGcoF\<^sub>M :: ('b \<Rightarrow> ('c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('c, 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'c \<Rightarrow> 'a coGcoF\<^sub>M"
term "dtor_corec_coG\<^sub>M :: ('b \<Rightarrow> ('a coGcoF\<^sub>M + 'c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('a coGcoF\<^sub>M + 'c, 'a coG\<^sub>M + 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'b \<Rightarrow> 'a coG\<^sub>M"
term "dtor_corec_coGcoF\<^sub>M :: ('b \<Rightarrow> ('a coGcoF\<^sub>M + 'c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('a coGcoF\<^sub>M + 'c, 'a coG\<^sub>M + 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'c \<Rightarrow> 'a coGcoF\<^sub>M"
thm coG\<^sub>M_coGcoF\<^sub>M.dtor_rel_coinduct[unfolded rel_pre_coG\<^sub>M_def rel_pre_coGcoF\<^sub>M_def]

subsection \<open>Mutualization\<close>

subsubsection \<open>Coiterators\<close>

definition n2m_dtor_unfold_coG :: "('b \<Rightarrow> ('c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('c, 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'b \<Rightarrow> 'a coG"
  where "n2m_dtor_unfold_coG s1 s2 = dtor_unfold_coG (BNF_Composition.id_bnf o BNF_Composition.id_bnf o
    map_pre_coG\<^sub>M id (id :: unit \<Rightarrow> unit) (dtor_unfold_coF (BNF_Composition.id_bnf o BNF_Composition.id_bnf o s2)) o s1)"
definition n2m_dtor_unfold_coG_coF :: "('b \<Rightarrow> ('c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('c, 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'c \<Rightarrow> 'a coG coF"
  where "n2m_dtor_unfold_coG_coF s1 s2 = dtor_unfold_coF (BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coGcoF\<^sub>M (id :: unit \<Rightarrow> unit) (n2m_dtor_unfold_coG s1 s2) id o s2)"

lemma coG_dtor_o_unfold: "dtor_coG o dtor_unfold_coG s = map_pre_coG id (dtor_unfold_coG s) o s"
  unfolding fun_eq_iff o_apply coG.dtor_unfold by simp
lemma coF_dtor_o_unfold: "dtor_coF o dtor_unfold_coF s = map_pre_coF id (dtor_unfold_coF s) o s"
  unfolding fun_eq_iff o_apply coF.dtor_unfold by simp

lemma coG_dtor_o_corec: "dtor_coG o dtor_corec_coG s = map_pre_coG id (case_sum id (dtor_corec_coG s)) o s"
  unfolding fun_eq_iff o_apply coG.dtor_corec by simp
lemma coF_dtor_o_corec: "dtor_coF o dtor_corec_coF s = map_pre_coF id (case_sum id (dtor_corec_coF s)) o s"
  unfolding fun_eq_iff o_apply coF.dtor_corec by simp

lemma n2m_dtor_unfold_coG:
  "dtor_coG o n2m_dtor_unfold_coG s1 s2 = BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coG\<^sub>M id id (n2m_dtor_unfold_coG_coF s1 s2) o s1"
  unfolding n2m_dtor_unfold_coG_def n2m_dtor_unfold_coG_coF_def
    map_pre_coG_def map_pre_coF_def map_pre_coG\<^sub>M_def map_pre_coGcoF\<^sub>M_def
    coG_dtor_o_unfold id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF type_copy_map_comp0_undo[OF BNF_Composition.type_definition_id_bnf_UNIV BNF_Composition.type_definition_id_bnf_UNIV BNF_Composition.type_definition_id_bnf_UNIV pre_coG\<^sub>M.map_comp0[unfolded map_pre_coG\<^sub>M_def]]]
    coF.dtor_unfold_o_map
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

lemma n2m_dtor_unfold_coG_coF:
  "dtor_coF o n2m_dtor_unfold_coG_coF s1 s2 = BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coGcoF\<^sub>M id (n2m_dtor_unfold_coG s1 s2) (n2m_dtor_unfold_coG_coF s1 s2) o s2"
  unfolding n2m_dtor_unfold_coG_coF_def map_pre_coF_def map_pre_coG\<^sub>M_def map_pre_coGcoF\<^sub>M_def
    coF_dtor_o_unfold id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF coF0.map_comp0[symmetric]]
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

subsubsection \<open>Corecursors\<close>

definition n2m_dtor_corec_coG ::
  "('b \<Rightarrow> ('a coG coF + 'c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('a coG coF + 'c, 'a coG + 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'b \<Rightarrow> 'a coG"
  where "n2m_dtor_corec_coG s1 s2 =
    dtor_corec_coG (BNF_Composition.id_bnf o BNF_Composition.id_bnf o
      map_pre_coG\<^sub>M id (id :: unit \<Rightarrow> unit)
        (case_sum (map_coF Inl) (dtor_corec_coF (BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coGcoF\<^sub>M (id :: unit \<Rightarrow> unit) id (map_sum (map_coF Inl) id) o s2))) o
      s1)"

definition n2m_dtor_corec_coG_coF ::
  "('b \<Rightarrow> ('a coG coF + 'c, 'a) coG\<^sub>M_pre_coG\<^sub>M) \<Rightarrow> ('c \<Rightarrow> ('a coG coF + 'c, 'a coG + 'b) coGcoF\<^sub>M_pre_coGcoF\<^sub>M) \<Rightarrow> 'c \<Rightarrow> 'a coG coF"
  where "n2m_dtor_corec_coG_coF s1 s2 = dtor_corec_coF (BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coGcoF\<^sub>M (id :: unit \<Rightarrow> unit) (case_sum id (n2m_dtor_corec_coG s1 s2)) id o s2)"

lemma n2m_dtor_corec_coG:
  "dtor_coG o n2m_dtor_corec_coG s1 s2 = BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coG\<^sub>M id id (case_sum id (n2m_dtor_corec_coG_coF s1 s2)) o s1"
  unfolding n2m_dtor_corec_coG_def n2m_dtor_corec_coG_coF_def
    map_pre_coG_def map_pre_coF_def map_pre_coG\<^sub>M_def map_pre_coGcoF\<^sub>M_def
    coG_dtor_o_corec
    id_apply comp_id id_comp comp_assoc[symmetric] map_sum.comp map_sum.id
    case_sum_o_inj(1) case_sum_o_map_sum o_case_sum
    rewriteR_comp_comp[OF coG0.map_comp0[symmetric]]
    rewriteR_comp_comp[OF coF0.map_comp0[symmetric]]
    coF.map_comp0[symmetric] coF.map_id0
    coF.dtor_corec_o_map
    rewriteR_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

lemma n2m_dtor_corec_coG_coF:
  "dtor_coF o n2m_dtor_corec_coG_coF s1 s2 = BNF_Composition.id_bnf o BNF_Composition.id_bnf o map_pre_coGcoF\<^sub>M id (case_sum id (n2m_dtor_corec_coG s1 s2)) (case_sum id (n2m_dtor_corec_coG_coF s1 s2)) o s2"
  unfolding n2m_dtor_corec_coG_coF_def map_pre_coF_def map_pre_coG\<^sub>M_def map_pre_coGcoF\<^sub>M_def
    coF_dtor_o_corec id_apply comp_id id_comp comp_assoc
    rewriteL_comp_comp[OF coF0.map_comp0[symmetric]]
    rewriteL_comp_comp[OF type_copy_Rep_o_Abs[OF BNF_Composition.type_definition_id_bnf_UNIV]] ..

subsubsection \<open>Coinduction\<close>

lemma n2m_rel_coinduct_coG_coG_coF:
  assumes CIH1: "\<forall>x y. R x y \<longrightarrow> BNF_Def.vimage2p (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (rel_pre_coG\<^sub>M P R S) (dtor_coG x) (dtor_coG y)"
    and     CIH2: "\<forall>x y. S x y \<longrightarrow> BNF_Def.vimage2p (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (BNF_Composition.id_bnf o BNF_Composition.id_bnf) (rel_pre_coGcoF\<^sub>M P R S) (dtor_coF x) (dtor_coF y)"
  shows "R \<le> rel_coG P \<and> S \<le> rel_coF (rel_coG P)"
  apply (rule context_conjI)
  apply (rule coG.dtor_rel_coinduct[unfolded rel_pre_coG_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF CIH1], THEN vimage2p_mono[OF _ pre_coG\<^sub>M.rel_mono], unfolded vimage2p_def o_apply rel_pre_coG\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])
  apply (rule order_refl)
  apply (rule order_refl)
  apply (rule coF.dtor_rel_coinduct[unfolded rel_pre_coF_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF CIH2], unfolded vimage2p_def o_apply rel_pre_coGcoF\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])

  apply (rule coF.dtor_rel_coinduct[unfolded rel_pre_coF_def id_apply vimage2p_def o_apply])
  apply (erule mp[OF spec2[OF CIH2], THEN vimage2p_mono[OF _ pre_coGcoF\<^sub>M.rel_mono], unfolded vimage2p_def o_apply rel_pre_coGcoF\<^sub>M_def type_definition.Abs_inverse[OF BNF_Composition.type_definition_id_bnf_UNIV UNIV_I]])
  apply (rule order_refl)
  apply assumption
  apply (rule order_refl)
  done

lemmas n2m_ctor_induct_coG_coG_coF = spec[OF spec[OF spec[OF spec[OF
          n2m_rel_coinduct_coG_coG_coF[of _ "(=)",
            unfolded coG.rel_eq coF.rel_eq le_fun_def le_bool_def all_simps(1,2)[symmetric]]]]]]

(*<*)
end
(*>*)
