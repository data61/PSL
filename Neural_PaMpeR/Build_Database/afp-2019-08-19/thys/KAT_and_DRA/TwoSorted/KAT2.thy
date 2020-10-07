(* Title:      Kleene Algebra with Tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Two sorted Kleene Algebra with Tests\<close>

theory KAT2
  imports Kleene_Algebra.Kleene_Algebra
begin

text \<open>
  As an alternative to the one-sorted implementation of tests, we provide a two-sorted, more 
  conventional one. In this setting, Isabelle's Boolean algebra theory can be used.
  This alternative can be developed further along the lines of the one-sorted implementation.
\<close>

syntax "_kat" :: "'a \<Rightarrow> 'a" ("`_`")

ML \<open>
val kat_test_vars = ["p","q","r","s","t","p'","q'","r'","s'","t'","p''","q''","r''","s''","t''"]

fun map_ast_variables ast =
  case ast of
    (Ast.Variable v) =>
      if exists (fn tv => tv = v) kat_test_vars
      then Ast.Appl [Ast.Variable "test", Ast.Variable v]
      else Ast.Variable v
  | (Ast.Constant c) => Ast.Constant c
  | (Ast.Appl []) => Ast.Appl []
  | (Ast.Appl (f :: xs)) => Ast.Appl (f :: map map_ast_variables xs)

structure KATHomRules = Named_Thms
  (val name = @{binding "kat_hom"}
   val description = "KAT test homomorphism rules")

fun kat_hom_tac ctxt n =
  let
    val rev_rules = map (fn thm => thm RS @{thm sym}) (KATHomRules.get ctxt)
  in
    asm_full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps rev_rules) n
  end
\<close>

setup \<open>KATHomRules.setup\<close>

method_setup kat_hom = \<open>
Scan.succeed (fn ctxt => SIMPLE_METHOD (CHANGED (kat_hom_tac ctxt 1)))
\<close>

parse_ast_translation \<open>
let
  fun kat_tr ctxt [t] = map_ast_variables t
in [(@{syntax_const "_kat"}, kat_tr)] end
\<close>

ML \<open>
structure VCGRules = Named_Thms
  (val name = @{binding "vcg"}
   val description = "verification condition generator rules")

fun vcg_tac ctxt n =
  let
    fun vcg' [] = no_tac
      | vcg' (r :: rs) = resolve_tac ctxt [r] n ORELSE vcg' rs;
  in REPEAT (CHANGED
       (kat_hom_tac ctxt n
        THEN REPEAT (vcg' (VCGRules.get ctxt))
        THEN kat_hom_tac ctxt n
        THEN TRY (resolve_tac ctxt @{thms order_refl} n ORELSE asm_full_simp_tac (put_simpset HOL_basic_ss ctxt) n)))
  end
\<close>

method_setup vcg = \<open>
Scan.succeed (fn ctxt => SIMPLE_METHOD (CHANGED (vcg_tac ctxt 1)))
\<close>

setup \<open>VCGRules.setup\<close>

locale dioid_tests =
  fixes test :: "'a::boolean_algebra \<Rightarrow> 'b::dioid_one_zerol"
  and not :: "'b::dioid_one_zerol \<Rightarrow> 'b::dioid_one_zerol" ("-")
  assumes test_sup [simp,kat_hom]: "test (sup p q) = `p + q`"
  and test_inf [simp,kat_hom]: "test (inf p q) = `p \<cdot> q`"
  and test_top [simp,kat_hom]: "test top = 1"
  and test_bot [simp,kat_hom]: "test bot = 0"
  and test_not [simp,kat_hom]: "test (- p) = `-p`"
  and test_iso_eq [kat_hom]: "p \<le> q \<longleftrightarrow> `p \<le> q`"
begin

notation test ("\<iota>")

lemma test_eq [kat_hom]: "p = q \<longleftrightarrow> `p = q`"
  by (metis eq_iff test_iso_eq)

ML_val \<open>map (fn thm => thm RS @{thm sym}) (KATHomRules.get @{context})\<close>

lemma test_iso: "p \<le> q \<Longrightarrow> `p \<le> q`"
  by (simp add: test_iso_eq)

(* Import lemmas and modify them to fit KAT syntax *)

lemma test_meet_comm: "`p \<cdot> q = q \<cdot> p`"
  by kat_hom (fact inf_commute)

lemmas test_one_top[simp] = test_iso[OF top_greatest, simplified]

lemma [simp]: "`-p + p = 1`"
  by kat_hom (metis compl_sup_top)

lemma [simp]: "`p + (-p) = 1`"
  by kat_hom (metis sup_compl_top)

lemma [simp]: "`(-p) \<cdot> p = 0`"
  by (metis inf.commute inf_compl_bot test_bot test_inf test_not)

lemma [simp]: "`p \<cdot> (-p) = 0`"
  by (metis inf_compl_bot test_bot test_inf test_not)

end

locale kat = 
  fixes test :: "'a::boolean_algebra \<Rightarrow> 'b::kleene_algebra"
  and not :: "'b::kleene_algebra \<Rightarrow> 'b::kleene_algebra" ("!")
  assumes is_dioid_tests: "dioid_tests test not"

sublocale kat \<subseteq> dioid_tests using is_dioid_tests .

context kat
begin

notation test ("\<iota>")

lemma test_eq [kat_hom]: "p = q \<longleftrightarrow> `p = q`"
  by (metis eq_iff test_iso_eq)

ML_val \<open>map (fn thm => thm RS @{thm sym}) (KATHomRules.get @{context})\<close>

lemma test_iso: "p \<le> q \<Longrightarrow> `p \<le> q`"
  by (simp add: test_iso_eq)

(* Import lemmas and modify them to fit KAT syntax *)

lemma test_meet_comm: "`p \<cdot> q = q \<cdot> p`"
  by kat_hom (fact inf_commute)

lemmas test_one_top[simp] = test_iso[OF top_greatest, simplified]

lemma test_star [simp]: "`p\<^sup>\<star> = 1`"
  by (metis star_subid test_iso test_top top_greatest)

lemmas [kat_hom] = test_star[symmetric]

lemma [simp]: "`!p + p = 1`"
  by kat_hom (metis compl_sup_top)

lemma [simp]: "`p + !p = 1`"
  by kat_hom (metis sup_compl_top)

lemma [simp]: "`!p \<cdot> p = 0`"
  by (metis inf.commute inf_compl_bot test_bot test_inf test_not)

lemma [simp]: "`p \<cdot> !p = 0`"
  by (metis inf_compl_bot test_bot test_inf test_not)

definition hoare_triple :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>") where
  "\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace> \<equiv> p\<cdot>c \<le> c\<cdot>q"

declare hoare_triple_def[iff]

lemma hoare_triple_def_var: "`p\<cdot>c \<le> c\<cdot>q \<longleftrightarrow> p\<cdot>c\<cdot>!q = 0`"
  apply (intro iffI antisym)
  apply (rule order_trans[of _ "`c \<cdot> q \<cdot> !q`"])
  apply (rule mult_isor[rule_format])
  apply (simp add: mult.assoc)+
  apply (simp add: mult.assoc[symmetric])
  apply (rule order_trans[of _ "`p\<cdot>c\<cdot>(!q + q)`"])
  apply simp
  apply (simp only: distrib_left add_zerol)
  apply (rule order_trans[of _ "`1 \<cdot> c \<cdot> q`"])
  apply (simp only: mult.assoc)
  apply (rule mult_isor[rule_format])
  by simp_all

lemmas [intro!] = star_sim2[rule_format]

lemma hoare_weakening: "p \<le> p' \<Longrightarrow> q' \<le> q \<Longrightarrow> `\<lbrace>p'\<rbrace> c \<lbrace>q'\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> c \<lbrace>q\<rbrace>`"
  by auto (metis mult_isol mult_isor order_trans test_iso)

lemma hoare_star: "`\<lbrace>p\<rbrace> c \<lbrace>p\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> c\<^sup>\<star> \<lbrace>p\<rbrace>`"
  by auto

lemmas [vcg] = hoare_weakening[OF order_refl _ hoare_star]

lemma hoare_test [vcg]: "`p \<cdot> t \<le> q` \<Longrightarrow> `\<lbrace>p\<rbrace> t \<lbrace>q\<rbrace>`"
  by auto (metis inf_le2 le_inf_iff test_inf test_iso_eq)

lemma hoare_mult [vcg]: "`\<lbrace>p\<rbrace> x \<lbrace>r\<rbrace>` \<Longrightarrow> `\<lbrace>r\<rbrace> y \<lbrace>q\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> x\<cdot>y \<lbrace>q\<rbrace>`"
proof auto
  assume [simp]: "`p \<cdot> x \<le> x \<cdot> r`" and [simp]: "`r \<cdot> y \<le> y \<cdot> q`"
  have "`p \<cdot> (x \<cdot> y) \<le> x \<cdot> r \<cdot> y`"
    by (auto simp add: mult.assoc[symmetric] intro!: mult_isor[rule_format])
  also have "`... \<le> x \<cdot> y \<cdot> q`"
    by (auto simp add: mult.assoc intro!: mult_isol[rule_format])
  finally show "`p \<cdot> (x \<cdot> y) \<le> x \<cdot> y \<cdot> q`" .
qed

lemma [simp]: "`!p \<cdot> !p = !p`"
  by (metis inf.idem test_inf test_not)

lemma hoare_plus [vcg]: "`\<lbrace>p\<rbrace> x \<lbrace>q\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> y \<lbrace>q\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> x + y \<lbrace>q\<rbrace>`"
proof -
  assume a1: "\<lbrace>\<iota> p\<rbrace> x \<lbrace>\<iota> q\<rbrace>"
  assume "\<lbrace>\<iota> p\<rbrace> y \<lbrace>\<iota> q\<rbrace>"
  hence "\<iota> p \<cdot> (x + y) \<le> x \<cdot> \<iota> q + y \<cdot> \<iota> q"
    using a1 by (metis (no_types) distrib_left hoare_triple_def join.sup.mono)
  thus ?thesis
    by force
qed

definition While :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" ("While _ Do _ End" [50,50] 51) where
  "While t Do c End = (t\<cdot>c)\<^sup>\<star>\<cdot>!t"

lemma hoare_while: "`\<lbrace>p \<cdot> t\<rbrace> c \<lbrace>p\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> While t Do c End \<lbrace>!t \<cdot> p\<rbrace>`"
  unfolding While_def by vcg (metis inf_commute order_refl)

lemma [vcg]: "`\<lbrace>p \<cdot> t\<rbrace> c \<lbrace>p\<rbrace>` \<Longrightarrow> `!t \<cdot> p \<le> q` \<Longrightarrow> `\<lbrace>p\<rbrace> While t Do c End \<lbrace>q\<rbrace>`"
  by (metis hoare_weakening hoare_while order_refl test_inf test_iso_eq test_not)

definition If :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b" ("If _ Then _ Else _" [50,50,50] 51) where
  "If p Then c1 Else c2 \<equiv> p\<cdot>c1 + !p\<cdot>c2"

lemma hoare_if [vcg]: "`\<lbrace>p \<cdot> t\<rbrace> c1 \<lbrace>q\<rbrace>` \<Longrightarrow> `\<lbrace>p \<cdot> !t\<rbrace> c2 \<lbrace>q\<rbrace>` \<Longrightarrow> `\<lbrace>p\<rbrace> If t Then c1 Else c2 \<lbrace>q\<rbrace>`"
  unfolding If_def by vcg assumption

end

end
