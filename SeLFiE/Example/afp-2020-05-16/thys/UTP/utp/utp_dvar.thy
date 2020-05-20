subsection \<open>Deep UTP variables\<close>

theory utp_dvar
  imports utp_pred
begin

(* FIXME: Redo also this properly using the function update lens *)

text \<open>UTP variables represented by record fields are shallow, nameless entities. They are fundamentally
        static in nature, since a new record field can only be introduced definitionally and cannot be
        otherwise arbitrarily created. They are nevertheless very useful as proof automation is excellent,
        and they can fully make use of the Isabelle type system. However, for constructs like alphabet
        extension that can introduce new variables they are inadequate. As a result we also introduce
        a notion of deep variables to complement them. A deep variable is not a record field, but
        rather a key within a store map that records the values of all deep variables. As such the
        Isabelle type system is agnostic of them, and the creation of a new deep variable does not
        change the portion of the alphabet specified by the type system.

        In order to create a type of stores (or bindings) for variables, we must fix a universe
        for the variable valuations. This is the major downside of deep variables -- they cannot
        have any type, but only a type whose cardinality is up to $\mathfrak{c}$, the cardinality
        of the continuum. This is why we need both deep and shallow variables, as the latter are
        unrestricted in this respect. Each deep variable will therefore specify the cardinality
        of the type it possesses.\<close>

subsection \<open>Cardinalities\<close>

text \<open>We first fix a datatype representing all possible cardinalities for a deep variable. These
        include finite cardinalities, $\aleph_0$ (countable), and $\mathfrak{c}$ (uncountable up
        to the continuum).\<close>

datatype ucard = fin nat | aleph0 ("\<aleph>\<^sub>0") | cont ("\<c>")

text \<open>Our universe is simply the set of natural numbers; this is sufficient for all types up
        to cardinality $\mathfrak{c}$.\<close>

type_synonym uuniv = "nat set"

text \<open>We introduce a function that gives the set of values within our universe of the given
        cardinality. Since a cardinality of 0 is no proper type, we use finite cardinality 0 to
        mean cardinality 1, 1 to mean 2 etc.\<close>

fun uuniv :: "ucard \<Rightarrow> uuniv set" ("\<U>'(_')") where
"\<U>(fin n) = {{x} | x. x \<le> n}" |
"\<U>(\<aleph>\<^sub>0) = {{x} | x. True}" |
"\<U>(\<c>) = UNIV"

text \<open>We also define the following function that gives the cardinality of a type within
        the @{class continuum} type class.\<close>

definition ucard_of :: "'a::continuum itself \<Rightarrow> ucard" where
"ucard_of x = (if (finite (UNIV :: 'a set))
                  then fin(card(UNIV :: 'a set) - 1)
               else if (countable (UNIV :: 'a set))
                  then \<aleph>\<^sub>0
               else \<c>)"

syntax
  "_ucard" :: "type \<Rightarrow> ucard" ("UCARD'(_')")

translations
  "UCARD('a)" == "CONST ucard_of (TYPE('a))"

lemma ucard_non_empty:
  "\<U>(x) \<noteq> {}"
  by (induct x, auto)

lemma ucard_of_finite [simp]:
  "finite (UNIV :: 'a::continuum set) \<Longrightarrow> UCARD('a) = fin(card(UNIV :: 'a set) - 1)"
  by (simp add: ucard_of_def)

lemma ucard_of_countably_infinite [simp]:
  "\<lbrakk> countable(UNIV :: 'a::continuum set); infinite(UNIV :: 'a set) \<rbrakk> \<Longrightarrow> UCARD('a) = \<aleph>\<^sub>0"
  by (simp add: ucard_of_def)

lemma ucard_of_uncountably_infinite [simp]:
  "uncountable (UNIV :: 'a set) \<Longrightarrow> UCARD('a :: continuum) = \<c>"
  apply (simp add: ucard_of_def)
  using countable_finite apply blast
done

subsection \<open>Injection functions\<close>

definition uinject_finite :: "'a::finite \<Rightarrow> uuniv" where
"uinject_finite x = {to_nat_fin x}"

definition uinject_aleph0 :: "'a::{countable, infinite} \<Rightarrow> uuniv" where
"uinject_aleph0 x = {to_nat_bij x}"

definition uinject_continuum :: "'a::{continuum, infinite} \<Rightarrow> uuniv" where
"uinject_continuum x = to_nat_set_bij x"

definition uinject :: "'a::continuum \<Rightarrow> uuniv" where
"uinject x = (if (finite (UNIV :: 'a set))
                 then {to_nat_fin x}
               else if (countable (UNIV :: 'a set))
                  then {to_nat_on (UNIV :: 'a set) x}
               else to_nat_set x)"

definition uproject :: "uuniv \<Rightarrow> 'a::continuum" where
"uproject = inv uinject"

lemma uinject_finite:
  "finite (UNIV :: 'a::continuum set) \<Longrightarrow> uinject = (\<lambda> x :: 'a. {to_nat_fin x})"
  by (rule ext, auto simp add: uinject_def)

lemma uinject_uncountable:
  "uncountable (UNIV :: 'a::continuum set) \<Longrightarrow> (uinject :: 'a \<Rightarrow> uuniv) = to_nat_set"
  by (rule ext, auto simp add: uinject_def countable_finite)

lemma card_finite_lemma:
  assumes "finite (UNIV :: 'a set)"
  shows "x < card (UNIV :: 'a set) \<longleftrightarrow> x \<le> card (UNIV :: 'a set) - Suc 0"
proof -
  have "card (UNIV :: 'a set) > 0"
    by (simp add: assms finite_UNIV_card_ge_0)
  thus ?thesis
    by linarith
qed

text \<open>This is a key theorem that shows that the injection function provides a bijection between
        any continuum type and the subuniverse of types with a matching cardinality.\<close>

lemma uinject_bij:
  "bij_betw (uinject :: 'a::continuum \<Rightarrow> uuniv) UNIV \<U>(UCARD('a))"
proof (cases "finite (UNIV :: 'a set)")
  case True thus ?thesis
    apply (auto simp add: uinject_def bij_betw_def inj_on_def image_def card_finite_lemma[THEN sym])
    apply (auto simp add: inj_eq to_nat_fin_inj to_nat_fin_bounded)
    using to_nat_fin_ex apply blast
  done
  next
  case False note infinite = this thus ?thesis
  proof (cases "countable (UNIV :: 'a set)")
    case True thus ?thesis
      apply (auto simp add: uinject_def bij_betw_def inj_on_def infinite image_def card_finite_lemma[THEN sym])
      apply (meson image_to_nat_on infinite surj_def)
    done
    next
    case False note uncount = this thus ?thesis
      apply (simp add: uinject_uncountable)
      using to_nat_set_bij apply blast
    done
  qed
qed

lemma uinject_card [simp]: "uinject (x :: 'a::continuum) \<in> \<U>(UCARD('a))"
  by (metis bij_betw_def rangeI uinject_bij)

lemma uinject_inv [simp]:
  "uproject (uinject x) = x"
  by (metis UNIV_I bij_betw_def inv_into_f_f uinject_bij uproject_def)

lemma uproject_inv [simp]:
  "x \<in> \<U>(UCARD('a::continuum)) \<Longrightarrow> uinject ((uproject :: nat set \<Rightarrow> 'a)  x) = x"
  by (metis bij_betw_inv_into_right uinject_bij uproject_def)

subsection \<open>Deep variables\<close>

text \<open>A deep variable name stores both a name and the cardinality of the type it points to\<close>

record dname =
  dname_name :: "string"
  dname_card :: "ucard"

declare dname.splits [alpha_splits]

text \<open>A vstore is a function mapping deep variable names to corresponding values in the universe, such
        that the deep variables specified cardinality is matched by the value it points to.\<close>

typedef vstore = "{f :: dname \<Rightarrow> uuniv. \<forall> x. f(x) \<in> \<U>(dname_card x)}"
  apply (rule_tac x="\<lambda> x. {0}" in exI)
  apply (auto)
  apply (rename_tac x)
  apply (case_tac "dname_card x")
  apply (simp_all)
done

setup_lifting type_definition_vstore

typedef ('a::continuum) dvar = "{x :: dname. dname_card x = UCARD('a)}"
  morphisms dvar_dname Abs_dvar
  by (auto, meson dname.select_convs(2))

setup_lifting type_definition_dvar

lift_definition mk_dvar :: "string \<Rightarrow> ('a::{continuum,two}) dvar" ("\<lceil>_\<rceil>\<^sub>d")
is "\<lambda> n. \<lparr> dname_name = n, dname_card = UCARD('a) \<rparr>"
  by auto

lift_definition dvar_name :: "'a::continuum dvar \<Rightarrow> string" is "dname_name" .
lift_definition dvar_card :: "'a::continuum dvar \<Rightarrow> ucard" is "dname_card" .

lemma dvar_name [simp]: "dvar_name \<lceil>x\<rceil>\<^sub>d = x"
  by (transfer, simp)

term fun_lens

setup_lifting type_definition_lens_ext

lift_definition dvar_get :: "('a::continuum) dvar \<Rightarrow> vstore \<Rightarrow> 'a"
is "\<lambda> x s. (uproject :: uuniv \<Rightarrow> 'a) (s(x))" .

lift_definition dvar_put :: "('a::continuum) dvar \<Rightarrow> vstore \<Rightarrow> 'a \<Rightarrow> vstore"
is "\<lambda> (x :: dname) f (v :: 'a) . f(x := uinject v)"
  by (auto)

definition dvar_lens :: "('a::continuum) dvar \<Rightarrow> ('a \<Longrightarrow> vstore)" where
"dvar_lens x = \<lparr> lens_get = dvar_get x, lens_put = dvar_put x \<rparr>"

lemma vstore_vwb_lens [simp]:
  "vwb_lens (dvar_lens x)"
  apply (unfold_locales)
  apply (simp_all add: dvar_lens_def)
  apply (transfer, auto)
  apply (transfer)
  apply (metis fun_upd_idem uproject_inv)
  apply (transfer, simp)
done

lemma dvar_lens_indep_iff:
  fixes x :: "'a::{continuum,two} dvar" and y :: "'b::{continuum,two} dvar"
  shows "dvar_lens x \<bowtie> dvar_lens y \<longleftrightarrow> (dvar_dname x \<noteq> dvar_dname y)"
proof -
  obtain v1 v2 :: "'b::{continuum,two}" where v:"v1 \<noteq> v2"
    using two_diff by auto
  obtain u :: "'a::{continuum,two}" and v :: "'b::{continuum,two}"
    where uv: "uinject u \<noteq> uinject v"
    by (metis (full_types) uinject_inv v)
  show ?thesis
  proof (simp add: dvar_lens_def lens_indep_def, transfer, auto simp add: fun_upd_twist)
    fix y :: dname
    assume a1: "ucard_of (TYPE('b)::'b itself) = ucard_of (TYPE('a)::'a itself)"
    assume "dname_card y = ucard_of (TYPE('a)::'a itself)"
    assume a2:
      "\<forall> \<sigma>. (\<forall>x. \<sigma> x \<in> \<U>(dname_card x)) \<longrightarrow> (\<forall> v u. \<sigma>(y := uinject (u::'a)) = \<sigma>(y := uinject (v::'b)))"
      "\<forall> \<sigma>. (\<forall>x. \<sigma> x \<in> \<U>(dname_card x)) \<longrightarrow> (\<forall> v. (uproject (uinject v)::'a) = uproject (\<sigma> y))"
      "\<forall> \<sigma>. (\<forall>x. \<sigma> x \<in> \<U>(dname_card x)) \<longrightarrow> (\<forall> u. (uproject (uinject u)::'b) = uproject (\<sigma> y))"
    obtain NN :: "vstore \<Rightarrow> dname \<Rightarrow> nat set" where
      "\<And>v. \<forall>d. NN v d \<in> \<U>(dname_card d)"
      by (metis (lifting) Abs_vstore_cases mem_Collect_eq)
    then show False
      using a2 a1 by (metis fun_upd_same uv)
  qed
qed

text \<open>The vst class provides the location of the store in a larger type via a lens\<close>

class vst =
  fixes vstore_lens :: "vstore \<Longrightarrow> 'a" ("\<V>")
  assumes vstore_vwb_lens [simp]: "vwb_lens vstore_lens"

definition dvar_lift :: "'a::continuum dvar \<Rightarrow> ('a, '\<alpha>::vst) uvar" ("_\<up>" [999] 999) where
"dvar_lift x = dvar_lens x ;\<^sub>L vstore_lens"

definition [simp]: "in_dvar x = in_var (x\<up>)"
definition [simp]: "out_dvar x = out_var (x\<up>)"

adhoc_overloading
  ivar in_dvar and ovar out_dvar and svar dvar_lift

lemma uvar_dvar: "vwb_lens (x\<up>)"
  by (auto intro: comp_vwb_lens simp add: dvar_lift_def)

text \<open>Deep variables with different names are independent\<close>

lemma dvar_lift_indep_iff:
  fixes x :: "'a::{continuum,two} dvar" and y :: "'b::{continuum,two} dvar"
  shows "x\<up> \<bowtie> y\<up> \<longleftrightarrow> dvar_dname x \<noteq> dvar_dname y"
proof -
  have "x\<up> \<bowtie> y\<up> \<longleftrightarrow> dvar_lens x \<bowtie> dvar_lens y"
    by (metis dvar_lift_def lens_comp_indep_cong_left lens_indep_left_comp vst_class.vstore_vwb_lens vwb_lens_mwb)
  also have "... \<longleftrightarrow> dvar_dname x \<noteq> dvar_dname y"
    by (simp add: dvar_lens_indep_iff)
  finally show ?thesis .
qed

lemma dvar_indep_diff_name' [simp]:
  "x \<noteq> y \<Longrightarrow> \<lceil>x\<rceil>\<^sub>d\<up> \<bowtie> \<lceil>y\<rceil>\<^sub>d\<up>"
  by (simp add: dvar_lift_indep_iff mk_dvar.rep_eq)

text \<open>A basic record structure for vstores\<close>

record vstore_d =
  vstore :: vstore

instantiation vstore_d_ext :: (type) vst
begin
  definition "vstore_lens_vstore_d_ext = VAR vstore"
instance
  by (intro_classes, unfold_locales, simp_all add: vstore_lens_vstore_d_ext_def)
end

syntax
  "_sin_dvar"  :: "id \<Rightarrow> svar" ("%_" [999] 999)
  "_sout_dvar" :: "id \<Rightarrow> svar" ("%_\<acute>" [999] 999)

translations
  "_sin_dvar x"  => "CONST in_dvar (CONST mk_dvar IDSTR(x))"
  "_sout_dvar x" => "CONST out_dvar (CONST mk_dvar IDSTR(x))"

definition "MkDVar x = \<lceil>x\<rceil>\<^sub>d\<up>"

lemma uvar_MkDVar [simp]: "vwb_lens (MkDVar x)"
  by (simp add: MkDVar_def uvar_dvar)

lemma MkDVar_indep [simp]: "x \<noteq> y \<Longrightarrow> MkDVar x \<bowtie> MkDVar y"
  apply (rule lens_indepI)
  apply (simp_all add: MkDVar_def)
  apply (meson dvar_indep_diff_name' lens_indep_comm)
done

lemma MkDVar_put_comm [simp]:
  "m <\<^sub>l n \<Longrightarrow> put\<^bsub>MkDVar n\<^esub> (put\<^bsub>MkDVar m\<^esub> s u) v = put\<^bsub>MkDVar m\<^esub> (put\<^bsub>MkDVar n\<^esub> s v) u"
  by (simp add: lens_indep_comm)

text \<open>Set up parsing and pretty printing for deep variables\<close>

syntax
  "_dvar"     :: "id \<Rightarrow> svid" ("<_>")
  "_dvar_ty"  :: "id \<Rightarrow> type \<Rightarrow> svid" ("<_::_>")
  "_dvard"    :: "id \<Rightarrow> logic" ("<_>\<^sub>d")
  "_dvar_tyd" :: "id \<Rightarrow> type \<Rightarrow> logic" ("<_::_>\<^sub>d")

translations
  "_dvar x" => "CONST MkDVar IDSTR(x)"
  "_dvar_ty x a" => "_constrain (CONST MkDVar IDSTR(x)) (_uvar_ty a)"
  "_dvard x" => "CONST MkDVar IDSTR(x)"
  "_dvar_tyd x a" => "_constrain (CONST MkDVar IDSTR(x)) (_uvar_ty a)"

print_translation \<open>
let fun MkDVar_tr' _ [name] =
       Const (@{syntax_const "_dvar"}, dummyT) $
         Name_Utils.mk_id (HOLogic.dest_string (Name_Utils.deep_unmark_const name))
    | MkDVar_tr' _ _ = raise Match in
  [(@{const_syntax "MkDVar"}, MkDVar_tr')]
end
\<close>

definition dvar_exp :: "'t::continuum dvar \<Rightarrow> ('t, '\<alpha>::vst) uexpr"
where "dvar_exp x = var (dvar_lift x)"

definition unrest_dvar_upred :: "'a::continuum dvar \<Rightarrow> ('b, '\<alpha>::vst) uexpr \<Rightarrow> bool" where
"unrest_dvar_upred x P = unrest_upred (x\<up>) P"

definition subst_upd_dvar :: "('\<alpha>,'\<beta>::vst) psubst \<Rightarrow> 'a::continuum dvar \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('\<alpha>,'\<beta>) psubst" where
"subst_upd_dvar \<sigma> x v = subst_upd_uvar \<sigma> (x\<up>) v"

adhoc_overloading
  subst_upd subst_upd_dvar

declare subst_upd_dvar_def [upred_defs]

text \<open>Set up deep variable blocks\<close>

translations
  "var\<^bsub>T\<^esub> <x> \<bullet> P" => "var\<^bsub>T\<^esub> <x> ;; ((\<lambda> x. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end\<^bsub>T\<^esub> <x>"
  "var\<^bsub>T\<^esub> <x> :: 'a \<bullet> P" => "var\<^bsub>T\<^esub> <x::'a list> ;; ((\<lambda> x :: ('a, _) uvar. P) (CONST top_var (CONST MkDVar IDSTR(x)))) ;; end\<^bsub>T\<^esub> <x::'a list>"
  "var\<^bsub>T\<^esub> <x>  :: 'a := v \<bullet> P" => "var\<^bsub>T\<^esub> <x> :: 'a \<bullet> x ::=\<^bsub>T\<^esub> v ;; P"

(* Instantiate the vstore for reactive alphabets *)

instantiation alpha_rp'_ext :: (ordered_cancel_monoid_diff,vst) vst
begin
  definition vstore_lens_alpha_rp'_ext :: "vstore \<Longrightarrow> ('a, 'b) alpha_rp'_scheme" where
  "vstore_lens_alpha_rp'_ext = \<V> ;\<^sub>L \<Sigma>\<^sub>r"
instance
  by (intro_classes, simp add: vstore_lens_alpha_rp'_ext_def)
end
end