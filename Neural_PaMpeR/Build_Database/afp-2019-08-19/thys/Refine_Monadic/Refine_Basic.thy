section \<open>Basic Concepts\<close>
theory Refine_Basic
imports Main 
  "HOL-Library.Monad_Syntax" 
  Refine_Misc
  "Generic/RefineG_Recursion"
  "Generic/RefineG_Assert"
begin


subsection \<open>Nondeterministic Result Lattice and Monad\<close>
text \<open>
  In this section we introduce a complete lattice of result sets with an
  additional top element that represents failure. On this lattice, we define
  a monad: The return operator models a result that consists of a single value,
  and the bind operator models applying a function to all results.
  Binding a failure yields always a failure.
  
  In addition to the return operator, we also introduce the operator 
  \<open>RES\<close>, that embeds a set of results into our lattice. Its synonym for
  a predicate is \<open>SPEC\<close>.

  Program correctness is expressed by refinement, i.e., the expression
  \<open>M \<le> SPEC \<Phi>\<close> means that \<open>M\<close> is correct w.r.t.\ 
  specification \<open>\<Phi>\<close>. This suggests the following view on the program 
  lattice: The top-element is the result that is never correct. We call this
  result \<open>FAIL\<close>. The bottom element is the program that is always correct.
  It is called \<open>SUCCEED\<close>. An assertion can be encoded by failing if the
  asserted predicate is not true. Symmetrically, an assumption is encoded by
  succeeding if the predicate is not true. 
\<close>


datatype 'a nres = FAILi | RES "'a set"
text \<open>
  \<open>FAILi\<close> is only an internal notation, that should not be exposed to 
  the user.
  Instead, \<open>FAIL\<close> should be used, that is defined later as abbreviation 
  for the top element of the lattice.
\<close>
instantiation nres :: (type) complete_lattice
begin
fun less_eq_nres where
  "_ \<le> FAILi \<longleftrightarrow> True" |
  "(RES a) \<le> (RES b) \<longleftrightarrow> a\<subseteq>b" |
  "FAILi \<le> (RES _) \<longleftrightarrow> False"

fun less_nres where
  "FAILi < _ \<longleftrightarrow> False" |
  "(RES _) < FAILi \<longleftrightarrow> True" |
  "(RES a) < (RES b) \<longleftrightarrow> a\<subset>b"

fun sup_nres where
  "sup _ FAILi = FAILi" |
  "sup FAILi _ = FAILi" |
  "sup (RES a) (RES b) = RES (a\<union>b)"

fun inf_nres where 
  "inf x FAILi = x" |
  "inf FAILi x = x" |
  "inf (RES a) (RES b) = RES (a\<inter>b)"

definition "Sup X \<equiv> if FAILi\<in>X then FAILi else RES (\<Union>{x . RES x \<in> X})"
definition "Inf X \<equiv> if \<exists>x. RES x\<in>X then RES (\<Inter>{x . RES x \<in> X}) else FAILi"

definition "bot \<equiv> RES {}"
definition "top \<equiv> FAILi"

instance
  apply (intro_classes)
  unfolding Sup_nres_def Inf_nres_def bot_nres_def top_nres_def
  apply (case_tac x, case_tac [!] y, auto) []
  apply (case_tac x, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, simp_all) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, (case_tac [!] y)?, auto) []
  apply (case_tac x, case_tac [!] y, case_tac [!] z, auto) []
  apply (case_tac x, auto) []
  apply (case_tac z, fastforce+) []
  apply (case_tac x, auto) []
  apply (case_tac z, fastforce+) []
  apply auto []
  apply auto []
  done
  
end

abbreviation "FAIL \<equiv> top::'a nres"
abbreviation "SUCCEED \<equiv> bot::'a nres"
abbreviation "SPEC \<Phi> \<equiv> RES (Collect \<Phi>)"
definition "RETURN x \<equiv> RES {x}"

text \<open>We try to hide the original \<open>FAILi\<close>-element as well as possible. 
\<close>
lemma nres_cases[case_names FAIL RES, cases type]:
  obtains "M=FAIL" | X where "M=RES X"
  apply (cases M, fold top_nres_def) by auto

lemma nres_simp_internals: 
  "RES {} = SUCCEED"
  "FAILi = FAIL" 
  unfolding top_nres_def bot_nres_def by simp_all

lemma nres_inequalities[simp]: 
  "FAIL \<noteq> RES X"
  "FAIL \<noteq> SUCCEED" 
  "FAIL \<noteq> RETURN x"
  "SUCCEED \<noteq> FAIL"
  "SUCCEED \<noteq> RETURN x"
  "RES X \<noteq> FAIL"
  "RETURN x \<noteq> FAIL"
  "RETURN x \<noteq> SUCCEED"
  unfolding top_nres_def bot_nres_def RETURN_def
  by auto

lemma nres_more_simps[simp]:
  "SUCCEED = RES X \<longleftrightarrow> X={}"
  "RES X = SUCCEED \<longleftrightarrow> X={}"
  "RES X = RETURN x \<longleftrightarrow> X={x}"
  "RES X = RES Y \<longleftrightarrow> X=Y"
  "RETURN x = RES X \<longleftrightarrow> {x}=X"
  "RETURN x = RETURN y \<longleftrightarrow> x=y"
  unfolding top_nres_def bot_nres_def RETURN_def by auto

lemma nres_order_simps[simp]:
  "\<And>M. SUCCEED \<le> M"
  "\<And>M. M \<le> SUCCEED \<longleftrightarrow> M=SUCCEED"
  "\<And>M. M \<le> FAIL"
  "\<And>M. FAIL \<le> M \<longleftrightarrow> M=FAIL"
  "\<And>X Y. RES X \<le> RES Y \<longleftrightarrow> X\<le>Y"
  "\<And>X. Sup X = FAIL \<longleftrightarrow> FAIL\<in>X"
  "\<And>X f. Sup (f ` X) = FAIL \<longleftrightarrow> FAIL \<in> f ` X"
  "\<And>X. FAIL = Sup X \<longleftrightarrow> FAIL\<in>X"
  "\<And>X f. FAIL = Sup (f ` X) \<longleftrightarrow> FAIL \<in> f ` X"
  "\<And>X. FAIL\<in>X \<Longrightarrow> Sup X = FAIL"
  "\<And>X. FAIL\<in>f ` X \<Longrightarrow> Sup (f ` X) = FAIL"
  "\<And>A. Sup (RES ` A) = RES (Sup A)"
  "\<And>A. Sup (RES ` A) = RES (Sup A)"
  "\<And>A. A\<noteq>{} \<Longrightarrow> Inf (RES`A) = RES (Inf A)"
  "\<And>A. A\<noteq>{} \<Longrightarrow> Inf (RES ` A) = RES (Inf A)"
  "Inf {} = FAIL"
  "Inf UNIV = SUCCEED"
  "Sup {} = SUCCEED"
  "Sup UNIV = FAIL"
  "\<And>x y. RETURN x \<le> RETURN y \<longleftrightarrow> x=y"
  "\<And>x Y. RETURN x \<le> RES Y \<longleftrightarrow> x\<in>Y"
  "\<And>X y. RES X \<le> RETURN y \<longleftrightarrow> X \<subseteq> {y}"
  unfolding Sup_nres_def Inf_nres_def RETURN_def
  by (auto simp add: bot_unique top_unique nres_simp_internals)

lemma Sup_eq_RESE:
  assumes "Sup A = RES B"
  obtains C where "A=RES`C" and "B=Sup C"
proof -
  show ?thesis
    using assms unfolding Sup_nres_def
    apply (simp split: if_split_asm)
    apply (rule_tac C="{X. RES X \<in> A}" in that)
    apply auto []
    apply (case_tac x, auto simp: nres_simp_internals) []
    apply (auto simp: nres_simp_internals) []
    done
qed

declare nres_simp_internals[simp]

subsubsection \<open>Pointwise Reasoning\<close>

ML \<open>
  structure refine_pw_simps = Named_Thms
    ( val name = @{binding refine_pw_simps}
      val description = "Refinement Framework: " ^
        "Simplifier rules for pointwise reasoning" )
\<close>    
setup \<open>refine_pw_simps.setup\<close>
  
definition "nofail S \<equiv> S\<noteq>FAIL"
definition "inres S x \<equiv> RETURN x \<le> S"

lemma nofail_simps[simp, refine_pw_simps]:
  "nofail FAIL \<longleftrightarrow> False"
  "nofail (RES X) \<longleftrightarrow> True"
  "nofail (RETURN x) \<longleftrightarrow> True"
  "nofail SUCCEED \<longleftrightarrow> True"
  unfolding nofail_def
  by (simp_all add: RETURN_def)

lemma inres_simps[simp, refine_pw_simps]:
  "inres FAIL = (\<lambda>_. True)"
  "inres (RES X) = (\<lambda>x. x\<in>X)"
  "inres (RETURN x) = (\<lambda>y. x=y)"
  "inres SUCCEED = (\<lambda>_. False)"
  unfolding inres_def [abs_def]
  by (auto simp add: RETURN_def)

lemma not_nofail_iff: 
  "\<not>nofail S \<longleftrightarrow> S=FAIL" by (cases S) auto

lemma not_nofail_inres[simp, refine_pw_simps]: 
  "\<not>nofail S \<Longrightarrow> inres S x" 
  apply (cases S) by auto

lemma intro_nofail[refine_pw_simps]: 
  "S\<noteq>FAIL \<longleftrightarrow> nofail S"
  "FAIL\<noteq>S \<longleftrightarrow> nofail S"
  by (cases S, simp_all)+

text \<open>The following two lemmas will introduce pointwise reasoning for
  orderings and equalities.\<close>
lemma pw_le_iff: 
  "S \<le> S' \<longleftrightarrow> (nofail S'\<longrightarrow> (nofail S \<and> (\<forall>x. inres S x \<longrightarrow> inres S' x)))"
  apply (cases S, simp_all)
  apply (case_tac [!] S', auto)
  done

lemma pw_eq_iff:
  "S=S' \<longleftrightarrow> (nofail S = nofail S' \<and> (\<forall>x. inres S x \<longleftrightarrow> inres S' x))"
  apply (rule iffI)
  apply simp
  apply (rule antisym)
  apply (simp_all add: pw_le_iff)
  done

lemma pw_flat_le_iff: "flat_le S S' \<longleftrightarrow> 
  (\<exists>x. inres S x) \<longrightarrow> (nofail S \<longleftrightarrow> nofail S') \<and> (\<forall>x. inres S x \<longleftrightarrow> inres S' x)"
  by (auto simp : flat_ord_def pw_eq_iff)
  
lemma pw_flat_ge_iff: "flat_ge S S' \<longleftrightarrow> 
  (nofail S) \<longrightarrow> nofail S' \<and> (\<forall>x. inres S x \<longleftrightarrow> inres S' x)"
  apply (simp add: flat_ord_def pw_eq_iff) apply safe
  apply simp
  apply simp
  apply simp
  apply (rule ccontr)
  apply simp
  done

lemmas pw_ords_iff = pw_le_iff pw_flat_le_iff pw_flat_ge_iff

lemma pw_leI: 
  "(nofail S'\<longrightarrow> (nofail S \<and> (\<forall>x. inres S x \<longrightarrow> inres S' x))) \<Longrightarrow> S \<le> S'"
  by (simp add: pw_le_iff)

lemma pw_leI': 
  assumes "nofail S' \<Longrightarrow> nofail S"
  assumes "\<And>x. \<lbrakk>nofail S'; inres S x\<rbrakk> \<Longrightarrow> inres S' x"
  shows "S \<le> S'"
  using assms
  by (simp add: pw_le_iff)

lemma pw_eqI: 
  assumes "nofail S = nofail S'" 
  assumes "\<And>x. inres S x \<longleftrightarrow> inres S' x" 
  shows "S=S'"
  using assms by (simp add: pw_eq_iff)

lemma pwD1:
  assumes "S\<le>S'" "nofail S'" 
  shows "nofail S"
  using assms by (simp add: pw_le_iff)

lemma pwD2:
  assumes "S\<le>S'" "inres S x"
  shows "inres S' x"
  using assms 
  by (auto simp add: pw_le_iff)

lemmas pwD = pwD1 pwD2

text \<open>
  When proving refinement, we may assume that the refined program does not 
  fail.\<close>
lemma le_nofailI: "\<lbrakk> nofail M' \<Longrightarrow> M \<le> M' \<rbrakk> \<Longrightarrow> M \<le> M'"
  by (cases M') auto

text \<open>The following lemmas push pointwise reasoning over operators,
  thus converting an expression over lattice operators into a logical
  formula.\<close>

lemma pw_sup_nofail[refine_pw_simps]:
  "nofail (sup a b) \<longleftrightarrow> nofail a \<and> nofail b"
  apply (cases a, simp)
  apply (cases b, simp_all)
  done

lemma pw_sup_inres[refine_pw_simps]:
  "inres (sup a b) x \<longleftrightarrow> inres a x \<or> inres b x"
  apply (cases a, simp)
  apply (cases b, simp)
  apply (simp)
  done

lemma pw_Sup_inres[refine_pw_simps]: "inres (Sup X) r \<longleftrightarrow> (\<exists>M\<in>X. inres M r)"
  apply (cases "Sup X")
  apply (simp)
  apply (erule bexI[rotated])
  apply simp
  apply (erule Sup_eq_RESE)
  apply (simp)
  done

lemma pw_SUP_inres [refine_pw_simps]: "inres (Sup (f ` X)) r \<longleftrightarrow> (\<exists>M\<in>X. inres (f M) r)"
  using pw_Sup_inres [of "f ` X"] by simp

lemma pw_Sup_nofail[refine_pw_simps]: "nofail (Sup X) \<longleftrightarrow> (\<forall>x\<in>X. nofail x)"
  apply (cases "Sup X")
  apply force
  apply simp
  apply (erule Sup_eq_RESE)
  apply auto
  done

lemma pw_SUP_nofail [refine_pw_simps]: "nofail (Sup (f ` X)) \<longleftrightarrow> (\<forall>x\<in>X. nofail (f x))"
  using pw_Sup_nofail [of "f ` X"] by simp

lemma pw_inf_nofail[refine_pw_simps]:
  "nofail (inf a b) \<longleftrightarrow> nofail a \<or> nofail b"
  apply (cases a, simp)
  apply (cases b, simp_all)
  done

lemma pw_inf_inres[refine_pw_simps]:
  "inres (inf a b) x \<longleftrightarrow> inres a x \<and> inres b x"
  apply (cases a, simp)
  apply (cases b, simp)
  apply (simp)
  done

lemma pw_Inf_nofail[refine_pw_simps]: "nofail (Inf C) \<longleftrightarrow> (\<exists>x\<in>C. nofail x)"
  apply (cases "C={}")
  apply simp
  apply (cases "Inf C")
  apply (subgoal_tac "C={FAIL}")
  apply simp
  apply auto []
  apply (subgoal_tac "C\<noteq>{FAIL}")
  apply (auto simp: not_nofail_iff) []
  apply auto []
  done

lemma pw_INF_nofail [refine_pw_simps]: "nofail (Inf (f ` C)) \<longleftrightarrow> (\<exists>x\<in>C. nofail (f x))"
  using pw_Inf_nofail [of "f ` C"] by simp

lemma pw_Inf_inres[refine_pw_simps]: "inres (Inf C) r \<longleftrightarrow> (\<forall>M\<in>C. inres M r)"
  apply (unfold Inf_nres_def)
  apply auto
  apply (case_tac M)
  apply force
  apply force
  apply (case_tac M)
  apply force
  apply force
  done

lemma pw_INF_inres [refine_pw_simps]: "inres (Inf (f ` C)) r \<longleftrightarrow> (\<forall>M\<in>C. inres (f M) r)"
  using pw_Inf_inres [of "f ` C"] by simp

lemma nofail_RES_conv: "nofail m \<longleftrightarrow> (\<exists>M. m=RES M)" by (cases m) auto

primrec the_RES where "the_RES (RES X) = X"
lemma the_RES_inv[simp]: "nofail m \<Longrightarrow> RES (the_RES m) = m"
  by (cases m) auto

definition [refine_pw_simps]: "nf_inres m x \<equiv> nofail m \<and> inres m x"

lemma nf_inres_RES[simp]: "nf_inres (RES X) x \<longleftrightarrow> x\<in>X" 
  by (simp add: refine_pw_simps)
  
lemma nf_inres_SPEC[simp]: "nf_inres (SPEC \<Phi>) x \<longleftrightarrow> \<Phi> x" 
  by (simp add: refine_pw_simps)

lemma nofail_antimono_fun: "f \<le> g \<Longrightarrow> (nofail (g x) \<longrightarrow> nofail (f x))"
  by (auto simp: pw_le_iff dest: le_funD)


subsubsection \<open>Monad Operators\<close>
definition bind where "bind M f \<equiv> case M of 
  FAILi \<Rightarrow> FAIL |
  RES X \<Rightarrow> Sup (f`X)"

lemma bind_FAIL[simp]: "bind FAIL f = FAIL"
  unfolding bind_def by (auto split: nres.split)

lemma bind_SUCCEED[simp]: "bind SUCCEED f = SUCCEED"
  unfolding bind_def by (auto split: nres.split)

lemma bind_RES: "bind (RES X) f = Sup (f`X)" unfolding bind_def 
  by (auto)

adhoc_overloading
  Monad_Syntax.bind Refine_Basic.bind

lemma pw_bind_nofail[refine_pw_simps]:
  "nofail (bind M f) \<longleftrightarrow> (nofail M \<and> (\<forall>x. inres M x \<longrightarrow> nofail (f x)))"
  apply (cases M)
  by (auto simp: bind_RES refine_pw_simps)
  
lemma pw_bind_inres[refine_pw_simps]:
  "inres (bind M f) = (\<lambda>x. nofail M \<longrightarrow> (\<exists>y. (inres M y \<and> inres (f y) x)))"
  apply (rule ext)
  apply (cases M)
  apply (auto simp add: bind_RES refine_pw_simps)
  done

lemma pw_bind_le_iff:
  "bind M f \<le> S \<longleftrightarrow> (nofail S \<longrightarrow> nofail M) \<and> 
    (\<forall>x. nofail M \<and> inres M x \<longrightarrow> f x \<le> S)"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma pw_bind_leI: "\<lbrakk> 
  nofail S \<Longrightarrow> nofail M; \<And>x. \<lbrakk>nofail M; inres M x\<rbrakk> \<Longrightarrow> f x \<le> S\<rbrakk> 
  \<Longrightarrow> bind M f \<le> S"
  by (simp add: pw_bind_le_iff)

text \<open>\paragraph{Monad Laws}\<close>
lemma nres_monad1[simp]: "bind (RETURN x) f = f x"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemma nres_monad2[simp]: "bind M RETURN = M"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemma nres_monad3[simp]: "bind (bind M f) g = bind M (\<lambda>x. bind (f x) g)"
  by (rule pw_eqI) (auto simp: refine_pw_simps)
lemmas nres_monad_laws = nres_monad1 nres_monad2 nres_monad3

text \<open>\paragraph{Congruence rule for bind}\<close>
lemma bind_cong:
  assumes "m=m'"
  assumes "\<And>x. RETURN x \<le> m' \<Longrightarrow> f x = f' x"
  shows "bind m f = bind m' f'"  
  using assms
  by (auto simp: refine_pw_simps pw_eq_iff pw_le_iff)

text \<open>\paragraph{Monotonicity and Related Properties}\<close>
lemma bind_mono[refine_mono]:
  "\<lbrakk> M \<le> M'; \<And>x. RETURN x \<le> M \<Longrightarrow> f x \<le> f' x \<rbrakk> \<Longrightarrow> bind M f \<le> bind M' f'"
  (*"\<lbrakk> flat_le M M'; \<And>x. flat_le (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_le (bind M f) (bind M' f')"*)
  "\<lbrakk> flat_ge M M'; \<And>x. flat_ge (f x) (f' x) \<rbrakk> \<Longrightarrow> flat_ge (bind M f) (bind M' f')"
  apply (auto simp: refine_pw_simps pw_ords_iff) []
  apply (auto simp: refine_pw_simps pw_ords_iff) []
  done

lemma bind_mono1[simp, intro!]: "mono (\<lambda>M. bind M f)"
  apply (rule monoI)
  apply (rule bind_mono)
  by auto

lemma bind_mono1'[simp, intro!]: "mono bind"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule bind_mono)
  by auto

lemma bind_mono2'[simp, intro!]: "mono (bind M)"
  apply (rule monoI)
  apply (rule bind_mono)
  by (auto dest: le_funD)


lemma bind_distrib_sup1: "bind (sup M N) f = sup (bind M f) (bind N f)"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma  bind_distrib_sup2: "bind m (\<lambda>x. sup (f x) (g x)) = sup (bind m f) (bind m g)"
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma bind_distrib_Sup1: "bind (Sup M) f = (SUP m\<in>M. bind m f)" 
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma bind_distrib_Sup2: "F\<noteq>{} \<Longrightarrow> bind m (Sup F) = (SUP f\<in>F. bind m f)"
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma RES_Sup_RETURN: "Sup (RETURN`X) = RES X"
  by (rule pw_eqI) (auto simp add: refine_pw_simps)

    
subsection \<open>VCG Setup\<close>
  
lemma SPEC_cons_rule:
  assumes "m \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> \<Psi> x"
  shows "m \<le> SPEC \<Psi>"
  using assms by (auto simp: pw_le_iff)
  
lemmas SPEC_trans = order_trans[where z="SPEC Postcond" for Postcond, zero_var_indexes]
  
ML \<open>
structure Refine = struct

  structure vcg = Named_Thms
    ( val name = @{binding refine_vcg}
      val description = "Refinement Framework: " ^ 
        "Verification condition generation rules (intro)" )

  structure vcg_cons = Named_Thms
    ( val name = @{binding refine_vcg_cons}
      val description = "Refinement Framework: " ^
        "Consequence rules tried by VCG" )

  structure refine0 = Named_Thms
    ( val name = @{binding refine0}
      val description = "Refinement Framework: " ^
        "Refinement rules applied first (intro)" )

  structure refine = Named_Thms
    ( val name = @{binding refine}
      val description = "Refinement Framework: Refinement rules (intro)" )

  structure refine2 = Named_Thms
    ( val name = @{binding refine2}
      val description = "Refinement Framework: " ^
        "Refinement rules 2nd stage (intro)" )

  (* If set to true, the product splitter of refine_rcg is disabled. *)
  val no_prod_split = 
    Attrib.setup_config_bool @{binding refine_no_prod_split} (K false);

  fun rcg_tac add_thms ctxt = 
    let 
      val cons_thms = vcg_cons.get ctxt
      val ref_thms = (refine0.get ctxt 
        @ add_thms @ refine.get ctxt @ refine2.get ctxt);
      val prod_ss = (Splitter.add_split @{thm prod.split} 
        (put_simpset HOL_basic_ss ctxt));
      val prod_simp_tac = 
        if Config.get ctxt no_prod_split then 
          K no_tac
        else
          (simp_tac prod_ss THEN' 
            REPEAT_ALL_NEW (resolve_tac ctxt @{thms impI allI}));
    in
      REPEAT_ALL_NEW_FWD (DETERM o FIRST' [
        resolve_tac ctxt ref_thms,
        resolve_tac ctxt cons_thms THEN' resolve_tac ctxt ref_thms,
        prod_simp_tac
      ])
    end;

  fun post_tac ctxt = REPEAT_ALL_NEW_FWD (FIRST' [
    eq_assume_tac,
    (*match_tac ctxt thms,*)
    SOLVED' (Tagged_Solver.solve_tac ctxt)]) 
         

end;
\<close>
setup \<open>Refine.vcg.setup\<close>
setup \<open>Refine.vcg_cons.setup\<close>
setup \<open>Refine.refine0.setup\<close>
setup \<open>Refine.refine.setup\<close>
setup \<open>Refine.refine2.setup\<close>
(*setup {* Refine.refine_post.setup *}*)

method_setup refine_rcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac add_thms ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement conditions"

method_setup refine_vcg = 
  \<open>Attrib.thms >> (fn add_thms => fn ctxt => SIMPLE_METHOD' (
    Refine.rcg_tac (add_thms @ Refine.vcg.get ctxt) ctxt THEN_ALL_NEW_FWD (TRY o Refine.post_tac ctxt)
  ))\<close> 
  "Refinement framework: Generate refinement and verification conditions"


  (* Use tagged-solver instead!
  method_setup refine_post = 
    {* Scan.succeed (fn ctxt => SIMPLE_METHOD' (
      Refine.post_tac ctxt
    )) *} 
    "Refinement framework: Postprocessing of refinement goals"
    *)

declare SPEC_cons_rule[refine_vcg_cons]    
    
    
subsection \<open>Data Refinement\<close>
text \<open>
  In this section we establish a notion of pointwise data refinement, by
  lifting a relation \<open>R\<close> between concrete and abstract values to 
  our result lattice.

  Given a relation \<open>R\<close>, we define a {\em concretization function}
  \<open>\<Down>R\<close> that takes an abstract result, and returns a concrete result.
  The concrete result contains all values that are mapped by \<open>R\<close> to
  a value in the abstract result.

  Note that our concretization function forms no Galois connection, i.e.,
  in general there is no \<open>\<alpha>\<close> such that 
  \<open>m \<le>\<Down> R m'\<close> is equivalent to \<open>\<alpha> m \<le> m'\<close>.
  However, we get a Galois connection for the special case of 
  single-valued relations.
 
  Regarding data refinement as Galois connections is inspired by \cite{mmo97},
  that also uses the adjuncts of
  a Galois connection to express data refinement by program refinement.
\<close>

definition conc_fun ("\<Down>") where
  "conc_fun R m \<equiv> case m of FAILi \<Rightarrow> FAIL | RES X \<Rightarrow> RES (R\<inverse>``X)"

definition abs_fun ("\<Up>") where
  "abs_fun R m \<equiv> case m of FAILi \<Rightarrow> FAIL 
    | RES X \<Rightarrow> if X\<subseteq>Domain R then RES (R``X) else FAIL"

lemma 
  conc_fun_FAIL[simp]: "\<Down>R FAIL = FAIL" and
  conc_fun_RES: "\<Down>R (RES X) = RES (R\<inverse>``X)"
  unfolding conc_fun_def by (auto split: nres.split)

lemma abs_fun_simps[simp]: 
  "\<Up>R FAIL = FAIL"
  "X\<subseteq>Domain R \<Longrightarrow> \<Up>R (RES X) = RES (R``X)"
  "\<not>(X\<subseteq>Domain R) \<Longrightarrow> \<Up>R (RES X) = FAIL"
  unfolding abs_fun_def by (auto split: nres.split)
  
context fixes R assumes SV: "single_valued R" begin
lemma conc_abs_swap: "m' \<le> \<Down>R m \<longleftrightarrow> \<Up>R m' \<le> m"
  unfolding conc_fun_def abs_fun_def using SV
  by (auto split: nres.split)
    (metis ImageE converseD single_valuedD subsetD)

lemma ac_galois: "galois_connection (\<Up>R) (\<Down>R)"
  apply (unfold_locales)
  by (rule conc_abs_swap)

end

lemma pw_abs_nofail[refine_pw_simps]: 
  "nofail (\<Up>R M) \<longleftrightarrow> (nofail M \<and> (\<forall>x. inres M x \<longrightarrow> x\<in>Domain R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_simps abs_fun_def)
  done

lemma pw_abs_inres[refine_pw_simps]: 
  "inres (\<Up>R M) a \<longleftrightarrow> (nofail (\<Up>R M) \<longrightarrow> (\<exists>c. inres M c \<and> (c,a)\<in>R))"
  apply (cases M)
  apply simp
  apply (auto simp: abs_fun_def)
  done

lemma pw_conc_nofail[refine_pw_simps]: 
  "nofail (\<Down>R S) = nofail S"
  by (cases S) (auto simp: conc_fun_RES)

lemma pw_conc_inres[refine_pw_simps]:
  "inres (\<Down>R S') = (\<lambda>s. nofail S' 
  \<longrightarrow> (\<exists>s'. (s,s')\<in>R \<and> inres S' s'))"
  apply (rule ext)
  apply (cases S')
  apply (auto simp: conc_fun_RES)
  done

lemma abs_fun_strict[simp]:
  "\<Up> R SUCCEED = SUCCEED"
  unfolding abs_fun_def by (auto split: nres.split)

lemma conc_fun_strict[simp]:
  "\<Down> R SUCCEED = SUCCEED"
  unfolding conc_fun_def by (auto split: nres.split)

lemma conc_fun_mono[simp, intro!]: "mono (\<Down>R)"
  by rule (auto simp: pw_le_iff refine_pw_simps)

lemma abs_fun_mono[simp, intro!]: "mono (\<Up>R)"
  by rule (auto simp: pw_le_iff refine_pw_simps)

lemma conc_fun_R_mono:
  assumes "R \<subseteq> R'"
  shows "\<Down>R M \<le> \<Down>R' M"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)
    
lemma conc_fun_chain: "\<Down>R (\<Down>S M) = \<Down>(R O S) M"
  unfolding conc_fun_def
  by (auto split: nres.split)

lemma conc_Id[simp]: "\<Down>Id = id"
  unfolding conc_fun_def [abs_def] by (auto split: nres.split)

lemma abs_Id[simp]: "\<Up>Id = id"
  unfolding abs_fun_def [abs_def] by (auto split: nres.split)

lemma conc_fun_fail_iff[simp]: 
  "\<Down>R S = FAIL \<longleftrightarrow> S=FAIL"
  "FAIL = \<Down>R S \<longleftrightarrow> S=FAIL"
  by (auto simp add: pw_eq_iff refine_pw_simps)

lemma conc_trans[trans]:
  assumes A: "C \<le> \<Down>R B" and B: "B \<le> \<Down>R' A" 
  shows "C \<le> \<Down>R (\<Down>R' A)"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

lemma abs_trans[trans]:
  assumes A: "\<Up>R C \<le> B" and B: "\<Up>R' B \<le> A" 
  shows "\<Up>R' (\<Up>R C) \<le> A"
  using assms by (fastforce simp: pw_le_iff refine_pw_simps)

subsubsection \<open>Transitivity Reasoner Setup\<close>

text \<open>WARNING: The order of the single statements is important here!\<close>
lemma conc_trans_additional[trans]:
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>R  C \<Longrightarrow> A\<le>\<Down>R  C"
  "\<And>A B C. A\<le>\<Down>R  B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>\<Down>R  C"

  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>\<Down>Id B \<Longrightarrow> B\<le>    C \<Longrightarrow> A\<le>    C"
  "\<And>A B C. A\<le>    B \<Longrightarrow> B\<le>\<Down>Id C \<Longrightarrow> A\<le>    C"
  using conc_trans[where R=R and R'=Id]
  by (auto intro: order_trans)

text \<open>WARNING: The order of the single statements is important here!\<close>
lemma abs_trans_additional[trans]:
  "\<And>A B C. \<lbrakk> A \<le> B; \<Up> R B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; \<Up> R B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> R A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> \<Up> R A \<le> C"

  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"
  "\<And>A B C. \<lbrakk>\<Up> Id A \<le> B; B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"
  "\<And>A B C. \<lbrakk>A \<le> B; \<Up> Id B \<le> C\<rbrakk> \<Longrightarrow> A \<le> C"

  apply (auto simp: refine_pw_simps pw_le_iff)
  apply fastforce+
  done


subsection \<open>Derived Program Constructs\<close>
text \<open>
  In this section, we introduce some programming constructs that are derived 
  from the basic monad and ordering operations of our nondeterminism monad.
\<close>
subsubsection \<open>ASSUME and ASSERT\<close>

definition ASSERT where "ASSERT \<equiv> iASSERT RETURN"
definition ASSUME where "ASSUME \<equiv> iASSUME RETURN"
interpretation assert?: generic_Assert bind RETURN ASSERT ASSUME
  apply unfold_locales
  by (simp_all add: ASSERT_def ASSUME_def)

text \<open>Order matters! \<close>
lemmas [refine_vcg] = ASSERT_leI 
lemmas [refine_vcg] = le_ASSUMEI 
lemmas [refine_vcg] = le_ASSERTI 
lemmas [refine_vcg] = ASSUME_leI
    
    
lemma pw_ASSERT[refine_pw_simps]:
  "nofail (ASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inres (ASSERT \<Phi>) x"
  by (cases \<Phi>, simp_all)+

lemma pw_ASSUME[refine_pw_simps]:
  "nofail (ASSUME \<Phi>)"
  "inres (ASSUME \<Phi>) x \<longleftrightarrow> \<Phi>"
  by (cases \<Phi>, simp_all)+

subsubsection \<open>Recursion\<close>
lemma pw_REC_nofail: 
  shows "nofail (REC B x) \<longleftrightarrow> trimono B \<and>
  (\<exists>F. (\<forall>x. 
    nofail (F x) \<longrightarrow> nofail (B F x) 
    \<and> (\<forall>x'. inres (B F x) x' \<longrightarrow> inres (F x) x')
  ) \<and> nofail (F x))"
proof -
  have "nofail (REC B x) \<longleftrightarrow> trimono B \<and>
  (\<exists>F. (\<forall>x. B F x \<le> F x) \<and> nofail (F x))"
    unfolding REC_def lfp_def
    apply (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
    done
  thus ?thesis
    unfolding pw_le_iff .
qed

lemma pw_REC_inres: 
  "inres (REC B x) x' = (trimono B \<longrightarrow>
  (\<forall>F. (\<forall>x''. 
    nofail (F x'') \<longrightarrow> nofail (B F x'') 
    \<and> (\<forall>x. inres (B F x'') x \<longrightarrow> inres (F x'') x)) 
    \<longrightarrow> inres (F x) x'))"
proof -
  have "inres (REC B x) x' 
    \<longleftrightarrow> (trimono B \<longrightarrow> (\<forall>F. (\<forall>x''. B F x'' \<le> F x'') \<longrightarrow> inres (F x) x'))"
    unfolding REC_def lfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis unfolding pw_le_iff .
qed
  
lemmas pw_REC = pw_REC_inres pw_REC_nofail

lemma pw_RECT_nofail: 
  shows "nofail (RECT B x) \<longleftrightarrow> trimono B \<and>
  (\<forall>F. (\<forall>y. nofail (B F y) \<longrightarrow>
             nofail (F y) \<and> (\<forall>x. inres (F y) x \<longrightarrow> inres (B F y) x)) \<longrightarrow>
        nofail (F x))"
proof -
  have "nofail (RECT B x) \<longleftrightarrow> (trimono B \<and> (\<forall>F. (\<forall>y. F y \<le> B F y) \<longrightarrow> nofail (F x)))"
    unfolding RECT_gfp_def gfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis
    unfolding pw_le_iff .
qed

lemma pw_RECT_inres: 
  shows "inres (RECT B x) x' = (trimono B \<longrightarrow>
   (\<exists>M. (\<forall>y. nofail (B M y) \<longrightarrow>
             nofail (M y) \<and> (\<forall>x. inres (M y) x \<longrightarrow> inres (B M y) x)) \<and>
        inres (M x) x'))"
proof -
  have "inres (RECT B x) x' \<longleftrightarrow> trimono B \<longrightarrow> (\<exists>M. (\<forall>y. M y \<le> B M y) \<and> inres (M x) x')"
    unfolding RECT_gfp_def gfp_def
    by (auto simp: refine_pw_simps intro: le_funI dest: le_funD)
  thus ?thesis unfolding pw_le_iff .
qed
  
lemmas pw_RECT = pw_RECT_inres pw_RECT_nofail

  
  
subsection \<open>Proof Rules\<close>

subsubsection \<open>Proving Correctness\<close>
text \<open>
  In this section, we establish Hoare-like rules to prove that a program
  meets its specification.
\<close>
lemma le_SPEC_UNIV_rule [refine_vcg]: 
  "m \<le> SPEC (\<lambda>_. True) \<Longrightarrow> m \<le> RES UNIV" by auto
  
lemma RETURN_rule[refine_vcg]: "\<Phi> x \<Longrightarrow> RETURN x \<le> SPEC \<Phi>"
  by (auto simp: RETURN_def)
lemma RES_rule[refine_vcg]: "\<lbrakk>\<And>x. x\<in>S \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> RES S \<le> SPEC \<Phi>"
  by auto
lemma SUCCEED_rule[refine_vcg]: "SUCCEED \<le> SPEC \<Phi>" by auto
lemma FAIL_rule: "False \<Longrightarrow> FAIL \<le> SPEC \<Phi>" by auto
lemma SPEC_rule[refine_vcg]: "\<lbrakk>\<And>x. \<Phi> x \<Longrightarrow> \<Phi>' x\<rbrakk> \<Longrightarrow> SPEC \<Phi> \<le> SPEC \<Phi>'" by auto

lemma RETURN_to_SPEC_rule[refine_vcg]: "m\<le>SPEC ((=) v) \<Longrightarrow> m\<le>RETURN v"
  by (simp add: pw_le_iff refine_pw_simps)

lemma Sup_img_rule_complete: 
  "(\<forall>x. x\<in>S \<longrightarrow> f x \<le> SPEC \<Phi>) \<longleftrightarrow> Sup (f`S) \<le> SPEC \<Phi>"
  apply rule
  apply (rule pw_leI)
  apply (auto simp: pw_le_iff refine_pw_simps) []
  apply (intro allI impI)
  apply (rule pw_leI)
  apply (auto simp: pw_le_iff refine_pw_simps) []
  done

lemma SUP_img_rule_complete: 
  "(\<forall>x. x\<in>S \<longrightarrow> f x \<le> SPEC \<Phi>) \<longleftrightarrow> Sup (f ` S) \<le> SPEC \<Phi>"
  using Sup_img_rule_complete [of S f] by simp

lemma Sup_img_rule[refine_vcg]: 
  "\<lbrakk> \<And>x. x\<in>S \<Longrightarrow> f x \<le> SPEC \<Phi> \<rbrakk> \<Longrightarrow> Sup(f`S) \<le> SPEC \<Phi>"
  by (auto simp: SUP_img_rule_complete[symmetric])

text \<open>This lemma is just to demonstrate that our rule is complete.\<close>
lemma bind_rule_complete: "bind M f \<le> SPEC \<Phi> \<longleftrightarrow> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>)"
  by (auto simp: pw_le_iff refine_pw_simps)
lemma bind_rule[refine_vcg]: 
  "\<lbrakk> M \<le> SPEC (\<lambda>x. f x \<le> SPEC \<Phi>) \<rbrakk> \<Longrightarrow> bind M (\<lambda>x. f x) \<le> SPEC \<Phi>"
  \<comment> \<open>Note: @{text "\<eta>"}-expanded version helps Isabelle's unification to keep meaningful 
      variable names from the program\<close>
  by (auto simp: bind_rule_complete)

lemma ASSUME_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> ASSUME \<Phi> \<le> SPEC \<Psi>"
  by (cases \<Phi>) auto

lemma ASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> ASSERT \<Phi> \<le> SPEC \<Psi>" by auto

lemma prod_rule[refine_vcg]: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> S a b \<le> SPEC \<Phi>\<rbrakk> \<Longrightarrow> case_prod S p \<le> SPEC \<Phi>"
  by (auto split: prod.split)

(* TODO: Add a simplifier setup that normalizes nested case-expressions to
  the vcg! *)
lemma prod2_rule[refine_vcg]:
  assumes "\<And>a b c d. \<lbrakk>ab=(a,b); cd=(c,d)\<rbrakk> \<Longrightarrow> f a b c d \<le> SPEC \<Phi>"
  shows "(\<lambda>(a,b) (c,d). f a b c d) ab cd \<le> SPEC \<Phi>"
  using assms
  by (auto split: prod.split)

lemma if_rule[refine_vcg]: 
  "\<lbrakk> b \<Longrightarrow> S1 \<le> SPEC \<Phi>; \<not>b \<Longrightarrow> S2 \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> (if b then S1 else S2) \<le> SPEC \<Phi>"
  by (auto)

lemma option_rule[refine_vcg]: 
  "\<lbrakk> v=None \<Longrightarrow> S1 \<le> SPEC \<Phi>; \<And>x. v=Some x \<Longrightarrow> f2 x \<le> SPEC \<Phi>\<rbrakk> 
  \<Longrightarrow> case_option S1 f2 v \<le> SPEC \<Phi>"
  by (auto split: option.split)

lemma Let_rule[refine_vcg]:
  "f x \<le> SPEC \<Phi> \<Longrightarrow> Let x f \<le> SPEC \<Phi>" by auto

lemma Let_rule':
  assumes "\<And>x. x=v \<Longrightarrow> f x \<le> SPEC \<Phi>"
  shows "Let v (\<lambda>x. f x) \<le> SPEC \<Phi>"
  using assms by simp


(* Obsolete, use RECT_eq_REC_tproof instead
text {* The following lemma shows that greatest and least fixed point are equal,
  if we can provide a variant. *}
thm RECT_eq_REC
lemma RECT_eq_REC_old:
  assumes WF: "wf V"
  assumes I0: "I x"
  assumes IS: "\<And>f x. I x \<Longrightarrow> 
    body (\<lambda>x'. do { ASSERT (I x' \<and> (x',x)\<in>V); f x'}) x \<le> body f x"
  shows "REC\<^sub>T body x = REC body x"
  apply (rule RECT_eq_REC)
  apply (rule WF)
  apply (rule I0)
  apply (rule order_trans[OF _ IS])
  apply (subgoal_tac "(\<lambda>x'. if I x' \<and> (x', x) \<in> V then f x' else FAIL) = 
    (\<lambda>x'. ASSERT (I x' \<and> (x', x) \<in> V) \<bind> (\<lambda>_. f x'))")
  apply simp
  apply (rule ext)
  apply (rule pw_eqI)
  apply (auto simp add: refine_pw_simps)
  done
*)

(* TODO: Also require RECT_le_rule. Derive RECT_invisible_refine from that. *)
lemma REC_le_rule:
  assumes M: "trimono body"
  assumes I0: "(x,x')\<in>R"
  assumes IS: "\<And>f x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le> M x'; (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le> M x'"
  shows "REC body x \<le> M x'"
  by (rule REC_rule_arb[OF M, where pre="\<lambda>x' x. (x,x')\<in>R", OF I0 IS])

(* TODO: Invariant annotations and vcg-rule
  Possibility 1: Semantically alter the program, such that it fails if the 
    invariant does not hold
  Possibility 2: Only syntactically annotate the invariant, as hint for the VCG.
*)

subsubsection \<open>Proving Monotonicity\<close>

lemma nr_mono_bind:
  assumes MA: "mono A" and MB: "\<And>s. mono (B s)"
  shows "mono (\<lambda>F s. bind (A F s) (\<lambda>s'. B s F s'))"
  apply (rule monoI)
  apply (rule le_funI)
  apply (rule bind_mono)
  apply (auto dest: monoD[OF MA, THEN le_funD]) []
  apply (auto dest: monoD[OF MB, THEN le_funD]) []
  done


lemma nr_mono_bind': "mono (\<lambda>F s. bind (f s) F)"
  apply rule
  apply (rule le_funI)
  apply (rule bind_mono)
  apply (auto dest: le_funD)
  done

lemmas nr_mono = nr_mono_bind nr_mono_bind' mono_const mono_if mono_id

subsubsection \<open>Proving Refinement\<close>
text \<open>In this subsection, we establish rules to prove refinement between 
  structurally similar programs. All rules are formulated including a possible
  data refinement via a refinement relation. If this is not required, the 
  refinement relation can be chosen to be the identity relation.
\<close>

text \<open>If we have two identical programs, this rule solves the refinement goal
  immediately, using the identity refinement relation.\<close>
lemma Id_refine[refine0]: "S \<le> \<Down>Id S" by auto

lemma RES_refine: 
  "\<lbrakk> \<And>s. s\<in>S \<Longrightarrow> \<exists>s'\<in>S'. (s,s')\<in>R\<rbrakk> \<Longrightarrow> RES S \<le> \<Down>R (RES S')" 
  by (auto simp: conc_fun_RES)

lemma SPEC_refine: 
  assumes "S \<le> SPEC (\<lambda>x. \<exists>x'. (x,x')\<in>R \<and> \<Phi> x')"
  shows "S \<le> \<Down>R (SPEC \<Phi>)"
  using assms
  by (force simp: pw_le_iff refine_pw_simps)

(* TODO/FIXME: This is already part of a type-based heuristics! *)
lemma Id_SPEC_refine[refine]: 
  "S \<le> SPEC \<Phi> \<Longrightarrow> S \<le> \<Down>Id (SPEC \<Phi>)" by simp

lemma RETURN_refine[refine]:
  assumes "(x,x')\<in>R"
  shows "RETURN x \<le> \<Down>R (RETURN x')"
  using assms
  by (auto simp: RETURN_def conc_fun_RES)

lemma RETURN_SPEC_refine:
  assumes "\<exists>x'. (x,x')\<in>R \<and> \<Phi> x'"
  shows "RETURN x \<le> \<Down>R (SPEC \<Phi>)"
  using assms 
  by (auto simp: pw_le_iff refine_pw_simps)

lemma FAIL_refine[refine]: "X \<le> \<Down>R FAIL" by auto
lemma SUCCEED_refine[refine]: "SUCCEED \<le> \<Down>R X'" by auto

lemma sup_refine[refine]:
  assumes "ai \<le>\<Down>R a"
  assumes "bi \<le>\<Down>R b"
  shows "sup ai bi \<le>\<Down>R (sup a b)"
  using assms by (auto simp: pw_le_iff refine_pw_simps)
    
    
text \<open>The next two rules are incomplete, but a good approximation for refining
  structurally similar programs.\<close>
lemma bind_refine':
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; inres M x; inres M' x';
    nofail M; nofail M'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply fast
  done

lemma bind_refine[refine]:
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R' \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  apply (rule bind_refine') using assms by auto

lemma bind_refine_abs': (* Only keep nf_inres-information for abstract *)
  fixes R' :: "('a\<times>'b) set" and R::"('c\<times>'d) set"
  assumes R1: "M \<le> \<Down> R' M'"
  assumes R2: "\<And>x x'. \<lbrakk> (x,x')\<in>R'; nf_inres M' x'
  \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')"
  shows "bind M (\<lambda>x. f x) \<le> \<Down> R (bind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done



text \<open>Special cases for refinement of binding to \<open>RES\<close>
  statements\<close>
lemma bind_refine_RES:
  "\<lbrakk>RES X \<le> \<Down> R' M';
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<bind> (\<lambda>x. f x) \<le> \<Down> R (M' \<bind> (\<lambda>x'. f' x'))"

  "\<lbrakk>M \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x' \<in> X' \<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> M \<bind> (\<lambda>x. f x) \<le> \<Down> R (RES X' \<bind> (\<lambda>x'. f' x'))"

  "\<lbrakk>RES X \<le> \<Down> R' (RES X');
  \<And>x x'. \<lbrakk>(x, x') \<in> R'; x \<in> X; x' \<in> X'\<rbrakk> \<Longrightarrow> f x \<le> \<Down> R (f' x')\<rbrakk>
  \<Longrightarrow> RES X \<bind> (\<lambda>x. f x) \<le> \<Down> R (RES X' \<bind> (\<lambda>x'. f' x'))"
  by (auto intro!: bind_refine')

declare bind_refine_RES(1,2)[refine]
declare bind_refine_RES(3)[refine]


lemma ASSERT_refine[refine]:
  "\<lbrakk> \<Phi>'\<Longrightarrow>\<Phi> \<rbrakk> \<Longrightarrow> ASSERT \<Phi> \<le> \<Down>Id (ASSERT \<Phi>')"
  by (cases \<Phi>') auto

lemma ASSUME_refine[refine]: 
  "\<lbrakk> \<Phi> \<Longrightarrow> \<Phi>' \<rbrakk> \<Longrightarrow> ASSUME \<Phi> \<le> \<Down>Id (ASSUME \<Phi>')"
  by (cases \<Phi>) auto

text \<open>
  Assertions and assumptions are treated specially in bindings
\<close>
lemma ASSERT_refine_right:
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R S'"
  shows "S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  using assms by (cases \<Phi>) auto
lemma ASSERT_refine_right_pres:
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  shows "S \<le>\<Down>R (do {ASSERT \<Phi>; S'})"
  using assms by (cases \<Phi>) auto

lemma ASSERT_refine_left:
  assumes "\<Phi>"
  assumes "\<Phi> \<Longrightarrow> S \<le> \<Down>R S'"
  shows "do{ASSERT \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_right:
  assumes "\<Phi>"
  assumes "\<Phi> \<Longrightarrow> S \<le>\<Down>R S'"
  shows "S \<le>\<Down>R (do {ASSUME \<Phi>; S'})"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_left:
  assumes "\<Phi> \<Longrightarrow> S \<le> \<Down>R S'"
  shows "do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

lemma ASSUME_refine_left_pres:
  assumes "\<Phi> \<Longrightarrow> do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  shows "do {ASSUME \<Phi>; S} \<le> \<Down>R S'"
  using assms by (cases \<Phi>) auto

text \<open>Warning: The order of \<open>[refine]\<close>-declarations is 
  important here, as preconditions should be generated before 
  additional proof obligations.\<close>
lemmas [refine0] = ASSUME_refine_right
lemmas [refine0] = ASSERT_refine_left
lemmas [refine0] = ASSUME_refine_left
lemmas [refine0] = ASSERT_refine_right

text \<open>For backward compatibility, as \<open>intro refine\<close> still
  seems to be used instead of \<open>refine_rcg\<close>.\<close>
lemmas [refine] = ASSUME_refine_right
lemmas [refine] = ASSERT_refine_left
lemmas [refine] = ASSUME_refine_left
lemmas [refine] = ASSERT_refine_right


definition lift_assn :: "('a \<times> 'b) set \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)"
  \<comment> \<open>Lift assertion over refinement relation\<close>
  where "lift_assn R \<Phi> s \<equiv> \<exists>s'. (s,s')\<in>R \<and> \<Phi> s'"
lemma lift_assnI: "\<lbrakk>(s,s')\<in>R; \<Phi> s'\<rbrakk> \<Longrightarrow> lift_assn R \<Phi> s"
  unfolding lift_assn_def by auto




lemma REC_refine[refine]:
  assumes M: "trimono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R; 
        REC body' = f' \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "REC (\<lambda>f x. body f x) x \<le>\<Down>S (REC (\<lambda>f' x'. body' f' x') x')"
  unfolding REC_def
  apply (clarsimp simp add: M)
  apply (rule lfp_induct_pointwise[where pre="\<lambda>x' x. (x,x')\<in>R" and B=body])

  apply rule
  apply clarsimp
  apply (blast intro: SUP_least)

  apply simp

  apply (simp add: trimonoD[OF M])

  apply (rule R0)

  apply (subst lfp_unfold, simp add: trimonoD)
  apply (rule RS)
  apply blast
  apply blast
  apply (simp add: REC_def[abs_def])
  done

lemma RECT_refine[refine]:
  assumes M: "trimono body"
  assumes R0: "(x,x')\<in>R"
  assumes RS: "\<And>f f' x x'. \<lbrakk> \<And>x x'. (x,x')\<in>R \<Longrightarrow> f x \<le>\<Down>S (f' x'); (x,x')\<in>R \<rbrakk> 
    \<Longrightarrow> body f x \<le>\<Down>S (body' f' x')"
  shows "RECT (\<lambda>f x. body f x) x \<le>\<Down>S (RECT (\<lambda>f' x'. body' f' x') x')"
  unfolding RECT_def
  apply (clarsimp simp add: M)

  apply (rule flatf_fixp_transfer[where 
        fp'="flatf_gfp body" 
    and B'=body 
    and P="\<lambda>x x'. (x',x)\<in>R", 
    OF _ _ flatf_ord.fixp_unfold[OF M[THEN trimonoD_flatf_ge]] R0])
  apply simp
  apply (simp add: trimonoD)
  by (rule RS)

lemma if_refine[refine]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> S1 \<le> \<Down>R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> S2 \<le> \<Down>R S2'"
  shows "(if b then S1 else S2) \<le> \<Down>R (if b' then S1' else S2')"
  using assms by auto

lemma Let_unfold_refine[refine]:
  assumes "f x \<le> \<Down>R (f' x')"
  shows "Let x f \<le> \<Down>R (Let x' f')"
  using assms by auto

text \<open>The next lemma is sometimes more convenient, as it prevents
  large let-expressions from exploding by being completely unfolded.\<close>
lemma Let_refine:
  assumes "(m,m')\<in>R'"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let m (\<lambda>x. f x) \<le>\<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms by auto

lemma Let_refine':
  assumes "(m,m')\<in>R"
  assumes "(m,m')\<in>R \<Longrightarrow> f m \<le>\<Down>S (f' m')"
  shows "Let m f \<le> \<Down>S (Let m' f')"
  using assms by simp

    
lemma case_option_refine[refine]:
  assumes "(v,v')\<in>\<langle>Ra\<rangle>option_rel"
  assumes "\<lbrakk>v=None; v'=None\<rbrakk> \<Longrightarrow> n \<le> \<Down> Rb n'"
  assumes "\<And>x x'. \<lbrakk> v=Some x; v'=Some x'; (x, x') \<in> Ra \<rbrakk> 
    \<Longrightarrow> f x \<le> \<Down> Rb (f' x')"
  shows "case_option n f v \<le>\<Down>Rb (case_option n' f' v')"
  using assms
  by (auto split: option.split simp: option_rel_def)

lemma list_case_refine[refine]: 
  assumes "(li,l)\<in>\<langle>S\<rangle>list_rel"
  assumes "fni \<le>\<Down>R fn"  
  assumes "\<And>xi x xsi xs. \<lbrakk> (xi,x)\<in>S; (xsi,xs)\<in>\<langle>S\<rangle>list_rel; li=xi#xsi; l=x#xs \<rbrakk> \<Longrightarrow> fci xi xsi \<le>\<Down>R (fc x xs)"  
  shows "(case li of [] \<Rightarrow> fni | xi#xsi \<Rightarrow> fci xi xsi) \<le> \<Down>R (case l of [] \<Rightarrow> fn | x#xs \<Rightarrow> fc x xs)"  
  using assms by (auto split: list.split)  
    
text \<open>It is safe to split conjunctions in refinement goals.\<close>
declare conjI[refine]

text \<open>The following rules try to compensate for some structural changes,
  like inlining lets or converting binds to lets.\<close>
lemma remove_Let_refine[refine2]:
  assumes "M \<le> \<Down>R (f x)"
  shows "M \<le> \<Down>R (Let x f)" using assms by auto

lemma intro_Let_refine[refine2]:
  assumes "f x \<le> \<Down>R M'"
  shows "Let x f \<le> \<Down>R M'" using assms by auto
  
lemma bind2let_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "Let x f \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms 
  apply (simp add: pw_le_iff refine_pw_simps) 
  apply fast
  done

lemma bind_Let_refine2[refine2]: "\<lbrakk> 
    m' \<le>\<Down>R' (RETURN x);
    \<And>x'. \<lbrakk>inres m' x'; (x',x)\<in>R'\<rbrakk> \<Longrightarrow> f' x' \<le> \<Down>R (f x) 
  \<rbrakk> \<Longrightarrow> m'\<bind>(\<lambda>x'. f' x') \<le> \<Down>R (Let x (\<lambda>x. f x))"
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma bind2letRETURN_refine[refine2]:
  assumes "RETURN x \<le> \<Down>R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> RETURN (f x) \<le> \<Down>R (f' x')"
  shows "RETURN (Let x f) \<le> \<Down>R (bind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply fast
  done

lemma RETURN_as_SPEC_refine[refine2]:
  assumes "M \<le> SPEC (\<lambda>c. (c,a)\<in>R)"
  shows "M \<le> \<Down>R (RETURN a)"
  using assms
  by (simp add: pw_le_iff refine_pw_simps)

lemma RETURN_as_SPEC_refine_old:
  "\<And>M R. M \<le> \<Down>R (SPEC (\<lambda>x. x=v)) \<Longrightarrow> M \<le>\<Down>R (RETURN v)"
  by (simp add: RETURN_def)

lemma if_RETURN_refine [refine2]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> RETURN S1 \<le> \<Down>R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> RETURN S2 \<le> \<Down>R S2'"
  shows "RETURN (if b then S1 else S2) \<le> \<Down>R (if b' then S1' else S2')"
  (* this is nice to have for small functions, hence keep it in refine2 *)
  using assms
  by (simp add: pw_le_iff refine_pw_simps)

lemma RES_sng_as_SPEC_refine[refine2]:
  assumes "M \<le> SPEC (\<lambda>c. (c,a)\<in>R)"
  shows "M \<le> \<Down>R (RES {a})"
  using assms
  by (simp add: pw_le_iff refine_pw_simps)


lemma intro_spec_refine_iff:
  "(bind (RES X) f \<le> \<Down>R M) \<longleftrightarrow> (\<forall>x\<in>X. f x \<le> \<Down>R M)"
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma intro_spec_refine[refine2]:
  assumes "\<And>x. x\<in>X \<Longrightarrow> f x \<le> \<Down>R M"
  shows "bind (RES X) (\<lambda>x. f x) \<le> \<Down>R M"
  using assms
  by (simp add: intro_spec_refine_iff)


text \<open>The following rules are intended for manual application, to reflect 
  some common structural changes, that, however, are not suited to be applied
  automatically.\<close>

text \<open>Replacing a let by a deterministic computation\<close>
lemma let2bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>R (f' x')"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R (Let m' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done



text \<open>Introduce a new binding, without a structural match in the abstract 
  program\<close>
lemma intro_bind_refine:
  assumes "m \<le> \<Down>R' (RETURN m')"
  assumes "\<And>x. (x,m')\<in>R' \<Longrightarrow> f x \<le> \<Down>R m''"
  shows "bind m (\<lambda>x. f x) \<le> \<Down>R m''"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

lemma intro_bind_refine_id:
  assumes "m \<le> (SPEC ((=) m'))"
  assumes "f m' \<le> \<Down>R m''"
  shows "bind m f \<le> \<Down>R m''"
  using assms
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done

text \<open>The following set of rules executes a step on the LHS or RHS of 
  a refinement proof obligation, without changing the other side.
  These kind of rules is useful for performing refinements with 
  invisible steps.\<close>  
lemma lhs_step_If:
  "\<lbrakk> b \<Longrightarrow> t \<le> m; \<not>b \<Longrightarrow> e \<le> m \<rbrakk> \<Longrightarrow> If b t e \<le> m" by simp

lemma lhs_step_RES:
  "\<lbrakk> \<And>x. x\<in>X \<Longrightarrow> RETURN x \<le> m  \<rbrakk> \<Longrightarrow> RES X \<le> m" 
  by (simp add: pw_le_iff)

lemma lhs_step_SPEC:
  "\<lbrakk> \<And>x. \<Phi> x \<Longrightarrow> RETURN x \<le> m \<rbrakk> \<Longrightarrow> SPEC (\<lambda>x. \<Phi> x) \<le> m" 
  by (simp add: pw_le_iff)

lemma lhs_step_bind:
  fixes m :: "'a nres" and f :: "'a \<Rightarrow> 'b nres"
  assumes "nofail m' \<Longrightarrow> nofail m"
  assumes "\<And>x. nf_inres m x \<Longrightarrow> f x \<le> m'"
  shows "do {x\<leftarrow>m; f x} \<le> m'"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast

lemma rhs_step_bind:
  assumes "m \<le> \<Down>R m'" "inres m x" "\<And>x'. (x,x')\<in>R \<Longrightarrow> lhs \<le>\<Down>S (f' x')"
  shows "lhs \<le> \<Down>S (m' \<bind> f')"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast

lemma rhs_step_bind_RES:
  assumes "x'\<in>X'"
  assumes "m \<le> \<Down>R (f' x')"
  shows "m \<le> \<Down>R (RES X' \<bind> f')"
  using assms by (simp add: pw_le_iff refine_pw_simps) blast

lemma rhs_step_bind_SPEC:
  assumes "\<Phi> x'"
  assumes "m \<le> \<Down>R (f' x')"
  shows "m \<le> \<Down>R (SPEC \<Phi> \<bind> f')"
  using assms by (simp add: pw_le_iff refine_pw_simps) blast

lemma RES_bind_choose:
  assumes "x\<in>X"
  assumes "m \<le> f x"
  shows "m \<le> RES X \<bind> f"
  using assms by (auto simp: pw_le_iff refine_pw_simps)

lemma pw_RES_bind_choose: 
  "nofail (RES X \<bind> f) \<longleftrightarrow> (\<forall>x\<in>X. nofail (f x))"
  "inres (RES X \<bind> f) y \<longleftrightarrow> (\<exists>x\<in>X. inres (f x) y)"
  by (auto simp: refine_pw_simps)

lemma prod_case_refine:  
  assumes "(p',p)\<in>R1\<times>\<^sub>rR2"
  assumes "\<And>x1' x2' x1 x2. \<lbrakk> p'=(x1',x2'); p=(x1,x2); (x1',x1)\<in>R1; (x2',x2)\<in>R2\<rbrakk> \<Longrightarrow> f' x1' x2' \<le> \<Down>R (f x1 x2)"
  shows "(case p' of (x1',x2') \<Rightarrow> f' x1' x2') \<le>\<Down>R (case p of (x1,x2) \<Rightarrow> f x1 x2)"
  using assms by (auto split: prod.split)



subsection \<open>Relators\<close>
declare fun_relI[refine]
  
definition nres_rel where 
  nres_rel_def_internal: "nres_rel R \<equiv> {(c,a). c \<le> \<Down>R a}"

lemma nres_rel_def: "\<langle>R\<rangle>nres_rel \<equiv> {(c,a). c \<le> \<Down>R a}"
  by (simp add: nres_rel_def_internal relAPP_def)

lemma nres_relD: "(c,a)\<in>\<langle>R\<rangle>nres_rel \<Longrightarrow> c \<le>\<Down>R a" by (simp add: nres_rel_def)
lemma nres_relI[refine]: "c \<le>\<Down>R a \<Longrightarrow> (c,a)\<in>\<langle>R\<rangle>nres_rel" by (simp add: nres_rel_def)

lemma nres_rel_comp: "\<langle>A\<rangle>nres_rel O \<langle>B\<rangle>nres_rel = \<langle>A O B\<rangle>nres_rel"
  by (auto simp: nres_rel_def conc_fun_chain[symmetric] conc_trans)

lemma pw_nres_rel_iff: "(a,b)\<in>\<langle>A\<rangle>nres_rel \<longleftrightarrow> nofail (\<Down> A b) \<longrightarrow> nofail a \<and> (\<forall>x. inres a x \<longrightarrow> inres (\<Down> A b) x)"
  by (simp add: pw_le_iff nres_rel_def)
    
    
lemma param_SUCCEED[param]: "(SUCCEED,SUCCEED) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma param_FAIL[param]: "(FAIL,FAIL) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma param_RES[param]:
  "(RES,RES) \<in> \<langle>R\<rangle>set_rel \<rightarrow> \<langle>R\<rangle>nres_rel"
  unfolding set_rel_def nres_rel_def
  by (fastforce intro: RES_refine)

lemma param_RETURN[param]: 
  "(RETURN,RETURN) \<in> R \<rightarrow> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def RETURN_refine)

lemma param_bind[param]:
  "(bind,bind) \<in> \<langle>Ra\<rangle>nres_rel \<rightarrow> (Ra\<rightarrow>\<langle>Rb\<rangle>nres_rel) \<rightarrow> \<langle>Rb\<rangle>nres_rel"
  by (auto simp: nres_rel_def intro: bind_refine dest: fun_relD)

lemma param_ASSERT_bind[param]: "\<lbrakk> 
    (\<Phi>,\<Psi>) \<in> bool_rel; 
    \<lbrakk> \<Phi>; \<Psi> \<rbrakk> \<Longrightarrow> (f,g)\<in>\<langle>R\<rangle>nres_rel
  \<rbrakk> \<Longrightarrow> (ASSERT \<Phi> \<then> f, ASSERT \<Psi> \<then> g) \<in> \<langle>R\<rangle>nres_rel"
  by (auto intro: nres_relI)

subsection \<open>Autoref Setup\<close>

consts i_nres :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of nres_rel i_nres]

(*lemma id_nres[autoref_id_self]: "ID_LIST 
  (l SUCCEED FAIL bind (REC::_ \<Rightarrow> _ \<Rightarrow> _ nres,1) (RECT::_ \<Rightarrow> _ \<Rightarrow> _ nres,1))"
  by simp_all
*)
(*definition [simp]: "op_RETURN x \<equiv> RETURN x"
lemma [autoref_op_pat_def]: "RETURN x \<equiv> op_RETURN x" by simp
*)

definition [simp]: "op_nres_ASSERT_bnd \<Phi> m \<equiv> do {ASSERT \<Phi>; m}"


lemma param_op_nres_ASSERT_bnd[param]:
  assumes "\<Phi>' \<Longrightarrow> \<Phi>"
  assumes "\<lbrakk>\<Phi>'; \<Phi>\<rbrakk> \<Longrightarrow> (m,m')\<in>\<langle>R\<rangle>nres_rel"
  shows "(op_nres_ASSERT_bnd \<Phi> m, op_nres_ASSERT_bnd \<Phi>' m') \<in> \<langle>R\<rangle>nres_rel"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps nres_rel_def)



context begin interpretation autoref_syn .
lemma id_ASSERT[autoref_op_pat_def]:
  "do {ASSERT \<Phi>; m} \<equiv> OP (op_nres_ASSERT_bnd \<Phi>)$m"
  by simp

definition [simp]: "op_nres_ASSUME_bnd \<Phi> m \<equiv> do {ASSUME \<Phi>; m}"
lemma id_ASSUME[autoref_op_pat_def]:
  "do {ASSUME \<Phi>; m} \<equiv> OP (op_nres_ASSUME_bnd \<Phi>)$m"
  by simp

end

lemma autoref_SUCCEED[autoref_rules]: "(SUCCEED,SUCCEED) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma autoref_FAIL[autoref_rules]: "(FAIL,FAIL) \<in> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def)

lemma autoref_RETURN[autoref_rules]: 
  "(RETURN,RETURN) \<in> R \<rightarrow> \<langle>R\<rangle>nres_rel"
  by (auto simp: nres_rel_def RETURN_refine)

lemma autoref_bind[autoref_rules]: 
  "(bind,bind) \<in> \<langle>R1\<rangle>nres_rel \<rightarrow> (R1\<rightarrow>\<langle>R2\<rangle>nres_rel) \<rightarrow> \<langle>R2\<rangle>nres_rel"
  apply (intro fun_relI)
  apply (rule nres_relI)
  apply (rule bind_refine)
  apply (erule nres_relD)
  apply (erule (1) fun_relD[THEN nres_relD])
  done


context begin interpretation autoref_syn .
lemma autoref_ASSERT[autoref_rules]:
  assumes "\<Phi> \<Longrightarrow> (m',m)\<in>\<langle>R\<rangle>nres_rel"
  shows "(
    m',
    (OP (op_nres_ASSERT_bnd \<Phi>) ::: \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel) $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms unfolding nres_rel_def
  by (simp add: ASSERT_refine_right)

lemma autoref_ASSUME[autoref_rules]:
  assumes "SIDE_PRECOND \<Phi>"
  assumes "\<Phi> \<Longrightarrow> (m',m)\<in>\<langle>R\<rangle>nres_rel"
  shows "(
    m',
    (OP (op_nres_ASSUME_bnd \<Phi>) ::: \<langle>R\<rangle>nres_rel \<rightarrow> \<langle>R\<rangle>nres_rel) $ m)\<in>\<langle>R\<rangle>nres_rel"
  using assms unfolding nres_rel_def
  by (simp add: ASSUME_refine_right)

lemma autoref_REC[autoref_rules]:
  assumes "(B,B')\<in>(Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  assumes "DEFER trimono B"
  shows "(REC B,
    (OP REC 
      ::: ((Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel)$B'
    ) \<in> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  apply (intro fun_relI)
  using assms
  apply (auto simp: nres_rel_def intro!: REC_refine)
  apply (simp add: fun_rel_def)
  apply blast
  done

theorem param_RECT[param]:
  assumes "(B, B') \<in> (Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
    and "trimono B"
  shows "(REC\<^sub>T B, REC\<^sub>T B')\<in> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  apply (intro fun_relI)
  using assms
  apply (auto simp: nres_rel_def intro!: RECT_refine)
  apply (simp add: fun_rel_def)
  apply blast
  done

lemma autoref_RECT[autoref_rules]:
  assumes "(B,B') \<in> (Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel"
  assumes "DEFER trimono B"
  shows "(RECT B,
    (OP RECT 
      ::: ((Ra\<rightarrow>\<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel) \<rightarrow> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel)$B'
    ) \<in> Ra \<rightarrow> \<langle>Rr\<rangle>nres_rel"
  using assms
  unfolding autoref_tag_defs 
  by (rule param_RECT)

end

subsection \<open>Convenience Rules\<close>
text \<open>
  In this section, we define some lemmas that simplify common prover tasks.
\<close>

lemma ref_two_step: "A\<le>\<Down>R  B \<Longrightarrow> B\<le>C \<Longrightarrow> A\<le>\<Down>R  C" 
  by (rule conc_trans_additional)

   
lemma pw_ref_iff:
  shows "S \<le> \<Down>R S' 
  \<longleftrightarrow> (nofail S' 
    \<longrightarrow> nofail S \<and> (\<forall>x. inres S x \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inres S' s')))"
  by (simp add: pw_le_iff refine_pw_simps)

lemma pw_ref_I:
  assumes "nofail S' 
    \<longrightarrow> nofail S \<and> (\<forall>x. inres S x \<longrightarrow> (\<exists>s'. (x, s') \<in> R \<and> inres S' s'))"
  shows "S \<le> \<Down>R S'"
  using assms
  by (simp add: pw_ref_iff)

text \<open>Introduce an abstraction relation. Usage: 
  \<open>rule introR[where R=absRel]\<close>
\<close>
lemma introR: "(a,a')\<in>R \<Longrightarrow> (a,a')\<in>R" .

lemma intro_prgR: "c \<le> \<Down>R a \<Longrightarrow> c \<le> \<Down>R a" by auto

lemma refine_IdI: "m \<le> m' \<Longrightarrow> m \<le> \<Down>Id m'" by simp
    

lemma le_ASSERTI_pres:
  assumes "\<Phi> \<Longrightarrow> S \<le> do {ASSERT \<Phi>; S'}"
  shows "S \<le> do {ASSERT \<Phi>; S'}"
  using assms by (auto intro: le_ASSERTI)

lemma RETURN_ref_SPECD:
  assumes "RETURN c \<le> \<Down>R (SPEC \<Phi>)"
  obtains a where "(c,a)\<in>R" "\<Phi> a"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma RETURN_ref_RETURND:
  assumes "RETURN c \<le> \<Down>R (RETURN a)"
  shows "(c,a)\<in>R"
  using assms
  apply (auto simp: pw_le_iff refine_pw_simps)
  done

lemma return_refine_prop_return:
  assumes "nofail m"
  assumes "RETURN x \<le> \<Down>R m"
  obtains x' where "(x,x')\<in>R" "RETURN x' \<le> m"
  using assms
  by (auto simp: refine_pw_simps pw_le_iff)
    
lemma ignore_snd_refine_conv: 
  "(m \<le> \<Down>(R\<times>\<^sub>rUNIV) m') \<longleftrightarrow> m\<bind>(RETURN o fst) \<le>\<Down>R (m'\<bind>(RETURN o fst))"
  by (auto simp: pw_le_iff refine_pw_simps)
    
    
lemma ret_le_down_conv: 
  "nofail m \<Longrightarrow> RETURN c \<le> \<Down>R m \<longleftrightarrow> (\<exists>a. (c,a)\<in>R \<and> RETURN a \<le> m)"
  by (auto simp: pw_le_iff refine_pw_simps)
    
lemma SPEC_eq_is_RETURN:
  "SPEC ((=) x) = RETURN x"
  "SPEC (\<lambda>x. x=y) = RETURN y"
  by (auto simp: RETURN_def)

lemma RETURN_SPEC_conv: "RETURN r = SPEC (\<lambda>x. x=r)"
  by (simp add: RETURN_def)

lemma refine2spec_aux:
  "a \<le> \<Down>R b \<longleftrightarrow> ( (nofail b \<longrightarrow> a \<le> SPEC ( \<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )) )"
  by (auto simp: pw_le_iff refine_pw_simps)
  
lemma refine2specI:
  assumes "nofail b \<Longrightarrow> a \<le> SPEC (\<lambda>r. (\<exists>x. inres b x \<and> (r,x)\<in>R) )"
  shows "a \<le> \<Down>R b"  
  using assms by (simp add: refine2spec_aux)  
    
lemma specify_left:
  assumes "m \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> f x \<le> M"  
  shows "do { x \<leftarrow> m; f x } \<le> M"
  using assms by (auto simp: pw_le_iff refine_pw_simps)  
    
lemma build_rel_SPEC: 
  "M \<le> SPEC ( \<lambda>x. \<Phi> (\<alpha> x) \<and> I x) \<Longrightarrow> M \<le> \<Down>(build_rel \<alpha> I) (SPEC \<Phi>)"
  by (auto simp: pw_le_iff refine_pw_simps build_rel_def)

lemma build_rel_SPEC_conv: "\<Down>(br \<alpha> I) (SPEC \<Phi>) = SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
  by (auto simp: br_def pw_eq_iff refine_pw_simps)
    
lemma refine_IdD: "c \<le> \<Down>Id a \<Longrightarrow> c \<le> a" by simp

lemma bind_sim_select_rule:
  assumes "m\<bind>f' \<le> SPEC \<Psi>"
  assumes "\<And>x. \<lbrakk>nofail m; inres m x; f' x\<le>SPEC \<Psi>\<rbrakk> \<Longrightarrow> f x\<le>SPEC \<Phi>"
  shows "m\<bind>f \<le> SPEC \<Phi>"
  \<comment> \<open>Simultaneously select a result from assumption and verification goal.
    Useful to work with assumptions that restrict the current program to 
    be verified.\<close>
  using assms 
  by (auto simp: pw_le_iff refine_pw_simps)

lemma assert_bind_spec_conv: "ASSERT \<Phi> \<then> m \<le> SPEC \<Psi> \<longleftrightarrow> (\<Phi> \<and> m \<le> SPEC \<Psi>)"  
  \<comment> \<open>Simplify a bind-assert verification condition. 
    Useful if this occurs in the assumptions, and considerably faster than 
    using pointwise reasoning, which may causes a blowup for many chained 
    assertions.\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

lemma summarize_ASSERT_conv: "do {ASSERT \<Phi>; ASSERT \<Psi>; m} = do {ASSERT (\<Phi> \<and> \<Psi>); m}"
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma bind_ASSERT_eq_if: "do { ASSERT \<Phi>; m } = (if \<Phi> then m else FAIL)"
  by auto
    
    
lemma le_RES_nofailI:
  assumes "a\<le>RES x"
  shows "nofail a"
  using assms
  by (metis nofail_simps(2) pwD1)

lemma add_invar_refineI:
  assumes "f x \<le>\<Down>R (f' x')"
    and "nofail (f x) \<Longrightarrow> f x \<le> SPEC I"
  shows "f x \<le> \<Down> {(c, a). (c, a) \<in> R \<and> I c} (f' x')"
  using assms
  by (simp add: pw_le_iff refine_pw_simps sv_add_invar)


lemma bind_RES_RETURN_eq: "bind (RES X) (\<lambda>x. RETURN (f x)) = 
  RES { f x | x. x\<in>X }"
  by (simp add: pw_eq_iff refine_pw_simps)
    blast

lemma bind_RES_RETURN2_eq: "bind (RES X) (\<lambda>(x,y). RETURN (f x y)) = 
  RES { f x y | x y. (x,y)\<in>X }"
  apply (simp add: pw_eq_iff refine_pw_simps)
  apply blast
  done

lemma le_SPEC_bindI: 
  assumes "\<Phi> x"
  assumes "m \<le> f x"
  shows "m \<le> SPEC \<Phi> \<bind> f"
  using assms by (auto simp add: pw_le_iff refine_pw_simps)

lemma bind_assert_refine: 
  assumes "m1 \<le> SPEC \<Phi>"
  assumes "\<And>x. \<Phi> x \<Longrightarrow> m2 x \<le> m'"
  shows "do {x\<leftarrow>m1; ASSERT (\<Phi> x); m2 x} \<le> m'"
  using assms
  by (simp add: pw_le_iff refine_pw_simps) blast


lemma RETURN_refine_iff[simp]: "RETURN x \<le>\<Down>R (RETURN y) \<longleftrightarrow> (x,y)\<in>R"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma RETURN_RES_refine_iff: 
  "RETURN x \<le>\<Down>R (RES Y) \<longleftrightarrow> (\<exists>y\<in>Y. (x,y)\<in>R)"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma RETURN_RES_refine:
  assumes "\<exists>x'. (x,x')\<in>R \<and> x'\<in>X"
  shows "RETURN x \<le> \<Down>R (RES X)"
  using assms 
  by (auto simp: pw_le_iff refine_pw_simps)

lemma in_nres_rel_iff: "(a,b)\<in>\<langle>R\<rangle>nres_rel \<longleftrightarrow> a \<le>\<Down>R b"
  by (auto simp: nres_rel_def)

lemma inf_RETURN_RES: 
  "inf (RETURN x) (RES X) = (if x\<in>X then RETURN x else SUCCEED)"
  "inf (RES X) (RETURN x) = (if x\<in>X then RETURN x else SUCCEED)"
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma inf_RETURN_SPEC[simp]:
  "inf (RETURN x) (SPEC (\<lambda>y. \<Phi> y)) = SPEC (\<lambda>y. y=x \<and> \<Phi> x)"
  "inf (SPEC (\<lambda>y. \<Phi> y)) (RETURN x) = SPEC (\<lambda>y. y=x \<and> \<Phi> x)"
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma RES_sng_eq_RETURN: "RES {x} = RETURN x"
  by simp

lemma nofail_inf_serialize:
  "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> inf a b = do {x\<leftarrow>a; ASSUME (inres b x); RETURN x}"
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma conc_fun_SPEC: 
  "\<Down>R (SPEC (\<lambda>x. \<Phi> x)) = SPEC (\<lambda>y. \<exists>x. (y,x)\<in>R \<and> \<Phi> x)"  
  by (auto simp: pw_eq_iff refine_pw_simps)

lemma conc_fun_RETURN: 
  "\<Down>R (RETURN x) = SPEC (\<lambda>y. (y,x)\<in>R)"  
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma use_spec_rule:
  assumes "m \<le> SPEC \<Psi>"
  assumes "m \<le> SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
  shows "m \<le> SPEC \<Phi>"
  using assms
  by (auto simp: pw_le_iff refine_pw_simps)

lemma strengthen_SPEC: "m \<le> SPEC \<Phi> \<Longrightarrow> m \<le> SPEC(\<lambda>s. inres m s \<and> nofail m \<and> \<Phi> s)"
  \<comment> \<open>Strengthen SPEC by adding trivial upper bound for result\<close>
  by (auto simp: pw_le_iff refine_pw_simps)

lemma weaken_SPEC:
  "m \<le> SPEC \<Phi> \<Longrightarrow> (\<And>x. \<Phi> x \<Longrightarrow> \<Psi> x) \<Longrightarrow> m \<le> SPEC \<Psi>"
  by (force elim!: order_trans)

lemma bind_le_nofailI:
  assumes "nofail m"
  assumes "\<And>x. RETURN x \<le> m \<Longrightarrow> f x \<le> m'"
  shows "m\<bind>f \<le> m'"
  using assms 
  by (simp add: refine_pw_simps pw_le_iff) blast

lemma bind_le_shift:
  "bind m f \<le> m' 
  \<longleftrightarrow> m \<le> (if nofail m' then SPEC (\<lambda>x. f x \<le> m') else FAIL)"
  by (auto simp: pw_le_iff refine_pw_simps)

lemma If_bind_distrib[simp]:
  fixes t e :: "'a nres"
  shows "(If b t e \<bind> (\<lambda>x. f x)) = (If b (t\<bind>(\<lambda>x. f x)) (e\<bind>(\<lambda>x. f x)))"  
  by simp
    
(* TODO: Can we make this a simproc, using NO_MATCH? *)  
lemma unused_bind_conv: 
  assumes "NO_MATCH (ASSERT \<Phi>) m"
  assumes "NO_MATCH (ASSUME \<Phi>) m"
  shows "(m\<bind>(\<lambda>x. c))  = (ASSERT (nofail m) \<bind> (\<lambda>_. ASSUME (\<exists>x. inres m x) \<bind> (\<lambda>x. c)))" 
  by (auto simp: pw_eq_iff refine_pw_simps)

text \<open>The following rules are useful for massaging programs before the 
  refinement takes place\<close>
lemma let_to_bind_conv: 
  "Let x f = RETURN x\<bind>f"
  by simp

lemmas bind_to_let_conv = let_to_bind_conv[symmetric]

lemma pull_out_let_conv: "RETURN (Let x f) = Let x (\<lambda>x. RETURN (f x))"
  by simp

lemma push_in_let_conv: 
  "Let x (\<lambda>x. RETURN (f x)) = RETURN (Let x f)"
  "Let x (RETURN o f) = RETURN (Let x f)"
  by simp_all

lemma pull_out_RETURN_case_option: 
  "case_option (RETURN a) (\<lambda>v. RETURN (f v)) x = RETURN (case_option a f x)"
  by (auto split: option.splits)

lemma if_bind_cond_refine: 
  assumes "ci \<le> RETURN b"
  assumes "b \<Longrightarrow> ti\<le>\<Down>R t"
  assumes "\<not>b \<Longrightarrow> ei\<le>\<Down>R e"
  shows "do {b\<leftarrow>ci; if b then ti else ei} \<le> \<Down>R (if b then t else e)"
  using assms
  by (auto simp add: refine_pw_simps pw_le_iff)

lemma intro_RETURN_Let_refine:
  assumes "RETURN (f x) \<le> \<Down>R M'"
  shows "RETURN (Let x f) \<le> \<Down>R M'" 
  (* this should be needed very rarely - so don't add it *)
  using assms by auto

lemma ife_FAIL_to_ASSERT_cnv: 
  "(if \<Phi> then m else FAIL) = op_nres_ASSERT_bnd \<Phi> m"
  by (cases \<Phi>, auto)

lemma nres_bind_let_law: "(do { x \<leftarrow> do { let y=v; f y }; g x } :: _ nres)
  = do { let y=v; x\<leftarrow> f y; g x }" by auto

lemma unused_bind_RES_ne[simp]: "X\<noteq>{} \<Longrightarrow> do { _ \<leftarrow> RES X; m} = m"
  by (auto simp: pw_eq_iff refine_pw_simps)


lemma le_ASSERT_defI1:
  assumes "c \<equiv> do {ASSERT \<Phi>; m}"
  assumes "\<Phi> \<Longrightarrow> m' \<le> c"
  shows "m' \<le> c"
  using assms
  by (simp add: le_ASSERTI)

lemma refine_ASSERT_defI1:
  assumes "c \<equiv> do {ASSERT \<Phi>; m}"
  assumes "\<Phi> \<Longrightarrow> m' \<le> \<Down>R c"
  shows "m' \<le> \<Down>R c"
  using assms
  by (simp, refine_vcg)

lemma le_ASSERT_defI2:
  assumes "c \<equiv> do {ASSERT \<Phi>; ASSERT \<Psi>; m}"
  assumes "\<lbrakk>\<Phi>; \<Psi>\<rbrakk> \<Longrightarrow> m' \<le> c"
  shows "m' \<le> c"
  using assms
  by (simp add: le_ASSERTI)

lemma refine_ASSERT_defI2:
  assumes "c \<equiv> do {ASSERT \<Phi>; ASSERT \<Psi>; m}"
  assumes "\<lbrakk>\<Phi>; \<Psi>\<rbrakk> \<Longrightarrow> m' \<le> \<Down>R c"
  shows "m' \<le> \<Down>R c"
  using assms
  by (simp, refine_vcg)

lemma ASSERT_le_defI:
  assumes "c \<equiv> do { ASSERT \<Phi>; m'}"
  assumes "\<Phi>"
  assumes "\<Phi> \<Longrightarrow> m' \<le> m"
  shows "c \<le> m"
  using assms by (auto)

lemma ASSERT_same_eq_conv: "(ASSERT \<Phi> \<then> m) = (ASSERT \<Phi> \<then> n) \<longleftrightarrow> (\<Phi> \<longrightarrow> m=n)"  
  by auto

lemma case_prod_bind_simp[simp]: "
  (\<lambda>x. (case x of (a, b) \<Rightarrow> f a b) \<le> SPEC \<Phi>) = (\<lambda>(a,b). f a b \<le> SPEC \<Phi>)"
  by auto
    
lemma RECT_eq_REC': "nofail (RECT B x) \<Longrightarrow> RECT B x = REC B x"
  by (subst RECT_eq_REC; simp_all add: nofail_def)
    
    
lemma rel2p_nres_RETURN[rel2p]: "rel2p (\<langle>A\<rangle>nres_rel) (RETURN x) (RETURN y) = rel2p A x y"   
  by (auto simp: rel2p_def dest: nres_relD intro: nres_relI)


subsubsection \<open>Boolean Operations on Specifications\<close>
lemma SPEC_iff:
  assumes "P \<le> SPEC (\<lambda>s. Q s \<longrightarrow> R s)"
  and "P \<le> SPEC (\<lambda>s. \<not> Q s \<longrightarrow> \<not> R s)"
  shows "P \<le> SPEC (\<lambda>s. Q s \<longleftrightarrow> R s)"
  using assms[THEN pw_le_iff[THEN iffD1]]
  by (auto intro!: pw_leI)

lemma SPEC_rule_conjI:
  assumes "A \<le> SPEC P" and "A \<le> SPEC Q"
    shows "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
proof -
  have "A \<le> inf (SPEC P) (SPEC Q)" using assms by (rule_tac inf_greatest) assumption
  thus ?thesis by (auto simp add:Collect_conj_eq)
qed

lemma SPEC_rule_conjunct1:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC P"
proof -
  note assms
  also have "\<dots> \<le> SPEC P" by (rule SPEC_rule) auto
  finally show ?thesis .
qed

lemma SPEC_rule_conjunct2:
  assumes "A \<le> SPEC (\<lambda>v. P v \<and> Q v)"
    shows "A \<le> SPEC Q"
proof -
  note assms
  also have "\<dots> \<le> SPEC Q" by (rule SPEC_rule) auto
  finally show ?thesis .
qed


subsubsection \<open>Pointwise Reasoning\<close>
lemma inres_if:
  "\<lbrakk> inres (if P then Q else R) x; \<lbrakk>P; inres Q x\<rbrakk> \<Longrightarrow> S; \<lbrakk>\<not> P; inres R x\<rbrakk> \<Longrightarrow> S \<rbrakk> \<Longrightarrow> S"
by (metis (full_types))

lemma inres_SPEC:
  "inres M x \<Longrightarrow> M \<le> SPEC \<Phi> \<Longrightarrow> \<Phi> x"
by (auto dest: pwD2)

lemma SPEC_nofail:
  "X \<le> SPEC \<Phi> \<Longrightarrow> nofail X"
by (auto dest: pwD1)

lemma nofail_SPEC: "nofail m \<Longrightarrow> m \<le> SPEC (\<lambda>_. True)"
  by (simp add: pw_le_iff)

lemma nofail_SPEC_iff: "nofail m \<longleftrightarrow> m \<le> SPEC (\<lambda>_. True)"
  by (simp add: pw_le_iff)

lemma nofail_SPEC_triv_refine: "\<lbrakk> nofail m; \<And>x. \<Phi> x \<rbrakk> \<Longrightarrow> m \<le> SPEC \<Phi>"
  by (simp add: pw_le_iff)




end
